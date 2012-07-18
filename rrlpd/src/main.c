/* (C) 2011 by Dieter Spaar <spaar@mirider.augusta.de>
 *
 * All Rights Reserved
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
 
/*

  The idea behind the RRLP server is as follows:
  
  - Every RRLP related response from the MS is sent to the RRLP server
  
  - If it is a position, the decoded position is returned
  
  - If there is an error, an error message is returned
  
  - If assistance data are requested, a set of PDUs with the required
    data is generated. A set of PDUs is used to not exceed the maximum
    size for a RRLP message.
    
  - If an assitance data ACK is received, the next assitance data PDU 
    is sent (no data are returned if it is the final message).    
    
 */
 
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h> 

#include <sys/ioctl.h>
#include <termios.h>
#include <fcntl.h>

#include <PDU.h>

#include "gps.h"
#include "ubx.h"
#include "ubx-parse.h"
#include "rrlp.h"

#define DEBUG 1
#if DEBUG
	#define printd(x, args ...) printf(x, ## args)
#else
	#define printd(x, args ...)
#endif

#define DEBUG_GPS 1
#if DEBUG_GPD
	#define prints(x, args ...) printf(x, ## args)
#else
	#define prints(x, args ...)
#endif

//#define PDU RRLP_Component

/* Convert "Type" defined by -DPDU into "asn_DEF_Type" */
#define	ASN_DEF_PDU(t)	asn_DEF_ ## t
#define	DEF_PDU_Type(t)	ASN_DEF_PDU(t)
#define	PDU_Type	DEF_PDU_Type(PDU)

/* TODO */

#define RRLP_SERV_PORT	7890

#define MAX_RRLP_DATA	256

/* Server cmds */

#define RRLP_CMD_MS_DATA		1 /* data from MS */
#define RRLP_CMD_MS_DATA_SLOW	2 /* data from MS, slow channel */

/* Server response */

#define RRLP_RSP_ASSIST_DATA	1 /* assitance data, send to MS */
#define RRLP_RSP_RRLP_ERROR		2 /* RRLP error */
#define RRLP_RSP_RRLP_POSITION	3 /* RRLP position */
#define RRLP_RSP_ERROR			4 /* something went wrong */


#define SUBSC_ID_NONE		0

#define N_MAX_AD_RECORDS		10
#define N_MAX_AD_RECORDS_SLOW	1  /* maximum number of messages used on slow channel */

enum rrlp_state { RRLP_NONE = 0, RRLP_ASSIST, RRLP_ERROR, RRLP_POSITION, RRLP_WAIT_POSITION };

/* record for the state of a subscriber */

struct rrlp_sub_state {
	long long unsigned int id;	/* subscriber ID from OpenBSC */
	time_t time_first;			/* time when record was used the first time */
	
	int reference_num;			/* RRLP reference number */
	
	enum rrlp_state state;
	
	int	error;					/* error */
	
	/* a large assistance data APDU is split in smaller parts */	
	int cur_assist_record;		/* current assistance data record */
	uint8_t assist_data_len[N_MAX_AD_RECORDS]; /* length of a record */
	uint8_t assist_data[N_MAX_AD_RECORDS][MAX_RRLP_DATA]; /* record */
	
	/* GPS position */
	long latitude; /* */
	long longitude; /* */
	long altitude; /* in meter */
};

void free_rrlp_subscriber(struct rrlp_sub_state *rrlp_sub_state);

/* static allocation, might change that for a large number of queries at once */

#define N_MAX_RRLP_STATES	3000

struct rrlp_sub_state g_rrlp_states[N_MAX_RRLP_STATES];

/* assistance data from the GPS receiver */

struct gps_assist_data g_gps;

/* 
	According to TS 23.032
	
	So far only "Ellipsoid point with altitude and uncertainty Ellipsoid"
	seems to be sent from the MS.
*/

int decode_pos_estimate(struct rrlp_sub_state *rrlp_sub_state, uint8_t *data, int len)
{
	long latitude;
	long longitude;
	long altitude;
	
	if(len < 1) {
		fprintf(stderr, "decode_pos_estimate: len too short (%d)\n", len);
		return -1;
	}

	/* type of shape */
	switch((data[0] & 0xF0) >> 4) {
	case 0x00:
		printd("Ellipsoid point\n");
		break;

	case 0x01:
		printd("Ellipsoid point with uncertainty Circle\n");
		break;

	case 0x03:
		printd("Ellipsoid point with uncertainty Ellipse\n");
		break;

	case 0x05:
		printd("Polygon\n");
		break;

	case 0x08:
		printd("Ellipsoid point with altitude\n");
		break;

	case 0x09:
		printd("Ellipsoid point with altitude and uncertainty Ellipsoid\n");
		if(len != 14) {
			fprintf(stderr, "decode_pos_estimate: invalid len (%d)\n", len);
			return -1;
		}
		/* Deggrees of latitude */
		latitude = ((data[1] & 0x7F) << 16) + (data[2] << 8) + data[3];
		if(data[1] & 0x80)
			latitude = -latitude;
		printd("latitude = %f\n", ((double)latitude * 90.0) / 0x800000L);
		/* Deggrees of longitude */
		longitude = (data[4] << 16) + (data[5] << 8) + data[6];
		if(data[4] & 0x80)
			longitude |= 0xFF000000;
		printd("longitude = %f\n", ((double)longitude * 360.0) / 0x1000000L);
		/* Altitude */
		altitude = ((data[7] & 0x7F) << 8) + data[8];
		if(data[7] & 0x80)
			altitude = -altitude;
		printd("altitude = %ld\n", altitude);
		/* Uncertainty semi-major */
		/* Uncertainty semi-minor */
		/* Orientation of major axis */
		/* Uncertainty Altitude */
		/* Confidence */
		
		rrlp_sub_state->latitude = latitude;
		rrlp_sub_state->longitude = longitude;
		rrlp_sub_state->altitude = altitude;
		
		return 0;
		break;

	case 0x0A:
		printd("Ellipsoid Arc\n");
		break;

	default:
		printd("Unknown shape type: %d\n", (data[0] & 0xF0) >> 4);
		break;
	}
	
	fprintf(stderr, "cannot decode shape type (%d)\n", (data[0] & 0xF0) >> 4);
	
	return -1;
}

int decode_rrlp_data(struct rrlp_sub_state *rrlp_sub_state, int max_reply_msgs,
	uint8_t *data, int len,
	uint8_t *cmd_reply, uint8_t *reply, int *len_reply)
{
    static asn_TYPE_descriptor_t *pduType = &PDU_Type;
    void *structure; /* Decoded structure */    
	asn_codec_ctx_t *opt_codec_ctx = 0;
	asn_dec_rval_t rval;
	int rc;
	
	structure = 0;
    
	rval = uper_decode(opt_codec_ctx, pduType, (void **)&structure, data, len, 0, 0);
	
	if(!structure) {
		if(errno) {
			fprintf(stderr, "Error: errno = %d\n", errno);
			return -1;
		} else {
			/* EOF */
			fprintf(stderr, "EOF\n");
			return -1;
		}
	} else {
		/* dump PDU */
		asn_fprint(stdout, pduType, structure);
		
		long l;
		PDU_t *pdu = (PDU_t*)structure;
		
		printd("\n");
		printd("-- referenceNumber = %ld\n", pdu->referenceNumber);
		
		rrlp_sub_state->reference_num = pdu->referenceNumber;
		
		/* CHOICE */
		switch(pdu->component.present) {

		case RRLP_Component_PR_msrPositionReq:
			printd("-- msrPositionReq\n");
			
			*cmd_reply = RRLP_RSP_ERROR;
			strcpy(reply, "APU unsupported: msrPositionReq");
			*len_reply = strlen(reply) + 1;
			break;
		
		case RRLP_Component_PR_msrPositionRsp:
			printd("-- msrPositionRsp\n");
			
			/* "MsrPosition-Rsp": process either "locationInfo" or "locationError" */
			
			/* SEQUENCE with OPTIONAL components */
			MsrPosition_Rsp_t *msrPositionRsp = &pdu->component.choice.msrPositionRsp;
			
			if(msrPositionRsp->multipleSets) {
				printd("---- multipleSets\n");
			}
			
			if(msrPositionRsp->referenceIdentity) {
				printd("---- referenceIdentity\n");
			}
			
			if(msrPositionRsp->otd_MeasureInfo) {
				printd("---- otd_MeasureInfo\n");
			}
			
			if(msrPositionRsp->locationInfo) {
				printd("---- locationInfo\n");
				printd("------ refFrame = %ld\n", msrPositionRsp->locationInfo->refFrame);
				if(msrPositionRsp->locationInfo->gpsTOW) {
					printd("------ gpsTOW = %ld\n", *msrPositionRsp->locationInfo->gpsTOW);
					/* in ms */
				}
				printd("---- fixType = %ld\n", msrPositionRsp->locationInfo->fixType);
				printd("---- posEstimate\n");
				int n = msrPositionRsp->locationInfo->posEstimate.size;
				uint8_t *buf = msrPositionRsp->locationInfo->posEstimate.buf;
			#if 1 /* dump data */
				int i;
				for(i = 0; i < n; i++)
					printd("%02X ", buf[i]);
				printd("\n");
			#endif
				/* TODO */
				if(decode_pos_estimate(rrlp_sub_state, buf, n) != 0) {
					fprintf(stderr, "decode_pos_estimate failed\n");
					
					*cmd_reply = RRLP_RSP_ERROR;
					strcpy(reply, "decode_pos_estimate failed");
					*len_reply = strlen(reply) + 1;
				} else {
					*cmd_reply = RRLP_RSP_RRLP_POSITION;
					
					rrlp_sub_state->state = RRLP_POSITION;
					
					reply[0] = rrlp_sub_state->latitude & 0xFF;
					reply[1] = (rrlp_sub_state->latitude >>  8) & 0xFF;
					reply[2] = (rrlp_sub_state->latitude >> 16) & 0xFF;
					reply[3] = (rrlp_sub_state->latitude >> 24) & 0xFF;
					
					reply[4] = rrlp_sub_state->longitude & 0xFF;
					reply[5] = (rrlp_sub_state->longitude >>  8) & 0xFF;
					reply[6] = (rrlp_sub_state->longitude >> 16) & 0xFF;
					reply[7] = (rrlp_sub_state->longitude >> 24) & 0xFF;
					
					reply[ 8] = rrlp_sub_state->altitude & 0xFF;
					reply[ 9] = (rrlp_sub_state->altitude >>  8) & 0xFF;
					reply[10] = (rrlp_sub_state->altitude >> 16) & 0xFF;
					reply[11] = (rrlp_sub_state->altitude >> 24) & 0xFF;
					
					*len_reply = 3 * 4;
				}
				/* we got a location, ignore anything else */
				goto done;
			}
			
			if(msrPositionRsp->gps_MeasureInfo) {
				printd("---- gps_MeasureInfo\n");
			}
			
			if(msrPositionRsp->locationError) {
				printd("---- locationError\n");
				if(asn_INTEGER2long(&msrPositionRsp->locationError->locErrorReason, &l) == 0) {
					asn_INTEGER_specifics_t *specs = (asn_INTEGER_specifics_t *)asn_DEF_LocErrorReason.specifics;
					const asn_INTEGER_enum_map_t *el;	
					el = INTEGER_map_value2enum(specs, l);
					if(el) {
						printd("---- locErrorReason = %ld (%s)\n", l, el->enum_name);
						sprintf(reply, "locationError %ld (%s)", l, el->enum_name);
					} else {
						printd("---- locErrorReason = %ld\n", l);
						sprintf(reply, "locationError %ld", l);
					}
				} else {
					printd("---- locErrorReason: decode error\n");
					strcpy(reply, "locationError ??");				
					l = 9999;
				}
				if(msrPositionRsp->locationError->additionalAssistanceData) {
					printd("------ additionalAssistanceData\n");
					if(msrPositionRsp->locationError->additionalAssistanceData->gpsAssistanceData) {
						printd("------ gpsAssistanceData\n");
						int n = msrPositionRsp->locationError->additionalAssistanceData->gpsAssistanceData->size;
						uint8_t *buf = msrPositionRsp->locationError->additionalAssistanceData->gpsAssistanceData->buf;
						struct rrlp_assist_req ar;
					#if 1 /* dump data */
						int i;
						for(i = 0; i < n; i++)
							printd("%02X ", buf[i]);
						printd("\n");
					#endif
						/* check state */
						if(rrlp_sub_state->state == RRLP_ASSIST) {
							fprintf(stderr, "assistanceData in invalid state\n");
							
							*cmd_reply = RRLP_RSP_ERROR;
							strcpy(reply, "assistanceData in invalid state");
							*len_reply = strlen(reply) + 1;
							goto done;
						}
						if(rrlp_sub_state->state == RRLP_WAIT_POSITION) {
							fprintf(stderr, "assistanceData already sent\n");
							
							*cmd_reply = RRLP_RSP_ERROR;
							strcpy(reply, "assistanceData already sent");
							*len_reply = strlen(reply) + 1;
							goto done;
						}
						/* decode the requested assistance data */
						rc = rrlp_decode_assistance_request(&ar, buf, n);
						if(rc != 0) {
							fprintf(stderr, "rrlp_decode_assistance_request failed: %d\n", rc);
							
							*cmd_reply = RRLP_RSP_ERROR;
							sprintf(reply, "rrlp_decode_assistance_request failed: %d", rc);
							*len_reply = strlen(reply) + 1;
						} else if(l == LocErrorReason_gpsAssDataMissing) {													
							void *pdus[N_MAX_AD_RECORDS];
							int lens[N_MAX_AD_RECORDS];
							int i;
							int error = 0;
							int ref_num;
							
							/* take a new reference number for the assistance data */
							ref_num = rrlp_sub_state->reference_num;
							ref_num++;
							if(ref_num > 7) /* 0..7 */
								ref_num = 7;
							if(ref_num == 0) /* 0 is special */
								ref_num = 1;
						
							/* generate PDUs */							
							rc = rrlp_gps_assist_pdus(ref_num, &g_gps, &ar, pdus, lens, N_MAX_AD_RECORDS);
							if(rc < 0) {
								fprintf(stderr, "rrlp_gps_assist_pdus: %d\n", rc);
							
								*cmd_reply = RRLP_RSP_ERROR;
								sprintf(reply, "rrlp_gps_assist_pdus failed: %d", rc);
								*len_reply = strlen(reply) + 1;
								goto done;
							}
														
							/* clear messages */
							for(i = 0; i < N_MAX_AD_RECORDS; i++) {
								rrlp_sub_state->assist_data_len[i] = 0;
								memset(rrlp_sub_state->assist_data[i], 0, MAX_RRLP_DATA);
							}
							
							/* check if maximum number of messages exceeded */
							if(rc > max_reply_msgs) {
								for(i = 0; i < rc; i++) {
									if(pdus[i])
										asn_DEF_PDU.free_struct(&asn_DEF_PDU, pdus[i], 0);
								}
								
								fprintf(stderr, "too many assitance messages: (%d > %d)\n", rc, max_reply_msgs);
							
								*cmd_reply = RRLP_RSP_ERROR;
								sprintf(reply, "too many assitance messages: (%d > %d)\n", rc, max_reply_msgs);
								*len_reply = strlen(reply) + 1;
								goto done;
							}
							
							/* copy PDUs to subscriber state */
							for(i = 0; i < rc; i++) {
								printd("%p %d\n", pdus[i], lens[i]);
								if(pdus[i] == NULL) { 
									fprintf(stderr, "pdus[%d] == NULL\n", i);
									sprintf(reply, "pdus[%d] == NULL\n", i);
									error = -1;
								}
								#if 0 /* Debug */
									{
										int rv, fd;
										char filename[50];
										sprintf(filename, "pdu%02d.uper", i);
										fd = open(filename, O_TRUNC | O_CREAT | O_RDWR, S_IREAD | S_IWRITE);
										if (fd < 0)
											printf("File error\n");
										rv = write(fd, pdus[i], lens[i]);
										if(rv != lens[i])
											printf("Write error\n");
										close(fd);
									}
								#endif
								#if 0 /* Debug */
									int j;
									for(j = 0; j < lens[i]; j++)
										printf("%02X ", ((uint8_t*)pdus[i])[j]);
									printf("\n");
								#endif
								
								if(lens[i] > MAX_RRLP_DATA) {
									fprintf(stderr, "lens[%d] > MAX_RRLP_DATA (%d)\n", i, lens[i]);
									sprintf(reply, "lens[%d] > MAX_RRLP_DATA (%d)\n", i, lens[i]);
									error = -2;
								}
																
								if(error == 0) {
									rrlp_sub_state->assist_data_len[i] = lens[i];
									memcpy(rrlp_sub_state->assist_data[i], pdus[i], lens[i]);
									
								}
								
								if(pdus[i])
									free(pdus[i]);
							}
							
							if(error) {
								*cmd_reply = RRLP_RSP_ERROR;
								*len_reply = strlen(reply) + 1;
								goto done;
							}
							
							*cmd_reply = RRLP_RSP_ASSIST_DATA;
					
							rrlp_sub_state->state = RRLP_ASSIST;							
							rrlp_sub_state->cur_assist_record = 0;
							
							/* send first assistent data block */
							i = rrlp_sub_state->cur_assist_record;
							memcpy(reply, rrlp_sub_state->assist_data[i], rrlp_sub_state->assist_data_len[i]);
							*len_reply = rrlp_sub_state->assist_data_len[i];
							/* advance if not already at the end */
							if(rrlp_sub_state->assist_data_len[i])
								rrlp_sub_state->cur_assist_record++;
							
							/* we got assistance data, ignore anything else */
							goto done;
						}
					}
				}
				rrlp_sub_state->state = RRLP_ERROR;

				*cmd_reply = RRLP_RSP_RRLP_ERROR;
				*len_reply = strlen(reply) + 1;
				/* we got an error, ignore anything else */
				goto done;
			}
			
			if(msrPositionRsp->extensionContainer) {
				printd("---- extensionContainer\n");
			}			
			
			/* no "locationInfo" or "locationError" */
			*cmd_reply = RRLP_RSP_ERROR;
			strcpy(reply, "unexpected MsrPosition-Rsp component");
			*len_reply = strlen(reply) + 1;
			break;

		case RRLP_Component_PR_assistanceData:
			printd("-- assistanceData\n");
			
			*cmd_reply = RRLP_RSP_ERROR;
			strcpy(reply, "APDU unsupported: assistanceData");
			*len_reply = strlen(reply) + 1;
			break;

		case RRLP_Component_PR_assistanceDataAck:
			printd("-- assistanceDataAck\n");
						
			/* check state */
			if(rrlp_sub_state->state != RRLP_ASSIST) {
				*cmd_reply = RRLP_RSP_ERROR;
				fprintf(stderr, "assistanceData Ack in invalid state\n");
				strcpy(reply, "assistanceData Ack in invalid state");
				*len_reply = strlen(reply) + 1;
				goto done;
			}
						
			/* send next assitance data reply or done */
			
			*cmd_reply = RRLP_RSP_ASSIST_DATA;

			int i = rrlp_sub_state->cur_assist_record;
			if(i < N_MAX_AD_RECORDS) {
				memcpy(reply, rrlp_sub_state->assist_data[i], rrlp_sub_state->assist_data_len[i]);
				*len_reply = rrlp_sub_state->assist_data_len[i];
				/* advance if not already at the end */
				if(rrlp_sub_state->assist_data_len[i]) 
					rrlp_sub_state->cur_assist_record++;				
				else {
					rrlp_sub_state->state = RRLP_NONE;
				}
			} else {
				*len_reply = 0;
				rrlp_sub_state->state = RRLP_WAIT_POSITION;
			}
			
			break;

		case RRLP_Component_PR_protocolError:
			printd("-- protocolError\n");
			ProtocolError_t *protocolError = &pdu->component.choice.protocolError;
			if(asn_INTEGER2long(&protocolError->errorCause, &l) == 0) {
				asn_INTEGER_specifics_t *specs = (asn_INTEGER_specifics_t *)asn_DEF_ErrorCodes.specifics;
				const asn_INTEGER_enum_map_t *el;	
				el = INTEGER_map_value2enum(specs, l);
				if(el) {
					printd("---- errorCause = %ld (%s)\n", l, el->enum_name);
					sprintf(reply, "protocolError %ld (%s)", l, el->enum_name);
				} else {
					printd("---- errorCause = %ld\n", l);
					sprintf(reply, "protocolError %ld", l);				
				}
			} else {
				printd("---- errorCause: decode error\n");
				strcpy(reply, "protocolError ??");				
			}
			
			rrlp_sub_state->state = RRLP_ERROR;

			*cmd_reply = RRLP_RSP_RRLP_ERROR;
			*len_reply = strlen(reply) + 1;			
			break;

		default:
			printd("-- unknown %d\n", pdu->component.present);
			
			*cmd_reply = RRLP_RSP_ERROR;
			sprintf(reply, "unknown PDU conponent %d", pdu->component.present);
			*len_reply = strlen(reply) + 1;
			break;
		}
				
done:		
		/* free structure */
		
		asn_DEF_PDU.free_struct(&asn_DEF_PDU, (void*)structure, 0);
	}	
	
	return 0;
}

/***********************************************************************/

static int ubx_parse(struct gps_assist_data *gps, uint8_t *data, int len)
{
	int rv = 0, i;

	/* Parse each message */
	for(i = 0; i < len; ) {
		rv = ubx_msg_dispatch(ubx_parse_dt, data + i, len - i, gps);
		if (rv < 0)
			i++;	/* Invalid message: try one byte later */
		else
			i += rv;
	}

	return (rv >= 0) ? 0 : rv;
}

/***********************************************************************/

/* taken from OsmocomBB */

static int serial_init(const char *serial_port, speed_t baudrate)
{
	int rc, serial_fd;
	struct termios tio;

	serial_fd = open(serial_port, O_RDWR | O_NOCTTY | O_NDELAY);
	if (serial_fd < 0) {
		perror("cannot open serial port");
		return serial_fd;
	}

	//fcntl(serial_fd, F_SETFL, 0);

	/* Configure serial interface */
	rc = tcgetattr(serial_fd, &tio);
	if (rc < 0) {
		close(serial_fd);
		perror("tcgetattr()");
		return rc;
	}
	rc = cfsetispeed(&tio, baudrate);
	if (rc < 0) {
		close(serial_fd);
		perror("cfsetispeed()");
		return rc;
	}
	rc = cfsetospeed(&tio, baudrate);
	if (rc < 0) {
		close(serial_fd);
		perror("cfsetospeed()");
		return rc;
	}
	tio.c_cflag &= ~(PARENB | CSTOPB | CSIZE | CRTSCTS);
	tio.c_cflag |=  (CREAD | CLOCAL | CS8);
	tio.c_lflag &= ~(ICANON | ECHO | ECHOE | ISIG);
	tio.c_iflag |=  (INPCK | ISTRIP);
	tio.c_iflag &= ~(ISTRIP | IXON | IXOFF | IGNBRK | INLCR | ICRNL | IGNCR);
	tio.c_oflag &= ~(OPOST | ONLCR);
	rc = tcsetattr(serial_fd, TCSANOW, &tio);
	if (rc < 0) {
		close(serial_fd);
		perror("tcsetattr()");
		return rc;
	}

	return serial_fd;
}

#define GPS_USB	1 /* set to 1 if uBlox GPS receiver is connected to USB */

#if GPS_USB
  #define GPS_BAUDRATE	B115200
#else
  #define GPS_BAUDRATE	B9600
#endif

/*

USB: switch back to NMEA output

"$PUBX,41,3,0003,0002,9600,0*17\r\n"

*/

static int set_ubx_protocol(int fd)
{
	int len;
	/* Set Protocol and baudrate (switch to UBX output, still allow NMEA input) */
#if GPS_USB /* if uBlox is connected through USB */
	char upx_chg_mode[] = "$PUBX,41,3,0003,0001,115200,0*1C\r\n";
#else /* if uBlox is connected through the serial port */
	char upx_chg_mode[] = "$PUBX,41,1,0003,0001,9600,0*16\r\n";
#endif

	len = write(fd, upx_chg_mode, sizeof(upx_chg_mode) - 1);
	if(len != sizeof(upx_chg_mode) - 1) {
		perror("write()");
		return len;
	}

	/* a short delay */

	sleep(1);

	/* flush the input buffer (there is probably are more elegant solution) */
	
	for(;;) {			
		fd_set readset;
		struct timeval tv;
		int rc;	
		int len;
		uint8_t buf[256];
		
		/* check for data */
				
		FD_ZERO(&readset);
		FD_SET(fd, &readset);
		tv.tv_sec = 0;
		tv.tv_usec = 300 * 1000;
		
		rc = select(fd + 1, &readset, NULL, NULL, &tv);
		if(rc < 0) {
			if(errno != EINTR) {
				fprintf(stderr, "select() failed: (%d) %s\n", rc, strerror(errno));
				break;
			}
		}
		if(!FD_ISSET(fd, &readset))
			break;	
			
		/* read data */
		
	 	len = read(fd, buf, sizeof(buf));
		if(len <= 0) {
			fprintf(stderr, "serial read() failed: (%d) %s\n", len, strerror(errno));
			break;
		}				
			
	}	
	
	return 0;
}

static int ubx_get_data(int fd)
{
	int len;	
	char upx_msg1[] = "\xb5\x62\x01\x02\x00\x00\x03\x0a"; /* NAV-POSLLH */	
	char upx_msg2[] = "\xb5\x62\x0b\x10\x00\x00\x1b\x5c"; /* AID-DATA */
	char upx_msg3[] = "\xB5\x62\x06\x01\x03\x00\x01\x20\x01\x2C\x83"; /* CFG-MSG, send NAV-TIMEGPS every second */

	len = write(fd, upx_msg1, sizeof(upx_msg1) - 1);
	if(len != sizeof(upx_msg1) - 1) {
		perror("write()");
		return len;
	}

	len = write(fd, upx_msg2, sizeof(upx_msg2) - 1);
	if(len != sizeof(upx_msg2) - 1) {
		perror("write()");
		return len;
	}

#if 1	
	len = write(fd, upx_msg3, sizeof(upx_msg3) - 1);
	if(len != sizeof(upx_msg3) - 1) {
		perror("write()");
		return len;
	}
#endif	

	return 0;
}

static int ubx_get_time(int fd)
{
	int len;	
	char upx_msg1[] = "\xb5\x62\x01\x20\x00\x00\x21\x64";  /* NAV-TIMEGPS */
	//char upx_msg1[] = "\xb5\x62\x01\x22\x00\x00\x23\x6A";  /* NAV-CLOCK */
	fd_set readset;
	struct timeval tv;
	int rc;	
	uint8_t buf[256];
	struct gps_assist_data gps;

	len = write(fd, upx_msg1, sizeof(upx_msg1) - 1);
	if(len != sizeof(upx_msg1) - 1) {
		perror("write()");
		return len;
	}

	/* wait for reply (does it really take nearly a second ?) */
	
	FD_ZERO(&readset);
	FD_SET(fd, &readset);
	tv.tv_sec = 0;
	tv.tv_usec = 1000 * 1000;
		
	rc = select(fd + 1, &readset, NULL, NULL, &tv);
	if(rc < 0) {
		if(errno != EINTR) {
			fprintf(stderr, "select() failed: (%d) %s\n", rc, strerror(errno));
			return -1;
		}
	}
	if(!FD_ISSET(fd, &readset)) {
		fprintf(stderr, "timeout waiting for GPS time\n");
		return -2;	
	}
			
	/* read data */
		
 	len = read(fd, buf, sizeof(buf));
	if(len <= 0) {
		fprintf(stderr, "serial read() failed: (%d) %s\n", len, strerror(errno));
		return -1;
	}				
	
	/* parse data */
	
	memset(&gps, 0, sizeof(gps));
	if(ubx_parse(&gps, buf, len) != 0) {
		fprintf(stderr, "ubx_parse failed\n");
		return -1;
	}
	
	return 0;
}

/***********************************************************************/

void init_rrlp_states(void)
{
	int i;
	memset(&g_rrlp_states, 0, sizeof(g_rrlp_states));
	
	for(i = 0; i < N_MAX_RRLP_STATES; i++) {
		g_rrlp_states[i].id = SUBSC_ID_NONE;
		g_rrlp_states[i].state = RRLP_NONE;
	}
}

/* find record with this ID or get an unused one */

struct rrlp_sub_state *get_rrlp_subscriber(long long unsigned int id)
{
	int i;
	
	/* search for this ID */
	for(i = 0; i < N_MAX_RRLP_STATES; i++) {
		if(g_rrlp_states[i].id == id)
			return &g_rrlp_states[i];
	}
	
	/* search for an unused record */
	for(i = 0; i < N_MAX_RRLP_STATES; i++) {
		if(g_rrlp_states[i].id == SUBSC_ID_NONE) {
			g_rrlp_states[i].id = id;
			g_rrlp_states[i].time_first = time(NULL);
			return &g_rrlp_states[i];
		}
	}
	
	return NULL;
}

void free_rrlp_subscriber(struct rrlp_sub_state *rrlp_sub_state)
{
	memset(rrlp_sub_state, 0, sizeof(struct rrlp_sub_state));
	rrlp_sub_state->id = SUBSC_ID_NONE;
	rrlp_sub_state->state = RRLP_NONE;
}

/* find expired records and free them */

#define SUBS_RECORD_LIFETIME 300 /* in seconds */

void free_expired_rrlp_subscribers(void)
{
	int i;
	
	/* search for this ID */
	for(i = 0; i < N_MAX_RRLP_STATES; i++) {
		if(g_rrlp_states[i].id != SUBSC_ID_NONE && time(NULL) - g_rrlp_states[i].time_first > SUBS_RECORD_LIFETIME) {
			free_rrlp_subscriber(&g_rrlp_states[i]);
		}
	}
}

#define GPS_POLL_TIME	100 /* in seconds */

#define MAX(a, b) ((a > b) ? a : b)

int rrlp_serv(int fd, int fd_serial)
{
	fd_set readset;
	struct timeval tv;
	int rc;	
	int len;
	uint8_t buf[2 + 1 + 8 + MAX_RRLP_DATA]; /* len, cmd, subscriber ID, data */
	uint8_t buf_reply[MAX_RRLP_DATA];
	uint8_t buf_serial[1024 * 8]; /* should be large enough for the complete data set */
	int len_pkt, offs, len_reply, len_data;
	uint8_t cmd, cmd_reply;
	long long unsigned int id;	
	struct sockaddr_in from;
	int from_len;
	time_t last_gps_query = 0;
	time_t last_subs_expiration = time(NULL);
	struct rrlp_sub_state *rrlp_sub_state;

	memset(&g_gps, 0, sizeof(g_gps));
	
	init_rrlp_states();	
	
	for(;;) {	
			
		/* new GPS poll ? */
		
		if(time(NULL) - last_gps_query > GPS_POLL_TIME) {
			printd("GPS poll\n");			
			ubx_get_data(fd_serial);
			last_gps_query = time(NULL);
		}

		/* any data from RRLP client or GPS Receicer ? */ 
		
		FD_ZERO(&readset);
		FD_SET(fd, &readset);
		if(fd_serial != -1)
			FD_SET(fd_serial, &readset);
		tv.tv_sec = 1;
		tv.tv_usec = 0;
		
        /* this creates another UDP socket on Cygwin !? */
#if 0
		rc = select(sizeof(readset) * 8, &readset, NULL, NULL, &tv);
#else
		rc = select(MAX(fd, fd_serial) + 1, &readset, NULL, NULL, &tv);
#endif
		if(rc < 0) {
			if(errno == EINTR)
				continue;
			fprintf(stderr, "select() failed: (%d) %s\n", rc, strerror(errno));
			return -1;
		}
		
		/* data from RRLP client ? */
		
		if(FD_ISSET(fd, &readset)) {
		
			/* read packet */
        	from_len = sizeof(from);
			len = recvfrom(fd, buf, sizeof(buf), 0, (struct sockaddr*)&from, &from_len);
			if(len < 0) {
				fprintf(stderr, "recvfrom() failed: (%d) %s\n", len, strerror(errno));
				return -1;
			}		
			if(len < 2) {
				fprintf(stderr, "len < 2: %d\n", len);
				return -1;
			}		
			len_pkt = buf[0] + (buf[1] << 8);
			if(len_pkt < 2 + 1 + 8) {
				fprintf(stderr, "len_pkt < 2 + 8 + 1: %d\n", len_pkt);
				return -1;
			}		
			if(len != len_pkt) {
				/* TODO: we might have received more than one packet */
				fprintf(stderr, "recvfrom: len != len_pkt: %d %d\n", len, len_pkt);
				return -1;
			}		
			len_pkt -= 2;
			offs = 2;
			
#if 0		/* dump packet */	
			{
				int i;
				for(i = 0; i < len_pkt; i++)
					printd("%02X ", buf[offs + i]);
				printd("\n");
			}
#endif			

			cmd = buf[offs + 0];
			/* get subscriber ID */
			id = buf[offs + 1];
			id += ((long long unsigned int)buf[offs + 2] << 8);
			id += ((long long unsigned int)buf[offs + 3] << 16);
			id += ((long long unsigned int)buf[offs + 4] << 24);
			id += ((long long unsigned int)buf[offs + 5] << 32);
			id += ((long long unsigned int)buf[offs + 6] << 40);
			id += ((long long unsigned int)buf[offs + 7] << 48);
			id += ((long long unsigned int)buf[offs + 8] << 56);
			
			printd("cmd = 0x%02X ID = %llu\n", cmd, id);			
			
			len_data = len_pkt - (1 + 8);
			offs += (1 + 8);
			
#if 1		/* dump data */	
			{
				int i;
				for(i = 0; i < len_data; i++)
					printd("%02X ", buf[offs + i]);
				printd("\n");
			}
#endif			
			
			/* process packet */
			
			len_reply = 0;
			cmd_reply = 0x00;
			
			/* search subscriber record with this ID or allocate a new one */
			
			rrlp_sub_state = get_rrlp_subscriber(id);
			if(rrlp_sub_state == NULL) {
				fprintf(stderr, "cannot get subscriber reccord\n");
				
				cmd_reply = RRLP_RSP_ERROR;
				strcpy(buf_reply, "cannot get subscriber reccord");
				len_reply = strlen(buf_reply) + 1;
			} else {		
				if(cmd == RRLP_CMD_MS_DATA) {
					if(decode_rrlp_data(rrlp_sub_state, N_MAX_AD_RECORDS, &buf[offs], len_data, &cmd_reply, buf_reply, &len_reply) != 0) {
						cmd_reply = RRLP_RSP_ERROR;
						strcpy(buf_reply, "decode_rrlp_data failed");
						len_reply = strlen(buf_reply) + 1;
					}
				} else if(cmd == RRLP_CMD_MS_DATA_SLOW) {
					if(decode_rrlp_data(rrlp_sub_state, N_MAX_AD_RECORDS_SLOW, &buf[offs], len_data, &cmd_reply, buf_reply, &len_reply) != 0) {
						cmd_reply = RRLP_RSP_ERROR;
						strcpy(buf_reply, "decode_rrlp_data failed");
						len_reply = strlen(buf_reply) + 1;
					}
				} else {			
					cmd_reply = RRLP_RSP_ERROR;
					strcpy(buf_reply, "invalid command");
					len_reply = strlen(buf_reply) + 1;
				}
			}
			
			/* send reply, build packet */
			len_pkt = 2 + 1 + len_reply;
			buf[0] = len_pkt & 0xFF;
			buf[1] = (len_pkt >> 8) & 0xFF;
			buf[2] = cmd_reply; /* cmd */
			/* data */
			memcpy(&buf[3], buf_reply, len_reply);
			
			len = sendto(fd, buf, len_pkt, 0, (struct sockaddr*)&from, sizeof(from));
			if(len < 0) {
				fprintf(stderr, "sendto() failed: (%d) %s\n", len, strerror(errno));
				return -1;
			}		
			if(len != len_pkt) {
				fprintf(stderr, "sendto: len != len_pkt: %d %d\n", len, len_pkt);
				return -1;
			}					
		}
		
		/* data from the GPS receiver ? */
		
		if(fd_serial != -1 && FD_ISSET(fd_serial, &readset)) {

			int buf_offset = 0;
			int total_len = 0;
			struct gps_assist_data gps;

			for(;;) {			
			 	len = read(fd_serial, buf_serial + buf_offset, sizeof(buf_serial) - buf_offset);
				if(len <= 0) {
					fprintf(stderr, "serial read() failed: (%d) %s\n", len, strerror(errno));
					break;
				}				
				prints("serial data: %d\n", len);
				
				total_len += len;
				
				buf_offset += len;
				if(buf_offset >= sizeof(buf_serial)) {
					fprintf(stderr, "serial buffer full\n");
					break;
				}
				
				/* check for more data */
				
				FD_ZERO(&readset);
				FD_SET(fd_serial, &readset);
				tv.tv_sec = 0;
				tv.tv_usec = 300 * 1000;
		
				rc = select(fd_serial + 1, &readset, NULL, NULL, &tv);
				if(rc < 0) {
					if(errno != EINTR) {
						fprintf(stderr, "select() failed: (%d) %s\n", rc, strerror(errno));
						break;
					}
				}
				if(!FD_ISSET(fd_serial, &readset))
					break;
			}

			prints("total_len: %d\n", total_len);

#if 0		/* dump hex data */	
			{
				int i;
				for(i = 0; i < total_len; i++)
					prints("%02X ", buf_serial[i]);
				prints("\n");
			}
#endif			
#if 0		/* dump ASCII data */	
			{
				int i;
				for(i = 0; i < total_len; i++)
					prints("%c", buf_serial[i]);
			}
#endif			

			memset(&gps, 0, sizeof(gps));
			if(ubx_parse(&gps, buf_serial, total_len) != 0) {
				fprintf(stderr, "ubx_parse failed\n");
			}
			else {
				if(gps.fields == GPS_FIELD_REFTIME) {
					g_gps.ref_time = gps.ref_time;
				}
				else if (gps.fields != 0) {
					g_gps = gps;
				}
			}
			
			
		#if 0 /* for time testing */
			close(fd_serial);
			fd_serial = -1;			
		#endif
		}
		
		/* expire subscribers ? */
		
		if(time(NULL) - last_subs_expiration > SUBS_RECORD_LIFETIME) {
			printd("Subscriber expiration\n");			
			free_expired_rrlp_subscribers();
			last_subs_expiration = time(NULL);
		}
		
#if 0 /* for testing only */
		ubx_get_time(fd_serial);
#endif
	}

	return 0;
}

static int fd = -1; 
static int fd_serial = -1;

static void signal_handler(int signal)
{
	int rc;
	
	fprintf(stdout, "signal %u received\n", signal);

	switch (signal) {
	case SIGINT:	
		if(fd != -1) {
			printd("close\n");
			rc = close(fd);
			if(rc != 0) {
				fprintf(stderr, "close() failed: (%d) %s\n", rc, strerror(errno));
			}
		}
		if(fd_serial != -1) {
			printd("close serial\n");
			rc = close(fd_serial);
			if(rc != 0) {
				fprintf(stderr, "close() failed: (%d) %s\n", rc, strerror(errno));
			}
		}
		exit(0);
		break;
	default:
		break;
	}
}
			
int main(int argc, char *argv[])
{
	int rc;
	struct sockaddr_in sa;
    int on;
	
	printf("RRLP Server\n");

	if(argc != 3) {
		fprintf(stderr, "usage: rrlp-serv <IP address of the network interface to use> <GPS serial device>.\n");
		return -1;
	}
		
	fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
	if(fd < 0) {
		fprintf(stderr, "socket() failed: (%d) %s\n", fd, strerror(errno));
		return -1;
	}
	
	/* This is for Cygwin/Windows, for Linux take the interface name */
	
	sa.sin_family = AF_INET;
	sa.sin_port = htons(RRLP_SERV_PORT);
	sa.sin_addr.s_addr = INADDR_ANY;
	if(inet_aton(argv[1], &sa.sin_addr) != 1) {
		fprintf(stderr, "inet_aton() failed: %s\n", strerror(errno));
		close(fd);
		return -1;
	}
	
    if(sa.sin_addr.s_addr == INADDR_NONE)
    {
        fprintf(stderr, "Invalid local address\n"); 
		close(fd);
        return -1;
    }
	
	on = 1;
	rc = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));
	if(rc != 0) {
		fprintf(stderr, "setsockopt() failed: (%d) %s\n", rc, strerror(errno));
	}

	rc = bind(fd, (struct sockaddr *)&sa, sizeof(sa));
	if(rc < 0) {
		fprintf(stderr, "bind() failed: (%d) %s\n", rc, strerror(errno));
		close(fd);
		return -1;
	}

	/* serial port for GPS receiver */
	
	fd_serial= serial_init(argv[2], GPS_BAUDRATE);
	if(fd_serial < 0) {
		fprintf(stderr, "serial_init failed: (%d) %s\n", fd_serial, strerror(errno));
		close(fd);
		return -1;
	}

	set_ubx_protocol(fd_serial);

	signal(SIGINT, &signal_handler);
	signal(SIGABRT, &signal_handler);
	signal(SIGUSR1, &signal_handler);

	printf("Waiting for incoming data....\n");
	
	rrlp_serv(fd, fd_serial);
	
	rc = close(fd);
	if(rc != 0) {
		fprintf(stderr, "close() failed: (%d) %s\n", rc, strerror(errno));
	}
	fd = -1;
	
	rc = close(fd_serial);
	if(rc != 0) {
		fprintf(stderr, "close() serial failed: (%d) %s\n", rc, strerror(errno));
	}
	fd_serial = -1;
	
	return 0;
}
