/*
 * rrlp.c
 *
 * RRLP implementation
 *
 *
 * Copyright (C) 2009  Sylvain Munaut <tnt@246tNt.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


#include <errno.h>
#include <math.h>

#include "gps.h"
#include "rrlp.h"

#include <PDU.h>
#include <GPS-AssistData.h>
#include <NavigationModel.h>
#include <IonosphericModel.h>
#include <UTCModel.h>
#include <Almanac.h>
#include <RefLocation.h>
#include <ReferenceTime.h>


/* ------------------------------------------------------------------------ */
/* RRLP Assistance request decoding                                         */
/* ---------------------------------------------------------------------{{{ */
/* Decode and validate the assistance data request messages.
 * See section 10.10 of
 *  . ETSI TS 149 031 V8.1.0 (2009-01)
 *  . 3GPP TS 49.031 version 8.1.0 Release 8
 */

/* Packed structure from 49.031 spec (RGA = Request GPS Assistance) */

#define RRLP_RGA0_ALMANAC	(1<<0)
#define RRLP_RGA0_UTC_MODEL	(1<<1)
#define RRLP_RGA0_IONO_MODEL	(1<<2)
#define RRLP_RGA0_NAV_MODEL	(1<<3)
#define RRLP_RGA0_DGPS		(1<<4)
#define RRLP_RGA0_REF_LOC	(1<<5)
#define RRLP_RGA0_REF_TIME	(1<<6)
#define RRLP_RGA0_ACQ_ASSIST	(1<<7)

#define RRLP_RGA1_REALTIME_INT	(1<<0)
#define RRLP_RGA1_EPH_EXT	(1<<1)
#define RRLP_RGA1_EPH_EXT_CHECK	(1<<2)

struct rrlp_rga_hdr {
	uint8_t items0;
	uint8_t items1;
} __attribute__((packed));

struct rrlp_rga_eph_sv {
	uint8_t sv_id;		/* [7:6] reserved, [5:0] sv_id */
	uint8_t iode;		/* latest eph in the MS memory in hours */
} __attribute__((packed));

struct rrlp_rga_eph {
	uint8_t wn_hi;		/* [7:6] = wn[9:8] */
	uint8_t wn_lo;		/* wn[7:0] */
	uint8_t toe;		/* latest eph in the MS memory in hours */
	uint8_t nsat_tmtoe;	/* [7:4] nstat, [3:0] T-Toe limit */
	struct rrlp_rga_eph_sv svs[0];
} __attribute__((packed));

struct rrlp_rga_eph_ext {
	uint8_t validity;	/* in 4 hours units */
} __attribute__((packed));

struct rrlp_rga_eph_ext_check {
		/* weeks are in gps week modulo 4 */
	uint8_t wn_begin_end;	/* [7:4] begin, [3:0] end */
	uint8_t tow_begin;
	uint8_t tow_end;
} __attribute__((packed));


/* Parsing function */

int
rrlp_decode_assistance_request(
	struct rrlp_assist_req *ar,
	void *req, int req_len)
{
	struct rrlp_rga_hdr *hdr = NULL;
	struct rrlp_rga_eph *eph = NULL;
	struct rrlp_rga_eph_ext *eph_ext = NULL;
	struct rrlp_rga_eph_ext_check *eph_ext_check = NULL;
	int p = 0;
	int rc = 0;

	/* Reset */
	ar->req_elems = 0;
	ar->eph_svs = 0;

	/* Parse message */
	hdr = req;
	p += sizeof(struct rrlp_rga_hdr);
	if (p > req_len)
		return -1;

	if (hdr->items0 & RRLP_RGA0_NAV_MODEL) {
		printf("NAV_MODEL\n");
		eph = req + p;
		p += sizeof(struct rrlp_rga_eph);
		if (p > req_len)
			return -1;
		p += (eph->nsat_tmtoe >> 4) * sizeof(struct rrlp_rga_eph_sv);
		if (p > req_len)
			return -1;
			
		printf("  GPS week = %d\n", (eph->wn_hi << 8) + eph->wn_lo);
		printf("  TOE = %d\n", eph->toe);
		printf("  T-TOE limit = %d\n", eph->nsat_tmtoe & 0x0F);
		
		int i;
		for(i = 0; i < (eph->nsat_tmtoe >> 4); i++) {
			printf("  %2d: sv_id = %2d (%d)  IODE = %3d\n", i, eph->svs[i].sv_id & 0x3F, eph->svs[i].sv_id >> 6, eph->svs[i].iode);
			if(eph->svs[i].sv_id >> 6) {
				/* most certainly invalid data or have to be interpreted differently */
				rc = -3;
			}
		}
	}

	if (hdr->items1 & RRLP_RGA1_EPH_EXT) {
		printf("EPH_EXT\n");
		eph_ext = req + p;
		p += sizeof(struct rrlp_rga_eph_ext);
		if (p > req_len)
			return -1;
	}

	if (hdr->items1 & RRLP_RGA1_EPH_EXT_CHECK) {
		printf("EPH_EXT_CHECK\n");
		eph_ext_check = req + p;
		p += sizeof(struct rrlp_rga_eph_ext_check);
		if (p > req_len)
			return -1;
	}

	if (p != req_len && (p != 2 || req_len != 6)) { /* P==2 && req_len == 6 might happen */
		fprintf(stderr, "p != req_len (%d %d)\n", p, req_len);		
		return -2; /* not all bytes consumed ??? */
	}

	/* Print a warning for unsupported requests */
	if ((eph_ext != NULL) ||
	    (eph_ext_check != NULL) ||
	    (hdr->items0 & (RRLP_RGA0_DGPS | RRLP_RGA0_ACQ_ASSIST)) ||
	 #if 0
	    (hdr->items1 & RRLP_RGA1_REALTIME_INT)) {
	 #else
	    0) {
	 #endif
		fprintf(stderr, "[w] Unsupported assistance data requested, ignored ...\n");
		
	    if(hdr->items0 & RRLP_RGA0_DGPS)
			printf("Unsupported assistance data requested: RRLP_RGA0_DGPS\n");
	    if(hdr->items0 & RRLP_RGA0_ACQ_ASSIST)
			printf("Unsupported assistance data requested: RRLP_RGA0_ACQ_ASSIST\n");
	    if(hdr->items1 & RRLP_RGA1_REALTIME_INT)
			printf("Unsupported assistance data requested: RRLP_RGA1_REALTIME_INT\n");
	}

	/* Copy the request */
	if (hdr->items0 & RRLP_RGA0_ALMANAC) {
		printf("ALMANAC\n");
		ar->req_elems |= RRLP_AR_ALMANAC;
	}

	if (hdr->items0 & RRLP_RGA0_UTC_MODEL) {
		printf("UTC_MODEL\n");
		ar->req_elems |= RRLP_AR_UTC_MODEL;
	}

	if (hdr->items0 & RRLP_RGA0_IONO_MODEL) {
		printf("IONO_MODEL\n");
		ar->req_elems |= RRLP_AR_IONO_MODEL;
	}

	if (hdr->items0 & RRLP_RGA0_REF_LOC) {
		printf("REF_LOC\n");
		ar->req_elems |= RRLP_AR_REF_LOC;
	}

	if (hdr->items0 & RRLP_RGA0_REF_TIME) {
		printf("REF_TIME\n");
		ar->req_elems |= RRLP_AR_REF_TIME;
	}

	if (hdr->items1 & RRLP_RGA1_REALTIME_INT) {
		printf("REALTIME_INTEGRITY\n");
		ar->req_elems |= RRLP_AR_REALTIME_INT;
	}
	
	if (hdr->items0 & RRLP_RGA0_NAV_MODEL) {
		printf("NAV_MODEL\n");
		int i, n_svs = eph->nsat_tmtoe >> 4;
		ar->req_elems |= RRLP_AR_EPHEMERIS;
		if(n_svs == 0) {
			ar->eph_svs = 0xFFFFFFFFFFFFFFFFULL;
		}
		else {
			for (i=0; i<n_svs; i++)
				ar->eph_svs |= (1ULL << (eph->svs[i].sv_id - 1)); /* Dieter: CHECK */
		}
	}

	return rc;
}

/* }}} */


/* ------------------------------------------------------------------------ */
/* RRLP elements fill                                                       */
/* ---------------------------------------------------------------------{{{ */

	/* Helpers */

static void
_ts_23_032_store_latitude(double lat, uint8_t *b)
{
	uint32_t x;
	x = (uint32_t) floor(fabs(lat/90.0) * ((double)(1<<23)));
	if (x >= (1<<23))
		x = (1<<23) - 1;
	if (lat < 0.0)
		x |= (1<<23);
	b[0] = (x >> 16) & 0xff;
	b[1] = (x >>  8) & 0xff;
	b[2] =  x        & 0xff;
}

static void
_ts_23_032_store_longitude(double lon, uint8_t *b)
{
	int32_t x;
	x = floor((lon/360.0) * ((double)(1<<24)));
	if (x >= (1<<23))
		x = 0x007fffff;
	else if (x < -(1<<23))
		x = 0x00800000;
	b[0] = (x >> 16) & 0xff;
	b[1] = (x >>  8) & 0xff;
	b[2] =  x        & 0xff;
}

static void
_ts_23_032_store_altitude(double alt, uint8_t *b)
{
	int alt_i = (int)fabs(alt);
	b[0] = ((alt_i >> 8) & 0x7f) | (alt<0.0 ? 0x80 : 0x00);
	b[1] = alt_i & 0xff;
}


	/* Fill methods */

static void
_rrlp_fill_navigation_model_element(
	struct NavModelElement *rrlp_nme,
	struct gps_ephemeris_sv *gps_eph_sv)
{
	struct UncompressedEphemeris *rrlp_eph;

  #if 1
	rrlp_nme->satStatus.present = SatStatus_PR_newSatelliteAndModelUC;
	rrlp_eph = &rrlp_nme->satStatus.choice.newSatelliteAndModelUC;
  #else /* does this make any difference fro the MS !? */
	rrlp_nme->satStatus.present = SatStatus_PR_newNaviModelUC;
	rrlp_eph = &rrlp_nme->satStatus.choice.newNaviModelUC;
  #endif
	
	rrlp_nme->satelliteID = gps_eph_sv->sv_id - 1; /* Dieter: satellite ID is zero based */


	rrlp_eph->ephemCodeOnL2   = gps_eph_sv->code_on_l2;
	rrlp_eph->ephemURA        = gps_eph_sv->sv_ura;
	rrlp_eph->ephemSVhealth   = gps_eph_sv->sv_health;
	rrlp_eph->ephemIODC       = gps_eph_sv->iodc;
	rrlp_eph->ephemL2Pflag    = gps_eph_sv->l2_p_flag;
	rrlp_eph->ephemTgd        = gps_eph_sv->t_gd;
	rrlp_eph->ephemToc        = gps_eph_sv->t_oc;
	rrlp_eph->ephemAF2        = gps_eph_sv->a_f2;
	rrlp_eph->ephemAF1        = gps_eph_sv->a_f1;
	rrlp_eph->ephemAF0        = gps_eph_sv->a_f0;
	rrlp_eph->ephemCrs        = gps_eph_sv->c_rs;
	rrlp_eph->ephemDeltaN     = gps_eph_sv->delta_n;
	rrlp_eph->ephemM0         = gps_eph_sv->m_0;
	rrlp_eph->ephemCuc        = gps_eph_sv->c_uc;
	rrlp_eph->ephemE          = gps_eph_sv->e;
	rrlp_eph->ephemCus        = gps_eph_sv->c_us;
	rrlp_eph->ephemAPowerHalf = gps_eph_sv->a_powhalf;
	rrlp_eph->ephemToe        = gps_eph_sv->t_oe;
	rrlp_eph->ephemFitFlag    = gps_eph_sv->fit_flag;
	rrlp_eph->ephemAODA       = gps_eph_sv->aodo;
	rrlp_eph->ephemCic        = gps_eph_sv->c_ic;
	rrlp_eph->ephemOmegaA0    = gps_eph_sv->omega_0;
	rrlp_eph->ephemCis        = gps_eph_sv->c_is;
	rrlp_eph->ephemI0         = gps_eph_sv->i_0;
	rrlp_eph->ephemCrc        = gps_eph_sv->c_rc;
	rrlp_eph->ephemW          = gps_eph_sv->w;
	rrlp_eph->ephemOmegaADot  = gps_eph_sv->omega_dot;
	rrlp_eph->ephemIDot       = gps_eph_sv->idot;

	rrlp_eph->ephemSF1Rsvd.reserved1 = gps_eph_sv->_rsvd1;
	rrlp_eph->ephemSF1Rsvd.reserved2 = gps_eph_sv->_rsvd2;
	rrlp_eph->ephemSF1Rsvd.reserved3 = gps_eph_sv->_rsvd3;
	rrlp_eph->ephemSF1Rsvd.reserved4 = gps_eph_sv->_rsvd4;
}

static void
_rrlp_fill_almanac_element(
	struct AlmanacElement *rrlp_ae,
	struct gps_almanac_sv *gps_alm_sv)
{
	rrlp_ae->satelliteID = gps_alm_sv->sv_id - 1; /* Dieter: satellite ID is zero based */

	rrlp_ae->almanacE          = gps_alm_sv->e;
	rrlp_ae->alamanacToa       = gps_alm_sv->t_oa;
	rrlp_ae->almanacKsii       = gps_alm_sv->ksii;
	rrlp_ae->almanacOmegaDot   = gps_alm_sv->omega_dot;
	rrlp_ae->almanacSVhealth   = gps_alm_sv->sv_health;
	rrlp_ae->almanacAPowerHalf = gps_alm_sv->a_powhalf;
	rrlp_ae->almanacOmega0     = gps_alm_sv->omega_0;
	rrlp_ae->almanacW          = gps_alm_sv->w;
	rrlp_ae->almanacM0         = gps_alm_sv->m_0;
	rrlp_ae->almanacAF0        = gps_alm_sv->a_f0;
	rrlp_ae->almanacAF1        = gps_alm_sv->a_f1;

}

static void
_rrlp_fill_ionospheric_model(
	struct IonosphericModel *rrlp_iono,
	struct gps_ionosphere_model *gps_iono)
{
	rrlp_iono->alfa0 = gps_iono->alpha_0;
	rrlp_iono->alfa1 = gps_iono->alpha_1;
	rrlp_iono->alfa2 = gps_iono->alpha_2;
	rrlp_iono->alfa3 = gps_iono->alpha_3;
	rrlp_iono->beta0 = gps_iono->beta_0;
	rrlp_iono->beta1 = gps_iono->beta_1;
	rrlp_iono->beta2 = gps_iono->beta_2;
	rrlp_iono->beta3 = gps_iono->beta_3;
}

static void
_rrlp_fill_utc_model(
	struct UTCModel *rrlp_utc,
	struct gps_utc_model *gps_utc)
{
	rrlp_utc->utcA1        = gps_utc->a1;
	rrlp_utc->utcA0        = gps_utc->a0;
	rrlp_utc->utcTot       = gps_utc->t_ot;
	rrlp_utc->utcWNt       = gps_utc->wn_t & 0xff;
	rrlp_utc->utcDeltaTls  = gps_utc->delta_t_ls;
	rrlp_utc->utcWNlsf     = gps_utc->wn_lsf & 0xff;
	rrlp_utc->utcDN        = gps_utc->dn;
	rrlp_utc->utcDeltaTlsf = gps_utc->delta_t_lsf;
	
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcA1);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcA0);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcTot);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcWNt);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcDeltaTls);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcWNlsf);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcDN);
	printf("UTC:  0x%X\n", (unsigned)rrlp_utc->utcDeltaTlsf);
}

/* }}} */


/* ------------------------------------------------------------------------ */
/* RRLP Assistance PDU Generation                                           */
/* ---------------------------------------------------------------------{{{ */

struct PDU *
_rrlp_create_gps_assist_pdu(int refnum, struct GPS_AssistData **o_gps_ad, int iLast)
{
	struct PDU *pdu;
	struct GPS_AssistData *gps_ad;
	MoreAssDataToBeSent_t *moreAssDataToBeSent;

	pdu = calloc(1, sizeof(*pdu));
	if (!pdu)
		return NULL;

	gps_ad = calloc(1, sizeof(*gps_ad));
	if (!gps_ad) {
		free(pdu);
		return NULL;
	}

	moreAssDataToBeSent = calloc(1, sizeof(*moreAssDataToBeSent));
	if (!moreAssDataToBeSent) {
		free(gps_ad);
		free(pdu);
		return NULL;
	}
	/* last message or more messages ? */
	if(iLast) {
		if(asn_long2INTEGER(moreAssDataToBeSent, MoreAssDataToBeSent_noMoreMessages) != 0)
			fprintf(stderr, "encode error\n");		
	} else {
		if(asn_long2INTEGER(moreAssDataToBeSent, MoreAssDataToBeSent_moreMessagesOnTheWay) != 0)
			fprintf(stderr, "encode error\n");		
	}
	
	if (o_gps_ad)
		*o_gps_ad = gps_ad;
		
	pdu->referenceNumber = refnum;
	pdu->component.present = RRLP_Component_PR_assistanceData;
	pdu->component.choice.assistanceData.gps_AssistData = gps_ad;
	pdu->component.choice.assistanceData.moreAssDataToBeSent = moreAssDataToBeSent;

	return pdu;
}

static int
_rrlp_add_ionospheric_model(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad)
{
	struct IonosphericModel *rrlp_iono;

	if (!(gps_ad->fields & GPS_FIELD_IONOSPHERE))
		return -EINVAL;

	rrlp_iono = calloc(1, sizeof(*rrlp_iono));
	if (!rrlp_iono)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.ionosphericModel = rrlp_iono;

	_rrlp_fill_ionospheric_model(rrlp_iono, &gps_ad->ionosphere);

	return 0;
}

static int
_rrlp_add_utc_model(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad)
{
	struct UTCModel *rrlp_utc;

	if (!(gps_ad->fields & GPS_FIELD_UTC))
		return -EINVAL;

	rrlp_utc = calloc(1, sizeof(*rrlp_utc));
	if (!rrlp_utc)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.utcModel = rrlp_utc;

	_rrlp_fill_utc_model(rrlp_utc, &gps_ad->utc);

	return 0;
}

static int
_rrlp_add_reference_location(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad)
{
#if 0 /* old */
	struct RefLocation *rrlp_refloc;

	/* FIXME: Check if info is in gps_ad */

	rrlp_refloc = calloc(1, sizeof(*rrlp_refloc));
	if (!rrlp_refloc)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.refLocation = rrlp_refloc;

	/* FIXME */
	{
		uint8_t gps_loc[] = {
			0x80,			/* Ellipsoid Point with altitude */
	#if 0
			0x48, 0x0f, 0x93,	/* 50.667778 N */
			0x03, 0x47, 0x87,	/* 4.611667 E */
			0x00, 0x72,		/* 114m */
	#else // Dieter
			0x44, 0xEF, 0xEB,
			0x09, 0x33, 0xAD, 
			0x01, 0xEC,
	#endif
		};
		uint8_t *b = malloc(sizeof(gps_loc));
		memcpy(b, gps_loc, sizeof(gps_loc));
		rrlp_refloc->threeDLocation.buf = b;
		rrlp_refloc->threeDLocation.size = sizeof(gps_loc);
	}

	return 0;
	
#else /* new */

	struct RefLocation *rrlp_refloc;
	uint8_t *b;

	if (!(gps_ad->fields & GPS_FIELD_REFPOS))
		return -EINVAL;

	rrlp_refloc = calloc(1, sizeof(*rrlp_refloc));
	if (!rrlp_refloc)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.refLocation = rrlp_refloc;

	b = malloc(9);

	b[0] = 0x80; /* Ellipsoid Point with altitude */
	_ts_23_032_store_latitude(gps_ad->ref_pos.latitude, &b[1]);
	_ts_23_032_store_longitude(gps_ad->ref_pos.longitude, &b[4]);
	_ts_23_032_store_altitude(gps_ad->ref_pos.altitude, &b[7]);

	rrlp_refloc->threeDLocation.buf = b;
	rrlp_refloc->threeDLocation.size = 9;

	return 0;
#endif
}

static int
_rrlp_add_reference_time(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad)
{
#if 0 /* old */
	struct ReferenceTime *rrlp_reftime;

	/* FIXME: Check if info is in gps_ad */

	rrlp_reftime = calloc(1, sizeof(*rrlp_reftime));
	if (!rrlp_reftime)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.referenceTime = rrlp_reftime;

	/* FIXME */
//	rrlp_reftime.gpsTime.gpsTOW23b = g_gps_tow / 80;	/* 23 bits */
//	rrlp_reftime.gpsTime.gpsWeek   = g_gps_week & 0x3ff;	/* 10 bits */

  #if 1 // Dieter
    printf("Time %d\n", (int)time(NULL));
	//rrlp_reftime->gpsTime.gpsTOW23b = (time(NULL) - 1261643144) + 375961;
	rrlp_reftime->gpsTime.gpsTOW23b = (time(NULL) - 1281949530) + 119148;
    printf("GPS TOW %d\n", (int)rrlp_reftime->gpsTime.gpsTOW23b);
    rrlp_reftime->gpsTime.gpsTOW23b = (uint32_t)((double)rrlp_reftime->gpsTime.gpsTOW23b * 12.5 + 0.5) & 0x7FFFFF;
	//rrlp_reftime->gpsTime.gpsWeek = 1563 & 0x3FF; // KW52 2009
	//rrlp_reftime->gpsTime.gpsWeek = 1565 & 0x3FF; // KW1 2010
	rrlp_reftime->gpsTime.gpsWeek = 1597 & 0x3FF; // KW33 2010
  #endif

	return 0;
#else /* new */
	struct ReferenceTime *rrlp_reftime;
	double tow;

	if (!(gps_ad->fields & GPS_FIELD_REFTIME))
		return -EINVAL;

	rrlp_reftime = calloc(1, sizeof(*rrlp_reftime));
	if (!rrlp_reftime)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.referenceTime = rrlp_reftime;

	/* TODO: adjust offset so that MS receives the correct time ? */
	#define MY_OFFSET 0 	
	
	tow = gps_ad->ref_time.tow + (time(NULL) - gps_ad->ref_time.when) + MY_OFFSET;
	printf("TOW = %f\n", tow);
	
	rrlp_reftime->gpsTime.gpsWeek   = gps_ad->ref_time.wn & 0x3ff; /* 10b */
	rrlp_reftime->gpsTime.gpsTOW23b =
		((int)floor(tow / 0.08)) & 0x7fffff;  /* 23b */

	return 0;
#endif
}

static int
_rrlp_add_realtime_integrity(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad)
{
	struct SeqOf_BadSatelliteSet *rrlp_realtime_integrity;

#if 0 /* not yet */	
	if (!(gps_ad->fields & GPS_FIELD_REALTIME_INT))
		return -EINVAL;
#endif		

	rrlp_realtime_integrity = calloc(1, sizeof(*rrlp_realtime_integrity));
	if (!rrlp_realtime_integrity)
		return -ENOMEM;

	rrlp_gps_ad->controlHeader.realTimeIntegrity = rrlp_realtime_integrity;

#if 1 /* TODO */

	SatelliteID_t *sa_id;
	
	sa_id = calloc(1, sizeof(*sa_id));
	
	*sa_id = 63;
		
	ASN_SEQUENCE_ADD(&rrlp_realtime_integrity->list, sa_id);
#endif	

	return 0;
}

static int
_rrlp_add_almanac(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad, int *start, int count)
{
	int i;
	struct Almanac *rrlp_alm;
	struct gps_almanac *gps_alm = &gps_ad->almanac;

	if (!(gps_ad->fields & GPS_FIELD_ALMANAC))
		return -EINVAL;

	rrlp_alm = calloc(1, sizeof(*rrlp_alm));
	if (!rrlp_alm)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.almanac = rrlp_alm;

	rrlp_alm->alamanacWNa = gps_alm->wna;
	if (count == -1)
		count = gps_alm->n_sv - *start;
	for (i=*start; (i<*start+count) && (i<gps_alm->n_sv); i++) {
		struct AlmanacElement *ae;
		ae = calloc(1, sizeof(*ae));
		if (!ae)
			return -ENOMEM;
		_rrlp_fill_almanac_element(ae, &gps_alm->svs[i]);
		ASN_SEQUENCE_ADD(&rrlp_alm->almanacList.list, ae);
	}

	*start = i;

	return i < gps_alm->n_sv;
}

static int
_rrlp_add_ephemeris(
	struct GPS_AssistData *rrlp_gps_ad,
	struct gps_assist_data *gps_ad, int *start, int count, uint64_t mask)
{
	int i, j;
	struct NavigationModel *rrlp_nav;
	struct gps_ephemeris *gps_eph = &gps_ad->ephemeris;

	if (!(gps_ad->fields & GPS_FIELD_EPHEMERIS))
		return -EINVAL;

	rrlp_nav = calloc(1, sizeof(*rrlp_nav));
	if (!rrlp_nav)
		return -ENOMEM;
	rrlp_gps_ad->controlHeader.navigationModel = rrlp_nav;

	if (count == -1)
		count = gps_eph->n_sv - *start;
	for (i=*start,j=0; (j<count) && (i<gps_eph->n_sv); i++) {
		if (!(mask & (1ULL<<(gps_eph->svs[i].sv_id-1)))) /* Dieter: CHECK */
			continue;
		struct NavModelElement *nme;
		nme = calloc(1, sizeof(*nme));
		if (!nme)
			return -ENOMEM;
		_rrlp_fill_navigation_model_element(nme, &gps_eph->svs[i]);
		ASN_SEQUENCE_ADD(&rrlp_nav->navModelList.list, nme);
		j++;
	}

	*start = i;

	return i < gps_eph->n_sv;
}


#define MAX_PDUS 64

int
rrlp_gps_assist_pdus(int refnum,
	struct gps_assist_data *gps_ad, struct rrlp_assist_req *req,
	void **o_pdu, int *o_len, int o_max_pdus)
{
	struct PDU *lst_pdu[MAX_PDUS];
	int lst_cnt = 0;

	struct PDU *rrlp_pdu = NULL;
	struct GPS_AssistData *rrlp_gps_ad = NULL;
	uint32_t re = req->req_elems;
	int i, rv = 0;

	/* IonosphericModel, UTCModel, RefLocation, ReferenceTime */
	if (re & (RRLP_AR_IONO_MODEL |
	          RRLP_AR_UTC_MODEL |
	          RRLP_AR_REF_TIME |
	          RRLP_AR_REF_LOC |
	          RRLP_AR_REALTIME_INT))
	{
		int pdu_has_data = 0;

		rrlp_pdu = _rrlp_create_gps_assist_pdu(refnum, &rrlp_gps_ad, 0);
		if (!rrlp_pdu) {
			rv = -ENOMEM;
			goto error;
		}

#if 1 /* enable/disable component */
		if (re & RRLP_AR_IONO_MODEL) {
			printf("+ IONO_MODEL\n");
			if (!_rrlp_add_ionospheric_model(rrlp_gps_ad, gps_ad))
				pdu_has_data = 1;
		}
#endif
#if 1 /* enable/disable component */
		if (re & RRLP_AR_UTC_MODEL) {
			printf("+ UTC_MODEL\n");
			if (!_rrlp_add_utc_model(rrlp_gps_ad, gps_ad))
				pdu_has_data = 1;
		}
#endif
#if 1 /* enable/disable component */
		if (re & RRLP_AR_REF_TIME) {
			printf("+ REF_TIME\n");
			if (!_rrlp_add_reference_time(rrlp_gps_ad, gps_ad))
				pdu_has_data = 1;
		}
#endif
#if 1 /* enable/disable component */
		if (re & RRLP_AR_REF_LOC) {
			printf("+ REF_LOC\n");
			if (!_rrlp_add_reference_location(rrlp_gps_ad, gps_ad))
				pdu_has_data = 1;
		}
#endif
#if 0 /* enable/disable component (skip this as it is for now a dummy list only) */
		if (re & RRLP_AR_REALTIME_INT) {
			printf("+ REALTIME_INTEGRITY\n");
			if (!_rrlp_add_realtime_integrity(rrlp_gps_ad, gps_ad))
				pdu_has_data = 1;
		}
#endif

		if (pdu_has_data) {
			lst_pdu[lst_cnt++] = rrlp_pdu;
			rrlp_pdu = NULL;
		}
	}
#if 1 /* enable/disable component */
	/* Almanac */
	if (re & RRLP_AR_ALMANAC) {
		i = 0;
		do {
			if (!(gps_ad->fields & GPS_FIELD_ALMANAC))
				break;

			printf("+ ALMANAC\n");
				
			if (!rrlp_pdu) {
				rrlp_pdu = _rrlp_create_gps_assist_pdu(refnum, &rrlp_gps_ad, 0);
				if (!rrlp_pdu) {
					rv = -ENOMEM;
					goto error;
				}
			}

			/* adjust count so that messages fit in a single PDU */
			rv = _rrlp_add_almanac(rrlp_gps_ad, gps_ad, &i, 10);
			if (rv < 0)
				goto error;

			lst_pdu[lst_cnt++] = rrlp_pdu;
			rrlp_pdu = NULL;
		} while (rv);
	}
#endif
#if 1 /* enable/disable component */
	/* Ephemeris */
	if (re & RRLP_AR_EPHEMERIS) {
		i = 0;
		do {
			if (!(gps_ad->fields & GPS_FIELD_EPHEMERIS))
				break;

			printf("+ EPHEMERIS\n");
				
			if (!rrlp_pdu) {
				rrlp_pdu = _rrlp_create_gps_assist_pdu(refnum, &rrlp_gps_ad, 0);
				if (!rrlp_pdu) {
					rv = -ENOMEM;
					goto error;
				}
			}
#if 1 /* two sets in one PDS to be not larger than maximum message size */
			rv = _rrlp_add_ephemeris(rrlp_gps_ad, gps_ad, &i, 2, req->eph_svs);
#elif 0 /* three sets in one PDU, too large */			
			rv = _rrlp_add_ephemeris(rrlp_gps_ad, gps_ad, &i, 3, req->eph_svs);
#elif 0 /* all sets in one PDU, too large */
			rv = _rrlp_add_ephemeris(rrlp_gps_ad, gps_ad, &i, -1, req->eph_svs);
#endif
			lst_pdu[lst_cnt++] = rrlp_pdu;
			rrlp_pdu = NULL;

		} while (rv);
	}
#endif

	/* set last message flag */
    if(asn_long2INTEGER(lst_pdu[lst_cnt - 1]->component.choice.assistanceData.moreAssDataToBeSent, MoreAssDataToBeSent_noMoreMessages) != 0)
		fprintf(stderr, "encode error\n");
    
	/* Serialize & Release all PDUs */
	for (i=0; i<lst_cnt && i<o_max_pdus; i++) {
		/* Debugging, dump PDU */
		asn_fprint(stdout, &asn_DEF_PDU, lst_pdu[i]);
		rv = uper_encode_to_new_buffer(&asn_DEF_PDU, NULL, lst_pdu[i], &o_pdu[i]);
		if (rv < 0) {
			printf("uper_encode_to_new_buffer error %d (%d)\n", rv, i);
			goto error;
		}
		o_len[i] = rv;
	}

	return lst_cnt;

	/* Release ASN.1 objects */
error:
	if (rrlp_pdu)
		asn_DEF_PDU.free_struct(&asn_DEF_PDU, (void*)rrlp_pdu, 0);

	for (i=0; i<lst_cnt; i++)
		asn_DEF_PDU.free_struct(&asn_DEF_PDU, lst_pdu[i], 0);

	return rv;
}

/* }}} */

