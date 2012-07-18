# !! adjust as needed !!
ASN1C=/usr/local/bin/asn1c
ASN1_INCLUDE=/usr/src/asn1c/skeletons

CC=gcc
# -DEMIT_ASN_DEBUG=1 ??
CFLAGS=-I$(ASN1_INCLUDE) -I./asn1_gen -O3 -Wall

ASN1_FILES=$(wildcard asn1/*.asn)

all: rrlp-serv

rrlp-serv: librrlp-asn1.a main.o rrlp.o ubx.o ubx-parse.o gps.o
	$(CC) $(CFLAGS) -o $@ main.o rrlp.o ubx.o ubx-parse.o gps.o -L. -lrrlp-asn1
	
#
# ASN1 file autogeneration (need recursive makefile call)
#

ASN1_SOURCES = $(wildcard asn1_gen/*.c)
ASN1_OBJECTS = $(ASN1_SOURCES:.c=.o)
	
# -fnative-types ??

librrlp-asn1.a: $(ASN1_FILES)
	mkdir -p asn1_gen && \
	cd asn1_gen && \
	$(ASN1C) -fskeletons-copy -gen-PER $(addprefix ../,$^) && \
	rm converter-sample.c Makefile.am.sample && \
	$(ASN1C) -gen-PER $(addprefix ../,$^)
	@$(MAKE) librrlp-asn1.a.submake

librrlp-asn1.a.submake: $(ASN1_OBJECTS)
	$(AR) rcs librrlp-asn1.a $^

.PHONY: librrlp-asn1.a.submake
	
clean:
	rm -Rf asn1_gen
	rm -f *.o rrlp-serv rrlp-serv.exe test-clnt test-clnt.exe

