/*********************************************************************
 * Filename: sha256.h
 * Author: Brad Conte (brad AT bradconte.com)
 * Copyright:
 * Disclaimer: This code is presented "as is" without any guarantees.
 * Details: Defines the API for the corresponding SHA1 implementation.
 *********************************************************************/

#ifndef SHA256_H
#define SHA256_H

/*************************** HEADER FILES ***************************/
#include "mask_rom.h"
#include <stddef.h>

/****************************** MACROS ******************************/
#define SHA2_256_BLOCK_SIZE 32 // SHA256 outputs a 32 byte digest
#define HMAC_KEY_SIZE 32       // HMAC key is 32 bytes

/**************************** DATA TYPES ****************************/
typedef unsigned char BYTE; // 8-bit byte
typedef unsigned int WORD;  // 32-bit word, change to "long" for 16-bit machines

typedef struct {
  BYTE data[64];
  WORD datalen;
  unsigned long long bitlen;
  WORD state[8];
} SHA2_256_CTX;

/*********************** FUNCTION DECLARATIONS **********************/
void HMAC_SHA2_256_init(SHA2_256_CTX *ctx);
void HMAC_SHA2_256_update(SHA2_256_CTX *ctx, const BYTE data[], size_t len);
void HMAC_SHA2_256_final(SHA2_256_CTX *ctx, BYTE hash[]);
BYTE *HMAC_SHA2_256(BYTE key[], BYTE mes[], int size,
                    rom_ext_manifest_t __current_rom_ext_mf);

#endif // SHA256_H
