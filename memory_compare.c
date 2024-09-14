#include "mask_rom.h"

int cmp_key(const void *buf1, const void *buf2, unsigned int size) {
  __CPROVER_assert(
      size == (3072 + 32) / 8,
      "Assert: Size should be equal to size of modulus and exponent");

  const char *cbuf1 = (char *)buf1;
  const char *cbuf2 = (char *)buf2;

  int mismatch = 0;
  for (int i = 0; i < size; i++) {
    if (*cbuf1 != *cbuf2) {
      mismatch = 1;
      break;
    }
    cbuf1++;
    cbuf2++;
  }

  return mismatch; // 0 is equal, 1 is not equal.
}

int cmp_image_len(const void *buf1, const void *buf2, unsigned int size) {
  __CPROVER_assert(
      size == 4,
      "Assert: Size should be equal to size of image_len variable type");

  const char *cbuf1 = (char *)buf1;
  const char *cbuf2 = (char *)buf2;

  int mismatch = 0;
  for (int i = 0; i < size; i++) {
    if (*cbuf1 != *cbuf2) {
      mismatch = 1;
      break;
    }
    cbuf1++;
    cbuf2++;
  }

  return mismatch; // 0 is equal, 1 is not equal.
}

int cmp_image_code(const void *buf1, const void *buf2, unsigned int size) {
  __CPROVER_assert(
      size <= MAX_IMAGE_LENGTH && size > 0,
      "Assert: Size should be less than or equal to MAX_IMAGE_LENGTH");

  const char *cbuf1 = (char *)buf1;
  const char *cbuf2 = (char *)buf2;

  int mismatch = 0;
  for (int i = 0; i < size; i++) {
    if (*cbuf1 != *cbuf2) {
      mismatch = 1;
      break;
    }
    cbuf1++;
    cbuf2++;
  }

  return mismatch; // 0 is equal, 1 is not equal.
}

int cmp_modulus(const void *buf1, const void *buf2, unsigned int size) {
  __CPROVER_assert(size == 3072 / 8,
                   "Assert: Size should be equal to size of modulus");

  const char *cbuf1 = (char *)buf1;
  const char *cbuf2 = (char *)buf2;

  int mismatch = 0;
  for (int i = 0; i < size; i++) {
    if (*cbuf1 != *cbuf2) {
      mismatch = 1;
      break;
    }
    cbuf1++;
    cbuf2++;
  }

  return mismatch; // 0 is equal, 1 is not equal.
}

int cmp_signature(const void *buf1, const void *buf2, unsigned int size) {
  __CPROVER_assert(size == 3072 / 8,
                   "Assert: Size should be equal to size of signature");

  const char *cbuf1 = (char *)buf1;
  const char *cbuf2 = (char *)buf2;

  int mismatch = 0;
  for (int i = 0; i < size; i++) {
    if (*cbuf1 != *cbuf2) {
      mismatch = 1;
      break;
    }
    cbuf1++;
    cbuf2++;
  }

  return mismatch; // 0 is equal, 1 is not equal.
}

int cmp_hash_decrypt(const void *buf1, const void *buf2, unsigned int size) {
  __CPROVER_assert(size == 256 / 8,
                   "Assert: Size should be equal to size of hash");

  const char *cbuf1 = (char *)buf1;
  const char *cbuf2 = (char *)buf2;

  int mismatch = 0;
  for (int i = 0; i < size; i++) {
    if (*cbuf1 != *cbuf2) {
      mismatch = 1;
      break;
    }
    cbuf1++;
    cbuf2++;
  }

  return mismatch; // 0 is equal, 1 is not equal.
}
