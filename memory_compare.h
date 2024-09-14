#ifndef MEMORY_COMPARE_H
#define MEMORY_COMPARE_H

int cmp_key(const void *buf1, const void *buf2, unsigned int size);
int cmp_image_len(const void *buf1, const void *buf2, unsigned int size);
int cmp_image_code(const void *buf1, const void *buf2, unsigned int size);
int cmp_modulus(const void *buf1, const void *buf2, unsigned int size);
int cmp_signature(const void *buf1, const void *buf2, unsigned int size);
int cmp_hash_decrypt(const void *buf1, const void *buf2, unsigned int size);

#endif // MEMORY_COMPARE_H
