#include "hmac.h"
#include "memory_compare.h"

BYTE *HMAC_SHA2_256(BYTE key[], BYTE mes[], int size,
                    rom_ext_manifest_t __current_rom_ext_mf) {
  int __expected_size = sizeof(__current_rom_ext_mf.pub_signature_key) +
                        sizeof(__current_rom_ext_mf.image_length) +
                        __current_rom_ext_mf.image_length;

  __CPROVER_assert(cmp_key(mes, &__current_rom_ext_mf.pub_signature_key,
                           sizeof(__current_rom_ext_mf.pub_signature_key)) == 0,
                   "PROPERTY 4: Message contains the key");

  __CPROVER_assert(
      cmp_image_len(mes + sizeof(__current_rom_ext_mf.pub_signature_key),
                    &__current_rom_ext_mf.image_length,
                    sizeof(__current_rom_ext_mf.image_length)) == 0,
      "PROPERTY 4: Message contains the Image length");

  __CPROVER_assert(
      cmp_image_code(mes + sizeof(__current_rom_ext_mf.pub_signature_key) +
                         sizeof(__current_rom_ext_mf.image_length),
                     __current_rom_ext_mf.image_code,
                     __current_rom_ext_mf.image_length) == 0,
      "PROPERTY 4: Message contains the Image code");

  __CPROVER_assert(size == __expected_size,
                   "PROPERTY 4: Message size parameter is as expected.");

  __CPROVER_assert(__CPROVER_OBJECT_SIZE(mes) == __expected_size,
                   "PROPERTY 4: Size of message is as expected.");

  char *hash = malloc(256 / 8); // Model it to be ok for PROPERTY 5

  __CPROVER_assert(__CPROVER_OBJECT_SIZE(hash) == 256 / 8,
                   "PROPERTY 3: Hash is 256 bits");

  __CPROVER_assert(__CPROVER_r_ok(hash, 256 / 8),
                   "PROPERTY 3: hash is in readable address");

  __REACHABILITY_CHECK

  return hash;
}
