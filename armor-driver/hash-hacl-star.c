#include <string.h>
#include "internal/Hacl_Hash_SHA2.h"
#include "internal/Hacl_Hash_SHA1.h"
#include <stdio.h>
#include <stdint.h>

static inline void sha256_init(uint32_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = Hacl_Impl_SHA2_Generic_h256[i];
    os[i] = x;
  }
}

static inline void sha256_update(uint8_t *b, uint32_t *hash)
{
  uint32_t hash_old[8U] = { 0U };
  uint32_t ws[16U] = { 0U };
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint32_t));
  uint8_t *b10 = b;
  uint32_t u = load32_be(b10);
  ws[0U] = u;
  uint32_t u0 = load32_be(b10 + (uint32_t)4U);
  ws[1U] = u0;
  uint32_t u1 = load32_be(b10 + (uint32_t)8U);
  ws[2U] = u1;
  uint32_t u2 = load32_be(b10 + (uint32_t)12U);
  ws[3U] = u2;
  uint32_t u3 = load32_be(b10 + (uint32_t)16U);
  ws[4U] = u3;
  uint32_t u4 = load32_be(b10 + (uint32_t)20U);
  ws[5U] = u4;
  uint32_t u5 = load32_be(b10 + (uint32_t)24U);
  ws[6U] = u5;
  uint32_t u6 = load32_be(b10 + (uint32_t)28U);
  ws[7U] = u6;
  uint32_t u7 = load32_be(b10 + (uint32_t)32U);
  ws[8U] = u7;
  uint32_t u8 = load32_be(b10 + (uint32_t)36U);
  ws[9U] = u8;
  uint32_t u9 = load32_be(b10 + (uint32_t)40U);
  ws[10U] = u9;
  uint32_t u10 = load32_be(b10 + (uint32_t)44U);
  ws[11U] = u10;
  uint32_t u11 = load32_be(b10 + (uint32_t)48U);
  ws[12U] = u11;
  uint32_t u12 = load32_be(b10 + (uint32_t)52U);
  ws[13U] = u12;
  uint32_t u13 = load32_be(b10 + (uint32_t)56U);
  ws[14U] = u13;
  uint32_t u14 = load32_be(b10 + (uint32_t)60U);
  ws[15U] = u14;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint32_t k_t = Hacl_Impl_SHA2_Generic_k224_256[(uint32_t)16U * i0 + i];
      uint32_t ws_t = ws[i];
      uint32_t a0 = hash[0U];
      uint32_t b0 = hash[1U];
      uint32_t c0 = hash[2U];
      uint32_t d0 = hash[3U];
      uint32_t e0 = hash[4U];
      uint32_t f0 = hash[5U];
      uint32_t g0 = hash[6U];
      uint32_t h02 = hash[7U];
      uint32_t k_e_t = k_t;
      uint32_t
      t1 =
        h02
        +
          ((e0 << (uint32_t)26U | e0 >> (uint32_t)6U)
          ^
            ((e0 << (uint32_t)21U | e0 >> (uint32_t)11U)
            ^ (e0 << (uint32_t)7U | e0 >> (uint32_t)25U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint32_t
      t2 =
        ((a0 << (uint32_t)30U | a0 >> (uint32_t)2U)
        ^
          ((a0 << (uint32_t)19U | a0 >> (uint32_t)13U)
          ^ (a0 << (uint32_t)10U | a0 >> (uint32_t)22U)))
        + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
      uint32_t a1 = t1 + t2;
      uint32_t b1 = a0;
      uint32_t c1 = b0;
      uint32_t d1 = c0;
      uint32_t e1 = d0 + t1;
      uint32_t f1 = e0;
      uint32_t g1 = f0;
      uint32_t h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)3U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint32_t t16 = ws[i];
        uint32_t t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        uint32_t t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        uint32_t t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        uint32_t
        s1 =
          (t2 << (uint32_t)15U | t2 >> (uint32_t)17U)
          ^ ((t2 << (uint32_t)13U | t2 >> (uint32_t)19U) ^ t2 >> (uint32_t)10U);
        uint32_t
        s0 =
          (t15 << (uint32_t)25U | t15 >> (uint32_t)7U)
          ^ ((t15 << (uint32_t)14U | t15 >> (uint32_t)18U) ^ t15 >> (uint32_t)3U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

static inline void sha256_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  uint32_t blocks = len / (uint32_t)64U;
  for (uint32_t i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)64U;
    sha256_update(mb, st);
  }
}

static inline void
sha256_update_last(uint64_t totlen, uint32_t len, uint8_t *b, uint32_t *hash)
{
  uint32_t blocks;
  if (len + (uint32_t)8U + (uint32_t)1U <= (uint32_t)64U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)64U;
  uint8_t last[128U] = { 0U };
  uint8_t totlen_buf[8U] = { 0U };
  uint64_t total_len_bits = totlen << (uint32_t)3U;
  store64_be(totlen_buf, total_len_bits);
  uint8_t *b0 = b;
  memcpy(last, b0, len * sizeof (uint8_t));
  last[len] = (uint8_t)0x80U;
  memcpy(last + fin - (uint32_t)8U, totlen_buf, (uint32_t)8U * sizeof (uint8_t));
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)64U;
  uint8_t *l0 = last00;
  uint8_t *l1 = last10;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  uint8_t *last0 = lb0;
  uint8_t *last1 = lb1;
  sha256_update(last0, hash);
  if (blocks > (uint32_t)1U)
  {
    sha256_update(last1, hash);
  }
}

static inline void sha256_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store32_be(hbuf + i * (uint32_t)4U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)32U * sizeof (uint8_t));
}

static inline void sha224_init(uint32_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint32_t *os = hash;
    uint32_t x = Hacl_Impl_SHA2_Generic_h224[i];
    os[i] = x;
  }
}

static inline void sha224_update_nblocks(uint32_t len, uint8_t *b, uint32_t *st)
{
  sha256_update_nblocks(len, b, st);
}

static void sha224_update_last(uint64_t totlen, uint32_t len, uint8_t *b, uint32_t *st)
{
  sha256_update_last(totlen, len, b, st);
}

static inline void sha224_finish(uint32_t *st, uint8_t *h)
{
  uint8_t hbuf[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store32_be(hbuf + i * (uint32_t)4U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)28U * sizeof (uint8_t));
}

static void sha512_init(uint64_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = Hacl_Impl_SHA2_Generic_h512[i];
    os[i] = x;
  }
}

static inline void sha512_update(uint8_t *b, uint64_t *hash)
{
  uint64_t hash_old[8U] = { 0U };
  uint64_t ws[16U] = { 0U };
  memcpy(hash_old, hash, (uint32_t)8U * sizeof (uint64_t));
  uint8_t *b10 = b;
  uint64_t u = load64_be(b10);
  ws[0U] = u;
  uint64_t u0 = load64_be(b10 + (uint32_t)8U);
  ws[1U] = u0;
  uint64_t u1 = load64_be(b10 + (uint32_t)16U);
  ws[2U] = u1;
  uint64_t u2 = load64_be(b10 + (uint32_t)24U);
  ws[3U] = u2;
  uint64_t u3 = load64_be(b10 + (uint32_t)32U);
  ws[4U] = u3;
  uint64_t u4 = load64_be(b10 + (uint32_t)40U);
  ws[5U] = u4;
  uint64_t u5 = load64_be(b10 + (uint32_t)48U);
  ws[6U] = u5;
  uint64_t u6 = load64_be(b10 + (uint32_t)56U);
  ws[7U] = u6;
  uint64_t u7 = load64_be(b10 + (uint32_t)64U);
  ws[8U] = u7;
  uint64_t u8 = load64_be(b10 + (uint32_t)72U);
  ws[9U] = u8;
  uint64_t u9 = load64_be(b10 + (uint32_t)80U);
  ws[10U] = u9;
  uint64_t u10 = load64_be(b10 + (uint32_t)88U);
  ws[11U] = u10;
  uint64_t u11 = load64_be(b10 + (uint32_t)96U);
  ws[12U] = u11;
  uint64_t u12 = load64_be(b10 + (uint32_t)104U);
  ws[13U] = u12;
  uint64_t u13 = load64_be(b10 + (uint32_t)112U);
  ws[14U] = u13;
  uint64_t u14 = load64_be(b10 + (uint32_t)120U);
  ws[15U] = u14;
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)5U; i0++)
  {
    for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
    {
      uint64_t k_t = Hacl_Impl_SHA2_Generic_k384_512[(uint32_t)16U * i0 + i];
      uint64_t ws_t = ws[i];
      uint64_t a0 = hash[0U];
      uint64_t b0 = hash[1U];
      uint64_t c0 = hash[2U];
      uint64_t d0 = hash[3U];
      uint64_t e0 = hash[4U];
      uint64_t f0 = hash[5U];
      uint64_t g0 = hash[6U];
      uint64_t h02 = hash[7U];
      uint64_t k_e_t = k_t;
      uint64_t
      t1 =
        h02
        +
          ((e0 << (uint32_t)50U | e0 >> (uint32_t)14U)
          ^
            ((e0 << (uint32_t)46U | e0 >> (uint32_t)18U)
            ^ (e0 << (uint32_t)23U | e0 >> (uint32_t)41U)))
        + ((e0 & f0) ^ (~e0 & g0))
        + k_e_t
        + ws_t;
      uint64_t
      t2 =
        ((a0 << (uint32_t)36U | a0 >> (uint32_t)28U)
        ^
          ((a0 << (uint32_t)30U | a0 >> (uint32_t)34U)
          ^ (a0 << (uint32_t)25U | a0 >> (uint32_t)39U)))
        + ((a0 & b0) ^ ((a0 & c0) ^ (b0 & c0)));
      uint64_t a1 = t1 + t2;
      uint64_t b1 = a0;
      uint64_t c1 = b0;
      uint64_t d1 = c0;
      uint64_t e1 = d0 + t1;
      uint64_t f1 = e0;
      uint64_t g1 = f0;
      uint64_t h12 = g0;
      hash[0U] = a1;
      hash[1U] = b1;
      hash[2U] = c1;
      hash[3U] = d1;
      hash[4U] = e1;
      hash[5U] = f1;
      hash[6U] = g1;
      hash[7U] = h12;
    }
    if (i0 < (uint32_t)4U)
    {
      for (uint32_t i = (uint32_t)0U; i < (uint32_t)16U; i++)
      {
        uint64_t t16 = ws[i];
        uint64_t t15 = ws[(i + (uint32_t)1U) % (uint32_t)16U];
        uint64_t t7 = ws[(i + (uint32_t)9U) % (uint32_t)16U];
        uint64_t t2 = ws[(i + (uint32_t)14U) % (uint32_t)16U];
        uint64_t
        s1 =
          (t2 << (uint32_t)45U | t2 >> (uint32_t)19U)
          ^ ((t2 << (uint32_t)3U | t2 >> (uint32_t)61U) ^ t2 >> (uint32_t)6U);
        uint64_t
        s0 =
          (t15 << (uint32_t)63U | t15 >> (uint32_t)1U)
          ^ ((t15 << (uint32_t)56U | t15 >> (uint32_t)8U) ^ t15 >> (uint32_t)7U);
        ws[i] = s1 + t7 + s0 + t16;
      }
    }
  }
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = hash[i] + hash_old[i];
    os[i] = x;
  }
}

static inline void sha512_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  uint32_t blocks = len / (uint32_t)128U;
  for (uint32_t i = (uint32_t)0U; i < blocks; i++)
  {
    uint8_t *b0 = b;
    uint8_t *mb = b0 + i * (uint32_t)128U;
    sha512_update(mb, st);
  }
}

static inline void
sha512_update_last(FStar_UInt128_uint128 totlen, uint32_t len, uint8_t *b, uint64_t *hash)
{
  uint32_t blocks;
  if (len + (uint32_t)16U + (uint32_t)1U <= (uint32_t)128U)
  {
    blocks = (uint32_t)1U;
  }
  else
  {
    blocks = (uint32_t)2U;
  }
  uint32_t fin = blocks * (uint32_t)128U;
  uint8_t last[256U] = { 0U };
  uint8_t totlen_buf[16U] = { 0U };
  FStar_UInt128_uint128 total_len_bits = FStar_UInt128_shift_left(totlen, (uint32_t)3U);
  store128_be(totlen_buf, total_len_bits);
  uint8_t *b0 = b;
  memcpy(last, b0, len * sizeof (uint8_t));
  last[len] = (uint8_t)0x80U;
  memcpy(last + fin - (uint32_t)16U, totlen_buf, (uint32_t)16U * sizeof (uint8_t));
  uint8_t *last00 = last;
  uint8_t *last10 = last + (uint32_t)128U;
  uint8_t *l0 = last00;
  uint8_t *l1 = last10;
  uint8_t *lb0 = l0;
  uint8_t *lb1 = l1;
  uint8_t *last0 = lb0;
  uint8_t *last1 = lb1;
  sha512_update(last0, hash);
  if (blocks > (uint32_t)1U)
  {
    sha512_update(last1, hash);
  }
}

static inline void sha512_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store64_be(hbuf + i * (uint32_t)8U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)64U * sizeof (uint8_t));
}

static inline void sha384_init(uint64_t *hash)
{
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    uint64_t *os = hash;
    uint64_t x = Hacl_Impl_SHA2_Generic_h384[i];
    os[i] = x;
  }
}

static inline void sha384_update_nblocks(uint32_t len, uint8_t *b, uint64_t *st)
{
  sha512_update_nblocks(len, b, st);
}

static void
sha384_update_last(FStar_UInt128_uint128 totlen, uint32_t len, uint8_t *b, uint64_t *st)
{
  sha512_update_last(totlen, len, b, st);
}

static inline void sha384_finish(uint64_t *st, uint8_t *h)
{
  uint8_t hbuf[64U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)8U; i++)
  {
    store64_be(hbuf + i * (uint32_t)8U, st[i]);
  }
  memcpy(h, hbuf, (uint32_t)48U * sizeof (uint8_t));
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 32 bytes.
*/
static void hash_256(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint32_t st[8U] = { 0U };
  sha256_init(st);
  uint32_t rem = input_len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)input_len;
  sha256_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)64U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha256_update_last(len_, rem, lb, st);
  sha256_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 28 bytes.
*/
static void hash_224(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint32_t st[8U] = { 0U };
  sha224_init(st);
  uint32_t rem = input_len % (uint32_t)64U;
  uint64_t len_ = (uint64_t)input_len;
  sha224_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)64U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha224_update_last(len_, rem, lb, st);
  sha224_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 64 bytes.
*/
static void hash_512(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint64_t st[8U] = { 0U };
  sha512_init(st);
  uint32_t rem = input_len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  sha512_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)128U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha512_update_last(len_, rem, lb, st);
  sha512_finish(st, rb);
}

/**
Hash `input`, of len `input_len`, into `dst`, an array of 48 bytes.
*/
static void hash_384(uint8_t *input, uint32_t input_len, uint8_t *dst)
{
  uint8_t *ib = input;
  uint8_t *rb = dst;
  uint64_t st[8U] = { 0U };
  sha384_init(st);
  uint32_t rem = input_len % (uint32_t)128U;
  FStar_UInt128_uint128 len_ = FStar_UInt128_uint64_to_uint128((uint64_t)input_len);
  sha384_update_nblocks(input_len, ib, st);
  uint32_t rem1 = input_len % (uint32_t)128U;
  uint8_t *b0 = ib;
  uint8_t *lb = b0 + input_len - rem1;
  sha384_update_last(len_, rem, lb, st);
  sha384_finish(st, rb);
}

void hexStringToBytes(const char *hexString, uint8_t *outputBytes) {

    size_t len = strlen(hexString);
    for (size_t i = 0; i < len; i += 2) {
        sscanf(hexString + i, "%2hhx", &outputBytes[i / 2]);
    }
}

void main(int argc, char *argv[]) {
    if (argc != 3) {
        printf("Usage: %s <input_string> <hash_size>\n", argv[0]);
        return;
    }
    
    char *hex_input = argv[1];
    size_t input_length = strlen(hex_input) / 2;

    uint8_t input_data[input_length];
    hexStringToBytes(hex_input, input_data);

    uint8_t output_hash[32];

    const char *algorithm = argv[2];

    if (strcmp(algorithm, "sha256") == 0) {
        hash_256(input_data, input_length, output_hash);
    } else if (strcmp(algorithm, "sha384") == 0) {
        hash_384(input_data, input_length, output_hash);
    } else if (strcmp(algorithm, "sha512") == 0) {
        hash_512(input_data, input_length, output_hash);
    } else if (strcmp(algorithm, "sha224") == 0) {
        hash_224(input_data, input_length, output_hash);
    } else if (strcmp(algorithm, "sha1") == 0) {
        Hacl_Hash_SHA1_legacy_hash(input_data, input_length, output_hash);
    } else {
        printf("Unsupported hash algorithm\n");
        return;
    }

    for (int i = 0; i < sizeof(output_hash); i++) {
        printf("%02x", output_hash[i]);
    }
}