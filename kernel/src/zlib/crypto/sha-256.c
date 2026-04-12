// SPDX-FileCopyrightText: 2017 Ryad BENADJILA <ryadbenadjila@gmail.com>
// SPDX-FileCopyrightText: 2017 Arnaud EBALARD <arnaud.ebalard@ssi.gouv.fr>
// SPDX-FileCopyrightText: 2017 Jean-Pierre FLORI <jean-pierre.flori@ssi.gouv.fr>
// SPDX-FileCopyrightText: 2026 H2Lab Development Team
// SPDX-License-Identifier: BSD-2-Clause

#include <sentry/zlib/crypto.h>
#include <sentry/zlib/string.h>

#if CONFIG_SECU_METADATA_SHA256_CHECK

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef u64 word_t;

#define WORD(A) ((word_t)(A))

#define EG(cond, lbl) do { if (cond) { goto lbl; } } while (0)
#define MUST_HAVE(cond, ret, lbl) do { if (!(cond)) { ret = -1; goto lbl; } } while (0)

#define SHA256_HASH_MAGIC ((word_t)(0x11299a2b32098412ULL))
#define SHA256_HASH_CHECK_INITIALIZED(A, ret, err) \
    MUST_HAVE((((void *)(A)) != NULL) && ((A)->magic == SHA256_HASH_MAGIC), ret, err)

#define GET_UINT32_BE(n, b, i)                           \
do {                                                      \
    (n) =     (((u32)(b)[(i)]) << 24)                    \
            | (((u32)(b)[(i) + 1]) << 16)                \
            | (((u32)(b)[(i) + 2]) << 8)                 \
            | (((u32)(b)[(i) + 3]));                     \
} while (0)

#define PUT_UINT32_BE(n, b, i)      \
do {                                 \
    (b)[(i)] = (u8)((n) >> 24);      \
    (b)[(i) + 1] = (u8)((n) >> 16);  \
    (b)[(i) + 2] = (u8)((n) >> 8);   \
    (b)[(i) + 3] = (u8)((n));        \
} while (0)

#define PUT_UINT64_BE(n, b, i)      \
do {                                 \
    (b)[(i)] = (u8)((n) >> 56);      \
    (b)[(i) + 1] = (u8)((n) >> 48);  \
    (b)[(i) + 2] = (u8)((n) >> 40);  \
    (b)[(i) + 3] = (u8)((n) >> 32);  \
    (b)[(i) + 4] = (u8)((n) >> 24);  \
    (b)[(i) + 5] = (u8)((n) >> 16);  \
    (b)[(i) + 6] = (u8)((n) >> 8);   \
    (b)[(i) + 7] = (u8)((n));        \
} while (0)

#define CH(x, y, z) (((x) & (y)) ^ ((~(x)) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))

#define UPDATEW(w, i, sha_type) ((w)[(i)] = SIGMA_MIN1_##sha_type((w)[(i)-2]) + (w)[(i)-7] + SIGMA_MIN0_##sha_type((w)[(i)-15]) + (w)[(i)-16])

#define SHA2CORE(a, b, c, d, e, f, g, h, w, k, sha_word_type, sha_type) do {  \
    sha_word_type t1, t2;                                                        \
    t1 = (h) + SIGMA_MAJ1_##sha_type((e)) + CH((e), (f), (g)) + (k) + (w);      \
    t2 = SIGMA_MAJ0_##sha_type((a)) + MAJ((a), (b), (c));                        \
    (h) = (g);                                                                    \
    (g) = (f);                                                                    \
    (f) = (e);                                                                    \
    (e) = (d) + t1;                                                               \
    (d) = (c);                                                                    \
    (c) = (b);                                                                    \
    (b) = (a);                                                                    \
    (a) = t1 + t2;                                                                \
} while (0)

#define SHR_SHA256(x, n) (((u32)(x)) >> (n))
#define ROTR_SHA256(x, n) ((((u32)(x)) >> (n)) | (((u32)(x)) << (32 - (n))))
#define SIGMA_MAJ0_SHA256(x) (ROTR_SHA256(x, 2) ^ ROTR_SHA256(x, 13) ^ ROTR_SHA256(x, 22))
#define SIGMA_MAJ1_SHA256(x) (ROTR_SHA256(x, 6) ^ ROTR_SHA256(x, 11) ^ ROTR_SHA256(x, 25))
#define SIGMA_MIN0_SHA256(x) (ROTR_SHA256(x, 7) ^ ROTR_SHA256(x, 18) ^ SHR_SHA256(x, 3))
#define SIGMA_MIN1_SHA256(x) (ROTR_SHA256(x, 17) ^ ROTR_SHA256(x, 19) ^ SHR_SHA256(x, 10))
#define SHA2CORE_SHA256(a, b, c, d, e, f, g, h, w, k) \
    SHA2CORE(a, b, c, d, e, f, g, h, w, k, u32, SHA256)
#define UPDATEW_SHA256(w, i) UPDATEW(w, i, SHA256)

static const u32 K_SHA256[] = {
    0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5,
    0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5,
    0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3,
    0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174,
    0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC,
    0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
    0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7,
    0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967,
    0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13,
    0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
    0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3,
    0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
    0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5,
    0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
    0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
    0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2,
};

/* SHA-2 core processing */
/*@
    requires ctx != \null;
    requires data != \null;
    requires \valid(ctx);
    requires \initialized(data + (0 .. SHA256_BLOCK_SIZE - 1));
    requires \valid_read(data + (0 .. SHA256_BLOCK_SIZE - 1));
    requires ctx->magic == SHA256_HASH_MAGIC;
    assigns ctx->sha256_state[0 .. SHA256_STATE_SIZE - 1];
    ensures \result == 0;
    ensures ctx->magic == \old(ctx->magic);
    ensures ctx->sha256_total == \old(ctx->sha256_total);
    ensures \forall integer i; 0 <= i < SHA256_BLOCK_SIZE ==>
                        ctx->sha256_buffer[i] == \old(ctx->sha256_buffer[i]);
*/
static int sha256_process(sha256_context *ctx, const u8 data[SHA256_BLOCK_SIZE])
{
    u32 a, b, c, d, e, f, g, h;
    u32 W[64];
    unsigned int i;
    int ret;

    MUST_HAVE((data != NULL), ret, err);
    SHA256_HASH_CHECK_INITIALIZED(ctx, ret, err);

    /* Init our inner variables */
    a = ctx->sha256_state[0];
    b = ctx->sha256_state[1];
    c = ctx->sha256_state[2];
    d = ctx->sha256_state[3];
    e = ctx->sha256_state[4];
    f = ctx->sha256_state[5];
    g = ctx->sha256_state[6];
    h = ctx->sha256_state[7];

    /*@
        loop invariant 0 <= i <= 16;
        loop assigns i, a, b, c, d, e, f, g, h, W[0 .. 15];
        loop variant 16 - i;
    */
    for (i = 0; i < 16; i++) {
        GET_UINT32_BE(W[i], data, 4 * i);
        SHA2CORE_SHA256(a, b, c, d, e, f, g, h, W[i], K_SHA256[i]);
    }

        /*@
            loop invariant 16 <= i <= 64;
            loop assigns i, a, b, c, d, e, f, g, h, W[16 .. 63];
            loop variant 64 - i;
        */
    for (i = 16; i < 64; i++) {
        SHA2CORE_SHA256(a, b, c, d, e, f, g, h, UPDATEW_SHA256(W, i),
                        K_SHA256[i]);
    }

    /* Update state */
    ctx->sha256_state[0] += a;
    ctx->sha256_state[1] += b;
    ctx->sha256_state[2] += c;
    ctx->sha256_state[3] += d;
    ctx->sha256_state[4] += e;
    ctx->sha256_state[5] += f;
    ctx->sha256_state[6] += g;
    ctx->sha256_state[7] += h;

    ret = 0;

err:
    return ret;
}

/* Init hash function */
int sha256_init(sha256_context *ctx)
{
    int ret;

    MUST_HAVE((ctx != NULL), ret, err);

    ctx->sha256_total = 0;
    ctx->sha256_state[0] = 0x6A09E667;
    ctx->sha256_state[1] = 0xBB67AE85;
    ctx->sha256_state[2] = 0x3C6EF372;
    ctx->sha256_state[3] = 0xA54FF53A;
    ctx->sha256_state[4] = 0x510E527F;
    ctx->sha256_state[5] = 0x9B05688C;
    ctx->sha256_state[6] = 0x1F83D9AB;
    ctx->sha256_state[7] = 0x5BE0CD19;

    /* Tell that we are initialized */
    ctx->magic = SHA256_HASH_MAGIC;

    ret = 0;

err:
    return ret;
}

/* Update hash function */
int sha256_update(sha256_context *ctx, const u8 *input, u32 ilen)
{
    const u8 *data_ptr = input;
    u32 remain_ilen = ilen;
    u16 fill;
    u8 left;
    int ret;

    MUST_HAVE((input != NULL) || (ilen == 0), ret, err);
    SHA256_HASH_CHECK_INITIALIZED(ctx, ret, err);

    /* Nothing to process, return */
    if (ilen == 0) {
        ret = 0;
        goto err;
    }

    /* Get what's left in our local buffer */
    left = (ctx->sha256_total & 0x3F);
    fill = (u16)(SHA256_BLOCK_SIZE - left);

    ctx->sha256_total += ilen;

    if ((left > 0) && (remain_ilen >= fill)) {
        /* Copy data at the end of the buffer */
        ret = (memcpy(ctx->sha256_buffer + left, data_ptr, fill) == (ctx->sha256_buffer + left)) ? 0 : -1;
        EG(ret, err);
        ret = sha256_process(ctx, ctx->sha256_buffer); EG(ret, err);
        data_ptr += fill;
        remain_ilen -= fill;
        left = 0;
    }

        /*@
            loop invariant remain_ilen <= ilen;
            loop invariant data_ptr == input + (ilen - remain_ilen);
            loop assigns remain_ilen, data_ptr, ret, ctx->sha256_state[0 .. SHA256_STATE_SIZE - 1];
            loop variant remain_ilen;
        */
    while (remain_ilen >= SHA256_BLOCK_SIZE) {
        ret = sha256_process(ctx, data_ptr); EG(ret, err);
        data_ptr += SHA256_BLOCK_SIZE;
        remain_ilen -= SHA256_BLOCK_SIZE;
    }

    if (remain_ilen > 0) {
        ret = (memcpy(ctx->sha256_buffer + left, data_ptr, remain_ilen) == (ctx->sha256_buffer + left)) ? 0 : -1;
        EG(ret, err);
    }

    ret = 0;

err:
    return ret;
}

/* Finalize */
int sha256_final(sha256_context *ctx, u8 output[SHA256_DIGEST_SIZE])
{
    unsigned int block_present = 0;
    u8 last_padded_block[2 * SHA256_BLOCK_SIZE];
    int ret;

    MUST_HAVE((output != NULL), ret, err);
    SHA256_HASH_CHECK_INITIALIZED(ctx, ret, err);

    /* Fill in our last block with zeroes */
    ret = (memset(last_padded_block, 0, sizeof(last_padded_block)) == last_padded_block) ? 0 : -1;
    EG(ret, err);

    /* This is our final step, so we proceed with the padding */
    block_present = (ctx->sha256_total % SHA256_BLOCK_SIZE);
    if (block_present != 0) {
        /* Copy what's left in our temporary context buffer */
        ret = (memcpy(last_padded_block, ctx->sha256_buffer, block_present) == last_padded_block) ? 0 : -1;
        EG(ret, err);
    }

    /* Put the 0x80 byte, beginning of padding  */
    last_padded_block[block_present] = 0x80;

    /* Handle possible additional block */
    if (block_present > (SHA256_BLOCK_SIZE - 1 - sizeof(u64))) {
        /* We need an additional block */
        PUT_UINT64_BE(8 * ctx->sha256_total, last_padded_block,
                      (2 * SHA256_BLOCK_SIZE) - sizeof(u64));
        ret = sha256_process(ctx, last_padded_block); EG(ret, err);
        ret = sha256_process(ctx, last_padded_block + SHA256_BLOCK_SIZE); EG(ret, err);
    } else {
        /* We do not need an additional block */
        PUT_UINT64_BE(8 * ctx->sha256_total, last_padded_block,
                      SHA256_BLOCK_SIZE - sizeof(u64));
        ret = sha256_process(ctx, last_padded_block); EG(ret, err);
    }

    /* Output the hash result */
    PUT_UINT32_BE(ctx->sha256_state[0], output, 0);
    PUT_UINT32_BE(ctx->sha256_state[1], output, 4);
    PUT_UINT32_BE(ctx->sha256_state[2], output, 8);
    PUT_UINT32_BE(ctx->sha256_state[3], output, 12);
    PUT_UINT32_BE(ctx->sha256_state[4], output, 16);
    PUT_UINT32_BE(ctx->sha256_state[5], output, 20);
    PUT_UINT32_BE(ctx->sha256_state[6], output, 24);
    PUT_UINT32_BE(ctx->sha256_state[7], output, 28);

    /* Tell that we are uninitialized */
    ctx->magic = WORD(0);

    ret = 0;

err:
    return ret;
}

int sha256_scattered(const u8 **inputs, const u32 *ilens,
                     u8 output[SHA256_DIGEST_SIZE])
{
    sha256_context ctx;
    int ret, pos = 0;

    MUST_HAVE((inputs != NULL) && (ilens != NULL) && (output != NULL), ret, err);

    ret = sha256_init(&ctx); EG(ret, err);

    /*@
      loop invariant pos >= 0;
      loop invariant ctx.magic == SHA256_HASH_MAGIC;
      loop invariant \valid_read(inputs + (0 .. pos));
      loop invariant \valid_read(ilens + (0 .. pos));
      loop assigns pos, ret, ctx.sha256_total, ctx.sha256_state[0 .. SHA256_STATE_SIZE - 1],
                   ctx.sha256_buffer[0 .. SHA256_BLOCK_SIZE - 1], ctx.magic;
    */
    while (inputs[pos] != NULL) {
        ret = sha256_update(&ctx, inputs[pos], ilens[pos]); EG(ret, err);
        pos += 1;
    }

    ret = sha256_final(&ctx, output);

err:
    return ret;
}

int sha256(const u8 *input, u32 ilen, u8 output[SHA256_DIGEST_SIZE])
{
    sha256_context ctx;
    int ret;

    ret = sha256_init(&ctx); EG(ret, err);
    ret = sha256_update(&ctx, input, ilen); EG(ret, err);
    ret = sha256_final(&ctx, output);

err:
    return ret;
}

#endif
