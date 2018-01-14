#include "cache.h"
#include "tag.h"
#include "commit.h"
#include "pkt-line.h"
#include "utf8.h"
#include "diff.h"
#include "revision.h"
#include "notes.h"
#include "gpg-interface.h"
#include "mergesort.h"
#include "commit-slab.h"
#include "prio-queue.h"
#include "sha1-lookup.h"
#include "wt-status.h"


/// TAKEN FROM:
/// https://github.com/ARMmbed/mbedtls/blob/development/library/sha1.h
/// https://github.com/ARMmbed/mbedtls/blob/development/library/sha1.c

/*
 *  FIPS-180-1 compliant SHA-1 implementation
 *
 *  Copyright (C) 2006-2015, ARM Limited, All Rights Reserved
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Licensed under the Apache License, Version 2.0 (the "License"); you may
 *  not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *  This file is part of mbed TLS (https://tls.mbed.org)
 */
/*
 *  The SHA-1 standard was published by NIST in 1993.
 *
 *  http://www.itl.nist.gov/fipspubs/fip180-1.htm
 */

typedef struct
{
    uint32_t total[2];          /*!< number of bytes processed  */
    uint32_t state[5];          /*!< intermediate digest state  */
    unsigned char buffer[64];   /*!< data block being processed */
}
mbedtls_sha1_context;

#include <string.h>

#if !defined(MBEDTLS_SHA1_ALT)

/* Implementation that should never be optimized out by the compiler */
static void mbedtls_zeroize( void *v, size_t n ) {
    volatile unsigned char *p = (unsigned char*)v; while( n-- ) *p++ = 0;
}

/*
 * 32-bit integer manipulation macros (big endian)
 */
#ifndef GET_UINT32_BE
#define GET_UINT32_BE(n,b,i)                            \
{                                                       \
    (n) = ( (uint32_t) (b)[(i)    ] << 24 )             \
        | ( (uint32_t) (b)[(i) + 1] << 16 )             \
        | ( (uint32_t) (b)[(i) + 2] <<  8 )             \
        | ( (uint32_t) (b)[(i) + 3]       );            \
}
#endif

#ifndef PUT_UINT32_BE
#define PUT_UINT32_BE(n,b,i)                            \
{                                                       \
    (b)[(i)    ] = (unsigned char) ( (n) >> 24 );       \
    (b)[(i) + 1] = (unsigned char) ( (n) >> 16 );       \
    (b)[(i) + 2] = (unsigned char) ( (n) >>  8 );       \
    (b)[(i) + 3] = (unsigned char) ( (n)       );       \
}
#endif

void mbedtls_sha1_init( mbedtls_sha1_context *ctx )
{
    memset( ctx, 0, sizeof( mbedtls_sha1_context ) );
}

void mbedtls_sha1_free( mbedtls_sha1_context *ctx )
{
    if( ctx == NULL )
        return;

    mbedtls_zeroize( ctx, sizeof( mbedtls_sha1_context ) );
}

void mbedtls_sha1_clone( mbedtls_sha1_context *dst,
                         const mbedtls_sha1_context *src )
{
    *dst = *src;
}

/*
 * SHA-1 context setup
 */
void mbedtls_sha1_starts( mbedtls_sha1_context *ctx )
{
    ctx->total[0] = 0;
    ctx->total[1] = 0;

    ctx->state[0] = 0x67452301;
    ctx->state[1] = 0xEFCDAB89;
    ctx->state[2] = 0x98BADCFE;
    ctx->state[3] = 0x10325476;
    ctx->state[4] = 0xC3D2E1F0;
}

#if !defined(MBEDTLS_SHA1_PROCESS_ALT)
void mbedtls_sha1_process( mbedtls_sha1_context *ctx, const unsigned char data[64] )
{
    uint32_t temp, W[16], A, B, C, D, E;

    GET_UINT32_BE( W[ 0], data,  0 );
    GET_UINT32_BE( W[ 1], data,  4 );
    GET_UINT32_BE( W[ 2], data,  8 );
    GET_UINT32_BE( W[ 3], data, 12 );
    GET_UINT32_BE( W[ 4], data, 16 );
    GET_UINT32_BE( W[ 5], data, 20 );
    GET_UINT32_BE( W[ 6], data, 24 );
    GET_UINT32_BE( W[ 7], data, 28 );
    GET_UINT32_BE( W[ 8], data, 32 );
    GET_UINT32_BE( W[ 9], data, 36 );
    GET_UINT32_BE( W[10], data, 40 );
    GET_UINT32_BE( W[11], data, 44 );
    GET_UINT32_BE( W[12], data, 48 );
    GET_UINT32_BE( W[13], data, 52 );
    GET_UINT32_BE( W[14], data, 56 );
    GET_UINT32_BE( W[15], data, 60 );

#define S(x,n) ((x << n) | ((x & 0xFFFFFFFF) >> (32 - n)))

#define R(t)                                            \
(                                                       \
    temp = W[( t -  3 ) & 0x0F] ^ W[( t - 8 ) & 0x0F] ^ \
           W[( t - 14 ) & 0x0F] ^ W[  t       & 0x0F],  \
    ( W[t & 0x0F] = S(temp,1) )                         \
)

#define P(a,b,c,d,e,x)                                  \
{                                                       \
    e += S(a,5) + F(b,c,d) + K + x; b = S(b,30);        \
}

    A = ctx->state[0];
    B = ctx->state[1];
    C = ctx->state[2];
    D = ctx->state[3];
    E = ctx->state[4];

#define F(x,y,z) (z ^ (x & (y ^ z)))
#define K 0x5A827999

    P( A, B, C, D, E, W[0]  );
    P( E, A, B, C, D, W[1]  );
    P( D, E, A, B, C, W[2]  );
    P( C, D, E, A, B, W[3]  );
    P( B, C, D, E, A, W[4]  );
    P( A, B, C, D, E, W[5]  );
    P( E, A, B, C, D, W[6]  );
    P( D, E, A, B, C, W[7]  );
    P( C, D, E, A, B, W[8]  );
    P( B, C, D, E, A, W[9]  );
    P( A, B, C, D, E, W[10] );
    P( E, A, B, C, D, W[11] );
    P( D, E, A, B, C, W[12] );
    P( C, D, E, A, B, W[13] );
    P( B, C, D, E, A, W[14] );
    P( A, B, C, D, E, W[15] );
    P( E, A, B, C, D, R(16) );
    P( D, E, A, B, C, R(17) );
    P( C, D, E, A, B, R(18) );
    P( B, C, D, E, A, R(19) );

#undef K
#undef F

#define F(x,y,z) (x ^ y ^ z)
#define K 0x6ED9EBA1

    P( A, B, C, D, E, R(20) );
    P( E, A, B, C, D, R(21) );
    P( D, E, A, B, C, R(22) );
    P( C, D, E, A, B, R(23) );
    P( B, C, D, E, A, R(24) );
    P( A, B, C, D, E, R(25) );
    P( E, A, B, C, D, R(26) );
    P( D, E, A, B, C, R(27) );
    P( C, D, E, A, B, R(28) );
    P( B, C, D, E, A, R(29) );
    P( A, B, C, D, E, R(30) );
    P( E, A, B, C, D, R(31) );
    P( D, E, A, B, C, R(32) );
    P( C, D, E, A, B, R(33) );
    P( B, C, D, E, A, R(34) );
    P( A, B, C, D, E, R(35) );
    P( E, A, B, C, D, R(36) );
    P( D, E, A, B, C, R(37) );
    P( C, D, E, A, B, R(38) );
    P( B, C, D, E, A, R(39) );

#undef K
#undef F

#define F(x,y,z) ((x & y) | (z & (x | y)))
#define K 0x8F1BBCDC

    P( A, B, C, D, E, R(40) );
    P( E, A, B, C, D, R(41) );
    P( D, E, A, B, C, R(42) );
    P( C, D, E, A, B, R(43) );
    P( B, C, D, E, A, R(44) );
    P( A, B, C, D, E, R(45) );
    P( E, A, B, C, D, R(46) );
    P( D, E, A, B, C, R(47) );
    P( C, D, E, A, B, R(48) );
    P( B, C, D, E, A, R(49) );
    P( A, B, C, D, E, R(50) );
    P( E, A, B, C, D, R(51) );
    P( D, E, A, B, C, R(52) );
    P( C, D, E, A, B, R(53) );
    P( B, C, D, E, A, R(54) );
    P( A, B, C, D, E, R(55) );
    P( E, A, B, C, D, R(56) );
    P( D, E, A, B, C, R(57) );
    P( C, D, E, A, B, R(58) );
    P( B, C, D, E, A, R(59) );

#undef K
#undef F

#define F(x,y,z) (x ^ y ^ z)
#define K 0xCA62C1D6

    P( A, B, C, D, E, R(60) );
    P( E, A, B, C, D, R(61) );
    P( D, E, A, B, C, R(62) );
    P( C, D, E, A, B, R(63) );
    P( B, C, D, E, A, R(64) );
    P( A, B, C, D, E, R(65) );
    P( E, A, B, C, D, R(66) );
    P( D, E, A, B, C, R(67) );
    P( C, D, E, A, B, R(68) );
    P( B, C, D, E, A, R(69) );
    P( A, B, C, D, E, R(70) );
    P( E, A, B, C, D, R(71) );
    P( D, E, A, B, C, R(72) );
    P( C, D, E, A, B, R(73) );
    P( B, C, D, E, A, R(74) );
    P( A, B, C, D, E, R(75) );
    P( E, A, B, C, D, R(76) );
    P( D, E, A, B, C, R(77) );
    P( C, D, E, A, B, R(78) );
    P( B, C, D, E, A, R(79) );

#undef K
#undef F

    ctx->state[0] += A;
    ctx->state[1] += B;
    ctx->state[2] += C;
    ctx->state[3] += D;
    ctx->state[4] += E;
}
#endif /* !MBEDTLS_SHA1_PROCESS_ALT */

/*
 * SHA-1 process buffer
 */
void mbedtls_sha1_update( mbedtls_sha1_context *ctx, const unsigned char *input, size_t ilen )
{
    size_t fill;
    uint32_t left;

    if( ilen == 0 )
        return;

    left = ctx->total[0] & 0x3F;
    fill = 64 - left;

    ctx->total[0] += (uint32_t) ilen;
    ctx->total[0] &= 0xFFFFFFFF;

    if( ctx->total[0] < (uint32_t) ilen )
        ctx->total[1]++;

    if( left && ilen >= fill )
    {
        memcpy( (void *) (ctx->buffer + left), input, fill );
        mbedtls_sha1_process( ctx, ctx->buffer );
        input += fill;
        ilen  -= fill;
        left = 0;
    }

    while( ilen >= 64 )
    {
        mbedtls_sha1_process( ctx, input );
        input += 64;
        ilen  -= 64;
    }

    if( ilen > 0 )
        memcpy( (void *) (ctx->buffer + left), input, ilen );
}

static const unsigned char sha1_padding[64] =
{
 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

/*
 * SHA-1 final digest
 */
void mbedtls_sha1_finish( mbedtls_sha1_context *ctx, unsigned char output[20] )
{
    uint32_t last, padn;
    uint32_t high, low;
    unsigned char msglen[8];

    high = ( ctx->total[0] >> 29 )
         | ( ctx->total[1] <<  3 );
    low  = ( ctx->total[0] <<  3 );

    PUT_UINT32_BE( high, msglen, 0 );
    PUT_UINT32_BE( low,  msglen, 4 );

    last = ctx->total[0] & 0x3F;
    padn = ( last < 56 ) ? ( 56 - last ) : ( 120 - last );

    mbedtls_sha1_update( ctx, sha1_padding, padn );
    mbedtls_sha1_update( ctx, msglen, 8 );

    PUT_UINT32_BE( ctx->state[0], output,  0 );
    PUT_UINT32_BE( ctx->state[1], output,  4 );
    PUT_UINT32_BE( ctx->state[2], output,  8 );
    PUT_UINT32_BE( ctx->state[3], output, 12 );
    PUT_UINT32_BE( ctx->state[4], output, 16 );
}

#endif /* !MBEDTLS_SHA1_ALT */

/*
 * output = SHA-1( input buffer )
 */
void mbedtls_sha1( const unsigned char *input, size_t ilen, unsigned char output[20] )
{
    mbedtls_sha1_context ctx;

    mbedtls_sha1_init( &ctx );
    mbedtls_sha1_starts( &ctx );
    mbedtls_sha1_update( &ctx, input, ilen );
    mbedtls_sha1_finish( &ctx, output );
    mbedtls_sha1_free( &ctx );
}

#if defined(MBEDTLS_SELF_TEST)
/*
 * FIPS-180-1 test vectors
 */
static const unsigned char sha1_test_buf[3][57] =
{
    { "abc" },
    { "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" },
    { "" }
};

static const int sha1_test_buflen[3] =
{
    3, 56, 1000
};

static const unsigned char sha1_test_sum[3][20] =
{
    { 0xA9, 0x99, 0x3E, 0x36, 0x47, 0x06, 0x81, 0x6A, 0xBA, 0x3E,
      0x25, 0x71, 0x78, 0x50, 0xC2, 0x6C, 0x9C, 0xD0, 0xD8, 0x9D },
    { 0x84, 0x98, 0x3E, 0x44, 0x1C, 0x3B, 0xD2, 0x6E, 0xBA, 0xAE,
      0x4A, 0xA1, 0xF9, 0x51, 0x29, 0xE5, 0xE5, 0x46, 0x70, 0xF1 },
    { 0x34, 0xAA, 0x97, 0x3C, 0xD4, 0xC4, 0xDA, 0xA4, 0xF6, 0x1E,
      0xEB, 0x2B, 0xDB, 0xAD, 0x27, 0x31, 0x65, 0x34, 0x01, 0x6F }
};

/*
 * Checkup routine
 */
int mbedtls_sha1_self_test( int verbose )
{
    int i, j, buflen, ret = 0;
    unsigned char buf[1024];
    unsigned char sha1sum[20];
    mbedtls_sha1_context ctx;

    mbedtls_sha1_init( &ctx );

    /*
     * SHA-1
     */
    for( i = 0; i < 3; i++ )
    {
        if( verbose != 0 )
            mbedtls_printf( "  SHA-1 test #%d: ", i + 1 );

        mbedtls_sha1_starts( &ctx );

        if( i == 2 )
        {
            memset( buf, 'a', buflen = 1000 );

            for( j = 0; j < 1000; j++ )
                mbedtls_sha1_update( &ctx, buf, buflen );
        }
        else
            mbedtls_sha1_update( &ctx, sha1_test_buf[i],
                               sha1_test_buflen[i] );

        mbedtls_sha1_finish( &ctx, sha1sum );

        if( memcmp( sha1sum, sha1_test_sum[i], 20 ) != 0 )
        {
            if( verbose != 0 )
                mbedtls_printf( "failed\n" );

            ret = 1;
            goto exit;
        }

        if( verbose != 0 )
            mbedtls_printf( "passed\n" );
    }

    if( verbose != 0 )
        mbedtls_printf( "\n" );

exit:
    mbedtls_sha1_free( &ctx );

    return( ret );
}

#endif /* MBEDTLS_SELF_TEST */

/// sha1 from mbed tls

static struct commit_extra_header *read_commit_extra_header_lines(const char *buf, size_t len, const char **);

int save_commit_buffer = 1;

const char *commit_type = "commit";

struct commit *lookup_commit_reference_gently(const struct object_id *oid,
					      int quiet)
{
	struct object *obj = deref_tag(parse_object(oid), NULL, 0);

	if (!obj)
		return NULL;
	return object_as_type(obj, OBJ_COMMIT, quiet);
}

struct commit *lookup_commit_reference(const struct object_id *oid)
{
	return lookup_commit_reference_gently(oid, 0);
}

struct commit *lookup_commit_or_die(const struct object_id *oid, const char *ref_name)
{
	struct commit *c = lookup_commit_reference(oid);
	if (!c)
		die(_("could not parse %s"), ref_name);
	if (oidcmp(oid, &c->object.oid)) {
		warning(_("%s %s is not a commit!"),
			ref_name, oid_to_hex(oid));
	}
	return c;
}

struct commit *lookup_commit(const struct object_id *oid)
{
	struct object *obj = lookup_object(oid->hash);
	if (!obj)
		return create_object(oid->hash, alloc_commit_node());
	return object_as_type(obj, OBJ_COMMIT, 0);
}

struct commit *lookup_commit_reference_by_name(const char *name)
{
	struct object_id oid;
	struct commit *commit;

	if (get_oid_committish(name, &oid))
		return NULL;
	commit = lookup_commit_reference(&oid);
	if (parse_commit(commit))
		return NULL;
	return commit;
}

static timestamp_t parse_commit_date(const char *buf, const char *tail)
{
	const char *dateptr;

	if (buf + 6 >= tail)
		return 0;
	if (memcmp(buf, "author", 6))
		return 0;
	while (buf < tail && *buf++ != '\n')
		/* nada */;
	if (buf + 9 >= tail)
		return 0;
	if (memcmp(buf, "committer", 9))
		return 0;
	while (buf < tail && *buf++ != '>')
		/* nada */;
	if (buf >= tail)
		return 0;
	dateptr = buf;
	while (buf < tail && *buf++ != '\n')
		/* nada */;
	if (buf >= tail)
		return 0;
	/* dateptr < buf && buf[-1] == '\n', so parsing will stop at buf-1 */
	return parse_timestamp(dateptr, NULL, 10);
}

static struct commit_graft **commit_graft;
static int commit_graft_alloc, commit_graft_nr;

static const unsigned char *commit_graft_sha1_access(size_t index, void *table)
{
	struct commit_graft **commit_graft_table = table;
	return commit_graft_table[index]->oid.hash;
}

static int commit_graft_pos(const unsigned char *sha1)
{
	return sha1_pos(sha1, commit_graft, commit_graft_nr,
			commit_graft_sha1_access);
}

int register_commit_graft(struct commit_graft *graft, int ignore_dups)
{
	int pos = commit_graft_pos(graft->oid.hash);

	if (0 <= pos) {
		if (ignore_dups)
			free(graft);
		else {
			free(commit_graft[pos]);
			commit_graft[pos] = graft;
		}
		return 1;
	}
	pos = -pos - 1;
	ALLOC_GROW(commit_graft, commit_graft_nr + 1, commit_graft_alloc);
	commit_graft_nr++;
	if (pos < commit_graft_nr)
		memmove(commit_graft + pos + 1,
			commit_graft + pos,
			(commit_graft_nr - pos - 1) *
			sizeof(*commit_graft));
	commit_graft[pos] = graft;
	return 0;
}

struct commit_graft *read_graft_line(struct strbuf *line)
{
	/* The format is just "Commit Parent1 Parent2 ...\n" */
	int i, phase;
	const char *tail = NULL;
	struct commit_graft *graft = NULL;
	struct object_id dummy_oid, *oid;

	strbuf_rtrim(line);
	if (!line->len || line->buf[0] == '#')
		return NULL;
	/*
	 * phase 0 verifies line, counts hashes in line and allocates graft
	 * phase 1 fills graft
	 */
	for (phase = 0; phase < 2; phase++) {
		oid = graft ? &graft->oid : &dummy_oid;
		if (parse_oid_hex(line->buf, oid, &tail))
			goto bad_graft_data;
		for (i = 0; *tail != '\0'; i++) {
			oid = graft ? &graft->parent[i] : &dummy_oid;
			if (!isspace(*tail++) || parse_oid_hex(tail, oid, &tail))
				goto bad_graft_data;
		}
		if (!graft) {
			graft = xmalloc(st_add(sizeof(*graft),
					       st_mult(sizeof(struct object_id), i)));
			graft->nr_parent = i;
		}
	}
	return graft;

bad_graft_data:
	error("bad graft data: %s", line->buf);
	assert(!graft);
	return NULL;
}

static int read_graft_file(const char *graft_file)
{
	FILE *fp = fopen_or_warn(graft_file, "r");
	struct strbuf buf = STRBUF_INIT;
	if (!fp)
		return -1;
	while (!strbuf_getwholeline(&buf, fp, '\n')) {
		/* The format is just "Commit Parent1 Parent2 ...\n" */
		struct commit_graft *graft = read_graft_line(&buf);
		if (!graft)
			continue;
		if (register_commit_graft(graft, 1))
			error("duplicate graft data: %s", buf.buf);
	}
	fclose(fp);
	strbuf_release(&buf);
	return 0;
}

static void prepare_commit_graft(void)
{
	static int commit_graft_prepared;
	char *graft_file;

	if (commit_graft_prepared)
		return;
	graft_file = get_graft_file();
	read_graft_file(graft_file);
	/* make sure shallows are read */
	is_repository_shallow();
	commit_graft_prepared = 1;
}

struct commit_graft *lookup_commit_graft(const struct object_id *oid)
{
	int pos;
	prepare_commit_graft();
	pos = commit_graft_pos(oid->hash);
	if (pos < 0)
		return NULL;
	return commit_graft[pos];
}

int for_each_commit_graft(each_commit_graft_fn fn, void *cb_data)
{
	int i, ret;
	for (i = ret = 0; i < commit_graft_nr && !ret; i++)
		ret = fn(commit_graft[i], cb_data);
	return ret;
}

int unregister_shallow(const struct object_id *oid)
{
	int pos = commit_graft_pos(oid->hash);
	if (pos < 0)
		return -1;
	if (pos + 1 < commit_graft_nr)
		MOVE_ARRAY(commit_graft + pos, commit_graft + pos + 1,
			   commit_graft_nr - pos - 1);
	commit_graft_nr--;
	return 0;
}

struct commit_buffer {
	void *buffer;
	unsigned long size;
};
define_commit_slab(buffer_slab, struct commit_buffer);
static struct buffer_slab buffer_slab = COMMIT_SLAB_INIT(1, buffer_slab);

void set_commit_buffer(struct commit *commit, void *buffer, unsigned long size)
{
	struct commit_buffer *v = buffer_slab_at(&buffer_slab, commit);
	v->buffer = buffer;
	v->size = size;
}

const void *get_cached_commit_buffer(const struct commit *commit, unsigned long *sizep)
{
	struct commit_buffer *v = buffer_slab_peek(&buffer_slab, commit);
	if (!v) {
		if (sizep)
			*sizep = 0;
		return NULL;
	}
	if (sizep)
		*sizep = v->size;
	return v->buffer;
}

const void *get_commit_buffer(const struct commit *commit, unsigned long *sizep)
{
	const void *ret = get_cached_commit_buffer(commit, sizep);
	if (!ret) {
		enum object_type type;
		unsigned long size;
		ret = read_sha1_file(commit->object.oid.hash, &type, &size);
		if (!ret)
			die("cannot read commit object %s",
			    oid_to_hex(&commit->object.oid));
		if (type != OBJ_COMMIT)
			die("expected commit for %s, got %s",
			    oid_to_hex(&commit->object.oid), typename(type));
		if (sizep)
			*sizep = size;
	}
	return ret;
}

void unuse_commit_buffer(const struct commit *commit, const void *buffer)
{
	struct commit_buffer *v = buffer_slab_peek(&buffer_slab, commit);
	if (!(v && v->buffer == buffer))
		free((void *)buffer);
}

void free_commit_buffer(struct commit *commit)
{
	struct commit_buffer *v = buffer_slab_peek(&buffer_slab, commit);
	if (v) {
		FREE_AND_NULL(v->buffer);
		v->size = 0;
	}
}

const void *detach_commit_buffer(struct commit *commit, unsigned long *sizep)
{
	struct commit_buffer *v = buffer_slab_peek(&buffer_slab, commit);
	void *ret;

	if (!v) {
		if (sizep)
			*sizep = 0;
		return NULL;
	}
	ret = v->buffer;
	if (sizep)
		*sizep = v->size;

	v->buffer = NULL;
	v->size = 0;
	return ret;
}

int parse_commit_buffer(struct commit *item, const void *buffer, unsigned long size)
{
	const char *tail = buffer;
	const char *bufptr = buffer;
	struct object_id parent;
	struct commit_list **pptr;
	struct commit_graft *graft;
	const int tree_entry_len = GIT_SHA1_HEXSZ + 5;
	const int parent_entry_len = GIT_SHA1_HEXSZ + 7;

	if (item->object.parsed)
		return 0;
	item->object.parsed = 1;
	tail += size;
	if (tail <= bufptr + tree_entry_len + 1 || memcmp(bufptr, "tree ", 5) ||
			bufptr[tree_entry_len] != '\n')
		return error("bogus commit object %s", oid_to_hex(&item->object.oid));
	if (get_sha1_hex(bufptr + 5, parent.hash) < 0)
		return error("bad tree pointer in commit %s",
			     oid_to_hex(&item->object.oid));
	item->tree = lookup_tree(&parent);
	bufptr += tree_entry_len + 1; /* "tree " + "hex sha1" + "\n" */
	pptr = &item->parents;

	graft = lookup_commit_graft(&item->object.oid);
	while (bufptr + parent_entry_len < tail && !memcmp(bufptr, "parent ", 7)) {
		struct commit *new_parent;

		if (tail <= bufptr + parent_entry_len + 1 ||
		    get_sha1_hex(bufptr + 7, parent.hash) ||
		    bufptr[parent_entry_len] != '\n')
			return error("bad parents in commit %s", oid_to_hex(&item->object.oid));
		bufptr += parent_entry_len + 1;
		/*
		 * The clone is shallow if nr_parent < 0, and we must
		 * not traverse its real parents even when we unhide them.
		 */
		if (graft && (graft->nr_parent < 0 || grafts_replace_parents))
			continue;
		new_parent = lookup_commit(&parent);
		if (new_parent)
			pptr = &commit_list_insert(new_parent, pptr)->next;
	}
	if (graft) {
		int i;
		struct commit *new_parent;
		for (i = 0; i < graft->nr_parent; i++) {
			new_parent = lookup_commit(&graft->parent[i]);
			if (!new_parent)
				continue;
			pptr = &commit_list_insert(new_parent, pptr)->next;
		}
	}
	item->date = parse_commit_date(bufptr, tail);

	return 0;
}

int parse_commit_gently(struct commit *item, int quiet_on_missing)
{
	enum object_type type;
	void *buffer;
	unsigned long size;
	int ret;

	if (!item)
		return -1;
	if (item->object.parsed)
		return 0;
	buffer = read_sha1_file(item->object.oid.hash, &type, &size);
	if (!buffer)
		return quiet_on_missing ? -1 :
			error("Could not read %s",
			     oid_to_hex(&item->object.oid));
	if (type != OBJ_COMMIT) {
		free(buffer);
		return error("Object %s not a commit",
			     oid_to_hex(&item->object.oid));
	}
	ret = parse_commit_buffer(item, buffer, size);
	if (save_commit_buffer && !ret) {
		set_commit_buffer(item, buffer, size);
		return 0;
	}
	free(buffer);
	return ret;
}

void parse_commit_or_die(struct commit *item)
{
	if (parse_commit(item))
		die("unable to parse commit %s",
		    item ? oid_to_hex(&item->object.oid) : "(null)");
}

int find_commit_subject(const char *commit_buffer, const char **subject)
{
	const char *eol;
	const char *p = commit_buffer;

	while (*p && (*p != '\n' || p[1] != '\n'))
		p++;
	if (*p) {
		p = skip_blank_lines(p + 2);
		eol = strchrnul(p, '\n');
	} else
		eol = p;

	*subject = p;

	return eol - p;
}

struct commit_list *commit_list_insert(struct commit *item, struct commit_list **list_p)
{
	struct commit_list *new_list = xmalloc(sizeof(struct commit_list));
	new_list->item = item;
	new_list->next = *list_p;
	*list_p = new_list;
	return new_list;
}

unsigned commit_list_count(const struct commit_list *l)
{
	unsigned c = 0;
	for (; l; l = l->next )
		c++;
	return c;
}

struct commit_list *copy_commit_list(struct commit_list *list)
{
	struct commit_list *head = NULL;
	struct commit_list **pp = &head;
	while (list) {
		pp = commit_list_append(list->item, pp);
		list = list->next;
	}
	return head;
}

void free_commit_list(struct commit_list *list)
{
	while (list)
		pop_commit(&list);
}

struct commit_list * commit_list_insert_by_date(struct commit *item, struct commit_list **list)
{
	struct commit_list **pp = list;
	struct commit_list *p;
	while ((p = *pp) != NULL) {
		if (p->item->date < item->date) {
			break;
		}
		pp = &p->next;
	}
	return commit_list_insert(item, pp);
}

static int commit_list_compare_by_date(const void *a, const void *b)
{
	timestamp_t a_date = ((const struct commit_list *)a)->item->date;
	timestamp_t b_date = ((const struct commit_list *)b)->item->date;
	if (a_date < b_date)
		return 1;
	if (a_date > b_date)
		return -1;
	return 0;
}

static void *commit_list_get_next(const void *a)
{
	return ((const struct commit_list *)a)->next;
}

static void commit_list_set_next(void *a, void *next)
{
	((struct commit_list *)a)->next = next;
}

void commit_list_sort_by_date(struct commit_list **list)
{
	*list = llist_mergesort(*list, commit_list_get_next, commit_list_set_next,
				commit_list_compare_by_date);
}

struct commit *pop_most_recent_commit(struct commit_list **list,
				      unsigned int mark)
{
	struct commit *ret = pop_commit(list);
	struct commit_list *parents = ret->parents;

	while (parents) {
		struct commit *commit = parents->item;
		if (!parse_commit(commit) && !(commit->object.flags & mark)) {
			commit->object.flags |= mark;
			commit_list_insert_by_date(commit, list);
		}
		parents = parents->next;
	}
	return ret;
}

static void clear_commit_marks_1(struct commit_list **plist,
				 struct commit *commit, unsigned int mark)
{
	while (commit) {
		struct commit_list *parents;

		if (!(mark & commit->object.flags))
			return;

		commit->object.flags &= ~mark;

		parents = commit->parents;
		if (!parents)
			return;

		while ((parents = parents->next))
			commit_list_insert(parents->item, plist);

		commit = commit->parents->item;
	}
}

void clear_commit_marks_many(int nr, struct commit **commit, unsigned int mark)
{
	struct commit_list *list = NULL;

	while (nr--) {
		commit_list_insert(*commit, &list);
		commit++;
	}
	while (list)
		clear_commit_marks_1(&list, pop_commit(&list), mark);
}

void clear_commit_marks(struct commit *commit, unsigned int mark)
{
	clear_commit_marks_many(1, &commit, mark);
}

void clear_commit_marks_for_object_array(struct object_array *a, unsigned mark)
{
	struct object *object;
	struct commit *commit;
	unsigned int i;

	for (i = 0; i < a->nr; i++) {
		object = a->objects[i].item;
		commit = lookup_commit_reference_gently(&object->oid, 1);
		if (commit)
			clear_commit_marks(commit, mark);
	}
}

struct commit *pop_commit(struct commit_list **stack)
{
	struct commit_list *top = *stack;
	struct commit *item = top ? top->item : NULL;

	if (top) {
		*stack = top->next;
		free(top);
	}
	return item;
}

/*
 * Topological sort support
 */

/* count number of children that have not been emitted */
define_commit_slab(indegree_slab, int);

/* record author-date for each commit object */
define_commit_slab(author_date_slab, unsigned long);

static void record_author_date(struct author_date_slab *author_date,
			       struct commit *commit)
{
	const char *buffer = get_commit_buffer(commit, NULL);
	struct ident_split ident;
	const char *ident_line;
	size_t ident_len;
	char *date_end;
	timestamp_t date;

	ident_line = find_commit_header(buffer, "author", &ident_len);
	if (!ident_line)
		goto fail_exit; /* no author line */
	if (split_ident_line(&ident, ident_line, ident_len) ||
	    !ident.date_begin || !ident.date_end)
		goto fail_exit; /* malformed "author" line */

	date = parse_timestamp(ident.date_begin, &date_end, 10);
	if (date_end != ident.date_end)
		goto fail_exit; /* malformed date */
	*(author_date_slab_at(author_date, commit)) = date;

fail_exit:
	unuse_commit_buffer(commit, buffer);
}

static int compare_commits_by_author_date(const void *a_, const void *b_,
					  void *cb_data)
{
	const struct commit *a = a_, *b = b_;
	struct author_date_slab *author_date = cb_data;
	timestamp_t a_date = *(author_date_slab_at(author_date, a));
	timestamp_t b_date = *(author_date_slab_at(author_date, b));

	/* newer commits with larger date first */
	if (a_date < b_date)
		return 1;
	else if (a_date > b_date)
		return -1;
	return 0;
}

int compare_commits_by_commit_date(const void *a_, const void *b_, void *unused)
{
	const struct commit *a = a_, *b = b_;
	/* newer commits with larger date first */
	if (a->date < b->date)
		return 1;
	else if (a->date > b->date)
		return -1;
	return 0;
}

/*
 * Performs an in-place topological sort on the list supplied.
 */
void sort_in_topological_order(struct commit_list **list, enum rev_sort_order sort_order)
{
	struct commit_list *next, *orig = *list;
	struct commit_list **pptr;
	struct indegree_slab indegree;
	struct prio_queue queue;
	struct commit *commit;
	struct author_date_slab author_date;

	if (!orig)
		return;
	*list = NULL;

	init_indegree_slab(&indegree);
	memset(&queue, '\0', sizeof(queue));

	switch (sort_order) {
	default: /* REV_SORT_IN_GRAPH_ORDER */
		queue.compare = NULL;
		break;
	case REV_SORT_BY_COMMIT_DATE:
		queue.compare = compare_commits_by_commit_date;
		break;
	case REV_SORT_BY_AUTHOR_DATE:
		init_author_date_slab(&author_date);
		queue.compare = compare_commits_by_author_date;
		queue.cb_data = &author_date;
		break;
	}

	/* Mark them and clear the indegree */
	for (next = orig; next; next = next->next) {
		struct commit *commit = next->item;
		*(indegree_slab_at(&indegree, commit)) = 1;
		/* also record the author dates, if needed */
		if (sort_order == REV_SORT_BY_AUTHOR_DATE)
			record_author_date(&author_date, commit);
	}

	/* update the indegree */
	for (next = orig; next; next = next->next) {
		struct commit_list *parents = next->item->parents;
		while (parents) {
			struct commit *parent = parents->item;
			int *pi = indegree_slab_at(&indegree, parent);

			if (*pi)
				(*pi)++;
			parents = parents->next;
		}
	}

	/*
	 * find the tips
	 *
	 * tips are nodes not reachable from any other node in the list
	 *
	 * the tips serve as a starting set for the work queue.
	 */
	for (next = orig; next; next = next->next) {
		struct commit *commit = next->item;

		if (*(indegree_slab_at(&indegree, commit)) == 1)
			prio_queue_put(&queue, commit);
	}

	/*
	 * This is unfortunate; the initial tips need to be shown
	 * in the order given from the revision traversal machinery.
	 */
	if (sort_order == REV_SORT_IN_GRAPH_ORDER)
		prio_queue_reverse(&queue);

	/* We no longer need the commit list */
	free_commit_list(orig);

	pptr = list;
	*list = NULL;
	while ((commit = prio_queue_get(&queue)) != NULL) {
		struct commit_list *parents;

		for (parents = commit->parents; parents ; parents = parents->next) {
			struct commit *parent = parents->item;
			int *pi = indegree_slab_at(&indegree, parent);

			if (!*pi)
				continue;

			/*
			 * parents are only enqueued for emission
			 * when all their children have been emitted thereby
			 * guaranteeing topological order.
			 */
			if (--(*pi) == 1)
				prio_queue_put(&queue, parent);
		}
		/*
		 * all children of commit have already been
		 * emitted. we can emit it now.
		 */
		*(indegree_slab_at(&indegree, commit)) = 0;

		pptr = &commit_list_insert(commit, pptr)->next;
	}

	clear_indegree_slab(&indegree);
	clear_prio_queue(&queue);
	if (sort_order == REV_SORT_BY_AUTHOR_DATE)
		clear_author_date_slab(&author_date);
}

/* merge-base stuff */

/* Remember to update object flag allocation in object.h */
#define PARENT1		(1u<<16)
#define PARENT2		(1u<<17)
#define STALE		(1u<<18)
#define RESULT		(1u<<19)

static const unsigned all_flags = (PARENT1 | PARENT2 | STALE | RESULT);

static int queue_has_nonstale(struct prio_queue *queue)
{
	int i;
	for (i = 0; i < queue->nr; i++) {
		struct commit *commit = queue->array[i].data;
		if (!(commit->object.flags & STALE))
			return 1;
	}
	return 0;
}

/* all input commits in one and twos[] must have been parsed! */
static struct commit_list *paint_down_to_common(struct commit *one, int n, struct commit **twos)
{
	struct prio_queue queue = { compare_commits_by_commit_date };
	struct commit_list *result = NULL;
	int i;

	one->object.flags |= PARENT1;
	if (!n) {
		commit_list_append(one, &result);
		return result;
	}
	prio_queue_put(&queue, one);

	for (i = 0; i < n; i++) {
		twos[i]->object.flags |= PARENT2;
		prio_queue_put(&queue, twos[i]);
	}

	while (queue_has_nonstale(&queue)) {
		struct commit *commit = prio_queue_get(&queue);
		struct commit_list *parents;
		int flags;

		flags = commit->object.flags & (PARENT1 | PARENT2 | STALE);
		if (flags == (PARENT1 | PARENT2)) {
			if (!(commit->object.flags & RESULT)) {
				commit->object.flags |= RESULT;
				commit_list_insert_by_date(commit, &result);
			}
			/* Mark parents of a found merge stale */
			flags |= STALE;
		}
		parents = commit->parents;
		while (parents) {
			struct commit *p = parents->item;
			parents = parents->next;
			if ((p->object.flags & flags) == flags)
				continue;
			if (parse_commit(p))
				return NULL;
			p->object.flags |= flags;
			prio_queue_put(&queue, p);
		}
	}

	clear_prio_queue(&queue);
	return result;
}

static struct commit_list *merge_bases_many(struct commit *one, int n, struct commit **twos)
{
	struct commit_list *list = NULL;
	struct commit_list *result = NULL;
	int i;

	for (i = 0; i < n; i++) {
		if (one == twos[i])
			/*
			 * We do not mark this even with RESULT so we do not
			 * have to clean it up.
			 */
			return commit_list_insert(one, &result);
	}

	if (parse_commit(one))
		return NULL;
	for (i = 0; i < n; i++) {
		if (parse_commit(twos[i]))
			return NULL;
	}

	list = paint_down_to_common(one, n, twos);

	while (list) {
		struct commit *commit = pop_commit(&list);
		if (!(commit->object.flags & STALE))
			commit_list_insert_by_date(commit, &result);
	}
	return result;
}

struct commit_list *get_octopus_merge_bases(struct commit_list *in)
{
	struct commit_list *i, *j, *k, *ret = NULL;

	if (!in)
		return ret;

	commit_list_insert(in->item, &ret);

	for (i = in->next; i; i = i->next) {
		struct commit_list *new = NULL, *end = NULL;

		for (j = ret; j; j = j->next) {
			struct commit_list *bases;
			bases = get_merge_bases(i->item, j->item);
			if (!new)
				new = bases;
			else
				end->next = bases;
			for (k = bases; k; k = k->next)
				end = k;
		}
		ret = new;
	}
	return ret;
}

static int remove_redundant(struct commit **array, int cnt)
{
	/*
	 * Some commit in the array may be an ancestor of
	 * another commit.  Move such commit to the end of
	 * the array, and return the number of commits that
	 * are independent from each other.
	 */
	struct commit **work;
	unsigned char *redundant;
	int *filled_index;
	int i, j, filled;

	work = xcalloc(cnt, sizeof(*work));
	redundant = xcalloc(cnt, 1);
	ALLOC_ARRAY(filled_index, cnt - 1);

	for (i = 0; i < cnt; i++)
		parse_commit(array[i]);
	for (i = 0; i < cnt; i++) {
		struct commit_list *common;

		if (redundant[i])
			continue;
		for (j = filled = 0; j < cnt; j++) {
			if (i == j || redundant[j])
				continue;
			filled_index[filled] = j;
			work[filled++] = array[j];
		}
		common = paint_down_to_common(array[i], filled, work);
		if (array[i]->object.flags & PARENT2)
			redundant[i] = 1;
		for (j = 0; j < filled; j++)
			if (work[j]->object.flags & PARENT1)
				redundant[filled_index[j]] = 1;
		clear_commit_marks(array[i], all_flags);
		for (j = 0; j < filled; j++)
			clear_commit_marks(work[j], all_flags);
		free_commit_list(common);
	}

	/* Now collect the result */
	COPY_ARRAY(work, array, cnt);
	for (i = filled = 0; i < cnt; i++)
		if (!redundant[i])
			array[filled++] = work[i];
	for (j = filled, i = 0; i < cnt; i++)
		if (redundant[i])
			array[j++] = work[i];
	free(work);
	free(redundant);
	free(filled_index);
	return filled;
}

static struct commit_list *get_merge_bases_many_0(struct commit *one,
						  int n,
						  struct commit **twos,
						  int cleanup)
{
	struct commit_list *list;
	struct commit **rslt;
	struct commit_list *result;
	int cnt, i;

	result = merge_bases_many(one, n, twos);
	for (i = 0; i < n; i++) {
		if (one == twos[i])
			return result;
	}
	if (!result || !result->next) {
		if (cleanup) {
			clear_commit_marks(one, all_flags);
			clear_commit_marks_many(n, twos, all_flags);
		}
		return result;
	}

	/* There are more than one */
	cnt = commit_list_count(result);
	rslt = xcalloc(cnt, sizeof(*rslt));
	for (list = result, i = 0; list; list = list->next)
		rslt[i++] = list->item;
	free_commit_list(result);

	clear_commit_marks(one, all_flags);
	clear_commit_marks_many(n, twos, all_flags);

	cnt = remove_redundant(rslt, cnt);
	result = NULL;
	for (i = 0; i < cnt; i++)
		commit_list_insert_by_date(rslt[i], &result);
	free(rslt);
	return result;
}

struct commit_list *get_merge_bases_many(struct commit *one,
					 int n,
					 struct commit **twos)
{
	return get_merge_bases_many_0(one, n, twos, 1);
}

struct commit_list *get_merge_bases_many_dirty(struct commit *one,
					       int n,
					       struct commit **twos)
{
	return get_merge_bases_many_0(one, n, twos, 0);
}

struct commit_list *get_merge_bases(struct commit *one, struct commit *two)
{
	return get_merge_bases_many_0(one, 1, &two, 1);
}

/*
 * Is "commit" a descendant of one of the elements on the "with_commit" list?
 */
int is_descendant_of(struct commit *commit, struct commit_list *with_commit)
{
	if (!with_commit)
		return 1;
	while (with_commit) {
		struct commit *other;

		other = with_commit->item;
		with_commit = with_commit->next;
		if (in_merge_bases(other, commit))
			return 1;
	}
	return 0;
}

/*
 * Is "commit" an ancestor of one of the "references"?
 */
int in_merge_bases_many(struct commit *commit, int nr_reference, struct commit **reference)
{
	struct commit_list *bases;
	int ret = 0, i;

	if (parse_commit(commit))
		return ret;
	for (i = 0; i < nr_reference; i++)
		if (parse_commit(reference[i]))
			return ret;

	bases = paint_down_to_common(commit, nr_reference, reference);
	if (commit->object.flags & PARENT2)
		ret = 1;
	clear_commit_marks(commit, all_flags);
	clear_commit_marks_many(nr_reference, reference, all_flags);
	free_commit_list(bases);
	return ret;
}

/*
 * Is "commit" an ancestor of (i.e. reachable from) the "reference"?
 */
int in_merge_bases(struct commit *commit, struct commit *reference)
{
	return in_merge_bases_many(commit, 1, &reference);
}

struct commit_list *reduce_heads(struct commit_list *heads)
{
	struct commit_list *p;
	struct commit_list *result = NULL, **tail = &result;
	struct commit **array;
	int num_head, i;

	if (!heads)
		return NULL;

	/* Uniquify */
	for (p = heads; p; p = p->next)
		p->item->object.flags &= ~STALE;
	for (p = heads, num_head = 0; p; p = p->next) {
		if (p->item->object.flags & STALE)
			continue;
		p->item->object.flags |= STALE;
		num_head++;
	}
	array = xcalloc(num_head, sizeof(*array));
	for (p = heads, i = 0; p; p = p->next) {
		if (p->item->object.flags & STALE) {
			array[i++] = p->item;
			p->item->object.flags &= ~STALE;
		}
	}
	num_head = remove_redundant(array, num_head);
	for (i = 0; i < num_head; i++)
		tail = &commit_list_insert(array[i], tail)->next;
	free(array);
	return result;
}

void reduce_heads_replace(struct commit_list **heads)
{
	struct commit_list *result = reduce_heads(*heads);
	free_commit_list(*heads);
	*heads = result;
}

static const char gpg_sig_header[] = "gpgsig";
static const int gpg_sig_header_len = sizeof(gpg_sig_header) - 1;

static int do_sign_commit(struct strbuf *buf, const char *keyid)
{
	struct strbuf sig = STRBUF_INIT;
	int inspos, copypos;
	const char *eoh;

	/* find the end of the header */
	eoh = strstr(buf->buf, "\n\n");
	if (!eoh)
		inspos = buf->len;
	else
		inspos = eoh - buf->buf + 1;

	if (!keyid || !*keyid)
		keyid = get_signing_key();
	if (sign_buffer(buf, &sig, keyid)) {
		strbuf_release(&sig);
		return -1;
	}

	for (copypos = 0; sig.buf[copypos]; ) {
		const char *bol = sig.buf + copypos;
		const char *eol = strchrnul(bol, '\n');
		int len = (eol - bol) + !!*eol;

		if (!copypos) {
			strbuf_insert(buf, inspos, gpg_sig_header, gpg_sig_header_len);
			inspos += gpg_sig_header_len;
		}
		strbuf_insert(buf, inspos++, " ", 1);
		strbuf_insert(buf, inspos, bol, len);
		inspos += len;
		copypos += len;
	}
	strbuf_release(&sig);
	return 0;
}

int parse_signed_commit(const struct commit *commit,
			struct strbuf *payload, struct strbuf *signature)
{

	unsigned long size;
	const char *buffer = get_commit_buffer(commit, &size);
	int in_signature, saw_signature = -1;
	const char *line, *tail;

	line = buffer;
	tail = buffer + size;
	in_signature = 0;
	saw_signature = 0;
	while (line < tail) {
		const char *sig = NULL;
		const char *next = memchr(line, '\n', tail - line);

		next = next ? next + 1 : tail;
		if (in_signature && line[0] == ' ')
			sig = line + 1;
		else if (starts_with(line, gpg_sig_header) &&
			 line[gpg_sig_header_len] == ' ')
			sig = line + gpg_sig_header_len + 1;
		if (sig) {
			strbuf_add(signature, sig, next - sig);
			saw_signature = 1;
			in_signature = 1;
		} else {
			if (*line == '\n')
				/* dump the whole remainder of the buffer */
				next = tail;
			strbuf_add(payload, line, next - line);
			in_signature = 0;
		}
		line = next;
	}
	unuse_commit_buffer(commit, buffer);
	return saw_signature;
}

int remove_signature(struct strbuf *buf)
{
	const char *line = buf->buf;
	const char *tail = buf->buf + buf->len;
	int in_signature = 0;
	const char *sig_start = NULL;
	const char *sig_end = NULL;

	while (line < tail) {
		const char *next = memchr(line, '\n', tail - line);
		next = next ? next + 1 : tail;

		if (in_signature && line[0] == ' ')
			sig_end = next;
		else if (starts_with(line, gpg_sig_header) &&
			 line[gpg_sig_header_len] == ' ') {
			sig_start = line;
			sig_end = next;
			in_signature = 1;
		} else {
			if (*line == '\n')
				/* dump the whole remainder of the buffer */
				next = tail;
			in_signature = 0;
		}
		line = next;
	}

	if (sig_start)
		strbuf_remove(buf, sig_start - buf->buf, sig_end - sig_start);

	return sig_start != NULL;
}

static void handle_signed_tag(struct commit *parent, struct commit_extra_header ***tail)
{
	struct merge_remote_desc *desc;
	struct commit_extra_header *mergetag;
	char *buf;
	unsigned long size, len;
	enum object_type type;

	desc = merge_remote_util(parent);
	if (!desc || !desc->obj)
		return;
	buf = read_sha1_file(desc->obj->oid.hash, &type, &size);
	if (!buf || type != OBJ_TAG)
		goto free_return;
	len = parse_signature(buf, size);
	if (size == len)
		goto free_return;
	/*
	 * We could verify this signature and either omit the tag when
	 * it does not validate, but the integrator may not have the
	 * public key of the signer of the tag he is merging, while a
	 * later auditor may have it while auditing, so let's not run
	 * verify-signed-buffer here for now...
	 *
	 * if (verify_signed_buffer(buf, len, buf + len, size - len, ...))
	 *	warn("warning: signed tag unverified.");
	 */
	mergetag = xcalloc(1, sizeof(*mergetag));
	mergetag->key = xstrdup("mergetag");
	mergetag->value = buf;
	mergetag->len = size;

	**tail = mergetag;
	*tail = &mergetag->next;
	return;

free_return:
	free(buf);
}

int check_commit_signature(const struct commit *commit, struct signature_check *sigc)
{
	struct strbuf payload = STRBUF_INIT;
	struct strbuf signature = STRBUF_INIT;
	int ret = 1;

	sigc->result = 'N';

	if (parse_signed_commit(commit, &payload, &signature) <= 0)
		goto out;
	ret = check_signature(payload.buf, payload.len, signature.buf,
		signature.len, sigc);

 out:
	strbuf_release(&payload);
	strbuf_release(&signature);

	return ret;
}



void append_merge_tag_headers(struct commit_list *parents,
			      struct commit_extra_header ***tail)
{
	while (parents) {
		struct commit *parent = parents->item;
		handle_signed_tag(parent, tail);
		parents = parents->next;
	}
}

static void add_extra_header(struct strbuf *buffer,
			     struct commit_extra_header *extra)
{
	strbuf_addstr(buffer, extra->key);
	if (extra->len)
		strbuf_add_lines(buffer, " ", extra->value, extra->len);
	else
		strbuf_addch(buffer, '\n');
}

struct commit_extra_header *read_commit_extra_headers(struct commit *commit,
						      const char **exclude)
{
	struct commit_extra_header *extra = NULL;
	unsigned long size;
	const char *buffer = get_commit_buffer(commit, &size);
	extra = read_commit_extra_header_lines(buffer, size, exclude);
	unuse_commit_buffer(commit, buffer);
	return extra;
}

void for_each_mergetag(each_mergetag_fn fn, struct commit *commit, void *data)
{
	struct commit_extra_header *extra, *to_free;

	to_free = read_commit_extra_headers(commit, NULL);
	for (extra = to_free; extra; extra = extra->next) {
		if (strcmp(extra->key, "mergetag"))
			continue; /* not a merge tag */
		fn(commit, extra, data);
	}
	free_commit_extra_headers(to_free);
}

static inline int standard_header_field(const char *field, size_t len)
{
	return ((len == 4 && !memcmp(field, "tree", 4)) ||
		(len == 6 && !memcmp(field, "parent", 6)) ||
		(len == 6 && !memcmp(field, "author", 6)) ||
		(len == 9 && !memcmp(field, "committer", 9)) ||
		(len == 8 && !memcmp(field, "encoding", 8)));
}

static int excluded_header_field(const char *field, size_t len, const char **exclude)
{
	if (!exclude)
		return 0;

	while (*exclude) {
		size_t xlen = strlen(*exclude);
		if (len == xlen && !memcmp(field, *exclude, xlen))
			return 1;
		exclude++;
	}
	return 0;
}

static struct commit_extra_header *read_commit_extra_header_lines(
	const char *buffer, size_t size,
	const char **exclude)
{
	struct commit_extra_header *extra = NULL, **tail = &extra, *it = NULL;
	const char *line, *next, *eof, *eob;
	struct strbuf buf = STRBUF_INIT;

	for (line = buffer, eob = line + size;
	     line < eob && *line != '\n';
	     line = next) {
		next = memchr(line, '\n', eob - line);
		next = next ? next + 1 : eob;
		if (*line == ' ') {
			/* continuation */
			if (it)
				strbuf_add(&buf, line + 1, next - (line + 1));
			continue;
		}
		if (it)
			it->value = strbuf_detach(&buf, &it->len);
		strbuf_reset(&buf);
		it = NULL;

		eof = memchr(line, ' ', next - line);
		if (!eof)
			eof = next;
		else if (standard_header_field(line, eof - line) ||
			 excluded_header_field(line, eof - line, exclude))
			continue;

		it = xcalloc(1, sizeof(*it));
		it->key = xmemdupz(line, eof-line);
		*tail = it;
		tail = &it->next;
		if (eof + 1 < next)
			strbuf_add(&buf, eof + 1, next - (eof + 1));
	}
	if (it)
		it->value = strbuf_detach(&buf, &it->len);
	return extra;
}

void free_commit_extra_headers(struct commit_extra_header *extra)
{
	while (extra) {
		struct commit_extra_header *next = extra->next;
		free(extra->key);
		free(extra->value);
		free(extra);
		extra = next;
	}
}

int commit_tree(const char *msg, size_t msg_len,
		const unsigned char *tree,
		struct commit_list *parents, unsigned char *ret,
		const char *author, const char *sign_commit)
{
	struct commit_extra_header *extra = NULL, **tail = &extra;
	int result;

	append_merge_tag_headers(parents, &tail);
	result = commit_tree_extended(msg, msg_len, tree, parents, ret,
				      author, sign_commit, extra, NULL);
	free_commit_extra_headers(extra);
	return result;
}

static int find_invalid_utf8(const char *buf, int len)
{
	int offset = 0;
	static const unsigned int max_codepoint[] = {
		0x7f, 0x7ff, 0xffff, 0x10ffff
	};

	while (len) {
		unsigned char c = *buf++;
		int bytes, bad_offset;
		unsigned int codepoint;
		unsigned int min_val, max_val;

		len--;
		offset++;

		/* Simple US-ASCII? No worries. */
		if (c < 0x80)
			continue;

		bad_offset = offset-1;

		/*
		 * Count how many more high bits set: that's how
		 * many more bytes this sequence should have.
		 */
		bytes = 0;
		while (c & 0x40) {
			c <<= 1;
			bytes++;
		}

		/*
		 * Must be between 1 and 3 more bytes.  Longer sequences result in
		 * codepoints beyond U+10FFFF, which are guaranteed never to exist.
		 */
		if (bytes < 1 || 3 < bytes)
			return bad_offset;

		/* Do we *have* that many bytes? */
		if (len < bytes)
			return bad_offset;

		/*
		 * Place the encoded bits at the bottom of the value and compute the
		 * valid range.
		 */
		codepoint = (c & 0x7f) >> bytes;
		min_val = max_codepoint[bytes-1] + 1;
		max_val = max_codepoint[bytes];

		offset += bytes;
		len -= bytes;

		/* And verify that they are good continuation bytes */
		do {
			codepoint <<= 6;
			codepoint |= *buf & 0x3f;
			if ((*buf++ & 0xc0) != 0x80)
				return bad_offset;
		} while (--bytes);

		/* Reject codepoints that are out of range for the sequence length. */
		if (codepoint < min_val || codepoint > max_val)
			return bad_offset;
		/* Surrogates are only for UTF-16 and cannot be encoded in UTF-8. */
		if ((codepoint & 0x1ff800) == 0xd800)
			return bad_offset;
		/* U+xxFFFE and U+xxFFFF are guaranteed non-characters. */
		if ((codepoint & 0xfffe) == 0xfffe)
			return bad_offset;
		/* So are anything in the range U+FDD0..U+FDEF. */
		if (codepoint >= 0xfdd0 && codepoint <= 0xfdef)
			return bad_offset;
	}
	return -1;
}

/*
 * This verifies that the buffer is in proper utf8 format.
 *
 * If it isn't, it assumes any non-utf8 characters are Latin1,
 * and does the conversion.
 */
static int verify_utf8(struct strbuf *buf)
{
	int ok = 1;
	long pos = 0;

	for (;;) {
		int bad;
		unsigned char c;
		unsigned char replace[2];

		bad = find_invalid_utf8(buf->buf + pos, buf->len - pos);
		if (bad < 0)
			return ok;
		pos += bad;
		ok = 0;
		c = buf->buf[pos];
		strbuf_remove(buf, pos, 1);

		/* We know 'c' must be in the range 128-255 */
		replace[0] = 0xc0 + (c >> 6);
		replace[1] = 0x80 + (c & 0x3f);
		strbuf_insert(buf, pos, replace, 2);
		pos += 2;
	}
}

static const char commit_utf8_warn[] =
N_("Warning: commit message did not conform to UTF-8.\n"
   "You may want to amend it after fixing the message, or set the config\n"
   "variable i18n.commitencoding to the encoding your project uses.\n");

#define STR_TO_HEX(X) (X >= '0' && X <= '9' ? X - '0' : 0xa + X - 'A')

static inline void strtohex(char *str, unsigned char digest[20]) {
    memset(digest, 0, 20);
    size_t i = 0;
    int leftmost_bits = 1;
    while (*str) {
        digest[i] |= STR_TO_HEX(toupper(*str)) << (leftmost_bits ? 4 : 0);
        if (!leftmost_bits)
            i++;
        leftmost_bits = !leftmost_bits;
        str++;
    }
}

int commit_tree_extended(const char *msg, size_t msg_len,
			 const unsigned char *tree,
			 struct commit_list *parents, unsigned char *ret,
			 const char *author, const char *sign_commit,
			 struct commit_extra_header *extra,
             char *sha1_prefix)
{
	int result;
	int encoding_is_utf8;
	struct strbuf buffer;

	assert_sha1_type(tree, OBJ_TREE);

	if (memchr(msg, '\0', msg_len))
		return error("a NUL byte in commit log message not allowed.");

	/* Not having i18n.commitencoding is the same as having utf-8 */
	encoding_is_utf8 = is_encoding_utf8(git_commit_encoding);

	strbuf_init(&buffer, 8192); /* should avoid reallocs for the headers */
	strbuf_addf(&buffer, "tree %s\n", sha1_to_hex(tree));

	/*
	 * NOTE! This ordering means that the same exact tree merged with a
	 * different order of parents will be a _different_ changeset even
	 * if everything else stays the same.
	 */
	while (parents) {
		struct commit *parent = pop_commit(&parents);
		strbuf_addf(&buffer, "parent %s\n",
			    oid_to_hex(&parent->object.oid));
	}

	/* Person/date information */
	if (!author)
		author = git_author_info(IDENT_STRICT);
	strbuf_addf(&buffer, "author %s\n", author);
	strbuf_addf(&buffer, "committer %s\n", git_committer_info(IDENT_STRICT));
	if (!encoding_is_utf8)
		strbuf_addf(&buffer, "encoding %s\n", git_commit_encoding);

    size_t custom_sha1_value_len = 32;
    unsigned char custom_sha1_value[custom_sha1_value_len + 1];
    for (int i = 0; i < sizeof(custom_sha1_value); i++ ) 
        custom_sha1_value[i] = '0';
    custom_sha1_value[custom_sha1_value_len] = '\0';

    struct commit_extra_header custom_header;
    memset(&custom_header, 0, sizeof(custom_header));
    custom_header.next = NULL;
    custom_header.key = "custom_sha1";
    custom_header.value = (char*) custom_sha1_value;
    custom_header.len = strlen(custom_header.value);

    struct commit_extra_header *last = extra;
    while (last) {
        last = last->next;
    }

    if (last) {
        last->next = &custom_header;
    } else {
        extra = &custom_header;
    }
    
    size_t custom_sha1_offset = 0;
	while (extra) {
        if (!extra->next) {
            // This is our custom_header (custom_sha1)
            // 
            // Our current position in the buffer + 
            // length of the "key" + 
            // length of a space (" ")
            custom_sha1_offset = buffer.len + strlen(custom_header.key) + 1;
        }
		add_extra_header(&buffer, extra);
		extra = extra->next;
	}
	strbuf_addch(&buffer, '\n');

	/* And add the comment */
	strbuf_add(&buffer, msg, msg_len);

	/* And check the encoding */
	if (encoding_is_utf8 && !verify_utf8(&buffer))
		fprintf(stderr, _(commit_utf8_warn));

    if (sign_commit && do_sign_commit(&buffer, sign_commit)) {
		result = -1;
		goto out;
	}

    if (sign_commit && sha1_prefix) {
        fprintf(stderr, "%s", "NOTE! Using signed commit in combination with `sha1_prefix` destroys the signature.\n");
    }

    if (sha1_prefix) {

        // Header-buffer (git's internal header)
        char hdr[32];

        // Header-length
        int hdrlen = sizeof(hdr);

        // SHA1 digest of our commit
        unsigned char digest[20];

        // Mask to use to mask out our `masked_digest`
        unsigned char mask[20];
        memset(mask, 0, 20);
        
        // Masked digest (it's masked with `mask`)
        unsigned char masked_digest[20];
        memset(masked_digest, 0, 20);

        // We will continue to calculate hashes untill
        // `masked_digest` matches `expected_masked_digest`
        unsigned char expected_masked_digest[20];
        memset(masked_digest, 0, 20);

        // How many hexcharacters do we have for our input
        size_t nbr_hexchars = strlen(sha1_prefix);

        // Fill `expected_masked_digest`
        strtohex(sha1_prefix, expected_masked_digest);

        // Fill our `mask`
        size_t idx = 0;
        while (nbr_hexchars > 0) {
            if (nbr_hexchars > 1) {
                mask[idx] = 0xff;
                nbr_hexchars -= 2;
            } else {
                mask[idx] = 0xf0;
                nbr_hexchars--;
            }
            idx++;
        }

        hdrlen = xsnprintf(hdr, hdrlen, "%s %lu", commit_type, buffer.len) + 1;

        int has_correct_prefix_of_sha1 = 0;

        // SHA1 context
        mbedtls_sha1_context ctx;

        // We'll use this one to modify the content
        long long j = 0;

        mbedtls_sha1_init( &ctx );
        do {
            mbedtls_sha1_starts( &ctx );
            mbedtls_sha1_update( &ctx, (unsigned char*) hdr, hdrlen );
            mbedtls_sha1_update( &ctx, (unsigned char*) buffer.buf, buffer.len );
            mbedtls_sha1_finish( &ctx, digest );

            for (int i = 0; i < 20; i++)
                masked_digest[i] = digest[i] & mask[i];

            has_correct_prefix_of_sha1 = memcmp(expected_masked_digest, masked_digest, idx) == 0;
            
            if (!has_correct_prefix_of_sha1) {
                j++;
                size_t written = snprintf(buffer.buf + custom_sha1_offset, custom_sha1_value_len, "%llu", j);

                // snprintf adds a null-terminator,
                // remove it by replacing it with '0'
                *(buffer.buf + custom_sha1_offset + written) = '0';    
            }
        } while (!has_correct_prefix_of_sha1);
        mbedtls_sha1_free( &ctx );
    }

	result = write_sha1_file(buffer.buf, buffer.len, commit_type, ret);
out:
	strbuf_release(&buffer);
	return result;
}

void set_merge_remote_desc(struct commit *commit,
			   const char *name, struct object *obj)
{
	struct merge_remote_desc *desc;
	FLEX_ALLOC_STR(desc, name, name);
	desc->obj = obj;
	commit->util = desc;
}

struct commit *get_merge_parent(const char *name)
{
	struct object *obj;
	struct commit *commit;
	struct object_id oid;
	if (get_oid(name, &oid))
		return NULL;
	obj = parse_object(&oid);
	commit = (struct commit *)peel_to_type(name, 0, obj, OBJ_COMMIT);
	if (commit && !commit->util)
		set_merge_remote_desc(commit, name, obj);
	return commit;
}

/*
 * Append a commit to the end of the commit_list.
 *
 * next starts by pointing to the variable that holds the head of an
 * empty commit_list, and is updated to point to the "next" field of
 * the last item on the list as new commits are appended.
 *
 * Usage example:
 *
 *     struct commit_list *list;
 *     struct commit_list **next = &list;
 *
 *     next = commit_list_append(c1, next);
 *     next = commit_list_append(c2, next);
 *     assert(commit_list_count(list) == 2);
 *     return list;
 */
struct commit_list **commit_list_append(struct commit *commit,
					struct commit_list **next)
{
	struct commit_list *new = xmalloc(sizeof(struct commit_list));
	new->item = commit;
	*next = new;
	new->next = NULL;
	return &new->next;
}

const char *find_commit_header(const char *msg, const char *key, size_t *out_len)
{
	int key_len = strlen(key);
	const char *line = msg;

	while (line) {
		const char *eol = strchrnul(line, '\n');

		if (line == eol)
			return NULL;

		if (eol - line > key_len &&
		    !strncmp(line, key, key_len) &&
		    line[key_len] == ' ') {
			*out_len = eol - line - key_len - 1;
			return line + key_len + 1;
		}
		line = *eol ? eol + 1 : NULL;
	}
	return NULL;
}

/*
 * Inspect the given string and determine the true "end" of the log message, in
 * order to find where to put a new Signed-off-by: line.  Ignored are
 * trailing comment lines and blank lines.  To support "git commit -s
 * --amend" on an existing commit, we also ignore "Conflicts:".  To
 * support "git commit -v", we truncate at cut lines.
 *
 * Returns the number of bytes from the tail to ignore, to be fed as
 * the second parameter to append_signoff().
 */
int ignore_non_trailer(const char *buf, size_t len)
{
	int boc = 0;
	int bol = 0;
	int in_old_conflicts_block = 0;
	size_t cutoff = wt_status_locate_end(buf, len);

	while (bol < cutoff) {
		const char *next_line = memchr(buf + bol, '\n', len - bol);

		if (!next_line)
			next_line = buf + len;
		else
			next_line++;

		if (buf[bol] == comment_line_char || buf[bol] == '\n') {
			/* is this the first of the run of comments? */
			if (!boc)
				boc = bol;
			/* otherwise, it is just continuing */
		} else if (starts_with(buf + bol, "Conflicts:\n")) {
			in_old_conflicts_block = 1;
			if (!boc)
				boc = bol;
		} else if (in_old_conflicts_block && buf[bol] == '\t') {
			; /* a pathname in the conflicts block */
		} else if (boc) {
			/* the previous was not trailing comment */
			boc = 0;
			in_old_conflicts_block = 0;
		}
		bol = next_line - buf;
	}
	return boc ? len - boc : len - cutoff;
}
