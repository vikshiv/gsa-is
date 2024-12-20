// vim: noai:ts=2:sw=2

/* 
 * Authors: Felipe A. Louza, Simon Gog, Guilherme P. Telles
 * contact: louza@ic.unicamp.br
 * 03/04/2017
 */

/* 
 * This code is a modification of SACA-K algorithm by G. Nong, which can be
 * retrieved at: http://code.google.com/p/ge-nong/ 
 *
 * Our version of SACA-K, called gSACA-K, maintain the theoretical bounds of the
 * original algorithm to construct the generalized suffix array.
 *
 * Our algorithm gSACA-K can also computes the LCP-array and the Document-array
 * with no additional costs.
 * 
 * gsacak(s, SA, NULL, NULL, n) //computes only SA
 * gsacak(s, SA, LCP,  NULL, n) //computes SA and LCP
 * gsacak(s, SA, NULL, DA, n)   //computes SA and DA
 * gsacak(s, SA, LCP,  DA, n)   //computes SA, LCP and DA
 * 
 */

/******************************************************************************/

#ifndef GSACAK_H
#define GSACAK_H

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>

#define maxval(a,b) ((a) > (b) ? (a) : (b))

#ifndef DEBUG
	#define DEBUG 0
#endif

#ifndef M64
	#define M64 0
#endif

// Define the uint40 type as a struct
typedef struct {
    uint32_t low;
    uint8_t high;
} uint40_t;

// Constants
#define UINT40_MAX ((uint64_t)(1ULL << 40) - 1)
#define UINT40_EMPTY (1ULL << 39)

// Helper functions for uint40_t
static inline uint40_t uint40_from_u64(uint64_t val) {
    uint40_t result;
    result.low = val & 0xFFFFFFFF;
    result.high = (val >> 32) & 0xFF;
    return result;
}

static inline uint64_t uint40_to_u64(uint40_t val) {
    return ((uint64_t)val.high << 32) | val.low;
}

static inline int uint40_lt(uint40_t a, uint40_t b) {
    return (a.high < b.high) || (a.high == b.high && a.low < b.low);
}

static inline int uint40_gt(uint40_t a, uint40_t b) {
    return (a.high > b.high) || (a.high == b.high && a.low > b.low);
}

static inline int uint40_eq(uint40_t a, uint40_t b) {
    return a.high == b.high && a.low == b.low;
}

static inline uint40_t uint40_add(uint40_t a, uint40_t b) {
    uint64_t sum = uint40_to_u64(a) + uint40_to_u64(b);
    return uint40_from_u64(sum);
}

static inline uint40_t uint40_sub(uint40_t a, uint40_t b) {
    uint64_t diff = uint40_to_u64(a) - uint40_to_u64(b);
    return uint40_from_u64(diff);
}

static inline uint40_t uint40_inc(uint40_t a) {
    if (a.low == 0xFFFFFFFF) {
        a.low = 0;
        a.high++;
    } else {
        a.low++;
    }
    return a;
}

static inline uint40_t uint40_dec(uint40_t a) {
    if (a.low == 0) {
        a.low = 0xFFFFFFFF;
        a.high--;
    } else {
        a.low--;
    }
    return a;
}

#if M64
	typedef int64_t int_t;
	typedef uint40_t uint_t;
	#define PRIdN PRId64
	#define U_MAX uint40_from_u64(UINT40_MAX)
	#define I_MAX INT64_MAX
	#define I_MIN INT64_MIN
#else
	typedef int32_t int_t;
	typedef uint40_t uint_t;
	#define PRIdN PRId32
	#define U_MAX uint40_from_u64(UINT40_MAX)
	#define I_MAX INT32_MAX
	#define I_MIN INT32_MIN
#endif

/*! @option type of s[0,n-1] for integer alphabets 
 *
 *  @constraint sizeof(int_t) >= sizeof(int_text) 
 */
typedef uint32_t int_text;	//4N bytes for s[0..n-1]
#define PRIdT	PRIu32

/*! @option type for array DA
 */
typedef uint_t int_da;

/******************************************************************************/

/** @brief computes the suffix array of string s[0..n-1] 
 *
 *  @param s	input string with s[n-1]=0
 *  @param SA		suffix array 
 *  @param n	string length
 *  @return -1 if an error occured, otherwise the depth of the recursive calls.
 */
int sacak(unsigned char *s, uint_t *SA, uint64_t n);

/** @brief computes the suffix array of string s[0..n-1]
 *
 *  @param k	alphabet size+1 (0 is reserved)
 */
int sacak_int(int_text *s, uint_t *SA, uint64_t n, uint64_t k);

/******************************************************************************/

/** @brief Computes the suffix array SA (LCP, DA) of T^cat in s[0..n-1]
 *
 *  @param s		input concatenated string, using separators s[i]=1 and with s[n-1]=0
 *  @param SA		Suffix array 
 *  @param LCP	LCP array 
 *  @param DA		Document array
 *  @param n		String length
 *  
 *  @return depth of the recursive calls.
 */
int gsacak(unsigned char *s, uint_t *SA, int_t *LCP, int_da *DA, uint64_t n);

/** @brief Computes the suffix array SA (LCP, DA) of T^cat in s[0..n-1]
 *
 *  @param s		input concatenated string, using separators s[i]=1 and with s[n-1]=0
 *  @param SA		Suffix array 
 *  @param LCP	LCP array 
 *  @param DA		Document array
 *  @param n		String length
 *  @param k    alphabet size+2 (0 and 1 are reserved)
 *
 *  @return depth of the recursive calls.
 */
int gsacak_int(int_text *s, uint_t *SA, int_t *LCP, int_da *DA, uint64_t n, uint64_t k);

/******************************************************************************/

void getBuckets_k(int_t *s, uint_t *bkt, uint64_t n, unsigned int K, int end, int cs);
void putSuffix0(uint_t *SA, int_t *s, uint_t *bkt, uint64_t n, unsigned int K, int64_t n1, int cs);
void induceSAl0(uint_t *SA, int_t *s, uint_t *bkt, uint64_t n, unsigned int K, int_t suffix, int cs);
void induceSAs0(uint_t *SA, int_t *s, uint_t *bkt, uint64_t n, unsigned int K, int_t suffix, int cs);

#endif
