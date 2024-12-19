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

#if M64
	typedef int64_t	int_t;
	typedef uint40 uint_t;
	#define PRIdN	PRId64
	#define U_MAX	uint40((1ULL << 40) - 1)
	#define I_MAX	INT64_MAX
	#define I_MIN	INT64_MIN
#else
	typedef int32_t int_t;
	typedef uint40 uint_t;
	#define PRIdN	PRId32
	#define U_MAX	uint40((1ULL << 40) - 1)
	#define I_MAX	INT32_MAX
	#define I_MIN	INT32_MIN
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
int sacak(unsigned char *s, uint40 *SA, uint64_t n);

/** @brief computes the suffix array of string s[0..n-1]
 *
 *  @param k	alphabet size+1 (0 is reserved)
 */
int sacak_int(int_text *s, uint40 *SA, uint64_t n, uint64_t k);

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
int gsacak(unsigned char *s, uint40 *SA, int_t *LCP, int_da *DA, uint64_t n);

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
int gsacak_int(int_text *s, uint40 *SA, int_t *LCP, int_da *DA, uint64_t n, uint64_t k);

/******************************************************************************/

class uint40 {
private:
    uint32_t low;
    uint8_t high;

public:
    uint40() : low(0), high(0) {}
    
    uint40(uint64_t val) {
        low = val & 0xFFFFFFFF;
        high = (val >> 32) & 0xFF;
    }

    operator uint64_t() const {
        return ((uint64_t)high << 32) | low;
    }

    // Comparison operators
    bool operator<(const uint40& other) const {
        if (high != other.high)
            return high < other.high;
        return low < other.low;
    }
    bool operator>(const uint40& other) const {
        if (high != other.high)
            return high > other.high;
        return low > other.low;
    }
    bool operator<=(const uint40& other) const {
        if (high != other.high)
            return high < other.high;
        return low <= other.low;
    }
    bool operator>=(const uint40& other) const {
        if (high != other.high)
            return high > other.high;
        return low >= other.low;
    }
    bool operator==(const uint40& other) const {
        return high == other.high && low == other.low;
    }
    bool operator!=(const uint40& other) const {
        return high != other.high || low != other.low;
    }

    // Assignment operators
    uint40& operator=(const uint40& other) {
        if (this != &other) {
            low = other.low;
            high = other.high;
        }
        return *this;
    }
    uint40& operator=(uint64_t val) {
        low = val & 0xFFFFFFFF;
        high = (val >> 32) & 0xFF;
        return *this;
    }

    // Arithmetic operators
    uint40 operator+(const uint40& other) const {
        uint64_t sum = (uint64_t)*this + (uint64_t)other;
        return uint40(sum);
    }
    uint40 operator-(const uint40& other) const {
        uint64_t diff = (uint64_t)*this - (uint64_t)other;
        return uint40(diff);
    }
    uint40& operator++() {
        if (low == 0xFFFFFFFF) {
            low = 0;
            high++;
        } else {
            low++;
        }
        return *this;
    }
    uint40 operator++(int) {
        uint40 temp = *this;
        ++*this;
        return temp;
    }
    uint40& operator--() {
        if (low == 0) {
            low = 0xFFFFFFFF;
            high--;
        } else {
            low--;
        }
        return *this;
    }
    uint40 operator--(int) {
        uint40 temp = *this;
        --*this;
        return temp;
    }
};

// Add constants for uint40
const uint40 U_MAX = uint40((1ULL << 40) - 1);
const uint40 EMPTY_k = uint40(1ULL << 39);

void getBuckets_k(int_t *s, uint40 *bkt, uint64_t n, unsigned int K, int end, int cs);
void putSuffix0(uint40 *SA, int_t *s, uint40 *bkt, uint64_t n, unsigned int K, int64_t n1, int cs);
void induceSAl0(uint40 *SA, int_t *s, uint40 *bkt, uint64_t n, unsigned int K, int_t suffix, int cs);
void induceSAs0(uint40 *SA, int_t *s, uint40 *bkt, uint64_t n, unsigned int K, int_t suffix, int cs);

#endif
