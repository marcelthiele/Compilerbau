/***************************************************************************//**
 * @file vec.h
 * @author Dorian Weber
 * @brief Generic vector type.
 * 
 * @details
 * This file contains an implementation of a generic vector type. In order to
 * determine what kind of elements this vector holds, you declare a variable
 * that is a pointer to the type of elements. You can then proceed to initialize
 * and use this pointer as if it was pointing to a variable-length array.
 * 
 * Here is a usage example:
 * @code
 * int *vec = NULL;
 * 
 * vecPush(vec) = 1;
 * vecPush(vec) = 2;
 * vecPush(vec) = 3;
 * 
 * while (!vecIsEmpty(vec))
 * 	printf("%i\n", vecPop(vec));
 * 
 * vecRelease(vec);
 * @endcode
 * 
 * Many of the functions used are implemented in terms of macros that update
 * the variable holding the pointer to the array, even though it seems like
 * only one value is used throughout the program. This makes it risky to hold
 * pointers to the array in different variables, since resizes may invalidate
 * those. Even though these issues are subtle and potentially bug-prone — this
 * is an extremely leaky abstraction — I have found that it is nevertheless a
 * massive productivity boost; you just need to be vaguely aware of what's
 * going on under the hood so as to use the appropriate subset of programming
 * techniques that work correctly.
 ******************************************************************************/

#ifndef VEC_H_INCLUDED
#define VEC_H_INCLUDED

/* *** includes ************************************************************* */

#include <stddef.h>

/* *** structures *********************************************************** */

/**
 * @internal
 * Structure prepended to the array for bookkeeping purposes.
 */
typedef struct {
	size_t len; /**<@brief Anzahl der Elemente im Vektor. */
	size_t cap; /**<@brief Kapazität des reservierten Speichers. */
} VecHeader;

/* *** interface ************************************************************ */

/**
 * @internal
 * Allocates memory for the array. 
 * 
 * The length of the array is initialized to 0.
 * 
 * @param size      the size of the elements in the array
 * @param capacity  the initial minimum capacity
 * 
 * @return the pointer to a new array
 */
extern void* vecInit(size_t capacity, size_t size);

/**
 * @brief Initializes a new array.
 * 
 * Initializing the pointer with `NULL` is also a valid way of initializing
 * the vector.
 * 
 * @param self  the array
 */
#define vecInit(self) \
	(self = vecInit(8, sizeof(*(self))))

/**
 * @brief Releases the memory of a vector.
 * @param self  the vector to release
 */
extern void vecRelease(void *self);

/**
 * @internal
 * @brief Reserves space for a new value in the vector.
 * @param self  the vector
 * @param size  size of vector elements
 * @return the new pointer to the start of the vector
 */
extern void* vecPush(void *self, size_t size);

/**
 * Adds one element to the back of the vector and returns an lvalue reference.
 * 
 * This method can be used like this:
```
	float *myVec = NULL;
	vecPush(myVec) = 0.5;
```
 */
#define vecPush(self) \
	(self = vecPush(self, sizeof((self)[0])), (self)+vecLen(self)-1)[0]

/**
 * @internal
 * @brief Deletes the last element of the vector.
 * @param self  the vector
 */
extern void vecPop(void *self);

/**
 * Removes an element from the back of the vector and returns an lvalue
 * reference.
 * 
 * This macro can be used like this:
```
	float *myVec;
	float x;

	vecInit(myVec, 4);
	vecPush(myVec) = 0.5;
	vecPush(myVec) = 1.5;
	vecPush(myVec) = 2.5;

	x = vecPop(myVec); // yields 2.5
```
 */
#define vecPop(self) \
	(vecPop(self), (self)+vecLen(self))[0]

/**
 * @brief Returns the last element of the vector.
 * @param self  the vector
 * @return lvalue reference to the topmost element of \p self
 */
#define vecTop(self) \
	(self)[vecLen(self) - 1]

/**
 * Loops over each element of the vector in order.
 * 
 * You can use it like this:
```
	float *myVec = NULL;

	vecPush(myVec) = 0.5;
	vecPush(myVec) = 1.5;
	vecPush(myVec) = 2.5;

	vecForEach(float *x, myVec) {
		// do stuff with x
	}
```
 */
#define vecForEach(var, vec) \
	for (register size_t it = 0, c = 0; (c ^= 1) && it < vecLen(vec); ++it) \
		for (var = &(vec)[it]; c != 0; c = 0)

/**
 * @brief Returns whether the vector is empty.
 * @param self  the vector
 * @return 0, if not empty\n
 *      != 0, if empty
 */
extern int vecIsEmpty(const void *self);

/**
 * @brief Returns the number of vector elements in use.
 * @param self  the vector
 * @return number of elements in \p self
 */
extern unsigned int vecLen(const void *self);

#endif /* VEC_H_INCLUDED */
