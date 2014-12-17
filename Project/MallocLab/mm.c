/*
 * mm.c
 * Name: Chih-Feng Lin
 * Andrew ID: chihfenl
 *
 * This malloc algorithm is based on "Segregated Fits" method mentioned in the CSAPP 2e.
 * The allocator maintains the segregated array of free list. Each free list here we use
 * explicit free list method. For the Find_fit algorithm, we simply use first-fit search
 * to firstly find the appropriate class size and then search free list of that class. If
 * we can not find a fit, then we search the free list for the next larger size class. If
 * none of the free lists yields a block that fits, we use extend_heap function to ask OS
 * for more heap space. Also, when we place the allocated block to the free block, we will
 * use split technique to reset remainder free block to reduce internal fragmentation. For
 * realloc function, we just use naive implementation to check the size of old and new alloc
 * one. If the new size is larger than old size, we use memcpy method to copy the data of
 * memory to the new position. Otherwise, we just use place() to place the new size into old
 * position.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"

// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
printf("Checkheap failed on line %d\n", __LINE__);\
exit(-1);  \
}}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif


/*
 *  Helper functions
 *  ----------------
 */

/*
 *Self-defined functions and variables
 */

#define WSIZE		    4
#define DSIZE		    8
#define CHUNKSIZE	    (1 << 6)
#define BLOCKSIZE_MIN	    4
#define CLASS_NUMBER        12
#define MAX(x, y)    ((x) > (y) ? (x) : (y))
#define MIN(x, y)    ((x) > (y) ? (y) : (x))
#define PACK(size, alloc)    ((size) | (alloc << 30))
#define CONVERT_32_TO_64(value)    (!(value)? (void *) (NULL) : (void *) (0x800000000 + value))
#define CONVERT_64_TO_32(value)    (!(value)? 0 : (uint32_t)( (long) value - 0x800000000))

typedef uint32_t* block_pointer;
static block_pointer heap_listp = NULL;
static block_pointer* seg_array;

/*Function protitypes for the internal routines*/

static inline void* align(const void const* p, unsigned char w);
static inline int aligned(const void const* p);
static int in_heap(const void* p);
static block_pointer block_next(block_pointer const block);
static block_pointer block_prev(block_pointer const block);
static inline int block_free(const block_pointer block);
static inline void block_mark(block_pointer block, int free);
static block_pointer block_mem(block_pointer const block);
static inline unsigned int block_size(const block_pointer block);

static inline void put(block_pointer block, unsigned int val);
static inline unsigned int get(block_pointer block);
static inline block_pointer block_header(block_pointer block);
static inline block_pointer block_footer(block_pointer block);
static inline void set_pred_ptr(block_pointer block, block_pointer pred);
static inline void set_succ_ptr(block_pointer block, block_pointer succ);
static inline block_pointer get_pred_ptr(block_pointer block);
static inline block_pointer get_succ_ptr(block_pointer block);

int mm_init(void);
static block_pointer extend_heap(size_t words);
static int init_block(block_pointer block, size_t size);
static void add_to_free_list(block_pointer block);
static block_pointer find_first_fit(size_t size);
static block_pointer coalesce(block_pointer bp);
static void delete_block(block_pointer pointer);
static block_pointer combine_block(block_pointer first, block_pointer second);
void *malloc(size_t size);
void free(void *ptr);
static void place(block_pointer bp, size_t size);
void *realloc(void *oldptr, size_t size);
void *calloc(size_t nmemb, size_t size);
static int get_class_no(size_t size);

int mm_checkheap(int verbose);
static void check_in_heap(block_pointer bp);
static void checkblock_align(void *bp);
static void check_header_footer(block_pointer bp);
static void check_coalescing(block_pointer bp);
static void check_prev_next_ptr(block_pointer bp);
int inverse_get_class_no(int class);
static void check_seg_list(void);


/*Helper Function*/
/* Align p to a multiple of w bytes */
static inline void* align(const void const* p, unsigned char w) {
    return((void *) (((uintptr_t) (p) + (w - 1)) & ~(w - 1)));
}


/* Check if the given pointer is 8-byte aligned */
static inline int aligned(const void const* p) {
    return(align(p, 8) == p);
}


/* Return whether the pointer is in the heap. */
static int in_heap(const void* p) {
    return(p <= mem_heap_hi() && p >= mem_heap_lo());
}


/*Get next block throught header*/
/*Here we slightly modify the return value to make block_size include header and footer*/
static block_pointer block_next(block_pointer const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return block + block_size(block);
}


/*Get previous block through footer*/
/*Here we slightly modify the return value to make block_size include header and footer*/
static block_pointer block_prev(block_pointer const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return block - block_size(block - 1);
}

/* Return true if the block is free, false otherwise */
static inline int block_free(const block_pointer block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return(!(block[0] & 0x40000000));
}


/* Mark the given block as free(1)/alloced(0) by marking the block_header and footer. */
static inline void block_mark(block_pointer block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    unsigned int next;
    size_t size = block_size(block);
    
    if (size == 0)
    next = 0;
    else
    next = block_size(block) - 1;
    
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
}

/*Return the pointer of the block payload part*/
static block_pointer block_mem(block_pointer const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(in_heap(block + 1));
    return block + 1;
}

/* Return the size of the given block in multiples of the word size */
static inline unsigned int block_size(const block_pointer block ) {
    REQUIRES( block != NULL );
    REQUIRES( in_heap( block ) );
    
    return(block[0] & 0x3FFFFFFF);
}


/*
 *Self-defined static function.
 *Base on the above pre-provided function, we modify them to create the
 *following helper (Here is referenced from CSAPP 2e)
 */

/* Write the value to an address block*/
static inline void put(block_pointer block, unsigned int val) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    *block = val;
}


/* Read the value from an address block*/
static inline unsigned int get( block_pointer block ){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return *block;
}

/*Return the block header*/
static inline block_pointer block_header(block_pointer block){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return block - 1;
}

/*Return the block footer*/
static inline block_pointer block_footer(block_pointer block){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return block + block_size(block) - 1;
}

/*
 *Self-defined static function. - Manupulation segregated free list
 *For each free list of segregated array, here implements explicit free list
 *method. Threrfore, we need to use extra two pointer, pred and succ, to represent
 *the address of previous block and next block.
 */

/*Set pointer of previous block in the current block*/
static inline void set_pred_ptr(block_pointer block, block_pointer pred) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(pred != NULL);
    REQUIRES(in_heap(pred));
    
    *(block + 1) = CONVERT_64_TO_32(pred);
}

/*Set pointer of next block in the current block*/
static inline void set_succ_ptr(block_pointer block, block_pointer succ) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(succ != NULL);
    REQUIRES(in_heap(succ));
    
    *(block + 2) = CONVERT_64_TO_32(succ);
}

/*Get pointer of previous block in the free list*/
static inline block_pointer get_pred_ptr(block_pointer block){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return CONVERT_32_TO_64(*(block + 1));
}

/*Get pointer of next block in the free list**/
static inline block_pointer get_succ_ptr(block_pointer block){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    
    return CONVERT_32_TO_64(*(block + 2));
}




/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    block_pointer init_alloc;
    int i;
    
    /*Initialize segregated array */
    seg_array = (block_pointer*)mem_sbrk(sizeof(block_pointer) * CLASS_NUMBER);
    for (i = 0; i < CLASS_NUMBER; ++i) {
        /*Make each item of segregated list as NULL intially*/
        seg_array[i] = NULL;
    }
    
    /*Create the initial empty heap*/
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*) -1) {
        dbg_printf("mm_init error\n");
        return -1;
    }
    
    put(heap_listp, PACK(2, 0));       /*Alignment padding*/
    put(heap_listp + 1, PACK(2, 1));   /*Prologue header*/
    put(heap_listp + 2, PACK(2, 1));   /*Prologue footer*/
    put(heap_listp + 3, PACK(0, 0));   /*Epilogue header*/
    heap_listp += (2 * 1);
    
    /*Extend the empty heap with free block of CHUNKSIZE bytes*/
    if((init_alloc = extend_heap(CHUNKSIZE)) == NULL) {
        dbg_printf("extend_heap error\n");
        return -1;
    }
    
    /*Based on given init_alloc pointer by extend_heap(), here initializes a free block*/
    if(init_block(init_alloc, block_size(init_alloc)) != 0) {
        dbg_printf("Error in init_block\n");
        return -1;
    }
    
    /*
     * Based on segregated list method, we should insert free block into specific free list
     * of segregated array according to its size.
     */
    add_to_free_list(init_alloc);
    return 0;
}

/*Extends heap with free block and return its block pointer*/
static block_pointer extend_heap(size_t words) {
    
    size_t size;
    block_pointer bp, block;
    
    /*Allocate even number of words to maintain alignment*/
    size = (words % 2) ? (words + 1) : words;
    if((long)(bp = mem_sbrk(size * WSIZE)) == -1) {
        dbg_printf("mem_sbrk error\n");
        return NULL;
    }
    
    block = block_header(bp);
    
    if((init_block(block, size)) != 0) {     /*Set size to the block header and footer*/
        dbg_printf("Error in init_block\n");
        return (block_pointer) -1;
    }
    put(block_next(block), PACK(0, 1));      /*New epilogue header*/
    
    return block;
}

/*Initialize a block, set block size to its header and footer*/
int init_block(block_pointer block, size_t size) {
    
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    block_pointer temp;
    
    /*Set the size to the header and footer of block*/
    block[0] = size;
    temp = block_footer(block);
    temp[0] = size;
    
    /* I use explicit free list, thus we need two extra word size to
     * represent pred and suuc. Set next and prev block in the free list to NULL,
     * and mark them as free.
     */
    set_pred_ptr(block, (block_pointer)NULL);
    set_succ_ptr(block, (block_pointer)NULL);
    block_mark(block, 1);
    
    return 0;
}

/*Insert a free block into the size-matched free list*/
void add_to_free_list(block_pointer block){
    
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    size_t size;
    int class_no;
    
    /*According to block size, use get_class_no function to return which class it belongs to.*/
    size = block_size(block);
    class_no = get_class_no(size);
    
    if ((init_block(block, size)) != 0) {
        dbg_printf("Error in init_block\n");
        return;
    }
    
    block_mark(block, 1);   /*Mark the block as free*/
    
    /*If found free list is NULL, we can directly insert current block.*/
    if(seg_array[class_no] == NULL) {
        seg_array[class_no] = block;
    }
    
    /*
     * Otherwise, we insert current block in the front of free list via
     * setting pred and succ pointers
     */
    else {
        set_pred_ptr(seg_array[class_no], block);
        set_succ_ptr(block, seg_array[class_no]);
        seg_array[class_no] = block;
    }
}


/*Use first fit algorithm*/
block_pointer find_first_fit(size_t size) {
    int class_no;
    block_pointer freelist_head_ptr;
    
    class_no = get_class_no(size);
    
    /*Find the best fit one */
    /*If original class does not find fit one, we search the free list for the next larger size class*/
    for(int i = class_no; i < CLASS_NUMBER; ++i) {
        freelist_head_ptr = seg_array[i];
        
        while(freelist_head_ptr) {
            if(block_size(freelist_head_ptr) >= size) {
                return freelist_head_ptr;
            }
            /*Search whole size-matched free list*/
            freelist_head_ptr = get_succ_ptr(freelist_head_ptr);
        }
    }
    
    return (block_pointer)NULL;
}

/* Coalesce the memory - We check prev_pointer and next_pointer and classify them into 4 cases*/
static block_pointer coalesce(block_pointer bp) {
    
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    
    block_pointer prev_pointer, next_pointer, result;
    
    prev_pointer = block_prev(bp);
    next_pointer = block_next(bp);
    
    result = bp;
    
    if(!block_free(prev_pointer) && !block_free(next_pointer)) {       /*Case1*/
        return result;
    }
    
    else if(block_free(prev_pointer) && !block_free(next_pointer)) {   /*Case2*/
        delete_block(prev_pointer);
        result = combine_block(prev_pointer, bp);
    }
    
    else if(!block_free(prev_pointer) && block_free(next_pointer)){    /*Case3*/
        delete_block(next_pointer);
        result = combine_block(bp, next_pointer);
    }
    
    else {                                                             /*Case4*/
        delete_block(prev_pointer);
        delete_block(next_pointer);
        result = combine_block(prev_pointer, bp);
        result = combine_block(result, next_pointer);
    }
    
    return result;
}

/*
 * Delete the block from free list -
 * Before placing or allocating, we need to delete slected free block from free list.
 * Therefore, we use this function to achieve this object.
 */
void delete_block(block_pointer block) {
    
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    size_t size;
    int class_no;
    
    block_pointer prev = get_pred_ptr(block);
    block_pointer next = get_succ_ptr(block);
    
    /*If selected block is the head of the free list*/
    if(prev == NULL) {
        size = block_size(block);
        class_no = get_class_no(size);
        
        if(next == NULL) {
            seg_array[class_no] = NULL;
        } else {
            set_pred_ptr(next, NULL);
            seg_array[class_no] = next;
        }
    }
    
    /*If selected block is not the head of the free list*/
    else if(prev != NULL) {
        set_succ_ptr(prev, next);
        
        if(next != NULL){
            set_pred_ptr(next, prev);
        }
    }
    
    /*Initialize the block to be placed*/
    size = block_size(block);
    
    if((init_block(block, size)) != 0) {
        dbg_printf("Error in init_block\n");
        return;
    }
    
    block_mark(block, 0);   /*Mark block allocated*/
}


/*Combine two blocks, mainly used in coalesce function*/
static block_pointer combine_block(block_pointer first, block_pointer second){
    
    REQUIRES(first != NULL);
    REQUIRES(in_heap(first));
    REQUIRES(second != NULL);
    REQUIRES(in_heap(second));
    
    block_pointer temp;
    size_t first_size, second_size;
    
    first_size = block_size(first);
    second_size = block_size(second);
    
    /*Set the new size to the header and footer of the block*/
    first[0] = first_size + second_size;
    temp = block_footer(first);
    temp[0] = first_size + second_size;
    
    return first;
}


/*
 * malloc
 */
void *malloc(size_t size) {
    
    //mm_checkheap(1);
    
    size_t word_size;
    block_pointer bp, new_alloc;
    
    /*Ignore spurious requests*/
    if(size == 0)
    return NULL;
    
    /*Adjust block size to include overhead and alignment request*/
    if(size > BLOCKSIZE_MIN * WSIZE - DSIZE) {
        word_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    else {
        word_size = BLOCKSIZE_MIN * WSIZE;
    }
    word_size = (word_size / WSIZE);   /*convert byte size to word size*/
    
    /*Search the free list for a fit*/
    if((bp = find_first_fit(word_size)) != NULL) {
        delete_block(bp);
        place(bp, word_size);
        return block_mem(bp);
    }
    
    /*No fit found. Use extend_heap to get more memory*/
    if((new_alloc = extend_heap(MAX(word_size, CHUNKSIZE))) == NULL) {
        dbg_printf("extend_heap error\n");
        return (block_pointer)-1;
    }
    place(new_alloc, word_size);
    
    //mm_checkheap(1);
    
    return block_mem(new_alloc);
}


/*
 * Set alloc to free state and insert to free list
 */
void free(void *ptr) {
    REQUIRES(ptr != NULL);
    REQUIRES(in_heap(ptr));
    
    //mm_checkheap(1);
    
    if(ptr == NULL || !in_heap(ptr)) {
        return ;
    }
    
    block_pointer block = block_header(ptr);
    block_mark(block, 1);
    block = coalesce(block);
    add_to_free_list(block);
    
}

/**Optionally split the free block, and marked as allocated**/
static void place(block_pointer bp, size_t alloc_size) {
    REQUIRES(bp != NULL);
    REQUIRES(in_heap(bp));
    size_t total_size;
    block_pointer temp, next_block;
    
    total_size = block_size(bp);
    
    /*Check the reminder of the free block whether meet min requirement*/
    if(total_size - alloc_size <= BLOCKSIZE_MIN) {
        block_mark(bp, 0);
    }
    else {
        /*Set size to the header and footer of block*/
        bp[0] = alloc_size;
        temp = block_footer(bp);
        temp[0] = alloc_size;
        
        /*Reminder free blocks are split and initialize to a new free list*/
        next_block = block_next(bp);
        if((init_block(next_block, total_size - alloc_size)) != 0) {
            dbg_printf("Error in init_block\n");
            return;
        }
        
        block_mark(bp, 0);  /*Mark as allocated*/
        
        /*Insert this new splited part to the free list*/
        add_to_free_list(next_block);
    }
}



/*
 * Realloc - Naive implementation
 * Compare between old size and new size, if the new size is larger, then we do malloc
 * if the new size is smaller, then we do place.
 */
void *realloc(void *oldptr, size_t size) {
    REQUIRES(oldptr != NULL);
    REQUIRES(in_heap(oldptr));
    
    block_pointer block, newptr;
    size_t word_size, old_size;
    
    /*Adjust requested allocate block size to include overhead and alignment*/
    if(size > BLOCKSIZE_MIN * WSIZE - DSIZE) {
        word_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    else {
        word_size = BLOCKSIZE_MIN * WSIZE;
    }
    word_size = (word_size / WSIZE);   /*convert byte size to word size*/
    
    /*If size = 0 then this is just free, and we return NULL*/
    if (size == 0) {
        free(oldptr);
        return(0);
    }
    
    /*If oldptr = NULL, then this is just malloc*/
    if(oldptr == NULL) {
        return(malloc(size));
    }
    
    /*Use malloc to get new heap space*/
    newptr = malloc(size);
    
    if (newptr == NULL) {
        return NULL;
        
    } else {
        
        block = block_header(oldptr);
        old_size = block_size(block);
        
        /*Compare the size between old and new one*/
        if (old_size < word_size) {
            
            old_size = old_size * WSIZE;
            memcpy(newptr, oldptr, MIN(old_size, size));
            free(oldptr);
            return newptr;
            
        } else {
            
            place(block, word_size);
            return oldptr;
        }
    }
}

/*
 * Reapeat to do malloc and set the memory to zero
 */
void *calloc( size_t nmemb, size_t size )
{
    block_pointer newptr;
    
    /*Check the input size whether meets the requirement of min block size*/
    if(size < BLOCKSIZE_MIN){
        size = BLOCKSIZE_MIN;
    }
    
    newptr = malloc(nmemb * size);
    return newptr;
}

/*Determine which class that the block size belongs to*/
/*Here we simply use power of 2 to classify different class*/
int get_class_no(size_t size){
    if(size < 4)
    return 0;
    if(size < 8)
    return 1;
    if(size < 16)
    return 2;
    if(size < 32)
    return 3;
    if(size < 64)
    return 4;
    if(size < 128)
    return 5;
    if(size < 256)
    return 6;
    if(size < 512)
    return 7;
    if(size < 1024)
    return 8;
    if(size < 2048)
    return 9;
    if(size < 4096)
    return 10;
    
    return 11;
    
}

/*Self-definrf debug function*/

/*
 * checkheap
 */
int mm_checkheap(int verbose) {
    void *bp, *start;
    
    if(verbose) {
        /*Check prologue blocks*/
        if ((block_size(heap_listp) != 2) || block_free(heap_listp))
        printf("Bad prologue header\n");
        
        /*Check epilogue blocks*/
        bp = (block_pointer)((char*)mem_heap_hi() + 1) - 1;
        if ((block_size(bp) != 0) || block_free(bp))
        printf("Bad epilogue header\n");
        
        
        /*Check each block's address alignment and whether header and footer are the same*/
        /*Check each block whether they falls within heap boundary*/
        for (start = heap_listp + 1; block_size(bp) > 0; start = block_next(start)) {
            
            check_in_heap(start);
            checkblock_align(start);
            check_header_footer(start);
            check_coalescing(start);
            check_prev_next_ptr(start);
        }
        
        /*Check free block falls within correct bucket of segregate array*/
        check_seg_list();
        
        return 0;
    }
    
    else {
        return 0;
    }
}

static void check_in_heap(block_pointer bp) {
    
    block_pointer prev_pointer, next_pointer;
    prev_pointer = block_prev(bp);
    next_pointer = block_next(bp);
    
    if (in_heap(bp) != 1)
    printf("Error: block pointer does not fall within heap range\n");
    if (prev_pointer != NULL && in_heap(prev_pointer) != 1)
    printf("Error: block's prev_pointer does not fall within heap range\n");
    if (next_pointer != NULL && in_heap(next_pointer) != 1)
    printf("Error: block's next_pointer does not fall within heap range\n");
}

static void checkblock_align(void *bp) {
    if (aligned(bp) != 1)
    printf("Error: %p is not doubleword aligned\n", bp);
}

static void check_header_footer(block_pointer bp) {
    if (*bp != *block_footer(bp))
    printf("Error: header does not match footer\n");
}

static void check_coalescing(block_pointer bp) {
    block_pointer prev_block;
    prev_block = block_prev(bp);
    if(block_free(prev_block) && block_free(bp)) {
        printf("Error: two consecutive free blocks in the heap\n");
    }
}

static void check_prev_next_ptr(block_pointer bp) {
    block_pointer prev_block;
    prev_block = block_prev(bp);
    if(get_pred_ptr(bp) == prev_block && get_succ_ptr(prev_block) == bp) {
        return;
    } else {
        printf("Error: next/previous pointers are not consistent\n");
    }
}


int inverse_get_class_no(int class) {
    if(class == 0)
    return 4;
    if(class == 1)
    return 8;
    if(class == 2)
    return 16;
    if(class == 3)
    return 32;
    if(class == 4)
    return 64;
    if(class == 5)
    return 128;
    if(class == 6)
    return 256;
    if(class == 7)
    return 512;
    if(class == 8)
    return 1024;
    if(class == 9)
    return 2048;
    if(class == 10)
    return 4096;
    
    return INT_MAX;
}

static void check_seg_list(void) {
    int i, range_max;
    block_pointer free_list_ptr;
    
    for(i = 0; i < CLASS_NUMBER; ++i) {
        free_list_ptr = seg_array[i];
        range_max = inverse_get_class_no(i);
        
        while(free_list_ptr) {
            if(block_size(free_list_ptr) >= (unsigned int) range_max) {
                printf("Error: free block fall within wrong bucket size\n");
            }
            free_list_ptr = get_succ_ptr(free_list_ptr);
        }
    }
}