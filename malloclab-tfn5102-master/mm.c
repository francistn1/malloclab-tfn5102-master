/*
 * mm.c
 *
 * Name: Timothy Nicholl
 *
 * The following implements code from pg.857, section 9.9, from the third edition of Computer Systems Programmer's perspective by Randal E. Bryant and 
 * David R. O'Hallaron, both from Carnegie Mellon University. Many of the functions perform the same as intended and described in the book as well as the readme 
 * included in this program. However, the program and it's functions have been modified to work with segregated free lists as opposed to the implicit free list 
 * implementation in the book. The best way I figured how to implement this function was to create a free list struct containing the prev and next blocks of a free list
 * This was done to avoid the use of pointer arthimetic as attempting to use that caused alot of issues for me. Escentially, this could is treating the free lists as 
 * linked lists. I did have to define some of my own helper functions as well as the book's to aid me in this venture. Two functions I should describe here are
 * find_fit and mm_checkheap. find_fit was orginally implemented to find free blocks by searching the entire heap, it has been modified several times throughout this
 * venture to search for exclusivly free blocks, for explicit free list implementation, then implementated to peform searches for segregated free lists. The current 
 * implementation uses a form of best k fit implementation which works to some degree but It could be better. The next function is mm_checkheap, this function was intended
 * to be implemented for heap consistency and has been modified to do as such. Originally it simply printed out the heap boundaries when called, this would go on for
 * every trace file in this program and has been commented out for preformance reasons and redundancy. It now performs various checks for the free list as described in 
 * the read me. The most difficult check was the last one: basically we needed to make sure it was coalsced and to do this I figured out that by comparing the address of the header 
 * of the current block (HDRP(bp)) with the address of the footer of the previous block (FTRP(prev)). It checks if the distance between these two addresses is equal to the size of 
 * the header and footer combined and if the condition is true it returns false. This is because when coalscesing free blocks, the address of block that has been coalsced 
 * shouldn't exist anymore so if subtracting them equals DSIZE something went wrong. However, the most useful check was checking weather or not the free list was empty or not
 * because while working with TA's I kept getting segfaults when implementing this function, when Youssef suggested that I create a check to make sure it wasn't empty I was presented
 * with countless errors stating that the free list was empty. This allowed to recreate my free list structure and implement it to the way it is now.
 * 
 *
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16

/* Basic constants and macro's */
#define WSIZE 8             /* Word and header/footer size (bytes) */
#define DSIZE 16            /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /*. Extend heap by this amount (bytes) */
#define NUM_LISTS 10       // Number of segregated free lists

// PROTOTYPES
void *extend_heap(size_t words);
void *find_fit(size_t size);
void *coalesce(void *bp);
void place(void *bp, size_t asize);
void remove_freeblock(void *bp);
void insert_freeblock(void *bp);

// Private variables represeneting the heap and free list within the heap
// static char *heap_listp = 0;  /* Points to the start of the heap intinally, this one will be allocated*/
// static char *heap_basep = 0; /*points to start of heap, will not be allocated. Used a as control*/
// static char *free_listp = 0;  /* Points to the first free block */
// void* global_heap_listp = mm_heap_lo;

struct FreeBlock
{
    struct FreeBlock *next;
    struct FreeBlock *prev;
};

// struct FreeBlock* free_listp; THIS IS ONE FREE LIST

struct FreeBlock *free_lists[NUM_LISTS];

size_t MAX(size_t x, size_t y)
{
    return x > y ? x : y;
}

/* Pack a size and allocated bit into a word */
size_t PACK(size_t size, size_t alloc)
{
    return size | alloc;
}

/* HELPER FUNTIONS */
/* Read and write a word at address p */
size_t GET(void *p)
{
    return *(size_t *)p;
}

void PUT(void *p, size_t val)
{
    *(size_t *)p = val;
}

/* Read the size and allocated fields from address p */
size_t GET_SIZE(void *p)
{
    return GET(p) & ~0x7;
    ;
}

size_t GET_ALLOC(void *p)
{
    return GET(p) & 0x1;
}

/* Given block ptr bp, compute address of its header and footer */
void *HDRP(void *bp)
{
    return (char *)bp - WSIZE;
}

void *FTRP(void *bp)
{
    return (char *)bp + GET_SIZE(HDRP(bp)) - DSIZE;
}

/* Given block ptr bp, compute address of next and previous blocks */
void *NEXT_BLKP(void *bp)
{
    return (char *)bp + GET_SIZE(((char *)bp - WSIZE));
}

void *PREV_BLKP(void *bp)
{
    return (char *)bp - GET_SIZE((char *)bp - DSIZE);
}

/*Helper functions to look for Free list*/
char *NEXT_FREE(void *bp)
{
    return (char *)((bp)) + DSIZE;
}

char *PREV_FREE(void *bp)
{
    return ((char *)(bp));
    // Return pointer of previous free
}



// New helper function that gives the index that you should go to in the free list array using block size

/*
int find_size(size_t block_size)
{
    int index = 0;
    while (block_size > 1)
    {
        block_size >>=1; //right shift to divide by 2
        The reason we divide by 2 is because we are looking for the number of times we can divide the block size by 2 until it becomes 1.
        index++;
        if(block_size < 64)
        {
            return 0;
        }
    }

    return index;
}
*/

int find_size(size_t block_size)
{
    if (block_size <= 32)
        return 0;
    else if (block_size <= 64)
        return 1;
    else if (block_size <= 128)
        return 2;
    else if (block_size <= 256)
        return 3;
    else if (block_size <= 512)
        return 4;
    else if (block_size <= 1024)
        return 5;
    else if (block_size <= 2048)
        return 6;
    else if (block_size <= 4096)
        return 7;
    else if (block_size <= 8192)
        return 8;

    return 9; // For block sizes larger than 8192, assign the last index
}

void remove_freeblock(void *bp)
{
    struct FreeBlock *block = (struct FreeBlock *)bp;
    int block_size = GET_SIZE(HDRP(bp));
    int index = find_size(block_size);
    // struct FreeBlock* free_list = free_lists[index];
    //  Case: Empty free list
    if (free_lists[index] == NULL)
        return;

    // Case: Block is the only one in the list
    if (block->next == NULL && block->prev == NULL)
    {
        free_lists[index] = NULL;
        return;
    }

    // Case: Block is the first one in the list
    if (block->prev == NULL)
    {
        free_lists[index] = block->next;
        if (block->next != NULL)
            block->next->prev = NULL;
    }
    else
    {
        // Case: Block is in the middle or at the end of the list
        //*(char**)NEXT_FREE(PREV_FREE(bp)) = *(char**)NEXT_FREE(bp);
        if (block->next != NULL)
            block->next->prev = block->prev;

        block->prev->next = block->next;
    }
}

void insert_freeblock(void *bp)
{
    // Set the next and prev pointers of the current block
    // int block_size = DSIZE; //minimum block size
    struct FreeBlock *block = (struct FreeBlock *)bp;
    int block_size = GET_SIZE(HDRP(block));
    int index = find_size(block_size);
    // struct FreeBlock* block_list = free_lists[index];
    block->next = free_lists[index];
    block->prev = NULL;

    // Update the prev pointer of the next block if it exists
    if (free_lists[index] != NULL)
    {
        free_lists[index]->prev = block;
    }

    // Update the free list pointer to the current block
    free_lists[index] = block;
}

// rounds up to the nearest multiple of ALIGNMENT
static size_t align(size_t x)
{
    return ALIGNMENT * ((x + ALIGNMENT - 1) / ALIGNMENT);
}

void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    void *coalesce_ptr;
    // mm_checkheap(133);
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE + DSIZE : words * WSIZE + DSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    /* Initialize free block header/foot and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    // printf("Moved epilogue here %p \n", HDRP(NEXT_BLKP(bp))); /*Add print statments when moving epilogue*/

    /* Coalesce if the previous block was free */
    coalesce_ptr = coalesce(bp);
    // mm_checkheap(154);
    return coalesce_ptr;
}

/* In case 1, both adjacent blocks are allocated and thus no coalescing is possible.
So the status of the current block is simply changed from allocated to free.

In case 2, the current block is merged with the next block. The header of the current block
and the footer of the next block are updated with the combined sizes of the current
and next blocks.

In case 3, the previous block is merged with the current block. The header of the previous block
and the footer of the current block are updated with the combined sizes of the two blocks.

In case 4, all three blocks are merged to form a single free block, with the header of the previous block,
and the footer of the next block updated with the combined sizes of tbe three blocks. In each case,
the coalescing is performed in constant time. */

/*Need to remove free blocks when merging, need to remove an add*/
/*Get explicit free list then turn it into a segregrated free list*/
/*Coalescing happens when we free a block and we need to know if the previous and next block are also
free. If so we so we combine them. The reason we need to free them because they need to be added to a free list.
However, it's possible that after freeing the current block, there still a chance that the previous and next blocks were already free. That
means the next block is in a free list but it shouldn't exist because it should be a part of a free list. Which is why we must remove this
indivdual block*/

void *coalesce(void *bp)
{
    // free(bp);
    //mm_checkheap(__LINE__);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    if (PREV_BLKP(bp) == bp)
    {
        prev_alloc = 1;
    }
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // void* prev_free = PREV_FREE(bp);
    // void* next_free = NEXT_FREE(bp);

    // mm_checkheap(172);

    if (prev_alloc && next_alloc)
    { /* Case 1 */
        insert_freeblock(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        remove_freeblock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_freeblock(bp);
    }
    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        remove_freeblock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_freeblock(bp);
    }
    else
    { /* Case 4 */
        remove_freeblock(PREV_BLKP(bp));
        remove_freeblock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        // PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        insert_freeblock(bp);
    }
    // mm_checkheap(__LINE__);
    //  Insert the coalesced block at the front of the free list

    // Insert into header, treat as a linked list
    // Insert the coalesced block into the free list if it's within the heap boundaries

    // Return the coalesced block
    return bp;
}
/*
    pg.884 "There is nothing very tricky here. But the solution requires you to understand
how the rest of outr simple implicit-list allocator works and how to manipulate
and traverse blocks"
*/

/*Find Free blocks*/
// void* find_free

void *find_fit(size_t asize)
{
    // mm_checkheap(__LINE__);
    // void *local_heap_listp = mm_heap_lo();   // Points to the start of the heap
    // void *local_heap_endp = mm_heap_hi();    // Points to the end of the heap (including epilogue)

    // First-fit search
    // void *bp = (char *)local_heap_listp + DSIZE;  // Start from the first block after the prologue
    // void *bp; //= free_listp;// Need to start at the first free block avaliable
    struct FreeBlock *block;
    int index = find_size(asize);
    int k = 9; // Number of blocks to consider I sppose

    struct FreeBlock *best_blocks[k];
    int best_count = 0;

    // Iterate over the blocks within the heap, checks blocks one by one
    // 1. Should check for only free blocks. Explicit free lists
    // 2. How else can we cut corners?

    for (int i = index; i < NUM_LISTS; i++)
    {
        struct FreeBlock *list = free_lists[i];
        for (block = list; block != NULL; block = block->next)
        {
            size_t block_size = GET_SIZE(HDRP(block));
            if (!GET_ALLOC(HDRP(block)) && (asize <= block_size))
            {
                best_blocks[best_count] = block;
                best_count++;

                // If we have found enough best-fit blocks, select the smallest one
                if (best_count == k)
                {
                    struct FreeBlock *best_fit = best_blocks[0];
                    int best_fit_index = 0;
                    for (int j = 0; j < k; j++)
                    {
                        if (GET_SIZE(HDRP(best_blocks[j])) < GET_SIZE(HDRP(best_fit)))
                        {
                            best_fit = best_blocks[j];
                            best_fit_index = j;
                        }
                    }

                    remove_freeblock(best_fit); // Remove the selected best-fit block
                    // Move the last block in the array to fill the gap
                    best_blocks[best_fit_index] = best_blocks[best_count - 1];
                    return best_fit;
                }
            }
            // bp = (char *)bp + block_size;
            // bp = NEXT_FREE(bp);
        }
    }

    // If we have found enough best-fit blocks, select the smallest one
    if (best_count > 0)
    {
        struct FreeBlock *best_fit = best_blocks[0];
        int best_fit_index = 0;
        for (int j = 0; j < best_count; j++)
        {
            if (GET_SIZE(HDRP(best_blocks[j])) < GET_SIZE(HDRP(best_fit)))
            {
                best_fit = best_blocks[j];
                best_fit_index = j;
            }
        }

        remove_freeblock(best_fit); // Remove the selected best-fit block
        // Move the last block in the array to fill the gap
        best_blocks[best_fit_index] = best_blocks[best_count - 1];
        return best_fit;
    }

    return NULL; // No fit
}

/*
If the remainder of the block after splitting would be greater than or equal to the minimum block
size, then we go ahead and split the block. The only tricky part here
is to realize that you need to place the new allocated block before
moving to the next block.
*/
void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    remove_freeblock(bp);

    if ((csize - asize) >= (2 * DSIZE))
    {
        // Split the free block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
        /*ensure that the explicit free list remains up-to-date and reflects the current state of the heap.*/

        // Insert the remaining block into the explicit free list
        // insert_freeblock(bp);
    }
    else
    {
        // Allocate the entire free block without splitting
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));

        // Remove the allocated block from the explicit free list
        remove_freeblock(bp);
    }
}

/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{
    mm_checkheap(__LINE__);
    for (int i = 0; i < NUM_LISTS; i++)
    {
        free_lists[i] = NULL;
    }
    // mm_checkheap(257);
    /* Create the initial empty heap */
    if (mem_sbrk(4 * WSIZE) == (void *)-1)
    {
        return false;
    }
    /*Might need to change to global*/
    void *local_heap_listp = mm_heap_lo();               /* Call mm_heap_lo as a function */
    PUT(local_heap_listp, 0);                            /* Alignment padding */
    PUT(local_heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue Header */
    PUT(local_heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue Footer */
    PUT(local_heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue Header */
    local_heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return false;
    }

    return true;
    // mm_checkheap(__LINE__);
}

/*
 * malloc
 */
void *malloc(size_t size)
{
    // mm_checkheap(__LINE__);
    size_t asize = align(size + DSIZE); // Adjusted block size
    void *bp = find_fit(asize);

    if (bp != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // No suitable free block found, extend the heap
    size_t extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize / WSIZE);
    if (bp == NULL)
        return NULL;

    // free(bp);
    place(bp, asize);
    // mm_checkheap(__LINE__);
    return bp;
}

/*
 * free
Frees the requested block represented by a pointer
 */
void free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size)
{
    // void* bp;
    // char *next = HDRP(NEXT_BLKP(bp));
    //  If ptr is NULL, it's equivalent to calling malloc(size)
    if (oldptr == NULL)
    {
        return malloc(size);
    }

    // If size is 0, it's equivalent to calling free(ptr) and returning NULL
    if (size == 0)
    {
        free(oldptr);
        return NULL;
    }

    // Retrieve the size of the old block
    size_t oldsize = GET_SIZE(HDRP(oldptr)) - DSIZE;

    // If the old block is already large enough, return the same pointer
    if (oldsize >= size)
    {
        return oldptr;
    }

    // Allocate a new block of the requested size
    void *newptr = malloc(size);
    if (newptr == NULL)
    {
        // Failed to allocate a new block
        return NULL;
    }

    // Copy the contents from the old block to the new block
    size_t copy_size = (oldsize < size) ? oldsize : size;
    memcpy(newptr, oldptr, copy_size);

    // Free the old block
    free(oldptr);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void *calloc(size_t nmemb, size_t size)
{
    void *ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr)
    {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void *p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void *p)
{
    size_t ip = (size_t)p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 * You call the function via mm_checkheap(__LINE__)
 * The line number can be used to print the line number of the calling
 * function where there was an invalid heap.
 */
bool mm_checkheap(int line_number)
{

    // Check for other potential issues
    // ... (perform necessary checks and print any errors or warnings)

#ifdef DEBUG

    // if()
    // dbg_printf("Invalid heap state at line %d\n", line_number);
    // dbg_assert(GET_ALLOC(HDRP(block_ptr)) != GET_ALLOC(FTRP(block_ptr)));
    void *heap_lo = mm_heap_lo();
    //void *heap_hi = mm_heap_hi();
    //void *bp;
    struct FreeBlock *Free_Block;

    // void* block_ptr = heap_lo;
    //  Write code to check heap invariants here
    //  Check heap boundaries
    /*
    printf("Heap boundaries: %p - %p\n", heap_lo, heap_hi);

    if (heap_hi <= heap_lo)
    {
        printf("Invalid heap boundaries\n");
        return false;
    }
    */

    // Check heap consistency
    // ... (perform necessary checks and print any errors or warnings)

    // Check block headers and footers
    void *prologue_block = heap_lo + DSIZE; // Skip over the padding
    if (GET_SIZE(HDRP(prologue_block)) != DSIZE || !GET_ALLOC(HDRP(prologue_block)) || GET_SIZE(FTRP(prologue_block)) != DSIZE ||
        !GET_ALLOC(FTRP(prologue_block)))
    {
        printf("Invalid prologue block\n");
        return false;
    }

    /*It checks if the size stored in the header of the epilogue block is zero.
    Since the epilogue block should not have any allocated or free space, its size should be zero.
     also checks if the allocation status stored in the header of the epilogue block is not set (indicating it is not allocated).
     The epilogue block should not be marked as allocated.*/

    /*
    void* epilogue_block = heap_hi - WSIZE; // Epilogue block just before the heap boundary
    printf("Check for epilogue block %p \n", HDRP(epilogue_block));
    if (GET_SIZE(HDRP(epilogue_block)) != 0) {
        printf("Invalid epilogue block\n");
        return false;
        }

    else if(!GET_ALLOC(HDRP(epilogue_block)))
    {
        printf("epilogue marked as allocated\n");
        return false;
    }
    */

    /*Check for free blocks*/
    if (free_lists == NULL)
    {
        printf("Free list is empty");
    }
    else
    {
        for (int i = 0; i < NUM_LISTS; i++)
        {
            struct FreeBlock *list = free_lists[i];
            for (Free_Block = list; Free_Block != NULL; Free_Block = Free_Block->next)
            {
                if ((void*)Free_Block < mem_heap_lo() || (void*)Free_Block > mem_heap_hi()) /*Do the pointers in the free list point to valid free blocks?*/
                {
                    /*Perform heap check boundaries*/
                    printf("Error: block %p outisde of heap", Free_Block);
                    return false;
                }
                else if (GET_ALLOC(HDRP(Free_Block))) /*Is every block in the free list marked as free?*/
                {
                    /*Make sure it's zero ie free*/
                    printf("Error: block %p in free list but marked as allocated", Free_Block);
                    return false;
                }
                else if (Free_Block->prev != NULL && HDRP(Free_Block) - FTRP(Free_Block) == DSIZE) /*Are there any contiguous free blocks that somehow escaped coalescing?*/
                {
                    /*Checks if blocks have been coalseced*/
                    printf("Error: block %p missed coalescing", Free_Block);
                    return false;
                }
            }
        }
    }

#endif // DEBUG
    return true;
}