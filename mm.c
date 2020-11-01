


/*
 Doubly Linked Explicit List implementation of malloc, free, and realloc.
 Uses LIFO policy to free blocks. Allocates blocks using a first fit policy.
 This allows the allocator to inspect most recently freed blocks first so that freeing blocks
 can be performed in O(1) time.

 Code Framework for Malloc Lab was taken from impicit list shown in Computer Systems: A Programmer's Perspective Chapter 9.9

 32 bit system:
 WSIZE = 4
 DSIZE = 8
 */




/*
FREE BLOCK STRUCTURE:
 ___________________________________
|                                   |
|           HEADER                  |
|___________________________________|
|                                   |
|              NEXT                 |
|___________________________________|
|                                   |   
|                PREV               |
|___________________________________|
|                                   |
|             FOOTER                |
|___________________________________|

ALLOCATED BLOCK STRUCTURE:

 ___________________________________
|                                   |
|           HEADER                  |
|___________________________________|
|                                   |
|             Payload               |
|___________________________________|
|                                   |   
|              Payload              |
|___________________________________|
|                                   |
|             FOOTER                |
|___________________________________|

*/
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Lake",
    /* First member's full name */
    "James Guo",
    /* First member's email address */
    "jamesg6197@g.ucla.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


/* Basic constants and macros */

#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))
/* Pack a size and allocated bit into a word */

#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */

#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) 
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp,compute address of next and previous blocks */

#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp,compute address of its header and footer */

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_FREE_BLKP(bp) (*(char **)(bp + WSIZE))
#define PREV_FREE_BLKP(bp) (*(char**)(bp))

#define SET_NEXT_BLKP(bp, np) (NEXT_FREE_BLKP(bp) = np)
#define SET_PREV_BLKP(bp, np) (PREV_FREE_BLKP(bp) = np)


static char* heap_listp;
static char* freelistp;
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static void *extend_heap(size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/* Explicit List Managers */
static void add_to_beginning(void *bp);
static void remove_free_node(void *bp);

/* Heap Checkers */
static void printblock(void *ptr);
static int checkblock(void *ptr);
int mm_check(void);

/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == NULL)  /* Create empty heap with prologue, padding, and epilogue blocks */
    {
	   return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); 
    heap_listp += (2*WSIZE); //points to prologue footer
    freelistp = heap_listp + DSIZE; // points to the first free block
    if (extend_heap(16) == NULL) /* Extend heap length */
    {
	   return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block using an aligned PAYLOAD size.
 Returns NULL if failure
 */
void *mm_malloc(size_t size)
{
    int asize;
    /* If size is 0, dont do anything */
    if (size == 0)
    {
	   return NULL;
    }
    asize = MAX(ALIGN(size) + DSIZE, 4*WSIZE);
    void* bp;
    /* Find and Place Block */
    if ((bp = find_fit(asize)) != NULL) 
    {
	   place(bp, asize);
	   return bp;
    }
    size_t extendsize = MAX(asize, CHUNKSIZE);
    /* No fit found. Get more memory and place the block. If no more memory, return NULL.*/
    if ((bp = extend_heap(extendsize)) == NULL)
    {
	   return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Frees a block, Immediate Coalescing
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    if (ptr == NULL) return;
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);

}

/*
 * mm_realloc - Changes the size of a given block
 if block is null, acts as malloc
 if size is 0, acts as free
 if current block size is the same or as larger than the total block size of the desired size, just return the current block
 if we are expanding the block, look to see if we can do it in-place first by allocating part of the next block or search
 for another block to place the new block
 If successful, return address of new block, else return NULL
 */
void *mm_realloc(void *ptr, size_t size)
{

    void* newptr;
    size_t oldptrsize = GET_SIZE(HDRP(ptr));
    size_t newptrsize = size + DSIZE;
    if (!ptr) /* ptr == NULL */
    {
	   return mm_malloc(size);
    }
    if (size == 0) /* if size == 0, then free block */
    {
        mm_free(ptr);
	   return NULL;   
    }
    if (oldptrsize >= newptrsize) /*Do nothing if size < size of the current block */
    {
        return ptr;
    }
    /* if we are expanding and have an open block after the current one we can check if the merged block fits
    the desired size */
    else if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) 
    {
        size_t totalsize = (oldptrsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))));
        if (totalsize >= newptrsize)
        {

            remove_free_node(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(totalsize, 1));
            PUT(FTRP(ptr), PACK(totalsize, 1));
            return ptr;
        }
    }
    /* if not look for another spot in the heap to resize the block */
    newptr = mm_malloc(size);
    if (!newptr)
    {
        return NULL;
    }
    place(newptr, newptrsize);
    memcpy(newptr, ptr, oldptrsize); // Copy bytes
    mm_free(ptr);
    return newptr;

}
    
/*
Extends the heap by "size" bytes
*/
static void *extend_heap(size_t size)
{
    char *bp;
  	size_t asize;

  /* ALIGN size */
  	asize = ALIGN(size);
    if (asize < 16) asize = 16; // MINIMUM
    /* if no more memory, return NULL */
  	if ((long)(bp = mem_sbrk(asize)) == - 1 )
  	{ 
    	return NULL;
  	}
  /* Initialize free block header/footer and the epilogue header */
  	PUT(HDRP(bp), PACK(asize, 0));         /* free block header */
  	PUT(FTRP(bp), PACK(asize, 0));         /* free block footer */
  	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
  /* coalesce bp with next and previous blocks */
  	return coalesce(bp);
}
/* Merges adjacent free blocks*/
static void *coalesce(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_block;
    if (PREV_BLKP(bp) == bp) /*If the size of PREV_BLKP is zero, we set it */
    {
    	prev_block = 1;
    }
    else
    {
    	prev_block = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    }
    size_t next_block = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    if (prev_block && !next_block) /* Case 2: FREE NEXT BUT ALLOC PREV*/
    {
	   size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
       remove_free_node(NEXT_BLKP(bp));
	   PUT(HDRP(bp), PACK(size, 0));
       PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_block && next_block) /* Case 3: FREE PREV BUT ALLOC NEXT*/
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_free_node(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_block && !next_block) /* Case 4: FREE PREV AND FREE NEXT*/
    {
	   size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
       remove_free_node(PREV_BLKP(bp));
       remove_free_node(NEXT_BLKP(bp));
	   bp = PREV_BLKP(bp);
       PUT(HDRP(bp), PACK(size, 0));
       PUT(FTRP(bp), PACK(size, 0));
    }
    add_to_beginning(bp); /* Case 1: BOTH NEXT AND FREE ALLOCATED*/
    return bp;
}
/* ADDING A BLOCK USING LIFO POLICY */
static void add_to_beginning(void* bp)
{
    SET_NEXT_BLKP(bp, freelistp); 
    SET_PREV_BLKP(freelistp, bp); 
    SET_PREV_BLKP(bp, NULL); 
    freelistp = bp;

}
/* REMOVING A BLOCK USING LIFO POLICY */
static void remove_free_node(void* bp)
{

    if (PREV_FREE_BLKP(bp) == NULL)
    {
    	freelistp = NEXT_FREE_BLKP(bp);
    
    }
    else
    {
    	SET_NEXT_BLKP(PREV_FREE_BLKP(bp), NEXT_FREE_BLKP(bp));
        
    }
    SET_PREV_BLKP(NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp));
}




/* first fit search combined with LIFO Policy*/
static void *find_fit(size_t asize)
{
    void *bp;

    /* first fit search */
    for (bp = freelistp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREE_BLKP(bp)) /* while next block is free */
    {
	   if ((size_t)GET_SIZE(HDRP(bp)) >= asize)
       {
	       return bp;
       }
	}
    
    return NULL;
}
/* Place a block */
static void place(void *bp, size_t asize)
{
    size_t fblocksize = GET_SIZE(HDRP(bp));
    if ((fblocksize - asize) >= (2 * DSIZE)) /*If the free block we allocate is at least 4 words bigger than asize, we split */
    {
	   PUT(HDRP(bp), PACK(asize, 1));
	   PUT(FTRP(bp), PACK(asize, 1));
       remove_free_node(bp);
	   PUT(HDRP(NEXT_BLKP(bp)), PACK(fblocksize - asize, 0));
	   PUT(FTRP(NEXT_BLKP(bp)), PACK(fblocksize - asize, 0));
       coalesce(NEXT_BLKP(bp));


    }
    else /*No split case */
    {
        PUT(HDRP(bp), PACK(fblocksize, 1));
        PUT(FTRP(bp), PACK(fblocksize, 1));
        remove_free_node(bp);
    }
}

// printblock function format taken from Textbook
static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}
// check block function taken from Textbook
static int checkblock(void *bp) 
{
    if ((size_t)bp % 8)
    {
        printf("Error: %p is not doubleword aligned\n", bp); // checks alignment
        return 0;
    }

    else if (GET(HDRP(bp)) != GET(FTRP(bp)))
    {
        printf("Error: header does not match footer\n"); // checks that header == footer
        return 0;
    }
    if (!GET_ALLOC(HDRP(bp))){
    	if (!(GET_ALLOC(NEXT_BLKP(bp)) && (GET_ALLOC(PREV_BLKP(bp)))))
    	{
    		printf("Error: Not all blocks are coalesced property\n"); // checks that all free blocks adjacent to each other are coalesced
    		return 0;
    	}
	}
    return 1;

}

/* 
 * mm_check - check the heap's consistency and debug
 */
int mm_check(void) 
{
    char *bp = heap_listp;

    printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) // CHECK PROLOGUE BLOCK
        printf("Bad prologue header\n");

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) 
    {   // LOOP THROUGH THE HEAP
            printblock(bp);
        if (!checkblock(bp)) return 0;
    }
    printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) // CHECK EPILOGUE BLOCK
    {
        printf("Bad epilogue header\n");
        return 0;
    }
    char* fp;

    for (fp =freelistp; GET_ALLOC(HDRP(fp)) == 0; fp = NEXT_FREE_BLKP(fp))
    {           // LOOP THROUGH THE EXPLICIT FREE LIST
    	if (!((NEXT_FREE_BLKP(fp) == NULL) || (PREV_FREE_BLKP(fp) == NULL)))
    		if ((NEXT_FREE_BLKP(PREV_FREE_BLKP(fp))) !=  PREV_FREE_BLKP(NEXT_FREE_BLKP(fp))) //Check free block pointer consistency
    		{
    			printf("Next and Prev points do not match");
    			return 0;
    		}

    }
    return 1;
}















