/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "Oneju",
    /* First member's full name */
    "Noh Wonju",
    /* First member's email address */
    "wonju.noh.24@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define WSIZE 4 /* Word and header/footer size */
#define DSIZE 8 /* Double word size */
#define CHUNKSIZE (1<<12) /* Extned heap by this amount (bytes)*/

#define MAX(x, y) ((x)>(y)?(x):(y))
#define PACK(size, alloc) ((size)|(alloc))

#define GET(p)      (*(unsigned int *)(p))
#define PUT(p,val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) -WSIZE) /* bp = cur, header address*/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp))-DSIZE) /* footer address */

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

static char *heap_listp;
static char *last_bp; /* for next fit */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){
        return -1;
    }
    
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp + (2*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp + (3*WSIZE),PACK(0,1));
    
    heap_listp += (2*WSIZE);
    last_bp = heap_listp; /* last bp 블록 초기값으로 설정 */
    
    /* Extend the empty heap with a free block of CHNKSIZE bytes*/
    if (extend_heap(CHUNKSIZE/WSIZE)==NULL){
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    
    if ((long)(bp = mem_sbrk(size))==-1){
        return NULL;
    }
    
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    
    return coalesce(bp);
}
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* case 1 */
    if (prev_alloc && next_alloc){
        return bp;
    }
    /* case 2 */
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    /* case 3 */
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        
        bp = PREV_BLKP(bp);
    }
    /* case 4 */
    else{
        size += GET_SIZE(FTRP(NEXT_BLKP(bp)))+GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        
        bp = PREV_BLKP(bp);
    }
    last_bp = bp;
    return bp;
}
static void *find_fit(size_t asize)
{
    // Next-fit
    void *bp = last_bp;
    /* 탐색 : last_bp(마지막으로 방문한 블럭) -> Footer */
    for (; GET_SIZE(HDRP(last_bp))>0; last_bp = NEXT_BLKP(last_bp))
    {
        if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp)))){
            return last_bp;
        }
    }
    /* 탐색 : Header -> last_bp */
    for (last_bp = heap_listp; last_bp<bp; last_bp = NEXT_BLKP(last_bp))
    {
        if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp)))){
            return last_bp;
        }
    }
    return NULL;
/*
    // First-fit
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
*/    
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE))
    {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
    
        bp = NEXT_BLKP(bp);
    
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
    last_bp = bp;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    
    char *bp;

    if (size == 0){ 
        return NULL;
    }
    
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp,asize);
        return bp;
    }

    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE))==NULL){
        return NULL;
    }

    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    void *oldptr = ptr;
    newptr = mm_malloc(size);
    if (newptr == NULL){
        return NULL;
    }
    
    size_t copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize){
        copySize = size;
    }
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}