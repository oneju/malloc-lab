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

#define PRED_FREEP(bp) (*(void **)(bp))           /* Predeccessor for explicit */
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE))   /* Successor for explicit */

static char *heap_listp;
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static char *free_listp;
static void put_free_block(void *bp);      /* 가용리스트 앞에 가용블럭을 추가 */
static void remove_free_block(void *bp);   /* 가용블럭 하나 삭제 */


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1){
        return -1;
    }
    
    PUT(heap_listp, 0);                             /* padding */
    PUT(heap_listp + (1*WSIZE),PACK(DSIZE*2,1));    /* prolog : succ, pred가 추가됐기때문에 길이 추가 */
    PUT(heap_listp + (2*WSIZE),NULL);               /* successor */
    PUT(heap_listp + (3*WSIZE),NULL);               /* predeccessor */
    PUT(heap_listp + (4*WSIZE),PACK(DSIZE*2,1));    /* prolog footer */
    PUT(heap_listp + (5*WSIZE),PACK(0,1));          /* epilogue header */
    
    free_listp = heap_listp + DSIZE;                /* prolog를 가리킨다 */
    
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
    
    if ((long)(bp = mem_sbrk(size))==(void*)-1){
        return NULL;
    }
    
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    
    return coalesce(bp);
}
static void *coalesce(void *bp)
{   /* 현재 bp 는 가용리스트에 없기 떄문에 무조건 한번은 put을 해줘야한다 */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
    size_t size = GET_SIZE(HDRP(bp));                   
    /* Case 1 앞, 뒤 모두 할당되어 있을 때 */
    /* Case 2 앞은 할당되어 있고, 뒤는 가용블록일 때 */
    if (prev_alloc && !next_alloc)
    {
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 3 앞은 가용블록이고, 뒤는 할당되어 있을 때 */
    else if (!prev_alloc && next_alloc)
    {
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 4 앞, 뒤 모두 가용블록일 때 */
    else if (!prev_alloc && !next_alloc)
    {
        remove_free_block(NEXT_BLKP(bp));
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    put_free_block(bp);
    return bp;
}
static void *find_fit(size_t asize)
{
    // First-fit
    void *bp;
    for (bp = free_listp; GET_ALLOC(HDRP(bp))!=1; bp = SUCC_FREEP(bp))
    {
        /* bp가 할당이 되지 않았을 때 loop */
        if (asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    /* for Explicit list */
    remove_free_block(bp); // free -> alloc
    if((csize - asize) >= (2*DSIZE))
    {
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp),PACK(asize,1));
    
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        /* for Explicit list */
        put_free_block(bp); // 
    }
    else{
        PUT(HDRP(bp),PACK(csize,1));
        PUT(FTRP(bp),PACK(csize,1));
    }
}

static void put_free_block(void *bp)
{
    PRED_FREEP(bp) = NULL;          /* 현재 bp의 prev는 값이 없고 */
    SUCC_FREEP(bp) = free_listp;    /* 현재 bp의 next를 이전 값으로 저장한다 */          
    PRED_FREEP(free_listp) = bp;    /* 이전 bp의 prev를 현재 bp와 연결 */
    free_listp = bp;                /* 마지막 point bp로 업데이트 */
}
static void remove_free_block(void *bp)
{
    /* bp의 predeccessor과 successor를 연결시킨다 */
    if (bp == free_listp) 
    {
        PRED_FREEP(SUCC_FREEP(bp)) = NULL;  
        free_listp = SUCC_FREEP(bp);        
    }
    else
    {
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
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
    if (size <= 0){
        mm_free(ptr);
        return 0;
    }
    if (ptr == NULL){
        return mm_malloc(size);
    }
    newptr = mm_malloc(size);
    if (newptr == NULL){
        return NULL;
    }
    
    size_t copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize){
        copySize = size;
    }
    
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
