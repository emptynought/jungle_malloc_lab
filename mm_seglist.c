#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "3-1",
    /* First member's full name */
    "empty",
    /* First member's email address */
    "emptynought@kakao.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define SEGLIST

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define MINBLOCK    16
#define LISTSIZE    20
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount (bytes) */     

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define PACK(size, alloc)   ((size) | (alloc))
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp)    ((char *)(bp) - WSIZE)            
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)     

#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))

#define PREDP(bp)    (*(char **)(bp))
#define SUCCP(bp)    (*(char **)(bp + WSIZE))


static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void helloBlock(void *bp);
static void byeBlock(void *bp);
static int search_list(void *bp, size_t size);
static void *find_fit(size_t asize);

void* heap_listp;           /* 힙의 맨 처음 위치를 가리키고 있는 포인터, find_fit을 하는 시작점이 된다*/
void* free_listp;           /* 가용 블록의 시작 위치를 가리키고 있는 포인터 */
void* free_list[LISTSIZE];

// CLEAR
int mm_init(void)
{
    // if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    //     return -1;
    // PUT(heap_listp, NULL);                             /* Alignment padding */
    // PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    // PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    // PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */

    if((heap_listp = mem_sbrk((2*WSIZE) + LISTSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp + (0*WSIZE + LISTSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (1*WSIZE + LISTSIZE), PACK(0, 1));        /* Epilogue header */

    free_listp = NULL;
    
    for(int i = 0; i < LISTSIZE; i++){
        free_list[i] = NULL;
    }

    if (extend_heap(INITCHUNKSIZE) == NULL){
        return -1;
    }

    return 0;
}

// CLEAR
static void *extend_heap(size_t size)
{
    char *bp;
    size_t asize;
    asize = MAX(ALIGN(size) + DSIZE, MINBLOCK);
    if ((long)(bp = mem_sbrk(asize)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(asize, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(asize, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */
    return coalesce(bp);
}


void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */

    char *bp;
    if (size == 0)
        return NULL;

    asize = MAX(ALIGN(size) + DSIZE, MINBLOCK);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL){
        return NULL;
    }
        
    place(bp, asize);

    return bp;
}

// CLEAR
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (MINBLOCK)) {
        byeBlock(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        coalesce(bp);
    }
    else {
        byeBlock(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// CLEAR
void mm_free(void *bp)
{
    if(!bp) return;
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    coalesce(bp);
}


static void *coalesce(void *bp)
{
    
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc && next_alloc){                   /* Case 1 */
    }
    /* 다음 블록이 가용 블록이면 다음 블록과 합친다 */
    else if (prev_alloc && !next_alloc) {           /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        byeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));      
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {           /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        byeBlock(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));            
    }

    /* 이전 블록과 다음 블록이 가용블록이면 두 블록 모두와 합친다 */
    else {                                              /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        byeBlock(PREV_BLKP(bp)); 
        byeBlock(NEXT_BLKP(bp)); 
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));               
        PUT(FTRP(bp), PACK(size, 0));          
    }
    helloBlock(bp);
    return bp;
}

// CREAR
void *mm_realloc(void *ptr, size_t size)
{
    if (size == 0){
        mm_free(ptr);
        return 0;
    }
    
    if (ptr == NULL){
        return mm_malloc(size);
    }

    void *newptr = mm_malloc(size);

    if (newptr == NULL){
        return 0;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize){
        oldsize = size;
    }
    memcpy(newptr, ptr, oldsize);
    mm_free(ptr);
    return newptr;
}

static void helloBlock(void *bp){
    size_t asize = GET_SIZE(HDRP(bp));
    #ifdef SEGLIST
    int i = search_list(bp, asize);
    #else
    int i = 0;
    #endif
    if (free_list[i] == NULL){
        free_list[i] = bp;
        PREDP(bp) = NULL;
        SUCCP(bp) = NULL;
    }
    else{
        SUCCP(bp) = free_list[i];
        PREDP(free_list[i]) = bp;
        PREDP(bp) = NULL;
        free_list[i] = bp;
    }
}

static void byeBlock(void *bp){
    size_t asize = GET_SIZE(HDRP(bp));
    #ifdef SEGLIST
    int i = search_list(bp, asize);
    #else
    int i = 0;
    #endif
    if(PREDP(bp) == NULL){
        free_list[i] = SUCCP(bp);
    }
    else{
        SUCCP(PREDP(bp)) = SUCCP(bp);
    }
    if(SUCCP(bp) != NULL)
        PREDP(SUCCP(bp)) = PREDP(bp);
}

static int search_list(void *bp, size_t asize){
    int i = 0;
    while((i < LISTSIZE - 1) && (asize > 1)){
        asize >>= 1;
        i += 1;
    }
    return i;
}

static void *find_fit(size_t asize){
    void *bp;
    #ifdef SEGLIST
    for(int i = search_list(bp, asize); i < LISTSIZE; i++){
        if(free_list[i] != NULL){
            for (bp = free_list[i]; bp != NULL; bp = SUCCP(bp)){
                if (asize <= GET_SIZE(HDRP(bp))) {
                    return bp;
                }
            }
        }
    }    

    #else
    int i = 0;
    for (bp = free_list[i]; bp != NULL; bp = SUCCP(bp)){
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    #endif


    return NULL; /* No fit */
}
// test