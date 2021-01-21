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

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size_t)(size) + (ALIGNMENT-1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


// ------------------- Edit Start ------------------- //
/* find_fit strategy */
#define NEXT_FIT

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
/* size와 alloc 정보를 묶는다 */
#define PACK(size, alloc)   ((size) | (alloc))
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
/* Data를 가리키는 포인터에서 한 칸 전으로 가면 Header */
#define HDRP(bp)    ((char *)(bp) - WSIZE)            
/* Data를 가리키는 포인터에서 Header에 있는 size 만큼 가면 다음 블록의 데이터 위치
 * 그 곳에서 두 칸 전으로 가면 자신의 Footer 위치 */
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)     

/* Given block ptr bp, compute address of next and previous blocks */
/* Data를 가리키는 포인터에서 한 칸 뒤에 있는 헤더에서 size를 찾고
 * 그만큼 더하면 다음 블록의 데이터 위치 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
/* Data를 가리키는 포인터에서 두 칸 뒤에 있는 이전 블록의 Footer를 통해서 
 * 이전 블록의 크기를 확인하고 그 크기만큼 뒤로 이동하면 이전 블록의 Data 영역 */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 포인터가 가리키는 위치에 주어진 공간을 할당할 수 있는지 확인 */
#define CAN_ALLOC(p, size) !GET_ALLOC(HDRP(p)) && (size <= GET_SIZE(HDRP(p)))

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */

// ------------------- Edit Start ------------------- //

void* heap_listp;           /* 힙의 맨 처음 위치를 가리키고 있는 포인터, find_fit을 하는 시작점이 된다*/
#ifdef NEXT_FIT
void* next_fitp;           /* Next_fit 사용 시 탐색 시작 위치를 지정할 포인터 */
#endif 
int mm_init(void)
{
    /* Create the initial empty heap */
    /* 4 워드 크기 만큼을 추가한다, Alignment padding, Prologue header, Prologue footer, Epilogue header가 들어갈 공간 확보 */

    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                             /* Alignment padding */
    /* Data 부분 없이 header와 footer만 존재하는 DSIZE(WSIZE + WSIZE) 크기의 Prologue 블록 생성*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    /* find_fit으로 데이터를 찾을 때 끝을 확인하기 위해 header 만으로 이루어진 Epilogue 블록 생성
     * Epilogue 블록 이후에 접근할 필요가 없기 때문에 실제 크기는 4지만 끝을 표시하기 위한 size는 0을 입력 */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    /* heap_listp 의 위치는 Prologue header와 footer 사이인 footer의 주소를 가리킨다 */
    heap_listp += (2*WSIZE);
    #ifdef NEXT_FIT
    /* NEXT_FIT 탐색에 사용하기 위한 next_fitp 를 heap_listp로 초기화 */
    next_fitp = heap_listp;
    #endif
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    /* 힙이 처음 생성된 상태에서는 가용한 블록이 없기 때문에
     * 힙에 공간을 추가하는 최소 단위로 정한 CHUNKSIZE 만큼 공간을 할당 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* words : 힙에 추가할 워드의 개수 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    /* 더블 워드 할당 기준을 지키기 위해서 추가 해야하는 워드가 홀수면
     * 워드 1개를 더 추가해서 더블 워드의 배수로 조정*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* mem_sbrk를 통해 break를 뒤로 옮겨 힙 공간을 size만큼 키운다 */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    /* 확장한 크기는 가용 블록 header와 footer를 추가하여 가용 블록으로 만들어준다 */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header, bp는 데이터를 가리키고, HDRP는 한 칸 앞*/ 
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    /* 크기를 확장하면서 덮어쓰여진 epilogue header는 추가된 공간 뒤에 만들어준다 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

    /* Coalesce if the previous block was free */
    /* 힙 영역이 확장하면서 확장 이전 블록이 가용 영역이었다면 합쳐준다 */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{

    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    /* 공간 할당을 요청한 크기가 0이면 할당을 수행할 필요가 없으므로 NULL을 리턴 */
    if (size == 0)
        return NULL;

    asize = MAX(ALIGN(size) + DSIZE, 2*DSIZE);

    /* Search the free list for a fit */
    /* find_fit을 통해서 조정한 공간이 들어갈 블록이 있는지 확인해서 있으면 공간의 포인터 반환*/
    if ((bp = find_fit(asize)) != NULL) {
        /* 공간이 있으면 그 위치에 asize 만큼의 공간 할당 후 포인터 반환*/
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    /* 만약 적절한 공간을 찾지 못했다면 힙 추가 기본 단위인 CHUNKSIZE와 필요한 크기인 asize를 확인해서
     * 더 큰 값을 확장할 크기로 정한다 */
    extendsize = MAX(asize, CHUNKSIZE);
    /* extendsize 만큼 extend_heap 으로 힙 공간을 추가하고 포인터를 반환 */
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    /* 반환된 포인터 위치에 asize 만큼의 크기를 할당 */
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize){
    /* Next-fit search */
#ifdef NEXT_FIT
    /* next_fitp 가 가리키고 있는 지점을 oldptr로 기억 */
    void *oldptr = next_fitp;
    /* next_fitp는 마지막으로 free 된 공간을 가리키고 있고 그곳에서 부터 탐색 시작 
     * SIZE가 0보다 클 때까지(epilogue block을 만나기 전까지) 다음 블록을 탐색 */    
    for(; GET_SIZE(HDRP(next_fitp)) > 0; next_fitp = NEXT_BLKP(next_fitp))
        /* 다음 블록이 할당되어 있지 않고 할당하려는 크기가 가용 블록의 크기보다 작으면*/
        if (CAN_ALLOC(next_fitp, asize))
            /* 찾은 위치를 반환 */
	        return next_fitp;
    
    for(next_fitp = heap_listp; next_fitp < oldptr; next_fitp = NEXT_BLKP(next_fitp))
        if (CAN_ALLOC(next_fitp, asize))
	        return next_fitp;

#else
    /* First-fit search */
    void *bp;
    /* 시작점을 heap_listp 부터 시작해서 크기가 0(epilogue block)이 아닐 때까지 다음 블록으로 넘어가면서
     * 할당 가능한 공간을 찾고 찾으면 그 공간의 포인터를 return 한다 */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (CAN_ALLOC(bp, asize)) {
            return bp;
        }
    }
#endif
    /* 적절한 공간이 없으면 NULL을 리턴한다 */
    return NULL; /* No fit */
}

static void place(void *bp, size_t asize){
    /* 할당가능한 공간 전체 크기 */
    size_t csize = GET_SIZE(HDRP(bp));


    /* 할당가능한 공간의 전체 크기와 할당하려는 데이터 크기의 차가 16보다 크면
     * 데이터 크기가 최소인 경우 블록 할당이 가능하므로 공간을 분리한다 */
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    /* 차이가 16보다 더블 워드 할당을 만족하기 위해 모든 공간을 사용해야 하므로 공간을 모두 채운다 */
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // add hwp
    // if(!bp) return;
    /* 반환 요청한 공간의 크기를 확인 */
    size_t size = GET_SIZE(HDRP(bp));
    /* header와 footer에 가용 공간 표시를 한다 */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    
    /* 가용 공간을 만들어주고 앞 뒤 공간을 확인해서 합칠 수 있으면 합친다 */
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    // 이전 블록 할당 여부, 다음 블록 할당 여부, 현재 블록의 크기 확인 */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* 앞, 뒤 모두 할당되어 있으면 아무 동작 없이 포인터 반환 */
    if(prev_alloc && next_alloc){                   /* Case 1 */
        return bp;
    }

    /* 다음 블록이 가용 블록이면 다음 블록과 합친다 */
    else if (prev_alloc && !next_alloc) {           /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));      
        PUT(FTRP(bp), PACK(size, 0));           
    }

    /* 이전 블록이 가용 블록이면 이전 블록과 합친다 */
    else if (!prev_alloc && next_alloc) {           /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0));                  
    }

    /* 이전 블록과 다음 블록이 가용블록이면 두 블록 모두와 합친다 */
    else {                                          /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0));       
    }
#ifdef NEXT_FIT
    if (next_fitp > bp && next_fitp < NEXT_BLKP(bp))
        next_fitp = bp;
#endif
    return bp;
}



void *mm_realloc(void *ptr, size_t size)
{
    /* 재할당을 요청한 크기가 0이면 공간을 비워달라는 의미이므로 그냥 free하고 종료한다 */
    if (size == 0){
        mm_free(ptr);
        return 0;
    }
    
    /* 값이 NULL 인 포인터로 요청을 한다면 melloc과 동일한 동작을 한다 */
    if (ptr == NULL){
        return mm_malloc(size);
    }

    /* 새로운 공간을 할당 받아서 그 공간의 포인터를 반환받는다 */
    void *newptr = mm_malloc(size);

    /* 반환 받은 포인터가 NULL 이면 힙 전체 범위에서
     * 할당 가능한 공간이 없다는 이야기이므로 0을 반환한다 */
    if (newptr == NULL){
        return 0;
    }

    /* 할당 가능한 공간이 있으면
     * 현재 공간의 크기를 확인하고*/
    size_t oldsize = GET_SIZE(HDRP(ptr));
    /* 현재 데이터 크기가 옮겨갈 공간의 크기보다 크다면
     * 옮길 수 있는 크기로 조정한다 */
    if (size < oldsize){
        oldsize = size;
    }
    /* 새로운 위치에 이전 위치에 있던 oldsize 만큼 덮어쓴다 */
    memcpy(newptr, ptr, oldsize);
    /* 현재 공간은 반환하고 새로운 위치 포인터를 반환한다 */
    mm_free(ptr);
    return newptr;
}
