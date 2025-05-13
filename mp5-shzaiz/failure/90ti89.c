/******************************************************************************
 * 
 * Malloc lab header
 * 
 * Author: Guangwei Zhang
 * Email:  gzhang31@hawk.iit.edu
 * AID:    A20221001980
 * Date:   12/12/2024
 * 
 * By signing above, I pledge on my honor that I neither gave nor received any
 * unauthorized assistance on the code contained in this repository.
 * 
 *****************************************************************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// #define DEBUG
#ifdef DEBUG
#include <assert.h>
#endif
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include "mm.h"
#include "memlib.h"

#ifndef DEBUG
#define assert(x) 
#endif

// __attribute__((always_inline))
// inline int __dummy(bool x){return 0;}

void delete_node(void *);
void insert_node(void *, size_t);
void *extend_heap(size_t);
void *coalesce(void *, size_t *, size_t *);
void print_chain(int);
void print_blk(void *);
void print_heap();
void *split(void *, size_t);

// Debug macros
#define DBGI(...) //do{printf("(debug malloc)");printf(__VA_ARGS__);printf("\n");}while(0);
#define DBGR(...) //do{printf("(debug realloc)");printf(__VA_ARGS__);printf("\n");}while(0);
#define PANIC(...) do{assert(__VA_ARGS__);}while(0);

#define ERR(...) do{printf("(error)");printf(__VA_ARGS__);printf("\n");}while(0);

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define GET(pointer) (*(unsigned int*)(pointer))
#define PUT(pointer, val) ((*(unsigned int*)(pointer) = (val)))
#define PACK(size, hasalloc) ((size) | (hasalloc))
#define max(a, b) ((a)>(b)?(a):(b))
/**
 * =============================\
 *                                length is WSIZE 
 * =============================/
 *  PREV FOOTER(Size info|used)
 * ============================= 
 *    HEADER(size info|used)    <- ptr
 * ============================= 
 *         PAYLOAD              <- bp <-ptr(if free)--|   ====================
 * =============================                      |         NEXT PTR
 *          FOOTER                                    |   ====================
 * =============================                      |        PREV PTR
 *                                                    |   ====================
 *                                                    |           ...
 */


#define MAX_REQ_SIZE (1<<30)

#define BOOLIFY(x) (!(!(x)))

// get size of the current address pointer
#define GSZ(ptr) (GET(ptr) & (~0x7))
// get whether or not allocated for the current address pointer
#define GALLOC(ptr) (GET(ptr) & 0x1)
// get header pointer of the pointer(at start of payload)
#define GHDRP(bp) ((char *)(bp) - WSIZE)
// get footer pointer of the current pointer(at start of payload)
#define GFTRP(bp) ((char *)(bp) - WSIZE + GSZ(GHDRP(bp))    - WSIZE)
///                \header of this blk/  \size offset before end/

// at header, compute next block's payload pointer
#define NXT_BLKP(bp) (((char *)(bp))+(GSZ(((char *)(bp)-WSIZE))))
// at header, prev block's payload pointer
#define PRV_BLKP(bp) (((char *)(bp))-(GSZ(((char *)(bp)-WSIZE-WSIZE))))

#define BRUTE_TAGGING

typedef struct flist_node_t{
  struct flist_node_t *prev, *next;
}__attribute__((packed)) lnode;

#define INITCHUNKSZ ( 1<< 6)
#define EXTEND_CHUNK_SZ (1 << 12)


#define CURR_ALLOCATED 1


// Word size
#define WSIZE 4 
// Double word size
#define DWSIZE 8



#define NR_SLIST 30
char **seg_list;
char *rheap_start;

int mm_init(void)
{
  // lnode should occupy 2 of pointer type
  assert(sizeof(lnode) == 2*8);


  DBGI("Initilizing...");
  seg_list = mem_heap_lo();

  // Allocate block sizes
  /**
   * --------- 
   * seg_list[NR_SLIST] <- sbrk
   * ...
   * seg_list[1]
   * seg_list[0]
   * --------- <- start 
   */
  int i;
  for(i=0; i<NR_SLIST; i++){
    void *dummy = mem_sbrk(DWSIZE);
    if(dummy == (void *)-1){
      return -1;
    }
    seg_list[i] = NULL;
  }
  rheap_start = mem_sbrk(2*DWSIZE);
  if(rheap_start == (void *)-1){
    return -1;
  }  

  // place PROLOGUE and EPILOGUE after sbrk
  PUT(rheap_start, 0);
  PUT(rheap_start+WSIZE, PACK(DWSIZE, CURR_ALLOCATED)); // header of prologue
  PUT(rheap_start+2*WSIZE, PACK(DWSIZE, CURR_ALLOCATED)); // header of prologue
  PUT(rheap_start+3*WSIZE, PACK(0, CURR_ALLOCATED)); // header of prologue
  rheap_start = rheap_start + 2*WSIZE;
  if(extend_heap(INITCHUNKSZ/WSIZE) == NULL){
    return -1;
  }
  #ifdef DEBUG
  print_heap();
  #endif
  return 0;
}

void print_heap(){
  printf(" ==== START HEAPCHK ======\n");
  char *bp = rheap_start;
  printf("Heap from %p: \n", (void *)bp);
  assert(GSZ(GHDRP(bp))==DWSIZE && GALLOC(GHDRP(bp))==true);

  bool pre_free = false, cur_free = false;
  for(; GSZ(GHDRP(bp)) > 0; bp = NXT_BLKP(bp)){
    print_blk(bp);
    assert((!(pre_free && cur_free))); // should not have 2 frees in a row
    pre_free = cur_free, cur_free = !GALLOC(GHDRP(bp));
  }
  pre_free++, cur_free++; // to make Wall happy

  int i=0;
  for(; i<NR_SLIST; i++){
    printf("[%d] ", i); print_chain(i);
  }

  printf(" ==== END HEAPCHK ======\n");
}

void *extend_heap(size_t words){
  DBGI("Expanding heap by %lu words...", words);
  size_t toalloc = (words%2 == 0) ? (words)*WSIZE : (words+1)*WSIZE;
  DBGI("expanding %lu bytes for real", toalloc);
  // brk pointer: get where brk points to. 
  char *brkp = mem_sbrk(toalloc);
  if(brkp == NULL) return NULL;

  PUT(GHDRP(brkp), PACK(toalloc, false));        assert(GSZ(GHDRP(brkp)) == toalloc);
  PUT(GFTRP(brkp), PACK(toalloc, false));        assert(GSZ(GFTRP(brkp)) == toalloc);
  PUT(GHDRP(NXT_BLKP(brkp)), PACK(0, true)); // epilogue header

  return coalesce(brkp, NULL, NULL);

}

void *coalesce(void *bp, size_t *prv_free, size_t *nxt_free){
  bool preserve_empty = !(BOOLIFY(prv_free) | BOOLIFY(nxt_free));
  DBGI("Coaleasing %p..., %s with empty slot", bp, preserve_empty ? "" : "not yet");
  void *prev_footer = GFTRP(PRV_BLKP(bp));
  void  *next_header = GHDRP(NXT_BLKP(bp));
  /** Coalesce in two ways
 * +-------------+     
 * | prv_header  |     
 * +-------------+     
 * |             |     
 * | prv_payload |     
 * +-------------+     
 * | prv_footer  |     
 * +-------------+     
 * | cur_header  |     
 * +-------------+     
 * |             |<-ptr
 * | just freed  |     
 * | or to be ext|
 * | -ended blok |     
 * +-------------+     
 * | cur_footer  |     
 * +-------------+     
 * | nxt_header  |     
 * +-------------+     
 * | nxt_payload |     
 * |             |     
 * +-------------+     
 * | nxt_footer  |     
 * +-------------+     
 */

  size_t sz = GSZ(GHDRP(bp));
  bool prev_alloc = GALLOC(prev_footer), next_alloc = GALLOC(next_header);
  if(prev_alloc && next_alloc){
    DBGI("Not coaleacing, prev(footer=%p) and next(header=%p) is occupied.", prev_footer, next_header);
    if(prv_free) *prv_free = false;
    if(nxt_free) *nxt_free = false;
  }else if(prev_alloc && !next_alloc){
    DBGI("Coaleacing PREV_ALLOC, prev(footer=%p) and next(header=%p) is occupied.", prev_footer, next_header);
    sz += GSZ(next_header);
    delete_node(NXT_BLKP(bp));
    PUT(GHDRP(bp), PACK(sz, !preserve_empty)); // size info has changed now! 
    PUT(GFTRP(bp), PACK(sz, !preserve_empty)); // actually the next block's footer
    if(prv_free) *prv_free = 0;
    if(nxt_free) *nxt_free=GSZ(next_header);
  }else if(!prev_alloc && next_alloc){
    DBGI("Coaleacing NEXT_ALLOC, prev(footer=%p) and next(header=%p) is occupied.", prev_footer, next_header);
    sz += GSZ(prev_footer);
    delete_node(PRV_BLKP(bp));
    PUT(GFTRP(bp), PACK(sz, !preserve_empty));
    PUT(GHDRP(PRV_BLKP(bp)), PACK(sz, !preserve_empty));
    bp = PRV_BLKP(bp);
    if(prv_free) *prv_free=GSZ(prev_footer);
    if(nxt_free) *nxt_free=0;
  }else if(!prev_alloc && !next_alloc){
    DBGI("Coaleacing BOTH_ALLOC, prev(footer=%p) and next(header=%p) is occupied.", prev_footer, next_header);
    sz += GSZ(prev_footer) + GSZ(next_header);
    delete_node(NXT_BLKP(bp));
    delete_node(PRV_BLKP(bp));
    PUT(GHDRP(PRV_BLKP(bp)), PACK(sz, !preserve_empty));
    PUT(GFTRP(NXT_BLKP(bp)), PACK(sz, !preserve_empty));
    bp = PRV_BLKP(bp);
    if(prv_free) *prv_free = GSZ(prev_footer);
    if(nxt_free) *nxt_free = GSZ(next_header);
  }
  if(preserve_empty) insert_node(bp, sz);
  return bp;
}

void coalease_down(void *bp, bool preserve_empty){
    // void *prev_footer = GFTRP(PRV_BLKP(bp));
    void  *next_header = GHDRP(NXT_BLKP(bp));
    size_t sz = GSZ(GHDRP(bp));
    sz += GSZ(next_header);
    delete_node(NXT_BLKP(bp));
    PUT(GHDRP(bp), PACK(sz, !preserve_empty)); // size info has changed now! 
    PUT(GFTRP(bp), PACK(sz, !preserve_empty)); // actually the next block's footer
}

void get_coalease_info(void *bp, size_t *prv_free, size_t *nxt_free){
  void  *prev_footer = GFTRP(PRV_BLKP(bp));
  void  *next_header = GHDRP(NXT_BLKP(bp));
  if(prv_free) *prv_free = GSZ(prev_footer);
  if(nxt_free) *nxt_free = GSZ(next_header);
}

void print_blk(void *bp){
  assert((uintptr_t)bp % 8 == 0);
  long int hsz = GSZ(GHDRP(bp)), halloc = GALLOC(GHDRP(bp));
  long int fsz = GSZ(GFTRP(bp)), falloc = GALLOC(GFTRP(bp));
  if(hsz == 0){DBGI("%p: END OF BLOCK", bp);}
  else{
    printf("%p: header<%p,%ld, %c>; footer<%p, %ld, %c>\n", bp, (void *)GHDRP(bp),hsz, halloc?'Y':'N', (void *)GFTRP(bp),fsz, falloc?'Y':'N');
    assert(hsz == fsz);
    assert(halloc == falloc);
  }
}

void insert_node(void *bp, size_t size){
  int chno = 0;
  {
    size_t i;
    for(i=size; (i>1) && (chno < NR_SLIST-1); chno++, i>>=1);
  }
  lnode *head = (lnode *)seg_list[chno];
  lnode *pre = NULL;
  lnode *i = head;
  // first node >= input size
  while((i != NULL) && (size > GSZ(GHDRP(i)))){
    pre = i;
    i = i->next;
  }
  DBGI("Inserting to chain %d with %p size: %lu", chno, bp, size);
  lnode *curr = (lnode *)bp;
  if(i == NULL && pre == NULL){ // empty
    DBGI("adding to empty list");
    seg_list[chno] = bp;
    curr->next = curr->prev = NULL;
  }else if(i == NULL && pre != NULL){ // last
    curr->prev = pre;
    curr->next = NULL;
    pre->next = curr;
  }else if(i != NULL && pre == NULL){ // at the head
    seg_list[chno] = bp;
    i->prev = curr;
    curr->next = i;
    curr->prev = NULL;
  }else{ // between
    curr->prev = pre;
    curr->next = i;
    i->prev = curr;
    pre->next = curr;
  }
}

void delete_node(void *bp){
  size_t sz = GSZ(GHDRP(bp)); 
  int chno = 0;
  {
    size_t i;
    for(i=sz; (i>1) && (chno < NR_SLIST-1); chno++, i>>=1);
  }
  DBGI("Deleting from %d with size %lu, addr %p", chno, sz, bp);
  lnode *curr = (lnode *)bp;
  if(curr->prev == NULL){
    seg_list[chno] = (char *)curr->next;
    if(curr->next) {
      curr->next->prev = NULL;
    }
  }else if(curr->next == NULL){
    curr->prev->next = NULL;
  }else{
    curr->prev->next = curr->next;
    curr->next->prev = curr->prev;
  }
}



void print_chain(int chno){
  lnode *head = (lnode *)seg_list[chno];
  lnode *tmp = head; 
  while(tmp != NULL){
    printf("%p[%u] -> ", tmp, GSZ(GHDRP((char *)tmp)));
    // Invariant for DLList
    if(tmp->prev) assert(tmp->prev->next == tmp);
    if(tmp->next) assert(tmp->next->prev == tmp);
    tmp = tmp->next;
  }
  printf("NIL\n");

}


void *split(void *bp, size_t split_sz){
  size_t nowsize = GSZ(GHDRP(bp));
  DBGI("Splitting %p with size %lu out of %lu", bp, split_sz, nowsize);
  delete_node(bp);
  DBGI("Deleted %p", bp);
  assert(nowsize >= split_sz);
  if((nowsize - split_sz) <= (2 * DWSIZE)){
    // no split
    PUT(GHDRP(bp), PACK(nowsize, true));
    PUT(GFTRP(bp), PACK(nowsize, true));
    return bp;
  }else if(split_sz >= 4*(sizeof(lnode) + DWSIZE)){ // enough room for prev and next free list
    size_t remaining = nowsize - split_sz;
    PUT(GHDRP(bp), PACK(remaining, false));
    PUT(GFTRP(bp), PACK(remaining, false));
    PUT(GHDRP(NXT_BLKP(bp)), PACK(split_sz, true));
    PUT(GFTRP(NXT_BLKP(bp)), PACK(split_sz, true));
    insert_node(bp, remaining);
    return NXT_BLKP(bp);
  }else{
    PUT(GHDRP(bp), PACK(split_sz, true));
    PUT(GFTRP(bp), PACK(split_sz, true));
    PUT(GHDRP(NXT_BLKP(bp)), PACK(nowsize - split_sz, false));
    PUT(GFTRP(NXT_BLKP(bp)), PACK(nowsize - split_sz, false));
    insert_node(NXT_BLKP(bp), nowsize - split_sz);
    return bp;
  }
  assert(0);
  return NULL;
}

#define REALSZ(sz) ((sz) < DWSIZE ? (2*DWSIZE) : (ALIGN((sz) + DWSIZE)))
void *mm_malloc(size_t size)
{
  DBGI("Allocating %lu mems.", size);
  size_t adj_size = REALSZ(size);
  char *bp = NULL;
  if(size == 0 || size > MAX_REQ_SIZE) return NULL;

  int chno=0; size_t tmp=adj_size;
  for(; chno<NR_SLIST; chno++, tmp >>=1){
    if((tmp > 1 && chno < NR_SLIST-1) || seg_list[chno] == NULL) continue; 
    lnode *i = (lnode *)seg_list[chno];
    for(; i!=NULL; i = i->next){
      if(GSZ(GHDRP(i))<adj_size) continue;
      bp = (char *)i;
      break;
    }
    if(bp) break;
  }


  if(bp == NULL){
    DBGI("Ouch, I'm running out of space!");
    size_t ext = max(adj_size, EXTEND_CHUNK_SZ);
    bp = extend_heap(ext/WSIZE);
    if(bp == NULL) return NULL;
  }
  bp = split(bp, adj_size);
  #ifdef DEBUG
  print_heap();
  #endif
  return bp;

}

void realloc_split(void *bp, size_t sz){
  #ifdef BRUTE_TAGGING
  size_t thissz = GSZ(GHDRP(bp));
  PUT(GHDRP(bp), PACK(thissz, true));
  PUT(GFTRP(bp), PACK(thissz, true));
  #endif
}

void mm_free(void *ptr)
{
  // size_t *header = ptr - SIZE_T_SIZE;
  // *header &= ~1L;
  size_t sz = GSZ(GHDRP(ptr));
  PUT(GHDRP(ptr), PACK(sz, 0));
  PUT(GFTRP(ptr), PACK(sz, 0));
  coalesce(ptr, NULL, NULL);
  #ifdef DEBUG
  print_heap();
  #endif
}

void *mm_realloc(void *ptr, size_t size)
{
  #ifdef DEBUG
  print_heap();
  #endif
  if(ptr == NULL) return mm_malloc(size);
  if(size == 0) {mm_free(ptr); return NULL;}

  void *oldptr = ptr;
  void *newptr;
  
  size_t newsz=REALSZ(size), oldsz=GSZ(GHDRP(oldptr));
  DBGR("About to realloc %lu -> %lu", oldsz, newsz);
  if(oldsz < newsz){
    
    size_t next_free_sz = 0, prev_free_sz = 0;
    get_coalease_info(oldptr, &prev_free_sz, &next_free_sz);
    
    DBGR("Maybe grow in place? next_free_sz=%lu, grow = %lu", next_free_sz, (newsz-oldsz+16));

    if(next_free_sz > (newsz - oldsz + 16)){
      // realloc here 
      DBGR("I can grow now!");
      // realloc_split(oldptr, size);
      coalease_down(oldptr, false);
      #ifdef DEBUG
      print_heap();
      #endif
      return oldptr;
    }
    
    char *bp = coalesce(oldptr, &prev_free_sz, &next_free_sz);

    if(prev_free_sz ){
      DBGR("I must have copied this!! I can copy now!");
      memcpy(bp, ptr, size);
      realloc_split(bp, size);
      return bp;
    }else{
      // bad luck!
      DBGR("I cannot grow now, reallocating size %lu", size);
      newptr = mm_malloc(size);
      DBGR("Allocated at %p", newptr);
      memcpy(newptr, ptr, size);
      DBGR("Copied!");
      mm_free(oldptr);
      return newptr;
    }
  }else{
    realloc_split(oldptr, newsz);
    return oldptr;
  }
  assert(0); // should not reach here!
  return NULL;
}
