/******************************************************************************
 *
 * Cache lab header
 *
 * Author: Guangwei Zhang
 * Email:  gzhang31@hawk.iit.edu
 * AID:    A25027114
 * Date:   2024.11.22 
 *
 * By signing above, I pledge on my honor that I neither gave nor received any
 * unauthorized assistance on the code contained in this repository.
 *
 *****************************************************************************/

#include <getopt.h>
#include <assert.h>
#include <stdbool.h>
#include <inttypes.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include "cachelab.h"

/* --> macros for getopt */
#define setarg(letter, var, value) case letter: var = value; break;
#define UINT unsigned int
#define ULL unsigned long long
#define DEBUG(...) do{printf("[DEBUG!] "); printf(__VA_ARGS__); printf("\n");}while(0)

#define DBGINPUT(...)  // DEBUG(__VA_ARGS__)
#define DBGCACHE(...)  // DEBUG(__VA_ARGS__)
/* <-- macros for getopt */


/* --> Command line arguments */
bool help=false,verbose=false;

// set index bit (Number of set index bits (S = 2^s is the number of sets))
int sib, Setsz; 

// Associativity (number of lines per set)
int Enline;
// Number of block bits (B = 2^b is the block size)
int blkb, Blksz;
// Name of the valgrind trace to replay
char *tracefl;
/* <-- Command line arguments */

typedef uint64_t memaddr_t; // memory address is int64.

typedef struct cache_line{
    bool valid; // valid bit per line 
    memaddr_t tag; //t tag bits per line, we only use top t.
    // B does not count too much. 
    ULL lru; // least recent used counter
} cache_line_t;

typedef cache_line_t* cache_set_t; // A set of cache
typedef cache_set_t* cache_ker_t; // The whole cache

typedef struct cache_t{
    cache_ker_t data;
    int S,E,B;
}cache_t;


cache_t cache;
memaddr_t mask; // use this to make sure we are only using prev k bits.

void cache_init(cache_t *cache, int Setsz, int Enline, int Blksz){
    mask = Setsz - 1; 
    cache->S = Setsz;
    cache->E = Enline;
    cache->B = Blksz;
    cache->data = (cache_set_t *) malloc(sizeof(cache_set_t) * Setsz);
    int i,j;
    for(i=0; i<Setsz; i++){
        cache->data[i] = (cache_line_t *)malloc(sizeof(cache_line_t) * Enline);
        for(j=0; j<Enline; j++){
            cache->data[i][j].lru = cache->data[i][j].tag = cache->data[i][j].valid = 0;
        }
    }
}

void cache_print(cache_t *cache) {
    int s = log2(Setsz);    // Set index bits
    int b = log2(Blksz);    // Block offset bits
    int t = 64 - s - b;      // Tag bits

    printf("Cache Organization (S = %d, E = %d, B = %d)\n", Setsz, Enline, Blksz);
    printf("Set Index Bits (s)  = %d\n", s);
    printf("Block Offset Bits (b) = %d\n", b);
    printf("Tag Bits (t)        = %d\n", t);
    printf("------------------------------------\n");

    printf("Cache Content:\n");
    printf("Set | Line | Valid | Tag (in Hex)  | LRU\n");
    printf("---------------------------------------------\n");
    int i,j;
    for (i = 0; i < cache->S; i++) {
        for (j = 0; j < cache->E; j++) {
            // Extract tag by masking the upper bits (the tag portion of the address)
            memaddr_t tag = cache->data[i][j].tag;
            // Format the tag as hex for clarity (assuming memaddr_t is a 64-bit address)
            printf("%3d | %4d |   %d  | 0x%10"PRIx64" | %lld\n", 
                i, j, 
                cache->data[i][j].valid, 
                tag, 
                cache->data[i][j].lru);
        }
    }
    printf("\n");
}

void cache_free(cache_t *cache) {
    int i;
    for(i=0; i<cache->S; i++){
        free(cache->data[i]);
    }
    free(cache->data);
}

// Simulation of the cache starts here

#define MASK(x) ((x) & (mask))
#define ASS_HIT 0x001
#define ASS_MISS 0x010
#define ASS_EVIC 0x100
int nr_hit=0, nr_miss=0, nr_evic=0;
ULL count_lru = 0;

int get_data(cache_t *cache, memaddr_t addr){
    DBGCACHE("getting %"PRIx64 ":", addr);
    // 1. Which cell am I going to? 
    memaddr_t b = log2(cache->B);
    memaddr_t s = log2(cache->S); 
    memaddr_t setidx = MASK(addr>>b);
    memaddr_t tag = addr>>(b+s);

    
    cache_set_t cset = cache->data[setidx];
    int i;
    for(i=0; i<cache->E; i++){
        DBGCACHE("  %d has tag %"PRIx64, i, tag);
        if(cset[i].valid == 0) continue;
        if(!(cset[i].tag == tag)) continue;
        DBGCACHE("  HIT now"); 
        cset[i].lru = count_lru++;
        // 2. Hit! Horray! No more work to be done.
        nr_hit++;
        return ASS_HIT;
    }

    // 3. Unfortunately, we missed it...
    nr_miss++;
    int ret = ASS_MISS;
    int evict_line = -1;
    ULL evict_lru = INT64_MAX;
    

    for(i=0; i<cache->E; i++){
        ULL this_lru = cset[i].lru;
        if(evict_lru > this_lru) {
            evict_line = i;
            evict_lru = this_lru;
        }
    }
    assert(evict_line != -1);
    if(cset[evict_line].valid){
        // 4. Oh, some line is being removed.
        nr_evic++;
        ret |= ASS_EVIC;
    }

    cset[evict_line].lru = count_lru++;
    cset[evict_line].tag = tag;
    DBGCACHE("I have tag %"PRIx64, tag);
    cset[evict_line].valid = true;
    return ret;
}


void replay_file(FILE *file, cache_t *cache){
    char op;
    memaddr_t addr;
    int sz;

    
    while(fscanf(file, " %c %" PRIx64 ",%d\n", &op, &addr, &sz) == 3){
        int status = 0;
        switch(op){
            case 'M': status |= get_data(cache, addr); // Modify = Read + Write, 2 getdatas
            case 'L': case 'S': status |= get_data(cache, addr);
            default: break;
        }

        if(verbose){
            printf("%c %"PRIx64",%d ", op, addr, sz);
            if((status & ASS_MISS) != 0){
                printf("miss ");
            }
            if((status & ASS_EVIC) != 0){
                printf("eviction ");
            }
            if((status & ASS_HIT) != 0){
                printf("hit ");
            }
            printf("\n");
        }
    }

    

    fclose(file);
}


void get_help(char **argv, int retcode){
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(retcode);
}

// unused on purpose only a test
void test_cache_line_behavior(){
    {
        int i;
        for(i=0; i<50; i++){
            get_data(&cache, i);
        }
    }
    get_data(&cache, 0xDEADBEEF);
    
    cache_print(&cache);
}

int main(int argc, char **argv){
    char op=1;
    while((op = getopt(argc, argv, "s:E:b:t:vh"))!=-1){
        switch(op){
            setarg('s', sib, atoi(optarg));
            setarg('E', Enline, atoi(optarg));
            setarg('b', blkb, atoi(optarg));
            setarg('t', tracefl, optarg);
            setarg('v', verbose, true);
            setarg('h', help, true);
            default: get_help(argv,1);
        }
    }
    
    if(help) get_help(argv, 0);

    DBGINPUT("S=%d,E=%d,B=%d,tf=%s", sib, Enline, blkb, tracefl);
    if(tracefl == NULL || sib == 0 || Enline == 0 || blkb == 0){
        DBGINPUT("S=%d,E=%d,B=%d,tf=%s", sib, Enline, blkb, tracefl);
        printf("%s: Missing required command line argument\n", argv[0]);
        get_help(argv, 1);
    }

    Setsz = (UINT) pow(2, sib);
    Blksz = (UINT) pow(2, blkb);

    DBGINPUT("S=%d,E=%d,B=%d,tf=%s", Setsz, Enline, Blksz, tracefl);

    cache_init(&cache, Setsz, Enline, Blksz);
    
    FILE *trace = fopen(tracefl, "r");
    if(trace == NULL) {
        perror("fopen");
        exit(1);
    }

    replay_file(trace, &cache);
    
    // cache_print(&cache);
    
    cache_free(&cache);

    printSummary(nr_hit, nr_miss, nr_evic);
    return 0;
}
