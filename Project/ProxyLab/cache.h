#include "csapp.h"

#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400


typedef struct cache_elem {
    unsigned int time_stamp;
    size_t size;
    char hostname[MAXLINE];
    int port;
    char uri[MAXLINE];
    unsigned char *data;
    struct cache_elem *next;
} cache_elem;


typedef struct cache_list {
    cache_elem *head;
    size_t total_cache_size;
} cache_list;

/*Function prototypes*/
void initialize_cache();
cache_elem* check_cache_list(cache_list *cache, char *hostname, int *port, char *uri);
void insert_to_cache(cache_list *cache, char *hostname, int *port, char *uri, 
                          unsigned char *data, size_t insert_size);
void eviction(cache_list *cache);
unsigned int update_least_time(cache_list *cache, cache_elem *cache_ptr);

