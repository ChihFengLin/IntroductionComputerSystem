/*
 * Name: Chih-Feng Lin
         Chi-Heng Wu
 * Andrew ID: chihfenl
              chihengw

 *
 * cache.c - we use singly linked list to implement caches and
 *           apply the concept of reader-writer problem to solve
 *           cache memory synchronization issue.
 */

#include "cache.h"

/*Global variables*/
int readcnt;
unsigned int counter;
sem_t mutex, w;

void initialize_cache()
{
    readcnt = 0;
    counter = 0;
    Sem_init(&mutex, 0, 1);
    Sem_init(&w, 0, 1);
}

/*
 * Read the cache list and search whether there exists the same tag cache
 * If found, return the cache pointer. Otherwise, return NULL.
 */
cache_elem* check_cache_list(cache_list *cache, char *hostname, int *port, char *uri)
{
    P(&mutex);
    readcnt++;
    if(readcnt == 1) { //First reader in
        P(&w);
    }
    V(&mutex);

    /*Critical section for reader satrts*/
    cache_elem *cache_ptr = cache->head;
    counter++;
    while(cache_ptr) {
        if(!strcmp(cache_ptr->hostname, hostname) && (cache_ptr->port == *port) &&
                !strcmp(cache_ptr->uri, uri)) {
            cache_ptr->time_stamp = counter;
            break;
        }
        cache_ptr = cache_ptr->next;
    }
    /*Critical section for reader ends*/

    P(&mutex);
    readcnt--;
    if(readcnt == 0) {  //Last reader out
        V(&w);
    }
    V(&mutex);

    return cache_ptr;
}


void insert_to_cache(cache_list *cache, char *hostname, int *port, char *uri, 
                                unsigned char *data , size_t insert_size)
{
    P(&w);

    /*Critical section for writer satrts*/

    /*Create the new cahce element*/
    cache_elem *new_cache = (cache_elem*)Calloc(1, sizeof(cache_elem));
    strcpy(new_cache->hostname, hostname);
    new_cache->port = *port;
    strcpy(new_cache->uri, uri);
    new_cache->size = insert_size;
    new_cache->time_stamp = counter;

    new_cache->data = (unsigned char*)Calloc(1, MAX_OBJECT_SIZE);
    memcpy(new_cache->data, data, insert_size);
    cache->total_cache_size += insert_size;

    /*If cache space is enough, we can directly insert object to cache*/
    if(cache->total_cache_size <= MAX_CACHE_SIZE) {
        new_cache->next = cache->head;
        cache->head = new_cache;
        counter++;
    }
    /*Otherwise, we need to implement eviction*/
    else {
        eviction(cache);
        new_cache->next = cache->head;
        cache->head = new_cache;
        counter++;
    }

    /*Critical section for writer ends*/
    V(&w);
}


void eviction(cache_list *cache)
{
    cache_elem *temp;
    cache_elem *cache_ptr;
    unsigned int least_recent_time;

    while(cache->total_cache_size > MAX_CACHE_SIZE) {
        cache_ptr = cache->head;
        least_recent_time = update_least_time(cache, cache_ptr);

        if(cache->head->time_stamp == least_recent_time) {
            temp = cache->head;
            cache->head = cache->head->next;
            cache->total_cache_size -= cache_ptr->size;
            free(temp->data);
            free(temp);
        }

        else {
            while(cache_ptr != NULL) {
                if(cache_ptr->next->time_stamp == least_recent_time) {
                    cache->total_cache_size -= cache_ptr->next->size;
                    temp = cache_ptr->next;
                    cache_ptr->next = cache_ptr->next->next;
                    free(temp->data);
                    free(temp);
                }
                cache_ptr = cache_ptr->next;
            }
        }
    }
}


unsigned int update_least_time(cache_list *cache, cache_elem* cache_ptr)
{
    //cache_elem *cache_ptr = cache->head;
    unsigned int least_recent_time = cache->head->time_stamp;

    /*Traverse to find the least used cache and set least_recent_time*/
    while(cache_ptr) {
        if(cache_ptr->time_stamp < least_recent_time)
            least_recent_time = cache_ptr->time_stamp;
        cache_ptr = cache_ptr->next;
    }
    return least_recent_time;
}

