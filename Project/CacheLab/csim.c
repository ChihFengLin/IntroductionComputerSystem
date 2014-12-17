/*
 * Name: Chih-Feng Lin
 * Andrew ID: chihfenl 
 */

#include <stdio.h>
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include "cachelab.h"
#include <string.h>

/*define acceptable commend-line argument*/

const char opt[] = "hvs:E:b:t:";

/*define data structure*/

typedef struct {
  int valid_bit;
  int tag_bit;
  int replace_flag;     //indicate whether the line should be replaced (flag = 0) or not (flag = 1)
  int replace_count;    //count the stay time in the set of line
} line;

typedef struct {
  line *lines;
} set;

typedef struct {
  set *sets;
  int total_set_num;
  int total_line_num;
} cache_simulator;

/*declare function needed in cache simulator*/

int catch_SetBits(int address, int s, int b);
int catch_TagBits(int address, int s, int b);
int parse_commend_argv(int *s, int *E, int *b, char *tracefile, int argc, char* argv[]);
int initialize_cache(cache_simulator *cache, int s, int E, int b);
void load(cache_simulator *cache, unsigned long addr, int s, int b, char* buffer, int* stamp);
void store(cache_simulator *cache, unsigned long addr, int s, int b, char* buffer, int* stamp);
void update_replace_flag(cache_simulator *cache, int select_set, int current_line);

/*define global variable*/

char h = 0, v = 0;
int hit = 0;
int miss = 0;
int eviction = 0;

/*main function: the program starts from here*/

int main(int argc, char* argv[])
{
  FILE *in_file;
  char tracefile[200];
  char read_buf[200];
  int s, E, b, time_stamp;
  unsigned long long address;
  cache_simulator cache;  

  time_stamp = 0;
  parse_commend_argv(&s, &E, &b, tracefile, argc, argv);
  initialize_cache(&cache, s, E, b);
  in_file = fopen(tracefile, "r");  
  
  if(!in_file)
  {
    printf("Open Tracefile %s Error!\n", tracefile);
    return -1;
  }
  else
  {
    while(fgets(read_buf, sizeof(read_buf), in_file) != NULL)
    {
      if(read_buf[0] == 'I')
        continue;
      
      sscanf(read_buf + 2, "%Lx", &address);
      
      switch(read_buf[1])
      {
        case 'S':
                store(&cache, address, s, b, read_buf, &time_stamp);
                break;
        case 'L':
                load(&cache, address, s, b, read_buf, &time_stamp);
                break;
        case 'M':
                load(&cache, address, s, b, read_buf, &time_stamp);
                store(&cache, address, s, b, read_buf, &time_stamp);
                break;
        default:
               break;
      }
    }  
  }
   
  printSummary(hit, miss, eviction);
  
  fclose(in_file);
  return 0;
}

/*return the set bits and tag bits using catch_SetBits and catch_TagBits*/

int catch_SetBits(int addr, int s, int b)
{
  int mask;
  addr = addr >> b;
  mask = 0x7fffffff >> (31 - s);
  return (addr & mask);
}

int catch_TagBits(int addr, int s, int b)
{
  int mask;
  addr = addr >> (s + b);
  mask = 0x7fffffff >> (31 - s - b);
  return (addr & mask);
}
 
/*parse commend-line arguments and return the basic parameter for the cache simulator*/

int parse_commend_argv(int *s, int *E, int *b, char *tracefile, int argc, char* argv[])
{
  int ch, temp, count;
  while((ch = getopt(argc, argv, opt)) != -1) 
  {
    if (optarg != NULL)
      temp = atoi(optarg);
    switch(ch) {
      case 'h':
              h = 1;
              break;
      case 'v':
              v = 1;
              break;
      case 's':
              ++count;
              *s = temp;
              break;
      case 'E':
              ++count;
              *E = temp;
              break;
      case 'b':
              ++count;
              *b = temp;
              break;
      case 't':
              ++count;
              strcpy(tracefile, optarg);
              break;
      default:
              break;
    }
  }
  return 0;
}

/*initialize the cache based on input parameter (s, E, b)*/

int initialize_cache(cache_simulator *cache, int s, int E, int b)
{
  int i, j;
  cache -> total_line_num = E;
  cache -> total_set_num = 2 << s;  // S = (2^s)
  cache -> sets = malloc((cache -> total_set_num) * sizeof(set));
  if (cache -> sets == NULL)
  {
    printf("Initialize Cache Sets Error !");
    return -1;
  }
  for (i = 0; i < cache -> total_set_num; i++)
  {
    cache -> sets[i].lines = malloc((cache -> total_line_num) * sizeof(line));
    if (cache -> sets[i].lines == NULL)
    {
      printf("Initialize Cache Lines Error !");
      return -1;
    }  
    for (j = 0; j < cache -> total_line_num; j++)
    {
      cache -> sets[i].lines[j].valid_bit = 0;
      cache -> sets[i].lines[j].replace_count = 0;
      cache -> sets[i].lines[j].replace_flag = 0;
    }
  }
  return 0;  
}

/*implement load (read) action based on given memory address to check hit, miss or eviction*/

void load(cache_simulator *cache, unsigned long addr, int s, int b, char* buffer, int* stamp)
{
  int i;
  int selected_set, selected_tag;
  
  selected_set = catch_SetBits(addr, s, b);
  selected_tag = catch_TagBits(addr, s, b);
  
  for(i = 0; i < cache -> total_line_num; i++)
  {
    //hit condition
    if (cache -> sets[selected_set].lines[i].valid_bit == 1 && 
                 cache -> sets[selected_set].lines[i].tag_bit == selected_tag)
    { 
      ++hit;
      if (v)
        printf("%s hit\n", buffer+1);
      ++(*stamp);
      cache -> sets[selected_set].lines[i].replace_count = *stamp;
      update_replace_flag(cache, selected_set, i); 
      return;
    }
  }
  //miss condition: it can be approached from two cases, valid_bit = 0 and tag_bit doesn't match.
  ++miss;
  if (v)
        printf("%s miss\n", buffer+1);
  for(i = 0; i < cache -> total_line_num; i++)
  {
    if (cache -> sets[selected_set].lines[i].valid_bit == 0)  //this means there is the empty line
    {
      cache -> sets[selected_set].lines[i].valid_bit = 1;
      cache -> sets[selected_set].lines[i].tag_bit = selected_tag;
      ++(*stamp);
      cache -> sets[selected_set].lines[i].replace_count = *stamp;
      update_replace_flag(cache, selected_set, i);
      return; 
    }
  }
  
  //eviction condition: except for above two conditions, it needs to implement eviction
  ++eviction;
  if (v)
        printf("%s eviction\n", buffer+1); 
  for (i = 0; i < cache -> total_line_num; i++)
  {
    if (cache -> sets[selected_set].lines[i].replace_flag == 1)  //(replace_flag = 1) means this line i should be replaced
    {
      cache -> sets[selected_set].lines[i].valid_bit = 1;
      cache -> sets[selected_set].lines[i].tag_bit = selected_tag;
      ++(*stamp);
      cache -> sets[selected_set].lines[i].replace_count = *stamp;
      update_replace_flag(cache, selected_set, i);
      return;
    }
  }
}

/*implement store (write) action based on given memory address to check hit, miss or eviction*/

void store(cache_simulator *cache, unsigned long addr, int s, int b, char* buffer, int* stamp)
{
  load(cache, addr, s, b, buffer, stamp);
}

/*replacement policy algorithm*/

void update_replace_flag(cache_simulator *cache, int select_set, int current_line)
{
  int i;
  int min_line = current_line;
  
  for(i = 0; i < cache -> total_line_num; i++)
  {
    cache -> sets[select_set].lines[i].replace_flag = 0;  //reset flag
    if ((cache -> sets[select_set].lines[i].valid_bit == 1) &&
             ((cache -> sets[select_set].lines[min_line].replace_count) >
                     (cache -> sets[select_set].lines[i].replace_count)))
    {
      min_line = i;
    }
  }
  cache -> sets[select_set].lines[min_line].replace_flag = 1;
}
