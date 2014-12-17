/*
 * Name: Chih-Feng Lin
 * Andrew ID: chihfenl
 *
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 */ 
#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

#define BLOCK_SIZE 8
#define HALF_BLOCK_SIZE 4

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, p, q, temp;
    int *A_buf, *B_buf;
    int r = 0;

    REQUIRES(M > 0);
    REQUIRES(N > 0);
    
    /*use blocked method with 8*8 size block*/
    if(M == 32 && N == 32)
    {
      for(i = 0; i < N; i += BLOCK_SIZE)
      {
        for(j = 0; j < M; j += BLOCK_SIZE)
        {
          for(p = i; p < i + BLOCK_SIZE; p++)
          {
            r = 0 + p;
            A_buf = A[p];
            
            if (i == j)                  //reduce the confilc misses of the condition of diagnal case
              temp = A_buf[p];           // use temp buffer to store it
            
            for(q = j; q < j + BLOCK_SIZE; q++)
            { 
              if (q % BLOCK_SIZE == 0)
                B_buf = B[q];
              
              if (p != q)
                B_buf[r] = A_buf[q];
              
              r = r + 32;
            }
            
            if (i == j)
              B[p][p] = temp;
          }
        }
      }
    }

   /*
    * Similar to 32*32, we change the BLOCK_SIZE into HALF_BLOCK_SIZE to optimaize cache computation
    */
    
    if(M == 64 && N == 64)
    {
      for (j = 0; j < N; j += HALF_BLOCK_SIZE) 
      { 
        for (i = 0; i < N; i += HALF_BLOCK_SIZE) 
        {
          for (p = i; p < i + HALF_BLOCK_SIZE; p++) 
          { 
            r = 0 + p;
            A_buf = A[p];
           
            if(i == j)
              temp = A_buf[p];
            
            for (q = j; q < j + HALF_BLOCK_SIZE; q++) 
            {
              if (q % HALF_BLOCK_SIZE == 0)
                B_buf = B[q];

              if (p != q) 
                B_buf[r] = A_buf[q];

              r = r + 64;
            }
            
            if (i == j) 
              B[p][p] = temp;
            
          }	
        }
      }   
    }

    /*
     *  61*67 is similar to the case of 32*32, 
     *  and we only need to care about the transpose boundary
     */

    if(M == 61 && N == 67)
    {
      for(i = 0; i < N; i += BLOCK_SIZE)
      {
        for(j = 0; j < M; j += BLOCK_SIZE)
        {
          for(p = j; p < j + BLOCK_SIZE; p++)
          {
            if(p < M)
            {
              for(q = i; q < i + BLOCK_SIZE; q++)
              {
                if(q < N)
                  B[p][q] = A[q][p];
              }
            }
          }
        }
      }
    }

    
    ENSURES(is_transpose(M, N, A, B));
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc); 

}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

