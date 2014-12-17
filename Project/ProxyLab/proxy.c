/*
* Proxy Lab
*
* Name: Chih-Feng Lin
        Chi-Heng Wu
* Andrew ID: chihfenl
*            chihengw
*/

#include <stdio.h>
#include "csapp.h"
#include "cache.h"

/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* You won't lose style points for including these long lines in your code */
static const char *user_agent_hdr = "User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:10.0.3) Gecko/20120305 Firefox/10.0.3\r\n";
static const char *accept_hdr = "Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n";
static const char *accept_encoding_hdr = "Accept-Encoding: gzip, deflate\r\n";


/* Function prototypes */
void sigpipe_handler(int sig);
void *thread(void *vargp);
void do_transaction(int fd);
void clienterror(int fd, char *cause, char *errnum, char *shortmsg, char *longmsg);
void parse_request_url(char *url, char *hostname, int *port, char *uri);
void make_request_info(rio_t *rio, char *request_header, char *method, char *hostname, char *uri);
void request_to_server(char *hostname, char *uri, int port, int client_fd, char* request_header);
int check_object_size(size_t *object_size, size_t read_num, unsigned char *object_data, unsigned char *buf);

/*Global variables*/
cache_list *cache;


/*
*  When socket has been broken, kernel will send SIGPIPE to process.
*  The default action is to terminate. We use sigpipe_handler to avoid terminating.
*/

void sigpipe_handler(int sig)
{
    printf("Received SIGPIPE. Proxy ignored it.");
}


/*
 * main
 */
int main(int argc, char **argv)
{

    int listenfd, *connfdp, port;
    socklen_t clientlen = sizeof(struct sockaddr_in);
    struct sockaddr_in clientaddr;
    pthread_t tid;

    /*Install SIGPIPE handler to prevent process terminal*/
    Signal(SIGPIPE, sigpipe_handler);

    if(argc != 2) {
        fprintf(stderr, "usage: %s <port>\n", argv[0]);
        exit(0);
    }

    /*Set listening port and initialize web cache*/
    cache = (cache_list*)Calloc(1, sizeof(cache_list));
    cache->total_cache_size = 0;
    cache->head = NULL;
    initialize_cache();
    port = atoi(argv[1]);
    listenfd = Open_listenfd(port);

    /*Here I use straightforward method to spawn a new worker thread for each request*/
    while(1) {
		int counter = 0;
		while ((connfdp = (int*)Calloc(1, sizeof(int))) == NULL) {
        	if(counter > 10)
				break;
			counter++;
			sleep(1);
		}
		//connfdp = (int*)Calloc(1, sizeof(int));
        *connfdp = Accept(listenfd, (SA*) &clientaddr, &clientlen);
        Pthread_create(&tid, NULL, thread, connfdp);
    }

    return 0;
}

/*
* Thread routine - Use detach function to make spare resources be automatically
*                  reaped upon thread exit
*/
void *thread(void *vargp)
{
    int connfd;
    connfd = *((int*)vargp);
    Pthread_detach(Pthread_self());
    free(vargp);
    do_transaction(connfd);
    Close(connfd);
    return NULL;

}

/*
* do_transaction - Send request to web sever and sned the response accepted
*                  from server back to client
*/

void do_transaction(int fd)
{
    char request_header[MAXLINE];
    char buf[MAXLINE], method[MAXLINE], url[MAXLINE], version[MAXLINE];
    char uri[MAXLINE], hostname[MAXLINE];
    int port;
    rio_t rio;
    cache_elem *cached_object;


    /*Read request line and header from client*/
    Rio_readinitb(&rio, fd);
    rio_readlineb(&rio, buf, MAXLINE);  //write the data to the buf
    sscanf(buf, "%s %s %s", method, url, version); //move buf data respectively to three variables

    /*Set proxy to be able to handle GET request*/
    if(strcasecmp(method, "GET")) {
        clienterror(fd, method, "501", "Not Implemented",
                        "Proxy does not implement this method");
        return;
    }

    parse_request_url(url, hostname, &port, uri);
    make_request_info(&rio, request_header, method, hostname, uri);

    /*Check whether exists cached object*/
    cached_object = check_cache_list(cache, hostname, &port, uri);
    if (cached_object != NULL) {
        /*If exists, directly send the cached memory as response to client*/
	rio_writen(fd, cached_object->data, cached_object->size);
	return;
    }

    /*If object has not been cached, pass the request to web server*/
    request_to_server(hostname, uri, port, fd, request_header);
}

/*
* clienterror - Report the error to the clients
*/
void clienterror(int fd, char *cause, char *errnum, char *shortmsg, char *longmsg)
{
    char buf[MAXLINE], body[MAXBUF];

    /*Build the HTTP response body*/
    sprintf(body, "<html><title>Proxy error</title>");
    sprintf(body, "%s<body bgcolor=""ffffff"">\r\n", body);
    sprintf(body, "%s%s: %s\r\n", body, errnum, shortmsg);
    sprintf(body, "%s<p>%s: %s\r\n", body, longmsg, cause);
    sprintf(body, "%s<hr><em>The Proxy</em>\r\n", body);

    /*Print the HTTP response*/
    sprintf(buf, "HTTP/1.0 %s %s\r\n", errnum, shortmsg);
    rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-type: text/html\r\n");
    rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
    rio_writen(fd, buf, strlen(buf));
    rio_writen(fd, body, strlen(body));
}

/*
 * parse_request_url - 
 */
void parse_request_url(char *url, char *hostname, int *port, char *uri)
{
    char *ptr, *temp_ptr, *path, *port_ptr;

    /*If HTTP request includes the host name, we need to parse uri and hostname respectively*/
    if(strstr(url, "http") != NULL) {
        ptr = strchr(url, '/');
        temp_ptr = ptr + 2;
        if((path = strchr(temp_ptr, '/')) != NULL) {
            path[0] = '\0';
            strcpy(uri, "/");
            strcat(uri, ++path);
            strcpy(hostname, temp_ptr);
        } else {
            strcpy(uri, "/");
            strcpy(hostname, temp_ptr);
        }

        /*Extract port number from the hostname*/
        if((port_ptr = strchr(hostname, ':')) == NULL) {
            *port = 80; //use default port number
        } else {
            port_ptr[0] = '\0';
            port_ptr++;
            *port = atoi(port_ptr);
        }
    }
}

/*
* make_request_info - This function creates the request via the information from
*                     parse_request_url function.
*/

void make_request_info(rio_t *rio, char *request_header, char *method, char *hostname, char *uri)
{
    char buf[MAXLINE];

    /* Make the first line of request header */
    strcpy(request_header, "");
    sprintf(request_header, "%s %s HTTP/1.0\r\n", method, uri);

    /* Read client's rest request */
    rio_readlineb(rio, buf, MAXLINE);
    
    while(strcmp(buf, "\r\n")) {
        rio_readlineb(rio, buf, MAXLINE);
        if (strstr(buf, "Host:")) {
	    sprintf(request_header, "%s%s", request_header, buf);
	} else {
            sprintf(request_header, "%sHost: %s\r\n",request_header, hostname);
        }
    }

    sprintf(request_header, "%s%s", request_header, user_agent_hdr);
    sprintf(request_header, "%s%s", request_header, accept_hdr);
    sprintf(request_header, "%s%s", request_header, accept_encoding_hdr);
    sprintf(request_header, "%sConnection: close\r\n", request_header);
    sprintf(request_header, "%sProxy-Connection: close\r\n", request_header);
    sprintf(request_header, "%s\r\n", request_header);
}


/*
* request_to_serer - pass client's request to web server
*/
void request_to_server(char *hostname, char *uri, int port, int client_fd, char* request_header) {

    unsigned char buf[MAXLINE];
    unsigned char object_data[MAX_OBJECT_SIZE];
    int proxy_fd, is_over;
    rio_t rio;
    size_t read_num, object_size = 0;

    /*Establish connection between proxy and web server*/
    proxy_fd = open_clientfd_r(hostname, port);

    /*Check whether proxy_fd is valid or not*/
    if(proxy_fd < 0) {
        printf("Establish connection to web server error");
        return;
    }

    Rio_readinitb(&rio, proxy_fd);

    /*Send client's request to web server*/
    rio_writen(proxy_fd, request_header, strlen(request_header));

    /*Read response info from web server*/
    while((read_num = rio_readlineb(&rio, buf, MAXLINE)) != 0) {

        /*Send web server's response to client*/
        rio_writen(client_fd, buf, read_num);

        /*Check whether web object can be cached based on MAX_OBJECT_SIZE*/
        is_over = check_object_size(&object_size, read_num, object_data, buf);
				
    }

    if(!is_over) {
        insert_to_cache(cache, hostname, &port, uri, object_data, object_size);
    }

    Close(proxy_fd);

}

int check_object_size(size_t *object_size, size_t read_num, unsigned char *object_data, unsigned char *buf)
{
    int is_over, i;
    if(*object_size + read_num > MAX_OBJECT_SIZE) {

        /*This object can not be cached because its size is over criteria*/
        is_over = 1;

    } else {

        for(i = 0; i < read_num; i++) {
            object_data[(*object_size)++] = buf[i];
        }
        is_over = 0;
    }
    return is_over;
}

