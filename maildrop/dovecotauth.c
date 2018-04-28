/*
** Copyright 2009 Marko Njezic
** Licensed under the same terms as Courier Authlib AND/OR Courier Maildrop.
**
** Partially based on authdaemonlib.c from Courier Authlib, which had the following statement:
**
** Copyright 2000-2006 Double Precision, Inc.  See COPYING for
** distribution information.
**
** Code that was taken from authdaemonlib.c is as follows:
**  - s_connect() function
**  - opensock() function with modification to accept socket address
**  - writeauth() function
**  - readline() function with related support functions (with modification
**    to time-out after TIMEOUT_READ seconds)
*/

#include	"dovecotauth.h"
#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<errno.h>
#include	<fcntl.h>
#include	<pwd.h>
#include	<time.h>
#include	<unistd.h>
#include	<sys/types.h>
#include	<sys/socket.h>
#include	<sys/un.h>
#include	<sys/select.h>

static int TIMEOUT_SOCK=10,
	TIMEOUT_WRITE=10,
	TIMEOUT_READ=30;

static int s_connect(int sockfd,
		     const struct sockaddr *addr,
		     size_t addr_s,
		     time_t connect_timeout)
{
	fd_set fdr;
	struct timeval tv;
	int	rc;

#ifdef SOL_KEEPALIVE
	setsockopt(sockfd, SOL_SOCKET, SOL_KEEPALIVE,
		   (const char *)&dummy, sizeof(dummy));
#endif

#ifdef  SOL_LINGER
        {
		struct linger l;

                l.l_onoff=0;
                l.l_linger=0;

                setsockopt(sockfd, SOL_SOCKET, SOL_LINGER,
			   (const char *)&l, sizeof(l));
        }
#endif

        /*
        ** If configuration says to use the kernel's timeout settings,
        ** just call connect, and be done with it.
        */

        if (connect_timeout == 0)
                return ( connect(sockfd, addr, addr_s));

        /* Asynchronous connect with timeout. */

        if (fcntl(sockfd, F_SETFL, O_NONBLOCK) < 0)     return (-1);

        if ( connect(sockfd, addr, addr_s) == 0)
        {
                /* That was easy, we're done. */

                if (fcntl(sockfd, F_SETFL, 0) < 0)      return (-1);
                return (0);
        }

	if (errno != EINPROGRESS)
		return -1;

	/* Wait for the connection to go through, until the timeout expires */

        FD_ZERO(&fdr);
        FD_SET(sockfd, &fdr);
        tv.tv_sec=connect_timeout;
        tv.tv_usec=0;

        rc=select(sockfd+1, 0, &fdr, 0, &tv);
        if (rc < 0)     return (-1);

        if (!FD_ISSET(sockfd, &fdr))
        {
                errno=ETIMEDOUT;
                return (-1);
        }

	{
		int     gserr;
		socklen_t gslen = sizeof(gserr);

		if (getsockopt(sockfd, SOL_SOCKET,
			       SO_ERROR,
			       (char *)&gserr, &gslen)==0)
		{
			if (gserr == 0)
				return 0;

			errno=gserr;
		}
	}
	return (-1);
}

static int opensock(const char *addr)
{
	int	s=socket(PF_UNIX, SOCK_STREAM, 0);
	struct  sockaddr_un skun;

	memset(&skun, 0, sizeof(skun));
	skun.sun_family=AF_UNIX;
	strncpy(skun.sun_path, addr, sizeof(skun.sun_path)-1);

	if (s < 0)
	{
		perror("CRIT: dovecotauth: socket() failed");
		return (-1);
	}

	{
		const char *p=getenv("TIMEOUT_SOCK");
		int n=atoi(p ? p:"0");

		if (n > 0)
			TIMEOUT_SOCK=n;
	}

	{
		const char *p=getenv("TIMEOUT_READ");
		int n=atoi(p ? p:"0");

		if (n > 0)
			TIMEOUT_READ=n;
	}

	{
		const char *p=getenv("TIMEOUT_WRITE");
		int n=atoi(p ? p:"0");

		if (n > 0)
			TIMEOUT_WRITE=n;
	}

	if (s_connect(s, (const struct sockaddr *)&skun, sizeof(skun),
		      TIMEOUT_SOCK))
	{
		perror("ERR: dovecotauth: s_connect() failed");
		if (errno == ETIMEDOUT || errno == ECONNREFUSED)
			fprintf(stderr, "ERR: [Hint: perhaps dovecot-auth daemon is not running?]\n");
		close(s);
		return (-1);
	}
	return (s);
}

static int writeauth(int fd, const char *p, unsigned pl)
{
fd_set  fds;
struct  timeval tv;

	while (pl)
	{
	int     n;

		FD_ZERO(&fds);
		FD_SET(fd, &fds);
		tv.tv_sec=TIMEOUT_WRITE;
		tv.tv_usec=0;
		if (select(fd+1, 0, &fds, 0, &tv) <= 0 || !FD_ISSET(fd, &fds))
			return (-1);
		n=write(fd, p, pl);
		if (n <= 0)     return (-1);
		p += n;
		pl -= n;
	}
	return (0);
}

struct enum_getch {
	char buffer[BUFSIZ];
	char *buf_ptr;
	size_t buf_left;
};

#define getauthc(fd,eg) ((eg)->buf_left-- ? \
			(unsigned char)*((eg)->buf_ptr)++:\
			fillgetauthc((fd),(eg)))

static int fillgetauthc(int fd, struct enum_getch *eg)
{
	time_t	end_time, curtime;

	time(&end_time);
	end_time += TIMEOUT_READ;

	for (;;)
	{
		int     n;
		fd_set  fds;
		struct  timeval tv;

		time(&curtime);
		if (curtime >= end_time)
			break;

		FD_ZERO(&fds);
		FD_SET(fd, &fds);
		tv.tv_sec=end_time - curtime;
		tv.tv_usec=0;
		if (select(fd+1, &fds, 0, 0, &tv) <= 0 || !FD_ISSET(fd, &fds))
			break;

		n=read(fd, eg->buffer, sizeof(eg->buffer));
		if (n <= 0)
			break;

		eg->buf_ptr=eg->buffer;
		eg->buf_left=n;

		--eg->buf_left;
		return (unsigned char)*(eg->buf_ptr)++;
	}
	return EOF;
}

static int readline(int fd, struct enum_getch *eg,
		    char *buf,
		    size_t bufsize)
{
	if (bufsize == 0)
		return EOF;

	while (--bufsize)
	{
		int ch=getauthc(fd, eg);

		if (ch == EOF)
			return -1;
		if (ch == '\n')
			break;

		*buf++=ch;
	}
	*buf=0;
	return 0;
}

/*
** The actual implementation of Dovecot authentication protocol handling follows.
** Full specification of the protocol can be found at: http://wiki.dovecot.org/Authentication%20Protocol
** We are only interested in the "master" type requests for user information.
*/

int parse_userinfo(const char *user, const char *linebuf,
	int (*func)(struct dovecotauthinfo *, void *), void *arg)
{
	int return_value=1;
	struct dovecotauthinfo a;
	char *buf, *p;
	uid_t u;

	/* Validate input arguments */
	if (!user || !linebuf)
		return (1);

	/* Try to allocate buffer */
	buf = (char *)malloc(strlen(linebuf)+1);
	if (!buf)
		return (1);
	strcpy(buf, linebuf);

	memset(&a, 0, sizeof(a));
	a.homedir="";

	p = strtok(buf, "\t");
	if (p)
		a.address=p;
	else
		a.address=user;

	/* Parse any additional parameters */
	while ((p = strtok(0, "\t")) != 0)
	{
		if (strncmp(p, "uid=", 4) == 0)
		{
			u=atol(p+4);
			a.sysuserid = &u;
			if (u == 0)
			{
				fprintf(stderr, "ERR: dovecotauth: Received invalid uid from auth socket\n");
				return_value=1;
				goto cleanup_parse_userinfo;
			}
		}
		else if (strncmp(p, "gid=", 4) == 0)
		{
			a.sysgroupid=atol(p+4);
			if (a.sysgroupid == 0)
			{
				fprintf(stderr, "ERR: dovecotauth: Received invalid gid from auth socket\n");
				return_value=1;
				goto cleanup_parse_userinfo;
			}
		}
		else if (strncmp(p, "system_user=", 12) == 0)
		{
			a.sysusername=p+12;
			if (a.sysusername)
			{
				struct passwd *q=getpwnam(a.sysusername);

				if (q && q->pw_uid == 0)
				{
					fprintf(stderr, "ERR: dovecotauth: Received invalid system user from auth socket\n");
					return_value=1;
					goto cleanup_parse_userinfo;
				}
			}
		}
		else if (strncmp(p, "home=", 5) == 0)
		{
			a.homedir=p+5;
		}
		else if (strncmp(p, "mail=", 5) == 0)
		{
			a.maildir=p+5;
		}
	}

	return_value = (*func)(&a, arg);

cleanup_parse_userinfo:
	free(buf);
	return return_value;
}

#define	DOVECOTAUTH_LINEBUFSIZE	8192

int _dovecotauth_getuserinfo(int wrfd, int rdfd, const char *user,
	int (*func)(struct dovecotauthinfo *, void *), void *arg)
{
	static char cmdpart1[]="VERSION\t1\t0\nUSER\t1\t";
	static char cmdpart2[]="\tservice=maildrop\n";
	int return_value=1, handshake=0;
	struct enum_getch eg;
	char *cmdbuf, *linebuf;

	/* Validate input arguments */
	if (!user)
		return (1);

	/* Try to allocate buffers */
	cmdbuf=(char *)malloc(strlen(cmdpart1)+strlen(cmdpart2)+strlen(user)+20);
	if (!cmdbuf)
		return (1);

	linebuf=(char *)malloc(DOVECOTAUTH_LINEBUFSIZE);
	if (!linebuf)
		return (1);

	/* Initial handshake */
	eg.buf_left=0;
	while (readline(rdfd, &eg, linebuf, DOVECOTAUTH_LINEBUFSIZE) == 0)
	{
		if (strncmp(linebuf, "VERSION\t", 8) == 0)
		{
			if (strncmp(linebuf+8, "1\t", 2) != 0)
			{
				fprintf(stderr, "ERR: dovecotauth: Authentication protocol version mismatch\n");
				return_value=1;
				goto cleanup_dovecotauth_getuserinfo;
			}
		}
		else if (strncmp(linebuf, "SPID\t", 5) == 0)
		{
			/* End of server side handshake */
			handshake=1;
			break;
		}
	}

	if (!handshake)
	{
		fprintf(stderr, "ERR: dovecotauth: Did not receive proper server handshake from auth socket\n");
		return_value=1;
		goto cleanup_dovecotauth_getuserinfo;
	}

	/*
	** Try to be helpful in case that user tries to connect to the wrong auth socket.
	** There's a slight chance that this won't execute in case that the previously
	** returned line ends exactly at the buffer end, but we won't handle that case,
	** since this is just a hint to the user, and not really neccessary.
	** Normally, if user tries to communicate with wrong auth socket,
	** we would simply time-out, while waiting for information.
	*/
	if (eg.buf_left > 0 && readline(rdfd, &eg, linebuf, DOVECOTAUTH_LINEBUFSIZE) == 0)
	{
		if (strncmp(linebuf, "CUID\t", 5) == 0)
		{
			fprintf(stderr, "ERR: dovecotauth: Trying to connect to what appears to be a client auth socket, instead of a master auth socket\n");
			return_value=1;
			goto cleanup_dovecotauth_getuserinfo;
		}
	}

	/* Generate our part of communication */
	strcat(strcat(strcpy(cmdbuf, cmdpart1), user), cmdpart2);

	/* Send our part of communication */
	if (writeauth(wrfd, cmdbuf, strlen(cmdbuf)))
	{
		return_value=1;
		goto cleanup_dovecotauth_getuserinfo;
	}

	/* Parse returned information */
	eg.buf_left=0;
	if (readline(rdfd, &eg, linebuf, DOVECOTAUTH_LINEBUFSIZE) == 0)
	{
		if (strncmp(linebuf, "USER\t1\t", 7) == 0)
		{
			/* User was found in the database and we now parse returned information */
			return_value=parse_userinfo(user, linebuf+7, func, arg);
			goto cleanup_dovecotauth_getuserinfo;
		}
		else if (strcmp(linebuf, "NOTFOUND\t1") == 0)
		{
			/* User was not found in the database */
			return_value=-1; /* Negative return value means that user is not found! */
			goto cleanup_dovecotauth_getuserinfo;
		}
		else if (strncmp(linebuf, "FAIL\t1", 6) == 0)
		{
			/* An internal error has occurred on Dovecot's end */
			return_value=1;
			goto cleanup_dovecotauth_getuserinfo;
		}
		else
		{
			fprintf(stderr, "ERR: dovecotauth: Received unknown input from auth socket\n");
		}
	}
	else
		fprintf(stderr, "ERR: dovecotauth: Did not receive proper input from auth socket\n");

cleanup_dovecotauth_getuserinfo:
	free(cmdbuf);
	free(linebuf);
	return return_value;
}

int dovecotauth_getuserinfo(const char *addr, const char *user,
	int (*func)(struct dovecotauthinfo *, void *), void *arg)
{
	int	s=opensock(addr);
	int	rc;

	if (s < 0)
	{
		return (1);
	}
	rc = _dovecotauth_getuserinfo(s, s, user, func, arg);
	close(s);
	return rc;
}
