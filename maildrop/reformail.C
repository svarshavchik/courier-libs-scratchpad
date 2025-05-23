/*
** Copyright 1998 - 2023 Double Precision, Inc.
** See COPYING for distribution information.
*/

#include	"config.h"

#include	<stdio.h>
#include	<iostream>
#include	<iomanip>
#include	<stdlib.h>
#include	<string.h>
#include	<ctype.h>
#include	<signal.h>
#include	<pwd.h>

#if	HAVE_LOCALE_H
#include	<locale.h>
#endif

#if HAVE_UNISTD_H
#include	<unistd.h>
#endif
#if HAVE_FCNTL_H
#include	<fcntl.h>
#endif
#include	"mytime.h"
#include	<sys/types.h>
#include	"mywait.h"
#if HAVE_SYS_FILE_H
#include	<sys/file.h>
#endif
#include	"rfc822.h"
#include	"buffer.h"
#include	"liblock/config.h"
#include	"liblock/liblock.h"
#include <string>
#include <vector>
#include <algorithm>

#if	HAS_GETHOSTNAME
#else
extern "C" int gethostname(const char *, size_t);
#endif


static int inbody=0, addcrs=0, catenate=0;
static const char *(*append_more_headers)();

typedef std::vector<std::string> multibuf;
static multibuf	optx, optX, opta, optA, opti, optI, optu, optU, optubuf, optUbuf, optR;

typedef multibuf::iterator multibuf_iterator;


static std::string add_from_filter_buf;
static const char *add_from_filter_buf_ptr;
static const char *cache_maxlen="", *cache_name="";

static const char *( *from_filter)();
static std::string	current_line;

void outofmem()
{
	std::cerr << "reformail: Out of memory." << std::endl;
	exit(1);
}

void help()
{
	std::cerr << "reformail: Invalid arguments." << std::endl;
	exit(1);
}

// Return next line from standard input.  Trailing CRs are stripped

const char *NextLine()
{
static std::string buf;
int	c;

	buf.clear();
	while ((c=std::cin.get()) >= 0 && c != '\n')
		buf.push_back(c);
	if (c < 0 && buf.size() == 0)	return (0);
	if (buf.size())	// Strip CRs
	{
		c=buf.back();

		if (c == '\r')
			buf.pop_back();
	}
	buf.push_back('\n');
	return (buf.c_str());
}

// from_filter is the initial filtering done on the message.
// from_filter adds or subtracts "From " quoting from the message.
// from_filter returns the next line from the message, after filtering.
// The line is always terminated by a newline character.
// When the header is being read, multiline headers are silently
// concatenated into a single return from from_filter() (separated by
// newlines, of course.
//
// from_filter is initialized to either from_filter(), add_from_filter()
// and rem_from_filter() respectively, to cause either addition, removal of,
// or no change to from quoting.  The pointer is automatically updated.
//
// Also, the from_filter silently discards empty lines at the beginning of
// the message.

// DO NOT CHANGE FROM QUOTING.

const char *no_from_filter_header();

const char *no_from_filter()
{
const	char *p;

	while ((p=NextLine()) && *p == '\n')
		;
	if (!p)	return (0);

	current_line=p;
	return ( no_from_filter_header() );
}

const char *read_blank();

const char *no_from_filter_header()
{
const	char *p;

static std::string buf;

	from_filter= &no_from_filter_header;

	while ((p=NextLine()) && *p && *p != '\n' && isspace((unsigned char)*p))
		current_line += p;

	buf=current_line;
	if (!p || *p == '\n')
	{
		from_filter= &read_blank;
		return (buf.c_str());
	}
	current_line=p;
	return (buf.c_str());
}

const char *read_blank()
{
	from_filter= &NextLine;
	return ("\n");
}

//////////////////////////////////////////////////////////////////////////
//
//  Add 'From ' quoting.  All headers are read into add_from_filter_buf,
//  and a suitable return address is located.  The 'From ' line is
//  generated, and return.  Subsequent calls fetch one header at a
//  time from add_from_filter_buf, then resume reading the body of the
//  message.
//
//////////////////////////////////////////////////////////////////////////

const char *add_from_filter_header();
const char *add_from_filter()
{
const	char *p;

	while ((p=NextLine()) && *p == '\n')
		;
	if (!p)	return (0);

	current_line=p;
	if (strncmp(p, "From ", 5) == 0)
		return ( no_from_filter_header() );
	add_from_filter_buf.clear();
	while (p && *p != '\n')
	{
		add_from_filter_buf += p;
		p=NextLine();
	}


static std::string	return_path;
static std::string	from_header;

	return_path.clear();
	from_header.clear();

	for (p=add_from_filter_buf.c_str(); *p; )
	{
	std::string	header;

		while (*p && *p != ':' && *p != '\n')
		{
		int	c= (unsigned char)*p++;

			c=tolower(c);
			header.push_back(c);
		}
		for (;;)
		{
			while (*p && *p != '\n')
			{
				header.push_back(*p);
				p++;
			}
			if (!*p)	break;
			++p;
			header.push_back('\n');
			if (!*p || !isspace((unsigned char)*p))	break;
		}
		if (strncmp(header.c_str(), "return-path:", 12) == 0 ||
		    strncmp(header.c_str(), ">return-path:", 13) == 0 ||
		    strncmp(header.c_str(), "errors-to:", 10) == 0 ||
		    strncmp(header.c_str(), ">errors-to:", 11) == 0)
		{
			const char *p;

			for (p=header.c_str(); *p != ':'; p++)
				;
			return_path=p;
		}

		if (strncmp(header.c_str(), "from:", 5) == 0)
			from_header=header.c_str() + 5;
	}
	if (return_path.size() == 0)	return_path=from_header;

	rfc822::tokens rfc{return_path, [](size_t){}};

	rfc822::addresses addresses{rfc};

	for (auto &a:addresses)
	{
		if (!a.address.empty())
		{
			from_header.clear();
			a.address.print(std::back_inserter(from_header));
		}
	}

	if (from_header.size() == 0)	from_header="root";
	return_path="From ";
	return_path += from_header;
	return_path.push_back(' ');
time_t	t;

	time(&t);
	p=ctime(&t);
	while (*p && *p != '\n')
	{
		return_path.push_back(*p);
		p++;
	}
	return_path += "\n";
	from_filter=add_from_filter_header;
	add_from_filter_buf_ptr=add_from_filter_buf.c_str();
	return (return_path.c_str());
}

const char *add_from_filter_body();

const char *add_from_filter_header()
{
static std::string buf;

	buf.clear();

	if (*add_from_filter_buf_ptr == '\0')
	{
		from_filter= &add_from_filter_body;
		return ("\n");
	}

	do
	{
		while (*add_from_filter_buf_ptr)
		{
			buf.push_back( (unsigned char)*add_from_filter_buf_ptr );
			if ( *add_from_filter_buf_ptr++ == '\n')	break;
		}
	} while ( *add_from_filter_buf_ptr && *add_from_filter_buf_ptr != '\n'
		&& isspace( (unsigned char)*add_from_filter_buf_ptr ));
	return (buf.c_str());
}

const char *add_from_filter_body()
{
const char *p=NextLine();

	if (!p)	return (p);

const char *q;

	for (q=p; *q == '>'; q++)
		;
	if (strncmp(q, "From ", 5))	return (p);

static std::string add_from_buf;

	add_from_buf=">";
	add_from_buf += p;
	return (add_from_buf.c_str());
}

////////////////////////////////////////////////////////////////////////////
//
// Strip From quoting.
//
////////////////////////////////////////////////////////////////////////////

const char *rem_from_filter_header();

const char *(*rem_from_filter_header_ptr)();

const char *rem_from_filter()
{
const	char *p;

	while ((p=NextLine()) && *p == '\n')
		;
	if (!p)	return (0);

	if (strncmp(p, "From ", 5))
	{
		current_line=p;
		return ( no_from_filter_header() );
	}

	std::string new_opti="Return-Path: <";

	for (p += 5; *p && *p != '\n' && isspace(*p); ++p)
		;
	if (*p == '<')
		++p;

	while (*p && *p != '\n' && *p != '>' && !isspace(*p))
	{
		new_opti.push_back(*p);
		++p;
	}
	new_opti.push_back('>');
	optI.push_back(new_opti);

	p=NextLine();
	if (!p)	return (p);
	current_line=p;
	rem_from_filter_header_ptr= &no_from_filter_header;
	return ( rem_from_filter_header() );
}

const char *rem_from_filter_body();
const char *rem_from_filter_header()
{
const char *p=(*rem_from_filter_header_ptr)();

	rem_from_filter_header_ptr=from_filter;
	from_filter=rem_from_filter_header;
	if (!p || *p == '\n')
	{
		from_filter=&rem_from_filter_body;
		p="\n";
	}
	return (p);
}

const char *rem_from_filter_body()
{
const char *p=NextLine();

	if (!p)	return (p);

	if (*p == '>')
	{
	const char *q;

		for (q=p; *q == '>'; q++)
			;
		if (strncmp(q, "From ", 5) == 0)	++p;
	}
	return (p);
}

static const char *HostName()
{
static char hostname_buf[256];

	hostname_buf[0]=0;
	hostname_buf[sizeof(hostname_buf)-1]=0;
	gethostname(hostname_buf, sizeof(hostname_buf)-1);
	return (hostname_buf);
}

////////////////////////////////////////////////////////////////////////////
//
// Return TRUE if header is already in a list of headers.
//
// hdrs: list of headers
// hdr - header to check (must be lowercase and terminated by a colon)
// pos - if found, the specific header, and the iterator to one past the
//       colon.

static bool has_hdr(multibuf &hdrs, const std::string &hdr,
		    multibuf_iterator &ret)
{
	for (auto b=hdrs.begin(), e=hdrs.end(); b != e; ++b)
	{
		if (b->size() < hdr.size())
			continue;

		auto p=b->begin();

		auto hb=hdr.begin(), he=hdr.end();

		for (; hb != he; ++hb, ++p)
		{
			if (*hb != tolower(*p))
				break;
		}

		if (hb == he)
		{
			ret=b;
			return true;
		}
	}
	return false;
}

static bool has_hdr(multibuf &hdrs, const std::string &hdr)
{
	multibuf_iterator dummy;

	return (has_hdr(hdrs, hdr, dummy));
}

static void strip_empty_header(multibuf &buf)
{
	auto b=buf.begin(), e=buf.end(), p=b;

	while (b != e)
	{
		auto ce=b->end();

		auto ptr=std::find(b->begin(), ce, ':');

		if (ptr != ce && ++ptr == ce)
		{
			++b;
			continue;
		}

		if (b != p)
			*p=*b;
		++p;
		++b;
	}
	buf.erase(p, e);
}

const char *ReadLineAddNewHeader();

const char *ReadLineAddHeader()
{
	std::string buf1;
	const char *q;
	const char *p;
	multibuf_iterator pos;
	static std::string oldbuf;

	for (;;)
	{
		p= (*from_filter)();

		if (!p)	return p;
		if (*p == '\n')
		{
			strip_empty_header(opti);
			strip_empty_header(optI);
			return ( ReadLineAddNewHeader());
		}
		buf1.clear();
		for (q=p; *q && *q != '\n'; q++)
		{
			buf1.push_back( tolower(*q) );
			if (*q == ':')	break;
		}

		if (has_hdr(opti, buf1))
		{
			oldbuf="old-";
			oldbuf += buf1;
			buf1=oldbuf;

			std::string	tbuf;

			tbuf="Old-";
			tbuf += p;
			oldbuf=tbuf;
			p=oldbuf.c_str();
		}
		if (has_hdr(optR, buf1, pos))
		{
			std::string tbuf=pos->substr(buf1.size());

			p += buf1.size();

			tbuf += p;
			oldbuf=tbuf;
			p=oldbuf.c_str();
		}

		if (has_hdr(optI, buf1))
			continue;
		if (has_hdr(optu, buf1))
		{
			if (!has_hdr(optubuf, buf1))
			{
				optubuf.push_back(p);
				break;
			}
			continue;
		}

		if (has_hdr(optU, buf1))
		{
			if (has_hdr(optUbuf, buf1, pos))
				optUbuf.erase(pos);

			std::string s{p};

			s.pop_back();

			optUbuf.push_back(std::move(s));
			continue;
		}
		break;
	}

	if (has_hdr(opta, buf1, pos))
		opta.erase(pos);
	return (p);
}

const char *ReadLineAddNewHeaderDone();

const char *ReadLineAddNewHeader()
{
	append_more_headers= &ReadLineAddNewHeader;

	multibuf *bufptr;

	if (opta.size())	bufptr= &opta;
	else if (optA.size())	bufptr= &optA;
	else if (opti.size())	bufptr= &opti;
	else if (optI.size())	bufptr= &optI;
	else if (optUbuf.size())	bufptr= &optUbuf;
	else
	{
		append_more_headers=&ReadLineAddNewHeaderDone;
		return ("\n");
	}

	static std::string buf1;

	buf1= (*bufptr)[0];

	buf1.push_back('\n');

	(*bufptr).erase((*bufptr).begin());

	return (buf1.c_str());
}

const char *ReadLineAddNewHeaderDone()
{
	return ( (*from_filter)() );
}

////////////////////////////////////////////////////////////////////////////
const char *ReadLine()
{
const char *p=(*append_more_headers)();

	if (!p)	return (p);

static std::string	buf;

	if (*p == '\n')
		inbody=1;

	if (catenate && !inbody)
	{
	const char *q;

		buf.clear();
		for (q=p; *q; q++)
		{
			if (*q != '\n')
			{
				buf.push_back(*q);
				continue;
			}
			do
			{
				++q;
			} while (*q && isspace(*q));
			if (*q)
				buf.push_back(' ');
			--q;
		}
		if (addcrs)	buf.push_back('\r');
		buf.push_back('\n');
		return (buf.c_str());
	}

	if (addcrs)
	{
		buf=p;
		buf.pop_back();
		buf += "\r\n";
		return (buf.c_str());
	}
	return (p);
}

/////////////////////////////////////////////////////////////////////////
//
// Default activity: just copy the message (let the low-level format
// filters do their job.
//
/////////////////////////////////////////////////////////////////////////

void copy(int, char *[], int)
{
const char *p;

	while ((p= ReadLine()) != 0)
		std::cout << p;
}

void cache(int, char *[], int)
{
const char *p;
std::string	buf;
int found=0;

	addcrs=0;
	while ((p= ReadLine()) != 0)
	{
	int	c;

		if (inbody)	break;
		buf.clear();
		while (*p && *p != '\n')
		{
			c= (unsigned char)*p;
			c=tolower(c);
			buf.push_back(c);
			if (*p++ == ':')	break;
		}
		if (!(buf == "message-id:"))	continue;
		while (*p && isspace( (unsigned char)*p))	p++;
		buf.clear();
		while (*p)
		{
			buf.push_back(*p);
			++p;
		}

		while (buf.size())
		{
			auto c=buf.back();

			if (!isspace(c))
				break;
			buf.pop_back();
		}

		if (buf.size() == 0)	break;

	int	fd=open(cache_name, O_RDWR | O_CREAT, 0600);

		if (fd < 0)
		{
			perror("open");
			exit(75);
		}

		if (ll_lock_ex(fd) < 0)
		{
			perror("lock");
			exit(75);
		}

	off_t	pos=0;

		if (lseek(fd, 0L, SEEK_END) == -1 ||
			(pos=lseek(fd, 0L, SEEK_CUR)) == -1 ||
			lseek(fd, 0L, SEEK_SET) == -1)
		{
			perror("seek");
			exit(75);
		}

	off_t	maxlen_n=atol(cache_maxlen);
	char	*charbuf;
	off_t	newpos=maxlen_n;

		if (newpos < pos)	newpos=pos;

		if ((charbuf=new char[newpos+buf.size()+1]) == NULL)
			outofmem();

	off_t	readcnt=read(fd, charbuf, newpos);

		if (readcnt < 0)	perror("read");

	char *q, *r;

		for (q=r=charbuf; q<charbuf+readcnt; )
		{
			if (*q == '\0')	break;	// Double null terminator
			if (strcmp( buf.c_str(), q) == 0)
			{
				found=1;
				while (q < charbuf+readcnt)
					if (*q++ == '\0')	break;
			}
			else while (q < charbuf+readcnt)
				if ( (*r++=*q++) == '\0') break;
		}
		memcpy(r, buf.c_str(), buf.size());
		r += buf.size();
		for (q=charbuf; q<r; )
		{
			if (r - q < maxlen_n)
				break;
			while (q < r)
				if (*q++ == '\0')	break;
		}
		if (q == r)	q=charbuf;
		*r++ = '\0';
		if (lseek(fd, 0L, SEEK_SET) == -1)
		{
			perror("lseek");
			exit(1);
		}
		while (q < r)
		{
			readcnt=write(fd, q, r-q);
			if (readcnt == -1)
			{
				perror("write");
				exit(1);
			}
			q += readcnt;
		}
		close(fd);
		delete[] charbuf;
		break;
	}
	while ((p= ReadLine()) != 0)
		;
	exit(found ? 0:1);
}

//////////////////////////////////////////////////////////////////////////
//
// Extract headers

void extract_headers(int, char *[], int)
{
const char *p, *q;
std::string	b;

	catenate=1;
	while ((p=ReadLine()) && !inbody)
	{
		b.clear();
		for (q=p; *q && *q != '\n'; )
		{
		int	c= (unsigned char)*q;

			b.push_back( tolower(c) );
			if ( *q++ == ':')	break;
		}

		if (has_hdr(optx, b.c_str()))
		{
			while (*q && *q != '\n' && isspace(*q))
				q++;
			std::cout << q;
			continue;
		}

		if (has_hdr(optX, b.c_str()))
		{
			std::cout << p;
			continue;
		}
	}
	if (!std::cin.seekg(0, std::ios::end).fail())
		return;
	std::cin.clear();

	while ( ReadLine() )
		;
}
//////////////////////////////////////////////////////////////////////////
//
// Split mbox file into messages.

void split(int argc, char *argv[], int argn)
{
const char *p;
std::string	buf;
int	l;
int	do_environ=1;
unsigned long	environ=0;
unsigned	environ_len=3;
const	char *env;

	if (argn >= argc)	help();

	while ( (p=NextLine()) && *p == '\n')
		;

	signal(SIGCHLD, SIG_DFL);
	signal(SIGPIPE, SIG_IGN);
	env=getenv("FILENO");
	if (env)
	{
	const char *q;

		for (q=env; *q; q++)
			if (!isdigit(*q))	break;
		if (*q)	do_environ=0;
		else
		{
			environ_len=strlen(env);
			environ=atol(env);
		}
	}

	while (p)
	{
	int	fds[2];

		if (pipe(fds) < 0)
		{
			std::cerr << "reformail: pipe() failed." << std::endl;
			exit(1);
		}

	pid_t	pid=fork();

		if (pid == -1)
		{
			std::cerr << "reformail: fork() failed." << std::endl;
			exit(1);
		}

		if (pid == 0)
		{
			dup2(fds[0], 0);
			close(fds[0]);
			close(fds[1]);

		std::string	buf, buf2;

			if (do_environ)
			{
			char	*s;

				while (environ || environ_len)
				{
					buf.push_back( "0123456789"[environ % 10]);
					environ /= 10;
					if (environ_len)	--environ_len;
				}

				buf2="FILENO=";
				while (buf.size())
				{
					buf2.push_back(buf.back());
					buf.pop_back();
				}
				s=strdup(buf2.c_str());
				if (!s)
				{
					perror("strdup");
					exit (1);
				}
				putenv(s);
			}

			execvp( argv[argn], argv+argn);
			std::cerr << "reformail: exec() failed." << std::endl;
			exit(1);
		}
		close(fds[0]);
		environ++;

		do
		{
			buf=p;
			p=ReadLine();
			if (!p || strncmp(p, "From ", 5) == 0)
				buf.pop_back();	// Drop trailing newline
			else
			{
				if (addcrs)
				{
					buf.pop_back();
					buf.push_back('\r');
					buf.push_back('\n');
				}
			}

			const char *q=buf.c_str();

			l=buf.size();
			while (l)
			{
			int	n= ::write( fds[1], q, l);
				if (n <= 0)
				{
					std::cerr
					  << "reformail: write() failed."
					  << std::endl;
					exit(1);
				}
				q += n;
				l -= n;
			}
		} while (p && strncmp(p, "From ", 5));
		close(fds[1]);

	int	wait_stat;

		while ( wait(&wait_stat) != pid )
			;
		if (!WIFEXITED(wait_stat) || WEXITSTATUS(wait_stat))
			break;	// Rely on diagnostic from child
	}
}

//////////////////////////////////////////////////////////////////////////////

static void add_bin64(std::string &buf, unsigned long n)
{
int	i;

	for (i=0; i<16; i++)
	{
		buf.push_back( "0123456789ABCDEF"[n % 16] );
		n /= 16;
	}
}

static void add_messageid(std::string &buf)
{
	time_t	t;

	buf.push_back('<');
	time(&t);
	add_bin64(buf,t);
	buf.push_back('.');
	add_bin64(buf, getpid() );
	buf += ".reformail@";
	buf += HostName();
	buf.push_back('>');
}

static void add_opta(multibuf &buf, const char *optarg)
{
	std::string chk_buf;
	const char *c;

	chk_buf.reserve(strlen(optarg));

	for (c=optarg; *c; c++)
		chk_buf.push_back( tolower( (unsigned char)*c ));
	if (chk_buf == "message-id:" || chk_buf == "resent_message_id:")
	{
		chk_buf=optarg;
		chk_buf += " ";
		add_messageid(chk_buf);
		optarg=chk_buf.c_str();
	}

	buf.push_back(optarg);
}

int main(int argc, char *argv[])
{
int	argn, done;
const char	*optarg;
void	(*function)(int, char *[], int)=0;

#if HAVE_SETLOCALE
	setlocale(LC_ALL, "C");
#endif

	from_filter= &no_from_filter;
	append_more_headers=&ReadLineAddHeader;
	done=0;
	for (argn=1; argn<argc; argn++)
	{
		if (strcmp(argv[argn], "--") == 0 || strcmp(argv[argn],"-")==0)
		{
			++argn;
			break;
		}
		if (argv[argn][0] != '-')	break;
		optarg=argv[argn]+2;
		if (!*optarg)	optarg=0;
		switch ( argv[argn][1] )	{
		case 'd':
			if (!optarg || !*optarg)	optarg="1";
			addcrs=atoi(optarg);
			break;
		case 'c':
			catenate=1;
			break;
		case 'f':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || *optarg == '0')
				from_filter=&rem_from_filter;
			else
				from_filter=&add_from_filter;
			break;
		case 'D':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || argn+1 >= argc)	help();
			if (function)	help();
			function=cache;
			cache_maxlen=optarg;
			cache_name=argv[++argn];
			break;
		case 'a':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();
			add_opta(opta, optarg);
			break;
		case 'A':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();
			add_opta(optA, optarg);
			break;
		case 'i':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();

			opti.push_back(optarg);
			break;
		case 'I':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();
			optI.push_back(optarg);
			break;
		case 'R':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();

			optR.push_back(optarg);
			if (argn+1 >= argc)	help();
			optarg=argv[++argn];

			(*--optR.end()) += optarg;
			break;
		case 'u':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();

			optu.push_back(optarg);
			break;
		case 'U':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();

			optU.push_back(optarg);
			break;
		case 'x':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();

			optx.push_back(optarg);
			break;
		case 'X':
			if (!optarg && argn+1 < argc)	optarg=argv[++argn];
			if (!optarg || !*optarg)	help();
			if (function)	help();
			optX.push_back(optarg);
			break;
		case 's':
			if (function)	help();
			function= &split;
			++argn;
			done=1;
			break;
		default:
			help();
		}
		if (done)	break;
	}
	if (optx.size() || optX.size())
	{
		if (function)	help();
		function=extract_headers;
	}

	if (!function)	function=copy;
	(*function)(argc, argv, argn);
	std::cout.flush();
	if (std::cout.fail())
	{
		std::cerr << "reformail: error writing output." << std::endl;
		exit(1);
	}
	exit(0);
}
