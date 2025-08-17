/*
** Copyright 1998 - 2025 Double Precision, Inc.
** See COPYING for distribution information.
*/

#if	HAVE_CONFIG_H
#include	"config.h"
#endif

#include	<stdio.h>
#include	<stdlib.h>
#include	<string.h>
#include	<ctype.h>
#include	<errno.h>
#if	HAVE_UNISTD_H
#include	<unistd.h>
#endif
#include	<sys/types.h>
#include	<sys/stat.h>

#include	"imapd.h"
#include	"imaptoken.h"
#include	"imapwrite.h"
#include	"imapscanclient.h"
#include	"fetchinfo.h"
#include	"rfc822/rfc822.h"
#include	"rfc2045/rfc2045.h"
#include	"maildir/config.h"
#include	"maildir/maildirgetquota.h"
#include	"maildir/maildirquota.h"
#include	"maildir/maildiraclt.h"

#include	<algorithm>
#include	<optional>
#include	<fstream>
#include	<tuple>
#include	<functional>
#include	<fstream>

#if SMAP
extern int smapflag;
#endif

#ifndef LARGEHDR
#define LARGEHDR BUFSIZ
#endif

static const char unavailable[]=
	"\
From: System Administrator <root@localhost>\n\
Subject: message unavailable\n\n\
This message is no longer available on the server.\n";

unsigned long header_count=0, body_count=0;	/* Total transferred */

extern int current_mailbox_ro;
extern imapscaninfo current_maildir_info;

extern void snapshot_needed();

extern void msgenvelope(void (*)(const char *, size_t),
			rfc822::fdstreambuf &,
			rfc2045::entity &);
extern void msgbodystructure( void (*)(const char *, size_t), bool,
			      rfc822::fdstreambuf &, rfc2045::entity & );

extern int is_trash(const char *);
extern void get_message_flags(struct imapscanmessageinfo *,
	char *, struct imapflags *);
extern void append_flags(std::string &buf, struct imapflags &flags);

static int fetchitem(rfc822::fdstreambuf **, int *, const fetchinfo *,
		     imapscaninfo *,  unsigned long,
		     rfc2045::entity **, int *);

static void bodystructure(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *,  unsigned long,
	rfc2045::entity *);

static void body(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *,  unsigned long,
	rfc2045::entity *);

static void fetchmsgbody(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *,  unsigned long,
	rfc2045::entity *);

static void dofetchmsgbody(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *,  unsigned long,
	rfc2045::entity *);

static void envelope(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *,  unsigned long,
	rfc2045::entity *);

void doflags(rfc822::fdstreambuf *, const fetchinfo *,
	     imapscaninfo *, unsigned long, rfc2045::entity *);

static void internaldate(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long, rfc2045::entity *);

static void uid(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long, rfc2045::entity *);

static void all(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long, rfc2045::entity *);

static void fast(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long, rfc2045::entity *);

static void full(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long, rfc2045::entity *);

static void rfc822size(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long, rfc2045::entity *);

static void dofetchheadersbuf(rfc822::fdstreambuf &, const fetchinfo *,
			      imapscaninfo *, unsigned long,
			      rfc2045::entity &,
			      int (*)(const fetchinfo *fi, const char *));

static void dofetchheadersfile(rfc822::fdstreambuf &, const fetchinfo *,
			       imapscaninfo *, unsigned long,
			       rfc2045::entity &,
			       int (*)(const fetchinfo *fi, const char *));

static void print_bodysection_partial(const fetchinfo *,
				      void (*)(const std::string &));
static void print_bodysection_output(const std::string &);

static int dofetchheaderfields(const fetchinfo *, const char *);
static int dofetchheadernotfields(const fetchinfo *, const char *);
static int dofetchheadermime(const fetchinfo *, const char *);

static void rfc822main(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long,
	rfc2045::entity *);

static void rfc822header(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long,
	rfc2045::entity *);

static void rfc822text(rfc822::fdstreambuf *, const fetchinfo *,
	imapscaninfo *, unsigned long,
	rfc2045::entity *);

rfc2045::entity *fetch_alloc_rfc2045(unsigned long msgnum, rfc822::fdstreambuf &);
rfc822::fdstreambuf &open_cached_fp(unsigned long);

void fetchflags(unsigned long);

static void fetcherrorprt(const std::string &p)
{
	fprintf(stderr, "%s", p.c_str());
}

static void fetcherror(const char *errmsg,
		const fetchinfo *fi,
		imapscaninfo *info, unsigned long j)
{
	imapscanmessageinfo &mi=info->msgs.at(j);

	fprintf(stderr, "IMAP FETCH ERROR: %s, uid=%u, filename=%s: %s",
		errmsg, (unsigned)getuid(), mi.filename.c_str(),
		fi->name.c_str());
	if (fi->hasbodysection)
		print_bodysection_partial(fi, &fetcherrorprt);
	fprintf(stderr, "\n");
}

std::string get_reflagged_filename(std::string fn, struct imapflags &newflags)
{
	size_t n=fn.rfind(MDIRSEP[0]);

	if (n != fn.npos)
		fn.resize(n);

	fn += MDIRSEP "2,";
	append_flags(fn, newflags);
	return fn;
}

int reflag_filename(struct imapscanmessageinfo *mi, struct imapflags *flags,
	int fd)
{
	int	rc=0;
	struct	imapflags old_flags;
	struct	stat	stat_buf;

	get_message_flags(mi, 0, &old_flags);

	auto p=get_reflagged_filename(mi->filename, *flags);
	std::string q=current_maildir_info.current_mailbox;
	q += "/cur/";
	q += mi->filename;

	std::string r=current_maildir_info.current_mailbox;

	r += "/cur/";
	r += p;

	if (q != r)
	{
		if (maildirquota_countfolder(
			    current_maildir_info.current_mailbox.c_str()
		    ) && old_flags.deleted != flags->deleted
		    && fstat(fd, &stat_buf) == 0)
		{
			struct maildirsize quotainfo;
			int64_t	nbytes;
			unsigned long unbytes;
			int	nmsgs=1;

			if (maildir::parsequota(mi->filename, unbytes))
				nbytes=unbytes;
			else
				nbytes=stat_buf.st_size;
			if ( flags->deleted )
			{
				nbytes= -nbytes;
				nmsgs= -nmsgs;
			}

			if ( maildir_quota_delundel_start(
				     current_maildir_info.current_mailbox
				     .c_str(),
				     &quotainfo,
				     nbytes, nmsgs))
				rc= -1;
			else
				maildir_quota_delundel_end(&quotainfo,
							   nbytes, nmsgs);
		}

		if (rc == 0)
			rename(q.c_str(), r.c_str());

#if SMAP
		snapshot_needed();
#endif
	}
	mi->filename=p;

#if 0
	if (is_sharedsubdir(current_mailbox))
		maildir_shared_updateflags(current_mailbox, p);
#endif

	return (rc);
}

int do_fetch(unsigned long n, int byuid, const std::list<fetchinfo> &filist)
{
	rfc822::fdstreambuf *fds=nullptr;
	rfc2045::entity *rfc2045e=nullptr;
	int	seen;
	int	open_err;
	int	unicode_err=0;
	int	report_unicode_err=0;

	open_err=0;

	writes("* ");
	writen(n);
	writes(" FETCH (");

	if (byuid)
	{

		if (std::find_if(
			    filist.begin(), filist.end(),
			    [&]
			    (auto &fip)
			    {
				    return fip.name == "UID";
			    })
		    == filist.end())
		{
			writes("UID ");
			writen(current_maildir_info.msgs[n-1].uid);
			writes(" ");
		}
	}
	seen=0;

	const char *sep="";

	for (auto &fi:filist)
	{
		writes(sep);
		int rc=fetchitem(&fds, &open_err,
				 &fi, &current_maildir_info, n-1,
				 &rfc2045e, &unicode_err);

		if (rc > 0)
			seen=1;

		sep=" ";
	}
	writes(")\r\n");

	if (open_err)
	{
		writes("* NO [ALERT] Cannot open message ");
		writen(n);
		writes("\r\n");
		return (0);
	}

#if SMAP
	if (!smapflag)
#endif
		if (!current_maildir_info.has_acl(ACL_SEEN[0]))
			seen=0; /* No permissions */

	if (seen && !current_mailbox_ro)
	{
	struct	imapflags	flags;

		get_message_flags(&current_maildir_info.msgs.at(n-1),
				0, &flags);
		if (!flags.seen)
		{
			flags.seen=true;
			reflag_filename(&current_maildir_info.msgs[n-1],&flags,
					fds->fileno());
			current_maildir_info.msgs[n-1].changedflags=1;

			report_unicode_err=unicode_err;
		}
	}

	if (report_unicode_err)
	{
		writes("* OK [ALERT] Message ");
		writen(n);
		writes(" appears to be a Unicode message and your"
		       " E-mail reader did not enable Unicode support."
		       " Please use an E-mail reader that supports"
		       " IMAP with UTF-8 (see"
		       " https://tools.ietf.org/html/rfc6855.html)\r\n");
	}

	if (current_maildir_info.msgs[n-1].changedflags)
		fetchflags(n-1);
	return (0);
}

static int fetchitem(rfc822::fdstreambuf **fds,
		     int *open_err, const fetchinfo *fi,
		     imapscaninfo *i, unsigned long msgnum,
		     rfc2045::entity **mimee,
		     int *unicode_err)
{
	void (*fetchfunc)(rfc822::fdstreambuf *,
			  const fetchinfo *,
			  imapscaninfo *, unsigned long,
			  rfc2045::entity *);
	bool	parsemime=false;
	int	rc=0;
	bool	do_open=true;
	bool	mimecorrectness=false;

	if (fi->name == "ALL")
	{
		parsemime=true;
		fetchfunc= &all;
	}
	else if (fi->name == "BODYSTRUCTURE")
	{
		parsemime=true;
		fetchfunc= &bodystructure;
	}
	else if (fi->name == "BODY")
	{
		parsemime=true;
		fetchfunc= &body;
		if (fi->hasbodysection)
		{
			fetchfunc= &fetchmsgbody;
			mimecorrectness=true;
			rc=1;
		}
	}
	else if (fi->name == "BODY.PEEK")
	{
		parsemime=true;
		mimecorrectness=true;
		fetchfunc= &body;
		if (fi->hasbodysection)
		{
			fetchfunc= &fetchmsgbody;
			mimecorrectness=true;
		}
	}
	else if (fi->name == "ENVELOPE")
	{
		parsemime=true;
		fetchfunc= &envelope;
	}
	else if (fi->name == "FAST")
	{
		parsemime=true;
		fetchfunc= &fast;
	}
	else if (fi->name == "FULL")
	{
		parsemime=true;
		fetchfunc= &full;
	}
	else if (fi->name == "FLAGS")
	{
		fetchfunc= &doflags;
		do_open=false;
	}
	else if (fi->name == "INTERNALDATE")
	{
		fetchfunc= &internaldate;
	}
	else if (fi->name == "RFC822")
	{
		parsemime=true;
		fetchfunc= &rfc822main;
		mimecorrectness=true;
		rc=1;
	}
	else if (fi->name == "RFC822.HEADER")
	{
		parsemime=true;
		fetchfunc= &rfc822header;
		mimecorrectness=true;
	}
	else if (fi->name == "RFC822.SIZE")
	{
		parsemime=true;
		fetchfunc= &rfc822size;
	}
	else if (fi->name == "RFC822.TEXT")
	{
		parsemime=true;
		mimecorrectness=true;
		fetchfunc= &rfc822text;
	}
	else if (fi->name == "UID")
	{
		fetchfunc= &uid;
		do_open=false;
	}
	else	return (0);

	if (do_open && *fds == nullptr)
	{
		*fds = &open_cached_fp(msgnum);
		if ((*fds)->fileno() < 0)
		{
			*fds=nullptr;
			*open_err=1;
			return rc;
		}
	}

	if (mimecorrectness && !enabled_utf8)
		parsemime=true;

	if (parsemime && !*mimee)
	{
		*mimee=fetch_alloc_rfc2045(msgnum, **fds);
	}

	if (mimecorrectness && !enabled_utf8 &&
	    ((*mimee)->all_errors() & RFC2045_ERR8BITHEADER))
	{
		*unicode_err=1;
	}

	(*fetchfunc)(*fds, fi, i, msgnum, *mimee);
	return (rc);
}

static void bodystructure(rfc822::fdstreambuf *fds,
			  const fetchinfo *fi,
			  imapscaninfo *i, unsigned long msgnum,
			  rfc2045::entity *message)
{
	writes("BODYSTRUCTURE ");
	msgbodystructure(writemem, true, *fds, *message);
}

static void body(rfc822::fdstreambuf *fds, const fetchinfo *fi,
		 imapscaninfo *i, unsigned long msgnum,
		 rfc2045::entity *message)
{
	writes("BODY ");
	msgbodystructure(writemem, false, *fds, *message);
}

static void envelope(rfc822::fdstreambuf *fds,
		     const fetchinfo *fi,
		     imapscaninfo *i, unsigned long msgnum,
		     rfc2045::entity *message)
{
	writes("ENVELOPE ");
	msgenvelope( &writemem, *fds, *message);
}

void fetchflags(unsigned long n)
{
#if SMAP
	if (smapflag)
	{
		writes("* FETCH ");
		writen(n+1);
	}
	else
#endif
	{
		writes("* ");
		writen(n+1);
		writes(" FETCH (");
	}

	doflags(nullptr, nullptr, &current_maildir_info, n,
		nullptr);

#if SMAP
	if (smapflag)
	{
		writes("\n");
	}
	else
#endif
		writes(")\r\n");
}

void fetchflags_byuid(unsigned long n)
{
	writes("* ");
	writen(n+1);
	writes(" FETCH (");
	uid(nullptr, nullptr, &current_maildir_info, n,
	    nullptr);
	writes(" ");
	doflags(nullptr, nullptr, &current_maildir_info, n,
		nullptr);
	writes(")\r\n");
}

void doflags(rfc822::fdstreambuf *fds, const fetchinfo *fi,
	     imapscaninfo *i, unsigned long msgnum,
	     rfc2045::entity *)
{
	char	buf[256];

#if SMAP
	if (smapflag)
	{
		writes(" FLAGS=");
		get_message_flags(&i->msgs.at(msgnum), buf, 0);
		writes(buf);
	}
	else
#endif
	{
		writes("FLAGS ");

		get_message_flags(&i->msgs.at(msgnum), buf, 0);

		writes("(");
		writes(buf);

		if (buf[0])
			strcpy(buf, " ");

		i->msgs.at(msgnum).keywords.enumerate(
			[&]
			(const std::string &kw)
			{
				writes(buf);
				strcpy(buf, " ");
				writes(kw.c_str());
			});
		writes(")");
	}

	i->msgs.at(msgnum).changedflags=0;
}

static void internaldate(rfc822::fdstreambuf *fds,
			 const fetchinfo *fi,
			 imapscaninfo *i, unsigned long msgnum,
			 rfc2045::entity *message)
{
struct	stat	stat_buf;
char	buf[256];
char	*p, *q;

	writes("INTERNALDATE ");
	if (fstat(fds->fileno(), &stat_buf) == 0)
	{
		rfc822_mkdate_buf(stat_buf.st_mtime, buf);

		/* Convert RFC822 date to imap date */

		p=strchr(buf, ',');
		if (p)	++p;
		else	p=buf;
		while (*p == ' ')	++p;
		if ((q=strchr(p, ' ')) != 0)	*q++='-';
		if ((q=strchr(p, ' ')) != 0)	*q++='-';
		writes("\"");
		writes(p);
		writes("\"");
	}
	else
		writes("NIL");
}

static void uid(rfc822::fdstreambuf *fds, const fetchinfo *fi,
		imapscaninfo *i, unsigned long msgnum,
		rfc2045::entity *message)
{
	writes("UID ");
	writen(i->msgs.at(msgnum).uid);
}

static void rfc822size(rfc822::fdstreambuf *fds,
		       const fetchinfo *fi,
		       imapscaninfo *i, unsigned long msgnum,
		       rfc2045::entity *message)
{
	writes("RFC822.SIZE ");
	writen(message->rfc822_size());
}

static void all(rfc822::fdstreambuf *fds, const fetchinfo *fi,
		imapscaninfo *i, unsigned long msgnum,
		rfc2045::entity *message)
{
	doflags(fds, fi, i, msgnum, message);
	writes(" ");
	internaldate(fds, fi, i, msgnum, message);
	writes(" ");
	rfc822size(fds, fi, i, msgnum, message);
	writes(" ");
	envelope(fds, fi, i, msgnum, message);
}

static void fast(rfc822::fdstreambuf *fds, const fetchinfo *fi,
	imapscaninfo *i, unsigned long msgnum,
		 rfc2045::entity *message)
{
	doflags(fds, fi, i, msgnum, message);
	writes(" ");
	internaldate(fds, fi, i, msgnum, message);
	writes(" ");
	rfc822size(fds, fi, i, msgnum, message);
}

static void full(rfc822::fdstreambuf *fds, const fetchinfo *fi,
		 imapscaninfo *i, unsigned long msgnum,
		 rfc2045::entity *message)
{
	doflags(fds, fi, i, msgnum, message);
	writes(" ");
	internaldate(fds, fi, i, msgnum, message);
	writes(" ");
	rfc822size(fds, fi, i, msgnum, message);
	writes(" ");
	envelope(fds, fi, i, msgnum, message);
	writes(" ");
	body(fds, fi, i, msgnum, message);
}

static void fetchmsgbody(rfc822::fdstreambuf *fds,
			 const fetchinfo *fi,
			 imapscaninfo *i, unsigned long msgnum,
			 rfc2045::entity *message)
{
	writes("BODY");
	print_bodysection_partial(fi, &print_bodysection_output);
	writes(" ");
	dofetchmsgbody(fds, fi, i, msgnum, message);
}

static void print_bodysection_output(const std::string &p)
{
	writes(p.c_str());
}

static void print_bodysection_partial(const fetchinfo *fi,
				      void (*func)(const std::string &))
{
	(*func)("[");
	if (fi->hasbodysection)
	{
		(*func)(fi->bodysection);
		if (!fi->bodysublist.empty())
		{
			const char	*p=" (";

			for (auto &subl:fi->bodysublist)
			{
				(*func)(p);
				p=" ";
				(*func)("\"");
				(*func)(subl.name);
				(*func)("\"");
			}
			(*func)(")");
		}
	}
	(*func)("]");
	if (fi->ispartial)
	{
	char	buf[80];

		sprintf(buf, "<%lu>", (unsigned long)fi->partialstart);
		(*func)(buf);
	}
}

static void dofetchmsgbody(rfc822::fdstreambuf *fds,
			   const fetchinfo *fi,
			   imapscaninfo *i, unsigned long msgnum,
			   rfc2045::entity *message)
{
	const char *p=fi->hasbodysection ? fi->bodysection.c_str():nullptr;
	unsigned long cnt;
	char	buf[BUFSIZ];
	char	rbuf[BUFSIZ];
	char	*rbufptr;
	int	rbufleft;
	unsigned long bufptr;
	unsigned long skipping;
	bool	ismsgrfc822=true;

	off_t start_seek_pos;
	rfc2045::entity *headermessage;

/*
** To optimize consecutive FETCHes, we cache our virtual and physical
** position.  What we do is that on the first fetch we count off the
** characters we read, and keep track of both the physical and the CRLF-based
** offset into the message.  Then, on subsequent FETCHes, we attempt to
** use that information.
*/

off_t cnt_virtual_chars;
off_t cnt_phys_chars;

off_t cache_virtual_chars;
off_t cache_phys_chars;

	headermessage=message;

	while (p && isdigit((int)(unsigned char)*p))
	{
		unsigned long n=0;

		headermessage=message;;

		do
		{
			n=n*10 + (*p++ - '0');
		} while (isdigit((int)(unsigned char)*p));

		if (message)
		{
			if (ismsgrfc822)
			{
				if (message->subentities.empty())
				{
					/* Not a multipart, n must be 1 */
					if (n != 1)
						message=nullptr;
					if (*p == '.')
						++p;
					continue;
				}
				ismsgrfc822=false;

				if (rfc2045_message_content_type(
					    message->content_type.value.c_str()
				    ))
					ismsgrfc822=true;
				/* The content is another message/rfc822 */
			}

			message=n > 0 && n <= message->subentities.size()
				? &message->subentities[n-1]:nullptr;
			headermessage=message;

			if (message && message->subentities.size() == 1 &&
			    rfc2045_message_content_type(
				    message->content_type.value.c_str()
			    ))
			{
				/* This is a message/rfc822 part */

				if (!*p)
					break;

				message=&message->subentities[0];
				ismsgrfc822=true;
			}
		}
		if (*p == '.')
			++p;
	}

	if (p && strcmp(p, "MIME") == 0)
		message=headermessage;

	if (!message)
	{
		writes("{0}\r\n");
		return;
	}

	if (p && strcmp(p, "TEXT") == 0)
	{
		start_seek_pos=message->startbody;
		cnt=message->text_size();
	}
	else if (p && strcmp(p, "HEADER") == 0)
	{
		start_seek_pos=message->startpos;
		cnt= message->startbody - message->startpos +
			(message->nlines - message->nbodylines);
	}
	else if (p && strcmp(p, "HEADER.FIELDS") == 0)
	{
		if (message->startbody - message->startpos <= LARGEHDR)
			dofetchheadersbuf(*fds, fi, i, msgnum, *message,
				&dofetchheaderfields);
		else
			dofetchheadersfile(*fds, fi, i, msgnum, *message,
				&dofetchheaderfields);
		return;
	}
	else if (p && strcmp(p, "HEADER.FIELDS.NOT") == 0)
	{
		if (message->startbody - message->startpos <= LARGEHDR)
			dofetchheadersbuf(*fds, fi, i, msgnum, *message,
				&dofetchheadernotfields);
		else
			dofetchheadersfile(*fds, fi, i, msgnum, *message,
				&dofetchheadernotfields);
		return;
	}
	else if (p && strcmp(p, "MIME") == 0)
	{
		if (message->startbody - message->startpos <= LARGEHDR)
			dofetchheadersbuf(*fds, fi, i, msgnum, *message,
				&dofetchheadermime);
		else
			dofetchheadersfile(*fds, fi, i, msgnum, *message,
				&dofetchheadermime);
		return;
	}
	else if (fi->bodysection.empty())
	{
		start_seek_pos=message->startpos;
		cnt=message->rfc822_size();
	}
	else	/* Last possibility: entire body */
	{
		start_seek_pos=message->startbody;
		cnt=message->text_size();
	}

	skipping=0;
	if (fi->ispartial)
	{
		skipping=fi->partialstart;
		if (skipping > cnt)	skipping=cnt;
		cnt -= skipping;
		if (fi->ispartial > 1 && cnt > fi->partialend)
			cnt=fi->partialend;
	}

	if (get_cached_offsets(start_seek_pos, &cnt_virtual_chars,
			       &cnt_phys_chars) == 0 &&
	    cnt_virtual_chars <= (off_t)skipping) /* Yeah - cache it, baby! */
	{
		if (fds->pubseekpos(start_seek_pos+cnt_phys_chars) !=
		    start_seek_pos+cnt_phys_chars)
		{
			writes("{0}\r\n");
			fetcherror("fseek", fi, i, msgnum);
			return;
		}
		skipping -= cnt_virtual_chars;
	}
	else
	{
		if (fds->pubseekpos(start_seek_pos) != start_seek_pos)
		{
			writes("{0}\r\n");
			fetcherror("fseek", fi, i, msgnum);
			return;
		}

		cnt_virtual_chars=0;
		cnt_phys_chars=0;
	}

	cache_virtual_chars=cnt_virtual_chars;
	cache_phys_chars=cnt_phys_chars;

	writes("{");
	writen(cnt);
	writes("}\r\n");
	bufptr=0;
	writeflush();

	rbufptr=0;
	rbufleft=0;

	while (cnt)
	{
	int	c;

		if (!rbufleft)
		{
			rbufleft=fds->sgetn(rbuf, sizeof(rbuf));
			if (rbufleft < 0)	rbufleft=0;
			rbufptr=rbuf;
		}

		if (!rbufleft)
		{
			fetcherror("unexpected EOF", fi, i, msgnum);
			_exit(1);
		}

		--rbufleft;
		c=(int)(unsigned char)*rbufptr++;
		++cnt_phys_chars;

		if (c == '\n')
		{
			++cnt_virtual_chars;

			if (skipping)
				--skipping;
			else
			{
				if (bufptr >= sizeof(buf))
				{
					writemem(buf, sizeof(buf));
					bufptr=0;
					/*writeflush();*/
				}
				buf[bufptr++]='\r';
				--cnt;

				if (cnt == 0)
					break;
			}
		}

		++cnt_virtual_chars;
		if (skipping)
			--skipping;
		else
		{
			++body_count;

			if (bufptr >= sizeof(buf))
			{
				writemem(buf, sizeof(buf));
				bufptr=0;
				/*writeflush();*/
			}
			buf[bufptr++]=c;
			--cnt;
		}
		cache_virtual_chars=cnt_virtual_chars;
		cache_phys_chars=cnt_phys_chars;
	}
	writemem(buf, bufptr);
	writeflush();
	save_cached_offsets(start_seek_pos, cache_virtual_chars,
			    cache_phys_chars);
}

static int dofetchheaderfields(const fetchinfo *fi, const char *name)
{
	for (auto &subitem:fi->bodysublist)
	{
		int	i, a, b;

		if (subitem.name.empty())	continue;
		for (i=0; subitem.name[i] && name[i]; i++)
		{
			a=(unsigned char)name[i];
			a=toupper(a);
			b=subitem.name[i];
			b=toupper(b);
			if (a != b)	break;
		}
		if (subitem.name[i] == 0 && name[i] == 0)	return (1);
	}

	return (0);
}

static int dofetchheadernotfields(const fetchinfo *fi, const char *name)
{
	return (!dofetchheaderfields(fi, name));
}

static int dofetchheadermime(const fetchinfo *fi, const char *name)
{
	size_t i;
	int	a;
	static const char mv[]="MIME-VERSION";

	for (i=0; i<sizeof(mv)-1; i++)
	{
		a= (unsigned char)name[i];
		a=toupper(a);
		if (a != mv[i])	break;
	}
	if (mv[i] == 0 && name[i] == 0)	return (1);

	for (i=0; i<8; i++)
	{
		a= (unsigned char)name[i];
		a=toupper(a);
		if (a != "CONTENT-"[i])	return (0);
	}
	return (1);
}

static void dofetchheadersbuf(
	rfc822::fdstreambuf &src, const fetchinfo *fi,
	imapscaninfo *info, unsigned long msgnum,
	rfc2045::entity &message,
	int (*headerfunc)(const fetchinfo *fi, const char *))
{
	std::string buf;

	buf.reserve(LARGEHDR+2);

	rfc2045::entity::line_iter<false>::headers headers{message, src};

	headers.name_lc=false;
	headers.keep_eol=true;

	do
	{
		const auto &[name, last_line_is_empty]=
			headers.convert_name_check_empty();

		if (headerfunc(fi, name.c_str()) && !last_line_is_empty)
		{
			auto h=headers.current_header();

			buf.insert(buf.end(), h.begin(), h.end());
		}
	} while (headers.next());

	if (src.fileno() < 0) // There was an error
	{
		writes("{0}\r\n");
		fetcherror("fseek", fi, info, msgnum);
		return;
	}

	buf.push_back('\n'); /* Always append a blank line */

	size_t cnt=buf.size();

	for (char c:buf)
		if (c == '\n')	++cnt;

	size_t skipping=0;

	if (fi->ispartial)
	{
		skipping=fi->partialstart;
		if (skipping > cnt)	skipping=cnt;
		cnt -= skipping;
		if (fi->ispartial > 1 && cnt > fi->partialend)
			cnt=fi->partialend;
	}

	writes("{");
	writen(cnt);
	writes("}\r\n");
	auto p=buf.c_str();

	while (skipping)
	{
		if (*p == '\n')
		{
			--skipping;
			if (skipping == 0)
			{
				if (cnt)
				{
					writes("\n");
					--cnt;
				}
				break;
			}
		}
		--skipping;
		++p;
	}

	while (cnt)
	{
		if (*p == '\n')
		{
			writes("\r");
			if (--cnt == 0)	break;
			writes("\n");
			--cnt;
			++p;
			continue;
		}

		size_t i;
		for (i=0; i<cnt; i++)
			if (p[i] == '\n')
				break;
		writemem(p, i);
		p += i;
		cnt -= i;
		header_count += i;
	}
}

struct fetchheaderinfo {
	unsigned long skipping;
	unsigned long cnt;
	} ;

static void countheader(struct fetchheaderinfo *, const char *, size_t);

static void printheader(struct fetchheaderinfo *, const char *, size_t);

static void dofetchheadersfile(
	rfc822::fdstreambuf &src, const fetchinfo *fi,
	imapscaninfo *info, unsigned long msgnum,
	rfc2045::entity &message,
	int (*headerfunc)(const fetchinfo *fi, const char *))
{
	fetchheaderinfo finfo;

	finfo.cnt=0;
	for (int pass=0; pass<2; pass++)
	{
		void (*func)(struct fetchheaderinfo *, const char *, size_t)=
			pass ? printheader:countheader;

		if (pass)
		{
			finfo.skipping=0;
			if (fi->ispartial)
			{
				finfo.skipping=fi->partialstart;
				if (finfo.skipping > finfo.cnt)
					finfo.skipping=finfo.cnt;
				finfo.cnt -= finfo.skipping;
				if (fi->ispartial > 1 &&
					finfo.cnt > fi->partialend)
					finfo.cnt=fi->partialend;
			}

			writes("{");
			writen(finfo.cnt+2);	/* BUG */
			writes("}\r\n");
		}

		rfc2045::entity::line_iter<false>::headers
			headers{message, src};

		headers.name_lc=false;
		headers.keep_eol=true;

		do
		{
			const auto &[name, last_line_is_empty]=
				headers.convert_name_check_empty();

			if (headerfunc(fi, name.c_str()) &&
			    !last_line_is_empty)
			{
				auto h=headers.current_header();

				std::string crlf;

				crlf.reserve(h.size()+40);

				for (char c:h)
				{
					if (c == '\n')
						crlf.push_back('\r');
					crlf.push_back(c);
				}

				(*func)(&finfo, crlf.c_str(), crlf.size());

				if (pass && finfo.cnt == 0)	break;
			}
		} while (headers.next());

		if (pass && finfo.cnt)
		{
			fetcherror("unexpected EOF", fi, info, msgnum);
			_exit(1);
		}
	}
	writes("\r\n");	/* BUG */
}

static void countheader(struct fetchheaderinfo *fi, const char *p, size_t s)
{
	fi->cnt += s;
}

static void printheader(struct fetchheaderinfo *fi, const char *p, size_t s)
{
	size_t i;

	if (fi->skipping)
	{
		if (fi->skipping > s)
		{
			fi->skipping -= s;
			return;
		}
		p += fi->skipping;
		s -= fi->skipping;
		fi->skipping=0;
	}
	if (s > fi->cnt)	s=fi->cnt;
	for (i=0; i <= s; i++)
		if (p[i] != '\r')
			++header_count;
	writemem(p, s);
	fi->cnt -= s;
}

static void rfc822common(rfc822::fdstreambuf &fds,
			   const fetchinfo *fi,
			   imapscaninfo *info,
			   unsigned long msgnum,
			   const char *resp,
			   size_t start,
			   size_t n);

static void rfc822main(rfc822::fdstreambuf *fds,
		       const fetchinfo *fi,
		       imapscaninfo *info, unsigned long msgnum,
		       rfc2045::entity *message)
{
	rfc822common(*fds, fi, info, msgnum,
		     "RFC822 ", 0, message->rfc822_size());
}


static void rfc822header(rfc822::fdstreambuf *fds,
			 const fetchinfo *fi,
			 imapscaninfo *info, unsigned long msgnum,
			 rfc2045::entity *message)
{
	auto n=message->rfc822_size()-message->text_size();

	rfc822common(*fds, fi, info, msgnum,
		     "RFC822.HEADER ", 0, n);
}

static void rfc822text(rfc822::fdstreambuf *fds,
		       const fetchinfo *fi,
		       imapscaninfo *info, unsigned long msgnum,
		       rfc2045::entity *message)
{
	rfc822common(*fds, fi, info, msgnum,
		     "RFC822.TEXT ", message->startbody,
		     message->text_size());
}

static void rfc822common(rfc822::fdstreambuf &fds,
			 const fetchinfo *fi,
			 imapscaninfo *info,
			 unsigned long msgnum,
			 const char *resp,
			 size_t pos,
			 size_t n)
{
	char	buf[BUFSIZ];

	if (static_cast<size_t>(fds.pubseekpos(pos)) != pos)
	{
		writes("{0}\r\n");
		fetcherror("fseek", fi, info, msgnum);
		return;
	}

	writes(resp);

	writes("{");
	writen(n);
	writes("}\r\n");

	size_t i=0;

	while (n)
	{
		auto c=fds.sbumpc();
		if (c == '\n')
		{
			if (i >= sizeof(buf))
			{
				writemem(buf, i);
				i=0;
			}
			buf[i++]='\r';
			if (--n == 0)	break;
		}

		if (i >= sizeof(buf))
		{
			writemem(buf, i);
			i=0;
		}
		buf[i++]=c;
		--n;
	}
	writemem(buf, i);
}

/*
** Poorly written IMAP clients (read: Netscape Messenger) like to issue
** consecutive partial fetches for downloading large messages.
**
** To save the time of reparsing the MIME structure, we cache it.
*/

static struct rfc2045 *cached_rfc2045p;
static std::string cached_filename;

static std::optional<rfc2045::entity> cached_rfc2045_entity;
static std::string cached_rfc2045_filename;

void fetch_free_cached()
{
	if (cached_rfc2045p)
	{
		rfc2045_free(cached_rfc2045p);
		cached_rfc2045p=0;
		cached_filename.clear();
	}
}

void fetch_free_cachedentity()
{
	cached_rfc2045_entity.reset();
	cached_rfc2045_filename.clear();
}

rfc2045::entity *fetch_alloc_rfc2045(unsigned long msgnum,
				     rfc822::fdstreambuf &fds)
{
	if (cached_rfc2045_entity &&
	    cached_rfc2045_filename ==
	    current_maildir_info.msgs.at(msgnum).filename)
		return &cached_rfc2045_entity.value();

	fetch_free_cachedentity();

	cached_rfc2045_filename=current_maildir_info.msgs.at(msgnum).filename;

	if (fds.pubseekpos(0) != 0)
	{
		write_error_exit(0);
		return (0);
	}

	std::istreambuf_iterator<char> b{&fds}, e;
	rfc2045::entity::line_iter<false>::iter parser{b, e};

	auto &message=cached_rfc2045_entity.emplace();
	message.parse(parser);

	return (&message);
}

static rfc822::fdstreambuf cached_fdstreambuf;

static std::string cached_fp_filename;
static off_t cached_base_offset;
static off_t cached_virtual_offset;
static off_t cached_phys_offset;

rfc822::fdstreambuf &open_cached_fp(unsigned long msgnum)
{
	if (cached_fdstreambuf.fileno() >= 0 && cached_fp_filename ==
	    current_maildir_info.msgs.at(msgnum).filename)
		return cached_fdstreambuf;

	cached_fdstreambuf=rfc822::fdstreambuf{};
	cached_fp_filename.clear();

	int fd=imapscan_openfile(&current_maildir_info, msgnum);
	if (fd < 0)
	{
		FILE *cached_fp=nullptr;

		if (fd <0 && errno == ENOENT && (cached_fp=tmpfile()) != 0)
		{
			fprintf(cached_fp, unavailable);
			if (fseek(cached_fp, 0L, SEEK_SET) < 0 ||
			    ferror(cached_fp))
			{
				fclose(cached_fp);
				cached_fp=nullptr;
			}
			else
			{
				int fd2=dup(fileno(cached_fp));

				if (fd2 < 0)
				{
					fclose(cached_fp);
					cached_fp=nullptr;
				}
				else
				{
					cached_fdstreambuf=
						rfc822::fdstreambuf{fd2};
				}
			}
		}

		if (cached_fp == 0)
		{
			fprintf(stderr, "ERR: %s: %s\n",
				getenv("AUTHENTICATED"),
#if	HAVE_STRERROR
				strerror(errno)
#else
				"error"
#endif

				);
			fflush(stderr);
			_exit(1);
		}
		else
		{
			fclose(cached_fp);
		}
	}
	else
	{
		cached_fdstreambuf=
			rfc822::fdstreambuf{fd};
	}
	cached_fp_filename=current_maildir_info.msgs.at(msgnum).filename;

	cached_base_offset=0;
	cached_virtual_offset=0;
	cached_phys_offset=0;
	return cached_fdstreambuf;
}

void fetch_free_cache()
{
	cached_fdstreambuf=rfc822::fdstreambuf{};
	cached_fp_filename.clear();
}

void save_cached_offsets(off_t base, off_t virt, off_t phys)
{
	cached_base_offset=base;
	cached_virtual_offset=virt;
	cached_phys_offset=phys;
}

int get_cached_offsets(off_t base, off_t *virt, off_t *phys)
{
	if (cached_fdstreambuf.fileno() < 0)
		return (-1);
	if (base != cached_base_offset)
		return (-1);

	*virt=cached_virtual_offset;
	*phys=cached_phys_offset;
	return (0);
}
