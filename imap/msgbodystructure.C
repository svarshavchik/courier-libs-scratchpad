/*
** Copyright 1998 - 2001 Double Precision, Inc.
** See COPYING for distribution information.
*/

#if	HAVE_CONFIG_H
#include	"config.h"
#endif
#include	"imaptoken.h"
#include	"imapwrite.h"
#include	"rfc822/rfc822.h"
#include	"rfc2045/rfc2045.h"
#include	<stdio.h>
#include	<ctype.h>
#include	<stdlib.h>
#include	<string.h>

#include <string>
#include <algorithm>

extern void msgenvelope(void (*)(const char *, size_t),
			rfc822::fdstreambuf &,
			rfc2045::entity &);

extern void msgappends(void (*)(const char *, size_t), const char *, size_t);

static void do_param_list(void (*writefunc)(const char *, size_t),
			  const rfc2045::entity::rfc2231_header &header)
{
	if (header.parameters.empty())
	{
		(*writefunc)("NIL", 3);
		return;
	}

	std::vector<decltype(header.parameters)::const_iterator> parameters;

	parameters.reserve(header.parameters.size());

	for (auto b=header.parameters.begin(),
		     e=header.parameters.end();
	     b != e; ++b)
		parameters.push_back(b);

	std::sort(parameters.begin(), parameters.end(),
		  []
		  (const auto &a, const auto &b)
		  {
			  return a->first < b->first;
		  });

	const char *p="(";
	for (auto parameter:parameters)
	{
		(*writefunc)(p, strlen(p));
		(*writefunc)("\"", 1);
		if (!parameter->first.empty())
			msgappends(writefunc, parameter->first.c_str(),
				   parameter->first.size());

		(*writefunc)("\" \"", 3);

		auto value=parameter->second.value_in_charset(unicode::utf_8);

		if (!value.empty())
		{
#if	IMAP_CLIENT_BUGS

			/* NETSCAPE */

			std::string u=value;

			u.erase(std::remove(u.begin(), u.end(), '\\'),
				u.end());

			msgappends(writefunc, u.c_str(), u.size());
#else
			msgappends(writefunc, value.c_str(), value.size());
#endif
		}
		(*writefunc)("\"", 1);
		p=" ";
	}

	(*writefunc)(")", 1);
}

static void contentstr( void (*writefunc)(const char *, size_t),
			const std::string &s)
{
	if (s.empty())
	{
		(*writefunc)("NIL", 3);
		return;
	}

	(*writefunc)("\"", 1);
	msgappends(writefunc, s.c_str(), s.size());
	(*writefunc)("\"", 1);
}


static void do_disposition(
	void (*writefunc)(const char *, size_t),
	rfc2045::entity::rfc2231_header content_disposition
)
{
	if (content_disposition.value.empty())
	{
		(*writefunc)("NIL", 3);
		return;
	}
	(*writefunc)("(\"", 1);

	if (!content_disposition.value.empty())
	{
		(*writefunc)("\"", 1);
		msgappends(writefunc, content_disposition.value.c_str(),
			   content_disposition.value.size());
		(*writefunc)("\"", 1);
	}
	else
		(*writefunc)("\"\"", 2);

	(*writefunc)(" ", 1);
	do_param_list(writefunc, content_disposition);
	(*writefunc)(")", 1);
}

static void do_content_language(
	void (*writefunc)(const char *, size_t),
	const std::string &content_language
)
{
	std::vector<std::string_view> languages;

	for (auto b=content_language.begin(),
		     e=content_language.end();

	     (b=std::find_if(b, e,
			     []
			     (char c)
			     {
				     return c != ' ' && c != '\t' &&
					     c != '\r' &&
					     c != '\n' && c != ',';
			     })) != e; )
	{
		auto p=b;

		b=std::find_if(b, e,
			       []
			       (char c)
			       {
				       return c == ' ' || c == '\t' ||
					       c == '\r' ||
					       c == '\n' || c == ',';
			       });

		languages.emplace_back(&*p, b-p);
	}

	if (languages.empty())
	{
		writefunc("NIL", 3);
		return;
	}

	if (languages.size() == 1)
	{
		writefunc("\"", 1);
		msgappends(writefunc, languages[0].data(), languages[0].size());
		writefunc("\"", 1);
		return;
	}

	const char *pfix="(";

	for (auto &language:languages)
	{
		writefunc(pfix, strlen(pfix));
		writefunc("\"", 1);
		msgappends(writefunc, language.data(), language.size());
		writefunc("\"", 1);
		pfix=" ";
	}

	writefunc(")", 1);
}

void msgbodystructure( void (*writefunc)(const char *, size_t), bool dox,
		       rfc822::fdstreambuf &src,
		       rfc2045::entity &message )
{
	(*writefunc)("(", 1);

	if (message.subentities.size() > 0 &&
	    !(message.subentities.size() == 1 &&
	      rfc2045_message_content_type(
		      message.content_type.value.c_str()
	      )))
		/* MULTIPART */
	{
		for (auto &child:message.subentities)
			msgbodystructure(writefunc, dox, src, child);

		(*writefunc)(" \"", 2);
		auto p=strchr(message.content_type.value.c_str(), '/');
		if (p)
			msgappends(writefunc, p+1, strlen(p+1));
		(*writefunc)("\"", 1);

		if (dox)
		{
			(*writefunc)(" ", 1);
			do_param_list(writefunc, message.content_type);

			(*writefunc)(" ", 1);
			do_disposition(writefunc,
				       std::string_view{
					       message.content_disposition
				       });

			(*writefunc)(" ", 1);
			do_content_language(writefunc,
					    message.content_language);

			(*writefunc)(" ", 1);
			contentstr(writefunc, message.content_location);
		}
	}
	else
	{
		char	buf[40];

		auto &content_type_s=message.content_type.value;

		auto q=std::find_if(content_type_s.begin(),
				    content_type_s.end(),
				    []
				    (char c)
				    {
					    return c == ' ' || c == '/';
				    });

		(*writefunc)("\"", 1);
		msgappends(writefunc, content_type_s.c_str(),
			   q-content_type_s.begin());
		(*writefunc)("\" \"", 3);

		while (q != content_type_s.end() && (*q == ' ' || *q == '/'))
			++q;

		auto p=q;

		q=std::find_if(q, content_type_s.end(),
			       []
			       (char c)
			       {
				       return c == ' ' || c == '/';
			       });


		msgappends(writefunc, &*p, q-p);
		(*writefunc)("\" ", 2);

		do_param_list(writefunc, message.content_type);

		(*writefunc)(" ", 1);

		if (message.content_id.empty())
			contentstr(writefunc, message.content_id);
		else
		{
			(*writefunc)("\"<", 2);
			msgappends(writefunc, message.content_id.c_str(),
				   message.content_id.size());
			(*writefunc)(">\"", 2);
		}
		(*writefunc)(" ", 1);
		contentstr(writefunc, message.content_description);

		(*writefunc)(" \"", 2);

		auto content_transfer_encoding_s=
			rfc2045::to_cte(message.content_transfer_encoding);
		msgappends(writefunc, content_transfer_encoding_s,
			strlen(content_transfer_encoding_s));
		(*writefunc)("\" ", 2);

		sprintf(buf, "%lu", (unsigned long)
			(message.endbody-message.startbody+
			 message.nbodylines-message.no_terminating_nl));
			/* nbodylines added for CRs */
		(*writefunc)(buf, strlen(buf));

		if ( message.content_type.value == "text" ||
		     std::string_view{message.content_type.value}.substr(0, 5)
		     == "text/" )
		{
			(*writefunc)(" ", 1);
			sprintf(buf, "%lu", (unsigned long)message.nbodylines);
			(*writefunc)(buf, strlen(buf));
		}

		if (message.subentities.size())
			/* message/rfc822 */
		{
			(*writefunc)(" ", 1);
			msgenvelope(writefunc, src, message.subentities[0]);
			(*writefunc)(" ", 1);
			msgbodystructure(writefunc, dox, src,
					 message.subentities[0]);
			(*writefunc)(" ", 1);
			sprintf(buf, "%lu", (unsigned long)message.nbodylines);
			(*writefunc)(buf, strlen(buf));
		}

		if (dox)
		{
			(*writefunc)(" ", 1);
			contentstr(writefunc, message.content_md5);

			(*writefunc)(" ", 1);
			do_disposition(writefunc,
				       std::string_view{
					       message.content_disposition
				       });

			(*writefunc)(" ", 1);
			do_content_language(writefunc,
					    message.content_language);

			(*writefunc)(" ", 1);
			contentstr(writefunc, message.content_location);
		}
	}
	(*writefunc)(")", 1);
}
