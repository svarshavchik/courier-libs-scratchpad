/*
** Copyright 1998 - 2023 Double Precision, Inc.
** See COPYING for distribution information.
*/

#include	"config.h"
#include	"funcs.h"
#include	"deliverdotlock.h"
#include	"mio.h"
#include	"formatmbox.h"
#include	"xconfig.h"
#include	"varlist.h"
#include	"pipefds.h"
#include	"log.h"
#include	"exittrap.h"
#include	"maildir.h"
#include	"filelock.h"
#include	"setgroupid.h"
#include	<sys/types.h>
#if HAVE_SYS_STAT_H
#include	<sys/stat.h>
#endif
#if HAVE_SYS_FILE_H
#include	<sys/file.h>
#endif
#include	"mywait.h"
#include	<signal.h>
#include	<stdlib.h>
#include	<stdio.h>
#if HAVE_FCNTL_H
#include	<fcntl.h>
#endif
#if HAVE_UNISTD_H
#include	<unistd.h>
#endif
#include	<errno.h>


///////////////////////////////////////////////////////////////////////////
//
//  Deliver to a mailbox, a file, or a maildir.
//
//  If there was a delivery error, error message is printed, and we
//  return -1.
//
//  If delivery was succesfull, 0 is returned.
//
///////////////////////////////////////////////////////////////////////////

int delivery(const char *mailbox)
{
FormatMbox	format_mbox;

	if (format_mbox.HasMsg())	return (0);

	std::string	b;

	if ( *mailbox == '!' || *mailbox == '|' )
	{
	std::string	cmdbuf;

		if (*mailbox == '!')
		{
			cmdbuf=GetVar("SENDMAIL");

			cmdbuf += " -f '' ";
			cmdbuf += mailbox+1;
		}
		else
			cmdbuf= mailbox+1;


		if (VerboseLevel() > 0)
			merr << "maildrop: Delivering to |" <<
				cmdbuf.c_str() << "\n";

	PipeFds	pipe;

		if (pipe.Pipe())
			throw "Cannot create pipe.";

	pid_t	pid=fork();

		if (pid < 0)
			throw "Cannot fork.";

		if (pid == 0)
		{
			pipe.close1();
			dup2(pipe.fds[0], 0);
			pipe.close0();

			try
			{
				subshell(cmdbuf.c_str());
			}
			catch (const char *p)
			{
				if (write(2, p, strlen(p)) < 0 ||
				    write(2, "\n", 1) < 0)
					; /* ignored */
				_exit(100);
			}
#if NEED_NONCONST_EXCEPTIONS
			catch (char *p)
			{
				if (write(2, p, strlen(p)) < 0 ||
				    write(2, "\n", 1) < 0)
					; /* ignored */
				_exit(100);
			}
#endif
			catch (...)
			{
				_exit(100);
			}
		}

	Mio	pipemio;

		pipe.close0();
		pipemio.fd(pipe.fds[1]);
		pipe.fds[1]= -1;
		format_mbox.Init(0);

		int	rc=format_mbox.DeliverTo(pipemio);
		int	wait_stat;

		while (Alarm::wait_child(&wait_stat) != pid)
			;

		if (wait_stat == 0)
			rc=0;

		log(mailbox, rc || wait_stat, format_mbox);

		{
		std::string	name, val;

			if (rc)	wait_stat= -1;
			else wait_stat= WIFEXITED(wait_stat)
				? WEXITSTATUS(wait_stat):-1;

			add_integer(val, wait_stat);
			name="EXITCODE";
			SetVar(name, val);
		}

		if (rc)	return (-1);
	}
	else if (Maildir::IsMaildir(mailbox))
	{
		block_sigalarm pause;
		Maildir	deliver_maildir;
		Mio	deliver_file;

		if ( deliver_maildir.MaildirOpen(mailbox, deliver_file,
			maildrop.msgptr->MessageSize()) < 0)
		{
			throw 75;
		}

		format_mbox.Init(0);
		if (format_mbox.DeliverTo(deliver_file))
		{
			log(mailbox, -1, format_mbox);
			return (-1);
		}
		deliver_maildir.MaildirSave();
		log(mailbox, 0, format_mbox);
	}
	else		// Delivering to a mailbox (hopefully)
	{
		block_sigalarm pause;
		DeliverDotLock	dotlock;

		if (VerboseLevel() > 0)
			merr << "maildrop: Delivering to " << mailbox << "\n";

#if	USE_DOTLOCK
		dotlock.LockMailbox(mailbox);
#endif

		struct	stat	stat_buf;
		Mio	mio;
		std::string name_buf;

		std::string um=GetVar("UMASK");
		unsigned int umask_val=077;

		sscanf(um.c_str(), "%o", &umask_val);

		umask_val=umask(umask_val);

		if (mio.Open(mailbox, O_CREAT | O_WRONLY, 0666) < 0)
		{
			umask_val=umask(umask_val);
			throw "Unable to open mailbox.";
		}
		umask_val=umask(umask_val);

		if (fstat(mio.fd(), &stat_buf) < 0)
			throw "Unable to open mailbox.";

#if	USE_FLOCK

		if (VerboseLevel() > 4)
			merr << "maildrop: Flock()ing " << mailbox << ".\n";

		FileLock::do_filelock(mio.fd());
#endif
		if (S_ISREG(stat_buf.st_mode))
		{
			if (mio.seek(0L, SEEK_END) == (off_t)-1)
				throw "Seek error on mailbox.";
			dotlock.trap_truncate(mio.fd(), stat_buf.st_size);
		}

		if (VerboseLevel() > 4)
			merr << "maildrop: Appending to " << mailbox << ".\n";

		try
		{
			format_mbox.Init(1);

			if ((stat_buf.st_size > 0 &&
			     mio.write(
#if	CRLF_TERM
				       "\r\n", 2
#else
				       "\n", 1
#endif
				       ) < 0) ||
			    format_mbox.DeliverTo(mio))
			{
				dotlock.truncate();
				log(mailbox, -1, format_mbox);
				return (-1);
			}
		}
		catch (...)
		{
			dotlock.truncate();
			log(mailbox, -1, format_mbox);
			throw;
		}
		log(mailbox, 0, format_mbox);
	}

	if (VerboseLevel() > 4)
		merr << "maildrop: Delivery complete.\n";

	return (0);
}

void	subshell(const char *cmd)
{
	std::string	b;

	std::string shell=GetVar("SHELL");

	const char *p, *q;

	for (p=q=shell.c_str(); *p; p++)
		if (*p == SLASH_CHAR)	q=p+1;

	std::vector<std::vector<char>> strings;
	std::vector<char *> env;

	ExportEnv(strings, env);

int	n;

	for (n=0; n<NSIG; n++)
		signal(n, SIG_DFL);

	if (setgroupid(getgid()) < 0 ||
	    setuid(getuid()) < 0)
	{
		perror("setuid/setgid");
		_exit(100);
	}
	ExitTrap::onfork();
	execle(shell.c_str(), q, "-c", cmd, (const char *)NULL, env.data());
	if (write (2, "Unable to execute ", 18) < 0 ||
	    write (2, shell.c_str(), shell.size()) < 0 ||
	    write (2, "\n", 1) < 0)
		; /* ignored */
	_exit(100);
}
