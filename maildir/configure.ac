dnl Process this file with autoconf to produce a configure script.
dnl
dnl Copyright 1998 - 2001 Double Precision, Inc.  See COPYING for
dnl distribution information.

AC_INIT([maildir],[0.11],[courier-maildrop@lists.sourceforge.net])

>confdefs.h  # Kill PACKAGE_ macros

AC_CONFIG_SRCDIR(maildirquota.c)
AC_CONFIG_AUX_DIR(../..)
LPATH="$PATH:/usr/local/bin"
AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE([foreign no-define])
AC_CONFIG_HEADERS(config.h)

dnl Checks for programs.
AC_PROG_AWK
AC_USE_SYSTEM_EXTENSIONS
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_LN_S
LT_INIT

AC_PROG_CXX
AX_CXX_COMPILE_STDCXX_17

AC_PATH_PROGS(PERL, perl5 perl, perl, $LPATH)

if test "$GCC" = "yes"
then
	CFLAGS="$CFLAGS -Wall"
fi

if test "$GXX" = "yes"
then
	CXXFLAGS="$CXXFLAGS -Wall"
fi

CFLAGS="$CFLAGS -I${srcdir}/.. -I.. -I${srcdir}/../.. -I../.."
CXXFLAGS="$CXXFLAGS -I${srcdir}/.. -I.. -I${srcdir}/../.. -I../.."

dnl Checks for libraries.

dnl Checks for header files.
AC_HEADER_DIRENT

AC_CHECK_HEADERS_ONCE([sys/time.h])
# Obsolete code to be removed.
if test $ac_cv_header_sys_time_h = yes; then
  AC_DEFINE([TIME_WITH_SYS_TIME],[1],[Define to 1 if you can safely include both <sys/time.h>
	     and <time.h>.  This macro is obsolete.])
fi
# End of obsolete code.

AC_CHECK_HEADERS(sys/stat.h sys/wait.h fcntl.h unistd.h sysexits.h utime.h)

AC_CHECK_PROG(PCRE2, pcre2-config, yes, no)

if test "$PCRE2" = "yes"
then
	AC_DEFINE_UNQUOTED(HAVE_PCRE2,1,[Whether the pcre library was detected])
	PCRE_LDFLAGS="`pcre2-config --libs8`"
	PCRE_CFLAGS="`pcre2-config --cflags`"
fi
AC_SUBST(PCRE_LDFLAGS)
AC_SUBST(PCRE_CFLAGS)

AC_HEADER_SYS_WAIT

AC_LANG([C++])
AC_CHECK_HEADERS(vector vector.h)
AC_LANG([C])

dnl Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_TYPE_OFF_T
AC_TYPE_SIZE_T
AC_TYPE_UID_T
AC_STRUCT_TM
AC_SYS_LARGEFILE

dnl Checks for library functions.
AC_CHECK_FUNCS(symlink readlink utime utimes)

AC_CHECK_FUNCS(inotify_init inotify_init1)

AC_CACHE_CHECK([for missing gethostname prototype],maildir_cv_SYS_GETHOSTNAME,

AC_COMPILE_IFELSE([AC_LANG_PROGRAM([[
#if HAVE_UNISTD_H
#include	<unistd.h>
#endif

extern int gethostname(int,int);
]], [[
]])],[maildir_cv_SYS_GETHOSTNAME=yes],[maildir_cv_SYS_GETHOSTNAME=no
])

)

if test $maildir_cv_SYS_GETHOSTNAME = "no"
then
	AC_DEFINE_UNQUOTED(HAS_GETHOSTNAME,1,
	[ Whether gethostname() is prototyped ])
fi

AC_ARG_WITH(db, [  --with-db=gdbm          Use the GDBM library.
  --with-db=db            Use the libdb.a library.],
	db="$withval", db="")

if test "$db" = "no"
then
	db=""
fi

if test "$db" != ""
then
	AC_DEFINE_UNQUOTED(HAVE_DBOBJ,1,
	[ Whether the top-level configure script defined dbobj ])
fi

AC_ARG_WITH(trashquota, [  --with-trashquota       Count deleted messages as part of the quota],
	trashquota="$withval",
	trashquota="no")

if test "$trashquota" = "yes"
then
	AC_DEFINE_UNQUOTED(TRASHQUOTA,1,
	[ Whether to count deleted messages towards the maildir quota ])
fi

test "x$prefix" = xNONE && prefix=$ac_default_prefix
test "x$exec_prefix" = xNONE && exec_prefix='${prefix}'
eval "prefix=$prefix"
eval "exec_prefix=$exec_prefix"
eval "sysconfdir=$sysconfdir"

AC_PATH_PROGS(MAILBOT, mailbot, mailbot, $LPATH)

if test -d $srcdir/../../courier
then
	MAILBOT="$bindir/mailbot"
	AC_DEFINE_UNQUOTED(HAVE_COURIER,1,
				[ Whether building the full Courier suite. ])
fi

AC_SUBST(MAILBOT)
AM_CONDITIONAL(HAVE_SGML, test -d ${srcdir}/../docbook)

if test "$target_os" = "cygwin"
then
	AC_DEFINE_UNQUOTED(MDIRSEP, "!",
	[ Maildir target separator ])
else
	AC_DEFINE_UNQUOTED(MDIRSEP, ":",
	[ Maildir target separator ])
fi

AC_CONFIG_FILES([Makefile sharedindexinstall sharedindexsplit])
AC_OUTPUT
