dnl Process this file with autoconf to produce a configure script.
dnl
dnl Copyright 1998 - 2010 Double Precision, Inc.  See COPYING for
dnl distribution information.

AC_INIT([numlib],[0.10],[courier-users@lists.sourceforge.net])

>confdefs.h  # Kill PACKAGE_ macros

AC_CONFIG_SRCDIR([atotimet.c])
AC_CONFIG_AUX_DIR(../..)
AC_CONFIG_HEADERS([config.h])
AM_INIT_AUTOMAKE([foreign no-define])

dnl Checks for programs.
AC_PROG_AWK
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_LN_S
LT_INIT

if test "$GCC" = "yes"
then
	CFLAGS="$CFLAGS -Wall"
fi

CFLAGS="-I.. -I${srcdir}/.. $CFLAGS"

dnl Checks for libraries.

dnl Checks for header files.

AC_CHECK_HEADERS(unistd.h stdint.h)

AC_CHECK_TYPE(int64_t, [ : ],
		       [
		       AC_DEFINE_UNQUOTED(int64_t,long long,[default definition of int64_t])
		       ])

dnl Checks for typedefs, structures, and compiler characteristics.
AC_TYPE_UID_T
AC_TYPE_PID_T
AC_SYS_LARGEFILE

dnl Checks for library functions.

AC_CHECK_FUNCS(setgroups initgroups)
AC_CONFIG_FILES([Makefile])
AC_OUTPUT
