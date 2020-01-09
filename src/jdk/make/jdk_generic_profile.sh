#!/bin/sh

#
# Copyright (c) 2007, 2011, Oracle and/or its affiliates. All rights reserved.
# Copyright 2011 Red Hat, Inc.
# DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
#
# This code is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License version 2 only, as
# published by the Free Software Foundation.  Oracle designates this
# particular file as subject to the "Classpath" exception as provided
# by Oracle in the LICENSE file that accompanied this code.
#
# This code is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# version 2 for more details (a copy is included in the LICENSE file that
# accompanied this code).
#
# You should have received a copy of the GNU General Public License version
# 2 along with this work; if not, write to the Free Software Foundation,
# Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
#
# Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
# or visit www.oracle.com if you need additional information or have any
# questions.
#


#############################################################################
#
# Generic build profile.sh for all platforms, works in bash, sh, and ksh.
#
# Copy this file to your own area, and edit it to suit your needs.
#
# Ideally you either won't need to set the ALT_* variables because the
#   build system will find what it needs through system provided paths
#   or environment variables, or you have installed the component in the
#   recommended default path.
#
# If you find yourself forced to set an ALT_* environment variable and
#   suspect we could have figured it out automatically, please let us know.
#
# Most ALT_* directory defaults are based on being in the parent directory in
#    ALT_SLASH_JAVA, so it's possible to create for example a "C:/jdk6"
#    directory, assign that to ALT_SLASH_JAVA, and place all the components
#    in that directory. This could also minimize the ALT_* environment
#    variables you need to set.
#
########
#
# Assumes basic unix utilities are in the PATH already (uname, hostname, etc.).
#
# On Windows, assumes PROCESSOR_IDENTIFIER, VS100COMNTOOLS,
#   SYSTEMROOT (or SystemRoot), COMPUTERNAME (or hostname works), and
#   USERNAME is defined in the environment.
#   This profile does not rely on using vcvars32.bat and 64bit Setup.bat.
#   Uses CYGWIN cygpath to make sure paths are space-free.
#
# The JDK Makefiles may change in the future, making some of these
#   settings unnecessary or redundant.
#
# This is a working example, but may or may not work on all systems.
#
#############################################################################
#
# WARNING: This file will clobber the value of some environment variables.
#
# Sets up these environment variables for doing JDK builds:
#    USERNAME
#    COMPUTERNAME
#    PATH
#    Windows Only:
#      LIB
#      INCLUDE
#      PS1
#      SHELL
#
# Attempts to set these variables for the JDK builds:           
#    ALT_COMPILER_PATH
#    ALT_BOOTDIR
#    Windows Only:
#      ALT_UNIXCOMMAND_PATH
#      ALT_DXSDK_PATH
#      ALT_MSVCRNN_DLL_PATH
#
#############################################################################
#
# Keep in mind that at this point, we are running in some kind of shell
#   (sh, ksh, or bash). We don't know if it's solaris, linux, or windows 
#   CYGWIN. We need to figure that out.

# Find user name
if [ "${USERNAME}" = "" ] ; then
    USERNAME="${LOGNAME}"
fi
if [ "${USERNAME}" = "" ] ; then
    USERNAME="${USER}"
fi
export USERNAME

# Find machine name
if [ "${COMPUTERNAME}" = "" ] ; then
    COMPUTERNAME="$(hostname)"
fi
export COMPUTERNAME

# Boot jdk
bootjdk=jdk1.6.0
importjdk=jdk1.7.0

# Uses 'uname -s', but only expect SunOS or Linux, assume Windows otherwise.
osname=$(uname -s)
if [ "${osname}" = SunOS ] ; then
  
  # System place where JDK installed images are stored?
  jdk_instances=/usr/jdk/instances

  # Get the Sun Studio compilers (and latest patches for them too)
  if [ "${ALT_COMPILER_PATH}" = "" ] ; then
    ALT_COMPILER_PATH=/opt/SUNWspro/bin
    export ALT_COMPILER_PATH
  fi
  if [ ! -d ${ALT_COMPILER_PATH} ] ; then
    echo "WARNING: Cannot access ALT_COMPILER_PATH=${ALT_COMPILER_PATH}"
  fi
  
  # Place compiler path early in PATH to avoid 'cc' conflicts.
  path4sdk=${ALT_COMPILER_PATH}:/usr/ccs/bin:/usr/ccs/lib:/usr/bin:/bin:/usr/sfw/bin

  # Make sure these are unset
  unset JAVA_HOME
  unset LD_LIBRARY_PATH

  # Build in C locale
  LANG=C
  export LANG
  LC_ALL=C
  export LC_ALL

  umask 002

elif [ "${osname}" = Linux ] ; then
  
  # System place where JDK installed images are stored?
  jdk_instances=/opt/java
    
  # Use compilers from /usr/bin
  path4sdk=/usr/bin:/bin:/usr/sbin:/sbin

  # Make sure these are unset
  unset JAVA_HOME
  unset LD_LIBRARY_PATH

  # Build in C locale
  LANG=C
  export LANG
  LC_ALL=C
  export LC_ALL

  umask 002

else

  # System place where JDK installed images are stored?
  jdk_instances="C:"

  # Windows: Differs on CYGWIN and the compiler available.
  #   Also, blanks in pathnames gives make headaches, so anything placed
  #   in any ALT_* variable should be the short windows DOS names.
   
  # Check CYGWIN (should have already been done)
  #   Assumption here is that you are in a shell window via cygwin.
  proc_arch=`echo "${PROCESSOR_IDENTIFIER}" | expand | cut -d' ' -f1 | sed -e 's@x86@X86@g' -e 's@Intel64@X64@g' -e 's@em64t@X64@g' -e 's@EM64T@X64@g' -e 's@amd64@X64@g' -e 's@AMD64@X64@g' -e 's@ia64@IA64@g'`
  if [ "${proc_arch}" = "X64" ] ; then
    windows_arch=amd64
  else
    windows_arch=i586
  fi
  # We need to check if we are running a CYGWIN shell
  if [ "$(uname -a | fgrep Cygwin)" != "" -a -f /bin/cygpath ] ; then
    # For CYGWIN, uname will have "Cygwin" in it, and /bin/cygpath should exist
    # Utility to convert to short pathnames without spaces
    cygpath="/usr/bin/cygpath -a -m -s"
    # Most unix utilities are in the /usr/bin
    unixcommand_path="/usr/bin"
    # Make the prompt tell you CYGWIN
    export PS1="CYGWIN:${COMPUTERNAME}:${USERNAME}[\!] "
  else
    echo "ERROR: Cannot find CYGWIN on this machine"
    exit 1
  fi
  if [ "${ALT_UNIXCOMMAND_PATH}" != "" ] ; then
    unixcommand_path=${ALT_UNIXCOMMAND_PATH}
  fi
    
  # Default shell
  export SHELL="${unixcommand_path}/sh"

  # Setup path system (verify this is right)
  if [ "${SystemRoot}" != "" ] ; then
    sys_root=$(${cygpath} "${SystemRoot}")
  elif [ "${SYSTEMROOT}" != "" ] ; then
    sys_root=$(${cygpath} "${SYSTEMROOT}")
  else
    sys_root=$(${cygpath} "C:/WINNT")
  fi
  path4sdk="${unixcommand_path};${sys_root}/system32;${sys_root};${sys_root}/System32/Wbem"
  if [ ! -d "${sys_root}" ] ; then
    echo "WARNING: No system root found at: ${sys_root}"
  fi

  # Compiler setup (nasty part)
  #   NOTE: You can use vcvars32.bat to set PATH, LIB, and INCLUDE.
  #   NOTE: CYGWIN has a link.exe too, make sure the compilers are first

  # Use supplied vsvars.sh
  repo=`hg root`
  if [ -f "${repo}/make/scripts/vsvars.sh" ] ; then
    eval `sh ${repo}/make/scripts/vsvars.sh -v10`
  elif [ -f "${repo}/../make/scripts/vsvars.sh" ] ; then
    eval `sh ${repo}/../make/scripts/vsvars.sh -v10`
  else
    echo "WARNING: No make/scripts/vsvars.sh file found"
  fi
    
fi

# Get the previous JDK to be used to bootstrap the build
if [ "${ALT_BOOTDIR}" = "" ] ; then
  ALT_BOOTDIR=${jdk_instances}/${bootjdk}
  export ALT_BOOTDIR
fi
if [ ! -d ${ALT_BOOTDIR} ] ; then
  echo "WARNING: Cannot access ALT_BOOTDIR=${ALT_BOOTDIR}"
fi

# Get the import JDK to be used to get hotspot VM if not built
if [ "${ALT_JDK_IMPORT_PATH}" = "" -a -d ${jdk_instances}/${importjdk} ] ; then
  ALT_JDK_IMPORT_PATH=${jdk_instances}/${importjdk}
  export ALT_JDK_IMPORT_PATH
fi

# Export PATH setting
PATH="${path4sdk}"
export PATH

# Obtain pkgconfig for libs
pkgconfig=$(which pkg-config 2>/dev/null)
echo "pkgconfig=${pkgconfig}"

# Find source location
jdk_topdir=$(dirname ${BASH_SOURCE})/..
if [ ! -e ${jdk_topdir}/src ] ; then
  jdk_topdir=$(hg root) ;
fi
echo "jdk_topdir=${jdk_topdir}"

# Export variables required for Zero
if [ "x${ZERO_BUILD}" = "x" ] ; then ZERO_BUILD=false; fi
if [ "x${SHARK_BUILD}" = "x" ] ; then SHARK_BUILD=false; fi
if [ "${SHARK_BUILD}" = true ] ; then
  ZERO_BUILD=true
  export ZERO_BUILD
fi
echo "Building Zero: ${ZERO_BUILD}"
echo "Building Shark: ${SHARK_BUILD}"

if [ "${ZERO_BUILD}" = true ] ; then
  # ZERO_LIBARCH is the name of the architecture-specific
  # subdirectory under $JAVA_HOME/jre/lib
  arch=$(uname -m)
  case "${arch}" in
    x86_64)  ZERO_LIBARCH=amd64     ;;
    i?86)    ZERO_LIBARCH=i386      ;;
    sparc64) ZERO_LIBARCH=sparcv9   ;;
    arm*)    ZERO_LIBARCH=arm       ;;
    sh*)     ZERO_LIBARCH=sh        ;;
    ppc64le) ZERO_LIBARCH=ppc64le   ;;
    *)       ZERO_LIBARCH="$(arch)"
  esac
  export ZERO_LIBARCH
  echo "Zero library architecture: ${ZERO_LIBARCH}"

  # ARCH_DATA_MODEL is the number of bits in a pointer
  case "${ZERO_LIBARCH}" in
    arm|i386|ppc|s390|sh|sparc)
      ARCH_DATA_MODEL=32
      ;;
    aarch64|alpha|amd64|ia64|ppc64|ppc64le|s390x|sparcv9)
      ARCH_DATA_MODEL=64
      ;;
    *)
      echo "ERROR: Unable to determine ARCH_DATA_MODEL for ${ZERO_LIBARCH}"
      exit 1
  esac
  export ARCH_DATA_MODEL
  echo "Zero architecture data model: ${ARCH_DATA_MODEL}"

  # ZERO_ENDIANNESS is the endianness of the processor
  case "${ZERO_LIBARCH}" in
    arm|aarch64|amd64|i386|ia64|mipsel|ppc64le)
      ZERO_ENDIANNESS=little
      ;;
    ppc|ppc64|s390*|sparc*|alpha)
      ZERO_ENDIANNESS=big
      ;;
    *)
      echo "ERROR: Unable to determine ZERO_ENDIANNESS for ${ZERO_LIBARCH}"
      exit 1
  esac
  export ZERO_ENDIANNESS
  echo "Zero endianness: ${ZERO_ENDIANNESS}"

  # ZERO_ARCHDEF is used to enable architecture-specific code
  case "${ZERO_LIBARCH}" in
    i386)   ZERO_ARCHDEF=IA32  ;;
    ppc*)   ZERO_ARCHDEF=PPC   ;;
    s390*)  ZERO_ARCHDEF=S390  ;;
    sparc*) ZERO_ARCHDEF=SPARC ;;
    *)      ZERO_ARCHDEF=$(echo "${ZERO_LIBARCH}" | tr a-z A-Z)
  esac
  export ZERO_ARCHDEF
  echo "Zero architecture definition: ${ZERO_ARCHDEF}"

  # ZERO_ARCHFLAG tells the compiler which mode to build for
  case "${ZERO_LIBARCH}" in
    s390)
      ZERO_ARCHFLAG="-m31"
      ;;
    arm|aarch64|ppc64le)
      ZERO_ARCHFLAG="-D_LITTLE_ENDIAN"
      ;;
    *)
      ZERO_ARCHFLAG="-m${ARCH_DATA_MODEL}"
  esac
  export ZERO_ARCHFLAG
  echo "Zero architecture flag: ${ZERO_ARCHFLAG}"

  # LIBFFI_CFLAGS and LIBFFI_LIBS tell the compiler how to compile and
  # link against libffi
  if [ -x "${pkgconfig}" ] ; then
    if [ "${LIBFFI_CFLAGS}" = "" ] ; then
      LIBFFI_CFLAGS=$("${pkgconfig}" --cflags libffi)
    fi
    if [ "${LIBFFI_LIBS}" = "" ] ; then
      LIBFFI_LIBS=$("${pkgconfig}" --libs libffi)
    fi
  fi
  if [ "${LIBFFI_LIBS}" = "" ] ; then
      echo "No libffi detected.";
      LIBFFI_LIBS="-lffi"
  fi
  export LIBFFI_CFLAGS
  export LIBFFI_LIBS
  echo "Using LIBFFI_CFLAGS=${LIBFFI_CFLAGS}"
  echo "Using LIBFFI_LIBS=${LIBFFI_LIBS}"
  
  # LLVM_CFLAGS, LLVM_LDFLAGS and LLVM_LIBS tell the compiler how to
  # compile and link against LLVM
  if [ "${SHARK_BUILD}" = true ] ; then
    if [ "${LLVM_CONFIG}" = "" ] ; then
      LLVM_CONFIG=$(which llvm-config 2>/dev/null)
    fi
    if [ ! -x "${LLVM_CONFIG}" ] ; then
      echo "ERROR: Unable to locate llvm-config"
      exit 1
    fi
    llvm_components="jit engine nativecodegen"

    unset LLVM_CFLAGS
    for flag in $("${LLVM_CONFIG}" --cxxflags $llvm_components); do
      if echo "${flag}" | grep -q '^-[ID]'; then
        if [ "${flag}" != "-D_DEBUG" ] ; then
          if [ "${LLVM_CFLAGS}" != "" ] ; then
            LLVM_CFLAGS="${LLVM_CFLAGS} "
          fi
          LLVM_CFLAGS="${LLVM_CFLAGS}${flag}"
        fi
      fi
    done
    llvm_version=$("${LLVM_CONFIG}" --version | sed 's/\.//; s/svn.*//')
    LLVM_CFLAGS="${LLVM_CFLAGS} -DSHARK_LLVM_VERSION=${llvm_version}"

    unset LLVM_LDFLAGS
    for flag in $("${LLVM_CONFIG}" --ldflags $llvm_components); do
      if echo "${flag}" | grep -q '^-L'; then
        if [ "${LLVM_LDFLAGS}" != "" ] ; then
          LLVM_LDFLAGS="${LLVM_LDFLAGS} "
        fi
        LLVM_LDFLAGS="${LLVM_LDFLAGS}${flag}"
      fi
    done

    unset LLVM_LIBS
    for flag in $("${LLVM_CONFIG}" --libs $llvm_components); do
      if echo "${flag}" | grep -q '^-l'; then
        if [ "${LLVM_LIBS}" != "" ] ; then
          LLVM_LIBS="${LLVM_LIBS} "
        fi
        LLVM_LIBS="${LLVM_LIBS}${flag}"
      fi
    done

    export LLVM_CFLAGS
    export LLVM_LDFLAGS
    export LLVM_LIBS
    echo "Using LLVM_CFLAGS=${LLVM_CFLAGS}"
    echo "Using LLVM_LDFLAGS=${LLVM_LDFLAGS}"
    echo "Using LLVM_LIBS=${LLVM_LIBS}"
  fi
fi

# Export variables for system zlib
# ZLIB_CFLAGS and ZLIB_LIBS tell the compiler how to compile and
# link against zlib
if [ -x "${pkgconfig}" ] ; then
  if [ "${ZLIB_CFLAGS}" = "" ] ; then
    ZLIB_CFLAGS=$("${pkgconfig}" --cflags zlib)
  fi
  if [ "${ZLIB_LIBS}" = "" ] ; then
    ZLIB_LIBS=$("${pkgconfig}" --libs zlib)
  fi
fi
if [ "${ZLIB_LIBS}" = "" ] ; then
    echo "No zlib detected.";
    ZLIB_LIBS="-lz"
fi
export ZLIB_CFLAGS
export ZLIB_LIBS
echo "Using ZLIB_CFLAGS=${ZLIB_CFLAGS}"
echo "Using ZLIB_LIBS=${ZLIB_LIBS}"

# Export variables for system LCMS
# LCMS_CFLAGS and LCMS_LIBS tell the compiler how to compile and
# link against lcms2
if [ -x "${pkgconfig}" ] ; then
  if [ "${LCMS_CFLAGS}" = "" ] ; then
    LCMS_CFLAGS=$("${pkgconfig}" --cflags lcms2)
  fi
  if [ "${LCMS_LIBS}" = "" ] ; then
    LCMS_LIBS=$("${pkgconfig}" --libs lcms2)
  fi
fi
if [ "${LCMS_LIBS}" = "" ] ; then
    echo "No LCMS detected.";
    LCMS_LIBS="-llcms2"
fi
export LCMS_CFLAGS
export LCMS_LIBS
echo "Using LCMS_CFLAGS=${LCMS_CFLAGS}"
echo "Using LCMS_LIBS=${LCMS_LIBS}"

# Export variables for system jpeg
# JPEG_CFLAGS and JPEG_LIBS tell the compiler how to compile and
# link against libjpeg
if [ "${JPEG_LIBS}" = "" ] ; then
    JPEG_LIBS="-ljpeg"
fi
export JPEG_LIBS
echo "Using JPEG_LIBS=${JPEG_LIBS}"

# Export variables for system libpng
# PNG_CFLAGS and PNG_LIBS tell the compiler how to compile and
# link against libpng
if [ -x "${pkgconfig}" ] ; then
  if [ "${PNG_CFLAGS}" = "" ] ; then
    PNG_CFLAGS=$("${pkgconfig}" --cflags libpng)
  fi
  if [ "${PNG_LIBS}" = "" ] ; then
    PNG_LIBS=$("${pkgconfig}" --libs libpng)
  fi
fi
if [ "${PNG_LIBS}" = "" ] ; then
    echo "No libpng detected.";
    PNG_LIBS="-lpng"
fi
export PNG_CFLAGS
export PNG_LIBS
echo "Using PNG_CFLAGS=${PNG_CFLAGS}"
echo "Using PNG_LIBS=${PNG_LIBS}"

# Export variables for system giflib
# GIF_CFLAGS and GIF_LIBS tell the compiler how to compile and
# link against giflib
if [ "${GIF_LIBS}" = "" ] ; then
    GIF_LIBS="-lgif"
fi
export GIF_LIBS
echo "Using GIF_LIBS=${GIF_LIBS}"

# Export variables for system krb5
# KRB5_CFLAGS and KRB5_LIBS tell the compiler how to compile and
# link against Kerberos
if [ "${KRB5_LIBS}" = "" ] ; then
    KRB5_LIBS="-lkrb5"
fi
export KRB5_LIBS
echo "Using KRB5_LIBS=${KRB5_LIBS}"

# Export variables for system CUPS
# CUPS_CFLAGS and CUPS_LIBS tell the compiler how to compile and
# link against CUPS
if [ "${CUPS_LIBS}" = "" ] ; then
    CUPS_LIBS="-lcups"
fi
export CUPS_LIBS
echo "Using CUPS_LIBS=${CUPS_LIBS}"

# Export variables for system libgtk
# GTK_CFLAGS and GTK_LIBS tell the compiler how to compile and
# link against libgtk
if [ -x "${pkgconfig}" ] ; then
  if "${pkgconfig}" --exists gtk+-2.0 ; then
    if [ "${GTK_CFLAGS}" = "" ] ; then
      GTK_CFLAGS=$("${pkgconfig}" --cflags gtk+-2.0 gthread-2.0)
    fi
    if [ "${GTK_LIBS}" = "" ] ; then
      GTK_LIBS=$("${pkgconfig}" --libs gtk+-2.0 gthread-2.0)
    fi
  fi
fi
export GTK_CFLAGS
export GTK_LIBS
echo "Using GTK_CFLAGS=${GTK_CFLAGS}"
echo "Using GTK_LIBS=${GTK_LIBS}"

# Export variables for system libgio
# GIO_CFLAGS and GIO_LIBS tell the compiler how to compile and
# link against libgio
if [ -x "${pkgconfig}" ] ; then
  if "${pkgconfig}" --exists gio-2.0 ; then
    if [ "${GIO_CFLAGS}" = "" ] ; then
      GIO_CFLAGS=$("${pkgconfig}" --cflags gio-2.0)
    fi
    if [ "${GIO_LIBS}" = "" ] ; then
      GIO_LIBS=$("${pkgconfig}" --libs gio-2.0)
    fi
  fi
fi
export GIO_CFLAGS
export GIO_LIBS
echo "Using GIO_CFLAGS=${GIO_CFLAGS}"
echo "Using GIO_LIBS=${GIO_LIBS}"

# Export variables for system libpcsc
# PCSC_CFLAGS and PCSC_LIBS tell the compiler how to compile and
# link against libpcsc
if [ -x "${pkgconfig}" ] ; then
  if [ "${PCSC_CFLAGS}" = "" ] ; then
    PCSC_CFLAGS=$("${pkgconfig}" --cflags libpcsclite)
  fi
  if [ "${PCSC_LIBS}" = "" ] ; then
    PCSC_LIBS=$("${pkgconfig}" --libs libpcsclite)
  fi
fi
if [ "${PCSC_LIBS}" = "" ] ; then
    echo "No libpcsclite detected.";
    PCSC_LIBS="-lpcsclite"
fi
export PCSC_CFLAGS
export PCSC_LIBS
echo "Using PCSC_CFLAGS=${PCSC_CFLAGS}"
echo "Using PCSC_LIBS=${PCSC_LIBS}"

# Export variables for system fontconfig
# FONTCONFIG_CFLAGS and FONTCONFIG_LIBS tell the compiler how to compile and
# link against libfontconfig
if [ -x "${pkgconfig}" ] ; then
  if [ "${FONTCONFIG_CFLAGS}" = "" ] ; then
    FONTCONFIG_CFLAGS=$("${pkgconfig}" --cflags fontconfig)
  fi
  if [ "${FONTCONFIG_LIBS}" = "" ] ; then
    FONTCONFIG_LIBS=$("${pkgconfig}" --libs fontconfig)
  fi
fi
if [ "${FONTCONFIG_LIBS}" = "" ] ; then
    echo "No fontconfig detected.";
    FONTCONFIG_LIBS="-lfontconfig"
fi
export FONTCONFIG_CFLAGS
export FONTCONFIG_LIBS
echo "Using FONTCONFIG_CFLAGS=${FONTCONFIG_CFLAGS}"
echo "Using FONTCONFIG_LIBS=${FONTCONFIG_LIBS}"

# Export variables for system gconf
# GCONF_CFLAGS, GCONF_LIBS, GOBJECT_CFLAGS and
# GOBJECT_LIBS tell the compiler how to compile and
# link against gconf
if [ -x "${pkgconfig}" ] ; then
  if "${pkgconfig}" --exists gconf-2.0 ; then
    if [ "${GCONF_CFLAGS}" = "" ] ; then
      GCONF_CFLAGS=$("${pkgconfig}" --cflags gconf-2.0)
    fi
    if [ "${GCONF_LIBS}" = "" ] ; then
      GCONF_LIBS=$("${pkgconfig}" --libs gconf-2.0)
    fi
  fi
  if "${pkgconfig}" --exists gobject-2.0 ; then
    if [ "${GOBJECT_CFLAGS}" = "" ] ; then
      GOBJECT_CFLAGS=$("${pkgconfig}" --cflags gobject-2.0)
    fi
    if [ "${GOBJECT_LIBS}" = "" ] ; then
      GOBJECT_LIBS=$("${pkgconfig}" --libs gobject-2.0)
    fi
  fi
fi
export GCONF_CFLAGS
export GCONF_LIBS
export GOBJECT_CFLAGS
export GOBJECT_LIBS
echo "Using GCONF_CFLAGS=${GCONF_CFLAGS}"
echo "Using GCONF_LIBS=${GCONF_LIBS}"
echo "Using GOBJECT_CFLAGS=${GOBJECT_CFLAGS}"
echo "Using GOBJECT_LIBS=${GOBJECT_LIBS}"

# Export variables for system sctp
# SCTP_CFLAGS and SCTP_LIBS tell the compiler how to compile and
# link against libsctp
if [ "${SCTP_LIBS}" = "" ] ; then
    SCTP_LIBS="-lsctp"
fi
export SCTP_LIBS
echo "Using SCTP_LIBS=${SCTP_LIBS}"

# Setup nss.cfg using location of NSS libraries
if [ -x "${pkgconfig}" ] ; then
  if [ "${NSS_LIBDIR}" = "" ] ; then
    NSS_LIBDIR=$("${pkgconfig}" --variable=libdir nss)
  fi
fi
if [ "${NSS_LIBDIR}" = "" ] ; then
  NSS_LIBDIR="/usr/lib";
  echo "No NSS library directory detected.";
fi
echo "Using NSS_LIBDIR=${NSS_LIBDIR}"
sed -e "s#@NSS_LIBDIR@#${NSS_LIBDIR}#" \
  ${jdk_topdir}/src/share/lib/security/nss.cfg.in \
  > ${jdk_topdir}/src/share/lib/security/nss.cfg

# IcedTea defaults; use system libraries
export SYSTEM_LCMS=true
export SYSTEM_ZLIB=true
export SYSTEM_JPEG=true
export SYSTEM_PNG=true
export SYSTEM_GIF=true
export SYSTEM_KRB5=true
export SYSTEM_CUPS=true
export SYSTEM_FONTCONFIG=true
export SYSTEM_PCSC=true
export SYSTEM_SCTP=true
export COMPILE_AGAINST_SYSCALLS=true

if [ "x${GTK_LIBS}" != "x" ] ; then
  echo "Gtk+ detected; enabling system linking.";
  export SYSTEM_GTK=true
fi

if [ "x${GIO_LIBS}" != "x" ] ; then
  echo "GIO detected; enabling system linking.";
  export SYSTEM_GIO=true
fi

if [ "x${GCONF_LIBS}" != "x" -a "x${GOBJECT_LIBS}" != "x" ] ; then
  echo "GConf detected; enabling system linking.";
  export SYSTEM_GCONF=true
fi

# IcedTea default; turn on the ARM32 JIT
# Disabled for now due to PR2942
export ARM32JIT=false

# IcedTea versioning
export ICEDTEA_NAME="IcedTea"
export PACKAGE_VERSION="2.6.17"
export DERIVATIVE_ID="${ICEDTEA_NAME} ${PACKAGE_VERSION}"
echo "Building ${DERIVATIVE_ID}"

if [ -e ${jdk_topdir} ] ; then
  if hg -R ${jdk_topdir} id &>/dev/null ; then
    export JDK_REVID="r$(hg -R ${jdk_topdir} id -i)";
    echo "JDK Mercurial revision: ${JDK_REVID}"
  fi
fi
hotspot_topdir=${jdk_topdir}/../hotspot
if [ -e ${hotspot_topdir} ] ; then
  if hg -R ${hotspot_topdir} id &>/dev/null ; then
    export HOTSPOT_BUILD_VERSION="r$(hg -R ${hotspot_topdir} id -i)";
    echo "HotSpot Mercurial revision: ${HOTSPOT_BUILD_VERSION}"
  fi
fi

lsbrelease=$(which lsb_release 2>/dev/null)
echo "lsbrelease=${lsbrelease}"
if [ -x "${lsbrelease}" ] ; then
  lsbinfo="$(${lsbrelease} -ds | sed 's/^"//;s/"$//')"
  if test "x${PKGVERSION}" = "x"; then
    export DISTRIBUTION_ID="Built on ${lsbinfo} ($(date))"
  else
    export DISTRIBUTION_ID="${lsbinfo}, package $PKGVERSION"
  fi
  export DISTRO_NAME="$(${lsbrelease} -is | sed 's/^"//;s/"$//')"
  echo "Distribution ID: ${DISTRIBUTION_ID}"
  echo "Distribution Name: ${DISTRO_NAME}"
fi
