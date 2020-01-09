# If debug is 1, OpenJDK is built with all debug info present.
%global debug 0

%global icedtea_version 2.6.19
%global icedtea_snapshot %{nil}
%global hg_tag icedtea-%{icedtea_version}%{icedtea_snapshot}

%global accessmajorver 1.23
%global accessminorver 0
%global accessver %{accessmajorver}.%{accessminorver}
%global accessurl http://ftp.gnome.org/pub/GNOME/sources/java-access-bridge/

%global aarch64			aarch64 arm64 armv8
#sometimes we need to distinguish big and little endian PPC64
%global ppc64le			ppc64le
%global ppc64be			ppc64 ppc64p7
%global multilib_arches %{power64} sparc64 x86_64 
%global jit_arches		%{ix86} x86_64 sparcv9 sparc64 %{ppc64be} %{ppc64le} %{aarch64}

# With diabled nss is NSS deactivated, so in NSS_LIBDIR can be wrong path
# the initialisation must be here. LAter the pkg-connfig have bugy behaviour
#looks liekopenjdk RPM specific bug
# Always set this so the nss.cfg file is not broken
%global NSS_LIBDIR %(pkg-config --variable=libdir nss)
%global NSS_LIBS %(pkg-config --libs nss)
%global NSS_CFLAGS %(pkg-config --cflags nss-softokn)
# see https://bugzilla.redhat.com/show_bug.cgi?id=1332456
%global NSSSOFTOKN_BUILDTIME_NUMBER %(pkg-config --modversion nss-softokn || : )
%global NSS_BUILDTIME_NUMBER %(pkg-config --modversion nss || : )
#this is a workaround for processing of requires during srpm creation
%global NSSSOFTOKN_BUILDTIME_VERSION %(if [ "x%{NSSSOFTOKN_BUILDTIME_NUMBER}" == "x" ] ; then echo "" ;else echo ">= %{NSSSOFTOKN_BUILDTIME_NUMBER}" ;fi)
%global NSS_BUILDTIME_VERSION %(if [ "x%{NSS_BUILDTIME_NUMBER}" == "x" ] ; then echo "" ;else echo ">= %{NSS_BUILDTIME_NUMBER}" ;fi)

# Fix for https://bugzilla.redhat.com/show_bug.cgi?id=1111349.
# See also https://bugzilla.redhat.com/show_bug.cgi?id=1590796
# as to why some libraries *cannot* be excluded. In particular,
# these are:
# libjsig.so, libjava.so, libjawt.so, libjvm.so and libverify.so
%global _privatelibs libatk-wrapper[.]so.*|libattach[.]so.*|libawt_headless[.]so.*|libawt[.]so.*|libawt_xawt[.]so.*|libdt_socket[.]so.*|libfontmanager[.]so.*|libhprof[.]so.*|libinstrument[.]so.*|libj2gss[.]so.*|libj2pcsc[.]so.*|libj2pkcs11[.]so.*|libjaas_unix[.]so.*|libjava_crw_demo[.]so.*|libjavajpeg[.]so.*|libjdwp[.]so.*|libjli[.]so.*|libjsdt[.]so.*|libjsoundalsa[.]so.*|libjsound[.]so.*|liblcms[.]so.*|libmanagement[.]so.*|libmlib_image[.]so.*|libnet[.]so.*|libnio[.]so.*|libnpt[.]so.*|libsaproc[.]so.*|libsctp[.]so.*|libsplashscreen[.]so.*|libsunec[.]so.*|libunpack[.]so.*|libzip[.]so.*|lib[.]so\\(SUNWprivate_.*

%global __provides_exclude ^(%{_privatelibs})$
%global __requires_exclude ^(%{_privatelibs})$

# In some cases, the arch used by the JDK does
# not match _arch.
# Also, in some cases, the machine name used by SystemTap
# does not match that given by _build_cpu
%ifarch x86_64
%global archbuild amd64
%global archinstall amd64
%global stapinstall x86_64
%endif
%ifarch ppc
%global archbuild ppc
%global archinstall ppc
%global archdef PPC
%global stapinstall powerpc
%endif
%ifarch %{ppc64be}
%global archbuild ppc64
%global archinstall ppc64
%global archdef PPC
%global stapinstall powerpc
%endif
%ifarch %{ppc64le}
%global archbuild ppc64le
%global archinstall ppc64le
%global archdef PPC64
%global stapinstall powerpc
%endif
%ifarch %{ix86}
%global archbuild i586
%global archinstall i386
%global stapinstall i386
%endif
%ifarch ia64
%global archbuild ia64
%global archinstall ia64
%global stapinstall ia64
%endif
%ifarch s390
%global archbuild s390
%global archinstall s390
%global archdef S390
%global stapinstall s390
%endif
%ifarch s390x
%global archbuild s390x
%global archinstall s390x
%global archdef S390
%global stapinstall s390
%endif
%ifarch %{arm}
%global archbuild arm
%global archinstall arm
%global archdef ARM
%global stapinstall arm
%endif
%ifarch %{aarch64}
%global archbuild aarch64
%global archinstall aarch64
%global archdef AARCH64
%global stapinstall arm64
%endif
# 32 bit sparc, optimized for v9
%ifarch sparcv9
%global archbuild sparc
%global archinstall sparc
%global stapinstall %{_build_cpu}
%endif
# 64 bit sparc
%ifarch sparc64
%global archbuild sparcv9
%global archinstall sparcv9
%global stapinstall %{_build_cpu}
%endif
%ifnarch %{jit_arches}
%global archbuild %{_arch}
%global archinstall %{_arch}
%endif

%if %{debug}
%global debugbuild debug_build
%else
%global debugbuild %{nil}
%endif

%ifnarch %{ppc64le}
%global with_pulseaudio 1
%else
%global with_pulseaudio 0
%endif

%ifarch %{jit_arches}
%global with_systemtap 1
%else
%global with_systemtap 0
%endif

# Convert an absolute path to a relative path.  Each symbolic link is
# specified relative to the directory in which it is installed so that
# it will resolve properly within chrooted installations.
%global script 'use File::Spec; print File::Spec->abs2rel($ARGV[0], $ARGV[1])'
%global abs2rel %{__perl} -e %{script}

# Hard-code libdir on 64-bit architectures to make the 64-bit JDK
# simply be another alternative.
%global LIBDIR       %{_libdir}
#backuped original one
%ifarch %{multilib_arches}
%global syslibdir       %{_prefix}/lib64
%global _libdir         %{_prefix}/lib
%global archname        %{name}.%{_arch}
%else
%global syslibdir       %{_libdir}
%global archname        %{name}
%endif

# Standard JPackage naming and versioning defines.
%global origin          openjdk
%global top_level_dir_name   %{origin}
%global updatever       231
%global buildver        01
# Keep priority on 6digits in case updatever>9
%global priority        170%{updatever}
%global javaver         1.7.0

# Standard JPackage directories and symbolic links.
# Make 64-bit JDKs just another alternative on 64-bit architectures.
%ifarch %{multilib_arches}
%global sdklnk          java-%{javaver}-%{origin}.%{_arch}
%global jrelnk          jre-%{javaver}-%{origin}.%{_arch}
%global sdkdir          %{name}-%{version}.%{_arch}
%else
%global sdklnk          java-%{javaver}-%{origin}
%global jrelnk          jre-%{javaver}-%{origin}
%global sdkdir          %{name}-%{version}
%endif
%global jredir          %{sdkdir}/jre
%global sdkbindir       %{_jvmdir}/%{sdklnk}/bin
%global jrebindir       %{_jvmdir}/%{jrelnk}/bin
%ifarch %{multilib_arches}
%global comaptible_uniquesuffix  %{name}-%{version}.%{_arch}
%else
%global comaptible_uniquesuffix  %{name}-%{version}
%endif
%global jvmjardir       %{_jvmjardir}/%{comaptible_uniquesuffix}

%global rpm_state_dir %{_localstatedir}/lib/rpm-state/

# The suffix for file names when we have to make them unique (from
# other Java packages).
%global uniquesuffix          %{name}

%ifarch %{jit_arches}
# Where to install systemtap tapset (links)
# We would like these to be in a package specific subdir,
# but currently systemtap doesn't support that, so we have to
# use the root tapset dir for now. To distinquish between 64
# and 32 bit architectures we place the tapsets under the arch
# specific dir (note that systemtap will only pickup the tapset
# for the primary arch for now). Systemtap uses the machine name
# aka build_cpu as architecture specific directory name.
%global tapsetroot /usr/share/systemtap
%global tapsetdir %{tapsetroot}/tapset/%{stapinstall}
%endif

%if %{debug}
%global buildoutputdir %{top_level_dir_name}/build/linux-%{archbuild}-debug
%else
%global buildoutputdir %{top_level_dir_name}/build/linux-%{archbuild}
%endif

# Prevent brp-java-repack-jars from being run.
%global __jar_repack 0

Name:    java-%{javaver}-%{origin}
Version: %{javaver}.%{updatever}
Release: %{icedtea_version}%{icedtea_snapshot}.2%{?dist}
# java-1.5.0-ibm from jpackage.org set Epoch to 1 for unknown reasons,
# and this change was brought into RHEL-4.  java-1.5.0-ibm packages
# also included the epoch in their virtual provides.  This created a
# situation where in-the-wild java-1.5.0-ibm packages provided "java =
# 1:1.5.0".  In RPM terms, "1.6.0 < 1:1.5.0" since 1.6.0 is
# interpreted as 0:1.6.0.  So the "java >= 1.6.0" requirement would be
# satisfied by the 1:1.5.0 packages.  Thus we need to set the epoch in
# JDK package >= 1.6.0 to 1, and packages referring to JDK virtual
# provides >= 1.6.0 must specify the epoch, "java >= 1:1.6.0".
Epoch:   1
Summary: OpenJDK Runtime Environment
Group:   Development/Languages

# HotSpot code is licensed under GPLv2
# JDK library code is licensed under GPLv2 with the Classpath exception
# The Apache license is used in code taken from Apache projects (primarily JAXP & JAXWS)
# DOM levels 2 & 3 and the XML digital signature schemas are licensed under the W3C Software License
# The JSR166 concurrency code is in the public domain
# The BSD and MIT licenses are used for a number of third-party libraries (see THIRD_PARTY_README)
# The OpenJDK source tree includes the JPEG library (IJG), zlib & libpng (zlib), giflib and LCMS (MIT)
# The test code includes copies of NSS under the Mozilla Public License v2.0
# The PCSClite headers are under a BSD with advertising license
# The elliptic curve cryptography (ECC) source code is licensed under the LGPLv2.1 or any later version
# JavaScript support is provided by Rhino, which is licensed under MPLv1.1
License:  ASL 1.1 and ASL 2.0 and BSD and BSD with advertising and GPL+ and GPLv2 and GPLv2 with exceptions and IJG and LGPLv2+ and MIT and MPLv1.1 and MPLv2.0 and Public Domain and W3C and zlib
URL:      http://openjdk.java.net/

# Source from upstream IcedTea 2.x project. To regenerate, use
# VERSION=icedtea-${icedtea_version} FILE_NAME_ROOT=openjdk-${VERSION}
# REPO_ROOT=<path to checked-out repository> generate_source_tarball.sh
Source0:  openjdk-icedtea-%{icedtea_version}%{icedtea_snapshot}.tar.xz

# Gnome access bridge
# Download-able from accessurl, md5 hash supported
Source1:  %{accessurl}%{accessmajorver}/java-access-bridge-%{accessver}.tar.bz2

# README file
# This source is under maintainer's/java-team's control
Source2:  README.src

# Sources 6-11 are taken from hg clone http://icedtea.classpath.org/hg/icedtea7
# Unless said differently, there is directory with required sources which should be enough to pack/rename

# Class rewrite to rewrite rhino hierarchy
Source5: class-rewriter.tar.gz

# Systemtap tapsets. Zipped up to keep it small.
# last update from IcedTea 2.6.19
Source6: systemtap-tapset-2.6.19.tar.xz

# .desktop files. 
Source7:  policytool.desktop
Source77: jconsole.desktop

# nss configuration file
Source8: nss.cfg

# FIXME: Taken from IcedTea snapshot 877ad5f00f69, but needs to be moved out
# hg clone -r 877ad5f00f69 http://icedtea.classpath.org/hg/icedtea7
Source9: pulseaudio.tar.gz

# Removed libraries that we link instead
Source10: remove-intree-libraries.sh

#http://icedtea.classpath.org/hg/icedtea7/file/933d082ec889/fsg.sh
# file to clean tarball, should be ketp updated as possible
Source1111: fsg.sh

# Ensure we aren't using the limited crypto policy
Source12: TestCryptoLevel.java

# Ensure file type detection works (RH1190835)
Source13: RH1190835.java

# Missing headers not provided by nss-softokn
Source15: lowkeyti.h
Source16: softoknt.h

# RPM/distribution specific patches

# Allow TCK to pass with access bridge wired in
Patch1:   rh1648645-java_access_bridge_loading_java_version_privileged_tck.patch

# Disable access to access-bridge packages by untrusted apps
Patch3:   rh1648644-java_access_bridge_privlidged_security.patch

# Ignore AWTError when assistive technologies are loaded 
Patch4:   rh1648242-accessible_toolkit_crash_do_not_break_jvm.patch

# Build docs even in debug
Patch5:   rh1648254-javadoc_generated_during_all_variants_of_buid.patch

# Add debuginfo where missing
Patch6:   rh1648259-libsaproc_libjsig_compiled_with_g_to_provide_correct_debuginfo.patch

#
# OpenJDK specific patches
#

# Add rhino support
Patch100: rh1649777-add_rhino_support_jdk7.patch

Patch106: rh1648643-comment_out_freetype_check.patch

# allow to create hs_pid.log in tmp (in 700 permissions) if working directory is unwritable
Patch200: rh1648241-abrt_friendly_hs_log_jdk7.patch

#
# Optional component packages
#

# Make the ALSA based mixer the default when building with the pulseaudio based
# mixer
Patch300: rh1649760-make_alsa_based_mixer_default_when_pulseaudio_build.patch

# Make the curves reported by Java's SSL implementation match those of NSS
Patch400: pr1834-rh1022017-reduce_ellipticcurvesextension_to_provide_only_three_nss_supported_nist_curves_23_24_25.patch

# SystemTap support
#Workaround RH804632
Patch303: rh1648665-jstack_sprintf_prints_constant.patch

# Temporary patches

# 8076221, PR2809: Backport "8076221: Disable RC4 cipher suites" (will appear in 2.7.0)
Patch500: jdk8076221-pr2809-disable_rc4_cipher_suites.patch
# JDK-8226318, RH1738637: Fix crash in Class.forName (will appear in 7u241/2.6.20)
Patch502: jdk8226318-rh1738637-class_lookup_crash.patch
# End of tmp patches

BuildRequires: autoconf
BuildRequires: automake
BuildRequires: gcc-c++
BuildRequires: alsa-lib-devel
BuildRequires: cups-devel
BuildRequires: desktop-file-utils
BuildRequires: giflib-devel
#BuildRequires: lcms2-devel # No LCMS2 in RHEL6
BuildRequires: libX11-devel
BuildRequires: libXi-devel
BuildRequires: libXp-devel
BuildRequires: libXt-devel
BuildRequires: libXtst-devel
BuildRequires: libjpeg-devel
BuildRequires: libpng-devel
BuildRequires: wget
BuildRequires: xorg-x11-proto-devel
BuildRequires: ant
BuildRequires: ant-nodeps
BuildRequires: libXinerama-devel
# Provides lsb_release for generating distro id in jdk_generic_profile.sh
BuildRequires: redhat-lsb-core
BuildRequires: rhino >= 1.7R4
BuildRequires: zip
BuildRequires: fontconfig
BuildRequires: xorg-x11-fonts-Type1
BuildRequires: zlib > 1.2.3-6
# Require a build JDK which has a working jar uf (PR1437 / RH1207129)
BuildRequires: java-1.7.0-openjdk-devel >= 1.7.0.111-2.6.7.2
BuildRequires: fontconfig
# Java Access Bridge for GNOME build requirements.
BuildRequires: at-spi-devel
BuildRequires: gawk
BuildRequires: libbonobo-devel
BuildRequires: pkgconfig >= 0.9.0
BuildRequires: xorg-x11-utils
# Requirements for setting up the nss.cfg
BuildRequires: nss-devel
# Required for NIO2
BuildRequires: libattr-devel
# Required for native proxy support
BuildRequires: GConf2-devel
# Build requirements for SunEC system NSS support
BuildRequires: nss-softokn-freebl-devel >= 3.14.3-18
# Required for smartcard support
BuildRequires: pcsc-lite-devel
# Required for SCTP support
BuildRequires: lksctp-tools-devel
# PulseAudio build requirements.
%if %{with_pulseaudio}
BuildRequires: pulseaudio-libs-devel >= 0.9.11
%endif
# Zero-assembler build requirement.
%ifnarch %{jit_arches}
BuildRequires: libffi-devel >= 3.0.10
%endif

ExclusiveArch: x86_64 i686 %{ppc64be}

# cacerts build requirement.
BuildRequires: openssl
# execstack build requirement.
# no prelink on ARM yet
%ifnarch %{arm} %{aarch64} %{ppc64le}
BuildRequires: prelink
%endif
%ifarch %{jit_arches}
#systemtap build requirement.
BuildRequires: systemtap-sdt-devel
%endif
# visualvm build requirements.
BuildRequires: jakarta-commons-logging

#Requires: lcms2 # No LCMS2 on RHEL6
Requires: libjpeg = 6b
Requires: fontconfig
Requires: xorg-x11-fonts-Type1
# Require /etc/pki/java/cacerts.
Requires: ca-certificates
# Require jpackage-utils for ant.
Requires: jpackage-utils >= 1.7.3-1jpp.2
# Require zoneinfo data provided by tzdata-java subpackage.
Requires: tzdata-java
# nss provider requirements
# Part of NSS is statically linked into the libsunec.so library
# so we need at least the version we built against to be available
# on the system. Otherwise, the SunEC provider fails to initialise.
Requires: nss%{?_isa} %{NSS_BUILDTIME_VERSION}
Requires: nss-softokn%{?_isa} %{NSSSOFTOKN_BUILDTIME_VERSION}
# tool to copy jdk's configs - should be Recommends only, but then only dnf/yum eforce it, not rpm transaction and so no configs are persisted when pure rpm -u is run. I t may be consiedered as regression
Requires:	copy-jdk-configs >= 3.3-9
OrderWithRequires: copy-jdk-configs
# Post requires alternatives to install tool alternatives.
Requires(post):   %{_sbindir}/alternatives
# Postun requires alternatives to uninstall tool alternatives.
Requires(postun): %{_sbindir}/alternatives

# Standard JPackage base provides.
Provides: jre-%{javaver}-%{origin} = %{epoch}:%{version}-%{release}
Provides: jre-%{origin} = %{epoch}:%{version}-%{release}
Provides: jre-%{javaver} = %{epoch}:%{version}-%{release}
Provides: java-%{javaver} = %{epoch}:%{version}-%{release}
Provides: jre = %{javaver}
Provides: java-%{origin} = %{epoch}:%{version}-%{release}
Provides: java = %{epoch}:%{javaver}
# Standard JPackage extensions provides.
Provides: jndi = %{epoch}:%{version}
Provides: jndi-ldap = %{epoch}:%{version}
Provides: jndi-cos = %{epoch}:%{version}
Provides: jndi-rmi = %{epoch}:%{version}
Provides: jndi-dns = %{epoch}:%{version}
Provides: jaas = %{epoch}:%{version}
Provides: jsse = %{epoch}:%{version}
Provides: jce = %{epoch}:%{version}
Provides: jdbc-stdext = 4.1
Provides: java-sasl = %{epoch}:%{version}
Provides: java-fonts = %{epoch}:%{version}
# "7" versions
Provides: jre7-%{javaver}-%{origin} = %{epoch}:%{version}-%{release}
Provides: jre7-%{origin} = %{epoch}:%{version}-%{release}
Provides: jre7-%{javaver} = %{epoch}:%{version}-%{release}
Provides: java7-%{javaver} = %{epoch}:%{version}-%{release}
Provides: jre7 = %{javaver}
Provides: java7-%{origin} = %{epoch}:%{version}-%{release}
Provides: java7 = %{epoch}:%{javaver}
# Standard JPackage extensions provides.
Provides: jndi7 = %{epoch}:%{version}
Provides: jndi7-ldap = %{epoch}:%{version}
Provides: jndi7-cos = %{epoch}:%{version}
Provides: jndi7-rmi = %{epoch}:%{version}
Provides: jndi7-dns = %{epoch}:%{version}
Provides: jaas7 = %{epoch}:%{version}
Provides: jsse7 = %{epoch}:%{version}
Provides: jce7 = %{epoch}:%{version}
Provides: jdbc7-stdext = 4.1
Provides: java7-sasl = %{epoch}:%{version}
Provides: java7-fonts = %{epoch}:%{version}

%description
The OpenJDK runtime environment.

%package devel
Summary: OpenJDK Development Environment
Group:   Development/Tools

# Require base package.
Requires:         %{name} = %{epoch}:%{version}-%{release}
# Post requires alternatives to install tool alternatives.
Requires(post):   %{_sbindir}/alternatives
# Postun requires alternatives to uninstall tool alternatives.
Requires(postun): %{_sbindir}/alternatives

# Standard JPackage devel provides.
Provides: java7-sdk-%{javaver}-%{origin} = %{epoch}:%{version}
Provides: java7-sdk-%{javaver} = %{epoch}:%{version}
Provides: java7-sdk-%{origin} = %{epoch}:%{version}
Provides: java7-sdk = %{epoch}:%{javaver}
Provides: java7-%{javaver}-devel = %{epoch}:%{version}
Provides: java7-devel-%{origin} = %{epoch}:%{version}
Provides: java7-devel = %{epoch}:%{javaver}

Provides: java-sdk-%{javaver}-%{origin} = %{epoch}:%{version}
Provides: java-sdk-%{javaver} = %{epoch}:%{version}
Provides: java-sdk-%{origin} = %{epoch}:%{version}
Provides: java-sdk = %{epoch}:%{javaver}
Provides: java-%{javaver}-devel = %{epoch}:%{version}
Provides: java-devel-%{origin} = %{epoch}:%{version}
Provides: java-devel = %{epoch}:%{javaver}

%description devel
The OpenJDK development tools.

%package demo
Summary: OpenJDK Demos
Group:   Development/Languages

Requires: %{name} = %{epoch}:%{version}-%{release}

%description demo
The OpenJDK demos.

%package src
Summary: OpenJDK Source Bundle
Group:   Development/Languages

Requires: %{name} = %{epoch}:%{version}-%{release}

%description src
The OpenJDK source bundle.

%package javadoc
Summary: OpenJDK API Documentation
Group:   Documentation
Requires: jpackage-utils
BuildArch: noarch

# Post requires alternatives to install javadoc alternative.
Requires(post):   %{_sbindir}/alternatives
# Postun requires alternatives to uninstall javadoc alternative.
Requires(postun): %{_sbindir}/alternatives

# Standard JPackage javadoc provides.
Provides: java-javadoc = %{epoch}:%{version}-%{release}
Provides: java-%{javaver}-javadoc = %{epoch}:%{version}-%{release}

%description javadoc
The OpenJDK API documentation.

%prep
%setup -q -c -n %{name}
%setup -q -n %{name} -T -D -a 1
# https://bugzilla.redhat.com/show_bug.cgi?id=1189084
prioritylength=`expr length %{priority}`
if [ $prioritylength -ne 6 ] ; then
 echo "priority must be 6 digits in total, violated"
 exit 14
fi
cp %{SOURCE2} .
# Add local copies of missing NSS headers
cp -v %{SOURCE15} %{SOURCE16} openjdk/jdk/src/share/native/sun/security/ec

# OpenJDK patches
%patch100

# pulseaudio support
%if %{with_pulseaudio}
%patch300
%endif

# Temporary fixes
%patch500
%patch502
# End of temporary fixes

# ECC fix
%patch400

# Add systemtap patches if enabled
%if %{with_systemtap}
%endif

# Remove libraries that are linked
sh %{SOURCE10}

# Extract the rewriter (to rewrite rhino classes)
tar xzf %{SOURCE5}

# Extract systemtap tapsets
%if %{with_systemtap}

tar xf %{SOURCE6}
%patch303

for file in tapset/*.in; do

    OUTPUT_FILE=`echo $file | sed -e s:\.stp\.in$:-%{version}-%{release}.stp:g`
    sed -e s:@ABS_SERVER_LIBJVM_SO@:%{_jvmdir}/%{sdkdir}/jre/lib/%{archinstall}/server/libjvm.so:g $file > $file.1
# FIXME this should really be %if %{has_client_jvm}
%ifarch %{ix86}
    sed -e s:@ABS_CLIENT_LIBJVM_SO@:%{_jvmdir}/%{sdkdir}/jre/lib/%{archinstall}/client/libjvm.so:g $file.1 > $OUTPUT_FILE
%else
    sed -e '/@ABS_CLIENT_LIBJVM_SO@/d' $file.1 > $OUTPUT_FILE
%endif
    sed -i -e s:@INSTALL_ARCH_DIR@:%{archinstall}:g $OUTPUT_FILE
    sed -i -e s:@prefix@:%{_jvmdir}/%{sdkdir $suffix}/:g $OUTPUT_FILE

done

%endif

# Pulseaudio
%if %{with_pulseaudio}
tar xzf %{SOURCE9}
%endif


%patch3
%patch4

%if %{debug}
%patch5
%patch6
%endif

%patch106
%ifnarch %{aarch64}
#friendly hserror is not applicable in head, needs to be revisited
%patch200
%endif

%build
# How many cpu's do we have?
export NUM_PROC=`/usr/bin/getconf _NPROCESSORS_ONLN 2> /dev/null || :`
export NUM_PROC=${NUM_PROC:-1}

# Build IcedTea and OpenJDK.
%ifarch s390x sparc64 alpha %{power64} %{aarch64}
export ARCH_DATA_MODEL=64
%endif
%ifarch alpha
export CFLAGS="$CFLAGS -mieee"
%endif

#no fstack-protectors-strong in rhel 6.6
export CFLAGS="$CFLAGS"

# Build the re-written rhino jar
mkdir -p rhino/{old,new}

# Compile the rewriter
(cd rewriter 
 javac com/redhat/rewriter/ClassRewriter.java
)

# Extract rhino.jar contents and rewrite
(cd rhino/old 
 jar xf /usr/share/java/rhino.jar
)

java -cp rewriter com.redhat.rewriter.ClassRewriter \
    $PWD/rhino/old \
    $PWD/rhino/new \
    org.mozilla \
    sun.org.mozilla

(cd rhino/old
 for file in `find -type f -not -name '*.class'` ; do
     new_file=../new/`echo $file | sed -e 's#org#sun/org#'`
     mkdir -pv `dirname $new_file`
     cp -v $file $new_file
     sed -ie 's#org\.mozilla#sun.org.mozilla#g' $new_file
 done
)

(cd rhino/new
   jar cfm ../rhino.jar META-INF/MANIFEST.MF sun
)

export JDK_TO_BUILD_WITH=/usr/lib/jvm/java-openjdk



pushd openjdk >& /dev/null

export ALT_DROPS_DIR=$PWD/../drops
export ALT_BOOTDIR="$JDK_TO_BUILD_WITH"

# Save old umask as jdk_generic_profile overwrites it
oldumask=`umask`

# Set generic profile
%ifnarch %{jit_arches}
export ZERO_BUILD=true
%endif
export LCMS_CFLAGS="disabled"
export LCMS_LIBS="disabled"
export PKGVERSION="rhel-%{release}-%{_arch} u%{updatever}-b%{buildver}"

source jdk/make/jdk_generic_profile.sh

# Restore old umask
umask $oldumask

# RHEL 6 does not have LCMS2
export SYSTEM_LCMS=false

# Variable used in hs_err hook on build failures
top_dir_abs_path=$(pwd)/%{top_level_dir_name}

make \
  UNLIMITED_CRYPTO=true \
  ANT="/usr/bin/ant" \
  DISTRO_NAME="Red Hat Enterprise Linux" \
  DISTRO_PACKAGE_VERSION="${PKGVERSION}" \
  JDK_UPDATE_VERSION=`printf "%02d" %{updatever}` \
  JDK_BUILD_NUMBER=b`printf "%02d" %{buildver}` \
  JRE_RELEASE_VERSION=%{javaver}_`printf "%02d" %{updatever}`-b`printf "%02d" %{buildver}` \
  MILESTONE="fcs" \
  ALT_PARALLEL_COMPILE_JOBS="$NUM_PROC" \
  HOTSPOT_BUILD_JOBS="$NUM_PROC" \
  STATIC_CXX="false" \
  RHINO_JAR="$PWD/../rhino/rhino.jar" \
  GENSRCDIR="$PWD/generated.build" \
  FT2_CFLAGS="`pkg-config --cflags freetype2` " \
  FT2_LIBS="`pkg-config --libs freetype2` " \
  DEBUG_CLASSFILES="true" \
  DEBUG_BINARIES="true" \
  STRIP_POLICY="no_strip" \
  JAVAC_WARNINGS_FATAL="false" \
  INSTALL_LOCATION=%{_jvmdir}/%{sdkdir} \
  SYSTEM_NSS="true" \
  NSS_LIBS="%{NSS_LIBS} -lfreebl -lsoftokn" \
  NSS_CFLAGS="%{NSS_CFLAGS} -DLEGACY_NSS" \
  ECC_JUST_SUITE_B="true" \
  %{debugbuild} || ( pwd; find $top_dir_abs_path -name "hs_err_pid*.log" | xargs cat && false )

popd >& /dev/null

export JAVA_HOME=$(pwd)/%{buildoutputdir}/j2sdk-image

# Install nss.cfg right away as we will be using the JRE above
cp -a %{SOURCE8} $JAVA_HOME/jre/lib/security/
sed -i -e s:@NSS_LIBDIR@:%{NSS_LIBDIR}:g $JAVA_HOME/jre/lib/security/nss.cfg

# Build pulseaudio and install it to JDK build location
%if %{with_pulseaudio}
pushd pulseaudio
# IT_CFLAGS="-g" is needed so that debug info symbols get produced.
# See RHBZ#1657863.
make JAVA_HOME=$JAVA_HOME -f Makefile.pulseaudio IT_CFLAGS="-g"
cp -pPRf build/native/libpulse-java.so $JAVA_HOME/jre/lib/%{archinstall}/
cp -pPRf build/pulse-java.jar $JAVA_HOME/jre/lib/ext/
popd
%endif

# Build Java Access Bridge for GNOME.
pushd java-access-bridge-%{accessver}
  patch -l -p1 < %{PATCH1}
  OLD_PATH=$PATH
  export PATH=$JAVA_HOME/bin:$OLD_PATH
  ./configure
  make
  export PATH=$OLD_PATH
  cp -a bridge/accessibility.properties $JAVA_HOME/jre/lib
  chmod 644 gnome-java-bridge.jar
  cp -a gnome-java-bridge.jar $JAVA_HOME/jre/lib/ext
popd

# Copy tz.properties
echo "sun.zoneinfo.dir=/usr/share/javazi" >> $JAVA_HOME/jre/lib/tz.properties

#remove all fontconfig files. This change should be usptreamed soon
rm -f %{buildoutputdir}/j2re-image/lib/fontconfig*.properties.src
rm -f %{buildoutputdir}/j2re-image/lib/fontconfig*.bfc
rm -f %{buildoutputdir}/j2sdk-image/jre/lib/fontconfig*.properties.src
rm -f %{buildoutputdir}/j2sdk-image/jre/lib/fontconfig*.bfc
rm -f %{buildoutputdir}/lib/fontconfig*.properties.src
rm -f %{buildoutputdir}/lib/fontconfig*.bfc

%install
rm -rf $RPM_BUILD_ROOT
STRIP_KEEP_SYMTAB=libjvm*

# There used to be a link to the soundfont.
# This is now obsolete following the inclusion of 8140620/PR2710

pushd %{buildoutputdir}/j2sdk-image

#install jsa directories so we can owe them
mkdir -p $RPM_BUILD_ROOT%{_jvmdir}/%{jredir}/lib/%{archinstall}/server/
mkdir -p $RPM_BUILD_ROOT%{_jvmdir}/%{jredir}/lib/%{archinstall}/client/

  # Install main files.
  install -d -m 755 $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}
  cp -a bin include lib src.zip $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}
  install -d -m 755 $RPM_BUILD_ROOT%{_jvmdir}/%{jredir}
  cp -a jre/bin jre/lib $RPM_BUILD_ROOT%{_jvmdir}/%{jredir}
  cp -a ASSEMBLY_EXCEPTION LICENSE THIRD_PARTY_README $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}

%ifarch %{jit_arches}
  # Install systemtap support files.
  install -dm 755 $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/tapset
  cp -a $RPM_BUILD_DIR/%{uniquesuffix}/tapset/*.stp $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/tapset/
  install -d -m 755 $RPM_BUILD_ROOT%{tapsetdir}
  pushd $RPM_BUILD_ROOT%{tapsetdir}
    RELATIVE=$(%{abs2rel} %{_jvmdir}/%{sdkdir}/tapset %{tapsetdir})
    ln -sf $RELATIVE/*.stp .
  popd
%endif

  # Install cacerts symlink.
  rm -f $RPM_BUILD_ROOT%{_jvmdir}/%{jredir}/lib/security/cacerts
  pushd $RPM_BUILD_ROOT%{_jvmdir}/%{jredir}/lib/security
    RELATIVE=$(%{abs2rel} %{_sysconfdir}/pki/java \
      %{_jvmdir}/%{jredir}/lib/security)
    ln -sf $RELATIVE/cacerts .
  popd

  # Install extension symlinks.
  install -d -m 755 $RPM_BUILD_ROOT%{jvmjardir}
  pushd $RPM_BUILD_ROOT%{jvmjardir}
    RELATIVE=$(%{abs2rel} %{_jvmdir}/%{jredir}/lib %{jvmjardir})
    ln -sf $RELATIVE/jsse.jar jsse-%{version}.jar
    ln -sf $RELATIVE/jce.jar jce-%{version}.jar
    ln -sf $RELATIVE/rt.jar jndi-%{version}.jar
    ln -sf $RELATIVE/rt.jar jndi-ldap-%{version}.jar
    ln -sf $RELATIVE/rt.jar jndi-cos-%{version}.jar
    ln -sf $RELATIVE/rt.jar jndi-rmi-%{version}.jar
    ln -sf $RELATIVE/rt.jar jaas-%{version}.jar
    ln -sf $RELATIVE/rt.jar jdbc-stdext-%{version}.jar
    ln -sf jdbc-stdext-%{version}.jar jdbc-stdext-3.0.jar
    ln -sf $RELATIVE/rt.jar sasl-%{version}.jar
    for jar in *-%{version}.jar
    do
      if [ x%{version} != x%{javaver} ]
      then
        ln -sf $jar $(echo $jar | sed "s|-%{version}.jar|-%{javaver}.jar|g")
      fi
      ln -sf $jar $(echo $jar | sed "s|-%{version}.jar|.jar|g")
    done
  popd

  # Install JCE policy symlinks.
  install -d -m 755 $RPM_BUILD_ROOT%{_jvmprivdir}/%{archname}/jce/vanilla

  # Install versionless symlinks.
  pushd $RPM_BUILD_ROOT%{_jvmdir}
    ln -sf %{jredir} %{jrelnk}
    ln -sf %{sdkdir} %{sdklnk}
  popd

  pushd $RPM_BUILD_ROOT%{_jvmjardir}
    ln -sf %{sdkdir} %{jrelnk}
    ln -sf %{sdkdir} %{sdklnk}
  popd

  # Remove javaws man page
  rm -f man/man1/javaws*

  # Install man pages.
  install -d -m 755 $RPM_BUILD_ROOT%{_mandir}/man1
  for manpage in man/man1/*
  do
    # Convert man pages to UTF8 encoding.
    iconv -f ISO_8859-1 -t UTF8 $manpage -o $manpage.tmp
    mv -f $manpage.tmp $manpage
    install -m 644 -p $manpage $RPM_BUILD_ROOT%{_mandir}/man1/$(basename \
      $manpage .1)-%{uniquesuffix}.1
  done

  # Install demos and samples.
  cp -a demo $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}
  mkdir -p sample/rmi
  mv bin/java-rmi.cgi sample/rmi
  cp -a sample $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}

popd


# Install Javadoc documentation.
install -d -m 755 $RPM_BUILD_ROOT%{_javadocdir}
cp -a %{buildoutputdir}/docs $RPM_BUILD_ROOT%{_javadocdir}/%{name}

# Install icons and menu entries.
for s in 16 24 32 48 ; do
  install -D -p -m 644 \
    %{top_level_dir_name}/jdk/src/solaris/classes/sun/awt/X11/java-icon${s}.png \
    $RPM_BUILD_ROOT%{_datadir}/icons/hicolor/${s}x${s}/apps/java-%{javaver}.png
done

# Install desktop files.
install -d -m 755 $RPM_BUILD_ROOT%{_datadir}/{applications,pixmaps}
for e in %{SOURCE7} %{SOURCE77} ; do
    sed -i "s/#ARCH#/%{_arch}-%{release}/g" $e
    sed -i "s|/usr/bin|%{sdkbindir}/|g" $e
    desktop-file-install --vendor=%{uniquesuffix} --mode=644 \
        --dir=$RPM_BUILD_ROOT%{_datadir}/applications $e
done

# Install /etc/.java/.systemPrefs/ directory
# See https://bugzilla.redhat.com/show_bug.cgi?id=741821
mkdir -p $RPM_BUILD_ROOT%{_sysconfdir}/.java/.systemPrefs

# Find JRE directories.
find $RPM_BUILD_ROOT%{_jvmdir}/%{jredir} -type d \
  | grep -v jre/lib/security \
  | sed 's|'$RPM_BUILD_ROOT'|%dir |' \
  > %{name}.files
# Find JRE files.
find $RPM_BUILD_ROOT%{_jvmdir}/%{jredir} -type f -o -type l \
  | grep -v jre/lib/security \
  | sed 's|'$RPM_BUILD_ROOT'||' \
  >> %{name}.files
# Find demo directories.
find $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/demo \
  $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/sample -type d \
  | sed 's|'$RPM_BUILD_ROOT'|%dir |' \
  > %{name}-demo.files

# FIXME: remove SONAME entries from demo DSOs.  See
# https://bugzilla.redhat.com/show_bug.cgi?id=436497

# Find non-documentation demo files.
find $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/demo \
  $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/sample \
  -type f -o -type l | sort \
  | grep -v README \
  | sed 's|'$RPM_BUILD_ROOT'||' \
  >> %{name}-demo.files
# Find documentation demo files.
find $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/demo \
  $RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}/sample \
  -type f -o -type l | sort \
  | grep README \
  | sed 's|'$RPM_BUILD_ROOT'||' \
  | sed 's|^|%doc |' \
  >> %{name}-demo.files

%check
export JAVA_HOME=$RPM_BUILD_ROOT%{_jvmdir}/%{sdkdir}

# Check unlimited policy has been used
$JAVA_HOME/bin/javac -d . %{SOURCE12}
$JAVA_HOME/bin/java TestCryptoLevel

# Check native library support is available
$JAVA_HOME/bin/javac -d . %{SOURCE13}
$JAVA_HOME/bin/java RH1190835 %{SOURCE13}

%pretrans -p <lua>
-- see https://bugzilla.redhat.com/show_bug.cgi?id=1038092 for whole issue
-- see https://bugzilla.redhat.com/show_bug.cgi?id=1290388 for pretrans over pre
-- if copy-jdk-configs is in transaction, it installs in pretrans to temp
-- if copy_jdk_configs is in temp, then it means that copy-jdk-configs is in tranasction  and so is
-- preferred over one in %%{_libexecdir}. If it is not in transaction, then depends 
-- whether copy-jdk-configs is installed or not. If so, then configs are copied
-- (copy_jdk_configs from %%{_libexecdir} used) or not copied at all
local posix = require "posix"
local debug = false

SOURCE1 = "%{rpm_state_dir}/copy_jdk_configs.lua"
SOURCE2 = "%{_libexecdir}/copy_jdk_configs.lua"

local stat1 = posix.stat(SOURCE1, "type");
local stat2 = posix.stat(SOURCE2, "type");

  if (stat1 ~= nil) then
  if (debug) then
    print(SOURCE1 .." exists - copy-jdk-configs in transaction, using this one.")
  end;
  package.path = package.path .. ";" .. SOURCE1
else 
  if (stat2 ~= nil) then
  if (debug) then
    print(SOURCE2 .." exists - copy-jdk-configs alrady installed and NOT in transation. Using.")
  end;
  package.path = package.path .. ";" .. SOURCE2
  else
    if (debug) then
      print(SOURCE1 .." does NOT exists")
      print(SOURCE2 .." does NOT exists")
      print("No config files will be copied")
    end
  return
  end
end
-- run contetn of included file with fake args
arg = {"--currentjvm", "%{comaptible_uniquesuffix}", "--jvmdir", "%{_jvmdir}", "--origname", "%{name}", "--origjavaver", "%{javaver}", "--arch", "%{_arch}", "--temp", "%{rpm_state_dir}/%{name}.%{_arch}"}
require "copy_jdk_configs.lua"


%post
%ifarch %{jit_arches}
# MetaspaceShared::generate_vtable_methods not implemented for PPC JIT
%ifnarch %{power64}
#see https://bugzilla.redhat.com/show_bug.cgi?id=513605
%{jrebindir}/java -Xshare:dump >/dev/null 2>/dev/null
%endif
%endif

ext=.gz
alternatives \
  --install %{_bindir}/java java %{jrebindir}/java %{priority} \
  --slave %{_jvmdir}/jre jre %{_jvmdir}/%{jrelnk} \
  --slave %{_jvmjardir}/jre jre_exports %{_jvmjardir}/%{jrelnk} \
  --slave %{_bindir}/keytool keytool %{jrebindir}/keytool \
  --slave %{_bindir}/orbd orbd %{jrebindir}/orbd \
  --slave %{_bindir}/pack200 pack200 %{jrebindir}/pack200 \
  --slave %{_bindir}/rmid rmid %{jrebindir}/rmid \
  --slave %{_bindir}/rmiregistry rmiregistry %{jrebindir}/rmiregistry \
  --slave %{_bindir}/servertool servertool %{jrebindir}/servertool \
  --slave %{_bindir}/tnameserv tnameserv %{jrebindir}/tnameserv \
  --slave %{_bindir}/unpack200 unpack200 %{jrebindir}/unpack200 \
  --slave %{_mandir}/man1/java.1$ext java.1$ext \
  %{_mandir}/man1/java-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/keytool.1$ext keytool.1$ext \
  %{_mandir}/man1/keytool-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/orbd.1$ext orbd.1$ext \
  %{_mandir}/man1/orbd-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/pack200.1$ext pack200.1$ext \
  %{_mandir}/man1/pack200-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/rmid.1$ext rmid.1$ext \
  %{_mandir}/man1/rmid-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/rmiregistry.1$ext rmiregistry.1$ext \
  %{_mandir}/man1/rmiregistry-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/servertool.1$ext servertool.1$ext \
  %{_mandir}/man1/servertool-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/tnameserv.1$ext tnameserv.1$ext \
  %{_mandir}/man1/tnameserv-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/unpack200.1$ext unpack200.1$ext \
  %{_mandir}/man1/unpack200-%{uniquesuffix}.1$ext

alternatives \
  --install %{_jvmdir}/jre-%{origin} \
  jre_%{origin} %{_jvmdir}/%{jrelnk} %{priority} \
  --slave %{_jvmjardir}/jre-%{origin} \
  jre_%{origin}_exports %{_jvmjardir}/%{jrelnk}

alternatives \
  --install %{_jvmdir}/jre-%{javaver} \
  jre_%{javaver} %{_jvmdir}/%{jrelnk} %{priority} \
  --slave %{_jvmjardir}/jre-%{javaver} \
  jre_%{javaver}_exports %{_jvmjardir}/%{jrelnk}

update-desktop-database %{_datadir}/applications &> /dev/null || :

touch --no-create %{_datadir}/icons/hicolor
if [ -x %{_bindir}/gtk-update-icon-cache ] ; then
  %{_bindir}/gtk-update-icon-cache --quiet %{_datadir}/icons/hicolor
fi

# see pretrans where this file is declared
# also see that pretrans is only for nondebug
if [ ! "%1" == %{debug_suffix} ]; then
  if [ -f %{_libexecdir}/copy_jdk_configs_fixFiles.sh ] ; then
    sh  %{_libexecdir}/copy_jdk_configs_fixFiles.sh %{rpm_state_dir}/%{name}.%{_arch}  %{_jvmdir}/%{sdkdir}
  fi
fi


exit 0

%postun
if [ $1 -eq 0 ]
then
  alternatives --remove java %{jrebindir}/java
  alternatives --remove jre_%{origin} %{_jvmdir}/%{jrelnk}
  alternatives --remove jre_%{javaver} %{_jvmdir}/%{jrelnk}
fi

update-desktop-database %{_datadir}/applications &> /dev/null || :

touch --no-create %{_datadir}/icons/hicolor
if [ -x %{_bindir}/gtk-update-icon-cache ] ; then
  %{_bindir}/gtk-update-icon-cache --quiet %{_datadir}/icons/hicolor
fi

exit 0

%post devel
ext=.gz
alternatives \
  --install %{_bindir}/javac javac %{sdkbindir}/javac %{priority} \
  --slave %{_jvmdir}/java java_sdk %{_jvmdir}/%{sdklnk} \
  --slave %{_jvmjardir}/java java_sdk_exports %{_jvmjardir}/%{sdklnk} \
  --slave %{_bindir}/appletviewer appletviewer %{sdkbindir}/appletviewer \
  --slave %{_bindir}/apt apt %{sdkbindir}/apt \
  --slave %{_bindir}/extcheck extcheck %{sdkbindir}/extcheck \
  --slave %{_bindir}/idlj idlj %{sdkbindir}/idlj \
  --slave %{_bindir}/jar jar %{sdkbindir}/jar \
  --slave %{_bindir}/jarsigner jarsigner %{sdkbindir}/jarsigner \
  --slave %{_bindir}/javadoc javadoc %{sdkbindir}/javadoc \
  --slave %{_bindir}/javah javah %{sdkbindir}/javah \
  --slave %{_bindir}/javap javap %{sdkbindir}/javap \
  --slave %{_bindir}/jcmd jcmd %{sdkbindir}/jcmd \
  --slave %{_bindir}/jconsole jconsole %{sdkbindir}/jconsole \
  --slave %{_bindir}/jdb jdb %{sdkbindir}/jdb \
  --slave %{_bindir}/jhat jhat %{sdkbindir}/jhat \
  --slave %{_bindir}/jinfo jinfo %{sdkbindir}/jinfo \
  --slave %{_bindir}/jmap jmap %{sdkbindir}/jmap \
  --slave %{_bindir}/jps jps %{sdkbindir}/jps \
  --slave %{_bindir}/jrunscript jrunscript %{sdkbindir}/jrunscript \
  --slave %{_bindir}/jsadebugd jsadebugd %{sdkbindir}/jsadebugd \
  --slave %{_bindir}/jstack jstack %{sdkbindir}/jstack \
  --slave %{_bindir}/jstat jstat %{sdkbindir}/jstat \
  --slave %{_bindir}/jstatd jstatd %{sdkbindir}/jstatd \
  --slave %{_bindir}/native2ascii native2ascii %{sdkbindir}/native2ascii \
  --slave %{_bindir}/policytool policytool %{sdkbindir}/policytool \
  --slave %{_bindir}/rmic rmic %{sdkbindir}/rmic \
  --slave %{_bindir}/schemagen schemagen %{sdkbindir}/schemagen \
  --slave %{_bindir}/serialver serialver %{sdkbindir}/serialver \
  --slave %{_bindir}/wsgen wsgen %{sdkbindir}/wsgen \
  --slave %{_bindir}/wsimport wsimport %{sdkbindir}/wsimport \
  --slave %{_bindir}/xjc xjc %{sdkbindir}/xjc \
  --slave %{_mandir}/man1/appletviewer.1$ext appletviewer.1$ext \
  %{_mandir}/man1/appletviewer-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/apt.1$ext apt.1$ext \
  %{_mandir}/man1/apt-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/extcheck.1$ext extcheck.1$ext \
  %{_mandir}/man1/extcheck-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jar.1$ext jar.1$ext \
  %{_mandir}/man1/jar-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jarsigner.1$ext jarsigner.1$ext \
  %{_mandir}/man1/jarsigner-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/javac.1$ext javac.1$ext \
  %{_mandir}/man1/javac-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/javadoc.1$ext javadoc.1$ext \
  %{_mandir}/man1/javadoc-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/javah.1$ext javah.1$ext \
  %{_mandir}/man1/javah-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/javap.1$ext javap.1$ext \
  %{_mandir}/man1/javap-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jconsole.1$ext jconsole.1$ext \
  %{_mandir}/man1/jconsole-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jdb.1$ext jdb.1$ext \
  %{_mandir}/man1/jdb-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jhat.1$ext jhat.1$ext \
  %{_mandir}/man1/jhat-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jinfo.1$ext jinfo.1$ext \
  %{_mandir}/man1/jinfo-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jmap.1$ext jmap.1$ext \
  %{_mandir}/man1/jmap-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jps.1$ext jps.1$ext \
  %{_mandir}/man1/jps-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jrunscript.1$ext jrunscript.1$ext \
  %{_mandir}/man1/jrunscript-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jsadebugd.1$ext jsadebugd.1$ext \
  %{_mandir}/man1/jsadebugd-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jstack.1$ext jstack.1$ext \
  %{_mandir}/man1/jstack-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jstat.1$ext jstat.1$ext \
  %{_mandir}/man1/jstat-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/jstatd.1$ext jstatd.1$ext \
  %{_mandir}/man1/jstatd-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/native2ascii.1$ext native2ascii.1$ext \
  %{_mandir}/man1/native2ascii-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/policytool.1$ext policytool.1$ext \
  %{_mandir}/man1/policytool-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/rmic.1$ext rmic.1$ext \
  %{_mandir}/man1/rmic-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/schemagen.1$ext schemagen.1$ext \
  %{_mandir}/man1/schemagen-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/serialver.1$ext serialver.1$ext \
  %{_mandir}/man1/serialver-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/wsgen.1$ext wsgen.1$ext \
  %{_mandir}/man1/wsgen-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/wsimport.1$ext wsimport.1$ext \
  %{_mandir}/man1/wsimport-%{uniquesuffix}.1$ext \
  --slave %{_mandir}/man1/xjc.1$ext xjc.1$ext \
  %{_mandir}/man1/xjc-%{uniquesuffix}.1$ext

alternatives \
  --install %{_jvmdir}/java-%{origin} \
  java_sdk_%{origin} %{_jvmdir}/%{sdklnk} %{priority} \
  --slave %{_jvmjardir}/java-%{origin} \
  java_sdk_%{origin}_exports %{_jvmjardir}/%{sdklnk}

alternatives \
  --install %{_jvmdir}/java-%{javaver} \
  java_sdk_%{javaver} %{_jvmdir}/%{sdklnk} %{priority} \
  --slave %{_jvmjardir}/java-%{javaver} \
  java_sdk_%{javaver}_exports %{_jvmjardir}/%{sdklnk}

exit 0

%postun devel
if [ $1 -eq 0 ]
then
  alternatives --remove javac %{sdkbindir}/javac
  alternatives --remove java_sdk_%{origin} %{_jvmdir}/%{sdklnk}
  alternatives --remove java_sdk_%{javaver} %{_jvmdir}/%{sdklnk}
fi

exit 0

%post javadoc
alternatives \
  --install %{_javadocdir}/java javadocdir %{_javadocdir}/%{name}/api \
  %{priority}

exit 0

%postun javadoc
if [ $1 -eq 0 ]
then
  alternatives --remove javadocdir %{_javadocdir}/%{name}/api
fi

exit 0


%files -f %{name}.files
%defattr(-,root,root,-)
%doc %{_jvmdir}/%{sdkdir}/ASSEMBLY_EXCEPTION
%doc %{_jvmdir}/%{sdkdir}/LICENSE
%doc %{_jvmdir}/%{sdkdir}/THIRD_PARTY_README
%dir %{_jvmdir}/%{sdkdir}
%{_jvmdir}/%{jrelnk}
%{_jvmjardir}/%{jrelnk}
%{_jvmprivdir}/*
%{jvmjardir}
%dir %{_jvmdir}/%{jredir}/lib/security
%{_jvmdir}/%{jredir}/lib/security/cacerts
%dir %{_jvmdir}/%{jredir %%1}/lib/security/policy/unlimited/
%dir %{_jvmdir}/%{jredir %%1}/lib/security/policy/limited/
%dir %{_jvmdir}/%{jredir %%1}/lib/security/policy/
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/policy/unlimited/US_export_policy.jar
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/policy/unlimited/local_policy.jar
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/policy/limited/US_export_policy.jar
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/policy/limited/local_policy.jar
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/java.policy
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/java.security
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/blacklisted.certs
%config(noreplace) %{_jvmdir}/%{jredir}/lib/logging.properties
%{_datadir}/icons/hicolor/*x*/apps/java-%{javaver}.png
%{_mandir}/man1/java-%{uniquesuffix}.1*
%{_mandir}/man1/keytool-%{uniquesuffix}.1*
%{_mandir}/man1/orbd-%{uniquesuffix}.1*
%{_mandir}/man1/pack200-%{uniquesuffix}.1*
%{_mandir}/man1/rmid-%{uniquesuffix}.1*
%{_mandir}/man1/rmiregistry-%{uniquesuffix}.1*
%{_mandir}/man1/servertool-%{uniquesuffix}.1*
%{_mandir}/man1/tnameserv-%{uniquesuffix}.1*
%{_mandir}/man1/unpack200-%{uniquesuffix}.1*
%config(noreplace) %{_jvmdir}/%{jredir}/lib/security/nss.cfg
%ifarch %{jit_arches}
%attr(444, root, root) %ghost %{_jvmdir}/%{jredir}/lib/%{archinstall}/server/classes.jsa
%attr(444, root, root) %ghost %{_jvmdir}/%{jredir}/lib/%{archinstall}/client/classes.jsa
%endif
%{_jvmdir}/%{jredir}/lib/%{archinstall}/server/
%{_jvmdir}/%{jredir}/lib/%{archinstall}/client/
%{_sysconfdir}/.java/
%{_sysconfdir}/.java/.systemPrefs


%files devel
%defattr(-,root,root,-)
%doc %{_jvmdir}/%{sdkdir}/ASSEMBLY_EXCEPTION
%doc %{_jvmdir}/%{sdkdir}/LICENSE
%doc %{_jvmdir}/%{sdkdir}/THIRD_PARTY_README
%dir %{_jvmdir}/%{sdkdir}/bin
%dir %{_jvmdir}/%{sdkdir}/include
%dir %{_jvmdir}/%{sdkdir}/lib
%ifarch %{jit_arches}
%dir %{_jvmdir}/%{sdkdir}/tapset
%endif
%{_jvmdir}/%{sdkdir}/bin/*
%{_jvmdir}/%{sdkdir}/include/*
%{_jvmdir}/%{sdkdir}/lib/*
%ifarch %{jit_arches}
%{_jvmdir}/%{sdkdir}/tapset/*.stp
%endif
%{_jvmdir}/%{sdklnk}
%{_jvmjardir}/%{sdklnk}
%{_datadir}/applications/*jconsole.desktop
%{_datadir}/applications/*policytool.desktop
%{_mandir}/man1/appletviewer-%{uniquesuffix}.1*
%{_mandir}/man1/apt-%{uniquesuffix}.1*
%{_mandir}/man1/extcheck-%{uniquesuffix}.1*
%{_mandir}/man1/idlj-%{uniquesuffix}.1*
%{_mandir}/man1/jar-%{uniquesuffix}.1*
%{_mandir}/man1/jarsigner-%{uniquesuffix}.1*
%{_mandir}/man1/javac-%{uniquesuffix}.1*
%{_mandir}/man1/javadoc-%{uniquesuffix}.1*
%{_mandir}/man1/javah-%{uniquesuffix}.1*
%{_mandir}/man1/javap-%{uniquesuffix}.1*
%{_mandir}/man1/jconsole-%{uniquesuffix}.1*
%{_mandir}/man1/jcmd-%{uniquesuffix}.1*
%{_mandir}/man1/jdb-%{uniquesuffix}.1*
%{_mandir}/man1/jhat-%{uniquesuffix}.1*
%{_mandir}/man1/jinfo-%{uniquesuffix}.1*
%{_mandir}/man1/jmap-%{uniquesuffix}.1*
%{_mandir}/man1/jps-%{uniquesuffix}.1*
%{_mandir}/man1/jrunscript-%{uniquesuffix}.1*
%{_mandir}/man1/jsadebugd-%{uniquesuffix}.1*
%{_mandir}/man1/jstack-%{uniquesuffix}.1*
%{_mandir}/man1/jstat-%{uniquesuffix}.1*
%{_mandir}/man1/jstatd-%{uniquesuffix}.1*
%{_mandir}/man1/native2ascii-%{uniquesuffix}.1*
%{_mandir}/man1/policytool-%{uniquesuffix}.1*
%{_mandir}/man1/rmic-%{uniquesuffix}.1*
%{_mandir}/man1/schemagen-%{uniquesuffix}.1*
%{_mandir}/man1/serialver-%{uniquesuffix}.1*
%{_mandir}/man1/wsgen-%{uniquesuffix}.1*
%{_mandir}/man1/wsimport-%{uniquesuffix}.1*
%{_mandir}/man1/xjc-%{uniquesuffix}.1*
%ifarch %{jit_arches}
%{tapsetroot}
%endif

%files demo -f %{name}-demo.files
%defattr(-,root,root,-)
%doc %{_jvmdir}/%{sdkdir}/LICENSE

%files src
%defattr(-,root,root,-)
%doc README.src
%{_jvmdir}/%{sdkdir}/src.zip

%files javadoc
%defattr(-,root,root,-)
%doc %{_javadocdir}/%{name}
%doc %{buildoutputdir}/j2sdk-image/jre/LICENSE

%changelog
* Fri Aug 23 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.231-2.6.19.2
- Fix crash in Class.forName0
- Resolves: rhbz#1698274

* Tue Jul 16 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.231-2.6.19.1
- Add missing hyphen in tapset filename.
- Resolves: rhbz#1724452

* Tue Jul 16 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.231-2.6.19.0
- Update tapset name in patch.
- Resolves: rhbz#1724452

* Tue Jul 16 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.231-2.6.19.0
- Bump to 2.6.19 (including tapsets) and OpenJDK 7u231-b01.
- Fix fsg.sh to fail if patching fails.
- Resolves: rhbz#1724452

* Tue Apr 16 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.221-2.6.18.0
- Bump to 2.6.18 and OpenJDK 7u221-b02.
- Resolves: rhbz#1693468

* Wed Feb 27 2019 Severin Gehwolf <sgehwolf@redhat.com> - 1:1.7.0.211-2.6.17.1
- Produce debug symbols for libpulse-java.so
- Set IT_CFLAGS=-g so that debug symbols for the pulse audio
- native library are being produced. This is needed to fix
- rpmdiff errors of missing .debug_info in pulse-java.so.debug.
- Resolves: rhbz#1661577

* Mon Feb 25 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.211-2.6.17.0
- Bump to 2.6.17.
- Adjust jdk8076221-pr2809-disable_rc4_cipher_suites.patch to apply after 8211883
- Resolves: rhbz#1661577

* Thu Feb 21 2019 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.201-2.6.17pre01.0
- Bump to 2.6.17pre01.
- Add support for icedtea_snapshot so we can build pre-releases.
- Resolves: rhbz#1661577

* Mon Oct 22 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.201-2.6.16.0
- Bump to 2.6.16 and u201b00.
- Update 8076221/PR2809 (disable RC4) to apply after 8208350 (disable DES)
- Resolves: rhbz#1633817

* Sun Jul 22 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.191-2.6.15.4
- Bump to revised 2.6.15 tarball with PR3616 -notimestamp javadoc fix
- Resolves: rhbz#1594249

* Thu Jul 19 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.191-2.6.15.3
- Bump to revised 2.6.15 tarball with jdk7u191-b01
- Resolves: rhbz#1594249

* Mon Jul 16 2018 Severin Gehwolf <sgehwolf@redhat.com> - 1:1.7.0.191-2.6.15.2
- Fix hook to show hs_err*.log files on failures.
- Resolves: rhbz#1594249

* Mon Jul 16 2018 Severin Gehwolf <sgehwolf@redhat.com> - 1:1.7.0.191-2.6.15.2
- Fix requires/provides filters for internal libs. See RHBZ#1590796
- Resolves: rhbz#1594249

* Wed Jul 11 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.191-2.6.15.1
- Bump to revised 2.6.15 tarball with PR3604
- Resolves: rhbz#1594249

* Tue Jul 03 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.191-2.6.15.0
- Bump to 2.6.15 and u191b00.
- Drop PR3608/RH1566890/CVE-2018-3639 patch now applied upstream.
- Resolves: rhbz#1594249

* Tue Jul 03 2018 Severin Gehwolf <sgehwolf@redhat.com> - 1:1.7.0.181-2.6.14.12
- Add hook to show hs_err*.log files on failures.
- Resolves: rhbz#1594249

* Tue Jul 03 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.181-2.6.14.12
- Introduce stapinstall variable to set SystemTap arch directory correctly (e.g. arm64 on aarch64)
- ABS_JAVA_HOME_DIR is no longer used in the latest tapsets
- Resolves: rhbz#1594249

* Tue Jul 03 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.181-2.6.14.12
- Cleanup RH1566890 patch and differentiate from java-1.8.0-openjdk version.
- Resolves: rhbz#1594249

* Wed Jun 20 2018 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.181-2.6.14.12
- jsa files changed to 444 to pass rpm verification
- Add reg-ex for filtering private libraries' provides/requires.
- Resolves: rhbz#1594249

* Tue May 22 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.181-2.6.14.11
- Fix patch files to appease git apply --stat
- Resolves: rhbz#1578551

* Thu Apr 26 2018 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.181-2.6.14.10
- added hooks for copy jdk configs
- Resolves: rhbz#1578551

* Thu Apr 26 2018 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.181-2.6.14.9
- added and applied 1566890_embargoed20180521.patch
- Resolves: rhbz#1578551

* Fri Apr 20 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.181-2.6.14.2
- Fix invalid license 'LGPL+' (should be LGPLv2+ for ECC code) and add missing ones
- Resolves: rhbz#1559766

* Thu Apr 19 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.181-2.6.14.1
- Bump to 2.6.14 and u181b00.
- Drop 8197981 Zero 32-bit patch now applied upstream.
- Update RC4 patch (8076221/PR2809) to apply after 8175075 (disable 3DES)
- Resolves: rhbz#1559766

* Thu Feb 15 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.171-2.6.13.1
- Update to new tarball with AArch64 return value fixes.
- Resolves: rhbz#1528233

* Tue Feb 13 2018 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.171-2.6.13.1
- Bump to 2.6.13 and u171b01.
- Update rh1648644-java_access_bridge_privlidged_security.patch to apply after 8186080
- Update RC4 patch (8076221/PR2809) to apply after 8148108 (DH lower limit increase)
- Fix file path in pr1834-rh1022017-reduce_ellipticcurvesextension_to_provide_only_three_nss_supported_nist_curves_23_24_25.patch.
- Resolves: rhbz#1528233

* Tue Nov 28 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.161-2.6.12.1
- Remove superfluous %%1 from policy JAR file path.
- Resolves: rhbz#1499207

* Tue Nov 28 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.161-2.6.12.1
- Update location of policy JAR files following 8157561.
- Resolves: rhbz#1499207

* Tue Nov 28 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.161-2.6.12.1
- Bump to 2.6.12 and u161b00.
- Update SystemTap tapsets to version in IcedTea 2.6.12pre01 to fix RH1492139.
- Drop 8185716 patch, now applied upstream.
- Update location of OpenJDK zlib system library source code in remove-intree-libraries.sh
- Fix name of SystemTap tarball, following update.
- Resolves: rhbz#1499207

* Wed Aug 02 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.151-2.6.11.1
- Bump to 2.6.11 and u151b00.
- Update java-access-bridge-security.patch to apply against 2.6.11.
- Apply fix for 8185716 so ppc uses correct ins_encode format
- Resolves: rhbz#1466509

* Wed May 03 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.141-2.6.10.2
- Bump to u141b02 to include S8011123 fix for TCK failure.
- Resolves: rhbz#1438751

* Thu Apr 27 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.141-2.6.10.1
- Bump to 2.6.10 and u141b00.
- Adjust RH1022017 following application of 8173783
- Add more detailed output to fsg.sh and generate_source_tarball.sh.
- Bump to u141b01 to include S8043723 fix for s390.
- Resolves: rhbz#1438751

* Tue Feb 07 2017 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.131-2.6.9.1
- Bump to 2.6.9 and u131b00.
- Remove patch application debris in fsg.sh.
- Re-generate PR2809 and RH1022017 against 2.6.9.
- Add blacklisted.certs to installation file list.
- Resolves: rhbz#1410612

* Tue Nov 01 2016 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.121-2.6.8.2
- New variable, @prefix@, needs to be substituted in tapsets (rhbz1371005)
- Resolves: rhbz#1381990

* Tue Nov 01 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.121-2.6.8.2
- Require a version of java-1.7.0-openjdk-devel with a working jar uf
- Remove unneeded AArch64 environment variable setting.
- Resolves: rhbz#1381990

* Fri Oct 28 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.121-2.6.8.1
- Bump to 2.6.8 and u121b00.
- Drop patches (S7081817, S8140344, S8145017 and S8162344) applied upstream.
- Require at least the build-time version of NSS at run-time due to static linking.
- Resolves: rhbz#1381990

* Fri Jul 22 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.111-2.6.7.3
- Bump to jdk7u111 b01 to fix TCK regressions (7081817 & 8162344)
- Resolves: rhbz#1350040

* Thu Jul 21 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.111-2.6.7.2
- Reset permissions of resources.jar to avoid it only being readable by root (PR1437).
- Resolves: rhbz#1350040

* Wed Jul 20 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.111-2.6.7.1
- Bump to 2.6.7 and u111b00.
- Update SystemTap bundle with fix for PR3091/RH1204159
- Drop patches (PR2938 (ttable_match_7) and PR2939 (fontpath)) applied upstream.
- Resolves: rhbz#1350040

* Tue Apr 19 2016 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.101-2.6.6.1
- added Patch666 fontpath.patch to fix tck regressions
- Resolves: rhbz#1325426

* Mon Apr 18 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.101-2.6.6.1
- Fix ztos handling in templateTable_ppc_64.cpp to be same as others in 7.
- Resolves: rhbz#1325426

* Mon Apr 18 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.101-2.6.6.1
- Bump to 2.6.6 and u101b00.
- Drop a leading zero from the priority as the update version is now three digits
- Update PR2809 patch to apply against 2.6.6.
- Resolves: rhbz#1325426

* Thu Mar 24 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.99-2.6.5.1
- Bump to 2.6.5 and u99b00.
- Correct check for fsg.sh in tarball creation script
- Remove patches added for RH1183014 which are now upstream in 2.6.5/7u99.
- Resolves: rhbz#1320657

* Tue Feb 23 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.95-2.6.4.4
- Enable building against libsctp, now RH1242484 is resolved.
- Resolves: rhbz#1242510

* Tue Feb 23 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.95-2.6.4.4
- Allow specifying an address to bind JMX remote connector.
- Resolves: rhbz#1183014

* Wed Jan 27 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.95-2.6.4.3
- Disable RC4 by default.
- Resolves: rhbz#1217132

* Tue Jan 26 2016 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.95-2.6.4.2
- added java-devel group of provides
- Resolves: rhbz#1295767

* Tue Jan 19 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.95-2.6.4.1
- Remove reference to jre/lib/audio.
- Resolves: rhbz#1295767

* Tue Jan 19 2016 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.95-2.6.4.1
- Bump to 2.6.4 and u95b00.
- Backport tarball creation script from OpenJDK 8 RPMs and update fsg.sh to work with it.
- Drop 8072932or8074489 patch as applied upstream in u91b01.
- Drop installation of soundfont symlink following inclusion of 8140620/PR2710 in 2.6.3
- Resolves: rhbz#1295767

* Tue Nov 10 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.91-2.6.2.4
- Require Rhino 1.7R4 to resolve bug 1244351
- Resolves: rhbz#1271920

* Tue Oct 20 2015 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.91-2.6.2.3
- added and applied patch500 8072932or8074489.patch to fix tck failure
- Resolves: rhbz#1271920

* Mon Oct 19 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.91-2.6.2.1
- Bump to 2.6.2 and u91b00.
- Drop PR2568/RH1248530 backport now applied upstream.
- Resolves: rhbz#1271920

* Fri Aug 21 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.85-2.6.1.4
- Backport PR2568.
- Resolves: rhbz#1248530

* Mon Jul 13 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.85-2.6.1.3
- libsctp is not available on all versions of RHEL 6.
- Resolves: rhbz#1235157

* Sat Jul 11 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.85-2.6.1.2
- Bump upstream tarball to u25b01 to fix issue with 8075374 backport.
- Resolves: rhbz#1235157

* Thu Jul 09 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.85-2.6.1.1
- Update OpenJDK tarball so correct version is used.
- Resolves: rhbz#1235157

* Thu Jul 09 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.85-2.6.1.0
- Bump to 2.6.1 and u85b00.
- Resolves: rhbz#1235157

* Wed Jul 08 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.80-2.6.0.0
- Revert addition of LCMS removal as RHEL < 7 does not have LCMS 2.
- Resolves: rhbz#1235157

* Wed Jul 08 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.80-2.6.0.0
- Bump to 2.6.0 and u80b32.
- Drop upstreamed patches and separate AArch64 HotSpot.
- Add dependencies on pcsc-lite-devel (PR2496) and lksctp-tools-devel (PR2446)
- Only run -Xshare:dump on JIT archs other than power64 as port lacks support
- Update remove-intree-libraries script to cover LCMS and PCSC headers.
- Resolves: rhbz#1235157

* Wed May 27 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.4
- Bump release so version is newer than fix for 1190835 in 6.6.z.
- Resolves: rhbz#1190835

* Fri May 01 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Use installed directory in check section and remove duplicate tests in build
- Resolves: rhbz#1190835

* Fri May 01 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Revise PR2323 to account for different glibconfig.h define used on RHEL 6
- Resolves: rhbz#1190835

* Thu Apr 30 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Revise PR2323 to use header defines to mark whether GLib types have been defined or not
- Resolves: rhbz#1190835

* Thu Apr 30 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Apply PR2323 to fix building of networking support with system GConf on and system GIO off
- Resolves: rhbz#1190835

* Thu Apr 30 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Add build dependency on redhat-lsb-core to provide lsb_release for jdk_generic_profile.sh
- Resolves: rhbz#1190835

* Thu Apr 30 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Add build dependency on GConf2-devel for native proxy support.
- Remove outdated dependencies on mercurial, redhat-lsb and libxslt from IcedTea builds.
- Remove python dependency introduced for rpath rewrite script, which has now been removed.
- Resolves: rhbz#1190835

* Wed Apr 29 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.3
- Add backports of PR2233, PR2161, PR1661 (GConf changeset) and PR2320 from IcedTea 2.6.x
- No longer set SYSTEM_GIO to false as we can link against it now GSettings is not required
- Add test case to ensure file type detection works
- Correct bug ID in comment associated with PStack patch
- Resolves: rhbz#1190835

* Fri Apr 24 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.2
- Fix regression of S4890063
- Resolves: rhbz#1214835

* Fri Apr 10 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.1
- Revert change to jit_arches line
- Resolves: rhbz#1209071

* Fri Apr 10 2015 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.79-2.5.5.1
- repacked sources
- Resolves: rhbz#1209071

* Tue Apr 07 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.79-2.5.5.0
- Bump to 2.5.5 using OpenJDK 7u79 b14.
- Resolves: rhbz#1209071

* Fri Jan 09 2015 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.75-2.5.4.0
- Bump to 2.5.4 using OpenJDK 7u75 b13.
- Remove upstreamed patches for RH1146622, RH1168693, PR2123, PR2135
- Fix rh1648241-rh1648241-abrt_friendly_hs_log_jdk7.patch to apply again.
- Resolves: rhbz#1180296
- Resolves: rhbz#1146622
- Resolves: rhbz#1168693
- Resolves: rhbz#1176718

* Fri Dec 12 2014 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.71-2.5.3.8
- added and applied patch407, bug1146622-fix.patch
- Resolves: rhbz#1146622

* Wed Dec 10 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.8
- Fix race condition when using system NSS and SunEC provider
- Resolves: rhbz#1121211

* Fri Dec 05 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.7
- Fix crashes when using system NSS and SunEC provider
- Update sun.security.ec.NamedCurve to list only curves included in NSS.
- Resolves: rhbz#1121211

* Mon Dec 01 2014 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.71-2.5.3.6
- removed source14 remove-origin-from-rpaths (11690970)
- removed build requirement  for chrpath
- Resolves: rhbz#1168693

* Fri Nov 28 2014 Jiri Vanek <jvanek@redhat.com> - 1:1.7.0.71-2.5.3.5
- backported upstreamed patch http://icedtea.classpath.org/hg/icedtea7-forest/hotspot/rev/e975b826e8f5
- added and applied patch404 1168693-hotspot.patch
- Resolves: rhbz#1168693

* Thu Nov 06 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.4
- Enable SunEC provider using system NSS
- Resolves: rhbz#1121211

* Fri Oct 24 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.3
- Revert to depending on java-1.7.0-openjdk
- Resolves: rhbz#1153058

* Fri Oct 24 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.2
- Depend on java-1.6.0-openjdk instead of 1.7, as it is present for ppc64.
- Resolves: rhbz#1153058

* Fri Oct 24 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.2
- Include ppc64be in ExclusiveArch
- Resolves: rhbz#1153058

* Fri Oct 24 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.2
- Bump release for first build on PPC64
- Resolves: rhbz#1153058

* Thu Oct 02 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.71-2.5.3.1
- Bump to 2.5.3 with security updates.
- Resolves: rhbz#1148892

* Tue Sep 30 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1:1.7.0.65-2.5.3pre01.1
- Bump to 2.5.3pre01.
- Remove obsolete patches, which are now included upstream.
- Disable LCMS via environment variables rather than maintaining a patch.
- Resolves: rhbz#1145848

* Mon Jul 14 2014 Jiri Vanek  <jvanek@redhat.com> - 1.7.0.65-2.5.1.2
- added and applied fix for samrtcard io patch405, pr1864_smartcardIO.patch
- Resolves: rhbz#1115875

* Mon Jul 07 2014 Jiri Vanek  <jvanek@redhat.com> - 1.7.0.65-2.5.1.1.el6
- updated to security patched icedtea7-forest 2.5.1
- Resolves: rhbz#1115875

* Wed Jul 02 2014 Jiri Vanek  <jvanek@redhat.com> - 1.7.0.60-2.5.0.1.el6
- update to icedtea7-forest 2.5.0
- Resolves: rhbz#1114936

* Fri Jun 06 2014 Omair Majid <omajid@redhat.com> - 1.7.0.51-2.4.7.5.el6
- Work when capabilities are set on the binary
- Include hardcoded install path as well as $ORIGIN in RPATH
- Resolves: rhbz#1105293

* Thu May 22 2014 Jiri Vanek <jvanek@redhat.com> - 1.7.0.51-2.4.7.4.el6
- Debug turned off (0) and bumped release
- Resolves: rhbz#1092063

* Thu May 22 2014 Jiri Vanek <jvanek@redhat.com> - 1.7.0.51-2.4.7.3.el6
- bumped release
- changed  buildoutputdir to contains "-debug" in case of debug on
- rewritten (long unmaintained) rh1648254-javadoc_generated_during_all_variants_of_buid.patch and 
  rh1648259-libsaproc_libjsig_compiled_with_g_to_provide_correct_debuginfo.patch
- debug turned on (1)
- Resolves: rhbz#1092063

* Wed May 21 2014 Andrew Hughes <gnu.andrew@redhat.com> - 1.7.0.55-2.4.7.2
- Fix jinfo behaviour when prelink cache is present
- Resolves: rhbz#1064383

* Mon Apr 07 2014 Jiri Vanek <jvanek@redhat.com> - 1.7.0.51-2.4.7.1.el6
- regenerated sources to fix TCK failure
- Resolves: rhbz#1085003

* Mon Apr 07 2014 Jiri Vanek <jvanek@redhat.com> - 1.7.0.51-2.4.7.0.el6
- bumped to future icedtea-forest 2.4.7
- updatever set to 55, buildver se to 13, release reset to 0
- removed upstreamed patch402 gstackbounds.patch
- removed BuildRequires on pulseaudio >= 0.9.1, devel is enough
- removed Requires: rhino, BuildRequires is enough
- added JRE_RELEASE_VERSION and ALT_PARALLEL_COMPILE_JOBS
- fixed FT2_CFLAGS and FT2_LIBS
- ppc64 repalced by power64 macro
- patch111 applied as dry-run (6.5 forward port)
- Resolves: rhbz#1085003

* Fri Jan 10 2014 Jiri Vanek <jvanek@redhat.com> - 1.7.0.51-2.4.4.1.el6
- restored java7 provides
- bumped release (builds exists)
- Resolves: rhbz#1030634

* Fri Jan 10 2014 Jiri Vanek <jvanek@redhat.com> - 1.7.0.51-2.4.4.0.el6
- updated to security icedtea 2.4.4
 - icedtea_version set to 2.4.4
 - updatever bumped to       51
 - release reset to 0
- sync with fedora
 - added and applied patch411 1029588.patch (rh 1029588)
 - added aand applied patch410, 1015432 (rh 1015432)
- Resolves: rhbz#1050936

* Thu Oct 10 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.3.1.el6
- security update to new icedtea 2.4.3  (u45, b15)
- Resolves:rhbz#1017627

* Thu Oct 10 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.3.0.el6
- security update to icedtea 2.4.3  (u45, b15)
- removed unnecessary revert patch404: RH661505-toBeReverted.patch
- get rid of unaplied patch110 java-1.7.0-openjdk-nss-icedtea-e9c857dcb964.patch
- Resolves:rhbz#1017627

* Fri Oct 04 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.2.5.el6
- another tapset fix 
- Resolves:rhbz#825824

* Thu Oct 03 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.2.4.el6
- renamed tapset source to be "versioned"
- improved tapset handling
- Resolves: rhbz#825824

* Wed Oct 02 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.2.3.el6
- updated tapset to current head
- Resolves: rhbz#825824

* Wed Sep 11 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.2.2.el6
- NSS_LIBDIR variable replaced by macro initialised via  shell script
- Resolves: rhbz#978423

* Wed Sep 11 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.40-2.4.2.1.el6
- buildver replaced by updatever
- buildver reset to 60
- updatever set to 40
- added   JDK_BUILD_NUMBER=b`printf "%02d" buildver to make parameters
- buildversion included in id
- desktop icons extracted to text files
- Resolves: rhbz#978423

* Mon Sep 09 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.60-2.4.2.0.el6
- updated to icedtea7-forest 2.4.2 + aprtial sync with fedoras
- removed unnecessary patch112 java-1.7.0-openjdk-doNotUseDisabledEcc.patch
- renamed patch103 java-1.7.0-openjdk-arm-fixes.patch to 
patch120: rh1648643-comment_out_freetype_check.patch
- adapted patch104 java-1.7.0-openjdk-ppc-zero-jdk.patch
- adapted patch105 java-1.7.0-openjdk-ppc-zero-hotspot.patch
- added patch404 RH661505-toBeReverted.patch, to be *reverted* during prep
- added source12, TestCryptoLevel.java to ensure used crypto
- ppc64 repalced by macro
- buildver bumbed to 60
- Resolves: rhbz#978423

* Fri Aug 16 2013 Omair Majid <omajid@redhat.com> - 1.7.0.25-2.4.1.0el6
- Make requires on nss arch-specific
- Resolves: rhbz#997633

* Wed Jul 03 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.25-2.4.1.4.el6
- updated to icedtea 2.4.1
- fsg.sh  moved form sources to repository
- all (where applicable) usages of patch command replaced by patch macro
- removed upstreamed  patch 401 657854-openjdk7.patch (see RH947731)
- adapted patch 402 gstackbounds.patch - see (RH902004)
- Resolves: rhbz#978423

* Wed Jun 05 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.20-2.4.0.pre7.4.el6
- improoved handling of patch111 - nss-config-2.patch
- Resolves: rhbz#831734

* Wed Jun 05 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.20-2.4.0.pre7.3.el6
- Backported "uniquesuffix" patch from f19
- Added client/server directories so they can be owned
- Added fix for RH857717, owned /etc/.java/ and /etc/.java/.systemPrefs
- Resolves: rhbz#831734

* Wed May 29 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.20-2.4.0.pre7.2.el6
- added client/server directories so they can be owened
- Resolves: rhbz#831734

* Thu May 23 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.20-2.4.0.pre7.0.el6
- sync to latest 2.4 branch (fixing latest CPU)
- enabled nss
- Resolves: rhbz#831734

* Tue May 07 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.20-2.4.0.pre6.0.el6
- sync to latest 2.4 branch
- not added systemtap.patch as patch 302 (see RH905017) - upstreamed
- build requirements of jdk restricted to java7-devel-openjdk >= 1:1.6.0 (see RH953886)
- added patch 401 657854-openjdk7.patch (see RH947731)
- fixed icons (see https://bugzilla.redhat.com/show_bug.cgi?id=820619)
- now providing 'java' while keeping devel at 'java7-devel  (see RH916288)
- removed unnecessary bootstrap
- added patch 200 rh1648241-rh1648241-abrt_friendly_hs_log_jdk7.patch
- added patch 402 gstackbounds.patch - see (RH902004)
- added patch 403 PStack-808293.patch - to work more about jstack
- still not providing latest CPU fixes
- added client to ghosted classes.jsa
- Resolves: rhbz#916288

* Wed Apr 10 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.3.4.0.pre4.7.el6
- Added latest Fedora spec changes
- Bumped release
- Removed patch2 java-1.7.0-openjdk-java-access-bridge-idlj.patch (unapplied)
- zlib in BuildReq restricted for  1.2.3-7 or higher
 - see https://bugzilla.redhat.com/show_bug.cgi?id=904231
- Removed a -icedtea tag from the version
  - package have less and less connections to icedtea7
- Added gcc-c++ build dependence. Sometimes caused troubles during rpm -bb
- Added (Build)Requires for fontconfig and xorg-x11-fonts-Type1
  - see https://bugzilla.redhat.com/show_bug.cgi?id=721033 for details
- Removed all fonconfig files. Fonts are now handled differently in JDK 
  and those files are redundant. This is going to be usptreamed.
  - see https://bugzilla.redhat.com/show_bug.cgi?id=902227 for details
- logging.properties marked as config(noreplace)
  - see https://bugzilla.redhat.com/show_bug.cgi?id=679180 for details
- classes.jsa marked as ghost on full path
  - see https://bugzilla.redhat.com/show_bug.cgi?id=918172 for details
- nss.cfg was marked as config(noreplace)
- Add symlink to default soundfont (see 541466)
- Resolves: rhbz#950381

* Wed Apr 10 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.4.0.pre4.6.el6
- Disabled nss (enable_nss switch to 0)
- Resolves: rhbz#950381

* Thu Mar 28 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.4.0.pre4.5.el6
- Added and applied patch 116 - Patch116: rh905128-non_block_ciphers.patch
- Resolves: rhbz#895034

* Tue Feb 19 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.4.0.pre4.3.el6
- Updated  to icedtea 2.4.0.pre4, 
- Rewritten patch3 rh1648644-java_access_bridge_privlidged_security.patch
- Resolves: rhbz#912257

* Fri Feb 15 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.4.0.pre2.3.el6
- Removed testing
 - mauve was outdated and
 - jtreg was icedtea relict
- Updated  to icedtea 2.4.0.pre2, updated?
- Added java -Xshare:dump to post (see 513605) fo jitarchs
- Resolves: rhbz#911530

* Wed Jan 23 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.11-2.4.0.2.el6
- Unapplied but kept (for 2.3revert) patch110,  java-1.7.0-openjdk-nss-icedtea-e9c857dcb964.patch
- Added and applied patch113: java-1.7.0-openjdk-aes-update_reset.patch
- Added and applied patch114: java-1.7.0-openjdk-nss-tck.patch
- Added and applied patch115: java-1.7.0-openjdk-nss-split_results.patch
- NSS enabled by default - enable_nss set to 1
- rewritten patch109 - java-1.7.0-openjdk-nss-config-1.patch
- rewritten patch111 - java-1.7.0-openjdk-nss-config-2.patch
- Resolves: rhbz#831734

* Mon Jan 14 2013 Jiri Vanek <jvanek@redhat.com> - 1.7.0.11-2.4.0.1.el6
- Rewritten patch105: java-1.7.0-openjdk-disable-system-lcms.patch
- Added jxmd and idlj to alternatives
- make executed with   DISABLE_INTREE_EC=true and UNLIMITED_CRYPTO=true
- Unapplied patch302 and deleted systemtap.patch
- buildver increased to 11
- icedtea_version set to 2.4.0
- Added and applied patch112 java-1.7.openjdk-doNotUseDisabledEcc.patch
- removed tmp-patches source tarball
- Added /lib/security/US_export_policy.jar and lib/security/local_policy.jar
- Disabled nss - enable_nss set to 0
- Resolves: rhbz#895034

* Fri Nov 30 2012 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.3.3.el6.2
- Added nss support (see 831733)
  -added  enable_nss variable, set to true - 1 as default
  -added and applied if enable_nss true patch108 java-1.7.0-openjdk-aes-buffering.patch
  -added and applied if enable_nss true patch109 java-1.7.0-openjdk-nss-config-1.patch
  -added and applied if enable_nss true patch111 java-1.7.0-openjdk-nss-config-2.patch
  -added and applied if enable_nss true patch110 java-1.7.0-openjdk-nss-icedtea-e9c857dcb964.patch
- openjdk-nss-config-2.patch, is dynamically modified after build time and is
  changing build dependence (nss last) to runtime depndecne (nss first)
- release tag moved before dist (see 875245)
- Resolves: rhbz#871771

* Wed Nov 28 2012 Jiri Vanek <jvanek@redhat.com> - 1.7.0.9-2.3.3.el6.1
- Sync with 6.3
- introduced tmp-patches source tarball
- Resolves: rhbz#871771

* Tue May 01 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.7
- Updated priority to be higher than GCJ but lower than OpenJDK6

* Sat Apr 28 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.6
- Added patch to fix GIO detection

* Wed Apr 18 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.5
- Fix global definition yet again

* Wed Apr 18 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.4
- Removed commented global declaration as RPM was NOT ignoring it

* Tue Apr 17 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.3
- Added ALT_STRIP_POLICY="no_strip" flag so that binaries are not stripped
- Collapsed if cases for x86
- Decreased priority
- Removed xalan and xerces reqs in favor of libxslt which is what we use

* Wed Apr 04 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.2
- Fixed DISTRO_NAME, DISTRO_PACKAGE_VERSION and JDK_UPDATE_VERSION
- Fixed umask

* Tue Mar 27 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6.1
- Synched with 7.0 branch
- Removed unnecessary unsetting of USE_SYSTEM_LCMS
- Added SystemTap fixes from Mark Wielaard

* Wed Mar 21 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.el6
- Imported from Fedora into RHEL 6.3 branch
- Removed unused macros
- Removed rh740762 patch (removed from Fedora now too)
- Disabled system lcms (not available in RHEL6)
- Updated virtual provides to provide "7" specific items
- Made exclusive arch for i686 and x86_64

* Mon Mar 12 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.fc17.2
- Resolved rhbz#740762: java.library.path is missing some paths
- Unified spec file for x86, x86_64, ARM and s390
  - Integrated changes from Dan Horák <dhorak@redhat.com> for Zero/s390
  - Integrated changes from Chris Phillips <chphilli@redhat.com> for Zero/ARM

* Fri Feb 24 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1.fc17.1
- Added flag so that debuginfo is built into classfiles (rhbz# 796400)
- Updated rh1649777-add_rhino_support_jdk7.patch to build scripting support (rhbz# 796398)

* Tue Feb 14 2012 Deepak Bhole <dbhole@redhat.com> - 1.7.0.3-2.1
- Updated to OpenJDK7u3/IcedTea7 2.1
- Removed upstreamed glibc nameclash patch
- Added patch to remove the -mimpure option to gcc
- Security fixes:
  - S7112642, CVE-2012-0497: Incorrect checking for graphics rendering object
  - S7082299, CVE-2011-3571: AtomicReferenceArray insufficient array type check
  - S7110687, CVE-2012-0503: Unrestricted use of TimeZone.setDefault
  - S7110700, CVE-2012-0505: Incomplete info in the deserialization exception
  - S7110683, CVE-2012-0502: KeyboardFocusManager focus stealing
  - S7088367, CVE-2011-3563: JavaSound incorrect bounds check
  - S7126960, CVE-2011-5035: Add property to limit number of request headers to the HTTP Server
  - S7118283, CVE-2012-0501: Off-by-one bug in ZIP reading code
  - S7110704, CVE-2012-0506: CORBA fix
- Add patch to fix compilation with GCC 4.7

* Fri Jan 13 2012 Fedora Release Engineering <rel-eng@lists.fedoraproject.org> - 1:1.7.0.1-2.0.3.1
- Rebuilt for https://fedoraproject.org/wiki/Fedora_17_Mass_Rebuild

* Tue Nov 08 2011 Deepak Bhole <dbhole@redhat.com> - 1.7.0.1-2.0.3
- Added patch to fix bug in jdk_generic_profile.sh
- Compile with generic profile to use system libraries
- Made remove-intree-libraries.sh more robust
- Added lcms requirement
- Added patch to fix glibc name clash
- Updated java version to include -icedtea

* Sun Nov 06 2011 Deepak Bhole <dbhole@redhat.com> - 1.7.0.1-2.0.2
- Added missing changelog entry
- Updated Provides

* Sun Nov 06 2011 Deepak Bhole <dbhole@redhat.com> - 1.7.0.1-2.0.1
- Updated to IcedTea 2.0 tag in the IcedTea OpenJDK7 forest
- Removed obsoleted patches
- Added system timezone support
- Revamp version/release naming scheme to make it proper
- Security fixes
  - S7000600, CVE-2011-3547: InputStream skip() information leak
  - S7019773, CVE-2011-3548: mutable static AWTKeyStroke.ctor
  - S7023640, CVE-2011-3551: Java2D TransformHelper integer overflow
  - S7032417, CVE-2011-3552: excessive default UDP socket limit under SecurityManager
  - S7046823, CVE-2011-3544: missing SecurityManager checks in scripting engine
  - S7055902, CVE-2011-3521: IIOP deserialization code execution
  - S7057857, CVE-2011-3554: insufficient pack200 JAR files uncompress error checks
  - S7064341, CVE-2011-3389: HTTPS: block-wise chosen-plaintext attack against SSL/TLS (BEAST)
  - S7070134, CVE-2011-3558: HotSpot crashes with sigsegv from PorterStemmer
  - S7077466, CVE-2011-3556: RMI DGC server remote code execution
  - S7083012, CVE-2011-3557: RMI registry privileged code execution
  - S7096936, CVE-2011-3560: missing checkSetFactory calls in HttpsURLConnection

* Mon Aug 29 2011 Deepak Bhole <dbhole@redhat.com> - 1.7.0.0-0.1.20110823.1
- Provide a "7" version of items to enfore F-16 policy of no Java 7 builds
- Resolves: rhbz#728706,  patch from Ville Skyttä <ville.skytta at iki dot fi>

* Fri Aug 05 2011 Deepak Bhole <dbhole@redhat.com> - 1.7.0.0-0.1.20110803
- Use a newer snapshot and forest on classpath.org rather than on openjdk.net
- Added in-tree-removal script to remove libraries that we manually link
- Updated snapshots
- Added DISTRO_NAME and FreeType header/lib locations
- Removed application of patch100 and patch 113 (now in forest)

* Wed Aug 03 2011 Deepak Bhole <dbhole@redhat.com> - 1.7.0.0-0.1.20110729
- Initial build from java-1.6.0-openjdk RPM
