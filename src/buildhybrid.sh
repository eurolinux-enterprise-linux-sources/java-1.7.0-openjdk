#!/bin/sh
# check we have a simulator tree
if [ ! -d ../simulator ] ; then
  echo "downloading aarch64 simulator code from sourceforge into directory ../simulator"
  (cd .. ; hg clone http://hg.code.sourceforge.net/p/smallaarch64sim/code simulator)
fi

# check we have a binutils tree

if [ ! -d ../binutils ] ; then
  echo "downloading aarch64 binutils code from sourceforge into directory ../binutils"
  echo "by executing the following command"
  (cd .. ; hg clone http://hg.code.sourceforge.net/p/binutilsaarch64/code binutils)
fi

# ensure the sim lib has been built
if [ ! -f ../simulator/libarmsim.so ] ; then
  (cd ../simulator ; make)
fi

# ensure the hsdis lib has been built

if [ ! -f hotspot/src/share/tools/hsdis/build/linux-amd64/hsdis-aarch64.so ] ; then
  (export BINUTILS=`cd .. ; pwd`/binutils ; cd hotspot/src/share/tools/hsdis ; make BUILD_AARCH64=true)
  mv hotspot/src/share/tools/hsdis/build/linux-amd64/hsdis-amd64.so hotspot/src/share/tools/hsdis/build/linux-amd64/hsdis-aarch64.so
fi

unset JAVA_HOME
export LANG=C

set -x

if [ x"$JDK_TO_BUILD_WITH" == x ] ; then
JDK_TO_BUILD_WITH=/usr/lib/jvm/java-1.7.0
fi

source ./jdk/make/jdk_generic_profile.sh

make \
BUILTIN_SIM="true" \
ALLOW_DOWNLOADS="true" \
ALT_JDK_IMPORT_PATH="$JDK_TO_BUILD_WITH" \
ALT_BOOTDIR="$JDK_TO_BUILD_WITH" \
ANT="/usr/bin/ant" \
FT2_CFLAGS="$(pkg-config --cflags freetype2)" \
FT2_LIBS="$(pkg-config --libs freetype2)" \
STATIC_CXX="false" \
NO_DOCS="true" \
DEBUG_CLASSFILES="true" \
DEBUG_BINARIES="true" \
STRIP_POLICY=no_strip \
HOTSPOT_BUILD_JOBS=8 debug_build $*

# ensure hsdis lib is installed
if [ ! -f build/linux-amd64-debug/j2sdk-image/jre/lib/amd64/hsdis-aarch64.so -a \
      -d  build/linux-amd64-debug/j2sdk-image/jre/lib/amd64 ] ; then
  cp hotspot/src/share/tools/hsdis/build/linux-amd64/hsdis-aarch64.so \
     build/linux-amd64-debug/j2sdk-image/jre/lib/amd64/hsdis-aarch64.so
  cp hotspot/src/share/tools/hsdis/build/linux-amd64/hsdis-aarch64.so \
     build/linux-amd64-debug/j2sdk-server-image/jre/lib/amd64/hsdis-aarch64.so
fi
