# ensure the hsdis lib has been built

if [ ! -f hotspot/src/share/tools/hsdis/build/linux-aarch64/hsdis-aarch64.so ] ; then
  (export BINUTILS=`cd .. ; pwd`/binutils-2.23.52 ; cd hotspot/src/share/tools/hsdis ; make)
fi

unset JAVA_HOME
export LANG=C

set -x

if [ x"$JDK_TO_BUILD_WITH" == x ] ; then
JDK_TO_BUILD_WITH=/usr/lib/jvm/java-1.7.0
fi

source ./jdk/make/jdk_generic_profile.sh

make \
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
if [ ! -f build/linux-aarch64-debug/j2sdk-image/jre/lib/aarch64/hsdis-aarch64.so -a \
      -d  build/linux-aarch64-debug/j2sdk-image/jre/lib/aarch64 ] ; then
  cp hotspot/src/share/tools/hsdis/build/linux-aarch64/hsdis-aarch64.so \
     build/linux-aarch64-debug/j2sdk-image/jre/lib/aarch64/hsdis-aarch64.so
  cp hotspot/src/share/tools/hsdis/build/linux-aarch64/hsdis-aarch64.so \
     build/linux-aarch64-debug/j2sdk-server-image/jre/lib/aarch64/hsdis-aarch64.so
fi
