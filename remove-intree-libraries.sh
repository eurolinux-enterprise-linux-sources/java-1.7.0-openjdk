#!/bin/sh

ZIP_SRC=openjdk/jdk/src/share/native/java/util/zip/zlib
JPEG_SRC=openjdk/jdk/src/share/native/sun/awt/image/jpeg/jpeg-6b
GIF_SRC=openjdk/jdk/src/share/native/sun/awt/giflib
PNG_SRC=openjdk/jdk/src/share/native/sun/awt/libpng
PCSC_SRC=openjdk/jdk/src/solaris/native/sun/security/smartcardio/MUSCLE

echo "Removing built-in libs (they will be linked)"

echo "Removing zlib"
if [ ! -d ${ZIP_SRC} ]; then
	echo "${ZIP_SRC} does not exist. Refusing to proceed."
	exit 1
fi	
rm -rvf ${ZIP_SRC}

echo "Removing libjpeg"
if [ ! -f ${JPEG_SRC}/jdhuff.c ]; then # some file that sound definitely exist
	echo "${JPEG_SRC} does not contain jpeg sources. Refusing to proceed."
	exit 1
fi	

rm -rvf ${JPEG_SRC}

echo "Removing giflib"
if [ ! -d ${GIF_SRC} ]; then
	echo "${GIF_SRC} does not exist. Refusing to proceed."
	exit 1
fi	
rm -rvf ${GIF_SRC}

echo "Removing libpng"
if [ ! -d ${PNG_SRC} ]; then
	echo "${PNG_SRC} does not exist. Refusing to proceed."
	exit 1
fi	
rm -rvf ${PNG_SRC}

echo "Removing libpcsc headers"
if [ ! -d ${PCSC_SRC} ]; then
	echo "${PCSC_SRC} does not exist. Refusing to proceed."
	exit 1
fi	
rm -rvf ${PCSC_SRC}
