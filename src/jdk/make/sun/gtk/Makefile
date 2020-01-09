#
# Copyright (c) 2002, 2013, Oracle and/or its affiliates. All rights reserved.
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

BUILDDIR = ../..
PACKAGE = sun.awt.X11
LIBRARY = javagtk
PRODUCT = sun

include $(BUILDDIR)/common/Defs.gmk

#
# Files
#
include FILES_c_unix.gmk
include FILES_export_unix.gmk
AUTO_FILES_JAVA_DIRS = sun/awt/X11


#
# Rules.
#
include $(BUILDDIR)/common/Mapfile-vers.gmk
include $(BUILDDIR)/common/Library.gmk

#
# Add to the ambient vpath to pick up files in subdirectories
#
vpath %.c   $(PLATFORM_SRC)/native/sun/awt
vpath %.c   $(SHARE_SRC)/native/sun/awt/debug

ifneq ($(SYSTEM_GTK), true)
vpath %.c   $(PLATFORM_SRC)/native/common/deps/gtk2
endif

OTHER_LDLIBS = -lX11

ifeq ($(SYSTEM_GTK), true)
  OTHER_LDLIBS += $(GTK_LIBS)
else
  OTHER_LDLIBS += $(LIBDL)
endif

ifeq  ($(PLATFORM), solaris)
CPPFLAGS += -DFUNCPROTO=15
dummy := $(shell $(MKDIR) -p $(LIB_LOCATION))
endif

CPPFLAGS += -DXAWT -DXAWT_HACK \
        -I$(TEMPDIR)/../../sun.awt/awt/CClassHeaders \
        -I$(SHARE_SRC)/native/sun/awt/debug \
        -I$(PLATFORM_SRC)/native/sun/awt

ifeq ($(SYSTEM_GTK), true)
  CPPFLAGS += $(GTK_CFLAGS) -DUSE_SYSTEM_GTK
else
  CPPFLAGS += -I$(PLATFORM_SRC)/native/common/deps/gtk2
endif

ifeq ($(MILESTONE), internal)
  CPPFLAGS += -DINTERNAL_BUILD
endif

