/*
 * Copyright (c) 2005, 2011, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
#ifndef __GTK_FP_CHECK_H__
#define __GTK_FP_CHECK_H__

#include <gtk/gtk.h>
#include "jvm_md.h"

#define GTK2_LIB_VERSIONED VERSIONED_JNI_LIB_NAME("gtk-x11-2.0", "0")
#define GTK2_LIB JNI_LIB_NAME("gtk-x11-2.0")

gboolean gtk2_check_dlversion();

/************************
 * Gtk function pointers
 ************************/
/**
 * Returns :
 * NULL if the GTK+ library is compatible with the given version, or a string
 * describing the version mismatch.
 */
gchar* (*fp_gtk_check_version)(guint required_major, guint required_minor,
				      guint required_micro);

#endif
