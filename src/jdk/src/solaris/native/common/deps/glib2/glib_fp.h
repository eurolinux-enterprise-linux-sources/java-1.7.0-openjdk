/*
 * Copyright (c) 2004, 2010, Oracle and/or its affiliates. All rights reserved.
 * Copyright (c) 2012 Red Hat Inc.
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

#ifndef __GLIB_FP_H__
#define __GLIB_FP_H__

#include <stdint.h>

#ifndef __G_TYPES_H__
typedef void* gpointer;
typedef int    gint;
typedef gint   gboolean;
typedef char   gchar;
#endif

#ifndef __G_LIBCONFIG_H__
#ifndef __GLIBCONFIG_H__
typedef uint32_t guint32;
#endif
#endif

#ifndef __G_QUARK_H__
typedef guint32 GQuark;
#endif

#ifndef __G_ERROR_H__
typedef struct {
  GQuark       domain;
  gint         code;
  gchar       *message;
} GError;
#endif

#ifndef USE_SYSTEM_GIO
#ifndef USE_SYSTEM_GCONF
#define g_type_init (*type_init)
#define g_free (*gfree)
#endif
#endif

typedef void (*type_init_func)(void);
typedef void (*free_func) (void* mem);

extern type_init_func type_init;
extern free_func gfree;

#endif /* __GLIB_FP_H__ */
