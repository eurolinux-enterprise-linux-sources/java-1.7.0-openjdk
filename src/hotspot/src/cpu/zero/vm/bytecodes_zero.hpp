/*
 * Copyright (c) 1997, 2010, Oracle and/or its affiliates. All rights reserved.
 * Copyright 2009 Red Hat, Inc.
 * Copyright 2009 Edward Nevill
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
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
 *
 */

#ifndef CPU_ZERO_VM_BYTECODES_ZERO_HPP
#define CPU_ZERO_VM_BYTECODES_ZERO_HPP

#ifdef HOTSPOT_ASM
#define _iaccess_0      ((Bytecodes::Code)0xdb)
#define _iaccess_1      ((Bytecodes::Code)0xdc)
#define _iaccess_2      ((Bytecodes::Code)0xdd)
#define _iaccess_3      ((Bytecodes::Code)0xde)

#define _invokeresolved         ((Bytecodes::Code)0xdf)
#define _invokespecialresolved  ((Bytecodes::Code)0xe0)
#define _invokestaticresolved   ((Bytecodes::Code)0xe1)

#define _iload_iload    ((Bytecodes::Code)0xe3)
#define _iload_iload_N  ((Bytecodes::Code)0xe4)

#define _dmac           ((Bytecodes::Code)0xe8)

      _iload_0_iconst_N   , // 233 0xe9
      _iload_1_iconst_N   , // 234 0xea
      _iload_2_iconst_N   , // 235 0xeb
      _iload_3_iconst_N   , // 236 0xec
      _iload_iconst_N     , // 237 0xed
      _iadd_istore_N      , // 238 0xee
      _isub_istore_N      , // 239 0xef
      _iand_istore_N      , // 240 0xf0
      _ior_istore_N       , // 241 0xf1
      _ixor_istore_N      , // 242 0xf2
      _iadd_u4store       , // 243 0xf3
      _isub_u4store       , // 244 0xf4
      _iand_u4store       , // 245 0xf5
      _ior_u4store        , // 246 0xf6
      _ixor_u4store       , // 247 0xf7
      _iload_0_iload      , // 248 0xf8
      _iload_1_iload      , // 249 0xf9
      _iload_2_iload      , // 250 0xfa
      _iload_3_iload      , // 251 0xfb
      _iload_0_iload_N    , // 252 0xfc
      _iload_1_iload_N    , // 253 0xfd
      _iload_2_iload_N    , // 254 0xfe
      _iload_3_iload_N    , // 255 0xff
#endif // HOTSPOT_ASM

#endif // CPU_ZERO_VM_BYTECODES_ZERO_HPP
