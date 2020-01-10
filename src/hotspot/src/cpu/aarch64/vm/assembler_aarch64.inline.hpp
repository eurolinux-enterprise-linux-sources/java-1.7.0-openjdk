/*
 * Copyright (c) 2013, Red Hat Inc.
 * Copyright (c) 1997, 2010, Oracle and/or its affiliates.
 * All rights reserved.
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

#ifndef CPU_AARCH64_VM_ASSEMBLER_AARCH64_INLINE_HPP
#define CPU_AARCH64_VM_ASSEMBLER_AARCH64_INLINE_HPP

#include "asm/assembler.inline.hpp"
#include "asm/codeBuffer.hpp"
#include "code/codeCache.hpp"

inline void Assembler::emit_long64(jlong x) {
  *(jlong*) _code_pos = x;
  _code_pos += sizeof(jlong);
  code_section()->set_end(_code_pos);
}

#ifndef PRODUCT
inline void MacroAssembler::pd_print_patched_instruction(address branch) { Unimplemented(); }
#endif // ndef PRODUCT

#endif // CPU_AARCH64_VM_ASSEMBLER_AARCH64_INLINE_HPP
