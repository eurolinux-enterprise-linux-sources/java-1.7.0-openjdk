/*
 * Copyright (c) 2005, Oracle and/or its affiliates. All rights reserved.
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

package sun.security.smartcardio;

import java.io.File;
import java.io.IOException;

import java.security.AccessController;
import java.security.PrivilegedAction;

import sun.security.util.Debug;

/**
 * Platform specific code and functions for Unix / MUSCLE based PC/SC
 * implementations.
 *
 * @since   1.6
 * @author  Andreas Sterbenz
 */
class PlatformPCSC {

    static final Debug debug = Debug.getInstance("pcsc");

    static final Throwable initException;

    private final static String PROP_NAME = "sun.security.smartcardio.library";

    private final static String LIB1 = "/usr/$LIBISA/libpcsclite.so.1";
    private final static String LIB2 = "/usr/local/$LIBISA/libpcsclite.so.1";
    private final static String LIB3 = "/usr/lib/$ARCH-linux-gnu/libpcsclite.so.1";
    private final static String LIB4 = "/usr/lib/arm-linux-gnueabi/libpcsclite.so.1";
    private final static String LIB5 = "/usr/lib/arm-linux-gnueabihf/libpcsclite.so.1";
    private final static String LIB6 = "/usr/lib/$ARCH-kfreebsd-gnu/libpcsclite.so.1";
    private final static String PCSC_FRAMEWORK = "/System/Library/Frameworks/PCSC.framework/Versions/Current/PCSC";

    PlatformPCSC() {
        // empty
    }

    static {
        initException = AccessController.doPrivileged(new PrivilegedAction<Throwable>() {
            public Throwable run() {
                try {
                    System.loadLibrary("j2pcsc");
                    String library = getLibraryName();
                    if (debug != null) {
                        debug.println("Using PC/SC library: " + library);
                    }
                    initialize(library);
                    return null;
                } catch (Throwable e) {
                    return e;
                }
            }
        });
    }

    // expand $LIBISA to the system specific directory name for libraries
    private static String expand(String lib) {
        String s1, s2;
        int k = lib.indexOf("$LIBISA");
        if (k != -1) {
            String libDir;
            if ("64".equals(System.getProperty("sun.arch.data.model"))) {
                if ("SunOS".equals(System.getProperty("os.name"))) {
                    libDir = "lib/64";
                } else {
                    // assume Linux convention
                    libDir = "lib64";
                }
            } else {
                // must be 32-bit
                libDir = "lib";
            }
            lib = replace(k, lib, "$LIBISA", libDir);
        }

        k = lib.indexOf("$ARCH");
        if (k != -1) {
            String arch = System.getProperty("os.arch");
            switch (arch) {
            case "amd64":
                arch = "x86_64";
                break;
            case "ppc":
                arch = "powerpc";
                break;
            case "ppc64":
                arch = "powerpc64";
                break;
            case "ppc64le":
                arch = "powerpc64le";
                break;
            }
            lib = replace(k, lib, "$ARCH", arch);
        }

        return lib;
    }

    private static String replace(int k, String text,
                                  String template, String replacement) {
        String s1, s2;

        s1 = text.substring(0, k);
        s2 = text.substring(k + template.length());

        return s1 + replacement + s2;
    }

    private static String getLibraryName() throws IOException {
        // if system property is set, use that library
        String lib = expand(System.getProperty(PROP_NAME, "").trim());
        if (lib.length() != 0) {
            return lib;
        }
        lib = expand(LIB1);
        if (new File(lib).isFile()) {
            // if LIB1 exists, use that
            return lib;
        }
        lib = expand(LIB2);
        if (new File(lib).isFile()) {
            // if LIB2 exists, use that
            return lib;
        }
        lib = expand(LIB3);
        if (new File(lib).isFile()) {
            // if LIB3 exists, use that
            return lib;
        }
        lib = LIB4; // Debian armel special case
        if (new File(lib).isFile()) {
            // if LIB4 exists, use that
            return lib;
        }
        lib = LIB5; // Debian armhf special case
        if (new File(lib).isFile()) {
            // if LIB5 exists, use that
            return lib;
        }
        lib = expand(LIB6);
        if (new File(lib).isFile()) {
            // if LIB6 exists, use that
            return lib;
        }
        lib = PCSC_FRAMEWORK;
        if (new File(lib).isFile()) {
            // if PCSC.framework exists, use that
            return lib;
        }
        throw new IOException("No PC/SC library found on this system");
    }

    private static native void initialize(String libraryName);

    // PCSC constants defined differently under Windows and MUSCLE
    // MUSCLE version
    final static int SCARD_PROTOCOL_T0     =  0x0001;
    final static int SCARD_PROTOCOL_T1     =  0x0002;
    final static int SCARD_PROTOCOL_RAW    =  0x0004;

    final static int SCARD_UNKNOWN         =  0x0001;
    final static int SCARD_ABSENT          =  0x0002;
    final static int SCARD_PRESENT         =  0x0004;
    final static int SCARD_SWALLOWED       =  0x0008;
    final static int SCARD_POWERED         =  0x0010;
    final static int SCARD_NEGOTIABLE      =  0x0020;
    final static int SCARD_SPECIFIC        =  0x0040;

}
