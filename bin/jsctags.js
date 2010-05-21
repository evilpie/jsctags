#!/usr/bin/env node
/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an 'AS IS' basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is Bespin.
 *
 * The Initial Developer of the Original Code is
 * Mozilla.
 * Portions created by the Initial Developer are Copyright (C) 2009
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Bespin Team (bespin@mozilla.com)
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */

var argv = process.argv;
var path = require('path');
require.paths.unshift(path.join(path.dirname(argv[1]), '..', 'src', 'lib'));

var fs = require('fs');
var sys = require('sys');
var ctags = require('ctags');
var getopt = require('getopt').getopt;
var Tags = ctags.Tags;

function usage() {
    sys.puts("usage: jsctags [options] path0 [.. pathN]");
    sys.puts("options:");
    sys.puts("    -h, --help            display this usage info");
    sys.puts("    -L, --libroot dir     add a CommonJS module root (like " +
        "require.paths)")
    process.exit(1);
}

var opts;
try {
    opts = getopt("help|h", "libroot|L=s@");
} catch (e) {
    sys.puts(e);
    usage();
}

var pathCount = argv.length - 2;
if (opts.help || pathCount === 0) {
    usage();
}

var librootIds = {};
if ('libroot' in opts) {
    opts.libroot.forEach(function(libroot) {
        var st = fs.statSync(libroot);
        var id = st.dev + "," + st.ino;
        librootIds[id] = true;
    });
}

var tags = new Tags();

var idsSeen = {};
function processPath(cur, library, moduleId, packageId) {
    var st = fs.statSync(cur);
    var id = st.dev + "," + st.ino;
    if (id in idsSeen) {
        return; // avoid loops
    }
    idsSeen[id] = true;

    var ext = path.extname(cur);

    if (st.isDirectory()) {
        var basename = path.basename(cur);
        var submoduleId;
        try {
            var packageMetadataPath = path.join(cur, "package.json");
            var packageMetadata = fs.readFileSync(packageMetadataPath);
            var subpackageId = JSON.parse(packageMetadata).name;
            if (typeof(subpackageId) !== 'string') {
                // Fall back to the directory name in case we're in a package
                // that doesn't conform to the CommonJS spec, such as a Bespin
                // plugin.
                subpackageId = basename;
            }

            var libDir = path.join(cur, "lib");
            try {
                var libst = fs.statSync(libDir);
                if (!libst.isDirectory()) {
                    throw 'nondirectory';
                }

                processPath(libDir, true, "", subpackageId);
            } catch (e) {
                //
                // We're in a nonconformant (Bespin-style) package lacking a
                // "lib" directory. Assume that the module files are rooted
                // alongside the package.json file.
                //
                // FIXME: Check the exception. Make sure it's an ENOENT or
                // 'nondirectory'.
                //
                packageId = subpackageId;
            }

            submoduleId = "";
        } catch (e) {
            //
            // Not a CommonJS package.
            //
            // FIXME: Check the exception. Make sure it's an ENOENT.
            //
            if (library) {
                var submodulePrefix = (moduleId === "") ? "" : moduleId + "/";
                submoduleId = submodulePrefix + basename;
            } else {
                if (id in librootIds) {
                    library = true;
                    packageId = "";
                }

                submoduleId = "";
            }
        }

        fs.readdirSync(cur).forEach(function(filename) {
            var subpath = path.join(cur, filename);
            processPath(subpath, library, submoduleId, packageId);
        });
    } else if (ext === ".js") {
        var packagePrefix = (packageId === "") ? "" : packageId + ":";
        var basenameNoExt = path.basename(cur, ext);
        var thisModuleId;
        if (basenameNoExt === "index") {
            thisModuleId = packagePrefix + moduleId;
        } else {
            var modulePrefix = (moduleId === "") ? "" : moduleId + "/";
            thisModuleId = packagePrefix + modulePrefix + basenameNoExt;
        }
        var data = fs.readFileSync(cur);

        try {
            tags.add(data, cur, { commonJS: library, module: thisModuleId });
        } catch (e) {
            if ('lineNumber' in e) {
                sys.puts("at line " + e.lineNumber + ":");
            }
            throw e;
        }
    }
}

for (var i = 0; i < pathCount; i++) {
    processPath(argv[i + 2], false, "", "");
}

var out = fs.createWriteStream("tags");
tags.write(out);
out.end();

