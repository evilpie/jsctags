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
require.paths.unshift(path.join(path.dirname(argv[1]), "..", "lib",
    "jsctags"));

var _ = require('underscore')._;
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

function idFor(st) {
    return st.dev + "," + st.ino;
}

var librootIds = {};
if ('libroot' in opts) {
    opts.libroot.forEach(function(libroot) {
        var st = fs.statSync(libroot);
        librootIds[idFor(st)] = true;
    });
}

var tags = new Tags();

// Ascend the directory hierarchy to find the CommonJS package this module is
// in, if any.
function getModuleInfo(fullPath) {
    function commonJS(modulePath, packageId) {
        var ext = path.extname(modulePath), len = modulePath.length;
        var modulePart = modulePath.substring(0, len - ext.length);
        var moduleId = (packageId != null)
                       ? packageId + ":" + modulePart
                       : modulePart;
        return { commonJS: true, module: moduleId };
    }

    var dir = path.dirname(fullPath);
    var i = 0, lastPath = null, libPath = null;
    while (true) {
        var p, st;
        try {
            p = dir;
            _(i).times(function() { p = path.dirname(p); });
            st = fs.statSync(p);
        } catch (e) {
            break;
        }

        if (p === lastPath) {
            break;
        }
        lastPath = p;

        var metadataPath = path.join(p, "package.json");
        try {
            var metadata = fs.readFileSync(metadataPath);
            var packageId = JSON.parse(metadata).name;
            if (typeof(packageId) !== 'string') {
                // Fall back to the directory name in case we're in a package
                // that doesn't conform to the CommonJS spec, such as a Bespin
                // plugin.
                packageId = path.basename(p);
            }

            if (libPath == null) {
                // We're in a nonconformant (Bespin-style) package lacking a
                // "lib" directory. Assume that the module files are rooted
                // alongside the package.json file.
                libPath = p;
            }

            return commonJS(fullPath.substring(libPath.length + 1), packageId);
        } catch (e) {}

        if (path.basename(p) === "lib") {
            libPath = p;
        }

        if (librootIds.hasOwnProperty(idFor(st))) {
            return commonJS(fullPath.substring(p.length + 1));
        }

        i++;
    }

    return { commonJS: false };
}

var idsSeen = {};
function processPath(p) {
    var st = fs.statSync(p);
    var id = idFor(st);
    if (id in idsSeen) {
        return; // avoid loops
    }
    idsSeen[id] = true;

    if (st.isDirectory()) {
        fs.readdirSync(p).forEach(function(filename) {
            processPath(path.join(p, filename));
        });
    } else if (path.extname(p).toLowerCase() === ".js") {
        try {
            var data = fs.readFileSync(p);
            tags.add(data, p, getModuleInfo(p));
        } catch (e) {
            if ('lineNumber' in e) {
                sys.puts("error:" + p + ":" + e.lineNumber + ": " + e);
            } else {
                throw e;
            }
        }
    }
}

for (var i = 0; i < pathCount; i++) {
    processPath(argv[i + 2], false, "", "");
}

var out = fs.createWriteStream("tags");
tags.write(out);
out.end();

