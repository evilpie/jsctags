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

var Trait = require('traits').Trait;

const ESCAPES = { "\\": "\\\\", "\n": "\\n", "\r": "\\r", "\t": "\\t" };

const METATAGS = [
    { name: '!_TAG_FILE_FORMAT', file: 2, addr: "/extended format/" },
    {
        name: '!_TAG_FILE_SORTED',
        file: 1,
        addr: "/0=unsorted, 1=sorted, 2=foldcase/"
    },
    {
        name: '!_TAG_PROGRAM_AUTHOR',
        file: "Patrick Walton",
        addr: "/pwalton@mozilla.com/"
    },
    { name: '!_TAG_PROGRAM_NAME', file: "jsctags" },
    {
        name: '!_TAG_PROGRAM_URL',
        file: "http://github.com/pcwalton/jsctags",
        addr: "/GitHub repository/"
    },
    { name: '!_TAG_PROGRAM_VERSION', file: "0.1" }
];

exports.TagWriter = Trait({
    tags: Trait.required,

    init: function() {
        this.tags = this.tags.concat(METATAGS);
    },

    write: function(stream) {
        var tags = this.tags;
        tags.sort(function(a, b) { return a.name.localeCompare(b.name); });

        tags.forEach(function(tag) {
            stream.write(tag.name);
            stream.write("\t");
            stream.write(tag.file);
            stream.write("\t");

            var addr = tag.addr;
            stream.write(addr !== undefined ? addr : "//");

            var tagfields = [];
            for (var key in tag) {
                if (key !== 'addr' && key !== 'file' && key !== 'kind') {
                    tagfields.push(key);
                }
            }
            tagfields.sort();

            var kind = tag.kind;
            if (kind === undefined && tagfields.length === 0) {
                stream.write("\n");
                return;
            }

            stream.write(";\"");

            if (kind !== undefined) {
                stream.write(kind);
            }

            tagfields.forEach(function(tagfield) {
                stream.write("\t");
                stream.write(tagfield);
                stream.write(":");

                var escape = function(str) { return ESCAPES[str]; };
                stream.write(tag[tagfield].replace("[\\\n\r\t]", escape));
            });

            stream.write("\n");
        });
    }
});

