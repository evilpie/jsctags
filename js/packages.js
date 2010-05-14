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

// This script exports the CommonJS packages in the lib/ directory to Tiki so
// that they can be loaded in the browser.

tiki.register('::narcissus', {
    name:           'narcissus',
    //version:        "0.0.0",
    /* 'tiki:scripts': {
        'narcissus':            "../lib/narcissus/index.js",
        'narcissus/jsdefs':     "../lib/narcissus/jsdefs.js",
        'narcissus/jslex':      "../lib/narcissus/jslex.js",
        'narcissus/jsparse':    "../lib/narcissus/jsparse.js"
    } */
    'tiki:resources': [{
        url: "parser.html", //"lib/narcissus/index.js",
        type: 'script',
        id: 'narcissus',
        name: 'index.js'
    }]
});

tiki.register('::ctags', {
    name:           'ctags',
    //version:        "0.0.0",
    dependencies:   {
        narcissus:  "0.0.0"
    },
    'tiki:scripts': {
        'ctags':                "../lib/ctags/index.js",
        'ctags/reader':         "../lib/ctags/reader.js",
        'ctags/writer':         "../lib/ctags/writer.js"
    }
});

// Turn on autowrap so that the same .js files can be used both offline and in
// Tiki.
var browser = tiki.require.loader.sources[0];
browser.xhr = true;
browser.autowrap = true;

