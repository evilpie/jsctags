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

// Abstract interpreter, based on Narcissus.

var jsdefs = require('narcissus/jsdefs');
var tokens = jsdefs.tokens;
var Trait = require('traits').Trait;

var puts = require('sys').puts;

exports.Interpreter = Trait({
    _addDefs: function(defs, baseTag) {
        for (var name in defs) {
            var def = defs[name];
            if (def.hidden) {
                continue;
            }

            var tag = {};
            for (var tagfield in baseTag) {
                tag[tagfield] = baseTag[tagfield];
            }

            tag.name = name;

            var node = def.node;
            tag.tagfile = node.filename;
            tag.addr = node.lineno; // TODO: regex instead

            this.tags.push(tag);
        }
    },

    _exec: function(node, ctx) {
        switch (node.type) {
        case tokens.SCRIPT:
            var scopeObject = ctx.scope.object;
            node.funDecls.forEach(function(decl) {
                scopeObject[decl.name] = { node: decl, value: decl };
            });
            node.varDecls.forEach(function(decl) {
                scopeObject[decl.name] = { node: decl, value: decl };
            });

            // FALL THROUGH
        case tokens.BLOCK:
            node.forEach(function(node) { this._exec(ctx, node); }, this);
            break;

        case tokens.SEMICOLON:
            if (node.expression !== null && node.expression !== undefined) {
                this._exec(ctx, node.expression);
            }
            break;
        }
    },

    /** Takes a Narcissus AST and discovers the tags in it. */
    interpret: function(ast, module, opts) {
        var exportsDefs, windowDefs = {};

        var scope = {
            parent: null,
            object: { window: { hidden: true, value: windowDefs } }
        }

        if (opts.commonJS) {
            exportsDefs = {};
            scope.object.exports = { hidden: true, value: exportsDefs };
        }

        var ctx = { scope: scope };
        this._exec(ast, ctx, opts);

        this._addDefs(windowDefs, {});

        if (!opts.commonJS) {
            this._addDefs(scope.object, {});
        } else {
            this._addDefs(exportsDefs, { module: module });
        }
    }
});

