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
var jsparse = require('narcissus/jsparse');
var tokenIds = jsdefs.tokenIds, tokens = jsdefs.tokens;
var Trait = require('traits').Trait;

var sys = require('sys');
var puts = sys.puts, inspect = sys.inspect;

const INDEXED_TYPES  = { 'function': true, object: true };  
const LOADABLE_TYPES = { activation: true, 'function': true, object: true };
const STORABLE_TYPES = { activation: true, 'function': true, object: true };

const REGEX_ESCAPES = { "\t": "\\t" };

function note(node, str) {
    puts(node.lineno + ":note: " + str);
}

function warn(node, str) {
    puts(node.lineno + ":warn: " + str);
}

function FunctionObject(interp, node, scope) {
    this.interp = interp;
    this.node = node;
    this.scope = scope;
    this.data = {};
    this.proto = { type: 'object', data: {} };
};

FunctionObject.prototype = {
    call: function(thisObject, args) {
        var activation = { type: 'activation', data: {} };
        var params = this.node.params;
        for (var i = 0; i < args.data.length; i++) {
            activation.data[this.node.params[i]] = args.data[i];
        }
        activation.data.arguments = activation;

        var ctx = { scope: { object: activation, parent: this.scope } };

        try {
            this.interp._exec(this.node.body, ctx);
        } catch (e) {
            if (e === 'return') {
                return ctx.result;
            }

            throw e;
        }

        return { type: 'scalar', data: undefined };
    },

    props: {
        prototype: {
            get: function() { return this.proto; },
            set: function(newValue) { this.proto = newValue; }
        }
    },

    type: 'function'
};

exports.Interpreter = function(ast, file, lines, opts) {
    this.ast = ast;
    this.file = file;
    this.lines = lines;
    this.opts = opts;
    this.tags = [];
};

exports.Interpreter.prototype = {
    _addSubtag: function(parentTag, name, value, stack, prototypeMember) {
        if (stack.indexOf(value) !== -1) {
            return;     // avoid cyclic structures
        }

        var tag = {};
        tag.name = name;
        if ('name' in parentTag) {  // Do we have a parent?
            if ('class' in parentTag) {
                // If one or more of our parents is getting assigned to a
                // prototype, then we're part of a class.
                tag['class'] = parentTag['class'] + "." + parentTag.name;
            } else {
                var path =  ('namespace' in parentTag)
                            ? parentTag.namespace + "." + parentTag.name
                            : parentTag.name;

                if (prototypeMember) {
                    tag['class'] = path;
                } else {
                    tag.namespace = path;
                }
            }
        }

        this._addValue(value, tag, stack.concat(value));
    },

    _addValue: function(value, baseTag, stack) {
        if (stack == null) {
            stack = [ value ];
        }

        // Create the tag.
        var tag = {};
        for (var tagfield in baseTag) {
            tag[tagfield] = baseTag[tagfield];
        }
        tag.type = value.type;
        tag.kind = this._getTagKind(tag);

        var node = value.node;
        if (node != null) {
            tag.tagfile = node.filename;
            tag.addr = this._regexify(this.lines[node.lineno - 1]);

            if (!value.hidden && /^\S/.test(tag.name)) {
                this.tags.push(tag);
            }
        }

        // Stop here if there are no members of this value to consider.
        if (!(value.type in INDEXED_TYPES)) {
            return;
        }

        // Recurse through members.
        var data = value.data;
        for (var name in data) {
            this._addSubtag(tag, name, data[name], stack, false);
        }

        // Stop here if there's no sane prototype.
        if (value.type !== 'function' ||
                !(value.proto.type in INDEXED_TYPES)) {
            return;
        }

        // Recurse through the prototype chain.
        var proto = value.proto;
        for (var name in proto.data) {
            this._addSubtag(tag, name, proto.data[name], stack, true);
        }
    },

    _deref: function(value) {
        if (value.type === 'ref') {
            var name = value.name, container = value.container;
            if (!(container.type in LOADABLE_TYPES) ||
                    !(name in container.data)) {
                return this._getNullValue();
            }

            if ('props' in container && name in container.props) {
                var prop = container.props[name];
                if ('get' in prop) {
                    return prop.get.call(container);
                }

                // true behavior: exception
                warn(container.node, "returning null for get() because " +
                    "no getter is defined for property \"" + name + "\"");
                return this._getNullValue();
            }

            return container.data[name];
        }
        return value;
    },

    _dumpScope: function(scope, i) {
        if (i == null) {
            i = 0;
        }

        puts("scope " + i + ":");
        for (var key in scope.object.data) {
            puts("var " + key + ";");
        }

        if (scope.parent != null) {
            this._dumpScope(scope.parent, i + 1);
        }
    },

    _exec: function(node, ctx) {
        var self = this;

        function deref(val) { return self._deref(val); }
        function exec(node) { return self._exec(node, ctx); }

        switch (node.type) {
        case tokenIds.FUNCTION:
            if (node.functionForm === jsparse.DECLARED_FORM) {
                return;
            }

            var isStatement = node.functionForm === jsparse.STATEMENT_FORM;
            if (node.name != null && !isStatement) {
                // Introduce a new scope.
                var scopeObj = { type: 'object', data: {} };
                ctx.scope = { object: scopeObj, parent: ctx.scope };
            }

            var fn = new FunctionObject(this, node, ctx.scope);

            if (isStatement) {
                ctx.scope.object.data[node.name] = fn;
            }

            return fn;

        case tokenIds.SCRIPT:
            node.funDecls.forEach(function(decl) {
                var fn = new FunctionObject(this, decl, ctx.scope);
                ctx.scope.object.data[decl.name] = fn;
            }, this);
            node.varDecls.forEach(function(decl) {
                ctx.scope.object.data[decl.name] = {
                    node:   decl,
                    type:   'undefined',
                    data:   null
                };
            });

            // FALL THROUGH
        case tokenIds.BLOCK:
            node.forEach(exec);
            break;

        case tokenIds.VAR:  // TODO: const too
            node.forEach(function(decl) {
                var init = decl.initializer;
                if (init == null) {
                    return;
                }

                var name = decl.name;
                var scope = ctx.scope;
                while (scope != null) {
                    if (Object.hasOwnProperty.call(scope.object.data, name)) {
                        break;
                    }
                    scope = scope.parent;
                }

                var value = deref(exec(init));
                scope.object.data[name] = value;
            }, this);
            break;

        case tokenIds.SEMICOLON:
            if (node.expression != null) {
                exec(node.expression);
            }
            break;

        case tokenIds.ASSIGN:
            // TODO: +=, -=, &c.
            var lhs = exec(node[0]);
            var rhs = deref(exec(node[1]));
            this._store(lhs, rhs, ctx);
            return rhs;

        case tokenIds.DOT:
            var lhs = exec(node[0]);
            var container = deref(lhs);
            if (!(container.type in LOADABLE_TYPES)) {
                warn(node, "container type " + container.type + " not loadable");
                return this._getNullValue();    // TODO: primitives
            }

            return {
                type: 'ref',
                container: container,
                name: node[1].value,
                node: node
            };

        case tokenIds.LIST:
            var args = { type: 'list', node: node };
            args.data = node.map(exec).map(deref);
            args.data.length = node.length;
            return args;

        case tokenIds.CALL:
            var lhs = exec(node[0]);
            var rhs = exec(node[1]);
            var fn = deref(lhs);
            if (fn.type !== 'function') {
                note(node, "not a function");
                return this._getNullValue();
            }

            var thisObject = (lhs.type === 'ref' ? lhs.container : null);
            if (thisObject != null && thisObject.type === 'activation') {
                thisObject = null;
            }

            return fn.call(thisObject, rhs);

        case tokenIds.OBJECT_INIT:
            var data = {};
            node.forEach(function(init) {
                switch (init.type) {
                case tokenIds.PROPERTY_INIT:
                    data[init[0].value] = deref(exec(init[1]));
                    break;

                default:
                    warn(node, "unsupported initializer: " + tokens[init.type]);
                }
            });
            return { type: 'object', data: data, node: node };

        case tokenIds.IDENTIFIER:
            var scope = ctx.scope;
            while (scope != null) {
                if (node.value in scope.object.data) {
                    break;
                }
                scope = scope.parent;
            }

            var container = (scope === null)
                ? this._getNullValue()
                : scope.object;

            var rv = {
                type:       'ref',
                container:  container,
                name:       node.value,
                node:       node
            };
            return rv;

        case tokenIds.NUMBER:
            return { type: 'number', data: node.value, node: node };

        case tokenIds.STRING:
            return { type: 'string', data: node.value, node: node };

        case tokenIds.REGEXP:
            return { type: 'regexp', data: node.value, node: node };

        case tokenIds.GROUP:
            return exec(node[0]);

        default:
            warn(node, "unknown token \"" + tokens[node.type] + "\"");
            return this._getNullValue();
        }
    },

    // Determines the kind of a tag from the tag data.
    _getTagKind: function(tag) {
        if (tag.type === 'function') {
            return 'f';
        }
        if ('class' in tag || 'namespace' in tag) {
            return 'm';
        }
        return 'v';
    },

    _getNullValue: function() {
        return { type: 'null', data: null };
    },

    _regexify: function(str) {
        function subst(ch) {
            return (ch in REGEX_ESCAPES) ? REGEX_ESCAPES[ch] : "\\" + ch;
        }
        return "/" + str.replace(/[\t*^$.~\\\/]/g, subst) + "/";
    },

    _store: function(dest, src, ctx) {
        if (dest.type !== 'ref') {
            return;     // true behavior: ReferenceError
        }

        var container = dest.container != null ? dest.container : ctx.global;
        var name = dest.name;
        if (container.type in STORABLE_TYPES) {
            if ('props' in container && name in container.props) {
                var prop = container.props[name];
                if ('set' in prop) {
                    prop.set.call(container, src);
                } else {
                    // true behavior: exception
                    warn(dest.node, "not storing because no setter is " +
                        "defined for property \"" + name + "\"");
                }
            } else {
                container.data[name] = src;
            }
        } else {
            warn(dest.node, "not storing because type = " + container.type);
        }
    },

    /** Discovers the tags in the Narcissus-produced AST. */
    interpret: function() {
        var wnd = { hidden: true, type: 'object', data: {} };
        wnd.data.window = wnd;

        var ctx = { global: wnd, scope: { parent: null, object: wnd } };

        var opts = this.opts;
        var exports;
        if (opts.commonJS) {
            exports = { hidden: true, type: 'object', data: {} };
            wnd.data.exports = exports;
        }

        this._exec(this.ast, ctx);

        if (!opts.commonJS) {
            var scope = ctx.scope;
            while (scope !== null) {
                this._addValue(scope.object, {});
                scope = scope.parent;
            }
        } else {
            this._addValue(wnd, {});
            this._addValue(exports, { module: this.module });
        }
    }
};

