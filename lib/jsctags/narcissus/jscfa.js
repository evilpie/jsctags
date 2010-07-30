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
 * Dimitris Vardoulakis <dvardoulakis@mozilla.com>
 * Portions created by the Initial Developer are Copyright (C) 2010
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
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

/*
 * Narcissus - JS implemented in JS.
 *
 * Control-flow analysis to infer types. The output is in ctags format.
 */


/* FIXMEs:
 *
 * - Take care of cycles in the proto chain of abstract objects
 *
 * - Regarding frames. All states in the same fun share a frame. It's an obj, 
 *   not a list so I can't shadow bindings. The only case where shadowing is 
 *   needed in one scope is for vars w/ the same name in catch blocks.
 *   Maybe later for LETs too. Solve that by alphatisation or de Bruijn, don't 
 *   use lists for frames, slow.
 *
 * - fixStm turns (WHILE exp stm) to (FOR (; exp; ) STM) to reduce the AST more?
 *   There's a more drastic change I can do if speed needed. Since I ignore the 
 *   control flow from bool exps, IF, SWITCH, FOR, WHILE can all be turned to a
 *   series of semis and blocks, they have no other meaning.
 *   This decreases the dispatch on the stm AST dramatically.
 */

/* (Possible) TODOs:
 * - now all objs are in heap. If it's too imprecise, treat them as heap vars.
 *   Create on stack & heap, and if heap changes when u need the obj then join.
 * - representation of Aobj: in the common case, an abstract obj has one proto 
 *   and one constructor. Specialize for this case.
 */

/*
 * Semantics of: function foo (args) body:
 * It's not the same as: var foo = function foo (args) body
 * If it appears in a script then it's hoisted at the top, so it's in funDecls
 * If it appears in a block then it's visible after it's appearance, in the
 * whole rest of the script!!
 * {foo(); {function foo() {print("foo");}}; foo();}
 * The 1st call to foo throws, but if you remove it the 2nd call succeeds.
 */

/* (POSSIBLY) UNSOUND ASSUMPTIONS:
 * - Won't iterate loops to fixpt.
 * - Return undefined not tracked, eg (if sth return 12;) always returns number.
 * - If the prototype property of a function object foo is accessed in a weird
 *   way, eg foo["proto" + "type"] the analysis won't figure it out.
 * - When accessing properties w/ obj[exp], we act differently when exp is a
 *   constant & when it's a general exp. We may miss flows between them (test19)
 * - when popping from an array, I do nothing. This is hard to make sound.
 */

////////////////////////////////////////////////////////////////////////////////
/////////////////////////////   UTILITIES  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

if (!Array.prototype.forEach) 
  Array.prototype.forEach = function(fun) {
    for (var i = 0, len = this.length; i < len; i++) 
      /* if (i in this) */ fun(this[i], i, this);
  };

// search for an elm in the array that satisfies pred
Array.prototype.member = function(pred) {
  for (var i = 0, len = this.length; i < len; i++)
    /* if (i in this) */ if (pred(this[i])) return true;
  return false;
};

// starting at index, remove all instances of elm in linear time.
// pred determines the equality of elms
Array.prototype.rmElmAfterIndex = function(pred, elm, index) {
  if (index >= this.length) return;
  for (var i = index, j = index, len = this.length; i < len; i++)
    if (!pred(elm, this[i])) this[j++] = this[i];
  this.length = j;
};

// remove all duplicates from array (keep first occurence of each elm)
// pred determines the equality of elms
Array.prototype.rmDups = function(pred) {
  var i = 0;
  while (i < (this.length - 1)) {
    this.rmElmAfterIndex(pred, this[i], i+1);
    i++;
  }
};

// compare two arrays for structural equality
function arrayeq(eq, a1, a2) {
  var len = a1.length, i;
  if (len !== a2.length) return false;
  for (i=0; i<len; i++) if (!eq(a1[i], a2[i])) return false;
  return true;
}

function buildArray(size, elm) {
  var a = new Array(size);
  for (var i=0; i<size; i++) a[i] = elm;
  return a;
}

// merge two sorted arrays of numbers into a sorted new array
function arraymerge(a1, a2) {
  var i=0, j=0, len1 = a1.length, len2 = a2.length, a = new Array();
  while (true) {
    if (i === len1) {
      for (; j < len2; j++) a.push(a2[j]);
      return a;
    }
    if (j === len2) {
      for (; i<len1; i++) a.push(a1[i]);
      return a;
    }
    if (a1[i] <= a2[j]) a.push(a1[i++]); else a.push(a2[j++]);
  }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////    PREPARE AST FOR FLOW ANALYSIS    ///////////////////////
////////////////////////////////////////////////////////////////////////////////

var m_jsdefs = require('./jsdefs');
var jsparse = require('./jsparse');
var Node = jsparse.Node;
const DECLARED_FORM = jsparse.DECLARED_FORM;

eval(m_jsdefs.defineTokenConstants());

var print;
try {
  window;
  // it's defined, use firebug
  print = console.log;
 }
 catch (e) {
   // use node
   print = require('sys').puts;
 };

// count is used to generate a unique ID for each node in the AST.
var count;

// Instead of a flat long case dispatch, arities create a tree-like dispatch.
// Nodes are grouped in arities by how we recur down their structure.
var opArity = [];

const NULLARY = 0, UNARY = 1, BINARY = 2, TERNARY = 3, MULTI = 4, 
  MULTI_OI = 5, MULTI_CALL = 6, FUN = 7;

opArity[NULL] = opArity[THIS] = opArity[TRUE] = opArity[FALSE] = NULLARY;
opArity[IDENTIFIER] = opArity[NUMBER] = opArity[STRING] = NULLARY;
opArity[REGEXP] = NULLARY;

opArity[DELETE] = opArity[VOID] = opArity[TYPEOF] = opArity[NOT] = UNARY;
opArity[BITWISE_NOT] = opArity[UNARY_PLUS] = opArity[UNARY_MINUS] = UNARY;
opArity[NEW] = opArity[GROUP] = opArity[INCREMENT] = opArity[DECREMENT] = UNARY;

opArity[BITWISE_OR] = opArity[BITWISE_XOR] = opArity[BITWISE_AND] = BINARY;
opArity[EQ] = opArity[NE] = opArity[STRICT_EQ] = opArity[STRICT_NE] = BINARY;
opArity[LT] = opArity[LE] = opArity[GE] = opArity[GT] = BINARY;
opArity[INSTANCEOF] = opArity[LSH] = opArity[RSH] = opArity[URSH] = BINARY;
opArity[PLUS] = opArity[MINUS] = opArity[MUL] = opArity[DIV] = BINARY;
opArity[MOD] = opArity[DOT] = opArity[AND] = opArity[OR] = BINARY; 
opArity[ASSIGN] = opArity[INDEX] = opArity[IN] = opArity[DOT] = BINARY;

opArity[HOOK] = TERNARY;
opArity[COMMA] = opArity[ARRAY_INIT] = MULTI;
opArity[OBJECT_INIT] = MULTI_OI;
opArity[CALL] = opArity[NEW_WITH_ARGS] = MULTI_CALL;
opArity[FUNCTION] = FUN;

// el hacko grande: need new expression token but don't know the token id`s 
// (eval`d from jsdefs). No conflict w/ IF b/c it only appears as a stm.
const DOT_PROTO = IF;
opArity[DOT_PROTO] = UNARY;
const ARGUMENTS = FOR;
opArity[ARGUMENTS] = UNARY;
const PLUS_ASSIGN = WHILE;
opArity[PLUS_ASSIGN] = BINARY;

// expr node -> stm node
function semiNode(n) {
  var sn = new Node(n.tokenizer, SEMICOLON);
  sn.expression = n;
  return sn;
}

// tokenizer, string -> identifier node
function idNode(t, name) {
  var n = new Node(t, IDENTIFIER);
  n.name = n.value = name;
  return n;
}

// node -> node
// does some cleanup on the input expression node in-place.
function fixExp(n) {
  var nt = n.type;

  function fixe(n, i, parent) { parent[i] = fixExp(n); }

  switch (opArity[nt]) {
  case BINARY:
    if (nt === DOT) {
      if (n[1].value === "prototype") {
        n.type = DOT_PROTO;
        n.splice(1, 1);
      }
      else
        n[1].value += "-";
    }
    else if (nt === ASSIGN && n[0].assignOp === PLUS)
      n.type = PLUS_ASSIGN;
    //fall thru
  case TERNARY: case MULTI:
    n.forEach(fixe);
    return n;

  case MULTI_CALL:
    n[0] = fixExp(n[0]);
    n[1].forEach(fixe);
    return n;

  case NULLARY:
    if (nt === IDENTIFIER) n.name = n.value;
    return n;

  case UNARY:
    if (nt === GROUP) return fixExp(n[0]);
    if (nt === UNARY_MINUS && n[0].type === NUMBER) {
      n.type = NUMBER;
      n.value = -n[0].value;
      n.splice(0, 1);
      return n;
    }
    if (nt === NEW) { // unify NEW and NEW_WITH_ARGS
      n.type = NEW_WITH_ARGS;
      n[1] = [];
    }
    n[0] = fixExp(n[0]);
    return n;

  case FUN:
    fixFun(n);
    return n;

  case MULTI_OI:
    n.forEach(function(prop) {
        prop[0] = idNode(prop[0].tokenizer, prop[0].value + "-");
        prop[1] = fixExp(prop[1]);
      });
    return n;
  }
}

function fixFun(n) {
  var t = n.tokenizer;
  // replace name w/ a property fname which is an IDENTIFIER node.
  n.fname = idNode(t, n.name);
  delete n.name;
  // turn the formals to nodes, I'll want to attach stuff to them later.
  n.params.forEach(function(p, i, ps) { ps[i] = idNode(t, p); });
  // don't tag builtin funs, they never have RETURN when used as constructors.
  n.hasReturn = fixStm(n.body);
}

// node -> boolean
// returns true iff n contains RETURN directly (not RETURNs of inner functions).
function fixStm(n) {
  var i, j, n2, n3, ans1, ans2;

  // VAR or CONST node -> comma node
  // Convert to assignments, with readOnly field for constants.
  // The returned node may contain 0 subexpressions.
  function initsToAssigns(n) {
    var n2, vdecl, a, initv, i, len;

    n2 = new Node(n.tokenizer, COMMA);
    for (i=0, len=n.length; i < len; i++) {
      vdecl = n[i];
      initv = vdecl.initializer;
      if (initv) {
        initv = fixExp(initv);
        a = new Node(vdecl.tokenizer, ASSIGN);
        a.push(idNode(vdecl.tokenizer, vdecl.name));
        a.push(initv);
        a.readOnly = vdecl.readOnly;
        n2.push(a);
      }
    }
    return n2;
  }

  switch (n.type) {
  case SCRIPT:
  case BLOCK:
    var n2t, ans1 = false;
    i=0;
    while (i < n.length) {
      n2 = n[i];
      switch (n2.type) {
      case VAR:
      case CONST:
        n3 = initsToAssigns(n2);
        if (n3.length > 0) {
          var semin = semiNode(n3);
          n.splice(i++, 1, semin);
        }
        else n.splice(i, 1);
        break;

      case SWITCH:
        if (n2.cases.length === 0) {// switch w/out branches becomes semi node
          n2.discriminant = fixExp(n2.discriminant);
          n[i] = semiNode(n2.discriminant);
        }
        else
          ans1 = fixStm(n2) || ans1;
        i++;
        break;

      case BREAK:
      case CONTINUE: //rm break & continue nodes
        n.splice(i, 1);
        break;

      case FUNCTION: //rm functions from Script bodies, they're in funDecls
        fixFun(n2);
        if (n2.functionForm === DECLARED_FORM)
          n.splice(i, 1);
        else
          ++i;
        break;

      case LABEL: //replace LABEL nodes by their statement (forget labels)
        n[i] = n2.statement;
        break;
        
      case SEMICOLON: // remove empty SEMICOLON nodes
        if (n2.expression == null) {
          n.splice(i, 1);
          break;
        } // o/w fall thru to fix the node
        
      default:
        ans1 = fixStm(n2) || ans1;
        i++;
        break;
      }
    }
    return ans1;

  case BREAK: case CONTINUE:
    n.type = BLOCK;
    return false;

  case SEMICOLON:
    if (!n.expression)
      n.type = BLOCK;
    else
      n.expression = fixExp(n.expression); //n.expression can't be null
    return false;

  case IF:
    n.condition = fixExp(n.condition);
    ans1 = fixStm(n.thenPart);
    return (n.elsePart && fixStm(n.elsePart)) || ans1;

  case SWITCH:
    n.discriminant = fixExp(n.discriminant);
    ans1 = false;
    n.cases.forEach( function(branch) {
        branch.caseLabel && (branch.caseLabel = fixExp(branch.caseLabel));
        ans2 = fixStm(branch.statements);
        ans1 = ans1 || ans2;
      });
    return ans1;

  case FOR:
    n2 = n.setup;
    if (n2)
      if (n2.type === VAR || n2.type === CONST)
        n.setup = initsToAssigns(n2);
      else
        n.setup = fixExp(n2);
    n.condition && (n.condition = fixExp(n.condition));
    n.update && (n.update = fixExp(n.update));
    return fixStm(n.body);

  case FOR_IN:
    n.iterator = fixExp(n.iterator);
    n.object = fixExp(n.object);
    return fixStm(n.body);
    
  case WHILE:
  case DO:
    n.condition = fixExp(n.condition);
    return fixStm(n.body);

  case TRY: // turn the varName of each catch-clause to a node called exvar
    ans1 = fixStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) {
        clause.exvar = idNode(clause.tokenizer, clause.varName);
        clause.guard && (clause.guard = fixExp(clause.guard));
        ans2 = fixStm(clause.block);
        ans1 = ans1 || ans2;
      });
    return (n.finallyBlock && fixStm(n.finallyBlock)) || ans1;

  case THROW: 
    n.exception = fixExp(n.exception);
    return false;

  case RETURN:
    if (n.value === "return")
      n.value = idNode(n.tokenizer, "undefined");
    else
      n.value = fixExp(n.value);
    return true;
     
  case VAR: case CONST: // very rare to not appear in a block or script.
    n2 = initsToAssigns(n);
    n.type = SEMICOLON;
    n.expression = n2;
    n.length = 0;
    return false;
   
  case WITH:
    throw new Error("fixStm: WITH not implemented");

  default:
    throw new Error("fixStm unhandled case: " + n.type + ", line " + n.lineno);
  }
}

// Invariants of the AST after fixStm:
// - no GROUP nodes
// - no NEW nodes, they became NEW_WITH_ARGS
// - the formals of functions are nodes, not strings
// - functions have a property fname which is an IDENTIFIER node, name deleted
// - no VAR and CONST nodes, they've become semicolon comma nodes.
// - no BREAK and CONTINUE nodes.
//   Unfortunately, this isn't independent of exceptions.
//   If a finally-block breaks or continues, the exception isn't propagated.
//   I will falsely propagate it (still sound, just more approximate).
// - no LABEL nodes
// - function nodes only in blocks, not in scripts
// - no empty SEMICOLON nodes
// - no switches w/out branches
// - each catch clause has a property exvar which is an IDENTIFIER node
// - all returns have .value (the ones that didn't, got an undefined)
// - the lhs of a property initializer of an OBJECT_INIT is always an identifier
// - the property names in DOT and OBJECT_INIT end with a dash.
// - there is no DOT whose 2nd arg is "prototype", they've become NODE_PROTOs.
// - value of a NUMBER can be negative (UNARY_MINUS of constant became NUMBER).
// - the operator += has its own non-terminal, PLUS_ASSIGN.
// - each function node has a property hasReturn to show if it uses RETURN.

// FIXME: most of the addr`s will be redundant. Find the redundant ones and
// generate fewer addr`s here to compact the heap.

// node -> undefined
// adds an "addr" property to nodes which is a number unique for each node.
function labelExp(n) {
  n.addr = ++count;

  switch (opArity[n.type]) {
  case UNARY: case BINARY: case TERNARY: case MULTI:
    n.forEach(labelExp);
    return;

  case MULTI_CALL:
    labelExp(n[0]);
    n[1].forEach(labelExp);
    return;

  case NULLARY:
    return;

  case FUN:
    labelFun(n);
    return;

  case MULTI_OI:
    n.forEach(function(prop) { labelExp(prop[0]); labelExp(prop[1]); });
    return;
  }
}

function labelFun(n) {
  n.addr = ++count;
  n.defaultProtoAddr = ++count;
  n.fname.addr = ++count;
  n.params.forEach( function(p) { p.addr = ++count; });
  labelStm(n.body);
}

// node -> node
// adds an "addr" property to nodes, which is a number unique for each node.
function labelStm(n) {
  n.addr = ++count;

  switch (n.type) {
  case SCRIPT:
    n.varDecls.forEach(function(vd) {vd.addr = ++count;});
    n.funDecls.forEach(labelFun);
    // fall thru to fix the script body
  case BLOCK:
    n.forEach(labelStm);
    break;

  case FUNCTION:
    labelFun(n);
    break;

  case SEMICOLON:
    labelExp(n.expression); 
    break;

  case IF:
    labelExp(n.condition);
    labelStm(n.thenPart);
    n.elsePart && labelStm(n.elsePart);
    break;
        
  case SWITCH:
    labelExp(n.discriminant);
    n.cases.forEach(function(branch) {
        branch.caseLabel && labelExp(branch.caseLabel);
        labelStm(branch.statements);
      });
    break;

  case FOR: 
    n.setup && labelExp(n.setup);
    n.condition && labelExp(n.condition);
    n.update && labelExp(n.update);
    labelStm(n.body);
    break;

  case FOR_IN:
    labelExp(n.iterator);
    labelExp(n.object);
    labelStm(n.body);
    break;

  case WHILE: case DO:
    labelExp(n.condition);
    labelStm(n.body);
    break;

  case TRY:
    labelStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) {
        labelExp(clause.exvar);
        clause.guard && labelExp(clause.guard);
        labelStm(clause.block);
      });
    n.finallyBlock && labelStm(n.finallyBlock);
    break;

  case THROW: 
    labelExp(n.exception);
    break;

  case RETURN:
    labelExp(n.value);
    break;
        
  case WITH:
    throw new Error("labelStm: WITH not implemented");

  default:
    throw new Error("labelStm: unknown case");
  }
  return n;
}


// FIXME: if speed of frame lookups becomes an issue, revisit tagVarRefs and
// turn frame lookups to array accesses instead of property accesses.

const STACK = 0, HEAP = 1, GLOBAL = 2;

// node, array of id nodes, array of id nodes -> undefined
// classify variable references as either stack or heap variables.
// FIXME: add global variables to the global obj later.
function tagVarRefsExp(n, innerscope, otherscopes) {
  var nt = n.type;

  switch (opArity[nt]) {

  case BINARY:
    if (nt === DOT) {// don't classify property names
      var n0 = n[0];
      if (commonJSmode && n0.type === IDENTIFIER && n0.name === "exports")
        tagVarRefsExp(n0, innerscope, otherscopes, n[1]);
      else
        tagVarRefsExp(n0, innerscope, otherscopes);
      return;
    }
    else if (nt === INDEX) {
      var n0 = n[0], shadowed = false;
      // use new non-terminal only  if "arguments" refers to the arguments array
      if (n0.type === IDENTIFIER && n0.name === "arguments") {
        for (var i = innerscope.length - 1; i >= 0; i--) 
          if (innerscope[i].name === "arguments") {
            shadowed = true;
            break;
          }
        if (!shadowed) {
          n.type = ARGUMENTS;
          n.arguments = innerscope;//hack: innerscope is params (maybe extended)
          n[0] = n[1];
          n.splice(1, 1);
        }
      }
    }
    // fall thru
  case UNARY: case TERNARY: case MULTI:
    n.forEach(function(rand) { tagVarRefsExp(rand, innerscope, otherscopes); });
    return;

  case MULTI_CALL:
    tagVarRefsExp(n[0], innerscope, otherscopes);
    n[1].forEach(function(arg) {tagVarRefsExp(arg, innerscope, otherscopes);});
    return;

  case NULLARY:
    if (nt === IDENTIFIER) {
      var boundvar, varname = n.name;
      // search var in innermost scope
      for (var i = innerscope.length - 1; i >= 0; i--) {
        boundvar = innerscope[i];
        if (boundvar.name === varname) {
          //print("stack ref: " + varname);
          n.kind = STACK;
          // if boundvar is a heap var and some of its heap refs get mutated,
          // we may need to update bindings in frames during the cfa.
          n.addr = boundvar.addr; 
          return;
        }
      }
      // search var in other scopes
      for (var i = otherscopes.length - 1; i >= 0; i--) {
        boundvar = otherscopes[i];
        if (boundvar.name === varname) {
          // print("heap ref: " + varname);
          n.kind = boundvar.kind = HEAP;
          n.addr = boundvar.addr;
          return;
        }
      }
      // see if var refers to a core object
      if (core[varname]) {
        n.kind = HEAP;
        n.addr = core[varname];
        if (commonJSmode && varname === "exports") {
          var p = arguments[3]; // exported property name passed as extra arg
          if (p.type === IDENTIFIER)
            exportsObj.lines[p.name] = p.lineno;
        }
        return;
      }
      //print("global: " + varname + " :: " + n.lineno);
      n.kind = GLOBAL;
    }
    return;

  case FUN:
    tagVarRefsFun(n, innerscope, otherscopes);
    return;

  case MULTI_OI: 
    // don't classify property names
    n.forEach(function(prop){tagVarRefsExp(prop[1], innerscope, otherscopes);});
    return;        
  }
}

function tagVarRefsFun(n, innerscope, otherscopes) {
  var fn = n.fname, len, params = n.params;
  len = otherscopes.length;
  // extend otherscopes
  Array.prototype.push.apply(otherscopes, innerscope); 
  // fun name is visible in the body & not a heap ref, add it to scope
  params.push(fn);
  tagVarRefsStm(n.body, params, otherscopes);
  params.pop();
  if (fn.kind !== HEAP) fn.kind = STACK;    
  params.forEach(function(p) {if (p.kind !== HEAP) p.kind=STACK;});
  // trim otherscopes
  otherscopes.splice(len, innerscope.length); 
}

function tagVarRefsStm(n, innerscope, otherscopes) {
  switch (n.type) {

  case SCRIPT:
    var i, j, len, vdecl, vdecls = n.varDecls, fdecl, fdecls = n.funDecls;
    // extend inner scope
    j = innerscope.length;
    Array.prototype.push.apply(innerscope, vdecls);
    fdecls.forEach(function(fd) { innerscope.push(fd.fname); });
    // tag refs in fun decls
    fdecls.forEach(function(fd) { tagVarRefsFun(fd, innerscope, otherscopes);});
    // tag the var refs in the body
    n.forEach(function(stm) { tagVarRefsStm(stm, innerscope, otherscopes); });
    // tag formals
    vdecls.forEach(function(vd) { if (vd.kind !== HEAP) vd.kind = STACK; });
    fdecls.forEach(function(fd) { if (fd.kind !== HEAP) fd.kind = STACK; });    
    //trim inner scope 
    innerscope.splice(j, vdecls.length + fdecls.length); 
    break;

  case BLOCK:
    n.forEach(function(stm) { tagVarRefsStm(stm, innerscope, otherscopes); });
    break;

  case FUNCTION:
    tagVarRefsFun(n, innerscope, otherscopes);
    break;

  case SEMICOLON:
    tagVarRefsExp(n.expression, innerscope, otherscopes);
    break;

  case IF:
    tagVarRefsExp(n.condition, innerscope, otherscopes);
    tagVarRefsStm(n.thenPart, innerscope, otherscopes);
    n.elsePart && tagVarRefsStm(n.elsePart, innerscope, otherscopes);
    break;

  case SWITCH:
    tagVarRefsExp(n.discriminant, innerscope, otherscopes);
    n.cases.forEach(function(branch) {
        branch.caseLabel && 
          tagVarRefsExp(branch.caseLabel, innerscope, otherscopes);
        tagVarRefsStm(branch.statements, innerscope, otherscopes);
      });
    break;

  case FOR: 
    n.setup && tagVarRefsExp(n.setup, innerscope, otherscopes);
    n.condition && tagVarRefsExp(n.condition, innerscope, otherscopes);
    n.update && tagVarRefsExp(n.update, innerscope, otherscopes);
    tagVarRefsStm(n.body, innerscope, otherscopes);
    break;

  case FOR_IN:
    tagVarRefsExp(n.iterator, innerscope, otherscopes);
    tagVarRefsExp(n.object, innerscope, otherscopes);
    tagVarRefsStm(n.body, innerscope, otherscopes);
    break;

  case WHILE:
  case DO:
    tagVarRefsExp(n.condition, innerscope, otherscopes);
    tagVarRefsStm(n.body, innerscope, otherscopes);
    break;

  case TRY:
    tagVarRefsStm(n.tryBlock, innerscope, otherscopes);
    n.catchClauses.forEach(function(clause) {
        var xv = clause.exvar;
        innerscope.push(xv);
        clause.guard && tagVarRefsExp(clause.guard, innerscope, otherscopes);
        tagVarRefsStm(clause.block, innerscope, otherscopes);
        innerscope.pop();
        if (xv.kind !== HEAP) xv.kind = STACK;
      });
    n.finallyBlock && tagVarRefsStm(n.finallyBlock, innerscope, otherscopes);
    break;

  case THROW: 
    tagVarRefsExp(n.exception, innerscope, otherscopes);
    break;

  case RETURN:
    tagVarRefsExp(n.value, innerscope, otherscopes);
    break;
        
  case WITH:
    throw new Error("tagVarRefsStm: WITH not implemented");

  default:
    throw new Error("tagVarRefsStm: unknown case");
  }
  return n;
}


// node, node, node -> undefined
// For every node N in the AST, add refs from N to the node that is normally 
// exec'd after N and to the node that is exec'd if N throws an exception.
function markConts(n, kreg, kexc) {
  var i, len;

  // find functions in expression context and mark their continuations
  function markContsExp(n) {
    switch (opArity[n.type]) {

    case UNARY: case BINARY: case TERNARY: case MULTI:
      n.forEach(markContsExp);
      return;

    case MULTI_CALL:
      markContsExp(n[0]);
      n[1].forEach(markContsExp);
      return;

    case NULLARY: return;

    case FUN:
      markConts(n.body, undefined, undefined);
      return;

    case MULTI_OI:
      n.forEach(function(prop) { markContsExp(prop[1]); });
      return;
    }
  }

  function markContsCase(n, kreg, kexc) {
    var clabel = n.caseLabel, clabelStm, stms = n.statements;
    n.kexc = kexc;
    if (clabel) {
      clabelStm = semiNode(clabel);
      n.kreg = clabelStm;
      markConts(clabelStm, stms, kexc);
    }
    else {
      n.kreg = stms;
    }
    markConts(stms, kreg, kexc);
  }

  function markContsCatch(n, knocatch, kreg, kexc) {
    var guard = n.guard, guardStm, block = n.block;
    if (guard) {// Mozilla catch
      // The guard is of the form (var if expr).
      // If expr is truthy, the catch body is run w/ var bound to the exception.
      // If expr is falsy, we go to the next block (another catch or finally).
      // If the guard or the body throw, the next catches (if any) can't handle
      // the exception, we go to the finally block (if any) directly.      
      markContsExp(guard);
      guardStm = semiNode(guard);
      n.kreg = guardStm;
      guardStm.kcatch = block; // this catch handles the exception
      guardStm.knocatch = knocatch; // this catch doesn't handle the exception
      guardStm.kexc = kexc; // the guard throws a new exception
    }
    markConts(block, kreg, kexc);
  }
  
  switch (n.type) {
  case SCRIPT:
    n.funDecls.forEach(function(fd){markConts(fd.body, undefined, undefined);});
    // fall thru
  case BLOCK:
    n.kexc = kexc;
    len = n.length;
    if (len === 0) 
      n.kreg = kreg;
    else {
      n.kreg = n[0];
      len--;
      for (i=0; i < len; i++) markConts(n[i], n[i+1], kexc);
      markConts(n[len], kreg, kexc);
    }
    return;

  case FUNCTION:
    markConts(n.body, undefined, undefined);
    return;

  case SEMICOLON:
    n.kreg = kreg;
    n.kexc = kexc;
    markContsExp(n.expression);
    return;

    // normally, return & throw don't use their kreg. But this analysis allows 
    // more permissive control flow, to be faster.
  case THROW: 
    n.kreg = kreg;
    n.kexc = kexc;
    markContsExp(n.exception);
    return;

  case RETURN:
    n.kreg = kreg;
    n.kexc = kexc;
    markContsExp(n.value);
    return;

  case IF:
    var thenp = n.thenPart, elsep = n.elsePart, condStm;
    condStm = semiNode(n.condition);
    n.kreg = condStm; // first run the test
    n.kexc = kexc;
    markConts(condStm, thenp, kexc); // ignore result & run the true branch
    markConts(thenp, elsep || kreg, kexc); // then run the false branch
    elsep && markConts(elsep, kreg, kexc);
    return;
        
  case SWITCH:
    var cases = n.cases, discStm;
    discStm = semiNode(n.discriminant);
    n.kreg = discStm; // first run the discriminant, then all branches in order
    n.kexc = kexc;
    markConts(discStm, cases[0], kexc);
    for (i = 0, len = cases.length - 1; i < len; i++) //no empty switch, len >=0
      markContsCase(cases[i], cases[i+1], kexc);
    markContsCase(cases[len], kreg, kexc);
    return;

  case FOR: 
    var body = n.body;
    n.kexc = kexc;
    // Do setup, condition, body & update once.
    var setup = n.setup, setupStm, condition = n.condition, condStm;
    var update = n.update, updStm;
    n.kexc = kexc;
    if (!setup && !condition)
      n.kreg = body;
    else if (setup && !condition) {
      setupStm = semiNode(setup);
      n.kreg = body;
      markConts(setupStm, body, kexc);
    }
    else {// condition exists
      condStm = semiNode(condition);
      markConts(condStm, body, kexc);
      if (setup) {
        setupStm = semiNode(setup);
        n.kreg = setupStm;
        markConts(setupStm, condStm, kexc);  
      }
      else n.kreg = condStm;
    }
    if (update) {
      updStm = semiNode(update);
      markConts(body, updStm, kexc);
      markConts(updStm, kreg, kexc);
    }
    else markConts(body, kreg, kexc);
    return;

  case FOR_IN:
    var body = n.body;
    var iterStm, objStm;
    n.kexc = kexc;
    n.kreg = body;
    markConts(body, kreg, kexc);
    return;

  case WHILE:
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = condStm;
    n.kexc = kexc;
    markConts(condStm, body, kexc);
    markConts(body, kreg, kexc);
    return;

  case DO:
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = body;
    n.kexc = kexc;
    markConts(body, condStm, kexc);
    markConts(condStm, kreg, kexc);
    return;

  case TRY:
    var fin = n.finallyBlock, clause, clauses = n.catchClauses, knocatch;
    // process back-to-front to avoid if-madness
    if (fin) {
      markConts(fin, kreg, kexc);
      knocatch = kexc = kreg = fin; // TRY & CATCHes go to fin no matter what
    }
    for (len = clauses.length, i = len-1; i>=0; i--) {
      clause = clauses[i];
      markContsCatch(clause, knocatch, kreg, kexc);
      knocatch = clause;
    }
    markConts(n.tryBlock, kreg, knocatch || kexc);
    n.kreg = n.tryBlock;
    return;

  case WITH:
    throw new Error("markConts: WITH not implemented");

  default:
    throw new Error("markConts: unknown case");
  }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////   CFA2  code  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// abstract objects and abstract values are different!!!

var heap;
// modified[addr] is a timestamp that shows the last time heap[addr] was updated
var modified; 
var timestamp;
var addrsOfFuns;
var exportsObj;
var commonJSmode;

// A summary contains a function node (fn), an array of abstract values (args),
// a timestamp (ts) and an abstract value (res). It means: when we call fn w/ 
// args and the heap's timestamp is ts, we get back res.

// summaries: a map from addresses of fun nodes to triples {ts, insouts, type},
// where ts is a timestamp, insouts is an array of args-result pairs,
// and type is the join of all args-result pairs.
var summaries;

// seen: a map from addresses of fun nodes to pairs {ts, ins}, where ts is a
// timestamp, and ins is an array of args-arrays.
var seen;

// when initGlobals is called, count has its final value (core objs are in heap)
// FIXME, I'm violating the invariant in "function cfa2". Change it?
function initGlobals() {
  timestamp = 0;
  heap = new Array(count); // reserve heap space, don't grow it gradually
  modified = buildArray(count, timestamp);
  summaries = {}; // We use {} instead of an Array b/c it's sparse.
  seen = {};
  addrsOfFuns = {};
  exportsObj = {lines : {}};
}

// An abstract object o1 is represented as an array object o2. 
// The array elms of o2 are used for special properties of o1 & the properties
// of o2 are used for ordinary properties of o1.
// Can't use Array or Object properties for o2, e.g. if o1 has a "length"
// property then o2 has it and Array.length is shadowed.
// 1st elm: the address of o1's prototype in the heap
// 2nd elm: may contain a function node.
function Aobj(specialProps) {
  this.push(specialProps.proto); /* optional abstract value */
  this.push(specialProps.fun); /* optional function node */
}

Aobj.prototype = new Array();

Aobj.prototype.toType = function() {
  if (this[1]) return funToType(this[1]);
  var c = this.getProp("constructor-");
  var types = [];
  c.forEachObj(function(o) { if (o[1]) types.push(o[1].fname.name); });
  if (types.length === 0) return "Object";
  types.rmDups(function(e1, e2) {return e1 === e2;});
  if (types.length === 1) {
    if (types[0] === "Array") return this.toArrayType();
    return types[0];
  }
  return ("<" + types.join(" | ") + ">");
};

// for homogeneous arrays, include the type of their elms.
Aobj.prototype.toArrayType = function() {
  var elmtype = BOTTOM, self = this;
  this.forEachOwnProp(function(p) {
      if (propIsNumeric(p)) elmtype = avjoin(elmtype, self[p]);
    });
  elmtype = elmtype.toType();
  if (/\|/.test(elmtype) || (elmtype === "any"))
    return "Array";
  else
    return "Array[" + elmtype + "]";
};

// nothing -> function node
Aobj.prototype.getFun = function() { return this[1]; };

// Aval -> undefined
Aobj.prototype.updateProto = function(av) {
  if (this[0]) {
    this[0] = avjoin(av, this[0]);
    if (this[0].objs.length !== av.objs.length)
      ++timestamp;
    return;
  }
  this[0] = av;
  ++timestamp;
};

Aobj.prototype.forEachOwnProp = function(f) {
  for (var p in this) if (/(^-number$)|(^-string$)|-$/.test(p)) f(p);
};

// string -> Aval or undefined
// looks in prototype chain
Aobj.prototype.getProp = function(prop) {
  if (this.hasOwnProperty(prop)) return this[prop];
  if (!this[0]) return undefined; // reached the end of the prototype chain
  var retval = BOTTOM, av;
  this[0].forEachObj(function(proto) {
      av = proto.getProp(prop);
      retval = maybeavjoin(av, retval);
    });
  return retval;
};

// string -> Aval or undefined
// doesn't look in prototype chain
Aobj.prototype.getOwnProp = function(prop) {
  return this[prop];
};

// string, Aval -> undefined
Aobj.prototype.updateProp = function(prop, newv) {
  if (this.hasOwnProperty(prop)) {
    var oldv = this[prop];
    newv = avjoin(newv, oldv);
    this[prop] = newv;
    if ((oldv.base !== newv.base) || (oldv.objs.length !== newv.objs.length)) 
      ++timestamp;
    return;
  }
  this[prop] = newv;
  ++timestamp;
};

// nothing -> boolean
// Return true iff the object has a property whose name satisfies the predicate.
// FIXME: Considers non-enumerable properties also, it shouldn't.
Aobj.prototype.hasProp = function(pred) {
  for (var p in this) { if (pred(p)) return true; }
  if (!this[0]) return false; // reached the end of the prototype chain.
  var found = false;
  this[0].forEachObj(function(proto) {
      if (proto.hasProp(pred)) found = true;
    });
  return found;
};

// string -> boolean
function propIsNumeric(p) {
  return p === "-number" || (/-$/.test(p) && !isNaN(p.slice(0, -1)));
}

Aobj.prototype.hasNumericProp = function(){return this.hasProp(propIsNumeric);};

Aobj.prototype.hasStringProp = function() {
  return this.hasProp(function(p) {
      return p === "-string" || (/-$/.test(p) && isNaN(p.slice(0, -1)));
    });
};

// An abstract value is an obj w/ 2 properties: base is a number whose bits
// encode the base values, objs is an array of sorted heap addresses that 
// denotes a set of objects.
const ANUM = new Aval(1), ASTR = new Aval(2), ABOOL = new Aval(4);
const BOTTOM = new Aval(0), AUNDEF = new Aval(8), ANULL = new Aval(16);
const NOBASEVALS = 0;
const RESTARGS = -1;
const INVALID_TIMESTAMP = -1;

// AUNDEF is the only abstract value that contains just falsy concrete values
// guaranteed. All other Aval`s may contain both truthy & falsy concrete values.

// when creating an abs. value, it can contain at most one object
function Aval(base, objaddr) {
  this.base = base;
  this.objs = [];
  if (objaddr !== undefined) this.objs.push(objaddr);
}

Aval.prototype.toType = function() {
  var i = 1, base = this.base, types = [];
  var basetypes = {1 : "number", 2 : "string", 4 : "boolean",
                   8 : "undefined", 16 : "null"};
  while (i <= 16) {
    if ((base & i) === i) types.push(basetypes[i]);
    i *= 2;
  }
  this.forEachObj(function (o) { types.push(o.toType()); });
  if (types.length === 0) return "any";
  types.rmDups(function(e1, e2) {return e1 === e2;});
  if (types.length === 1) return types[0];
  return ("<" + types.join(" | ") + ">");
};

// fun takes an Aobj
// Convert base values to objects if needed.
Aval.prototype.forEachMayObj = function(fun) {
  var objaddrs = this.objs, base = this.base;
  if ((base & 3) !== 0) { // need to convert a base value to an object
    if ((base & 2) !== 0) fun(genericString);
    if ((base & 1) !== 0) fun(genericNumber);
  }
  if (objaddrs.length === 1) // make common case faster
    fun(heap[objaddrs[0]]);
  else
    objaddrs.forEach(function(addr) { fun(heap[addr]); });
};

// fun takes an Aobj
// Don't convert base values to objects.
Aval.prototype.forEachObj = function(fun) {
  var objaddrs = this.objs;
  if (objaddrs.length === 1) // make common case faster
    fun(heap[objaddrs[0]]);
  else
    objaddrs.forEach(function(addr) { fun(heap[addr]); });
};

Aval.prototype.hasNum = function() { return this.base & 1; };

Aval.prototype.hasStr = function() { return this.base & 2; };

// returns true iff it can guarantee that the Aval is falsy.
Aval.prototype.isFalsy = function() {
  var base = this.base;
  return (this.objs.length === 0) && (base !== 0) && (base % 8 === 0);
};

// Aval, Aval -> Aval
function avjoin(v1, v2) {
  var os1 = v1.objs, os2 = v2.objs, av = new Aval(v1.base | v2.base);
  if (os1.length === 0) 
    av.objs = os2; // need a copy of os2 here? I think not.
  else if (os2.length === 0)
    av.objs = os1; // need a copy of os1 here? I think not.
  else // merge the two arrays
    av.objs = arraymerge(os1, os2);
  return av;
}

// Aval or undefined, Aval or undefined -> Aval or undefined
function maybeavjoin(v1, v2) {
  if (!v1) return v2;
  if (!v2) return v1;
  return avjoin(v1, v2);
}

// Aval, Aval -> boolean
// compares abstract values for equality
function aveq(v1, v2) {
  if (v1.base !== v2.base) return false;
  var os1 = v1.objs, os2 = v2.objs, len = os1.length, i; 
  if (len !== os2.length) return false;
  for (i=0; i<len; i++) if (os1[i] !== os2[i]) return false;
  return true;
}

// function node -> Aval
// If the program doesn't set a function's prototype property, create default.
function makeDefaultProto(n) {
  var o = new Aobj({proto:object_prototype_av});
  o["constructor-"] = new Aval(NOBASEVALS, n.addr);
  var paddr = n.defaultProtoAddr;
  heap[paddr] = o;
  return new Aval(NOBASEVALS, paddr);
}

// heap address, Aval -> undefined
function updateHeapAv(addr, newv) {
  var oldv = heap[addr]; //oldv shouldn't be undefined
  newv = avjoin(newv, oldv);
  heap[addr] = newv;
  if ((oldv.base !== newv.base) || (oldv.objs.length !== newv.objs.length))
    modified[addr] = ++timestamp;
}

// abstract plus
function aplus(v1, v2) {
  if (v1.objs.length !== 0 || v2.objs.length !== 0)
    return new Aval(3);
  var base = ((v1.base | v2.base) & 2); // base is 0 or 2
  if (((v1.base & 29) !== 0) && ((v2.base & 29) !== 0)) base |= 1;
  return new Aval(base);
}

// Invariant: the following code should know nothing about the representation 
// of abstract values.

////////////////////////////////////////////////////////////////////////////////
/////////////////////  CORE AND CLIENT-SIDE OBJECTS   //////////////////////////
////////////////////////////////////////////////////////////////////////////////

var core; // maps the names of JS core objects to their heap addresses

// FIXME: these should ideally be passed around
var object_prototype_av;
var function_prototype_av;
var array_prototype_av;
var regexp_prototype_av;
// used to automatically convert base values to objs and call methods on them
var genericNumber;
var genericString;

// create the JS core objects in heap & fill in core
function initCoreObjs() {

  // string, function -> function node
  function funToNode(name, code) {
    var n = new Node({}, FUNCTION);
    n.fname = idNode({}, name);
    n.builtin = true;
    n.body = code;
    return n;
  }

  // Aobj, string, function -> undefined
  function attachMethod(o, mname, mcode) {
    var foaddr = ++count;
    heap[foaddr] = new Aobj({fun : funToNode(mname, mcode)});
    o.updateProp(mname + "-", new Aval(NOBASEVALS, foaddr));
  }

  function toStr(args) { return new Ans(ASTR, undefined); }

  function toNum(args) { return new Ans(ANUM, undefined); }

  function toBool(args) { return new Ans(ABOOL, undefined); }


  // Object.prototype
  var op = new Aobj({}), opaddr = ++count, opav = new Aval(NOBASEVALS, opaddr);
  object_prototype_av = opav;
  heap[opaddr] = op;
  attachMethod(op, "hasOwnProperty", toBool);
  attachMethod(op, "toString", toStr);
  attachMethod(op, "valueOf",
               function(args) { return new Ans(args[0], undefined); });

  // Object.__proto__ (same as Function.prototype)
  var o_p = new Aobj({proto:opav}), o_paddr = ++count;
  var o_pav = new Aval(NOBASEVALS, o_paddr);
  function_prototype_av = o_pav;
  heap[o_paddr] = o_p;
  attachMethod(o_p, "toString", toStr); 

  // Function.prototype.prototype
  var fpp = new Aobj({proto : opav}), fppaddr = ++count;
  var fppav = new Aval(NOBASEVALS, fppaddr);
  heap[fppaddr] = fpp;
  o_p.updateProp("prototype-", fppav);
  fpp.updateProp("constructor-", o_pav);

  // Object
  var _Object = (function () {
      // nonew is used when Object is called w/out new 
      var nonew = new Aobj({proto : opav}), nonewaddr = ++count;
      var nonewav = new Aval(NOBASEVALS, nonewaddr);
      heap[nonewaddr] = nonew;

      return function (args, withNew) {
        var retval = withNew ? args[0] : nonewav;
        var arg = args[1];
        if (!arg) {
          retval.forEachObj(function (o) { o.updateProto(opav); });
          return new Ans(retval, undefined);
        }
        // else call a suitable constructor, hasn't been defined yet. FIXME
      };
    })();
  var o = new Aobj({proto : o_pav, fun : funToNode("Object", _Object)});
  var oaddr = ++count, oav = new Aval(NOBASEVALS, oaddr), oavaddr = ++count;
  heap[oaddr] = o;
  heap[oavaddr] = oav;
  // Object is a heap var that will contain an Aval that points to o
  core["Object"] = oavaddr;
  o.updateProp("prototype-", opav);
  op.updateProp("constructor-", oav);

  // Function
  var f = new Aobj({proto : o_pav}), faddr = ++count;
  var fav = new Aval(NOBASEVALS, faddr), favaddr = ++count;
  heap[faddr] = f;
  heap[favaddr] = fav;
  core["Function"] = favaddr;
  f.updateProp("prototype-", o_pav);
  o_p.updateProp("constructor-", fav);
  
  (function () {
    // Array.prototype
    var ap = new Aobj({proto:opav}), apaddr = ++count;
    var apav = new Aval(NOBASEVALS, apaddr);
    array_prototype_av = apav;
    heap[apaddr] = ap;

    function putelms (args) {
      args[0].forEachObj(function (o) {
          for (var i = 1, len = args.length; i < len; i++)
            o.updateProp("-number", args[i]);
        });
      return new Ans(ANUM, undefined);
    }
    attachMethod(ap, "join", toStr);
    attachMethod(ap, "pop",
                 function(args) {
                   var av = BOTTOM, av2;
                   args[0].forEachObj(function (o) {
                       av2 = o.getOwnProp("-number");
                       if (av2) av = avjoin(av, av2);
                     });
                   return new Ans(av || AUNDEF, undefined);
                 });
    attachMethod(ap, "push", putelms);
    attachMethod(ap, "shift", // unsound: shift doesn't actually rm any elm
                 function(args) {
                   var av = BOTTOM, av2;
                   args[0].forEachObj(function (o) {
                       av2 = o.getOwnProp("0-");
                       if (av2) av = avjoin(av, av2);
                       av2 = o.getOwnProp("-number");
                       if (av2) av = avjoin(av, av2);
                     });
                   return new Ans(av || AUNDEF, undefined);
                 });
    attachMethod(ap, "toString", toStr); 
    attachMethod(ap, "unshift", putelms);

    // Array
    var _Array = (function () {
        // nonew is used when Array is called w/out new 
        var nonew = new Aobj({proto : apav}), nonewaddr = ++count;
        var nonewav = new Aval(NOBASEVALS, nonewaddr);
        heap[nonewaddr] = nonew;

        return function(args, withNew) {
          var retval = withNew ? args[0] : nonewav;
          var arglen = args.length;
          retval.forEachObj(function (o) {
              o.updateProto(apav);
              o.updateProp("length-", ANUM);
            });
          if (arglen <= 2) // new Array(), new Array(size)
            ;
          else { // new Array(elm1, ... , elmN)
            retval.forEachObj(function (o) {
                for (var i = 1; i < arglen; i++) {
                  o.updateProp((i - 1) + "-", args[i]);
                }
              });
          }
          return new Ans(retval, undefined);
        };
      })();
    var a = new Aobj({proto : o_pav, fun : funToNode("Array", _Array)});
    var aaddr = ++count, aav = new Aval(NOBASEVALS, aaddr), aavaddr = ++count;
    heap[aaddr] = a;
    heap[aavaddr] = aav;
    core["Array"] = aavaddr;
    a.updateProp("prototype-", apav);
    ap.updateProp("constructor-", aav);
  })();

  (function () {
    // Number.prototype
    var np = new Aobj({proto:opav}), npaddr = ++count;
    var npav = new Aval(NOBASEVALS, npaddr);
    heap[npaddr] = np;
    attachMethod(np, "toString", toStr);
    attachMethod(np, "valueOf", toNum);
    // create generic number object
    genericNumber = new Aobj({proto : npav});
    heap[++count] = genericNumber;

    // Number
    function _Number(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(npav); });
        return new Ans(args[0], undefined);
      }
      return new Ans(ANUM, undefined);
    }
    var n = new Aobj({proto : o_pav, fun : funToNode("Number", _Number)});
    var naddr = ++count, nav = new Aval(NOBASEVALS, naddr), navaddr = ++count;
    heap[naddr] = n;
    heap[navaddr] = nav;
    core["Number"] = navaddr;
    n.updateProp("prototype-", npav);
    np.updateProp("constructor-", nav);
  })();

  (function () {
    // String.prototype
    var sp = new Aobj({proto:opav}), spaddr = ++count;
    var spav = new Aval(NOBASEVALS, spaddr);
    heap[spaddr] = sp;
    attachMethod(sp, "valueOf", toStr);
    attachMethod(sp, "charAt", toStr);
    attachMethod(sp, "charCodeAt", toNum);
    attachMethod(sp, "indexOf", toNum);
    attachMethod(sp, "lastIndexOf", toNum);
    attachMethod(sp, "slice", toStr);
    attachMethod(sp, "substr", toStr);
    attachMethod(sp, "substring", toStr);
    attachMethod(sp, "toString", toStr);
    // all Arrays returned by calls to split are merged in one
    var osplit = new Aobj({proto : array_prototype_av}), osplitaddr = ++count;
    var osplitav = new Aval(NOBASEVALS, osplitaddr);
    heap[osplitaddr] = osplit;
    osplit.updateProp("-number", ASTR);
    attachMethod(sp, "split",
                 function(args) { return new Ans(osplitav, undefined); });
    // create generic string object
    genericString = new Aobj({proto : spav});
    heap[++count] = genericString;

    // String
    function _String(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(spav); });
        return new Ans(args[0], undefined);
      }
      return new Ans(ASTR, undefined);
    }
    var s = new Aobj({proto : o_pav, fun : funToNode("String", _String)});
    var saddr = ++count, sav = new Aval(NOBASEVALS, saddr), savaddr = ++count;
    heap[saddr] = s;
    heap[savaddr] = sav;
    core["String"] = savaddr;
    s.updateProp("prototype-", spav);
    sp.updateProp("constructor-", sav);
  })();

  (function () {
    // Error.prototype
    var ep = new Aobj({proto:opav}), epaddr = ++count;
    var epav = new Aval(NOBASEVALS, epaddr);
    heap[epaddr] = ep;
    attachMethod(ep, "toString", toStr);

    // Error
    function _Error(args) {
      args[0].forEachObj(function (o) {
          o.updateProto(epav);
          o.updateProp("message-", ASTR);
        });
      return new Ans(args[0], undefined);
    }
    var e = new Aobj({proto : o_pav, fun : funToNode("Error", _Error)});
    var eaddr = ++count, eav = new Aval(NOBASEVALS, eaddr), eavaddr = ++count;
    heap[eaddr] = e;
    heap[eavaddr] = eav;
    core["Error"] = eavaddr;
    e.updateProp("prototype-", epav);
    ep.updateProp("constructor-", eav);
    ep.updateProp("name-", ASTR);
  })();

  (function () {
    // RegExp.prototype
    var rp = new Aobj({proto:opav}), rpaddr = ++count;
    var rpav = new Aval(NOBASEVALS, rpaddr);
    regexp_prototype_av = rpav;
    heap[rpaddr] = rp;
    attachMethod(rp, "test", toBool);

    // RegExp
    function _RegExp(args) {
      args[0].forEachObj(function (o) { o.updateProto(rpav); });
      return new Ans(args[0], undefined);
    }
    var r = new Aobj({proto : o_pav, fun : funToNode("RegExp", _RegExp)});
    var raddr = ++count, rav = new Aval(NOBASEVALS, raddr), ravaddr = ++count;
    heap[raddr] = r;
    heap[ravaddr] = rav;
    core["RegExp"] = ravaddr;
    r.updateProp("prototype-", rpav);
    rp.updateProp("constructor-", rav);
  })();

  (function () {
    // Date.prototype
    var dp = new Aobj({proto:opav}), dpaddr = ++count;
    var dpav = new Aval(NOBASEVALS, dpaddr);
    heap[dpaddr] = dp;
    attachMethod(dp, "getDate", toNum);
    attachMethod(dp, "getDay", toNum);
    attachMethod(dp, "getFullYear", toNum);
    attachMethod(dp, "getHours", toNum);
    attachMethod(dp, "getMilliseconds", toNum);
    attachMethod(dp, "getMinutes", toNum);
    attachMethod(dp, "getMonth", toNum);
    attachMethod(dp, "getSeconds", toNum);
    attachMethod(dp, "getTime", toNum);
    attachMethod(dp, "getTimezoneOffset", toNum);
    attachMethod(dp, "getYear", toNum);
    attachMethod(dp, "setTime", toNum);
    attachMethod(dp, "toString", toStr);
    attachMethod(dp, "valueOf", toNum);

    // Date
    function _Date(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(dpav); });
        return new Ans(args[0], undefined);
      }
      return new Ans(ASTR, undefined);
    }
    var d = new Aobj({proto : o_pav, fun : funToNode("Date", _Date)});
    var daddr = ++count, dav = new Aval(NOBASEVALS, daddr), davaddr = ++count;
    heap[daddr] = d;
    heap[davaddr] = dav;
    core["Date"] = davaddr;
    d.updateProp("prototype-", dpav);
    dp.updateProp("constructor-", dav);
  })();
}


////////////////////////////////////////////////////////////////////////////////
//////////////////////////   EVALUATION FUNCTIONS   ////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// frame, identifier node, Aval -> undefined
function frameSet(fr, param, val) {
  fr[param.addr] = [val, timestamp]; // record when param was bound to val
}

// frame, identifier node -> Aval
function frameGet(fr, param) {
  var pa = param.addr, binding = fr[pa];
  if (binding[1] < modified[pa]) {
    // if binding changed in heap, change it in frame to be sound
    binding[0] = avjoin(binding[0], heap[pa]);
    binding[1] = timestamp;
  }
  return binding[0];
}

// fun. node, array of Aval  -> Aval or false
function searchSummary(n, args) {
  var summary = summaries[n.addr], insouts, pair;
  if (summary.ts < timestamp) return false;
  insouts = summary.insouts;
  for (var i = 0, len = insouts.length; i < len; i++) {
    pair = insouts[i];
    if (arrayeq(aveq, args, pair[0])) return pair[1];
  }
  return false;
}

// function node -> boolean
// check if any summary exists for this function node
function existsSummary(n) {
  return summaries[n.addr].ts !== INVALID_TIMESTAMP;
}

var countsums = 0;
// fun. node, array of Aval, Aval  -> undefined
function addSummary(n, args, retval) {
  countsums++;
  if ((countsums % 1000) === 0) print(countsums + " sum`s");

  var addr = n.addr, summary = summaries[addr];
  if (summary.ts === timestamp)
    summary.insouts.push([args, retval]);
  else { // discard summaries for old timestamps.
    summary.ts = timestamp;
    summary.insouts = [[args, retval]];
  }
  // join new summary w/ earlier ones.
  var insjoin = summary.type[0];
  for (var i = 0, len = insjoin.length; i < len; i++)
    insjoin[i] = avjoin(insjoin[i], args[i] || AUNDEF/*arg mismatch*/);
  summary.type[1] = avjoin(summary.type[1], retval);
}

// function node -> string
function funToType(n) {
  var addr = n.addr, summary = summaries[addr];
  if (summary.ts === INVALID_TIMESTAMP) // the function was never called
    return "function";
  var insjoin = summary.type[0], instypes = [], outtype;
  for (var i = 1, len = insjoin.length; i < len; i++)
    instypes[i - 1] = insjoin[i].toType();
  outtype = n.withNew ? insjoin[0].toType() : summary.type[1].toType();
  return (outtype + " function(" + instypes.join(", ") +")");
}

function showSummaries() {
  for (var addr in summaries) {
    var f = addrsOfFuns[addr];
    print(f.fname.name + ": " + funToType(f));
  }
}

// function node, array of Aval -> boolean
function searchSeen(n, args) {
  var nseen = seen[n.addr];
  if (nseen.ts < timestamp) return false;
  return nseen.ins.member(function(elm) { return arrayeq(aveq, args, elm); });
}

// function node, array of Aval -> undefined
function addSeen(n, args) {
  var nseen = seen[n.addr];
  if (nseen.ts === timestamp)
    nseen.ins.push(args);
  else {
    nseen.ts = timestamp;
    nseen.ins = [args];
  }
}

// evalExp & friends use Ans to return tuples
function Ans(v, fr) {
  this.v = v; // evalExp puts abstract values here, evalStm puts statements
  this.fr = fr; // frame
}

// Initialize the heap for each fun decl, var decl and heap var.
// Because of this function, we never get undefined by reading from heap.
// Must be run after initGlobals and after initCoreObjs.
function initDeclsInHeap(n) {

  function initDeclsExp(n) {
    switch (opArity[n.type]) {

    case MULTI:
      if (n.type === ARRAY_INIT)
        heap[n.addr] = new Aobj({proto:array_prototype_av});
      //fall thru
    case UNARY: case BINARY: case TERNARY:
      n.forEach(initDeclsExp);
      return;

    case MULTI_CALL:
      if (n.type === NEW_WITH_ARGS)
        heap[n.addr] = new Aobj({});
      initDeclsExp(n[0]);
      n[1].forEach(initDeclsExp);
      return;

    case NULLARY:
      if (n.type === REGEXP)
        heap[n.addr] = new Aobj({proto:regexp_prototype_av});
      return;

    case FUN:
      initDeclsFun(n);
      return;

    case MULTI_OI:
      heap[n.addr] = new Aobj({proto:object_prototype_av});
      n.forEach(function(prop) {initDeclsExp(prop[0]); initDeclsExp(prop[1]);});
      return;
    }
  }

  function initDeclsFun(n) {
    var objaddr = n.addr, fn = n.fname;
    // heap[objaddr] will point to this object throughout the analysis.
    heap[objaddr] = new Aobj({fun:n, proto:function_prototype_av});
    if (fn.kind === HEAP)
      heap[fn.addr] = new Aval(NOBASEVALS, objaddr);
    n.params.forEach(function(p) {
        if (p.kind === HEAP) heap[p.addr] = BOTTOM;
      });
    addrsOfFuns[objaddr] = n;
    // initialize summaries and seen
    summaries[objaddr] = {
    ts: INVALID_TIMESTAMP,
    insouts: [],
    type: [buildArray(n.params.length + 1, BOTTOM), BOTTOM] //arg 0 is for THIS
    };
    seen[objaddr] = {ts: INVALID_TIMESTAMP, ins: []};
    initDeclsInHeap(n.body);
  }

  switch (n.type) {
  case SCRIPT:
    n.funDecls.forEach(initDeclsFun);
    n.varDecls.forEach(function(vd) {
        if (vd.kind === HEAP) heap[vd.addr] = BOTTOM;
      });
    // fall thru
  case BLOCK:
    n.forEach(initDeclsInHeap);
    return;

  case FUNCTION:
    initDeclsFun(n);
    return;

  case IF:
    initDeclsExp(n.condition);
    initDeclsInHeap(n.thenPart);
    n.elsePart && initDeclsInHeap(n.elsePart);
    return;
    
  case SWITCH:
    initDeclsExp(n.discriminant);
    n.cases.forEach(function(branch) { initDeclsInHeap(branch.statements); });
    return;

  case FOR:
    n.setup && initDeclsExp(n.setup);
    n.condition && initDeclsExp(n.condition);
    n.update && initDeclsExp(n.update);
    initDeclsInHeap(n.body);
    return;

  case FOR_IN:
    initDeclsExp(n.iterator);
    initDeclsExp(n.object);
    initDeclsInHeap(n.body);
    return;

  case WHILE: case DO:
    initDeclsExp(n.condition);
    initDeclsInHeap(n.body);
    return;

  case TRY:
    initDeclsInHeap(n.tryBlock);
    n.catchClauses.forEach(function(clause) {
        clause.guard && initDeclsExp(clause.guard);
        initDeclsInHeap(clause.block);
      });
    n.finallyBlock && initDeclsInHeap(n.finallyBlock);
    return;

  case RETURN:
    initDeclsExp(n.value);
    return;

  case THROW:
    initDeclsExp(n.exception);
    return;

  case SEMICOLON:
    initDeclsExp(n.expression);
    return;

  case WITH:
    throw new Error("initDeclsInHeap: WITH not implemented");
  }
}

// node, answer, Aval or undefined -> Ans
// use n to get an lvalue, do the assignment and return the rvalue
function evalLval(n, ans, oldlval) {
  var rval = ans.v, fr = ans.fr, nt = n.type;
  var oldlval, errval = BOTTOM;

  function updateObjsProp(avobjs, pname, pval) {
    // FIXME: record error if avobjs contains base values
    avobjs.forEachObj(function(o) { o.updateProp(pname, pval); });
  }

  if (n.assignOp) {
    if (n.assignOp === PLUS)
      rval = aplus(rval, oldlval);
    else
      rval = ANUM;
  }

  switch (nt) {
  case IDENTIFIER:
    switch (n.kind) {
    case STACK:
      frameSet(fr, n, avjoin(frameGet(fr, n), rval));      
      // if (aveq(frameGet(fr, n), BOTTOM)) // FIXME: record unbound variable
      break;
    case HEAP:
      updateHeapAv(n.addr, rval);
      // if (aveq(heap[n.addr], BOTTOM)) // FIXME: record unbound variable
      break;
    default:
      //print("FIXME, global lval: " + n.name);
      break;
    }
    break;

  case INDEX:
    var prop = n[1], pt = prop.type;
    var  ansobj = evalExp(n[0], fr), avobj = ansobj.v;
    fr = ansobj.fr;
    if (ansobj.err) errval = ansobj.err;    
    if ((pt === NUMBER) || (pt === STRING)) {
      updateObjsProp(avobj, prop.value.toString() + "-", rval);
      break;
    }
    var ansprop = evalExp(prop, fr), avprop = ansprop.v;
    if (ansprop.err) errval = avjoin(errval, ansprop.err);
    if (avprop.hasNum()) updateObjsProp(avobj, "-number", rval);
    if (avprop.hasStr()) updateObjsProp(avobj, "-string", rval);
    break;

  case DOT: case DOT_PROTO:
    var ans2 = evalExp(n[0], fr), prop;
    if (ans2.err) errval = ans2.err;
    prop = (nt === DOT) ? n[1].name : "prototype-";
    fr = ans2.fr;
    updateObjsProp(ans2.v, prop, rval);
    break;

  default:
    throw new Error("evalLval unknown case");
  }

  if (ans.err) errval = avjoin(errval, ans.err);
  ans = new Ans(rval, fr);
  ans.err = errval;
  return ans;
}

// FIXME: will be rewritten for fast dispatch. Could tag AST w/ refs to funs
// in a pass b4 abs int.
// node, frame -> Ans
function evalExp(n, fr) {
  var ans, ans1, ans2, nt = n.type, av, errval;

  // objav is an Aval denoting the object(s) whose property we access
  function evalPropertyAccess(objav, prop /* string */) {
    var av = BOTTOM, av2;
    // FIXME: record error if ans.v contains base values
    objav.forEachMayObj(function(o) {
        av2 = o.getProp(prop);
        av = avjoin(av, av2 ? av2 : AUNDEF);
      });
    return aveq(av, BOTTOM) ? AUNDEF : av;
  }
  
  switch (nt) {
  case IDENTIFIER:
    switch (n.kind) {
    case STACK:
      // if (aveq(frameGet(fr, n), BOTTOM)) // FIXME: record error, unbound var
      return new Ans(frameGet(fr, n), fr);
    case HEAP:
      // if (aveq(heap[n.addr], BOTTOM)) // FIXME: record unbound variable
      return new Ans(heap[n.addr], fr);
    default:
      //print("FIXME, global variable: " + n.name);
      return new Ans(BOTTOM, fr);
    }

  case NUMBER: return new Ans(ANUM, fr);
        
  case STRING: return new Ans(ASTR, fr);

  case TRUE: case FALSE: return new Ans(ABOOL, fr);

  case NULL:
    return new Ans(ANULL, fr);

  case REGEXP:
    return new Ans(new Aval(NOBASEVALS, n.addr), fr);
    
  case THIS: return new Ans(fr.thisav, fr);

  case UNARY_PLUS: case UNARY_MINUS:
  case INCREMENT: case DECREMENT: case BITWISE_NOT:
    ans = evalExp(n[0], fr);
    ans.v = ANUM;
    return ans;

  case NOT:
    ans = evalExp(n[0], fr);
    ans.v = ABOOL;
    return ans;

  case TYPEOF:
    ans = evalExp(n[0], fr);
    ans.v = ASTR;
    return ans;

  case VOID:
    ans = evalExp(n[0], fr);
    ans.v = AUNDEF;
    return ans;

  case DELETE: // unsound: I'm not deleting anything
    ans = evalExp(n[0], fr);
    ans.v = avjoin(ABOOL, AUNDEF);
    return ans;

  case EQ: case NE: case STRICT_EQ: case STRICT_NE:
  case LT: case LE: case GE: case GT:
  case INSTANCEOF: case IN:
    ans1 = evalExp(n[0], fr);
    ans2 = evalExp(n[1], ans1.fr);
    ans2.v = ABOOL;
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;

  case AND:
    ans1 = evalExp(n[0], fr);
    av = ans1.v;
    if (av.isFalsy()) return ans1;
    ans2 = evalExp(n[1], ans1.fr);
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    // we can't guarantee that ans1 is only truthy, must join it in result.
    ans2.v = avjoin(av, ans2.v);
    return ans2;

  case OR:
    ans1 = evalExp(n[0], fr);
    ans2 = evalExp(n[1], ans1.fr);
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    if (ans1.v.isFalsy()) return ans2;
    ans2.v = avjoin(ans1.v, ans2.v);
    return ans2;

  case PLUS:
    ans1 = evalExp(n[0], fr);
    ans2 = evalExp(n[1], ans1.fr);
    ans2.v = aplus(ans1.v, ans2.v);
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;

  case MINUS: case MUL: case DIV: case MOD:
  case BITWISE_OR: case BITWISE_XOR: case BITWISE_AND:
  case LSH: case RSH: case URSH:
    ans1 = evalExp(n[0], fr);
    ans2 = evalExp(n[1], ans1.fr);
    ans2.v = ANUM;
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;

  case PLUS_ASSIGN:
    // computing n[0] twice for += is better than checking every lhs in evalLval
    ans = evalExp(n[0], fr);
    return evalLval(n[0], evalExp(n[1], fr), ans.v);

  case ASSIGN:
    return evalLval(n[0], evalExp(n[1], fr));

  case HOOK:
    ans = evalExp(n[0], fr);
    ans1 = evalExp(n[1], ans.fr);
    ans2 = evalExp(n[2], ans1.fr);
    ans2.err = maybeavjoin(ans.err, maybeavjoin(ans1.err, ans2.err));
    ans2.v = avjoin(ans1.v, ans2.v);
    return ans2;

  case FUNCTION:
    return new Ans(new Aval(NOBASEVALS, n.addr), fr);

  case COMMA:
    n.forEach(function(exp) {
        ans = evalExp(exp, fr);
        av = ans.v; // keep last one
        fr = ans.fr;
        errval = maybeavjoin(errval, ans.err);
      });
    ans.v = av;
    ans.err = errval;
    return ans;

  case OBJECT_INIT:
    var objaddr = n.addr, newobj = heap[objaddr];
    n.forEach(function(pinit) {
        ans = evalExp(pinit[1], fr);
        fr = ans.fr;
        newobj.updateProp(pinit[0].name, ans.v);
        errval = maybeavjoin(errval, ans.err);
      });
    ans = new Ans(new Aval(NOBASEVALS, objaddr), fr);
    ans.err = errval;
    return ans;

  case ARRAY_INIT:
    var arrayaddr = n.addr, newarray = heap[arrayaddr];
    n.forEach(function(elm, i) {
        ans = evalExp(elm, fr);
        fr = ans.fr;
        newarray.updateProp(i + "-", ans.v);
        errval = maybeavjoin(errval, ans.err);
      });
    ans = new Ans(new Aval(NOBASEVALS, arrayaddr), fr);
    ans.err = errval;
    return ans;

  case DOT_PROTO:
    var ans = evalExp(n[0], fr), av = BOTTOM, av2;
    errval = ans.err;
    // FIXME: record error if ans.v contains base values
    ans.v.forEachMayObj(function(o) {
        var clos = o.getFun(), proto;
        if (!clos) {
          av2 = o.getProp("prototype-");
          av = avjoin(av, av2 ? av2 : AUNDEF);
        }
        else if (proto = o.getOwnProp("prototype-")) {
          av = avjoin(av, proto);
        }
        else {// create default prototype and return it
          proto = makeDefaultProto(clos);
          o.updateProp("prototype-", proto);
          av = avjoin(av, proto);
        }
      });
    ans2 = new Ans(av, ans.fr);
    ans2.thisav = ans.v; // used by method calls
    ans2.err = errval;
    return ans2;

  case INDEX:
    var prop = n[1], pt = prop.type, ansobj = evalExp(n[0], fr); 
    errval = ansobj.err;
    // if [] notation is used with a constant, try to be precise.
    if ((pt === NUMBER) || (pt === STRING)) {
      ansobj.thisav = ansobj.v;
      ansobj.v = evalPropertyAccess(ansobj.v, prop.value.toString() + "-");
      ansobj.err = errval;
      return ansobj;
    }
    // else merge nums to a generic number and strings to a generic string.
    var ansprop = evalExp(prop, ansobj.fr), avprop = ansprop.v;
    ansobj.err = maybeavjoin(errval, ansprop.err);
    ansobj.thisav = ansobj.v;
    ansobj.v = BOTTOM;
    //FIXME: should be improved to also look for individual num/str properties.
    // A property "-number" in the input becomes "-number-". No shadowing.
    if (avprop.hasNum()) 
      ansobj.v = evalPropertyAccess(ansobj.thisav, "-number");
    if (avprop.hasStr())
      ansobj.v = avjoin(ansobj.v, evalPropertyAccess(ansobj.thisav, "-string"));
    return ansobj;

  case DOT:
    ans = evalExp(n[0], fr);
    ans.thisav = ans.v; // used by method calls
    ans.v = evalPropertyAccess(ans.v, n[1].name);
    return ans;
    
  case CALL:
  case NEW_WITH_ARGS:
    var rands = [undefined /* reserved for THIS */], retval = BOTTOM, rator;
    ans = evalExp(n[0], fr);
    rator = ans.v;
    fr = ans.fr;
    errval = ans.err;
    // evaluate arguments
    n[1].forEach(function(rand) {
        ans1 = evalExp(rand, fr);
        rands.push(ans1.v);
        fr = ans1.fr;
        errval = maybeavjoin(errval, ans1.err);
      });
    if (nt === CALL) {
      // FIXME: bind rands[0] to the global object if (!ans.thisav)
      rands[0] = (ans.thisav ? ans.thisav : BOTTOM);
      // FIXME: record error if rator contains base vals and non-functions
      // call each function that can flow to the operator position
      rator.forEachMayObj(function(o) {
          var clos = o.getFun();
          if (!clos) return; 
          ans = evalFun(clos, rands, false);
          retval = avjoin(retval, ans.v);
          errval = maybeavjoin(errval, ans.err);
        });
    }
    else {
      var objaddr = n.addr, thisobj = heap[objaddr];
      rands[0] = new Aval(NOBASEVALS, objaddr);
      // FIXME: record error if rator contains base vals and non-functions
      rator.forEachMayObj(function(o) {
          var clos = o.getFun(), proto;
          if (!clos) return;
          if (!(proto = o.getOwnProp("prototype-"))) {
            // create default prototype & use it
            proto = makeDefaultProto(clos);
            o.updateProp("prototype-", proto);
          }
          thisobj.updateProto(proto);
          // if a fun is called both w/ and w/out new, assume it's a constructor
          clos.withNew = true;
          ans = evalFun(clos, rands, true);
          if (clos.hasReturn) // constructor uses return
            retval = avjoin(retval, ans.v);
          else // constructor doesn't use return
            retval = avjoin(retval, rands[0]);
          errval = maybeavjoin(errval, ans.err);
        });
    }
    ans = new Ans(retval, fr);
    ans.err = errval;
    return ans;

  case ARGUMENTS:
    var index = n[0], ps = n.arguments, restargs = fr[RESTARGS] || BOTTOM;
    if (index.type === NUMBER) {
      var iv = index.value;
      if (iv < 0)
        av = AUNDEF;
      else if (iv < ps.length)
        av = frameGet(fr, ps[iv]);
      else
        av = restargs; // unsound: not checking if iv > #args
    }
    else {
      ans = evalExp(index, fr);
      fr = ans.fr;
      errval = ans.err;
      av = BOTTOM;
      // when we don't know the index, we return the join of all args
      ps.forEach(function(p) { av = avjoin(av, frameGet(fr, p)); });
      av = avjoin(av, restargs);
    }
    ans = new Ans(av, fr);
    ans.err = errval;
    return ans;
    
  default:
    print("evalExp unhandled case: " + nt + ", line " + n.lineno);
    return new Ans(BOTTOM, fr);
  }
}

// statement, frame -> Ans
function evalStm(n, fr) {
  var nt = n.type, ans, errval, av;
  switch (nt) {
  case BLOCK: case IF: case SWITCH: case CASE: case DEFAULT:
  case FOR: case DO: case WHILE: case TRY:
    return new Ans(n.kreg, fr);

  case SEMICOLON: 
    ans = evalExp(n.expression, fr);
    ans.v = n.kreg;
    return ans;

  case CATCH:
    frameSet(fr, n.exvar, n.errav);
    return new Ans(n.block, fr);
    
  case THROW:
    ans = evalExp(n.exception, fr);
    ans.err = maybeavjoin(ans.err, ans.v);
    ans.v = n.kreg;
    return ans;
    
  case FOR_IN:
    var av = BOTTOM;
    ans = evalExp(n.object, fr);
    errval = ans.err;
    ans.v.forEachObj(function(o) {
        if (o.hasNumericProp()) av = avjoin(av, ANUM);
        if (o.hasStringProp()) av = avjoin(av, ASTR);
      });
    ans.v = av;
    ans = evalLval(n.iterator, ans);
    errval = maybeavjoin(errval, ans.err);
    ans.v = n.kreg;
    return ans;

    // case FUNCTION: // fix for fun decls in blocks

    // case WITH: 

  default:
    throw new Error("evalStm: unknown case: " + n.type + ", line " + n.lineno);
  }
}

// function node, array of Aval, optional boolean -> Ans w/out fr
function evalFun(fn, args, withNew) {
  var ans, n, params, fr, w /* workset */, retval, errval, script = fn.body;

  // stm node (exception continuation), av (exception value) -> undefined
  function stmThrows(n, errav) {
    if (n) {// many throws in the same try go to the same catch => need to join
      n.errav = maybeavjoin(n.errav, errav);
      w.push(n);
    }
    else
      errval = maybeavjoin(errval, errav);
  }

  // treat built-in functions specially
  if (fn.builtin) return fn.body(args, withNew);

  retval = searchSummary(fn, args);
  if (retval) return new Ans(retval, undefined);
  // When a call eventually leads to itself, stop processing.
  // Some other branch may make the recursion bottom out.
  // It's sound & precise to return BOTTOM; it doesn't contribute to the result.
  if (searchSeen(fn, args))
    return new Ans(BOTTOM, undefined);
  else
    addSeen(fn, args);

  w = [];
  fr = {};
  retval = BOTTOM;
  params = fn.params;
  frameSet(fr, fn.fname, new Aval(NOBASEVALS, fn.addr));
  // args[0] is always the obj that THIS is bound to.
  // THIS never has a heap ref, so its entry in the frame is special.
  fr.thisav = args[0];
  for (var i = 0, len = params.length; i < len; i++) { //Bind formals to actuals
    var param = params[i], arg = args[i+1] || AUNDEF; // maybe #args < #params
    if (param.kind === HEAP) updateHeapAv(param.addr, arg);
    frameSet(fr, param, arg);
  }
  var argslen = args.length;
  if ((++i) < argslen) { // handling of extra arguments
    var restargs = BOTTOM;
    for (; i<argslen; i++) restargs = avjoin(restargs, args[i]);
    fr[RESTARGS] = restargs; // special entry in the frame.
  }
  // bind a non-init`d var to bottom, different from assigning undefined to it.
  script.varDecls.forEach(function(vd) { frameSet(fr, vd, BOTTOM); });
  // bind the fun names in the frame.
  script.funDecls.forEach(function(fd) {
      frameSet(fr, fd.fname, new Aval(NOBASEVALS, fd.addr));
    });

  w.push(script.kreg);
  while (w.length !== 0) {
    n = w.pop();
    if (n === undefined) continue;
    if (n.type === RETURN) {
      ans = evalExp(n.value, fr);
      // fr is passed to exprs/stms & mutated, no need to join(fr, ans.fr)
      fr = ans.fr;
      retval = avjoin(retval, ans.v);
      w.push(n.kreg);
      if (ans.err) stmThrows(n.kexc, ans.err);
    }
    else {
      ans = evalStm(n, fr);
      fr = ans.fr;
      w.push(ans.v);
      if (ans.err) stmThrows(n.kexc, ans.err);
    }
  }
  // A function that doesn't have a RETURN sets ans.noreturn;
  if (!fn.hasReturn) retval = AUNDEF;
  ans = new Ans(retval, undefined);
  addSummary(fn, args, retval);
  if (errval) ans.err = errval; // exception wasn't caught in this function
  return ans;
}

// maybe merge with evalFun at some point
function evalToplevel(tl) {
  var w /* workset */, fr, n, ans;
  w = [];
  fr = {};
  initDeclsInHeap(tl);
  
  // bind a non-init`d var to bottom, different from assigning undefined to it.
  tl.varDecls.forEach(function(vd) { frameSet(fr, vd, BOTTOM); });
  // bind the fun names in the frame.
  tl.funDecls.forEach(function(fd) {
      frameSet(fr, fd.fname, new Aval(NOBASEVALS, fd.addr));
    });
  
  // evaluate the stms of the toplevel in order
  w.push(tl.kreg);
  while (w.length !== 0) {
    n = w.pop();
    if (n === undefined) continue; // end of toplevel reached
    if (n.type === RETURN)
      ; // record error, return in toplevel
    else {
      ans = evalStm(n, fr);
      fr = ans.fr;
      w.push(ans.v);
      // FIXME: handle toplevel uncaught exception
    }
  }
  
  // each function w/out a summary is called with unknown arguments
  tl.funDecls.forEach(function(fd) {
      if (!existsSummary(fd)) {
        //FIXME: don't pass BOTTOM for THIS, create some generic object in heap
        ans = evalFun(fd, buildArray(fd.params.length + 1, BOTTOM), false);
      }
    });

  //showSummaries();
}

// consumes the ast returned by jsparse.parse
function cfa2(ast) {
  count = 0;
  core = {};
  initGlobals();

  //print("fixStm start");

  fixStm(ast);

  //print("fixStm succeeded");
  
  initCoreObjs();
  if (commonJSmode) { // create the exports object
    var e = new Aobj({}), eaddr = ++count;
    var eav = new Aval(NOBASEVALS, eaddr), eavaddr = ++count;
    heap[eaddr] = e;
    heap[eavaddr] = eav;
    core["exports"] = eavaddr;
    exportsObj.obj = e;
  }
  labelStm(ast);
  
  //print("labelStm done");

  tagVarRefsStm(ast, [], []);

  //print("tagrefsStm done");

  markConts(ast, undefined, undefined);

  //print("markconts done");

  try {
    //print("Done with preamble. Analysis starting.");
    print(count);
    evalToplevel(ast);
  }
  catch (e) {
    print("timestamp: " + timestamp); // 1155 for v8:crypto and v8:splay
    print(e.message);
    throw e;
  }
}

// node, string, Array of string, cmd-line options -> Array of ctags
function getTags(ast, pathtofile, lines, options) {
  const REGEX_ESCAPES = { "\n": "\\n", "\r": "\\r", "\t": "\\t" };
  var tags = [];

  function regexify(str) {
    function subst(ch) {
      return (ch in REGEX_ESCAPES) ? REGEX_ESCAPES[ch] : "\\" + ch;
    }
    return "/^" + str.replace(/[\\/$\n\r\t]/g, subst) + "$/";
  }

  //print("before everything");

  if (options.commonJS) {
    commonJSmode = true;
  }

  //print("before cfa2");

  cfa2(ast);

  //print("after cfa2");

  if (exportsObj.obj) {
    var eo = exportsObj.obj;
    eo.forEachOwnProp(function (p) {
        var av = eo.getOwnProp(p);
        var tag = {};
        tag.name = /-$/.test(p) ? p.slice(0, -1) : p.slice(1);
        tag.tagfile = pathtofile;
        tag.addr = regexify(lines[exportsObj.lines[p] - 1]);
        var type = av.toType();
        if (/(^<.*> function)|(^[^<>\|]*function)/.test(type))
          tag.kind = "f";
        else
          tag.kind = "v";
        tag.type = type;
        tag.module = options.module;
        tags.push(tag);
      });
  }
  for (var addr in summaries) {
    var f = addrsOfFuns[addr];
    tags.push({ name : f.fname.name || "%anonymous_function",
          tagfile : pathtofile,
          addr : regexify(lines[f.lineno - 1]),
          kind : "f",
          type : funToType(f)
          });
  }
  return tags;
}

// node -> boolean
// hacky test suite. Look in run-tests.js
function runtest(ast) {
  count = 0;
  core = {};
  initGlobals();
  fixStm(ast);
  initCoreObjs();
  labelStm(ast);
  tagVarRefsStm(ast, [], []);
  markConts(ast, undefined, undefined);
  // find test's addr at the toplevel
  var testaddr, fds = ast.funDecls;
  for (var i = 0, len = fds.length; i < len; i++) 
    if (fds[i].fname.name === "test") {
      testaddr = fds[i].addr;
      break;
    }
  if (testaddr === undefined) throw new Error("malformed test");
  print(count);
  evalToplevel(ast);
  var type = summaries[testaddr].type;
  return aveq(type[0][1], type[1]);
}

exports.cfa2 = cfa2;
exports.runtest = runtest;
exports.getTags = getTags;

////////////////////////////////////////////////////////////////////////////////
//////////////    DATA DEFINITIONS FOR THE AST RETURNED BY JSPARSE  ////////////
////////////////////////////////////////////////////////////////////////////////

function walkExp(n) {

  switch (n.type){

    //nullary
  case NULL:
  case THIS:
  case TRUE:
  case FALSE:
    break;

  case IDENTIFIER:
  case NUMBER:
  case STRING:
  case REGEXP:
    // n.value
    break;

    //unary
  case DELETE:
  case VOID:
  case TYPEOF:
  case NOT:
  case BITWISE_NOT:
  case UNARY_PLUS: case UNARY_MINUS:
  case NEW:
  case GROUP: //parenthesized expr
    walkExp(n[0]); 
    break;

  case INCREMENT: case DECREMENT:
    // n.postfix is true or undefined
    walkExp(n[0]);
    break;

    //binary
  case CALL:
  case NEW_WITH_ARGS:
    walkExp(n[0]); 
    //n[1].type === LIST
    n[1].forEach(walkExp);
    break;

  case IN:
    walkExp(n[0]); // an exp which must eval to string
    walkExp(n[1]); // an exp which must eval to obj
    break;

  case DOT:
    walkExp(n[0]);
    walkExp(n[1]); // must be IDENTIFIER
    break;

  case BITWISE_OR: case BITWISE_XOR: case BITWISE_AND:
  case EQ: case NE: case STRICT_EQ: case STRICT_NE:
  case LT: case LE: case GE: case GT:
  case INSTANCEOF:
  case LSH: case RSH: case URSH:
  case PLUS: case MINUS: case MUL: case DIV: case MOD:
  case AND: case OR:
  case ASSIGN: // n[0].assignOp shows which op-and-assign operator we have here
  case INDEX: // property indexing  
    walkExp(n[0]);
    walkExp(n[1]);
    break;

    //ternary
  case HOOK:
    walkExp(n[0]);
    walkExp(n[1]);
    walkExp(n[2]);
    break;

    //variable arity
  case COMMA:
  case ARRAY_INIT: // array literal
    n.forEach(walkExp);
    break;

  case OBJECT_INIT:
    n.forEach(function(prop) { // prop.type === PROPERTY_INIT
        walkExp(prop[0]); // identifier, number or string
        walkExp(prop[1]);
      });
    break;

    //other
  case FUNCTION:
    // n.name is a string
    // n.params is an array of strings
    // n.functionForm === EXPRESSED_FORM
    walkStm(n.body);
    break;
  }
}

function walkStm(n) {
  switch (n.type) {

  case SCRIPT: 
  case BLOCK:
    n.forEach(walkStm);
    break;

  case FUNCTION:
    // n.name is a string
    // n.params is an array of strings
    // n.functionForm === DECLARED_FORM or STATEMENT_FORM
    // STATEMENT_FORM is for funs declared in inner blocks, like IF branches
    // It doesn't extend the funDecls of the script, bad!
    walkStm(n.body);
    break;

  case SEMICOLON:
    n.expression && walkExp(n.expression); 
    break;

  case IF:
    walkExp(n.condition);
    walkStm(n.thenPart);
    n.elsePart && walkStm(n.elsePart);
    break;
        
  case SWITCH:
    walkExp(n.discriminant);
    // a switch w/out branches is legal, n.cases is []
    n.cases.forEach(function(branch) {
        branch.caseLabel && walkExp(branch.caseLabel);
        // if the branch has no stms, branch.statements is an empty block
        walkStm(branch.statements);
      });
    break;

  case FOR: 
    if (n.setup) {
      if (n.setup.type === VAR || n.setup.type === CONST)
        walkStm(n.setup);
      else walkExp(n.setup);
    }
    n.condition && walkExp(n.condition);
    n.update && walkExp(n.update);
    walkStm(n.body);
    break;

  case FOR_IN:
    // n.varDecl is defined when the var keyword is used by for/in to show 
    // that the var may not already be in scope.
    walkExp(n.iterator);
    walkExp(n.object);
    walkStm(n.body);
    break;

  case WHILE:
  case DO:
    walkExp(n.condition);
    walkStm(n.body);
    break;

  case BREAK:
  case CONTINUE:
    // do nothing: n.label is just a name, n.target points back to ancestor
    break;

  case TRY:
    walkStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) { // clause.varName is a string
        clause.guard && walkExp(clause.guard);
        walkStm(clause.block);
      });
    n.finallyBlock && walkStm(n.finallyBlock);
    break;

  case THROW: 
    walkExp(n.exception);
    break;

  case RETURN:
    n.value && walkExp(n.value);
    break;
        
  case WITH:
    walkExp(n.object);
    walkStm(n.body);
    break;

  case LABEL:
    // n.label is a string
    walkStm(n.statement);
    break;

  case VAR: 
  case CONST: // variable or constant declaration
    // vd.name is a string
    // vd.readOnly is true for constants, false for variables
    n.forEach(function(vd) { walkExp(vd.initializer); });
    break;
  }
  return n;
}
