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

/*
 * Semantics of: function foo (args) body:
 * It's not the same as: var foo = function foo (args) body
 * If it appears in a script then it's hoisted at the top, so it's in funDecls
 * If it appears in a block then it's visible after it's appearance, in the
 * whole rest of the script!!
 * {foo(); {function foo() {print("foo");}}; foo();}
 * The 1st call to foo throws, but if you remove it the 2nd call succeeds.
 */

/*
 * 
 */

/* (POSSIBLY) UNSOUND ASSUMPTIONS:
 * - Won't iterate loops to fixpt. With types as abs. values, this may be sound.
 * - Return undefined not tracked, eg (if sth return 12;) always returns number.
 */

////////////////////////////////////////////////////////////////////////////////
/////////////////////////////   UTILITIES  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

if (!Array.prototype.forEach) {
  Array.prototype.forEach = function(fun) {
    for (var i = 0, len = this.length; i < len; i++) 
      /* if (i in this) */ fun(this[i], i, this);
  };
 }

// search for an elm in the array that satisfies pred
Array.prototype.member = function(pred) {
  for (var i = 0, len = this.length; i < len; i++)
    /* if (i in this) */ if (pred(this[i])) return true;
  return false;
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
  var i=0, j=0, len1 = a1.length, len2 = a2.length, a = new Array(len1 + len2);
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
//var print = require('sys').puts; // only when run in node

eval(m_jsdefs.defineTokenConstants());

// count is used to generate a unique ID for each node in the AST.
var count = 0;

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

// node -> undefined
// does some cleanup on the input expression node in-place.
function fixExp(n) {
  var nt = n.type;

  switch (opArity[nt]) {
  case BINARY: case TERNARY: case MULTI:
    n.forEach(fixExp);
    return;

  case MULTI_CALL:
    fixExp(n[0]);
    n[1].forEach(fixExp);
    return;

  case NULLARY:
    if (nt === IDENTIFIER) n.name = n.value;
    return;

  case UNARY:
    if (nt === NEW) { // unify NEW and NEW_WITH_ARGS
      n.type = NEW_WITH_ARGS;
      n[1] = [];
    }
    fixExp(n[0]);
    return;

  case FUN:
    fixFun(n);
    return;

  case MULTI_OI:
    n.forEach(function(prop) { fixExp(prop[0]); fixExp(prop[1]); })
    return;
  }
}

function fixFun(n) {
  var t = n.tokenizer;
  // replace name w/ a property fname which is an IDENTIFIER node.
  n.fname = idNode(t, n.name);
  delete n.name;
  // turn the formals to nodes, I'll want to attach stuff to them later.
  n.params.forEach(function(p, i, ps) { ps[i] = idNode(t, p); });
  fixStm(n.body); 
}

// node -> node 
function fixStm(n) {
  var i, j, n2, n3;

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
        fixExp(initv);
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
    var n2t;
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
          fixExp(n2.discriminant);
          n[i] = semiNode(n2.discriminant);
        }
        else fixStm(n2);
        i++;
        break;

      case BREAK:
      case CONTINUE: //rm break & continue nodes
        n.splice(i, 1);
        break;

      case FUNCTION: //rm functions from Script bodies, they're in funDecls
        fixFun(n2);
        if (n2.functionForm === DECLARED_FORM) n.splice(i, 1);
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
        fixStm(n2);
        i++;
        break;
      }
    }
    break;

  case SEMICOLON:
    fixExp(n.expression); //n.expression can't be null
    break;

  case IF:
    fixExp(n.condition);
    fixStm(n.thenPart);
    n.elsePart && fixStm(n.elsePart);
    break;
        
  case SWITCH:
    fixExp(n.discriminant);
    n.cases.forEach( function(branch) {
        branch.caseLabel && fixExp(branch.caseLabel);
        fixStm(branch.statements);
      });
    break;

  case FOR:
    n2 = n.setup;
    if (n2)
      if (n2.type === VAR || n2.type === CONST)
        n.setup = initsToAssigns(n2);
      else
        fixExp(n2);
    n.condition && fixExp(n.condition);
    n.update && fixExp(n.update);
    fixStm(n.body);
    break;

  case FOR_IN:
    fixExp(n.iterator);
    fixExp(n.object);
    fixStm(n.body);
    break;
    
  case WHILE:
  case DO:
    fixExp(n.condition);
    fixStm(n.body);
    break;

  case TRY: // turn the varName of each catch-clause to a node called exvar
    fixStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) {
        clause.exvar = idNode(clause.tokenizer, clause.varName);
        clause.guard && fixExp(clause.guard);
        fixStm(clause.block);
      });
    n.finallyBlock && fixStm(n.finallyBlock);
    break;

  case THROW: 
    fixExp(n.exception);
    break;

  case RETURN:
    (n.value) ? fixExp(n.value) : (n.value = idNode(n.tokenizer, "undefined"));
    break;
        
  case WITH:
    throw new Error("fixStm: WITH not implemented");

  default:
    throw new Error("fixStm: unknown case");
  }
  return n;
}

// Invariants of the AST after fixStm:
// - no NEW nodes, they became NEW_WITH_ARGS
// - the formals of functions are nodes, not strings
// - functions have a property fname which is an IDENTIFIER node, name deleted
// - no VAR and CONST nodes, they've become semicolon comma nodes
// - no BREAK and CONTINUE nodes.
//   Unfortunately, this isn't independent of exceptions.
//   If a finally-block breaks or continues, the exception isn't propagated.
//   I will falsely propagate it (still sound, just more approximate).
// - no LABEL nodes
// - function nodes only in blocks, not in scripts
// - no empty SEMICOLON nodes
// - no switches w/out branches
// - each catch clause has a property exvar which is an IDENTIFIER node
// - all returns have .value (the ones that didn't got an undefined)

// FIXME: most of the addr`s will be redundant. Find the redundant ones and
// generate fewer addr`s here to compact the heap.

// node -> undefined
// adds an "addr" property to nodes which is a number unique for each node.
function labelExp(n) {
  var nt = n.type;

  n.addr = ++count;

  switch (opArity[nt]) {
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
    n.forEach(function(prop) { labelExp(prop[0]); labelExp(prop[1]); })
    return;
  }
}

function labelFun(n) {
  n.addr = ++count;
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
      tagVarRefsExp(n[0], innerscope, otherscopes);
      return;
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
      var boundvar;
      // search var in innermost scope
      for (var i = innerscope.length - 1; i >= 0; i--) {
        boundvar = innerscope[i];
        if (boundvar.name === n.name) {
          //console.log("stack ref: " + n.name);
          n.kind = STACK;
          return;
        }
      }
      // search var in other scopes
      for (var i = otherscopes.length - 1; i >= 0; i--) {
        boundvar = otherscopes[i];
        if (boundvar.name === n.name) {
          console.log("heap ref: " + n.name);
          n.kind = boundvar.kind = HEAP;
          n.addr = boundvar.addr;
          return;
        }
      }
      console.log("global: " + n.name);
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

    // normally, return & throw don't use their kreg. But this analysis allows 
    // more permissive control flow to be faster.
  case SEMICOLON:
  case THROW: 
  case RETURN:
    n.kreg = kreg;
    n.kexc = kexc;
    return;

  case IF:
    var thenp = n.thenPart, elsep = n.elsePart, condStm;
    condStm = semiNode(n.condition);
    n.kreg = condStm; // first run the test
    n.kexc = kexc;
    markConts(condStm, thenp, kexc); // ignore its result & run the true branch
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
    iterStm = semiNode(n.iterator);
    n.kreg = iterStm;
    objStm = semiNode(n.object);
    markConts(iterStm, objStm, kexc);
    markConts(objStm, body, kexc);
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
var timestamp;

// A summary contains a function node (fn), an array of abstract values (args),
// a timestamp (h) and an abstract value (res). It means: when we call fn w/ 
// args and the heap's timestamp is h, we get back res.

// summaries is a 2-level hash table. The keys in level 1 are the addr`s of
// function nodes. The keys in level 2 are timestamps.
// It contains pairs: args, abstract value.
var summaries;

// A member of seen is the same as a summary but w/out res.
// seen is a 2-level hash table. The keys in level 1 are the addr`s of
// function nodes. The keys in level 2 are timestamps.
var seen;

function initGlobals() {
  heap = new Array(count); // reserve heap space, don't grow it gradually
  timestamp = 0;
  summaries = {};
  seen = {};
}

// An abstract object o1 is represented as an array object o2. 
// The array elms of o2 are used for special properties of o1 & the properties
// of o2 are used for ordinary properties of o1. 
// 1st elm: the address of o1's prototype in the heap
// 2nd elm: may contain a function node.
// 3rd elm: may contain a set of constructors.
function Aobj(specialProps) {
  this.push(specialProps.proto); /* address of the prototype obj in the heap */
  this.push(specialProps.fun); /* optional function node */
  this.push(specialProps.constructors); /* optional abstract value */
}

Aobj.prototype = new Array();

// function node -> undefined
// Aobj.prototype.setFun = function(n) { this[1] = n; };

// nothing -> function node
Aobj.prototype.getFun = function() { return this[1]; };

// An abstract value is an obj w/ 2 properties: base is a number whose bits
// encode the base values, objs is an array of sorted heap addresses that 
// denotes a set of objects.
const ANUM = new Aval(1), ASTR = new Aval(2), ABOOL = new Aval(4);
const BOTTOM = new Aval(0), AUNDEF = new Aval(8);

function Aval(base) {
  if (base === undefined) this.base = 0; else this.base = base;
  this.objs = [];
}

// insert the heap address of an object in a sorted set of heap addresses
// Aval.prototype.addObj = function(addr) {
//   var os = this.objs;
//   for (var i=0, len=os.length; i<len; i++) {
//     if (addr <= os[i]) {
//       os.splice(i, 0, addr);
//       return;
//     }
//   }
//   os.push(addr);
// };

Aval.prototype.initObj = function(addr) {
  this.objs.push(addr); // this.objs is empty initially
};

// fun takes an abstract object
Aval.prototype.forEachObj = function(fun) {
  var objaddrs = this.objs;
  objaddrs.forEach(function(addr) { fun(heap[addr]); });
};

// pretty printer for abstract values
function avshow(v) {
  var base = v.base;
  return "{" + ((base & 4) ? "bool " : "") +
    ((base & 2) ? " string " : "") +
    ((base & 1) ? "number" : "") + "}";
}

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

// abstract value, abstract value -> boolean
// compares abstract values for equality
function aveq(v1, v2) {
  if (v1.base !== v2.base) return false;
  var os1 = v1.objs, os2 = v2.objs, len = os1.length, i; 
  if (len !== os2.length) return false;
  for (i=0; i<len; i++) if (os1[i] !== os2[i]) return false;
  return true;
}

// abstract object, string, abstract value -> timestamp
function updateHeapObj(o, prop, newv) {
  var oldv = o[prop];
  if (oldv === undefined) {
    o[prop] = newv;
    return ++timestamp;
  }
  newv = avjoin(newv, oldv);
  if ((oldv.base !== newv.base) || (oldv.objs.length !== newv.objs.length)) 
    return ++timestamp;
  else
    return timestamp;
}

// heap address, abstract value -> timestamp
function updateHeapAv(addr, newv) {
  var oldv = heap[addr];
  if (oldv === undefined) {
    heap[addr] = newv;
    return ++timestamp;
  }
  newv = avjoin(newv, oldv);
  heap[addr] = newv;
  if ((oldv.base !== newv.base) || (oldv.objs.length !== newv.objs.length))
    return ++timestamp;
  else
    return timestamp;
}

function aplus(v1, v2) {
  if (v1 === BOTTOM || v2 === BOTTOM) return new Aval(3);
  // v1 and v2 must not contain string or undefined
  if (((v1.base | v2.base) & 10) === 0) return ANUM;
  else return new Aval(3);
}

function aminus(v1, v2) {
  // FIXME: could signal type errors or get constraints about the arg types?
  return ANUM;
}


////////////////////////////////////////////////////////////////////////////////
/////////////////////////    EVALUATION FUNCTIONS   ////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// Invariant: the functions that follow should know nothing about the
// representation of abstract values.

// fun. node, timestamp, optional array of abs. values  -> abs. value or bool
function searchSummary(n, h, args) {
  var bucket, pair;
  if (!summaries[n.addr]) return false;
  bucket = summaries[n.addr][h];
  if (!args) return !!bucket; // check only if a summary exists, don't retrieve.
  if (!bucket) return false; // no summaries exist for this timestamp.
  for (var i = 0, len = bucket.length; i < len; i++) {
    pair = bucket[i];
    if (arrayeq(aveq, args, pair[0])) return pair[1];
  }
  return false;
}

function addSummary(n, args, h, retval) {
  var addr = n.addr;
  // for level1 we use {} instead of [] because it's sparse.
  summaries[addr] || (summaries[addr] = {}); 
  var level1 = summaries[addr];
  level1[h] || (level1[h] = []);
  level1[h].push([args, retval]);
  console.log("summary: " + n.fname.name + " " + h + " " + avshow(retval));
}

// function node, array of abstract values, timestamp -> boolean
function searchSeen(n, args, h) {
  if (!seen[n.addr]) return false;
  var bucket = seen[n.addr][h];
  if (!bucket) return false;
  return bucket.member(function(elm){ return arrayeq(aveq, args, elm); });
}

function addSeen(n, args, h) {
  var addr = n.addr;
  seen[addr] || (seen[addr] = {});
  var level1 = seen[addr];
  level1[h] || (level1[h] = []);
  level1[h].push(args);
}

// constructor for answer-objects (basically triples)
function Ans(v, fr, h) {
  this.v = v; // evalExp puts abstract values here, evalStm puts statements
  this.fr = fr; // frame
  this.h = h; // timestamp
}

// node, answer -> answer
// use n to get an lvalue, do the assignment and return the rvalue
function evalLval(n, ans) {
  val rval = ans.v, fr = ans.fr, h = ans.h, nt = n.type;
  switch (nt) {
  case IDENTIFIER:
    switch (n.kind) {
    case STACK: fr[n.name] = avjoin(fr[n.name], ans.v);
    case HEAP: h = updateHeapAv(n.addr, ans.v);
    default: throw new Error("FIXME: globals");
    }
    break;

  case DOT:
    var ans2 = evalExp(n[0], fr, h), prop = n[1].name;
    h = ans2.h;
    // FIXME: record error if ans2.v contains base values
    ans2.v.forEachObj(function(o) { h = updateHeapObj(o, prop, ans.v); });
  }
  return new Ans(rval, ans2.fr, h); 
}

// FIXME: will be rewritten for fast dispatch. Could tag AST w/ refs to funs
// in a pass b4 abs int.
// node, frame, timestamp -> answer
function evalExp(n, fr, h) {
  var ans, ans1, ans2, nt = n.type, av;
  switch (nt) {
  case IDENTIFIER:
    switch (n.kind) {
    case STACK: return new Ans(fr[n.name], fr, h);
    case HEAP: return new Ans(heap[n.addr], fr, h);
    default: throw new Error("FIXME: globals");
    }

  case NUMBER: return new Ans(ANUM, fr, h);
        
  case STRING: return new Ans(ASTR, fr, h);

  case PLUS:
    ans1 = evalExp(n[0], fr, h);
    ans2 = evalExp(n[1], ans1.fr, ans1.h);
    ans2.v = aplus(ans1.v, ans2.v);
    return ans2;

  case MINUS:
    ans1 = evalExp(n[0], fr, h);
    ans2 = evalExp(n[1], ans1.fr, ans1.h);
    ans2.v = aminus(ans1.v, ans2.v);
    return ans2;

  case ASSIGN: 
    return evalLval(n[0], evalExp(n[1], fr, h));

  case DOT:
    var ans = evalExp(n[0], fr, h), prop = n[1].name, av = BOTTOM;
    h = ans.h;
    // FIXME: record error if ans.v contains base values
    ans.v.forEachObj(function(o) {
        av = avjoin(av, (prop in o) ? o[prop] : AUNDEF);
      });
    ans2 = new Ans(av, ans.fr, h);
    ans2.thisav = ans.v; // used by method calls
    return ans2;
    
  case CALL:
  case NEW_WITH_ARGS:
    var rands = [undefined /* reserved for THIS */], retval = BOTTOM, rator;
    ans = evalExp(n[0], fr, h);
    rator = ans.v;
    fr = ans.fr;
    h = ans.h;
    // evaluate arguments
    n[1].forEach(function(rand) {
        ans = evalExp(rand, fr, h);
        rands.push(ans.v);
        fr = ans.fr;
        h = ans.h;
      });
    if (nt === CALL) {
      // FIXME: bind rands[0] to the global onject if (!ans.thisav)
      rand[0] = (ans.thisav ? ans.thisav : BOTTOM);
      // FIXME: record error if rator contains base vals and non-functions
      // call each function that can flow to the operator position
      rator.forEachObj(function(o) {
          var clos = o.getFun();
          if (!clos) return; 
          ans = evalFun(clos, rands, h);
          retval = avjoin(retval, aveq(ans.v, BOTTOM) ? AUNDEF : ans.v);
          h = ans.h;
        });
    }
    else {
      var objaddr = n.addr;
      //unsound: if the obj is already created, I should update its constructors
      //every time in the loop below. I assume the constructors won't change.
      if (!heap[objaddr]) heap[objaddr] = new Aobj({constructors : rator});
      av = new Aval();
      av.initObj(objaddr);
      rands[0] = av;
      // FIXME: record error if rator contains base vals and non-functions
      rator.forEachObj(function(o) {
          var clos = o.getFun();
          if (!clos) return; 
          ans = evalFun(clos, rands, h);
          if (aveq(ans.v, BOTTOM)) {
            // called a constructor that doesn't use return
            retval = avjoin(retval, av);
          }
          else // called a constructor that uses return or some other function
            retval = avjoin(retval, ans.v);
          h = ans.h;
        });
    }
    return new Ans(retval, fr, h);

  default: return new Ans(BOTTOM, fr, h);
  }
}

//FIXME: are there more cases to handle than the typical b/c of markConts?
// statement, frame, timestamp -> Ans
function evalStm(n, fr, h) {
  var nt = n.type, ans;
  switch (nt) {
  case BLOCK: case IF: //case SWITCH:
  case FOR: case DO: case WHILE:
    return new Ans(n.kreg, fr, h);

  case SWITCH:
    return new Ans(n.kreg, fr, h);

  case SEMICOLON: // handle exception here
    ans = evalExp(n.expression, fr, h);
    return new Ans(n.kreg, ans.fr, ans.h);

    // case FUNCTION: // fix for fun decls in blocks

    // case FOR_IN: 

    // case TRY:

    // case THROW:

    //case WITH: 
    
    //case SCRIPT: case RETURN: are handled by processFun, not here
  default:
    throw new Error("evalStm: unknown case");
  }
}

// fun. node, array of abs. vals, timestamp -> Ans w/out fr 
// The first arg is always the obj that THIS will be bound too.
function evalFun(fn, args, h) { 
  var ans, i, n, len, params, fr, w /* workset */, retval;
  retval = searchSummary(fn, h, args);
  if (retval) return new Ans(retval, undefined, h);
  // When a call eventually leads to itself, stop processing.
  // Some other branch may make the recursion bottom out.
  if (searchSeen(fn, args, h))
    throw new Error("recursion");
  else
    addSeen(fn, args, h);
  w = [];
  fr = {};
  retval = BOTTOM;
  params = fn.params;
  // create frame, bind formals to actuals
  // FIXME: don't add local vardecls to fr, but detect if a local var is refd
  // before it's initialized and report an error.
  fr.this = args[0]; 
  for (i=0, len=params.length; i<len; i++) {
    //FIXME: are there vars whose name I can't use as a property directly?
    fr[params[i].name] = args[i+1];
    //FIXME: case when params and args have different length
    //FIXME: enter funDecls in scope
    //FIXME: update heap for formals that are heap vars
  }
  w.push(fn.body.kreg);
  while (w.length !== 0) {
    n = w.pop();
    try {
      switch (n.type) {
      case RETURN: 
        ans = evalExp(n.value, fr, h);
        // fr is passed to exprs/stms & mutated, no need to join(fr, ans.fr)
        fr = ans.fr;
        h = ans.h;
        retval = avjoin(retval, ans.v);
        w.push(n.kreg);
        break;

      default: //FIXME: if n is undefined.
        ans = evalStm(n, fr, h);
        fr = ans.fr;
        h = ans.h;
        w.push(ans.v);
        break;
      }
    }
    catch (e) {
      //FIXME: handle exception thrown by recursive funs
    }
  }
  addSummary(fn, args, h, retval);
  // A function that doesn't have a RETURN always returns bottom. If it wasn't
  // called with NEW, the caller will turn that to undefined.
  return new Ans(retval, undefined, h);
}

function evalToplevel(tl) {
  var w /* workset */, fr, h, n, ans, fdecls;
  initGlobals();
  w = [];
  fr = {};
  h = timestamp;
  fdecls = tl.funDecls;
  
  // FIXME: add var decls to the frame, bound to abstract undefined
  // or don't add them & if ref`d before init`d signal error.
  // tl.varDecls.forEach(function(vd){});

  // create objs for the funDecls & store them in the heap.
  // bind the fun names in the frame to those objs.
  fdecls.forEach(function(fd) {
      var objaddr = fd.addr, fn = fd.fname, av;
      // heap[objaddr] will point to this object throughout the analysis.
      heap[objaddr] = new Aobj({fun:fd});
      av = new Aval();
      av.initObj(objaddr);
      if (fn.kind === HEAP) h = updateHeapAv(fn.addr, av);
      fr[fn.name] = av;
    });
  
  // evaluate the stms of the toplevel in order
  w.push(tl.kreg);
  while (w.length !== 0) {
    n = w.pop();
    if (n === undefined) break; // end of toplevel reached
    ans = evalStm(n, fr, h);
    fr = ans.fr;
    h = ans.h;
    w.push(ans.v);
  }
  
  //call with unknown arguments each function w/out a summary 
  fdecls.forEach(function(fd) {
      if (!searchSummary(fd, h)) {
        ans = evalFun(fd, buildArray(fd.params.length, BOTTOM), h);
        h = ans.h;
      }
    });
}


exports.fixAst = fixStm;
exports.labelAst = labelStm;
exports.tagVarRefsAst = function(ast){return tagVarRefsStm(ast,[],[]);};
exports.changeAst = function(ast){
  fixStm(ast);
  labelStm(ast);
  tagVarRefsStm(ast, [], []);
  markConts(ast, undefined, undefined);
}
//exports.evalFun = evalFun;
exports.evalToplevel = evalToplevel;

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
  case DOT:
  case AND: case OR:
  case ASSIGN:      
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

