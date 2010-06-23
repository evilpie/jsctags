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
 * The CFA won't iterate loops to a fixpt. With types as abstract values, this
 * may not be unsound.
 */

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

// node -> undefined
// does some cleanup on the input expression node in-place.
function fixExp(n) {
  var nt = n.type;

  switch (opArity[nt]) {
  case BINARY: case TERNARY: case MULTI:
    for (var i=0, len = n.length; i < len; i++) fixExp(n[i]);
    return;

  case MULTI_CALL:
    fixExp(n[0]);
    for (var i=0, n1 = n[1], len = n1.length; i < len; i++)
      fixExp(n1[i]);
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
    var prop;
    for (var i=0, len=n.length; i < len; i++) {
      prop = n[i];
      fixExp(prop[0]);
      fixExp(prop[1]);
    }
    return;
  }
}

function fixFun(n) {
  // turn the formals to nodes, I'll want to attach stuff to them later.
  var id, params = n.params, t = n.tokenizer;
  for (var i=0, len=params.length; i < len; i++) {
    id = new Node(t, IDENTIFIER);
    id.name = id.value = params[i];
    params[i] = id;
  }
  fixStm(n.body); 
}

// node -> node 
// does some cleanup on the input statement node in-place.
function fixStm(n) {
  var i, j, n2, n3;

  // VAR or CONST node -> comma node
  // Convert to assignments, with readOnly field for constants.
  // The returned node may contain 0 subexpressions.
  function initsToAssigns(n) {
    var n2, vdecl, a, initv, id, t, i, len;

    n2 = new Node(n.tokenizer, COMMA);
    for (i=0, len=n.length; i < len; i++) {
      vdecl = n[i];
      initv = vdecl.initializer;
      if (initv) {
        fixExp(initv);
        t = vdecl.tokenizer;
        id = new Node(t, IDENTIFIER);
        id.value = id.name = vdecl.name;
        a = new Node(t, ASSIGN);
        a.push(id);
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
    var branch, cases;
    fixExp(n.discriminant);
    cases = n.cases;
    for (var i = 0, len = cases.length; i < len; i++) {
      branch = cases[i];
      branch.caseLabel && fixExp(branch.caseLabel);
      fixStm(branch.statements);
    }
    break;

  case FOR:
    n2 = n.setup;
    if (n2 && (n2.type === VAR || n2.type === CONST))
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
    var ev, clause, clauses = n.catchClauses;
    for (var i=0, len=clauses.length; i < len; i++) {
      clause = clauses[i];
      ev = new Node(clause.tokenizer, IDENTIFIER);
      ev.name = ev.value = clause.varName;
      clause.exvar = ev;
      clause.guard && fixExp(clause.guard);
      fixStm(clause.block);
    }
    n.finallyBlock && fixStm(n.finallyBlock);
    break;

  case THROW: 
    fixExp(n.exception);
    break;

  case RETURN:
    n.value && fixExp(n.value);
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


// FIXME: most of the addr`s will be redundant. Find the redundant ones and
// generate fewer addr`s here to compact the heap.

// node -> undefined
// adds an "addr" property to nodes which is a number unique for each node.
function labelExp(n) {
  var nt = n.type;

  n.addr = ++count;

  switch (opArity[nt]) {
  case UNARY: case BINARY: case TERNARY: case MULTI:
    for (var i=0, len = n.length; i < len; i++) labelExp(n[i]);
    return;

  case MULTI_CALL:
    labelExp(n[0]);
    for (var i=0, n1 = n[1], len = n1.length; i < len; i++)
      labelExp(n1[i]);
    return;

  case NULLARY:
    return;

  case FUN:
    labelFun(n);
    return;

  case MULTI_OI:
    var prop;
    for (var i=0, len=n.length; i<len; i++) {
      prop = n[i];
      labelExp(prop[0]);
      labelExp(prop[1]);
    }
    return;
  }
}

function labelFun(n) {
  var params = n.params;
  n.addr = ++count;
  for (var i=0, len = params.length; i < len; i++) params[i].addr = ++count;
  labelStm(n.body);
}

// node -> node
// adds an "addr" property to nodes, which is a number unique for each node.
function labelStm(n) {
  n.addr = ++count;

  switch (n.type) {
  case SCRIPT:
    var fdecls = n.funDecls, vdecls = n.varDecls;
    for (var i=0, len=vdecls.length; i < len; i++) vdecls[i].addr = ++count;
    for (var i=0, len=fdecls.length; i < len; i++) labelFun(fdecls[i]);
    // fall thru to fix the script body
  case BLOCK:
    for (var i=0, len = n.length; i < len; i++) labelStm(n[i]);
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
    var branch, cases = n.cases;
    labelExp(n.discriminant);
    for (var i = 0, len = cases.length; i < len; i++) {
      branch = cases[i];
      branch.caseLabel && labelExp(branch.caseLabel);
      labelStm(branch.statements);
    }
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
    var clause, clauses = n.catchClauses;
    for (var i = 0, len = clauses.length; i < len; i++) {
      clause = clauses[i];
      labelExp(clause.exvar);
      clause.guard && labelExp(clause.guard);
      labelStm(clause.block);
    }
    n.finallyBlock && labelStm(n.finallyBlock);
    break;

  case THROW: 
    labelExp(n.exception);
    break;

  case RETURN:
    n.value && labelExp(n.value);
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
    for (var i=0, len = n.length; i < len; i++)
      tagVarRefsExp(n[i], innerscope, otherscopes);
    return;

  case MULTI_CALL:
    tagVarRefsExp(n[0], innerscope, otherscopes);
    for (var i=0, n1 = n[1], len = n1.length; i < len; i++)
      tagVarRefsExp(n1[i], innerscope, otherscopes);
    return;

  case NULLARY:
    if (nt === IDENTIFIER) {
      var boundvar;
      // search var in innermost scope
      for (var i = innerscope.length - 1; i >= 0; i--) {
        boundvar = innerscope[i];
        if (boundvar.name === n.name) {
          console.log("stack ref: " + n.name);
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
    for (var i=0, len=n.length; i<len; i++) 
      // don't classify property names
      tagVarRefsExp(n[i][1], innerscope, otherscopes);
    return;        
  }
}

function tagVarRefsFun(n, innerscope, otherscopes) {
  var i, f, len, param, params = n.params;
  len = otherscopes.length;
  // extend otherscopes
  Array.prototype.push.apply(otherscopes, innerscope); 
  // fun name is visible in the body & not a heap ref, add it to scope
  params.push(n);
  tagVarRefsStm(n.body, params, otherscopes);
  params.pop();
  if (n.kind !== HEAP) n.kind = STACK;    
  tagVarBinders(params);
  // trim otherscopes
  otherscopes.splice(len, innerscope.length); 
}

// array of id nodes -> undefined
function tagVarBinders(vs) {
  var i, len, vdecl;
  for (i=0, len=vs.length; i<len; i++) {
    vdecl = vs[i];
    if (vdecl.kind !== HEAP) vdecl.kind = STACK;
  }
}

function tagVarRefsStm(n, innerscope, otherscopes) {
  switch (n.type) {

  case SCRIPT:
    var i, j, len, vdecl, vdecls = n.varDecls, fdecl, fdecls = n.funDecls;
    // extend inner scope
    j = innerscope.length;
    Array.prototype.push.apply(innerscope, vdecls);
    Array.prototype.push.apply(innerscope, fdecls);
    // tag refs in fun decls
    for (i=0, len=fdecls.length; i<len; i++)
      tagVarRefsFun(fdecls[i], innerscope, otherscopes);
    // tag the var refs in the body
    for (i=0, len=n.length; i<len; i++)
      tagVarRefsStm(n[i], innerscope, otherscopes);
    tagVarBinders(vdecls);
    tagVarBinders(fdecls);
    innerscope.splice(j, vdecls.length + fdecls.length); //trim inner scope 
    break;

  case BLOCK:
    for (var i=0, len = n.length; i < len; i++)
      tagVarRefsStm(n[i], innerscope, otherscopes);
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
    var branch, cases = n.cases;
    tagVarRefsExp(n.discriminant, innerscope, otherscopes);
    for (var i = 0, len = cases.length; i < len; i++) {
      branch = cases[i];
      branch.caseLabel && 
        tagVarRefsExp(branch.caseLabel, innerscope, otherscopes);
      tagVarRefsStm(branch.statements, innerscope, otherscopes);
    }
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
    var xv, clause, clauses = n.catchClauses;
    for (var i = 0, len = clauses.length; i < len; i++) {
      clause = clauses[i];
      xv = clause.exvar;
      innerscope.push(xv);
      clause.guard && tagVarRefsExp(clause.guard, innerscope, otherscopes);
      tagVarRefsStm(clause.block, innerscope, otherscopes);
      innerscope.pop();
      if (xv.kind !== HEAP) xv.kind = STACK;
    }
    n.finallyBlock &&
      tagVarRefsStm(n.finallyBlock, innerscope, otherscopes);
    break;

  case THROW: 
    tagVarRefsExp(n.exception, innerscope, otherscopes);
    break;

  case RETURN:
    n.value && tagVarRefsExp(n.value, innerscope, otherscopes);
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
    else
      n.kreg = stms;
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
    var fdecls = n.funDecls;
    for (i=0, len=fdecls.length; i<len; i++)
      markConts(fdecls[i].body, undefined, undefined);
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
    len = cases.length;
    markConts(discStm, cases[0], kexc);
    len--;
    for (i=0; i < len; i++) markContsCase(cases[i], cases[i+1], kexc);
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
  case DO:
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = condStm;
    n.kexc = kexc;
    markConts(condStm, body, kexc);
    markConts(body, kreg, kexc);
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

  case THROW: // will never use its kreg
  case RETURN: // will never use its kreg
    n.kexc = kexc;
    return;
        
  case WITH:
    throw new Error("markConts: WITH not implemented");

  default:
    throw new Error("markConts: unknown case");
  }
}

// function Stack() {
//   this.s = [];
// }

// Stack.prototype.push = function (elm) {
//   this.s = [elm, this.s];
//   return this; // for functional style
// };

// Stack.prototype.pop = function () {
//   var s = this.s;
//   if (s.length === 0)
//     throw new Error("Tried to pop from empty stack");
//   else {
//     var top = s[0];
//     this.s = s[1];
//     return top;
//   }
// };

// Stack.prototype.top = function () {
//   var s = this.s;
//   if (s.length === 0)
//     throw new Error("Tried to peek in an empty stack");
//   else
//     return s[0];
// };

////////////////////////////////////////////////////////////////////////////////
////////////////////////////   CFA2  code  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

const UNKNOWN = 0, ANUM = [1, []], ASTR = [2, []], ABOOL = [4, []];
var heap = new Array(count); // reserve heap space, don't grow it gradually

function aplus(v1, v2) {
  if (v1 === UNKNOWN || v2 === UNKNOWN) return [3, []];
  if (((v1[0] | v2[0]) & 2) === 0) return [1, []];
  else return [3, []];
}

function aminus(v1, v2) {
  // FIXME: could signal type errors or get constraints about the arg types?
  return [1, []];
}

// constructor for answer-objects (basically triples)
function Ans(v, fr, h) {
  this.v = v; // evalExp puts abstract values here, evalStm puts statements
  this.fr = fr; // frame
  this.h = h; // heap
}

// FIXME: will be rewritten for fast dispatch. Could tag AST w/ refs to funs
// in a pass b4 abs int.
// node, frame, heap -> answer
function evalExp(n, fr, h) {
  var ans1, ans2, nt = n.type;
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
    ans1 = evalExp(n[0]);
    ans2 = evalExp(n[1], ans1.fr, ans1.h);
    ans2.v = aplus(ans1.v, ans2.v);
    return ans2;

  case MINUS:
    ans1 = evalExp(n[0]);
    ans2 = evalExp(n[1], ans1.fr, ans1.h);
    ans2.v = aminus(ans1.v, ans2.v);
    return ans2;

  default: return new Ans(UNKNOWN, fr, h);
  }
}

// statement, frame, heap -> Ans
function evalStm(s, fr, h) {
  var nt = n.type;
  switch (nt) {
  case BLOCK:
    return new Ans(n.kreg, fr, h);
  default:
    throw new Error("evalStm: unknown case");
  }
}


exports.fixAst = fixStm;
exports.labelAst = labelStm;
exports.tagVarRefsAst = function(ast){return tagVarRefsStm(ast,[],[]);};

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
    for (var i=0, len = n[1].length; i < len; i++)
      walkExp(n[1][i]);
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
    for (var i=0, len = n.length; i < len; i++)
      walkExp(n[i]);
    break;

  case OBJECT_INIT:
    for (var i=0, len = n.length; i < len; i++) {
      // n[i].type === PROPERTY_INIT
      walkExp(n[i][0]); // identifier, number or string
      walkExp(n[i][1]);
    }
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
    for (var i=0, len = n.length; i < len; i++)
      walkStm(n[i]);
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
    var branch /*switch branch*/;
    walkExp(n.discriminant);
    // a switch w/ branches is legal, n.cases is []
    for (var i = 0, len = n.cases.length; i < len; i++) {
      branch = n.cases[i];
      branch.caseLabel && walkExp(branch.caseLabel);
      // if there are no stms in the branch, branch.statements is an empty block
      walkStm(branch.statements);
    }
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
    var clause, clauses = n.catchClauses;
    for (var i = 0, len = clauses.length; i < len; i++) {
      // clause.varName is a string
      clause = clauses[i];
      clause.guard && walkExp(clause.guard);
      walkStm(clause.block);
    }
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
    for (var i = 0, len = n.length; i < len; i++) {
      // n[i].name is a string
      // n[i].readOnly is true for constants, false for variables
      walkExp(n[i].initializer);
    }
    break;
  }
  return n;
}

