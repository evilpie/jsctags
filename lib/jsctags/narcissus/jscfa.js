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

var m_jsdefs = require('./jsdefs');
var Node = require('./jsparse').Node;
//var print = require('sys').puts;

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


// node -> undefined
// does some cleanup on the input expression node in-place.
function fixExp(n) {
    var nt = n.type;

    switch (opArity[nt]) {
    case BINARY: case TERNARY: case MULTI:
        for (var i=0, len = n.length; i < len; i++) fixExp(n[i]);
        break;

    case MULTI_CALL:
        fixExp(n[0]);
        for (var i=0, n1 = n[1], len = n1.length; i < len; i++)
            fixExp(n1[i]);
        break;

    case NULLARY:
        if (nt === IDENTIFIER) n.name = n.value;
        break;

    case UNARY:
        if (nt === NEW) { // unify NEW and NEW_WITH_ARGS
            n.type = NEW_WITH_ARGS;
            n[1] = [];
        }
        fixExp(n[0]);
        break;

    case FUN:
        fixFun(n);
        break;

    case MULTI_OI:
        var prop;
        for (var i=0, len=n.length; i < len; i++) {
            prop = n[i];
            fixExp(prop[0]);
            fixExp(prop[1]);
        }
        break;
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
    fixStm(n.body); //FIXME: handle expression closures
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
    case SCRIPT: case BLOCK:
        i=0;
        while (i < n.length) {
            n2 = n[i];
            // remove empty SEMICOLON nodes (expression statements).
            if (n2.type === SEMICOLON && n2.expression == null) 
                // many splices in a row could be expensive, because removing
                // an elm is linear time, not constant.
                // But how do I create a new array and copy the elms I need,
                // and also maintain the remaining properties of n?
                n.splice(i,1);
            else if (n2.type === VAR || n2.type === CONST) {
                n3 = initsToAssigns(n2);
                if (n3.length > 0) {
                    var semin = new Node(n3.tokenizer, SEMICOLON);
                    semin.expression = n3;
                    semin.end = n3.end;
                    n.splice(i++, 1, semin);
                }
                else n.splice(i, 1);
            }
            else {
                fixStm(n2);
                i++;
            }
        }
        break;

    case FUNCTION:
        fixFun(n);
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

    case FOR: //FIXME: handle lets
        if (n.iterator) {// FOR_IN
            fixExp(n.iterator);
            fixExp(n.object);
        }
        else {// classic FOR
            n2 = n.setup;
            if (n2 && (n2.type === VAR || n2.type === CONST))
                n.setup = initsToAssigns(n2);
            else
                fixExp(n2);
            n.condition && fixExp(n.condition);
            n.update && fixExp(n.update);
        }
        fixStm(n.body);
        break;

    case WHILE:
    case DO:
        fixExp(n.condition);
        fixStm(n.body);
        break;

    case BREAK:
    case CONTINUE:
        // do nothing: n.label is just a name, n.target points back to ancestor
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
        fixExp(n.object);
        fixStm(n.body);
        break;

    // case LET: //FIXME: handle LETs
    //     if (n.value === "Let stm") fixStm(n.body); else fixExp(n.body);
    //     break;

    case VAR: 
    case CONST:
        throw new Error("VAR & CONST decls must be handled by their context");
    }
    return n;
}


// no more NEW, empty SEMICOLON, VAR and CONST nodes in the AST.


// node -> undefined
// adds an "addr" property to nodes which is a number unique for each node.
function labelExp(n) {
    var nt = n.type;

    n.addr = ++count;

    switch (opArity[nt]) {
    case UNARY: case BINARY: case TERNARY: case MULTI:
        for (var i=0, len = n.length; i < len; i++) {
            labelExp(n[i]);
        }
        break;

    case MULTI_CALL:
        labelExp(n[0]);
        for (var i=0, n1 = n[1], len = n1.length; i < len; i++)
            labelExp(n1[i]);
        break;

    case NULLARY:
        break;

    case FUN:
        labelFun(n);
        break;

    case MULTI_OI:
        var prop;
        for (var i=0, len=n.length; i<len; i++) {
            prop = n[i];
            labelExp(prop[0]);
            labelExp(prop[1]);
        }
        break;
    }
}

function labelFun(n) {
    var params = n.params;
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
        for (var i=0, len=fdecls.length; i < len; i++) fdecls[i].addr = ++count;
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
        if (n.iterator) {// FOR_IN
            labelExp(n.iterator);
            labelExp(n.object);
        }
        else {// classic FOR
            n.setup && labelExp(n.setup);
            n.condition && labelExp(n.condition);
            n.update && labelExp(n.update);
        }
        labelStm(n.body);
        break;

    case WHILE: case DO:
        labelExp(n.condition);
        labelStm(n.body);
        break;

    case BREAK: case CONTINUE:
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
        labelExp(n.object);
        labelStm(n.body);
        break;
    }
    return n;
}


const STACK = 0, HEAP = 1, GLOBAL = 2;

// node, array of id nodes, array of id nodes -> undefined
// classify variable references as either stack or heap variables.
// FIXME: add global variables to the global obj later.
function tagVarRefsExp(n, innerscope, otherscopes) {
    var nt = n.type;

    here:
    switch (opArity[nt]) {

    case BINARY:
        if (nt === DOT) {// don't classify property names
            tagVarRefsExp(n[0], innerscope, otherscopes);
            break;
        }
        // fall thru
    case UNARY: case TERNARY: case MULTI:
        for (var i=0, len = n.length; i < len; i++)
            tagVarRefsExp(n[i], innerscope, otherscopes);
        break;

    case MULTI_CALL:
        tagVarRefsExp(n[0], innerscope, otherscopes);
        for (var i=0, n1 = n[1], len = n1.length; i < len; i++)
            tagVarRefsExp(n1[i], innerscope, otherscopes);
        break;

    case NULLARY:
        if (nt === IDENTIFIER) {
            var boundvar;
            // search var in innermost scope
            for (var i = innerscope.length - 1; i >= 0; i--) {
                boundvar = innerscope[i];
                if (boundvar.name === n.name) {
                    //console.log("stack ref: " + n.name + " ::: " + n.value);
                    n.kind = STACK;
                    break here;
                }
            }
            // search var in other scopes
            for (var i = otherscopes.length - 1; i >= 0; i--) {
                boundvar = otherscopes[i];
                if (boundvar.name === n.name) {
                    //console.log("heap ref: " + n.name + " ::: " + n.value);
                    n.kind = boundvar.kind = HEAP;
                    n.addr = boundvar.addr;
                    break here;
                }
            }
            //console.log("global: " + n.name + " ::: " + n.value);
            n.kind = GLOBAL;
        }
        break;

    case FUN:
        tagVarRefsFun(n, innerscope, otherscopes);
        break;

    case MULTI_OI: 
        for (var i=0, len=n.length; i<len; i++) 
            // don't classify property names
            tagVarRefsExp(n[i][1], innerscope, otherscopes);
        break;        
    }
}

//fixme fun name in innerscope
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
        var branch, cases = n.cases, stms;
        tagVarRefsExp(n.discriminant, innerscope, otherscopes);
        for (var i = 0, len = cases.length; i < len; i++) {
            branch = cases[i];
            branch.caseLabel &&
                tagVarRefsExp(branch.caseLabel, innerscope, otherscopes);
            tagVarRefsStm(branch.statements, innerscope, otherscopes);
        }
        break;

    case FOR: 
        if (n.iterator) {// FOR_IN
            tagVarRefsExp(n.iterator, innerscope, otherscopes);
            tagVarRefsExp(n.object, innerscope, otherscopes);
        }
        else {// classic FOR
            if (n.setup) {
                if (n.setup.type === VAR || n.setup.type === CONST)
                    walkStm(n.setup);
                else walkExp(n.setup);
            }
            n.setup && tagVarRefsExp(n.setup, innerscope, otherscopes);
            n.condition && tagVarRefsExp(n.condition, innerscope, otherscopes);
            n.update && tagVarRefsExp(n.update, innerscope, otherscopes);
        }
        tagVarRefsStm(n.body, innerscope, otherscopes);
        break;

    case WHILE:
    case DO:
        tagVarRefsExp(n.condition, innerscope, otherscopes);
        tagVarRefsStm(n.body, innerscope, otherscopes);
        break;

    case BREAK:
    case CONTINUE:
        break;

    case TRY:
        tagVarRefsStm(n.tryBlock, innerscope, otherscopes);
        var xv, clause, clauses = n.catchClauses;
        for (var i = 0, len = clauses.length; i < len; i++) {
            clause = clauses[i];
            xv = clause.exvar;
            innerscope.push(xv);
            clause.guard &&
                tagVarRefsExp(clause.guard, innerscope, otherscopes);
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
        tagVarRefsExp(n.object, innerscope, otherscopes);
        tagVarRefsStm(n.body, innerscope, otherscopes);
        break;
    }
    return n;
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
        walkExp(n[0]); // must eval to string
        walkExp(n[1]); // must eval to obj
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
        for (var i = 0, len = n.cases.length; i < len; i++) {
            branch = n.cases[i];
            branch.caseLabel && walkExp(branch.caseLabel);
            walkStm(branch.statements);
        }
        break;

    case FOR: 
        if (n.iterator) {// FOR_IN
            // n.varDecl doesn't seem to be useful
            walkExp(n.iterator);
            walkExp(n.object);
        }
        else {// classic FOR
            if (n.setup) {
                if (n.setup.type === VAR || n.setup.type === CONST)
                    walkStm(n.setup);
                else walkExp(n.setup);
            }
            n.condition && walkExp(n.condition);
            n.update && walkExp(n.update);
        }
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



