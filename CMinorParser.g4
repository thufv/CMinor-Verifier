/*
 * compatible with ACSL language grammar v1.17
 */

parser grammar CMinorParser;

options {
	tokenVocab = CMinorLexer;
}

@header {#pragma warning disable 3021}

/* top level */
main: def* EOF;

def: funcDef | structDef | predDefs;

funcDef:
	funcContract retVar '(' (paraVar (',' paraVar)*)? ')' '{' (
		decl
		| stmt
	)* '}';

structDef: 'struct' IDENT '{' (atomicType IDENT ';')* '}' ';';

/* variable */
localVar:
	atomicType IDENT
	| 'struct' IDENT IDENT
	| atomicType IDENT '[' INT_CONSTANT ']';

paraVar:
	atomicType IDENT
	| 'struct' IDENT IDENT
	| atomicType IDENT '[' ']';

retVar:
	atomicType IDENT
	| 'struct' IDENT IDENT
	| 'void' IDENT;

atomicType: 'int' | 'float';

logicParaVar:
	logicAtomicType IDENT
	| IDENT IDENT
	| logicAtomicType '[' ']' IDENT;

logicAtomicType: 'integer' | 'real' | 'boolean';

/* about statement */
stmt:
	';'																# EmptyStmt
	| expr ';'														# ExprStmt
	| assign ';'													# AssignStmt
	| 'if' '(' expr ')' stmt ('else' stmt)?							# IfStmt
	| loopAnnot 'while' '(' expr ')' stmt							# WhileStmt
	| loopAnnot 'do' stmt 'while' '(' expr ')'						# DoStmt
	| loopAnnot 'for' '(' forInit? ';' expr? ';' forIter? ')' stmt	# ForStmt
	| 'break' ';'													# BreakStmt
	| 'continue' ';'												# ContStmt
	| 'return' expr? ';'											# ReturnStmt
	| assertion														# AssertStmt
	| '{' (stmt | decl)* '}'										# BlockStmt;

forInit: localVar ('=' expr)? | assign;

forIter: assign | expr;

assign:
	IDENT '=' expr					# VarAssign
	| IDENT '[' expr ']' '=' expr	# SubAssign
	| IDENT '.' IDENT '=' expr		# MemAssign;

decl: localVar ('=' expr)? ';';

/* about expression */
expr:
	IDENT									# IdentExpr
	| constant								# ConstExpr
	| IDENT '(' (expr (',' expr)*)? ')'		# CallExpr
	| '(' expr ')'							# ParExpr
	| expr '[' expr ']'						# ArrAccessExpr
	| expr '.' IDENT						# MemExpr
	| ('!' | '-') expr						# UnaryExpr
	| expr ('*' | '/' | '%') expr			# MulExpr
	| expr ('+' | '-') expr					# AddExpr
	| expr ('<' | '<=' | '>' | '>=') expr	# OrdExpr
	| expr ('==' | '!=') expr				# EquExpr
	| expr '&&' expr						# AndExpr
	| expr '||' expr						# OrExpr;

/* annotation */
logicConstant:
	INT_CONSTANT
	| FLOAT_CONSTANT
	| '\\true'
	| '\\false';

arithTerm:
	IDENT															# IdentTerm
	| '\\result'													# ResTerm
	| logicConstant													# ConstTerm
	| '{' arithTerm '\\with' '[' arithTerm ']' '=' arithTerm '}'	# ArrUpdTerm
	| arithTerm '[' arithTerm ']'									# ArrAccessTerm
	| arithTerm '.' IDENT											# MemTerm
	| ('-' | '!') arithTerm											# UnaryTerm
	| arithTerm ('*' | '/' | '%') arithTerm							# MulTerm
	| arithTerm ('+' | '-') arithTerm								# AddTerm;

term:
	arithTerm								# AriTerm
	| '(' term ')'							# ParTerm
	| term ('<' | '<=' | '>' | '>=') term	# OrdTerm
	| term ('==' | '!=') term				# EquTerm
	| term '&&' term						# AndTerm
	| term '||' term						# OrTerm;

pred:
	'\\true'	# TruePred
	| '\\false'	# FalsePred
	| arithTerm (
		('<' | '<=' | '>' | '>=' | '==' | '!=') arithTerm
	)+									# CmpPred
	| IDENT ('(' term (',' term)* ')')?	# CallPred
	| '(' pred ')'						# ParPred
	| pred '&&' pred					# ConPred
	| pred '||' pred					# DisPred
	| pred '==>' pred					# ImpPred
	| pred '<==>' pred					# IffPred
	| '!' pred							# NegPred
	| pred '^^' pred					# XorPred
	// 这里化简了 ACSL 中 location 和 tset 的概念 range 是个闭区间，其首尾的类型都只能是 integer
	| '\\valid' '(' IDENT '+' '(' INT_CONSTANT '..' arithTerm ')' ')'	# LengthPred
	| ('\\forall' | '\\exists') binder (',' binder)* ';' pred			# QuantiPred;

binder: logicAtomicType IDENT (',' IDENT)*;

funcContract:
	'/*@' requiresClause* decreasesClause? ensuresClause* '*/'
	| '//@' requiresClause* decreasesClause? ensuresClause* LINEEND;

requiresClause: 'requires' pred ';';

decreasesClause: 'decreases' term ';';

ensuresClause: 'ensures' pred ';';

assertion:
	'/*@' 'assert' pred ';' '*/'
	| '//@' 'assert' pred ';' LINEEND;

loopAnnot:
	'/*@' ('loop' 'invariant' pred ';')* (
		'loop' 'variant' term ';'
	)? '*/'
	| '//@' ('loop' 'invariant' pred ';')* (
		'loop' 'variant' term ';'
	)? LINEEND;

predDefs:
	'/*@' predDef* '*/'
	| '//@' predDef* LINEEND;

predDef:
	'predicate' IDENT (
		'(' logicParaVar (',' logicParaVar)* ')'
	)? '=' pred ';';

/* miscellaneous */
constant: INT_CONSTANT | FLOAT_CONSTANT | 'true' | 'false';
