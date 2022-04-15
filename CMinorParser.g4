/*
 * compatible with ACSL language grammar v1.17
 */

parser grammar CMinorParser;

options {
	tokenVocab = CMinorLexer;
}

@header {#pragma warning disable 3021}

// TODO: logic function

/* top level */
main: def* EOF;

def: funcDef | structDef | predDef;

funcDef:
	funcContract retVar '(' (paraVar (',' paraVar)*)? ')' '{' (
		decl
		| stmt
	)* '}';

structDef: 'struct' IDENT '{' (atomicType IDENT ';')* '}' ';';

/* variable */
localVar:
	atomicType IDENT
	| IDENT IDENT
	| atomicType IDENT '[' INT_CONSTANT ']';

paraVar:
	atomicType IDENT
	| IDENT IDENT
	| atomicType IDENT '[' ']';

retVar: atomicType IDENT | IDENT IDENT | 'void' IDENT;

atomicType: 'int' | 'float';

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

term:
	IDENT											# IdentTerm
	| '\\result'									# ResTerm
	| logicConstant									# ConstTerm
	| '\\length' '(' term ')'						# LengthTerm
	| '(' term ')'									# ParTerm
	| '{' term '\\with' '[' term ']' '=' term '}'	# ArrUpdTerm
	| term '[' term ']'								# ArrAccessTerm
	| term '.' IDENT								# MemTerm
	| ('!' | '-') term								# UnaryTerm
	| term ('*' | '/' | '%') term					# MulTerm
	| term ('+' | '-') term							# AddTerm
	| term ('<' | '<=' | '>' | '>=') term			# OrdTerm
	| term ('==' | '!=') term						# EquTerm
	| term '&&' term								# AndTerm
	| term '||' term								# OrTerm;

pred:
	'\\true'													# TruePred
	| '\\false'													# FalsePred
	| term (('<' | '<=' | '>' | '>=' | '==' | '!=') term)+		# CmpPred
	| IDENT ('(' term (',' term)* ')')?							# CallPred
	| '(' pred ')'												# ParPred
	| pred '&&' pred											# ConPred
	| pred '||' pred											# DisPred
	| pred '==>' pred											# ImpPred
	| pred '<==>' pred											# IffPred
	| '!' pred													# NegPred
	| pred '^^' pred											# XorPred
	| ('\\forall' | '\\exists') binder (',' binder)* ';' pred	# QuantiPred;

binder: ('boolean' | 'integer' | 'real') IDENT;

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

predDef:
	'/*@' 'predicate' IDENT ('(' paraVar (',' paraVar)* ')')? '=' pred ';' '*/'
	| '//@' 'predicate' IDENT ('(' paraVar (',' paraVar)* ')')? '=' pred ';' LINEEND;

/* miscellaneous */
constant: INT_CONSTANT | FLOAT_CONSTANT | 'true' | 'false';
