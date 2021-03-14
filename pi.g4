grammar pi;

@header {#pragma warning disable 3021}

/* top level */

main: decl* EOF;

decl: fnDecl | predicate | structDecl;

fnDecl:
	beforeFunc (type | 'void') IDENT '(' (var (',' var)*)? ')' stmtBlock;

structDecl: 'struct' IDENT '{' varDecl* '}';

predicate:
	'predicate' IDENT '(' (var (',' var)*)? ')' ':=' expr ';';

/* about statement */
stmt:
	varDecl
	| varDeclAndAssign ';'
	| call ';'
	| assignStmt
	| ifStmt
	| whileStmt
	| forStmt
	| breakStmt
	| returnStmt
	| assertStmt
	| stmtBlock;

stmtBlock: '{' stmt* '}';

varDeclAndAssign: var ':=' expr;

ifStmt: 'if' '(' expr ')' stmt ('else' stmt)?;

whileStmt: 'while' beforeBranch '(' expr ')' stmt;

forStmt: 'for' beforeBranch '(' forCondition ')' stmt;

forCondition:
	expr? ';' expr ';' expr?
	| varDeclAndAssign ';' expr ';' expr?;

returnStmt: 'return' expr? ';';

breakStmt: 'break' ';';

assertStmt: annotationWithLabel ';';

assignStmt:
	IDENT ':=' expr					# VarAssign
	| expr '[' expr ']' ':=' expr	# SubAssign
	| IDENT '.' IDENT ':=' expr		# MemAssign;

/* about expression */
expr:
	IDENT												# IdentExpr
	| constant											# ConstExpr
	| IDENT '(' callInterior ')'						# CallExpr
	| '(' expr ')'										# ParExpr
	| expr '[' expr ']'									# SubExpr
	| 'new' type '[' expr ']'							# NewArrayExpr
	| IDENT '.' IDENT									# MemExpr
	| expr '{' expr '<-' expr '}'						# ArrUpdExpr
	| ('!' | '-') expr									# UnaryExpr
	| expr ('*' | '/' | 'div' | '%') expr				# MulExpr
	| expr ('+' | '-') expr								# AddExpr
	| expr ('<' | '<=' | '>' | '>=') expr				# InequExpr
	| expr ('=' | '!=') expr							# EquExpr
	| ('forall' | 'exists') IDENT (',' IDENT)* '.' expr	# QuantifiedExpr
	| expr '&&' expr									# AndExpr
	| expr '||' expr									# OrExpr
	| expr ('<->' | '->') expr							# ArrowExpr
	| '|' expr '|'										# LengthExpr;

// This rule is actually the same as the CallExpr alternative rule, it is separated as an
// independent rule because ANTLR cannot handle mutually left-recursiveness.
call: expr '(' callInterior ')';

callInterior: | (expr ',')* expr;

/* annotation */
annotationWithLabel: '@' IDENT ':' expr | '@' expr;

annotationPre: '@pre' expr;

annotationPost: '@post' expr;

beforeFunc:
	termination annotationPre annotationPost
	| annotationPre annotationPost
	| annotationPre termination annotationPost
	| annotationPre annotationPost termination
	| termination annotationPost annotationPre
	| annotationPost annotationPre
	| annotationPost termination annotationPre
	| annotationPost annotationPre termination;

beforeBranch:
	termination annotationWithLabel
	| annotationWithLabel termination
	| annotationWithLabel;

termination: '#' '(' terminationArgs ')';

terminationArgs: expr | terminationArgs ',' expr;

/* about type */
type: atomicType '[]'? | IDENT;

atomicType: 'int' | 'float' | 'bool';

/* miscellaneous */
constant: INT_CONSTANT | FLOAT_CONSTANT | 'true' | 'false';

var: type IDENT;

varDecl: var ';';

/* lexer */
INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;

WS: [ \t\r\n\u000C] -> skip;
