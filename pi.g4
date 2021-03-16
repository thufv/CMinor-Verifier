grammar pi;

@header {#pragma warning disable 3021}

/* top level */

main: decl* EOF;

decl: funcDef | structDef | predDef;

funcDef:
	beforeFunc (type | 'void') IDENT '(' (var (',' var)*)? ')' '{' stmt* '}';

structDef: 'struct' IDENT '{' var* '}';

predDef:
	'predicate' IDENT '(' (var (',' var)*)? ')' ':=' expr ';';

/* about statement */
stmt:
	var (':=' expr)? ';'														# VarDeclStmt
	| expr ';'																	# ExprStmt
	| IDENT ':=' expr															# VarAssignStmt
	| expr '[' expr ']' ':=' expr												# SubAssignStmt
	| expr '.' IDENT ':=' expr													# MemAssignStmt
	| 'if' '(' expr ')' stmt ('else' stmt)?										# IfStmt
	| 'while' beforeBranch '(' expr ')' stmt									# WhileStmt
	| 'for' beforeBranch '(' (var (':=' expr)?)? ';' expr ';' expr? ')' stmt	# ForStmt
	| 'break' ';'																# BreakStmt
	| 'return' expr? ';'														# ReturnStmt
	| annotationWithLabel ';'													# AssertStmt
	| '{' stmt* '}'																# StmtBlock;

/* about expression */
expr:
	IDENT												# IdentExpr
	| constant											# ConstExpr
	| IDENT '(' (expr (',' expr)*)? ')'					# CallExpr
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

/* annotation */
annotationWithLabel: '@' (IDENT ':')? expr;

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

termination: '#' '(' expr (',' expr)* ')';

/* variable */
var: type IDENT;

/* type */
type: atomicType '[]'? | IDENT;

atomicType: 'int' | 'float' | 'bool';

/* miscellaneous */
constant: INT_CONSTANT | FLOAT_CONSTANT | 'true' | 'false';

/* lexer */
INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;

WS: [ \t\r\n\u000C] -> skip;
