grammar pi;

@header {#pragma warning disable 3021}

/* top level */

main: def* EOF;

def: funcDef | structDef | predDef;

funcDef:
	beforeFunc (type | 'void') IDENT '(' (var (',' var)*)? ')' '{' stmt* '}';

structDef: 'struct' IDENT '{' (var ';')* '}';

predDef:
	'predicate' IDENT '(' (var (',' var)*)? ')' ':=' expr ';';

/* about statement */
stmt:
	var (':=' expr)? ';'												# VarDeclStmt
	| expr ';'															# ExprStmt
	| assign ';'														# AssignStmt
	| 'if' '(' expr ')' stmt ('else' stmt)?								# IfStmt
	| 'while' beforeBranch '(' expr ')' stmt							# WhileStmt
	| 'for' beforeBranch '(' forInit? ';' expr ';' forIter? ')' stmt	# ForStmt
	| 'break' ';'														# BreakStmt
	| 'return' expr? ';'												# ReturnStmt
	| annotationWithLabel ';'											# AssertStmt
	| '{' stmt* '}'														# StmtBlock;

forInit: var (':=' expr)? | assign;

forIter: assign | expr;

assign:
	IDENT ':=' expr					# VarAssign
	| IDENT '[' expr ']' ':=' expr	# SubAssign
	// 可以有结果为 struct 类型的表达式——事实上只能是函数的返回值， 但这种表达式不是左值，不能放到赋值符号的右边
	| IDENT '.' IDENT ':=' expr # MemAssign;

/* about expression */
expr:
	IDENT								# IdentExpr
	| constant							# ConstExpr
	| IDENT '(' (expr (',' expr)*)? ')'	# CallExpr
	| '(' expr ')'						# ParExpr
	| expr '[' expr ']'					# SubExpr
	// 为了让 IR 更简单一点，我们仅在非 annotation 中支持新建数组
	| 'new' atomicType '[' expr ']'						# NewArrayExpr
	| expr '.' IDENT									# MemExpr
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
