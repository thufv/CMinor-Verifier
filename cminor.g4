grammar cminor;

// @header {#pragma warning disable 3021}

/* top level */
main: def* EOF;

def: funcDef | structDef;

funcDef:
	(type | 'void') IDENT '(' (var (',' var)*)? ')' '{' (decl | stmt)* '}';

structDef: 'struct' IDENT '{' (var ';')* '}' ';';

/* variable */
var:
	atomicType IDENT 						# atomicVar
	| IDENT IDENT 							# structVar
	| atomicType IDENT '[' INT_CONSTANT ']' # arrayVar;

/* type */
type: atomicType | IDENT;

atomicType: 'int' | 'float' | 'bool';

/* about statement */
stmt:
	';'																	# EmptyStmt
	| expr ';'															# ExprStmt
	| assign ';'														# AssignStmt
	| 'if' '(' expr ')' stmt ('else' stmt)?								# IfStmt
	| 'while' '(' expr ')' stmt											# WhileStmt
	| 'for' '(' forInit? ';' expr? ';' forIter? ')' stmt				# ForStmt
	| 'break' ';'														# BreakStmt
	| 'continue' ';'													# ContStmt
	| 'return' expr? ';'												# ReturnStmt
	| '{' (stmt | decl)* '}'											# StmtBlock;

forInit: var ('=' expr)? | assign;

forIter: assign | expr;

assign:
	IDENT '=' expr					# VarAssign
	| IDENT '[' expr ']' '=' expr	# SubAssign
	| IDENT '.' IDENT '=' expr 		# MemAssign;

decl: var ('=' expr)? ';';

/* about expression */
expr:
	IDENT								# IdentExpr
	| constant							# ConstExpr
	| IDENT '(' (expr (',' expr)*)? ')'	# CallExpr
	| '(' expr ')'						# ParExpr
	| expr '[' expr ']'					# SubExpr
	| expr '.' IDENT							# MemExpr
	| ('!' | '-') expr									# UnaryExpr
	| expr ('*' | '/' | '%') expr				# MulExpr
	| expr ('+' | '-') expr								# AddExpr
	| expr ('<' | '<=' | '>' | '>=') expr				# InequExpr
	| expr ('==' | '!=') expr							# EquExpr
	| expr '&&' expr									# AndExpr
	| expr '||' expr									# OrExpr;

// logicExpr:
// 	expr														# normalLogicExpr
// 	| '\\length' '(' logicExpr ')'								# LengthExpr
// 	| '{' logicExpr '\\with' '[' IDENT ']' '=' logicExpr '}'	# arrayUpdExpr
// 	| expr ('<->' | '->') expr							 		# ArrowExpr
// 	| ('\\forall' | '\\exists') IDENT (',' IDENT)* '.' expr	 	# QuantifiedExpr;

/* annotation */
// annotationWithLabel: '@' (IDENT ':')? expr;

// annotationPre: '@pre' expr;

// annotationPost: '@post' expr;

// beforeFunc:
// 	termination annotationPre annotationPost
// 	| annotationPre annotationPost
// 	| annotationPre termination annotationPost
// 	| annotationPre annotationPost termination
// 	| termination annotationPost annotationPre
// 	| annotationPost annotationPre
// 	| annotationPost termination annotationPre
// 	| annotationPost annotationPre termination;

// beforeBranch:
// 	termination annotationWithLabel
// 	| annotationWithLabel termination
// 	| annotationWithLabel;

// termination: '#' '(' expr (',' expr)* ')';

/* miscellaneous */
constant: INT_CONSTANT | FLOAT_CONSTANT | 'true' | 'false';

/* spec */
// spec:

/* pred */
// predDef:
// 	'predicate' IDENT '(' (var (',' var)*)? ')' ':=' expr ';';

/* lexer */
INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;

WS: [ \t\r\n\u000C] -> skip;
