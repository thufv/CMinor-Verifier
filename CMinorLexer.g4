lexer grammar CMinorLexer;

@header {#pragma warning disable 3021}

VOID: 'void';
STRUCT: 'struct';

LPAR: '(';
RPAR: ')';
LBRACE: '{';
RBRACE: '}';
COMMA: ',';
SEMICOLON: ';';
LBRACKET: '[';
RBRACKET: ']';
PERIOD: '.';

INT: 'int';
FLOAT: 'float';
BOOL: 'bool';

IF: 'if';
ELSE: 'else';
BREAK: 'break';
CONTINUE: 'continue';
RETURN: 'return';
WHILE: 'while';
DO: 'do';
FOR: 'for';

ASSIGN: '=';

EQ: '==';
NE: '!=';
LE: '<=';
LT: '<';
GE: '>=';
GT: '>';
ADD: '+';
MINUS: '-';
MUL: '*';
DIV: '/';
NEG: '!';
MOD: '%';
AND: '&&';
OR: '||';
EXPR_TRUE: 'true';
EXPR_FALSE: 'false';

ANNO_TRUE: '\\true';
ANNO_FALSE: '\\false';
RESULT: '\\result';
LENGTH: '\\length';
OLD: '\\old';
WITH: '\\with';
IMPLY: '==>';
EQUIV: '<==>';
XOR: '^^';
FORALL: '\\forall';
EXISTS: '\\exists';
BOOLEAN: 'boolean';
INTEGER: 'integer';
REAL: 'real';
REQUIRES: 'requires';
DECREASES: 'decreases';
ENSURES: 'ensures';
ASSERT: 'assert';
LOOP: 'loop';
INVARIANT: 'invariant';
VARIANT: 'variant';
PREDICATE: 'predicate';

INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

COMMENT: '/*' ~('@') .*? '*/' -> skip; // TODO: 这里也要改改，万一第一个字符就是 * 怎么办呢qwq
LINE_COMMENT: '//' ~('@') ~[\r\n]* -> skip;

ANNOT_START: '/*@';
ANNOT_END: '*/';
LINE_ANNOT_START: '//@';

// 不在 line annotation 里时，我们
WS: [ \t\u000C\r\n] -> skip; // if 

// mode IN_ANNOT;

// 在 line annotation 里时，我们就不能 skip '\r' 和 '\n' 了
// WS: [ \t\u000C] -> popMode;
