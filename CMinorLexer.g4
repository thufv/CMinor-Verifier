/*
 * This lexer grammar only targets C#.
 */

lexer grammar CMinorLexer;

@header {#pragma warning disable 3021}

@preinclude {
    using Antlr4.Runtime;
}

@members {
  bool inAnnot = false;
  bool inLineAnnot = false;
}

/* --- literals --- */
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

/* --- constants --- */
INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

/* --- comments --- */
COMMENT: '/*' ('*/' | ~('@') .*? '*/') -> skip;
LINE_COMMENT: '//' ([\r\n] | ~('@') ~[\r\n]*) -> skip;

/* --- annotationss --- */
ANNOT_START: '/*@' { inAnnot = true; };
ANNOT_END: '*/' { inAnnot = false; };
LINE_ANNOT_START: '//@' { inLineAnnot = true; };

/* --- '@' is skipped in annotation --- */
AT: '@' { if (inAnnot || inLineAnnot) Skip(); };

/* --- LINEEND cannot be skipped for line annotation --- */
LINEEND: [\r\n] {
    if (inLineAnnot) inLineAnnot = false;
    else Skip();
};

/* --- skip white spaces --- */
WS: [ \t\u000C] -> skip;
