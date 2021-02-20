grammar piVC;

// TODO: not sure how to correctly handle %prec in ocamlyacc.

main: decl* EOF;

decl:
    varDeclOutsideOfFunc
    | fnDecl
    | predicate
    | classDecl;

declInsideClass:
    varDecl
    | fnDecl
    | predicate;

type:
    'int'
    | 'float'
    | 'bool'
    | IDENT
    | type '[]';

fnDecl:
    beforeFunc type IDENT '(' formalsOrEmpty ')' stmtBlock
    | beforeFunc 'void' IDENT '(' formalsOrEmpty ')' stmtBlock;

classDecl: ('struct' | 'class') IDENT '{' declInsideClass* '}';

beforeFunc:
    | termination annotationPre annotationPost
    | annotationPre annotationPost
    | annotationPre termination annotationPost
    | annotationPre annotationPost termination
    | termination annotationPost annotationPre
    | annotationPost annotationPre
    | annotationPost termination annotationPre
    | annotationPost annotationPre termination;

beforeBranch:
    | termination annotationWithLabel
    | annotationWithLabel termination '(' callInterior ')'
    | annotationWithLabel; // TODO: %prec MediumPrecedence

predicate: 'predicate' IDENT '(' formalsOrEmpty ')' ':=' expr ';';

formalsOrEmpty:
    | formals;
    
formals:
    paramVar
    | formals ',' paramVar;

var: type IDENT;

varOutSideOfFunc: type IDENT;

paramVar: type IDENT;

stmtBlock: '{' stmt* '}';

varDeclOutsideOfFunc: varOutSideOfFunc ';';

varDecl: var ';';

stmt:
    varDecl
    | varDeclAndAssign ';'
    | expr? ';'
    | ifStmt
    | whileStmt
    | forStmt
    | breakStmt
    | returnStmt
    | assertStmt
    | stmtBlock;

varDeclAndAssign: var ':=' expr;

ifStmt: 'if' '(' expr ')' stmt 'else' stmt // %prec T_Else
    | 'if' '(' expr ')' stmt // %prec T_If
    ;

whileStmt: 'while' beforeBranch stmt;

forStmt: 'for' beforeBranch stmt;

termination: '#' '(' terminationArgs ')';

terminationArgs:
    expr
    | terminationArgs ',' expr;

returnStmt: 'return' expr? ';';

breakStmt: 'break' ';';

assertStmt: annotationWithLabel ';';

commaSeperatedListOfUniversalVarDecls:
    IDENT ',' commaSeperatedListOfUniversalVarDecls
    | IDENT;

commaSeperatedListOfExistentialVarDecls:
    IDENT ',' commaSeperatedListOfExistentialVarDecls
    | IDENT;

lValue:
    IDENT
    | expr '[' expr ']'
    | IDENT '.' IDENT;

expr:
    IDENT ':=' expr
    | expr '[' expr ']' ':='
    | IDENT '.' IDENT ':='
    | constant
    | IDENT
    | expr '[' expr ']'
    | IDENT '.' IDENT
    | expr '(' callInterior ')'
    | '(' expr ')'
    | expr '+' expr
    | expr '-' expr
    | expr '*' expr
    | expr '/' expr
    | expr 'div' expr
    | expr '%' expr
    | '-' expr // TODO: %prec UnaryMinus
    | 'forall' commaSeperatedListOfUniversalVarDecls '.' expr // TODO: %prec T_ForAll
    | 'exists' commaSeperatedListOfExistentialVarDecls '.' expr // TODO: %prec T_Exists
    | expr '{' expr '<-' expr '}'
    | expr '<' expr
    | expr '<=' expr
    | expr '>' expr
    | expr '>=' expr
    | expr '=' expr
    | expr '!=' expr
    | expr '<->' expr
    | expr '->' expr
    | expr '&&' expr
    | expr '||' expr
    | '!' expr
    | '|' expr '|'
    | 'new' type '[' expr ']';

callInterior:
    | (expr ',')* expr
    | expr? ';' expr ';' expr?
    | varDeclAndAssign ';' expr ';' expr?
    ;

constant:
    INT_CONSTANT
    | FLOAT_CONSTANT
    | 'true'
    | 'false';

annotation:
    IDENT ':=' annotation
    | annotation '[' annotation ']' ':=' annotation
    | IDENT '.' IDENT ':=' annotation
    | constant
    | IDENT // TODO: %prec VeryLowPrecedence
    | annotation '[' annotation ']' // TODO: %prec VeryLowPrecedence
    | IDENT '.' IDENT // TODO: %prec VeryLowPrecedence
    | annotation '(' callInterior ')'
    | '(' annotation ')'
    | annotation '+' annotation
    | annotation '-' annotation
    | annotation '*' annotation
    | annotation '/' annotation
    | annotation 'div' annotation
    | annotation '%' annotation
    | '-' annotation // TODO: %prec UnaryMinus
    | 'forall' commaSeperatedListOfUniversalVarDecls '.' annotation // TODO: %prec T_ForAll
    | 'exists' commaSeperatedListOfExistentialVarDecls '.' annotation // TODO: %prec T_Exists
    | IDENT ':=' annotation '{' annotation '<-' annotation '}'
    | annotation '[' annotation ']' ':=' annotation '{' annotation '<-' annotation '}'
    | IDENT '.' IDENT ':=' annotation '{' annotation '<-' annotation '}'
    | annotation '<' annotation
    | annotation '<=' annotation
    | annotation '>' annotation
    | annotation '>=' annotation
    | annotation '=' annotation
    | annotation '!=' annotation
    | annotation '<->' annotation
    | annotation '->' annotation
    | annotation '&&' annotation
    | annotation '||' annotation
    | '!' annotation
    | '|' annotation '|';

annotationExpr:
    annotation // TODO: %prec T_Period
    | annotation 'and' annotation
    | annotation 'or' annotation
    | annotation '<->' annotation
    | annotation '->' annotation
    | '!' annotation
    | '(' annotation ')';

annotationWithLabel:
    '@' IDENT ':' annotationExpr
    | '@' annotationExpr;

annotationPre: '@pre' annotationExpr;

annotationPost: '@post' annotationExpr;

/* lexer */
INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;

WS: [ \t\r\n\u000C] -> skip;
