grammar pi;

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
    | annotationWithLabel termination
    | annotationWithLabel;

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

ifStmt: 'if' '(' expr ')' stmt ('else' stmt)?;

whileStmt: 'while' beforeBranch '(' expr ')' stmt;

forCondition:
    expr? ';' expr ';' expr?
    | varDeclAndAssign ';' expr ';' expr?
    ;

forStmt: 'for' beforeBranch '(' forCondition ')' stmt;

termination: '#' '(' terminationArgs ')';

terminationArgs:
    expr
    | terminationArgs ',' expr;

returnStmt: 'return' expr? ';';

breakStmt: 'break' ';';

assertStmt: annotationWithLabel ';';

commaSeperatedListOfVars:
    IDENT ',' commaSeperatedListOfVars
    | IDENT;

expr:
    IDENT # IdentExpr
    | constant # ConstExpr
    | expr '(' callInterior ')' # CallExpr
    | '(' expr ')' # ParExpr
    | expr '[' expr ']' # SubExpr
    | 'new' type '[' expr ']' # NewExpr
    | IDENT '.' IDENT # MemExpr
    | expr '{' expr '<-' expr '}' # ArrUpdExpr
    | ('!' | '-') expr # UnaryExpr
    | expr ('*' | '/' | 'div' | '%') expr # MulExpr
    | expr ('+' | '-') expr # AddExpr
    | expr ('<' | '<=' | '>' | '>=') expr # InequExpr
    | expr ('=' | '!=') expr # EquExpr
    | ('forall' | 'exists') commaSeperatedListOfVars '.' expr # QuantifiedExpr
    | expr '&&' expr # AndExpr
    | expr '||' expr # OrExpr
    | expr ('<->' | '->') expr # ArrowExpr
    | '|' expr '|' # LengthExpr
    | IDENT ':=' expr # AssignExpr
    | expr '[' expr ']' ':=' # SubAssignExpr
    | IDENT '.' IDENT ':=' # MemAssignExpr
    ;

callInterior:
    | (expr ',')* expr
    ;

constant:
    INT_CONSTANT
    | FLOAT_CONSTANT
    | 'true'
    | 'false';

annotation: expr;

annotationWithLabel:
    '@' IDENT ':' annotation
    | '@' annotation;

annotationPre: '@pre' annotation;

annotationPost: '@post' annotation;

/* lexer */
INT_CONSTANT: [0-9]+;
FLOAT_CONSTANT: [0-9]+ '.' [0-9]+;
IDENT: [a-zA-Z] [a-zA-Z0-9_]*;

COMMENT: '/*' .*? '*/' -> skip;
LINE_COMMENT: '//' ~[\r\n]* -> skip;

WS: [ \t\r\n\u000C] -> skip;
