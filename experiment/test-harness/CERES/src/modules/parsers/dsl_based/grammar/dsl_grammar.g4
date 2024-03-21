grammar dsl_grammar;

// Lexer rules
NW : [\n];
WS : [ \t]+ -> skip;
EXTFUNC : 'Func_' [a-zA-Z]+ ('_' [a-zA-Z]+)*;
RANGE : 'RANGE';
NULL : 'NULL';
PRECONDKWENT : 'PRECONDENT';
PRECONDKWRET : 'PRECONDRET';
POSTCONDKW : 'POSTCOND';
BOOL : 'True' | 'False';
NTERM : [A-Z] [a-z]+;
ATTRNAME : 'SIZE' | 'VAL' | 'BEGIN';
LETTER : [a-zA-Z];
NUMBER : [0-9]+;
LTB : '[';
RTB : ']';
LFB : '(';
RFB : ')';
LSB : '{';
RSB : '}';
COLON : ':';
DCOLON : '::=';
STRUCTOR : '|';
STRUCTAND : '&';
GT : '>';
LT : '<';
GTE : '>=';
LTE : '<=';
EQ : '=';
NEQ : '!=';
AND : '&&';
OR : '||';
NOT : '!';
ASSGNOP : '<-';
ADD : '+';
MIN : '-';
MUL : '*';
DIV : '/';
COMMA : ',';
SEMICOLON : ';';
US : '_';
DOLLAR : '$';
QSN : '?';

// Parser rules
nw : NW;
ws : WS;
extfunc : EXTFUNC;
nullg : NULL;
preconditionkw_ent : PRECONDKWENT;
preconditionkw : PRECONDKWRET;
conditionkw : POSTCONDKW;
boolg : BOOL;
nterm : NTERM params?;
attrname : ATTRNAME;
letter : LETTER;
number : NUMBER;
term : letter | number;
ltb : LTB ;
rtb : RTB;
lfb : LFB ;
rfb : RFB;
lsb : LSB;
rsb : RSB;
colon : COLON;
dcolon : DCOLON;
structorg : STRUCTOR ;
structandg : STRUCTAND;
gt : GT ;
lt : LT ;
gte : GTE ;
lte : LTE ;
eq : EQ ;
neq : NEQ ;
andg : AND ;
org : OR ;
notg : NOT;
assgnop : ASSGNOP ;
add : ADD ;
minus : MIN ;
mul : MUL ;
div : DIV ;
comma : COMMA;
semicolon : SEMICOLON;
us : US;
index : DOLLAR number DOLLAR;
noterm : notg term;
attrbt : attrname us nterm;
rangeg : (RANGE lfb number comma number rfb) | (RANGE lfb letter comma letter rfb);

start : (nw | structstmnt)* EOF;

arrexpr : arrexpr add arrterm | arrexpr minus arrterm | arrterm;
arrterm : arrterm mul arrfactorg | arrterm div arrfactorg | arrfactorg;
arrfactorg : extfunccall |index | attrbt | number | lfb arrexpr rfb | minus arrfactorg;
boolgexpr : boolgexpr andg boolgfactorg | boolgexpr org boolgfactorg | boolgexpr eq boolgexpr | boolgexpr neq boolgexpr | boolgfactorg;
boolgfactorg : extfunccall | index | attrbt | boolg | lfb boolgexpr rfb | notg boolgfactorg | boolrelation;
boolrelation : arrexpr gt arrexpr
        |  arrexpr lt arrexpr
        |  arrexpr gte arrexpr
        |  arrexpr lte arrexpr
        |  arrexpr eq arrexpr
        |  arrexpr neq arrexpr;

structrhs1 : (nterm (US QSN)? | term)+;
structrhs2 : ltb (nterm | term) (structorg (nterm | term))+ rtb;
structrhs3 : noterm (structandg noterm)*;
structrhscodes : lsb assignstmntblock (nw precondition)? (nw precondition_ent)? (nw condblock)? rsb;

structrhs : (structrhs1 | structrhs2 | rangeg) nw structrhscodes;
structrhsnoterm : structrhs3  nw structrhscodes;
structstmnt : nterm dcolon structrhs (nw structorg structrhs)* (nw structorg structrhsnoterm)?;

precondition_ent : preconditionkw_ent colon boolgexpr;
precondition : preconditionkw colon boolgexpr;
condblock : conditionkw colon boolgexpr;
assignstmnt : attrbt assgnop (arrexpr | boolgexpr | nullg | retuple | relist);
assignstmntblock : assignstmnt (nw assignstmnt)*;
params : lfb (arrexpr|boolgexpr) (comma (arrexpr|boolgexpr))* rfb;
extfunccall : extfunc params;
retuple : lfb attrbt (comma attrbt)* rfb;
relist : ltb attrbt (comma attrbt)* rtb;
