grammar Data;
import Lexer;

@lexer::members {
	int VOCURLY_TOKEN = VOCURLY;
	int VCCURLY_TOKEN = VCCURLY;
	int SEMI_TOKEN 	  = SEMI;
}

@parser::members {
	std::vector <std::string> functions;
}

module : body EOF;

body : (topdecls | NEWLINE)+;

topdecls : topdecl semi;

topdecl : 
	(TYPE simpletype '=' type)
    | (DATA (context '=>')? simpletype ('=' constrs)? deriving?)
	| (NEWTYPE (context '=>')? simpletype '=' newconstr deriving?)
	| (CLASS (scontext '=>')? tycls tyvar (WHERE cdecls)?)
	| (INSTANCE (scontext '=>')? qtycls inst (WHERE idecls)?)
	| (DEFAULT ( type (',' type)* ))
	// | (Foreign fdecl)
	| decl;

decls 
	:
	open ((decl semi+)* decl semi*)? close
	;

decl 
	: 
	gendecl
	| ((funlhs | pat) rhs)
	;

cdecls
	:
	open ((cdecl semi+)* cdecl semi*)? close
	;

cdecl
	:
	gendecl
	| ((funlhs | var) rhs)
	;

idecls
	:
	open ((idecl semi+)* idecl semi*)? close
	;

idecl
	:
	(funlhs | var) rhs
	;

gendecl	
	:
	vars '::' (context '=>')? type
	| (fixity (DECIMAL)? ops)
	;

ops
	:
	op (',' op)*
	;

vars
	:
	var (',' var)*
	;

fixity 
	:
	INFIX | INFIXL | INFIXL
	;

type
	:
	btype ('->' type)?
	;
	
btype
	:
	atype+
	;

atype
	:
	gtycon
	| varid
	| ( '(' type (',' type)* ')' )
	| ( '[' type ']' )
	| ( '(' type ')' )
	;

gtycon
	:
	qtycon
	| ( '(' ')' )
	| ( '[' ']' )
	| ( '(' '->' ')' )
	| ( '(' ',' '{' ',' '}' ')' )
	;

context
	:
	cls
	| ( '(' cls (',' cls)* ')' )
	;

cls
	:
	(conid varid)
	| ( qtycls '(' tyvar (atype (',' atype)*) ')' )
	;

scontext
	:
	simpleclass
	| ( '(' (simpleclass (',' simpleclass)*)? ')' )
	;

simpleclass
	:
	qtycls tyvar
	;

simpletype
	: 
	tycon tyvar*
	;

constrs
	: 
	constr ('|' constr)*
	;

constr
	: 
	(con ('!'? atype)*)
	| ((btype | ('!' atype)) conop (btype | ('!' atype)))
	| (con '{' (fielddecl (',' fielddecl)* )? '}')
	;

newconstr
	:
	(con atype)
	| (con '{' var '::' type '}')
	;

fielddecl
	:
	vars '::' (type | ('!' atype))
	;

deriving
	:
	DERIVING (dclass | ('(' (dclass (',' dclass)*)? ')' ))
	;

dclass
	:
	qtycls
	;

inst 
	:
	gtycon
	| ( '(' gtycon tyvar* ')' )
	| ( '(' tyvar ',' tyvar (',' tyvar)* ')') 
	| ( '[' tyvar ']')
	| ( '(' tyvar '->' tyvar ')' )
	;

funlhs 
	:
	(var apat+)
	| (pat varop pat)
	| ( '(' funlhs ')' apat+)
	;

rhs 
	: 
	('=' exp (WHERE decls)?)
	| (gdrhs (WHERE decls)?);

gdrhs
	:
	(guards '=' exp)+
	;

guards
	:
	'|' guard (',' guard)*
	;

guard
	:
	infixexp
	;

exp	
	:
	// infixexp
	(varid | conid | DECIMAL | arithmetic)+
	;

infixexp
	:
	// (lexp qop infixexp)
	// | ('-' infixexp)
	lexp
	;

lexp
	:
	LET decls IN exp
	;

pat
	:
	(lpat qconop pat)
	| lpat
	;

lpat
	:
	apat
	| ('-' (INTEGER | FLOAT))
	| (gcon apat+)
	;

apat 
	:
	(var ('@' apat)?)
	| gcon
	// | (qocn '{' (fpat (',' fpat)*)? '}')
	// | literal
	| '_'
	| ('(' pat ')')
	| ('(' pat ',' pat (',' pat)* ')')
	| ('[' pat (',' pat)* ']')
	| ('~'apat) 
	;

gcon
	:
	('(' ')')
	| ('[' ']')
	| ('(' (',')+ ')')
	| qcon
	;

// fpat
// 	:
// 	qvar '=' pat
// 	;

arithmetic
	:
	('+' | '-' | '*' | '/')
	;

var	:    varid   | ( '(' varsym ')' );
qvar:    qvarid  | ( '(' qvarsym ')');
con :    conid   | ( '(' consym ')' );
qcon:    qconid  | ( '(' gconsym ')');
varop:   varsym  | ('`' varid '`')   ;
qvarop:  qvarsym | ('`' qvarid '`')	 ;
conop:   consym  | ('`' conid '`')	 ;
qconop:  gconsym | ('`' qconid '`')	 ;
op:      varop   | conop			 ;
qop:     qvarop  | qconop			 ;
gconsym: ':'  	 | qconsym			 ;

open : VOCURLY | OCURLY;
close : VCCURLY | CCURLY;
semi : ';' | SEMI;

// Case    : CASE    ;
// Class   : CLASS   ;
// Data    : DATA    ;
// Default : DEFAULT ;
// Deriving: DERIVING;
// Do      : DO	  ;
// Else    : ELSE    ;
// Foreign : FOREIGN ;
// If      : IF      ;
// Import  : IMPORT  ;
// In      : IN      ;
// Infix   : INFIX   ;
// Infixl  : INFIXL  ;
// Infixr  : INFIXR  ;
// Instance: INSTANCE;
// Let     : LET	  ;
// Module  : MODULE  ;
// Newtype : NEWTYPE ;
// Of      : OF	  ;
// Then    : THEN    ;
// Type    : TYPE    ;
// Where   : WHERE   ;
// Wildcard: WILDCARD;

///////////////////////////////////////////////////

special : '(' | ')' | ',' | ';' | '[' | ']' | '`' | '{' | '}';

varid : VARID;
conid : CONID;

symbol: ascSymbol;
ascSymbol: ASCSYMBOL;
// ascSymbol: '!' | '#' | '$' | '%' | '&' | '*' | '+'
//         | '.' | '/' | '<' | '=' | '>' | '?' | '@' 
//         | '\\' | '^' | '|' | '-' | '~' | ':' ; 

// reservedid : 
// 		'case' | 'class' | 'data' | 'default' 
//         | 'deriving' | 'do' | 'else' | 'foreign'
//         | 'if' | 'import' | 'in' | 'infix' 
//         | 'infix' | 'infixl' | 'infixr'
//         | 'instance' | 'let' | 'module' | 'newtype'
//         | 'of' | 'then' | 'type' | 'where' | '_'
//         ;

// graphic : SMALL | LARGE | DIGIT | symbol | special; 

varsym : VARSYM;
consym : CONSYM;

tyvar : varid;
tycon : conid;
tycls : conid;
modid : (conid '.')* conid;

qvarid : (modid '.')? varid;
qconid : (modid '.')? varid;
qtycon : (modid '.')? tycon;
qtycls : (modid '.')? tycls;
qvarsym: (modid '.')? varsym;
qconsym: (modid '.')? consym;

// integer: INTEGER;
// float: FLOAT;
// char: '\'' ((graphic~[\'|\\]) | ' ' | escape~[\\&]) '\'';
// string : '"' ((graphic~[\'|\\]) | ' ' | escape | gap )* '"';
// escape : '\\' (char | DECIMAL);
// charesc : [a..z] | '\\' | '"' | '\'' | '&';
// gap : '\\' (NEWLINE | '\t' | ' ')'\\';