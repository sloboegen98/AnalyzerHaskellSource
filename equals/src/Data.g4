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
	// ('type' simpletype '=' type)
   ('data' (context '=>')? simpletype ('=' constrs)? deriving?)
	// | ('newtype' (context '=>')? simpletype '=' newconstr ('deriving')?)
	// | ('class' (scontext '=>')? tycls tyvar ('where' cdecls)?)
	// | ('instance' (scontext '=>')? QTYCLS inst ('where' idecls)?)
	// | ('default' ( type (',' type)* ))
	// | ('foreign' fdecl)
	| (decl);

decls 
	:
	open (decl semi+)* decl semi* close
	;

decl 
	: 
	gendecl
	| ((funlhs | pat) rhs)
	;

cdecls
	:
	open (cdecl semi+)* cdecl semi* close
	;

cdecl
	:
	gendecl
	| ((funlhs | var) rhs)
	;

idecls
	:
	open (idecl semi+)* idecl semi* close
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
	'infixl' | 'infixr' | 'infix'
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
	| TYVAR
	| ( '(' type (',' type)* ')' )
	| ( '[' type ']' )
	| ( '(' type ')' )
	;

gtycon
	:
	QTYCON
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
	(QTYCLS TYVAR)
	| ( QTYCLS '(' TYVAR (atype (',' atype)*) ')' )
	;

scontext
	:
	'(' simpleclass (',' simpleclass)* ')'
	;

simpleclass
	:
	QTYCLS TYVAR
	;

simpletype
	:
	TYCON TYVAR*
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

fielddecl
	:
	vars '::' (type | ('!' atype))
	;

deriving
	:
	'deriving' (dclass | ('(' (dclass (',' dclass)*)? ')' ))
	;

dclass
	:
	QTYCLS
	;

funlhs 
	:
	(var apat+)
	| (pat varop pat)
	| ( '(' funlhs ')' apat+)
	;

rhs 
	: 
	('=' exp ('where' decls)?)
	| (gdrhs ('where' decls)?);

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
	(VARID | CONID | DECIMAL | arithmetic)+
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
	;

// fpat
// 	:
// 	qvar '=' pat
// 	;

arithmetic
	:
	('+' | '-' | '*' | '/')
	;

var	: VARID | ( '(' VARSYM ')' );
qvar: QVARID| ( '(' QVARSYM ')');
con : CONID | ( '(' CONSYM ')' );
qcon: QCONID| ( '(' gconsym ')');
varop: QVARSYM | ('`' VARID '`');
qvarop: QVARSYM | ('`' QVARID '`');
conop: CONSYM | ('`' CONID '`');
qconop: gconsym | ('`' QCONID '`');
op: varop | conop;
qop: qvarop | qconop;
gconsym: ':' | QCONSYM;

open : VOCURLY | OCURLY;
close : VCCURLY | CCURLY;
semi : ';' | SEMI;


////////////////////

// module :  (clause | NEWLINE)+ EOF ;

// clause
// 	:
// 	decl
// 	;

// decl
// 	:
// 	funlhs rhs semi
// 	;

// where_decls
// 	:
// 	open (where_decl semi+)* where_decl semi* close
// 	;

// where_decl
// 	:
// 	funlhs rhs
// 	;

// funlhs
// 	:
// 	var apat*
// 	;

// rhs
// 	:
// 	'=' exp (WHERE where_decls)?
// 	;

// var:
// 	LEGIT
// 	;

// apat
// 	:
// 	LEGIT
// 	;

// exp
// 	:
// 	(LEGIT | DECIMAL | arithmetic)+
// 	;

// arithmetic
// 	:
// 	'+' | '-' | '*' | '/'
// 	;

// semi
// 	:
// 	SEMI
// 	| ';'
// 	;

// open
// 	:
// 	OCURLY
// 	| VOCURLY
// 	;
// close
// 	:
// 	CCURLY
// 	| VCCURLY
// 	;