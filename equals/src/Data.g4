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

module : ((MODULE modid exports? WHERE open body close semi*) | body) EOF;

body
	:
	(impdecls topdecls)
	| impdecls
	| topdecls
	;

impdecls
	:
	(impdecl | NEWLINE | semi)+
	;

exports
	:
	'(' (exprt (',' exprt)*)? ','? ')'
	;

exprt
	:
	qvar
	| ( qtycon ( ('(' '..' ')') | ('(' (cname (',' cname)*)? ')') )? )
	| ( qtycls ( ('(' '..' ')') | ('(' (qvar (',' qvar)*)? ')') )? )
	| ( MODULE modid )
	;

impdecl
	:
	IMPORT QUALIFIED? modid ('as' modid)? impspec? semi+
	;

impspec
	:
	('(' (himport (',' himport)* ','?)? ')')
	| ( 'hiding' '(' (himport (',' himport)* ','?)? ')' )
 	;

himport
	:
	var
	| ( tycon ( ('(' '..' ')') | ('(' (cname (',' cname)*)? ')') )? )
	| ( tycls ( ('(' '..' ')') | ('(' (var (',' var)*)? ')') )? )
	;

cname 
	:
	var | con
	;

topdecls : ((topdecl semi+) | NEWLINE | semi)+;

topdecl 
	: 
	(TYPE simpletype '=' type)
    | (DATA (context '=>')? simpletype ('=' constrs)? deriving?)
	| (NEWTYPE (context '=>')? simpletype '=' newconstr deriving?)
	| (CLASS (scontext '=>')? tycls tyvar (WHERE cdecls)?)
	| (INSTANCE (scontext '=>')? qtycls inst (WHERE idecls)?)
	| (DEFAULT '(' (type (',' type)*)? ')' )
	| (FOREIGN fdecl)
	| decl;

decls 
	:
	open ((decl semi+)* decl semi*)? close
	;

decl 
	: 
	gendecl
	| ((funlhs | pat) rhs)
	| semi+
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

fdecl
	:
	(IMPORT callconv safety? impent var '::' type)
	| (EXPORT callconv expent var '::' type)
	;

callconv
	:
	'ccall' | 'stdcall' | 'cplusplus' | 'jvm' | 'dotnet'
	;

impent : pstring;
expent : pstring;
safety : 'unsafe' | 'safe';

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
	pat '<-' infixexp
	| LET decls
	| infixexp
	;

exp	
	:
	(infixexp '::' (context '=>')? type)
	| infixexp 
	;

// comment original alt 'lexp'
infixexp
	:
	(lexp qop infixexp)
	| ('-' infixexp)
	| lexp
	;

lexp
	:
	('\\' apat+ '->' exp)
	| (LET decls IN exp)
	| (IF exp semi? THEN exp semi? ELSE exp)
	| (CASE exp OF alts)
	| (DO stmts)
	| fexp
	;

fexp
	:
	aexp+
	;

aexp 
	:
	qvar
	| gcon
	| literal
	| ( '(' exp ')' )
	| ( '(' exp ',' exp (',' exp)* ')' )
	| ( '[' exp (',' exp)* ']' )
	| ( '[' exp (',' exp)? '..' exp? ']' )
	| ( '[' exp '|' qual (',' qual)* ']' )
	| ( '(' infixexp qop ')' )
	| ( '(' qop infixexp ')' )    // qop ~ [-] ?????????
	| ( qcon '{' (fbind (',' fbind))? '}' )
	| ('{' fbind (',' fbind)* '}')+ // aexp {fbind+} ???
	;

qual 
	:
	(pat '<-' exp)
	| (LET decls)
	| exp
	;

alts
	:
	open (alt semi+)+ close
	;

alt
	:
	(pat '->' exp (WHERE decls)?)
	| (pat gdpat (WHERE decls)?)
	;

gdpat
	:
	(guards '->' exp)+
	;

// check!
stmts
	:
	open (stmt (WHERE decls)?)* exp (WHERE decls)? semi* close
	;

stmt
	:
	(exp semi+)
	| (pat '<-' exp semi+)
	| (LET decls semi+)
	| semi+
	;

fbind
	:
	qvar '=' exp	
	;

pat
	:
	(lpat qconop pat)
	| lpat
	;

lpat
	:
	apat
	| ('-' (integer | pfloat))
	| (gcon apat+)
	;

apat 
	:
	(var ('@' apat)?)
	| gcon
	| (qcon '{' (fpat (',' fpat)*)? '}')
	| literal
	| '_'
	| ('(' pat ')')
	| ('(' pat ',' pat (',' pat)* ')')
	| ('[' pat (',' pat)* ']')
	| ('~'apat) 
	;

fpat
	:
	qvar '=' pat
	;

gcon
	:
	('(' ')')
	| ('[' ']')
	| ('(' (',')+ ')')
	| qcon
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

///////////////////////////////////////////////////

literal : integer | pfloat | pchar | pstring;
// | STRING | CHAR ;
special : '(' | ')' | ',' | ';' | '[' | ']' | '`' | '{' | '}';

varid : VARID;
conid : CONID;

symbol: ascSymbol;
// ascSymbol: ASCSYMBOL;
ascSymbol: '!' | '#' | '$' | '%' | '&' | '*' | '+'
        | '.' | '/' | '<' | '=' | '>' | '?' | '@' 
        | '\\' | '^' | '|' | '-' | '~' | ':' ; 

// fix [:]// 
varsym : ascSymbol+;
consym : ':' ascSymbol;
//

tyvar : varid;
tycon : conid;
tycls : conid;
modid : (conid '.')* conid;

qvarid : (modid '.')? varid;
qconid : (modid '.')? conid;
qtycon : (modid '.')? tycon;
qtycls : (modid '.')? tycls;
qvarsym: (modid '.')? varsym;
qconsym: (modid '.')? consym;

integer: DECIMAL;
pfloat: FLOAT;
pchar: CHAR;
pstring: STRING;

// BlockComment 
// 	:
// 	'{-' .*? '-}' -> skip
// 	;

// LineComment
// 	:
// 	'--' ~[\r\n]* -> skip
// 	;


// pchar: '\'' (' ' | DECIMAL | SMALL | LARGE 
//               | ascSymbol | DIGIT | ',' | ';' | '(' | ')' 
//               | '[' | ']' | '`' | '"') '\'';

// pstring : '"' (' ' | DECIMAL | SMALL | LARGE 
//               | ascSymbol | DIGIT | ',' | ';' | '(' | ')' 
//               | '[' | ']' | '`' | '\'')* '"';


// char: '\'' ((graphic~[\'|\\]) | ' ' | escape~[\\&]) '\'';
// string : '"' ((graphic~[\'|\\]) | ' ' | escape | gap )* '"';
// escape : '\\' (char | DECIMAL);
// charesc : [a..z] | '\\' | '"' | '\'' | '&';
// gap : '\\' (NEWLINE | '\t' | ' ')'\\';