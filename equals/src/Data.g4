grammar Data;
import Lexer;

@lexer::members {
	int INDENT_TOKEN  = INDENT;
	int DEDENT_TOKEN  = DEDENT;
	int VOCURLY_TOKEN = VOCURLY;
	int VCCURLY_TOKEN = VCCURLY;
	int SEMI_TOKEN 	  = SEMI;
}

@parser::members {
	std::vector <std::string> functions;
}

module : body EOF;

body : (topdecls | NEWLINE)+;

topdecls : topdecl;

topdecl : decl semi;

decls 
	:
	open (decl semi+)* decl semi* close
	;

decl 
	: 
	gendecl
	| (funlhs rhs)
	;

gendecl	
	:
	fixity (DECIMAL)? ops
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

funlhs 
	:
	var apat*
	;

rhs 
	: 
	('=' exp (WHERE decls)?)
	| (gdrhs (WHERE decls)?);

gdrhs
	:
	guards '=' exp (guards '=' exp)*
	;

guards
	:
	GUARD guard (',' guard)*
	;

guard
	:
	exp
	;

exp	
	:
	infixexp
	| (LEGIT | DECIMAL | arithmetic)+
	;

infixexp
	:
	lexp
	;

lexp
	:
	LET decls IN exp
	;

arithmetic
	:
	('+' | '-' | '*' | '/')
	;

var : LEGIT;

apat : LEGIT;

op	: ('$' | '?' | '<' | '>')+; 

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