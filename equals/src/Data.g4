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

// module 
// 	:
// 	body EOF
// 	;

// body 
// 	:
// 	topdecls+
// 	;

// topdecls
// 	:
// 	(topdecl | NEWLINE)+ 
// 	;

// topdecl
// 	:
// 	decl
// 	;

// decls
// 	:
// 	(decl semi+)* decl semi*
// 	;

// decl
// 	:
// 	funlhs rhs semi
// 	;

// funlhs
// 	:
// 	var apat*
// 	;

// rhs 
// 	:
// 	'=' exp (WHERE open decls close)?
// 	;

// semi 
// 	:
// 	';'
// 	| SEMI
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

////////////////////

module :  (clause | NEWLINE)+ EOF ;

clause
	:
	decl
	;

decl
	:
	funlhs rhs semi
	;

where_decls
	:
	open (where_decl semi+)* where_decl semi* close
	;

where_decl
	:
	funlhs rhs
	;

funlhs
	:
	var apat*
	;

rhs
	:
	'=' exp (WHERE where_decls)?
	;

var:
	LEGIT
	;

apat
	:
	LEGIT
	;

exp
	:
	(LEGIT | DECIMAL | arithmetic)+
	;

arithmetic
	:
	'+' | '-' | '*' | '/'
	;

semi
	:
	SEMI
	| ';'
	;

open
	:
	OCURLY
	| VOCURLY
	;
close
	:
	CCURLY
	| VCCURLY
	;