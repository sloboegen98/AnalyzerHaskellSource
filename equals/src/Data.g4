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

module :  (clause | NEWLINE)+ EOF ;

clause
	:
	decl
	;

decl
	:
	funlhs rhs SEMI
	;

where_decls
	:
	VOCURLY where_decl+ VCCURLY
	;

where_decl
	:
	decl
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

// open
// 	:
// 	'{' | VOCURLY
// 	;
// close
// 	:
// 	'}' | VCCURLY
// 	;