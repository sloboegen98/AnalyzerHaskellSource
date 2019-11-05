grammar Data;
import Lexer;

@lexer::members {
	int INDENT_TOKEN = INDENT;
	int DEDENT_TOKEN = DEDENT;
}

@parser::members {
	std::vector <std::string> functions;
}

module :  (clause | NEWLINE)+ EOF ;

clause
	:	
	decl
	;

decl:
	funlhs rhs DEDENT
	;

funlhs
	:
	var { functions.push_back($var.text); } apat*
	;

rhs
	:
	'=' exp (WHERE decl+)?
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