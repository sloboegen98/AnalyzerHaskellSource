grammar Data;
import Lexer;

@lexer::members {
	int INDENT_TOKEN = INDENT;
	int DEDENT_TOKEN = DEDENT;
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
	var apat*
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