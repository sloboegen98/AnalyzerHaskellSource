grammar Data;
import Lexer;

@lexer::members {
	int INDENT_TOKEN = INDENT;
	int DEDENT_TOKEN = DEDENT;
}

@parser::members {
	int num_groups = 0;
	std::vector <std::vector <std::string> > groups;
}

script : ( NEWLINE | statement { ++num_groups; } )* EOF ;

statement
	:	simpleStatement
	|	blockStatements
	;

simpleStatement
	: { if (groups.size() == num_groups) groups.push_back({}); } LEGIT { groups[num_groups].push_back($LEGIT.text); } LEGIT* NEWLINE ;

blockStatements
	: { if (groups.size() == num_groups) groups.push_back({}); } LEGIT { groups[num_groups].push_back($LEGIT.text); } LEGIT* NEWLINE INDENT statement+ DEDENT ;

// BlockComment : '/*' ( BlockComment | . )*? '*/' -> channel(HIDDEN) ;   // allow nesting comments
// LineComment : '--' ~[\r\n]* -> channel(HIDDEN) ;

LEGIT : [a-z]+;