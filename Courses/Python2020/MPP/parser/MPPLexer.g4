lexer grammar MPPLexer;

@lexer::header {
from .MPPBaseLexer import MPPBaseLexer
}

options { superClass=MPPBaseLexer; }

tokens { Open, Close, Semi, Forall }


Forall    : 'FORALL' | 'forall'      ;
Landscape : 'LANDSCAPE' | 'landscape';
Portrait  : 'PORTRAIT'  | 'portrait' ;
Image     : 'Image'                  ;
Capture   : 'Capture'                ;
Full      : 'Full'                   ;
Docx      : '[' 'docx' ']'           ;
A4        : 'A4'                     ;
Paragraph : 'p'                      ;
Header    : 'h'                      ;
Subheader : 'sh'                     ;
TText     : 't'                      ;

Add          : '+';
OpenBracket  : '(';
CloseBracket : ')';
Comma        : ',';

CommonWord : '\'' ~[']* '\''            ;
Varid      : (Letter+ Digit*) | Wildcard;
Number     : Digit+                     ;

fragment Letter  : [a-zA-Z];
fragment Digit   : [0-9];
fragment Wildcard: '_';

OneLineComment: '#' ~[\n]* -> skip;
MultilineComment: '#' (~ [\n]*? '\\' '\r'? '\n')+ ~ [\n]+ -> skip;
Ws: [ ]+ { self.processWs() } -> skip;
Tab: [\t]+ { self.processTab() } -> skip;
Newline: ('\r'? '\n' | '\r') { self.processNewline() } -> skip;

