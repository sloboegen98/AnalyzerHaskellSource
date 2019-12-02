lexer grammar Lexer;

@lexer::header {
    #include <list>
    #include <stack>
    #include <memory>
    #include <vector>
    #include <utility>
    #include <string>
}

@lexer::members {

    typedef antlr4::CommonToken CommonToken;
    typedef antlr4::Token       Token;

    struct initIndent {
        int getStartIndex = 0;
        int getLine = 0;
        int getCharPositionInLine = 0;
    };

    void assign_next(initIndent* &ptr, std::unique_ptr <antlr4::Token> &next) {
        ptr = new initIndent();

        ptr->getStartIndex = next->getStartIndex();
        ptr->getLine = next->getLine();
        ptr->getCharPositionInLine = next->getCharPositionInLine();
    }

    bool pendingDent = true;
    int indentCount = 0;
    std::list < std::unique_ptr<Token> > tokenQueue;
    std::stack <std::pair <std::string, int> > indentStack;
    initIndent* initialIndentToken = nullptr;
    std::string last_key_word;

    bool prev_was_endl = false;
    bool prev_was_keyword = false;
    bool ignore_indent = false;

    int start_indent = -1;
    int nested_level = 0;

    int getSavedIndent() { return indentStack.empty() ? start_indent : indentStack.top().second; }

    std::unique_ptr <CommonToken> 
    createToken(int type, std::string text, int start_ind) {
        auto token = std::unique_ptr<CommonToken>(new CommonToken(type, text));

        if (initialIndentToken) {
            token->setStartIndex(initialIndentToken->getStartIndex);
            token->setLine(initialIndentToken->getLine);
            token->setCharPositionInLine(initialIndentToken->getCharPositionInLine);
            token->setStopIndex(start_ind - 1);
        } 
        return token;
    }   

    void processINToken(int st_ind) {
        if (indentStack.empty()) return;

        while (((indentStack.top()).first) != "let") {
            tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
            tokenQueue.push_back(createToken(VCCURLY, "VCCURLY", st_ind));
            nested_level--;
            indentStack.pop();
        }

        if ((indentStack.top()).first == "let") {
            tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
            tokenQueue.push_back(createToken(VCCURLY, "VCCURLY", st_ind));
            nested_level--;
            indentStack.pop();
        }
    }

    void processEOFToken(std::unique_ptr<Token>& next) {
        indentCount = start_indent;
        if (!pendingDent) {
            assign_next(initialIndentToken, next);
        }

        int st_ind = next->getStartIndex();

        while (nested_level > indentStack.size()) {
            if (nested_level > 0)
                nested_level--;

            tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
            tokenQueue.push_back(createToken(VCCURLY, "VCCURLY", st_ind));
        }

        while (indentCount < getSavedIndent()) {
            if (!indentStack.empty() && nested_level > 0) {
                indentStack.pop();
                nested_level--;
            }

            tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
            tokenQueue.push_back(createToken(VCCURLY, "VCCURLY", st_ind));
        }

        if (indentCount == getSavedIndent()) {
            tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
        }

        start_indent = -1;
    }

    std::unique_ptr <Token> nextToken() override {
        if (!tokenQueue.empty()) {
            auto ptr = std::move(tokenQueue.front());
            tokenQueue.pop_front();
            return ptr;
        }

        auto next = Lexer::nextToken();

        if (start_indent == -1 && (next->getType() != NEWLINE && next->getType() != WS && next->getType() != TAB))
            start_indent = next->getCharPositionInLine();

        int st_ind = next->getStartIndex();

        // std::cout << next->toString() << std::endl;
        if (next->getType() == OCURLY) {
            if (prev_was_keyword) { 
                nested_level--;
                prev_was_keyword = false;
            }

            ignore_indent = true;
            prev_was_endl = false;
        }

        if (prev_was_keyword && !prev_was_endl && (next->getType() == VARID || next->getType() == CONID)) {
            prev_was_keyword = false;
            indentStack.push({last_key_word, next->getCharPositionInLine()});
            tokenQueue.push_back(createToken(VOCURLY, "VOCURLY", st_ind));
        }

        if (ignore_indent && (next->getType() == WHERE || next->getType() == DO || next->getType() == LET || next->getType() == OF || next->getType() == CCURLY)) {
            ignore_indent = false;
            prev_was_endl = (next->getType() == WHERE || next->getType() == DO || next->getType() == LET || next->getType() == OF);
        }

        if (pendingDent && prev_was_endl
            && !ignore_indent
            && indentCount <= getSavedIndent()
            && next->getType() != NEWLINE
            && next->getType() != WHERE
            && next->getType() != LET
            && next->getType() != DO
            && next->getType() != OF
            && next->getType() != EOF) {

            while (nested_level > indentStack.size()) {
                if (nested_level > 0)
                    nested_level--;
                
                tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
                tokenQueue.push_back(createToken(VCCURLY, "VCCURLY", st_ind));
            }

            while (indentCount < getSavedIndent()) {
                if (!indentStack.empty() && nested_level > 0) {
                    indentStack.pop();
                    nested_level--;
                }

                tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
                tokenQueue.push_back(createToken(VCCURLY, "VCCURLY", st_ind));
            }
            
            if (indentCount == getSavedIndent()) {
                tokenQueue.push_back(createToken(SEMI, "SEMI", st_ind));
            }

            prev_was_endl = false;
            if (indentCount == start_indent) pendingDent = false;
        }

        if (pendingDent && prev_was_keyword
            && !ignore_indent
            && indentCount > getSavedIndent()
            && next->getType() != NEWLINE
            && next->getType() != WS
            && next->getType() != EOF) {
            
            prev_was_keyword = false;

            if (prev_was_endl) {
                indentStack.push({last_key_word, indentCount});
                prev_was_endl = false;
            }

            tokenQueue.push_back(createToken(VOCURLY, "VOCURLY", st_ind));
        }

        if (pendingDent && initialIndentToken == nullptr && NEWLINE != next->getType()) {     
            assign_next(initialIndentToken, next);
        }

        if (next != nullptr && next->getType() == NEWLINE) {
            prev_was_endl = true;
        }

        if (next->getType() == WHERE || next->getType() == LET || next->getType() == DO || next->getType() == OF) {
            nested_level++; // if next will be OCURLY need to decrement nested_level
            prev_was_keyword = true;
            prev_was_endl = false;
            last_key_word = next->getText();
        }

        if (next != nullptr && next->getType() == OCURLY) {
            prev_was_keyword = false;
        }

        if (next == nullptr || HIDDEN == next->getChannel() || NEWLINE == next->getType())
            return next; 

        if (next->getType() == IN) {
            processINToken(st_ind);
        }

        if (next->getType() == EOF) {
            processEOFToken(next);
        }

        pendingDent = true;

        tokenQueue.push_back(std::move(next));
        auto p = std::move(tokenQueue.front());
        tokenQueue.pop_front();
        
        return p; 
    }
}

NEWLINE : ('\r'? '\n' | '\r') {
    if (pendingDent) { setChannel(HIDDEN); }
    indentCount = 0;
    initialIndentToken = nullptr;
} ;

TAB : [\t]+ {
    setChannel(HIDDEN);
    if (pendingDent) {
        indentCount += 8*getText().length();
    }
} ;

WS : [ ]+ {
    setChannel(HIDDEN);
    if (pendingDent) {
        indentCount += getText().length();
    }
} ;

COMMENT : '--' (~[\r\n])* -> skip;
NCOMMENT : OPECOM .*? CLOSECOM -> skip;
OPECOM : '{-';
CLOSECOM : '-}';

OCURLY : '{';
CCURLY : '}';
VOCURLY : 'VOCURLY' { setChannel(HIDDEN); };
VCCURLY : 'VCCURLY' { setChannel(HIDDEN); };
SEMI    : 'SEMI'    { setChannel(HIDDEN); };

CASE     : 'case'    ;
CLASS    : 'class'   ;
DATA     : 'data'    ;
DEFAULT  : 'default' ;
DERIVING : 'deriving';
DO       : 'do'      ;
ELSE     : 'else'    ;
EXPORT   : 'export'  ;
FOREIGN  : 'foreign' ;
IF       : 'if'      ;
IMPORT   : 'import'  ;
IN       : 'in'      ;
INFIX    : 'infix'   ;
INFIXL   : 'infixl'  ;
INFIXR   : 'infixr'  ;
INSTANCE : 'instance';
LET      : 'let'     ;
MODULE   : 'module'  ;
NEWTYPE  : 'newtype' ;
OF       : 'of'      ;
THEN     : 'then'    ;
TYPE     : 'type'    ;
WHERE    : 'where'   ;
WILDCARD : '_'       ;
QUALIFIED: 'qualified';

CHAR : '\'' (' ' | DECIMAL | SMALL | LARGE 
              | ASCSYMBOL | DIGIT | ',' | ';' | '(' | ')' 
              | '[' | ']' | '`' | '"') '\'';
STRING : '"' (' ' | DECIMAL | SMALL | LARGE 
              | ASCSYMBOL | DIGIT | ',' | ';' | '(' | ')' 
              | '[' | ']' | '`' | '\'')* '"';

VARID : SMALL (SMALL | LARGE | DIGIT | '\'' )*;
CONID : LARGE (SMALL | LARGE | DIGIT | '\'' )*;

ASCSYMBOL : '!' | '#' | '$' | '%' | '&' | '*' | '+'
        | '.' | '/' | '<' | '=' | '>' | '?' | '@' 
        | '\\' | '^' | '|' | '-' | '~' | ':' ; 

// RESERVEDOP : '..' | ':' | '::' | '=' | '\\' 
//              | '|' | '<-' | '->' | '@' | '~' | '=>';

fragment DIGIT : ASCDIGIT;

fragment ASCDIGIT : [0-9];
// fragment UNIDIGIT:
//     | [\u0030-\u0039]
//     | [\u0660-\u0669]
//     | [\u06F0-\u06F9]
//     | [\u0966-\u096F]
//     | [\u09E6-\u09EF]
//     | [\u0A66-\u0A6F]
//     | [\u0AE6-\u0AEF]
//     | [\u0B66-\u0B6F]
//     | [\u0BE7-\u0BEF]
//     | [\u0C66-\u0C6F]
//     | [\u0CE6-\u0CEF]
//     | [\u0D66-\u0D6F]
//     | [\u0E50-\u0E59]
//     | [\u0ED0-\u0ED9]
//     | [\u0F20-\u0F29]
//     | [\u1040-\u1049]
//     | [\u1369-\u1371]
//     | [\u17E0-\u17E9]
//     | [\u1810-\u1819]
//     | [\uFF10-\uFF19]
//     ;


DECIMAL : DIGIT+;
FLOAT: (DECIMAL '.' DECIMAL (EXPONENT)?) | (DECIMAL EXPONENT);
EXPONENT : [eE] [+-]? DECIMAL;

fragment LARGE : ASCLARGE | UNILARGE;

fragment ASCLARGE : [A-Z];
fragment UNILARGE : [\u0421];

fragment SMALL : ASCSMALL | UNISMALL;
fragment ASCSMALL : [_a-z];
fragment UNISMALL 
    :
    [\u0425] 
    ;
