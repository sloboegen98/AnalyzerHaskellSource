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

    int nested_level = 0;

    int getSavedIndent() { return indentStack.empty() ? 0 : indentStack.top().second; }

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
        indentCount = 0;
        if (!pendingDent) {
            assign_next(initialIndentToken, next);
        }
        
        int st_ind = next->getStartIndex();

        while (nested_level > indentStack.size()) {
            if (nested_level > 0)
                nested_level--;

            // std::cout << nested_level << ' ' << indentStack.size() << '\n';    
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
    }

    std::unique_ptr <Token> nextToken() override {
        if (!tokenQueue.empty()) {
            auto ptr = std::move(tokenQueue.front());
            tokenQueue.pop_front();
            return ptr;
        }

        auto next = Lexer::nextToken();
        int st_ind = next->getStartIndex();

        // std::cout << next->toString() << std::endl;

        if (prev_was_keyword && next->getType() == OCURLY) {
            prev_was_keyword = false;
            ignore_indent = true;
            prev_was_endl = false;
            nested_level--;
        }

        if (prev_was_keyword && !prev_was_endl && next->getType() == VARID || next->getType() == CONID) {
            prev_was_keyword = false;
            indentStack.push({last_key_word, next->getCharPositionInLine()});
            tokenQueue.push_back(createToken(VOCURLY, "VOCURLY", st_ind));
        }

        if (ignore_indent && (next->getType() == WHERE || next->getType() == CCURLY)) {
            ignore_indent = false;
            prev_was_endl = (next->getType() == WHERE);
        }

        if (pendingDent && prev_was_endl
            && !ignore_indent
            && indentCount <= getSavedIndent()
            && next->getType() != NEWLINE
            && next->getType() != WHERE
            && next->getType() != LET
            && next->getType() != DO
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
            if (indentCount == 0) pendingDent = false;
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

        if (next->getType() == WHERE || next->getType() == LET || next->getType() == DO) {
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

fragment LARGE   : [A-Z];
fragment SMALL   : [a-z];
fragment DIGIT   : [0-9];

WHERE : 'where';
LET   : 'let'  ;
IN    : 'in'   ;
DO    : 'do'   ;
CASE  : 'case' ;
OF    : 'of'   ;

IF    : 'if'   ;
THEN  : 'then' ;
ELSE  : 'else' ;

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

// GUARD  : '|';
OCURLY : '{';
CCURLY : '}';

VOCURLY : 'VOCURLY' { setChannel(HIDDEN); };
VCCURLY : 'VCCURLY' { setChannel(HIDDEN); };
SEMI    : 'SEMI'    { setChannel(HIDDEN); };


// LITERAL : INTEGER | FLOAT | CHAR | STRING;

// fragment SPECIAL : '(' | ')' | ',' | ';' | '[' | ']' | '`' | '{' | '}' ;

// COMMENT : DASHES (ANY~SYMBOL (ANY)*)? NEWLINE;
DASHES  : '--' ('-')*;
// OPENCOM : '{-';
// CLOSECOM: '-}';
// NCOMMENT: OPENCOM ANYSEQ CLOSECOM -> channel(HIDDEN);

// ANYSEQ  : (ANY)* ~(OPENCOM | CLOSECOM)
// ANY     : 

SYMBOL  : '$' | '!' | '^';

VARID   : SMALL (SMALL | LARGE | DIGIT | '\'')*;
CONID   : LARGE (SMALL | LARGE | DIGIT | '\'')*;
// fragment RESERVEDID :
//         'case' | 'class' | 'data' | 'default' 
//         | 'deriving' | 'do' | 'else' | 'foreign'
//         | 'if' | 'import' | 'in' | 'infix' 
//         | 'infix' | 'infixl' | 'infixr'
//         | 'instance' | 'let' | 'module' | 'newtype'
//         | 'of' | 'then' | 'type' | 'where' | '_'
//         ;

VARSYM  : SYMBOL~[:] (SYMBOL)*;
CONSYM  : (':' (SYMBOL)*);
fragment RESERVEDOP : '..' | ':' | '::' | '=' | '\\' | '|' 
            | '<-' | '@' | '~' | '=>'
            ;

TYVAR : VARID;
TYCON : CONID;
TYCLS : CONID;
MODID : (CONID '.')* CONID;

QVARID  : (MODID '.')? VARID ;
QCONID  : (MODID '.')? CONID ;
QTYCON  : (MODID '.')? TYCON ;
QTYCLS  : (MODID '.')? TYCLS ; 
QVARSYM : (MODID '.')? VARSYM;
QCONSYM : (MODID '.')? CONSYM;

DECIMAL : DIGIT+;

INTEGER : DECIMAL;

FLOAT: (DECIMAL '.' DECIMAL (EXPONENT)?) | (DECIMAL EXPONENT);

EXPONENT : [eE] [+-]? DECIMAL;