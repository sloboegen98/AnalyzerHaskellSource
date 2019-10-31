lexer grammar Lexer;

@lexer::header {
    #include <list>
    #include <stack>
    #include <memory>
    #include <vector>
    #include <string>
}

@lexer::members {

    typedef antlr4::CommonToken CommonToken;
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
    std::list < std::unique_ptr<antlr4::Token> > tokenQueue;
    std::stack <int> indentStack;
    initIndent* initialIndentToken = nullptr;

    bool prev_was_endl = false;

    int getSavedIndent() { return indentStack.empty() ? 0 : indentStack.top(); }

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


    std::unique_ptr <antlr4::Token> nextToken() override {
        if (!tokenQueue.empty()) {
            auto ptr = std::move(tokenQueue.front());
            tokenQueue.pop_front();
            std::cout << ptr->toString() << std::endl;
            return ptr;
        }

        auto next = Lexer::nextToken();
        int st_ind = next->getStartIndex();

        // std::cout << next->toString() << ' ' << indentCount << ' ' << getSavedIndent() << std::endl;

        if (pendingDent && initialIndentToken == nullptr && NEWLINE != next->getType()) {     
            assign_next(initialIndentToken, next);
        }
        
        if (next != nullptr && next->getType() == NEWLINE) {
            prev_was_endl = true;
        }

        if (next == nullptr || HIDDEN == next->getChannel() || NEWLINE == next->getType())
            return next; 

        if (prev_was_endl && indentCount <= getSavedIndent()) {
            prev_was_endl = false;
            tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
        } else if (next->getType() == EOF) {
            indentCount = 0;
            if (!pendingDent) {
                assign_next(initialIndentToken, next);
            }

            tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
        }

        pendingDent = false;
        
        // if ()
            tokenQueue.push_back(std::move(next));
        
        auto p = std::move(tokenQueue.front());
        tokenQueue.pop_front();
        
        return p; 
    }
}

fragment UPPER   : [A-Z];
fragment LOWER   : [a-z];
fragment DIGIT   : [0-9];

LEGIT : LOWER+;
DECIMAL : DIGIT+;

NEWLINE : ('\r'? '\n' | '\r') {
    if (!pendingDent) { setChannel(HIDDEN); }
    pendingDent = true;
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

INDENT : 'INDENT' { setChannel(HIDDEN); };
DEDENT : 'DEDENT' { setChannel(HIDDEN); };
