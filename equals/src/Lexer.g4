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
    bool prev_was_where = false;
    bool first_time = true;
    // int last_indent = 0;

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
        if (first_time) {
            indentStack.push(indentCount);
            first_time = false;
        }


        if (!tokenQueue.empty()) {
            auto ptr = std::move(tokenQueue.front());
            tokenQueue.pop_front();
            return ptr;
        }

        auto next = Lexer::nextToken();
        int st_ind = next->getStartIndex();

        std::cout << next->toString() << std::endl;

        if (pendingDent && prev_was_endl && indentCount <= getSavedIndent() && next->getType() != NEWLINE && next->getType() != EOF) {
            std::cout << "ALERT: " << next->toString() << ' ' << indentCount << std::endl;
            
            // while(indentCount < getSavedIndent()) {
            //     // tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
            //     if (!indentStack.empty()) {
            //         // std::cout << getSavedIndent() << std::endl;
            //         indentStack.pop();
            //     }
            // }

            // if (indentCount == getSavedIndent()) {
            //     prev_was_endl = false;  
            //     // pendingDent = false;
                
            //     if (indentCount == 0) {
            //         pendingDent = false;
            //     }

            //     tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
            // }

            // // if (!indentStack.empty())
            // //     indentStack.pop();

            // // indentStack.push(indentCount);

            while (indentCount != getSavedIndent()) {
                indentStack.pop();
                tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
            }

            // tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
        }

        if (pendingDent && prev_was_endl && indentCount > getSavedIndent() && next->getType() != NEWLINE && next->getType() != EOF) {
            std::cout << "PUSH: " << next->toString() << ' ' << indentCount << std::endl;

            // if (!indentStack.empty()) {
            //     indentStack.pop();
            // }

            if (prev_was_where) {
                prev_was_where = false;
                indentStack.push(indentCount);
            }
            
            prev_was_endl = false; 
        }

        if (pendingDent && initialIndentToken == nullptr && NEWLINE != next->getType()) {     
            assign_next(initialIndentToken, next);
        }

        
        if (next != nullptr && next->getType() == NEWLINE) {
            prev_was_endl = true;
        }

        if (next != nullptr && next->getType() == WHERE) {
            prev_was_where = true;
        }

        if (next == nullptr || HIDDEN == next->getChannel() || NEWLINE == next->getType())
            return next; 


        if (next->getType() == EOF) {
            indentCount = 0;
            if (!pendingDent) {
                assign_next(initialIndentToken, next);
            }

            // while (getSavedIndent() != indentCount) {
            //     indentStack.pop();
            //     tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
            // }

            // if (getSavedIndent() == indentCount) {
            //     tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
            // }

            // tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));


            while (indentCount != getSavedIndent()) {
                indentStack.pop();
                tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
            }

            tokenQueue.push_back(createToken(DEDENT, "DEDENT" + getSavedIndent(), st_ind));
        }

        pendingDent = true;

        tokenQueue.push_back(std::move(next));
        auto p = std::move(tokenQueue.front());
        tokenQueue.pop_front();
        
        return p; 
    }
}

fragment UPPER   : [A-Z];
fragment LOWER   : [a-z];
fragment DIGIT   : [0-9];

WHERE : 'where';

LEGIT : LOWER+;
DECIMAL : DIGIT+;

NEWLINE : ('\r'? '\n' | '\r') {
    if (pendingDent) { setChannel(HIDDEN); }
    // pendingDent = true;
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
