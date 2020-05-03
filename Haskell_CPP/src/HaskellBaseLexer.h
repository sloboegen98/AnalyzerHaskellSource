#pragma once

#include <list>
#include <stack>
#include <memory>
#include <utility>
#include <string>

#include "antlr4-runtime.h"

class HaskellBaseLexer : public antlr4::Lexer {
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

public:
    HaskellBaseLexer(antlr4::CharStream *input);
    bool pendingDent = true;
    // Current indent
    int indentCount = 0;
    // A queue where extra tokens are pushed on
    std::list < std::unique_ptr<antlr4::Token> > tokenQueue;
    // The stack that keeps key word and indent after that
    std::stack <std::pair <std::string, int> > indentStack;
    // Pointer keeps last indent token
    initIndent* initialIndentToken = nullptr;
    std::string last_key_word      = "";

    bool prev_was_endl       = false;
    bool prev_was_keyword    = false;
    // Need, for example, in {}-block
    bool ignore_indent       = false;
    // Check moment, when you should calculate start indent
    // module ... where {now you should remember start indent}
    bool module_start_indent = false;
    bool was_module_export   = false;
    bool in_pragmas          = false;

    // Haskell saves indent before first symbol as null indent
    int start_indent = -1;
    // Count of "active" key words in this moment
    int nested_level = 0;

    int getSavedIndent();
    std::unique_ptr <antlr4::CommonToken> createToken(int type, std::string text, int start_ind);
    void processINToken(int st_ind);
    void processEOFToken(std::unique_ptr<antlr4::Token>& next);
    void processNEWLINEToken();
    void processWSToken();
    void processTABToken();
    virtual std::unique_ptr <antlr4::Token> nextToken() override;
};