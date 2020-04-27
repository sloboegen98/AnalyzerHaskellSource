#include "HaskellLexer.h"

using namespace antlr4;

HaskellBaseLexer::HaskellBaseLexer(CharStream *input) : Lexer(input) {}

int HaskellBaseLexer::getSavedIndent() { 
    return indentStack.empty() ? start_indent : indentStack.top().second; 
}

std::unique_ptr <antlr4::CommonToken>
HaskellBaseLexer::createToken(int type, std::string text, int start_ind) {
    auto token = std::unique_ptr<CommonToken>(new CommonToken(type, text));

    if (initialIndentToken) {
        token->setStartIndex(initialIndentToken->getStartIndex);
        token->setLine(initialIndentToken->getLine);
        token->setCharPositionInLine(initialIndentToken->getCharPositionInLine);
        token->setStopIndex(start_ind - 1);
    }
    return token;
}

void HaskellBaseLexer::processINToken(int st_ind) {
    while (!indentStack.empty() && indentStack.top().first != "let") {
        tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
        tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
        nested_level--;
        indentStack.pop();
    }

    if (!indentStack.empty() && indentStack.top().first == "let") {
        tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
        tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
        nested_level--;
        indentStack.pop();
    }
}

void HaskellBaseLexer::processEOFToken(std::unique_ptr<Token>& next) {
    indentCount = start_indent;
    if (!pendingDent) {
        assign_next(initialIndentToken, next);
    }

    int st_ind = next->getStartIndex();

    while (nested_level > indentStack.size()) {
        if (nested_level > 0)
            nested_level--;

        tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
        tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
    }

    while (indentCount < getSavedIndent()) {
        if (!indentStack.empty() && nested_level > 0) {
            indentStack.pop();
            nested_level--;
        }

        tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
        tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
    }

    if (indentCount == getSavedIndent()) {
        tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
    }

    if (was_module_export) {
        tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
    }

    start_indent = -1;
}

void HaskellBaseLexer::processWSToken() {
    setChannel(HIDDEN);
    if (pendingDent){
        indentCount += getText().length();
    }
}

void HaskellBaseLexer::processTABToken() {
    setChannel(HIDDEN);
    if (pendingDent) {
        indentCount += 8*getText().length();
    }
}

void HaskellBaseLexer::processNEWLINEToken() {
    if (pendingDent) {
        setChannel(HIDDEN);
    }

    indentCount = 0;
    initialIndentToken = nullptr;
}
 
// Algorithm's description here:
// https://www.haskell.org/onlinereport/haskell2010/haskellch10.html
// https://en.wikibooks.org/wiki/Haskell/Indentation
std::unique_ptr <antlr4::Token> HaskellBaseLexer::nextToken() {
    if (!tokenQueue.empty()) {
        auto ptr = std::move(tokenQueue.front());
        tokenQueue.pop_front();
        return ptr;
    }

    auto next = Lexer::nextToken();
    int st_ind = next->getStartIndex();
    // For debug
    // std::cout << next->toString() << std::endl;

    // if (next->getText() == "{-#") {
    //     in_pragmas = true;
    // } else if (next->getText() == "#-}") {
    //     std::cout << start_indent << std::endl;
    //     in_pragmas = false;
    // }

    if (start_indent == -1
        && next->getType() != HaskellLexer::NEWLINE
        && next->getType() != HaskellLexer::WS
        && next->getType() != HaskellLexer::TAB
        && next->getType() != HaskellLexer::OCURLY) {
        if (next->getType() == HaskellLexer::MODULE) {
            module_start_indent = true;
            was_module_export = true;
        } else if (next->getType() != HaskellLexer::MODULE && !module_start_indent) {
            start_indent = next->getCharPositionInLine();
        } else if (last_key_word == "where" && module_start_indent) {
            last_key_word = "";
            prev_was_keyword = false;
            nested_level = 0;
            module_start_indent = false;
            
            prev_was_endl = false;

            start_indent = next->getCharPositionInLine();
            tokenQueue.push_back(createToken(HaskellLexer::VOCURLY, "VOCURLY", st_ind));
            tokenQueue.push_back(createToken(next->getType(), next->getText(), st_ind));

            auto ptr = std::move(tokenQueue.front());
            tokenQueue.pop_front();
            return ptr;
        }
    }

    if (next->getType() == HaskellLexer::OCURLY) {
        if (prev_was_keyword) {
            nested_level--;
            prev_was_keyword = false;
        }

        if (module_start_indent) {
            module_start_indent = false;
            was_module_export = false;
        }

        ignore_indent = true;
        prev_was_endl = false;
    }

    if (prev_was_keyword && !prev_was_endl
        && !module_start_indent
        && next->getType() != HaskellLexer::NEWLINE
        && next->getType() != HaskellLexer::WS
        && next->getType() != HaskellLexer::TAB
        && next->getType() != HaskellLexer::OCURLY) {
        prev_was_keyword = false;
        indentStack.push({last_key_word, next->getCharPositionInLine()});
        tokenQueue.push_back(createToken(HaskellLexer::VOCURLY, "VOCURLY", st_ind));
    }

    if (ignore_indent
        && (next->getType() == HaskellLexer::WHERE
        || next->getType() == HaskellLexer::DO
        || next->getType() == HaskellLexer::MDO
        || next->getType() == HaskellLexer::LET
        || next->getType() == HaskellLexer::OF
        || next->getType() == HaskellLexer::LCASE
        || next->getType() == HaskellLexer::REC
        || next->getType() == HaskellLexer::CCURLY)
        ) {
        ignore_indent = false;
    }

    if (pendingDent
        && prev_was_keyword
        && !ignore_indent
        && indentCount <= getSavedIndent()
        && next->getType() != HaskellLexer::NEWLINE
        && next->getType() != HaskellLexer::WS) {

        tokenQueue.push_back(createToken(HaskellLexer::VOCURLY, "VOCURLY", st_ind));
        prev_was_keyword = false;
        prev_was_endl = true;
    }


    if (pendingDent && prev_was_endl
        && !ignore_indent
        && indentCount <= getSavedIndent()
        && next->getType() != HaskellLexer::NEWLINE
        && next->getType() != HaskellLexer::WS
        && next->getType() != HaskellLexer::WHERE
        && next->getType() != HaskellLexer::IN
        && next->getType() != HaskellLexer::DO
        && next->getType() != HaskellLexer::MDO
        && next->getType() != HaskellLexer::OF
        && next->getType() != HaskellLexer::LCASE
        && next->getType() != HaskellLexer::REC
        && next->getType() != HaskellLexer::CCURLY
        && next->getType() != EOF) {

        while (nested_level > indentStack.size()) {
            if (nested_level > 0)
                nested_level--;

            tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
            tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
        }

        while (indentCount < getSavedIndent()) {
            if (!indentStack.empty() && nested_level > 0) {
                indentStack.pop();
                nested_level--;
            }

            // std::cout << next->toString() << ' ' << indentCount << ' ' << getSavedIndent() << std::endl;

            tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
            tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
        }

        if (indentCount == getSavedIndent()) {
            tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
        }

        prev_was_endl = false;
        if (indentCount == start_indent)
            pendingDent = false;
    }


    if (pendingDent && prev_was_keyword
        && !module_start_indent
        && !ignore_indent
        && indentCount > getSavedIndent()
        && next->getType() != HaskellLexer::NEWLINE
        && next->getType() != HaskellLexer::WS
        && next->getType() != EOF) {

        prev_was_keyword = false;

        if (prev_was_endl) {
            indentStack.push({last_key_word, indentCount});
            prev_was_endl = false;
        }

        tokenQueue.push_back(createToken(HaskellLexer::VOCURLY, "VOCURLY", st_ind));
    }

    if (pendingDent
        && initialIndentToken == nullptr
        && HaskellLexer::NEWLINE != next->getType()) {
        assign_next(initialIndentToken, next);
    }

    if (next != nullptr && next->getType() == HaskellLexer::NEWLINE) {
        prev_was_endl = true;
    }

    if (next->getType() == HaskellLexer::WHERE
        || next->getType() == HaskellLexer::LET
        || next->getType() == HaskellLexer::DO
        || next->getType() == HaskellLexer::MDO
        || next->getType() == HaskellLexer::OF
        || next->getType() == HaskellLexer::LCASE
        || next->getType() == HaskellLexer::REC) {
        // if next will be OCURLY need to decrement nested_level
        nested_level++;
        prev_was_keyword = true;
        prev_was_endl = false;
        last_key_word = next->getText();

        if (next->getType() == HaskellLexer::WHERE) {
            if (!indentStack.empty() && (indentStack.top().first == "do" || indentStack.top().first == "mdo")) {
                tokenQueue.push_back(createToken(HaskellLexer::SEMI, "SEMI", st_ind));
                tokenQueue.push_back(createToken(HaskellLexer::VCCURLY, "VCCURLY", st_ind));
                indentStack.pop();
                nested_level--;
            }
        }
    }

    if (next != nullptr && next->getType() == HaskellLexer::OCURLY) {
        prev_was_keyword = false;
    }

    if (next == nullptr || HIDDEN == next->getChannel() || HaskellLexer::NEWLINE == next->getType())
        return next;

    if (next->getType() == HaskellLexer::IN) {
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