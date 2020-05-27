#include <iostream>
#include <vector>
#include <string>
#include <strstream>

#include "antlr4-runtime.h"
#include "HaskellLexer.h"
#include "HaskellParser.h"

class MyParserErrorListener: public antlr4::BaseErrorListener {
  virtual void syntaxError(
      antlr4::Recognizer *recognizer,
      antlr4::Token *offendingSymbol,
      size_t line,
      size_t charPositionInLine,
      const std::string &msg,
      std::exception_ptr e) override {
    std::ostrstream s;
    s << "Line(" << line << ":" << charPositionInLine << ") Error(" << msg << ")";
    throw std::invalid_argument(s.str());
  }
};


// #define VISITOR

int main(int argc, char *argv[]) {
    std::ifstream str;
    str.open(argv[1]);
    antlr4::ANTLRInputStream input(str);
    HaskellLexer lexer(&input);
    antlr4::CommonTokenStream tokens(&lexer);
    tokens.fill();
    HaskellParser parser(&tokens);

    antlr4::tree::ParseTree* tree = parser.module();
    
    std::cout << tree->toStringTree(&parser) << std::endl;

    return 0;
}