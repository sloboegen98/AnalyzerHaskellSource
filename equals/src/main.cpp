#include <iostream>
#include <vector>
#include <string>
#include <strstream>

#include "antlr4-runtime.h"
#include "DataLexer.h"
#include "DataParser.h"

#include "printer/printer.h"

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



int main(int argc, char *argv[]) {
    std::ifstream str;
    str.open(argv[1]);
    antlr4::ANTLRInputStream input(str);
    DataLexer lexer(&input);
    antlr4::CommonTokenStream tokens(&lexer);
//
    MyParserErrorListener errorListner;

    tokens.fill();
    // Only if you want to list the tokens
    // for (auto token : tokens.getTokens()) {
    //  std::cout << token->toString() << std::endl;
    // }
    
    DataParser parser(&tokens);
    // parser.removeErrorListeners();
    // parser.addErrorListener(&errorListner);
    // try {
        antlr4::tree::ParseTree* tree = parser.module();
        std::cerr << tree->toStringTree(&parser) << std::endl;
        DotPrinter::print(tree, "tree.dot", "");

        for (auto& fname : parser.functions) {
            std::cout << fname << std::endl;
        }

    //     return 0;
    // } catch (std::invalid_argument &e) {
    //     std::cout << e.what() << std::endl;
    //     return 10;
    // }
}