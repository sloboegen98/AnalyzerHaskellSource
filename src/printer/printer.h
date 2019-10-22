#pragma once 

#include <string>
#include <cstdint>
#include <ostream>

#include "antlr4-runtime.h"
#include "../DataLexer.h"
#include "../DataParser.h"

using antlr4::tree::ParseTree;

class DotPrinter {
public:
    static uint32_t printNode(ParseTree *node, std::ostream &ost, uint32_t id);

    static void print(ParseTree *node, std::string file, std::string test_case);
    static void print(ParseTree *node, std::ostream &ost, std::string test_case);
};

