#include <vector>
#include <string>
#include <cstdint>
#include <ostream>

#include "printer.h"

uint32_t DotPrinter::printNode(ParseTree *node, std::ostream &ost, uint32_t id) {
    std::string node_name = "op" + std::to_string(id);
    ost << node_name << "[shape=box, label = \"" << node->toStringTree() << "\"];\n";

    uint32_t cur_id = id + 1;
    for(auto child : node->children) {
        uint32_t new_id = printNode(child, ost, cur_id);
        ost << node_name + " -> " + "op" + std::to_string(cur_id) + ";\n";
        cur_id = new_id;
    }

    return cur_id;
}

void DotPrinter::print(ParseTree *node, std::string file, std::string test_case) {
    std::ofstream os(file, std::ofstream::out | std::ofstream::app);
    print(node, os, test_case);
}

void DotPrinter::print(ParseTree *node, std::ostream &ost, std::string test_case) {
    static uint32_t qid = 0;
    ost << "digraph q" << std::to_string(qid) << "{label=\""
        << test_case + "\";\nlabelloc=top;\nlabeljust=left;\n";
    printNode(node, ost, 0);
    ost << "}\n";
    ++qid;
}