#pragma once

#include <vector>
#include <string>

#include "HaskellParserBaseVisitor.h"

class HaskellVisitor : public HaskellParserBaseVisitor {
    std::vector <std::string> type_notations;
public:
    std::vector <std::string> get_type_notations();
    virtual antlrcpp::Any visitGendecl(HaskellParser::GendeclContext *ctx) override;
};