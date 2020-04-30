#include "HaskellVisitor.h"

antlrcpp::Any HaskellVisitor::visitGendecl(HaskellParser::GendeclContext *ctx) {
    if (ctx->sig_vars() != nullptr) {
        type_notations.push_back(ctx->getText());
    }
    
    return visitChildren(ctx);
}

std::vector<std::string> HaskellVisitor::get_type_notations() {
    return type_notations;
}