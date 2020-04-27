ANTLR 	= java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$(CLASSPATH)" org.antlr.v4.Tool
GRUN    = java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$(CLASSPATH)" org.antlr.v4.gui.TestRig
LEXER   = HaskellLexer
PARSER  = HaskellParser
TEST 	= file.txt
ROOT	= module
LIBPATH = -L/usr/local/lib
LINK 	= -lantlr4-runtime
INCLUDE = -I/usr/local/include/antlr4-runtime 

all: antlr compile

antlr: lexer parser

lexer:
	$(ANTLR) -Dlanguage=Cpp src/${LEXER}".g4" -no-listener

parser:
	$(ANTLR) -Dlanguage=Cpp src/${PARSER}".g4" -no-listener

# compile:
# 	g++ src/*.cpp -g $(INCLUDE) $(LINK) $(LIBPATH) -std=c++17 -o parsertestexe

compile:
	g++ src/*.cpp -g $(INCLUDE) $(LINK) $(LIBPATH) -std=c++17 -o parsertestexe

grun:
	$(GRUN) $(GRAMMAR) $(ROOT) -gui $(TEST) 

test: 
	./test/run.sh

clean:
	rm -rf src/HaskellLexer.cpp src/HaskellLexer.h src/HaskellParser.cpp src/HaskellParser.h src/*.tokens src/*.interp result/

.PHONY: all clean test
