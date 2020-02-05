ANTLR 	= java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$(CLASSPATH)" org.antlr.v4.Tool
GRUN    = java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$(CLASSPATH)" org.antlr.v4.gui.TestRig
GRAMMAR = Haskell
TEST 	= file.txt
ROOT	= file
LIBPATH = -L/usr/local/lib
LINK 	= -lantlr4-runtime
INCLUDE = -I/usr/local/include/antlr4-runtime 

all: antlr compile

antlr:
	$(ANTLR) -Dlanguage=Cpp src/${GRAMMAR}".g4" -no-listener

compile:
	g++ src/*.cpp src/printer/*.cpp -g $(INCLUDE) $(LINK) $(LIBPATH) -std=c++17 -o parsertestexe

grun:
	$(GRUN) $(GRAMMAR) $(ROOT) -gui $(TEST) 

test: 
	./test/run.sh

clean:
	rm -rf tree.dot src/Haskell*.cpp src/Haskell*.h result/

.PHONY: all clean test
