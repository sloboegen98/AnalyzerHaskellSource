ANTLR 	= java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$(CLASSPATH)" org.antlr.v4.Tool
GRUN    = java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$(CLASSPATH)" org.antlr.v4.gui.TestRig
GRAMMAR = Data
TEST 	= file.txt
ROOT	= file

all: antlr compile

antlr:
	$(ANTLR) ${GRAMMAR}".g4" -no-listener
compile:
	javac ${GRAMMAR}*.java 

grun:
	$(GRUN) $(GRAMMAR) $(ROOT) -gui $(TEST) 
