lexer grammar Lexer;

@lexer::members {

    private boolean pendingDent = true;

    private boolean prev_was_endl = false;
    private boolean prev_was_where = false;

	private int indentCount = 0;

	private java.util.LinkedList<Token> tokenQueue = new java.util.LinkedList<>();

	private java.util.Stack<Integer> indentStack = new java.util.Stack<>();

	private Token initialIndentToken = null;

	private int getSavedIndent() { return indentStack.isEmpty() ? 0 : indentStack.peek(); }

	private CommonToken createToken(int type, String text, Token next) {
		CommonToken token = new CommonToken(type, text);
		if (null != initialIndentToken) {
			token.setStartIndex(initialIndentToken.getStartIndex());
			token.setLine(initialIndentToken.getLine());
			token.setCharPositionInLine(initialIndentToken.getCharPositionInLine());
			token.setStopIndex(next.getStartIndex()-1);
		}
		return token;
    }


    @Override
    public Token nextToken() {
        if (!tokenQueue.isEmpty()) { return tokenQueue.poll(); }

        Token next = super.nextToken();

        if (pendingDent && prev_was_endl 
            && indentCount <= getSavedIndent() 
            && next.getType() != NEWLINE 
            && next.getType() != EOF 
            && next.getType() != WHERE) {

            while (indentCount < getSavedIndent()) {
                if (!indentStack.empty()) 
                    indentStack.pop();
                tokenQueue.offer(createToken(DEDENT, "DEDENT", next));
            }

            if (indentCount == getSavedIndent()) {
                tokenQueue.offer(createToken(DEDENT, "DEDENT", next));
            }

            prev_was_endl = false;
            if (indentCount == 0)
                pendingDent = false;
        }


        if (pendingDent && prev_was_endl
            && indentCount > getSavedIndent()
            && next.getType() != NEWLINE 
            && next.getType() != WS
            && next.getType() != EOF) {

            if (prev_was_where) {
                prev_was_where = false;
                indentStack.push(indentCount);
            }
            
            prev_was_endl = false; 
        }


        if (pendingDent && initialIndentToken == null && NEWLINE != next.getType()) {     
            initialIndentToken = next;
        }

        if (next != null && next.getType() == NEWLINE) {
            prev_was_endl = true;
        }

        if (next != null && next.getType() == WHERE) {
            prev_was_where = true;
        }

        if (next == null || HIDDEN == next.getChannel() || NEWLINE == next.getType())
            return next; 

        if (next.getType() == EOF) {
            indentCount = 0;
            if (!pendingDent) {
               initialIndentToken = next;
            }

            while (indentCount < getSavedIndent()) {
                if (!indentStack.empty())
                    indentStack.pop();
                tokenQueue.offer(createToken(DEDENT, "DEDENT", next));
            }

            if (indentCount == getSavedIndent())             
                tokenQueue.offer(createToken(DEDENT, "DEDENT", next));
        }

        pendingDent = true;

        tokenQueue.offer(next);
        
        return tokenQueue.poll(); 

    }
}

fragment UPPER   : [A-Z];
fragment LOWER   : [a-z];
fragment DIGIT   : [0-9];

WHERE : 'where';

LEGIT : LOWER+;
DECIMAL : DIGIT+;

NEWLINE : ('\r'? '\n' | '\r') {
    if (pendingDent) { setChannel(HIDDEN); }
    // pendingDent = true;
    indentCount = 0;
    initialIndentToken = null;
} ;

TAB : [\t]+ {
    setChannel(HIDDEN);
    if (pendingDent) {
        indentCount += 8*getText().length();
    }
} ;

WS : [ ]+ {
    setChannel(HIDDEN);
    if (pendingDent) {
        indentCount += getText().length();
    }
} ;

INDENT : 'INDENT' { setChannel(HIDDEN); };
DEDENT : 'DEDENT' { setChannel(HIDDEN); };
