package parsers;

import exceptions.IllegalCharacterException;
import exceptions.ParserException;
import lambdaTree.Abstraction;
import lambdaTree.Applicative;
import lambdaTree.LambdaExpression;
import lambdaTree.LambdaVariable;

public class LambdaParser {
    private String expression;
    private int position;

    private Token currentToken;
    private String currentString;

    public LambdaExpression parse(String string) throws ParserException {
        expression = string;
        position = 0;
        currentToken = nextToken();
        return readExpression();
    }

    private boolean isDigit(char c) {
        return Character.isDigit(c);
    }

    private boolean isLowerLetter(char c) {
        return Character.isLowerCase(c);
    }

    private boolean isUpperLetter(char c) {
        return Character.isUpperCase(c);
    }

    private enum Token {

        LBRACE("("),
        RBRACE(")"),
        LAMBDA("\\"),
        DOT("."),
        LOWER_LETTER("low"),
        UPPER_LETTER("high"),
        COMMA(","),
        EQUALS("::="),
        SINGLE_QUOTE("\'"),
        END("eof");

        private final String name;

        Token(String name) {
            this.name = name;
        }

        public String getName() {
            return name;
        }
    }

    private Token nextToken() throws IllegalCharacterException {
        while (Character.isWhitespace(currentChar())) {
            position++;
        }
        if (position >= expression.length()) {
            return Token.END;
        }
        char oldChar = currentChar();
        position++;
        for (Token token : Token.values()) {
            if (token.getName().equals(Character.toString(oldChar))) {
                return token;
            }
        }
        if (isLowerLetter(oldChar)) {
            currentString = String.valueOf(oldChar);
            while (isLowerLetter(currentChar()) || isDigit(currentChar())) {
                currentString += currentChar();
                position++;
            }
            return Token.LOWER_LETTER;
        }
        if (isUpperLetter(oldChar)) {
            currentString = String.valueOf(oldChar);
            while (isUpperLetter(currentChar()) || isDigit(currentChar())) {
                currentString += currentChar();
                position++;
            }
            return Token.UPPER_LETTER;
        }
        throw new IllegalCharacterException(position);
    }

    private char currentChar() {
        //$ - impossible symbol in parsing
        return position >= expression.length() ? '$' : expression.charAt(position);
    }

    private LambdaExpression readVariable() throws ParserException {
        //Переменная = ('a'..'z'){'a'...'z'| '0'..'9' | \'}*
        if (currentToken != Token.LOWER_LETTER) {
            throw new IllegalCharacterException(position);
        }
        String varName = currentString;
        currentToken = nextToken();
        return new LambdaVariable(varName);
    }

    private LambdaExpression readAtom() throws ParserException {
        //(атом) = '(' (выражение) ')' | (Переменная)
        if (currentToken == Token.LBRACE) {
            currentToken = nextToken();
            LambdaExpression result = readExpression();
            if (currentToken != Token.RBRACE) {
                throw new ParserException(") expected but found " + currentString);
            }
            currentToken = nextToken();
            return result;
        }
        return readVariable();
    }

    private LambdaExpression readApplicative() throws ParserException {
        //(применение) ::= (применение) (атом) | (атом)
        LambdaExpression result = readAtom();
        while (currentToken == Token.LOWER_LETTER || currentToken == Token.LBRACE) {
            LambdaExpression nextAtom = readAtom();
            result = new Applicative(result, nextAtom);
        }
        return result;
    }

    private LambdaExpression readAbstraction() throws ParserException {
        //(абстракция) ::= (переменная) '.' (Выражение)
        LambdaExpression variable = readVariable();
        if (currentToken != Token.DOT) {
            throw new ParserException("Expected dot '.' but found " + currentString);
        }
        currentToken = nextToken();
        LambdaExpression expression = readExpression();
        return new Abstraction(variable, expression);
    }

    private LambdaExpression readExpression() throws ParserException {
        //(выражение)  ::= [(применение)] '\' (абстракция) | (применение)
        if (currentToken == Token.LAMBDA) {
            currentToken = nextToken();
            return readAbstraction();
        }
        LambdaExpression result = readApplicative();
        if (currentToken == Token.LAMBDA) {
            currentToken = nextToken();
            LambdaExpression abstraction = readAbstraction();
            result = new Applicative(result, abstraction);
        }
        return result;
    }
}
