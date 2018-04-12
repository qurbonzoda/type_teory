package parsers;

import exceptions.IllegalCharacterException;
import exceptions.ParserException;
import lambdaTree.*;

import java.util.Objects;

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
        LET("let"),
        LET_EQUAL("="),
        LET_IN("in"),
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
            if (currentString.equals(Token.LET.name)) {
                return Token.LET;
            }
            if (currentString.equals(Token.LET_IN.name)) {
                return Token.LET_IN;
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
        //(абстракция) ::= [(применение)] '\' (переменная) '.' (абстракция) | (применение)
        if (currentToken == Token.LAMBDA) {
            return readLambda();
        }
        LambdaExpression applicative = readApplicative();
        if (currentToken == Token.LAMBDA) {
            LambdaExpression abstraction = readLambda();
            return new Applicative(applicative, abstraction);
        }
        return applicative;
    }

    private Abstraction readLambda() throws ParserException {
        if (currentToken != Token.LAMBDA) {
            throw new ParserException("'\\' expected, got " + currentString);
        }
        currentToken = nextToken();
        LambdaExpression variable = readVariable();
        if (currentToken != Token.DOT) throw new ParserException("'.' expected, got " + currentString);
        currentToken = nextToken();
        LambdaExpression statement = readAbstraction();
        return new Abstraction(variable, statement);
    }

    private LambdaExpression readExpression() throws ParserException {
        //(выражение)  ::= 'let' (переменная) '=' (выражение) 'in' (выражение) | (абстракция)
        if (currentToken == Token.LET) {
            currentToken = nextToken();
            LambdaExpression variable = readVariable();
            if (currentToken != Token.LET_EQUAL) throw new ParserException("'=' expected, got "+ currentString);
            currentToken = nextToken();
            LambdaExpression variableExpr = readExpression();
            if (currentToken != Token.LET_IN) throw new ParserException("'in' expected, got " + currentString);
            currentToken = nextToken();
            LambdaExpression inExpr = readExpression();
            return new LetExpression(variable, variableExpr, inExpr);
        }
        return readAbstraction();
    }
}
