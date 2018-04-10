package exceptions;

public class UnknownVariableName extends ParserException {
    public UnknownVariableName(String varName) {
        super("Illegal variable name '" + varName + "'");
    }
}
