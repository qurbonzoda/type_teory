package exceptions;

public class IllegalOperationException extends EvaluationException {
    public IllegalOperationException(String s) {
        super("illegal operation " + s);
    }
}
