package lambdaTree;

import java.util.Objects;

public class LetExpression implements LambdaExpression {
    public final LambdaExpression variable;
    public final LambdaExpression variableExpr;
    public final LambdaExpression inExpr;

    public LetExpression(LambdaExpression variable, LambdaExpression variableExpr, LambdaExpression inExpr) {
        Objects.requireNonNull(variable);
        Objects.requireNonNull(variableExpr);
        Objects.requireNonNull(inExpr);

        this.variable = variable;
        this.variableExpr = variableExpr;
        this.inExpr = inExpr;
    }

    @Override
    public String toString() {
        return "(let " + variable + " = " + variableExpr + " in " + inExpr + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof LetExpression)) {
            return false;
        }
        LetExpression letExpr = (LetExpression) o;
        return this.variable.equals(letExpr.variable)
                && this.variableExpr.equals(letExpr.variableExpr)
                && this.inExpr.equals(letExpr.inExpr);
    }

    @Override
    public int hashCode() {
        return (variable.hashCode() * 31 + variableExpr.hashCode()) * 31 + inExpr.hashCode();
    }
}
