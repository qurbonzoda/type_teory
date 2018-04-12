package hmType;

public class ForallType implements HMType {
    public final VariableType variable;
    public final HMType statement;

    public ForallType(VariableType variable, HMType statement) {
        this.variable = variable;
        this.statement = statement;
    }

    @Override
    public String toString() {
        return "(" + "forall " + variable.toString() + "." + statement.toString() + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof ForallType)) {
            return false;
        }
        ForallType oForall = (ForallType) o;
        return this.variable.equals(oForall.variable)
                && this.statement.equals(oForall.statement);
    }

    @Override
    public int hashCode() {
        return variable.hashCode() * 31 + statement.hashCode();
    }
}
