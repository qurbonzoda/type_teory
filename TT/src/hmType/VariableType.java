package hmType;

public class VariableType implements HMType {
    public final String name;

    public VariableType(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof VariableType)) {
            return false;
        }
        VariableType oVar = (VariableType) o;
        return this.name.equals(oVar.name);

    }

    @Override
    public int hashCode() {
        return this.name.hashCode();
    }
}
