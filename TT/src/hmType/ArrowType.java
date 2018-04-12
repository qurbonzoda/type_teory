package hmType;

public class ArrowType implements HMType {
    public final HMType left;
    public final HMType right;

    public ArrowType(HMType left, HMType right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return "(" + left.toString() + " -> " + right.toString() + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof ArrowType)) {
            return false;
        }
        ArrowType oArrow = (ArrowType) o;
        return this.left.equals(oArrow.left)
                && this.right.equals(oArrow.right);
    }

    @Override
    public int hashCode() {
        return left.hashCode() * 31 + right.hashCode();
    }
}
