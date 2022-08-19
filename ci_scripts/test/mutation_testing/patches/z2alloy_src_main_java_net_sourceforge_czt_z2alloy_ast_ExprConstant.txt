package net.sourceforge.czt.z2alloy.ast;

public final class ExprConstant extends AlloyExpr {

  private final Op op;

  private final int num;

  public int num() {
    return num;
  }

  public Op op() {
    return op;
  }

  private ExprConstant(Op op, int num) {
    super();
    this.op = op;
    this.num = (op == Op.NUMBER ? num : 0);
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public String toString() {
    if (op == Op.NUMBER) {
      return Integer.toString(num);
    }
    return op.toString();
  }

  public ExprConstant copy() {
    return this;
  }

  public static final AlloyExpr TRUE = new ExprConstant(Op.TRUE, 0);

  public static final AlloyExpr FALSE = new ExprConstant(Op.FALSE, 0);

  public static final AlloyExpr IDEN = new ExprConstant(Op.IDEN, 0);

  public static final AlloyExpr MIN = new ExprConstant(Op.MIN, 0);

  public static final AlloyExpr MAX = new ExprConstant(Op.MAX, 0);

  public static final AlloyExpr NEXT = new ExprConstant(Op.NEXT, 0);

  public static final AlloyExpr ZERO = new ExprConstant(Op.NUMBER, 0);

  public static final AlloyExpr ONE = new ExprConstant(Op.NUMBER, 1);

  public static AlloyExpr makeNUMBER(int n) {
    if (n == 0)
      return ZERO;
    if (n == 1)
      return ONE;
    return new ExprConstant(Op.NUMBER, n);
  }

  /** This class contains all possible constant types. */
  public enum Op {
    /** true */
    TRUE("true"),
    /** false */
    FALSE("false"),
    /** the builtin "iden" relation */
    IDEN("iden"),
    /** the minimum integer constant */
    MIN("min"),
    /** the maximum integer constant */
    MAX("max"),
    /** the "next" relation between integers */
    NEXT("next"),
    /** the emptyness relation whose type is UNIV */
    EMPTYNESS("none"),
    /** an integer constant */
    NUMBER("NUMBER");

    /** The constructor. */
    private Op(String label) {
      this.label = label;
    }

    /** The human readable label for this operator. */
    private final String label;

    public final String toString() {
      return label;
    }
  }

}
