package net.sourceforge.czt.z2alloy.ast;

/**
 * Represents a binary expression
 */

public final class ExprBinary extends AlloyExpr {

  /** the operator */
  private final Op op;
  /** the expression on the left */
  private final AlloyExpr left;
  /** the expression on the right */
  private final AlloyExpr right;

  /**
   * creates a new binary expression
   * 
   * @param op
   *          The operation
   * @param left
   *          The left expression
   * @param right
   *          The right expression
   */
  public ExprBinary(Op op, AlloyExpr left, AlloyExpr right) {
    super();
    this.op = op;
    this.left = left;
    this.right = right;
  }

  /** {@inheritDoc} */
  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public ExprBinary.Op op() {
    return op;
  }

  public AlloyExpr left() {
    return left;
  }

  public AlloyExpr right() {
    return right;
  }

  /** This class contains all possible binary operators. */
  public static enum Op {
    /** -&gt; */
    ARROW("->", true),
    /** -&gt;some */
    ANY_ARROW_SOME("->some", true),
    /** -&gt;one */
    ANY_ARROW_ONE("->one", true),
    /** -&gt;lone */
    ANY_ARROW_LONE("->lone", true),
    /** some-&gt; */
    SOME_ARROW_ANY("some->", true),
    /** some-&gt;some */
    SOME_ARROW_SOME("some->some", true),
    /** some-&gt;one */
    SOME_ARROW_ONE("some->one", true),
    /** some-&gt;lone */
    SOME_ARROW_LONE("some->lone", true),
    /** one-&gt; */
    ONE_ARROW_ANY("one->", true),
    /** one-&gt;some */
    ONE_ARROW_SOME("one->some", true),
    /** one-&gt;one */
    ONE_ARROW_ONE("one->one", true),
    /** one-&gt;lone */
    ONE_ARROW_LONE("one->lone", true),
    /** lone-&gt; */
    LONE_ARROW_ANY("lone->", true),
    /** lone-&gt;some */
    LONE_ARROW_SOME("lone->some", true),
    /** lone-&gt;one */
    LONE_ARROW_ONE("lone->one", true),
    /** lone-&gt;lone */
    LONE_ARROW_LONE("lone->lone", true),
    /** . */
    JOIN(".", false),
    /** &lt;: */
    DOMAIN("<:", false),
    /** :&gt; */
    RANGE(":>", false),
    /** &amp; */
    INTERSECT("&", false),
    /** ++ */
    PLUSPLUS("++", false),
    /** + */
    PLUS("+", false),
    /** - */
    MINUS("-", false),
    /** multiply */
    MUL("*", false),
    /** divide */
    DIV("/", false),
    /** remainder */
    REM("%", false),
    /** = */
    EQUALS("=", false),
    /** &lt; */
    LT("<", false),
    /** =&lt; */
    LTE("<=", false),
    /** &gt; */
    GT(">", false),
    /** &gt;= */
    GTE(">=", false),
    /** &lt;&lt; */
    SHL("<<", false),
    /** &gt;&gt; */
    SHA(">>", false),
    /** &gt;&gt;&gt; */
    SHR(">>>", false),
    /** in */
    IN("in", false),
    /** &amp;&amp; */
    AND("&&", false),
    /** || */
    OR("||", false),
    /** &lt;=&gt; */
    IFF("<=>", false),
    /** =&gt; */
    IMPLIES("=>", false),
    /** seq */
    SEQ("seq", true);

    /**
     * The constructor.
     * 
     * @param label
     *          - the label (for printing debugging messages)
     * @param isArrow
     *          - true if this operator is one of the 17 arrow operators
     */
    private Op(String label, boolean isArrow) {
      this.label = label;
      this.isArrow = isArrow;
    }

    /** The human readable label for this operator. */
    private final String label;

    public String toString() {
      return label;
    }

    /**
     * True if and only if this operator is the Cartesian product "->", a "seq"
     * multiplicity, or is a multiplicity arrow of the form "?->?".
     */
    public final boolean isArrow;
  }

  public String toString() {
    return left + " " + op + " " + right;
  }
}
