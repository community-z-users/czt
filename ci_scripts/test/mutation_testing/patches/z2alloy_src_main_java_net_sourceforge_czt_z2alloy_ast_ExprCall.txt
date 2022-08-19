package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class ExprCall extends AlloyExpr {

  /** The actual function being called; never null. */
  private final Func fun;

  /** The list of arguments to the call. */
  private final List<? extends AlloyExpr> args;

  public ExprCall(Func fun, List<? extends AlloyExpr> args) {
    super();
    this.fun = fun;
    this.args = Collections.unmodifiableList(args);
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public Func fun() {
    return fun;
  }

  public List<AlloyExpr> args() {
    List<AlloyExpr> args = new ArrayList<AlloyExpr>();
    for (AlloyExpr arg : this.args)
      args.add(arg);
    return args;
  }

  public String toString() {
    return "call" + fun.label();
  }
}
