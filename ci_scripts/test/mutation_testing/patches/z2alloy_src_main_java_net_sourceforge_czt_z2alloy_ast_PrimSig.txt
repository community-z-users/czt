package net.sourceforge.czt.z2alloy.ast;

public class PrimSig extends Sig {

  public PrimSig(String label, AlloyExpr pred, boolean abs, boolean lone,
      boolean one, boolean some) {
    super(label, pred, abs, lone, one, some);
  }

  public PrimSig(String label, AlloyExpr pred) {
    super(label, pred);
  }

  public PrimSig(String label) {
    super(label);
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }
}
