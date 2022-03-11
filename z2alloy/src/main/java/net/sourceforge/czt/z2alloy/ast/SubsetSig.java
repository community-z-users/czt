package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class SubsetSig extends Sig {

  private final Sig parent;
  private final List<Field> extraFields;

  public SubsetSig(String label, Sig parent, AlloyExpr pred, boolean abs,
      boolean lone, boolean one, boolean some) {
    super(label, pred, abs, lone, one, one);
    for (Field f : parent) {
      super.addField(f);
    }
    this.parent = parent;
    extraFields = new ArrayList<Field>();
  }

  public SubsetSig(String label, Sig parent, AlloyExpr pred) {
    super(label, pred);
    for (Field f : parent) {
      super.addField(f);
    }
    this.parent = parent;
    extraFields = new ArrayList<Field>();
  }

  public SubsetSig(String label, Sig parent) {
    super(label);
    for (Field f : parent) {
      super.addField(f);
    }
    this.parent = parent;
    extraFields = new ArrayList<Field>();
  }

  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

  public Sig parent() {
    return parent;
  }

  public void addField(Field f) {
    extraFields.add(f);
    super.addField(f);
  }

  public List<Field> extraFields() {
    return Collections.unmodifiableList(extraFields);
  }
}
