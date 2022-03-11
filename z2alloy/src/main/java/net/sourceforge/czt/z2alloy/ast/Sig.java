package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

public abstract class Sig extends AlloyExpr implements Iterable<Field> {

  public static final PrimSig UNIV = new PrimSig("univ");

  public static final PrimSig SIGINT = new PrimSig("Int");

  public static final PrimSig SEQIDX = new PrimSig("seq/Int");

  public static final PrimSig NONE = new PrimSig("none");

  private final boolean isAbstract;
  private final boolean isLone;
  private final boolean isOne;
  private final boolean isSome;

  private final String label;
  private AlloyExpr pred;

  private final List<Field> fields;

  public Sig(String label, AlloyExpr pred, boolean abs, boolean lone, boolean one,
      boolean some) {
    if (lone && one)
      throw new IllegalArgumentException("Cannot be both lone and one");
    if (lone && some)
      throw new IllegalArgumentException("Cannot be both lone and some");
    if (one && some)
      throw new IllegalArgumentException("Cannot be both one and some");
    this.isAbstract = abs;
    this.isLone = lone;
    this.isOne = one;
    this.isSome = some;
    this.label = label;
    this.pred = pred == null ? ExprConstant.TRUE : pred;
    this.fields = new ArrayList<Field>();
  }

  public Sig(String label, AlloyExpr pred) {
    this(label, pred, false, false, false, false);
  }

  public Sig(String label) {
    this(label, ExprConstant.TRUE);
  }

  public void addField(Field field) {
    fields.add(field);
  }

  public Iterator<Field> iterator() {
    return fields.iterator();
  }

  public List<Field> fields() {
    return Collections.unmodifiableList(fields);
  }

  public Field field(String label) {
    for (Field f : fields) {
      if (f.label().equals(label)) {
        return f;
      }
    }
    return null;
  }

  public boolean containsField(String label) {
    return field(label) != null;
  }

  public void addPred(AlloyExpr pred) {
    if (this.pred == ExprConstant.TRUE) {
      this.pred = pred;
    } else {
      this.pred.and(pred);
    }
  }

  public AlloyExpr pred() {
    return this.pred;
  }

  public String label() {
    return label;
  }

  public boolean isAbstract() {
    return isAbstract;
  }

  public boolean isOne() {
    return isOne;
  }

  public boolean isSome() {
    return isSome;
  }

  public boolean isLone() {
    return isLone;
  }

  public String toString() {
    return label;
  }
}
