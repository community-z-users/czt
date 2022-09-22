package net.sourceforge.czt.z2alloy.ast;

/**
 * An enum is a special signature declaration. It has the form:
 * <pre>enumDecl ::= "enum" name "{" name  ("," name)*  "}"</pre>
 * 
 * This is the same as:
 * <pre>
 * abstract sig name{}
 * one name1, ..., namen extends name {}
 * </pre>
 * 
 * In particular, none of the sigs can have any fields, and the predicate is always true
 */

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Enum extends Sig {
  /** the parent signature. No fields/predicates can be added to this */
  private final PrimSig parent;
  /** the children signatures. No fields/predicates can be added to any of these */
  private final List<SubSig> children;

  /**
   * Creates a new enum of a parent, and a list of children with given names
   * 
   * @param parent
   *          The name of the parent
   * @param children
   *          The names of the children, in the given
   */
  public Enum(String parent, List<String> children) {
    super(parent);
    this.parent = new EnumParent(parent);
    List<SubSig> childrenTemp = new ArrayList<SubSig>();
    for (String child : children) {
      childrenTemp.add(new EnumChild(child, this.parent));
    }
    this.children = Collections.unmodifiableList(childrenTemp);
  }

  public PrimSig parent() {
    return parent;
  }

  public List<SubSig> children() {
    return Collections.unmodifiableList(children);
  }

  public void addField(Field f) {
  }

  public void addPred(AlloyExpr e) {
  }

  /**
   * Represents an EnumParent This is the same as a PrimSig, except the
   * predicate is always true, and trying to add a field does nothing.
   */
  private class EnumParent extends PrimSig {
    private EnumParent(String label) {
      super(label);
    }

    public void addField(Field f) {
    }

    public void addPred(AlloyExpr e) {
    }

  }

  /**
   * Represents an EnumChild. This is the same as a SubSig, except the predicate
   * is always true, and trying to add a field does nothing.
   */
  private class EnumChild extends SubSig {
    private EnumChild(String label, PrimSig parent) {
      super(label, parent);
    }

    public void addField(Field f) {
    }

    public void addPred(AlloyExpr e) {
    }
  }

  public String toString() {
    return "enum" + parent.label();

  }

  @Override
  public <T> T accept(VisitReturn<T> visitor) {
    return visitor.visit(this);
  }

}
