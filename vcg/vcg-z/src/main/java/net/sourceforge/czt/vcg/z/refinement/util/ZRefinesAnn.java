package net.sourceforge.czt.vcg.z.refinement.util;

import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZName;


/**
 * Z Refinement annotation. It contains to names for the abstract and concrete operation names to be refined.
 *
 * @author Leo Freitas
 */
public interface ZRefinesAnn extends Ann
{

  /**
   * <p>Returns the Name elements.</p>
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * @return a list of Name elements.
   */
  net.sourceforge.czt.base.ast.ListTerm<Name> getName();

  /**
   * Returns the RefKind element.
   *
   * @return the RefKind element.
   */
  ZRefinementKind getRefKind();


  /**
   * Sets the RefKind element.
   *
   * @param refKind   the RefKind element.
   * @see #getRefKind
   */
  void setRefKind(ZRefinementKind refKind);
  Name getAbstractName();
  void setAbstractName(Name name);
  Name getConcreteName();
  void setConcreteName(Name name);

  /**
   * This is a convenience method.
   * It returns the ZName if DeclName (AbstractName) is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  ZName getZAbstractName();

  /**
   * This is a convenience method.
   * It returns the ZName if RefName (ConcreteName) is an instance of
   * ZName and throws an UnsupportedAstClassException otherwise.
   */
  ZName getZConcreteName();
}
