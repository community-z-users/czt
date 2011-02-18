/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 *
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.vcg.util;

import net.sourceforge.czt.z.ast.ZName;

/**
 * <p>
 * Kind of definition added to a definition table (see {@link DefinitionTable#Definition}).
 * Definition contain generic types and its expression. It also contain the context where
 * the definition appears as defined by this enumeration.
 * </p>
 * <p>
 * Definition table has a map from the defined name to a triple containing: given
 * generic parameters, defining expression, and a definition type (e.g., X[T] == E)
 * will have a map between ZName("X") to Def(List(T), E, AXIOM). This enumeration
 * (attempts to) summarise all possible cases.
 * </p>
 * @author Leo Freitas
 */
// We changed from DefinitionType to avoid confusion with declared/carrier type information
public class DefinitionKind {
  /*
  // used for S == E (i.e. horizontal or schemas)
  CONSTDECL,
  // used for axiomatic boxes
  VARDECL,
  // used for schema boxes from trivial (RefExpr) inclusions
  LOCALDECL,
  // used for complex schema inclusions
  INCLDECL,
   *
   */

  // Given sets are special and map to a \power~G expression
  // e.g., [G]  ==>  (ZN("G"), Def({}, Power(G), GIVENSET)
  public static final int GIVENSET_VALUE = 0;
  public static final DefinitionKind GIVENSET = new DefinitionKind(GIVENSET_VALUE);

  // Free types introduce constant and constructors
  // e.g., FT ::= c | f < E >   ==>
  //                  one for FT: (ZN("FT"), Def({}, Power(Ref(FT)) , GIVENSET) // [FT]
  //                  one for  c: (ZN("c") , Def({}, Ref(FT)        , FREETYPE) // c: FT
  //                  one for  f: (ZN("f") , Def({}, Ref({E,FT},Inj), FREETYPE) // f: E \inj FT
  public static final int FREETYPE_VALUE = 1;
  public static final DefinitionKind FREETYPE = new DefinitionKind(FREETYPE_VALUE);

  // Axioms introduce generics to variables and types; this includes horizontal axioms
  // e.g., N[X] == E       ==> (ZN("N"), Def({X}, E, AXIOM) // within \begin{zed}\end{zed}
  //       N == E          ==> (ZN("N"), Def({} , E, AXIOM) // within \begin{zed}\end{zed}
  //       [X] v: T | P    ==> (ZN("v"), Def({X}, T, AXIOM) // within \begin{gendef}\end{gendef}
  //       v: T | P        ==> (ZN("v"), Def({} , T, AXIOM) // within \begin{axdef}\end{axdef}
  public static final int AXIOM_VALUE = 2;
  public static final DefinitionKind AXIOM = new DefinitionKind(AXIOM_VALUE);

  // Schemas introduce generics to their corresponding expressions; this includes horizontal schemas
  // e.g., S[X] == SchExpr ==> (ZN("S"), Def({X}, SchExpr, SCHEMADECL) // within \begin{zed} or \begin{schema}
  //       S    == SchExpr ==> (ZN("S"), Def({} , SchExpr, SCHEMADECL) // within \begin{zed} or \begin{schema}
  public static final int SCHEMADECL_VALUE = 3;
  public static final DefinitionKind SCHEMADECL = new DefinitionKind(SCHEMADECL_VALUE);

  // Schema inclusion is the most complex. We assume the Oxford style of Z here.
  // e.g., St[T]    == [ x: \seq~T | P ]
  //       Init[T]  == [ St[T]~' | Q ]
  //       OpUpd[T] == [ \Delta St[T]; i?: I; o!: O | inv ]
  //       OpQry[T] == [ \Xi St[T]; i?: I; o!: O | inv ]
  //
  // Apart from the SCHEMA definitions for each schema above, we also add
  //          (ZN("x")          , Def({T}, \seq~T, INCLUSION(SchExpr for St)) and
  //          (ZN("x",Stroke(')), Def({T}, \seq~T, INCLUSION(SchExpr for St))
  //
  // In the case of \Delta/Xi, duplicates are ignored, given \Delta St may appear multiple times.
  //
  public static final int SCHEMABINDING_VALUE = 4;
  //public static final DefinitionKind SCHEMABINDING = new DefinitionKind(SCHEMABINDING_VALUE);

  // NOTE: With local decls within Definition, SCHEMADECL locals are inclusions references
  //
  // All bindings that are simple inclusion expressions. The common ones are:
  // RefExpr (\Delta S), DecorExpr (S'), HideExpr (S \hides (x,y)), RenameExpr (S[x/y])
  //public static final int SCHEMAINCL_VALUE = 5;
  //public static final DefinitionKind SCHEMAINCLUSION = new DefinitionKind(SCHEMAINCL_VALUE);

  // All bindings that are complex inclusion expressions.
  // Complex schema expressions are more difficult to handle, becuase their signature can vary.
  // These are either schema construction on-the-fly (1) or inclusions involving the schema calculus (2).
  // We leave these cases up to the user. In DefinitionTableVisitor, we make a bast guess by querying
  // for type information (e.g., SectTypeEnvAnn), which will have signature for such schema expressions.
  // If type information is not avilable, it will fail (e.g., it should have these, as def are to be queried
  // for well-formed specs only?)
  // e.g., S == [ (T \land R) \hide (x) | P ] (1) schema construction for inclusion
  //       A == B \land C
  //       D == [ A | P ]                     (2) schema calculus inclusion
  public static final int SCHEMAEXPR_VALUE = 5;
  //public static final DefinitionKind SCHEMAEXPR = new DefinitionKind(SCHEMAEXPR_VALUE);

  public static final int UNKNOWN_VALUE = 6; //for name below Integer.MAX_VALUE;
  public static final DefinitionKind UNKNOWN = new DefinitionKind(UNKNOWN_VALUE);

  //private final SchExpr binding_;
  private final ZName name_;
  private final int value_;
  
  private static final String[] NAMES = 
    { "GIVENSET", "FREETYPE", "AXIOM", "SCHEMADECL", "SCHEMABINDING", /*"SCHEMAINCL", */ "SCHEMAEXPR", "UNKNOWN" };

  private DefinitionKind(int v)
  {
    this(v, null/*, null*/);
  }

  private DefinitionKind(int v, ZName schName/*, SchExpr expr*/)
  {
    super();
    value_ = v;
    name_ = schName;
    //binding_ = expr;
  }

  // avoid clonning, please...
//  protected DefinitionKind(DefinitionKind copy)
//  {
//    this(copy.value_, copy.name_ == null ? copy.name_ : Definition.cloneTerm(copy.name_));
//  }

  public boolean isGlobal()
  {
                                        // TODO: should this be just isSchemaDecl()? MAYBE
    return isGivenSet() || isAxiom() || isSchemaReference();
  }

  public boolean isLocal()
  {
    return isSchemaReference() || isFreeTypeBranch();
  }

  /**
   * Schema declarations like S in S == [ D | P ] or complex schema expressions like T in S == T \land R.
   * These are to be used by global names only.
   * @return
   */
  public boolean isSchemaReference()
  {
    return isSchemaDecl() || isSchemaExpr();
  }

  public boolean hasSchemaName()
  {
    return isSchemaBinding() || isSchemaExpr();
  }

  public ZName getSchName()
  {
    if (!hasSchemaName())
    {
      throw new UnsupportedOperationException("Only schema bindings and complex schema expressions have schema name");
    }
    return name_;
  }
  
  public boolean isGivenSet()
  {
    return value_ == GIVENSET_VALUE;
  }

  public boolean isFreeTypeBranch()
  {
    return value_ == FREETYPE_VALUE;
  }
  
  public boolean isAxiom()
  {
    return value_ == AXIOM_VALUE;
  }

  public boolean isSchemaDecl()
  {
    return value_ == SCHEMADECL_VALUE;
  }

  public boolean isSchemaBinding()
  {
    return value_ == SCHEMABINDING_VALUE;
  }

  public boolean isSchemaExpr()
  {
    return value_ == SCHEMAEXPR_VALUE;
  }

  /**
   * Underlying value for a definition kind. The lower the value
   * the simples the definition.
   * @return
   */
  public int value()
  {
    return value_;
  }

  /**
   * It compares value and binding for INCLUSION type.
   * @param o
   * @return
   */
  @Override
  public boolean equals(Object o)
  {
    if (this == o)
    {
      return true;
    }

    if (!(o instanceof DefinitionKind))
    {
      return false;
    }

    DefinitionKind other = (DefinitionKind)o;
    return (other.value_ == this.value_ &&
            ((/*other.binding_ == null && this.binding_ == null &&*/
              other.name_ == null && this.name_ == null) ||
             (/*other.binding_ != null &&
              other.binding_.equals(this.binding_) &&*/
              other.name_ != null &&
              other.name_.equals(this.name_))));

  }

  /**
   * Given the fact INCLUSION elements all have same value_ yet different binding
   * could enable hash tables for this class. Yet, if one would like to consider
   * all inclusions regardless of binding, then this class wouldn't make a good hash key.
   * @return
   */
  @Override
  public int hashCode() {
    int result = this.value_;
//    if (binding_ != null)
//      result += binding_.hashCode();
    if (name_ != null)
      result += name_.hashCode();
    return result;
  }

  @Override
  public String toString()
  {
    return NAMES[value_] +
    (hasSchemaName() ?
       "(" + getSchName() /*+ "@" + Integer.toHexString(getBindingSchExpr().hashCode())*/ + ")" : "");
      // (isSchemaInclusion() ? "(" + getSchName() + ")" : ""));
  }
/*
  public static DefinitionKind getGivenSet(String sectName)
  {
    DefinitionKind result = new DefinitionKind(GIVENSET_VALUE);
    return result;
  }

  public static DefinitionKind getFreeType(String sectName)
  {
    DefinitionKind result = new DefinitionKind(FREETYPE_VALUE);
    return result;
  }

  public static DefinitionKind getAxiom(String sectName)
  {
    DefinitionKind result = new DefinitionKind(AXIOM_VALUE);
    return result;
  }

  public static DefinitionKind getSchDecl(String sectName)
  {
    DefinitionKind result = new DefinitionKind(SCHEMADECL_VALUE);
    return result;
  }
*/
  public static DefinitionKind getSchBinding(ZName name/*, SchExpr expr*/)
  {
    DefinitionKind result = new DefinitionKind(SCHEMABINDING_VALUE, name/*, expr*/);
    return result;
  }

  public static DefinitionKind getSchExpr(ZName name)
  {
    DefinitionKind result = new DefinitionKind(SCHEMAEXPR_VALUE, name);
    return result;
  }

/*
  public static DefinitionKind getSchInclusion(Name refName)
  {
    DefinitionKind result = new DefinitionKind(SCHEMAINCL_VALUE, refName, null);
    return result;
  }


  public static DefinitionKind getUnknown(String sectName)
  {
    DefinitionKind result = new DefinitionKind(UNKNOWN_VALUE);
    return result;
  }
  */
}
