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

import java.util.Collections;
import java.util.Iterator;
import java.util.SortedMap;
import java.util.TreeMap;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * This defines a definition, including its name.
 * That is, for the generic definition g[T,U] = T \fun U,
 * this Definition records the type parameters T,U,
 * the right hand side expression, the name, and the kind
 * of definition it is given the context where it appeared.
 * If types are available, a carrier set is also attached; it's null otherwise.
 *
 * @authot Leo Freitas
 */
public class Definition extends InfoTable.Info
{

  private final ZName defName_;
  private final DefinitionKind defKind_;
  private final ZNameList genericParams_;
  private final Expr definition_;
  private final Type2 carrierSet_;
  private final SortedMap<ZName, Definition> locals_;

  protected Definition(String sectName, ZName defName, 
          ZNameList generic, Expr definition, Type2 carrierSet,
          DefinitionKind definitionKind)
  {
    super(sectName);
    assert generic != null && defName != null && definition != null && definitionKind != null;
    genericParams_ = generic;
    defName_ = defName;
    definition_ = definition;
    defKind_ = definitionKind;
    carrierSet_ = carrierSet; // type maybe null
    locals_ = new TreeMap<ZName, Definition>(ZUtils.ZNAME_COMPARATOR);
  }

  public SortedMap<ZName, Definition> getLocalDecls()
  {
    return Collections.unmodifiableSortedMap(locals_);
  }

  protected Definition addLocalDecl(ZName defName,
          ZNameList generic, Expr definition, Type2 carrierSet,
          DefinitionKind definitionKind) throws DefinitionException
  {
    Definition localDef = new Definition(getSectionName(), defName,
            generic, definition, carrierSet, definitionKind);
    addLocalDecl(localDef);
    return localDef;
  }

  protected void addLocalDecl(Definition def) throws DefinitionException
  {
    ZName defName = def.getDefName();
    Definition oldLocalDef = locals_.put(defName, def);
    if (oldLocalDef != null)
    {
      final String message = "Duplicated local def \"" + DefinitionTable.printName(defName) +
              "\" of \"" + DefinitionTable.printName(defName_) + "\" in section " + getSectionName();
      throw new DefinitionException(message);
    }
  }

  /** Returns the list of generic type parameters of this definition.
   *  It never returns null, so if the definition has no generic
   *  parameters, it returns an empty list.
   * @return List of the names of any type parameters.
   */
  public ZNameList getDeclNames()
  {
    return genericParams_;
  }

  /** For an equality definition (name==expr), this returns the
   *  right-hand side of the definition, expr.
   *  For a variable declaration (name:expr), this returns the type
   *  expression, expr.  Note that this is often more specific than
   *  the carrier set of name (as returned by the typechecker).
   * @return
   */
  public Expr getExpr()
  {
    return definition_;
  }

  /** Tells you whether this name was declared via a constant
   * definition, or a variable declaration.
   * @return
   */
  public DefinitionKind getDefinitionKind()
  {
    return defKind_;
  }

  /**
   * Carrier set, if available; null otherwise.
   * @return
   */
  public Type2 getCarrierSet()
  {
    return carrierSet_;
  }

  public ZName getDefName()
  {
    return defName_;
  }

  protected String printLocals(boolean simple)
  {
    StringBuilder buffer = new StringBuilder(locals_.size()+1 * 20);
    buffer.append("Locals = {");
    if (!locals_.isEmpty())
    {
      Iterator<SortedMap.Entry<ZName, Definition>> itE = locals_.entrySet().iterator();
      buffer.append(" ");
       while (itE.hasNext())
       {
         SortedMap.Entry<ZName, Definition> entry2 = itE.next();
         buffer.append(DefinitionTable.printName(entry2.getKey()));
         buffer.append("=");
         buffer.append(entry2.getValue().toString(simple));
         if (itE.hasNext())
               buffer.append(", ");
       }
    }
    buffer.append("}");
    return buffer.toString();
  }

  // Add \n\t here since it is likely to appear from within a DefTable.
  @Override
  public String toString()
  {
    return definition_.toString() + 
           "\n\t\t\t DEFNAME = " + DefinitionTable.printName(defName_) +
            "\n\t\t\t " + (genericParams_.isEmpty() ? "" :
                 "GENERICS= " + genericParams_.toString() +
      "\n\t\t\t ") + "KIND    = " + defKind_.toString() +
                      (carrierSet_ == null ? "" :
            "\n\t\t\t CARSET  = " + carrierSet_.toString().replaceAll("\n;","; ").replaceAll("\n]", "] ")) +
                      (locals_.isEmpty() ? "" :
            "\n\t\t\t LOCALS  = \n\t\t\t\t   " + locals_.toString().replaceAll("\n\t\t\t", "\n\t\t\t\t").replaceAll("}", "}\n\t\t"));
  }

  public String toString(boolean simple)
  {
    if (simple)
    {
      return (genericParams_.isEmpty() ? "" : " [" + genericParams_.toString() + "]") + defKind_.toString() +
             //"(" + DefinitionTable.printName(defName_) + ", " +
                    //+ ")"
                   (!locals_.isEmpty() ? "\t" + printLocals(simple) : "");
    }
    else
      return toString();
  }

  @Override
  public boolean equals(Object o)
  {
    boolean result = o == this;
    if (!result && o instanceof Definition)
    {
      Definition d = (Definition) o;
      result = this.getSectionName().equals(d.getSectionName()) &&
              this.defName_.equals(d.defName_) &&
              this.defKind_.equals(d.defKind_) &&
              this.genericParams_.equals(d.genericParams_) &&
              this.locals_.equals(d.locals_);
    }
    return result;
  }

  @Override
  public int hashCode()
  {
    int hash = 31;
    hash = 29 * hash + this.getSectionName().hashCode();
    hash = 29 * hash + this.defName_.hashCode();
    hash = 29 * hash + this.defKind_.hashCode();
    hash = 29 * hash + this.genericParams_.hashCode();
    hash = 29 * hash + this.locals_.hashCode();
    return hash;
  }
}
