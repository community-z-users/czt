/*
  Copyright (C) 2005, 2006 Mark Utting
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z.util;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

public final class ZUtils
{
  /**
   * Do not create instances of this class.
   */
  private ZUtils()
  {
  }

  /**
   * Computes a list of all the NameTypePairs from the given signature
   * whose name ends with the given decoration.  If <code>decor</code>
   * is <code>null</code> a list of all undecored names with its
   * corresponding types is returned.
   */
  public static List<NameTypePair> subsignature(Signature sig, Class decor)
  {
    List result = new ArrayList<NameTypePair>();
    for (NameTypePair pair : sig.getNameTypePair()) {
      final ZName zName = pair.getZName();
      final ZStrokeList strokeList = zName.getZStrokeList();
      final int size = strokeList.size();
      if ((size == 0 && decor == null) ||
          (size > 0 && decor != null &&
           decor.isInstance(strokeList.get(strokeList.size() - 1)))) {
        result.add(pair);
      }
    }
    return result;
  }

  public static boolean isAnonymous(ZSect zSect)
  {
    final String name = zSect.getName();
    final List<Parent> parents = zSect.getParent();
    return Section.ANONYMOUS.getName().equals(name) &&
      parents.size() == 1 &&
      Section.STANDARD_TOOLKIT.getName().equals(parents.get(0).getWord());
  }

  /** Schema or generic schema definition (vertical).
   *      AxPara.Box          = SchBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = ConstDecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = SchemaName
   *      ConstDecl.expr      = SchExpr
   *
   * Axiomatic or generic definitions
   *      AxPara.Box          = AxBox
   *      AxPara.decl         = generics
   *
   *      AxPara.SchText.decl = declared variables
   *      AxPara.SchText.pred = axiomatic predicate
   *
   * Horizontal definition
   *      AxPara.Box          = OmitBox
   *      AxPara.decl         = generics
   *      AxPara.SchText.decl = Constdecl
   *      AxPara.SchText.pred = null
   *
   *      ConstDecl.dname     = HorizDefName (either SchName or AbbrvName)
   *      ConstDecl.expr      = HorizDefExpr (either SchExpr or Other)
   */
  
  /** Checks whether the given term is an AxPara */
  public static boolean isAxPara(Term term) {
      return term instanceof AxPara;
  }
  
  /** Assuming term is an AxPara casts it. A ClassCastException is raised otherwise. */
  public static AxPara asAxPara(Term term) {
      assert isAxPara(term);
      return (AxPara)term;
  }
  
  /** Checks whether the given term is an AxPara with OmixBox */
  public static boolean isHorizontalDef(Term term) {
      return (isAxPara(term) && asAxPara(term).getBox().equals(Box.OmitBox));
  }
  
  /** Checks whether the given term <code>isHorizontalDef(Term)</code> and <code>isSchema(Term)</code> */
  public static boolean isHorizontalSchema(Term term) {
      return (isHorizontalDef(term) && isSchema(term));
  }
  
  /** Checks whether the given term <code>isHorizontalDef(Term)</code> and <code>!isSchema(Term)</code> */
  public static boolean isAbbreviation(Term term) {
      return (isHorizontalDef(term) && !isSchema(term));
  }
  
  private static boolean coreBoxedAxiomaticDef(Term term) {
      return (isAxPara(term) && asAxPara(term).getBox().equals(Box.AxBox));
  }
  
  public static NameList getAxParaGenFormals(Term term) {
      return (isAxPara(term) ? asAxPara(term).getNameList() : null);
  }

  public static ZNameList getAxParaZGenFormals(Term term) {
      return term == null ? null : assertZNameList(getAxParaGenFormals(term));
  }

  /** Checks whether the given term is an AxPara with AxBox (i.e. it comes from a \begin{axdef}/AX */
  public static boolean isBoxedAxiomaticDef(Term term) {
      boolean result = coreBoxedAxiomaticDef(term);
      if (result) {
        NameList nl = getAxParaGenFormals(term);      
        result = (nl == null || ((nl instanceof ZNameList) && ((ZNameList)nl).isEmpty()));
      }
      return result;
  }
  
  /** Checks whether the given term is an AxPara with AxBox (i.e. it comes from a \begin{gendef}[...]/GENAX */
  public static boolean isBoxedGenericDef(Term term) {
      boolean result = coreBoxedAxiomaticDef(term);
      if (result) {
        ZNameList nl = getAxParaZGenFormals(term);      
        result = (nl != null && !nl.isEmpty());
      }
      return result;
  }
  
  /**
   * Returns true if the AxPara has been properly encoded as either
   * a schema box or a horizontal definition. It is useful for assertions.
   */
  public static boolean isAxParaSchemaValid(AxPara axp) {
    // ensure our understanding of the CZT encoding is right.
    return (axp.getZSchText().getPred() == null) &&
           (axp.getZSchText().getZDeclList().size() == 1) &&
           (axp.getZSchText().getZDeclList().get(0) instanceof ConstDecl);
  }
  
  /**
   * Checks whether the given paragraph is an <code>AxPara</code> term encoded 
   * as a schema or not. That is, it checks whether the term is properly encoded
   * as either a horizontal or a boxed schema.
   */
  public static boolean isSchema(Term term) 
  {
    boolean result = isAxPara(term);
    if (result) {
      AxPara axp = asAxPara(term);
      result = axp.getBox().equals(Box.SchBox);        
      // If it is not a SchBox then check for OmitBox.    
      if (!result) {
          result = axp.getBox().equals(Box.OmitBox);

          // If it is an OmitBox, check if it is a schema or not.
          if (result) {
              assert isAxParaSchemaValid(axp);
              ConstDecl cdecl = (ConstDecl)axp.getZSchText().getZDeclList().get(0);
              result = (cdecl.getExpr() instanceof SchExpr);
          }
          // Otherwise, it is an AxBox and not a schema, result = false already.
      }
      // Otherwise, it is already a schema.
    }        
    // Otherwise, it is not an AxPara, so not a schema.
    return result;
  }
  
  /**
   * If the given paragraph <code>isSchema(para)</code>, returns
   * the declared schema name. Otherwise, the method returns null.
   */
  public static Name getSchemaName(Term term)  
  {
    Name result = null;
    if (isSchema(term)) {
      AxPara axp = asAxPara(term);
      assert isAxParaSchemaValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getName();
    }
    return result;
  } 
  
  public static Expr getSchemaDefExpr(Term term)  
  {
    Expr result = null;
    if (isSchema(term)) {
      AxPara axp = asAxPara(term);
      assert isAxParaSchemaValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getExpr();
    }
    return result;
  }
  
  public static ZNameList getSchemaZGenFormals(Term term) {
      ZNameList result = null;
      if (isSchema(term)) {
          
      }
      return result;
  }
  
  public static ZBranchList assertZBranchList(Term term)
  {
    if (term instanceof ZBranchList) {
      return (ZBranchList) term;
    }
    final String message =
      "Expected a ZBranchList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZName assertZName(Term term)
  {
    if (term instanceof ZName) {
      return (ZName) term;
    }
    final String message =
      "Expected a ZName but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZNumeral assertZNumeral(Term term)
  {
    if (term instanceof ZNumeral) {
      return (ZNumeral) term;
    }
    final String message =
      "Expected a ZNumeral but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZParaList assertZParaList(Term term)
  {
    if (term instanceof ZParaList) {
      return (ZParaList) term;
    }
    final String message =
      "Expected a ZParaList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZExprList assertZExprList(Term term)
  {
    if (term instanceof ZExprList) {
      return (ZExprList) term;
    }
    final String message =
      "Expected a ZExprList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZNameList assertZNameList(Term term)
  {
    if (term instanceof ZNameList) {
      return (ZNameList) term;
    }
    final String message =
      "Expected a ZNameList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZDeclList assertZDeclList(Term term)
  {
    if (term instanceof ZDeclList) {
      return (ZDeclList) term;
    }
    final String message =
      "Expected a ZDeclList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZFreetypeList assertZFreetypeList(Term term)
  {
    if (term instanceof ZFreetypeList) {
      return (ZFreetypeList) term;
    }
    final String message =
      "Expected a ZFreetypeList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZSchText assertZSchText(Term term)
  {
    if (term instanceof ZSchText) {
      return (ZSchText) term;
    }
    final String message =
      "Expected a ZSchText but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }
  
  public static ZFactoryImpl assertZFactoryImpl(Object factory) {
    if (factory instanceof ZFactoryImpl) {
      return (ZFactoryImpl) factory;
    }
    final String message = "Expected a ZFactoryImpl but found " + 
      String.valueOf(factory);
    throw new UnsupportedAstClassException(message);    
  }
}
