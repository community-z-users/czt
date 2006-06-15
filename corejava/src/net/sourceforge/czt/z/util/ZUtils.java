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

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.z.ast.*;

public final class ZUtils
{
  /**
   * Do not create instances of this class.
   */
  private ZUtils()
  {
  }

  public static boolean isAnonymous(ZSect zSect)
  {
    final String name = zSect.getName();
    final List<Parent> parents = zSect.getParent();
    return Section.ANONYMOUS.getName().equals(name) &&
      parents.size() == 1 &&
      Section.STANDARD_TOOLKIT.getName().equals(parents.get(0).getWord());
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
  public static boolean isSchema(Para p) 
  {
    boolean result = (p instanceof AxPara);
    if (result) {
      AxPara axp = (AxPara)p;
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
  public static DeclName getSchemaName(Para para)  
  {
    DeclName result = null;
    if (isSchema(para)) {
      AxPara axp = (AxPara)para;
      assert isAxParaSchemaValid(axp);
      result = ((ConstDecl)axp.getZSchText().getZDeclList().get(0)).getDeclName();
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

  public static ZDeclName assertZDeclName(Term term)
  {
    if (term instanceof ZDeclName) {
      return (ZDeclName) term;
    }
    final String message =
      "Expected a ZDeclName but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static ZRefName assertZRefName(Term term)
  {
    if (term instanceof ZRefName) {
      return (ZRefName) term;
    }
    final String message =
      "Expected a ZRefName but found " + String.valueOf(term);
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

  public static ZDeclNameList assertZDeclNameList(Term term)
  {
    if (term instanceof ZDeclNameList) {
      return (ZDeclNameList) term;
    }
    final String message =
      "Expected a ZDeclNameList but found " + String.valueOf(term);
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

  public static ZRefNameList assertZRefNameList(Term term)
  {
    if (term instanceof ZRefNameList) {
      return (ZRefNameList) term;
    }
    final String message =
      "Expected a ZRefNameList but found " + String.valueOf(term);
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
}
