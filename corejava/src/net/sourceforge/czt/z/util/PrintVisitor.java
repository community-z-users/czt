/*
  Copyright (C) 2006 Mark Utting
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * @author Petra Malik
 */
public class PrintVisitor
  implements GenericTypeVisitor<String>,
             GenParamTypeVisitor<String>,
             GivenTypeVisitor<String>,
             InStrokeVisitor<String>,
             NameSectTypeTripleVisitor<String>,
             NewOldPairVisitor<String>,
             NextStrokeVisitor<String>,
             NumExprVisitor<String>,
             NumStrokeVisitor<String>,
             OutStrokeVisitor<String>,
             PowerTypeVisitor<String>,
             ProdTypeVisitor<String>,
             SchemaTypeVisitor<String>,
             SectTypeEnvAnnVisitor<String>,
             SignatureVisitor<String>,
             ZDeclNameVisitor<String>,
             ZNumeralVisitor<String>,
             ZRefNameVisitor<String>
{
  protected String visit(Term term)
  {
    return term.accept(this);
  }

  public String visitGenericType(GenericType genericType)
  {
    StringBuilder result = new StringBuilder();
    result.append("[");
    result.append(visit(genericType.getName()));
    result.append("] ");
    result.append(visit(genericType.getType()));
    if (genericType.getOptionalType() != null) {
      result.append(", ");
      result.append(visit(genericType.getOptionalType()));
    }
    return result.toString();
  }

  public String visitGenParamType(GenParamType genParamType)
  {
    return "GENTYPE " + visit(genParamType.getName());
  }

  public String visitGivenType(GivenType givenType)
  {
    return "GIVEN " + visit(givenType.getName());
  }

  public String visitInStroke(InStroke inStroke)
  {
    return ZString.INSTROKE;
  }

  public String visitNameSectTypeTriple(NameSectTypeTriple triple)
  {
    return visit(triple.getDeclName()) + " : (" + triple.getSect() + ", " +
      visit(triple.getType()) + ")";
  }

  public String visitNewOldPair(NewOldPair pair)
  {
    return
      visit(pair.getNewName()) +
      ZString.SPACE + ZString.SLASH + ZString.SPACE +
      visit(pair.getOldName());
  }

  public String visitNextStroke(NextStroke nextStroke)
  {
    return ZString.PRIME;
  }

  public String visitNumExpr(NumExpr numExpr)
  {
    return visit(numExpr.getNumeral());
  }

  public String visitNumStroke(NumStroke numStroke)
  {
    return ZString.SE + numStroke.getDigit() + ZString.NW;
  }

  public String visitOutStroke(OutStroke outStroke)
  {
    return ZString.OUTSTROKE;
  }

  public String visitPowerType(PowerType powerType)
  {
    return "POWER " + visit(powerType.getType());
  }

  public String visitProdType(ProdType prodType)
  {
    StringBuilder result = new StringBuilder();
    result.append("(");
    boolean first = true;
    for (Type type : prodType.getType()) {
      if (! first) {
        result.append(ZString.SPACE + ZString.CROSS + ZString.SPACE);
      }
      result.append(visit(type));
      first = false;
    }
    result.append(")");
    return result.toString();
  }

  public String visitSchemaType(SchemaType schemaType)
  {
    return "[" + visit(schemaType.getSignature()) + "]";
  }

  public String visitSectTypeEnvAnn(SectTypeEnvAnn sectTypeEnvAnn)
  {
    return "SectTypeEnv [" +
      visitList(sectTypeEnvAnn.getNameSectTypeTriple(), "\n") +
      "]";
  }

  public String visitSignature(Signature signature)
  {
    StringBuilder result = new StringBuilder();
    boolean first = true;
    for (NameTypePair pair : signature.getNameTypePair()) {
      if (! first) result.append("; ");
      result.append(visit(pair.getDeclName()));
      result.append(" : ");
      result.append(visit(pair.getType()));
      first = false;
    }
    return result.toString();
  }

  public String visitZDeclName(ZDeclName zDeclName)
  {
    StringBuilder result = new StringBuilder();
    result.append(zDeclName.getWord());
    for (Stroke stroke : zDeclName.getStroke()) {
      result.append(visit(stroke));
    }
    return result.toString();
  }

  public String visitZNumeral(ZNumeral zNumeral)
  {
    return zNumeral.getValue().toString();
  }

  public String visitZRefName(ZRefName zRefName)
  {
    StringBuilder result = new StringBuilder();
    result.append(zRefName.getWord());
    for (Stroke stroke : zRefName.getStroke()) {
      result.append(visit(stroke));
    }
    return result.toString();
  }

  protected String visitList(List<? extends Term> list, String separator)
  {
    final StringBuilder result = new StringBuilder();
    String sep = "";
    for (Term term : list) {
      String string = visit(term);
      if (string != null) {
        result.append(sep + string);
        sep = separator;
      }
    }
    return result.toString();
  }

  /**
   * No spaces are added.
   *
   * @param first if printed first if the list is not empty
   * @param last is printed last if the list is not empty
   * @return the (non-null) string representation of the given list
   */
  protected String visitList(List<? extends Term> list,
                             String first,
                             String separator,
                             String last)
  {
    if (list.size() > 0) {
      return first + visitList(list, separator) + last;
    }
    return "";
  }
}
