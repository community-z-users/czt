/*
  Copyright (C) 2006, 2007 Mark Utting
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

/**A convenience class for printing SIMPLE terms as strings.
 * This simple printer does not handle predicates or expressions,
 * just types, names, numbers, etc.
 * It generally returns Unicode strings, but you can create it
 * so that it produces ASCII-only strings.
 * <p>
 * For more sophisticated printing of arbitrary terms, you
 * should use the SectionManager class in the session project
 * and ask it for a UnicodeString or LatexString class.
 * </p>
 * @author Petra Malik
 */
public class PrintVisitor
  extends net.sourceforge.czt.base.util.PrintVisitor
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
             TypeAnnVisitor<String>,
             ZNameVisitor<String>,
             ZNumeralVisitor<String>,
             ZStrokeListVisitor<String>,
             LocAnnVisitor<String>,
             NameTypePairVisitor<String>
{
  protected boolean printUnicode_;
  protected boolean printIds_;

  /**
   * Constructs a PrintVisitor that produces Unicode strings.
   */
  public PrintVisitor()
  {
    printUnicode_ = true;
    printIds_ = false;
  }

  public boolean setPrintIds(boolean bool)
  {
    boolean result = printIds_;
    printIds_ = bool;
    return result;
  }
  
  public boolean getPrintIds() 
  {
    return printIds_;
  }
  
  public boolean setPrintUnicode(boolean bool)
  {
    boolean result = printUnicode_;
    printUnicode_ = bool;
    return result;
  }
  
  public boolean getPrintUnicode() 
  {
    return printUnicode_;
  }

  /**
   * Constructs a PrintVisitor that produces Unicode strings
   * if the unicode parameter is true, and ASCII strings otherwise.
   * The ASCII strings produced are designed to be human-readable,
   * so are not necessarily in LaTeX markup.
   * 
   * @param unicode true means Unicode characters may appear in the output.
   */
  public PrintVisitor(boolean unicode)
  {
    printUnicode_ = unicode;
    printIds_ = false;
  }

  public String visitGenericType(GenericType genericType)
  {
    StringBuilder result = new StringBuilder();
    result.append("[");
    result.append(visit(genericType.getNameList()));
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
    return visit(triple.getName()) + " : (" + triple.getSect() + ", " +
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
    if (printUnicode_)
      return ZString.PRIME;
    else
      return "'";
  }

  public String visitNumExpr(NumExpr numExpr)
  {
    return visit(numExpr.getNumeral());
  }

  public String visitNumStroke(NumStroke numStroke)
  {
    if (printUnicode_)
      return ZString.SE + numStroke.getDigit().getValue() + ZString.NW;
    else
      return "_" + numStroke.getDigit().getValue();
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
  
  public String visitNameTypePair(NameTypePair pair)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(pair.getName()));
    result.append(" : ");
    result.append(visit(pair.getType()));
    result.append("\n");
    return result.toString();
  }

  public String visitSignature(Signature signature)
  {
    StringBuilder result = new StringBuilder();
    boolean first = true;
    for (NameTypePair pair : signature.getNameTypePair()) {
      if (! first) result.append("; ");
      result.append(visit(pair));
      first = false;
    }
    return result.toString();
  }

  public String visitTypeAnn(TypeAnn typeAnn)
  {
    return visit(typeAnn.getType());
  }
  
  public String visitZName(ZName zName)
  {
    StringBuffer result = new StringBuffer();
    if (printUnicode_) {
      result.append(zName.getWord());
    }
    else {
      ZUtils.unicodeToAscii(zName.getWord(), result);
    }
    if (printIds_) {
      result.append("_" + zName.getId());
    }
    result.append(visit(zName.getStrokeList()));
    return result.toString();
  }

  public String visitZNumeral(ZNumeral zNumeral)
  {
    return zNumeral.getValue().toString();
  }

  public String visitZStrokeList(ZStrokeList zStrokeList)
  {
    StringBuilder result = new StringBuilder();
    for (Stroke stroke : zStrokeList) {
      result.append(visit(stroke));
    }
    return result.toString();
  }

  public String visitLocAnn(LocAnn loc) {
    StringBuffer result = new StringBuffer();
    if (loc.getLine() != null &&
        loc.getLine().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append("line " + loc.getLine());
    }
    if (loc.getCol() != null &&
        loc.getCol().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append(" column " + loc.getCol());
    }
    if (loc.getStart() != null &&
        loc.getStart().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append(" start " + loc.getStart());
    }
    if (loc.getLength() != null &&
        loc.getLength().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append(" length " + loc.getLength());
    }
    if (loc.getLoc() != null) {
      result.append(" in \"" + loc.getLoc() + "\"");
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

  protected String visit(Term term)
  {
    if (term != null) return term.accept(this);
    return null;
  }
}
