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

import java.math.BigInteger;
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
             ZNameListVisitor<String>,
             ZNumeralVisitor<String>,
             ZStrokeListVisitor<String>,
             LocAnnVisitor<String>,
             RefExprVisitor<String>,
             NameTypePairVisitor<String>
{
  protected boolean printUnicode_;
  protected boolean printIds_;
  protected int lineOffset_;
  protected int columnOffset_;

  /**
   * Constructs a PrintVisitor that produces Unicode strings.
   */
  public PrintVisitor()
  {
    this(true);
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
    lineOffset_ = 0;
    columnOffset_ = 0;
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

  public void setOffset(int line, int column)
  {
    lineOffset_ = line;
    columnOffset_ = column;
  }

  public int getLineOffset()
  {
    return lineOffset_;
  }

  public int getColumnOffset()
  {
    return columnOffset_;
  }
  
  @Override
  public String visitZNameList(ZNameList term)
  {
    return visitList(term, ", ");
  }

  @Override
  public String visitGenericType(GenericType genericType)
  {
    StringBuilder result = new StringBuilder();
    result.append("[");
    result.append(visit(genericType.getNameList()));
    result.append("] ");
    result.append(visit(genericType.getType().get(0)));
    if (genericType.getType().size() > 1) {
      result.append(", ");
      result.append(visit(genericType.getType().get(1)));
    }
    return result.toString();
  }

  @Override
  public String visitRefExpr(RefExpr refExpr)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(refExpr.getZName()));
    if (((refExpr.getExprList() instanceof ZExprList) && !refExpr.getZExprList().isEmpty()) ||
          refExpr.getExplicit() != null && refExpr.getExplicit())
    {
      result.append("[");
      result.append(visit(refExpr.getExprList()));
      result.append("]");
    }
    return result.toString();
  }

  @Override
  public String visitGenParamType(GenParamType genParamType)
  {
    return "GENTYPE " + visit(genParamType.getName());
  }

  @Override
  public String visitGivenType(GivenType givenType)
  {
    return "GIVEN " + visit(givenType.getName());
  }

  @Override
  public String visitInStroke(InStroke inStroke)
  {
    return ZString.INSTROKE;
  }

  @Override
  public String visitNameSectTypeTriple(NameSectTypeTriple triple)
  {
    return visit(triple.getName()) + " : (" + triple.getSect() + ", " +
      visit(triple.getType()) + ")";
  }

  @Override
  public String visitNewOldPair(NewOldPair pair)
  {
    return
      visit(pair.getNewName()) +
      ZString.SPACE + ZString.SLASH + ZString.SPACE +
      visit(pair.getOldName());
  }

  @Override
  public String visitNextStroke(NextStroke nextStroke)
  {
    if (printUnicode_)
      return ZString.PRIME;
    else
      return "'";
  }

  @Override
  public String visitNumExpr(NumExpr numExpr)
  {
    return visit(numExpr.getNumeral());
  }

  @Override
  public String visitNumStroke(NumStroke numStroke)
  {
    if (printUnicode_)
      return ZString.SE + numStroke.getDigit().getValue() + ZString.NW;
    else
      return "_" + numStroke.getDigit().getValue();
  }

  @Override
  public String visitOutStroke(OutStroke outStroke)
  {
    return ZString.OUTSTROKE;
  }

  @Override
  public String visitPowerType(PowerType powerType)
  {
    return "POWER " + visit(powerType.getType());
  }

  @Override
  public String visitProdType(ProdType prodType)
  {
    StringBuilder result = new StringBuilder();
    result.append("(");
    boolean first = true;
    for (Type type : prodType.getType()) {
      if (! first) {
        result.append(ZString.SPACE);
        result.append(printUnicode_ ? ZString.CROSS : "x");
        result.append(ZString.SPACE);
      }
      result.append(visit(type));
      first = false;
    }
    result.append(")");
    return result.toString();
  }

  @Override
  public String visitSchemaType(SchemaType schemaType)
  {
    return "[" + visit(schemaType.getSignature()) + "]";
  }

  @Override
  public String visitSectTypeEnvAnn(SectTypeEnvAnn sectTypeEnvAnn)
  {
    return "SectTypeEnv [" +
      visitList(sectTypeEnvAnn.getNameSectTypeTriple(), "\n") +
      "]";
  }
  
  @Override
  public String visitNameTypePair(NameTypePair pair)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(pair.getName()));
    result.append(" : ");
    result.append(visit(pair.getType()));
    result.append("\n");
    return result.toString();
  }

  @Override
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

  @Override
  public String visitTypeAnn(TypeAnn typeAnn)
  {
    return visit(typeAnn.getType());
  }
  
  @Override
  public String visitZName(ZName zName)
  {
    StringBuffer result = new StringBuffer();
    if (printUnicode_) {
      result.append(zName.getWord());
    }
    else {
      String word = zName.getWord();
      int size = 0;
      if (word.startsWith(ZString.DELTA))
      {
        size = ZString.DELTA.length();
        result.append("Delta ");
      }
      else if(word.startsWith(ZString.XI))
      {
        size = ZString.XI.length();
        result.append("Xi ");
      }
      else if(word.startsWith(ZString.THETA))
      {
        size = ZString.XI.length();
        result.append("theta ");
      }
//      else if(word.startsWith(ZString.LAMBDA))
//      {
//        size = ZString.LAMBDA.length();
//        result.append("lambda ");
//      }
//      else if(word.startsWith(ZString.MU))
//      {
//        size = ZString.MU.length();
//        result.append("mu ");
//      }
      else if(word.startsWith(ZString.ARITHMOS))
      {
        size = ZString.ARITHMOS.length();
        result.append("ARITHMOS");
      }
      else if(word.startsWith(ZString.NAT))
      {
        size = ZString.NAT.length();
        result.append("NAT");
      }
      else if(word.startsWith(ZString.NUM))
      {
        size = ZString.NAT.length();
        result.append("INT");
      }
//      else if(word.startsWith(ZString.POWER))
//      {
//        size = ZString.POWER.length();
//        result.append("Power ");
//      }
//      else if (word.startsWith(ZString.ARG_TOK) && word.endsWith(ZString.ARG_TOK))
//      {
//        size += ZString.ARG_TOK.length();
//        result.append("_ ");
//
//        if (word.indexOf(ZString.REL.toString()) != -1)
//        {
//          size += ZString.REL.length();
//          result.append("<->");
//        }
//        else if (word.indexOf(ZString.FUN) != -1)
//        {
//          size += ZString.FUN.length();
//          result.append("-->");
//        }
//        else if (word.indexOf(ZString.NEQ) != -1)
//        {
//          size += ZString.NEQ.length();
//          result.append("!=");
//        }
//        else if (word.indexOf(ZString.NOTMEM) != -1)
//        {
//          size += ZString.NOTMEM.length();
//          result.append("!in");
//        }
//        else if (word.indexOf(ZString.EMPTYSET) != -1)
//        {
//          size += ZString.EMPTYSET.length();
//          result.append("{}");
//        }
//        else if (word.indexOf(ZString.SUBSETEQ) != -1)
//        {
//          size += ZString.SUBSETEQ.length();
//          result.append("c=");
//        }
//        else if (word.indexOf(ZString.CUP) != -1)
//        {
//          size += ZString.CUP.length();
//          result.append("CUP");
//        }
//        else if (word.indexOf(ZString.CAP) != -1)
//        {
//          size += ZString.CAP.length();
//          result.append("CAP");
//        }
//        else if (word.indexOf(ZString.SETMINUS) != -1)
//        {
//          size += ZString.SETMINUS.length();
//          result.append("\\");
//        }
//        else if (word.indexOf(ZString.SYMDIFF) != -1)
//        {
//          size += ZString.SYMDIFF.length();
//          result.append("\\-");
//        }
//        else if (word.indexOf(ZString.BIGCAP) != -1)
//        {
//          size += ZString.BIGCAP.length();
//          result.append("BCAP");
//        }
//        else if (word.indexOf(ZString.BIGCUP) != -1)
//        {
//          size += ZString.BIGCUP.length();
//          result.append("BCUP");
//        }
//        else if (word.indexOf(ZString.MAPSTO) != -1)
//        {
//          size += ZString.MAPSTO.length();
//          result.append("|->");
//        }
//        else if (word.indexOf(ZString.COMP) != -1)
//        {
//          size += ZString.COMP.length();
//          result.append(";");
//        }
//        else if (word.indexOf(ZString.CIRC) != -1)
//        {
//          size += ZString.CIRC.length();
//          result.append("o");
//        }
//        else if (word.indexOf(ZString.DRES) != -1)
//        {
//          size += ZString.DRES.length();
//          result.append("<|");
//        }
//        else if (word.indexOf(ZString.RRES) != -1)
//        {
//          size += ZString.RRES.length();
//          result.append("|>");
//        }
//        else if (word.indexOf(ZString.NDRES) != -1)
//        {
//          size += ZString.NDRES.length();
//          result.append("!<|");
//        }
//        else if (word.indexOf(ZString.NRRES) != -1)
//        {
//          size += ZString.NRRES.length();
//          result.append("!|>");
//        }
//        else if (word.indexOf(ZString.OPLUS) != -1)
//        {
//          size += ZString.OPLUS.length();
//          result.append("(+)");
//        }
//        else if (word.indexOf(ZString.PFUN) != -1)
//        {
//          size += ZString.PFUN.length();
//          result.append("-|->");
//        }
//        else if (word.indexOf(ZString.PINJ) != -1)
//        {
//          size += ZString.PINJ.length();
//          result.append(">-|->");
//        }
//        else if (word.indexOf(ZString.INJ) != -1)
//        {
//          size += ZString.INJ.length();
//          result.append(">-->");
//        }
//        else if (word.indexOf(ZString.PSURJ) != -1)
//        {
//          size += ZString.PSURJ.length();
//          result.append("-|->>");
//        }
//        else if (word.indexOf(ZString.SURJ) != -1)
//        {
//          size += ZString.SURJ.length();
//          result.append("-->>");
//        }
//        else if (word.indexOf(ZString.BIJ) != -1)
//        {
//          size += ZString.BIJ.length();
//          result.append(">-->>");
//        }
//        else if (word.indexOf(ZString.FFUN) != -1)
//        {
//          size += ZString.FFUN.length();
//          result.append("-||->");
//        }
//        else if (word.indexOf(ZString.FINJ) != -1)
//        {
//          size += ZString.FINJ.length();
//          result.append(">-||->");
//        }
//
//        if (size > ZString.ARG_TOK.length() && word.endsWith(ZString.ARG_TOK))
//        {
//          size += ZString.ARG_TOK.length();
//          result.append(" _");
//        }
//      }
      ZUtils.unicodeToAscii(word.substring(size), result);
    }
    if (printIds_) {
      result.append("_").append(zName.getId());
    }
    result.append(visit(zName.getStrokeList()));
    return result.toString();
  }

  @Override
  public String visitZNumeral(ZNumeral zNumeral)
  {
    return zNumeral.getValue().toString();
  }

  @Override
  public String visitZStrokeList(ZStrokeList zStrokeList)
  {
    StringBuilder result = new StringBuilder();
    for (Stroke stroke : zStrokeList) {
      result.append(visit(stroke));
    }
    return result.toString();
  }

  @Override
  public String visitLocAnn(LocAnn loc) {
    StringBuilder result = new StringBuilder();
    if (loc.getLine() != null &&
        loc.getLine().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append("line ").append(loc.getLine().add(BigInteger.valueOf(getLineOffset())));
    }
    if (loc.getCol() != null &&
        loc.getCol().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append(" column ").append(loc.getCol().add(BigInteger.valueOf(getColumnOffset())));
    }
    if (loc.getStart() != null &&
        loc.getStart().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append(" start ").append(loc.getStart());
    }
    if (loc.getLength() != null &&
        loc.getLength().compareTo(java.math.BigInteger.ZERO) >= 0) {
      result.append(" length ").append(loc.getLength());
    }
    if (loc.getLoc() != null) {
      result.append(" in \"").append(loc.getLoc()).append("\"");
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
        result.append(sep).append(string);
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
