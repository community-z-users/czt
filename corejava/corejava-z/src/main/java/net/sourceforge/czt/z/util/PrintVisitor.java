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
  extends net.sourceforge.czt.base.util.BasePrintVisitor
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
             //SectWarningEnvAnnVisitor<String>,
             SignatureVisitor<String>,
             TypeAnnVisitor<String>,
             ZNameVisitor<String>,
             ZNameListVisitor<String>,
             ZNumeralVisitor<String>,
             ZStrokeListVisitor<String>,
             LocAnnVisitor<String>,
             RefExprVisitor<String>,
             PowerExprVisitor<String>,
             ApplExprVisitor<String>,
             TupleExprVisitor<String>,
             ZExprListVisitor<String>,
             ParentVisitor<String>,
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
    return visitList(term, ",");
  }

  @Override
  public String visitParent(Parent term)
  {
	  return term.getWord();
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
      result.append(",");
      result.append(visit(genericType.getType().get(1)));
    }
    return result.toString();
  }

  @Override
  public String visitPowerExpr(PowerExpr pexr)
  {
    return "POWER " + visit(pexr.getExpr());
  }

  @Override
  public String visitApplExpr(ApplExpr expr)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(expr.getLeftExpr()));
    result.append(visit(expr.getRightExpr()));
    return result.toString();
  }

  @Override
  public String visitTupleExpr(TupleExpr expr)
  {
    StringBuilder result = new StringBuilder();
    result.append("(");
    result.append(expr.getExprList());
    result.append(")");
    return result.toString();
  }

  @Override
  public String visitZExprList(ZExprList zlist)
  {
    return visitList(zlist, ",");
//    Iterator<Expr> it = zlist.iterator();
//    if (it.hasNext())
//      result.append(visit(it.next()));
//    while (it.hasNext())
//    {
//      result.append(",");
//      result.append(visit(it.next()));
//    }
//    return result.toString();
  }

  @Override
  public String visitRefExpr(RefExpr refExpr)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(refExpr.getName()));
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
    return visit(triple.getName()) + " : (" + triple.getSect() + "," +
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
  
//  @Override
//  public String visitSectWarningEnvAnn(SectWarningEnvAnn sectWarningEnvAnn)
//  {
//    return "SectWarningEnv [" +
//      visitList(sectWarningEnvAnn.getElements(), "\n") +
//      "]";
//  }

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
    else
    {
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
      else if(word.startsWith(ZString.POWER))
      {
        size = ZString.POWER.length();
        result.append("Power ");
      }
      else if(word.startsWith(ZString.FINSET))
      {
        size = ZString.FINSET.length();
        result.append("Finset ");
      }
      else if(word.startsWith(ZString.BIGCUP))
      {
        size = ZString.BIGCUP.length();
        result.append("BCUP ");
      }
      else if(word.startsWith(ZString.NEG))
      {
        size = ZString.NEG.length();
        result.append("- ");
      }
      else if(word.startsWith(ZString.BIGCAP))
      {
        size = ZString.BIGCAP.length();
        result.append("BCAP ");
      }
      else if(word.startsWith(ZString.TILDE))
      {
        size = ZString.TILDE.length();
        result.append(" INV");
      }
      else if(word.startsWith(ZString.NUMBER))
      {
        size = ZString.NUMBER.length();
        result.append("# ");
      }
      else if (word.startsWith(ZString.ARG_TOK) && word.endsWith(ZString.ARG_TOK))
      {
        String op = null;
        if (word.indexOf(ZString.PLUS) != -1)
        {
          size = ZString.PLUS.length();
          op = "+";
        }
        else if(word.indexOf(ZString.REL) != -1)
        {
          size = ZString.REL.length();
          op = "<->";
        }
        else if (word.indexOf(ZString.FUN) != -1)
        {
          size = ZString.FUN.length();
          op = "-->";
        }
        else if (word.indexOf(ZString.NEQ) != -1)
        {
          size = ZString.NEQ.length();
          op = "!=";
        }
        else if (word.indexOf(ZString.NOTMEM) != -1)
        {
          size = ZString.NOTMEM.length();
          op = "!in";
        }
        else if (word.indexOf(ZString.EMPTYSET) != -1)
        {
          size = ZString.EMPTYSET.length();
          op = "{}";
        }
        else if (word.indexOf(ZString.SUBSETEQ) != -1)
        {
          size = ZString.SUBSETEQ.length();
          op = "c=";
        }
        else if(word.indexOf(ZString.SUBSET) != -1)
        {
          size = ZString.SUBSET.length();
          op = "c";
        }
        else if (word.indexOf(ZString.CUP) != -1)
        {
          size = ZString.CUP.length();
          op = "CUP";
        }
        else if (word.indexOf(ZString.CAP) != -1)
        {
          size = ZString.CAP.length();
          op = "CAP";
        }
        else if (word.indexOf(ZString.SETMINUS) != -1)
        {
          size = ZString.SETMINUS.length();
          op = "\\";
        }
        else if (word.indexOf(ZString.SYMDIFF) != -1)
        {
          size = ZString.SYMDIFF.length();
          op = "(-)";
        }
        else if (word.indexOf(ZString.MAPSTO) != -1)
        {
          size = ZString.MAPSTO.length();
          op = "|->";
        }
        else if (word.indexOf(ZString.COMP) != -1)
        {
          size = ZString.COMP.length();
          op = ";";
        }
        else if (word.indexOf(ZString.CIRC) != -1)
        {
          size = ZString.CIRC.length();
          op = "o";
        }
        else if (word.indexOf(ZString.DRES) != -1)
        {
          size = ZString.DRES.length();
          op = "<|";
        }
        else if (word.indexOf(ZString.RRES) != -1)
        {
          size = ZString.RRES.length();
          op = "|>";
        }
        else if (word.indexOf(ZString.NDRES) != -1)
        {
          size = ZString.NDRES.length();
          op = "!<|";
        }
        else if (word.indexOf(ZString.NRRES) != -1)
        {
          size = ZString.NRRES.length();
          op = "!|>";
        }
        else if (word.indexOf(ZString.OPLUS) != -1)
        {
          size = ZString.OPLUS.length();
          op = "(+)";
        }
        else if (word.indexOf(ZString.PFUN) != -1)
        {
          size = ZString.PFUN.length();
          op = "-|->";
        }
        else if (word.indexOf(ZString.PINJ) != -1)
        {
          size = ZString.PINJ.length();
          op = ">-|->";
        }
        else if (word.indexOf(ZString.INJ) != -1)
        {
          size = ZString.INJ.length();
          op = ">-->";
        }
        else if (word.indexOf(ZString.PSURJ) != -1)
        {
          size = ZString.PSURJ.length();
          op = "-|->>";
        }
        else if (word.indexOf(ZString.SURJ) != -1)
        {
          size = ZString.SURJ.length();
          op = "-->>";
        }
        else if (word.indexOf(ZString.BIJ) != -1)
        {
          size = ZString.BIJ.length();
          op = ">-->>";
        }
        else if (word.indexOf(ZString.FFUN) != -1)
        {
          size = ZString.FFUN.length();
          op = "-||->";
        }
        else if (word.indexOf(ZString.FINJ) != -1)
        {
          size = ZString.FINJ.length();
          op = ">-||->";
        }
        else if (word.indexOf(ZString.MINUS) != -1)
        {
          size = ZString.MINUS.length();
          op = "-";
        }
        else if (word.indexOf(ZString.MULT) != -1)
        {
          size = ZString.MULT.length();
          op = "*";
        }
        else if (word.indexOf(ZString.LEQ) != -1)
        {
          size = ZString.LEQ.length();
          op = "<=";
        }
        else if (word.indexOf(ZString.LESS) != -1)
        {
          size = ZString.LESS.length();
          op = "<";
        }
        else if (word.indexOf(ZString.GEQ) != -1)
        {
          size = ZString.LEQ.length();
          op = ">=";
        }
        else if (word.indexOf(ZString.GREATER) != -1)
        {
          size = ZString.GREATER.length();
          op = ">";
        }
        else if (word.indexOf(ZString.CAT) != -1)
        {
          size = ZString.GREATER.length();
          op = "^";
        }
        else if (word.indexOf(ZString.EXTRACT) != -1)
        {
          size = ZString.EXTRACT.length();
          op = "EXTRACT";
        }
        else if (word.indexOf(ZString.FILTER) != -1)
        {
          size = ZString.FILTER.length();
          op = "FILTER";
        }
        if (op != null)
        {
          result.append("_ ");
          result.append(op);
          result.append(" _");
          size += 2 * ZString.ARG_TOK.length();
        }
      }
      else
      {
        String other = matchOtherStrings(word);
        if (other != null)
        {
          size = matchOtherSize(other);
          result.append(other);
        }
      }
      ZUtils.unicodeToAscii(word.substring(size), result);
    }
    if (printIds_) {
      result.append("_").append(zName.getId());
    }
    result.append(visit(zName.getStrokeList()));
    return result.toString();
  }

  // for extensions to add any extra special ZName matching within PrintVisitor
  protected String matchOtherStrings(String zNameWord)
  {
    return null;
  }

  protected int matchOtherSize(String other)
  {
    return other != null ? other.length() : 0;
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
