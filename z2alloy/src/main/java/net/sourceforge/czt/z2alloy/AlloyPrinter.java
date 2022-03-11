package net.sourceforge.czt.z2alloy;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z2alloy.ast.Enum;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprBinary;
import net.sourceforge.czt.z2alloy.ast.ExprCall;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;
import net.sourceforge.czt.z2alloy.ast.ExprITE;
import net.sourceforge.czt.z2alloy.ast.ExprLet;
import net.sourceforge.czt.z2alloy.ast.ExprQuant;
import net.sourceforge.czt.z2alloy.ast.ExprUnary;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;
import net.sourceforge.czt.z2alloy.ast.SubSig;
import net.sourceforge.czt.z2alloy.ast.SubsetSig;
import net.sourceforge.czt.z2alloy.ast.VisitReturn;

public class AlloyPrinter extends VisitReturn<String> {
  /**
   * returns a String representation of the sig which looks like :
   * 
   * <pre>
   * (lone/one/some/abstract) sig sigLabel (extends parent) {
   *    fieldLabel : field,
   *    fieldLabel : field,
   *    ... 
   * } {
   *    fact
   * } 
   * pred
   * some_sigLabel : run {some sigLabel}
   * </pre>
   * 
   * Calls visitThis for the fields, fact and pred
   */
  public String visitSig(Sig sig) {

    String ret = "";

    if (sig instanceof Enum) {
      // enums looks totally different
      Enum enumSig = (Enum) sig;

      ret = "enum " + enumSig.parent().label();
      List<SubSig> children = enumSig.children();
      ret += "{" + children.get(0).label();
      for (int i = 1; i < children.size(); i++) {
        ret += ", " + children.get(i).label();
      }
      ret += "}";
      return ret;
    }

    if (sig.isLone())
      ret += "lone ";
    if (sig.isOne())
      ret += "one ";
    if (sig.isSome())
      ret += "some ";
    if (sig.isAbstract())
      ret += "abstract ";

    ret += "sig " + sig.label();
    if (sig instanceof SubSig)
      ret += " extends " + visit(((SubSig) sig).parent());
    if (sig instanceof SubsetSig)
      ret += " in " + visit(((SubsetSig) sig).parent());

    // abbreviated version for fieldless + predless sigs
    if (sig.fields().isEmpty() && sig.pred() instanceof ExprConstant
        && ((ExprConstant) sig.pred() == ExprConstant.TRUE)) {
      return ret + "{}";
    }

    ret += "{\n";
    List<Field> printedFields = null;
    if (sig instanceof PrimSig)
      printedFields = sig.fields();
    if (sig instanceof SubsetSig)
      printedFields = ((SubsetSig) sig).extraFields();
    if (sig instanceof SubSig)
      printedFields = ((SubSig) sig).extraFields();

    for (Field f : printedFields) {
      ret += "\t" + f.label() + ": " + visitThis(f.expr()) + ",\n";
    }
    ret += "}{";
    ret += visitThis(sig.pred());
    ret += "}";
    ret += "\n";
    // ret += "\nsome_" + sig.label() + " : run { some " + sig.label() +
    // " }";

    return ret;
  }

  /**
   * returns a String representation of the func which looks like:
   * 
   * <pre>
   * func/pred fLabel [params] (: returnDecl) {
   *    body
   * }
   * </pre>
   * 
   * calls visitThis for the returnDecl and body
   * 
   */
  public String print(Func f) {
    StringBuffer result = new StringBuffer();
    result.append(f.toString());
    result.append("[");
    result.append(print(f.params()));
    result.append("]");
    if (!f.pred() && f.returnDecl() != null) {
      result.append(" : ");
      result.append(visitThis(f.returnDecl()));
    }
    result.append(" {");
    if (f.getBody() != ExprConstant.TRUE) {
      List<AlloyExpr> splitBody = splitPred(f.getBody());
      for (AlloyExpr sub : splitBody) {
        String subExpr = visitThis(sub);
        if (subExpr.startsWith("(") && subExpr.endsWith(")")) {
          subExpr = subExpr.substring(1, subExpr.length() - 1);
        }
        result.append("\n\t" + subExpr);
      }
      if (!splitBody.isEmpty()) {
        result.append("\n");
      }
    }
    result.append("}");
    return result.toString();
  }

  /**
   * returns a String representation of the ExprVar list which looks like:
   * 
   * <pre>
   * label1 : expr1, label2 : expr2, ..., labeln : exprn
   * </pre>
   * 
   * calls visitThis for the exprs.
   * 
   */

  public String print(List<ExprVar> list) {
    StringBuffer result = new StringBuffer("");
    for (Iterator<ExprVar> iter = list.iterator(); iter.hasNext();) {
      ExprVar var = iter.next();
      result.append(var.label() + ": " + visitThis(var.expr()));
      if (iter.hasNext())
        result.append(", ");
    }
    return result.toString();
  }

  /**
   * returns a String representation of the ExprBinary which looks like:
   * 
   * <pre>
   * ( left op right )
   * </pre>
   * 
   * unless the op is ISSEQ_ARROW_LONE in which case it looks like:
   * 
   * <pre>
   * seq right
   * </pre>
   * 
   * calling visitThis for the left and right expression
   * 
   */
  public String visit(ExprBinary x) {
    if (x.op().equals(ExprBinary.Op.SEQ)) {
      return "(seq " + visitThis(x.right()) + ")";
    }
    String left = visitThis(x.left()).toString();
    String right = visitThis(x.right()).toString();
    if (x.op().equals(ExprBinary.Op.JOIN) && x.right() instanceof Field) {
      return "(" + left + " " + "." + " @" + right + ")";
    }
    return "(" + left + " " + x.op() + " " + right + ")";
  }

  /**
   * returns a String representation of the ExprList which looks like:
   * 
   * <pre>
   * funLabel [arg1, arg2, ..., argn]
   * </pre>
   * 
   * calling visitThis for each arg
   * 
   */
  public String visit(ExprCall x) {
    String ret = x.fun().label();
    ret += "[";
    for (int i = 0; i < x.args().size(); i++) {
      ret += visitThis(x.args().get(i));
      if (i < x.args().size() - 1) {
        ret += ", ";
      }
    }

    ret += "]";
    return "(" + ret + ")";
  }

  /**
   * returns a printed version of the constant
   */

  public String visit(ExprConstant x) {
    if (x.op() == ExprConstant.Op.TRUE)
      return visitThis(ExprConstant.ONE.equal(ExprConstant.ONE));
    if (x.op() == ExprConstant.Op.FALSE)
      return visitThis(ExprConstant.ONE.equal(ExprConstant.ZERO));
    return x.toString();
  }

  // TODO
  public String visit(ExprITE x) {
    return x.toString();
  }

  // TODO
  public String visit(ExprLet x) {
    return x.toString();
  }

  /**
   * returns a String representation of the ExprQuant. If the ExprQuant
   * operation is comprehension is looks like:
   * 
   * <pre>
   * { vars | subexpr }
   * </pre>
   * 
   * otherwise :
   * 
   * <pre>
   * op vars | subexpr
   * </pre>
   * 
   * calling visitThis for the subexpr and print for the vars
   */

  public String visit(ExprQuant x) {
    String ret = "";
    if (x.op() != ExprQuant.Op.COMPREHENSION) {
      ret += x.op() + " ";
    }
    ret += print(x.vars());
    ret += " | ";
    ret += visitThis(x.sub());
    if (x.op() == ExprQuant.Op.COMPREHENSION) {
      ret = "{" + ret + "}";
    }
    return ret;
  }

  /**
   * returns a String representation of the ExprUnary which looks like:
   * 
   * <pre>
   * op subexpr
   * </pre>
   * 
   * If the operation is cast2int or cast2sigint the op is ommitted. <br/>
   * If the operation is oneOf, someOf, loneOf, setOf then the of is ommitted.
   */
  public String visit(ExprUnary x) {
    String op = x.op().toString() + " ";
    if (op.contains("of")) {
      op = op.replace("of", "");
    }
    if (x.op() == ExprUnary.Op.CAST2INT
        || x.op() == ExprUnary.Op.CAST2SIGINT) {
      op = "";
    }
    return "(" + op + visitThis(x.sub()) + ")";
  }

  /**
   * returns the label of the exprVar
   */
  public String visit(ExprVar x) {
    return x.label();
  }

  /**
   * returns the label of the sig
   */
  public String visit(Sig x) {
    return x.label();
  }

  /**
   * returns the label of the field
   */
  public String visit(Field x) {
    return x.label();
  }

  public String visit(Enum x) {
    return x.label();
  }

  /*
   * split top level and chains into separate predicates, so they can go on
   * different lines eg instead of ((1==1) && (1==2)) (1==1) (1==2)
   * 
   * makes it much, much nicer to read, and far fewer annoying stupid brackets
   */
  private List<AlloyExpr> splitPred(AlloyExpr e) {
    List<AlloyExpr> exprs = new ArrayList<AlloyExpr>();
    if (e instanceof ExprBinary
        && ((ExprBinary) e).op().equals(ExprBinary.Op.AND)) {
      ExprBinary exprBinary = (ExprBinary) e;
      exprs.addAll(splitPred(exprBinary.left()));
      exprs.addAll(splitPred(exprBinary.right()));
    } else {
      exprs.add(e);
    }
    return exprs;
  }
}
