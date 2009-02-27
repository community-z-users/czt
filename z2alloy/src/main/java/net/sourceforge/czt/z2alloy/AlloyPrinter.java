package net.sourceforge.czt.z2alloy;

import java.util.Iterator;
import java.util.List;

import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprITE;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprLet;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQuant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;

public class AlloyPrinter extends VisitReturn
{
  /**
   * returns a String representation of the sig which looks like :
   * <pre>(lone/one/some/abstract) sig sigLabel (extends parent) {
   *    fieldLabel : field,
   *    fieldLabel : field,
   *    ... 
   * } {
   *    fact
   * } 
   * pred
   * some_sigLabel : run {some sigLabel}</pre>
   * 
   * Calls visitThis for the fields, fact and pred
   */
  public String visitSig (Sig sig, Expr fact, Func pred) throws Err {
    String ret = "";
    if (sig.isLone != null) ret += "lone ";
    if (sig.isOne != null) ret += "one ";
    if (sig.isSome != null) ret += "some ";
    if (sig.isAbstract != null) ret += "abstract ";

    ret += "sig " + sig.label;
    PrimSig s = (PrimSig) sig;
    if (sig.isSubsig != null) ret += " extends " + visit(s.parent);

    ret += "{\n";
    for (Field f : sig.getFields()) {
      ret += "\t" + f.label + ": " + visitThis(Z2Alloy.getFieldExpr(f)) + ",\n";
    }
    ret += "}{";
    ret += visitThis(fact);
    ret += "}";
    ret += "\n";
    ret += print(pred);

    ret += "\nsome_" + sig.label + " : run { some " + sig.label + " }";

    return ret;
  }

  /**
   * returns a String representation of the func which looks like:
   * <pre>func/pred fLabel [params] (: returnDecl) {
   *    body
   * }</pre>
   * calls visitThis for the returnDecl and body
   * 
   */
  public String print(Func f) throws Err
  {
    StringBuffer result = new StringBuffer();
    result.append(f.toString());
    result.append("[");
    result.append(print(f.params));
    result.append("]");
    if (!f.isPred) {
      result.append(" : ");      
      result.append(visitThis(f.returnDecl));
    }
    result.append(" {");
    if (f.getBody() != ExprConstant.TRUE) {
      result.append("\n" + visitThis(f.getBody()) + "\n");
    }
    result.append("}");
    return result.toString();
  }


  /**
   * returns a String representation of the ExprVar list which looks like:
   * <pre>label1 : expr1, label2 : expr2, ..., labeln : exprn</pre>
   * calls visitThis for the exprs.
   * 
   */
  
  public String print(ConstList<ExprVar> list) throws Err
  {
    StringBuffer result = new StringBuffer(" ");
    for (Iterator<ExprVar> iter = list.iterator(); iter.hasNext();) {
      ExprVar var = iter.next();
      result.append(var.label + ": " + visitThis(var.expr));
      if (iter.hasNext()) result.append(", ");
    }
    return result.toString();
  }

  
  /**
   * returns a String representation of the ExprBinary which looks like:
   * <pre> ( left op right )</pre>
   * unless the op is ISSEQ_ARROW_LONE in which case it looks like: <pre>seq right</pre>
   * 
   * calling visitThis for the left and right expression
   * 
   */
  @Override
  public String visit(ExprBinary x) throws Err
  {
    if (x.op.equals(ExprBinary.Op.ISSEQ_ARROW_LONE)) {
      return "(seq " + visitThis(x.right) + ")";
    }
    String left = visitThis(x.left).toString();
    String right = visitThis(x.right).toString();
    if (x.op.equals(ExprBinary.Op.JOIN) && x.right instanceof Field) {
      return "(" + left + " " + "." + " @" + right + ")";
    }
    return "(" + left + " " + x.op + " " + right + ")";
  }

  /**
   * returns a String representation of the ExprList which looks like:
   * <pre>(expr1 op expr2 op ... op exprn) </pre>
   * calling visitThis for each expr
   */
  
  @Override
  public String visit(ExprList x) throws Err
  {
    String opstring = x.op.toString().toLowerCase();
    String ret = "(";
    List<Expr> exprs = x.args;
    for (int i = 0; i < exprs.size() - 1 ; i++) {
      ret += visitThis(exprs.get(i)) + " " + opstring + " ";
    }
    ret += visitThis(exprs.get(exprs.size()-1));
    ret += ")";
    return ret;
  }

  /**
   * returns a String representation of the ExprList which looks like:
   * <pre>funLabel [arg1, arg2, ..., argn]</pre>
   * 
   * calling visitThis for each arg
   * 
   */
  @Override
  public String visit(ExprCall x) throws Err
  {
    String ret = x.fun.label;
    ret += "[";
    for (int i = 0; i < x.args.size(); i++) {
      ret += visitThis(x.args.get(i));
      if (i < x.args.size() -1) {
        ret += ", ";
      }
    }

    ret += "]";
    return "(" + ret + ")";
  }

  /**
   * returns a printed version of the constant
   */
  
  @Override
  public String visit(ExprConstant x) throws Err
  {
    return x.toString();
  }

  // TODO
  @Override
  public String visit(ExprITE x) throws Err
  {
    return x.toString();
  }

  // TODO
  @Override
  public String visit(ExprLet x) throws Err
  {
    return x.toString();
  }

  /**
   * returns a String representation of the ExprQuant. If the ExprQuant operation is comprehension is looks like:
   * <pre> {vars | subexpr} </pre>
   * otherwise :
   * <pre> op vars | subexpr </pre>
   * 
   * calling visitThis for the subexpr and print for the vars
   */
  
  @Override
  public String visit(ExprQuant x) throws Err
  {
    String ret = "";
    if (x.op != ExprQuant.Op.COMPREHENSION) {
      ret += x.op;
    }
    ret += print(x.vars);
    ret += " | ";
    ret += visitThis(x.sub);
    if (x.op == ExprQuant.Op.COMPREHENSION) {
      ret = "{" + ret + "}";
    }
    return ret;
  }

  /**
   * returns a String representation of the ExprUnary which looks like:
   * <pre>op subexpr</pre>
   * If the operation is cast2int or cast2sigint the op is ommitted.
   * <br/>
   * If the operation is oneOf, someOf, loneOf, setOf then the of is ommitted.
   */
  @Override
  public String visit(ExprUnary x) throws Err
  {
    String op = x.op.toString() + " ";
    if (op.contains("of")){
      op = op.replace("of", "");
    }
    if (x.op == ExprUnary.Op.CAST2INT || x.op == ExprUnary.Op.CAST2SIGINT) {
      op = "";
    }
    return "(" + op + visitThis(x.sub) + ")";
  }

  /**
   * returns the label of the exprVar
   */
  @Override
  public String visit(ExprVar x) throws Err
  {
    return x.label;
  }

  /**
   * returns the label of the sig
   */
  @Override
  public String visit(Sig x) throws Err
  {
    return x.label;
  }

  /**
   * returns the label of the field
   */
  @Override
  public String visit(Field x) throws Err
  {
    return x.label;
  }
}
