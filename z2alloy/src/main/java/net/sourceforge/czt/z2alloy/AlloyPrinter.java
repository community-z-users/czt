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
  public Object visitSig (Sig sig, Expr fact, Func pred) throws Err {
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

  @Override
  public Object visit(ExprBinary x) throws Err
  {
    return "(" + visitThis(x.left) + " " + x.op + " " + visitThis(x.right) + ")";
  }

  @Override
  public Object visit(ExprList x) throws Err
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

  @Override
  public Object visit(ExprCall x) throws Err
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
    return ret;
  }

  @Override
  public Object visit(ExprConstant x) throws Err
  {
    return x.toString();
  }

  @Override
  public Object visit(ExprITE x) throws Err
  {
    return x.toString();
  }

  @Override
  public Object visit(ExprLet x) throws Err
  {
    return x.toString();
  }

  @Override
  public Object visit(ExprQuant x) throws Err
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

  @Override
  public Object visit(ExprUnary x) throws Err
  {
    String op = x.op.toString() + " ";
    if (op.contains("of")){
      op = op.replace("of", "");
    }
    if (x.op == ExprUnary.Op.CAST2INT || x.op == ExprUnary.Op.CAST2SIGINT) {
      op = "";
    }
    return op + visitThis(x.sub);
  }

  @Override
  public Object visit(ExprVar x) throws Err
  {
    return x.label;
  }

  @Override
  public Object visit(Sig x) throws Err
  {
    return x.label;
  }

  @Override
  public Object visit(Field x) throws Err
  {
    return x.label;
  }
}
