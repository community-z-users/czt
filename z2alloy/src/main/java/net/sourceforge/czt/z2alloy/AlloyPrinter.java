package net.sourceforge.czt.z2alloy;

import java.util.List;

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
  
  public String createSig (Sig sig, Func pred) throws Err {
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
    ret += "}{" + pred.label + "[";
    for (Sig.Field f : sig.getFields()) {
      ret += f.label + ", ";
    }
    // remove last , 
    if (!sig.getFields().isEmpty()) {
      ret = ret.substring(0, ret.length() - 2);
    }
    ret += "]}";
    ret += "\npred " + pred.label + " (";
    for (ExprVar exprVar : pred.params) {
      ret += exprVar.label + " : " + exprVar.type + ", ";
    }
    // remove last , 
    if (!pred.params.isEmpty()) {
      ret = ret.substring(0, ret.length() - 2);
    }
    ret += ") {";
    if (pred.getBody() != ExprConstant.FALSE) {
      ret += "\n\t";
      ret += visitThis(pred.getBody());
      ret += "\n";
    }
    ret += "}";

    ret += "\nsome_" + sig.label + " : run { some " + sig.label + " }";

    return ret;
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
    return x.toString();
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
    if (x.op == ExprQuant.Op.COMPREHENSION) {
      ret = "{";
    }
    else {
      ret += x.op;
    }
    for (ExprVar var : x.vars) {
      ret += " " + visit(var) + " : " + var.expr + ",";
    }
    ret = ret.substring(0, ret.length() - 1);
    ret += " | ";
    ret += visitThis(x.sub);
    if (x.op == ExprQuant.Op.COMPREHENSION) {
      ret += "}";
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
