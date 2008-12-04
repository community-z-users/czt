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
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;

public class AlloyPrinter extends VisitReturn
{

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
      if (ret.length() > 75) ret += "\n\t";
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
    return x.toString();
  }

  @Override
  public Object visit(ExprUnary x) throws Err
  {
    String op = x.op.toString();
    if (op.contains("of")){
      op = op.replace("of", "");
    }
    return op + " " + visitThis(x.sub);
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
