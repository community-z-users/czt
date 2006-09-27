package net.sourceforge.czt.gaffe2.animation.common.adapter;


public class SetExpr_DefaultAdapter extends AdapterDefaultImpl
{

  public SetExpr_DefaultAdapter()
  {
    super();
    // TODO Auto-generated constructor stub
  }

  /*public Object encodeExpr(Expr expr){
    SetExpr setExpr = (SetExpr) expr;
    ZExprList exprList = setExpr.getZExprList();
    ArrayList<String> code = new ArrayList<String>();
    for (Expr tempExpr : exprList) {
      RefExpr value = (RefExpr) tempExpr;
      code.add(value.getZRefName().getWord());
    }
    return code;
  }
  
  @SuppressWarnings("unchecked")
  public Expr decodeExpr(Object code){
    ZExprList exprList = factory.createZExprList();
    ArrayList<String> value = (ArrayList<String>)code;
    for (String temp: value){
      exprList.add(factory.createRefExpr(factory.createZRefName(temp)));
    }
    return factory.createSetExpr(exprList);
  }*/
}
