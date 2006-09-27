package net.sourceforge.czt.gaffe2.animation.common.adapter;


public class BindExpr_DefaultAdapter extends AdapterDefaultImpl
{

  public BindExpr_DefaultAdapter()
  {
    super();
    // TODO Auto-generated constructor stub
  }
  
  /**
   * @param expr
   * @return
   *//*
  public Object encodeExpr(Expr expr){
    BindExpr bindExpr = (BindExpr) expr;
    ZDeclList declList = bindExpr.getZDeclList();
    
    HashMap<String,String> code = new HashMap<String,String>();
    String key;
    String value;
    for (Decl decl : declList) {
      ConstDecl tempDecl = (ConstDecl) decl;
      key = tempDecl.getZDeclName().toString();
      value = ((RefExpr) tempDecl.getExpr()).getZRefName().getWord();
      code.put(key,value);
    }
    return code;
    
  }
  
  *//**
   * @param value
   * @return
   *//*
  @SuppressWarnings("unchecked")
  public Expr decodeExpr(Object value)
  {
    HashMap<String,String> code = (HashMap<String,String>)(value);
    ZDeclList result = factory.createZDeclList();
    for (String key : code.keySet()) {
      ZDeclName name = factory.createZDeclName(key);
      RefExpr expr = factory.createRefExpr(factory.createZRefName(code.get(key)));
      result.add((Decl) factory.createConstDecl(name, expr));
    }
    return factory.createBindExpr(result);
  }*/
}
