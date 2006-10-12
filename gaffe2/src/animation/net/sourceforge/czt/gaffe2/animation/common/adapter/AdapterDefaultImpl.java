package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.Factory;

public class AdapterDefaultImpl implements Adapter
{
  protected Expr expr;
  protected JComponent component;
  
  protected static Factory factory;
  protected static ZLive zLive;
  
  public AdapterDefaultImpl()
  {
    factory = GaffeFactory.getFactory();
    zLive   = GaffeFactory.getZLive();
  }

  public void setExpr(Expr expr)
  {
    this.expr = expr;
  }

  public Expr getExpr()
  {
    return expr;
  }
  
  public JComponent getComponent()
  {
    return component;
  }
  
  public String toString(){
    return this.getClass().getSimpleName();
  }
}
