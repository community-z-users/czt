
package net.sourceforge.czt.animation.common.adapter;

import java.math.BigInteger;

import javax.swing.ImageIcon;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;

/**
 * @author Linan Zhang
 *
 */
public class NumExpr_ImageAdapter extends NumExpr_DefaultAdapter
{
  private ImageIcon imageIcon;  // The imageIcon to display number

  /**
   * Constructor
   */
  public NumExpr_ImageAdapter()
  {
    super();
    imageIcon = new ImageIcon();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    BigInteger num = new BigInteger(imageIcon.getDescription());
    expr = factory.createNumExpr(num);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#setExpr(net.sourceforge.czt.z.ast.Expr)
   */
  public void setExpr(Expr expr)
  {
    this.expr = (NumExpr) expr;
    imageIcon.setImage(new ImageIcon().getImage());
    imageIcon.setDescription(this.expr.getValue().toString());
  }

}
