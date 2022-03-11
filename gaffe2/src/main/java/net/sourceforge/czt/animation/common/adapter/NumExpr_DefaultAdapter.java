
package net.sourceforge.czt.animation.common.adapter;

import java.awt.Color;
import java.awt.Font;
import java.math.BigInteger;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;

/**
 * @author Linan Zhang
 *
 */
public class NumExpr_DefaultAdapter extends AdapterDefaultImpl
{
  protected NumExpr expr;                            // Default expr ref for NumExpr   

  private JTextField component = new JTextField(""); // Default displayed as TextField

  /**
   * Constructor
   */
  public NumExpr_DefaultAdapter()
  {
    super();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getExpr()
   */
  public Expr getExpr()
  {
    BigInteger num = new BigInteger(component.getText());
    expr = factory.createNumExpr(num);
    return expr;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#setExpr(net.sourceforge.czt.z.ast.Expr)
   */
  public void setExpr(Expr expr)
  {
    this.expr = (NumExpr) expr;
    component.setText(this.expr.getValue().toString());
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.adapter.Adapter#getComponent()
   */
  public JComponent getComponent()
  {
    return component;
  }

  /**
   * @return the color.
   */
  public Color getBackground()
  {
    return component.getBackground();
  }

  /**
   * @param color The color to set.
   */
  public void setBackground(Color color)
  {
    this.component.setBackground(color);
  }

  /**
   * @return the font.
   */
  public Font getFont()
  {
    return component.getFont();
  }

  /**
   * @param font The font to set.
   */
  public void setFont(Font font)
  {
    this.component.setFont(font);
  }
}
