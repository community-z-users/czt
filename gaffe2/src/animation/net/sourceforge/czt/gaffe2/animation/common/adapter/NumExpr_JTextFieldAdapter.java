package net.sourceforge.czt.gaffe2.animation.common.adapter;

import javax.swing.JComponent;
import javax.swing.JTextField;

import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;

public class NumExpr_JTextFieldAdapter extends AdapterDefaultImpl
{

  public NumExpr_JTextFieldAdapter()
  {
    super();
    // TODO Auto-generated constructor stub
  }

  public Expr componentToData(JComponent jc){
    JTextField component = (JTextField)jc;
    int num = Integer.parseInt(component.getText());
    NumExpr expr = factory.createNumExpr(num);
    return expr;
  }

  public JComponent dataToComponent(JComponent origin, Expr data){
    JTextField component = (origin==null)? new JTextField(): (JTextField)origin;
    NumExpr expr = (NumExpr) data;
    component.setText(expr.getValue().toString());
    return component;
  }
  
}
