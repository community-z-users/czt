package net.sourceforge.czt.gaffe2.animation.common.adapter;

import java.io.IOException;

import javax.swing.JComponent;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.Factory;

public class AdapterDefaultImpl implements Adapter
{
  protected Factory factory;
  protected ZLive zLive;
  
  public AdapterDefaultImpl()
  {
    factory = GaffeFactory.getFactory();
    zLive   = GaffeFactory.getZLive();
  }

  public Expr componentToData(JComponent jc)
  {
    // TODO Auto-generated method stub
    return null;
  }

  public JComponent dataToComponent(JComponent origin, Expr expr)
  {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * @param expr
   * @return
   */
  public Object encodeExpr(Expr expr){
    return zLive.printTerm(expr, Markup.LATEX);
  }
  
  /**
   * @param value
   * @return
   */
  public Expr decodeExpr(Object value)
  {
    Source newSource = new StringSource(value.toString());
    newSource.setMarkup(Markup.LATEX);
    SectionManager sectman = zLive.getSectionManager();
    //String name of section
    try {
      Expr expr = ParseUtils.parseExpr(newSource, zLive.getCurrentSection(),
          sectman);
      return expr;
    } catch (IOException ex) {
      ex.printStackTrace();
      return null;
    } catch (CommandException ex) {
      ex.printStackTrace();
      return null;
    }
  }
  
}
