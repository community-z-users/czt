/*
 * WarningManager.java
 *
 * Created on 02 May 2007, 13:46
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.typecheck.circus;

import java.io.StringWriter;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.circus.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;

/**
 *
 * @author leo
 */
public class WarningManager extends net.sourceforge.czt.z.util.WarningManager
{
  private Markup markup_ = Markup.LATEX;
  private final SectionInfo sectInfo_;
  
  
  public WarningManager()
  {
    super();
    sectInfo_ = null;
  }

  /** Creates a new instance of WarningManager
   * @param forLogger 
   */
  public WarningManager(Class<?> forLogger)
  {
    super(forLogger);
    sectInfo_ = null;
  }
  
  public WarningManager(SectionInfo manager)
  {
    super();
    sectInfo_ = manager;
  }
  
  public WarningManager(Class<?> forLogger, SectionInfo manager)
  {
    super(forLogger);
    sectInfo_ = manager;
  }
  
  @Override
  protected String format(String message, Object... arguments)
  { 
    if (sectInfo_ != null)
    {
      Object[] values = new Object[arguments.length];
      for(int i = 0; i < arguments.length; i++)      
      {        
        if (arguments[i] instanceof Term)
        {          
          try 
          {
            StringWriter writer = new StringWriter();          
            PrintUtils.print((Term)arguments[i], writer, (SectionManager)sectInfo_, getCurrentSectName(), getMarkup());
            values[i] = writer.toString();
          } catch (CztException e)
          {
            values[i] = String.valueOf(arguments[i]) + "\n\t\t- could not use pretty printer because '" + e.toString() + "'";
          }
          
        }
        else
        {
          values[i] = String.valueOf(arguments[i]);
        }
      }
      return super.format(message, values);
    }
    else
    {
      return super.format(message, arguments);
    }    
  }
  
  public Markup getMarkup()
  {
    assert markup_ != null;
    return markup_;
  }
  
  public void setMarkup(Markup markup)
  {
    assert markup != null : "invalid null markup";
    markup_ = markup;
  }

  public void warn(WarningMessage wm, List<Object> params)
  {
    warn(wm, params.toArray());
  }

  public void warn(WarningMessage wm, Object... arguments)
  {
    warn(wm.getFullMessage(), arguments);
  }
}
