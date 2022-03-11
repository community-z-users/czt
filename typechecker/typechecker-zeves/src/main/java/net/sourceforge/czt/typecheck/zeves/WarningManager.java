/*
 * WarningManager.java
 *
 * Created on 02 May 2007, 13:46
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.typecheck.zeves;

import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.zeves.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.util.CztException;
//import net.sourceforge.czt.print.zeves.PrintUtils;

/**
 * TODO: REFACTOR into Z: just copied from Circus typechecker (!) not good...
 * @author leo
 */
public class WarningManager 
    extends net.sourceforge.czt.z.util.WarningManager
{
  private Markup markup_ = Markup.LATEX;
  private final SectionInfo sectInfo_;
  private Term term_ = null;
  private final List<ErrorAnn> warnErrors_ = new ArrayList<ErrorAnn>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  
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
            PrintUtils.print((Term)arguments[i], writer, (SectionManager)sectInfo_, 
            		getCurrentSectName(), getMarkup());
            values[i] = writer.toString();
          } 
          catch (PrintException f)
          {
              values[i] = String.valueOf(arguments[i]) + "\n\t\t- could not use pretty printer because '" + f.toString() + "'";        	  
          }
          catch (CztException e)
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
  
  public Term getTerm()
  {
    return term_;
  }
  
  @Override
public void clear()
  {
    super.clear();
    clearWarnErrors();
  }
  
  public void clearWarnErrors()
  {
    warnErrors_.clear();
  }
  
  public List<ErrorAnn> warnErrors()
  {
    return Collections.unmodifiableList(warnErrors_);
  }
  
  public void setMarkup(Markup markup)
  {
    assert markup != null : "invalid null markup";
    markup_ = markup;
  }

  public void warn(Term term, WarningMessage wm, List<Object> params)
  {
    warn(term, wm, params.toArray());
  }

  public void warn(Term term, ErrorMessage msg, Object... params)
  {
    ErrorAnn errorAnn = new ErrorAnn(msg.toString(), params, (SectionManager)sectInfo_,
      getCurrentSectName(), GlobalDefs.nearestLocAnn(term), term, markup_);
    errorAnn.setErrorType(ErrorType.WARNING);
    //errorAnn.setInfo(msg.name());
    warnErrors_.add(errorAnn);
    doWarn(errorAnn.toString());
  }

  public void warn(Term term, WarningMessage wm, Object... arguments)
  {
    ErrorAnn errorAnn = new ErrorAnn(wm.toString(), arguments, (SectionManager)sectInfo_,
      getCurrentSectName(), GlobalDefs.nearestLocAnn(term), term, markup_);
    errorAnn.setErrorType(ErrorType.WARNING);
    errorAnn.setInfo(wm.getExplanation());
    warnErrors_.add(errorAnn);
    warn(term, wm.getFullMessage(), arguments);
  }  
  
  public void warn(Term term, String message, Object... arguments) 
  {
    StringBuilder sb = new StringBuilder();
    term_ = term;
    String s = createWarning(message, arguments);
    sb.append(s);
    if (term != null)
    {
      // "Location..".length() = 10, for beautification
      sb.append("\n\tLocation..: ");      
      sb.append(GlobalDefs.position(term));
    }
    doWarn(sb.toString());
  }  
}
