/*
 * WarningManager.java
 *
 * Created on 02 May 2007, 13:46
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.typecheck.circusconf;

import java.io.Writer;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.circusconf.PrintUtils;
import net.sourceforge.czt.session.SectionInfo;

/**
 *
 * @author leo
 */
public class WarningManager 
    extends  net.sourceforge.czt.typecheck.circus.WarningManager
{
  
  public WarningManager()
  {
    super();
  }

  /** Creates a new instance of WarningManager
   * @param forLogger 
   */
  public WarningManager(Class<?> forLogger)
  {
    super(forLogger);
  }
  
  public WarningManager(SectionInfo manager)
  {
    super(manager);
  }
  
  public WarningManager(Class<?> forLogger, SectionInfo manager)
  {
    super(forLogger, manager);
  }
  
  @Override
  protected void print(Term t, Writer w)
  {
	 PrintUtils.print(t, w, getManager(), getCurrentSectName(), getMarkup());
  }
}
