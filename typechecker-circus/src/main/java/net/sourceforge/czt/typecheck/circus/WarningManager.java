/*
 * WarningManager.java
 *
 * Created on 02 May 2007, 13:46
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.typecheck.circus;

import java.util.List;

/**
 *
 * @author leo
 */
public class WarningManager extends net.sourceforge.czt.z.util.WarningManager
{

  public WarningManager()
  {
    super();
  }

  /** Creates a new instance of WarningManager */
  public WarningManager(Class<?> forLogger)
  {
    super(forLogger);
  }

  public void warn(WarningMessage wm, List<Object> params)
  {
    warn(wm, params.toArray());
  }

  public void warn(WarningMessage wm, Object... arguments)
  {
    String message = wm.getMessage() + "\n\n\t" + wm.getExplanation();
    warn(message, arguments);
  }
}
