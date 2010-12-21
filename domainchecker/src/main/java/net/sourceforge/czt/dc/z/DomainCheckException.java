/*
 * DomainCheckException.java
 *
 * Created on 09 July 2007, 23:33
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.dc.z;

import net.sourceforge.czt.session.CommandException;

/**
 *
 * @author leo
 */
public class DomainCheckException extends CommandException
{
  
  /** Creates a new instance of DomainCheckException
   * @param message
   */
  public DomainCheckException(String message)  
  {
     super(message);
  }
  
  public DomainCheckException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public DomainCheckException(Throwable cause)
  {
    super(cause);
  }
}
