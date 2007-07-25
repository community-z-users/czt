/*
 * DomainCheckException.java
 *
 * Created on 09 July 2007, 23:33
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.z.dc;

/**
 *
 * @author leo
 */
public class DomainCheckException extends Exception
{
  
  /** Creates a new instance of DomainCheckException */
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
