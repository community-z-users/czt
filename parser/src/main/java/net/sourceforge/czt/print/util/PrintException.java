/*
 * PrintException.java
 *
 * Created on 23 June 2006, 15:09
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.util;

/**
 *
 * @author leo
 */
public class PrintException extends RuntimeException {
  
  public PrintException()
  {
      super();
  }

  public PrintException(String message)
  {
    super(message);
  }

  public PrintException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public PrintException(Throwable cause)
  {
    super(cause);
  }
  
}
