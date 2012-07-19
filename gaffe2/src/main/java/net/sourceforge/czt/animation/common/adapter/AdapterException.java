
package net.sourceforge.czt.animation.common.adapter;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class AdapterException extends Exception
{

  /**
   * Empty Exception
   */
  public AdapterException()
  {
    super();
  }

  /**
   * Exception with a String messsage
   * @param arg0
   */
  public AdapterException(String arg0)
  {
    super(arg0);
  }

  /**
   * Exception with a Message and a Throwable 
   * @param arg0
   * @param arg1
   */
  public AdapterException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }

  /**
   * Excpetion with only the Throwable
   * @param arg0
   */
  public AdapterException(Throwable arg0)
  {
    super(arg0);
  }

}
