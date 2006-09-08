
package net.sourceforge.czt.gaffe2.animation.common.adapter;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class AdapterException extends Exception
{

  /**
   * 
   */
  public AdapterException()
  {
    super();
  }

  /**
   * @param arg0
   */
  public AdapterException(String arg0)
  {
    super(arg0);
  }

  /**
   * @param arg0
   * @param arg1
   */
  public AdapterException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }

  /**
   * @param arg0
   */
  public AdapterException(Throwable arg0)
  {
    super(arg0);
  }

}
