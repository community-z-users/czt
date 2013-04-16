
package net.sourceforge.czt.animation.gui.temp;

public final class UnexpectedTypeException extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 8168459716906329037L;

/**
   * Unexpected type of expr with message
   * @param message The message ready to show
   */
  public UnexpectedTypeException(String message)
  {
    super(message);
  }

  /**
   * Unexpected type of expr with message and cause
   * @param message The message ready to show
   * @param cause The cause
   */
  public UnexpectedTypeException(String message, Throwable cause)
  {
    super(message, cause);
  }

  /**
   * Unexpected type of expr with cause
   * @param cause
   */
  public UnexpectedTypeException(Throwable cause)
  {
    super(cause);
  }
}