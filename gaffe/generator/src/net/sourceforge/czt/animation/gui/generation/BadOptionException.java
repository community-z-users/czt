
package net.sourceforge.czt.animation.gui.generation;

public final class BadOptionException extends Exception
{
  public BadOptionException(String message)
  {
    super(message);
  };

  public BadOptionException(String message, Throwable cause)
  {
    super(message, cause);
  };

  public BadOptionException(Throwable cause)
  {
    super(cause);
  };
};
