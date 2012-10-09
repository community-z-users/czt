package net.sourceforge.czt.specreader;

/**
 * Exception for when a file has a first section header after formal paragraphs.
 * 
 * @author ian
 */
public final class IllegalAnonSectionException extends Exception
{
  private static final long serialVersionUID = 1L;

  public IllegalAnonSectionException()
  {
  }

  public IllegalAnonSectionException(String arg0)
  {
    super(arg0);
  }

  public IllegalAnonSectionException(Throwable arg0)
  {
    super(arg0);
  }

  public IllegalAnonSectionException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }
}
