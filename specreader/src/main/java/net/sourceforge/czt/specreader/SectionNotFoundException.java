package net.sourceforge.czt.specreader;

/**
 * Exception for when a section cannot be found.
 * 
 * @author ian
 */
public final class SectionNotFoundException extends Exception
{
  private static final long serialVersionUID = 1L;

  public SectionNotFoundException()
  {
  }

  public SectionNotFoundException(String arg0)
  {
    super(arg0);
  }

  public SectionNotFoundException(Throwable arg0)
  {
    super(arg0);
  }

  public SectionNotFoundException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }

}
