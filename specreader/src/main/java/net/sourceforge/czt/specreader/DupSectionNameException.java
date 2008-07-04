package net.sourceforge.czt.specreader;

/**
 * Exception for when a section has the same name as another.
 * 
 * @author ian
 */
public class DupSectionNameException extends Exception
{
  private static final long serialVersionUID = 1L;

  public DupSectionNameException()
  {
  }

  public DupSectionNameException(String arg0)
  {
    super(arg0);
  }

  public DupSectionNameException(Throwable arg0)
  {
    super(arg0);
  }

  public DupSectionNameException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }

}
