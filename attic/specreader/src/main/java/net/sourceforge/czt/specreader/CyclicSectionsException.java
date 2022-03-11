package net.sourceforge.czt.specreader;

/**
 * Exception for when sections are ancestors of one another.
 * 
 * @author ian
 */
public final class CyclicSectionsException extends Exception
{
  private static final long serialVersionUID = 1L;

  public CyclicSectionsException()
  {
  }

  public CyclicSectionsException(String arg0)
  {
    super(arg0);
  }

  public CyclicSectionsException(Throwable arg0)
  {
    super(arg0);
  }

  public CyclicSectionsException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }

}
