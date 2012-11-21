package net.sourceforge.czt.zeves;

import net.sourceforge.czt.zeves.response.ZEvesError;

public class ZEvesException extends Exception
{
  private static final long serialVersionUID = 5537787929670373518L;

  private ZEvesError zEvesErr;
  
  private String debugInfo;

  public ZEvesException()
  {
  }

  public ZEvesException(String message)
  {
    super(message);
  }

  public ZEvesException(Throwable cause)
  {
    super(cause);
  }

  public ZEvesException(String message, Throwable cause)
  {
    super(message, cause);
  }
  
  public ZEvesException(String message, Throwable cause, String debugInfo)
  {
    this(message, cause);
    this.debugInfo = debugInfo;
  }

  public ZEvesException(ZEvesError error)
  {
    this(error, null);
  }
  
  public ZEvesException(ZEvesError error, String debugInfo)
  {
    super(error.toString());

    this.zEvesErr = error;
    this.debugInfo = debugInfo;
  }

  public ZEvesError getZEvesError()
  {
    return zEvesErr;
  }

  public String getDebugInfo()
  {
    return debugInfo;
  }

}
