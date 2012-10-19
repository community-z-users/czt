package java_cup;

/**
 * An unchecked exception to signal fatal errors in CUP parser.
 * 
 * @author Andrius Velykis
 */
public class CupParserException extends RuntimeException
{
  private static final long serialVersionUID = 4629960521393135343L;

  public CupParserException()
  {
    super();
  }

  public CupParserException(String message, Throwable cause)
  {
    super(message, cause);
  }

  public CupParserException(String message)
  {
    super(message);
  }

  public CupParserException(Throwable cause)
  {
    super(cause);
  }

}
