package net.sourceforge.czt.typecheck.z;

/**
 * An class for annotating error messages associated with terms.
 */
public class ErrorAnn
{
  /** The position message. */
  protected String position_;

  /** Error message. */
  protected String message_;

  public ErrorAnn(String message)
  {
    this(null, message);
  }

  public ErrorAnn(String position, String message)
  {
    position_ = position;
    message_ = message;
  }

  public void setPosition(String position)
  {
    position_ = position;
  }

  public String getPosition()
  {
    return position_;
  }

  public void setMessage(String message)
  {
    message_ = message;
  }

  public String getMessage()
  {
    return message_;
  }

  public String toString()
  {
    String result = new String();
    if (position_ != null) {
      result += position_;
    }
    result += message_;

    return result;
  }
}
