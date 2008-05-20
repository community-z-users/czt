package net.sourceforge.czt.animation.eval.result;

/** This exception is throw when precise information is requested
 *  from a 'fuzzy' set (partially unknown) too early.  For example,
 *  when size() is called.
 * @author marku
 *
 */
public class FuzzySetException extends net.sourceforge.czt.util.CztException
{
  private static final long serialVersionUID = 1403403910627393752L;

  public FuzzySetException()
  {
  }

  public FuzzySetException(String arg0)
  {
    super(arg0);
  }

  public FuzzySetException(Throwable arg0)
  {
    super(arg0);
  }

  public FuzzySetException(String arg0, Throwable arg1)
  {
    super(arg0, arg1);
  }
}
