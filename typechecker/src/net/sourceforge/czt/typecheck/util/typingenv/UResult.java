package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * A class for holding the results of unification. A partial
 * unificiation (PARTIAL), must be created with the types that are not
 * unified.
 */
final public class UResult
{
  /** The possible results of a unification. */
  /** Succeed. */
  public static final UResult SUCC = new UResult("SUCC");

  /** Partial (there are still variable types). */
  public static final UResult PARTIAL = new UResult("PARTIAL");

  /** Failure. */
  public static final UResult FAIL = new UResult("FAIL");

  protected final String name_;

  /**
   * Only this class can create instances.
   */
  private UResult(String name)
  {
    name_ = name;
  }

  public String toString()
  {
    return name_;
  }
}
