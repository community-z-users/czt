package czt.animation;

import czt.animation.gui.temp.*;

/**
 * General class for all locators.  Locates a value inside a composite ZValue (e.g. ZBinding, ZTuple).
 */
public abstract class ZLocator {
  /**
   * The next locator.  If this is not a multi-level locator, then <code>nextLocator</code> will be 
   * <code>null</code>.
   */
  protected ZLocator nextLocator;
  /**
   * Creates a single-level locator.
   */
  protected ZLocator() {
    nextLocator=null;
  };
  /**
   * Creates a multi-level locator.  Wraps another locator around nl.
   */
  protected ZLocator(ZLocator nl) {
    nextLocator=nl;
  };
  /**
   * Does the recursive part of an apply.
   */
  protected ZValue recurse(ZValue v) throws ClassCastException {
    return (nextLocator==null)?v:nextLocator.apply(v);
  };
  /**
   * Locates a value within <code>v</code>.
   * @throws ClassCastException If the value passed wasn't of the correct type for this locator, or if the next locator didn't match up with its variable.   */
  public abstract ZValue apply(ZValue v) throws ClassCastException;
};
