package czt.animation;

import czt.animation.gui.temp.*;

/**
 * <code>ZLocator</code> for <code>ZTuple</code>s.
 * Locates a value inside a ZTuple.
 */
class  ZTupleLocator extends ZLocator {
  /**
   * The index of the tuple-member to return.
   */
  protected int location;

  /**
   * Creates a ZTupleLocator for the <code>l</code>th member of a tuple.
   */
  public ZTupleLocator(int l) {
    location=l;
  };
  /**
   * Creates a ZTupleLocator for the <code>l</code>th member of a tuple, with a locator <code>nl</code>
   * to go inside that member.
   */
  public ZTupleLocator(int l, ZLocator nl) {
    super(nl);
    location=l;
  };
  
  /**
   * Locates a value within a ZTuple.  
   * @throws ClassCastException If the value passed wasn't a Tuple, or if the next locator didn't match up with its variable.
   */
  public ZValue apply(ZValue v) throws ClassCastException{
    ZTuple t=(ZTuple) v;
    return recurse(t.get(location));
  };
};
