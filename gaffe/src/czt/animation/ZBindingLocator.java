package czt.animation;
import czt.animation.gui.temp.*;
/**
 * <code>ZLocator</code> for <code>ZBinding</code>s.
 * Locates a value inside a ZBinding.
 */
class  ZBindingLocator extends ZLocator {
  /**
   * The name of the variable in a binding to return.
   */
  protected String location;

  /**
   * Creates a ZBindingLocator for a variable named l.
   */
  public ZBindingLocator(String l) {
    location=l;
  };
  /**
   * Creates a ZBindingLocator for a variable <code>l</code>, with a locator <code>nl</code> to go
   * inside that variable.
   */
  public ZBindingLocator(String l, ZLocator nl) {
    super(nl);
    location=l;
  };
  /**
   * Locates a value within a ZBinding.  
   * @throws ClassCastException If the value passed wasn't a Binding, or if the next locator didn't match up with its variable.
   */
  public ZValue apply(ZValue v) throws ClassCastException{
    ZBinding t=(ZBinding) v;
    return recurse(t.get(location));
  };
};
