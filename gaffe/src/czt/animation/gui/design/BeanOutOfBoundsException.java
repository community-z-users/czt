package czt.animation.gui.design;
import java.awt.Rectangle;
import java.awt.Point;

public class BeanOutOfBoundsException extends Exception {
  Class type;
  Point attemptedLocation;
  Rectangle formBounds;
  public BeanOutOfBoundsException(Class type, Point attemptedLocation, Rectangle formBounds) {
    super("BeanOutOfBoundsException: Attempted to place "+type.getName()
	  +(formBounds.contains(attemptedLocation)?" in":" out")
	  +"side the Form, which is not allowed.  Attempted location = "
	  +attemptedLocation+"; Form bounds = "+formBounds+".");
    this.type=type;
    this.attemptedLocation=attemptedLocation;
    this.formBounds=formBounds;
  };
  public Class getType() {return type;};
  public Point getAttemptedLocation() {return attemptedLocation;};
  public Rectangle getFormBounds() {return formBounds;};
};
