
package net.sourceforge.czt.modeljunit.gui;

/**
 * IView.java
 * @author rong 16th/October/2007
 */

/*
 * IView interface provides a way for model object to update view. When the data
 * in model changed, model should call update method to update view's display.
 */
public interface IView
{
  public void update(Object data);
}
