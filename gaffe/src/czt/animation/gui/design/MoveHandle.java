package czt.animation.gui.design;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.event.*;
import java.awt.*;
import java.beans.*;

/**
 * The invisible component that sits on the glass pane above each bean in the FormDesign.
 * Manages moving the bean it is matched to.
 */
class MoveHandle extends JComponent {
  /**
   * The component on the content pane this handle is matched to.
   */
  protected Component component;
  
  /**
   * Creates a MoveHandle that isn't associated with a component.
   */
  public MoveHandle() {this(null);};
  
  /**
   * Creates a MoveHandle associated with <code>c</code>
   */
  public MoveHandle(Component c) {
    setComponent(c);
    DragListener dl=new DragListener();
    addMouseMotionListener(dl);
    addMouseListener(dl);
    component.addComponentListener(new BoundsChangeListener());
    setCursor(new Cursor(Cursor.MOVE_CURSOR));
  };

  /**
   * Getter function for component.
   */
  public Component getComponent() {
    return component;
  };
  /**
   * Setter function for component.
   */
  public void setComponent(Component c) {
    component=c;
    setBounds(c.getBounds());
  };
  /**
   * Listener used to keep a MoveHandle the same size and position as the component it is
   * matched to.
   */
  protected class BoundsChangeListener extends ComponentAdapter {
    public void componentMoved(ComponentEvent e) {
      setBounds(component.getBounds());
    };
    public void componentResized(ComponentEvent e) {
      setBounds(component.getBounds());
    };    
  };
  
  
  /**
   * Listener used to move a MoveHandle's component whenever it is dragged.
   */
  protected class DragListener extends MouseInputAdapter {
    /**
     * The point where a drag started.
     */
    protected Point clickDownPoint;
    
    /**
     * Moves the component. Inherited from MouseInputAdapter.
     */
    public synchronized void mouseDragged(MouseEvent e) {
      if((e.getModifiers()&InputEvent.BUTTON1_MASK)==0) return;
      if(clickDownPoint==null) {
	System.err.println("### possible coding error###, "
			   +"mouseDragged in MoveHandle without press first");
	clickDownPoint=e.getPoint();
	return;
      };
      getComponent().setLocation(getX()+e.getX()-(int)clickDownPoint.getX(),
				 getY()+e.getY()-(int)clickDownPoint.getY());
    }; 
    /**
     * Sets the clickDownPoint.  Inherited from MouseInputAdapter.
     */
    public synchronized void mousePressed(MouseEvent e) {
      clickDownPoint=e.getPoint();
    };
    /**
     * Resets the clickDownPoint.  Inherited from MouseInputAdapter.
     */
    public synchronized void mouseReleased(MouseEvent e) {
      clickDownPoint=null;
    };
  };
};
