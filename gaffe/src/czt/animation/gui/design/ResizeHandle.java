package czt.animation.gui.design;

import czt.animation.gui.Form;
import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;

/**
 * The component that acts as a resizing handle for each bean in the FormDesign.
 * These handles are small squares that sit above the edges and corners of their matching bean.
 */
class ResizeHandle extends JPanel {
  /**
   * The component on the content pane this handle is matched to.
   */
  protected Component component;
  /**
   * Which corner/edge this handle sits on.
   */
  protected final int corner;
  /**
   * Creates a ResizeHandle without specifying which bean it is for.
   * @param corner The edge/corner to sit this handle on.
   */
  public ResizeHandle(int corner) {this(null,corner);};
  
  /**
   * Checks the invariant of this class.  That the corner has to be one of the 8 compass directions 
   * specified in Cursor.
   * @see java.awt.Cursor
   */
  protected void invariant() {
    switch(corner) {
     case Cursor.N_RESIZE_CURSOR:case Cursor.NW_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR: 
     case Cursor.S_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
     case Cursor.W_RESIZE_CURSOR:case Cursor.E_RESIZE_CURSOR:break;
     default:
       throw new Error("Error: Invariant for ResizeHandle broken "
		       +"- corner must be one of the compass point cursor numbers.");
    };
  };
  /**
   * Creates a ResizeHandle for a particular component.
   * @param c the component to match this handle to.
   * @param corner The edge/corner to sit this handle on.
   */
  public ResizeHandle(Component c, int corner) {
    setComponent(c);
    this.corner=corner;
    setCursor(new Cursor(corner));
    setBorder(BorderFactory.createLineBorder(Color.black)); 
    DragListener dl=new DragListener();
    addMouseMotionListener(dl);
    addMouseListener(dl);
    setSize(10,10);
    
    setLocation();
    component.addComponentListener(new BoundsChangeListener());
    setBackground(Color.gray);
    
    invariant();
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
  };
  
  /**
   * Listener used to resize the matching component whenever this handle is dragged.
   */
  class DragListener extends MouseInputAdapter {
    /**
     * The point where a drag started.
     */
    protected Point clickDownPoint;
    
    /**
     * Resizes the component. Inherited from MouseInputAdapter.
     */
    public synchronized void mouseDragged(MouseEvent e) {
      if((e.getModifiers()&InputEvent.BUTTON1_MASK)==0) return;
      Point mousePoint=e.getPoint();
      if(clickDownPoint==null) {
	System.err.println("### possible coding error###, "
			   +"mouseDragged in ResizeHandle without press first");
	clickDownPoint=mousePoint;
	return;
      };
      mousePoint.translate((int)-clickDownPoint.x,(int)-clickDownPoint.y);
      Rectangle newBounds=getComponent().getBounds();
      switch(corner) {
       case Cursor.N_RESIZE_CURSOR:case Cursor.NW_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR:
	 if(mousePoint.getY()>newBounds.getHeight()) mousePoint.y=(int)newBounds.getHeight();
	 newBounds.y+=mousePoint.getY();
	 newBounds.height-=mousePoint.getY();
	 break;
       case Cursor.S_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
	 if(-mousePoint.getY()>newBounds.getHeight()) mousePoint.y=(int)-newBounds.getHeight();
	 newBounds.height+=mousePoint.getY();
	 break;
      };
      switch(corner) {
       case Cursor.W_RESIZE_CURSOR:case Cursor.NW_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:
	 if(mousePoint.getX()>newBounds.width) mousePoint.x=(int)newBounds.getWidth();
	 newBounds.x+=mousePoint.getX();
	 newBounds.width-=mousePoint.getX();
	 break;
       case Cursor.E_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
	 if(-mousePoint.getX()>newBounds.getWidth()) mousePoint.x=(int)-newBounds.getWidth();
	 newBounds.width+=mousePoint.getX();
	 break;
      };
      
      newBounds.setLocation(translateHandleLocation2ComponentLocation(newBounds.getLocation()));
      getComponent().setBounds(newBounds);
      //XXX use Robot to stop mouse moving?
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
  protected void setLocation() {
    Point newLocation=getComponent().getLocation();
    
    switch(corner) {
     case Cursor.E_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
       newLocation.x+=getComponent().getWidth();
       break;
     case Cursor.N_RESIZE_CURSOR:case Cursor.S_RESIZE_CURSOR:
       newLocation.x+=getComponent().getWidth()/2;
    };
    switch(corner) {
     case Cursor.S_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
       newLocation.y+=getComponent().getHeight();
       break;
     case Cursor.W_RESIZE_CURSOR:case Cursor.E_RESIZE_CURSOR:
       newLocation.y+=getComponent().getHeight()/2;
    };
    
    newLocation.x-=getWidth()/2;newLocation.y-=getHeight()/2;
    setLocation(translateComponentLocation2HandleLocation(newLocation));
  };
  protected Point translateComponentLocation2HandleLocation(Point p) {
    p=new Point(p);
    Component c=getComponent().getParent();
    
    for(;c instanceof Form;c=c.getParent())
      p.translate(c.getX(),c.getY());
    return p;
  };
  protected Point translateHandleLocation2ComponentLocation(Point p) {
    p=new Point(p);
    Component c=getComponent().getParent();
    
    for(;c instanceof Form;c=c.getParent())
      p.translate(-c.getX(),-c.getY());
    return p;
  };
  
  protected class BoundsChangeListener extends ComponentAdapter {

    public void componentMoved(ComponentEvent e)   {setLocation();};
    public void componentResized(ComponentEvent e) {setLocation();};
  };  
};

  
