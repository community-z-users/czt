/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.gui.design;

import java.awt.Color;                    import java.awt.Component;
import java.awt.Cursor;                   import java.awt.Point;
import java.awt.Rectangle;                 

import java.awt.event.ComponentAdapter;   import java.awt.event.ComponentEvent;
import java.awt.event.InputEvent;         import java.awt.event.MouseEvent;

import javax.swing.BorderFactory;         import javax.swing.JPanel;
import javax.swing.event.MouseInputAdapter;

/**
 * The component that acts as a resizing/moving handle for each bean in the FormDesign.
 * These handles are small squares that sit above the edges, corners, and center of their matching
 * bean.
 */
class BeanHandle extends JPanel {
  /**
   * The component on the content pane this handle is matched to.
   */
  protected Component component;
  /**
   * Which corner/edge this handle sits on.
   */
  protected final int corner;

  private final FormDesign formDesign;
  /**
   * Creates a BeanHandle without specifying which bean it is for.
   * @param corner The edge/corner to sit this handle on.
   */
  public BeanHandle(int corner,FormDesign formDesign) {this(null,corner,formDesign);};
  
  /**
   * Checks the invariant of this class.  That the corner has to be one of the 8 compass directions 
   * specified in Cursor.
   * @see java.awt.Cursor
   */
  protected void invariant() {
    switch(corner) {
     case Cursor.N_RESIZE_CURSOR:case Cursor.NW_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR: 
     case Cursor.S_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
     case Cursor.W_RESIZE_CURSOR:case Cursor.E_RESIZE_CURSOR: case Cursor.MOVE_CURSOR:break;
     default:
       throw new Error("Error: Invariant for BeanHandle broken "
		       +"- corner must be one of the move or compass point cursor numbers.");
    };
  };
  /**
   * Creates a BeanHandle for a particular component.
   * @param c the component to match this handle to.
   * @param corner The edge/corner to sit this handle on.
   */
  public BeanHandle(Component c, int corner, FormDesign formDesign) {
    setComponent(c);
    this.corner=corner;
    this.formDesign=formDesign;
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
   * Listener used to resize/move the matching component whenever this handle is dragged.
   */
  class DragListener extends MouseInputAdapter {
    /**
     * The point where a drag started.
     */
    protected Point clickDownPoint;
    
    /**
     * Resizes/moves the component. Inherited from MouseInputAdapter.
     */
    public synchronized void mouseDragged(MouseEvent e) {
      if((e.getModifiers()&InputEvent.BUTTON1_MASK)==0) return;
      Point mousePoint=e.getPoint();
      if(clickDownPoint==null) {
	System.err.println("### possible coding error###, "
			   +"mouseDragged in BeanHandle without press first");
	clickDownPoint=mousePoint;
	return;
      };
      mousePoint.translate((int)-clickDownPoint.x,(int)-clickDownPoint.y);
      Rectangle newBounds=getComponent().getBounds();
      switch(corner) {
       case Cursor.N_RESIZE_CURSOR:case Cursor.NW_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR:
	 if(mousePoint.getY()>newBounds.getHeight()) mousePoint.y=(int)newBounds.getHeight();
	 newBounds.height-=mousePoint.getY();
       case Cursor.MOVE_CURSOR:
	 newBounds.y+=mousePoint.getY();
	 break;
       case Cursor.S_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
	 if(-mousePoint.getY()>newBounds.getHeight()) mousePoint.y=(int)-newBounds.getHeight();
	 newBounds.height+=mousePoint.getY();
	 break;
      };
      switch(corner) {
       case Cursor.W_RESIZE_CURSOR:case Cursor.NW_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:
	 if(mousePoint.getX()>newBounds.width) mousePoint.x=(int)newBounds.getWidth();
	 newBounds.width-=mousePoint.getX();
       case Cursor.MOVE_CURSOR:
	 newBounds.x+=mousePoint.getX();
	 break;
       case Cursor.E_RESIZE_CURSOR:case Cursor.NE_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
	 if(-mousePoint.getX()>newBounds.getWidth()) mousePoint.x=(int)-newBounds.getWidth();
	 newBounds.width+=mousePoint.getX();
	 break;
      };
      
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
     case Cursor.N_RESIZE_CURSOR:case Cursor.S_RESIZE_CURSOR:case Cursor.MOVE_CURSOR:
       newLocation.x+=getComponent().getWidth()/2;
    };
    switch(corner) {
     case Cursor.S_RESIZE_CURSOR:case Cursor.SW_RESIZE_CURSOR:case Cursor.SE_RESIZE_CURSOR:
       newLocation.y+=getComponent().getHeight();
       break;
     case Cursor.W_RESIZE_CURSOR:case Cursor.E_RESIZE_CURSOR:case Cursor.MOVE_CURSOR:
       newLocation.y+=getComponent().getHeight()/2;
    };
    
    newLocation.x-=getWidth()/2;newLocation.y-=getHeight()/2;
    newLocation=formDesign.translateCoordinateFromCSpace(newLocation,getComponent().getParent());
    setLocation(newLocation);
    formDesign.repaint();
  };
  protected class BoundsChangeListener extends ComponentAdapter {
    public void componentMoved(ComponentEvent e)   {setLocation();};
    public void componentResized(ComponentEvent e) {setLocation();};
  };  
};
