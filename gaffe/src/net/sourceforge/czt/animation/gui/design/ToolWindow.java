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

import java.awt.BorderLayout;             import java.awt.Color;
import java.awt.Component;                import java.awt.Container;                
import java.awt.Cursor;                   import java.awt.Dimension;                
import java.awt.FlowLayout;               import java.awt.Graphics;                 
import java.awt.Image;                    import java.awt.MediaTracker;             
import java.awt.Point;                    import java.awt.Toolkit;                  
import java.awt.Transparency;             

import java.awt.event.ActionEvent;        import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;

import java.beans.BeanInfo;               import java.beans.BeanDescriptor;
import java.beans.Beans;                  import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException; import java.beans.Introspector;
import java.beans.PropertyChangeSupport;  

import java.io.IOException;

import java.util.Iterator;                import java.util.ListIterator;            
import java.util.Vector;

import javax.swing.AbstractAction;        import javax.swing.Action;
import javax.swing.BorderFactory;         import javax.swing.BoxLayout;
import javax.swing.Icon; 
import javax.swing.ImageIcon;             import javax.swing.JButton;
import javax.swing.JFrame;                import javax.swing.JCheckBox;
import javax.swing.JLabel;                import javax.swing.JOptionPane;
import javax.swing.JPanel;                import javax.swing.JScrollPane;

import javax.swing.border.BevelBorder;    import javax.swing.border.Border;
import javax.swing.border.EtchedBorder;   

import javax.swing.event.EventListenerList;

import net.sourceforge.czt.animation.gui.Form;

class ToolWindow extends JFrame {
  protected Vector tools; //Vector<Tool> tools
  protected JPanel nonBeanToolPanel;
  protected JPanel beanToolPanel;

  private Tool currentTool;
  private final Tool defaultTool;
  public Tool getCurrentTool() {
    return currentTool;
  };
  protected void setCurrentTool(Tool t) {
    Tool oldTool=currentTool;
    currentTool=t;
    if(oldTool!=null)oldTool.unselected();
    if(currentTool!=null)currentTool.selected();
    fireToolChanged(currentTool,oldTool);
    if(currentTool!=null&&currentTool.isOneShot()&&currentTool!=defaultTool)
      setCurrentTool(defaultTool);
  };
  
  private EventListenerList toolChangeListeners;
  /**
   * Registers a <code>ToolChangeListener</code> with the <code>ToolWindow</code>.  
   * Note: it will send a toolChanged message to the listener (with the tool and oldTool parameters 
   * equal) when it is registered.
   */
  public void addToolChangeListener(ToolChangeListener l) {
    toolChangeListeners.add(ToolChangeListener.class, l);
    l.toolChanged(new ToolChangeEvent(this,getCurrentTool(),getCurrentTool()));
  }
  /**
   * Unregisters a <code>ToolChangeListener</code> with the <code>ToolWindow</code>.
   */
  public void removeToolChangeListener(ToolChangeListener l) {
    toolChangeListeners.remove(ToolChangeListener.class, l);
  }
  public ToolChangeListener[] getToolChangeListeners() {
    return (ToolChangeListener[])toolChangeListeners.getListeners(ToolChangeListener.class);
  };
  protected void fireToolChanged(Tool tool, Tool oldTool) {
    final ToolChangeListener[] listeners=getToolChangeListeners();
    final ToolChangeEvent ev=new ToolChangeEvent(this,tool, oldTool);
    for(int i=0;i<listeners.length;i++) listeners[i].toolChanged(ev);
  };
  Cursor crossCursor;
  private void setupCrossCursor() {
    MediaTracker mt=new MediaTracker(this);
    Image baseCursorImage=getToolkit()
      .getImage(ClassLoader.getSystemResource("net/sourceforge/czt/animation/gui/design/XCursor.gif"))
      .getScaledInstance(16,16,Image.SCALE_DEFAULT);;
    mt.addImage(baseCursorImage,0);
    try {
      mt.waitForID(0);
    } catch (InterruptedException ex) {
      System.err.println("Interrupted");//XXX
    };
    
    Dimension bestSize=getToolkit().getBestCursorSize(16,16);
    Image cursorImage=getGraphicsConfiguration().createCompatibleImage((int)bestSize.getWidth(),
								       (int)bestSize.getHeight(),
								       Transparency.BITMASK);
    mt.addImage(cursorImage,1);
    cursorImage.getGraphics().drawImage(baseCursorImage,0,0,null);
    try {
      mt.waitForID(1);
    } catch (InterruptedException ex) {
      System.err.println("Interrupted");//XXX
    };
    crossCursor=getToolkit().createCustomCursor(cursorImage,new Point(8,8),"CrossCursor");
  };
  
  public ToolWindow() {
    this(new Class[] {});
  };
  public ToolWindow(Class[] beanTypes) {
    setupCrossCursor();
    setTitle("GAfFE: Tool Window");
    toolChangeListeners=new EventListenerList();
    tools=new Vector();
    Tool tool;
    tool=new SelectBeanTool(); defaultTool=tool;setCurrentTool(tool);tools.add(tool);
    tool=new DeleteBeanTool(); tools.add(tool);
    tool=new MakeEventLinkTool(); tools.add(tool);
    tool=new DeleteEventLinkTool(); tools.add(tool);
    
    getContentPane().setLayout(new BoxLayout(getContentPane(),BoxLayout.Y_AXIS));
    getContentPane().add(nonBeanToolPanel=new JPanel());
    nonBeanToolPanel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    getContentPane().add(beanToolPanel=new JPanel());
    beanToolPanel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));//XXX title border?
    nonBeanToolPanel.setLayout(new FlowLayout());
    beanToolPanel.setLayout(new FlowLayout());
    
    for(ListIterator i=tools.listIterator();i.hasNext();)
      nonBeanToolPanel.add(((Tool)i.next()).getButton());

    for(int i=0;i<beanTypes.length;i++) 
      try {
	addBeanTool(beanTypes[i]);
      } catch (IntrospectionException ex) {
	//Do Nothing
      };
    //    setSize(200,200);
    pack();
  };
  

  public void addBeanTool(Class type) throws IntrospectionException {
    Tool tool=new PlaceBeanTool(type);
    tools.add(tool);
    beanToolPanel.add(tool.getButton());
  };
  public void removeBeanTool(Class type) {
    for(ListIterator i=tools.listIterator();i.hasNext();) {
      Tool tool=(Tool)i.next();
      if(tool instanceof PlaceBeanTool) if(((PlaceBeanTool)tool).getType().equals(type)) {
	beanToolPanel.remove(tool.getButton());
	i.remove();
      }
    }
  };

  public abstract class Tool {
    /**
     * <code>Icon</code> to display in the <code>ToolWindow</code> for this <code>Tool</code>
     */
    private final Icon icon;
    /**
     * Name of this tool.  Appears on the tool's button if there is no icon.
     */
    private final String name;
    /**
     * Short description of this tool.
     */
    private final String description;
    /**
     * Button to display in the <code>ToolWindow</code>
     */
    private final JButton button;
    private final Border buttonBorderSelected;
    private final Border buttonBorderUnselected;
    private final boolean oneShot;

    protected Tool(Icon icon, String name, String description) {
      this(icon,name,description,false);
    };
    
    /**
     * Button is generated from the other information given.
     * @param icon Value for @{link #icon icon}.
     * @param name Value for @{link #name name}.
     * @param description Value for @{link #description description}.
     */
    protected Tool(Icon icon, String name, String description, boolean oneShot) {
      this.icon=icon;
      this.name=name;
      this.description=description;
      this.oneShot=oneShot;
      Action action=new AbstractAction(getIcon()==null?getName():null,getIcon()) {
	  public void actionPerformed(ActionEvent e) {
	    if(getCurrentTool()==Tool.this)
	      setCurrentTool(defaultTool);
	    else
	      setCurrentTool(Tool.this);
	  };
	};
      action.putValue(Action.SHORT_DESCRIPTION,getDescription());
      button=new JButton(action);
      
      buttonBorderUnselected
	=BorderFactory.createCompoundBorder(BorderFactory.createBevelBorder(BevelBorder.RAISED),
					    BorderFactory.createEmptyBorder(5,5,5,5));
      buttonBorderSelected
	=BorderFactory.createCompoundBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED),
					    BorderFactory.createEmptyBorder(5,5,5,5));
      button.setBorder(buttonBorderUnselected);
    };
    
    /**
     * Getter function for {@link #button button}.
     */
    public final JButton getButton()      {return button;};
    /**
     * Getter function for {@link #description description}.
     */
    public final String  getDescription() {return description;};
    /**
     * Getter function for {@link #icon icon}.
     */
    public final Icon    getIcon()        {return icon;};
    /**
     * Getter function for {@link #name name}.
     */
    public final String  getName()        {return name;};
    
    public final boolean isOneShot()      {return oneShot;};
    
    /**
     * Called by the <code>ToolWindow</code> when the <code>Tool</code> is selected.
     */
    public void selected() {
      getButton().setBorder(buttonBorderSelected);
      getButton().setBackground(getButton().getBackground().darker());
      getButton().requestFocus();
    };
    /**
     * Called by the <code>ToolWindow</code> when a different <code>Tool</code> is selected.
     */
    public void unselected() {
      getButton().setBorder(buttonBorderUnselected);
      getButton().setBackground(getButton().getBackground().brighter());
    };
    /**
     * Called by the <code>FormDesign f</code> when the <code>Tool</code> is selected.
     */
    public void selected(FormDesign f) {};
    /**
     * Called by the <code>FormDesign f</code> when a different <code>Tool</code> is selected.
     */
    public void unselected(FormDesign f) {};
    
    /**
     * Called by the <code>FormDesign f</code> when it experiences a mouseClicked  event.
     */
    public void mouseClicked (MouseEvent e, FormDesign f) {};
    /**
     * Called by the <code>FormDesign f</code> when it experiences a mousePressed  event.
     */
    public void mousePressed (MouseEvent e, FormDesign f) {};
    /**
     * Called by the <code>FormDesign f</code> when it experiences a mouseReleased event.
     */
    public void mouseReleased(MouseEvent e, FormDesign f) {};
    /**
     * Called by the <code>FormDesign f</code> when it experiences a mouseEntered  event.
     */								     
    public void mouseEntered (MouseEvent e, FormDesign f) {};	     
    /**								     
     * Called by the <code>FormDesign f</code> when it experiences a mouseExited   event.
     */								     
    public void mouseExited  (MouseEvent e, FormDesign f) {};	     
    /**								     
     * Called by the <code>FormDesign f</code> when it experiences a mouseDragged  event.
     */								     
    public void mouseDragged (MouseEvent e, FormDesign f) {};	     
    /**								     
     * Called by the <code>FormDesign f</code> when it experiences a mouseMoved    event.
     */
    public void mouseMoved   (MouseEvent e, FormDesign f) {};    

    /**
     * Called by the <code>FormDesign f</code>'s glass pane when it experiences a paint event.
     */
    public void paint(Graphics g, FormDesign f) {};
  };

  //Not actually needed outside of PlaceBeanTool, but to be usable by PlaceBeanTool's constructor it 
  //needs to be static which isn't possible because PlaceBeanTool must be non-static!
  //XXX Is there a way around this? an ugly way around it could use an anonymous inner class with this
  //function.
  private static Icon getIconForType(Class type) throws IntrospectionException {
    final BeanInfo bi=Introspector.getBeanInfo(type);
    final BeanDescriptor bd=bi.getBeanDescriptor();
    
    Image icon;
    icon=bi.getIcon(BeanInfo.ICON_COLOR_32x32);
    if(icon==null)
      icon=bi.getIcon(BeanInfo.ICON_MONO_32x32);
    if(icon==null)
      icon=bi.getIcon(BeanInfo.ICON_COLOR_16x16);
    if(icon==null)
      icon=bi.getIcon(BeanInfo.ICON_MONO_16x16);
    return icon==null?null:new ImageIcon(icon);
  };

  protected class PlaceBeanTool extends Tool {
    protected final Class type;
    protected final BeanInfo beanInfo;
    public PlaceBeanTool(Class type) throws IntrospectionException {
      super(getIconForType(type),
	    Introspector.getBeanInfo(type).getBeanDescriptor().getDisplayName(),
	    Introspector.getBeanInfo(type).getBeanDescriptor().getShortDescription());
      beanInfo=Introspector.getBeanInfo(type);
      this.type=type;
    };
    public Class  getType() {return type;};

    protected Object beanInProgress=null;
    protected Component componentInProgress=null;

    public void mousePressed (MouseEvent e, FormDesign f) {
      if(!f.placementAllowed(e.getPoint(),type)) return;
      try {
	beanInProgress=Beans.instantiate(null,type.getName());
      } catch (ClassNotFoundException ex) {
	System.err.println("Couldn't instantiate an object for "+type.getName());
	System.err.println(ex);//XXX do more reporting here
	return;
      } catch (IOException ex) {
	System.err.println("I/O error trying to load "+type.getName());
	System.err.println(ex);//XXX do more reporting here
	return;
      };
      try {
	componentInProgress=f.addBean(beanInProgress,e.getPoint());
      } catch (BeanOutOfBoundsException ex) {
	beanInProgress=null;componentInProgress=null;
	throw new Error("FormDesign.addBean threw BeanOutOfBoundsException after bounds were "
			+"checked.",ex);
      }
    }; 
    public void mouseDragged(MouseEvent e, FormDesign f) {
      if(beanInProgress==null) return;
      if(componentInProgress==null) System.err.println("EH WHAT!!, componentInProgress=null, but beanInProgress doesn't!");
      
      Dimension newSize=new Dimension(e.getX()
				      -f.componentLocationInBeanPaneSpace(componentInProgress).x,
				      e.getY()
				      -f.componentLocationInBeanPaneSpace(componentInProgress).y);
      if(newSize.getWidth()<0)newSize.width=0;
      if(newSize.getHeight()<0)newSize.height=0;
      componentInProgress.setSize(newSize);
      //XXX stop from resizing off side of parent?
    };
    public void mouseReleased(MouseEvent e, FormDesign f) {
      beanInProgress=componentInProgress=null;
      setCurrentTool(defaultTool);
    };
    
    public void mouseMoved(MouseEvent e, FormDesign f) {
      f.setCursor(f.placementAllowed(e.getPoint(),type)?
		  Cursor.getPredefinedCursor(Cursor.CROSSHAIR_CURSOR):crossCursor);      
    };
    public void unselected() {
      super.unselected();
      beanInProgress=componentInProgress=null;
    };
    public void unselected(FormDesign f) {
      f.setCursor(Cursor.getDefaultCursor());
    };
    
  };

  protected class SelectBeanTool extends Tool {
    public SelectBeanTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader.getSystemResource(
                                "net/sourceforge/czt/animation/gui/design/selectIcon.gif"))),
	    "Select",
	    "Select Beans");
    };
    protected SelectBeanTool(Icon icon, String name, String description) {
      super(icon,name,description);
    };

    public synchronized void mousePressed(MouseEvent e, FormDesign f) {
      Component current=f.getCurrentBeanComponent();
      Point location=e.getPoint();
      if(current!=null && current instanceof Container) {
	Point translatedLocation=f.translateCoordinateToCSpace(location,current);
	if(current.contains(translatedLocation)) {
	  if(current instanceof JScrollPane) {
	    f.setCurrentBeanComponent(((JScrollPane)current).getViewport().getView());
	    return;
	  }
	  Component c=current.getComponentAt(translatedLocation);
	  if(c!=current) {
	    f.setCurrentBeanComponent(c);
	    return;
	  }
	}
      }
      Component c=f.getBeanPane().getComponentAt(e.getPoint());
      if(c!=f.getBeanPane())
	f.setCurrentBeanComponent(c);
    };
  };

  protected class DeleteBeanTool extends Tool {
    public DeleteBeanTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader.getSystemResource(
                                "net/sourceforge/czt/animation/gui/design/deleteIcon.gif"))),
	    "Delete",
	    "Delete Selected Bean",true);
    };

    public void selected(FormDesign f) {
      if(f.getCurrentBean()!=null) 
	if(!f.removeCurrentBean())getToolkit().beep();
    };
  };

  protected class MakeEventLinkTool extends Tool {
    public MakeEventLinkTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader.getSystemResource(
                                "net/sourceforge/czt/animation/gui/design/eventIcon.gif"))),
	    "Event",
	    "Link a bean to a listener bean",false);
    };
    
    private BeanInfo sourceInfo;
    private Component source;
    private Object sourceBean;

    private BeanInfo listenerInfo;
    private Component listener;
    private Object listenerBean;

    private Point lastMousePoint;

    private void getSource(MouseEvent e, FormDesign f) {
      source=f.lowestComponentAt(e.getPoint());
      if(source==null) {
	sourceBean=null;
	sourceInfo=null;
	return;
      } 
      
      sourceBean=BeanWrapper.getBean(source);
      try {
	sourceInfo=Introspector.getBeanInfo(sourceBean.getClass());
      } catch (IntrospectionException ex) {
	sourceInfo=null;
      }
    };
    private void getListener(MouseEvent e, FormDesign f) {
      listener=f.lowestComponentAt(e.getPoint());
      if(listener==null) {
	listenerBean=null;
	listenerInfo=null;
	return;
      } 
      
      listenerBean=BeanWrapper.getBean(listener);
      try {
	listenerInfo=Introspector.getBeanInfo(listenerBean.getClass());
      } catch (IntrospectionException ex) {
	listenerInfo=null;
      }
    };

    public void mouseMoved(MouseEvent e, FormDesign f) {
      getSource(e,f);
      lastMousePoint=e.getPoint();
      if(sourceInfo!=null&&sourceInfo.getEventSetDescriptors().length>0)
	f.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
      else 
	f.setCursor(crossCursor);
    };
    
    public void mousePressed(MouseEvent e, FormDesign f) {
      getSource(e,f);
      lastMousePoint=e.getPoint();
    };

    public void mouseDragged(MouseEvent e, FormDesign f) {
      getListener(e,f);
      lastMousePoint=e.getPoint();
      f.repaint();
      if(sourceInfo!=null && listenerBean!=null) {
	EventSetDescriptor[] esds=sourceInfo.getEventSetDescriptors();
	for(int i=0;i<esds.length;i++) {
	  Class ltype=esds[i].getListenerType();
	  if(ltype.isAssignableFrom(listenerBean.getClass())) {
	    f.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
	    return;
	  }
	}
      }
      f.setCursor(crossCursor);
    };
    
    public void mouseReleased(MouseEvent e, FormDesign f) {
      getListener(e,f);

      Vector/*<Class>*/ approvedListenerTypes=new Vector();
      if(sourceInfo!=null && listenerBean!=null) {
	EventSetDescriptor[] esds=sourceInfo.getEventSetDescriptors();
	for(int i=0;i<esds.length;i++) {
	  Class ltype=esds[i].getListenerType();
	  if(ltype.isAssignableFrom(listenerBean.getClass())) {
	    approvedListenerTypes.add(ltype);
	  }
	}
      };
      if(approvedListenerTypes.size()==0)
	getToolkit().beep();
      else {
	lastMousePoint=f.componentLocationInBeanPaneSpace(listener);
	lastMousePoint.translate(listener.getWidth()/2,listener.getHeight()/2);
	f.repaint();
	//XXX different dialog if there's only one approvedListenerType?
	//XXX highlight the two beans?
	Class chosenListenerType
	  =(Class)JOptionPane.showInputDialog(f,//Parent window
					      "Register listener as type:",//Message
					      "Listener type selection",//Dialog title
					      JOptionPane.QUESTION_MESSAGE,//Message type
					      null,//icon
					      approvedListenerTypes.toArray(),//options
					      approvedListenerTypes.get(0));//default option
	if(chosenListenerType!=null)
	  f.addEventLink(source,listener,chosenListenerType);
      }
      f.repaint();
      source=listener=null;
      sourceBean=listenerBean=null;
      sourceInfo=listenerInfo=null;
      lastMousePoint=null;
      setCurrentTool(defaultTool);
    };
    
    public void unselected(FormDesign f) {
      f.setCursor(Cursor.getDefaultCursor());
    };
    
    public void paint(Graphics g, FormDesign f) {
      if(source==null) return;
      Point sp=f.componentLocationInBeanPaneSpace(source);
      g.setColor(Color.green);
      g.drawLine(sp.x+source.getWidth()/2,sp.y+source.getHeight()/2,
		 lastMousePoint.x,lastMousePoint.y);
    };
    
  };

  protected class DeleteEventLinkTool extends Tool {
    public DeleteEventLinkTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader.getSystemResource(
                                "net/sourceforge/czt/animation/gui/design/deleteEventIcon.gif"))),
	    "Delete Event",
	    "Delete an event link",false);
    };
    public void selected(FormDesign f) {
      f.setEventLinkHighlightingOverride(true);
    };
    
    public void mouseMoved(MouseEvent e, FormDesign f) {
      for(Iterator linkIt=f.getEventLinks().iterator();linkIt.hasNext();) {
	FormDesign.BeanLink bl=(FormDesign.BeanLink)linkIt.next();
	if(f.getVisualLine(bl).ptSegDist(e.getPoint())<5) {
	  f.setCursor(Cursor.getDefaultCursor());
	  return;
	};
      }
      f.setCursor(crossCursor);
    };
    public void mouseClicked(MouseEvent e, FormDesign f) {
      for(Iterator linkIt=f.getEventLinks().iterator();linkIt.hasNext();) {
	FormDesign.BeanLink bl=(FormDesign.BeanLink)linkIt.next();
	if(f.getVisualLine(bl).ptSegDist(e.getPoint())<5) {
	  f.removeEventLink(bl);
	  setCurrentTool(defaultTool);      
	  return;
	};
      }
      getToolkit().beep();
      setCurrentTool(defaultTool);
    };
    

    public void unselected(FormDesign f) {
      f.setEventLinkHighlightingOverride(false);
      f.setCursor(Cursor.getDefaultCursor());
    };
    
    
    
  };  

  public static void main(String[] args) {
    (new ToolWindow(new Class[] {JButton.class,JCheckBox.class,JLabel.class})).show();
    
  };
  
};
