package czt.animation.gui.design;

import czt.animation.gui.Form;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;
import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Container;
import java.awt.Cursor;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Image;
import java.awt.Point;
import java.awt.Toolkit;
import java.beans.BeanInfo;
import java.beans.Beans;
import java.beans.BeanDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyChangeSupport;
import java.io.IOException;
import java.util.ListIterator;
import java.util.Vector;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.border.BevelBorder;
import javax.swing.BorderFactory;
import javax.swing.event.EventListenerList;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JPanel;

import javax.swing.JCheckBox;
import javax.swing.JLabel;

class ToolWindow extends JFrame {
  protected Vector tools; //Vector<Tool> tools
  protected JPanel nonBeanToolPanel;
  protected JPanel beanToolPanel;

  private Tool currentTool;
  public Tool getCurrentTool() {
    return currentTool;
  };
  protected void setCurrentTool(Tool t) {
    Tool oldTool=currentTool;
    currentTool=t;
    if(oldTool!=null)oldTool.unselected();
    if(currentTool!=null)currentTool.selected();
    fireToolChanged(currentTool,oldTool);
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


  public ToolWindow() {
    this(new Class[] {});
  };
  public ToolWindow(Class[] beanTypes) {
    toolChangeListeners=new EventListenerList();
    tools=new Vector();
    Tool tool;
    tool=new SelectBeanTool(); setCurrentTool(tool);tools.add(tool);
    tool=new MoveBeanTool(); setCurrentTool(tool);tools.add(tool);
    
    getContentPane().setLayout(new BorderLayout());
    getContentPane().add(nonBeanToolPanel=new JPanel(),BorderLayout.NORTH);
    nonBeanToolPanel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    getContentPane().add(beanToolPanel=new JPanel(),BorderLayout.CENTER);
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
    setSize(200,200);
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

    /**
     * Button is generated from the other information given.
     * @param icon Value for @{link #icon icon}.
     * @param name Value for @{link #name name}.
     * @param description Value for @{link #description description}.
     */
    protected Tool(Icon icon, String name, String description) {
      this.icon=icon;
      this.name=name;
      this.description=description;
      Action action=new AbstractAction(getIcon()==null?getName():null,getIcon()) {
	  public void actionPerformed(ActionEvent e) {setCurrentTool(Tool.this);};
	};
      action.putValue(Action.SHORT_DESCRIPTION,getDescription());
      button=new JButton(action);
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

    /**
     * Called by the <code>ToolWindow</code> when the <code>Tool</code> is selected.
     */
    public void selected() {};
    /**
     * Called by the <code>ToolWindow</code> when a different <code>Tool</code> is selected.
     */
    public void unselected() {};
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
    if(icon!=null) System.err.println("Found icon for"+bd.getDisplayName());
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
      
      Dimension newSize=new Dimension(e.getX()-componentInProgress.getX(),
				      e.getY()-componentInProgress.getY());
      if(newSize.getWidth()<0)newSize.width=0;
      if(newSize.getHeight()<0)newSize.height=0;
      componentInProgress.setSize(newSize);
      //XXX stop from resizing off side of parent?
    };
    public void mouseReleased(MouseEvent e, FormDesign f) {
      beanInProgress=componentInProgress=null;
    };
    
    public void mouseMoved(MouseEvent e, FormDesign f) {
      f.setCursor(Cursor.getPredefinedCursor(f.placementAllowed(e.getPoint(),type)?
					     Cursor.CROSSHAIR_CURSOR:
					     Cursor.DEFAULT_CURSOR));
    };
    public void unselected() {
      beanInProgress=componentInProgress=null;
    };
    public void unselected(FormDesign f) {
      f.setCursor(Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR));
    };
    
  };

  protected class SelectBeanTool extends Tool {
    public SelectBeanTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader
				    .getSystemResource("czt/animation/gui/design/selectIcon.gif"))),
	    "Select",
	    "Select Beans");
    };
    protected SelectBeanTool(Icon icon, String name, String description) {
      super(icon,name,description);
    };

    public synchronized void mousePressed(MouseEvent e, FormDesign f) {
      Component current=f.getCurrentBeanComponent();
      Point location=e.getPoint();
      if(current!=null && current instanceof Form) {
	Point translatedLocation=f.translateCoordinateToCSpace(location,(Container)current);
	if(current.contains(translatedLocation)) {
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


  protected class MoveBeanTool extends SelectBeanTool {
    public MoveBeanTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader
				    .getSystemResource("czt/animation/gui/design/moveIcon.gif"))),
	    "Move",
	    "Move Beans");
      //XXX some mechanism for making the cursor only appear above a bean would be nice.
    };

    protected Point clickDownPoint;
    protected Component clickDownBean;
    
    public void unselected(FormDesign f) {
      f.setCursor(Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR));      
    };

    public synchronized void mouseDragged(MouseEvent e, FormDesign f) {
      super.mouseDragged(e,f);
      if((e.getModifiers()&InputEvent.BUTTON1_MASK)==0) return;
      if(clickDownPoint==null) {
	System.err.println("### possible coding error###, "
			   +"mouseDragged in MoveBeanTool without press first");
	clickDownPoint=e.getPoint();
	clickDownBean=f.getBeanPane().getComponentAt(clickDownPoint);
	return;
      };
      if(clickDownBean!=null)
	clickDownBean.setLocation(clickDownBean.getX()+e.getX()-(int)clickDownPoint.getX(),
				  clickDownBean.getY()+e.getY()-(int)clickDownPoint.getY());
      clickDownPoint=e.getPoint();
    };
    public synchronized void mousePressed(MouseEvent e, FormDesign f) {
      Component current=f.getCurrentBeanComponent();
      //If we've clicked inside the current bean, we don't want to change what is selected.
      if(!current.getBounds().contains(f.translateCoordinateToCSpace(e.getPoint(),
								     current.getParent())))
	super.mousePressed(e,f);
      current=f.getCurrentBeanComponent();
      clickDownPoint=e.getPoint();
      if(f.getBeanPane().getComponentAt(e.getPoint())==f.getBeanPane()) clickDownBean=null;
      else clickDownBean=current;
    };

    public synchronized void mouseReleased(MouseEvent e, FormDesign f) {
      super.mouseReleased(e,f);
      clickDownPoint=null;
      clickDownBean=null;
    };

    public void mouseMoved(MouseEvent e, FormDesign f) {
      f.setCursor(Cursor.getPredefinedCursor((f.getBeanPane().getComponentAt(e.getPoint())
					      !=f.getBeanPane())?
					     Cursor.MOVE_CURSOR:
					     Cursor.DEFAULT_CURSOR));
    };
    
  };


  public static void main(String[] args) {
    (new ToolWindow(new Class[] {JButton.class,JCheckBox.class,JLabel.class})).show();
    
  };
  
};
