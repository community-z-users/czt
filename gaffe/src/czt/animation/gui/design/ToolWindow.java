package czt.animation.gui.design;

import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.MouseEvent;
import java.awt.BorderLayout;
import java.awt.Component;
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

  protected Tool currentTool;
  public Tool getCurrentTool() {
    return currentTool;
  };
  protected void setCurrentTool(Tool t) {
    currentTool=t;
    fireToolChanged(currentTool);
  };
  
  protected EventListenerList toolChangeListeners;
  public void addToolChangeListener(ToolChangeListener l) {
    toolChangeListeners.add(ToolChangeListener.class, l);

    l.toolChanged(new ToolChangeEvent(this,currentTool));
  }
  
  public void removeToolChangeListener(ToolChangeListener l) {
    toolChangeListeners.remove(ToolChangeListener.class, l);
  }
  public ToolChangeListener[] getToolChangeListeners() {
    return (ToolChangeListener[])toolChangeListeners.getListeners(ToolChangeListener.class);
  };
  protected void fireToolChanged(Tool tool) {
    final ToolChangeListener[] listeners=getToolChangeListeners();
    final ToolChangeEvent ev=new ToolChangeEvent(this,tool);
    for(int i=0;i<listeners.length;i++) listeners[i].toolChanged(ev);
  };


  public ToolWindow() {
    this(new Class[] {});
  };
  public ToolWindow(Class[] beanTypes) {
    toolChangeListeners=new EventListenerList();
    tools=new Vector();
    tools.add(currentTool=new SelectBeanTool());
    tools.add(currentTool=new MoveBeanTool());
    
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

    private final Icon icon;
    private final String name;
    private final String description;
    private final Cursor cursor;
    private final JButton button;

    protected Tool(Icon icon, String name, String description) {
      this(icon,name,description,new Cursor(Cursor.DEFAULT_CURSOR));
    };
    protected Tool(Icon icon, String name, String description, Cursor cursor) {
      this.icon=icon;
      this.name=name;
      this.description=description;
      this.cursor=cursor;
      Action action=new AbstractAction(getIcon()==null?getName():null,getIcon()) {
	  public void actionPerformed(ActionEvent e) {setCurrentTool(Tool.this);};
	};
      action.putValue(Action.SHORT_DESCRIPTION,getDescription());
      button=new JButton(action);
    };
    
    public final JButton getButton()      {return button;};
    public final Cursor  getCursor()      {return cursor;};
    public final String  getDescription() {return description;};
    public final Icon    getIcon()        {return icon;};
    public final String  getName()        {return name;};

    public void mouseClicked (MouseEvent e, FormDesign f) {};
    public void mousePressed (MouseEvent e, FormDesign f) {};
    public void mouseReleased(MouseEvent e, FormDesign f) {};
    public void mouseEntered (MouseEvent e, FormDesign f) {};
    public void mouseExited  (MouseEvent e, FormDesign f) {};
    public void mouseDragged (MouseEvent e, FormDesign f) {};
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
      System.err.println("PlaceBeanTool.mousePressed(e,f)");
      beanInProgress=null;componentInProgress=null;
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
      if(f.mayAddBeanAt(beanInProgress,e.getPoint()))
	try {
	  componentInProgress=f.addBean(beanInProgress,e.getPoint());
	} catch (BeanOutOfBoundsException ex) {
	  throw new Error("FormDesign.addBean threw BeanOutOfBoundsException after bounds were "
			  +"checked.",ex);
	}
      else
	beanInProgress=null;
    }; 
    public void mouseDragged(MouseEvent e, FormDesign f) {
      System.err.println("PlaceBeanTool.mouseDragged(e,f)");
      if(beanInProgress==null) return;
      Dimension newSize=new Dimension(e.getX()-componentInProgress.getX(),
				      e.getY()-componentInProgress.getY());
      if(newSize.getWidth()<0)newSize.width=0;
      if(newSize.getHeight()<0)newSize.height=0;
      componentInProgress.setSize(newSize);
    };
    //XXX would be nice if these cursors could be static.
    private final Cursor OK_CURSOR=Cursor.getPredefinedCursor(Cursor.CROSSHAIR_CURSOR);
    private final Cursor NOT_OK_CURSOR=Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR);
    public void mouseMoved(MouseEvent e, FormDesign f) {
      System.err.println("PlaceBeanTool.mouseMoved(e,f)");
      if(f.mayAddBeanAt(type,e.getPoint())) f.setCursor(OK_CURSOR);
      else f.setCursor(NOT_OK_CURSOR);
    };
    public void mouseReleased(MouseEvent e, FormDesign f) {
      System.err.println("PlaceBeanTool.mouseReleased(e,f)");
      beanInProgress=null;
      componentInProgress=null;
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
    protected SelectBeanTool(Icon icon, String name, String description, Cursor cursor) {
      super(icon,name,description,cursor);
    };
    protected SelectBeanTool(Icon icon, String name, String description) {
      super(icon,name,description);
    };

    public synchronized void mousePressed(MouseEvent e, FormDesign f) {
      Component curr=f.getCurrentBeanComponent();
      Component clicked=f.getBeanPane().getComponentAt(e.getPoint());
      if(curr==clicked && curr==f.getForm()) {
	e.translatePoint(-curr.getX(),-curr.getY());
	clicked=curr.getComponentAt(e.getPoint());
      }
      f.setCurrentBeanComponent(clicked);
    };
//      public synchronized void mouseClicked(MouseEvent e, FormDesign f) {
//        Component curr=f.getCurrentBeanComponent();
//        Component clicked=f.getBeanPane().getComponentAt(e.getPoint());
//        if(curr==clicked && curr==f.getForm()) {
//  	e.translatePoint(-curr.getX(),-curr.getY());
//  	clicked=curr.getComponentAt(e.getPoint());
//        }
//        f.setCurrentBeanComponent(clicked);
//      };
  };


  protected class MoveBeanTool extends SelectBeanTool {
    public MoveBeanTool() {
      super(new ImageIcon(getToolkit()//XXX change to use javabeancontext's getSystemResource instead? 
			  .getImage(ClassLoader
				    .getSystemResource("czt/animation/gui/design/moveIcon.gif"))),
	    "Move",
	    "Move Beans",
	    new Cursor(Cursor.MOVE_CURSOR));
      //XXX some mechanism for making the cursor only appear above a bean would be nice.
    };

    protected Point clickDownPoint;
    protected Component clickDownBean;
    
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
      if(clickDownBean!=f.getBeanPane())
	clickDownBean.setLocation(clickDownBean.getX()+e.getX()-(int)clickDownPoint.getX(),
				  clickDownBean.getY()+e.getY()-(int)clickDownPoint.getY());
      clickDownPoint=e.getPoint();
    };
    public synchronized void mousePressed(MouseEvent e, FormDesign f) {
      super.mousePressed(e,f);
      clickDownPoint=e.getPoint();
      clickDownBean=f.getBeanPane().getComponentAt(clickDownPoint);
    };
    public synchronized void mouseReleased(MouseEvent e, FormDesign f) {
      super.mouseReleased(e,f);
      clickDownPoint=null;
      clickDownBean=null;
    };
  };


  public static void main(String[] args) {
    (new ToolWindow(new Class[] {JButton.class,JCheckBox.class,JLabel.class})).show();
    
  };
  
};
