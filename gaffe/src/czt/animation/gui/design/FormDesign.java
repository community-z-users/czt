package czt.animation.gui.design;

import java.beans.*;
import java.beans.beancontext.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import czt.animation.gui.*;
import czt.animation.gui.util.IntrospectionHelper;
import java.util.*;
import java.io.IOException;

/**
 * Window for designing a form.
 * This class manages the placement of beans into a form, configuration of properties, and linking of 
 * beans with events.
 */
public class FormDesign extends JFrame implements ToolChangeListener {
  protected EventListenerList beanSelectedListeners=new EventListenerList();
  public void addBeanSelectedListener(BeanSelectedListener l) {
    beanSelectedListeners.add(BeanSelectedListener.class, l);
  };
  public void removeBeanSelectedListener(BeanSelectedListener l) {
    beanSelectedListeners.remove(BeanSelectedListener.class, l);
  };
  public BeanSelectedListener[] getBeanSelectedListeners() {
    return (BeanSelectedListener[])beanSelectedListeners.getListeners(BeanSelectedListener.class);
  };
  protected void fireBeanSelected(Object bean) {
    final BeanSelectedListener[] listeners=getBeanSelectedListeners();
    final BeanSelectedEvent ev=new BeanSelectedEvent(this,bean);
    for(int i=0;i<listeners.length;i++) listeners[i].beanSelected(ev);
  };

  /**
   * The form being designed by this window
   */
  protected Form form;
  
  public Form getForm() {
    return form;
  };
  
  /**
   * The glass pane is used to block interaction with the beans/components being placed, and to draw
   * handles and other guides on top of the form being designed.<br>
   * <em>Note:</em> This glass pane is not the glass pane in this frame's root window.  It is part of a
   * layered panel placed inside the contentPane.  This is done because we don't want the glass pane to
   * go over the menu bar, tool bar, status bar, etc.
   */
  protected JPanel glassPane;
  /**
   * The bean pane is used to contain the form being designed, and any beans (wrapped) that do not
   * visually appear within the form.<br>
   */
  protected JPanel beanPane;
  public JPanel getBeanPane() {return beanPane;};
  
  /**
   * The actions provided by the user interface in this window.
   */
  protected final ActionMap actionMap;
  /**
   * A map from key strokes to action keys for this window.
   */
  protected final InputMap inputMap;

  protected static class StatusBar extends JPanel {
    private JLabel beanLabel, toolLabel;
    public StatusBar() {
      this(null,null);
    }
    public StatusBar(Object bean, ToolWindow.Tool tool) {
      setLayout(new GridLayout(1,2));
      add(beanLabel=new JLabel());
      add(toolLabel=new JLabel());
      beanLabel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
      toolLabel.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
      setBean(bean);
      setTool(tool);
    };
    public void setBean(Object bean) {
      String beanName;
      if(bean==null) beanName="(none)";
      else {
	if(IntrospectionHelper.beanHasReadableProperty(bean,"name")) { 
	  beanName=(String)IntrospectionHelper.getBeanProperty(bean,"name");
	  if(beanName==null) 
	    beanName="(unnamed)";
	} else
	  beanName="(unnamed)";
      }
      beanLabel.setText("Current bean: "+beanName);
    };
    public void setTool(ToolWindow.Tool tool) {
      toolLabel.setText("Current tool: "+(tool==null?"(none)":tool.getName()));
    };
  };
  protected final StatusBar statusBar=new StatusBar();

  /**
   * The currently selected bean.
   */
  protected Object currentBean=null;

  public void unselectBean() {setCurrentBean(null);};
  
  /**
   * Setter method for the currentBean property.  Sets the currentBean property, makes the resize 
   * handles visible for only the current bean.
   */  
  public void setCurrentBean(Object t) {
    Object oldBean=currentBean;
    currentBean=t;
    if(currentBean!=null) fireBeanSelected(currentBean);

    if(t==null)
      System.err.println("Current bean is now (null)");
    else
      System.err.println("Current bean is now of type "+currentBean.getClass().getName());
    
    HandleSet hs;
    if(oldBean!=null) {
      hs=(HandleSet)handles.get(oldBean);
      if(hs!=null) hs.setResizeHandlesVisible(false);
    }
    if(currentBean!=null) {
      hs=(HandleSet)handles.get(currentBean);
      if(hs!=null) hs.setResizeHandlesVisible(true);
    }

    statusBar.setBean(t);
  };
  /**
   * Getter method for the currentBean property.
   */
  public Object getCurrentBean() {
    return currentBean;
  };
  public void addBean(Object bean, Point location) {
    ((BeanContext)form.getBeanContextProxy()).add(bean);
    Component component;
    if(Beans.isInstanceOf(bean,Component.class)) {
      component=(Component) bean;
    } else {
      component=new BeanWrapper(bean);
    }
    component.setLocation(location);
    getBeanPane().add(component);
    new HandleSet(component);
    setCurrentBean(component);
  };
  
  /**
   * Getter method for the currentComponent property.
   * The currentComponent property is equal to the currentBean property if the currentBean is a 
   * Component, otherwise it is a BeanWrapper wrapping the currentBean.
   * @see czt.animation.gui.design.BeanWrapper
   */
  public Component getCurrentComponent() {
    return (Component)currentBean;//XXX if not component should return BeanWrapper
  };
  
  /**
   * The currently selected tool.  It is a BeanInfo describing the bean type to place.
   */
  protected ToolWindow.Tool currentTool=null;
  public void toolChanged(ToolChangeEvent ev) {
    currentTool=ev.getTool();
    statusBar.setTool(ev.getTool());
  };


  /**
   * Getter method for the currentTool property.
   */
  public ToolWindow.Tool getCurrentTool() {
    return currentTool;
  };
  
  
  /**
   * Sets up the layering of {@link #glassPane glassPane} and {@link #beanPane beanPane}.
   * Called once only from the constructor.
   */
  protected void setupLayeredPanes() {
    JLayeredPane layeredPane=new JLayeredPane();
    layeredPane.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    //layeredPane.setBorder(BorderFactory.createLineBorder(Color.black));
    layeredPane.setLayout(new OverlayLayout(layeredPane));
    getContentPane().setLayout(new BorderLayout());
    getContentPane().add(layeredPane,BorderLayout.CENTER);

    beanPane=new JPanel(null);
    layeredPane.add(beanPane,new Integer(0));
    

    glassPane=new JPanel(null);
    layeredPane.add(glassPane,new Integer(1));
    glassPane.setOpaque(false);
    GPMouseListener gpml=new GPMouseListener();
    glassPane.addMouseListener(gpml);
    glassPane.addMouseMotionListener(gpml);

    layeredPane.setActionMap(actionMap);
    layeredPane.setInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT,inputMap);
  };
  /**
   * Sets up the menu bar.  Called once only from the constructor.
   */
  protected void setupMenus(JMenu window) {
    JMenuBar mb=new JMenuBar();
    JMenu file=new JMenu("File");
    file.setMnemonic(KeyEvent.VK_F);
    file.add(new JMenuItem(actionMap.get("Quit")));
    JMenu edit=new JMenu("Edit");
    edit.setMnemonic(KeyEvent.VK_E);
    JMenu help=new JMenu("Help");
    help.setMnemonic(KeyEvent.VK_H);
    help.add(new JMenuItem(actionMap.get("About...")));
    mb.add(file);
    mb.add(edit);
    mb.add(window);
    mb.add(Box.createHorizontalGlue());
    mb.add(help);
    setJMenuBar(mb);
  };
  /**
   * Sets up the status bar.  Called once only from the constructor.
   */
  protected void setupStatusBar() {
    getContentPane().add(statusBar,BorderLayout.SOUTH);
  };
  
  /**
   * Creates a new Form designer.
   */
  public FormDesign(ActionMap am, InputMap im, JMenu wm) {
    this("Main",am,im,wm);
  };
  
  public FormDesign(String name, ActionMap am, InputMap im, JMenu windowMenu) {
    super("Design Mode: "+name);

    actionMap=am;
    inputMap=im;
    setupLayeredPanes();
    setupMenus(windowMenu);
    setupStatusBar();
    handles=new HashMap();
    
    addWindowListener(new WindowAdapter() {
	public void windowClosing(WindowEvent e) {
	  //XXX a bit nasty, is there a better way to do this?
	  actionMap.get("Quit").actionPerformed(new ActionEvent(e,e.getID(),null,0));
	};
      });


    form=new Form(name);
    form.setBounds(5,5,100,100);
    form.addPropertyChangeListener("name",new PropertyChangeListener() {
	public void propertyChange(PropertyChangeEvent evt) {
	  setTitle("Design Mode: "+form.getName());
	};
      });
    
    form.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(Color.black),form.getName()));
    form.addPropertyChangeListener("name",new PropertyChangeListener() {
	public void propertyChange(PropertyChangeEvent evt) {
	  //XXX It seems that Component/JComponent etc, don't send an event when 'name' changes!
	  //    Should find a solution that will work.
	  System.err.println("``` source = "+evt.getSource());
	  System.err.println("``` propertyName = "+evt.getPropertyName());
	  System.err.println("``` newValue = "+evt.getNewValue());
	  ((TitledBorder)((Form)evt.getSource()).getBorder()).setTitle((String)evt.getNewValue());
	};
      });
    
    beanPane.add(form);//XXX
    new HandleSet(form);
    setCurrentBean(form);
    
  };
  
  /**
   * Mapping from beans in the design to their set of handles.
   */
  protected Map handles;//Map<Object, HandleSet> map from bean/component to handles
  
  /**
   * Class collecting together the eight resize handle, and one move handle belonging to a bean.
   */
  protected class HandleSet {
    /**
     * The corner and edge resize handles.  These appear as squares on the corners and edges of a bean.
     */
    public ResizeHandle n,ne,e,se,s,sw,w,nw;
    /**
     * The move handle.  This is a transparent handle that sits above the whole bean.
     */
//      public MoveHandle m;
    /**
     * Calls setVisible on all of the ResizeHandles.
     */
    public void setResizeHandlesVisible(boolean b) {
      n.setVisible(b);ne.setVisible(b);
      e.setVisible(b);se.setVisible(b);
      s.setVisible(b);sw.setVisible(b);
      w.setVisible(b);nw.setVisible(b);
    };
    
    /**
     * Creates a HandleSet, all of the handles that go in it, and a mouse adapter that sets the current
     * bean when it is clicked on.
     */
    public HandleSet(final Component bean) {
      glassPane.add(se=new ResizeHandle(bean,Cursor.SE_RESIZE_CURSOR));
      glassPane.add(s=new ResizeHandle(bean,Cursor.S_RESIZE_CURSOR));
      glassPane.add(e=new ResizeHandle(bean,Cursor.E_RESIZE_CURSOR));
      glassPane.add(sw=new ResizeHandle(bean,Cursor.SW_RESIZE_CURSOR));
      glassPane.add(ne=new ResizeHandle(bean,Cursor.NE_RESIZE_CURSOR));
      glassPane.add(n=new ResizeHandle(bean,Cursor.N_RESIZE_CURSOR));
      glassPane.add(w=new ResizeHandle(bean,Cursor.W_RESIZE_CURSOR));
      glassPane.add(nw=new ResizeHandle(bean,Cursor.NW_RESIZE_CURSOR));
//        glassPane.add(m=new MoveHandle(bean));
//        m.addMouseListener(new MouseAdapter() {
//  	  public void mouseClicked(MouseEvent e) {
//  	    setCurrentBean(bean);
//  	  };
//  	});
      
      handles.put(bean,this);
      glassPane.repaint();
      
    };
  };
  
  /**
   * Mouse listener for the {@link #glassPane glass pane}.  Used mostly for creation of beans when 
   * the user clicks or drags directly on the glass pane.
   */
  protected class GPMouseListener extends MouseInputAdapter {
    public void mouseClicked (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseClicked (e,FormDesign.this);
    };
    public void mousePressed (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mousePressed (e,FormDesign.this);
    };
    public void mouseReleased(MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseReleased(e,FormDesign.this);
    };
    public void mouseEntered (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseEntered (e,FormDesign.this);
    };
    public void mouseExited  (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseExited  (e,FormDesign.this);
    };
    public void mouseDragged (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseDragged (e,FormDesign.this);
    };
    public void mouseMoved   (MouseEvent e) {
      ToolWindow.Tool t=getCurrentTool();
      if(t!=null)t.mouseMoved   (e,FormDesign.this);
    };
  };  
};
