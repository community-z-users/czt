package czt.animation.gui.design;

import java.beans.*;
import java.beans.beancontext.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import czt.animation.gui.*;
import czt.animation.gui.design.properties.PropertiesWindow;
import czt.animation.gui.util.IntrospectionHelper;
import java.util.*;
import java.io.IOException;

/**
 * Window for designing a form.
 * This class manages the placement of beans into a form, configuration of properties, and linking of 
 * beans with events.
 */
public class FormDesign extends JFrame {
  /**
   * The form being designed by this window
   */
  protected Form form;
  /**
   * The glass pane is used to block interaction with the beans/components being placed, and to draw
   * handles and other guides on top of the form being designed.<br>
   * <em>Note:</em> This glass pane is not the glass pane in this frame's root window.  It is part of a
   * layered panel placed inside the contentPane.  This is done because we don't want the glass pane to
   * go over the menu bar, tool bar, status bar, etc.
   */
  protected JPanel glassPane;
  /**
   * The content pane is used to contain the form being designed, and any beans (wrapped) that do not
   * visually appear within the form.<br>
   * <em>Note:</em> This is not the content pane of this frame's root window.
   */
  protected JPanel contentPane;
  /**
   * The properties window is used to display the properties, events, methods of the currently selected
   * bean; and to edit properties.
   */
  protected PropertiesWindow propertiesWindow;
  /**
   * The actions provided by the user interface in this window.
   */
  protected final ActionMap actionMap=new ActionMap();
  /**
   * A map from key strokes to action keys for this window.
   */
  protected final InputMap inputMap=new InputMap();

  /**
   * Support class for triggering property change events.
   */
  protected PropertyChangeSupport propertyChangeSupport=new PropertyChangeSupport(this);

  /**
   * The currently selected bean.
   */
  protected Object currentBean=null;
  

  /**
   * Setter method for the currentBean property.  Sets the currentBean property, makes the resize 
   * handles visible for only the current bean.
   */  
  public void setCurrentBean(Object t) {
    Object oldBean=currentBean;
    currentBean=t;
    propertiesWindow.setBean(t);
    propertyChangeSupport.firePropertyChange("currentBean",oldBean,currentBean);
    
    if(t==null)
      System.err.println("Current bean is now of type (null)");
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
  };
  /**
   * Getter method for the currentBean property.
   */
  public Object getCurrentBean() {
    return currentBean;
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
  protected BeanInfo currentTool=null;
  /**
   * Setter method for the currentTool property.
   */
  public void setCurrentTool(BeanInfo t) {
    BeanInfo oldTool=currentTool;
    currentTool=t;
    propertyChangeSupport.firePropertyChange("currentTool",oldTool,currentTool);
  };
  /**
   * Getter method for the currentTool property.
   */
  public BeanInfo getCurrentTool() {
    return currentTool;
  };
  
  
  /**
   * Sets up {@link #actionMap actionMap} and {@link #inputMap inputMap}.  Called once only from the 
   * constructor.
   */
  protected void setupActions() {
    Action action_quit;
    action_quit=new AbstractAction("Quit") {
	public void actionPerformed(ActionEvent e) {
	  dispose();
	  propertiesWindow.dispose();
	  
	  //XXX properly close all windows
	  System.exit(0);
	};
      };
    action_quit.putValue(Action.NAME,"Quit");
    action_quit.putValue(Action.SHORT_DESCRIPTION,"Quit");
    action_quit.putValue(Action.LONG_DESCRIPTION,"Quit");
    //XXX action_quit.putValue(Action.SMALL_ICON,...);
    //XXX action_quit.putValue(Action.ACTION_COMMAND_KEY,...);
    action_quit.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control Q"));
    //XXX action_quit.putValue(Action.MNEMONIC_KEY,...);
    
    //    actionMap=new ActionMap();
    actionMap.put("Quit",action_quit);

    inputMap.put((KeyStroke)actionMap.get("Quit").getValue(Action.ACCELERATOR_KEY),
		 "Quit");


    Action action_show_properties_window;
    action_show_properties_window=new AbstractAction("Show Properties Window") {
	public void actionPerformed(ActionEvent e) {
	  propertiesWindow.setVisible(true);
	  propertiesWindow.toFront();
	};
	
      };
    action_show_properties_window.putValue(Action.NAME,"Show Properties Window");
    action_show_properties_window.putValue(Action.SHORT_DESCRIPTION,"Show Properties Window");
    action_show_properties_window.putValue(Action.LONG_DESCRIPTION, "Show Properties Window");
    //XXX action_show_properties_window.putValue(Action.SMALL_ICON,...);
    //XXX action_show_properties_window.putValue(Action.ACTION_COMMAND_KEY,...);
    action_show_properties_window.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control P"));
    //XXX action_show_properties_window.putValue(Action.MNEMONIC_KEY,...);

    actionMap.put("Show Properties Window",action_show_properties_window);
    inputMap.put((KeyStroke)actionMap.get("Show Properties Window").getValue(Action.ACCELERATOR_KEY),
		 "Show Properties Window");

    
    Action action_show_about_dialog;
    action_show_about_dialog=new AbstractAction("About...") {
	public void actionPerformed(ActionEvent e) {
	  JOptionPane.showMessageDialog(FormDesign.this,"(c) XXX About message here","About GAfFE",JOptionPane.INFORMATION_MESSAGE);//XXX icon
	};
      };
    action_show_about_dialog.putValue(Action.NAME,"About...");
    action_show_about_dialog.putValue(Action.SHORT_DESCRIPTION,"Show About Dialog");
    action_show_about_dialog.putValue(Action.LONG_DESCRIPTION, "Show About Dialog");
    //XXX action_show_about_dialog.putValue(Action.SMALL_ICON,...);
    //XXX action_show_about_dialog.putValue(Action.ACTION_COMMAND_KEY,...);
    action_show_about_dialog.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control H"));
    //XXX action_show_about_dialog.putValue(Action.MNEMONIC_KEY,...);

    actionMap.put("About...",action_show_about_dialog);
    inputMap.put((KeyStroke)actionMap.get("About...").getValue(Action.ACCELERATOR_KEY),
		 "About...");
  };
  
  /**
   * Sets up the layering of {@link #glassPane glassPane} and {@link #contentPane contentPane}.
   * Called once only from the constructor.
   */
  protected void setupLayeredPanes() {
    JLayeredPane layeredPane=new JLayeredPane();
    layeredPane.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    //layeredPane.setBorder(BorderFactory.createLineBorder(Color.black));
    layeredPane.setLayout(new OverlayLayout(layeredPane));
    getContentPane().setLayout(new BorderLayout());
    getContentPane().add(layeredPane,BorderLayout.CENTER);

    contentPane=new JPanel(null);
    layeredPane.add(contentPane,new Integer(0));
    

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
  protected void setupMenus() {
    JMenuBar mb=new JMenuBar();
    JMenu file=new JMenu("File");
    file.setMnemonic(KeyEvent.VK_F);
    file.add(new JMenuItem(actionMap.get("Quit")));
    JMenu edit=new JMenu("Edit");
    edit.setMnemonic(KeyEvent.VK_E);
    JMenu window=new JMenu("Window");
    window.add(new JMenuItem(actionMap.get("Show Properties Window")));
    window.setMnemonic(KeyEvent.VK_W);
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
    final JLabel statusBar=new JLabel();
    statusBar.setBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
    
    if(getCurrentTool()==null)
      statusBar.setText("Current Tool: (none)");
    else
      statusBar.setText("Current Tool: "+currentTool.getBeanDescriptor().getDisplayName());
    PropertyChangeListener l=new PropertyChangeListener () {
	public void propertyChange(PropertyChangeEvent evt) {
	  String text="Current Tool: ";
	  if(getCurrentTool()==null)
	    text+="(none)";
	  else
	    text+=currentTool.getBeanDescriptor().getDisplayName();
	  text+="     Current Bean: ";
	  if(getCurrentBean()==null)
	    text+="(none)";
	  else {
	    if(IntrospectionHelper.beanHasReadableProperty(getCurrentBean(),"name")) { 
	      String name=(String)IntrospectionHelper.getBeanProperty(getCurrentBean(),"name");
	      if(name==null) 
		text+="(unnamed)";
	      else
		text+=name;
	    } else
	      text+="(unnamed)";
	    text+="("+getCurrentBean().getClass().getName()+")";
	    statusBar.setText(text);
	  }
	};
      };
    l.propertyChange(null);
    propertyChangeSupport.addPropertyChangeListener("currentTool",l);
    propertyChangeSupport.addPropertyChangeListener("currentBean",l);
    getContentPane().add(statusBar,BorderLayout.SOUTH);
  };
  /**
   * Sets up the tool bar.  Called once only from the constructor.
   */
  protected void setupToolbar() {
    final Class[] beanTypes={JButton.class,JCheckBox.class,JLabel.class};
    final Action[] beanActions=new Action[beanTypes.length];

    JToolBar toolbar=new JToolBar();
    toolbar.setFloatable(false);
    
    for(int i=0;i<beanTypes.length;i++) {
      try {
	final BeanInfo bi=Introspector.getBeanInfo(beanTypes[i]);
	final BeanDescriptor bd=bi.getBeanDescriptor();
	Image icon=bi.getIcon(BeanInfo.ICON_COLOR_16x16);
	if(icon==null)
	  icon=bi.getIcon(BeanInfo.ICON_MONO_16x16);
	if(icon==null)
	  icon=bi.getIcon(BeanInfo.ICON_COLOR_32x32);
	if(icon==null)
	  icon=bi.getIcon(BeanInfo.ICON_MONO_32x32);
	if(icon!=null) System.err.println("Found icon for"+bd.getName());
	
	beanActions[i]=new AbstractAction(bd.getDisplayName(),icon==null?null:new ImageIcon(icon)) {
	    public void actionPerformed(ActionEvent e) {
	      System.err.println("toolbar button '"+getValue(Action.NAME)+"' clicked");
	      setCurrentTool(bi);
	    };
	  };
	beanActions[i].putValue(Action.SHORT_DESCRIPTION,bd.getShortDescription());  
	
	toolbar.add(beanActions[i]);
      } catch (IntrospectionException e) {
	System.err.println("*** Introspection Exception while adding buttons ***");
	System.err.println(e);
      };
    };
    getContentPane().add(toolbar,BorderLayout.NORTH);
    
  };
  
  /**
   * Creates a new Form designer.
   */
  public FormDesign() {
    super("Design Mode: Main");

    setupActions();
    setupLayeredPanes();
    setupMenus();
    setupStatusBar();
    setupToolbar();
    propertiesWindow=new PropertiesWindow();
    propertyChangeSupport.addPropertyChangeListener("currentBean",propertiesWindow);
    handles=new HashMap();
    
    addWindowListener(new WindowAdapter() {
	public void windowClosing(WindowEvent e) {
	  //XXX a bit nasty, is there a better way to do this?
	  actionMap.get("Quit").actionPerformed(new ActionEvent(e,e.getID(),null,0));
	};
      });


    form=new Form("Main");
    form.setBounds(5,5,100,100);
    form.addPropertyChangeListener("name",new PropertyChangeListener() {
	public void propertyChange(PropertyChangeEvent evt) {
	  setTitle("Design Mode: "+form.getName());
	};
      });
    
    form.setBorder(BorderFactory.createTitledBorder(BorderFactory.createLineBorder(Color.black),form.getName()));
    contentPane.add(form);//XXX
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
    public MoveHandle m;
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
      glassPane.add(m=new MoveHandle(bean));
      m.addMouseListener(new MouseAdapter() {
	  public void mouseClicked(MouseEvent e) {
	    setCurrentBean(bean);
	  };
	});
      
      handles.put(bean,this);
      glassPane.repaint();
      
    };
  };
  
  /**
   * Mouse listener for the {@link #glassPane glass pane}.  Used mostly for creation of beans when 
   * the user clicks or drags directly on the glass pane.
   */
  protected class GPMouseListener extends MouseInputAdapter {
    /**
     * Inherited from MouseInputAdapter.  Creates a new bean of the type specified by currentTool.
     */
    public void mousePressed(MouseEvent e) {
      setCurrentBean(null);
      BeanInfo ct=getCurrentTool();
      if(ct==null) {
	System.err.println("No current tool");
	return;
      }
      System.err.println("Current tool is "+ct.getBeanDescriptor().getBeanClass().getName());
      
      Object bean;
      Component component;
      try {
	bean=Beans.instantiate(null,ct.getBeanDescriptor().getBeanClass().getName());
      } catch (ClassNotFoundException ex) {
	System.err.println("Couldn't instantiate an object for "+ct.getBeanDescriptor().getName());
	System.err.println(ex);//XXX do more reporting here
	return;
      } catch (IOException ex) {
	System.err.println("I/O error trying to load "+ct.getBeanDescriptor().getName());
	System.err.println(ex);//XXX do more reporting here
	return;
      };
      
      if(Beans.isInstanceOf(bean,Component.class)) {
	component=(Component) bean;
      } else {
	component=new BeanWrapper(bean);
      }
      
      ((BeanContext)form.getBeanContextProxy()).add(bean);
      component.setLocation(e.getPoint());
      contentPane.add(component);
      new HandleSet(component);
      setCurrentBean(component);      
    };
    /**
     * Inherited from MouseInputAdapter.  Resizes a just placed bean.
     */
    public void mouseDragged(MouseEvent e) {
      if(getCurrentBean()==null||getCurrentTool()==null) return;
      
      ResizeHandle se=((HandleSet)handles.get(getCurrentComponent())).se;
      Dimension newSize=new Dimension(e.getX()-getCurrentComponent().getX(),
				      e.getY()-getCurrentComponent().getY());
      if(newSize.getWidth()<0)newSize.width=0;
      if(newSize.getHeight()<0)newSize.height=0;
      getCurrentComponent().setSize(newSize);
    };
  };
  
  
  /**
   * For testing purposes.
   * Creates a new Design window.
   */
  public static void main(String args[]){//XXX testing only
    FormDesign fd=new FormDesign();
    fd.setSize(300,300);
    
    fd.show();
    try {
      Thread.sleep(2000);
    } catch (InterruptedException e) {
    };
    
    fd.form.setSize(200,200);
    
  };
  
  
};
