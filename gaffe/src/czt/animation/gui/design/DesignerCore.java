package czt.animation.gui.design;

import czt.animation.gui.Form;

import czt.animation.gui.design.FormDesign;
import czt.animation.gui.design.ToolWindow;

import czt.animation.gui.design.properties.PropertiesWindow;

import czt.animation.gui.persistence.delegates.BeanWrapperDelegate;
import czt.animation.gui.persistence.delegates.FormDelegate;

import czt.animation.gui.scripting.ScriptDelegate;

import java.awt.event.ActionEvent;        import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;      import java.awt.event.WindowEvent;

import java.beans.ExceptionListener;
import java.beans.XMLDecoder;             import java.beans.XMLEncoder;

import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextProxy;
import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;
import java.beans.beancontext.BeanContextServicesSupport;

import java.util.EventListener;           import java.util.HashMap;
import java.util.Iterator;                import java.util.List;
import java.util.ListIterator;            import java.util.Vector;

import java.io.File;                      import java.io.FileInputStream;
import java.io.FileOutputStream;          import java.io.FileNotFoundException;     
import java.io.IOException;

import javax.swing.AbstractAction;        import javax.swing.Action;
import javax.swing.ActionMap;             import javax.swing.InputMap;
import javax.swing.JButton;               import javax.swing.JCheckBox;
import javax.swing.JFileChooser;          import javax.swing.JLabel;                
import javax.swing.JMenu;                 import javax.swing.JMenuItem;             
import javax.swing.JOptionPane;           import javax.swing.KeyStroke;

import javax.swing.event.EventListenerList;

public class DesignerCore implements BeanContextProxy {

  public static int run(String[] args) {
    new DesignerCore();
    return 0;
  };
  
  private BeanContextServicesSupport bcsSupport;
  public BeanContextChild getBeanContextProxy() {return bcsSupport;};

  private final List forms;//List<FormDesign>
  private FormDesign currentBeansForm;
  protected FormDesign getSelectedBeansForm() {return currentBeansForm;};
  private Object currentBean;
  protected Object getSelectedBean() {return currentBean;};

  private final ToolWindow toolWindow;
  public ToolWindow getToolWindow() {return toolWindow;};

  private final PropertiesWindow propertiesWindow=new PropertiesWindow();
  public PropertiesWindow getPropertiesWindow() {return propertiesWindow;};
  
  private EventListenerList listenerSupport=new EventListenerList();
  
  public void addFormDesignListener(FormDesignListener l) {
    for(Iterator i=forms.iterator();i.hasNext();)
      l.formCreated(new FormDesignEvent(this,(FormDesign)i.next(),FormDesignEvent.CREATED));
    listenerSupport.add(FormDesignListener.class,l);
  };
  public void removeFormDesignListener(FormDesignListener l) {
    listenerSupport.remove(FormDesignListener.class,l);
  };
  protected void fireFormCreated(FormDesign f) {
    EventListener[] list=listenerSupport.getListeners(FormDesignListener.class);
    FormDesignEvent ev=new FormDesignEvent(this,f,FormDesignEvent.CREATED);
    for(int i=0;i<list.length;i++)
      ((FormDesignListener)list[i]).formCreated(ev);
  };
  protected void fireFormDeleted(FormDesign f) {
    EventListener[] list=listenerSupport.getListeners(FormDesignListener.class);
    FormDesignEvent ev=new FormDesignEvent(this,f,FormDesignEvent.DELETED);
    for(int i=0;i<list.length;i++)
      ((FormDesignListener)list[i]).formDeleted(ev);
  };
  
  

  public DesignerCore() {
    forms=new Vector();//List<FormDesign>
    currentBeansForm=null; currentBean=null;

    //XXX classes should come from a settings file or something
    toolWindow=new ToolWindow(new Class[] {JButton.class,JCheckBox.class,JLabel.class,
					   ScriptDelegate.class});
    setupActions();
    
    bcsSupport=new BeanContextServicesSupport();
    bcsSupport.addService(DesignerCore.class,new BeanContextServiceProvider() {
	public Object getService(BeanContextServices bcs, Object requestor, Class serviceClass,
				 Object serviceSelector) {
	  return DesignerCore.this;
	};
	public void releaseService(BeanContextServices bcs, Object requestor, Object service) {
	};
	public Iterator getCurrentServiceSelectors(BeanContextServices bcs, Class serviceClass) {
	  return null;
	};
      });
    bcsSupport.addService(ToolWindow.class,new BeanContextServiceProvider() {
	public Object getService(BeanContextServices bcs, Object requestor, Class serviceClass,
				 Object serviceSelector) {
	  return getToolWindow();
	};
	public void releaseService(BeanContextServices bcs, Object requestor, Object service) {
	};
	public Iterator getCurrentServiceSelectors(BeanContextServices bcs, Class serviceClass) {
	  return null;
	};
      });
    
    FormDesign firstForm=createNewForm("Main");
    firstForm.show();
    propertiesWindow.beanSelected(new BeanSelectedEvent(firstForm,firstForm.getForm()));
    beanSelectListener.beanSelected(new BeanSelectedEvent(firstForm,firstForm.getForm()));
  };
  
  private final BeanSelectedListener beanSelectListener =new BeanSelectedListener() {
      public void beanSelected(BeanSelectedEvent ev) {
	currentBeansForm=ev.getSelectedBeansForm();
	currentBean=getSelectedBean();
	for(ListIterator i=forms.listIterator();i.hasNext();) {
	  FormDesign fd=(FormDesign)i.next();
	  if(fd!=currentBeansForm) fd.unselectBean();
	};
      };
    };
  public FormDesign createNewForm(String name) {
    FormDesign form=new FormDesign(name, actionMap, inputMap, setupWindowMenu(),this);
    addForm(form);
    return form;
  };
  public void addForm(FormDesign form) {
    forms.add(form);
    //Add to windows menu/other structures
    form.addBeanSelectedListener(beanSelectListener);
    form.addBeanSelectedListener(propertiesWindow);

    //If the last window closes we will want the program to quit.
    form.addWindowListener(new WindowAdapter() {
	public void windowClosing(WindowEvent ev) {
	  Vector v=getVisibleForms();
	  
	  v.remove(ev.getWindow());
	  if(v.isEmpty()) {
	    if(JOptionPane.showConfirmDialog(ev.getWindow(),
					     "Closing the last design window will exit the program.\n"
					     +"Are you sure you want to do this?"
					     +"\n",
					     "Confirm exit",
					     JOptionPane.YES_NO_OPTION)==JOptionPane.NO_OPTION) {
	      ev.getWindow().setVisible(true);
	      return;
	    }
	    actionMap.get("Quit").actionPerformed(new ActionEvent(ev,ev.getID(),null,0));
	  }
	  ev.getWindow().setVisible(false);
	};
      });
			   
    toolWindow.addToolChangeListener(form);
    form.setSize(300,300);
    form.setVisible(true);
    fireFormCreated(form);
  };

  public Vector/*<FormDesign>*/ getVisibleForms() {
    Vector result=new Vector(forms);
    
    for(Iterator i=result.iterator();i.hasNext();)
      if(!((FormDesign)i.next()).isVisible()) i.remove();
    return result;
  };
  
  public int getNumberVisibleForms() {
    return getVisibleForms().size();
  };
  public boolean isNoVisibleForms() {
    return getVisibleForms().isEmpty();
  };
  
  
  public void removeForm(FormDesign form) {
    form.setVisible(false);
    forms.remove(form);
    toolWindow.removeToolChangeListener(form);
    form.removeBeanSelectedListener(beanSelectListener);
    form.removeBeanSelectedListener(propertiesWindow);
    fireFormDeleted(form);
  };
  

  protected final ActionMap actionMap=new ActionMap();
  protected final InputMap inputMap=new InputMap();
  protected void setupActions() {
    Action action_new_form;
    action_new_form=new AbstractAction("New Form") {
	private int i=1;
	public void actionPerformed(ActionEvent e) {
	  createNewForm("Form"+i).show();
	  i++;
	};
      };
    action_new_form.putValue(Action.NAME,"New Form");
    action_new_form.putValue(Action.SHORT_DESCRIPTION,"New Form");
    action_new_form.putValue(Action.LONG_DESCRIPTION,"New Form");
    //XXX action_new_form.putValue(Action.SMALL_ICON,...);
    //XXX action_new_form.putValue(Action.ACTION_COMMAND_KEY,...);
    action_new_form.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control N"));
    //XXX action_new_form.putValue(Action.MNEMONIC_KEY,...);
    
    actionMap.put("New Form",action_new_form);

    inputMap.put((KeyStroke)actionMap.get("New Form").getValue(Action.ACCELERATOR_KEY),
		 "New Form");


    Action action_quit;
    action_quit=new AbstractAction("Quit") {
	public void actionPerformed(ActionEvent e) {
	  for(ListIterator i=forms.listIterator();i.hasNext();((FormDesign)i.next()).dispose());
	  propertiesWindow.dispose();
	  toolWindow.dispose();
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

    Action action_show_toolbox_window;
    action_show_toolbox_window=new AbstractAction("Show Toolbox Window") {
	public void actionPerformed(ActionEvent e) {
	  toolWindow.setVisible(true);
	  toolWindow.toFront();
	};
      };
    action_show_toolbox_window.putValue(Action.NAME,"Show Toolbox Window");
    action_show_toolbox_window.putValue(Action.SHORT_DESCRIPTION,"Show Toolbox Window");
    action_show_toolbox_window.putValue(Action.LONG_DESCRIPTION, "Show Toolbox Window");
    //XXX action_show_toolbox_window.putValue(Action.SMALL_ICON,...);
    //XXX action_show_toolbox_window.putValue(Action.ACTION_COMMAND_KEY,...);
    action_show_toolbox_window.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control T"));
    //XXX action_show_toolbox_window..putValue(Action.MNEMONIC_KEY,...);

    actionMap.put("Show Toolbox Window",action_show_toolbox_window);
    inputMap.put((KeyStroke)actionMap.get("Show Toolbox Window").getValue(Action.ACCELERATOR_KEY),
		 "Show Toolbox Window");

    Action action_show_about_dialog;
    action_show_about_dialog=new AbstractAction("About...") {
	public void actionPerformed(ActionEvent e) {
	  JOptionPane.showMessageDialog(null,"(c) XXX About message here","About GAfFE",JOptionPane.INFORMATION_MESSAGE);//XXX icon, chose better frame
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
    
    
    Action action_save_forms;
    action_save_forms=new AbstractAction("Save...") {
	public void actionPerformed(ActionEvent e) {
	  JFileChooser fc=new JFileChooser();
	  if(fc.showSaveDialog(null)!=JFileChooser.APPROVE_OPTION) 
	    return;
	  File file=fc.getSelectedFile();
	  XMLEncoder encoder;
	  try {
	    encoder=new XMLEncoder(new FileOutputStream(file));
	  } catch (FileNotFoundException ex) {
	    JOptionPane.showMessageDialog(null,"File not found:"+ex,"File not found",
					  JOptionPane.ERROR_MESSAGE);
	    return;
	  }
	  encoder.setExceptionListener(new ExceptionListener() {
	      public void exceptionThrown(Exception ex) {
		System.err.println("### Exception ###");
		ex.printStackTrace();
	      };
	    });
	  
	  //	  encoder.setPersistenceDelegate(Form.class,new FormDelegate());
	  for(Iterator i=forms.iterator();i.hasNext();) {
	    //	    Form form=((FormDesign)i.next()).getForm();
	    //	    encoder.writeObject(form);
	    ((FormDesign)i.next()).saveDesign(encoder);
	  }
	  encoder.close();
	};
      };
    action_save_forms.putValue(Action.NAME,"Save...");
    action_save_forms.putValue(Action.SHORT_DESCRIPTION,"Save all forms");
    action_save_forms.putValue(Action.LONG_DESCRIPTION, "Save all forms");
    //XXX action_save_forms.putValue(Action.SMALL_ICON,...);
    //XXX action_save_forms.putValue(Action.ACTION_COMMAND_KEY,...);
    action_save_forms.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control S"));
    //XXX action_save_forms.putValue(Action.MNEMONIC_KEY,...);

    actionMap.put("Save...",action_save_forms);
    inputMap.put((KeyStroke)actionMap.get("Save...").getValue(Action.ACCELERATOR_KEY),
		 "Save...");


    Action action_open_forms;
    action_open_forms=new AbstractAction("Open...") {
	public void actionPerformed(ActionEvent e) {
	  //XXX Change to delegate to a delete all forms action?
	  if(JOptionPane.showConfirmDialog(null,
					   "Opening an interface design will clear all other designs."
					   +"\n"
					   +"Are you sure you want to do this?\n",
					   "Confirm delete all current forms",
					   JOptionPane.YES_NO_OPTION)==JOptionPane.NO_OPTION)
	    return;

//  	  JOptionPane.showOptionDialog(null,"Opening the file...","Opening...",JOptionPane.DEFAULT_OPTION,JOptionPane.INFORMATION_MESSAGE,null,new Object[] {},null);
	  JFileChooser fc=new JFileChooser();
	  if(fc.showOpenDialog(null)!=JFileChooser.APPROVE_OPTION) 
	    return;
	  Vector formDesigns=readFile(fc.getSelectedFile());

	  //We got nothing from the file, so we'll leave the current designs.
	  if(formDesigns.isEmpty()) return;

	  //Delete the old forms.
	  while(!forms.isEmpty()) removeForm((FormDesign)forms.get(0));
	  //Display the new forms.
	  for(Iterator it=formDesigns.iterator();it.hasNext();addForm((FormDesign)it.next()));
	};
      };
    action_open_forms.putValue(Action.NAME,"Open...");
    action_open_forms.putValue(Action.SHORT_DESCRIPTION,
			       "Open an interface design, deleting the current design.");
    action_open_forms.putValue(Action.LONG_DESCRIPTION, 
			       "Open an interface design, deleting the current design.");
    //XXX action_open_forms.putValue(Action.SMALL_ICON,...);
    //XXX action_open_forms.putValue(Action.ACTION_COMMAND_KEY,...);
    action_open_forms.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control O"));
    //XXX action_open_forms.putValue(Action.MNEMONIC_KEY,...);

    actionMap.put("Open...",action_open_forms);
    inputMap.put((KeyStroke)actionMap.get("Open...").getValue(Action.ACCELERATOR_KEY),
		 "Open...");


    Action action_import_forms;
    action_import_forms=new AbstractAction("Import...") {
	public void actionPerformed(ActionEvent e) {
	  JFileChooser fc=new JFileChooser();
	  if(fc.showOpenDialog(null)!=JFileChooser.APPROVE_OPTION) 
	    return;
	  Vector formDesigns=readFile(fc.getSelectedFile());
	  for(Iterator it=formDesigns.iterator();it.hasNext();addForm((FormDesign)it.next()));
	};
      };
    action_import_forms.putValue(Action.NAME,"Import...");
    action_import_forms.putValue(Action.SHORT_DESCRIPTION,
				 "Import an interface, adding to the current interface.");
    action_import_forms.putValue(Action.LONG_DESCRIPTION, 
				 "Import an interface, adding to the current interface.");
    //XXX action_import_forms.putValue(Action.SMALL_ICON,...);
    //XXX action_import_forms.putValue(Action.ACTION_COMMAND_KEY,...);
    action_import_forms.putValue(Action.ACCELERATOR_KEY,KeyStroke.getKeyStroke("control I"));
    //XXX action_import_forms.putValue(Action.MNEMONIC_KEY,...);

    actionMap.put("Import...",action_import_forms);
    inputMap.put((KeyStroke)actionMap.get("Import...").getValue(Action.ACCELERATOR_KEY),
		 "Import...");
  };

  protected Vector/*<FormDesign>*/ readFile(File file) {
    XMLDecoder decoder;
    try {
      decoder=new XMLDecoder(new FileInputStream(file));
    } catch (FileNotFoundException ex) {
      JOptionPane.showMessageDialog(null,"File not found:"+ex,"File not found",
				    JOptionPane.ERROR_MESSAGE);
      return new Vector();
    }
    Vector formDesigns=new Vector();
    try {
      while(true) {
	formDesigns.add(FormDesign.loadDesign(decoder,actionMap,inputMap,setupWindowMenu(),
					      DesignerCore.this));
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
    };
    decoder.close();
    if(formDesigns.isEmpty()) 
      JOptionPane.showMessageDialog(null,"File contains no form designs","Bad or empty file",
				    JOptionPane.ERROR_MESSAGE);
    return formDesigns;
  };
  
  


  protected JMenu setupWindowMenu() {
    final JMenu windowMenu=new JMenu("Window");
    windowMenu.add(new JMenuItem(actionMap.get("Show Properties Window")));
    windowMenu.add(new JMenuItem(actionMap.get("Show Toolbox Window")));
    windowMenu.setMnemonic(KeyEvent.VK_W);
    windowMenu.addSeparator();
    addFormDesignListener(new FormDesignListener() {
	private HashMap/*<Action,JMenuItem>*/ map=new HashMap();
	public void formCreated(FormDesignEvent e) {
	  JMenuItem mi=new JMenuItem(e.getFormDesign().getRaiseAction());
	  windowMenu.add(mi);
	  map.put(e.getFormDesign().getRaiseAction(),mi);
	};
	public void formDeleted(FormDesignEvent e) {
	  windowMenu.remove((JMenuItem)map.get(e.getFormDesign().getRaiseAction()));
	};
      });
    
    return windowMenu;
  };
  
};



