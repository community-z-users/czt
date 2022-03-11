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

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.beans.Beans;
import java.beans.ExceptionListener;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.beans.Statement;
import java.beans.XMLDecoder;
import java.beans.beancontext.BeanContextChild;
import java.beans.beancontext.BeanContextProxy;
import java.beans.beancontext.BeanContextServiceProvider;
import java.beans.beancontext.BeanContextServices;
import java.beans.beancontext.BeanContextServicesSupport;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.EventListener;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;
import java.util.prefs.Preferences;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.ActionMap;
import javax.swing.InputMap;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.KeyStroke;
import javax.swing.event.EventListenerList;

import net.sourceforge.czt.animation.gui.design.properties.PropertiesWindow;
import net.sourceforge.czt.animation.gui.persistence.GaffeEncoder;
import net.sourceforge.czt.animation.gui.util.Utils;

import org.apache.bsf.BSFException;
import org.apache.bsf.BSFManager;
import org.apache.bsf.util.IOUtils;

/**
 * The core of the Gaffe interface design program.
 * A GUI interface builder for creating GUI interfaces to the animator.
 */
public class DesignerCore implements BeanContextProxy
{
  private final List<FormDesign> forms;

  private FormDesign currentBeansForm;

  private Object currentBean;

  private final ToolWindow toolWindow;

  private final PropertiesWindow propertiesWindow;

  private final ActionMap actionMap = new ActionMap();

  private final InputMap inputMap = new InputMap();

  private EventListenerList listenerSupport = new EventListenerList();

  private PropertyChangeSupport pcSupport = new PropertyChangeSupport(this);

  private Vector<Class<?>> toolClasses = new Vector<Class<?>>();

  protected int beanHighlightingStatus = BHS_HIGHLIGHT_NO_BEANS;

  protected static final int BHS_HIGHLIGHT_NO_BEANS = 0;

  protected static final int BHS_HIGHLIGHT_COMPONENT_BEANS = 1;

  protected static final int BHS_HIGHLIGHT_NONVISUAL_BEANS = 2;

  protected static final int BHS_HIGHLIGHT_ALL_BEANS = BHS_HIGHLIGHT_COMPONENT_BEANS
      | BHS_HIGHLIGHT_NONVISUAL_BEANS;

  protected int eventLinkHighlightingStatus = ELHS_HIGHLIGHT_ALL_LINKS;

  protected static final int ELHS_HIGHLIGHT_NO_LINKS = 0;

  protected static final int ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS = 1;

  protected static final int ELHS_HIGHLIGHT_CURRENT_OUTGOING_LINKS = 2;

  protected static final int ELHS_HIGHLIGHT_CURRENT_ALL_LINKS = 3;

  protected static final int ELHS_HIGHLIGHT_ALL_LINKS = 4;

  //XXX This is not nice, shouldn't create, then delete the forms.
  public DesignerCore(File f)
  {
    this();
    Vector<FormDesign> formDesigns = readFile(f);
    //Delete the old forms.
    while (!forms.isEmpty())
      removeForm((FormDesign) forms.get(0));
    //Display the new forms.
    for (FormDesign fd : formDesigns) {
      addForm(fd, fd.getForm().getStartsVisible());
    }
  };

  public DesignerCore()
  {
    Beans.setDesignTime(true);
    runConfigScript();
    forms = new Vector<FormDesign>(); //List<FormDesign>
    currentBeansForm = null;
    currentBean = null;

    toolWindow = new ToolWindow((Class[]) toolClasses.toArray(new Class[0]),
        actionMap);

    setupActions();
    propertiesWindow = new PropertiesWindow(actionMap, inputMap);
    bcsSupport = new BeanContextServicesSupport();
    bcsSupport.addService(DesignerCore.class, new BeanContextServiceProvider()
    {
      public Object getService(BeanContextServices bcs, Object requestor,
          @SuppressWarnings("rawtypes") Class serviceClass, Object serviceSelector)
      {
        return DesignerCore.this;
      };

      public void releaseService(BeanContextServices bcs, Object requestor,
          Object service)
      {
      };

      public Iterator<Object> getCurrentServiceSelectors(BeanContextServices bcs,
          @SuppressWarnings("rawtypes") Class serviceClass)
      {
        return null;
      };
    });
    bcsSupport.addService(ToolWindow.class, new BeanContextServiceProvider()
    {
      public Object getService(BeanContextServices bcs, Object requestor,
          @SuppressWarnings("rawtypes") Class serviceClass, Object serviceSelector)
      {
        return getToolWindow();
      };

      public void releaseService(BeanContextServices bcs, Object requestor,
          Object service)
      {
      };

      public Iterator<Object> getCurrentServiceSelectors(BeanContextServices bcs,
    		  @SuppressWarnings("rawtypes") Class serviceClass)
      {
        return null;
      };
    });

    FormDesign firstForm = createNewForm("Main");
    firstForm.getForm().setStartsVisible(true);
    firstForm.setVisible(true);
    propertiesWindow.beanSelected(new BeanSelectedEvent(firstForm, firstForm
        .getForm()));
    beanSelectListener.beanSelected(new BeanSelectedEvent(firstForm, firstForm
        .getForm()));
  };

  public static int run(String[] args)
  {
    if (args.length == 0)
      new DesignerCore();
    else
      new DesignerCore(new File(args[0]));
    return 0;
  };

  private BeanContextServicesSupport bcsSupport;

  public BeanContextChild getBeanContextProxy()
  {
    return bcsSupport;
  };

  private Object getSelectedBean()
  {
    return currentBean;
  };

  public ToolWindow getToolWindow()
  {
    return toolWindow;
  };

  public PropertiesWindow getPropertiesWindow()
  {
    return propertiesWindow;
  };

  public int getBeanHighlightingStatus()
  {
    return beanHighlightingStatus;
  };

  private void setBeanHighlightingStatus(int bhs)
  {
    int oldBhs = beanHighlightingStatus;
    beanHighlightingStatus = bhs;
    pcSupport.firePropertyChange("beanHighlightingStatus", oldBhs, bhs);
  };

  public int getEventLinkHighlightingStatus()
  {
    return eventLinkHighlightingStatus;
  };

  private void setEventLinkHighlightingStatus(int elhs)
  {
    int oldElhs = eventLinkHighlightingStatus;
    eventLinkHighlightingStatus = elhs;
    pcSupport.firePropertyChange("eventLinkHighlightingStatus", oldElhs, elhs);
  };

  public void addFormDesignListener(FormDesignListener l)
  {
    for (FormDesign fd : forms) {
      l.formCreated(new FormDesignEvent(this, fd,
          FormDesignEvent.CREATED));
    }
    listenerSupport.add(FormDesignListener.class, l);
  };

  public void removeFormDesignListener(FormDesignListener l)
  {
    listenerSupport.remove(FormDesignListener.class, l);
  };

  private void fireFormCreated(FormDesign f)
  {
    EventListener[] list = listenerSupport
        .getListeners(FormDesignListener.class);
    FormDesignEvent ev = new FormDesignEvent(this, f, FormDesignEvent.CREATED);
    for (int i = 0; i < list.length; i++)
      ((FormDesignListener) list[i]).formCreated(ev);
  };

  private void fireFormDeleted(FormDesign f)
  {
    EventListener[] list = listenerSupport
        .getListeners(FormDesignListener.class);
    FormDesignEvent ev = new FormDesignEvent(this, f, FormDesignEvent.DELETED);
    for (int i = 0; i < list.length; i++)
      ((FormDesignListener) list[i]).formDeleted(ev);
  };

  public void addPropertyChangeListener(String property,
      PropertyChangeListener listener)
  {
    pcSupport.addPropertyChangeListener(property, listener);
  };

  public void removePropertyChangeListener(String property,
      PropertyChangeListener listener)
  {
    pcSupport.removePropertyChangeListener(property, listener);
  };

  public void addPropertyChangeListener(PropertyChangeListener listener)
  {
    pcSupport.addPropertyChangeListener(listener);
  };

  public void removePropertyChangeListener(PropertyChangeListener listener)
  {
    pcSupport.removePropertyChangeListener(listener);
  };

  private void runConfigScript()
  {
    BSFManager bsfm = new BSFManager();
    try {
      bsfm.declareBean("err", System.err, System.err.getClass());
      bsfm.declareBean("out", System.out, System.out.getClass());
      bsfm.declareBean("DesignerCore", this, DesignerCore.class);
      bsfm.declareBean("ToolClasses", toolClasses, toolClasses.getClass());
    } catch (BSFException ex) {
      throw new Error(
          "Beans couldn't be declared for the configuration script." + ex);
    }

    Preferences userPref = Preferences.userNodeForPackage(DesignerCore.class);
    Preferences systemPref = Preferences
        .systemNodeForPackage(DesignerCore.class);

    boolean fallBackOnSystem = userPref.getBoolean("Use System Preferences",
        true);
    boolean fallBackOnPackage;
    if (fallBackOnSystem) {
      fallBackOnPackage = userPref.getBoolean("Use Package Preferences",
          systemPref.getBoolean("Use Package Preferences", true));
    }
    else {
      fallBackOnPackage = userPref.getBoolean("Use Package Preferences", true);
    }

    Reader in;
    String scriptName;
    if (fallBackOnPackage) {
      scriptName = "net/sourceforge/czt/animation/gui/design/design-config.js";
      InputStream scriptStream = ClassLoader
          .getSystemResourceAsStream(scriptName);
      in = new InputStreamReader(scriptStream);
      try {
        bsfm.exec("javascript", scriptName, 1, 0, IOUtils
            .getStringFromReader(in));
      } catch (IOException ex) {
        throw new Error("Couldn't read the config script from the package.");
      } catch (BSFException ex) {
        System.err.println("Warning: Caught exception caused by the "
            + "distribution config script." + ex);
      }
    }
    if (fallBackOnSystem) {
      scriptName = systemPref.get("Config Script", null);
      if (scriptName != null)
        try {
          bsfm.exec("javascript", scriptName, 0, 0, IOUtils
              .getStringFromReader(new FileReader(scriptName)));
        } catch (FileNotFoundException ex) {
          System.err
              .println("Warning: Could not find the Config Script listed "
                  + "in the System Preferences.");
        } catch (IOException ex) {
          System.err.println("Warning: Could not read from the Config Script "
              + "listed in the System Preferences.");
        } catch (BSFException ex) {
          System.err.println("Warning: Caught exception caused by config "
              + "script listed in the System Preferences." + ex);
        }
    }
    scriptName = userPref.get("Config Script", null);
    if (scriptName != null)
      try {
        bsfm.exec("javascript", scriptName, 0, 0, IOUtils
            .getStringFromReader(new FileReader(scriptName)));
      } catch (FileNotFoundException ex) {
        System.err.println("Warning: Could not find the Config Script listed "
            + "in the User Preferences.");
      } catch (IOException ex) {
        System.err.println("Warning: Could not read from the Config Script "
            + "listed in the User Preferences.");
      } catch (BSFException ex) {
        System.err.println("Warning: Caught exception caused by config script "
            + "listed in the User Preferences." + ex);
      }
  };

  private final BeanSelectedListener beanSelectListener = new BeanSelectedListener()
  {
    public void beanSelected(BeanSelectedEvent ev)
    {
      currentBeansForm = ev.getSelectedBeansForm();
      currentBean = getSelectedBean();
      for (FormDesign fd : forms) {
        if (fd != currentBeansForm)
          fd.unselectBean();
      };
    };
  };

  public FormDesign createNewForm(String name)
  {
    FormDesign form = new FormDesign(name, actionMap, inputMap,
        setupWindowMenu(), this);
    addForm(form);
    return form;
  };

  public void addForm(FormDesign form)
  {
    addForm(form, true);
  };

  public void addForm(FormDesign form, boolean visible)
  {
    forms.add(form);
    //Add to windows menu/other structures
    form.addBeanSelectedListener(beanSelectListener);
    form.addBeanSelectedListener(propertiesWindow);

    //If the last window closes we will want the program to quit.
    form.addWindowListener(new WindowAdapter()
    {
      public void windowClosing(WindowEvent ev)
      {
        Vector<FormDesign> v = getVisibleForms();
        v.remove(ev.getWindow());
        if (v.isEmpty()) {
          actionMap.get("Quit").actionPerformed(
              new ActionEvent(ev, ev.getID(), null, 0));
          //Should not return from the call to actionPerformed.
        }
        else
          ev.getWindow().setVisible(false);
      };
    });

    toolWindow.addToolChangeListener(form);
    form.setSize(300, 300);
    form.setVisible(visible);
    fireFormCreated(form);
  };

  public Vector<FormDesign> getVisibleForms()
  {
    Vector<FormDesign> result = new Vector<FormDesign>(forms);

    for (Iterator<FormDesign> i = result.iterator(); i.hasNext();)
      if (! i.next().isVisible())
        i.remove();
    return result;
  };

  public int getNumberVisibleForms()
  {
    return getVisibleForms().size();
  };

  public boolean isNoVisibleForms()
  {
    return getVisibleForms().isEmpty();
  };

  public void removeForm(FormDesign form)
  {
    form.setVisible(false);
    forms.remove(form);
    toolWindow.removeToolChangeListener(form);
    form.removeBeanSelectedListener(beanSelectListener);
    form.removeBeanSelectedListener(propertiesWindow);
    fireFormDeleted(form);
  };

  private String initScript = "";

  private String initScriptLanguage = "javascript";

  private URL specificationURL = null;

  public void setInitScript(String initScript)
  {
    this.initScript = initScript;
  };

  public void setInitScriptLanguage(String initScriptLanguage)
  {
    this.initScriptLanguage = initScriptLanguage;
  };

  public void setSpecificationURL(URL url)
  {
    this.specificationURL = url;
  };

  public void setSpecificationURL(String url)
  {
    try {
      this.specificationURL = new URL(url);
    } catch (MalformedURLException ex) {
      this.specificationURL = null;
    };
  };

  public String getInitScript()
  {
    return initScript;
  };

  public String getInitScriptLanguage()
  {
    return initScriptLanguage;
  };

  public String getSpecificationURL()
  {
    return specificationURL.toExternalForm();
  };

  /**
   * <code>XMLEncoder</code>/<code>XMLDecoder</code> owner for saving and
   * loading interfaces.
   */
  public final static class EncoderOwner
  {
    private String initScript = "";

    private String initScriptLanguage = "javascript";

    private URL specificationURL = null;

    public EncoderOwner()
    {
    };

    public EncoderOwner(String is, String isl, URL url)
    {
      initScript = is;
      initScriptLanguage = isl;
      specificationURL = url;
    };

    public EncoderOwner(String is, String isl, String url)
    {
      this(is, isl, (URL) null);
      setSpecificationURL(url);
    };

    public void setInitScript(String is)
    {
      initScript = is;
    };

    public void setInitScriptLanguage(String isl)
    {
      initScriptLanguage = isl;
    };

    public void setSpecificationURL(String url)
    {
      try {
        specificationURL = new URL(url);
      } catch (MalformedURLException ex) {
        specificationURL = null;
      };
    };

    public void setSpecificationURL(URL url)
    {
      specificationURL = url;
    };

    public String getInitScript()
    {
      return initScript;
    };

    public String getInitScriptLanguage()
    {
      return initScriptLanguage;
    };

    public String getSpecificationURL()
    {
      return specificationURL.toExternalForm();
    };
  };

  private void registerAction(Action action, String name, String desc,
      KeyStroke key)
  {
    action.putValue(Action.NAME, name);
    action.putValue(Action.SHORT_DESCRIPTION, desc);
    action.putValue(Action.LONG_DESCRIPTION, desc);
    //XXX action.putValue(Action.SMALL_ICON,...);
    //XXX action.putValue(Action.ACTION_COMMAND_KEY,...);
    action.putValue(Action.ACCELERATOR_KEY, key);
    //XXX action.putValue(Action.MNEMONIC_KEY,...);
    actionMap.put(name, action);
    inputMap.put(key, name);
  };

  private void registerAction(Action action, String name, KeyStroke key)
  {
    registerAction(action, name, name, key);
  };

  private void setupActions()
  {
    Action action_new_form;
    action_new_form = new AbstractAction("New Form")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -8754034273204539204L;
	private int i = 1;

      public void actionPerformed(ActionEvent e)
      {
        createNewForm("Form" + i).setVisible(true);
        i++;
      };
    };
    registerAction(action_new_form, "New Form", KeyStroke
        .getKeyStroke("control N"));

    Action action_quit;
    action_quit = new AbstractAction("Quit")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 5889514569705569123L;

	public void actionPerformed(ActionEvent e)
      {
        String confirmText = "This action will exit the program.\n"
            + "Are you sure you want to do this?\n";
        int result = JOptionPane.showConfirmDialog(null, confirmText,
            "Confirm exit", JOptionPane.YES_NO_OPTION);
        if (result == JOptionPane.NO_OPTION)
          return;
        for (FormDesign f : forms) {
          f.dispose();
        }
        propertiesWindow.dispose();
        toolWindow.dispose();
        //XXX properly close all windows
        System.exit(0);
      };
    };
    registerAction(action_quit, "Quit", KeyStroke.getKeyStroke("control Q"));

    Action action_show_properties_window;
    action_show_properties_window = new AbstractAction("Show Properties Window")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -6433723370617787699L;

	public void actionPerformed(ActionEvent e)
      {
        propertiesWindow.setVisible(true);
        propertiesWindow.toFront();
      };
    };
    registerAction(action_show_properties_window, "Show Properties Window",
        KeyStroke.getKeyStroke("control P"));

    Action action_show_toolbox_window;
    action_show_toolbox_window = new AbstractAction("Show Toolbox Window")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 1117360825409225961L;

	public void actionPerformed(ActionEvent e)
      {
        toolWindow.setVisible(true);
        toolWindow.toFront();
      };
    };
    registerAction(action_show_toolbox_window, "Show Toolbox Window", KeyStroke
        .getKeyStroke("control T"));

    Action action_show_about_dialog;
    action_show_about_dialog = new AbstractAction("About...")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -5920403473085689067L;

	public void actionPerformed(ActionEvent e)
      {
        String message = "GAfFE Copyright 2003 Nicholas Daley\n"
            + "GAfFE comes under the GPL (See Help->License).";
        JOptionPane.showMessageDialog(null, message, "About GAfFE",
            JOptionPane.INFORMATION_MESSAGE);
      };
    };
    registerAction(action_show_about_dialog, "About...", "Show About Dialog",
        KeyStroke.getKeyStroke("control H"));

    Action action_show_license_dialog;
    action_show_license_dialog = new AbstractAction("License...")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 2649118383604557339L;

	public void actionPerformed(ActionEvent e)
      {
        licenseDialog.setVisible(true);
        licenseDialog.toFront();
      };
    };
    registerAction(action_show_license_dialog, "License...",
        "Show License Dialog", KeyStroke.getKeyStroke("control L"));

    Action action_show_initscript_dialog;
    action_show_initscript_dialog = new AbstractAction("Init Script...")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 4162570919300637810L;

	public void actionPerformed(ActionEvent e)
      {
        initScriptDialog.setVisible(true);
        initScriptDialog.toFront();
      };
    };
    registerAction(action_show_initscript_dialog, "Init Script...",
        "Show Init Script Dialog", KeyStroke.getKeyStroke("control #"));

    Action action_save_forms;
    action_save_forms = new AbstractAction("Save...")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 2891580714664635416L;

	public void actionPerformed(ActionEvent e)
      {
        boolean allNonVisible = true;
        for (Iterator<FormDesign> it = forms.iterator(); it.hasNext();)
          if (( it.next()).getForm().getStartsVisible()) {
            allNonVisible = false;
            break;
          }
        if (allNonVisible) {
          String message = "At least one form must have its 'startsVisible' "
              + "property set to true.  Otherwise the animator will not know "
              + "which forms to to display when it starts.";
          JOptionPane.showMessageDialog(null, message, "No visible forms",
              JOptionPane.ERROR_MESSAGE);
          return;
        }

        JFileChooser fc = new JFileChooser();
        fc.addChoosableFileFilter(Utils.gaffeFileFilter);
        if (fc.showSaveDialog(null) != JFileChooser.APPROVE_OPTION)
          return;
        File file = fc.getSelectedFile();
        GaffeEncoder encoder;
        try {
          encoder = new GaffeEncoder(new FileOutputStream(file));
        } catch (FileNotFoundException ex) {
          JOptionPane.showMessageDialog(null, "File not found:" + ex,
              "File not found", JOptionPane.ERROR_MESSAGE);
          return;
        }
        encoder.setOwner(new EncoderOwner(initScript, initScriptLanguage,
            specificationURL));
        encoder.writeStatement(new Statement(encoder.getOwner(),
            "setInitScript", new Object[]{initScript}));
        encoder.writeStatement(new Statement(encoder.getOwner(),
            "setInitScriptLanguage", new Object[]{initScriptLanguage}));
        encoder.writeStatement(new Statement(encoder.getOwner(),
            "setSpecificationURL", new Object[]{getSpecificationURL()}));

        encoder.setExceptionListener(new ExceptionListener()
        {
          public void exceptionThrown(Exception ex)
          {
            System.err.println("### Exception ###");
            ex.printStackTrace();
          };
        });

        for (FormDesign fd : forms) {
          fd.saveDesign(encoder);
        }
        encoder.close();
      };
    };
    registerAction(action_save_forms, "Save...", "Save all forms", KeyStroke
        .getKeyStroke("control S"));

    Action action_open_forms;
    action_open_forms = new AbstractAction("Open...")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 4368271836388602569L;

	public void actionPerformed(ActionEvent e)
      {
        //XXX Change to delegate to a delete all forms action?
        String message = "Opening an interface design will clear all other designs.\n"
            + "Are you sure you want to do this?\n";
        int result = JOptionPane.showConfirmDialog(null, message,
            "Confirm delete all current forms", JOptionPane.YES_NO_OPTION);
        if (result == JOptionPane.NO_OPTION)
          return;

        JFileChooser fc = new JFileChooser();
        fc.addChoosableFileFilter(Utils.gaffeFileFilter);
        if (fc.showOpenDialog(null) != JFileChooser.APPROVE_OPTION)
          return;
        Vector<FormDesign> formDesigns = readFile(fc.getSelectedFile());

        //We got nothing from the file, so we'll leave the current designs.
        if (formDesigns.isEmpty())
          return;

        //Delete the old forms.
        while (!forms.isEmpty())
          removeForm((FormDesign) forms.get(0));
        //Display the new forms.
        for (FormDesign fd : formDesigns) {
          addForm(fd, fd.getForm().getStartsVisible());
        }
      };
    };
    registerAction(action_open_forms, "Open...",
        "Open an interface design, deleting the current design.", KeyStroke
            .getKeyStroke("control O"));

    Action action_import_forms;
    action_import_forms = new AbstractAction("Import...")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 4270381310872830577L;

	public void actionPerformed(ActionEvent e)
      {
        JFileChooser fc = new JFileChooser();
        fc.addChoosableFileFilter(Utils.gaffeFileFilter);
        if (fc.showOpenDialog(null) != JFileChooser.APPROVE_OPTION)
          return;
        Vector<FormDesign> formDesigns = readFile(fc.getSelectedFile());
        for (Iterator<FormDesign> it = formDesigns.iterator(); it.hasNext();) {
          FormDesign fd =  it.next();
          addForm(fd, fd.getForm().getStartsVisible());
        }
      };
    };
    registerAction(action_import_forms, "Import...",
        "Import an interface, adding to the current interface.", KeyStroke
            .getKeyStroke("control I"));

    Action action_view_highlight_all_beans;
    action_view_highlight_all_beans = new AbstractAction("Highlight All Beans")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 1794596959224711436L;

	public void actionPerformed(ActionEvent e)
      {
        setBeanHighlightingStatus(BHS_HIGHLIGHT_ALL_BEANS);
        System.err.println("All beans highlighting");
      };
    };
    registerAction(action_view_highlight_all_beans, "Highlight All Beans",
        KeyStroke.getKeyStroke("control A"));

    Action action_view_highlight_component_beans;
    action_view_highlight_component_beans = new AbstractAction(
        "Highlight Components")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 1016527654336416206L;

	public void actionPerformed(ActionEvent e)
      {
        setBeanHighlightingStatus(BHS_HIGHLIGHT_COMPONENT_BEANS);
      };
    };
    registerAction(action_view_highlight_component_beans,
        "Highlight Components", KeyStroke.getKeyStroke("control C"));

    Action action_view_highlight_nonvisual_beans;
    action_view_highlight_nonvisual_beans = new AbstractAction(
        "Highlight Non-visual Beans")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -141699344771600075L;

	public void actionPerformed(ActionEvent e)
      {
        setBeanHighlightingStatus(BHS_HIGHLIGHT_NONVISUAL_BEANS);
      };
    };
    registerAction(action_view_highlight_nonvisual_beans,
        "Highlight Non-visual Beans", KeyStroke.getKeyStroke("control B"));

    Action action_view_highlight_no_beans;
    action_view_highlight_no_beans = new AbstractAction(
        "Highlight Non-visual Beans")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -372356445740038987L;

	public void actionPerformed(ActionEvent e)
      {
        setBeanHighlightingStatus(BHS_HIGHLIGHT_NO_BEANS);
      };
    };
    registerAction(action_view_highlight_no_beans, "Don't Highlight Beans",
        KeyStroke.getKeyStroke("control D"));

    Action action_view_highlight_all_event_links;
    action_view_highlight_all_event_links = new AbstractAction(
        "Highlight All Event Links")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -5827750931707437569L;

	public void actionPerformed(ActionEvent e)
      {
        setEventLinkHighlightingStatus(ELHS_HIGHLIGHT_ALL_LINKS);
        System.err.println("All EventLinks Highlighting");
      };
    };
    registerAction(action_view_highlight_all_event_links,
        "Highlight All Event Links", KeyStroke.getKeyStroke("control #")); //XXX

    Action action_view_highlight_current_all_event_links;
    action_view_highlight_current_all_event_links = new AbstractAction(
        "Highlight Current Bean's Event Links")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 2268484360334780763L;

	public void actionPerformed(ActionEvent e)
      {
        setEventLinkHighlightingStatus(ELHS_HIGHLIGHT_CURRENT_ALL_LINKS);
      };
    };
    registerAction(action_view_highlight_current_all_event_links,
        "Highlight Current Bean's Event Links", KeyStroke
            .getKeyStroke("control #")); //XXX

    Action action_view_highlight_current_incoming_event_links;
    action_view_highlight_current_incoming_event_links = new AbstractAction(
        "Highlight Current Bean's Incoming Event Links")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = 4406143568907736216L;

	public void actionPerformed(ActionEvent e)
      {
        setEventLinkHighlightingStatus(ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS);
      };
    };
    registerAction(action_view_highlight_current_incoming_event_links,
        "Highlight Current Bean's Incoming Event Links", KeyStroke
            .getKeyStroke("control #")); //XXX

    Action action_view_highlight_current_outgoing_event_links;
    action_view_highlight_current_outgoing_event_links = new AbstractAction(
        "Highlight Current Bean's Outgoing Event Links")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -1250883901048228774L;

	public void actionPerformed(ActionEvent e)
      {
        setEventLinkHighlightingStatus(ELHS_HIGHLIGHT_CURRENT_OUTGOING_LINKS);
      };
    };
    registerAction(action_view_highlight_current_outgoing_event_links,
        "Highlight Current Bean's Outgoing Event Links", KeyStroke
            .getKeyStroke("control #")); //XXX

    Action action_view_highlight_no_event_links;
    action_view_highlight_no_event_links = new AbstractAction(
        "Don't Highlight Event Links")
    {
      /**
		 * 
		 */
		private static final long serialVersionUID = -5630078707206228803L;

	public void actionPerformed(ActionEvent e)
      {
        setEventLinkHighlightingStatus(ELHS_HIGHLIGHT_CURRENT_INCOMING_LINKS);
      };
    };
    registerAction(action_view_highlight_no_event_links,
        "Don't Highlight Event Links", KeyStroke.getKeyStroke("control #")); //XXX

  };

  private Vector<FormDesign> readFile(File file)
  {
    XMLDecoder decoder;
    try {
      decoder = new XMLDecoder(new FileInputStream(file), this);
    } catch (FileNotFoundException ex) {
      JOptionPane.showMessageDialog(null, "File not found:" + ex,
          "File not found", JOptionPane.ERROR_MESSAGE);
      return new Vector<FormDesign>();
    }
    Vector<FormDesign> formDesigns = new Vector<FormDesign>();
    try {
      while (true) {
        formDesigns.add(FormDesign.loadDesign(decoder, actionMap, inputMap,
            setupWindowMenu(), DesignerCore.this));
      }
    } catch (ArrayIndexOutOfBoundsException ex) {
    } finally {
      decoder.close();
    }
    if (formDesigns.isEmpty())
      JOptionPane.showMessageDialog(null, "File contains no form designs",
          "Bad or empty file", JOptionPane.ERROR_MESSAGE);
    return formDesigns;
  };

  private JMenu setupWindowMenu()
  {
    final JMenu windowMenu = new JMenu("Window");
    windowMenu.add(new JMenuItem(actionMap.get("Show Properties Window")));
    windowMenu.add(new JMenuItem(actionMap.get("Show Toolbox Window")));
    windowMenu.add(new JMenuItem(actionMap.get("Init Script...")));
    windowMenu.setMnemonic(KeyEvent.VK_W);
    windowMenu.addSeparator();
    addFormDesignListener(new FormDesignListener()
    {
      private HashMap<Action, JMenuItem> map = new HashMap<Action, JMenuItem>();

      public void formCreated(FormDesignEvent e)
      {
        JMenuItem mi = new JMenuItem(e.getFormDesign().getRaiseAction());
        windowMenu.add(mi);
        map.put(e.getFormDesign().getRaiseAction(), mi);
      };

      public void formDeleted(FormDesignEvent e)
      {
        JMenuItem formMenuItem = (JMenuItem) map.get(e.getFormDesign()
            .getRaiseAction());
        windowMenu.remove(formMenuItem);
      };
    });
    return windowMenu;
  };

  /**
   * Dialog box for displaying the GPL.
   */
  private final static class LicenseDialog extends JDialog
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 8063718535766310934L;

	public LicenseDialog()
    {
      super();
      BufferedReader input;
      try {
        String licensePath = "net/sourceforge/czt/animation/gui/GPL.txt";
        URL licenseURL = ClassLoader.getSystemResource(licensePath);
        input = new BufferedReader(new InputStreamReader(licenseURL
            .openStream()));
      } catch (IOException ex) {
        throw new Error("Couldn't find the GPL License text.");
      };
      String license = "";
      try {
        try {
          String s = input.readLine();
          do {
            license += s + "\n";
            s = input.readLine();
          } while (s != null);
        } finally {
          input.close();
        }
      } catch (IOException ex) {
        throw new Error("Couldn't read the GPL License text.");
      }
      JTextArea ta = new JTextArea(license);
      ta.setEditable(false);

      getRootPane().setLayout(new BorderLayout());
      getRootPane().add(new JScrollPane(ta), BorderLayout.CENTER);
      setSize(getPreferredSize().width, Math
          .min(getPreferredSize().height, 600));
    };
  };

  private final JDialog licenseDialog = new LicenseDialog();

  /**
   * Dialog box for setting the initialisation script for the interface.
   */
  private final class InitScriptDialog extends JDialog
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 8451737641558063375L;

	public JComboBox<String> scriptLibraryCB;

    public JButton scriptLibraryPaste;

    @SuppressWarnings("serial")
	public InitScriptDialog()
    {
      super((JFrame) null, "Edit Init Script");
      final JTextField languageField = new JTextField();
      final JTextArea scriptField = new JTextArea();

      final JPanel northPane = new JPanel();
      GridBagLayout layout = new GridBagLayout();
      northPane.setLayout(layout);

      GridBagConstraints constraints = new GridBagConstraints();
      constraints.fill = GridBagConstraints.BOTH;
      JLabel label = new JLabel("Language:", JLabel.RIGHT);
      layout.setConstraints(label, constraints);
      northPane.add(label);
      constraints.weightx = 1;
      constraints.gridwidth = GridBagConstraints.REMAINDER;
      layout.setConstraints(languageField, constraints);
      northPane.add(languageField);

      constraints = new GridBagConstraints();
      constraints.fill = GridBagConstraints.BOTH;
      scriptLibraryPaste = new JButton(new AbstractAction("Paste from Library")
      {
        /**
		 * 
		 */
		private static final long serialVersionUID = 9103894973359695758L;

		public void actionPerformed(ActionEvent ev)
        {
          try {
            URL scriptURL = (URL) scriptLibrary.get(scriptLibraryCB
                .getSelectedItem());
            InputStreamReader scriptReader = new InputStreamReader(scriptURL
                .openStream());
            try {
              String script = IOUtils.getStringFromReader(scriptReader);
              scriptField.replaceSelection(script);
            } finally {
              scriptReader.close();
            }
          } catch (FileNotFoundException ex) {
            JOptionPane.showMessageDialog(InitScriptDialog.this,
                "File not found:" + ex, "File not found",
                JOptionPane.ERROR_MESSAGE);
          } catch (IOException ex) {
            JOptionPane.showMessageDialog(InitScriptDialog.this,
                "Error reading file:" + ex, "Error reading file",
                JOptionPane.ERROR_MESSAGE);
          };
        };
      });
      constraints.weightx = 0;
      scriptLibraryPaste.setEnabled(false);
      layout.setConstraints(scriptLibraryPaste, constraints);
      northPane.add(scriptLibraryPaste);

      scriptLibraryCB = new JComboBox<>();
      constraints.weightx = 1;
      constraints.gridwidth = GridBagConstraints.REMAINDER;
      layout.setConstraints(scriptLibraryCB, constraints);
      northPane.add(scriptLibraryCB);

      final JPanel southPane = new JPanel();
      southPane.setLayout(new FlowLayout(FlowLayout.CENTER));
      southPane.add(new JButton(new AbstractAction("OK")
      {
    	  
        /**
		 * 
		 */
		private static final long serialVersionUID = 7033479319892300411L;

		public void actionPerformed(ActionEvent e)
        {
          setInitScript(scriptField.getText());
          setInitScriptLanguage(languageField.getText());
          setVisible(false);
        };
      }));
      southPane.add(new JButton(new AbstractAction("Cancel")
      {
        
		public void actionPerformed(ActionEvent e)
        {
          setVisible(false);
        };
      }));

      getContentPane().setLayout(new BorderLayout());
      getContentPane().add(northPane, BorderLayout.NORTH);
      getContentPane().add(new JScrollPane(scriptField), BorderLayout.CENTER);
      getContentPane().add(southPane, BorderLayout.SOUTH);

      addComponentListener(new ComponentAdapter()
      {
        public void componentShown(ComponentEvent e)
        {
          scriptField.setText(getInitScript());
          languageField.setText(getInitScriptLanguage());
        };
      });
      setSize(300, 200);
    };
  };

  private final InitScriptDialog initScriptDialog = new InitScriptDialog();

  private final HashMap<String, URL> scriptLibrary = new HashMap<String, URL>();

  public final void registerScriptLibrary(String scriptName, URL scriptURL)
  {
    scriptLibrary.put(scriptName, scriptURL);
    initScriptDialog.scriptLibraryCB.addItem(scriptName);
    initScriptDialog.scriptLibraryPaste.setEnabled(true);
  };

  public final void registerScriptLibrary(String scriptName, String scriptFile)
  {
    registerScriptLibrary(scriptName, ClassLoader.getSystemResource(scriptFile));
  };
};
