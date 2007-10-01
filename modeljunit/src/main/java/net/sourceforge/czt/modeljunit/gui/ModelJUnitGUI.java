
package net.sourceforge.czt.modeljunit.gui;

// For GUIs
import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.KeyEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

// For compiler
import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

/**
 * ModelJUnitGUI.java
 *
 * @author rong
 * ID : 1005450
 * 26th Jul 2007
 * */
public class ModelJUnitGUI implements ActionListener,ComponentListener
{
  private JFrame m_frame;

  private ImageIcon[] m_iconTag;

  private JTabbedPane m_tabbedPane = new JTabbedPane();

  private PanelTestDesign m_panelTD;

  private PanelCodeViewer m_panelCV;

  private PanelResultViewer m_panelRV;

  private PanelExecuteActions m_panelEA;
  
  // The panel with run button
  private JPanel m_panelOption = new JPanel();

  private JButton m_butRun = new JButton("Run test");

  // Menu items
  private JMenuBar m_menuBar;

  private JMenuItem m_miFile;

  private JMenuItem m_miExit;

  private JRadioButtonMenuItem m_miOpenModel;

  private JRadioButtonMenuItem m_miOpenModelDefault;

  private JMenuItem m_miAbout;

  public void createAndShowGUI()
  {
    // Load setting file
    Parameter.readSettingFile();
    // Initialize GUI
    m_butRun.addActionListener(this);
    m_frame = new JFrame("ModelJUnit GUI");
    m_frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    m_frame.addComponentListener(this);

    try {
      // UIManager.setLookAndFeel("com.sun.java.swing.plaf.motif.MotifLookAndFeel");
      // UIManager.setLookAndFeel("com.sun.java.swing.plaf.windows.WindowsLookAndFeel") ;
      UIManager.setLookAndFeel("javax.swing.plaf.metal.MetalLookAndFeel");
      // UIManager.setLookAndFeel("com.sun.java.swing.plaf.motif.MotifLookAndFeel");

      }
      catch (Exception e) {
      System.out.println ("Couldn't load Motif look and feel " + e);
      }

    // Initialize TestDesign panel
    m_panelTD = PanelTestDesign.createTestDesignPanel();
    // If user opens java file button text will be set to compile
    // else if user opens class file, button test becomes run test
    m_panelTD.setModelRelatedButton(m_butRun);
    // Initialize CodeViewer panel
    m_panelCV = PanelCodeViewer.createCodeViewer();
    // Initialize ResuleViewer panel
    m_panelRV = PanelResultViewer.createResultViewer();
    // Initialize ExecuteAction panel
    m_panelEA = PanelExecuteActions.createExecuteActionsPanel();
    Thread initializeImage = new Thread()
    {
      public void run()
      {
        try {

          /*m_iconTag = new ImageIcon[3];
          m_iconTag[0] = new ImageIcon(getClass().getResource("icon.gif"));
          m_iconTag[1] = new ImageIcon(getClass().getResource("icon.gif"));
          m_iconTag[2] = new ImageIcon(getClass().getResource("icon.gif"));*/


          // Setup the tab
          m_tabbedPane.addTab("Test Design", m_panelTD);
          m_tabbedPane.addTab("Code viewer", m_panelCV);
          m_tabbedPane.addTab("Result viewer", m_panelRV);
          m_tabbedPane.addTab("Action Execution", m_panelEA);
          m_tabbedPane.addChangeListener(new TabChangeListener());
          m_panelOption
              .setLayout(new BoxLayout(m_panelOption, BoxLayout.Y_AXIS));
          m_panelOption.add(Box.createHorizontalStrut(16));
          m_panelOption.add(m_butRun);
          m_panelOption.add(Box.createHorizontalGlue());
          m_frame.setLayout(new BorderLayout());
          m_frame.getContentPane().add(m_tabbedPane, BorderLayout.CENTER);
          m_frame.getContentPane().add(m_panelOption, BorderLayout.SOUTH);
          m_frame.pack();
          m_frame.setVisible(true);
        }
        catch (Exception exp) {
          exp.printStackTrace();
        }
      }
    };
    initializeImage.start();

    /*
     * JMenu file = new JMenu("Look & Feel", true);
ButtonGroup buttonGroup = new ButtonGroup();
final UIManager.LookAndFeelInfo[] info = UIManager.getInstalledLookAndFeels();
for (int i = 0; i < info.length; i++) {
JRadioButtonMenuItem item = new
JRadioButtonMenuItem(info[i].getName(), i == 0);
final String className = info[i].getClassName();
item.addActionListener(new ActionListener() {
public void actionPerformed(ActionEvent ae) {
try { UIManager.setLookAndFeel(className); }
catch (Exception e) { System.out.println(e); }
SwingUtilities.updateComponentTreeUI(ToUChyFeely.this); }
});
buttonGroup.add(item);
file.add(item);
}
mb.add(file);
setJMenuBar(mb);

     * */
    // Menu and menu items
    m_menuBar = new JMenuBar();
    // File meun
    JMenu fMenu = new JMenu("File");
    fMenu.setMnemonic('f');

    m_miFile = new JMenuItem("Export java file");
    m_miFile.setMnemonic(KeyEvent.VK_E);
    m_miFile.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_E,
        ActionEvent.ALT_MASK));
    m_miFile.addActionListener(this);
    fMenu.add(m_miFile);
    fMenu.addSeparator();
    // Exit application
    m_miExit = new JMenuItem("Exit");
    m_miExit.setMnemonic(KeyEvent.VK_F4);
    m_miExit.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F4,
        ActionEvent.ALT_MASK));
    m_miExit.addActionListener(this);
    fMenu.add(m_miExit);
    m_menuBar.add(fMenu);
    // Setting menu
    ButtonGroup group = new ButtonGroup();
    JMenu sMenu = new JMenu("Settings");
    sMenu.setMnemonic('s');
    m_miOpenModel = new JRadioButtonMenuItem(
        "use last time directory to open model");
    m_miOpenModel.setMnemonic(KeyEvent.VK_L);
    m_miOpenModel.addActionListener(this);
    m_miOpenModel.setSelected(true);
    group.add(m_miOpenModel);
    sMenu.add(m_miOpenModel);

    m_miOpenModelDefault = new JRadioButtonMenuItem("Use default directory");
    m_miOpenModelDefault.setMnemonic(KeyEvent.VK_L);
    m_miOpenModelDefault.addActionListener(this);
    group.add(m_miOpenModelDefault);
    sMenu.add(m_miOpenModelDefault);
    m_menuBar.add(sMenu);
    // About menu
    JMenu aMenu = new JMenu("About");
    aMenu.setMnemonic('a');
    m_miAbout = new JMenuItem("Version");
    aMenu.add(m_miAbout);
    m_menuBar.add(aMenu);
    m_frame.setJMenuBar(m_menuBar);
  }

  // TEMP directory: System.getProperty("java.io.tmpdir")
  // LIB PATH directory:  System.getProperty("java.library.path")
  // CLASSPATH directory: System.getProperty("java.class.path")
  // SYSTEM DIR: System.getProperty("user.home")
  public void actionPerformed(ActionEvent e)
  {
    //-------------- Menu radio buttons ------------------
    if (e.getSource() == m_miOpenModel) {
      Parameter.setFileChooserOpenMode(0);
    }
    if (e.getSource() == m_miOpenModelDefault) {
      Parameter.setFileChooserOpenMode(1);
    }
    //-------------- Run button event handler -------------
    if (e.getSource() == m_butRun) {
      // No model imported
      if(!Parameter.isTestRunnable(false))
      {
        ErrorMessage
            .DisplayErrorMessage("NO TEST MODEL HAS BEEN SELECTED",
                "Please select Test Model \nfrom Test Design tab\nbefore code generating!");
        return;
      }
      // No algorithm selected
      if (m_panelTD.getCurrentAlgorithm() < 1) {
        ErrorMessage
            .DisplayErrorMessage("NO TEST ALGORITHM HAS BEEN SELECTED",
                "Please select algorithm \nfrom Test Design tab\nbefore generate code!");
        return;
      }
      // Clear the information in Result viewer text area
      m_panelRV.resetRunTimeInformation();

      String sourceFile = Parameter.getModelLocation();
      String name[] = sourceFile.split("\\.");

      if (name.length == 2 && name[1].equalsIgnoreCase("class"))
        runClass();
      // Compile file
      else {
        System.out.println("File from: " + sourceFile);
        // Clear the result table
        m_panelRV.getTableModel().clearData();
        // Java compiler
        /**
         * http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6477844
         * Following statement will produce a null reference without exception
         * it happens when I use only the JRE as Standard VM in Eclipse.
         * Please the JDK as Standard VM. It will work then.
         * Window->Preferences->Installed JREs->
         * Add C:\Program Files/Java/jdk1.6.0_02
         */
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        StandardJavaFileManager fileManager = compiler.getStandardFileManager(
            null, null, null);
        DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<JavaFileObject>();

        Iterable<? extends JavaFileObject> compilationUnits = fileManager
            .getJavaFileObjects(sourceFile);
        JavaCompiler.CompilationTask task = compiler.getTask(null, fileManager,
            diagnostics, null, null, compilationUnits);
        task.call();
        // Check the compile result
        boolean bHasProblem = false;
        for (Diagnostic d : diagnostics.getDiagnostics()) {
          // String type, String class name, String desc,String location, String path
          ResultDetails details = new ResultDetails(d.getKind().name(), d
              .getClass().toString(), d.getMessage(null), "Line: "
              + Long.toString(d.getLineNumber()) + ", Column: "
              + Long.toString(d.getColumnNumber()), d.getSource().toString());
          m_panelRV.getTableModel().addData(details);
          bHasProblem = true;
        }
        // If there is no problem display successful compile message
        if (!bHasProblem) {
          ResultDetails details = new ResultDetails("Successfully compiled ",
              diagnostics.getDiagnostics().getClass().toString(), "", "",
              sourceFile);
          m_panelRV.getTableModel().addData(details);
        }
        try {
          fileManager.close();
        }
        catch (IOException exp) {
          exp.printStackTrace();
        }
      }
    }
    // ------------- Export java file --------------
    if (e.getSource() == m_miFile) 
    {
      String code = m_panelTD.generateCode();
      if (code.length() > 0) 
      {
        String extension = "java";
        FileChooserFilter javaFileFilter = new FileChooserFilter(extension,
            "Java Files");
        JFileChooser chooser = new JFileChooser();
        chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
        chooser.setDialogTitle("Save test file");
        if (Parameter.getFileChooserOpenMode() == 0)
          chooser.setCurrentDirectory(new File(Parameter
              .getModelChooserDirectory()));
        else
          chooser.setCurrentDirectory(new File(Parameter.DEFAULT_DIRECTORY));
        chooser.addChoosableFileFilter(javaFileFilter);
        int option = chooser.showDialog(m_frame, "Export");

        if (option == JFileChooser.APPROVE_OPTION) {
          File f = chooser.getSelectedFile();
          // Set file chooser directory
          Parameter.setModelChooserDirectory(f.getParent());
          // Check the suffix ensure it be .java
          String name[] = f.getName().split("\\.");
          if (name.length != 2) {
            System.out.println(name[0] + ", " + f.getPath());
            File nf = new File(f.getParent(), name[0] + ".java");
            try {
              nf.createNewFile();
            }
            catch (IOException e1) {
              e1.printStackTrace();
              ErrorMessage.DisplayErrorMessage("Cannot create file",
                  "Try select other java file.");
            }
            f.delete();
            f = nf;
          }
          // Write the java file
          try {
            BufferedWriter writer = new BufferedWriter(new FileWriter(f));
            writer.write(code);
            writer.close();
          }
          catch (IOException e1) {
            e1.printStackTrace();
          }
        }
      }
    }
    // ----------------- Exit application ---------------------
    if (e.getSource() == m_miExit)
    {
      Parameter.wirteSettingFile();
      System.exit(0);
    }
  }


  private class FileChooserFilter extends javax.swing.filechooser.FileFilter
  {
    private String m_description = null;

    private String m_extension = null;

    public FileChooserFilter(String extension, String description)
    {
      m_description = description;
      m_extension = "." + extension.toLowerCase();
    }

    @Override
    public boolean accept(File f)
    {
      if (f == null)
        return false;
      if (f.isDirectory())
        return true;
      if (f.getName().toLowerCase().endsWith(m_extension))
        return true;
      return false;
    }

    @Override
    public String getDescription()
    {
      return m_description;
    }
  }

  private void updateGeneratedCode()
  {
    String code = m_panelTD.generateCode();
    m_panelCV.updateCode(code);
    m_panelEA.setGeneratedCode(code);
  }

  private void runClass()
  {
    m_panelRV.updateRunTimeInformation(TestExeModel.runTestAuto());
  }

  class TabChangeListener implements ChangeListener
  {
    public void stateChanged(ChangeEvent e)
    {
      
      JTabbedPane sourcePane = (JTabbedPane)e.getSource();
      
      int idx = sourcePane.getSelectedIndex();
      
      // If user loaded a new model initialize it.
      if(m_panelTD.isNewModelLoaded())
      {
        m_panelTD.initializeTester();
        // if user already selected an algorithm,
        // reset new model before do any action.
        if(Parameter.getAlgorithmName()!= null &&
            !Parameter.getAlgorithmName().equals(Parameter.ALGORITHM_NAME[0]))
          m_panelEA.doResetAction();
        // Clean the action history
        m_panelEA.resetActionHistoryList();
        // Fill actions in action list
        m_panelEA.reloadActionModel();
      }
      // Regenerate code
      if(!Parameter.isTestRunnable(false))
        return;
      updateGeneratedCode();
      // If user click the ExecuteAction pane
      if(3 == idx)
      {
        m_panelEA.resetSubComponents();
        m_panelEA.autoModelInitialization();
      }
    }
  }

  public void componentHidden(ComponentEvent e)
  {
    // TODO Auto-generated method stub

  }

  public void componentMoved(ComponentEvent e)
  {
    m_panelRV.resizeScrollPanes(m_frame.getContentPane().getSize());
  }

  public void componentResized(ComponentEvent e)
  {
    m_panelRV.resizeScrollPanes(m_frame.getContentPane().getSize());
  }

  public void componentShown(ComponentEvent e)
  {
    // TODO Auto-generated method stub
  }
}
