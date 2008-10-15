
package net.sourceforge.czt.modeljunit.gui;

// For GUIs
import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.JTabbedPane;
import javax.swing.KeyStroke;
import javax.swing.UIManager;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.modeljunit.gui.visualisaton.PanelJUNGVisualisation;

/*
 * ModelJUnitGUI.java
 * @author rong ID : 1005450 26th Jul 2007
 */
public class ModelJUnitGUI implements ActionListener
{
  private JFrame m_frame;

  private ImageIcon[] m_iconTag;

  private JTabbedPane m_tabbedPane = new JTabbedPane();

  private PanelTestDesign m_panelTD;

  private PanelCodeViewer m_panelCV;

  private PanelResultViewer m_panelRV;

  private PanelExecuteActions m_panelEA;

  private PanelCoverage m_panelC;

  private PanelJUNGVisualisation m_panelGV;

  // The panel with run button
  private JPanel m_panelOption = new JPanel();

  private JButton m_butRun = new JButton("Generate tests");

  // Menu items
  private JMenuBar m_menuBar;

  private JMenuItem m_miFile;

  private JMenuItem m_miExit;

  private JRadioButtonMenuItem m_miOpenModel;

  private JRadioButtonMenuItem m_miOpenModelDefault;

  private JMenuItem m_miAbout;

  private JMenuItem m_miCoverageColor;

  private int m_nCurrentPanelIndex;

  public void createAndShowGUI()
  {
    // Initialize GUI
    m_butRun.addActionListener(this);
    m_frame = new JFrame("ModelJUnit GUI");
    m_frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

    try {
      // TODO: would be nice to make this user-settable.
      //UIManager.setLookAndFeel("com.sun.java.swing.plaf.motif.MotifLookAndFeel");
      //UIManager.setLookAndFeel("com.sun.java.swing.plaf.windows.WindowsLookAndFeel") ;
      UIManager.setLookAndFeel("javax.swing.plaf.metal.MetalLookAndFeel");
      //UIManager.setLookAndFeel("com.sun.java.swing.plaf.gtk.GTKLookAndFeel");
    }
    catch (Exception e) {
      System.out.println("Couldn't load Motif look and feel " + e);
    }

    // Initialize TestDesign panel
    m_panelTD = PanelTestDesign.getTestDesignPanelInstance(this);
    // Initialize CodeViewer panel
    m_panelCV = PanelCodeViewer.getCodeViewerInstance();
    // Initialize ResuleViewer panel
    m_panelRV = PanelResultViewer.getResultViewerInstance();
    // Initialize ExecuteAction panel
    m_panelEA = PanelExecuteActions.getPanelExecuteActionsInstance();
    // If user opens java file button text will be set to compile
    // else if user opens class file, button test becomes run test
    m_panelTD.setModelRelatedButton(m_butRun);
    // Initialize coverage view panel
    m_panelC = PanelCoverage.getInstance();
    //Get the JUNG visualisation panel
    m_panelGV = PanelJUNGVisualisation.getGraphVisualisationInstance();

    Thread initializeImage = new Thread()
    {
      public void run()
      {
        try {

          m_iconTag = new ImageIcon[6];
          String strIconPath = System.getProperty("user.dir") + File.separator
              + "images" + File.separator;
          /*ClassLoader loader = this.getClass().getClassLoader();
          java.net.URL url = loader.getResource("."+File.separator+"images"+File.separator+"YinyangOrb.gif");
          System.out.println("url: "+"images"+File.separator+"YinyangOrb.gif");
          System.out.println(url.toString());*/

          // System.out.println(System.getProperty("user.dir"));
          // Image img = Toolkit.getDefaultToolkit().getImage(java.net.URLClassLoader.getSystemResource(strIconPath+"images.jpg"));
          try {
            m_iconTag[0] = new ImageIcon(strIconPath + "YinyangOrb.png");
            m_iconTag[1] = new ImageIcon(strIconPath + "PurpleOrb.png");
            m_iconTag[2] = new ImageIcon(strIconPath + "BlueOrb.png");
            m_iconTag[3] = new ImageIcon(strIconPath + "RedOrb.png");
            m_iconTag[4] = new ImageIcon(strIconPath + "YellowOrb.png");
            m_iconTag[5] = new ImageIcon(strIconPath + "GreenOrb.png");
            m_frame.setIconImage(m_iconTag[0].getImage());
          }
          catch (Exception e) {
            e.printStackTrace();
          }
          // Setup the tabs
          m_tabbedPane.addTab("Test Design", m_iconTag[1], m_panelTD);
          m_tabbedPane.addTab("Code viewer", m_iconTag[2], m_panelCV);
          m_tabbedPane.addTab("Result viewer", m_iconTag[3], m_panelRV);
          m_tabbedPane.addTab("Manual test design", m_iconTag[4], m_panelEA);
          m_tabbedPane.addTab("Model coverage graph", m_iconTag[5], m_panelC);
          //TODO fix the index to the icon for this tab
          m_tabbedPane.addTab("Model Visualisation", m_iconTag[5], m_panelGV);

          m_tabbedPane.addChangeListener(new TabChangeListener());
          m_panelOption
              .setLayout(new BoxLayout(m_panelOption, BoxLayout.Y_AXIS));
          m_panelOption.add(Box.createHorizontalStrut(80));
          m_butRun.setMaximumSize(new Dimension(200,25));
          m_panelOption.add(m_butRun);
          m_panelOption.add(Box.createHorizontalGlue());
          m_frame.setLayout(new BorderLayout());
          m_frame.getContentPane().add(m_tabbedPane, BorderLayout.CENTER);
          m_frame.getContentPane().add(m_panelOption, BorderLayout.SOUTH);
          m_frame.pack();
          m_frame.setSize(800, 680); // force the VisualisationPanel smaller!
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
     * ButtonGroup buttonGroup = new ButtonGroup();
     * final UIManager.LookAndFeelInfo[] info = UIManager.getInstalledLookAndFeels();
     * for (int i = 0; i < info.length; i++) {
     *   JRadioButtonMenuItem item = new
     *   JRadioButtonMenuItem(info[i].getName(), i == 0);
     *   final String className = info[i].getClassName();
     *   item.addActionListener(new ActionListener() {
     *     public void actionPerformed(ActionEvent ae) {
     *       try { UIManager.setLookAndFeel(className); }
     *       catch (Exception e) { System.out.println(e); }
     *       SwingUtilities.updateComponentTreeUI(ToUChyFeely.this);
     *     }
     *   });
     *   buttonGroup.add(item);
     *   file.add(item);
     * }
     * mb.add(file);
     * setJMenuBar(mb);
     */
    // Menu and menu items
    m_menuBar = new JMenuBar();
    // File menu
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

    m_miCoverageColor = new JMenuItem("Coverage line color");
    m_miCoverageColor.addActionListener(this);
    sMenu.add(m_miCoverageColor);

    m_menuBar.add(sMenu);
    // About menu
    JMenu aMenu = new JMenu("About");
    aMenu.setMnemonic('a');
    m_miAbout = new JMenuItem("Version");
    m_miAbout.addActionListener(this);
    aMenu.add(m_miAbout);
    m_menuBar.add(aMenu);
    m_frame.setJMenuBar(m_menuBar);
  }

  /** Call this whenever a new model is loaded/chosen.
   *  It tells all the tabs about the new model, so that they can
   *  clear any old state.
   */
  public void newModel()
  {
    m_panelTD.newModel();
    m_panelCV.newModel();
    m_panelRV.newModel();
    m_panelEA.newModel();
    m_panelC.newModel();
    m_panelGV.newModel();
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
    if (e.getSource() == m_miAbout) {
      DialogAbout aboutDlg = new DialogAbout(m_frame);
      aboutDlg.setLocation(new Point(100, 100));
      aboutDlg.setVisible(true);
    }
    if (e.getSource() == m_miCoverageColor) {
      DialogCoverageLineColor colorDlg = new DialogCoverageLineColor(m_frame);
      colorDlg.setLocation(new Point(100, 100));
      colorDlg.setVisible(true);
    }
    //-------------- Run button event handler -------------
    if (e.getSource() == m_butRun) {
      // No model imported
      if (!Parameter.isTestRunnable(false)) {
        ErrorMessage
            .DisplayErrorMessage("NO TEST MODEL HAS BEEN SELECTED",
                "Please select Test Model\n"
                +"from Test Design tab\n"
                +"before generating tests!");
        return;
      }

      String sourceFile = Parameter.getModelPath();
      String name[] = sourceFile.split("\\.");

      if (name.length == 2 && name[1].equalsIgnoreCase("class"))
        runClass();
    }
    // ------------- Export java file --------------
    if (e.getSource() == m_miFile) {
      String code = m_panelTD.generateCode();
      if (code.length() > 0) {
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
                  "Error creating file '"+nf.getAbsolutePath()
                  +"': "+e1.getLocalizedMessage());
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
    if (e.getSource() == m_miExit) {
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

  /**
   * Run test automatically
   */
  private void runClass()
  {
    // Draw line chart in coverage panel
    if (m_panelTD.isLineChartDrawable() && m_nCurrentPanelIndex == 4) {
      m_panelC.clearCoverages();
      int[] stages = m_panelC.computeStages(TestExeModel.getWalkLength());

      m_panelTD.initializeTester(0);
      Tester tester = TestExeModel.getTester(0);
      tester.buildGraph();

      CoverageHistory[] coverage = new CoverageHistory[TestExeModel.COVERAGE_NUM];
      coverage[0] = new CoverageHistory(new StateCoverage(), 1);
      coverage[1] = new CoverageHistory(new TransitionCoverage(), 1);
      coverage[2] = new CoverageHistory(new TransitionPairCoverage(), 1);
      coverage[3] = new CoverageHistory(new ActionCoverage(), 1);
      tester.addCoverageMetric(coverage[0]);
      tester.addCoverageMetric(coverage[1]);
      tester.addCoverageMetric(coverage[2]);
      tester.addCoverageMetric(coverage[3]);
      // Run test several times to draw line chart
      for (int i = 0; i < stages.length; i++) {
        tester.generate(stages[0]);
        // Update the line chart and repaint
        m_panelC.addStateCoverage((int) coverage[0].getPercentage());
        m_panelC.addTransitionCoverage((int) coverage[1].getPercentage());
        m_panelC.addTransitionPairCoverage((int) coverage[2].getPercentage());
        m_panelC.addActionCoverage((int) coverage[3].getPercentage());
        m_panelC.redrawGraph();
        try {
          Thread.sleep(100);
        }
        catch (InterruptedException e) {
          e.printStackTrace();
        }
      }
    }
    // To reset tester, it solve the problem that coverage matrix incorrect.
    m_panelTD.initializeTester(0);
    //reset the visualisation panel
    m_panelGV.resetRunTimeInformation();
    //Try to fully explore the complete graph before running the test explorations
    Tester tester = TestExeModel.getTester(0);
    GraphListener graph = tester.buildGraph();
    m_panelGV.showEmptyExploredGraph(graph);

    // Clear the information in Result viewer text area
    m_panelRV.resetRunTimeInformation();

    // Run test and display test output
    TestExeModel.runTestAuto();
    // Finish the visualisation panel. This effectively starts the animation.    
    m_panelGV.updateGUI(m_nCurrentPanelIndex==5);    

  }


  class TabChangeListener implements ChangeListener
  {
    public void stateChanged(ChangeEvent e)
    {

      JTabbedPane sourcePane = (JTabbedPane) e.getSource();

      m_nCurrentPanelIndex = sourcePane.getSelectedIndex();
      // Set run button visibility
      m_butRun.setVisible(m_nCurrentPanelIndex != 3);
      // Regenerate code
      if (!Parameter.isTestRunnable(false))
        return;
      updateGeneratedCode();

      // If user click the ExecuteAction pane
      //if (3 == m_nCurrentPanelIndex) {
      //  m_panelEA.resetSubComponents();
      //  m_panelEA.autoModelInitialization();
      //}
    }
  }
}
