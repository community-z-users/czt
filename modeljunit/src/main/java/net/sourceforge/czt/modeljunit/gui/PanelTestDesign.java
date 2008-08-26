
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.regex.Matcher;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSlider;
import javax.swing.JTextField;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import org.objectweb.asm.ClassReader;

import net.sourceforge.czt.modeljunit.Action;

/*
 * PanelTestDesign.java
 * @author rong ID : 1005450 26th Jul 2007
 */
public class PanelTestDesign extends JPanel
    implements
      ActionListener,
      FocusListener,
      ChangeListener
{
  private static final long serialVersionUID = 5316043261026727079L;

  // The index of paint graph check box
  private static final int CHECKBOX_PAINTGRAPH = 4;

  // There are 5 check boxes about coverage and paint graph
  private static final int NUM_GRAPH_CHECKBOX = 5;

  // 0 Random, 1 Greedy,
  private static final int ALGORITHM_NUM = OptionPanelCreator.NUM_PANE;

  /** The topmost (model) panel.
   *  This is for finding and loading the model class.
   */
  private JPanel m_panelModel;

  /** Labels for displaying information about the loaded model. */
  private JLabel m_modelInfo1, m_modelInfo2, m_modelInfo3;
  
  private static final String MSG_NO_MODEL = "(No model loaded yet)";

  /** The button for loading the model class. */
  private JButton m_butOpenModel;

  /** The button that runs the test generation. */
  private JButton m_butExternalExecute;

  /** true after user successfully loads a new model to test.
   * Once the tester and model are initialised, this variable should
   * be set to false
   */
  private boolean m_bNewModelLoaded = false;

  // Algorithm panel
  private final static int H_SPACE = 6;

  private JTextField m_txtLength;

  private int m_nCurAlgo;

  public int getCurrentAlgorithm()
  {
    return m_nCurAlgo;
  }

  /** The middle (algorithm) panel.
   *  This is for choosing test generation algorithm and options.
   */
  private JPanel m_panelAlgorithmBase;

  private JComboBox m_combAlgorithmSelection = new JComboBox();

  // min, max, initialize value
  private JSlider m_sliderAverageTestLength = new JSlider(JSlider.HORIZONTAL,
      1, 99, 1);

  private OptionPanelAdapter[] m_panelAlgorithm;

  JPanel m_algorithmRight;

  JPanel m_algorithmLeft;

  // Report panel
  private JCheckBox m_checkVerbosity = new JCheckBox(
      "Display the generated tests");

  private JCheckBox m_checkFailureVerbosity = new JCheckBox(
      "Display test failures in verbose mode (Not used yet)");

  /** The bottom (reporting) panel.
   *  This is for controlling the reports/statistics from the test generation.
   */
  private JPanel m_panelReport;

  private JCheckBox[] m_checkCoverage;

  private boolean[] m_bChecked;

  /** Main panel for the test design tab. */
  private static PanelTestDesign m_panel = null;

  /** Singleton factory method for creating the test design panel. */
  public static PanelTestDesign getTestDesignPanelInstance()
  {
    if (m_panel == null)
      m_panel = new PanelTestDesign();
    return m_panel;
  }

  /** Use PanelTestDesign to get a test design panel. */
  private PanelTestDesign()
  {
    // Panel background color
    Color[] bg = new Color[3];
    bg[0] = new Color(156, 186, 216);
    bg[1] = new Color(216, 186, 156);
    bg[2] = new Color(186, 216, 186);
    // Set test case variable name the name will affect code generation
    Parameter.setTestCaseVariableName("testCase");
    this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

    // ------ Setup model panel ------
    m_panelModel = new JPanel();
    m_panelModel.setLayout(new BoxLayout(m_panelModel, BoxLayout.X_AXIS));
    m_panelModel.setPreferredSize(new Dimension(400, 120));

    // The "Choose Model" button is on the left
    m_panelModel.add(Box.createHorizontalStrut(10));
    m_butOpenModel = new JButton("Load Model...");
    m_butOpenModel.setPreferredSize(new Dimension(120, 120));
    m_butOpenModel.addActionListener(this);
    m_butOpenModel.setToolTipText("Load a .class file that contains your test model");
    m_panelModel.add(m_butOpenModel);
    m_panelModel.add(Box.createHorizontalStrut(10));

    // An information area is to the right of the button.
    JPanel infoPane = new JPanel();
    infoPane.setLayout(new BoxLayout(infoPane, BoxLayout.Y_AXIS));
    infoPane.setBackground(bg[0]);
    m_modelInfo1 = new JLabel(" ");
    m_modelInfo2 = new JLabel(MSG_NO_MODEL);
    m_modelInfo3 = new JLabel(" ");
    //m_modelInfo.setPreferredSize(new Dimension(300, 80));
    infoPane.add(m_modelInfo1);
    infoPane.add(m_modelInfo2);
    infoPane.add(m_modelInfo3);
    m_panelModel.add(infoPane);
    
    m_panelModel.add(Box.createHorizontalGlue());
    
    // Set panel border
    m_panelModel.setBorder(new TitledBorder(new EtchedBorder(
        EtchedBorder.LOWERED), "Test model"));
    m_panelModel.setBackground(bg[0]);
    this.add(m_panelModel);
    this.add(Box.createVerticalStrut(H_SPACE));

    // ------ Initialize algorithm panel ------
    m_nCurAlgo = 0;
    m_panelAlgorithmBase = new JPanel();

    m_panelAlgorithm = OptionPanelCreator.createPanels();
    // Add algorithm names into combo box
    for (int i = 0; i < OptionPanelCreator.NUM_PANE; i++)
      m_combAlgorithmSelection.addItem(m_panelAlgorithm[i].getAlgorithmName());
    // Set default algorithm name
    Parameter.setAlgorithmName(OptionPanelCreator.ALGORITHM_NAME[0]);
    m_combAlgorithmSelection.addActionListener(this);
    
    // Setup slider
    m_sliderAverageTestLength.setValue((int) (1 / Parameter
        .getResetProbability()));
    m_sliderAverageTestLength.addChangeListener(this);
    m_sliderAverageTestLength.setToolTipText("Average walk length = "
        + (1 / Parameter.getResetProbability()));
    m_sliderAverageTestLength.setMajorTickSpacing(10);
    //m_sliderAverageTestLength.setPaintTicks(true);
    BoxLayout layout = new BoxLayout(m_panelAlgorithmBase, BoxLayout.X_AXIS);
    m_panelAlgorithmBase.setLayout(layout);

    m_algorithmLeft = new JPanel();
    GridBagLayout algGrid = new GridBagLayout();
    m_algorithmLeft.setLayout(algGrid);
    GridBagConstraints c = new GridBagConstraints();
    c.anchor = GridBagConstraints.LINE_START;
    // top, left, bottom, right
    c.insets = new Insets(10, 0, 3, 10);
    c.gridx = 0;
    c.gridy = 0;
    m_algorithmLeft.add(new JLabel("Algorithms"), c);
    c.gridx = 1;
    c.gridy = 0;
    m_algorithmLeft.add(m_combAlgorithmSelection, c);
    c.gridx = 0;
    c.gridy = 1;
    m_algorithmLeft.add(new JLabel("Test length"), c);
    c.gridx = 1;
    c.gridy = 1;
    m_algorithmLeft.add(m_sliderAverageTestLength, c);
    // Test walk length text field
    m_txtLength = new JTextField();
    m_txtLength.setColumns(5);
    m_txtLength.setText("10");
    m_txtLength.addFocusListener(this);
    // Set walk length to default value
    TestExeModel.setWalkLength(Integer.valueOf(m_txtLength.getText()));

    c.gridx = 0;
    c.gridy = 2;
    m_algorithmLeft.add(new JLabel("Walk length"), c);
    // m_txtLength.setMaximumSize(new Dimension(60,15));
    c.gridx = 1;
    c.gridy = 2;
    m_algorithmLeft.add(m_txtLength, c);

    // Try to set up the left and right parts to be equal
    //m_algorithmLeft.setAlignmentX(LEFT_ALIGNMENT);
    m_algorithmLeft.setMinimumSize(new Dimension(100,100));
    m_algorithmLeft.setPreferredSize(new Dimension(500,150));
    m_algorithmLeft.setMaximumSize(new Dimension(600,300));
    
    m_algorithmRight = new JPanel();
    m_algorithmRight.setMinimumSize(new Dimension(100,100));
    m_algorithmRight.setPreferredSize(new Dimension(200,150));
    m_algorithmRight.setMaximumSize(new Dimension(300,300));
    m_panelAlgorithmBase.add(m_algorithmRight);
    m_panelAlgorithmBase.add(m_algorithmLeft);
    // Add components
    addComponentsToTestGenerationPanel();
    //m_panelAlgorithmBase.add(m_panelDefaultOption);
    this.add(m_panelAlgorithmBase);
    m_panelAlgorithmBase.setBorder(new TitledBorder(new EtchedBorder(
        EtchedBorder.LOWERED), "Test generation"));
    //this.add(Box.createHorizontalStrut(H_SPACE));

    // ------------ Report setting panel ------------
    m_panelReport = new JPanel();
    // 7: there are 7 lines
    m_panelReport.setLayout(new GridLayout(7, 3, 7, 3));
    // Generate verbosity and failure verbosity
    m_checkVerbosity
        .setToolTipText("<html>Sets the level of progress messages "
            + "<br>that will be printed as this class builds the FSM graph and generates tests. </html>");
    // Can only use html tags separate lines in tool tip text "\n" doesnt work
    m_checkVerbosity.addActionListener(this);
    m_checkVerbosity.setBackground(bg[2]);
    m_checkVerbosity.setSelected(true);
    m_panelReport.add(m_checkVerbosity);
    m_panelReport.add(Box.createHorizontalStrut(10));
    m_panelReport.add(Box.createVerticalGlue());

    m_checkFailureVerbosity
        .setToolTipText("Sets the amount of information printed when tests fail.");
    m_checkFailureVerbosity.addActionListener(this);
    m_checkFailureVerbosity.setBackground(bg[2]);
    m_panelReport.add(m_checkFailureVerbosity);
    m_panelReport.add(Box.createHorizontalStrut(10));
    m_panelReport.add(Box.createHorizontalGlue());
    // Coverage matrix
    m_checkCoverage = new JCheckBox[NUM_GRAPH_CHECKBOX];
    m_checkCoverage[0] = new JCheckBox("State coverage");
    m_checkCoverage[1] = new JCheckBox("Transition coverage");
    m_checkCoverage[2] = new JCheckBox("Transition pair coverage");
    m_checkCoverage[3] = new JCheckBox("Action coverage");
    m_checkCoverage[CHECKBOX_PAINTGRAPH] = new JCheckBox(
        "Print graph to a file");

    m_bChecked = new boolean[NUM_GRAPH_CHECKBOX];
    for (int i = 0; i < NUM_GRAPH_CHECKBOX; i++) {
      m_checkCoverage[i].setBackground(bg[2]);
      m_checkCoverage[i].addActionListener(this);
      m_bChecked[i] = false;
      m_panelReport.add(m_checkCoverage[i]);
      m_panelReport.add(Box.createHorizontalStrut(10));
      m_panelReport.add(Box.createHorizontalGlue());
    }

    // set border
    m_panelReport.setBackground(bg[2]);
    m_panelReport.setBorder(new TitledBorder(new EtchedBorder(
        EtchedBorder.LOWERED), "Reporting"));
    this.add(m_panelReport);
    //this.add(Box.createVerticalGlue());
  }

  /**
   * If user successfully load a new model to test, return true,
   * Otherwise return false.
   **/
  public boolean isNewModelLoaded()
  {
    return m_bNewModelLoaded;
  }

  /**
   * If user successfully load a new model to test, set state to true,
   * Otherwise set to false.
   **/
  public void setModelLoadState(boolean state)
  {
    m_bNewModelLoaded = state;
  }

  public void setModelRelatedButton(JButton button)
  {
    button.setEnabled(false);  // disabled until user loads a model
    m_butExternalExecute = button;
  }

  public PanelTestDesign clone()
  {
    return null;
  }

  protected void addComponentsToTestGenerationPanel()
  {
    m_panelAlgorithmBase.remove(m_algorithmRight);
    m_nCurAlgo = m_combAlgorithmSelection.getSelectedIndex();
    m_algorithmRight = m_panelAlgorithm[m_nCurAlgo];
    m_panelAlgorithmBase.add(Box.createHorizontalStrut(16));
    m_panelAlgorithmBase.add(m_algorithmRight);
    m_panelAlgorithmBase.revalidate();
  }

  /**
   * After user successfully load a new model this method
   * will be involved to initialize model and tester to run test
   * and set the new model loaded flag to false.
   * */
  public void initializeTester(int idx)
  {
    // Generate the Tester object
    m_panelAlgorithm[m_nCurAlgo].initialize(idx);
    // Set current algorithm for prepare execution
    TestExeModel.setTester(m_panelAlgorithm[m_nCurAlgo].getTester(idx), idx);
    TestExeModel.setAlgorithm(m_panelAlgorithm[m_nCurAlgo]);
    m_bNewModelLoaded = false;
  }

  /**
   * If user checked any coverage check button
   * or want to generate .dot graph file.
   * Tester will build graph, this function will return ture.
   * Otherwise false.
   * */
  public boolean isLineChartDrawable()
  {
    return (m_checkCoverage[0].isSelected() || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected() || m_checkCoverage[3].isSelected())
        ? true
        : false;
  }

  /**
   * Including:
   *    Algorithm combobox handler
   *    Check button for coverage matrix
   *    Model loading button handler
   * */
  public void actionPerformed(ActionEvent e)
  {
    // ------------ Algorithm combobox handler --------------
    if (e.getSource() == this.m_combAlgorithmSelection) {
      addComponentsToTestGenerationPanel();
      for (int i = 0; i < ALGORITHM_NUM; i++) {
        if (i == m_nCurAlgo)
          m_panelAlgorithm[m_nCurAlgo].setVisible(true);
        else
          m_panelAlgorithm[i].setVisible(false);
      }
      // Display the algorithm related panel
      if (m_panelAlgorithm[m_nCurAlgo] == null)
        System.out.println("Error: Algorithm panel is null");

      m_algorithmRight.setToolTipText(m_panelAlgorithm[m_nCurAlgo]
          .getExplanation());
      // Update the setting
      Parameter.setAlgorithmName(m_panelAlgorithm[m_nCurAlgo]
          .getAlgorithmName());

    }
    // -------------- Check the coverage matrix options --------------
    for (int i = 0; i < NUM_GRAPH_CHECKBOX; i++) {
      if (e.getSource() == m_checkCoverage[i]) {
        m_bChecked[i] = !m_bChecked[i];
        Parameter.setCoverageOption(m_bChecked);
        if (i == CHECKBOX_PAINTGRAPH)
          Parameter.setGenerateGraph(m_checkCoverage[CHECKBOX_PAINTGRAPH]
              .isSelected());
      }
    }
    // ------- Model loading --------
    if (e.getSource() == m_butOpenModel) {
      openModelFromFile();
    }
    // ------- Verbosity comboboxes --------
    if (e.getSource() == m_checkVerbosity) {
      Parameter.setVerbosity(m_checkVerbosity.isSelected());
    }
    if (e.getSource() == m_checkFailureVerbosity) {
      Parameter.setFailureVerbosity(m_checkFailureVerbosity.isSelected());
    }
  }

  private void openModelFromFile()
  {
    // ------------ Open model from class file --------------
    String[] extensions = {"class"};
    FileChooserFilter javaFileFilter = new FileChooserFilter(extensions,
        "Java class Files");
    JFileChooser chooser = new JFileChooser();
    chooser.setCurrentDirectory(new File(Parameter.getModelChooserDirectory()));
    chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
    chooser.setDialogTitle("Open model file");
    chooser.addChoosableFileFilter(javaFileFilter);
    int option = chooser.showOpenDialog(this.m_panelModel);

    if (option == JFileChooser.APPROVE_OPTION) {
      String errmsg = null;  // null means no errors yet
      File f = chooser.getSelectedFile();
      String wholePath = f.getAbsolutePath();
      Parameter.setModelChooserDirectory(f.getParent());

      /*
      // Update the text field component
      m_txtFilePath.setText(Parameter.getClassName());
      // Set file chooser dialog initial directory
      m_txtFilePath.setCaretPosition(0);
      m_txtFilePath.setToolTipText(Parameter.getModelPath());
       */
      
      // Use ASM to read the package and class name from the .class file
      try {
        ClassReader reader = new ClassReader(new FileInputStream(f));
        String internalName = reader.getClassName();
        int slash = internalName.lastIndexOf('/');
        String className = internalName.substring(slash+1);
        String packageName = "";
        if (slash >= 0) {
          packageName = internalName.substring(0, slash).replaceAll("/", ".");
        }
        //System.out.println("f.absolutePath="+f.getAbsolutePath());
        //System.out.println("internalName="+internalName);
        //System.out.println("className="+className);
        //System.out.println("packageName="+packageName);

        // now calculate the classpath for this .class file.
        String sep = Matcher.quoteReplacement(File.separator);
        String ignore = ("/"+internalName+".class").replaceAll("/", sep);
        System.out.println("ignore="+ignore);
        if (wholePath.endsWith(ignore)) {
          String classPath = wholePath.substring(0, wholePath.lastIndexOf(ignore));
          System.out.println("MU: classPath="+classPath);
          Parameter.setModelPath(wholePath);
          Parameter.setClassName(className);
          Parameter.setPackageName(packageName);
          Parameter.setPackageLocation(classPath);
        }
        else {
          errmsg = "Error calculating top of package from: "+wholePath;
        }
      }
      catch (IOException ex) {
        errmsg = "Error reading .class file: "+ex.getLocalizedMessage();
      }
      System.out.println("errmsg="+errmsg);

      // Load model from file and initialize the model object
      int actionNumber = 0;
      if (errmsg == null) {
        TestExeModel.loadModelClassFromFile();
        Class<?> testcase = TestExeModel.getModelClass();
        for (Method method : testcase.getMethods()) {
          if (method.isAnnotationPresent(Action.class)) {
            actionNumber++;
            TestExeModel.addMethod(method);
          }
        }
        // Failed to load model
        if (actionNumber == 0) {
          errmsg = "Invalid model class: no @Action methods.";
        }
      }
      if (errmsg == null) {
        // Successfully load a new model
        m_bNewModelLoaded = true;
        //m_butExternalExecute.setText("");
        String cName = Parameter.getPackageName()+"."+Parameter.getClassName();
        m_modelInfo1.setText("Model:   "+cName);
        m_modelInfo2.setText("Path:     "+Parameter.getPackageLocation());
        m_modelInfo3.setText("Actions: "+actionNumber + " actions were loaded.");
      }
      else {
        ErrorMessage.DisplayErrorMessage("Error loading model", errmsg);
        TestExeModel.resetModelToNull();
        m_bNewModelLoaded = false;
        m_modelInfo1.setText(" ");
        m_modelInfo2.setText(MSG_NO_MODEL);
        m_modelInfo3.setText(" ");
      }
      m_butExternalExecute.setEnabled(m_bNewModelLoaded);
    }
  }

  public String generateCode()
  {
    // Random walking length
    int length = Integer.valueOf(m_txtLength.getText());
    if (Parameter.getClassName() == null
        || Parameter.getClassName().length() <= 0)
      return "";
    StringBuffer buf = new StringBuffer();

    // String strTestCase = Parameter.getTestCaseVariableName();
    if (m_nCurAlgo != 0
        && m_panelAlgorithm[m_nCurAlgo].generateImportLab() != null)
      buf.append(m_panelAlgorithm[m_nCurAlgo].generateImportLab());

    buf.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.*;"));
    // Import coverage history file(s)
    if (m_checkCoverage[0].isSelected() || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected()) {
      buf
          .append(Indentation
              .wrap("import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;"));
    }
    // Import state coverage lab
    if (m_checkCoverage[0].isSelected()) {
      buf
          .append(Indentation
              .wrap("import net.sourceforge.czt.modeljunit.coverage.StateCoverage;"));
    }
    // Import transition coverage lab
    if (m_checkCoverage[1].isSelected()) {
      buf
          .append(Indentation
              .wrap("import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;"));
    }
    // Import state transition pair coverage lab
    if (m_checkCoverage[2].isSelected()) {
      buf
          .append(Indentation
              .wrap("import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;"));
    }
    // Import state action coverage lab
    if (m_checkCoverage[3].isSelected()) {
      buf
          .append(Indentation
              .wrap("import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;"));
    }
    // Generate class content
    buf.append(Indentation.SEP);
    buf.append(Indentation.wrap("public class " + Parameter.getClassName()
        + "Tester" + Indentation.SEP + "{"));
    buf.append(Indentation.wrap("public static void main(String args[])"));
    buf.append(Indentation.wrap("{"));

    // Generate code according to particular algorithm.
    buf.append(m_panelAlgorithm[m_nCurAlgo].generateCode());

    // If user want to check coverage or draw dot graph,
    // build graph before add coverage listener.
    if (m_checkCoverage[0].isSelected() || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected() || m_checkCoverage[3].isSelected()) {
      if (m_checkCoverage[CHECKBOX_PAINTGRAPH].isSelected())
        buf.append(Indentation
            .wrap("GraphListener graph = tester.buildGraph();"));
      else
        buf.append(Indentation.wrap("tester.buildGraph();"));
      buf.append(Indentation.SEP);
    }

    // Setup coverage matrix
    if (m_checkCoverage[0].isSelected() || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected() || m_checkCoverage[3].isSelected()) {
      buf.append(Indentation.SEP);
      if (m_checkCoverage[0].isSelected()) {
        buf.append(Indentation
            .wrap("CoverageHistory stateCoverage = new StateCoverage();"));
        buf
            .append(Indentation
                .wrap("tester.addCoverageMetric(stateCoverage);"));
        buf.append(Indentation.SEP);
      }
      if (m_checkCoverage[1].isSelected()) {
        buf
            .append(Indentation
                .wrap("CoverageHistory transitionCoverage = new TransitionCoverage();"));
        buf.append(Indentation
            .wrap("tester.addCoverageMetric(transitionCoverage);"));
        buf.append(Indentation.SEP);
      }
      if (m_checkCoverage[2].isSelected()) {
        buf
            .append(Indentation
                .wrap("CoverageHistory transitionPairCoverage = new TransitionPairCoverage();"));
        buf.append(Indentation
            .wrap("tester.addCoverageMetric(transitionPairCoverage);"));
        buf.append(Indentation.SEP);
      }
      if (m_checkCoverage[3].isSelected()) {
        buf.append(Indentation
            .wrap("CoverageHistory actionCoverage = new ActionCoverage();"));
        buf.append(Indentation
            .wrap("tester.addCoverageMetric(actionCoverage);"));
        buf.append(Indentation.SEP);
      }
    }
    // Verbose settings
    if (this.m_checkVerbosity.isSelected()) {
      buf
          .append(Indentation
              .wrap("tester.addListener(\"verbose\", new VerboseListener(tester.getModel()));"));
      buf.append(Indentation.SEP);
    }

    buf.append(Indentation.wrap("tester.generate(" + length + ");"));

    if (m_checkCoverage[0].isSelected()) {
      buf.append(Indentation.SEP);
      buf
          .append(Indentation
              .wrap("System.out.println(\"State coverage: \"+stateCoverage.toString());"));
      buf
          .append(Indentation
              .wrap("System.out.println(\"State history : \"+stateCoverage.toCSV());"));
    }

    if (m_checkCoverage[1].isSelected()) {
      buf.append(Indentation.SEP);
      buf
          .append(Indentation
              .wrap("System.out.println(\"Transition coverage: \"+transitionCoverage.toString());"));
      buf
          .append(Indentation
              .wrap("System.out.println(\"Transition history : \"+transitionCoverage.toCSV());"));
    }

    if (m_checkCoverage[2].isSelected()) {
      buf.append(Indentation.SEP);
      buf
          .append(Indentation
              .wrap("System.out.println(\"Transition pair coverage: \"+transitionPairCoverage.toString());"));
      buf
          .append(Indentation
              .wrap("System.out.println(\"Transition pair history : \"+transitionPairCoverage.toCSV());"));
    }
    if (m_checkCoverage[3].isSelected()) {
      buf.append(Indentation.SEP);
      buf
          .append(Indentation
              .wrap("System.out.println(\"Action coverage: \"+actionCoverage.toString());"));
      buf
          .append(Indentation
              .wrap("System.out.println(\"Action history : \"+actionCoverage.toCSV());"));
    }

    if (m_checkCoverage[CHECKBOX_PAINTGRAPH].isSelected()) {
      buf.append(Indentation.wrap("graph.printGraphDot(\"map.dot\");"));
    }
    // Ending
    buf.append(Indentation.wrap("}"));
    buf.append(Indentation.wrap("}"));

    return buf.toString();
  }


  private class FileChooserFilter extends javax.swing.filechooser.FileFilter
  {
    private String m_description = null;

    private String[] m_extension = null;

    public FileChooserFilter(String[] extension, String description)
    {
      m_description = description;
      m_extension = new String[extension.length];
      for (int i = 0; i < extension.length; i++) {
        m_extension[i] = "." + extension[i].toLowerCase();
      }
    }

    public String getDescription()
    {
      return m_description;
    }

    @Override
    public boolean accept(File f)
    {
      if (f == null)
        return false;
      if (f.isDirectory())
        return true;
      for (int i = 0; i < m_extension.length; i++) {
        if (f.getName().toLowerCase().endsWith(m_extension[i]))
          return true;
      }
      return false;
    }
  }

  public void stateChanged(ChangeEvent e)
  {
    if (e.getSource() == this.m_sliderAverageTestLength) {
      int avgLength = 1;
      JSlider source = (JSlider) e.getSource();
      if (!source.getValueIsAdjusting()) {
        avgLength = (int) source.getValue();
        double prob = (double) 1.0 / (double) (avgLength + 1);
        Parameter.setResetProbability(prob);
        m_sliderAverageTestLength.setToolTipText("Average walk length: "
            + (1 / Parameter.getResetProbability()));
        // System.out.println("(PaneltestDesign.java)Average length :"+prob);
      }
    }
  }

  @Override
  public void focusGained(FocusEvent e)
  {
  }

  @Override
  public void focusLost(FocusEvent e)
  {
    if (e.getSource() == m_txtLength) {
      TestExeModel.setWalkLength(Integer.valueOf(m_txtLength.getText()));
    }

  }
}
