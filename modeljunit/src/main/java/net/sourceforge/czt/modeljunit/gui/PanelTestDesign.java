
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
import java.io.File;
import java.lang.reflect.Method;

import javax.swing.*;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import net.sourceforge.czt.modeljunit.Action;

/**
 * PanelTestDesign.java
 *
 * @author rong
 * ID : 1005450
 * 26th Jul 2007
 * */
public class PanelTestDesign extends JPanel 
  implements 
    ActionListener,
    FocusListener,
    ChangeListener
{
  /**
   * serial version ID
   */
  private static final long serialVersionUID = 5316043261026727079L;

  // Model panel
  private JPanel m_panelModel;

  private JTextField m_txtFilePath;

  private JButton m_butOpenModel;

  private JButton m_butExternalExecute;

  private JLabel m_labLoadingInfo = new JLabel("No model loaded");

  private JLabel m_labPackageName;

  private JButton m_butPackageName = new JButton("Package");
  // If user successfully load a new model to test, this variable will be set to true
  // Once the tester and model are initialized variable should be set to false
  private boolean m_bNewModelLoaded = false;
  
  // Algorithm panel
  private final static int H_SPACE = 6;

  private JTextField m_txtLength;

  private int m_nCurAlgo;

  public int getCurrentAlgorithm()
  {
    return m_nCurAlgo;
  }

  private JPanel m_panelAlgorithmBase;

  private JComboBox m_combAlgorithmSelection = new JComboBox();

  // min, max, initialize value
  private JSlider m_sliderAverageTestLength =
    new JSlider(JSlider.HORIZONTAL,1,99,1);

  private OptionPanelAdapter[] m_panelAlgorithm;

  JPanel m_algorithmRight;

  JPanel m_algorithmLeft;
  // Report panel
  private JCheckBox m_checkVerbosity = new JCheckBox("Display the generated tests");

  private JCheckBox m_checkFailureVerbosity = new JCheckBox("Display test failures in verbose mode (Not used yet)");

  private JPanel m_panelReport;

  private final int m_nCheckBox = 4;

  private JCheckBox[] m_checkCoverage;

  private boolean[] m_bChecked;

  // Base panel
  private static PanelTestDesign m_panel = null;

  // Singleton creator 
  public static PanelTestDesign getTestDesignPanelInstance()
  {
    if (m_panel == null)
      m_panel = new PanelTestDesign();
    return m_panel;
  }

  // The constructor
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
    
    m_txtFilePath = new JTextField(36);
    m_txtFilePath.setColumns(36);
    m_txtFilePath.setEditable(true);

    m_butOpenModel = new JButton("...");
    m_butOpenModel.addActionListener(this);
    m_butOpenModel.setToolTipText("HINT: load a .class file here");

    m_panelModel = new JPanel();

    m_panelModel.setLayout(new GridBagLayout());
    // Setup the grid bag layout
    GridBagConstraints c1 = new GridBagConstraints();
    c1.gridx = 0;
    c1.gridy = 0;
    c1.ipadx = 6;
    c1.fill = GridBagConstraints.HORIZONTAL;
    c1.anchor = GridBagConstraints.FIRST_LINE_START;
    m_panelModel.add(new JLabel("Test Model:"),c1);
    GridBagConstraints c2 = new GridBagConstraints();
    c2.gridx = 1;
    c2.gridy = 0;
    c2.ipadx = 6;
    c2.gridwidth = 3;
    c2.fill = GridBagConstraints.HORIZONTAL;
    c2.anchor = GridBagConstraints.PAGE_START;
    m_panelModel.add(m_txtFilePath,c2);
    GridBagConstraints c3 = new GridBagConstraints();
    c3.gridx = 5;
    c3.gridy = 0;
    c3.ipadx = 6;
    // Insets(top, left, down, right)
    c3.insets = new Insets(0,16,0,16);
    c3.anchor = GridBagConstraints.FIRST_LINE_END;
    c3.fill = GridBagConstraints.HORIZONTAL;
    m_panelModel.add(m_butOpenModel,c3);
    // Pixels between last line components and edge of panel
    int nBotDist = 6;
    // Package setting button
    GridBagConstraints c4 = new GridBagConstraints();
    c4.gridx = 0;
    c4.gridy = 1;
    // Insets(top, left, down, right)
    c4.insets = new Insets(0,0,nBotDist,16);
    m_butPackageName.addActionListener(this);
    m_panelModel.add(m_butPackageName,c4);
    // Package name label
    m_labPackageName = new JLabel(Parameter.getPackageName());
    GridBagConstraints c5 = new GridBagConstraints();
    c5.gridx = 1;
    c5.gridy = 1;
    c5.insets = new Insets(0,0,nBotDist,16);
    m_panelModel.add(m_labPackageName,c5);
    // Class loaded label
    GridBagConstraints c6 = new GridBagConstraints();
    c6.gridx = 2;
    c6.gridy = 1;
    c6.fill = GridBagConstraints.HORIZONTAL;
    c6.anchor = GridBagConstraints.PAGE_END;
    c6.insets = new Insets(0,0,nBotDist,16);
    m_panelModel.add(m_labLoadingInfo,c6);

    // Set panel size
    m_panelModel.setPreferredSize(new Dimension(160,50));
    // Set panel border
    m_panelModel.setBorder(
        new TitledBorder(
            new EtchedBorder (EtchedBorder.LOWERED),
            "Test model"));
    m_panelModel.setBackground(bg[0]);
    this.add(m_panelModel);
    this.add(Box.createVerticalStrut(H_SPACE));
    // ------ Initialize algorithm panel ------
    m_nCurAlgo = 0;
    m_panelAlgorithmBase = new JPanel();

    m_panelAlgorithm = new OptionPanelAdapter[3];
    m_panelAlgorithm = OptionPanelCreator.createPanels();
    /*m_panelAlgorithm[0] = OptionPanelCreator.createOptionPane(Parameter.ALGORITHM_NAME[0],
        "Select an algorithm from combobox.", "default.gif");
    
    m_panelAlgorithm[1] = OptionPanelCreator.createOptionPane(Parameter.ALGORITHM_NAME[1],
        "Random algorithm to traverse the model", "random.gif");
    
    m_panelAlgorithm[2] = OptionPanelCreator.createOptionPane(Parameter.ALGORITHM_NAME[2],
        "Greedy algorithm to traverse the model", "greedy.gif");*/
    // Add algorithm name into combobox
    for(int i=0;i<OptionPanelCreator.NUM_PANE;i++)
      m_combAlgorithmSelection.addItem(m_panelAlgorithm[i].getAlgorithmName());
    m_combAlgorithmSelection.addActionListener(this);
    // Setup slider
    
    m_sliderAverageTestLength.setValue((int)(1/Parameter.getResetProbility()));
    m_sliderAverageTestLength.addChangeListener(this);
    m_sliderAverageTestLength.setToolTipText("Average walk length: "+(1/Parameter.getResetProbility()));
    m_sliderAverageTestLength.setMajorTickSpacing(10);
    //m_sliderAverageTestLength.setPaintTicks(true);
    m_panelAlgorithmBase.setLayout(new BoxLayout(m_panelAlgorithmBase,BoxLayout.X_AXIS));

    m_algorithmLeft = new JPanel();
    m_algorithmLeft.setLayout(new GridBagLayout());
    GridBagConstraints c = new GridBagConstraints();
    c.anchor = GridBagConstraints.LINE_START;
    // top, left, bottom, right
    c.insets = new Insets(10,0,3,10);
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
    m_algorithmLeft.add(m_sliderAverageTestLength,c);
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

    m_algorithmRight = new JPanel();
    m_panelAlgorithmBase.add(m_algorithmRight);
    m_panelAlgorithmBase.add(m_algorithmLeft);
    // Add components
    addComponentsToTestGenerationPanel();
    //m_panelAlgorithmBase.add(m_panelDefaultOption);
    add(m_panelAlgorithmBase);
    m_panelAlgorithmBase.setBorder(
        new TitledBorder(
            new EtchedBorder (EtchedBorder.LOWERED),
            "Test generation"));
    add(Box.createHorizontalStrut(H_SPACE));
    // ------------ Report setting panel ------------
    m_panelReport = new JPanel();
    m_panelReport.setLayout(new GridLayout(6,3,6,3));
    // Generate verbosity and failure verbosity
    m_checkVerbosity.setToolTipText("<html>Sets the level of progress messages " +
    		"<br>that will be printed as this class builds the FSM graph and generates tests. </html>" );
    // Can only use html tags separate lines in tool tip text "\n" doesnt work
    m_checkVerbosity.addActionListener(this);
    m_checkVerbosity.setBackground(bg[2]);
    m_checkVerbosity.setSelected(true);
    m_panelReport.add(m_checkVerbosity);
    m_panelReport.add(Box.createHorizontalStrut(10));
    m_panelReport.add(Box.createVerticalGlue());

    m_checkFailureVerbosity.setToolTipText("Sets the amount of information printed when tests fail.");
    m_checkFailureVerbosity.addActionListener(this);
    m_checkFailureVerbosity.setBackground(bg[2]);
    m_panelReport.add(m_checkFailureVerbosity);
    m_panelReport.add(Box.createHorizontalStrut(10));
    m_panelReport.add(Box.createHorizontalGlue());
    // Coverage matrix
    m_checkCoverage = new JCheckBox[m_nCheckBox];
    m_checkCoverage[0] = new JCheckBox("State coverage");
    m_checkCoverage[1] = new JCheckBox("Transition coverage");
    m_checkCoverage[2] = new JCheckBox("Transition pair coverage");
    m_checkCoverage[3] = new JCheckBox("Print graph to a file");

    m_bChecked = new boolean[m_nCheckBox];
    for (int i = 0; i < m_nCheckBox; i++) {
      m_checkCoverage[i].setBackground(bg[2]);
      m_checkCoverage[i].addActionListener(this);
      m_bChecked[i] = false;
      m_panelReport.add(m_checkCoverage[i]);
      m_panelReport.add(Box.createHorizontalStrut(10));
      m_panelReport.add(Box.createHorizontalGlue());
    }

    // set border
    m_panelReport.setBackground(bg[2]);
    m_panelReport.setBorder(
        new TitledBorder(
            new EtchedBorder (EtchedBorder.LOWERED),
            "Reporting"));
    this.add(m_panelReport);
    this.add(Box.createVerticalGlue());
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

  public void updatePackageName()
  {
    String name = Parameter.getPackageName();
    m_labPackageName.setText(name);
    m_labPackageName.setToolTipText(name);
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
    TestExeModel.setTester(m_panelAlgorithm[m_nCurAlgo].getTester(idx),idx);
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
    return (m_checkCoverage[0].isSelected() ||
        m_checkCoverage[1].isSelected() ||
        m_checkCoverage[2].isSelected()||
        m_checkCoverage[3].isSelected())?true:false;
  }
  /**
   * Including:
   *    Algorithm combobox handler
   *    Package selection button handler
   *    Check button for coverage matrix
   *    Model loading button handler
   * */
  public void actionPerformed(ActionEvent e)
  {
    // ------------ Algorithm combo-box handler --------------
    if (e.getSource() == this.m_combAlgorithmSelection) 
    {  
      addComponentsToTestGenerationPanel();
      for(int i=0;i<3;i++)
      {
        if(i == m_nCurAlgo)
          m_panelAlgorithm[m_nCurAlgo].setVisible(true);
        else
          m_panelAlgorithm[i].setVisible(false);
      }
      // Display the algorithm related panel
      if (m_panelAlgorithm[m_nCurAlgo] == null)
        System.out.println("Error: Algorithm panel is null");

      // Update the setting
      Parameter.setAlgorithmName(m_panelAlgorithm[m_nCurAlgo].getAlgorithmName());
      
    }
 // ------------ Package selection button handler --------------
    if(e.getSource() == m_butPackageName)
    {
      // DialogPackageSelection dlg = DialogPackageSelection.createPackageSelectionDialog(this);
      // dlg.setVisible(true);
      DialogPackageURLSelection dlg = new DialogPackageURLSelection();
      dlg.setVisible(true);
    }
    // -------------- Check the coverage matrix options --------------
    for (int i = 0; i < m_nCheckBox; i++) {
      if (e.getSource() == m_checkCoverage[i]) {
        m_bChecked[i] = !m_bChecked[i];
        Parameter.setCoverageOption(m_bChecked);
        if(i==3)
          Parameter.setGenerateGraph(m_checkCoverage[3].isSelected());
      }
    }
    // ------- Model loading --------
    if (e.getSource() == m_butOpenModel)
    {
      openModelFromFile();
    }
    // ------- Verbosity comboboxes --------
    if(e.getSource() == m_checkVerbosity)
    {
      Parameter.setVerbosity(m_checkVerbosity.isSelected());
    }
    if(e.getSource() == m_checkFailureVerbosity)
    {
      Parameter.setFailureVerbosity(m_checkFailureVerbosity.isSelected());
    }
  }

  private void openModelFromFile()
  {
    // ------------ Open model from class file --------------

      String[] extensions = {"java", "class"};
      FileChooserFilter javaFileFilter = new FileChooserFilter(extensions,
          "Java Files");
      JFileChooser chooser = new JFileChooser();
      if(Parameter.getFileChooserOpenMode() == 0)
        // Open dialog from package location
        if(Parameter.getPackageLocation() != null && Parameter.getPackageLocation().length()>0)
          chooser.setCurrentDirectory(new File(Parameter.getPackageTopFolder()));
        else // Open dialog from last time record
          chooser.setCurrentDirectory(new File(Parameter.getModelChooserDirectory()));
      else
        chooser.setCurrentDirectory(new File(Parameter.DEFAULT_DIRECTORY));

      chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
      chooser.setDialogTitle("Open model file");
      chooser.addChoosableFileFilter(javaFileFilter);
      int option = chooser.showOpenDialog(this.m_panelModel);

      if (option == JFileChooser.APPROVE_OPTION) {
        File f = chooser.getSelectedFile();
        String[] fileName = f.getName().split("\\.");
        Parameter.setClassName(fileName[0]);
        Parameter.setModelLocation(f.getAbsolutePath());
        // Update the text field component
        m_txtFilePath.setText(Parameter.getClassName());
        // Set file chooser dialog initial directory
        Parameter.setModelChooserDirectory(f.getParent());
        m_txtFilePath.setCaretPosition(0);
        m_txtFilePath.setToolTipText(Parameter.getModelLocation());
        // Load model from file and initialize the model object
        if(fileName.length ==2 && fileName[1].equalsIgnoreCase("class"))
        {
          TestExeModel.loadModelClassFromFile();
          Class<?> testcase = TestExeModel.getModelClass();
          int actionNumber = 0;
          for(Method method : testcase.getMethods())
          {
            if(method.isAnnotationPresent(Action.class))
            {
              actionNumber++;
              TestExeModel.addMethod(method);
            }
          }
          // Failed to load model
          if(actionNumber==0)
          {
            ErrorMessage.DisplayErrorMessage(
                "NO ACTION IN THE CLASS",
                "Invalid model class, it doesnt includes any actions to test!");
            TestExeModel.resetModelToNull();
            m_bNewModelLoaded = false;
          }
          // Successfully load a new model
          else
          {
            m_bNewModelLoaded = true;
            m_labLoadingInfo.setText(actionNumber + " actions were loaded.");
          }
          // To get how many actions in the model file

          m_butExternalExecute.setText("Run test");
        }
        else if(fileName.length ==2 && fileName[1].equalsIgnoreCase("java"))
        {
          m_butExternalExecute.setText("Compile java file");
        }
      }
  }

  public String generateCode()
  {
    // Random walking length
    int length = Integer.valueOf(m_txtLength.getText());
    if(m_nCurAlgo<1
        || Parameter.getClassName() == null
        || Parameter.getClassName().length()<=0)
      return "";
    StringBuffer buf = new StringBuffer();

    // String strTestCase = Parameter.getTestCaseVariableName();
    if (m_nCurAlgo !=0 && m_panelAlgorithm[m_nCurAlgo].generateImportLab() != null)
      buf.append(m_panelAlgorithm[m_nCurAlgo].generateImportLab());

    buf.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.*;"));
    // Import coverage history file(s)
    if(m_checkCoverage[0].isSelected()
        || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;"));
    }
    // Import state coverage lab
    if(m_checkCoverage[0].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.StateCoverage;"));
    }
    // Import transition coverage lab
    if(m_checkCoverage[1].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;"));
    }
    // Import state transition pair coverage lab
    if(m_checkCoverage[2].isSelected())
    {
      buf.append(Indentation.wrap
        ("import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;"));
    }
    // Generate class content
    buf.append(Indentation.SEP);
    buf.append(Indentation.wrap("public class " + Parameter.getClassName()
        + "Tester"+Indentation.SEP+"{"));
    buf.append(Indentation.wrap("public static void main(String args[])"));
    buf.append(Indentation.wrap("{"));

    // Generate code according to particular algorithm.
    buf.append(m_panelAlgorithm[m_nCurAlgo].generateCode());
    
    // If user want to check coverage or draw dot graph, 
    // build graph before add coverage listener. 
    if(m_checkCoverage[0].isSelected()
        || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected()
        || m_checkCoverage[3].isSelected())
    {
      if(m_checkCoverage[3].isSelected())
        buf.append(Indentation.wrap("GraphListener graph = tester.buildGraph();"));
      else
        buf.append(Indentation.wrap("tester.buildGraph();"));
      buf.append(Indentation.SEP);
    }
    
    // Setup coverage matrix
    if(m_checkCoverage[0].isSelected()
        || m_checkCoverage[1].isSelected()
        || m_checkCoverage[2].isSelected())
    {
      buf.append(Indentation.SEP);
      if(m_checkCoverage[0].isSelected())
      {
        buf.append(Indentation.wrap("CoverageHistory stateCoverage = new StateCoverage();"));
        buf.append(Indentation.wrap("tester.addCoverageMetric(stateCoverage);"));
        buf.append(Indentation.SEP);
      }
      if(m_checkCoverage[1].isSelected())
      {
        buf.append(Indentation.wrap("CoverageHistory transitionCoverage = new TransitionCoverage();"));
        buf.append(Indentation.wrap("tester.addCoverageMetric(transitionCoverage);"));
        buf.append(Indentation.SEP);
      }
      if(m_checkCoverage[2].isSelected())
      {
        buf.append(Indentation.wrap("CoverageHistory transitionPairCoverage = new TransitionCoverage();"));
        buf.append(Indentation.wrap("tester.addCoverageMetric(transitionPairCoverage);"));
        buf.append(Indentation.SEP);
      }
    }
    // Verbose settings
    if(this.m_checkVerbosity.isSelected())
    {
      buf.append(Indentation.wrap("tester.addListener(\"verbose\", new VerboseListener(tester.getModel()));"));
      buf.append(Indentation.SEP);
    }

    buf.append(Indentation.wrap("tester.generate("+length+");"));
    
    if(m_checkCoverage[0].isSelected())
    {
      buf.append(Indentation.SEP);
      buf.append(Indentation.wrap("System.out.println(\"State coverage: \"+stateCoverage.toString());"));
      buf.append(Indentation.wrap("System.out.println(\"State history : \"+stateCoverage.toCSV());"));
    }
    
    if(m_checkCoverage[1].isSelected())
    {
      buf.append(Indentation.SEP);
      buf.append(Indentation.wrap("System.out.println(\"Transition coverage: \"+transitionCoverage.toString());"));
      buf.append(Indentation.wrap("System.out.println(\"Transition history : \"+transitionCoverage.toCSV());"));
    }
    
    if(m_checkCoverage[2].isSelected())
    {
      buf.append(Indentation.SEP);
      buf.append(Indentation.wrap("System.out.println(\"Transition pair coverage: \"+transitionPairCoverage.toString());"));
      buf.append(Indentation.wrap("System.out.println(\"Transition pair history : \"+transitionPairCoverage.toCSV());"));
    }
    
    if(m_checkCoverage[3].isSelected())
    { buf.append(Indentation.wrap("graph.printGraphDot(\"map.dot\");"));}
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
    if(e.getSource()==this.m_sliderAverageTestLength)
    {
      int avgLength = 1;
      JSlider source = (JSlider)e.getSource();
      if (!source.getValueIsAdjusting()) {
        avgLength = (int)source.getValue();
        double prob = (double)1.0/(double)(avgLength+1);
        Parameter.setResetProbility(prob);
        m_sliderAverageTestLength.setToolTipText("Average walk length: "+(1/Parameter.getResetProbility()));
        // System.out.println("(PaneltestDesign.java)Average length :"+prob);
      }
    }
  }

  @Override
  public void focusGained(FocusEvent e)
  {}
  @Override
  public void focusLost(FocusEvent e)
  {
    if(e.getSource() == m_txtLength)
    {
      TestExeModel.setWalkLength(Integer.valueOf(m_txtLength.getText()));
    }
    
  }
}
