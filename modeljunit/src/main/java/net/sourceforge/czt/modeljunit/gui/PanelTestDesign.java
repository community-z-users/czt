
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;

import javax.swing.*;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import net.sourceforge.czt.modeljunit.ModelTestCase;

public class PanelTestDesign extends JPanel implements ActionListener,ChangeListener
{

  /**
   * 
   */
  private static final long serialVersionUID = 5316043261026727079L;

  // Model panel
  private JPanel m_panelModel;

  private JLabel m_labTestModel = new JLabel("Test Model:");

  private JTextField m_txtFilePath;

  private JButton m_butOpenModel;
  
  private JButton m_butExternalExecute;

  // Algorithm panel
  private final static int H_SPACE = 6;

  private int m_nCurAlgo;

  public int getCurrentAlgorithm()
  {
    return m_nCurAlgo;
  }

  private JPanel m_panelAlgorithmBase;

  private JComboBox m_combAlgorithmSelection = new JComboBox();

  private JSlider m_sliderAverageTestLength = 
    new JSlider(JSlider.HORIZONTAL,1,100,5);
  
  private AlgorithmPanel[] m_panelAlgorithm;

  JPanel m_algorithmRight;
  
  JPanel m_algorithmLeft;
  // Report panel
  private JLabel m_labelVerbosity = new JLabel("Test Generation Verbosity");
  private JComboBox m_comboVerbosity = new JComboBox(new String[]{"0","1","2","3"});
  private JLabel m_labelFailureVerbosity = new JLabel("Test Failure Verbosity");
  private JComboBox m_comboFailureVerbosity = new JComboBox(new String[]{"0","1","2","3"});
  
  private JPanel m_panelReport;

  private final int m_nCheckBox = 4;

  private JCheckBox[] m_checkCoverage;

  private boolean[] m_bChecked;

  // Base panel
  private static PanelTestDesign m_panel = null;

  public static PanelTestDesign createTestDesignPanel()
  {
    if (m_panel == null)
      m_panel = new PanelTestDesign();
    return m_panel;
  }

  private PanelTestDesign()
  {
    // Set test case variable name the name will affect code generation 
    Parameter.setTestCaseVariableName("testCase");
    this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
    // ------ Setup model panel ------
    m_txtFilePath = new JTextField();
    m_txtFilePath.setColumns(26);
    m_txtFilePath.setEditable(false);
    
    m_butOpenModel = new JButton("...");
    m_butOpenModel.addActionListener(this);
    m_panelModel = new JPanel();
    m_panelModel.setLayout(new FlowLayout());
    m_panelModel.add(m_labTestModel);
    m_panelModel.add(m_txtFilePath);
    m_panelModel.add(m_butOpenModel);
    m_panelModel.setPreferredSize(new Dimension(30, 40));
    m_panelModel.setBorder(
        new TitledBorder(
            new EtchedBorder (EtchedBorder.LOWERED),
            "Test model"));
    this.add(m_panelModel);
    this.add(Box.createVerticalStrut(H_SPACE));
    // ------ Initialize algorithm panel ------
    m_nCurAlgo = 0;
    m_panelAlgorithmBase = new JPanel();
    
    m_panelAlgorithm = new AlgorithmPanel[3];
    m_panelAlgorithm[0] = new AlgorithmPanel("Algorithm selection",
        "Select an algorithm from combobox.", "default.gif");
    m_panelAlgorithm[0].setOptionPanel(new OptionPanelDefault());
    m_panelAlgorithm[1] = new AlgorithmPanel("Random",
        "Random algorithm to travsal the model", "random.gif");
    m_panelAlgorithm[1].setOptionPanel(new OptionPanelRandomWalking());
    m_panelAlgorithm[2] = new AlgorithmPanel("Greedy",
        "Greedy algorithm to travsal the model", "greedy.gif");
    m_panelAlgorithm[2].setOptionPanel(new OptionPanelGreedy());
    m_combAlgorithmSelection.addItem(m_panelAlgorithm[0].getAlgorithmName());
    m_combAlgorithmSelection.addItem(m_panelAlgorithm[1].getAlgorithmName());
    m_combAlgorithmSelection.addItem(m_panelAlgorithm[2].getAlgorithmName());
    m_combAlgorithmSelection.addActionListener(this);
    // Setup slider 
    m_sliderAverageTestLength.addChangeListener(this);
    m_sliderAverageTestLength.setMajorTickSpacing(10);
    //m_sliderAverageTestLength.setPaintTicks(true);
    m_algorithmLeft = new JPanel();
    m_algorithmLeft.setLayout(new BoxLayout(m_algorithmLeft, BoxLayout.Y_AXIS));
    
    m_panelAlgorithmBase.setLayout(new BoxLayout(m_panelAlgorithmBase,BoxLayout.X_AXIS));
    m_algorithmLeft.add(Box.createVerticalStrut(16));
    m_algorithmLeft.add(m_combAlgorithmSelection);
    m_algorithmLeft.add(Box.createVerticalStrut(16));
    m_algorithmLeft.add(m_sliderAverageTestLength);
    m_algorithmLeft.add(Box.createVerticalGlue());
    m_algorithmLeft.setPreferredSize(new Dimension(160,30));
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
    // ------ Report setting panel ------
    m_panelReport = new JPanel();
    m_panelReport.setLayout(new GridLayout(6,3,6,3));
    // Generation verbosity and failure verbosity
    m_labelVerbosity.setToolTipText("<html>Sets the level of progress messages " +
    		"<br>that will be printed as this class builds the FSM graph and generates tests. </html>" );
    m_panelReport.add(m_labelVerbosity);
    m_comboVerbosity.setSelectedIndex(2);
    // Can only use html tags separate lines in tool tip text "\n" doesnt work
    m_comboVerbosity.setToolTipText("<html>0 means no messages. " +
    	" <br>1 means statistical summaries only. " +
    	" <br>2 means also show each transition taken. " +
    	" <br>3 means also show progress messages as the FSM graph is built. </html>");
    m_comboVerbosity.addActionListener(this);
    m_panelReport.add(m_comboVerbosity);
    m_panelReport.add(Box.createVerticalGlue());
    m_panelReport.add(m_labelFailureVerbosity);
    m_labelFailureVerbosity.setToolTipText("Sets the amount of information printed when tests fail.");
    m_comboFailureVerbosity.setToolTipText("<html>0 means none. " +
    		"<br>1 means print a statistical summary of the number of failed tests. " +
    		"<br>2 means print a one line summary of each failed test. " +
    		"<br>3 means print more information about each failed test. </html>");
    m_comboFailureVerbosity.setSelectedIndex(3);
    m_comboFailureVerbosity.addActionListener(this);
    m_panelReport.add(m_comboFailureVerbosity);
    m_panelReport.add(Box.createHorizontalGlue());
    // Coverage matrix
    m_checkCoverage = new JCheckBox[m_nCheckBox];
    m_checkCoverage[0] = new JCheckBox("State coverage");
    m_checkCoverage[1] = new JCheckBox("Transition coverage");
    m_checkCoverage[2] = new JCheckBox("Transition pair coverage");
    m_checkCoverage[3] = new JCheckBox("Print graph");
    Color bg = new Color(206, 206, 206);

    m_bChecked = new boolean[m_nCheckBox];
    for (int i = 0; i < m_nCheckBox; i++) {
      m_checkCoverage[i].setBackground(bg);
      m_checkCoverage[i].addActionListener(this);
      m_bChecked[i] = false;
      m_panelReport.add(m_checkCoverage[i]);
      m_panelReport.add(Box.createHorizontalStrut(10));
      m_panelReport.add(Box.createHorizontalGlue());
    }
    
    // set border
    m_panelReport.setBackground(bg);
    m_panelReport.setBorder(
        new TitledBorder(
            new EtchedBorder (EtchedBorder.LOWERED),
            "Reporting"));
    this.add(m_panelReport);
    this.add(Box.createVerticalGlue());
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
    m_algorithmRight = m_panelAlgorithm[m_nCurAlgo].getOptionPanel();
    m_panelAlgorithmBase.add(Box.createHorizontalStrut(16));
    m_panelAlgorithmBase.add(m_algorithmRight);
    m_panelAlgorithmBase.revalidate();
  }
  @Override
  public void actionPerformed(ActionEvent e)
  {
    // ------------ Algorithm combo-box handler -------------- 
    if (e.getSource() == this.m_combAlgorithmSelection) {
      
      addComponentsToTestGenerationPanel();
      // Display the algorithm related panel
      if (m_panelAlgorithm[m_nCurAlgo].getOptionPanel() == null)
        System.out.println("Error: Algorithm panel is null");
      
      
      // Update the setting
      Parameter.setAlgorithmName(m_panelAlgorithm[m_nCurAlgo].getAlgorithmName());
    }
    // ------------ Open model from class file -------------- 
    if (e.getSource() == m_butOpenModel) {
      String[] extensions = {"java", "class"};
      FileChooserFilter javaFileFilter = new FileChooserFilter(extensions,
          "Java Files");
      JFileChooser chooser = new JFileChooser();
      if(Parameter.getFileChooserOpenMode() == 0)
        chooser.setCurrentDirectory(new File(Parameter.getModelChooserDirectory()));
      else
        chooser.setCurrentDirectory(new File(Parameter.DEFAULT_DIRECTORY));
      chooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
      chooser.setDialogTitle("Opne model file");
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
        Parameter.setModelChooserDirectory(f.getAbsolutePath());
        m_txtFilePath.setCaretPosition(0);
        m_txtFilePath.setToolTipText(Parameter.getModelLocation());
        // Load model from file and initialize the model object
        if(fileName.length ==2 && fileName[1].equalsIgnoreCase("class"))
        {
          Parameter.loadModelClassFromFile();
          m_butExternalExecute.setText("Run test");
        }
        else if(fileName.length ==2 && fileName[1].equalsIgnoreCase("java"))
        {
          m_butExternalExecute.setText("Compile java file");
        }
      }
    }
    // ------ Check the coverage matrix options ------ 
    for (int i = 0; i < m_nCheckBox; i++) {
      if (e.getSource() == m_checkCoverage[i]) {
        m_bChecked[i] = !m_bChecked[i];
        Parameter.setCoverageOption(m_bChecked);
        if(i==3)
          Parameter.setGenerateGraph(m_checkCoverage[3].isSelected());
      }
    }
    // ------- Verbosity comboboxes --------
    if(e.getSource() == this.m_comboVerbosity)
    {
      Parameter.setVerbosity(m_comboVerbosity.getSelectedIndex());
    }
    if(e.getSource() == this.m_comboFailureVerbosity)
    {
      Parameter.setFailureVerbosity(m_comboFailureVerbosity.getSelectedIndex());
    }
  }

  public String generateCode()
  {
    if(m_nCurAlgo<1 
        || m_panelAlgorithm[m_nCurAlgo].hasError()
        || Parameter.getClassName() == null
        || Parameter.getClassName().length()<=0)
      return "";
    StringBuffer buf = new StringBuffer();
    // For random walk using random seed or not
    String strTestCase = Parameter.getTestCaseVariableName();
    if (m_nCurAlgo == 1 && m_panelAlgorithm[1].generateImportLab() != null)
      buf.append(m_panelAlgorithm[1].generateImportLab());

    buf.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.*;"));
    //
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
    // Setup coverage matrix
    if(m_checkCoverage[0].isSelected() 
        || m_checkCoverage[1].isSelected() 
        || m_checkCoverage[2].isSelected())
    {
      if(m_checkCoverage[0].isSelected())
      {
        buf.append(Indentation.wrap("CoverageMetric stCoverage = new StateCoverage();"));
        buf.append(Indentation.wrap("ModelTestCase.addCoverageMetric(stCoverage);"));
      }
      if(m_checkCoverage[1].isSelected())
      {
        buf.append(Indentation.wrap("CoverageMetric trCoverage = new TransitionCoverage();"));
        buf.append(Indentation.wrap("ModelTestCase.addCoverageMetric(trCoverage);"));
      }
      if(m_checkCoverage[2].isSelected())
      {
        buf.append(Indentation.wrap("CoverageMetric tpCoverage = new TransitionCoverage();"));
        buf.append(Indentation.wrap("ModelTestCase.addCoverageMetric(tpCoverage);"));
      }
      buf.append(Indentation.SEP);
    }
    // Initialize test model
    buf.append(Indentation.wrap(Parameter.getClassName() + " model = new "
        + Parameter.getClassName() + "();"));
    buf.append(Indentation.wrap("ModelTestCase " + strTestCase
        + " = new ModelTestCase(model);"));
    buf.append(Indentation.wrap(strTestCase + ".setResetProbability("+Parameter.getResetProbility()+");"));
    buf.append(Indentation.wrap(strTestCase + ".setVerbosity("+Parameter.getVerbosity()+");"));
    buf.append(Indentation.wrap(strTestCase + ".setFailureVerbosity("+Parameter.getFailureVerbosity()+");"));
    // Generate code according to particular algorithm.
    buf.append(Indentation.SEP);
    buf.append(m_panelAlgorithm[m_nCurAlgo].generateCode());
    // Accurate coverage metrics 
    buf.append(Indentation.SEP);
    if(m_checkCoverage[3].isSelected())
    {
      buf.append(Indentation.wrap("testCase.buildGraph();"));
      buf.append(Indentation.wrap("try"));
      buf.append(Indentation.wrap("{"));
      buf.append(Indentation.wrap("testCase.printGraphDot(\""+Parameter.getClassName()+".dot\");"));
      buf.append(Indentation.wrap("}"));
      buf.append(Indentation.wrap("catch(Exception exp)"));
      buf.append(Indentation.wrap("{"));
      buf.append(Indentation.wrap("exp.printStackTrace();"));
      buf.append(Indentation.wrap("}"));
    }
    buf.append(Indentation.wrap("}"));
    buf.append(Indentation.wrap("}"));

    return buf.toString();
  }

  public String runTest()
  {
    String output = new String();
    // Redirect the system.out to result viewer text area component
    PrintStream ps = System.out; //Backup the System.out for later restore
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    System.setOut(new PrintStream(baos, true));

    ModelTestCase caseObj = m_panelAlgorithm[m_nCurAlgo].runAlgorithm();
    
    output = baos.toString();
    System.out.println(output);
    // Restore system.out to default value.
    System.setOut(ps);
    return output;
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

  @Override
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
        System.out.println("(PaneltestDesign.java)Average length :"+prob);
      }
    }
  }
}
