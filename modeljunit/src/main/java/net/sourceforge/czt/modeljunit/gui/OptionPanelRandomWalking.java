
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Random;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.JCheckBox;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.border.Border;

import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.modeljunit.examples.SimpleSet;

public class OptionPanelRandomWalking extends OptionPanelAdapter
    implements
      IAlgorithmParameter
{

  /**
   * Serial version UID
   */
  private static final long serialVersionUID = -7675450997014889733L;

  private StringBuffer m_bufRandomTest;

  private JCheckBox m_checkRandomSeed;

  public OptionPanelRandomWalking(String name, String explain, String imgPath)
  {
    super(name, explain, imgPath);
    // setLayout(new GridLayout(2,3,3,2));
    m_checkRandomSeed = new JCheckBox("Use random seed");
    add(m_checkRandomSeed);
    add(Box.createHorizontalStrut(6));
    add(Box.createHorizontalGlue());
    
    Border edge = BorderFactory.createLineBorder(Color.WHITE);

    this.setBorder(BorderFactory.createTitledBorder(
        edge, "Random walk algorithm pane"));
  }

  @Override
  public String generateCode()
  {
    m_bufRandomTest = new StringBuffer();

    // Initialize test model
    m_bufRandomTest.append(Indentation.wrap(Parameter.getClassName() + " model = new "
        + Parameter.getClassName() + "();"));
    m_bufRandomTest.append(Indentation.wrap("Tester tester = new RandomTester(model);"));
    // To use random seed or not
    // If user does not want to use random seed,
    // test will user tester.setRandom(new Random(tester.FIXEDSEED)),
    // Which makes application will generate same tests every time it runs.
    if(m_checkRandomSeed.isSelected())
      m_bufRandomTest.append(Indentation.wrap("tester.setRandom(new Random());"));

    return m_bufRandomTest.toString();
  }

  @Override
  public void initialize()
  {
    try
    {
    // Initialize model test case by using the loaded model
    // Tester tester = new GreedyTester(new SimpleSet());
    Class<?> testerClass =
      Class.forName("net.sourceforge.czt.modeljunit.RandomTester");
    Constructor<?> con = testerClass.getConstructor
      (new Class[]{Class.forName("net.sourceforge.czt.modeljunit.FsmModel")});
    m_tester =
      (RandomTester)con.newInstance(new Object[]{TestExeModel.getModelObject()});
    }catch(Exception exp)
    {
      exp.printStackTrace();
    }
  }

  @Override
  public void loadParameters(BufferedReader bufReader)
  {
    m_bufRandomTest = new StringBuffer();
    try {
      m_bufRandomTest.append(bufReader.readLine());
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }

  @Override
  public void saveParameters(BufferedWriter bufWriter)
  {
    try {
      bufWriter.write(m_bufRandomTest.toString());
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }
  @Override
  public String generateImportLab()
  {
    m_bufRandomTest = new StringBuffer();
    if(m_checkRandomSeed.isSelected())
    {
      m_bufRandomTest.append(Indentation.wrap("import java.util.Random;"));
    }
    m_bufRandomTest.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.RandomTester;"));
    return m_bufRandomTest.toString();
  }

  @Override
  public void runAlgorithm()
  {
    // Use random seed to generate test or not
    if(m_checkRandomSeed.isSelected())
    {
      Random rand = new Random();
      m_tester.setRandom(rand);
    }
    else
    {
      m_tester.setRandom(new Random(Tester.FIXEDSEED));
    }
  }
}
