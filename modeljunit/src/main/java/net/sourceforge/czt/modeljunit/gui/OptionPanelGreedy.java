
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.FocusEvent;
import java.awt.event.FocusListener;
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

public class OptionPanelGreedy extends OptionPanelAdapter
    implements
      IAlgorithmParameter
{

  /**
   * Serial version ID
   */
  private static final long serialVersionUID = -3666437825873201003L;

  private StringBuffer m_bufCode;

  private JCheckBox m_checkRandomSeed;

  public OptionPanelGreedy(String name, String explain, String imgPath)
  {
    super(name, explain, imgPath);
    m_checkRandomSeed = new JCheckBox("Use random seed");
    add(m_checkRandomSeed);
    add(Box.createHorizontalStrut(6));
    add(Box.createHorizontalGlue());

    Border edge = BorderFactory.createLineBorder(Color.WHITE);

    this.setBorder(BorderFactory.createTitledBorder(
        edge, "Greedy algorithm pane"));
  }

  @Override
  public String generateCode()
  {
    m_bufCode = new StringBuffer();

    // Initialize test model
    m_bufCode.append(Indentation.wrap(Parameter.getClassName() + " model = new "
        + Parameter.getClassName() + "();"));
    m_bufCode.append(Indentation.wrap("GreedyTester tester = new GreedyTester(model);"));
    // To use random seed or not
    // If user does not want to use random seed,
    // test will user tester.setRandom(new Random(tester.FIXEDSEED)),
    // Which makes application will generate same tests every time it runs.
    if(m_checkRandomSeed.isSelected())
      m_bufCode.append(Indentation.wrap("tester.setRandom(new Random());"));

    double resetProb = Parameter.getResetProbability();
    if (resetProb != RandomTester.DEFAULT_RESET_PROBABILITY) {
      m_bufCode.append(Indentation.wrap("tester.setResetProbability("
          +String.format("%1$.3f", new Object[] {resetProb}) + ");"));
    }
    return m_bufCode.toString();
  }

  /**
   * Initialize tester and model
   * */
  @Override
  public void initialize(int idx)
  {
    try
    {
    // Initialize model test case by using the loaded model
    // Tester tester = new GreedyTester(new SimpleSet());
    Class<?> testerClass =
      Class.forName("net.sourceforge.czt.modeljunit.GreedyTester");
    Constructor<?> con = testerClass.getConstructor
      (new Class[]{Class.forName("net.sourceforge.czt.modeljunit.FsmModel")});
    m_tester[idx] =
      (GreedyTester)con.newInstance(new Object[]{TestExeModel.getModelObject()});
    }catch(Exception exp)
    {
      exp.printStackTrace();
    }
  }

  @Override
  public String generateImportLab()
  {
    m_bufCode = new StringBuffer();
    if(m_checkRandomSeed.isSelected())
      m_bufCode.append(Indentation.wrap("import java.util.Random;"));
    
    m_bufCode.append(Indentation.wrap("import net.sourceforge.czt.modeljunit.GreedyTester;"));
    return m_bufCode.toString();
  }

  @Override
  public void runAlgorithm(int idx)
  {
    // Set reset probability
    // caseObj.setResetProbability(Parameter.getResetProbility());
    if(m_checkRandomSeed.isSelected())
    {
      Random rand = new Random();
      m_tester[idx].setRandom(rand);
    }
    else
    {
      m_tester[idx].setRandom(new Random(Tester.FIXEDSEED));
    }
  }
}

