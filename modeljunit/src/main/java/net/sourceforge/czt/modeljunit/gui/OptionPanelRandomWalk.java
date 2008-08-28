
package net.sourceforge.czt.modeljunit.gui;

import java.lang.reflect.Constructor;
import java.util.Random;

import javax.swing.Box;
import javax.swing.JCheckBox;

import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;

public class OptionPanelRandomWalk extends OptionPanelAdapter
    implements
      IAlgorithmParameter
{
  private static final long serialVersionUID = -7675450997014889733L;

  private StringBuffer m_bufRandomTest;

  private JCheckBox m_checkRandomSeed;

  public OptionPanelRandomWalk(String name, String explain, String imgPath)
  {
    super(name, explain, imgPath);
    m_checkRandomSeed = new JCheckBox("Use random seed");
    add(m_checkRandomSeed);
    add(Box.createHorizontalStrut(6));
    add(Box.createHorizontalGlue());
  }

  @Override
  public String generateCode()
  {
    m_bufRandomTest = new StringBuffer();

    // Initialize test model
    m_bufRandomTest.append(Indentation.indent(Parameter.getClassName()
        + " model = new " + Parameter.getClassName() + "();"));
    m_bufRandomTest.append(Indentation
        .indent("Tester tester = new RandomTester(model);"));
    // To use random seed or not
    // If user does not want to use random seed,
    // test will user tester.setRandom(new Random(tester.FIXEDSEED)),
    // Which makes application will generate same tests every time it runs.
    if (m_checkRandomSeed.isSelected())
      m_bufRandomTest.append(Indentation
          .indent("tester.setRandom(new Random());"));

    return m_bufRandomTest.toString();
  }

  @Override
  public void initialize(int idx)
  {
    try {
      // Initialize model test case by using the loaded model
      // Tester tester = new GreedyTester(new SimpleSet());
      Class<?> testerClass = Class
          .forName("net.sourceforge.czt.modeljunit.RandomTester");
      Constructor<?> con = testerClass.getConstructor(new Class[]{Class
          .forName("net.sourceforge.czt.modeljunit.FsmModel")});
      m_tester[idx] = (RandomTester) con.newInstance(new Object[]{TestExeModel
          .getModelObject()});
    }
    catch (Exception exp) {
      exp.printStackTrace();
    }
  }

  @Override
  public String generateImportLab()
  {
    m_bufRandomTest = new StringBuffer();
    if (m_checkRandomSeed.isSelected()) {
      m_bufRandomTest.append(Indentation.indent("import java.util.Random;"));
    }
    m_bufRandomTest.append(Indentation
        .indent("import net.sourceforge.czt.modeljunit.RandomTester;"));
    return m_bufRandomTest.toString();
  }

  @Override
  public void runAlgorithm(int idx)
  {
    // Use random seed to generate test or not
    if (m_checkRandomSeed.isSelected()) {
      Random rand = new Random();
      m_tester[idx].setRandom(rand);
    }
    else {
      m_tester[idx].setRandom(new Random(Tester.FIXEDSEED));
    }
  }
}
