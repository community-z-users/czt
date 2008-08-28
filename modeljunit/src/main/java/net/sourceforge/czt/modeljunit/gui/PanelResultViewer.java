
package net.sourceforge.czt.modeljunit.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

public class PanelResultViewer extends PanelAbstract
{
  private static final long serialVersionUID = -6522938608020451281L;

  private static PanelResultViewer m_panelRV;

  // Minimum height of the compile result table and text area
  private final int MIN_HEIGHT = 60;

  private final int INITIAL_WIDTH = 300;

  // Display the test runtime information
  private JTextArea m_txtOutput;

  //Scroll pane for test runtime info
  private JScrollPane m_scrollTextArea;

  public static PanelResultViewer getResultViewerInstance()
  {
    if (m_panelRV == null)
      m_panelRV = new PanelResultViewer();
    return m_panelRV;
  }

  private PanelResultViewer()
  {
    this.setLayout(new BorderLayout());

    // -------------------- Set up the split pane ------------------
    // Scroll pane for text area
    Dimension minimumSize = new Dimension(INITIAL_WIDTH, MIN_HEIGHT);
    m_txtOutput = new JTextArea();
    m_txtOutput.setEditable(false);

    m_scrollTextArea = new JScrollPane(m_txtOutput);
    //m_scrollTextArea.getViewport().setBackground(m_txtOutput.getBackground());
    m_scrollTextArea.getViewport().add(m_txtOutput);

    // Provide minimum sizes for the two components in the split pane.
    m_scrollTextArea.setMinimumSize(minimumSize);

    add(m_scrollTextArea, BorderLayout.CENTER);
  }

  public void resetRunTimeInformation()
  {
    m_txtOutput.setText("");
  }

  public void updateRunTimeInformation(String str)
  {
    m_txtOutput.append(str);
    m_txtOutput.paintImmediately(m_txtOutput.getBounds());
  }

  public void newModel()
  {
    resetRunTimeInformation();
  }
}
