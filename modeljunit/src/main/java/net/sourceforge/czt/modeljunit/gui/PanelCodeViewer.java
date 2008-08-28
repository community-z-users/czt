
package net.sourceforge.czt.modeljunit.gui;

import java.awt.BorderLayout;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

public class PanelCodeViewer extends PanelAbstract
{
  private static final long serialVersionUID = -8433568076533100620L;

  private static PanelCodeViewer m_panelCV;

  private JTextArea m_txtCode;

  //Use singleton pattern to get instance of code view panel
  public static PanelCodeViewer getCodeViewerInstance()
  {
    if (m_panelCV == null)
      m_panelCV = new PanelCodeViewer();
    return m_panelCV;
  }

  private PanelCodeViewer()
  {
    setLayout(new BorderLayout());
    m_txtCode = new JTextArea();
    JScrollPane scrollPane = new JScrollPane(m_txtCode);
    m_txtCode.setEditable(true);
    add(scrollPane, BorderLayout.CENTER);
  }

  public void updateCode(String content)
  {
    // Generate the code
    m_txtCode.setText(content);
  }
  
  public void newModel()
  {
    m_txtCode.setText("");
  }
}
