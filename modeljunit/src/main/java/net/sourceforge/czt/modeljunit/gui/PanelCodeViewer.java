
package net.sourceforge.czt.modeljunit.gui;

import java.awt.BorderLayout;

import javax.swing.*;

public class PanelCodeViewer extends JPanel
{

  /**
   * 
   */
  private static final long serialVersionUID = -8433568076533100620L;

  private static PanelCodeViewer m_panelCV;

  private JTextArea m_txtCode;

  public static PanelCodeViewer createCodeViewer()
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
    m_txtCode.setEditable(false);
    add(scrollPane, BorderLayout.CENTER);
  }

  public void updateCode(String content)
  {
    // Clear the content in text area
    /*
    Document doc = m_txtCode.getDocument();
    try {
      doc.remove(0, doc.getLength());
    }
    catch (Exception exp) {
      exp.printStackTrace();
    }*/
    // Generate the code
    m_txtCode.setText(content);
    // Write the code into a file
    /*doc = m_txtCode.getDocument();
    try {
      doc.getText(0, doc.getLength());
    }
    catch (Exception exp) {
      exp.printStackTrace();
    }*/
  }
}
