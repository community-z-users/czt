
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.border.Border;

public class OptionPanelDefault extends OptionPanelAdapter
{
  private static final long serialVersionUID = -9005457035103622777L;

  private JLabel m_labelLength;

  public OptionPanelDefault(String name, String explain, String imgPath)
  {
    super(name, explain, imgPath);
    m_labelLength = new JLabel("Find algorithm options here.");
    add(m_labelLength);

    Border edge = BorderFactory.createLineBorder(Color.WHITE);

    this.setBorder(BorderFactory.createTitledBorder(edge));
  }
}
