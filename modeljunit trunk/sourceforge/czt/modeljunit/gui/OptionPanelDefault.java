package net.sourceforge.czt.modeljunit.gui;

import javax.swing.JLabel;
import javax.swing.JPanel;


public class OptionPanelDefault extends JPanel {

	private JLabel m_labelLength;
	public OptionPanelDefault(){
		m_labelLength = new JLabel("Find algorithm options here.");
		add(m_labelLength);
	}
}
