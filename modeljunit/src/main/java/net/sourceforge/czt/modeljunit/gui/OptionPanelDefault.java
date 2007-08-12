package net.sourceforge.czt.modeljunit.gui;

import javax.swing.JLabel;

public class OptionPanelDefault extends OptionPanelAdapter {

	/**
	 * 
	 */
	private static final long serialVersionUID = -9005457035103622777L;

	private JLabel m_labelLength;
	public OptionPanelDefault(){
		m_labelLength = new JLabel("Find algorithm options here.");
		add(m_labelLength);
	}
}
