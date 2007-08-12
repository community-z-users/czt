package net.sourceforge.czt.modeljunit.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JLabel;

public class OptionPanelGreedy extends OptionPanelAdapter
	implements ActionListener{

	/**
	 * 
	 */
	private static final long serialVersionUID = -5507515122641604928L;
	private JLabel m_labelLength;
	public OptionPanelGreedy(){
		m_labelLength = new JLabel("Greedy algorithm options here.");
		add(m_labelLength);
	}
	
	@Override
	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
	}

}
