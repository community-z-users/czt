package net.sourceforge.czt.modeljunit.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JLabel;
import javax.swing.JPanel;

public class OptionPanelGreedy extends JPanel
	implements ActionListener{

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
