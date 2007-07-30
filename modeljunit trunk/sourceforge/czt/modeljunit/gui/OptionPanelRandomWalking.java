package net.sourceforge.czt.modeljunit.gui;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;


public class OptionPanelRandomWalking extends JPanel 
	implements ActionListener{

	private JLabel m_labelLength;
	private JTextField m_txtLength;
	public OptionPanelRandomWalking(){
		m_labelLength = new JLabel("Random walk length:");
		m_txtLength = new JTextField();
		m_txtLength.setColumns(5);
		//m_txtLength.setPreferredSize(new Dimension(16,20));
		setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
		add(Box.createHorizontalStrut(6));
		add(m_labelLength);
		add(Box.createHorizontalStrut(6));
		add(m_txtLength);
		add(Box.createHorizontalGlue());
	}
	
	@Override
	public void actionPerformed(ActionEvent arg0) {
		// TODO Auto-generated method stub
		
	}
}
