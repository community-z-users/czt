package net.sourceforge.czt.modeljunit.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JTextField;


public class OptionPanelRandomWalking extends OptionPanelAdapter 
	implements ActionListener, IAlgorithmParameter{

	/**
	 * 
	 */
	private static final long serialVersionUID = -7675450997014889733L;
	private JLabel m_labelLength;
	private JTextField m_txtLength;
	private StringBuffer m_bufRandomTest;
	
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

	@Override
	public String generateCode() {
		m_bufRandomTest = new StringBuffer();
		m_bufRandomTest.append("tester.randomWalk(");
		m_bufRandomTest.append(m_txtLength);
		m_bufRandomTest.append(");");
		return m_bufRandomTest.toString();
	}

	@Override
	public void initialize() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void loadParameters(BufferedReader bufReader) {
		m_bufRandomTest = new StringBuffer();
		try {
			m_bufRandomTest.append(bufReader.readLine());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void saveParameters(BufferedWriter bufWriter) {
		try {
			bufWriter.write(m_bufRandomTest.toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
}
