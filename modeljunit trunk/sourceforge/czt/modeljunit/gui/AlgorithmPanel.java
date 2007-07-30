package net.sourceforge.czt.modeljunit.gui;

import javax.swing.*;

public class AlgorithmPanel extends JPanel{
	private String m_strNameOfAlgorithm;
	private String m_strExplanation;
	private ImageIcon m_imgIcon;
	private JPanel m_panelOption;
	
	public AlgorithmPanel(String name, String explain, String imgPath){
		m_strNameOfAlgorithm = name;
		m_strExplanation = explain;
		//m_imgIcon = new ImageIcon(getClass().getResource("icon.gif"));
	}

	public String getAlgorithmName(){ return m_strNameOfAlgorithm; }
	
	public String getExplanation(){ return m_strExplanation; }
	
	public void setOptionPanel(JPanel panel){
		m_panelOption = panel;
	}
	public JPanel getOptionPanel(){ return m_panelOption; }
}
