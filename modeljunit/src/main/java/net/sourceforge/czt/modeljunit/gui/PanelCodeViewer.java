package net.sourceforge.czt.modeljunit.gui;
import java.awt.BorderLayout;

import javax.swing.*;
import javax.swing.text.Document;

public class PanelCodeViewer extends JPanel{

	/**
	 * 
	 */
	private static final long serialVersionUID = -8433568076533100620L;
	private static PanelCodeViewer m_panelCV;
	private JTextArea m_txtCode;

	public static PanelCodeViewer createCodeViewer(){
		if(m_panelCV==null)
			m_panelCV = new PanelCodeViewer();
		return m_panelCV;
	}
	private PanelCodeViewer(){
		setLayout(new BorderLayout());
		m_txtCode = new JTextArea();
		JScrollPane scrollPane = new JScrollPane(m_txtCode); 
		m_txtCode.setEditable(false);
		add(scrollPane, BorderLayout.CENTER);
	}
	
	public void updateCode()
	{
		// Clear the content in text area
		Document doc = m_txtCode.getDocument();
		try{
			doc.remove(0, doc.getLength());
		}catch(Exception exp)
		{
			exp.printStackTrace();
		}
		// Generate the code
		m_txtCode.append("public static void main(String args[]) \n" +
				"{ \n" +
				"//set up our favourite coverage metrics \n" +
				"CoverageMetric trCoverage = new TransitionCoverage(); \n" +
				"ModelTestCase.addCoverageMetric(trCoverage); \n" +
				"// create our model and get ready to generate tests \n" +
				"FSM model = new FSM(); \n" +
				"ModelTestCase testgen = new ModelTestCase(model); \n" +
				"testgen.setVerbosity(2);  // show the generated test sequence \n" +
				"// generate a test suite of 20 steps \n" +
				"testgen.randomWalk(20); \n" +
				"// finish building the FSM of our model so that we get \n" +
				"// accurate coverage metrics. \n" +
				"testgen.buildGraph(); \n" +
				"System.out.println(trCoverage.getName()+ \" was \" +trCoverage.toString()); \n" +
				"}");
		// Write the code into a file
		doc = m_txtCode.getDocument();
		try{
			doc.getText(0, doc.getLength());
		}catch(Exception exp)
		{
			exp.printStackTrace();
		}
	}
}
