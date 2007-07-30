package net.sourceforge.czt.modeljunit.gui;
// For GUIs
import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
// For compiler
import javax.tools.Diagnostic;
import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

public class ModelJUnitGUI implements ActionListener{
	private JFrame m_frame;
	private AlgorithmPanel[] m_algo;
	private ImageIcon[] m_iconTag;
	private JTabbedPane m_tabbedPane = new JTabbedPane();
	private PanelTestDesign m_panelTD;
	private PanelCodeViewer m_panelCV;
	private PanelResultViewer m_panelRV;
	// The panel with run button
	private JPanel m_panelOption = new JPanel();
	private JButton m_butRun = new JButton("Run");
	
	public void createAndShowGUI(){
		m_butRun.addActionListener(this);
		Thread initializeImage = new Thread(){
			public void run(){
				try{
					m_frame = new JFrame("ModelJUnit GUI");
					m_frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
					/*m_iconTag = new ImageIcon[3];
					m_iconTag[0] = new ImageIcon(getClass().getResource("icon.gif"));
					m_iconTag[1] = new ImageIcon(getClass().getResource("icon.gif"));
					m_iconTag[2] = new ImageIcon(getClass().getResource("icon.gif"));*/
					// Initialize TestDesign panel
					m_panelTD = PanelTestDesign.createTestDesignPanel(); 
					// Initialize CodeViewer panel
					m_panelCV = PanelCodeViewer.createCodeViewer();
					// Initialize ResuleViewer panel
					m_panelRV = PanelResultViewer.createResultViewer();
					// Setup the tab
					m_tabbedPane.addTab("Test Design", m_panelTD);
					m_tabbedPane.addTab("Code viewer", m_panelCV);
					m_tabbedPane.addTab("Result viewer", m_panelRV);
					
					m_panelOption.setLayout(new BoxLayout(m_panelOption, BoxLayout.Y_AXIS));
					m_panelOption.add(Box.createHorizontalStrut(16));
					m_panelOption.add(m_butRun);
					m_panelOption.add(Box.createHorizontalGlue());
					m_frame.setLayout(new BorderLayout());
					m_frame.getContentPane().add(m_tabbedPane, BorderLayout.CENTER);
					m_frame.getContentPane().add(m_panelOption, BorderLayout.SOUTH);
					m_frame.pack();
					m_frame.setVisible(true);
				}catch(Exception exp){
					exp.printStackTrace();
				}
			} 
		};
		initializeImage.start();
	}

	protected void createTab(){
		
	}

	@Override
	// TEMP directory: System.getProperty("java.io.tmpdir")
	// LIB PATH directory:  System.getProperty("java.library.path")
	// CLASSPATH directory: System.getProperty("java.class.path")
	// SYSTEM DIR: System.getProperty("user.home")
	public void actionPerformed(ActionEvent e) {
		if(e.getSource() == m_butRun){
			String fileName = "Test.java";
			String currentDirectory = System.getProperty("user.dir");
			String sourceFile = currentDirectory+"\\"+fileName;
			System.out.println("File from: "+sourceFile);
			// Clear the result table
			m_panelRV.getTableModel().clearData();
			// Java compiler
			/**
			 * http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6477844
			 * Following statement will produce a null reference without exception
			 * it happens when I use only the JRE as Standard VM in Eclipse. 
			 * Please the JDK as Standard VM. It will work then.
			 * Window->Preferences->Installed JREs->
			 * Add C:\Program Files/Java/jdk1.6.0_02
			 */
			JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
			StandardJavaFileManager fileManager = compiler.getStandardFileManager(null, null, null);
			DiagnosticCollector<JavaFileObject> diagnostics = new DiagnosticCollector<JavaFileObject>();

	        Iterable<? extends JavaFileObject> compilationUnits = 
	        		fileManager.getJavaFileObjects(sourceFile);
	        JavaCompiler.CompilationTask task = 
	            compiler.getTask(null, fileManager, diagnostics, null, null, compilationUnits); 
	        task.call();
	        // Check the result
	        boolean bHasProblem = false;
	        for(Diagnostic d : diagnostics.getDiagnostics())
	        {
	        	// String type, String class name, String desc,String location, String path
	        	ResultDetails details = 
	        		new ResultDetails(
	        				d.getKind().name(),
	        				d.getClass().toString(),
	        				d.getMessage(null),
	        				"Line: "+Long.toString(d.getLineNumber())+
	        				", Column: "+Long.toString(d.getColumnNumber()),
	        				d.getSource().toString());
	        	m_panelRV.getTableModel().addData(details);
	        	bHasProblem = true;
	        }
	        // If there is no problem display successful compile message
	        if(!bHasProblem){
	        	ResultDetails details = 
	        		new ResultDetails(
	        				"Successfully compiled ",
	        				diagnostics.getDiagnostics().getClass().toString(),
	        				"","",
	        				sourceFile);
	        	m_panelRV.getTableModel().addData(details);
	        }
	        try {fileManager.close();} 
	        catch (IOException exp) {exp.printStackTrace();}

		}
		
	}
	private void saveData(){
		
	}
	class TabChangeListener implements ChangeListener {
		@Override
		public void stateChanged(ChangeEvent e) {
			saveData();
			}
		}
}
