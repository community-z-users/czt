package net.sourceforge.czt.modeljunit.gui;
import javax.swing.*;

public class PanelCodeViewer extends JPanel{

	private static PanelCodeViewer m_panelCV;
	
	public static PanelCodeViewer createCodeViewer(){
		if(m_panelCV==null)
			m_panelCV = new PanelCodeViewer();
		return m_panelCV;
	}
	private PanelCodeViewer(){
		
	}
}
