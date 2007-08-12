/**
 * @author rong
 * The TestingParameter class includes all the value of PanelTestDesign,
 * Application can store these parameters into file or load them from file
 * */
package net.sourceforge.czt.modeljunit.gui;

public class TestingParameter {

	public String m_strClassName;
	public String m_strModelLocation;
	public String m_strAlgorithmName;
	public boolean[] m_bCoverageOption;
	
	public TestingParameter()
	{
		m_bCoverageOption = new boolean[3];
	}
	
	public TestingParameter(String className, 
			String path, 
			String algorithmName, 
			boolean[] coverage)
	{
		m_strClassName = className;
		m_strModelLocation = path;
		m_strAlgorithmName = algorithmName;
		m_bCoverageOption = coverage;
	}
	@Override
	public String toString()
	{ 
		return "class name: "+m_strClassName 
			+ ", \nLocation: " + m_strModelLocation
			+ ", \nAlgorithm: " + m_strAlgorithmName
			+ ", \nCoverage: " + m_bCoverageOption[0]
			+", "+m_bCoverageOption[1]+", "
			+m_bCoverageOption[2]+".";
	}
}
