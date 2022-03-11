package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

/**
 * <!ELEMENT rename (name, name)>
 * 
 * @author Andrius Velykis
 */
public class ZEvesRename {

	@XmlElement(name = "name")
	private List<ZEvesName> names = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@Override
	public String toString() {
	        /*
	         * For now use Replace instead of rename. This is because Z/EVES CZT parser
	         * does not support mixed cases of rename/replace. Since we cannot escape
	         * replace, and renaming can be substituted by one, we use replace everywhere
	         * for successful parsing.
	         */
		return String.valueOf(names.get(0)) + " := " + String.valueOf(names.get(1));
//		return String.valueOf(names.get(0)) 
//				+ ZString.SPACE + ZString.SLASH + ZString.SPACE
//				+ String.valueOf(names.get(1));
	}
	
}
