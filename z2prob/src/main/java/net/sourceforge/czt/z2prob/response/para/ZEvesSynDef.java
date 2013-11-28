package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.form.ZEvesName;

/**
 * <!ELEMENT syndef (name, name?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "syndef")
public class ZEvesSynDef {

	/**
	 * <!ATTLIST syndef opclass CDATA #REQUIRED>
	 */
	@XmlAttribute(name = "opclass", required = true)
	private String opClass;
	
	@XmlElement(name = "name")
	private List<ZEvesName> names = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@Override
	public String toString() {
		
		String name2Str = names.size() > 1 ? "; " + String.valueOf(names.get(1)) : "";
		
		return "syntax [" + opClass + "] " + String.valueOf(names.get(0)) + name2Str;
	}
	
}
