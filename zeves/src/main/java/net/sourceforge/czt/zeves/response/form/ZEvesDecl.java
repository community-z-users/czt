package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * <!ELEMENT decl (namelist, %form;)>
 * 
 * @author Andrius Velykis
 */
public class ZEvesDecl {

	/**
	 * <!ELEMENT namelist (name+)>
	 */
	@XmlElementWrapper(name = "namelist")
	@XmlElement(name = "name")
	private List<ZEvesName> names = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@XmlAnyElement(lax = true)
	private Object form;

	@Override
	public String toString() {
		return ZEvesResponseUtil.concat(names, ", ") + " : " + String.valueOf(form);
	}

}
