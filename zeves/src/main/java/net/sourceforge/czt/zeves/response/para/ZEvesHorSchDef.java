package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesSchName;

/**
 * schema definition (horizontal)
 * <!ELEMENT horschdef (schname, formals?, %form;)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "horschdef")
public class ZEvesHorSchDef {

	/**
	 * <!ATTLIST horschdef %ability;>
	 */
	@XmlAttribute
	private ZEvesAbility ability;
	
	@XmlElement(name = "schname", required = true)
	private ZEvesSchName name;
	
	/**
	 * <!ELEMENT formals (name+)>
	 */
	@XmlElementWrapper(name = "formals")
	@XmlElement(name = "name")
	private List<ZEvesName> formals = new ArrayList<ZEvesName>();
	
	
	@XmlAnyElement(lax = true)
	private Object form;

	@Override
	public String toString() {
		
		String formalsStr = !formals.isEmpty() ? 
				"[" + ZEvesResponseUtil.concat(formals, ", ") + "]" : "";
		
		return ZEvesAbility.getInfo(ability) + ZString.ZEDCHAR + String.valueOf(name) 
				+ formalsStr + " == " + String.valueOf(form) + "\n" + ZString.END;
	}
	
}
