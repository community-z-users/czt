package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.XmlAnyElementList;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesDecl;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesSchName;

/**
 * axiomatic and generic definition
 * <!ELEMENT axdef (formals?, decpart, axpart?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "axdef")
public class ZEvesAxDef {

	/**
	 * <!ATTLIST axdef %ability;>
	 */
	@XmlAttribute
	private ZEvesAbility ability;
	
	/**
	 * <!ELEMENT formals (name+)>
	 */
	@XmlElementWrapper(name = "formals")
	@XmlElement(name = "name")
	private List<ZEvesName> formals = new ArrayList<ZEvesName>();
	
	
	/**
	 * <!ELEMENT decpart (decl | schname)+>
	 */
	@XmlElementWrapper(name = "decpart", required = true)
	@XmlElements({
		@XmlElement(name = "decl", type=ZEvesDecl.class),
		@XmlElement(name = "schname", type=ZEvesSchName.class) })
	private List<?> decPart = new ArrayList<Object>();
	
	
	/**
	 * <!ELEMENT axpart (labeledform | %form;)+>
	 */
	@XmlElement(name = "axpart")
	private XmlAnyElementList axPart = new XmlAnyElementList();

	@Override
	public String toString() {
		
		String formalsStr = !formals.isEmpty() ? 
				"[" + ZEvesResponseUtil.concat(formals, ", ") + "]" : "";
		String axStr = !axPart.getItems().isEmpty() ? 
				ZEvesResponseUtil.concat(axPart.getItems(), "\n") : "";

		return ZEvesAbility.getInfo(ability) + ZString.AX + "\n" + formalsStr
				+ ZEvesResponseUtil.concat(decPart, "\n") + "\n" + ZString.VL + "\n" 
				+ axStr + "\n" + ZString.ENDCHAR;
	}
	
}
