package net.sourceforge.czt.zeves.response.para;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * <!ELEMENT labeledform (%form;)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "labeledform")
public class ZEvesLabeledForm {
	
	/**
	 * <!ATTLIST labeledform %ability;>
	 */
	@XmlAttribute
	private ZEvesAbility ability;
	
	/**
	 * <!ATTLIST labeledform %usage;>
	 */
	@XmlAttribute
	private ZEvesUsage usage;
	
	/**
	 * <!ATTLIST labeledform ident CDATA #REQUIRED>
	 */
	@XmlAttribute(required = true)
	private String ident;
	
	@XmlAnyElement(lax = true)
	private Object form;

	@Override
	public String toString() {
		return "\u300A" + ZEvesAbility.getInfo(ability) + ZEvesUsage.getInfo(usage) 
				+ ident	+ "\u300B " + String.valueOf(form);
	}
	
}
