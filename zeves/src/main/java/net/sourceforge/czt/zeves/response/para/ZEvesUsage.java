package net.sourceforge.czt.zeves.response.para;

import javax.xml.bind.annotation.XmlEnumValue;

/**
 * <!ENTITY % usage "usage (axiom | rule | grule | frule) #IMPLIED">
 * 
 * @author Andrius Velykis
 */
public enum ZEvesUsage {
	@XmlEnumValue("axiom")
	AXIOM,
	@XmlEnumValue("rule")
	RULE,
	@XmlEnumValue("grule")
	GRULE,
	@XmlEnumValue("frule")
	FRULE;
	
	public static String getInfo(ZEvesUsage usage) {
		if (usage == null) {
			return "";
		}
		
		if (usage == AXIOM) {
			// not displayed usually
			return "";
		}
		
		return usage.toString().toLowerCase() + " ";
	}
	
}