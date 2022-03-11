package net.sourceforge.czt.zeves.response.para;

import javax.xml.bind.annotation.XmlEnumValue;

/**
 * <!ENTITY % ability "ability (enabled | disabled) #IMPLIED">
 * 
 * @author Andrius Velykis
 */
public enum ZEvesAbility {
	@XmlEnumValue("enabled")
	ENABLED,
	@XmlEnumValue("disabled")
	DISABLED;
	
	public static String getInfo(ZEvesAbility ability) {
		if (ability == null) {
			return "";
		}
		
		return "[" + ability.toString().toLowerCase() + "] ";
	}
	
}