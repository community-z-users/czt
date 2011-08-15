package net.sourceforge.czt.zeves.response.form;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * <!ELEMENT string EMPTY>
 * 
 * @author Andrius Velykis
 */
// FIXME: Change this name to something else? There is already a ZEvesResponseString from CoreJava :-( ; Leo...
@XmlRootElement(name = "string")
public class ZEvesResponseString {

	/**
	 * <!ATTLIST string value CDATA #REQUIRED>
	 */
	@XmlAttribute
	private String value;
	
	@Override
	public String toString() {
		return value;
	}
	
	public String getValue() {
		return value;
	}
	
}
