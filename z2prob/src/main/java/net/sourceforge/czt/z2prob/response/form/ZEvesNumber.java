package net.sourceforge.czt.zeves.response.form;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * <!ELEMENT number EMPTY>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "number")
public class ZEvesNumber {

	/**
	 * <!ATTLIST number value CDATA #REQUIRED>
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
