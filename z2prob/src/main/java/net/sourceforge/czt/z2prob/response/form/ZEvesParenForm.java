package net.sourceforge.czt.zeves.response.form;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * Schema expressions, predicates, and expressions are not differentiated in
 * this syntax; the only reason to do so would be to decide whether certain
 * forms should be parenthesized (e.g., if expression vs. if predicate), and
 * that decision is made by Z/EVES and indicated with a <parenform> tag.
 * <parenform> is also used to indicate non-default precedence.
 * 
 * <!ELEMENT parenform (%form;, type?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "parenform")
public class ZEvesParenForm {

	/**
	 * <!ATTLIST parenform %kind; #REQUIRED>
	 */
	@XmlAttribute(required = true)
	private ZEvesKind kind;
	
	@XmlAnyElement(lax = true)
	private Object form;
	
	@XmlElement
	private ZEvesType type;
	
	@Override
	public String toString() {
		return "(" + String.valueOf(form) + ")";
	}
	
}
