package net.sourceforge.czt.zeves.response.form;

import javax.xml.bind.annotation.XmlAnyElement;

/**
 * Many forms allow for an optional "type" child element; this can be included
 * if output is to be fully annotated with type information.
 * 
 * <!ELEMENT type %form;>
 * 
 * @author Andrius Velykis
 */
public class ZEvesType {

	@XmlAnyElement(lax = true)
	private Object form;
	
}
