package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * <!ELEMENT schematext (decpart, (%form;)?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "schematext")
public class ZEvesSchemaText {

	/**
	 * <!ELEMENT decpart (decl | schname)+>
	 */
	@XmlElementWrapper(name = "decpart", required = true)
	@XmlElements({
		@XmlElement(name = "decl", type=ZEvesDecl.class),
		@XmlElement(name = "schname", type=ZEvesSchName.class) })
	private List<?> decPart = new ArrayList<Object>();
	
	@XmlAnyElement(lax = true)
	private List<?> form = new ArrayList<Object>();
	
	@Override
	public String toString() {
		
		String decPartStr = ZEvesResponseUtil.concat(decPart, "; ");
		String predPartStr = !form.isEmpty() ? " | " + ZEvesResponseUtil.concat(form, "; ") : "";
		
		return decPartStr + predPartStr;
	}
	
}
