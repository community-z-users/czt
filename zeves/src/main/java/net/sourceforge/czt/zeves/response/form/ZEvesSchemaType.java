package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * <!ELEMENT schematype (decl*)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "schematype")
public class ZEvesSchemaType {

	@XmlElement(name = "decl")
	private List<ZEvesDecl> decls = new ArrayList<ZEvesDecl>();

	@Override
	public String toString() {
		return "SchemaType[" + ZEvesResponseUtil.concat(decls, "; ") + "]";
	}
	
}