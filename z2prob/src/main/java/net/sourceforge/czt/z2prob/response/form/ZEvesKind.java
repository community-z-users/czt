package net.sourceforge.czt.zeves.response.form;

import javax.xml.bind.annotation.XmlEnumValue;

/**
 * <!ATTLIST name kind (expr | pred | schema) #IMPLIED>
 * 
 * @author Andrius Velykis
 */
public enum ZEvesKind {
	@XmlEnumValue("expr")
	EXPR,
	@XmlEnumValue("pred")
	PRED,
	@XmlEnumValue("schema")
	SCHEMA
}