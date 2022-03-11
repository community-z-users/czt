package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.XmlAnyElementList;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * The schname element represents a schema name. The value of the ident
 * attribute includes decorations applied to the schema name, and the decoration
 * attribute is for decorations applied to the names of the schema components.
 * Z/EVES does not currently make this distinction.
 * 
 * <!ELEMENT schname (genactuals?, renaming?, type?)>
 * 
 * @author Andrius Velykis
 * 
 */
@XmlRootElement(name = "schname")
public class ZEvesSchName {

	/**
	 * <!ATTLIST schname prefix CDATA #IMPLIED>
	 */
	@XmlAttribute
	private String prefix;
	
	/**
	 * <!ATTLIST schname ident CDATA #REQUIRED>
	 */
	@XmlAttribute(required = true)
	private String ident;
	
	/**
	 * <!ATTLIST schname decoration CDATA #IMPLIED>
	 */
	@XmlAttribute
	private String decoration;
	
	/**
	 * <!ATTLIST schname %kind; "schema">
	 */
	@XmlAttribute
	private ZEvesKind kind = ZEvesKind.SCHEMA;

	/**
	 * <!ELEMENT genactuals (%form;)+>
	 */
	@XmlElement(name = "genactuals")
	private XmlAnyElementList genActuals = new XmlAnyElementList();
	
	/**
	 * <!ELEMENT renaming (rename | replace)+>
	 */
	@XmlElementWrapper
	@XmlElements({ @XmlElement(name = "rename", type = ZEvesRename.class),
				   @XmlElement(name = "replace", type = ZEvesReplace.class) })
	private List<?> renaming = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
	
	@XmlElement
	private ZEvesType type;

	@Override
	public String toString() {
		
		String prefixStr = prefix != null ? prefix + " " : "";
		String decStr = decoration != null ? decoration : "";
		String renamingStr = !renaming.isEmpty() ? 
				"[" + ZEvesResponseUtil.concat(renaming, ", ") + "]" : "";

		return prefixStr + ident + decStr + renamingStr
				+ ZEvesName.getGenActInfo(genActuals.getItems());
	}
	
}
