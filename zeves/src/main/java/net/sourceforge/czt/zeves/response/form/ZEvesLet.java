package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;

/**
 * <!ELEMENT let (letdef+, %form;, type?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "let")
public class ZEvesLet {

	/**
	 * <!ATTLIST let %kind; "expr">
	 */
	@XmlAttribute
	private ZEvesKind kind = ZEvesKind.EXPR;

	@XmlElement(name = "letdef")
	private List<ZEvesLetDef> letDefs = new ArrayList<ZEvesLetDef>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@XmlAnyElement(lax = true)
	private Object form;

	@XmlElement
	private ZEvesType type;

	@Override
	public String toString() {
		return "let " + ZEvesResponseUtil.concat(letDefs, "; ") + " " + ZString.SPOT + " "
				+ String.valueOf(form);
	}

}
