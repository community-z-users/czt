package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.util.ZString;

/**
 * <!ELEMENT if (%form;, %form;, %form;, type?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "if")
public class ZEvesIf {

	/**
	 * <!ATTLIST if %kind; "expr">
	 */
	@XmlAttribute
	private ZEvesKind kind = ZEvesKind.EXPR;

	@XmlAnyElement(lax = true)
	private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@XmlElement
	private ZEvesType type;

	@Override
	public String toString() {

		if (form.size() != 3) {
			throw new IllegalStateException("Invalid ZEvesIf items: " + form);
		}

		String ifStr = String.valueOf(form.get(0));
		String thenStr = String.valueOf(form.get(1));
		String elseStr = String.valueOf(form.get(2));

		return ZString.IF + " " + ifStr + " " 
				+ ZString.THEN + " " + predToExpr(thenStr) + " "
				+ ZString.ELSE + " " + predToExpr(elseStr);
	}
	
	// wrap into an empty schema to convert predicate to expression
	// note the necessary space before predicate, otherwise parsing fails in some cases
	// e.g. LSQUARE + VL + NOT + rest of var pred.. + RSQUARE
	private String predToExpr(String pred) {
		return ZString.LSQUARE + ZString.VL + ZString.SPACE + pred + ZString.RSQUARE;
	}

}
