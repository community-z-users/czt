package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlEnumValue;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.XmlAnyElementItem;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;

/**
 * In a number of places, the kind of the expression is indicated with an
 * attribute rather than with a tag (e.g., binders). This represents a grouping
 * of forms that are prettyprinted in more-or-less the same way, with just a few
 * differences in glyphs.
 * 
 * <!ELEMENT binder (decpart, predpart?, (%form;)?, type?)>
 * 
 * @author Andrius Velykis
 * 
 */
@XmlRootElement(name = "binder")
public class ZEvesBinder {

	/**
	 * <!ATTLIST binder type (forall | forsome | forone | lambda | mu | set)
	 * #REQUIRED>
	 * 
	 * @author Andrius Velykis
	 */
	public enum BinderType {
		@XmlEnumValue("forall")
		FORALL, @XmlEnumValue("forsome")
		FORSOME, @XmlEnumValue("forone")
		FORONE, @XmlEnumValue("lambda")
		LAMBDA, @XmlEnumValue("mu")
		MU, @XmlEnumValue("set")
		SET
	}

	@XmlAttribute(required = true)
	private BinderType type;

	/**
	 * <!ATTLIST binder %kind; "pred">
	 */
	@XmlAttribute
	private ZEvesKind kind = ZEvesKind.PRED;

	/**
	 * <!ELEMENT decpart (decl | schname)+>
	 */
	@XmlElementWrapper(name = "decpart", required = true)
	@XmlElements({ @XmlElement(name = "decl", type = ZEvesDecl.class),
			@XmlElement(name = "schname", type = ZEvesSchName.class) })
	private List<?> decPart = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	/**
	 * <!ELEMENT predpart (%form;)>
	 */
	@XmlElement(name = "predpart")
	private XmlAnyElementItem predPart = new XmlAnyElementItem();

	@XmlAnyElement(lax = true)
	private Object form;

	@XmlElement(name = "type")
	private ZEvesType elType;

	@Override
	public String toString() {

		String decPartStr = ZEvesResponseUtil.concat(decPart, "; ");
		String predPartStr = predPart.getItem() != null ? 
				" | " + String.valueOf(predPart.getItem()) : "";

		String formStr = form != null ? " " + ZString.SPOT + " " + String.valueOf(form) : "";

		String out = getTypeStr() + " " + decPartStr + predPartStr + formStr;

		if (type == BinderType.SET) {
			out = out + " }";
		}

		return out;
	}

	private String getTypeStr() {
		switch (type) {
		case FORALL:
			return ZString.ALL;
		case FORONE:
			return ZString.EXIONE;
		case FORSOME:
			return ZString.EXI;
		case LAMBDA:
			return ZString.LAMBDA;
		case MU:
			return ZString.MU;
		case SET:
			return "{ ";
		}

		return String.valueOf(type);
	}

}
