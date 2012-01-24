package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlEnumValue;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.util.ZEvesString;

/**
 * <!ELEMENT display ((%form;)*, type?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "display")
public class ZEvesDisplay {

	/**
	 * <!ATTLIST display type (set | sequence | bag | tuple ) #REQUIRED>
	 * 
	 * @author Andrius Velykis
	 */
	public enum DisplayType {
		@XmlEnumValue("set")
		SET, 
		@XmlEnumValue("sequence")
		SEQUENCE, 
		@XmlEnumValue("bag")
		BAG, 
		@XmlEnumValue("tuple")
		TUPLE
	}

	@XmlAttribute(required = true)
	private DisplayType type;

	@XmlAnyElement(lax = true)
	private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@XmlElement(name = "type")
	private ZEvesType elType;

	@Override
	public String toString() {

		String content = ZEvesResponseUtil.concat(form, ", ");

		switch (type) {
		case BAG:
			return ZEvesString.LBAG + content + ZEvesString.RBAG; // TODO get proper brackets for bags
		case SEQUENCE:
			return ZString.LANGLE + content + ZString.RANGLE;
		case SET:
			return "{" + content + "}";
		case TUPLE:
			return "(" + content + ")";
		}

		return "Unknown display: " + content;
	}

}
