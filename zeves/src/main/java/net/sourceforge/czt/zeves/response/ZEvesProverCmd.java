package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;

import net.sourceforge.czt.zeves.response.form.ZEvesLetDef;
import net.sourceforge.czt.zeves.response.form.ZEvesTheoremRef;

/**
 * <!ELEMENT provercmd ((%form; | letdef | theoremref)*, provercmd?)>
 * 
 * The provercmd form allows for the different kinds of commands to be
 * represented.
 * 
 * @author Andrius Velykis
 */
public class ZEvesProverCmd {

	/**
	 * <!ATTLIST provercmd name CDATA #REQUIRED>
	 */
	@XmlAttribute
	private String name;

	@XmlElement(name = "provercmd")
	private ZEvesProverCmd command;

	@XmlElement(name = "letdef")
	private ZEvesLetDef letDef;

	@XmlElement(name = "theoremref")
	private ZEvesTheoremRef theoremRef;

	@XmlAnyElement(lax = true)
	private List<?> form = new ArrayList<Object>();

	@Override
	public String toString() {

		String letDefStr = letDef != null ? String.valueOf(letDef) + "; " : "";
		String formStr = !form.isEmpty() ? ZEvesResponseUtil.concat(form, "; ") + "; " : "";
		String theoremRefStr = theoremRef != null ? String.valueOf(theoremRef) : "";
		String commandRefStr = command != null ? "; " + String.valueOf(command) : "";

		String suffix = letDefStr + formStr + theoremRefStr + commandRefStr;
		if (!suffix.isEmpty()) {
			suffix = ": " + suffix;
		}

		return name + suffix;
	}

}
