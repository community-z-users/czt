package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.form.ZEvesBlurb;

/**
 * <!ELEMENT zoutput (%para; | zsectionbegin | zsectionend | zsectionproofbegin
 * 							 | zsectionproofend | provercmd | blurb)*>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "zoutput")
public class ZEvesOutput {

	@XmlElement(name = "provercmd", type = ZEvesProverCmd.class)
	private Object command;

	@XmlElements({
			// TODO proper classes - not used in Z/Eves at the moment?
			@XmlElement(name = "zsectionbegin"), @XmlElement(name = "zsectionend"),
			@XmlElement(name = "zsectionproofbegin"), @XmlElement(name = "zsectionproofend") })
	private Object sectionTag;

	@XmlElement(name = "blurb")
	private ZEvesBlurb info;

	@XmlAnyElement(lax = true)
	private List<?> para = new ArrayList<Object>();

	public List<?> getResults() {
		return Collections.unmodifiableList(para);
	}

	public Object getFirstResult() {
		if (para.isEmpty()) {
			return null;
		}

		return para.get(0);
	}

	public boolean isEmpty() {
		return command == null && sectionTag == null && info == null && para.isEmpty();
	}

	@Override
	public String toString() {

		String cmdStr = command != null ? "Command sent: " + String.valueOf(command) + "\n" : "";
		String infoStr = info != null ? String.valueOf(info) + "\n" : "";
		String sectionStr = sectionTag != null ? String.valueOf(sectionTag) + "\n" : "";

		return cmdStr + infoStr + sectionStr + ZEvesResponseUtil.concat(para, "\n");

	}

}
