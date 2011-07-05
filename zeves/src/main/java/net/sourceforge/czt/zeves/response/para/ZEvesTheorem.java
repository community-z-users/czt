package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.ZEvesProverCmd;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;

/**
 * theorem
 * <!ELEMENT theorem (name, formals?, %form;, proof?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "theorem")
public class ZEvesTheorem {

	/**
	 * <!ATTLIST theorem %ability;>
	 */
	@XmlAttribute
	private ZEvesAbility ability;
	
	/**
	 * <!ATTLIST theorem %usage;>
	 */
	@XmlAttribute
	private ZEvesUsage usage;
	
	@XmlElement(required = true)
	private ZEvesName name;
	
	/**
	 * <!ELEMENT formals (name+)>
	 */
	@XmlElementWrapper(name = "formals")
	@XmlElement(name = "name")
	private List<ZEvesName> formals = new ArrayList<ZEvesName>();
	
	@XmlAnyElement(lax = true)
	private Object form;
	
	/**
	 * <!ELEMENT proof (provercmd+)>
	 */
	@XmlElementWrapper(name = "proof")
	@XmlElement(name = "provercmd", type = ZEvesProverCmd.class)
	private List<ZEvesProverCmd> proof = new ArrayList<ZEvesProverCmd>();
	
	public List<ZEvesProverCmd> getProof() {
		return Collections.unmodifiableList(proof);
	}
	
	@Override
	public String toString() {
		
		String formalsStr = !formals.isEmpty() ? 
				"[" + ZEvesResponseUtil.concat(formals, ", ") + "]" : "";
		String proofStr = !proof.isEmpty() ? 
				ZEvesResponseUtil.concat(proof, "\n") + "\n" : "";
		
		return ZEvesAbility.getInfo(ability) + ZString.ZEDCHAR + " theorem "
				+ ZEvesUsage.getInfo(usage) + String.valueOf(name) + formalsStr + "\n"
				+ ZString.CONJECTURE + " " + String.valueOf(form) + "\n" + ZString.END 
				+ proofStr;
	}
	
}
