package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;

/**
 * Given set declaration
 * <!ELEMENT givendef (name)+>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "givendef")
public class ZEvesGivenDef {

	/**
	 * <!ATTLIST givendef %ability;>
	 */
	@XmlAttribute
	private ZEvesAbility ability;
	
	@XmlElement(name = "name")
	private List<ZEvesName> names = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@Override
	public String toString() {
		
		return ZEvesAbility.getInfo(ability) + ZString.ZEDCHAR 
				+ "[" + ZEvesResponseUtil.concat(names, ", ") + "]\n" + ZString.END;
	}
	
}
