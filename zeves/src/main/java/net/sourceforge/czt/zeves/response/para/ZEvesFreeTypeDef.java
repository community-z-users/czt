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
 * free type definition
 * <!ELEMENT freetypedef (name, branch+)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "freetypedef")
public class ZEvesFreeTypeDef {

	/**
	 * <!ATTLIST freetypedef %ability;>
	 */
	@XmlAttribute
	private ZEvesAbility ability;
	
	@XmlElement(required = true)
	private ZEvesName name;
	
	@XmlElement(name = "branch")
	private List<ZEvesBranch> branches = new ArrayList<ZEvesBranch>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	@Override
	public String toString() {
		
		return ZEvesAbility.getInfo(ability) + ZString.ZEDCHAR + String.valueOf(name) + " ::= "
				+ ZEvesResponseUtil.concat(branches, " | ") + "\n" + ZString.END;
	}
	
}
