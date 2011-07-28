package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;

import net.sourceforge.czt.z.util.ZString;

/**
 * <!ELEMENT rename (name, name)>
 * 
 * @author Andrius Velykis
 */
public class ZEvesRename {

	@XmlElement(name = "name")
	private List<ZEvesName> names = new ArrayList<ZEvesName>();

	@Override
	public String toString() {
		return String.valueOf(names.get(0)) 
				+ ZString.SPACE + ZString.SLASH + ZString.SPACE
				+ String.valueOf(names.get(1));
	}
	
}
