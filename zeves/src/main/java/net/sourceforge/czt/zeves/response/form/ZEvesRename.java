package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;

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
		return String.valueOf(names.get(0)) + "/" + String.valueOf(names.get(1));
	}
	
}
