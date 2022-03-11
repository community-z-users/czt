package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

/**
 * <!ELEMENT replace (name, %form;)>
 * 
 * @author Andrius Velykis
 */
public class ZEvesReplace {

//	// name interferes with form here, use #getName()
//	@XmlElement(required = true)
//	private ZEvesName name;
	
	@XmlAnyElement(lax = true)
	private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	public ZEvesName getName() {
		// always take the first in form
		return (ZEvesName) form.get(0);
	}

	public Object getForm() {
		// since form interferes with name, it gets caught into the first
		// element here
		return form.get(1);
	}

	@Override
	public String toString() {
		return String.valueOf(getName()) + " := " + String.valueOf(getForm());
	}
	
}
