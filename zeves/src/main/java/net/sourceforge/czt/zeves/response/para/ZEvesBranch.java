package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;

/**
 * <!ELEMENT branch (name, (%form;)?)>
 * 
 * @author Andrius Velykis
 */
public class ZEvesBranch {

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
		if (form.size() < 2) {
			return null;
		}
		
		return form.get(1);
	}

	@Override
	public String toString() {
		
		Object form = getForm();
		String formStr = form != null ? 
				ZString.LDATA + String.valueOf(getForm()) + ZString.RDATA : "";
		
		return String.valueOf(getName()) + formStr;
	}
	
}
