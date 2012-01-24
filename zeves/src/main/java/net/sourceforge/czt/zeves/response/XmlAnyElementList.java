package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

/**
 * A special list to act for XmlAnyElement wrappers, because currently one
 * cannot have the following annotations: @XmlElementWrapper @XmlAnyElement -
 * they fail to unmarshall.
 * 
 * The bug is fixed in new JAXB versions, but they are not part of the official
 * Java distro yet: http://java.net/jira/browse/JAXB-669
 * 
 * @author Andrius Velykis
 */
public class XmlAnyElementList {

	@XmlAnyElement(lax = true)
	private List<?> items = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

	public List<?> getItems() {
		return items;
	}

}
