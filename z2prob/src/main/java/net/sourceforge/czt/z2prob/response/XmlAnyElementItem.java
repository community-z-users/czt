package net.sourceforge.czt.zeves.response;

import javax.xml.bind.annotation.XmlAnyElement;

/**
 * Similar to {@link XmlAnyElementList}, but for a single item, because we
 * cannot have a wrapper on a single item.
 * 
 * @author Andrius Velykis
 */
public class XmlAnyElementItem {

	@XmlAnyElement(lax = true)
	private Object item;

	public Object getItem() {
		return item;
	}

}
