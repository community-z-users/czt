package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;


/**
 * <!ELEMENT relchain (%form;, (name, %form;)+)>
 * @author Andrius Velykis
 */
@XmlRootElement(name = "relchain")
public class ZEvesRelChain {

	@XmlAnyElement(lax = true)
	private List<?> items = new ArrayList<Object>();
	
	@Override
	public String toString() {
		return ZEvesResponseUtil.concat(items, " ");
	}
	
}
