package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;


/**
 * <!ELEMENT relchain (%form;, (name, %form;)+)>
 * @author Andrius Velykis
 */
@XmlRootElement(name = "relchain")
public class ZEvesRelChain {

	private static final List<String> IFF_NAMES = Arrays.asList("true", "false");

	@XmlAnyElement(lax = true)
	private List<?> items = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
	
	@Override
	public String toString() {

		List<?> itms = checkIff(items);

		List<String> itemStrs = new ArrayList<String>(itms.size());
		for (Object item : itms) {
			// wrap complex elements into parentheses to avoid parsing issues
			itemStrs.add(ZEvesResponseUtil.withParentheses(item));
		}
		
		return ZEvesResponseUtil.concat(itemStrs, " ");
	}

	private static List<?> checkIff(List<?> original) {
		List<Object> items = new ArrayList<Object>(original);
		
		if (items.size() > 2) {
			if (isZEvesName(items.get(1), "=")) {
				// check for true/false on either side - then use IFF rather than EQUALS
				boolean needsIff = false;
				for (Object item : items) {
					if (item instanceof ZEvesName) {
						if (IFF_NAMES.contains(((ZEvesName) item).getIdent())) {
							needsIff = true;
							break;
						}
					}
				}

				if (needsIff) {
					items.set(1, ZString.IFF);
				}
			}
		}
		
		return items;
	}

	private static boolean isZEvesName(Object elem, String name) {
		if (elem instanceof ZEvesName) {
			ZEvesName nameElem = (ZEvesName) elem;
			if (name.equals(nameElem.getIdent())) {
				return true;
			}
		}

		return false;
	}
	
}
