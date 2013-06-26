/*
 * CircusParseResources.java
 *
 * Created on 22 March 2006, 14:11
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.ohcircus;

import java.util.ListResourceBundle;

public class OhCircusParseResources extends ListResourceBundle {
	private static final Object[][] contents_ = computeContents();

	private static Object[][] computeContents() {
		Object[][] result = new Object[OhCircusParseMessage.values().length][2];
		int i = 0;
		for (OhCircusParseMessage msg : OhCircusParseMessage.values()) {
			result[i][0] = msg.toString();
			result[i][1] = msg.getFullMessage();
			i++;
		}
		return result;
	}

	public Object[][] getContents() {
		return contents_;
	}
}
