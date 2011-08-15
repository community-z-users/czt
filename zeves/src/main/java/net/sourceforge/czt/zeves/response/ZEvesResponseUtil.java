package net.sourceforge.czt.zeves.response;

import java.util.Collection;

public class ZEvesResponseUtil {

	public static String concat(Collection<?> list, String delimiter) {

		StringBuilder sb = new StringBuilder();

		String delim = "";
		for (Object i : list) {
			sb.append(delim).append(String.valueOf(i));
			delim = delimiter;
		}

		return sb.toString();
	}

  private ZEvesResponseUtil()
  {
  }

}
