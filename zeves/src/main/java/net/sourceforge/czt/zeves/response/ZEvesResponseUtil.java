
package net.sourceforge.czt.zeves.response;

import java.util.Collection;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesParenForm;

public class ZEvesResponseUtil
{

  public static String concat(Collection<?> list, String delimiter)
  {

    StringBuilder sb = new StringBuilder();

    String delim = "";
    for (Object i : list) {
      sb.append(delim).append(String.valueOf(i));
      delim = delimiter;
    }

    return sb.toString();
  }
  
  public static String withParentheses(Object elem)
  {
    String val = String.valueOf(elem);

    if (elem instanceof ZEvesName || elem instanceof ZEvesParenForm) {
      // simple element - no parentheses
      return val;
    }

    // a complex element - add parentheses
    return ZString.LPAREN + val + ZString.RPAREN;
  }

  private ZEvesResponseUtil()
  {
  }

}
