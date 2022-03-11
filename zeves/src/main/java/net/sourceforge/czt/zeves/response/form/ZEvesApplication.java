
package net.sourceforge.czt.zeves.response.form;

import net.sourceforge.czt.base.util.PerformanceSettings;
import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.z.util.ZString;

import static net.sourceforge.czt.zeves.response.ZEvesResponseUtil.withParentheses;

/**
 * <!ELEMENT application (%form;, %form;, type?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "application")
public class ZEvesApplication
{

  @XmlAnyElement(lax = true)
  private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @XmlElement
  private ZEvesType type;

  @Override
  public String toString()
  {

    if (form.size() != 2) {
      throw new IllegalStateException("Invalid ZEvesApplication items: " + form);
    }

    return withParentheses(form.get(0)) + " " + fixArgument(form.get(1));
  }
  
  private String fixArgument(Object element) {
    
    String val = withParentheses(element);
    
    if ("#".equals(val)) {
      /*
       * Need to handle a special case of "#" operator.
       * 
       * It is not considered as such by Z/EVES, so when it appears in argument 
       * of function application, we need to add arguments to the name.
       */
      return ZString.LPAREN + val + ZString.ARG_TOK + ZString.RPAREN;
    }
    
    return val;
  }
  
}
