
package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesSchName;

/**
 * schema definition (horizontal)
 * <!ELEMENT horschdef (schname, formals?, %form;)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "horschdef")
public class ZEvesHorSchDef
{

  /**
   * <!ATTLIST horschdef %ability;>
   */
  @XmlAttribute
  private ZEvesAbility ability;

  // schname interferes with form here, use #getName()
//  @XmlElement(name = "schname", required = true)
//  private ZEvesSchName name;

  /**
   * <!ELEMENT formals (name+)>
   */
  @XmlElementWrapper(name = "formals")
  @XmlElement(name = "name")
  private List<ZEvesName> formals = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @XmlAnyElement(lax = true)
  private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  public ZEvesSchName getName()
  {
    // always take the first in form
    return (ZEvesSchName) form.get(0);
  }

  public Object getForm()
  {
    // since form interferes with name, it gets caught into the first
    // element here
    return form.get(1);
  }

  @Override
  public String toString()
  {

    return ZEvesAbility.getInfo(ability) 
        + ZString.ZEDCHAR + String.valueOf(getName()) + ZEvesAxDef.getGenFormalsInfo(formals)
        + ZString.SPACE + ZString.DEFEQUAL + ZString.SPACE 
        + String.valueOf(getForm()) + ZString.NL + ZString.END;
  }

}
