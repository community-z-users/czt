
package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlEnumValue;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName;

/**
 * abbreviation definition (var-name, prefix generic, infix generic)
 * <!ELEMENT abbrevdef (name, formals?, %form;)>  
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "abbrevdef")
public class ZEvesAbbrevDef
{

  /**
   * <!ATTLIST abbrevdef type (var | pregen | ingen) "var">
   * 
   * @author Andrius Velykis
   */
  public enum AbbrevType {
    @XmlEnumValue("var")
    VAR, 
    @XmlEnumValue("pregen")
    PREGEN, 
    @XmlEnumValue("ingen")
    INGEN;

    public static String getInfo(AbbrevType type)
    {
      if (type == null) {
        return "";
      }

      return "[" + type.toString().toLowerCase() + "] ";
    }
  }

  /**
   * <!ATTLIST abbrevdef %ability;>
   */
  @XmlAttribute
  private ZEvesAbility ability;

  /**
   * <!ATTLIST abbrevdef type (var | pregen | ingen) "var">
   */
  @XmlAttribute
  private AbbrevType type = AbbrevType.VAR;

//  // name interferes with form here, use #getName()
//  @XmlElement(required = true)
//  private ZEvesName name;

  /**
   * <!ELEMENT formals (name+)>
   */
  @XmlElementWrapper(name = "formals")
  @XmlElement(name = "name")
  private List<ZEvesName> formals = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @XmlAnyElement(lax = true)
  private List<?> form = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  // note that differently from DTD, sometimes the name can be 
  // a ZEvesParenForm (e.g. for operator defs)
  public Object getName()
  {
    // always take the first in form
    return (Object) form.get(0);
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
    String infoStr = ZEvesAbility.getInfo(ability) + AbbrevType.getInfo(type);
    if (!infoStr.isEmpty()) {
      infoStr = infoStr + ZString.NL;
    }

    return infoStr
        + ZString.ZED + ZString.NL 
        + String.valueOf(getName()) + ZEvesAxDef.getGenFormalsInfo(formals) 
        + ZString.SPACE + ZString.DEFEQUAL + ZString.SPACE 
        + String.valueOf(getForm()) + ZString.NL + ZString.END;
  }

}
