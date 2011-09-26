
package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlEnumValue;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
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

  @XmlElement(required = true)
  private ZEvesName name;

  /**
   * <!ELEMENT formals (name+)>
   */
  @XmlElementWrapper(name = "formals")
  @XmlElement(name = "name")
  private List<ZEvesName> formals = new ArrayList<ZEvesName>();

  @XmlAnyElement(lax = true)
  private Object form;

  @Override
  public String toString()
  {

    String formalsStr = !formals.isEmpty()
        ? "[" + ZEvesResponseUtil.concat(formals, ", ") + "]"
        : "";

    return ZEvesAbility.getInfo(ability) + "abbreviation " + AbbrevType.getInfo(type)
        + String.valueOf(name) + formalsStr + "\n" + String.valueOf(form) + "\n";
  }

}
