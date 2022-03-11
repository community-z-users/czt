
package net.sourceforge.czt.zeves.response.para;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlElements;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.zeves.response.XmlAnyElementList;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesDecl;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesSchName;

/**
 * axiomatic and generic definition
 * <!ELEMENT axdef (formals?, decpart, axpart?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "axdef")
public class ZEvesAxDef
{

  /**
   * <!ATTLIST axdef %ability;>
   */
  @XmlAttribute
  private ZEvesAbility ability;

  /**
   * <!ELEMENT formals (name+)>
   */
  @XmlElementWrapper(name = "formals")
  @XmlElement(name = "name")
  private List<ZEvesName> formals = new ArrayList<ZEvesName>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  /**
   * <!ELEMENT decpart (decl | schname)+>
   */
  @XmlElementWrapper(name = "decpart", required = true)
  @XmlElements({
    @XmlElement(name = "decl", type = ZEvesDecl.class),
    @XmlElement(name = "schname", type = ZEvesSchName.class)})
  private List<?> decPart = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  /**
   * <!ELEMENT axpart (labeledform | %form;)+>
   */
  @XmlElement(name = "axpart")
  private XmlAnyElementList axPart = new XmlAnyElementList();

  @Override
  public String toString()
  {

    String axStr = !axPart.getItems().isEmpty()
        ? ZString.VL + ZString.NL + ZEvesResponseUtil.concat(axPart.getItems(), ZString.NL) + ZString.NL 
        : "";

    return ZEvesAbility.getInfo(ability) + ZString.AX + getGenChar(formals) + getGenFormalsInfo(formals) + ZString.NL
        + ZEvesResponseUtil.concat(decPart, ZString.NL) + ZString.NL + axStr
        + ZString.ENDCHAR;
  }

  public static String getGenChar(List<ZEvesName> formals) {
    
    if (formals.isEmpty()) {
      return "";
    }
    
    return ZString.GENCHAR;
  }
  
  public static String getGenFormalsInfo(List<ZEvesName> formals) {
    
    if (formals.isEmpty()) {
      return "";
    }
    
    return ZString.LSQUARE + ZEvesResponseUtil.concat(formals, ", ") + ZString.RSQUARE;
  }

}
