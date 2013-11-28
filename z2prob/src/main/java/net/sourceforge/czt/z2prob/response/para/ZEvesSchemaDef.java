
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
 * schema definition (vertical)
 * <!ELEMENT schemadef (schname, formals?, decpart, axpart?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "schemadef")
public class ZEvesSchemaDef
{

  /**
   * <!ATTLIST schemadef %ability;>
   */
  @XmlAttribute
  private ZEvesAbility ability;

  @XmlElement(name = "schname", required = true)
  private ZEvesSchName name;

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

    String axStr = !axPart.getItems().isEmpty() ? 
        ZEvesResponseUtil.concat(axPart.getItems(), ZString.NL) : "";

    return ZEvesAbility.getInfo(ability) 
        + ZString.SCHCHAR 
        + ZEvesAxDef.getGenChar(formals) + String.valueOf(name) + ZEvesAxDef.getGenFormalsInfo(formals) 
        + ZString.NL 
        + ZEvesResponseUtil.concat(decPart, ZString.NL) + ZString.NL 
        + ZString.VL + ZString.NL 
        + axStr + ZString.NL + ZString.ENDCHAR;
  }

}
