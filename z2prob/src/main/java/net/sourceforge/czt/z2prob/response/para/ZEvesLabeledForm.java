
package net.sourceforge.czt.zeves.response.para;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.util.ZEvesString;

/**
 * <!ELEMENT labeledform (%form;)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "labeledform")
public class ZEvesLabeledForm
{

  /**
   * <!ATTLIST labeledform %ability;>
   */
  @XmlAttribute
  private ZEvesAbility ability;

  /**
   * <!ATTLIST labeledform %usage;>
   */
  @XmlAttribute
  private ZEvesUsage usage;

  /**
   * <!ATTLIST labeledform ident CDATA #REQUIRED>
   */
  @XmlAttribute(required = true)
  private String ident;

  @XmlAnyElement(lax = true)
  private Object form;

  @Override
  public String toString()
  {
    String abilityStr = ability != null ? ability.toString().toLowerCase() + ZString.SPACE : "";
    
    return ZEvesString.LLABEL 
        + abilityStr + ZEvesUsage.getInfo(usage) + ident
        + ZEvesString.RLABEL + ZString.SPACE 
        + String.valueOf(form);
  }

}
