package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlElementWrapper;
import javax.xml.bind.annotation.XmlElements;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.XmlAnyElementList;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * theoremref represents a theorem reference, and is used only in a prover command (use).
 * 
 * <!ELEMENT theoremref (genactuals?, renaming?)>
 * 
 * @author Andrius Velykis
 * 
 */
public class ZEvesTheoremRef
{

  /**
   * <!ATTLIST theoremref ident CDATA #REQUIRED>
   */
  @XmlAttribute(required = true)
  private String ident;

  /**
   * <!ATTLIST theoremref decoration CDATA #IMPLIED>
   */
  @XmlAttribute
  private String decoration;

  /**
   * <!ELEMENT genactuals (%form;)+>
   */
  @XmlElement(name = "genactuals")
  private XmlAnyElementList genActuals = new XmlAnyElementList();

  /**
   * <!ELEMENT renaming (rename | replace)+>
   */
  @XmlElementWrapper
  @XmlElements({ @XmlElement(name = "rename", type = ZEvesRename.class),
                 @XmlElement(name = "replace", type = ZEvesReplace.class)})
  private List<?> renaming = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @Override
  public String toString()
  {
    String decStr = decoration != null ? decoration : "";
    String renamingStr = !renaming.isEmpty() ? ZString.LSQUARE
        + ZEvesResponseUtil.concat(renaming, ZString.COMMA + ZString.SPACE) 
        + ZString.RSQUARE : "";

    return ident + decStr + ZEvesName.getGenActInfo(genActuals.getItems()) + renamingStr;
  }

}
