
package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * <!ELEMENT schematype (decl*)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "schematype")
public class ZEvesSchemaType
{

  @XmlElement(name = "decl")
  private List<ZEvesDecl> decls = new ArrayList<ZEvesDecl>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @Override
  public String toString()
  {
    return ZString.LBIND + ZString.SPACE 
        + ZEvesResponseUtil.concat(decls, "; ") 
        + ZString.SPACE + ZString.RBIND;
  }

}
