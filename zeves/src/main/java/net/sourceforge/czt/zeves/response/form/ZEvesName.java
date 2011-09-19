
package net.sourceforge.czt.zeves.response.form;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlEnumValue;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.XmlAnyElementList;
import net.sourceforge.czt.zeves.response.ZEvesResponseUtil;

/**
 * The name element represents a variable or constant name.
 * <!ELEMENT name (genactuals?, type?)>
 * @author Andrius Velykis
 */
@XmlRootElement(name = "name")
public class ZEvesName
{

  /**
   * A list of prefix functions, which are specified here because Z/Eves does not report PREFUN class 
   */
  private static final List<String> PREFUNS = Collections.unmodifiableList(Arrays.asList(
      "#"));
  
  /**
   * <!ATTLIST name scope (local | global) #IMPLIED>
   * 
   * @author Andrius Velykis
   */
  public enum NameScope {
    @XmlEnumValue("local")
    LOCAL, 
    @XmlEnumValue("global")
    GLOBAL
  }


  /**
   * <!ATTLIST name style (roman | underlined | italic | bold | sans)
   * #IMPLIED>
   * 
   * @author Andrius Velykis
   */
  public enum NameStyle {
    @XmlEnumValue("roman")
    ROMAN, 
    @XmlEnumValue("underlined")
    UNDERLINED, 
    @XmlEnumValue("italic")
    ITALIC, 
    @XmlEnumValue("bold")
    BOLD, 
    @XmlEnumValue("sans")
    SANS
  }


  /**
   * <!ATTLIST name class (infun | ingen | inrel | pregen | prerel | postfun |
   * 						 word | opname | relimg | other) #IMPLIED>
   * 
   * @author Andrius Velykis
   */
  public enum NameClass {
    @XmlEnumValue("infun")
    INFUN, 
    @XmlEnumValue("ingen")
    INGEN,
    @XmlEnumValue("inrel")
    INREL,
    @XmlEnumValue("pregen")
    PREGEN,
    @XmlEnumValue("prerel")
    PREREL,
    @XmlEnumValue("postfun")
    POSTFUN,
    @XmlEnumValue("word")
    WORD,
    @XmlEnumValue("opname")
    OPNAME,
    @XmlEnumValue("relimg")
    RELIMG,
    @XmlEnumValue("other")
    OTHER
  }

  /**
   * The value of the ident attribute is intended to include underbars and
   * decorations. <!ATTLIST name ident CDATA #REQUIRED>
   */
  @XmlAttribute(required = true)
  private String ident;

  /**
   * The scope attribute is for scope specified by the user, not scope as
   * determined by Z/EVES.
   */
  @XmlAttribute
  private NameScope scope;

  /**
   * The style attribute can be used to underline a relation name, or set a
   * name like pre or dom in roman font. (We might want to add more styles -
   * perhaps it should be mixed or CDATA?)
   */
  @XmlAttribute
  private NameStyle style;

  @XmlAttribute(name = "class")
  private NameClass cclass;

  @XmlAttribute
  private ZEvesKind kind;

  /**
   * <!ELEMENT genactuals (%form;)+>
   */
  @XmlElement(name = "genactuals")
  private XmlAnyElementList genActuals = new XmlAnyElementList();

  @XmlElement
  private ZEvesType type;

  public String getIdent()
  {

    if (ident != null) {
      if (ident.endsWith("'")) {
        // Z/Eves outputs a simple ' instead of Prime, and it is not separated as a decorator,
        // so instead just check and replace
        ident = ident.substring(0, ident.length() - 1) + ZString.PRIME;
      } else if (ident.equals("\\")) {
        // Z/Eves outputs a simple backslash instead of setminus, so check and replace
        ident = ZString.SETMINUS;
      }
    }

    return ident;
  }

  @Override
  public String toString()
  {
    String genActs = getGenActInfo(genActuals.getItems());
    String ident = getIdent();
    if (genActs.isEmpty()) {
      return getIdent();
    }
    
    // for genactuals, there are several cases, where Z/Eves uses them
    // differently than CZT, so we need to take into account the operators with genacts
    String genIdent;
    if (PREFUNS.contains(ident) || cclass == NameClass.PREREL) {
      // add varargs to the end
      genIdent = "(" + ident + ZString.ARG_TOK + ")";
    } else if (cclass == NameClass.POSTFUN) {
      // add varargs to the front
      genIdent = "(" + ZString.ARG_TOK + ident + ")";
    } else if (cclass == NameClass.INFUN || cclass == NameClass.INREL) {
      // add varargs to both sides
      genIdent = "(" + ZString.ARG_TOK + ident + ZString.ARG_TOK + ")";
    } else {
      // unsupported yet - just use ident
      genIdent = ident;
    }
    
    return genIdent + genActs;
  }

  public static String getGenActInfo(List<?> genActuals)
  {
    if (genActuals.isEmpty()) {
      return "";
    }

    return "[" + ZEvesResponseUtil.concat(genActuals, ", ") + "]";
  }

}
