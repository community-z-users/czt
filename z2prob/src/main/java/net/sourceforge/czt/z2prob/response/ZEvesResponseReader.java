
package net.sourceforge.czt.zeves.response;

import java.io.StringReader;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import javax.xml.transform.sax.SAXSource;

import net.sourceforge.czt.zeves.response.form.ZEvesApplication;
import net.sourceforge.czt.zeves.response.form.ZEvesBinder;
import net.sourceforge.czt.zeves.response.form.ZEvesDisplay;
import net.sourceforge.czt.zeves.response.form.ZEvesIf;
import net.sourceforge.czt.zeves.response.form.ZEvesLet;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.response.form.ZEvesNumber;
import net.sourceforge.czt.zeves.response.form.ZEvesOp;
import net.sourceforge.czt.zeves.response.form.ZEvesParenForm;
import net.sourceforge.czt.zeves.response.form.ZEvesRelChain;
import net.sourceforge.czt.zeves.response.form.ZEvesSchName;
import net.sourceforge.czt.zeves.response.form.ZEvesSchemaText;
import net.sourceforge.czt.zeves.response.form.ZEvesSchemaType;
import net.sourceforge.czt.zeves.response.form.ZEvesResponseString;
import net.sourceforge.czt.zeves.response.para.ZEvesAbbrevDef;
import net.sourceforge.czt.zeves.response.para.ZEvesAxDef;
import net.sourceforge.czt.zeves.response.para.ZEvesFreeTypeDef;
import net.sourceforge.czt.zeves.response.para.ZEvesGivenDef;
import net.sourceforge.czt.zeves.response.para.ZEvesHorSchDef;
import net.sourceforge.czt.zeves.response.para.ZEvesLabeledForm;
import net.sourceforge.czt.zeves.response.para.ZEvesSchemaDef;
import net.sourceforge.czt.zeves.response.para.ZEvesSynDef;
import net.sourceforge.czt.zeves.response.para.ZEvesTheorem;

import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.XMLReader;
import org.xml.sax.ext.DefaultHandler2;

/**
 * The reader parses Z/EVES response XML and produces appropriate Z/EVES Java
 * objects with the data. It uses JAXB unmarshalling to perform the XML parsing.
 * 
 * This class is not thread safe.
 * 
 * @author Andrius Velykis
 */
public class ZEvesResponseReader
{

  private final static Pattern OP_DECL_XML_PATTERN = Pattern.compile("\\&[a-z]+\\$declaration");

  /** 
   * A pattern to match entities without a semicolon, which get output by Z/EVES sometimes, e.g.
   * in a message "the next token, "&lvparen (left rel image bracket), is not ")"." We need
   * to capture this and fix by adding a semicolon. 
   */
  private final static Pattern ENTITY_NO_SEMI_PATTERN = 
      Pattern.compile("\\&[A-Za-z][A-Za-z0-9]*\\s");
  
  /**
   * The pattern finds XML numerical character references and stores the 
   * contents as $1 backreference.
   */
  private final static String UNICODE_XML_PATTERN_SEARCH = "\\&#(x?[A-Fa-f0-9]+);";
  
  /**
   * The pattern restores XML numerical character reference with the contents of
   * $1 backreference. 
   */
  private final static String UNICODE_XML_PATTERN_REPLACE = "\\&#$1;";
  
  /**
   * Using axiom_ as a prefix, because axiom is a reserved word in CZT so user should not be able
   * to define a name starting with axiom_. This improves prevention against accidental clashing.
   * 
   * Also using the suffix _unicode, to know the end of the character reference.
   */
  private final static String ZEVES_XML_PATTERN_SEARCH = "axiom_(x?[A-Fa-f0-9]+)_unicode";
  private final static String ZEVES_XML_PATTERN_REPLACE = "axiom_$1_unicode";

  private final Unmarshaller unmarshaller;

  private final XMLReader xmlReader;

  private ZEvesResponseReader(Unmarshaller unmarshaller, XMLReader xmlReader)
  {
    super();
    this.unmarshaller = unmarshaller;
    this.xmlReader = xmlReader;
  }

  private static JAXBContext configZEvesApiContext() throws JAXBException
  {

    return JAXBContext.newInstance(ZEvesOutput.class, ZEvesError.class,

    /*
     * <!ENTITY % form "(binder | let | if | schematext | op | relchain |
     *                   application | parenform | display | schematype | 
     *                   name | schname | number | string)">
     */
    ZEvesBinder.class, ZEvesLet.class, ZEvesIf.class, ZEvesSchemaText.class, ZEvesOp.class,
    ZEvesRelChain.class, ZEvesApplication.class, ZEvesParenForm.class, ZEvesDisplay.class,
    ZEvesSchemaType.class, ZEvesName.class, ZEvesSchName.class, ZEvesNumber.class,
    ZEvesResponseString.class,
    /*
     * <!ENTITY % para "(schemadef | axdef | theorem | givendef |
     *                   horschdef | abbrevdef | freetypedef | %form; | 
     *                   labeledform | syndef)">
     */
    ZEvesSchemaDef.class, ZEvesAxDef.class, ZEvesTheorem.class, ZEvesGivenDef.class,
    ZEvesHorSchDef.class, ZEvesAbbrevDef.class, ZEvesFreeTypeDef.class, ZEvesLabeledForm.class,
    ZEvesSynDef.class);
  }

  public static ZEvesResponseReader createReader() throws JAXBException,
      ParserConfigurationException, SAXException
  {

    // setup object mapper using the Z/EVES API context classes
    JAXBContext context = configZEvesApiContext();
    XMLReader xmlReader = configXmlReader();

    // create the unmarshaller from XML to Z/EVES API POJOs
    Unmarshaller unmarshaller = context.createUnmarshaller();

    return new ZEvesResponseReader(unmarshaller, xmlReader);
  }

  private static XMLReader configXmlReader() throws ParserConfigurationException, SAXException
  {

    SAXParserFactory parserFactory = SAXParserFactory.newInstance();
    // do not validate, otherwise we need to include whole of DTD, not just the entities
    parserFactory.setValidating(false);

    SAXParser parser = parserFactory.newSAXParser();
    XMLReader reader = parser.getXMLReader();

    reader.setErrorHandler(new DefaultHandler2());

    return reader;
  }

  public Object readXml(String xml) throws JAXBException
  {

    xml = fixXmlResponse(xml);

    // use the XML string as the input source to JAXB unmarshaller
    InputSource inputSource = new InputSource(new StringReader(appendXmlHeader(xml)));

    // wrap the plain XML text into SAX source to perform 
    // parsing and entity resolving
    SAXSource xmlSource = new SAXSource(xmlReader, inputSource);

    return unmarshaller.unmarshal(xmlSource);
  }

  private String appendXmlHeader(String xml)
  {
    return ZEvesXmlEntities.XML_HEADER + xml;
  }

  /**
   * The Z/EVES response XML is not well-formatted. This method adapts the XML
   * to fix that.
   * 
   * One of the problems is theorem references to Z/EVES mathematical toolkit,
   * e.g. "&dom$declaration". This is invalid, because in XML, everything that
   * starts with "&" is an XML entity, and must finish with a semicolon.
   * However, it is not the case for these theorem references.
   * 
   * @param xmlStr
   * @return
   */
  private String fixXmlResponse(String xmlStr)
  {
    
    // unescape custom unicode characters
    xmlStr = unescapeUnicode(xmlStr);

    StringBuilder xml = new StringBuilder(xmlStr);
    Matcher opDeclMatcher = OP_DECL_XML_PATTERN.matcher(xml);
    while (opDeclMatcher.find()) {
      int startIndex = opDeclMatcher.start();
      // remove the first ampersand, then reference will be ok
      xml.deleteCharAt(startIndex);
      opDeclMatcher.reset(xml);
    }

    Matcher noSemiMatcher = ENTITY_NO_SEMI_PATTERN.matcher(xml);
    while (noSemiMatcher.find()) {
      int endIndex = noSemiMatcher.end();
      // add a semicolon in the last-to position
      xml.insert(endIndex - 1, ";");
      noSemiMatcher.reset(xml);
    }

    xmlStr = xml.toString();

    // Replaced by RegEx matching above
    // return xmlStr.replace("&dom$declaration", "dom$declaration")
    //              .replace("&cup$declaration", "cup$declaration")
    //              .replace("&map$declaration", "map$declaration")
    //              .replace("&notin$declaration", "notin$declaration")
    //              .replace("&neq$declaration", "neq$declaration")
    //              .replace("&upto$declaration", "neq$declaration")
    //              .replace("&cardinality$declaration", "neq$declaration")
    //              .replace("&setminus$declaration", "neq$declaration")

    /*
     * Need to replace Arithmos and Finset ZEves XML symbols with
     * their unicode representation, because they get represented as
     * a UTF-16 surrogate pair and the parser somehow misses them
     * them. See ZEvesXmlEntities class for more explanation.
     */
    return xmlStr.replace("&Aopf;", "&#x1d538;")
                 .replace("&Fopf;", "&#x1d53d;");
  }
  
  public static String escapeUnicode(String text) {

    return escapeXmlNumericalZEves(unicodeToXml(text));
  }
  
  private static String unescapeUnicode(String text) {
    return unescapeXmlNumericalZEves(text);
  }
  
  private static String escapeXmlNumericalZEves(String text) {
    return text.replaceAll(UNICODE_XML_PATTERN_SEARCH, ZEVES_XML_PATTERN_REPLACE);
  }
  
  private static String unescapeXmlNumericalZEves(String text) {
    return text.replaceAll(ZEVES_XML_PATTERN_SEARCH, UNICODE_XML_PATTERN_REPLACE);
  }

  /*
   * Adapted from org.apache.commons.lang3.text.translate.CharSequenceTranslator
   */
  private static String unicodeToXml(CharSequence input)
  {

    StringBuilder out = new StringBuilder();

    int pos = 0;
    int len = input.length();
    while (pos < len) {

      int codepoint = Character.codePointAt(input, pos);
      boolean consumed = translate(codepoint, out);

      if (!consumed) {
        char[] c = Character.toChars(Character.codePointAt(input, pos));
        out.append(c);
        pos += c.length;
      }
      else {
        pos += Character.charCount(Character.codePointAt(input, pos));
      }
    }

    return out.toString();
  }

  private static boolean translate(int codepoint, StringBuilder out)
  {
    if (codepoint < 0x7f) {
      // ASCII - do not translate
      return false;
    }

    out.append("&#x");
    out.append(Integer.toHexString(codepoint));
    out.append(';');
    return true;
  }

}
