/**
Copyright (C) 2003, 2004 Petra Malik
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/



/*
Requirements with respect to the XML schema:
- xs:element either global, used with ref attribute, or have a build
  in or simple type.
- xs:sequence always without arguments (no minOccurs or maxOccurs)
- no xs:restriction
- namespace prefixes are unique
*/
package net.sourceforge.czt.gnast.schema;

import java.io.*;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.util.*;
import java.util.logging.Logger;
import java.util.regex.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.*;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.traversal.NodeIterator;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

import net.sourceforge.czt.gnast.*;
import net.sourceforge.czt.gnast.gen.*;

/**
 * A Schema project.
 * Parses an XML Schema file and collects all classes
 * to be generated.
 *
 * @author Petra Malik
 */
public class SchemaProject
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  private static final Logger LOGGER =
    Logger.getLogger("net.sourceforge.czt.gnast.schema.SchemaProject");

  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String CLASS_NAME = "SchemaProject";

  /**
   * Access to the XPath API (should never be <code>null</code>).
   */
  private XPath xPath_;

  /**
   * <p>A mapping from XML schema types to java types.
   * It is also possible to map any string occuring
   * as a type to a class name.</p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Properties bindings_ = new Properties();

  private Document document_;

  /**
   * A mapping from class names to SchemaClass objects.
   * This map does only contain classes from this project.
   */
  private Map map_ = new HashMap();

  /**
   * A mapping from enumeration names
   * to a list of all values of that enumeration.
   * This map does only contain enumerations from this project.
   */
  private Map enum_ = new HashMap();

  /**
   * The project imported from the XML Schema.
   */
  private String importProject_;

  private GlobalProperties global_;

  /**
   * A mapping from namespace prefixes
   * to its associated namespaces.
   *
   * Should never be <code>null</code>.
   */
  private Properties nsPrefixProps_;

  /**
   * A mapping from objects that does not belong to the project
   * to be generated to its corresponding project names.
   */
  private final Properties objectProjectProps_ = new Properties();

  /**
   * The target namespace of the schema.
   */
  private String targetNamespace_;

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * @param schemaFilename the XML Schema file name.
   * @param mapping the mapping information.
   */
  public SchemaProject(String schemaFilename,
                       Properties mapping,
                       GlobalProperties globalProperties)
    throws ParserConfigurationException,
           SAXException, IOException, XSDException
  {
    nsPrefixProps_ = collectNamespacePrefixes(schemaFilename);
    global_ = globalProperties;
    if (mapping != null) bindings_ = mapping;
    InputSource in = new InputSource(new FileInputStream(schemaFilename));
    DocumentBuilderFactory dfactory = DocumentBuilderFactory.newInstance();
    dfactory.setNamespaceAware(true);
    document_ = dfactory.newDocumentBuilder().parse(in);
    xPath_ = new XPath(document_);
    Node schemaNode = xPath_.selectSingleNode(document_, "/xs:schema");
    if (schemaNode != null) {
      targetNamespace_ = xPath_.getNodeValue(schemaNode, "@targetNamespace");
      String importNamespace =
        xPath_.getNodeValue(schemaNode, "xs:import/@namespace");
      if (importNamespace != null) {
        importProject_ = global_.getProjectName(importNamespace);
      }

      Node n;

      // collecting all enumerations
      NodeIterator nl = xPath_.selectNodeIterator(schemaNode,
                    "xs:simpleType[xs:restriction/@base = 'xs:string']");
      while ((n = nl.nextNode()) != null) {
        String enumName = xPath_.getNodeValue(n, "@name");
        List enumValues = new ArrayList();
        if (enumName == null) xPath_.getNodeValue(n.getParentNode(), "@name");
        // TODO error message if enumName == null
        NodeIterator valueIter =
          xPath_.selectNodeIterator(n, ".//xs:enumeration");
        Node valueNode;
        while ((valueNode = valueIter.nextNode()) != null) {
          enumValues.add(xPath_.getNodeValue(valueNode, "@value"));
        }
        enum_.put(enumName, enumValues);
      }

      // collecting all Ast classes
      nl = xPath_.selectNodeIterator(schemaNode, "xs:element | xs:group");
      while ((n = nl.nextNode()) != null) {
        SchemaClass c = new SchemaClass(n);
        map_.put(c.getName(), c);
      }
    }
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ************* ACCESSING SPECIAL SCHEMA NODES ***************

  /**
   * Returns an xs:complexType node that has an attribute name
   * whos value is equal to <code>name</code>.
   *
   * @param name the name of the complex type to be returned.
   * @return an xs:complexType node that has an attribute name
   *         whos value is equal to <code>name</code>;
   *         <code>null</code> if such a node could not be found.
   */
  public Node getComplexTypeNode(String name)
  {
    String xPathExpr = "//xs:schema/xs:complexType[@name='" + name + "']";
    return xPath_.selectSingleNode(xPathExpr);
  }

  public String getPropertyBinding(Node node)
  {
    String xPathExpr = "./xs:annotation/xs:appinfo/jaxb:property/@name";
    return xPath_.getNodeValue(node, xPathExpr);
  }

  private String getGnastPackageXPathExpr()
  {
    return "//xs:schema/xs:annotation/xs:appinfo/"
      + "gnast:schemaBindings/gnast:package";
  }

  public String getJaxbGenPackage()
  {
    return xPath_.getNodeValue("//jaxb:package/@name");
  }

  public String getName()
  {
    return xPath_.getNodeValue("//gnast:schemaBindings/@name");
  }

  private String getPackageOffset(String packageName)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "/gnast:package[@id='"
                               + packageName
                               + "']/@name");
  }

  public String getPackageDocumentation(String packageName)
  {
    String result =
      xPath_.getNodeValue(getGnastPackageXPathExpr()
                          + "/gnast:package[@id='"
                          + packageName
                          + "']/gnast:javadoc/text()");
    if (result != null) result = result.trim();
    return result;
  }

  public String getBasePackage()
  {
    return xPath_.getNodeValue(
          getGnastPackageXPathExpr() + "/@name");
  }

  public String getAstPackageOffset()
  {
    return getPackageOffset("ast");
  }

  public String getAstPackage()
  {
    return getBasePackage() + "." + getAstPackageOffset();
  }

  public String getImplPackageOffset()
  {
    return getPackageOffset("impl");
  }

  public String getImplPackage()
  {
    return getBasePackage() + "." + getImplPackageOffset();
  }

  public String getVisitorPackageOffset()
  {
    return getPackageOffset("visitor");
  }

  public String getVisitorPackage()
  {
    return getBasePackage() + "." + getVisitorPackageOffset();
  }

  public String getJaxbPackageOffset()
  {
    return getPackageOffset("jaxb");
  }

  public String getJaxbPackage()
  {
    return getBasePackage() + "." + getJaxbPackageOffset();
  }

  public String getDomPackageOffset()
  {
    return getPackageOffset("dom");
  }

  public String getDomPackage()
  {
    return getBasePackage() + "." + getDomPackageOffset();
  }

  public JObject getGenObject(String id)
  {
    String xPathExpr = "//*[@id='" + id + "']";
    Node node = xPath_.selectSingleNode(xPathExpr);
    if (node == null) {
      LOGGER.warning("Cannot find node with id " + id);
      return null;
    }
    String objectName = xPath_.getNodeValue(node, "@class");
    if (objectName == null) {
      LOGGER.warning("Node with id " + id + " doesn't have a class name");
      return null;
    }
    String packageName = getBasePackage() + "."
      + xPath_.getNodeValue(node, "../@name");
    if (packageName == null) {
      LOGGER.warning("The parent of the node with id " + id
                     + "doesn't have a name");
      return null;
    }
    return new JObjectImpl(objectName, packageName);
  }

  public String getClassName(String id)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='"
                               + id
                               + "']/@class");
  }

  public String getTemplate(String id)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='"
                               + id
                               + "']/@template");
  }

  public String getPackage(String id)
  {
    String xPathExpr = getGnastPackageXPathExpr()
      + "/gnast:package[gnast:generate[@id='" + id + "']]/@name";
    return xPath_.getNodeValue(xPathExpr);
  }

  // *********************** OTHERS ************************

  /**
   * Returns the namespace that corresponds to the given prefix.
   */
  protected String getNamespace(String prefix)
  {
    return nsPrefixProps_.getProperty(prefix);
  }

  /**
   * Returns the name of the project that corresponds to the
   * given namespace.
   */
  protected String getProjectName(String namespace)
  {
    return global_.getProjectName(namespace);
  }

  /**
   * Returns the project that has the given name.
   */
  protected Project getProject(String name)
  {
    return global_.getProject(name);
  }

  /**
   * Returns the GnastClass with the given name.
   *
   * @param className the name of the GnastClass to be retrieved.
   *                  (it may contain the package name).
   * @return the GnastClass with that name, or <code>null</code>
   *         if a GnastClass with that name could not be found.
   * @czt.todo What about Term and TermA?
   * @czt.todo Should it really be possible to support names
   *           containing package info?
   */
  public JAstObject getAstClass(String className)
  {
    String methodName = "getAstClass";
    LOGGER.entering(CLASS_NAME, methodName, className);

    String[] blubb = className.split("\\.");
    String name = blubb[blubb.length - 1];
    JAstObject result = (JAstObject) map_.get(name);
    if (result == null) {
      String projectName = objectProjectProps_.getProperty(name);
      if (projectName != null) {
        Project project = getProject(projectName);
        if (project != null) result = project.getAstObject(name);
      }
    }
    LOGGER.exiting(CLASS_NAME, methodName, result);
    return result;
  }

  /**
   * <p>Returns a mapping from class names to SchemaClass objects.</p>
   */
  public Map getAstClasses()
  {
    return map_;
  }

  /**
   * Returns a Map of all enumerations found in the given
   * XML schema file.
   */
  public Map getEnumerations()
  {
    return enum_;
  }

  /**
   * Return the name of the imported project.
   */
  public String getImportProject()
  {
    return importProject_;
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  private String serialize(Node node)
  {
    if (node == null) return null;
    try {
      TransformerFactory tFactory =
        TransformerFactory.newInstance();
      Transformer transformer =
        tFactory.newTransformer();
      transformer.setOutputProperty("omit-xml-declaration", "yes");
      StringWriter writer = new StringWriter();
      StreamResult result = new StreamResult(writer);
      NodeIterator iter = xPath_.selectNodeIterator(node, "* | text()");
      Node nextNode = iter.nextNode();
      while(nextNode != null) {
        DOMSource source = new DOMSource(nextNode);
        transformer.transform(source, result);
        nextNode = iter.nextNode();
      }
      writer.close();
      return writer.toString();
    }
    catch (Exception e) {
      throw new GnastException(e);
    }
  }

  /**
   * <p>Collects all used namespace prefixes (defined via xmlns)
   * of an XML file into a map. The namespace prefix is used as
   * the key, its associated namespace is the value of the map.</p>
   *
   * <p>If the same prefix is used several times, only the last
   * occurrence is contained in the map.</p>
   *
   * @param filename the name of the (XML) file to be searched.
   * @return a map from string representing a namespace prefix
   *         to string representing its associated namespace.
   */
  public static Properties collectNamespacePrefixes(String filename)
  {
    final String methodName = "collectNamespacePrefixes";
    LOGGER.entering(CLASS_NAME, methodName, filename);

    final Properties result = new Properties();
    Pattern p =
      Pattern.compile("xmlns:[a-zA-Z]+[\\s]*\\=\\s*\\\"[^\\\"]*\\\"");
    CharSequence seq;
    try {
      seq = file2CharSeq(filename);
    }
    catch (IOException e) {
      LOGGER.warning("Cannot read " + filename);
      return null;
    }
    Matcher m = p.matcher(seq);
    while (m.find()) {
      String s = m.group();
      String[] blubb = s.split("\"");
      Pattern p2 = Pattern.compile("xmlns:[a-zA-Z]+[^a-zA-Z]");
      Matcher m2 = p2.matcher(blubb[0]);
      if (m2.find()) {
        String string = m2.group();
        final int l = "xmlns:".length();
        result.setProperty(string.substring(l, string.length() - 1), blubb[1]);
      }
    }
    LOGGER.exiting(CLASS_NAME, methodName, result);
    return result;
  }

  /**
   * <p>Converts the contents of a file into a CharSequence
   * suitable for use by the regex package.</p>
   *
   * @param filename the name of the file to be converted.
   * @return a <code>CharSequence</code> of the contents of
   *         the given file.
   */
  public static CharSequence file2CharSeq(String filename)
    throws IOException
  {
    FileInputStream fis = new FileInputStream(filename);
    FileChannel fc = fis.getChannel();

    // Create a read-only CharBuffer on the file
    ByteBuffer bbuf =
      fc.map(FileChannel.MapMode.READ_ONLY, 0, (int) fc.size());
    CharBuffer cbuf = Charset.forName("8859_1").newDecoder().decode(bbuf);
    return cbuf;
  }

  /**
   * <p>This method asserts that there is at most one colon
   * in the given string.</p>
   *
   * <p>Note: This method updates private member variable
   * <code>objectProjectProps_</code>.
   *
   * @return ...
   *   and <code>null</code> if <code>string</code> is <code>null</code>.
   */
  public String removeNamespace(String string)
  {
    final String methodName = "removeNamespace";
    LOGGER.entering(CLASS_NAME, methodName, string);
    if (string == null) return null;
    try {
      String[] blubb = string.split(":");
      assert blubb.length > 0;
      if (blubb.length == 1) {
        LOGGER.exiting(CLASS_NAME, methodName, string);
        return string;
      }
      else {
        String prefix = blubb[0];
        String obj = blubb[1];
        String namespace = getNamespace(prefix);
        if (!namespace.equals("http://www.w3.org/2001/XMLSchema")) {
          String projectName = getProjectName(namespace);
          if (projectName == null) {
            String message =
              "Cannot find project that corresponds to prefix " + prefix;
            LOGGER.warning(message);
          }
          else if (!targetNamespace_.equals(namespace)) {
            objectProjectProps_.setProperty(obj, projectName);
            objectProjectProps_.setProperty(obj + "Impl", projectName);
          }
        }
        LOGGER.exiting(CLASS_NAME, methodName, obj);
        return obj;
      }
    }
    catch (Exception e) {
      throw new GnastException(e);
    }
  }

  /**
   * Returns the Java Object with that name.
   *
   * @return should never be <code>null</code>.
   */
  public JObject getObject(String type)
  {
    String projectName = objectProjectProps_.getProperty(type);
    if (projectName != null) {
      Project project = getProject(projectName);
      if (project != null) {
        return project.getObject(type);
      }
    }
    return new JObjectImpl(type);
  }

  // ############################################################
  // ##################### INNER CLASSES ########################
  // ############################################################

  class SchemaClass extends JAstObjectImpl
  {
    /**
     * The name of this Schema class.
     */
    private String name_ = null;

    /**
     * Is this class abstract?
     */
    private boolean abstract_ = false;

    /**
     * The base class of this Schema class.
     */
    private String extends_ = null;

    /**
     * Properties for this Schema class.
     */
    private List properties_ = null;

    /**
     *
     */
    private String xsdType_ = null;

    /**
     * Javadoc documentation for this class.
     */
    private String javadoc_ = null;

    /**
     * Creates a new schema class from the node given.
     *
     * @param node  The XML Schema node from which all the neccessary
     *              information is extracted.
     */
    SchemaClass(Node node)
      throws XSDException
    {
      // parsing the name
      name_ = xPath_.getNodeValue(node, "@name");
      if (name_ == null) {
        String message = "The name attribute of a global XML Schema "
          + "element, group, or type is missing: ";
        message += node.toString();
        throw new XSDException(message);
      }

      // parsing whether this class is abstract
      String abstractAttribute = xPath_.getNodeValue(node, "@abstract");
      if (new String("true").equals(xPath_.getNodeValue(node, "@abstract")))
        abstract_ = true;
      else abstract_ = false;

      // parsing the substitution group attribute
      extends_ =
        removeNamespace(xPath_.getNodeValue(node, "@substitutionGroup"));

      properties_ = new ArrayList();
      if (node.getNodeName().equals("xs:group")) {
        properties_ = collectProperties(node);
      }

      // parsing the type
      xsdType_ = xPath_.getNodeValue(node, "@type");
      if (xsdType_ == null) {
        String message = "The type attribute for " + name_
          + " is either missing or invalid.  "
          + "Are you using unnamed types?  "
          + "Unnamed types are currently not supported.";
        throw new XSDException(message);
      }

      // collecting properties
      properties_ = collectAllProperties(removeNamespace(xsdType_));

      if (extends_ == null) {
        extends_ = "Term";
      }

      // parsing javadoc
      String xPathExpr = "xs:annotation/xs:documentation";
      javadoc_ = serialize(xPath_.selectSingleNode(node, xPathExpr));
      if (javadoc_ != null) javadoc_ = javadoc_.trim();
    }

    public String getName()
    {
      return name_;
    }

    public String getJavadoc()
    {
      return javadoc_;
    }

    public JProject getProject()
    {
      return null;
    }

    public boolean getNameEqualsType()
    {
      return xsdType_.endsWith(name_);
    }

    public String getImplName()
    {
      return getName() + "Impl";
    }

    public String getExtends()
    {
      return extends_;
    }

    public String getPackage()
    {
      return getAstPackage();
    }

    public String getImplPackage()
    {
      return SchemaProject.this.getImplPackage();
    }

    /**
     * Returns whether this gnast class is an instance of
     * the gnast class whos name is <code>name</code>.
     *
     * @param  name the name of the gnast class.
     * @return <code>true</code> if this class is an instance of
     *         a class named <code>name</code>;
     *         <code>false</code> otherwise.
     */
    public boolean isInstanceOf(String name)
    {
      boolean result = false;
      String parent = getExtends();
      if (parent != null) {
        if (parent.equals(name)) return true;
        JAstObject c = (JAstObject) map_.get(parent);
        if (c != null) {
          result = c.isInstanceOf(name);
        }
      }
      return result;
    }

    public String getImplExtends()
    {
      String methodName = "getExtendsImpl";
      LOGGER.entering(CLASS_NAME, methodName, name_);
      String result = extends_ + "Impl";
      LOGGER.exiting(CLASS_NAME, methodName, result);
      return result;
    }

    public List getProperties()
    {
      String methodName = "getProperties";
      LOGGER.entering(CLASS_NAME, methodName, name_);
      List erg = new Vector();
      erg.addAll(properties_);
      LOGGER.exiting(CLASS_NAME, methodName, erg);
      return erg;
    }

    public List getInheritedProperties()
    {
      String methodName = "getInheritedProperties";
      LOGGER.entering(CLASS_NAME, methodName, name_);
      List erg = null;
      String ext = getExtends();
      if (ext != null) {
        JAstObject c = getAstClass(ext);
        if (c != null) {
          erg = c.getAllProperties();
        }
        else if (ext.equals("Term") || ext.equals("TermA")) {
          erg = new ArrayList();
        }
      }
      LOGGER.exiting(CLASS_NAME, methodName, erg);
      return erg;
    }

    /**
     * Uses extends_ and name_ (in log messages and exceptions),
     * so make sure these are set prior to calling this method.
     *
     * @throws NullPointerException if <code>node</code> is <code>null</code>.
     */
    private void parseProperties(Node node)
      throws XSDException
    {
      String methodName = "parseProperties";
      LOGGER.entering(CLASS_NAME, methodName, node);

      if (node == null) {
        NullPointerException e = new NullPointerException();
        LOGGER.exiting(CLASS_NAME, methodName, e);
        throw e;
      }

      LOGGER.fine("Properties for " + name_ + " are " + properties_);
      LOGGER.exiting(CLASS_NAME, methodName);
    }

    /**
     * Identifies all properties that are children of that node.
     * For instance, given an xs:complexType node, this method
     * returns a list of all properties associated with this type
     * (not included inherited properties).
     *
     * @czt.todo Should this method be static?
     */
    private List collectProperties(Node node)
      throws XSDException
    {
      final String methodName = "collectProperties";
      LOGGER.entering(CLASS_NAME, methodName, node);

      List list = new ArrayList();
      String xpathexpr = ".//xs:element | .//xs:attribute";
      NodeIterator nl = null;
      try {
        nl = xPath_.selectNodeIterator(node, xpathexpr);
      }
      catch (Exception e) {
        LOGGER.fine("ERROR while getting the properties "
                    + "of a Schema class.");
        e.printStackTrace();
        throw new XSDException();
      }
      Node n;
      while ((n = nl.nextNode()) != null) {
        try {
          SchemaProperty prop = new SchemaProperty(n);
          LOGGER.finer("Found property " + prop);
          list.add(prop);
        }
        catch (XSDException e) {
          XSDException exception =
            new XSDException("Error while processing " + node.toString(), e);
          LOGGER.exiting(CLASS_NAME, methodName, exception);
          throw exception;
        }
      }
      LOGGER.exiting(CLASS_NAME, methodName, list);
      return list;
    }

    public boolean getAbstract()
    {
      return abstract_;
    }

    /**
     * The search is stopped at extends_.
     *
     * @param typeName  the name of the complex type
     *                  where the search is started.
     * @throws NullPointerException if <code>typeName</code>
     *                  is <code>null</code>.
     * @czt.todo The collectAllProperties(typeName) method
     *           should get the namespace information as well
     *           since it is not guaranteed that the given type is
     *           defined within this project rather than in an
     *           imported project.
     * @czt.todo Currently, this method changes the member
     *           variable extends_ (when it finds a type whos
     *           name is TermA).  This is very dangerous and
     *           unintuitive.  Think of a better way to handle
     *           this.
     */
    private List collectAllProperties(String typeName)
      throws XSDException
    {
      String methodName = "collectAllProperties";
      LOGGER.entering(CLASS_NAME, methodName, typeName);

      if (typeName == null) {
        NullPointerException e = new NullPointerException();
        LOGGER.exiting(CLASS_NAME, methodName, e);
        throw e;
      }

      List erg = new Vector();

      if (typeName.equals("TermA")) {
        extends_ = "TermA";
      }
      else if (!typeName.equals(extends_)) {
        Node startNode = getComplexTypeNode(typeName);
        if (startNode == null) {
          LOGGER.warning("Cannot find definition of complex type "
                         + typeName
                         + "; proceeding anyway.");
          LOGGER.exiting(CLASS_NAME, methodName, erg);
          return erg;
        }

        erg.addAll(collectProperties(startNode));
        Node n = xPath_.selectSingleNode(startNode,
              "./xs:complexContent/xs:extension/@base");
        if (n != null && n.getNodeValue() != null) {
          String base = removeNamespace(n.getNodeValue());
          erg.addAll(collectAllProperties(base));
        }
      }
      LOGGER.exiting(CLASS_NAME, methodName, erg);
      return erg;
    }
  } // end SchemaClass




  /**
   * xs:element or xs:attribute.
   */
  class SchemaProperty
    extends JPropertyImpl
  {
    /**
     * The name of this property.
     *
     * @see #parseName(Node)
     */
    private String name_ = null;

    /**
     * The type of this property.
     *
     * @see #parseType(Node)
     */
    private String type_ = null;

    private String listType_ = null;

    private boolean attribute_ = false;

    private boolean isReference_ = false;

    SchemaProperty(Node node)
      throws XSDException
    {
      parseName(node);
      parseType(node);
      if (node.getLocalName().equals("attribute")) {
        attribute_ = true;
      }
    }

    public boolean getAttribute()
    {
      return attribute_;
    }

    /**
     * <p>Parses an xs:element or xs:attribute node
     * and sets the name of this property appropriatly.<p>
     *
     * <p>The rules are as follows:  If there is a jaxb property
     * customization,  take the value of the name attribute.  Otherwise,
     * take the value of the name attribute.  If this is not present
     * either, take the value of the ref attribute.  If non of the
     * above suceeds, throw an XSDException.</p>
     */
    /*@
      @ assignable name_;
      @*/
    private void parseName(Node node)
      throws XSDException
    {
      name_ = getPropertyBinding(node);
      if (name_ == null) name_ = xPath_.getNodeValue(node, "@name");
      if (name_ == null)
        name_ = removeNamespace(xPath_.getNodeValue(node, "@ref"));
      if (name_ == null) {
        String message = "Cannot generate a getter method "
          + "since there is neither a property customization, "
          + "a name attribute, nor a ref attribute "
          + "for the following node: ";
        message += node.toString();
        throw new XSDException(message);
      }
    }

    /**
     * <p>Parses an xs:element or xs:attribute node
     * and sets the type of this property appropriatly.<p>
     *
     * @czt.todo Check the value of attribute maxOccurs.  Currently,
     *           it is only checked whether it is present or not.
     * @czt.todo Check the value of attribute minOccurs as well.
     */
    /*@
      @ assignable isReference_;
      @ assignable listType_;
      @ assignable type_;
      @*/
    public void parseType(Node node)
      throws XSDException
    {
      String result = null;
      if (parseRefAttribute(node) || parseTypeAttribute(node)) {
        String maxOccurs = xPath_.getNodeValue(node, "@maxOccurs");
        if ("unbounded".equals(maxOccurs)) {
          listType_ = type_;
          type_ = "java.util.List";
        }
        return;
      }
      String message = "There is neither a type nor a ref attribute "
        + "for the following node:\n         " + node.toString();
      throw new XSDException(message);
    }

    /**
     * Returns <code>true</code> iff the given node has a ref attribute.
     */
    /*@
      @ assignable type_;
      @ assignable isReference_;
      @*/
    private boolean parseRefAttribute(Node node)
    {
      String ref = xPath_.getNodeValue(node, "@ref");
      boolean refAttributePresent = ref != null;
      if (refAttributePresent) {
        type_ = removeNamespace(ref);
        isReference_ = true;
      }
      return refAttributePresent;
    }

    /**
     * Returns <code>true</code> iff the given node has a type attribute.
     */
    /*@
      @ assignable type_;
      @*/
    private boolean parseTypeAttribute(Node node)
    {
      String typeAttr = removeNamespace(xPath_.getNodeValue(node, "@type"));
      boolean typeAttributePresent = typeAttr != null;
      if (typeAttributePresent) {
        type_ = (String) bindings_.get(typeAttr);
        if (type_ == null) {
          type_ = typeAttr;
        }
      }
      return typeAttributePresent;
    }

    public String getName()
    {
      return name_;
    }

    public JObject getType()
    {
      return getObject(type_);
    }

    public JObject getListType()
    {
      if (listType_ != null) {
        return getObject(listType_);
      }
      return getObject("java.lang.Object");
    }

    public boolean isReference()
    {
      return isReference_;
    }
  } // end class SchemaAttribute
} // end class SchemaProject
