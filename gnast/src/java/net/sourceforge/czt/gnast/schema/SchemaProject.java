/**
Copyright 2003 Petra Malik
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

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

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
public class SchemaProject implements GnastProject
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

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

  public Node getGlobalElementNode(String name)
  {
    return xPath_.selectSingleNode(
          "//xs:schema/xs:element[@name='" + name + "']");
  }

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

  private String getPackageOffset(String packageName)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "/gnast:package[@id='"
                               + packageName
                               + "']/@name");
  }

  public String getPackageDocumentation(String packageName)
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "/gnast:package[@id='"
                               + packageName
                               + "']/gnast:javadoc/text()");
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
    Logger logger = getLogger();
    String xPathExpr = "//*[@id='" + id + "']";
    Node node = xPath_.selectSingleNode(xPathExpr);
    if (node == null) {
      logger.warning("Cannot find node with id " + id);
      return null;
    }
    String objectName = xPath_.getNodeValue(node, "@class");
    if (objectName == null) {
      logger.warning("Node with id " + id + " doesn't have a class name");
      return null;
    }
    String packageName = getBasePackage() + "."
      + xPath_.getNodeValue(node, "../@name");
    if (packageName == null) {
      logger.warning("The parent of the node with id " + id
                     + "doesn't have a name");
      return null;
    }
    return new JObjectImpl(objectName, packageName);
  }

  public String getFactoryClassName()
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='factory']/@class");
  }

  public String getFactoryTemplate()
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='factory']/@template");
  }

  public String getFactoryPackage()
  {
    String xPathExpr = getGnastPackageXPathExpr()
      + "/gnast:package[gnast:generate[@id='factory']]/@name";
    return xPath_.getNodeValue(xPathExpr);
  }

  public String getFactoryImplClassName()
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='factoryImpl']/@class");
  }

  public String getFactoryImplTemplate()
  {
    return xPath_.getNodeValue(getGnastPackageXPathExpr()
                               + "//gnast:generate[@id='factoryImpl']/@template");
  }

  public String getFactoryImplPackage()
  {
    String xPathExpr = getGnastPackageXPathExpr()
      + "/gnast:package[gnast:generate[@id='factoryImpl']]/@name";
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
    getLogger().entering(CLASS_NAME, methodName, className);

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
    getLogger().exiting(CLASS_NAME, methodName, result);
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

  /**
   * The logger used when logging information is provided.
   */
  private static Logger getLogger()
  {
    return Logger.getLogger("net.sourceforge.czt.gnast.schema.SchemaProject");
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
    getLogger().entering(CLASS_NAME, methodName, filename);

    final Properties result = new Properties();
    Pattern p =
      Pattern.compile("xmlns:[a-zA-Z]+[\\s]*\\=\\s*\\\"[^\\\"]*\\\"");
    CharSequence seq;
    try {
      seq = file2CharSeq(filename);
    }
    catch (IOException e) {
      getLogger().warning("Cannot read " + filename);
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
        result.setProperty(string.substring(6, string.length() - 1), blubb[1]);
      }
    }
    getLogger().exiting(CLASS_NAME, methodName, result);
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
    getLogger().entering(CLASS_NAME, methodName, string);
    if (string == null) return null;
    try {
      String[] blubb = string.split(":");
      assert blubb.length > 0;
      if (blubb.length == 1) {
        getLogger().exiting(CLASS_NAME, methodName, string);
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
            getLogger().warning(message);
          }
          else if (!targetNamespace_.equals(namespace)) {
            objectProjectProps_.setProperty(obj, projectName);
            objectProjectProps_.setProperty(obj + "Impl", projectName);
          }
        }
        getLogger().exiting(CLASS_NAME, methodName, obj);
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
    }

    public String getName()
    {
      return name_;
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
      getLogger().entering(CLASS_NAME, methodName, name_);
      String result = extends_ + "Impl";
      getLogger().exiting(CLASS_NAME, methodName, result);
      return result;
    }

    public List getProperties()
    {
      String methodName = "getProperties";
      getLogger().entering(CLASS_NAME, methodName, name_);
      List erg = new Vector();
      erg.addAll(properties_);
      getLogger().exiting(CLASS_NAME, methodName, erg);
      return erg;
    }

    public List getInheritedProperties()
    {
      String methodName = "getInheritedProperties";
      getLogger().entering(CLASS_NAME, methodName, name_);
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
      getLogger().exiting(CLASS_NAME, methodName, erg);
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
      getLogger().entering(CLASS_NAME, methodName, node);

      if (node == null) {
        NullPointerException e = new NullPointerException();
        getLogger().exiting(CLASS_NAME, methodName, e);
        throw e;
      }

      getLogger().fine("Properties for " + name_ + " are " + properties_);
      getLogger().exiting(CLASS_NAME, methodName);
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
      getLogger().entering(CLASS_NAME, methodName, node);

      List list = new ArrayList();
      String xpathexpr = ".//xs:choice | "
        + ".//xs:element[not(parent::xs:choice)] | "
        + ".//xs:attribute";
      NodeIterator nl = null;
      try {
        nl = xPath_.selectNodeIterator(node, xpathexpr);
      }
      catch (Exception e) {
        getLogger().fine("ERROR while getting the properties "
                         + "of a Schema class.");
        e.printStackTrace();
        throw new XSDException();
      }
      while ((node = nl.nextNode()) != null) {
        try {
          SchemaProperty prop = new SchemaProperty(node);
          getLogger().finer("Found property " + prop);
          list.add(prop);
        }
        catch (XSDException e) {
          XSDException exception =
            new XSDException("Error while processing " + node.toString(), e);
          getLogger().exiting(CLASS_NAME, methodName, exception);
          throw exception;
        }
      }
      getLogger().exiting(CLASS_NAME, methodName, list);
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
      getLogger().entering(CLASS_NAME, methodName, typeName);

      if (typeName == null) {
        NullPointerException e = new NullPointerException();
        getLogger().exiting(CLASS_NAME, methodName, e);
        throw e;
      }

      List erg = new Vector();

      if (typeName.equals("TermA")) {
        extends_ = "TermA";
      }
      else if (!typeName.equals(extends_)) {
        Node startNode = getComplexTypeNode(typeName);
        if (startNode == null) {
          getLogger().warning("Cannot find definition of complex type "
                          + typeName
                          + "; proceeding anyway.");
          getLogger().exiting(CLASS_NAME, methodName, erg);
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
      getLogger().exiting(CLASS_NAME, methodName, erg);
      return erg;
    }
  } // end SchemaClass




  /**
   * xs:element or xs:choice or xs:attribute.
   */
  class SchemaProperty extends JPropertyImpl
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
      parseIsReference(node);
      if (node.getLocalName().equals("attribute")) {
        attribute_ = true;
      }
    }

    public boolean getAttribute()
    {
      return attribute_;
    }

    /**
     * <p>Parses an xs:element, xs:choice, or xs:attribute node
     * and sets the name of this property appropriatly.<p>
     *
     * <p>The rules are as follows:  If there is a jaxb property customization,
     * take the value of the name attribute. ... </p>
     */
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
     *
     * @czt.todo Check the values of attributes minOccurs and maxOccurs.
     *           So far, it is only checked whether these attributes are
     *           present or not.
     * @czt.todo Don't use the xs namespace prefix explicitly.
     */
    public void parseType(Node node)
      throws XSDException
    {
      String result = null;
      if (xPath_.getNodeValue(node, "@maxOccurs") != null) {
        result = "java.util.List";
        listType_ = removeNamespace(xPath_.getNodeValue(node, "@ref"));
        if (listType_ == null) {
          listType_ = removeNamespace(xPath_.getNodeValue(node, "@type"));
        }
      }
      else if ("xs:choice".equals(node.getNodeName())) {
        result = "TermA";
      }
      else {
        result = removeNamespace(xPath_.getNodeValue(node, "@ref"));
      }
      if (result == null) {
        String typeAttr = removeNamespace(xPath_.getNodeValue(node, "@type"));
        if (typeAttr == null) {
          String message = "There is neither a type nor a ref attribute "
            + "for the following node:\n         ";
          message += node.toString();
          throw new XSDException(message);
        }
        result = (String) bindings_.get(typeAttr);
        if (result == null) {
          result = typeAttr;
          if (enum_.get(typeAttr) == null
              && getGlobalElementNode(typeAttr) == null)
          {
            String message = "Cannot find binding for "
              + xPath_.getNodeValue(node, "@type")
              + "; assume it is an existing class.";
            getLogger().warning(message);
          }
        }
      }
      type_ = result;
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

    public void parseIsReference(Node node)
    {
      if (xPath_.getNodeValue(node, "@ref") != null) isReference_ = true;
      else isReference_ = false;
    }

    public boolean isReference()
    {
      return isReference_;
    }
  } // end class SchemaAttribute
} // end class SchemaProject
