package net.sourceforge.czt.zeves.response;

import java.io.StringReader;

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
import net.sourceforge.czt.zeves.response.form.ZEvesString;
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
 * The reader parses Z/Eves response XML and produces appropriate Z/Eves Java
 * objects with the data. It uses JAXB unmarshalling to perform the XML parsing.
 * 
 * This class is not thread safe.
 * 
 * @author Andrius Velykis
 */
public class ZEvesResponseReader {

	private final Unmarshaller unmarshaller;
	private final XMLReader xmlReader;

	private ZEvesResponseReader(Unmarshaller unmarshaller, XMLReader xmlReader) {
		super();
		this.unmarshaller = unmarshaller;
		this.xmlReader = xmlReader;
	}

	private static JAXBContext configZEvesApiContext() throws JAXBException {

		return JAXBContext.newInstance(
				ZEvesOutput.class, ZEvesError.class,

				/*
				 * <!ENTITY % form "(binder | let | if | schematext | op | relchain |
				 * 					 application | parenform | display | schematype | 
				 * 					 name | schname | number | string)">
				 */
				ZEvesBinder.class, ZEvesLet.class, ZEvesIf.class, ZEvesSchemaText.class, 
				ZEvesOp.class, ZEvesRelChain.class, ZEvesApplication.class, ZEvesParenForm.class,
				ZEvesDisplay.class, ZEvesSchemaType.class, ZEvesName.class, ZEvesSchName.class,
				ZEvesNumber.class, ZEvesString.class,
				/*
				 * <!ENTITY % para "(schemadef | axdef | theorem | givendef |
				 * 					 horschdef | abbrevdef | freetypedef | %form; | 
				 * 					 labeledform | syndef)">
				 */
				ZEvesSchemaDef.class, ZEvesAxDef.class, ZEvesTheorem.class, ZEvesGivenDef.class,
				ZEvesHorSchDef.class, ZEvesAbbrevDef.class, ZEvesFreeTypeDef.class,
				ZEvesLabeledForm.class, ZEvesSynDef.class);
	}

	public static ZEvesResponseReader createReader() throws JAXBException,
			ParserConfigurationException, SAXException {

		// setup object mapper using the Z/Eves API context classes
		JAXBContext context = configZEvesApiContext();
		XMLReader xmlReader = configXmlReader();

		// create the unmarshaller from XML to Z/Eves API POJOs
		Unmarshaller unmarshaller = context.createUnmarshaller();

		return new ZEvesResponseReader(unmarshaller, xmlReader);
	}

	private static XMLReader configXmlReader() throws ParserConfigurationException, SAXException {

		SAXParserFactory parserFactory = SAXParserFactory.newInstance();
		// do not validate, otherwise we need to include whole of DTD, 
		// not just the entities
		parserFactory.setValidating(false);

		SAXParser parser = parserFactory.newSAXParser();
		XMLReader reader = parser.getXMLReader();

		reader.setErrorHandler(new DefaultHandler2());

		return reader;
	}

	public Object readXml(String xml) throws JAXBException {

		xml = fixXmlResponse(xml);

		// use the XML string as the input source to JAXB unmarshaller
		InputSource inputSource = new InputSource(new StringReader(appendXmlHeader(xml)));

		// wrap the plain XML text into SAX source to perform 
		// parsing and entity resolving
		SAXSource xmlSource = new SAXSource(xmlReader, inputSource);

		return unmarshaller.unmarshal(xmlSource);
	}

	private String appendXmlHeader(String xml) {
		return ZEvesXmlEntities.XML_HEADER + xml;
	}

	/**
	 * The Z/Eves response XML is not well-formatted. This method adapts the XML
	 * to fix that.
	 * 
	 * One of the problems is theorem references to Z/Eves mathematical toolkit,
	 * e.g. "&dom$declaration". This is invalid, because in XML, everything that
	 * starts with "&" is an XML entity, and must finish with a semicolon.
	 * However, it is not the case for these theorem references.
	 * 
	 * @param xmlStr
	 * @return
	 */
	private String fixXmlResponse(String xmlStr) {
		// TODO improve this somehow?
		return xmlStr.replace("&dom$declaration", "dom$declaration")
				.replace("&cup$declaration", "cup$declaration")
				.replace("&map$declaration", "map$declaration")
				.replace("&notin$declaration", "notin$declaration")
				.replace("&neq$declaration", "neq$declaration");
	}

}
