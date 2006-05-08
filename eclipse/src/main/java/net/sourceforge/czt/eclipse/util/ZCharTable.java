/*
 * Created on 2005-10-13
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package net.sourceforge.czt.eclipse.util;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import net.sourceforge.czt.eclipse.CZTPlugin;

import org.eclipse.core.runtime.Platform;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/**
 * @author Chengdong Xu
 */
public class ZCharTable {
	private final String ZTABLEFILE = "lib/ZTable2.xml";
	
    /**
     * An array of objects where the first column contains strings
     * (the heading for the corresponding row) and all other columns
     * contain ZChar objects.
     */
	private Object[][] mTableArray = createZCharTable();
	
	public ZCharTable() {
	}
	
	/*
    private static final Object[][] mTableArray = {
    	{ "Paragraphs",
	    	new ZChar("Sect",
	    		"\u2500 section NAME parents standard_toolkit \u2029\n",
				"\\begin{zsection}\n  \\SECTION NAME \\parents standard\\_toolkit\n\\end{zsection}\n",
			  	"Section Header"),
			new ZChar("Op",
				"\u2500\n  function 42 leftassoc ( _ OPERATOR _ )\n\u2029\n",
				"\\begin{zed}\n  \\function 42 \\leftassoc ( \\varg OPERATOR \\varg )\n\\end{zed}\n",
			  	"Operator Template"),
			new ZChar("[G]",
				"\u2500 [ TYPE ] \u2029\n",
				"\\begin{zed}\n  [ TYPE ]\n\\end{zed}\n",
			  	"Given Sets"),
			new ZChar("Ax",
				"\u2577\n  DECLS\n|\n  PREDS\n\u2029\n",
				"\\begin{axdef}\n  DECLS\n\\where\n  PREDS\n\\end{axdef}\n",
			  	"Axiomatic Definition"),
			new ZChar("Ax[]",
				"\u2577\u2550[ TYPE ]\n  DECLS\n|\n  PREDS\n\u2029\n",
				"\\begin{gendef}[ TYPE ]\n  DECLS\n\\where\n  PREDS\n\\end{gendef}\n",
			  	"Generic Axiomatic Definition"),
			new ZChar("::=",
				"\u2500\n  TYPE ::= NAME | NAME \u27EA TYPE \u27EB\n\u2029\n",
				"\\begin{zed}\n  TYPE ::= NAME | NAME \\ldata TYPE \\rdata\n\\end{zed}\n",
			  	"Freetype Definition"),
			new ZChar("==",
				"\u2500\n  NAME == EXPR\n\u2029\n",
				"\\begin{zed}\n  NAME == EXPR\n\\end{zed}\n",
			  	"Horizontal Definition"),
			new ZChar("Sch",
				"\u250C NAME\n  DECLS\n|\n  PREDS\n\u2029\n",
				"\\begin{schema}{NAME}\n  DECLS\n\\where\n  PREDS\n\\end{schema}\n",
			  	"Schema Definition"),
			new ZChar("Sch[]",
				"\u250C\u2550 NAME [ TYPE ]\n  DECLS\n|\n  PREDS\n\u2029\n",
				"\\begin{schema}{NAME}[ TYPE ]\n  DECLS\n\\where\n  PREDS\n\\end{schema}\n",
			  	"Generic Schema Definition"),
			new ZChar("\u22A2?",
				"\u2500\n  \u22A2? PRED\n\u2029\n",
				"\\begin{zed}\n  \\vdash? PRED\n\\end{zed}\n",
			  	"Conjecture")
    	},
		{ "Predicates",
    		new ZChar("\u2200", "\\forall", "Universal Quantification"),
			new ZChar("\u2203", "\\exists", "Existential Quantification"),
			new ZChar("\u2227", "\\land", "Conjunction"),
			new ZChar("\u2228", "\\lor", "Disjunction"),
			new ZChar("\u00AC", "\\lnot", "Negation"),
			new ZChar("\u21D2", "\\implies", "Implication"),
			new ZChar("\u21D4", "\\iff", "Equivalence"),
			new ZChar("\u2260", "\\neq", "Not Equal"),
			new ZChar("\u2208", "\\in", "Membership"),
			new ZChar("\u2209", "\\notin", "Not Member"),
			new ZChar("\u2286", "\\subseteq", "Subset Of Or Equal To"),    
			new ZChar("\u2282", "\\subset", "Subset Of")
		},
		{ "Sets",
			new ZChar("\u2119", "\\power", "Power Set"),
			//	new ZChar("\uD835\uDD3D", "\\finset", "Finite Power Set"),  // U+1D53D
			new ZChar("{", "\\{", "Begin Set"),
			new ZChar("|", "|", "Such That"),
			new ZChar("\u2981", "@", "Returning"),
			new ZChar("}", "\\}", "End Set"),
			new ZChar("\u2205", "\\emptyset", "Empty Set"),
			new ZChar("\u222A", "\\cup", "Union"),
			new ZChar("\u22C3", "\\bigcup", "n-ary Union"),
			new ZChar("\u2229", "\\cap", "Intersection"),
			new ZChar("\u22C2", "\\bigcap", "n-ary Intersection"),
			new ZChar("\u2216", "\\setminus", "Set Subtraction"),
			new ZChar("\u2296", "\\symdiff", "Symmetric Difference")
		},
		{ "Relations",
			new ZChar("\u2194", "\\rel", "Relation"),
			new ZChar("\u21A6", "\\mapsto", "Mapsto"),
			new ZChar("\u00D7", "\\cross", "Cartesian Product"),
			new ZChar("\u25C1", "\\dres", "Domain Restriction"),
			new ZChar("\u2A64", "\\ndres", "Domain Subtraction"),
			new ZChar("\u25B7", "\\rres", "Range Restriction"),
			new ZChar("\u2A65", "\\nrres", "Range Substraction"),
			new ZChar("\u2295", "\\oplus", "Relational Overriding"),
			new ZChar("\u2A3E", "\\comp", "Relational Composition"),
			new ZChar("\u223C", "\\inv", "Relational Inverse"),
			new ZChar("\u2987  \u2988", "\\limg  \\rimg", "Relational Image"),
			new ZChar("\u2197+\u2199", "^{+}", "Transitive closure")
		},
		{ "Functions",
			new ZChar("\u2192", "\\fun", "Total Function"),
			new ZChar("\u21F8", "\\pfun", "Partial Function"),
			new ZChar("\u2914", "\\pinj", "Partial Injection"),
			new ZChar("\u21A3", "\\inj", "Total Injection"),
			new ZChar("\u2900", "\\psurj", "Partial Surjection"),
			new ZChar("\u2916", "\\bij", "Total Bijection"),
			new ZChar("\u21FB", "\\ffun", "Finite Function"),
			new ZChar("\u2915", "\\finj", "Finite Injection"),
			new ZChar("\u2218", "\\circ", "Functional Composition"),
			new ZChar("\u03BB", "\\lambda", "Lambda"),
			new ZChar("\u03BC", "\\mu", "Mu (Choice)")
		},
		{ "Sequences",
			new ZChar("\u27E8  \u27E9", "\\langle  \\rangle", "Literal Sequence"),
			new ZChar("\u2040", "\\cat", "Concatenation"),
			new ZChar("\u2040/", "\\dcat", "Distributed Concatenation"),
			new ZChar("\u21BF", "\\extract", "Extract"),
			new ZChar("\u21BE", "\\filter", "Filter"),
			new ZChar("#", "\\#", "Size of a finite set")
		},
		{ "Arithmetic",
			new ZChar("\u2124", "\\num", "Integers"),
			new ZChar("\u2115", "\\nat", "Natural Numbers"),
			new ZChar("\uD835\uDD38", "\\arithmos", "All Numbers"),  // U+1D538
			new ZChar("+", "+", "Binary Plus"),
			new ZChar("\u2212", "-", "Binary Minus"),
			new ZChar("-", "\\negate", "Unary Negation"),
			new ZChar("*", "*", "Multiplication"),
			new ZChar("div", "\\div", "Integer Division"),
			new ZChar("mod", "\\mod", "Integer Modulo"),
			new ZChar("\u2264", "\\leq", "Less Than"),
			new ZChar("\u2265", "\\geq", "Greater Than")
		},
      	{ "Schemas",
			new ZChar("\u0394", "\\Delta", "Delta"),
			new ZChar("\u039E", "\\Xi", "Xi"),
			new ZChar("\u03B8", "\\theta", "Theta"),
			new ZChar("\u2989..\u298A", "\u2989 NAME == EXPR \u298A", 
					"\\lblot NAME == EXPR \\rblot", "Literal Binding"),
			new ZChar("\u29F9", "\\hide", "Schema Hiding"),
			new ZChar("\u2A21", "\\project", "Schema Projection"),
			new ZChar("\u2A1F", "\\semi", "Sequential Composition"),
			new ZChar("\u2A20", "\\pipe", "Schema Piping"),
			new ZChar("\u2032", "'", "Prime decoration"),
			new ZChar("\u21981\u2196", "_{1}", "Subscript decoration"),
      	}
    };
    */
	
	/**
	 * Returns the Z Char file
	 */
	public File getZCharFile() {
		try {
			return new File(Platform.resolve(
		            CZTPlugin.getDefault().getBundle().getEntry("/")).getFile(), this.ZTABLEFILE);
		} catch (IOException ie) {
			
		}
		
		return null;
/*
		String filepath = getClass().getResource("/ZTable2.xml").getFile();
		return new File(filepath);
*/
	}
	
    /**
     * Returns the Object array comprising Z char table.
     *
     * @return the Object array comprising Z char table.
     */
    public Object[][] getZCharTable() {
    	return this.mTableArray;
    }
    
    public Object[][] createZCharTable() {
    	Object[][] table;
		// to store all z chars
		List tableList = new ArrayList();
    	try {
    		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
    		DocumentBuilder builder = factory.newDocumentBuilder();
    		File file = getZCharFile();
    		if (file == null)
    			return new Object[0][0];
    		Document doc = builder.parse(file);
    		
    		// gets the root of the structure of the XML file
    		Element root = doc.getDocumentElement();
    		// gets the list of all items
    		NodeList rows = root.getChildNodes();
    		for (int i = 0; i < rows.getLength(); i++) {
    			Node rowNode = rows.item(i);
    			// continue if the child is not an element, but a whitespace
    			if (! (rowNode instanceof Element))
    				continue;
    			// to store all z chars in a row of the XML file
    			List rowList = new ArrayList();
    			Element row = (Element) rowNode;
    			String heading = row.getAttribute("heading");
    			rowList.add(heading);
    			NodeList items = row.getChildNodes();
    			for (int j = 0; j < items.getLength(); j++) {
    				Node itemNode = items.item(j);
    				// continue if the child is not an element, but a whitespace
    				if ( ! (itemNode instanceof Element))
    					continue;
    				Element item = (Element) itemNode;
    				String name = item.getAttribute("name");
    				String description = item.getAttribute("description");
    				String unicode = item.getAttribute("unicode");
    				String latex = item.getAttribute("latex");
    				ZChar zch;
    				if (unicode == null)
    					zch = new ZChar(name, latex, description);
    				else
    					zch = new ZChar(name, unicode, latex, description);
    				rowList.add(zch);
    			}
    			
    			Object[] rowArray = new Object[rowList.size()];
    			rowList.toArray(rowArray);    			
    			tableList.add(rowArray);
    		}
    	} catch (IOException ie) {
    		ie.printStackTrace();
    	} catch (ParserConfigurationException pce) {
    		pce.printStackTrace();
    	} catch (SAXException se) {
    		se.printStackTrace();
    	}
    	
    	table = new Object[tableList.size()][];
    	tableList.toArray(table);    	
    	
    	return table;
    }
    
    /**
     * Returns the maximum length of all the rows.
     *
     * @return the number of columns in this table.
     */
    public int getColumnCount() {
    	int erg = 0;
    	for(int i=0; i<mTableArray.length; i++) {
    		if (mTableArray[i].length > erg) {
    			erg = mTableArray[i].length;
    		}
    	}
    	return erg;
    }

    /**
     * Returns the number of rows.
     *
     * @return the number of rows in this table.
     */
    public int getRowCount() {
    	return mTableArray.length;
    }
    
    /**
     * Gets the object at the specified position.
     * If no object can be found the empty string
     * is returned.
     *
     * @return the object at the specified position
     *         or the empty string (should never be
     *         <code>null</code>). 
     */
    public Object getValueAt(int row, int col) {
    	try {
    		return mTableArray[row][col];
    	} catch(IndexOutOfBoundsException e) {
    		return "";
    	}
    }

    /**
     * Returns <code>String.class</code> if <code>col</code>
     * is zero, <code>ZChar.class</code> otherwise.
     * Note that this method does not take the actual classes
     * contained in table into account.
     *
     * @return <code>String.class</code> if <code>col</code>
     *         is zero, <code>ZChar.class</code> otherwise.
     */
    public Class getColumnClass(int col) {
    	if (col==0) {
    		return String.class;
    	}
    	return ZChar.class;
    }

    /**
     * Returns <code>null</code> regardless of the column number.
     *
     * @return <code>null</code>
     */
    public String getColumnName(int col) {
      return null;
    }
}
