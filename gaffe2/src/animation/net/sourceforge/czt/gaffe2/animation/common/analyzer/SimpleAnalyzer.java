
package net.sourceforge.czt.gaffe2.animation.common.analyzer;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.URL;
import java.util.HashMap;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.table.DefaultTableModel;

import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class SimpleAnalyzer implements Analyzer
{
  private URL specURL;

  private HashMap<String, String> contentMap;

  /**
   * 
   */
  public SimpleAnalyzer()
  {
    specURL = null;
    contentMap = new HashMap<String, String>();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#initialize(java.io.File)
   */
  public void initialize(File file)
  {
    String line = "";
    String name = "";
    Matcher m;
    Pattern p;
    contentMap.clear();
    try {
      BufferedReader br = new BufferedReader(new FileReader(file));
      p = Pattern
          .compile("\\\\begin\\p{Punct}schema\\p{Punct}\\p{Punct}(\\w+)\\p{Punct}");
      String content;
      while (br.ready()) {
        line = br.readLine().trim();
        m = p.matcher(line);
        if (m.matches()) {
          content = "";
          content += (line + (char) Character.LINE_SEPARATOR);
          name = m.group(1);
          while (!line.equals("\\end{schema}") && br.ready()) {
            line = br.readLine();
            content += (line + (char) Character.LINE_SEPARATOR);
          }
          contentMap.put(name, content);
        }
      }
      br.close();
      this.specURL = file.toURL();
    } catch (IOException ioex) {
      ioex.printStackTrace();
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSpecURL()
   */
  public URL getSpecURL()
  {
    return this.specURL;
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaType(java.lang.String)
   */
  public String getSchemaType(String schemaName)
  {
    int stateSize = this.getVariableMap(schemaName, "state").keySet().size();
    int primedSize = this.getVariableMap(schemaName, "primed").keySet().size();
    int inputSize = this.getVariableMap(schemaName, "input").keySet().size();
    int outputSize = this.getVariableMap(schemaName, "output").keySet().size();
    if (stateSize > 0 && primedSize == 0 && inputSize == 0 && outputSize == 0) {
      return "State";
    }
    else if (stateSize == 0 && primedSize > 0 && inputSize == 0
        && outputSize == 0) {
      return "Initial";
    }
    else {
      return "Operation";
    }
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaContent(java.lang.String)
   */
  public String getSchemaContent(String schemaName)
  {
    return contentMap.get(schemaName);
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaNames()
   */
  public Set<String> getSchemaNames()
  {
    return contentMap.keySet();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getVariableMap(java.lang.String, java.lang.String)
   */
  public HashMap<String, Expr> getVariableMap(String schemaName,
      String variableType)
  {
    Factory factory = GaffeFactory.getFactory();
    HashMap<String, Expr> result = new HashMap<String, Expr>();
    String[] content = contentMap.get(schemaName).split(
        String.valueOf((char) Character.LINE_SEPARATOR));
    String line = "";
    String[] words;
    String name = "";
    String type = "";
    Matcher m;
    Pattern statePattern = Pattern.compile("\\w+");
    Pattern ioPattern = Pattern.compile("\\w+(\\p{Punct})");
    int i = 1;
    for (i = 1; i < content.length; i++) {
      line = content[i];
      if (line.equals("\\where")) {
        break;
      }
      words = line.split(":");
      if (words.length < 2) {
        continue;
      }
      name = words[0].trim();
      type = words[1].trim();
      Expr expr = null;
      for (String variable : name.split(",")) {
        if (variableType.equals("state")) {
          m = statePattern.matcher(variable);
          if (!m.matches()) {
            continue;
          }
        }
        else if (variableType.equals("primed")) {
          m = ioPattern.matcher(variable);
          if (!m.matches()) {
            continue;
          }
          else if (!m.group(1).equals("'")) {
            continue;
          }
        }
        else if (variableType.equals("input")) {
          m = ioPattern.matcher(variable);
          if (!m.matches()) {
            continue;
          }
          else if (!m.group(1).equals("?")) {
            continue;
          }
        }
        else if (variableType.equals("output")) {
          m = ioPattern.matcher(variable);
          if (!m.matches()) {
            continue;
          }
          else if (!m.group(1).equals("!")) {
            continue;
          }
        }
        if (type.contains("\\power")) {
          expr = factory.createSetExpr(factory.createZExprList());
        }
        else if (type.contains("\\pfun")) {
          DefaultTableModel dataModel = new DefaultTableModel();
          words = type.split("\\\\pfun");
          dataModel.addColumn(words[0]);
          dataModel.addColumn(words[1]);
          expr = factory.createBindExpr(factory.createZDeclList());
        }
        else {
          expr = factory.createRefExpr(factory.createZRefName(""));
        }
        result.put(variable.trim(), expr);
      }
    }
    return result;
  }
}
