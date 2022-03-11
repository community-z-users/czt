
package net.sourceforge.czt.animation.common.analyzer;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.animation.common.factory.GaffeUtil;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.impl.PowerTypeImpl;
import net.sourceforge.czt.typecheck.z.impl.SchemaTypeImpl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZChar;

/**
 * @author Linan Zhang
 *
 */
public class ZLiveAnalyzer implements Analyzer
{
  private URL specURL;                              // The specification URL

  private Map<String, Signature> schemaMap;         // The schema name -> content map

  private Factory factory;                          // The factory from ZLive

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#initialize(java.io.File)
   */
  public void initialize(File specFile)
  {
    try {
      specURL = specFile.toURI().toURL();
      schemaMap = new HashMap<String, Signature>();
      factory = GaffeFactory.getFactory();

      // Init ZLive
      ZLive zlive_ = GaffeFactory.getZLive();
      Source src = new FileSource(specFile);
      SectionManager manager = zlive_.getSectionManager();
      manager.reset();
      manager.put(new Key<Source>(specFile.getName(), Source.class), src);
      Spec spec = manager.get(new Key<Spec>(specFile.getName(), Spec.class));
      String sectName = null;

      // Find the last section, normally the specification
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          sectName = ((ZSect) sect).getName();
          Key<SectTypeEnvAnn> typekey = new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class);
          SectTypeEnvAnn types = manager.get(typekey);

          // If belongs to specification, put them into schemaMap
          for (NameSectTypeTriple triple : types.getNameSectTypeTriple()) {
            String section = triple.getSect();
            if (section.equals("Specification")) {
              ZName declName = triple.getZName();
              Type type = triple.getType();
              if (type instanceof PowerTypeImpl) {
                PowerTypeImpl pti = (PowerTypeImpl) type;
                Type type0 = pti.getType();
                if (type0 instanceof SchemaTypeImpl) {
                  SchemaTypeImpl sti = (SchemaTypeImpl) type0;
                  Signature signature = sti.getSignature();
                  schemaMap.put(declName.getWord(), signature);
                }
              }
            }
          }
        }
      }
      if (sectName != null) {
        zlive_.setCurrentSection(sectName);
      }
    } catch (CommandException comex) {
      comex.printStackTrace();
    } catch (MalformedURLException muex) {
      muex.printStackTrace();
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
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getSchemaNames()
   */
  public Set<String> getSchemaNames()
  {
    return schemaMap.keySet();
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
    return schemaMap.get(schemaName).toString();
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.gaffe2.animation.common.analyzer.Analyzer#getVariableMap(java.lang.String, java.lang.String)
   */
  public HashMap<String, Expr> getVariableMap(String schemaName,
      String variableType)
  {
    HashMap<String, Expr> result = new HashMap<String, Expr>();
    Signature signature = schemaMap.get(schemaName);
    String name;
    Type type;
    Stroke stroke;
    ZStrokeList strokeList;
    Map<String, Class<?>> customMap = GaffeUtil.getCustomMap();
    for (NameTypePair ntp : signature.getNameTypePair()) {
      name = ntp.getZName().toString();
      type = ntp.getType();
      strokeList = ntp.getZName().getZStrokeList();
      /*
       PowerType(Type) "\{..,..,..,..,..\}"         SetExpr
       ProdType(Type)  "(..,..,..,..,..)"           TupleExpr
       GivenType(ZString.ARITHMOS)   "33"           NumExpr    
       GivenType(ZString.S)          "fred"         RefExpr(GivenValue)
       SchemaType(Signature(ListTerm<NameTypePair(DeclName, Type)>)) 
       "\lblot n1== v1, n2==v2, ...... \rblot"  BindExpr
       */
      if (strokeList.size() == 0 && !variableType.equals("state")) {
        continue;
      }
      else if (strokeList.size() > 0) {
        stroke = strokeList.get(0);
        if (stroke instanceof InStroke && !variableType.equals("input")) {
          continue;
        }
        else if (stroke instanceof OutStroke && !variableType.equals("output")) {
          continue;
        }
        else if (stroke instanceof NextStroke && !variableType.equals("primed")) {
          continue;
        }
      }
      if (type instanceof GivenType) {
        //GivenType givenType = (GivenType)type;
        result.put(name, factory.createNumExpr(0));
      }
      else if (type instanceof PowerType) {
        ZExprList exprList = factory.createZExprList();
        result.put(name, factory.createSetExpr(exprList));
      }
      else if (type instanceof ProdType) {
        ZExprList exprList = factory.createZExprList();
        result.put(name, factory.createTupleExpr(exprList));
      }
      else if (type instanceof SchemaType) {
        ZDeclList declList = factory.createZDeclList();
        result.put(name, factory.createBindExpr(declList));
      }
      else {
        System.out.println("Unknown Type for DeclName: " + name
            + " as Type of " + type.toString());
      }
      if (customMap.get(name) == null) {
        customMap.put(name, GaffeUtil.getAvailableMap().get(
            result.get(name).getClass().getSimpleName()).get(0));
        customMap.put(name+ZChar.PRIME, GaffeUtil.getAvailableMap().get(
            result.get(name).getClass().getSimpleName()).get(0));
      }
    }
    return result;
  }

}
