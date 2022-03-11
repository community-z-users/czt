/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.history;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.animation.ZLocator;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.gui.temp.GaffeFactory;
import net.sourceforge.czt.animation.gui.temp.SolutionSet;
import net.sourceforge.czt.animation.gui.temp.ZBinding;
import net.sourceforge.czt.animation.gui.temp.ZSet;
import net.sourceforge.czt.animation.gui.temp.ZValue;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * History Interface that proxy to ZLive.
 */
public class ZLiveHistory extends BasicHistory
{
  private ZLive zLive_;
  private SectionManager sectman_;
  /**
   * 
   */
  public ZLiveHistory()
  {
    super();
  }
  
  /**
   * @param stateSchema
   * @param initSchema
   */
  public ZLiveHistory(String stateSchema, String initSchema)
  {
    super();
    System.out.println("Please specify the URL for the tex file");
  }
  
  public ZLiveHistory(String stateSchema, String initSchema, URL specURL)
  {
    zLive_ = GaffeFactory.getZLive();
    sectman_ = zLive_.getSectionManager();
    sectman_.putCommands(Dialect.ZPATT);
    try {
      Source specSource = new UrlSource(specURL);
      specSource.setMarkup(Markup.LATEX);
      sectman_.put(new Key<Source>("ZLiveHistory",Source.class), specSource);
      Spec spec = sectman_.get(new Key<Spec>("ZLiveHistory", Spec.class));
      String sectName = null;
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          sectName = ((ZSect) sect).getName();
          //output_.println("Loading section " + sectName);
          sectman_.get(new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class));
        }
      }
      if (sectName != null) {
        //output_.println("Setting section to " + sectName);
        zLive_.setCurrentSection(sectName);
      }
      this.activateSchema(initSchema);
    }
    catch (Exception e) {
      System.err.println("ERROR creating ZLiveHistory section: " + e);
      e.printStackTrace();
    }
  }
  
  public void activateSchema(String schema)
  {
    try {
      Expr sexpr = zLive_.schemaExpr(schema);
      BindExpr inputs = this.format(this.inputs_).getExpr();
      Envir env = new Envir().plusAll(inputs);
      EvalSet temp = (EvalSet) zLive_.evalTerm(true, sexpr,env).getResult();
      ZSet result = new ZSet(temp);
      this.solutionSets.add(new SolutionSet(schema,result.getSet()));
      this.nextSolutionSet();  // Calls the listeners
    }
    catch (CommandException coex){
      coex.printStackTrace();
    }
  }
  
  public ZBinding format(Map<ZLocator,ZValue> inputs){
    Map<String, ZValue> bindMap = new HashMap<String,ZValue>();
    String temp = "";
    for (ZLocator key : inputs.keySet()){
      temp = key.toString();
      if (temp.endsWith("'")){
        temp = temp.substring(0,temp.length()-1);
      }
      bindMap.put(temp, (ZValue)inputs.get(key));
    }
    ZBinding result = new ZBinding(bindMap);
    return result;
  }
}
