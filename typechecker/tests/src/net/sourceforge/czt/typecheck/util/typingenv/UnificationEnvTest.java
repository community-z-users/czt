/**
Copyright (C) 2004 Tim Miller
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

package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

import net.sourceforge.czt.typecheck.testutil.TypeParser;

/**
 * A JUnit test class for testing the Z type-unification environment
 *
 * @author Tim Miller
 */
public class UnificationEnvTest
  extends TestCase
{
  protected UnificationEnv unificationEnv_;
  protected ZFactory factory_ = new ZFactoryImpl();

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(UnificationEnvTest.class);
    return suite;
  }

  protected void setUp()
  {
    unificationEnv_ = new UnificationEnv();
    unificationEnv_.enterScope();
  }

  protected void tearDown()
  {
    unificationEnv_.exitScope();
  }

  //test basic types without variable types
  public void testBasic()
  {
    //unification succeeds
    String [][] succ =
      {
        //basic GivenType
        {"GIVEN g", "GIVEN g", "GivenType"},

        //basic PowerType
        {"P GIVEN g", "P GIVEN g", "PowerType"},

        //basic ProdType - 2 elements
        {"P(GIVEN g) x GIVEN g", "P(GIVEN g) x GIVEN g", "ProdType - 2 elements"},

        //basic ProdType - 3 elements
        {"P(GIVEN g) x GIVEN g x P(GIVEN g)",
         "P(GIVEN g) x GIVEN g x P(GIVEN g)",
         "ProdType - 3 elements"},

        //empty SchemaType
        {"[]", "[]", "SchemaType - empty sig"},

        //SchemaType - 1 name
        {"[name1 : P(GIVEN g)]", "[name1 : P(GIVEN g)]", "SchemaType - 1 name"},

        //SchemaType - > 1 names
        {"[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "SchemaType - > 1 name"},

        //swap pairs in SchemaType
        {"[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "[name1 : P(GIVEN g); name3 : []; name2 : GIVEN g]",
         "SchemaType - swapped names"},

      };

    for (int i = 0; i < succ.length; i++) {
      String [] next = succ[i];
      Type2 first = TypeParser.getType(next[0]);
      Type2 second = TypeParser.getType(next[1]);
      String message = next[2];

      Type unified = unificationEnv_.unify(first, second);
      assertEquals(message, unified, first);
    }

    //unification fails
    String [][] fail =
      {
        //different names in GivenType
        {"GIVEN g", "GIVEN g2", "GivenType different names"},

        //different type in PowerType
        {"P GIVEN g", "P []", "PowerType different types"},

        //nested PowerType in PowerType
        {"P GIVEN g", "P P GIVEN g", "PowerType nested PowerType"},

        //change 1 type to ProdType
        {"P(GIVEN given) x GIVEN given x P(GIVEN given)",
         "P(GIVEN given) x GIVEN given2 x P(GIVEN given)",
         "ProdType change one type"},

        //remove 1 type to ProdType
        {"P(GIVEN given) x GIVEN given x P(GIVEN given)",
         "P(GIVEN given) x GIVEN given",
         "ProdType remove one type"},

        //add 1 type to ProdType
        {"P(GIVEN given) x GIVEN given x P(GIVEN given)",
         "P(GIVEN given) x GIVEN given x P(GIVEN given) x []",
         "ProdType add one type"},

        //remove 1 pair from SchemaType
        {"[name1 : P(GIVEN g)]", "[]", "SchemaType remove 1 pair - 1"},

        {"[name1 : P(GIVEN g); name2 : GIVEN g]",
         "[name1 : P(GIVEN g)]",
         "SchemaType remove 1 pair - 2"},

        {"[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "[name1 : P(GIVEN g); name3 : []]",
         "SchemaType remove 1 pair - 3"},

        //different types for the same name
        {"[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "[name1 : P(GIVEN g); name2 : GIVEN g; name3 : [name4 : GIVEN g]]",
         "SchemaType different types for same name"},
      };

    for (int i = 0; i < fail.length; i++) {
      String [] next = fail[i];
      Type2 first = TypeParser.getType(next[0]);
      Type2 second = TypeParser.getType(next[1]);
      String message = next[2];

      Type unified = unificationEnv_.unify(first, second);
      assertNull(message, unified);
    }
  }

  public void testVariableType()
  {
    //unification succeeds
    String [][] succ =
      {
        //one VariableType for another
        {"VARTYPE _a1", "VARTYPE _a2", "one VariableType for another"},

        //GivenType for a VariableType
        {"VARTYPE _a2", "GIVEN g", "GivenType for a VariableType"},
        {"VARTYPE _a1", "GIVEN g", "testing transitive unification"},

        //PowerType for a VarType
        {"P GIVEN g", "VARTYPE _a3", "PowerType for a VariableType"},

        //Variable type within a PowerType
        {"P GIVEN g", "P VARTYPE _a4", "VariableType within a PowerType"},

        //one type in ProdType
        {"P(GIVEN g) x GIVEN g", "VARTYPE _a5 x GIVEN g", "ProdType - one var"},
        {"VARTYPE _a5", "P(GIVEN g)", "testing unification of _a5"},

        //several types in ProdType
        {"P(GIVEN g) x GIVEN g x []",
         "P(VARTYPE _a6) x VARTYPE _a6 x VARTYPE _a7",
         "several variables in ProdType"},
        {"VARTYPE _a6", "GIVEN g", "testing unification of _a6"},
        {"VARTYPE _a7", "[]", "testing unification of _a7"},

        //mixed variables in ProdType
        {"P(GIVEN g) x VARTYPE _a8 x VARTYPE _a9",
         "P(VARTYPE _a8) x VARTYPE _a8 x []",
         "mixed variables in ProdType"},
        {"VARTYPE _a8", "GIVEN g", "testing unification of _a8"},
        {"VARTYPE _a9", "[]", "testing unification of _a9"},


        //empty SchemaType
        {"VARTYPE _a10", "[]", "SchemaType - empty sig"},

        //a SchemaType for a VariableType
        {"VARTYPE _a11", "[name1 : GIVEN g]", "SchemaType - empty sig"},

        //a variables within a SchemaType signature
        {"[name1 : VARTYPE _a12]",
         "[name1 : P GIVEN g]",
         "SchemaType - VariableType within a SchemaType signature"},
        {"VARTYPE _a12", "P GIVEN g", "testing unification of _a12"},

        //mixed variables within SchemaTypes
        {"[name1 : VARTYPE _a13; name2 : P P GIVEN g; name3 : GIVEN g]",
         "[name1 : P GIVEN g; name2 : P VARTYPE _a13; name3 : VARTYPE _a14]",
         "SchemaType - mixed variables within a SchemaType signature"},
        {"VARTYPE _a13", "P GIVEN g", "testing unification of _a13"},
        {"VARTYPE _a14", "GIVEN g", "testing unification of _a14"},

        //test that transitive subsitutions occur
        {"VARTYPE _a12", "VARTYPE _a15", "testing transitive _a15 (part 1)"},
        {"VARTYPE _a15", "P GIVEN g", "testing transitive _a15 (part 2)"},

        /*
        //SchemaType - 1 name
        {"[name1 : P(GIVEN g)]", "[name1 : P(GIVEN g)]", "SchemaType - 1 name"},

        //SchemaType - > 1 names
        {"[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "SchemaType - > 1 name"},

        //swap pairs in SchemaType
        {"[name1 : P(GIVEN g); name2 : GIVEN g; name3 : []]",
         "[name1 : P(GIVEN g); name3 : []; name2 : GIVEN g]",
         "SchemaType - swapped names"},
        */
      };

    for (int i = 0; i < succ.length; i++) {
      String [] next = succ[i];
      Type2 first = TypeParser.getType(next[0]);
      Type2 second = TypeParser.getType(next[1]);
      String message = next[2];

      Type unified = unificationEnv_.unify(first, second);
      assertNotNull(message, unified);
    }
  }

  protected static List list()
  {
    return new ArrayList();
  }
}
