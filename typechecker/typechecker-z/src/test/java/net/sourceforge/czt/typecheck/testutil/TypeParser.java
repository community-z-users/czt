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
package net.sourceforge.czt.typecheck.testutil;

import java.util.List;
import java.util.ArrayList;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * Parses a Z type written in an abstract format and produces CZT Type
 * objects
 *
 * @author Tim Miller
 */
public class TypeParser
{
  //the buffer containing the type
  protected String sType_;

  //the index to the current symbol
  protected int index_;

  //the current symbol
  protected String current_;

  //the list of variable types that have been created
  protected List<VariableType> vTypes_;

  //the Factory
  protected Factory factory_ ;

  protected TypeParser()
  {
    this("");
  }

  protected TypeParser(String sType)
  {
    sType_ = sType;
    index_ = 0;
    current_ = null;
    vTypes_ = list();
    ZFactory zFactory = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    factory_ = new Factory(zFactory);
  }

  public static Type getType(String sType)
  {
    TypeParser typeParser = new TypeParser(sType);
    return typeParser.parseType();
  }

  protected void setType(String sType)
  {
    sType_ = sType;
    index_ = 0;
    current_ = null;
  }

  protected String currentToken()
  {
    //String result = new String(current_);
    return current_;
  }

  protected String lookAhead()
  {
    String result = "";

    final int currentIndex = index_;
    result = nextToken();
    index_ = currentIndex;

    return result;
  }

  protected String nextToken()
  {
    current_ = "";

    //skip whitespace
    while (index_ < sType_.length() && sType_.charAt(index_) == ' ') {
      index_++;
    }

    //if at the end of the buffer, return null
    if (index_ == sType_.length()) {
      return null;
    }

    char prevSym = '@';
    char nextSym = '@';
    final char sym = sType_.charAt(index_);
    if (index_ + 1 < sType_.length()) {
      nextSym = sType_.charAt(index_ + 1);
    }
    if (index_ != 0) {
      prevSym = sType_.charAt(index_ - 1);
    }

    switch(sym) {
    case '\\':
      if ('[' == nextSym) {
        current_ = "\\[";
        index_ += 2;
        break;
      }
      else if (']' == nextSym) {
        current_ = "\\]";
        index_ += 2;
        break;
      }
    case '(':
    case ')':
    case '[':
    case ']':
    case ':':
    case ';':
    case ',':
      current_ = Character.toString(sym);
      index_++;
      break;
    case 'P':
    case 'x':
      if (!Character.isJavaIdentifierPart(nextSym) &&
          !Character.isJavaIdentifierPart(prevSym)) {
        current_ = Character.toString(sym);
        index_++;
        break;
      }
    default:
      //an identifier
      while (index_ < sType_.length() &&
             Character.isJavaIdentifierPart(sType_.charAt(index_))) {
        current_ += sType_.charAt(index_++);
      }
    }

    return current_;
  }

  protected Type2 parseInnerType()
  {
    Type2 result = null;
    String token = nextToken();

    if ("GIVEN".equals(token)) {
      token = nextToken();
      ZName zName = createZName(token);
      result = factory_.createGivenType(zName);
    }
    else if ("VARTYPE".equals(token)) {
      token = nextToken();
      ZName zName = createZName(token);
      result = createVariableType(zName);
    }
    else if ("GENTYPE".equals(token)) {
      token = nextToken();
      ZName zName = createZName(token);
      result = factory_.createGenParamType(zName);
    }
    else if ("(".equals(token)) {
      result = parseType2();
      nextToken(); //consume the ")"
    }
    else if ("P".equals(token)) {
      Type2 innerType = parseInnerType();
      result = factory_.createPowerType(innerType);
    }
    else if ("[".equals(token)) {
      Signature signature = parseSignature();
      result = factory_.createSchemaType(signature);
    }

    return result;
  }

  protected GenericType parseGenericType()
  {
    String nextToken = nextToken();  //consume "\\["

    //parse the list of names
    List<Name> nameList = list();
    ZNameList names = factory_.createZNameList(nameList);
    while (!"\\]".equals(nextToken)) {
      String word = nextToken();
      ZName zName = createZName(word);
      names.add(zName);

      nextToken = nextToken();
    }

    Type2 type = null;
    Type2 optionalType = null;

    //if there are two types
    if ("(".equals(lookAhead())) {
      nextToken(); //consume the "("
      type = parseType2();
      nextToken(); //consume the ","
      optionalType = parseType2();
      nextToken(); //consume the ");
    }
    else {
      type = parseType2();
    }

    GenericType result =
      factory_.createGenericType(names, type, optionalType);

    return result;
  }

  protected Type2 parseType2()
  {
    Type2 result = parseInnerType();

    String lookAhead = lookAhead();
    //if this is a product type
    while (lookAhead != null && "x".equals(lookAhead)) {
      nextToken(); //consume the "x"

      Type2 nextType = parseInnerType();

      List<Type2> types = list();
      types.add(result);
      types.add(nextType);
      result = factory_.createProdType(types);

      lookAhead = lookAhead();
    }

    return result;
  }

  protected Type parseType()
  {
    Type result = null;

    if ("\\[".equals(lookAhead())) {
      result = parseGenericType();
    }
    else {
      result = parseType2();
    }

    return result;
  }

  protected Signature parseSignature()
  {
    List<NameTypePair> pairs = list();

    //if empty, consume the "]" token
    if ("]".equals(lookAhead())) {
      nextToken();    //consume the  "]"
    }
    else {
      //the next token should be an identifier
      String nextToken = null;
      while (!"]".equals(nextToken)) {
        String word = nextToken();
        ZName zName = createZName(word);
        nextToken();   //consume the ":"

        Type type = parseType();
        NameTypePair nameTypePair =
          factory_.createNameTypePair(zName, type);
        pairs.add(nameTypePair);
        nextToken = nextToken();   //consume the ";" or "]"
      }
    }

    Signature signature = factory_.createSignature(pairs);
    return signature;
  }

  protected VariableType createVariableType(ZName zName)
  {
    for (VariableType vType : vTypes_) {
      if (vType.getName().equals(zName)) {
        return vType;
      }
    }
    VariableType result = factory_.createVariableType(zName);
    vTypes_.add(result);
    return result;
  }

  //create a name, but set the ID to 0
  protected ZName createZName(String word)
  {
    ZName zName = factory_.createZDeclName(word);
    zName.setId("0");
    return zName;
  }

  protected static <T> List<T> list()
  {
    return new ArrayList<T>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }
}
