/*
  Copyright (C) 2007 Leo Freitas
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

package net.sourceforge.czt.typecheck.circus;

/**
 * <P>Contains String constants for the keys used in parse properties.</P>
 *
 * <P>The behaviour of the CZT parser utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the parser utilities.</P>
 *
 * @author Leo Freitas
 */
public interface TypecheckPropertiesKeys
  extends net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys
{
  /**
   * <p>
   * This property tells whether or not to create special LetVar terms    *
   * within some variable scopes. That is, a LetVar term  creates a 
   * syntactic scope of the declared variable type (rather than its 
   * maximal typechecked type), which is useful for other tools to 
   * generate type-related proof obligations (e.g., a type is non-empty).
   * </p>
   * <p>
   * If switched off, the typechecked AST is left unchanged. Otherwsie,
   * the productions affected by this switch are wrapped around a LetVar
   * term (see Circus.xsd). Obviously, tools handling a typechecked AST
   * must be aware of the modified AST, in case LetVar is enabled.
   * </p>
   * <p>
   * The productions affected are input prefixing communication and variable
   * declaration. By default it is disabled, but different tools can change 
   * it accordingly through a configuration file (TODO).
   * </p>
   */
  String PROP_TYPECHECK_CREATE_LETVAR =
    "circus_typecheck_create_letvar";
  
  /**
   * <p>
   * This property tells whether or not to create special LetMu terms   
   * for mutually recursive actions. That is, a LetMu term  creates an 
   * array of recursive equations, where each declaring action contains 
   * its definition on a local environment. This allows syntactic scope 
   * for mutual recursion to be easily resolved. This is useful for other 
   * tools to handle mutual recursion.
   * </p>
   * <p>
   * If switched off, the typechecked AST is left unchanged. Otherwsie,
   * the productions affected by this switch are wrapped around a LetMu
   * term (see Circus.xsd). Obviously, tools handling a typechecked AST
   * must be aware of the modified AST, in case LetMu is enabled.
   * </p>
   * <p>
   * By default it is disabled, but different tools can change it accordingly
   * through a configuration file (TODO).
   * </p>
   */
  String PROP_TYPECHECK_RESOLVE_MUTUAL_REC =
    "circus_typecheck_resolve_mutual_rec";

  boolean PROP_TYPECHECK_CREATE_LETVAR_DEFAULT      = false;
  boolean PROP_TYPECHECK_RESOLVE_MUTUAL_REC_DEFAULT = false;
}
