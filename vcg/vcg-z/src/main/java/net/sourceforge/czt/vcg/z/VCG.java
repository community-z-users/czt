/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the czt project.
 * 
 * The czt project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The czt project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with czt; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z;

import java.util.SortedSet;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author Leo Freitas
 */
public interface VCG<R> {

  /**
   * True whenever section manager and VC collectors are not null, if the
   * configuration flag is set as well.
   * @return sectManager_ != null &amp;&amp; getVCCollector() != null &amp;&amp; isConfigured_
   */
  boolean isConfigured();

  /**
   * Sets up available options according to the section manager's configuration.
   * It does nothing if no section manager is available.
   * @return underlying section manager properly configured, if needed (see {@link #isConfigured() }).
   * @throws VCGException
   */
  SectionManager config() throws VCGException;
  void setSectionManager(SectionManager manager) throws VCGException;
  void setDefaultProperties(SectionManager manager);
  void reset();

  SectionManager getManager();
  VCCollector<R> getVCCollector();
  Class<? extends VCEnvAnn<R>> getVCEnvAnnClass();

  void typeCheck(String sectName, boolean sourceSect) throws VCGException;

  /**
   * Process the given Z section to generate VCs. The result is a Z sections with the
   * given Z section as its parent, and with generated VCs as conjectures for
   * its paragraphs.
   *
   * @param term Z section to generate VCs
   * @return Z section as a list of VC conjectures
   * @throws VCGException
   */
  VCEnvAnn<R> createVCEnvAnn(ZSect term) throws VCGException;

  /**
   * VC calculation for the given term, presuming it is a ZSect, Para, Pred,
   * Expr or Decl. The result is Z sections named uniquely with
   * standard toolkits as its parents, and with VC
   * conjectures for the term, if any. The result is a wrapped VCEnvAnn.
   *
   * @param term Z section to generate VCs
   * @param parents list of parents for the on-the-fly section
   * @return VC Z section as a list of VC conjectures
   * @throws VCGException
   */
  VCEnvAnn<R> createVCEnvAnn(Term term) throws VCGException;

  /**
   *
   * @param parent
   */
  void addParentSectionToIgnore(String parent);

  /**
   * Returns a unmodifiable set of section names not being processed for VC generation.
   * @return
   */
  SortedSet<String> getParentsToIgnore();
  boolean isAddingTrivialVC();
  boolean isProcessingParents();
  boolean isRaisingTypeWarnings();
  boolean isCheckingDefTblConsistency();
}
