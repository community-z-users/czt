package net.sourceforge.czt.vcg.z.feasibility;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.util.BindingFilter;
import net.sourceforge.czt.vcg.util.BindingUtils;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.util.DefinitionComparator;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.TermTransformer;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.transformer.feasibility.ZPredTransformerFSB;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.ZBranchListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;

/**
 * Abstract class used by both FSB and REF
 * @author nljsf
 *
 */
public abstract class AbstractFeasibilityVCCollector<T, B> extends
		TrivialFeasibilityVCCollector<T, B> implements GivenParaVisitor<Pred>,
		FreeParaVisitor<Pred>, AxParaVisitor<Pred>, ZFreetypeListVisitor<Pred>,
		FreetypeVisitor<Pred>, ZBranchListVisitor<Pred>, BranchVisitor<Pred>//,
		//FeasibilityPropertyKeys 
{

	private ZPredTransformerFSB predTransformer_;

	private boolean nonEmptyGivenSets_;
	private boolean doCreateZSchemas_;

	protected final Map<ZName, AxPara> addedSigSchemas_;
	protected final Map<ZName, SortedSet<Definition>> computedBindings_;

	/**
	 * Creates a new instance of DCTerm
	 * 
	 * @param factory
	 */
	public AbstractFeasibilityVCCollector(Factory factory) {
		super(factory);
		setPredTransformer(new ZPredTransformerFSB(factory, this));
		predTransformer_.setApplyTransformer(PROP_VCG_FEASIBILITY_APPLY_TRANSFORMERS_DEFAULT);
		setNonemptyGivenSetVC(PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS_DEFAULT);
		setCreateZSchemas(PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS_DEFAULT);
		addedSigSchemas_ = new TreeMap<ZName, AxPara>(ZUtils.ZNAME_COMPARATOR);
		computedBindings_ = new TreeMap<ZName, SortedSet<Definition>>(
				ZUtils.ZNAME_COMPARATOR);

	}

	protected ZPredTransformerFSB getPredTransformerFSB()
	{
	  return (ZPredTransformerFSB)getTransformer();
	}

	protected final void setPredTransformer(ZPredTransformerFSB tt)
	{
		assert tt != null;
		predTransformer_ = tt;
	}
		
	protected void clearAddedPara() {
		addedSigSchemas_.clear();
		computedBindings_.clear();
		getVCGContext().clear();
	}

	@Override
	public List<? extends Para> addedPara() {
		return new ArrayList<Para>(addedSigSchemas_.values());
	}

	protected VCCollectionException createVCCollectionException(
			final String message) {
		return new FeasibilityException(getDialect(), message);
	}

	protected VCCollectionException createVCCollectionException(
			final String message, Throwable e) {
		return new FeasibilityException(getDialect(), message, e);
	}

	@Override
	public TermTransformer<Pred> getTransformer() {
		return predTransformer_;
	}

	public boolean isAddingNonemptyGivenSetVC() {
		return nonEmptyGivenSets_;
	}

	public boolean isCreatingZSchemas() {
		return doCreateZSchemas_;
	}

	protected final void setNonemptyGivenSetVC(boolean value) {
		nonEmptyGivenSets_ = value;
	}

	protected final void setCreateZSchemas(boolean value) {
		doCreateZSchemas_ = value;
	}

	/**
	 * VC COLLECTOR METHODS
	 * 
	 * @param vc
	 * @return
	 * @throws VCCollectionException
	 */

	@Override
	protected VCType getVCType(Pred vc) throws VCCollectionException {
		VCType result = vc.getAnn(VCType.class);
		if (result == null)
			result = VCType.NONE;
		return result;
	}

	@Override
	protected void beforeCalculateVC(Term term, List<? extends InfoTable> tables)
			throws VCCollectionException {
		super.beforeCalculateVC(term, tables);
		if (getDefTable() == null) {
			throw new VCCollectionException(getDialect(), 
					"VCG-FSB-NO-DEFTBL: cannot calculate fsb vcs without DefTbl");
		}
	}

	/** PARAGRAPH VISITING METHODS */

	/**
	 * Calculates DC for given term (i.e. visits term). As some Z productions
	 * have null terms , like AxPara \begin{axdef} x: \nat \end{axdef} has null
	 * predicate, implementations should take care of such situations
	 * accordingly. For null terms in this collector, we presume a harmless DC
	 * condition (e.g., true).
	 * 
	 * @param term
	 * @return
	 */
	@Override
	public Pred visit(Term term) {
		assert getDefTable() != null;
		if (term == null) {
			// for null terms, warn, but assume harmless (E.g., no VCs to be
			// generated)
			getLogger().finest("VCG-FSBCOL-NULL-TERM");
			return getPredTransformerFSB().truePred();
		} else {
			return getTransformer().visit(term);
		}
	}

	protected void checkPreviousState(String prefix, ZName oldStName,
			ZName newStName) throws CztException {
		if (oldStName != null)
			throw new CztException(createVCCollectionException(prefix
					+ " already set through section manager properties as "
					+ ZUtils.toStringZName(oldStName)
					+ ". Cannot change it to "
					+ ZUtils.toStringZName(newStName)));
	}

	/**
	 * Checks the given schema name in the definition table
	 * 
	 * @param prefix
	 * @param stName
	 * @param filter
	 * @throws CztException
	 */
	protected void checkStateBindings(String prefix, ZName stName,
			BindingFilter filter) throws CztException {
		SortedSet<Definition> mixedBindings;
		try {
			if (computedBindings_.containsKey(stName))
				throw new DefinitionException(getDialect(), 
						"VC-FSB-DUPLICATE-SCHEMA-IN-DEFTBL = " + stName);
			mixedBindings = new TreeSet<Definition>(getBindingsFor(stName));
		} catch (DefinitionException ex) {
			throw new CztException(createVCCollectionException(
					"VC-FSB-STATE-SCHEMA-DEFEXCEPTION for " + stName, ex));
		}
		SortedSet<Definition> stateBindings = BindingUtils.filterBindings(
				mixedBindings, filter);
		mixedBindings.removeAll(stateBindings);
		if (!mixedBindings.isEmpty()) {
			throw new CztException(createVCCollectionException(prefix + " '"
					+ stName
					+ "' has inconsistent state bindings.\n\tBindings...: "
					+ mixedBindings.toString()));
		}
	}

	/**
	 * Check whether bindings were already computed for the given name and
	 * return a copy of them if so. Otherwise, return compute them, save them,
	 * and return a copy so that the next call can use the originals. This is
	 * useful to see whether to populate schema declarations with schema
	 * inclusions or not. Ah, actually there is no need to copy the result,
	 * providing it's not changed. So return a unmodifiable version then.
	 * 
	 * @param name
	 * @return
	 * @throws DefinitionException
	 */
	protected SortedSet<Definition> getBindingsFor(ZName name)
			throws DefinitionException {
		SortedSet<Definition> result = computedBindings_.get(name);
		if (result == null) {
			result = getDefTable().bindings(name);
			computedBindings_.put(name, result);
		}
		assert result != null;
		return Collections.unmodifiableSortedSet(result); // new
															// TreeSet<Definition>(result);
	}

	/* VC GENERATION HELPER METHODS */

	public FSBVCNameFactory getFSBVCNameFactory() {
		assert getVCNameFactory() instanceof FSBVCNameFactory;
		return (FSBVCNameFactory) getVCNameFactory();
	}

	protected ZName getSigSchemaName(ZName schName) {
		String sigSchemaName = getFSBVCNameFactory().getSigSchemaName(
				schName.getWord());
		return ZUtils.FACTORY.createZName(sigSchemaName,
				schName.getStrokeList());
	}

	/**
	 * 
	 * @param inclStateSchemaName
	 *            concrete or abstract state schema
	 * @param schName
	 * @param beforeBindings
	 */
	protected void checkInclBindingsWithinGivenSchBindings(
			ZName inclStateSchemaName, ZName schName,
			SortedSet<Definition> beforeBindings) {
		assert inclStateSchemaName != null && schName != null;

		// check the given mixed bindings are indeed within the remit of the
		// state associated with it.
		SortedSet<Definition> stateBindings = computedBindings_
				.get(inclStateSchemaName);
		if (stateBindings == null || !beforeBindings.containsAll(stateBindings)) {
			final String message = "Included state schema "
					+ ZUtils.toStringZName(inclStateSchemaName)
					+ " depends on bindings not declared in schema "
					+ ZUtils.toStringZName(schName) + "\n\tGiven.....: "
					+ String.valueOf(beforeBindings) + "\n\tExpected..: "
					+ String.valueOf(stateBindings);
			handleInclBindingsMismatch(message);
		}
	}

	/**
	 * Just log a waning on the feasibility case. On refinement case throw an
	 * exception
	 * 
	 * @param errorMsg
	 */
	protected void handleInclBindingsMismatch(String errorMsg) {
		final String message = errorMsg
				+ "\n\n\tThis might be caused by inconsistent state. Ignoring for "
				+ getClass().getSimpleName();
		getLogger().warning(message);
	}

	private final DefinitionComparator definitionComparatorIgnoringStrokes_ = new DefinitionComparator(
			true);

	protected boolean bindingsSubsetEq(SortedSet<Definition> LHS,
			SortedSet<Definition> RHS, boolean dashed) {
		if (LHS.isEmpty())
			return true;
		else if (RHS.isEmpty())
			return false;
		else if (!dashed)
			return LHS.containsAll(RHS);
		else {
			// change the comparator to ignore strokes
			SortedSet<Definition> lhs = new TreeSet<Definition>(
					definitionComparatorIgnoringStrokes_);
			lhs.addAll(LHS);
			// if considering dashed bindings, then ignore dash for comparison
			for (Definition e : RHS)
				if (!lhs.contains(e))
					return false;
			return true;
		}
	}

	protected boolean bindingsRemoveAll(SortedSet<Definition> LHS,
			SortedSet<Definition> RHS, boolean dashed) {
		if (!dashed)
			return LHS.removeAll(RHS);
		else {
			// change the comparator to ignore strokes
			SortedSet<Definition> rhs = new TreeSet<Definition>(
					definitionComparatorIgnoringStrokes_);
			rhs.addAll(RHS);

			// if considering dashed bindings, then ignore dash for comparison
			boolean modified = false;
			Iterator<Definition> it = LHS.iterator();
			while (it.hasNext()) {
				if (rhs.contains(it.next())) {
					// affects the LHS from caller.
					it.remove();
					modified = true;
				}
			}
			it = null;
			return modified;
		}
	}
}
