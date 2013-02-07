package net.sourceforge.czt.vcg.z;

import java.util.List;

import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.z.ast.ZName;

/**
 * <p>
 * VCG contextual information to be used by various VC generation tools.
 * It includes meta-information about how state and operations are split 
 * or combined together. 
 * </p>
 * <p>
 * For instance, on feasibility VCs we get a meta schema like
 * \begin{schema}{SpecProperties1}
 * 	  state: MyStateSchema
 * 	  init : MyStateInitSchema
 *    opN  : MyOpNSchema
 * \end{schema}
 * When asking the context for the operation type, for opN, it would return
 * a SchemaType for MyOpNSchema (i.e. its maximal type signature), whereas 
 * the bindings would return the declared names/types for the corresponding name.
 * This includes the state and init schemas. Similarly, we could have more
 * complex arrangements for refinement (i.e. ProdType and Pair of set of bindings).
 * \begin{schema}{REFSpecProperties}
 * 	  abs : SpecProperties1
 *    con : SpecProperties2
 *    opN : MyOpNSchema \cross MyConcreteOpNSchema
 * \end{schema}
 * where there is an implicit check that all operations involved at top-level
 * are declared in each abs/con meta-model. This way, we ensure that those operations
 * with refinement VC context will have FSB VC context set up properly as well.
 * </p>
 * @author Leo Freitas
 *
 * @param <T> some subtype of Type2, perhaps Type2 directly...? TODO
 * @param <B> kind of bindinds to consider 
 */
public interface VCGContext<T, B> 
{
	/**
	 * Get the ZName for the state schema considered under this VCG context
	 * @return
	 */
	ZName getStateName();

	/**
	 * Get the ZName for the state initialisation schema considered under this VCG context
	 * @return
	 */
	ZName getInitName();
	
	/**
	 * For a given schema name representing an operation over the state schema, 
	 * return the 
	 * @param operationName
	 * @return
	 */
	T getOpType(ZName operationName);
	B getOpBindings(ZName operationName);
	
	List<? extends InfoTable> getInfoTables();
}
