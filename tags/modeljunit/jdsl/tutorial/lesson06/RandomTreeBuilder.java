import jdsl.core.algo.traversals.*;
import jdsl.core.api.*;
import jdsl.core.ref.*;
import java.util.Random;

/**
 * Class that builds a random tree.  Each node stores a random 
 * name from a Sequence of names.
 *
 * @author Lucy Perry (lep)
 * @version JDSL 2
*/
public class RandomTreeBuilder { 

    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 

    //b6.1
    protected Tree tree;
    protected Sequence names;
    //e6.1
    
    /**
     *Builds a random tree.  The build method does the work.
     */
    //b6.2
    public Tree randomTree(int n) {
        // Create a random binary tree with n external nodes
        tree = new NodeTree();
        names = NameGenerator.getNames();
        build(tree.root(), n);  // auxiliary recursive method
        return tree;
    }
    //e6.2
    
    /**
     * Recursively build a random tree.  The algorithm builds a subtree with
     * n nodes with root node p as follows:
     *   - If n=1 then do nothing
     *   - Otherwise
     *       - randomly select the size of the subtree rooted at the first child
     *       - repeat until the number of nodes to build has been distributed to 
     *         children subtrees.
     *       - randomly permute the order of sizes.
     *       - recursively build each subtree
     */
    //b6.3 
    protected void build(Position p, int n) {
        int toBuild = n-1;
        Sequence sizes=new ArraySequence();
        if (tree.isExternal(p)) {
            while (toBuild>0) {
                int size = randomInteger(1, toBuild);
                sizes.insertLast(new Integer(size));
                toBuild-=size;
            }
            permute(sizes);
            for(int i=0; i<sizes.size();i++){
                Position pos = tree.insertLastChild(p,null);
                int size = ((Integer)sizes.atRank(i).element()).intValue();
                build(pos,size);
            }
            tree.replaceElement(p,pickName());
        }
    }
    //e6.3

    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
    protected Random gen = new Random();

    /**
     * Randomly permute a sequence.  This is the same method as in lesson 2.
     */
    protected void permute(Sequence s) {
        for(int i=s.size()-1;i>1;i--) {
            int j=randomInteger(1,i);
            if (j<i)
                s.swapElements(s.atRank(i),s.atRank(j));
        }
    }

    /**
     * Randomly pick a name. 
     */
    protected String pickName() {
        int i=randomInteger(0,names.size()-1);
        return (String)names.atRank(i).element();
    }

    /** 
     * Return a random integer i such that min <= i <= max
     */
    protected int randomInteger(int min, int max) {
        int r = gen.nextInt(max-min+1);
        return r+min;
    }
}
