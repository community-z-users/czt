package net.sourceforge.czt.session;

public enum Dialect {

   Z,				//0
   ZPATT,			//1
   OZ,				//2
   OZPATT,			//3
   ZEVES,			//4
   CIRCUSPATT,		//5
   CIRCUS,			//6
   CIRCUSTIME,		//7
   OHCIRCUS;		//8
   
   private static final int NUM_OF_DIALECTS = OHCIRCUS.ordinal()+1;
   
   private static String[] known_ = null;
   public static String[] knownDialectsAsStringArray()
   {
	   if (known_ == null)
	   {
		   int i = 0;
		   known_ = new String[NUM_OF_DIALECTS];
		   for(Dialect d : values())
		   {
			   known_[i] = d.toString();
			   i++;
		   }
	   }
	   assert known_ != null && known_.length == NUM_OF_DIALECTS;
	   return known_;
   }
   
   /**
    * Matrix where rows are for THIS enum in comparison to given dialect.
    * TODO: find a more compact (yet clear) way of describing this. Perhaps BitSet?
    */
   private static final boolean[][] EXTENSION_MATRIX = 
	   	{ //   0	  1		 2		3		4	  5		 6		7	  8
	   		{ true, false, false, false, false, false, false, false, false }, //0
	   		{ true, true,  false, false, false, false, false, false, false }, //1
	   		{ true, true,  true,  false, false, false, false, false, false }, //2
	   		{ true, true,  true,  true,  false, false, false, false, false }, //3
	   		{ true, false, false, false, true,  false, false, false, false }, //4
	   		{ true, true,  false, false, false, true,  true,  false, false }, //5
	   		{ true, true,  false, false, false, false, true,  false, false }, //6
	   		{ true, true,  false, false, false, true,  true,  true,  false }, //7
	   		{ true, true,  false, false, false, true,  true,  true,  true  }  //8
	   	};
   
   public boolean isExtensionOf(Dialect d)
   {
	   return d != null && EXTENSION_MATRIX[ordinal()][d.ordinal()];
   }
   
   public String toString()
   {
	   return name().toLowerCase();
   }
}
