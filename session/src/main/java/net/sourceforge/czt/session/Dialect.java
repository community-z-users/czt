package net.sourceforge.czt.session;

public enum Dialect {

   Z,				//0
   ZPATT,			//1
   OZ,				//2
   OZPATT,			//3
   ZEVES,			//4
   CIRCUSPATT,		//5
   CIRCUS,			//6
   CIRCUSTIME;		//7
   
   /**
    * Matrix where rows are for THIS enum in comparison to given dialect.
    * TODO: find a more compact (yet clear) way of describing this. Perhaps BitSet?
    */
   private static final boolean[][] EXTENSION_MATRIX = 
	   	{ //   0	  1		 2		3		4	  5		 6		7
	   		{ true, false, false, false, false, false, false, false }, //0
	   		{ true, true,  false, false, false, false, false, false }, //1
	   		{ true, true,  true,  false, false, false, false, false }, //2
	   		{ true, true,  true,  true,  false, false, false, false }, //3
	   		{ true, false, false, false, true,  false, false, false }, //4
	   		{ true, true,  false, false, false, true,  true,  false }, //5
	   		{ true, true,  false, false, false, false, true,  false }, //6
	   		{ true, true,  false, false, false, true,  true,  true  }  //7
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
