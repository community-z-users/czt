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
   CIRCUSCONF;		//8
   
   private static final int NUM_OF_DIALECTS = CIRCUSCONF.ordinal()+1;
   
   private static final class LazyKnownDialectsLoader {
	   private final static String[] INSTANCE = loadKnownDialects();
	   
	   private static final String[] loadKnownDialects()
	   {
		   int i = 0;
		   String[] result = new String[NUM_OF_DIALECTS];
		   for(Dialect d : values())
		   {
			   result[i] = d.toString();
			   i++;
		   }
		   return result;
	   }
   }
   
   public static String[] knownDialectsAsStringArray()
   {
	   return LazyKnownDialectsLoader.INSTANCE;
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
	   		{ true, true,  false, false, false, true,  true,  true , false },  //7
	   		{ true, true,  false, false, false, true,  true,  false, true }  //8
	   	};
   
   public boolean isExtensionOf(Dialect d)
   {
	   return d != null && EXTENSION_MATRIX[ordinal()][d.ordinal()];
   }
   
   @Override
public String toString()
   {
	   return name().toLowerCase();
   }
}
