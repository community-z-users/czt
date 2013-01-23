package net.sourceforge.czt.session;

public enum Dialect {

   Z,
   ZPATT,
   OZ,
   OZPATT,
   ZEVES,
   CIRCUSPATT,
   CIRCUS,
   CIRCUSTIME;
   
   public String dialect()
   {
	   return name().toLowerCase();
   }   
}
