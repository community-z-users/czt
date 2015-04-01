package net.sourceforge.czt.session;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class DialectTest {

	/*
	Each test represent a row in the EXTENSION_MATRIX from Dialect.
   	*/
	
	@Test
	public void testZ() {
		assertTrue(Dialect.Z.isExtensionOf(Dialect.Z));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.ZPATT));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.ZEVES));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.CIRCUSPATT));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.Z.isExtensionOf(Dialect.CIRCUSTIME));
	}

	@Test
	public void testZPatt() {
		assertTrue(Dialect.ZPATT.isExtensionOf(Dialect.Z));
		assertTrue(Dialect.ZPATT.isExtensionOf(Dialect.ZPATT));
		assertFalse(Dialect.ZPATT.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.ZPATT.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.ZPATT.isExtensionOf(Dialect.ZEVES));
		assertFalse(Dialect.ZPATT.isExtensionOf(Dialect.CIRCUSPATT));
		assertFalse(Dialect.ZPATT.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.ZPATT.isExtensionOf(Dialect.CIRCUSTIME));
	}

	@Test
	public void testOZ() {
		assertTrue(Dialect.OZ.isExtensionOf(Dialect.Z));
		assertTrue(Dialect.OZ.isExtensionOf(Dialect.ZPATT));
		assertTrue(Dialect.OZ.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.OZ.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.OZ.isExtensionOf(Dialect.ZEVES));
		assertFalse(Dialect.OZ.isExtensionOf(Dialect.CIRCUSPATT));
		assertFalse(Dialect.OZ.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.OZ.isExtensionOf(Dialect.CIRCUSTIME));
	}
	
	@Test
	public void testOZPatt() {
		assertTrue(Dialect.OZPATT.isExtensionOf(Dialect.Z));
		assertTrue(Dialect.OZPATT.isExtensionOf(Dialect.ZPATT));
		assertTrue(Dialect.OZPATT.isExtensionOf(Dialect.OZ));
		assertTrue(Dialect.OZPATT.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.OZPATT.isExtensionOf(Dialect.ZEVES));
		assertFalse(Dialect.OZPATT.isExtensionOf(Dialect.CIRCUSPATT));
		assertFalse(Dialect.OZPATT.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.OZPATT.isExtensionOf(Dialect.CIRCUSTIME));
	}

	@Test
	public void testZEVES() {
		assertTrue(Dialect.ZEVES.isExtensionOf(Dialect.Z));
		assertFalse(Dialect.ZEVES.isExtensionOf(Dialect.ZPATT));
		assertFalse(Dialect.ZEVES.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.ZEVES.isExtensionOf(Dialect.OZPATT));
		assertTrue(Dialect.ZEVES.isExtensionOf(Dialect.ZEVES));
		assertFalse(Dialect.ZEVES.isExtensionOf(Dialect.CIRCUSPATT));
		assertFalse(Dialect.ZEVES.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.ZEVES.isExtensionOf(Dialect.CIRCUSTIME));
	}
	
	@Test
	public void testCircusPatt() {
		assertTrue(Dialect.CIRCUSPATT.isExtensionOf(Dialect.Z));
		assertTrue(Dialect.CIRCUSPATT.isExtensionOf(Dialect.ZPATT));
		assertFalse(Dialect.CIRCUSPATT.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.CIRCUSPATT.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.CIRCUSPATT.isExtensionOf(Dialect.ZEVES));
		assertTrue(Dialect.CIRCUSPATT.isExtensionOf(Dialect.CIRCUSPATT));
		assertTrue(Dialect.CIRCUSPATT.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.CIRCUSPATT.isExtensionOf(Dialect.CIRCUSTIME));
	}

	@Test
	public void testCircus() {
		assertTrue(Dialect.CIRCUS.isExtensionOf(Dialect.Z));
		assertTrue(Dialect.CIRCUS.isExtensionOf(Dialect.ZPATT));
		assertFalse(Dialect.CIRCUS.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.CIRCUS.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.CIRCUS.isExtensionOf(Dialect.ZEVES));
		assertFalse(Dialect.CIRCUS.isExtensionOf(Dialect.CIRCUSPATT));
		assertTrue(Dialect.CIRCUS.isExtensionOf(Dialect.CIRCUS));
		assertFalse(Dialect.CIRCUS.isExtensionOf(Dialect.CIRCUSTIME));
	}

	@Test
	public void testCircusTime() {
		assertTrue(Dialect.CIRCUSTIME.isExtensionOf(Dialect.Z));
		assertTrue(Dialect.CIRCUSTIME.isExtensionOf(Dialect.ZPATT));
		assertFalse(Dialect.CIRCUSTIME.isExtensionOf(Dialect.OZ));
		assertFalse(Dialect.CIRCUSTIME.isExtensionOf(Dialect.OZPATT));
		assertFalse(Dialect.CIRCUSTIME.isExtensionOf(Dialect.ZEVES));
		assertTrue(Dialect.CIRCUSTIME.isExtensionOf(Dialect.CIRCUSPATT));
		assertTrue(Dialect.CIRCUSTIME.isExtensionOf(Dialect.CIRCUS));
		assertTrue(Dialect.CIRCUSTIME.isExtensionOf(Dialect.CIRCUSTIME));
	}
	
	@Test
	public void testKnownDialects() {
		String[] exptected = new String[] { Dialect.Z.toString(), Dialect.ZPATT.toString(),
				 Dialect.OZ.toString(), Dialect.OZPATT.toString(),	
				 Dialect.ZEVES.toString(), Dialect.CIRCUSPATT.toString(),
				 Dialect.CIRCUS.toString(), Dialect.CIRCUSTIME.toString(),
				 Dialect.CIRCUSCONF.toString()
				 };
		assertArrayEquals("", exptected, Dialect.knownDialectsAsStringArray());
	}
	
	@Test
	public void testDialectFromString() {
		// don't use toString as it puts enum in lower-case
		Dialect s2 = Dialect.valueOf(Dialect.Z.name());
		Dialect s1 = Dialect.valueOf("Z");
		assertEquals(s1, s2);
	}
}
