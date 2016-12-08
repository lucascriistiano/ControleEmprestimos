package controle;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import builder.GerenciadorRecursosScenarioBuilder;
import dao.DaoUsuarioMemoria;

public class GerenciadorRecursosTest {
	
	private static GerenciadorRecursos gerenciador;
	private GerenciadorRecursosScenarioBuilder builder;
	
	@BeforeClass
	public static void beforeClass(){
		gerenciador = new GerenciadorRecursos();
	}
	
	@Before
	public void before(){
		builder = new GerenciadorRecursosScenarioBuilder(gerenciador);
	}
		
	@After 
	public void tearDown(){
		DaoUsuarioMemoria.getInstance().clear();
	}

	@Test
	public void test(){
		
	}
	
}
