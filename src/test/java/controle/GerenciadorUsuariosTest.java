package controle;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import builder.GerenciadorUsuariosScenarioBuilder;
import dao.DaoUsuarioMemoria;

public class GerenciadorUsuariosTest {

	private static GerenciadorUsuarios gerenciador;
	private GerenciadorUsuariosScenarioBuilder builder;
	
	@BeforeClass
	public static void beforeClass(){
		gerenciador = new GerenciadorUsuarios();
	}
	
	@Before
	public void before(){
		builder = new GerenciadorUsuariosScenarioBuilder(gerenciador);
	}
		
	@After 
	public void tearDown(){
		DaoUsuarioMemoria.getInstance().clear();
	}
	
	@Test
	public void test(){
		
	}
	
}
