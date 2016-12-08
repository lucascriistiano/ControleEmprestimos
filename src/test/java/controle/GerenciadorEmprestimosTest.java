package controle;

import org.junit.Before;
import org.junit.Test;

import builder.GerenciadorClientesScenarioBuilder;
import excecao.ClienteInvalidoException;
import excecao.DataException;

public class GerenciadorEmprestimosTest {
	
	private static final int QUANTIDADE_CLIENTES = 10;
	
	private static GerenciadorClientes gerenciadorClientes;
	
	private static GerenciadorEmprestimos gerenciador;
	
	private GerenciadorClientesScenarioBuilder builderClientes;
		
	public static void beforeClass(){
		gerenciadorClientes = new GerenciadorClientes();
	}
	
	@Before
	public void setUp() throws DataException, ClienteInvalidoException{
		gerenciadorClientes = new GerenciadorClientes();
		builderClientes = new GerenciadorClientesScenarioBuilder(gerenciadorClientes);
		
		for(int i = 0; i < QUANTIDADE_CLIENTES; i++){
			builderClientes.criarClienteValido().cadastrarCliente();
		}
	}
	
	@Test
	public void test(){
		
	}
	
	
	
	

}
