package controle;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import dao.DaoClienteMemoria;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;


public class GerenciadorClientesTest {
	
	private static GerenciadorClientes gerenciador;
	private GerenciadorClientesScenarioBuilder builder;
	
	@BeforeClass
	public static void beforeClass(){
		gerenciador = new GerenciadorClientes();
	}
	
	@Before
	public void before(){
		builder = new GerenciadorClientesScenarioBuilder(gerenciador);
	}
		
	@After 
	public void tearDown(){
		DaoClienteMemoria.getInstance().clear();
	}
	
	@Test(expected=ClienteInvalidoException.class)
	public void testPreconditionInvalid() throws DataException, ClienteInvalidoException {
		builder.criarClienteInvalido()
				.cadastrarCliente();
	}
	
	@Test
	public void testCadastrarClienteNormalBehavior() throws DataException, ClienteInvalidoException {		
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists();
	}
	
	@Test(expected=DataException.class)
	public void testCadastrarClienteRepetidoExceptionalBehavior() throws DataException, ClienteInvalidoException{		
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists()
				.cadastrarCliente(); // Cadastra um cliente que já existe
	}
	
	@Test
	public void testRemoverClienteNormalBehavior() throws DataException, ClienteInvalidoException {				
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists()
				.removerCliente()
				.assertNotExists();
	}

	@Test(expected=DataException.class)
	public void testRemoverClienteInexistenteExceptionalBehavior() throws DataException {				
		builder.criarClienteValido()
				.assertNotExists()
				.removerCliente();
	}
	
	@Test(expected=DataException.class)
	public void testRemoverClienteIdInvalidoExceptionalBehavior() throws DataException {				
		//Id <= 0 verifica uma condição especial da verificação e do exists()
		builder.criarClienteValido()
				.setCodigoInvalido()
				.assertNotExists()
				.removerCliente();
	}

	@Test
	public void testAtualizarClienteNormalBehavior() throws DataException, ClienteInvalidoException{		
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists()
				.setNomeCliente("Maria")
				.atualizarCliente();
	}
	
	@Test(expected=ClienteInvalidoException.class)
	public void testAtualizarClienteInvalidoExceptionalBehavior() throws DataException, ClienteInvalidoException{	
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists()
				.tornarClienteInvalido()
				.atualizarCliente();
	}
	
	@Test(expected=DataException.class)
	public void testAtualizarClienteNaoCadastradoExceptionalBehavior() throws DataException, ClienteInvalidoException{
		builder.criarClienteValido()
				.assertNotExists()
				.atualizarCliente();
	}
	
	/** TESTES GET */
	
	@Test
	public void testGetClienteNormalBehavior() throws DataException, ClienteInvalidoException {			
		builder.criarClienteValido()
				.assertCodigoValido()
				.cadastrarCliente()
				.assertExists();
		
		Cliente clienteCadastrado = builder.getClienteInstance();
		
		Cliente clienteBuscado = builder.getCliente(clienteCadastrado.getCodigo()).getClienteInstance();
		
		assertTrue("Cliente não deve ser nulo", clienteBuscado != null);
		assertTrue("Cliente deve ter Id igual ao consultado", clienteCadastrado.getCodigo() == clienteBuscado.getCodigo());
		
	}
	
	@Test(expected=DataException.class)
	public void testGetClienteInexistenteExceptionalBehavior() throws DataException {	
		builder.criarClienteValido()
				.assertCodigoValido()
				.assertNotExists()
				.getCliente(builder.getClienteInstance().getCodigo()); // Tenta buscar um cliente que Não existe
	}
	
	@Test(expected=DataException.class)
	public void testGetClienteIdInvalidoExceptionalBehavior() throws DataException {
		//Id <= 0 verifica uma condição especial da verificação e do exists()
		builder.criarClienteValido().tornarCodigoInvalido().assertNotExists().getCliente();
	}
	
	/** TESTES LISTAR */
	
	public void testListarClientesListaVaziaNormalBehavior() throws DataException {		
		List<Cliente> clientes = gerenciador.listarClientes();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertTrue("Lista deve estar vazia", clientes.isEmpty());
	}
	
	public void testListarClientesNormalBehavior() throws DataException, ClienteInvalidoException {	
		
		builder.criarClienteValido()
				.assertNotExists()
				.cadastrarCliente()
				.assertExists();
		
		Cliente clienteCadastrado = builder.getClienteInstance();
		
		List<Cliente> clientes = gerenciador.listarClientes();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertFalse("Lista não deve ser vazia", clientes.isEmpty());
		assertTrue("Lista deve ter 1 item", clientes.size() == 1);
		assertTrue("Lista deve ter o cliente inserido", clientes.get(0).getCodigo() == clienteCadastrado.getCodigo());
	}
	
	/** TESTES EXISTS */
	
	public void testExistsIdsInvalidosNormalBehavior() {		
		builder.criarClienteValido().setCodigo(-5L).assertNotExists();
		builder.criarClienteValido().setCodigo(0L).assertNotExists();
		builder.criarClienteValido().setCodigo(2L).assertNotExists();
	}
	
	public void testExistsIdsValidosNormalBehavior() throws DataException, ClienteInvalidoException {	
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists();
	}

}
