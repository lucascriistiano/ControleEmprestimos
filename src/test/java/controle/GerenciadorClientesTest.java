package controle;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Random;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import builder.GerenciadorClientesScenarioBuilder;
import dao.DaoCliente;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import instanciahotel.ClienteHotel;
import instancialocadoraveiculos.ClienteLocadoraVeiculos;

@RunWith(Parameterized.class)
public class GerenciadorClientesTest {
	
	private Class<Cliente> classeTest;
	private static GerenciadorClientes gerenciador;
	private GerenciadorClientesScenarioBuilder builder;
	
	@BeforeClass
	public static void beforeClass(){
		gerenciador = new GerenciadorClientes();
	}
	
	@Before
	public void before(){
		builder = new GerenciadorClientesScenarioBuilder(gerenciador, classeTest);
	}
		
	@After 
	public void tearDown(){
		DaoCliente.getInstance().clear();
	}
	
	@Parameters
	public static Object[] parameters(){
		return new Object[] {ClienteHotel.class, ClienteLocadoraVeiculos.class};
	}
	
	
	public GerenciadorClientesTest(Class<Cliente> classeTest) {
		super();
		this.classeTest = classeTest;
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
				.cadastrarCliente(); 
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
		builder.criarClienteValido()
				.tornarCodigoInvalido()
				.assertNotExists()
				.removerCliente();
	}

	@Test
	public void testAtualizarClienteNormalBehavior() throws DataException, ClienteInvalidoException{		
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists()
				.setNomeCliente("Maria" + new Random().nextInt())
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
		builder.criarClienteValido().tornarCodigoInvalido().assertNotExists().getCliente();
	}
		
	@Test
	public void testListarClientesListaVaziaNormalBehavior() throws DataException {		
		List<Cliente> clientes = gerenciador.listarClientes();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertTrue("Lista deve estar vazia", clientes.isEmpty());
	}
	
	@Test
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
	
	@Test
	public void testExistsIdsInvalidosNormalBehavior() throws DataException {		
		builder.criarClienteValido().setCodigo(-5L).assertNotExists();
		builder.criarClienteValido().setCodigo(0L).assertNotExists();
		builder.criarClienteValido().setCodigo(2L).assertNotExists();
	}
	
	@Test
	public void testExistsIdsValidosNormalBehavior() throws DataException, ClienteInvalidoException {	
		builder.criarClienteValido()
				.cadastrarCliente()
				.assertExists();
	}

}
