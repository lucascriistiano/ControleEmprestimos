package controle;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;
import java.util.Random;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import builder.GerenciadorUsuariosScenarioBuilder;
import dao.DaoUsuario;
import dominio.Usuario;
import excecao.UsuarioInvalidoException;
import excecao.DataException;

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
		DaoUsuario.getInstance().clear();
	}
	
	@Test(expected=UsuarioInvalidoException.class)
	public void testPreconditionInvalid() throws DataException, UsuarioInvalidoException {
		builder.criarUsuarioInvalido()
				.cadastrarUsuario();
	}
	
	@Test
	public void testCadastrarUsuarioNormalBehavior() throws DataException, UsuarioInvalidoException {		
		builder.criarUsuarioValido()
				.cadastrarUsuario()
				.assertExists();
	}
	
	@Test(expected=UsuarioInvalidoException.class)
	public void testCadastrarUsuarioRepetidoExceptionalBehavior() throws DataException, UsuarioInvalidoException{		
		builder.criarUsuarioValido()
				.cadastrarUsuario()
				.assertExists()
				.cadastrarUsuario(); 
	}
	
	@Test
	public void testRemoverUsuarioNormalBehavior() throws DataException, UsuarioInvalidoException {				
		builder.criarUsuarioValido()
				.cadastrarUsuario()
				.assertExists()
				.removerUsuario()
				.assertNotExists();
	}

	@Test(expected=DataException.class)
	public void testRemoverUsuarioInexistenteExceptionalBehavior() throws DataException {				
		builder.criarUsuarioValido()
				.assertNotExists()
				.removerUsuario();
	}
	
	@Test(expected=DataException.class)
	public void testRemoverUsuarioIdInvalidoExceptionalBehavior() throws DataException {				
		builder.criarUsuarioValido()
				.tornarCodigoInvalido()
				.assertNotExists()
				.removerUsuario();
	}

	@Test
	public void testAtualizarUsuarioNormalBehavior() throws DataException, UsuarioInvalidoException{		
		builder.criarUsuarioValido()
				.cadastrarUsuario()
				.assertExists()
				.setNomeUsuario("Maria" + new Random().nextInt())
				.atualizarUsuario();
	}
	
	@Test(expected=UsuarioInvalidoException.class)
	public void testAtualizarUsuarioInvalidoExceptionalBehavior() throws DataException, UsuarioInvalidoException{	
		builder.criarUsuarioValido()
				.cadastrarUsuario()
				.assertExists()
				.tornarUsuarioInvalido()
				.atualizarUsuario();
	}
	
	@Test(expected=DataException.class)
	public void testAtualizarUsuarioNaoCadastradoExceptionalBehavior() throws DataException, UsuarioInvalidoException{
		builder.criarUsuarioValido()
				.assertNotExists()
				.atualizarUsuario();
	}
		
	@Test
	public void testGetUsuarioNormalBehavior() throws DataException, UsuarioInvalidoException {			
		builder.criarUsuarioValido()
				.assertCodigoValido()
				.cadastrarUsuario()
				.assertExists();
		
		Usuario clienteCadastrado = builder.getUsuarioInstance();
		
		Usuario clienteBuscado = builder.getUsuario(clienteCadastrado.getCodigo()).getUsuarioInstance();
		
		assertTrue("Usuario não deve ser nulo", clienteBuscado != null);
		assertTrue("Usuario deve ter Id igual ao consultado", clienteCadastrado.getCodigo() == clienteBuscado.getCodigo());
		
	}
	
	@Test(expected=DataException.class)
	public void testGetUsuarioInexistenteExceptionalBehavior() throws DataException {	
		builder.criarUsuarioValido()
				.assertCodigoValido()
				.assertNotExists()
				.getUsuario(builder.getUsuarioInstance().getCodigo()); // Tenta buscar um cliente que Não existe
	}
	
	@Test(expected=DataException.class)
	public void testGetUsuarioIdInvalidoExceptionalBehavior() throws DataException {
		builder.criarUsuarioValido().tornarCodigoInvalido().assertNotExists().getUsuario();
	}
		
	public void testListarUsuariosListaVaziaNormalBehavior() throws DataException {		
		List<Usuario> clientes = gerenciador.listarUsuarios();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertTrue("Lista deve estar vazia", clientes.isEmpty());
	}
	
	public void testListarUsuariosNormalBehavior() throws DataException, UsuarioInvalidoException {	
		builder.criarUsuarioValido()
				.assertNotExists()
				.cadastrarUsuario()
				.assertExists();
		
		Usuario clienteCadastrado = builder.getUsuarioInstance();
		
		List<Usuario> clientes = gerenciador.listarUsuarios();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertFalse("Lista não deve ser vazia", clientes.isEmpty());
		assertTrue("Lista deve ter 1 item", clientes.size() == 1);
		assertTrue("Lista deve ter o cliente inserido", clientes.get(0).getCodigo() == clienteCadastrado.getCodigo());
	}
	
	public void testExistsIdsInvalidosNormalBehavior() throws DataException {		
		builder.criarUsuarioValido().setCodigo(-5L).assertNotExists();
		builder.criarUsuarioValido().setCodigo(0L).assertNotExists();
		builder.criarUsuarioValido().setCodigo(2L).assertNotExists();
	}
	
	public void testExistsIdsValidosNormalBehavior() throws DataException, UsuarioInvalidoException {	
		builder.criarUsuarioValido()
				.cadastrarUsuario()
				.assertExists();
	}
	
}
