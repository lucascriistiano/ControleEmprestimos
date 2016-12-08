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

import builder.GerenciadorRecursosScenarioBuilder;
import dao.DaoRecurso;
import dominio.Recurso;
import excecao.DataException;
import excecao.RecursoInvalidoException;
import instanciahotel.Quarto;
import instancialocadoraveiculos.Carro;

@RunWith(Parameterized.class)
public class GerenciadorRecursosTest {
	
	private static GerenciadorRecursos gerenciador;
	private GerenciadorRecursosScenarioBuilder builder;
	private Class<Recurso> classeRecurso;
	
	@BeforeClass
	public static void beforeClass(){
		gerenciador = new GerenciadorRecursos();
	}
	
	@Before
	public void before(){
		builder = new GerenciadorRecursosScenarioBuilder(gerenciador, classeRecurso);
	}
		
	@After 
	public void tearDown(){
		DaoRecurso.getInstance().clear();
	}
	
	@Parameters
	public static Object[] parameters(){
		return new Object[] {Quarto.class, Carro.class};
	}
	
	public GerenciadorRecursosTest(Class<Recurso> classeRecurso){
		super();
		this.classeRecurso = classeRecurso;	
	}
		
	@Test(expected=RecursoInvalidoException.class)
	public void testPreconditionInvalid() throws DataException, RecursoInvalidoException {
		builder.criarRecursoInvalido()
				.cadastrarRecurso();
	}
	
	@Test
	public void testCadastrarRecursoNormalBehavior() throws DataException, RecursoInvalidoException {		
		builder.criarRecursoValido()
				.cadastrarRecurso()
				.assertExists();
	}
	
	@Test(expected=DataException.class)
	public void testCadastrarRecursoRepetidoExceptionalBehavior() throws DataException, RecursoInvalidoException{		
		builder.criarRecursoValido()
				.cadastrarRecurso()
				.assertExists()
				.cadastrarRecurso(); 
	}
	
	@Test
	public void testRemoverRecursoNormalBehavior() throws DataException, RecursoInvalidoException {				
		builder.criarRecursoValido()
				.cadastrarRecurso()
				.assertExists()
				.removerRecurso()
				.assertNotExists();
	}

	@Test(expected=DataException.class)
	public void testRemoverRecursoInexistenteExceptionalBehavior() throws DataException {				
		builder.criarRecursoValido()
				.assertNotExists()
				.removerRecurso();
	}
	
	@Test(expected=DataException.class)
	public void testRemoverRecursoIdInvalidoExceptionalBehavior() throws DataException {				
		builder.criarRecursoValido()
				.tornarCodigoInvalido()
				.assertNotExists()
				.removerRecurso();
	}

	@Test
	public void testAtualizarRecursoNormalBehavior() throws DataException, RecursoInvalidoException{		
		builder.criarRecursoValido()
				.cadastrarRecurso()
				.assertExists()
				.setDescricaoRecurso("RecursoImportante	" + new Random().nextInt())
				.atualizarRecurso();
	}
	
	@Test(expected=RecursoInvalidoException.class)
	public void testAtualizarRecursoInvalidoExceptionalBehavior() throws DataException, RecursoInvalidoException{	
		builder.criarRecursoValido()
				.cadastrarRecurso()
				.assertExists()
				.tornarRecursoInvalido()
				.atualizarRecurso();
	}
	
	@Test(expected=DataException.class)
	public void testAtualizarRecursoNaoCadastradoExceptionalBehavior() throws DataException, RecursoInvalidoException{
		builder.criarRecursoValido()
				.assertNotExists()
				.atualizarRecurso();
	}
		
	@Test
	public void testGetRecursoNormalBehavior() throws DataException, RecursoInvalidoException {			
		builder.criarRecursoValido()
				.assertCodigoValido()
				.cadastrarRecurso()
				.assertExists();
		
		Recurso clienteCadastrado = builder.getRecursoInstance();
		
		Recurso clienteBuscado = builder.getRecurso(clienteCadastrado.getCodigo()).getRecursoInstance();
		
		assertTrue("Recurso não deve ser nulo", clienteBuscado != null);
		assertTrue("Recurso deve ter Id igual ao consultado", clienteCadastrado.getCodigo() == clienteBuscado.getCodigo());
		
	}
	
	@Test(expected=DataException.class)
	public void testGetRecursoInexistenteExceptionalBehavior() throws DataException {	
		builder.criarRecursoValido()
				.assertCodigoValido()
				.assertNotExists()
				.getRecurso(builder.getRecursoInstance().getCodigo()); // Tenta buscar um cliente que Não existe
	}
	
	@Test(expected=DataException.class)
	public void testGetRecursoIdInvalidoExceptionalBehavior() throws DataException {
		builder.criarRecursoValido().tornarCodigoInvalido().assertNotExists().getRecurso();
	}
		
	public void testListarRecursosListaVaziaNormalBehavior() throws DataException {		
		List<Recurso> clientes = gerenciador.listarRecursos();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertTrue("Lista deve estar vazia", clientes.isEmpty());
	}
	
	public void testListarRecursosNormalBehavior() throws DataException, RecursoInvalidoException {	
		builder.criarRecursoValido()
				.assertNotExists()
				.cadastrarRecurso()
				.assertExists();
		
		Recurso clienteCadastrado = builder.getRecursoInstance();
		
		List<Recurso> clientes = gerenciador.listarRecursos();
		assertFalse("Lista não deve ser nula", clientes == null);
		assertFalse("Lista não deve ser vazia", clientes.isEmpty());
		assertTrue("Lista deve ter 1 item", clientes.size() == 1);
		assertTrue("Lista deve ter o cliente inserido", clientes.get(0).getCodigo() == clienteCadastrado.getCodigo());
	}
	
	public void testExistsIdsInvalidosNormalBehavior() throws DataException {		
		builder.criarRecursoValido().setCodigo(-5L).assertNotExists();
		builder.criarRecursoValido().setCodigo(0L).assertNotExists();
		builder.criarRecursoValido().setCodigo(2L).assertNotExists();
	}
	
	public void testExistsIdsValidosNormalBehavior() throws DataException, RecursoInvalidoException {	
		builder.criarRecursoValido()
				.cadastrarRecurso()
				.assertExists();
	}
	
}
