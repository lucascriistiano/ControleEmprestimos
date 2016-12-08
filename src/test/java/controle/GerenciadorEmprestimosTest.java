package controle;

import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import builder.GerenciadorClientesScenarioBuilder;
import builder.GerenciadorUsuariosScenarioBuilder;
import dao.DaoClienteMemoria;
import dao.DaoEmprestimoMemoria;
import dao.DaoUsuarioMemoria;
import dominio.Cliente;
import dominio.ComprovanteDevolucaoBuilder;
import dominio.ComprovanteEmprestimoBuilder;
import dominio.FabricaNotificacao;
import dominio.Recurso;
import dominio.RegraEmprestimo;
import dominio.Usuario;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import excecao.EmprestimoInvalidoException;
import excecao.RecursoInvalidoException;
import excecao.UsuarioInvalidoException;
import instanciahotel.ComprovanteDevolucaoBuilderHotel;
import instanciahotel.ComprovanteEmprestimoBuilderHotel;
import instanciahotel.FabricaNotificacaoHotel;
import instanciahotel.Quarto;
import instanciahotel.RegraHotel;
import instancialocadoraveiculos.ComprovanteDevolucaoBuilderLocadoraVeiculos;
import instancialocadoraveiculos.ComprovanteEmprestimoBuilderLocadoraVeiculos;
import instancialocadoraveiculos.FabricaNotificacaoLocadoraVeiculos;
import instancialocadoraveiculos.RegraLocadoraVeiculos;

@RunWith(Parameterized.class)
public class GerenciadorEmprestimosTest {

	private static final int QUANTIDADE_CLIENTES = 10;

	private static final Object[] PARAMETROS_HOTEL = new Object[] { new RegraHotel(),
			new ComprovanteEmprestimoBuilderHotel(), new ComprovanteDevolucaoBuilderHotel(),
			new FabricaNotificacaoHotel() };

	private static final Object[] PARAMETROS_LOCADORA_VEICULOS = new Object[] { new RegraLocadoraVeiculos(),
			new ComprovanteEmprestimoBuilderLocadoraVeiculos(), new ComprovanteDevolucaoBuilderLocadoraVeiculos(),
			new FabricaNotificacaoLocadoraVeiculos() };

	private static GerenciadorUsuarios gerenciadorUsuarios;
	
	private static GerenciadorClientes gerenciadorClientes;

	private static GerenciadorEmprestimos gerenciador;

	private GerenciadorClientesScenarioBuilder builderClientes;
	
	private GerenciadorUsuariosScenarioBuilder builderUsuarios;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		return Arrays.asList(PARAMETROS_HOTEL, PARAMETROS_LOCADORA_VEICULOS);
	}
	
	/** 
	 * Construtor que recebe os Parâmetros para os testes
	 */
	public GerenciadorEmprestimosTest(RegraEmprestimo regra, ComprovanteEmprestimoBuilder emprestimo,
			ComprovanteDevolucaoBuilder devolucao, FabricaNotificacao notificacao) {
		gerenciador = new GerenciadorEmprestimos(regra, emprestimo, devolucao, notificacao);
	}
	
	@BeforeClass
	public static void beforeClass() {
		gerenciadorUsuarios = new GerenciadorUsuarios();
		gerenciadorClientes = new GerenciadorClientes();
	}
	
	@Before
	public void beforeTest() throws DataException, ClienteInvalidoException {
		gerenciadorClientes = new GerenciadorClientes();
		
		builderUsuarios = new GerenciadorUsuariosScenarioBuilder(gerenciadorUsuarios);
		builderClientes = new GerenciadorClientesScenarioBuilder(gerenciadorClientes);

		for (int i = 0; i < QUANTIDADE_CLIENTES; i++) {
			builderClientes.criarClienteValido().cadastrarCliente();
		}
	}
	
	@After 
	public void afterTest(){
		DaoClienteMemoria.getInstance().clear();
		DaoUsuarioMemoria.getInstance().clear();
		DaoEmprestimoMemoria.getInstance().clear();
	}

	@Test(expected=UsuarioInvalidoException.class)
	public void testPreconditionUsuarioInvalido() throws DataException, UsuarioInvalidoException, EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException{
		Cliente cliente = builderClientes.criarClienteValido().getClienteInstance();
		Usuario usuario = builderUsuarios.criarUsuarioInvalido().getUsuarioInstance();
		
		Recurso recurso = new Quarto(1L, "Quarto Pequeno", 1);
		
		gerenciador.realizarEmprestimo(usuario, cliente, Arrays.asList(recurso));
	}
	
	@Test(expected=ClienteInvalidoException.class)
	public void testPreconditionClienteInvalido() throws DataException, UsuarioInvalidoException, EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException{
		Cliente cliente = builderClientes.criarClienteInvalido().getClienteInstance();
		Usuario usuario = builderUsuarios.criarUsuarioValido().getUsuarioInstance();
		
		Recurso recurso = new Quarto(1L, "Quarto Pequeno", 1);
		
		gerenciador.realizarEmprestimo(usuario, cliente, Arrays.asList(recurso));
	}
	
	@Test
	public void testCadastrarEmprestimoNormalBehavior() throws DataException, UsuarioInvalidoException, EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException{
		Cliente cliente = builderClientes.criarClienteValido().assertNotExists().getClienteInstance();
		Usuario usuario = builderUsuarios.criarUsuarioValido().cadastrarUsuario().assertExists().getUsuarioInstance();
		
		Recurso recurso = new Quarto(1L, "Quarto Pequeno", 1);
		
		gerenciador.realizarEmprestimo(usuario, cliente,  Arrays.asList(recurso));
	}
}
