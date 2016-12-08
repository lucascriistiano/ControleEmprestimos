package controle;

import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Date;

import org.junit.After;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import builder.GerenciadorClientesScenarioBuilder;
import builder.GerenciadorEmprestimosScenarioBuilder;
import builder.GerenciadorUsuariosScenarioBuilder;
import dao.DaoCliente;
import dao.DaoEmprestimo;
import dao.DaoUsuario;
import dominio.Cliente;
import dominio.ComprovanteEmprestimo;
import dominio.FabricaNotificacao;
import dominio.GeradorComprovante;
import dominio.Recurso;
import dominio.RegraEmprestimo;
import dominio.Usuario;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import excecao.EmprestimoInvalidoException;
import excecao.RecursoInvalidoException;
import excecao.UsuarioInvalidoException;
import instanciahotel.FabricaNotificacaoHotel;
import instanciahotel.GeradorComprovanteHotel;
import instanciahotel.Quarto;
import instanciahotel.RegraHotel;
import instancialocadoraveiculos.FabricaNotificacaoLocadoraVeiculos;
import instancialocadoraveiculos.GeradorComprovanteLocadoraVeiculos;
import instancialocadoraveiculos.RegraLocadoraVeiculos;
import util.GerenciadorDatas;

@RunWith(Parameterized.class)
public class VerificadorPrazosTest {

	private static final int QUANTIDADE_CLIENTES = 10;

	private static final Object[] PARAMETROS_HOTEL = new Object[] { new RegraHotel(), new GeradorComprovanteHotel(),
			new FabricaNotificacaoHotel() };

	private static final Object[] PARAMETROS_LOCADORA_VEICULOS = new Object[] { new RegraLocadoraVeiculos(),
			new GeradorComprovanteLocadoraVeiculos(), new FabricaNotificacaoLocadoraVeiculos() };

	private static GerenciadorUsuarios gerenciadorUsuarios;

	private static GerenciadorClientes gerenciadorClientes;

	private static GerenciadorEmprestimos gerenciadorEmprestimos;

	private static GerenciadorDatas gerenciadorDatas;

	private GerenciadorClientesScenarioBuilder builderClientes;

	private GerenciadorUsuariosScenarioBuilder builderUsuarios;

	private GerenciadorEmprestimosScenarioBuilder builderEmprestimos;

	private RegraEmprestimo regra;

	private GeradorComprovante geradorComprovante;

	private FabricaNotificacao notificacao;

	@Parameters
	public static Collection<Object[]> parameters() {
		Collection<Object[]> colecao = new ArrayList<>();
		colecao.add(PARAMETROS_HOTEL);
		return colecao;
	}

	/**
	 * Construtor que recebe os Parâmetros para os testes
	 */
	public VerificadorPrazosTest(RegraEmprestimo regra, GeradorComprovante geradorComprovante,
			FabricaNotificacao notificacao) {
		this.regra = regra;
		this.geradorComprovante = geradorComprovante;
		this.notificacao = notificacao;

		gerenciadorEmprestimos = new GerenciadorEmprestimos(regra, geradorComprovante, notificacao, gerenciadorDatas);
	}

	@BeforeClass
	public static void beforeClass() {
		gerenciadorUsuarios = new GerenciadorUsuarios();
		gerenciadorClientes = new GerenciadorClientes();
		gerenciadorDatas = new GerenciadorDatas();
	}

	@Before
	public void beforeTest() throws DataException, ClienteInvalidoException {
		gerenciadorClientes = new GerenciadorClientes();

		builderUsuarios = new GerenciadorUsuariosScenarioBuilder(gerenciadorUsuarios);
		builderClientes = new GerenciadorClientesScenarioBuilder(gerenciadorClientes);
		builderEmprestimos = new GerenciadorEmprestimosScenarioBuilder(gerenciadorEmprestimos);

		for (int i = 0; i < QUANTIDADE_CLIENTES; i++) {
			builderClientes.criarClienteValido().cadastrarCliente();
		}
	}

	@After
	public void afterTest() {
		DaoCliente.getInstance().clear();
		DaoUsuario.getInstance().clear();
		DaoEmprestimo.getInstance().clear();
	}

	@Test
	public void testVerificarEmprestimoExpiradoNormalBehavior() throws DataException, UsuarioInvalidoException,
			EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException {
		Cliente cliente = builderClientes.criarClienteValido().assertNotExists().getClienteInstance();
		Usuario usuario = builderUsuarios.criarUsuarioValido().cadastrarUsuario().assertExists().getUsuarioInstance();
		Recurso recurso = new Quarto("Quarto Pequeno", 1);
		ComprovanteEmprestimo comprovante = gerenciadorEmprestimos.realizarEmprestimo(usuario, cliente,
				Arrays.asList(recurso));

		GerenciadorDatas gerenciadorDatasModificado = mock(GerenciadorDatas.class);
		Calendar calendar = Calendar.getInstance();
		calendar.add(Calendar.DAY_OF_MONTH, 10);
		Date dataModificada = calendar.getTime();
		when(gerenciadorDatasModificado.getDataAtual()).thenReturn(dataModificada);

		VerificadorPrazos verificadorPrazos = new VerificadorPrazos(regra, notificacao, gerenciadorDatasModificado);

		assertTrue(verificadorPrazos.prazoExpirado(comprovante.getEmprestimo()));
	}

}
