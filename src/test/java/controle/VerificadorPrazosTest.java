package controle;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Date;

import org.junit.After;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import builder.GerenciadorClientesScenarioBuilder;
import builder.GerenciadorRecursosScenarioBuilder;
import builder.GerenciadorUsuariosScenarioBuilder;
import dao.DaoCliente;
import dao.DaoEmprestimo;
import dao.DaoUsuario;
import dominio.Cliente;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
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
import instanciahotel.ClienteHotel;
import instanciahotel.FabricaNotificacaoHotel;
import instanciahotel.GeradorComprovanteHotel;
import instanciahotel.Quarto;
import instanciahotel.RegraHotel;
import instancialocadoraveiculos.Carro;
import instancialocadoraveiculos.ClienteLocadoraVeiculos;
import instancialocadoraveiculos.FabricaNotificacaoLocadoraVeiculos;
import instancialocadoraveiculos.GeradorComprovanteLocadoraVeiculos;
import instancialocadoraveiculos.RegraLocadoraVeiculos;
import util.GerenciadorDatas;

@RunWith(Parameterized.class)
public class VerificadorPrazosTest {

	private static final Object[] PARAMETROS_HOTEL = new Object[] { new RegraHotel(), new GeradorComprovanteHotel(),
			new FabricaNotificacaoHotel(), Quarto.class, ClienteHotel.class };

	private static final Object[] PARAMETROS_LOCADORA_VEICULOS = new Object[] { new RegraLocadoraVeiculos(),
			new GeradorComprovanteLocadoraVeiculos(), new FabricaNotificacaoLocadoraVeiculos(), Carro.class, ClienteLocadoraVeiculos.class };

	private GerenciadorDatas gerenciadorDatasNaoModificado;
	private RegraEmprestimo regra;
	private FabricaNotificacao notificacao;
	
	private Emprestimo emprestimo;

	@Parameters
	public static Collection<Object[]> parameters() {
		return Arrays.asList(PARAMETROS_HOTEL, PARAMETROS_LOCADORA_VEICULOS);
	}

	public VerificadorPrazosTest(RegraEmprestimo regra, GeradorComprovante geradorComprovante,
			FabricaNotificacao notificacao, Class<Recurso> classeRecurso, Class<Cliente> classeCliente) throws DataException, UsuarioInvalidoException, EmprestimoInvalidoException, ClienteInvalidoException, RecursoInvalidoException {
		this.gerenciadorDatasNaoModificado = new GerenciadorDatas();
		this.regra = regra;
		this.notificacao = notificacao;
		
		GerenciadorUsuarios gerenciadorUsuarios = new GerenciadorUsuarios();
		GerenciadorClientes gerenciadorClientes = new GerenciadorClientes();
		GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
		
		GerenciadorUsuariosScenarioBuilder builderUsuarios = new GerenciadorUsuariosScenarioBuilder(gerenciadorUsuarios);
		GerenciadorClientesScenarioBuilder builderClientes = new GerenciadorClientesScenarioBuilder(gerenciadorClientes,classeCliente);
		GerenciadorRecursosScenarioBuilder builderRecursos = new GerenciadorRecursosScenarioBuilder(gerenciadorRecursos, classeRecurso);
		
		Cliente cliente = builderClientes.criarClienteValido().assertNotExists().getClienteInstance();
		Usuario usuario = builderUsuarios.criarUsuarioValido().cadastrarUsuario().assertExists().getUsuarioInstance();
		Recurso recurso = builderRecursos.criarRecursoValido().getRecursoInstance();
	
		GerenciadorEmprestimos gerenciadorEmprestimos = new GerenciadorEmprestimos(regra, geradorComprovante, notificacao, gerenciadorDatasNaoModificado);
		ComprovanteEmprestimo comprovante = gerenciadorEmprestimos.realizarEmprestimo(usuario, cliente, Arrays.asList(recurso));
		this.emprestimo = comprovante.getEmprestimo();
	}

	@After
	public void afterTest() {
		DaoCliente.getInstance().clear();
		DaoUsuario.getInstance().clear();
		DaoEmprestimo.getInstance().clear();
	}

	@Test
	public void testVerificarEmprestimoNaoExpiradoNormalBehavior() {
		VerificadorPrazos verificadorPrazos = new VerificadorPrazos(regra, notificacao, gerenciadorDatasNaoModificado);
		assertFalse(verificadorPrazos.prazoExpirado(emprestimo));
	}
	
	@Test
	public void testVerificarEmprestimoExpiradoNormalBehavior() {
		VerificadorPrazos verificadorPrazos = new VerificadorPrazos(regra, notificacao, criarGerenciadorDatasComAvanco(10));
		assertTrue(verificadorPrazos.prazoExpirado(emprestimo));
	}
	
	@Test
	public void testVerificarEmprestimoPrazoProximoNormalBehavior() {
		VerificadorPrazos verificadorPrazos = new VerificadorPrazos(regra, notificacao, criarGerenciadorDatasComAvanco(-1));
		assertTrue(verificadorPrazos.prazoProximo(emprestimo));
	}
	
	private GerenciadorDatas criarGerenciadorDatasComAvanco(int dias) {
		GerenciadorDatas gerenciadorDatasModificado = mock(GerenciadorDatas.class);
		
		Calendar calendar = Calendar.getInstance();
		calendar.add(Calendar.DAY_OF_MONTH, dias);
		Date dataModificada = calendar.getTime();
		when(gerenciadorDatasModificado.getDataAtual()).thenReturn(dataModificada);
		
		return gerenciadorDatasModificado;
	}

}
