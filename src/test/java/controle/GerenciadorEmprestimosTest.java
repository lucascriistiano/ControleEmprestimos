package controle;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import builder.GerenciadorClientesScenarioBuilder;
import dominio.Cliente;
import dominio.ComprovanteDevolucaoBuilder;
import dominio.ComprovanteEmprestimoBuilder;
import dominio.FabricaNotificacao;
import dominio.RegraEmprestimo;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import instanciahotel.ComprovanteDevolucaoBuilderHotel;
import instanciahotel.ComprovanteEmprestimoBuilderHotel;
import instanciahotel.FabricaNotificacaoHotel;
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

	private static GerenciadorClientes gerenciadorClientes;

	private static GerenciadorEmprestimos gerenciador;

	private GerenciadorClientesScenarioBuilder builderClientes;

	@Parameters
	public static Collection<Object[]> parameters() {
		return Arrays.asList(PARAMETROS_HOTEL, PARAMETROS_LOCADORA_VEICULOS);
	}

	public GerenciadorEmprestimosTest(RegraEmprestimo regra, ComprovanteEmprestimoBuilder emprestimo,
			ComprovanteDevolucaoBuilder devolucao, FabricaNotificacao notificacao) {
		gerenciador = new GerenciadorEmprestimos(regra, emprestimo, devolucao, notificacao);
	}

	public static void beforeClass() {
		gerenciadorClientes = new GerenciadorClientes();
	}

	@Before
	public void setUp() throws DataException, ClienteInvalidoException {
		gerenciadorClientes = new GerenciadorClientes();
		builderClientes = new GerenciadorClientesScenarioBuilder(gerenciadorClientes);

		for (int i = 0; i < QUANTIDADE_CLIENTES; i++) {
			builderClientes.criarClienteValido().cadastrarCliente();
		}
	}

	@Test(expected=ClienteInvalidoException.class)
	public void testPreconditionInvalid(){
		Cliente cliente = builderClientes.criarClienteInvalido().assertNotExists().getClienteInstance();
//		gerenciador.realizarEmprestimo(usuario, cliente, recursos);
	}
	
}
