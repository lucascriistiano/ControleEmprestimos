package junit;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

import org.jmlspecs.ajmlrac.runtime.JMLAssertionError;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import controle.GerenciadorClientes;
import dao.DaoClienteMemoria;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import instanciahotel.ClienteHotel;


public class TestGerenciadorClientes {
	
	private Cliente clienteValido;
	private Cliente clienteInvalido;
	
	@Before
	public void setUp() throws ParseException{
		long codigoCliente = 1L;
		SimpleDateFormat sdf = new SimpleDateFormat("dd/MM/yyyy");
		Date nascimento = sdf.parse("01/01/1998");
		clienteValido = new ClienteHotel(codigoCliente,"Roberto","123456789","123123","rua importante", nascimento);
		clienteInvalido = new ClienteHotel(2L, "","","","rua", new Date());
	}
	
	@After 
	public void tearDown(){
		
		/** Como é singleton precisa limpar os dados a cada teste */
		DaoClienteMemoria.getInstance().clear();

	}
	
	/**
	 * Teste deve lançar ClienteInvalidoException e não deve lançar Pós Condição.
	 * @throws DataException
	 * @throws ClienteInvalidoException
	 * @throws ParseException
	 */
	@Test(expected=ClienteInvalidoException.class)
	public void testPreconditionInvalid() throws DataException, ClienteInvalidoException, ParseException{
		GerenciadorClientes gerenciador = new GerenciadorClientes();
						
		try{
			gerenciador.cadastrarCliente(clienteInvalido);
		} catch (JMLAssertionError e){
			fail(e.toString());
		}

	}
	
	
	@Test
	public void testCadastrarClienteNormalBehavior() throws DataException, ClienteInvalidoException, ParseException{
		GerenciadorClientes gerenciador = new GerenciadorClientes();
				
		assertTrue("Cliente Não deve ser nulo",clienteValido != null);
		assertTrue("Cliente Deve ser Válido.",clienteValido.valido());
		assertFalse("Não deve existir esse cliente", gerenciador.exists(clienteValido.getCodigo()));
		
		gerenciador.cadastrarCliente(clienteValido);
		
		// Se alguma pós condição não for obedecida o teste falhará
		// Não é obrigado esse assertTrue		
		assertTrue("Deve existir o cliente",gerenciador.exists(clienteValido.getCodigo()));
	}
	
	@Test(expected=DataException.class)
	public void testCadastrarDataExceptionalBehavior() throws DataException, ClienteInvalidoException{
		GerenciadorClientes gerenciador = new GerenciadorClientes();
		
		assertTrue("Cliente Não deve ser nulo",clienteValido != null);
		assertTrue("Cliente Deve ser Válido.",clienteValido.valido());
		gerenciador.cadastrarCliente(clienteValido);
		assertTrue("Deve existir esse cliente", gerenciador.exists(clienteValido.getCodigo()));
		
		// Tenta cadastrar novamente - Throws DataException
		gerenciador.cadastrarCliente(clienteValido);
	}

}
