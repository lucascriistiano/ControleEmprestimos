package junit;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.text.ParseException;
import java.util.Calendar;
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
	
	private GerenciadorClientes gerenciador;
	private Cliente clienteValido;
	private Cliente clienteInvalido;
	
	@Before
	public void setUp() throws ParseException{
		gerenciador = new GerenciadorClientes();
		clienteValido = createClienteHotel(1L, "Roberto", "12345678900", "123123", "Rua importante", 1, 1, 1998);
		clienteInvalido = createClienteHotel(2L, "", "", "", "Rua", new Date());
	}
	
	private Cliente createClienteHotel(long codigo, String nome, String cpf, String rg, String endereco, int dia, int mes, int ano) {
		Calendar dataNascimento = Calendar.getInstance();
		dataNascimento.set(Calendar.DAY_OF_MONTH, dia);
		dataNascimento.set(Calendar.MONTH, mes-1);
		dataNascimento.set(Calendar.YEAR, ano);
		return createClienteHotel(codigo, nome, cpf, rg, endereco, dataNascimento.getTime());
	}
	
	private Cliente createClienteHotel(long codigo, String nome, String cpf, String rg, String endereco, Date nascimento) {
		return new ClienteHotel(codigo, nome, cpf, rg, endereco, nascimento);
	}
	
	@After 
	public void tearDown(){
		//Como é singleton precisa limpar os dados a cada teste
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
		try{
			gerenciador.cadastrarCliente(clienteInvalido);
		} catch (JMLAssertionError e){
			fail(e.toString());
		}
	}
	
	@Test
	public void testCadastrarClienteNormalBehavior() throws DataException, ClienteInvalidoException, ParseException{				
		assertTrue("Cliente não deve ser nulo", clienteValido != null);
		assertTrue("Cliente deve ser válido", clienteValido.valido());
		assertFalse("Cliente não deve já estar cadastrado", gerenciador.exists(clienteValido.getCodigo()));
		
		gerenciador.cadastrarCliente(clienteValido); // Se alguma pós condição não for obedecida o teste falhará
			
		assertTrue("Deve existir o cliente", gerenciador.exists(clienteValido.getCodigo()));
	}
	
	@Test(expected=DataException.class)
	public void testCadastrarClienteRepetidoExceptionalBehavior() throws DataException, ClienteInvalidoException{		
		assertTrue("Cliente não deve ser nulo", clienteValido != null);
		assertTrue("Cliente deve ser válido", clienteValido.valido());
		assertFalse("Cliente não deve já estar cadastrado", gerenciador.exists(clienteValido.getCodigo()));
		
		gerenciador.cadastrarCliente(clienteValido);
		
		assertTrue("Cliente deve estar cadastrado", gerenciador.exists(clienteValido.getCodigo()));
		
		gerenciador.cadastrarCliente(clienteValido); //Tenta cadastrar novamente - Throws DataException
	}
	
	

}
