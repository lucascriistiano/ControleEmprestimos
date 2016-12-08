package builder;

import static org.junit.Assert.assertTrue;

import java.util.Calendar;
import java.util.Date;

import controle.GerenciadorClientes;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import instanciahotel.ClienteHotel;
import instancialocadoraveiculos.ClienteLocadoraVeiculos;

public class GerenciadorClientesScenarioBuilder {
	
	private Cliente cliente;
	private GerenciadorClientes gerenciador;
	private Class<Cliente> classeCliente;

	public GerenciadorClientesScenarioBuilder(GerenciadorClientes gerenciador, Class<Cliente> classeCliente) {
		super();
		this.gerenciador = gerenciador;
		this.classeCliente = classeCliente;
	}

	public GerenciadorClientesScenarioBuilder criarClienteValido() {		
		cliente = createCliente(classeCliente.getSimpleName(), "12345678900", "123123", "Rua importante", 1, 1, 1980);
		assertTrue("Cliente não deve ser nulo", cliente != null);
		assertTrue("Cliente deve ser válido", cliente.valido());	
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder criarClienteInvalido(){
		cliente = createCliente("", "", "", "Rua ", 1, 1, 2016);
		assertTrue("Cliente não deve ser nulo", cliente != null);
		assertTrue("Cliente deve ser inválido", !cliente.valido());	
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder cadastrarCliente() throws DataException, ClienteInvalidoException{
		gerenciador.cadastrarCliente(cliente);
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder atualizarCliente() throws DataException, ClienteInvalidoException{
		gerenciador.updateCliente(cliente);
		return this;
	}	
	
	public GerenciadorClientesScenarioBuilder removerCliente() throws DataException{
		gerenciador.removerCliente(cliente);
		return this;
	}
		
	public GerenciadorClientesScenarioBuilder setNomeCliente(String nome){
		if(cliente != null){
			cliente.setNome(nome);
		}
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder setCodigo(Long codigo){
		if(cliente != null){
			cliente.setCodigo(codigo);
		}
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder tornarClienteInvalido(){
		if(cliente != null){
			cliente.setNome("");
		}
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder tornarCodigoInvalido(){
		if(cliente != null){
			cliente.setCodigo(-1L);
		}
		return this;
	}	
	
	public GerenciadorClientesScenarioBuilder getCliente() throws DataException{
		cliente = gerenciador.getCliente(cliente.getCodigo());
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder getCliente(Long codigo) throws DataException{
		cliente = gerenciador.getCliente(codigo);
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder assertExists(){
		assertTrue("Cliente deve estar cadastrado", gerenciador.exists(cliente.getCodigo()));
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder assertNotExists(){
		assertTrue("Cliente não deve estar cadastrado", !gerenciador.exists(cliente.getCodigo()));
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder assertCodigoValido(){
		assertTrue("Id do cliente não deve ser menor que 0", !(cliente.getCodigo() < 0));
		return this;
	}
	
	public Cliente getClienteInstance(){
		return cliente;
	}
	
	
	private Cliente createCliente(String nome, String cpf, String rg, String endereco, int dia, int mes, int ano) {
		Calendar dataNascimento = Calendar.getInstance();
		dataNascimento.set(Calendar.DAY_OF_MONTH, dia);
		dataNascimento.set(Calendar.MONTH, mes-1);
		dataNascimento.set(Calendar.YEAR, ano);
		return createCliente(nome, cpf, rg, endereco, dataNascimento.getTime());
	}

	
	private Cliente createCliente(String nome, String cpf, String rg, String endereco, Date nascimento) {
		
		if(classeCliente.equals(ClienteHotel.class)){
			return new ClienteHotel(nome, cpf, rg, endereco, nascimento);
		} else {
			return new ClienteLocadoraVeiculos(nome, cpf, rg, "415485", nascimento);
		}
		
		
	}

}
