package builder;

import static org.junit.Assert.assertTrue;

import java.util.Calendar;
import java.util.Date;
import java.util.List;

import controle.GerenciadorClientes;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;
import instanciahotel.ClienteHotel;

public class GerenciadorClientesScenarioBuilder {
	
	private Cliente cliente;
	private GerenciadorClientes gerenciador;

	public GerenciadorClientesScenarioBuilder(GerenciadorClientes gerenciador) {
		super();
		this.gerenciador = gerenciador;
	}

	public GerenciadorClientesScenarioBuilder criarClienteValido() {
		long codigo;
		try{
			List<Cliente> lista = gerenciador.listarClientes();
			if(lista == null || lista.isEmpty()){
				codigo = 1L;
			} else {
				codigo = lista.get(lista.size() -1).getCodigo() + 1L;
			}
		} catch (DataException e){
			codigo = 1L;
		}
		
		cliente = createClienteHotel(codigo, "Roberto", "12345678900", "123123", "Rua importante", 1, 1, 1998);
		assertTrue("Cliente não deve ser nulo", cliente != null);
		assertTrue("Cliente deve ser válido", cliente.valido());	
		return this;
	}
	
	public GerenciadorClientesScenarioBuilder criarClienteInvalido(){
		cliente = createClienteHotel(1L, "", "", "", "Rua ", 1, 1, 2016);
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
	
	public GerenciadorClientesScenarioBuilder setCodigoInvalido(){
		if(cliente != null){
			cliente.setCodigo(0L);
		}
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
			cliente.setCodigo(0L);
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
		assertTrue("Id do cliente deve ser maior que 0", cliente.getCodigo() > 0);
		return this;
	}
	
	public Cliente getClienteInstance(){
		return cliente;
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

}
