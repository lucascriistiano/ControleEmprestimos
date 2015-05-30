package controle;

import java.util.List;

import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dominio.Cliente;

public class GerenciadorClientes {
	private DaoCliente daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = DaoClienteMemoria.getInstance();
	}
	
	public void cadastrarCliente(Cliente cliente) {
		if(cliente.validar()) {
			this.daoCliente.add(cliente);
		}
	}
	
	public void removerCliente(Cliente cliente) {
		this.daoCliente.remove(cliente);
	}
	
	public List<Cliente> listarClientes() {
		return this.daoCliente.list();
	}
}
