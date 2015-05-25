package controle;

import dao.DaoCliente;
import dominio.Cliente;

public class GerenciadorClientes {
	private DaoCliente daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = new DaoCliente();
	}
	
	public void cadastrarCliente(Cliente cliente) {
		this.daoCliente.add(cliente);
	}
}
