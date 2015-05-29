package controle;

import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dominio.Cliente;

public class GerenciadorClientes {
	private DaoCliente daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = DaoClienteMemoria.getInstance();
	}
	
	public boolean cadastrarCliente(Cliente cliente) {
		if(cliente.validar()) {
			this.daoCliente.add(cliente);
			return true;
		}
		
		return false;
	}
}
