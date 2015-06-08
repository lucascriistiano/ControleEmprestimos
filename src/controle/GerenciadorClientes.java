package controle;

import java.util.List;

import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;

public class GerenciadorClientes {
	private DaoCliente daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = DaoClienteMemoria.getInstance();
	}
	
	public void cadastrarCliente(Cliente cliente) throws DataException, ClienteInvalidoException {
		if(cliente.validar()) {
			this.daoCliente.add(cliente);
		}
	}
	
	public void removerCliente(Cliente cliente) throws DataException {
		this.daoCliente.remove(cliente);
	}
	
	public List<Cliente> listarClientes() throws DataException {
		return this.daoCliente.list();
	}

	public Cliente getCliente(Long codigo) throws DataException {
		return this.daoCliente.get(codigo);
	}
}
