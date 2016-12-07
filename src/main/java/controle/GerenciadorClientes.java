package controle;

import java.util.List;

import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;

public class GerenciadorClientes {
	
	protected DaoCliente daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = DaoClienteMemoria.getInstance();
	}
	
	public void cadastrarCliente(Cliente cliente) throws DataException, ClienteInvalidoException {	
		if(cliente.valido()) {
			this.daoCliente.add(cliente);
		} else {
			throw new ClienteInvalidoException(cliente.toClienteInvalidoException());
		}
	}

	public void removerCliente(Cliente cliente) throws DataException {
		this.daoCliente.remove(cliente);
	}
	
	public List<Cliente> listarClientes() throws DataException {
		return this.daoCliente.list();
	}

	public Cliente getCliente(long codigo) throws DataException {
		return this.daoCliente.get(codigo);
	}

	public boolean exists(long codigo){
		return this.daoCliente.exists(codigo);
	}
}
