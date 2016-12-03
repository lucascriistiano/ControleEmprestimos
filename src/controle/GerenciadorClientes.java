package controle;

import java.util.List;

import dao.DaoCliente;
import dao.DaoClienteMemoria;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;

public class GerenciadorClientes {
	
	//@ public invariant daoCliente != null;
	protected /*@ spec_public @*/ DaoCliente daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = DaoClienteMemoria.getInstance();
	}
	
	/*@ 
	@ public normal_behavior
	@ 	requires cliente != null && cliente.validar() == true;
	@ 	assignable daoCliente;
	@ 	ensures this.listarClientes().contains(cliente);
	@*/
	public void cadastrarCliente(Cliente cliente) throws DataException, ClienteInvalidoException {
		if(cliente.validar()) {
			this.daoCliente.add(cliente);
		}
	}

	/*@  
	@ public normal_behavior
	@ 	requires cliente != null;
	@ 	assignable daoCliente;
	@ 	ensures this.listarClientes().contains(cliente) == false;
	@*/
	public void removerCliente(Cliente cliente) throws DataException {
		this.daoCliente.remove(cliente);
	}
	
	public /*@ pure @*/  List<Cliente> listarClientes() throws DataException {
		return this.daoCliente.list();
	}
	
	/*@ requires codigo > 0L; @*/
	public /*@ pure @*/  Cliente getCliente(long codigo) throws DataException {
		return this.daoCliente.get(codigo);
	}
	
	/*@ 
	 @ requires codigo > 0L; 
	 @ assignable \nothing;
	 @ ensures this.daoCliente.exists(codigo) ==> \result == true;
	 @ ensures !this.daoCliente.exists(codigo) ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean exists(long codigo){
		return this.daoCliente.exists(codigo);
	}
}
