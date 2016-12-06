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
	@	public normal_behavior
	@ 		requires cliente != null;
	@		requires cliente.valido();
	@		requires !exists((long) cliente.getCodigo());
	@ 		ensures exists((long) cliente.getCodigo());
	@	also
	@	public exceptional_behavior
	@		requires cliente != null;
	@		requires cliente.valido();
	@		signals (DataException e)
	@			exists((long) cliente.getCodigo());
	@	also
	@	public exceptional_behavior
	@		signals (ClienteInvalidoException e)
	@			cliente.valido() == false;
	@*/
	public /*@ pure @*/ void cadastrarCliente(Cliente cliente) throws DataException, ClienteInvalidoException {	
		if(cliente.valido()) {
			this.daoCliente.add(cliente);
		} else {
			throw new ClienteInvalidoException(cliente.toClienteInvalidoException());
		}
	}

	/*@  
	@ public normal_behavior
	@ 	requires cliente != null;
	@ 	assignable daoCliente;
	@ 	ensures !exists((long) cliente.getCodigo());
	@*/
	public void removerCliente(Cliente cliente) throws DataException {
		this.daoCliente.remove(cliente);
	}
	
	/*@
	@ public normal_behavior
	@ 		ensures \result != null;
	@ also
	@ public exceptional_behavior
	@		signals_only DataException;
	@*/
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
