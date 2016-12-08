package controle;

import java.util.List;

import dao.Dao;
import dao.DaoCliente;
import dominio.Cliente;
import excecao.ClienteInvalidoException;
import excecao.DataException;

public class GerenciadorClientes {
	
	//@ public invariant daoCliente != null;
	protected /*@ spec_public @*/ Dao<Cliente> daoCliente;
	
	public GerenciadorClientes() {
		daoCliente = DaoCliente.getInstance();
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
	@		requires exists((long) cliente.getCodigo());
	@		signals_only DataException;
	@	also
	@	public exceptional_behavior
	@		requires cliente == null || !cliente.valido();
	@		signals_only ClienteInvalidoException;
	@*/
	public /*@ pure @*/ void cadastrarCliente(Cliente cliente) throws DataException, ClienteInvalidoException {	
		if(!cliente.valido()) throw new ClienteInvalidoException(cliente.toClienteInvalidoException());
		this.daoCliente.add(cliente);
	}

	/*@  
	@ public normal_behavior
	@ 	requires cliente != null;
	@	requires ((long) cliente.getCodigo()) > 0;
	@	requires exists((long) cliente.getCodigo());
	@ 	ensures !exists((long) cliente.getCodigo());
	@ also
	@ public exceptional_behavior
	@	requires cliente == null || ((long) cliente.getCodigo()) <= 0 || !exists((long) cliente.getCodigo());
	@	signals_only DataException;
	@*/
	public /*@ pure @*/ void removerCliente(Cliente cliente) throws DataException {
		this.daoCliente.remove(cliente);
	}
	
	/*@ 
	@	public normal_behavior
	@ 		requires cliente != null;
	@		requires cliente.valido();
	@		requires exists((long) cliente.getCodigo());
	@ 		ensures exists((long) cliente.getCodigo());
	@		ensures cliente.getCodigo() == \old(cliente.getCodigo());
	@	also
	@	public exceptional_behavior
	@		requires cliente != null;
	@		requires cliente.valido();
	@		requires !exists((long) cliente.getCodigo());
	@		signals_only DataException;
	@	also
	@	public exceptional_behavior
	@		requires cliente == null || !cliente.valido();
	@		signals_only ClienteInvalidoException;
	@*/
	public /*@ pure @*/ void updateCliente(Cliente cliente) throws DataException, ClienteInvalidoException {
		if(!cliente.valido()) throw new ClienteInvalidoException(cliente.toClienteInvalidoException());
		this.daoCliente.update(cliente);
	}
 	
	/*@
	 @	public normal_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires this.daoCliente.exists(codigo);
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires !this.daoCliente.exists(codigo);
	 @		signals_only DataException;
	 @	also
	 @	public exceptional_behavior
	 @		requires ((long) codigo) <= 0 || !this.daoCliente.exists(codigo);
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/ Cliente getCliente(long codigo) throws DataException {
		return (Cliente) this.daoCliente.get(codigo);
	}

	public /*@ pure @*/ List<Cliente> listarClientes() throws DataException {
		return this.daoCliente.list();
	}

	/*@
	 @ ensures ((long) codigo) <= 0 ==> \result == false;
	 @ ensures this.daoCliente.exists(codigo) ==> \result == true;
	 @ ensures !this.daoCliente.exists(codigo) ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean exists(long codigo){
		return this.daoCliente.exists(codigo);
	}
	
}
