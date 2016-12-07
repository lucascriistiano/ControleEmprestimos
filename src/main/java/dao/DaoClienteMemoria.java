package dao;

import dominio.Cliente;

public class DaoClienteMemoria extends DaoMemoria<Cliente> implements DaoCliente {
	
	private static /*@ nullable @*/ DaoCliente daoCliente = null;

	private DaoClienteMemoria() {
		super("Cliente");
	}
	
	public static DaoCliente getInstance() {
		if(daoCliente == null)
			daoCliente = new DaoClienteMemoria();
				
		return daoCliente;
	}
		
}
