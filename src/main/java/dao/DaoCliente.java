package dao;

import dominio.Cliente;

public class DaoCliente extends DaoImpl<Cliente> {
				
	private static /*@ nullable @*/ DaoCliente daoCliente = null;

	private DaoCliente() {
		super("Cliente");
	}
	
	public static DaoCliente getInstance() {
		if(daoCliente == null)
			daoCliente = new DaoCliente();
				
		return daoCliente;
	}
	
	
		
}
