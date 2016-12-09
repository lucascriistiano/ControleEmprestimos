package dao;

import dominio.Cliente;

public class DaoCliente extends DaoImpl<Cliente> {
	
	//@ public initially daoCliente == null;			
	private static /*@ spec_public nullable @*/ DaoCliente daoCliente = null;

	private DaoCliente() {
		super("Cliente");
	}
	
	public static DaoCliente getInstance() {
		if(daoCliente == null)
			daoCliente = new DaoCliente();
				
		return daoCliente;
	}
	
	
		
}
