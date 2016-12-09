package dao;

import dominio.Emprestimo;

public class DaoEmprestimo extends DaoImpl<Emprestimo> {
	
	//@ public initially daoEmprestimo == null;	
	private static /*@ spec_public nullable @*/ DaoEmprestimo daoEmprestimo = null;

	private DaoEmprestimo() {
		super("Emprestimo");
	}
	
	public static DaoEmprestimo getInstance() {
		if(daoEmprestimo == null)
			daoEmprestimo = new DaoEmprestimo();
				
		return daoEmprestimo;
	}

	
}
