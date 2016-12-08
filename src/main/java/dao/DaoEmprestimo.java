package dao;

import dominio.Emprestimo;

public class DaoEmprestimo extends DaoMemoria<Emprestimo> {
	
	private static /*@ nullable @*/ DaoEmprestimo daoEmprestimo = null;

	private DaoEmprestimo() {
		super("Emprestimo");
	}
	
	public static DaoEmprestimo getInstance() {
		if(daoEmprestimo == null)
			daoEmprestimo = new DaoEmprestimo();
				
		return daoEmprestimo;
	}

	
}
