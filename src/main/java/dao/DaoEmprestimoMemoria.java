package dao;

import dominio.Emprestimo;

public class DaoEmprestimoMemoria extends DaoMemoria<Emprestimo> implements DaoEmprestimo {

	private static /*@ nullable @*/ DaoEmprestimo daoEmprestimo = null;

	private DaoEmprestimoMemoria() {
		super("Emprestimo");
	}
	
	public static DaoEmprestimo getInstance() {
		if(daoEmprestimo == null)
			daoEmprestimo = new DaoEmprestimoMemoria();
				
		return daoEmprestimo;
	}

}
