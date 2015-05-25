package controle;

import dao.DaoRecurso;
import dominio.Recurso;

public class GerenciadorRecursos {
	private DaoRecurso daoRecurso;
	
	public GerenciadorRecursos() {
		this.daoRecurso = new DaoRecurso();
	}
	
	public void cadastrarRecurso(Recurso recurso) {
		this.daoRecurso.add(recurso);
	}
}
