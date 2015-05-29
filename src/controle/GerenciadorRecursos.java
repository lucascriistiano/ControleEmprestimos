package controle;

import java.util.List;

import dao.DaoRecurso;
import dao.DaoRecursoMemoria;
import dominio.Recurso;

public class GerenciadorRecursos {
	private DaoRecurso daoRecurso;
	
	public GerenciadorRecursos() {
		this.daoRecurso = DaoRecursoMemoria.getInstance();
	}
	
	public void cadastrarRecurso(Recurso recurso) {
		this.daoRecurso.add(recurso);
	}
	
	public void removerRecurso(Recurso recurso) {
		this.daoRecurso.remove(recurso);
	}
	
	public List<Recurso> listarRecursos() {
		return this.daoRecurso.list();
	}
}
