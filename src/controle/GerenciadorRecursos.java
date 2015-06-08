package controle;

import java.util.List;

import dao.DaoRecurso;
import dao.DaoRecursoMemoria;
import dominio.Recurso;
import excecao.DataException;

public class GerenciadorRecursos {
	private DaoRecurso daoRecurso;
	
	public GerenciadorRecursos() {
		this.daoRecurso = DaoRecursoMemoria.getInstance();
	}
	
	public void cadastrarRecurso(Recurso recurso) throws DataException {
		this.daoRecurso.add(recurso);
	}
	
	public void removerRecurso(Recurso recurso) throws DataException {
		this.daoRecurso.remove(recurso);
	}
	
	public List<Recurso> listarRecursos() throws DataException {
		return this.daoRecurso.list();
	}

	public Recurso getRecurso(Long codigo) throws DataException {
		return this.daoRecurso.get(codigo);
	}
}
