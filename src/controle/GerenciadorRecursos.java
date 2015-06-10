package controle;

import java.util.ArrayList;
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
	
	public List<Recurso> listarRecursos(boolean isDisponivel) throws DataException {
		List<Recurso> recursos = this.daoRecurso.list();
		
		List<Recurso> resultList = new ArrayList<Recurso>();
		for(Recurso recurso : recursos) {
			if(recurso.isDisponivel() == isDisponivel)
				resultList.add(recurso);
		}
		
		return resultList;
	}

	public Recurso getRecurso(Long codigo) throws DataException {
		return this.daoRecurso.get(codigo);
	}
}
