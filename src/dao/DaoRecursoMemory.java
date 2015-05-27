package dao;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import dominio.Recurso;

public class DaoRecursoMemory implements DaoRecurso {

	static DaoRecurso daoRecurso = null;
	private Set<Recurso> recursos;
	
	public static DaoRecurso getInstance() {
		if(daoRecurso == null)
			daoRecurso = new DaoRecursoMemory();
		
		return daoRecurso;
	}
	
	private DaoRecursoMemory() {
		recursos = new HashSet<Recurso>();
	}
	
	@Override
	public void add(Recurso recurso) {
		recursos.add(recurso);
	}

	@Override
	public void remove(Recurso recurso) {
		recursos.remove(recurso);
	}

	@Override
	public void update(Recurso recurso) {
		recursos. add(recurso);
		
		Iterator<Recurso> it = recursos.iterator();
		while(it.hasNext()) {
			Recurso r = it.next();
			
			//Atualiza objeto armazenado se o numero for igual
			if(r.getCodigo().equals(recurso.getCodigo())) {
				r = recurso;
				return;
			}
		}
	}

	@Override
	public Recurso get(Long codigo) {
		Iterator<Recurso> it = recursos.iterator();
		while(it.hasNext()) {
			Recurso r = it.next();
			
			//Atualiza objeto armazenado se o numero for igual
			if(r.getCodigo().equals(codigo)) {
				return r;
			}
		}
		
		return null;
	}

	@Override
	public List<Recurso> list() {
		List<Recurso> resultList = new ArrayList<Recurso>();
		
		Iterator<Recurso> it = recursos.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}

}
