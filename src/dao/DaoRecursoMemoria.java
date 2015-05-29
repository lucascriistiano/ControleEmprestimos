package dao;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import dominio.Recurso;

public class DaoRecursoMemoria implements DaoRecurso {

	static DaoRecurso daoRecurso = null;
	private Set<Recurso> recursos;
	
	public static DaoRecurso getInstance() {
		if(daoRecurso == null)
			daoRecurso = new DaoRecursoMemoria();
		
		return daoRecurso;
	}
	
	private DaoRecursoMemoria() {
		recursos = new HashSet<Recurso>();
	}
	
	@Override
	public void add(Recurso recurso) {
		recursos.add(recurso);
	}

	@Override
	public void remove(Recurso recurso) {
		Iterator<Recurso> it = recursos.iterator();
		while(it.hasNext()) {
			Recurso r = it.next();
			
			//Remove o objeto armazenado se o codigo for igual
			if(r.getCodigo().equals(recurso.getCodigo())) {
				it.remove();
				return;
			}
		}
	}

	@Override
	public void update(Recurso recurso) {
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
