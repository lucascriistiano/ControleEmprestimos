package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import dominio.Recurso;
import excecao.DataException;

public class DaoRecursoMemoria implements DaoRecurso {

	private static /*@ nullable @*/ DaoRecurso daoRecurso = null;
	
	private List<Recurso> recursos; //@ in listaRecursos;
	//@ private represents listaRecursos <- recursos;
	
	public static DaoRecurso getInstance() {
		if(daoRecurso == null)
			daoRecurso = new DaoRecursoMemoria();
		
		return daoRecurso;
	}
	
	private DaoRecursoMemoria() {
		recursos = new ArrayList<Recurso>();
	}
	
	@Override
	public void add(Recurso recurso)  throws DataException{
		recursos.add(recurso);
	}

	@Override
	public void remove(Recurso recurso) throws DataException {
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
	public void update(Recurso recurso) throws DataException {
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
	public Recurso get(long codigo) throws DataException {
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
	public List<Recurso> getPorCategoria(int categoria) throws DataException {
		List<Recurso> resultList = new ArrayList<Recurso>();
		
		Iterator<Recurso> it = recursos.iterator();
		while(it.hasNext()) {
			Recurso recurso = it.next();
			
			if(recurso.getCategoria() == categoria) {
				resultList.add(recurso);
			}
		}
		
		return resultList;
	}
	
	@Override
	public List<Recurso> list() throws DataException {
		List<Recurso> resultList = new ArrayList<Recurso>();
		
		Iterator<Recurso> it = recursos.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}
	
	@Override
	public boolean exists(long codigo) {
		List<Recurso> list;
		try{
			list = list();
		} catch (DataException e){
			return false;
		}
		
		if(list.isEmpty()){
			return false;
		} else {
			return list.stream().filter(x -> {	return x.getCodigo()!= null && x.getCodigo().equals(codigo);}).count() > 0;
		}
	}

}
