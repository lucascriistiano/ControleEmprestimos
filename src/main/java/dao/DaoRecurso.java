package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import dominio.Recurso;
import excecao.DataException;

public class DaoRecurso extends DaoImpl<Recurso> {

	private static /*@ nullable @*/ DaoRecurso daoRecurso = null;
	
	public DaoRecurso() {
		super("Recurso");
	}	
	
	public static DaoRecurso getInstance() {
		if(daoRecurso == null)
			daoRecurso = new DaoRecurso();
		
		return daoRecurso;
	}

	public List<Recurso> getPorCategoria(int categoria) throws DataException {
		List<Recurso> resultList = new ArrayList<Recurso>();
		
		Iterator<Recurso> it = list.iterator();
		while(it.hasNext()) {
			Recurso recurso = it.next();
			
			if(recurso.getCategoria() == categoria) {
				resultList.add(recurso);
			}
		}
		
		return resultList;
	}
	
}
