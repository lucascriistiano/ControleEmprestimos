package dao;

import java.util.List;

import dominio.Recurso;
import excecao.DataException;

public interface DaoRecurso {
	
	//@ public model instance List listaRecursos;
	
	/*@ 
	 @ requires recurso != null;
	 @ assignable listaRecursos;
	 @ ensures listaRecursos.size() == \old(listaRecursos.size()) + 1;
	 @ ensures listaRecursos.get(listaRecursos.size()-1) == recurso;
	 @*/
	public void add(Recurso recurso) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires recurso != null;
	 @		requires listaRecursos.isEmpty() == false;
	 @		requires listaRecursos.contains(recurso);
	 @ 		assignable listaRecursos;	 
	 @		ensures !listaRecursos.contains(recurso);
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
     @		signals_only DataException;
	 @		signals (DataException e)
	 @			listaRecursos.isEmpty() || listaRecursos.contains(recurso) == false;
	 @*/
	public void remove(Recurso recurso) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires recurso != null;
	 @		requires listaRecursos.isEmpty() == false;
	 @		requires listaRecursos.contains(recurso);
	 @ 		assignable listaRecursos;	 
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			listaRecursos.isEmpty() || listaRecursos.contains(recurso) == false;
	 @*/	
	public void update(Recurso recurso) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires codigo > 0L;
	 @		requires listaRecursos.isEmpty() == false;
	 @		requires this.exists(codigo);
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			codigo <= 0L || listaRecursos.isEmpty();
	 @*/	
	public /*@ pure @*/ Recurso get(long codigo) throws DataException;
	
	/*@
	 @ 	requires codigo > 0L;
	 @	ensures this.get(codigo) != null ==> (\result == true);
	 */
	public /*@ pure @*/ boolean exists(long codigo);
	
	public /*@ pure @*/ List<Recurso> getPorCategoria(int categoria) throws DataException;
	
	public /*@ pure @*/ List<Recurso> list() throws DataException;
}