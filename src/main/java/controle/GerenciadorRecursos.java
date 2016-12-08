package controle;

import java.util.ArrayList;
import java.util.List;

import dao.DaoRecurso;
import dao.DaoRecurso;
import dominio.Recurso;
import excecao.DataException;
import excecao.RecursoInvalidoException;

public class GerenciadorRecursos {
	
	//@ public invariant daoRecurso != null;		
	private /*@ spec_public @*/ DaoRecurso daoRecurso;
	
	public GerenciadorRecursos() {
		this.daoRecurso = DaoRecurso.getInstance();
	}
	
	/*@ 
	@	public normal_behavior
	@ 		requires recurso != null;
	@		requires recurso.valido();
	@		requires !exists((long) recurso.getCodigo());
	@ 		ensures exists((long) recurso.getCodigo());
	@	also
	@	public exceptional_behavior
	@		requires recurso != null;
	@		requires recurso.valido();
	@		requires exists((long) recurso.getCodigo());
	@		signals_only DataException;
	@	also
	@	public exceptional_behavior
	@		requires recurso == null || !recurso.valido();
	@		signals_only RecursoInvalidoException;
	@*/	
	public /*@ pure @*/  void cadastrarRecurso(Recurso recurso) throws DataException, RecursoInvalidoException {
		if(!recurso.valido()) throw new RecursoInvalidoException(recurso.toRecursoInvalidoException());
		this.daoRecurso.add(recurso);
	}
		
	/*@  
	@ public normal_behavior
	@ 	requires recurso != null;
	@	requires ((long) recurso.getCodigo()) > 0;
	@	requires exists((long) recurso.getCodigo());
	@ 	ensures !exists((long) recurso.getCodigo());
	@ also
	@ public exceptional_behavior
	@	requires recurso == null || ((long) recurso.getCodigo()) <= 0 || !exists((long) recurso.getCodigo());
	@	signals_only DataException;
	@*/
	public /*@ pure @*/ void removerRecurso(Recurso recurso) throws DataException {
		this.daoRecurso.remove(recurso);
	}
	
	/*@ 
	@	public normal_behavior
	@ 		requires recurso != null;
	@		requires recurso.valido();
	@		requires exists((long) recurso.getCodigo());
	@ 		ensures exists((long) recurso.getCodigo());
	@		ensures recurso.getCodigo() == \old(recurso.getCodigo());
	@	also
	@	public exceptional_behavior
	@		requires recurso != null;
	@		requires recurso.valido();
	@		requires !exists((long) recurso.getCodigo());
	@		signals_only DataException;
	@	also
	@	public exceptional_behavior
	@		requires recurso == null || !recurso.valido();
	@		signals_only RecursoInvalidoException;
	@*/
	public /*@ pure @*/ void updateRecurso(Recurso recurso) throws DataException, RecursoInvalidoException{
		if(!recurso.valido()) throw new RecursoInvalidoException(recurso.toRecursoInvalidoException());
		this.daoRecurso.update(recurso);
	}
	
	/*@
	 @	public normal_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires this.daoRecurso.exists(codigo);
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires !this.daoRecurso.exists(codigo);
	 @		signals_only DataException;
	 @	also
	 @	public exceptional_behavior
	 @		requires ((long) codigo) <= 0 || !this.daoRecurso.exists(codigo);
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/ Recurso getRecurso(long codigo) throws DataException {
		return (Recurso) this.daoRecurso.get(codigo);
	}
	
	/*@
	 @ ensures ((long) codigo) <= 0 ==> \result == false;
	 @ ensures this.daoRecurso.exists(codigo) ==> \result == true;
	 @ ensures !this.daoRecurso.exists(codigo) ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean exists(long codigo){
		return this.daoRecurso.exists(codigo);
	}
	
	@SuppressWarnings("unchecked")
	public /*@ pure @*/ List<Recurso> listarRecursos() throws DataException {
		return (List<Recurso>)(List<?>) this.daoRecurso.list();
	}
	
	@SuppressWarnings("unchecked")
	public /*@ pure @*/ List<Recurso> listarRecursos(boolean isDisponivel) throws DataException {
		List<Recurso> recursos = (List<Recurso>)(List<?>) this.daoRecurso.list();
		
		List<Recurso> resultList = new ArrayList<Recurso>();
		for(Recurso recurso : recursos) {
			if(recurso.isDisponivel() == isDisponivel)
				resultList.add(recurso);
		}
		
		return (List<Recurso>)(List<?>) resultList;
	}

	
}
