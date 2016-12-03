package dao;

import java.util.List;

import dominio.Emprestimo;
import excecao.DataException;

public interface DaoHistorico {
	
	//@ public model instance List listaEmprestimos;
	
	/*@ 
	 @ requires emprestimo != null;
	 @ assignable listaEmprestimos;
	 @ ensures listaEmprestimos.size() == \old(listaEmprestimos.size()) + 1;
	 @ ensures listaEmprestimos.get(listaEmprestimos.size()-1) == emprestimo;
	 @*/
	public void add(Emprestimo emprestimo) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires emprestimo != null;
	 @		requires listaEmprestimos.isEmpty() == false;
	 @		requires listaEmprestimos.contains(emprestimo);
	 @ 		assignable listaEmprestimos;	 
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			listaEmprestimos.isEmpty() || listaEmprestimos.contains(emprestimo) == false;
	 @*/	
	public void update(Emprestimo emprestimo) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires codigo > 0L;
	 @		requires listaEmprestimos.isEmpty() == false;
	 @		requires this.exists(codigo);
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			codigo <= 0L || listaEmprestimos.isEmpty();
	 @*/	
	public /*@ pure @*/ Emprestimo get(long codigo) throws DataException;
	
	/*@
	 @ 	requires codigo > 0L;
	 @	ensures this.get(codigo) != null ==> (\result == true);
	 */
	public /*@ pure @*/ boolean exists(long codigo);
	
	public /*@ pure @*/ List<Emprestimo> getHistoricoCliente(Long codigo) throws DataException;
	
	public /*@ pure @*/ List<Emprestimo> list() throws DataException;
}