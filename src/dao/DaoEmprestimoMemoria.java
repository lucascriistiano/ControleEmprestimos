package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import dominio.Emprestimo;
import excecao.DataException;

public class DaoEmprestimoMemoria implements DaoEmprestimo {

	private static /*@ nullable @*/ DaoEmprestimo daoEmprestimo = null;
	
	private List<Emprestimo> emprestimos; //@ in listaEmprestimos;
	//@ private represents listaEmprestimos <- emprestimos;
	
	public static DaoEmprestimo getInstance() {
		if(daoEmprestimo == null)
			daoEmprestimo = new DaoEmprestimoMemoria();
		
		return daoEmprestimo;
	}
	
	private DaoEmprestimoMemoria() {
		emprestimos = new ArrayList<Emprestimo>();
	}
	
	@Override
	public void add(Emprestimo emprestimo) throws DataException{
		emprestimos.add(emprestimo);
	}

	@Override
	public void remove(Emprestimo emprestimo) throws DataException {
		Iterator<Emprestimo> it = emprestimos.iterator();
		while(it.hasNext()) {
			Emprestimo e = it.next();
			
			//Remove o objeto armazenado se o codigo for igual
			if(e.getCodigo().equals(emprestimo.getCodigo())) {
				it.remove();
				return;
			}
		}
	}

	@Override
	public void update(Emprestimo emprestimo) throws DataException {
		Iterator<Emprestimo> it = emprestimos.iterator();
		while(it.hasNext()) {
			Emprestimo e = it.next();
			
			//Atualiza objeto armazenado se o codigo for igual
			if(e.getCodigo().equals(emprestimo.getCodigo())) {
				e = emprestimo;
				return;
			}
		}
	}

	@Override
	public Emprestimo get(long codigo) throws DataException {
		Iterator<Emprestimo> it = emprestimos.iterator();
		while(it.hasNext()) {
			Emprestimo e = it.next();
			
			if(e.getCodigo().equals(codigo)) {
				return e;
			}
		}
		
		return null;
	}

	@Override
	public List<Emprestimo> list() throws DataException {
		List<Emprestimo> resultList = new ArrayList<Emprestimo>();
		
		Iterator<Emprestimo> it = emprestimos.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}

	@Override
	public boolean exists(long codigo) {
		List<Emprestimo> list;
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
