package dao;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import dominio.Emprestimo;

public class DaoEmprestimoMemoria implements DaoEmprestimo {

	static DaoEmprestimo daoEmprestimo = null;
	private Set<Emprestimo> emprestimos;
	
	public static DaoEmprestimo getInstance() {
		if(daoEmprestimo == null)
			daoEmprestimo = new DaoEmprestimoMemoria();
		
		return daoEmprestimo;
	}
	
	private DaoEmprestimoMemoria() {
		emprestimos = new HashSet<Emprestimo>();
	}
	
	@Override
	public void add(Emprestimo emprestimo) {
		emprestimos.add(emprestimo);
	}

	@Override
	public void remove(Emprestimo emprestimo) {
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
	public void update(Emprestimo emprestimo) {
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
	public Emprestimo get(Long codigo) {
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
	public List<Emprestimo> list() {
		List<Emprestimo> resultList = new ArrayList<Emprestimo>();
		
		Iterator<Emprestimo> it = emprestimos.iterator();
		while(it.hasNext()) {
			resultList.add(it.next());
		}
		
		return resultList;
	}

}
