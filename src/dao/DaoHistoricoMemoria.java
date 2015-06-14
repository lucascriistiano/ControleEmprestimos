package dao;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import dominio.Emprestimo;
import excecao.DataException;

public class DaoHistoricoMemoria implements DaoHistorico {

	static DaoHistorico daoHistorico = null;
	private Set<Emprestimo> emprestimos;
	
	public static DaoHistorico getInstance() {
		if(daoHistorico == null)
			daoHistorico = new DaoHistoricoMemoria();
		
		return daoHistorico;
	}
	
	private DaoHistoricoMemoria() {
		emprestimos = new HashSet<Emprestimo>();
	}
	
	@Override
	public void add(Emprestimo emprestimo) throws DataException{
		emprestimos.add(emprestimo);
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
	public Emprestimo get(Long codigo) throws DataException {
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
	public List<Emprestimo> getHistoricoCliente(Long codigo) throws DataException {
		List<Emprestimo> resultList = new ArrayList<Emprestimo>();
		
		Iterator<Emprestimo> it = emprestimos.iterator();
		while(it.hasNext()) {
			Emprestimo emprestimo = it.next();
			if(emprestimo.getCliente().getCodigo().equals(codigo)) {
				resultList.add(emprestimo);
			}
		}
		
		return resultList;
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

}
