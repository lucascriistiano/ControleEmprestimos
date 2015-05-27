package dao;

import java.util.List;

import dominio.Emprestimo;

public interface DaoEmprestimo {
	public void add(Emprestimo emprestimo);
	public void remove(Emprestimo emprestimo);
	public void update(Emprestimo emprestimo);
	
	public Emprestimo get(Long codigo);
	public List<Emprestimo> list();
}