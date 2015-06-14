package dao;

import java.util.List;

import dominio.Emprestimo;
import excecao.DataException;

public interface DaoHistorico {
	public void add(Emprestimo emprestimo) throws DataException;
	public void update(Emprestimo emprestimo) throws DataException;
	
	public Emprestimo get(Long codigo) throws DataException;
	public List<Emprestimo> getHistoricoCliente(Long codigo) throws DataException;
	public List<Emprestimo> list() throws DataException;
}