package dao;

import java.util.List;

import dominio.Recurso;
import excecao.DataException;

public interface DaoRecurso {
	public void add(Recurso recurso) throws DataException;
	public void remove(Recurso recurso) throws DataException;
	public void update(Recurso recurso) throws DataException;
	
	public Recurso get(Long codigo) throws DataException;
	public List<Recurso> getPorCategoria(int categoria) throws DataException;
	public List<Recurso> list() throws DataException;
}