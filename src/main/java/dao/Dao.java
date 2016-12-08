package dao;

import java.util.List;

import dominio.Dominio;
import excecao.DataException;

public interface Dao<T extends Dominio> {

	public void add(T obj) throws DataException;
	public void remove(T obj) throws DataException;
	public void update (T obj) throws DataException;
	public /*@ pure @*/ Dominio get(long codigo) throws DataException;
	public /*@ pure @*/ List<T> list() throws DataException;
	public /*@ pure @*/ boolean exists(long codigo);
	public /*@ pure @*/ boolean exists(T obj);
	public void clear();
	
}
