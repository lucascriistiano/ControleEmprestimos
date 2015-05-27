package dao;

import java.util.List;

import dominio.Recurso;

public interface DaoRecurso {
	public void add(Recurso recurso);
	public void remove(Recurso recurso);
	public void update(Recurso recurso);
	
	public Recurso get(Long codigo);
	public List<Recurso> list();
}