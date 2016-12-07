package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import dominio.Dominio;
import excecao.DataException;

public class DaoMemoria<T extends Dominio> implements Dao {
	
	private final String entidade;
	protected List<T> lista; //@ in list;
	//@ protected represents list <- lista;
	
	
	public DaoMemoria(String entidade) {
		super();
		this.entidade = entidade;
		this.lista = new ArrayList<>();
	}

	@Override
	public void add(Dominio obj) throws DataException {
		@SuppressWarnings("unchecked")
		T cobj = (T) obj;
		if(!lista.contains(cobj)){
			lista.add(cobj);
		} else {
			throw new DataException(entidade + " já Cadastrado");
		}
	}

	@Override
	public void remove(Dominio obj) throws DataException {
		Iterator<T> it = lista.iterator();
		while(it.hasNext()) {
			Dominio c = it.next();
			
			//Remove o objeto armazenado se o codigo for igual
			if(c.equals(obj)) {
				it.remove();
				return;
			}
		}
		throw new DataException(entidade + " nao encontrado");
	}

	@Override
	public void update(Dominio obj) throws DataException {
		Iterator<T> it = lista.iterator();
		while(it.hasNext()) {
			Dominio c = it.next();
			
			//Atualiza objeto armazenado se o codigo for igual
			if(c.equals(obj)) {
				c = obj;
				return;
			}
		}
	}

	@Override
	public Dominio get(long codigo) throws DataException {
		if(codigo <= 0L) {
			throw new DataException("Codigo menor que zero");
		}
		
		Iterator<T> it = lista.iterator();
		while(it.hasNext()) {
			Dominio c = it.next();
			if(Long.compare(c.getCodigo(), codigo) == 0) {
				return c;
			}
		}
		
		throw new DataException("Cliente não cadastrado");
	}

	@Override
	public List<Dominio> list() throws DataException {
		if(lista == null){
			throw new DataException("Não há " + entidade + "s cadastrados.");
		}
		return new ArrayList<Dominio>(lista);
	}

	@Override
	public boolean exists(long codigo) {
		List<Dominio> list;
		try{
			list = list();
		} catch (DataException e){
			return false;
		}
		
		if(list.isEmpty()){
			return false;
		} else {
			return list.stream().filter(x -> {
				return Long.compare(x.getCodigo(), codigo) == 0;
			}).count() > 0;
		}		
	}

	@Override
	public boolean exists(Dominio obj) {
		Iterator<T> it = lista.iterator();
		while(it.hasNext()) {
			Dominio c = it.next();
			if(Long.compare(c.getCodigo(), obj.getCodigo()) == 0) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void clear() {
		if(lista != null){
			lista.clear();
		}
	}


	
	
	

}
