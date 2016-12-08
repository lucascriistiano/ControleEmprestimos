package dao;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import dominio.Dominio;
import excecao.DataException;

public abstract class DaoImpl<T extends Dominio> implements Dao<T> {
	
	private long contador;
	private final String entidade;
	protected /*@ spec_public @*/ List<T> list; 
	
		
	public DaoImpl(String entidade) {
		super();
		this.contador = 0;
		this.entidade = entidade;
		this.list = new ArrayList<>();
	}
	
	/*@ 
	 @ also
	 @ public normal_behavior
	 @ 		requires obj != null;
 	 @		requires ((long) obj.getCodigo()) == 0L;
	 @		requires !list.contains(obj);
	 @ 		ensures list.size() == \old(list.size()) + 1;
	 @ 		ensures list.get(list.size()-1) == obj;
	 @		ensures ((long) obj.getCodigo()) > 0L;
	 @	also
	 @	public exceptional_behavior
	 @ 		requires obj != null;
	 @		requires list.contains(obj);
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/ void add(T obj) throws DataException {	
		if(list.contains(obj)) throw new DataException(entidade + " já Cadastrado");

		contador++;
		obj.setCodigo(contador);
		list.add(obj);
	}

	/*@
	 @ also
	 @ public normal_behavior
	 @		requires obj != null;
	 @		requires ((long) obj.getCodigo()) > 0;
	 @		requires list.isEmpty() == false;
	 @		requires list.contains(obj);	 
	 @		ensures !list.contains(obj);
	 @	also
	 @	public exceptional_behavior
	 @		requires obj == null || ((long) obj.getCodigo()) <= 0 || list.isEmpty() || list.contains(obj) == false;
	 @		assignable \nothing;
    @		signals_only DataException;
	 @*/
	public /*@ pure @*/ final void remove(T obj) throws DataException {
		Iterator<T> it = list.iterator();
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

	/*@
	 @ also
	 @ public normal_behavior
	 @		requires obj != null;
	 @		requires list.contains(obj);
	 @		ensures	list.contains(obj);
	 @		ensures obj.getCodigo() == \old(obj.getCodigo());	 
	 @	also
	 @	public exceptional_behavior
	 @		requires obj != null;
	 @		requires !list.contains(obj);
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			list.isEmpty() || list.contains(obj) == false;
	 @*/
	public /*@ pure @*/ final void update(T obj) throws DataException {	
		Iterator<T> it = list.iterator();
		while(it.hasNext()) {
			Dominio c = it.next();
			
			//Atualiza objeto armazenado se o codigo for igual
			if(c.equals(obj)) {
				c = obj;
				return;
			}
		}
		
		throw new DataException(entidade + " não existe");
	}

	/*@
	 @ also
	 @ public normal_behavior
	 @		requires ((long) codigo) > 0;
	 @		requires this.exists(codigo);
	 @		ensures ((Dominio)\result) != null;
	 @		ensures ((Dominio) \result).getCodigo() == codigo;
	 @	also
	 @	public exceptional_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires !this.exists(codigo);
	 @		signals_only DataException;
	 @	also
	 @	public exceptional_behavior
	 @		requires ((long) codigo) <= 0;
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/ Dominio get(long codigo) throws DataException {
		if(codigo <= 0L) {
			throw new DataException("Codigo menor que zero");
		}
		
		Iterator<T> it = list.iterator();
		while(it.hasNext()) {
			T c = it.next();
			if(Long.compare(c.getCodigo(), codigo) == 0) {
				return c;
			}
		}
		
		throw new DataException("Cliente não cadastrado");
	}

	/*@ 
	 @ also
	 @ public normal_behavior
	 @ 		requires list != null;
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior
	 @		requires list == null;
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/final List<T> list() throws DataException {
		if(list== null){
			throw new DataException("Não há " + entidade + "s cadastrados.");
		}
		return new ArrayList<T>(list);
	}

	/*@
	 @ also
	 @ ensures ((long) codigo) <= 0 ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean exists(long codigo) {
		List<T> list;
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

	/*@
	 @ also
	 @ ensures ((long) obj.getCodigo()) <= 0 ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean exists(T obj) {
		Iterator<T> it = list.iterator();
		while(it.hasNext()) {
			Dominio c = it.next();
			if(Long.compare(c.getCodigo(), obj.getCodigo()) == 0) {
				return true;
			}
		}
		return false;
	}

	public final void clear() {
		if(list != null){
			list.clear();
			contador = 0;
		}
	}


	
	
	

}
