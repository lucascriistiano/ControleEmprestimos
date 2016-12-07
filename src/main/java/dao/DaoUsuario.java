package dao;

import java.util.List;

import dominio.Usuario;
import excecao.DataException;

public interface DaoUsuario {
	
	//@ public model instance List listaUsuarios;
	
	/*@ 
	 @ requires usuario != null;
	 @ assignable listaUsuarios;
	 @ ensures listaUsuarios.size() == \old(listaUsuarios.size()) + 1;
	 @ ensures listaUsuarios.get(listaUsuarios.size()-1) == usuario;
	 @*/
	public void add(Usuario usuario) throws DataException;
	
	
	public void remove(Usuario usuario) throws DataException;
	
	/*@
	 @	public normal_behavior 
	 @		requires usuario != null;
	 @		requires listaUsuarios.isEmpty() == false;
	 @		requires listaUsuarios.contains(usuario);
	 @ 		assignable listaUsuarios;	 
	 @	also
	 @	public exceptional_behavior
	 @		assignable \nothing;
	 @		signals_only DataException;
	 @		signals (DataException e)
	 @			listaUsuarios.isEmpty() || listaUsuarios.contains(usuario) == false;
	 @*/	
	public void update(Usuario usuario) throws DataException;
	
	public /*@ pure @*/ Usuario get(String login) throws DataException;
	
	/*@
	 @ 	requires login != null;
	 @	ensures this.get(login) != null ==> (\result == true);
	 */
	public /*@ pure @*/ boolean exists(String login);
	
	public /*@ pure @*/ List<Usuario> list() throws DataException;
}