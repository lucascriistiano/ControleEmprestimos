package controle;

import java.util.List;

import dao.DaoUsuario;
import dao.DaoUsuarioMemoria;
import dominio.Usuario;
import excecao.DataException;
import excecao.UsuarioInvalidoException;

public class GerenciadorUsuarios {
	
	//@ public invariant daoUsuario != null;		
	protected /*@ spec_public @*/ DaoUsuario daoUsuario; 
	
	public GerenciadorUsuarios() {
		this.daoUsuario = DaoUsuarioMemoria.getInstance();
	}
	
	/*@ 
	@	public normal_behavior
	@ 		requires usuario != null;
	@		requires usuario.valido();
	@		requires !exists((long) usuario.getCodigo());
	@ 		ensures exists((long) usuario.getCodigo());
	@	also
	@	public exceptional_behavior
	@		requires usuario != null;
	@		requires usuario.valido();
	@		requires exists((long) usuario.getCodigo());
	@		signals_only DataException;
	@	also
	@	public exceptional_behavior
	@		requires usuario == null || !usuario.valido();
	@		signals_only UsuarioInvalidoException;
	@*/
	public /*@ pure @*/ void cadastrarUsuario(Usuario usuario) throws UsuarioInvalidoException, DataException {
		if(validarUsuario(usuario)){
			this.daoUsuario.add(usuario);
		}
	}
	
	/*@  
	@ public normal_behavior
	@ 	requires usuario != null;
	@	requires ((long) usuario.getCodigo()) > 0;
	@	requires exists((long) usuario.getCodigo());
	@ 	ensures !exists((long) usuario.getCodigo());
	@ also
	@ public exceptional_behavior
	@	requires usuario == null || ((long) usuario.getCodigo()) <= 0 || !exists((long) usuario.getCodigo());
	@	signals_only DataException;
	@*/
	public /*@ pure @*/ void removerUsuario(Usuario usuario) throws DataException {
		this.daoUsuario.remove(usuario);
	}
	
	/*@ 
	@	public normal_behavior
	@ 		requires usuario != null;
	@		requires usuario.valido();
	@		requires exists((long) usuario.getCodigo());
	@ 		ensures exists((long) usuario.getCodigo());
	@		ensures usuario.getCodigo() == \old(usuario.getCodigo());
	@	also
	@	public exceptional_behavior
	@		requires usuario != null;
	@		requires usuario.valido();
	@		requires !exists((long) usuario.getCodigo());
	@		signals_only DataException;
	@	also
	@	public exceptional_behavior
	@		requires usuario == null || !usuario.valido();
	@		signals_only UsuarioInvalidoException;
	@*/
	public /*@ pure @*/ void updateUsuario(Usuario usuario) throws DataException, UsuarioInvalidoException{
		if(usuario.valido()) {
			this.daoUsuario.update(usuario);
		} else {
			throw new UsuarioInvalidoException(usuario.toUsuarioInvalidoException());
		}
	}
	
	/*@
	 @	public normal_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires this.daoUsuario.exists(codigo);
	 @		ensures \result != null;
	 @	also
	 @	public exceptional_behavior 
	 @		requires ((long) codigo) > 0;
	 @		requires !this.daoUsuario.exists(codigo);
	 @		signals_only DataException;
	 @	also
	 @	public exceptional_behavior
	 @		requires ((long) codigo) <= 0 || !this.daoUsuario.exists(codigo);
	 @		signals_only DataException;
	 @*/
	public /*@ pure @*/ Usuario getUsuario(long codigo) throws DataException {
		return (Usuario) daoUsuario.get(codigo);
	}

	/*@
	 @ ensures ((long) codigo) <= 0 ==> \result == false;
	 @ ensures this.daoUsuario.exists(codigo) ==> \result == true;
	 @ ensures !this.daoUsuario.exists(codigo) ==> \result == false;
	 @*/
	public /*@ pure @*/ boolean exists(long codigo){
		return this.daoUsuario.exists(codigo);
	}
	
	@SuppressWarnings("unchecked")
	public /*@ pure @*/ List<Usuario> listarUsuarios() throws DataException {
		return (List<Usuario>)(List<?>) daoUsuario.list();
	}
	
	public /*@ pure @*/ Usuario getUsuario(String login) throws DataException {
		return daoUsuario.get(login);
	}
	
	public boolean validarUsuario(Usuario usuario) throws UsuarioInvalidoException, DataException {
		
		if(!usuario.valido()){
			throw usuario.toUsuarioInvalidoException();
		}
		
		try {
			Usuario usuarioBusca = daoUsuario.get(usuario.getLogin());
			if(usuarioBusca != null){
				throw new DataException("Nome de usuario ja esta em uso");
			}
			
		} catch (DataException e){
			return true;
		}
		
		return true;
		
	}
}
