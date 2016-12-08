package controle;

import java.util.List;

import dao.DaoUsuario;
import dao.DaoUsuarioMemoria;
import dominio.Usuario;
import excecao.DataException;
import excecao.UsuarioInvalidoException;

public class GerenciadorUsuarios {
	
	
	private DaoUsuario daoUsuario; 
	
	public GerenciadorUsuarios() {
		this.daoUsuario = DaoUsuarioMemoria.getInstance();
	}
	
	public void cadastrarUsuario(Usuario usuario) throws UsuarioInvalidoException, DataException {
		if(validarUsuario(usuario))
			this.daoUsuario.add(usuario);
	}
	
	public void updateUsuario(Usuario usuario) throws DataException{
		this.daoUsuario.update(usuario);
	}
	
	public void removerUsuario(Usuario usuario) throws DataException {
		this.daoUsuario.remove(usuario);
	}
	
	@SuppressWarnings("unchecked")
	public List<Usuario> listarUsuarios() throws DataException {
		return (List<Usuario>)(List<?>) daoUsuario.list();
	}
	
	public Usuario getUsuario(Long codigo) throws DataException {
		return (Usuario) daoUsuario.get(codigo);
	}
	
	public Usuario getUsuario(String login) throws DataException {
		return daoUsuario.get(login);
	}
	
	public /*@ pure @*/ boolean exists(long codigo){
		return this.daoUsuario.exists(codigo);
	}
	
	public boolean validarUsuario(Usuario usuario) throws UsuarioInvalidoException, DataException {
		
		if(!usuario.valido()){
			throw usuario.toUsuarioInvalidoException();
		}
		
		try {
			Usuario usuarioBusca = daoUsuario.get(usuario.getLogin());
			if(usuarioBusca != null){
				throw new UsuarioInvalidoException("Nome de usuario ja esta em uso");
			}
			
		} catch (DataException e){
			return true;
		}
		
		return true;
		
	}
}
