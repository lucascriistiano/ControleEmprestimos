package builder;

import static org.junit.Assert.assertTrue;

import java.util.Random;

import controle.GerenciadorUsuarios;
import dominio.Usuario;
import excecao.DataException;
import excecao.UsuarioInvalidoException;

public class GerenciadorUsuariosScenarioBuilder {
	
	private Usuario usuario;
	private GerenciadorUsuarios gerenciador;

	public GerenciadorUsuariosScenarioBuilder(GerenciadorUsuarios gerenciador) {
		super();
		this.gerenciador = gerenciador;
	}

	public GerenciadorUsuariosScenarioBuilder criarUsuarioValido() {
		Random rand = new Random();
		usuario = new Usuario("Nome" + rand.nextInt(), "login" + rand.nextInt() , "pass" + rand.nextInt());
		assertTrue("Usuario não deve ser nulo", usuario != null);
		assertTrue("Usuario deve ser válido", usuario.valido());	
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder criarUsuarioInvalido(){
		usuario = new Usuario();
		assertTrue("Usuario não deve ser nulo", usuario != null);
		assertTrue("Usuario deve ser inválido", !usuario.valido());	
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder cadastrarUsuario() throws DataException, UsuarioInvalidoException{
		gerenciador.cadastrarUsuario(usuario);
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder atualizarUsuario() throws DataException, UsuarioInvalidoException{
		gerenciador.updateUsuario(usuario);
		return this;
	}	
	
	public GerenciadorUsuariosScenarioBuilder removerUsuario() throws DataException{
		gerenciador.removerUsuario(usuario);
		return this;
	}
		
	public GerenciadorUsuariosScenarioBuilder setNomeUsuario(String nome){
		if(usuario != null){
			usuario.setNome(nome);
		}
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder setCodigo(Long codigo){
		if(usuario != null){
			usuario.setCodigo(codigo);
		}
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder tornarUsuarioInvalido(){
		if(usuario != null){
			usuario.setNome("");
		}
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder tornarCodigoInvalido(){
		if(usuario != null){
			usuario.setCodigo(-1L);
		}
		return this;
	}	
	
	public GerenciadorUsuariosScenarioBuilder getUsuario() throws DataException{
		usuario = gerenciador.getUsuario(usuario.getCodigo());
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder getUsuario(Long codigo) throws DataException{
		usuario = gerenciador.getUsuario(codigo);
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder assertExists(){
		assertTrue("Usuario deve estar cadastrado", gerenciador.exists(usuario.getCodigo()));
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder assertNotExists(){
		assertTrue("Usuario não deve estar cadastrado", !gerenciador.exists(usuario.getCodigo()));
		return this;
	}
	
	public GerenciadorUsuariosScenarioBuilder assertCodigoValido(){
		assertTrue("Id do cliente não deve ser menor que 0", !(usuario.getCodigo() < 0));
		return this;
	}
	
	public Usuario getUsuarioInstance(){
		return usuario;
	}
	
	
}
