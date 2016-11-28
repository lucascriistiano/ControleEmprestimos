package dominio;

public class Usuario {
	
	private /*@ spec_public @*/ String nome;
	private /*@ spec_public @*/ String login;
	private /*@ spec_public @*/ String senha;
	
	public Usuario() { }
	
	public Usuario(String nome, String login, String senha) {
		this.nome = nome;
		this.login = login;
		this.senha = senha;
	}

	public String /*@ pure @*/ getNome() {
		return nome;
	}

	public void setNome(String nome) {
		this.nome = nome;
	}

	public String /*@ pure @*/ getLogin() {
		return login;
	}

	public void setLogin(String login) {
		this.login = login;
	}

	public String /*@ pure @*/ getSenha() {
		return senha;
	}

	public void setSenha(String senha) {
		this.senha = senha;
	}
	
}
