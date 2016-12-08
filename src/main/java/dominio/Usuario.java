package dominio;

import excecao.UsuarioInvalidoException;

public class Usuario extends Dominio {
	
	private /*@ nullable spec_public @*/ String nome;
	private /*@ nullable spec_public @*/ String login;
	private /*@ nullable spec_public @*/ String senha;
	
	public Usuario() { }
	
	public Usuario(Long codigo,String nome, String login, String senha) {
		this.codigo = codigo;
		this.nome = nome;
		this.login = login;
		this.senha = senha;
	}

	public /*@ pure @*/ String getNome() {
		return nome;
	}

	public void setNome(String nome) {
		this.nome = nome;
	}

	public /*@ pure @*/ String getLogin() {
		return login;
	}

	public void setLogin(String login) {
		this.login = login;
	}

	public /*@ pure @*/ String getSenha() {
		return senha;
	}

	public void setSenha(String senha) {
		this.senha = senha;
	}
	
	@Override
	public boolean valido() {
		boolean isValido = true;
		if("".equals(login) || login == null){
			isValido = false;
		} else if ("".equals(nome)){
			isValido = false;
		}
		return isValido;
	}
	
	public UsuarioInvalidoException toUsuarioInvalidoException(){
		UsuarioInvalidoException exception = new UsuarioInvalidoException("Usuário Inválido");
		if("".equals(login) || login == null){
			exception = new UsuarioInvalidoException("Login Inválido", exception);
		} else if ("".equals(nome)){
			exception = new UsuarioInvalidoException("Nome Vazio", exception);
		}
		return exception;
	}
	
	@Override
	public String toString() {
		return "Usuario [nome=" + nome + ", login=" + login + ", senha=" + senha + ", codigo=" + codigo + ", valido()="
				+ valido() + "]";
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((login == null) ? 0 : login.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Usuario other = (Usuario) obj;
		if (login == null) {
			if (other.login != null)
				return false;
		} else if (!login.equals(other.login))
			return false;
		return true;
	}
	
	
	
	
}
