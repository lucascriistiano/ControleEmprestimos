package dominio;

import excecao.ClienteInvalidoException;

public abstract class Cliente extends Dominio {
	
	private /*@ spec_public @*/ String nome;
	
	protected Cliente(Long codigo, String nome) {
		this.codigo = codigo;
		this.nome = nome;
	}
	
	public /*@ pure @*/ String getNome() {
		return nome;
	}

	/*@ 
	 @ assignable this.nome;
	 @ ensures this.nome == nome;
	 @*/
	public void setNome(String nome) {
		this.nome = nome;
	}
		
	@Override
	public String toString() {
		return "Cliente [nome=" + nome + ", codigo=" + codigo + ", getNome()=" + getNome() + "]";
	}

	public /*@ pure @*/ abstract ClienteInvalidoException toClienteInvalidoException();
}
