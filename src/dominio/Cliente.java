package dominio;

import excecao.ClienteInvalidoException;

public abstract class Cliente {
	
	private /*@ spec_public @*/ Long codigo;
	
	private /*@ spec_public @*/ String nome;
	
	protected Cliente(Long codigo, String nome) {
		this.codigo = codigo;
		this.nome = nome;
	}
	
	public /*@ pure @*/ Long getCodigo() {
		return codigo;
	}
	
	/*@ 
	 @ assignable this.codigo;
	 @ ensures this.codigo == codigo;
	 */
	public void setCodigo(Long codigo) {
		this.codigo = codigo;
	}

	public /*@ pure @*/ String getNome() {
		return nome;
	}

	/*@ 
	 @ assignable this.nome;
	 @ ensures this.nome == nome;
	 */
	public void setNome(String nome) {
		this.nome = nome;
	}
	
	public abstract boolean validar() throws ClienteInvalidoException;
}
