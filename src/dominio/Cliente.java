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
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((codigo == null) ? 0 : codigo.hashCode());
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
		Cliente other = (Cliente) obj;
		if (codigo == null) {
			if (other.codigo != null)
				return false;
		} else if (!codigo.equals(other.codigo))
			return false;
		return true;
	}
	
	public abstract boolean validar() throws ClienteInvalidoException;
}
