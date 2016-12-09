package dominio;

import excecao.RecursoInvalidoException;

public abstract class Recurso extends Dominio {
	
	private /*@ spec_public @*/ String descricao;
	private /*@ spec_public @*/ int categoria;
	private /*@ spec_public @*/ boolean disponivel;
	
	protected Recurso(String descricao, int categoria) {
		this.descricao = descricao;
		this.categoria = categoria;
		this.disponivel = true;
	}
	
	protected Recurso(String descricao, int categoria, boolean disponivel) {
		this.descricao = descricao;
		this.categoria = categoria;
		this.disponivel =  disponivel;
	}
	
	public /*@ pure @*/ int getCategoria() {
		return categoria;
	}

	public void setCategoria(int categoria) {
		this.categoria = categoria;
	}

	public /*@ pure @*/ String getDescricao() {
		return descricao;
	}

	public void setDescricao(String descricao) {
		this.descricao = descricao;
	}

	public /*@ pure @*/ boolean isDisponivel() {
		return disponivel;
	}

	public void setDisponivel(boolean disponivel) {
		this.disponivel = disponivel;
	}
	
	@Override
	public String toString() {
		return "Recurso [descricao=" + descricao + ", categoria=" + categoria + ", disponivel=" + disponivel
				+ ", codigo=" + codigo + ", isDisponivel()=" + isDisponivel() + ", valido()=" + valido() + "]";
	}
	

	@Override
	public /*@ pure @*/ boolean valido() {
		boolean isValido = super.valido();
		
		if ("".equals(descricao) || descricao == null){
			isValido = false;
		}
		return isValido;
	}
	
	public /*@ pure @*/ RecursoInvalidoException toRecursoInvalidoException(){
		RecursoInvalidoException exception = new RecursoInvalidoException("Usuário Inválido");
		if(codigo < 0L){
			exception = new RecursoInvalidoException("Codigo Inválido < 0", exception);
		} else if("".equals(descricao) || descricao == null){
			exception = new RecursoInvalidoException("Descrição Inválida", exception);
		} 
		return exception;
	}
	
}
