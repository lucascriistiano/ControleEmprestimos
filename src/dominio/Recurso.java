package dominio;

import excecao.RecursoInvalidoException;

public abstract class Recurso {
	
	private Long codigo;
	private String descricao;
	private boolean disponivel;
	
	protected Recurso(Long codigo, String descricao) {
		this.codigo = codigo;
		this.descricao = descricao;
		this.disponivel = true;
	}
	
	protected Recurso(Long codigo, String descricao, boolean disponivel) {
		this.codigo = codigo;
		this.descricao = descricao;
		this.disponivel =  disponivel;
	}
	
	public Long getCodigo() {
		return codigo;
	}

	public void setCodigo(Long codigo) {
		this.codigo = codigo;
	}

	public String getDescricao() {
		return descricao;
	}

	public void setDescricao(String descricao) {
		this.descricao = descricao;
	}

	public boolean isDisponivel() {
		return disponivel;
	}

	public void setDisponivel(boolean disponivel) {
		this.disponivel = disponivel;
	}

	public abstract void alocar();
	public abstract void desalocar();
	public abstract boolean validar() throws RecursoInvalidoException;
}
