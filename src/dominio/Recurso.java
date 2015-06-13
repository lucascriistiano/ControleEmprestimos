package dominio;

import excecao.RecursoInvalidoException;

public abstract class Recurso {
	
	private Long codigo;
	private String descricao;
	private int categoria;
	private boolean disponivel;
	
	protected Recurso(Long codigo, String descricao, int categoria) {
		this.codigo = codigo;
		this.descricao = descricao;
		this.categoria = categoria;
		this.disponivel = true;
	}
	
	protected Recurso(Long codigo, String descricao, int categoria, boolean disponivel) {
		this.codigo = codigo;
		this.descricao = descricao;
		this.categoria = categoria;
		this.disponivel =  disponivel;
	}
	
	public int getCategoria() {
		return categoria;
	}

	public void setCategoria(int categoria) {
		this.categoria = categoria;
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
