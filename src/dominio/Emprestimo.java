package dominio;

import java.util.ArrayList;

public class Emprestimo {
	private long numero; // id do empréstimo
	private Usuario usuario;
	private Cliente cliente;
	private ArrayList<Recurso> recursos;
	
	public Emprestimo() {
		this.recursos = new ArrayList<Recurso>();
	}
	
	public void adicionarRecurso(Recurso recurso){
		this.recursos.add(recurso);
	}
	
	public ArrayList<Recurso> todosRecursos() {
		return this.recursos;
	}

	public Usuario getUsuario() {
		return usuario;
	}

	public void setUsuario(Usuario usuario) {
		this.usuario = usuario;
	}

	public Cliente getCliente() {
		return cliente;
	}

	public void setCliente(Cliente cliente) {
		this.cliente = cliente;
	}

	public long getNumero() {
		return numero;
	}

	public void setNumero(long numero) {
		this.numero = numero;
	}
	
}
