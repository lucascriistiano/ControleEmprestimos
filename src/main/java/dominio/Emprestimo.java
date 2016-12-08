package dominio;

import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class Emprestimo extends Dominio {
	private /*@ nullable spec_public @*/ Date dataEmprestimo;	//Data de realizacao do emprestimo
	private /*@ nullable spec_public @*/ Date dataDevolucao;		//Data de realizacao do emprestimo
	private /*@ nullable spec_public @*/ Usuario usuario;		//Usuario que efetivou o emprestimo 
	private /*@ nullable spec_public @*/ Cliente cliente;		//Cliente que realizou o emprestimo
	private /*@ nullable spec_public @*/ List<Recurso> recursos;//Lista de recursos emprestados
	
	public Emprestimo() {		
		this.recursos = new ArrayList<Recurso>();
	}
	
	public Emprestimo(Date dataEmprestimo, Usuario usuario, Cliente cliente, List<Recurso> recursos) {		
		this.dataEmprestimo = dataEmprestimo;
		this.usuario = usuario;
		this.cliente = cliente;
		
		this.recursos = new ArrayList<Recurso>(recursos);
	}
	
	public /*@ pure @*/ Date getDataEmprestimo() {
		return dataEmprestimo;
	}

	public void setDataEmprestimo(Date dataEmprestimo) {
		this.dataEmprestimo = dataEmprestimo;
	}
	
	public /*@ pure @*/ Date getDataDevolucao() {
		return dataDevolucao;
	}

	public void setDataDevolucao(Date dataDevolucao) {
		this.dataDevolucao = dataDevolucao;
	}

	public /*@ pure @*/ Usuario getUsuario() {
		return usuario;
	}

	public void setUsuario(Usuario usuario) {
		this.usuario = usuario;
	}

	public /*@ pure @*/ Cliente getCliente() {
		return cliente;
	}

	public void setCliente(Cliente cliente) {
		this.cliente = cliente;
	}

	public void adicionarRecurso(Recurso recurso){
		this.recursos.add(recurso);
	}
	
	public void removerRecurso(Recurso recurso) {
		this.recursos.remove(recurso);
	}
	
	public /*@ pure @*/ List<Recurso> getRecursos() {
		return recursos;
	}

	@Override
	public String toString() {
		return "Emprestimo [dataEmprestimo=" + dataEmprestimo + ", dataDevolucao=" + dataDevolucao + ", usuario="
				+ usuario + ", cliente=" + cliente + ", recursos=" + recursos + ", codigo=" + codigo + "]";
	}

	@Override
	public boolean valido() {
		if(codigo < 0){
			return false;
		} else {
			return true;
		}
	}
	
	
	
}
