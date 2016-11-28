package dominio;

import java.util.Date;
import java.util.List;

public abstract class Comprovante {
	private /*@ spec_public @*/ String empresa;
	private /*@ spec_public @*/ String locador;
	private /*@ spec_public @*/ Long codigo;
	private /*@ spec_public @*/ Date dataEmprestimo;
	private /*@ spec_public @*/ Date dataDevolucao;
	private /*@ spec_public @*/ List<Recurso> recursos;
	
	public Comprovante(String empresa, String locador, Long codigo, Date dataEmprestimo, Date dataDevolucao, List<Recurso> recursos) {
		this.empresa = empresa;
		this.locador = locador;
		this.codigo = codigo;
		this.dataEmprestimo = dataEmprestimo;
		this.dataDevolucao = dataDevolucao;
		this.recursos = recursos;
	}
	
	public String /*@ pure @*/ getEmpresa() {
		return empresa;
	}
	
    public String /*@ pure @*/ getLocador() {
		return locador;
	}
    
    public Long /*@ pure @*/ getCodigo() {
		return codigo;
	}
    
    public Date /*@ pure @*/ getDataEmprestimo() {
		return dataEmprestimo;
	}
    
    public Date /*@ pure @*/ getDataDevolucao() {
		return dataDevolucao;
	}
    
    public List<Recurso> /*@ pure @*/ getRecursos() {
		return recursos;
	}
    
    public abstract void imprimir();
}