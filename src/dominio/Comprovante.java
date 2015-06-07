package dominio;

import java.util.Date;
import java.util.List;

public abstract class Comprovante {
	private String empresa;
	private String locador;
	private Long codigo;
	private Date dataEmprestimo;
	private Date dataDevolucao;
	private List<Recurso> recursos;
	
	public Comprovante(String empresa, String locador, Long codigo, Date dataEmprestimo, Date dataDevolucao, List<Recurso> recursos) {
		this.empresa = empresa;
		this.locador = locador;
		this.codigo = codigo;
		this.dataEmprestimo = dataEmprestimo;
		this.dataDevolucao = dataDevolucao;
		this.recursos = recursos;
	}
	
	public String getEmpresa() {
		return empresa;
	}
	
    public String getLocador() {
		return locador;
	}
    
    public Long getCodigo() {
		return codigo;
	}
    
    public Date getDataEmprestimo() {
		return dataEmprestimo;
	}
    
    public Date getDataDevolucao() {
		return dataDevolucao;
	}
    
    public List<Recurso> getRecursos() {
		return recursos;
	}
    
    public abstract void imprimir();
}