package dominio;

import java.util.Date;

public interface RegraEmprestimo {
	public boolean prazoExpirado(Emprestimo emprestimo);
	public double calcularValorFinal(Emprestimo emprestimo, double taxaExtra);
	public Date calcularDataDevolucao(Emprestimo emprestimo);
	public boolean validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao);
}