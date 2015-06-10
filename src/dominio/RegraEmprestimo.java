package dominio;

import java.util.Date;

import excecao.EmprestimoInvalidoException;

public interface RegraEmprestimo {
	public int getDiasNotificacaoPrevia();
	public double calcularValorFinal(Emprestimo emprestimo, double taxaExtra);
	public Date calcularDataDevolucao(Emprestimo emprestimo);
	public boolean validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao) throws EmprestimoInvalidoException;
}