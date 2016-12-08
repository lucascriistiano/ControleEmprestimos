package dominio;

import java.util.Date;

import excecao.EmprestimoInvalidoException;

public interface RegraEmprestimo {
	public /*@ pure @*/ int getDiasNotificacaoPrevia();
	public /*@ pure @*/ double calcularValorFinal(Emprestimo emprestimo, double taxaExtra);
	public /*@ pure @*/ Date calcularDataDevolucao(Emprestimo emprestimo);
	
	/*@
	 @ public exceptional_behavior
	 @	requires dataDevolucao.before(dataEmprestimo);
	 @  signals_only EmprestimoInvalidoException;
	 @*/
	public /*@ pure @*/ void validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao) throws EmprestimoInvalidoException;
}