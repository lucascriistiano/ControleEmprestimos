package dominio;

import excecao.EmprestimoInvalidoException;

public interface GeradorComprovante {

	/*@
	 @  requires emprestimo.valido();
	 @	ensures (\forall int i; 
	 @				0 <= i && i < emprestimo.getRecursos().size();
	 @				( \result.getEmprestimo().getRecursos() ).contains( ((Recurso) emprestimo.getRecursos().get(i)) ) );	
	 @	ensures \result.getEmprestimo().equals(emprestimo);
	 @*/
    public ComprovanteEmprestimo gerarComprovanteEmprestimo(Emprestimo emprestimo) throws EmprestimoInvalidoException;
    
	/*@
	 @  requires emprestimo.valido();
	 @	ensures (\forall int i; 
	 @				0 <= i && i < emprestimo.getRecursos().size();
	 @				( \result.getEmprestimo().getRecursos() ).contains( ((Recurso) emprestimo.getRecursos().get(i)) ) );	
	 @	ensures \result.getEmprestimo().equals(emprestimo);
	 @	ensures \result.getValor() >= 0;
	 @*/
    public ComprovanteDevolucao gerarComprovanteDevolucao(Emprestimo emprestimo, double valor);
    
}
