package dominio;

public abstract class ComprovanteEmprestimo extends Comprovante {

	//@ protected initially emprestimo != null;	
	public ComprovanteEmprestimo(Emprestimo emprestimo) {
		super(emprestimo);
	}

}