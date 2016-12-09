package dominio;

public abstract class ComprovanteDevolucao extends Comprovante {

	protected /*@ spec_public @*/  double valor;

	//@ protected initially emprestimo != null;	
	public ComprovanteDevolucao(Emprestimo emprestimo, double valor) {
		super(emprestimo);
		this.valor = valor;
	}

	public /*@ pure @*/ double getValor() {
		return valor;
	}
}