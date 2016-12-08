package dominio;

public abstract class ComprovanteDevolucao extends Comprovante {

	protected /*@ spec_public @*/  double valor;

	public ComprovanteDevolucao(Emprestimo emprestimo, double valor) {
		super(emprestimo);
		this.valor = valor;
	}

	public /*@ pure @*/ double getValor() {
		return valor;
	}
}