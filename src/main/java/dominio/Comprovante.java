package dominio;

public abstract class Comprovante {

	protected /* @ spec_public @ */ Emprestimo emprestimo;

	public Comprovante(Emprestimo emprestimo) {
		super();
		this.emprestimo = emprestimo;
	}

	public /*@ pure @*/ Emprestimo getEmprestimo() {
		return emprestimo;
	}

	public /* @ pure @ */ abstract void imprimir();
}