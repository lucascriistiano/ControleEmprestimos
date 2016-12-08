package dominio;

public class HistoricoEmprestimo extends Dominio {

	private /*@ spec_public @*/ Emprestimo emprestimo;
	
	public HistoricoEmprestimo(Emprestimo emprestimo) {
		super();
		this.emprestimo = emprestimo;
	}

	public /*@ pure @*/ Emprestimo getEmprestimo() {
		return emprestimo;
	}

	@Override
	public /*@ pure @*/ boolean valido() {
		return emprestimo.getCodigo() > 0;
	}
	
		
}
