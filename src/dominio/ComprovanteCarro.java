package dominio;

import java.util.Date;

public class ComprovanteCarro implements Comprovante{

	private Date data;
	private Emprestimo emprestimo;
	
	public ComprovanteCarro(Emprestimo emprestimo) {
		this.emprestimo = emprestimo;
	}
	
	public void imprimir() {
		// TODO Auto-generated method stub
		
	}

}
