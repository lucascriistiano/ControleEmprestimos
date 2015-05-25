package dominio;

import java.util.Calendar;

public class ComprovanteCarro implements Comprovante{

	private Calendar data;
	private Emprestimo emprestimo;
	
	public ComprovanteCarro(Emprestimo emprestimo) {
		this.emprestimo = emprestimo;
	}
	
	public void imprimir() {
		// TODO Auto-generated method stub
		
	}

}
