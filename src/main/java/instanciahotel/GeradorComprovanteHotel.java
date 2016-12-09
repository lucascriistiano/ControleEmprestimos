package instanciahotel;

import dominio.ComprovanteDevolucao;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.GeradorComprovante;

public class GeradorComprovanteHotel implements GeradorComprovante {

	/*@ also
	  @ ensures \result != null; 
	  @*/
	@Override
	public /*@ pure @*/ ComprovanteEmprestimo gerarComprovanteEmprestimo(Emprestimo emprestimo) {
		return new ComprovanteEmprestimoHotel(emprestimo);
	}

	/*@ also
	  @ ensures \result != null; 
	  @*/
	@Override
	public /*@ pure @*/ ComprovanteDevolucao gerarComprovanteDevolucao(Emprestimo emprestimo, double valor) {
		return new ComprovanteDevolucaoHotel(emprestimo, valor);
	}

}
