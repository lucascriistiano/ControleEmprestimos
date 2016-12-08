package instanciahotel;

import dominio.ComprovanteDevolucao;
import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.GeradorComprovante;

public class GeradorComprovanteHotel implements GeradorComprovante {

	@Override
	public ComprovanteEmprestimo gerarComprovanteEmprestimo(Emprestimo emprestimo) {
		return new ComprovanteEmprestimoHotel(emprestimo);
	}

	@Override
	public ComprovanteDevolucao gerarComprovanteDevolucao(Emprestimo emprestimo, double valor) {
		return new ComprovanteDevolucaoHotel(emprestimo, valor);
	}

}
