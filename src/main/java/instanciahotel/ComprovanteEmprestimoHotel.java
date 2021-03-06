package instanciahotel;

import java.text.SimpleDateFormat;

import dominio.ComprovanteEmprestimo;
import dominio.Emprestimo;
import dominio.Recurso;

public class ComprovanteEmprestimoHotel extends ComprovanteEmprestimo {
    
	public ComprovanteEmprestimoHotel(Emprestimo emprestimo) {
		super(emprestimo);
	}

	@Override
	public /*@ pure @*/ void imprimir() {
		System.out.println("------- HOTEL 5 ESTRELAS -------");
		
		System.out.println("----- Comprovante de Checkin -----");
		System.out.println("Codigo do aluguel: " + emprestimo.getCodigo());
		System.out.println("Nome do locador: " + emprestimo.getCliente().getNome());
		System.out.println("Data de checkin: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataEmprestimo()));
		System.out.println("Data prevista checkout: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataDevolucao()));
		
		System.out.println("Lista de Quartos Alugados: ");
		for (Recurso recurso : emprestimo.getRecursos()) {
			Quarto quarto = (Quarto) recurso;
			
			System.out.print("\tCodigo: " + quarto.getCodigo());
			System.out.print(" - Descricao: " + quarto.getDescricao());
			System.out.print(" - Area: " + quarto.getArea());
			System.out.print(" - Numero: " + quarto.getNumero());
			System.out.print(" - Quantidade de pessoas: " + quarto.getQuantidadePessoas());
			System.out.print(" - Preco de aluguel: R$ " + quarto.getPreco());
			System.out.println();
		}
	}
}