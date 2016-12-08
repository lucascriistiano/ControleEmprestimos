package instancialocadoraveiculos;

import java.text.SimpleDateFormat;

import dominio.ComprovanteDevolucao;
import dominio.Emprestimo;
import dominio.Recurso;

public class ComprovanteDevolucaoLocadoraVeiculos extends ComprovanteDevolucao {
    
	
	public ComprovanteDevolucaoLocadoraVeiculos(Emprestimo emprestimo, double valor) {
		super(emprestimo, valor);
	}

	@Override
	public void imprimir() {
		System.out.println("------- LOCADORA VEICULOS -------");
		
		System.out.println("----- Comprovante de Devolucao -----");
		System.out.println("Codigo do aluguel: " + emprestimo.getCodigo());
		System.out.println("Nome do locador: " + emprestimo.getCliente().getNome());
		System.out.println("Data de emprestimo: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataEmprestimo()));
		System.out.println("Data da devolucao: " + new SimpleDateFormat("dd/MM/yyyy").format(emprestimo.getDataDevolucao()));
		
		System.out.println("Lista de Veiculos Alugados: ");
		for (Recurso recurso : emprestimo.getRecursos()) {
			Carro carro = (Carro) recurso;
			
			System.out.print("Codigo: " + carro.getCodigo());
			System.out.print(" - Descricao: " + carro.getDescricao());
			System.out.print(" - Placa: " + carro.getPlaca());
			System.out.print(" - Modelo: " + carro.getModelo());
			System.out.print(" - Fabricante: " + carro.getFabricante());
			System.out.print(" - Cor: " + carro.getCor());
			System.out.print(" - Quilometragem inicial: " + carro.getQuilometragemInicial() + "km");
			System.out.print(" - Preco de aluguel: " + carro.getPreco());
			System.out.println();
		}
		
		System.out.println("Valor do aluguel: R$ " + valor);
	}
}