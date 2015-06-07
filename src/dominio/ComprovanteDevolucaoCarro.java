package dominio;

import java.util.Date;
import java.util.List;

public class ComprovanteDevolucaoCarro extends ComprovanteDevolucao {
    
	public ComprovanteDevolucaoCarro(String empresa, String locador, Long codigo, Date dataEmprestimo, Date dataDevolucao, List<Recurso> recursos, double valor) {
		super(empresa, locador, codigo, dataEmprestimo, dataDevolucao, recursos, valor);
	}

	@Override
	public void imprimir() {
		System.out.println("Nome da empresa de carro: " + this.getEmpresa());
		
		System.out.println("---- Comprovante de Devolucao ----");
		System.out.println("Codigo do aluguel: " + this.getCodigo());
		System.out.println("Nome do locador: " + this.getLocador());
		System.out.println("Data de emprestimo: " + this.getDataEmprestimo());
		System.out.println("Data da devolucao: " + this.getDataDevolucao());
		
		System.out.println("Lista de Veiculos Alugados: ");
		for (Recurso recurso : getRecursos()) {
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
		
		System.out.println("Valor do aluguel: R$ " + this.getValor());
	}
}