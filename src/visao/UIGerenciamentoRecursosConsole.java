package visao;

import java.util.List;
import java.util.Scanner;

import controle.GerenciadorRecursos;
import dominio.Carro;
import dominio.Recurso;

public class UIGerenciamentoRecursosConsole implements UIGerenciamentoRecursos {

	private GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
	private Scanner in = new Scanner(System.in);
	
	@Override
	public void cadastrarRecurso() {
		System.out.println("---------- Cadastrar Carro ----------");
		System.out.print("Codigo: ");
		Long codigo = in.nextLong();
		in.nextLine();
		System.out.print("Descricao: ");
		String descricao = in.nextLine();
		System.out.print("Placa: ");
		String placa = in.nextLine();
		System.out.print("Modelo: ");
		String modelo = in.nextLine();
		System.out.print("Fabricante: ");
		String fabricante = in.nextLine();
		System.out.print("Cor: ");
		String cor = in.nextLine();
		System.out.print("Preco de aluguel: ");
		double preco = in.nextDouble();
		
		Recurso recurso = new Carro(codigo, descricao, placa, modelo, fabricante, cor, preco);
		gerenciadorRecursos.cadastrarRecurso(recurso);
	}

	@Override
	public void removerRecurso() {
		System.out.println("---------- Remover Carro ----------");
		System.out.print("Codigo: ");
		Long codigo = in.nextLong();
		in.nextLine();
		
		Recurso recurso = new Carro(codigo,"");
		gerenciadorRecursos.removerRecurso(recurso);
	}

	@Override
	public void listarRecursos() {
		List<Recurso> recursos = gerenciadorRecursos.listarRecursos();
		
		System.out.println("---------- Lista de Carros ----------");
		
		for(Recurso recurso : recursos) {
			Carro carro = (Carro) recurso;
			
			System.out.print("Codigo: " + carro.getCodigo());
			System.out.print(" - Descricao: " + carro.getDescricao());
			System.out.print(" - Placa: " + carro.getPlaca());
			System.out.print(" - Modelo: " + carro.getModelo());
			System.out.print(" - Fabricante: " + carro.getFabricante());
			System.out.print(" - Cor: " + carro.getCor());
			System.out.print(" - Preco de aluguel: " + carro.getPreco());
			System.out.println();
		}
	}

}
