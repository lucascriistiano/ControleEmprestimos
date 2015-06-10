package visao;

import java.util.List;
import java.util.Scanner;

import controle.GerenciadorRecursos;
import dominio.Carro;
import dominio.Quarto;
import dominio.Recurso;
import excecao.DataException;

public class UIGerenciamentoRecursosConsoleQuarto implements UIGerenciamentoRecursos {

	private GerenciadorRecursos gerenciadorRecursos = new GerenciadorRecursos();
	private Scanner in = new Scanner(System.in);
	
	@Override
	public void cadastrarRecurso() {
		try {
			System.out.println("---------- Cadastrar Quarto ----------");
			
			System.out.print("Codigo: ");
			Long codigo = in.nextLong();
			in.nextLine();
			System.out.print("Descricao: ");
			String descricao = in.nextLine();
			System.out.print("Área: ");
			double area = in.nextDouble();
			System.out.print("Número: ");
			int numero = in.nextInt();
			System.out.print("Quantidade de pessoas: ");
			int quantidadePessoas = in.nextInt();
			System.out.print("Preco de aluguel: ");
			double preco = in.nextDouble();
					
			Recurso recurso = new Quarto(codigo, descricao, area, numero, quantidadePessoas, preco);
			
			gerenciadorRecursos.cadastrarRecurso(recurso);
		} catch (DataException e) {
			System.out.println("Erro ao armazenar dados do recurso. Erro: " + e.getMessage());
		}
	}

	@Override
	public void removerRecurso() {
		try {
			System.out.println("---------- Remover Quarto ----------");
		
			System.out.print("Codigo: ");
			Long codigo = in.nextLong();
			in.nextLine();
			
			Recurso recurso = new Quarto(codigo,"");
		
			gerenciadorRecursos.removerRecurso(recurso);
		} catch (DataException e) {
			System.out.println("Erro ao remover registro do recurso. Erro: " + e.getMessage());
		}
	}

	@Override
	public void listarRecursos() {
		try {
			List<Recurso> recursos = gerenciadorRecursos.listarRecursos();
		
			System.out.println("---------- Lista de Quartos ----------");
			
			for(Recurso recurso : recursos) {
				Quarto quarto = (Quarto) recurso;
				
				System.out.print("Codigo: " + quarto.getCodigo());
				System.out.print(" - Descricao: " + quarto.getDescricao());
				System.out.print(" - Área: " + quarto.getArea());
				System.out.print(" - Número: " + quarto.getNumero());
				System.out.print(" - Quantidade de pessoas: " + quarto.getQuantidadePessoas());
				System.out.print(" - Preco de aluguel: " + quarto.getPreco());
				System.out.println();
			}
		} catch (DataException e) {
			System.out.println("Erro ao recuperar registros dos recursos. Erro: " + e.getMessage());
		}
	}

}
