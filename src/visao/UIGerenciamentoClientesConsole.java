package visao;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;
import java.util.Scanner;

import controle.GerenciadorClientes;
import dominio.Cliente;
import dominio.ClienteLocador;
import excecao.ClienteInvalidoException;
import excecao.DataException;

public class UIGerenciamentoClientesConsole implements UIGerenciamentoClientes {

	private Scanner in = new Scanner(System.in);
	private GerenciadorClientes gerenciadorClientes = new GerenciadorClientes();
	
	@Override
	public void cadastrarCliente() {
		
		try {
			System.out.println("---------- Cadastrar Cliente ----------");
			
			System.out.print("Codigo: ");
			Long codigo = in.nextLong();
			in.nextLine();
			System.out.print("Nome: ");
			String nome = in.nextLine();
			System.out.print("CPF: ");
			String cpf = in.nextLine();
			System.out.print("RG: ");
			String rg = in.nextLine();
			System.out.print("Carteira de Motorista: ");
			String carteiraMotorista = in.nextLine();
			System.out.print("Data de Nascimento (dd/mm/aaaa): ");
			String strDataNascimento = in.nextLine();
			SimpleDateFormat dateFormat = new SimpleDateFormat("dd/MM/yyyy");
			Date dataNascimento;
		
			dataNascimento = dateFormat.parse(strDataNascimento);
			
			Cliente cliente = new ClienteLocador(codigo,nome,cpf,rg,carteiraMotorista,dataNascimento);
			gerenciadorClientes.cadastrarCliente(cliente);
		
		} catch (DataException e) {
			System.out.println("Erro ao armazenar dados do cliente. Erro: " + e.getMessage());
		} catch (ClienteInvalidoException e) {
			System.out.println("Cliente invalido inserido. Erro: " + e.getMessage());
		} catch (ParseException e) {
			System.out.println("Erro ao cadastrar data de nascimento. Verifique o formato inserido.");
		}
	}

	@Override
	public void removerCliente() {
		
		try {
			System.out.println("---------- Remover Cliente ----------");
			
			System.out.print("Codigo: ");
			Long codigo = in.nextLong();
			in.nextLine();
	
			Cliente cliente = new ClienteLocador(codigo,"");
			gerenciadorClientes.removerCliente(cliente);
		
		} catch (DataException e) {
			System.out.println("Erro ao remover registro do cliente. Erro: " + e.getMessage());
		}
	}

	@Override
	public void listarClientes() {
		
		try {
			List<Cliente> clientes = gerenciadorClientes.listarClientes();
		
			System.out.println("---------- Lista de Clientes ----------");
			
			for(Cliente cliente : clientes) {
				ClienteLocador clienteLocador = (ClienteLocador) cliente;
				
				System.out.print("Codigo: " + clienteLocador.getCodigo());
				System.out.print(" - Nome: " + clienteLocador.getNome());
				System.out.print(" - CPF: " + clienteLocador.getCpf());
				System.out.print(" - RG: " + clienteLocador.getRg());
				System.out.print(" - Carteira de Motorista: " + clienteLocador.getCarteiraMotorista());
				System.out.print(" - Data de Nascimento: " + new SimpleDateFormat("dd/MM/yyyy").format(clienteLocador.getDataNascimento()));
				System.out.print(" - Idade: " + clienteLocador.getIdade());
				System.out.println();
			}
			
		} catch (DataException e) {
			System.out.println("Erro ao recuperar registros dos clientes. Erro: " + e.getMessage());
		}
	}

}
