package visao;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;
import java.util.Scanner;

import controle.GerenciadorClientes;
import dominio.Cliente;
import dominio.ClienteLocador;

public class UIGerenciamentoClientesConsole implements UIGerenciamentoClientes {

	private Scanner in = new Scanner(System.in);
	private GerenciadorClientes gerenciadorClientes = new GerenciadorClientes();
	
	@Override
	public void cadastrarCliente() {
		
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
		
		try {
			dataNascimento = dateFormat.parse(strDataNascimento);
			
			Cliente cliente = new ClienteLocador(codigo,nome,cpf,rg,carteiraMotorista,dataNascimento);
			gerenciadorClientes.cadastrarCliente(cliente);
		} catch (ParseException e) {
			// TODO Lancar excessao
			System.out.println("Impossivel cadastrar cliente");
			e.printStackTrace();
		}
	}

	@Override
	public void removerCliente() {
		
		System.out.println("---------- Remover Cliente ----------");
		
		System.out.print("Codigo: ");
		Long codigo = in.nextLong();
		in.nextLine();

		Cliente cliente = new ClienteLocador(codigo,"");
		gerenciadorClientes.removerCliente(cliente);
		
	}

	@Override
	public void listarClientes() {
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
		
	}

}
