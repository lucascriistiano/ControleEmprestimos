package dominio;

import java.util.Date;

public class TesteComprovante {
	public static void main(String[] args) {
		ComprovanteBuilder comprovantebuilder = new ComprovanteCarroBuilder();
		GeradorDeComprovante geradorDeComprovante = new GeradorDeComprovante(comprovantebuilder);
		
		//Emprestimo emprestimo = new Emprestimo();
		//Comprovante comprovante = geradorDeComprovante.geraComprovante(emprestimo);
		//System.out.println(comprovante.imprimir());
	}
}
