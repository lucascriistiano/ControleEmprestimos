package dominio;
import java.util.Calendar;

public class ComprovanteCarroBuilder implements ComprovanteBuilder{

	private String empresa;
	private String locador;
	private double valor;
    private Calendar devolucao;
    private long numero;
    private ComprovanteCarro comprovanteCarro;
	
	@Override
	public void buildEmpresa(String nomeEmpresa) {
		this.empresa = nomeEmpresa;
	}

	@Override
	public void buildLocador(String nomeLocador) {
		this.locador = nomeLocador;
	}

	@Override
	public void buildValor(double valor) {
		this.valor = valor;
	}

	@Override
	public void buildDevolucao(Calendar devolucao) {
		this.devolucao = devolucao;
	}

	@Override
	public void buildNumero(long numero) {
		this.numero = numero;
	}

	@Override
	public void instanciarComprovante() {
		this.comprovanteCarro = new ComprovanteCarro(empresa, locador, valor, devolucao, numero);
	}

	@Override
	public Comprovante getComprovante() {
		return this.comprovanteCarro;
	}

}
