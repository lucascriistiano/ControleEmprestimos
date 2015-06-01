package dominio;
import java.util.Calendar;
import java.util.List;

public class ComprovanteCarroBuilder implements ComprovanteBuilder{

	private String empresa;
	private String locador;
	private double valor;
    private Calendar devolucao;
    private long numero;
    private List<Recurso> recursos;
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
		this.comprovanteCarro = new ComprovanteCarro(empresa, locador, valor, devolucao, numero, recursos);
	}

	@Override
	public Comprovante getComprovante() {
		return this.comprovanteCarro;
	}

	@Override
	public void buildRecursos(List<Recurso> recursos) {
		this.recursos = recursos;		
	}

}
