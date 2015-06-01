package dominio;
import java.util.Calendar;
import java.util.List;

public interface ComprovanteBuilder {
	void buildEmpresa( String nomeEmpresa );
    void buildLocador( String nomeLocador );
    void buildValor(double valor);
    void buildDevolucao(Calendar date);
    void buildNumero(long numero );
    void buildRecursos(List<Recurso> recursos);
    
    void instanciarComprovante();
    Comprovante getComprovante();
}
