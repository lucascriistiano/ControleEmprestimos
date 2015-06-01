package dominio;
import java.util.Calendar;

public interface ComprovanteBuilder {
	void buildEmpresa( String nomeEmpresa );
    void buildLocador( String nomeLocador );
    void buildValor(double valor);
    void buildDevolucao(Calendar date);
    void buildNumero(long numero );
    
    void instanciarComprovante();
    Comprovante getComprovante();
}
