package dominio;

import java.util.Calendar;
import java.util.List;

public interface Comprovante {
	String getEmpresa();
    String getLocador();
    double getValor();
    Calendar getDevolucao();
    long getNumero();
    List<Recurso> getRecursos();
    void imprimir();
}