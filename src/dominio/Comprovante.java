package dominio;

import java.util.Calendar;

public interface Comprovante {
	String getEmpresa();
    String getLocador();
    double getValor();
    Calendar getDevolucao();
    long getNumero();
    void imprimir();
}