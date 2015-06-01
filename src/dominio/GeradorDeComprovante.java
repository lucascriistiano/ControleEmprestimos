package dominio;

import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;

public class GeradorDeComprovante {

    private ComprovanteBuilder comprovantebuilder;

    public GeradorDeComprovante(ComprovanteBuilder comprovantebuilder) {
        this.comprovantebuilder = comprovantebuilder;
    }

    public Comprovante geraComprovante(Emprestimo emprestimo) {
        this.comprovantebuilder.buildEmpresa(" nome da empresa ");
        this.comprovantebuilder.buildLocador(emprestimo.getCliente().getNome());
        this.comprovantebuilder.buildValor(100); // colocar valor do empréstimo
        Calendar cal = Calendar.getInstance();
        DateFormat format = new SimpleDateFormat("yyyy/mm/dd");
        format.format(emprestimo.getDataDevolucao());
        cal = format.getCalendar();
        this.comprovantebuilder.buildDevolucao(cal);
        this.comprovantebuilder.buildNumero(emprestimo.getCodigo());
        comprovantebuilder.instanciarComprovante();
        Comprovante comprovante = comprovantebuilder.getComprovante();
        return comprovante;
    }
}
