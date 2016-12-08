package dominio;

public interface GeradorComprovante {

    public ComprovanteEmprestimo gerarComprovanteEmprestimo(Emprestimo emprestimo);
    public ComprovanteDevolucao gerarComprovanteDevolucao(Emprestimo emprestimo, double valor);
    
}
