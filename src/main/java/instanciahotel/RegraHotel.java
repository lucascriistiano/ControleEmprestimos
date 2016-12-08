package instanciahotel;

import java.util.Calendar;
import java.util.Date;
import java.util.concurrent.TimeUnit;

import dominio.Emprestimo;
import dominio.Recurso;
import dominio.RegraEmprestimo;
import excecao.EmprestimoInvalidoException;

public class RegraHotel implements RegraEmprestimo{

	private static final int DIAS_PARA_NOTIFICACAO = 2;
	
	@Override
	public int getDiasNotificacaoPrevia() {
		return DIAS_PARA_NOTIFICACAO;
	}
	
	@Override
	public double calcularValorFinal(Emprestimo emprestimo, double taxaExtra) {
		Date dataAtual = Calendar.getInstance().getTime();
		Long msDiff = dataAtual.getTime() - emprestimo.getDataEmprestimo().getTime();
		Long diasEmprestimo = TimeUnit.DAYS.convert(msDiff, TimeUnit.MILLISECONDS);
		
		double valorFinal = 0;
		
		for(Recurso recurso : emprestimo.getRecursos()) {
			Quarto quarto = (Quarto) recurso;
			valorFinal += (quarto.getPreco() * diasEmprestimo);
		}
		
		if(taxaExtra > 0)
			valorFinal += taxaExtra;
		
		return valorFinal;
	}

	@Override
	public Date calcularDataDevolucao(Emprestimo emprestimo) {
		//Retorna a data minima para emprestimo (1 dia)
		Calendar calendar = Calendar.getInstance();
		calendar.setTime(emprestimo.getDataEmprestimo());
		calendar.add(Calendar.DAY_OF_MONTH, 1);
		return calendar.getTime();
	}

	@Override
	public boolean validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao) throws EmprestimoInvalidoException {
		Emprestimo emprestimo = new Emprestimo();
		emprestimo.setDataEmprestimo(dataEmprestimo);
		emprestimo.setDataDevolucao(dataDevolucao);
		
		Date dataDevolucaoPrevista = calcularDataDevolucao(emprestimo);
		
		if (dataDevolucao.after(dataDevolucaoPrevista)){
			throw new EmprestimoInvalidoException("Passou do limite de devolução");
		}
		
		return true;
		
	}
	
	
}
