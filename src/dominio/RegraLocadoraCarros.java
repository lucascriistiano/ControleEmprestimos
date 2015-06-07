package dominio;

import java.util.Calendar;
import java.util.Date;
import java.util.concurrent.TimeUnit;

public class RegraLocadoraCarros implements RegraEmprestimo{
	
	private static final int DIAS_QUILOMETRAGEM_LIVRE = 20;
	private static final int QUILOMETRAGEM_MAXIMA = 4500;
	private static final double TAXA_QUILOMETRO_EXCEDIDO = 0.45;
	
	@Override
	public boolean prazoExpirado(Emprestimo emprestimo) {
		Date dataAtual = Calendar.getInstance().getTime();
		
		if((dataAtual.getTime() - emprestimo.getDataDevolucao().getTime()) >= 0)			
			return false;
		else
			return true;
	}

	@Override
	public double calcularValorFinal(Emprestimo emprestimo, double taxaExtra) {
		Date dataAtual = Calendar.getInstance().getTime();
		Long msDiff = dataAtual.getTime() - emprestimo.getDataEmprestimo().getTime();
		Long diasEmprestimo = TimeUnit.DAYS.convert(msDiff, TimeUnit.MILLISECONDS);
		
		double valorFinal = 0;
		
		if(diasEmprestimo > 1) {
			if(diasEmprestimo <= DIAS_QUILOMETRAGEM_LIVRE) {
				for(Recurso recurso : emprestimo.getRecursos()) {
					Carro carro = (Carro) recurso;
					valorFinal += (carro.getPreco() * diasEmprestimo);
				}
			}
			else {
				for(Recurso recurso : emprestimo.getRecursos()) {
					Carro carro = (Carro) recurso;
					valorFinal += (carro.getPreco() * diasEmprestimo);
					
					int quilometragemPercorrida = carro.getQuilometragemFinal() - carro.getQuilometragemInicial();
					if(quilometragemPercorrida > QUILOMETRAGEM_MAXIMA) {
						int quilometragemExcedida = quilometragemPercorrida - QUILOMETRAGEM_MAXIMA;
						valorFinal += quilometragemExcedida*TAXA_QUILOMETRO_EXCEDIDO;
					}
				}
			}
		}
		else {
			for(Recurso recurso : emprestimo.getRecursos()) {
				Carro carro = (Carro) recurso;
				valorFinal += carro.getPreco();
			}
		}
		
		if(taxaExtra > 0)
			valorFinal += taxaExtra;
	
		return valorFinal;
	}

	@Override
	public Date calcularDataDevolucao(Emprestimo emprestimo) {
		//Retorna a data minima para emprestimo (1 diaria)
		Calendar calendar = Calendar.getInstance();
		calendar.add(Calendar.DAY_OF_MONTH, 1);
		return calendar.getTime();
	}

	@Override
	public boolean validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao) {
		//Verificar se o periodo de emprestimo eh de pelo menos 1 dia (prazo minimo) 
		Long msDiff = dataDevolucao.getTime() - dataEmprestimo.getTime();
		Long diasDiff = TimeUnit.DAYS.convert(msDiff, TimeUnit.MILLISECONDS);
		
		if(diasDiff >= 1)
			return true;
		else
			return false;
	}

}