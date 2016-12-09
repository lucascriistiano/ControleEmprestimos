package instancialocadoraveiculos;

import java.util.Calendar;
import java.util.Date;
import java.util.concurrent.TimeUnit;

import dominio.Emprestimo;
import dominio.Recurso;
import dominio.RegraEmprestimo;
import excecao.EmprestimoInvalidoException;

public class RegraLocadoraVeiculos implements RegraEmprestimo{
	
	private static final int DIAS_QUILOMETRAGEM_LIVRE = 20;
	private static final int QUILOMETRAGEM_MAXIMA = 4500;
	private static final double TAXA_QUILOMETRO_EXCEDIDO = 0.45;
	private static final int DIAS_PARA_NOTIFICACAO = 2;

	@Override
	public /*@ pure @*/ int getDiasNotificacaoPrevia() {
		return DIAS_PARA_NOTIFICACAO;
	}
	
	@Override
	public /*@ pure @*/ double calcularValorFinal(Emprestimo emprestimo, double taxaExtra) {
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
	public /*@ pure @*/ Date calcularDataDevolucao(Emprestimo emprestimo) {
		//Retorna a data minima para emprestimo (1 diaria)
		Calendar calendar = Calendar.getInstance();
		calendar.setTime(emprestimo.getDataEmprestimo());
		calendar.add(Calendar.DAY_OF_MONTH, 1);
		return calendar.getTime();
	}

	@Override
	public /*@ pure @*/ void validarDataDevolucao(Date dataEmprestimo, Date dataDevolucao) throws EmprestimoInvalidoException {
		if (dataDevolucao.before(dataEmprestimo)){
			throw new EmprestimoInvalidoException("Data de devolução precisa ser após data do empréstimo");
		}
	}

}
