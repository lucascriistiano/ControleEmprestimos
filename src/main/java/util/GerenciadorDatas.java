package util;

import java.util.Calendar;
import java.util.Date;

public class GerenciadorDatas {

	public /*@ pure @*/ Date getDataAtual() {
		return Calendar.getInstance().getTime();
	}
	
}