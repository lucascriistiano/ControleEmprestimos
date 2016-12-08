package test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import controle.GerenciadorClientesTest;
import controle.GerenciadorEmprestimosTest;
import controle.GerenciadorRecursosTest;
import controle.GerenciadorUsuariosTest;
import controle.VerificadorPrazosTest;
import dominio.GeradorComprovanteTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	GerenciadorClientesTest.class,
	GerenciadorEmprestimosTest.class,
	GerenciadorRecursosTest.class,
	GerenciadorUsuariosTest.class,
	VerificadorPrazosTest.class,
	GeradorComprovanteTest.class
})
public class SuiteDeTestes {

}
