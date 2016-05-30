# sae-project-2

APRON explained: http://apron.cri.ensmp.fr/library/expose_mine_CEA_2007.pdf

	http://www.inrialpes.fr/pop-art/people/bjeannet/bjeannet-forge/bddapron/html/Apron.html

Texpr1Node isihlukanisi = new Texpr1VarNode(((JimpleLocal) divisor).getName());
//Tcons1 isNotZeroConstraint = new Tcons1(state.get().getEnvironment(), Tcons1.DISEQ, isihlukanisi);
Tcons1 isGreaterZeroConstraint = new Tcons1(state.get().getEnvironment(), Tcons1.SUP, isihlukanisi);
Tcons1 isGreaterEqualZeroConstraint = new Tcons1(state.get().getEnvironment(), Tcons1.SUPEQ, isihlukanisi);
try {
	if (! (state.get().satisfy(Analysis.man, isGreaterZeroConstraint) || !(state.get().satisfy(Analysis.man, isGreaterEqualZeroConstraint)))) return false;
}
catch (ApronException e) {
	e.printStackTrace();
} 

TND_May2 abort
TND_May5 has false result
