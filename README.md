# sae-project-2



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
