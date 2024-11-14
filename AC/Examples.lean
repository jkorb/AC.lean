import AC.Syntax

#check Fml.conj (Fml.var 1) (Fml.var 1)
#eval Fml.conj (Fml.var 1) (Fml.var 1)

#check p_{1} ∨ (p_{1} ∧ ¬p_{2})
#eval p_{1} ∨ (p_{1} ∧ ¬p_{2})

#check p_{1} ↔ (p_{1} ∧ ¬p_{2})
#eval p_{1} ↔ (p_{1} ∧ ¬¬p_{1})
