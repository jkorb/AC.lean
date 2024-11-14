namespace Formula

inductive Fml : Type where
  | var   : Nat → Fml
  | neg   : Fml → Fml
  | conj  : Fml → Fml  → Fml 
  | disj  : Fml → Fml  → Fml 
  deriving DecidableEq

prefix:50 "¬" => Fml.neg
infixr:20 " ∧ " => Fml.conj
infixr:20 " ∨ " => Fml.disj
notation "p_{" i "}"=> Fml.var i

def fmlToStr : Fml → String
  | Fml.var i  => "p" ++ "_" ++ toString i ++ ""
  | Fml.neg A => "¬" ++ fmlToStr A 
  | Fml.conj A B   => "(" ++ fmlToStr A ++ " ∧ " ++ fmlToStr B ++ ")"
  | Fml.disj A B   => "(" ++ fmlToStr A ++ " ∨ " ++ fmlToStr B ++ ")"

instance : Repr Fml := ⟨fun t _ => fmlToStr t⟩
instance : ToString Fml := ⟨fmlToStr⟩

end Formula

namespace Equivalence

open Formula

inductive Eqv : Type
| eqv : Fml → Fml  → Eqv

infix:10 " ↔ " => Eqv.eqv

def eqvToStr : Eqv → String
  | Eqv.eqv A B  => fmlToStr A ++ " ↔ " ++ fmlToStr B

instance : Repr Eqv := ⟨fun t _ => eqvToStr t⟩
instance : ToString Eqv := ⟨eqvToStr⟩

end Equivalence

namespace Substitution

open Formula
open Formula.Fml

def subs : Fml → Nat → Fml → Fml
  | var n, i, B    => if i = n then B else var n
  | neg P, i, B    => ¬ (subs P i B)
  | conj P Q, i, B => (subs P i B) ∧ (subs Q i B)
  | disj P Q, i, B => (subs P i B) ∨ (subs Q i B)

notation A "[" i ":=" B "]" => subs A i B

end Substitution

namespace Occurrences

open Formula

inductive OnlyPosIn : Nat → Fml → Prop where
  | var_pos {i} : OnlyPosIn i (Fml.var i)
  | conj_pos {i P Q} : OnlyPosIn i P → OnlyPosIn i Q → OnlyPosIn i (Fml.conj P Q)
  | disj_pos {i P Q} : OnlyPosIn i P → OnlyPosIn i Q → OnlyPosIn i (Fml.disj P Q)

end Occurrences
