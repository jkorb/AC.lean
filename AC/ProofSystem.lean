import AC.syntax

namespace AC

open Formula
open Equivalence

inductive Thm : Eqv → Prop
| E1  : {A : Fml} →  Thm (A ↔ ¬¬A)
| E2  : { A : Fml} → Thm (A ↔ (A ∧ A))
| E3  : { A B : Fml} → Thm ((A ∧ B) ↔ (B ∧ A))
| E4  : { A B C : Fml} → Thm (((A ∧ B) ∧ C) ↔ (A ∧ (B ∧ C)))
| E5  : { A : Fml} → Thm (A ↔ (A ∨ A))
| E6  : { A B : Fml} → Thm ((A ∨ B) ↔ (B ∨ A))
| E7  : { A B C : Fml} → Thm (((A ∨ B) ∨ C) ↔ (A ∨ (B ∨ C)))
| E8  : { A B : Fml} → Thm (¬(A ∧ B) ↔ (¬A ∨ ¬B))
| E9  : { A B : Fml} → Thm (¬(A ∨ B) ↔ (¬A ∧ ¬B))
| E10 : { A B C : Fml} →  Thm ((A ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ (A ∧ C)))
| E11 : { A B C : Fml} → Thm ((A ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C)))
| E12 : {A B : Fml} → (Thm (A ↔ B)) → (Thm (B ↔ A))
| E13 : {A B C : Fml} → Thm (A ↔ B) → Thm (B ↔ C) → Thm (A ↔ C)
| E14 : {A B C : Fml} → Thm (A ↔ B) → (Thm ((A ∧ C) ↔ B ∧ C))
| E15 : {A B C : Fml} → (Thm (A ↔ B)) → Thm ((A ∨ C) ↔ (B ∨ C))

infix:25 " ⊣⊢ " => (fun A B => Thm (A ↔ B))

notation "first_de_morgan" => Thm.E8
notation "second_de_morgan" => Thm.E9
notation "first_distribution" => Thm.E10
notation "second_distribution" => Thm.E11

theorem reflexivity { A : Fml} : A ⊣⊢ A := by
  have h : (A ⊣⊢ ¬¬A) := Thm.E1
  have g : (¬¬A ⊣⊢ A) := Thm.E12 h
  exact Thm.E13 h g

end AC

section Admissibility 

open Formula
open Substitution
open Occurrences
open AC
open AC.Thm

theorem admissibility_of_PR (A B C : Fml) (i : Nat): (OnlyPosIn i C) → (A ⊣⊢ B) → (C[i := A] ⊣⊢ (C[i := B])) := by
  intro h_pos h_eqv
  induction h_pos with
  | var_pos => 
    unfold subs
    simp [if_pos]
    exact h_eqv
  | @conj_pos P Q hP hQ ihP ihQ =>  
    have step_1 : (P[i := A] ∧ Q[i := A]) ⊣⊢ (P[i := B] ∧ Q[i := A]) := by
      apply E14 ihP
    have step_2 : (Q[i := A] ∧ P[i := B]) ⊣⊢ (Q[i := B] ∧ P[i := B]) := by
      apply E14 ihQ
    have step_3 : (P[i := B] ∧ Q[i := A]) ⊣⊢ (Q[i := B] ∧ P[i := B]) := by
      apply E13 
      apply @E3 (P[i:=B]) (Q[i:=A]) 
      apply step_2
    have step_4 : (P[i := A] ∧ Q[i := A]) ⊣⊢  (Q[i := B] ∧ P[i := B]) := by
      apply E13 
      apply step_1
      apply step_3
    have step_5 : (P[i := A] ∧ Q[i := A]) ⊣⊢  (P[i := B] ∧ Q[i := B]) := by
      apply E13
      apply step_4
      apply @E3 (Q[i:=B]) (P[i:=B])
    unfold subs
    exact step_5
  | @disj_pos P Q hP hQ ihP ihQ =>  
    have step_1 : (P[i := A] ∨ Q[i := A]) ⊣⊢ (P[i := B] ∨ Q[i := A]) := by
      apply E15 ihP
    have step_2 : (Q[i := A] ∨ P[i := B]) ⊣⊢ (Q[i := B] ∨ P[i := B]) := by
      apply E15 ihQ
    have step_3 : (P[i := B] ∨ Q[i := A]) ⊣⊢ (Q[i := B] ∨ P[i := B]) := by
      apply E13 
      apply @E6 (P[i:=B]) (Q[i:=A]) 
      apply step_2
    have step_4 : (P[i := A] ∨ Q[i := A]) ⊣⊢  (Q[i := B] ∨ P[i := B]) := by
      apply E13 
      apply step_1
      apply step_3
    have step_5 : (P[i := A] ∨ Q[i := A]) ⊣⊢  (P[i := B] ∨ Q[i := B]) := by
      apply E13
      apply step_4
      apply @E6 (Q[i:=B]) (P[i:=B])
    unfold subs
    exact step_5

theorem admissibility_of_NR (A B : Fml) : (A ⊣⊢ B) → (¬A ⊣⊢ ¬B) := by
  intro h_eqv
  cases h_eqv with
  | E1 => 
    apply E1
  | E2 => 
    have step_1 : ¬(A ∧ A) ⊣⊢ (¬A ∨ ¬A) := by
      exact E8 
    have step_2 : (¬A ∨ ¬A)⊣⊢ ¬A := by
      apply E12
      exact E5
    have step_3 : ¬(A ∧ A) ⊣⊢  ¬A := by
      apply E13
      exact step_1
      exact step_2
    apply E12
    exact step_3
  | @E3 A B => 
    have step_1 : ¬(A ∧ B) ⊣⊢ (¬A ∨ ¬B) := by
      exact E8
    have step_2 : (¬A ∨ ¬B) ⊣⊢ (¬B ∨ ¬A) := by
      exact E6
    have step_3 : ¬(A ∧ B) ⊣⊢ (¬B ∨ ¬A) := by
      apply E13
      exact step_1
      exact step_2
    have step_4: (¬B ∨ ¬A) ⊣⊢ ¬(B ∧ A) := by
      apply E12
      exact E8
    have step_5 : ¬(A ∧ B) ⊣⊢ ¬(B ∧ A) := by
      apply E13
      exact step_3
      exact step_4
    exact step_5
  | @E4 A B C => 
    have step_1 : ¬((A ∧ B) ∧ C) ⊣⊢ (¬(A ∧ B) ∨ ¬C) := by
      exact E8
    have step_2 : (¬(A ∧ B) ∨ ¬C) ⊣⊢ ((¬A ∨ ¬B) ∨ ¬C) := by
      apply E15
      exact E8
    have step_3: ((¬A ∨ ¬B) ∨ ¬C) ⊣⊢ (¬A ∨ (¬B ∨ ¬C)) := by
      exact E7
    have step_4: (¬A ∨ (¬B ∨ ¬C)) ⊣⊢ (¬A ∨ ¬(B ∧ C)) := by
      apply E13
      apply E13 
      exact E6
      apply E15
      apply E12
      exact E8
      apply E6
    have step_5 : (¬A ∨ ¬(B ∧ C)) ⊣⊢ ¬(A ∧ (B ∧ C)) := by
      apply E12
      exact E8
    have step_6 : ¬((A ∧ B) ∧ C) ⊣⊢ ¬(A ∧ (B ∧ C)) := by
      apply E13
      exact step_1
      apply E13
      exact step_2
      apply E13
      exact step_3
      apply E13
      exact step_4
      exact step_5
    exact step_6
  | E5 => 
    have step_1 : ¬(A ∨ A) ⊣⊢ (¬A ∧ ¬A) := by
      exact E9
    have step_2 : (¬A ∧ ¬A)⊣⊢ ¬A := by
      apply E12
      exact E2
    have step_3 : ¬(A ∨ A) ⊣⊢  ¬A := by
      apply E13
      exact step_1
      exact step_2
    apply E12
    exact step_3 
  | @E6 A B => 
    have step_1 : ¬(A ∨ B) ⊣⊢ (¬A ∧ ¬B) := by
      exact E9
    have step_2 : (¬A ∧ ¬B) ⊣⊢ (¬B ∧ ¬A) := by
      exact E3
    have step_3 : ¬(A ∨ B) ⊣⊢ (¬B ∧ ¬A) := by
      apply E13
      exact step_1
      exact step_2
    have step_4: (¬B ∧ ¬A) ⊣⊢ ¬(B ∨ A) := by
      apply E12
      exact E9
    have step_5 : ¬(A ∨ B) ⊣⊢ ¬(B ∨ A) := by
      apply E13
      exact step_3
      exact step_4
    exact step_5
  | @E7 A B C =>
    sorry
  | E8 => sorry
  | E9 => sorry
  | E10 => sorry
  | E11 => sorry
  | E12 => sorry
  | E13 => sorry
  | E14 => sorry
  | E15 => sorry

theorem admissibility_of_FR (A B C : Fml) (i : Nat): (A ⊣⊢ B) → (C[i := A] ⊣⊢ (C[i := B])) := by
  sorry

end Admissibility
