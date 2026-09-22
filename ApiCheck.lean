import Mathlib.Tactic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open PMF
open BigOperators

#check tsum_eq_sum

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (n : ℕ)

noncomputable def probBlock' (P : PMF X) (x : Fin n → X) : ENNReal :=
  ∏ i, P (x i)

lemma sum_pmf' (P : PMF X) : (∑ x : X, P x) = 1 := by
  simpa only [← tsum_coe P, tsum_eq_sum (s := Finset.univ) (fun b hb => False.elim (hb (Finset.mem_univ b)))]

noncomputable def blockPMF' (P : PMF X) : PMF (Fin n → X) :=
  PMF.ofFintype (probBlock' n P) (by
    classical
    simp only [probBlock']
    rw [← Fintype.piFinset_univ]
    rw [Finset.sum_prod_piFinset]
    simp [sum_pmf'])
