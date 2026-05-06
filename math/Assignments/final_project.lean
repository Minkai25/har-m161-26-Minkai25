import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

set_option warningAsError false
set_option linter.style.induction false
set_option linter.unusedVariables false
open Finset
namespace StarsAndBarsInduction

/- Hockey stick identity. -/
lemma sum_choose_eq_choose (m n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (m+j).choose j = (m+n+1).choose n := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, ih]
    exact (Nat.choose_succ_succ (m+n+1) n).symm


/- Partition each tuple summing to `n` by the value of its first coordinate. -/
lemma card_antidiagonalTuple_succ (m n : ℕ) :
    (Finset.Nat.antidiagonalTuple (m+2) n).card
      = ∑ i ∈ Finset.range (n+1), (Finset.Nat.antidiagonalTuple (m+1) (n-i)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (m+2) → ℕ => x 0)
      (t := Finset.range (n+1)) (by
    intros x hx
    simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
    simp only [Finset.mem_coe, Finset.mem_range]
    rw [Fin.sum_univ_succ] at hx
    grind)]
  apply Finset.sum_congr rfl
  intros i hi
  rw [Finset.mem_range] at hi
  -- Bijection: Fin.tail (forward), Fin.cons i (inverse).
  apply Finset.card_bij (fun (x : Fin (m+2) → ℕ) _ => Fin.tail x)
  · intros x hx
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hx
    rcases hx with ⟨hxsum, hx0⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    have h := (Fin.sum_univ_succ x).symm
    rw [hxsum] at h
    show ∑ k : Fin (m+1), x k.succ = n - i
    grind
  · intros x hx y hy heq
    simp only [Finset.mem_filter] at hx hy
    have h0 : x 0 = y 0 := hx.2.trans hy.2.symm
    calc x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
      _   = Fin.cons (y 0) (Fin.tail y) := by rw [h0, heq]
      _   = y                           := Fin.cons_self_tail y
  · intros t ht
    rw [Finset.Nat.mem_antidiagonalTuple] at ht
    refine ⟨Fin.cons i t,? _, ?_⟩
    · simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.cons_zero, and_true]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      grind
    · simp [Fin.tail_cons]


/- Stars and Bars main theorem. -/
theorem stars_and_bars (m n : ℕ) :
    (Finset.Nat.antidiagonalTuple (m+1) n).card = (m+n).choose n := by
  induction' m with m ih generalizing n
  · rw [Finset.Nat.antidiagonalTuple_one, Finset.card_singleton, Nat.zero_add, Nat.choose_self]
  · rw [card_antidiagonalTuple_succ]
    have step : ∀ i ∈ Finset.range (n+1),
        (Finset.Nat.antidiagonalTuple (m+1) (n-i)).card = (m + (n-i)).choose (n-i) := by
      intros i _; exact ih (n-i)
    rw [Finset.sum_congr rfl step]
    -- Reindex i ↦ n - i to invoke the hockey stick identity.
    have reindex :
        ∑ i ∈ Finset.range (n+1), (m + (n-i)).choose (n-i)
          = ∑ j ∈ Finset.range (n+1), (m + j).choose j := by
      apply Finset.sum_nbij' (fun i => n - i) (fun j => n - j)
      · intros i hi; rw [Finset.mem_range]; grind
      · intros j hj; rw [Finset.mem_range]; grind
      · intros i hi; rw [Finset.mem_range] at hi; grind
      · intros j hj; rw [Finset.mem_range] at hj; grind
      · intros i _; rfl
    rw [reindex, sum_choose_eq_choose]
    ring_nf

end StarsAndBarsInduction

namespace StarsAndBars

end StarsAndBars
