import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Init.Internal.Order.Basic

set_option warningAsError false



/- This assignment is due by 11:59pm on Friday, March 3, 2023 . -/

/-
EXERCISE 1.

A function `F : set α → set α` is called a *monotone operator* if for every
pair of sets `s ⊆ t`, we have `F s ⊆ F t`.

Every such operator has a *least fixed point*, i.e. a set `s` satisfying:
- `F s = s`
- For every `t`, if `F t = t`, then `s ⊆ t`.

This exercise has you prove that fact. In fact, the least fixed point is
the intersection of all sets `s` such that `F s ⊆ s`.

This theorem, or the generalization to monotone operators on a complete lattice,
is called *Tarski's theorem* or the *Knaster-Tarski Theorem*. Feel free to use
Google to find more information.
-/
namespace monotone_set_operator
open Set

-- You will need these. The full names are `Set.mem_sInter`, etc.
#check @mem_sInter
#check @subset_sInter
#check @subset_sInter_iff

variable {α : Type*}

def lfp (F : Set α → Set α) := ⋂₀ { t | F t ⊆ t }

variable {F : Set α → Set α}
-- The monotonicity assumption:
variable (monoF : ∀ ⦃s t⦄, s ⊆ t → F s ⊆ F t)

/-
This follows immediately from the definition of `lfp F`.
-/
-- Exercise 1a. [8pts]
lemma aux0 {s : Set α} (h : F s ⊆ s) : lfp F ⊆ s := by
  unfold lfp
  intro x hx
  exact mem_sInter.1 hx s h



/-
All the remaining theorems in this section need the monotonicity assumption.
After you prove `aux1`, you have to write `aux1 monoF` to use it in a
later theorem.
-/
include monoF

/-
To show this next statement, it suffices to show that `F (lfp F)` is contained
in every set `t` such that `F t ⊆ t`. So suppose `t` has this property.
Then by `aux0`, `lfp F ⊆ t`, and by monotonicity, we have `F (lfp F) ⊆ F t ⊆ t`.
-/
-- Exercise 1b. [10pts]
lemma aux1 : F (lfp F) ⊆ lfp F := by
  nth_rw 2 [lfp]
  refine subset_sInter_iff.2 ?_
  intro t ht
  have lfp_F_t : lfp F ⊆ t := by exact aux0 ht
  have lfp_F_F_t : F (lfp F) ⊆ F (t) := by exact monoF lfp_F_t
  exact Set.Subset.trans lfp_F_F_t ht



-- Hint: The remaining exercise 1 proofs below can be done in at most three
-- lines each.

/- To show this, use `aux0`. -/
-- Exercise 1c. [5pts]
lemma aux2 : lfp F ⊆ F (lfp F) := by
  have h: F (F (lfp F)) ⊆ F (lfp F) := by exact monoF (aux1 monoF)
  exact aux0 h



/- Follows from `aux1` and `aux2`. -/
-- Exercise 1d. [5pts]
theorem lfp_fixed_point : F (lfp F) = lfp F := by
  exact subset_antisymm (aux1 monoF) (aux2 monoF)


-- Exercise 1e. [5pts]
theorem lfp_least_fixed_point (s : Set α) (h : F s = s) : lfp F ⊆ s := by
  exact aux0 h.subset


end monotone_set_operator

/-
EXERCISE 2.

A `complete lattice` is a partial order such that every subset has a greatest
lower bound (`Inf`) and a least upper bound (`Sup`). In fact, the existence
of either implies the other.

The proofs above carry over to this more general setting, if you replace
`α` by `set α`, `⊆` by `≤`, `⋂₀` by `Inf`, and make some small adjustments
to the proof.

Really, start by cutting and pasting the proofs above.
-/

namespace monotone_operator
open Order

#check @le_inf
#check @le_inf_iff
#check @inf_le_iff

variable {α : Type*} [CompleteLattice α]

def lfp (F : α → α) := sInf { s | F s ≤ s }

variable {F : α → α} (monoF : ∀ ⦃s t⦄, s ≤ t → F s ≤ F t)

-- Exercise 2a. [5pts]
lemma aux0 {s : α} (h : F s ≤ s) : lfp F ≤ s := by
  unfold lfp
  exact CompleteSemilatticeInf.sInf_le {s | F s ≤ s} s h
  -- apply?
  -- intro x hx
  -- exact Set.mem_sInter.1 hx s h


include monoF

-- Exercise 2b. [5pts]
lemma aux1 : F (lfp F) ≤ lfp F := by
  nth_rw 2 [lfp]
  apply le_sInf
  -- refine le_sInf ?_
  intro t ht
  have lfp_F_t : lfp F ≤ t := by exact aux0 ht
  have lfp_F_F_t : F (lfp F) ≤ F (t) := by exact monoF lfp_F_t
  exact le_trans lfp_F_F_t ht


-- Exercise 2c. [3pts]
lemma aux2 : lfp F ≤ F (lfp F) := by
  have h: F (F (lfp F)) ≤ F (lfp F) := by exact monoF (aux1 monoF)
  exact aux0 h


-- Exercise 2d. [2pts]
theorem lfp_fixed_point : F (lfp F) = lfp F := by
  exact le_antisymm (aux1 monoF) (aux2 monoF)

-- Exercise 2e. [2pts]
theorem lfp_least_fixed_point (s : α) (h : F s = s) : lfp F ≤ s := by
  exact aux0 h.le


end monotone_operator

/-
EXERCISE 3.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`B n = ⋃ i < n, A i`. Then the sequence `B 0, B 1, B 2, ...` is a monotone
sequence with the same union.
-/

namespace set_sequences

variable {α : Type*}
variable (A B : ℕ → Set α)
variable (B_def : ∀ n, B n = ⋃ i < n, A i)

/-
Remember, a (bounded) union corresponds to a (bounded) existential quantifier.
Use the simplifier with `simp only [Set.mem_iUnion]` to do the translation for
you. You can also write `simp only [Set.mem_iUnion] at h` to simplify a
hypothesis. You can also just use `simp`. However, mathlib conventions
discourage "non-terminal" calls, i.e. ones which don't close a goal, to `simp`
without `only`.
-/
theorem x_in_a_i (x : α) (n : ℕ) : (x ∈ ⋃ i < n, A i) ↔ ∃ i < n, x ∈ A i :=
  by simp only [Set.mem_iUnion, exists_prop]

-- This might be helpful to you:
example (i : ℕ) : i < i + 1 := Nat.lt_succ_self _

include B_def

#check set_sequences.x_in_a_i
-- Exercise 3a. [10pts]
theorem monotone_B : ∀ i j, i ≤ j → B i ⊆ B j := by
  intro i j h x hbi
  rw[B_def] at hbi
  rw [x_in_a_i] at hbi
  rcases hbi with ⟨k, hk, hxk⟩
  have kj : k < j := by linarith
  rw[B_def]
  apply (x_in_a_i A x j).2
  exact ⟨k, kj, hxk⟩





-- Exercise 3b. [15pts]
theorem Union_B_eq_Union_A : (⋃ i, B i) = (⋃ i, A i) := by
  apply subset_antisymm
  · intro x hb
    simp only [Set.mem_iUnion]
    simp only [Set.mem_iUnion] at hb
    rcases hb with ⟨i, hxb⟩
    rw[B_def] at hxb
    rw[x_in_a_i] at hxb
    rcases hxb with ⟨k, hk, hxk⟩
    use k
  intro x ha
  simp only [Set.mem_iUnion]
  simp only [Set.mem_iUnion] at ha
  rcases ha with ⟨k, hk⟩
  use k + 1
  rw[B_def]
  apply (x_in_a_i A x (k + 1)).2
  use k
  have: k < k + 1 := by linarith
  exact ⟨this, hk⟩



end set_sequences

/-
EXERCISE 4.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`C n = A n \ (⋃ i < n, A i)`. Then whenever `i ≠ j`, the sets `C i` and `C j` are
disjoint, but the sequence still has the same union.
-/

namespace set_sequences

variable {α : Type*}
variable (A C : ℕ → Set α)
variable (C_def : ∀ n, C n = A n \ (⋃ i < n, A i))

-- This may be useful.
#check @Set.eq_empty_of_forall_notMem
--#check @Set.eq_empty_of_ forall_not_mem

/-
Use the lemma `aux` below to show that if `x` is in some `A i`, then there
is a least `i` with that property.
-/
section
open Classical in
-- classical reason for just the following lemma
lemma aux {A : ℕ → Set α} {x : α} (h : ∃ i, x ∈ A i) :
  ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
  Subtype.exists_of_subtype (Nat.findX h)

end

include C_def

#check Set.inter_subset_right
-- Exercise 4a. [10pts]
theorem disjoint_C_of_lt : ∀ i j, i < j → C i ∩ C j = ∅ := by
  intro i j hij
  apply Set.eq_empty_of_forall_notMem
  intro x
  by_cases h: x ∈ C i
  · rw[C_def] at h
    apply (Set.mem_diff x).mp at h
    rcases h with ⟨hl, hr⟩
    intro ⟨hi, hj⟩
    have hjfalse: x ∉ C j := by
      rw[C_def]
      intro h
      apply (Set.mem_diff x).mp at h
      rcases h with ⟨hj, hjlt⟩
      apply hjlt
      simp only [Set.mem_iUnion]
      use i
    contradiction
  intro hij
  rcases hij with ⟨hi, hj⟩
  contradiction









#check Set.mem_diff
-- Exercise 4b. [15pts]
theorem Union_C_eq_Union_A : (⋃ i, C i) = (⋃ i, A i) := by
  apply subset_antisymm
  · intro x hcx
    simp only [Set.mem_iUnion]
    simp only [Set.mem_iUnion] at hcx
    rcases hcx with ⟨k, hk⟩
    rw[C_def] at hk
    apply (Set.mem_diff x).mp at hk
    use k
    exact hk.left
  intro x hcx
  simp only [Set.mem_iUnion]
  simp only [Set.mem_iUnion] at hcx
  apply aux at hcx
  rcases hcx with ⟨k, hak, hnotj⟩
  use k
  rw[C_def]
  apply (Set.mem_diff x).mpr
  constructor
  · exact hak
  intro ha
  simp only [Set.mem_iUnion] at ha
  rcases ha with ⟨m, hm, ham⟩
  specialize hnotj m hm
  contradiction








end set_sequences
