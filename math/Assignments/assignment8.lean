import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

set_option warningAsError false
--note a new option set for `  induction'  ` tactic
set_option linter.style.induction false



/-
EXERCISE 1.

In set theory, one typically builds up a foundation for reasoning about finite
sets as follows. First, one defines the set of natural numbers. Then one says
that a set is *finite* if it is in bijection with the set {0, 1, ..., n-1} for
some n. We then want to say that the *cardinality* of that set is n, but that
requires knowing that a set cannot be in bijection with the canonical n-element
set and the canonical m-element set at the same time if m ≠ n. This can be
reduced to showing that there is no injective function from the canonical
n-element set to the canonical n-1-element set. This is the pigeonhole
principle, below.

This is *not* how it is done in mathlib. For the record, there we do the
following:

- Define the type of lists.
- Say what it means for one list to be a permutation of another, and prove that
  this is an equivalence relation.
- Define multisets to be lists modulo permutation equivalence.
- Define finsets to be multisets without duplicates.

Operations like union, intersection, cardinality are defined on lists and
lifted to multisets.

The next proof of the pigeonhole principle is pretty messy. I'd love to see a
cleaner one (that doesn't use finsets!).
-/

section
variable {α : Type*}
--open finset
#check Nat.le_succ
-- Exercise 1 [40pts]. Fill in the sorry below.
theorem pigeonhole_principle (n : ℕ) :
  ∀ f : ℕ → ℕ, (∀ i ≤ n, f i < n) → ∃ i ≤ n, ∃ j ≤ n, i ≠ j ∧ f i = f j := by
  induction' n with n ih
  · simp
  · intros f hf
    by_cases h: ∀ i ≤ n, f i < n
    · have := ih f h
      rcases this with ⟨i, ilen, j, jlen, inej, fieqfj⟩
      use i
      constructor
      · have := Nat.le_succ_of_le ilen
        apply this
      use j
      constructor
      · have := Nat.le_succ_of_le jlen
        apply this
      use inej--, fieqfj Since it is a hypothesis, it is inferred
    push_neg at h
    rcases h with ⟨i, hi, nle⟩
    have := hf i (Nat.le_succ_of_le hi)
    have fieq : f i = n := le_antisymm (Nat.le_of_lt_succ this) nle
    by_cases h': ∃ j ≤ n.succ, i ≠ j ∧ f j = n
    · rcases h' with ⟨ j, jle, inej, fjeq⟩
      use i, Nat.le_succ_of_le hi, j, jle, inej, fieq.trans fjeq.symm
    push_neg at h'
    --we will use h' to define a _new_ function f'
    set f' := fun j ↦ if j=i then f n.succ else f j with f'def
    have : ∀ j ≤ n , f' j < n := by
      intros j jle
      rw [f'def]
      dsimp
      split_ifs with h0
      -- goals from here: try to apply induction to f'
      · have hn1: i ≠ n + 1 := by
          linarith
        specialize h' (n + 1) _
        · rfl
        have fn1: f (n + 1) ≠ n := by
          exact h' hn1
        specialize hf (n + 1) _
        · rfl
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hf) fn1
      · specialize hf j _
        · linarith
        specialize h' j _ _
        · linarith
        · exact Ne.symm h0
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hf) h'
    have fn1 : f (n + 1) < n := by
      specialize this i hi
      rw[f'def] at this
      dsimp at this
      simp only [if_true] at this
      exact this
    specialize ih f' this
    rcases ih with ⟨k, kn, m, mn, kneqm, fkm⟩
    by_cases hki : k = i
    · by_cases hmi : m = i
      · simp [hki, hmi] at kneqm
      · have hfk : f' k = f n.succ := by simp [f'def, hki]
        have hfm : f' m = f m     := by simp [f'def, hmi]
        rw [hfk, hfm] at fkm
        exact ⟨n.succ, le_refl _, m, Nat.le_succ_of_le mn,
               ne_of_gt (Nat.lt_succ_of_le mn), fkm⟩
    · by_cases hmi : m = i
      · have hfk : f' k = f k      := by simp [f'def, hki]
        have hfm : f' m = f n.succ := by simp [f'def, hmi]
        rw [hfk, hfm] at fkm
        exact ⟨k, Nat.le_succ_of_le kn, n.succ, le_refl _,
               Nat.ne_of_lt (Nat.lt_succ_of_le kn), fkm⟩
      · have hfk : f' k = f k := by simp [f'def, hki]
        have hfm : f' m = f m := by simp [f'def, hmi]
        rw [hfk, hfm] at fkm
        exact ⟨k, Nat.le_succ_of_le kn, m, Nat.le_succ_of_le mn, kneqm, fkm⟩


/-
EXERCISE 2. The following is an exercise on structural induction on formulas.
-/

inductive PropForm : Type
| var (n : ℕ)           : PropForm
| fls                   : PropForm
| conj (A B : PropForm) : PropForm
| disj (A B : PropForm) : PropForm
| impl (A B : PropForm) : PropForm

namespace PropForm

def eval : PropForm → (ℕ → Bool) → Bool
| (var n),    v => v n
| fls,        _  => false
| (conj A B), v  => A.eval v && B.eval v
| (disj A B), v  => A.eval v || B.eval v
| (impl A B), v  => !! A.eval v || B.eval v

def subst : PropForm → ℕ → PropForm → PropForm
| (var n),    m, C => if n = m then C else var n
| fls   ,     _, _ => fls
| (conj A B), m, C => conj (A.subst m C) (B.subst m C)
| (disj A B), m, C => disj (A.subst m C) (B.subst m C)
| (impl A B), m, C => impl (A.subst m C) (B.subst m C)

def free_variables : PropForm → Finset ℕ
| (var n)    => {n}
| fls        => ∅
| (conj A B) => A.free_variables ∪ B.free_variables
| (disj A B) => A.free_variables ∪ B.free_variables
| (impl A B) => A.free_variables ∪ B.free_variables


theorem subst_eq_of_not_mem_free_variables :
  ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.free_variables →
      A.subst n C = A
| (var m) , n, C, h => by
  rw [subst]; split_ifs with h0
  · simp [h0,free_variables] at h
  rfl
| fls, n, C, h => by rw [subst]
| (conj A B), n, C, h => by
  simp [free_variables] at h
  rw [subst,subst_eq_of_not_mem_free_variables,
      subst_eq_of_not_mem_free_variables]
  · exact h.2
  exact h.1
| (disj A B), n, C, h => sorry
| (impl A B), n, C, h => sorry

-- complete this theorem, including the inductive structure.
-- try in class


-- Exercise 2 [30pts].--complete the sorries below
theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
  (A.subst n C).eval v = A.eval (fun m ↦ if m = n then C.eval v else v m)
| (var m), n, C, v => by
      sorry
| fls, n, C, v => by
      sorry
| (conj A B), n, C, v => by
      sorry
| (disj A B), n, C, v => by
      sorry
| (impl A B), n, C, v => by
      sorry





end PropForm  --closing the PropForm namespace

/-
EXERCISE 3. This is an exercise in defining the integers as a quotient
with (p.1, p.2) representing the equivalence class of p.1 - p.2.
(It's not the definition used in mathlib, but at one time it was.)
-/

def iequiv (p q : ℕ × ℕ) := p.1 + q.2 = q.1 + p.2

--longer version of below
example : Equivalence iequiv := by
   --try in class, in tactic mode
  constructor
  · intro p
    --unfold iequiv
    rfl
  · intros p q h
    unfold iequiv
    unfold iequiv at h
    rw [h]
  · intros p q r h1 h2
    simp [iequiv] at *
    linarith

--same example as above, but now in term mode
theorem equivalence_iequiv : Equivalence iequiv :=
⟨ fun p ↦ by rfl,
  --@fun p q h ↦ h.symm,
  fun h ↦ h.symm,
  @fun p q r h1 h2 ↦ by
    simp [iequiv] at *
    linarith
⟩


def isetoid : Setoid (ℕ × ℕ) := ⟨iequiv, equivalence_iequiv⟩

def integer := Quotient isetoid

--local attribute [instance] isetoid
--local instance isetoid --maybe this gets farther?
--local instance isetoid : integer := [(0,0)]
--default_instance isetoid

def izero : integer := ⟦(0, 0)⟧


def iadd : integer → integer → integer :=
  Quotient.lift₂
  (fun p q : ℕ × ℕ ↦ ⟦(p.1 + q.1, p.2 + q.2)⟧)
  (by
    intros a₁ a₂ b₁ b₂
    dsimp [HasEquiv.Equiv, isetoid, iequiv]
    intros h1 h2
    apply Quotient.sound
    dsimp [HasEquiv.Equiv,isetoid, iequiv]
    linarith
  )


variable (c d : integer)
#check @Quotient.inductionOn₂ _ _ _ _ _ c d



def iadd_comm (a b : integer) : iadd a b = iadd b a := by
   ---added after class
   apply @Quotient.inductionOn₂ _ _ _ _ _ a b
   intros a b
   rw [iadd]
   dsimp
   rw [add_comm,add_comm a.2]




#check @Quotient.inductionOn _ _ _ c
#check Quotient.inductionOn



def iadd_zero (a : integer) : iadd a izero = a := by
   ---added after class
   apply @Quotient.inductionOn _ _ _ a
   intro b
   rw [iadd, izero]
   --from dsimp?
   dsimp only [Quotient.lift_mk, Nat.add_zero]





-- Define negation and prove that it works.

--hint for below: try using
#check Quotient.lift

-- Exercise 3a [15pts].
def ineg : integer → integer :=
  Quotient.lift (s := isetoid)
  (fun p : ℕ × ℕ ↦ ⟦(p.2, p.1)⟧)
  (by
    intro p q pq
    dsimp [HasEquiv.Equiv, isetoid, iequiv] at pq
    apply Quotient.sound
    dsimp [HasEquiv.Equiv, isetoid, iequiv]
    linarith
  )




-- Exercise 3b [15pts].
theorem iadd_ineg (a : integer) : iadd a (ineg a) = izero := by
  apply @Quotient.inductionOn _ _ _ a
  intro b
  rw[iadd, izero]
  dsimp only [Quotient.lift_mk, ineg]
  apply Quotient.sound
  dsimp only [HasEquiv.Equiv, isetoid, iequiv]
  linarith
