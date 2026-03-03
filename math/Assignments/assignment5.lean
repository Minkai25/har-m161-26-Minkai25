import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false

/-
# Homework assignment 5

- Homework 5 is due on Friday, March 6
  It is worth 70 points, and the goal is to
  formalize a complete proof of the
  Intermediate Value Theorem.
-/

/-
# The intermediate value theorem
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

def continuous (f : ℝ → ℝ) := ∀ a, approaches_at f (f a) a


section
variable (a b : ℝ) (f : ℝ → ℝ) (S : Set ℝ)

#check sSup S

#check @sSup
#check sSup { x : ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0 }

#check le_csSup
#check @le_csSup

#check csSup_le
#check @csSup_le

#print BddAbove
#print upperBounds

#check exists_lt_of_lt_csSup
#check @exists_lt_of_lt_csSup

#check Mathlib.Tactic.linarith


theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  let S := { x: ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have ainS : a ∈ S := by
    -- or constructor twice
    exact ⟨le_refl a ,aleb , hfa⟩
  have bddS : BddAbove S := by
    use b
    intro s sinS
    --exact sinS.2.1
    exact sinS.right.left
  --set c := sSup S with cdef -- gives a _name_ to fact c= sSup S
  let c := sSup S
  --Next: establish c ∈ [a,b]
  have cdef : c = sSup S := by --instead of using `set`
    rfl

  have cleb : c ≤ b := by
    apply csSup_le
      --in term mode:
      --exact ⟨a, ainS⟩
    · use a
    intro s sinS
    exact sinS.2.1
  have alec : a ≤ c := by
    exact le_csSup bddS ainS
  --**Big step---cases on f(c) vs 0
  rcases lt_trichotomy (f c) 0 with fcneg | fczero | fcpos
    --Case 1
  · exfalso
    unfold continuous at ctsf
    specialize ctsf c
    set ε := - (f c)/2 with εdef
    have εpos : ε > 0 := by
      linarith
    unfold approaches_at at ctsf
    specialize ctsf ε εpos
    rcases ctsf with ⟨ δ, δpos, hδ⟩
    by_cases hc2: c + δ/2 > b
    · have bnearc : |b-c| < δ := by
        rw [abs_lt]
        constructor <;> linarith
      specialize hδ b bnearc
      have forcontra : ¬ 0 < f b
      { rw [abs_lt] at hδ
        linarith
      }
      apply forcontra
      exact hfb
    -- Now in case where c + δ/2 ≤ b
    push_neg at hc2
    have c2nearc : |c + δ/2 -c| < δ := by
      rw [add_sub_cancel_left]
      rw [abs_of_pos] <;> linarith
    specialize hδ (c + δ/2) c2nearc
    -- here is where class ended on 3/2 --
    /- PROBLEM 1: [10pts] Finish the proof by replacing
                  the `sorry` statements -/
    have hfc2neg : f (c + δ/2) < 0 := by
      apply abs_lt.mp at hδ
      -- have hfc2ltnegeps: f (c + δ/2) < -ε := by
      --   linarith
      linarith
    have c2inS : c + δ/2 ∈ S := by
      have altc2 : a <= c + δ/2 := by
        linarith
      exact ⟨altc2, hc2, hfc2neg⟩
    have c2lec : c + δ/2 ≤ c := by
      exact le_csSup bddS c2inS
    linarith
    --At this pont, Case 1 where f c < 0 is finished
  · --now on to Case 2
    /-PROBLEM 2: [3pts] Complete the proof of this
      case, where f c = 0 -/
    use c
  · --finally Case 3, where 0 < f c
    /- PROBLEM 3: [57pts] Complete the proof of
       the third case below.  You can follow the
       outline in the pdf lecture0302-ivt.pdf
       in the course directory.  Note that the pdf
       is written to reasonably precisely line up
       with a possible Lean code formalization.-/
    exfalso
    set ε := (f c) / 2 with edef
    have epos: ε > 0 := by linarith
    unfold continuous at ctsf
    specialize ctsf c
    unfold approaches_at at ctsf
    specialize ctsf ε epos
    rcases ctsf with ⟨ δ, δpos, hδ⟩
    have hc2 : c - δ/2 < c := by linarith
    have snonempty: S.Nonempty := by use a
    have ⟨s, hs_mem, ha_lt⟩ := exists_lt_of_lt_csSup snonempty hc2
    have hsc: s ≤ c := by exact le_csSup bddS hs_mem
    have hscabs : |s - c| < δ := by
      rw[abs_lt]
      constructor <;> linarith
    have fspos : 0 < (f s) := by
      have fscont : |(f s) - (f c)| < ε := by exact hδ s hscabs
      apply abs_lt.mp at fscont
      linarith
    have fsneg : (f s) < 0 := by
      exact hs_mem.right.right
    linarith


end
