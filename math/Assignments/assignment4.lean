import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false
/-
EXERCISE 1. [30pts]

Prove the following without using automation, i.e. only with basic tactics
such as `intros`, `apply`, `split`, `cases`, `left`, `right`, and `use`.
-/

section

variable {α β : Type} (p q : α → Prop) (r : α → β → Prop)

-- Exercise 1a. [10pts]
example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
  intro h x
  have h1: p x := by exact h.1 x
  have h2: q x := by exact h.2 x
  exact ⟨h1, h2⟩


-- Exercise 1b. [10pts]
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  rcases h with hp | hq
  {
    left
    exact hp x
  }
  right
  exact hq x


-- Exercise 1c. [10pts]
example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by
  intro h y
  rcases h with ⟨x, hx⟩
  use x
  exact hx y


end

/-
EXERCISE 2.

Suppose two pairs of real numbers {a, b} and {c, d} have the same sum
and product. The following theorem shows that either a = c and b = d,
or a = d and b = c. Fill in the details. You can use `ring`, `ring_nf`
and `linarith` freely.
-/

-- Exercise 2. [20pts]
theorem sum_product_magic (a b c d : ℝ)
    (sumeq : a + b = c + d) (prodeq : a * b = c * d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have : (a - c) * (a - d) = 0
  {
    have bsim : b = c + d - a := by linarith
    rw[bsim] at prodeq
    linarith
  }
  have := eq_zero_or_eq_zero_of_mul_eq_zero this
  rcases this with  h | h
  {
    left
    have h1: a = c := by exact sub_eq_zero.1 h
    have h2: b = d := by
      rw [h1] at sumeq
      exact add_left_cancel sumeq
    exact ⟨h1, h2⟩
  }
  {
    right
    have h1: a = d := by exact sub_eq_zero.1 h
    have h2: b = c := by
      rw [h1] at sumeq
      rw [add_comm] at sumeq
      exact add_right_cancel sumeq
    exact ⟨h1, h2⟩
  }


/-
EXERCISE 3. [30pts]

The predicate `approaches_at f b a` should be read "f(x) approaches b as x
approaches a", and the predicate `continuous f` says that f is continuous.

Prove the following two theorems.

Note that bounded quantification such as `∀ ε > 0, ..` really means `∀ ε, ε > 0 → ..`
and `∃ δ > 0, ..` really means `∃ δ, δ > 0 ∧ ..`.
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

-- Exercise 3a. [10pts]
theorem approaches_at_add_right  {f : ℝ → ℝ} {a b c: ℝ}
    (hf : approaches_at f b a) :
  approaches_at (fun x ↦ f x + c) (b + c) a := by
  -- unfold approaches_at at hf
  intro ε he
  rcases hf ε he with ⟨δ, hd, hg⟩
  use δ
  use hd
  intro x
  dsimp
  have hsim: f x + c - (b + c) = f x - b := by simp
  rw[hsim]
  exact hg x






-- Exercise 3b. [10pts]
theorem approaches_at_comp {f g : ℝ → ℝ} {a b c : ℝ}
  (hf : approaches_at f b a) (hg : approaches_at g c b) :
    approaches_at (g ∘ f) c a := by
  intro ε he
  rcases hg ε he with ⟨δ, hd, hgd⟩
  rcases hf δ hd with ⟨δ_1, hl, hfd⟩
  use δ_1
  use hl
  dsimp
  intro x
  specialize hfd x
  specialize hgd (f x)
  intro hxa
  exact hgd (hfd hxa)


def continuous (f : ℝ → ℝ) := ∀ x, approaches_at f (f x) x

-- Exercise 3c. [10pts]
theorem my_continuous_add_right {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (fun x ↦ f x + r) := by
  intro x
  specialize ctsf x
  intro ε he
  rcases ctsf ε he with ⟨δ, hd, hf⟩
  use δ
  use hd
  dsimp
  intro x_1
  specialize hf x_1
  have hsimp : f x_1 + r - (f x + r) = f x_1 - f x := by simp
  rw[hsimp]
  exact hf
-- Since `f x - r` is the same as `f x + (- r)`, the following is an instance
-- of the previous theorem.
theorem continuous_sub {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (fun x ↦ f x - r) :=
  my_continuous_add_right ctsf (-r)

/-
EXERCISE 4.

In class, I will prove the intermediate value theorem in the form `ivt`.
Use that version to prove the more general one that comes after.
-/

/- We'll do this in class! You don't have to prove it,
   and you can leave the `sorry` and apply the theorem
   as a black box. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
sorry

-- Use `ivt` to prove `ivt'` below.

-- Exercise 4. [20pts]
theorem ivt' {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c := by
  let g := fun x ↦ f x - c
  have : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0
  {
    have hga: g a < 0 := by
      dsimp [g]
      linarith
    have hgb: 0 < g b := by
      dsimp [g]
      linarith
    have hgcont: continuous g := by
      dsimp [g]
      exact continuous_sub ctsf c
    exact ivt aleb hgcont hga hgb
  }
  dsimp [g] at this
  rcases this with ⟨x, res⟩
  use x
  have hfxc : f x = c := by exact sub_eq_zero.1 (res.2.2)
  exact ⟨res.1, ⟨res.2.1, hfxc⟩ ⟩
