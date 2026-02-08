import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

set_option warningAsError false
/-
FIRST EXERCISE: Strict monotonicity

Section 3.1 of MIL discusses the `monotone` predicate. There is also a strict
version. Prove the theorems below, *and* come up with suitable names
(in other words, replace `example` with `theorem foo`.)

(Don't use any library theorems about `strict_mono` or `monotone`! You should
only use basic properties of orderings.)
-/

#print Monotone
#print StrictMono

namespace strict_mono_exercise

variable (f : ℝ → ℝ) (g : ℝ → ℝ)

theorem strict_mono_add (hf : StrictMono f) (hg : StrictMono g) : StrictMono (f + g) := by
  intro a b aleb
  dsimp
  exact add_lt_add (hf aleb) (hg aleb)




#check mul_lt_mul_of_pos_left

-- You'll have to guess at the name of a theorem for this one.
theorem strict_mono_mul_pos_const (c : ℝ) (hf : StrictMono f) (hc : 0 < c) :
  StrictMono (fun x ↦ c * f x) := by
  intro a b aleb
  dsimp
  apply mul_lt_mul_of_pos_left (hf aleb) hc

-- This is trickier than you might think. Use `by_cases h : a = b` to split
-- on cases whether `a = b`. You can also use `lt_of_le_of_ne`.

theorem mono_of_strict_mono (hf : StrictMono f) : Monotone f := by
  intro a b aleb
  by_cases h : a = b
  · rw[h]
  have altb: a < b := by apply lt_of_le_of_ne aleb h
  apply le_of_lt
  apply hf altb




/-
The following (trivial) example shows how to use trichotomy. You do not need
to fully understand the pattern now; you can take it as a black box.
-/

example (x1 x2 : ℝ) : x1 ≤ x2 ∨ x2 < x1 := by
  rcases lt_trichotomy x1 x2 with h | h | h
  { -- In this case, we have `h : x1 < x2`.
    left
    apply le_of_lt h }
  { -- In this case, we have `h : x1 = x2`.
    left
    rw [h] }
  -- In this case, we have `h : x2 < x1`
  right
  exact h

-- another example

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt


open Function

/-
Here is an example that shows that `x ↦ x + 1` is injective.
-/

example : Injective (fun x ↦ x + 1) := by
  intros x1 x2 h
  dsimp at h -- this makes `h` more readable
  exact add_right_cancel h


/-
Show that every strictly monotone function is injective.
-/

theorem injective_of_strict_mono (hf : StrictMono f) : Injective f := by
  intros a b h
  contrapose! h
  by_cases hlt: a < b
  · apply ne_of_lt (hf hlt)
  apply ne_of_gt
  apply hf
  rw[not_lt] at hlt
  symm at h
  apply lt_of_le_of_ne hlt h












end strict_mono_exercise

/-
SECOND EXERCISE: Galois connections

Given `α` with a partial order, a *closure operator* `cl : α → α` has the
following properties:

- `cl` is monotone
- `cl` is increasing, in the sense that for every `a : α`, `a ≤ cl a`
- `cl` is idempotent, in the sense that for every `a : α`, `cl (cl a) = cl a`.

Given `α` and `β` with partial orders, a *Galois connection* is a pair of
monotone functions `f : α → β` and `g : β → α` satisfying the following:

  For every `a` and `b`, `f a ≤ b` if and only if `a ≤ g b`.

You can read more about these here:

  https://en.wikipedia.org/wiki/Closure_operator
  https://en.wikipedia.org/wiki/Galois_connection

The exercises below ask you to show that if `f` and `g` form a Galois
connection, then `g ∘ f` is a closure operator, and `f ∘ g` is a closure
operator on the reverse order.
-/

namespace galois_connection_exercise

variable {α β : Type*} [PartialOrder α] [PartialOrder β]
variable {f : α → β}
variable {g : β → α}
variable {mono_f : Monotone f}
variable {mono_g : Monotone g}
variable {adj1 : ∀ a b, f a ≤ b → a ≤ g b}
variable {adj2 : ∀ a b, a ≤ g b → f a ≤ b}

section
-- you can use these:
include mono_f mono_g

theorem mono_gf : Monotone (g ∘ f) := by
  intro a b aleb
  dsimp
  apply mono_g
  exact mono_f aleb


theorem mono_fg : Monotone (f ∘ g) := by
  intro a b aleb
  dsimp
  apply mono_f
  apply mono_g aleb


end

section
include adj1

theorem increasing_gf : ∀ a, a ≤ g (f a) := by
  intro a
  have hfa: f a <= f a := by rfl
  exact adj1 a (f a) hfa


end

section
include adj2

theorem decreasing_fg : ∀ b, f (g b) ≤ b := by
  intro b
  have hfb: g b <= g b := by rfl
  exact adj2 (g b) b hfb

end


include mono_f mono_g adj1 adj2


#check mono_f
#check mono_fg
#check mono_fg
#check mono_gf
#check increasing_gf
#check decreasing_fg

theorem idempotent_gf : ∀ a, g (f (g (f a))) = g (f a) := by
  intro a
  apply le_antisymm
  · exact mono_g (@decreasing_fg _ _ _ _ _ _ adj2 (f a))
  exact @increasing_gf _ _ _ _ _ _ adj1 (g (f a))




theorem idempotent_fg : ∀ b, f (g (f (g b))) = f (g b) := by
  intro b
  apply le_antisymm
  · exact @decreasing_fg _ _ _ _ _ _ adj2 (f (g b))
  apply mono_f
  exact @increasing_gf _ _ _ _ _ _ adj1 (g b)


end galois_connection_exercise

/-
THIRD EXERCISE: convergence to infinity

Below, `to_infinity f` expresses that `f x` approaches infinity as
`x` approaches infinity.

The properties below are analogous to properties proved in Sections 3.2
and 3.6 in Mathematics in Lean. They involve the universal and existential
quantifiers (both no other logical connectives).
-/

def to_infinity (f : ℝ → ℝ) := ∀ b, ∃ x₀, ∀ x, x₀ ≤ x → b < f x

-- hint: you can use `linarith` at the end
example (f : ℝ → ℝ) (r : ℝ) (hf : to_infinity f) :
  to_infinity (fun x ↦ f x  + r) := by
  intro b
  rcases hf (b - r) with ⟨y, hg⟩
  dsimp
  use y
  intro x hxy
  have hb: b - r < f x := by apply hg x hxy
  linarith




-- hint: `div_lt_iff'` is useful here
example (f : ℝ → ℝ) (r : ℝ) (hr : 0 < r) (hf : to_infinity f) :
  to_infinity (fun x ↦ r * f x) := by
  intro b
  rcases hf (b / r) with ⟨y, hg⟩
  use y
  intro x hxy
  have hb: b / r < f x := by apply hg x hxy
  dsimp
  exact (@div_lt_iff₀' _ _ _ _ (f x) b r hr).mp hb

#check le_max_left
#check le_trans
-- hint: you can use `le_max_left` and `le_max_right`
example (f g : ℝ → ℝ) (hf : to_infinity f) (hg : to_infinity g) :
  to_infinity (f + g) := by
  intro b
  rcases hf (b / 2) with ⟨y, hfx⟩
  rcases hg (b / 2) with ⟨z, hgx⟩
  use max y z
  intro x hyz
  have hyx: y <= x := by apply le_trans (le_max_left y z) hyz
  have hbf: (b / 2) < f x := by exact hfx x hyx
  have hzx: z <= x := by apply le_trans (le_max_right y z) hyz
  have hbg: (b / 2) < g x := by exact hgx x hzx
  dsimp
  linarith
