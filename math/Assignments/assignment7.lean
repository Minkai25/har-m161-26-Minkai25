import Mathlib.Tactic
import Mathlib.Data.Nat.Factors
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic

set_option warningAsError false
--note a new option set for `  induction'  ` tactic
set_option linter.style.induction false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.flexible false


/- This assignment is due by 11:59pm on Friday, April 10th 2026. -/

/-
EXERCISE 1. Using the definition `mypow a n`, which is supposed to define
exponentiation `a^n`, use induction to prove the theorem below.

Hint: you can use `nat.add_succ` to unfold the defition of `m + n.succ`.
-/

section
variable {α : Type*} [CommMonoid α]


def mypow : α → ℕ → α
| a , 0       => 1
| a , (n + 1) => a * (mypow a n)

#eval mypow 3 5

theorem mypow_zero (a : α) : mypow a 0 = 1 := rfl

theorem mypow_succ (a : α) (n : ℕ) : mypow a (n + 1) = a * mypow a n := rfl

-- Exercise 1 [10pts].
theorem mypow_add (a : α) (m n : ℕ) : mypow a (m + n) = mypow a m * mypow a n := by
  induction' n with n ih
  · simp [mypow_zero]
  · calc mypow a (m + (n + 1))
          = mypow a ((m + n) + 1)         := by rw [Nat.add_succ]
        _ = a * mypow a (m + n)           := mypow_succ a (m + n)
        _ = a * (mypow a m * mypow a n)   := by rw [ih]
        _ = mypow a m * (a * mypow a n)   := by rw [← mul_assoc, mul_comm a (mypow a m), mul_assoc]
        _ = mypow a m * mypow a (n + 1)   := by rw [← mypow_succ]


end

/-
EXERCISE 2.

In class, we have used ordinary induction on the natural numbers,
which allows you to prove `p n` for an arbitrary natural number
`n` by proving `p 0` and `∀ m, p m → p m.succ`.

It is often more useful to the principle of *complete induction*
or *strong induction*. This is found in the library under the
name `Nat.strong_induction_on`, but the exercise below asks you
to prove it independently, using ordinary induction on the natural numbers.
The principle is stated in a form that the induction tactic
can use it, as illustrated in exercise 3.

The trick is to prove the stronger claim `∀ n, ∀ m < n, p m` by
induction on the natural numbers. The `suffices` step in the proof
shows that this suffices to establish `p n` for the *particular* `n` in
the context. Once we have done that, we throw away the particular `n`,
and focus on proving the stronger claim by induction.
-/

section

-- Exercise 2 [17pts].
theorem complete_induction_on {p : ℕ → Prop} (n : ℕ)
  (h : ∀ n, (∀ m < n, p m) → p n) : p n := by
  suffices : ∀ n, ∀ m < n, p m
  {
    apply h
    intro m
    apply this
  }
  clear n
  intro n
  induction' n with n ih
  {
    simp
  }
  intro m hmn
  by_cases hm: m = n
  · rw[hm]
    apply h
    exact ih
  apply ih
  exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hmn) hm






end

/-
EXERCISE 3.

In this exercise, we use the principle of strong induction to show that
every natural number greater than or equal to two has a prime divisor.

You can use the lemma `exists_lt_dvd_of_not_prime`. After the boilerplate
that we have set up for you, you should formalize the following argument:
if `n` is prime, we are done.  If `n` is not prime, the lemma tells us that
there it has a nontrivial divisor `m < n`, and we can apply the induction
hypothesis to that.
-/

-- This follows straightforwardly from the definition of `nat.prime`.
lemma exists_lt_dvd_of_not_prime {n : Nat} (h : ¬ Nat.Prime n) (h' : 2 ≤ n) :
  ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n := by
  simp [Nat.prime_def_lt'] at h
  exact h h'


-- Exercise 3 [18pts].
theorem exists_prime_dvd (n : ℕ) : 2 ≤ n → ∃ p, Nat.Prime p ∧ p ∣ n := by
  induction' n using complete_induction_on with n ih
  intro nle
  by_cases h: Nat.Prime n
  · use n
  have div : ∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n := by exact exists_lt_dvd_of_not_prime h nle
  rcases div with ⟨m, hm2, hmn, hdvd⟩
  specialize ih m hmn hm2
  rcases ih with ⟨p, primep, pm⟩
  use p
  have pn : p ∣ n := by exact dvd_trans pm hdvd
  exact ⟨primep, pn⟩






/-
EXERCISE 4.

Finally, in this exercise, we define the structure of a `quasigroup`,
show that the integers with subtraction form an instance, and prove
some basic properties.

You can find the definition of a quasigroup here:

  https://en.wikipedia.org/wiki/Quasigroup

We'll use the notation `ldiv a b` for left division (on Wikipedia, `a \ b`),
and we'll use `rdiv a b` for right division (on Wikipedia, `a / b`).

(Instantiating the integers as a quasigroup is dangerous, because it
redefines the notation of multiplication to mean substraction. Such
a thing could destroy the understanding of mathematics for a generation
of elementary school students, so please make sure your git repositories
stay private!)
-/

-- Exercise 4a [10pts].
/-
First, fill in the remaining axioms. E.g. the first should say,
"for any `a`, `b` and `x`, if `x` satisfies the defining equation for `a \ b`
(that is, the cancellation law), then it is equal to `a \ b`."
-/

class quasigroup (α : Type*) extends Mul α where
(ldiv : α → α → α)
(rdiv : α → α → α)
(mul_ldiv_cancel : ∀ a b, a * ldiv a b = b)
(rdiv_mul_cancel : ∀ a b, rdiv a b * b = a)
(ldiv_unique : ∀ a b x, a * x = b → x = ldiv a b)
(rdiv_unique : ∀ a b y, y * b = a → y = rdiv a b)



/-
class quasigroup (α : Type*) extends Mul α :=
(ldiv : α → α → α)
(rdiv : α → α → α)
(mul_ldiv_cancel : ∀ a b, a * ldiv a b = b)
(rdiv_mul_cancel : ∀ a b, rdiv a b * b = a)
(ldiv_unique : sorry)
(rdiv_unique : sorry)
-/
-- Exercise 4b [15pts].
/-
Next, show that the integers with subtraction are an instance. You will
have to figure out the right definitions of `ldiv` and `rdiv`. For
example, if you decide `ldiv a b` should be `a * b`, write
`ldiv := λ a b, a * b`.

Note: Be sure to write this out on paper first, and check the identities
as you see them wikipedia.  This will make the coding much easier, and
help avoid you trying to prove something that is impossible.

Note that in goals within the instance definition, you might see "multiplication"
which is really integer subtraction, because that's we defined it as! To check
which one it really is, you can click on the `*` operation in the infoview and look
for something like `{mul := int.sub}`.

Also, the `show` tactic can sometimes be used to unfold definitions. For example
on the goal `⊢ a * b = stuff`, `show a - b = stuff` should work.
-/

instance : quasigroup ℤ where
  mul  := Int.sub
  ldiv := fun a b => a - b
  rdiv := fun a b => a + b
  mul_ldiv_cancel := by
      intro a b
      change a - (a - b) = b
      ring
  rdiv_mul_cancel := by
      intro a b
      change (a + b) - b = a
      ring
  ldiv_unique := by
      intro a b x h
      change a - x = b at h
      linarith


  rdiv_unique := by
      intro a b y h
      change y - b = a at h
      linarith


/- Finally, prove that some identities hold in *any* quasigroup. -/

namespace quasigroup
variable {α : Type*} [quasigroup α]

-- Exercise 4c [5pts].
theorem eq_ldiv_mul_self (y x : α) : y = ldiv x (x * y) := by
  apply ldiv_unique
  rfl


-- Exercise 4d [5pts].
theorem eq_mul_rdiv_self (y x : α) : y = rdiv (y * x) x := by
  apply rdiv_unique
  rfl


-- Exercise 4e [10pts].
theorem left_cancel (a b c : α) (h : a * b = a * c) : b = c := by
  apply ldiv_unique at h
  have hc : c = ldiv a (a * c) := by apply eq_ldiv_mul_self
  rw[← hc] at h
  exact h



-- Exercise 4f [10pts].
theorem right_cancel (a b c : α) (h : a * b = c * b) : a = c := by
  apply rdiv_unique at h
  have hc : c = rdiv (c * b) b := by apply eq_mul_rdiv_self
  rw[← hc] at h
  exact h



end quasigroup
