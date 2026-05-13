import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

set_option warningAsError false
set_option linter.style.induction false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
open Finset
namespace StarsAndBarsInduction

/- Hockey stick identity. -/
lemma hockey_stick (m n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (m+j).choose j = (m+n+1).choose n := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, ih]
    exact (Nat.choose_succ_succ (m+n+1) n).symm


/- Partition each tuple summing to `n` by the value of its first coordinate. -/
lemma card_antidiagonalTuple_succ (m n : ℕ) :
    (Finset.Nat.antidiagonalTuple (m+2) n).card
      = ∑ i ∈ Finset.range (n+1), (Finset.Nat.antidiagonalTuple (m+1) (n-i)).card := by
  have fiber : Set.MapsTo (fun x : Fin (m+2) → ℕ => x 0)
      (Finset.Nat.antidiagonalTuple (m+2) n) (Finset.range (n+1)) := by
    intros x hx
    simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hx
    simp only [Finset.mem_coe, Finset.mem_range]
    rw [Fin.sum_univ_succ] at hx
    grind
  rw [Finset.card_eq_sum_card_fiberwise fiber]
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
    refine ⟨Fin.cons i t,?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.cons_zero, and_true]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      grind
    · simp [Fin.tail_cons]


/- Stars and Bars theorem. -/
theorem stars_and_bars (m n : ℕ) :
    (Finset.Nat.antidiagonalTuple (m+1) n).card = (m+n).choose n := by
  induction' m with m ih generalizing n
  · rw [Finset.Nat.antidiagonalTuple_one, Finset.card_singleton, Nat.zero_add, Nat.choose_self]
  · rw [card_antidiagonalTuple_succ]
    have step : ∀ i ∈ Finset.range (n+1),
        (Finset.Nat.antidiagonalTuple (m+1) (n-i)).card = (m + (n-i)).choose (n-i) := by
      intros i hi
      exact ih (n-i)
    rw [Finset.sum_congr rfl step]
    -- Reindex i ↦ n - i to invoke the hockey stick identity.
    have index :
        ∑ i ∈ Finset.range (n+1), (m + (n-i)).choose (n-i)
          = ∑ j ∈ Finset.range (n+1), (m + j).choose j := by
      apply Finset.sum_nbij' (fun i => n - i) (fun j => n - j)
      · intros i hi
        rw [Finset.mem_range]
        grind
      · intros j hj
        rw [Finset.mem_range]
        grind
      · intros i hi
        rw [Finset.mem_range] at hi
        grind
      · intros j hj
        rw [Finset.mem_range] at hj
        grind
      · intros i hi
        rfl
    rw [index, hockey_stick]
    ring_nf

end StarsAndBarsInduction

namespace StarsAndBars

/-! Stars and Bars bijection Proof.
We link two distinct bijections. The first goes from Finset.Nat.antidiagonalTuple
to sets of natural numbers with
-/

open Finset

variable {m n : ℕ}

def Φ_A (x : Fin (m+1) → ℕ) : Fin (m+2) → ℕ :=
  fun i => (∑ k : Fin (m+1), if (k : ℕ) < i.val then x k else 0) + i.val

def Ψ_A (σ : Fin (m+2) → ℕ) : Fin (m+1) → ℕ :=
  fun i => σ i.succ - σ i.castSucc - 1

def Φ_B (σ : Fin (m+2) → ℕ) : Finset ℕ :=
  (univ : Finset (Fin m)).image (fun j => σ j.succ.castSucc - 1)

def Ψ_B (n : ℕ) (S : Finset ℕ) (hSc : S.card = m) : Fin (m+2) → ℕ :=
  Fin.cons 0 (Fin.snoc (fun j : Fin m => (S.orderEmbOfFin hSc) j + 1) (m + n + 1))

/- Telescoping helper. -/
lemma sum_succ_sub_castSucc (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ) :
    ∑ i : Fin (m+1), (σ i.succ - σ i.castSucc) = σ (Fin.last (m+1)) - σ 0 := by
  induction' m with m ih
  · rw [Fin.sum_univ_one]
    rfl
  · rw [Fin.sum_univ_succ]
    have hσ' : StrictMono (σ ∘ Fin.succ) := hσ.comp Fin.strictMono_succ
    have key : ∑ i : Fin (m+1), (σ i.succ.succ - σ i.castSucc.succ) =
               σ ((Fin.last (m+1)).succ) - σ ((0 : Fin (m+2)).succ) :=
      ih (σ ∘ Fin.succ) hσ'
    simp only [Fin.castSucc_succ]
    rw [key]
    have h1 : σ 0 ≤ σ ((0 : Fin (m+2)).succ) := hσ.monotone (Fin.zero_le _)
    have h2 : σ ((0 : Fin (m+2)).succ) ≤ σ ((Fin.last (m+1)).succ) :=
      hσ.monotone (Fin.le_last _)
    rw [add_comm]
    exact Nat.sub_add_sub_cancel h2 h1


theorem Φ_A_strictMono (x : Fin (m+1) → ℕ) : StrictMono (Φ_A (m := m) x) := by
  intros i j hij
  unfold Φ_A
  have hij' : i.val < j.val := hij
  have h_sum : (∑ k : Fin (m+1), if (k : ℕ) < i.val then x k else 0) ≤
               (∑ k : Fin (m+1), if (k : ℕ) < j.val then x k else 0) := by
    apply Finset.sum_le_sum
    intros k hk
    by_cases h1 : (k : ℕ) < i.val
    · have h2 : (k : ℕ) < j.val := lt_trans h1 hij'
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
      by_cases h2 : (k : ℕ) < j.val
      · rw [if_pos h2]; exact Nat.zero_le _
      · rw [if_neg h2]
  linarith

theorem Φ_A_zero (x : Fin (m+1) → ℕ) : Φ_A x (0 : Fin (m+2)) = 0 := by
  simp [Φ_A]

theorem Φ_A_last (x : Fin (m+1) → ℕ) (hx : ∑ k, x k = n) :
    Φ_A x (Fin.last (m+1)) = m + n + 1 := by
  unfold Φ_A
  simp only [Fin.val_last]
  have h_sum_eq : (∑ k : Fin (m+1), if (k : ℕ) < m+1 then x k else 0) = ∑ k, x k := by
    apply Finset.sum_congr rfl
    intros k hk
    exact if_pos k.isLt
  rw [h_sum_eq]
  simp only [hx]; linarith

theorem Ψ_A_sum (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ)
    (h0 : σ 0 = 0) (hl : σ (Fin.last (m+1)) = m + n + 1) :
    ∑ i, Ψ_A σ i = n := by
  unfold Ψ_A
  have h_step : ∀ i : Fin (m+1), σ i.castSucc + 1 ≤ σ i.succ := by
    intros i
    exact hσ Fin.castSucc_lt_succ
  have h_telescope := sum_succ_sub_castSucc σ hσ
  have h_eq : ∑ i : Fin (m+1), ((σ i.succ - σ i.castSucc - 1) + 1) =
              ∑ i : Fin (m+1), (σ i.succ - σ i.castSucc) := by
    apply Finset.sum_congr rfl
    intros i hi
    exact Nat.sub_add_cancel (Nat.sub_pos_of_lt (h_step i))
  rw [Finset.sum_add_distrib] at h_eq
  simp [Finset.sum_const, Finset.card_univ] at h_eq
  rw [h_telescope, h0, Nat.sub_zero, hl] at h_eq
  linarith

theorem Ψ_A_Φ_A (x : Fin (m+1) → ℕ) : Ψ_A (Φ_A x) = x := by
  ext i
  have h_fn_eq : (fun k : Fin (m+1) => if (k : ℕ) < i.val + 1 then x k else 0) =
                 (fun k : Fin (m+1) => (if (k : ℕ) < i.val then x k else 0) +
                                       (if k = i then x k else 0)) := by
    ext k
    have hki : k = i ↔ (k : ℕ) = i.val := Fin.ext_iff
    by_cases h1 : (k : ℕ) < i.val
    · have h2 : (k : ℕ) < i.val + 1 := Nat.lt_succ_of_lt h1
      have h3 : ¬ k = i := by
        intros h
        exact Nat.lt_irrefl _ (hki.mp h ▸ h1)
      rw [if_pos h1, if_pos h2, if_neg h3]; ring
    · by_cases h2 : (k : ℕ) = i.val
      · have h3 : (k : ℕ) < i.val + 1 := by rw [h2]; exact Nat.lt_succ_self _
        have h4 : k = i := by exact hki.mpr h2
        rw [if_pos h3, if_neg h1, if_pos h4]
        ring
      · have h_le : i.val ≤ (k : ℕ) := Nat.le_of_not_lt h1
        have h3 : ¬ (k : ℕ) < i.val + 1 := by
          have : i.val < (k : ℕ) := lt_of_le_of_ne h_le (Ne.symm h2)
          linarith
        have h5 : ¬ k = i := by
          intros h
          exact h2 (by rw [h])
        rw [if_neg h3, if_neg h1, if_neg h5]
  have key : (∑ k : Fin (m+1), if (k : ℕ) < i.val + 1 then x k else 0) =
             (∑ k : Fin (m+1), if (k : ℕ) < i.val then x k else 0) + x i := by
    rw [h_fn_eq, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  unfold Ψ_A Φ_A
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [key]
  have h_rearrange :
      (∑ k : Fin (m+1), if (k : ℕ) < i.val then x k else 0) + x i + (i.val + 1) =
      ((∑ k : Fin (m+1), if (k : ℕ) < i.val then x k else 0) + i.val) + (x i + 1) := by ring
  rw [h_rearrange, Nat.add_sub_cancel_left, Nat.add_sub_cancel]

theorem Φ_A_Ψ_A (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ)
    (h0 : σ 0 = 0) (hl : σ (Fin.last (m+1)) = m + n + 1) :
    Φ_A (Ψ_A σ) = σ := by
  ext j
  induction' j using Fin.induction with i ih
  · rw [Φ_A_zero, h0]
  · have h_step : Φ_A (Ψ_A σ) i.succ = Φ_A (Ψ_A σ) i.castSucc + Ψ_A σ i + 1 := by
      unfold Φ_A
      have h_fn_eq : (fun k : Fin (m+1) => if (k : ℕ) < i.val + 1 then Ψ_A σ k else 0) =
                     (fun k : Fin (m+1) => (if (k : ℕ) < i.val then Ψ_A σ k else 0) +
                                           (if k = i then Ψ_A σ k else 0)) := by
        ext k
        have hki : k = i ↔ (k : ℕ) = i.val := Fin.ext_iff
        by_cases h1 : (k : ℕ) < i.val
        · have h2 : (k : ℕ) < i.val + 1 := Nat.lt_succ_of_lt h1
          have h3 : ¬ k = i := by
            intros h
            exact absurd (hki.mp h) h1.ne
          rw [if_pos h1, if_pos h2, if_neg h3]
          ring
        · by_cases h2 : (k : ℕ) = i.val
          · have h3 : (k : ℕ) < i.val + 1 := by rw [h2]; exact Nat.lt_succ_self _
            have h4 : k = i := hki.mpr h2
            rw [if_pos h3, if_neg h1, if_pos h4]
            ring
          · have h_le : i.val ≤ (k : ℕ) := Nat.le_of_not_lt h1
            have h3 : ¬ (k : ℕ) < i.val + 1 := by
              have : i.val < (k : ℕ) := lt_of_le_of_ne h_le (Ne.symm h2)
              linarith
            have h5 : ¬ k = i := by
              intros h
              exact h2 (by rw [h])
            rw [if_neg h3, if_neg h1, if_neg h5]
      have key : (∑ k : Fin (m+1), if (k : ℕ) < i.val + 1 then Ψ_A σ k else 0) =
                 (∑ k : Fin (m+1), if (k : ℕ) < i.val then Ψ_A σ k else 0) + Ψ_A σ i := by
        rw [h_fn_eq, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [key]
      ring
    have h_lt : σ i.castSucc < σ i.succ := hσ Fin.castSucc_lt_succ
    rw [h_step, ih]
    unfold Ψ_A
    have h_pos : 1 ≤ σ i.succ - σ i.castSucc := Nat.sub_pos_of_lt h_lt
    calc σ i.castSucc + (σ i.succ - σ i.castSucc - 1) + 1
        = σ i.castSucc + ((σ i.succ - σ i.castSucc - 1) + 1) := by ring
      _ = σ i.castSucc + (σ i.succ - σ i.castSucc) := by rw [Nat.sub_add_cancel h_pos]
      _ = σ i.succ := Nat.add_sub_of_le (le_of_lt h_lt)


theorem Φ_B_subset (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ)
    (h0 : σ 0 = 0) (hl : σ (Fin.last (m+1)) = m + n + 1) :
    Φ_B (m := m) σ ⊆ range (m + n) := by
  unfold Φ_B
  intros p hp
  rw [Finset.mem_image] at hp
  obtain ⟨j, _, rfl⟩ := hp
  rw [Finset.mem_range]
  have h_lt : j.succ.castSucc < Fin.last (m+1) := by
    rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
    linarith [j.isLt]
  have h_σ_lt : σ j.succ.castSucc < σ (Fin.last (m+1)) := hσ h_lt
  rw [hl] at h_σ_lt
  have h_pos : 1 ≤ σ j.succ.castSucc := by
    have h0_lt : (0 : Fin (m+2)) < j.succ.castSucc := by
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
      simp
    linarith [hσ h0_lt]
  rw [Nat.sub_lt_iff_lt_add h_pos]
  linarith

theorem Φ_B_card (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ) :
    (Φ_B (m := m) σ).card = m := by
  unfold Φ_B
  rw [Finset.card_image_of_injOn, Finset.card_univ, Fintype.card_fin]
  intros j₁ _ j₂ _ heq
  simp only at heq
  have h_pos : ∀ j : Fin m, 1 ≤ σ j.succ.castSucc := by
    intros j
    have h0 : (0 : Fin (m+2)) < j.succ.castSucc := by rw [Fin.lt_def]; simp
    linarith [hσ h0]
  have h1 := h_pos j₁
  have h2 := h_pos j₂
  have h_eq : σ j₁.succ.castSucc = σ j₂.succ.castSucc := by
    rw [← Nat.sub_add_cancel h1, ← Nat.sub_add_cancel h2, heq]
  exact Fin.succ_injective _ (Fin.castSucc_injective _ (hσ.injective h_eq))

theorem Φ_B_mem_powersetCard (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ)
    (h0 : σ 0 = 0) (hl : σ (Fin.last (m+1)) = m + n + 1) :
    Φ_B (m := m) σ ∈ (range (m + n)).powersetCard m := by
  rw [mem_powersetCard]
  exact ⟨Φ_B_subset σ hσ h0 hl, Φ_B_card σ hσ⟩

theorem Ψ_B_zero (S : Finset ℕ) (hSc : S.card = m) :
    Ψ_B n S hSc (0 : Fin (m+2)) = 0 := by
  simp [Ψ_B]

theorem Ψ_B_last (S : Finset ℕ) (hSc : S.card = m) :
    Ψ_B n S hSc (Fin.last (m+1)) = m + n + 1 := by
  simp [Ψ_B]

theorem Ψ_B_strictMono (S : Finset ℕ) (hSc : S.card = m)
    (hSr : S ⊆ range (m + n)) : StrictMono (Ψ_B n S hSc) := by
  have hσS_mono : StrictMono (S.orderEmbOfFin hSc) := (S.orderEmbOfFin hSc).strictMono
  have hσS_lt : ∀ j : Fin m, (S.orderEmbOfFin hSc) j < m + n := by
    intros j
    exact Finset.mem_range.mp (hSr (S.orderEmbOfFin_mem hSc j))
  intros a b hab
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · exact absurd hab (lt_irrefl _)
    · rcases Fin.eq_castSucc_or_eq_last b' with ⟨j, rfl⟩ | rfl
      · unfold Ψ_B
        rw [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc]
        linarith
      · unfold Ψ_B
        rw [Fin.cons_zero, Fin.cons_succ, Fin.snoc_last]
        linarith
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · exact absurd (Fin.zero_le a'.succ) (not_le.mpr hab)
    · have hab' : a' < b' := Fin.succ_lt_succ_iff.mp hab
      rcases Fin.eq_castSucc_or_eq_last a' with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last b' with ⟨j, rfl⟩ | rfl
        · unfold Ψ_B
          rw [Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]
          have hij : i < j := Fin.castSucc_lt_castSucc_iff.mp hab'
          linarith [hσS_mono hij]
        · unfold Ψ_B
          rw [Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last]
          linarith [hσS_lt i]
      · rcases Fin.eq_castSucc_or_eq_last b' with ⟨j, rfl⟩ | rfl
        · exfalso
          have hlt : (Fin.last m).val < j.castSucc.val := hab'
          rw [Fin.val_castSucc, Fin.val_last] at hlt
          exact absurd hlt (not_lt.mpr (le_of_lt j.isLt))
        · exact absurd hab' (lt_irrefl _)

theorem Ψ_B_Φ_B (σ : Fin (m+2) → ℕ) (hσ : StrictMono σ)
    (h0 : σ 0 = 0) (hl : σ (Fin.last (m+1)) = m + n + 1) :
    Ψ_B n (Φ_B σ) (Φ_B_card σ hσ) = σ := by
  have h_pos : ∀ j : Fin m, 1 ≤ σ j.succ.castSucc := by
    intros j
    have h0_lt : (0 : Fin (m+2)) < j.succ.castSucc := by
      rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; simp
    linarith [hσ h0_lt]
  have h_strict : StrictMono (fun j : Fin m => σ j.succ.castSucc - 1) := by
    intros i j hij
    have h_lt : σ i.succ.castSucc < σ j.succ.castSucc :=
      hσ (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_lt_succ_iff.mpr hij))
    have hi := Nat.sub_add_cancel (h_pos i)
    have hj := Nat.sub_add_cancel (h_pos j)
    linarith
  have h_in : ∀ x : Fin m, σ x.succ.castSucc - 1 ∈ Φ_B σ := by
    intros x
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have h_oef : ∀ j : Fin m, (Φ_B σ).orderEmbOfFin (Φ_B_card σ hσ) j = σ j.succ.castSucc - 1 := by
    intros j
    have h := Finset.orderEmbOfFin_unique (Φ_B_card σ hσ) h_in h_strict
    exact (congrFun h j).symm
  ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · rw [Ψ_B_zero, h0]
  · rcases Fin.eq_castSucc_or_eq_last i' with ⟨j, rfl⟩ | rfl
    · unfold Ψ_B
      simp only [Fin.cons_succ, Fin.snoc_castSucc]
      rw [h_oef j, ← Fin.castSucc_succ]
      exact Nat.sub_add_cancel (h_pos j)
    · have h_succ_last : ((Fin.last m).succ : Fin (m+2)) = Fin.last (m+1) := rfl
      rw [h_succ_last, Ψ_B_last]
      exact hl.symm

theorem Φ_B_Ψ_B (S : Finset ℕ) (hSc : S.card = m) (hSr : S ⊆ range (m + n)) :
    Φ_B (Ψ_B n S hSc) = S := by
  unfold Φ_B
  have h_fn_eq : (fun j : Fin m => Ψ_B n S hSc j.succ.castSucc - 1) =
                 (fun j : Fin m => (S.orderEmbOfFin hSc) j) := by
    ext j
    unfold Ψ_B
    rw [Fin.castSucc_succ]
    simp [Fin.cons_succ, Fin.snoc_castSucc]
  rw [h_fn_eq]
  exact S.image_orderEmbOfFin_univ hSc


theorem stars_and_bars (m n : ℕ) :
    (Finset.Nat.antidiagonalTuple (m+1) n).card = (m+n).choose n := by
  have h_rhs : (m+n).choose n = ((range (m+n)).powersetCard m).card := by
    rw [card_powersetCard, card_range, Nat.choose_symm_add]
  rw [h_rhs]
  refine Finset.card_bij'
    (fun (x : Fin (m+1) → ℕ) (_ : x ∈ Finset.Nat.antidiagonalTuple (m+1) n) => Φ_B (Φ_A x))
    (fun (S : Finset ℕ) (hS : S ∈ (range (m+n)).powersetCard m) =>
      Ψ_A (Ψ_B n S (Finset.mem_powersetCard.mp hS).2))
    ?_ ?_ ?_ ?_
  · intros x hx
    rw [Finset.Nat.mem_antidiagonalTuple] at hx
    exact Φ_B_mem_powersetCard (Φ_A x) (Φ_A_strictMono x) (Φ_A_zero x) (Φ_A_last x hx)
  · intros S hS
    rcases Finset.mem_powersetCard.mp hS with ⟨hSr, hSc⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact Ψ_A_sum (Ψ_B n S hSc) (Ψ_B_strictMono S hSc hSr) (Ψ_B_zero S hSc) (Ψ_B_last S hSc)
  · intros x hx
    dsimp
    have hx' := Finset.Nat.mem_antidiagonalTuple.mp hx
    rw [Ψ_B_Φ_B (Φ_A x) (Φ_A_strictMono x) (Φ_A_zero x) (Φ_A_last x hx')]
    exact Ψ_A_Φ_A x
  · intros S hS
    dsimp
    rcases Finset.mem_powersetCard.mp hS with ⟨hSr, hSc⟩
    rw [Φ_A_Ψ_A (Ψ_B n S hSc) (Ψ_B_strictMono S hSc hSr) (Ψ_B_zero S hSc) (Ψ_B_last S hSc)]
    exact Φ_B_Ψ_B S hSc hSr

end StarsAndBars
