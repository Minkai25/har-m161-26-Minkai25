import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Setoid.Partition

open scoped Pointwise

#check MulAction.injective
theorem coset_size {G : Type*} [Group G] (H : Subgroup G) (g₁ : G) :
  Set.ncard (g₁ • (H : Set G)) = Set.ncard ((H : Set G)) := by
  apply Set.ncard_image_of_injOn
  intro x hx y hy h
  dsimp at h
  exact mul_left_cancel h

theorem coset_eq_or_disjoint {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    a • (H : Set G) = b • (H : Set G) ∨ Disjoint (a • (H : Set G)) (b • (H : Set G)) := by
    by_cases h : ∃ x, x ∈ a • (H : Set G) ∧ x ∈ b • (H : Set G)
    · left
      rcases h with ⟨x, ha, hb⟩
      rcases ha with ⟨h1, hh1, ha⟩
      dsimp only at ha
      rcases hb with ⟨h2, hh2, hb⟩
      dsimp only at hb
      have subset: a • (H : Set G) ⊆ b • (H : Set G) := by
        intro g hag
        rcases hag with ⟨h, hh, hg⟩
        dsimp only at hg
        have asimp : a = b • h2 • (h1)⁻¹ := by
          rw[← hb] at ha
          simp only [smul_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
          exact ha
        rw[asimp] at hg
        apply Set.mem_smul_set.mpr
        use h2 • h1⁻¹ • h
        constructor
        · apply H.mul_mem hh2
          apply H.mul_mem
          · exact H.inv_mem hh1
          · exact hh
        simp only [smul_assoc] at hg
        exact hg
      have supset: a • (H : Set G) ⊇ b • (H : Set G) := by
        intro g hag
        rcases hag with ⟨h, hh, hg⟩
        dsimp only at hg
        have bsimp : a • h1 • h2⁻¹= b := by
          rw[← hb] at ha
          simp only [smul_eq_mul, ← mul_assoc, mul_inv_eq_iff_eq_mul]
          exact ha
        rw[← bsimp] at hg
        apply Set.mem_smul_set.mpr
        use h1 • h2⁻¹ • h
        constructor
        · apply H.mul_mem hh1
          apply H.mul_mem
          · exact H.inv_mem hh2
          · exact hh
        simp only [smul_assoc] at hg
        exact hg
      exact Set.Subset.antisymm subset supset
    right
    rw [Set.disjoint_left]
    intro x hx hbx
    exact h ⟨x, hx, hbx⟩

theorem memb_some_coset {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    ∃ a : G, g ∈ a • (H : Set G) := by
    use g
    apply Set.mem_smul_set.mpr
    use 1
    constructor
    · exact H.one_mem
    exact mul_one g

theorem cosets_partition (G : Type*) [Group G] (H : Subgroup G) :
    Setoid.IsPartition (QuotientGroup.leftRel H).classes :=
  Setoid.isPartition_classes (QuotientGroup.leftRel H)
