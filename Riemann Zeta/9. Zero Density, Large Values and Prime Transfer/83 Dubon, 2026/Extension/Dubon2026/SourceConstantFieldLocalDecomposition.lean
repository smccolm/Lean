import Dubon2026.SourceConstantFieldLocalCombinations
import Dubon2026.SourceConstantFieldResidueDigits

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact constant-field place extension. A residue digit followed by a uniformizer
factor decomposes finite local combinations. The original consumer supplies
the proved finite residue field; no IsCurveOver or order-preservation premise
is introduced. This is the local calculation needed to show extension has
ramification index one and is unique.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

theorem decomp [IsAlgClosed K] [Module.Finite K P.ResidueField] {π : P.toValuationSubring} (hπ : Irreducible π)
    (w : ι →₀ P.toValuationSubring) (hw : w ≠ 0) :
    ∃ (k : ℕ) (d : K') (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
      Psi F' B P w = algebraMap F F' (π : F) ^ k *
        (algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w') := by
  classical
  choose dig rest hdr hr0 using exists_digit P hπ
  have hrest0 : rest 0 = 0 := hr0 0 rfl
  have step : ∀ w : ι →₀ P.toValuationSubring,
      Psi F' B P w = algebraMap K' F' (∑ j ∈ w.support, dig (w j) • B j) +
        algebraMap F F' (π : F) * Psi F' B P (w.mapRange rest hrest0) := by
    intro w
    rw [Psi_apply F' B P (w.mapRange _ _),
      Finsupp.sum_mapRange_index (fun j => by simp)]
    rw [Psi_apply]
    simp only [Finsupp.sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hdr (w j)]
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, Place.coe_algebraMap, map_add, map_mul,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K K' F',
      ← IsScalarTower.algebraMap_apply K F F']
    ring
  suffices h : ∀ (n : ℕ) (w : ι →₀ P.toValuationSubring) (j₁ : ι), w j₁ ≠ 0 →
      P.ord ((w j₁ : P.toValuationSubring) : F) < n →
      ∃ (k : ℕ) (d : K') (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
        Psi F' B P w = algebraMap F F' (π : F) ^ k *
          (algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w') by
    obtain ⟨j₁, hj₁⟩ : ∃ j₁, w j₁ ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (Finsupp.ext h)
    exact h ((P.ord ((w j₁ : P.toValuationSubring) : F)).toNat + 1) w j₁ hj₁ (by omega)
  intro n
  induction n with
  | zero =>
    intro w j₁ _ hlt
    have := P.ord_nonneg_of_mem (w j₁).2
    push_cast at hlt
    omega
  | succ n ih =>
    intro w j₁ hj₁ hlt
    by_cases hdig : ∃ j ∈ w.support, dig (w j) ≠ 0
    · refine ⟨0, ∑ j ∈ w.support, dig (w j) • B j, w.mapRange rest hrest0, ?_, ?_⟩
      · intro hd
        obtain ⟨j, hj, hne⟩ := hdig
        exact hne (linearIndependent_iff'.1 B.linearIndependent w.support (fun j => dig (w j))
          hd j hj)
      · rw [pow_zero, one_mul]
        exact step w
    · push Not at hdig
      have hd0 : ∑ j ∈ w.support, dig (w j) • B j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hdig j hj, zero_smul]
      have hj₁s : j₁ ∈ w.support := Finsupp.mem_support_iff.2 hj₁
      have hwj : ((w j₁ : P.toValuationSubring) : F) = (π : F) * (rest (w j₁) : F) := by
        conv_lhs => rw [hdr (w j₁)]
        rw [hdig j₁ hj₁s]
        simp
      have hr : rest (w j₁) ≠ 0 := by
        intro h
        apply hj₁
        apply Subtype.ext
        rw [hwj, h]
        simp
      have hw' : (w.mapRange rest hrest0) j₁ ≠ 0 := by
        rwa [Finsupp.mapRange_apply]
      have hord : P.ord (((w.mapRange rest hrest0) j₁ : P.toValuationSubring) : F) < n := by
        rw [Finsupp.mapRange_apply]
        have hr0' : ((rest (w j₁) : P.toValuationSubring) : F) ≠ 0 := fun h => hr (Subtype.ext h)
        have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
        have := P.ord_mul hπ0 hr0'
        rw [← hwj, P.ord_coe_irreducible hπ] at this
        push_cast at hlt
        omega
      obtain ⟨k, d, w'', hd, heq⟩ := ih (w.mapRange rest hrest0) j₁ hw' hord
      refine ⟨k + 1, d, w'', hd, ?_⟩
      rw [step w, hd0, map_zero, zero_add, heq]
      ring

end
end Dubon2026.SourceCurve.ConstantField
