import Dubon2026.SourceCurveDivisorDimensionGrowth
import Dubon2026.SourceCurveWeilRankOne

/-! DUB-17/18 -> finite torsion descent -> unique reduced representatives.
The least pole bound with a nonzero Riemann--Roch space has dimension one.
This isolates the finite-dimensional minimum argument from the concrete
original-field representation; all premises are discharged by the original
consumer. Adapted from exists_reduced in
S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [HasPrincipalDivisors K F] [∀ v : Place K F, Module.Finite K v.ResidueField]

theorem exists_reduced_space_of_nonempty
    (hfinite : ∀ D : Divisor K F, FiniteDimensional K (LSpace D))
    (c : Divisor K F) (hc : Divisor.degree c = 0) (P : Place K F)
    (hP : Module.finrank K P.ResidueField = 1)
    (hex : ∃ k : ℕ, LSpace (c + (k : ℤ) • Finsupp.single P (1 : ℤ)) ≠ ⊥) :
    ∃ (r : ℕ) (f : F), f ≠ 0 ∧ f ∈ LSpace (c + (r : ℤ) • Finsupp.single P (1 : ℤ)) ∧
      ∀ h ∈ LSpace (c + (r : ℤ) • Finsupp.single P (1 : ℤ)), ∃ a : K, a • f = h := by
  classical
  let Dk : ℕ → Divisor K F := fun k => c + (k : ℤ) • Finsupp.single P (1 : ℤ)
  have hsingle (n : ℤ) : Divisor.degree (Finsupp.single P n) = n := by
    rw [Divisor.degree_single, hP, Nat.cast_one, mul_one]
  have hdegk (k : ℕ) : Divisor.degree (Dk k) = k := by
    simp only [Dk, map_add, map_zsmul, hc, hsingle, smul_eq_mul, mul_one, zero_add]
  let r := Nat.find (p := fun k : ℕ => LSpace (Dk k) ≠ ⊥) hex
  have hr : LSpace (Dk r) ≠ ⊥ := Nat.find_spec (p := fun k : ℕ => LSpace (Dk k) ≠ ⊥) hex
  obtain ⟨f, hfmem, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
  refine ⟨r, f, hf0, hfmem, ?_⟩
  have hprev : LSpace (Dk r - Finsupp.single P (1 : ℤ)) = ⊥ := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · apply lSpace_eq_bot_of_degree_neg
      rw [map_sub, hdegk, h0, hsingle]
      norm_num
    · have heq : Dk r - Finsupp.single P (1 : ℤ) = Dk (r - 1) := by
        dsimp only [Dk]
        rw [Nat.cast_sub hpos, sub_smul, Nat.cast_one, one_smul]
        abel
      rw [heq]
      by_contra hne
      exact Nat.find_min (p := fun k : ℕ => LSpace (Dk k) ≠ ⊥) hex (Nat.sub_lt hpos one_pos) hne
  letI := hfinite (Dk r)
  have hle : ell (Dk r) ≤ 1 := by
    have hD : Dk r - Finsupp.single P (1 : ℤ) ≤ Dk r := by
      intro v
      simp only [Finsupp.sub_apply]
      apply sub_le_self
      by_cases hv : v = P <;> simp [hv]
    have h := ell_sub_ell_le_degree_sub_degree hD
    have hzero : ell (Dk r - Finsupp.single P (1 : ℤ)) = 0 := by rw [ell, hprev, finrank_bot]
    rw [hzero, map_sub, hsingle] at h
    omega
  have hfne : (⟨f, hfmem⟩ : LSpace (Dk r)) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hone : Module.finrank K (LSpace (Dk r)) = 1 :=
    le_antisymm hle (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hfmem⟩, hfne⟩)
  intro h hh
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨f, hfmem⟩ : LSpace (Dk r)) hfne).mp hone ⟨h, hh⟩
  exact ⟨a, by simpa only [Submodule.coe_smul_of_tower] using congrArg Subtype.val ha⟩


end
end Dubon2026.SourceCurve.ConstantField
