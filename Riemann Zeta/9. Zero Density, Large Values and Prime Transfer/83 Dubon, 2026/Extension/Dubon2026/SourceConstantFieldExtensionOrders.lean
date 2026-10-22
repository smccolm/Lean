import Dubon2026.SourceConstantFieldLocalFractions
import Dubon2026.SourceConstantFieldLocalDecomposition
import Dubon2026.SourceConstantFieldLocalUnits

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact constant-field place extension. Local fractions and residue digits force the
extended uniformizer to have order one. Hence every original function retains
its normalized order, and two places above one original place coincide.
The original consumer supplies image generation and finite residue fields.
Place existence is a separate construction, not a hypothesis of that consumer.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  [IsAlgClosed K] (P : Place K F) [Module.Finite K P.ResidueField]

theorem extension_order_and_unique
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    (∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ f : F, Q'.ord (algebraMap F F' f) = P.ord f) ∧
    (∀ Q₁ Q₂ : Place K' F',
      Q₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q₁ = Q₂) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπ1 : P.ord (π : F) = 1 := P.ord_coe_irreducible hπ
  have hπinv : (π : F)⁻¹ ∉ P.toValuationSubring := by
    intro h
    have := P.ord_nonneg_of_mem h
    rw [P.ord_inv, hπ1] at this
    omega
  let B := Module.Basis.ofVectorSpace K K'

  have memO : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ o : P.toValuationSubring, algebraMap F F' (o : F) ∈ Q'.toValuationSubring := by
    intro Q' hQ o
    have : (o : F) ∈ Q'.toValuationSubring.comap (algebraMap F F') := by rw [hQ]; exact o.2
    exact ValuationSubring.mem_comap.1 this
  have pinv : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      (algebraMap F F' (π : F))⁻¹ ∉ Q'.toValuationSubring := by
    intro Q' hQ h
    have h2 : (π : F)⁻¹ ∈ Q'.toValuationSubring.comap (algebraMap F F') :=
      ValuationSubring.mem_comap.2 (by rwa [map_inv₀])
    rw [hQ] at h2
    exact hπinv h2

  have ordPsi : ∀ w : _ →₀ P.toValuationSubring, w ≠ 0 → ∃ k : ℕ, ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Psi F' B P w ≠ 0 ∧
        Q'.ord (Psi F' B P w) = k * Q'.ord (algebraMap F F' (π : F)) := by
    intro w hw
    obtain ⟨k, d, w', hd, heq⟩ := decomp F' B P hπ w hw
    refine ⟨k, fun Q' hQ => ?_⟩
    have hunit := ne_zero_and_inv_mem_of_add Q'.toValuationSubring
      (a := algebraMap K' F' d) (m := Psi F' B P w') (p := algebraMap F F' (π : F))
      (Q'.algebraMap_mem' d) (by rw [← map_inv₀]; exact Q'.algebraMap_mem' d⁻¹)
      (by simpa using hd)
      (Psi_mem F' B P Q'.toValuationSubring Q'.algebraMap_mem' (memO Q' hQ) w')
      (memO Q' hQ π) (pinv Q' hQ)
    have hmem : algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w' ∈
        Q'.toValuationSubring :=
      add_mem (Q'.algebraMap_mem' d)
        (mul_mem (memO Q' hQ π)
          (Psi_mem F' B P Q'.toValuationSubring Q'.algebraMap_mem' (memO Q' hQ) w'))
    have hpk : algebraMap F F' (π : F) ^ k ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hπ0)
    refine ⟨by rw [heq]; exact mul_ne_zero hpk hunit.1, ?_⟩
    rw [heq, Q'.ord_mul hpk hunit.1, ord_eq_zero_of_mem_of_inv_mem Q' hmem hunit.2,
      ← zpow_natCast, Q'.ord_zpow]
    ring

  have ordAny : ∀ z : F', z ≠ 0 → ∃ m : ℤ, ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q'.ord z = m * Q'.ord (algebraMap F F' (π : F)) := by
    intro z hz
    obtain ⟨w₁, w₂, hne, hzw⟩ := exists_mul_Psi_eq F' B P hgen hz
    have hw₂ : w₂ ≠ 0 := by rintro rfl; exact hne (map_zero _)
    have hw₁ : w₁ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hzw
      exact mul_ne_zero hz hne hzw
    obtain ⟨k₁, h₁⟩ := ordPsi w₁ hw₁
    obtain ⟨k₂, h₂⟩ := ordPsi w₂ hw₂
    refine ⟨k₁ - k₂, fun Q' hQ => ?_⟩
    have e₁ := (h₁ Q' hQ).2
    have e₂ := (h₂ Q' hQ).2
    have := Q'.ord_mul hz hne
    rw [hzw, e₁, e₂] at this
    linarith

  have eOne : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q'.ord (algebraMap F F' (π : F)) = 1 := by
    intro Q' hQ
    obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible Q'.toValuationSubring
    have hπ'0 : (π' : F') ≠ 0 := fun h => hπ'.ne_zero (Subtype.ext h)
    obtain ⟨m, hm⟩ := ordAny (π' : F') hπ'0
    have h := hm Q' hQ
    rw [Q'.ord_coe_irreducible hπ'] at h
    have hnn : 0 ≤ Q'.ord (algebraMap F F' (π : F)) := Q'.ord_nonneg_of_mem (memO Q' hQ π)
    exact Int.eq_one_of_dvd_one hnn ⟨m, by rw [mul_comm]; exact h⟩
  have ordEq : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ f : F, Q'.ord (algebraMap F F' f) = P.ord f := by
    intro Q' hQ f
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf hπ
    have hu0 : algebraMap F F' ((u : P.toValuationSubring) : F) ≠ 0 := by
      rw [map_ne_zero]
      exact fun h => u.ne_zero (Subtype.ext h)
    have hzp : algebraMap F F' (π : F) ^ P.ord f ≠ 0 := zpow_ne_zero _ ((map_ne_zero _).2 hπ0)
    have huinv : (algebraMap F F' ((u : P.toValuationSubring) : F))⁻¹ ∈ Q'.toValuationSubring := by
      have hmul : ((u : P.toValuationSubring) : F) *
          (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) = 1 := by
        rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
      rw [← map_inv₀, ← eq_inv_of_mul_eq_one_right hmul]
      exact memO Q' hQ _
    conv_lhs => rw [hu, map_mul, map_zpow₀]
    rw [Q'.ord_mul hu0 hzp, Q'.ord_zpow, eOne Q' hQ,
      ord_eq_zero_of_mem_of_inv_mem Q' (memO Q' hQ u) huinv]
    ring

  have uniq : ∀ Q₁ Q₂ : Place K' F',
      Q₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q₁ = Q₂ := by
    intro Q₁ Q₂ h1 h2
    apply Place.ext
    ext z
    rcases eq_or_ne z 0 with rfl | hz
    · simp
    obtain ⟨m, hm⟩ := ordAny z hz
    rw [Q₁.mem_iff_ord_nonneg (f := z), Q₂.mem_iff_ord_nonneg (f := z), hm Q₁ h1, hm Q₂ h2, eOne Q₁ h1,
      eOne Q₂ h2]

  exact ⟨ordEq, uniq⟩

end
end Dubon2026.SourceCurve.ConstantField
