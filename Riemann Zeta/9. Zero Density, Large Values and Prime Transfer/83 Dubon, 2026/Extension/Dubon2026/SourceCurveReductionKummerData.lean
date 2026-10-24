import Dubon2026.SourceCurveReductionPicardR2

/-! DUB-17/18 -> original Frobenius/inertia -> torsion injectivity of modular
reduction -> Kummer power lifting. A torsion class in the actual Picard kernel
gives a normalized function with divisible orders and a principal reduced
divisor. Adapted from the Kummer section of
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero.
Existing divisor quotients and constant normalization are reused. -/
namespace Dubon2026.SourceCurve.ConstantReduction
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_kummer_divisor_data (R : ConstantReduction A F Fbar)
    (z : Pic0 L F) (m : ℕ) (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    ∃ D : Divisor.degZero (K := L) (F := F), Pic0.mk D = z ∧
      ∃ f : R.integers, R.residue f ≠ 0 ∧
        (∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (f : F)) ∧
        ∃ g : Fbar, g ≠ 0 ∧
          (∀ Q, Finsupp.mapDomain R.placeMap (D : Divisor L F) Q = Q.ord g) ∧
          ∀ Q : Place (ResidueField A) Fbar,
            Q.ord (R.residue f) = (m : ℤ) * Q.ord g := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  have hmD : ((m • D : Divisor.degZero (K := L) (F := F)) : Divisor L F) ∈
      Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk (m • D) = 0 := by
      change QuotientAddGroup.mk (m • D) = (0 : Pic0 L F)
      rw [QuotientAddGroup.mk_nsmul]
      exact hmz
    have h2 := (QuotientAddGroup.eq_zero_iff (m • D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨f₀, hf₀, hDf₀⟩ := hmD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f₀ hf₀
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have h0 : (⟨(0 : L) • f₀, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [h0, map_zero]
  have hdivf : ∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (c • f₀) := by
    intro P
    rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr hc0) hf₀,
      P.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c), zero_add, ← hDf₀ P,
      AddSubgroupClass.coe_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  have hrD : (R.degZeroMap D : Divisor (ResidueField A) Fbar) ∈
      Divisor.principal (K := ResidueField A) (F := Fbar) := by
    have h1 : Pic0.mk (R.degZeroMap D) = 0 := by rw [← pic0Map_mk]; exact hz
    have h2 := (QuotientAddGroup.eq_zero_iff (R.degZeroMap D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨g, hg, hDg⟩ := hrD
  refine ⟨D, rfl, ⟨c • f₀, hc⟩, hres, hdivf, g, hg, fun Q => by
    rw [← hDg Q]; rfl, fun Q => ?_⟩
  have key := R.mapDomain_placeMap ⟨c • f₀, hc⟩ hres
    ((m • D : Divisor.degZero (K := L) (F := F)) : Divisor L F)
    (fun P => by
      change (m • (D : Divisor L F)) P = P.ord (c • f₀)
      rw [Finsupp.smul_apply, nsmul_eq_mul, hdivf P]) Q
  rw [← key, AddSubgroupClass.coe_nsmul, Finsupp.mapDomain_smul,
    Finsupp.smul_apply, nsmul_eq_mul, ← hDg Q]
  rfl

end
end Dubon2026.SourceCurve.ConstantReduction
