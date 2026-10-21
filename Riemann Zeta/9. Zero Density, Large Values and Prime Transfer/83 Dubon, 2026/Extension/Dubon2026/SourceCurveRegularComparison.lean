import Dubon2026.SourceCurveRiemannRochSpace
import Dubon2026.SourceCurveCanonicalDivisor

/-! DUB-17/18 -> matching cusp-form dimension -> regular differential dimension.
The literal canonical-divisor space is linearly equivalent to the actual
regular differential space. Adapted from the comparison portion of
S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The Riemann--Roch/genus assertion
is not assumed by this comparison and remains a separate obligation.
-/
namespace Dubon2026.SourceCurve.RegularDifferentialsComparison
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem differentialCoeff_ne_zero {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) [v.DCoordGenerates] :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

theorem exists_smul_eq [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω : Ω[F⁄K]) :
    ∃ h : F, h • ω₀ = ω :=
  (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2 ω

section Comparison

variable [Nontrivial Ω[F⁄K]] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

theorem smul_mem_regularDifferentials_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : F) :
    h • ω₀ ∈ regularDifferentials K F ↔ h ∈ LSpace (canonicalDivisorOf hω₀) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [zero_smul, Submodule.zero_mem]
  rw [mem_regularDifferentials_iff, mem_lSpace_iff_ord, or_iff_right hh]
  refine forall_congr' fun v => ?_
  have hc : v.differentialCoeff ω₀ ≠ 0 := differentialCoeff_ne_zero hω₀ v

  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩

    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    have h0 : 0 ≤ v.ord (h * v.differentialCoeff ω₀) :=
      hgu ▸ v.ord_nonneg_of_mem hg
    rw [v.ord_mul hh hc] at h0
    linarith
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine v.mem_of_ord_nonneg ?_
    rw [v.ord_mul hh hc]
    linarith

/-- Multiply a function in the canonical-divisor space by its defining differential. -/
def toRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) →ₗ[K] regularDifferentials K F where
  toFun h := ⟨(h : F) • ω₀, (smul_mem_regularDifferentials_iff hω₀ (h : F)).mpr h.2⟩
  map_add' h₁ h₂ := by
    ext
    simp [add_smul]
  map_smul' c h := by
    ext
    simp [smul_assoc]

theorem toRegular_apply {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : LSpace (canonicalDivisorOf hω₀)) :
    ((toRegular hω₀ h : regularDifferentials K F) : Ω[F⁄K]) = (h : F) • ω₀ := rfl

theorem toRegular_bijective [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Function.Bijective (toRegular (K := K) (F := F) hω₀) := by
  constructor
  · intro h₁ h₂ hEq
    have hEq' : ((h₁ : F) - (h₂ : F)) • ω₀ = 0 := by
      have := congrArg (fun x : regularDifferentials K F => (x : Ω[F⁄K])) hEq
      simp only [toRegular_apply] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hEq' with h0 | h0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd h0 hω₀
  · rintro ⟨ω, hω⟩
    obtain ⟨h, rfl⟩ := exists_smul_eq hω₀ ω
    exact ⟨⟨h, (smul_mem_regularDifferentials_iff hω₀ h).mp hω⟩, rfl⟩

/-- The actual canonical-divisor space is linearly equivalent to regular differentials. -/
def lSpaceCanonicalEquivRegular [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) ≃ₗ[K] regularDifferentials K F :=
  LinearEquiv.ofBijective (toRegular hω₀) (toRegular_bijective hω₀)


end Comparison
end
end Dubon2026.SourceCurve.RegularDifferentialsComparison
