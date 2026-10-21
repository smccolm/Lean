import Dubon2026.SourceCurveCanonicalResidueData
import Dubon2026.SourceCurveRegularComparison
import Dubon2026.SourceCurveAdelicIndex
import Mathlib.RingTheory.Trace.Basic

/-! DUB-17/18 -> original regular differential dimension -> Riemann--Roch
-> residue duality. Actual local canonical residues define a finite sum on
repartitions. This functional annihilates the canonical divisor bound;
annihilation of global functions is the still-required global residue identity.
Selected source: Def_AlgebraicCurve_LocalResidue, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.CanonicalLocalResidueDataK.res_eq_zero_of_ord_nonneg
    {v : Place K F} (R : v.CanonicalLocalResidueDataK) {f : F}
    (hf : f = 0 ∨ 0 ≤ v.ord f) : R.res f = 0 := by
  rcases hf with rfl | hf
  · exact map_zero _
  · exact R.res_of_mem f (v.mem_of_ord_nonneg hf)

/-- The trace to constants of the local differential residue. -/
def Place.kaehlerResidueTermK (v : Place K F) (R : v.CanonicalLocalResidueDataK)
    (ω : Ω[F⁄K]) (f : F) : K :=
  Algebra.trace K v.ResidueField (R.res (f * v.differentialCoeff ω))

/-- Local differential residues on actual repartitions. -/
def kaehlerResidueTermKFam (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) : K :=
  v.kaehlerResidueTermK (Rfam v) ω (α v)

@[simp]
theorem kaehlerResidueTermKFam_apply (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω α v
      = Algebra.trace K v.ResidueField ((Rfam v).res (α v * v.differentialCoeff ω)) := rfl

theorem kaehlerResidueTermKFam_eq_zero_of_ord_nonneg
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]}
    {α : Place K F → F} {v : Place K F}
    (h : α v * v.differentialCoeff ω = 0 ∨ 0 ≤ v.ord (α v * v.differentialCoeff ω)) :
    kaehlerResidueTermKFam Rfam ω α v = 0 := by
  rw [kaehlerResidueTermKFam_apply, (Rfam v).res_eq_zero_of_ord_nonneg h, map_zero]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem kaehlerResidueTermKFam_eq_zero_of_adeleBdd_canonical
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleBdd (canonicalDivisorOf hω)) (v : Place K F) :
    kaehlerResidueTermKFam Rfam ω α v = 0 := by
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := RegularDifferentialsComparison.differentialCoeff_ne_zero hω v
    rw [v.ord_mul h0 hg]
    have hαv : -(canonicalDivisorOf hω v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

theorem kaehlerResidueTermKFam_support_subset
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    Function.support (kaehlerResidueTermKFam Rfam ω α)
      ⊆ ↑(D - canonicalDivisorOf hω).support := by
  intro v hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply, ne_eq, sub_eq_zero]
  intro hDω
  apply hv
  refine kaehlerResidueTermKFam_eq_zero_of_ord_nonneg Rfam ?_
  rcases eq_or_ne (α v) 0 with h0 | h0
  · exact Or.inl (by rw [h0, zero_mul])
  · refine Or.inr ?_
    have hg := RegularDifferentialsComparison.differentialCoeff_ne_zero hω v
    rw [v.ord_mul h0 hg]
    have hαv : -(D v) ≤ v.ord (α v) := by
      have hval := hα v
      rw [v.adicValuation_eq_exp_neg_ord h0] at hval
      exact neg_le_of_neg_le (WithZero.exp_le_exp.mp hval)
    rw [hDω, canonicalDivisorOf_apply hω v, Place.ordDifferential] at hαv
    linarith

theorem kaehlerResidueTermKFam_support_finite
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    (Function.support (kaehlerResidueTermKFam Rfam ω α)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _)
    (kaehlerResidueTermKFam_support_subset Rfam hω hα)

theorem kaehlerResidueTermKFam_support_finite_of_adeleSpace
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    (Function.support (kaehlerResidueTermKFam Rfam ω α)).Finite := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact kaehlerResidueTermKFam_support_finite Rfam hω hD

/-- The actual finite sum of local residues on repartitions. -/
def weilOfKaehlerK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Module.Dual K (adeleSpace K F) where
  toFun α := ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (α : Place K F → F) v
  map_add' α β := by
    have hsupα := kaehlerResidueTermKFam_support_finite_of_adeleSpace Rfam hω α.2
    have hsupβ := kaehlerResidueTermKFam_support_finite_of_adeleSpace Rfam hω β.2
    rw [← finsum_add_distrib hsupα hsupβ]
    refine finsum_congr fun v => ?_
    simp only [kaehlerResidueTermKFam_apply]
    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]
  map_smul' c α := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    refine finsum_congr fun v => ?_
    simp only [kaehlerResidueTermKFam_apply]
    rw [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, mul_assoc,
      ← Algebra.smul_def, map_smul, map_smul]

theorem weilOfKaehlerK_apply (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (α : adeleSpace K F) :
    weilOfKaehlerK Rfam hω α
      = ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (α : Place K F → F) v := rfl

theorem weilOfKaehlerK_vanish_adeleBdd_canonical
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd (canonicalDivisorOf hω)) :
    weilOfKaehlerK Rfam hω α = 0 := by
  rw [weilOfKaehlerK_apply]
  exact finsum_eq_zero_of_forall_eq_zero
    (kaehlerResidueTermKFam_eq_zero_of_adeleBdd_canonical Rfam hω hα)

end
end Dubon2026.SourceCurve
