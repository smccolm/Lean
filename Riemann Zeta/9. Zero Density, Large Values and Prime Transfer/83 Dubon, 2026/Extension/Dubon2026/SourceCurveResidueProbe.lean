import Dubon2026.SourceCurveResidueFunctional

/-! DUB-17/18 -> Riemann--Roch -> residue duality. A single-place simple
pole probes the actual residue sum. At rational residue fields its value is
one, proving nonvanishing and the exact maximal divisor bound independently
of the still-required global residue identity. The probe argument specializes
the selected CanonicalProbe/CanonicalNonvanishingMaximality source proof in
S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open scoped Classical in
theorem single_mem_adeleBdd (v : Place K F) (g : F) (D : Divisor K F)
    (hg : v.adicValuation g ≤ WithZero.exp (D v)) : Pi.single v g ∈ adeleBdd D := by
  intro w
  rcases eq_or_ne w v with rfl | hw
  · simpa only [Pi.single_eq_same] using hg
  · rw [Pi.single_eq_of_ne hw, Valuation.map_zero]
    exact zero_le'

open scoped Classical in
theorem single_mem_adeleSpace (v : Place K F) (g : F) :
    Pi.single v g ∈ adeleSpace K F := by
  rcases eq_or_ne g 0 with rfl | hg
  · simpa only [Pi.single_zero] using (adeleSpace K F).zero_mem
  · refine adeleBdd_le_adeleSpace
      (single_mem_adeleBdd v g (Finsupp.single v (-v.ord g)) ?_)
    rw [v.adicValuation_eq_exp_neg_ord hg, Finsupp.single_eq_same]

open scoped Classical in
/-- A repartition supported at one actual place. -/
def adeleSingle (v : Place K F) (g : F) : adeleSpace K F :=
  ⟨Pi.single v g, single_mem_adeleSpace v g⟩

theorem Place.trace_one_of_residue_bijective (v : Place K F)
    (hres : Function.Bijective (algebraMap K v.ResidueField)) :
    Algebra.trace K v.ResidueField 1 = 1 := by
  let e := AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hres
  have hd : Module.finrank K v.ResidueField = 1 := by
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [← map_one (algebraMap K v.ResidueField), Algebra.trace_algebraMap, hd, one_smul]

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

open scoped Classical in
theorem weilOfKaehlerK_single
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :
    weilOfKaehlerK Rfam hω (adeleSingle v g) =
      Algebra.trace K v.ResidueField ((Rfam v).res (g * v.differentialCoeff ω)) := by
  rw [weilOfKaehlerK_apply]
  change (∑ᶠ w, kaehlerResidueTermKFam Rfam ω (Pi.single v g) w) = _
  refine (finsum_eq_single _ v (fun w hw => ?_)).trans ?_
  · rw [kaehlerResidueTermKFam_apply, Pi.single_eq_of_ne hw, zero_mul, map_zero, map_zero]
  · rw [kaehlerResidueTermKFam_apply, Pi.single_eq_same]

/-- A single-place repartition making the differential have a simple pole of residue one. -/
def simplePoleProbe (ω : Ω[F⁄K]) (v : Place K F) : adeleSpace K F :=
  adeleSingle v (v.uniformizer⁻¹ * (v.differentialCoeff ω)⁻¹)

theorem weilOfKaehlerK_simplePoleProbe
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F)
    (hres : Function.Bijective (algebraMap K v.ResidueField)) :
    weilOfKaehlerK Rfam hω (simplePoleProbe ω v) = 1 := by
  rw [simplePoleProbe, weilOfKaehlerK_single, mul_assoc,
    inv_mul_cancel₀ (RegularDifferentialsComparison.differentialCoeff_ne_zero hω v), mul_one]
  have hm : v.uniformizer * v.uniformizer⁻¹ ∈ v.toValuationSubring := by
    rw [mul_inv_cancel₀ v.uniformizer_ne_zero]
    exact one_mem _
  rw [(Rfam v).res_simplePole _ hm]
  have he : (⟨v.uniformizer * v.uniformizer⁻¹, hm⟩ : v.toValuationSubring) = 1 :=
    Subtype.ext (mul_inv_cancel₀ v.uniformizer_ne_zero)
  rw [he, map_one, v.trace_one_of_residue_bijective hres]

theorem simplePoleProbe_mem_adeleBdd
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) {D : Divisor K F}
    (hD : canonicalDivisorOf hω v < D v) :
    (simplePoleProbe ω v : Place K F → F) ∈ adeleBdd D := by
  apply single_mem_adeleBdd
  have hc := RegularDifferentialsComparison.differentialCoeff_ne_zero hω v
  rw [v.adicValuation_eq_exp_neg_ord (mul_ne_zero (inv_ne_zero v.uniformizer_ne_zero) (inv_ne_zero hc)),
    v.ord_mul (inv_ne_zero v.uniformizer_ne_zero) (inv_ne_zero hc), v.ord_inv,
    v.ord_inv, v.ord_uniformizer]
  apply WithZero.exp_le_exp.mpr
  rw [canonicalDivisorOf_apply, Place.ordDifferential] at hD
  omega

theorem weilOfKaehlerK_ne_zero_of_rational_residues [Nonempty (Place K F)]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : weilOfKaehlerK Rfam hω ≠ 0 := by
  obtain ⟨v⟩ := ‹Nonempty (Place K F)›
  intro h
  have he := weilOfKaehlerK_simplePoleProbe Rfam hω v (hres v)
  rw [h, LinearMap.zero_apply] at he
  exact zero_ne_one he

theorem weilOfKaehlerK_adeleBound_le_canonical
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : ∀ α : adeleSpace K F, (α : Place K F → F) ∈ adeleBdd D →
      weilOfKaehlerK Rfam hω α = 0) : D ≤ canonicalDivisorOf hω := by
  intro v
  by_contra hv
  have hlt : canonicalDivisorOf hω v < D v := lt_of_not_ge hv
  have hz := hD (simplePoleProbe ω v) (simplePoleProbe_mem_adeleBdd hω v hlt)
  rw [weilOfKaehlerK_simplePoleProbe Rfam hω v (hres v)] at hz
  exact one_ne_zero hz

end
end Dubon2026.SourceCurve
