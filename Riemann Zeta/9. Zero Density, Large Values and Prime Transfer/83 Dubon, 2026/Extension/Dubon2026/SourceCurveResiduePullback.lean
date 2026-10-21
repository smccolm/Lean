import Dubon2026.SourceCurveLogarithmicResidue
import Dubon2026.SourceCurvePlaceRestriction

/-! DUB-17/18 -> original regular differential dimension -> global residue
identity -> finite-extension comparison. Restriction of an actual place
scales the residue of g dπ by the order of the mapped base uniformizer.
Integral coefficients and pure poles determine the map uniquely; the power
residue formula supplies its normalization without completion machinery.
The global fiber sum and trace comparison remain separate obligations.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsIntegral F E] (w : Place K E)
variable [w.DCoordGenerates] [Nontrivial Ω[E⁄K]]

theorem differentialCoeff_map_restrict [(w.restrict F).DCoordGenerates]
    (ω : Ω[F⁄K]) :
    w.differentialCoeff (KaehlerDifferential.map K K F E ω) =
      algebraMap F E ((w.restrict F).differentialCoeff ω) *
        w.coordinateDerivation (algebraMap F E (w.restrict F).uniformizer) := by
  conv_lhs => rw [← (w.restrict F).differentialCoeff_smul_dCoord ω]
  rw [map_smul]
  change w.differentialCoeff ((w.restrict F).differentialCoeff ω •
    KaehlerDifferential.map K K F E (D K F (w.restrict F).uniformizer)) = _
  rw [KaehlerDifferential.map_D,
    ← algebraMap_smul E ((w.restrict F).differentialCoeff ω), w.differentialCoeff_smul]
  rfl

variable [CharZero K]
variable [Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K w.ResidueField]

theorem localResidueScalar_restrict_pullback
    (hbase : Function.Surjective (algebraMap K (w.restrict F).ResidueField))
    (htop : Function.Surjective (algebraMap K w.ResidueField)) (g : F) :
    w.localResidueScalar (algebraMap F E g *
      w.coordinateDerivation (algebraMap F E (w.restrict F).uniformizer)) =
      (w.ord (algebraMap F E (w.restrict F).uniformizer) : K) *
        (w.restrict F).localResidueScalar g := by
  let v := w.restrict F
  let π : E := algebraMap F E v.uniformizer
  let e : K := (w.ord π : K)
  let φ : F →ₗ[K] K := w.localResidueScalar.comp
    ((LinearMap.mulRight K (w.coordinateDerivation π)).comp
      (IsScalarTower.toAlgHom K F E).toLinearMap)
  have hπ : π ≠ 0 := by
    simpa only [map_zero] using (algebraMap F E).injective.ne v.uniformizer_ne_zero
  have hπreg : π ∈ w.toValuationSubring :=
    (w.mem_restrict_iff).mp v.uniformizerSubring.2
  have hδreg : w.coordinateDerivation π ∈ w.toValuationSubring :=
    w.differentialCoeff_D_mem_of_mem hπreg
  have hzero : φ - e • v.localResidueScalar = 0 := by
    apply v.linearMap_zero_of_integral_and_poles hbase
    · intro f hf
      change w.localResidueScalar (algebraMap F E f * w.coordinateDerivation π) -
        e * v.localResidueScalar f = 0
      rw [v.localResidueScalar_of_mem hf, mul_zero, sub_zero]
      exact w.localResidueScalar_of_mem (mul_mem ((w.mem_restrict_iff).mp hf) hδreg)
    · intro n
      change w.localResidueScalar (algebraMap F E (v.uniformizer ^ (-(n + 1 : ℤ))) *
        w.coordinateDerivation π) - e * v.localResidueScalar
          (v.uniformizer ^ (-(n + 1 : ℤ))) = 0
      rw [map_zpow₀, w.localResidueScalar_power_differential htop hπ,
        v.localResidueScalar_neg_pow]
      by_cases hn : n = 0
      · subst n
        simp only [Nat.cast_zero, zero_add, ↓reduceIte, mul_one, e, sub_self]
      · rw [if_neg (show -(n + 1 : ℤ) ≠ -1 by omega), if_neg hn, mul_zero, sub_self]
  have he := LinearMap.congr_fun hzero g
  change w.localResidueScalar (algebraMap F E g * w.coordinateDerivation π) -
    e * v.localResidueScalar g = 0 at he
  exact sub_eq_zero.mp he

theorem localResidueScalar_map_restrict [(w.restrict F).DCoordGenerates]
    (hbase : Function.Surjective (algebraMap K (w.restrict F).ResidueField))
    (htop : Function.Surjective (algebraMap K w.ResidueField)) (ω : Ω[F⁄K]) :
    w.localResidueScalar (w.differentialCoeff (KaehlerDifferential.map K K F E ω)) =
      (w.ord (algebraMap F E (w.restrict F).uniformizer) : K) *
        (w.restrict F).localResidueScalar ((w.restrict F).differentialCoeff ω) := by
  rw [w.differentialCoeff_map_restrict]
  exact w.localResidueScalar_restrict_pullback hbase htop _

end
end Dubon2026.SourceCurve.Place
