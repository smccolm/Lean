import Dubon2026.SourceCurveLogarithmicResidue
import Dubon2026.SourceCurveResidueFunctional

/-! DUB-17/18 -> function-field Riemann--Roch -> global residue identity
-> the characteristic-zero power and logarithmic differential atoms.
The local power formula and the actual principal-divisor product formula
give zero global residue for f^n df. Arbitrary differentials still require
the rational-function spanning and finite-extension trace arguments.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
variable [Nontrivial Ω[F⁄K]] [∀ v : Place K F, v.DCoordGenerates]
variable [∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]

theorem kaehlerResidueTermKFam_power_differential
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    {f : F} (hf : f ≠ 0) (n : ℤ) (v : Place K F) :
    kaehlerResidueTermKFam Rfam (D K F f) (diagonalHom K F (f ^ n)) v =
      if n = -1 then ((v.ord f * (Module.finrank K v.ResidueField : ℤ) : ℤ) : K)
      else 0 := by
  rw [kaehlerResidueTermKFam_apply]
  change Algebra.trace K v.ResidueField ((Rfam v).res (f ^ n *
    v.differentialCoeff (D K F f))) = _
  rw [v.canonicalLocalResidueData_power_differential (hres v) (Rfam v) hf n]
  split_ifs
  · rw [← map_intCast (algebraMap K v.ResidueField), Algebra.trace_algebraMap]
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    exact mul_comm _ _
  · exact map_zero _

theorem residueSum_power_differential [HasPrincipalDivisors K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    {f : F} (hf : f ≠ 0) (n : ℤ) :
    (∑ᶠ v : Place K F,
      kaehlerResidueTermKFam Rfam (D K F f) (diagonalHom K F (f ^ n)) v) = 0 := by
  classical
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  by_cases hn : n = -1
  · have heq : (fun v : Place K F =>
        kaehlerResidueTermKFam Rfam (D K F f) (diagonalHom K F (f ^ n)) v) =
        (fun v => ((E v * (Module.finrank K v.ResidueField : ℤ) : ℤ) : K)) := by
      funext v
      rw [kaehlerResidueTermKFam_power_differential Rfam hres hf n v, if_pos hn, hE]
    rw [heq, finsum_eq_finsetSum_of_support_subset _ (s := E.support) (by
      intro v hv
      apply Finsupp.mem_support_iff.mpr
      intro hv0
      exact hv (by simp only [hv0, zero_mul, Int.cast_zero]))]
    rw [← Int.cast_sum]
    change ((Divisor.degree E : ℤ) : K) = 0
    rw [hdeg, Int.cast_zero]
  · have heq : (fun v : Place K F =>
        kaehlerResidueTermKFam Rfam (D K F f) (diagonalHom K F (f ^ n)) v) = 0 := by
      funext v
      rw [kaehlerResidueTermKFam_power_differential Rfam hres hf n v, if_neg hn]
      rfl
    rw [heq]
    exact finsum_zero

end
end Dubon2026.SourceCurve
