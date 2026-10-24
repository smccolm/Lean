import Dubon2026.SourceCurveUnramifiedDifferentialOrder
import Dubon2026.SourceCurveResidueFiberSum
import Dubon2026.SourceCurveCanonicalDivisor

/-! DUB-17/18 -> Picard torsion injectivity -> unramified Kummer-cover
genus. The actual finite-support canonical divisor is summed over place
restriction fibers. The existing ramification-degree identity and the
proved unramified differential orders give multiplication of canonical
degree by the field degree. No Riemann--Hurwitz formula is assumed. -/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

theorem divisor_degree_eq_finsum_of_rational_residues
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (D : Divisor K F) : Divisor.degree D = ∑ᶠ v, D v := by
  rw [Divisor.degree_eq_finsum]
  apply finsum_congr
  intro v
  have hd : Module.finrank K v.ResidueField = 1 :=
    (AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) (hres v)).toLinearEquiv.finrank_eq.symm.trans
      (Module.finrank_self K)
  rw [hd, Nat.cast_one, mul_one]

variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero K]
  [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := E)]
  [Nontrivial Ω[F⁄K]] [Nontrivial Ω[E⁄K]]
  [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K E, w.DCoordGenerates]
  [∀ w : Place K E, Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
  [∀ w : Place K E, Algebra.IsSeparable K w.ResidueField]

theorem canonical_degree_map_of_unramified
    (hbase : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (he : ∀ w : Place K E, w.ramificationIndex (F := F) = 1)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (hωE : KaehlerDifferential.map K K F E ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hωE) =
      (Module.finrank F E : ℤ) * Divisor.degree (canonicalDivisorOf hω) := by
  have hf : (Function.support (fun w : Place K E => canonicalDivisorOf hωE w)).Finite :=
    (canonicalDivisorOf hωE).hasFiniteSupport
  rw [divisor_degree_eq_finsum_of_rational_residues htop,
    divisor_degree_eq_finsum_of_rational_residues hbase,
    finsum_eq_fiber_finsum (fun w : Place K E => w.restrict F) _ hf, mul_finsum]
  apply finsum_congr
  intro v
  calc
    _ = ∑ᶠ w : {w : Place K E // w.restrict F = v},
        w.1.ord (algebraMap F E v.uniformizer) * canonicalDivisorOf hω v := by
      apply finsum_congr
      intro w
      have hu : w.1.ord (algebraMap F E v.uniformizer) = 1 := by
        have h := w.1.ramificationIndex_cast (F := F)
        rw [he, Nat.cast_one, w.2] at h
        exact h.symm
      rw [hu, one_mul, canonicalDivisorOf_apply, canonicalDivisorOf_apply,
        w.1.ordDifferential_map_of_ramificationIndex_one (he w.1) hω, w.2]
    _ = (∑ᶠ w : {w : Place K E // w.restrict F = v},
        w.1.ord (algebraMap F E v.uniformizer)) * canonicalDivisorOf hω v :=
      (finsum_mul _ _).symm
    _ = _ := by rw [v.sum_fiber_ramification (hbase v) htop]

end
end Dubon2026.SourceCurve
