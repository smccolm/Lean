import Dubon2026.SourceCurveUnramifiedChart
import Mathlib.RingTheory.DedekindDomain.Different

/-! DUB-17/18 -> canonical-divisor finite support. Away from the different
ideal, pinned unramifiedness and the actual local coordinate comparison make
the differential order zero. A single nonzero element of the different ideal
reduces the exceptional set to the already proved finite prime-factor support.
No general ramification-fiber or place-classification machinery is needed.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open Polynomial IsDedekindDomain KaehlerDifferential
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable [Algebra K R] [Algebra K[X] R] [IsScalarTower K K[X] R]
variable [Algebra R F] [IsFractionRing R F] [IsScalarTower K R F]
variable [Module.IsTorsionFree K[X] R] [Module.Finite K[X] R]
variable [Algebra.IsSeparable (FractionRing K[X]) (FractionRing R)]

theorem finite_differential_support_on_chart
    [∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
    [∀ v : Place K F, Algebra.IsSeparable K v.ResidueField]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    {v : Place K F | (∀ r : R, algebraMap R F r ∈ v.toValuationSubring) ∧
      v.ordDifferential (D K F (algebraMap R F (algebraMap K[X] R X))) ≠ 0}.Finite := by
  have hdiff : differentIdeal K[X] R ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdiff
  refine (finite_setOf_forall_mem_and_ord_pos (K := K) (F := F) hr0).subset ?_
  intro v hv
  have hdvd : center R v hv.1 ∣ differentIdeal K[X] R := by
    by_contra h
    exact hv.2 (v.ordDifferential_coordinate_eq_zero_of_unramified hv.1
      (not_dvd_differentIdeal_iff.mp h))
  exact ⟨hv.1, (mem_center_iff_ord_pos v hv.1 hr0).mp (Ideal.le_of_dvd hdvd hr)⟩

end
end Dubon2026.SourceCurve.Place
