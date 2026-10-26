import Dubon2026.SourceOriginalArithmeticResidual
import Dubon2026.SourceArithmeticSupportInflationValues

/-! DUB-17/18 -> close the actual parabolic branch -> the prescribed
original arithmetic support. Inflate the already constructed primitive
representation along the existing support restriction. The proved
local conjugacy preserves the exact polynomial, trace, determinant
and inertia identities at every original good prime. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open Matrix Polynomial
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (N M ell : ℕ) [NeZero M] (hell : ell.Prime) [Fact ell.Prime]
variable (K : Type) [Field K] [TopologicalSpace K] [DiscreteTopology K] [CharP K ell]
variable (hMN : M ∣ N) (f : PrimitiveCuspForm M 2) (φ : integralClosure ℤ ℂ →+* K)

include hell hMN in
theorem originalPrimitive_divisor_arithmetic_residual_realization :
    ∃ ρ : rationalArithmeticGaloisGroup (N * ell : ℕ) →* GeneralLinearGroup (Fin 2) K,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ N * ell →
        (∀ g ∈ rationalPrimeNormInertia q hq,
          ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g) = 1) ∧
        ∀ g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq),
          (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing (rationalPrimeLocalClosure q hq)),
            g • z = z ^ q) →
          let a : integralClosure ℤ ℂ := ⟨cuspCoefficients f.toCuspForm q,
            sourcePrimitiveCoefficient_isIntegral f (by norm_num) q⟩
          (ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.charpoly =
              X ^ 2 - C (φ a) * X + C (q : K) ∧
            (ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.trace = φ a ∧
            (ρ (rationalPrimeArithmeticRestriction (N * ell : ℕ) q hq g)).val.det = (q : K) := by
  have hsrc := originalPrimitive_prescribed_arithmetic_residual_realization M ell hell K f φ
  rcases hsrc with ⟨ρ, hc, _, hlocal⟩
  have hd : M * ell ∣ N * ell := Nat.mul_dvd_mul hMN dvd_rfl
  have hab : ((M * ell : ℕ) : 𝓞 ℚ) ∣ ((N * ell : ℕ) : 𝓞 ℚ) :=
    map_dvd (Nat.castRingHom (𝓞 ℚ)) hd
  let π := rationalArithmeticSupportRestriction (M * ell : ℕ) (N * ell : ℕ) hab
  let η := ρ.comp π.toMonoidHom
  have hη : Continuous η := hc.comp π.continuous
  have hcomp : ∀ g, ρ (rationalArithmeticSupportRestriction
      (M * ell : ℕ) (N * ell : ℕ) hab g) = η g := fun _ => rfl
  refine ⟨η, hη, (isCompact_range hη).finite_of_discrete, ?_⟩
  intro q hq hqN
  have hqM : ¬q ∣ M * ell := fun h => hqN (h.trans hd)
  constructor
  · intro g hg
    exact sourceArithmeticSupport_local_inflate_eq_one (M * ell : ℕ) (N * ell : ℕ) hab
      ρ η hcomp q hq g ((hlocal q hq hqM).1 g hg)
  · intro g hg
    have hv := (hlocal q hq hqM).2 g hg
    rcases hv with ⟨hpoly, htrace, hdet⟩
    exact ⟨(sourceArithmeticSupport_local_charpoly (M * ell : ℕ) (N * ell : ℕ) hab
        ρ η hcomp q hq g).symm.trans hpoly,
      (sourceArithmeticSupport_local_trace (M * ell : ℕ) (N * ell : ℕ) hab
        ρ η hcomp q hq g).symm.trans htrace,
      (sourceArithmeticSupport_local_det (M * ell : ℕ) (N * ell : ℕ) hab
        ρ η hcomp q hq g).symm.trans hdet⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
