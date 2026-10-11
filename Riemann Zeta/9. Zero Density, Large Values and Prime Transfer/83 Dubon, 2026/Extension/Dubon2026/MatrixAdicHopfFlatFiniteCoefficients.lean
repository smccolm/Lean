import Dubon2026.MatrixAdicHopfFlatCondition
import Dubon2026.FiniteLocalCoefficientTopology

/-! # The full adic condition over actual finite local coefficients -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K ι A : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [IsLocalRing A]

/-- A genuine model of the original representation supplies a model at every actual positive maximal-adic level by its original surjective coefficient reduction. -/
theorem matrixAdicHopfFlat_of_model
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    MatrixAdicHopfFlat R F K ρ := by
  letI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  letI : Module.Flat R K := Module.Flat.trans R F K
  intro n _hn
  exact matrixCoefficientHopfModel_of_surjective_exists
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) Ideal.Quotient.mk_surjective ρ m

/-- At an actual positive nilpotence level the original quotient map is injective, so a model of that original reduction gives a model of the entire original representation. -/
theorem matrixHopfModel_of_adic_nilpotent
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (n : ℕ) (hn : 0 < n) (hz : IsLocalRing.maximalIdeal A ^ n = ⊥)
    (hρ : MatrixAdicHopfFlat R F K ρ) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) := by
  obtain ⟨m⟩ := hρ n hn
  have hinj : Function.Injective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) := by
    intro a b hab
    have hmem := Ideal.Quotient.eq.mp hab
    rw [hz, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  exact matrixCoefficientHopfModel_of_injective_exists _ hinj ρ m

/-- For the original finite local coefficient ring, the complete all-positive-level condition is equivalent to existence of a genuine model of the original representation. Nilpotence is derived from the actual finite local ring. -/
theorem matrixAdicHopfFlat_finite_iff [Finite A]
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
        (matrixUnderlyingGroupAction ρ)) := by
  constructor
  · intro hρ
    obtain ⟨n, hn⟩ := finiteLocalCoefficient_maximal_nilpotent A
    apply matrixHopfModel_of_adic_nilpotent ρ (n + 1) (Nat.zero_lt_succ n) _ hρ
    rw [pow_succ, hn, Ideal.bot_mul]
  · rintro ⟨m⟩
    exact matrixAdicHopfFlat_of_model ρ m

end
end Dubon2026
