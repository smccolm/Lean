import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord

open AlgebraicCurve ModularCurve Polynomial
theorem ModularCurve.natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N)]
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀))
    (hsum : ∑ v ∈ S, v.ord (jBar N -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar N} : Set ↥(modularFunctionFieldBar N)))
        ↥(modularFunctionFieldBar N))

    (hP1 : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      ∃ φ' : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ]
          LaurentSeries (AlgebraicClosure ℚ),
        φ' (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
          HahnSeries.single (((w.ord (jBar N - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar N) j₀)).toNat : ℤ)) 1 ∧
        ∀ x, (φ' x).order = w.ord x)

    :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) →
      Nat.card {ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ) //
        ψ (jBar N) = HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ) ∧
        ∃ g : ℚ, 0 < g ∧ ∀ x, (w.ord x : ℚ) * g = (ψ x).order} =
      (w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_normalized_algHom_hahnSeries_jBar_sub_eq_toNat_ord.solution
