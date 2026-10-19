import Dubon2026.AuxiliaryConvergingParameterAction
import Dubon2026.AuxiliaryFixedPowerSeriesComparison

/-! The coefficient action and its quantitative kernel convergence
are constructed for the exact character generators and index already
returned by the actual arithmetic comparison. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped MvPowerSeries.WithPiTopology

/-- The original comparison constructs its actual auxiliary algebra
action with all kernel bounds below the selected congruence level. -/
def auxiliaryComparisonConvergingParameterAction
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {R A ι m G η : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing A] [Algebra O A] [Fintype ι] [DecidableEq ι] [Fintype η]
    [Fintype m] [DecidableEq m]
    (Q : Finset Nat.Primes) (q level : ℕ) [Fact q.Prime] [CharP (ResidueField O) q]
    (τ : G → GeneralLinearGroup m R) (τ₀ : G → GeneralLinearGroup m A)
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level]) :
    let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    {f : MvPowerSeries η O →ₐ[O] MonoidAlgebra O D //
      (∀ j, f (MvPowerSeries.X j) = MonoidAlgebra.of O D
        (Pi.mulSingle (d.index j).1 (Pi.mulSingle (d.index j).2
          (d.comparison.parameters.generators (d.index j).1))) - 1) ∧
      IsLocalHom f.toRingHom ∧ Continuous f ∧
      ∀ n ≤ level, RingHom.ker f.toRingHom ≤ maximalIdeal (MvPowerSeries η O) ^ n} :=
  let h := auxiliaryGroupAlgebra_exists_converging_parameterMap O Q q level d.index hmod
    d.comparison.parameters.generators d.comparison.parameters.generates
  ⟨Classical.choose h, Classical.choose_spec h⟩

end
end Dubon2026
