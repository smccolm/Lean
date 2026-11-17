import Dubon2026.SourceOriginalTorusClassPredicates

/-! The exact original-field bounded detecting-family conclusion needed
for DUB-17's dual-Selmer prime selection. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Actual localization on every original H1 subspace is jointly injective
at a family of regular primes bounded by that subspace's dimension. -/
def HasArithmeticTorusDetectingFamily
    (a : 𝓞 ℚ) (p n level : ℕ)
    {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (A : Rep.{0} K (rationalArithmeticGaloisGroup a))
    [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A]
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a × A => A.ρ z.1 z.2))
    (R : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    (hR : Continuous R) : Prop :=
  ∀ (P : Submodule K (ContinuousRepresentationH1 A hA)) (S : Finset ℕ),
    ∃ Q : Finset Nat.Primes, Q.card ≤ Module.finrank K P ∧
      (∀ q ∈ Q, q.val ∉ S ∧ RationalArithmeticOriginalTorusAuxiliaryPrime a p n level R hR q) ∧
      (∀ x : P, (∀ q ∈ Q,
        rationalArithmeticH1PrimeRestriction a A hA q.val q.property x.val = 0) → x = 0)

end
end Dubon2026
