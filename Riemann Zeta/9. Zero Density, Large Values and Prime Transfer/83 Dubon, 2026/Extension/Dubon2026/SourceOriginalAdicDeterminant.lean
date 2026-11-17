import Dubon2026.SourceAdicCyclotomicDeterminant
import Dubon2026.SourceAbsoluteCyclicFrobeniusEquality

/-! DUB-17/18 -> actual rank-two realization -> odd original determinant.
The proved original norm-Frobenius comparison identifies any continuous
original adic determinant with the actual cyclotomic weight. The original
trace consumer supplies every hypothesis; no determinant identity is assumed. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable {R : Type} [CommRing R] [IsLocalRing R]
variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]

private theorem monoid_cyclic {G C : Type} [Group G] [CommMonoid C]
    (D : G →* C) (g h : G) : D (g * h) = D (h * g) := by
  rw [map_mul, map_mul, mul_comm]

/-- The original good-prime determinant values uniquely determine the full
adic determinant, including its value at actual complex conjugation. -/
theorem originalAdicDeterminant_eq_cyclotomic
    (D : (Qbar ≃ₐ[ℚ] Qbar) →* R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))
    (hD : @Continuous _ _ _ ⊥ D)
    (hFrob : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
        D (embeddedNormalGaloisRestriction e φ) =
          (q : R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) ^ w) :
    D = sourceAdicCyclotomicDeterminant (R := R) p n w := by
  letI : TopologicalSpace (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := ⊥
  letI : DiscreteTopology (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1)) := ⟨rfl⟩
  have he := absolute_continuous_cyclic_eq_of_norm_frobenius D
    (sourceAdicCyclotomicDeterminant (R := R) p n w) hD
    (sourceAdicCyclotomicDeterminant_continuous p n w)
    (monoid_cyclic D) (monoid_cyclic _) (Q * p).primeFactors
  apply MonoidHom.ext
  intro g
  apply congrFun (he ?_) g
  intro q hq hqS e φ hφ
  have haway : ¬q ∣ Q * p := fun h => hqS (hq.mem_primeFactors' h)
  exact (hFrob q hq haway e φ hφ).trans
    (sourceAdicCyclotomicDeterminant_frobenius p n w q hq
      (fun h => haway (dvd_mul_of_dvd_right h Q)) e φ hφ).symm

end
end Dubon2026
