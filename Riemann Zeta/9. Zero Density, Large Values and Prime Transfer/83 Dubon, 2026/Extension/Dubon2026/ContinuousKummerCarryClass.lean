import Dubon2026.ContinuousKummerCarryBoundary
import Dubon2026.ContinuousKummerH2Torsion

/-! # The actual Kummer cup and cyclic carry have opposite cohomology classes

The original root inclusion is injective by the proved Kummer exactness. Thus
the actual root cup vanishes precisely when the original unit carry class does.
This is the required bridge to the finite cyclic norm pairing.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) (a : Kˣ)

/-- The original root cup, included in actual unit H2, is the negative of the
literal carry class. The sign follows from the proved original continuous boundary. -/
theorem continuousKummerH1Cup_inclusion_eq_neg_carry :
    galoisKummerH2Inclusion (K := K) (Ω := Ω) n
      (continuousGaloisRootCharacterH1Cup n χ (galoisKummerH1Class n a)) =
        -(Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ a) :
          GaloisUnitContinuousH2 (K := K) (Ω := Ω)) := by
  let β := galoisKummerRadical (Ω := Ω) n a
  have hβ := galoisKummerRadical_pow (Ω := Ω) n a
  change galoisKummerH2Inclusion n
    (continuousGaloisRootCharacterH1Cup n χ
      (Submodule.Quotient.mk (galoisRootRadicalOneCocycle n a β hβ))) = _
  rw [continuousGaloisRootCharacterH1Cup_mk]
  change Submodule.Quotient.mk
    (continuousCoefficientCocycleTwoMap
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (Rep.ofAlgebraAutOnUnits K Ω)
      (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
      (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
      (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n))
      (continuousGaloisRootCharacterCupCocycle n χ (galoisRootRadicalOneCocycle n a β hβ))) = _
  rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_add]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨galoisRadicalCharacterOneCochain n χ β,
    continuousKummer_cup_add_carry_boundary n χ a β hβ⟩

/-- Vanishing of the original root cup is equivalent to vanishing of the
actual character carry class in original unit H2. -/
theorem continuousKummerH1Cup_eq_zero_iff_carry :
    continuousGaloisRootCharacterH1Cup n χ (galoisKummerH1Class n a) = 0 ↔
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ a) :
        GaloisUnitContinuousH2 (K := K) (Ω := Ω)) = 0 := by
  have hi := galoisKummerH2Inclusion_injective (K := K) (Ω := Ω) n (NeZero.pos n)
  have he : continuousGaloisRootCharacterH1Cup n χ (galoisKummerH1Class n a) = 0 ↔
      galoisKummerH2Inclusion (K := K) (Ω := Ω) n
        (continuousGaloisRootCharacterH1Cup n χ (galoisKummerH1Class n a)) = 0 := by
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply hi
      rw [h, map_zero]
  rw [he, continuousKummerH1Cup_inclusion_eq_neg_carry, neg_eq_zero]

end
end Dubon2026
