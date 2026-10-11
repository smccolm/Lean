import Dubon2026.ContinuousKummerH2Maps
import Dubon2026.ContinuousConnectingH2Exactness
import Dubon2026.ContinuousCoefficientH2MiddleExactness

/-! # Original root-of-unity H2 and the actual torsion in Galois unit H2 -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

include hn in
/-- Actual continuous infinite-extension Hilbert90 kills the source of the
original Kummer connecting map, so the genuine root inclusion on H2 is injective. -/
theorem galoisKummerH2Inclusion_injective :
    Function.Injective (galoisKummerH2Inclusion (K := K) (Ω := Ω) n) := by
  intro x y hxy
  have hz : galoisKummerH2Inclusion (K := K) (Ω := Ω) n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hr := (continuousConnectingH2_mem_range_iff
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω)
    (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerInclusion_injective (K := K) (Ω := Ω) n)
    (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
    (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n))
    (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerPower_surjective (K := K) (Ω := Ω) n hn)
    (Rep.hom_comm_apply (galoisKummerPower (K := K) (Ω := Ω) n))
    (galoisKummerCoefficient_exact (K := K) (Ω := Ω) n)
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) (x - y)).mpr hz
  obtain ⟨z, hzx⟩ := hr
  have hz0 := discreteInfiniteGaloisUnitH1_eq_zero z
  rw [hz0, map_zero] at hzx
  exact sub_eq_zero.mp hzx.symm

include hn in
/-- Actual coefficient-sequence exactness and the proved middle H2 theorem
identify the original inclusion image with the original unit-power H2 kernel. -/
theorem galoisKummerH2_range_eq_ker :
    LinearMap.range (galoisKummerH2Inclusion (K := K) (Ω := Ω) n) =
      LinearMap.ker (galoisKummerH2Power (K := K) (Ω := Ω) n) := by
  exact continuousCoefficientH2_middle_range_eq_ker
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (Rep.ofAlgebraAutOnUnits K Ω) (Rep.ofAlgebraAutOnUnits K Ω)
    (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerInclusion_injective (K := K) (Ω := Ω) n)
    (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
    (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n))
    (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerPower_surjective (K := K) (Ω := Ω) n hn)
    (Rep.hom_comm_apply (galoisKummerPower (K := K) (Ω := Ω) n))
    (galoisKummerCoefficient_exact (K := K) (Ω := Ω) n)
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))

include hn in
/-- The original root H2 image is exactly the actual subgroup killed by n,
using the proved identity for the original coefficient power endomorphism. -/
theorem galoisKummerH2_mem_range_iff_nsmul_zero
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    x ∈ LinearMap.range (galoisKummerH2Inclusion (K := K) (Ω := Ω) n) ↔ n • x = 0 := by
  rw [galoisKummerH2_range_eq_ker n hn]
  change galoisKummerH2Power (K := K) (Ω := Ω) n x = 0 ↔ n • x = 0
  rw [galoisKummerH2Power_eq_nsmul]

/-- The actual root-of-unity continuous H2 is linearly equivalent to the
actual power-kernel subgroup of original continuous Galois unit H2. This does
not assert any local invariant or classification by central simple algebras. -/
def galoisKummerH2KernelEquiv :
    GaloisRootContinuousH2 (K := K) (Ω := Ω) n ≃ₗ[ℤ]
      LinearMap.ker (galoisKummerH2Power (K := K) (Ω := Ω) n) :=
  (LinearEquiv.ofInjective (galoisKummerH2Inclusion (K := K) (Ω := Ω) n)
    (galoisKummerH2Inclusion_injective (K := K) (Ω := Ω) n hn)).trans
      (LinearEquiv.ofEq _ _ (galoisKummerH2_range_eq_ker (K := K) (Ω := Ω) n hn))

/-- The actual Kummer equivalence retains the original coefficient-induced
inclusion as its underlying class map. -/
theorem galoisKummerH2KernelEquiv_apply
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) :
    (galoisKummerH2KernelEquiv (K := K) (Ω := Ω) n hn x).val =
      galoisKummerH2Inclusion (K := K) (Ω := Ω) n x := by
  rfl

end
end Dubon2026
