import Dubon2026.ContinuousFiniteBaseGaloisUnitH2
import Dubon2026.ContinuousKummerH2Torsion

/-! # Actual root-of-unity H2 over a finite base field -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] [Finite K] (n : ℕ) (hn : 0 < n)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

include hn in
/-- The genuine Kummer inclusion and finite-base unit H2 computation force
every original continuous root-of-unity H2 class to vanish. The coefficient
object is the original root group with its actual Galois action. -/
theorem continuousFiniteBaseRootH2_eq_zero
    (x : GaloisRootContinuousH2 (K := K) (Ω := Ω) n) : x = 0 := by
  apply galoisKummerH2Inclusion_injective (K := K) (Ω := Ω) n hn
  rw [map_zero]
  exact continuousFiniteBaseGaloisUnitH2_eq_zero
    (galoisKummerH2Inclusion (K := K) (Ω := Ω) n x)

end
end Dubon2026
