import Dubon2026.LocalFieldUnitPowerFinite
import Dubon2026.ContinuousKummerH1Map

/-! # Finiteness of actual local continuous Kummer H1

The actual Kummer equivalence transports the proved original unit-power quotient
finiteness. No H1 dimension, cardinality or duality formula is assumed.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Original root-valued continuous H1 is finite when the actual field
characteristic does not divide n, by the genuine Kummer quotient comparison. -/
theorem localFieldKummerH1_finite (hn : (n : K) ≠ 0) :
    Finite (GaloisRootContinuousH1 (K := K) (Ω := Ω) n) := by
  haveI : Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :=
    localField_unitPower_quotient_finite K n hn
  exact Finite.of_equiv (Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range))
    (galoisKummerH1Equiv (K := K) (Ω := Ω) n).toEquiv

end
end Dubon2026
