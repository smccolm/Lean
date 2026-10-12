import Dubon2026.LocalFieldPrimeKummerPairing
import Dubon2026.LocalFieldKummerRootNondegeneracy
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # The actual prime-field Kummer pairing is perfect over a base primitive root

Both dual maps are proved bijective using the actual cup, its original local
invariant, the proved two annihilator statements and proved H1 finiteness.
Descent without base roots and arbitrary finite coefficient modules remain open.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] galoisFiniteCharacterZModModule galoisRootH1ZModModule

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The actual prime-field cup functional distinguishes original root H1
classes when the primitive root is present in the original base field. -/
theorem localFieldPrimeKummerPairing_left_injective
    {ζ : K} (hζ : IsPrimitiveRoot ζ q) :
    Function.Injective (localFieldPrimeKummerPairing K Ω q) := by
  intro x y h
  apply sub_eq_zero.mp
  apply localFieldKummer_root_eq_zero_of_cup_zero K Ω hζ
  intro χ
  apply (localFieldPrimeKummerPairing_eq_zero_iff K Ω q (x - y) (Additive.ofMul χ)).mp
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h (Additive.ofMul χ))

/-- The actual invariant-valued prime-field cup distinguishes original
continuous finite characters, without any base primitive-root hypothesis. -/
theorem localFieldPrimeKummerPairing_right_injective :
    Function.Injective (localFieldPrimeKummerPairing K Ω q).flip := by
  intro χ ψ h
  apply localFieldKummerCharacterPairing_right_injective K Ω q
  apply LinearMap.ext
  intro x
  apply (localFieldRootH2CyclicEquiv K Ω q).injective
  exact DFunLike.congr_fun h x

/-- Over a base primitive root and with q nonzero in the actual local field,
the original Kummer cup and normalized local invariant form a perfect pairing:
both maps to the actual prime-field linear duals are bijective. -/
theorem localFieldPrimeKummerPairing_isPerfPair
    {ζ : K} (hζ : IsPrimitiveRoot ζ q) (hq : (q : K) ≠ 0) :
    (localFieldPrimeKummerPairing K Ω q).IsPerfPair := by
  haveI := localFieldKummerH1_finite K Ω q hq
  exact LinearMap.IsPerfPair.of_injective
    (localFieldPrimeKummerPairing_left_injective K Ω q hζ)
    (localFieldPrimeKummerPairing_right_injective K Ω q)

end
end Dubon2026
