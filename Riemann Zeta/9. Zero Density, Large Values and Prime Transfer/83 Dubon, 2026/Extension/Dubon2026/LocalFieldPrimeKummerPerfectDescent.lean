import Dubon2026.LocalFieldPrimeKummerDescent
import Dubon2026.LocalFieldPrimeKummerPerfect

/-! # The original prime-field Kummer pairing is perfect without base roots

Cyclotomic descent discharges the primitive-root hypothesis. The conclusion
still concerns the actual root/character coefficients, not arbitrary modules.
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

/-- The actual invariant-valued Kummer cup distinguishes original root H1
classes whenever the coefficient prime is nonzero in the actual local field. -/
theorem localFieldPrimeKummerPairing_left_injective_of_nonzero (hq : (q : K) ≠ 0) :
    Function.Injective (localFieldPrimeKummerPairing K Ω q) := by
  intro x y h
  apply sub_eq_zero.mp
  apply localFieldPrimeKummer_root_eq_zero_of_cup_zero K Ω q hq
  intro χ
  apply (localFieldPrimeKummerPairing_eq_zero_iff K Ω q (x - y) (Additive.ofMul χ)).mp
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h (Additive.ofMul χ))

/-- The original continuous Kummer cup followed by its normalized local
invariant is a perfect prime-field pairing without a base primitive root.
Both maps to the actual linear duals are bijective, using proved H1 finiteness. -/
theorem localFieldPrimeKummerPairing_isPerfPair_of_nonzero (hq : (q : K) ≠ 0) :
    (localFieldPrimeKummerPairing K Ω q).IsPerfPair := by
  haveI := localFieldKummerH1_finite K Ω q hq
  exact LinearMap.IsPerfPair.of_injective
    (localFieldPrimeKummerPairing_left_injective_of_nonzero K Ω q hq)
    (localFieldPrimeKummerPairing_right_injective K Ω q)

end
end Dubon2026
