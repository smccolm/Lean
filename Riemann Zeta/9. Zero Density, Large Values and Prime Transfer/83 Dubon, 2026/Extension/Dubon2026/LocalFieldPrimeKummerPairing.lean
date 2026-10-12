import Dubon2026.KummerCharacterZModModules
import Dubon2026.LocalFieldKummerCharacterFinite

/-! # The actual local prime-field Kummer pairing with its original invariant -/

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

/-- The literal continuous Kummer cup followed by the original local invariant,
as a bilinear pairing over the actual coefficient prime field. -/
def localFieldPrimeKummerPairing :
    GaloisRootContinuousH1 (K := K) (Ω := Ω) q →ₗ[ZMod q]
      Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod q)) →ₗ[ZMod q] ZMod q := by
  let B := (continuousKummerCharacterPairing (K := K) (Ω := Ω) q).compr₂
    (localFieldRootH2CyclicEquiv K Ω q).toLinearMap
  exact LinearMap.mk₂ (ZMod q) (fun x χ => B x χ)
    (fun x y χ => DFunLike.congr_fun (map_add B x y) χ)
    (fun r x χ => ZMod.map_smul (B.flip χ) r x)
    (fun x χ ψ => map_add (B x) χ ψ)
    (fun r x χ => ZMod.map_smul (B x) r χ)

/-- The prime-field bilinear form keeps the actual cup class and the normalized
original root H2 invariant, rather than an abstract nondegenerate replacement. -/
theorem localFieldPrimeKummerPairing_apply
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) q)
    (χ : Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod q))) :
    localFieldPrimeKummerPairing K Ω q x χ =
      localFieldRootH2CyclicEquiv K Ω q
        (continuousGaloisRootCharacterH1Cup q χ.toMul x) := by
  rfl

/-- Scalarization loses no information about whether the genuine original
Kummer cup class is zero. -/
theorem localFieldPrimeKummerPairing_eq_zero_iff
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) q)
    (χ : Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod q))) :
    localFieldPrimeKummerPairing K Ω q x χ = 0 ↔
      continuousGaloisRootCharacterH1Cup q χ.toMul x = 0 := by
  rw [localFieldPrimeKummerPairing_apply]
  exact (localFieldRootH2CyclicEquiv K Ω q).map_eq_zero_iff

end
end Dubon2026
