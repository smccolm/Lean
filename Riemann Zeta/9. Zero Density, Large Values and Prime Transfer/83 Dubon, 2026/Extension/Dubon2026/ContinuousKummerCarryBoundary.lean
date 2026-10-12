import Dubon2026.ContinuousRootCharacterCup
import Dubon2026.RepresentationCarryCocycle
import Dubon2026.FiniteGaloisUnitNormRange

/-! # The actual coboundary comparing Kummer cups and character carries

This retains the original continuous cochain witness and the sign in the local
cup/norm comparison. The local pairing is not declared perfect here.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))

/-- The actual continuous carry cocycle of an original finite character and
original base unit, in the original absolute Galois unit coefficients. -/
def continuousGaloisCharacterCarryCocycle (a : Kˣ) :
    continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K Ω) := by
  let f : Multiplicative (ZMod n) × Multiplicative (ZMod n) → Rep.ofAlgebraAutOnUnits K Ω :=
    fun z => zmodAdditionCarry z.1.toAdd z.2.toAdd • galoisUnitsBaseCoefficient a
  exact ⟨representationCarryCocycle (Rep.ofAlgebraAutOnUnits K Ω) χ.toMonoidHom
    (galoisUnitsBaseCoefficient a) (galoisUnitsBaseCoefficient_fixed a),
    (show Continuous f from continuous_of_discreteTopology).comp
      ((χ.continuous.comp continuous_fst).prodMk (χ.continuous.comp continuous_snd))⟩

/-- The literal original continuous cochain whose boundary relates the radical
cup and carry cocycle: its value at g is the radical to the canonical character exponent. -/
def galoisRadicalCharacterOneCochain (β : Ωˣ) : C(Gal(Ω/K), Rep.ofAlgebraAutOnUnits K Ω) := by
  let u : Rep.ofAlgebraAutOnUnits K Ω := Rep.toAdditive.symm (Additive.ofMul β)
  let f : Multiplicative (ZMod n) → Rep.ofAlgebraAutOnUnits K Ω := fun t => t.toAdd.val • u
  exact ⟨fun g => f (χ g), (show Continuous f from continuous_of_discreteTopology).comp χ.continuous⟩

/-- The exact original continuous boundary is the sum of the included Kummer
cup and original carry cocycle. Consequently their unit-H2 classes have opposite signs. -/
theorem continuousKummer_cup_add_carry_boundary (a : Kˣ) (β : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a) :
    continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
      (galoisRadicalCharacterOneCochain n χ β) =
    continuousCoefficientCocycleTwoMap
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (Rep.ofAlgebraAutOnUnits K Ω)
      (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
      (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
      (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n))
      (continuousGaloisRootCharacterCupCocycle n χ (galoisRootRadicalOneCocycle n a β hβ)) +
        continuousGaloisCharacterCarryCocycle n χ a := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  obtain ⟨g, h⟩ := z
  let u : Rep.ofAlgebraAutOnUnits K Ω := Rep.toAdditive.symm (Additive.ofMul β)
  have hp : n • u = galoisUnitsBaseCoefficient a := hβ
  have hcup :
      (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
        ((continuousGaloisRootCharacterCupCocycle n χ
          (galoisRootRadicalOneCocycle n a β hβ)).val (g, h)) =
      (χ h).toAdd.val • ((Rep.ofAlgebraAutOnUnits K Ω).ρ g u - u) := by
    change ((Additive.toMul (Rep.toAdditive
      ((continuousGaloisRootCharacterCupCocycle n χ
        (galoisRootRadicalOneCocycle n a β hβ)).val (g, h))) : rootsOfUnity n Ω) : Ωˣ) =
          (g • β / β) ^ (χ h).toAdd.val
    rw [continuousGaloisRootCharacterCupCocycle_apply, galoisRootRadicalOneCocycle_ratio]
  have hb := zmodAdditionCarry_balance (χ g).toAdd (χ h).toAdd
  have hχ : (χ (g * h)).toAdd = (χ g).toAdd + (χ h).toAdd := by
    rw [map_mul, toAdd_mul]
  rw [← hχ] at hb
  have hv := congrArg (fun m : ℕ => m • u) hb
  dsimp only at hv
  rw [add_nsmul, add_nsmul, mul_nsmul, hp] at hv
  change (Rep.ofAlgebraAutOnUnits K Ω).ρ g ((χ h).toAdd.val • u) -
      (χ (g * h)).toAdd.val • u + (χ g).toAdd.val • u =
    (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
      ((continuousGaloisRootCharacterCupCocycle n χ
        (galoisRootRadicalOneCocycle n a β hβ)).val (g, h)) +
      zmodAdditionCarry (χ g).toAdd (χ h).toAdd • galoisUnitsBaseCoefficient a
  rw [hcup, map_nsmul, nsmul_sub]
  calc
    _ = (χ h).toAdd.val • (Rep.ofAlgebraAutOnUnits K Ω).ρ g u -
        ((χ (g * h)).toAdd.val • u +
          zmodAdditionCarry (χ g).toAdd (χ h).toAdd • galoisUnitsBaseCoefficient a) +
        ((χ g).toAdd.val • u +
          zmodAdditionCarry (χ g).toAdd (χ h).toAdd • galoisUnitsBaseCoefficient a) := by abel
    _ = _ := by rw [hv]; abel

end
end Dubon2026
