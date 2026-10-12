import Dubon2026.CoinducedCosetReconstruction
import Dubon2026.CosetTraceDifferential

/-! # Original Shapiro cochains from the proved coset transition formulas

Each original term is reconstructed as an actual coinduced coefficient. These
maps supply the low-degree continuous Shapiro comparison in DUB-17's local
duality dependency, retaining the original object and its action.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The degree-zero original coefficient lift in genuine coinduced coordinates. -/
def coinducedShapiroZero : A →ₗ[R] Rep.coind S.subtype (Rep.res S.subtype A) :=
  (coinducedCosetReconstruct A S).comp (LinearMap.pi (fun q => A.ρ q.out))

/-- The degree-one lift uses the same original transition term at the inverse
translate of the output coset, before reconstructing the original coefficient. -/
def coinducedShapiroOne :
    (S → A) →ₗ[R] (G → Rep.coind S.subtype (Rep.res S.subtype A)) :=
  LinearMap.pi (fun g => (coinducedCosetReconstruct A S).comp
    (LinearMap.pi (fun q => (A.ρ (g • g⁻¹ • q).out).comp
      (LinearMap.proj (cosetTransition S g (g⁻¹ • q))))))

/-- The degree-two lift uses both original transition coordinates in the same
actual coinduced coefficient space. -/
def coinducedShapiroTwo :
    (S × S → A) →ₗ[R] (G × G → Rep.coind S.subtype (Rep.res S.subtype A)) :=
  LinearMap.pi (fun z => (coinducedCosetReconstruct A S).comp
    (LinearMap.pi (fun q => (A.ρ (z.1 • z.2 • (z.1 * z.2)⁻¹ • q).out).comp
      (LinearMap.proj (cosetTransition S z.1 (z.2 • (z.1 * z.2)⁻¹ • q),
        cosetTransition S z.2 ((z.1 * z.2)⁻¹ • q))))))

/-- The original degree-zero lift has its literal chosen coset values. -/
theorem coinducedShapiroZero_values (a : A) :
    coinducedCosetValues A S (coinducedShapiroZero A S a) = fun q => A.ρ q.out a :=
  coinducedCosetValues_reconstruct A S (fun q => A.ρ q.out a)

/-- The actual degree-one coinduced values are exactly the original terms. -/
theorem coinducedShapiroOne_values (f : S → A) (g : G) :
    coinducedCosetValues A S (coinducedShapiroOne A S f g) =
      fun q => cosetTraceOneTerm A S f g (g⁻¹ • q) :=
  coinducedCosetValues_reconstruct A S (fun q => cosetTraceOneTerm A S f g (g⁻¹ • q))

/-- The actual degree-two coinduced values are exactly the original terms. -/
theorem coinducedShapiroTwo_values (c : S × S → A) (g h : G) :
    coinducedCosetValues A S (coinducedShapiroTwo A S c (g, h)) =
      fun q => cosetTraceTwoTerm A S c g h ((g * h)⁻¹ • q) :=
  coinducedCosetValues_reconstruct A S (fun q => cosetTraceTwoTerm A S c g h ((g * h)⁻¹ • q))

end
end Dubon2026
