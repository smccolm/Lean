import Dubon2026.AlgebraicLocalInertia
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.Integral

/-! The original field embedding sends global integers to actual local
integers and contracts the actual residue kernel to a prime. This is the
next DUB-17 dependency: identify the original local inertia action in a
selected unramified finite factor, before realizing the local deformation
conditions. No unramifiedness or prime-above-p identification is asserted
by the integral embedding construction itself. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Every element integral over the original integers belongs to the
actual nonarchimedean valuation ring. -/
theorem algebraicLocal_mem_of_integral_int
    {L : Type} [NormedField L] [IsUltrametricDist L] {x : L} (hx : IsIntegral ℤ x) :
    x ∈ (NormedField.valuation (K := L)).valuationSubring := by
  exact (Valuation.valuationSubring.integers (NormedField.valuation (K := L))).mem_of_integral
    (hx.tower_top (A := algebraicLocalIntegerRing L))

/-- The same original field embedding restricts to the actual integer rings. -/
def algebraicLocalGlobalIntegerMap
    {F L : Type} [Field F] [NormedField L] [IsUltrametricDist L] (e : F →+* L) :
    𝓞 F →+* algebraicLocalIntegerRing L :=
  (e.comp (algebraMap (𝓞 F) F)).codRestrict
    (NormedField.valuation (K := L)).valuationSubring (fun x =>
      algebraicLocal_mem_of_integral_int (x.property.map e.toIntAlgHom))

/-- The restricted map keeps the literal original field-element image. -/
theorem algebraicLocalGlobalIntegerMap_coe
    {F L : Type} [Field F] [NormedField L] [IsUltrametricDist L]
    (e : F →+* L) (x : 𝓞 F) :
    (algebraicLocalGlobalIntegerMap e x : L) = e (x : F) := rfl

/-- Contract the actual local residue kernel along the original integer embedding. -/
def algebraicLocalGlobalPrime
    {F L : Type} [Field F] [NormedField L] [IsUltrametricDist L] (e : F →+* L) :
    Ideal (𝓞 F) :=
  RingHom.ker ((IsLocalRing.residue (algebraicLocalIntegerRing L)).comp
    (algebraicLocalGlobalIntegerMap e))

/-- The contracted actual residue kernel is a prime ideal. -/
theorem algebraicLocalGlobalPrime_isPrime
    {F L : Type} [Field F] [NormedField L] [IsUltrametricDist L] (e : F →+* L) :
    (algebraicLocalGlobalPrime e).IsPrime := RingHom.ker_isPrime _

attribute [local instance] algebraicLocalIntegerAction

/-- A literal intertwining of the original field actions sends actual
local inertia into inertia at the contracted original global prime. -/
theorem algebraicLocalGlobalPrime_inertia
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Field F] [NumberField F]
    (e : F →+* L) (σ : Gal(F/ℚ)) (δ : Gal(L/K))
    (hδ : δ ∈ algebraicLocalInertia K L)
    (he : ∀ x : F, e (σ x) = δ (e x)) :
    σ ∈ (algebraicLocalGlobalPrime e).inertia Gal(F/ℚ) := by
  intro x
  change IsLocalRing.residue (algebraicLocalIntegerRing L)
    (algebraicLocalGlobalIntegerMap e (σ • x - x)) = 0
  rw [map_sub, map_sub]
  apply sub_eq_zero.mpr
  have he' : algebraicLocalGlobalIntegerMap e (σ • x) =
      δ • algebraicLocalGlobalIntegerMap e x := by
    apply Subtype.ext
    exact he x.val
  rw [he', IsLocalRing.ResidueField.residue_smul]
  exact (algebraicLocalInertia_mem_iff K L δ).mp hδ _

end
end Dubon2026
