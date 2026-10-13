import Dubon2026.SupportedFiniteCoordinateFactors
import Dubon2026.NumberFieldSupportedIdeleExact
import Dubon2026.ValuationSubringPowerSaturation

/-! # The original S-unit map into selected local unit power quotients

The already proved supported-idele coordinate equivalences give the actual
integer unit at each place outside S. Composing with the actual n-th-power
quotients defines the selected local-unit map. Power saturation identifies
its kernel with exactly the original completion-field power conditions used
by Kummer coordinate localization. Its image cardinality is the next
required input to DUB-17's principal S-union-T localization argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- An original S-unit at an actual prime outside S, valued in the original
integer-unit group using the existing supported-idele coordinates. -/
def originalSUnitLocalIntegerMap (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    (S : Set (HeightOneSpectrum (𝓞 K))).unit K →* (v.adicCompletionIntegers K)ˣ where
  toFun x := (numberFieldSupportedFiniteFactorEquiv K S
    (numberFieldSupportedIdeleCoordinateEquiv K S
      (numberFieldSupportedPrincipalIdele K S x)).2).2 ⟨v, hv⟩
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    exact map_one (algebraMap K (v.adicCompletion K))
  map_mul' x y := by
    apply Units.ext
    apply Subtype.ext
    exact map_mul (algebraMap K (v.adicCompletion K)) (x.val : K) (y.val : K)

/-- The local integer-unit map retains exactly the original field embedding
of the original S-unit. -/
theorem originalSUnitLocalIntegerMap_toField (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom
      (originalSUnitLocalIntegerMap K S v hv x) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x.val := by
  apply Units.ext
  rfl

/-- The actual original S-unit map to the product of selected local
integer-unit power quotients. -/
def originalSUnitLocalPowerMap (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) :
    (S : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      ∀ v : T, (v.val.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom n : (v.val.adicCompletionIntegers K)ˣ →*
          (v.val.adicCompletionIntegers K)ˣ).range :=
  Pi.monoidHom fun v => (QuotientGroup.mk' _).comp
    (originalSUnitLocalIntegerMap K S v.val
      (fun h => (Finset.disjoint_left.mp hST) h v.property))

/-- Its literal kernel is the original completion-field power condition at
every selected prime; no integer/field comparison hypothesis remains. -/
theorem originalSUnitLocalPowerMap_mem_ker_iff
    (n : ℕ) (hn : n ≠ 0) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) (x : (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    x ∈ (originalSUnitLocalPowerMap K n S T hST).ker ↔
      ∀ v : T, Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom x.val ∈
        (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range := by
  change (fun v : T => QuotientGroup.mk' _
    (originalSUnitLocalIntegerMap K S v.val _ x)) = 1 ↔ _
  rw [funext_iff]
  apply forall_congr'
  intro v
  change ((originalSUnitLocalIntegerMap K S v.val _ x : (v.val.adicCompletionIntegers K)ˣ) :
    (v.val.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom n).range) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff,
    valuationSubring_unit_mem_power_range_iff _ n hn,
    originalSUnitLocalIntegerMap_toField]

end
end Dubon2026
