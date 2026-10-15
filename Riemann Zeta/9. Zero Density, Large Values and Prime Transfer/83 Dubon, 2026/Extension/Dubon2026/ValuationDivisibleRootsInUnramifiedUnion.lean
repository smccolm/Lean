import Dubon2026.OriginalValuationDivisibleKummer
import Dubon2026.LocalizedUnitRootsInUnramifiedUnion
import Dubon2026.OriginalFinitePrimeOrbits

/-! # Actual nonunit Kummer roots in the original arithmetic union

The original primewise q-divisibility of a field element's valuations gives
unramifiedness of its root field at precisely the original exceptional
support. The existing normal-closure and tower comparisons place that root
inside the same arithmetic union. This is needed for the q-primary Hom class
comparison serving DUB-17; no full class principalization is asserted.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain IntermediateField
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- Original primewise q-power valuations imply unramifiedness of the actual generated root field outside the original exceptional integer. -/
theorem originalValuationDivisibleKummer_unramifiedAway
    (a : 𝓞 K) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (u : Kˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), a ∉ v.asIdeal →
      ∃ c : Kˣ, v.valuation K (u : K) = v.valuation K (c : K) ^ q)
    (β : L) (hβ : β ^ q = algebraMap K L (u : K))
    (hgen : IntermediateField.adjoin K {β} = ⊤) :
    ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  intro w hw
  let v := originalFinitePrimeBelow K L w
  letI := originalFinitePrimeBelow_liesOver K L w
  have hva : a ∉ v.asIdeal := hw
  have hqv : (q : 𝓞 K) ∉ v.asIdeal := by
    intro hq
    obtain ⟨d, hd⟩ := hqa
    apply hva
    rw [hd]
    exact v.asIdeal.mul_mem_right d hq
  obtain ⟨c, hc⟩ := hu v hva
  exact originalValuationDivisibleKummer_unramified K L v w q hqv u c hc β hβ hgen

variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

omit [Field L] [NumberField L] [Algebra K L] in
/-- Every original qth root whose base valuations are q-powers away from the same exceptional support lies in the original arithmetic union. -/
theorem originalValuationDivisibleRoot_mem_unramifiedUnion
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (u : Kˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), a ∉ v.asIdeal →
      ∃ c : Kˣ, v.valuation K (u : K) = v.valuation K (c : K) ^ q)
    (β : Ω) (hβ : β ^ q = algebraMap K Ω (u : K)) :
    β ∈ originalUnramifiedGaloisUnion (Ω := Ω) a := by
  let E := IntermediateField.adjoin K {β}
  have hi : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  letI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hi
  letI : NumberField E := NumberField.of_module_finite K E
  let b : E := AdjoinSimple.gen K β
  have hb : b ^ q = algebraMap K E (u : K) := by
    apply E.val.injective
    exact hβ
  have hgen : IntermediateField.adjoin K {b} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K {b}
      (IntermediateField.adjoin.powerBasis hi).adjoin_gen_eq_top
  have hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a :=
    (originalUnramifiedUnion_finite_le_iff a ha E).mpr
      (originalValuationDivisibleKummer_unramifiedAway K E a q hqa u hu b hb hgen)
  exact hE (IntermediateField.subset_adjoin K {β} (Set.mem_singleton β))

omit [Field L] [NumberField L] [Algebra K L] in
/-- Valuation-divisible roots from an original finite arithmetic stage remain in the same base arithmetic union. -/
theorem originalValuationDivisibleFiniteStageRoot_mem_unramifiedUnion
    (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
    (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (u : Eˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), algebraMap (𝓞 K) (𝓞 E) a ∉ v.asIdeal →
      ∃ c : Eˣ, v.valuation E (u : E) = v.valuation E (c : E) ^ q)
    (β : Ω) (hβ : β ^ q = algebraMap E Ω (u : E)) :
    β ∈ originalUnramifiedGaloisUnion (Ω := Ω) a := by
  let aE := algebraMap (𝓞 K) (𝓞 E) a
  have hqE : (q : 𝓞 E) ∣ aE := by
    simpa only [map_natCast] using map_dvd (algebraMap (𝓞 K) (𝓞 E)) hqa
  let F := IntermediateField.adjoin E {β}
  have hi : IsIntegral E β := (Algebra.IsIntegral.isIntegral (R := K) β).tower_top
  letI : FiniteDimensional E F := IntermediateField.adjoin.finiteDimensional hi
  letI : NumberField F := NumberField.of_module_finite E F
  letI : Algebra K F := Algebra.compHom F (algebraMap K E)
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K F := Module.Finite.trans E F
  let b : F := AdjoinSimple.gen E β
  have hb : b ^ q = algebraMap E F (u : E) := by
    apply F.val.injective
    exact hβ
  have hgen : IntermediateField.adjoin E {b} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra E {b}
      (IntermediateField.adjoin.powerBasis hi).adjoin_gen_eq_top
  have hF := numberField_unramified_tower (K := K) (L := E) (M := F) a
    (originalUnramifiedUnion_ambient_finite_ramification a ha E hE)
    (originalValuationDivisibleKummer_unramifiedAway E F aE q hqE u hu b hb hgen)
  letI : IsGalois K (normalClosure K F Ω) := {}
  let N : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K F Ω⟩
  have hN := numberField_normalClosure_unramified (Ω := Ω) a ha hF
  have hbN : β ∈ N.toIntermediateField :=
    (F.val.restrictScalars K).fieldRange_le_normalClosure ⟨b, rfl⟩
  exact originalUnramifiedGaloisStage_le_union a ⟨N, hN⟩ hbN

end
end Dubon2026
