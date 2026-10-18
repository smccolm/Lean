import Dubon2026.ArithmeticSourceClassSaturationStage
import Dubon2026.ArithmeticSourceClassColimitInjection

/-! Prime saturation of the actual S-place class image in the fixed
arithmetic union. Finite-stage Kummer correction is applied after literal
direct-limit equality detection. This is the lifting condition for the
free-cover extension in DUB-17's reverse-localization construction. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)

include hqa in
/-- If a coefficient-prime multiple of a full class lies in the original
S-place class image, the class itself has an original S-place preimage. -/
theorem arithmeticSourceClassColimit_prime_saturated
    (x : arithmeticClassesModOutsideColimitRep K Ω a ha)
    (s : arithmeticSPlaceClassColimitRep K Ω a ha)
    (hx : q • x = (arithmeticSourceClassColimitComparison K Ω a ha).hom s) :
    ∃ z : arithmeticSPlaceClassColimitRep K Ω a ha,
      (arithmeticSourceClassColimitComparison K Ω a ha).hom z = x := by
  letI : DirectedSystem (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticClassesModOutsideDirectedSystem K Ω a ha
  obtain ⟨E, x, rfl⟩ := Module.DirectLimit.exists_of x
  obtain ⟨F, s, rfl⟩ := Module.DirectLimit.exists_of s
  let P := E ⊔ F
  have hEP : E ≤ P := le_sup_left
  have hFP : F ≤ P := le_sup_right
  let xP := arithmeticClassesModOutsideTransitionMap K Ω a ha E P hEP x
  let sP := arithmeticSPlaceClassTransitionMap K Ω a ha F P hFP s
  let ofC := Module.DirectLimit.of ℤ _
    (fun N => arithmeticClassesModOutsideStageRep K Ω a ha N)
    (arithmeticClassesModOutsideTransitionMap K Ω a ha)
  have hxx : ofC P xP = ofC E x := Module.DirectLimit.of_f (hij := hEP)
  have hs : ofC P ((arithmeticSourceClassStageComparison K Ω a ha P).hom sP) =
      (arithmeticSourceClassColimitComparison K Ω a ha).hom
        (Module.DirectLimit.of ℤ _ (fun N => ArithmeticSPlaceClassFiniteStageRep K Ω a ha N)
          (arithmeticSPlaceClassTransitionMap K Ω a ha) F s) := by
    refine Eq.trans ?_ (arithmeticSourceClassColimitComparison_of K Ω a ha F s).symm
    change ofC P ((arithmeticSourceClassStageComparison K Ω a ha P).hom
      (arithmeticSPlaceClassTransitionMap K Ω a ha F P hFP s)) =
        ofC F ((arithmeticSourceClassStageComparison K Ω a ha F).hom s)
    rw [← arithmeticSourceClassStageComparison_natural]
    exact Module.DirectLimit.of_f (hij := hFP)
  have he : ofC P (q • xP) =
      ofC P ((arithmeticSourceClassStageComparison K Ω a ha P).hom sP) := by
    rw [map_nsmul, hxx, hs]
    exact hx
  obtain ⟨M, hPM, hM⟩ := Module.DirectLimit.exists_eq_of_of_eq he
  let xM := arithmeticClassesModOutsideTransitionMap K Ω a ha P M hPM xP
  let sM := arithmeticSPlaceClassTransitionMap K Ω a ha P M hPM sP
  have hm : q • xM = (arithmeticSourceClassStageComparison K Ω a ha M).hom sM := by
    exact ((map_nsmul (arithmeticClassesModOutsideTransitionMap K Ω a ha P M hPM) q xP).symm.trans hM).trans
      (arithmeticSourceClassStageComparison_natural K Ω a ha P M hPM sP)
  obtain ⟨N, hMN, z, hz⟩ := arithmeticSourceClassPower_exists_source_stage K Ω a ha q hqa M xM sM hm
  refine ⟨(coefficientRepresentationColimitOf _
    (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) N).hom z, ?_⟩
  rw [arithmeticSourceClassColimitComparison_of K Ω a ha N z, hz]
  change ofC N (arithmeticClassesModOutsideTransitionMap K Ω a ha M N hMN xM) = ofC E x
  exact (Module.DirectLimit.of_f (hij := hMN)).trans
    ((Module.DirectLimit.of_f (hij := hPM)).trans hxx)

end
end Dubon2026
