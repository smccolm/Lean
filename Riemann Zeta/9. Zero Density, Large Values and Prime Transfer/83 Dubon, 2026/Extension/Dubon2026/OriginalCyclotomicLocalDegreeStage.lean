import Dubon2026.CyclotomicPrimePowerLocalDegrees
import Dubon2026.OriginalUnramifiedCyclotomicPowerRoots
import Dubon2026.OriginalCyclotomicPrimeStage

/-! # A constructed cyclic cyclotomic stage with prescribed local degree divisibility

For the actual odd auxiliary-prime branch in DUB-17, the stage is adjoined
from a primitive root inside the original ambient field. It lies in the
original unramified union for the fixed exceptional integer and has the
required degree divisibility at every prime in a given finite support.
No root, cyclicity, conductor exponent or local-degree witness is assumed.
This constructs the extension needed for local-invariant killing; the
cohomological base-change and zero-sum conclusions still need assembly.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- A cyclic cyclotomic stage inside the original unramified union has auxiliary-prime-divisible original local degrees on any prescribed finite prime support. -/
theorem originalCyclotomic_exists_localDegree_stage
    (a : 𝓞 ℚ) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (k : ℕ) (F : FiniteGaloisIntermediateField ℚ Ω),
      letI : NumberField F := NumberField.of_module_finite ℚ F
      1 ≤ k ∧ IsCyclotomicExtension {q ^ (k + 1)} ℚ F ∧ IsCyclic Gal(F/ℚ) ∧
      F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
      ∀ (p : ℕ), p ∈ S → ∀ (w : HeightOneSpectrum (𝓞 F)),
        w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) →
        let v := originalFinitePrimeBelow ℚ F w
        letI := originalFinitePrimeBelow_liesOver ℚ F w
        letI : Algebra (v.adicCompletion ℚ) (w.adicCompletion F) :=
          (originalAdicBaseChangeMap ℚ F v w).toAlgebra
        q ∣ Module.finrank (v.adicCompletion ℚ) (w.adicCompletion F) := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  let r := S.sup fun p => p ^ (q - 1) - 1
  let k := r + 1
  have hk : 1 ≤ k := by omega
  have hlarge (p : ℕ) (hp : p ∈ S) : p ^ (q - 1) - 1 < q ^ (k + 1) := by
    have hr : r < q ^ r := Nat.lt_pow_self hq.one_lt
    exact lt_of_le_of_lt (Finset.le_sup (f := fun p => p ^ (q - 1) - 1) hp)
      (hr.trans_le (Nat.pow_le_pow_right hq.pos (by omega)))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ (k + 1))
  let F := originalPrimitiveRootStage ℚ Ω hζ
  letI : NumberField F := NumberField.of_module_finite ℚ F
  have hcycOriginal : @IsCyclotomicExtension {q ^ (k + 1)} ℚ F _ _ F.algebra' :=
    originalPrimitiveRootStage_isCyclotomic ℚ Ω hζ
  have hrat : (F.algebra' : Algebra ℚ F) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hcyc : IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hrat ▸ hcycOriginal
  letI := hcyc
  refine ⟨k, F, hk, hcyc, ?_, ?_, ?_⟩
  · exact cyclotomicPrimePower_galois_isCyclic q k F hq2
  · change IntermediateField.adjoin ℚ ({ζ} : Set Ω) ≤ _
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact originalQUnramifiedUnion_mem_of_powerRoot a q (k + 1) hqa ζ hζ
  · intro p hp w hw
    letI : Fact p.Prime := ⟨hS p hp⟩
    letI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hw
    exact cyclotomicPrimePower_original_completion_degree_dvd q k F hk p (fun _ => hlarge p hp) w

end
end Dubon2026
