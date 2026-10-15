import Dubon2026.RationalPrimeCyclotomicResidualReduction

/-! # The actual cyclotomic principal character product -/

namespace Dubon2026
noncomputable section

set_option maxHeartbeats 1200000

open IsDedekindDomain HeightOneSpectrum Metric
open scoped ValuativeRel

/-- The ramified local reciprocity character and the real/away-prime character
of the same normalized residual multiply to one in the canonical unit group
of the actual prime-power cyclotomic conductor. -/
theorem rationalPrimeNormalizedResidual_exists_cyclotomic_principal_character
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) (q : ℚˣ) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let N := p ^ (m + 1)
    let r := rationalPrimeNormalizedResidual p hp q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ N,
        (∀ v ∉ S, v.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
                  (Rat.HeightOneSpectrum.prime_natGenerator v) r))) = r.val ∧
        ∃ (a c : ℕ), 0 < a ∧ 0 < c ∧ ¬p ∣ c ∧
          ∃ ha : ¬p ∣ a, ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
            a.Coprime N ∧ d.Coprime N ∧ b.Coprime N ∧ c.Coprime N ∧
            a * b ≡ 1 [MOD N] ∧ c * d ≡ 1 [MOD N] ∧
            let L := rationalPrimeOriginalCyclotomicClosureStage p hp m a u hu ha
            letI : IsCyclic Gal(L/K) :=
              rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 m a u hu ha
            letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
            letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
            let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp m a u hu ha
            let σ := (localFieldFiniteCyclicReciprocity K Ω L
              (Additive.ofMul (rationalPrimeRationalUnit p hp r))).toMul
            letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
            σ ζ = ζ ^ (b * c) ∧
            (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp m a u hu ha).autToPow
                K σ * arithmeticCyclotomicSignedAwayProductUnit N S hS r = 1 := by
  dsimp only
  obtain ⟨S, hS, houtside, hproduct, a, c, ha0, hc0, hc, ha, u, hu,
      b, d, hca, hcd, hcb, hcc, hab, hcdinv, haction, hchar, hunit⟩ :=
    rationalPrimeNormalizedResidual_exists_forwardUnit_identity p hp hp2 m q
  refine ⟨S, hS, houtside, hproduct, a, c, ha0, hc0, hc, ha, u, hu,
    b, d, hca, hcd, hcb, hcc, hab, hcdinv, haction, ?_⟩
  rw [hunit]
  exact hchar

end
end Dubon2026
