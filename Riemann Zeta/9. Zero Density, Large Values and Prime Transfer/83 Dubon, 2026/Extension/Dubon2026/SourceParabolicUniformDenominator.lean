import Dubon2026.SourceParabolicFiniteCuspWitnesses
import Dubon2026.SourceParabolicWitnessDenominators
import Dubon2026.SourceBinaryParabolicChange

/-! DUB17/18 -> original all-weight association -> original integral
parabolic Hecke character. The existing uniform rational-cocycle
denominator and finite original cusp quotient give one integer multiple
whose cocycle and all parabolic witnesses are integral. The premise is
the whole-cusp-stabilizer coboundary statement already available for
the original period cocycle, to be retained under rational projection. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup groupCohomology SourceManin

theorem sourceRationalBinaryCocycle_parabolic_integerMultiple
    (Q w : ℕ) [NeZero Q]
    (c : cocycles₁ (sourceBinaryCoefficientRep ℚ Q w))
    (hc : ∀ β : OnePoint ℚ, ∃ v : sourceBinaryCoefficientRep ℚ Q w,
      ∀ γ : Gamma0 Q, mapGL ℚ γ.val • β = β →
        c γ = (sourceBinaryCoefficientRep ℚ Q w).ρ γ v - v) :
    ∃ (D : ℤ) (z : cocycles₁ (sourceBinaryCoefficientRep ℤ Q w)),
      D ≠ 0 ∧ sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w z = (D : ℚ) • c ∧
      z ∈ sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q w) := by
  classical
  obtain ⟨d, z₀, hd, hz₀⟩ := sourceRationalBinaryCocycle_integerMultiple Q w c
  letI : Fintype (CuspSpace Q) := Fintype.ofFinite _
  choose v hv using fun q : CuspSpace Q => hc q.out
  obtain ⟨e, he, hfamily⟩ := sourceParabolicWitness_family_integerMultiple w
    (Finset.univ : Finset (CuspSpace Q)) (fun q => (d : ℚ) • v q)
  choose b hb using fun q : CuspSpace Q => hfamily q (Finset.mem_univ q)
  let z : cocycles₁ (sourceBinaryCoefficientRep ℤ Q w) := e • z₀
  have hz : sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w z = ((e * d : ℤ) : ℚ) • c := by
    simp only [z, map_smulₛₗ, hz₀, smul_smul, Int.cast_mul, Int.coe_castRingHom]
  refine ⟨e * d, z, mul_ne_zero he hd, hz, ?_⟩
  apply sourceParabolicCocycles_of_cusp_orbit_witnesses Q (sourceBinaryCoefficientRep ℤ Q w) z
  intro q
  refine ⟨b q, ?_⟩
  intro γ hγ
  apply homogeneousCoefficientMap_injective w (Int.castRingHom ℚ) Int.cast_injective
  change (sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w z) γ = _
  rw [hz]
  change ((e * d : ℤ) : ℚ) • c γ = _
  rw [map_sub, sourceBinaryCoefficientMap_equivariant, hb q, hv q γ hγ]
  simp only [Int.cast_mul, mul_smul, smul_sub, map_smul]

end
end Dubon2026
