import Dubon2026.SourceBinaryCohomologyChange
import Mathlib.RingTheory.Localization.Integer

/-! Clear denominators of the actual rational binary cocycle.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> integral Hecke character -> spanning by integral cocycles.
Finite generation of the actual Gamma0 group reduces denominator clearing
to finitely many polynomial coefficients.

Adapted to native cocycles and the existing coefficient map from
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top.lean,
section Denominators (Apache-2.0; retained archive LICENSE and NOTICE).
-/

namespace Dubon2026
noncomputable section
open MvPolynomial Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private def integralPolynomial (w : ℕ) (v : homogeneousSubmodule (Fin 2) ℚ w) : Prop :=
  ∃ z : homogeneousSubmodule (Fin 2) ℤ w,
    homogeneousCoefficientMap w (Int.castRingHom ℚ) z = v

private theorem integralPolynomial_zero (w : ℕ) :
    integralPolynomial w 0 := ⟨0, map_zero _⟩

private theorem integralPolynomial_add {w : ℕ}
    {v u : homogeneousSubmodule (Fin 2) ℚ w}
    (hv : integralPolynomial w v) (hu : integralPolynomial w u) :
    integralPolynomial w (v + u) := by
  obtain ⟨z, rfl⟩ := hv
  obtain ⟨t, rfl⟩ := hu
  exact ⟨z + t, map_add _ _ _⟩

private theorem integralPolynomial_neg {w : ℕ}
    {v : homogeneousSubmodule (Fin 2) ℚ w} (hv : integralPolynomial w v) :
    integralPolynomial w (-v) := by
  obtain ⟨z, rfl⟩ := hv
  exact ⟨-z, map_neg _ _⟩

private theorem integralPolynomial_action {Q w : ℕ}
    {v : homogeneousSubmodule (Fin 2) ℚ w} (hv : integralPolynomial w v)
    (g : Gamma0 Q) :
    integralPolynomial w ((sourceBinaryCoefficientRep ℚ Q w).ρ g v) := by
  obtain ⟨z, rfl⟩ := hv
  exact ⟨(sourceBinaryCoefficientRep ℤ Q w).ρ g z,
    sourceBinaryCoefficientMap_equivariant (Int.castRingHom ℚ) Q w g z⟩

private theorem integer_multiple_of_finite {ι : Type} (w : ℕ)
    (s : Finset ι) (v : ι → homogeneousSubmodule (Fin 2) ℚ w) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ i ∈ s, integralPolynomial w ((d : ℚ) • v i) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    (s.biUnion fun i => (v i).val.support.image fun m => (v i).val.coeff m)
  choose! a ha using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i hi => ⟨⟨
    ∑ m ∈ (v i).val.support, monomial m (a ((v i).val.coeff m)), ?_⟩, ?_⟩⟩
  · rw [mem_homogeneousSubmodule]
    refine IsHomogeneous.sum _ _ _ fun m hm => ?_
    have hv := (mem_homogeneousSubmodule w _).mp (v i).property
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact hv (mem_support_iff.mp hm)
  · apply Subtype.ext
    change map (Int.castRingHom ℚ)
      (∑ m ∈ (v i).val.support, monomial m (a ((v i).val.coeff m))) =
        (b.val : ℚ) • (v i).val
    simp only [map_sum, map_monomial]
    conv_rhs => rw [(v i).val.as_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have h := ha _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ hm⟩)
    rw [smul_monomial, eq_intCast]
    rw [eq_intCast] at h
    rw [h, zsmul_eq_mul, smul_eq_mul]

/-- Every actual rational binary cocycle is an integral cocycle after multiplication
by one nonzero integer; the denominator is uniform over the entire original Gamma0 group. -/
theorem sourceRationalBinaryCocycle_integerMultiple (Q w : ℕ) [NeZero Q]
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℚ Q w)) :
    ∃ (d : ℤ) (z : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℤ Q w)),
      d ≠ 0 ∧ sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w z = (d : ℚ) • c := by
  classical
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  obtain ⟨s, hs⟩ := (inferInstance : Group.FG (Gamma0 Q)).out
  obtain ⟨d, hd, hdS⟩ := integer_multiple_of_finite w s (fun g => c g)
  have hall (g : Gamma0 Q) : integralPolynomial w ((d : ℚ) • c g) := by
    have hg : g ∈ Subgroup.closure (s : Set (Gamma0 Q)) := by rw [hs]; trivial
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact hdS g hg
    | one =>
      rw [groupCohomology.cocycles₁_map_one, smul_zero]
      exact integralPolynomial_zero w
    | mul g h _ _ hg hh =>
      rw [(groupCohomology.mem_cocycles₁_iff c).mp c.property, smul_add, ← map_smul]
      exact integralPolynomial_add (integralPolynomial_action hh g) hg
    | inv g _ hg =>
      have h := congrArg ((sourceBinaryCoefficientRep ℚ Q w).ρ g⁻¹)
        (groupCohomology.cocycles₁_map_inv c g)
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply, map_neg] at h
      rw [h, smul_neg, ← map_smul]
      exact integralPolynomial_neg (integralPolynomial_action hg g⁻¹)
  choose z hz using hall
  let zc : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℤ Q w) :=
    ⟨z, (groupCohomology.mem_cocycles₁_iff _).mpr (by
      intro g h
      apply homogeneousCoefficientMap_injective w (Int.castRingHom ℚ) Int.cast_injective
      rw [hz, map_add, sourceBinaryCoefficientMap_equivariant, hz, hz,
        (groupCohomology.mem_cocycles₁_iff c).mp c.property, smul_add, map_smul])⟩
  refine ⟨d, zc, hd, ?_⟩
  apply groupCohomology.cocycles₁_ext
  intro g
  exact hz g

/-- Integral cocycles span the full original rational binary cocycle space. -/
theorem sourceRationalBinaryCocycles_span_integer (Q w : ℕ) [NeZero Q] :
    Submodule.span ℚ
      (Set.range (sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w)) = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨d, z, hd, hz⟩ := sourceRationalBinaryCocycle_integerMultiple Q w c
  have hmem := Submodule.subset_span (R := ℚ) (Set.mem_range_self
    (f := sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w) z)
  have h := Submodule.smul_mem
    (Submodule.span ℚ (Set.range (sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w)))
    (d : ℚ)⁻¹ hmem
  rw [hz, smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), one_smul] at h
  exact h

end
end Dubon2026
