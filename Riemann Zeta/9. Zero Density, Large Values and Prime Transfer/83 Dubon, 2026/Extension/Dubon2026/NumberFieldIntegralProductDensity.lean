/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Dubon2026.NumberFieldIntegralPlaceApproximation

/-! # Density in the original product of finite integral completions

Adapted from TauCetiProject/TauCeti at
51d586d1cdfd170cd66989af5fda3e6a9e07ca4d, with valuation balls in place of
an additional maximal-ideal topology port. Finite-coordinate Chinese
remainder approximation supplies the original integral density needed
for DUB-17's adelic lattice local recovery.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Topology
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Every original local integral neighborhood of zero contains a sufficiently small valuation ball. -/
theorem numberFieldIntegralPlace_nhds_bound (v : HeightOneSpectrum (𝓞 K))
    {s : Set (v.adicCompletionIntegers K)} (hs : s ∈ nhds 0) :
    ∃ n : ℕ, ∀ x : v.adicCompletionIntegers K,
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) → x ∈ s := by
  obtain ⟨t, ht, hts⟩ := mem_nhds_subtype _ _ _ |>.mp hs
  rw [ZeroMemClass.coe_zero] at ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
  have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.val : ℤᵐ⁰) ≠ 0 :=
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨m, hm⟩ : ∃ m : ℤ, exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.val := by
    refine ⟨log (MonoidWithZeroHom.ValueGroup₀.embedding γ.val) - 1, ?_⟩
    exact (exp_lt_exp.mpr (by omega)).trans_eq (exp_log hγ0)
  refine ⟨(-m).toNat, fun x hx => hts ?_⟩
  apply hγ
  apply (Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
  apply hx.trans_lt
  calc
    exp (-(((-m).toNat : ℤ))) ≤ exp m := exp_le_exp.mpr (by omega)
    _ < _ := hm

/-- The global ring of integers is dense diagonally in the whole product of its original local integers. -/
theorem numberFieldIntegers_dense_integral_product :
    DenseRange (fun r : 𝓞 K => fun v : HeightOneSpectrum (𝓞 K) =>
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) := by
  classical
  intro y
  refine mem_closure_iff_nhds.mpr fun U hU => ?_
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hIt⟩ := hU
  have hzero (v : HeightOneSpectrum (𝓞 K)) :
      (fun z : v.adicCompletionIntegers K => y v - z) ⁻¹' t v ∈ nhds 0 :=
    (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht v)
  choose n hn using fun v => numberFieldIntegralPlace_nhds_bound K v (hzero v)
  obtain ⟨r, hr⟩ := numberFieldIntegralPlaces_approximation K hI.toFinset y n
  refine ⟨(fun v => algebraMap (𝓞 K) (v.adicCompletionIntegers K) r), ?_, r, rfl⟩
  apply hIt
  intro v hv
  have happ := hr v (hI.mem_toFinset.mpr hv)
  have hm : y v - algebraMap (𝓞 K) (v.adicCompletionIntegers K) r ∈
      (fun z : v.adicCompletionIntegers K => y v - z) ⁻¹' t v := by
    apply hn v
    exact happ
  simpa only [Set.mem_preimage, sub_sub_cancel] using hm

end
end Dubon2026
