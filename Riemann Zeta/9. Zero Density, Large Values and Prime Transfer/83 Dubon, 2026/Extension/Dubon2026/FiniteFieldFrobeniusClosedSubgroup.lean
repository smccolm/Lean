import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.KrullTopology

/-! Frobenius generates the original Krull automorphism group topologically.
This supplies cyclicity of finite residue-action quotients for DUB-17,
using pinned finite-field Frobenius surjectivity on each finite subfield. -/

namespace Dubon2026
noncomputable section
open scoped Topology

variable (k L : Type*) [Field k] [Fintype k] [Field L] [Algebra k L]
  [Algebra.IsAlgebraic k L]

/-- A closed subgroup of the original residue automorphism group containing
arithmetic Frobenius is the whole group. No alternate field is introduced. -/
theorem finiteField_closedSubgroup_eq_top_of_frobenius_mem
    (H : Subgroup Gal(L/k)) (hH : IsClosed (H : Set Gal(L/k)))
    (hφ : FiniteField.frobeniusAlgEquivOfAlgebraic k L ∈ H) : H = ⊤ := by
  classical
  apply top_unique
  intro g _
  by_contra hg
  let W := (fun h : Gal(L/k) => g * h) ⁻¹' (H : Set Gal(L/k))ᶜ
  have hW : IsOpen W := hH.isOpen_compl.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : Gal(L/k)) ∈ W := by simpa [W] using hg
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff k L W).mp (hW.mem_nhds h1)
  letI : FiniteDimensional k E := hE
  letI : Finite E := Module.finite_of_finite k
  letI : Fintype E := Fintype.ofFinite E
  letI : Normal k E := Normal.of_isSplittingField
    (Polynomial.X ^ Fintype.card E - Polynomial.X : Polynomial k)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).surjective
    (g.restrictNormal E)
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k L
  have he : g⁻¹ * φ ^ n.val ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply g.injective
    change g (g.symm ((φ ^ n.val) x)) = g x
    rw [AlgEquiv.apply_symm_apply]
    have ht := congrArg (fun e : Gal(E/k) => (e ⟨x, hx⟩ : L)) hn
    have hpow (a : ℕ) : ∀ y : E,
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ a) y : L) = (φ ^ a) (y : L) := by
      induction a with
      | zero => intro y; rfl
      | succ a ih =>
        intro y
        rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
        rw [ih]
        rfl
    change ((FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ n.val) ⟨x, hx⟩ : L) =
      (g.restrictNormal E ⟨x, hx⟩ : L) at ht
    rw [hpow n.val] at ht
    exact ht.trans (AlgEquiv.restrictNormal_commutes g E ⟨x, hx⟩)
  have hnH := H.pow_mem hφ n.val
  have hnW := hEW he
  change g * (g⁻¹ * φ ^ n.val) ∉ H at hnW
  exact hnW (by simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hnH)

end
end Dubon2026
