import Dubon2026.OriginalUnramifiedDecompositionCyclic
import Mathlib.RingTheory.Frobenius

/-! The actual arithmetic Frobenius generates the original unramified
prime stabilizer. This sharpens the existing cyclicity theorem with its
specified generator for DUB-17's selected auxiliary-prime dimension input. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField Pointwise

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every original decomposition element at an index-one prime is a power
of the same original arithmetic Frobenius. Its generator is identified by
the literal residue action, not an unspecified cyclic-group witness. -/
theorem originalUnramified_frobenius_generates_stabilizer
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (hunr : v.asIdeal.ramificationIdx w.asIdeal = 1)
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal)
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    g.val ∈ Subgroup.zpowers σ := by
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let f := Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal Gal(L/K)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [Ideal.Quotient.ker_stabilizerHom,
      numberField_inertia_eq_bot_of_ramificationIdx_one v w hunr]
    exact Subgroup.bot_subgroupOf _
  let s : MulAction.stabilizer Gal(L/K) w.asIdeal := ⟨σ, hσ.mem_stabilizer⟩
  have hs : f s = FiniteField.frobeniusAlgEquivOfAlgebraic
      (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx := hσ.mk_apply x
    rw [← Ideal.over_def w.asIdeal v.asIdeal, Nat.card_eq_fintype_card] at hx
    exact hx
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)).surjective (f g)
  have he : s ^ n.val = g := hf (by rw [map_pow, hs]; exact hn)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(n.val : ℤ), ?_⟩
  rw [zpow_natCast]
  exact congrArg Subtype.val he

end
end Dubon2026
