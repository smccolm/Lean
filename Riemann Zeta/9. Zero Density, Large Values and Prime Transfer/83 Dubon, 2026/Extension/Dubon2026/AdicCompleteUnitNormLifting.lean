import Dubon2026.AdicCompletePrincipalNormLifting

/-! # Lifting actual residue norm preimages to original complete-ring unit norms -/

namespace Dubon2026
noncomputable section

variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
  (I : Ideal R) [IsAdicComplete I R]

include b in
/-- An original extension unit with the correct residual norm can be
corrected to an exact norm preimage in the original extension ring. The
correction comes from the actual complete-ring principal norm lift. -/
theorem adicComplete_unit_norm_lift
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (u : Rˣ) (a : Sˣ)
    (ha : Ideal.Quotient.mk I (Algebra.norm R a.val) = Ideal.Quotient.mk I u.val) :
    ∃ v : Sˣ, Units.map (Algebra.norm R (S := S)) v = u := by
  let n : Rˣ := Units.map (Algebra.norm R (S := S)) a
  let q := Units.map (Ideal.Quotient.mk I).toMonoidHom
  have hq : q n = q u := Units.ext ha
  have hc : q (u / n) = 1 := by rw [map_div, hq, div_self']
  have hcv : Ideal.Quotient.mk I (u / n).val = 1 := congrArg Units.val hc
  have hprincipal : 1 - (u / n).val ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, hcv, sub_self]
  obtain ⟨v, hv⟩ := adicComplete_exists_principal_unit_norm b I x hx (u / n) hprincipal
  refine ⟨a * v, ?_⟩
  rw [map_mul, hv]
  change n * (u / n) = u
  rw [mul_comm n, div_mul_cancel]

include b in
/-- Actual residual norm preimages and a unit residual trace direction
imply surjectivity of the original finite-free algebra unit norm over the
complete base. Both residual conditions remain explicit upstream inputs. -/
theorem adicComplete_unit_norm_surjective
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (hres : ∀ u : Rˣ, ∃ a : Sˣ,
      Ideal.Quotient.mk I (Algebra.norm R a.val) = Ideal.Quotient.mk I u.val) :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) := by
  intro u
  obtain ⟨a, ha⟩ := hres u
  exact adicComplete_unit_norm_lift b I x hx u a ha

end
end Dubon2026
