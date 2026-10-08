import Dubon2026.ComplexSl2Basis
import Dubon2026.UniversalEnvelopingInduction
import Dubon2026.Sl2CasimirAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # The actual central normalized Casimir in the genuine complex sl2 enveloping algebra -/

namespace Dubon2026

noncomputable section

local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ (L := ComplexSl2)

/-- The actual three matrix generators retain their precise brackets inside the genuine enveloping algebra. -/
theorem complexSl2Enveloping_brackets :
    ι complexSl2A * ι complexSl2U - ι complexSl2U * ι complexSl2A = ι complexSl2U ∧
    ι complexSl2A * ι complexSl2F - ι complexSl2F * ι complexSl2A = -ι complexSl2F ∧
    ι complexSl2U * ι complexSl2F - ι complexSl2F * ι complexSl2U = ι complexSl2A + ι complexSl2A := by
  have hAU := (ι).map_lie complexSl2A complexSl2U
  have hAF := (ι).map_lie complexSl2A complexSl2F
  have hUF := (ι).map_lie complexSl2U complexSl2F
  constructor
  · simpa only [complexSl2_bracket_A_U, LieRing.of_associative_ring_bracket] using hAU.symm
  constructor
  · simpa only [complexSl2_bracket_A_F, map_neg, LieRing.of_associative_ring_bracket] using hAF.symm
  · simpa only [complexSl2_bracket_U_F, map_add, LieRing.of_associative_ring_bracket] using hUF.symm

/-- The normalized Casimir as a literal element of the actual universal enveloping algebra of traceless complex matrices. -/
def complexSl2EnvelopingCasimir : UniversalEnvelopingAlgebra ℂ ComplexSl2 :=
  normalizedSl2Casimir (ι complexSl2A) (ι complexSl2U) (ι complexSl2F)

/-- The actual quadratic element commutes with the image of every original traceless matrix. -/
theorem complexSl2EnvelopingCasimir_commutes_generator (x : ComplexSl2) :
    Commute complexSl2EnvelopingCasimir (ι x) := by
  have hb := complexSl2Enveloping_brackets
  have hc := normalizedSl2Casimir_commutes (ι complexSl2A) (ι complexSl2U) (ι complexSl2F)
    hb.1 hb.2.1 hb.2.2
  rw [complexSl2_decomposition x, map_add, map_add, map_smul, map_smul, map_smul]
  exact ((hc.1.smul_right (2 * x.val 0 0)).add_right (hc.2.1.smul_right (x.val 0 1))).add_right
    (hc.2.2.smul_right (x.val 1 0))

/-- The actual normalized quadratic element commutes with every element of the full universal enveloping algebra. -/
theorem complexSl2EnvelopingCasimir_commutes (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) :
    Commute complexSl2EnvelopingCasimir z := by
  apply universalEnveloping_induction (fun w => Commute complexSl2EnvelopingCasimir w)
    (fun r => ?_) complexSl2EnvelopingCasimir_commutes_generator
    (fun _ _ hx hy => hx.add_right hy) (fun _ _ hx hy => hx.mul_right hy) z
  exact (Algebra.commutes r complexSl2EnvelopingCasimir).symm

/-- The original normalized Casimir belongs to the genuine algebraic center of the full enveloping algebra. -/
theorem complexSl2EnvelopingCasimir_mem_center :
    complexSl2EnvelopingCasimir ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2) := by
  rw [Subalgebra.mem_center_iff]
  intro z
  exact (complexSl2EnvelopingCasimir_commutes z).symm.eq

end
end Dubon2026
