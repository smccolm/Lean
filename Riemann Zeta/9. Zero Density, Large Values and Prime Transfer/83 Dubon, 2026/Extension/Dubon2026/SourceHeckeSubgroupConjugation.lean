import Dubon2026.HeckeCongruenceConjugation

/-! The original diagonal Hecke conjugation as a homomorphism.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
compatibility. The existing integral transition already proves closure
in the actual Gamma0. Uniqueness in GL2 supplies multiplicativity, without
rebuilding the matrix-entry or coset arguments from the external proof.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {p Q : ℕ} [NeZero p]

/-- The actual upper subgroup has finite index by reduction of the original matrices modulo p. -/
theorem sourceHeckeUpper_finiteIndex :
    (heckeUpperSubgroup Q p).FiniteIndex := by
  let red : Gamma0 Q →* SL(2, ZMod p) :=
    (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod p))).comp
      (Gamma0 Q).subtype
  haveI : red.ker.FiniteIndex := Subgroup.finiteIndex_ker red
  apply Subgroup.finiteIndex_of_le (H := red.ker)
  intro γ hγ
  have h := congrArg (fun A : SL(2, ZMod p) => A 0 1) hγ
  change (((γ.val 0 1 : ℤ) : ZMod p)) = 0
  simpa [red, MonoidHom.mem_ker] using h

/-- A finite enumeration of the genuine Hecke quotient, derived from its actual congruence kernel. -/
abbrev sourceHeckeUpperFintype (Q p : ℕ) [NeZero p] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) := by
  letI := sourceHeckeUpper_finiteIndex (Q := Q) (p := p)
  exact Fintype.ofFinite _

/-- The original diagonal conjugation, with integrality and level derived
from the already proved actual subgroup transition. -/
def sourceHeckeConjugation (hp : Nat.Prime p) :
    heckeUpperSubgroup Q p →* Gamma0 Q where
  toFun γ := (heckeUpperSubgroup_transition hp γ.val γ.property).choose
  map_one' := by
    apply Subtype.ext
    apply mapGL_injective (S := ℝ)
    have h := (heckeUpperSubgroup_transition hp
      (1 : Gamma0 Q) (one_mem (heckeUpperSubgroup Q p))).choose_spec.2
    simpa only [Subgroup.coe_one, map_one, mul_one, one_mul] using
      (mul_right_cancel (b := (1 : GL (Fin 2) ℝ)) (by simpa using h.symm))
  map_mul' γ δ := by
    apply Subtype.ext
    apply mapGL_injective (S := ℝ)
    apply mul_right_cancel (b := heckeTriangularMatrix 1 p 0)
    have hg := (heckeUpperSubgroup_transition hp γ.val γ.property).choose_spec.2
    have hd := (heckeUpperSubgroup_transition hp δ.val δ.property).choose_spec.2
    have hgd := (heckeUpperSubgroup_transition hp (γ * δ).val (γ * δ).property).choose_spec.2
    rw [← hgd]
    change heckeTriangularMatrix 1 p 0 * mapGL ℝ (γ.val.val * δ.val.val) = _
    calc
      _ = (heckeTriangularMatrix 1 p 0 * mapGL ℝ γ.val.val) *
          mapGL ℝ δ.val.val := by rw [map_mul, mul_assoc]
      _ = (mapGL ℝ (heckeUpperSubgroup_transition hp γ.val γ.property).choose.val *
          heckeTriangularMatrix 1 p 0) * mapGL ℝ δ.val.val :=
        congrArg (fun x => x * mapGL ℝ δ.val.val) hg
      _ = mapGL ℝ (heckeUpperSubgroup_transition hp γ.val γ.property).choose.val *
          (mapGL ℝ (heckeUpperSubgroup_transition hp δ.val δ.property).choose.val *
            heckeTriangularMatrix 1 p 0) :=
        (mul_assoc _ _ _).trans (congrArg
          (fun x => mapGL ℝ (heckeUpperSubgroup_transition hp γ.val γ.property).choose.val * x) hd)
      _ = _ := by rw [← mul_assoc, ← map_mul]; rfl

/-- The chosen original subgroup homomorphism satisfies the exact diagonal equation. -/
theorem sourceHeckeConjugation_matrix (hp : Nat.Prime p)
    (γ : heckeUpperSubgroup Q p) :
    heckeTriangularMatrix 1 p 0 * mapGL ℝ γ.val.val =
      mapGL ℝ (sourceHeckeConjugation (Q := Q) hp γ).val *
        heckeTriangularMatrix 1 p 0 :=
  (heckeUpperSubgroup_transition hp γ.val γ.property).choose_spec.2

/-- The original subgroup conjugation is faithful. -/
theorem sourceHeckeConjugation_injective (hp : Nat.Prime p) :
    Function.Injective (sourceHeckeConjugation (Q := Q) hp) := by
  intro γ δ h
  have e := (sourceHeckeConjugation_matrix hp γ).trans
    ((congrArg (fun x : Gamma0 Q => mapGL ℝ x.val * heckeTriangularMatrix 1 p 0) h).trans
      (sourceHeckeConjugation_matrix hp δ).symm)
  exact Subtype.ext (Subtype.ext (mapGL_injective (mul_left_cancel e)))

end
end Dubon2026
