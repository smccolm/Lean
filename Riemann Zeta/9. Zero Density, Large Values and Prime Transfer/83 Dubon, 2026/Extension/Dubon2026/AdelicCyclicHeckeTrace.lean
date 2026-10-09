import Dubon2026.AdelicHeckeClassicalRestriction

/-! # The original Hecke trace in the genuine algebraic cyclic representation and its Hilbert completion -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Restrict the actual original algebraic cusp representation to its genuine finite-place subgroup. -/
def adelicCyclicFiniteRepresentation : Representation ℂ
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (adelicLiftCyclicRepresentation N k f).toSubmodule :=
  (adelicLiftCyclicRepresentation N k f).toRepresentation.comp rationalAdelicFiniteGL2Embedding

/-- The genuine finite Hecke sum acting on the original algebraic cyclic cusp functions. -/
def adelicAlgebraicHeckeTrace (p : ℕ) [NeZero p] (hpN : p.Coprime N) :
    Module.End ℂ (adelicLiftCyclicRepresentation N k f).toSubmodule :=
  finiteAdelicHeckeTrace (adelicCyclicFiniteRepresentation f) N p hpN

/-- The same actual finite-adelic operator sum acts on the original completed Hilbert representation. -/
def adelicHilbertHeckeTrace (p : ℕ) [NeZero p] (hpN : p.Coprime N) : Module.End ℂ (AdelicCyclicHilbert f) :=
  finiteAdelicHeckeTrace ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding) N p hpN

/-- Literal function inclusion intertwines the actual algebraic Hecke trace with the same original full-function trace. -/
theorem adelicAlgebraicHeckeTrace_coe (p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    (adelicAlgebraicHeckeTrace f p hpN v).val =
      finiteAdelicHeckeTrace adelicFunctionFiniteRepresentation N p hpN v.val :=
  finiteAdelicHeckeTrace_intertwines (adelicCyclicFiniteRepresentation f) adelicFunctionFiniteRepresentation
    N p hpN (adelicLiftCyclicRepresentation N k f).toSubmodule.subtype (fun _ _ => rfl) v

/-- The original faithful Hilbert embedding intertwines the actual finite Hecke operators exactly. -/
theorem adelicHeckeTrace_embedding (p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    adelicCyclicHilbertEmbedding f (adelicAlgebraicHeckeTrace f p hpN v) =
      adelicHilbertHeckeTrace f p hpN (adelicCyclicHilbertEmbedding f v) :=
  finiteAdelicHeckeTrace_intertwines (adelicCyclicFiniteRepresentation f)
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding) N p hpN
    (adelicCyclicHilbertEmbedding f)
    (fun g v => (adelicCyclicHilbertEmbedding_intertwines f (rationalAdelicFiniteGL2Embedding g) v).symm) v

/-- The actual Hilbert Hecke trace preserves the original finite-level fixed subspace. -/
theorem adelicHilbertHeckeTrace_level (p : ℕ) [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicLevelFixedSpace f) :
    adelicHilbertHeckeTrace f p hpN v ∈ adelicLevelFixedSpace f :=
  finiteAdelicHeckeTrace_level_fixed
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding) N p hpN v hv

/-- Genuine full adelic intertwiners commute with the actual original Hilbert Hecke trace. -/
theorem adelicHilbertHeckeTrace_intertwiner (p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (A : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f g v) = adelicCyclicHilbertRepresentation f g (A v))
    (v : AdelicCyclicHilbert f) : A (adelicHilbertHeckeTrace f p hpN v) = adelicHilbertHeckeTrace f p hpN (A v) :=
  finiteAdelicHeckeTrace_intertwiner
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding) N p hpN A.toLinearMap
    (fun g v => hA (rationalAdelicFiniteGL2Embedding g) v) v

end
end Dubon2026
