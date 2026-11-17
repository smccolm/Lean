/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Public statements for Dickson's classification in `PGL₂`

DUB-17/18 -> actual residual-image classification. These are only the literal
finite-field closure and projective matrix groups. Upstream admitted statement
copies are omitted; no classification theorem is assumed.
-/



namespace Dubon2026.SourceDickson

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- An algebraic closure `K p` of the finite field `𝔽_p = ZMod p`. -/
noncomputable abbrev K : Type := AlgebraicClosure (ZMod p)

/-- The projective general linear group `PGL₂(K p)`, i.e. `GL₂(K p)` modulo its centre. -/
abbrev PGL : Type := Matrix.ProjGenLinGroup (Fin 2) (K p)

/-- The projective special linear group `PSL₂(K p)`. -/
abbrev PSL : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K p)


end Dubon2026.SourceDickson
