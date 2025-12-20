import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup

open scoped TensorProduct

/-!
## Picard group vs. ideal class group

This project’s first goal is to formalize (at least the statement of) the classical result that,
for a commutative domain, the Picard group is (canonically) isomorphic to the ideal class group.
-/

namespace Picard

variable (R : Type*) [CommRing R]

/-- The Picard group of a commutative domain is isomorphic to its ideal class group. -/
theorem picardGroup_mulEquiv_classGroup
    [IsDomain R] :
  Nonempty (CommRing.Pic R ≃* ClassGroup R) := by
  sorry


/-- Invertible $K$-modules are trivial in the Picard group of a field.

Let $K$ be a field and let $V$ be a $K$-module. If $V$ is invertible as a $K$-module, then
there exists a $K$-linear isomorphism $V \cong K$.
Equivalently, $V$ is $1$-dimensional as a $K$-vector space. -/
theorem invertible_over_field (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    (hinv : Module.Invertible K V) :
  Nonempty (V ≃ₗ[K] K) := by
  -- Apply the mathlib lemma Module.Invertible.free_iff_linearEquiv
  apply (Module.Invertible.free_iff_linearEquiv).mp
  -- Over a field, every module is a vector space and hence is free
  exact Module.Free.of_divisionRing K V


/-- Let K be the field of fractions of a domain R, and let M be an invertible R-module.
Then M ⊗ R K is isomorphic to K as a left K-module. -/
theorem tensor_invertible_with_field_of_fractions (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsLocalization (Submonoid.powers 0 : Submonoid R) K]
    (M : Type*) [AddCommGroup M] [Module R M] (hinv : Module.Invertible R M) :
  Nonempty (K ⊗[R] M ≃ₗ[K] K) := by
  apply invertible_over_field K (K ⊗[R] M)
  -- Tensoring preserves invertibility
  exact Module.Invertible.instTensorProduct_2 R M K K




end Picard
