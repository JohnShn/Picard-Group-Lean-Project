import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup

/-!
## Picard group vs. ideal class group

This project’s first goal is to formalize (at least the statement of) the classical result that,
for a commutative domain, the Picard group is (canonically) isomorphic to the ideal class group.
-/

namespace Picard

/-- The Picard group of a commutative domain is isomorphic to its ideal class group. -/
theorem picardGroup_mulEquiv_classGroup
    (R : Type*) [CommRing R] [IsDomain R] :
  Nonempty (CommRing.Pic R ≃* ClassGroup R) := by
  classical
  sorry

end Picard
