# Picard Group and Ideal Class Group Isomorphism in Lean 4

## Overview
This repository contains the formalization of commutative algebra theorems concerning fractional ideals, Picard groups, and ideal class groups within the Lean 4 proof assistant, utilizing the Mathlib library. The primary objective is to formalize the canonical isomorphism between the Picard group and the ideal class group for an arbitrary commutative domain.

## Repository Structure
* `Basic.lean`: Establishes commutative algebra prerequisites, demonstrating that invertible modules can be embedded into fraction fields and equivalently represented as integral ideals.
* `UFD.lean`: Formalizes the theorem that the ideal class group of a Unique Factorization Domain (UFD) is trivial.
* `Eisenbud.lean`: Formulates the tensor products of fractional ideals to construct the isomorphism between the Picard group and the ideal class group.

## Compilation and Execution
* **Dependencies:** Lean 4, Mathlib (`mathlib4`).
* **Build Command:**
```bash
  lake build
```

## Upstream Contributions
The formalizations contained in `UFD.lean` establishing the triviality of the ideal class group for UFDs and normalized GCD domains have been merged upstream into Mathlib via pull request 33744.

## TODOs
* **Overarching Isomorphism:** Complete the proof of `picardGroup_equiv_classGroup` demonstrating the full Picard-Class group equivalence.
* **Local-to-Global Injectivity:** Finalize the lemma asserting that invertible fractional ideals over local rings are free of rank 1 (`invertible_fractionalIdeal_free_rank_one`) to close the local-to-global injectivity deduction for the multiplication map.