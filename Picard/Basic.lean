import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Finsupp.SMul
import Mathlib.RingTheory.Localization.BaseChange

open scoped TensorProduct
open scoped nonZeroDivisors

/-!
## Picard group vs. ideal class group

This project’s first goal is to formalize (at least the statement of) the classical result that,
for a commutative domain, the Picard group is (canonically) isomorphic to the ideal class group.
-/

namespace Picard

section TorsionFree

variable {R : Type*} [CommRing R] [IsDomain R]
variable {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]

/-- Projective modules over a domain are torsion-free:
if `s ≠ 0` and `s • p = 0`, then `p = 0`.

This is formulated via `NoZeroSMulDivisors`, and proved by using the defining embedding of a
projective module into a free module. -/
lemma projective_torsionFree {s : R} (hs : s ≠ 0) {p : P} (hsp : s • p = 0) : p = 0 := by
  classical
  obtain ⟨retract, hleft⟩ := (Module.projective_def (R := R) (P := P)).1 (by infer_instance)
  haveI : NoZeroSMulDivisors R (P →₀ R) := by infer_instance
  haveI : NoZeroSMulDivisors R P :=
    (hleft.injective).noZeroSMulDivisors (R := R) (M := P) (N := P →₀ R) retract
      (by simp)
      (by intro c x; simp)
  exact (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hsp).resolve_left hs

end TorsionFree

section Localization

variable {R : Type*} [CommRing R] [IsDomain R]
variable {T : Type*} [AddCommGroup T] [Module R T]

/-- Localization map is injective for torsion-free modules.

This is the Lean version of: if `R` is a domain, `S = R \ {0}` and `T` is torsion-free,
then the canonical map `T → S⁻¹T` is injective.

In Mathlib, we take `S := R⁰ := nonZeroDivisors R`. -/
lemma localization_mkLinearMap_injective [NoZeroSMulDivisors R T] :
    Function.Injective (LocalizedModule.mkLinearMap (R⁰) T) := by
  -- Reduce to: the kernel is `⊥`.
  refine (LinearMap.ker_eq_bot).1 ?_
  ext t
  constructor
  · intro ht
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff (S := (R⁰)) (m := t)).1 ht with ⟨r, hrS, hrt⟩
    have hr0 : (r : R) ≠ 0 := nonZeroDivisors.ne_zero (M₀ := R) hrS
    exact (Submodule.mem_bot _).2 <|
      (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hrt).resolve_left hr0
  · intro ht
    -- If `t = 0`, then it certainly maps to `0`.
    have ht0 : t = 0 := by simpa [Submodule.mem_bot] using ht
    -- Membership in the kernel is the same as mapping to `0`.
    simp [ht0]

/-- A convenient reformulation: the canonical map `T → FractionRing R ⊗[R] T`,
`t ↦ (1 : FractionRing R) ⊗ₜ t`, is injective for torsion-free `T`.

This matches the statement “`T → S⁻¹T ≃ K ⊗[R] T` is injective” where `K` is the field of
fractions and `S = R \ {0}`. -/
lemma tensor_fractionRing_mk_one_injective [NoZeroSMulDivisors R T] :
    Function.Injective (TensorProduct.mk R (FractionRing R) T 1) := by
  -- `FractionRing R` is the localization of `R` at `R⁰`, and tensor base-change is a localized
  -- module; therefore `t ↦ 1 ⊗ₜ t` is a localization map of modules.
  refine (LinearMap.ker_eq_bot).1 ?_
  ext t
  constructor
  · intro ht
    haveI : IsLocalizedModule (R⁰) (TensorProduct.mk R (FractionRing R) T 1) := inferInstance
    have ht' : ∃ s : (R⁰), s • t = 0 :=
      (IsLocalizedModule.eq_zero_iff (S := (R⁰)) (f := TensorProduct.mk R (FractionRing R) T 1)
          (m := t)).1 (show (TensorProduct.mk R (FractionRing R) T 1) t = 0 by
            simpa [LinearMap.mem_ker] using ht)
    rcases ht' with ⟨s, hs⟩
    have hs0 : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero (M₀ := R) s
    have hsR : ((s : R) • t) = 0 := by
      simpa [Submonoid.smul_def] using hs
    exact (Submodule.mem_bot _).2 <|
      (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero (R := R) (M := T) hsR).resolve_left hs0
  · intro ht
    have ht0 : t = 0 := by simpa [Submodule.mem_bot] using ht
    simp [ht0]

end Localization

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
    (M : Type*) [AddCommGroup M] [Module R M] (hinv : Module.Invertible R M) :
  Nonempty (FractionRing R ⊗[R] M ≃ₗ[FractionRing R] FractionRing R) := by
  apply invertible_over_field (K := FractionRing R) (V := FractionRing R ⊗[R] M)
  -- Tensoring preserves invertibility
  exact Module.Invertible.instTensorProduct_2 R M (FractionRing R) (FractionRing R)


/-!
## Embedding an invertible module into the fraction field

This is the Lean version of the standard argument:

- over a domain, a projective module is torsion-free, so `m ↦ 1 ⊗ₜ m` into the localization is
  injective;
- if `M` is invertible, then `K ⊗[R] M ≃ K` as `K`-modules, so composing yields an embedding
  `M ↪ K`;
- the image is finitely generated since `M` is.

Note: your informal proof says “injective `R`-module”; the argument you outlined uses the
`Module.Invertible` hypotheses (which give projective + finite), so we formalize that version.
-/

/-- If `R` is a domain and `M` is an invertible `R`-module, then `M` embeds into `FractionRing R`.

Moreover, the image is a finitely generated `R`-submodule of `FractionRing R`. -/
theorem embed_in_fractionRing_of_invertible (R : Type*) [CommRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    ∃ ι : M →ₗ[R] FractionRing R,
      Function.Injective ι ∧ (LinearMap.range ι).FG := by
  classical
  -- `M` is torsion-free as an `R`-module (since it is projective over a domain).
  haveI : NoZeroSMulDivisors R M := by
    refine ⟨?_⟩
    intro c m hcm
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (projective_torsionFree (R := R) (P := M) (s := c) hc (p := m) hcm)
  -- The canonical map `M → K ⊗[R] M`, `m ↦ 1 ⊗ₜ m`, is injective.
  have hMk : Function.Injective (TensorProduct.mk R (FractionRing R) M 1) :=
    tensor_fractionRing_mk_one_injective (R := R) (T := M)
  -- Choose a `K`-linear equivalence `K ⊗[R] M ≃ K` (since `M` is invertible).
  obtain ⟨e⟩ :=
    tensor_invertible_with_field_of_fractions (R := R) (M := M)
      (hinv := (by infer_instance : Module.Invertible R M))
  -- Compose to get `ι : M → K`.
  let ι : M →ₗ[R] FractionRing R :=
    (e.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (FractionRing R) M 1
  refine ⟨ι, ?_, ?_⟩
  · -- Injectivity follows from injectivity of both factors.
    exact (e.restrictScalars R).injective.comp hMk
  · -- The image is finitely generated since `M` is a finite module.
    have htop : (⊤ : Submodule R M).FG := Module.Finite.fg_top (R := R) (M := M)
    -- `range ι = map ι ⊤`.
    simpa [ι, Submodule.map_top] using (htop.map ι)




end Picard
