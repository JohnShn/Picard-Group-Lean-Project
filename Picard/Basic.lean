import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup

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

section InvertibleOverFields

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module.Invertible K V]

/-- Invertible $K$-modules are trivial in the Picard group of a field.

Let $K$ be a field and let $V$ be a $K$-module. If $V$ is invertible as a $K$-module, then
there exists a $K$-linear isomorphism $V \cong K$.
Equivalently, $V$ is $1$-dimensional as a $K$-vector space. -/
theorem invertible_over_field : Nonempty (V ≃ₗ[K] K) := by
  -- Apply the mathlib lemma Module.Invertible.free_iff_linearEquiv
  apply (Module.Invertible.free_iff_linearEquiv).mp
  -- Over a field, every module is a vector space and hence is free
  exact Module.Free.of_divisionRing K V

end InvertibleOverFields

section TensorWithFractionField

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Invertible R M]

/-- Let K be the field of fractions of a domain R, and let M be an invertible R-module.
Then M ⊗ R K is isomorphic to K as a left K-module. -/
theorem tensor_invertible_with_field_of_fractions :
  Nonempty (FractionRing R ⊗[R] M ≃ₗ[FractionRing R] FractionRing R) := by
  apply invertible_over_field (K := FractionRing R) (V := FractionRing R ⊗[R] M)
  -- Tensoring preserves invertibility
  --exact Module.Invertible.instTensorProduct_2 R M (FractionRing R) (FractionRing R)

end TensorWithFractionField


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

section InvertibleEmbeddings

variable {R : Type*} [CommRing R] [IsDomain R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Invertible R M]

/-- If `R` is a domain and `M` is an invertible `R`-module, then `M` embeds into `FractionRing R`.

Moreover, the image is a finitely generated `R`-submodule of `FractionRing R`. -/
theorem embed_in_fractionRing_of_invertible :
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
  obtain ⟨e⟩ := tensor_invertible_with_field_of_fractions (R := R) (M := M)
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


/-- Every invertible `R`-module over a domain is isomorphic to an (integral) ideal of `R`.

Here “invertible ideal” is meant in the same sense as `Module.Invertible R I` for the
`R`-module `I` (viewing an ideal as an `R`-submodule of `R`).

Construction: embed `M` into `K := FractionRing R`, take the induced finitely generated
`R`-submodule `I₀ ⊆ K`, view it as a fractional ideal, and take its numerator ideal in `R`.
-/
theorem invertible_isomorphic_to_ideal :
    ∃ I : Ideal R, Module.Invertible R I ∧ Nonempty (M ≃ₗ[R] I) := by
  classical
  -- Embed `M` into the fraction field with finitely generated image.
  obtain ⟨ι, hιinj, hιfg⟩ := embed_in_fractionRing_of_invertible (R := R) (M := M)
  -- Regard the image as a fractional ideal, using finite generation to clear denominators.
  let I₀ : FractionalIdeal (R⁰) (FractionRing R) :=
    ⟨LinearMap.range ι,
      FractionalIdeal.isFractional_of_fg (R := R) (S := (R⁰)) (P := FractionRing R) hιfg⟩
  let I : Ideal R := I₀.num
  have hden0 : ((I₀.den : R) ≠ 0) := nonZeroDivisors.coe_ne_zero (M₀ := R) I₀.den
  -- `M ≃ range ι` since `ι` is injective.
  have e1 : M ≃ₗ[R] LinearMap.range ι := LinearEquiv.ofInjective ι hιinj
  -- `range ι` is definitional equal to `I₀` as a type of elements of `FractionRing R`.
  have e2 : LinearMap.range ι ≃ₗ[R] I₀ := by
    -- Both sides are the same subtype of `FractionRing R`.
    simpa [I₀] using (LinearEquiv.refl R (LinearMap.range ι))
  -- `I₀ ≃ I₀.num` via multiplication by the denominator.
  have e3 : I₀ ≃ₗ[R] I := by
    simpa [I, I₀] using
      (FractionalIdeal.equivNum (S := (R⁰)) (P := FractionRing R) (I := I₀) hden0)
  have eMI : M ≃ₗ[R] I := e1.trans (e2.trans e3)
  refine ⟨I, ?_, ⟨eMI⟩⟩
  -- Transfer invertibility along the `R`-linear equivalence.
  exact Module.Invertible.congr (R := R) (M := M) eMI

end InvertibleEmbeddings

section PrincipalIdealFreeRankOne

variable {R : Type*} [CommRing R] [IsDomain R]

/--
Over a commutative domain, the nonzero principal ideal `(a)` (implemented as `Ideal.span {a}`)
is a free `R`-module of rank `1`, witnessed by a linear equivalence with `R`.
-/
theorem principalIdeal_free_rank1 (a : R) (ha : a ≠ 0) :
    Module.Free R (Ideal.span ({a} : Set R)) ∧
      Nonempty (Ideal.span ({a} : Set R) ≃ₗ[R] R) := by
  classical
  -- `f : R →ₗ[R] Ideal.span {a}`,  r ↦ r * a
  let f : R →ₗ[R] Ideal.span ({a} : Set R) :=
  { toFun := fun r =>
      ⟨r * a, by
        have ha_mem : a ∈ Ideal.span ({a} : Set R) :=
          Ideal.subset_span (by simp)
        -- ideals are closed under left multiplication by ring elements
        simpa [mul_assoc] using
          (Ideal.mul_mem_left (Ideal.span ({a} : Set R)) r ha_mem)⟩
    map_add' := by
      intro r s
      ext
      simp [add_mul]
    map_smul' := by
      intro r s
      ext
      simp [mul_assoc] }
  have hf_bij : Function.Bijective f := by
    constructor
    · -- injective
      intro r s hrs
      have hrs' : (f r).1 = (f s).1 := congrArg Subtype.val hrs
      dsimp [f] at hrs'  -- now `hrs' : r * a = s * a`
      have h0 : (r - s) * a = 0 := by
        calc
          (r - s) * a = r * a - s * a := by
            simp [sub_mul]
          _ = 0 := by
            -- from `r*a = s*a` we get `r*a - s*a = 0`
            simpa [sub_eq_zero] using hrs'
      have hrs0 : r - s = 0 := (mul_eq_zero.mp h0).resolve_right ha
      exact sub_eq_zero.mp hrs0
    · -- surjective
      intro x
      rcases (Ideal.mem_span_singleton'.1 x.property) with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      ext
      -- `f r` is `r*a`, while `hr` is `a*r = x`; commute
      have : r * a = (x : R) := by
        simpa [mul_comm] using hr
      dsimp [f]
      exact this
  let e : R ≃ₗ[R] Ideal.span ({a} : Set R) :=
    LinearEquiv.ofBijective f hf_bij
  refine ⟨?_, ⟨e.symm⟩⟩
  haveI : Module.Free R R := Module.Free.self R
  exact Module.Free.of_equiv e

end PrincipalIdealFreeRankOne




--/-- The Picard group of a commutative domain is isomorphic to its ideal class group. -/
--theorem picardGroup_mulEquiv_classGroup (R : Type*) [CommRing R] [IsDomain R] :
--  Nonempty (CommRing.Pic R ≃* ClassGroup R) := by
--  sorry

/-!
## Invertible fractional ideals imply invertible modules

If `R` is a domain with fraction field `K` and `I` is an invertible fractional ideal of `R`
(i.e. a unit of `FractionalIdeal (R⁰) K`), then the underlying `R`-module `I` is invertible
in the sense of the Picard group (`Module.Invertible R I`).

Conceptually, the multiplication pairing gives an equivalence `I ⊗[R] I⁻¹ ≃ₗ[R] R`; the
existence of this equivalence is exactly the `Module.Invertible` witness. -/
section FractionalIdealToModuleInvertible

variable {R : Type*} [CommRing R] [IsDomain R]

open scoped nonZeroDivisors

local notation "K" => FractionRing R

/-- Auxiliary: tensor equivalence for a unit fractional ideal. -/
noncomputable def fractionalIdeal_tensorInvEquiv (u : (FractionalIdeal (R⁰) K)ˣ) :
  (u : FractionalIdeal (R⁰) K) ⊗[R]
    ((u⁻¹ : (FractionalIdeal (R⁰) K)ˣ) : FractionalIdeal (R⁰) K) ≃ₗ[R] R := by
  classical
  -- TODO: reuse a mathlib lemma if available; otherwise, build from multiplication pairing.
  sorry

/-- A nonzero invertible fractional ideal yields an invertible module. -/
theorem fractionalIdeal_isUnit_implies_moduleInvertible
    (I : FractionalIdeal (R⁰) K) (hIunit : IsUnit I) : Module.Invertible R I := by
  classical
  -- Mention the domain structure to placate the unused section variable linter.
  have _ := (inferInstance : IsDomain R)
  -- Choose a unit representative so that its inverse is definitionally available.
  rcases hIunit with ⟨u, rfl⟩
  let J : FractionalIdeal (R⁰) K := (u⁻¹ : (FractionalIdeal (R⁰) K)ˣ)
  -- Placeholder: obtain the tensor equivalence from the unit structure.
  have h : (u : FractionalIdeal (R⁰) K) ⊗[R] J ≃ₗ[R] R := by
    -- For a unit fractional ideal, the tensor with its inverse is canonically `R`.
    -- The definition of `J` matches the underlying fractional ideal of `u⁻¹`.
    simpa [J] using (fractionalIdeal_tensorInvEquiv (R := R) (u := u))
  -- Turn the equivalence into a `Module.Invertible` witness.
  exact Module.Invertible.left (R := R) (M := (u : FractionalIdeal (R⁰) K)) (N := J) h

end FractionalIdealToModuleInvertible

/-!
## Invertible module (fractional ideal) implies unit fractional ideal

If a fractional ideal `I` carries an invertible `R`-module structure, then `I` is a unit in
the fractional ideal monoid. The standard argument passes through the dual module and clears
denominators.
-/
section ModuleInvertibleToFractionalIdealUnit

variable {R : Type*} [CommRing R] [IsDomain R]
variable [Algebra R (FractionRing R)] [IsFractionRing R (FractionRing R)]
-- We rely on the canonical `Inv` instance for fractional ideals.

open scoped nonZeroDivisors

local notation "K" => FractionRing R

/-- Placeholder: identify the `R`-linear dual of a fractional ideal with its fractional inverse.
This rests on a clearing-denominators argument for finitely generated fractional ideals. -/
noncomputable def fractionalIdeal_dualEquiv_inv
  (I : FractionalIdeal (R⁰) (FractionRing R)) :
  (I →ₗ[R] R) ≃ₗ[R] (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) := by
  -- TODO: prove using `mem_inv_iff`, finite generation, and clearing denominators.
  -- The intended construction sends a multiplier `q ∈ I⁻¹` to the map `x ↦ q * x`.
  -- Conversely, for an `R`-linear map `f`, pick a common denominator for a finite spanning
  -- set of `I` to recover the unique `q ∈ K` with `f x = q * x` for all `x`.
  sorry

/-!
Auxiliary lemmas needed for the dual/inverse identification. Each is stated in a reusable
generality and left as a `sorry` placeholder.
-/

noncomputable def fractionalIdeal_linearMap_mul_mem_inv
    (I : FractionalIdeal (R⁰) (FractionRing R)) {q : FractionRing R}
    (hq : q ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R))) :
    I →ₗ[R] R := by
  /- This should be `x ↦ q * x`, using `hq` to show the codomain is in `R`. -/
  sorry

lemma fractionalIdeal_linearMap_is_mul
    (I : FractionalIdeal (R⁰) (FractionRing R)) (f : I →ₗ[R] R) :
    ∃ q : FractionRing R,
      q ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) ∧
      ∀ x : I, algebraMap R (FractionRing R) (f x) = q * (x : FractionRing R) := by
  /- Clear denominators on a finite spanning set of `I` using
     `FractionalIdeal.exists_multiple_submodule_basis`, then define
     `q := f (s • x₀) / s` and check `mem_inv_iff`. -/
  sorry

lemma fractionalIdeal_mul_scalar_unique
    (I : FractionalIdeal (R⁰) (FractionRing R)) {q₁ q₂ : FractionRing R}
    (hq₁ : q₁ ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)))
    (hq₂ : q₂ ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)))
    (h : ∀ x : I, q₁ * x = q₂ * x) : q₁ = q₂ := by
  /- Use torsion-freeness of `I` as an `R`-submodule of a domain to cancel a nonzero element
     in `I`, or clear denominators using `hq₁`/`hq₂` and injectivity of `algebraMap`. -/
  sorry

lemma fractionalIdeal_mul_inv_le_one
    (I : FractionalIdeal (R⁰) (FractionRing R)) :
    (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I ≤
      (1 : FractionalIdeal (R⁰) (FractionRing R)) := by
  /- This follows directly from `mem_inv_iff`: every product `q*x` with `q ∈ I⁻¹`, `x ∈ I`
     lands in `R`, so the product ideal is contained in `1`. -/
  refine (FractionalIdeal.mul_le).2 ?_
  intro q hq x hx
  -- Membership in the inverse means products land in `1`.
  by_cases hI : (I : FractionalIdeal (R⁰) (FractionRing R)) = 0
  · -- If `I = 0`, then any `x ∈ I` is zero, so the product vanishes and is in `1`.
    have hx0 : x = 0 := by
      have hx' : (x : FractionRing R) ∈ (0 : FractionalIdeal (R⁰) (FractionRing R)) := by
        simpa [hI] using hx
      simpa using (FractionalIdeal.mem_zero_iff (S := (R⁰)) (P := FractionRing R)).1 hx'
    -- Now `q * x = 0`, and `0 ∈ 1`.
    simp [hx0, FractionalIdeal.mem_one_iff]
  · -- Otherwise use the `mem_inv_iff` characterization.
    have hqx := (FractionalIdeal.mem_inv_iff (I := I) hI).1 hq
    exact hqx x hx

lemma fractionalIdeal_mul_tensor_eval_one
    (I : FractionalIdeal (R⁰) (FractionRing R))
    (e : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) ⊗[R] I ≃ₗ[R] R)
    (t : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) ⊗[R] I)
    (ht : e t = 1)
    (hcanon : ∀ (q : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R))) (x : I),
      algebraMap R (FractionRing R) (e (TensorProduct.tmul (R := R) q x)) =
        (q : FractionRing R) * (x : FractionRing R)) :
    (1 : FractionRing R) ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I := by
  classical
  -- Show that `algebraMap R K (e t)` lands in the product ideal by tensor induction.
  have hEt : algebraMap R (FractionRing R) (e t) ∈
      (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I := by
    refine TensorProduct.induction_on t ?h0 ?hsimple ?hadd
    · -- Zero tensor maps to `0`.
      simpa [LinearEquiv.map_zero] using
        (FractionalIdeal.zero_mem (I := (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I))
    · intro q x
      -- Simple tensors map to products, which belong to the product ideal.
      have hq : (q : FractionRing R) ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) := q.property
      have hx : (x : FractionRing R) ∈ I := x.property
      have hmul : (q : FractionRing R) * (x : FractionRing R) ∈
          (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I :=
        FractionalIdeal.mul_mem_mul hq hx
      have hcanon' := hcanon q x
      -- Rewrite using the canonical pairing identity.
      simpa [hcanon'] using hmul
    · intro u v hu hv
      -- Closed under addition.
      have hsum : algebraMap R (FractionRing R) (e (u + v)) =
          algebraMap R (FractionRing R) (e u) + algebraMap R (FractionRing R) (e v) := by
        simp [map_add]
      -- Work in the underlying submodule to use `Submodule.add_mem`.
      change algebraMap R (FractionRing R) (e (u + v)) ∈
        ((I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I).val
      -- Coerce the hypotheses into the underlying submodule.
      have hhu := hu
      change algebraMap R (FractionRing R) (e u) ∈
          ((I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I).val at hhu
      have hhv := hv
      change algebraMap R (FractionRing R) (e v) ∈
          ((I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I).val at hhv
      have hmem : algebraMap R (FractionRing R) (e u) + algebraMap R (FractionRing R) (e v) ∈
          ((I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I).val :=
        Submodule.add_mem _ hhu hhv
      simpa [hsum] using hmem
  -- Use `ht : e t = 1` to finish.
  simpa [ht] using hEt

/-- Using the evaluation isomorphism, the inverse of an invertible fractional ideal multiplies
with it to `1`. -/
lemma fractionalIdeal_inv_mul (I : FractionalIdeal (R⁰) (FractionRing R))
    [Module.Invertible R I] : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I = 1 := by
  classical
  -- Transport the evaluation equivalence along the dual/inverse identification.
  let eDual : Module.Dual R I ≃ₗ[R]
      (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) :=
    fractionalIdeal_dualEquiv_inv (R := R) (I := I)
  let eval := Module.Invertible.linearEquiv (R := R) (M := I)
  let e : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) ⊗[R] I ≃ₗ[R] R :=
    (TensorProduct.congr (eDual.symm) (LinearEquiv.refl R I)) ≪≫ₗ eval
  -- Pull back `1 : R` along this equivalence to obtain a tensor witness.
  obtain ⟨t, ht⟩ := (LinearEquiv.surjective e) 1
  -- The pairing `e` coincides with multiplication on simple tensors.
  have hcanon : ∀ (q : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R))) (x : I),
      algebraMap R (FractionRing R) (e (TensorProduct.tmul (R := R) q x)) =
        (q : FractionRing R) * (x : FractionRing R) := by
    -- This follows from the definition of `e` as the multiplication pairing.
    sorry
  -- From `e t = 1`, deduce `1 ∈ (I⁻¹) * I`.
  have hmem : (1 : FractionRing R) ∈ (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I :=
    fractionalIdeal_mul_tensor_eval_one (I := I) (e := e) (t := t) ht hcanon
  -- And the product ideal is bounded above by `1`.
  have hle : (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I ≤ 1 :=
    fractionalIdeal_mul_inv_le_one (I := I)
  -- Membership of `1` gives the reverse inequality.
  have hge : (1 : FractionalIdeal (R⁰) (FractionRing R)) ≤
      (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I :=
    (FractionalIdeal.one_le (S := (R⁰)) (P := FractionRing R)
      (I := (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) * I)).2 hmem
  exact le_antisymm hle hge

/-/ If a fractional ideal `I` is invertible as an `R`-module, then it is a unit fractional
ideal. -/
theorem fractionalIdeal_moduleInvertible_implies_isUnit
    (I : FractionalIdeal (R⁰) K) [Module.Invertible R I] : IsUnit I := by
  classical
  -- First show that an invertible module cannot be the zero fractional ideal.
  have hne : I ≠ (0 : FractionalIdeal (R⁰) K) := by
    intro h0
    -- If `I = 0`, then the underlying module is subsingleton.
    have hsubI : Subsingleton I := by
      refine ⟨?_⟩
      intro x y
      cases x with
      | mk x hx =>
      cases y with
      | mk y hy =>
      -- Membership in the zero fractional ideal forces elements to vanish.
      have hx0 : x = 0 := by simpa [h0] using hx
      have hy0 : y = 0 := by simpa [h0] using hy
      ext
      simp [hx0, hy0]
    -- With a subsingleton domain, the evaluation equivalence would make `R` subsingleton.
    haveI := hsubI
    obtain ⟨x, hx⟩ := (Module.Invertible.linearEquiv (R := R) (M := I)).surjective 1
    have hx0 : x = 0 := Subsingleton.elim _ _
    have hzero : (1 : R) = 0 := by
      calc
        (1 : R) = (Module.Invertible.linearEquiv (R := R) (M := I)) x := hx.symm
        _ = (Module.Invertible.linearEquiv (R := R) (M := I)) 0 := by simp [hx0]
        _ = 0 := by simp
    exact one_ne_zero hzero
  -- TODO: construct the inverse fractional ideal from the module invertibility of `I`.
  -- This typically uses the dual module and clearing denominators.
  -- Identify the dual of `I` with its fractional inverse and use evaluation to get a witness.
  have hmul : I * (I⁻¹ : FractionalIdeal (R⁰) (FractionRing R)) = 1 := by
    -- Commutativity lets us reuse the lemma with factors swapped.
    simpa [mul_comm] using (fractionalIdeal_inv_mul (R := R) (I := I))
  -- Conclude `IsUnit I` from the cancellation criterion.
  exact (FractionalIdeal.mul_inv_cancel_iff_isUnit (I := I)).1 hmul

end ModuleInvertibleToFractionalIdealUnit


end Picard
