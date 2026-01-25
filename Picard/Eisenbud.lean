import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup

open scoped TensorProduct
open scoped nonZeroDivisors

-- Silence the `unnecessarySimpa` linter in this exploratory file.
set_option linter.unnecessarySimpa false

/-!
## Picard group vs. ideal class group

This project’s first goal is to formalize (at least the statement of) the classical result that,
for a commutative domain, the Picard group is (canonically) isomorphic to the ideal class group.
-/

namespace Eisenbud


variable {R : Type*} [CommRing R] [IsDomain R]
variable {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (I : Type*) [AddCommGroup I] [Module R I]

-- Aux instances: the carrier of a fractional ideal inherits the natural module structure.
instance fractionalIdeal_carrier_addCommMonoid
  {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (I : FractionalIdeal (nonZeroDivisors R) K) :
    AddCommMonoid ↥I := by
  -- The carrier of a fractional ideal is the carrier of its underlying submodule.
  change AddCommMonoid ↥(FractionalIdeal.coeToSubmodule I)
  infer_instance

instance fractionalIdeal_carrier_module
  {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (I : FractionalIdeal (nonZeroDivisors R) K) :
    Module R ↥I := by
  -- The carrier of a fractional ideal inherits the module structure of the underlying submodule.
  change Module R ↥(FractionalIdeal.coeToSubmodule I)
  infer_instance


/-! ### Theorem 11.6 -/

/-! ### Corollary 11.7 -/

-- The product of fractional ideals is isomorphic to their tensor product as modules.
noncomputable def fractionalIdeal_mul_linear
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal (nonZeroDivisors R) K) :
  I ⊗[R] J →ₗ[R] (I * J : FractionalIdeal (nonZeroDivisors R) K) := by
  classical
  -- Build the bilinear map `(a,b) ↦ a*b` and lift it to the tensor product.
  refine TensorProduct.lift ?mulMap
  refine
    { toFun := fun a =>
        { toFun := fun b =>
            ⟨a.1 * b.1, FractionalIdeal.mul_mem_mul a.property b.property⟩
          , map_add' := by
              intro b c; ext; simp [mul_add]
                , map_smul' := by
                  intro r b; ext; simp [Algebra.smul_def, mul_comm, mul_assoc] }
      , map_add' := by
          intro a a'; ext b; simp [add_mul]
      , map_smul' := by
          intro r a; ext b
          simp [LinearMap.smul_apply, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] }

@[simp]
lemma fractionalIdeal_mul_linear_tmul
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal (nonZeroDivisors R) K) (a : I) (b : J) :
    fractionalIdeal_mul_linear (R := R) (K := K) I J
      (TensorProduct.tmul (R := R) (M := I) (N := J) a b) =
      ⟨a.1 * b.1, FractionalIdeal.mul_mem_mul a.property b.property⟩ := by
  classical
  -- By construction the lifted map sends pure tensors to the product.
  -- `TensorProduct.lift` evaluates to the defining bilinear map on pure tensors.
  rfl

lemma fractionalIdeal_mul_linear_surjective
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal (nonZeroDivisors R) K) :
    Function.Surjective (fractionalIdeal_mul_linear (R := R) (K := K) I J) := by
  classical
  intro x
  -- Let `L` be the multiplication map; show every element of `I*J` is in its range.
  let L := fractionalIdeal_mul_linear (R := R) (K := K) I J
  have hmem : ∃ t, (L t : K) = x := by
    -- `mul_induction_on` with predicate “`r` lies in the image of `L` (on the underlying field).”
    refine FractionalIdeal.mul_induction_on (S := (nonZeroDivisors R))
      (r := (x : K)) (C := fun r : K => ∃ t, (L t : K) = r)
      (hr := x.property) ?hm ?ha
    · intro i hi j hj
      let t := TensorProduct.tmul (R := R) (M := I) (N := J) ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨t, ?_⟩
      -- The lifted map sends pure tensors to products.
      change (L t).1 = i * j
      -- Evaluate directly with the tmul lemma.
      simp [L, fractionalIdeal_mul_linear_tmul, t]
    · intro y z hy hz
      rcases hy with ⟨ty, hty⟩
      rcases hz with ⟨tz, htz⟩
      refine ⟨ty + tz, ?_⟩
      -- Linearity of `L`.
      calc
        (L (ty + tz) : K) = (L ty : K) + (L tz : K) := by
          simp [LinearMap.map_add]
        _ = y + z := by
          -- `hty` and `htz` identify the images with `y` and `z`.
          simp [hty, htz]
  rcases hmem with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  -- Equality in the subtype follows from equality of underlying field elements.
  apply Subtype.ext
  simpa using ht

/-!
Injectivity of the multiplication map in the local case.

Suppose `R` is a local domain with fraction field `K`, and `I, J` are invertible fractional
ideals. The natural map `I ⊗[R] J →ₗ[R] I * J` is injective. The classical argument is:

- Localize at a prime to reduce injectivity to the local case.
- Over a local domain, invertible fractional ideals are free of rank `1`, generated by
  nonzerodivisors `s ∈ I`, `t ∈ J`.
- The composite `R ≃ R ⊗[R] R → I ⊗[R] J → I * J ⊆ K` is multiplication by `s * t`, a
  nonzerodivisor, hence injective; this identifies the tensor map on pure tensors.

We record this lemma as a placeholder; the detailed proof will follow this outline.
-/
/-!
Auxiliary: over a local domain, invertible fractional ideals are free of rank `1`.

This is left as a placeholder; it should be proven by the usual argument that an invertible
ideal over a local ring is principal, generated by a nonzerodivisor, hence free of rank `1`.
-/
lemma invertible_fractionalIdeal_free_rank_one
    {R K : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    Nonempty ((↥(↑I : FractionalIdeal (nonZeroDivisors R) K)) ≃ₗ[R] R) := by
  classical
  -- TODO: fill in the local/principal argument showing invertible fractional ideals are free.
  sorry

/-- Injectivity of the multiplication map in the local case: if `R` is local and `I, J` are
invertible fractional ideals, then `I ⊗[R] J → I * J` is injective. -/
lemma fractionalIdeal_mul_linear_injective_local
    {R K : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    Function.Injective
      (fractionalIdeal_mul_linear (R := R) (K := K)
        (I := (↑I : FractionalIdeal (nonZeroDivisors R) K))
        (J := (↑J : FractionalIdeal (nonZeroDivisors R) K))) := by
  classical
  -- Choose explicit linear equivalences to `R` witnessing free rank `1`.
  obtain ⟨eI⟩ := invertible_fractionalIdeal_free_rank_one (R := R) (K := K) I
  obtain ⟨eJ⟩ := invertible_fractionalIdeal_free_rank_one (R := R) (K := K) J
  -- The product ideal is also a unit, hence free of rank `1`.
  have hIJ : Nonempty ((↥(((↑I : FractionalIdeal (nonZeroDivisors R) K) *
        (↑J : FractionalIdeal (nonZeroDivisors R) K)) :
        FractionalIdeal (nonZeroDivisors R) K)) ≃ₗ[R] R) :=
    invertible_fractionalIdeal_free_rank_one (R := R) (K := K) (I := I * J)
  obtain ⟨eIJ⟩ := hIJ
  -- The comparison isomorphism `R ≃ I ⊗ J` built from the chosen bases.
  -- First `R ≃ R ⊗ R`, then transport along the chosen equivalences of `I` and `J` with `R`.
  let iso : R ≃ₗ[R]
      (↥(↑I : FractionalIdeal (nonZeroDivisors R) K) ⊗[R]
        ↥(↑J : FractionalIdeal (nonZeroDivisors R) K)) :=
    (TensorProduct.lid R R).symm.trans (TensorProduct.congr (eI.symm) (eJ.symm))
  -- The composite map `f : R → R` obtained by conjugating the multiplication map.
  let L := fractionalIdeal_mul_linear (R := R) (K := K)
      (I := (↑I : FractionalIdeal (nonZeroDivisors R) K))
      (J := (↑J : FractionalIdeal (nonZeroDivisors R) K))
  let f : R →ₗ[R] R := eIJ.toLinearMap ∘ₗ L ∘ₗ iso.toLinearMap
  -- Compute `f 1`; it is nonzero because it is the image of a product of nonzero vectors in `K`.
  have hf_one_ne : f 1 ≠ (0 : R) := by
    -- The chosen equivalences send `1` to nonzero vectors (otherwise `1 = 0`).
    have hI_ne : eI.symm 1 ≠ (0 : ↥(↑I : FractionalIdeal (nonZeroDivisors R) K)) := by
      intro h
      -- If `eI.symm 1 = 0`, applying `eI` forces `1 = 0`, contradiction in a domain.
      have h' := congrArg eI h
      have h1 : (1 : R) = 0 := by simpa using h'
      exact one_ne_zero h1
    have hJ_ne : eJ.symm 1 ≠ (0 : ↥(↑J : FractionalIdeal (nonZeroDivisors R) K)) := by
      intro h
      have h' := congrArg eJ h
      have h1 : (1 : R) = 0 := by simpa using h'
      exact one_ne_zero h1
    -- The underlying element of `K` given by the product of these vectors is nonzero.
    have hprod_ne : ((L (TensorProduct.tmul (R := R) (eI.symm 1) (eJ.symm 1))) : K) ≠ 0 := by
      have hx : ((eI.symm 1 : ↥(↑I : FractionalIdeal (nonZeroDivisors R) K)) : K) ≠ 0 := by
        intro hx0
        refine hI_ne ?_
        ext; simpa using hx0
      have hy : ((eJ.symm 1 : ↥(↑J : FractionalIdeal (nonZeroDivisors R) K)) : K) ≠ 0 := by
        intro hy0
        refine hJ_ne ?_
        ext; simpa using hy0
      -- The multiplication map on pure tensors is just multiplication in `K`.
      simpa [L, fractionalIdeal_mul_linear_tmul] using mul_ne_zero hx hy
    -- If `f 1 = 0`, injectivity of `eIJ` would force that product to be zero.
    intro hzero
    have hzero' : L (TensorProduct.tmul (R := R) (eI.symm 1) (eJ.symm 1)) = 0 := by
      apply eIJ.injective
      simpa [f, iso, L, LinearMap.comp_apply] using hzero
    exact hprod_ne (by
      -- underlying field element vanishes
      have := congrArg Subtype.val hzero'
      simpa using this)
  -- Any `R`-linear map `R →ₗ[R] R` is multiplication by `f 1`; nonvanishing of `f 1`
  -- implies injectivity.
  have hf_injective : Function.Injective f := by
    intro r s hrs
    -- `f` is determined by its value on `1`; `f r = r * f 1`.
    have hscale : ∀ t : R, f t = t * f 1 := by
      intro t
      calc
        f t = f (t • (1 : R)) := by simp
        _ = t • f 1 := by
          simpa using (f.map_smulₛₗ t (1 : R))
        _ = t * f 1 := by simp
    have hzero : f (r - s) = 0 := by
      -- Turn `f r = f s` into `f (r - s) = 0` using linearity.
      have h' : f r - f s = (0 : R) := by
        simpa using congrArg (fun x => x - f s) hrs
      simpa [LinearMap.map_sub] using h'
    have hmul : (r - s) * f 1 = 0 := by
      -- Rewrite via the scalar description.
      simpa [hscale (r - s)] using hzero
    have hsub : r - s = 0 := (mul_eq_zero.mp hmul).resolve_right hf_one_ne
    exact sub_eq_zero.mp hsub
  -- Identify `L` as `eIJ.symm ∘ f ∘ iso.symm`; compositions with equivalences preserve injective.
  have hL_inj : Function.Injective L := by
    -- Conjugate `L` by the equivalences `iso` and `eIJ`; injectivity is preserved.
    have h_eq : (fun x => eIJ.symm (f (iso.symm x))) = L := by
      funext x
      have hArg : L (iso (iso.symm x)) = L x := by
        simpa using congrArg L (iso.apply_symm_apply x)
      unfold f
      -- After unfolding, both sides reduce to `L (iso (iso.symm x))`; rewrite with `hArg`.
      simpa [LinearMap.comp_apply, L, hArg]
    have h_conj : Function.Injective (fun x => eIJ.symm (f (iso.symm x))) :=
      eIJ.symm.injective.comp (hf_injective.comp iso.symm.injective)
    simpa [h_eq] using h_conj
  exact hL_inj

-- TODO: show the multiplication map is an equivalence by proving injectivity.
lemma fractionalIdeal_tensor_equiv_mul
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    Nonempty ((↥(↑I : FractionalIdeal (nonZeroDivisors R) K) ⊗[R]
        ↥(↑J : FractionalIdeal (nonZeroDivisors R) K)) ≃ₗ[R]
      ((↑I : FractionalIdeal (nonZeroDivisors R) K) *
        (↑J : FractionalIdeal (nonZeroDivisors R) K) :
        FractionalIdeal (nonZeroDivisors R) K)) := by
  classical
  -- Surjectivity from the previously proved lemma.
  have hsurj :=
    fractionalIdeal_mul_linear_surjective (R := R) (K := K)
      (I := (↑I : FractionalIdeal (nonZeroDivisors R) K))
      (J := (↑J : FractionalIdeal (nonZeroDivisors R) K))
  -- Injectivity to be supplied.
  -- TODO: prove injectivity for units and use `LinearEquiv.ofBijective`.
  have hinj : Function.Injective
      (fractionalIdeal_mul_linear (R := R) (K := K)
        (↑I : FractionalIdeal (nonZeroDivisors R) K)
        (↑J : FractionalIdeal (nonZeroDivisors R) K)) := by
    -- The map is injective after localizing at every prime `p` of `R`,
    -- by `fractionalIdeal_mul_linear_injective_local`; hence it is injective globally.
    -- (The localization argument is packaged in the cited lemma.)
    sorry
  exact ⟨LinearEquiv.ofBijective
    (fractionalIdeal_mul_linear (R := R) (K := K)
      (↑I : FractionalIdeal (nonZeroDivisors R) K)
      (↑J : FractionalIdeal (nonZeroDivisors R) K)) ⟨hinj, hsurj⟩⟩

-- Placeholder: the unit fractional ideal is (linearly) the same as `R`.
-- We'll fill this in later; for now we leave it as a `sorry` so that we can
-- thread the invertibility argument for a gi   ven fractional ideal.
-- The carrier of the unit fractional ideal is linearly equivalent to `R`.
noncomputable def fractionalIdeal_one_equiv_R
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    ↥(↑(1 : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) ≃ₗ[R] R := by
  classical
  -- Forward map: include `R` into the unit fractional ideal via `algebraMap`.
  let f : R →ₗ[R] ↥(↑(1 : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) :=
    { toFun := fun r =>
        ⟨algebraMap R K r, by
          change algebraMap R K r ∈ (1 : FractionalIdeal (nonZeroDivisors R) K)
          simpa using
            (FractionalIdeal.mem_one_iff (S := (nonZeroDivisors R)) (P := K)).2 ⟨r, rfl⟩⟩
      map_add' := by
        intro r s; ext; simp
      map_smul' := by
        intro r s; ext; simp [Algebra.smul_def] }
  have hinj : Function.Injective f := by
    intro r s h
    -- `congrArg Subtype.val` collapses the subtype equality to the ambient field.
    apply (IsFractionRing.injective R K)
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro x
    rcases
        (FractionalIdeal.mem_one_iff (S := (nonZeroDivisors R)) (P := K)).1 x.property with
      ⟨r, hr⟩
    refine ⟨r, ?_⟩
    ext; simp [f, hr]
  -- `ofBijective` builds `R ≃ₗ[R] 1`; take the symmetric equivalence.
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm

noncomputable def cartierGroup_to_picardGroup
    (I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ) : CommRing.Pic R := by
  classical
  have _ : Module.Invertible R (↑I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
    -- Use the tensor-product description of the inverse fractional ideal.
    -- First, rewrite the product `I * I⁻¹` to `1` in the fractional ideal group.
    have hMul : ((↑I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) * (↑(I⁻¹)) :
        FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = 1 :=
      (Units.mul_inv I :
        (↑I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) *
          (↑(I⁻¹) : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = 1)
    -- The tensor–product equivalence landing in the product ideal.
    -- Work with named fractional ideals to avoid coercion clutter.
    set I' : FractionalIdeal (nonZeroDivisors R) (FractionRing R) := ↑I
    set J' : FractionalIdeal (nonZeroDivisors R) (FractionRing R) := ↑(I⁻¹)
    rcases fractionalIdeal_tensor_equiv_mul (R := R) (K := FractionRing R)
      (I := I) (J := I⁻¹) with ⟨eMul⟩
    -- Fix the carrier types explicitly to avoid coercion ambiguity.
    have eMul' :
        (↥(↑I' : Submodule R (FractionRing R)) ⊗[R]
          ↥(↑J' : Submodule R (FractionRing R))) ≃ₗ[R]
          ↥(I' * J' : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
      simpa [I', J'] using eMul
    -- Transport along the equality `I * I⁻¹ = 1` in the fractional ideal group.
    have hMul' := hMul
    change (I' * J' : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = 1 at hMul'
    have hMulSub : (↑(I' * J') : Submodule R (FractionRing R)) =
        (↑(1 : FractionalIdeal (nonZeroDivisors R) (FractionRing R))
          : Submodule R (FractionRing R)) := by
      simpa using congrArg FractionalIdeal.coeToSubmodule hMul'
    have eOne : (↥(↑I' : Submodule R (FractionRing R)) ⊗[R]
          ↥(↑J' : Submodule R (FractionRing R))) ≃ₗ[R]
        ↥(↑(1 : FractionalIdeal (nonZeroDivisors R) (FractionRing R))
          : Submodule R (FractionRing R)) :=
      eMul'.trans (LinearEquiv.ofEq _ _ hMulSub)
    -- Identify the unit fractional ideal with the base ring.
    have eR : (↥(↑I' : Submodule R (FractionRing R)) ⊗[R]
        ↥(↑J' : Submodule R (FractionRing R))) ≃ₗ[R] R :=
      eOne.trans (fractionalIdeal_one_equiv_R (R := R) (K := FractionRing R))
    -- An isomorphism `I ⊗ I⁻¹ ≃ R` makes `I` invertible as an `R`-module.
    -- `Module.Invertible.left` matches the direction we need.
    have hInv : Module.Invertible R (↑I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) :=
      Module.Invertible.left (R := R) (M := (↑I)) (N := (↑(I⁻¹))) eR
    exact hInv
  exact CommRing.Pic.mk R (↑I : FractionalIdeal (nonZeroDivisors R) (FractionRing R))

/-- The Picard group of a commutative domain is isomorphic to its ideal class group. -/
theorem picardGroup_equiv_classGroup (R : Type*) [CommRing R] [IsDomain R] :
 Nonempty (CommRing.Pic R ≃* ClassGroup R) := by
 sorry


end Eisenbud
