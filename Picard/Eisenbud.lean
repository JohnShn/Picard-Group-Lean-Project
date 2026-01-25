import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup

open scoped TensorProduct
open scoped nonZeroDivisors

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
