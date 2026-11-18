import WideE.HopfPointGroup
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The conjugation action and the cotangent space at the identity of an affine Hopf group. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Conjugation

variable {F H A B : Type*} [CommRing F] [CommRing H] [HopfAlgebra F H]
variable [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]

private def postcomposeHopfPoint (f : A →ₐ[F] B) :
    letI := hopfPointGroup (k := F) (H := H) (A := A)
    letI := hopfPointGroup (k := F) (H := H) (A := B)
    (H →ₐ[F] A) →* (H →ₐ[F] B) := by
  letI : Group (H →ₐ[F] A) := hopfPointGroup
  letI : Group (H →ₐ[F] B) := hopfPointGroup
  exact {
    toFun := fun p => f.comp p
    map_one' := hopfPointOne_postcompose f
    map_mul' := hopfPointMul_postcompose f }

private theorem tensorPoint_comp_includeLeft (p q : H →ₐ[F] A) :
    (tensorPoint p q).comp Algebra.TensorProduct.includeLeft = p :=
  AlgHom.ext fun _ => (tensorPoint_tmul p q _ 1).trans (by rw [map_one, mul_one])

private theorem tensorPoint_comp_includeRight (p q : H →ₐ[F] A) :
    (tensorPoint p q).comp Algebra.TensorProduct.includeRight = q :=
  AlgHom.ext fun _ => (tensorPoint_tmul p q 1 _).trans (by rw [map_one, one_mul])

/-- Pullback along the map `(p,q) ↦ p*q*p⁻¹` on affine group points. -/
def hopfConjugation (F H : Type*) [CommRing F] [CommRing H] [HopfAlgebra F H] :
    H →ₐ[F] H ⊗[F] H := by
  letI : Group (H →ₐ[F] H ⊗[F] H) := hopfPointGroup
  let l : H →ₐ[F] H ⊗[F] H := Algebra.TensorProduct.includeLeft
  let r : H →ₐ[F] H ⊗[F] H := Algebra.TensorProduct.includeRight
  exact l * r * l⁻¹

/-- Evaluation of the universal conjugation is conjugation of actual group points. -/
theorem hopfConjugation_eval (p q : H →ₐ[F] A) :
    letI := hopfPointGroup (k := F) (H := H) (A := A)
    (tensorPoint p q).comp (hopfConjugation F H) = p * q * p⁻¹ := by
  letI : Group (H →ₐ[F] A) := hopfPointGroup
  letI : Group (H →ₐ[F] H ⊗[F] H) := hopfPointGroup
  let f := postcomposeHopfPoint (H := H) (tensorPoint p q)
  let l : H →ₐ[F] H ⊗[F] H := Algebra.TensorProduct.includeLeft
  let r : H →ₐ[F] H ⊗[F] H := Algebra.TensorProduct.includeRight
  change f (l * r * l⁻¹) = _
  rw [map_mul f, map_mul f, map_inv f]
  change (tensorPoint p q).comp Algebra.TensorProduct.includeLeft *
    (tensorPoint p q).comp Algebra.TensorProduct.includeRight *
    ((tensorPoint p q).comp Algebra.TensorProduct.includeLeft)⁻¹ = _
  rw [tensorPoint_comp_includeLeft, tensorPoint_comp_includeRight]

/-- Conjugation fixes the identity in the second variable. -/
theorem hopfConjugation_identity (p : H →ₐ[F] A) :
    (tensorPoint p hopfPointOne).comp (hopfConjugation F H) = hopfPointOne := by
  letI : Group (H →ₐ[F] A) := hopfPointGroup
  change (tensorPoint p 1).comp (hopfConjugation F H) = 1
  rw [hopfConjugation_eval, mul_one, mul_inv_cancel]

/-- The identity acts trivially by conjugation. -/
theorem hopfConjugation_identity_action (p : H →ₐ[F] A) :
    (tensorPoint hopfPointOne p).comp (hopfConjugation F H) = p := by
  letI : Group (H →ₐ[F] A) := hopfPointGroup
  change (tensorPoint 1 p).comp (hopfConjugation F H) = p
  rw [hopfConjugation_eval, one_mul, inv_one, mul_one]

/-- Successive conjugation is conjugation by the product. -/
theorem hopfConjugation_coassoc (a : H) :
    Algebra.TensorProduct.assoc F H H H
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom F H) (AlgHom.id F H)
        (hopfConjugation F H a)) =
    Algebra.TensorProduct.map (AlgHom.id F H) (hopfConjugation F H) (hopfConjugation F H a) := by
  let S := H ⊗[F] H
  let T := H ⊗[F] S
  letI : Group (H →ₐ[F] T) := hopfPointGroup
  let p : H →ₐ[F] T := Algebra.TensorProduct.includeLeft
  let i : S →ₐ[F] T := Algebra.TensorProduct.includeRight
  let q := i.comp (Algebra.TensorProduct.includeLeft : H →ₐ[F] S)
  let r := i.comp (Algebra.TensorProduct.includeRight : H →ₐ[F] S)
  let φ : S →ₐ[F] T := (Algebra.TensorProduct.assoc F H H H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom F H) (AlgHom.id F H))
  let ψ : S →ₐ[F] T := Algebra.TensorProduct.map (AlgHom.id F H) (hopfConjugation F H)
  have hφ : φ = tensorPoint (p * q) r := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change Algebra.TensorProduct.assoc F H H H ((Bialgebra.comulAlgHom F H x) ⊗ₜ[F] y) = _
    rw [tensorPoint_tmul]
    change Algebra.TensorProduct.assoc F H H H ((Bialgebra.comulAlgHom F H x) ⊗ₜ[F] y) =
      tensorPoint p q (Bialgebra.comulAlgHom F H x) * r y
    generalize Bialgebra.comulAlgHom F H x = z
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero, zero_mul]
    | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, add_mul, ha, hb]
    | tmul a b =>
      rw [Algebra.TensorProduct.assoc_tmul, tensorPoint_tmul]
      change a ⊗ₜ[F] (b ⊗ₜ[F] y) =
        (a ⊗ₜ[F] (1 : H ⊗[F] H)) * ((1 : H) ⊗ₜ[F] (b ⊗ₜ[F] (1 : H))) * ((1 : H) ⊗ₜ[F] ((1 : H) ⊗ₜ[F] y))
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hI : i = tensorPoint q r := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [tensorPoint_tmul]
    change 1 ⊗ₜ[F] (x ⊗ₜ[F] y) =
      (1 ⊗ₜ[F] (x ⊗ₜ[F] (1 : H))) * (1 ⊗ₜ[F] ((1 : H) ⊗ₜ[F] y))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hψ : ψ = tensorPoint p (q * r * q⁻¹) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    change x ⊗ₜ[F] hopfConjugation F H y = tensorPoint p (q * r * q⁻¹) (x ⊗ₜ[F] y)
    rw [tensorPoint_tmul, ← hopfConjugation_eval q r, ← hI]
    change x ⊗ₜ[F] hopfConjugation F H y = (x ⊗ₜ[F] (1 : S)) * (1 ⊗ₜ[F] hopfConjugation F H y)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change (φ.comp (hopfConjugation F H)) a = (ψ.comp (hopfConjugation F H)) a
  rw [hφ, hψ, hopfConjugation_eval, hopfConjugation_eval]
  simp only [mul_inv_rev, mul_assoc]

end Conjugation

section Cotangent

variable (F H : Type*) [Field F] [CommRing H] [Bialgebra F H]

local notation "ε" => Bialgebra.counitAlgHom F H

/-- The ideal of the identity point. -/
abbrev hopfAugmentationIdeal : Ideal H := RingHom.ker (ε).toRingHom

/-- The cotangent space at the identity point. -/
abbrev HopfCotangent := (hopfAugmentationIdeal F H).Cotangent

/-- The differential at the identity, sending `a` to the class of `a-ε(a)`. -/
def hopfCotangentProjection : H →ₗ[F] HopfCotangent F H := by
  let I := hopfAugmentationIdeal F H
  let u := (Algebra.ofId F H).toLinearMap
  refine (I.toCotangent.restrictScalars F).comp
    ((LinearMap.id - u.comp (ε).toLinearMap).codRestrict (I.restrictScalars F) ?_)
  intro a
  change ε (a - algebraMap F H (ε a)) = 0
  rw [map_sub, (ε).commutes]
  exact sub_self _

/-- The cotangent projection is represented by the coordinate with its counit subtracted. -/
theorem hopfCotangentProjection_apply (a : H) :
    hopfCotangentProjection F H a = (hopfAugmentationIdeal F H).toCotangent
      ⟨a - algebraMap F H (ε a), by
        change ε (a - algebraMap F H (ε a)) = 0
        rw [map_sub, (ε).commutes]
        exact sub_self _⟩ := rfl

/-- Every cotangent vector is represented by an element of the coordinate algebra. -/
theorem hopfCotangentProjection_surjective : Function.Surjective (hopfCotangentProjection F H) := by
  intro x
  obtain ⟨a, rfl⟩ := (hopfAugmentationIdeal F H).toCotangent_surjective x
  have ha : ε (a : H) = 0 := a.property
  refine ⟨a, ?_⟩
  rw [hopfCotangentProjection_apply]
  congr 1
  apply Subtype.ext
  change (a : H) - algebraMap F H (ε a) = a
  rw [ha, map_zero, sub_zero]

@[simp] theorem hopfCotangentProjection_one : hopfCotangentProjection F H 1 = 0 := by
  rw [hopfCotangentProjection_apply, (hopfAugmentationIdeal F H).toCotangent_eq_zero]
  change (1 : H) - algebraMap F H (ε 1) ∈ _
  rw [map_one, map_one, sub_self]
  exact zero_mem _

/-- The cotangent projection is a derivation with respect to the identity point. -/
theorem hopfCotangentProjection_mul (a b : H) :
    hopfCotangentProjection F H (a * b) =
      ε a • hopfCotangentProjection F H b + ε b • hopfCotangentProjection F H a := by
  let I := hopfAugmentationIdeal F H
  let u := algebraMap F H
  let a₀ : I := ⟨a - u (ε a), by
    change ε (a - u (ε a)) = 0
    rw [map_sub, (ε).commutes]
    exact sub_self _⟩
  let b₀ : I := ⟨b - u (ε b), by
    change ε (b - u (ε b)) = 0
    rw [map_sub, (ε).commutes]
    exact sub_self _⟩
  rw [hopfCotangentProjection_apply, hopfCotangentProjection_apply, hopfCotangentProjection_apply]
  let q := I.toCotangent.restrictScalars F
  change q ⟨a * b - u (ε (a * b)), _⟩ = ε a • q b₀ + ε b • q a₀
  rw [← q.map_smul, ← q.map_smul, ← q.map_add]
  apply I.toCotangent_eq.mpr
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def]
  change a * b - u (ε (a * b)) - ((u (ε a)) * (b - u (ε b)) + (u (ε b)) * (a - u (ε a))) ∈ I ^ 2
  rw [map_mul ε, map_mul u, pow_two]
  convert Ideal.mul_mem_mul a₀.property b₀.property using 1
  ring

/-- Finite type of the coordinate algebra makes the cotangent space finite-dimensional. -/
theorem hopfCotangent_finiteDimensional [Algebra.FiniteType F H] :
    FiniteDimensional F (HopfCotangent F H) := by
  letI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing F H
  let C := HopfCotangent F H
  have hScalar (a : H) (x : C) : a • x = ε a • x := by
    have ha : a - algebraMap F H (ε a) ∈ hopfAugmentationIdeal F H := by
      change ε (a - algebraMap F H (ε a)) = 0
      simp
    rw [← sub_eq_zero, ← IsScalarTower.algebraMap_smul H (ε a), ← sub_smul]
    exact Ideal.Cotangent.smul_eq_zero_of_mem ha x
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (⊤ : Submodule H C)
  apply Module.finite_def.mpr
  refine ⟨s, eq_top_iff.mpr ?_⟩
  intro x hTop
  clear hTop
  have hx : x ∈ Submodule.span H (s : Set C) := hs.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y hx hy hx' hy' => exact add_mem hx' hy'
  | smul a x hx hx' => rw [hScalar]; exact Submodule.smul_mem _ _ hx'

end Cotangent

section CotangentCoaction

variable (F H : Type*) [Field F] [CommRing H] [HopfAlgebra F H]

local notation "ε" => Bialgebra.counitAlgHom F H
local notation "Δ" => Bialgebra.comulAlgHom F H
local notation "C" => HopfCotangent F H

private def projectSecond : H ⊗[F] H →ₗ[F] H ⊗[F] C :=
  (hopfCotangentProjection F H).lTensor H

private def counitSecond : H ⊗[F] H →ₐ[F] H :=
  tensorPoint (AlgHom.id F H) hopfPointOne

private theorem projectSecond_mul (x y : H ⊗[F] H) :
    projectSecond F H (x * y) =
      counitSecond F H x • projectSecond F H y + counitSecond F H y • projectSecond F H x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero, zero_smul, smul_zero, add_zero]
  | add x z hx hz =>
    simp only [add_mul, map_add, hx, hz, add_smul, smul_add, add_add_add_comm]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, zero_smul, smul_zero, add_zero]
    | add y z hy hz =>
      simp only [mul_add, map_add, hy, hz, add_smul, smul_add, add_add_add_comm]
    | tmul c d =>
      change projectSecond F H ((a ⊗ₜ[F] b) * (c ⊗ₜ[F] d)) =
        (a * algebraMap F H (ε b)) • (c ⊗ₜ[F] hopfCotangentProjection F H d) +
        (c * algebraMap F H (ε d)) • (a ⊗ₜ[F] hopfCotangentProjection F H b)
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      change (a * c) ⊗ₜ[F] hopfCotangentProjection F H (b * d) = _
      rw [hopfCotangentProjection_mul, TensorProduct.tmul_add,
        ← TensorProduct.smul_tmul (ε b) (a * c), ← TensorProduct.smul_tmul (ε d) (a * c),
        ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
      have hB : ε b • (a * c) = (a * algebraMap F H (ε b)) * c := by
        rw [Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap F H (ε b)) a]
      have hD : ε d • (a * c) = (c * algebraMap F H (ε d)) * a := by
        rw [Algebra.smul_def, mul_comm a c, ← mul_assoc, mul_comm (algebraMap F H (ε d)) c]
      exact congrArg₂ (fun u v : H => (u ⊗ₜ[F] hopfCotangentProjection F H d) +
        (v ⊗ₜ[F] hopfCotangentProjection F H b)) hB hD

private def conjugationDifferential : H →ₗ[F] H ⊗[F] C :=
  (projectSecond F H).comp (hopfConjugation F H).toLinearMap

private theorem conjugationDifferential_mul (x y : H) :
    conjugationDifferential F H (x * y) =
      ε x • conjugationDifferential F H y + ε y • conjugationDifferential F H x := by
  have h (a : H) : counitSecond F H (hopfConjugation F H a) = algebraMap F H (ε a) :=
    DFunLike.congr_fun (hopfConjugation_identity (AlgHom.id F H)) a
  change projectSecond F H (hopfConjugation F H (x * y)) = _
  rw [map_mul, projectSecond_mul, h, h]
  exact congrArg₂ (· + ·) (IsScalarTower.algebraMap_smul H _ _) (IsScalarTower.algebraMap_smul H _ _)

private theorem conjugationDifferential_scalar (c : F) :
    conjugationDifferential F H (algebraMap F H c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  have hOne : conjugationDifferential F H 1 = 0 := by
    change projectSecond F H (hopfConjugation F H 1) = 0
    rw [map_one]
    change (1 : H) ⊗ₜ[F] hopfCotangentProjection F H 1 = 0
    rw [hopfCotangentProjection_one, TensorProduct.tmul_zero]
  rw [hOne, smul_zero]

/-- The pullback of conjugation differentiated in its second variable. -/
def hopfCotangentCoaction : C →ₗ[F] H ⊗[F] C := by
  let I := hopfAugmentationIdeal F H
  let W := I • (⊤ : Submodule H I)
  let D := conjugationDifferential F H
  refine (W.restrictScalars F).liftQ (D.comp (I.restrictScalars F).subtype) ?_
  intro v hv
  change v ∈ W at hv
  change D v = 0
  refine Submodule.smul_induction_on (p := fun w : I => D w = 0) hv ?_ ?_
  · intro a ha b _
    have hA : ε a = 0 := ha
    have hB : ε (b : H) = 0 := b.property
    change D (a * b) = 0
    dsimp only [D]
    rw [conjugationDifferential_mul, hA, hB, zero_smul, zero_smul, add_zero]
  · intro x y hx hy
    change D ((x : H) + (y : H)) = 0
    rw [map_add, hx, hy, add_zero]

/-- On an element of the coordinate ring, the coaction is the differential
of the actual conjugation pullback. -/
theorem hopfCotangentCoaction_proj (a : H) :
    hopfCotangentCoaction F H (hopfCotangentProjection F H a) =
      projectSecond F H (hopfConjugation F H a) := by
  rw [hopfCotangentProjection_apply]
  change conjugationDifferential F H (a - algebraMap F H (ε a)) = conjugationDifferential F H a
  rw [map_sub, conjugationDifferential_scalar, sub_zero]

private def cotangentCounit : H ⊗[F] C →ₗ[F] C :=
  (TensorProduct.lid F C).toLinearMap.comp ((ε).toLinearMap.rTensor C)

/-- The identity acts trivially on the cotangent space. -/
theorem hopfCotangentCoaction_counit (x : C) :
    cotangentCounit F H (hopfCotangentCoaction F H x) = x := by
  obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective F H x
  rw [hopfCotangentCoaction_proj]
  have h (z : H ⊗[F] H) : cotangentCounit F H (projectSecond F H z) =
      hopfCotangentProjection F H (tensorPoint (hopfPointOne : H →ₐ[F] H) (AlgHom.id F H) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      change ε x • hopfCotangentProjection F H y =
        hopfCotangentProjection F H ((algebraMap F H (ε x)) * y)
      rw [← Algebra.smul_def, map_smul]
  rw [h]
  exact congrArg (hopfCotangentProjection F H)
    (DFunLike.congr_fun (hopfConjugation_identity_action (AlgHom.id F H)) a)

/-- The comultiplication law for the coaction on the cotangent space. -/
theorem hopfCotangentCoaction_coassoc (x : C) :
    TensorProduct.assoc F H H C ((Δ).toLinearMap.rTensor C (hopfCotangentCoaction F H x)) =
      (hopfCotangentCoaction F H).lTensor H (hopfCotangentCoaction F H x) := by
  obtain ⟨a, rfl⟩ := hopfCotangentProjection_surjective F H x
  rw [hopfCotangentCoaction_proj]
  have hLeft (z : H ⊗[F] H) :
      TensorProduct.assoc F H H C ((Δ).toLinearMap.rTensor C (projectSecond F H z)) =
        (projectSecond F H).lTensor H
          (Algebra.TensorProduct.assoc F H H H
            (Algebra.TensorProduct.map Δ (AlgHom.id F H) z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul u v =>
      change TensorProduct.assoc F H H C ((Δ u) ⊗ₜ[F] hopfCotangentProjection F H v) =
        (projectSecond F H).lTensor H (Algebra.TensorProduct.assoc F H H H ((Δ u) ⊗ₜ[F] v))
      generalize Δ u = w
      induction w using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul u₁ u₂ => rfl
  have hRight (z : H ⊗[F] H) :
      (hopfCotangentCoaction F H).lTensor H (projectSecond F H z) =
        (projectSecond F H).lTensor H
          (Algebra.TensorProduct.map (AlgHom.id F H) (hopfConjugation F H) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      change x ⊗ₜ[F] hopfCotangentCoaction F H (hopfCotangentProjection F H y) =
        x ⊗ₜ[F] projectSecond F H (hopfConjugation F H y)
      rw [hopfCotangentCoaction_proj]
  rw [hLeft, hRight, hopfConjugation_coassoc]

end CotangentCoaction

section AdjointMatrix

open scoped Matrix

variable {F H ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H]
variable [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H
local notation "Δ" => Bialgebra.comulAlgHom F H
local notation "ε" => Bialgebra.counitAlgHom F H

/-- The matrix of the adjoint action in the coordinates dual to a cotangent basis. -/
def hopfAdjointMatrix (b : Basis ι F C) : Matrix ι ι H :=
  fun i j => (b.baseChange H).repr (hopfCotangentCoaction F H (b i)) j

omit [DecidableEq ι] in
private theorem coaction_basis (b : Basis ι F C) (i : ι) :
    hopfCotangentCoaction F H (b i) = ∑ j, hopfAdjointMatrix b i j ⊗ₜ[F] b j := by
  calc
    hopfCotangentCoaction F H (b i) = ∑ j, hopfAdjointMatrix b i j • b.baseChange H j :=
      ((b.baseChange H).sum_repr (hopfCotangentCoaction F H (b i))).symm
    _ = ∑ j, hopfAdjointMatrix b i j ⊗ₜ[F] b j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Basis.baseChange_apply]
      let h := hopfAdjointMatrix b i j
      exact (TensorProduct.smul_tmul' h (1 : H) (b j)).symm.trans
        (congrArg (fun a => a ⊗ₜ[F] b j) (mul_one h))

private theorem baseChange_repr_sum_tmul {A : Type*} [CommRing A] [Algebra F A]
    (b : Basis ι F C) (x : ι → A) (j : ι) :
    (b.baseChange A).repr (∑ l, x l ⊗ₜ[F] b l) j = x j := by
  change (b.baseChange A).coord j (∑ l, x l ⊗ₜ[F] b l) = x j
  rw [map_sum]
  simp only [Basis.coord_apply, Basis.baseChange_repr_tmul, Basis.repr_self,
    Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Comultiplication is matrix multiplication on adjoint coefficients. -/
theorem hopfAdjointMatrix_comul (b : Basis ι F C) (i j : ι) :
    Coalgebra.comul (R := F) (hopfAdjointMatrix b i j) =
      ∑ l, hopfAdjointMatrix b i l ⊗ₜ[F] hopfAdjointMatrix b l j := by
  let U := hopfAdjointMatrix b
  let B := hopfCotangentCoaction F H
  let a := TensorProduct.assoc F H H C
  have hL : (Δ).toLinearMap.rTensor C (B (b i)) = ∑ l, Δ (U i l) ⊗ₜ[F] b l := by
    change (Δ).toLinearMap.rTensor C (hopfCotangentCoaction F H (b i)) = _
    rw [coaction_basis]
    simp only [map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, U]
  have hR : B.lTensor H (B (b i)) = a (∑ k, (∑ l, U i l ⊗ₜ[F] U l k) ⊗ₜ[F] b k) := by
    calc
      B.lTensor H (B (b i)) = ∑ l, U i l ⊗ₜ[F] B (b l) := by
        change B.lTensor H (hopfCotangentCoaction F H (b i)) = _
        rw [coaction_basis]
        simp only [map_sum, LinearMap.lTensor_tmul, U]
      _ = a (∑ k, (∑ l, U i l ⊗ₜ[F] U l k) ⊗ₜ[F] b k) := by
        simp only [a, B, U, coaction_basis, TensorProduct.tmul_sum, TensorProduct.sum_tmul,
          map_sum, TensorProduct.assoc_tmul]
        rw [Finset.sum_comm]
  have h : a ((Δ).toLinearMap.rTensor C (B (b i))) = B.lTensor H (B (b i)) :=
    hopfCotangentCoaction_coassoc F H (b i)
  rw [hL, hR] at h
  have h' := congrArg (fun z => (b.baseChange (H ⊗[F] H)).repr z j) (a.injective h)
  simpa only [baseChange_repr_sum_tmul, U] using h'

/-- The identity has the identity adjoint matrix. -/
theorem hopfAdjointMatrix_counit (b : Basis ι F C) (i j : ι) :
    Coalgebra.counit (R := F) (hopfAdjointMatrix b i j) = if i = j then 1 else 0 := by
  let U := hopfAdjointMatrix b
  have h := hopfCotangentCoaction_counit F H (b i)
  rw [coaction_basis, map_sum] at h
  change ∑ l, ε (U i l) • b l = b i at h
  have h' := congrArg (b.coord j) h
  change (b.coord j) (∑ l, ε (U i l) • b l) = (b.coord j) (b i) at h'
  rw [map_sum] at h'
  simp only [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at h'
  exact h'

/-- The adjoint matrix is invertible, with inverse obtained by the antipode. -/
def hopfAdjointMatrixUnit (b : Basis ι F C) : (Matrix ι ι H)ˣ where
  val := hopfAdjointMatrix b
  inv := (hopfAdjointMatrix b).map (hopfAntipodeAlgHom F H)
  val_inv := by
    apply Matrix.ext
    intro i j
    let U := hopfAdjointMatrix b
    have h := HopfAlgebra.mul_antipode_lTensor_comul_apply (R := F) (U i j)
    rw [hopfAdjointMatrix_comul] at h
    simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.mul'_apply, LinearMap.id_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, hopfAntipodeAlgHom_apply]
    rw [h, hopfAdjointMatrix_counit, Matrix.one_apply]
    simp only [apply_ite, map_zero, map_one]
    split_ifs <;> rfl
  inv_val := by
    apply Matrix.ext
    intro i j
    let U := hopfAdjointMatrix b
    have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := F) (U i j)
    rw [hopfAdjointMatrix_comul] at h
    simp only [map_sum, LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.id_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, hopfAntipodeAlgHom_apply]
    rw [h, hopfAdjointMatrix_counit, Matrix.one_apply]
    simp only [apply_ite, map_zero, map_one]
    split_ifs <;> rfl

end AdjointMatrix

section TangentAction

open scoped Matrix

variable {F H A ι : Type*} [Field F] [CommRing H] [HopfAlgebra F H]
variable [CommRing A] [Algebra F A] [Fintype ι] [DecidableEq ι]

local notation "C" => HopfCotangent F H

/-- An algebra-valued tangent vector at the identity, dual to the cotangent space. -/
abbrev HopfLieVector (F H A : Type*) [Field F] [CommRing H] [Bialgebra F H]
    [CommRing A] [Algebra F A] := HopfCotangent F H →ₗ[F] A

/-- The adjoint action of a point on a Lie vector. -/
def hopfAdjoint (p : H →ₐ[F] A) (x : HopfLieVector F H A) : HopfLieVector F H A :=
  ((LinearMap.mul' F A).comp (TensorProduct.map p.toLinearMap x)).comp (hopfCotangentCoaction F H)

omit [DecidableEq ι] in
/-- The coordinate action of the adjoint matrix agrees with actual conjugation on tangent vectors. -/
theorem hopfAdjoint_apply_basis (b : Basis ι F C) (p : H →ₐ[F] A) (x : HopfLieVector F H A) :
    (fun i => hopfAdjoint p x (b i)) = (hopfAdjointMatrix b).map p *ᵥ (fun i => x (b i)) := by
  funext i
  change (LinearMap.mul' F A) (TensorProduct.map p.toLinearMap x (hopfCotangentCoaction F H (b i))) = _
  rw [coaction_basis]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply]

end TangentAction

end WideE
