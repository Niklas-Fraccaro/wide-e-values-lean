import Mathlib.RingTheory.Flat.Equalizer

/-! Descent of a submodule of a scalar extension whose two pullbacks agree. -/

open scoped TensorProduct

noncomputable section

namespace WideE

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

section TensorSwap

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Exchange the two copies of the cover ring on the double overlap. -/
def swapDescentFactors : S ⊗[R] (S ⊗[R] M) ≃ₗ[R] S ⊗[R] (S ⊗[R] M) :=
  (TensorProduct.assoc R S S M).symm.trans
    (((TensorProduct.comm R S S).rTensor M).trans (TensorProduct.assoc R S S M))

@[simp] theorem swapDescentFactors_tmul (a b : S) (x : M) :
    swapDescentFactors R S M (a ⊗ₜ[R] (b ⊗ₜ[R] x)) = b ⊗ₜ[R] (a ⊗ₜ[R] x) := rfl

private theorem swapDescentFactors_one_tmul (x : S ⊗[R] M) :
    swapDescentFactors R S M ((1 : S) ⊗ₜ[R] x) =
      (TensorProduct.mk R S M (1 : S)).lTensor S x := by
  induction x with
  | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, LinearEquiv.map_add, hx, hy, LinearMap.map_add]
  | tmul a x => rfl

end TensorSwap

section SubmoduleDescent

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

local notation "A" => S ⊗[R] M
local notation "unitTensor" => TensorProduct.mk R S M (1 : S)

variable (N : Submodule S (S ⊗[R] M))

/-- The pullback of the submodule to the overlap, using the second copy of the cover. -/
def submoduleOnOverlap : Submodule R (S ⊗[R] A) :=
  LinearMap.range (((N.restrictScalars R).subtype).lTensor S)

/-- The submodule over the base obtained by taking the preimage under `x ↦ 1 ⊗ x`. -/
def descendedSubmodule : Submodule R M := (N.restrictScalars R).comap unitTensor

@[simp] theorem mem_descendedSubmodule (x : M) :
    x ∈ descendedSubmodule N ↔ ((1 : S) ⊗ₜ[R] x) ∈ N := Iff.rfl

/-- The scalar extension of the descended submodule maps into the original one. -/
def descendedSubmoduleMap : S ⊗[R] (descendedSubmodule N) →ₗ[S] N :=
  (TensorProduct.AlgebraTensorModule.lTensor S S (descendedSubmodule N).subtype).codRestrict N (by
    intro x
    induction x with
    | zero => rw [LinearMap.map_zero]; exact N.zero_mem
    | add x y hx hy => rw [LinearMap.map_add]; exact N.add_mem hx hy
    | tmul a x =>
      change (a ⊗ₜ[R] x.val) ∈ N
      have h := N.smul_mem a ((mem_descendedSubmodule N x.val).mp x.property)
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h)

@[simp] theorem descendedSubmoduleMap_tmul (a : S) (x : descendedSubmodule N) :
    ((descendedSubmoduleMap N (a ⊗ₜ[R] x)) : A) = a ⊗ₜ[R] x.val := rfl

private def submoduleRestrictionQuotient : M →ₗ[R] A ⧸ (N.restrictScalars R) :=
  ((N.restrictScalars R).mkQ).comp unitTensor

private theorem exact_submoduleRestrictionQuotient :
    Function.Exact (descendedSubmodule N).subtype (submoduleRestrictionQuotient N) := by
  intro x
  change (N.restrictScalars R).mkQ ((1 : S) ⊗ₜ[R] x) = 0 ↔
    x ∈ LinearMap.range (descendedSubmodule N).subtype
  rw [Submodule.range_subtype]
  change Submodule.Quotient.mk (p := N.restrictScalars R) ((1 : S) ⊗ₜ[R] x) = 0 ↔
    ((1 : S) ⊗ₜ[R] x) ∈ N.restrictScalars R
  exact Submodule.Quotient.mk_eq_zero (N.restrictScalars R)

variable [Module.Flat R S]

/-- If the two pullbacks of a submodule agree, extension of scalars from its
contraction recovers the original submodule. -/
def descendedSubmoduleEquiv
    (hStable : Set.MapsTo (swapDescentFactors R S M) (submoduleOnOverlap N) (submoduleOnOverlap N)) :
    S ⊗[R] (descendedSubmodule N) ≃ₗ[S] N := by
  refine LinearEquiv.ofBijective (descendedSubmoduleMap N) ⟨?_, ?_⟩
  · intro x y h
    exact (Module.Flat.lTensor_preserves_injective_linearMap (M := S) (descendedSubmodule N).subtype
      Subtype.val_injective) (congrArg Subtype.val h)
  · intro y
    let r : S ⊗[R] M := y.val
    let yR : N.restrictScalars R := ⟨r, y.property⟩
    have hOne : ((1 : S) ⊗ₜ[R] r) ∈ submoduleOnOverlap N := ⟨(1 : S) ⊗ₜ[R] yR, rfl⟩
    have hSwap : (unitTensor).lTensor S r ∈ submoduleOnOverlap N := by
      have h := hStable hOne
      rwa [swapDescentFactors_one_tmul] at h
    let NR := N.restrictScalars R
    have hquot : NR.mkQ.lTensor S ((unitTensor).lTensor S r) = 0 := by
      obtain ⟨a, ha⟩ := hSwap
      change NR.subtype.lTensor S a = (unitTensor).lTensor S r at ha
      rw [← ha, ← LinearMap.lTensor_comp_apply]
      have hcomp : NR.mkQ.comp NR.subtype = 0 := by
        apply LinearMap.ext
        intro x
        exact (Submodule.Quotient.mk_eq_zero NR).mpr x.property
      simp only [hcomp, LinearMap.lTensor_zero, LinearMap.zero_apply]
    have hzero : (submoduleRestrictionQuotient N).lTensor S r = 0 := by
      change ((N.restrictScalars R).mkQ.comp unitTensor).lTensor S r = 0
      rw [LinearMap.lTensor_comp_apply]
      exact hquot
    let f := submoduleRestrictionQuotient N
    have hker : LinearMap.ker f = descendedSubmodule N := by
      exact (LinearMap.exact_iff.mp (exact_submoduleRestrictionQuotient N)).trans (Submodule.range_subtype _)
    have hmem : r ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S f) := hzero
    rw [Module.Flat.ker_lTensor_eq S S f, hker] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, Subtype.ext hx⟩

@[simp] theorem descendedSubmoduleEquiv_tmul
    (hStable : Set.MapsTo (swapDescentFactors R S M) (submoduleOnOverlap N) (submoduleOnOverlap N))
    (a : S) (x : descendedSubmodule N) :
    ((descendedSubmoduleEquiv N hStable (a ⊗ₜ[R] x)) : A) = a ⊗ₜ[R] x.val := rfl

end SubmoduleDescent

section IdealDescent

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

local notation "T" => S ⊗[R] A
local notation "U" => S ⊗[R] (S ⊗[R] A)
local notation "includeBase" => (Algebra.TensorProduct.includeRight : A →ₐ[R] T)
local notation "secondPull" => (Algebra.TensorProduct.includeRight : T →ₐ[R] U)

/-- The other pullback of a base-changed algebra to the double overlap. -/
def scalarDescentFirstPull : T →ₐ[R] U :=
  Algebra.TensorProduct.map (AlgHom.id R S) includeBase

private def swapDescentAlgebra : U ≃ₐ[R] U :=
  (Algebra.TensorProduct.assoc R S S A).symm.trans
    ((Algebra.TensorProduct.congr (Algebra.TensorProduct.comm R S S) (AlgEquiv.refl : A ≃ₐ[R] A)).trans
      (Algebra.TensorProduct.assoc R S S A))

private theorem swapDescentAlgebra_apply (x : U) :
    swapDescentAlgebra R S A x = swapDescentFactors R S A x := rfl

private theorem swapDescentAlgebra_comp_secondPull :
    (swapDescentAlgebra R S A).toAlgHom.comp secondPull = scalarDescentFirstPull R S A :=
  Algebra.TensorProduct.ext' (fun _ _ => rfl)

variable {R S A} [Module.Flat R S]

/-- An ideal whose two pullbacks to the overlap agree is the scalar extension of
its contraction. This applies in particular to a stable homogeneous polynomial ideal. -/
theorem ideal_descends_of_equal_pulls (I : Ideal T)
    (hPull : I.map (scalarDescentFirstPull R S A) = I.map secondPull) :
    (I.comap includeBase).map includeBase = I := by
  let N : Submodule S T := I.restrictScalars S
  have hOverlap : submoduleOnOverlap N = (I.map secondPull).restrictScalars R :=
    (Ideal.map_includeRight_eq (R := R) (A := S) I).symm
  have hStable : Set.MapsTo (swapDescentFactors R S A) (submoduleOnOverlap N) (submoduleOnOverlap N) := by
    rw [hOverlap]
    intro x hx
    change x ∈ I.map secondPull at hx
    change swapDescentFactors R S A x ∈ I.map secondPull
    have h := Ideal.mem_map_of_mem (swapDescentAlgebra R S A).toAlgHom hx
    rw [Ideal.map_mapₐ] at h
    change swapDescentAlgebra R S A x ∈ I.map ((swapDescentAlgebra R S A).toAlgHom.comp secondPull) at h
    rw [swapDescentAlgebra_comp_secondPull, hPull, swapDescentAlgebra_apply] at h
    exact h
  refine le_antisymm Ideal.map_comap_le ?_
  intro x hx
  let e := descendedSubmoduleEquiv N hStable
  obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
  change x ∈ ((I.comap includeBase).map includeBase).restrictScalars R
  rw [Ideal.map_includeRight_eq]
  exact ⟨y, congrArg Subtype.val hy⟩

end IdealDescent

end WideE
