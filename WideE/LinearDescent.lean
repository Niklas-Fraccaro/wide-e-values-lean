import WideE.FiniteDescent
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! Effective linear descent for a matrix cocycle on an affine cover. -/

open scoped TensorProduct Matrix

set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 90000

noncomputable section

namespace WideE

section Overlaps

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

local notation "S₂" => S ⊗[R] S
local notation "S₃" => S ⊗[R] (S ⊗[R] S)

/-- Restriction along factors one and two of the triple overlap. -/
def linearDescent12 : S₂ →ₐ[R] S₃ :=
  (Algebra.TensorProduct.assoc R S S S).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : S₂ →ₐ[R] S₂ ⊗[R] S)

/-- Restriction along factors one and three of the triple overlap. -/
def linearDescent13 : S₂ →ₐ[R] S₃ :=
  Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.includeRight : S →ₐ[R] S₂)

/-- Restriction along factors two and three of the triple overlap. -/
def linearDescent23 : S₂ →ₐ[R] S₃ :=
  Algebra.TensorProduct.includeRight

@[simp] theorem linearDescent12_tmul (x y : S) :
    linearDescent12 R S (x ⊗ₜ[R] y) = x ⊗ₜ[R] (y ⊗ₜ[R] (1 : S)) := rfl

@[simp] theorem linearDescent13_tmul (x y : S) :
    linearDescent13 R S (x ⊗ₜ[R] y) = x ⊗ₜ[R] ((1 : S) ⊗ₜ[R] y) := rfl

@[simp] theorem linearDescent23_tmul (x y : S) :
    linearDescent23 R S (x ⊗ₜ[R] y) = (1 : S) ⊗ₜ[R] (x ⊗ₜ[R] y) := rfl

private def descentProduct : S₂ →ₐ[R] S :=
  Algebra.TensorProduct.lift (AlgHom.id R S) (AlgHom.id R S) (fun _ _ => Commute.all _ _)

private theorem descentProduct_tmul (a b : S) : descentProduct R S (a ⊗ₜ[R] b) = a * b := rfl

private def descentMerge : S₃ →ₐ[R] S₂ :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : S →ₐ[R] S₂)
    (AlgHom.id R S₂) (fun _ _ => Commute.all _ _)

private theorem descentMerge_tmul (a b c : S) :
    descentMerge R S (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = (a * b) ⊗ₜ[R] c := by
  simp only [descentMerge, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem descentMerge_12 (x : S₂) :
    descentMerge R S (linearDescent12 R S x) = descentProduct R S x ⊗ₜ[R] (1 : S) := by
  exact DFunLike.congr_fun (Algebra.TensorProduct.ext' (fun a b => by
    simp only [AlgHom.comp_apply, linearDescent12_tmul, descentMerge_tmul,
      descentProduct_tmul, Algebra.TensorProduct.includeLeft_apply]) :
    (descentMerge R S).comp (linearDescent12 R S) =
      Algebra.TensorProduct.includeLeft.comp (descentProduct R S)) x

private theorem descentMerge_13 (x : S₂) :
    descentMerge R S (linearDescent13 R S x) = x := by
  exact DFunLike.congr_fun (Algebra.TensorProduct.ext' (fun a b => by
    simp only [AlgHom.comp_apply, linearDescent13_tmul, descentMerge_tmul,
      mul_one, AlgHom.id_apply]) :
    (descentMerge R S).comp (linearDescent13 R S) = AlgHom.id R S₂) x

private theorem descentMerge_23 (x : S₂) :
    descentMerge R S (linearDescent23 R S x) = x := by
  exact DFunLike.congr_fun (Algebra.TensorProduct.ext' (fun a b => by
    simp only [AlgHom.comp_apply, linearDescent23_tmul, descentMerge_tmul,
      one_mul, AlgHom.id_apply]) :
    (descentMerge R S).comp (linearDescent23 R S) = AlgHom.id R S₂) x

end Overlaps

section MatrixDescent

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype ι] [DecidableEq ι]

local notation "S₂" => S ⊗[R] S
local notation "S₃" => S ⊗[R] (S ⊗[R] S)
local notation "ι₁" => (Algebra.TensorProduct.includeLeft : S →ₐ[R] S₂)
local notation "ι₂" => (Algebra.TensorProduct.includeRight : S →ₐ[R] S₂)

/-- A descent datum on a free module, written as an invertible matrix on the double overlap. -/
structure MatrixDescentDatum (R S ι : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Fintype ι] [DecidableEq ι] where
  matrix : (Matrix ι ι (S ⊗[R] S))ˣ
  cocycle : matrix.val.map (linearDescent13 R S).toRingHom =
    matrix.val.map (linearDescent12 R S).toRingHom * matrix.val.map (linearDescent23 R S).toRingHom

namespace MatrixDescentDatum

variable (U : MatrixDescentDatum R S ι)

private def left : (ι → S) →ₗ[R] (ι → S₂) := (ι₁).toLinearMap.compLeft ι

private def right : (ι → S) →ₗ[R] (ι → S₂) :=
  (U.matrix.val.mulVecLin.restrictScalars R).comp ((ι₂).toLinearMap.compLeft ι)

/-- The descended module consists of vectors agreeing on the double overlap. -/
def module : Submodule R (ι → S) :=
  LinearMap.eqLocus (left (R := R) (S := S) (ι := ι)) U.right

@[simp] theorem mem_module (x : ι → S) :
    x ∈ U.module ↔ (ι₁ ∘ x) = U.matrix.val *ᵥ (ι₂ ∘ x) := Iff.rfl

/-- The comparison is the scalar extension of the inclusion of descended vectors. -/
def comparison : S ⊗[R] U.module →ₗ[S] (ι → S) :=
  U.module.subtype.liftBaseChange S

@[simp] theorem comparison_tmul (a : S) (x : U.module) :
    U.comparison (a ⊗ₜ[R] x) = a • x.val := rfl

local notation "coordinates₂" => TensorProduct.piRight R S S (fun _ : ι => S)
local notation "coordinates₃" => TensorProduct.piRight R S S (fun _ : ι => S₂)
local notation "p₁₂" => linearDescent12 R S
local notation "p₁₃" => linearDescent13 R S
local notation "p₂₃" => linearDescent23 R S
local notation "prod₂" => descentProduct R S

private theorem coordinates₃_left (x : S ⊗[R] (ι → S)) :
    coordinates₃ (TensorProduct.AlgebraTensorModule.lTensor S S left x) =
      p₁₂ ∘ coordinates₂ x := by
  induction x with
  | zero =>
    simp only [LinearMap.map_zero, LinearEquiv.map_zero]
    funext i
    exact (map_zero p₁₂).symm
  | add x y hx hy =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy]
    funext i
    exact (map_add p₁₂ _ _).symm
  | tmul a x => rfl

private theorem coordinates₃_right (x : S ⊗[R] (ι → S)) :
    coordinates₃ (TensorProduct.AlgebraTensorModule.lTensor S S U.right x) =
      (U.matrix.val.map (p₂₃).toRingHom) *ᵥ (p₁₃ ∘ coordinates₂ x) := by
  induction x with
  | zero =>
    simp only [LinearMap.map_zero, LinearEquiv.map_zero, show p₁₃ ∘ (0 : ι → S₂) = 0 from funext fun _ => map_zero p₁₃,
      Matrix.mulVec_zero]
  | add x y hx hy =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy, ← Matrix.mulVec_add]
    have hcomp : (p₁₃ ∘ coordinates₂ x) + (p₁₃ ∘ coordinates₂ y) =
        p₁₃ ∘ (coordinates₂ x + coordinates₂ y) := by
      funext i
      exact ((p₁₃).map_add _ _).symm
    rw [hcomp]
  | tmul a x =>
    funext i
    change a ⊗ₜ[R] (U.matrix.val *ᵥ (ι₂ ∘ x)) i =
      ((U.matrix.val.map (p₂₃).toRingHom) *ᵥ (p₁₃ ∘ fun j => a ⊗ₜ[R] x j)) i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply,
      TensorProduct.tmul_sum, linearDescent13_tmul, linearDescent23]
    apply Finset.sum_congr rfl
    intro j _
    change a ⊗ₜ[R] (U.matrix.val i j * ((1 : S) ⊗ₜ[R] x j)) =
      ((1 : S) ⊗ₜ[R] U.matrix.val i j) * (a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] x j))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem overlap_diagonal : U.matrix.val.map (prod₂).toRingHom = 1 := by
  have h := congrArg (fun M : Matrix ι ι S₃ => M.map (descentMerge R S).toRingHom) U.cocycle
  change (U.matrix.val.map (p₁₃).toRingHom).map (descentMerge R S).toRingHom =
    ((U.matrix.val.map (p₁₂).toRingHom) * (U.matrix.val.map (p₂₃).toRingHom)).map
      (descentMerge R S).toRingHom at h
  rw [Matrix.map_mul] at h
  have h₁ : (U.matrix.val.map (p₁₃).toRingHom).map (descentMerge R S).toRingHom = U.matrix.val :=
    Matrix.ext (fun i j => descentMerge_13 R S _)
  have h₂ : (U.matrix.val.map (p₂₃).toRingHom).map (descentMerge R S).toRingHom = U.matrix.val :=
    Matrix.ext (fun i j => descentMerge_23 R S _)
  have h₃ : (U.matrix.val.map (p₁₂).toRingHom).map (descentMerge R S).toRingHom =
      (U.matrix.val.map (prod₂).toRingHom).map (ι₁).toRingHom :=
    Matrix.ext (fun i j => descentMerge_12 R S _)
  rw [h₁, h₂, h₃] at h
  replace h := congrArg (fun M : Matrix ι ι S₂ => M * (U.matrix⁻¹).val) h
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h
  apply Matrix.map_injective (f := (ι₁ : S → S₂))
    (fun a b hab => by
      have ha := congrArg prod₂ hab
      simpa only [Algebra.TensorProduct.includeLeft_apply, descentProduct_tmul, mul_one] using ha)
  change (U.matrix.val.map (prod₂).toRingHom).map (ι₁).toRingHom =
    (1 : Matrix ι ι S).map (ι₁).toRingHom
  rw [Matrix.map_one _ (map_zero (ι₁).toRingHom) (map_one (ι₁).toRingHom)]
  exact h.symm

omit [DecidableEq ι] in
private theorem map_mulVec_comp {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Matrix ι ι A) (v : ι → A) :
    f ∘ (M *ᵥ v) = M.map f *ᵥ (f ∘ v) :=
  funext (RingHom.map_mulVec f M v)

private theorem overlap_eq_of_compatible (v : ι → S₂)
    (hv : p₁₂ ∘ v = U.matrix.val.map (p₂₃).toRingHom *ᵥ (p₁₃ ∘ v)) :
    v = (U.matrix⁻¹).val *ᵥ (ι₁ ∘ prod₂ ∘ v) := by
  let m := descentMerge R S
  have h := congrArg (fun w : ι → S₃ => m.toRingHom ∘ w) hv
  change m.toRingHom ∘ (p₁₂ ∘ v) =
    m.toRingHom ∘ (U.matrix.val.map (p₂₃).toRingHom *ᵥ (p₁₃ ∘ v)) at h
  have hLeft : m.toRingHom ∘ (p₁₂ ∘ v) = ι₁ ∘ prod₂ ∘ v :=
    funext (fun i => descentMerge_12 R S (v i))
  have hRight : (U.matrix.val.map (p₂₃).toRingHom).map m.toRingHom = U.matrix.val :=
    Matrix.ext (fun i j => descentMerge_23 R S _)
  have hArg : m.toRingHom ∘ (p₁₃ ∘ v) = v := funext (fun i => descentMerge_13 R S (v i))
  rw [hLeft, map_mulVec_comp, hRight, hArg] at h
  rw [h, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem overlap_inverse_cocycle :
    (U.matrix⁻¹).val.map (p₁₂).toRingHom =
      U.matrix.val.map (p₂₃).toRingHom * (U.matrix⁻¹).val.map (p₁₃).toRingHom := by
  let u₁₂ : (Matrix ι ι S₃)ˣ := Units.map (p₁₂).toRingHom.mapMatrix.toMonoidHom U.matrix
  let u₁₃ : (Matrix ι ι S₃)ˣ := Units.map (p₁₃).toRingHom.mapMatrix.toMonoidHom U.matrix
  let u₂₃ : (Matrix ι ι S₃)ˣ := Units.map (p₂₃).toRingHom.mapMatrix.toMonoidHom U.matrix
  have h : u₁₃ = u₁₂ * u₂₃ := Units.ext U.cocycle
  have hi : u₁₂⁻¹ = u₂₃ * u₁₃⁻¹ := by
    rw [h, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hmap (p : S₂ →ₐ[R] S₃) : (U.matrix⁻¹).val.map p.toRingHom =
      ((Units.map p.toRingHom.mapMatrix.toMonoidHom U.matrix : (Matrix ι ι S₃)ˣ)⁻¹).val := by
    let f : (Matrix ι ι S₂)ˣ →* (Matrix ι ι S₃)ˣ := Units.map p.toRingHom.mapMatrix.toMonoidHom
    exact congrArg Units.val (map_inv f U.matrix)
  rw [hmap, hmap]
  exact congrArg Units.val hi

private theorem overlap_inverse_diagonal : (U.matrix⁻¹).val.map (prod₂).toRingHom = 1 := by
  have h := congrArg ((prod₂).toRingHom.mapMatrix : Matrix ι ι S₂ →+* Matrix ι ι S)
    (Units.inv_mul U.matrix)
  rw [map_mul, map_one] at h
  change (U.matrix⁻¹).val.map (prod₂).toRingHom * U.matrix.val.map (prod₂).toRingHom = 1 at h
  simpa only [U.overlap_diagonal, Matrix.mul_one] using h

private theorem exists_compatible_overlap (x : ι → S) :
    ∃ v : ι → S₂, (p₁₂ ∘ v = U.matrix.val.map (p₂₃).toRingHom *ᵥ (p₁₃ ∘ v)) ∧
      prod₂ ∘ v = x := by
  let v := (U.matrix⁻¹).val *ᵥ (ι₁ ∘ x)
  refine ⟨v, ?_, ?_⟩
  · have hLeft : (p₁₂).toRingHom ∘ v =
        (U.matrix⁻¹).val.map (p₁₂).toRingHom *ᵥ ((p₁₂).toRingHom ∘ ι₁ ∘ x) :=
      map_mulVec_comp (p₁₂).toRingHom _ _
    have hRight : (p₁₃).toRingHom ∘ v =
        (U.matrix⁻¹).val.map (p₁₃).toRingHom *ᵥ ((p₁₃).toRingHom ∘ ι₁ ∘ x) :=
      map_mulVec_comp (p₁₃).toRingHom _ _
    have hArg : (p₁₂).toRingHom ∘ ι₁ ∘ x = (p₁₃).toRingHom ∘ ι₁ ∘ x := rfl
    change (p₁₂).toRingHom ∘ v = U.matrix.val.map (p₂₃).toRingHom *ᵥ ((p₁₃).toRingHom ∘ v)
    rw [hLeft, hRight, hArg, U.overlap_inverse_cocycle, Matrix.mulVec_mulVec]
  · change (prod₂).toRingHom ∘ ((U.matrix⁻¹).val *ᵥ (ι₁ ∘ x)) = x
    rw [map_mulVec_comp, U.overlap_inverse_diagonal, Matrix.one_mulVec]
    funext i
    change prod₂ (x i ⊗ₜ[R] (1 : S)) = x i
    rw [descentProduct_tmul, mul_one]

section FlatCover

variable [Module.Flat R S]

local notation "lt" => TensorProduct.AlgebraTensorModule.lTensor S S
local notation "leftMap" => left (R := R) (S := S) (ι := ι)

private def tensorEqualizer :
    S ⊗[R] U.module ≃ₗ[S] LinearMap.eqLocus (lt leftMap) (lt U.right) :=
  LinearMap.tensorEqLocusEquiv S S leftMap U.right

private theorem comparison_eq_diagonal (x : S ⊗[R] U.module) :
    U.comparison x = prod₂ ∘ coordinates₂ ((U.tensorEqualizer x).val) := by
  induction x with
  | zero =>
    simp only [LinearMap.map_zero, LinearEquiv.map_zero, ZeroMemClass.coe_zero]
    funext i
    exact (map_zero prod₂).symm
  | add x y hx hy =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, AddMemClass.coe_add, hx, hy]
    funext i
    exact (map_add prod₂ _ _).symm
  | tmul a x =>
    funext i
    change a * x.val i = prod₂ (a ⊗ₜ[R] x.val i)
    rfl

/-- A flat cover with a matrix cocycle recovers the given free module by extending
scalars from its equalizer module. -/
def comparisonEquiv : S ⊗[R] U.module ≃ₗ[S] (ι → S) := by
  refine LinearEquiv.ofBijective U.comparison ⟨?_, ?_⟩
  · intro x y h
    let b := U.tensorEqualizer
    let x' := coordinates₂ (b x).val
    let y' := coordinates₂ (b y).val
    have hx : p₁₂ ∘ x' = U.matrix.val.map (p₂₃).toRingHom *ᵥ (p₁₃ ∘ x') := by
      have h := congrArg coordinates₃ (b x).property
      simpa only [coordinates₃_left, coordinates₃_right] using h
    have hy : p₁₂ ∘ y' = U.matrix.val.map (p₂₃).toRingHom *ᵥ (p₁₃ ∘ y') := by
      have h := congrArg coordinates₃ (b y).property
      simpa only [coordinates₃_left, coordinates₃_right] using h
    apply b.injective
    apply Subtype.ext
    apply (coordinates₂).injective
    change x' = y'
    have hxy : prod₂ ∘ x' = prod₂ ∘ y' :=
      (U.comparison_eq_diagonal x).symm.trans (h.trans (U.comparison_eq_diagonal y))
    rw [U.overlap_eq_of_compatible x' hx, U.overlap_eq_of_compatible y' hy, hxy]
  · intro x
    obtain ⟨v, hv, hEval⟩ := U.exists_compatible_overlap x
    let y := (coordinates₂).symm v
    have hy : coordinates₂ y = v := (coordinates₂).apply_symm_apply v
    have hEqual : lt leftMap y = lt U.right y := by
      apply (coordinates₃).injective
      rw [coordinates₃_left, coordinates₃_right, hy]
      exact hv
    let y' : LinearMap.eqLocus (lt leftMap) (lt U.right) := ⟨y, hEqual⟩
    refine ⟨U.tensorEqualizer.symm y', ?_⟩
    rw [U.comparison_eq_diagonal, LinearEquiv.apply_symm_apply]
    change prod₂ ∘ coordinates₂ y = x
    rw [hy, hEval]

@[simp] theorem comparisonEquiv_tmul (a : S) (x : U.module) :
    U.comparisonEquiv (a ⊗ₜ[R] x) = a • x.val := rfl

end FlatCover

/-- For a faithfully flat cover the descended module is finite. -/
theorem module_finite [Module.FaithfullyFlat R S] : Module.Finite R U.module := by
  letI : Module.Finite S (S ⊗[R] U.module) := Module.Finite.equiv U.comparisonEquiv.symm
  exact finite_of_faithfullyFlat_tensor (S := S)

/-- Flatness of the original free module descends along the faithfully flat cover. -/
theorem module_flat [Module.FaithfullyFlat R S] : Module.Flat R U.module := by
  letI : Module.Flat S (S ⊗[R] U.module) := (Module.Flat.equiv_iff U.comparisonEquiv).mpr inferInstance
  exact Module.Flat.of_flat_tensorProduct R U.module S

/-- In particular the descended module admits a finite basis over a PID. -/
theorem module_free [IsDomain R] [IsPrincipalIdealRing R] [Module.FaithfullyFlat R S] :
    Module.Free R U.module := by
  letI : Module.Finite R U.module := U.module_finite
  letI : Module.Flat R U.module := U.module_flat
  letI : Module.FinitePresentation R U.module := Module.finitePresentation_of_finite R U.module
  have hProjective : Module.Projective R U.module := Module.Flat.projective_of_finitePresentation
  obtain ⟨j, hj⟩ := Module.projective_def.mp hProjective
  letI : NoZeroSMulDivisors R U.module := ⟨by
    intro r x h
    have hsmul : r • j x = 0 := by rw [← j.map_smul, h, j.map_zero]
    exact (smul_eq_zero.mp hsmul).imp_right (fun hx => hj.injective (hx.trans j.map_zero.symm))⟩
  infer_instance

section PIDBase

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.FaithfullyFlat R S]

/-- The descended free module has the same finite rank as the matrix datum. -/
theorem exists_basis : Nonempty (Basis ι R U.module) := by
  letI : Module.Finite R U.module := U.module_finite
  letI : Module.Free R U.module := U.module_free
  letI : Nontrivial (S ⊗[R] R) := Module.FaithfullyFlat.lTensor_nontrivial R S R
  letI : Nontrivial S := (TensorProduct.rid R S).symm.toEquiv.nontrivial
  let b := Module.finBasis R U.module
  let bS := (b.baseChange S).map U.comparisonEquiv
  have h : Fintype.card (Fin (Module.finrank R U.module)) = Fintype.card ι :=
    (Module.finrank_eq_card_basis bS).symm.trans (Module.finrank_eq_card_basis (Pi.basisFun S ι))
  exact ⟨b.reindex (Fintype.equivOfCardEq h)⟩

/-- A basis of the descended free module trivializes the given matrix cocycle. -/
theorem exists_trivializingMatrix : ∃ g : (Matrix ι ι S)ˣ,
    g.val.map (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) =
      U.matrix.val * g.val.map (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S) := by
  obtain ⟨b⟩ := U.exists_basis
  let bS := (b.baseChange S).map U.comparisonEquiv
  let g : (Matrix ι ι S)ˣ := Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv bS.equivFun.symm)
  have hg (i j : ι) : g.val i j = (b j).val i := by
    change LinearMap.toMatrixAlgEquiv' bS.equivFun.symm.toLinearMap i j = (b j).val i
    rw [LinearMap.toMatrixAlgEquiv'_apply]
    have h : (fun j' => if j' = j then (1 : S) else 0) = Pi.single j 1 := by
      funext j'
      simp only [Pi.single_apply]
    rw [h]
    change bS.equivFun.symm (Pi.single j 1) i = (b j).val i
    rw [Basis.equivFun_symm_single, Basis.map_apply, Basis.baseChange_apply, U.comparisonEquiv_tmul, one_smul]
  refine ⟨g, Matrix.ext fun i j => ?_⟩
  have h := congrFun ((U.mem_module (b j)).mp (b j).property) i
  simpa only [Matrix.map_apply, Matrix.mul_apply, hg, Matrix.mulVec, dotProduct, Function.comp_apply] using h

end PIDBase

end MatrixDescentDatum

end MatrixDescent

end WideE
