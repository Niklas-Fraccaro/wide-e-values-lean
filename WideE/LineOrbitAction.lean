import WideE.ProjectiveLineReduction
import WideE.GaloisTorsor

/-! Evaluation and transport of equivariant frame vectors at torsor points. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

section ChangeTarget

variable {k R S H A B : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing H]
  [CommRing A] [CommRing B]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S] [HopfAlgebra k H]
  [Algebra k A] [Algebra R A] [IsScalarTower k R A]
  [Algebra k B] [Algebra R B] [IsScalarTower k R B]

/-- An algebra morphism between distinct target algebras preserves the torsor action. -/
theorem AffineHopfTorsor.actPoint_postcompose
    (T : AffineHopfTorsor k R S H) (f : A →ₐ[R] B) (p : S →ₐ[R] A) (h : H →ₐ[k] A) :
    f.comp (T.actPoint p h) = T.actPoint (f.comp p) ((f.restrictScalars k).comp h) := by
  apply AlgHom.ext
  intro s
  change f (tensorPoint p h (T.coaction s)) =
    tensorPoint (f.comp p) ((f.restrictScalars k).comp h) (T.coaction s)
  generalize T.coaction s = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp only [tensorPoint_tmul, map_mul, AlgHom.comp_apply,
      AlgHom.restrictScalars_apply]

end ChangeTarget

section FrameAction

variable {k R S H A ι : Type*} [Field k] [CommRing R] [CommRing S] [CommRing H]
  [CommRing A] [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [HopfAlgebra k H] [Algebra k A] [Algebra R A] [IsScalarTower k R A] [Fintype ι] [DecidableEq ι]

local notation "ιS" => (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H)
local notation "ιH" => (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H)

/-- The right torsor action moves an equivariant frame vector by the inverse
of the evaluated representation matrix. -/
theorem AffineHopfTorsor.actPoint_projectiveFrameVector
    (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ) (g : (Matrix ι ι S)ˣ)
    (y : ι → R)
    (hg : g.val.map T.coaction.toRingHom = (U⁻¹).val.map (ιH).toRingHom * g.val.map (ιS).toRingHom)
    (p : S →ₐ[R] A) (h : H →ₐ[k] A) :
    (T.actPoint p h).toRingHom ∘ projectiveFrameVector g y =
      (U⁻¹).val.map h.toRingHom *ᵥ (p.toRingHom ∘ projectiveFrameVector g y) := by
  let e := (tensorPoint p h).toRingHom
  have hL (s : S) : e (ιS s) = p s := by
    change tensorPoint p h (s ⊗ₜ[k] (1 : H)) = p s
    rw [tensorPoint_tmul, map_one, mul_one]
  have hR (a : H) : e (ιH a) = h a := by
    change tensorPoint p h ((1 : S) ⊗ₜ[k] a) = h a
    rw [tensorPoint_tmul, map_one, one_mul]
  have hMat : g.val.map (T.actPoint p h).toRingHom =
      (U⁻¹).val.map h.toRingHom * g.val.map p.toRingHom := by
    have hm := congrArg (fun M : Matrix ι ι (S ⊗[k] H) => M.map e) hg
    change (g.val.map T.coaction.toRingHom).map e =
      ((U⁻¹).val.map (ιH).toRingHom * g.val.map (ιS).toRingHom).map e at hm
    rw [Matrix.map_mul] at hm
    have hML : (g.val.map (ιS).toRingHom).map e = g.val.map p.toRingHom :=
      Matrix.ext fun _ _ => hL _
    have hMR : ((U⁻¹).val.map (ιH).toRingHom).map e = (U⁻¹).val.map h.toRingHom :=
      Matrix.ext fun _ _ => hR _
    rwa [hML, hMR] at hm
  have hScalar (r : S →ₐ[R] A) :
      r.toRingHom ∘ (algebraMap R S ∘ y) = algebraMap R A ∘ y :=
    funext fun i => r.commutes (y i)
  funext i
  change (T.actPoint p h).toRingHom ((g.val *ᵥ (algebraMap R S ∘ y)) i) =
    (((U⁻¹).val.map h.toRingHom) *ᵥ (p.toRingHom ∘ (g.val *ᵥ (algebraMap R S ∘ y)))) i
  rw [RingHom.map_mulVec, hMat, hScalar, ← Matrix.mulVec_mulVec]
  have hp : p.toRingHom ∘ (g.val *ᵥ (algebraMap R S ∘ y)) =
      g.val.map p.toRingHom *ᵥ (algebraMap R A ∘ y) := by
    funext j
    change p.toRingHom ((g.val *ᵥ (algebraMap R S ∘ y)) j) = _
    rw [RingHom.map_mulVec, hScalar]
  rw [hp]

/-- Equivalently, the representation matrix sends the translated frame
vector back to its original value. -/
theorem AffineHopfTorsor.projectiveFrameVector_eq_mulVec_actPoint
    (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ) (g : (Matrix ι ι S)ˣ)
    (y : ι → R)
    (hg : g.val.map T.coaction.toRingHom = (U⁻¹).val.map (ιH).toRingHom * g.val.map (ιS).toRingHom)
    (p : S →ₐ[R] A) (h : H →ₐ[k] A) :
    p.toRingHom ∘ projectiveFrameVector g y =
      U.val.map h.toRingHom *ᵥ ((T.actPoint p h).toRingHom ∘ projectiveFrameVector g y) := by
  rw [T.actPoint_projectiveFrameVector U g y hg p h, Matrix.mulVec_mulVec, ← Matrix.map_mul,
    Units.mul_inv, Matrix.map_one h.toRingHom (map_zero h.toRingHom) (map_one h.toRingHom), Matrix.one_mulVec]

end FrameAction

end WideE
