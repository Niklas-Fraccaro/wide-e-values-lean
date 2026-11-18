import WideE.HopfCotangentBaseChange
import WideE.HopfQuotientBaseChange
import WideE.AdjointToricDescent

/-! The actual adjoint centralizer quotient commutes with scalar extension. -/

noncomputable section

open scoped TensorProduct Matrix
open Module

namespace WideE

variable {k F H ι : Type*} [Field k] [Field F] [Algebra k F] [CommRing H] [HopfAlgebra k H]

local notation "H'" => (F ⊗[k] H)
local notation "r" => (Algebra.TensorProduct.includeRight : H →ₐ[k] H')

attribute [local instance] hopfScalarExtension

/-- The original cotangent basis regarded as a basis of the extended coordinate algebra. -/
def hopfCotangentBasisBaseChange (b : Basis ι k (HopfCotangent k H)) :
    Basis ι F (HopfCotangent F H') :=
  (b.baseChange F).map hopfCotangentBaseChange

theorem hopfLieVectorBaseChange_basis {B : Type*} [CommRing B]
    [Algebra k B] [Algebra F B] [IsScalarTower k F B]
    (b : Basis ι k (HopfCotangent k H)) (x : HopfLieVector k H B) (i : ι) :
    hopfLieVectorBaseChange (F := F) x (hopfCotangentBasisBaseChange b i) = x (b i) := by
  obtain ⟨h, hh⟩ := hopfCotangentProjection_surjective k H (b i)
  simp only [hopfCotangentBasisBaseChange, Basis.map_apply, Basis.baseChange_apply, ← hh,
    hopfCotangentBaseChange_tmul, hopfLieVectorBaseChange_projection_tmul, one_smul]

section Matrix

variable [Fintype ι] [DecidableEq ι]

/-- The adjoint coefficient functions extend through the right-factor inclusion. -/
theorem hopfAdjointMatrix_baseChange (b : Basis ι k (HopfCotangent k H)) :
    hopfAdjointMatrix (hopfCotangentBasisBaseChange (F := F) b) = (hopfAdjointMatrix b).map r := by
  let b' := hopfCotangentBasisBaseChange (F := F) b
  let q := AlgHom.id F H'
  have hq : scalarExtendPoint (A := F) r = q := by
    apply scalarExtendPoint_ext
    intro x
    rw [scalarExtendPoint_one_tmul]
    rfl
  apply Matrix.ext
  intro i j
  let v : ι → H' := Pi.single j 1
  let x := b.constr H' v
  let x' := hopfLieVectorBaseChange (F := F) x
  have hx : (fun l => x (b l)) = v := funext (b.constr_basis H' v)
  have hx' : (fun l => x' (b' l)) = v := by
    funext l
    exact (hopfLieVectorBaseChange_basis b x l).trans (congrFun hx l)
  have h := DFunLike.congr_fun (hopfLieVectorBaseChange_adjoint r x) (b' i)
  change hopfLieVectorBaseChange (F := F) (hopfAdjoint r x) (b' i) =
    hopfAdjoint (scalarExtendPoint (A := F) r) x' (b' i) at h
  rw [hopfLieVectorBaseChange_basis, hq] at h
  have hL := congrFun (hopfAdjoint_apply_basis b r x) i
  have hR := congrFun (hopfAdjoint_apply_basis b' q x') i
  rw [hx] at hL
  rw [hx'] at hR
  change hopfAdjoint r x (b i) = _ at hL
  change hopfAdjoint q x' (b' i) = _ at hR
  rw [hL, hR] at h
  simpa only [v, Matrix.mulVec_single_one, Matrix.map_apply, q, AlgHom.id_apply] using h.symm

end Matrix

section Ideals

variable [Fintype ι]

theorem vectorStabilizerIdeal_baseChange (U : Matrix ι ι H) (v : ι → k) :
    (vectorStabilizerIdeal U v).map r = vectorStabilizerIdeal (U.map r) (algebraMap k F ∘ v) := by
  have hScalar : ((r).toRingHom : H → H') ∘ (algebraMap k H ∘ v) =
      algebraMap F H' ∘ (algebraMap k F ∘ v) := by
    funext i
    exact ((r).commutes (v i)).trans (IsScalarTower.algebraMap_apply k F H' (v i))
  have hEquation (i : ι) : r (vectorStabilizerEquation U v i) =
      vectorStabilizerEquation (U.map r) (algebraMap k F ∘ v) i := by
    unfold vectorStabilizerEquation
    rw [map_sub, (r).commutes,
      show r ((U *ᵥ (algebraMap k H ∘ v)) i) =
        (U.map r *ᵥ (((r).toRingHom : H → H') ∘ (algebraMap k H ∘ v))) i
        from RingHom.map_mulVec (r).toRingHom U (algebraMap k H ∘ v) i,
      hScalar, IsScalarTower.algebraMap_apply k F H']
    rfl
  unfold vectorStabilizerIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  exact congrArg (fun f : ι → H' => Ideal.span (Set.range f)) (funext hEquation)

/-- A rational Lie vector extended to the new base field. -/
abbrev hopfLieVectorBaseChangeRational (x : HopfLieVector k H k) : HopfLieVector F H' F :=
  hopfLieVectorBaseChange (F := F) ((Algebra.ofId k F).toLinearMap.comp x)

variable [DecidableEq ι]

theorem hopfAdjointCentralizerIdeal_baseChange
    (b : Basis ι k (HopfCotangent k H)) (x : HopfLieVector k H k) :
    (hopfAdjointCentralizerIdeal b x).map r =
      hopfAdjointCentralizerIdeal (hopfCotangentBasisBaseChange (F := F) b)
        (hopfLieVectorBaseChangeRational x) := by
  let b' := hopfCotangentBasisBaseChange (F := F) b
  let x' := hopfLieVectorBaseChangeRational (F := F) x
  change (vectorStabilizerIdeal (hopfAdjointMatrix b) (fun i => x (b i))).map r =
    vectorStabilizerIdeal (hopfAdjointMatrix b') (fun i => x' (b' i))
  have hx (i : ι) : x' (b' i) = algebraMap k F (x (b i)) :=
    hopfLieVectorBaseChange_basis b _ i
  rw [vectorStabilizerIdeal_baseChange, show hopfAdjointMatrix b' = _ from hopfAdjointMatrix_baseChange b]
  exact congrArg (vectorStabilizerIdeal ((hopfAdjointMatrix b).map r)) (funext hx).symm

/-- Extension of the actual closed centralizer to the new base field is its
counterpart for the extended Lie vector, as a bialgebra. -/
def hopfAdjointCentralizerBaseChange (b : Basis ι k (HopfCotangent k H)) (x : HopfLieVector k H k) :
    let b' := hopfCotangentBasisBaseChange (F := F) b
    let x' := hopfLieVectorBaseChangeRational (F := F) x
    letI := (hopfAdjointCentralizerIdeal_isHopf b x).quotientHopf
    letI := (hopfAdjointCentralizerIdeal_isHopf b' x').quotientHopf
    (F ⊗[k] (H ⧸ hopfAdjointCentralizerIdeal b x)) ≃ₐc[F] (H' ⧸ hopfAdjointCentralizerIdeal b' x') :=
  hopfQuotientBaseChange (hopfAdjointCentralizerIdeal_isHopf b x) (hopfAdjointCentralizerIdeal_isHopf _ _)
    (hopfAdjointCentralizerIdeal_baseChange b x)

end Ideals

end WideE
