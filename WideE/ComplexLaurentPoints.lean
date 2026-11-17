import WideE.LaurentEtaleChart
import WideE.LaurentAnalyticRigidity

/-! The complex points of a Laurent algebra, with their coordinate topology. -/

open Set Topology
open scoped TensorProduct

noncomputable section

namespace WideE

/-- The unit associated to a complex point away from zero. -/
def complexPuncturedUnit (z : ComplexPuncturedLine) : ℂˣ := Units.mk0 z.val z.property

variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (LaurentPolynomial ℂ) A]
  [IsScalarTower ℂ (LaurentPolynomial ℂ) A]

/-- All complex points of the Laurent algebra, indexed by their base points. -/
def ComplexLaurentPoints := Σ z : ComplexPuncturedLine, LaurentFiberPoint A (complexPuncturedUnit z)

namespace ComplexLaurentPoints

variable {A}

/-- Projection to the complex punctured line. -/
def proj (p : ComplexLaurentPoints A) : ComplexPuncturedLine := p.1

/-- The algebra map at a complex point of the Laurent algebra. -/
def algHom (p : ComplexLaurentPoints A) : A →ₐ[ℂ] ℂ := p.2.val

theorem algHom_algebraMap (p : ComplexLaurentPoints A) (r : LaurentPolynomial ℂ) :
    p.algHom (algebraMap (LaurentPolynomial ℂ) A r) = complexLaurentFunctions r p.proj :=
  DFunLike.congr_fun p.2.property r

private def coordinates (p : ComplexLaurentPoints A) : ComplexPuncturedLine × (A → ℂ) :=
  (p.proj, p.algHom)

instance : TopologicalSpace (ComplexLaurentPoints A) := TopologicalSpace.induced coordinates inferInstance

private theorem isEmbedding_coordinates : IsEmbedding (coordinates (A := A)) := by
  apply Function.Injective.isEmbedding_induced
  rintro ⟨z, p⟩ ⟨w, q⟩ h
  have hzw : z = w := congrArg Prod.fst h
  subst w
  have hpq : p = q := Subtype.ext (AlgHom.ext (congrFun (congrArg Prod.snd h)))
  subst q
  rfl

instance : T2Space (ComplexLaurentPoints A) := isEmbedding_coordinates.t2Space

theorem continuous_proj : Continuous (proj (A := A)) :=
  continuous_fst.comp isEmbedding_coordinates.continuous

theorem continuous_evaluation (a : A) : Continuous (fun p : ComplexLaurentPoints A => p.algHom a) :=
  (continuous_apply a).comp (continuous_snd.comp isEmbedding_coordinates.continuous)

theorem continuousOn_of_proj_and_evaluations {X : Type*} [TopologicalSpace X]
    {g : X → ComplexLaurentPoints A} {U : Set X}
    (hproj : ContinuousOn (proj ∘ g) U)
    (hEval : ∀ a : A, ContinuousOn (fun x => (g x).algHom a) U) : ContinuousOn g U := by
  rw [continuousOn_iff_continuous_restrict, isEmbedding_coordinates.isInducing.continuous_iff]
  refine (continuousOn_iff_continuous_restrict.mp hproj).prodMk ?_
  exact continuous_pi fun a => continuousOn_iff_continuous_restrict.mp (hEval a)

/-- The topological fiber has exactly the algebraic points above its base point. -/
def fiberEquiv (z : ComplexPuncturedLine) :
    (proj (A := A) ⁻¹' {z} : Set (ComplexLaurentPoints A)) ≃ LaurentFiberPoint A (complexPuncturedUnit z) where
  toFun := fun p => (show p.val.proj = z from p.property) ▸ p.val.2
  invFun := fun p => ⟨⟨z, p⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨w, p⟩, h⟩
    change w = z at h
    subst w
    rfl
  right_inv := fun _ => rfl

theorem finite_fiber [Algebra.Etale (LaurentPolynomial ℂ) A] (z : ComplexPuncturedLine) :
    (proj (A := A) ⁻¹' {z}).Finite := by
  letI := finite_laurentFiberPoint A (complexPuncturedUnit z)
  letI : Finite (proj (A := A) ⁻¹' {z} : Set (ComplexLaurentPoints A)) :=
    Finite.of_equiv _ (fiberEquiv z).symm
  exact Set.toFinite _

variable [Algebra.Etale (LaurentPolynomial ℂ) A] {n : ℕ}

/-- Each complex fiber of a finite étale Laurent algebra has cardinality equal to its rank. -/
theorem card_fiber (b : Basis (Fin n) (LaurentPolynomial ℂ) A) (z : ComplexPuncturedLine) :
    Nat.card (proj (A := A) ⁻¹' {z} : Set (ComplexLaurentPoints A)) = n := by
  calc
    _ = Nat.card (Fin n) := Nat.card_congr ((fiberEquiv z).trans
      (evaluationFiberPoint_indexEquiv b (laurentEvalAlg (complexPuncturedUnit z))).symm)
    _ = n := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]

theorem surjective_proj [Nontrivial A] (b : Basis (Fin n) (LaurentPolynomial ℂ) A) :
    Function.Surjective (proj (A := A)) := by
  intro z
  obtain ⟨i⟩ := b.index_nonempty
  exact ⟨⟨z, evaluationFiberPoint_indexEquiv b (laurentEvalAlg (complexPuncturedUnit z)) i⟩, rfl⟩

end ComplexLaurentPoints

end WideE
