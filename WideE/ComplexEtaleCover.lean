import WideE.ComplexLaurentPoints
import WideE.FiniteLocalHomeomorphism
import WideE.KummerAnalyticPoint
import WideE.LaurentPowerCoordinates

/-! The covering map of complex points of a finite étale Laurent algebra. -/

open scoped Topology
open Set Filter Topology

noncomputable section

namespace WideE

@[simp] theorem complexLaurentFunctions_puncturedOne (r : LaurentPolynomial ℂ) :
    complexLaurentFunctions r puncturedOne = evalAtOne ℂ r := by
  change LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 1 one_ne_zero) r =
    LaurentPolynomial.eval₂ (RingHom.id ℂ) 1 r
  rw [show Units.mk0 (1 : ℂ) one_ne_zero = 1 from Units.ext rfl]

end WideE

namespace WideE.ComplexLaurentPoints

variable {A : Type} [CommRing A] [Algebra ℂ A] [Algebra (LaurentPolynomial ℂ) A]
  [IsScalarTower ℂ (LaurentPolynomial ℂ) A] [Algebra.Etale (LaurentPolynomial ℂ) A]
  {n : ℕ}

local notation "E" => ComplexLaurentPoints A

private abbrev baseEval (z : ComplexPuncturedLine) := laurentEvalAlg (complexPuncturedUnit z)

private theorem continuous_baseEval (d : LaurentPolynomial ℂ) :
    Continuous (fun z : ComplexPuncturedLine => baseEval z d) := by
  have heq : (fun z : ComplexPuncturedLine => complexLaurentEvaluation z d) =
      fun z => baseEval z d := by
    funext z
    rw [complexLaurentEvaluation_of_ne z.property]
    rfl
  rw [← heq]
  exact continuous_iff_continuousAt.mpr fun z =>
    (complexLaurentEvaluation_analyticAt d z.property).continuousAt.comp continuousAt_subtype_val

/-- The projection has a local inverse at every complex point. On that inverse,
evaluation of each algebra element extends differentiably across the base point. -/
theorem exists_analytic_chart (b : Basis (Fin n) (LaurentPolynomial ℂ) A) (x : E) :
    ∃ e : PartialHomeomorph E ComplexPuncturedLine, x ∈ e.source ∧ proj = e ∧
      ∀ c : A, ∃ f : ℂ → ℂ, DifferentiableAt ℂ f (x.proj : ℂ) ∧
        ∀ z : ComplexPuncturedLine, z ∈ e.target → f z = (e.symm z).algHom c := by
  classical
  obtain ⟨a, ha⟩ := exists_primitiveChart_at b (baseEval x.proj)
  let P := primitiveCharpoly b a
  have hxroot : (P.map (baseEval x.proj).toRingHom).IsRoot (x.algHom a) :=
    evaluationFiberPoint_isRoot b a (baseEval x.proj) x.2
  have hsimple := eval_primitiveCharpoly_derivative_ne_zero b a (baseEval x.proj) ha hxroot
  obtain ⟨s, U, V, hU, hxU, _, hV, hxV, _, hsDiff, hsCont, hsV, hgraph⟩ :=
    exists_laurent_simple_root_chart P x.proj.property hxroot hsimple
  let d := powerCoordinateDet b a
  let W := {z : ComplexPuncturedLine | (z : ℂ) ∈ U ∧ baseEval z d ≠ 0}
  have hW : IsOpen W := (continuous_subtype_val.isOpen_preimage _ hU).inter
    (isOpen_ne_fun (continuous_baseEval d) continuous_const)
  have hxW : x.proj ∈ W := ⟨hxU, ha⟩
  let lift (z : ComplexPuncturedLine) (hz : z ∈ W) : E :=
    ⟨z, (evaluationFiberPointRootEquiv b a (baseEval z) hz.2).symm
      ⟨s z, (hgraph z hz.1 (s z) (hsV hz.1) z.property).mpr rfl⟩⟩
  have lift_apply (z : ComplexPuncturedLine) (hz : z ∈ W) : (lift z hz).algHom a = s z :=
    congrArg Subtype.val ((evaluationFiberPointRootEquiv b a (baseEval z) hz.2).apply_symm_apply _)
  let inv (z : ComplexPuncturedLine) := if hz : z ∈ W then lift z hz else x
  let O : Set E := proj ⁻¹' W ∩ (fun y : E => y.algHom a) ⁻¹' V
  have hxO : x ∈ O := ⟨hxW, hxV⟩
  have hProj (z : ComplexPuncturedLine) (hz : z ∈ W) : (inv z).proj = z := by
    rw [show inv z = lift z hz from dif_pos hz]
    rfl
  have hMaps : MapsTo inv W O := by
    intro z hz
    rw [show inv z = lift z hz from dif_pos hz]
    refine ⟨hz, ?_⟩
    change (lift z hz).algHom a ∈ V
    rw [lift_apply z hz]
    exact hsV hz.1
  have hLeft : ∀ y ∈ O, inv y.proj = y := by
    rintro ⟨z, p⟩ hy
    have hz : z ∈ W := hy.1
    change inv z = ⟨z, p⟩
    rw [show inv z = lift z hz from dif_pos hz]
    have hEq : (lift z hz).2 = p := by
      apply evaluationFiberPoint_sep_of_det_ne_zero b a (baseEval z) hz.2
      change (lift z hz).algHom a = p.val a
      rw [lift_apply z hz]
      exact ((hgraph z hz.1 (p.val a) hy.2 z.property).mp
        (evaluationFiberPoint_isRoot b a (baseEval z) p)).symm
    exact congrArg (Sigma.mk z) hEq
  let evalInv (c : A) (z : ℂ) := ∑ i : Fin n,
    complexEvaluationPowerCoordinates b a c i z * (s z) ^ i.val
  have evalInv_apply (c : A) (z : ComplexPuncturedLine) (hz : z ∈ W) :
      evalInv c z = (inv z).algHom c := by
    rw [show inv z = lift z hz from dif_pos hz]
    have h := evaluationFiberPoint_apply_eq_sum b a (baseEval z) hz.2 (lift z hz).2 c
    change (lift z hz).algHom c = ∑ i : Fin n,
      evaluationPowerCoordinates b a (baseEval z) c i * ((lift z hz).algHom a) ^ i.val at h
    rw [lift_apply z hz] at h
    simpa only [evalInv, complexEvaluationPowerCoordinates_of_ne _ _ _ _ z.property] using h.symm
  have hInv_cont : ContinuousOn inv W := by
    apply continuousOn_of_proj_and_evaluations
    · exact continuousOn_id.congr fun z hz => hProj z hz
    · intro c
      apply ContinuousOn.congr _ (fun z hz => (evalInv_apply c z hz).symm)
      have hs' : ContinuousOn (fun z : ComplexPuncturedLine => s z) W :=
        hsCont.comp continuous_subtype_val.continuousOn fun _ hz => hz.1
      apply continuousOn_finset_sum _
      intro i _
      refine ContinuousOn.mul (fun z hz => ?_) (hs'.pow i.val)
      have hcoord := (complexEvaluationPowerCoordinates_analyticAt b a c i z.property hz.2).continuousAt
      exact (hcoord.comp continuousAt_subtype_val).continuousWithinAt
  let e : PartialHomeomorph E ComplexPuncturedLine := {
    toFun := proj
    invFun := inv
    source := O
    target := W
    map_source' := fun _ hy => hy.1
    map_target' := hMaps
    left_inv' := hLeft
    right_inv' := hProj
    open_source := (continuous_proj.isOpen_preimage _ hW).inter
      ((continuous_evaluation a).isOpen_preimage _ hV)
    open_target := hW
    continuousOn_toFun := continuous_proj.continuousOn
    continuousOn_invFun := hInv_cont }
  refine ⟨e, hxO, rfl, fun c => ⟨evalInv c, ?_, evalInv_apply c⟩⟩
  apply DifferentiableAt.sum
  intro i _
  have hi := (complexEvaluationPowerCoordinates_analyticAt b a c i x.proj.property ha).differentiableAt
  exact hi.mul (hsDiff.pow i.val)

theorem isCoveringMap_proj [Nontrivial A] (b : Basis (Fin n) (LaurentPolynomial ℂ) A) :
    IsCoveringMap (proj (A := A)) := by
  refine isCoveringMap_of_localHomeomorph_of_finite_fibers ?_ (surjective_proj b) finite_fiber ?_
  · intro x
    obtain ⟨e, he, hEq, _⟩ := exists_analytic_chart b x
    exact ⟨e, he, hEq⟩
  · intro z w
    rw [card_fiber b z, card_fiber b w]

/-- Every continuous lift of the power map has holomorphic coordinate evaluations. -/
theorem exists_holomorphic_evaluation_of_power_lift (b : Basis (Fin n) (LaurentPolynomial ℂ) A)
    (q : ℕ) (g : C(ComplexPuncturedLine, E))
    (hg : ∀ z, ((g z).proj : ℂ) = (z : ℂ) ^ q) (a : A) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({0}ᶜ : Set ℂ) ∧ ∀ z : ComplexPuncturedLine, f z = (g z).algHom a := by
  classical
  let τ (z : ℂ) : ComplexPuncturedLine := if hz : z ≠ 0 then ⟨z, hz⟩ else puncturedOne
  let f (z : ℂ) := (g (τ z)).algHom a
  refine ⟨f, fun z hz => ?_, fun z => by simp [f, τ, z.property]⟩
  have hz₀ : z ≠ 0 := hz
  let z₀ : ComplexPuncturedLine := ⟨z, hz₀⟩
  let x := g z₀
  obtain ⟨e, he, heq, hev⟩ := exists_analytic_chart b x
  obtain ⟨F, hF, hEval⟩ := hev a
  have hDiff : DifferentiableAt ℂ (fun w : ℂ => F (w ^ q)) z :=
    ((hg z₀) ▸ hF).comp z ((differentiableAt_id (𝕜 := ℂ)).pow q)
  apply DifferentiableAt.differentiableWithinAt
  apply hDiff.congr_of_eventuallyEq
  have hne : ∀ᶠ w in 𝓝 z, w ≠ (0 : ℂ) := isClosed_singleton.isOpen_compl.mem_nhds hz₀
  have hτ : ContinuousAt τ z := by
    apply (IsInducing.subtypeVal.continuousAt_iff).2
    apply continuousAt_id.congr
    exact hne.mono fun w hw => by simp [τ, hw]
  have hnear : ∀ᶠ w in 𝓝 z, g (τ w) ∈ e.source :=
    (g.continuous.continuousAt.comp hτ).preimage_mem_nhds
      (e.open_source.mem_nhds (show g (τ z) ∈ e.source by simpa [τ, hz₀, z₀, x] using he))
  filter_upwards [hne, hnear] with w hw hmem
  have hProj : (e (g (τ w)) : ℂ) = w ^ q := by
    rw [← heq]
    simpa [τ, hw] using hg (τ w)
  have hImage := hEval (e (g (τ w))) (e.map_source hmem)
  rw [hProj, e.left_inv hmem] at hImage
  exact hImage.symm

/-- A given complex point above one extends to a point over a positive
Kummer power of the Laurent coordinate. -/
theorem exists_pointed_kummerPoint [Nontrivial A] [Module.Finite (LaurentPolynomial ℂ) A]
    (b : Basis (Fin n) (LaurentPolynomial ℂ) A) (e : E) (he : proj e = puncturedOne) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : A →ₐ[LaurentPolynomial ℂ] KummerExtension ℂ q,
      ∀ a : A, evalAtOne ℂ (KummerExtension.toLaurent ℂ q (f a)) = e.algHom a := by
  letI : Finite (proj (A := A) ⁻¹' {puncturedOne} : Set E) := (finite_fiber puncturedOne).to_subtype
  obtain ⟨q, hq, g, hg₁, hg⟩ := exists_puncturedPower_lift (isCoveringMap_proj b) e he
  obtain ⟨f, hf⟩ := exists_kummerPoint_of_holomorphic_points q (fun z => (g z).algHom)
    (fun z r => ((g z).algHom_algebraMap r).trans
      (congrArg (complexLaurentFunctions r) (Subtype.ext (hg z))))
    (exists_holomorphic_evaluation_of_power_lift b q g hg)
  exact ⟨q, hq, f, fun a => by simpa only [complexLaurentFunctions_puncturedOne, hg₁] using hf puncturedOne a⟩

/-- A nonempty finite étale complex Laurent algebra with a Laurent basis
admits a point after a positive power of the base coordinate. -/
theorem exists_kummerPoint [Nontrivial A] [Module.Finite (LaurentPolynomial ℂ) A]
    (b : Basis (Fin n) (LaurentPolynomial ℂ) A) :
    ∃ q : ℕ, 0 < q ∧ Nonempty (A →ₐ[LaurentPolynomial ℂ] KummerExtension ℂ q) := by
  obtain ⟨e, he⟩ := surjective_proj b puncturedOne
  obtain ⟨q, hq, f, _⟩ := exists_pointed_kummerPoint b e he
  exact ⟨q, hq, ⟨f⟩⟩

end WideE.ComplexLaurentPoints
