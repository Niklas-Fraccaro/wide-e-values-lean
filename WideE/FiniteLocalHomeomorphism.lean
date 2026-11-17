import Mathlib.Topology.Covering
import Mathlib.SetTheory.Cardinal.Finite

/-! A surjective local homeomorphism with finite fibers of constant size is a covering. -/

open scoped Topology
open Set Bundle Topology

noncomputable section

namespace WideE

theorem isCoveringMap_of_localHomeomorph_of_finite_fibers
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] [T2Space E] {p : E → B}
    (hp : IsLocalHomeomorph p) (hpSurj : Function.Surjective p)
    (hFinite : ∀ b, (p ⁻¹' {b}).Finite) (hCard : ∀ b b',
      Nat.card (p ⁻¹' {b} : Set E) = Nat.card (p ⁻¹' {b'} : Set E)) :
    IsCoveringMap p := by
  classical
  intro b
  let I := p ⁻¹' {b}
  letI : Finite I := (hFinite b).to_subtype
  let i₀ : I := ⟨Classical.choose (hpSurj b), Classical.choose_spec (hpSurj b)⟩
  refine ⟨inferInstance, ?_⟩
  obtain ⟨O, hO, hdisjoint⟩ := (hFinite b).t2_separation
  choose c hc heq using fun i : I => hp (i : E)
  let e (i : I) := (c i).restr (O i)
  have he (i : I) : (i : E) ∈ (e i).source := by
    rw [PartialHomeomorph.restr_source' _ _ (hO i).2]
    exact ⟨hc i, (hO i).1⟩
  have hsep (i j : I) (hij : i ≠ j) : Disjoint (e i).source (e j).source := by
    refine (hdisjoint i.property j.property (fun h => hij (Subtype.ext h))).mono ?_ ?_
    · rw [PartialHomeomorph.restr_source' _ _ (hO i).2]
      exact inter_subset_right
    · rw [PartialHomeomorph.restr_source' _ _ (hO j).2]
      exact inter_subset_right
  let V := ⋂ i, (e i).target
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => (e i).open_target
  have hb : b ∈ V := mem_iInter.mpr fun i => by
    have h := (e i).map_source (he i)
    simpa only [e, PartialHomeomorph.restr_apply, ← heq i, show p i = b from i.property] using h
  have htarget {y : B} (hy : y ∈ V) (i : I) : y ∈ (e i).target := mem_iInter.mp hy i
  let g (y : B) (i : I) : E := (e i).symm y
  have hg {y : B} (hy : y ∈ V) (i : I) : p (g y i) = y :=
    (congrFun (heq i) _).trans ((e i).right_inv (htarget hy i))
  have hinj {y : B} (hy : y ∈ V) : Function.Injective (g y) := by
    intro i j h
    by_contra hij
    have hmem : g y i ∈ (e j).source := by
      rw [h]
      exact (e j).map_target (htarget hy j)
    exact Set.disjoint_left.mp (hsep i j hij) ((e i).map_target (htarget hy i)) hmem
  have hbij {y : B} (hy : y ∈ V) : Function.Bijective
      (fun i : I => (⟨g y i, hg hy i⟩ : (p ⁻¹' {y} : Set E))) := by
    letI : Finite (p ⁻¹' {y} : Set E) := (hFinite y).to_subtype
    exact (Nat.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => hinj hy (congrArg Subtype.val h), hCard b y⟩
  let label (z : E) : I := if h : p z ∈ V then
    (Equiv.ofBijective _ (hbij h)).symm ⟨z, rfl⟩ else i₀
  have hlabel {z : E} (hz : p z ∈ V) : g (p z) (label z) = z := by
    simpa only [label, dif_pos hz] using congrArg Subtype.val
      ((Equiv.ofBijective _ (hbij hz)).apply_symm_apply ⟨z, rfl⟩)
  have hlocal {z : E} (hz : p z ∈ V) {i : I} (hi : z ∈ (e i).source) : label z = i := by
    apply hinj hz
    rw [hlabel hz]
    simpa only [g, e, PartialHomeomorph.restr_apply, ← heq i] using ((e i).left_inv hi).symm
  refine ⟨{
    toFun := fun z => (p z, label z)
    invFun := fun y => g y.1 y.2
    source := p ⁻¹' V
    target := V ×ˢ univ
    map_source' := fun _ hz => ⟨hz, trivial⟩
    map_target' := fun y hy => by
      change p (g y.1 y.2) ∈ V
      rw [hg hy.1 y.2]
      exact hy.1
    left_inv' := fun _ hz => hlabel hz
    right_inv' := fun y hy => by
      refine Prod.ext (hg hy.1 y.2) (hlocal ?_ ((e y.2).map_target (htarget hy.1 y.2)))
      rw [hg hy.1 y.2]
      exact hy.1
    open_source := hp.continuous.isOpen_preimage _ hV
    open_target := hV.prod isOpen_univ
    continuousOn_toFun := hp.continuous.continuousOn.prodMk (fun z hz => by
      let i := label z
      have hs : z ∈ (e i).source := (hlabel hz) ▸ (e i).map_target (htarget hz i)
      have hn : p ⁻¹' V ∩ (e i).source ∈ 𝓝 z :=
        IsOpen.mem_nhds ((hp.continuous.isOpen_preimage _ hV).inter (e i).open_source) ⟨hz, hs⟩
      exact (continuousAt_const.congr (show (fun _ : E => i) =ᶠ[𝓝 z] label from
        Filter.eventually_of_mem hn fun _ hw => (hlocal hw.1 hw.2).symm)).continuousWithinAt)
    continuousOn_invFun := fun y hy => by
      have hc : ContinuousAt (fun z : B × I => g z.1 y.2) y :=
        ((e y.2).continuousAt_symm (htarget hy.1 y.2)).comp continuousAt_fst
      exact (hc.congr (show (fun z : B × I => g z.1 y.2) =ᶠ[𝓝 y] (fun z => g z.1 z.2) from by
        have h : ∀ᶠ z : B × I in 𝓝 y, z.2 = y.2 :=
          continuous_snd.continuousAt.preimage_mem_nhds ((isOpen_discrete {y.2}).mem_nhds rfl)
        exact h.mono fun z hz => congrArg (g z.1) hz.symm)).continuousWithinAt
    baseSet := V
    open_baseSet := hV
    source_eq := rfl
    target_eq := rfl
    proj_toFun := fun _ _ => rfl }, hb⟩

end WideE
