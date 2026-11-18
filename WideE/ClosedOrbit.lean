import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.NoetherianSpace

/-! A constructible group action on a nonempty Noetherian space has a closed orbit. -/

open Set TopologicalSpace Topology
open scoped Pointwise

namespace WideE

variable {X : Type*} [TopologicalSpace X]

private theorem constructible_interior_frontier {s : Set X} (hs : IsConstructible s) :
    interior (frontier s) = ∅ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    rw [← frontier_compl]
    exact interior_frontier hU.isClosed_compl
  | compl s hs h => rwa [frontier_compl]
  | union s _ t _ hs ht =>
    have hS : Dense (frontier s)ᶜ := by simp [dense_iff_closure_eq, closure_compl, hs]
    have hT : Dense (frontier t)ᶜ := by simp [dense_iff_closure_eq, closure_compl, ht]
    have hD := hS.inter_of_isOpen_left hT isClosed_frontier.isOpen_compl
    rw [← compl_union] at hD
    have hInt : interior (frontier s ∪ frontier t) = ∅ := by
      apply compl_injective
      simpa only [closure_compl, compl_empty] using hD.closure_eq
    have hF : frontier (s ∪ t) ⊆ frontier s ∪ frontier t :=
      (frontier_union_subset s t).trans (union_subset_union inter_subset_left inter_subset_right)
    exact subset_empty_iff.mp ((interior_mono hF).trans hInt.le)

variable [NoetherianSpace X]

private theorem constructible_exists_open_inter_closure {s : Set X}
    (hs : IsConstructible s) (hne : s.Nonempty) :
    ∃ (x : X) (U : Set X), x ∈ s ∧ x ∈ U ∧ IsOpen U ∧ U ∩ closure s ⊆ s := by
  classical
  let C := closure s
  obtain ⟨x, hx⟩ := hne
  letI : Nonempty C := ⟨⟨x, subset_closure hx⟩⟩
  let t : Set C := Subtype.val ⁻¹' s
  have ht : IsConstructible t := hs.preimage continuous_subtype_val
    (fun _ _ _ => by intro _ _ _; exact NoetherianSpace.isCompact _)
  have hImage : Subtype.val '' t = s := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left]
    exact subset_closure
  have hd : Dense t := by
    intro y
    rw [closure_subtype, hImage]
    exact y.2
  have hInt : (interior t).Nonempty := by
    by_contra h
    have hEmpty := not_nonempty_iff_eq_empty.mp h
    have hFront : frontier t = univ := by rw [frontier, hd.closure_eq, hEmpty, diff_empty]
    have hF := constructible_interior_frontier ht
    rw [hFront, interior_univ] at hF
    exact univ_nonempty.ne_empty hF
  obtain ⟨y, hy⟩ := hInt
  obtain ⟨U, hU, hEq⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior t))
  refine ⟨y.val, U, interior_subset (s := t) hy, ?_, hU, ?_⟩
  · change y ∈ Subtype.val ⁻¹' U
    rwa [hEq]
  · intro z hz
    let w : C := ⟨z, hz.2⟩
    have hw : w ∈ Subtype.val ⁻¹' U := hz.1
    rw [hEq] at hw
    exact interior_subset (s := t) hw

variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

private theorem orbit_isLocallyClosed (x : X) (h : IsConstructible (MulAction.orbit G x)) :
    IsLocallyClosed (MulAction.orbit G x) := by
  let O := MulAction.orbit G x
  obtain ⟨y, U, hy, hyU, hU, hSub⟩ := constructible_exists_open_inter_closure h
    ⟨x, MulAction.mem_orbit_self x⟩
  obtain ⟨g₀, hg₀⟩ := hy
  refine ((isLocallyClosed_tfae O).out 3 0).mp ?_
  intro z hz
  obtain ⟨g, hg⟩ := hz
  let e : X ≃ₜ X := Homeomorph.smul (g * g₀⁻¹)
  have he : e y = z := by
    change g₀ • x = y at hg₀
    change g • x = z at hg
    change (g * g₀⁻¹) • y = z
    rw [← hg₀, mul_smul, inv_smul_smul, hg]
  have hCl : e '' closure O = closure O := by
    rw [e.image_closure]
    change closure ((g * g₀⁻¹) • O) = closure O
    rw [MulAction.smul_orbit]
  refine ⟨e '' U, ⟨y, hyU, he⟩, e.isOpenMap U hU, ?_⟩
  rintro w ⟨⟨a, ha, rfl⟩, hw⟩
  rw [← hCl] at hw
  obtain ⟨b, hb, hbEq⟩ := hw
  have hba : b = a := e.injective hbEq
  exact MulAction.mapsTo_smul_orbit _ _ (hSub ⟨ha, hba ▸ hb⟩)

/-- The closure of a smallest orbit contains no other orbit. -/
theorem exists_closed_orbit [Nonempty X] (h : ∀ x : X, IsConstructible (MulAction.orbit G x)) :
    ∃ x : X, IsClosed (MulAction.orbit G x) := by
  classical
  let C (x : X) : Closeds X := ⟨closure (MulAction.orbit G x), isClosed_closure⟩
  obtain ⟨_, ⟨x, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds X)).has_min (range C) (range_nonempty C)
  let O := MulAction.orbit G x
  let B := closure O \ O
  have hB : IsClosed B := by
    have hOpen := (orbit_isLocallyClosed x (h x)).isOpen_coborder
    simpa only [coborder, compl_compl] using hOpen.isClosed_compl
  refine ⟨x, Classical.byContradiction ?_⟩
  intro hx
  have hneq : closure O ≠ O := by
    intro he
    apply hx
    change IsClosed O
    rw [← he]
    exact isClosed_closure
  have hne : B.Nonempty := Set.nonempty_of_not_subset (fun hle => hneq (hle.antisymm subset_closure))
  obtain ⟨y, hy⟩ := hne
  have hY : MulAction.orbit G y ⊆ B := by
    intro z hz
    obtain ⟨g, rfl⟩ := hz
    refine ⟨?_, ?_⟩
    · exact smul_closure_orbit_subset g x ⟨y, hy.1, rfl⟩
    · intro hg
      have ht := MulAction.mapsTo_smul_orbit g⁻¹ x hg
      change g⁻¹ • (g • y) ∈ O at ht
      rw [inv_smul_smul] at ht
      exact hy.2 ht
  have hYc := closure_minimal hY hB
  have hle : C y ≤ C x := hYc.trans diff_subset
  have hneC : C y ≠ C x := by
    intro he
    have hxC : x ∈ (C y : Set X) := he.symm ▸ subset_closure (MulAction.mem_orbit_self x)
    exact (hYc hxC).2 (MulAction.mem_orbit_self x)
  exact hmin (C y) ⟨y, rfl⟩ (lt_of_le_of_ne hle hneC)

end WideE
