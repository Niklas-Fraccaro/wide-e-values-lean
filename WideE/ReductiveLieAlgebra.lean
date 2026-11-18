import WideE.CartanCriterion
import Mathlib.Algebra.Lie.LieTheorem

/-! A faithful family of irreducible Lie representations gives a reductive Lie algebra. -/

noncomputable section

open LieAlgebra LieModule Module

namespace WideE

section Radical

variable {k L V : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] [AddCommGroup V]
  [Module k V] [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]
  [IsIrreducible k L V]

/-- The solvable radical acts on an irreducible representation by scalar operators. -/
theorem exists_radical_toEnd_eq_smul (x : radical k L) :
    ∃ c : k, toEnd k L V x.val = c • LinearMap.id := by
  letI := nontrivial_of_isIrreducible k L V
  obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable k (radical k L) V
  let W : LieSubmodule k L V := weightSpaceOfIsLieTower k V χ
  haveI : Nontrivial W := hχ
  have hW : W = ⊤ := W.eq_top_of_isIrreducible k L V
  refine ⟨χ x, ?_⟩
  ext v
  have hv : v ∈ W := hW ▸ LieSubmodule.mem_top v
  exact ((mem_weightSpace χ v).mp hv) x

end Radical

section Derived

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

private theorem derivedSeries_one_eq_top_of_isSemisimple [LieAlgebra.IsSemisimple k L] :
    derivedSeries k L 1 = ⊤ := by
  apply top_unique
  rw [← LieAlgebra.IsSemisimple.sSup_atoms_eq_top (R := k) (L := L), sSup_le_iff]
  intro I hI
  change IsAtom I at hI
  have he := lie_eq_self_of_isAtom_of_nonabelian I hI
    (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)
  rw [← he, derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
  exact LieSubmodule.mono_lie le_top le_top

private theorem derivedSeries_one_eq_of_isKilling_compl [FiniteDimensional k L] (S : LieIdeal k L)
    (hComp : IsCompl S (center k L)) [IsKilling k S] : derivedSeries k L 1 = S := by
  have hD := LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_map S 1
  rw [derivedSeries_one_eq_top_of_isSemisimple, ← S.incl.idealRange_eq_map,
    S.incl_idealRange, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero] at hD
  have hZ : ⁅center k L, S⁆ = ⊥ := by
    rw [LieSubmodule.lie_comm]
    exact ideal_oper_maxTrivSubmodule_eq_bot k L L S
  rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    ← hComp.sup_eq_top, LieSubmodule.sup_lie, LieSubmodule.lie_sup, LieSubmodule.lie_sup]
  simp only [hZ, ideal_oper_maxTrivSubmodule_eq_bot, sup_bot_eq, bot_sup_eq]
  exact hD.symm

end Derived

section Complement

variable {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

omit [CharZero k] [IsAlgClosed k] in
private theorem hasTrivialRadical_of_central_complement (S : LieIdeal k L)
    (hRad : radical k L = center k L) (hComp : IsCompl S (center k L)) : HasTrivialRadical k S := by
  apply hasTrivialRadical_of_no_solvable_ideals
  intro X hX
  let Y : LieIdeal k L :=
    { toSubmodule := X.toSubmodule.map S.toSubmodule.subtype
      lie_mem := by
        rintro a _ ⟨x, hx, rfl⟩
        have ha : a ∈ S ⊔ center k L := hComp.sup_eq_top ▸ LieSubmodule.mem_top a
        obtain ⟨s, hs, z, hz, rfl⟩ := (LieSubmodule.mem_sup _ _ a).mp ha
        have hz' : ⁅z, (x : L)⁆ = 0 := by
          rw [← lie_skew, (mem_maxTrivSubmodule k L L z).mp hz (x : L), neg_zero]
        refine ⟨⁅(⟨s, hs⟩ : S), x⁆, X.lie_mem hx, ?_⟩
        change ⁅s, (x : L)⁆ = ⁅s + z, (x : L)⁆
        rw [add_lie, hz', add_zero] }
  let f : X →ₗ⁅k⁆ Y :=
    { toLinearMap := (S.toSubmodule.subtype.comp X.toSubmodule.subtype).codRestrict Y.toSubmodule
        (fun x => ⟨x.val, x.property, rfl⟩)
      map_lie' := fun {_ _} => rfl }
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  letI : IsSolvable X := hX
  have hY : Y ≤ center k L := hRad ▸
    (LieIdeal.solvable_iff_le_radical k L Y).mp hf.lieAlgebra_isSolvable
  apply (LieSubmodule.eq_bot_iff X).mpr
  intro x hx
  have hxY : (x : L) ∈ Y := ⟨x, hx, rfl⟩
  have hx' : (x : L) ∈ S ⊓ center k L := ⟨x.property, hY hxY⟩
  rw [hComp.inf_eq_bot] at hx'
  exact Subtype.ext hx'

end Complement

section Faithful

variable {k L ι : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
  (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, LieRingModule L (V i)] [∀ i, LieModule k L (V i)] [∀ i, FiniteDimensional k (V i)]
  [∀ i, IsIrreducible k L (V i)]

/-- If a family of irreducible representations is jointly faithful, its Lie algebra is the
direct sum of its center and an ideal with nondegenerate Killing form. -/
theorem exists_isKilling_complement_center_of_faithful_family
    (hFaith : ∀ x : L, (∀ i (v : V i), ⁅x, v⁆ = 0) → x = 0) :
    ∃ S : LieIdeal k L, IsCompl S (center k L) ∧ IsKilling k S := by
  let ρ (i : ι) := toEnd k L (V i)
  have hRad : radical k L = center k L := by
    refine le_antisymm (fun x hx => (mem_maxTrivSubmodule k L L x).mpr ?_) (center_le_radical k L)
    intro y
    apply hFaith
    intro i v
    obtain ⟨c, hc⟩ := exists_radical_toEnd_eq_smul (V := V i) ⟨x, hx⟩
    change ρ i x = c • LinearMap.id at hc
    have hg : ρ i ⁅y, x⁆ = 0 := by
      rw [LieHom.map_lie, hc, lie_smul, (ρ i y).commute_id_right.lie_eq, smul_zero]
    exact LinearMap.congr_fun hg v
  let T : L →ₗ[k] (ι → k) := LinearMap.pi fun i =>
    (LinearMap.trace k (V i)).comp (ρ i).toLinearMap
  have hTraceBracket (x y : L) : T ⁅x, y⁆ = 0 := by
    funext i
    change LinearMap.trace k (V i) (ρ i ⁅x, y⁆) = 0
    rw [LieHom.map_lie, LinearMap.trace_lie]
  let Z := center k L
  let θ : Z →ₗ[k] (ι → k) := T.comp Z.toSubmodule.subtype
  have hθ : LinearMap.ker θ = ⊥ := by
    apply LinearMap.ker_eq_bot_of_injective
    apply (injective_iff_map_eq_zero θ).mpr
    intro x hx
    apply Subtype.ext
    apply hFaith
    intro i v
    have hr : (x : L) ∈ radical k L := hRad.symm ▸ x.property
    obtain ⟨c, hc⟩ := exists_radical_toEnd_eq_smul (k := k) (L := L) (V := V i) ⟨(x : L), hr⟩
    change ρ i x = c • LinearMap.id at hc
    have hci := congrFun hx i
    change LinearMap.trace k (V i) (ρ i x) = 0 at hci
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul] at hci
    letI := nontrivial_of_isIrreducible k L (V i)
    have hDim : (finrank k (V i) : k) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
    have hC := (mul_eq_zero.mp hci).resolve_right hDim
    change ρ i x v = 0
    rw [hc, hC, zero_smul, LinearMap.zero_apply]
  obtain ⟨q, hq⟩ := θ.exists_leftInverse_of_injective hθ
  let π : L →ₗ[k] Z := q.comp T
  have hπ (z : Z) : π z.val = z := LinearMap.congr_fun hq z
  let S : LieIdeal k L :=
    { toSubmodule := LinearMap.ker π
      lie_mem := fun {x y} _ => by
        change q (T ⁅x, y⁆) = 0
        rw [hTraceBracket, map_zero] }
  have hComp : IsCompl S Z := by
    constructor
    · rw [disjoint_iff]
      apply (LieSubmodule.eq_bot_iff (S ⊓ Z)).mpr
      rintro x ⟨hxS, hxZ⟩
      have h := hπ ⟨x, hxZ⟩
      change π x = 0 at hxS
      rw [hxS] at h
      exact congrArg Subtype.val h.symm
    · rw [codisjoint_iff]
      apply top_unique
      intro x _
      refine (LieSubmodule.mem_sup S Z x).mpr ⟨x - (π x : L), ?_, π x, (π x).property,
        sub_add_cancel _ _⟩
      change π (x - (π x : L)) = 0
      rw [map_sub, hπ, sub_self]
  haveI := hasTrivialRadical_of_central_complement S hRad hComp
  exact ⟨S, hComp, isKilling_of_hasTrivialRadical⟩

/-- The derived ideal of a Lie algebra with a jointly faithful family of irreducibles is
semisimple and complements the center. -/
theorem derived_isKilling_and_isCompl_center_of_faithful_family
    (hFaith : ∀ x : L, (∀ i (v : V i), ⁅x, v⁆ = 0) → x = 0) :
    IsKilling k (derivedSeries k L 1) ∧ IsCompl (derivedSeries k L 1) (center k L) := by
  obtain ⟨S, hComp, hK⟩ := exists_isKilling_complement_center_of_faithful_family (k := k) V hFaith
  letI := hK
  rw [derivedSeries_one_eq_of_isKilling_compl S hComp]
  exact ⟨hK, hComp⟩

end Faithful

end WideE
