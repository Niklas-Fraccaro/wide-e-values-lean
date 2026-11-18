import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.RelSeries
import Mathlib.RingTheory.Artinian.Module

/-! Composition flags of finite-dimensional Lie modules and bases adapted to them. -/

noncomputable section

open scoped Matrix

namespace WideE

section SubmoduleBases

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Choose compatible independent spanning sets along a finite increasing flag. -/
private theorem exists_flagBasisSets {r : ℕ} (W : Fin (r + 1) → Submodule k V)
    (hW : Monotone W) (h0 : W 0 = ⊥) :
    ∃ B : Fin (r + 1) → Set V, B 0 = ∅ ∧ Monotone B ∧
      ∀ i, LinearIndepOn k id (B i) ∧ Submodule.span k (B i) = W i := by
  let Sets (i : Fin (r + 1)) := {t : Set V // LinearIndepOn k id t ∧ Submodule.span k t = W i}
  let start : Sets 0 := ⟨∅, linearIndepOn_empty k id, by rw [Submodule.span_empty, h0]⟩
  let hSub (i : Fin r) (A : Sets i.castSucc) : A.val ⊆ (W i.succ : Set V) := fun x hx =>
    hW (Fin.castSucc_le_succ i) (A.property.2 ▸ Submodule.subset_span hx)
  let next (i : Fin r) (A : Sets i.castSucc) : Sets i.succ :=
    ⟨A.property.1.extend (hSub i A), A.property.1.linearIndepOn_extend _,
      (A.property.1.span_extend_eq_span _).trans (Submodule.span_eq (W i.succ))⟩
  let B (i : Fin (r + 1)) : Sets i := Fin.induction start next i
  refine ⟨fun i => (B i).val, rfl, Fin.monotone_iff_le_succ.mpr ?_, fun i => (B i).property⟩
  intro i
  change (B i.castSucc).val ⊆ (B i.succ).val
  have hstep : B i.succ = next i (B i.castSucc) := Fin.induction_succ start next i
  rw [hstep]
  exact (B i.castSucc).property.1.subset_extend (hSub i (B i.castSucc))

/-- Reindex any finite family so that its values in a linear order increase. -/
private theorem exists_monotone_reindex {α β : Type*} [Fintype α] [LinearOrder β]
    {d : ℕ} (hd : Fintype.card α = d) (f : α → β) :
    ∃ e : Fin d ≃ α, Monotone (f ∘ e) := by
  classical
  let t := Fintype.equivFin α
  let g (a : α) : β ×ₗ Fin (Fintype.card α) := toLex (f a, t a)
  have hg : Function.Injective g := fun _ _ h =>
    t.injective (congrArg (fun x : β ×ₗ Fin (Fintype.card α) => (ofLex x).2) h)
  letI : LinearOrder α := LinearOrder.lift' g hg
  let e := Fintype.orderIsoFinOfCardEq α hd
  refine ⟨e.toEquiv, fun i j hij => ?_⟩
  exact Prod.Lex.monotone_fst_ofLex (show g (e i) ≤ g (e j) from e.monotone hij)

/-- A finite flag from zero to the whole space has a basis ordered by first appearance. -/
theorem exists_basis_adapted_to_flag [FiniteDimensional k V]
    {r : ℕ} (W : Fin (r + 1) → Submodule k V) (hW : Monotone W)
    (h0 : W 0 = ⊥) (hTop : W (Fin.last r) = ⊤) :
    ∃ (v : Basis (Fin (Module.finrank k V)) k V) (b : Fin (Module.finrank k V) → Fin r),
      Monotone b ∧ ∀ t : Fin (r + 1),
        Submodule.span k (v '' {i | (b i).val < t.val}) = W t := by
  classical
  obtain ⟨B, hB0, hMono, hB⟩ := exists_flagBasisSets W hW h0
  let A := B (Fin.last r)
  let v : Basis A k V := Basis.mk ((hB (Fin.last r)).1.linearIndependent_restrict) (by
    change ⊤ ≤ Submodule.span k (Set.range ((↑) : A → V))
    rw [Subtype.range_coe, show Submodule.span k A = ⊤ from (hB (Fin.last r)).2.trans hTop])
  have hv (a : A) : v a = a.val := Basis.mk_apply _ _ _
  letI : Fintype A := FiniteDimensional.fintypeBasisIndex v
  let T (a : A) := Finset.univ.filter fun i : Fin (r + 1) => a.val ∈ B i
  have hT (a : A) : (T a).Nonempty :=
    ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property⟩⟩
  let first (a : A) := (T a).min' (hT a)
  have hfirst (a : A) (i : Fin (r + 1)) : a.val ∈ B i ↔ first a ≤ i := by
    constructor
    · intro hi
      exact (T a).min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro hi
      exact hMono hi (Finset.mem_filter.mp ((T a).min'_mem (hT a))).2
  have hpos (a : A) : 0 < (first a).val := by
    have hn : first a ≠ 0 := by
      intro h
      have hmem := (hfirst a (first a)).mpr le_rfl
      rwa [h, hB0] at hmem
    exact (Fin.pos_iff_ne_zero.mpr hn)
  let block (a : A) : Fin r := ⟨(first a).val - 1, by
    have h := (first a).isLt
    have := hpos a
    omega⟩
  have hb (a : A) (i : Fin (r + 1)) : (block a).val < i.val ↔ a.val ∈ B i := by
    rw [hfirst]
    change (first a).val - 1 < i.val ↔ (first a).val ≤ i.val
    have := hpos a
    omega
  obtain ⟨e, he⟩ := exists_monotone_reindex (Module.finrank_eq_card_basis v).symm block
  refine ⟨v.reindex e.symm, block ∘ e, he, fun t => ?_⟩
  rw [← (hB t).2]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    change (block (e i)).val < t.val at hi
    simpa only [Basis.reindex_apply, Equiv.symm_symm, hv] using (hb (e i) t).mp hi
  · intro hx
    let a : A := ⟨x, hMono (Fin.le_last t) hx⟩
    refine ⟨e.symm a, ?_, ?_⟩
    · change (block (e (e.symm a))).val < t.val
      rw [Equiv.apply_symm_apply]
      exact (hb a t).mpr hx
    · simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply, hv, a]

theorem basis_repr_zero_of_mem_flag {d r : ℕ}
    (v : Basis (Fin d) k V) (b : Fin d → Fin r) (W : Fin (r + 1) → Submodule k V)
    (hW : ∀ t : Fin (r + 1), Submodule.span k (v '' {i | (b i).val < t.val}) = W t)
    {t : Fin (r + 1)} {i : Fin d} (hi : ¬ (b i).val < t.val) {x : V}
    (hx : x ∈ W t) : v.repr x i = 0 := by
  rw [← hW] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    rw [Basis.repr_self, Finsupp.single_eq_of_ne hji]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

/-- A flag-preserving linear map is block upper triangular in an adapted basis. -/
theorem toMatrix_blockTriangular_of_preserves_flag {d r : ℕ}
    (v : Basis (Fin d) k V) (b : Fin d → Fin r) (W : Fin (r + 1) → Submodule k V)
    (hW : ∀ t : Fin (r + 1), Submodule.span k (v '' {i | (b i).val < t.val}) = W t)
    (f : V →ₗ[k] V) (hf : ∀ t, W t ≤ (W t).comap f) :
    (LinearMap.toMatrix v v f).BlockTriangular b := by
  intro i j hij
  let t := (b j).succ
  have hj : v j ∈ W t := by
    rw [← hW]
    exact Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩
  rw [LinearMap.toMatrix_apply]
  have hi : ¬ (b i).val < t.val := Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hij)
  exact basis_repr_zero_of_mem_flag v b W hW hi (hf t hj)

end SubmoduleBases

section LieModule

variable {k L V : Type*} [Field k] [LieRing L]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [FiniteDimensional k V]

/-- A finite-dimensional Lie module has a flag with genuine cover relations. -/
theorem exists_lieCompositionFlag :
    ∃ s : RelSeries (fun P Q : LieSubmodule k L V => P ⋖ Q), s.head = ⊥ ∧ s.last = ⊤ := by
  letI := LieSubmodule.wellFoundedLT_of_isArtinian k L V
  obtain ⟨f, h0, n, hTop, hStep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (LieSubmodule k L V)
  exact ⟨⟨n, fun i => f i, fun i => hStep i i.isLt⟩, h0.eq_bot, hTop.eq_top⟩

/-- A finite-dimensional Lie module has an ordered basis adapted to its composition flag. -/
theorem exists_lieCompositionBasis :
    ∃ (s : RelSeries (fun P Q : LieSubmodule k L V => P ⋖ Q))
      (v : Basis (Fin (Module.finrank k V)) k V) (b : Fin (Module.finrank k V) → Fin s.length),
      s.head = ⊥ ∧ s.last = ⊤ ∧ Monotone b ∧
      ∀ t : Fin (s.length + 1), Submodule.span k (v '' {i | (b i).val < t.val}) = (s t).toSubmodule := by
  obtain ⟨s, h0, hTop⟩ := exists_lieCompositionFlag (k := k) (L := L) (V := V)
  have hMono : Monotone fun t => (s t).toSubmodule := Fin.monotone_iff_le_succ.mpr fun i =>
    (LieSubmodule.toSubmodule_le_toSubmodule _ _).mpr (s.step i).le
  have h0' : (s 0).toSubmodule = ⊥ := congrArg LieSubmodule.toSubmodule h0
  have hTop' : (s (Fin.last s.length)).toSubmodule = ⊤ := congrArg LieSubmodule.toSubmodule hTop
  obtain ⟨v, b, hb, hv⟩ := exists_basis_adapted_to_flag (fun t => (s t).toSubmodule) hMono h0' hTop'
  exact ⟨s, v, b, h0, hTop, hb, hv⟩

end LieModule

section CompositionFactors

variable {k L V : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

/-- Adjacent terms of a composition flag have an irreducible Lie quotient. -/
theorem lieSubmodule_quotient_isIrreducible_of_covBy
    (P Q : LieSubmodule k L V) (h : P ⋖ Q) :
    LieModule.IsIrreducible k L (Q ⧸ P.comap Q.incl) := by
  let N := P.comap Q.incl
  let π := LieSubmodule.Quotient.mk' N
  have hπ : Function.Surjective π := LieSubmodule.Quotient.surjective_mk' N
  have hN : N ≠ ⊤ := fun hTop =>
    not_le_of_gt h.lt (LieSubmodule.comap_incl_eq_top.mp hTop)
  have hNontrivial : (⊥ : LieSubmodule k L (Q ⧸ N)) ≠ ⊤ := by
    intro heq
    have hImage : LieSubmodule.map π ⊤ = ⊥ := by
      rw [LieModuleHom.map_top, (LieModuleHom.range_eq_top π).mpr hπ, heq]
    exact hN (top_unique ((LieSubmodule.Quotient.map_mk'_eq_bot_le N ⊤).mp hImage))
  refine { toNontrivial := ⟨⟨⊥, ⊤, hNontrivial⟩⟩, eq_bot_or_eq_top := ?_ }
  intro S
  let T := (S.comap π).map Q.incl
  have hPT : P ≤ T := by
    intro x hx
    let y : Q := ⟨x, h.le hx⟩
    refine ⟨y, ?_, rfl⟩
    change π y ∈ S
    rw [(LieSubmodule.Quotient.mk_eq_zero N).mpr hx]
    exact S.zero_mem
  have hTQ : T ≤ Q := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  rcases eq_or_lt_of_le hPT with heq | hlt
  · left
    apply eq_bot_iff.mpr
    intro y hy
    obtain ⟨x, rfl⟩ := hπ y
    have hx : Q.incl x ∈ T := ⟨x, hy, rfl⟩
    rw [← heq] at hx
    exact (LieSubmodule.Quotient.mk_eq_zero N).mpr hx
  · right
    have heq : T = Q := (eq_or_lt_of_le hTQ).resolve_right (h.2 hlt)
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hπ y
    have hx : Q.incl x ∈ T := by
      rw [heq]
      exact x.property
    obtain ⟨z, hz, he⟩ := hx
    have he' : z = x := Subtype.ext he
    exact he' ▸ hz

end CompositionFactors

end WideE
