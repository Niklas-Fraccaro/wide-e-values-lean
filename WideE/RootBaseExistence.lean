/-
The chamber proof follows the construction in mathlib's
Mathlib/LinearAlgebra/RootSystem/BaseExists.lean.
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under the Apache License, Version 2.0. See LICENSE-MATHLIB.
-/
import Mathlib.LinearAlgebra.RootSystem.BaseChange
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Base existence for a finite crystallographic root system

On the rational root system, choose a functional nonzero on all roots.
The indecomposable positive roots are independent by positivity of the root
form. The perfect pairing over the rationals transports independence to
the original field.
-/

noncomputable section

open Function Set Finset
open scoped BigOperators

namespace WideE

section FiniteChamber

variable {ι M : Type*} [AddCommGroup M] [Module ℚ M]

private theorem exists_generic_functional [Fintype ι] (v : ι → M) (hv : ∀ i, v i ≠ 0) :
    ∃ f : M →ₗ[ℚ] ℚ, ∀ i, f (v i) ≠ 0 := by
  classical
  have claim (t : Finset ι) : ∃ f : M →ₗ[ℚ] ℚ, ∀ i ∈ t, f (v i) ≠ 0 := by
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert i t hi ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨g, hg⟩ : ∃ g : M →ₗ[ℚ] ℚ, g (v i) ≠ 0 := by
        by_contra! h
        exact hv i ((Module.forall_dual_apply_eq_zero_iff ℚ _).mp h)
      let forbidden := (insert i t).image (fun j => -f (v j) / g (v j))
      obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset forbidden
      refine ⟨f + c • g, fun j hj hz => ?_⟩
      change f (v j) + c * g (v j) = 0 at hz
      by_cases hjg : g (v j) = 0
      · have hji : j ≠ i := fun h => hg (h ▸ hjg)
        exact hf j ((mem_insert.mp hj).resolve_left hji) (by simpa [hjg] using hz)
      · apply hc
        refine mem_image.mpr ⟨j, hj, ?_⟩
        apply (div_eq_iff hjg).mpr
        linarith
  obtain ⟨f, hf⟩ := claim univ
  exact ⟨f, fun i => hf i (mem_univ i)⟩

/-- The indecomposable positive indices for a finite family of vectors. -/
private def simpleIndices (v : ι → M) (f : M →ₗ[ℚ] ℚ) : Set ι :=
  {i | 0 < f (v i) ∧ ∀ j, 0 < f (v j) → ∀ l, 0 < f (v l) → v i ≠ v j + v l}

private theorem mem_closure_simpleIndices_of_pos [Fintype ι] (v : ι → M)
    (f : M →ₗ[ℚ] ℚ) {i : ι} (hi : 0 < f (v i)) :
    v i ∈ AddSubmonoid.closure (v '' simpleIndices v f) := by
  classical
  let C := AddSubmonoid.closure (v '' simpleIndices v f)
  by_contra h
  let t := univ.filter fun j => 0 < f (v j) ∧ v j ∉ C
  obtain ⟨j, hj, hmin⟩ := t.exists_min_image (fun j => f (v j))
    ⟨i, mem_filter.mpr ⟨mem_univ i, hi, h⟩⟩
  obtain ⟨hjpos, hjmem⟩ := (mem_filter.mp hj).2
  have hjs : j ∉ simpleIndices v f :=
    fun hs => hjmem (AddSubmonoid.subset_closure (mem_image_of_mem _ hs))
  have hDecomp : ∃ p, 0 < f (v p) ∧ ∃ q, 0 < f (v q) ∧ v j = v p + v q := by
    simpa only [simpleIndices, mem_setOf_eq, hjpos, true_and, not_forall, not_ne_iff,
      Classical.not_imp, exists_prop] using hjs
  obtain ⟨p, hp, q, hq, he⟩ := hDecomp
  have heft : f (v j) = f (v p) + f (v q) := by rw [he, map_add]
  have hlt (l : ι) (hl : 0 < f (v l)) (hstrict : f (v l) < f (v j)) : v l ∈ C := by
    by_cases hl' : v l ∈ C
    · exact hl'
    · exact False.elim ((not_lt_of_ge (hmin l (mem_filter.mpr ⟨mem_univ l, hl, hl'⟩))) hstrict)
  exact hjmem (he ▸ C.add_mem (hlt p hp (by linarith)) (hlt q hq (by linarith)))

private theorem root_or_neg_mem_closure_simpleIndices [Fintype ι] (v : ι → M)
    (f : M →ₗ[ℚ] ℚ) (hf : ∀ i, f (v i) ≠ 0)
    (opp : ι → ι) (hopp : ∀ i, v (opp i) = -v i) (i : ι) :
    v i ∈ AddSubmonoid.closure (v '' simpleIndices v f) ∨
      -v i ∈ AddSubmonoid.closure (v '' simpleIndices v f) := by
  rcases lt_or_gt_of_ne (hf i) with h | h
  · right
    rw [← hopp]
    exact mem_closure_simpleIndices_of_pos v f (by rw [hopp, map_neg]; exact neg_pos.mpr h)
  · exact Or.inl (mem_closure_simpleIndices_of_pos v f h)

private theorem simpleIndices_sub_not_mem_range (v : ι → M)
    (f : M →ₗ[ℚ] ℚ) (hf : ∀ i, f (v i) ≠ 0)
    (opp : ι → ι) (hopp : ∀ i, v (opp i) = -v i)
    {i j : ι} (hi : i ∈ simpleIndices v f) (hj : j ∈ simpleIndices v f) :
    v i - v j ∉ Set.range v := by
  rintro ⟨q, hq⟩
  rcases lt_or_gt_of_ne (hf q) with h | h
  · have ho : 0 < f (v (opp q)) := by rw [hopp, map_neg]; exact neg_pos.mpr h
    apply hj.2 i hi.1 (opp q) ho
    rw [hopp, hq]
    abel
  · apply hi.2 j hj.1 q h
    rw [hq]
    abel

private theorem linearIndependent_of_pairwise_nonpos [Fintype ι]
    (B : LinearMap.BilinForm ℚ M) (hB : ∀ x : M, x ≠ 0 → 0 < B x x)
    (v : ι → M) (f : M →ₗ[ℚ] ℚ) (hf : ∀ i, 0 < f (v i))
    (hOffdiag : Pairwise fun i j => B (v i) (v j) ≤ 0) :
    LinearIndependent ℚ v := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  let p (j : ι) := max (c j) 0
  let n (j : ι) := max (-c j) 0
  let x := ∑ j, p j • v j
  let y := ∑ j, n j • v j
  have hpn (j : ι) : p j - n j = c j := by
    by_cases h : 0 ≤ c j
    · simp [p, n, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    · have h' := le_of_not_ge h
      simp [p, n, max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
  have hxy : x = y := by
    apply sub_eq_zero.mp
    simpa only [x, y, ← Finset.sum_sub_distrib, ← sub_smul, hpn] using hc
  have hpos (j : ι) : 0 ≤ p j := le_max_right _ _
  have hneg (j : ι) : 0 ≤ n j := le_max_right _ _
  have hcross : B x y ≤ 0 := by
    simp only [x, y, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_nonpos
    intro j hj
    apply Finset.sum_nonpos
    intro l hl
    by_cases h : j = l
    · subst l
      by_cases hjc : 0 ≤ c j
      · simp [n, max_eq_right (neg_nonpos.mpr hjc)]
      · have hp : p j = 0 := max_eq_right (le_of_not_ge hjc)
        simp [hp]
    · exact mul_nonpos_of_nonneg_of_nonpos (hneg j)
        (mul_nonpos_of_nonneg_of_nonpos (hpos l) (hOffdiag (fun h' => h h'.symm)))
  have hx : x = 0 := by
    by_cases hx : x = 0
    · exact hx
    · rw [← hxy] at hcross
      exact False.elim ((not_lt_of_ge hcross) (hB x hx))
  have hy : y = 0 := hxy ▸ hx
  have hpi : p i = 0 := by
    have hsum : ∑ j, p j * f (v j) = 0 := by
      simpa [x, map_sum, map_smul] using congrArg f hx
    have hprod := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (hpos j) (hf j).le).mp hsum i (mem_univ i)
    exact (mul_eq_zero.mp hprod).resolve_right (hf i).ne'
  have hni : n i = 0 := by
    have hsum : ∑ j, n j * f (v j) = 0 := by
      simpa [y, map_sum, map_smul] using congrArg f hy
    have hprod := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (hneg j) (hf j).le).mp hsum i (mem_univ i)
    exact (mul_eq_zero.mp hprod).resolve_right (hf i).ne'
  simpa [hpi, hni] using (hpn i).symm

end FiniteChamber

section RationalRootSystem

variable {ι M N : Type*} [Fintype ι] [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N] (P : RootSystem ι ℚ M N) [P.IsCrystallographic]

omit [P.IsCrystallographic] in
private theorem rationalRootForm_pos {x : M} (hx : x ≠ 0) : 0 < P.RootForm x x :=
  P.rootForm_pos_of_ne_zero (by
    change x ∈ Submodule.span ℚ (Set.range P.root)
    rw [P.span_root_eq_top]
    exact Submodule.mem_top) hx

private theorem simpleIndices_root_linearIndependent (f : M →ₗ[ℚ] ℚ)
    (hf : ∀ i, f (P.root i) ≠ 0) :
    LinearIndependent ℚ (fun i : simpleIndices P.root f => P.root i) := by
  classical
  letI : Fintype (simpleIndices P.root f) := Fintype.ofFinite _
  have hOpp (i : ι) : P.root (P.reflection_perm i i) = -P.root i := by simp
  refine linearIndependent_of_pairwise_nonpos P.RootForm (fun _ hx => rationalRootForm_pos P hx)
    _ f (fun i => i.property.1) ?_
  intro i j hij
  have hji : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
  have hInt : P.pairingIn ℤ i j ≤ 0 := by
    apply le_of_not_gt
    intro h
    exact simpleIndices_sub_not_mem_range P.root f hf _ hOpp i.property j.property
      (P.root_sub_root_mem_of_pairingIn_pos h hji)
  have hRat : P.pairing i j ≤ 0 := by
    rw [← P.algebraMap_pairingIn ℤ]
    change (↑(P.pairingIn ℤ i j) : ℚ) ≤ 0
    exact_mod_cast hInt
  have hB := congrArg (P.toPerfectPairing (P.root i)) (P.rootForm_self_smul_coroot j)
  simp only [map_smul, map_nsmul, smul_eq_mul, P.root_coroot_eq_pairing,
    P.toPerfectPairing_apply_apply_Polarization, nsmul_eq_mul] at hB
  have hSym : P.RootForm (P.root j) (P.root i) = P.RootForm (P.root i) (P.root j) :=
    P.rootForm_symmetric.eq _ _
  rw [hSym] at hB
  have hNonPos := mul_nonpos_of_nonneg_of_nonpos
    (rationalRootForm_pos P (P.ne_zero j)).le hRat
  rw [hB] at hNonPos
  by_contra! h
  exact (not_lt_of_ge hNonPos) (mul_pos (by norm_num) h)

private def simpleRootBasis (f : M →ₗ[ℚ] ℚ) (hf : ∀ i, f (P.root i) ≠ 0) :
    Basis (simpleIndices P.root f) ℚ M := by
  classical
  let s := simpleIndices P.root f
  have hOpp (i : ι) : P.root (P.reflection_perm i i) = -P.root i := by simp
  refine Basis.mk (simpleIndices_root_linearIndependent P f hf) ?_
  rw [← P.span_root_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  let V := Submodule.span ℚ (Set.range (fun j : s => P.root j))
  have hV : AddSubmonoid.closure (P.root '' s) ≤ V.toAddSubmonoid :=
    AddSubmonoid.closure_le.mpr (by
      rintro _ ⟨j, hj, rfl⟩
      exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  rcases root_or_neg_mem_closure_simpleIndices P.root f hf _ hOpp i with h | h
  · exact hV h
  · exact (Submodule.neg_mem_iff V).mp (hV h)

omit [P.IsCrystallographic] in
private theorem coPolarization_coroot_eq (i : ι) :
    P.CoPolarization (P.coroot i) =
      (P.CorootForm (P.coroot i) (P.coroot i) / 2) • P.root i := by
  calc
    P.CoPolarization (P.coroot i) = (2 : ℚ)⁻¹ • (2 • P.CoPolarization (P.coroot i)) := by
      rw [two_nsmul, ← two_smul ℚ, smul_smul]
      norm_num
    _ = _ := by rw [← P.corootForm_self_smul_root, smul_smul, div_eq_mul_inv, mul_comm]

omit [P.IsCrystallographic] in
private theorem coPolarization_coroot_scale_pos (i : ι) :
    0 < P.CorootForm (P.coroot i) (P.coroot i) / 2 :=
  div_pos (rationalRootForm_pos P.flip (P.flip.ne_zero i)) (by norm_num)

omit [P.IsCrystallographic] in
private theorem coPolarization_positive_iff (f : M →ₗ[ℚ] ℚ) (i : ι) :
    0 < (f.comp P.CoPolarization) (P.coroot i) ↔ 0 < f (P.root i) := by
  simp only [LinearMap.comp_apply, coPolarization_coroot_eq P, map_smul, smul_eq_mul]
  rw [mul_pos_iff_of_pos_left (coPolarization_coroot_scale_pos P i)]

private theorem simpleIndices_root_subset_coroot [P.IsReduced] (f : M →ₗ[ℚ] ℚ)
    (hf : ∀ i, f (P.root i) ≠ 0) :
    simpleIndices P.root f ⊆ simpleIndices P.coroot (f.comp P.CoPolarization) := by
  classical
  let s := simpleIndices P.root f
  let b := simpleRootBasis P f hf
  have hBasis (w : s) : b w = P.root w := by simp only [b, simpleRootBasis, Basis.mk_apply]
  have hNonnegative (w : s) {j : ι} (hj : 0 < f (P.root j)) :
      0 ≤ b.coord w (P.root j) := by
    refine AddSubmonoid.closure_induction (motive := fun x _ => 0 ≤ b.coord w x)
      ?_ (by simp) ?_ (mem_closure_simpleIndices_of_pos P.root f hj)
    · rintro x ⟨l, hl, rfl⟩
      rw [← hBasis ⟨l, hl⟩, Basis.coord_apply, Basis.repr_self_apply]
      split <;> norm_num
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_nonneg hx hy
  intro i hi
  refine ⟨(coPolarization_positive_iff P f i).mpr hi.1, ?_⟩
  intro j hj l hl hDecomp
  have hPosJ := (coPolarization_positive_iff P f j).mp hj
  have hPosL := (coPolarization_positive_iff P f l).mp hl
  let q (z : ι) := P.CorootForm (P.coroot z) (P.coroot z) / 2
  have hScale := congrArg P.CoPolarization hDecomp
  simp only [map_add, coPolarization_coroot_eq P] at hScale
  change q i • P.root i = q j • P.root j + q l • P.root l at hScale
  let i₀ : s := ⟨i, hi⟩
  have hZero (w : s) (hw : w ≠ i₀) : b.coord w (P.root j) = 0 := by
    have hiZero : b.coord w (P.root i) = 0 := by
      rw [show P.root i = b i₀ from (hBasis i₀).symm, Basis.coord_apply,
        Basis.repr_self_apply, if_neg (Ne.symm hw)]
    have h := congrArg (b.coord w) hScale
    simp only [map_add, map_smul, smul_eq_mul, hiZero, mul_zero] at h
    have hp := mul_nonneg (coPolarization_coroot_scale_pos P j).le (hNonnegative w hPosJ)
    have hq := mul_nonneg (coPolarization_coroot_scale_pos P l).le (hNonnegative w hPosL)
    change 0 ≤ q j * b.coord w (P.root j) at hp
    change 0 ≤ q l * b.coord w (P.root l) at hq
    have hz : q j * b.coord w (P.root j) = 0 :=
      le_antisymm ((le_add_of_nonneg_right hq).trans h.symm.le) hp
    exact (mul_eq_zero.mp hz).resolve_left (coPolarization_coroot_scale_pos P j).ne'
  let c := b.coord i₀ (P.root j)
  have hRootJ : P.root j = c • P.root i := by
    apply b.repr.injective
    ext w
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, show P.root i = b i₀ from (hBasis i₀).symm,
      Basis.repr_self_apply]
    by_cases hw : w = i₀
    · subst w
      simp [c, Basis.coord_apply]
    · rw [if_neg (Ne.symm hw), mul_zero]
      exact hZero w hw
  have hPair : ¬ LinearIndependent ℚ ![P.root i, P.root j] := by
    intro h
    have hcomb : c • P.root i + (-1 : ℚ) • P.root j = 0 := by
      rw [neg_smul, one_smul, hRootJ, add_neg_cancel]
    exact (by norm_num : (-1 : ℚ) ≠ 0) ((LinearIndependent.pair_iff.mp h _ _ hcomb).2)
  have hRoots : P.root i = P.root j := by
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P.toRootPairing) i j hPair with h | h
    · exact h
    · have h' := congrArg f h
      rw [map_neg] at h'
      exact False.elim (by linarith [hi.1])
  have hij : i = j := P.root.injective hRoots
  subst j
  apply P.flip.ne_zero l
  exact add_left_cancel (hDecomp.symm.trans (add_zero (P.coroot i)).symm)

/-- A finite reduced crystallographic root system over the rationals admits a base. -/
theorem rationalRootSystem_nonempty_base [P.IsReduced] : Nonempty P.Base := by
  classical
  letI : P.flip.IsCrystallographic := by
    change P.toRootPairing.flip.IsCrystallographic
    infer_instance
  obtain ⟨f, hf⟩ := exists_generic_functional P.root (fun i => P.ne_zero i)
  let g := f.comp P.CoPolarization
  have hg (i : ι) : g (P.coroot i) ≠ 0 := by
    simp only [g, LinearMap.comp_apply, coPolarization_coroot_eq P, map_smul, smul_eq_mul]
    exact mul_ne_zero (coPolarization_coroot_scale_pos P i).ne' (hf i)
  let b := simpleRootBasis P f hf
  let b' : Basis (simpleIndices P.coroot g) ℚ N := simpleRootBasis P.flip g hg
  letI : Fintype (simpleIndices P.root f) := Fintype.ofFinite _
  letI : FiniteDimensional ℚ M := FiniteDimensional.of_fintype_basis b
  have hCard : (simpleIndices P.root f).ncard = (simpleIndices P.coroot g).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Module.finrank_eq_nat_card_basis b,
      ← Module.finrank_eq_nat_card_basis b', P.toPerfectPairing.finrank_eq]
  have hEq : simpleIndices P.root f = simpleIndices P.coroot g :=
    Set.eq_of_subset_of_ncard_le (simpleIndices_root_subset_coroot P f hf) hCard.ge
  have hOpp (i : ι) : P.root (P.reflection_perm i i) = -P.root i := by simp
  have hOpp' (i : ι) : P.coroot (P.reflection_perm i i) = -P.coroot i := by simp
  refine ⟨⟨simpleIndices P.root f, simpleIndices_root_linearIndependent P f hf, ?_, ?_, ?_⟩⟩
  · rw [hEq]
    exact simpleIndices_root_linearIndependent P.flip g hg
  · exact root_or_neg_mem_closure_simpleIndices P.root f hf _ hOpp
  · rw [hEq]
    exact root_or_neg_mem_closure_simpleIndices P.coroot g hg _ hOpp'

end RationalRootSystem

section ScalarExtension

variable {ι K k M₀ N₀ M N : Type*} [Fintype ι] [Field K] [Field k] [Algebra K k]
  [AddCommGroup M₀] [Module K M₀] [AddCommGroup N₀] [Module K N₀]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

private theorem linearIndependent_of_pairing_extension (b : Basis ι K M₀)
    (p : PerfectPairing K M₀ N₀) (P : PerfectPairing k M N) (v : M₀ → M) (w : N₀ → N)
    (hP : ∀ x y, algebraMap K k (p x y) = P (v x) (w y)) :
    LinearIndependent k (fun i => v (b i)) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
  let y := p.toDualRight.symm (b.coord i)
  let eval := P.flip (w y)
  have hEval (j : ι) : eval (v (b j)) = if j = i then 1 else 0 := by
    change P (v (b j)) (w y) = _
    rw [← hP, PerfectPairing.apply_apply_toDualRight_symm, Basis.coord_apply,
      Basis.repr_self_apply]
    split <;> simp
  have h := congrArg eval hc
  simpa only [map_sum, map_smul, map_zero, smul_eq_mul, hEval, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

private theorem mem_closure_image_of_map {X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y]
    (g : X →+ Y) {s : Set X} {x : X} (hx : x ∈ AddSubmonoid.closure s) :
    g x ∈ AddSubmonoid.closure (g '' s) := by
  refine AddSubmonoid.closure_induction (motive := fun x _ => g x ∈ AddSubmonoid.closure (g '' s))
    (fun y hy => AddSubmonoid.subset_closure (mem_image_of_mem g hy))
    (by
      change g 0 ∈ AddSubmonoid.closure (g '' s)
      rw [map_zero]
      exact AddSubmonoid.zero_mem _) ?_ hx
  intro a b _ _ ha hb
  rw [map_add]
  exact (AddSubmonoid.closure (g '' s)).add_mem ha hb

end ScalarExtension

section GeneralRootSystem

variable {ι k M N : Type*} [Finite ι] [Field k] [CharZero k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- A finite reduced crystallographic root system over a field of characteristic zero admits
a base, obtained by restriction to its rational root system. -/
theorem rootSystem_nonempty_base (P : RootSystem ι k M N) [P.IsCrystallographic] [P.IsReduced] :
    Nonempty P.Base := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Module ℚ M := Module.compHom M (algebraMap ℚ k)
  letI : Module ℚ N := Module.compHom N (algebraMap ℚ k)
  let Q := P.restrictScalars ℚ
  letI : Q.IsCrystallographic := by
    constructor
    intro i j
    obtain ⟨z, hz⟩ := P.exists_value (S := ℤ) i j
    refine ⟨z, (algebraMap ℚ k).injective ?_⟩
    change algebraMap ℚ k (z : ℚ) = algebraMap ℚ k (Q.pairing i j)
    rw [map_intCast, RootPairing.restrictScalars_pairing]
    exact hz
  letI : Q.IsReduced := by
    constructor
    intro i j hij
    have h : ¬ LinearIndependent k ![P.root i, P.root j] := by
      intro hInd
      apply hij
      have hMap : ((P.rootSpan ℚ).subtype ∘ ![Q.root i, Q.root j]) =
          ![P.root i, P.root j] := by
        funext l
        fin_cases l <;> rfl
      apply LinearIndependent.of_comp (P.rootSpan ℚ).subtype
      rw [hMap]
      exact hInd.restrict_scalars' ℚ
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P.toRootPairing) i j h with hr | hr
    · exact Or.inl (Subtype.ext hr)
    · exact Or.inr (Subtype.ext hr)
  obtain ⟨b⟩ := rationalRootSystem_nonempty_base Q
  letI : Fintype b.support := Fintype.ofFinite _
  have hP (x : P.rootSpan ℚ) (y : P.corootSpan ℚ) :
      algebraMap ℚ k (Q.toPerfectPairing x y) = P.toPerfectPairing x.val y.val :=
    P.restrictScalars_toPerfectPairing_apply_apply ℚ _ x y
  refine ⟨⟨b.support, ?_, ?_, ?_, ?_⟩⟩
  · have h := linearIndependent_of_pairing_extension b.toWeightBasis Q.toPerfectPairing
      P.toPerfectPairing Subtype.val Subtype.val hP
    simpa only [RootPairing.Base.toWeightBasis, Basis.mk_apply, Q,
      RootPairing.restrictScalars_coe_root] using h
  · have h := linearIndependent_of_pairing_extension b.toCoweightBasis Q.toPerfectPairing.flip
      P.toPerfectPairing.flip Subtype.val Subtype.val (fun y x => hP x y)
    simpa only [RootPairing.Base.toCoweightBasis, RootPairing.Base.toWeightBasis, Basis.mk_apply, Q,
      RootPairing.restrictScalars_coe_coroot] using h
  · intro i
    have hc {x : P.rootSpan ℚ} (hx : x ∈ AddSubmonoid.closure (Q.root '' b.support)) :
        x.val ∈ AddSubmonoid.closure (P.root '' b.support) := by
      have hx' := mem_closure_image_of_map (P.rootSpan ℚ).subtype.toAddMonoidHom hx
      simpa only [Set.image_image, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply] using hx'
    exact (b.root_mem_or_neg_mem i).imp hc hc
  · intro i
    have hc {y : P.corootSpan ℚ} (hy : y ∈ AddSubmonoid.closure (Q.coroot '' b.support)) :
        y.val ∈ AddSubmonoid.closure (P.coroot '' b.support) := by
      have hy' := mem_closure_image_of_map (P.corootSpan ℚ).subtype.toAddMonoidHom hy
      simpa only [Set.image_image, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply] using hy'
    exact (b.coroot_mem_or_neg_mem i).imp hc hc

end GeneralRootSystem

end WideE
