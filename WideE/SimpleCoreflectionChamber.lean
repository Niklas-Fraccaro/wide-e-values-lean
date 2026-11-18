import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! A permutation of the principal root values is moved back by simple coreflections. -/

noncomputable section

namespace WideE

open Function Set Module

variable {k M N ι : Type*} [Field k] [CharZero k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

section Permutation

variable (P : RootSystem ι k M N) (B : P.Base)

omit [CharZero k] in
private theorem coreflectionClosure_perm_roots {g : N ≃ₗ[k] N}
    (hg : g ∈ Subgroup.closure (Set.range fun i : B.support => P.coreflection i)) :
    ∃ p : Equiv.Perm ι, ∀ x i, P.root' i (g x) = P.root' (p i) x := by
  refine Subgroup.closure_induction (p := fun g _ => ∃ p : Equiv.Perm ι,
    ∀ x i, P.root' i (g x) = P.root' (p i) x) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨i, rfl⟩
    exact ⟨P.reflection_perm i, fun x j => P.flip.coroot'_reflection x⟩
  · exact ⟨Equiv.refl _, fun _ _ => rfl⟩
  · rintro g h _ _ ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p.trans q, fun x i => ?_⟩
    change P.root' i (g (h x)) = P.root' (q (p i)) x
    rw [hp, hq]
  · rintro g _ ⟨p, hp⟩
    refine ⟨p.symm, fun x i => ?_⟩
    have h := hp (g.symm x) (p.symm i)
    rw [g.apply_symm_apply, p.apply_symm_apply] at h
    exact h.symm

omit [CharZero k] in
include B in
private theorem injective_root_values : Function.Injective (fun x : N => fun i => P.root' i x) := by
  intro x y h
  apply P.toDualRight.injective
  apply B.toWeightBasis.ext
  intro i
  simpa only [RootPairing.Base.toWeightBasis, Basis.mk_apply] using congrFun h i

end Permutation

section Chamber

variable [Fintype ι] (P : RootSystem ι k M N) (B : P.Base)

private theorem exists_ratLinearForm_one : ∃ φ : k →ₗ[ℚ] ℚ, φ 1 = 1 := by
  let f := (Algebra.ofId ℚ k).toLinearMap
  have hKer : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot_of_injective
    (FaithfulSMul.algebraMap_injective ℚ k)
  obtain ⟨φ, hφ⟩ := f.exists_leftInverse_of_injective hKer
  refine ⟨φ, ?_⟩
  have h := LinearMap.congr_fun hφ 1
  simpa only [LinearMap.comp_apply, f, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply] using h

private theorem casts_int_of_ratLinearForm (φ : k →ₗ[ℚ] ℚ) (hφ : φ 1 = 1) (n : ℤ) :
    φ (n : k) = (n : ℚ) := by
  rw [← zsmul_one, map_zsmul, hφ, zsmul_one]

set_option maxHeartbeats 900000 in
/-- Any element whose root values are a permutation of the principal root values
is carried to the principal element by a product of simple coreflections. -/
theorem exists_coreflectionClosure_apply_eq_of_permuted_principal_values (h₀ x : N)
    (hSimple : ∀ i : B.support, P.root' i h₀ = 2)
    (hReg : ∀ i, ∃ n : ℤ, n ≠ 0 ∧ P.root' i h₀ = ((2 * n : ℤ) : k))
    (hx : ∃ p : Equiv.Perm ι, ∀ i, P.root' i x = P.root' (p i) h₀) :
    ∃ g ∈ Subgroup.closure (Set.range fun i : B.support => P.coreflection i), g x = h₀ := by
  classical
  letI : Fintype B.support := Fintype.ofFinite _
  let G := Subgroup.closure (Set.range fun i : B.support => P.coreflection i)
  let O := Set.range (fun g : G => g.val x)
  obtain ⟨p, hp⟩ := hx
  have hOrbit (y : N) (hy : y ∈ O) : ∃ r : Equiv.Perm ι, ∀ i, P.root' i y = P.root' (r i) h₀ := by
    obtain ⟨g, rfl⟩ := hy
    obtain ⟨q, hq⟩ := coreflectionClosure_perm_roots P B g.property
    exact ⟨q.trans p, fun i => (hq x i).trans (hp _)⟩
  let E (y : N) (i : ι) := P.root' i y
  have hFinite : O.Finite := by
    apply Set.Finite.of_finite_image (f := E) _ (injective_root_values P B).injOn
    refine (Set.finite_range (fun q : Equiv.Perm ι => fun i => P.root' (q i) h₀)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq⟩ := hOrbit y hy
    exact ⟨q, (funext hq).symm⟩
  obtain ⟨φ, hφ⟩ := exists_ratLinearForm_one (k := k)
  let val (y : N) (i : ι) := φ (P.root' i y)
  let l : N →ₗ[k] k := ∑ i : B.support, B.toCoweightBasis.coord i
  have hl (i : B.support) : l (P.coroot i) = 1 := by
    have he : B.toCoweightBasis i = P.coroot i := by
      rw [RootPairing.Base.toCoweightBasis, RootPairing.Base.toWeightBasis, Basis.mk_apply]
      rfl
    rw [← he]
    simp [l, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  let m (y : N) := φ (l y)
  have hNonempty : O.Nonempty := ⟨x, ⟨1, rfl⟩⟩
  obtain ⟨y, hy, hMax⟩ := Set.exists_max_image O m hFinite hNonempty
  obtain ⟨q, hq⟩ := hOrbit y hy
  have hStep (i : B.support) : P.coreflection i y ∈ O := by
    obtain ⟨g, rfl⟩ := hy
    let u : G := ⟨P.coreflection i, Subgroup.subset_closure (Set.mem_range_self i)⟩
    exact ⟨u * g, rfl⟩
  have hNonneg (i : B.support) : 0 ≤ val y i := by
    have h := hMax _ (hStep i)
    change φ (l (P.coreflection i y)) ≤ φ (l y) at h
    rw [P.coreflection_apply, map_sub, map_smul, hl, smul_eq_mul, mul_one, map_sub] at h
    change 0 ≤ φ (P.root' i y)
    linarith only [h]
  have hCast₀ (i : ι) : ∃ n : ℤ, n ≠ 0 ∧ val h₀ i = (2 : ℚ) * n := by
    obtain ⟨n, hn, he⟩ := hReg i
    refine ⟨n, hn, ?_⟩
    change φ (P.root' i h₀) = _
    rw [he, casts_int_of_ratLinearForm φ hφ, Int.cast_mul, Int.cast_ofNat]
  have hVal (i : ι) : val y i = val h₀ (q i) := congrArg φ (hq i)
  have hNe₀ (i : ι) : val h₀ i ≠ 0 := by
    obtain ⟨n, hn, he⟩ := hCast₀ i
    exact he ▸ mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr hn)
  have hNe (i : ι) : val y i ≠ 0 := by rw [hVal]; exact hNe₀ _
  have hMin (i : B.support) : (2 : ℚ) ≤ val y i := by
    obtain ⟨n, hn, he⟩ := hCast₀ (q i)
    rw [hVal, he]
    have hc := lt_of_le_of_ne (hNonneg i) (Ne.symm (hNe i))
    rw [hVal, he] at hc
    have hP : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℚ) < (n : ℚ) by linarith)
    have h1 : (1 : ℚ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    linarith
  let W : AddSubmonoid M := {
    carrier := {v | 0 ≤ φ (P.toDualRight h₀ v) ∧ φ (P.toDualRight h₀ v) ≤ φ (P.toDualRight y v)}
    zero_mem' := by simp
    add_mem' := by
      intro a b ha hb
      change 0 ≤ φ (P.toDualRight h₀ (a + b)) ∧ φ (P.toDualRight h₀ (a + b)) ≤ φ (P.toDualRight y (a + b))
      simp only [map_add]
      exact ⟨add_nonneg ha.1 hb.1, add_le_add ha.2 hb.2⟩ }
  have hSimpleVal (i : B.support) : val h₀ i = 2 := by
    change φ (P.root' i h₀) = 2
    rw [hSimple]
    simpa only [Int.cast_ofNat] using casts_int_of_ratLinearForm φ hφ 2
  have hW : AddSubmonoid.closure (P.root '' B.support) ≤ W := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change 0 ≤ val h₀ i ∧ val h₀ i ≤ val y i
    rw [hSimpleVal ⟨i, hi⟩]
    exact ⟨by norm_num, hMin ⟨i, hi⟩⟩
  have hSigns (i : ι) : (0 < val h₀ i ↔ 0 < val y i) ∧ (0 < val h₀ i → val h₀ i ≤ val y i) := by
    rcases B.root_mem_or_neg_mem i with hp | hn
    · have h : 0 ≤ val h₀ i ∧ val h₀ i ≤ val y i := hW hp
      have h0' := lt_of_le_of_ne h.1 (Ne.symm (hNe₀ i))
      exact ⟨iff_of_true h0' (h0'.trans_le h.2), fun _ => h.2⟩
    · have h : 0 ≤ φ (P.toDualRight h₀ (-P.root i)) ∧
        φ (P.toDualRight h₀ (-P.root i)) ≤ φ (P.toDualRight y (-P.root i)) := hW hn
      simp only [map_neg] at h
      change 0 ≤ -val h₀ i ∧ -val h₀ i ≤ -val y i at h
      have h0' : ¬ 0 < val h₀ i := by linarith [h.1]
      have hy' : ¬ 0 < val y i := by linarith [h.1, h.2]
      exact ⟨iff_of_false h0' hy', fun hh => (h0' hh).elim⟩
  let s := Finset.univ.filter fun i => 0 < val h₀ i
  have hMem (i : ι) : i ∈ s ↔ q i ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hSigns i).1.trans (by rw [hVal])
  have hSum : ∑ i ∈ s, val y i = ∑ i ∈ s, val h₀ i := by
    simp_rw [hVal]
    refine Finset.sum_bij (fun i _ => q i) (fun i hi => (hMem i).mp hi) ?_ ?_ (fun _ _ => rfl)
    · exact fun _ _ _ _ h => q.injective h
    · intro i hi
      use q.symm i, (hMem _).mpr (by simpa only [Equiv.apply_symm_apply] using hi)
      exact q.apply_symm_apply _
  have hEqual (i : B.support) : P.root' i y = P.root' i h₀ := by
    have hi : (i : ι) ∈ s := by simp [s, hSimpleVal i]
    have hsum0 : ∑ j ∈ s, (val y j - val h₀ j) = 0 := by rw [Finset.sum_sub_distrib, hSum, sub_self]
    have hNonneg' (j : ι) (hj : j ∈ s) : 0 ≤ val y j - val h₀ j :=
      sub_nonneg.mpr ((hSigns j).2 (Finset.mem_filter.mp hj).2)
    have hEq := (Finset.sum_eq_zero_iff_of_nonneg hNonneg').mp hsum0 i hi
    obtain ⟨n, -, hn⟩ := hReg (q i)
    have hny : P.root' i y = ((2 * n : ℤ) : k) := (hq i).trans hn
    rw [show val y i = φ (((2 * n : ℤ) : k)) from congrArg φ hny, hSimpleVal i,
      casts_int_of_ratLinearForm φ hφ, sub_eq_zero] at hEq
    have hi' : 2 * n = 2 := by exact_mod_cast hEq
    rw [hny, hi', hSimple]
    norm_num
  have hY : y = h₀ := by
    apply P.toDualRight.injective
    apply B.toWeightBasis.ext
    intro i
    simpa only [RootPairing.Base.toWeightBasis, Basis.mk_apply] using hEqual i
  obtain ⟨g, hg⟩ := hy
  exact ⟨g.val, g.property, hg.trans hY⟩

end Chamber

end WideE
