/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under the Apache License, Version 2.0. See LICENSE-MATHLIB.
Adapted for Lean 4.19 from the algebraically closed case in mathlib4 revision
5d69f04e6539d5394e336e3c5c2b51a1603feebe, Mathlib/Algebra/Lie/CartanCriterion.lean.
-/
import WideE.SemisimpleEigenbasis
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Cartan's criterion over an algebraically closed field at the project's mathlib pin. -/

noncomputable section

open Algebra LieAlgebra LieIdeal LieModule LinearMap Module Module.End Polynomial

namespace WideE

attribute [local instance] LieRing.ofAssociativeRing

section Interpolation

variable {k ι : Type*} [Field k] [Fintype ι]

private theorem exists_poly_eval_on_finite_range (a b : ι → k)
    (h : ∀ i j, a i = a j → b i = b j) : ∃ p : k[X], ∀ i, p.eval (a i) = b i := by
  classical
  let s := Finset.univ.image a
  let r (x : k) := if hx : ∃ i, a i = x then b (Classical.choose hx) else 0
  refine ⟨Lagrange.interpolate s id r, fun i => ?_⟩
  have hi : a i ∈ s := Finset.mem_image_of_mem a (Finset.mem_univ i)
  exact (Lagrange.eval_interpolate_at_node (v := id) r (Set.injOn_id _) hi).trans (by
    simp only [r, dif_pos (show ∃ j, a j = a i from ⟨i, rfl⟩)]
    exact h _ i (Classical.choose_spec (show ∃ j, a j = a i from ⟨i, rfl⟩)))

end Interpolation

section AdjointJordan

variable {k V ι : Type*} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Fintype ι] [DecidableEq ι]

omit [CharZero k] [FiniteDimensional k V] in
private theorem ad_basis_end (b : Basis ι k V) (s : End k V) (d : ι → k)
    (hs : ∀ i, s (b i) = d i • b i) (i j : ι) :
    ad k _ s (b.end (i, j)) = (d i - d j) • b.end (i, j) := by
  apply b.ext
  intro l
  simp only [ad_apply, Ring.lie_def, sub_apply, End.mul_apply, LinearMap.smul_apply, hs,
    map_smul, b.end_apply_apply]
  by_cases h : j = l
  · subst l
    simp only [if_true, hs, sub_smul]
  · simp only [if_neg h, map_zero, smul_zero, sub_self]

omit [CharZero k] [FiniteDimensional k V] in
private theorem ad_commute_of_commute {s n : End k V} (h : Commute s n) :
    Commute (ad k _ s) (ad k _ n) := by
  apply sub_eq_zero.mp
  change ⁅ad k _ s, ad k _ n⁆ = 0
  rw [← LieHom.map_lie, h.lie_eq]
  exact (ad k (End k V)).map_zero

private theorem ad_semisimple_mem_adjoin (b : Basis ι k V) (s n : End k V) (d : ι → k)
    (hs : ∀ i, s (b i) = d i • b i) (hsn : Commute s n) (hn : IsNilpotent n) :
    ad k _ s ∈ Algebra.adjoin k {ad k _ (n + s)} := by
  let f := ad k _ (n + s)
  obtain ⟨u, _, v, hv, hNil, hSemi, hSum⟩ := f.exists_isNilpotent_isSemisimple
  have hVf : Commute f v := commute_of_mem_adjoin_self hv
  have hVnil : IsNilpotent (f - v) := by rwa [hSum, add_sub_cancel_right]
  have hA : f = ad k _ n + ad k _ s := (ad k (End k V)).map_add n s
  have hNilA : IsNilpotent (ad k _ n) := ad_nilpotent_of_nilpotent k hn
  have hEach (i j : ι) : b.end (i, j) ∈ f.maxGenEigenspace (d i - d j) := by
    obtain ⟨m, hm⟩ := hNilA
    let z := b.end (i, j)
    let a := d i - d j
    have hz : ad k _ s z = a • z := ad_basis_end b s d hs i j
    have hCom := (ad_commute_of_commute hsn).pow_right
    have hPow (l : ℕ) : ((f - a • 1) ^ l) z = (ad k _ n ^ l) z := by
      induction l with
      | zero => simp
      | succ l ih =>
        have hStep : ad k _ s ((ad k _ n ^ l) z) = a • (ad k _ n ^ l) z := by
          rw [← End.mul_apply, (hCom l).eq, End.mul_apply, hz, map_smul]
        rw [pow_succ', End.mul_apply, ih, LinearMap.sub_apply, LinearMap.smul_apply,
          End.one_apply, hA, LinearMap.add_apply, hStep, add_sub_cancel_right,
          ← End.mul_apply, ← pow_succ']
    refine (mem_maxGenEigenspace f a z).mpr ⟨m, ?_⟩
    rw [hPow, hm, LinearMap.zero_apply]
  have he : v = ad k _ s := by
    apply b.end.ext
    rintro ⟨i, j⟩
    rw [ad_basis_end b s d hs i j]
    exact apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil (hEach i j) hVf
      hSemi.isFinitelySemisimple hVnil
  rwa [← he]

end AdjointJordan

/-- The adjoint of the nilpotent part is a polynomial in the adjoint of the sum. -/
theorem ad_nilpotent_mem_adjoin_of_jordan {k V : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {s n : End k V}
    (h : Commute s n) (hs : s.IsSemisimple) (hn : IsNilpotent n) :
    ad k _ n ∈ Algebra.adjoin k {ad k _ (s + n)} := by
  obtain ⟨b, d, hb⟩ := exists_eigenbasis_of_isSemisimple s hs
  have hS := ad_semisimple_mem_adjoin b s n d hb h hn
  rw [add_comm n s] at hS
  have hN : ad k _ n = ad k _ (s + n) - ad k _ s := by
    rw [LieHom.map_add, add_sub_cancel_left]
  rw [hN]
  exact sub_mem (Algebra.self_mem_adjoin_singleton k _) hS

section TraceCriterion

variable {k L V : Type*} [Field k] [CharZero k] [IsAlgClosed k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]

omit [CharZero k] [IsAlgClosed k] [FiniteDimensional k V] in
private theorem trace_of_derived_mul_eq_zero (h : traceForm k L V = 0) (Y : End k V)
    (hY : ∀ a : L, ⁅Y, toEnd k L V a⁆ ∈ (toEnd k L V).range)
    (x : L) (hx : x ∈ derivedSeries k L 1) :
    trace k V (toEnd k L V x * Y) = 0 := by
  let ρ := toEnd k L V
  let T : L →ₗ[k] k := (trace k V).comp ((LinearMap.mulRight k Y).comp ρ.toLinearMap)
  change T x = 0
  have hT (a b : L) : T ⁅a, b⁆ = 0 := by
    obtain ⟨c, hc⟩ := hY b
    change ρ c = Y * ρ b - ρ b * Y at hc
    have ht : trace k V (ρ a * ρ c) = 0 := by
      change traceForm k L V a c = 0
      rw [h, LinearMap.zero_apply, LinearMap.zero_apply]
    have hCycle : trace k V (ρ b * ρ a * Y) = trace k V (ρ a * Y * ρ b) := by
      rw [mul_assoc, trace_mul_comm k (ρ b)]
    have hSub : ρ b * Y - Y * ρ b = -ρ c := by rw [hc, neg_sub]
    change trace k V (ρ ⁅a, b⁆ * Y) = 0
    rw [LieHom.map_lie, Ring.lie_def, sub_mul, map_sub, hCycle,
      mul_assoc (ρ a), mul_assoc (ρ a), ← map_sub, ← mul_sub, hSub, mul_neg, map_neg, ht, neg_zero]
  have hx' : x ∈ Submodule.span k (Set.range fun ab : L × L => ⁅ab.1, ab.2⁆) := by
    rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
      ← LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    apply Submodule.span_mono _ hx
    rintro _ ⟨a, -, b, -, rfl⟩
    exact ⟨(a, b), rfl⟩
  have hKer : Submodule.span k (Set.range fun ab : L × L => ⁅ab.1, ab.2⁆) ≤ LinearMap.ker T :=
    Submodule.span_le.mpr (by rintro _ ⟨⟨a, b⟩, rfl⟩; exact hT a b)
  exact hKer hx'

private theorem cartan_isNilpotent_derived_module (h : traceForm k L V = 0) :
    LieModule.IsNilpotent (derivedSeries k L 1) V := by
  classical
  let ρ := toEnd k L V
  suffices ∀ x ∈ derivedSeries k L 1, IsNilpotent (ρ x) from
    LieModule.isNilpotent_iff_forall'.mpr fun ⟨x, hx⟩ => this x hx
  intro x hx
  obtain ⟨n, hnA, s, hsA, hn, hs, hX⟩ := (ρ x).exists_isNilpotent_isSemisimple
  have hns := commute_of_mem_adjoin_singleton_of_commute hsA (commute_of_mem_adjoin_self hnA).symm
  obtain ⟨b, d, hd⟩ := exists_eigenbasis_of_isSemisimple s hs
  let E := Submodule.span ℚ (Set.range d)
  let δ (i : Fin (finrank k V)) : E := ⟨d i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hF (f : Module.Dual ℚ E) : ∀ i, f (δ i) = 0 := by
    let z (i : Fin (finrank k V)) : k := f (δ i)
    let Y : End k V := b.constr k fun i => z i • b i
    have hY (i : Fin (finrank k V)) : Y (b i) = z i • b i := b.constr_basis _ _ _
    have hDer : ∀ a : L, ⁅Y, ρ a⁆ ∈ ρ.range := by
      obtain ⟨p, hp⟩ := exists_poly_eval_on_finite_range
        (fun ij : Fin (finrank k V) × Fin (finrank k V) => d ij.1 - d ij.2)
        (fun ij => z ij.1 - z ij.2) (by
          rintro ⟨i, j⟩ ⟨l, m⟩ he
          have hδ : δ i - δ j = δ l - δ m := Subtype.ext he
          simpa only [z, ← Rat.cast_sub, ← map_sub] using congrArg (fun a : E => (f a : k)) hδ)
      have hAd : Polynomial.aeval (ad k _ s) p = ad k _ Y := by
        apply b.end.ext
        rintro ⟨i, j⟩
        rw [aeval_apply_of_hasEigenvector (μ := d i - d j)
          ⟨mem_eigenspace_iff.mpr (ad_basis_end b s d hd i j), b.end.ne_zero (i, j)⟩,
          hp (i, j), ad_basis_end b Y z hY i j]
      have hsAd := ad_semisimple_mem_adjoin b s n d hd hns.symm hn
      rw [← hX, adjoin_singleton_eq_range_aeval] at hsAd
      obtain ⟨q, hq⟩ := hsAd
      change Polynomial.aeval (ad k _ (ρ x)) q = ad k _ s at hq
      have hPoly : Polynomial.aeval (ad k _ (ρ x)) (p.comp q) = ad k _ Y := by
        rw [aeval_comp, hq, hAd]
      intro a
      rw [← ad_apply k, ← hPoly]
      apply Polynomial.aeval_apply_smul_mem_of_le_comap (q := ρ.range.toSubmodule)
        (show ρ a ∈ ρ.range from ⟨a, rfl⟩)
      rintro _ ⟨c, rfl⟩
      exact ⟨⁅x, c⁆, LieHom.map_lie ρ x c⟩
    have hComm : Commute n Y := by
      apply commute_of_mem_adjoin_singleton_of_commute (R := k) (b := s) _ hns
      rw [adjoin_singleton_eq_range_aeval]
      obtain ⟨p, hp⟩ := exists_poly_eval_on_finite_range d z (fun i j he =>
        congrArg (fun a : E => (f a : k)) (Subtype.ext he))
      refine ⟨p, b.ext fun i => ?_⟩
      change Polynomial.aeval s p (b i) = Y (b i)
      rw [aeval_apply_of_hasEigenvector (μ := d i) ⟨mem_eigenspace_iff.mpr (hd i), b.ne_zero i⟩, hp, hY]
    have hTraceN := (isNilpotent_trace_of_isNilpotent (hComm.isNilpotent_mul_left hn)).eq_zero
    have hTraceS : trace k V (s * Y) = ∑ i, z i * d i := by
      rw [trace_eq_matrix_trace _ b, Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.diag_apply, toMatrix_apply, End.mul_apply, hY, map_smul, hd,
        Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    have hTrace := trace_of_derived_mul_eq_zero h Y hDer x hx
    change trace k V (ρ x * Y) = 0 at hTrace
    rw [hX, add_mul, map_add, hTraceN, zero_add, hTraceS] at hTrace
    have hSum : (∑ i, f (δ i) • δ i) = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Rat.smul_def, z, δ,
        Submodule.coe_zero] using hTrace
    have hsquare : ∑ i, f (δ i) ^ 2 = 0 := by
      simpa only [map_sum, map_smul, map_zero, smul_eq_mul, sq] using congrArg f hSum
    intro i
    exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f (δ j)))).mp
      hsquare i (Finset.mem_univ i))
  have hδ (i : Fin (finrank k V)) : δ i = 0 := by
    exact (Module.forall_dual_apply_eq_zero_iff ℚ (δ i)).mp fun f => hF f i
  have hS : s = 0 := b.ext fun i => by
    have hi : d i = 0 := congrArg Subtype.val (hδ i)
    rw [hd, hi, zero_smul, LinearMap.zero_apply]
  rw [hX, hS, add_zero]
  exact hn

end TraceCriterion

section KillingForm

variable {k L : Type*} [Field k] [CharZero k] [IsAlgClosed k] [LieRing L] [LieAlgebra k L]
  [FiniteDimensional k L]

/-- Over an algebraically closed field of characteristic zero, the Killing radical is solvable. -/
theorem killingCompl_top_le_radical : LieIdeal.killingCompl k L ⊤ ≤ radical k L := by
  let K := LieIdeal.killingCompl k L ⊤
  let D : LieIdeal k L := ⁅K, K⁆
  have hTrace : traceForm k K L = 0 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    change killingForm k L x y = 0
    rw [LieModule.traceForm_comm]
    exact (LieIdeal.mem_killingCompl k L ⊤).mp hx y (LieSubmodule.mem_top y)
  have hNil := cartan_isNilpotent_derived_module hTrace
  have hD : LieRing.IsNilpotent D := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := k)]
    rintro ⟨x, hx⟩
    apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad (D : LieSubalgebra k L) (x := ⟨x, hx⟩)
    refine (LieModule.isNilpotent_iff_forall' (R := k)).mp hNil
      ⟨⟨x, LieSubmodule.lie_le_left K K hx⟩, ?_⟩
    rw [derivedSeries_eq_derivedSeriesOfIdeal_comap]
    exact hx
  letI := hD
  obtain ⟨n, hn⟩ := IsSolvable.solvable k D
  rw [derivedSeries_eq_bot_iff] at hn
  have hK : IsSolvable K := IsSolvable.mk (k := n + 1) ((derivedSeries_eq_bot_iff K _).mpr (by
    rwa [derivedSeriesOfIdeal_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]))
  exact (LieIdeal.solvable_iff_le_radical k L K).mp hK

/-- Cartan's criterion for semisimplicity in the algebraically closed case. -/
theorem isKilling_of_hasTrivialRadical [HasTrivialRadical k L] : IsKilling k L where
  killingCompl_top_eq_bot := le_antisymm
    (by simpa using (killingCompl_top_le_radical (k := k) (L := L))) bot_le

end KillingForm

end WideE
