import AlgebraicPoint
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Filtration

/-! Smooth algebras over an algebraically closed field are reduced. -/

noncomputable section

open scoped Polynomial TensorProduct

namespace WideE

universe u

section PolynomialPowers

variable {k ι : Type*} [Field k]

local notation "P" => MvPolynomial ι k

private def variableIdeal : Ideal P := Ideal.span (Set.range (MvPolynomial.X : ι → P))

private def degreeMap : P →ₐ[k] P[X] :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

private theorem degreeMap_monomial (d : ι →₀ ℕ) (a : k) :
    degreeMap (MvPolynomial.monomial d a) =
      Polynomial.C (MvPolynomial.monomial d a) * Polynomial.X ^ d.degree := by
  classical
  rw [degreeMap, MvPolynomial.aeval_monomial]
  change Polynomial.C (MvPolynomial.C a : P) *
    (d.prod fun i n => (Polynomial.C (MvPolynomial.X i : P) * Polynomial.X) ^ n) = _
  simp only [Finsupp.prod, Finsupp.degree, mul_pow, Finset.prod_mul_distrib,
    ← map_pow Polynomial.C, ← map_prod Polynomial.C, Finset.prod_pow_eq_pow_sum, ← mul_assoc,
    ← map_mul Polynomial.C]
  simp only [MvPolynomial.monomial_eq, Finsupp.prod]

private theorem degreeMap_coeff (p : P) (n : ℕ) :
    (degreeMap p).coeff n = MvPolynomial.homogeneousComponent n p := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero, Polynomial.coeff_zero]
  | add x y hx hy => simp only [map_add, Polynomial.coeff_add, hx, hy]
  | single d a =>
    change (degreeMap (MvPolynomial.monomial d a)).coeff n =
      MvPolynomial.homogeneousComponent n (MvPolynomial.monomial d a)
    rw [degreeMap_monomial, Polynomial.coeff_C_mul_X_pow]
    by_cases hn : n = d.degree
    · subst n
      rw [if_pos rfl]
      apply MvPolynomial.ext
      intro b
      rw [MvPolynomial.coeff_homogeneousComponent]
      by_cases h : b = d
      · subst b
        simp
      · simp [MvPolynomial.coeff_monomial, h, Ne.symm h]
    · rw [if_neg hn]
      apply MvPolynomial.ext
      intro b
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero]
      by_cases h : b = d
      · subst b
        simp [Ne.symm hn]
      · simp [MvPolynomial.coeff_monomial, h, Ne.symm h]

private theorem degreeMap_dvd (n : ℕ) {p : P} (hp : p ∈ (variableIdeal : Ideal P) ^ n) :
    (Polynomial.X : P[X]) ^ n ∣ degreeMap p := by
  let I : Ideal P := variableIdeal
  let J : Ideal P[X] := Ideal.span {(Polynomial.X : P[X])}
  have h : Ideal.map (degreeMap : P →ₐ[k] P[X]) I ≤ J := by
    change Ideal.map (degreeMap : P →ₐ[k] P[X]) (Ideal.span (Set.range MvPolynomial.X)) ≤ J
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change degreeMap (MvPolynomial.X i : P) ∈ J
    rw [degreeMap, MvPolynomial.aeval_X]
    exact J.mul_mem_left _ (Ideal.subset_span rfl)
  have hPower : Ideal.map (degreeMap : P →ₐ[k] P[X]) (I ^ n) ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' h n
  have hMem : degreeMap p ∈ J ^ n := hPower (Ideal.mem_map_of_mem _ hp)
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hMem

private theorem monomial_mem_variableIdeal_pow {d : ι →₀ ℕ} (a : k) :
    MvPolynomial.monomial d a ∈ (variableIdeal : Ideal P) ^ d.degree := by
  classical
  let I : Ideal P := variableIdeal
  have h (i : ι) : (MvPolynomial.X i : P) ∈ I := Ideal.subset_span (Set.mem_range_self i)
  rw [MvPolynomial.monomial_eq]
  apply Ideal.mul_mem_left
  change (∏ i ∈ d.support, (MvPolynomial.X i : P) ^ d i) ∈ I ^ d.degree
  rw [Finsupp.degree, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (h i) (d i))

private theorem mem_variableIdeal_pow_of_degreeMap_dvd {n : ℕ} {p : P}
    (hp : (Polynomial.X : P[X]) ^ n ∣ degreeMap p) : p ∈ (variableIdeal : Ideal P) ^ n := by
  classical
  rw [MvPolynomial.as_sum p]
  apply Ideal.sum_mem
  intro d hd
  have hD : n ≤ d.degree := by
    by_contra! hlt
    have h := Polynomial.X_pow_dvd_iff.mp hp _ hlt
    rw [degreeMap_coeff] at h
    have hCoeff := congrArg (MvPolynomial.coeff d) h
    rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl, MvPolynomial.coeff_zero] at hCoeff
    exact (MvPolynomial.mem_support_iff.mp hd) hCoeff
  exact (Ideal.pow_le_pow_right hD) (monomial_mem_variableIdeal_pow (p.coeff d))

private theorem natTrailingDegree_pow_of_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p ≠ 0) (r : ℕ) : (p ^ r).natTrailingDegree = p.natTrailingDegree * r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero r hp) hp, ih, Nat.mul_succ]

private theorem X_pow_dvd_of_pow {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} {n r : ℕ} (hr : 0 < r) (h : (Polynomial.X : R[X]) ^ (n * r) ∣ p ^ r) :
    (Polynomial.X : R[X]) ^ n ∣ p := by
  by_cases hp : p = 0
  · rw [hp]
    exact dvd_zero _
  have hDeg : n * r ≤ (p ^ r).natTrailingDegree := by
    by_contra! hlt
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (pow_ne_zero r hp))
      (Polynomial.X_pow_dvd_iff.mp h _ hlt)
  rw [natTrailingDegree_pow_of_ne_zero hp] at hDeg
  have hDeg' : n ≤ p.natTrailingDegree := Nat.le_of_mul_le_mul_right hDeg hr
  exact Polynomial.X_pow_dvd_iff.mpr fun i hi =>
    Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hi.trans_le hDeg')

private theorem mem_variableIdeal_pow_of_pow_mem {p : P} {n r : ℕ} (hr : 0 < r)
    (h : p ^ r ∈ (variableIdeal : Ideal P) ^ (n * r)) : p ∈ (variableIdeal : Ideal P) ^ n := by
  apply mem_variableIdeal_pow_of_degreeMap_dvd
  have hDvd := degreeMap_dvd (n * r) h
  rw [map_pow] at hDvd
  exact X_pow_dvd_of_pow hr hDvd

end PolynomialPowers

section Lifting

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A] [Algebra.FormallySmooth k A]

/-- A nilpotent element of a smooth affine algebra vanishes to every order at a rational point. -/
theorem isNilpotent_mem_point_ideal_pow (p : A →ₐ[k] k) {x : A} (hx : IsNilpotent x)
    (n : ℕ) : x ∈ (RingHom.ker p.toRingHom) ^ n := by
  classical
  obtain ⟨r, hr⟩ := hx
  have hrPos : 0 < r + 1 := Nat.succ_pos _
  have hNil : x ^ (r + 1) = 0 := by rw [pow_succ, hr, zero_mul]
  let I := RingHom.ker p.toRingHom
  change x ∈ I ^ n
  by_cases hn : n = 0
  · simp [hn]
  let N := n * (r + 1)
  have hN : N ≠ 0 := Nat.mul_ne_zero hn hrPos.ne'
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k A).out
  let ι := { a : A // a ∈ s }
  let u (a : ι) : A := a.val - algebraMap k A (p a.val)
  let P := MvPolynomial ι k
  let π : P →ₐ[k] A := MvPolynomial.aeval u
  let J : Ideal P := variableIdeal
  have hAug : p.comp π = MvPolynomial.aeval (fun _ : ι => (0 : k)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, show π (MvPolynomial.X i) = u i from MvPolynomial.aeval_X u i,
      MvPolynomial.aeval_X]
    change p (i.val - algebraMap k A (p i.val)) = 0
    rw [map_sub, p.commutes]
    exact sub_self _
  have hSurj : Function.Surjective π := by
    rw [← AlgHom.range_eq_top]
    change (MvPolynomial.aeval u).range = ⊤
    rw [← Algebra.adjoin_range_eq_range_aeval]
    apply top_unique
    rw [← hs, Algebra.adjoin_le_iff]
    intro a ha
    let B := Algebra.adjoin k (Set.range u)
    have hu : u ⟨a, ha⟩ ∈ B := Algebra.subset_adjoin (Set.mem_range_self _)
    have h := B.add_mem hu (B.algebraMap_mem (p a))
    simpa only [u, sub_add_cancel] using h
  have hMap : J.map π ≤ I := by
    change (Ideal.span (Set.range (MvPolynomial.X : ι → P))).map π ≤ I
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change p (π (MvPolynomial.X i)) = 0
    have h := DFunLike.congr_fun hAug (MvPolynomial.X i)
    exact h.trans (MvPolynomial.aeval_X _ _)
  have hPower (m : ℕ) : (J ^ m).map π ≤ I ^ m := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hMap m
  have hComap : J ^ N ≤ (I ^ N).comap π := Ideal.map_le_iff_le_comap.mp (hPower N)
  let f : P ⧸ J ^ N →ₐ[k] A ⧸ I ^ N := Ideal.quotientMapₐ (I ^ N) π hComap
  have hF : Function.Surjective f := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := hSurj b
    exact ⟨Ideal.Quotient.mk _ b', rfl⟩
  have hKer : RingHom.ker f.toRingHom ≤ J.map (Ideal.Quotient.mk (J ^ N)) := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hb : π b ∈ I ^ N := Ideal.Quotient.eq_zero_iff_mem.mp ha
    have hb₀ : p (π b) = 0 := Ideal.pow_le_self hN hb
    have hc : b.coeff 0 = 0 := by
      have h := DFunLike.congr_fun hAug b
      rw [MvPolynomial.aeval_zero'] at h
      exact h.symm.trans hb₀
    apply Ideal.mem_map_of_mem
    change b ∈ J
    rw [← pow_one J]
    apply mem_variableIdeal_pow_of_degreeMap_dvd
    apply Polynomial.X_pow_dvd_iff.mpr
    intro i hi
    have hi₀ : i = 0 := Nat.lt_one_iff.mp hi
    rw [hi₀, degreeMap_coeff, MvPolynomial.homogeneousComponent_zero, hc, map_zero]
  have hKerNil : IsNilpotent (RingHom.ker f.toRingHom) := by
    refine ⟨N, ?_⟩
    change (RingHom.ker f.toRingHom) ^ N = ⊥
    refine le_antisymm ((pow_le_pow_left' hKer N).trans ?_) bot_le
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  let g := Algebra.FormallySmooth.liftOfSurjective (Ideal.Quotient.mkₐ k (I ^ N)) f hF hKerNil
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (g x)
  have hPow : b ^ (r + 1) ∈ J ^ N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_pow, hb, ← map_pow g, hNil, map_zero]
  have hbMem : b ∈ J ^ n := mem_variableIdeal_pow_of_pow_mem hrPos hPow
  have hbTo : π b ∈ I ^ n := hPower n (Ideal.mem_map_of_mem π hbMem)
  have hSame : Ideal.Quotient.mk (I ^ N) (π b) = Ideal.Quotient.mk (I ^ N) x := by
    change f (Ideal.Quotient.mk (J ^ N) b) = _
    rw [hb]
    exact Algebra.FormallySmooth.liftOfSurjective_apply _ f hF hKerNil x
  have hDiff : π b - x ∈ I ^ N := Ideal.Quotient.eq.mp hSame
  have hNn : n ≤ N := Nat.le_mul_of_pos_right n hrPos
  have hIn : π b - x ∈ I ^ n := Ideal.pow_le_pow_right hNn hDiff
  simpa only [sub_sub_cancel] using (I ^ n).sub_mem hbTo hIn

end Lifting

section Reduced

variable (k A : Type u) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]

/-- A smooth affine algebra over an algebraically closed field has no nonzero nilpotents. -/
theorem isReduced_of_smooth_of_isAlgClosed [Algebra.Smooth k A] : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let J := (Submodule.span A {x}).annihilator
  have hJ (s : A) : s ∈ J ↔ s * x = 0 := Submodule.mem_annihilator_span_singleton x s
  have hJTop : J ≠ ⊤ := by
    intro h
    have hOne : (1 : A) ∈ J := (J.eq_top_iff_one).mp h
    exact hx0 (by simpa only [one_mul] using (hJ 1).mp hOne)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJTop
  letI : M.IsMaximal := hM
  let p := StrictEUnit.maximalIdealPoint (k := k) M
  have hp : RingHom.ker p.toRingHom = M := StrictEUnit.maximalIdealPoint_ker M
  have hPow (n : ℕ) : x ∈ M ^ n := hp ▸ isNilpotent_mem_point_ideal_pow p hx n
  have hInf : x ∈ (⨅ n : ℕ, M ^ n • ⊤ : Submodule A A) := by
    apply (Submodule.mem_iInf _).mpr
    intro n
    rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    exact hPow n
  obtain ⟨a, ha⟩ := (M.mem_iInf_smul_pow_eq_bot_iff x).mp hInf
  have hA : (1 - (a : A)) ∈ J := by
    apply (hJ _).mpr
    rw [sub_mul, one_mul, ← smul_eq_mul, ha, sub_self]
  have hOne : (1 : A) ∈ M := by
    simpa only [sub_add_cancel] using M.add_mem (hJM hA) a.property
  exact hM.ne_top (M.eq_top_iff_one.mpr hOne)

end Reduced

/-- Every smooth algebra over a field is reduced. -/
theorem isReduced_of_smooth_over_field (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] : IsReduced A := by
  let K := AlgebraicClosure k
  letI : IsReduced (K ⊗[k] A) := isReduced_of_smooth_of_isAlgClosed K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)

end WideE
