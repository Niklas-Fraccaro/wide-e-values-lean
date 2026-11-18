import Mathlib.Data.Finsupp.PWO
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# Generic freeness of finite-type algebras

Inverting the product of the leading coefficients of finitely many
polynomials makes the standard monomials a basis. Dickson's lemma gives
the finite family, and the division algorithm works over the localized
coefficient ring because the selected leading coefficients become units.
-/

noncomputable section

namespace WideE

open MvPolynomial

universe uσ

section LeadingTerms

variable {σ : Type uσ} {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private theorem exists_finite_leadingFamily [Finite σ] (m : MonomialOrder σ)
    (f : MvPolynomial σ A →ₐ[A] B) :
    ∃ (ι : Type uσ) (_ : Fintype ι) (b : ι → MvPolynomial σ A),
      (∀ i, f (b i) = 0) ∧ (∀ i, b i ≠ 0) ∧
      ∀ p, f p = 0 → p ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree p := by
  classical
  let E : Set (σ →₀ ℕ) := {e | ∃ p, f p = 0 ∧ p ≠ 0 ∧ m.degree p = e}
  let M : Set (σ →₀ ℕ) := {e | Minimal (· ∈ E) e}
  have hAntichain : IsAntichain (· ≤ ·) M := by
    intro a ha b hb hne hab
    exact hne (le_antisymm hab (hb.2 ha.1 hab))
  have hFinite := hAntichain.finite_of_partiallyWellOrderedOn (Finsupp.isPWO M)
  letI : Fintype M := hFinite.fintype
  have hChoose (e : M) : ∃ p, f p = 0 ∧ p ≠ 0 ∧ m.degree p = (e : σ →₀ ℕ) := e.prop.1
  choose b hb₀ hbNe hbDeg using hChoose
  refine ⟨M, inferInstance, b, hb₀, hbNe, fun p hp hpNe => ?_⟩
  have hE : m.degree p ∈ E := ⟨p, hp, hpNe, rfl⟩
  obtain ⟨e, he, hmin⟩ := (Set.wellFoundedOn_iff.mp (Finsupp.isPWO E).isWF).has_min
    (E ∩ Set.Iic (m.degree p)) ⟨m.degree p, hE, Set.mem_Iic.mpr le_rfl⟩
  have heM : e ∈ M := by
    refine ⟨he.1, fun a ha hae => ?_⟩
    by_contra h
    exact hmin a ⟨ha, hae.trans he.2⟩ ⟨lt_of_le_of_ne hae (fun hEq => h hEq.ge), ha, he.1⟩
  exact ⟨⟨e, heM⟩, (hbDeg _).le.trans he.2⟩

omit [Algebra A B] in
private theorem degree_map_of_injective (m : MonomialOrder σ) (f : A →+* B)
    (hf : Function.Injective f) (p : MvPolynomial σ A) :
    m.degree (MvPolynomial.map f p) = m.degree p := by
  unfold MonomialOrder.degree
  rw [support_map_of_injective _ hf]

private theorem degree_C_mul_of_isUnit (m : MonomialOrder σ) {c : A}
    (hc : IsUnit c) (p : MvPolynomial σ A) :
    m.degree (MvPolynomial.C c * p) = m.degree p := by
  unfold MonomialOrder.degree
  congr 2
  ext a
  simp only [mem_support_iff, coeff_C_mul, ne_eq, hc.mul_right_eq_zero]

end LeadingTerms

section Localization

variable {σ A : Type*} [CommRing A]

private theorem mvPolynomial_clearAwayDenominator (d : A)
    (p : MvPolynomial σ (Localization.Away d)) :
    ∃ (b : Submonoid.powers d) (q : MvPolynomial σ A),
      MvPolynomial.map (algebraMap A (Localization.Away d)) q =
        MvPolynomial.C (algebraMap A (Localization.Away d) (b : A)) * p := by
  classical
  let D := Localization.Away d
  let M := Submonoid.powers d
  let b := IsLocalization.commonDenom (S := D) M p.support (fun a => p.coeff a)
  let c (a : p.support) := IsLocalization.integerMultiple (S := D) M p.support
    (fun a => p.coeff a) a
  let q : MvPolynomial σ A := Finsupp.onFinset p.support
    (fun a => if h : a ∈ p.support then c ⟨a, h⟩ else 0) (by
      intro a h
      by_contra hn
      exact h (dif_neg hn))
  refine ⟨b, q, ?_⟩
  ext a
  rw [coeff_map, coeff_C_mul]
  change algebraMap A D (if h : a ∈ p.support then c ⟨a, h⟩ else 0) =
    algebraMap A D (b : A) * p.coeff a
  split_ifs with h
  · exact (IsLocalization.map_integerMultiple (S := D) M p.support
      (fun a => p.coeff a) ⟨a, h⟩).trans (Algebra.smul_def (b : A) (p.coeff a))
  · have hz : p.coeff a = 0 := not_ne_iff.mp (mt mem_support_iff.mpr h)
    rw [hz, mul_zero, map_zero]

end Localization

section StandardMonomials

variable {σ A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A family with invertible leading coefficients that detects the leading
degree of every nonzero kernel element gives a free module of normal monomials. -/
private theorem moduleFree_of_leadingFamily (m : MonomialOrder σ)
    (f : MvPolynomial σ A →ₐ[A] B) (hf : Function.Surjective f)
    (b : ι → MvPolynomial σ A) (hb₀ : ∀ i, f (b i) = 0)
    (hbUnit : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (hp : ∀ p, f p = 0 → p ≠ 0 → ∃ i, m.degree (b i) ≤ m.degree p) :
    Module.Free A B := by
  let N : Set (σ →₀ ℕ) := {a | ∀ i, ¬ m.degree (b i) ≤ a}
  let D : Submodule A ((σ →₀ ℕ) →₀ A) := Finsupp.supported A A N
  let L : D →ₗ[A] B := f.toLinearMap.comp D.subtype
  have hInjective : Function.Injective L := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun p hz => ?_)
    change f (p.val : MvPolynomial σ A) = 0 at hz
    apply Subtype.ext
    by_contra hNe
    obtain ⟨i, hi⟩ := hp (p.val : MvPolynomial σ A) hz hNe
    have hDeg : m.degree (p.val : MvPolynomial σ A) ∈ (p.val : MvPolynomial σ A).support :=
      mem_support_iff.mpr ((MonomialOrder.coeff_degree_ne_zero_iff (m := m)).mpr hNe)
    exact (p.prop hDeg) i hi
  have hSurjective : Function.Surjective L := by
    intro x
    obtain ⟨p, rfl⟩ := hf x
    obtain ⟨g, r, hDecomp, _, hr⟩ := m.div hbUnit p
    refine ⟨⟨r, hr⟩, ?_⟩
    change f r = f p
    have hComb : f (Finsupp.linearCombination (MvPolynomial σ A) b g) = 0 := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [smul_eq_mul, map_mul, hb₀, mul_zero]
    rw [hDecomp, map_add, hComb, zero_add]
  let e := LinearEquiv.ofBijective L ⟨hInjective, hSurjective⟩
  exact Module.Free.of_equiv ((Finsupp.supportedEquivFinsupp (R := A) N).symm.trans e)

end StandardMonomials

section Generic

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]

/-- Generic freeness for a finite-type algebra over a domain, with the
actual localization algebra structure. -/
theorem exists_free_localizationAway [Algebra.FiniteType A B] :
    ∃ d : A, d ≠ 0 ∧
      (let A' := Localization.Away d
       let B' := Localization.Away (algebraMap A B d)
       letI : Algebra A' B' := (IsLocalization.Away.map A' B' (algebraMap A B) d).toAlgebra
       Module.Free A' B') := by
  classical
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType A B)
  let m := MonomialOrder.lex (σ := Fin n)
  obtain ⟨ι, _, b, hb₀, hbNe, hLead⟩ := exists_finite_leadingFamily m f
  let d : A := ∏ i, m.leadingCoeff (b i)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (MonomialOrder.leadingCoeff_ne_zero_iff (m := m)).mpr (hbNe i)
  refine ⟨d, hd, ?_⟩
  let A' := Localization.Away d
  let B' := Localization.Away (algebraMap A B d)
  let a := algebraMap A A'
  let j := algebraMap B B'
  let e := IsLocalization.Away.map A' B' (algebraMap A B) d
  have he (x : A) : e (a x) = j (algebraMap A B x) := IsLocalization.map_eq _ _
  letI : Algebra A' B' := e.toAlgebra
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => (he x).symm)
  let g : MvPolynomial (Fin n) A' →ₐ[A'] B' := MvPolynomial.aeval (j ∘ f ∘ MvPolynomial.X)
  have hg (p : MvPolynomial (Fin n) A) : g (MvPolynomial.map a p) = j (f p) := by
    have h : g.toRingHom.comp (MvPolynomial.map a) = j.comp f.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change g (MvPolynomial.map a (MvPolynomial.C c)) = j (f (MvPolynomial.C c))
        rw [MvPolynomial.map_C, show g (MvPolynomial.C (a c)) = e (a c) from g.commutes _,
          show f (MvPolynomial.C c) = algebraMap A B c from f.commutes c, he]
      · intro i
        change g (MvPolynomial.map a (MvPolynomial.X i)) = j (f (MvPolynomial.X i))
        rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
        rfl
    exact DFunLike.congr_fun h p
  have hdUnit : IsUnit (a d) := IsLocalization.Away.algebraMap_isUnit d
  have hgSurj : Function.Surjective g := by
    intro z
    obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj (algebraMap A B d) z
    obtain ⟨p, rfl⟩ := hf y
    let u := hdUnit.unit
    have hu : e ↑u = j (algebraMap A B d) := by rw [hdUnit.unit_spec, he]
    refine ⟨MvPolynomial.map a p * MvPolynomial.C ((↑(u⁻¹) : A') ^ n), ?_⟩
    rw [map_mul, hg, show g (MvPolynomial.C ((↑(u⁻¹) : A') ^ n)) = e ((↑(u⁻¹) : A') ^ n) from
      g.commutes _, map_pow, ← hy, ← hu, mul_assoc, ← mul_pow, ← map_mul, Units.mul_inv,
      map_one, one_pow, mul_one]
  have haInj : Function.Injective a := by
    apply IsLocalization.injective (M := Submonoid.powers d)
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hd)
  let b' : ι → MvPolynomial (Fin n) A' := MvPolynomial.map a ∘ b
  have hDeg (i : ι) : m.degree (b' i) = m.degree (b i) :=
    degree_map_of_injective m a haInj _
  have hUnit (i : ι) : IsUnit (m.leadingCoeff (b' i)) := by
    change IsUnit (MvPolynomial.coeff (m.degree (b' i)) (MvPolynomial.map a (b i)))
    rw [coeff_map, hDeg]
    exact isUnit_of_dvd_unit (map_dvd a (Finset.dvd_prod_of_mem (fun i => m.leadingCoeff (b i)) (Finset.mem_univ i))) hdUnit
  have hLift (p : MvPolynomial (Fin n) A') (hp₀ : g p = 0) (hpNe : p ≠ 0) :
      ∃ q : MvPolynomial (Fin n) A, f q = 0 ∧ q ≠ 0 ∧ m.degree q = m.degree p := by
    obtain ⟨s, q, hq⟩ := mvPolynomial_clearAwayDenominator d p
    have hDegQ : m.degree q = m.degree p := by
      rw [← degree_map_of_injective m a haInj, hq]
      exact degree_C_mul_of_isUnit m (IsLocalization.map_units A' s) p
    have hCleared : j (f q) = 0 := by rw [← hg, hq, map_mul, hp₀, mul_zero]
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A B d))
      B' (f q)).mp hCleared
    obtain ⟨l, hl⟩ := t.prop
    have hqNe : q ≠ 0 := by
      intro hZero
      rw [hZero, map_zero] at hq
      have hUnitQ := (IsLocalization.map_units A' s).map (MvPolynomial.C (σ := Fin n))
      exact hpNe (hUnitQ.mul_right_eq_zero.mp hq.symm)
    refine ⟨MvPolynomial.C (d ^ l) * q, ?_, ?_, ?_⟩
    · change (algebraMap A B d) ^ l = (t : B) at hl
      rw [map_mul, show f (MvPolynomial.C (d ^ l)) = algebraMap A B (d ^ l)
        from f.commutes _, map_pow, hl, ht]
    · exact mul_ne_zero (fun hz => pow_ne_zero l hd (C_eq_zero.mp hz)) hqNe
    · rw [← degree_map_of_injective m a haInj, map_mul, MvPolynomial.map_C, map_pow,
        degree_C_mul_of_isUnit m (hdUnit.pow l), degree_map_of_injective m a haInj, hDegQ]
  letI : Module.Free A' B' := moduleFree_of_leadingFamily m g hgSurj b'
    (fun i => (hg (b i)).trans (by rw [hb₀, map_zero])) hUnit (fun p hp hpNe => by
      obtain ⟨q, hq₀, hqNe, hqDeg⟩ := hLift p hp hpNe
      obtain ⟨i, hi⟩ := hLead q hq₀ hqNe
      exact ⟨i, by rwa [hDeg, ← hqDeg]⟩)
  exact inferInstance

/-- For a finite-type algebra over a domain, there is a nonzero base
element whose inversion makes the corresponding algebra flat over the base. -/
theorem exists_flat_localizationAway [Algebra.FiniteType A B] :
    ∃ d : A, d ≠ 0 ∧ Module.Flat A (Localization.Away (algebraMap A B d)) := by
  obtain ⟨d, hd, hFree⟩ := exists_free_localizationAway (A := A) (B := B)
  let A' := Localization.Away d
  let B' := Localization.Away (algebraMap A B d)
  let e := IsLocalization.Away.map A' B' (algebraMap A B) d
  letI : Algebra A' B' := e.toAlgebra
  have he (x : A) : e (algebraMap A A' x) = algebraMap B B' (algebraMap A B x) :=
    IsLocalization.map_eq _ _
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => (he x).symm)
  letI : Module.Free A' B' := hFree
  exact ⟨d, hd, Module.Flat.trans A A' B'⟩

end Generic

end WideE
