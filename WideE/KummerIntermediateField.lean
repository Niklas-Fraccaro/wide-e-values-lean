import WideE.KummerCoordinates
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! The intermediate fields of the Laurent power cover. -/

noncomputable section

namespace WideE

open Polynomial

section Roots

variable {k L : Type*} [Field k] [hk : IsAlgClosed k] [Field L] [hkl : Algebra k L]

include hk hkl in
private theorem splits_power_sub_constant {t : L} (ht : t ≠ 0) (q : ℕ) :
    ((X ^ q - C (t ^ q)) : Polynomial L).Splits (RingHom.id L) := by
  have h₀ : ((X ^ q - 1) : Polynomial k).Splits (RingHom.id k) := IsAlgClosed.splits _
  have h₁ : ((X ^ q - 1) : Polynomial k).Splits (algebraMap k L) := by
    simpa only [RingHom.comp_id] using splits_comp_of_splits (RingHom.id k) (algebraMap k L) h₀
  have h₂ : ((X ^ q - 1) : Polynomial L).Splits (RingHom.id L) := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one] using
      (splits_id_iff_splits (algebraMap k L)).2 h₁
  have h₃ := h₂.comp_of_degree_le_one (degree_C_mul_X_le t⁻¹)
  have h₄ := splits_mul (RingHom.id L) (splits_C (RingHom.id L) (t ^ q)) h₃
  have hcoef : (C (t ^ q) : Polynomial L) * C t⁻¹ ^ q = 1 := by
    rw [← map_pow, ← map_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero q ht), map_one]
  simpa only [sub_comp, pow_comp, X_comp, one_comp, mul_pow, mul_sub, ← mul_assoc, hcoef,
    one_mul, mul_one] using h₄

private theorem root_power_is_scalar_multiple {t r : L} (ht : t ≠ 0)
    {q : ℕ} (hq : 0 < q) (hr : r ^ q = t ^ q) : ∃ c : k, r = algebraMap k L c * t := by
  let P : Polynomial k := X ^ q - 1
  have hP : P.Splits (RingHom.id k) := IsAlgClosed.splits _
  have hMonic : P.Monic := by simpa only [P, map_one] using monic_X_pow_sub_C (1 : k) hq.ne'
  have hpow : (r / t) ^ q = 1 := by rw [div_pow, hr, div_self (pow_ne_zero q ht)]
  have hroot : r / t ∈ (P.map (algebraMap k L)).roots := by
    apply (mem_roots ((hMonic.map (algebraMap k L)).ne_zero)).mpr
    simp only [IsRoot, P, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one,
      eval_sub, eval_pow, eval_X, eval_one, hpow, sub_self]
  rw [Polynomial.roots_map _ hP] at hroot
  obtain ⟨c, _, hc⟩ := Multiset.mem_map.mp hroot
  exact ⟨c, by rw [hc, div_mul_cancel₀ r ht]⟩

omit [IsAlgClosed k] in
private theorem prod_scalar_multiples (t : L) (l : Multiset L)
    (h : ∀ r ∈ l, ∃ c : k, r = algebraMap k L c * t) :
    ∃ c : k, l.prod = algebraMap k L c * t ^ l.card := by
  induction l using Multiset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | cons r l ih =>
    obtain ⟨a, ha⟩ := h r (Multiset.mem_cons_self r l)
    obtain ⟨b, hb⟩ := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    refine ⟨a * b, ?_⟩
    rw [Multiset.prod_cons, Multiset.card_cons, ha, hb, map_mul, pow_succ]
    ac_rfl

/-- The actual power with exponent the minimal-polynomial degree belongs to the
intermediate field containing a positive power. -/
theorem pow_natDegree_minpoly_mem_of_pow_mem (E : IntermediateField k L) {t : L} (ht : t ≠ 0)
    {q : ℕ} (hq : 0 < q) (htq : t ^ q ∈ E) :
    IsIntegral E t ∧ t ^ (minpoly E t).natDegree ∈ E := by
  let P : Polynomial E := X ^ q - C (⟨t ^ q, htq⟩ : E)
  have hP : P.Monic := monic_X_pow_sub_C _ hq.ne'
  have hroot : aeval t P = 0 := by simp [P]
  have hint : IsIntegral E t := ⟨P, hP, hroot⟩
  refine ⟨hint, ?_⟩
  let M := (minpoly E t).map (algebraMap E L)
  have hm : M.Monic := (minpoly.monic hint).map _
  have hdiv : M ∣ ((X ^ q - C (t ^ q)) : Polynomial L) := by
    have h := Polynomial.map_dvd (algebraMap E L) (minpoly.dvd E t hroot)
    simpa only [M, P, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] using h
  have hsplit : M.Splits (RingHom.id L) :=
    Polynomial.splits_of_splits_of_dvd _ (monic_X_pow_sub_C (t ^ q) hq.ne').ne_zero
      (splits_power_sub_constant (k := k) ht q) hdiv
  have hroots (r : L) (hr : r ∈ M.roots) : ∃ c : k, r = algebraMap k L c * t := by
    have hr₀ : M.eval r = 0 := (mem_roots hm.ne_zero).mp hr
    obtain ⟨W, hW⟩ := hdiv
    have hrP : ((X ^ q - C (t ^ q)) : Polynomial L).eval r = 0 := by
      rw [hW, eval_mul, hr₀, zero_mul]
    apply root_power_is_scalar_multiple ht hq
    simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hrP
  let d := (minpoly E t).natDegree
  have hd : M.natDegree = d := Polynomial.natDegree_map _
  have hcard : M.roots.card = d := (splits_iff_card_roots.mp hsplit).trans hd
  obtain ⟨c, hc⟩ := prod_scalar_multiples t M.roots hroots
  let e : L := (-1) ^ d * algebraMap k L c
  have hconst : M.coeff 0 = e * t ^ d := by
    rw [prod_roots_eq_coeff_zero_of_monic_of_splits hm hsplit, hd, hc, hcard, mul_assoc]
  have hconstE : M.coeff 0 ∈ E := by
    dsimp only [M]
    rw [Polynomial.coeff_map]
    exact ((minpoly E t).coeff 0).property
  have he : e ∈ E := E.mul_mem (pow_mem (E.neg_mem E.one_mem) d) (E.algebraMap_mem c)
  have hconst₀ : M.coeff 0 ≠ 0 := by
    dsimp only [M]
    rw [Polynomial.coeff_map]
    exact (map_ne_zero_iff _ (algebraMap E L).injective).2 (minpoly.coeff_zero_ne_zero hint ht)
  have he₀ : e ≠ 0 := fun h => hconst₀ (by rw [hconst, h, zero_mul])
  have h := E.div_mem hconstE he
  rwa [hconst, mul_comm e, mul_div_cancel_right₀ _ he₀] at h

end Roots

section LaurentFraction

open LaurentPolynomial

variable (k : Type*) [Field k]

local notation "R" => LaurentPolynomial k
local notation "L" => FractionRing (LaurentPolynomial k)

/-- The Laurent coordinate in the fraction field. -/
def laurentFractionCoordinate : L := algebraMap R L (T 1)

theorem laurentFractionCoordinate_ne_zero : laurentFractionCoordinate k ≠ 0 :=
  ((show IsUnit (T 1 : LaurentPolynomial k) from LaurentPolynomial.isUnit_T 1).map
    (algebraMap R L)).ne_zero

private def laurentEvalAtUnit {F : Type*} [Field F] [Algebra k F] (u : Fˣ) : R →ₐ[k] F where
  __ := LaurentPolynomial.eval₂ (algebraMap k F) u
  commutes' c := LaurentPolynomial.eval₂_C _ _ c

@[simp] private theorem laurentEvalAtUnit_T_one {F : Type*} [Field F] [Algebra k F] (u : Fˣ) :
    laurentEvalAtUnit k u (T 1) = u := by
  change LaurentPolynomial.eval₂ (algebraMap k F) u (T 1) = u
  rw [LaurentPolynomial.eval₂_T, zpow_one]

/-- The fraction field of the Laurent ring is generated by its actual coordinate. -/
theorem laurentFractionCoordinate_generates :
    IntermediateField.adjoin k ({laurentFractionCoordinate k} : Set L) = ⊤ := by
  let E := IntermediateField.adjoin k ({laurentFractionCoordinate k} : Set L)
  let t : E := ⟨laurentFractionCoordinate k, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
  have ht : t ≠ 0 := fun h => laurentFractionCoordinate_ne_zero k (congrArg Subtype.val h)
  let f := laurentEvalAtUnit k (Units.mk0 t ht)
  have hf : E.val.comp f = IsScalarTower.toAlgHom k R L := by
    apply laurentAlgHom_ext
    change (f (T 1) : L) = laurentFractionCoordinate k
    rw [laurentEvalAtUnit_T_one, Units.val_mk0]
  have hmem (a : R) : algebraMap R L a ∈ E := by
    have h := DFunLike.congr_fun hf a
    change (f a : L) = algebraMap R L a at h
    exact h ▸ (f a).property
  apply top_unique
  intro x _
  obtain ⟨a, b, _, hx⟩ := IsFractionRing.div_surjective (A := R) x
  exact hx ▸ E.div_mem (hmem a) (hmem b)

/-- The subfield generated by a positive power of the Laurent coordinate. -/
def laurentPowerField (d : ℕ) : IntermediateField k L :=
  IntermediateField.adjoin k ({(laurentFractionCoordinate k) ^ d} : Set L)

/-- The Laurent pullback by a positive power is injective. -/
theorem kummerAlgHom_injective {d : ℕ} (hd : 0 < d) : Function.Injective (kummerAlgHom k d) := by
  have h : (d : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hd.ne'
  change Function.Injective (Finsupp.mapDomain (fun n : ℤ => (d : ℤ) * n) : (ℤ →₀ k) → (ℤ →₀ k))
  exact Finsupp.mapDomain_injective (fun _ _ hz => mul_left_cancel₀ h hz)

private theorem kummer_polynomial_irreducible {d : ℕ} (hd : 0 < d) :
    Irreducible (KummerExtension.polynomial k d) := by
  let S := KummerExtension k d
  letI : IsDomain S := inferInstanceAs (IsDomain R)
  have hd' : IsDomain (AdjoinRoot (KummerExtension.polynomial k d)) :=
    Equiv.isDomain (KummerExtension.adjoinRootEquiv k d hd).toRingEquiv
  have hprime := (Ideal.Quotient.isDomain_iff_prime (Ideal.span {KummerExtension.polynomial k d})).mp hd'
  have hmonic : (KummerExtension.polynomial k d).Monic := monic_X_pow_sub_C _ hd.ne'
  have h₀ : KummerExtension.polynomial k d ≠ 0 := hmonic.ne_zero
  exact ((Ideal.span_singleton_prime h₀).mp hprime).irreducible

private theorem laurentFractionCoordinate_generates_over (E : IntermediateField k L) :
    IntermediateField.adjoin E ({laurentFractionCoordinate k} : Set L) = ⊤ := by
  apply IntermediateField.restrictScalars_injective k
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.restrictScalars_top,
    laurentFractionCoordinate_generates, sup_top_eq]

private theorem finrank_eq_minpoly_laurentFractionCoordinate (E : IntermediateField k L)
    (ht : IsIntegral E (laurentFractionCoordinate k)) :
    Module.finrank E L = (minpoly E (laurentFractionCoordinate k)).natDegree := by
  rw [← IntermediateField.finrank_top', ← laurentFractionCoordinate_generates_over k E,
    IntermediateField.adjoin.finrank ht]

private theorem exists_laurentPowerFieldEquiv {d : ℕ} (hd : 0 < d) :
    ∃ e : L ≃ₐ[k] laurentPowerField k d,
      (e (laurentFractionCoordinate k) : L) = (laurentFractionCoordinate k) ^ d := by
  let F := laurentPowerField k d
  let t := laurentFractionCoordinate k
  let td : F := ⟨t ^ d, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
  have ht : td ≠ 0 := fun h => pow_ne_zero d (laurentFractionCoordinate_ne_zero k) (congrArg Subtype.val h)
  let f := laurentEvalAtUnit k (Units.mk0 td ht)
  have hfT : f (T 1) = td := by rw [laurentEvalAtUnit_T_one, Units.val_mk0]
  have hf : F.val.comp f = (IsScalarTower.toAlgHom k R L).comp (kummerAlgHom k d) := by
    apply laurentAlgHom_ext
    simp only [AlgHom.comp_apply, hfT, kummerAlgHom_apply, kummer_T, mul_one]
    change t ^ d = algebraMap R L (T (d : ℤ))
    rw [show t = algebraMap R L (T 1) from rfl, ← map_pow, T_pow, mul_one]
  have hcomp : Function.Injective (F.val.comp f) := by
    rw [hf]
    exact (IsFractionRing.injective R L).comp (kummerAlgHom_injective k hd)
  have hfi : Function.Injective f := fun _ _ he => hcomp (congrArg F.val he)
  let g : L →ₐ[k] F := IsFractionRing.liftAlgHom (g := f) hfi
  have hg (a : R) : g (algebraMap R L a) = f a := IsFractionRing.lift_algebraMap hfi a
  have hgT : g t = td := (hg (T 1)).trans hfT
  have hRange : F ≤ (F.val.comp g).fieldRange := by
    change IntermediateField.adjoin k ({t ^ d} : Set L) ≤ _
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact AlgHom.mem_fieldRange.mpr ⟨t, congrArg Subtype.val hgT⟩
  have hgSurj : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp (hRange x.property)
    exact ⟨y, Subtype.ext hy⟩
  let e := AlgEquiv.ofBijective g ⟨g.injective, hgSurj⟩
  exact ⟨e, congrArg Subtype.val hgT⟩

private theorem kummer_fractionPolynomial_irreducible {d : ℕ} (hd : 0 < d) :
    Irreducible ((KummerExtension.polynomial k d).map (algebraMap R L)) := by
  letI : IsPrincipalIdealRing R := StrictEUnit.laurentPolynomial_isPrincipalIdealRing k
  letI : IsIntegrallyClosed R := inferInstance
  have hmonic : (KummerExtension.polynomial k d).Monic := monic_X_pow_sub_C _ hd.ne'
  exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp (kummer_polynomial_irreducible k hd)

/-- The extension of the rational Laurent fraction field over the subfield
generated by its `d`th power has degree exactly `d`. -/
theorem finrank_laurentPowerField {d : ℕ} (hd : 0 < d) :
    Module.finrank (laurentPowerField k d) L = d := by
  let F := laurentPowerField k d
  let t := laurentFractionCoordinate k
  let td : F := ⟨t ^ d, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩
  let P : Polynomial F := X ^ d - Polynomial.C td
  obtain ⟨e, he⟩ := exists_laurentPowerFieldEquiv k hd
  have heT : e (algebraMap R L (T 1)) = td := Subtype.ext he
  let P₀ : Polynomial L := (KummerExtension.polynomial k d).map (algebraMap R L)
  have hmap : P₀.map e.toRingHom = P := by
    simp only [P₀, P, KummerExtension.polynomial, Polynomial.map_sub, Polynomial.map_pow,
      map_X, map_C]
    change X ^ d - Polynomial.C (e (algebraMap R L (T 1))) = X ^ d - Polynomial.C td
    rw [heT]
  have hP : P.Monic := monic_X_pow_sub_C _ hd.ne'
  have hI₀ : Irreducible (P₀.map e.toRingHom) :=
    (Polynomial.mapEquiv e.toRingEquiv).toMulEquiv.irreducible_iff.mpr
      (kummer_fractionPolynomial_irreducible k hd)
  have hI : Irreducible P := hmap ▸ hI₀
  have hroot : Polynomial.aeval t P = 0 := by
    dsimp only [P]
    rw [map_sub, map_pow, aeval_X, aeval_C]
    change t ^ d - t ^ d = 0
    exact sub_self _
  have htI : IsIntegral F t := ⟨P, hP, hroot⟩
  have hmin : P = minpoly F t := minpoly.eq_of_irreducible_of_monic hI hroot hP
  exact (finrank_eq_minpoly_laurentFractionCoordinate k F htI).trans
    ((congrArg Polynomial.natDegree hmin.symm).trans Polynomial.natDegree_X_pow_sub_C)

variable [IsAlgClosed k]

set_option maxHeartbeats 700000 in
/-- Every intermediate field containing the `q`th power is generated by a
power of the actual Laurent coordinate whose exponent divides `q`. -/
theorem intermediateField_eq_laurentPowerField (E : IntermediateField k L) {q : ℕ} (hq : 0 < q)
    (htq : (laurentFractionCoordinate k) ^ q ∈ E) :
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ E = laurentPowerField k d := by
  obtain ⟨hint, htd⟩ := pow_natDegree_minpoly_mem_of_pow_mem E (laurentFractionCoordinate_ne_zero k) hq htq
  let d := (minpoly E (laurentFractionCoordinate k)).natDegree
  have hd : 0 < d := minpoly.natDegree_pos hint
  have hEd : Module.finrank E L = d := finrank_eq_minpoly_laurentFractionCoordinate k E hint
  have hle : laurentPowerField k d ≤ E :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr htd)
  have hFd := finrank_laurentPowerField k hd
  letI : FiniteDimensional (laurentPowerField k d) L :=
    FiniteDimensional.of_finrank_pos (hFd.symm ▸ hd)
  have hEq := IntermediateField.eq_of_le_of_finrank_eq' hle (hFd.trans hEd.symm)
  refine ⟨d, hd, ?_, hEq.symm⟩
  let F := laurentPowerField k q
  have hF : F ≤ E := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr htq)
  let i := IntermediateField.inclusion hF
  letI : Algebra F E := i.toRingHom.toAlgebra
  letI : SMul F E := Algebra.toSMul
  letI : SMul E L := Algebra.toSMul
  letI : SMul F L := Algebra.toSMul
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module F E := Algebra.toModule
  letI : Module E L := Algebra.toModule
  letI : Module F L := Algebra.toModule
  letI : Module.Free E L := Module.Free.of_divisionRing E L
  have h := Module.finrank_mul_finrank F E L
  rw [hEd, finrank_laurentPowerField k hq] at h
  exact ⟨Module.finrank F E, h.symm.trans (Nat.mul_comm _ _)⟩

end LaurentFraction

end WideE
