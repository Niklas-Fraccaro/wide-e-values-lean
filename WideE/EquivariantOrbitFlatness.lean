import WideE.GenericFreeness
import AlgebraicPoint
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# Flatness for a morphism equivariant under a transitive action

A principal open supplied by generic freeness can be translated to cover
the maximal points of the source. On an affine chart, lifting each
rational point then proves faithful flatness.
-/

noncomputable section

namespace WideE

section ClosedPoints

variable {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B]

private theorem exists_kPoint_nonzero_of_not_isNilpotent {b : B} (h : ¬ IsNilpotent b) :
    ∃ p : B →ₐ[k] k, p b ≠ 0 := by
  letI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k) (B := B)
  let D := PrimeSpectrum.basicOpen b
  have hNE : (D : Set (PrimeSpectrum B)).Nonempty := by
    by_contra hn
    apply h ((PrimeSpectrum.basicOpen_eq_bot_iff b).mp ?_)
    exact TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.mp hn)
  obtain ⟨x, hx, hClosed⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing _
    D.isOpen hNE
  letI := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hClosed
  let p := StrictEUnit.maximalIdealPoint (k := k) x.asIdeal
  refine ⟨p, fun hz => hx ?_⟩
  change b ∈ x.asIdeal
  rw [← StrictEUnit.maximalIdealPoint_ker (k := k) x.asIdeal]
  exact RingHom.mem_ker.mpr hz

end ClosedPoints

section Equivariance

universe u

variable {k : Type*} {A B : Type u}
  [Field k] [IsAlgClosed k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- An injective morphism into a finite-type algebra over an algebraically
closed field is flat if compatible algebra automorphisms act transitively
on the source's closed points. -/
theorem flat_of_transitive_closedPoints [IsDomain A] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f)
    (hAction : ∀ p q : B →ₐ[k] k, ∃ (eA : A ≃ₐ[k] A) (eB : B ≃ₐ[k] B),
      eB.toAlgHom.comp f = f.comp eA.toAlgHom ∧ p.comp eB.toAlgHom = q) :
    f.toRingHom.Flat := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  obtain ⟨d, hd, hFlat⟩ := exists_flat_localizationAway (A := A) (B := B)
  change Module.Flat A (Localization.Away (f d)) at hFlat
  have hFlat' : ((algebraMap B (Localization.Away (f d))).comp f.toRingHom).Flat :=
    flat_algebraMap_iff.mpr hFlat
  obtain ⟨q, hq⟩ := exists_kPoint_nonzero_of_not_isNilpotent (k := k)
    (show ¬ IsNilpotent (f d) from fun h =>
      hd (isNilpotent_iff_eq_zero.mp ((IsNilpotent.map_iff hf).mp h)))
  let E : Set B := {b | ∃ (eA : A ≃ₐ[k] A) (eB : B ≃ₐ[k] B),
    eB.toAlgHom.comp f = f.comp eA.toAlgHom ∧ eB (f d) = b}
  have hSpan : Ideal.span E = ⊤ := by
    by_contra hProper
    obtain ⟨m, hm, hLe⟩ := (Ideal.span E).exists_le_maximal hProper
    letI := hm
    let p := StrictEUnit.maximalIdealPoint (k := k) m
    obtain ⟨eA, eB, he, hp⟩ := hAction p q
    have hMem : eB (f d) ∈ m := hLe (Ideal.subset_span ⟨eA, eB, he, rfl⟩)
    rw [← StrictEUnit.maximalIdealPoint_ker (k := k) m] at hMem
    apply hq
    exact (DFunLike.congr_fun hp (f d)).symm.trans hMem
  apply RingHom.Flat.ofLocalizationSpanTarget f.toRingHom E hSpan
  rintro ⟨b, eA, eB, he, rfl⟩
  change ((algebraMap B (Localization.Away (eB (f d)))).comp f.toRingHom).Flat
  let eL : Localization.Away (f d) ≃+* Localization.Away (eB (f d)) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (f d))
      (T := Submonoid.powers (eB (f d))) _ _ eB.toRingEquiv (Submonoid.map_powers _ _)
  have hLocal (x : B) : eL (algebraMap B (Localization.Away (f d)) x) =
      algebraMap B (Localization.Away (eB (f d))) (eB x) :=
    IsLocalization.ringEquivOfRingEquiv_eq _ _
  have hMap : (algebraMap B (Localization.Away (eB (f d)))).comp f.toRingHom =
      eL.toRingHom.comp (((algebraMap B (Localization.Away (f d))).comp
        f.toRingHom).comp eA.symm.toRingEquiv.toRingHom) := by
    apply RingHom.ext
    intro x
    change algebraMap B _ (f x) = eL (algebraMap B _ (f (eA.symm x)))
    rw [hLocal, show eB (f (eA.symm x)) = f (eA (eA.symm x)) from
      DFunLike.congr_fun he _, AlgEquiv.apply_symm_apply]
  rw [hMap]
  exact ((RingHom.Flat.of_bijective eA.symm.bijective).comp hFlat').comp
    (RingHom.Flat.of_bijective eL.bijective)

end Equivariance

section Faithfulness

variable {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- For a flat algebra over an affine base of finite type, a lift of every
closed point detects faithful flatness. -/
theorem faithfullyFlat_of_lift_kPoints [Algebra.FiniteType k A] [Module.Flat A B]
    (h : ∀ p : A →ₐ[k] k, ∃ q : B →ₐ[k] k, q.comp (IsScalarTower.toAlgHom k A B) = p) :
    Module.FaithfullyFlat A B := by
  constructor
  intro m hm
  letI := hm
  let p := StrictEUnit.maximalIdealPoint (k := k) m
  obtain ⟨q, hq⟩ := h p
  have hLe : m.map (algebraMap A B) ≤ RingHom.ker q.toRingHom := by
    apply (Ideal.map_le_iff_le_comap).mpr
    intro x hx
    change q (algebraMap A B x) = 0
    rw [show q (algebraMap A B x) = p x from DFunLike.congr_fun hq x]
    exact RingHom.mem_ker.mp (StrictEUnit.maximalIdealPoint_ker (k := k) m ▸ hx)
  rw [Ideal.smul_top_eq_map]
  intro hTop
  have ht := (Submodule.restrictScalars_eq_top_iff A B _).mp hTop
  exact (RingHom.ker_ne_top q.toRingHom) (top_le_iff.mp (ht ▸ hLe))

end Faithfulness

section Charts

universe u

variable {k : Type*} {A B : Type u}
  [Field k] [IsAlgClosed k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The morphism obtained by localizing a map at one base coordinate. -/
abbrev localizationAwayAlgHom (f : A →ₐ[k] B) (a : A) :
    Localization.Away a →ₐ[k] Localization.Away (f a) :=
  IsLocalization.Away.mapₐ _ _ f a

omit [IsAlgClosed k] in
@[simp]
theorem localizationAwayAlgHom_algebraMap (f : A →ₐ[k] B) (a x : A) :
    localizationAwayAlgHom f a (algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away (f a)) (f x) := by
  rw [localizationAwayAlgHom, IsLocalization.Away.mapₐ_apply]
  exact IsLocalization.map_eq _ _

omit [IsAlgClosed k] in
/-- A point where the chosen coordinate is a unit extends to the affine chart. -/
def localizationAway_kPoint (p : A →ₐ[k] k) (a : A) (ha : p a ≠ 0) :
    Localization.Away a →ₐ[k] k where
  toRingHom := IsLocalization.Away.lift a (isUnit_iff_ne_zero.mpr ha)
  commutes' r := by
    change IsLocalization.Away.lift (g := p.toRingHom) a (isUnit_iff_ne_zero.mpr ha)
      (algebraMap k (Localization.Away a) r) = algebraMap k k r
    rw [IsScalarTower.algebraMap_apply k A (Localization.Away a),
      IsLocalization.Away.lift_eq]
    exact p.commutes r

omit [IsAlgClosed k] in
@[simp]
theorem localizationAway_kPoint_algebraMap (p : A →ₐ[k] k) (a : A) (ha : p a ≠ 0) (x : A) :
    localizationAway_kPoint p a ha (algebraMap A (Localization.Away a) x) = p x :=
  IsLocalization.Away.lift_eq a (isUnit_iff_ne_zero.mpr ha) x

/-- A flat morphism that lifts the closed points of a principal open is
faithfully flat over that open. -/
theorem faithfullyFlat_localizationAway_of_lift_kPoints [Algebra.FiniteType k A]
    (f : A →ₐ[k] B) (hFlat : f.toRingHom.Flat) (a : A)
    (hLift : ∀ p : A →ₐ[k] k, p a ≠ 0 → ∃ q : B →ₐ[k] k, q.comp f = p) :
    letI : Algebra (Localization.Away a) (Localization.Away (f a)) :=
      (localizationAwayAlgHom f a).toRingHom.toAlgebra
    Module.FaithfullyFlat (Localization.Away a) (Localization.Away (f a)) := by
  let A' := Localization.Away a
  let B' := Localization.Away (f a)
  let e := localizationAwayAlgHom f a
  letI : Algebra A' B' := e.toRingHom.toAlgebra
  letI : IsScalarTower k A' B' := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  letI := IsLocalization.Away.finitePresentation a (S := A')
  letI : Algebra.FiniteType k A' := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k A) (inferInstance : Algebra.FiniteType A A')
  have hFlat' : e.toRingHom.Flat :=
    RingHom.Flat.propertyIsLocal.localizationAwayPreserves f.toRingHom a A' B' hFlat
  letI : Module.Flat A' B' := flat_algebraMap_iff.mp hFlat'
  apply faithfullyFlat_of_lift_kPoints (k := k)
  intro p
  let p₀ := p.comp (IsScalarTower.toAlgHom k A A')
  have hp : p₀ a ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := A') a).map p.toRingHom).ne_zero
  obtain ⟨q, hq⟩ := hLift p₀ hp
  have hqNe : q (f a) ≠ 0 := fun hZero => hp ((DFunLike.congr_fun hq a).symm.trans hZero)
  let q' := localizationAway_kPoint q (f a) hqNe
  refine ⟨q', ?_⟩
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (M := Submonoid.powers a)
  apply RingHom.ext
  intro x
  change q' (e (algebraMap A A' x)) = p (algebraMap A A' x)
  rw [show e (algebraMap A A' x) = algebraMap B B' (f x)
    from localizationAwayAlgHom_algebraMap f a x, localizationAway_kPoint_algebraMap]
  exact DFunLike.congr_fun hq x

end Charts

end WideE
