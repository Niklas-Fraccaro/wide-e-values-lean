import WideE.GaloisRootsOfUnity
import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Finite Galois enlargement for abelian p-group cocycles

A finite p-group acting on a nontrivial abelian p-group of coefficients has
a fixed cyclic subgroup of order p. Quotienting by this subgroup reduces
the size of the coefficients. The remaining cocycle takes values in the
fixed subgroup and vanishes after a finite Galois enlargement.
-/

noncomputable section

namespace WideE

section PrimeOrder

variable {p : ℕ} [Fact p.Prime]
variable {P M : Type*} [Group P] [CommGroup M] [Finite M] [MulDistribMulAction P M]

/-- A p-group acting on a nontrivial finite abelian p-group has a fixed
element of order p. -/
theorem exists_fixed_prime_order [Nontrivial M] (hP : IsPGroup p P) (hM : IsPGroup p M) :
    ∃ x : M, orderOf x = p ∧ ∀ g : P, g • x = x := by
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial M)).ne' hn
  have hpM : p ∣ Nat.card M := by
    rw [hn]
    exact dvd_pow_self _ hn0
  obtain ⟨x, hx, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hpM
    (a := 1) (fun g => smul_one g)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hM x
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero, orderOf_eq_one_iff] at hk
    exact hne hk.symm
  have hpx : p ∣ orderOf x := by
    rw [hk]
    exact dvd_pow_self _ hk0
  refine ⟨x ^ (orderOf x / p), orderOf_pow_orderOf_div (orderOf_pos x).ne' hpx, fun g => ?_⟩
  rw [smul_pow', hx g]

end PrimeOrder

section Quotient

variable {P M : Type*} [Group P] [CommGroup M] [MulDistribMulAction P M]

variable (J : Subgroup M) (hJ : ∀ (g : P) (x : M), x ∈ J → g • x ∈ J)

private def quotientActionMap (g : P) : (M ⧸ J) →* (M ⧸ J) :=
  QuotientGroup.map J J (MulDistribMulAction.toMonoidHom M g) (hJ g)

/-- A compatible action on an abelian group descends to a stable subgroup quotient. -/
def quotientMulDistribMulAction : MulDistribMulAction P (M ⧸ J) where
  smul g := quotientActionMap J hJ g
  one_smul q := Quotient.inductionOn' q fun x =>
    congrArg (QuotientGroup.mk' J) (one_smul P x)
  mul_smul g h q := Quotient.inductionOn' q fun x =>
    congrArg (QuotientGroup.mk' J) (mul_smul g h x)
  smul_mul g := map_mul (quotientActionMap J hJ g)
  smul_one g := map_one (quotientActionMap J hJ g)

end Quotient

section Cocycle

variable {G P M : Type*} [Group G] [Group P] [CommGroup M] [MulDistribMulAction P M]

/-- A normalized multiplicative 2-cocycle for an action through `ρ`. -/
structure NormalizedMulTwoCocycle (ρ : G →* P) (M : Type*) [CommGroup M]
    [MulDistribMulAction P M] where
  value : G → G → M
  one_left : ∀ g, value 1 g = 1
  one_right : ∀ g, value g 1 = 1
  cocycle : ∀ g h j, value g h * value (g * h) j = (ρ g • value h j) * value g (h * j)

attribute [simp] NormalizedMulTwoCocycle.one_left NormalizedMulTwoCocycle.one_right

/-- The inhomogeneous coboundary of a 1-cochain. -/
def mulTwoCoboundary (ρ : G →* P) (b : G → M) (g h : G) : M :=
  b g * (ρ g • b h) / b (g * h)

namespace NormalizedMulTwoCocycle

variable {ρ : G →* P} (c : NormalizedMulTwoCocycle ρ M)

/-- Extend a cocycle along a group homomorphism acting on its indices. -/
def comap {K : Type*} [Group K] (r : K →* G) : NormalizedMulTwoCocycle (ρ.comp r) M where
  value g h := c.value (r g) (r h)
  one_left g := by simp
  one_right g := by simp
  cocycle g h j := by
    simpa only [map_mul, MonoidHom.comp_apply] using c.cocycle (r g) (r h) (r j)

/-- Map the values of a cocycle along an equivariant homomorphism. -/
def map {N : Type*} [CommGroup N] [MulDistribMulAction P N]
    (f : M →* N) (hf : ∀ (g : P) (x : M), f (g • x) = g • f x) :
    NormalizedMulTwoCocycle ρ N where
  value g h := f (c.value g h)
  one_left g := by simp
  one_right g := by simp
  cocycle g h j := by
    rw [← map_mul, ← hf, ← map_mul, c.cocycle]

/-- Divide two cocycles for the same action. -/
def div (d : NormalizedMulTwoCocycle ρ M) : NormalizedMulTwoCocycle ρ M where
  value g h := c.value g h / d.value g h
  one_left g := by simp
  one_right g := by simp
  cocycle g h j := by
    rw [div_mul_div_comm, c.cocycle, d.cocycle, ← div_mul_div_comm, ← smul_div']

private theorem div_mul_left_cancel {A : Type*} [CommGroup A] (x a b t : A) :
    a / x * (x * b / t) = a * b / t := by
  rw [div_mul_div_comm, mul_left_comm a x b, mul_div_mul_left_eq_div]

/-- A normalized 1-cochain has a normalized 2-cocycle as its coboundary. -/
def ofCoboundary (b : G → M) (hb : b 1 = 1) : NormalizedMulTwoCocycle ρ M where
  value := mulTwoCoboundary ρ b
  one_left g := by simp [mulTwoCoboundary, hb]
  one_right g := by simp [mulTwoCoboundary, hb]
  cocycle g h j := by
    simp only [mulTwoCoboundary, smul_div', smul_mul', ← mul_smul, ← map_mul, mul_assoc g h j]
    rw [div_mul_left_cancel, mul_comm (b g) (ρ g • b (h * j)), div_mul_left_cancel]
    simp only [mul_assoc, mul_comm, mul_left_comm]

end NormalizedMulTwoCocycle

private theorem stable_of_pointwise_fixed (J : Subgroup M)
    (hFix : ∀ (g : P) (x : J), g • (x : M) = x) :
    ∀ (g : P) (x : M), x ∈ J → g • x ∈ J := by
  intro g x hx
  rw [show g • x = x from hFix g ⟨x, hx⟩]
  exact hx

private theorem exists_fixed_kernel_correction
    {ρ : G →* P} (c : NormalizedMulTwoCocycle ρ M)
    (J : Subgroup M) (hFix : ∀ (g : P) (x : J), g • (x : M) = x)
    (bQ : G → M ⧸ J)
    (hQ : letI := quotientMulDistribMulAction J (stable_of_pointwise_fixed J hFix)
          ∀ g h, QuotientGroup.mk' J (c.value g h) = mulTwoCoboundary ρ bQ g h) :
    ∃ (b : G → M) (α : G → G → J),
      (∀ g, α 1 g = 1) ∧ (∀ g, α g 1 = 1) ∧
      (∀ g h j, α g h * α (g * h) j = α h j * α g (h * j)) ∧
      (∀ g h, c.value g h = (α g h : M) * mulTwoCoboundary ρ b g h) := by
  classical
  letI := quotientMulDistribMulAction J (stable_of_pointwise_fixed J hFix)
  let q := QuotientGroup.mk' J
  have hCompat (g : P) (x : M) : q (g • x) = g • q x := rfl
  have hbQOne : bQ 1 = 1 := by
    simpa [mulTwoCoboundary] using (hQ 1 1).symm
  let b (g : G) := if g = 1 then 1 else (QuotientGroup.mk'_surjective J (bQ g)).choose
  have hbOne : b 1 = 1 := by simp [b]
  have hb (g : G) : q (b g) = bQ g := by
    by_cases hg : g = 1
    · simp [hg, hbOne, hbQOne]
    · simpa only [b, if_neg hg] using (QuotientGroup.mk'_surjective J (bQ g)).choose_spec
  let d := c.div (NormalizedMulTwoCocycle.ofCoboundary b hbOne)
  have hMem (g h : G) : d.value g h ∈ J := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (c.value g h / mulTwoCoboundary ρ b g h) = 1
    rw [map_div, div_eq_one, hQ g h]
    simp only [mulTwoCoboundary, map_div, map_mul, hCompat, hb]
  let α (g h : G) : J := ⟨d.value g h, hMem g h⟩
  refine ⟨b, α, fun g => Subtype.ext (d.one_left g),
    fun g => Subtype.ext (d.one_right g), ?_, ?_⟩
  · intro g h j
    apply Subtype.ext
    have hFixed : ρ g • d.value h j = d.value h j := hFix (ρ g) (α h j)
    simpa only [hFixed] using d.cocycle g h j
  · intro g h
    change c.value g h = c.value g h / mulTwoCoboundary ρ b g h * mulTwoCoboundary ρ b g h
    rw [div_mul_cancel]

end Cocycle

section Fields

open IntermediateField

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- Galois restriction between nested finite Galois subfields of the same field. -/
def restrictFiniteGalois {E L : FiniteGaloisIntermediateField F Ω} (h : E ≤ L) :
    (L ≃ₐ[F] L) →* E ≃ₐ[F] E := by
  letI : Algebra E L := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom E

theorem restrictFiniteGalois_comp {E L N : FiniteGaloisIntermediateField F Ω}
    (hEL : E ≤ L) (hLN : L ≤ N) :
    (restrictFiniteGalois hEL).comp (restrictFiniteGalois hLN) =
      restrictFiniteGalois (hEL.trans hLN) := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : Algebra L N := (IntermediateField.inclusion hLN).toAlgebra
  letI : Algebra E N := (IntermediateField.inclusion (hEL.trans hLN)).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower E L N := IsScalarTower.of_algebraMap_eq' rfl
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp F E L N).symm

variable [CharZero F] [IsAlgClosed Ω] [IsGalois F Ω]

/-- A cocycle with constant coefficients of prime order vanishes over a finite
Galois enlargement, provided the base contains the corresponding roots of unity. -/
theorem exists_constant_prime_coboundary
    (hF : IsC1 F) {p : ℕ} [Fact p.Prime] (hζ : (primitiveRoots p F).Nonempty)
    {C : Type*} [CommGroup C] (hC : Nat.card C = p)
    (E : FiniteGaloisIntermediateField F Ω)
    (α : (E ≃ₐ[F] E) → (E ≃ₐ[F] E) → C)
    (hOneLeft : ∀ σ, α 1 σ = 1) (hOneRight : ∀ σ, α σ 1 = 1)
    (hα : ∀ σ τ ρ, α σ τ * α (σ * τ) ρ = α τ ρ * α σ (τ * ρ)) :
    ∃ (L : FiniteGaloisIntermediateField F Ω) (hEL : E ≤ L),
      ∃ b : (L ≃ₐ[F] L) → C, ∀ σ τ,
        α (restrictFiniteGalois hEL σ) (restrictFiniteGalois hEL τ) =
          b σ * b τ / b (σ * τ) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hCard : Nat.card (rootsOfUnity p F) = p := by
    rw [Nat.card_eq_fintype_card]
    exact ((mem_primitiveRoots (NeZero.pos p)).mp hζ.choose_spec).card_rootsOfUnity
  let e : C ≃* rootsOfUnity p F := mulEquivOfPrimeCardEq hC hCard
  let uE : (rootsOfUnity p F) →* Eˣ :=
    (Units.map (algebraMap F E).toMonoidHom).comp (rootsOfUnity p F).subtype
  let cE : GaloisTwoCocycle F E :=
    { value := fun σ τ => uE (e (α σ τ))
      one_left := fun σ => by rw [hOneLeft, map_one, map_one]
      one_right := fun σ => by rw [hOneRight, map_one, map_one]
      cocycle := fun σ τ ρ => by
        have hFixed (u : rootsOfUnity p F) :
            Units.map σ.toRingEquiv.toMonoidHom (uE u) = uE u :=
          Units.ext (σ.commutes ((u : Fˣ) : F))
        change uE (e (α σ τ)) * uE (e (α (σ * τ) ρ)) =
          Units.map σ.toRingEquiv.toMonoidHom (uE (e (α τ ρ))) * uE (e (α σ (τ * ρ)))
        rw [hFixed, ← map_mul uE, ← map_mul uE, ← map_mul e, ← map_mul e, hα] }
  have hPow (σ τ : E ≃ₐ[F] E) : cE.value σ τ ^ p = 1 := by
    let u := e (α σ τ)
    change (Units.map (algebraMap F E).toMonoidHom (u : Fˣ)) ^ p = 1
    rw [← map_pow, (mem_rootsOfUnity p (u : Fˣ)).mp u.property, map_one]
  obtain ⟨L, hEL, hLfin, hLGal, hLift⟩ :=
    cE.exists_finiteGalois_rootsOfUnity_coboundary hF (NeZero.pos p) hPow
  let L' : FiniteGaloisIntermediateField F Ω :=
    { toIntermediateField := L, finiteDimensional := hLfin, isGalois := hLGal }
  let h' : E ≤ L' := hEL
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨d, hdPow, hd⟩ := hLift
  let ψ := rootsOfUnityEquivOfPrimitiveRoots (f := algebraMap F L)
    (algebraMap F L).injective hζ
  let w (σ : L ≃ₐ[F] L) : rootsOfUnity p F :=
    ψ.symm ⟨d σ, (mem_rootsOfUnity p (d σ)).mpr (hdPow σ)⟩
  let uL : (rootsOfUnity p F) →* Lˣ :=
    (Units.map (algebraMap F L).toMonoidHom).comp (rootsOfUnity p F).subtype
  have hUinj : Function.Injective uL :=
    (Units.map_injective (algebraMap F L).injective).comp Subtype.coe_injective
  have hLifted (σ : L ≃ₐ[F] L) : uL (w σ) = d σ :=
    Units.ext (rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      (algebraMap F L).injective hζ ⟨d σ, (mem_rootsOfUnity p (d σ)).mpr (hdPow σ)⟩)
  refine ⟨L', h', fun σ => e.symm (w σ), fun σ τ => ?_⟩
  apply e.injective
  apply hUinj
  rw [map_div e, map_mul e, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply,
    map_div uL, map_mul uL, hLifted, hLifted, hLifted]
  have h := hd σ τ
  change Units.map (algebraMap E L).toMonoidHom
      (uE (e (α (restrictFiniteGalois h' σ) (restrictFiniteGalois h' τ)))) =
    d σ * Units.map σ.toRingEquiv.toMonoidHom (d τ) / d (σ * τ) at h
  have hMap (u : rootsOfUnity p F) : Units.map (algebraMap E L).toMonoidHom (uE u) = uL u :=
    Units.ext (IsScalarTower.algebraMap_apply F E L ((u : Fˣ) : F)).symm
  have hFixed : Units.map σ.toRingEquiv.toMonoidHom (d τ) = d τ := by
    rw [← hLifted τ]
    exact Units.ext (σ.commutes ((w τ : Fˣ) : F))
  rw [hMap, hFixed] at h
  exact h

universe u

/-- When the action on finite abelian p-group coefficients factors through a
p-group, every normalized 2-cocycle becomes a coboundary over a finite
Galois enlargement of a characteristic-zero C₁ field. -/
theorem exists_pGroup_coboundary_after_finiteGalois
    (hF : IsC1 F) {p : ℕ} [Fact p.Prime] (hζ : (primitiveRoots p F).Nonempty)
    {P : Type*} [Group P] (hP : IsPGroup p P)
    {M : Type u} [CommGroup M] [Finite M] [MulDistribMulAction P M] (hM : IsPGroup p M)
    (E : FiniteGaloisIntermediateField F Ω) (ρ : (E ≃ₐ[F] E) →* P)
    (c : NormalizedMulTwoCocycle ρ M) :
    ∃ (L : FiniteGaloisIntermediateField F Ω) (hEL : E ≤ L),
      ∃ b : (L ≃ₐ[F] L) → M, ∀ σ τ,
        c.value (restrictFiniteGalois hEL σ) (restrictFiniteGalois hEL τ) =
          mulTwoCoboundary (ρ.comp (restrictFiniteGalois hEL)) b σ τ := by
  classical
  have hKill (n : ℕ) :
      ∀ (A : Type u) [CommGroup A] [Finite A] [MulDistribMulAction P A],
        Nat.card A = n → IsPGroup p A →
        ∀ (B : FiniteGaloisIntermediateField F Ω) (r : (B ≃ₐ[F] B) →* P)
          (e : NormalizedMulTwoCocycle r A),
          ∃ (C : FiniteGaloisIntermediateField F Ω) (hBC : B ≤ C),
            ∃ b : (C ≃ₐ[F] C) → A, ∀ σ τ,
              e.value (restrictFiniteGalois hBC σ) (restrictFiniteGalois hBC τ) =
                mulTwoCoboundary (r.comp (restrictFiniteGalois hBC)) b σ τ := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ _ _ hCard hA B r e
      rcases subsingleton_or_nontrivial A with hSub | hNon
      · exact ⟨B, le_rfl, fun _ => 1, fun _ _ => Subsingleton.elim _ _⟩
      letI : Nontrivial A := hNon
      obtain ⟨x, hxOrder, hxFix⟩ := exists_fixed_prime_order hP hA
      let J := Subgroup.zpowers x
      have hFix (g : P) (y : J) : g • (y : A) = y := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.property
        rw [← hk]
        have h := map_zpow (MulDistribMulAction.toMonoidHom A g) x k
        change g • (x ^ k) = (g • x) ^ k at h
        rw [h, hxFix]
      have hJCard : Nat.card J = p := (Nat.card_zpowers x).trans hxOrder
      have hCount : p * Nat.card (A ⧸ J) = n := by
        rw [← hJCard, ← Subgroup.index_eq_card, J.card_mul_index, hCard]
      have hLt : Nat.card (A ⧸ J) < n := by
        have h := Nat.mul_lt_mul_of_pos_right (Fact.out : p.Prime).one_lt
          (Nat.card_pos (α := A ⧸ J))
        simpa only [one_mul, hCount] using h
      letI := quotientMulDistribMulAction J (stable_of_pointwise_fixed J hFix)
      let q := QuotientGroup.mk' J
      let eQ := e.map q (fun _ _ => rfl)
      obtain ⟨C, hBC, bQ, hbQ⟩ :=
        ih (Nat.card (A ⧸ J)) hLt (A ⧸ J) rfl (hA.to_quotient J) B r eQ
      let r₁ := restrictFiniteGalois hBC
      let eC := e.comap r₁
      obtain ⟨b, α, hLeft, hRight, hα, hFactor⟩ :=
        exists_fixed_kernel_correction eC J hFix bQ hbQ
      obtain ⟨D, hCD, a, ha⟩ :=
        exists_constant_prime_coboundary hF hζ hJCard C α hLeft hRight hα
      let r₂ := restrictFiniteGalois hCD
      let r₃ := restrictFiniteGalois (hBC.trans hCD)
      have hRes (σ : D ≃ₐ[F] D) : r₁ (r₂ σ) = r₃ σ :=
        DFunLike.congr_fun (restrictFiniteGalois_comp hBC hCD) σ
      refine ⟨D, hBC.trans hCD, fun σ => (a σ : A) * b (r₂ σ), fun σ τ => ?_⟩
      have h := hFactor (r₂ σ) (r₂ τ)
      change e.value (r₁ (r₂ σ)) (r₁ (r₂ τ)) =
        (α (r₂ σ) (r₂ τ) : A) * mulTwoCoboundary (r.comp r₁) b (r₂ σ) (r₂ τ) at h
      rw [hRes σ, hRes τ, ha] at h
      refine h.trans ?_
      simp only [Subgroup.coe_div, Subgroup.coe_mul, mulTwoCoboundary, MonoidHom.comp_apply,
        smul_mul', hFix, map_mul r₂]
      rw [mul_mul_mul_comm (a σ : A), ← div_mul_div_comm, hRes σ]
  exact hKill (Nat.card M) M rfl hM E ρ c

end Fields

end WideE
