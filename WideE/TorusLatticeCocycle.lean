import WideE.TorusLattice
import WideE.TorusGaloisExponent

/-!
# Galois cocycles in torus coordinates

Inflation preserves cocycles and reflects triviality. On a subgroup
acting trivially on the lattice, Hilbert 90 applies to each coordinate.
-/

noncomputable section

namespace WideE

open IntermediateField

section Cocycle

variable {F K Λ : Type*} [Field F] [Field K] [Algebra F K] [AddCommGroup Λ]

abbrev torusLatticeAct (ρ : (K ≃ₐ[F] K) →* MulAut (Multiplicative Λ)) :
    (K ≃ₐ[F] K) → TorusLatticePoint Λ K → TorusLatticePoint Λ K :=
  (torusLatticeAction ρ).smul

/-- The cocycle equation for the semilinear action on torus lattice points. -/
def IsTorusLatticeCocycle (ρ : (K ≃ₐ[F] K) →* MulAut (Multiplicative Λ))
    (c : (K ≃ₐ[F] K) → TorusLatticePoint Λ K) : Prop :=
  ∀ σ τ, c (σ * τ) = c σ * torusLatticeAct ρ σ (c τ)

/-- The equation for a right-action trivialization. -/
def IsTorusLatticeCoboundary (ρ : (K ≃ₐ[F] K) →* MulAut (Multiplicative Λ))
    (c : (K ≃ₐ[F] K) → TorusLatticePoint Λ K) : Prop :=
  ∃ b : TorusLatticePoint Λ K, ∀ σ, c σ * torusLatticeAct ρ σ b = b

theorem IsTorusLatticeCocycle.one
    {ρ : (K ≃ₐ[F] K) →* MulAut (Multiplicative Λ)}
    {c : (K ≃ₐ[F] K) → TorusLatticePoint Λ K} (hc : IsTorusLatticeCocycle ρ c) :
    c 1 = 1 := by
  have h := hc 1 1
  have hAct : torusLatticeAct ρ 1 (c 1) = c 1 := (torusLatticeAction ρ).one_smul (c 1)
  rw [one_mul, hAct] at h
  apply MonoidHom.ext
  intro x
  have hx : c 1 x = c 1 x * c 1 x := DFunLike.congr_fun h x
  exact (mul_left_cancel ((mul_one (c 1 x)).trans hx)).symm

end Cocycle

section Inflation

variable {F Ω Λ ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [AddCommGroup Λ]
variable {E L : FiniteGaloisIntermediateField F Ω}
variable {ρ : (E ≃ₐ[F] E) →* MulAut (Multiplicative Λ)}

/-- Inflating a cocycle extends points and restricts Galois indices. -/
def inflateTorusLatticeCocycle (hEL : E ≤ L)
    (c : (E ≃ₐ[F] E) → TorusLatticePoint Λ E) (σ : L ≃ₐ[F] L) :
    TorusLatticePoint Λ L :=
  extendTorusLatticePoint hEL (c (restrictFiniteGalois hEL σ))

theorem IsTorusLatticeCocycle.inflate {c : (E ≃ₐ[F] E) → TorusLatticePoint Λ E}
    (hc : IsTorusLatticeCocycle ρ c) (hEL : E ≤ L) :
    IsTorusLatticeCocycle (ρ.comp (restrictFiniteGalois hEL))
      (inflateTorusLatticeCocycle hEL c) := by
  intro σ τ
  rw [inflateTorusLatticeCocycle, map_mul (restrictFiniteGalois hEL), hc, map_mul]
  exact congrArg (extendTorusLatticePoint hEL (c (restrictFiniteGalois hEL σ)) * ·)
    (extendTorusLatticePoint_smul hEL ρ σ (c (restrictFiniteGalois hEL τ)))

private theorem torusCoords_act_over_subfield (basis : Basis ι ℤ Λ) (hEL : E ≤ L)
    (x : TorusLatticePoint Λ L) (i : ι) :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
    letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ σ : L ≃ₐ[E] L, latticeCharacterCoords basis
        (torusLatticeAct (ρ.comp (restrictFiniteGalois hEL)) (σ.restrictScalars F) x) i =
      Units.map σ.toRingEquiv.toMonoidHom (latticeCharacterCoords basis x i) := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  intro σ
  have hRes : restrictFiniteGalois hEL (σ.restrictScalars F) = 1 :=
    (galoisOverFieldEquivKer hEL σ).property
  change Units.map σ.toRingEquiv.toMonoidHom
    (x (((ρ (restrictFiniteGalois hEL (σ.restrictScalars F)))⁻¹)
      (Multiplicative.ofAdd (basis i)))) = _
  rw [hRes, map_one ρ, inv_one]
  rfl

private theorem exists_units_of_galois_fixed
    {E K : Type*} [Field E] [Field K] [Algebra E K] [IsGalois E K]
    (x : Kˣ) (hx : ∀ σ : K ≃ₐ[E] K, σ (x : K) = x) :
    ∃ y : Eˣ, Units.map (algebraMap E K).toMonoidHom y = x := by
  have h : (x : K) ∈ fixedField (⊤ : Subgroup (K ≃ₐ[E] K)) :=
    (mem_fixedField_iff _ _).mpr (fun σ _ => hx σ)
  rw [InfiniteGalois.fixedField_bot] at h
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp h
  have hyne : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hyne, Units.ext hy⟩

/-- A trivialization of an inflated torus cocycle descends to the original field. -/
theorem IsTorusLatticeCoboundary.of_inflate (basis : Basis ι ℤ Λ) (hEL : E ≤ L)
    {c : (E ≃ₐ[F] E) → TorusLatticePoint Λ E} (hc : IsTorusLatticeCocycle ρ c)
    (h : IsTorusLatticeCoboundary (ρ.comp (restrictFiniteGalois hEL))
      (inflateTorusLatticeCocycle hEL c)) : IsTorusLatticeCoboundary ρ c := by
  obtain ⟨a, ha⟩ := h
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  letI := IsGalois.tower_top_of_isGalois F E L
  let r := restrictFiniteGalois hEL
  let j := extendTorusLatticePoint (Λ := Λ) hEL
  let e := latticeCharacterCoords (B := Eˣ) basis
  let f := latticeCharacterCoords (B := Lˣ) basis
  have hFix (σ : L ≃ₐ[E] L) (i : ι) : σ (f a i : L) = f a i := by
    let s := σ.restrictScalars F
    have hRes : r s = 1 := (galoisOverFieldEquivKer hEL σ).property
    have hh := ha s
    change j (c (r s)) * torusLatticeAct (ρ.comp r) s a = a at hh
    rw [hRes, hc.one, map_one] at hh
    have hh' : torusLatticeAct (ρ.comp r) s a = a :=
      (one_mul (torusLatticeAct (ρ.comp r) s a)).symm.trans hh
    have hCoords := congrFun (congrArg f hh') i
    have hOver := torusCoords_act_over_subfield (ρ := ρ) basis hEL a i σ
    exact congrArg Units.val (hOver.symm.trans hCoords)
  choose b₀ hb₀ using fun i => exists_units_of_galois_fixed (f a i) (fun σ => hFix σ i)
  let b := e.symm b₀
  have hb : j b = a := by
    apply f.injective
    funext i
    change Units.map (algebraMap E L).toMonoidHom (e b i) = f a i
    rw [congrFun (e.apply_symm_apply b₀) i, hb₀]
  refine ⟨b, fun τ => (extendTorusLatticePoint_injective hEL) ?_⟩
  obtain ⟨σ, hσ⟩ := restrictFiniteGalois_surjective hEL τ
  have hh := ha σ
  change j (c (r σ)) * torusLatticeAct (ρ.comp r) σ a = a at hh
  rw [← hb] at hh
  have hAct := extendTorusLatticePoint_smul hEL ρ σ b
  change j (torusLatticeAct ρ (r σ) b) = torusLatticeAct (ρ.comp r) σ (j b) at hAct
  rw [← hAct, show r σ = τ from hσ, ← map_mul] at hh
  exact hh

/-- On the subgroup that fixes the splitting field, trivialize each torus
coordinate by scalar Hilbert 90. -/
theorem exists_torusLattice_coboundary_on_subfield (basis : Basis ι ℤ Λ) (hEL : E ≤ L)
    (c : (L ≃ₐ[F] L) → TorusLatticePoint Λ L)
    (hc : IsTorusLatticeCocycle (ρ.comp (restrictFiniteGalois hEL)) c) :
    letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
    letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
    ∃ b : TorusLatticePoint Λ L, ∀ σ : L ≃ₐ[E] L, c (σ.restrictScalars F) *
      torusLatticeAct (ρ.comp (restrictFiniteGalois hEL)) (σ.restrictScalars F) b = b := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module E L := Algebra.toModule
  letI : FiniteDimensional E L := FiniteDimensional.right F E L
  let f := latticeCharacterCoords (B := Lˣ) basis
  let u (i : ι) (σ : L ≃ₐ[E] L) := f (c (σ.restrictScalars F)) i
  have hUnit (i : ι) (σ τ : L ≃ₐ[E] L) :
      u i (σ * τ) = u i σ * Units.map σ.toRingEquiv.toMonoidHom (u i τ) := by
    have h := congrFun (congrArg f (hc (σ.restrictScalars F) (τ.restrictScalars F))) i
    change u i (σ * τ) = u i σ *
      f (torusLatticeAct (ρ.comp (restrictFiniteGalois hEL))
        (σ.restrictScalars F) (c (τ.restrictScalars F))) i at h
    rw [torusCoords_act_over_subfield basis hEL (c (τ.restrictScalars F)) i σ] at h
    exact h
  choose a ha using fun i => unitHilbert90 (u i) (hUnit i)
  let b := f.symm (fun i => (a i)⁻¹)
  refine ⟨b, fun σ => f.injective (funext fun i => ?_)⟩
  change u i σ * f (torusLatticeAct (ρ.comp (restrictFiniteGalois hEL))
    (σ.restrictScalars F) b) i = f b i
  rw [torusCoords_act_over_subfield basis hEL b i σ,
    congrFun (f.apply_symm_apply (fun i => (a i)⁻¹)) i]
  have h := ha i σ
  change Units.map σ.toRingEquiv.toMonoidHom (a i) / a i = u i σ at h
  rw [← h, map_inv, div_mul_eq_mul_div, mul_inv_cancel, one_div]

end Inflation

end WideE
