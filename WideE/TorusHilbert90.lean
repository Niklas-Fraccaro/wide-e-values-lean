import WideE.TorusLatticeCocycle
import WideE.C1Extension

/-!
# Hilbert 90 for finite Galois actions on torus lattices

The p-group case first adjoins roots of each cocycle value. The defects of
multiplicativity are torsion points of the original torus. A second finite
Galois enlargement makes those defects a coboundary.
-/

noncomputable section

namespace WideE

open IntermediateField

section PGroup

variable {F Ω Λ ι : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [IsAlgClosed Ω] [IsGalois F Ω]
variable [AddCommGroup Λ] [Finite ι]

set_option synthInstance.maxHeartbeats 180000 in
set_option maxHeartbeats 1500000 in
/-- A torus split by a finite Galois p-extension over a C₁ field containing
all primitive roots of unity has trivial first Galois cohomology. -/
theorem torusLatticeHilbert90_of_isPGroup
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis ι ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p (E ≃ₐ[F] E))
    (ρ : (E ≃ₐ[F] E) →* MulAut (Multiplicative Λ))
    (c : (E ≃ₐ[F] E) → TorusLatticePoint Λ E) (hc : IsTorusLatticeCocycle ρ c) :
    IsTorusLatticeCoboundary ρ c := by
  classical
  letI : CommGroup (TorusLatticePoint Λ E) := MonoidHom.instCommGroup
  let n := Nat.card (E ≃ₐ[F] E)
  have hn : 0 < n := Nat.card_pos
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  obtain ⟨L, hEL, v, hv⟩ := exists_finiteGalois_torusLattice_roots basis E hn c
  letI : CommGroup (TorusLatticePoint Λ L) := MonoidHom.instCommGroup
  let r₁ := restrictFiniteGalois hEL
  let i₁ := extendTorusLatticePoint (Λ := Λ) hEL
  let ρ₁ := ρ.comp r₁
  letI := torusLatticeAction ρ₁
  let c₁ := inflateTorusLatticeCocycle hEL c
  have hc₁ : IsTorusLatticeCocycle ρ₁ c₁ := hc.inflate hEL
  let b (σ : L ≃ₐ[F] L) : TorusLatticePoint Λ L := if σ = 1 then 1 else v (r₁ σ)
  have hbOne : b 1 = 1 := if_pos rfl
  have hbPow (σ : L ≃ₐ[F] L) : b σ ^ n = c₁ σ := by
    by_cases h : σ = 1
    · subst σ
      rw [hbOne, hc₁.one]
      exact one_pow n
    · exact (congrArg (fun x : TorusLatticePoint Λ L => x ^ n) (if_neg h)).trans (hv (r₁ σ))
  let d : NormalizedMulTwoCocycle (MonoidHom.id (L ≃ₐ[F] L)) (TorusLatticePoint Λ L) :=
    NormalizedMulTwoCocycle.ofCoboundary b hbOne
  have hdPow (σ τ : L ≃ₐ[F] L) : d.value σ τ ^ n = 1 := by
    change (b σ * torusLatticeAct ρ₁ σ (b τ) / b (σ * τ)) ^ n = 1
    rw [div_pow (b σ * torusLatticeAct ρ₁ σ (b τ)) (b (σ * τ)) n, mul_pow]
    have hAct := smul_pow' σ (b τ) n
    change torusLatticeAct ρ₁ σ (b τ ^ n) =
      torusLatticeAct ρ₁ σ (b τ) ^ n at hAct
    rw [← hAct, hbPow, hbPow, hbPow, ← hc₁ σ τ, div_self']
  let M := torusLatticeTorsion Λ E n
  have hζE : (primitiveRoots n E).Nonempty := primitiveRoots_nonempty_of_algebra hn (hRoots n hn)
  choose d₀ hd₀ using fun σ τ => exists_torusLatticeTorsion_of_extension
    basis hEL hζE (d.value σ τ) (hdPow σ τ)
  let iT : M →* TorusLatticePoint Λ L := i₁.comp (torusLatticeTorsion Λ E n).subtype
  have hInjective : Function.Injective iT :=
    (extendTorusLatticePoint_injective hEL).comp Subtype.coe_injective
  letI : Finite M := finite_torusLatticeTorsion basis
  letI : MulDistribMulAction (E ≃ₐ[F] E) M := torusLatticeTorsionAction ρ n
  have hT (σ : L ≃ₐ[F] L) (x : M) : iT (r₁ σ • x) = torusLatticeAct ρ₁ σ (iT x) :=
    extendTorusLatticePoint_smul hEL ρ σ (x : TorusLatticePoint Λ E)
  have hVal (σ τ : L ≃ₐ[F] L) : iT (d₀ σ τ) = d.value σ τ := hd₀ σ τ
  let dE : NormalizedMulTwoCocycle r₁ M :=
    { value := d₀
      one_left := fun σ => hInjective (by rw [hVal, map_one, d.one_left])
      one_right := fun σ => hInjective (by rw [hVal, map_one, d.one_right])
      cocycle := fun σ τ υ => hInjective (by
        simp only [map_mul, hT, hVal]
        exact d.cocycle σ τ υ) }
  have hM : IsPGroup p M := by
    change IsPGroup p (torusLatticeTorsion Λ E n)
    rw [show n = p ^ j from hj]
    exact isPGroup_torusLatticeTorsion p j
  obtain ⟨N, hLN, a, ha⟩ := exists_pGroup_coboundary_after_finiteGalois hF
    (hRoots p (Fact.out : p.Prime).pos) hP hM L r₁ dE
  letI : CommGroup (TorusLatticePoint Λ N) := MonoidHom.instCommGroup
  let hEN := hEL.trans hLN
  let r₂ := restrictFiniteGalois hLN
  let r₃ := restrictFiniteGalois hEN
  let i₂ := extendTorusLatticePoint (Λ := Λ) hLN
  let i₃ := extendTorusLatticePoint (Λ := Λ) hEN
  let ρ₃ := ρ.comp r₃
  letI := torusLatticeAction ρ₃
  have hRes (σ : N ≃ₐ[F] N) : r₁ (r₂ σ) = r₃ σ :=
    DFunLike.congr_fun (restrictFiniteGalois_comp hEL hLN) σ
  have hActionComp : ρ₁.comp r₂ = ρ₃ := MonoidHom.ext fun σ => congrArg ρ (hRes σ)
  have hAct₂ (σ : N ≃ₐ[F] N) (x : TorusLatticePoint Λ L) :
      i₂ (torusLatticeAct ρ₁ (r₂ σ) x) = torusLatticeAct ρ₃ σ (i₂ x) := by
    have h := extendTorusLatticePoint_smul hLN ρ₁ σ x
    change i₂ (torusLatticeAct ρ₁ (r₂ σ) x) = torusLatticeAct (ρ₁.comp r₂) σ (i₂ x) at h
    rw [hActionComp] at h
    exact h
  have hAct₃ (σ : N ≃ₐ[F] N) (x : TorusLatticePoint Λ E) :
      i₃ (torusLatticeAct ρ (r₃ σ) x) = torusLatticeAct ρ₃ σ (i₃ x) :=
    extendTorusLatticePoint_smul hEN ρ σ x
  let bN (σ : N ≃ₐ[F] N) := i₂ (b (r₂ σ))
  let aN (σ : N ≃ₐ[F] N) := i₃ (a σ : TorusLatticePoint Λ E)
  have hCob₁ (σ τ : N ≃ₐ[F] N) :
      i₂ (d.value (r₂ σ) (r₂ τ)) = bN σ * torusLatticeAct ρ₃ σ (bN τ) / bN (σ * τ) := by
    change i₂ (b (r₂ σ) * torusLatticeAct ρ₁ (r₂ σ) (b (r₂ τ)) / b (r₂ σ * r₂ τ)) =
      bN σ * torusLatticeAct ρ₃ σ (bN τ) / i₂ (b (r₂ (σ * τ)))
    rw [map_div, map_mul, hAct₂, map_mul r₂]
  have hCob₂ (σ τ : N ≃ₐ[F] N) :
      i₃ (d₀ (r₂ σ) (r₂ τ) : TorusLatticePoint Λ E) =
        aN σ * torusLatticeAct ρ₃ σ (aN τ) / aN (σ * τ) := by
    have h := congrArg i₃ (congrArg Subtype.val (ha σ τ))
    change i₃ (d₀ (r₂ σ) (r₂ τ) : TorusLatticePoint Λ E) =
      i₃ ((a σ : TorusLatticePoint Λ E) * torusLatticeAct ρ (r₁ (r₂ σ)) (a τ) / a (σ * τ)) at h
    rw [hRes, map_div, map_mul, hAct₃] at h
    exact h
  have hCob (σ τ : N ≃ₐ[F] N) : bN σ * torusLatticeAct ρ₃ σ (bN τ) / bN (σ * τ) =
      aN σ * torusLatticeAct ρ₃ σ (aN τ) / aN (σ * τ) := by
    rw [← hCob₁, ← hCob₂, ← hd₀]
    exact extendTorusLatticePoint_trans hEL hLN _
  let z (σ : N ≃ₐ[F] N) := bN σ / aN σ
  have hz : IsTorusLatticeCocycle ρ₃ z := by
    intro σ τ
    have h : z σ * torusLatticeAct ρ₃ σ (z τ) / z (σ * τ) = 1 := by
      change (bN σ / aN σ) * (σ • (bN τ / aN τ)) / (bN (σ * τ) / aN (σ * τ)) = 1
      rw [smul_div', div_mul_div_comm, div_div_div_comm]
      exact (div_eq_one.mpr (hCob σ τ))
    exact (div_eq_one.mp h).symm
  have hzPow (σ : N ≃ₐ[F] N) : z σ ^ n = inflateTorusLatticeCocycle hEN c σ := by
    have hBN : bN σ ^ n = inflateTorusLatticeCocycle hEN c σ := by
      change i₂ (b (r₂ σ)) ^ n = i₃ (c (r₃ σ))
      rw [← map_pow, hbPow]
      change i₂ (i₁ (c (r₁ (r₂ σ)))) = i₃ (c (r₃ σ))
      rw [hRes]
      exact extendTorusLatticePoint_trans hEL hLN _
    have hAN : aN σ ^ n = 1 := by
      change i₃ (a σ : TorusLatticePoint Λ E) ^ n = 1
      rw [← map_pow, show (a σ : TorusLatticePoint Λ E) ^ n = 1 from (a σ).property, map_one]
    change (bN σ / aN σ) ^ n = _
    rw [div_pow, hBN, hAN, div_one]
  obtain ⟨u, hu⟩ := exists_torusLattice_coboundary_on_subfield (ρ := ρ) basis hEN z hz
  obtain ⟨w, hw⟩ := exists_coboundary_pow_galois_card hEN z hz u hu
  exact IsTorusLatticeCoboundary.of_inflate basis hEN hc
    ⟨w, fun σ => hzPow σ ▸ hw σ⟩

end PGroup

section Sylow

variable {F Ω Λ ι : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [CharZero F] [IsAlgClosed Ω] [IsGalois F Ω]
variable [AddCommGroup Λ] [Finite ι]

set_option synthInstance.maxHeartbeats 180000 in
set_option maxHeartbeats 1500000 in
private theorem torusLatticeCoboundaryOnSylow
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis ι ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    {p : ℕ} [Fact p.Prime] (P : Sylow p (E ≃ₐ[F] E))
    (ρ : (E ≃ₐ[F] E) →* MulAut (Multiplicative Λ))
    (c : (E ≃ₐ[F] E) → TorusLatticePoint Λ E) (hc : IsTorusLatticeCocycle ρ c) :
    ∃ b : TorusLatticePoint Λ E, ∀ σ : (P : Subgroup (E ≃ₐ[F] E)),
      c σ * torusLatticeAct ρ σ b = b := by
  let S := IntermediateField.fixedField (P : Subgroup (E ≃ₐ[F] E))
  let incl : S →ₐ[F] Ω := (IsScalarTower.toAlgHom F E Ω).comp S.val
  letI : Algebra S Ω := incl.toRingHom.toAlgebra
  letI : IsScalarTower F S Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S E Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois S Ω := IsGalois.tower_top_of_isGalois F S Ω
  letI : CharZero S := charZero_of_injective_algebraMap (algebraMap F S).injective
  let E_S : IntermediateField S Ω :=
    E.toIntermediateField.toSubfield.toIntermediateField (fun x => (x : E).property)
  let B : FiniteGaloisIntermediateField S Ω :=
    { toIntermediateField := E_S
      finiteDimensional := (show FiniteDimensional S E from inferInstance)
      isGalois := (show IsGalois S E from inferInstance) }
  let e : (P : Subgroup (E ≃ₐ[F] E)) ≃* (B ≃ₐ[S] B) :=
    (MulEquiv.subgroupCongr (fixingSubgroup_fixedField (P : Subgroup (E ≃ₐ[F] E))).symm).trans
      S.fixingSubgroupEquiv
  let r : (B ≃ₐ[S] B) →* (E ≃ₐ[F] E) := P.toSubgroup.subtype.comp e.symm.toMonoidHom
  let ρS := ρ.comp r
  let cS (σ : B ≃ₐ[S] B) : TorusLatticePoint Λ B := c (r σ)
  have hAct (σ : B ≃ₐ[S] B) (x : TorusLatticePoint Λ B) :
      torusLatticeAct ρS σ x = torusLatticeAct ρ (r σ) x := by
    apply MonoidHom.ext
    intro a
    apply Units.ext
    rfl
  have hcS : IsTorusLatticeCocycle ρS cS := by
    intro σ τ
    have h := hc (r σ) (r τ)
    rw [← map_mul r, ← hAct σ (c (r τ))] at h
    exact h
  have hS : IsC1 S := isC1_of_isAlgebraic hF
  have hRootsS (n : ℕ) (hn : 0 < n) : (primitiveRoots n S).Nonempty :=
    primitiveRoots_nonempty_of_algebra hn (hRoots n hn)
  have hP : IsPGroup p (B ≃ₐ[S] B) := P.isPGroup'.of_equiv e
  obtain ⟨b, hb⟩ := torusLatticeHilbert90_of_isPGroup hS hRootsS basis B hP ρS cS hcS
  refine ⟨b, fun σ => ?_⟩
  have h := hb (e σ)
  change c (r (e σ)) * (torusLatticeAct ρS (e σ) b : TorusLatticePoint Λ E) = b at h
  have hr : r (e σ) = (σ : E ≃ₐ[F] E) := congrArg Subtype.val (e.symm_apply_apply σ)
  rw [hAct, hr] at h
  exact h

set_option synthInstance.maxHeartbeats 180000 in
/-- The first Galois cohomology of a finite free torus lattice is trivial over a
characteristic-zero C₁ field containing all roots of unity. -/
theorem torusLatticeHilbert90_of_isC1
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis ι ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    (ρ : (E ≃ₐ[F] E) →* MulAut (Multiplicative Λ))
    (c : (E ≃ₐ[F] E) → TorusLatticePoint Λ E) (hc : IsTorusLatticeCocycle ρ c) :
    IsTorusLatticeCoboundary ρ c := by
  classical
  letI : CommGroup (TorusLatticePoint Λ E) := MonoidHom.instCommGroup
  letI := torusLatticeAction ρ
  apply exists_coboundary_of_sylow c hc
  intro p _ _
  let P : Sylow p (E ≃ₐ[F] E) := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨b, hb⟩ := torusLatticeCoboundaryOnSylow hF hRoots basis E P ρ c hc
  exact ⟨P, b, hb⟩

end Sylow

set_option synthInstance.maxHeartbeats 180000 in
/-- The torus-lattice Hilbert 90 theorem over a rational function field with
algebraically closed constants. -/
theorem torusLatticeHilbert90_over_ratFunc
    {k Λ ι : Type*} [Field k] [CharZero k] [IsAlgClosed k] [AddCommGroup Λ] [Finite ι]
    (basis : Basis ι ℤ Λ)
    (E : FiniteGaloisIntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)))
    (ρ : (E ≃ₐ[RatFunc k] E) →* MulAut (Multiplicative Λ))
    (c : (E ≃ₐ[RatFunc k] E) → TorusLatticePoint Λ E) (hc : IsTorusLatticeCocycle ρ c) :
    IsTorusLatticeCoboundary ρ c := by
  letI : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  exact torusLatticeHilbert90_of_isC1 (ratFunc_isC1 k)
    (fun _ hn => primitiveRoots_nonempty_of_algClosed_subfield (k := k) hn) basis E ρ c hc

end WideE
