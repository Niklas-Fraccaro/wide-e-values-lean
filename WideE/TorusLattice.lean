import WideE.FinitePModuleCocycle
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Points of a torus in character lattice coordinates

With a finite free character lattice `Λ`, a point over a splitting field
takes each character to a unit. The Galois action combines conjugation
of units with the inverse action on characters.
-/

noncomputable section

namespace WideE

/-- Over a splitting field, a point of the torus is a unit-valued character of its lattice. -/
abbrev TorusLatticePoint (Λ K : Type*) [AddCommGroup Λ] [Field K] :=
  Multiplicative Λ →* Kˣ

section Coordinates

variable {Λ ι B C : Type*} [AddCommGroup Λ] [CommGroup B] [CommGroup C]

/-- Evaluation on a free abelian basis identifies the characters with coordinates. -/
def latticeCharacterCoords (basis : Basis ι ℤ Λ) :
    (Multiplicative Λ →* B) ≃* (ι → B) where
  toFun f i := f (Multiplicative.ofAdd (basis i))
  invFun u := (basis.constr ℤ (fun i => Additive.ofMul (u i))).toAddMonoidHom.toMultiplicative''
  left_inv f := by
    apply MonoidHom.toAdditive''.injective
    apply AddMonoidHom.toIntLinearMap_injective
    apply basis.ext
    intro i
    change (basis.constr ℤ (fun i => Additive.ofMul (f (Multiplicative.ofAdd (basis i)))))
      (basis i) = Additive.ofMul (f (Multiplicative.ofAdd (basis i)))
    exact Basis.constr_basis (b := basis) (S := ℤ) _ i
  right_inv u := by
    funext i
    change Additive.toMul ((basis.constr ℤ (fun i => Additive.ofMul (u i))) (basis i)) = u i
    rw [Basis.constr_basis]
    rfl
  map_mul' _ _ := rfl

/-- Postcomposition of characters with a homomorphism of coefficient groups. -/
def latticeCharacterMap (f : B →* C) :
    (Multiplicative Λ →* B) →* (Multiplicative Λ →* C) where
  toFun := f.comp
  map_one' := MonoidHom.ext fun _ => f.map_one
  map_mul' p q := MonoidHom.ext fun x => f.map_mul (p x) (q x)

theorem latticeCharacterMap_injective (f : B →* C) (hf : Function.Injective f) :
    Function.Injective (latticeCharacterMap (Λ := Λ) f) :=
  fun _ _ h => MonoidHom.ext fun x => hf (DFunLike.congr_fun h x)

end Coordinates

section Action

variable {F K Λ : Type*} [Field F] [Field K] [Algebra F K] [AddCommGroup Λ]

/-- The semilinear action on torus points, with the inverse action on characters. -/
def torusLatticeAction (ρ : (K ≃ₐ[F] K) →* MulAut (Multiplicative Λ)) :
    MulDistribMulAction (K ≃ₐ[F] K) (TorusLatticePoint Λ K) where
  smul σ f := (Units.map σ.toRingEquiv.toMonoidHom).comp (f.comp ((ρ σ)⁻¹).toMonoidHom)
  one_smul f := by
    apply MonoidHom.ext
    intro x
    change Units.map (1 : K ≃ₐ[F] K).toRingEquiv.toMonoidHom (f (((ρ 1)⁻¹) x)) = f x
    rw [map_one ρ, inv_one]
    apply Units.ext
    rfl
  mul_smul σ τ f := by
    apply MonoidHom.ext
    intro x
    change Units.map (σ * τ).toRingEquiv.toMonoidHom (f (((ρ (σ * τ))⁻¹) x)) =
      Units.map σ.toRingEquiv.toMonoidHom
        (Units.map τ.toRingEquiv.toMonoidHom (f (((ρ τ)⁻¹) (((ρ σ)⁻¹) x))))
    rw [map_mul ρ, mul_inv_rev]
    apply Units.ext
    rfl
  smul_one σ := MonoidHom.ext fun _ => (Units.map σ.toRingEquiv.toMonoidHom).map_one
  smul_mul σ f g := MonoidHom.ext fun x =>
    (Units.map σ.toRingEquiv.toMonoidHom).map_mul (f (((ρ σ)⁻¹) x)) (g (((ρ σ)⁻¹) x))

end Action

section Extension

variable {F Ω Λ : Type*} [Field F] [Field Ω] [Algebra F Ω] [AddCommGroup Λ]
variable {E L N : FiniteGaloisIntermediateField F Ω}

/-- Extending a torus point along nested splitting fields. -/
def extendTorusLatticePoint (hEL : E ≤ L) : TorusLatticePoint Λ E →* TorusLatticePoint Λ L :=
  latticeCharacterMap (Units.map (IntermediateField.inclusion hEL).toRingHom.toMonoidHom)

theorem extendTorusLatticePoint_injective (hEL : E ≤ L) :
    Function.Injective (extendTorusLatticePoint (Λ := Λ) hEL) :=
  latticeCharacterMap_injective _ (Units.map_injective (IntermediateField.inclusion hEL).injective)

theorem extendTorusLatticePoint_trans (hEL : E ≤ L) (hLN : L ≤ N) (f : TorusLatticePoint Λ E) :
    extendTorusLatticePoint hLN (extendTorusLatticePoint hEL f) =
      extendTorusLatticePoint (hEL.trans hLN) f :=
  MonoidHom.ext fun _ => Units.ext rfl

/-- Extending point coordinates is compatible with Galois restriction. -/
theorem extendTorusLatticePoint_smul
    (hEL : E ≤ L) (ρ : (E ≃ₐ[F] E) →* MulAut (Multiplicative Λ))
    (σ : L ≃ₐ[F] L) (x : TorusLatticePoint Λ E) :
    letI := torusLatticeAction ρ
    let smulE := fun r : E ≃ₐ[F] E => SMul.smul r x
    letI := torusLatticeAction (ρ.comp (restrictFiniteGalois hEL))
    extendTorusLatticePoint hEL (smulE (restrictFiniteGalois hEL σ)) =
      σ • extendTorusLatticePoint hEL x := by
  letI : Algebra E L := (IntermediateField.inclusion hEL).toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' rfl
  apply MonoidHom.ext
  intro a
  apply Units.ext
  exact σ.restrictNormal_commutes E (x (((ρ (restrictFiniteGalois hEL σ))⁻¹) a) : E)

end Extension

section Roots

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Primitive roots in a subfield remain primitive roots in a field extension. -/
theorem primitiveRoots_nonempty_of_algebra {n : ℕ} (hn : 0 < n)
    (h : (primitiveRoots n k).Nonempty) : (primitiveRoots n K).Nonempty := by
  obtain ⟨u, hu⟩ := h
  exact ⟨algebraMap k K u, (mem_primitiveRoots hn).mpr
    (((mem_primitiveRoots hn).mp hu).map_of_injective (algebraMap k K).injective)⟩

/-- A characteristic-zero algebraically closed subfield supplies all primitive roots. -/
theorem primitiveRoots_nonempty_of_algClosed_subfield [CharZero k] [IsAlgClosed k]
    {n : ℕ} (hn : 0 < n) : (primitiveRoots n K).Nonempty := by
  letI : NeZero (n : k) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  exact primitiveRoots_nonempty_of_algebra hn ⟨u, (mem_primitiveRoots hn).mpr hu⟩

end Roots

section Torsion

variable {F K Λ ι : Type*} [Field F] [Field K] [Algebra F K] [AddCommGroup Λ]

/-- The subgroup killed by the n-th power map. -/
abbrev torusLatticeTorsion (Λ K : Type*) [AddCommGroup Λ] [Field K] (n : ℕ) :
    Subgroup (TorusLatticePoint Λ K) :=
  (powMonoidHom n).ker

/-- The Galois action preserves the subgroup of n-torsion points. -/
def torusLatticeTorsionAction (ρ : (K ≃ₐ[F] K) →* MulAut (Multiplicative Λ)) (n : ℕ) :
    MulDistribMulAction (K ≃ₐ[F] K) (torusLatticeTorsion Λ K n) := by
  letI := torusLatticeAction ρ
  have hStable (σ : K ≃ₐ[F] K) (f : torusLatticeTorsion Λ K n) :
      σ • (f : TorusLatticePoint Λ K) ∈ torusLatticeTorsion Λ K n := by
    change (σ • (f : TorusLatticePoint Λ K)) ^ n = 1
    rw [← smul_pow', show (f : TorusLatticePoint Λ K) ^ n = 1 from f.property]
    exact (torusLatticeAction ρ).smul_one σ
  exact
    { smul := fun σ f => ⟨σ • (f : TorusLatticePoint Λ K), hStable σ f⟩
      one_smul := fun f => Subtype.ext (one_smul _ (f : TorusLatticePoint Λ K))
      mul_smul := fun σ τ f => Subtype.ext (mul_smul σ τ (f : TorusLatticePoint Λ K))
      smul_one := fun σ => Subtype.ext (smul_one σ)
      smul_mul := fun σ f g => Subtype.ext
        (smul_mul' σ (f : TorusLatticePoint Λ K) (g : TorusLatticePoint Λ K)) }

/-- Finite-rank character lattices have finitely many n-torsion points. -/
theorem finite_torusLatticeTorsion [Finite ι] (basis : Basis ι ℤ Λ) {n : ℕ} [NeZero n] :
    Finite (torusLatticeTorsion Λ K n) := by
  let coords := latticeCharacterCoords (B := Kˣ) basis
  let f (x : torusLatticeTorsion Λ K n) (i : ι) : rootsOfUnity n K :=
    ⟨coords x i, (mem_rootsOfUnity n _).mpr (DFunLike.congr_fun
      (show (x : TorusLatticePoint Λ K) ^ n = 1 from x.property)
      (Multiplicative.ofAdd (basis i)))⟩
  refine Finite.of_injective f fun x y h => Subtype.ext (coords.injective ?_)
  exact funext fun i => congrArg Subtype.val (congrFun h i)

theorem isPGroup_torusLatticeTorsion (p r : ℕ) :
    IsPGroup p (torusLatticeTorsion Λ K (p ^ r)) :=
  fun f => ⟨r, Subtype.ext f.property⟩

end Torsion

section TorsionDescent

variable {F Ω Λ ι : Type*} [Field F] [Field Ω] [Algebra F Ω] [AddCommGroup Λ]
variable {E L : FiniteGaloisIntermediateField F Ω}

/-- All torsion coordinates already lie in the original field when it contains the
required primitive roots. -/
theorem exists_torusLatticeTorsion_of_extension (basis : Basis ι ℤ Λ)
    (hEL : E ≤ L) {n : ℕ} [NeZero n] (hζ : (primitiveRoots n E).Nonempty)
    (x : TorusLatticePoint Λ L) (hx : x ^ n = 1) :
    ∃ f : torusLatticeTorsion Λ E n, extendTorusLatticePoint hEL f = x := by
  let jAlg := IntermediateField.inclusion hEL
  let j := Units.map jAlg.toRingHom.toMonoidHom
  let ψ := rootsOfUnityEquivOfPrimitiveRoots (f := jAlg.toRingHom) jAlg.injective hζ
  let coordsE := latticeCharacterCoords (B := Eˣ) basis
  let coordsL := latticeCharacterCoords (B := Lˣ) basis
  let w (i : ι) : rootsOfUnity n E :=
    ψ.symm ⟨coordsL x i, (mem_rootsOfUnity n _).mpr
      (DFunLike.congr_fun hx (Multiplicative.ofAdd (basis i)))⟩
  let f := coordsE.symm (fun i => (w i : Eˣ))
  have hf (i : ι) : coordsE f i = (w i : Eˣ) :=
    congrFun (coordsE.apply_symm_apply _) i
  have hPow : f ^ n = 1 := by
    apply coordsE.injective
    rw [map_pow, map_one]
    funext i
    change (coordsE f i) ^ n = 1
    rw [hf]
    exact (mem_rootsOfUnity n _).mp (w i).property
  refine ⟨⟨f, hPow⟩, coordsL.injective ?_⟩
  funext i
  change j (coordsE f i) = coordsL x i
  rw [hf]
  apply Units.ext
  exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply (f := jAlg.toRingHom) jAlg.injective hζ
    ⟨coordsL x i, (mem_rootsOfUnity n _).mpr
      (DFunLike.congr_fun hx (Multiplicative.ofAdd (basis i)))⟩

end TorsionDescent

section FiniteRoots

variable {F Ω Λ ι X : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [IsAlgClosed Ω] [IsGalois F Ω] [AddCommGroup Λ]

/-- A finite family of torus points has coordinatewise n-th roots over a common finite
Galois extension of the splitting field. -/
theorem exists_finiteGalois_torusLattice_roots [Finite ι] [Finite X]
    (basis : Basis ι ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    {n : ℕ} (hn : 0 < n) (c : X → TorusLatticePoint Λ E) :
    ∃ (L : FiniteGaloisIntermediateField F Ω) (hEL : E ≤ L)
      (b : X → TorusLatticePoint Λ L), ∀ x, b x ^ n = extendTorusLatticePoint hEL (c x) := by
  classical
  let cE := latticeCharacterCoords (B := Eˣ) basis
  choose y hy using fun p : X × ι =>
    IsAlgClosed.exists_pow_nat_eq (((cE (c p.1) p.2 : Eˣ) : E) : Ω) hn
  have hFinite : (Set.range y).Finite := Set.finite_range y
  letI : Finite (Set.range y) := hFinite.to_subtype
  let D := FiniteGaloisIntermediateField.adjoin F (Set.range y)
  let L := E ⊔ D
  let hEL : E ≤ L := le_sup_left
  let hDL : D ≤ L := le_sup_right
  let w (x : X) (i : ι) : L :=
    ⟨y (x, i), hDL (FiniteGaloisIntermediateField.subset_adjoin F (Set.range y)
      (Set.mem_range_self (x, i)))⟩
  let incl := IntermediateField.inclusion hEL
  have hw (x : X) (i : ι) : w x i ^ n = incl (cE (c x) i) :=
    Subtype.ext (hy (x, i))
  have hwne (x : X) (i : ι) : w x i ≠ 0 := by
    intro h
    have hPow := hw x i
    rw [h, zero_pow hn.ne'] at hPow
    exact (cE (c x) i).ne_zero (incl.injective (hPow.symm.trans (map_zero incl).symm))
  let cL := latticeCharacterCoords (B := Lˣ) basis
  let b (x : X) := cL.symm fun i => Units.mk0 (w x i) (hwne x i)
  refine ⟨L, hEL, b, fun x => cL.injective ?_⟩
  rw [map_pow]
  funext i
  have hBi := congrFun (cL.apply_symm_apply (fun i => Units.mk0 (w x i) (hwne x i))) i
  change (cL (b x) i) ^ n = Units.map incl.toRingHom.toMonoidHom (cE (c x) i)
  rw [hBi]
  exact Units.ext (hw x i)

end FiniteRoots

end WideE
