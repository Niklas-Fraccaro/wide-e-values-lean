import WideE.CartanToricLocus
import WideE.DiagonalTangentCocycle
import WideE.PrincipalSliceCoordinates
import WideE.NormalizedCartanDescent
import Mathlib.Algebra.Lie.CartanExists

/-! Galois cocycles for a reductive quotient over the rational function field. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule Module
open scoped Matrix TensorProduct

namespace WideE

section NontrivialDerived

universe u

variable {k Ω : Type u} {H ι : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω] [CommRing H] [HopfAlgebra k H] [IsDomain H]
  [Algebra.FiniteType k H] [Fintype ι] [DecidableEq ι]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "𝔰" => (derivedSeries k (hopfInvariantDerivations k H) 1)
local notation "𝔷" => (center k (hopfInvariantDerivations k H))

set_option maxHeartbeats 3600000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- The nonzero semisimple ideal supplies the principal triple for the normalized slice. -/
private theorem isHopfPointCoboundary_of_nontrivial_derivedLie
    [Nontrivial (derivedSeries k (hopfInvariantDerivations k H) 1)]
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hK : IsKilling k 𝔰) (hCompl : IsCompl 𝔰 𝔷)
    (hNil : ∀ D ∈ 𝔷, IsNilpotent (hopfLieMatrix U.val D) → D = 0)
    (E : FiniteGaloisIntermediateField (RatFunc k) Ω)
    (c : (E ≃ₐ[RatFunc k] E) → H →ₐ[k] E) (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  classical
  letI : IsKilling k 𝔰 := hK
  letI : FiniteDimensional k (HopfCotangent k H) := hopfCotangent_finiteDimensional k H
  let J := hopfLieVectorInvariantDerivations (k := k) (H := H)
  letI : FiniteDimensional k 𝔤 := FiniteDimensional.of_surjective J.toLinearMap J.surjective
  letI : FiniteDimensional k 𝔰 := FiniteDimensional.of_injective (𝔰).toSubmodule.subtype Subtype.val_injective
  letI : FiniteDimensional k 𝔷 := FiniteDimensional.of_injective (𝔷).toSubmodule.subtype Subtype.val_injective
  let b := finBasis k (HopfCotangent k H)
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel (K := k) (L := 𝔰)
  let C := LieSubalgebra.engel k x
  letI : C.IsCartanSubalgebra := hx
  letI : FiniteDimensional k C := FiniteDimensional.of_injective C.toSubmodule.subtype Subtype.val_injective
  letI : IsTriangularizable k C 𝔰 := inferInstance
  let cB := finBasis k (C × 𝔷)
  let Φ := LieAlgebra.IsKilling.rootSystem C
  obtain ⟨B⟩ := rootSystem_nonempty_base Φ
  letI : Fintype B.support := Fintype.ofFinite _
  letI : Nonempty B.support := principalRootBase_nonempty_support B
  obtain ⟨e, f, hE, hF, ht, ht₀⟩ := exists_principalSl2Triple_of_rootBase B
  let z := principalCartanElement B
  have hz (α : C.root) : (Φ).root α z ≠ 0 := by
    obtain ⟨m, hm, h⟩ := principalCartanElement_root_height B α
    rw [h]
    exact Int.cast_ne_zero.mpr (mul_ne_zero (by decide) hm)
  obtain ⟨l, m, P, d, π, hSurj, hπ, hLift, n, ⟨basis⟩⟩ :=
    exists_diagonalTorus_of_reductiveCartan U hD he hGen hNil 𝔰 hCompl C
  let T := diagonalWeightAlgebra k d
  let Λ := diagonalCharacterLattice d
  letI : UniqueSums Λ := (basis.equivFun.toAddEquiv.uniqueSums_iff).mpr
    (inferInstance : UniqueSums (Fin n → ℤ))
  letI : IsDomain T := MonoidAlgebra.instIsDomainOfUniqueProds
  let V := conjugateMatrixUnit P U
  obtain ⟨hDV, heV⟩ := conjugateMatrixUnit_hopf P U hD he
  have hGenV := conjugateMatrixUnit_generating P U hGen
  have hπV (i j : ι) (hij : i ≠ j) : π (V.val i j) = 0 := (hπ i j).trans (if_neg hij)
  obtain ⟨hPrincipal, d₀, hd₀, hRegular, hTorus⟩ :=
    exists_cartanToricLocus b V hDV heV hGenV hCompl cB z hz ht₀ π hSurj hπV hLift
  obtain ⟨r, s, e₀, w, N, hNormalize, hUnique⟩ :=
    exists_ground_principalSliceNormalization b V hDV heV hGenV hCompl B e f hE hF ht ht₀
      hPrincipal cB d₀ hRegular
  obtain ⟨p, hp, hOpen⟩ :=
    exists_reductiveCartan_principal_open_avoiding V hDV heV hGenV b hCompl cB z hz d₀ hd₀
  let v (i : Fin (finrank k (C × 𝔷))) := cartanCenterLieEmbedding C (cB i)
  exact isHopfPointCoboundary_of_normalizedCartanSlice (Λ := Λ) b V hDV heV hGenV e₀ v w N d₀
    hNormalize hUnique p hp (hOpen Ω) basis (hTorus Ω) E c hc

end NontrivialDerived

local notation "k₀" => AlgebraicComplex
local notation "F₀" => RatFunc AlgebraicComplex
local notation "Ω₀" => AlgebraicClosure (RatFunc AlgebraicComplex)

variable {H : Type} {ι : Type*} [CommRing H] [HopfAlgebra k₀ H] [IsDomain H]
  [Algebra.FiniteType k₀ H] [Fintype ι] [DecidableEq ι]

attribute [local instance] hopfScalarExtension

local notation "𝔤" => hopfInvariantDerivations k₀ H
local notation "𝔰" => (derivedSeries k₀ (hopfInvariantDerivations k₀ H) 1)
local notation "𝔷" => (center k₀ (hopfInvariantDerivations k₀ H))

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- Finite Galois cocycles of the given reductive group are coboundaries over `K(t)`. -/
theorem isHopfPointCoboundary_of_reductiveLie (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k₀) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k₀] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k₀) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k₀ (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hK : IsKilling k₀ 𝔰) (hCompl : IsCompl 𝔰 𝔷)
    (hCenter : ∀ D ∈ 𝔷, ∃ a : ι → k₀, hopfLieMatrix U.val D = Matrix.diagonal a)
    (hNil : ∀ D ∈ 𝔷, IsNilpotent (hopfLieMatrix U.val D) → D = 0)
    (E : FiniteGaloisIntermediateField F₀ Ω₀) (c : (E ≃ₐ[F₀] E) → H →ₐ[k₀] E)
    (hc : IsHopfPointCocycle c) : IsHopfPointCoboundary c := by
  classical
  letI : IsAlgClosed k₀ := IsAlgClosure.isAlgClosed ℚ
  letI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap k₀ F₀).injective
  by_cases h₀ : Subsingleton 𝔰
  · have hS : 𝔰 = ⊥ := LieSubmodule.toSubmodule_injective
      (Submodule.subsingleton_iff_eq_bot.mp h₀)
    have hZ : 𝔷 = ⊤ := by simpa only [hS, bot_sup_eq] using hCompl.sup_eq_top
    exact isHopfPointCoboundary_of_diagonal_tangents U hD he hGen
      (fun D => hCenter D (hZ.symm ▸ LieSubmodule.mem_top D)) E c hc
  letI : Nontrivial 𝔰 := not_subsingleton_iff_nontrivial.mp h₀
  exact isHopfPointCoboundary_of_nontrivial_derivedLie U hD he hGen hK hCompl hNil E c hc

end WideE
