import WideE.CartanConjugacy
import WideE.PrincipalKostantSlice

/-! Principal slice existence and orbit uniqueness on the reductive Lie algebra. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule Module
open scoped Matrix TensorProduct

namespace WideE

variable {k H ι η : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsDomain H] [Fintype ι] [DecidableEq ι] [Fintype η]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := H)
local notation "S" => (derivedSeries k (hopfInvariantDerivations k H) 1)
local notation "Z" => center k 𝔤
local notation "Bfil" => kostantWeightFiltration (k := k)

/-- A vector in the first derived Lie ideal together with its central coordinate. -/
def derivedCenterLieVector (x : S) (z : Z) : HopfLieVector k H k := (J).symm ((x : 𝔤) + (z : 𝔤))

private theorem hopfAdjointDerivedCenter_eq_iff (bC : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (p : H →ₐ[k] k) (x y : S) (z : Z) :
    hopfAdjoint p (derivedCenterLieVector x z) = derivedCenterLieVector y z ↔
      hopfAdjoint p ((J).symm (x : 𝔤)) = (J).symm (y : 𝔤) := by
  classical
  let a := hopfAdjointInvariantDerivationsLieEquiv bC U hD he hGen p
  have hFix : a (z : 𝔤) = z := by
    rw [hopfAdjointInvariantDerivationsLieEquiv_apply, hopfAdjoint_fixes_centralDirection U hD he hGen,
      (J).apply_symm_apply]
  have h (u v : 𝔤) : hopfAdjoint p ((J).symm u) = (J).symm v ↔ a u = v := by
    rw [hopfAdjointInvariantDerivationsLieEquiv_apply]
    exact (J).injective.eq_iff.symm.trans (by rw [(J).apply_symm_apply])
  have hAdd : a ((x : 𝔤) + (z : 𝔤)) = a (x : 𝔤) + a (z : 𝔤) := a.toLieHom.map_add _ _
  rw [derivedCenterLieVector, derivedCenterLieVector, h, h, hAdd, hFix, add_left_inj]

variable [IsKilling k (derivedSeries k (hopfInvariantDerivations k H) 1)]
  [FiniteDimensional k (derivedSeries k (hopfInvariantDerivations k H) 1)]
  {C : LieSubalgebra k (derivedSeries k (hopfInvariantDerivations k H) 1)}
  [C.IsCartanSubalgebra] [IsTriangularizable k C (derivedSeries k (hopfInvariantDerivations k H) 1)]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem C

set_option maxHeartbeats 2400000 in
/-- The negative normalization and the conjugation back to the Cartan both preserve the center. -/
theorem exists_principalKostantSlice_reductive (bC : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (B : (Φ).Base) [Fintype B.support] (e : B.support → S)
    (hE : ∀ i : B.support, e i ∈ rootSpace C (((Φ).root i : C →ₗ[k] k) : C → k))
    {f : S} (ht : IsSl2Triple (principalCartanElement B : S) (∑ i, e i) f)
    (a : C) (z : Z) (ha : ∀ α : C.root, (Φ).root α a ≠ 0) :
    ∃ (s : S) (p q : H →ₐ[k] k),
      s ∈ Bfil (principalCartanElement B : S) 0 ∧ ⁅f, s⁆ = 0 ∧
      U.val.map p - 1 ∈ Bfil (hopfLieMatrix U.val ((principalCartanElement B : S) : 𝔤)) 1 ∧
      hopfAdjoint p (derivedCenterLieVector ((∑ i, e i) + (a : S)) z) =
        derivedCenterLieVector ((∑ i, e i) + s) z ∧
      hopfAdjoint q (derivedCenterLieVector ((∑ i, e i) + s) z) = derivedCenterLieVector (a : S) z := by
  classical
  letI : LieAlgebra ℚ S := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k S))
  have h := exists_principalKostantSlice_conjugate_regularCartan
    (L := S) (H := C) (A := H) U hD he hGen (S).incl B e hE ht a ha
  obtain ⟨s, p, hs, hfs, hp, hNeg, q, hPos⟩ := h
  let E : S := ∑ i, e i
  refine ⟨s, p, q, hs, hfs, hp, ?_, ?_⟩
  · exact (hopfAdjointDerivedCenter_eq_iff bC U hD he hGen p (E + a.val) (E + s) z).mpr hNeg
  · exact (hopfAdjointDerivedCenter_eq_iff bC U hD he hGen q (E + s) a.val z).mpr hPos

set_option maxHeartbeats 1600000 in
/-- Two normalizations in the same actual orbit give the same point on the principal slice. -/
theorem principalKostantSlice_reductive_eq_of_conjugate (bC : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hCompl : IsCompl S Z) (B : (Φ).Base) [Fintype B.support] (e f : B.support → S)
    (hE : ∀ i : B.support, e i ∈ rootSpace C (((Φ).root i : C →ₗ[k] k) : C → k))
    (hF : ∀ i : B.support, f i ∈ rootSpace C (-(((Φ).root i : C →ₗ[k] k) : C → k)))
    (ht : ∀ i : B.support, IsSl2Triple ((Φ).coroot i : S) (e i) (f i))
    {f₀ : S} (ht₀ : IsSl2Triple (principalCartanElement B : S) (∑ i, e i) f₀)
    (hPrincipal : ∀ p : H →ₐ[k] k,
      hopfAdjoint p ((J).symm ((principalCartanElement B : S) : 𝔤)) =
        (J).symm ((principalCartanElement B : S) : 𝔤) →
      ∀ x : C, hopfAdjoint p ((J).symm ((x : S) : 𝔤)) = (J).symm ((x : S) : 𝔤))
    (a a' : C) (za za' zs zs' : Z) (s s' : S)
    (ha : ∀ α : C.root, (Φ).root α a ≠ 0) (ha' : ∀ α : C.root, (Φ).root α a' ≠ 0)
    (hs : s ∈ Bfil (principalCartanElement B : S) 0) (hs' : s' ∈ Bfil (principalCartanElement B : S) 0)
    (hf : ⁅f₀, s⁆ = 0) (hf' : ⁅f₀, s'⁆ = 0)
    (p p' q q' g : H →ₐ[k] k)
    (hp : U.val.map p - 1 ∈ Bfil (hopfLieMatrix U.val ((principalCartanElement B : S) : 𝔤)) 1)
    (hp' : U.val.map p' - 1 ∈ Bfil (hopfLieMatrix U.val ((principalCartanElement B : S) : 𝔤)) 1)
    (hNeg : hopfAdjoint p (derivedCenterLieVector ((∑ i, e i) + (a : S)) za) =
      derivedCenterLieVector ((∑ i, e i) + s) zs)
    (hNeg' : hopfAdjoint p' (derivedCenterLieVector ((∑ i, e i) + (a' : S)) za') =
      derivedCenterLieVector ((∑ i, e i) + s') zs')
    (hPos : hopfAdjoint q (derivedCenterLieVector ((∑ i, e i) + s) zs) = derivedCenterLieVector (a : S) za)
    (hPos' : hopfAdjoint q' (derivedCenterLieVector ((∑ i, e i) + s') zs') = derivedCenterLieVector (a' : S) za')
    (hConj : hopfAdjoint g (derivedCenterLieVector ((∑ i, e i) + s) zs) =
      derivedCenterLieVector ((∑ i, e i) + s') zs') :
    s = s' ∧ zs = zs' := by
  classical
  letI : LieAlgebra ℚ S := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k S))
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  let E : S := ∑ i, e i
  have hCenter (r : H →ₐ[k] k) (x y : S) (z z' : Z)
      (h : hopfAdjoint r (derivedCenterLieVector x z) = derivedCenterLieVector y z') : z = z' := by
    let A := hopfAdjointInvariantDerivationsLieEquiv bC U hD he hGen r
    let a := lieEquivOnDerived A
    have hFix : A (z : 𝔤) = z := by
      rw [hopfAdjointInvariantDerivationsLieEquiv_apply, hopfAdjoint_fixes_centralDirection U hD he hGen,
        (J).apply_symm_apply]
    have hTot : A ((x : 𝔤) + (z : 𝔤)) = (y : 𝔤) + (z' : 𝔤) := by
      rw [hopfAdjointInvariantDerivationsLieEquiv_apply]
      change (J) (hopfAdjoint r (derivedCenterLieVector x z)) = _
      rw [h, derivedCenterLieVector, (J).apply_symm_apply]
    have hAdd : A ((x : 𝔤) + (z : 𝔤)) = A (x : 𝔤) + A (z : 𝔤) := A.toLieHom.map_add _ _
    rw [hAdd, hFix, ← lieEquivOnDerived_apply_val] at hTot
    have hDiff : ((a x : S) : 𝔤) - (y : 𝔤) = (z' : 𝔤) - (z : 𝔤) := by
      rw [sub_eq_sub_iff_add_eq_add]
      simpa only [add_comm (z' : 𝔤)] using hTot
    have hMem : (z' : 𝔤) - (z : 𝔤) ∈ S ⊓ Z := by
      refine ⟨?_, (Z).toSubmodule.sub_mem z'.property z.property⟩
      rw [← hDiff]
      exact (S).toSubmodule.sub_mem (a x).property y.property
    rw [hCompl.inf_eq_bot, LieSubmodule.mem_bot] at hMem
    exact Subtype.ext (sub_eq_zero.mp hMem).symm
  have hz := hCenter p (E + (a : S)) (E + s) za zs hNeg
  have hz' := hCenter p' (E + (a' : S)) (E + s') za' zs' hNeg'
  have hzSlice := hCenter g (E + s) (E + s') zs zs' hConj
  have hC : hopfAdjoint ((q' * g) * q⁻¹) (derivedCenterLieVector (a : S) za) =
      derivedCenterLieVector (a' : S) za' := by
    rw [← hPos, ← hopfAdjoint_mul bC, mul_assoc, inv_mul_cancel, mul_one, hopfAdjoint_mul bC, hConj, hPos']
  obtain ⟨_, w, hw, hW⟩ := exists_cartanCoreflection_of_regular_conjugate (C := C) bC U hD he hGen hCompl
    B e f hE hF ht hPrincipal a a' za za' ha ha' _ hC
  rw [← hz] at hNeg
  rw [← hz'] at hNeg'
  have hN := (hopfAdjointDerivedCenter_eq_iff bC U hD he hGen p _ _ za).mp hNeg
  have hN' := (hopfAdjointDerivedCenter_eq_iff bC U hD he hGen p' _ _ za').mp hNeg'
  rw [← hW] at hN'
  refine ⟨?_, hzSlice⟩
  exact principalKostantSlice_eq_of_coreflectionOrbit (H := C) U hD he hGen (S).incl B e f hE hF ht
    Subtype.val_injective ht₀ w hw a s s' hs hs' hf hf' p p' hp hp' hN hN'

end WideE
