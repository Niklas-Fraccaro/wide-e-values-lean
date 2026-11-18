import WideE.LineOrbitAction
import WideE.OrbitPullbackFlatness
import WideE.ProjectiveLineStabilizer
import WideE.ComponentFaithfulFlatness

/-!
# Identification of a line reduction with the orbit pullback over the torsor

After scalar extension to the torsor algebra, the canonical point
difference identifies the line equations with the scaled orbit equations.
The Laurent unit is uniquely determined by the line and its pivot.
-/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

set_option maxHeartbeats 1000000

open LaurentPolynomial

section Pullback

variable {k R S H A ι : Type*} [Field k] [CommRing R] [CommRing S] [CommRing H] [CommRing A]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S] [HopfAlgebra k H]
  [Algebra k A] [Algebra A S] [Algebra A (LaurentPolynomial H)]
  [IsScalarTower k A S] [IsScalarTower k A (LaurentPolynomial H)]
  [Fintype ι] [DecidableEq ι]

local notation "ιS" => (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H)
local notation "ιH" => (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H)

/-- The base change of the quotient by line equations, over the original
torsor algebra, is the pullback of the scaled orbit map. The chosen
coordinates generate the orbit coordinate algebra. -/
theorem nonempty_lineOrbitPullbackEquiv
    (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ)
    (g : (Matrix ι ι S)ˣ) (y : ι → R)
    (hg : g.val.map T.coaction.toRingHom = (U⁻¹).val.map (ιH).toRingHom * g.val.map (ιS).toRingHom)
    (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0)
    (hPrimitive : Ideal.span (Set.range (projectiveFrameVector g y)) = ⊤)
    (a : ι → A) (ha : Algebra.adjoin k (Set.range a) = ⊤)
    (hS : ∀ i, algebraMap A S (a i) = projectiveFrameVector g y i)
    (hL : ∀ i, algebraMap A (LaurentPolynomial H) (a i) = C (orbitVector U.val v i) * LaurentPolynomial.T 1) :
    Nonempty ((S ⊗[R] ProjectiveLineReduction v pivot (projectiveFrameVector g y)) ≃ₐ[S]
      S ⊗[A] LaurentPolynomial H) := by
  let w := projectiveFrameVector g y
  change ∀ j, algebraMap A S (a j) = w j at hS
  let Q := ProjectiveLineReduction v pivot w
  let π := projectiveLineQuotient (R := R) v pivot w
  let L := LaurentPolynomial H
  let D := S ⊗[R] Q
  let E := S ⊗[A] L
  letI : Algebra R E := ((algebraMap S E).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := E) fun _ => rfl
  letI : IsScalarTower k R E := IsScalarTower.of_algebraMap_eq (R := k) (S := R) (A := E) fun r => by
    rw [IsScalarTower.algebraMap_apply k S E, IsScalarTower.algebraMap_apply k R S]
    rfl
  letI : Algebra A D := ((algebraMap S D).comp (algebraMap A S)).toAlgebra
  letI : IsScalarTower A S D := IsScalarTower.of_algebraMap_eq (R := A) (S := S) (A := D) fun _ => rfl
  letI : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq (R := k) (S := A) (A := D) fun r => by
    rw [IsScalarTower.algebraMap_apply k S D, IsScalarTower.algebraMap_apply k A S]
    rfl
  let pD : S →ₐ[R] D := IsScalarTower.toAlgHom R S D
  let iD : Q →ₐ[R] D := Algebra.TensorProduct.includeRight
  let qD : S →ₐ[R] D := iD.comp π
  let hD : H →ₐ[k] D := T.pointDifference pD qD
  obtain ⟨cQ, hcQ⟩ := projectiveLineQuotient_unit_vector (R := R) v pivot w hPrimitive
  let cD : Dˣ := cQ.map iD.toRingHom.toMonoidHom
  have hQD : qD.toRingHom ∘ w = (cD : D) • (algebraMap k D ∘ v) := by
    funext j
    change iD (π (w j)) = iD (cQ : Q) * algebraMap k D (v j)
    rw [show π (w j) = (cQ : Q) * algebraMap k Q (v j) from congrFun hcQ j,
      map_mul, show iD (algebraMap k Q (v j)) = algebraMap k D (v j)
        from (iD.restrictScalars k).commutes _]
  have hWD : pD.toRingHom ∘ w =
      (cD : D) • (U.val.map hD.toRingHom *ᵥ (algebraMap k D ∘ v)) := by
    have h := T.projectiveFrameVector_eq_mulVec_actPoint U g y hg pD hD
    change pD.toRingHom ∘ w = U.val.map hD.toRingHom *ᵥ ((T.actPoint pD hD).toRingHom ∘ w) at h
    rw [show T.actPoint pD hD = qD from T.actPoint_pointDifference pD qD, hQD,
      Matrix.mulVec_smul] at h
    exact h
  let orbitD : L →ₐ[k] D := laurentOrbitPoint hD cD
  have hCD : orbitD.comp (IsScalarTower.toAlgHom k A L) = IsScalarTower.toAlgHom k A D := by
    apply AlgHom.ext_of_adjoin_eq_top ha
    rintro _ ⟨j, rfl⟩
    change orbitD (algebraMap A L (a j)) = pD (algebraMap A S (a j))
    rw [hL, hS, map_mul]
    change laurentOrbitPoint hD cD (C (orbitVector U.val v j)) *
      laurentOrbitPoint hD cD (LaurentPolynomial.T 1) = pD (w j)
    rw [laurentOrbitPoint_C, laurentOrbitPoint_T, mul_comm]
    have he := congrFun (orbitVector_map hD U.val v) j
    change hD (orbitVector U.val v j) = (U.val.map hD.toRingHom *ᵥ (algebraMap k D ∘ v)) j at he
    rw [he]
    exact (congrFun hWD j).symm
  let orbitDA : L →ₐ[A] D := ⟨orbitD.toRingHom, fun z => DFunLike.congr_fun hCD z⟩
  let forward : E →ₐ[S] D := Algebra.TensorProduct.lift (Algebra.ofId S D) orbitDA
    (fun _ _ => Commute.all _ _)
  let pE : S →ₐ[R] E := IsScalarTower.toAlgHom R S E
  let iE : L →ₐ[A] E := Algebra.TensorProduct.includeRight
  let hE : H →ₐ[k] E := (iE.restrictScalars k).comp (IsScalarTower.toAlgHom k H L)
  let uT : Lˣ := (LaurentPolynomial.isUnit_T (R := H) 1).unit
  let cE := uT.map iE.toRingHom.toMonoidHom
  have hTE : (cE : E) = iE (LaurentPolynomial.T 1) :=
    congrArg iE (LaurentPolynomial.isUnit_T (R := H) 1).unit_spec
  have hWE : pE.toRingHom ∘ w =
      (cE : E) • (U.val.map hE.toRingHom *ᵥ (algebraMap k E ∘ v)) := by
    funext j
    change algebraMap S E (w j) = (cE : E) *
      (U.val.map hE.toRingHom *ᵥ (algebraMap k E ∘ v)) j
    have hBase : algebraMap S E (w j) = iE (algebraMap A L (a j)) := by
      rw [← hS j, ← IsScalarTower.algebraMap_apply A S E, iE.commutes]
    rw [hBase, hL, map_mul, ← hTE, mul_comm]
    have he := congrFun (orbitVector_map hE U.val v) j
    exact congrArg ((cE : E) * ·) he
  let qE := T.actPoint pE hE
  let M : (Matrix ι ι E)ˣ := U.map hE.toRingHom.mapMatrix.toMonoidHom
  have hQE : qE.toRingHom ∘ w = (cE : E) • (algebraMap k E ∘ v) := by
    have h := T.actPoint_projectiveFrameVector U g y hg pE hE
    change qE.toRingHom ∘ w = M.inv *ᵥ (pE.toRingHom ∘ w) at h
    rw [h, hWE, Matrix.mulVec_smul]
    change (cE : E) • (M.inv *ᵥ (M.val *ᵥ (algebraMap k E ∘ v))) = _
    rw [Matrix.mulVec_mulVec, M.inv_val, Matrix.one_mulVec]
  obtain ⟨liftQE, hLiftQE, _⟩ := existsUnique_projectiveLinePoint v pivot hpivot w qE (cE : E) hQE
  let backward : D →ₐ[S] E := Algebra.TensorProduct.lift (Algebra.ofId S E) liftQE
    (fun _ _ => Commute.all _ _)
  have fLeft (s : S) : forward (pE s) = pD s := forward.commutes s
  have bLeft (s : S) : backward (pD s) = pE s := backward.commutes s
  have fRight (z : L) : forward (iE z) = orbitD z := by
    change Algebra.TensorProduct.lift (Algebra.ofId S D) orbitDA (fun _ _ => Commute.all _ _)
      ((1 : S) ⊗ₜ[A] z) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have bRight (z : Q) : backward (iD z) = liftQE z := by
    change Algebra.TensorProduct.lift (Algebra.ofId S E) liftQE (fun _ _ => Commute.all _ _)
      ((1 : S) ⊗ₜ[R] z) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  have fGroup : (forward.restrictScalars k).comp hE = hD := by
    apply AlgHom.ext
    intro h
    change forward (iE (C h)) = hD h
    rw [fRight]
    exact laurentOrbitPoint_C hD cD h
  have fAct : (forward.restrictScalars R).comp qE = qD := by
    change (forward.restrictScalars R).comp (T.actPoint pE hE) = qD
    rw [T.actPoint_postcompose,
      show (forward.restrictScalars R).comp pE = pD from AlgHom.ext fLeft,
      show ((forward.restrictScalars R).restrictScalars k).comp hE = hD from fGroup]
    exact T.actPoint_pointDifference pD qD
  have bAct : (backward.restrictScalars R).comp qD = qE := by
    apply AlgHom.ext
    intro s
    change backward (iD (π s)) = qE s
    rw [bRight]
    exact DFunLike.congr_fun hLiftQE s
  have bGroup : (backward.restrictScalars k).comp hD = hE := by
    apply T.actPoint_injective pE
    rw [← show (backward.restrictScalars R).comp pD = pE from AlgHom.ext bLeft]
    change T.actPoint ((backward.restrictScalars R).comp pD)
      (((backward.restrictScalars R).restrictScalars k).comp hD) = _
    rw [← T.actPoint_postcompose,
      show T.actPoint pD hD = qD from T.actPoint_pointDifference pD qD, bAct,
      show (backward.restrictScalars R).comp pD = pE from AlgHom.ext bLeft]
  have bUnit : backward (cD : D) = (cE : E) := by
    apply (IsUnit.mul_left_inj ((isUnit_iff_ne_zero.mpr hpivot).map (algebraMap k E))).mp
    calc
      backward (cD : D) * algebraMap k E (v pivot) = backward (qD (w pivot)) := by
        rw [show qD (w pivot) = (cD : D) * algebraMap k D (v pivot) from congrFun hQD pivot,
          map_mul, show backward (algebraMap k D (v pivot)) = algebraMap k E (v pivot)
            from (backward.restrictScalars k).commutes _]
      _ = qE (w pivot) := DFunLike.congr_fun bAct _
      _ = (cE : E) * algebraMap k E (v pivot) := congrFun hQE pivot
  have bLaurent : (backward.restrictScalars k).comp orbitD = iE.restrictScalars k := by
    apply laurentAlgHom_ext_C_T
    · intro h
      change backward (laurentOrbitPoint hD cD (C h)) = hE h
      rw [laurentOrbitPoint_C]
      exact DFunLike.congr_fun bGroup h
    · change backward (laurentOrbitPoint hD cD (LaurentPolynomial.T 1)) =
        iE (LaurentPolynomial.T 1)
      rw [laurentOrbitPoint_T, ← hTE, bUnit]
  refine ⟨AlgEquiv.ofAlgHom backward forward ?_ ?_⟩
  · apply Algebra.TensorProduct.ext
    · exact AlgHom.ext fun s => (backward.comp forward).commutes s
    · apply AlgHom.ext
      intro z
      change backward (forward (iE z)) = iE z
      rw [fRight]
      exact DFunLike.congr_fun bLaurent z
  · apply Algebra.TensorProduct.ext
    · exact AlgHom.ext fun s => (forward.comp backward).commutes s
    · apply AlgHom.ext
      intro z
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (projectiveLineIdeal v pivot w) z
      change forward (backward (iD (π s))) = qD s
      rw [bRight, show liftQE (π s) = qE s from DFunLike.congr_fun hLiftQE s]
      exact DFunLike.congr_fun fAct s

end Pullback

section FaithfulLine

universe u

variable {k H ι : Type u} {R S : Type*} [Field k] [IsAlgClosed k] [CommRing H] [IsDomain H]
  [CommRing R] [CommRing S] [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
  [HopfAlgebra k H] [Fintype ι] [DecidableEq ι] [Algebra.FiniteType k R]

local notation "ιS" => (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H)
local notation "ιH" => (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H)

/-- The affine line reduction associated to a closed orbit and a primitive
frame vector is faithfully flat over the original base ring. -/
theorem projectiveLineReduction_faithfullyFlat
    (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (g : (Matrix ι ι S)ˣ) (y : ι → R)
    (hg : g.val.map T.coaction.toRingHom = (U⁻¹).val.map (ιH).toRingHom * g.val.map (ιS).toRingHom)
    (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0)
    (hPrimitive : Ideal.span (Set.range (projectiveFrameVector g y)) = ⊤)
    (hCone : ∀ P ∈ orbitConeIdeal U.val v, P.eval₂ (algebraMap k S) (projectiveFrameVector g y) = 0)
    (hOrbit : ∀ x : ι → k, x ≠ 0 →
      (∀ P ∈ orbitConeIdeal U.val v, MvPolynomial.aeval x P = 0) →
      ∃ (q : H →ₐ[k] k) (c : kˣ), x = (c : k) • (U.val.map q.toRingHom *ᵥ v)) :
    Module.FaithfullyFlat R (ProjectiveLineReduction v pivot (projectiveFrameVector g y)) := by
  let Q := ProjectiveLineReduction v pivot (projectiveFrameVector g y)
  let D := OrbitConeAlgebra U.val v
  let L := LaurentPolynomial H
  let F := orbitConeMap U.val v
  let f := projectiveFramePoint (orbitConeIdeal U.val v) g y hCone
  let a := orbitConeCoordinate U.val v
  letI : Algebra D S := f.toRingHom.toAlgebra
  letI : Algebra D L := F.toRingHom.toAlgebra
  letI : IsScalarTower k D S := IsScalarTower.of_algebraMap_eq (R := k) (S := D) (A := S)
    fun x => (f.commutes x).symm
  letI : IsScalarTower k D L := IsScalarTower.of_algebraMap_eq (R := k) (S := D) (A := L)
    fun x => (F.commutes x).symm
  have hCoords (j : ι) : f (a j) = projectiveFrameVector g y j :=
    projectiveFramePoint_coordinate _ _ _ _ _
  have hPrimitive' : Ideal.span (Set.range (f ∘ a)) = ⊤ := by
    rw [show f ∘ a = projectiveFrameVector g y from funext hCoords, hPrimitive]
  letI : Algebra.FiniteType R S := T.finiteType
  letI : Algebra.FiniteType k S :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  letI : Algebra.FiniteType k H := T.group_finiteType
  letI : Module.FaithfullyFlat S (S ⊗[D] L) :=
    orbitConeMap_primitiveBaseChange_faithfullyFlat U hU v f hPrimitive' hOrbit
  let π := Ideal.Quotient.mkₐ k (orbitConeIdeal U.val v)
  have ha : Algebra.adjoin k (Set.range a) = ⊤ := by
    change Algebra.adjoin k (Set.range (π ∘ (MvPolynomial.X : ι → MvPolynomial ι k))) = ⊤
    rw [Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top π).mpr (Ideal.Quotient.mkₐ_surjective k (orbitConeIdeal U.val v))
  obtain ⟨e⟩ := nonempty_lineOrbitPullbackEquiv (A := D) T U g y hg v pivot hpivot hPrimitive a
    ha hCoords (orbitConeMap_coordinate U.val v)
  letI : Module.FaithfullyFlat S (S ⊗[R] Q) :=
    Module.FaithfullyFlat.of_linearEquiv S (S ⊗[D] L) e.toLinearEquiv
  letI := T.faithfullyFlat
  exact faithfullyFlat_of_faithfullyFlat_tensor R S Q

end FaithfulLine

end WideE
