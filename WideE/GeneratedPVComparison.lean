import WideE.KummerSections
import WideE.PVSubquotients
import WideE.PVTensorOperations

/-! Normalized fundamental matrices over a common Picard–Vessiot algebra. -/

noncomputable section

open scoped WideE Matrix Kronecker

namespace WideE

open StrictEUnit

variable {K : Type*} [Field K]

local notation "R" => LaurentPolynomial K
local notation "P" => PowerSeries K

/-- The finite free systems generated in coordinates by a given Laurent system.
The splits of subobjects and quotients are taken on the underlying modules. -/
inductive GeneratedLaurentSystem {r : ℕ} (A : Matrix (Fin r) (Fin r) R) :
    {n : ℕ} → Matrix (Fin n) (Fin n) R → Prop
  | generator : GeneratedLaurentSystem A A
  | unit : GeneratedLaurentSystem A (0 : Matrix (Fin 1) (Fin 1) R)
  | sum {m n : ℕ} {B : Matrix (Fin m) (Fin m) R} {D : Matrix (Fin n) (Fin n) R} :
      GeneratedLaurentSystem A B → GeneratedLaurentSystem A D →
        GeneratedLaurentSystem A (combinedLaurentSystem B D)
  | tensor {m n : ℕ} {B : Matrix (Fin m) (Fin m) R} {D : Matrix (Fin n) (Fin n) R} :
      GeneratedLaurentSystem A B → GeneratedLaurentSystem A D →
        GeneratedLaurentSystem A (tensorLaurentSystem B D)
  | dual {m : ℕ} {B : Matrix (Fin m) (Fin m) R} :
      GeneratedLaurentSystem A B → GeneratedLaurentSystem A (dualLaurentSystem B)
  | subobject {m n : ℕ} {B : Matrix (Fin m) (Fin m) R} {D : Matrix (Fin n) (Fin n) R}
      (hB : GeneratedLaurentSystem A B) (i : Matrix (Fin m) (Fin n) R)
      (retract : Matrix (Fin n) (Fin m) R) (hSplit : retract * i = 1)
      (hHorizontal : i.map laurentDerivation = B * i - i * D) :
      GeneratedLaurentSystem A D
  | quotient {m n : ℕ} {B : Matrix (Fin m) (Fin m) R} {D : Matrix (Fin n) (Fin n) R}
      (hB : GeneratedLaurentSystem A B) (p : Matrix (Fin n) (Fin m) R)
      (sectionMatrix : Matrix (Fin m) (Fin n) R) (hSplit : p * sectionMatrix = 1)
      (hHorizontal : p.map laurentDerivation = D * p - p * B) :
      GeneratedLaurentSystem A D

local instance generatedComparisonPowerAlgebra : Algebra R P := (formalAtOne K).toRingHom.toAlgebra

variable [CharZero K]

private theorem formalFundamentalAtOneUnit_zero {m : ℕ} :
    formalFundamentalAtOneUnit (0 : Matrix (Fin m) (Fin m) R) = 1 := by
  let A : Matrix (Fin m) (Fin m) R := 0
  let U := formalFundamentalAtOneUnit A
  have hU : U.val.map (PowerSeries.derivative K) = A.map (formalAtOne K) * U.val := by
    simp only [U, formalFundamentalAtOneUnit_val, formalFundamentalMatrix_derivative]
  have hU₀ : U.val.map (PowerSeries.constantCoeff K) = 1 := by
    simp only [U, formalFundamentalAtOneUnit_val, formalFundamentalMatrix_constantCoeff]
  have hOne : (1 : Matrix (Fin m) (Fin m) P).map (PowerSeries.derivative K) =
      A.map (formalAtOne K) * 1 := by
    rw [matrix_deriv_one, Matrix.mul_one]
    exact (Matrix.map_zero (formalAtOne K) (map_zero _)).symm
  exact Units.ext (normalized_fundamental_eq U hU hOne hU₀
    (Matrix.map_one _ (map_zero _) (map_one _))).symm

section Lifts

variable {S : Type*} [CommRing S] [Algebra (LaurentPolynomial K) S]
variable (e : S →ₐ[LaurentPolynomial K] PowerSeries K)

private theorem map_sum_unit {m n : ℕ} {B : Matrix (Fin m) (Fin m) R}
    {D : Matrix (Fin n) (Fin n) R} (U : (Matrix (Fin m) (Fin m) S)ˣ)
    (V : (Matrix (Fin n) (Fin n) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit B)
    (hV : Units.map e.toRingHom.mapMatrix.toMonoidHom V = formalFundamentalAtOneUnit D) :
    Units.map e.toRingHom.mapMatrix.toMonoidHom
        (reindexMatrixUnit finSumFinEquiv (blockDiagonalMatrixUnit U V)) =
      formalFundamentalAtOneUnit (combinedLaurentSystem B D) := by
  let idx := finSumFinEquiv (m := m) (n := n)
  apply Units.ext
  apply (Matrix.reindex idx.symm idx.symm).injective
  have hU' : U.val.map e.toRingHom = (formalFundamentalAtOneUnit B).val := congrArg Units.val hU
  have hV' : V.val.map e.toRingHom = (formalFundamentalAtOneUnit D).val := congrArg Units.val hV
  change Matrix.reindex idx.symm idx.symm
      (Matrix.reindex idx idx ((Matrix.fromBlocks U.val 0 0 V.val).map e.toRingHom)) =
    Matrix.reindex idx.symm idx.symm (formalFundamentalAtOneUnit (combinedLaurentSystem B D)).val
  rw [← Matrix.reindex_symm, Equiv.symm_apply_apply, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), hU', hV']
  exact (formalFundamentalAtOneUnit_combinedSystem B D).symm

private theorem map_tensor_unit {m n : ℕ} {B : Matrix (Fin m) (Fin m) R}
    {D : Matrix (Fin n) (Fin n) R} (U : (Matrix (Fin m) (Fin m) S)ˣ)
    (V : (Matrix (Fin n) (Fin n) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit B)
    (hV : Units.map e.toRingHom.mapMatrix.toMonoidHom V = formalFundamentalAtOneUnit D) :
    Units.map e.toRingHom.mapMatrix.toMonoidHom (tensorMatrixUnit U V) =
      formalFundamentalAtOneUnit (tensorLaurentSystem B D) := by
  rw [map_tensorMatrixUnit, hU, hV]
  apply Units.ext
  exact (formalFundamentalAtOneUnit_tensorSystem B D).symm

private theorem map_dual_unit {m : ℕ} {B : Matrix (Fin m) (Fin m) R}
    (U : (Matrix (Fin m) (Fin m) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit B) :
    Units.map e.toRingHom.mapMatrix.toMonoidHom (dualMatrixUnit U) =
      formalFundamentalAtOneUnit (dualLaurentSystem B) := by
  apply Units.ext
  have hInv : Units.map e.toRingHom.mapMatrix.toMonoidHom U⁻¹ =
      (formalFundamentalAtOneUnit B)⁻¹ := by rw [map_inv, hU]
  change ((U⁻¹).val.map e.toRingHom).transpose = (formalFundamentalAtOneUnit (dualLaurentSystem B)).val
  rw [show (U⁻¹).val.map e.toRingHom = _ from congrArg Units.val hInv]
  exact (formalFundamentalAtOneUnit_dualSystem B).symm

/-- Every generated system has a normalized formal fundamental matrix over
the common algebra as soon as the generating system has one. -/
theorem exists_liftFundamentalMatrix_of_generated (he : Function.Injective e)
    {r n : ℕ} {A : Matrix (Fin r) (Fin r) R} {B : Matrix (Fin n) (Fin n) R}
    (U : (Matrix (Fin r) (Fin r) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit A)
    (hB : GeneratedLaurentSystem A B) :
    ∃ V : (Matrix (Fin n) (Fin n) S)ˣ,
      Units.map e.toRingHom.mapMatrix.toMonoidHom V = formalFundamentalAtOneUnit B := by
  induction hB with
  | generator => exact ⟨U, hU⟩
  | unit => exact ⟨1, (map_one _).trans formalFundamentalAtOneUnit_zero.symm⟩
  | sum _ _ hV hW =>
    obtain ⟨V, hV⟩ := hV
    obtain ⟨W, hW⟩ := hW
    exact ⟨_, map_sum_unit e V W hV hW⟩
  | tensor _ _ hV hW =>
    obtain ⟨V, hV⟩ := hV
    obtain ⟨W, hW⟩ := hW
    exact ⟨_, map_tensor_unit e V W hV hW⟩
  | dual _ hV =>
    obtain ⟨V, hV⟩ := hV
    exact ⟨_, map_dual_unit e V hV⟩
  | subobject _ i retract hSplit hHorizontal hV =>
    obtain ⟨V, hV⟩ := hV
    let lift := liftFundamentalMatrixOfHorizontalSubobject e he V hV i retract hSplit hHorizontal
    exact ⟨lift.val, lift.property⟩
  | quotient _ p sectionMatrix hSplit hHorizontal hV =>
    obtain ⟨V, hV⟩ := hV
    let lift := liftFundamentalMatrixOfHorizontalQuotient e he V hV p sectionMatrix hSplit hHorizontal
    exact ⟨lift.val, lift.property⟩

end Lifts

section Comparison

variable {T : Type*} [CommRing T] [Algebra K T]

/-- A natural tensor comparison in coordinates, with the prescribed specialization at one. -/
structure NormalizedLaurentComparison {r : ℕ} (A : Matrix (Fin r) (Fin r) R)
    (base : R →ₐ[K] T) (E : T →ₐ[K] K) where
  matrix : ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) R},
    GeneratedLaurentSystem A B → (Matrix (Fin n) (Fin n) T)ˣ
  specializes : ∀ {n : ℕ} {B : Matrix (Fin n) (Fin n) R}
    (hB : GeneratedLaurentSystem A B), (matrix hB).val.map E = 1
  naturality : ∀ {m n : ℕ} {B : Matrix (Fin m) (Fin m) R} {D : Matrix (Fin n) (Fin n) R}
    (hB : GeneratedLaurentSystem A B) (hD : GeneratedLaurentSystem A D)
    (F : Matrix (Fin n) (Fin m) R), F.map laurentDerivation = D * F - F * B →
      F.map base * (matrix hB).val = (matrix hD).val * (F.map (evalAtOne K)).map (algebraMap K T)
  onUnit : matrix GeneratedLaurentSystem.unit = 1
  onTensor : ∀ {m n : ℕ} {B : Matrix (Fin m) (Fin m) R} {D : Matrix (Fin n) (Fin n) R}
    (hB : GeneratedLaurentSystem A B) (hD : GeneratedLaurentSystem A D),
    matrix (GeneratedLaurentSystem.tensor hB hD) = tensorMatrixUnit (matrix hB) (matrix hD)

local instance generatedComparisonPowerTower : IsScalarTower K R P :=
  IsScalarTower.of_algebraMap_eq (fun a => ((formalAtOne K).commutes a).symm)

variable {S : Type*} [CommRing S] [Algebra (LaurentPolynomial K) S] [Algebra K S]
  [IsScalarTower K (LaurentPolynomial K) S]

/-- A section of the common coefficient algebra yields a single normalized
tensor comparison for the systems generated by the original one. -/
def normalizedLaurentComparison_of_section
    {r : ℕ} {A : Matrix (Fin r) (Fin r) R} (e : S →ₐ[R] P) (he : Function.Injective e)
    (U : (Matrix (Fin r) (Fin r) S)ˣ)
    (hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit A)
    (s : S →ₐ[K] T) (E : T →ₐ[K] K) (hE : ∀ p : R, E (s (algebraMap R S p)) = evalAtOne K p) :
    NormalizedLaurentComparison A (s.comp (IsScalarTower.toAlgHom K R S)) E := by
  let b := IsScalarTower.toAlgHom K R S
  let eK := e.restrictScalars K
  have heK : Function.Injective eK := he
  have hb : eK.comp b = formalAtOne K := by
    apply AlgHom.ext
    exact e.commutes
  have hEC : Function.LeftInverse E.toRingHom (algebraMap K T) := by
    intro a
    simpa only [AlgHom.coe_toRingHom, Algebra.id.map_eq_id, RingHom.id_apply] using E.commutes a
  let lift {n : ℕ} {B : Matrix (Fin n) (Fin n) R} (hB : GeneratedLaurentSystem A B) :=
    Classical.choose (exists_liftFundamentalMatrix_of_generated e he U hU hB)
  have lift_spec {n : ℕ} {B : Matrix (Fin n) (Fin n) R} (hB : GeneratedLaurentSystem A B) :
      Units.map e.toRingHom.mapMatrix.toMonoidHom (lift hB) = formalFundamentalAtOneUnit B :=
    Classical.choose_spec (exists_liftFundamentalMatrix_of_generated e he U hU hB)
  have lift_injective (n : ℕ) : Function.Injective (Units.map
      (e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) P).toMonoidHom) :=
    Units.map_injective (Matrix.map_injective (f := (e : S → P)) he)
  let specialize {n : ℕ} (W : (Matrix (Fin n) (Fin n) S)ˣ) :=
    Units.map s.toRingHom.mapMatrix.toMonoidHom W
  let compare {n : ℕ} {B : Matrix (Fin n) (Fin n) R} (hB : GeneratedLaurentSystem A B) :=
    normalizeMatrixAt E.toRingHom (algebraMap K T) (specialize (lift hB))
  refine ⟨fun hB => compare hB, fun hB => normalizeMatrixAt_specialize _ _ hEC _, ?_, ?_, ?_⟩
  · intro m n B D hB hD F hF
    let F' := F.map (s.comp b)
    have hLift := liftedFundamentalMatrix_naturality b eK heK hb (lift hB) (lift hD)
      (congrArg Units.val (lift_spec hB)) (congrArg Units.val (lift_spec hD)) F hF
    have h := congrArg (fun M : Matrix (Fin n) (Fin m) S => M.map s.toRingHom) hLift
    change (F.map b * (lift hB).val).map s.toRingHom =
      ((lift hD).val * (F.map (evalAtOne K)).map (algebraMap K S)).map s.toRingHom at h
    rw [Matrix.map_mul, Matrix.map_mul] at h
    have hCoeff : ((F.map (evalAtOne K)).map (algebraMap K S)).map s.toRingHom =
        (F.map (evalAtOne K)).map (algebraMap K T) :=
      Matrix.ext (fun i j => s.commutes (evalAtOne K (F i j)))
    rw [hCoeff] at h
    have hEval : F'.map E.toRingHom = F.map (evalAtOne K) := Matrix.ext (fun i j => hE (F i j))
    have hn : F' * (specialize (lift hB)).val =
        (specialize (lift hD)).val * (F'.map E.toRingHom).map (algebraMap K T) := by
      rw [hEval]
      exact h
    have hNormalized := normalizeMatrixAt_naturality E.toRingHom (algebraMap K T)
      hEC (specialize (lift hB)) (specialize (lift hD)) F' hn
    rwa [hEval] at hNormalized
  · have h : lift GeneratedLaurentSystem.unit = 1 := by
      apply lift_injective 1
      rw [lift_spec (GeneratedLaurentSystem.unit (A := A)), formalFundamentalAtOneUnit_zero, map_one]
    change compare GeneratedLaurentSystem.unit = 1
    simp [compare, h, specialize, normalizeMatrixAt]
  · intro m n B D hB hD
    have h : lift (GeneratedLaurentSystem.tensor hB hD) = tensorMatrixUnit (lift hB) (lift hD) := by
      apply lift_injective (m * n)
      exact (lift_spec (GeneratedLaurentSystem.tensor hB hD)).trans
        (map_tensor_unit e (lift hB) (lift hD) (lift_spec hB) (lift_spec hD)).symm
    change compare (GeneratedLaurentSystem.tensor hB hD) = tensorMatrixUnit (compare hB) (compare hD)
    simp only [compare, h, specialize, map_tensorMatrixUnit, normalizeMatrixAt_tensor]

end Comparison

/-- Specialization at one as a morphism of coefficient algebras. -/
def evalAtOneAlgHom (K : Type*) [CommRing K] : LaurentPolynomial K →ₐ[K] K where
  toRingHom := evalAtOne K
  commutes' a := evalAtOne_C K a

section KummerComparison

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K))

local instance generatedComparisonPVCommRing : CommRing (ordinaryPVAlgebra A) :=
  (ordinaryPVAlgebra A).toCommRing
local instance generatedComparisonPVLaurentAlgebra : Algebra (LaurentPolynomial K) (ordinaryPVAlgebra A) :=
  (ordinaryPVAlgebra A).algebra
local instance generatedComparisonPVCoefficientAlgebra : Algebra K (ordinaryPVAlgebra A) :=
  (ordinaryPVAlgebra A).algebra'

set_option maxHeartbeats 1400000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- A Kummer section specializes the common Picard–Vessiot algebra to a
normalized natural tensor comparison on its generated systems. -/
def normalizedOrdinaryKummerComparison (q : ℕ)
    (s : ordinaryPVAlgebra A →ₐ[LaurentPolynomial K] KummerExtension K q) :
    NormalizedLaurentComparison A (kummerAlgHom K q) (evalAtOneAlgHom K) := by
  let e := ordinaryPVToPowerSeries A
  have he : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    simpa only [e, ordinaryPVToPowerSeries_embed] using congrArg (powerSeriesInLaurent K) h
  let U := ordinaryPVMatrix A
  have hU : Units.map e.toRingHom.mapMatrix.toMonoidHom U = formalFundamentalAtOneUnit A := by
    apply Units.ext
    exact (ordinaryPVToPowerSeries_matrix A).trans (formalFundamentalAtOneUnit_val A).symm
  let i : KummerExtension K q →ₐ[K] R :=
    { toRingHom := (KummerExtension.toLaurent K q).toRingHom
      commutes' := fun _ => rfl }
  let φ := i.comp (s.restrictScalars K)
  have hBase (p : R) : φ (algebraMap R (ordinaryPVAlgebra A) p) = kummer K q p := by
    change KummerExtension.toLaurent K q (s (algebraMap R (ordinaryPVAlgebra A) p)) = kummer K q p
    rw [s.commutes]
    rfl
  have hφ : φ.comp (IsScalarTower.toAlgHom K R (ordinaryPVAlgebra A)) = kummerAlgHom K q :=
    AlgHom.ext hBase
  have comparison := normalizedLaurentComparison_of_section e he U hU φ (evalAtOneAlgHom K)
    (fun p => (congrArg (evalAtOne K) (hBase p)).trans (evalAtOne_kummer K q p))
  rwa [hφ] at comparison

end KummerComparison

/-- The coordinate form of the general normalized tensor comparison under the
connected-group section theorem. -/
theorem exists_normalizedLaurentComparison_of_pianzola
    (hPianzola : PianzolaForKummerAlgebras AlgebraicComplex) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial AlgebraicComplex)) :
    ∃ q : ℕ, 0 < q ∧ Nonempty
      (NormalizedLaurentComparison A (kummerAlgHom AlgebraicComplex q) (evalAtOneAlgHom AlgebraicComplex)) := by
  obtain ⟨q, hq, ⟨s⟩⟩ := widePVKummerSectionExistence_of_pianzola hPianzola r A
  exact ⟨q, hq, ⟨normalizedOrdinaryKummerComparison A q s⟩⟩

end WideE
