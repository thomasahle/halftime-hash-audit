import ProvenHashes.Halftime.IntegerNH
import ProvenHashes.Halftime.MatrixFibre
import ProvenHashes.Halftime.Matrices

namespace ProvenHashes.Halftime
open scoped BigOperators Matrix
set_option maxHeartbeats 500000

/-- A matrix applied to independent scalar variables with atom bound ε has
atom bound |ker A| ε^r. No independence of output coordinates is asserted. -/
theorem matrix_atom_bound {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (A : Matrix I I ℤ) (m : ℕ) (hA : A.det ≠ 0)
    (hv : padicValNat 2 A.det.natAbs ≤ m)
    (d : I → K → ZMod (2 ^ m)) (ε : ℚ≥0)
    (hd : ∀ i t, uniformProb (fun k => d i k = t) ≤ ε) (b : I → ZMod (2 ^ m)) :
    uniformProb (fun k : I → K => (A.map (Int.castRingHom (ZMod (2 ^ m)))).mulVec
      (fun i => d i (k i)) = b) ≤
      (2 : ℚ≥0) ^ padicValNat 2 A.det.natAbs * ε ^ Fintype.card I := by
  classical
  have ha (v : I → ZMod (2 ^ m)) :
      uniformProb (fun k : I → K => (fun i => d i (k i)) = v) ≤ ε ^ Fintype.card I := by
    simp only [funext_iff]
    rw [uniformProb_pi (fun i (k : K) => d i k = v i)]
    calc
      _ ≤ ∏ _i : I, ε := Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hd i (v i))
      _ = _ := by simp
  have hpre := uniformProb_preimage_le (fun (k : I → K) i => d i (k i))
    (fun v => (A.map (Int.castRingHom (ZMod (2 ^ m)))).mulVec v = b)
    (ε ^ Fintype.card I) ha
  apply hpre.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast matrix_fibre_card_le A m hA hv b

/-- The exact conditioning step used after selecting k differing encoded
symbols. `J` contains every other key; their total contribution is arbitrary. -/
theorem ehc_conditioned_adu {I K J : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Fintype J] [Nonempty J]
    (A : Matrix I I ℤ) (t : ℕ) (ht : t ≤ 64) (hA : A.det ≠ 0)
    (hv : padicValNat 2 A.det.natAbs ≤ t)
    (d : I → K → ZMod (2 ^ 64)) (ε : ℚ≥0)
    (hd : ∀ i z, uniformProb (fun k => d i k = z) ≤ ε)
    (offset : J → I → ZMod (2 ^ 64)) (b : I → ZMod (2 ^ 64)) :
    uniformProb (fun k : J × (I → K) =>
      (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (k.2 i)) + offset k.1 = b) ≤
      (2 : ℚ≥0) ^ t * ε ^ Fintype.card I := by
  apply uniformProb_prod_le
  intro j
  have he : (fun k : I → K =>
      (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (k i)) + offset j = b) =
      (fun k => (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (k i)) = b - offset j) := by
    funext k
    exact propext (eq_sub_iff_add_eq.symm)
  rw [he]
  exact (matrix_atom_bound A 64 hA (hv.trans ht) d ε hd _).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hv) (by positivity))

/-- Selecting an injective list of columns merely permutes the full independent
key space. All unselected columns are conditioned on, even if they differ. -/
theorem combine_selected_bound {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Nonempty K] {r t : ℕ}
    (T : Matrix (Fin r) I ℤ) (j : Fin r ↪ I)
    (hA : (T.submatrix id j).det ≠ 0)
    (hv : padicValNat 2 (T.submatrix id j).det.natAbs ≤ t) (ht : t ≤ 64)
    (d : I → K → ZMod (2 ^ 64)) (ε : ℚ≥0)
    (hd : ∀ i z, uniformProb (fun k => d (j i) k = z) ≤ ε)
    (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k : I → K =>
      (T.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (k i)) = b) ≤
      (2 : ℚ≥0) ^ t * ε ^ r := by
  classical
  let J := {i : I // i ∉ Set.range j}
  let e : Fin r ⊕ J ≃ I :=
    (Equiv.sumCongr (Equiv.ofInjective j j.injective) (Equiv.refl J)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range j))
  let keyEquiv : ((J → K) × (Fin r → K)) ≃ (I → K) :=
    (Equiv.prodComm _ _).trans ((Equiv.sumArrowEquivProdArrow (Fin r) J K).symm.trans
      (Equiv.arrowCongr e (Equiv.refl K)))
  let offset (k : J → K) : Fin r → ZMod (2 ^ 64) := fun row =>
    ∑ i : J, (T row i.1 : ZMod (2 ^ 64)) * d i.1 (k i)
  have he0 (i : Fin r) : e (Sum.inl i) = j i := rfl
  have he1 (i : J) : e (Sum.inr i) = i.1 := rfl
  have hkey (k : (J → K) × (Fin r → K)) (i : Fin r ⊕ J) :
      keyEquiv k (e i) = Sum.elim k.2 k.1 i := by
    simp [keyEquiv, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]
  have hsplit (k : (J → K) × (Fin r → K)) :
      (T.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (keyEquiv k i)) =
      ((T.submatrix id j).map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec
        (fun i => d (j i) (k.2 i)) + offset k.1 := by
    funext row
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      Matrix.submatrix_apply, id_eq, Pi.add_apply, offset]
    rw [← e.sum_comp]
    simp only [Fintype.sum_sum_type, hkey, he0, he1, Sum.elim_inl, Sum.elim_inr]
    rfl
  rw [← uniformProb_equiv keyEquiv]
  simp only [hsplit]
  simpa only [Fintype.card_fin] using ehc_conditioned_adu (T.submatrix id j) t ht hA hv
    (fun i => d (j i)) ε hd offset b

/-- The actual EHC formula, with a whole independent NH key for each encoded
symbol. Encoders may be nonlinear; only their symbol distance matters. -/
def ehc {X I : Type*} [Fintype I] {r n : ℕ}
    (encode : X → I → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) I ℤ) (x : X) (k : I → (Fin n × Bool → ZMod (2 ^ 32))) :
    Fin r → ZMod (2 ^ 64) :=
  (T.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => nh32 (encode x i) (k i))

/-- Corrected EHC theorem: 2^t / 2^(32k) AΔU for a distance-k encoder and
maximal-minor valuations at most t. The distance and minor conditions are
structural hypotheses, not assumed collision bounds. -/
theorem ehc_adu {X I : Type*} [Fintype I] [DecidableEq I] {r n t : ℕ}
    (encode : X → I → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) I ℤ) (ht : t ≤ 64)
    (hminor : ∀ j : Fin r ↪ I,
      (T.submatrix id j).det ≠ 0 ∧ padicValNat 2 (T.submatrix id j).det.natAbs ≤ t)
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin r ↪ I, ∀ i, encode x (j i) ≠ encode y (j i))
    (x y : X) (hxy : x ≠ y) (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k => ehc encode T x k - ehc encode T y k = b) ≤
      (2 : ℚ≥0) ^ t / 2 ^ (32 * r) := by
  classical
  obtain ⟨j, hj⟩ := hdistance x y hxy
  have h := combine_selected_bound T j (hminor j).1 (hminor j).2 ht
    (fun i k => nh32 (encode x i) k - nh32 (encode y i) k)
    (1 / (2 : ℚ≥0) ^ 32) (fun i z => nh32_adu _ _ (hj i) z) b
  simpa only [ehc, ← Matrix.mulVec_sub, Pi.sub_apply, div_pow, one_pow,
    ← pow_mul, mul_one_div] using h

theorem ehc_T2_adu {X : Type*} {n : ℕ}
    (encode : X → Fin 7 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode x (j i) ≠ encode y (j i))
    (x y : X) (hxy : x ≠ y) (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k => ehc encode T2 x k - ehc encode T2 y k = b) ≤ 1 / (2 : ℚ≥0) ^ 62 := by
  convert ehc_adu encode T2 (by decide : 2 ≤ 64) T2_minor_valuations hdistance x y hxy b using 1
  norm_num

theorem ehc_T3_adu {X : Type*} {n : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (x y : X) (hxy : x ≠ y) (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k => ehc encode T3 x k - ehc encode T3 y k = b) ≤ 1 / (2 : ℚ≥0) ^ 94 := by
  convert ehc_adu encode T3 (by decide : 2 ≤ 64) T3_minor_valuations hdistance x y hxy b using 1
  norm_num

end ProvenHashes.Halftime
