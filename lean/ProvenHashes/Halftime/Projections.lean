import ProvenHashes.Halftime.EHC

namespace ProvenHashes.Halftime
open scoped Matrix BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem valuation_le_four {d : ℤ} (hd : d ≠ 0) (h32 : ¬ (32 : ℤ) ∣ d) :
    padicValNat 2 d.natAbs ≤ 4 := by
  have hn : ¬ (2 ^ 5 : ℕ) ∣ d.natAbs := by
    intro h
    exact h32 (by simpa using Int.natCast_dvd.mpr h)
  rw [padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hd)] at hn
  omega

/-- For one- and two-row projections a zero minor gives a valid trivial
bound. Nonzero minors use their exact kernel size. -/
theorem combine_small_weight_bound {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Nonempty K] {r : ℕ} (hr : r ≤ 2)
    (T : Matrix (Fin r) I ℤ) (j : Fin r ↪ I)
    (hv : (T.submatrix id j).det ≠ 0 → ¬ (32 : ℤ) ∣ (T.submatrix id j).det)
    (d : I → K → ZMod (2 ^ 64))
    (hd : ∀ i z, uniformProb (fun k => d (j i) k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k : I → K =>
      (T.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (k i)) = b) ≤
      (weight (T.submatrix id j).det : ℚ≥0) * (1 / 2 ^ 32) ^ r := by
  by_cases hA : (T.submatrix id j).det = 0
  · apply (uniformProb_le_one _).trans
    interval_cases r <;> norm_num [weight, hA]
  · have hval := valuation_le_four hA (hv hA)
    have hval64 : padicValNat 2 (T.submatrix id j).det.natAbs ≤ 64 := hval.trans (by decide)
    have hw : weight (T.submatrix id j).det = 2 ^ padicValNat 2 (T.submatrix id j).det.natAbs :=
      gcd_two_pow_of_val_le _ 64 (Int.natAbs_ne_zero.mpr hA) hval64
    rw [hw, Nat.cast_pow, Nat.cast_ofNat]
    exact combine_selected_bound T j hA le_rfl hval64 d _ hd b

def combine {I K : Type*} [Fintype I] {r : ℕ} (T : Matrix (Fin r) I ℤ)
    (d : I → K → ZMod (2 ^ 64)) (k : I → K) : Fin r → ZMod (2 ^ 64) :=
  (T.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec (fun i => d i (k i))

theorem row_atom_bound {N r : ℕ} {K : Type*} [Fintype K] [Nonempty K]
    (T : Matrix (Fin r) (Fin N) ℤ) (row : Fin r) (a : Fin N)
    (hv : T row a ≠ 0 → ¬ (32 : ℤ) ∣ T row a)
    (d : Fin N → K → ZMod (2 ^ 64))
    (hd : ∀ z, uniformProb (fun k => d a k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (b : ZMod (2 ^ 64)) :
    uniformProb (fun k => combine T d k row = b) ≤ (weight (T row a) : ℚ≥0) / 2 ^ 32 := by
  let j : Fin 1 ↪ Fin N := ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩
  have hdet : ((T.submatrix (fun _ : Fin 1 => row) id).submatrix id j).det = T row a := by
    simp [Matrix.submatrix, j]
  have H := combine_small_weight_bound (by decide : 1 ≤ 2)
    (T.submatrix (fun _ : Fin 1 => row) id) j (by simpa only [hdet] using hv)
    d (fun _ z => hd z) (fun _ => b)
  simpa [combine, Matrix.mulVec, dotProduct, Matrix.submatrix, funext_iff, hdet] using H

def pairEmbedding {N : ℕ} (a b : Fin N) (hab : a ≠ b) : Fin 2 ↪ Fin N :=
  ⟨![a, b], by intro i j he; fin_cases i <;> fin_cases j <;> simp_all⟩

theorem pair_atom_bound {N r : ℕ} {K : Type*} [Fintype K] [Nonempty K]
    (T : Matrix (Fin r) (Fin N) ℤ) (row row' : Fin r) (a b : Fin N) (hab : a ≠ b)
    (hv : det2 T row row' a b ≠ 0 → ¬ (32 : ℤ) ∣ det2 T row row' a b)
    (d : Fin N → K → ZMod (2 ^ 64))
    (ha : ∀ z, uniformProb (fun k => d a k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hb : ∀ z, uniformProb (fun k => d b k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (u v : ZMod (2 ^ 64)) :
    uniformProb (fun k => combine T d k row = u ∧ combine T d k row' = v) ≤
      (weight (det2 T row row' a b) : ℚ≥0) * (1 / 2 ^ 32) ^ 2 := by
  let j := pairEmbedding a b hab
  have hdet : ((T.submatrix ![row, row'] id).submatrix id j).det = det2 T row row' a b := by
    simp [Matrix.det_fin_two, Matrix.submatrix, det2, j, pairEmbedding]
  have hd (i : Fin 2) (z : ZMod (2 ^ 64)) :
      uniformProb (fun k => d (j i) k = z) ≤ 1 / (2 : ℚ≥0) ^ 32 := by
    fin_cases i
    · exact ha z
    · exact hb z
  have H := combine_small_weight_bound (by decide : 2 ≤ 2)
    (T.submatrix ![row, row'] id) j (by simpa only [hdet] using hv) d hd ![u, v]
  rw [hdet] at H
  simpa [combine, Matrix.mulVec, dotProduct, Matrix.submatrix, funext_iff, Fin.forall_fin_two] using H

theorem T2_small_entries : ∀ r : Fin 2, ∀ a : Fin 7, T2 r a ≠ 0 → ¬ (32 : ℤ) ∣ T2 r a := by decide
theorem T3_small_entries : ∀ r : Fin 3, ∀ a : Fin 9, T3 r a ≠ 0 → ¬ (32 : ℤ) ∣ T3 r a := by decide
theorem T3_small_pairs : ∀ r s : Fin 3, ∀ a b : Fin 9,
    det2 T3 r s a b ≠ 0 → ¬ (32 : ℤ) ∣ det2 T3 r s a b := by decide

theorem T2_distinct_coefficients : ∀ a b : Fin 7, a ≠ b →
    singleton2 0 a b + singleton2 1 a b ≤ 5 := by decide

theorem T3_distinct_coefficients : ∀ a b c : Fin 9, a ≠ b → a ≠ c → b ≠ c →
    singleton3 0 a b c + singleton3 1 a b c + singleton3 2 a b c ≤ 6 ∧
    pair3 0 1 a b c + pair3 0 2 a b c + pair3 1 2 a b c ≤ 9 := by decide

theorem T2_subset_bounds {K : Type*} [Fintype K] [Nonempty K]
    (d : Fin 7 → K → ZMod (2 ^ 64)) (j : Fin 2 ↪ Fin 7)
    (hd : ∀ i z, uniformProb (fun k => d (j i) k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    (uniformProb (fun k => combine T2 d k 0 = b 0) +
      uniformProb (fun k => combine T2 d k 1 = b 1) ≤ 5 / (2 : ℚ≥0) ^ 32) ∧
    (uniformProb (fun k => combine T2 d k 0 = b 0 ∧ combine T2 d k 1 = b 1) ≤
      4 / (2 : ℚ≥0) ^ 64) := by
  have hab : j 0 ≠ j 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (j.injective h)
  have hs (r : Fin 2) : uniformProb (fun k => combine T2 d k r = b r) ≤
      (singleton2 r (j 0) (j 1) : ℚ≥0) * (1 / 2 ^ 32) := by
    have h0 := row_atom_bound T2 r (j 0) (T2_small_entries r (j 0)) d (hd 0) (b r)
    have h1 := row_atom_bound T2 r (j 1) (T2_small_entries r (j 1)) d (hd 1) (b r)
    simpa [singleton2, Nat.cast_min, min_mul, mul_one_div] using le_min h0 h1
  constructor
  · calc
      _ ≤ ((singleton2 0 (j 0) (j 1) + singleton2 1 (j 0) (j 1) : ℕ) : ℚ≥0) * (1 / 2 ^ 32) := by
        simpa only [Nat.cast_add, add_mul] using add_le_add (hs 0) (hs 1)
      _ ≤ 5 * (1 / 2 ^ 32) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast T2_distinct_coefficients (j 0) (j 1) hab
      _ = _ := by ring
  · have H := combine_selected_bound T2 j (T2_minor_valuations j).1 (T2_minor_valuations j).2
      (by decide : 2 ≤ 64) d (1 / (2 : ℚ≥0) ^ 32) hd b
    simpa [combine, funext_iff, Fin.forall_fin_two] using H

theorem T3_subset_bounds {K : Type*} [Fintype K] [Nonempty K]
    (d : Fin 9 → K → ZMod (2 ^ 64)) (j : Fin 3 ↪ Fin 9)
    (hd : ∀ i z, uniformProb (fun k => d (j i) k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    (uniformProb (fun k => combine T3 d k 0 = b 0) +
      uniformProb (fun k => combine T3 d k 1 = b 1) +
      uniformProb (fun k => combine T3 d k 2 = b 2) ≤ 6 / (2 : ℚ≥0) ^ 32) ∧
    (uniformProb (fun k => combine T3 d k 0 = b 0 ∧ combine T3 d k 1 = b 1) +
      uniformProb (fun k => combine T3 d k 0 = b 0 ∧ combine T3 d k 2 = b 2) +
      uniformProb (fun k => combine T3 d k 1 = b 1 ∧ combine T3 d k 2 = b 2) ≤
      9 / (2 : ℚ≥0) ^ 64) ∧
    (uniformProb (fun k => combine T3 d k 0 = b 0 ∧ combine T3 d k 1 = b 1 ∧ combine T3 d k 2 = b 2) ≤
      4 / (2 : ℚ≥0) ^ 96) := by
  have hab : j 0 ≠ j 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (j.injective h)
  have hac : j 0 ≠ j 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (j.injective h)
  have hbc : j 1 ≠ j 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (j.injective h)
  have coeff := T3_distinct_coefficients (j 0) (j 1) (j 2) hab hac hbc
  have hs (r : Fin 3) : uniformProb (fun k => combine T3 d k r = b r) ≤
      (singleton3 r (j 0) (j 1) (j 2) : ℚ≥0) * (1 / 2 ^ 32) := by
    have h0 := row_atom_bound T3 r (j 0) (T3_small_entries r (j 0)) d (hd 0) (b r)
    have h1 := row_atom_bound T3 r (j 1) (T3_small_entries r (j 1)) d (hd 1) (b r)
    have h2 := row_atom_bound T3 r (j 2) (T3_small_entries r (j 2)) d (hd 2) (b r)
    simpa [singleton3, Nat.cast_min, min_mul, mul_one_div] using le_min h0 (le_min h1 h2)
  have hp (r s : Fin 3) : uniformProb (fun k => combine T3 d k r = b r ∧ combine T3 d k s = b s) ≤
      (pair3 r s (j 0) (j 1) (j 2) : ℚ≥0) * (1 / 2 ^ 32) ^ 2 := by
    have h01 := pair_atom_bound T3 r s (j 0) (j 1) hab (T3_small_pairs r s (j 0) (j 1)) d (hd 0) (hd 1) (b r) (b s)
    have h02 := pair_atom_bound T3 r s (j 0) (j 2) hac (T3_small_pairs r s (j 0) (j 2)) d (hd 0) (hd 2) (b r) (b s)
    have h12 := pair_atom_bound T3 r s (j 1) (j 2) hbc (T3_small_pairs r s (j 1) (j 2)) d (hd 1) (hd 2) (b r) (b s)
    simpa [pair3, Nat.cast_min, min_mul] using le_min h01 (le_min h02 h12)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ((singleton3 0 (j 0) (j 1) (j 2) + singleton3 1 (j 0) (j 1) (j 2) +
          singleton3 2 (j 0) (j 1) (j 2) : ℕ) : ℚ≥0) * (1 / 2 ^ 32) := by
        simpa only [Nat.cast_add, add_mul] using add_le_add (add_le_add (hs 0) (hs 1)) (hs 2)
      _ ≤ 6 * (1 / 2 ^ 32) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast coeff.1
      _ = _ := by ring
  · calc
      _ ≤ ((pair3 0 1 (j 0) (j 1) (j 2) + pair3 0 2 (j 0) (j 1) (j 2) +
          pair3 1 2 (j 0) (j 1) (j 2) : ℕ) : ℚ≥0) * (1 / 2 ^ 32) ^ 2 := by
        simpa only [Nat.cast_add, add_mul] using add_le_add (add_le_add (hp 0 1) (hp 0 2)) (hp 1 2)
      _ ≤ 9 * (1 / 2 ^ 32) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast coeff.2
      _ = _ := by norm_num
  · have H := combine_selected_bound T3 j (T3_minor_valuations j).1 (T3_minor_valuations j).2
      (by decide : 2 ≤ 64) d (1 / (2 : ℚ≥0) ^ 32) hd b
    simpa [combine, funext_iff, Fin.forall_fin_succ] using H

end ProvenHashes.Halftime
