import ProvenHashes.Halftime.SharpTruncation
import ProvenHashes.Halftime.Projections
import ProvenHashes.Halftime.EndToEnd

namespace ProvenHashes.Halftime
open scoped BigOperators Matrix
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem four_mul_eq_iff_lowBits_eq (x y : ZMod (2 ^ 64)) :
    (4 : ZMod (2 ^ 64)) * x = 4 * y ↔ lowBits 62 (by decide) x = lowBits 62 (by decide) y := by
  have hk (z : ZMod (2 ^ 64)) : (4 : ZMod (2 ^ 64)) * z = 0 ↔ lowBits 62 (by decide) z = 0 := by
    rw [← ZMod.natCast_zmod_val z]
    have he : ((4 * z.val : ℕ) : ZMod (2 ^ 64)) = 4 * (z.val : ZMod (2 ^ 64)) := by simp
    rw [← he, ZMod.natCast_eq_zero_iff, map_natCast, ZMod.natCast_eq_zero_iff]
    change 4 * (2 ^ 62) ∣ 4 * z.val ↔ 2 ^ 62 ∣ z.val
    exact Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)
  rw [← sub_eq_zero, ← mul_sub, hk, map_sub, sub_eq_zero]

/-- A modular left multiplier taking the coefficient to four lets us use
the sharp 62-bit NH bound, instead of a union over four 64-bit atoms. -/
theorem mul_atom_of_lowBits {K : Type*} [Fintype K]
    (d : K → ZMod (2 ^ 64)) (c w : ZMod (2 ^ 64)) (hw : w * c = 4)
    (η : ℚ≥0) (hd : ∀ z, uniformProb (fun k => lowBits 62 (by decide) (d k) = z) ≤ η)
    (t : ZMod (2 ^ 64)) :
    uniformProb (fun k => c * d k = t) ≤ η := by
  classical
  by_cases ht : ∃ z, c * z = t
  · obtain ⟨z, hz⟩ := ht
    apply (uniformProb_mono (fun k (hk : c * d k = t) => ?_)).trans (hd (lowBits 62 (by decide) z))
    apply (four_mul_eq_iff_lowBits_eq _ _).mp
    have he := congrArg (fun v => w * v) (hk.trans hz.symm)
    simpa only [← mul_assoc, hw] using he
  · have he (k : K) : ¬ c * d k = t := fun hk => ht ⟨d k, hk⟩
    simp [uniformProb, he]

theorem linear_pair_sharp {K : Type*} [Fintype K] [Nonempty K]
    (p q : K → ZMod (2 ^ 64)) (b c d w : ZMod (2 ^ 64)) (hw : w * (d - c * b) = 4)
    (ε η : ℚ≥0) (hp : ∀ t, uniformProb (fun k => p k = t) ≤ ε)
    (hq : ∀ z, uniformProb (fun k => lowBits 62 (by decide) (q k) = z) ≤ η)
    (u v : ZMod (2 ^ 64)) :
    uniformProb (fun k : K × K =>
      p k.2 + b * q k.1 = u ∧ c * p k.2 + d * q k.1 = v) ≤ ε * η := by
  classical
  rw [uniformProb_prod]
  change mean (fun k => uniformProb (fun a => p a + b * q k = u ∧ c * p a + d * q k = v)) ≤ _
  let E (k : K) := (d - c * b) * q k = v - c * u
  calc
    _ ≤ mean (fun k => ε * indicator E k) := by
      apply mean_mono
      intro k
      by_cases he : E k
      · simp only [indicator, he, if_true, mul_one]
        exact (uniformProb_mono (fun (a : K)
          (ha : p a + b * q k = u ∧ c * p a + d * q k = v) =>
            (eq_sub_iff_add_eq.mpr ha.1 : p a = u - b * q k))).trans (hp _)
      · have hn (a : K) : ¬ (p a + b * q k = u ∧ c * p a + d * q k = v) := by
          intro ha
          apply he
          dsimp [E]
          linear_combination ha.2 - c * ha.1
        simp [indicator, he, uniformProb, hn]
    _ = ε * uniformProb E := by rw [mean_mul, mean_indicator]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_atom_of_lowBits q _ w hw η hq _) (zero_le _)

/-- Explicit modular witnesses for the twelve nonzero determinants of T2.
Their correctness is checked below by integer remainder computation. -/
def fourWitness : ℤ → ℤ
  | 1 => 4
  | -1 => -4
  | 2 => 2
  | -2 => -2
  | 3 => -6148914691236517204
  | -3 => 6148914691236517204
  | 4 => 1
  | -4 => -1
  | 7 => -5270498306774157604
  | -7 => 5270498306774157604
  | 15 => -4919131752989213764
  | -15 => 4919131752989213764
  | _ => 0

theorem T2_four_witness : ∀ a b : Fin 7, a ≠ b →
    (fourWitness (det2 T2 0 1 a b) * det2 T2 0 1 a b - 4) % (2 ^ 64 : ℤ) = 0 := by decide

theorem T2_column_unit : ∀ a : Fin 7, T2 0 a = 1 ∨ T2 1 a = 1 := by decide

theorem T2_witness_mul (a b : Fin 7) (hab : a ≠ b) :
    (fourWitness (det2 T2 0 1 a b) : ZMod (2 ^ 64)) * (det2 T2 0 1 a b : ℤ) = 4 := by
  apply sub_eq_zero.mp
  rw [← Int.cast_mul, ← Int.cast_ofNat, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.dvd_of_emod_eq_zero (T2_four_witness a b hab)

theorem combine_selected_custom {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Nonempty K] {r : ℕ}
    (T : Matrix (Fin r) I ℤ) (j : Fin r ↪ I) (d : I → K → ZMod (2 ^ 64)) (η : ℚ≥0)
    (hselected : ∀ b, uniformProb (fun k : Fin r → K =>
      ((T.submatrix id j).map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec
        (fun i => d (j i) (k i)) = b) ≤ η)
    (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k => combine T d k = b) ≤ η := by
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
      combine T d (keyEquiv k) =
      ((T.submatrix id j).map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec
        (fun i => d (j i) (k.2 i)) + offset k.1 := by
    funext row
    simp only [combine, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Matrix.submatrix_apply, id_eq, Pi.add_apply, offset]
    rw [← e.sum_comp]
    simp only [Fintype.sum_sum_type, hkey, he0, he1, Sum.elim_inl, Sum.elim_inr]
    rfl
  rw [← uniformProb_equiv keyEquiv]
  simp only [hsplit]
  apply uniformProb_prod_le
  intro k
  simpa only [eq_sub_iff_add_eq] using hselected (b - offset k)

theorem T2_selected_sharp {K : Type*} [Fintype K] [Nonempty K]
    (j : Fin 2 ↪ Fin 7) (d : Fin 7 → K → ZMod (2 ^ 64)) (ε η : ℚ≥0)
    (hd : ∀ i t, uniformProb (fun k => d (j i) k = t) ≤ ε)
    (hl : ∀ i t, uniformProb (fun k => lowBits 62 (by decide) (d (j i) k) = t) ≤ η)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k : Fin 2 → K =>
      ((T2.submatrix id j).map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec
        (fun i => d (j i) (k i)) = b) ≤ ε * η := by
  let e : (K × K) ≃ (Fin 2 → K) := (Equiv.prodComm K K).trans (piFinTwoEquiv (fun _ => K)).symm
  have hab : j 0 ≠ j 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (j.injective h)
  let w : ZMod (2 ^ 64) := fourWitness (det2 T2 0 1 (j 0) (j 1))
  have hw := T2_witness_mul (j 0) (j 1) hab
  rw [← uniformProb_equiv e]
  rcases T2_column_unit (j 0) with h0 | h1
  · have hw' : w * ((T2 1 (j 1) : ZMod (2 ^ 64)) -
        (T2 1 (j 0) : ZMod (2 ^ 64)) * T2 0 (j 1)) = 4 := by
      simpa [det2, h0, w, mul_comm] using hw
    have H := linear_pair_sharp (d (j 0)) (d (j 1))
      (T2 0 (j 1)) (T2 1 (j 0)) (T2 1 (j 1)) w hw' ε η (hd 0) (hl 1) (b 0) (b 1)
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, funext_iff, Fin.forall_fin_two,
      Fin.sum_univ_two, e, piFinTwoEquiv, h0] using H
  · have hw' : (-w) * ((T2 0 (j 1) : ZMod (2 ^ 64)) -
        (T2 0 (j 0) : ZMod (2 ^ 64)) * T2 1 (j 1)) = 4 := by
      have hw0 : w * ((T2 0 (j 0) : ZMod (2 ^ 64)) * T2 1 (j 1) - T2 0 (j 1)) = 4 := by
        simpa [det2, h1, w] using hw
      calc
        _ = w * ((T2 0 (j 0) : ZMod (2 ^ 64)) * T2 1 (j 1) - T2 0 (j 1)) := by ring
        _ = 4 := hw0
    have H := linear_pair_sharp (d (j 0)) (d (j 1))
      (T2 1 (j 1)) (T2 0 (j 0)) (T2 0 (j 1)) (-w) hw' ε η (hd 0) (hl 1) (b 1) (b 0)
    simpa [Matrix.mulVec, dotProduct, Matrix.submatrix, funext_iff, Fin.forall_fin_two,
      Fin.sum_univ_two, e, piFinTwoEquiv, h1, and_comm] using H

def sharpEntryWeight (c : ℤ) : ℕ := if c = 0 then 2 ^ 32 else if c = 1 then 1 else 2

theorem T2_entry_cases : ∀ r : Fin 2, ∀ a : Fin 7,
    T2 r a = 0 ∨ T2 r a = 1 ∨ T2 r a = 2 ∨ T2 r a = 4 := by decide

theorem T2_sharp_coefficients : ∀ a b : Fin 7, a ≠ b →
    min (sharpEntryWeight (T2 0 a)) (sharpEntryWeight (T2 0 b)) +
      min (sharpEntryWeight (T2 1 a)) (sharpEntryWeight (T2 1 b)) ≤ 3 := by decide

theorem T2_entry_atom {K : Type*} [Fintype K]
    (r : Fin 2) (a : Fin 7) (d : K → ZMod (2 ^ 64))
    (hd : ∀ t, uniformProb (fun k => d k = t) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hl : ∀ t, uniformProb (fun k => lowBits 62 (by decide) (d k) = t) ≤ 2 / (2 : ℚ≥0) ^ 32)
    (t : ZMod (2 ^ 64)) :
    uniformProb (fun k => (T2 r a : ZMod (2 ^ 64)) * d k = t) ≤
      (sharpEntryWeight (T2 r a) : ℚ≥0) / 2 ^ 32 := by
  rcases T2_entry_cases r a with h | h | h | h
  · have he : (sharpEntryWeight (T2 r a) : ℚ≥0) / 2 ^ 32 = 1 := by
      rw [h]
      norm_num [sharpEntryWeight]
    rw [he]
    exact uniformProb_le_one _
  · simpa [h, sharpEntryWeight] using hd t
  · simpa [h, sharpEntryWeight] using
      mul_atom_of_lowBits d 2 2 (by norm_num) (2 / (2 : ℚ≥0) ^ 32) hl t
  · simpa [h, sharpEntryWeight] using
      mul_atom_of_lowBits d 4 1 (by norm_num) (2 / (2 : ℚ≥0) ^ 32) hl t

theorem row_atom_custom {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [Nonempty K]
    {r : ℕ} (T : Matrix (Fin r) I ℤ) (row : Fin r) (a : I)
    (d : I → K → ZMod (2 ^ 64)) (η : ℚ≥0)
    (hd : ∀ t, uniformProb (fun k => (T row a : ZMod (2 ^ 64)) * d a k = t) ≤ η)
    (t : ZMod (2 ^ 64)) : uniformProb (fun k => combine T d k row = t) ≤ η := by
  classical
  apply uniformProb_of_update_bound _ a t η
  intro k
  have he (v : K) : combine T d (Function.update k a v) row =
      (T row a : ZMod (2 ^ 64)) * d a v +
        ∑ i ∈ Finset.univ.erase a, (T row i : ZMod (2 ^ 64)) * d i (k i) := by
    change (∑ i, (T row i : ZMod (2 ^ 64)) * d i (Function.update k a v i)) = _
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  simp only [he]
  simpa only [eq_sub_iff_add_eq] using hd
    (t - ∑ i ∈ Finset.univ.erase a, (T row i : ZMod (2 ^ 64)) * d i (k i))

/-- Sharp T2 projections, with the sharp residue hypothesis explicit. Integer
NH discharges both hypotheses in `nh_T2_sharp_subset_bounds`. -/
theorem T2_sharp_subset_bounds {K : Type*} [Fintype K] [Nonempty K]
    (d : Fin 7 → K → ZMod (2 ^ 64)) (j : Fin 2 ↪ Fin 7)
    (hd : ∀ i z, uniformProb (fun k => d (j i) k = z) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hl : ∀ i z, uniformProb (fun k => lowBits 62 (by decide) (d (j i) k) = z) ≤ 2 / (2 : ℚ≥0) ^ 32)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    (uniformProb (fun k => combine T2 d k 0 = b 0) +
      uniformProb (fun k => combine T2 d k 1 = b 1) ≤ 3 / (2 : ℚ≥0) ^ 32) ∧
    (uniformProb (fun k => combine T2 d k 0 = b 0 ∧ combine T2 d k 1 = b 1) ≤
      2 / (2 : ℚ≥0) ^ 64) := by
  have hab : j 0 ≠ j 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (j.injective h)
  have hs (r : Fin 2) : uniformProb (fun k => combine T2 d k r = b r) ≤
      (min (sharpEntryWeight (T2 r (j 0))) (sharpEntryWeight (T2 r (j 1))) : ℚ≥0) / 2 ^ 32 := by
    have h0 := row_atom_custom T2 r (j 0) d _ (T2_entry_atom r (j 0) _ (hd 0) (hl 0)) (b r)
    have h1 := row_atom_custom T2 r (j 1) d _ (T2_entry_atom r (j 1) _ (hd 1) (hl 1)) (b r)
    simpa [Nat.cast_min, min_div_div_right] using le_min h0 h1
  constructor
  · calc
      _ ≤ ((min (sharpEntryWeight (T2 0 (j 0))) (sharpEntryWeight (T2 0 (j 1))) +
          min (sharpEntryWeight (T2 1 (j 0))) (sharpEntryWeight (T2 1 (j 1))) : ℕ) : ℚ≥0) / 2 ^ 32 := by
        simpa only [Nat.cast_add, Nat.cast_min, add_div] using add_le_add (hs 0) (hs 1)
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast T2_sharp_coefficients (j 0) (j 1) hab) (by positivity)
  · have H := combine_selected_custom T2 j d
      ((1 / (2 : ℚ≥0) ^ 32) * (2 / (2 : ℚ≥0) ^ 32))
      (T2_selected_sharp j d _ _ hd hl) b
    simpa only [funext_iff, Fin.forall_fin_two, div_mul_div_comm, one_mul, ← pow_add] using H

theorem nh_T2_sharp_subset_bounds {n : ℕ}
    (x y : Fin 7 → (Fin n × Bool → ZMod (2 ^ 32))) (j : Fin 2 ↪ Fin 7)
    (hxy : ∀ i, x (j i) ≠ y (j i)) (b : Fin 2 → ZMod (2 ^ 64)) :
    let d := fun i k => nh32 (x i) k - nh32 (y i) k
    (uniformProb (fun k => combine T2 d k 0 = b 0) +
      uniformProb (fun k => combine T2 d k 1 = b 1) ≤ 3 / (2 : ℚ≥0) ^ 32) ∧
    (uniformProb (fun k => combine T2 d k 0 = b 0 ∧ combine T2 d k 1 = b 1) ≤
      2 / (2 : ℚ≥0) ^ 64) :=
  T2_sharp_subset_bounds (fun (i : Fin 7) (k : Fin n × Bool → ZMod (2 ^ 32)) =>
    nh32 (x i) k - nh32 (y i) k) j
    (fun i z => nh32_adu (x (j i)) (y (j i)) (hxy i) z)
    (fun i z => nh_mod62_adu (x (j i)) (y (j i)) (hxy i) z) b

end ProvenHashes.Halftime
