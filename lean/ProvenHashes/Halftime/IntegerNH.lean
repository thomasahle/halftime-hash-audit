import ProvenHashes.Halftime.Probability

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 2000000

/-- Products use unsigned representatives *after* addition in the small ring. -/
def nh {q n : ℕ} (x k : Fin n × Bool → ZMod q) : ZMod (q * q) :=
  ∑ i, ((x (i, false) + k (i, false)).val : ZMod (q * q)) *
    ((x (i, true) + k (i, true)).val : ZMod (q * q))

lemma small_dvd {N z : ℤ} (hN : 0 < N) (hz : -N < z ∧ z < N)
    (h : N ∣ z) : z = 0 := by
  obtain ⟨a, rfl⟩ := h
  have : a = 0 := by
    by_contra ha
    rcases lt_or_gt_of_ne ha with ha | ha
    · have : N * a ≤ -N := by nlinarith
      omega
    · have : N ≤ N * a := by nlinarith
      omega
  simp [this]

/-- The UMAC unsigned one-pair lemma, at arbitrary radix `q` (not just powers
of two). This includes both wrap branches and every target difference. -/
theorem unsigned_pair_injective {q : ℕ} [NeZero q]
    (c c' d : ZMod q) (hc : c ≠ c') :
    Function.Injective (fun k : ZMod q =>
      (c.val : ZMod (q * q)) * k.val -
      (c'.val : ZMod (q * q)) * (k + d).val) := by
  suffices H : ∀ x y : ZMod q, x.val < y.val →
      (c.val : ZMod (q * q)) * x.val - (c'.val : ZMod (q * q)) * (x + d).val ≠
      (c.val : ZMod (q * q)) * y.val - (c'.val : ZMod (q * q)) * (y + d).val by
    intro x y h
    by_contra hxy
    have hn : x.val ≠ y.val := fun he => hxy (ZMod.val_injective q he)
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact H x y hlt h
    · exact H y x hlt h.symm
  intro x y hxy he
  have hq : (0 : ℤ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have cx : (0 : ℤ) ≤ c.val := by positivity
  have cy : (0 : ℤ) ≤ c'.val := by positivity
  have cq : (c.val : ℤ) < q := by exact_mod_cast c.val_lt
  have c'q : (c'.val : ℤ) < q := by exact_mod_cast c'.val_lt
  have cc : (c.val : ℤ) ≠ c'.val := by
    have hn : c.val ≠ c'.val := fun he => hc (ZMod.val_injective q he)
    exact_mod_cast hn
  have tx : (0 : ℤ) < (y.val : ℤ) - x.val := by omega
  have tq : (y.val : ℤ) - x.val < q := by
    have := y.val_lt; omega
  have hx := x.val_lt
  have hy := y.val_lt
  have hd := d.val_lt
  have hwrap : ((y + d).val : ℤ) - (x + d).val = (y.val : ℤ) - x.val ∨
      ((y + d).val : ℤ) - (x + d).val = (y.val : ℤ) - x.val - q := by
    by_cases hxw : x.val + d.val < q
    · by_cases hyw : y.val + d.val < q
      · rw [ZMod.val_add_of_lt hxw, ZMod.val_add_of_lt hyw]
        omega
      · rw [ZMod.val_add_of_lt hxw, ZMod.val_add_of_le (by omega : q ≤ y.val + d.val)]
        omega
    · rw [ZMod.val_add_of_le (by omega : q ≤ x.val + d.val),
        ZMod.val_add_of_le (by omega : q ≤ y.val + d.val)]
      omega
  have hdvd : (q : ℤ) * q ∣
      (c.val : ℤ) * ((y.val : ℤ) - x.val) -
        (c'.val : ℤ) * (((y + d).val : ℤ) - (x + d).val) := by
    have he' : (((c.val : ℤ) * x.val - (c'.val : ℤ) * (x + d).val : ℤ) : ZMod (q * q)) =
        (((c.val : ℤ) * y.val - (c'.val : ℤ) * (y + d).val : ℤ) : ZMod (q * q)) := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using he
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (q * q)).mp he'
    push_cast at this
    convert this using 1; ring
  rcases hwrap with hw | hw
  · rw [hw] at hdvd
    have ht : -(q : ℤ) * q <
        ((c.val : ℤ) - c'.val) * ((y.val : ℤ) - x.val) ∧
        ((c.val : ℤ) - c'.val) * ((y.val : ℤ) - x.val) < (q : ℤ) * q := by
      constructor
      · nlinarith [mul_pos (by omega : 0 < (q : ℤ) + c.val - c'.val) tx,
          mul_pos hq (by omega : 0 < (q : ℤ) - ((y.val : ℤ) - x.val))]
      · nlinarith [mul_pos (by omega : 0 < (q : ℤ) - c.val + c'.val) tx,
          mul_pos hq (by omega : 0 < (q : ℤ) - ((y.val : ℤ) - x.val))]
    rw [← sub_mul] at hdvd
    have hz := small_dvd (mul_pos hq hq) (by simpa only [neg_mul] using ht) hdvd
    exact (mul_ne_zero (sub_ne_zero.mpr cc) (ne_of_gt tx)) hz
  · rw [hw] at hdvd
    have hpos : 0 < (c.val : ℤ) * ((y.val : ℤ) - x.val) +
        c'.val * ((q : ℤ) - ((y.val : ℤ) - x.val)) := by
      have := mul_nonneg cx (le_of_lt tx)
      have := mul_nonneg cy (le_of_lt (sub_pos.mpr tq))
      rcases lt_or_gt_of_ne cc with hcc | hcc
      · nlinarith [mul_pos (by omega : 0 < (c'.val : ℤ)) (sub_pos.mpr tq)]
      · nlinarith [mul_pos (by omega : 0 < (c.val : ℤ)) tx]
    have hlt : (c.val : ℤ) * ((y.val : ℤ) - x.val) +
        c'.val * ((q : ℤ) - ((y.val : ℤ) - x.val)) < (q : ℤ) * q := by
      nlinarith [mul_pos (sub_pos.mpr cq) tx,
        mul_pos (sub_pos.mpr c'q) (sub_pos.mpr tq)]
    have hz := small_dvd (mul_pos hq hq) (show
        -((q : ℤ) * q) < (c.val : ℤ) * ((y.val : ℤ) - x.val) +
          c'.val * ((q : ℤ) - ((y.val : ℤ) - x.val)) ∧
        (c.val : ℤ) * ((y.val : ℤ) - x.val) +
          c'.val * ((q : ℤ) - ((y.val : ℤ) - x.val)) < (q : ℤ) * q from
        ⟨by nlinarith, hlt⟩) (by convert hdvd using 1; ring)
    omega

theorem unsigned_pair_add_injective {q : ℕ} [NeZero q]
    (c c' a b : ZMod q) (hc : c ≠ c') :
    Function.Injective (fun k : ZMod q =>
      (c.val : ZMod (q * q)) * (a + k).val -
      (c'.val : ZMod (q * q)) * (b + k).val) := by
  intro x y h
  have h' := unsigned_pair_injective c c' (b - a) hc
  have he : a + x = a + y := h' (by
    simpa only [show ∀ k : ZMod q, a + k + (b - a) = b + k by intro k; ring] using h)
  exact add_left_cancel he

private def rest {q n : ℕ} (x k : Fin n × Bool → ZMod q) (i : Fin n) :
    ZMod (q * q) :=
  ∑ j ∈ Finset.univ.erase i,
    ((x (j, false) + k (j, false)).val : ZMod (q * q)) *
    ((x (j, true) + k (j, true)).val : ZMod (q * q))

lemma nh_update_false {q n : ℕ} (x k : Fin n × Bool → ZMod q)
    (i : Fin n) (v : ZMod q) :
    nh x (Function.update k (i, false) v) =
      ((x (i, true) + k (i, true)).val : ZMod (q * q)) *
        (x (i, false) + v).val + rest x k i := by
  classical
  unfold nh rest
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [mul_comm]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update, hji]

lemma nh_update_true {q n : ℕ} (x k : Fin n × Bool → ZMod q)
    (i : Fin n) (v : ZMod q) :
    nh x (Function.update k (i, true) v) =
      ((x (i, false) + k (i, false)).val : ZMod (q * q)) *
        (x (i, true) + v).val + rest x k i := by
  classical
  unfold nh rest
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update, hji]

/-- Unsigned NH is `1/q` almost difference universal on distinct, equal-length
messages. Every one of the `2n` small-word key entries is uniform and independent. -/
theorem nh_adu {q n : ℕ} [NeZero q] (x y : Fin n × Bool → ZMod q)
    (hxy : x ≠ y) (t : ZMod (q * q)) :
    uniformProb (fun k => nh x k - nh y k = t) ≤ 1 / (q : ℚ≥0) := by
  classical
  obtain ⟨⟨i, b⟩, hi⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp hxy
  have H : ∀ k, Function.Injective (fun v =>
      nh x (Function.update k (i, !b) v) - nh y (Function.update k (i, !b) v)) := by
    intro k u v huv
    cases b
    · simp only [Bool.not_false, nh_update_true] at huv
      have hinj := unsigned_pair_add_injective
        (x (i, false) + k (i, false)) (y (i, false) + k (i, false))
        (x (i, true)) (y (i, true)) (by simpa using hi)
      apply hinj
      linear_combination huv
    · simp only [Bool.not_true, nh_update_false] at huv
      have hinj := unsigned_pair_add_injective
        (x (i, true) + k (i, true)) (y (i, true) + k (i, true))
        (x (i, false)) (y (i, false)) (by simpa using hi)
      apply hinj
      linear_combination huv
  simpa only [ZMod.card] using uniformProb_of_injective_update
    (fun k => nh x k - nh y k) (i, !b) H t

def nh32Equiv : ZMod (2 ^ 32 * 2 ^ 32) ≃+* ZMod (2 ^ 64) := by
  exact RingEquiv.refl _

def nh32 {n : ℕ} (x k : Fin n × Bool → ZMod (2 ^ 32)) : ZMod (2 ^ 64) :=
  nh32Equiv (nh x k)

theorem nh32_adu {n : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (t : ZMod (2 ^ 64)) :
    uniformProb (fun k => nh32 x k - nh32 y k = t) ≤ 1 / (2 : ℚ≥0) ^ 32 := by
  have he : (fun k => nh32 x k - nh32 y k = t) =
      (fun k => nh x k - nh y k = nh32Equiv.symm t) := by
    funext k
    apply propext
    rw [nh32, nh32, ← map_sub]
    exact nh32Equiv.toEquiv.apply_eq_iff_eq_symm_apply
  rw [he]
  simpa using nh_adu x y hxy (nh32Equiv.symm t)

/-- The un-hashed pair is one arbitrary `2w`-bit accumulator word. Its two
halves are passed through, not multiplied. This family is AU on the whole
message and AΔU only when the hashed portion differs. -/
def nhLast {q n : ℕ} (x : (Fin n × Bool → ZMod q) × ZMod (q * q))
    (k : Fin n × Bool → ZMod q) : ZMod (q * q) := nh x.1 k + x.2

theorem nhLast_adu {q n : ℕ} [NeZero q]
    (x y : (Fin n × Bool → ZMod q) × ZMod (q * q))
    (hxy : x.1 ≠ y.1) (t : ZMod (q * q)) :
    uniformProb (fun k => nhLast x k - nhLast y k = t) ≤ 1 / (q : ℚ≥0) := by
  convert nh_adu x.1 y.1 hxy (t - x.2 + y.2) using 1
  congr 1
  funext k
  simp only [nhLast]
  exact propext (by constructor <;> intro h <;> linear_combination h)

theorem nhLast_au {q n : ℕ} [NeZero q]
    (x y : (Fin n × Bool → ZMod q) × ZMod (q * q)) (hxy : x ≠ y) :
    uniformProb (fun k => nhLast x k = nhLast y k) ≤ 1 / (q : ℚ≥0) := by
  classical
  by_cases hfirst : x.1 = y.1
  · have hlast : x.2 ≠ y.2 := fun h => hxy (Prod.ext hfirst h)
    simp [nhLast, hfirst, hlast, uniformProb]
  · simpa only [sub_eq_zero] using nhLast_adu x y hfirst 0

theorem nhLast_same_hashed_difference {q n : ℕ}
    (x : Fin n × Bool → ZMod q) (a b : ZMod (q * q)) (k : Fin n × Bool → ZMod q) :
    nhLast (x, a) k - nhLast (x, b) k = a - b := by
  simp only [nhLast]
  abel

theorem nhLast_same_hashed_target_probability {q n : ℕ} [NeZero q]
    (x : Fin n × Bool → ZMod q) (a b : ZMod (q * q)) :
    uniformProb (fun k => nhLast (x, a) k - nhLast (x, b) k = a - b) = 1 := by
  simp only [nhLast_same_hashed_difference]
  simp [uniformProb]

end ProvenHashes.Halftime
