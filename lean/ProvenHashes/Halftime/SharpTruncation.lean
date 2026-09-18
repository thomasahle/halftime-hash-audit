import ProvenHashes.Halftime.Truncation

namespace ProvenHashes.Halftime
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Cancellation of a bounded power of two from an integral product. -/
theorem power_two_cancel (a b : ℕ) (d s : ℤ)
    (hd : ¬ (2 : ℤ) ^ (a + 1) ∣ d) (h : (2 : ℤ) ^ (a + b) ∣ d * s) :
    (2 : ℤ) ^ b ∣ s := by
  by_cases hs : s = 0
  · simp [hs]
  have hd0 : d ≠ 0 := by intro he; exact hd (he ▸ dvd_zero _)
  have hvd : padicValNat 2 d.natAbs ≤ a := by
    have hn : ¬ 2 ^ (a + 1) ∣ d.natAbs := by
      intro hh
      exact hd (by exact_mod_cast Int.natCast_dvd.mpr hh)
    rw [padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hd0)] at hn
    omega
  have hv : a + b ≤ padicValNat 2 d.natAbs + padicValNat 2 s.natAbs := by
    have hn : 2 ^ (a + b) ∣ (d * s).natAbs := by
      apply Int.natCast_dvd.mp
      exact_mod_cast h
    rw [Int.natAbs_mul, padicValNat_dvd_iff_le
      (mul_ne_zero (Int.natAbs_ne_zero.mpr hd0) (Int.natAbs_ne_zero.mpr hs)),
      padicValNat.mul (Int.natAbs_ne_zero.mpr hd0) (Int.natAbs_ne_zero.mpr hs)] at hn
    exact hn
  have hn : 2 ^ b ∣ s.natAbs :=
    (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hs)).mpr (by omega)
  exact_mod_cast Int.natCast_dvd.mpr hn

def pair62 (c c' d k : ZMod (2 ^ 32)) : ZMod (2 ^ 62) :=
  (c.val : ZMod (2 ^ 62)) * k.val - (c'.val : ZMod (2 ^ 62)) * (k + d).val

theorem pair62_divisibility (c c' d u v : ZMod (2 ^ 32))
    (he : pair62 c c' d u = pair62 c c' d v)
    (hw : ((v + d).val : ℤ) - (u + d).val = (v.val : ℤ) - u.val) :
    (2 : ℤ) ^ 62 ∣ ((c.val : ℤ) - c'.val) * ((v.val : ℤ) - u.val) := by
  have he' : (((c.val : ℤ) * u.val - (c'.val : ℤ) * (u + d).val : ℤ) : ZMod (2 ^ 62)) =
      (((c.val : ℤ) * v.val - (c'.val : ℤ) * (v + d).val : ℤ) : ZMod (2 ^ 62)) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, pair62] using he
  have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (2 ^ 62)).mp he'
  have hh' : (2 : ℤ) ^ 62 ∣
      (c.val : ℤ) * ((v.val : ℤ) - u.val) -
        (c'.val : ℤ) * (((v + d).val : ℤ) - (u + d).val) := by
    convert hh using 1
    push_cast
    ring
  rw [hw] at hh'
  convert hh' using 1; ring

theorem pair62_regular (c c' d : ZMod (2 ^ 32))
    (hc : ¬ (2 : ℤ) ^ 31 ∣ (c.val : ℤ) - c'.val) (t : ZMod (2 ^ 62)) :
    uniformProb (fun k => pair62 c c' d k = t) ≤ 2 / (2 : ℚ≥0) ^ 32 := by
  classical
  let tag (u : ZMod (2 ^ 32)) : Bool := decide (u.val + d.val < 2 ^ 32)
  have htag : ∀ u v, tag u = tag v → pair62 c c' d u = pair62 c c' d v → u = v := by
    intro u v ht he
    have hw : ((v + d).val : ℤ) - (u + d).val = (v.val : ℤ) - u.val := by
      have ht' : (u.val + d.val < 2 ^ 32) ↔ (v.val + d.val < 2 ^ 32) := by
        simpa only [tag, decide_eq_decide] using ht
      by_cases hu : u.val + d.val < 2 ^ 32
      · rw [ZMod.val_add_of_lt hu, ZMod.val_add_of_lt (ht'.mp hu)]
        omega
      · rw [ZMod.val_add_of_le (by omega : 2 ^ 32 ≤ u.val + d.val),
          ZMod.val_add_of_le (by omega : 2 ^ 32 ≤ v.val + d.val)]
        have := u.val_lt; have := v.val_lt; have := d.val_lt
        omega
    have hdvd := power_two_cancel 30 32 _ _ hc (pair62_divisibility c c' d u v he hw)
    have hz : (v.val : ℤ) - u.val = 0 := small_dvd (by norm_num : (0 : ℤ) < 2 ^ 32)
      (by have := u.val_lt; have := v.val_lt; constructor <;> omega) hdvd
    apply ZMod.val_injective
    omega
  simpa only [Fintype.card_bool, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using
    uniformProb_of_tag_injective (pair62 c c' d) tag htag t

/-- When the other half changes only in its top bit, splitting the exposed
key into two half-intervals also gives at most two solutions. -/
theorem pair62_high (c c' d : ZMod (2 ^ 32)) (hc : c ≠ c')
    (hd : d.val = 0 ∨ d.val = 2 ^ 31) (t : ZMod (2 ^ 62)) :
    uniformProb (fun k => pair62 c c' d k = t) ≤ 2 / (2 : ℚ≥0) ^ 32 := by
  classical
  let tag (u : ZMod (2 ^ 32)) : Bool := decide (u.val < 2 ^ 31)
  have htag : ∀ u v, tag u = tag v → pair62 c c' d u = pair62 c c' d v → u = v := by
    intro u v ht he
    have ht' : (u.val < 2 ^ 31) ↔ (v.val < 2 ^ 31) := by
      simpa only [tag, decide_eq_decide] using ht
    have hu := u.val_lt
    have hv := v.val_lt
    have hw : ((v + d).val : ℤ) - (u + d).val = (v.val : ℤ) - u.val := by
      rcases hd with hd | hd
      · rw [ZMod.val_add_of_lt (by omega : u.val + d.val < 2 ^ 32),
          ZMod.val_add_of_lt (by omega : v.val + d.val < 2 ^ 32)]
        omega
      · by_cases hup : u.val < 2 ^ 31
        · rw [ZMod.val_add_of_lt (by omega : u.val + d.val < 2 ^ 32),
            ZMod.val_add_of_lt (by omega : v.val + d.val < 2 ^ 32)]
          omega
        · rw [ZMod.val_add_of_le (by omega : 2 ^ 32 ≤ u.val + d.val),
            ZMod.val_add_of_le (by omega : 2 ^ 32 ≤ v.val + d.val)]
          omega
    have hc' : ¬ (2 : ℤ) ^ 32 ∣ (c.val : ℤ) - c'.val := by
      intro h
      have hz := small_dvd (by norm_num : (0 : ℤ) < 2 ^ 32)
        (show -(2 : ℤ) ^ 32 < (c.val : ℤ) - c'.val ∧ (c.val : ℤ) - c'.val < 2 ^ 32 by
          have := c.val_lt; have := c'.val_lt; constructor <;> omega) h
      exact hc (ZMod.val_injective _ (by omega))
    have hdvd := power_two_cancel 31 31 _ _ hc' (pair62_divisibility c c' d u v he hw)
    have hz : (v.val : ℤ) - u.val = 0 := small_dvd (by norm_num : (0 : ℤ) < 2 ^ 31)
      (by constructor <;> omega) hdvd
    apply ZMod.val_injective
    omega
  simpa only [Fintype.card_bool, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using
    uniformProb_of_tag_injective (pair62 c c' d) tag htag t

def halfLow : ZMod (2 ^ 32) →+* ZMod (2 ^ 31) :=
  ZMod.castHom (pow_dvd_pow 2 (by decide : 31 ≤ 32)) _

theorem halfLow_val (c : ZMod (2 ^ 32)) : halfLow c = (c.val : ZMod (2 ^ 31)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

theorem halfLow_eq_iff (c c' : ZMod (2 ^ 32)) :
    halfLow c = halfLow c' ↔ (2 : ℤ) ^ 31 ∣ (c.val : ℤ) - c'.val := by
  rw [halfLow_val, halfLow_val]
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (c'.val : ℤ) (c.val : ℤ) (2 ^ 31)
  simpa only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, eq_comm] using h

theorem pair62_add_bound (c c' a b : ZMod (2 ^ 32))
    (hc : c ≠ c') (hh : halfLow c ≠ halfLow c' ∨ halfLow a = halfLow b)
    (t : ZMod (2 ^ 62)) :
    uniformProb (fun k : ZMod (2 ^ 32) =>
      (c.val : ZMod (2 ^ 62)) * ((a + k).val : ZMod (2 ^ 62)) -
        (c'.val : ZMod (2 ^ 62)) * ((b + k).val : ZMod (2 ^ 62)) = t) ≤
      2 / (2 : ℚ≥0) ^ 32 := by
  have he : (fun k : ZMod (2 ^ 32) =>
      (c.val : ZMod (2 ^ 62)) * ((a + k).val : ZMod (2 ^ 62)) -
        (c'.val : ZMod (2 ^ 62)) * ((b + k).val : ZMod (2 ^ 62)) = t) =
      (fun k => pair62 c c' (b - a) (a + k) = t) := by
    funext k
    simp only [pair62, show a + k + (b - a) = b + k by ring]
  rw [he]
  have hprob := uniformProb_equiv (Equiv.addLeft a) (fun k => pair62 c c' (b - a) k = t)
  change uniformProb (fun k => pair62 c c' (b - a) (a + k) = t) = _ at hprob
  rw [hprob]
  rcases hh with hh | hh
  · exact pair62_regular c c' (b - a) (fun h => hh ((halfLow_eq_iff c c').mpr h)) t
  · have hv : (2 ^ 31 : ℕ) ∣ (b - a).val := by
      have hz : halfLow (b - a) = 0 := by rw [map_sub, hh, sub_self]
      rw [halfLow_val, ZMod.natCast_eq_zero_iff] at hz
      exact hz
    have hd : (b - a).val = 0 ∨ (b - a).val = 2 ^ 31 := by
      obtain ⟨z, hz⟩ := hv
      have := (b - a).val_lt
      omega
    exact pair62_high c c' (b - a) hc hd t

theorem nh_mod62_coordinate {n : ℕ}
    (x y : Fin n × Bool → ZMod (2 ^ 32)) (i : Fin n) (b : Bool)
    (hi : x (i, b) ≠ y (i, b))
    (hh : halfLow (x (i, b)) ≠ halfLow (y (i, b)) ∨
      halfLow (x (i, !b)) = halfLow (y (i, !b))) (c : ZMod (2 ^ 62)) :
    uniformProb (fun k => lowBits 62 (by decide) (nh32 x k - nh32 y k) = c) ≤
      2 / (2 : ℚ≥0) ^ 32 := by
  classical
  apply uniformProb_of_update_bound _ (i, !b)
  intro k
  let F (v : ZMod (2 ^ 32)) :=
    lowBits 62 (by decide) (nh32 x (Function.update k (i, !b) v) -
      nh32 y (Function.update k (i, !b) v))
  let G (v : ZMod (2 ^ 32)) : ZMod (2 ^ 62) :=
    ((x (i, b) + k (i, b)).val : ZMod (2 ^ 62)) * (x (i, !b) + v).val -
      ((y (i, b) + k (i, b)).val : ZMod (2 ^ 62)) * (y (i, !b) + v).val
  let offset := F 0 - G 0
  have he (v : ZMod (2 ^ 32)) : F v = G v + offset := by
    dsimp [F, G, offset]
    cases b <;> simp only [Bool.not_false, Bool.not_true, nh32, nh_update_true,
      nh_update_false, map_sub, map_add, map_mul, map_natCast] <;> ring
  have hh' : halfLow (x (i, b) + k (i, b)) ≠ halfLow (y (i, b) + k (i, b)) ∨
      halfLow (x (i, !b)) = halfLow (y (i, !b)) := by
    rcases hh with hh | hh
    · left
      intro he
      rw [map_add, map_add] at he
      exact hh (add_right_cancel he)
    · exact Or.inr hh
  have H := pair62_add_bound (x (i, b) + k (i, b)) (y (i, b) + k (i, b))
    (x (i, !b)) (y (i, !b)) (by simpa using hi) hh' (c - offset)
  change uniformProb (fun v => F v = c) ≤ _
  have hevent : (fun v => F v = c) = (fun v => G v = c - offset) := by
    funext v
    rw [he]
    exact propext eq_sub_iff_add_eq.symm
  rw [hevent]
  exact H

/-- Sharp fourth-review truncation statement. All half-word keys are uniform
and independent; the target is arbitrary, and messages are distinct with the
same number of pairs. This costs two keys, not four lifted output atoms. -/
theorem nh_mod62_adu {n : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (c : ZMod (2 ^ 62)) :
    uniformProb (fun k => lowBits 62 (by decide) (nh32 x k - nh32 y k) = c) ≤
      2 / (2 : ℚ≥0) ^ 32 := by
  classical
  by_cases hl : ∃ j, halfLow (x j) ≠ halfLow (y j)
  · obtain ⟨⟨i, b⟩, hj⟩ := hl
    exact nh_mod62_coordinate x y i b (fun he => hj (congrArg halfLow he)) (Or.inl hj) c
  · obtain ⟨⟨i, b⟩, hj⟩ := Function.ne_iff.mp hxy
    have ha : ∀ j, halfLow (x j) = halfLow (y j) := by simpa using hl
    exact nh_mod62_coordinate x y i b hj (Or.inr (ha (i, !b))) c

theorem truncatedNH62Bound : TruncatedNH62Bound := fun _ x y hxy c => nh_mod62_adu x y hxy c

end ProvenHashes.Halftime
