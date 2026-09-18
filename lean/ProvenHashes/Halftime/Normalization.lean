import ProvenHashes.Halftime.Survival

namespace ProvenHashes.Halftime
set_option maxHeartbeats 500000

theorem style_height_coefficient (h : ℕ) : (h + 2) * (h + 3) ≤ 18 * 8 ^ h := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [pow_succ]
    have hg : (h + 1 + 2) * (h + 1 + 3) ≤ 8 * ((h + 2) * (h + 3)) := by nlinarith
    nlinarith

/-- One full height-h subtree requires at least 8^h leaves, and each leaf
contains 18b words. This converts the sharp bound into the word-cap bound. -/
theorem styleTwoBound_word_cap (h L b : ℕ) (hb : 0 < b) (hL : 18 * b * 8 ^ h ≤ L) :
    styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h ≤ (L : ℚ≥0) / 2 ^ 64 := by
  have hc : (h + 2) * (h + 3) ≤ L := by
    have hg := style_height_coefficient h
    have hmul : 18 * 8 ^ h ≤ 18 * b * 8 ^ h := by gcongr; omega
    exact hg.trans (hmul.trans hL)
  calc
    _ ≤ ((h : ℚ≥0) + 2) * ((h : ℚ≥0) + 3) * (1 / (2 : ℚ≥0) ^ 32) ^ 2 :=
      styleTwoBound_le _ h
    _ = (((h + 2) * (h + 3) : ℕ) : ℚ≥0) / 2 ^ 64 := by push_cast; norm_num; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hc) (zero_le _)

theorem style_log_height_word_cap (n L b : ℕ) (hb : 0 < b) (hn : n ≠ 0)
    (hL : 18 * b * n ≤ L) :
    styleTwoBound (1 / (2 : ℚ≥0) ^ 32) (Nat.log 8 n) ≤ (L : ℚ≥0) / 2 ^ 64 := by
  apply styleTwoBound_word_cap _ _ b hb
  exact (Nat.mul_le_mul_left _ (Nat.pow_log_le_self 8 hn)).trans hL

/-- The exact public coefficient, with both equal and unequal lengths handled.
This helper accepts a core bound; the concrete construction discharges it. -/
theorem flat_wrapper_word_cap (L : ℕ) (hL : 1 ≤ L)
    (x y : LowerTableKey → Fin 16 → Fin 256)
    (lx ly : Fin 8 → Fin 256)
    (hcore : lx = ly → uniformProb (fun k => x k = y k) ≤ (L : ℚ≥0) / 2 ^ 64) :
    uniformProb (fun key => flatStyleWrapper x lx key = flatStyleWrapper y ly key) ≤
      (L : ℚ≥0) * (1 / 2 ^ 63 - 1 / 2 ^ 128) :=
  flat_wrapper_normalized_from_core L hL x y lx ly hcore

end ProvenHashes.Halftime
