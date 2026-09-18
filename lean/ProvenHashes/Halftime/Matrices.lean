import Mathlib

namespace ProvenHashes.Halftime
open scoped Matrix BigOperators
set_option maxRecDepth 4000
set_option maxHeartbeats 400000

def T2 : Matrix (Fin 2) (Fin 7) ℤ :=
  !![1, 0, 1, 1, 2, 1, 4; 0, 1, 1, 2, 1, 4, 1]

def T3 : Matrix (Fin 3) (Fin 9) ℤ :=
  !![0, 0, 1, 4, 1, 1, 2, 2, 1;
     1, 1, 0, 0, 1, 4, 1, 2, 2;
     1, 4, 1, 1, 0, 0, 2, 1, 2]

def det2 {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℤ)
    (r s : Fin m) (a b : Fin n) : ℤ := T r a * T s b - T r b * T s a

def det3 (T : Matrix (Fin 3) (Fin 9) ℤ) (a b c : Fin 9) : ℤ :=
  T 0 a * T 1 b * T 2 c + T 0 b * T 1 c * T 2 a + T 0 c * T 1 a * T 2 b -
  T 0 c * T 1 b * T 2 a - T 0 b * T 1 a * T 2 c - T 0 a * T 1 c * T 2 b

theorem det2_eq_det {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℤ)
    (r s : Fin m) (a b : Fin n) :
    det2 T r s a b = (T.submatrix ![r, s] ![a, b]).det := by
  simp [det2, Matrix.det_fin_two, Matrix.submatrix]

theorem det3_eq_det (T : Matrix (Fin 3) (Fin 9) ℤ) (a b c : Fin 9) :
    det3 T a b c = (T.submatrix id ![a, b, c]).det := by
  simp [det3, Matrix.det_fin_three, Matrix.submatrix]
  ring

/-- All 21 increasing two-column choices are nonsingular, with v₂(det) ≤ 2. -/
theorem T2_minors : ∀ a b : Fin 7, a < b →
    det2 T2 0 1 a b ≠ 0 ∧ ¬ (8 : ℤ) ∣ det2 T2 0 1 a b := by decide

/-- All 84 increasing three-column choices are nonsingular, with v₂(det) ≤ 2. -/
theorem T3_minors : ∀ a b c : Fin 9, a < b → b < c →
    det3 T3 a b c ≠ 0 ∧ ¬ (8 : ℤ) ∣ det3 T3 a b c := by decide

theorem T2_worst_minor : det2 T2 0 1 0 5 = 4 := by decide
theorem T3_worst_minor : det3 T3 0 1 3 = 12 := by decide

theorem valuation_le_two {d : ℤ} (hd : d ≠ 0) (h8 : ¬ (8 : ℤ) ∣ d) :
    padicValNat 2 d.natAbs ≤ 2 := by
  have hn : ¬ (2 ^ 3 : ℕ) ∣ d.natAbs := by
    intro h
    exact h8 (by simpa using Int.natCast_dvd.mpr h)
  rw [padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hd)] at hn
  omega

theorem T2_distinct_minors : ∀ a b : Fin 7, a ≠ b →
    det2 T2 0 1 a b ≠ 0 ∧ ¬ (8 : ℤ) ∣ det2 T2 0 1 a b := by decide

theorem T3_distinct_minors : ∀ a b c : Fin 9, a ≠ b → a ≠ c → b ≠ c →
    det3 T3 a b c ≠ 0 ∧ ¬ (8 : ℤ) ∣ det3 T3 a b c := by decide

theorem T2_minor_valuations (j : Fin 2 ↪ Fin 7) :
    (T2.submatrix id j).det ≠ 0 ∧ padicValNat 2 (T2.submatrix id j).det.natAbs ≤ 2 := by
  have he : (T2.submatrix id j).det = det2 T2 0 1 (j 0) (j 1) := by
    simp [Matrix.det_fin_two, Matrix.submatrix, det2]
  rw [he]
  have h := T2_distinct_minors (j 0) (j 1) (fun h => by have := j.injective h; norm_num at this)
  exact ⟨h.1, valuation_le_two h.1 h.2⟩

theorem T3_minor_valuations (j : Fin 3 ↪ Fin 9) :
    (T3.submatrix id j).det ≠ 0 ∧ padicValNat 2 (T3.submatrix id j).det.natAbs ≤ 2 := by
  have he : (T3.submatrix id j).det = det3 T3 (j 0) (j 1) (j 2) := by
    simp [Matrix.det_fin_three, Matrix.submatrix, det3]
    ring
  rw [he]
  have h := T3_distinct_minors (j 0) (j 1) (j 2)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (j.injective h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (j.injective h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (j.injective h))
  exact ⟨h.1, valuation_le_two h.1 h.2⟩

/-- For a scalar map modulo 2^64 this is its exact kernel cardinality. Zero
minors receive 2^64, so taking a minimum never selects zero when a cheaper
nonzero minor is available. -/
def weight (d : ℤ) : ℕ := Nat.gcd d.natAbs (2 ^ 64)

def singleton2 (r : Fin 2) (a b : Fin 7) : ℕ := min (weight (T2 r a)) (weight (T2 r b))
def full2 (a b : Fin 7) : ℕ := weight (det2 T2 0 1 a b)
def singleton3 (r : Fin 3) (a b c : Fin 9) : ℕ :=
  min (weight (T3 r a)) (min (weight (T3 r b)) (weight (T3 r c)))
def pair3 (r s : Fin 3) (a b c : Fin 9) : ℕ :=
  min (weight (det2 T3 r s a b))
    (min (weight (det2 T3 r s a c)) (weight (det2 T3 r s b c)))
def full3 (a b c : Fin 9) : ℕ := weight (det3 T3 a b c)

theorem T2_projection_coefficients : ∀ a b : Fin 7, a < b →
    singleton2 0 a b + singleton2 1 a b ≤ 5 ∧ full2 a b ≤ 4 := by decide

theorem T3_projection_coefficients : ∀ a b c : Fin 9, a < b → b < c →
    singleton3 0 a b c + singleton3 1 a b c + singleton3 2 a b c ≤ 6 ∧
    pair3 0 1 a b c + pair3 0 2 a b c + pair3 1 2 a b c ≤ 9 ∧
    full3 a b c ≤ 4 := by decide

/-- Expansion of Σ_S c_{S,F} u^(2-|S|) v^|S|, with c_empty=1 and the
minimum scalar/square-minor weight on each nonempty row subset. -/
def projection2 (a b : Fin 7) (u v : ℚ≥0) : ℚ≥0 :=
  u ^ 2 + (singleton2 0 a b + singleton2 1 a b : ℕ) * u * v + full2 a b * v ^ 2

/-- The analogous expansion for the eight subsets of the three output rows. -/
def projection3 (a b c : Fin 9) (u v : ℚ≥0) : ℚ≥0 :=
  u ^ 3 + (singleton3 0 a b c + singleton3 1 a b c + singleton3 2 a b c : ℕ) * u ^ 2 * v +
    (pair3 0 1 a b c + pair3 0 2 a b c + pair3 1 2 a b c : ℕ) * u * v ^ 2 +
    full3 a b c * v ^ 3

theorem projection2_le (a b : Fin 7) (hab : a < b) (u v : ℚ≥0) :
    projection2 a b u v ≤ (u + v) ^ (2 - 1) * (u + 2 ^ 2 * v) := by
  obtain ⟨h1, h2⟩ := T2_projection_coefficients a b hab
  calc
    _ ≤ u ^ 2 + 5 * u * v + 4 * v ^ 2 := by
      unfold projection2
      gcongr <;> exact_mod_cast ‹_›
    _ = _ := by ring

theorem projection3_le (a b c : Fin 9) (hab : a < b) (hbc : b < c) (u v : ℚ≥0) :
    projection3 a b c u v ≤ (u + v) ^ (3 - 1) * (u + 2 ^ 2 * v) := by
  obtain ⟨h1, h2, h3⟩ := T3_projection_coefficients a b c hab hbc
  calc
    _ ≤ u ^ 3 + 6 * u ^ 2 * v + 9 * u * v ^ 2 + 4 * v ^ 3 := by
      unfold projection3
      gcongr <;> exact_mod_cast ‹_›
    _ = _ := by ring

def coefficient2 (a b : Fin 7) (S : Finset (Fin 2)) : ℕ :=
  if 0 ∈ S then if 1 ∈ S then full2 a b else singleton2 0 a b
  else if 1 ∈ S then singleton2 1 a b else 1

def coefficient3 (a b c : Fin 9) (S : Finset (Fin 3)) : ℕ :=
  if 0 ∈ S then
    if 1 ∈ S then if 2 ∈ S then full3 a b c else pair3 0 1 a b c
    else if 2 ∈ S then pair3 0 2 a b c else singleton3 0 a b c
  else if 1 ∈ S then if 2 ∈ S then pair3 1 2 a b c else singleton3 1 a b c
  else if 2 ∈ S then singleton3 2 a b c else 1

theorem projection2_subset_sum (a b : Fin 7) (u v : ℚ≥0) :
    (∑ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      (coefficient2 a b S : ℚ≥0) * u ^ (2 - S.card) * v ^ S.card) = projection2 a b u v := by
  have hu : (Finset.univ : Finset (Fin 2)).powerset =
      Finset.cons ∅ (Finset.cons {0} (Finset.cons {1} {{0, 1}} (by decide)) (by decide)) (by decide) := by decide
  rw [hu]
  simp only [Finset.sum_cons, Finset.sum_singleton]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  simp [coefficient2, projection2, h01, Ne.symm h01]
  ring

theorem projection3_subset_sum (a b c : Fin 9) (u v : ℚ≥0) :
    (∑ S ∈ (Finset.univ : Finset (Fin 3)).powerset,
      (coefficient3 a b c S : ℚ≥0) * u ^ (3 - S.card) * v ^ S.card) = projection3 a b c u v := by
  have hu : (Finset.univ : Finset (Fin 3)).powerset =
      Finset.cons ∅ (Finset.cons {0} (Finset.cons {1} (Finset.cons {2}
        (Finset.cons {0, 1} (Finset.cons {0, 2} (Finset.cons {1, 2} {{0, 1, 2}}
          (by decide)) (by decide)) (by decide)) (by decide)) (by decide)) (by decide)) (by decide) := by decide
  rw [hu]
  simp only [Finset.sum_cons, Finset.sum_singleton]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  simp [coefficient3, projection3, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12]
  ring

theorem projection_polynomial_T2 (a b : Fin 7) (hab : a < b) (u v : ℚ≥0) :
    (∑ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      (coefficient2 a b S : ℚ≥0) * u ^ (2 - S.card) * v ^ S.card) ≤
      (u + v) ^ (2 - 1) * (u + 2 ^ 2 * v) := by
  rw [projection2_subset_sum]
  exact projection2_le a b hab u v

theorem projection_polynomial_T3 (a b c : Fin 9) (hab : a < b) (hbc : b < c) (u v : ℚ≥0) :
    (∑ S ∈ (Finset.univ : Finset (Fin 3)).powerset,
      (coefficient3 a b c S : ℚ≥0) * u ^ (3 - S.card) * v ^ S.card) ≤
      (u + v) ^ (3 - 1) * (u + 2 ^ 2 * v) := by
  rw [projection3_subset_sum]
  exact projection3_le a b c hab hbc u v

end ProvenHashes.Halftime
