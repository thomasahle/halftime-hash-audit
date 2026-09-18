import ProvenHashes.Halftime.IntegerNH
import ProvenHashes.Halftime.MatrixFibre

namespace ProvenHashes.Halftime
set_option maxHeartbeats 500000

/-- Exact cardinality of the fibres of reduction modulo a divisor. -/
theorem zmod_projection_fibre_card (M B : ℕ) [NeZero M] [NeZero B] (c : ZMod M) :
    Nat.card {x : ZMod (M * B) // ZMod.castHom (dvd_mul_right M B) (ZMod M) x = c} = B := by
  let f := ZMod.castHom (dvd_mul_right M B) (ZMod M)
  have hker (x : ZMod (M * B)) : f x = 0 ↔ (B : ZMod (M * B)) * x = 0 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    conv_rhs => rw [← ZMod.natCast_zmod_val x]
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    conv_rhs => lhs; rw [mul_comm]
    exact (mul_dvd_mul_iff_left (NeZero.ne B)).symm
  have e := Equiv.subtypeEquivRight hker
  calc
    _ = Nat.card {x : ZMod (M * B) // f x = 0} :=
      fibre_card_eq_kernel f.toAddMonoidHom c (ZMod.castHom_surjective (dvd_mul_right M B) c)
    _ = Nat.card {x : ZMod (M * B) // (B : ZMod (M * B)) * x = 0} := Nat.card_congr e
    _ = Nat.gcd B (M * B) := scalar_kernel_card_nat _ _
    _ = B := Nat.gcd_eq_left (dvd_mul_left B M)

def lowBits (bits : ℕ) (hb : bits ≤ 64) : ZMod (2 ^ 64) →+* ZMod (2 ^ bits) :=
  ZMod.castHom (pow_dvd_pow 2 hb) _

/-- Direct residue statement for every target in the smaller output ring. -/
theorem nh_lowBits_atom_bound {n bits : ℕ} (hb : bits ≤ 64)
    (x y : Fin n × Bool → ZMod (2 ^ 32)) (hxy : x ≠ y) (c : ZMod (2 ^ bits))
    (hcard : Nat.card {v : ZMod (2 ^ 64) // lowBits bits hb v = c} ≤ 2 ^ (64 - bits)) :
    uniformProb (fun k => lowBits bits hb (nh32 x k - nh32 y k) = c) ≤
      (2 : ℚ≥0) ^ (64 - bits) / 2 ^ 32 := by
  classical
  have h := uniformProb_preimage_le (fun k => nh32 x k - nh32 y k)
    (fun v => lowBits bits hb v = c) (1 / (2 : ℚ≥0) ^ 32) (nh32_adu x y hxy)
  calc
    _ ≤ _ := h
    _ ≤ (2 : ℚ≥0) ^ (64 - bits) * (1 / 2 ^ 32) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = _ := by ring

theorem nh_mod63_adu {n : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (c : ZMod (2 ^ 63)) :
    uniformProb (fun k => lowBits 63 (by decide) (nh32 x k - nh32 y k) = c) ≤
      2 / (2 : ℚ≥0) ^ 32 := by
  apply (nh_lowBits_atom_bound (by decide : 63 ≤ 64) x y hxy c _).trans_eq
  · norm_num
  · exact (zmod_projection_fibre_card (2 ^ 63) 2 c).le

/-- This is only the generic four-atom consequence. It is deliberately named
`coarse`; it is not the fourth review's stronger two-atom result. -/
theorem nh_mod62_coarse {n : ℕ} (x y : Fin n × Bool → ZMod (2 ^ 32))
    (hxy : x ≠ y) (c : ZMod (2 ^ 62)) :
    uniformProb (fun k => lowBits 62 (by decide) (nh32 x k - nh32 y k) = c) ≤
      4 / (2 : ℚ≥0) ^ 32 := by
  apply (nh_lowBits_atom_bound (by decide : 62 ≤ 64) x y hxy c _).trans_eq
  · norm_num
  · exact (zmod_projection_fibre_card (2 ^ 62) 4 c).le

/-- The exact M1 truncation proposition, proved by `truncatedNH62Bound` in
`SharpTruncation`. Messages have equal pair count, are distinct, and all
32-bit half-word key entries are independent uniform. -/
def TruncatedNH62Bound : Prop :=
  ∀ (n : ℕ) (x y : Fin n × Bool → ZMod (2 ^ 32)), x ≠ y →
    ∀ c : ZMod (2 ^ 62),
      uniformProb (fun k => lowBits 62 (by decide) (nh32 x k - nh32 y k) = c) ≤
        2 / (2 : ℚ≥0) ^ 32

end ProvenHashes.Halftime
