import ProvenHashes.Halftime.StyleBytes
import ProvenHashes.Halftime.Normalization

namespace ProvenHashes.Halftime
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- A public schedule and leaf ordering for n complete Encode2 groups.
All fields are structural. There are no probabilistic premises. The height
budget is supported by the number of leaves; at most 64 roots are live. -/
structure StyleSchedule (n : ℕ) where
  height : ℕ
  roots : ℕ
  shape : Fin roots → TreeShape 8 height
  order : (Σ i, LeafPath (shape i)) ≃ Fin n
  height_le : height ≤ 9
  roots_le : roots ≤ 64
  height_load : n ≠ 0 → 8 ^ height ≤ n

def styleByteLimit (b : ℕ) : ℕ := 144 * b * (19173960 + 1)

abbrev StyleScheduleFamily (b : ℕ) :=
  (bytes : Fin (styleByteLimit b)) → StyleSchedule (styleGroups b bytes.val)

abbrev StyleMessage (b : ℕ) := (bytes : Fin (styleByteLimit b)) × (Fin bytes.val → Byte)

noncomputable def byteStyleCore {b bytes : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plan : StyleSchedule (styleGroups b bytes)) (x : Fin bytes → Byte) (key : LowerTableKey) :
    Fin 2 → Word64 :=
  flatStyleCore hb plan.height_le plan.roots_le (styleTailWords_le hb0)
    plan.shape (parseStyle plan.shape plan.order x) key

theorem byteStyleCore_survival {b bytes : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plan : StyleSchedule (styleGroups b bytes)) (x y : Fin bytes → Byte) (hxy : x ≠ y)
    (target : Fin 2 → Word64) :
    uniformProb (fun key => byteStyleCore hb0 hb plan x key - byteStyleCore hb0 hb plan y key = target) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) plan.height := by
  exact flatStyleCore_survival hb0 hb plan.height_le plan.roots_le (styleTailWords_le hb0)
    plan.shape _ _ (fun he => hxy (parseStyle_injective hb0 _ _ he)) target

theorem byteStyleCore_no_groups {b bytes : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plan : StyleSchedule (styleGroups b bytes)) (hn : styleGroups b bytes = 0)
    (x y : Fin bytes → Byte) (hxy : x ≠ y) (target : Fin 2 → Word64) :
    uniformProb (fun key => byteStyleCore hb0 hb plan x key - byteStyleCore hb0 hb plan y key = target) ≤
      (1 / (2 : ℚ≥0) ^ 32) ^ 2 := by
  have hf : (parseStyle plan.shape plan.order x).1 = (parseStyle plan.shape plan.order y).1 := by
    apply (forestInputEquiv _ plan.shape plan.order).injective
    funext i
    have hi := i.isLt
    omega
  have ht : (parseStyle plan.shape plan.order x).2 ≠ (parseStyle plan.shape plan.order y).2 := by
    intro he
    exact hxy (parseStyle_injective hb0 _ _ (Prod.ext hf he))
  unfold byteStyleCore flatStyleCore
  rw [readStyleKey_uniform hb plan.height_le plan.roots_le (styleTailWords_le hb0)
    (fun key => styleCore plan.shape (parseStyle plan.shape plan.order x) key -
      styleCore plan.shape (parseStyle plan.shape plan.order y) key = target)]
  exact styleCore_different_tail hb0 plan.shape _ _ ht target

theorem byteStyleCore_word_cap {b bytes L : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plan : StyleSchedule (styleGroups b bytes)) (hL : 1 ≤ L) (hbytes : bytes ≤ 8 * L)
    (x y : Fin bytes → Byte) (hxy : x ≠ y) :
    uniformProb (fun key => byteStyleCore hb0 hb plan x key = byteStyleCore hb0 hb plan y key) ≤
      (L : ℚ≥0) / 2 ^ 64 := by
  by_cases hn : styleGroups b bytes = 0
  · have H := byteStyleCore_no_groups hb0 hb plan hn x y hxy 0
    simp only [sub_eq_zero] at H
    apply H.trans
    have hL' : (1 : ℚ≥0) ≤ L := by exact_mod_cast hL
    calc
      _ = (1 : ℚ≥0) / 2 ^ 64 := by norm_num
      _ ≤ _ := div_le_div_of_nonneg_right hL' (zero_le _)
  · have H := byteStyleCore_survival hb0 hb plan x y hxy 0
    simp only [sub_eq_zero] at H
    apply H.trans
    apply styleTwoBound_word_cap plan.height L b hb0
    have hg := Nat.div_mul_le_self bytes (144 * b)
    have hc : 18 * b * styleGroups b bytes ≤ L := by
      unfold styleGroups
      nlinarith
    exact (Nat.mul_le_mul_left (18 * b) (plan.height_load hn)).trans hc

/-- Flat-address Style wrapper: the same lower words are used by the core
and length tables; the sixteen output rows occupy words 2048 through 6143. -/
noncomputable def byteStyleHash {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plans : StyleScheduleFamily b) (x : StyleMessage b) (key : Fin 6144 → XorWord 64) : XorWord 64 :=
  flatStyleWrapper (fun k => signatureBytes (byteStyleCore hb0 hb (plans x.1) x.2 k))
    (lengthBytes x.1.val) key

theorem byteStyleHash_equal_length {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plans : StyleScheduleFamily b) (bytes : Fin (styleByteLimit b))
    (x y : Fin bytes.val → Byte) :
    uniformProb (fun key => byteStyleHash hb0 hb plans ⟨bytes, x⟩ key =
      byteStyleHash hb0 hb plans ⟨bytes, y⟩ key) =
      (1 / (2 : ℚ≥0) ^ 64) + (1 - 1 / (2 : ℚ≥0) ^ 64) *
        uniformProb (fun k => byteStyleCore hb0 hb (plans bytes) x k = byteStyleCore hb0 hb (plans bytes) y k) := by
  unfold byteStyleHash
  rw [flat_wrapper_equal_length]
  simp only [signatureBytes_injective.eq_iff]

theorem styleByteLimit_lt_word (b : ℕ) (hb : b ≤ 8) : styleByteLimit b < 2 ^ 64 := by
  unfold styleByteLimit
  omega

theorem byteStyleHash_unequal_length {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plans : StyleScheduleFamily b) (x y : StyleMessage b) (hlen : x.1 ≠ y.1) :
    uniformProb (fun key => byteStyleHash hb0 hb plans x key = byteStyleHash hb0 hb plans y key) ≤
      1 / (2 : ℚ≥0) ^ 63 - 1 / (2 : ℚ≥0) ^ 128 := by
  have he : lengthBytes x.1.val ≠ lengthBytes y.1.val := by
    intro h
    exact hlen (Fin.ext (lengthBytes_injective_below
      (x.1.isLt.trans (styleByteLimit_lt_word b hb))
      (y.1.isLt.trans (styleByteLimit_lt_word b hb)) h))
  exact (flat_wrapper_unequal_length _ _ _ _ he).trans_eq wrapper_numeric_coefficient

/-- The normalized theorem on byte strings, for every public admissible
forest schedule. Length is a positive cap in eight-byte words. -/
theorem byteStyleHash_normalized {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (plans : StyleScheduleFamily b) (L : ℕ) (hL : 1 ≤ L)
    (x y : StyleMessage b) (hxy : x ≠ y)
    (hx : x.1.val ≤ 8 * L) (hy : y.1.val ≤ 8 * L) :
    uniformProb (fun key => byteStyleHash hb0 hb plans x key = byteStyleHash hb0 hb plans y key) ≤
      (L : ℚ≥0) * (1 / 2 ^ 63 - 1 / 2 ^ 128) := by
  apply flat_wrapper_normalized_from_core L hL _ _ _ _
  intro he
  have hn : x.1 = y.1 := Fin.ext (lengthBytes_injective_below
    (x.1.isLt.trans (styleByteLimit_lt_word b hb))
    (y.1.isLt.trans (styleByteLimit_lt_word b hb)) he)
  rcases x with ⟨nx, x⟩
  rcases y with ⟨ny, y⟩
  dsimp only at hn
  subst ny
  have hdata : x ≠ y := by intro hh; subst y; exact hxy rfl
  have hp : (fun k => signatureBytes (byteStyleCore hb0 hb (plans nx) x k) =
      signatureBytes (byteStyleCore hb0 hb (plans nx) y k)) =
      (fun k => byteStyleCore hb0 hb (plans nx) x k = byteStyleCore hb0 hb (plans nx) y k) := by
    funext k
    exact propext signatureBytes_injective.eq_iff
  change uniformProb (fun k => signatureBytes (byteStyleCore hb0 hb (plans nx) x k) =
    signatureBytes (byteStyleCore hb0 hb (plans nx) y k)) ≤ _
  rw [hp]
  exact byteStyleCore_word_cap hb0 hb (plans nx) hL hx x y hdata

end ProvenHashes.Halftime
