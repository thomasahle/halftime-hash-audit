import ProvenHashes.Halftime.EndToEnd
import ProvenHashes.Tabulation

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem uniformProb_complement_add {K : Type*} [Fintype K] [Nonempty K]
    (E : K → Prop) :
    uniformProb (fun k => ¬ E k) + uniformProb E = 1 := by
  classical
  rw [← mean_indicator, ← mean_indicator, ← mean_add]
  have he : (fun k => indicator (fun k => ¬ E k) k + indicator E k) =
      (fun _ : K => 1) := by
    funext k
    by_cases h : E k <;> simp [indicator, h]
  rw [he, mean_const]

/-- The lower keys may affect both the core signature and the length term.
Only the output tables are sampled independently of those lower keys. -/
def wrappedHash {K I A G : Type*} [Fintype I] [AddCommGroup G]
    (core : K → I → A) (lengthTerm : K → G) (k : K × (I × A → G)) : G :=
  lengthTerm k.1 + tabulationHash (core k.1) k.2

/-- Exact conditioning identity, including arbitrary core/length dependence. -/
theorem wrapper_conditioning {K I A G : Type*}
    [Fintype K] [Nonempty K] [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [AddCommGroup G] [Fintype G]
    (x y : K → I → A) (l l' : K → G) :
    uniformProb (fun k => wrappedHash x l k = wrappedHash y l' k) =
      (1 / Fintype.card G : ℚ≥0) * uniformProb (fun k => x k ≠ y k) +
        uniformProb (fun k => x k = y k ∧ l k = l' k) := by
  classical
  rw [uniformProb_prod]
  change mean (fun k => uniformProb (fun t =>
    l k + tabulationHash (x k) t = l' k + tabulationHash (y k) t)) = _
  rw [← mean_indicator, ← mean_indicator, ← mean_mul, ← mean_add]
  congr 1
  funext k
  by_cases h : x k = y k
  · simp [h, indicator, uniformProb_const]
  · have ht := tabulation_difference_uniform (x k) (y k) h (l' k - l k)
    have he : (fun t : I × A → G =>
        l k + tabulationHash (x k) t = l' k + tabulationHash (y k) t) =
        (fun t => tabulationHash (x k) t - tabulationHash (y k) t = l' k - l k) := by
      funext t
      apply propext
      simp only [sub_eq_sub_iff_add_eq_add, add_comm]
    rw [he, ht]
    simp [indicator, h]

theorem reciprocal_card_le_one {G : Type*} [Fintype G] [Nonempty G] :
    (1 / Fintype.card G : ℚ≥0) ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)
  · positivity

/-- Equal lengths make their overlapping length-table terms cancel exactly. -/
theorem wrapper_equal_length {K I A G : Type*}
    [Fintype K] [Nonempty K] [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [AddCommGroup G] [Fintype G]
    (x y : K → I → A) (l : K → G) :
    uniformProb (fun k => wrappedHash x l k = wrappedHash y l k) =
      (1 / Fintype.card G : ℚ≥0) +
        (1 - 1 / Fintype.card G) * uniformProb (fun k => x k = y k) := by
  rw [wrapper_conditioning]
  simp only [and_true]
  have hp := uniformProb_complement_add (fun k => x k = y k)
  have hd := add_tsub_cancel_of_le (reciprocal_card_le_one (G := G))
  have hp' := congrArg (fun z => (1 / Fintype.card G : ℚ≥0) * z) hp
  have hd' := congrArg (fun z => z * uniformProb (fun k => x k = y k)) hd
  simp only [mul_add, add_mul, mul_one, one_mul] at hp' hd'
  conv_lhs => rw [← hd']
  rw [← add_assoc, hp']

/-- Unequal lengths require only the marginal probability of equal length
table values. No independence between that event and core equality is used. -/
theorem wrapper_unequal_length {K I A G : Type*}
    [Fintype K] [Nonempty K] [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [AddCommGroup G] [Fintype G]
    (x y : K → I → A) (l l' : K → G)
    (hl : uniformProb (fun k => l k = l' k) ≤ (1 / Fintype.card G : ℚ≥0)) :
    uniformProb (fun k => wrappedHash x l k = wrappedHash y l' k) ≤
      (1 / Fintype.card G : ℚ≥0) +
        (1 - 1 / Fintype.card G) * (1 / Fintype.card G) := by
  rw [wrapper_conditioning]
  have hp := uniformProb_complement_add (fun k => x k = y k)
  have hc : uniformProb (fun k => x k = y k ∧ l k = l' k) ≤
      uniformProb (fun k => x k = y k) := uniformProb_mono (fun _ h => h.1)
  have hlc : uniformProb (fun k => x k = y k ∧ l k = l' k) ≤
      (1 / Fintype.card G : ℚ≥0) :=
    (uniformProb_mono (fun _ h => h.2)).trans hl
  have hd := add_tsub_cancel_of_le (reciprocal_card_le_one (G := G))
  have hp' := congrArg (fun z => (1 / Fintype.card G : ℚ≥0) * z) hp
  have hd' := congrArg (fun z => z * uniformProb (fun k => x k = y k ∧ l k = l' k)) hd
  have hc' := mul_le_mul_of_nonneg_left hc (zero_le (1 / Fintype.card G : ℚ≥0))
  have hlc' := mul_le_mul_of_nonneg_left hlc (zero_le (1 - 1 / Fintype.card G : ℚ≥0))
  simp only [mul_add, add_mul, mul_one, one_mul] at hp' hd'
  calc
    _ = (1 / Fintype.card G : ℚ≥0) * uniformProb (fun k => x k ≠ y k) +
        ((1 / Fintype.card G : ℚ≥0) * uniformProb (fun k => x k = y k ∧ l k = l' k) +
          (1 - 1 / Fintype.card G) * uniformProb (fun k => x k = y k ∧ l k = l' k)) := by rw [hd']
    _ ≤ (1 / Fintype.card G : ℚ≥0) * uniformProb (fun k => x k ≠ y k) +
        ((1 / Fintype.card G : ℚ≥0) * uniformProb (fun k => x k = y k) +
          (1 - 1 / Fintype.card G) * uniformProb (fun k => x k = y k ∧ l k = l' k)) := by gcongr
    _ = (1 / Fintype.card G : ℚ≥0) +
          (1 - 1 / Fintype.card G) * uniformProb (fun k => x k = y k ∧ l k = l' k) := by
      rw [← add_assoc, hp']
    _ ≤ _ := add_le_add_left hlc' _

/-- The flat address partition used by the shipped Style wrappers: eight
length-byte rows followed by sixteen output-byte rows, 256 words per row. -/
def flatTableIndex : ((Fin 8 × Fin 256) ⊕ (Fin 16 × Fin 256)) ≃ Fin 6144 :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

def flatKeyEquiv (G : Type*) : (Fin 6144 → G) ≃
    ((Fin 8 × Fin 256 → G) × (Fin 16 × Fin 256 → G)) :=
  (Equiv.arrowCongr flatTableIndex.symm (Equiv.refl G)).trans
    (Equiv.sumArrowEquivProdArrow _ _ G)

theorem flat_length_address (j : Fin 8) (a : Fin 256) :
    (flatTableIndex (Sum.inl (j, a))).val = 256 * j.val + a.val := by
  change a.val + 256 * j.val = 256 * j.val + a.val
  omega

theorem flat_output_address (j : Fin 16) (a : Fin 256) :
    (flatTableIndex (Sum.inr (j, a))).val = 2048 + 256 * j.val + a.val := by
  change 2048 + (a.val + 256 * j.val) = 2048 + 256 * j.val + a.val
  omega

abbrev LowerTableKey := Fin 8 × Fin 256 → XorWord 64

/-- `core` returns the sixteen bytes of the two 64-bit core outputs and may
read every lower word, including the actual length-table entries. The word
operation on `XorWord 64` is bitwise XOR. `lengthBytes` is the fixed eight-byte
length encoding. Core arithmetic and byte parsing are parameters here. -/
def flatStyleWrapper (core : LowerTableKey → Fin 16 → Fin 256)
    (lengthBytes : Fin 8 → Fin 256) (key : Fin 6144 → XorWord 64) : XorWord 64 :=
  wrappedHash core (fun k => tabulationHash lengthBytes k) (flatKeyEquiv _ key)

theorem flatStyleWrapper_formula (core : LowerTableKey → Fin 16 → Fin 256)
    (lengthBytes : Fin 8 → Fin 256) (key : Fin 6144 → XorWord 64) :
    flatStyleWrapper core lengthBytes key =
      (∑ j, key (flatTableIndex (Sum.inl (j, lengthBytes j)))) +
      ∑ j, key (flatTableIndex (Sum.inr (j, core (flatKeyEquiv _ key).1 j))) := rfl

theorem flat_wrapper_equal_length (x y : LowerTableKey → Fin 16 → Fin 256)
    (lengthBytes : Fin 8 → Fin 256) :
    uniformProb (fun key => flatStyleWrapper x lengthBytes key = flatStyleWrapper y lengthBytes key) =
      (1 / (2 : ℚ≥0) ^ 64) + (1 - 1 / (2 : ℚ≥0) ^ 64) *
        uniformProb (fun k => x k = y k) := by
  unfold flatStyleWrapper
  rw [uniformProb_equiv (flatKeyEquiv (XorWord 64))
    (fun k => wrappedHash x (fun k => tabulationHash lengthBytes k) k =
      wrappedHash y (fun k => tabulationHash lengthBytes k) k)]
  simpa [XorWord, Fintype.card_fun] using
    wrapper_equal_length x y (fun k => tabulationHash lengthBytes k)

theorem flat_wrapper_unequal_length (x y : LowerTableKey → Fin 16 → Fin 256)
    (lengthBytes lengthBytes' : Fin 8 → Fin 256) (hne : lengthBytes ≠ lengthBytes') :
    uniformProb (fun key => flatStyleWrapper x lengthBytes key = flatStyleWrapper y lengthBytes' key) ≤
      (1 / (2 : ℚ≥0) ^ 64) + (1 - 1 / (2 : ℚ≥0) ^ 64) * (1 / (2 : ℚ≥0) ^ 64) := by
  unfold flatStyleWrapper
  rw [uniformProb_equiv (flatKeyEquiv (XorWord 64))
    (fun k => wrappedHash x (fun k => tabulationHash lengthBytes k) k =
      wrappedHash y (fun k => tabulationHash lengthBytes' k) k)]
  have hl := (tabulation_collision_exact 64 lengthBytes lengthBytes' hne).le
  simpa [XorWord, Fintype.card_fun] using
    wrapper_unequal_length x y (fun k => tabulationHash lengthBytes k)
      (fun k => tabulationHash lengthBytes' k)
      (by simpa [XorWord, Fintype.card_fun] using hl)

theorem wrapper_numeric_coefficient :
    (1 / (2 : ℚ≥0) ^ 64) + (1 - 1 / (2 : ℚ≥0) ^ 64) * (1 / (2 : ℚ≥0) ^ 64) =
      1 / (2 : ℚ≥0) ^ 63 - 1 / (2 : ℚ≥0) ^ 128 := by
  apply NNRat.coe_injective
  have h64 : (1 / (2 : ℚ≥0) ^ 64) ≤ 1 := by
    exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 64) ≤ 1)
  have h128 : (1 / (2 : ℚ≥0) ^ 128) ≤ 1 / (2 : ℚ≥0) ^ 63 := by
    exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 128) ≤ 1 / (2 : ℚ) ^ 63)
  rw [NNRat.coe_add, NNRat.coe_mul, NNRat.coe_sub h64, NNRat.coe_sub h128]
  norm_num

/-- The normalized reduction is conditional only on the equal-length core
bound. This theorem alone does not verify a byte parser or a Style core. -/
theorem flat_wrapper_normalized_from_core (L : ℕ) (hL : 1 ≤ L)
    (x y : LowerTableKey → Fin 16 → Fin 256)
    (lengthBytes lengthBytes' : Fin 8 → Fin 256)
    (hcore : lengthBytes = lengthBytes' →
      uniformProb (fun k => x k = y k) ≤ (L : ℚ≥0) / 2 ^ 64) :
    uniformProb (fun key => flatStyleWrapper x lengthBytes key = flatStyleWrapper y lengthBytes' key) ≤
      (L : ℚ≥0) * (1 / 2 ^ 63 - 1 / 2 ^ 128) := by
  have hL' : (1 : ℚ≥0) ≤ L := by exact_mod_cast hL
  by_cases he : lengthBytes = lengthBytes'
  · subst lengthBytes'
    rw [flat_wrapper_equal_length]
    have hc := hcore rfl
    calc
      _ ≤ (L : ℚ≥0) / 2 ^ 64 + (1 - 1 / (2 : ℚ≥0) ^ 64) * ((L : ℚ≥0) / 2 ^ 64) := by
        exact add_le_add (div_le_div_of_nonneg_right hL' (by positivity))
          (mul_le_mul_of_nonneg_left hc (zero_le _))
      _ = (L : ℚ≥0) * ((1 / (2 : ℚ≥0) ^ 64) +
          (1 - 1 / (2 : ℚ≥0) ^ 64) * (1 / (2 : ℚ≥0) ^ 64)) := by ring
      _ = _ := by rw [wrapper_numeric_coefficient]
  · exact (flat_wrapper_unequal_length x y lengthBytes lengthBytes' he).trans (by
      rw [wrapper_numeric_coefficient]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hL'
        (zero_le (1 / (2 : ℚ≥0) ^ 63 - 1 / (2 : ℚ≥0) ^ 128)))

/-- The core's finalizer/tail address envelope on the stack-safe domain. -/
theorem style_core_address_envelope (b roots : ℕ) (hb : b ≤ 8) (hr : roots ≤ 64) :
    659 + b * (2 * roots + 19) ≤ 1835 ∧ 1835 < 2048 := by
  constructor
  · nlinarith
  · decide

theorem style_ehc_address (s t : ℕ) (hs : s < 7) (ht : t < 3) :
    512 ≤ 512 + 3 * s + t ∧ 512 + 3 * s + t < 533 := by omega

theorem style_tree_address (j c v : ℕ) (hj : j < 9) (hc : c < 2) (hv : v < 7) :
    533 ≤ 533 + 14 * j + 7 * c + v ∧ 533 + 14 * j + 7 * c + v < 659 := by omega

theorem style_final_address (b roots v c lane : ℕ) (hv : v < roots)
    (hc : c < 2) (hl : lane < b) :
    659 + b * (2 * v + c) + lane < 659 + 2 * b * roots := by
  nlinarith

theorem style_tail_address (b roots t c lane : ℕ) (ht : t < 18)
    (hc : c < 2) (hl : lane < b) :
    659 + 2 * b * roots + b * (t + c) + lane < 659 + b * (2 * roots + 19) := by
  nlinarith

end ProvenHashes.Halftime
