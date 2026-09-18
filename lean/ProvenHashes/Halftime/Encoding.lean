import ProvenHashes.Halftime.StyleCore

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- The systematic parity encoder. With bit-vector symbols, addition is XOR. -/
def systematicParity {A : Type*} [AddCommGroup A] {n : ℕ}
    (x : Fin n → A) : Fin (n + 1) → A :=
  Fin.lastCases (∑ i, x i) x

theorem systematicParity_distance {A : Type*} [AddCommGroup A] {n : ℕ}
    (x y : Fin n → A) (hxy : x ≠ y) :
    ∃ j : Fin 2 ↪ Fin (n + 1), ∀ i, systematicParity x (j i) ≠ systematicParity y (j i) := by
  classical
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hxy
  have pair (b : Fin (n + 1)) (hab : a.castSucc ≠ b)
      (hb : systematicParity x b ≠ systematicParity y b) :
      ∃ j : Fin 2 ↪ Fin (n + 1), ∀ i, systematicParity x (j i) ≠ systematicParity y (j i) := by
    let j : Fin 2 ↪ Fin (n + 1) := ⟨![a.castSucc, b], by
      intro i k he
      fin_cases i <;> fin_cases k <;> simp_all⟩
    refine ⟨j, ?_⟩
    intro i
    fin_cases i
    · simpa [j, systematicParity] using ha
    · simpa [j] using hb
  by_cases ho : ∃ b : Fin n, b ≠ a ∧ x b ≠ y b
  · obtain ⟨b, hba, hb⟩ := ho
    exact pair b.castSucc (fun he => hba (Fin.castSucc_injective n he).symm)
      (by simpa [systematicParity] using hb)
  · have hrest (i : Fin n) (hi : i ≠ a) : x i = y i := by
      by_contra hne
      exact ho ⟨i, hi, hne⟩
    apply pair (Fin.last n) (Fin.castSucc_ne_last a)
    simp only [systematicParity, Fin.lastCases_last]
    intro he
    apply ha
    have hs : (∑ i, (x i - y i)) = x a - y a := by
      apply Finset.sum_eq_single a
      · intro i _ hi
        rw [hrest i hi, sub_self]
      · simp
    rw [Finset.sum_sub_distrib, he, sub_self] at hs
    exact sub_eq_zero.mp hs.symm

/-- Little-endian identification of XOR bits with a modular unsigned word.
The forward natural value is the sum of bit_i * 2^i. -/
noncomputable def xorWordEquiv (w : ℕ) : XorWord w ≃ ZMod (2 ^ w) :=
  (Equiv.piCongrRight fun _ : Fin w => (ZMod.finEquiv 2).toEquiv.symm).trans
    (finFunctionFinEquiv.trans (ZMod.finEquiv (2 ^ w)).toEquiv)

/-- The six triples in one physical lane, in the header's symbol order. -/
abbrev Encode2Input := Fin 6 → Fin 3 × Bool → XorWord 32

/-- Encode2 on one lane, followed by the unsigned interpretation of halves. -/
noncomputable def encode2 (x : Encode2Input) : Fin 7 → Fin 3 × Bool → ZMod (2 ^ 32) :=
  fun s p => xorWordEquiv 32 (systematicParity x s p)

theorem encode2_distance (x y : Encode2Input) (hxy : x ≠ y) :
    ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode2 x (j i) ≠ encode2 y (j i) := by
  obtain ⟨j, hj⟩ := systematicParity_distance x y hxy
  refine ⟨j, fun i he => hj i ?_⟩
  funext p
  exact (xorWordEquiv 32).injective (congrFun he p)

theorem encode2_systematic (x : Encode2Input) (i : Fin 6) (p : Fin 3 × Bool) :
    encode2 x i.castSucc p = xorWordEquiv 32 (x i p) := by
  simp [encode2, systematicParity]

theorem encode2_parity (x : Encode2Input) (p : Fin 3 × Bool) :
    encode2 x (Fin.last 6) p = xorWordEquiv 32 (∑ i, x i p) := by
  simp only [encode2, systematicParity, Fin.lastCases_last, Finset.sum_apply]

/-- The actual Encode2 discharges the encoder-distance assumption of the
scalar construction. The input symbols are arbitrary 32-bit bit patterns. -/
theorem encode2_scalar_survival {nt roots h l : ℕ}
    (s : Fin roots → TreeShape (nt + 1) h)
    (x y : (∀ i, TreeInput Encode2Input (s i)) × (Fin l × Bool → ZMod (2 ^ 32)))
    (hxy : x ≠ y) (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode2 T2 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s x k -
      halftimeCore encode2 T2 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s y k = b) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
  exact scalar_halftime_two_survival encode2 encode2_distance s x y hxy b

end ProvenHashes.Halftime
