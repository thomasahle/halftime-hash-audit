import ProvenHashes.Halftime.Forest
import ProvenHashes.Halftime.Matrices

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def mean {K : Type*} [Fintype K] (f : K → ℚ≥0) : ℚ≥0 :=
  (∑ k, f k) / Fintype.card K

noncomputable def indicator {K : Type*} (E : K → Prop) (k : K) : ℚ≥0 := by
  classical
  exact if E k then 1 else 0

theorem mean_mono {K : Type*} [Fintype K] {f g : K → ℚ≥0} (h : ∀ k, f k ≤ g k) :
    mean f ≤ mean g := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun k _ => h k)) (by positivity)

theorem mean_const {K : Type*} [Fintype K] [Nonempty K] (c : ℚ≥0) :
    mean (fun _ : K => c) = c := by simp [mean]

theorem mean_add {K : Type*} [Fintype K] (f g : K → ℚ≥0) :
    mean (fun k => f k + g k) = mean f + mean g := by simp [mean, Finset.sum_add_distrib, add_div]

theorem mean_mul {K : Type*} [Fintype K] (c : ℚ≥0) (f : K → ℚ≥0) :
    mean (fun k => c * f k) = c * mean f := by simp [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_indicator {K : Type*} [Fintype K] (E : K → Prop) :
    mean (indicator E) = uniformProb E := by
  classical
  simp [mean, indicator, uniformProb, Finset.sum_boole]

/-- Independent component keys, after fixing the entire EHC key. The indicator
may be equality of just one selected leaf; no independence of leaf events is
needed or assumed. -/
theorem component_product_bound {I K J : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Fintype J]
    (E : I → K → Prop) (C : K → I → J → Prop) (ρ : ℚ≥0)
    (hc : ∀ k i, ¬ E i k → uniformProb (C k i) ≤ ρ) :
    uniformProb (fun k : K × (I → J) => ∀ i, C k.1 i (k.2 i)) ≤
      mean (fun k => ∏ i, (ρ + indicator (E i) k)) := by
  classical
  rw [uniformProb_prod]
  change mean (fun k => uniformProb (fun j : I → J => ∀ i, C k i (j i))) ≤ _
  apply mean_mono
  intro k
  rw [uniformProb_pi]
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i _
  by_cases he : E i k
  · exact (uniformProb_le_one _).trans (by simp [indicator, he])
  · simpa [indicator, he] using hc k i he

theorem product_two_expansion {K : Type*} (E : Fin 2 → K → Prop) (ρ : ℚ≥0) (k : K) :
    (∏ i, (ρ + indicator (E i) k)) =
      ρ ^ 2 + ρ * (indicator (E 0) k + indicator (E 1) k) +
        indicator (fun k => E 0 k ∧ E 1 k) k := by
  classical
  simp only [Fin.prod_univ_two]
  by_cases h0 : E 0 k <;> by_cases h1 : E 1 k <;> simp [indicator, h0, h1] <;> ring

theorem product_three_expansion {K : Type*} (E : Fin 3 → K → Prop) (ρ : ℚ≥0) (k : K) :
    (∏ i, (ρ + indicator (E i) k)) =
      ρ ^ 3 + ρ ^ 2 * (indicator (E 0) k + indicator (E 1) k + indicator (E 2) k) +
        ρ * (indicator (fun k => E 0 k ∧ E 1 k) k + indicator (fun k => E 0 k ∧ E 2 k) k +
          indicator (fun k => E 1 k ∧ E 2 k) k) +
        indicator (fun k => E 0 k ∧ E 1 k ∧ E 2 k) k := by
  classical
  simp only [Fin.prod_univ_succ, Fin.succ_zero_eq_one]
  by_cases h0 : E 0 k <;> by_cases h1 : E 1 k <;> by_cases h2 : E 2 k <;>
    simp [indicator, h0, h1, h2] <;> ring

theorem end_to_end_two_from_subsets {K J : Type*} [Fintype K] [Nonempty K] [Fintype J]
    (E : Fin 2 → K → Prop) (C : K → Fin 2 → J → Prop) (ε : ℚ≥0) (h : ℕ)
    (hc : ∀ k i, ¬ E i k → uniformProb (C k i) ≤ ((h + 1 : ℕ) : ℚ≥0) * ε)
    (hs : uniformProb (E 0) + uniformProb (E 1) ≤ 5 * ε)
    (hp : uniformProb (fun k => E 0 k ∧ E 1 k) ≤ 4 * ε ^ 2) :
    uniformProb (fun k : K × (Fin 2 → J) => ∀ i, C k.1 i (k.2 i)) ≤
      min 1 (ε ^ 2 * ((h : ℚ≥0) + 2) * ((h : ℚ≥0) + 5)) := by
  apply le_min (uniformProb_le_one _)
  let ρ : ℚ≥0 := ((h + 1 : ℕ) : ℚ≥0) * ε
  have hmean : mean (fun k => ∏ i, (ρ + indicator (E i) k)) =
      ρ ^ 2 + ρ * (uniformProb (E 0) + uniformProb (E 1)) +
        uniformProb (fun k => E 0 k ∧ E 1 k) := by
    simp only [product_two_expansion, mean_add, mean_mul, mean_const, mean_indicator]
  calc
    _ ≤ mean (fun k => ∏ i, (ρ + indicator (E i) k)) := component_product_bound E C ρ hc
    _ = _ := hmean
    _ ≤ ρ ^ 2 + ρ * (5 * ε) + 4 * ε ^ 2 := by gcongr
    _ = _ := by dsimp [ρ]; push_cast; ring

theorem end_to_end_three_from_subsets {K J : Type*} [Fintype K] [Nonempty K] [Fintype J]
    (E : Fin 3 → K → Prop) (C : K → Fin 3 → J → Prop) (ε : ℚ≥0) (h : ℕ)
    (hc : ∀ k i, ¬ E i k → uniformProb (C k i) ≤ ((h + 1 : ℕ) : ℚ≥0) * ε)
    (hs : uniformProb (E 0) + uniformProb (E 1) + uniformProb (E 2) ≤ 6 * ε)
    (hp : uniformProb (fun k => E 0 k ∧ E 1 k) + uniformProb (fun k => E 0 k ∧ E 2 k) +
      uniformProb (fun k => E 1 k ∧ E 2 k) ≤ 9 * ε ^ 2)
    (ht : uniformProb (fun k => E 0 k ∧ E 1 k ∧ E 2 k) ≤ 4 * ε ^ 3) :
    uniformProb (fun k : K × (Fin 3 → J) => ∀ i, C k.1 i (k.2 i)) ≤
      min 1 (ε ^ 3 * ((h : ℚ≥0) + 2) ^ 2 * ((h : ℚ≥0) + 5)) := by
  apply le_min (uniformProb_le_one _)
  let ρ : ℚ≥0 := ((h + 1 : ℕ) : ℚ≥0) * ε
  have hmean : mean (fun k => ∏ i, (ρ + indicator (E i) k)) =
      ρ ^ 3 + ρ ^ 2 * (uniformProb (E 0) + uniformProb (E 1) + uniformProb (E 2)) +
        ρ * (uniformProb (fun k => E 0 k ∧ E 1 k) + uniformProb (fun k => E 0 k ∧ E 2 k) +
          uniformProb (fun k => E 1 k ∧ E 2 k)) +
        uniformProb (fun k => E 0 k ∧ E 1 k ∧ E 2 k) := by
    simp only [product_three_expansion, mean_add, mean_mul, mean_const, mean_indicator]
  calc
    _ ≤ mean (fun k => ∏ i, (ρ + indicator (E i) k)) := component_product_bound E C ρ hc
    _ = _ := hmean
    _ ≤ ρ ^ 3 + ρ ^ 2 * (6 * ε) + ρ * (9 * ε ^ 2) + 4 * ε ^ 3 := by gcongr
    _ = _ := by dsimp [ρ]; push_cast; ring

/-- Conditioning on all non-tail keys fixes an arbitrary target for the tail.
There is no additive tail error term. This lemma is independent of the details
used to prove the tail's AΔU bound. -/
theorem tail_conditioning {K J R : Type*} [Fintype K] [Fintype J] [Nonempty K]
    [AddCommGroup R] (prefixHash : K → R) (tail : J → R) (b : R) (ε : ℚ≥0)
    (htail : ∀ t, uniformProb (fun j => tail j = t) ≤ ε) :
    uniformProb (fun k : K × J => prefixHash k.1 + tail k.2 = b) ≤ ε := by
  apply uniformProb_prod_le
  intro k
  have he : (fun j => prefixHash k + tail j = b) = (fun j => tail j = b - prefixHash k) := by
    funext j
    exact propext (eq_sub_iff_add_eq'.symm)
  rw [he]
  exact htail _

theorem numeric_6804 :
    (1 / (2 : ℚ≥0) ^ 32) ^ 3 * (16 + 2) ^ 2 * (16 + 1 + 2 ^ 2) = 6804 / 2 ^ 96 := by
  norm_num

/-- The numerical collision corollary retains the stage and subset
hypotheses explicitly. `numeric_6804` alone is only arithmetic. -/
theorem collision_6804_from_subsets {K J : Type*} [Fintype K] [Nonempty K] [Fintype J]
    (E : Fin 3 → K → Prop) (C : K → Fin 3 → J → Prop)
    (hc : ∀ k i, ¬ E i k → uniformProb (C k i) ≤ 17 / (2 : ℚ≥0) ^ 32)
    (hs : uniformProb (E 0) + uniformProb (E 1) + uniformProb (E 2) ≤ 6 / (2 : ℚ≥0) ^ 32)
    (hp : uniformProb (fun k => E 0 k ∧ E 1 k) + uniformProb (fun k => E 0 k ∧ E 2 k) +
      uniformProb (fun k => E 1 k ∧ E 2 k) ≤ 9 / (2 : ℚ≥0) ^ 64)
    (ht : uniformProb (fun k => E 0 k ∧ E 1 k ∧ E 2 k) ≤ 4 / (2 : ℚ≥0) ^ 96) :
    uniformProb (fun k : K × (Fin 3 → J) => ∀ i, C k.1 i (k.2 i)) ≤ 6804 / (2 : ℚ≥0) ^ 96 := by
  have h := end_to_end_three_from_subsets E C (1 / 2 ^ 32) 16
    (by simpa using hc) (by simpa using hs) (by norm_num at hp ⊢; exact hp)
    (by norm_num at ht ⊢; exact ht)
  exact h.trans (by norm_num)

end ProvenHashes.Halftime
