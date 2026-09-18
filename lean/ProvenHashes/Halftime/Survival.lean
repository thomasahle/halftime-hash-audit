import ProvenHashes.Halftime.Wrapper

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- A refined composition step retaining the probability of surviving earlier
stages. `E` can be any exceptional event on all previously exposed keys. -/
theorem conditional_event_affine {K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] (E : K → Prop) (C : K → J → Prop) (ε : ℚ≥0) (hε : ε ≤ 1)
    (hc : ∀ k, ¬ E k → uniformProb (C k) ≤ ε) :
    uniformProb (fun k : K × J => C k.1 k.2) ≤
      ε + (1 - ε) * uniformProb E := by
  classical
  rw [uniformProb_prod]
  change mean (fun k => uniformProb (C k)) ≤ _
  calc
    _ ≤ mean (fun k => ε + (1 - ε) * indicator E k) := by
      apply mean_mono
      intro k
      by_cases he : E k
      · simpa [indicator, he, add_tsub_cancel_of_le hε] using uniformProb_le_one (C k)
      · simpa [indicator, he] using hc k he
    _ = _ := by rw [mean_add, mean_const, mean_mul, mean_indicator]

def failure (ε : ℚ≥0) : ℕ → ℚ≥0
  | 0 => 0
  | h + 1 => ε + (1 - ε) * failure ε h

def survival (ε : ℚ≥0) (h : ℕ) : ℚ≥0 := (1 - ε) ^ h

theorem failure_add_survival (ε : ℚ≥0) (hε : ε ≤ 1) (h : ℕ) :
    failure ε h + survival ε h = 1 := by
  induction h with
  | zero => simp [failure, survival]
  | succ h ih =>
    calc
      _ = ε + (1 - ε) * (failure ε h + survival ε h) := by
        simp only [failure, survival, pow_succ]
        ring
      _ = 1 := by rw [ih, mul_one]; exact add_tsub_cancel_of_le hε

theorem failure_eq (ε : ℚ≥0) (hε : ε ≤ 1) (h : ℕ) :
    failure ε h = 1 - (1 - ε) ^ h := by
  calc
    _ = (failure ε h + survival ε h) - survival ε h := (add_tsub_cancel_right _ _).symm
    _ = _ := by rw [failure_add_survival ε hε]; rfl

theorem failure_mono_step (ε : ℚ≥0) (hε : ε ≤ 1) (h : ℕ) :
    failure ε h ≤ failure ε (h + 1) := by
  have he : failure ε h + ε * survival ε h = failure ε (h + 1) := by
    calc
      _ = (ε + (1 - ε)) * failure ε h + ε * survival ε h := by
        rw [add_tsub_cancel_of_le hε, one_mul]
      _ = ε * (failure ε h + survival ε h) + (1 - ε) * failure ε h := by ring
      _ = _ := by rw [failure_add_survival ε hε, mul_one]; rfl
  rw [← he]
  exact le_add_of_nonneg_right (zero_le _)

theorem failure_le_linear (ε : ℚ≥0) (h : ℕ) :
    failure ε h ≤ (h : ℚ≥0) * ε := by
  induction h with
  | zero => simp [failure]
  | succ h ih =>
    have hq : 1 - ε ≤ (1 : ℚ≥0) := tsub_le_self
    calc
      _ = ε + (1 - ε) * failure ε h := rfl
      _ ≤ ε + 1 * ((h : ℚ≥0) * ε) := by gcongr
      _ = _ := by push_cast; ring

theorem survival_le_one (ε : ℚ≥0) (h : ℕ) : survival ε h ≤ 1 := by
  exact pow_le_one₀ (zero_le _) tsub_le_self

theorem tree_collision_survival {K W : Type*} [Fintype K] [Nonempty K] {f : ℕ}
    (g : K → (Fin f → W) → W) (ε : ℚ≥0) (hε : ε ≤ 1)
    (hg : ∀ x y, x ≠ y → uniformProb (fun k => g k x = g k y) ≤ ε)
    {h : ℕ} (s : TreeShape f h) (x y : TreeInput W s) (hxy : x ≠ y) :
    uniformProb (fun k => treeHash g s x k = treeHash g s y k) ≤ failure ε h := by
  induction s with
  | leaf => simp [treeHash, uniformProb, hxy, failure]
  | @skip h s ih =>
    change uniformProb (fun k : LevelKeys K h × K => treeHash g s x k.1 = treeHash g s y k.1) ≤ _
    rw [uniformProb_prod_fst (J := K) (fun k : LevelKeys K h => treeHash g s x k = treeHash g s y k)]
    exact (ih x y hxy).trans (failure_mono_step ε hε h)
  | @node h s ih =>
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    have hs : uniformProb (fun k : LevelKeys K h =>
        (fun i => treeHash g (s i) (x i) k) = (fun i => treeHash g (s i) (y i) k)) ≤ failure ε h :=
      (uniformProb_mono (fun k hk => congrFun hk i)).trans (ih i (x i) (y i) hi)
    change uniformProb (fun k : LevelKeys K h × K =>
      g k.2 (fun i => treeHash g (s i) (x i) k.1) =
      g k.2 (fun i => treeHash g (s i) (y i) k.1)) ≤ _
    apply (conditional_event_affine
      (fun k : LevelKeys K h =>
        (fun i => treeHash g (s i) (x i) k) = (fun i => treeHash g (s i) (y i) k))
      (fun k key => g key (fun i => treeHash g (s i) (x i) k) =
        g key (fun i => treeHash g (s i) (y i) k))
      ε hε (fun k hk => hg _ _ hk)).trans
    exact add_le_add_left (mul_le_mul_of_nonneg_left hs (zero_le _)) _

theorem forest_collision_survival {I K W : Type*} [Fintype K] [Nonempty K] {f h : ℕ}
    (g : K → (Fin f → W) → W) (ε : ℚ≥0) (hε : ε ≤ 1)
    (hg : ∀ x y, x ≠ y → uniformProb (fun k => g k x = g k y) ≤ ε)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput W (s i)) (hxy : x ≠ y) :
    uniformProb (fun k => forestHash g s x k = forestHash g s y k) ≤ failure ε h := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  exact (uniformProb_mono (fun k hk => congrFun hk i)).trans
    (tree_collision_survival g ε hε hg (s i) (x i) (y i) hi)

theorem forest_final_survival {I K J W R : Type*}
    [Fintype K] [Fintype J] [Nonempty K] [Nonempty J] [AddCommGroup R] {f h : ℕ}
    (g : K → (Fin f → W) → W) (ε : ℚ≥0) (hε : ε ≤ 1)
    (hg : ∀ x y, x ≠ y → uniformProb (fun k => g k x = g k y) ≤ ε)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput W (s i)) (hxy : x ≠ y)
    (final : J → (I → W) → R)
    (hfinal : ∀ x y, x ≠ y → ∀ t, uniformProb (fun k => final k x - final k y = t) ≤ ε)
    (t : R) :
    uniformProb (fun k : LevelKeys K h × J =>
      final k.2 (forestHash g s x k.1) - final k.2 (forestHash g s y k.1) = t) ≤
      failure ε (h + 1) := by
  apply (conditional_event_affine
    (fun k => forestHash g s x k = forestHash g s y k) _ ε hε
    (fun k hk => hfinal _ _ hk t)).trans
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (forest_collision_survival g ε hε hg s x y hxy) (zero_le _)) _

theorem component_product_affine {I K J : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Fintype J] (E : I → K → Prop) (C : K → I → J → Prop)
    (a s : ℚ≥0) (has : a + s = 1)
    (hc : ∀ k i, ¬ E i k → uniformProb (C k i) ≤ a) :
    uniformProb (fun k : K × (I → J) => ∀ i, C k.1 i (k.2 i)) ≤
      mean (fun k => ∏ i, (a + s * indicator (E i) k)) := by
  classical
  rw [uniformProb_prod]
  change mean (fun k => uniformProb (fun j : I → J => ∀ i, C k i (j i))) ≤ _
  apply mean_mono
  intro k
  rw [uniformProb_pi]
  apply Finset.prod_le_prod (fun i _ => zero_le _)
  intro i _
  by_cases he : E i k
  · simpa [indicator, he, has] using uniformProb_le_one (C k i)
  · simpa [indicator, he] using hc k i he

theorem product_two_affine_expansion {K : Type*} (E : Fin 2 → K → Prop)
    (a s : ℚ≥0) (k : K) :
    (∏ i, (a + s * indicator (E i) k)) =
      a ^ 2 + a * s * (indicator (E 0) k + indicator (E 1) k) +
        s ^ 2 * indicator (fun k => E 0 k ∧ E 1 k) k := by
  classical
  simp only [Fin.prod_univ_two]
  by_cases h0 : E 0 k <;> by_cases h1 : E 1 k <;> simp [indicator, h0, h1] <;> ring

def styleTwoBound (ε : ℚ≥0) (h : ℕ) : ℚ≥0 :=
  (failure ε (h + 1) + survival ε (h + 1) * ε) *
    (failure ε (h + 1) + 2 * survival ε (h + 1) * ε)

/-- B₂(h) from the sharp singleton-sum and pair bounds. Those bounds are
explicit hypotheses here; they must be supplied by the distance-2 EHC proof. -/
theorem end_to_end_two_survival_from_subsets {K J : Type*} [Fintype K] [Nonempty K] [Fintype J]
    (E : Fin 2 → K → Prop) (C : K → Fin 2 → J → Prop) (ε : ℚ≥0) (hε : ε ≤ 1) (h : ℕ)
    (hc : ∀ k i, ¬ E i k → uniformProb (C k i) ≤ failure ε (h + 1))
    (hs : uniformProb (E 0) + uniformProb (E 1) ≤ 3 * ε)
    (hp : uniformProb (fun k => E 0 k ∧ E 1 k) ≤ 2 * ε ^ 2) :
    uniformProb (fun k : K × (Fin 2 → J) => ∀ i, C k.1 i (k.2 i)) ≤ styleTwoBound ε h := by
  let a := failure ε (h + 1)
  let s := survival ε (h + 1)
  have hm : mean (fun k => ∏ i, (a + s * indicator (E i) k)) =
      a ^ 2 + a * s * (uniformProb (E 0) + uniformProb (E 1)) +
        s ^ 2 * uniformProb (fun k => E 0 k ∧ E 1 k) := by
    simp only [product_two_affine_expansion, mean_add, mean_mul, mean_const, mean_indicator]
  calc
    _ ≤ mean (fun k => ∏ i, (a + s * indicator (E i) k)) :=
      component_product_affine E C a s (failure_add_survival ε hε _) hc
    _ = _ := hm
    _ ≤ a ^ 2 + a * s * (3 * ε) + s ^ 2 * (2 * ε ^ 2) := by gcongr
    _ = _ := by dsimp [a, s, styleTwoBound]; ring

theorem styleTwoBound_formula (ε : ℚ≥0) (hε : ε ≤ 1) (h : ℕ) :
    styleTwoBound ε h =
      (1 - (1 - ε) ^ (h + 1) + (1 - ε) ^ (h + 1) * ε) *
        (1 - (1 - ε) ^ (h + 1) + 2 * (1 - ε) ^ (h + 1) * ε) := by
  simp only [styleTwoBound, failure_eq ε hε, survival]

theorem styleTwoBound_le (ε : ℚ≥0) (h : ℕ) :
    styleTwoBound ε h ≤ ((h : ℚ≥0) + 2) * ((h : ℚ≥0) + 3) * ε ^ 2 := by
  have ha := failure_le_linear ε (h + 1)
  have hs := survival_le_one ε (h + 1)
  calc
    _ ≤ (((h + 1 : ℕ) : ℚ≥0) * ε + 1 * ε) *
        (((h + 1 : ℕ) : ℚ≥0) * ε + 2 * 1 * ε) := by unfold styleTwoBound; gcongr
    _ = _ := by push_cast; ring

end ProvenHashes.Halftime
