import ProvenHashes.Halftime.Probability

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 200000
universe u

/-- One independent key per height. Every node at a given height uses the same
key; the number of nodes does not appear in the collision bound. -/
def LevelKeys (K : Type u) : ℕ → Type u
  | 0 => PUnit
  | h + 1 => LevelKeys K h × K

instance levelKeysFintype (K : Type*) [Fintype K] (h : ℕ) : Fintype (LevelKeys K h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ h ih =>
    letI := ih
    exact inferInstanceAs (Fintype (LevelKeys K h × K))

instance levelKeysNonempty (K : Type*) [Nonempty K] (h : ℕ) : Nonempty (LevelKeys K h) := by
  induction h with
  | zero => exact inferInstanceAs (Nonempty PUnit)
  | succ h ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (LevelKeys K h × K))

/-- A public, key-independent tree schedule. `skip` embeds a shorter tree into
a common height budget, so trees in a forest use the same key at the same
actual height. Complete f-ary trees and their base-f forest fit this model. -/
inductive TreeShape (f : ℕ) : ℕ → Type
  | leaf : TreeShape f 0
  | skip {h : ℕ} : TreeShape f h → TreeShape f (h + 1)
  | node {h : ℕ} : (Fin f → TreeShape f h) → TreeShape f (h + 1)

def TreeInput (W : Type u) {f : ℕ} : {h : ℕ} → TreeShape f h → Type u
  | _, .leaf => W
  | _, .skip s => TreeInput W s
  | _, .node s => ∀ i, TreeInput W (s i)

def treeHash {K W : Type*} {f : ℕ} (g : K → (Fin f → W) → W) :
    {h : ℕ} → (s : TreeShape f h) → TreeInput W s → LevelKeys K h → W
  | _, .leaf, x, _ => x
  | _, .skip s, x, k => treeHash g s x k.1
  | _, .node s, x, k => g k.2 (fun i => treeHash g (s i) (x i) k.1)

theorem tree_collision_bound {K W : Type*} [Fintype K] [Nonempty K] {f : ℕ}
    (g : K → (Fin f → W) → W) (ε : ℚ≥0)
    (hg : ∀ x y, x ≠ y → uniformProb (fun k => g k x = g k y) ≤ ε)
    {h : ℕ} (s : TreeShape f h) (x y : TreeInput W s) (hxy : x ≠ y) :
    uniformProb (fun k => treeHash g s x k = treeHash g s y k) ≤ (h : ℚ≥0) * ε := by
  induction s with
  | leaf => simp [treeHash, uniformProb, hxy]
  | @skip h s ih =>
    change uniformProb (fun k : LevelKeys K h × K => treeHash g s x k.1 = treeHash g s y k.1) ≤ _
    rw [uniformProb_prod_fst (J := K) (fun k : LevelKeys K h => treeHash g s x k = treeHash g s y k)]
    exact (ih x y hxy).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ h) (by positivity))
  | @node h s ih =>
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    have hs : uniformProb (fun k : LevelKeys K h =>
        (fun i => treeHash g (s i) (x i) k) = (fun i => treeHash g (s i) (y i) k)) ≤ (h : ℚ≥0) * ε :=
      (uniformProb_mono (fun k hk => congrFun hk i)).trans (ih i (x i) (y i) hi)
    change uniformProb (fun k : LevelKeys K h × K =>
      g k.2 (fun i => treeHash g (s i) (x i) k.1) =
      g k.2 (fun i => treeHash g (s i) (y i) k.1)) ≤ _
    calc
      _ ≤ (h : ℚ≥0) * ε + ε := compose_collision_bound _ _ g _ _ hs (fun k hk => hg _ _ hk)
      _ = _ := by push_cast; ring

def forestHash {I K W : Type*} {f h : ℕ} (g : K → (Fin f → W) → W)
    (s : I → TreeShape f h) (x : ∀ i, TreeInput W (s i)) (k : LevelKeys K h) : I → W :=
  fun i => treeHash g (s i) (x i) k

/-- Root-list agreement costs at most hε. No independence between roots or
between nodes at one height is used. -/
theorem forest_collision_bound {I K W : Type*} [Fintype K] [Nonempty K] {f h : ℕ}
    (g : K → (Fin f → W) → W) (ε : ℚ≥0)
    (hg : ∀ x y, x ≠ y → uniformProb (fun k => g k x = g k y) ≤ ε)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput W (s i)) (hxy : x ≠ y) :
    uniformProb (fun k => forestHash g s x k = forestHash g s y k) ≤ (h : ℚ≥0) * ε := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  exact (uniformProb_mono (fun k hk => congrFun hk i)).trans
    (tree_collision_bound g ε hg (s i) (x i) (y i) hi)

/-- Difference universality after an independently keyed final compressor. -/
theorem compose_difference_bound {K J M R : Type*}
    [Fintype K] [Fintype J] [Nonempty K] [Nonempty J] [AddCommGroup R]
    (s s' : K → M) (g : J → M → R) (a b : ℚ≥0)
    (hs : uniformProb (fun k => s k = s' k) ≤ a)
    (hg : ∀ k, s k ≠ s' k → ∀ t, uniformProb (fun j => g j (s k) - g j (s' k) = t) ≤ b)
    (t : R) :
    uniformProb (fun k : K × J => g k.2 (s k.1) - g k.2 (s' k.1) = t) ≤ a + b := by
  classical
  let E : K × J → Prop := fun k => s k.1 = s' k.1
  let D : K × J → Prop := fun k => s k.1 ≠ s' k.1 ∧ g k.2 (s k.1) - g k.2 (s' k.1) = t
  have he : uniformProb E ≤ a :=
    (uniformProb_prod_fst (J := J) (fun k : K => s k = s' k)).le.trans hs
  have hd : uniformProb D ≤ b := by
    apply uniformProb_prod_le
    intro k
    by_cases hk : s k = s' k
    · simp [D, hk, uniformProb]
    · exact (uniformProb_mono (fun j hj => hj.2)).trans (hg k hk t)
  calc
    _ ≤ uniformProb (fun k => E k ∨ D k) := uniformProb_mono (by
      intro k hk
      by_cases h : s k.1 = s' k.1
      · exact Or.inl h
      · exact Or.inr ⟨h, hk⟩)
    _ ≤ uniformProb E + uniformProb D := uniformProb_or_le _ _
    _ ≤ a + b := add_le_add he hd

theorem forest_final_adu {I K J W R : Type*}
    [Fintype K] [Fintype J] [Nonempty K] [Nonempty J] [AddCommGroup R] {f h : ℕ}
    (g : K → (Fin f → W) → W) (ε : ℚ≥0)
    (hg : ∀ x y, x ≠ y → uniformProb (fun k => g k x = g k y) ≤ ε)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput W (s i)) (hxy : x ≠ y)
    (final : J → (I → W) → R)
    (hfinal : ∀ x y, x ≠ y → ∀ t, uniformProb (fun k => final k x - final k y = t) ≤ ε)
    (t : R) :
    uniformProb (fun k : LevelKeys K h × J =>
      final k.2 (forestHash g s x k.1) - final k.2 (forestHash g s y k.1) = t) ≤
      ((h + 1 : ℕ) : ℚ≥0) * ε := by
  calc
    _ ≤ (h : ℚ≥0) * ε + ε := compose_difference_bound _ _ final _ _
      (forest_collision_bound g ε hg s x y hxy) (fun k hk => hfinal _ _ hk) t
    _ = _ := by push_cast; ring

end ProvenHashes.Halftime
