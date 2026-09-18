import ProvenHashes.Halftime.Projections
import ProvenHashes.Halftime.EndToEnd
import ProvenHashes.Halftime.Toeplitz
import ProvenHashes.Halftime.WordPacking

namespace ProvenHashes.Halftime
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def LeafPath {f : ℕ} : {h : ℕ} → TreeShape f h → Type
  | _, .leaf => PUnit
  | _, .skip s => LeafPath s
  | _, .node s => Σ i, LeafPath (s i)

def leafValue {X : Type*} {f : ℕ} : {h : ℕ} → (s : TreeShape f h) → TreeInput X s → LeafPath s → X
  | _, .leaf, x, _ => x
  | _, .skip s, x, p => leafValue s x p
  | _, .node s, x, p => leafValue (s p.1) (x p.1) p.2

def mapLeaves {X Y : Type*} {f : ℕ} (g : X → Y) :
    {h : ℕ} → (s : TreeShape f h) → TreeInput X s → TreeInput Y s
  | _, .leaf, x => g x
  | _, .skip s, x => mapLeaves g s x
  | _, .node s, x => fun i => mapLeaves g (s i) (x i)

theorem leafValue_map {X Y : Type*} {f h : ℕ} (g : X → Y) (s : TreeShape f h)
    (x : TreeInput X s) (p : LeafPath s) :
    leafValue s (mapLeaves g s x) p = g (leafValue s x p) := by
  induction s with
  | leaf => rfl
  | skip s ih => exact ih x p
  | node s ih => exact ih p.1 (x p.1) p.2

theorem exists_differing_leaf {X : Type*} {f h : ℕ} (s : TreeShape f h)
    (x y : TreeInput X s) (hxy : x ≠ y) :
    ∃ p : LeafPath s, leafValue s x p ≠ leafValue s y p := by
  induction s with
  | leaf => exact ⟨PUnit.unit, hxy⟩
  | skip s ih => exact ih x y hxy
  | node s ih =>
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    obtain ⟨p, hp⟩ := ih i (x i) (y i) hi
    exact ⟨⟨i, p⟩, hp⟩

/-- One EHC key is shared by every leaf. Each output component then has its
own tree keys (one per height) and its own independent final key. -/
def forestCore {X I K J : Type*} {N r n f h : ℕ}
    (encode : X → Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) (Fin N) ℤ)
    (g : Fin r → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin r → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (s : I → TreeShape f h) (x : ∀ i, TreeInput X (s i))
    (k : (Fin N → (Fin n × Bool → ZMod (2 ^ 32))) × (Fin r → (LevelKeys K h × J))) :
    Fin r → ZMod (2 ^ 64) := fun row =>
  final row (k.2 row).2 (forestHash (g row) s
    (fun i => mapLeaves (fun v => ehc encode T v k.1 row) (s i) (x i)) (k.2 row).1)

/-- The component estimate is derived from a selected differing leaf and the
forest lemma; it does not assume independent EHC output coordinates. -/
theorem forestCore_component_bound {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {N r n f h : ℕ}
    (encode : X → Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) (Fin N) ℤ)
    (g : Fin r → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin r → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (hg : ∀ row x y, x ≠ y → uniformProb (fun k => g row k x = g row k y) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hf : ∀ row x y, x ≠ y → ∀ t,
      uniformProb (fun k => final row k x - final row k y = t) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput X (s i))
    (root : I) (p : LeafPath (s root)) (key : Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (row : Fin r)
    (hne : ehc encode T (leafValue (s root) (x root) p) key row ≠
      ehc encode T (leafValue (s root) (y root) p) key row) (t : ZMod (2 ^ 64)) :
    uniformProb (fun k : LevelKeys K h × J =>
      final row k.2 (forestHash (g row) s
        (fun i => mapLeaves (fun v => ehc encode T v key row) (s i) (x i)) k.1) -
      final row k.2 (forestHash (g row) s
        (fun i => mapLeaves (fun v => ehc encode T v key row) (s i) (y i)) k.1) = t) ≤
      ((h + 1 : ℕ) : ℚ≥0) * (1 / 2 ^ 32) := by
  apply forest_final_adu (g row) _ (hg row) s _ _ _ (final row) (hf row) t
  intro he
  have hv := congrArg (fun z => leafValue (s root) (z root) p) he
  simp only [leafValue_map] at hv
  exact hne hv

theorem ehc_difference_eq_combine {X : Type*} {N r n : ℕ}
    (encode : X → Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) (Fin N) ℤ) (x y : X)
    (key : Fin N → (Fin n × Bool → ZMod (2 ^ 32))) :
    ehc encode T x key - ehc encode T y key =
      combine T (fun i k => nh32 (encode x i) k - nh32 (encode y i) k) key := by
  simp only [ehc, combine, ← Matrix.mulVec_sub]
  rfl

/-- EHC, shared-height forests, and independent final compression, with every
joint EHC subset bound discharged from the explicit T2 matrix. -/
theorem forestCore_two_bound {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {n f h : ℕ}
    (encode : X → Fin 7 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode x (j i) ≠ encode y (j i))
    (g : Fin 2 → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin 2 → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (hg : ∀ row x y, x ≠ y → uniformProb (fun k => g row k x = g row k y) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hf : ∀ row x y, x ≠ y → ∀ t,
      uniformProb (fun k => final row k x - final row k y = t) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput X (s i)) (hxy : x ≠ y)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k => forestCore encode T2 g final s x k - forestCore encode T2 g final s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 2 * ((h : ℚ≥0) + 2) ^ (2 - 1) * ((h : ℚ≥0) + 5)) := by
  classical
  obtain ⟨root, hroot⟩ := Function.ne_iff.mp hxy
  obtain ⟨p, hp⟩ := exists_differing_leaf (s root) (x root) (y root) hroot
  let u := leafValue (s root) (x root) p
  let v := leafValue (s root) (y root) p
  obtain ⟨j, hj⟩ := hdistance u v hp
  let d (i : Fin 7) (k : Fin n × Bool → ZMod (2 ^ 32)) := nh32 (encode u i) k - nh32 (encode v i) k
  let E (row : Fin 2) (key : Fin 7 → (Fin n × Bool → ZMod (2 ^ 32))) := combine T2 d key row = 0
  let C (key : Fin 7 → (Fin n × Bool → ZMod (2 ^ 32))) (row : Fin 2) (k : LevelKeys K h × J) :=
    final row k.2 (forestHash (g row) s
      (fun i => mapLeaves (fun v => ehc encode T2 v key row) (s i) (x i)) k.1) -
    final row k.2 (forestHash (g row) s
      (fun i => mapLeaves (fun v => ehc encode T2 v key row) (s i) (y i)) k.1) = b row
  have hc (key) (row) (hne : ¬ E row key) : uniformProb (C key row) ≤
      ((h + 1 : ℕ) : ℚ≥0) * (1 / 2 ^ 32) := by
    apply forestCore_component_bound encode T2 g final hg hf s x y root p key row _ (b row)
    intro he
    have hh := congrFun (ehc_difference_eq_combine encode T2 u v key) row
    change ehc encode T2 u key row - ehc encode T2 v key row = combine T2 d key row at hh
    exact hne (hh.symm.trans (sub_eq_zero.mpr he))
  have hs := T2_subset_bounds d j (fun i z => nh32_adu _ _ (hj i) z) 0
  have H := end_to_end_two_from_subsets E C (1 / 2 ^ 32) h hc
    (by simpa [E] using hs.1) (by norm_num [E] at hs ⊢; exact hs.2)
  simpa [forestCore, funext_iff, C] using H

/-- EHC, shared-height forests, and independent final compression, with every
joint EHC subset bound discharged from the explicit T3 matrix. -/
theorem forestCore_three_bound {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {n f h : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (g : Fin 3 → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin 3 → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (hg : ∀ row x y, x ≠ y → uniformProb (fun k => g row k x = g row k y) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hf : ∀ row x y, x ≠ y → ∀ t,
      uniformProb (fun k => final row k x - final row k y = t) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (s : I → TreeShape f h) (x y : ∀ i, TreeInput X (s i)) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k => forestCore encode T3 g final s x k - forestCore encode T3 g final s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 3 * ((h : ℚ≥0) + 2) ^ (3 - 1) * ((h : ℚ≥0) + 5)) := by
  classical
  obtain ⟨root, hroot⟩ := Function.ne_iff.mp hxy
  obtain ⟨p, hp⟩ := exists_differing_leaf (s root) (x root) (y root) hroot
  let u := leafValue (s root) (x root) p
  let v := leafValue (s root) (y root) p
  obtain ⟨j, hj⟩ := hdistance u v hp
  let d (i : Fin 9) (k : Fin n × Bool → ZMod (2 ^ 32)) := nh32 (encode u i) k - nh32 (encode v i) k
  let E (row : Fin 3) (key : Fin 9 → (Fin n × Bool → ZMod (2 ^ 32))) := combine T3 d key row = 0
  let C (key : Fin 9 → (Fin n × Bool → ZMod (2 ^ 32))) (row : Fin 3) (k : LevelKeys K h × J) :=
    final row k.2 (forestHash (g row) s
      (fun i => mapLeaves (fun v => ehc encode T3 v key row) (s i) (x i)) k.1) -
    final row k.2 (forestHash (g row) s
      (fun i => mapLeaves (fun v => ehc encode T3 v key row) (s i) (y i)) k.1) = b row
  have hc (key) (row) (hne : ¬ E row key) : uniformProb (C key row) ≤
      ((h + 1 : ℕ) : ℚ≥0) * (1 / 2 ^ 32) := by
    apply forestCore_component_bound encode T3 g final hg hf s x y root p key row _ (b row)
    intro he
    have hh := congrFun (ehc_difference_eq_combine encode T3 u v key) row
    change ehc encode T3 u key row - ehc encode T3 v key row = combine T3 d key row at hh
    exact hne (hh.symm.trans (sub_eq_zero.mpr he))
  have hs := T3_subset_bounds d j (fun i z => nh32_adu _ _ (hj i) z) 0
  have H := end_to_end_three_from_subsets E C (1 / 2 ^ 32) h hc
    (by simpa [E] using hs.1) (by norm_num [E] at hs ⊢; exact hs.2.1)
    (by norm_num [E] at hs ⊢; exact hs.2.2)
  simpa only [forestCore, Pi.sub_apply, funext_iff, C] using H

/-- Fixed-layout abstract HalftimeHash: forest prefix plus a separately keyed
Toeplitz NH tail, added componentwise. Both messages use the same forest shape
and padded tail length. The input type therefore describes equal-layout data. -/
def halftimeCore {X I K J : Type*} {N r n f h l : ℕ}
    (encode : X → Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) (Fin N) ℤ)
    (g : Fin r → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin r → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (s : I → TreeShape f h)
    (x : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32)))
    (k : ((Fin N → (Fin n × Bool → ZMod (2 ^ 32))) × (Fin r → (LevelKeys K h × J))) ×
      (Fin (l + r - 1) × Bool → ZMod (2 ^ 32))) : Fin r → ZMod (2 ^ 64) :=
  forestCore encode T g final s x.1 k.1 + toeplitzNH x.2 k.2

theorem halftimeCore_different_tail {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {N r n f h l : ℕ}
    (encode : X → Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) (Fin N) ℤ)
    (g : Fin r → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin r → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (s : I → TreeShape f h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32)))
    (hxy : x.2 ≠ y.2) (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k => halftimeCore encode T g final s x k - halftimeCore encode T g final s y k = b) ≤
      (1 / (2 : ℚ≥0) ^ 32) ^ r := by
  have H := tail_conditioning
    (fun k => forestCore encode T g final s x.1 k - forestCore encode T g final s y.1 k)
    (fun k => toeplitzNH x.2 k - toeplitzNH y.2 k) b _ (toeplitzNH_adu x.2 y.2 hxy)
  have he : (fun k => halftimeCore encode T g final s x k - halftimeCore encode T g final s y k = b) =
      (fun k => (forestCore encode T g final s x.1 k.1 - forestCore encode T g final s y.1 k.1) +
        (toeplitzNH x.2 k.2 - toeplitzNH y.2 k.2) = b) := by
    funext k
    simp only [halftimeCore]
    congr 1
    abel
  rw [he]
  exact H

theorem halftimeCore_equal_tail {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {N r n f h l : ℕ}
    (encode : X → Fin N → (Fin n × Bool → ZMod (2 ^ 32)))
    (T : Matrix (Fin r) (Fin N) ℤ)
    (g : Fin r → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin r → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (s : I → TreeShape f h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32)))
    (hxy : x.2 = y.2) (b : Fin r → ZMod (2 ^ 64)) :
    uniformProb (fun k => halftimeCore encode T g final s x k - halftimeCore encode T g final s y k = b) =
    uniformProb (fun k => forestCore encode T g final s x.1 k - forestCore encode T g final s y.1 k = b) := by
  simp only [halftimeCore, hxy, add_sub_add_right_eq_sub]
  exact uniformProb_prod_fst
    (K := (Fin N → (Fin n × Bool → ZMod (2 ^ 32))) × (Fin r → (LevelKeys K h × J)))
    (J := Fin (l + r - 1) × Bool → ZMod (2 ^ 32))
    (fun k => forestCore encode T g final s x.1 k - forestCore encode T g final s y.1 k = b)

/-- End-to-end abstract construction, including both equal-tail and
unequal-tail comparisons. Tail conditioning contributes no additive term. -/
theorem halftimeCore_two_bound {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {n f h l : ℕ}
    (encode : X → Fin 7 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode x (j i) ≠ encode y (j i))
    (g : Fin 2 → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin 2 → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (hg : ∀ row x y, x ≠ y → uniformProb (fun k => g row k x = g row k y) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hf : ∀ row x y, x ≠ y → ∀ t,
      uniformProb (fun k => final row k x - final row k y = t) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (s : I → TreeShape f h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k => halftimeCore encode T2 g final s x k - halftimeCore encode T2 g final s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 2 * ((h : ℚ≥0) + 2) ^ (2 - 1) * ((h : ℚ≥0) + 1 + 2 ^ 2)) := by
  by_cases ht : x.2 = y.2
  · rw [halftimeCore_equal_tail encode T2 g final s x y ht b]
    have hp : x.1 ≠ y.1 := fun he => hxy (Prod.ext he ht)
    have he : (h : ℚ≥0) + 1 + 2 ^ 2 = (h : ℚ≥0) + 5 := by ring
    rw [he]
    exact forestCore_two_bound encode hdistance g final hg hf s x.1 y.1 hp b
  · apply le_min (uniformProb_le_one _)
    apply (halftimeCore_different_tail encode T2 g final s x y ht b).trans
    have h1 : (1 : ℚ≥0) ≤ ((h : ℚ≥0) + 2) ^ (2 - 1) :=
      one_le_pow₀ (le_trans (by norm_num : (1 : ℚ≥0) ≤ 2) (le_add_of_nonneg_left (zero_le _)))
    have h2 : (1 : ℚ≥0) ≤ (h : ℚ≥0) + 1 + 2 ^ 2 :=
      (le_add_of_nonneg_left (zero_le (h : ℚ≥0))).trans (le_add_of_nonneg_right (by positivity))
    calc
      _ = (1 / (2 : ℚ≥0) ^ 32) ^ 2 * 1 * 1 := by ring
      _ ≤ _ := by gcongr

/-- End-to-end abstract construction, including both equal-tail and
unequal-tail comparisons. Tail conditioning contributes no additive term. -/
theorem halftimeCore_three_bound {X I K J : Type*} [Fintype K] [Nonempty K]
    [Fintype J] [Nonempty J] {n f h l : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (g : Fin 3 → K → (Fin f → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (final : Fin 3 → J → (I → ZMod (2 ^ 64)) → ZMod (2 ^ 64))
    (hg : ∀ row x y, x ≠ y → uniformProb (fun k => g row k x = g row k y) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (hf : ∀ row x y, x ≠ y → ∀ t,
      uniformProb (fun k => final row k x - final row k y = t) ≤ 1 / (2 : ℚ≥0) ^ 32)
    (s : I → TreeShape f h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k => halftimeCore encode T3 g final s x k - halftimeCore encode T3 g final s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 3 * ((h : ℚ≥0) + 2) ^ (3 - 1) * ((h : ℚ≥0) + 1 + 2 ^ 2)) := by
  by_cases ht : x.2 = y.2
  · rw [halftimeCore_equal_tail encode T3 g final s x y ht b]
    have hp : x.1 ≠ y.1 := fun he => hxy (Prod.ext he ht)
    have he : (h : ℚ≥0) + 1 + 2 ^ 2 = (h : ℚ≥0) + 5 := by ring
    rw [he]
    exact forestCore_three_bound encode hdistance g final hg hf s x.1 y.1 hp b
  · apply le_min (uniformProb_le_one _)
    apply (halftimeCore_different_tail encode T3 g final s x y ht b).trans
    have h1 : (1 : ℚ≥0) ≤ ((h : ℚ≥0) + 2) ^ (3 - 1) :=
      one_le_pow₀ (le_trans (by norm_num : (1 : ℚ≥0) ≤ 2) (le_add_of_nonneg_left (zero_le _)))
    have h2 : (1 : ℚ≥0) ≤ (h : ℚ≥0) + 1 + 2 ^ 2 :=
      (le_add_of_nonneg_left (zero_le (h : ℚ≥0))).trans (le_add_of_nonneg_right (by positivity))
    calc
      _ = (1 / (2 : ℚ≥0) ^ 32) ^ 3 * 1 * 1 := by ring
      _ ≤ _ := by gcongr

/-- Tree NH with an unhashed 64-bit accumulator, under an injective packing
of the child list into hashed half-word pairs and that accumulator. -/
def nhNode {f nt : ℕ}
    (pack : (Fin f → ZMod (2 ^ 64)) →
      ((Fin nt × Bool → ZMod (2 ^ 32)) × ZMod (2 ^ 32 * 2 ^ 32)))
    (key : Fin nt × Bool → ZMod (2 ^ 32)) (x : Fin f → ZMod (2 ^ 64)) : ZMod (2 ^ 64) :=
  nh32Equiv (nhLast (pack x) key)

theorem nhNode_au {f nt : ℕ}
    (pack : (Fin f → ZMod (2 ^ 64)) →
      ((Fin nt × Bool → ZMod (2 ^ 32)) × ZMod (2 ^ 32 * 2 ^ 32)))
    (hinj : Function.Injective pack) (x y : Fin f → ZMod (2 ^ 64)) (hxy : x ≠ y) :
    uniformProb (fun key => nhNode pack key x = nhNode pack key y) ≤ 1 / (2 : ℚ≥0) ^ 32 := by
  have H := nhLast_au (pack x) (pack y) (fun he => hxy (hinj he))
  simpa only [nhNode, nh32Equiv.injective.eq_iff, Nat.cast_pow, Nat.cast_ofNat] using H

/-- Integer-NH instantiation of the full abstract construction. Its only
hash-structural hypotheses are encoder distance and injective word packings;
no collision-probability hypothesis remains. -/
theorem halftimeCore_two_nh_bound {X I : Type*} {n nt nf f h l : ℕ}
    (encode : X → Fin 7 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode x (j i) ≠ encode y (j i))
    (treePack : (Fin f → ZMod (2 ^ 64)) →
      ((Fin nt × Bool → ZMod (2 ^ 32)) × ZMod (2 ^ 32 * 2 ^ 32)))
    (htree : Function.Injective treePack)
    (finalPack : (I → ZMod (2 ^ 64)) → (Fin nf × Bool → ZMod (2 ^ 32)))
    (hfinal : Function.Injective finalPack)
    (s : I → TreeShape f h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T2 (fun _ => nhNode treePack) (fun _ key v => nh32 (finalPack v) key) s x k -
      halftimeCore encode T2 (fun _ => nhNode treePack) (fun _ key v => nh32 (finalPack v) key) s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 2 * ((h : ℚ≥0) + 2) ^ (2 - 1) * ((h : ℚ≥0) + 1 + 2 ^ 2)) := by
  exact halftimeCore_two_bound encode hdistance _ _
    (fun _ u v huv => nhNode_au treePack htree u v huv)
    (fun _ u v huv t => nh32_adu (finalPack u) (finalPack v) (fun he => huv (hfinal he)) t) s x y hxy b

/-- Integer-NH instantiation of the full abstract construction. Its only
hash-structural hypotheses are encoder distance and injective word packings;
no collision-probability hypothesis remains. -/
theorem halftimeCore_three_nh_bound {X I : Type*} {n nt nf f h l : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (treePack : (Fin f → ZMod (2 ^ 64)) →
      ((Fin nt × Bool → ZMod (2 ^ 32)) × ZMod (2 ^ 32 * 2 ^ 32)))
    (htree : Function.Injective treePack)
    (finalPack : (I → ZMod (2 ^ 64)) → (Fin nf × Bool → ZMod (2 ^ 32)))
    (hfinal : Function.Injective finalPack)
    (s : I → TreeShape f h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T3 (fun _ => nhNode treePack) (fun _ key v => nh32 (finalPack v) key) s x k -
      halftimeCore encode T3 (fun _ => nhNode treePack) (fun _ key v => nh32 (finalPack v) key) s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 3 * ((h : ℚ≥0) + 2) ^ (3 - 1) * ((h : ℚ≥0) + 1 + 2 ^ 2)) := by
  exact halftimeCore_three_bound encode hdistance _ _
    (fun _ u v huv => nhNode_au treePack htree u v huv)
    (fun _ u v huv t => nh32_adu (finalPack u) (finalPack v) (fun he => huv (hfinal he)) t) s x y hxy b

/-- Numerical end-to-end AΔU corollary for k=3, t=2, h=16, with integer NH
at every stage and the separately keyed, shared-pool Toeplitz tail. -/
theorem halftime_6804 {X I : Type*} {n nt nf f l : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (treePack : (Fin f → ZMod (2 ^ 64)) →
      ((Fin nt × Bool → ZMod (2 ^ 32)) × ZMod (2 ^ 32 * 2 ^ 32)))
    (htree : Function.Injective treePack)
    (finalPack : (I → ZMod (2 ^ 64)) → (Fin nf × Bool → ZMod (2 ^ 32)))
    (hfinal : Function.Injective finalPack)
    (s : I → TreeShape f 16)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T3 (fun _ => nhNode treePack) (fun _ key v => nh32 (finalPack v) key) s x k -
      halftimeCore encode T3 (fun _ => nhNode treePack) (fun _ key v => nh32 (finalPack v) key) s y k = b) ≤
      6804 / (2 : ℚ≥0) ^ 96 := by
  exact (halftimeCore_three_nh_bound encode hdistance treePack htree finalPack hfinal s x y hxy b).trans
    (by norm_num)

/-- Concrete scalar-word construction. Child and root packing are the actual
low/high 32-bit decompositions, and the last child is passed through unhashed. -/
theorem scalar_halftime_two_bound {X : Type*} {n nt roots h l : ℕ}
    (encode : X → Fin 7 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode x (j i) ≠ encode y (j i))
    (s : Fin roots → TreeShape (nt + 1) h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T2 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s x k -
      halftimeCore encode T2 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 2 * ((h : ℚ≥0) + 2) ^ (2 - 1) * ((h : ℚ≥0) + 1 + 2 ^ 2)) := by
  exact halftimeCore_two_nh_bound encode hdistance packTree packTree_injective
    packWords packWords_injective s x y hxy b

/-- Concrete scalar-word construction. Child and root packing are the actual
low/high 32-bit decompositions, and the last child is passed through unhashed. -/
theorem scalar_halftime_three_bound {X : Type*} {n nt roots h l : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (s : Fin roots → TreeShape (nt + 1) h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T3 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s x k -
      halftimeCore encode T3 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s y k = b) ≤
      min 1 ((1 / (2 : ℚ≥0) ^ 32) ^ 3 * ((h : ℚ≥0) + 2) ^ (3 - 1) * ((h : ℚ≥0) + 1 + 2 ^ 2)) := by
  exact halftimeCore_three_nh_bound encode hdistance packTree packTree_injective
    packWords packWords_injective s x y hxy b

theorem scalar_halftime_6804 {X : Type*} {n nt roots l : ℕ}
    (encode : X → Fin 9 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 3 ↪ Fin 9, ∀ i, encode x (j i) ≠ encode y (j i))
    (s : Fin roots → TreeShape (nt + 1) 16)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 3 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T3 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s x k -
      halftimeCore encode T3 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s y k = b) ≤
      6804 / (2 : ℚ≥0) ^ 96 := by
  exact (scalar_halftime_three_bound encode hdistance s x y hxy b).trans (by norm_num)

end ProvenHashes.Halftime
