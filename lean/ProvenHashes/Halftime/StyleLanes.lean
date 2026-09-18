import ProvenHashes.Halftime.Encoding

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

abbrev Word32 := ZMod (2 ^ 32)
abbrev Word64 := ZMod (2 ^ 64)
abbrev PairKey (n : ℕ) := Fin n × Bool → Word32

/-- The header carries child zero and hashes children one through seven. -/
def headTreePack {m : ℕ} (x : Fin (m + 1) → Word64) :
    PairKey m × ZMod (2 ^ 32 * 2 ^ 32) :=
  (packWords (fun i => x i.succ), nh32Equiv.symm (x 0))

theorem headTreePack_injective {m : ℕ} : Function.Injective (@headTreePack m) := by
  intro x y he
  have h0 : x 0 = y 0 := nh32Equiv.symm.injective (congrArg Prod.snd he)
  have hs : (fun i : Fin m => x i.succ) = (fun i => y i.succ) :=
    packWords_injective (congrArg Prod.fst he)
  funext i
  exact Fin.cases h0 (fun j => congrFun hs j) i

/-- EHC and tree keys are broadcast across physical lanes. -/
noncomputable def styleLeaf {b : ℕ} (x : Fin b → Encode2Input)
    (key : Fin 7 → PairKey 3) (row : Fin 2) (lane : Fin b) : Word64 :=
  ehc encode2 T2 (x lane) key row

def styleNode {b : ℕ} (key : PairKey 7) (x : Fin 8 → Fin b → Word64) : Fin b → Word64 :=
  fun lane => nhNode headTreePack key (fun i => x i lane)

theorem styleNode_au {b : ℕ} (x y : Fin 8 → Fin b → Word64) (hxy : x ≠ y) :
    uniformProb (fun key => styleNode key x = styleNode key y) ≤ 1 / (2 : ℚ≥0) ^ 32 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  obtain ⟨lane, hl⟩ := Function.ne_iff.mp hi
  have hs : (fun j => x j lane) ≠ (fun j => y j lane) := fun he => hl (congrFun he i)
  exact (uniformProb_mono (fun _ he => congrFun he lane)).trans
    (nhNode_au headTreePack headTreePack_injective _ _ hs)

/-- Root-major, lane-minor flattening for the horizontal NH sum. -/
def flattenBlocks {roots b : ℕ} (x : Fin roots → Fin b → Word64) : Fin (roots * b) → Word64 :=
  fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem flattenBlocks_injective {roots b : ℕ} : Function.Injective (@flattenBlocks roots b) := by
  intro x y he
  funext i lane
  simpa [flattenBlocks] using congrFun he (finProdFinEquiv (i, lane))

/-- Unlike the broadcast tree keys, finalizer keys are independent per lane. -/
def styleFinal {roots b : ℕ} (key : PairKey (roots * b)) (x : Fin roots → Fin b → Word64) : Word64 :=
  nh32 (packWords (flattenBlocks x)) key

theorem styleFinal_adu {roots b : ℕ} (x y : Fin roots → Fin b → Word64)
    (hxy : x ≠ y) (t : Word64) :
    uniformProb (fun key => styleFinal key x - styleFinal key y = t) ≤ 1 / (2 : ℚ≥0) ^ 32 := by
  exact nh32_adu _ _ (fun he => hxy (flattenBlocks_injective (packWords_injective he))) t

abbrev StyleForestKey (b h roots : ℕ) :=
  (Fin 7 → PairKey 3) × (Fin 2 → LevelKeys (PairKey 7) h × PairKey (roots * b))

noncomputable def styleForest {b h roots : ℕ} (s : Fin roots → TreeShape 8 h)
    (x : ∀ i, TreeInput (Fin b → Encode2Input) (s i)) (key : StyleForestKey b h roots) : Fin 2 → Word64 :=
  fun row => styleFinal (key.2 row).2 (forestHash styleNode s
    (fun i => mapLeaves (fun v => styleLeaf v key.1 row) (s i) (x i)) (key.2 row).1)

/-- Sharp B₂(h) for whole blocks with the header's broadcast keys and
independent finalizer lane keys. No lane independence is assumed. -/
theorem styleForest_survival {b h roots : ℕ} (s : Fin roots → TreeShape 8 h)
    (x y : ∀ i, TreeInput (Fin b → Encode2Input) (s i)) (hxy : x ≠ y)
    (target : Fin 2 → Word64) :
    uniformProb (fun key => styleForest s x key - styleForest s y key = target) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
  classical
  obtain ⟨root, hr⟩ := Function.ne_iff.mp hxy
  obtain ⟨p, hp⟩ := exists_differing_leaf (s root) (x root) (y root) hr
  obtain ⟨lane, hl⟩ := Function.ne_iff.mp hp
  let u := leafValue (s root) (x root) p lane
  let v := leafValue (s root) (y root) p lane
  obtain ⟨j, hj⟩ := encode2_distance u v hl
  let d (i : Fin 7) (key : PairKey 3) := nh32 (encode2 u i) key - nh32 (encode2 v i) key
  let E (row : Fin 2) (key : Fin 7 → PairKey 3) := combine T2 d key row = 0
  let C (key : Fin 7 → PairKey 3) (row : Fin 2)
      (k : LevelKeys (PairKey 7) h × PairKey (roots * b)) :=
    styleFinal k.2 (forestHash styleNode s
      (fun i => mapLeaves (fun z => styleLeaf z key row) (s i) (x i)) k.1) -
    styleFinal k.2 (forestHash styleNode s
      (fun i => mapLeaves (fun z => styleLeaf z key row) (s i) (y i)) k.1) = target row
  have hε : (1 / (2 : ℚ≥0) ^ 32) ≤ 1 := by
    exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 32) ≤ 1)
  have hc (key) (row) (hne : ¬ E row key) : uniformProb (C key row) ≤
      failure (1 / (2 : ℚ≥0) ^ 32) (h + 1) := by
    apply forest_final_survival styleNode _ hε styleNode_au s _ _ _ styleFinal styleFinal_adu (target row)
    intro he
    have hv := congrArg (fun z : ∀ i, TreeInput (Fin b → Word64) (s i) =>
      leafValue (s root) (z root) p lane) he
    simp only [leafValue_map, styleLeaf] at hv
    have hd := congrFun (ehc_difference_eq_combine encode2 T2 u v key) row
    exact hne (hd.symm.trans (sub_eq_zero.mpr hv))
  have hs := nh_T2_sharp_subset_bounds (encode2 u) (encode2 v) j hj 0
  have H := end_to_end_two_survival_from_subsets E C (1 / 2 ^ 32) hε h hc
    (by simpa [E, d, mul_one_div] using hs.1)
    (by norm_num [E, d] at hs ⊢; exact hs.2)
  simpa only [styleForest, Pi.sub_apply, funext_iff, C] using H

/-- Any increasing selection of Toeplitz offsets admits triangular exposure.
This includes offsets 0 and b, as used by the b-lane Style finalizer. -/
theorem toeplitzNH_selected_adu {n r m : ℕ} (x y : PairKey n) (hxy : x ≠ y)
    (offset : Fin r → Fin m) (hoff : StrictMono offset) (target : Fin r → Word64) :
    uniformProb (fun key => ∀ j,
      toeplitzNH x key (offset j) - toeplitzNH y key (offset j) = target j) ≤
      (1 / (2 : ℚ≥0) ^ 32) ^ r := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ∃ bit, x (i, bit) ≠ y (i, bit))
  have hS : S.Nonempty := by
    obtain ⟨⟨i, bit⟩, hi⟩ := Function.ne_iff.mp hxy
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bit, hi⟩⟩
  let p := S.max' hS
  obtain ⟨bit, hb⟩ := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hafter (a : Fin n) (ha : p < a) (bit : Bool) : x (a, bit) = y (a, bit) := by
    by_contra hn
    exact (not_le_of_gt ha) (Finset.le_max' S a (Finset.mem_filter.mpr ⟨Finset.mem_univ _, bit, hn⟩))
  have H := triangular_adu r (fun j key => toeplitzNH x key (offset j) - toeplitzNH y key (offset j))
    (fun j => shiftEmbedding (offset j) (p, !bit))
    (fun j key => toeplitz_update_injective x y p bit hb (offset j) key)
    (fun i j hij key v => toeplitz_earlier_ignores_update x y p hafter (offset i) (offset j)
      (hoff hij) (!bit) key v) target
  simpa only [ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using H

def styleOffset (b : ℕ) (j : Fin 2) : Fin (b + 1) := ⟨b * j.val, by fin_cases j <;> simp⟩

theorem styleOffset_strictMono {b : ℕ} (hb : 0 < b) : StrictMono (styleOffset b) := by
  intro i j hij
  change b * i.val < b * j.val
  exact Nat.mul_lt_mul_of_pos_left hij hb

/-- The raw suffix flattened to pairs, with the key shift by b whole pairs. -/
def styleTail {b l : ℕ} (x : PairKey l) (key : PairKey (l + (b + 1) - 1)) : Fin 2 → Word64 :=
  fun j => toeplitzNH x key (styleOffset b j)

theorem styleTail_adu {b l : ℕ} (hb : 0 < b) (x y : PairKey l) (hxy : x ≠ y)
    (target : Fin 2 → Word64) :
    uniformProb (fun key => styleTail (b := b) x key - styleTail y key = target) ≤
      (1 / (2 : ℚ≥0) ^ 32) ^ 2 := by
  simpa only [styleTail, funext_iff, Pi.sub_apply] using
    toeplitzNH_selected_adu x y hxy (styleOffset b) (styleOffset_strictMono hb) target

abbrev StyleKey (b h roots l : ℕ) := StyleForestKey b h roots × PairKey (l + (b + 1) - 1)

noncomputable def styleCore {b h roots l : ℕ} (s : Fin roots → TreeShape 8 h)
    (x : (∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey l)
    (key : StyleKey b h roots l) : Fin 2 → Word64 :=
  styleForest s x.1 key.1 + styleTail x.2 key.2

theorem styleCore_different_tail {b h roots l : ℕ} (hb : 0 < b) (s : Fin roots → TreeShape 8 h)
    (x y : (∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey l) (ht : x.2 ≠ y.2)
    (target : Fin 2 → Word64) :
    uniformProb (fun key => styleCore s x key - styleCore s y key = target) ≤
      (1 / (2 : ℚ≥0) ^ 32) ^ 2 := by
  apply uniformProb_prod_le
  intro key
  have he : (fun k => styleCore s x (key, k) - styleCore s y (key, k) = target) =
      (fun k => styleTail (b := b) x.2 k - styleTail y.2 k =
        target - (styleForest s x.1 key - styleForest s y.1 key)) := by
    funext k
    apply propext
    simp only [styleCore]
    rw [add_sub_add_comm, add_comm, eq_sub_iff_add_eq]
  rw [he]
  exact styleTail_adu hb x.2 y.2 ht _

theorem styleCore_survival {b h roots l : ℕ} (hb : 0 < b) (s : Fin roots → TreeShape 8 h)
    (x y : (∀ i, TreeInput (Fin b → Encode2Input) (s i)) × PairKey l) (hxy : x ≠ y)
    (target : Fin 2 → Word64) :
    uniformProb (fun key => styleCore s x key - styleCore s y key = target) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
  by_cases ht : x.2 = y.2
  · have he (key : StyleKey b h roots l) :
        styleCore s x key - styleCore s y key = styleForest s x.1 key.1 - styleForest s y.1 key.1 := by
      simp only [styleCore, ht, add_sub_add_right_eq_sub]
    simp_rw [he]
    rw [uniformProb_prod_fst (J := PairKey (l + (b + 1) - 1))
      (fun key : StyleForestKey b h roots => styleForest s x.1 key - styleForest s y.1 key = target)]
    exact styleForest_survival s x.1 y.1 (fun hx => hxy (Prod.ext hx ht)) target
  · exact (styleCore_different_tail hb s x y ht target).trans
      (epsilon_sq_le_styleTwoBound _
        (by exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 32) ≤ 1)) h)

end ProvenHashes.Halftime
