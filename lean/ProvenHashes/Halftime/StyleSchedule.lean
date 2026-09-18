import ProvenHashes.Halftime.StyleModel

namespace ProvenHashes.Halftime
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def stackCapacity : ℕ → ℕ
  | 0 => 0
  | f + 1 => 8 + 8 * stackCapacity f

theorem stackCapacity_eight : stackCapacity 8 = 19173960 := by decide

/-- Low-level-first root heights for bijective base eight. The recursion
reserves eight live levels; the ninth array slot is the zero sentinel. -/
def lazyHeights : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else
      List.replicate ((n - 1) % 8 + 1) 0 ++ (lazyHeights f ((n - 1) / 8)).map Nat.succ

theorem sum_eight_pow_succ (xs : List ℕ) :
    ((xs.map Nat.succ).map (fun j => 8 ^ j)).sum = 8 * (xs.map (fun j => 8 ^ j)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.succ_eq_add_one, pow_succ, ih]
    omega

theorem lazyHeights_spec (f n : ℕ) (hn : n ≤ stackCapacity f) :
    (lazyHeights f n).length ≤ 8 * f ∧
      ((lazyHeights f n).map (fun j => 8 ^ j)).sum = n ∧
      ∀ j ∈ lazyHeights f n, j < f := by
  induction f generalizing n with
  | zero =>
    have hz : n = 0 := by simpa [stackCapacity] using hn
    simp [lazyHeights, hz]
  | succ f ih =>
    by_cases hz : n = 0
    · simp [lazyHeights, hz]
    · have hm := Nat.mod_add_div (n - 1) 8
      have hd := Nat.mod_lt (n - 1) (by decide : 0 < 8)
      have hq : (n - 1) / 8 ≤ stackCapacity f := by
        have hs : n ≤ 8 + 8 * stackCapacity f := hn
        omega
      obtain ⟨hlen, hsum, hdepth⟩ := ih _ hq
      have hn' : (n - 1) % 8 + 1 + 8 * ((n - 1) / 8) = n := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [lazyHeights, hz, if_false, List.length_append, List.length_replicate, List.length_map]
        omega
      · simp only [lazyHeights, hz, if_false, List.map_append, List.map_replicate,
          pow_zero, List.sum_append, List.sum_replicate, nsmul_eq_mul, mul_one]
        rw [sum_eight_pow_succ, hsum]
        exact hn'
      · intro j hj
        simp only [lazyHeights, hz, if_false, List.mem_append] at hj
        rcases hj with hj | hj
        · have he := (List.mem_replicate.mp hj).2
          omega
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
          exact Nat.succ_lt_succ (hdepth i hi)

def maxRootHeight : List ℕ → ℕ
  | [] => 0
  | j :: js => max j (maxRootHeight js)

theorem le_maxRootHeight {js : List ℕ} {j : ℕ} (hj : j ∈ js) : j ≤ maxRootHeight js := by
  induction js with
  | nil => simp at hj
  | cons x xs ih =>
    rcases List.mem_cons.mp hj with rfl | hm
    · exact le_max_left _ _
    · exact (ih hm).trans (le_max_right _ _)

theorem maxRootHeight_le {js : List ℕ} {h : ℕ} (hh : ∀ j ∈ js, j ≤ h) :
    maxRootHeight js ≤ h := by
  induction js with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    apply max_le
    · exact hh x List.mem_cons_self
    · exact ih (fun j hj => hh j (List.mem_cons_of_mem _ hj))

theorem maxRootHeight_load {js : List ℕ} (hne : js ≠ []) :
    8 ^ maxRootHeight js ≤ (js.map (fun j => 8 ^ j)).sum := by
  induction js with
  | nil => exact (hne rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => simp [maxRootHeight]
    | cons y ys =>
      have hi := ih (by simp)
      change 8 ^ max x (maxRootHeight (y :: ys)) ≤
        8 ^ x + ((y :: ys).map (fun j => 8 ^ j)).sum
      by_cases hx : x ≤ maxRootHeight (y :: ys)
      · rw [max_eq_right hx]
        exact hi.trans (Nat.le_add_left _ _)
      · rw [max_eq_left (by omega : maxRootHeight (y :: ys) ≤ x)]
        exact Nat.le_add_right _ _

noncomputable instance leafPathFintype {f h : ℕ} (s : TreeShape f h) : Fintype (LeafPath s) := by
  induction s with
  | leaf => exact inferInstanceAs (Fintype PUnit)
  | skip s ih => exact ih
  | node s ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Σ i, LeafPath (s i)))

def treeLeafCount {f : ℕ} : {h : ℕ} → TreeShape f h → ℕ
  | _, .leaf => 1
  | _, .skip s => treeLeafCount s
  | _, .node s => ∑ i, treeLeafCount (s i)

theorem leafPath_card {f h : ℕ} (s : TreeShape f h) : Fintype.card (LeafPath s) = treeLeafCount s := by
  induction s with
  | leaf => exact Fintype.card_punit
  | skip s ih => exact ih
  | node s ih =>
    change Fintype.card (Σ i, LeafPath (s i)) = _
    simp only [Fintype.card_sigma, treeLeafCount, ih]

def fullShape : (h : ℕ) → TreeShape 8 h
  | 0 => .leaf
  | h + 1 => .node (fun _ => fullShape h)

theorem fullShape_count (h : ℕ) : treeLeafCount (fullShape h) = 8 ^ h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [fullShape, treeLeafCount, ih, pow_succ, Nat.mul_comm]

def raiseShape {f h : ℕ} (s : TreeShape f h) : (extra : ℕ) → TreeShape f (h + extra)
  | 0 => s
  | extra + 1 => .skip (raiseShape s extra)

theorem raiseShape_count {f h : ℕ} (s : TreeShape f h) (extra : ℕ) :
    treeLeafCount (raiseShape s extra) = treeLeafCount s := by
  induction extra with
  | zero => rfl
  | succ extra ih => exact ih

theorem treeLeafCount_cast {f a b : ℕ} (he : a = b) (s : TreeShape f a) :
    treeLeafCount (he ▸ s) = treeLeafCount s := by subst b; rfl

def paddedFull (h j : ℕ) (hj : j ≤ h) : TreeShape 8 h :=
  (show j + (h - j) = h by omega) ▸ raiseShape (fullShape j) (h - j)

theorem paddedFull_count (h j : ℕ) (hj : j ≤ h) : treeLeafCount (paddedFull h j hj) = 8 ^ j := by
  unfold paddedFull
  rw [treeLeafCount_cast, raiseShape_count, fullShape_count]

def lazyShapes (n : ℕ) : Fin (lazyHeights 8 n).length → TreeShape 8 (maxRootHeight (lazyHeights 8 n)) :=
  fun i => paddedFull _ ((lazyHeights 8 n).get i) (le_maxRootHeight (List.get_mem _ i))

theorem list_eight_pow_sum (xs : List ℕ) :
    (∑ i : Fin xs.length, 8 ^ xs.get i) = (xs.map (fun j => 8 ^ j)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Fin.sum_univ_succ, ih]

theorem lazyShapes_card (n : ℕ) (hn : n ≤ 19173960) :
    Fintype.card (Σ i, LeafPath (lazyShapes n i)) = n := by
  have hs := (lazyHeights_spec 8 n (by rwa [stackCapacity_eight])).2.1
  simp only [Fintype.card_sigma, leafPath_card, lazyShapes, paddedFull_count]
  rw [list_eight_pow_sum, hs]

/-- The order is any fixed public bijection between chronological group
indices and tree leaves. Collision bounds are uniform over every such order. -/
noncomputable def lazySchedule (n : ℕ) (hn : n ≤ 19173960) : StyleSchedule n where
  height := maxRootHeight (lazyHeights 8 n)
  roots := (lazyHeights 8 n).length
  shape := lazyShapes n
  order := Fintype.equivOfCardEq (by rw [lazyShapes_card n hn, Fintype.card_fin])
  height_le := by
    have hs := (lazyHeights_spec 8 n (by rwa [stackCapacity_eight])).2.2
    exact (maxRootHeight_le (fun j hj => Nat.le_of_lt (hs j hj))).trans (by decide : 8 ≤ 9)
  roots_le := (lazyHeights_spec 8 n (by rwa [stackCapacity_eight])).1
  height_load := by
    intro hne
    have hs := (lazyHeights_spec 8 n (by rwa [stackCapacity_eight])).2.1
    have hl : lazyHeights 8 n ≠ [] := by
      intro he
      rw [he] at hs
      exact hne (by simpa using hs.symm)
    exact (maxRootHeight_load hl).trans_eq hs

theorem styleGroups_stack_safe {b : ℕ} (hb : 0 < b) (bytes : Fin (styleByteLimit b)) :
    styleGroups b bytes.val ≤ 19173960 := by
  have h := bytes.isLt
  unfold styleByteLimit at h
  unfold styleGroups
  have hd : bytes.val / (144 * b) < 19173960 + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 144 * b)).mpr (by nlinarith)
  omega

noncomputable def lazyScheduleFamily (b : ℕ) (hb : 0 < b) : StyleScheduleFamily b :=
  fun bytes => lazySchedule (styleGroups b bytes.val) (styleGroups_stack_safe hb bytes)

theorem lazySchedule_height_le_seven (n : ℕ) (hn : n ≤ 19173960) : (lazySchedule n hn).height ≤ 7 := by
  apply maxRootHeight_le
  intro j hj
  have hs := (lazyHeights_spec 8 n (by rwa [stackCapacity_eight])).2.2 j hj
  omega

theorem styleByteLimits :
    styleByteLimit 1 = 2761050384 ∧ styleByteLimit 2 = 5522100768 ∧
      styleByteLimit 4 = 11044201536 ∧ styleByteLimit 8 = 22088403072 := by decide

/-- A fully instantiated abstract family, with bijective-base-eight root
counts, complete trees, literal flat addresses, byte loading and zero padding. -/
noncomputable def modeledStyleHash {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (x : StyleMessage b) (key : Fin 6144 → XorWord 64) : XorWord 64 :=
  byteStyleHash hb0 hb (lazyScheduleFamily b hb0) x key

theorem modeledStyleHash_normalized {b : ℕ} (hb0 : 0 < b) (hb : b ≤ 8)
    (L : ℕ) (hL : 1 ≤ L) (x y : StyleMessage b) (hxy : x ≠ y)
    (hx : x.1.val ≤ 8 * L) (hy : y.1.val ≤ 8 * L) :
    uniformProb (fun key => modeledStyleHash hb0 hb x key = modeledStyleHash hb0 hb y key) ≤
      (L : ℚ≥0) * (1 / 2 ^ 63 - 1 / 2 ^ 128) :=
  byteStyleHash_normalized hb0 hb (lazyScheduleFamily b hb0) L hL x y hxy hx hy

end ProvenHashes.Halftime
