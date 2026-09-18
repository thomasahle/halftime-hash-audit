import ProvenHashes.Halftime.Construction
import ProvenHashes.Halftime.Survival
import ProvenHashes.Halftime.SharpT2

namespace ProvenHashes.Halftime
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem forestCore_component_survival {X I K J : Type*} [Fintype K] [Nonempty K]
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
      failure (1 / (2 : ℚ≥0) ^ 32) (h + 1) := by
  have hε : (1 / (2 : ℚ≥0) ^ 32) ≤ 1 := by
    exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 32) ≤ 1)
  apply forest_final_survival (g row) _ hε (hg row) s _ _ _ (final row) (hf row) t
  intro he
  have hv := congrArg (fun z => leafValue (s root) (z root) p) he
  simp only [leafValue_map] at hv
  exact hne hv

/-- The sharp B₂(h) bound with the concrete T2 projection probabilities
discharged by integer NH, including its sharp reduction modulo 2^62. -/
theorem forestCore_two_survival {X I K J : Type*} [Fintype K] [Nonempty K]
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
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
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
      failure (1 / (2 : ℚ≥0) ^ 32) (h + 1) := by
    apply forestCore_component_survival encode T2 g final hg hf s x y root p key row _ (b row)
    intro he
    have hh := congrFun (ehc_difference_eq_combine encode T2 u v key) row
    change ehc encode T2 u key row - ehc encode T2 v key row = combine T2 d key row at hh
    exact hne (hh.symm.trans (sub_eq_zero.mpr he))
  have hs := nh_T2_sharp_subset_bounds (encode u) (encode v) j hj 0
  have hε : (1 / (2 : ℚ≥0) ^ 32) ≤ 1 := by
    exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 32) ≤ 1)
  have H := end_to_end_two_survival_from_subsets E C (1 / 2 ^ 32) hε h hc
    (by simpa [E, d, mul_one_div] using hs.1)
    (by norm_num [E, d] at hs ⊢; exact hs.2)
  simpa [forestCore, funext_iff, C] using H

theorem epsilon_sq_le_styleTwoBound (ε : ℚ≥0) (hε : ε ≤ 1) (h : ℕ) :
    ε ^ 2 ≤ styleTwoBound ε h := by
  have he : ε ≤ failure ε (h + 1) + survival ε (h + 1) * ε := by
    calc
      _ = (failure ε (h + 1) + survival ε (h + 1)) * ε := by rw [failure_add_survival ε hε, one_mul]
      _ = failure ε (h + 1) * ε + survival ε (h + 1) * ε := by ring
      _ ≤ _ := add_le_add_right (mul_le_of_le_one_right (zero_le _) hε) _
  calc
    _ = ε * ε := pow_two ε
    _ ≤ (failure ε (h + 1) + survival ε (h + 1) * ε) *
        (failure ε (h + 1) + survival ε (h + 1) * ε) := by gcongr
    _ ≤ styleTwoBound ε h := by
      unfold styleTwoBound
      gcongr
      exact le_mul_of_one_le_left (zero_le _) (by norm_num)

theorem halftimeCore_two_survival {X I K J : Type*} [Fintype K] [Nonempty K]
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
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
  by_cases ht : x.2 = y.2
  · rw [halftimeCore_equal_tail encode T2 g final s x y ht b]
    exact forestCore_two_survival encode hdistance g final hg hf s x.1 y.1
      (fun he => hxy (Prod.ext he ht)) b
  · exact (halftimeCore_different_tail encode T2 g final s x y ht b).trans
      (epsilon_sq_le_styleTwoBound _
        (by exact_mod_cast (by norm_num : (1 / (2 : ℚ) ^ 32) ≤ 1)) h)

/-- Sharp scalar-word distance-2 construction theorem. There are no assumed
projection probabilities or stage collision bounds in this statement. -/
theorem scalar_halftime_two_survival {X : Type*} {n nt roots h l : ℕ}
    (encode : X → Fin 7 → (Fin n × Bool → ZMod (2 ^ 32)))
    (hdistance : ∀ x y, x ≠ y → ∃ j : Fin 2 ↪ Fin 7, ∀ i, encode x (j i) ≠ encode y (j i))
    (s : Fin roots → TreeShape (nt + 1) h)
    (x y : (∀ i, TreeInput X (s i)) × (Fin l × Bool → ZMod (2 ^ 32))) (hxy : x ≠ y)
    (b : Fin 2 → ZMod (2 ^ 64)) :
    uniformProb (fun k =>
      halftimeCore encode T2 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s x k -
      halftimeCore encode T2 (fun _ => nhNode packTree) (fun _ key v => nh32 (packWords v) key) s y k = b) ≤
      styleTwoBound (1 / (2 : ℚ≥0) ^ 32) h := by
  exact halftimeCore_two_survival encode hdistance _ _
    (fun _ u v huv => nhNode_au packTree packTree_injective u v huv)
    (fun _ u v huv t => nh32_adu (packWords u) (packWords v)
      (fun he => huv (packWords_injective he)) t) s x y hxy b

end ProvenHashes.Halftime
