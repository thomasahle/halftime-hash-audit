import ProvenHashes.Composition

namespace ProvenHashes
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem uniformProb_le_one {K : Type*} [Fintype K] (E : K → Prop) :
    uniformProb E ≤ 1 := by
  classical
  unfold uniformProb
  exact div_le_one_of_le₀ (by exact_mod_cast Finset.card_filter_le _ _) (by positivity)

theorem uniformProb_of_injective {K V : Type*} [Fintype K]
    (f : K → V) (hf : Function.Injective f) (v : V) :
    uniformProb (fun k => f k = v) ≤ 1 / Fintype.card K := by
  classical
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (Finset.univ.filter fun k => f k = v).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact hf ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  exact_mod_cast hc

/-- A single exposed uniform key coordinate suffices; the output need not have
the same cardinality as that coordinate. -/
theorem uniformProb_of_injective_update {I V O : Type*}
    [Fintype I] [Fintype V] [Nonempty V] [DecidableEq I]
    (f : (I → V) → O) (i : I)
    (h : ∀ k, Function.Injective (fun v => f (Function.update k i v))) (t : O) :
    uniformProb (fun k => f k = t) ≤ 1 / Fintype.card V := by
  classical
  let split := Equiv.funSplitAt i V
  let v₀ : V := Classical.choice inferInstance
  have hu (r : {j // j ≠ i} → V) (v : V) :
      split.symm (v, r) = Function.update (split.symm (v₀, r)) i v := by
    funext j
    by_cases hj : j = i
    · subst j; simp [split]
    · simp [split, Function.update, hj]
  let e : (({j // j ≠ i} → V) × V) ≃ (I → V) :=
    (Equiv.prodComm _ _).trans split.symm
  calc
    _ = uniformProb (fun p : ({j // j ≠ i} → V) × V =>
          f (split.symm (p.2, p.1)) = t) :=
      (uniformProb_equiv e (fun k => f k = t)).symm
    _ ≤ 1 / Fintype.card V := by
      apply uniformProb_prod_le
      intro r
      apply uniformProb_of_injective
      intro u v huv
      apply h (split.symm (v₀, r))
      change f (Function.update (split.symm (v₀, r)) i u) =
        f (Function.update (split.symm (v₀, r)) i v)
      rw [← hu r u, ← hu r v]
      exact huv

theorem uniformProb_eq_card_subtype {K : Type*} [Fintype K] (E : K → Prop) :
    uniformProb E = (Nat.card {k // E k} : ℚ≥0) / Fintype.card K := by
  classical
  simp [uniformProb, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Independent coordinates: this is a counting identity, not an independence
assumption about derived hash outputs. -/
theorem uniformProb_pi {I : Type*} [Fintype I] [DecidableEq I]
    {K : I → Type*} [∀ i, Fintype (K i)] (E : ∀ i, K i → Prop) :
    uniformProb (fun k : ∀ i, K i => ∀ i, E i (k i)) = ∏ i, uniformProb (E i) := by
  classical
  have hc : Nat.card {k : ∀ i, K i // ∀ i, E i (k i)} =
      ∏ i, Nat.card {k : K i // E i k} :=
    (Nat.card_congr (Equiv.subtypePiEquivPi (p := E))).trans Nat.card_pi
  simp only [uniformProb_eq_card_subtype, hc, Nat.cast_prod, Fintype.card_pi, Finset.prod_div_distrib]

theorem uniformProb_preimage {K V : Type*} [Fintype K] [Fintype V]
    (f : K → V) (E : V → Prop) [DecidablePred E] :
    uniformProb (fun k => E (f k)) = ∑ v ∈ Finset.univ.filter E, uniformProb (fun k => f k = v) := by
  classical
  unfold uniformProb
  rw [← Finset.sum_div, ← Nat.cast_sum]
  congr 1
  have h := (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset K)
      (Finset.univ.filter E) f).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hc : (Finset.univ.filter (fun k => E (f k))).card =
      ∑ v ∈ Finset.univ.filter E, (Finset.univ.filter (fun k => f k = v)).card := by
    convert h using 1
  convert congrArg (fun n : ℕ => (n : ℚ≥0)) hc using 1
  congr 1
  congr 1
  ext k
  simp

theorem uniformProb_preimage_le {K V : Type*} [Fintype K] [Fintype V]
    (f : K → V) (E : V → Prop) (a : ℚ≥0)
    (ha : ∀ v, uniformProb (fun k => f k = v) ≤ a) :
    uniformProb (fun k => E (f k)) ≤ (Nat.card {v // E v} : ℚ≥0) * a := by
  classical
  rw [uniformProb_preimage]
  calc
    _ ≤ ∑ _v ∈ Finset.univ.filter E, a := Finset.sum_le_sum (fun v _ => ha v)
    _ = _ := by simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Conditioning on every key except one coordinate. -/
theorem uniformProb_of_update_bound {I V O : Type*}
    [Fintype I] [Fintype V] [Nonempty V] [DecidableEq I]
    (f : (I → V) → O) (i : I) (t : O) (a : ℚ≥0)
    (h : ∀ k, uniformProb (fun v => f (Function.update k i v) = t) ≤ a) :
    uniformProb (fun k => f k = t) ≤ a := by
  classical
  let split := Equiv.funSplitAt i V
  let v₀ : V := Classical.choice inferInstance
  have hu (r : {j // j ≠ i} → V) (v : V) :
      split.symm (v, r) = Function.update (split.symm (v₀, r)) i v := by
    funext j
    by_cases hj : j = i
    · subst j; simp [split]
    · simp [split, Function.update, hj]
  let e : (({j // j ≠ i} → V) × V) ≃ (I → V) :=
    (Equiv.prodComm _ _).trans split.symm
  rw [← uniformProb_equiv e]
  apply uniformProb_prod_le
  intro r
  change uniformProb (fun v => f (split.symm (v, r)) = t) ≤ a
  convert h (split.symm (v₀, r)) using 1
  congr 1
  funext v
  exact congrArg (fun k => f k = t) (hu r v)

/-- A fibre injects into a finite set of tags if the map is injective within
each tag. This is useful for piecewise affine unsigned arithmetic. -/
theorem uniformProb_of_tag_injective {K O B : Type*} [Fintype K] [Fintype B]
    (f : K → O) (tag : K → B)
    (h : ∀ u v, tag u = tag v → f u = f v → u = v) (t : O) :
    uniformProb (fun k => f k = t) ≤ (Fintype.card B : ℚ≥0) / Fintype.card K := by
  classical
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (Finset.univ.filter fun k => f k = t).card ≤ (Finset.univ : Finset B).card := by
    apply Finset.card_le_card_of_injOn tag (fun _ _ => Finset.mem_univ _)
    intro u hu v hv he
    exact h u v he ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  exact_mod_cast hc

end ProvenHashes
