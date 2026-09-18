import Mathlib

namespace ProvenHashes.Halftime
open scoped BigOperators Matrix
open Module
set_option maxHeartbeats 1000000

/-- Translation identifies every inhabited fibre with the kernel. -/
def fibreEquivKernel {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (x : G) : {y // f y = f x} ≃ {y // f y = 0} where
  toFun y := ⟨y.1 - x, by simp [map_sub, y.2]⟩
  invFun y := ⟨y.1 + x, by simp [map_add, y.2]⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp

theorem fibre_card_eq_kernel {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (b : H) (hb : ∃ x, f x = b) :
    Nat.card {x // f x = b} = Nat.card {x // f x = 0} := by
  obtain ⟨x, rfl⟩ := hb
  exact Nat.card_congr (fibreEquivKernel f x)

theorem scalar_kernel_card_nat (N d : ℕ) [NeZero N] :
    Nat.card {x : ZMod N // (d : ZMod N) * x = 0} = Nat.gcd d N := by
  have h := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) d
  have he : {x : ZMod N // (d : ZMod N) * x = 0} ≃
      (nsmulAddMonoidHom (α := ZMod N) d).ker :=
    Equiv.subtypeEquivRight (fun x => by simp [nsmul_eq_mul])
  rw [Nat.card_congr he]
  simpa [Nat.card_eq_fintype_card, ZMod.card, Nat.gcd_comm] using h

theorem scalar_kernel_card (N : ℕ) [NeZero N] (d : ℤ) :
    Nat.card {x : ZMod N // (d : ZMod N) * x = 0} = Nat.gcd d.natAbs N := by
  have habs : (d.natAbs : ZMod N) = if 0 ≤ d then (d : ZMod N) else -(d : ZMod N) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    split_ifs with hd
    · rw [abs_of_nonneg hd]
    · rw [abs_of_neg (lt_of_not_ge hd), Int.cast_neg]
  have he : {x : ZMod N // (d : ZMod N) * x = 0} ≃
      {x : ZMod N // (d.natAbs : ZMod N) * x = 0} :=
    Equiv.subtypeEquivRight (fun x => by rw [habs]; split_ifs <;> simp)
  exact (Nat.card_congr he).trans (scalar_kernel_card_nat N d.natAbs)

theorem diagonal_kernel_card {I : Type*} [Fintype I] [DecidableEq I]
    (N : ℕ) [NeZero N] (d : I → ℤ) :
    Nat.card {x : I → ZMod N // (Matrix.diagonal (fun i => (d i : ZMod N))).mulVec x = 0} =
      ∏ i, Nat.gcd (d i).natAbs N := by
  classical
  let e : {x : I → ZMod N // (Matrix.diagonal (fun i => (d i : ZMod N))).mulVec x = 0} ≃
      (∀ i : I, {x : ZMod N // (d i : ZMod N) * x = 0}) :=
    (Equiv.subtypeEquivRight (fun x => by simp [funext_iff, Matrix.mulVec, dotProduct, Matrix.diagonal])).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => scalar_kernel_card N (d i))

/-- Multiplying a square matrix on either side by a unit preserves its kernel
cardinality over any finite commutative ring. -/
theorem kernel_card_units {I R : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] [Fintype R] (A U V : Matrix I I R) (hU : IsUnit U) (hV : IsUnit V) :
    Nat.card {x // (U * A * V).mulVec x = 0} = Nat.card {x // A.mulVec x = 0} := by
  let e : (I → R) ≃ (I → R) := Equiv.ofBijective V.mulVec
    ((Finite.injective_iff_bijective).mp (Matrix.mulVec_injective_of_isUnit hV))
  apply Nat.card_congr (Equiv.subtypeEquiv e _)
  intro x
  change (U * A * V).mulVec x = 0 ↔ A.mulVec (V.mulVec x) = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact ⟨fun h => Matrix.mulVec_injective_of_isUnit hU (h.trans (Matrix.mulVec_zero U).symm),
    fun h => by rw [h, Matrix.mulVec_zero]⟩

/-- Mathlib's module Smith normal form yields integral unimodular row and
column transformations for every nonsingular square integer matrix. -/
theorem integer_diagonalization {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) :
    ∃ (U V : Matrix I I ℤ) (d : I → ℤ),
      IsUnit U ∧ IsUnit V ∧ U * A * V = Matrix.diagonal d := by
  classical
  let b := Pi.basisFun ℤ I
  let f : (I → ℤ) →ₗ[ℤ] (I → ℤ) := Matrix.toLin' A
  have hdet : f.det ≠ 0 := by simpa only [f, LinearMap.det_toLin'] using hA
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  let e : (I → ℤ) ≃ₗ[ℤ] LinearMap.range f := LinearEquiv.ofInjective f hf
  have hr : Module.finrank ℤ (LinearMap.range f) = Module.finrank ℤ (I → ℤ) := e.symm.finrank_eq
  obtain ⟨bM, d, bN, hsnf⟩ := (LinearMap.range f).exists_smith_normal_form_of_rank_eq b hr
  let bD := bN.map e.symm
  let U := bM.toMatrix b
  let V := b.toMatrix bD
  have hU : IsUnit U := by
    letI := bM.invertibleToMatrix b
    exact isUnit_of_invertible _
  have hV : IsUnit V := by
    letI := b.invertibleToMatrix bD
    exact isUnit_of_invertible _
  refine ⟨U, V, d, hU, hV, ?_⟩
  have hAf : LinearMap.toMatrix b b f = A := by simp [b, f]
  rw [← hAf, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  rw [LinearMap.toMatrix_apply]
  have hfb : f (bD j) = d j • bM j := by
    change f (e.symm (bN j)) = _
    have he : f (e.symm (bN j)) = (bN j : I → ℤ) := congrArg Subtype.val (e.apply_symm_apply (bN j))
    exact he.trans (hsnf j)
  rw [hfb]
  rw [LinearEquiv.map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases h : i = j
  · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
  · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]

theorem gcd_two_pow_of_val_le (a m : ℕ) (ha : a ≠ 0) (hv : padicValNat 2 a ≤ m) :
    Nat.gcd a (2 ^ m) = 2 ^ padicValNat 2 a := by
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right a (2 ^ m))
  have hka : k ≤ padicValNat 2 a := (padicValNat_dvd_iff_le ha).mp
    (by simpa only [he] using Nat.gcd_dvd_left a (2 ^ m))
  have hvk : padicValNat 2 a ≤ k := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
    rw [← he]
    exact Nat.dvd_gcd pow_padicValNat_dvd (pow_dvd_pow 2 hv)
  simpa only [Nat.le_antisymm hka hvk] using he

theorem v2_prod {I : Type*} [DecidableEq I] (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    padicValNat 2 (∏ i ∈ s, a i) = ∑ i ∈ s, padicValNat 2 (a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, padicValNat.mul
      (ha i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => ha j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]

/-- The determinant valuation controls the exact kernel size. The hypothesis
`det ≠ 0` expresses finite valuation (Mathlib defines padicValNat 2 0 = 0).
This holds for every dimension, not just the combine matrices. -/
theorem matrix_kernel_card {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (m : ℕ) (hA : A.det ≠ 0)
    (hv : padicValNat 2 A.det.natAbs ≤ m) :
    Nat.card {x : I → ZMod (2 ^ m) // (A.map (Int.castRingHom (ZMod (2 ^ m)))).mulVec x = 0} =
      2 ^ padicValNat 2 A.det.natAbs := by
  classical
  obtain ⟨U, V, d, hU, hV, hD⟩ := integer_diagonalization A hA
  have hUdet : U.det.natAbs = 1 := Int.natAbs_of_isUnit (Matrix.isUnit_iff_isUnit_det U |>.mp hU)
  have hVdet : V.det.natAbs = 1 := Int.natAbs_of_isUnit (Matrix.isUnit_iff_isUnit_det V |>.mp hV)
  have hprod : ∏ i, (d i).natAbs = A.det.natAbs := by
    have hd := congrArg (fun M : Matrix I I ℤ => M.det.natAbs) hD
    simp only [Matrix.det_mul, Matrix.det_diagonal, Int.natAbs_mul, hUdet, hVdet,
      one_mul, mul_one] at hd
    exact (map_prod Int.natAbsHom d Finset.univ).symm.trans hd.symm
  have hdn : ∀ i, (d i).natAbs ≠ 0 := by
    have hp : ∏ i, (d i).natAbs ≠ 0 := by rw [hprod]; exact Int.natAbs_ne_zero.mpr hA
    exact fun i => Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  have hsum : ∑ i, padicValNat 2 (d i).natAbs = padicValNat 2 A.det.natAbs := by
    rw [← v2_prod Finset.univ (fun i => (d i).natAbs) (fun i _ => hdn i), hprod]
  have hdi : ∀ i, padicValNat 2 (d i).natAbs ≤ m := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans (hsum ▸ hv)
  let rho : Matrix I I ℤ →+* Matrix I I (ZMod (2 ^ m)) :=
    (Int.castRingHom (ZMod (2 ^ m))).mapMatrix
  have hdiag : rho (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ZMod (2 ^ m))) := by
    ext i j
    by_cases h : i = j <;> simp [rho, RingHom.mapMatrix, Matrix.diagonal, h]
  have hD' : rho U * rho A * rho V = Matrix.diagonal (fun i => (d i : ZMod (2 ^ m))) := by
    rw [← map_mul, ← map_mul, hD, hdiag]
  change Nat.card {x // (rho A).mulVec x = 0} = _
  rw [← kernel_card_units (rho A) (rho U) (rho V) (hU.map rho) (hV.map rho), hD',
    diagonal_kernel_card]
  simp_rw [gcd_two_pow_of_val_le _ m (hdn _) (hdi _)]
  rw [Finset.prod_pow_eq_pow_sum, hsum]

/-- Every nonempty fibre over 2^64 has exactly 2^τ elements for finite τ<64. -/
theorem matrix_fibre_card {r τ : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hA : A.det ≠ 0) (hτ : padicValNat 2 A.det.natAbs = τ) (h64 : τ < 64)
    (b : Fin r → ZMod (2 ^ 64))
    (hb : ∃ x, (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec x = b) :
    Nat.card {x // (A.map (Int.castRingHom (ZMod (2 ^ 64)))).mulVec x = b} = 2 ^ τ := by
  exact (fibre_card_eq_kernel
    (Matrix.mulVecLin (A.map (Int.castRingHom (ZMod (2 ^ 64))))).toAddMonoidHom b hb).trans
      ((matrix_kernel_card A 64 hA (by omega)).trans (congrArg (fun v => 2 ^ v) hτ))

theorem matrix_fibre_card_le {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (m : ℕ) (hA : A.det ≠ 0)
    (hv : padicValNat 2 A.det.natAbs ≤ m) (b : I → ZMod (2 ^ m)) :
    Nat.card {x // (A.map (Int.castRingHom (ZMod (2 ^ m)))).mulVec x = b} ≤
      2 ^ padicValNat 2 A.det.natAbs := by
  classical
  by_cases hb : ∃ x, (A.map (Int.castRingHom (ZMod (2 ^ m)))).mulVec x = b
  · exact ((fibre_card_eq_kernel
      (Matrix.mulVecLin (A.map (Int.castRingHom (ZMod (2 ^ m))))).toAddMonoidHom b hb).trans
        (matrix_kernel_card A m hA hv)).le
  · haveI : IsEmpty {x // (A.map (Int.castRingHom (ZMod (2 ^ m)))).mulVec x = b} :=
      ⟨fun x => hb ⟨x.1, x.2⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

end ProvenHashes.Halftime
