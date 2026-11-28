import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_29716.Irred
open Polynomial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
abbrev F := ZMod 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def f : F[X] := X^5 + X^2 + 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem degree_f : f.natDegree = 5 := by
  unfold f
  have h₂ : (X ^ 2 + 1 : F[X]).natDegree = 2 := by simp
  have h₅ : (X ^ 5 : F[X]).natDegree = 5 := by simp
  rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt (by rw [h₂, h₅]; decide), h₅]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem div_f : f ∣ (X ^ 32 - X : F[X]) := by
  refine ⟨X ^ 27 + X ^ 24 + X ^ 22 + X ^ 21 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 10 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X, ?_⟩
  have two : (2 : F[X]) = 0 := CharP.cast_eq_zero F[X] 2
  simp only [f]
  ring_nf
  simp [two, CharTwo.neg_eq]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem coprime_f : IsCoprime f (X ^ 2 - X : F[X]) := by
  refine ⟨1, X ^ 3 + X ^ 2 + X, ?_⟩
  have two : (2 : F[X]) = 0 := CharP.cast_eq_zero F[X] 2
  simp only [f]
  ring_nf
  simp [two, CharTwo.neg_eq]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem irreducible_f : Irreducible f := by
  rw [Polynomial.irreducible_iff_dvd_X_pow_card_pow_sub_X_and_isCoprime (by rw [degree_f]; decide)]
  rw [degree_f]
  norm_num only [Nat.card_zmod]
  refine ⟨div_f, ?_⟩
  intro m hm hne
  have hm5 : m ≤ 5 := Nat.le_of_dvd (by decide) hm
  interval_cases m <;> norm_num at *
  simpa using coprime_f

end PEqualNP.Outside.L_meta_29716.Irred




namespace PEqualNP.Outside.L_meta_29716.Root
open Polynomial

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
abbrev K := GaloisField 2 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def poly : K[X] := X ^ 5 + X ^ 2 + 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem divisor : poly ∣ (X ^ 32 - X : K[X]) := by
  refine ⟨X ^ 27 + X ^ 24 + X ^ 22 + X ^ 21 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 10 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X, ?_⟩
  have two : (2 : K[X]) = 0 := CharP.cast_eq_zero K[X] 2
  simp only [poly]
  ring_nf
  simp [two, CharTwo.neg_eq]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem hasRoot : ∃ a : K, a ^ 5 + a ^ 2 + 1 = 0 := by
  have hs : (X ^ 32 - X : K[X]).Splits := by
    have h := SplittingField.splits (X ^ 2 ^ 5 - X : (ZMod 2)[X])
    change ((X ^ 2 ^ 5 - X : (ZMod 2)[X]).map (algebraMap (ZMod 2) K)).Splits at h
    norm_num only at h ⊢
    simpa using h
  have hn : (X ^ 32 - X : K[X]) ≠ 0 := by
    exact X_pow_sub_X_ne_zero (by decide)
  have hp : poly.Splits := hs.of_dvd hn divisor
  have hd : poly.degree ≠ 0 := by
    have hn : poly.natDegree = 5 := by
      unfold poly
      have h₂ : (X ^ 2 + 1 : K[X]).natDegree = 2 := by simpa using (natDegree_X_pow_add_C (R := K) (n := 2) (r := 1))
      have h₅ : (X ^ 5 : K[X]).natDegree = 5 := by simp
      rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt (by rw [h₂, h₅]; decide), h₅]
    have hd : poly.degree = 5 := (degree_eq_iff_natDegree_eq_of_neZero).2 hn
    rw [hd]
    norm_num
  obtain ⟨a,ha⟩ := hp.exists_eval_eq_zero hd
  exact ⟨a, by simpa [poly] using ha⟩

end PEqualNP.Outside.L_meta_29716.Root

namespace PEqualNP.Outside.L_meta_29716.Basis
open Polynomial
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
abbrev F := ZMod 2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
abbrev K := GaloisField 2 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def alpha : K := Classical.choose PEqualNP.Outside.L_meta_29716.Root.hasRoot

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alphaRoot : alpha ^ 5 + alpha ^ 2 + 1 = 0 :=
  Classical.choose_spec PEqualNP.Outside.L_meta_29716.Root.hasRoot

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem f_monic : PEqualNP.Outside.L_meta_29716.Irred.f.Monic := by
  unfold PEqualNP.Outside.L_meta_29716.Irred.f
  rw [add_assoc]
  apply monic_X_pow_add
  calc
    (X ^ 2 + 1 : F[X]).degree ≤ ((X ^ 2 + 1 : F[X]).natDegree : WithBot ℕ) := degree_le_natDegree
    _ < 5 := by simp; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_minpoly : minpoly F alpha = PEqualNP.Outside.L_meta_29716.Irred.f := by
  symm
  apply minpoly.eq_of_irreducible_of_monic PEqualNP.Outside.L_meta_29716.Irred.irreducible_f _ f_monic
  simpa [PEqualNP.Outside.L_meta_29716.Irred.f] using alphaRoot

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alphaIntegral : IsIntegral F alpha := Algebra.IsIntegral.isIntegral alpha

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_adjoin_top : IntermediateField.adjoin F {alpha} = ⊤ := by
  apply IntermediateField.finrank_eq_one_iff_eq_top.mp
  have ha : Module.finrank F (IntermediateField.adjoin F {alpha}) = 5 := by
    rw [IntermediateField.adjoin.finrank alphaIntegral, alpha_minpoly, PEqualNP.Outside.L_meta_29716.Irred.degree_f]
  have hk : Module.finrank F K = 5 := GaloisField.finrank 2 (by decide)
  have h := Module.finrank_mul_finrank F (IntermediateField.adjoin F {alpha}) K
  rw [ha,hk] at h
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def pb : PowerBasis F K := PowerBasis.ofAdjoinSimpleEqTop alphaIntegral alpha_adjoin_top

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem pb_dim : pb.dim = 5 := by
  rw [pb, PowerBasis.ofAdjoinSimpleEqTop_dim, alpha_minpoly, PEqualNP.Outside.L_meta_29716.Irred.degree_f]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def basis : Module.Basis (Fin 5) F K := pb.basis.reindex (finCongr pb_dim)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem basis_pow (i : Fin 5) : basis i = alpha ^ i.val := by
  simp only [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, pb, PowerBasis.ofAdjoinSimpleEqTop_gen]
  congr 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def bit : K →ₗ[F] F := basis.coord 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem bit_nonzero : bit ≠ 0 := by
  intro h
  have e := DFunLike.congr_fun h (basis 0)
  simp [bit, Module.Basis.coord_apply] at e

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_five : alpha ^ 5 = alpha ^ 2 + 1 := by
  have h : alpha ^ 5 + alpha ^ 2 = 1 := by
    have h := add_eq_zero_iff_eq_neg.mp alphaRoot
    simpa only [CharTwo.neg_eq] using h
  calc
    alpha ^ 5 = (alpha ^ 5 + alpha ^ 2) + alpha ^ 2 := by simp [CharTwo.add_self_eq_zero, add_assoc]
    _ = alpha ^ 2 + 1 := by rw [h, add_comm]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_recurrence (n : ℕ) : alpha ^ (n+5) = alpha ^ (n+2) + alpha ^ n := by
  calc
    alpha ^ (n+5) = alpha ^ n * alpha ^ 5 := by rw [pow_add]
    _ = alpha ^ n * (alpha ^ 2 + 1) := by rw [alpha_five]
    _ = alpha ^ (n+2) + alpha ^ n := by rw [pow_add]; ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_0 : alpha ^ 0 = 1 := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_1 : alpha ^ 1 = alpha := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_2 : alpha ^ 2 = alpha ^ 2 := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_3 : alpha ^ 3 = alpha ^ 3 := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_4 : alpha ^ 4 = alpha ^ 4 := by simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_5 : alpha ^ 5 = 1 + alpha ^ 2 := by
  have h := alpha_recurrence 0
  norm_num only at h
  rw [h]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_6 : alpha ^ 6 = alpha + alpha ^ 3 := by
  have h := alpha_recurrence 1
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_7 : alpha ^ 7 = alpha ^ 2 + alpha ^ 4 := by
  have h := alpha_recurrence 2
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5, alpha_pow_6]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_8 : alpha ^ 8 = 1 + alpha ^ 2 + alpha ^ 3 := by
  have h := alpha_recurrence 3
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5, alpha_pow_6, alpha_pow_7]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_9 : alpha ^ 9 = alpha + alpha ^ 3 + alpha ^ 4 := by
  have h := alpha_recurrence 4
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5, alpha_pow_6, alpha_pow_7, alpha_pow_8]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_10 : alpha ^ 10 = 1 + alpha ^ 4 := by
  have h := alpha_recurrence 5
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5, alpha_pow_6, alpha_pow_7, alpha_pow_8, alpha_pow_9]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_11 : alpha ^ 11 = 1 + alpha + alpha ^ 2 := by
  have h := alpha_recurrence 6
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5, alpha_pow_6, alpha_pow_7, alpha_pow_8, alpha_pow_9, alpha_pow_10]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem alpha_pow_12 : alpha ^ 12 = alpha + alpha ^ 2 + alpha ^ 3 := by
  have h := alpha_recurrence 7
  norm_num only at h
  rw [h]
  try simp only [alpha_pow_5, alpha_pow_6, alpha_pow_7, alpha_pow_8, alpha_pow_9, alpha_pow_10, alpha_pow_11]
  all_goals ring_nf
  all_goals simp [CharTwo.add_self_eq_zero, CharTwo.neg_eq, CharP.cast_eq_zero K 2]
  all_goals exact Or.inr (CharP.cast_eq_zero K 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem bit_basis (i : Fin 5) : bit (alpha ^ i.val) = if i = 0 then 1 else 0 := by
  rw [← basis_pow i]
  by_cases hi : i = 0 <;> simp [bit, Module.Basis.coord_apply, Finsupp.single_apply, hi]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem bit_powers (n : Fin 13) :
    bit (alpha ^ n.val) = if ([1, 2, 4, 8, 16, 5, 10, 20, 13, 26, 17, 7, 14] : List ℕ).getD n.val 0 % 2 = 1 then 1 else 0 := by
  have h0 := bit_basis (0 : Fin 5)
  have h1 := bit_basis (1 : Fin 5)
  have h2 := bit_basis (2 : Fin 5)
  have h3 := bit_basis (3 : Fin 5)
  have h4 := bit_basis (4 : Fin 5)
  norm_num at h0 h1 h2 h3 h4
  fin_cases n <;> norm_num only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceMod, ↓reduceIte]
  all_goals simp only [alpha_pow_5, alpha_pow_6, alpha_pow_7, alpha_pow_8, alpha_pow_9, alpha_pow_10, alpha_pow_11, alpha_pow_12]
  all_goals simp only [map_add, pow_one, pow_zero, h0, h1, h2, h3, h4]
  all_goals norm_num

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def bits (n : Fin 32) (i : Fin 5) : F := if n.val.testBit i.val then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 15000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem bits_surjective : ∀ f : Fin 5 → F, ∃ n : Fin 32, bits n = f := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def element (n : Fin 32) : K :=
  ∑ i : Fin 5, bits n i • (alpha ^ i.val)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem element_surjective : ∀ z : K, ∃ n : Fin 32, element n = z := by
  intro z
  obtain ⟨n, hn⟩ := bits_surjective (fun i => basis.repr z i)
  refine ⟨n, ?_⟩
  unfold element
  rw [hn]
  simpa only [basis_pow] using basis.sum_repr z

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem element_zero : element ⟨0, by decide⟩ = 0 := by
  simp [element, bits]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem nonzero_rep (z : K) (hz : z ≠ 0) :
    ∃ n : Fin 32, n.val ≠ 0 ∧ element n = z := by
  obtain ⟨n, hn⟩ := element_surjective z
  refine ⟨n, ?_, hn⟩
  intro h
  have hn0 : n = 0 := Fin.ext h
  subst n
  apply hz
  rw [← hn]
  exact element_zero


set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def gfMul (a b : Nat) : Nat := Id.run do
  let mut x := a
  let mut y := b
  let mut out := 0
  for _ in [0:5] do
    if y % 2 = 1 then out := Nat.xor out x
    x := Nat.xor (x <<< 1) (if x.testBit 4 then 37 else 0)
    y := y >>> 1
  return out

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def lowBit (n : Fin 13) : F :=
  if ([1, 2, 4, 8, 16, 5, 10, 20, 13, 26, 17, 7, 14] : List ℕ).getD n.val 0 % 2 = 1 then 1 else 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem bit_product_basis (r i j : Fin 5) :
    bit ((alpha ^ r.val) * (alpha ^ i.val) * (alpha ^ j.val)) =
      lowBit ⟨r.val+i.val+j.val, by omega⟩ := by
  have h := bit_powers ⟨r.val+i.val+j.val, by omega⟩
  simpa only [lowBit, pow_add] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem field_linear (n : Fin 32) (i j : Fin 5) :
    bit (element n * alpha ^ i.val * alpha ^ j.val) =
      ∑ r : Fin 5, bits n r * lowBit ⟨r.val+i.val+j.val, by omega⟩ := by
  simp only [element, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    smul_eq_mul, bit_product_basis]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem numeric_table : ∀ n : Fin 32, ∀ i j : Fin 5,
    (∑ r : Fin 5, bits n r * lowBit ⟨r.val+i.val+j.val, by omega⟩) =
      if (gfMul (gfMul n.val (2^i.val)) (2^j.val)).testBit 0 then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem compact_table (n : Fin 32) (i j : Fin 5) :
  bit (element n * alpha ^ i.val * alpha ^ j.val) =
    if (gfMul (gfMul n.val (2^i.val)) (2^j.val)).testBit 0 then 1 else 0 := by
  rw [field_linear]
  exact numeric_table n i j

end PEqualNP.Outside.L_meta_29716.Basis


namespace PEqualNP.Outside.L_meta_29716.Cert

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def gfMul (a b : Nat) : Nat := Id.run do
  let mut x := a
  let mut y := b
  let mut out := 0
  for _ in [0:5] do
    if y % 2 = 1 then out := Nat.xor out x
    x := Nat.xor (x <<< 1) (if x.testBit 4 then 37 else 0)
    y := y >>> 1
  return out

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def realPrep : List Gate := [⟨.or, []⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 7]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 3]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 4]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 7]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 9]⟩, ⟨.not, [27]⟩, ⟨.mod 2, [28, 10]⟩, ⟨.not, [29]⟩, ⟨.mod 2, [30, 11]⟩, ⟨.not, [31]⟩, ⟨.and, [18, 32]⟩, ⟨.mod 2, [33, 16]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [3, 5]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 8]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [40]⟩, ⟨.mod 2, [41, 7]⟩, ⟨.not, [42]⟩, ⟨.mod 2, [43, 10]⟩, ⟨.not, [44]⟩, ⟨.mod 2, [45, 11]⟩, ⟨.not, [46]⟩, ⟨.and, [39, 47]⟩, ⟨.mod 2, [48, 3]⟩, ⟨.not, [49]⟩]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c1 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 11]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 5]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 7]⟩, ⟨.not, [25]⟩, ⟨.and, [20, 26]⟩, ⟨.mod 2, [3, 5]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [27, 29]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [4, 10]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 11]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [5, 9]⟩, ⟨.not, [36]⟩, ⟨.and, [35, 37]⟩, ⟨.mod 2, [38, 12]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [31, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c2 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 3]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 11]⟩, ⟨.not, [25]⟩, ⟨.and, [18, 26]⟩, ⟨.mod 2, [27, 2]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [1, 10]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 11]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [22, 5]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 9]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 11]⟩, ⟨.not, [38]⟩, ⟨.and, [33, 39]⟩, ⟨.mod 2, [1, 11]⟩, ⟨.not, [41]⟩, ⟨.mod 2, [40, 42]⟩, ⟨.not, [43]⟩, ⟨.mod 2, [29, 44]⟩, ⟨.not, [45]⟩], 46)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c3 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 5]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 8]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 11]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [14, 3]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 5]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 7]⟩, ⟨.not, [27]⟩, ⟨.and, [22, 28]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [29, 31]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [1, 4]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 10]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [31, 9]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [39, 11]⟩, ⟨.not, [40]⟩, ⟨.and, [37, 41]⟩, ⟨.mod 2, [42, 1]⟩, ⟨.not, [43]⟩, ⟨.mod 2, [33, 44]⟩, ⟨.not, [45]⟩], 46)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c4 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [3, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 7]⟩, ⟨.not, [19]⟩, ⟨.and, [18, 20]⟩, ⟨.mod 2, [21, 12]⟩, ⟨.not, [22]⟩, ⟨.mod 2, [2, 5]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [25, 10]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 4]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 5]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 9]⟩, ⟨.not, [34]⟩, ⟨.and, [27, 35]⟩, ⟨.mod 2, [36, 5]⟩, ⟨.not, [37]⟩, ⟨.mod 2, [23, 38]⟩, ⟨.not, [39]⟩], 40)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c5 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 5]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 11]⟩, ⟨.not, [23]⟩, ⟨.and, [16, 24]⟩, ⟨.mod 2, [25, 14]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [14, 3]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 4]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 5]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 10]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [4, 9]⟩, ⟨.not, [36]⟩, ⟨.and, [35, 37]⟩, ⟨.mod 2, [38, 4]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [27, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c6 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [3, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 11]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 11]⟩, ⟨.not, [23]⟩, ⟨.and, [18, 24]⟩, ⟨.mod 2, [4, 11]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [25, 27]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 5]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 10]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 11]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [39, 3]⟩, ⟨.not, [40]⟩, ⟨.mod 2, [41, 4]⟩, ⟨.not, [42]⟩, ⟨.mod 2, [43, 9]⟩, ⟨.not, [44]⟩, ⟨.and, [37, 45]⟩, ⟨.mod 2, [46, 31]⟩, ⟨.not, [47]⟩, ⟨.mod 2, [29, 48]⟩, ⟨.not, [49]⟩], 50)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c7 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 9]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 5]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 8]⟩, ⟨.not, [25]⟩, ⟨.and, [18, 26]⟩, ⟨.mod 2, [27, 16]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 5]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 11]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [31, 10]⟩, ⟨.not, [36]⟩, ⟨.and, [35, 37]⟩, ⟨.mod 2, [38, 31]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [29, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c8 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 10]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 11]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 4]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 5]⟩, ⟨.not, [27]⟩, ⟨.mod 2, [28, 7]⟩, ⟨.not, [29]⟩, ⟨.mod 2, [30, 11]⟩, ⟨.not, [31]⟩, ⟨.and, [22, 32]⟩, ⟨.mod 2, [3, 4]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 11]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [33, 37]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [9, 10]⟩, ⟨.not, [40]⟩, ⟨.mod 2, [41, 11]⟩, ⟨.not, [42]⟩, ⟨.and, [35, 43]⟩, ⟨.mod 2, [44, 12]⟩, ⟨.not, [45]⟩, ⟨.mod 2, [39, 46]⟩, ⟨.not, [47]⟩], 48)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c9 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 3]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 4]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 8]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 11]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 4]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 7]⟩, ⟨.not, [27]⟩, ⟨.and, [22, 28]⟩, ⟨.mod 2, [29, 26]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [3, 10]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [24, 5]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 9]⟩, ⟨.not, [36]⟩, ⟨.and, [33, 37]⟩, ⟨.mod 2, [38, 3]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [31, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c10 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 5]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 8]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 10]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 5]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 7]⟩, ⟨.not, [27]⟩, ⟨.mod 2, [28, 10]⟩, ⟨.not, [29]⟩, ⟨.mod 2, [30, 11]⟩, ⟨.not, [31]⟩, ⟨.and, [22, 32]⟩, ⟨.mod 2, [3, 5]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 10]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [33, 37]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [9, 10]⟩, ⟨.not, [40]⟩, ⟨.mod 2, [41, 11]⟩, ⟨.not, [42]⟩, ⟨.and, [4, 43]⟩, ⟨.mod 2, [44, 12]⟩, ⟨.not, [45]⟩, ⟨.mod 2, [39, 46]⟩, ⟨.not, [47]⟩], 48)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c11 : Nat × List Gate × Nat := (3, [⟨.or, []⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 11]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [14, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [20, 22]⟩, ⟨.mod 2, [23, 14]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [10, 11]⟩, ⟨.not, [28]⟩, ⟨.and, [27, 29]⟩, ⟨.mod 2, [30, 12]⟩, ⟨.not, [31]⟩, ⟨.mod 2, [25, 32]⟩, ⟨.not, [33]⟩], 34)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c12 : Nat × List Gate × Nat := (3, [⟨.or, []⟩, ⟨.mod 2, [2, 5]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 11]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 3]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 4]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 5]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 7]⟩, ⟨.not, [27]⟩, ⟨.mod 2, [28, 10]⟩, ⟨.not, [29]⟩, ⟨.and, [18, 30]⟩, ⟨.mod 2, [31, 14]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 4]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 5]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [9, 10]⟩, ⟨.not, [40]⟩, ⟨.and, [39, 41]⟩, ⟨.mod 2, [42, 12]⟩, ⟨.not, [43]⟩, ⟨.mod 2, [33, 44]⟩, ⟨.not, [45]⟩], 46)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c13 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [1, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 9]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 5]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.and, [18, 24]⟩, ⟨.mod 2, [1, 5]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [25, 27]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 4]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 11]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [4, 10]⟩, ⟨.not, [36]⟩, ⟨.and, [35, 37]⟩, ⟨.mod 2, [38, 4]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [29, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c14 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [4, 8]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [4, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 7]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 11]⟩, ⟨.not, [19]⟩, ⟨.and, [14, 20]⟩, ⟨.mod 2, [21, 4]⟩, ⟨.not, [22]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [25, 3]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [27, 4]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 5]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 10]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 11]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [25, 4]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 5]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [39, 9]⟩, ⟨.not, [40]⟩, ⟨.and, [35, 41]⟩, ⟨.mod 2, [42, 39]⟩, ⟨.not, [43]⟩, ⟨.mod 2, [23, 44]⟩, ⟨.not, [45]⟩], 46)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c15 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [1, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 10]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 11]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [4, 7]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 11]⟩, ⟨.not, [23]⟩, ⟨.and, [20, 24]⟩, ⟨.mod 2, [4, 11]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [25, 27]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 3]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 5]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [9, 10]⟩, ⟨.not, [36]⟩, ⟨.and, [35, 37]⟩, ⟨.mod 2, [38, 12]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [29, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c16 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [4, 5]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 11]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [18, 22]⟩, ⟨.mod 2, [23, 12]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [1, 5]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [27, 10]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 11]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 3]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 4]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 5]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [39, 9]⟩, ⟨.not, [40]⟩, ⟨.mod 2, [41, 11]⟩, ⟨.not, [42]⟩, ⟨.and, [31, 43]⟩, ⟨.mod 2, [27, 11]⟩, ⟨.not, [45]⟩, ⟨.mod 2, [44, 46]⟩, ⟨.not, [47]⟩, ⟨.mod 2, [25, 48]⟩, ⟨.not, [49]⟩], 50)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c17 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 5]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 9]⟩, ⟨.not, [25]⟩, ⟨.and, [18, 26]⟩, ⟨.mod 2, [27, 5]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 4]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 5]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 11]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [39, 5]⟩, ⟨.not, [40]⟩, ⟨.mod 2, [41, 10]⟩, ⟨.not, [42]⟩, ⟨.and, [37, 43]⟩, ⟨.mod 2, [44, 41]⟩, ⟨.not, [45]⟩, ⟨.mod 2, [29, 46]⟩, ⟨.not, [47]⟩], 48)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c18 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 3]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.and, [18, 24]⟩, ⟨.mod 2, [25, 14]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [5, 10]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [3, 4]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 5]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 9]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 11]⟩, ⟨.not, [36]⟩, ⟨.and, [29, 37]⟩, ⟨.mod 2, [38, 5]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [27, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c19 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 3]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 5]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 9]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 10]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [4, 5]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 7]⟩, ⟨.not, [25]⟩, ⟨.mod 2, [26, 8]⟩, ⟨.not, [27]⟩, ⟨.and, [22, 28]⟩, ⟨.mod 2, [29, 5]⟩, ⟨.not, [30]⟩, ⟨.and, [2, 11]⟩, ⟨.mod 2, [32, 12]⟩, ⟨.not, [33]⟩, ⟨.mod 2, [31, 34]⟩, ⟨.not, [35]⟩], 36)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c20 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 11]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 4]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 7]⟩, ⟨.not, [25]⟩, ⟨.and, [20, 26]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [27, 29]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [14, 10]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [22, 3]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 9]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 11]⟩, ⟨.not, [38]⟩, ⟨.and, [33, 39]⟩, ⟨.mod 2, [40, 14]⟩, ⟨.not, [41]⟩, ⟨.mod 2, [31, 42]⟩, ⟨.not, [43]⟩], 44)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c21 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 5]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 10]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 5]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [18, 22]⟩, ⟨.mod 2, [23, 5]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [27, 4]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 11]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 4]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 9]⟩, ⟨.not, [36]⟩, ⟨.and, [31, 37]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [38, 40]⟩, ⟨.not, [41]⟩, ⟨.mod 2, [25, 42]⟩, ⟨.not, [43]⟩], 44)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c22 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 9]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 3]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 8]⟩, ⟨.not, [21]⟩, ⟨.and, [16, 22]⟩, ⟨.mod 2, [23, 2]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [3, 11]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 5]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 10]⟩, ⟨.not, [32]⟩, ⟨.and, [27, 33]⟩, ⟨.mod 2, [34, 3]⟩, ⟨.not, [35]⟩, ⟨.mod 2, [25, 36]⟩, ⟨.not, [37]⟩], 38)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c23 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 8]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 5]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 7]⟩, ⟨.not, [19]⟩, ⟨.and, [14, 20]⟩, ⟨.mod 2, [21, 12]⟩, ⟨.not, [22]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [25, 3]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [27, 4]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 11]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [27, 9]⟩, ⟨.not, [32]⟩, ⟨.and, [31, 33]⟩, ⟨.mod 2, [34, 27]⟩, ⟨.not, [35]⟩, ⟨.mod 2, [23, 36]⟩, ⟨.not, [37]⟩], 38)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c24 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [2, 8]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 9]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 4]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 5]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.and, [16, 24]⟩, ⟨.mod 2, [25, 12]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 5]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 11]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 10]⟩, ⟨.not, [36]⟩, ⟨.and, [33, 37]⟩, ⟨.mod 2, [38, 2]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [27, 40]⟩, ⟨.not, [41]⟩], 42)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c25 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 5]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 8]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [3, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [20, 22]⟩, ⟨.mod 2, [23, 3]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [5, 10]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 3]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [31, 4]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 9]⟩, ⟨.not, [34]⟩, ⟨.and, [27, 35]⟩, ⟨.mod 2, [36, 12]⟩, ⟨.not, [37]⟩, ⟨.mod 2, [25, 38]⟩, ⟨.not, [39]⟩], 40)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c26 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [3, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 9]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [18, 22]⟩, ⟨.mod 2, [23, 14]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [1, 4]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [27, 5]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 11]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [1, 2]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 4]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 5]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 10]⟩, ⟨.not, [38]⟩, ⟨.and, [31, 39]⟩, ⟨.mod 2, [40, 29]⟩, ⟨.not, [41]⟩, ⟨.mod 2, [25, 42]⟩, ⟨.not, [43]⟩], 44)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c27 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 4]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [3, 4]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [18, 22]⟩, ⟨.mod 2, [23, 20]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [3, 5]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [27, 10]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 11]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [16, 5]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [33, 9]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 11]⟩, ⟨.not, [36]⟩, ⟨.and, [31, 37]⟩, ⟨.mod 2, [27, 11]⟩, ⟨.not, [39]⟩, ⟨.mod 2, [38, 40]⟩, ⟨.not, [41]⟩, ⟨.mod 2, [25, 42]⟩, ⟨.not, [43]⟩], 44)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c28 : Nat × List Gate × Nat := (3, [⟨.or, []⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 9]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 8]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 10]⟩, ⟨.not, [23]⟩, ⟨.and, [18, 24]⟩, ⟨.mod 2, [25, 2]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [2, 5]⟩, ⟨.not, [28]⟩, ⟨.and, [29, 11]⟩, ⟨.mod 2, [30, 12]⟩, ⟨.not, [31]⟩, ⟨.mod 2, [27, 32]⟩, ⟨.not, [33]⟩], 34)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c29 : Nat × List Gate × Nat := (1, [⟨.or, []⟩, ⟨.mod 2, [1, 3]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 9]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [2, 7]⟩, ⟨.not, [19]⟩, ⟨.and, [18, 20]⟩, ⟨.mod 2, [21, 12]⟩, ⟨.not, [22]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [25, 11]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [3, 5]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 10]⟩, ⟨.not, [30]⟩, ⟨.and, [27, 31]⟩, ⟨.mod 2, [32, 3]⟩, ⟨.not, [33]⟩, ⟨.mod 2, [23, 34]⟩, ⟨.not, [35]⟩], 36)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c30 : Nat × List Gate × Nat := (2, [⟨.or, []⟩, ⟨.mod 2, [2, 4]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 5]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [16, 8]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 9]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [1, 5]⟩, ⟨.not, [21]⟩, ⟨.mod 2, [22, 7]⟩, ⟨.not, [23]⟩, ⟨.mod 2, [24, 9]⟩, ⟨.not, [25]⟩, ⟨.and, [20, 26]⟩, ⟨.mod 2, [5, 9]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [27, 29]⟩, ⟨.not, [30]⟩, ⟨.mod 2, [1, 11]⟩, ⟨.not, [32]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [34]⟩, ⟨.mod 2, [35, 4]⟩, ⟨.not, [36]⟩, ⟨.mod 2, [37, 5]⟩, ⟨.not, [38]⟩, ⟨.mod 2, [39, 10]⟩, ⟨.not, [40]⟩, ⟨.and, [33, 41]⟩, ⟨.mod 2, [42, 12]⟩, ⟨.not, [43]⟩, ⟨.mod 2, [31, 44]⟩, ⟨.not, [45]⟩], 46)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def c31 : Nat × List Gate × Nat := (3, [⟨.or, []⟩, ⟨.mod 2, [1, 5]⟩, ⟨.not, [13]⟩, ⟨.mod 2, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.mod 2, [2, 3]⟩, ⟨.not, [17]⟩, ⟨.mod 2, [18, 4]⟩, ⟨.not, [19]⟩, ⟨.mod 2, [20, 7]⟩, ⟨.not, [21]⟩, ⟨.and, [16, 22]⟩, ⟨.mod 2, [23, 12]⟩, ⟨.not, [24]⟩, ⟨.mod 2, [18, 11]⟩, ⟨.not, [26]⟩, ⟨.mod 2, [1, 4]⟩, ⟨.not, [28]⟩, ⟨.mod 2, [29, 9]⟩, ⟨.not, [30]⟩, ⟨.and, [27, 31]⟩, ⟨.mod 2, [32, 12]⟩, ⟨.not, [33]⟩, ⟨.mod 2, [25, 34]⟩, ⟨.not, [35]⟩], 36)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def selected (z : Nat) : Nat × List Gate × Nat :=
  if z = 1 then c1 else if z = 2 then c2 else if z = 3 then c3 else if z = 4 then c4 else if z = 5 then c5 else if z = 6 then c6 else if z = 7 then c7 else if z = 8 then c8 else if z = 9 then c9 else if z = 10 then c10 else if z = 11 then c11 else if z = 12 then c12 else if z = 13 then c13 else if z = 14 then c14 else if z = 15 then c15 else if z = 16 then c16 else if z = 17 then c17 else if z = 18 then c18 else if z = 19 then c19 else if z = 20 then c20 else if z = 21 then c21 else if z = 22 then c22 else if z = 23 then c23 else if z = 24 then c24 else if z = 25 then c25 else if z = 26 then c26 else if z = 27 then c27 else if z = 28 then c28 else if z = 29 then c29 else if z = 30 then c30 else if z = 31 then c31 else (0, [], 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def numericTarget (z : Nat) (u v : Fin 6) : Bool :=
  if u.val = 0 ∨ v.val = 0 then false else (gfMul (gfMul z (2^(u.val-1))) (2^(v.val-1))).testBit 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def oneEach (u v : Fin 6) : List Bool :=
  List.ofFn (fun i : Fin 6 => decide (i = u)) ++ List.ofFn (fun i : Fin 6 => decide (i = v))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def prepValue (tap : Nat) (u v : Fin 6) : Bool := Circuit.eval ⟨realPrep, tap⟩ (oneEach u v)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def residualGoal (z : Nat) (u v : Fin 6) : Bool :=
  let m := (selected z).1
  xor (numericTarget z u v) (xor (m.testBit 0 && prepValue 35 u v) (m.testBit 1 && prepValue 50 u v))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def realCorrect (z : Nat) (u v : Fin 6) : Bool :=
  let c := selected z
  decide (Circuit.eval ⟨c.2.1, c.2.2⟩ (oneEach u v) = residualGoal z u v)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_1 : ∀ u v : Fin 6, realCorrect 1 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_2 : ∀ u v : Fin 6, realCorrect 2 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_3 : ∀ u v : Fin 6, realCorrect 3 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_4 : ∀ u v : Fin 6, realCorrect 4 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_5 : ∀ u v : Fin 6, realCorrect 5 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_6 : ∀ u v : Fin 6, realCorrect 6 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_7 : ∀ u v : Fin 6, realCorrect 7 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_8 : ∀ u v : Fin 6, realCorrect 8 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_9 : ∀ u v : Fin 6, realCorrect 9 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_10 : ∀ u v : Fin 6, realCorrect 10 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_11 : ∀ u v : Fin 6, realCorrect 11 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_12 : ∀ u v : Fin 6, realCorrect 12 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_13 : ∀ u v : Fin 6, realCorrect 13 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_14 : ∀ u v : Fin 6, realCorrect 14 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_15 : ∀ u v : Fin 6, realCorrect 15 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_16 : ∀ u v : Fin 6, realCorrect 16 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_17 : ∀ u v : Fin 6, realCorrect 17 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_18 : ∀ u v : Fin 6, realCorrect 18 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_19 : ∀ u v : Fin 6, realCorrect 19 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_20 : ∀ u v : Fin 6, realCorrect 20 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_21 : ∀ u v : Fin 6, realCorrect 21 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_22 : ∀ u v : Fin 6, realCorrect 22 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_23 : ∀ u v : Fin 6, realCorrect 23 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_24 : ∀ u v : Fin 6, realCorrect 24 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_25 : ∀ u v : Fin 6, realCorrect 25 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_26 : ∀ u v : Fin 6, realCorrect 26 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_27 : ∀ u v : Fin 6, realCorrect 27 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_28 : ∀ u v : Fin 6, realCorrect 28 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_29 : ∀ u v : Fin 6, realCorrect 29 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_30 : ∀ u v : Fin 6, realCorrect 30 u v = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_correct_31 : ∀ u v : Fin 6, realCorrect 31 u v = true := by decide +kernel

open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def depths (C : Circuit) : List Nat :=
  C.gates.foldl (fun ds g => ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]) (List.replicate 12 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def validGate (g : Gate) : Bool := decide (g.inputs.length ≤ 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def legalCheck (gs : List Gate) (tap : Nat) : Prop :=
  let C : Circuit := ⟨gs, tap⟩
  ReadsBack 12 C ∧ gs.all validGate = true ∧ gs.countP nonlinear ≤ 2 ∧ (depths C).getD tap 0 ≤ 1

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
instance (gs : List Gate) (tap : Nat) : Decidable (legalCheck gs tap) := by
  unfold legalCheck
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem prep_legal_1 : legalCheck realPrep 35 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem prep_legal_2 : legalCheck realPrep 50 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_1 : legalCheck (c1).2.1 (c1).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_2 : legalCheck (c2).2.1 (c2).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_3 : legalCheck (c3).2.1 (c3).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_4 : legalCheck (c4).2.1 (c4).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_5 : legalCheck (c5).2.1 (c5).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_6 : legalCheck (c6).2.1 (c6).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_7 : legalCheck (c7).2.1 (c7).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_8 : legalCheck (c8).2.1 (c8).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_9 : legalCheck (c9).2.1 (c9).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_10 : legalCheck (c10).2.1 (c10).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_11 : legalCheck (c11).2.1 (c11).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_12 : legalCheck (c12).2.1 (c12).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_13 : legalCheck (c13).2.1 (c13).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_14 : legalCheck (c14).2.1 (c14).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_15 : legalCheck (c15).2.1 (c15).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_16 : legalCheck (c16).2.1 (c16).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_17 : legalCheck (c17).2.1 (c17).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_18 : legalCheck (c18).2.1 (c18).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_19 : legalCheck (c19).2.1 (c19).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_20 : legalCheck (c20).2.1 (c20).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_21 : legalCheck (c21).2.1 (c21).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_22 : legalCheck (c22).2.1 (c22).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_23 : legalCheck (c23).2.1 (c23).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_24 : legalCheck (c24).2.1 (c24).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_25 : legalCheck (c25).2.1 (c25).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_26 : legalCheck (c26).2.1 (c26).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_27 : legalCheck (c27).2.1 (c27).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_28 : legalCheck (c28).2.1 (c28).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_29 : legalCheck (c29).2.1 (c29).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_30 : legalCheck (c30).2.1 (c30).2.2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_legal_31 : legalCheck (c31).2.1 (c31).2.2 := by decide +kernel



end PEqualNP.Outside.L_meta_29716.Cert

namespace PEqualNP.Outside.L_meta_29716.Cert

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem real_all (n : Fin 32) (hn : n.val ≠ 0) (u v : Fin 6) :
    realCorrect n.val u v = true := by
  fin_cases n
  · contradiction
  · exact real_correct_1 u v
  · exact real_correct_2 u v
  · exact real_correct_3 u v
  · exact real_correct_4 u v
  · exact real_correct_5 u v
  · exact real_correct_6 u v
  · exact real_correct_7 u v
  · exact real_correct_8 u v
  · exact real_correct_9 u v
  · exact real_correct_10 u v
  · exact real_correct_11 u v
  · exact real_correct_12 u v
  · exact real_correct_13 u v
  · exact real_correct_14 u v
  · exact real_correct_15 u v
  · exact real_correct_16 u v
  · exact real_correct_17 u v
  · exact real_correct_18 u v
  · exact real_correct_19 u v
  · exact real_correct_20 u v
  · exact real_correct_21 u v
  · exact real_correct_22 u v
  · exact real_correct_23 u v
  · exact real_correct_24 u v
  · exact real_correct_25 u v
  · exact real_correct_26 u v
  · exact real_correct_27 u v
  · exact real_correct_28 u v
  · exact real_correct_29 u v
  · exact real_correct_30 u v
  · exact real_correct_31 u v

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem legal_all (n : Fin 32) (hn : n.val ≠ 0) :
    legalCheck (selected n.val).2.1 (selected n.val).2.2 := by
  fin_cases n
  · contradiction
  · exact real_legal_1
  · exact real_legal_2
  · exact real_legal_3
  · exact real_legal_4
  · exact real_legal_5
  · exact real_legal_6
  · exact real_legal_7
  · exact real_legal_8
  · exact real_legal_9
  · exact real_legal_10
  · exact real_legal_11
  · exact real_legal_12
  · exact real_legal_13
  · exact real_legal_14
  · exact real_legal_15
  · exact real_legal_16
  · exact real_legal_17
  · exact real_legal_18
  · exact real_legal_19
  · exact real_legal_20
  · exact real_legal_21
  · exact real_legal_22
  · exact real_legal_23
  · exact real_legal_24
  · exact real_legal_25
  · exact real_legal_26
  · exact real_legal_27
  · exact real_legal_28
  · exact real_legal_29
  · exact real_legal_30
  · exact real_legal_31

end PEqualNP.Outside.L_meta_29716.Cert

namespace PEqualNP.Outside.L_meta_29716.Bridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_29716.Cert PEqualNP.Outside.L_meta_29716.Basis

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
noncomputable def point : Fin 6 → K := Fin.cases 0 basis

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem field_target (n : Fin 32) (hn : n.val ≠ 0) (u v : Fin 6) :
    decide (bit (element n * point u * point v) ≠ 0) = numericTarget n.val u v := by
  refine Fin.cases ?_ (fun i => ?_) u
  · simp [point, numericTarget]
  · refine Fin.cases ?_ (fun j => ?_) v
    · simp [point, numericTarget]
    · simp only [point, Fin.cases_succ, basis_pow]
      have h := compact_table n i j
      change decide (bit (element n * alpha ^ i.val * alpha ^ j.val) ≠ 0) = _
      rw [h]
      simp only [numericTarget, Fin.val_succ, Nat.succ_ne_zero, false_or, ↓reduceIte, Nat.add_sub_cancel]
      split <;> simp_all [PEqualNP.Outside.L_meta_29716.Cert.gfMul, PEqualNP.Outside.L_meta_29716.Basis.gfMul]


set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def chosen (n : Fin 32) : Finset (Fin 2) :=
  Finset.univ.filter (fun j => (selected n.val).1.testBit j.val = true)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
def table (j : Fin 2) (u v : Fin 6) : Bool :=
  prepValue (if j = 0 then 35 else 50) u v

set_option maxRecDepth 20000 in
set_option maxHeartbeats 50000000 in
theorem chosen_parity (n : Fin 32) (u v : Fin 6) :
    (((chosen n).filter (fun j => table j u v)).card % 2 == 1) =
      xor ((selected n.val).1.testBit 0 && prepValue 35 u v)
          ((selected n.val).1.testBit 1 && prepValue 50 u v) := by
  simp only [chosen, table, Finset.filter_filter]
  cases h0 : (selected n.val).1.testBit 0 <;>
    cases h1 : (selected n.val).1.testBit 1 <;>
    cases a : prepValue 35 u v <;> cases b : prepValue 50 u v <;>
    simp [Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, h0,h1,a,b]

end PEqualNP.Outside.L_meta_29716.Bridge

theorem PEqualNP.Outside.L_meta_29716 :
(
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∃ (k s g : ℕ), 2 ≤ s ∧ k % 2 = 1 ∧ 5 ≤ k ∧ s*(s+1)/2 < k ∧ k ≤ s*(2*s+1) ∧
  ∃ (basis : Module.Basis (Fin k) F (GaloisField 2 k))
    (bit : GaloisField 2 k →ₗ[F] F), bit ≠ 0 ∧
  let n := k+1
  let point : Fin n → GaloisField 2 k := Fin.cases 0 basis
  let mult := fun (z : GaloisField 2 k) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : GaloisField 2 k) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)

  ∃ T : Fin g → Fin n → Fin n → Bool, fits n n g T s ∧
    ∀ z : GaloisField 2 k, z ≠ 0 →
      ∃ S : Finset (Fin g), fits n n 1 (fun _ => residual T S z) (k/2)
) := by
  dsimp only
  refine ⟨5, 2, 2, by decide, by decide, by decide, by decide, by decide,
    PEqualNP.Outside.L_meta_29716.Basis.basis, PEqualNP.Outside.L_meta_29716.Basis.bit,
    PEqualNP.Outside.L_meta_29716.Basis.bit_nonzero, ?_⟩
  refine ⟨PEqualNP.Outside.L_meta_29716.Bridge.table, ?_, ?_⟩
  · refine ⟨⟨PEqualNP.Outside.L_meta_29716.Cert.realPrep, 0⟩,
      fun j => if j = 0 then 35 else 50, ?_, ?_, ?_, ?_⟩
    · exact PEqualNP.Outside.L_meta_29716.Cert.prep_legal_1.1
    · intro g hg
      exact of_decide_eq_true (List.all_eq_true.mp PEqualNP.Outside.L_meta_29716.Cert.prep_legal_1.2.1 g hg)
    · exact PEqualNP.Outside.L_meta_29716.Cert.prep_legal_1.2.2.1
    · intro j
      fin_cases j
      · exact ⟨PEqualNP.Outside.L_meta_29716.Cert.prep_legal_1.2.2.2, fun u v => rfl⟩
      · exact ⟨PEqualNP.Outside.L_meta_29716.Cert.prep_legal_2.2.2.2, fun u v => rfl⟩
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := PEqualNP.Outside.L_meta_29716.Basis.nonzero_rep z hz
    refine ⟨PEqualNP.Outside.L_meta_29716.Bridge.chosen n, ?_⟩
    let c := PEqualNP.Outside.L_meta_29716.Cert.selected n.val
    have legal := PEqualNP.Outside.L_meta_29716.Cert.legal_all n hn
    refine ⟨⟨c.2.1, c.2.2⟩, fun _ => c.2.2, ?_, ?_, ?_, ?_⟩
    · exact legal.1
    · intro g hg
      exact of_decide_eq_true (List.all_eq_true.mp legal.2.1 g hg)
    · exact legal.2.2.1
    · intro j
      refine ⟨legal.2.2.2, ?_⟩
      intro u v
      have hc := PEqualNP.Outside.L_meta_29716.Cert.real_all n hn u v
      unfold PEqualNP.Outside.L_meta_29716.Cert.realCorrect PEqualNP.Outside.L_meta_29716.Cert.residualGoal at hc
      have hc := of_decide_eq_true hc
      change PEqualNP.CircuitLowerBounds.Circuit.eval ⟨(PEqualNP.Outside.L_meta_29716.Cert.selected n.val).2.1,
          (PEqualNP.Outside.L_meta_29716.Cert.selected n.val).2.2⟩ (PEqualNP.Outside.L_meta_29716.Cert.oneEach u v) =
        xor (decide (PEqualNP.Outside.L_meta_29716.Basis.bit (PEqualNP.Outside.L_meta_29716.Basis.element n *
          PEqualNP.Outside.L_meta_29716.Bridge.point u * PEqualNP.Outside.L_meta_29716.Bridge.point v) ≠ 0))
          (((PEqualNP.Outside.L_meta_29716.Bridge.chosen n).filter (fun j => PEqualNP.Outside.L_meta_29716.Bridge.table j u v)).card % 2 == 1)
      rw [PEqualNP.Outside.L_meta_29716.Bridge.field_target n hn u v,
        PEqualNP.Outside.L_meta_29716.Bridge.chosen_parity n u v]
      exact hc
