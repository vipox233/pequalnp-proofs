import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_715

open Finset

def bits (k : ℕ) (v : Fin (2 ^ k)) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)

def dot (k : ℕ) (u v : Fin (2 ^ k)) : Bool := ((bits k u ∩ bits k v).card % 2 == 1)

def G (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (u v : Fin (2 ^ k)) : Bool :=
  (dot k u v != rf u) != cf v

def β (b : Bool) : ZMod 2 := if b then 1 else 0

def ψ (k : ℕ) (x : ℕ) : Fin k → ZMod 2 := fun i => β (x.testBit i.val)

lemma z2_self (z : ZMod 2) : z + z = 0 := by revert z; decide

lemma ψ_xor (k x y : ℕ) : ψ k (x ^^^ y) = ψ k x + ψ k y := by
  funext i
  simp only [ψ, Pi.add_apply, Nat.testBit_xor]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

lemma ψ_zero_iff (k x : ℕ) (hx : x < 2 ^ k) : ψ k x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < k
    · have := congrFun h ⟨i, hi⟩
      simp only [ψ, Pi.zero_apply, β] at this
      by_contra hne
      simp only [Bool.not_eq_false] at hne
      rw [hne] at this
      exact absurd this (by decide)
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)))
  · rintro rfl
    funext i
    simp [ψ, β]

lemma ψ_add_ne (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (hne : x ≠ y) :
    ψ k x + ψ k y ≠ 0 := by
  intro h
  rw [← ψ_xor, ψ_zero_iff k _ (Nat.xor_lt_two_pow hx hy)] at h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun z => z.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this
  cases x.testBit i <;> cases y.testBit i <;> decide

lemma ψ_inj (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (h : ψ k x = ψ k y) : x = y := by
  by_contra hne
  apply ψ_add_ne k x y hx hy hne
  rw [h]
  funext i
  exact z2_self _

lemma dot_eq (k : ℕ) (u v : Fin (2 ^ k)) : β (dot k u v) = ψ k u.val ⬝ᵥ ψ k v.val := by
  have hI : bits k u ∩ bits k v =
      (Finset.univ : Finset (Fin k)).filter (fun i => u.val.testBit i.val ∧ v.val.testBit i.val) := by
    ext i; simp [bits]
  have h1 : ψ k u.val ⬝ᵥ ψ k v.val = ((bits k u ∩ bits k v).card : ZMod 2) := by
    rw [hI, Finset.natCast_card_filter]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ψ, β]
    cases u.val.testBit i.val <;> cases v.val.testBit i.val <;> simp
  rw [h1]
  unfold dot
  generalize (bits k u ∩ bits k v).card = c
  rw [← ZMod.natCast_mod c 2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> rfl

lemma bool_ne (p q : Bool) : p ≠ q ↔ β p + β q = 1 := by cases p <;> cases q <;> decide

lemma bool_eq (p q : Bool) : p = q ↔ β p + β q = 0 := by cases p <;> cases q <;> decide

lemma βG (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (u v : Fin (2 ^ k)) :
    β (G k rf cf u v) = β (dot k u v) + β (rf u) + β (cf v) := by
  unfold G
  cases dot k u v <;> cases rf u <;> cases cf v <;> decide

lemma pairG (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (a b j : Fin (2 ^ k)) :
    β (G k rf cf a j) + β (G k rf cf b j) =
      (ψ k a.val + ψ k b.val) ⬝ᵥ ψ k j.val + (β (rf a) + β (rf b)) := by
  rw [βG, βG, dot_eq, dot_eq, add_dotProduct]
  linear_combination z2_self (β (cf j))

lemma z2_one (x c : ZMod 2) : x + c = 1 ↔ x = 1 + c := by revert x c; decide

lemma z2_zero (x c : ZMod 2) : x + c = 0 ↔ x = c := by revert x c; decide

lemma fiber (k m : ℕ) (R : Fin m → (Fin k → ZMod 2)) (hR : LinearIndependent (ZMod 2) R)
    (t : Fin m → ZMod 2) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ i, R i ⬝ᵥ w = t i)).card
      = 2 ^ (k - m) := by
  classical
  let L := Matrix.mulVecLin (Matrix.of R)
  have hL : ∀ w, L w = fun i => R i ⬝ᵥ w := fun w => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have h1 := Matrix.rank_eq_finrank_span_row (Matrix.of R)
    unfold Matrix.rank at h1
    rw [h1]
    exact (finrank_span_eq_card hR).trans (Fintype.card_fin m)
  have hfib : ∀ t, ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => L w = t)).card =
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => L w = 0)).card := by
    intro t
    obtain ⟨w0, hw0⟩ := hsurj t
    apply Finset.card_bij (fun w _ => w - w0)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [map_sub, hw, hw0, sub_self]
    · intro w1 _ w2 _ h
      simpa using h
    · intro w hw
      refine ⟨w + w0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [map_add, hw, hw0, zero_add]
      · simp
  have htot := Finset.card_eq_sum_card_fiberwise (f := L)
    (s := (Finset.univ : Finset (Fin k → ZMod 2))) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun t _ => hfib t), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, smul_eq_mul] at htot
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
  have heq : ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ i, R i ⬝ᵥ w = t i)) =
      (Finset.univ.filter (fun w => L w = t)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hL, funext_iff]
  rw [heq, hfib]
  set X := ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => L w = 0)).card
  have hX : 1 ≤ X := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hmk : m ≤ k := by
    have : 2 ^ m ≤ 2 ^ k := by rw [htot]; exact Nat.le_mul_of_pos_right _ hX
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have h2 : 2 ^ k = 2 ^ m * 2 ^ (k - m) := by rw [← pow_add, Nat.add_sub_cancel' hmk]
  rw [h2] at htot
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) htot).symm

lemma z2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

theorem main (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (_hk : 3 ≤ k) (a b c d : Fin (2 ^ k))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun j : Fin (2 ^ k) =>
      G k rf cf a j ≠ G k rf cf b j ∧ G k rf cf a j ≠ G k rf cf c j ∧
        G k rf cf a j = G k rf cf d j)).card =
      if (a.val ^^^ b.val ^^^ c.val ^^^ d.val) = 0 then
        (if (rf a != rf b) = (rf c != rf d) then 2 ^ (k - 2) else 0) else 2 ^ (k - 3) := by
  classical
  set R0 := ψ k a.val + ψ k b.val with hR0
  set R1 := ψ k a.val + ψ k c.val with hR1
  set R2 := ψ k a.val + ψ k d.val with hR2
  set t0 := 1 + (β (rf a) + β (rf b)) with ht0
  set t1 := 1 + (β (rf a) + β (rf c)) with ht1
  set t2 := β (rf a) + β (rf d) with ht2
  let Q := fun w : Fin k → ZMod 2 => R0 ⬝ᵥ w = t0 ∧ R1 ⬝ᵥ w = t1 ∧ R2 ⬝ᵥ w = t2
  have hmem : ∀ j : Fin (2 ^ k), (G k rf cf a j ≠ G k rf cf b j ∧ G k rf cf a j ≠ G k rf cf c j ∧
        G k rf cf a j = G k rf cf d j) ↔ Q (ψ k j.val) := by
    intro j
    rw [bool_ne, bool_ne, bool_eq, pairG, pairG, pairG, z2_one, z2_one, z2_zero]
  have hbij : Function.Bijective (fun j : Fin (2 ^ k) => ψ k j.val) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y h => Fin.ext (ψ_inj k _ _ x.isLt y.isLt h), ?_⟩
    simp [ZMod.card]
  have hcard : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun j : Fin (2 ^ k) =>
      G k rf cf a j ≠ G k rf cf b j ∧ G k rf cf a j ≠ G k rf cf c j ∧
        G k rf cf a j = G k rf cf d j)).card =
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter Q).card := by
    apply Finset.card_bij (fun j _ => ψ k j.val)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (hmem j).mp hj
    · intro x _ y _ h
      exact hbij.1 h
    · intro w hw
      obtain ⟨j, hj⟩ := hbij.2 w
      refine ⟨j, ?_, hj⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [hmem, show ψ k j.val = w from hj]
      exact hw
  rw [hcard]
  have hne01 : R0 + R1 = ψ k b.val + ψ k c.val := by
    funext i; simp only [hR0, hR1, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k b.val i = y; generalize ψ k c.val i = z
    revert x y z; decide
  have hne02 : R0 + R2 = ψ k b.val + ψ k d.val := by
    funext i; simp only [hR0, hR2, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k b.val i = y; generalize ψ k d.val i = z
    revert x y z; decide
  have hne12 : R1 + R2 = ψ k c.val + ψ k d.val := by
    funext i; simp only [hR1, hR2, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k c.val i = y; generalize ψ k d.val i = z
    revert x y z; decide
  have h012 : R0 + R1 + R2 = ψ k (a.val ^^^ b.val ^^^ c.val ^^^ d.val) := by
    rw [ψ_xor, ψ_xor, ψ_xor]
    funext i; simp only [hR0, hR1, hR2, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k b.val i = y; generalize ψ k c.val i = z
    generalize ψ k d.val i = w
    revert x y z w; decide
  have nR0 : R0 ≠ 0 := ψ_add_ne k _ _ a.isLt b.isLt (fun h => hab (Fin.ext h))
  have nR1 : R1 ≠ 0 := ψ_add_ne k _ _ a.isLt c.isLt (fun h => hac (Fin.ext h))
  have nR2 : R2 ≠ 0 := ψ_add_ne k _ _ a.isLt d.isLt (fun h => had (Fin.ext h))
  have n01 : R0 + R1 ≠ 0 := by rw [hne01]; exact ψ_add_ne k _ _ b.isLt c.isLt (fun h => hbc (Fin.ext h))
  have n02 : R0 + R2 ≠ 0 := by rw [hne02]; exact ψ_add_ne k _ _ b.isLt d.isLt (fun h => hbd (Fin.ext h))
  have n12 : R1 + R2 ≠ 0 := by rw [hne12]; exact ψ_add_ne k _ _ c.isLt d.isLt (fun h => hcd (Fin.ext h))
  split_ifs with hpar hev
  · -- parallelogram, even
    have hR2' : R2 = R0 + R1 := by
      have : R0 + R1 + R2 = 0 := by rw [h012, hpar]; funext i; simp [ψ, β]
      funext i
      have := congrFun this i
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      revert this
      generalize R0 i = x; generalize R1 i = y; generalize R2 i = z
      revert x y z; decide
    have ht : t2 = t0 + t1 := by
      simp only [ht0, ht1, ht2]
      revert hev
      cases rf a <;> cases rf b <;> cases rf c <;> cases rf d <;> decide
    have hli : LinearIndependent (ZMod 2) ![R0, R1] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      rcases z2_cases (g 0) with h0 | h0 <;> rcases z2_cases (g 1) with h1 | h1 <;>
        rw [h0, h1] at hg <;> simp at hg
      · fin_cases i <;> simp [h0, h1]
      · exact absurd hg nR1
      · exact absurd hg nR0
      · exact absurd hg n01
    rw [← fiber k 2 ![R0, R1] hli ![t0, t1]]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, hR2', ht, add_dotProduct]
    constructor
    · rintro ⟨h0, h1, _⟩; exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0, h1, by rw [h0, h1]⟩
  · -- parallelogram, odd
    have hR2' : R2 = R0 + R1 := by
      have : R0 + R1 + R2 = 0 := by rw [h012, hpar]; funext i; simp [ψ, β]
      funext i
      have := congrFun this i
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      revert this
      generalize R0 i = x; generalize R1 i = y; generalize R2 i = z
      revert x y z; decide
    have ht : t2 ≠ t0 + t1 := by
      simp only [ht0, ht1, ht2]
      revert hev
      cases rf a <;> cases rf b <;> cases rf c <;> cases rf d <;> decide
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w - ⟨h0, h1, h2⟩
    rw [hR2', add_dotProduct, h0, h1] at h2
    exact ht h2.symm
  · -- independent
    have nall : R0 + R1 + R2 ≠ 0 := by
      rw [h012]; intro h
      exact hpar ((ψ_zero_iff k _ (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
        (Nat.xor_lt_two_pow a.isLt b.isLt) c.isLt) d.isLt)).mp h)
    have hli : LinearIndependent (ZMod 2) ![R0, R1, R2] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
      rcases z2_cases (g 0) with h0 | h0 <;> rcases z2_cases (g 1) with h1 | h1 <;>
        rcases z2_cases (g 2) with h2 | h2 <;> rw [h0, h1, h2] at hg <;> simp at hg
      · fin_cases i <;> simp [h0, h1, h2]
      · exact absurd hg nR2
      · exact absurd hg nR1
      · exact absurd hg n12
      · exact absurd hg nR0
      · exact absurd hg n02
      · exact absurd hg n01
      · exact absurd hg nall
    rw [← fiber k 3 ![R0, R1, R2] hli ![t0, t1, t2]]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.forall_iff, and_true]

end PEqualNP.Outside.L_lib_715

theorem PEqualNP.Outside.L_lib_715 : ∀ (k : ℕ) (rowFlip colFlip : Fin (2^k) → Bool), 3 ≤ k →
  let N := 2 ^ k
  let bits := fun (v : Fin N) =>
    (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
  let dot := fun (u v : Fin N) => ((bits u ∩ bits v).card % 2 == 1)
  let G := fun (u v : Fin N) => (dot u v != rowFlip u) != colFlip v
  ∀ (a b c d : Fin N), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    let split := Finset.univ.filter (fun j : Fin N =>
      G a j ≠ G b j ∧ G a j ≠ G c j ∧ G a j = G d j)
    let parallelogram := (a.val ^^^ b.val ^^^ c.val ^^^ d.val) = 0
    let evenFlip := (rowFlip a != rowFlip b) = (rowFlip c != rowFlip d)
    split.card = if parallelogram then (if evenFlip then 2^(k-2) else 0) else 2^(k-3) := by
  intro k rowFlip colFlip hk N bits dot G a b c d hab hac had hbc hbd hcd split parallelogram evenFlip
  exact PEqualNP.Outside.L_lib_715.main k rowFlip colFlip hk a b c d hab hac had hbc hbd hcd
