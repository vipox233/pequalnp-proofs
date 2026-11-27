import Mathlib
import PEqualNP.Defs
-- The four-row fiber count follows L_lib_715. The circuit decomposition and
-- single-boundary factorization follow L_meta_25806. Their helpers are included
-- here because this step lists PEqualNP.Defs as its only project dependency.

namespace PEqualNP.Outside.L_meta_25875.Fibers

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

lemma main (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (_hk : 3 ≤ k) (a b c d : Fin (2 ^ k))
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

end PEqualNP.Outside.L_meta_25875.Fibers

namespace PEqualNP.Outside.L_meta_25875.Fibers
lemma enumeration : ∀ (k : ℕ) (rowFlip colFlip : Fin (2^k) → Bool), 3 ≤ k →
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
  exact PEqualNP.Outside.L_meta_25875.Fibers.main k rowFlip colFlip hk a b c d hab hac had hbc hbd hcd
end PEqualNP.Outside.L_meta_25875.Fibers

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def brun (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma brun_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    brun (gs ++ [g]) x = brun gs x ++ [g.op ((brun gs x).getD g.left false) ((brun gs x).getD g.right false)] := by
  simp [brun, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma brun_length (gs : List BinaryGate) (x : List Bool) : (brun gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [brun]
  | append_singleton gs g ih => rw [brun_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma brun_init (gs hs : List BinaryGate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (brun (gs ++ hs) x).getD i false = (brun gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, brun_snoc, getD_lt _ _ _ (by
      rw [brun_length, List.length_append]; omega), ih]

abbrev Ref := Bool ⊕ ((Bool → Bool) × ℕ)

def val (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr r => r.1 (w.getD r.2 false)

def idx : Ref → ℕ
  | .inl _ => 0
  | .inr r => r.2

def fn : Ref → Bool → Bool
  | .inl b => fun _ => b
  | .inr r => r.1

def Valid (N : ℕ) : Ref → Prop
  | .inl _ => True
  | .inr r => r.2 < N

def lift (f : Bool → Bool) : Ref → Ref
  | .inl b => .inl (f b)
  | .inr r => .inr (f ∘ r.1, r.2)

lemma val_fn (w : List Bool) (r : Ref) : val w r = fn r (w.getD (idx r) false) := by
  cases r <;> rfl

lemma val_lift (w : List Bool) (f : Bool → Bool) (r : Ref) : val w (lift f r) = f (val w r) := by
  cases r <;> rfl

lemma valid_lift (N : ℕ) (f : Bool → Bool) (r : Ref) (h : Valid N r) : Valid N (lift f r) := by
  cases r <;> exact h

lemma valid_mono {N M : ℕ} (h : N ≤ M) (r : Ref) (hr : Valid N r) : Valid M r := by
  cases r with
  | inl b => trivial
  | inr r => exact lt_of_lt_of_le hr h

lemma val_ext (gs hs : List BinaryGate) (x : List Bool) (r : Ref)
    (hr : Valid (x.length + gs.length) r) :
    val (brun (gs ++ hs) x) r = val (brun gs x) r := by
  cases r with
  | inl b => rfl
  | inr r => simp only [val]; rw [brun_init _ _ _ _ hr]

lemma idx_valid (N : ℕ) (r : Ref) (hN : 0 < N) (hr : Valid N r) : idx r < N := by
  cases r with
  | inl b => exact hN
  | inr r => exact hr

def Back (N : ℕ) (gs : List BinaryGate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].left < N + j ∧ gs[j].right < N + j

lemma back_append (N : ℕ) (gs hs : List BinaryGate) (hg : Back N gs)
    (hh : ∀ g ∈ hs, g.left < N + gs.length ∧ g.right < N + gs.length) : Back N (gs ++ hs) := by
  intro j hj
  by_cases h : j < gs.length
  · rw [List.getElem_append_left h]
    exact hg j h
  · have hj' : j - gs.length < hs.length := by simp at hj; omega
    rw [List.getElem_append_right (by omega)]
    have hm : hs[j - gs.length] ∈ hs := List.getElem_mem hj'
    obtain ⟨hl,hr⟩ := hh _ hm
    exact ⟨by omega,by omega⟩

lemma emit (N : ℕ) (hs : List BinaryGate) (g : Gate) (refs : ℕ → Ref)
    (hg : g.inputs.length ≤ 2) (hv : ∀ i, Valid (N + hs.length) (refs i)) :
    ∃ (r : Ref) (es : List BinaryGate), es.length ≤ (if g.inputs.length == 2 then 1 else 0) ∧
      Valid (N + hs.length + es.length) r ∧
      (0 < N → ∀ g ∈ es, g.left < N + hs.length ∧ g.right < N + hs.length) ∧
      ∀ x : List Bool, x.length = N →
        val (brun (hs ++ es) x) r = g.op.eval (g.inputs.map fun i => val (brun hs x) (refs i)) := by
  rcases g with ⟨op, is⟩
  rcases is with _ | ⟨a, _ | ⟨b, _ | ⟨c, is⟩⟩⟩
  · refine ⟨.inl (op.eval []), [], by simp, by trivial, by simp, ?_⟩
    intro x hx
    rfl
  · refine ⟨lift (fun v => op.eval [v]) (refs a), [], by simp, ?_, by simp, ?_⟩
    · simpa using valid_lift _ _ _ (hv a)
    · intro x hx
      simp only [List.append_nil, val_lift, List.map_cons, List.map_nil]
  · let gate : BinaryGate := ⟨fun u v => op.eval [fn (refs a) u, fn (refs b) v], idx (refs a), idx (refs b)⟩
    refine ⟨.inr (id, N + hs.length), [gate], by simp, by simp [Valid], ?_, ?_⟩
    · intro hN g hg
      have heq : g = gate := by simpa using hg
      subst g
      exact ⟨idx_valid _ _ (by omega) (hv a), idx_valid _ _ (by omega) (hv b)⟩
    intro x hx
    have he : N + hs.length = (brun hs x).length := by rw [brun_length, hx]
    change (brun (hs ++ [gate]) x).getD (N + hs.length) false = _
    rw [brun_snoc, he, getD_at]
    simp only [gate, List.map_cons, List.map_nil, val_fn]
  · simp at hg

lemma getD_ne (l : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  by_cases h : i < l.length
  · exact getD_lt _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma normalize_run (N : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (hs : List BinaryGate) (refs : ℕ → Ref),
      hs.length ≤ gs.countP (fun g => g.inputs.length == 2) ∧
      (∀ i, Valid (N + hs.length) (refs i)) ∧
      (0 < N → Back N hs) ∧
      ∀ x : List Bool, x.length = N → ∀ i,
        val (brun hs x) (refs i) = (run gs x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], (fun i => if i < N then .inr (id,i) else .inl false), by simp, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with hi
      · simpa [Valid] using hi
      · trivial
    · intro hN j hj
      simp at hj
    · intro x hx i
      by_cases hi : i < N
      · simp [hi, val, brun, run]
      · simp only [hi, ↓reduceIte, val, run, List.foldl_nil]
        exact (List.getD_eq_default _ _ (by omega)).symm
  | append_singleton gs g ih =>
    have hgs' : ∀ a ∈ gs, a.inputs.length ≤ 2 := by
      intro a ha
      exact hgs a (by simp [ha])
    have hg : g.inputs.length ≤ 2 := hgs g (by simp)
    obtain ⟨hs, refs, hc, hv, hb, heval⟩ := ih hgs'
    obtain ⟨r, es, he, hr, heb, hem⟩ := emit N hs g refs hg hv
    refine ⟨hs ++ es, (fun i => if i = N + gs.length then r else refs i), ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.countP_append, List.countP_singleton]
      omega
    · intro i
      dsimp only
      split_ifs
      · simpa [List.length_append, Nat.add_assoc] using hr
      · exact valid_mono (by simp) _ (hv i)
    · intro hN
      exact back_append N hs es (hb hN) (heb hN)
    · intro x hx i
      by_cases hi : i = N + gs.length
      · simp only [hi, ↓reduceIte]
        rw [hem x hx, run_snoc]
        have hlen : N + gs.length = (run gs x).length := by rw [run_length,hx]
        rw [hlen, getD_at]
        congr 1
        exact List.map_congr_left fun j _ => heval x hx j
      · simp only [hi, ↓reduceIte]
        rw [val_ext hs es x (refs i) (by rw [hx]; exact hv i), heval x hx i, run_snoc]
        exact (getD_ne _ _ _ (by rw [run_length,hx]; exact hi)).symm

lemma normalize_back (N : ℕ) (hN : 0 < N) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (B : BinaryCircuit) (out : Bool → Bool),
      B.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      Back N B.gates ∧ B.output < N + B.gates.length ∧
      ∀ x : List Bool, x.length = N → C.eval x = out (B.eval x) := by
  obtain ⟨hs, refs, hc, hv, hb, heval⟩ := normalize_run N C.gates hC
  refine ⟨⟨hs,idx (refs C.output)⟩, fn (refs C.output), hc, hb hN,
    idx_valid _ _ (by omega) (hv C.output), ?_⟩
  intro x hx
  change (run C.gates x).getD C.output false = fn (refs C.output) ((brun hs x).getD (idx (refs C.output)) false)
  rw [← heval x hx C.output, val_fn]

def down (k i : ℕ) : ℕ := if i < k then i else i - 1

def remap (k : ℕ) (g : BinaryGate) : BinaryGate :=
  ⟨g.op, down k g.left, down k g.right⟩

lemma getD_erase_down (l : List Bool) (k i : ℕ) (hi : i ≠ k) :
    (l.eraseIdx k).getD (down k i) false = l.getD i false := by
  simp only [down]
  split_ifs with h
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt h]
  · have hki : k ≤ i - 1 := by omega
    have hii : i - 1 + 1 = i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hki, hii]

lemma back_prefix (N : ℕ) (gs hs : List BinaryGate) (hb : Back N (gs ++ hs)) : Back N gs := by
  intro j hj
  have h := hb j (by simp; omega)
  simpa only [List.getElem_append_left hj] using h

lemma remap_eq_of_back (N : ℕ) (gs : List BinaryGate) (hb : Back N gs) :
    gs.map (remap (N + gs.length)) = gs := by
  calc
    gs.map (remap (N + gs.length)) = gs.map id := by
      apply List.map_congr_left
      intro g hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      obtain ⟨hl,hr⟩ := hb j hj
      simp only [remap, down, ite_eq_left (by omega : gs[j].left < N + gs.length),
        ite_eq_left (by omega : gs[j].right < N + gs.length), id_eq]
    _ = gs := List.map_id gs

lemma brun_erase (N : ℕ) (gs : List BinaryGate) (j : ℕ) (hj : j < gs.length)
    (hb : Back N gs) (hd : ∀ g ∈ gs, g.left ≠ N + j ∧ g.right ≠ N + j)
    (x : List Bool) (hx : x.length = N) :
    brun ((gs.eraseIdx j).map (remap (N + j))) x = (brun gs x).eraseIdx (N + j) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    have hb' : Back N gs := back_prefix N gs [g] hb
    have hd' : ∀ a ∈ gs, a.left ≠ N + j ∧ a.right ≠ N + j := by
      intro a ha
      exact hd a (by simp [ha])
    have hdg := hd g (by simp)
    by_cases hj' : j < gs.length
    · rw [List.eraseIdx_append_of_lt_length hj', List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [brun_snoc, ih hj' hb' hd', brun_snoc,
        List.eraseIdx_append_of_lt_length (by rw [brun_length,hx]; omega)]
      congr 1
      simp only [remap, getD_erase_down _ _ _ hdg.1, getD_erase_down _ _ _ hdg.2]
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.eraseIdx_append_of_length_le (by omega)]
      simp only [Nat.sub_self, List.eraseIdx_zero, List.tail_cons, List.append_nil]
      rw [remap_eq_of_back N gs hb', brun_snoc]
      have hl : N + gs.length = (brun gs x).length := by rw [brun_length,hx]
      rw [hl, List.eraseIdx_append_of_length_le (by omega)]
      simp

lemma back_erase (N : ℕ) (gs : List BinaryGate) (j : ℕ) (hj : j < gs.length)
    (hb : Back N gs) (hd : ∀ g ∈ gs, g.left ≠ N + j ∧ g.right ≠ N + j) :
    Back N ((gs.eraseIdx j).map (remap (N + j))) := by
  intro i hi
  have hi' : i < (gs.eraseIdx j).length := by simpa using hi
  rw [List.getElem_map]
  by_cases hij : i < j
  · rw [List.getElem_eraseIdx_of_lt hi' hij]
    have hi0 : i < gs.length := by have := List.length_eraseIdx_le gs j; omega
    obtain ⟨hl,hr⟩ := hb i hi0
    simp only [remap, down]
    constructor <;> split_ifs <;> omega
  · rw [List.getElem_eraseIdx_of_ge hi' (by omega)]
    have hi0 : i + 1 < gs.length := by rw [List.length_eraseIdx_of_lt hj] at hi'; omega
    obtain ⟨hl,hr⟩ := hb (i+1) hi0
    obtain ⟨hdl,hdr⟩ := hd gs[i+1] (List.getElem_mem hi0)
    simp only [remap, down]
    constructor <;> split_ifs <;> omega

def eraseCircuit (N : ℕ) (C : BinaryCircuit) (j : ℕ) : BinaryCircuit :=
  ⟨(C.gates.eraseIdx j).map (remap (N+j)), down (N+j) C.output⟩

lemma eraseCircuit_spec (N : ℕ) (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length)
    (hb : Back N C.gates) (hd : ∀ g ∈ C.gates, g.left ≠ N + j ∧ g.right ≠ N + j)
    (ho : C.output < N + C.gates.length) (hne : C.output ≠ N+j) :
    (eraseCircuit N C j).size + 1 = C.size ∧
    Back N (eraseCircuit N C j).gates ∧
    (eraseCircuit N C j).output < N + (eraseCircuit N C j).gates.length ∧
    ∀ x : List Bool, x.length = N → (eraseCircuit N C j).eval x = C.eval x := by
  refine ⟨?_, back_erase N C.gates j hj hb hd, ?_, ?_⟩
  · simp only [eraseCircuit, BinaryCircuit.size, List.length_map, List.length_eraseIdx_of_lt hj]
    omega
  · simp only [eraseCircuit, List.length_map, List.length_eraseIdx_of_lt hj, down]
    split_ifs <;> omega
  · intro x hx
    change (brun ((C.gates.eraseIdx j).map (remap (N+j))) x).getD (down (N+j) C.output) false =
      (brun C.gates x).getD C.output false
    rw [brun_erase N C.gates j hj hb hd x hx, getD_erase_down _ _ _ hne]

def Live (N : ℕ) (C : BinaryCircuit) : Prop :=
  ∀ i (hi : i < C.gates.length), N+i ≠ C.output →
    ∃ (j : ℕ) (hj : j < C.gates.length), i < j ∧ (C.gates[j].left = N+i ∨ C.gates[j].right = N+i)

lemma prune (N : ℕ) (C : BinaryCircuit) (hb : Back N C.gates)
    (ho : C.output < N + C.gates.length) :
    ∃ D : BinaryCircuit, D.size ≤ C.size ∧ Back N D.gates ∧
      D.output < N + D.gates.length ∧
      (∀ x : List Bool, x.length = N → D.eval x = C.eval x) ∧ Live N D := by
  classical
  have hex : ∃ k, ∃ D : BinaryCircuit, Back N D.gates ∧
      D.output < N + D.gates.length ∧ D.size ≤ k ∧
      ∀ x : List Bool, x.length = N → D.eval x = C.eval x :=
    ⟨C.size,C,hb,ho,le_rfl,fun x hx => rfl⟩
  obtain ⟨D,hback,hout,hsize,hval⟩ := Nat.find_spec hex
  have hmin : Nat.find hex ≤ C.size :=
    Nat.find_min' hex ⟨C,hb,ho,le_rfl,fun x hx => rfl⟩
  refine ⟨D,hsize.trans hmin,hback,hout,hval,?_⟩
  intro i hi hio
  by_contra hn
  have hd : ∀ g ∈ D.gates, g.left ≠ N+i ∧ g.right ≠ N+i := by
    intro g hg
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    obtain ⟨hl,hr⟩ := hback j hj
    constructor
    · intro he
      exact hn ⟨j,hj,by omega,Or.inl he⟩
    · intro he
      exact hn ⟨j,hj,by omega,Or.inr he⟩
  obtain ⟨hes,heb,heo,hev⟩ := eraseCircuit_spec N D i hi hback hd hout hio.symm
  have hlower : Nat.find hex ≤ (eraseCircuit N D i).size :=
    Nat.find_min' hex ⟨eraseCircuit N D i,heb,heo,le_rfl,
      fun x hx => (hev x hx).trans (hval x hx)⟩
  omega

def Edge (N : ℕ) (C : BinaryCircuit) (a b : ℕ) : Prop :=
  ∃ (j : ℕ) (hj : j < C.gates.length), b = N+j ∧ (C.gates[j].left = a ∨ C.gates[j].right = a)

lemma live_reaches (N : ℕ) (C : BinaryCircuit) (hl : Live N C) :
    ∀ i, i < C.gates.length → Relation.ReflTransGen (Edge N C) (N+i) C.output := by
  have aux : ∀ k i, C.gates.length-i = k → i < C.gates.length →
      Relation.ReflTransGen (Edge N C) (N+i) C.output := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hki hi
      by_cases hio : N+i = C.output
      · rw [hio]
      · obtain ⟨j,hj,hij,hr⟩ := hl i hi hio
        have tail := ih (C.gates.length-j) (by omega) j rfl hj
        exact (Relation.ReflTransGen.single ⟨j,hj,rfl,hr⟩).trans tail
  intro i hi
  exact aux (C.gates.length-i) i rfl hi

lemma live_output_last (N : ℕ) (C : BinaryCircuit) (hl : Live N C)
    (hn : 0 < C.gates.length) : C.output = N + (C.gates.length - 1) := by
  by_contra ho
  obtain ⟨j,hj,hij,hr⟩ := hl (C.gates.length-1) (by omega) (fun h => ho h.symm)
  omega

lemma normalize_live (N : ℕ) (hN : 0 < N) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ (B : BinaryCircuit) (out : Bool → Bool),
      B.size ≤ C.gates.countP (fun g => g.inputs.length == 2) ∧
      Back N B.gates ∧ B.output < N + B.gates.length ∧ Live N B ∧
      (∀ i, i < B.gates.length → Relation.ReflTransGen (Edge N B) (N+i) B.output) ∧
      ∀ x : List Bool, x.length = N → C.eval x = out (B.eval x) := by
  obtain ⟨B,out,hsize,hback,hout,heval⟩ := normalize_back N hN C hC
  obtain ⟨D,hds,hdb,hdo,hdv,hdl⟩ := prune N B hback hout
  refine ⟨D,out,hds.trans hsize,hdb,hdo,hdl,live_reaches N D hdl,?_⟩
  intro x hx
  rw [heval x hx,hdv x hx]

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

abbrev gatesOf (C : Circuit) : Finset ℕ := Finset.range C.size
abbrev readsOf (C : Circuit) (w : ℕ) : ℕ := readsIn C (Finset.range C.size) w
def isBinOp (_op : GateOp) : Prop := True

lemma readsIn_empty (C : Circuit) (w : ℕ) : readsIn C ∅ w = 0 := by
  simp [readsIn]

lemma readsIn_insert (C : Circuit) (G : Finset ℕ) (j w : ℕ) (hj : j ∉ G) :
    readsIn C (insert j G) w = (gateAt C j).inputs.count w + readsIn C G w := by
  unfold readsIn
  exact Finset.sum_insert hj

lemma readsIn_union (C : Circuit) (G1 G2 : Finset ℕ) (w : ℕ) (h : Disjoint G1 G2) :
    readsIn C (G1 ∪ G2) w = readsIn C G1 w + readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_union h

lemma readsIn_mono (C : Circuit) {G1 G2 : Finset ℕ} (h : G1 ⊆ G2) (w : ℕ) :
    readsIn C G1 w ≤ readsIn C G2 w := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset h

lemma readsIn_eq_zero_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    readsIn C G w = 0 ↔ ∀ j ∈ G, w ∉ (gateAt C j).inputs := by
  unfold readsIn
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h j hj hw
    have hp : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hz := h j hj
    omega
  · intro h j hj
    exact List.count_eq_zero.mpr (h j hj)

lemma readsIn_pos_iff (C : Circuit) (G : Finset ℕ) (w : ℕ) :
    0 < readsIn C G w ↔ ∃ j ∈ G, w ∈ (gateAt C j).inputs := by
  constructor
  · intro hp
    by_contra h
    have hz : readsIn C G w = 0 := (readsIn_eq_zero_iff C G w).2 (fun j hj hw => h ⟨j, hj, hw⟩)
    omega
  · rintro ⟨j, hj, hw⟩
    have hc : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn
    omega

lemma readsIn_ge_of_mem (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ G) (hw : w ∈ (gateAt C j).inputs) : 1 ≤ readsIn C G w :=
  (readsIn_pos_iff C G w).2 ⟨j, hj, hw⟩

lemma readsIn_eq_one_unique (C : Circuit) (G : Finset ℕ) (w : ℕ) (h : readsIn C G w = 1) :
    ∃ j ∈ G, w ∈ (gateAt C j).inputs ∧ (gateAt C j).inputs.count w = 1 ∧
      ∀ j' ∈ G, w ∈ (gateAt C j').inputs → j' = j := by
  obtain ⟨j, hj, hw⟩ := (readsIn_pos_iff C G w).1 (by omega)
  have hcpos : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
  have hcle : (gateAt C j).inputs.count w ≤ 1 := by
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hj
    unfold readsIn at h
    omega
  refine ⟨j, hj, hw, by omega, ?_⟩
  intro j' hj' hw'
  by_contra hne
  have hc' : 0 < (gateAt C j').inputs.count w := List.count_pos_iff.mpr hw'
  have hsub : ({j, j'} : Finset ℕ) ⊆ G := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun i => (gateAt C i).inputs.count w) hsub
  rw [Finset.sum_pair (Ne.symm hne)] at hle
  unfold readsIn at h
  omega

lemma readsIn_disjoint_zero (C : Circuit) {G1 G2 : Finset ℕ} {w : ℕ}
    (h1 : G1 ⊆ gatesOf C) (h2 : G2 ⊆ gatesOf C) (hdisj : Disjoint G1 G2)
    (hr : readsOf C w = 1) (h1r : readsIn C G1 w = 1) : readsIn C G2 w = 0 := by
  have hsub : G1 ∪ G2 ⊆ gatesOf C := Finset.union_subset h1 h2
  have hle := readsIn_mono C hsub w
  rw [readsIn_union C G1 G2 w hdisj] at hle
  change readsIn C (gatesOf C) w = 1 at hr
  omega

lemma readsIn_zero_of_count_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hj : j ∈ gatesOf C) (hG : G ⊆ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (hc : (gateAt C j).inputs.count w = 1) : readsIn C G w = 0 := by
  refine readsIn_disjoint_zero C (G1 := {j}) (G2 := G)
    (Finset.singleton_subset_iff.2 hj) hG (Finset.disjoint_singleton_left.2 hn) hr ?_
  simpa [readsIn] using hc

lemma count_zero_of_readsIn_one (C : Circuit) {G : Finset ℕ} {j w : ℕ}
    (hG : G ⊆ gatesOf C) (hj : j ∈ gatesOf C) (hn : j ∉ G)
    (hr : readsOf C w = 1) (h1 : readsIn C G w = 1) : (gateAt C j).inputs.count w = 0 := by
  have hz := readsIn_disjoint_zero C (G1 := G) (G2 := {j})
    hG (Finset.singleton_subset_iff.2 hj) (Finset.disjoint_singleton_right.2 hn) hr h1
  simpa [readsIn] using hz

lemma readsIn_ge_bound_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    {G : Finset ℕ} (hG : G ⊆ gatesOf C) {r : ℕ} (hbound : ∀ j ∈ G, n + j ≤ r) :
    readsIn C G r = 0 := by
  rw [readsIn_eq_zero_iff]
  intro j hj hr
  have hjlt : j < C.gates.length := Finset.mem_range.1 (hG hj)
  have hlt := hback j hjlt r hr
  have hle := hbound j hj
  omega

lemma reads_output_zero (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) : readsOf C C.output = 0 := by
  refine readsIn_ge_bound_zero n C hback (Finset.Subset.refl _) ?_
  intro j hj
  have hjlt : j < C.size := Finset.mem_range.1 hj
  omega

lemma ne_output_of_reads_pos (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {w : ℕ} (hw : 0 < readsOf C w) : C.output ≠ w := by
  rintro rfl
  have hz := reads_output_zero n C hback hout
  omega

lemma gateAt_mem_gates (C : Circuit) {j : ℕ} (hj : j < C.size) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  have hlen : j < C.gates.length := hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

lemma list_len2_eq (l : List ℕ) (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at h ⊢

lemma list_len1_eq (l : List ℕ) (h : l.length = 1) :
    l = [l.getD 0 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h ⊢

lemma count_pair_eq_one_left {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count a = 1 := by
  simp [h]

lemma count_pair_eq_one_right {a b : ℕ} (h : a ≠ b) : ([a, b] : List ℕ).count b = 1 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

lemma count_pair_eq_two {a : ℕ} : ([a, a] : List ℕ).count a = 2 := by
  simp

lemma count_pair_eq_zero {a b x : ℕ} (ha : x ≠ a) (hb : x ≠ b) :
    ([a, b] : List ℕ).count x = 0 := by
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

inductive BTree
  | priv (w : ℕ) : BTree
  | mark (w : ℕ) : BTree
  | node (j : ℕ) (l r : BTree) : BTree

def BTree.root (n : ℕ) : BTree → ℕ
  | BTree.priv w => w
  | BTree.mark w => w
  | BTree.node j _ _ => n + j

def BTree.marks : BTree → ℕ
  | BTree.priv _ => 0
  | BTree.mark _ => 1
  | BTree.node _ l r => l.marks + r.marks

def BTree.privs : BTree → Finset ℕ
  | BTree.priv w => {w}
  | BTree.mark _ => ∅
  | BTree.node _ l r => l.privs ∪ r.privs

def BTree.gates : BTree → Finset ℕ
  | BTree.priv _ => ∅
  | BTree.mark _ => ∅
  | BTree.node j l r => insert j (l.gates ∪ r.gates)

def BTree.wires (n : ℕ) (t : BTree) : Finset ℕ :=
  t.privs ∪ t.gates.image (fun k => n + k)

def BTree.nonMark : BTree → Prop
  | BTree.mark _ => False
  | _ => True

def GoodTree (n : ℕ) (C : Circuit) : BTree → Prop
  | BTree.priv w => w < n ∧ readsOf C w = 1
  | BTree.mark _ => True
  | BTree.node j l r =>
      j < C.size ∧ isBinOp (gateAt C j).op ∧
      (gateAt C j).inputs = [l.root n, r.root n] ∧
      GoodTree n C l ∧ GoodTree n C r ∧
      (l.nonMark → readsOf C (l.root n) = 1) ∧
      (r.nonMark → readsOf C (r.root n) = 1)

lemma BTree.wires_node (n j : ℕ) (l r : BTree) :
    (BTree.node j l r).wires n = insert (n + j) (l.wires n ∪ r.wires n) := by
  ext w
  simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_insert, Finset.image_union,
    Finset.mem_union, Finset.mem_insert]
  tauto

lemma BTree.root_mem_wires (n : ℕ) {t : BTree} (ht : t.nonMark) : t.root n ∈ t.wires n := by
  cases t with
  | priv w => simp [BTree.wires, BTree.privs, BTree.root]
  | mark w => exact False.elim ht
  | node j l r =>
    rw [BTree.wires_node, BTree.root]
    exact Finset.mem_insert_self _ _

lemma BTree.nonMark_of_marks_zero {t : BTree} (h : t.marks = 0) : t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.marks] at h
  | node _ _ _ => trivial

lemma BTree.nonMark_of_wires_nonempty (n : ℕ) {t : BTree} {w : ℕ} (hw : w ∈ t.wires n) :
    t.nonMark := by
  cases t with
  | priv _ => trivial
  | mark _ => simp [BTree.wires, BTree.privs, BTree.gates] at hw
  | node _ _ _ => trivial

lemma good_gates_sub {n : ℕ} {C : Circuit} {t : BTree} (ht : GoodTree n C t) :
    t.gates ⊆ gatesOf C := by
  induction t with
  | priv _ => simp [BTree.gates]
  | mark _ => simp [BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, _, hgl, hgr, _, _⟩
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · exact Finset.mem_range.2 hj
    · exact ihl hgl hkl
    · exact ihr hgr hkr

lemma good_wires_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ w ∈ t.wires n, w ≤ t.root n := by
  induction t with
  | priv w =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu ⊢
    omega
  | mark _ =>
    intro u hu
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
    have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
    have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
    intro w hw
    rw [BTree.wires_node] at hw
    rw [BTree.root]
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihl hgl w hwl) hl_lt)
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ihr hgr w hwr) hr_lt)

lemma good_gates_le {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : ∀ k ∈ t.gates, n + k ≤ t.root n := by
  intro k hk
  refine good_wires_le hback ht (n + k) ?_
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk, rfl⟩)

lemma good_readsIn_top_zero {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) : readsIn C t.gates (t.root n) = 0 :=
  readsIn_ge_bound_zero n C hback (good_gates_sub ht) (good_gates_le hback ht)

lemma good_node_not_mem_sub {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {j : ℕ} {l r : BTree}
    (ht : GoodTree n C (BTree.node j l r)) : j ∉ l.gates ∧ j ∉ r.gates := by
  rcases ht with ⟨hj, _, hinp, hgl, hgr, _, _⟩
  have hl_lt : l.root n < n + j := hback j hj (l.root n) (by rw [hinp]; simp)
  have hr_lt : r.root n < n + j := hback j hj (r.root n) (by rw [hinp]; simp)
  constructor
  · intro hjl
    have := good_gates_le hback hgl j hjl
    omega
  · intro hjr
    have := good_gates_le hback hgr j hjr
    omega

lemma good_internal_reads {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree} (ht : GoodTree n C t) :
    (∀ w ∈ t.wires n, w ≠ t.root n → readsIn C t.gates w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) ∧
    (∀ j l r, t = BTree.node j l r → Disjoint (l.wires n) (r.wires n)) := by
  induction t with
  | priv w =>
    refine ⟨fun u hu hne => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates, BTree.root] at hu hne
    exact absurd hu hne
  | mark _ =>
    refine ⟨fun u hu => ?_, fun _ _ _ h => by cases h⟩
    simp [BTree.wires, BTree.privs, BTree.gates] at hu
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    obtain ⟨ihl_int, _⟩ := ihl hgl
    obtain ⟨ihr_int, _⟩ := ihr hgr
    have hnot : j ∉ l.gates ∧ j ∉ r.gates :=
      good_node_not_mem_sub hback ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
    have hl_sub : l.gates ⊆ gatesOf C := good_gates_sub hgl
    have hr_sub : r.gates ⊆ gatesOf C := good_gates_sub hgr
    have hdisj_wires : Disjoint (l.wires n) (r.wires n) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      by_contra hne
      have hnon : (l.wires n ∩ r.wires n).Nonempty := Finset.nonempty_iff_ne_empty.2 hne
      let w := (l.wires n ∩ r.wires n).max' hnon
      have hw_mem : w ∈ l.wires n ∩ r.wires n := Finset.max'_mem _ hnon
      have hwl : w ∈ l.wires n := (Finset.mem_inter.1 hw_mem).1
      have hwr : w ∈ r.wires n := (Finset.mem_inter.1 hw_mem).2
      have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      by_cases h1 : w = l.root n
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hcnt : (gateAt C j).inputs.count w = 2 := by
            rw [hinp, ← h1, ← h2]
            exact count_pair_eq_two
          have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) hjG
          change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count w = 1 at hrw
          omega
        · have hrw : readsOf C w = 1 := h1 ▸ hl1 hlnm
          have hrr : readsIn C r.gates w = 1 := (ihr_int w hwr h2).1
          have hdisj_j : Disjoint r.gates {j} := by simp [hnot.2]
          have hsub_rj : r.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hr_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_rj w
          rw [readsIn_union C r.gates {j} w hdisj_j] at hle
          have hjr : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h1]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
      · by_cases h2 : w = r.root n
        · have hrw : readsOf C w = 1 := h2 ▸ hr1 hrnm
          have hrl : readsIn C l.gates w = 1 := (ihl_int w hwl h1).1
          have hdisj_j : Disjoint l.gates {j} := by simp [hnot.1]
          have hsub_lj : l.gates ∪ {j} ⊆ gatesOf C := Finset.union_subset hl_sub (by simp [hjG])
          have hle := readsIn_mono C hsub_lj w
          rw [readsIn_union C l.gates {j} w hdisj_j] at hle
          have hjl : 1 ≤ readsIn C {j} w := by
            refine readsIn_ge_of_mem C (Finset.mem_singleton_self j) ?_
            rw [hinp, ← h2]
            simp
          change readsIn C (gatesOf C) w = 1 at hrw
          omega
        · have hrl := ihl_int w hwl h1
          have hrr := ihr_int w hwr h2
          obtain ⟨p, hpG, hpw, _, hpuniq⟩ := readsIn_eq_one_unique C (gatesOf C) w hrl.2.1
          obtain ⟨pl, hpl, hplw⟩ := (readsIn_pos_iff C l.gates w).1 (by omega)
          obtain ⟨pr, hpr, hprw⟩ := (readsIn_pos_iff C r.gates w).1 (by omega)
          have hpl_eq : pl = p := hpuniq pl (hl_sub hpl) hplw
          have hpr_eq : pr = p := hpuniq pr (hr_sub hpr) hprw
          subst hpl_eq
          have hpr' : pl ∈ r.gates := by rwa [← hpr_eq]
          have hmem_inter : n + pl ∈ l.wires n ∩ r.wires n := Finset.mem_inter.2
            ⟨Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpl, rfl⟩),
             Finset.mem_union_right _ (Finset.mem_image.2 ⟨pl, hpr', rfl⟩)⟩
          have hle_max : n + pl ≤ w := Finset.le_max' _ _ hmem_inter
          have hlt := hback pl (Finset.mem_range.1 (hl_sub hpl)) w hplw
          omega
    have hdisj_gates : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_wires
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hj_not_u : j ∉ l.gates ∪ r.gates := by
      simp [hnot.1, hnot.2]
    refine ⟨?_, fun j' l' r' heq => by cases heq; exact hdisj_wires⟩
    intro w hw hne
    rw [BTree.wires_node] at hw
    rw [BTree.root] at hne
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwl | hwr
    · exact absurd rfl hne
    · have hlnm : l.nonMark := BTree.nonMark_of_wires_nonempty n hwl
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1l : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 2 := by
          rw [hinp, ← heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (l.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (l.root n) = 1 at hr1l
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = l.root n
      · subst hwr_eq
        have hrw : readsOf C (l.root n) = 1 := hl1 hlnm
        have hcnt : (gateAt C j).inputs.count (l.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_left hlr_ne
        have hrl0 : readsIn C l.gates (l.root n) = 0 := good_readsIn_top_zero hback hgl
        have hrr0 : readsIn C r.gates (l.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hr_sub hnot.2 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihl_int w hwl hwr_eq
        have hrr0 : readsIn C r.gates w = 0 :=
          readsIn_disjoint_zero C hl_sub hr_sub hdisj_gates hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hl_sub hjG hnot.1 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩
    · have hrnm : r.nonMark := BTree.nonMark_of_wires_nonempty n hwr
      have hlr_ne : l.root n ≠ r.root n := by
        intro heq
        have hr1r : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 2 := by
          rw [hinp, heq]
          exact count_pair_eq_two
        have hs := Finset.single_le_sum
          (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (r.root n))) hjG
        change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (r.root n) = 1 at hr1r
        omega
      rw [BTree.gates, readsIn_insert C _ j w hj_not_u, readsIn_union C l.gates r.gates w hdisj_gates]
      by_cases hwr_eq : w = r.root n
      · subst hwr_eq
        have hrw : readsOf C (r.root n) = 1 := hr1 hrnm
        have hcnt : (gateAt C j).inputs.count (r.root n) = 1 := by
          rw [hinp]
          exact count_pair_eq_one_right hlr_ne
        have hrr0 : readsIn C r.gates (r.root n) = 0 := good_readsIn_top_zero hback hgr
        have hrl0 : readsIn C l.gates (r.root n) = 0 :=
          readsIn_zero_of_count_one C hjG hl_sub hnot.1 hrw hcnt
        refine ⟨by omega, hrw, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := ihr_int w hwr hwr_eq
        have hrl0 : readsIn C l.gates w = 0 :=
          readsIn_disjoint_zero C hr_sub hl_sub hdisj_gates.symm hi.2.1 hi.1
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hr_sub hjG hnot.2 hi.2.1 hi.1
        refine ⟨by omega, hi.2.1, hi.2.2⟩

lemma good_markFree_inputs {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) :
    ∀ j ∈ t.gates, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ t.wires n := by
  induction t with
  | priv _ =>
    intro j hj
    simp [BTree.gates] at hj
  | mark _ =>
    simp [BTree.marks] at hm
  | node j l r ihl ihr =>
    rcases ht with ⟨_, hop, hinp, hgl, hgr, _, _⟩
    simp only [BTree.marks] at hm
    have hml : l.marks = 0 := by omega
    have hmr : r.marks = 0 := by omega
    intro k hk
    simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkl | hkr
    · refine ⟨hop, by rw [hinp]; rfl, fun w hw => ?_⟩
      rw [hinp] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rw [BTree.wires_node]
      rcases hw with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hml)))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmr)))
    · obtain ⟨ho, hl2, hwin⟩ := ihl hgl hml k hkl
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · obtain ⟨ho, hl2, hwin⟩ := ihr hgr hmr k hkr
      refine ⟨ho, hl2, fun w hw => ?_⟩
      rw [BTree.wires_node]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (hwin w hw))

def IsTree (n : ℕ) (C : Circuit) (S E : Finset ℕ) : Prop :=
  ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := readsIn C region
    region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
      (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

lemma good_markFree_isTree {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : t.marks = 0) : IsTree n C t.privs ∅ := by
  refine ⟨t.gates, t.root n, good_gates_sub ht,
    BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hm),
    good_readsIn_top_zero hback ht, fun _ hb => absurd hb (Finset.notMem_empty _), ?_,
    (good_internal_reads hback hout ht).1⟩
  intro j hj
  obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs ht hm j hj
  exact ⟨ho, hl, fun w hw => Or.inl (hwin w hw)⟩

def IsTopStretch (n : ℕ) (C : Circuit) (t : BTree) (reg priv : Finset ℕ) (b : ℕ) : Prop :=
  reg ⊆ t.gates ∧ priv ⊆ t.privs ∧ b ≤ t.root n ∧
  ((reg = ∅ ∧ priv = ∅ ∧ b = t.root n) ∨
   (let wires := priv ∪ reg.image (fun k => n + k)
    t.root n ∈ wires ∧ b ∉ wires ∧ b < t.root n ∧ readsIn C reg b = 1 ∧
    (∀ j ∈ reg, isBinOp (gateAt C j).op ∧ (gateAt C j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ t.root n → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w)))

lemma isTree_of_topStretch {n : ℕ} {C : Circuit} (hback : ReadsBack n C) {t : BTree}
    (ht : GoodTree n C t) {reg priv : Finset ℕ} {b : ℕ}
    (hs : IsTopStretch n C t reg priv b) (hnp : priv.Nonempty) : IsTree n C priv {b} := by
  rcases hs with ⟨hreg, _, _, ⟨_, hpe, _⟩ | ⟨hrm, hbn, hblt, hbr, hgj, hwint⟩⟩
  · rw [hpe] at hnp
    exact absurd hnp Finset.not_nonempty_empty
  · refine ⟨reg, t.root n, hreg.trans (good_gates_sub ht), hrm,
      readsIn_ge_bound_zero n C hback (hreg.trans (good_gates_sub ht))
        (fun k hk => good_gates_le hback ht k (hreg hk)),
      fun b' hb' => by
        rw [Finset.mem_singleton.1 hb']
        exact ⟨hbn, hblt, hbr⟩,
      fun j hj => by
        obtain ⟨ho, hl, hwin⟩ := hgj j hj
        exact ⟨ho, hl, fun w hw => (hwin w hw).imp id (fun h => Finset.mem_singleton.2 h)⟩,
      hwint⟩

lemma extend_stretch_aux {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {j : ℕ} {mf mk : BTree}
    (hj : j < C.size) (hop : isBinOp (gateAt C j).op)
    (hinp : (gateAt C j).inputs = [mf.root n, mk.root n] ∨
      (gateAt C j).inputs = [mk.root n, mf.root n])
    (hgf : GoodTree n C mf) (hgk : GoodTree n C mk)
    (hmf : mf.marks = 0)
    (hrf1 : readsOf C (mf.root n) = 1)
    (hrk1 : mk.nonMark → readsOf C (mk.root n) = 1)
    (hdisj_w : Disjoint (mf.wires n) (mk.wires n))
    (hdisj_g : Disjoint mf.gates mk.gates)
    (hj_mf : j ∉ mf.gates) (hj_mk : j ∉ mk.gates)
    {reg_k priv_k : Finset ℕ} {b : ℕ}
    (hsk : IsTopStretch n C mk reg_k priv_k b) :
    let reg := insert j (mf.gates ∪ reg_k)
    let priv := mf.privs ∪ priv_k
    let wires := priv ∪ reg.image (fun k => n + k)
    (n + j) ∈ wires ∧ b ∉ wires ∧ b < n + j ∧ readsIn C reg b = 1 ∧
    (∀ k ∈ reg, isBinOp (gateAt C k).op ∧ (gateAt C k).inputs.length = 2 ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ wires ∨ w = b) ∧
    (∀ w ∈ wires, w ≠ n + j → readsIn C reg w = 1 ∧ readsOf C w = 1 ∧ C.output ≠ w) := by
  intro reg priv wires
  have hjG : j ∈ gatesOf C := Finset.mem_range.2 hj
  have hmf_sub : mf.gates ⊆ gatesOf C := good_gates_sub hgf
  have hmk_sub : mk.gates ⊆ gatesOf C := good_gates_sub hgk
  have hmf_int := (good_internal_reads hback hout hgf).1
  have hmf_lt : mf.root n < n + j := hback j hj (mf.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmk_lt : mk.root n < n + j := hback j hj (mk.root n) (by rcases hinp with h | h <;> rw [h] <;> simp)
  have hmf_ne_mk : mf.root n ≠ mk.root n := by
    intro heq
    have hcnt : (gateAt C j).inputs.count (mf.root n) = 2 := by
      rcases hinp with h | h <;> rw [h, heq] <;> exact count_pair_eq_two
    have hs := Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count (mf.root n))) hjG
    change ∑ i ∈ gatesOf C, (gateAt C i).inputs.count (mf.root n) = 1 at hrf1
    omega
  have hcnt_mf : (gateAt C j).inputs.count (mf.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_left hmf_ne_mk
    · exact count_pair_eq_one_right hmf_ne_mk.symm
  have hcnt_mk : (gateAt C j).inputs.count (mk.root n) = 1 := by
    rcases hinp with h | h <;> rw [h]
    · exact count_pair_eq_one_right hmf_ne_mk
    · exact count_pair_eq_one_left hmf_ne_mk.symm
  rcases hsk with ⟨hreg_k, hpriv_k, hb_le, hcase⟩
  have hdisj_rk : Disjoint mf.gates reg_k := Disjoint.mono_right hreg_k hdisj_g
  have hj_not_u : j ∉ mf.gates ∪ reg_k := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hj_mf, fun h => hj_mk (hreg_k h)⟩
  have hwires_eq : wires = insert (n + j) (mf.wires n ∪ (priv_k ∪ reg_k.image (fun k => n + k))) := by
    ext w
    simp only [wires, priv, reg, BTree.wires, Finset.image_insert, Finset.image_union,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h1 | h2) | (h3 | h4 | h5))
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inl h3
      · exact Or.inr (Or.inl (Or.inr h4))
      · exact Or.inr (Or.inr (Or.inr h5))
    · rintro (h1 | (h2 | h3) | (h4 | h5))
      · exact Or.inr (Or.inl h1)
      · exact Or.inl (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inr (Or.inr h5))
  have hwk_sub : priv_k ∪ reg_k.image (fun k => n + k) ⊆ mk.wires n := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_image] at hw
    rcases hw with hp | ⟨k, hk, rfl⟩
    · exact Finset.mem_union_left _ (hpriv_k hp)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hreg_k hk, rfl⟩)
  have hmf_reads_sub : ∀ w ∈ mf.wires n, readsIn C reg_k w = 0 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · subst hwr
      exact readsIn_zero_of_count_one C hjG (hreg_k.trans hmk_sub) (fun h => hj_mk (hreg_k h)) hrf1 hcnt_mf
    · have hi := hmf_int w hw hwr
      exact readsIn_disjoint_zero C hmf_sub (hreg_k.trans hmk_sub) hdisj_rk hi.2.1 hi.1
  have hmf_all_reads1 : ∀ w ∈ mf.wires n, readsOf C w = 1 := by
    intro w hw
    by_cases hwr : w = mf.root n
    · exact hwr ▸ hrf1
    · exact (hmf_int w hw hwr).2.1
  have hb_not_mf : b ∉ mf.wires n := by
    intro hbm
    have hrb1 : readsOf C b = 1 := hmf_all_reads1 b hbm
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, _, hbr1, _, _⟩
    · subst hbeq
      have hne_root : mk.root n ≠ mf.root n := hmf_ne_mk.symm
      have hi := hmf_int (mk.root n) hbm hne_root
      have h0 := count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
      omega
    · have h0 := hmf_reads_sub b hbm
      omega
  have hmf_reads_b : readsIn C mf.gates b = 0 := by
    rw [readsIn_eq_zero_iff]
    intro k hk hbk
    have hwin := (good_markFree_inputs hgf hmf k hk).2.2 b hbk
    exact hb_not_mf hwin
  have hroot_mem : n + j ∈ wires := by
    rw [hwires_eq]
    exact Finset.mem_insert_self _ _
  have hb_lt : b < n + j := Nat.lt_of_le_of_lt hb_le hmk_lt
  have hb_not_w : b ∉ wires := by
    rw [hwires_eq]
    simp only [Finset.mem_insert, Finset.mem_union, not_or]
    refine ⟨by omega, hb_not_mf, ?_⟩
    rcases hcase with ⟨hre, hpe, _⟩ | ⟨_, hbn, _, _, _, _⟩
    · simp [hre, hpe]
    · simpa [Finset.mem_union, not_or] using hbn
  have hb_reads : readsIn C reg b = 1 := by
    rw [readsIn_insert C _ j b hj_not_u, readsIn_union C mf.gates reg_k b hdisj_rk, hmf_reads_b]
    rcases hcase with ⟨hre, _, hbeq⟩ | ⟨_, _, hblt_k, hbr1, _, _⟩
    · subst hbeq
      rw [hre, readsIn_empty, hcnt_mk]
    · have hcj0 : (gateAt C j).inputs.count b = 0 := by
        have hbn1 : b ≠ mf.root n := fun heq =>
          hb_not_mf (heq ▸ BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf))
        have hbn2 : b ≠ mk.root n := by omega
        rcases hinp with h | h <;> rw [h]
        · exact count_pair_eq_zero hbn1 hbn2
        · exact count_pair_eq_zero hbn2 hbn1
      rw [hcj0, hbr1]
  refine ⟨hroot_mem, hb_not_w, hb_lt, hb_reads, ?_, ?_⟩
  · intro k hk
    simp only [reg, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | hkm | hkk
    · refine ⟨hop, by rcases hinp with h | h <;> rw [h] <;> rfl, fun w hw => ?_⟩
      have hwf : w = mf.root n ∨ w = mk.root n := by
        rcases hinp with h | h <;> rw [h] at hw <;> simp at hw <;> tauto
      rcases hwf with rfl | rfl
      · left
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (BTree.root_mem_wires n (BTree.nonMark_of_marks_zero hmf)))
      · rcases hcase with ⟨_, _, hbeq⟩ | ⟨hrm, _, _, _, _, _⟩
        · exact Or.inr hbeq.symm
        · left
          rw [hwires_eq]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hrm)
    · obtain ⟨ho, hl, hwin⟩ := good_markFree_inputs hgf hmf k hkm
      refine ⟨ho, hl, fun w hw => Or.inl ?_⟩
      rw [hwires_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hwin w hw))
    · rcases hcase with ⟨hre, _, _⟩ | ⟨_, _, _, _, hgj, _⟩
      · rw [hre] at hkk
        exact absurd hkk (Finset.notMem_empty _)
      · obtain ⟨ho, hl, hwin⟩ := hgj k hkk
        refine ⟨ho, hl, fun w hw => (hwin w hw).imp (fun h => ?_) id⟩
        rw [hwires_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
  · intro w hw hne
    rw [hwires_eq] at hw
    simp only [Finset.mem_insert, Finset.mem_union] at hw
    rcases hw with rfl | hwm | hwk
    · exact absurd rfl hne
    · rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk,
        hmf_reads_sub w hwm]
      by_cases hwr : w = mf.root n
      · subst hwr
        rw [hcnt_mf, good_readsIn_top_zero hback hgf]
        exact ⟨by omega, hrf1, ne_output_of_reads_pos n C hback hout (by omega)⟩
      · have hi := hmf_int w hwm hwr
        have hcj0 : (gateAt C j).inputs.count w = 0 :=
          count_zero_of_readsIn_one C hmf_sub hjG hj_mf hi.2.1 hi.1
        rw [hcj0, hi.1]
        exact ⟨by omega, hi.2.1, hi.2.2⟩
    · rcases hcase with ⟨hre, hpe, _⟩ | ⟨hrm, _, _, _, _, hwint⟩
      · simp [hre, hpe] at hwk
      · have hw_in_mk : w ∈ mk.wires n := hwk_sub (Finset.mem_union.2 hwk)
        have hmknm : mk.nonMark := BTree.nonMark_of_wires_nonempty n hw_in_mk
        rw [readsIn_insert C _ j w hj_not_u, readsIn_union C mf.gates reg_k w hdisj_rk]
        by_cases hwr : w = mk.root n
        · subst hwr
          have hrk := hrk1 hmknm
          have hrl0 : readsIn C mf.gates (mk.root n) = 0 :=
            readsIn_zero_of_count_one C hjG hmf_sub hj_mf hrk hcnt_mk
          have hrr0 : readsIn C reg_k (mk.root n) = 0 :=
            readsIn_ge_bound_zero n C hback (hreg_k.trans hmk_sub)
              (fun k hk => good_gates_le hback hgk k (hreg_k hk))
          rw [hcnt_mk, hrl0, hrr0]
          exact ⟨by omega, hrk, ne_output_of_reads_pos n C hback hout (by omega)⟩
        · have hi := hwint w (Finset.mem_union.2 hwk) hwr
          have hrl0 : readsIn C mf.gates w = 0 :=
            readsIn_disjoint_zero C (hreg_k.trans hmk_sub) hmf_sub hdisj_rk.symm hi.2.1 hi.1
          have hcj0 : (gateAt C j).inputs.count w = 0 :=
            count_zero_of_readsIn_one C (hreg_k.trans hmk_sub) hjG (fun h => hj_mk (hreg_k h)) hi.2.1 hi.1
          rw [hcj0, hrl0, hi.1]
          exact ⟨by omega, hi.2.1, hi.2.2⟩

lemma decomp_marked {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) {t : BTree}
    (ht : GoodTree n C t) (hm : 1 ≤ t.marks) :
    ∃ (reg_top priv_top : Finset ℕ) (b_top : ℕ) (rest : List (Finset ℕ)),
      IsTopStretch n C t reg_top priv_top b_top ∧
      rest.length + 2 ≤ 2 * t.marks ∧
      (∀ S ∈ rest, S.Nonempty ∧ S ⊆ t.privs ∧ Disjoint S priv_top ∧ ∃ b, IsTree n C S {b}) ∧
      rest.Pairwise Disjoint ∧
      priv_top ∪ rest.toFinset.biUnion (fun S => S) = t.privs := by
  induction t with
  | priv _ =>
    simp [BTree.marks] at hm
  | mark w =>
    refine ⟨∅, ∅, w, [], ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _,
      Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [BTree.marks], fun _ h => by simp at h, List.Pairwise.nil,
      by simp [BTree.privs]⟩
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hgt_node : GoodTree n C (BTree.node j l r) := ⟨hj, hop, hinp, hgl, hgr, hl1, hr1⟩
    have hdisj_w : Disjoint (l.wires n) (r.wires n) :=
      (good_internal_reads hback hout hgt_node).2 j l r rfl
    have hdisj_g : Disjoint l.gates r.gates := by
      rw [Finset.disjoint_left]
      intro k hkl hkr
      exact Finset.disjoint_left.1 hdisj_w
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
        (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
    have hdisj_p : Disjoint l.privs r.privs :=
      Disjoint.mono (Finset.subset_union_left) (Finset.subset_union_left) hdisj_w
    have hnot := good_node_not_mem_sub hback hgt_node
    simp only [BTree.marks] at hm
    by_cases hml : l.marks = 0
    · have hmr : 1 ≤ r.marks := by omega
      obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr
      have hrf1 : readsOf C (l.root n) = 1 := hl1 (BTree.nonMark_of_marks_zero hml)
      have hext := extend_stretch_aux hback hout hj hop (Or.inl hinp) hgl hgr hml hrf1 hr1
        hdisj_w hdisj_g hnot.1 hnot.2 hsr
      refine ⟨insert j (l.gates ∪ reg_r), l.privs ∪ priv_r, b_r, rest_r, ?_, ?_, ?_, hpw_r, ?_⟩
      · refine ⟨Finset.insert_subset_insert j (Finset.union_subset_union_right hsr.1),
          Finset.union_subset_union_right hsr.2.1, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
      · simp only [BTree.marks]
        omega
      · intro S hS
        obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_r S hS
        refine ⟨hnp, hsub.trans Finset.subset_union_right, ?_, htr⟩
        rw [Finset.disjoint_union_right]
        exact ⟨Disjoint.mono_left hsub hdisj_p.symm, hdp⟩
      · simp only [BTree.privs]
        rw [Finset.union_assoc, hcov_r]
    · by_cases hmr : r.marks = 0
      · have hml1 : 1 ≤ l.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        have hrf1 : readsOf C (r.root n) = 1 := hr1 (BTree.nonMark_of_marks_zero hmr)
        have hext := extend_stretch_aux hback hout hj hop (Or.inr hinp) hgr hgl hmr hrf1 hl1
          hdisj_w.symm hdisj_g.symm hnot.2 hnot.1 hsl
        refine ⟨insert j (r.gates ∪ reg_l), r.privs ∪ priv_l, b_l, rest_l, ?_, ?_, ?_, hpw_l, ?_⟩
        · refine ⟨?_, ?_, Nat.le_of_lt hext.2.2.1, Or.inr hext⟩
          · intro k hk
            simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk ⊢
            rcases hk with rfl | h1 | h2
            · exact Or.inl rfl
            · exact Or.inr (Or.inr h1)
            · exact Or.inr (Or.inl (hsl.1 h2))
          · intro w hw
            simp only [BTree.privs, Finset.mem_union] at hw ⊢
            rcases hw with h1 | h2
            · exact Or.inr h1
            · exact Or.inl (hsl.2.1 h2)
        · simp only [BTree.marks]
          omega
        · intro S hS
          obtain ⟨hnp, hsub, hdp, htr⟩ := hrest_l S hS
          refine ⟨hnp, hsub.trans Finset.subset_union_left, ?_, htr⟩
          rw [Finset.disjoint_union_right]
          exact ⟨Disjoint.mono_left hsub hdisj_p, hdp⟩
        · simp only [BTree.privs]
          rw [Finset.union_assoc, hcov_l, Finset.union_comm]
      · have hml1 : 1 ≤ l.marks := by omega
        have hmr1 : 1 ≤ r.marks := by omega
        obtain ⟨reg_l, priv_l, b_l, rest_l, hsl, hlen_l, hrest_l, hpw_l, hcov_l⟩ := ihl hgl hml1
        obtain ⟨reg_r, priv_r, b_r, rest_r, hsr, hlen_r, hrest_r, hpw_r, hcov_r⟩ := ihr hgr hmr1
        let Ll : List (Finset ℕ) := if priv_l.Nonempty then priv_l :: rest_l else rest_l
        let Lr : List (Finset ℕ) := if priv_r.Nonempty then priv_r :: rest_r else rest_r
        have hLl_len : Ll.length ≤ rest_l.length + 1 := by
          dsimp only [Ll]
          split_ifs <;> simp
        have hLr_len : Lr.length ≤ rest_r.length + 1 := by
          dsimp only [Lr]
          split_ifs <;> simp
        have hLl_prop : ∀ S ∈ Ll, S.Nonempty ∧ S ⊆ l.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Ll] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsl.2.1, b_l, isTree_of_topStretch hback hgl hsl hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_l S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_l S hS
            exact ⟨a, b, c⟩
        have hLr_prop : ∀ S ∈ Lr, S.Nonempty ∧ S ⊆ r.privs ∧ ∃ b, IsTree n C S {b} := by
          intro S hS
          dsimp only [Lr] at hS
          split_ifs at hS with hnp
          · rcases List.mem_cons.1 hS with rfl | hSr
            · exact ⟨hnp, hsr.2.1, b_r, isTree_of_topStretch hback hgr hsr hnp⟩
            · obtain ⟨a, b, _, c⟩ := hrest_r S hSr
              exact ⟨a, b, c⟩
          · obtain ⟨a, b, _, c⟩ := hrest_r S hS
            exact ⟨a, b, c⟩
        have hLl_pw : Ll.Pairwise Disjoint := by
          dsimp only [Ll]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_l S hS).2.2.1.symm, hpw_l⟩
          · exact hpw_l
        have hLr_pw : Lr.Pairwise Disjoint := by
          dsimp only [Lr]
          split_ifs
          · exact List.pairwise_cons.2 ⟨fun S hS => (hrest_r S hS).2.2.1.symm, hpw_r⟩
          · exact hpw_r
        have hLl_cov : Ll.toFinset.biUnion (fun S => S) = l.privs := by
          dsimp only [Ll]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_l]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_l
            exact hcov_l
        have hLr_cov : Lr.toFinset.biUnion (fun S => S) = r.privs := by
          dsimp only [Lr]
          split_ifs with hnp
          · rw [List.toFinset_cons, Finset.biUnion_insert, hcov_r]
          · rw [Finset.not_nonempty_iff_eq_empty.1 hnp, Finset.empty_union] at hcov_r
            exact hcov_r
        refine ⟨∅, ∅, n + j, Ll ++ Lr,
          ⟨Finset.empty_subset _, Finset.empty_subset _, Nat.le_refl _, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, BTree.marks]
          omega
        · intro S hS
          rcases List.mem_append.1 hS with h1 | h2
          · obtain ⟨a, b, c⟩ := hLl_prop S h1
            exact ⟨a, b.trans Finset.subset_union_left, Finset.disjoint_empty_right S, c⟩
          · obtain ⟨a, b, c⟩ := hLr_prop S h2
            exact ⟨a, b.trans Finset.subset_union_right, Finset.disjoint_empty_right S, c⟩
        · rw [List.pairwise_append]
          refine ⟨hLl_pw, hLr_pw, fun S1 h1 S2 h2 => ?_⟩
          exact Disjoint.mono (hLl_prop S1 h1).2.1 (hLr_prop S2 h2).2.1 hdisj_p
        · rw [Finset.empty_union, List.toFinset_append, Finset.union_biUnion, hLl_cov, hLr_cov]
          rfl

def isInternalChild (n : ℕ) (C : Circuit) (u : ℕ) : Prop :=
  readsOf C u = 1 ∧ ¬ (n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not)

open Classical in
noncomputable def buildTree (n : ℕ) (C : Circuit) (r : ℕ) : BTree :=
  if h : n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not then
    let j := r - n
    let u0 := (gateAt C j).inputs.getD 0 0
    let u1 := (gateAt C j).inputs.getD 1 0
    let child : ℕ → BTree := fun u =>
      if hu : u < r ∧ isInternalChild n C u then
        if u < n then BTree.priv u else buildTree n C u
      else BTree.mark u
    BTree.node j (child u0) (child u1)
  else if r < n ∧ readsOf C r = 1 then
    BTree.priv r
  else
    BTree.mark r
termination_by r

lemma buildTree_root (n : ℕ) (C : Circuit) (r : ℕ) : (buildTree n C r).root n = r := by
  rw [buildTree]
  split_ifs with h1 h2
  · simp [BTree.root]
    omega
  · rfl
  · rfl

lemma buildTree_good (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C) : ∀ r : ℕ, GoodTree n C (buildTree n C r) := by
  classical
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    rw [buildTree]
    split_ifs with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨trivial, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      classical
      have hchild_prop : ∀ u : ℕ, u < r →
          let ch := if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u
          ch.root n = u ∧ GoodTree n C ch ∧ (ch.nonMark → readsOf C u = 1) := by
        intro u hult
        dsimp only
        split_ifs with hu hun
        · refine ⟨rfl, ⟨hun, hu.2.1⟩, fun _ => hu.2.1⟩
        · refine ⟨buildTree_root n C u, ih u hult, fun _ => hu.2.1⟩
        · refine ⟨rfl, trivial, fun h => False.elim h⟩
      have hc0 := hchild_prop _ hu0_lt
      have hc1 := hchild_prop _ hu1_lt
      refine ⟨hj, hbin.1, ?_, hc0.2.1, hc1.2.1, ?_, ?_⟩
      · rw [hc0.1, hc1.1]
        exact hinp
      · rw [hc0.1]
        exact hc0.2.2
      · rw [hc1.1]
        exact hc1.2.2
    · exact h2
    · trivial

open Classical in
noncomputable def parentGate (C : Circuit) (w : ℕ) : ℕ :=
  if h : ∃ j ∈ gatesOf C, w ∈ (gateAt C j).inputs then Classical.choose h else 0

lemma parentGate_spec (C : Circuit) {w : ℕ} (h : readsOf C w = 1) :
    parentGate C w ∈ gatesOf C ∧ w ∈ (gateAt C (parentGate C w)).inputs ∧
    ∀ j ∈ gatesOf C, w ∈ (gateAt C j).inputs → j = parentGate C w := by
  obtain ⟨j, hj, hw, _, huniq⟩ := readsIn_eq_one_unique C (gatesOf C) w h
  have hex : ∃ j' ∈ gatesOf C, w ∈ (gateAt C j').inputs := ⟨j, hj, hw⟩
  have hdef : parentGate C w = Classical.choose hex := by
    unfold parentGate
    exact dif_pos hex
  rw [hdef]
  have hch := Classical.choose_spec hex
  have heq : Classical.choose hex = j := huniq _ hch.1 hch.2
  rw [heq]
  exact ⟨hj, hw, huniq⟩

open Classical in
noncomputable def owner (n : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  if h : w < n + C.size ∧ readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not ∧
      w < n + parentGate C w then
    owner n C (n + parentGate C w)
  else w
termination_by n + C.size - w

open Classical in
lemma owner_step (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {w : ℕ}
    (hw1 : readsOf C w = 1) (hnot : (gateAt C (parentGate C w)).op ≠ GateOp.not) :
    owner n C w = owner n C (n + parentGate C w) := by
  obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hw1
  have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
  have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
  have hcond : w < n + C.size ∧ readsOf C w = 1 ∧
      (gateAt C (parentGate C w)).op ≠ GateOp.not ∧ w < n + parentGate C w :=
    ⟨by omega, hw1, hnot, hwlt⟩
  rw [owner]
  exact dif_pos hcond

lemma owner_fixed (n : ℕ) (C : Circuit) {w : ℕ}
    (h : ¬ (readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not)) :
    owner n C w = w := by
  rw [owner]
  split_ifs with h1
  · exact absurd ⟨h1.2.1, h1.2.2.1⟩ h
  · rfl

lemma owner_of_good_child (n : ℕ) (C : Circuit) (hback : ReadsBack n C) {j u : ℕ}
    (hj : j < C.size) (hop : (gateAt C j).op ≠ GateOp.not)
    (hu : u ∈ (gateAt C j).inputs) (hr1 : readsOf C u = 1) :
    owner n C u = owner n C (n + j) := by
  obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
  have hpeq : j = parentGate C u := huniq j (Finset.mem_range.2 hj) hu
  rw [owner_step n C hback hr1 (by rwa [← hpeq]), ← hpeq]

open Classical in
lemma owner_eq_of_mem_wires (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ), ∀ w ∈ (buildTree n C r).wires n, owner n C w = owner n C r := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro w hw
    rw [buildTree] at hw
    split_ifs at hw with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨trivial, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      have hchild : ∀ (u : ℕ), u ∈ (gateAt C (r - n)).inputs →
          w ∈ (if hu : u < r ∧ isInternalChild n C u then
            if u < n then BTree.priv u else buildTree n C u
          else BTree.mark u : BTree).wires n → owner n C w = owner n C r := by
        intro u hu hwu
        split_ifs at hwu with huc hun
        · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
            Finset.union_empty, Finset.mem_singleton] at hwu
          subst hwu
          rw [owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · rw [ih u huc.1 w hwu, owner_of_good_child n C hback hj h1.2.2 hu huc.2.1, hnj]
        · simp [BTree.wires, BTree.privs, BTree.gates] at hwu
      rw [BTree.wires_node] at hw
      simp only [Finset.mem_insert, Finset.mem_union] at hw
      rcases hw with rfl | hwl | hwr
      · rw [hnj]
      · exact hchild _ (by rw [hinp]; simp) hwl
      · exact hchild _ (by rw [hinp]; simp) hwr
    · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
        Finset.mem_singleton] at hw
      rw [hw]
    · simp [BTree.wires, BTree.privs, BTree.gates] at hw

open Classical in
lemma mem_wires_buildTree_owner (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (w : ℕ),
      ((w < n ∧ readsOf C w = 1) ∨
        (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not)) →
      w ∈ (buildTree n C (owner n C w)).wires n := by
  intro w
  induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
  | ind d ih =>
    intro hw
    by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
    · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
      have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
      have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
      have hown : owner n C w = owner n C (n + parentGate C w) :=
        owner_step n C hback hstep.1 hstep.2
      have hnp_in : n + parentGate C w ∈ (buildTree n C (owner n C (n + parentGate C w))).wires n :=
        ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      rw [hown]
      have hrec : ∀ (r : ℕ), n + parentGate C w ∈ (buildTree n C r).wires n →
          w ∈ (buildTree n C r).wires n := by
        intro r
        induction r using Nat.strong_induction_on with
        | ind r ihr =>
          intro hrw
          rw [buildTree] at hrw ⊢
          split_ifs at hrw ⊢ with h1 h2
          · have hj : r - n < C.size := h1.2.1
            have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
            have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
              rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
              · exact ⟨trivial, hl⟩
              · exact absurd hn h1.2.2
            have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
            have hnj : n + (r - n) = r := by omega
            rw [BTree.wires_node] at hrw ⊢
            simp only [Finset.mem_insert, Finset.mem_union] at hrw ⊢
            rcases hrw with hreq | hwl | hwr
            · have hpeq : r - n = parentGate C w := by omega
              have hwin_r : w ∈ (gateAt C (r - n)).inputs := by rwa [hpeq]
              rw [hinp] at hwin_r
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin_r
              have hint_w : isInternalChild n C w := by
                refine ⟨hstep.1, ?_⟩
                rintro ⟨hle, _, hnot⟩
                rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
                · omega
                · exact hne hnot
              have hw_in_child : ∀ u : ℕ, w = u →
                  w ∈ (if hu : u < r ∧ isInternalChild n C u then
                    if u < n then BTree.priv u else buildTree n C u
                  else BTree.mark u : BTree).wires n := by
                intro u hu
                subst hu
                have hcond : w < r ∧ isInternalChild n C w := ⟨by omega, hint_w⟩
                rw [dif_pos hcond]
                by_cases hwn : w < n
                · rw [if_pos hwn]
                  simp [BTree.wires, BTree.privs]
                · rw [if_neg hwn, buildTree]
                  have hwb : n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not := by
                    rcases hw with ⟨hlt, _⟩ | hgood
                    · omega
                    · exact hgood
                  rw [dif_pos hwb, BTree.wires_node]
                  have : n + (w - n) = w := by omega
                  rw [this]
                  exact Finset.mem_insert_self _ _
              rcases hwin_r with h0 | h1'
              · exact Or.inr (Or.inl (hw_in_child _ h0))
              · exact Or.inr (Or.inr (hw_in_child _ h1'))
            · refine Or.inr (Or.inl ?_)
              split_ifs at hwl ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwl
                omega
              · exact ihr _ huc.1 hwl
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwl
            · refine Or.inr (Or.inr ?_)
              split_ifs at hwr ⊢ with huc hun
              · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty,
                  Finset.union_empty, Finset.mem_singleton] at hwr
                omega
              · exact ihr _ huc.1 hwr
              · simp [BTree.wires, BTree.privs, BTree.gates] at hwr
          · simp only [BTree.wires, BTree.privs, BTree.gates, Finset.image_empty, Finset.union_empty,
              Finset.mem_singleton] at hrw
            omega
          · simp [BTree.wires, BTree.privs, BTree.gates] at hrw
      exact hrec _ hnp_in
    · rw [owner_fixed n C hstep, buildTree]
      rcases hw with ⟨hlt, hr1⟩ | hbin
      · have hnotb : ¬ (n ≤ w ∧ w - n < C.size ∧ (gateAt C (w - n)).op ≠ GateOp.not) := by omega
        rw [dif_neg hnotb, if_pos ⟨hlt, hr1⟩]
        simp [BTree.wires, BTree.privs, BTree.gates]
      · rw [dif_pos hbin, BTree.wires_node]
        have : n + (w - n) = w := by omega
        rw [this]
        exact Finset.mem_insert_self _ _

lemma mem_privs_iff_lt (n : ℕ) (C : Circuit) {t : BTree} (ht : GoodTree n C t) :
    ∀ w, w ∈ t.privs ↔ w ∈ t.wires n ∧ w < n := by
  induction t with
  | priv u =>
    intro w
    simp only [BTree.privs, BTree.wires, BTree.gates, Finset.image_empty, Finset.union_empty,
      Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, ht.1⟩
    · exact fun h => h.1
  | mark _ =>
    intro w
    simp [BTree.privs, BTree.wires, BTree.gates]
  | node j l r ihl ihr =>
    rcases ht with ⟨_, _, _, hgl, hgr, _, _⟩
    intro w
    rw [BTree.wires_node]
    simp only [BTree.privs, Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · have := (ihl hgl w).1 h
        exact ⟨Or.inr (Or.inl this.1), this.2⟩
      · have := (ihr hgr w).1 h
        exact ⟨Or.inr (Or.inr this.1), this.2⟩
    · rintro ⟨rfl | h | h, hlt⟩
      · omega
      · exact Or.inl ((ihl hgl w).2 ⟨h, hlt⟩)
      · exact Or.inr ((ihr hgr w).2 ⟨h, hlt⟩)

open Classical in
lemma buildTree_marks_eq_sum (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) :
    ∀ (r : ℕ),
      ((r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)) →
      (buildTree n C r).marks =
        ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr
    have hgt := buildTree_good n C hshape hback r
    have hdisj_from_good := (good_internal_reads hback hout hgt).2
    have hnot_from_good : ∀ j l r', buildTree n C r = BTree.node j l r' → j ∉ l.gates ∧ j ∉ r'.gates := by
      intro j l r' heq
      rw [heq] at hgt
      exact good_node_not_mem_sub hback hgt
    rw [buildTree] at hgt hdisj_from_good hnot_from_good ⊢
    split_ifs at hgt hdisj_from_good hnot_from_good ⊢ with h1 h2
    · have hj : r - n < C.size := h1.2.1
      have hgs := hshape (gateAt C (r - n)) (gateAt_mem_gates C hj)
      have hbin : isBinOp (gateAt C (r - n)).op ∧ (gateAt C (r - n)).inputs.length = 2 := by
        rcases hgs with ⟨ho, hl⟩ | ⟨hn, _⟩
        · exact ⟨trivial, hl⟩
        · exact absurd hn h1.2.2
      have hinp := list_len2_eq (gateAt C (r - n)).inputs hbin.2
      have hnj : n + (r - n) = r := by omega
      set ch : ℕ → BTree := fun u =>
        if hu : u < r ∧ isInternalChild n C u then
          if u < n then BTree.priv u else buildTree n C u
        else BTree.mark u
      have hnot := good_node_not_mem_sub hback hgt
      have hdisjw := hdisj_from_good (r - n) _ _ rfl
      have hdisjg : Disjoint (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates := by
        rw [Finset.disjoint_left]
        intro k hkl hkr
        exact Finset.disjoint_left.1 hdisjw
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkl, rfl⟩))
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hkr, rfl⟩))
      have hj_not_u : r - n ∉ (ch ((gateAt C (r - n)).inputs.getD 0 0)).gates ∪
          (ch ((gateAt C (r - n)).inputs.getD 1 0)).gates :=
        Finset.notMem_union.2 hnot
      simp only [BTree.marks, BTree.gates]
      rw [Finset.sum_insert hj_not_u, Finset.sum_union hdisjg]
      have hch_eq : ∀ u : ℕ, u < r →
          (ch u).marks =
            (if ¬ isInternalChild n C u then 1 else 0) +
            ∑ j ∈ (ch u).gates,
              @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
                (gateAt C j).inputs := by
        intro u hult
        dsimp only [ch]
        by_cases huc : u < r ∧ isInternalChild n C u
        · rw [dif_pos huc, if_neg (not_not.2 huc.2), zero_add]
          by_cases hun : u < n
          · rw [if_pos hun]
            simp [BTree.marks, BTree.gates]
          · rw [if_neg hun]
            have hvalid : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op ≠ GateOp.not :=
              ⟨by omega, by omega, fun hnot => huc.2.2 ⟨by omega, by omega, hnot⟩⟩
            exact ih u hult (Or.inr hvalid)
        · rw [dif_neg huc]
          have hni : ¬ isInternalChild n C u := fun hi => huc ⟨hult, hi⟩
          rw [if_pos hni]
          simp [BTree.marks, BTree.gates]
      have hu0_lt : (gateAt C (r - n)).inputs.getD 0 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 0 0) (by rw [hinp]; simp)
        omega
      have hu1_lt : (gateAt C (r - n)).inputs.getD 1 0 < r := by
        have hlt := hback (r - n) hj ((gateAt C (r - n)).inputs.getD 1 0) (by rw [hinp]; simp)
        omega
      rw [hch_eq _ hu0_lt, hch_eq _ hu1_lt]
      have hcnt_pair :
          @List.countP ℕ (fun v => @decide (¬ isInternalChild n C v) (Classical.propDecidable _))
            (gateAt C (r - n)).inputs =
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 0 0) then 1 else 0) +
          (if ¬ isInternalChild n C ((gateAt C (r - n)).inputs.getD 1 0) then 1 else 0) := by
        conv_lhs => rw [hinp]
        simp only [List.countP_cons, List.countP_nil]
        have hdec : ∀ (P : Prop),
            (if (@decide P (Classical.propDecidable P)) = true then 1 else 0) =
            if P then 1 else 0 := by
          intro P
          by_cases hP : P
          · rw [@decide_eq_true P (Classical.propDecidable P) hP, if_pos rfl, if_pos hP]
          · rw [@decide_eq_false P (Classical.propDecidable P) hP, if_neg Bool.false_ne_true, if_neg hP]
        rw [hdec, hdec, Nat.zero_add, Nat.add_comm]
        congr 1
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
        · exact congrArg (fun d => @ite ℕ _ d 1 0) (Subsingleton.elim _ _)
      rw [hcnt_pair]
      omega
    · simp [BTree.marks, BTree.gates]
    · rcases hr with h | h
      · exact absurd h h2
      · exact absurd h h1

lemma list_countP_le_sum_count (l : List ℕ) (S : Finset ℕ) :
    @List.countP ℕ (fun u => @decide (u ∈ S) (Classical.propDecidable _)) l =
      ∑ w ∈ S, l.count w := by
  induction l with
  | nil => simp
  | cons a ls ih =>
    simp only [List.countP_cons, List.count_cons, Finset.sum_add_distrib, ih]
    have h1 : (∑ w ∈ S, if a == w then 1 else 0) = if a ∈ S then 1 else 0 := by
      by_cases ha : a ∈ S
      · rw [if_pos ha, Finset.sum_eq_single a]
        · simp
        · intro w _ hwa
          simp [beq_eq_false_iff_ne.2 (Ne.symm hwa)]
        · intro h
          exact absurd ha h
      · rw [if_neg ha, Finset.sum_eq_zero]
        intro w hw
        have hne : a ≠ w := fun h => ha (h ▸ hw)
        simp [beq_eq_false_iff_ne.2 hne]
    rw [h1]
    by_cases ha : a ∈ S <;> simp [ha] <;> omega

lemma list_flatMap_collect {α : Type*} [DecidableEq α] (L : List α) (f : α → List (Finset ℕ))
    (g : α → Finset ℕ)
    (hnd : L.Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (g a) (g b))
    (hf_sub : ∀ a ∈ L, ∀ S ∈ f a, S ⊆ g a)
    (hf_pw : ∀ a ∈ L, (f a).Pairwise Disjoint)
    (hf_cov : ∀ a ∈ L, (f a).toFinset.biUnion (fun S => S) = g a) :
    (L.flatMap f).Pairwise Disjoint ∧
    (L.flatMap f).toFinset.biUnion (fun S => S) = L.toFinset.biUnion g ∧
    (L.flatMap f).length = ∑ a ∈ L.toFinset, (f a).length := by
  induction L with
  | nil => simp
  | cons a ls ih =>
    rw [List.nodup_cons] at hnd
    have hrec := ih hnd.2
      (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hf_sub x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_pw x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_cov x (List.mem_cons_of_mem a hx))
    have hfa_sub : ∀ S ∈ f a, S ⊆ g a := hf_sub a (List.mem_cons_self ..)
    have hfa_pw : (f a).Pairwise Disjoint := hf_pw a (List.mem_cons_self ..)
    have hfa_cov : (f a).toFinset.biUnion (fun S => S) = g a := hf_cov a (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨hfa_pw, hrec.1, fun S1 h1 S2 h2 => ?_⟩
      obtain ⟨b, hb, hS2⟩ := List.mem_flatMap.1 h2
      have hab : a ≠ b := fun h => hnd.1 (h ▸ hb)
      exact Disjoint.mono (hfa_sub S1 h1) (hf_sub b (List.mem_cons_of_mem a hb) S2 hS2)
        (hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb) hab)
    · simp only [List.flatMap_cons, List.toFinset_append, Finset.union_biUnion, hfa_cov, hrec.2.1,
        List.toFinset_cons, Finset.biUnion_insert]
    · simp only [List.flatMap_cons, List.length_append, hrec.2.2, List.toFinset_cons]
      rw [Finset.sum_insert (mt List.mem_toFinset.1 hnd.1)]

lemma forest_extract (n : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hback : ReadsBack n C)
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size → 0 < readsIn C (Finset.range C.size) (n + j)) :
    let gates := Finset.range C.size
    let gate := gateAt C
    let reads := readsIn C gates
    let neg := @Finset.filter ℕ (fun k => (gate k).op = GateOp.not)
      (fun k => Classical.propDecidable ((gate k).op = GateOp.not)) gates
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := gates.filter (fun k => 2 ≤ reads (n + k))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ (R : Finset ℕ) (tree : ℕ → BTree),
      R.card ≤ sharedGates.card + neg.card + 1 ∧
      (∀ r ∈ R, GoodTree n C (tree r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (tree r).privs (tree s).privs) ∧
      R.biUnion (fun r => (tree r).privs) = once ∧
      (∑ r ∈ R, (tree r).marks) ≤ markedReads + neg.card := by
  classical
  intro gates gate reads neg shared sharedGates markedReads once
  let validRoot : ℕ → Prop := fun r =>
    (r < n ∧ readsOf C r = 1) ∨ (n ≤ r ∧ r - n < C.size ∧ (gateAt C (r - n)).op ≠ GateOp.not)
  let Rout : Finset ℕ := if (gateAt C (C.size - 1)).op ≠ GateOp.not then {C.output} else ∅
  let Rsh : Finset ℕ :=
    (sharedGates.filter (fun k => (gateAt C k).op ≠ GateOp.not)).image (fun k => n + k)
  let Rneg : Finset ℕ :=
    (neg.filter (fun j => isInternalChild n C ((gateAt C j).inputs.getD 0 0))).image
      (fun j => (gateAt C j).inputs.getD 0 0)
  let Roots : Finset ℕ := Rout ∪ Rsh ∪ Rneg
  have hRout_card : Rout.card ≤ 1 := by
    dsimp only [Rout]
    split_ifs <;> simp
  have hRsh_card : Rsh.card ≤ sharedGates.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRneg_card : Rneg.card ≤ neg.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  have hRoots_le3 : Roots.card ≤ Rout.card + Rsh.card + Rneg.card :=
    (Finset.card_union_le (Rout ∪ Rsh) Rneg).trans
      (Nat.add_le_add_right (Finset.card_union_le Rout Rsh) _)
  have hRoots_card : Roots.card ≤ sharedGates.card + neg.card + 1 := by
    omega
  have hRoots_valid : ∀ r ∈ Roots, validRoot r := by
    intro r hr
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        exact Or.inr ⟨by omega, by omega, by rwa [show C.output - n = C.size - 1 by omega]⟩
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates, gates, Finset.mem_range] at hk
      exact Or.inr ⟨by omega, by omega, by simpa using hk.2⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      have hlt : (gateAt C j).inputs.getD 0 0 < n + j := hback j hj.1.1 _ hmem0
      by_cases hlt_n : (gateAt C j).inputs.getD 0 0 < n
      · exact Or.inl ⟨hlt_n, hj.2.1⟩
      · exact Or.inr ⟨by omega, by omega, fun hnot => hj.2.2 ⟨by omega, by omega, hnot⟩⟩
  have hRoots_fixed : ∀ r ∈ Roots, owner n C r = r := by
    intro r hr
    refine owner_fixed n C ?_
    rintro ⟨hr1, hnot⟩
    simp only [Roots, Finset.mem_union] at hr
    rcases hr with (h1 | h2) | h3
    · dsimp only [Rout] at h1
      split_ifs at h1 with hop
      · rw [Finset.mem_singleton] at h1
        subst h1
        have hz := reads_output_zero n C hback hout
        omega
      · exact absurd h1 (Finset.notMem_empty _)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h2
      simp only [Finset.mem_filter, sharedGates] at hk
      have h2r : 2 ≤ readsOf C (n + k) := hk.1.2
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h3
      simp only [Finset.mem_filter, neg, gates, Finset.mem_range] at hj
      have hgs := hshape (gateAt C j) (gateAt_mem_gates C hj.1.1)
      have hlen1 : (gateAt C j).inputs.length = 1 := by
        rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
        · rcases ho with ho | ho <;> rw [hj.1.2] at ho <;> cases ho
        · exact hl
      have hmem0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by
        rw [list_len1_eq _ hlen1]
        simp
      obtain ⟨_, _, huniq⟩ := parentGate_spec C hr1
      have hpeq : j = parentGate C ((gateAt C j).inputs.getD 0 0) :=
        huniq j (Finset.mem_range.2 hj.1.1) hmem0
      rw [← hpeq] at hnot
      exact hnot hj.1.2
  have howner_mem : ∀ w : ℕ, validRoot w → owner n C w ∈ Roots := by
    intro w
    induction hrem : n + C.size - w using Nat.strong_induction_on generalizing w with
    | ind d ih =>
      intro hw
      by_cases hstep : readsOf C w = 1 ∧ (gateAt C (parentGate C w)).op ≠ GateOp.not
      · obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hstep.1
        have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
        have hwlt : w < n + parentGate C w := hback (parentGate C w) hplt w hpw
        rw [owner_step n C hback hstep.1 hstep.2]
        exact ih (n + C.size - (n + parentGate C w)) (by omega) (n + parentGate C w) rfl
          (Or.inr ⟨by omega, by omega, by simpa using hstep.2⟩)
      · rw [owner_fixed n C hstep]
        by_cases hr1 : readsOf C w = 1
        · have hpnot : (gateAt C (parentGate C w)).op = GateOp.not := by
            by_contra hne
            exact hstep ⟨hr1, hne⟩
          obtain ⟨hpG, hpw, _⟩ := parentGate_spec C hr1
          have hplt : parentGate C w < C.size := Finset.mem_range.1 hpG
          have hgs := hshape (gateAt C (parentGate C w)) (gateAt_mem_gates C hplt)
          have hlen1 : (gateAt C (parentGate C w)).inputs.length = 1 := by
            rcases hgs with ⟨ho, _⟩ | ⟨_, hl⟩
            · rcases ho with ho | ho <;> rw [hpnot] at ho <;> cases ho
            · exact hl
          have hweq : (gateAt C (parentGate C w)).inputs.getD 0 0 = w := by
            rw [list_len1_eq _ hlen1] at hpw
            simp only [List.mem_singleton] at hpw
            exact hpw.symm
          have hint : isInternalChild n C w := by
            refine ⟨hr1, ?_⟩
            rintro ⟨hle, _, hnot⟩
            rcases hw with ⟨hlt, _⟩ | ⟨_, _, hne⟩
            · omega
            · exact hne hnot
          refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨parentGate C w, ?_, hweq⟩)
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_filter.2 ⟨hpG, hpnot⟩, by rwa [hweq]⟩
        · rcases hw with ⟨_, hr1'⟩ | ⟨hle, hlt, hne⟩
          · exact absurd hr1' hr1
          · by_cases hlast : w - n = C.size - 1
            · have hwout : w = C.output := by omega
              subst hwout
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              dsimp only [Rout]
              have hop : (gateAt C (C.size - 1)).op ≠ GateOp.not := by
                rwa [← hlast]
              simp [hop]
            · have hpos := hused (w - n) hlt (by omega)
              have hge2 : 2 ≤ readsOf C (n + (w - n)) := by
                have heq : n + (w - n) = w := by omega
                rw [heq] at hpos ⊢
                change 0 < readsOf C w at hpos
                omega
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              refine Finset.mem_image.2 ⟨w - n, ?_, by omega⟩
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hlt, hge2⟩, hne⟩
  have hpriv_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).privs (buildTree n C r2).privs := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 w (Finset.mem_union_left _ hw1)
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 w (Finset.mem_union_left _ hw2)
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hgates_disj : ∀ r1 ∈ Roots, ∀ r2 ∈ Roots, r1 ≠ r2 →
      Disjoint (buildTree n C r1).gates (buildTree n C r2).gates := by
    intro r1 hr1 r2 hr2 hne
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := owner_eq_of_mem_wires n C hback hshape r1 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk1, rfl⟩))
    have h2 := owner_eq_of_mem_wires n C hback hshape r2 (n + k)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨k, hk2, rfl⟩))
    rw [hRoots_fixed r1 hr1] at h1
    rw [hRoots_fixed r2 hr2] at h2
    exact hne (h1.symm.trans h2)
  have hpriv_cov : Roots.biUnion (fun r => (buildTree n C r).privs) = once := by
    ext w
    simp only [Finset.mem_biUnion, once, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨r, hr, hwp⟩
      have hgt := buildTree_good n C hshape hback r
      have hlt := ((mem_privs_iff_lt n C hgt w).1 hwp).2
      have hwr : readsOf C w = 1 := by
        by_cases hweq : w = r
        · subst hweq
          rcases hRoots_valid w hr with ⟨_, hr1⟩ | ⟨hle, _, _⟩
          · exact hr1
          · omega
        · have hroot : (buildTree n C r).root n = r := buildTree_root n C r
          exact ((good_internal_reads hback hout hgt).1 w (Finset.mem_union_left _ hwp)
            (by rwa [hroot])).2.1
      exact ⟨hlt, hwr⟩
    · rintro ⟨hlt, hr1⟩
      have hmemR : owner n C w ∈ Roots := howner_mem w (Or.inl ⟨hlt, hr1⟩)
      refine ⟨owner n C w, hmemR, ?_⟩
      have hw := mem_wires_buildTree_owner n C hback hshape w (Or.inl ⟨hlt, hr1⟩)
      exact (mem_privs_iff_lt n C (buildTree_good n C hshape hback _) w).2 ⟨hw, hlt⟩
  have hsum_marks : ∑ r ∈ Roots, (buildTree n C r).marks ≤ markedReads + neg.card := by
    have h1 : ∑ r ∈ Roots, (buildTree n C r).marks =
        ∑ r ∈ Roots, ∑ j ∈ (buildTree n C r).gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_congr rfl (fun r hr => buildTree_marks_eq_sum n C hback hout hshape r (hRoots_valid r hr))
    rw [h1, ← Finset.sum_biUnion (fun r1 hr1 r2 hr2 hne => hgates_disj r1 hr1 r2 hr2 hne)]
    have hsub_g : Roots.biUnion (fun r => (buildTree n C r).gates) ⊆ gates := by
      intro j hj
      obtain ⟨r, _, hjr⟩ := Finset.mem_biUnion.1 hj
      exact good_gates_sub (buildTree_good n C hshape hback r) hjr
    have hle1 :
        ∑ j ∈ Roots.biUnion (fun r => (buildTree n C r).gates),
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs :=
      Finset.sum_le_sum_of_subset hsub_g
    let negOnly : Finset ℕ := (neg.filter (fun k => readsOf C (n + k) = 1)).image (fun k => n + k)
    have hterm_le : ∀ j ∈ gates,
        @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
          (gateAt C j).inputs ≤
        @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
          (gateAt C j).inputs +
        @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
          (gateAt C j).inputs := by
      intro j hj
      have hjlt : j < C.size := Finset.mem_range.1 hj
      have hgen : ∀ (l : List ℕ), (∀ u ∈ l, u < n + j) →
          (∀ u ∈ l, 1 ≤ readsOf C u) →
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _)) l ≤
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _)) l +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _)) l := by
        intro l
        induction l with
        | nil => intros; simp
        | cons u ls ih =>
          intro hlt_l hpos_l
          simp only [List.countP_cons]
          have ih' := ih (fun v hv => hlt_l v (List.mem_cons_of_mem u hv))
            (fun v hv => hpos_l v (List.mem_cons_of_mem u hv))
          have hult : u < n + j := hlt_l u (List.mem_cons_self ..)
          have hupos : 1 ≤ readsOf C u := hpos_l u (List.mem_cons_self ..)
          by_cases hni : ¬ isInternalChild n C u
          · have hor : u ∈ shared ∨ u ∈ negOnly := by
              by_cases hr2 : 2 ≤ readsOf C u
              · left
                exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hr2⟩
              · right
                have hr1 : readsOf C u = 1 := by omega
                have hnotg : n ≤ u ∧ u - n < C.size ∧ (gateAt C (u - n)).op = GateOp.not := by
                  by_contra h
                  exact hni ⟨hr1, h⟩
                refine Finset.mem_image.2 ⟨u - n, ?_, by omega⟩
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hnotg.2.1, hnotg.2.2⟩, ?_⟩
                have : n + (u - n) = u := by omega
                rwa [this]
            have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = true :=
              @decide_eq_true _ (Classical.propDecidable _) hni
            rw [hd1, if_pos rfl]
            rcases hor with hsh | hno
            · have hd2 : (@decide (u ∈ shared) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hsh
              rw [hd2, if_pos rfl]
              split_ifs <;> omega
            · have hd3 : (@decide (u ∈ negOnly) (Classical.propDecidable _)) = true :=
                @decide_eq_true _ (Classical.propDecidable _) hno
              rw [hd3, if_pos rfl]
              split_ifs <;> omega
          · have hd1 : (@decide (¬ isInternalChild n C u) (Classical.propDecidable _)) = false :=
              @decide_eq_false _ (Classical.propDecidable _) hni
            rw [hd1]
            simp only [Bool.false_eq_true, ↓reduceIte]
            split_ifs <;> omega
      exact hgen (gateAt C j).inputs (fun u hu => hback j hjlt u hu)
        (fun u hu => readsIn_ge_of_mem C hj hu)
    have hle2 :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (¬ isInternalChild n C u) (Classical.propDecidable _))
            (gateAt C j).inputs ≤
        ∑ j ∈ gates,
          (@List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs +
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs) :=
      Finset.sum_le_sum hterm_le
    rw [Finset.sum_add_distrib] at hle2
    have hsum_sh :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ shared) (Classical.propDecidable _))
            (gateAt C j).inputs = markedReads := by
      simp_rw [list_countP_le_sum_count _ shared]
      rw [Finset.sum_comm]
      rfl
    have hsum_no :
        ∑ j ∈ gates,
          @List.countP ℕ (fun u => @decide (u ∈ negOnly) (Classical.propDecidable _))
            (gateAt C j).inputs ≤ neg.card := by
      simp_rw [list_countP_le_sum_count _ negOnly]
      rw [Finset.sum_comm]
      calc ∑ w ∈ negOnly, readsOf C w
          = ∑ _w ∈ negOnly, 1 := by
            refine Finset.sum_congr rfl (fun w hw => ?_)
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
            exact (Finset.mem_filter.1 hk).2
        _ = negOnly.card := by simp
        _ ≤ neg.card := (Finset.card_image_le).trans (Finset.card_filter_le _ _)
    omega
  exact ⟨Roots, buildTree n C, hRoots_card,
    fun r _ => buildTree_good n C hshape hback r, hpriv_disj, hpriv_cov, hsum_marks⟩

def binarySkeleton (C : PEqualNP.MetaComplexity.BinaryCircuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨GateOp.and, [g.left, g.right]⟩), C.output⟩

lemma binarySkeleton_size (C : PEqualNP.MetaComplexity.BinaryCircuit) :
    (binarySkeleton C).size = C.size := by
  simp [binarySkeleton, Circuit.size, PEqualNP.MetaComplexity.BinaryCircuit.size]

lemma binarySkeleton_shape (C : PEqualNP.MetaComplexity.BinaryCircuit) :
    ∀ g ∈ (binarySkeleton C).gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1) := by
  intro g hg
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp hg
  exact Or.inl ⟨Or.inl rfl, rfl⟩

lemma binarySkeleton_gate (C : PEqualNP.MetaComplexity.BinaryCircuit) (j : ℕ)
    (hj : j < C.gates.length) :
    gateAt (binarySkeleton C) j =
      ⟨GateOp.and, [(C.gates[j]).left, (C.gates[j]).right]⟩ := by
  simp [gateAt, binarySkeleton, List.getD_eq_getElem, hj]

lemma binarySkeleton_back (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (hback : ∀ (j : ℕ) (hj : j < C.gates.length),
      (C.gates[j]).left < n + j ∧ (C.gates[j]).right < n + j) :
    ReadsBack n (binarySkeleton C) := by
  intro j hj w hw
  have hj' : j < C.gates.length := by simpa [binarySkeleton, Circuit.size] using hj
  rw [binarySkeleton_gate C j hj'] at hw
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl
  · exact (hback j hj').1
  · exact (hback j hj').2

lemma binarySkeleton_forest (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (hback : ReadsBack n (binarySkeleton C))
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size →
      0 < readsOf (binarySkeleton C) (n + j)) :
    let reads := readsOf (binarySkeleton C)
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := (Finset.range C.size).filter (fun j => 2 ≤ reads (n + j))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ (R : Finset ℕ) (tree : ℕ → BTree),
      R.card ≤ sharedGates.card + 1 ∧
      (∀ r ∈ R, GoodTree n (binarySkeleton C) (tree r)) ∧
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (tree r).privs (tree s).privs) ∧
      R.biUnion (fun r => (tree r).privs) = once ∧
      (∑ r ∈ R, (tree r).marks) ≤ markedReads := by
  classical
  have negEmpty : (Finset.range (binarySkeleton C).size).filter
      (fun k => (gateAt (binarySkeleton C) k).op = GateOp.not) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j hj
    have hj' : j < C.gates.length := by
      have hj'' := Finset.mem_range.mp hj
      simpa [binarySkeleton, Circuit.size] using hj''
    rw [binarySkeleton_gate C j hj']
    exact GateOp.noConfusion
  have result := forest_extract n (binarySkeleton C) (binarySkeleton_shape C) hback
    (by simpa only [binarySkeleton_size] using hsz)
    (by rw [binarySkeleton_size]; exact hout)
    (by simpa only [readsOf, binarySkeleton_size] using hused)
  dsimp only at result ⊢
  rw [negEmpty] at result
  simpa only [readsOf, binarySkeleton_size, Finset.card_empty, Nat.add_zero] using result

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

def BTree.privateMultiset : BTree → Multiset ℕ
  | .priv w => {w}
  | .mark _ => 0
  | .node _ l r => l.privateMultiset + r.privateMultiset

def BTree.cutDecompose (n : ℕ) : BTree → BTree × List BTree
  | .priv w => (.priv w, [])
  | .mark w => (.mark w, [])
  | .node j l r =>
    if l.marks = 0 then
      (.node j l (r.cutDecompose n).1, (r.cutDecompose n).2)
    else if r.marks = 0 then
      (.node j (l.cutDecompose n).1 r, (l.cutDecompose n).2)
    else
      (.mark (n + j), (l.cutDecompose n).1 :: (l.cutDecompose n).2 ++
        (r.cutDecompose n).1 :: (r.cutDecompose n).2)

def BTree.cutPieces (n : ℕ) (t : BTree) : List BTree :=
  (t.cutDecompose n).1 :: (t.cutDecompose n).2

lemma BTree.cutDecompose_root (n : ℕ) (t : BTree) :
    (t.cutDecompose n).1.root n = t.root n := by
  cases t with
  | priv w => rfl
  | mark w => rfl
  | node j l r =>
    simp only [cutDecompose]
    split_ifs <;> rfl

lemma BTree.cutDecompose_nonMark (n : ℕ) (t : BTree)
    (h : (t.cutDecompose n).1.nonMark) : t.nonMark := by
  cases t with
  | priv w => trivial
  | mark w => exact h
  | node j l r => trivial

lemma BTree.cutDecompose_pure (n : ℕ) (t : BTree) (h : t.marks = 0) :
    t.cutDecompose n = (t, []) := by
  induction t with
  | priv w => rfl
  | mark w => simp [marks] at h
  | node j l r ihl ihr =>
    have hl : l.marks = 0 := by simp only [marks] at h; omega
    have hr : r.marks = 0 := by simp only [marks] at h; omega
    simp [cutDecompose, hl, ihr hr]

lemma BTree.cutDecompose_top_marks (n : ℕ) (t : BTree) :
    (t.cutDecompose n).1.marks ≤ 1 := by
  induction t with
  | priv w => simp [cutDecompose, marks]
  | mark w => simp [cutDecompose, marks]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl, marks] using ihr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr, marks] using ihl
      · simp [cutDecompose, hl, hr, marks]

lemma BTree.cutDecompose_rest_marks (n : ℕ) (t : BTree) :
    ∀ p ∈ (t.cutDecompose n).2, p.marks ≤ 1 := by
  induction t with
  | priv w => simp [cutDecompose]
  | mark w => simp [cutDecompose]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl] using ihr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr] using ihl
      · intro p hp
        simp only [cutDecompose, if_neg hl, if_neg hr, List.mem_cons, List.mem_append] at hp
        rcases hp with (rfl | hp) | (rfl | hp)
        · exact cutDecompose_top_marks n l
        · exact ihl p hp
        · exact cutDecompose_top_marks n r
        · exact ihr p hp

lemma BTree.cutDecompose_length (n : ℕ) (t : BTree) (h : 0 < t.marks) :
    (t.cutDecompose n).2.length + 2 ≤ 2 * t.marks := by
  induction t with
  | priv w => simp [marks] at h
  | mark w => simp [cutDecompose, marks]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · have hr : 0 < r.marks := by simp only [marks] at h; omega
      simpa [cutDecompose, hl, marks] using ihr hr
    · by_cases hr : r.marks = 0
      · have hl' : 0 < l.marks := by omega
        simpa [cutDecompose, hl, hr, marks] using ihl hl'
      · have hl' := ihl (by omega : 0 < l.marks)
        have hr' := ihr (by omega : 0 < r.marks)
        simp only [cutDecompose, if_neg hl, if_neg hr, List.length_cons,
          List.length_append, marks]
        omega

lemma BTree.cutDecompose_leaves (n : ℕ) (t : BTree) :
    (t.cutDecompose n).1.privateMultiset +
      ((t.cutDecompose n).2.map privateMultiset).sum = t.privateMultiset := by
  induction t with
  | priv w => simp [cutDecompose, privateMultiset]
  | mark w => simp [cutDecompose, privateMultiset]
  | node j l r ihl ihr =>
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl, privateMultiset, add_assoc] using
        congrArg (fun z => l.privateMultiset + z) ihr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr, privateMultiset, add_assoc, add_left_comm, add_comm] using
          congrArg (fun z => z + r.privateMultiset) ihl
      · simp only [cutDecompose, if_neg hl, if_neg hr, privateMultiset, List.map_cons,
          List.map_append, List.sum_cons, List.sum_append, zero_add]
        rw [← add_assoc, ihl, add_assoc, ihr]

lemma BTree.mem_privateMultiset (t : BTree) (w : ℕ) :
    w ∈ t.privateMultiset ↔ w ∈ t.privs := by
  induction t with
  | priv a => simp [privateMultiset, privs]
  | mark a => simp [privateMultiset, privs]
  | node j l r ihl ihr => simp [privateMultiset, privs, ihl, ihr]

lemma BTree.cutDecompose_top_good {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) : GoodTree n C (t.cutDecompose n).1 := by
  induction t with
  | priv w => exact ht
  | mark w => trivial
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hrl, hrr⟩
    by_cases hl : l.marks = 0
    · simp only [cutDecompose, if_pos hl]
      refine ⟨hj, hop, ?_, hgl, ihr hgr, hrl, ?_⟩
      · simpa only [cutDecompose_root] using hinp
      · intro h
        rw [cutDecompose_root]
        exact hrr (cutDecompose_nonMark n r h)
    · by_cases hr : r.marks = 0
      · simp only [cutDecompose, if_neg hl, if_pos hr]
        refine ⟨hj, hop, ?_, ihl hgl, hgr, ?_, hrr⟩
        · simpa only [cutDecompose_root] using hinp
        · intro h
          rw [cutDecompose_root]
          exact hrl (cutDecompose_nonMark n l h)
      · simp [cutDecompose, hl, hr, GoodTree]

lemma BTree.cutDecompose_rest_good {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) : ∀ p ∈ (t.cutDecompose n).2, GoodTree n C p := by
  induction t with
  | priv w => simp [cutDecompose]
  | mark w => simp [cutDecompose]
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hrl, hrr⟩
    by_cases hl : l.marks = 0
    · simpa [cutDecompose, hl] using ihr hgr
    · by_cases hr : r.marks = 0
      · simpa [cutDecompose, hl, hr] using ihl hgl
      · intro p hp
        simp only [cutDecompose, if_neg hl, if_neg hr, List.mem_cons, List.mem_append] at hp
        rcases hp with (rfl | hp) | (rfl | hp)
        · exact cutDecompose_top_good hgl
        · exact ihl hgl p hp
        · exact cutDecompose_top_good hgr
        · exact ihr hgr p hp

lemma BTree.privateMultiset_nodup {n : ℕ} {C : Circuit}
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) : t.privateMultiset.Nodup := by
  induction t with
  | priv w => simp [privateMultiset]
  | mark w => simp [privateMultiset]
  | node j l r ihl ihr =>
    have hd := (good_internal_reads hback hout ht).2 j l r rfl
    have hgl := ht.2.2.2.1
    have hgr := ht.2.2.2.2.1
    rw [privateMultiset, Multiset.nodup_add]
    refine ⟨ihl hgl, ihr hgr, ?_⟩
    rw [Multiset.disjoint_left]
    intro w hw1 hw2
    exact Finset.disjoint_left.1 hd
      (Finset.mem_union_left _ ((mem_privateMultiset l w).1 hw1))
      (Finset.mem_union_left _ ((mem_privateMultiset r w).1 hw2))

lemma btree_multiset_sum_nodup_pairwise (L : List (Multiset ℕ)) (h : L.sum.Nodup) :
    L.Pairwise Disjoint := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons s L ih =>
    rw [List.sum_cons, Multiset.nodup_add] at h
    refine List.pairwise_cons.2 ⟨?_, ih h.2.1⟩
    intro r hr
    exact Disjoint.mono_right (List.le_sum_of_mem hr) h.2.2

lemma BTree.cutPieces_leaves (n : ℕ) (t : BTree) :
    ((t.cutPieces n).map privateMultiset).sum = t.privateMultiset := by
  simpa [cutPieces] using cutDecompose_leaves n t

lemma BTree.cutPieces_good {n : ℕ} {C : Circuit} {t : BTree}
    (ht : GoodTree n C t) :
    ∀ p ∈ t.cutPieces n, GoodTree n C p ∧ p.marks ≤ 1 := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact ⟨cutDecompose_top_good ht, cutDecompose_top_marks n t⟩
  · exact ⟨cutDecompose_rest_good ht p hp, cutDecompose_rest_marks n t p hp⟩

lemma BTree.cutPieces_length_pos (n : ℕ) (t : BTree) (h : 0 < t.marks) :
    (t.cutPieces n).length + 1 ≤ 2 * t.marks := by
  simpa [cutPieces, Nat.add_assoc] using cutDecompose_length n t h

lemma BTree.cutPieces_length_zero (n : ℕ) (t : BTree) (h : t.marks = 0) :
    (t.cutPieces n).length = 1 := by
  simp [cutPieces, cutDecompose_pure n t h]

lemma BTree.cutPieces_length (n : ℕ) (t : BTree) :
    (t.cutPieces n).length ≤ 2 * t.marks + 1 := by
  by_cases h : t.marks = 0
  · simp [cutPieces_length_zero n t h, h]
  · have := cutPieces_length_pos n t (by omega)
    omega

lemma BTree.cutPieces_disjoint {n : ℕ} {C : Circuit}
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) :
    (t.cutPieces n).Pairwise (fun p q => Disjoint p.privs q.privs) := by
  have hs : (((t.cutPieces n).map privateMultiset).sum).Nodup := by
    rw [cutPieces_leaves]
    exact privateMultiset_nodup hback hout ht
  have hp := btree_multiset_sum_nodup_pairwise _ hs
  rw [List.pairwise_map] at hp
  refine hp.imp (fun {p q} hd => ?_)
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  exact Multiset.disjoint_left.1 hd
    ((mem_privateMultiset p w).2 hw1) ((mem_privateMultiset q w).2 hw2)

lemma btree_mem_multiset_list_sum (L : List (Multiset ℕ)) (w : ℕ) :
    w ∈ L.sum ↔ ∃ s ∈ L, w ∈ s := by
  induction L with
  | nil => simp
  | cons s L ih => simp [ih]

lemma BTree.cutPieces_cover (n : ℕ) (t : BTree) :
    (@List.toFinset BTree (Classical.decEq _) (t.cutPieces n)).biUnion BTree.privs = t.privs := by
  classical
  ext w
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  rw [← mem_privateMultiset t w, ← cutPieces_leaves n t,
    btree_mem_multiset_list_sum]
  constructor
  · rintro ⟨p, hp, hw⟩
    exact ⟨p.privateMultiset, List.mem_map.2 ⟨p, hp, rfl⟩,
      (mem_privateMultiset p w).2 hw⟩
  · rintro ⟨s, hs, hws⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    exact ⟨p, hp, (mem_privateMultiset p w).1 hws⟩

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

def paintBad (bad : Finset ℕ) : BTree → BTree
  | .priv w => if w ∈ bad then .mark w else .priv w
  | .mark w => .mark w
  | .node j l r => .node j (paintBad bad l) (paintBad bad r)

lemma paintBad_root (bad : Finset ℕ) (n : ℕ) (t : BTree) :
    (paintBad bad t).root n = t.root n := by
  cases t <;> simp only [paintBad, BTree.root]
  split_ifs <;> rfl

lemma paintBad_nonMark (bad : Finset ℕ) (t : BTree) :
    (paintBad bad t).nonMark → t.nonMark := by
  cases t <;> simp only [paintBad, BTree.nonMark]
  · intro _; trivial
  · exact False.elim
  · intro _; trivial

lemma paintBad_privs (bad : Finset ℕ) (t : BTree) :
    (paintBad bad t).privs = t.privs \ bad := by
  induction t with
  | priv w =>
    by_cases hw : w ∈ bad <;> ext x <;> simp [paintBad, BTree.privs, hw] <;> aesop
  | mark w => simp [paintBad, BTree.privs]
  | node j l r ihl ihr =>
    ext w
    simp only [paintBad, BTree.privs, ihl, ihr, Finset.mem_union, Finset.mem_sdiff]
    tauto

lemma paintBad_good {n : ℕ} {C : Circuit} (bad : Finset ℕ) {t : BTree}
    (ht : GoodTree n C t) : GoodTree n C (paintBad bad t) := by
  induction t with
  | priv w =>
    by_cases hw : w ∈ bad
    · simp [paintBad, hw, GoodTree]
    · simpa [paintBad, hw] using ht
  | mark w => trivial
  | node j l r ihl ihr =>
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl, hr⟩
    refine ⟨hj, hop, ?_, ihl hgl, ihr hgr, ?_, ?_⟩
    · simpa only [paintBad_root] using hinp
    · simpa only [paintBad_root] using fun h => hl (paintBad_nonMark bad l h)
    · simpa only [paintBad_root] using fun h => hr (paintBad_nonMark bad r h)

lemma paintBad_marks {n : ℕ} {C : Circuit} (bad : Finset ℕ)
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) :
    (paintBad bad t).marks = t.marks + (t.privs ∩ bad).card := by
  induction t with
  | priv w =>
    by_cases hw : w ∈ bad <;> simp [paintBad, BTree.marks, BTree.privs, hw]
  | mark w => simp [paintBad, BTree.marks, BTree.privs]
  | node j l r ihl ihr =>
    have disj := (good_internal_reads hback hout ht).2 j l r rfl
    have dp : Disjoint l.privs r.privs :=
      Disjoint.mono Finset.subset_union_left Finset.subset_union_left disj
    have di : Disjoint (l.privs ∩ bad) (r.privs ∩ bad) :=
      Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left dp
    rcases ht with ⟨hj, hop, hinp, hgl, hgr, hl, hr⟩
    simp only [paintBad, BTree.marks, BTree.privs, ihl hgl, ihr hgr,
      Finset.union_inter_distrib_right, Finset.card_union_of_disjoint di]
    omega

lemma concrete_tree_bad_partition {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) (bad : Finset ℕ) {t : BTree}
    (ht : GoodTree n C t) :
    ∃ L : List BTree,
      L.length ≤ 2 * (t.marks + (t.privs ∩ bad).card) + 1 ∧
      (∀ p ∈ L, GoodTree n C p ∧ p.marks ≤ 1 ∧ p.privs.Nonempty ∧
        p.privs ⊆ t.privs \ bad) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs = t.privs \ bad := by
  classical
  let u := paintBad bad t
  let L := (u.cutPieces n).filter (fun p => decide p.privs.Nonempty)
  have hu : GoodTree n C u := paintBad_good bad ht
  have hcov : (@List.toFinset BTree (Classical.decEq _) (u.cutPieces n)).biUnion BTree.privs =
      t.privs \ bad := by
    rw [BTree.cutPieces_cover, paintBad_privs]
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · have hlen := BTree.cutPieces_length n u
    have hfilter : L.length ≤ (u.cutPieces n).length := List.length_filter_le _ _
    have hm : u.marks = t.marks + (t.privs ∩ bad).card := paintBad_marks bad hback hout ht
    omega
  · intro p hp
    have hpf := List.mem_filter.1 hp
    have hg := BTree.cutPieces_good hu p hpf.1
    refine ⟨hg.1, hg.2, of_decide_eq_true hpf.2, ?_⟩
    intro w hw
    rw [← hcov]
    exact Finset.mem_biUnion.2 ⟨p, List.mem_toFinset.2 hpf.1, hw⟩
  · exact (BTree.cutPieces_disjoint hback hout hu).filter _
  · ext w
    simp only [Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · rintro ⟨p, hp, hw⟩
      rw [← hcov]
      exact Finset.mem_biUnion.2 ⟨p, List.mem_toFinset.2 (List.mem_filter.1 hp).1, hw⟩
    · intro hw
      rw [← hcov] at hw
      obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.1 hw
      refine ⟨p, List.mem_filter.2 ⟨List.mem_toFinset.1 hp, ?_⟩, hwp⟩
      exact decide_eq_true ⟨w, hwp⟩

lemma concrete_flatmap_collect {α : Type*} [DecidableEq α] (L : List α)
    (f : α → List BTree) (g : α → Finset ℕ)
    (hnd : L.Nodup)
    (hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (g a) (g b))
    (hf_sub : ∀ a ∈ L, ∀ p ∈ f a, p.privs ⊆ g a)
    (hf_pw : ∀ a ∈ L, (f a).Pairwise (fun p q => Disjoint p.privs q.privs))
    (hf_cov : ∀ a ∈ L,
      (@List.toFinset BTree (Classical.decEq _) (f a)).biUnion BTree.privs = g a) :
    (L.flatMap f).Pairwise (fun p q => Disjoint p.privs q.privs) ∧
    (@List.toFinset BTree (Classical.decEq _) (L.flatMap f)).biUnion BTree.privs =
      L.toFinset.biUnion g ∧
    (L.flatMap f).length = ∑ a ∈ L.toFinset, (f a).length := by
  classical
  induction L with
  | nil => simp
  | cons a ls ih =>
    rw [List.nodup_cons] at hnd
    have hrec := ih hnd.2
      (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)
      (fun x hx => hf_sub x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_pw x (List.mem_cons_of_mem a hx))
      (fun x hx => hf_cov x (List.mem_cons_of_mem a hx))
    have hfa_sub : ∀ p ∈ f a, p.privs ⊆ g a := hf_sub a (List.mem_cons_self ..)
    have hfa_pw := hf_pw a (List.mem_cons_self ..)
    have hfa_cov := hf_cov a (List.mem_cons_self ..)
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.pairwise_append]
      refine ⟨hfa_pw, hrec.1, fun p hp q hq => ?_⟩
      obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.1 hq
      have hab : a ≠ b := fun h => hnd.1 (h ▸ hb)
      exact Disjoint.mono (hfa_sub p hp) (hf_sub b (List.mem_cons_of_mem a hb) q hqb)
        (hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb) hab)
    · simp only [List.flatMap_cons, List.toFinset_append, Finset.union_biUnion, hfa_cov,
        hrec.2.1, List.toFinset_cons, Finset.biUnion_insert]
    · simp only [List.flatMap_cons, List.length_append, hrec.2.2, List.toFinset_cons]
      rw [Finset.sum_insert (mt List.mem_toFinset.1 hnd.1)]

lemma concrete_forest_inter_sum_le (R : Finset ℕ) (f : ℕ → Finset ℕ) (bad : Finset ℕ)
    (hd : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (f a) (f b)) :
    (∑ a ∈ R, (f a ∩ bad).card) ≤ bad.card := by
  have hdisj : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint (f a ∩ bad) (f b ∩ bad) := by
    intro a ha b hb hab
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left (hd a ha b hb hab)
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (by
    intro x hx
    obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxa).2)

lemma concrete_forest_bad_partition {n : ℕ} {C : Circuit} (hback : ReadsBack n C)
    (hout : C.output + 1 = n + C.size) (bad R : Finset ℕ) (trees : ℕ → BTree)
    (hgood : ∀ r ∈ R, GoodTree n C (trees r))
    (hdisj : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (trees r).privs (trees s).privs) :
    ∃ L : List BTree,
      L.length ≤ 2 * ((∑ r ∈ R, (trees r).marks) + bad.card) + R.card ∧
      (∀ p ∈ L, GoodTree n C p ∧ p.marks ≤ 1 ∧ p.privs.Nonempty) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs =
        (R.biUnion fun r => (trees r).privs) \ bad := by
  classical
  have hex (r : ℕ) : ∃ L : List BTree, r ∈ R →
      L.length ≤ 2 * ((trees r).marks + ((trees r).privs ∩ bad).card) + 1 ∧
      (∀ p ∈ L, GoodTree n C p ∧ p.marks ≤ 1 ∧ p.privs.Nonempty ∧
        p.privs ⊆ (trees r).privs \ bad) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      L.toFinset.biUnion BTree.privs = (trees r).privs \ bad := by
    by_cases hr : r ∈ R
    · obtain ⟨L, hL⟩ := concrete_tree_bad_partition hback hout bad (hgood r hr)
      exact ⟨L, fun _ => hL⟩
    · exact ⟨[], fun h => False.elim (hr h)⟩
  choose parts hparts using hex
  have hc := concrete_flatmap_collect R.toList parts (fun r => (trees r).privs \ bad)
    R.nodup_toList
    (fun a ha b hb hab => Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
      (hdisj a (Finset.mem_toList.mp ha) b (Finset.mem_toList.mp hb) hab))
    (fun a ha p hp => ((hparts a (Finset.mem_toList.mp ha)).2.1 p hp).2.2.2)
    (fun a ha => (hparts a (Finset.mem_toList.mp ha)).2.2.1)
    (fun a ha => (hparts a (Finset.mem_toList.mp ha)).2.2.2)
  refine ⟨R.toList.flatMap parts, ?_, ?_, hc.1, ?_⟩
  · rw [hc.2.2, Finset.toList_toFinset]
    have hsum := Finset.sum_le_sum (fun r hr => (hparts r hr).1)
    have hbad := concrete_forest_inter_sum_le R (fun r => (trees r).privs) bad hdisj
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      smul_eq_mul, mul_one] at hsum
    omega
  · intro p hp
    obtain ⟨r, hr, hpr⟩ := List.mem_flatMap.mp hp
    obtain ⟨hg, hm, hne, _⟩ := (hparts r (Finset.mem_toList.mp hr)).2.1 p hpr
    exact ⟨hg, hm, hne⟩
  · rw [hc.2.1, Finset.toList_toFinset]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_sdiff]
    aesop

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

def BTree.Subtree (t u : BTree) : Prop :=
  t = u ∨ match t with
    | .node _ l r => l.Subtree u ∨ r.Subtree u
    | _ => False

lemma BTree.Subtree.refl (t : BTree) : t.Subtree t := by
  cases t <;> exact Or.inl rfl

lemma BTree.Subtree.left (j : ℕ) (l r : BTree) :
    (BTree.node j l r).Subtree l := Or.inr (Or.inl (BTree.Subtree.refl l))

lemma BTree.Subtree.right (j : ℕ) (l r : BTree) :
    (BTree.node j l r).Subtree r := Or.inr (Or.inr (BTree.Subtree.refl r))

lemma BTree.Subtree.trans {t u v : BTree} (htu : t.Subtree u) (huv : u.Subtree v) :
    t.Subtree v := by
  induction t with
  | priv w =>
    rcases htu with h | h
    · simpa only [h] using huv
    · exact False.elim h
  | mark w =>
    rcases htu with h | h
    · simpa only [h] using huv
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases htu with h | h | h
    · simpa only [h] using huv
    · exact Or.inr (Or.inl (ihl h))
    · exact Or.inr (Or.inr (ihr h))

lemma BTree.Subtree.good {n : ℕ} {C : Circuit} {t u : BTree}
    (h : t.Subtree u) (ht : GoodTree n C t) : GoodTree n C u := by
  induction t with
  | priv w =>
    rcases h with h | h
    · simpa only [← h] using ht
    · exact False.elim h
  | mark w =>
    rcases h with h | h
    · simpa only [← h] using ht
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases h with h | h | h
    · simpa only [← h] using ht
    · exact ihl h ht.2.2.2.1
    · exact ihr h ht.2.2.2.2.1

lemma BTree.Subtree.marks_le {t u : BTree} (h : t.Subtree u) :
    u.marks ≤ t.marks := by
  induction t with
  | priv w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | mark w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases h with h | h | h
    · subst u; exact le_rfl
    · exact (ihl h).trans (Nat.le_add_right _ _)
    · exact (ihr h).trans (Nat.le_add_left _ _)

lemma BTree.Subtree.privs_subset {t u : BTree} (h : t.Subtree u) :
    u.privs ⊆ t.privs := by
  induction t with
  | priv w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | mark w =>
    rcases h with h | h
    · subst u; exact le_rfl
    · exact False.elim h
  | node j l r ihl ihr =>
    rcases h with h | h | h
    · subst u; exact le_rfl
    · exact (ihl h).trans Finset.subset_union_left
    · exact (ihr h).trans Finset.subset_union_right

def BTree.bankCount (P : ℕ → Prop) [DecidablePred P] (t : BTree) : ℕ :=
  (t.privs.filter P).card

lemma BTree.bankCount_node_le (P : ℕ → Prop) [DecidablePred P]
    (j : ℕ) (l r : BTree) :
    (BTree.node j l r).bankCount P ≤ l.bankCount P + r.bankCount P := by
  unfold bankCount
  rw [BTree.privs, Finset.filter_union]
  exact Finset.card_union_le _ _

lemma BTree.small_violating_subtree (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (t : BTree)
    (hlarge : 2 < t.bankCount P ∨ 2 < t.bankCount Q) :
    ∃ u : BTree, t.Subtree u ∧
      (2 < u.bankCount P ∨ 2 < u.bankCount Q) ∧
      u.bankCount P ≤ 4 ∧ u.bankCount Q ≤ 4 := by
  induction t with
  | priv w =>
    have hp : (BTree.priv w).bankCount P ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp [BTree.privs])
    have hq : (BTree.priv w).bankCount Q ≤ 1 := by
      exact (Finset.card_filter_le _ _).trans (by simp [BTree.privs])
    omega
  | mark w =>
    simp [BTree.bankCount, BTree.privs] at hlarge
  | node j l r ihl ihr =>
    by_cases hl : 2 < l.bankCount P ∨ 2 < l.bankCount Q
    · obtain ⟨u, hu, hlarge, hp, hq⟩ := ihl hl
      exact ⟨u, (BTree.Subtree.left j l r).trans hu, hlarge, hp, hq⟩
    by_cases hr : 2 < r.bankCount P ∨ 2 < r.bankCount Q
    · obtain ⟨u, hu, hlarge, hp, hq⟩ := ihr hr
      exact ⟨u, (BTree.Subtree.right j l r).trans hu, hlarge, hp, hq⟩
    refine ⟨BTree.node j l r, BTree.Subtree.refl _, hlarge, ?_, ?_⟩
    · have h := BTree.bankCount_node_le P j l r
      omega
    · have h := BTree.bankCount_node_le Q j l r
      omega

lemma BTree.good_small_violating_subtree {n : ℕ} {C : Circuit}
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (t : BTree) (ht : GoodTree n C t)
    (hmarks : t.marks ≤ 1)
    (hlarge : 2 < t.bankCount P ∨ 2 < t.bankCount Q) :
    ∃ u : BTree, GoodTree n C u ∧ u.marks ≤ 1 ∧ u.privs ⊆ t.privs ∧
      (2 < u.bankCount P ∨ 2 < u.bankCount Q) ∧
      u.bankCount P ≤ 4 ∧ u.bankCount Q ≤ 4 := by
  obtain ⟨u, hu, hlarge, hp, hq⟩ := small_violating_subtree P Q t hlarge
  exact ⟨u, hu.good ht, hu.marks_le.trans hmarks, hu.privs_subset, hlarge, hp, hq⟩

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

lemma one_mark_good_isTree {n : ℕ} {C : Circuit}
    (hback : ReadsBack n C) (hout : C.output + 1 = n + C.size)
    {t : BTree} (ht : GoodTree n C t) (hm : t.marks ≤ 1)
    (hnp : t.privs.Nonempty) :
    ∃ E : Finset ℕ, E.card ≤ 1 ∧ IsTree n C t.privs E := by
  by_cases hzero : t.marks = 0
  · exact ⟨∅, by simp, good_markFree_isTree hback hout ht hzero⟩
  obtain ⟨reg, priv, b, rest, hs, hlen, hrest, hpw, hcov⟩ :=
    decomp_marked hback hout ht (by omega)
  cases rest with
  | nil =>
    simp only [List.toFinset_nil, Finset.biUnion_empty, Finset.union_empty] at hcov
    subst priv
    exact ⟨{b}, by simp, isTree_of_topStretch hback ht hs hnp⟩
  | cons s rest =>
    simp only [List.length_cons] at hlen
    omega

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Finset

lemma binary_concrete_bad_partition (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (hback : ReadsBack n (binarySkeleton C))
    (hsz : 0 < C.size)
    (hout : C.output + 1 = n + C.size)
    (hused : ∀ j < C.size, j + 1 < C.size →
      0 < readsOf (binarySkeleton C) (n + j))
    (bad : Finset ℕ) :
    let reads := readsOf (binarySkeleton C)
    let shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    let sharedGates := (Finset.range C.size).filter (fun j => 2 ≤ reads (n + j))
    let markedReads := ∑ w ∈ shared, reads w
    let once := (Finset.range n).filter (fun w => reads w = 1)
    ∃ L : List BTree,
      L.length ≤ 2 * (markedReads + bad.card) + sharedGates.card + 1 ∧
      (∀ p ∈ L, GoodTree n (binarySkeleton C) p ∧ p.marks ≤ 1 ∧
        p.privs.Nonempty ∧ p.privs ⊆ once \ bad ∧
        ∃ E : Finset ℕ, E.card ≤ 1 ∧ IsTree n (binarySkeleton C) p.privs E) ∧
      L.Pairwise (fun p q => Disjoint p.privs q.privs) ∧
      (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs = once \ bad := by
  classical
  intro reads shared sharedGates markedReads once
  obtain ⟨R, trees, hR, hgood, hdisj, hcov, hmarks⟩ :=
    binarySkeleton_forest n C hback hsz hout hused
  have hout' : (binarySkeleton C).output + 1 = n + (binarySkeleton C).size := by
    rw [binarySkeleton_size]
    exact hout
  obtain ⟨L, hL, hpieces, hpw, hcover⟩ :=
    concrete_forest_bad_partition hback hout' bad R trees hgood hdisj
  rw [hcov] at hcover
  have hsubset : ∀ p ∈ L, p.privs ⊆ once \ bad := by
    intro p hp w hw
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨p, List.mem_toFinset.mpr hp, hw⟩
  refine ⟨L, ?_, ?_, hpw, hcover⟩
  · change R.card ≤ sharedGates.card + 1 at hR
    change (∑ r ∈ R, (trees r).marks) ≤ markedReads at hmarks
    omega
  · intro p hp
    obtain ⟨hg, hm, hn⟩ := hpieces p hp
    exact ⟨hg, hm, hn, hsubset p hp, one_mark_good_isTree hback hout' hg hm hn⟩

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Selection

lemma choose_disjoint_pairs {ι α : Type*} [DecidableEq α]
    (S : ι → Finset α) (hs : ∀ i, (S i).card = 2)
    (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∃ a b : ι → α, Function.Injective a ∧ Function.Injective b ∧
      (∀ i j, a i ≠ b j) ∧ ∀ i, a i ∈ S i ∧ b i ∈ S i ∧ a i ≠ b i := by
  classical
  have ex : ∀ i, ∃ a b, a ≠ b ∧ S i = {a, b} := fun i =>
    Finset.card_eq_two.mp (hs i)
  choose a b hab hS using ex
  have ha (i : ι) : a i ∈ S i := by rw [hS]; simp
  have hb (i : ι) : b i ∈ S i := by rw [hS]; simp
  have cross (i j : ι) (hij : i ≠ j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j) : False :=
    Finset.disjoint_left.mp (hd i j hij) hxi hxj
  refine ⟨a, b, ?_, ?_, ?_, fun i => ⟨ha i, hb i, hab i⟩⟩
  · intro i j he
    by_contra hij
    exact cross i j hij (a i) (ha i) (he ▸ ha j)
  · intro i j he
    by_contra hij
    exact cross i j hij (b i) (hb i) (he ▸ hb j)
  · intro i j he
    by_cases hij : i = j
    · subst j
      exact hab i he
    · exact cross i j hij (a i) (ha i) (he ▸ hb j)

lemma two_bank_piece_count {ι : Type*} [Fintype ι]
    (r c : ι → ℕ) (hr : ∀ i, r i ≤ 2) (hc : ∀ i, c i ≤ 2) :
    (∑ i, (r i + c i)) ≤ 2 * Fintype.card ι +
      Fintype.card {i // r i = 2} + Fintype.card {i // c i = 2} := by
  classical
  have each (i : ι) : r i + c i ≤ 2 +
      (if r i = 2 then 1 else 0) + (if c i = 2 then 1 else 0) := by
    have hri := hr i
    have hci := hc i
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => each i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at hsum
  simp only [Fintype.card_subtype, Finset.card_filter]
  simpa only [Nat.mul_comm (Fintype.card ι) 2, Finset.sum_add_distrib] using hsum

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Selection

namespace PEqualNP.Outside.L_meta_25875.Counting

open Finset

lemma shared_count_le_excess {α : Type*} [DecidableEq α]
    (W : Finset α) (d : α → ℕ) :
    (W.filter fun a => 2 ≤ d a).card ≤ ∑ a ∈ W, (d a - 1) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a ha
  split_ifs <;> omega

lemma normalized_budget (N s : ℕ) (v : ℕ → ℕ) (hs : 0 < s)
    (hlive : ∀ j < s, v (N+j) = 0 ↔ j+1 = s)
    (htotal : ∑ i ∈ Finset.range (N+s), v i = 2*s) :
    ((Finset.range N).filter (fun i => 1 ≤ v i)).card +
      ∑ i ∈ Finset.range (N+s), (v i - 1) = s+1 := by
  have split (t : Finset ℕ) :
      (∑ i ∈ t, v i) = (t.filter (fun i => 1 ≤ v i)).card +
        ∑ i ∈ t, (v i - 1) := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> omega
  have gates : ((Finset.range (N+s)).filter (fun i => 1 ≤ v i)).card =
      ((Finset.range N).filter (fun i => 1 ≤ v i)).card + (s-1) := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
    congr 1
    have hh : (∑ i ∈ Finset.range s, (if 1 ≤ v (N+i) then 1 else 0 : ℕ)) =
        ∑ i ∈ Finset.range s, (if i = s-1 then 0 else 1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hz := hlive i (Finset.mem_range.mp hi)
      split_ifs <;> omega
    rw [hh]
    simp [Finset.sum_ite, Finset.filter_ne', show s-1 ∈ Finset.range s by simp; omega]
  have h := split (Finset.range (N+s))
  rw [htotal, gates] at h
  omega

lemma binary_fanout_total (N s : ℕ) (left right : ℕ → ℕ)
    (hleft : ∀ j < s, left j < N+j)
    (hright : ∀ j < s, right j < N+j) :
    (∑ w ∈ Finset.range (N+s), ∑ j ∈ Finset.range s,
      ((if w = left j then 1 else 0) + (if w = right j then 1 else 0) : ℕ)) = 2*s := by
  rw [Finset.sum_comm]
  have step (j : ℕ) (hj : j ∈ Finset.range s) :
      (∑ w ∈ Finset.range (N+s),
        ((if w = left j then 1 else 0) + (if w = right j then 1 else 0) : ℕ)) = 2 := by
    have hjlt := Finset.mem_range.mp hj
    have h1 : left j < N+s := (hleft j hjlt).trans_le (by omega)
    have h2 : right j < N+s := (hright j hjlt).trans_le (by omega)
    simp [Finset.sum_add_distrib, h1, h2]
  calc
    _ = ∑ _j ∈ Finset.range s, 2 := Finset.sum_congr rfl step
    _ = _ := by simp [Nat.mul_comm]

lemma marked_reads_budget {α : Type*} [DecidableEq α]
    (W M : Finset α) (d : α → ℕ) (hM : M ⊆ W)
    (hpos : ∀ a ∈ M, 1 ≤ d a) :
    (∑ a ∈ M, d a) ≤ (∑ a ∈ W, (d a - 1)) + M.card := by
  have he : (∑ a ∈ M, d a) = (∑ a ∈ M, (d a - 1)) + M.card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have := hpos a ha
    omega
  rw [he]
  exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset hM) _

end PEqualNP.Outside.L_meta_25875.Counting

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.BinarySupport

open PEqualNP.MetaComplexity

def run (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

lemma run_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++
      [g.op ((run gs x).getD g.left false) ((run gs x).getD g.right false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List BinaryGate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma run_input (gs : List BinaryGate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, List.getD_append _ _ _ _ (by rw [run_length]; omega), ih]

lemma run_congr (N : ℕ) (gs : List BinaryGate) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N)
    (agree : ∀ g ∈ gs, ∀ i, (i = g.left ∨ i = g.right) → i < N →
      x.getD i false = y.getD i false) :
    ∀ i, N ≤ i → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    simp only [run, List.foldl_nil]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    have ih' := ih (fun a ha => agree a (List.mem_append_left _ ha))
    have operands (i : ℕ) (hi : i = g.left ∨ i = g.right) :
        (run gs x).getD i false = (run gs y).getD i false := by
      by_cases hN : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
        exact agree g (by simp) i hi hN
      · exact ih' i (by omega)
    intro i hi
    rw [run_snoc, run_snoc, getD_snoc, getD_snoc, run_length, run_length, hx, hy]
    split_ifs
    · rw [operands g.left (Or.inl rfl), operands g.right (Or.inr rfl)]
    · exact ih' i hi

def gateAt (C : BinaryCircuit) (j : ℕ) : BinaryGate :=
  C.gates.getD j ⟨fun _ _ => false, 0, 0⟩

def reads (C : BinaryCircuit) (w : ℕ) : ℕ :=
  ∑ j ∈ Finset.range C.size,
    ((if w = (gateAt C j).left then 1 else 0) +
      (if w = (gateAt C j).right then 1 else 0))

lemma reads_positive (C : BinaryCircuit) (g : BinaryGate) (hg : g ∈ C.gates)
    (w : ℕ) (hw : w = g.left ∨ w = g.right) : 0 < reads C w := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hg
  have gat : gateAt C j = g := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, he]
  have hterm : 1 ≤ (if w = (gateAt C j).left then 1 else 0) +
      (if w = (gateAt C j).right then 1 else 0) := by
    rw [gat]
    rcases hw with h | h <;> simp [h]
  have hsingle := Finset.single_le_sum
    (f := fun k => (if w = (gateAt C k).left then 1 else 0) +
      (if w = (gateAt C k).right then 1 else 0))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  exact lt_of_lt_of_le (by omega) hsingle

lemma eval_congr (N : ℕ) (C : BinaryCircuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (ho : N ≤ C.output)
    (agree : ∀ i < N, 0 < reads C i → x.getD i false = y.getD i false) :
    C.eval x = C.eval y := by
  apply run_congr N C.gates x y hx hy ?_ C.output ho
  intro g hg i hi hN
  exact agree i hN (reads_positive C g hg i hi)

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n+m := by
  simp [PEqualNP.Represents.oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n+v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i-n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n+v.val
      · simp [hv]
      · have hv' : ¬ i-n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.BinarySupport

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.BinarySupport

open PEqualNP.MetaComplexity

lemma reads_total (N : ℕ) (C : BinaryCircuit)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j) :
    (∑ w ∈ Finset.range (N+C.size), reads C w) = 2*C.size := by
  exact PEqualNP.Outside.L_meta_25875.Counting.binary_fanout_total N C.size
    (fun j => (gateAt C j).left) (fun j => (gateAt C j).right)
    (fun j hj => (back j hj).1) (fun j hj => (back j hj).2)

lemma reads_last (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j) :
    reads C (N+(C.size-1)) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  have hb := back j hjlt
  have hl : N+(C.size-1) ≠ (gateAt C j).left := by omega
  have hr : N+(C.size-1) ≠ (gateAt C j).right := by omega
  simp [hl, hr]

lemma reads_gate_zero_iff (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j)
    (live : ∀ j < C.size, j+1 < C.size → 0 < reads C (N+j)) :
    ∀ j < C.size, reads C (N+j) = 0 ↔ j+1 = C.size := by
  intro j hj
  constructor
  · intro hz
    by_contra h
    have hp := live j hj (by omega)
    omega
  · intro h
    have hjlast : j = C.size-1 := by omega
    rw [hjlast]
    exact reads_last N C hs back

lemma reads_budget (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j)
    (live : ∀ j < C.size, j+1 < C.size → 0 < reads C (N+j)) :
    ((Finset.range N).filter (fun w => 1 ≤ reads C w)).card +
      ∑ w ∈ Finset.range (N+C.size), (reads C w - 1) = C.size+1 := by
  exact PEqualNP.Outside.L_meta_25875.Counting.normalized_budget N C.size (reads C) hs
    (reads_gate_zero_iff N C hs back live) (reads_total N C back)

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.BinarySupport

namespace PEqualNP.Outside.L_meta_25875.Counting

lemma shared_name_gate_budget (N s : ℕ) (d : ℕ → ℕ) :
    ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range s).filter (fun j => 2 ≤ d (N+j))).card ≤
      ∑ w ∈ Finset.range (N+s), (d w - 1) := by
  have h := shared_count_le_excess (Finset.range (N+s)) d
  simpa only [Finset.card_filter, Finset.sum_range_add] using h

lemma shared_marked_reads_budget (N s bad : ℕ) (d : ℕ → ℕ) :
    (∑ w ∈ (Finset.range (N+s)).filter (fun w => 2 ≤ d w), d w) + bad ≤
      (∑ w ∈ Finset.range (N+s), (d w - 1)) +
      ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range s).filter (fun j => 2 ≤ d (N+j))).card + bad := by
  have h := marked_reads_budget (Finset.range (N+s))
    ((Finset.range (N+s)).filter (fun w => 2 ≤ d w)) d
    (Finset.filter_subset _ _) (fun w hw => by have := (Finset.mem_filter.mp hw).2; omega)
  have split : ((Finset.range (N+s)).filter (fun w => 2 ≤ d w)).card =
      ((Finset.range N).filter (fun w => 2 ≤ d w)).card +
      ((Finset.range s).filter (fun j => 2 ≤ d (N+j))).card := by
    simp only [Finset.card_filter, Finset.sum_range_add]
  rw [split] at h
  omega

end PEqualNP.Outside.L_meta_25875.Counting

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.BinarySupport

open PEqualNP.MetaComplexity

lemma normalize_back_reads (N : ℕ) (C : BinaryCircuit)
    (back : PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize.Back N C.gates) :
    ∀ j < C.size, (gateAt C j).left < N+j ∧ (gateAt C j).right < N+j := by
  intro j hj
  simpa only [gateAt, List.getD_eq_getElem _ _ hj] using back j hj

lemma normalize_live_reads (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (live : PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize.Live N C) :
    ∀ j < C.size, j+1 < C.size → 0 < reads C (N+j) := by
  intro j hj hjlast
  have hout := PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize.live_output_last N C live hs
  have hne : N+j ≠ C.output := by rw [hout]; change j+1 < C.gates.length at hjlast; omega
  obtain ⟨k, hk, hjk, he⟩ := live j hj hne
  apply reads_positive C C.gates[k] (List.getElem_mem hk) (N+j)
  simpa only [eq_comm] using he

lemma normalized_reads_budget (N : ℕ) (C : BinaryCircuit) (hs : 0 < C.size)
    (back : PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize.Back N C.gates)
    (live : PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Normalize.Live N C) :
    ((Finset.range N).filter (fun w => 1 ≤ reads C w)).card +
      ∑ w ∈ Finset.range (N+C.size), (reads C w - 1) = C.size+1 := by
  exact reads_budget N C hs (normalize_back_reads N C back)
    (normalize_live_reads N C hs live)

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.BinarySupport

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Assembly

open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis

lemma reads_eq (C : BinaryCircuit) (w : ℕ) :
    readsOf (binarySkeleton C) w = BinarySupport.reads C w := by
  unfold readsOf PEqualNP.MetaComplexity.NestedCover.readsIn BinarySupport.reads
  rw [binarySkeleton_size]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < C.gates.length := Finset.mem_range.mp hj
  rw [binarySkeleton_gate C j hj']
  simp only [BinarySupport.gateAt, List.getD_eq_getElem _ _ hj', List.count_cons, List.count_nil, beq_iff_eq]
  split_ifs <;> omega

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Assembly
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def binaryInputs (C : BinaryCircuit) (j : ℕ) : List ℕ :=
  ((C.gates[j]?).map (fun g => [g.left, g.right])).getD []

def binaryReadsIn (C : BinaryCircuit) (G : Finset ℕ) (w : ℕ) : ℕ :=
  ∑ j ∈ G, (binaryInputs C j).count w

def BinaryReadsBack (n : ℕ) (C : BinaryCircuit) : Prop :=
  ∀ j < C.gates.length, ∀ i ∈ binaryInputs C j, i < n + j

def BinaryIsTree (n : ℕ) (C : BinaryCircuit) (S E : Finset ℕ) : Prop :=
  ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := binaryReadsIn C region
    region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      (binaryInputs C j).length = 2 ∧ ∀ w ∈ binaryInputs C j, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧
      binaryReadsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)

lemma binarySkeleton_output (C : BinaryCircuit) : (binarySkeleton C).output = C.output := rfl

lemma binaryInputs_at (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length) :
    binaryInputs C j = [C.gates[j].left, C.gates[j].right] := by
  simp [binaryInputs, List.getElem?_eq_getElem hj]

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer

open PEqualNP.MetaComplexity

def run (gs : List BinaryGate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x

lemma run_snoc (gs : List BinaryGate) (g : BinaryGate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op ((run gs x).getD g.left false) ((run gs x).getD g.right false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List BinaryGate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma run_init (gs hs : List BinaryGate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, List.getD_append _ _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List BinaryGate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have h := run_init [] gs x i (by simpa using hi)
  simpa [run] using h

lemma getD_snoc_length (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by simp

lemma run_gate (gs : List BinaryGate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op
      (if gs[j].left < x.length + j then (run gs x).getD gs[j].left false else false)
      (if gs[j].right < x.length + j then (run gs x).getD gs[j].right false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have same (k w : ℕ) (hk : k ≤ gs.length) :
        (if w < x.length + k then (run (gs ++ [g]) x).getD w false else false) =
        (if w < x.length + k then (run gs x).getD w false else false) := by
      split_ifs with h
      · exact run_init gs [g] x w (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j _ (by omega), same j _ (by omega),
        run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst j
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ _ le_rfl, same _ _ le_rfl, run_snoc]
      have hlen := run_length gs x
      rw [← hlen]
      rw [getD_snoc_length]
      congr 1
      · split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
      · split_ifs with h
        · rfl
        · exact List.getD_eq_default _ _ (by omega)

def value (C : BinaryCircuit) (x : List Bool) (w : ℕ) : Bool :=
  (run C.gates x).getD w false

def inside (N : ℕ) (reg : Finset ℕ) (w : ℕ) : Prop :=
  N ≤ w ∧ w - N ∈ reg

lemma outside_agree (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (raw : ∀ i < N, i ∉ src → x.getD i false = y.getD i false)
    (root : value C x cap = value C y cap) :
    ∀ i, i ∉ src → ¬ inside N reg i → value C x i = value C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hs hi
    by_cases low : i < N
    · unfold value
      rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      exact raw i low hs
    by_cases far : N + C.gates.length ≤ i
    · unfold value
      rw [List.getD_eq_default _ _ (by rw [run_length, hx]; exact far),
        List.getD_eq_default _ _ (by rw [run_length, hy]; exact far)]
    let j := i - N
    have jlen : j < C.gates.length := by dsimp [j]; omega
    have idx : N + j = i := by dsimp [j]; omega
    have jr : j ∉ reg := fun h => hi ⟨by omega, h⟩
    have vx := run_gate C.gates x j jlen
    have vy := run_gate C.gates y j jlen
    rw [hx] at vx
    rw [hy] at vy
    change (run C.gates x).getD i false = (run C.gates y).getD i false
    rw [← idx, vx, vy]
    have arg (w : ℕ) (hw : w = C.gates[j].left ∨ w = C.gates[j].right) :
        (if w < N + j then value C x w else false) =
        (if w < N + j then value C y w else false) := by
      split_ifs with h
      · rcases closed j jlen jr w hw with rfl | ⟨hsrc, hreg⟩
        · exact root
        · exact ih w (by omega) hsrc hreg
      · rfl
    exact congrArg₂ (C.gates[j].op)
      (arg _ (Or.inl rfl)) (arg _ (Or.inr rfl))

lemma output_agree (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (visible : C.output = cap ∨ (C.output ∉ src ∧ ¬ inside N reg C.output))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (raw : ∀ i < N, i ∉ src → x.getD i false = y.getD i false)
    (root : value C x cap = value C y cap) : C.eval x = C.eval y := by
  change value C x C.output = value C y C.output
  rcases visible with h | ⟨hs, hi⟩
  · simpa only [h] using root
  · exact outside_agree N C src reg cap closed x y hx hy raw root C.output hs hi

lemma unary_factor {α : Type*} (keep : α → Prop) (f g : α → Bool)
    (h : ∀ a, keep a → ∀ b, keep b → f a = f b → g a = g b) :
    ∃ out : Bool → Bool, ∀ a, keep a → g a = out (f a) := by
  classical
  refine ⟨fun b => decide (∃ a, keep a ∧ f a = b ∧ g a = true), ?_⟩
  intro a ha
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hg
    exact ⟨a, ha, rfl, hg⟩
  · rintro ⟨b, hb, hf, hg⟩
    exact (h a ha b hb hf.symm).trans hg

lemma family_factor {α : Type*} (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (visible : C.output = cap ∨ (C.output ∉ src ∧ ¬ inside N reg C.output))
    (keep : α → Prop) (input : α → List Bool)
    (hlen : ∀ a, keep a → (input a).length = N)
    (raw : ∀ a, keep a → ∀ b, keep b → ∀ i < N, i ∉ src →
      (input a).getD i false = (input b).getD i false) :
    ∃ out : Bool → Bool, ∀ a, keep a → C.eval (input a) = out (value C (input a) cap) := by
  apply unary_factor keep (fun a => value C (input a) cap) (fun a => C.eval (input a))
  intro a ha b hb he
  exact output_agree N C src reg cap closed visible (input a) (input b)
    (hlen a ha) (hlen b hb) (raw a ha b hb) he

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer

open PEqualNP.MetaComplexity

def shadow (C : BinaryCircuit) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨C.gates.map (fun g => ⟨.and, [g.left, g.right]⟩), C.output⟩

lemma shadow_size (C : BinaryCircuit) : (shadow C).size = C.size := by
  simp [shadow, PEqualNP.CircuitLowerBounds.Circuit.size, BinaryCircuit.size]

lemma shadow_inputs (C : BinaryCircuit) (j : ℕ) (hj : j < C.gates.length) :
    (NestedCover.gateAt (shadow C) j).inputs = [C.gates[j].left, C.gates[j].right] := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ (by simpa [shadow] using hj)]
  simp [shadow]

lemma no_outside_read_of_equal_counts (C : PEqualNP.CircuitLowerBounds.Circuit)
    (reg : Finset ℕ) (hreg : reg ⊆ Finset.range C.size) (w j : ℕ)
    (he : NestedCover.readsIn C reg w = NestedCover.readsIn C (Finset.range C.size) w)
    (hj : j < C.size) (hjr : j ∉ reg) : w ∉ (NestedCover.gateAt C j).inputs := by
  intro hw
  have hp := List.count_pos_iff.mpr hw
  have hs : insert j reg ⊆ Finset.range C.size :=
    Finset.insert_subset (Finset.mem_range.mpr hj) hreg
  have hh := Finset.sum_le_sum_of_subset
    (f := fun k => (NestedCover.gateAt C k).inputs.count w) hs
  rw [Finset.sum_insert hjr] at hh
  unfold NestedCover.readsIn at he
  omega

lemma closed_of_counts (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (hreg : reg ⊆ Finset.range C.size)
    (he : ∀ w ∈ src ∪ reg.image (fun j => N + j), w ≠ cap →
      NestedCover.readsIn (shadow C) reg w =
        NestedCover.readsIn (shadow C) (Finset.range (shadow C).size) w) :
    ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w) := by
  intro j hj hjr w hw
  by_cases hcap : w = cap
  · exact Or.inl hcap
  right
  have hn : w ∉ src ∪ reg.image (fun j => N + j) := by
    intro hmem
    have hno := no_outside_read_of_equal_counts (shadow C) reg
      (by simpa only [shadow_size] using hreg) w j (he w hmem hcap)
      (by simpa only [shadow_size, BinaryCircuit.size] using hj) hjr
    apply hno
    rw [shadow_inputs C j hj]
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hw
  constructor
  · intro hs
    exact hn (Finset.mem_union_left _ hs)
  · intro hi
    apply hn
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨w - N, hi.2, Nat.add_sub_of_le hi.1⟩)

lemma visible_of_internal (N : ℕ) (C : BinaryCircuit) (src reg : Finset ℕ) (cap : ℕ)
    (ho : ∀ w ∈ src ∪ reg.image (fun j => N + j), w ≠ cap → C.output ≠ w) :
    C.output = cap ∨ (C.output ∉ src ∧ ¬ inside N reg C.output) := by
  by_cases hc : C.output = cap
  · exact Or.inl hc
  right
  constructor
  · intro hs
    exact ho C.output (Finset.mem_union_left _ hs) hc rfl
  · intro hi
    apply ho C.output (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨C.output - N, hi.2, Nat.add_sub_of_le hi.1⟩)) hc rfl

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal

lemma outside_agree
    (N s top cap : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (backL : ∀ j < s, left j < N + j)
    (backR : ∀ j < s, right j < N + j)
    (evalV : ∀ j < s, V (N + j) = op j (V (left j)) (V (right j)))
    (evalW : ∀ j < s, W (N + j) = op j (W (left j)) (W (right j)))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (exterior : ∀ j < s, ¬ region (N + j) →
      (¬ src (left j) ∧ (region (left j) → left j = N + top)) ∧
      (¬ src (right j) ∧ (region (right j) → right j = N + top)))
    (top_eq : N + top < cap → V (N + top) = W (N + top)) :
    ∀ i < cap, ¬ src i → ¬ region i → V i = W i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi hs hr
    by_cases low : i < N
    · exact raw i low hs
    by_cases far : N + s ≤ i
    · exact (pastV i far).trans (pastW i far).symm
    have hj : i - N < s := by omega
    have idx : N + (i - N) = i := by omega
    have cut := exterior (i - N) hj (by simpa only [idx] using hr)
    have eqL : V (left (i - N)) = W (left (i - N)) := by
      have lt : left (i - N) < i := by simpa only [idx] using backL (i - N) hj
      by_cases hin : region (left (i - N))
      · have he := cut.1.2 hin
        rw [he]
        exact top_eq (by omega)
      · exact ih _ lt (by omega) cut.1.1 hin
    have eqR : V (right (i - N)) = W (right (i - N)) := by
      have lt : right (i - N) < i := by simpa only [idx] using backR (i - N) hj
      by_cases hin : region (right (i - N))
      · have he := cut.2.2 hin
        rw [he]
        exact top_eq (by omega)
      · exact ih _ lt (by omega) cut.2.1 hin
    have v := evalV (i - N) hj
    have w := evalW (i - N) hj
    rw [idx] at v w
    rw [v, w, eqL, eqR]

lemma outside_agree_cut
    (N s root limit : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (evalV : ∀ j < s, V (N + j) = op j
      (if left j < N+j then V (left j) else false)
      (if right j < N+j then V (right j) else false))
    (evalW : ∀ j < s, W (N + j) = op j
      (if left j < N+j then W (left j) else false)
      (if right j < N+j then W (right j) else false))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (closed : ∀ j < s, ¬ region (N+j) →
      (left j = root ∨ (¬ src (left j) ∧ ¬ region (left j))) ∧
      (right j = root ∨ (¬ src (right j) ∧ ¬ region (right j))))
    (root_eq : root < limit → V root = W root) :
    ∀ i < limit, ¬ src i → ¬ region i → V i = W i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi hs hr
    by_cases low : i < N
    · exact raw i low hs
    by_cases far : N+s ≤ i
    · exact (pastV i far).trans (pastW i far).symm
    have hj : i-N < s := by omega
    have idx : N+(i-N) = i := by omega
    have cut := closed (i-N) hj (by simpa only [idx] using hr)
    have arg (w : Nat) (hw : w = root ∨ (¬ src w ∧ ¬ region w)) :
        (if w < i then V w else false) = (if w < i then W w else false) := by
      split <;> rename_i h
      · rcases hw with rfl | ⟨hsrc,hreg⟩
        · exact root_eq (by omega)
        · exact ih w h (by omega) hsrc hreg
      · rfl
    have v := evalV (i-N) hj
    have w := evalW (i-N) hj
    rw [idx] at v w
    rw [v,w]
    rw [arg _ cut.1, arg _ cut.2]

lemma boundary_agree_cut
    (N s root : Nat) (left right : Nat → Nat)
    (op : Nat → Bool → Bool → Bool)
    (V W : Nat → Bool) (src region : Nat → Prop)
    (evalV : ∀ j < s, V (N + j) = op j
      (if left j < N+j then V (left j) else false)
      (if right j < N+j then V (right j) else false))
    (evalW : ∀ j < s, W (N + j) = op j
      (if left j < N+j then W (left j) else false)
      (if right j < N+j then W (right j) else false))
    (pastV : ∀ i, N + s ≤ i → V i = false)
    (pastW : ∀ i, N + s ≤ i → W i = false)
    (raw : ∀ i < N, ¬ src i → V i = W i)
    (closed : ∀ j < s, ¬ region (N+j) →
      (left j = root ∨ (¬ src (left j) ∧ ¬ region (left j))) ∧
      (right j = root ∨ (¬ src (right j) ∧ ¬ region (right j))))
    (w : Nat) (earlier : w < root) (notSrc : ¬ src w) (notRegion : ¬ region w) :
    V w = W w := by
  exact outside_agree_cut N s root root left right op V W src region
    evalV evalW pastV pastW raw closed (by omega) w earlier notSrc notRegion

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal

lemma oneHot_getD_ne {n : Nat} (u : Fin n) (i : Nat) (hi : i ≠ u.val) :
    (List.ofFn (fun k : Fin n => decide (k = u))).getD i false = false := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h, Fin.ext_iff, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma oneHot_left_blank {n : Nat} (u : Fin n) (right : List Bool) (i : Nat)
    (hi : i ≠ u.val) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++ right).getD i false =
      (List.replicate n false ++ right).getD i false := by
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa), List.getD_append _ _ _ _ (by simpa)]
    rw [oneHot_getD_ne u i hi, List.getD_replicate false h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp only [List.length_ofFn, List.length_replicate]

lemma oneHot_right_blank {n m : Nat} (left : List Bool) (hlen : left.length = n)
    (v : Fin m) (i : Nat) (hi : i ≠ n + v.val) :
    (left ++ List.ofFn (fun k : Fin m => decide (k = v))).getD i false =
      (left ++ List.replicate m false).getD i false := by
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]
    rw [oneHot_getD_ne v (i-n) (by omega)]
    simp [List.getD_eq_getElem?_getD]

lemma oneEach_left_raw {n m : Nat} (u : Fin n) (v : Fin m)
    (src : Nat → Prop) (hu : src u.val) (i : Nat) (hi : ¬ src i) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++
      List.ofFn (fun k : Fin m => decide (k = v))).getD i false =
    (List.replicate n false ++
      List.ofFn (fun k : Fin m => decide (k = v))).getD i false := by
  apply oneHot_left_blank
  intro he
  exact hi (he.symm ▸ hu)

lemma oneEach_right_raw {n m : Nat} (u : Fin n) (v : Fin m)
    (src : Nat → Prop) (hv : src (n + v.val)) (i : Nat) (hi : ¬ src i) :
    (List.ofFn (fun k : Fin n => decide (k = u)) ++
      List.ofFn (fun k : Fin m => decide (k = v))).getD i false =
    (List.ofFn (fun k : Fin n => decide (k = u)) ++
      List.replicate m false).getD i false := by
  apply oneHot_right_blank (n := n) (m := m) _ (by simp) v i
  intro he
  exact hi (he.symm ▸ hv)

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer

open PEqualNP.MetaComplexity

lemma boundary_value_agree (N : Nat) (C : BinaryCircuit) (src reg : Finset Nat) (cap : Nat)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside N reg w))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (raw : ∀ i < N, i ∉ src → x.getD i false = y.getD i false)
    (w : Nat) (earlier : w < cap) (notSrc : w ∉ src) (notRegion : ¬ inside N reg w) :
    value C x w = value C y w := by
  let gate (j : Nat) : BinaryGate := C.gates.getD j ⟨fun _ _ => false, 0, 0⟩
  have gate_eq (j : Nat) (hj : j < C.gates.length) : gate j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  refine PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal.boundary_agree_cut
    N C.gates.length cap (fun j => (gate j).left) (fun j => (gate j).right)
    (fun j => (gate j).op) (value C x) (value C y)
    (fun i => i ∈ src) (inside N reg) ?_ ?_ ?_ ?_ ?_ ?_
    w earlier notSrc notRegion
  · intro j hj
    have h := run_gate C.gates x j hj
    rw [hx] at h
    simpa only [gate_eq j hj, value] using h
  · intro j hj
    have h := run_gate C.gates y j hj
    rw [hy] at h
    simpa only [gate_eq j hj, value] using h
  · intro i hi
    exact List.getD_eq_default _ _ (by rw [run_length, hx]; exact hi)
  · intro i hi
    exact List.getD_eq_default _ _ (by rw [run_length, hy]; exact hi)
  · intro i hi hs
    change (run C.gates x).getD i false = (run C.gates y).getD i false
    rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
    exact raw i hi hs
  · intro j hj hr
    have hjr : j ∉ reg := by simpa [inside] using hr
    rw [gate_eq j hj]
    exact ⟨closed j hj hjr _ (Or.inl rfl), closed j hj hjr _ (Or.inr rfl)⟩

lemma oneEach_boundary_left {n m : Nat} (C : BinaryCircuit)
    (src reg : Finset Nat) (cap : Nat)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside (n+m) reg w))
    (u : Fin n) (v : Fin m) (hu : u.val ∈ src)
    (w : Nat) (earlier : w < cap) (notSrc : w ∉ src)
    (notRegion : ¬ inside (n+m) reg w) :
    value C (List.ofFn (fun k : Fin n => decide (k=u)) ++
      List.ofFn (fun k : Fin m => decide (k=v))) w =
    value C (List.replicate n false ++
      List.ofFn (fun k : Fin m => decide (k=v))) w := by
  apply boundary_value_agree (n+m) C src reg cap closed _ _ (by simp) (by simp)
    ?_ w earlier notSrc notRegion
  intro i hi hsrc
  exact PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal.oneEach_left_raw u v
    (fun k => k ∈ src) hu i hsrc

lemma oneEach_boundary_right {n m : Nat} (C : BinaryCircuit)
    (src reg : Finset Nat) (cap : Nat)
    (closed : ∀ j (hj : j < C.gates.length), j ∉ reg →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ src ∧ ¬ inside (n+m) reg w))
    (u : Fin n) (v : Fin m) (hv : n+v.val ∈ src)
    (w : Nat) (earlier : w < cap) (notSrc : w ∉ src)
    (notRegion : ¬ inside (n+m) reg w) :
    value C (List.ofFn (fun k : Fin n => decide (k=u)) ++
      List.ofFn (fun k : Fin m => decide (k=v))) w =
    value C (List.ofFn (fun k : Fin n => decide (k=u)) ++
      List.replicate m false) w := by
  apply boundary_value_agree (n+m) C src reg cap closed _ _ (by simp) (by simp)
    ?_ w earlier notSrc notRegion
  intro i hi hsrc
  exact PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal.oneEach_right_raw u v
    (fun k => k ∈ src) hv i hsrc

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Semantics

lemma region_interior_congr (N : ℕ) (R S E : Finset ℕ)
    (left right : ℕ → ℕ) (op : ℕ → Bool → Bool → Bool)
    (v w : ℕ → Bool)
    (hleft : ∀ j ∈ R, left j < N + j)
    (hright : ∀ j ∈ R, right j < N + j)
    (hclosed : ∀ j ∈ R, ∀ i, i = left j ∨ i = right j →
      i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (hS : ∀ i ∈ S, v i = w i)
    (hE : ∀ i ∈ E, v i = w i)
    (hv : ∀ j ∈ R, v (N + j) = op j (v (left j)) (v (right j)))
    (hw : ∀ j ∈ R, w (N + j) = op j (w (left j)) (w (right j))) :
    ∀ j ∈ R, v (N + j) = w (N + j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hwire (i : ℕ) (hi : i < N + j)
        (hc : i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E) : v i = w i := by
      rcases hc with hs | ⟨k, hk, rfl⟩ | he
      · exact hS i hs
      · exact ih k (by omega) hk
      · exact hE i he
    rw [hv j hj, hw j hj]
    rw [hwire (left j) (hleft j hj) (hclosed j hj _ (Or.inl rfl)),
      hwire (right j) (hright j hj) (hclosed j hj _ (Or.inr rfl))]

lemma region_cap_congr (N : ℕ) (R S E : Finset ℕ)
    (left right : ℕ → ℕ) (op : ℕ → Bool → Bool → Bool)
    (v w : ℕ → Bool)
    (hleft : ∀ j ∈ R, left j < N + j)
    (hright : ∀ j ∈ R, right j < N + j)
    (hclosed : ∀ j ∈ R, ∀ i, i = left j ∨ i = right j →
      i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (hS : ∀ i ∈ S, v i = w i)
    (hE : ∀ i ∈ E, v i = w i)
    (hv : ∀ j ∈ R, v (N + j) = op j (v (left j)) (v (right j)))
    (hw : ∀ j ∈ R, w (N + j) = op j (w (left j)) (w (right j)))
    (root : ℕ) (hroot : root ∈ S ∨ ∃ j ∈ R, root = N + j) :
    v root = w root := by
  rcases hroot with hs | ⟨j, hj, rfl⟩
  · exact hS root hs
  · exact region_interior_congr N R S E left right op v w
      hleft hright hclosed hS hE hv hw j hj

lemma bool_fiber_factor {X : Type*} (f : X → Bool) (t : X → Bool)
    (h : ∀ x y, t x = t y → f x = f y) :
    ∃ q : Bool → Bool, ∀ x, f x = q (t x) := by
  classical
  let q : Bool → Bool := fun b =>
    if hb : ∃ x, t x = b then f (Classical.choose hb) else false
  refine ⟨q, ?_⟩
  intro x
  have hx : ∃ y, t y = t x := ⟨x, rfl⟩
  simp only [q, dite_eq_left hx]
  exact h x (Classical.choose hx) (Classical.choose_spec hx).symm

lemma binary_region_congr (N : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit)
    (R S E : Finset ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range N)
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < N + j ∧ C.gates[j].right < N + j)
    (hclosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hraw : ∀ i ∈ S, x.getD i false = y.getD i false)
    (hboundary : ∀ i ∈ E, PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C x i = PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C y i)
    (root : ℕ) (hroot : root ∈ S ∨ ∃ j ∈ R, root = N + j) :
    PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C x root = PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C y root := by
  let left : ℕ → ℕ := fun j => if hj : j < C.gates.length then C.gates[j].left else 0
  let right : ℕ → ℕ := fun j => if hj : j < C.gates.length then C.gates[j].right else 0
  let op : ℕ → Bool → Bool → Bool := fun j =>
    if hj : j < C.gates.length then C.gates[j].op else fun _ _ => false
  have hlen (j : ℕ) (hj : j ∈ R) : j < C.gates.length := Finset.mem_range.mp (hR hj)
  apply region_cap_congr N R S E left right op
    (PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C x) (PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C y) ?_ ?_ ?_ ?_
    hboundary ?_ ?_ root hroot
  · intro j hj
    simpa [left, hlen j hj] using (hback j (hlen j hj) hj).1
  · intro j hj
    simpa [right, hlen j hj] using (hback j (hlen j hj) hj).2
  · intro j hj i hi
    apply hclosed j (hlen j hj) hj i
    simpa [left, right, hlen j hj] using hi
  · intro i hi
    have hil : i < N := Finset.mem_range.mp (hS hi)
    unfold PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value
    rw [PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.run_input _ _ _ (by omega),
      PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.run_input _ _ _ (by omega)]
    exact hraw i hi
  · intro j hj
    have h := PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.run_gate C.gates x j (hlen j hj)
    rw [hx] at h
    simpa [PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value, left, right, op, hlen j hj,
      (hback j (hlen j hj) hj).1, (hback j (hlen j hj) hj).2] using h
  · intro j hj
    have h := PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.run_gate C.gates y j (hlen j hj)
    rw [hy] at h
    simpa [PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value, left, right, op, hlen j hj,
      (hback j (hlen j hj) hj).1, (hback j (hlen j hj) hj).2] using h

lemma binary_region_family_factor {X : Type*}
    (N : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range N)
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < N + j ∧ C.gates[j].right < N + j)
    (hclosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (root : ℕ) (hroot : root ∈ S ∨ ∃ j ∈ R, root = N + j)
    (keep : X → Prop) (input : X → List Bool) (t : X → Bool)
    (hlen : ∀ a, keep a → (input a).length = N)
    (hraw : ∀ a, keep a → ∀ b, keep b → ∀ i ∈ S,
      (input a).getD i false = (input b).getD i false)
    (hboundary : ∀ a, keep a → ∀ b, keep b → t a = t b → ∀ i ∈ E,
      PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a) i = PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input b) i) :
    ∃ q : Bool → Bool, ∀ a, keep a →
      PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a) root = q (t a) := by
  obtain ⟨q, hq⟩ := bool_fiber_factor
    (fun a : {a : X // keep a} => PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a.val) root)
    (fun a => t a.val) (by
      intro a b hab
      exact binary_region_congr N C R S E hR hS hback hclosed
        (input a.val) (input b.val) (hlen a.val a.property) (hlen b.val b.property)
        (hraw a.val a.property b.val b.property)
        (hboundary a.val a.property b.val b.property hab) root hroot)
  exact ⟨q, fun a ha => hq ⟨a, ha⟩⟩

def bankInputRight {n : ℕ} (fixed : List Bool) (v : Fin n) : List Bool :=
  fixed ++ List.ofFn (fun j : Fin n => decide (j = v))

def bankInputLeft {n : ℕ} (u : Fin n) (fixed : List Bool) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u)) ++ fixed

lemma bank_input_right_raw_agree {n : ℕ} (fixed : List Bool) (hlen : fixed.length = n)
    (S : Finset ℕ) (v w : Fin n) (hv : n + v.val ∉ S) (hw : n + w.val ∉ S) :
    ∀ i ∈ S, (bankInputRight fixed v).getD i false =
      (bankInputRight fixed w).getD i false := by
  intro i hi
  simp only [bankInputRight, List.getD_eq_getElem?_getD, List.getElem?_append, hlen]
  by_cases h : i < n
  · simp [h]
  · by_cases h' : i - n < n
    · have h₁ : (⟨i - n, h'⟩ : Fin n) ≠ v := by
        intro he
        apply hv
        have he' := congrArg Fin.val he
        have heq : n + v.val = i := by dsimp at he'; omega
        simpa [heq] using hi
      have h₂ : (⟨i - n, h'⟩ : Fin n) ≠ w := by
        intro he
        apply hw
        have he' := congrArg Fin.val he
        have heq : n + w.val = i := by dsimp at he'; omega
        simpa [heq] using hi
      simp [h, h', h₁, h₂]
    · simp [h, h']

lemma bank_input_left_raw_agree {n : ℕ} (fixed : List Bool)
    (S : Finset ℕ) (u w : Fin n) (hu : u.val ∉ S) (hw : w.val ∉ S) :
    ∀ i ∈ S, (bankInputLeft u fixed).getD i false =
      (bankInputLeft w fixed).getD i false := by
  intro i hi
  simp only [bankInputLeft, List.getD_eq_getElem?_getD,
    List.getElem?_append, List.length_ofFn]
  by_cases h : i < n
  · have h₁ : (⟨i, h⟩ : Fin n) ≠ u := by
      intro he
      apply hu
      simpa [← congrArg Fin.val he] using hi
    have h₂ : (⟨i, h⟩ : Fin n) ≠ w := by
      intro he
      apply hw
      simpa [← congrArg Fin.val he] using hi
    simp [h, h₁, h₂]
  · simp [h]

lemma binary_region_tensor_factor {A X : Type*}
    (N : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ)
    (cap : ℕ) (K : A → Prop) (P : X → Prop) (input : A → X → List Bool)
    (a₀ : A) (ha₀ : K a₀)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range N)
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < N + j ∧ C.gates[j].right < N + j)
    (innerClosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E)
    (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = N + j)
    (outerClosed : ∀ j (hj : j < C.gates.length), j ∉ R →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside N R w))
    (visible : C.output = cap ∨
      (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside N R C.output))
    (hE : E.card ≤ 1)
    (hlen : ∀ a, K a → ∀ x, P x → (input a x).length = N)
    (rawInside : ∀ a, K a → ∀ x, P x → ∀ y, P y → ∀ i ∈ S,
      (input a x).getD i false = (input a y).getD i false)
    (rawOutside : ∀ x, P x → ∀ a, K a → ∀ b, K b → ∀ i < N, i ∉ S →
      (input a x).getD i false = (input b x).getD i false)
    (boundaryCommon : ∀ a, K a → ∀ x, P x → ∀ e ∈ E,
      PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a x) e =
        PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a₀ x) e) :
    ∃ t : X → Bool, ∃ q : A → Bool → Bool, ∃ U : X → Bool → Bool,
      ∀ a, K a → ∀ x, P x → C.eval (input a x) = U x (q a (t x)) := by
  classical
  obtain ⟨port, hport⟩ : ∃ port : ℕ, ∀ e ∈ E, e = port := by
    by_cases hnonempty : E.Nonempty
    · obtain ⟨port, hp⟩ := hnonempty
      exact ⟨port, fun e he => Finset.card_le_one.mp hE e he port hp⟩
    · exact ⟨0, fun e he => False.elim (hnonempty ⟨e, he⟩)⟩
  let t : X → Bool := fun x => PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a₀ x) port
  have inner : ∀ a, ∃ q : Bool → Bool, ∀ x, K a → P x →
      PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a x) cap = q (t x) := by
    intro a
    by_cases ha : K a
    · obtain ⟨q, hq⟩ := binary_region_family_factor N C R S E hR hS hback
        innerClosed cap hcap P (input a) t (hlen a ha) (rawInside a ha) (by
          intro x hx y hy hxy e he
          rw [boundaryCommon a ha x hx e he, boundaryCommon a ha y hy e he,
            hport e he]
          exact hxy)
      exact ⟨q, fun x _ hx => hq x hx⟩
    · exact ⟨fun _ => false, fun x hk _ => False.elim (ha hk)⟩
  choose q hq using inner
  have outer : ∀ x, ∃ U : Bool → Bool, ∀ a, K a → P x →
      C.eval (input a x) = U (PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (input a x) cap) := by
    intro x
    by_cases hx : P x
    · obtain ⟨U, hU⟩ := PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.family_factor N C S R cap outerClosed visible
        K (fun a => input a x) (fun a ha => hlen a ha x hx) (rawOutside x hx)
      exact ⟨U, fun a ha _ => hU a ha⟩
    · exact ⟨fun _ => false, fun a _ hp => False.elim (hx hp)⟩
  choose U hU using outer
  refine ⟨t, q, U, ?_⟩
  intro a ha x hx
  rw [hU x a ha hx, hq a x ha hx]

def blankLeft {n : ℕ} (v : Fin n) : List Bool :=
  List.replicate n false ++ List.ofFn (fun k : Fin n => decide (k = v))

def blankRight {n : ℕ} (u : Fin n) : List Bool :=
  List.ofFn (fun k : Fin n => decide (k = u)) ++ List.replicate n false

lemma row_region_tensor_factor {n : ℕ}
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ) (cap : ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range (2 * n))
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < 2 * n + j ∧ C.gates[j].right < 2 * n + j)
    (innerClosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = 2 * n + k) ∨ i ∈ E)
    (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = 2 * n + j)
    (outerClosed : ∀ j (hj : j < C.gates.length), j ∉ R →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside (2 * n) R w))
    (visible : C.output = cap ∨
      (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside (2 * n) R C.output))
    (hE : E.card ≤ 1) (post : Bool → Bool)
    (boundaryCommon : ∀ u : Fin n, u.val ∈ S → ∀ v : Fin n, n + v.val ∉ S →
      ∀ e ∈ E, PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (PEqualNP.Represents.oneEach u v) e =
        PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (blankLeft v) e) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ v, n + v.val ∉ S → post (C.eval (blankLeft v)) = U v (q₀ (t v))) ∧
      (∀ u, u.val ∈ S → ∀ v, n + v.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U v (q u (t v))) := by
  classical
  let K : Option (Fin n) → Prop := fun a => match a with
    | none => True
    | some u => u.val ∈ S
  let fixed : Option (Fin n) → List Bool := fun a => match a with
    | none => List.replicate n false
    | some u => List.ofFn (fun k : Fin n => decide (k = u))
  let input : Option (Fin n) → Fin n → List Bool := fun a v => bankInputRight (fixed a) v
  have fixed_length (a : Option (Fin n)) : (fixed a).length = n := by
    cases a <;> simp [fixed]
  have raw_blank (a : Option (Fin n)) (ha : K a) (v : Fin n) (i : ℕ) (hi : i ∉ S) :
      (input a v).getD i false = (blankLeft v).getD i false := by
    cases a with
    | none => rfl
    | some u =>
      exact PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal.oneEach_left_raw
        u v (fun j => j ∈ S) ha i hi
  obtain ⟨t, q, U, hfactor⟩ := binary_region_tensor_factor (2 * n) C R S E cap
    K (fun v : Fin n => n + v.val ∉ S) input none trivial hR hS hback innerClosed
    hcap outerClosed visible hE
    (by intro a ha v hv; simp [input, bankInputRight, fixed_length, two_mul])
    (by
      intro a ha v hv w hw
      exact bank_input_right_raw_agree (fixed a) (fixed_length a) S v w hv hw)
    (by
      intro v hv a ha b hb i hi his
      exact (raw_blank a ha v i his).trans (raw_blank b hb v i his).symm)
    (by
      intro a ha v hv e he
      cases a with
      | none => rfl
      | some u => exact boundaryCommon u ha v hv e he)
  refine ⟨t, q none, (fun u => q (some u)), (fun v b => post (U v b)), ?_, ?_⟩
  · intro v hv
    exact congrArg post (hfactor none trivial v hv)
  · intro u hu v hv
    exact congrArg post (hfactor (some u) hu v hv)

lemma col_region_tensor_factor {n : ℕ}
    (C : PEqualNP.MetaComplexity.BinaryCircuit) (R S E : Finset ℕ) (cap : ℕ)
    (hR : R ⊆ Finset.range C.gates.length) (hS : S ⊆ Finset.range (2 * n))
    (hback : ∀ j (hj : j < C.gates.length), j ∈ R →
      C.gates[j].left < 2 * n + j ∧ C.gates[j].right < 2 * n + j)
    (innerClosed : ∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
      i = C.gates[j].left ∨ i = C.gates[j].right →
        i ∈ S ∨ (∃ k ∈ R, i = 2 * n + k) ∨ i ∈ E)
    (hcap : cap ∈ S ∨ ∃ j ∈ R, cap = 2 * n + j)
    (outerClosed : ∀ j (hj : j < C.gates.length), j ∉ R →
      ∀ w, w = C.gates[j].left ∨ w = C.gates[j].right →
        w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside (2 * n) R w))
    (visible : C.output = cap ∨
      (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside (2 * n) R C.output))
    (hE : E.card ≤ 1) (post : Bool → Bool)
    (boundaryCommon : ∀ v : Fin n, n + v.val ∈ S → ∀ u : Fin n, u.val ∉ S →
      ∀ e ∈ E, PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (PEqualNP.Represents.oneEach u v) e =
        PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.value C (blankRight u) e) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ u, u.val ∉ S → post (C.eval (blankRight u)) = U u (q₀ (t u))) ∧
      (∀ v, n + v.val ∈ S → ∀ u, u.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U u (q v (t u))) := by
  classical
  let K : Option (Fin n) → Prop := fun a => match a with
    | none => True
    | some v => n + v.val ∈ S
  let fixed : Option (Fin n) → List Bool := fun a => match a with
    | none => List.replicate n false
    | some v => List.ofFn (fun k : Fin n => decide (k = v))
  let input : Option (Fin n) → Fin n → List Bool := fun a u => bankInputLeft u (fixed a)
  have fixed_length (a : Option (Fin n)) : (fixed a).length = n := by
    cases a <;> simp [fixed]
  have raw_blank (a : Option (Fin n)) (ha : K a) (u : Fin n) (i : ℕ) (hi : i ∉ S) :
      (input a u).getD i false = (blankRight u).getD i false := by
    cases a with
    | none => rfl
    | some v =>
      exact PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Causal.oneEach_right_raw
        u v (fun j => j ∈ S) ha i hi
  obtain ⟨t, q, U, hfactor⟩ := binary_region_tensor_factor (2 * n) C R S E cap
    K (fun u : Fin n => u.val ∉ S) input none trivial hR hS hback innerClosed
    hcap outerClosed visible hE
    (by intro a ha u hu; simp [input, bankInputLeft, fixed_length, two_mul])
    (by
      intro a ha u hu w hw
      exact bank_input_left_raw_agree (fixed a) S u w hu hw)
    (by
      intro u hu a ha b hb i hi his
      exact (raw_blank a ha u i his).trans (raw_blank b hb u i his).symm)
    (by
      intro a ha u hu e he
      cases a with
      | none => rfl
      | some v => exact boundaryCommon v ha u hu e he)
  refine ⟨t, q none, (fun v => q (some v)), (fun u b => post (U u b)), ?_, ?_⟩
  · intro u hu
    exact congrArg post (hfactor none trivial u hu)
  · intro v hv u hu
    exact congrArg post (hfactor (some v) hv u hu)

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Semantics
namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.MetaComplexity Semantics

lemma shadow_binary_reads (C : BinaryCircuit) (G : Finset ℕ)
    (hG : G ⊆ Finset.range C.size) (w : ℕ) :
    NestedCover.readsIn (PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.shadow C) G w = binaryReadsIn C G w := by
  unfold NestedCover.readsIn binaryReadsIn
  apply Finset.sum_congr rfl
  intro j hj
  have hlen : j < C.gates.length := Finset.mem_range.mp (hG hj)
  rw [PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.shadow_inputs C j hlen, binaryInputs_at C j hlen]

lemma binary_tree_topology (N : ℕ) (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : BinaryIsTree N C S E) (hback : BinaryReadsBack N C) :
    ∃ (R : Finset ℕ) (cap : ℕ),
      R ⊆ Finset.range C.gates.length ∧
      (cap ∈ S ∨ ∃ j ∈ R, cap = N + j) ∧
      (∀ j (hj : j < C.gates.length), j ∈ R →
        C.gates[j].left < N + j ∧ C.gates[j].right < N + j) ∧
      (∀ j (hj : j < C.gates.length), j ∈ R → ∀ i,
        i = C.gates[j].left ∨ i = C.gates[j].right →
          i ∈ S ∨ (∃ k ∈ R, i = N + k) ∨ i ∈ E) ∧
      (∀ j (hj : j < C.gates.length), j ∉ R → ∀ w,
        w = C.gates[j].left ∨ w = C.gates[j].right →
          w = cap ∨ (w ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside N R w)) ∧
      (C.output = cap ∨ (C.output ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside N R C.output)) ∧
      (∀ e ∈ E, e < cap ∧ e ∉ S ∧ ¬ PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.inside N R e) := by
  classical
  obtain ⟨R, cap, hR, hcap, hcapread, hE, hin, hint⟩ := htree
  refine ⟨R, cap, hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases Finset.mem_union.mp hcap with hs | hr
    · exact Or.inl hs
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hr
      exact Or.inr ⟨j, hj, he.symm⟩
  · intro j hj hreg
    constructor
    · apply hback j hj
      simp [binaryInputs_at C j hj]
    · apply hback j hj
      simp [binaryInputs_at C j hj]
  · intro j hj hreg i hi
    have hm : i ∈ binaryInputs C j := by
      simpa [binaryInputs_at C j hj] using hi
    rcases (hin j hreg).2 i hm with hw | he
    · rcases Finset.mem_union.mp hw with hs | hr
      · exact Or.inl hs
      · obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hr
        exact Or.inr (Or.inl ⟨k, hk, he.symm⟩)
    · exact Or.inr (Or.inr he)
  · apply PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.closed_of_counts N C S R cap hR
    intro w hw hne
    rw [PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.shadow_size,
      shadow_binary_reads C R hR w,
      shadow_binary_reads C (Finset.range C.size) (Finset.Subset.refl _) w]
    exact (hint w hw hne).1.trans (hint w hw hne).2.1.symm
  · apply PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.visible_of_internal N C S R cap
    intro w hw hne
    exact (hint w hw hne).2.2
  · intro e he
    have hb := hE e he
    refine ⟨hb.2.1, ?_, ?_⟩
    · intro hs
      exact hb.1 (Finset.mem_union_left _ hs)
    · intro hr
      apply hb.1
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨e - N, hr.2, Nat.add_sub_of_le hr.1⟩)

lemma binary_tree_row_factor {n : ℕ} (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : BinaryIsTree (2 * n) C S E) (hback : BinaryReadsBack (2 * n) C)
    (hS : S ⊆ Finset.range (2 * n)) (hE : E.card ≤ 1) (post : Bool → Bool) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ v, n + v.val ∉ S → post (C.eval (blankLeft v)) = U v (q₀ (t v))) ∧
      (∀ u, u.val ∈ S → ∀ v, n + v.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U v (q u (t v))) := by
  obtain ⟨R, cap, hR, hcap, hbk, hin, hout, hvis, hbound⟩ :=
    binary_tree_topology (2 * n) C S E htree hback
  apply row_region_tensor_factor C R S E cap hR hS hbk hin hcap hout hvis hE post
  intro u hu v hv e he
  have hb := hbound e he
  have h := PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.oneEach_boundary_left C S R cap
    (by simpa only [two_mul] using hout) u v hu e hb.1 hb.2.1
    (by simpa only [two_mul] using hb.2.2)
  exact h

lemma binary_tree_col_factor {n : ℕ} (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : BinaryIsTree (2 * n) C S E) (hback : BinaryReadsBack (2 * n) C)
    (hS : S ⊆ Finset.range (2 * n)) (hE : E.card ≤ 1) (post : Bool → Bool) :
    ∃ t : Fin n → Bool, ∃ q₀ : Bool → Bool, ∃ q : Fin n → Bool → Bool,
      ∃ U : Fin n → Bool → Bool,
      (∀ u, u.val ∉ S → post (C.eval (blankRight u)) = U u (q₀ (t u))) ∧
      (∀ v, n + v.val ∈ S → ∀ u, u.val ∉ S →
        post (C.eval (PEqualNP.Represents.oneEach u v)) = U u (q v (t u))) := by
  obtain ⟨R, cap, hR, hcap, hbk, hin, hout, hvis, hbound⟩ :=
    binary_tree_topology (2 * n) C S E htree hback
  apply col_region_tensor_factor C R S E cap hR hS hbk hin hcap hout hvis hE post
  intro v hv u hu e he
  have hb := hbound e he
  have h := PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Outer.oneEach_boundary_right C S R cap
    (by simpa only [two_mul] using hout) u v hv e hb.1 hb.2.1
    (by simpa only [two_mul] using hb.2.2)
  exact h

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

lemma one_boundary_missing : ∀ (f₀ f₁ f₂ : Bool → Bool),
    ∃ p q : Bool, (p = true ∨ q = true) ∧
      ∀ (t : Bool) (c : Bool → Bool),
        ¬ (Bool.xor (c (f₁ t)) (c (f₀ t)) = p ∧
          Bool.xor (c (f₂ t)) (c (f₀ t)) = q) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis

namespace PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma skeleton_binary_reads (C : BinaryCircuit) (G : Finset ℕ)
    (hG : G ⊆ Finset.range C.size) (w : ℕ) :
    readsIn (binarySkeleton C) G w = binaryReadsIn C G w := by
  exact shadow_binary_reads C G hG w

lemma skeleton_tree_to_binary {N : ℕ} (C : BinaryCircuit) (S E : Finset ℕ)
    (htree : IsTree N (binarySkeleton C) S E) : BinaryIsTree N C S E := by
  obtain ⟨R, cap, hR, hcap, hz, hE, hin, hint⟩ := htree
  have hR' : R ⊆ Finset.range C.size := by simpa only [binarySkeleton_size] using hR
  have hr : readsIn (binarySkeleton C) R = binaryReadsIn C R :=
    funext (skeleton_binary_reads C R hR')
  have hall : readsIn (binarySkeleton C) (Finset.range (binarySkeleton C).size) =
      binaryReadsIn C (Finset.range C.size) := by
    rw [binarySkeleton_size]
    exact funext (skeleton_binary_reads C _ (Finset.Subset.refl _))
  refine ⟨R, cap, hR', hcap, ?_, ?_, ?_, ?_⟩
  · simpa only [hr] using hz
  · simpa only [hr] using hE
  · intro j hj
    have hjlt : j < C.gates.length := Finset.mem_range.mp (hR' hj)
    have hji := hin j hj
    rw [binarySkeleton_gate C j hjlt] at hji
    rw [binaryInputs_at C j hjlt]
    exact hji.2
  · simpa only [hr, hall, show (binarySkeleton C).output = C.output from rfl] using hint

lemma skeleton_back_to_binary {N : ℕ} (C : BinaryCircuit)
    (hback : ReadsBack N (binarySkeleton C)) : BinaryReadsBack N C := by
  intro j hj w hw
  apply hback j (by simpa only [binarySkeleton, List.length_map] using hj) w
  rw [binarySkeleton_gate C j hj]
  simpa only [binaryInputs_at C j hj] using hw

end PEqualNP.Outside.L_meta_25875.CircuitAnalysis

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset
abbrev I (k : ℕ) := Fin (2^k)

def dot {k : ℕ} (u v : I k) : Bool :=
  let bits := fun (z : I k) => (univ : Finset (Fin k)).filter (fun i => z.val.testBit i.val)
  ((bits u ∩ bits v).card % 2 == 1)

def table {k : ℕ} (rf cf : I k → Bool) (u v : I k) := (dot u v != rf u) != cf v

def err {I : Type} [DecidableEq I] (A F : I → I → Bool) (B : Finset I) (r : I) :=
  B.filter (fun j => A r j ≠ F r j)

def misses {I : Type} [DecidableEq I] (B T : Finset I) (A : I → I → Bool)
    (H : I → Bool) (a b : I) (p q : Bool) : Prop :=
  ∀ j ∈ B, j ∉ T → ¬ (xor (A a j) (H j) = p ∧ xor (A b j) (H j) = q)

def color (r s p q : Bool) := xor (xor r s) (xor p q)

lemma four_bound {k e : ℕ} (hk : 3 ≤ k) (rf cf H : I k → Bool) (A : I k → I k → Bool)
    (B T U : Finset (I k)) (a b c d : I k)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (p q s t : Bool) (m1 : misses B T A H a b p q) (m2 : misses B U A H c d s t)
    (ha : (err A (table rf cf) B a).card ≤ e) (hb : (err A (table rf cf) B b).card ≤ e)
    (hc : (err A (table rf cf) B c).card ≤ e) (hd : (err A (table rf cf) B d).card ≤ e)
    (hbudget : 2^k - B.card + T.card + U.card + 4*e < 2^(k-3)) :
    color (rf a) (rf b) p q ≠ color (rf c) (rf d) s t := by
  let tweak := fun i : I k => if i = a then !p else if i = b then q else if i = c then !s else t
  let rf' := fun i => xor (rf i) (tweak i)
  let G := table rf' cf
  let X := univ.filter (fun j => G a j ≠ G b j ∧ G a j ≠ G c j ∧ G a j = G d j)
  let D := err A (table rf cf) B
  let Z := Bᶜ ∪ T ∪ U ∪ D a ∪ D b ∪ D c ∪ D d
  have htweak : tweak a = !p ∧ tweak b = q ∧ tweak c = !s ∧ tweak d = t := by
    simp [tweak, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  have hG (i j : I k) : G i j = xor (table rf cf i j) (tweak i) := by
    simp only [G, table, rf']
    generalize dot i j = x, rf i = y, cf j = z, tweak i = u
    revert x y z u; decide
  have logic : ∀ x y z w h p' q' s' t' : Bool,
      xor x (!p') ≠ xor y q' → xor x (!p') ≠ xor z (!s') → xor x (!p') = xor w t' →
      (xor x h = p' ∧ xor y h = q') ∨ (xor z h = s' ∧ xor w h = t') := by
    intro x; cases x <;> intro y <;> cases y <;> decide +kernel
  have sub : X ⊆ Z := by
    intro j hj
    by_contra hn
    simp only [Z, mem_union, mem_compl, not_or, not_not] at hn
    obtain ⟨⟨⟨⟨⟨⟨hjB,hjT⟩,hjU⟩,hja⟩,hjb⟩,hjc⟩,hjd⟩ := hn
    have eqv (i : I k) (hi : j ∉ D i) : table rf cf i j = A i j := by
      by_contra h
      exact hi (mem_filter.mpr ⟨hjB,Ne.symm h⟩)
    have hh := (mem_filter.mp hj).2
    simp only [hG, eqv a hja,eqv b hjb,eqv c hjc,eqv d hjd,htweak.1,htweak.2.1,
      htweak.2.2.1,htweak.2.2.2] at hh
    rcases logic _ _ _ _ (H j) _ _ _ _ hh.1 hh.2.1 hh.2.2 with h | h
    · exact m1 j hjB hjT h
    · exact m2 j hjB hjU h
  have hcZ : Z.card ≤ 2^k - B.card + T.card + U.card + 4*e := by
    have h0 := card_union_le Bᶜ T
    have h1 := card_union_le (Bᶜ ∪ T) U
    have h2 := card_union_le (Bᶜ ∪ T ∪ U) (D a)
    have h3 := card_union_le (Bᶜ ∪ T ∪ U ∪ D a) (D b)
    have h4 := card_union_le (Bᶜ ∪ T ∪ U ∪ D a ∪ D b) (D c)
    have h5 := card_union_le (Bᶜ ∪ T ∪ U ∪ D a ∪ D b ∪ D c) (D d)
    simp only [card_compl,Fintype.card_fin] at h0
    change (D a).card ≤ e at ha
    change (D b).card ≤ e at hb
    change (D c).card ≤ e at hc
    change (D d).card ≤ e at hd
    dsimp only [Z]; omega
  have sm := (card_le_card sub).trans_lt (hcZ.trans_lt hbudget)
  have calcX := PEqualNP.Outside.L_meta_25875.Fibers.enumeration k rf' cf hk a b c d hab hac had hbc hbd hcd
  change X.card = (if _ then (if (rf' a != rf' b) = (rf' c != rf' d) then _ else _) else _) at calcX
  have opp : (rf' a != rf' b) ≠ (rf' c != rf' d) := by
    intro h
    rw [if_pos h] at calcX
    have hp : (2:ℕ)^(k-3) ≤ 2^(k-2) := Nat.pow_le_pow_right (by decide) (by omega)
    split at calcX
    · exact (Nat.not_lt_of_ge hp) (calcX ▸ sm)
    · exact (Nat.lt_irrefl _) (calcX ▸ sm)
  simp only [rf',htweak.1,htweak.2.1,htweak.2.2.1,htweak.2.2.2] at opp
  have law : ∀ i j l m p q s t : Bool, (xor i (!p) != xor j q) ≠ (xor l (!s) != xor m t) →
      color i j p q ≠ color l m s t := by decide
  exact law _ _ _ _ _ _ _ _ opp

end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis

lemma robust_three {k e : ℕ} (hk : 3 ≤ k) (rf cf : I k → Bool) (A : I k → I k → Bool)
    (B T : Finset (I k)) (a b c : I k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p q : Bool) (ha : (err A (table rf cf) B a).card ≤ e)
    (hb : (err A (table rf cf) B b).card ≤ e) (hc : (err A (table rf cf) B c).card ≤ e)
    (budget : 2^k-B.card + T.card + 3*e < 2^(k-3)) :
    ∃ j ∈ B, j ∉ T ∧ xor (A a j) (A b j) = p ∧ xor (A a j) (A c j) = q := by
  have hn : 8 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  let S : Finset (I k) := {a,b,c}
  have hs : S.card = 3 := by simp [S,hab,hac,hbc]
  have hex : S.card < (univ : Finset (I k)).card := by simpa [hs] using (show 3 < 2^k by omega)
  obtain ⟨d,hd⟩ := sdiff_nonempty_of_card_lt_card hex
  have hd' := (mem_sdiff.mp hd).2
  simp only [S,mem_insert,mem_singleton,not_or] at hd'
  let r1 := xor (rf b) (!p)
  let r2 := xor (rf c) (!q)
  let rf' := fun i => if i = a then rf a else if i = b then r1 else if i = c then r2
    else xor (xor (rf a) r1) r2
  have hrf : rf' a = rf a ∧ rf' b = r1 ∧ rf' c = r2 ∧ rf' d = xor (xor (rf a) r1) r2 := by
    simp [rf',Ne.symm hab,Ne.symm hac,Ne.symm hbc,hd'.1,hd'.2.1,hd'.2.2]
  let G := table rf' cf
  let X := univ.filter (fun j => G a j ≠ G b j ∧ G a j ≠ G c j ∧ G a j = G d j)
  have hpar : (rf' a != rf' b) = (rf' c != rf' d) := by
    rw [hrf.1,hrf.2.1,hrf.2.2.1,hrf.2.2.2]
    generalize rf a = x, r1 = y, r2 = z
    revert x y z; decide
  have calcX := PEqualNP.Outside.L_meta_25875.Fibers.enumeration k rf' cf hk a b c d hab hac (Ne.symm hd'.1) hbc (Ne.symm hd'.2.1) (Ne.symm hd'.2.2)
  change X.card = (if _ then (if (rf' a != rf' b) = (rf' c != rf' d) then _ else _) else _) at calcX
  rw [if_pos hpar] at calcX
  have lb : 2^(k-3) ≤ X.card := by
    rw [calcX]; split
    · exact Nat.pow_le_pow_right (by decide) (by omega)
    · rfl
  let D := err A (table rf cf) B
  let Z := Bᶜ ∪ T ∪ D a ∪ D b ∪ D c
  have hcZ : Z.card < X.card := by
    have h0 := card_union_le Bᶜ T
    have h1 := card_union_le (Bᶜ ∪ T) (D a)
    have h2 := card_union_le (Bᶜ ∪ T ∪ D a) (D b)
    have h3 := card_union_le (Bᶜ ∪ T ∪ D a ∪ D b) (D c)
    simp only [card_compl,Fintype.card_fin] at h0
    change (D a).card ≤ e at ha
    change (D b).card ≤ e at hb
    change (D c).card ≤ e at hc
    dsimp only [Z]; omega
  obtain ⟨j,hj⟩ := sdiff_nonempty_of_card_lt_card hcZ
  obtain ⟨hx,hz⟩ := mem_sdiff.mp hj
  simp only [Z,mem_union,mem_compl,not_or,not_not] at hz
  obtain ⟨⟨⟨⟨hjB,hjT⟩,hja⟩,hjb⟩,hjc⟩ := hz
  have eqv (i : I k) (hi : j ∉ D i) : A i j = table rf cf i j := by
    by_contra h
    exact hi (mem_filter.mpr ⟨hjB,h⟩)
  refine ⟨j,hjB,hjT,?_⟩
  rw [eqv a hja,eqv b hjb,eqv c hjc]
  have h := (mem_filter.mp hx).2
  simp only [G, table,hrf.1,hrf.2.1,hrf.2.2.1,r1,r2] at h
  simp only [table]
  have bit : ∀ x y u v w p : Bool,
      ((x != v) != u) ≠ ((y != xor w (!p)) != u) → xor ((x != v) != u) ((y != w) != u) = p := by
    decide +kernel
  exact ⟨bit _ _ _ _ _ _ h.1, bit _ _ _ _ _ _ h.2.1⟩

lemma factored_cap {k e : ℕ} (hk : 3 ≤ k) (rf cf : I k → Bool) (A : I k → I k → Bool)
    (B T names : Finset (I k)) (hT : T.card ≤ 4)
    (budget : 5 + (2^k-B.card) + 4*e ≤ 2^(k-3))
    (he : ∀ a ∈ names, (err A (table rf cf) B a).card ≤ e)
    (t : I k → Bool) (q : I k → Bool → Bool) (U : I k → Bool → Bool)
    (hf : ∀ a ∈ names, ∀ j ∈ B, j ∉ T → A a j = U j (q a (t j))) :
    names.card ≤ 2 := by
  by_contra! h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp h
  obtain ⟨p,r,_,hm⟩ := one_boundary_missing (q a) (q b) (q c)
  obtain ⟨j,hj,ht,hp,hr⟩ := robust_three hk rf cf A B T a b c hab hac hbc p r
    (he a ha) (he b hb) (he c hc) (by omega)
  apply hm (t j) (U j)
  rw [Bool.xor_comm, hf a ha j hj ht,hf b hb j hj ht] at hp
  rw [Bool.xor_comm, hf a ha j hj ht,hf c hc j hj ht] at hr
  exact ⟨hp,hr⟩

end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis

lemma pair_charge {k e : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (hk : 3 ≤ k) (rf cf H : I k → Bool) (A : I k → I k → Bool)
    (B R : Finset (I k)) (S : J → Finset (I k)) (hsub : ∀ i, S i ⊆ R)
    (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (he : ∀ a ∈ R, (err A (table rf cf) B a).card ≤ e)
    (budget : 5+(2^k-B.card)+4*e ≤ 2^(k-3))
    (miss : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a ≠ b →
      ∃ p q T, T.card ≤ 2 ∧ misses B T A H a b p q) :
    (univ.filter (fun i => (S i).card = 2)).card ≤ 2 := by
  classical
  let K := univ.filter (fun i => (S i).card = 2)
  obtain ⟨a,b,hA,hB,hAB,mems⟩ := Selection.choose_disjoint_pairs
    (fun i : K => S i.val) (fun i => (mem_filter.mp i.property).2)
    (fun i j hij => hd _ _ (fun eq => hij (Subtype.ext eq)))
  choose p q T ht hm using fun i : K => miss i (a i) (mems i).1 (b i) (mems i).2.1 (mems i).2.2
  let f := fun i : K => color (rf (a i)) (rf (b i)) (p i) (q i)
  have inj : Function.Injective f := by
    intro i j eq
    by_contra hij
    exact four_bound hk rf cf H A B (T i) (T j) (a i) (b i) (a j) (b j)
      (mems i).2.2 (fun h => hij (hA h)) (hAB i j) (Ne.symm (hAB j i))
      (fun h => hij (hB h)) (mems j).2.2 _ _ _ _ (hm i) (hm j)
      (he _ (hsub i (mems i).1)) (he _ (hsub i (mems i).2.1))
      (he _ (hsub j (mems j).1)) (he _ (hsub j (mems j).2.1))
      (by have := ht i; have := ht j; omega) eq
  simpa only [Fintype.card_coe,Fintype.card_bool] using Fintype.card_le_of_injective f inj

lemma absent_charge {k e : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (hk : 3 ≤ k) (rf cf H : I k → Bool) (A : I k → I k → Bool)
    (B R : Finset (I k)) (S : J → Finset (I k)) (hsub : ∀ i, S i ⊆ R)
    (he : ∀ a ∈ R, (err A (table rf cf) B a).card ≤ e)
    (budget : 5+(2^k-B.card)+4*e ≤ 2^(k-3))
    (miss : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a ≠ b →
      ∃ p q T, T.card ≤ 2 ∧ misses B T A H a b p q)
    (u : I k) (hu : u ∈ R) (hpriv : ∀ i, u ∉ S i) (hblank : ∀ j ∈ B, A u j = H j) :
    (univ.filter (fun i => (S i).card = 2)).card = 0 := by
  rw [card_eq_zero,filter_eq_empty_iff]
  intro i _ h
  obtain ⟨a,b,hab,hS⟩ := card_eq_two.mp h
  have ha : a ∈ S i := hS ▸ mem_insert_self ..
  have hb : b ∈ S i := hS ▸ mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨p,q,T,hT,hm⟩ := miss i a ha b hb hab
  obtain ⟨j,hjB,hjT,hp,hq⟩ := robust_three hk rf cf A B T u a b
    (fun eq => hpriv i (eq ▸ ha)) (fun eq => hpriv i (eq ▸ hb)) hab p q (he u hu)
    (he a (hsub i ha)) (he b (hsub i hb)) (by omega)
  apply hm j hjB hjT
  rw [Bool.xor_comm,hblank j hjB] at hp hq
  exact ⟨hp,hq⟩

lemma bank_arithmetic (r c used excess b pieces good sn sg marks pr pc ur uc : ℕ)
    (hr : ur ≤ 1) (hc : uc ≤ 1) (hpr : pr ≤ 2) (hpc : pc ≤ 2)
    (hpr0 : 0 < ur → pr = 0) (hpc0 : 0 < uc → pc = 0)
    (hread : used + excess ≤ b+1)
    (covered : r+c ≤ ur+uc+used)
    (hparts : r+c ≤ ur+uc+good+sn)
    (hshare : sn+sg ≤ excess) (hmarks : marks ≤ excess+sn+sg)
    (hpieces : pieces ≤ 2*marks+sg+1) (hleaf : good ≤ 2*pieces+pr+pc) :
    11*(r+c) ≤ 10*b+34 := by omega

end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Semantics

def bank {n : ℕ} (S : Finset ℕ) (R : Finset (Fin n)) (f : Fin n → ℕ) :=
  R.filter (fun a => f a ∈ S)

lemma bank_image {n : ℕ} (S : Finset ℕ) (R : Finset (Fin n)) (f : Fin n → ℕ) :
    (bank S R f).image f = S.filter (fun w => w ∈ R.image f) := by
  ext w
  simp only [bank,mem_image,mem_filter]
  constructor
  · rintro ⟨a,⟨ha,hw⟩,rfl⟩; exact ⟨hw,a,ha,rfl⟩
  · rintro ⟨hw,a,ha,rfl⟩; exact ⟨a,⟨ha,hw⟩,rfl⟩

lemma bank_card {n : ℕ} (t : BTree) (R : Finset (Fin n)) (f : Fin n → ℕ)
    (hi : Function.Injective f) :
    (bank t.privs R f).card = t.bankCount (fun w => w ∈ R.image f) := by
  rw [← card_image_of_injective _ hi,bank_image]; rfl

abbrev row {n : ℕ} : Fin n → ℕ := Fin.val
abbrev col {n : ℕ} : Fin n → ℕ := fun a => n+a.val
lemma col_inj {n : ℕ} : Function.Injective (col (n:=n)) := by
  intro x y h; exact Fin.ext (Nat.add_left_cancel h)

def observed {n : ℕ} (C : BinaryCircuit) (o : Bool → Bool) (a b : Fin n) :=
  o (C.eval (PEqualNP.Represents.oneEach a b))

lemma table_trans {k : ℕ} (rf cf : I k → Bool) (a b : I k) :
    table cf rf b a = table rf cf a b := by
  have h : dot b a = dot a b := by simp only [dot,inter_comm]
  simp only [table,h]; generalize dot a b = x, rf a = y, cf b = z; revert x y z; decide

structure Data (k : ℕ) where
  R : Finset (I k)
  B : Finset (I k)
  rf : I k → Bool
  cf : I k → Bool
  er : ℕ
  ec : ℕ
  hk : 3 ≤ k
  br : 5+(2^k-B.card)+4*er ≤ 2^(k-3)
  bc : 5+(2^k-R.card)+4*ec ≤ 2^(k-3)

structure Good {k : ℕ} (d : Data k) (A : I k → I k → Bool) : Prop where
  rowE : ∀ a ∈ d.R, (err A (table d.rf d.cf) d.B a).card ≤ d.er
  colE : ∀ b ∈ d.B, (err (fun b a => A a b) (table d.cf d.rf) d.R b).card ≤ d.ec

def Fact {n : ℕ} (names allowed avoid : Finset (Fin n))
    (A : Fin n → Fin n → Bool) (H : Fin n → Bool) : Prop :=
  ∃ (t : Fin n → Bool) (q0 : Bool → Bool) (q : Fin n → Bool → Bool) (U : Fin n → Bool → Bool),
    (∀ j ∈ allowed, j ∉ avoid → H j = U j (q0 (t j))) ∧
    ∀ a ∈ names, ∀ j ∈ allowed, j ∉ avoid → A a j = U j (q a (t j))

lemma factors {k : ℕ} (d : Data k) (C : BinaryCircuit) (o : Bool → Bool) (S E : Finset ℕ)
    (tree : BinaryIsTree (2*2^k) C S E) (back : BinaryReadsBack (2*2^k) C)
    (raw : S ⊆ range (2*2^k)) (mark : E.card ≤ 1) :
    Fact (bank S d.R row) d.B (bank S d.B col) (observed C o) (fun j => o (C.eval (blankLeft j))) ∧
    Fact (bank S d.B col) d.R (bank S d.R row) (fun b a => observed C o a b)
      (fun a => o (C.eval (blankRight a))) := by
  constructor
  · obtain ⟨t,q0,q,U,h0,h⟩ := binary_tree_row_factor C S E tree back raw mark o
    refine ⟨t,q0,q,U,fun j hj hn => h0 j (fun hw => hn (mem_filter.mpr ⟨hj,hw⟩)),?_⟩
    intro a ha j hj hn
    exact h a (mem_filter.mp ha).2 j (fun hw => hn (mem_filter.mpr ⟨hj,hw⟩))
  · obtain ⟨t,q0,q,U,h0,h⟩ := binary_tree_col_factor C S E tree back raw mark o
    refine ⟨t,q0,q,U,fun j hj hn => h0 j (fun hw => hn (mem_filter.mpr ⟨hj,hw⟩)),?_⟩
    intro a ha j hj hn
    exact h a (mem_filter.mp ha).2 j (fun hw => hn (mem_filter.mpr ⟨hj,hw⟩))

lemma caps {k : ℕ} (d : Data k) (C : BinaryCircuit) (o : Bool → Bool)
    (ok : Good d (observed C o)) (back : ReadsBack (2*2^k) (binarySkeleton C))
    (hout : (binarySkeleton C).output+1 = 2*2^k+(binarySkeleton C).size)
    (t : BTree) (ht : GoodTree (2*2^k) (binarySkeleton C) t) (hm : t.marks ≤ 1)
    (hraw : t.privs ⊆ range (2*2^k)) :
    (bank t.privs d.R row).card ≤ 2 ∧ (bank t.privs d.B col).card ≤ 2 := by
  rw [bank_card _ _ _ Fin.val_injective,bank_card _ _ _ col_inj]
  by_contra hn
  obtain ⟨u,hgu,hmu,hsub,hbig,hr,hc⟩ := BTree.good_small_violating_subtree
    (fun w => w ∈ d.R.image row) (fun w => w ∈ d.B.image col) t ht hm (by
      rcases not_and_or.mp hn with h | h
      · exact Or.inl (Nat.lt_of_not_ge h)
      · exact Or.inr (Nat.lt_of_not_ge h))
  have ne : u.privs.Nonempty := by
    by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    simp [BTree.bankCount,he] at hbig
  obtain ⟨E,m,tr⟩ := one_mark_good_isTree back hout hgu hmu ne
  obtain ⟨fr,fc⟩ := factors d C o u.privs E (skeleton_tree_to_binary C _ _ tr)
    (skeleton_back_to_binary C back) (hsub.trans hraw) m
  rw [← bank_card u d.R row Fin.val_injective] at hr hbig
  rw [← bank_card u d.B col col_inj] at hc hbig
  obtain ⟨t1,_,q1,U1,_,hf1⟩ := fr
  obtain ⟨t2,_,q2,U2,_,hf2⟩ := fc
  have h1 := factored_cap d.hk d.rf d.cf _ _ _ _ hc d.br
    (fun a ha => ok.rowE a (mem_filter.mp ha).1) t1 q1 U1 hf1
  have h2 := factored_cap d.hk d.cf d.rf _ _ _ _ hr d.bc
    (fun a ha => ok.colE a (mem_filter.mp ha).1) t2 q2 U2 hf2
  exact hbig.elim (Nat.not_lt_of_ge h1) (Nat.not_lt_of_ge h2)

lemma fact_misses {n : ℕ} {names allowed avoid : Finset (Fin n)} {A : Fin n → Fin n → Bool}
    {H : Fin n → Bool} (h : Fact names allowed avoid A H) {a b : Fin n} (ha : a ∈ names)
    (hb : b ∈ names) : ∃ p q, misses allowed avoid A H a b p q := by
  obtain ⟨t,q0,v,U,h0,hv⟩ := h
  obtain ⟨p,q,_,hm⟩ := one_boundary_missing q0 (v a) (v b)
  refine ⟨p,q,?_⟩
  intro j hj ht; rw [hv a ha j hj ht,hv b hb j hj ht,h0 j hj ht]
  exact hm (t j) (U j)

end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_25875.CircuitAnalysis

open PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Semantics

lemma large_bank {k e : ℕ} {B : Finset (I k)} (h : 5 + (2^k-B.card)+4*e ≤ 2^(k-3)) :
    5 ≤ B.card := by
  have hp : (2:ℕ)^(k-3) ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
  omega

lemma separates {k e : ℕ} (hk : 3 ≤ k) (rf cf : I k → Bool) (A : I k → I k → Bool)
    (B R : Finset (I k)) (hr : 3 ≤ R.card)
    (budget : 5+(2^k-B.card)+4*e ≤ 2^(k-3))
    (he : ∀ a ∈ R, (err A (table rf cf) B a).card ≤ e)
    (a b : I k) (ha : a ∈ R) (hb : b ∈ R) (hab : a ≠ b) :
    ∃ j ∈ B, A a j ≠ A b j := by
  have hlt : ({a,b} : Finset _).card < R.card := by simp [hab]; omega
  obtain ⟨c,hc⟩ := sdiff_nonempty_of_card_lt_card hlt
  obtain ⟨hc,hn⟩ := mem_sdiff.mp hc
  simp only [mem_insert,mem_singleton,not_or] at hn
  obtain ⟨j,hj,_,hd,_⟩ := robust_three hk rf cf A B ∅ a b c hab (Ne.symm hn.1) (Ne.symm hn.2)
    true false (he a ha) (he b hb) (he c hc) (by simp; omega)
  exact ⟨j,hj,fun eq => by simp [eq] at hd⟩

lemma unused_small {k : ℕ} (A : I k → I k → Bool) (R B : Finset (I k)) (W : Finset (I k))
    (H : I k → Bool) (hW : W ⊆ R) (hblank : ∀ a ∈ W, ∀ j ∈ B, A a j = H j)
    (sep : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ∃ j ∈ B, A a j ≠ A b j) : W.card ≤ 1 := by
  by_contra! hc
  obtain ⟨a,b,ha,hb,hn⟩ := one_lt_card_iff.mp hc
  obtain ⟨j,hj,h⟩ := sep _ (hW ha) _ (hW hb) hn
  exact h ((hblank _ ha _ hj).trans (hblank _ hb _ hj).symm)

lemma blank_row {n : ℕ} (C : BinaryCircuit) (o : Bool → Bool) (ho : n+n ≤ C.output)
    (a j : Fin n) (h : BinarySupport.reads C (row a) = 0) :
    observed C o a j = o (C.eval (blankLeft j)) := by
  apply congrArg o
  apply BinarySupport.eval_congr (n+n) C _ _ (BinarySupport.oneEach_length _ _) (by simp [blankLeft]) ho
  intro i _ hi
  apply Causal.oneHot_left_blank
  intro eq; subst i; exact (Nat.ne_of_gt hi) h

lemma blank_col {n : ℕ} (C : BinaryCircuit) (o : Bool → Bool) (ho : n+n ≤ C.output)
    (b j : Fin n) (h : BinarySupport.reads C (col b) = 0) :
    observed C o j b = o (C.eval (blankRight j)) := by
  apply congrArg o
  apply BinarySupport.eval_congr (n+n) C _ _ (BinarySupport.oneEach_length _ _) (by simp [blankRight]) ho
  intro i _ hi
  apply Causal.oneHot_right_blank (n:=n) _ (by simp)
  intro eq; subst i
  exact (Nat.ne_of_gt hi) h

lemma nonzero {k : ℕ} (d : Data k) (C : BinaryCircuit) (o : Bool → Bool)
    (ok : Good d (observed C o)) : 0 < C.size := by
  by_contra! hz
  have hem : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hz)
  let W := d.R.filter (fun a => row a ≠ C.output)
  have bw (a : I k) (ha : a ∈ W) (j : I k) :
      observed C o a j = o (C.eval (blankLeft j)) := by
    apply congrArg o
    simp only [BinaryCircuit.eval,BinaryCircuit.wires,hem,List.foldl_nil]
    exact Causal.oneHot_left_blank _ _ _ (Ne.symm (mem_filter.mp ha).2)
  have sw := unused_small (observed C o) d.R d.B W _ (filter_subset ..) (fun a ha j _ => bw a ha j)
    (fun a ha b hb hab => separates d.hk d.rf d.cf _ d.B d.R (by have := large_bank d.bc; omega)
      d.br ok.rowE a b ha hb hab)
  let V := d.R.filter (fun a => row a = C.output)
  have sv : V.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    exact Fin.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  have partition := card_filter_add_card_filter_not (s:=d.R) (fun a => row a = C.output)
  change V.card + W.card = d.R.card at partition
  have := large_bank d.bc
  omega

end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset PEqualNP.Outside.L_meta_25875.CircuitAnalysis

def rawBank {n : ℕ} (A B : Finset (Fin n)) := A.image row ∪ B.image col
lemma raw_card {n : ℕ} (A B : Finset (Fin n)) : (rawBank A B).card = A.card+B.card := by
  have disj : Disjoint (A.image row) (B.image col) := by
    apply disjoint_left.mpr
    intro w hw hw'
    obtain ⟨a,_,rfl⟩ := mem_image.mp hw
    obtain ⟨b,_,eq⟩ := mem_image.mp hw'
    have h := a.isLt
    change n+b.val=a.val at eq
    omega
  rw [rawBank,card_union_of_disjoint disj,card_image_of_injective _ Fin.val_injective,
    card_image_of_injective _ col_inj]

lemma cover_counts {n : ℕ} (R B : Finset (Fin n)) (r : ℕ → ℕ) {J : Type}
    [Fintype J] [DecidableEq J] (S : J → Finset ℕ)
    (cover : ∀ w < n+n, r w = 1 → ∃ i, w ∈ S i) :
    let U := R.filter (fun a => r (row a) = 0)
    let V := B.filter (fun a => r (col a) = 0)
    let used := ((range (n+n)).filter (fun w => 1 ≤ r w)).card
    let shared := ((range (n+n)).filter (fun w => 2 ≤ r w)).card
    R.card+B.card ≤ U.card+V.card+used ∧
    R.card+B.card ≤ U.card+V.card + (∑ i, ((bank (S i) R row).card+(bank (S i) B col).card)) +shared := by
  classical
  intro U V used shared
  let T := rawBank R B
  let Z := rawBank U V
  let P := (range (n+n)).filter (fun w => 1 ≤ r w)
  let Q := (range (n+n)).filter (fun w => 2 ≤ r w)
  let M := fun i => rawBank (bank (S i) R row) (bank (S i) B col)
  have small (w) (h : w ∈ T) : w < n+n := by
    rcases mem_union.mp h with h | h
    · obtain ⟨a,_,rfl⟩ := mem_image.mp h; have := a.isLt; dsimp [row]; omega
    · obtain ⟨b,_,rfl⟩ := mem_image.mp h; have := b.isLt; dsimp [col]; omega
  have zero (w) (h : w ∈ T) (h0 : r w = 0) : w ∈ Z := by
    rcases mem_union.mp h with h | h
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨ha,h0⟩))
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨hb,h0⟩))
  have once (w) (h : w ∈ T) (h1 : r w = 1) : w ∈ univ.biUnion M := by
    obtain ⟨i,hi⟩ := cover w (small w h) h1
    apply mem_biUnion.mpr; refine ⟨i,mem_univ _,?_⟩
    rcases mem_union.mp h with h | h
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨ha,hi⟩))
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨hb,hi⟩))
  have s1 : T ⊆ Z ∪ P := by
    intro w h
    by_cases h0 : r w = 0
    · exact mem_union_left _ (zero w h h0)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (small w h),by omega⟩)
  have s2 : T ⊆ Z ∪ univ.biUnion M ∪ Q := by
    intro w h
    by_cases h0 : r w = 0
    · exact mem_union_left _ (mem_union_left _ (zero w h h0))
    by_cases h1 : r w = 1
    · exact mem_union_left _ (mem_union_right _ (once w h h1))
    exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (small w h),by omega⟩)
  have b1 := (card_le_card s1).trans (card_union_le Z P)
  have b2 := (card_le_card s2).trans (card_union_le _ Q)
  have b3 := card_union_le Z (univ.biUnion M)
  have b4 : (univ.biUnion M).card ≤ ∑ i, (M i).card := card_biUnion_le
  simp only [M,T,Z,raw_card] at b1 b2 b3 b4
  exact ⟨b1,by change _ ≤ _ + Q.card; omega⟩
end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Semantics
open PEqualNP.Outside.L_meta_25875.CircuitAnalysis.Assembly

lemma charge {k e : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (hk : 3 ≤ k) (rf cf H : I k → Bool) (A : I k → I k → Bool)
    (R B W : Finset (I k)) (S : J → Finset (I k)) (hsub : ∀ i, S i ⊆ R)
    (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (he : ∀ a ∈ R, (err A (table rf cf) B a).card ≤ e)
    (hr : 3 ≤ R.card) (budget : 5+(2^k-B.card)+4*e ≤ 2^(k-3))
    (miss : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a ≠ b →
      ∃ p q T, T.card ≤ 2 ∧ misses B T A H a b p q)
    (sw : W ⊆ R) (fresh : ∀ a ∈ W, ∀ i, a ∉ S i) (hblank : ∀ a ∈ W, ∀ j ∈ B, A a j = H j) :
    let count := (univ.filter (fun i => (S i).card = 2)).card
    W.card ≤ 1 ∧ count ≤ 2 ∧ (0 < W.card → count = 0) := by
  intro count
  refine ⟨unused_small A R B W H sw hblank (fun a ha b hb hn =>
    separates hk rf cf A B R hr budget he a b ha hb hn),
    pair_charge hk rf cf H A B R S hsub hd he budget miss,?_⟩
  intro hx; obtain ⟨u,hu⟩ := card_pos.mp hx
  exact absent_charge hk rf cf H A B R S hsub he budget miss u (sw hu) (fresh u hu) (hblank u hu)

lemma normalized_bound {k : ℕ} (d : Data k) (C : BinaryCircuit) (o : Bool → Bool)
    (ok : Good d (observed C o)) (back : Normalize.Back (2^k+2^k) C.gates)
    (live : Normalize.Live (2^k+2^k) C) : 11*(d.R.card+d.B.card) ≤ 10*C.size+34 := by
  classical
  let N := 2^k+2^k
  let r := BinarySupport.reads C
  have hs := nonzero d C o ok
  have hout : C.output+1 = N+C.size := by
    have hh := Normalize.live_output_last N C live hs
    change C.output = N+(C.size-1) at hh; omega
  have hb := binarySkeleton_back N C back
  have parts := binary_concrete_bad_partition N C hb hs hout
    (fun j hj hl => by rw [reads_eq]; exact BinarySupport.normalize_live_reads N C hs live j hj hl) ∅
  have heq : readsOf (binarySkeleton C) = r := funext (reads_eq C)
  rw [heq] at parts
  dsimp only at parts
  simp only [card_empty,Nat.add_zero,sdiff_empty] at parts
  obtain ⟨L,pieces,props,disj,cov⟩ := parts
  let J := Fin L.length
  let S := fun i : J => (L.get i).privs
  let rr := fun i : J => bank (S i) d.R row
  let cc := fun i : J => bank (S i) d.B col
  let U := d.R.filter (fun a => r (row a) = 0)
  let V := d.B.filter (fun b => r (col b) = 0)
  have prop (i : J) := props (L.get i) (List.get_mem L i)
  have raw (i : J) : S i ⊆ range N := (prop i).2.2.2.1.trans (filter_subset ..)
  have hb' : ReadsBack (2*2^k) (binarySkeleton C) := by simpa only [two_mul, N] using hb
  have hout' : (binarySkeleton C).output+1 = 2*2^k+(binarySkeleton C).size := by
    simpa only [binarySkeleton_output,binarySkeleton_size,two_mul,N] using hout
  have cap (i : J) : (rr i).card ≤ 2 ∧ (cc i).card ≤ 2 := by
    apply caps d C o ok hb' hout' (L.get i) _ (prop i).2.1
    · simpa only [two_mul,N] using raw i
    · simpa only [two_mul,N] using (prop i).1
  have fac (i : J) :
      Fact (rr i) d.B (cc i) (observed C o) (fun j => o (C.eval (blankLeft j))) ∧
      Fact (cc i) d.R (rr i) (fun b a => observed C o a b) (fun j => o (C.eval (blankRight j))) := by
    obtain ⟨E,m,tr⟩ := (prop i).2.2.2.2
    apply factors d C o (S i) E _ (skeleton_back_to_binary C hb') _ m
    · apply skeleton_tree_to_binary; simpa only [two_mul,N] using tr
    · simpa only [two_mul,N] using raw i
  have dis (i j : J) (hij : i ≠ j) : Disjoint (S i) (S j) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact disj.rel_get_of_lt h
    · exact (disj.rel_get_of_lt h).symm
  have ho : 2^k+2^k ≤ C.output := by change N ≤ C.output; omega
  have gr := charge d.hk d.rf d.cf (fun j => o (C.eval (blankLeft j))) (observed C o)
    d.R d.B U rr (fun i => filter_subset ..)
    (fun i j hij => disjoint_left.mpr fun a ha hb => disjoint_left.mp (dis i j hij)
      (mem_filter.mp ha).2 (mem_filter.mp hb).2) ok.rowE (by have := large_bank d.bc; omega) d.br
    (fun i a ha b hb _ => by obtain ⟨p,q,h⟩ := fact_misses (fac i).1 ha hb
                             exact ⟨p,q,cc i,(cap i).2,h⟩) (filter_subset ..)
    (fun a ha i hi => by
      have h1 := (mem_filter.mp ((prop i).2.2.2.1 (mem_filter.mp hi).2)).2
      exact (Nat.zero_ne_one ((mem_filter.mp ha).2.symm.trans h1)))
    (fun a ha j _ => blank_row C o ho a j (mem_filter.mp ha).2)
  have gc := charge d.hk d.cf d.rf (fun j => o (C.eval (blankRight j))) (fun b a => observed C o a b)
    d.B d.R V cc (fun i => filter_subset ..)
    (fun i j hij => disjoint_left.mpr fun a ha hb => disjoint_left.mp (dis i j hij)
      (mem_filter.mp ha).2 (mem_filter.mp hb).2) ok.colE (by have := large_bank d.br; omega) d.bc
    (fun i a ha b hb _ => by obtain ⟨p,q,h⟩ := fact_misses (fac i).2 ha hb
                             exact ⟨p,q,rr i,(cap i).1,h⟩) (filter_subset ..)
    (fun a ha i hi => by
      have h1 := (mem_filter.mp ((prop i).2.2.2.1 (mem_filter.mp hi).2)).2
      exact (Nat.zero_ne_one ((mem_filter.mp ha).2.symm.trans h1)))
    (fun b hb j _ => blank_col C o ho b j (mem_filter.mp hb).2)
  have cover (w) (hw : w < N) (h1 : r w = 1) : ∃ i, w ∈ S i := by
    have hmem : w ∈ (range N).filter (fun z => r z = 1) := mem_filter.mpr ⟨mem_range.mpr hw,h1⟩
    rw [← cov] at hmem
    obtain ⟨t,ht,hw'⟩ := mem_biUnion.mp hmem
    obtain ⟨i,hh⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp ht)
    exact ⟨i,by simpa only [S,hh] using hw'⟩
  have counts := cover_counts d.R d.B r S cover
  have total := Selection.two_bank_piece_count (fun i => (rr i).card) (fun i => (cc i).card)
    (fun i => (cap i).1) (fun i => (cap i).2)
  simp only [Fintype.card_subtype,Fintype.card_fin,J] at total
  have marks := PEqualNP.Outside.L_meta_25875.Counting.shared_marked_reads_budget N C.size 0 r
  simp only [Nat.add_zero] at marks
  apply bank_arithmetic _ _ _ _ _ _ _ _ _ _ _ _ _ _ gr.1 gc.1 gr.2.1 gc.2.1 gr.2.2 gc.2.2
    (BinarySupport.normalized_reads_budget N C hs back live).le counts.1 counts.2
    (PEqualNP.Outside.L_meta_25875.Counting.shared_name_gate_budget N C.size r) marks pieces total

end PEqualNP.Outside.L_meta_25875.Retained

namespace PEqualNP.Outside.L_meta_25875.Retained
open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_25875.CircuitAnalysis

lemma no_witness : ¬ (∃ (k er ec : ℕ) (rowFlip colFlip : Fin (2^k) → Bool)
    (R B : Finset (Fin (2^k))) (C : PEqualNP.CircuitLowerBounds.Circuit), 6 ≤ k ∧
  let N := 2 ^ k
  let bits := fun (v : Fin N) =>
    (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
  let dot := fun (u v : Fin N) => ((bits u ∩ bits v).card % 2 == 1)
  let G := fun (u v : Fin N) => (dot u v != rowFlip u) != colFlip v
  let observed := fun (r j : Fin N) => C.eval
    (List.ofFn (fun x : Fin N => decide (x = r)) ++ List.ofFn (fun y : Fin N => decide (y = j)))
  5 + (N-B.card) + 4*er ≤ 2^(k-3) ∧ 5 + (N-R.card) + 4*ec ≤ 2^(k-3) ∧
  (∀ r ∈ R, (B.filter (fun j => observed r j ≠ G r j)).card ≤ er) ∧
  (∀ j ∈ B, (R.filter (fun r => observed r j ≠ G r j)).card ≤ ec) ∧
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    10*(C.gates.countP (fun g => g.inputs.length == 2)) + 34 < 11*(R.card+B.card)) := by
  rintro ⟨k,er,ec,rf,cf,R,B,C,hk,rest⟩
  dsimp only at rest
  obtain ⟨br,bc,hr,hc,legal,strict⟩ := rest
  let d : Data k := ⟨R,B,rf,cf,er,ec,by omega,br,bc⟩
  obtain ⟨D,o,size,back,_,live,_,ev⟩ := Normalize.normalize_live (2^k+2^k) (by positivity) C legal
  have ev' (a b : I k) : C.eval (PEqualNP.Represents.oneEach a b) = observed D o a b :=
    ev _ (BinarySupport.oneEach_length _ _)
  have ok : Good d (observed D o) := by
    constructor
    · intro a ha
      change (B.filter (fun j => observed D o a j ≠ table rf cf a j)).card ≤ er
      simpa only [← ev', PEqualNP.Represents.oneEach,table,dot] using hr a ha
    · intro b hb
      change (R.filter (fun a => observed D o a b ≠ table cf rf b a)).card ≤ ec
      simp only [table_trans rf cf]
      simpa only [← ev',PEqualNP.Represents.oneEach,table,dot] using hc b hb
  have bound := normalized_bound d D o ok back live
  change 11*(R.card+B.card) ≤ 10*D.size+34 at bound
  omega

end PEqualNP.Outside.L_meta_25875.Retained

theorem PEqualNP.Outside.L_meta_25875 : ∀ (k er ec : ℕ) (rowFlip colFlip : Fin (2^k) → Bool)
    (R B : Finset (Fin (2^k))) (C : PEqualNP.CircuitLowerBounds.Circuit), 6 ≤ k →
  let N := 2 ^ k
  let bits := fun (v : Fin N) =>
    (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
  let dot := fun (u v : Fin N) => ((bits u ∩ bits v).card % 2 == 1)
  let G := fun (u v : Fin N) => (dot u v != rowFlip u) != colFlip v
  let observed := fun (r j : Fin N) => C.eval
    (List.ofFn (fun x : Fin N => decide (x = r)) ++ List.ofFn (fun y : Fin N => decide (y = j)))
  5 + (N-B.card) + 4*er ≤ 2^(k-3) → 5 + (N-R.card) + 4*ec ≤ 2^(k-3) →
  (∀ r ∈ R, (B.filter (fun j => observed r j ≠ G r j)).card ≤ er) →
  (∀ j ∈ B, (R.filter (fun r => observed r j ≠ G r j)).card ≤ ec) →
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    11*(R.card+B.card) ≤ 10*(C.gates.countP (fun g => g.inputs.length == 2)) + 34 := by
  intro k er ec rf cf R B C hk
  dsimp only
  intro br bc hr hc legal
  by_contra! strict
  exact PEqualNP.Outside.L_meta_25875.Retained.no_witness ⟨k,er,ec,rf,cf,R,B,C,hk,br,bc,hr,hc,legal,strict⟩
