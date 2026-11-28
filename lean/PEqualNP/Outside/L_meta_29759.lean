import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_29759_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

private lemma zmod_of_bool_pred (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  fin_cases a
  · change b2z (decide ((0 : ZMod 2) ≠ 0)) = 0
    decide
  · change b2z (decide ((1 : ZMod 2) ≠ 0)) = 1
    decide

private lemma zmod2_smul_eq_ite {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (c : ZMod 2) (x : M) : c • x = if c = 1 then x else 0 := by
  by_cases hc : c = 1
  · subst hc
    simp
  · have h0 : c = 0 := by
      fin_cases c
      · rfl
      · exact absurd rfl hc
    subst h0
    simp [hc]

private def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

private def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

private theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

private theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

private theorem foldl_append_head {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

private theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_head
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

private theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_head
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

private theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

private theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

private theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

private theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

private theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

private theorem oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

private theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

private theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

private theorem anchor_zero_row {n m : ℕ} (u : Fin n) (v : Fin m)
    (h : Fin n → Fin m → ZMod 2) (j : Fin m) :
    anchor u v h u j = 0 := by
  simp only [anchor]
  have h1 : h u j + h u v + h u j + h u v = (h u j + h u j) + (h u v + h u v) := by ring
  rw [h1, zmod2_add_self, zmod2_add_self, add_zero]

private theorem anchor_zero_col {n m : ℕ} (u : Fin n) (v : Fin m)
    (h : Fin n → Fin m → ZMod 2) (i : Fin n) :
    anchor u v h i v = 0 := by
  simp only [anchor]
  have h1 : h i v + h i v + h u v + h u v = (h i v + h i v) + (h u v + h u v) := by ring
  rw [h1, zmod2_add_self, zmod2_add_self, add_zero]

private theorem anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [zmod2_add_self]

private theorem anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

private theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]
  ring

private theorem anchor_sum {n m : ℕ} {ι : Type*} (u : Fin n) (v : Fin m)
    (S : Finset ι) (f : ι → Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => ∑ a ∈ S, f a i j) = ∑ a ∈ S, anchor u v (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact anchor_const u v 0
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [anchor_add, ih]

private theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
    (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2) :
    anchor u v (fun i j => (r1 i + s1 j) * (r2 i + s2 j)) =
      Matrix.vecMulVec (fun i => r1 i + r1 u) (fun j => s2 j + s2 v) +
      Matrix.vecMulVec (fun i => r2 i + r2 u) (fun j => s1 j + s1 v) := by
  ext i j
  simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h : ((r1 i + s1 j) * (r2 i + s2 j) + (r1 i + s1 v) * (r2 i + s2 v) +
      (r1 u + s1 j) * (r2 u + s2 j) + (r1 u + s1 v) * (r2 u + s2 v)) +
      ((r1 i + r1 u) * (s2 j + s2 v) + (r2 i + r2 u) * (s1 j + s1 v)) =
      (2 : ZMod 2) * (r1 i * r2 i + r1 u * r2 u + s1 j * s2 j + s1 v * s2 v +
        r1 i * s2 j + r1 i * s2 v + r1 u * s2 j + r1 u * s2 v +
        r2 i * s1 j + r2 i * s1 v + r2 u * s1 j + r2 u * s1 v) := by ring
  rw [zmod2_two, zero_mul] at h
  have hsub : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    intro a b hab
    calc a = a + 0 := (add_zero a).symm
      _ = a + (b + b) := by rw [zmod2_add_self]
      _ = (a + b) + b := by ring
      _ = 0 + b := by rw [hab]
      _ = b := zero_add b
  exact hsub _ _ h

private lemma anchor_table_xor {n m : ℕ} (u : Fin n) (v : Fin m)
    (H G : Fin n → Fin m → Bool) :
    anchor u v (fun i j => b2z (xor (H i j) (G i j))) =
      anchor u v (fun i j => b2z (H i j)) + anchor u v (fun i j => b2z (G i j)) := by
  simp only [b2z_xor, anchor_add]

private lemma anchor_table_encode {n m : ℕ} (u : Fin n) (v : Fin m)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) (hu : ∀ j, A u j = 0)
    (hv : ∀ i, A i v = 0) :
    anchor u v (fun i j => b2z (decide (A i j ≠ 0))) = A := by
  ext i j
  simp only [anchor, zmod_of_bool_pred, hu, hv, add_zero]

private theorem card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

private lemma finrank_range_add_le {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (f g : V →ₗ[F] W) :
    Module.finrank F (LinearMap.range (f + g)) ≤
      Module.finrank F (LinearMap.range f) + Module.finrank F (LinearMap.range g) := by
  have hle : LinearMap.range (f + g) ≤ LinearMap.range f ⊔ LinearMap.range g := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
  omega

private lemma finrank_range_sum_le {F V W ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (S : Finset ι) (f : ι → (V →ₗ[F] W)) :
    Module.finrank F (LinearMap.range (∑ i ∈ S, f i)) ≤
      ∑ i ∈ S, Module.finrank F (LinearMap.range (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, LinearMap.range_zero, finrank_bot]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (finrank_range_add_le (f a) (∑ i ∈ S, f i)).trans (Nat.add_le_add_left ih _)

private lemma matrix_mulVecLin_sum {n m : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ i ∈ S, f i).mulVecLin = ∑ i ∈ S, (f i).mulVecLin := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext x i
    simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    ext x i
    simp

private lemma matrix_rank_sum_le {n m : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ i ∈ S, f i).rank ≤ ∑ i ∈ S, (f i).rank := by
  change Module.finrank (ZMod 2) (LinearMap.range (∑ i ∈ S, f i).mulVecLin) ≤
    ∑ i ∈ S, Module.finrank (ZMod 2) (LinearMap.range (f i).mulVecLin)
  rw [matrix_mulVecLin_sum]
  exact finrank_range_sum_le S (fun i => (f i).mulVecLin)

private lemma rank_two_outer {n m : ℕ} (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2) :
    (Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2).rank ≤ 2 := by
  let P : Matrix (Fin n) (Fin 2) (ZMod 2) := fun i k => if k = 0 then r1 i else r2 i
  let Q : Matrix (Fin 2) (Fin m) (ZMod 2) := fun k j => if k = 0 then s1 j else s2 j
  have hPQ : Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2 = P * Q := by
    ext i j
    rw [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_two]
    change r1 i * s1 j + r2 i * s2 j =
      (if (0 : Fin 2) = 0 then r1 i else r2 i) * (if (0 : Fin 2) = 0 then s1 j else s2 j) +
      (if (1 : Fin 2) = 0 then r1 i else r2 i) * (if (1 : Fin 2) = 0 then s1 j else s2 j)
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp [h10]
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (Fin 2 → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card (Fin 2) := Module.finrank_pi (ZMod 2)
    _ = 2 := Fintype.card_fin 2

private theorem circuit_decomp {n m q : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (s : ℕ)
    (C : Circuit) (tap : Fin q → ℕ)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hcnt : C.gates.countP nlGate ≤ s)
    (htap : ∀ j : Fin q, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates, tap j⟩) :
    ∃ (pieces : Fin s → Matrix (Fin n) (Fin m) (ZMod 2))
      (mask : Fin q → Finset (Fin s)),
      (∀ r : Fin s, (pieces r).rank ≤ 2 ∧ (∀ j, pieces r u j = 0) ∧ (∀ i, pieces r i v = 0)) ∧
      (∀ j : Fin q, anchor u v (fun i l => b2z (G j i l)) = ∑ r ∈ mask j, pieces r) := by
  classical
  let val : ℕ → Fin n → Fin m → ZMod 2 :=
    fun k i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
  let dep : ℕ → ℕ := fun k => (depthsOf (n + m) C.gates).getD k 0
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ (C.gates[idx]).inputs, a < n + m + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (i : Fin n) (j : Fin m),
      val (n + m + idx) i j =
        b2z ((C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
          (wiresOf (oneEach i j) C.gates).getD a false)) := by
    intro idx hidx i j
    unfold val
    have h := wiresOf_getD_gate (oneEach i j) C.gates hidx (by
      intro a ha
      rw [oneEach_length]
      exact hrb' idx hidx a ha)
    rw [oneEach_length] at h
    rw [h]
  have hdep_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      dep (n + m + idx) =
        ((C.gates[idx]).inputs.map (fun a => dep a)).foldr max 0 +
          (nlGate (C.gates[idx])).toNat := by
    intro idx hidx
    exact depthsOf_getD_gate (n + m) C.gates hidx (hrb' idx hidx)
  have hsplit_zero : ∀ k : ℕ, dep k = 0 →
      ∃ (r : Fin n → ZMod 2) (s' : Fin m → ZMod 2), ∀ i j, val k i j = r i + s' j := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hk1 : k < n + m
      · by_cases hk0 : k < n
        · refine ⟨fun i => b2z (decide (k = i.val)), fun _ => 0, fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_left i j hk0, add_zero]
        · refine ⟨fun _ => 0, fun j => b2z (decide (k - n = j.val)), fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_right i j (by omega) hk1, zero_add]
      · by_cases hk2 : k < n + m + C.gates.length
        · let idx := k - (n + m)
          have hidx : idx < C.gates.length := by omega
          have hkeq : k = n + m + idx := by omega
          rw [hkeq] at hdk ⊢
          let g := C.gates[idx]
          have hdg := hdep_gate idx hidx
          change dep (n + m + idx) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
          rw [hdk] at hdg
          have hnl : nlGate g = false := by
            have h0 : (nlGate g).toNat = 0 := by omega
            cases h : nlGate g
            · rfl
            · rw [h] at h0
              simp at h0
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem hidx)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_nil, add_zero]
          | [a] =>
            have ha_lt : a < n + m + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have ha_d : dep a = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun i => c0 + c1 * r1 i, fun j => c1 * s1 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_nil]
            have hanf := anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            change b2z (g.op.eval [_]) = c0 + c1 * val a i j at hanf
            rw [hanf, h1 i j]
            ring
          | [a, b] =>
            have ha_lt : a < n + m + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have hb_lt : b < n + m + idx := hrb' idx hidx b (by rw [hg_in]; simp)
            have hab_d : dep a = 0 ∧ dep b = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) hab_d.1
            obtain ⟨r2, s2, h2⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnl
              rw [hg_in] at hnl
              simpa using hnl
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun i => c0 + c1 * r1 i + c2 * r2 i, fun j => c1 * s1 j + c2 * s2 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
            have hanf := anf_two (fun x y => g.op.eval [x, y])
              ((wiresOf (oneEach i j) C.gates).getD a false)
              ((wiresOf (oneEach i j) C.gates).getD b false)
            rw [hxor] at hanf
            have hbf : b2z false = 0 := rfl
            change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
            rw [hbf, zero_mul, add_zero] at hanf
            rw [hanf, h1 i j, h2 i j]
            ring
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
        · refine ⟨fun _ => 0, fun _ => 0, fun i j => ?_⟩
          unfold val
          have hge : (wiresOf (oneEach i j) C.gates).length ≤ k := by
            rw [wiresOf_length, oneEach_length]
            omega
          rw [List.getD_eq_default _ _ hge]
          simp [b2z]
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate (C.gates[idx.val]) = true ∧ dep (n + m + idx.val) ≤ 1)
  have hNL_card : NL.card ≤ s := by
    calc NL.card
        ≤ (Finset.univ.filter (fun idx : Fin C.gates.length => nlGate (C.gates[idx.val]) = true)).card :=
          Finset.card_le_card (fun idx hidx => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hidx).2.1⟩)
      _ = C.gates.countP nlGate := card_filter_fin_eq_countP C.gates nlGate
      _ ≤ s := hcnt
  have hNL_rank : ∀ idx ∈ NL, (anchor u v (val (n + m + idx.val))).rank ≤ 2 := by
    intro idx hidx_mem
    have hnl : nlGate (C.gates[idx.val]) = true := (Finset.mem_filter.mp hidx_mem).2.1
    have hdg1 : dep (n + m + idx.val) ≤ 1 := (Finset.mem_filter.mp hidx_mem).2.2
    let g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      simpa using hnl.1
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [h] at hlen2; simp at hlen2
      | [_] => rw [h] at hlen2; simp at hlen2
      | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
    have hdg := hdep_gate idx.val idx.isLt
    change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
    rw [hab, hnl] at hdg
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdg
    have hda : dep a = 0 := by omega
    have hdb : dep b = 0 := by omega
    obtain ⟨r1, s1, h1⟩ := hsplit_zero a hda
    obtain ⟨r2, s2, h2⟩ := hsplit_zero b hdb
    have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      exact hnl.2
    let c0 := b2z (g.op.eval [false, false])
    let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
    let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
    have hfun : val (n + m + idx.val) = fun i j =>
        (c0 + c1 * r1 i + c2 * r2 i + (c1 * s1 j + c2 * s2 j)) +
        (r1 i + s1 j) * (r2 i + s2 j) := by
      funext i j
      rw [hval_gate idx.val idx.isLt i j]
      change b2z (g.op.eval (g.inputs.map _)) = _
      rw [hab, List.map_cons, List.map_cons, List.map_nil]
      have hanf := anf_two (fun x y => g.op.eval [x, y])
        ((wiresOf (oneEach i j) C.gates).getD a false)
        ((wiresOf (oneEach i j) C.gates).getD b false)
      rw [hxor] at hanf
      have hbt : b2z true = 1 := rfl
      change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z true * (val a i j * val b i j) at hanf
      rw [hbt, one_mul] at hanf
      rw [hanf, h1 i j, h2 i j]
      ring
    rw [hfun, anchor_add, anchor_split, zero_add, anchor_prod_split]
    exact rank_two_outer _ _ _ _
  have hspan : ∀ k : ℕ, dep k ≤ 1 →
      ∃ coeff : Fin C.gates.length → ZMod 2,
        anchor u v (val k) = ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hdk0 : dep k = 0
      · obtain ⟨r, s', hrs⟩ := hsplit_zero k hdk0
        refine ⟨fun _ => 0, ?_⟩
        have hfun : val k = fun i j => r i + s' j := by funext i j; exact hrs i j
        rw [hfun, anchor_split]
        simp
      · have hk1 : n + m ≤ k := by
          by_contra hlt
          have := depthsOf_getD_input (n + m) C.gates (by omega : k < n + m)
          exact hdk0 this
        have hk2 : k < n + m + C.gates.length := by
          by_contra hge
          have hlen_d : (depthsOf (n + m) C.gates).length ≤ k := by
            rw [depthsOf_length]
            omega
          exact hdk0 (List.getD_eq_default _ _ hlen_d)
        let idx : Fin C.gates.length := ⟨k - (n + m), by omega⟩
        have hkeq : k = n + m + idx.val := by simp [idx]; omega
        rw [hkeq] at hdk ⊢
        let g := C.gates[idx.val]
        by_cases hnl : nlGate g = true
        · have hmem : idx ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl, hdk⟩
          refine ⟨fun idx' => if idx' = idx then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single idx]
          · simp
          · intro idx' _ hne
            simp [hne]
          · intro h
            exact absurd hmem h
        · have hnlf : nlGate g = false := by cases h : nlGate g <;> simp_all
          have hdg := hdep_gate idx.val idx.isLt
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => 0, ?_⟩
            have hfun : val (n + m + idx.val) = fun _ _ => b2z (g.op.eval []) := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_nil]
            rw [hfun, anchor_const]
            simp
          | [a] =>
            have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have ha_d : dep a ≤ 1 := by
              change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun idx' => c1 * ca idx', ?_⟩
            have hfun : val (n + m + idx.val) = fun i j => c0 + c1 * val a i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_nil]
              exact anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            rw [hfun, anchor_add, anchor_const, zero_add, anchor_smul, hca, Finset.smul_sum]
            refine Finset.sum_congr rfl fun idx' _ => by rw [smul_smul]
          | [a, b] =>
            have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have hb_lt : b < n + m + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
            have hab_d : dep a ≤ 1 ∧ dep b ≤ 1 := by
              change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) hab_d.1
            obtain ⟨cb, hcb⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnlf
              rw [hg_in] at hnlf
              simpa using hnlf
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun idx' => c1 * ca idx' + c2 * cb idx', ?_⟩
            have hfun : val (n + m + idx.val) = fun i j => (c0 + c1 * val a i j) + c2 * val b i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
              have hanf := anf_two (fun x y => g.op.eval [x, y])
                ((wiresOf (oneEach i j) C.gates).getD a false)
                ((wiresOf (oneEach i j) C.gates).getD b false)
              rw [hxor] at hanf
              have hbf : b2z false = 0 := rfl
              change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
              rw [hbf, zero_mul, add_zero] at hanf
              exact hanf
            rw [hfun, anchor_add, anchor_add, anchor_const, zero_add, anchor_smul, anchor_smul,
              hca, hcb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun idx' _ => by
              rw [smul_smul, smul_smul, ← add_smul]
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
  let e : Fin NL.card ≃ NL := NL.equivFin.symm
  let pieces : Fin s → Matrix (Fin n) (Fin m) (ZMod 2) := fun r =>
    if hr : r.val < NL.card then anchor u v (val (n + m + (e ⟨r.val, hr⟩).val.val)) else 0
  choose coeff hcoeff using fun j : Fin q => hspan (tap j) (htap j).1
  let mask : Fin q → Finset (Fin s) := fun j =>
    Finset.univ.filter (fun r : Fin s => ∃ hr : r.val < NL.card, coeff j (e ⟨r.val, hr⟩).val = 1)
  refine ⟨pieces, mask, ?_, ?_⟩
  · intro r
    by_cases hr : r.val < NL.card
    · simp only [pieces, hr, dite_true]
      exact ⟨hNL_rank (e ⟨r.val, hr⟩).val (e ⟨r.val, hr⟩).property,
        anchor_zero_row u v _, anchor_zero_col u v _⟩
    · simp only [pieces, hr, dite_false]
      refine ⟨?_, fun _ => rfl, fun _ => rfl⟩
      simp
  · intro j
    have hAeq : anchor u v (fun i l => b2z (G j i l)) = anchor u v (val (tap j)) := by
      congr 1
      funext i l
      unfold val
      rw [← (htap j).2 i l]
      rfl
    rw [hAeq, hcoeff j]
    symm
    rw [Finset.sum_filter]
    have hfilt : ∑ r : Fin s, (if ∃ hr : r.val < NL.card, coeff j (e ⟨r.val, hr⟩).val = 1 then pieces r else 0) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin s => r.val < NL.card),
          (if ∃ hr : r.val < NL.card, coeff j (e ⟨r.val, hr⟩).val = 1 then pieces r else 0) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r _ hnr
      rw [Finset.mem_filter] at hnr
      have hge : ¬ r.val < NL.card := fun hr => hnr ⟨Finset.mem_univ r, hr⟩
      simp [hge]
    rw [hfilt]
    have hbij : ∑ r ∈ Finset.univ.filter (fun r : Fin s => r.val < NL.card),
        (if ∃ hr : r.val < NL.card, coeff j (e ⟨r.val, hr⟩).val = 1 then pieces r else 0) =
        ∑ t : Fin NL.card, coeff j (e t).val • anchor u v (val (n + m + (e t).val.val)) := by
      refine Finset.sum_bij (fun r hr => ⟨r.val, (Finset.mem_filter.mp hr).2⟩) ?_ ?_ ?_ ?_
      · intro _ _
        exact Finset.mem_univ _
      · intro r1 _ r2 _ heq
        exact Fin.ext (Fin.mk.inj heq)
      · intro t _
        refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt hNL_card⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
      · intro r hr
        have hlt : r.val < NL.card := (Finset.mem_filter.mp hr).2
        simp only [pieces, hlt, dite_true, exists_true_left]
        rw [zmod2_smul_eq_ite]
    rw [hbij, Fintype.sum_equiv e _ (fun idx : NL => coeff j idx.val • anchor u v (val (n + m + idx.val.val))) (fun _ => rfl)]
    exact Finset.sum_attach NL (fun idx => coeff j idx • anchor u v (val (n + m + idx.val)))

private theorem single_tap_rank_le {n m : ℕ} (G : Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit) (tap : Fin 1 → ℕ)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hcnt : C.gates.countP nlGate ≤ t)
    (htap : ∀ j : Fin 1, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents G ⟨C.gates, tap j⟩) :
    (anchor u v (fun i l => b2z (G i l))).rank ≤ 2 * t := by
  obtain ⟨pieces, mask, hpieces, hmask⟩ :=
    circuit_decomp (fun (_ : Fin 1) => G) u v t C tap hlen hrb hcnt htap
  rw [hmask 0]
  calc (∑ r ∈ mask 0, pieces r).rank
      ≤ ∑ r ∈ mask 0, (pieces r).rank := matrix_rank_sum_le (mask 0) pieces
    _ ≤ ∑ _r ∈ mask 0, 2 := Finset.sum_le_sum fun r _ => (hpieces r).1
    _ = (mask 0).card * 2 := by simp
    _ ≤ t * 2 := Nat.mul_le_mul_right 2 (by simpa using Finset.card_le_univ (mask 0))
    _ = 2 * t := Nat.mul_comm t 2

section Pairing

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

private noncomputable def pairCoordinates (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

private theorem pairCoordinates_apply (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (x : K) (i : Fin k) :
    pairCoordinates b bit x i = bit (b i * x) := rfl

private noncomputable def pairEquiv (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0) :
    K ≃ₗ[F] (Fin k → F) := by
  letI : FiniteDimensional F K := b.finiteDimensional_of_finite
  have dim : finrank F K = finrank F (Fin k → F) := by
    simp [Module.finrank_eq_card_basis b]
  have hinj : Function.Injective (pairCoordinates b bit) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : bit.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [pairCoordinates_apply, mul_comm x (b i)] using hi
    apply hbit
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  exact LinearEquiv.ofBijective (pairCoordinates b bit)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hinj⟩

private noncomputable def pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) : Matrix (Fin k) (Fin k) F :=
  fun i j => bit (b i * C (b j))

private noncomputable def pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0)
    (A : Matrix (Fin k) (Fin k) F) : K →ₗ[F] K :=
  (pairEquiv b bit hbit).symm.toLinearMap.comp (Matrix.toLin b (Pi.basisFun F _) A)

private theorem pair_toLin_entry (b : Basis (Fin k) F K) (A : Matrix (Fin k) (Fin k) F)
    (i j : Fin k) : Matrix.toLin b (Pi.basisFun F _) A (b j) i = A i j := by
  rw [Matrix.toLin_self]
  simp [Pi.single_apply, mul_ite]

private theorem pairMatrix_pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (A : Matrix (Fin k) (Fin k) F) :
    pairMatrix b bit (pairMap b bit hbit A) = A := by
  ext i j
  change pairEquiv b bit hbit ((pairEquiv b bit hbit).symm
    (Matrix.toLin b (Pi.basisFun F _) A (b j))) i = A i j
  rw [LinearEquiv.apply_symm_apply, pair_toLin_entry]

private theorem pairMatrix_injective (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) : Function.Injective (pairMatrix b bit) := by
  intro C D h
  apply b.ext
  intro j
  apply (pairEquiv b bit hbit).injective
  funext i
  exact congrFun (congrFun h i) j

private theorem rank_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairMatrix b bit C).rank = finrank F (LinearMap.range C) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun F _) b]
  have h : Matrix.toLin b (Pi.basisFun F _) (pairMatrix b bit C) =
      (pairEquiv b bit hbit).toLinearMap.comp C := by
    apply b.ext
    intro j
    funext i
    rw [pair_toLin_entry]
    rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

private noncomputable def pairAnchor (A : Matrix (Fin k) (Fin k) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  fun i j => Fin.cases 0 (fun i => Fin.cases 0 (A i) j) i

private theorem pairAnchor_zero_left (A : Matrix (Fin k) (Fin k) F) (j : Fin (k + 1)) :
    pairAnchor A 0 j = 0 := rfl

private theorem pairAnchor_zero_right (A : Matrix (Fin k) (Fin k) F) (i : Fin (k + 1)) :
    pairAnchor A i 0 = 0 := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

private theorem pairAnchor_succ_succ (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    pairAnchor A i.succ j.succ = A i j := rfl

private theorem pairAnchor_submatrix (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (hrow : ∀ j, A 0 j = 0) (hcol : ∀ i, A i 0 = 0) :
    pairAnchor (A.submatrix Fin.succ Fin.succ) = A := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · exact (hrow j).symm
  · exact (hcol i.succ).symm
  · rfl

private theorem rank_pairAnchor (A : Matrix (Fin k) (Fin k) F) : (pairAnchor A).rank = A.rank := by
  classical
  let e : (Fin k → F) →ₗ[F] (Fin (k + 1) → F) :=
    { toFun := Fin.cases 0
      map_add' := by
        intro x y
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp
      map_smul' := by
        intro a x
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp }
  let p : (Fin (k + 1) → F) →ₗ[F] (Fin k → F) :=
    { toFun := fun x i => x i.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := fun _ _ h => funext fun i => congrFun h i.succ
  have hp : LinearMap.range p = ⊤ :=
    LinearMap.range_eq_top.mpr (fun x => ⟨e x, rfl⟩)
  have heq : (pairAnchor A).mulVecLin = e.comp (A.mulVecLin.comp p) := by
    ext x i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [e, Matrix.mulVec, dotProduct, pairAnchor_zero_left]
    · simp [e, p, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pairAnchor_zero_right, pairAnchor_succ_succ]
  rw [Matrix.rank, Matrix.rank, heq, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ hp]
  exact (Submodule.equivMapOfInjective e he _).finrank_eq.symm

private theorem rank_pairAnchor_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairAnchor (pairMatrix b bit C)).rank = finrank F (LinearMap.range C) :=
  (rank_pairAnchor _).trans (rank_pairMatrix b bit hbit C)

private theorem existsUnique_anchoredPairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (hrow : ∀ j, A 0 j = 0) (hcol : ∀ i, A i 0 = 0) :
    ∃! C : K →ₗ[F] K, pairAnchor (pairMatrix b bit C) = A := by
  let B := A.submatrix Fin.succ Fin.succ
  refine ⟨pairMap b bit hbit B, ?_, ?_⟩
  · change pairAnchor (pairMatrix b bit (pairMap b bit hbit B)) = A
    rw [pairMatrix_pairMap, pairAnchor_submatrix A hrow hcol]
  · intro C h
    apply pairMatrix_injective b bit hbit
    rw [pairMatrix_pairMap]
    exact Matrix.ext fun i j => congrFun (congrFun h i.succ) j.succ

private theorem pair_add_lmul (bit : K →ₗ[F] F) (C : K →ₗ[F] K) (t x y : K) :
    bit (x * (C + LinearMap.mulLeft F t) y) = bit (x * C y) + bit (t * x * y) := by
  change bit (x * (C y + t * y)) = _
  rw [mul_add, map_add, ← mul_assoc, mul_comm x t]

private theorem pairAnchor_pairMatrix_apply (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) (i j : Fin (k + 1)) :
    pairAnchor (pairMatrix b bit C) i j =
      bit (Fin.cases 0 b i * C (Fin.cases 0 b j)) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · simp [pairAnchor_zero_left]
  · simp [pairAnchor_zero_right]
  · rfl

private theorem pairAnchor_add_lmul (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) (t : K) (i j : Fin (k + 1)) :
    pairAnchor (pairMatrix b bit (C + LinearMap.mulLeft F t)) i j =
      pairAnchor (pairMatrix b bit C) i j +
        bit (t * Fin.cases 0 b i * Fin.cases 0 b j) := by
  simp only [pairAnchor_pairMatrix_apply, pair_add_lmul]

private theorem pairAnchor_pairMatrix_zero (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    pairAnchor (pairMatrix b bit (0 : K →ₗ[F] K)) = 0 := by
  ext i j
  simp only [pairAnchor_pairMatrix_apply, LinearMap.zero_apply, mul_zero, map_zero, Matrix.zero_apply]

private theorem pairAnchor_pairMatrix_add (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C1 C2 : K →ₗ[F] K) :
    pairAnchor (pairMatrix b bit (C1 + C2)) =
      pairAnchor (pairMatrix b bit C1) + pairAnchor (pairMatrix b bit C2) := by
  ext i j
  simp only [pairAnchor_pairMatrix_apply, LinearMap.add_apply, mul_add, map_add, Matrix.add_apply]

private theorem pairAnchor_pairMatrix_sum {ι : Type*} (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (S : Finset ι) (f : ι → (K →ₗ[F] K)) :
    pairAnchor (pairMatrix b bit (∑ i ∈ S, f i)) =
      ∑ i ∈ S, pairAnchor (pairMatrix b bit (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact pairAnchor_pairMatrix_zero b bit
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [pairAnchor_pairMatrix_add, ih]

end Pairing

private lemma b2z_parity_filter {g : ℕ} (S : Finset (Fin g)) (p : Fin g → Bool) :
    b2z (((S.filter (fun i => p i)).card % 2) == 1) = ∑ i ∈ S, b2z (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.filter_empty, Finset.card_empty, Finset.sum_empty]
    decide
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    cases hpa : p a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      simp [b2z]
    · simp only [↓reduceIte]
      have hna : a ∉ S.filter (fun i => p i) := fun h => ha (Finset.mem_filter.mp h).1
      rw [Finset.card_insert_of_notMem hna, ← ih]
      change b2z ((((S.filter (fun i => p i)).card + 1) % 2) == 1) =
        (1 : ZMod 2) + b2z (((S.filter (fun i => p i)).card % 2) == 1)
      set m := (S.filter (fun i => p i)).card
      rcases Nat.mod_two_eq_zero_or_one m with hm | hm
      · have hm1 : (m + 1) % 2 = 1 := by omega
        rw [hm, hm1]
        decide
      · have hm1 : (m + 1) % 2 = 0 := by omega
        rw [hm, hm1]
        decide

private lemma add_self_eq_zero_of_algebra_zmod2 {K : Type*} [Field K] [Algebra (ZMod 2) K] (x : K) :
    x + x = 0 := by
  have h2 : (2 : K) = 0 := by
    calc (2 : K) = 1 + 1 := one_add_one_eq_two.symm
      _ = algebraMap (ZMod 2) K 1 + algebraMap (ZMod 2) K 1 := by rw [map_one]
      _ = algebraMap (ZMod 2) K (1 + 1) := (map_add _ 1 1).symm
      _ = algebraMap (ZMod 2) K 0 := by rw [show (1 + 1 : ZMod 2) = 0 by decide]
      _ = 0 := map_zero _
  calc x + x = (2 : K) * x := (two_mul x).symm
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

private lemma eq_of_add_eq_zero_of_algebra_zmod2 {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {x y : K} (h : x + y = 0) : x = y := by
  calc x = x + 0 := (add_zero x).symm
    _ = x + (y + y) := by rw [add_self_eq_zero_of_algebra_zmod2 y]
    _ = (x + y) + y := (add_assoc x y y).symm
    _ = 0 + y := by rw [h]
    _ = y := zero_add y

private lemma card_ker_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] (M : K →ₗ[ZMod 2] K) :
    (Finset.univ.filter (fun x : K => M x = 0)).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker M) := by
  classical
  let Z : Finset K := Finset.univ.filter fun x => M x = 0
  have hZ : Z.card = Fintype.card (LinearMap.ker M) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivProp (funext fun x => by simp [Z]))
  rw [show (Finset.univ.filter (fun x : K => M x = 0)).card = Z.card from rfl, hZ,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

private lemma card_nonzero_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] (M : K →ₗ[ZMod 2] K) :
    (Finset.univ.filter (fun x : K => x ≠ 0 ∧ M x = 0)).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker M) - 1 := by
  classical
  let Z : Finset K := Finset.univ.filter fun x => M x = 0
  have he : Finset.univ.filter (fun x : K => x ≠ 0 ∧ M x = 0) = Z.erase 0 := by
    ext x
    simp [Z]
  have hz : (0 : K) ∈ Z := by simp [Z]
  rw [he, Finset.card_erase_of_mem hz]
  exact congrArg (· - 1) (card_ker_eq M)

private lemma arith_conjunct2 {k t s : ℕ} (ht : 2 * t < k) (hk : 2 < k) (hs : s ≤ k - 2 * t) :
    let h := k - 2 * t
    let B := fun j : ℕ => if h ≤ 2 * j then (2 ^ k - 2 ^ (k - 2 * j)) / (2 ^ h - 1) else 0
    (∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j) < 2 ^ k - 1 := by
  dsimp only
  set h := k - 2 * t
  let B : ℕ → ℕ := fun j : ℕ => if h ≤ 2 * j then (2 ^ k - 2 ^ (k - 2 * j)) / (2 ^ h - 1) else 0
  change (∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j) < 2 ^ k - 1
  have hh1 : 1 ≤ h := by omega
  have hpowk : 8 ≤ 2 ^ k := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  by_cases hs0 : s = 0
  · subst hs0
    have hB0 : B 0 = 0 := by
      simp only [B]
      exact if_neg (by omega)
    rw [show (0 + 1 : ℕ) = 1 from rfl, Finset.sum_range_one]
    simp only [Nat.choose_self, one_mul, hB0]
    omega
  · have hs1 : 1 ≤ s := by omega
    by_cases hh_eq1 : h = 1
    · have hs_eq1 : s = 1 := by omega
      subst hs_eq1
      have hB0 : B 0 = 0 := by
        simp only [B]
        exact if_neg (by omega)
      have hB1 : B 1 = 2 ^ k - 2 ^ (k - 2) := by
        simp only [B, hh_eq1]
        have : 1 ≤ 2 * 1 := by omega
        simp [this]
      rw [show (1 + 1 : ℕ) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.choose_zero_right, Nat.choose_self, one_mul, hB0, hB1, zero_add]
      have h2k2 : 2 ≤ 2 ^ (k - 2) := by
        calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ (k - 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have hle : 2 ^ (k - 2) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · by_cases hh_eq2 : h = 2
      · have hk4 : 4 ≤ k := by omega
        set m := k - 4
        have hkm : k = m + 4 := by omega
        have hk2m : k - 2 = m + 2 := by omega
        have hk4m : k - 4 = m := by omega
        set P := 2 ^ m
        have hP1 : 1 ≤ P := Nat.one_le_two_pow
        have h2k : 2 ^ k = 16 * P := by
          rw [hkm, pow_add]
          change P * 16 = 16 * P
          ring
        have h2k2 : 2 ^ (k - 2) = 4 * P := by
          rw [hk2m, pow_add]
          change P * 4 = 4 * P
          ring
        have h2k4 : 2 ^ (k - 4) = P := by
          rw [hk4m]
        have hB0 : B 0 = 0 := by
          simp only [B, hh_eq2]
          exact if_neg (by omega)
        have hB1 : B 1 = 4 * P := by
          simp only [B, hh_eq2]
          have : 2 ≤ 2 * 1 := by omega
          simp only [this, ↓reduceIte, mul_one, h2k, h2k2]
          have hsub : 16 * P - 4 * P = 3 * (4 * P) := by omega
          have hden : 2 ^ 2 - 1 = 3 := by decide
          rw [hsub, hden, Nat.mul_div_right _ (by omega)]
        have hB2 : B 2 = 5 * P := by
          simp only [B, hh_eq2]
          have : 2 ≤ 2 * 2 := by omega
          simp only [this, ↓reduceIte, show 2 * 2 = 4 from rfl, h2k, h2k4]
          have hsub : 16 * P - P = 3 * (5 * P) := by omega
          have hden : 2 ^ 2 - 1 = 3 := by decide
          rw [hsub, hden, Nat.mul_div_right _ (by omega)]
        have hs12 : s = 1 ∨ s = 2 := by omega
        rcases hs12 with rfl | rfl
        · rw [show (1 + 1 : ℕ) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
          simp only [Nat.choose_zero_right, Nat.choose_self, one_mul, hB0, hB1, zero_add, h2k]
          omega
        · rw [show (2 + 1 : ℕ) = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
          have hc0 : Nat.choose 2 0 = 1 := by decide
          have hc1 : Nat.choose 2 1 = 2 := by decide
          have hc2 : Nat.choose 2 2 = 1 := by decide
          rw [hc0, hc1, hc2, hB0, hB1, hB2, h2k]
          omega
      · have hh3 : 3 ≤ h := by omega
        have hB0 : B 0 = 0 := by
          simp only [B]
          exact if_neg (by omega)
        have hB1 : B 1 = 0 := by
          simp only [B]
          exact if_neg (by omega)
        set Q := (2 ^ k - 1) / (2 ^ h - 1)
        have hBQ : ∀ j, B j ≤ Q := by
          intro j
          simp only [B]
          by_cases hj : h ≤ 2 * j
          · simp only [hj, ↓reduceIte]
            have h1 : 1 ≤ 2 ^ (k - 2 * j) := Nat.one_le_two_pow
            exact Nat.div_le_div_right (by omega)
          · simp only [hj, ↓reduceIte]
            exact Nat.zero_le Q
        let c : ℕ → ℕ := fun j => if j ≤ 1 then 0 else Nat.choose s j
        have hsum_le : ∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j ≤
            (∑ j ∈ Finset.range (s + 1), c j) * Q := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hj0 : j = 0
          · subst hj0
            simp [hB0, c]
          · by_cases hj1 : j = 1
            · subst hj1
              simp [hB1, c]
            · have hge2 : ¬ j ≤ 1 := by omega
              simp only [c, hge2, ↓reduceIte]
              exact Nat.mul_le_mul_left _ (hBQ j)
        have hcsum : (∑ j ∈ Finset.range (s + 1), c j) + 1 + s = 2 ^ s := by
          have hpt : ∀ j ∈ Finset.range (s + 1),
              Nat.choose s j = c j + (if j = 0 then 1 else 0) + (if j = 1 then s else 0) := by
            intro j _
            by_cases hj0 : j = 0
            · subst hj0
              simp [c]
            · by_cases hj1 : j = 1
              · subst hj1
                simp [c]
              · have hge2 : ¬ j ≤ 1 := by omega
                simp [c, hge2, hj0, hj1]
          have htot : ∑ j ∈ Finset.range (s + 1), Nat.choose s j = 2 ^ s := Nat.sum_range_choose s
          rw [← htot, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib]
          have h0mem : 0 ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
          have h1mem : 1 ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
          have hs0' : (∑ j ∈ Finset.range (s + 1), if j = 0 then (1 : ℕ) else 0) = 1 := by
            rw [Finset.sum_ite_eq' (Finset.range (s + 1)) 0 (fun _ => (1 : ℕ))]
            simp [h0mem]
          have hs1' : (∑ j ∈ Finset.range (s + 1), if j = 1 then s else 0) = s := by
            rw [Finset.sum_ite_eq' (Finset.range (s + 1)) 1 (fun _ => s)]
            simp [h1mem]
          rw [hs0', hs1']
        have h2sh : 2 ^ s ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hs
        have h2h8 : 8 ≤ 2 ^ h := by
          calc 8 = 2 ^ 3 := by decide
            _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) hh3
        have hcle : ∑ j ∈ Finset.range (s + 1), c j ≤ 2 ^ h - 2 := by omega
        have hprod_le : (∑ j ∈ Finset.range (s + 1), c j) * Q ≤ (2 ^ h - 2) * Q :=
          Nat.mul_le_mul_right Q hcle
        have hstrict : (2 ^ h - 2) * Q < 2 ^ k - 1 := by
          by_cases hQ0 : Q = 0
          · rw [hQ0, mul_zero]
            omega
          · have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
            have hlt : (2 ^ h - 2) * Q < (2 ^ h - 1) * Q :=
              Nat.mul_lt_mul_of_pos_right (by omega) hQpos
            have hdiv : (2 ^ h - 1) * Q ≤ 2 ^ k - 1 := Nat.mul_div_le (2 ^ k - 1) (2 ^ h - 1)
            omega
        omega

private theorem main_proof
    (K : Type) [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    (k : ℕ) (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0)
    (g s t : ℕ) (T : Fin g → Fin (k + 1) → Fin (k + 1) → Bool) (Z : Finset K)
    (ht : 2 * t < k)
    (hfits : ∃ (C : Circuit) (tap : Fin g → ℕ),
      ReadsBack ((k + 1) + (k + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ s ∧
      ∀ j : Fin g, (depthsOf ((k + 1) + (k + 1)) C.gates).getD (tap j) 0 ≤ 1 ∧
        Represents (T j) ⟨C.gates, tap j⟩)
    (hzero : (0 : K) ∉ Z)
    (hres : ∀ z ∈ Z, ∃ S : Finset (Fin g),
      ∃ (C : Circuit) (tap : Fin 1 → ℕ),
        ReadsBack ((k + 1) + (k + 1)) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
        ∀ j : Fin 1, (depthsOf ((k + 1) + (k + 1)) C.gates).getD (tap j) 0 ≤ 1 ∧
          Represents (fun x y => xor (decide (bit (z * Fin.cases 0 basis x * Fin.cases 0 basis y) ≠ 0))
            (((S.filter (fun i => T i x y)).card % 2) == 1)) ⟨C.gates, tap j⟩) :
    let h := k - 2 * t
    let B := fun j : ℕ => if h ≤ 2 * j then (2 ^ k - 2 ^ (k - 2 * j)) / (2 ^ h - 1) else 0
    Z.card ≤ (∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j) ∧
      (2 < k → Z.card = 2 ^ k - 1 → h < s) := by
  classical
  dsimp only
  set h := k - 2 * t
  let B := fun j : ℕ => if h ≤ 2 * j then (2 ^ k - 2 ^ (k - 2 * j)) / (2 ^ h - 1) else 0
  let n := k + 1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun (S : Finset (Fin g)) (z : K) (x y : Fin n) =>
    xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)
  have hconj1 : Z.card ≤ ∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j := by
    let : Fintype K := Fintype.ofEquiv (Fin k → ZMod 2) basis.equivFun.symm
    have hfinK : Module.finrank (ZMod 2) K = k := by
      rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]
    have hcardK : Fintype.card K = 2 ^ k := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hfinK]
    obtain ⟨C, tap, hrb, hlen, hcnt, htap⟩ := hfits
    obtain ⟨pieces, maskTap, hpieces, hmaskTap⟩ :=
      circuit_decomp T (0 : Fin n) (0 : Fin n) s C tap hlen hrb hcnt htap
    have hexP : ∀ r : Fin s, ∃ P : K →ₗ[ZMod 2] K,
        pairAnchor (pairMatrix basis bit P) = pieces r ∧
        Module.finrank (ZMod 2) (LinearMap.range P) ≤ 2 := by
      intro r
      obtain ⟨P, hP, _⟩ :=
        existsUnique_anchoredPairMatrix basis bit hbit (pieces r) (hpieces r).2.1 (hpieces r).2.2
      refine ⟨P, hP, ?_⟩
      rw [← rank_pairAnchor_pairMatrix basis bit hbit P, hP]
      exact (hpieces r).1
    choose P hP_eq hP_rank using hexP
    let maskOf : Finset (Fin g) → Finset (Fin s) := fun S =>
      Finset.univ.filter (fun r : Fin s =>
        (∑ i ∈ S, if r ∈ maskTap i then (1 : ZMod 2) else 0) = 1)
    let D : Finset (Fin s) → (K →ₗ[ZMod 2] K) := fun J => ∑ r ∈ J, P r
    have hanchor_mask : ∀ S : Finset (Fin g),
        anchor (0 : Fin n) (0 : Fin n)
          (fun x y => b2z (((S.filter (fun i => T i x y)).card % 2) == 1)) =
        pairAnchor (pairMatrix basis bit (D (maskOf S))) := by
      intro S
      have h1 : (fun x y => b2z (((S.filter (fun i => T i x y)).card % 2) == 1)) =
          fun x y => ∑ i ∈ S, b2z (T i x y) := by
        funext x y
        exact b2z_parity_filter S (fun i => T i x y)
      rw [h1, anchor_sum]
      have h2 : ∑ i ∈ S, anchor (0 : Fin n) (0 : Fin n) (fun x y => b2z (T i x y)) =
          ∑ i ∈ S, ∑ r : Fin s,
            (if r ∈ maskTap i then (1 : ZMod 2) else 0) • pairAnchor (pairMatrix basis bit (P r)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmaskTap i]
        have hsub : ∑ r ∈ maskTap i, pieces r =
            ∑ r : Fin s, if r ∈ maskTap i then pairAnchor (pairMatrix basis bit (P r)) else 0 := by
          rw [← Finset.sum_filter]
          have hfeq : Finset.univ.filter (fun r : Fin s => r ∈ maskTap i) = maskTap i := by
            ext r; simp
          rw [hfeq]
          exact Finset.sum_congr rfl fun r _ => (hP_eq r).symm
        rw [hsub]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hr : r ∈ maskTap i <;> simp [hr]
      rw [h2, Finset.sum_comm]
      have h3 : ∑ r : Fin s, ∑ i ∈ S,
            (if r ∈ maskTap i then (1 : ZMod 2) else 0) • pairAnchor (pairMatrix basis bit (P r)) =
          ∑ r ∈ maskOf S, pairAnchor (pairMatrix basis bit (P r)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.sum_smul, zmod2_smul_eq_ite]
      rw [h3, pairAnchor_pairMatrix_sum]
    have hanchor_res : ∀ (S : Finset (Fin g)) (z : K),
        anchor (0 : Fin n) (0 : Fin n) (fun x y => b2z (residual S z x y)) =
          pairAnchor (pairMatrix basis bit (D (maskOf S) + LinearMap.mulLeft (ZMod 2) z)) := by
      intro S z
      change anchor (0 : Fin n) (0 : Fin n)
        (fun x y => b2z (xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1))) = _
      rw [anchor_table_xor, hanchor_mask S]
      let Mz : Matrix (Fin n) (Fin n) (ZMod 2) := fun x y => bit (z * point x * point y)
      have hMz0L : ∀ y : Fin n, Mz 0 y = 0 := by
        intro y
        simp [Mz, point]
      have hMz0R : ∀ x : Fin n, Mz x 0 = 0 := by
        intro x
        simp [Mz, point]
      have hmult_eq : anchor (0 : Fin n) (0 : Fin n) (fun x y => b2z (mult z x y)) = Mz :=
        anchor_table_encode (0 : Fin n) (0 : Fin n) Mz hMz0L hMz0R
      rw [hmult_eq]
      ext x y
      rw [pairAnchor_add_lmul, Matrix.add_apply, add_comm]
    have hchoice : ∀ z : K, z ∈ Z →
        ∃ S : Finset (Fin g),
          Module.finrank (ZMod 2) (LinearMap.range (D (maskOf S) + LinearMap.mulLeft (ZMod 2) z)) ≤ 2 * t := by
      intro z hz
      obtain ⟨S, C1, tap1, hrb1, hlen1, hcnt1, htap1⟩ := hres z hz
      refine ⟨S, ?_⟩
      have hrk := single_tap_rank_le (residual S z) (0 : Fin n) (0 : Fin n) t C1 tap1 hlen1 hrb1 hcnt1 htap1
      rw [hanchor_res S z, rank_pairAnchor_pairMatrix basis bit hbit] at hrk
      exact hrk
    let S_of : K → Finset (Fin g) := fun z =>
      if hz : z ∈ Z then Classical.choose (hchoice z hz) else ∅
    have hS_of_rank : ∀ z ∈ Z,
        Module.finrank (ZMod 2) (LinearMap.range (D (maskOf (S_of z)) + LinearMap.mulLeft (ZMod 2) z)) ≤ 2 * t := by
      intro z hz
      have hS : S_of z = Classical.choose (hchoice z hz) := by
        dsimp only [S_of]
        split_ifs
        rfl
      rw [hS]
      exact Classical.choose_spec (hchoice z hz)
    let fmask : K → Finset (Fin s) := fun z => maskOf (S_of z)
    have hfiber_bound : ∀ J : Finset (Fin s), (Z.filter (fun z => fmask z = J)).card ≤ B J.card := by
      intro J
      set ZJ := Z.filter (fun z => fmask z = J)
      have hDrank : Module.finrank (ZMod 2) (LinearMap.range (D J)) ≤ 2 * J.card := by
        calc Module.finrank (ZMod 2) (LinearMap.range (∑ r ∈ J, P r))
            ≤ ∑ r ∈ J, Module.finrank (ZMod 2) (LinearMap.range (P r)) := finrank_range_sum_le J P
          _ ≤ ∑ _r ∈ J, 2 := Finset.sum_le_sum fun r _ => hP_rank r
          _ = J.card * 2 := by simp
          _ = 2 * J.card := Nat.mul_comm _ _
      have hDker : k - 2 * J.card ≤ Module.finrank (ZMod 2) (LinearMap.ker (D J)) := by
        have hnull := LinearMap.finrank_range_add_finrank_ker (D J)
        rw [hfinK] at hnull
        omega
      have hz_ker : ∀ z ∈ ZJ,
          h ≤ Module.finrank (ZMod 2) (LinearMap.ker (D J + LinearMap.mulLeft (ZMod 2) z)) ∧
          h ≤ 2 * J.card := by
        intro z hzJ
        have hzZ : z ∈ Z := (Finset.mem_filter.mp hzJ).1
        have hfz : fmask z = J := (Finset.mem_filter.mp hzJ).2
        have hz0 : z ≠ 0 := fun h0 => hzero (h0 ▸ hzZ)
        have hrz := hS_of_rank z hzZ
        change Module.finrank (ZMod 2) (LinearMap.range (D (fmask z) + LinearMap.mulLeft (ZMod 2) z)) ≤ 2 * t at hrz
        rw [hfz] at hrz
        have hnull := LinearMap.finrank_range_add_finrank_ker (D J + LinearMap.mulLeft (ZMod 2) z)
        rw [hfinK] at hnull
        have hkh : h ≤ Module.finrank (ZMod 2) (LinearMap.ker (D J + LinearMap.mulLeft (ZMod 2) z)) := by omega
        have hsub : LinearMap.ker (D J + LinearMap.mulLeft (ZMod 2) z) ≤
            (LinearMap.range (D J)).map (LinearMap.mulLeft (ZMod 2) z⁻¹) := by
          intro x hx
          have hsum0 : D J x + z * x = 0 := LinearMap.mem_ker.mp hx
          have heq : D J x = z * x := eq_of_add_eq_zero_of_algebra_zmod2 hsum0
          refine ⟨D J x, ⟨x, rfl⟩, ?_⟩
          change z⁻¹ * D J x = x
          rw [heq, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
        have hle_ran : Module.finrank (ZMod 2) (LinearMap.ker (D J + LinearMap.mulLeft (ZMod 2) z)) ≤
            Module.finrank (ZMod 2) (LinearMap.range (D J)) :=
          (Submodule.finrank_mono hsub).trans (Submodule.finrank_map_le _ _)
        exact ⟨hkh, by omega⟩
      by_cases hJ : h ≤ 2 * J.card
      · simp only [B, hJ, ↓reduceIte]
        let Bz : K → Finset K := fun z => Finset.univ.filter (fun x : K => x ≠ 0 ∧ D J x + z * x = 0)
        let NonKer : Finset K := Finset.univ.filter (fun x : K => D J x ≠ 0)
        have hdisj : (ZJ : Set K).PairwiseDisjoint Bz := by
          intro z1 _ z2 _ hne
          refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
          have h1 := (Finset.mem_filter.mp hx1).2
          have h2 := (Finset.mem_filter.mp hx2).2
          have heq : z1 * x = z2 * x := add_left_cancel (h1.2.trans h2.2.symm)
          exact hne (mul_right_cancel₀ h1.1 heq)
        have hsub_nk : ZJ.biUnion Bz ⊆ NonKer := by
          intro x hx
          obtain ⟨z, hzJ, hxz⟩ := Finset.mem_biUnion.mp hx
          have hzZ : z ∈ Z := (Finset.mem_filter.mp hzJ).1
          have hz0 : z ≠ 0 := fun h0 => hzero (h0 ▸ hzZ)
          have hx_prop := (Finset.mem_filter.mp hxz).2
          have hDx : D J x = z * x := eq_of_add_eq_zero_of_algebra_zmod2 hx_prop.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, by rw [hDx]; exact mul_ne_zero hz0 hx_prop.1⟩
        have hBz_lb : ∀ z ∈ ZJ, 2 ^ h - 1 ≤ (Bz z).card := by
          intro z hzJ
          have hcardBz : (Bz z).card =
              2 ^ Module.finrank (ZMod 2) (LinearMap.ker (D J + LinearMap.mulLeft (ZMod 2) z)) - 1 :=
            card_nonzero_eq (D J + LinearMap.mulLeft (ZMod 2) z)
          rw [hcardBz]
          exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (hz_ker z hzJ).1) 1
        have hNK_ub : NonKer.card ≤ 2 ^ k - 2 ^ (k - 2 * J.card) := by
          have hcomp : (Finset.univ.filter (fun x : K => D J x = 0)).card + NonKer.card = Fintype.card K := by
            have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K)) (p := fun x : K => D J x = 0)
            simpa [NonKer] using this
          rw [card_ker_eq (D J), hcardK] at hcomp
          have hpow : 2 ^ (k - 2 * J.card) ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (D J)) :=
            Nat.pow_le_pow_right (by omega) hDker
          omega
        have hmul : ZJ.card * (2 ^ h - 1) ≤ 2 ^ k - 2 ^ (k - 2 * J.card) := by
          calc ZJ.card * (2 ^ h - 1)
              = ∑ _z ∈ ZJ, (2 ^ h - 1) := by simp
            _ ≤ ∑ z ∈ ZJ, (Bz z).card := Finset.sum_le_sum hBz_lb
            _ = (ZJ.biUnion Bz).card := (Finset.card_biUnion hdisj).symm
            _ ≤ NonKer.card := Finset.card_le_card hsub_nk
            _ ≤ 2 ^ k - 2 ^ (k - 2 * J.card) := hNK_ub
        have hden_pos : 0 < 2 ^ h - 1 := by
          have : 2 ≤ 2 ^ h := by
            calc 2 = 2 ^ 1 := by decide
              _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        exact (Nat.le_div_iff_mul_le hden_pos).mpr hmul
      · have hZJ_empty : ZJ = ∅ := by
          ext z
          simp only [Finset.notMem_empty, iff_false]
          intro hzJ
          exact hJ (hz_ker z hzJ).2
        rw [hZJ_empty, Finset.card_empty]
        exact Nat.zero_le _
    have hpart : Z.card = ∑ J : Finset (Fin s), (Z.filter (fun z => fmask z = J)).card := by
      have h1 : Z.card = ∑ z ∈ Z, ∑ J : Finset (Fin s), if fmask z = J then 1 else 0 := by
        calc Z.card = ∑ _z ∈ Z, 1 := by simp
          _ = ∑ z ∈ Z, ∑ J : Finset (Fin s), if fmask z = J then 1 else 0 := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.sum_ite_eq (Finset.univ : Finset (Finset (Fin s))) (fmask z) (fun _ => (1 : ℕ))]
            simp
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => ?_
      rw [Finset.card_filter]
    have hsum_card : ∑ J : Finset (Fin s), B J.card =
        ∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j := by
      have h1 : ∑ J : Finset (Fin s), B J.card =
          ∑ J : Finset (Fin s), ∑ j ∈ Finset.range (s + 1), if J.card = j then B j else 0 := by
        refine Finset.sum_congr rfl fun J _ => ?_
        have hlt : J.card < s + 1 := Nat.lt_succ_of_le (by simpa using Finset.card_le_univ J)
        rw [Finset.sum_ite_eq (Finset.range (s + 1)) J.card (fun j => B j)]
        simp [Finset.mem_range.mpr hlt]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      congr 1
      have hfilt : (Finset.univ : Finset (Finset (Fin s))).filter (fun J => J.card = j) =
          (Finset.univ : Finset (Fin s)).powersetCard j := by
        ext J
        simp [Finset.mem_powersetCard]
      rw [hfilt, Finset.card_powersetCard, Finset.card_fin]
    calc Z.card
        = ∑ J : Finset (Fin s), (Z.filter (fun z => fmask z = J)).card := hpart
      _ ≤ ∑ J : Finset (Fin s), B J.card := Finset.sum_le_sum fun J _ => hfiber_bound J
      _ = ∑ j ∈ Finset.range (s + 1), Nat.choose s j * B j := hsum_card
  refine ⟨hconj1, ?_⟩
  intro hk hZcard
  by_contra hnot
  have hs : s ≤ h := by omega
  have hlt := arith_conjunct2 ht hk hs
  rw [hZcard] at hconj1
  exact Nat.not_le.mpr hlt hconj1

end PEqualNP.Outside.L_meta_29759_aux

theorem PEqualNP.Outside.L_meta_29759 : (
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
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
  let n := k+1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)


  ∀ (g s t : ℕ) (T : Fin g → Fin n → Fin n → Bool) (Z : Finset K),
    2*t < k → fits n n g T s → (0 : K) ∉ Z →
    (∀ z ∈ Z, ∃ S : Finset (Fin g), fits n n 1 (fun _ => residual T S z) t) →
    let h := k-2*t
    let B := fun j : ℕ => if h ≤ 2*j then (2^k - 2^(k-2*j))/(2^h-1) else 0
    Z.card ≤ (∑ j ∈ Finset.range (s+1), Nat.choose s j * B j)
    ∧ (2 < k → Z.card = 2^k-1 → h < s)) := by
  intro nonlinear depths fits F K _ _ _ k basis bit hbit n point mult residual g s t T Z ht hfits hzero hres
  exact PEqualNP.Outside.L_meta_29759_aux.main_proof K k basis bit hbit g s t T Z ht hfits hzero hres
