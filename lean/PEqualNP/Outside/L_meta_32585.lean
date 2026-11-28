import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PEqualNP.Outside.L_meta_32585_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open scoped Matrix

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

theorem zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem depthsOf_length (w : ℕ) (gs : List Gate) :
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

theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

theorem foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
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

theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
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

theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

theorem oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

theorem anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [zmod2_add_self]

theorem anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]
  ring

theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

theorem anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
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

theorem factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
    ∃ (rowVec : Fin K → Fin n → ZMod 2) (colVec : Fin K → Fin m → ZMod 2),
      ∀ i j, A i j = ∑ k : Fin K, rowVec k i * colVec k j := by
  let r := A.rank
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : Fin m, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let rowVec : Fin K → Fin n → ZMod 2 := fun k i =>
    if hk : k.val < r then (b ⟨k.val, hk⟩).val i else 0
  let colVec : Fin K → Fin m → ZMod 2 := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val, hk⟩ else 0
  refine ⟨rowVec, colVec, fun i j => ?_⟩
  have hrepr : ∑ t : Fin r, (b.repr ⟨fun i => A i j, hcol j⟩ t) • (b t) =
      ⟨fun i => A i j, hcol j⟩ := b.sum_repr ⟨fun i => A i j, hcol j⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i) hrepr
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin K, rowVec k i * colVec k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < r), rowVec k i * colVec k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [rowVec, colVec, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro k1 _ k2 _ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [rowVec, colVec, hlt, dite_true]
    rfl

theorem rank_add_le {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  obtain ⟨rA, cA, hA⟩ := factor_of_rank_le A le_rfl
  obtain ⟨rB, cB, hB⟩ := factor_of_rank_le B le_rfl
  let P : Matrix (Fin n) (Fin A.rank ⊕ Fin B.rank) (ZMod 2) := fun i k =>
    match k with
    | Sum.inl a => rA a i
    | Sum.inr b => rB b i
  let Q : Matrix (Fin A.rank ⊕ Fin B.rank) (Fin m) (ZMod 2) := fun k j =>
    match k with
    | Sum.inl a => cA a j
    | Sum.inr b => cB b j
  have hPQ : A + B = P * Q := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, hA i j, hB i j]
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (Fin A.rank ⊕ Fin B.rank → ZMod 2) :=
      LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card (Fin A.rank ⊕ Fin B.rank) := Module.finrank_pi (ZMod 2)
    _ = A.rank + B.rank := by simp

theorem card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
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

theorem dir_le {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents G C)
    (hd1 : (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1)
    (hcnt : C.gates.countP nlGate ≤ t) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t := by
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
      ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2), ∀ i j, val k i j = r i + s j := by
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
  have hNL_card : NL.card ≤ t := by
    calc NL.card
        ≤ (Finset.univ.filter (fun idx : Fin C.gates.length => nlGate (C.gates[idx.val]) = true)).card :=
          Finset.card_le_card (fun idx hidx => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hidx).2.1⟩)
      _ = C.gates.countP nlGate := card_filter_fin_eq_countP C.gates nlGate
      _ ≤ t := hcnt
  have hNL_outer : ∀ idx ∈ NL,
      ∃ (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2),
        anchor u v (val (n + m + idx.val)) =
          Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2 := by
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
    refine ⟨fun i => r1 i + r1 u, fun i => r2 i + r2 u, fun j => s2 j + s2 v, fun j => s1 j + s1 v, ?_⟩
    rw [hfun, anchor_add, anchor_split, zero_add, anchor_prod_split]
  have hspan : ∀ k : ℕ, dep k ≤ 1 →
      ∃ coeff : Fin C.gates.length → ZMod 2,
        anchor u v (val k) = ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hdk0 : dep k = 0
      · obtain ⟨r, s, hrs⟩ := hsplit_zero k hdk0
        refine ⟨fun _ => 0, ?_⟩
        have hfun : val k = fun i j => r i + s j := by funext i j; exact hrs i j
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
  obtain ⟨coeff, hcoeff⟩ := hspan C.output hd1
  have hAeq : anchor u v (fun i j => b2z (G i j)) = anchor u v (val C.output) := by
    congr 1
    funext i j
    unfold val
    rw [← hrep i j]
    rfl
  rw [hAeq, hcoeff]
  choose r1 r2 s1 s2 houter using fun idx : NL => hNL_outer idx.val idx.property
  let P : Matrix (Fin n) (NL ⊕ NL) (ZMod 2) := fun i k =>
    match k with
    | Sum.inl idx => coeff idx.val * r1 idx i
    | Sum.inr idx => coeff idx.val * r2 idx i
  let Q : Matrix (NL ⊕ NL) (Fin m) (ZMod 2) := fun k j =>
    match k with
    | Sum.inl idx => s1 idx j
    | Sum.inr idx => s2 idx j
  have hPQ : ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) = P * Q := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply]
    rw [← Finset.sum_attach NL]
    refine Finset.sum_congr rfl fun idx _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, houter idx, Matrix.add_apply,
      Matrix.vecMulVec_apply, P, Q]
    ring
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (NL ⊕ NL → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card (NL ⊕ NL) := Module.finrank_pi (ZMod 2)
    _ = NL.card + NL.card := by simp
    _ ≤ 2 * t := by omega

theorem rank_anchor_row_support {n m : ℕ} (u : Fin n) (v : Fin m)
    (R : Finset (Fin n)) (A : Fin n → Fin m → ZMod 2)
    (hsupp : ∀ i ∉ R, ∀ j, A i j = 0) :
    (anchor u v A).rank ≤ R.card := by
  by_cases hu : u ∈ R
  · let P : Matrix (Fin n) R (ZMod 2) := fun i r =>
      if r.val = u then (if i = u then 0 else 1) else (if i = r.val then 1 else 0)
    let Q : Matrix R (Fin m) (ZMod 2) := fun r j => A r.val j + A r.val v
    have hPQ : anchor u v A = P * Q := by
      ext i j
      rw [Matrix.mul_apply]
      by_cases hiu : i = u
      · subst hiu
        simp only [anchor]
        have hzero : A i j + A i v + A i j + A i v = (A i j + A i j) + (A i v + A i v) := by ring
        rw [hzero, zmod2_add_self, zmod2_add_self, add_zero]
        symm
        apply Finset.sum_eq_zero
        intro r _
        by_cases hru : r.val = i
        · simp [P, hru]
        · have hne : i ≠ r.val := Ne.symm hru
          simp [P, hru, hne]
      · let ru : R := ⟨u, hu⟩
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ru)]
        have hru_term : P i ru * Q ru j = A u j + A u v := by
          simp [P, Q, ru, hiu]
        rw [hru_term]
        by_cases hiR : i ∈ R
        · let ri : R := ⟨i, hiR⟩
          have hri_mem : ri ∈ Finset.univ.erase ru := by
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ ri⟩
            intro heq
            exact hiu (congrArg Subtype.val heq)
          have hrest : ∑ r ∈ Finset.univ.erase ru, P i r * Q r j = A i j + A i v := by
            rw [Finset.sum_eq_single ri]
            · simp [P, Q, ri, hiu]
            · intro r hr hne
              have hru' : r.val ≠ u := by
                intro heq
                exact (Finset.mem_erase.mp hr).1 (Subtype.ext heq)
              have hri' : i ≠ r.val := by
                intro heq
                exact hne (Subtype.ext heq.symm)
              simp [P, hru', hri']
            · intro hnot
              exact absurd hri_mem hnot
          rw [hrest]
          simp only [anchor]
          ring
        · have hrest : ∑ r ∈ Finset.univ.erase ru, P i r * Q r j = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            have hru' : r.val ≠ u := by
              intro heq
              exact (Finset.mem_erase.mp hr).1 (Subtype.ext heq)
            have hri' : i ≠ r.val := by
              intro heq
              exact hiR (heq ▸ r.property)
            simp [P, hru', hri']
          rw [hrest, add_zero]
          simp only [anchor, hsupp i hiR j, hsupp i hiR v, zero_add]
    rw [hPQ]
    calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
      _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
      _ ≤ Module.finrank (ZMod 2) (R → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
      _ = Fintype.card R := Module.finrank_pi (ZMod 2)
      _ = R.card := Fintype.card_coe R
  · let P : Matrix (Fin n) R (ZMod 2) := fun i r => if i = r.val then 1 else 0
    let Q : Matrix R (Fin m) (ZMod 2) := fun r j => A r.val j + A r.val v
    have hPQ : anchor u v A = P * Q := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [anchor, hsupp u hu j, hsupp u hu v, add_zero]
      by_cases hiR : i ∈ R
      · let ri : R := ⟨i, hiR⟩
        symm
        rw [Finset.sum_eq_single ri]
        · simp [P, Q, ri]
        · intro r _ hne
          have hri' : i ≠ r.val := fun heq => hne (Subtype.ext heq.symm)
          simp [P, hri']
        · intro hnot
          exact absurd (Finset.mem_univ ri) hnot
      · rw [hsupp i hiR j, hsupp i hiR v, add_zero]
        symm
        apply Finset.sum_eq_zero
        intro r _
        have hri' : i ≠ r.val := fun heq => hiR (heq ▸ r.property)
        simp [P, hri']
    rw [hPQ]
    calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
      _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
      _ ≤ Module.finrank (ZMod 2) (R → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
      _ = Fintype.card R := Module.finrank_pi (ZMod 2)
      _ = R.card := Fintype.card_coe R

theorem rank_anchor_col_support {n m : ℕ} (u : Fin n) (v : Fin m)
    (S : Finset (Fin m)) (A : Fin n → Fin m → ZMod 2)
    (hsupp : ∀ j ∉ S, ∀ i, A i j = 0) :
    (anchor u v A).rank ≤ S.card := by
  have htr : (anchor u v A)ᵀ = anchor v u (fun j i => A i j) := by
    ext j i
    simp only [Matrix.transpose_apply, anchor]
    ring
  rw [← Matrix.rank_transpose, htr]
  exact rank_anchor_row_support v u S (fun j i => A i j) hsupp

theorem sum_option_eq {α β : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid β]
    (f : Option α → β) :
    ∑ i : Option α, f i = f none + ∑ x : α, f (some x) := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ none)]
  congr 1
  refine Finset.sum_bij (fun (i : Option α) hi => Option.get i (by
    cases i with
    | none => exact absurd rfl (Finset.mem_erase.mp hi).1
    | some _ => exact rfl)) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro i1 hi1 i2 hi2 heq
    cases i1 with
    | none => exact absurd rfl (Finset.mem_erase.mp hi1).1
    | some a1 =>
      cases i2 with
      | none => exact absurd rfl (Finset.mem_erase.mp hi2).1
      | some a2 =>
        simp at heq
        rw [heq]
  · intro x _
    refine ⟨some x, Finset.mem_erase.mpr ⟨Option.some_ne_none x, Finset.mem_univ _⟩, rfl⟩
  · intro i hi
    cases i with
    | none => exact absurd rfl (Finset.mem_erase.mp hi).1
    | some a => rfl

theorem sum_fin_eq_range {s : ℕ} (f : ℕ → ℕ) :
    ∑ k : Fin s, f k.val = ∑ k ∈ Finset.range s, f k := by
  refine Finset.sum_bij (fun (k : Fin s) _ => k.val) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_range.mpr k.isLt
  · intro k1 _ k2 _ heq
    exact Fin.ext heq
  · intro k hk
    exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl

def deltaBit {n m : ℕ} (T : Fin n → Fin m → Bool) (u x : Fin n) (c : Fin m) : ℕ :=
  if T x c ≠ T u c then 1 else 0

def distNat {n m : ℕ} (T : Fin n → Fin m → Bool) (i j : Fin n) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card

theorem distNat_eq_sum_delta {n m : ℕ} (T : Fin n → Fin m → Bool) (u x : Fin n) :
    distNat T u x = ∑ c : Fin m, deltaBit T u x c := by
  unfold distNat deltaBit
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : T u c = T x c
  · simp [h]
  · have h1 : T u c ≠ T x c := h
    have h2 : T x c ≠ T u c := Ne.symm h
    simp [h1, h2]

theorem distNat_halving_nat {n m : ℕ} (T : Fin n → Fin m → Bool) (u x y : Fin n) :
    distNat T u x + distNat T u y =
      distNat T x y + 2 * ∑ c : Fin m, deltaBit T u x c * deltaBit T u y c := by
  unfold distNat deltaBit
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  cases T u c <;> cases T x c <;> cases T y c <;> decide

theorem mod_halving_nat {M a b c k : ℕ} (hM : 0 < M) (hab : a + b = c + 2 * k) :
    ((a % (2 * M) + b % (2 * M) + 2 * M - c % (2 * M)) % (2 * M)) / 2 = k % M := by
  have h2M : 0 < 2 * M := by omega
  have hcle : c % (2 * M) ≤ a % (2 * M) + b % (2 * M) + 2 * M := by
    have := Nat.mod_lt c h2M
    omega
  have ha_eq : (a : ℤ) = (2 * M : ℤ) * (a / (2 * M) : ℤ) + (a % (2 * M) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a (2 * M)).symm
  have hb_eq : (b : ℤ) = (2 * M : ℤ) * (b / (2 * M) : ℤ) + (b % (2 * M) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod b (2 * M)).symm
  have hc_eq : (c : ℤ) = (2 * M : ℤ) * (c / (2 * M) : ℤ) + (c % (2 * M) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod c (2 * M)).symm
  have hk_eq : (k : ℤ) = (M : ℤ) * (k / M : ℤ) + (k % M : ℤ) := by
    exact_mod_cast (Nat.div_add_mod k M).symm
  have hab_z : (a : ℤ) + (b : ℤ) = (c : ℤ) + 2 * (k : ℤ) := by exact_mod_cast hab
  set lhs : ℕ := a % (2 * M) + b % (2 * M) + 2 * M - c % (2 * M)
  have hlhs_z : (lhs : ℤ) = (a % (2 * M) : ℤ) + (b % (2 * M) : ℤ) + (2 * M : ℤ) - (c % (2 * M) : ℤ) := by
    have h1 : (lhs : ℤ) + (c % (2 * M) : ℤ) = (a % (2 * M) : ℤ) + (b % (2 * M) : ℤ) + (2 * M : ℤ) := by
      exact_mod_cast Nat.sub_add_cancel hcle
    linarith
  have hdiff : (lhs : ℤ) = (2 * (k % M) : ℤ) +
      (2 * M : ℤ) * (1 + (c / (2 * M) : ℤ) + (k / M : ℤ) - (a / (2 * M) : ℤ) - (b / (2 * M) : ℤ)) := by
    linarith
  have hmod_z : (lhs : ℤ) % (2 * M : ℤ) = (2 * (k % M) : ℤ) := by
    rw [hdiff, Int.add_mul_emod_self_left]
    apply Int.emod_eq_of_lt
    · omega
    · have := Nat.mod_lt k hM
      omega
  have hmod_nat : lhs % (2 * M) = 2 * (k % M) := by
    have h1 : ((lhs % (2 * M) : ℕ) : ℤ) = (lhs : ℤ) % (2 * M : ℤ) := by
      push_cast
      rfl
    rw [hmod_z] at h1
    exact_mod_cast h1
  rw [hmod_nat]
  exact Nat.mul_div_right (k % M) (by omega)

theorem natCast_mod_pow_two_succ {h a : ℕ} :
    ((a % (2 ^ (h + 1)) : ℕ) : ZMod (2 ^ h)) = (a : ZMod (2 ^ h)) := by
  have hdiv := Nat.div_add_mod a (2 ^ (h + 1))
  have hcast := congrArg (fun t : ℕ => (t : ZMod (2 ^ h))) hdiv
  simp only [Nat.cast_add, Nat.cast_mul, pow_succ, mul_assoc] at hcast
  have hz : ((2 ^ h : ℕ) : ZMod (2 ^ h)) = 0 := ZMod.natCast_self (2 ^ h)
  rw [hz, zero_mul, zero_add] at hcast
  exact hcast

theorem natCast_mod_pow_two {h a : ℕ} :
    ((a % (2 ^ h) : ℕ) : ZMod (2 ^ h)) = (a : ZMod (2 ^ h)) := by
  have hdiv := Nat.div_add_mod a (2 ^ h)
  have hcast := congrArg (fun t : ℕ => (t : ZMod (2 ^ h))) hdiv
  simp only [Nat.cast_add, Nat.cast_mul] at hcast
  have hz : ((2 ^ h : ℕ) : ZMod (2 ^ h)) = 0 := ZMod.natCast_self (2 ^ h)
  rw [hz, zero_mul, zero_add] at hcast
  exact hcast

def M0Mat {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) :
    Matrix (Option (Fin n)) (Fin m) ℤ := fun i c =>
  match i with
  | none => 1
  | some x => (deltaBit T u x c : ℤ)

def LMat {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v0 : Fin m) :
    Matrix (Option (Fin n)) (Fin m) ℤ := fun i c =>
  match i with
  | none => 1
  | some x => if deltaBit T u x v0 = 1 then 1 - (deltaBit T u x c : ℤ) else (deltaBit T u x c : ℤ)

def UMat {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v0 : Fin m) (h : ℕ) :
    Matrix (Option (Fin n)) (Option (Fin n)) (ZMod (2 ^ h)) := fun i j =>
  match i, j with
  | none, none => 1
  | none, some _ => 0
  | some x, none => if deltaBit T u x v0 = 1 then 1 else 0
  | some x, some y => if x = y then (if deltaBit T u x v0 = 1 then -1 else 1) else 0

theorem UMat_mul_self {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v0 : Fin m) (h : ℕ) :
    UMat T u v0 h * UMat T u v0 h = 1 := by
  ext i j
  rw [Matrix.mul_apply, sum_option_eq]
  cases i with
  | none =>
    cases j with
    | none =>
      simp [UMat]
    | some y =>
      simp [UMat]
  | some x =>
    cases j with
    | none =>
      simp only [UMat, Matrix.one_apply, reduceCtorEq, ite_false]
      rw [Finset.sum_eq_single x]
      · by_cases hdx : deltaBit T u x v0 = 1 <;> simp [hdx]
      · intro z _ hzx
        have hxz : x ≠ z := Ne.symm hzx
        simp [hxz]
      · intro hnot
        exact absurd (Finset.mem_univ x) hnot
    | some y =>
      simp only [UMat, mul_zero, zero_add]
      rw [Finset.sum_eq_single x]
      · by_cases hxy : x = y
        · subst hxy
          by_cases hdx : deltaBit T u x v0 = 1 <;> simp [hdx]
        · have hne : (some x : Option (Fin n)) ≠ some y := fun heq => hxy (Option.some.inj heq)
          simp [hxy, hne]
      · intro z _ hzx
        have hxz : x ≠ z := Ne.symm hzx
        simp [hxz]
      · intro hnot
        exact absurd (Finset.mem_univ x) hnot

theorem M0_eq_U_mul_L {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v0 : Fin m) (h : ℕ) :
    (M0Mat T u).map (Int.cast : ℤ → ZMod (2 ^ h)) =
      UMat T u v0 h * (LMat T u v0).map (Int.cast : ℤ → ZMod (2 ^ h)) := by
  ext i c
  rw [Matrix.mul_apply, sum_option_eq]
  cases i with
  | none =>
    simp [M0Mat, UMat, LMat]
  | some x =>
    simp only [Matrix.map_apply, M0Mat, UMat, LMat]
    rw [Finset.sum_eq_single x]
    · by_cases hdx : deltaBit T u x v0 = 1
      · simp [hdx]
      · simp [hdx]
    · intro z _ hzx
      have hxz : x ≠ z := Ne.symm hzx
      simp [hxz]
    · intro hnot
      exact absurd (Finset.mem_univ x) hnot

theorem card_image_conj_eq {α : Type*} [Fintype α] [DecidableEq α] {R : Type*}
    [CommRing R] [Fintype R] [DecidableEq R]
    (U H : Matrix α α R) (hU : U * U = 1) :
    (Finset.univ.image (fun x : α → R => (U * H * Uᵀ).mulVec x)).card =
      (Finset.univ.image (fun x : α → R => H.mulVec x)).card := by
  have hUT : Uᵀ * Uᵀ = 1 := by
    rw [← Matrix.transpose_mul, hU, Matrix.transpose_one]
  have hU_inj : Function.Injective U.mulVec := by
    intro a b hab
    have h1 := congrArg U.mulVec hab
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, Matrix.one_mulVec] at h1
    exact h1
  have himg_eq : Finset.univ.image (fun x : α → R => (U * H * Uᵀ).mulVec x) =
      (Finset.univ.image (fun x : α → R => H.mulVec x)).image U.mulVec := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨H.mulVec (Uᵀ.mulVec x), ⟨Uᵀ.mulVec x, rfl⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
      refine ⟨Uᵀ.mulVec y, ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hUT, Matrix.mul_one,
        ← Matrix.mulVec_mulVec]
  rw [himg_eq, Finset.card_image_of_injective _ hU_inj]

theorem LMat_mod2_eq_anchor {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v0 : Fin m)
    (x : Fin n) (c : Fin m) :
    ((LMat T u v0 (some x) c : ℤ) : ZMod 2) = anchor u v0 (fun i j => b2z (T i j)) x c := by
  simp only [LMat, deltaBit, anchor]
  let d : Bool → Bool → ℕ := fun a b => if a ≠ b then 1 else 0
  have aux : ∀ a b c' d' : Bool,
      (((if d c' d' = 1 then 1 - (d a b : ℤ) else (d a b : ℤ)) : ℤ) : ZMod 2) =
      b2z a + b2z c' + b2z b + b2z d' := by
    decide
  exact aux (T x c) (T u c) (T x v0) (T u v0)

theorem LMat_zero_or_one {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v0 : Fin m)
    (x : Fin n) (c : Fin m) :
    LMat T u v0 (some x) c = 0 ∨ LMat T u v0 (some x) c = 1 := by
  simp only [LMat, deltaBit]
  by_cases h1 : T x v0 ≠ T u v0 <;> by_cases h2 : T x c ≠ T u c <;> simp [h1, h2]

theorem parity_prod_eq {r : ℕ} (S : Finset (Fin r)) (b : Fin r → Bool) :
    1 - 2 * (((S.filter (fun a => b a = true)).card % 2 : ℕ) : ℤ) =
      ∏ a ∈ S, (1 - 2 * (if b a then (1 : ℤ) else 0)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, ← ih, Finset.filter_insert]
    cases hb : b a
    · simp
    · simp only [ite_true]
      have ha' : a ∉ S.filter (fun x => b x = true) := fun hm => ha (Finset.mem_filter.mp hm).1
      rw [Finset.card_insert_of_notMem ha']
      set k := (S.filter (fun x => b x = true)).card
      have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rcases hk with h0 | h1
      · have hk1 : (k + 1) % 2 = 1 := by omega
        rw [h0, hk1]
        norm_num
      · have hk1 : (k + 1) % 2 = 0 := by omega
        rw [h1, hk1]
        norm_num

theorem prod_one_sub_two_eq {r : ℕ} (S : Finset (Fin r)) (β : Fin r → ℤ) :
    ∏ a ∈ S, (1 - 2 * β a) =
      ∑ K ∈ S.powerset, (-2 : ℤ) ^ K.card * ∏ a ∈ K, β a := by
  have h1 : ∏ a ∈ S, (1 - 2 * β a) = ∏ a ∈ S, ((-2 * β a) + 1) := by
    refine Finset.prod_congr rfl fun a _ => by ring
  rw [h1, Finset.prod_add_one]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem parity_eq_powerset_sum {r : ℕ} (S : Finset (Fin r)) (b : Fin r → Bool) :
    (((S.filter (fun a => b a = true)).card % 2 : ℕ) : ℤ) =
      ∑ K ∈ S.powerset.erase ∅,
        (2 : ℤ) ^ (K.card - 1) * ((-1 : ℤ) ^ (K.card - 1) * ∏ a ∈ K, (if b a then (1 : ℤ) else 0)) := by
  set β : Fin r → ℤ := fun a => if b a then 1 else 0
  set x : ℤ := (((S.filter (fun a => b a = true)).card % 2 : ℕ) : ℤ)
  have h1 : 1 - 2 * x = ∑ K ∈ S.powerset, (-2 : ℤ) ^ K.card * ∏ a ∈ K, β a := by
    rw [parity_prod_eq S b, prod_one_sub_two_eq S β]
  have hmem : (∅ : Finset (Fin r)) ∈ S.powerset := Finset.empty_mem_powerset S
  rw [← Finset.add_sum_erase S.powerset _ hmem] at h1
  simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one] at h1
  have h2 : (-2 : ℤ) * x = ∑ K ∈ S.powerset.erase ∅, (-2 : ℤ) ^ K.card * ∏ a ∈ K, β a := by
    linarith
  have h3 : (-2 : ℤ) *
      (∑ K ∈ S.powerset.erase ∅, (2 : ℤ) ^ (K.card - 1) * ((-1 : ℤ) ^ (K.card - 1) * ∏ a ∈ K, β a)) =
      ∑ K ∈ S.powerset.erase ∅, (-2 : ℤ) ^ K.card * ∏ a ∈ K, β a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK => ?_
    have hKne : K ≠ ∅ := (Finset.mem_erase.mp hK).1
    have hpos : 1 ≤ K.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hKne)
    have hpow : (-2 : ℤ) * ((2 : ℤ) ^ (K.card - 1) * (-1 : ℤ) ^ (K.card - 1)) = (-2 : ℤ) ^ K.card := by
      rw [← mul_pow]
      have hmul : (2 : ℤ) * (-1 : ℤ) = (-2 : ℤ) := by norm_num
      rw [hmul, ← pow_succ']
      congr 1
      omega
    calc (-2 : ℤ) * ((2 : ℤ) ^ (K.card - 1) * ((-1 : ℤ) ^ (K.card - 1) * ∏ a ∈ K, β a))
        = ((-2 : ℤ) * ((2 : ℤ) ^ (K.card - 1) * (-1 : ℤ) ^ (K.card - 1))) * ∏ a ∈ K, β a := by ring
      _ = (-2 : ℤ) ^ K.card * ∏ a ∈ K, β a := by rw [hpow]
  linarith

def wt2 {r : ℕ} (K : Finset (Fin r)) : ℕ :=
  if K = ∅ then 0 else K.card - 1

def Ffun (r s : ℕ) : ℕ :=
  (Finset.range s).sum (fun k => (s - k) * Nat.choose r (k + 1))

theorem pow_two_mul_zmod_eq_of_mod {s k : ℕ} (hk : k ≤ s) (z : ZMod (2 ^ s)) :
    (2 : ZMod (2 ^ s)) ^ k * z =
      (2 : ZMod (2 ^ s)) ^ k * (((z.val % (2 ^ (s - k)) : ℕ) : ZMod (2 ^ s))) := by
  have : NeZero (2 ^ s) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))⟩
  have hz : z = (z.val : ZMod (2 ^ s)) := (ZMod.natCast_zmod_val z).symm
  have hdiv : z.val = 2 ^ (s - k) * (z.val / 2 ^ (s - k)) + z.val % 2 ^ (s - k) :=
    (Nat.div_add_mod z.val (2 ^ (s - k))).symm
  conv_lhs => rw [hz, hdiv]
  push_cast
  have hzero : (2 : ZMod (2 ^ s)) ^ k * (2 : ZMod (2 ^ s)) ^ (s - k) = 0 := by
    rw [← pow_add, Nat.add_sub_of_le hk]
    have h1 : (2 : ZMod (2 ^ s)) ^ s = ((2 ^ s : ℕ) : ZMod (2 ^ s)) := by push_cast; rfl
    rw [h1, ZMod.natCast_self]
  calc (2 : ZMod (2 ^ s)) ^ k *
        ((2 : ZMod (2 ^ s)) ^ (s - k) * ((z.val / 2 ^ (s - k) : ℕ) : ZMod (2 ^ s)) +
          ((z.val % 2 ^ (s - k) : ℕ) : ZMod (2 ^ s)))
      = ((2 : ZMod (2 ^ s)) ^ k * (2 : ZMod (2 ^ s)) ^ (s - k)) *
          ((z.val / 2 ^ (s - k) : ℕ) : ZMod (2 ^ s)) +
          (2 : ZMod (2 ^ s)) ^ k * ((z.val % 2 ^ (s - k) : ℕ) : ZMod (2 ^ s)) := by ring
    _ = (2 : ZMod (2 ^ s)) ^ k * ((z.val % 2 ^ (s - k) : ℕ) : ZMod (2 ^ s)) := by
        rw [hzero, zero_mul, zero_add]

theorem card_image_mulVec_le_of_powerset_factor
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {r s : ℕ}
    (A : α → Finset (Fin r) → ℤ) (B : Finset (Fin r) → β → ℤ)
    (M : Matrix α β (ZMod (2 ^ s)))
    (hM : ∀ i j, M i j =
      ((∑ K ∈ (Finset.univ : Finset (Fin r)).powerset,
          (2 : ℤ) ^ (wt2 K) * A i K * B K j : ℤ) : ZMod (2 ^ s))) :
    (Finset.univ.image (fun y : β → ZMod (2 ^ s) => M.mulVec y)).card ≤
      2 ^ (s + Ffun r s) := by
  have : NeZero (2 ^ s) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))⟩
  let Code := ZMod (2 ^ s) ×
    ((k : Fin s) → ((Finset.univ : Finset (Fin r)).powersetCard (k.val + 1)) → Fin (2 ^ (s - k.val)))
  let enc : (β → ZMod (2 ^ s)) → Code := fun y =>
    (∑ j : β, (B ∅ j : ZMod (2 ^ s)) * y j,
     fun k K => ⟨((∑ j : β, (B K.val j : ZMod (2 ^ s)) * y j).val) % (2 ^ (s - k.val)),
       Nat.mod_lt _ (Nat.pow_pos (by omega))⟩)
  have hmul_expand : ∀ (y : β → ZMod (2 ^ s)) (i : α),
      (M.mulVec y) i =
        ∑ K ∈ (Finset.univ : Finset (Fin r)).powerset,
          (A i K : ZMod (2 ^ s)) *
            ((2 : ZMod (2 ^ s)) ^ (wt2 K) * ∑ j : β, (B K j : ZMod (2 ^ s)) * y j) := by
    intro y i
    simp only [Matrix.mulVec, dotProduct]
    have h1 : ∑ j : β, M i j * y j =
        ∑ j : β, ∑ K ∈ (Finset.univ : Finset (Fin r)).powerset,
          ((2 : ZMod (2 ^ s)) ^ (wt2 K) * (A i K : ZMod (2 ^ s)) * (B K j : ZMod (2 ^ s))) * y j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM i j]
      push_cast
      rw [Finset.sum_mul]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have henc_det : ∀ y1 y2 : β → ZMod (2 ^ s), enc y1 = enc y2 → M.mulVec y1 = M.mulVec y2 := by
    intro y1 y2 heq
    ext i
    rw [hmul_expand y1 i, hmul_expand y2 i]
    refine Finset.sum_congr rfl fun K _ => ?_
    congr 1
    by_cases hKe : K = ∅
    · subst hKe
      have h1 : (enc y1).1 = (enc y2).1 := congrArg Prod.fst heq
      simpa [enc] using congrArg (fun t => (2 : ZMod (2 ^ s)) ^ (wt2 (∅ : Finset (Fin r))) * t) h1
    · by_cases hlt : s < K.card
      · have hle : s ≤ wt2 K := by
          simp only [wt2, hKe, ite_false]
          omega
        have hzero : (2 : ZMod (2 ^ s)) ^ (wt2 K) = 0 := by
          have hdecomp : wt2 K = s + (wt2 K - s) := by omega
          rw [hdecomp, pow_add]
          have h1 : (2 : ZMod (2 ^ s)) ^ s = ((2 ^ s : ℕ) : ZMod (2 ^ s)) := by push_cast; rfl
          rw [h1, ZMod.natCast_self, zero_mul]
        rw [hzero, zero_mul, zero_mul]
      · have hpos : 1 ≤ K.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hKe)
        have hklts : K.card - 1 < s := by omega
        let k : Fin s := ⟨K.card - 1, hklts⟩
        have hKmem : K ∈ (Finset.univ : Finset (Fin r)).powersetCard (k.val + 1) := by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ K, by simp [k]; omega⟩
        have hwt : wt2 K = k.val := by simp [wt2, hKe, k]
        rw [hwt]
        have h2 := congrArg (fun c : Code => (c.2 k ⟨K, hKmem⟩).val) heq
        simp only [enc] at h2
        rw [pow_two_mul_zmod_eq_of_mod (Nat.le_of_lt k.isLt)
            (∑ j : β, (B K j : ZMod (2 ^ s)) * y1 j),
          pow_two_mul_zmod_eq_of_mod (Nat.le_of_lt k.isLt)
            (∑ j : β, (B K j : ZMod (2 ^ s)) * y2 j), h2]
  have hcard_le : (Finset.univ.image (fun y : β → ZMod (2 ^ s) => M.mulVec y)).card ≤
      Fintype.card Code := by
    have hsub : ∀ v ∈ Finset.univ.image (fun y : β → ZMod (2 ^ s) => M.mulVec y),
        ∃ y, M.mulVec y = v := by
      intro v hv
      obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hv
      exact ⟨y, hy⟩
    let f : (α → ZMod (2 ^ s)) → Code := fun v =>
      if hv : v ∈ Finset.univ.image (fun y : β → ZMod (2 ^ s) => M.mulVec y) then
        enc (Classical.choose (hsub v hv))
      else
        enc 0
    calc (Finset.univ.image (fun y : β → ZMod (2 ^ s) => M.mulVec y)).card
        ≤ (Finset.univ : Finset Code).card := by
          apply Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _)
          intro v1 hv1 v2 hv2 hfeq
          rw [Finset.mem_coe] at hv1 hv2
          dsimp only [f] at hfeq
          simp only [hv1, hv2, dite_true] at hfeq
          rw [← Classical.choose_spec (hsub v1 hv1), ← Classical.choose_spec (hsub v2 hv2)]
          exact henc_det _ _ hfeq
      _ = Fintype.card Code := Finset.card_univ
  have hcode_card : Fintype.card Code = 2 ^ (s + Ffun r s) := by
    dsimp only [Code]
    rw [Fintype.card_prod, ZMod.card (2 ^ s), Fintype.card_pi]
    have hprod : ∏ k : Fin s,
        Fintype.card (((Finset.univ : Finset (Fin r)).powersetCard (k.val + 1)) → Fin (2 ^ (s - k.val))) =
        2 ^ Ffun r s := by
      have hterm : ∀ k : Fin s,
          Fintype.card (((Finset.univ : Finset (Fin r)).powersetCard (k.val + 1)) → Fin (2 ^ (s - k.val))) =
          2 ^ ((s - k.val) * Nat.choose r (k.val + 1)) := by
        intro k
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
          Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      simp_rw [hterm]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      rw [sum_fin_eq_range (fun k => (s - k) * Nat.choose r (k + 1))]
      rfl
    rw [hprod, ← pow_add]
  rw [hcode_card] at hcard_le
  exact hcard_le

theorem liftP_intCast {h p q : ℕ} (hpq : p + q = h) (K : ℤ) :
    (((2 ^ p : ℤ) * K : ℤ) : ZMod (2 ^ h)) =
      ((2 ^ p * (K : ZMod (2 ^ q)).val : ℕ) : ZMod (2 ^ h)) := by
  have : NeZero (2 ^ q) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))⟩
  have hrhs : ((2 ^ p * (K : ZMod (2 ^ q)).val : ℕ) : ZMod (2 ^ h)) =
      (((2 ^ p : ℤ) * ((K : ZMod (2 ^ q)).val : ℤ) : ℤ) : ZMod (2 ^ h)) := by
    push_cast
    rfl
  rw [hrhs, ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [ZMod.val_intCast]
  have hdiv : ((2 ^ q : ℕ) : ℤ) * (K / ((2 ^ q : ℕ) : ℤ)) + K % ((2 ^ q : ℕ) : ℤ) = K :=
    Int.mul_ediv_add_emod K ((2 ^ q : ℕ) : ℤ)
  refine ⟨-(K / ((2 ^ q : ℕ) : ℤ)), ?_⟩
  have hpow : ((2 ^ h : ℕ) : ℤ) = (2 ^ p : ℤ) * ((2 ^ q : ℕ) : ℤ) := by
    rw [← hpq, pow_add]
    push_cast
    rfl
  rw [hpow]
  have hsub : K % ((2 ^ q : ℕ) : ℤ) - K = -(((2 ^ q : ℕ) : ℤ) * (K / ((2 ^ q : ℕ) : ℤ))) := by
    linarith
  calc (2 ^ p : ℤ) * (K % ((2 ^ q : ℕ) : ℤ)) - (2 ^ p : ℤ) * K
      = (2 ^ p : ℤ) * (K % ((2 ^ q : ℕ) : ℤ) - K) := by ring
    _ = (2 ^ p : ℤ) * (-(((2 ^ q : ℕ) : ℤ) * (K / ((2 ^ q : ℕ) : ℤ)))) := by rw [hsub]
    _ = (2 ^ p : ℤ) * ((2 ^ q : ℕ) : ℤ) * -(K / ((2 ^ q : ℕ) : ℤ)) := by ring

theorem main_proof (n m h : ℕ) (T P : Fin n → Fin m → Bool) (u : Fin n)
    (R : Finset (Fin n)) (S : Finset (Fin m)) (C : Circuit)
    (hTP : ∀ i ∉ R, ∀ j ∉ S, T i j = P i j)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents P C)
    (hd1 : (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1) :
    let d := fun i j : Fin n => (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card % (2 ^ (h + 1))
    let I := Option (Fin n)
    let G : Matrix I I (ZMod (2 ^ h)) := fun i j =>
      let x := i.getD u
      let y := j.getD u
      if i.isNone then (if j.isNone then (m : ZMod (2 ^ h)) else (d u y : ZMod (2 ^ h)))
      else if j.isNone then (d u x : ZMod (2 ^ h))
      else (((((d u x + d u y + 2 ^ (h + 1) - d x y) % (2 ^ (h + 1))) / 2 : ℕ)) : ZMod (2 ^ h))
    let r := 2 * C.gates.countP nlGate + R.card + S.card
    (Finset.univ.image (fun x : I → ZMod (2 ^ h) => G.mulVec x)).card ≤
      2 ^ (h + Ffun r (h / 2) + Ffun r (h - h / 2)) := by
  intro d I G r
  by_cases hh0 : h = 0
  · subst hh0
    have hcard1 : (Finset.univ.image (fun x : I → ZMod (2 ^ 0) => G.mulVec x)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a _ b _
      ext i
      exact Subsingleton.elim (α := ZMod 1) (a i) (b i)
    exact le_trans hcard1 Nat.one_le_two_pow
  by_cases hm0 : m = 0
  · subst hm0
    have hG0 : G = 0 := by
      ext i j
      have hd0 : ∀ a b : Fin n, d a b = 0 := by
        intro a b
        simp [d]
      cases i <;> cases j <;> simp [G, hd0]
    have hcard1 : (Finset.univ.image (fun x : I → ZMod (2 ^ h) => G.mulVec x)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨xa, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨xb, _, rfl⟩ := Finset.mem_image.mp hb
      simp [hG0]
    exact le_trans hcard1 Nat.one_le_two_pow
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  let v0 : Fin m := ⟨0, hm_pos⟩
  let M0_h : Matrix I (Fin m) (ZMod (2 ^ h)) := (M0Mat T u).map (Int.cast : ℤ → ZMod (2 ^ h))
  have hG_eq : G = M0_h * M0_hᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    cases i with
    | none =>
      cases j with
      | none =>
        simp [G, M0_h, M0Mat]
      | some y =>
        simp only [G, M0_h, M0Mat, Option.isNone_none, Option.isNone_some, Option.getD_some,
          ite_true, Matrix.transpose_apply, Matrix.map_apply, Int.cast_one, one_mul,
          Int.cast_natCast]
        change ((distNat T u y % (2 ^ (h + 1)) : ℕ) : ZMod (2 ^ h)) = _
        rw [natCast_mod_pow_two_succ, distNat_eq_sum_delta T u y, Nat.cast_sum]
    | some x =>
      cases j with
      | none =>
        simp only [G, M0_h, M0Mat, Option.isNone_none, Option.isNone_some, Option.getD_some,
          ite_true, Matrix.transpose_apply, Matrix.map_apply, Int.cast_one, mul_one,
          Int.cast_natCast]
        change ((distNat T u x % (2 ^ (h + 1)) : ℕ) : ZMod (2 ^ h)) = _
        rw [natCast_mod_pow_two_succ, distNat_eq_sum_delta T u x, Nat.cast_sum]
      | some y =>
        simp only [G, M0_h, M0Mat, Option.isNone_some, Option.getD_some,
          Matrix.transpose_apply, Matrix.map_apply, Int.cast_natCast]
        have h2pow : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
        have hhalv := mod_halving_nat (M := 2 ^ h) (Nat.pow_pos (by omega))
          (distNat_halving_nat T u x y)
        have hdg : (((d u x + d u y + 2 ^ (h + 1) - d x y) % (2 ^ (h + 1))) / 2) =
            (∑ c : Fin m, deltaBit T u x c * deltaBit T u y c) % (2 ^ h) := by
          simpa only [d, distNat, h2pow] using hhalv
        rw [hdg, natCast_mod_pow_two]
        push_cast
        rfl
  let L_Z : Matrix I (Fin m) ℤ := LMat T u v0
  let L_h : Matrix I (Fin m) (ZMod (2 ^ h)) := L_Z.map (Int.cast : ℤ → ZMod (2 ^ h))
  let U : Matrix I I (ZMod (2 ^ h)) := UMat T u v0 h
  let H : Matrix I I (ZMod (2 ^ h)) := L_h * L_hᵀ
  have hG_conj : G = U * H * Uᵀ := by
    rw [hG_eq, show M0_h = U * L_h from M0_eq_U_mul_L T u v0 h, Matrix.transpose_mul]
    simp only [H, Matrix.mul_assoc]
  have hcard_GH : (Finset.univ.image (fun x : I → ZMod (2 ^ h) => G.mulVec x)).card =
      (Finset.univ.image (fun x : I → ZMod (2 ^ h) => H.mulVec x)).card := by
    rw [hG_conj]
    exact card_image_conj_eq U H (UMat_mul_self T u v0 h)
  let L2 : Matrix (Fin n) (Fin m) (ZMod 2) := fun x c => ((L_Z (some x) c : ℤ) : ZMod 2)
  have hL2_rank : L2.rank ≤ r := by
    have hL2_anch : L2 = anchor u v0 (fun x c => b2z (T x c)) := by
      ext x c
      exact LMat_mod2_eq_anchor T u v0 x c
    let E : Fin n → Fin m → ZMod 2 := fun x c => b2z (T x c) + b2z (P x c)
    let ER : Fin n → Fin m → ZMod 2 := fun x c => if x ∈ R then E x c else 0
    let ES : Fin n → Fin m → ZMod 2 := fun x c => if x ∉ R ∧ c ∈ S then E x c else 0
    have hT_split : (fun x c => b2z (T x c)) =
        fun x c => (b2z (P x c) + ER x c) + ES x c := by
      funext x c
      by_cases hxR : x ∈ R
      · simp only [ER, ES, E, hxR, ite_true, not_true_eq_false, false_and, ite_false, add_zero]
        have h1 : b2z (P x c) + (b2z (T x c) + b2z (P x c)) =
            b2z (T x c) + (b2z (P x c) + b2z (P x c)) := by ring
        rw [h1, zmod2_add_self, add_zero]
      · by_cases hcS : c ∈ S
        · simp only [ER, ES, E, hxR, hcS, not_false_eq_true, and_self, ite_false, ite_true, add_zero]
          have h1 : b2z (P x c) + (b2z (T x c) + b2z (P x c)) =
              b2z (T x c) + (b2z (P x c) + b2z (P x c)) := by ring
          rw [h1, zmod2_add_self, add_zero]
        · simp only [ER, ES, hxR, hcS, and_false, ite_false, add_zero, hTP x hxR c hcS]
    rw [hL2_anch, hT_split, anchor_add, anchor_add]
    have hP_rk : (anchor u v0 (fun x c => b2z (P x c))).rank ≤ 2 * C.gates.countP nlGate :=
      dir_le P u v0 (C.gates.countP nlGate) C hlen hrb hrep hd1 le_rfl
    have hR_rk : (anchor u v0 ER).rank ≤ R.card :=
      rank_anchor_row_support u v0 R ER (fun i hi j => by simp [ER, hi])
    have hS_rk : (anchor u v0 ES).rank ≤ S.card :=
      rank_anchor_col_support u v0 S ES (fun j hj i => by simp [ES, hj])
    calc (anchor u v0 (fun x c => b2z (P x c)) + anchor u v0 ER + anchor u v0 ES).rank
        ≤ (anchor u v0 (fun x c => b2z (P x c)) + anchor u v0 ER).rank + (anchor u v0 ES).rank :=
          rank_add_le _ _
      _ ≤ (anchor u v0 (fun x c => b2z (P x c))).rank + (anchor u v0 ER).rank + (anchor u v0 ES).rank :=
          Nat.add_le_add_right (rank_add_le _ _) _
      _ ≤ 2 * C.gates.countP nlGate + R.card + S.card := by omega
  obtain ⟨rowVec, colVec, hfac⟩ := factor_of_rank_le L2 hL2_rank
  let uBit : Fin n → Fin r → Bool := fun x a => decide (rowVec a x = 1)
  let wBit : Fin r → Fin m → Bool := fun a c => decide (colVec a c = 1)
  have hL_parity : ∀ x c, L_Z (some x) c =
      (((Finset.univ.filter (fun a : Fin r => (uBit x a && wBit a c) = true)).card % 2 : ℕ) : ℤ) := by
    intro x c
    have hmod2 : ((L_Z (some x) c : ℤ) : ZMod 2) =
        (((Finset.univ.filter (fun a : Fin r => (uBit x a && wBit a c) = true)).card : ℕ) : ZMod 2) := by
      change L2 x c = _
      rw [hfac x c, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hu1 : b2z (uBit x a) = rowVec a x := by
        simpa [uBit, b2z] using zmod2_ite_eq (rowVec a x)
      have hw1 : b2z (wBit a c) = colVec a c := by
        simpa [wBit, b2z] using zmod2_ite_eq (colVec a c)
      rw [← hu1, ← hw1, ← b2z_and]
      cases uBit x a && wBit a c <;> simp [b2z]
    have hval := congrArg ZMod.val hmod2
    rw [ZMod.val_natCast] at hval
    rcases LMat_zero_or_one T u v0 x c with h0 | h1
    · change L_Z (some x) c = 0 at h0
      rw [h0] at hval ⊢
      have h0' : (0 : ℕ) = (Finset.univ.filter (fun a : Fin r => (uBit x a && wBit a c) = true)).card % 2 := by
        simpa using hval
      exact_mod_cast h0'
    · change L_Z (some x) c = 1 at h1
      rw [h1] at hval ⊢
      have hv1 : ZMod.val (1 : ZMod 2) = 1 := rfl
      rw [Int.cast_one, hv1] at hval
      exact_mod_cast hval
  let P_row : I → Finset (Fin r) → ℤ := fun i K =>
    match i with
    | none => if K = ∅ then 1 else 0
    | some x => if K = ∅ then 0 else (-1 : ℤ) ^ (K.card - 1) * ∏ a ∈ K, (if uBit x a then (1 : ℤ) else 0)
  let P_col : Finset (Fin r) → Fin m → ℤ := fun K c =>
    ∏ a ∈ K, (if wBit a c then (1 : ℤ) else 0)
  have hL_powerset : ∀ (i : I) (c : Fin m),
      L_Z i c = ∑ K ∈ (Finset.univ : Finset (Fin r)).powerset,
        (2 : ℤ) ^ (wt2 K) * P_row i K * P_col K c := by
    intro i c
    cases i with
    | none =>
      rw [Finset.sum_eq_single (∅ : Finset (Fin r))]
      · simp [L_Z, LMat, wt2, P_row, P_col]
      · intro K _ hKne
        simp [P_row, hKne]
      · intro hnot
        exact absurd (Finset.empty_mem_powerset _) hnot
    | some x =>
      rw [hL_parity x c, parity_eq_powerset_sum Finset.univ (fun a => uBit x a && wBit a c)]
      rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin r)).powerset _ (Finset.empty_mem_powerset _)]
      simp only [P_row, ite_true, mul_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun K hK => ?_
      have hKne : K ≠ ∅ := (Finset.mem_erase.mp hK).1
      simp only [wt2, P_col, hKne, ite_false]
      have hprod : (∏ a ∈ K, (if uBit x a then (1 : ℤ) else 0)) *
          (∏ a ∈ K, (if wBit a c then (1 : ℤ) else 0)) =
          ∏ a ∈ K, (if (uBit x a && wBit a c) then (1 : ℤ) else 0) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun a _ => ?_
        cases uBit x a <;> cases wBit a c <;> decide
      calc (2 : ℤ) ^ (K.card - 1) * ((-1 : ℤ) ^ (K.card - 1) *
            ∏ a ∈ K, (if (uBit x a && wBit a c) then (1 : ℤ) else 0))
          = (2 : ℤ) ^ (K.card - 1) * ((-1 : ℤ) ^ (K.card - 1) *
              ((∏ a ∈ K, (if uBit x a then (1 : ℤ) else 0)) *
                (∏ a ∈ K, (if wBit a c then (1 : ℤ) else 0)))) := by rw [← hprod]
        _ = (2 : ℤ) ^ (K.card - 1) *
              ((-1 : ℤ) ^ (K.card - 1) * ∏ a ∈ K, (if uBit x a then (1 : ℤ) else 0)) *
              ∏ a ∈ K, (if wBit a c then (1 : ℤ) else 0) := by ring
  let p : ℕ := h / 2
  let q : ℕ := h - h / 2
  have hpq : p + q = h := by omega
  have hp_le : p ≤ h := Nat.div_le_self h 2
  have : NeZero (2 ^ p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))⟩
  have : NeZero (2 ^ q) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by omega))⟩
  let L_p : Matrix I (Fin m) (ZMod (2 ^ p)) := L_Z.map (Int.cast : ℤ → ZMod (2 ^ p))
  let L_q : Matrix I (Fin m) (ZMod (2 ^ q)) := L_Z.map (Int.cast : ℤ → ZMod (2 ^ q))
  have hcard_LpT : (Finset.univ.image (fun x : I → ZMod (2 ^ p) => L_pᵀ.mulVec x)).card ≤
      2 ^ (p + Ffun r p) := by
    refine card_image_mulVec_le_of_powerset_factor
      (fun c K => P_col K c) (fun K i => P_row i K) L_pᵀ ?_
    intro c i
    simp only [L_p, Matrix.transpose_apply, Matrix.map_apply]
    rw [hL_powerset i c]
    congr 1
    refine Finset.sum_congr rfl fun K _ => by ring
  have hcard_Lq : (Finset.univ.image (fun y : Fin m → ZMod (2 ^ q) => L_q.mulVec y)).card ≤
      2 ^ (q + Ffun r q) := by
    refine card_image_mulVec_le_of_powerset_factor P_row P_col L_q ?_
    intro i c
    simp only [L_q, Matrix.map_apply]
    rw [hL_powerset i c]
  let castHP : ZMod (2 ^ h) →+* ZMod (2 ^ p) :=
    ZMod.castHom (pow_dvd_pow 2 hp_le) (ZMod (2 ^ p))
  let cls : (I → ZMod (2 ^ h)) → (Fin m → ZMod (2 ^ p)) :=
    fun x c => castHP ((L_hᵀ.mulVec x) c)
  have hcls_eq : ∀ x : I → ZMod (2 ^ h), cls x = L_pᵀ.mulVec (fun i => castHP (x i)) := by
    intro x
    ext c
    simp only [cls, Matrix.mulVec, dotProduct, L_h, L_p, Matrix.transpose_apply, Matrix.map_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast]
  have hcls_card : (Finset.univ.image cls).card ≤ 2 ^ (p + Ffun r p) := by
    have hsub : Finset.univ.image cls ⊆
        Finset.univ.image (fun y : I → ZMod (2 ^ p) => L_pᵀ.mulVec y) := by
      intro v hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨fun i => castHP (x i), Finset.mem_univ _, (hcls_eq x).symm⟩
    exact le_trans (Finset.card_le_card hsub) hcard_LpT
  let liftP : ZMod (2 ^ q) → ZMod (2 ^ h) := fun u => ((2 ^ p * u.val : ℕ) : ZMod (2 ^ h))
  have hfiber_card : ∀ v ∈ Finset.univ.image cls,
      ((Finset.univ.filter (fun x : I → ZMod (2 ^ h) => cls x = v)).image H.mulVec).card ≤
        2 ^ (q + Ffun r q) := by
    intro v hv
    obtain ⟨x0, _, hx0⟩ := Finset.mem_image.mp hv
    let shift : (I → ZMod (2 ^ q)) → (I → ZMod (2 ^ h)) :=
      fun y i => H.mulVec x0 i + liftP (y i)
    have hsub : (Finset.univ.filter (fun x : I → ZMod (2 ^ h) => cls x = v)).image H.mulVec ⊆
        (Finset.univ.image (fun y : Fin m → ZMod (2 ^ q) => L_q.mulVec y)).image shift := by
      intro out hout
      obtain ⟨x, hx_mem, rfl⟩ := Finset.mem_image.mp hout
      have hclseq : cls x = cls x0 := by
        rw [(Finset.mem_filter.mp hx_mem).2, hx0]
      let w : Fin m → ZMod (2 ^ h) := L_hᵀ.mulVec x - L_hᵀ.mulVec x0
      have hwdvd : ∀ c : Fin m, 2 ^ p ∣ (w c).val := by
        intro c
        have hwc : castHP (w c) = 0 := by
          simp only [w, Pi.sub_apply, map_sub]
          have hc := congrFun hclseq c
          simp only [cls] at hc
          rw [hc, sub_self]
        have hcast : ((w c).val : ZMod (2 ^ p)) = 0 := by
          have h1 := congrArg castHP (ZMod.natCast_zmod_val (w c))
          rw [map_natCast] at h1
          rw [h1, hwc]
        exact (ZMod.natCast_eq_zero_iff (w c).val (2 ^ p)).mp hcast
      let qNat : Fin m → ℕ := fun c => (w c).val / 2 ^ p
      let z : Fin m → ZMod (2 ^ q) := fun c => (qNat c : ZMod (2 ^ q))
      refine Finset.mem_image.mpr ⟨L_q.mulVec z, Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, ?_⟩
      ext i
      have hH_add : H.mulVec x i = H.mulVec x0 i + (L_h.mulVec w) i := by
        have h1 : H.mulVec x = H.mulVec x0 + L_h.mulVec w := by
          simp only [H, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, w]
          congr 1
          ext c
          simp only [Pi.add_apply, Pi.sub_apply]
          abel
        exact congrFun h1 i
      rw [hH_add]
      simp only [shift]
      congr 1
      let K_Z : ℤ := ∑ c : Fin m, L_Z i c * (qNat c : ℤ)
      have hlhs : (L_h.mulVec w) i = (((2 ^ p : ℤ) * K_Z : ℤ) : ZMod (2 ^ h)) := by
        have h1 : (L_h.mulVec w) i = ∑ c : Fin m, (L_Z i c : ZMod (2 ^ h)) * w c := rfl
        rw [h1]
        have h2 : (((2 ^ p : ℤ) * K_Z : ℤ) : ZMod (2 ^ h)) =
            ∑ c : Fin m, (2 : ZMod (2 ^ h)) ^ p *
              ((L_Z i c : ZMod (2 ^ h)) * (qNat c : ZMod (2 ^ h))) := by
          dsimp only [K_Z]
          push_cast
          rw [Finset.mul_sum]
        rw [h2]
        refine Finset.sum_congr rfl fun c _ => ?_
        have hwc : w c = ((2 ^ p * qNat c : ℕ) : ZMod (2 ^ h)) := by
          dsimp only [qNat]
          rw [Nat.mul_div_cancel' (hwdvd c), ZMod.natCast_zmod_val]
        rw [hwc]
        push_cast
        ring
      have hrhs : (L_q.mulVec z) i = (K_Z : ZMod (2 ^ q)) := by
        dsimp only [Matrix.mulVec, dotProduct, L_q, z, K_Z]
        simp only [Matrix.map_apply]
        push_cast
        rfl
      rw [hlhs, hrhs, liftP_intCast hpq K_Z]
    calc ((Finset.univ.filter (fun x : I → ZMod (2 ^ h) => cls x = v)).image H.mulVec).card
        ≤ ((Finset.univ.image (fun y : Fin m → ZMod (2 ^ q) => L_q.mulVec y)).image shift).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.image (fun y : Fin m → ZMod (2 ^ q) => L_q.mulVec y)).card :=
          Finset.card_image_le
      _ ≤ 2 ^ (q + Ffun r q) := hcard_Lq
  have hcover : Finset.univ.image (fun x : I → ZMod (2 ^ h) => H.mulVec x) ⊆
      (Finset.univ.image cls).biUnion
        (fun v => (Finset.univ.filter (fun x : I → ZMod (2 ^ h) => cls x = v)).image H.mulVec) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_biUnion.mpr ⟨cls x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  rw [hcard_GH]
  calc (Finset.univ.image (fun x : I → ZMod (2 ^ h) => H.mulVec x)).card
      ≤ ((Finset.univ.image cls).biUnion
          (fun v => (Finset.univ.filter (fun x : I → ZMod (2 ^ h) => cls x = v)).image H.mulVec)).card :=
        Finset.card_le_card hcover
    _ ≤ (Finset.univ.image cls).card * 2 ^ (q + Ffun r q) :=
        Finset.card_biUnion_le_card_mul _ _ _ hfiber_card
    _ ≤ 2 ^ (p + Ffun r p) * 2 ^ (q + Ffun r q) :=
        Nat.mul_le_mul_right _ hcls_card
    _ = 2 ^ (h + Ffun r (h / 2) + Ffun r (h - h / 2)) := by
        rw [← pow_add]
        congr 1
        dsimp only [p, q]
        omega

end PEqualNP.Outside.L_meta_32585_aux

theorem PEqualNP.Outside.L_meta_32585 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
let F := fun (r s : ℕ) => (Finset.range s).sum (fun k => (s-k) * Nat.choose r (k+1))
∀ (n m h : ℕ) (T P : Fin n → Fin m → Bool) (u : Fin n)
  (R : Finset (Fin n)) (S : Finset (Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ i ∉ R, ∀ j ∉ S, T i j = P i j) →
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
  PEqualNP.Represents.Represents P C → depth (n+m) C ≤ 1 →
  let d := fun i j : Fin n => (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card % (2^(h+1))
  let I := Option (Fin n)
  let G : Matrix I I (ZMod (2^h)) := fun i j =>
    let x := i.getD u
    let y := j.getD u
    if i.isNone then (if j.isNone then (m : ZMod (2^h)) else (d u y : ZMod (2^h)))
    else if j.isNone then (d u x : ZMod (2^h))
    else (((((d u x + d u y + 2^(h+1) - d x y) % (2^(h+1))) / 2 : ℕ)) : ZMod (2^h))
  let r := 2*C.gates.countP nonlinear + R.card + S.card
  (Finset.univ.image (fun x : I → ZMod (2^h) => G.mulVec x)).card ≤
    2^(h + F r (h/2) + F r (h-h/2))) := by
  exact PEqualNP.Outside.L_meta_32585_aux.main_proof
