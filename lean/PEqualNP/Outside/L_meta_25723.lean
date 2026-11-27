import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25723.Base

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

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

theorem rank_of_factor {n m K : ℕ} (P : Matrix (Fin n) (Fin K) (ZMod 2))
    (Q : Matrix (Fin K) (Fin m) (ZMod 2)) : (P * Q).rank ≤ K := by
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (Fin K → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = K := Module.finrank_fin_fun (ZMod 2)

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

def Valid (n m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) ⟨gs, 0⟩

theorem valid_nil (n m : ℕ) : Valid n m [] := by
  exact ⟨by simp, by simp [ReadsBack]⟩

theorem valid_snoc {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hbound : ∀ a ∈ g.inputs, a < n + m + gs.length) :
    Valid n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hv.1 g' h
    · rw [List.mem_singleton.mp h]
      exact hlen
  · intro j hj a ha
    change j < (gs ++ [g]).length at hj
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at ha
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at ha
      exact hv.2 j hj' a ha
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at ha
      simp only [Nat.sub_self, List.getD_cons_zero] at ha
      exact hbound a ha

theorem nlGate_or_nil : nlGate ⟨GateOp.or, []⟩ = false := rfl

theorem nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := rfl

theorem nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := rfl

theorem nlGate_and (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := rfl

def pushFalse (gs : List Gate) : List Gate := gs ++ [⟨GateOp.or, []⟩]

def pushXor (n m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [n + m + gs.length]⟩]

def pushAnd (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [a, b]⟩]

theorem pushFalse_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) :
    let gs' := pushFalse gs
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 = 0 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) = 0) := by
  refine ⟨valid_snoc hv _ (by simp) (by simp), by simp [pushFalse], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushFalse, List.countP_append, nlGate_or_nil]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushFalse
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, nlGate_or_nil]
  · intro i j
    unfold pushFalse
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, GateOp.eval, b2z]

theorem pushXor_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushXor n m gs a b
    let w := n + m + gs.length + 1
    Valid n m gs' ∧ gs'.length = gs.length + 2 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) +
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  let g2 : Gate := ⟨GateOp.not, [n + m + gs.length]⟩
  have hsplit : pushXor n m gs a b = (gs ++ [g1]) ++ [g2] := by
    simp [pushXor, g1, g2]
  have hv1 : Valid n m (gs ++ [g1]) := valid_snoc hv g1 (by simp [g1]) (by
    intro x hx; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hv2 : Valid n m ((gs ++ [g1]) ++ [g2]) := valid_snoc hv1 g2 (by simp [g2]) (by
    intro x hx; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp)
  refine ⟨hsplit ▸ hv2, by simp [pushXor], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushXor, List.countP_append, nlGate_mod2, nlGate_not]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · rw [hsplit, depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (depthsOf (n + m) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [depthsOf_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_not, Bool.toNat_false, add_zero, Nat.max_zero]
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_mod2, Bool.toNat_false, add_zero, Nat.max_zero]
  · intro i j
    rw [hsplit, wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (wiresOf (oneEach i j) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [wiresOf_length, oneEach_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil]
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

theorem pushAnd_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushAnd gs a b
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate + 1 ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) + 1 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) *
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  refine ⟨valid_snoc hv _ (by simp) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption), by simp [pushAnd], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushAnd, List.countP_append, nlGate_and]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushAnd
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_and, Bool.toNat_true, Nat.max_zero]
  · intro i j
    unfold pushAnd
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

theorem build_xor_list {n m : ℕ} (D : ℕ) (ws : List ℕ) (gs : List Gate) (hv : Valid n m gs)
    (hb : ∀ w ∈ ws, w < n + m + gs.length)
    (hd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ D ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum) := by
  induction ws generalizing gs with
  | nil =>
    obtain ⟨hv', hlen', hcnt', hdp', hwp', hdout, hwout⟩ := pushFalse_spec hv
    exact ⟨pushFalse gs, n + m + gs.length, hv', by omega, by omega, hcnt', hdp', hwp',
      by omega, fun i j => by simpa using hwout i j⟩
  | cons w ws ih =>
    have hw_lt : w < n + m + gs.length := hb w List.mem_cons_self
    have hw_d : (depthsOf (n + m) gs).getD w 0 ≤ D := hd w List.mem_cons_self
    obtain ⟨gs1, out1, hv1, hle1, hout1, hcnt1, hdp1, hwp1, hd1, hw1⟩ :=
      ih gs hv (fun a ha => hb a (List.mem_cons_of_mem w ha))
        (fun a ha => hd a (List.mem_cons_of_mem w ha))
    obtain ⟨hv2, hlen2, hcnt2, hdp2, hwp2, hd2, hw2⟩ :=
      pushXor_spec hv1 (by omega : w < n + m + gs1.length) hout1
    refine ⟨pushXor n m gs1 w out1, n + m + gs1.length + 1, hv2, by omega, by omega,
      by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hdp2 k (by omega), hdp1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · rw [hd2, hdp1 w hw_lt]
      exact max_le hw_d hd1
    · intro i j
      rw [hw2 i j, hwp1 i j w hw_lt, hw1 i j]
      simp

theorem build_row_fn {n m : ℕ} (f : Fin n → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = f i) := by
  let ws : List ℕ := ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map Fin.val
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin n, if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map
          (fun k : Fin n => if k = i then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega), oneEach_getD_left i j k.isLt]
      by_cases hki : k = i
      · subst hki; simp [b2z]
      · have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
        simp [b2z, hki, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin n)),
        ((l.filter (fun k => decide (f k = 1))).map (fun k => if k = i then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hfa : f a = 1 <;> simp [hfa, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    exact zmod2_ite_eq (f i)
  · intro k _ hki
    simp [hki]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem build_col_fn {n m : ℕ} (g : Fin m → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = g j) := by
  let ws : List ℕ :=
    ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map (fun k => n + k.val)
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin m, if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map
          (fun k : Fin m => if k = j then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega),
        oneEach_getD_right i j (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left]
      by_cases hkj : k = j
      · subst hkj; simp [b2z]
      · have hne : k.val ≠ j.val := fun e => hkj (Fin.ext e)
        simp [b2z, hkj, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin m)),
        ((l.filter (fun k => decide (g k = 1))).map (fun k => if k = j then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hga : g a = 1 <;> simp [hga, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    exact zmod2_ite_eq (g j)
  · intro k _ hkj
    simp [hkj]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem build_pair_and {n m : ℕ} (a b : Fin n → ZMod 2) (c d : Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate + 1 ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ 1 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (a i + d j) * (b i + c j)) := by
  obtain ⟨gs1, wa, hv1, hl1, hwa, hc1, hd1, hw1, hda, hfa⟩ := build_row_fn a gs hv
  obtain ⟨gs2, wd, hv2, hl2, hwd, hc2, hd2, hw2, hdd, hfd⟩ := build_col_fn d gs1 hv1
  obtain ⟨hv3, hl3, hc3, hd3, hw3, hdL, hwL⟩ :=
    pushXor_spec hv2 (by omega : wa < n + m + gs2.length) hwd
  set gs3 := pushXor n m gs2 wa wd
  let wL := n + m + gs2.length + 1
  obtain ⟨gs4, wb, hv4, hl4, hwb, hc4, hd4, hw4, hdb, hfb⟩ := build_row_fn b gs3 hv3
  obtain ⟨gs5, wc, hv5, hl5, hwc, hc5, hd5, hw5, hdc, hfc⟩ := build_col_fn c gs4 hv4
  obtain ⟨hv6, hl6, hc6, hd6, hw6, hdR, hwR⟩ :=
    pushXor_spec hv5 (by omega : wb < n + m + gs5.length) hwc
  set gs6 := pushXor n m gs5 wb wc
  let wR := n + m + gs5.length + 1
  obtain ⟨hv7, hl7, hc7, hd7, hw7, hdP, hwP⟩ :=
    pushAnd_spec hv6 (by omega : wL < n + m + gs6.length) (by omega : wR < n + m + gs6.length)
  set gs7 := pushAnd gs6 wL wR
  let out := n + m + gs6.length
  refine ⟨gs7, out, hv7, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hd7 k (by omega), hd6 k (by omega), hd5 k (by omega), hd4 k (by omega),
      hd3 k (by omega), hd2 k (by omega), hd1 k hk]
  · intro i j k hk
    rw [hw7 i j k (by omega), hw6 i j k (by omega), hw5 i j k (by omega), hw4 i j k (by omega),
      hw3 i j k (by omega), hw2 i j k (by omega), hw1 i j k hk]
  · rw [hdP]
    have hL0 : (depthsOf (n + m) gs6).getD wL 0 = 0 := by
      rw [hd6 wL (by omega), hd5 wL (by omega), hd4 wL (by omega), hdL, hd2 wa hwa, hda, hdd]
      simp
    have hR0 : (depthsOf (n + m) gs6).getD wR 0 = 0 := by
      rw [hdR, hd5 wb hwb, hdb, hdc]
      simp
    rw [hL0, hR0]
    simp
  · intro i j
    rw [hwP i j]
    have hLv : b2z ((wiresOf (oneEach i j) gs6).getD wL false) = a i + d j := by
      rw [hw6 i j wL (by omega), hw5 i j wL (by omega), hw4 i j wL (by omega),
        hwL i j, hw2 i j wa hwa, hfa i j, hfd i j]
    have hRv : b2z ((wiresOf (oneEach i j) gs6).getD wR false) = b i + c j := by
      rw [hwR i j, hw5 i j wb hwb, hfb i j, hfc i j]
    rw [hLv, hRv]

theorem build_many_pairs {n m : ℕ} (t : ℕ)
    (a b : Fin t → Fin n → ZMod 2) (c d : Fin t → Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧
      (∀ w ∈ ws, w < n + m + gs'.length) ∧
      (∀ w ∈ ws, (depthsOf (n + m) gs').getD w 0 ≤ 1) ∧
      gs'.countP nlGate = gs.countP nlGate + t ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (∀ (i : Fin n) (j : Fin m), (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs').getD w false))).sum =
        ∑ p : Fin t, (a p i + d p j) * (b p i + c p j)) := by
  induction t generalizing gs with
  | zero =>
    exact ⟨gs, [], hv, le_rfl, by simp, by simp, by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => by simp⟩
  | succ t ih =>
    obtain ⟨gs1, w0, hv1, hl1, hw0, hc1, hd1, hwp1, hdw0, hfv0⟩ :=
      build_pair_and (a 0) (b 0) (c 0) (d 0) gs hv
    obtain ⟨gs2, ws, hv2, hl2, hws, hdws, hc2, hd2, hwp2, hsum⟩ :=
      ih (fun p => a p.succ) (fun p => b p.succ) (fun p => c p.succ) (fun p => d p.succ) gs1 hv1
    refine ⟨gs2, w0 :: ws, hv2, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · exact hws w hw
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [hd2 w hw0]; exact hdw0
      · exact hdws w hw
    · intro k hk
      rw [hd2 k (by omega), hd1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · intro i j
      rw [List.map_cons, List.sum_cons, hwp2 i j w0 hw0, hfv0 i j, hsum i j, Fin.sum_univ_succ]

theorem dir_ge {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (hr : (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t) :
    ∃ C : Circuit,
      ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
      (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
      C.gates.countP nlGate ≤ t := by
  obtain ⟨rowVec, colVec, hfac⟩ := factor_of_rank_le (anchor u v (fun i j => b2z (G i j))) hr
  let a : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val, by omega⟩
  let b : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val + 1, by omega⟩
  let c : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val, by omega⟩
  let d : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val + 1, by omega⟩
  let R : Fin n → ZMod 2 := fun i => b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i
  let S : Fin m → ZMod 2 := fun j => b2z (G u j) + ∑ p : Fin t, c p j * d p j
  have hdecomp : ∀ i j, b2z (G i j) = R i + S j + ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) := by
    intro i j
    have hA := hfac i j
    have hpair : ∑ k : Fin (2 * t), rowVec k i * colVec k j =
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      let e : Fin t × Fin 2 ≃ Fin (2 * t) := {
        toFun := fun x => ⟨2 * x.1.val + x.2.val, by omega⟩
        invFun := fun k => (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext
          · simp; omega
          · simp; omega
        right_inv := fun k => by
          ext
          simp
          omega
      }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.sum_univ_two]
      rfl
    rw [hpair] at hA
    simp only [anchor] at hA
    have hterm : ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) =
        ∑ p : Fin t, (a p i * b p i + c p j * d p j) +
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hterm, ← hA]
    simp only [R, S, Finset.sum_add_distrib]
    have h2 : (b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i) +
        (b2z (G u j) + ∑ p : Fin t, c p j * d p j) +
        ((∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) +
        (b2z (G i j) + b2z (G i v) + b2z (G u j) + b2z (G u v))) =
        b2z (G i j) + (2 : ZMod 2) * (b2z (G i v) + b2z (G u j) + b2z (G u v) +
          ∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) := by ring
    rw [h2, zmod2_two, zero_mul, add_zero]
  obtain ⟨gs1, wR, hv1, hl1, hwR, hc1, _, _, hdR, hfR⟩ := build_row_fn R [] (valid_nil n m)
  obtain ⟨gs2, wS, hv2, hl2, hwS, hc2, hd2, hw2, hdS, hfS⟩ := build_col_fn S gs1 hv1
  obtain ⟨gs3, ws, hv3, hl3, hws, hdws, hc3, hd3, hw3, hsum3⟩ :=
    build_many_pairs t a b c d gs2 hv2
  obtain ⟨gs4, out, hv4, hl4, hout, hc4, hd4, hw4, hdout, hwout⟩ :=
    build_xor_list 1 (wR :: wS :: ws) gs3 hv3
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · omega
          · exact hws w hw)
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rw [hd3 w (by omega), hd2 w hwR, hdR]; omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · rw [hd3 w hwS, hdS]; omega
          · exact hdws w hw)
  refine ⟨⟨gs4, out⟩, ⟨hv4.1, hv4.2, ?_⟩, hdout, ?_⟩
  · intro i j
    apply b2z_inj
    change b2z ((wiresOf (oneEach i j) gs4).getD out false) = b2z (G i j)
    rw [hwout i j]
    simp only [List.map_cons, List.sum_cons]
    rw [hw3 i j wR (by omega), hw2 i j wR hwR, hfR i j,
      hw3 i j wS hwS, hfS i j, hsum3 i j, hdecomp i j]
    ring
  · change gs4.countP nlGate ≤ t
    simp only [List.countP_nil] at hc1
    omega

theorem main (n m : ℕ) (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t ↔
      ∃ C : Circuit,
        ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
        (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
        C.gates.countP nlGate ≤ t :=
  ⟨dir_ge G u v t, fun ⟨C, ⟨hlen, hrb, hrep⟩, hd1, hcnt⟩ => dir_le G u v t C hlen hrb hrep hd1 hcnt⟩

end PEqualNP.Outside.L_meta_25723.Base


namespace PEqualNP.Outside.L_meta_25723

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.Outside.L_meta_25723.Base

lemma eq_anchor_rank_ge (k : ℕ) (hk : 0 < k) :
    2 ^ k ≤ 2 + (anchor (0 : Fin (2 ^ k)) (0 : Fin (2 ^ k))
      (fun i j => b2z (decide (i = j)))).rank := by
  let N := 2 ^ k
  have hNpos : 0 < N := by positivity
  set A : Matrix (Fin N) (Fin N) (ZMod 2) :=
    anchor (0 : Fin N) (0 : Fin N) (fun i j => b2z (decide (i = j)))
  let v0 : Fin N → ZMod 2 := fun i => if i = 0 then 1 else 0
  let v1 : Fin N → ZMod 2 := fun i => if i = 0 then 0 else 1
  have hker_le : LinearMap.ker A.mulVecLin ≤ Submodule.span (ZMod 2) ({v0, v1} : Set (Fin N → ZMod 2)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    let S : ZMod 2 := ∑ j : Fin N, if j = 0 then 0 else x j
    have hxi : ∀ i : Fin N, i ≠ 0 → x i = S := by
      intro i hi
      have h0 : (A.mulVec x) i = 0 := congrFun hx i
      have hsum : (A.mulVec x) i = x i + S := by
        rw [Matrix.mulVec, dotProduct]
        have hterm : ∀ j : Fin N, A i j * x j =
            (if j = i then x j else 0) + (if j = 0 then 0 else x j) := by
          intro j
          by_cases hj0 : j = 0
          · subst hj0
            have hij : i ≠ 0 := hi
            simp only [A, anchor, b2z, decide_eq_true_eq, hij, ite_false, ite_true, zero_add, add_zero, zmod2_add_self, zero_mul, Ne.symm hij]
          · by_cases hji : j = i
            · subst hji
              simp only [A, anchor, b2z, decide_eq_true_eq, hi, Ne.symm hi, ite_false, ite_true, add_zero, zero_add, zmod2_add_self, zero_mul]
            · have hij : i ≠ j := Ne.symm hji
              simp only [A, anchor, b2z, decide_eq_true_eq, hi, hj0, Ne.symm hj0, hij, hji, ite_false, ite_true, add_zero, zero_add, one_mul]
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
      rw [hsum] at h0
      have : x i = x i + (x i + S) := by rw [h0, add_zero]
      rw [← add_assoc, zmod2_add_self, zero_add] at this
      exact this
    have hx_eq : x = x 0 • v0 + S • v1 := by
      funext i
      by_cases hi : i = 0
      · subst hi; simp [v0, v1]
      · simp [v0, v1, hi, hxi i hi]
    rw [hx_eq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) ≤ 2 := by
    calc Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin)
        ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v0, v1} : Set (Fin N → ZMod 2))) :=
          Submodule.finrank_mono hker_le
      _ ≤ ({v0, v1} : Finset (Fin N → ZMod 2)).card := by
          simpa using finrank_span_le_card ({v0, v1} : Set (Fin N → ZMod 2))
      _ ≤ 2 := by
          exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  change A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = N at hrn
  omega

lemma eq_anchor_rank_le (w : ℕ) (hw : 0 < w) :
    (anchor (0 : Fin (2 ^ w)) (0 : Fin (2 ^ w))
      (fun i j => b2z (decide (i = j)))).rank ≤ 2 ^ w - 2 := by
  let W := 2 ^ w
  have hW2 : 2 ≤ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hWeven : (W : ZMod 2) = 0 := by
    have : ∃ q, W = 2 * q := ⟨2 ^ (w - 1), by
      have : w = (w - 1) + 1 := by omega
      conv_lhs => rw [show W = 2 ^ w from rfl, this, pow_succ, mul_comm]⟩
    obtain ⟨q, hq⟩ := this
    rw [hq, Nat.cast_mul, Nat.cast_ofNat, zmod2_two, zero_mul]
  set A : Matrix (Fin W) (Fin W) (ZMod 2) :=
    anchor (0 : Fin W) (0 : Fin W) (fun i j => b2z (decide (i = j)))
  let v0 : Fin W → ZMod 2 := fun j => if j = 0 then 1 else 0
  let v1 : Fin W → ZMod 2 := fun j => if j = 0 then 0 else 1
  have hv0 : v0 ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext i
    rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    have hterm : ∀ j : Fin W, A i j * v0 j = 0 := by
      intro j
      by_cases hj : j = 0
      · subst hj
        simp only [A, anchor, b2z, decide_eq_true_eq, ite_true, v0]
        by_cases hi : i = 0 <;> simp [hi, zmod2_add_self]
      · simp [v0, hj]
    simp [hterm]
  have hv1 : v1 ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext i
    rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    by_cases hi0 : i = 0
    · subst hi0
      have hterm : ∀ j : Fin W, A 0 j * v1 j = 0 := by
        intro j
        simp only [A, anchor, b2z, decide_eq_true_eq, ite_true]
        by_cases hj : j = 0
        · subst hj; simp [zmod2_add_self]
        · simp [hj, Ne.symm hj, zmod2_add_self]
      simp [hterm]
    · have hterm : ∀ j : Fin W, A i j * v1 j =
          (if j = i then (1 : ZMod 2) else 0) + (if j = 0 then 0 else 1) := by
        intro j
        by_cases hj0 : j = 0
        · subst hj0
          simp [v1, Ne.symm hi0]
        · by_cases hji : j = i
          · subst hji
            simp only [A, anchor, b2z, decide_eq_true_eq, hi0, Ne.symm hi0, ite_false, ite_true, v1,
              mul_one, add_zero, zero_add, zmod2_add_self]
          · simp only [A, anchor, b2z, decide_eq_true_eq, hi0, hj0, Ne.symm hj0, hji, Ne.symm hji,
              ite_false, ite_true, v1, mul_one, add_zero, zero_add]
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
      have hsum1 : (∑ j : Fin W, if j = (0 : Fin W) then (0 : ZMod 2) else 1) = (W : ZMod 2) - 1 := by
        have htot : (∑ j : Fin W, (1 : ZMod 2)) = (W : ZMod 2) := by simp
        have hsplit : (∑ j : Fin W, (1 : ZMod 2)) =
            (∑ j : Fin W, if j = (0 : Fin W) then (1 : ZMod 2) else 0) +
            (∑ j : Fin W, if j = (0 : Fin W) then (0 : ZMod 2) else 1) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = 0 <;> simp [hj]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ (0 : Fin W))] at hsplit
        rw [htot] at hsplit
        have : (1 : ZMod 2) + (∑ j : Fin W, if j = (0 : Fin W) then (0 : ZMod 2) else 1) = (W : ZMod 2) :=
          hsplit.symm
        linear_combination this
      rw [hsum1, hWeven]
      simp [zmod2_add_self]
  have hli : LinearIndependent (ZMod 2) ![v0, v1] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg (0 : Fin W)
    have h1 := congrFun hg ⟨1, by omega⟩
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v0, v1] at h0 h1
    have hne : (⟨1, by omega⟩ : Fin W) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp only [ite_true, ite_false, hne, mul_one, mul_zero, add_zero, zero_add] at h0 h1
    fin_cases i
    · exact h0
    · exact h1
  have hle : Submodule.span (ZMod 2) (Set.range ![v0, v1]) ≤ LinearMap.ker A.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hv0
    · exact hv1
  have hker_ge : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by
    calc 2 = Fintype.card (Fin 2) := by simp
      _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![v0, v1])) :=
          (finrank_span_eq_card hli).symm
      _ ≤ Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := Submodule.finrank_mono hle
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  change A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = W at hrn
  omega

lemma pullback_rank_le {n m n' m' : ℕ} (f : Fin n → Fin n') (g : Fin m → Fin m')
    (B : Matrix (Fin n') (Fin m') (ZMod 2)) :
    (Matrix.of (fun i j => B (f i) (g j))).rank ≤ B.rank := by
  let P : Matrix (Fin n) (Fin n') (ZMod 2) := Matrix.of (fun i a => if f i = a then 1 else 0)
  let Q : Matrix (Fin m') (Fin m) (ZMod 2) := Matrix.of (fun b j => if g j = b then 1 else 0)
  have heq : Matrix.of (fun i j => B (f i) (g j)) = P * B * Q := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, P, Q, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ (g j)),
      Finset.sum_ite_eq, if_pos (Finset.mem_univ (f i))]
  rw [heq]
  calc (P * B * Q).rank ≤ (P * B).rank := Matrix.rank_mul_le_left (P * B) Q
    _ ≤ B.rank := Matrix.rank_mul_le_right P B

def mon {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    (S T : Finset K) (i : Fin n) (j : Fin m) : ZMod 2 :=
  (∏ x ∈ S, α x i) * (∏ y ∈ T, β y j)

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma prod_mul_prod_zmod2 {K : Type*} [DecidableEq K] (f : K → ZMod 2) (S₁ S₂ : Finset K) :
    (∏ x ∈ S₁, f x) * (∏ x ∈ S₂, f x) = ∏ x ∈ S₁ ∪ S₂, f x := by
  induction S₁ using Finset.induction_on with
  | empty => simp
  | @insert a S₁ ha ih =>
    rw [Finset.prod_insert ha, Finset.insert_union, mul_assoc, ih]
    by_cases ha2 : a ∈ S₁ ∪ S₂
    · rw [Finset.insert_eq_of_mem ha2, ← Finset.mul_prod_erase _ _ ha2, ← mul_assoc, zmod2_mul_self]
    · rw [Finset.prod_insert ha2]

lemma mon_mul {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    (S₁ T₁ S₂ T₂ : Finset K) (i : Fin n) (j : Fin m) :
    mon α β S₁ T₁ i j * mon α β S₂ T₂ i j = mon α β (S₁ ∪ S₂) (T₁ ∪ T₂) i j := by
  unfold mon
  calc (∏ x ∈ S₁, α x i) * (∏ y ∈ T₁, β y j) * ((∏ x ∈ S₂, α x i) * (∏ y ∈ T₂, β y j))
      = ((∏ x ∈ S₁, α x i) * (∏ x ∈ S₂, α x i)) * ((∏ y ∈ T₁, β y j) * (∏ y ∈ T₂, β y j)) := by ring
    _ = (∏ x ∈ S₁ ∪ S₂, α x i) * (∏ y ∈ T₁ ∪ T₂, β y j) := by
        rw [prod_mul_prod_zmod2, prod_mul_prod_zmod2]

def PolyDeg {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) (D : ℕ) :
    Submodule (ZMod 2) (Fin n → Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) {f | ∃ S T : Finset K, S.card + T.card ≤ D ∧ f = mon α β S T}

lemma polyDeg_mono {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) {D₁ D₂ : ℕ} (h : D₁ ≤ D₂) :
    PolyDeg α β D₁ ≤ PolyDeg α β D₂ := by
  apply Submodule.span_mono
  rintro f ⟨S, T, hST, rfl⟩
  exact ⟨S, T, le_trans hST h, rfl⟩

lemma polyDeg_mul {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) {D₁ D₂ : ℕ}
    {f g : Fin n → Fin m → ZMod 2}
    (hf : f ∈ PolyDeg α β D₁) (hg : g ∈ PolyDeg α β D₂) :
    (fun i j => f i j * g i j) ∈ PolyDeg α β (D₁ + D₂) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S₁, T₁, h1, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨S₂, T₂, h2, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨S₁ ∪ S₂, T₁ ∪ T₂, ?_, ?_⟩
      · have hs := Finset.card_union_le S₁ S₂
        have ht := Finset.card_union_le T₁ T₂
        omega
      · funext i j
        exact mon_mul α β S₁ T₁ S₂ T₂ i j
    | zero =>
      have : (fun i j => mon α β S₁ T₁ i j * (0 : Fin n → Fin m → ZMod 2) i j) = 0 := by
        funext i j; simp
      rw [this]
      exact Submodule.zero_mem _
    | add g₁ g₂ _ _ ih1 ih2 =>
      have : (fun i j => mon α β S₁ T₁ i j * (g₁ + g₂) i j) =
          (fun i j => mon α β S₁ T₁ i j * g₁ i j) + (fun i j => mon α β S₁ T₁ i j * g₂ i j) := by
        funext i j; simp [mul_add]
      rw [this]
      exact Submodule.add_mem _ ih1 ih2
    | smul c g₁ _ ih =>
      have : (fun i j => mon α β S₁ T₁ i j * (c • g₁) i j) =
          c • (fun i j => mon α β S₁ T₁ i j * g₁ i j) := by
        funext i j; simp; ring
      rw [this]
      exact Submodule.smul_mem _ c ih
  | zero =>
    have : (fun i j => (0 : Fin n → Fin m → ZMod 2) i j * g i j) = 0 := by
      funext i j; simp
    rw [this]
    exact Submodule.zero_mem _
  | add f₁ f₂ _ _ ih1 ih2 =>
    have : (fun i j => (f₁ + f₂) i j * g i j) =
        (fun i j => f₁ i j * g i j) + (fun i j => f₂ i j * g i j) := by
      funext i j; simp [add_mul]
    rw [this]
    exact Submodule.add_mem _ ih1 ih2
  | smul c f₁ _ ih =>
    have : (fun i j => (c • f₁) i j * g i j) = c • (fun i j => f₁ i j * g i j) := by
      funext i j; simp; ring
    rw [this]
    exact Submodule.smul_mem _ c ih

lemma polyDeg_const {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) (D : ℕ) (c : ZMod 2) :
    (fun _ _ => c) ∈ PolyDeg α β D := by
  let oneFn : Fin n → Fin m → ZMod 2 := fun _ _ => 1
  have h1 : oneFn = mon α β ∅ ∅ := by
    funext i j; simp [oneFn, mon]
  have hm : oneFn ∈ PolyDeg α β D := by
    rw [h1]
    exact Submodule.subset_span ⟨∅, ∅, by simp, rfl⟩
  have : (fun (_ : Fin n) (_ : Fin m) => c) = c • oneFn := by
    funext i j; simp [oneFn]
  rw [this]
  exact Submodule.smul_mem _ c hm

lemma polyDeg_alpha {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) {D : ℕ} (hD : 1 ≤ D) (x : K) :
    (fun i (_ : Fin m) => α x i) ∈ PolyDeg α β D := by
  apply Submodule.subset_span
  refine ⟨{x}, ∅, by simp [hD], ?_⟩
  funext i j; simp [mon]

lemma polyDeg_beta {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) {D : ℕ} (hD : 1 ≤ D) (y : K) :
    (fun (_ : Fin n) j => β y j) ∈ PolyDeg α β D := by
  apply Submodule.subset_span
  refine ⟨∅, {y}, by simp [hD], ?_⟩
  funext i j; simp [mon]

lemma rank_anchor_polyDeg {n m : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (u : Fin n) (v : Fin m)
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    (hα0 : ∀ x, α x u = 0) (hβ0 : ∀ y, β y v = 0)
    (b : ℕ) {f : Fin n → Fin m → ZMod 2} (hf : f ∈ PolyDeg α β (2 * b)) :
    (anchor u v f).rank ≤
      (∑ j ∈ Finset.range b, Nat.choose (Fintype.card K) (j + 1)) +
      (∑ j ∈ Finset.range (b - 1), Nat.choose (Fintype.card K) (j + 1)) := by
  let F1 : Finset (Finset K) := Finset.univ.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ b)
  let F2 : Finset (Finset K) := Finset.univ.powerset.filter (fun T => 1 ≤ T.card ∧ T.card ≤ b - 1)
  have hF1_card : F1.card = ∑ j ∈ Finset.range b, Nat.choose (Fintype.card K) (j + 1) := by
    have hmaps : ∀ S ∈ F1, S.card - 1 ∈ Finset.range b := by
      intro S hS
      rw [Finset.mem_filter] at hS
      rw [Finset.mem_range]
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have heq : F1.filter (fun S => S.card - 1 = j) =
        (Finset.univ : Finset K).powersetCard (j + 1) := by
      ext S
      simp only [F1, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      omega
    rw [heq, Finset.card_powersetCard, Finset.card_univ]
  have hF2_card : F2.card = ∑ j ∈ Finset.range (b - 1), Nat.choose (Fintype.card K) (j + 1) := by
    have hmaps : ∀ T ∈ F2, T.card - 1 ∈ Finset.range (b - 1) := by
      intro T hT
      rw [Finset.mem_filter] at hT
      rw [Finset.mem_range]
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have heq : F2.filter (fun T => T.card - 1 = j) =
        (Finset.univ : Finset K).powersetCard (j + 1) := by
      ext T
      simp only [F2, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      omega
    rw [heq, Finset.card_powersetCard, Finset.card_univ]
  have hsplit : ∃ (A1 A2 : Matrix (Fin n) (Fin m) (ZMod 2)),
      anchor u v f = A1 + A2 ∧
      (∃ Q1 : Matrix F1 (Fin m) (ZMod 2),
        A1 = Matrix.of (fun (i : Fin n) (S : F1) => ∏ x ∈ S.val, α x i) * Q1) ∧
      (∃ P2 : Matrix (Fin n) F2 (ZMod 2),
        A2 = P2 * Matrix.of (fun (T : F2) (j : Fin m) => ∏ y ∈ T.val, β y j)) := by
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨S, T, hST, rfl⟩ := hg
      by_cases hS0 : S = ∅
      · subst hS0
        have ha0 : anchor u v (mon α β ∅ T) = 0 := by
          have : mon α β ∅ T = fun _ j => (0 : ZMod 2) + ∏ y ∈ T, β y j := by
            funext i j; simp [mon]
          rw [this, anchor_split]
        exact ⟨0, 0, by simp [ha0], ⟨0, by simp⟩, ⟨0, by simp⟩⟩
      · by_cases hT0 : T = ∅
        · subst hT0
          have ha0 : anchor u v (mon α β S ∅) = 0 := by
            have : mon α β S ∅ = fun i _ => (∏ x ∈ S, α x i) + 0 := by
              funext i j; simp [mon]
            rw [this, anchor_split]
          exact ⟨0, 0, by simp [ha0], ⟨0, by simp⟩, ⟨0, by simp⟩⟩
        · have hSpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
          have hTpos : 1 ≤ T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT0)
          have hprod_u : ∏ x ∈ S, α x u = 0 := by
            obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
            exact Finset.prod_eq_zero hx0 (hα0 x0)
          have hprod_v : ∏ y ∈ T, β y v = 0 := by
            obtain ⟨y0, hy0⟩ := Finset.nonempty_iff_ne_empty.mpr hT0
            exact Finset.prod_eq_zero hy0 (hβ0 y0)
          have ha_eq : anchor u v (mon α β S T) = Matrix.of (mon α β S T) := by
            ext i j
            simp only [anchor, mon, Matrix.of_apply, hprod_u, hprod_v, zero_mul, mul_zero, add_zero]
          by_cases hSb : S.card ≤ b
          · have hSmem : S ∈ F1 := Finset.mem_filter.mpr
              ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hSpos, hSb⟩
            refine ⟨Matrix.of (mon α β S T), 0, by simp [ha_eq], ?_, ⟨0, by simp⟩⟩
            refine ⟨Matrix.of (fun (S' : F1) (j : Fin m) => if S'.val = S then ∏ y ∈ T, β y j else 0), ?_⟩
            ext i j
            rw [Matrix.mul_apply]
            simp only [Matrix.of_apply, mon]
            rw [Finset.sum_eq_single (⟨S, hSmem⟩ : F1)]
            · simp
            · intro S' _ hne
              have : S'.val ≠ S := fun h => hne (Subtype.ext h)
              simp [this]
            · intro h; exact absurd (Finset.mem_univ _) h
          · have hTb : T.card ≤ b - 1 := by omega
            have hTmem : T ∈ F2 := Finset.mem_filter.mpr
              ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hTpos, hTb⟩
            refine ⟨0, Matrix.of (mon α β S T), by simp [ha_eq], ⟨0, by simp⟩, ?_⟩
            refine ⟨Matrix.of (fun (i : Fin n) (T' : F2) => if T'.val = T then ∏ x ∈ S, α x i else 0), ?_⟩
            ext i j
            rw [Matrix.mul_apply]
            simp only [Matrix.of_apply, mon]
            rw [Finset.sum_eq_single (⟨T, hTmem⟩ : F2)]
            · simp
            · intro T' _ hne
              have : T'.val ≠ T := fun h => hne (Subtype.ext h)
              simp [this]
            · intro h; exact absurd (Finset.mem_univ _) h
    | zero =>
      have : anchor u v (0 : Fin n → Fin m → ZMod 2) = 0 := anchor_const u v 0
      exact ⟨0, 0, by simp [this], ⟨0, by simp⟩, ⟨0, by simp⟩⟩
    | add f1 f2 _ _ ih1 ih2 =>
      obtain ⟨A1, A2, ha, ⟨Q1, hQ1⟩, ⟨P2, hP2⟩⟩ := ih1
      obtain ⟨B1, B2, hb, ⟨Q1', hQ1'⟩, ⟨P2', hP2'⟩⟩ := ih2
      refine ⟨A1 + B1, A2 + B2, ?_, ⟨Q1 + Q1', ?_⟩, ⟨P2 + P2', ?_⟩⟩
      · change anchor u v (fun i j => f1 i j + f2 i j) = _
        rw [anchor_add, ha, hb]; abel
      · rw [Matrix.mul_add, hQ1, hQ1']
      · rw [Matrix.add_mul, hP2, hP2']
    | smul c f1 _ ih =>
      obtain ⟨A1, A2, ha, ⟨Q1, hQ1⟩, ⟨P2, hP2⟩⟩ := ih
      refine ⟨c • A1, c • A2, ?_, ⟨c • Q1, ?_⟩, ⟨c • P2, ?_⟩⟩
      · change anchor u v (fun i j => c * f1 i j) = _
        rw [anchor_smul, ha, smul_add]
      · rw [Matrix.mul_smul, hQ1]
      · rw [Matrix.smul_mul, hP2]
  obtain ⟨A1, A2, hsum, ⟨Q1, hQ1⟩, ⟨P2, hP2⟩⟩ := hsplit
  have hr1 : A1.rank ≤ F1.card := by
    rw [hQ1]
    calc (Matrix.of (fun (i : Fin n) (S : F1) => ∏ x ∈ S.val, α x i) * Q1).rank
        ≤ (Matrix.of (fun (i : Fin n) (S : F1) => ∏ x ∈ S.val, α x i)).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Module.finrank (ZMod 2) (F1 → ZMod 2) := LinearMap.finrank_range_le _
      _ = F1.card := by rw [Module.finrank_pi]; simp
  have hr2 : A2.rank ≤ F2.card := by
    rw [hP2]
    calc (P2 * Matrix.of (fun (T : F2) (j : Fin m) => ∏ y ∈ T.val, β y j)).rank
        ≤ P2.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Module.finrank (ZMod 2) (F2 → ZMod 2) := LinearMap.finrank_range_le _
      _ = F2.card := by rw [Module.finrank_pi]; simp
  have hr_add : (A1 + A2).rank ≤ A1.rank + A2.rank := by
    let S1 : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range A1.mulVecLin
    let S2 : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range A2.mulVecLin
    have hrange : LinearMap.range (A1 + A2).mulVecLin ≤ S1 ⊔ S2 := by
      rintro _ ⟨x, rfl⟩
      have hmul : (A1 + A2).mulVecLin x = A1.mulVecLin x + A2.mulVecLin x := by
        simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
      rw [hmul]
      exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq S1 S2
    have hmono := Submodule.finrank_mono hrange
    change (A1 + A2).rank ≤ Module.finrank (ZMod 2) ↥(S1 ⊔ S2) at hmono
    change Module.finrank (ZMod 2) ↥(S1 ⊔ S2) + Module.finrank (ZMod 2) ↥(S1 ⊓ S2) =
      A1.rank + A2.rank at hsup
    omega
  rw [hsum, ← hF1_card, ← hF2_card]
  exact le_trans hr_add (Nat.add_le_add hr1 hr2)

lemma lower_bound_general {n m d : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents G C)
    (hdep : (depthsOf (n + m) C.gates).getD C.output 0 ≤ d + 1) :
    let t := C.gates.countP nlGate
    (anchor u v (fun i j => b2z (G i j))).rank ≤
      (∑ j ∈ Finset.range (2 ^ d), Nat.choose (2 * t) (j + 1)) +
      (∑ j ∈ Finset.range (2 ^ d - 1), Nat.choose (2 * t) (j + 1)) := by
  intro t
  let val : ℕ → Fin n → Fin m → ZMod 2 :=
    fun k i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
  let dep : ℕ → ℕ := fun k => (depthsOf (n + m) C.gates).getD k 0
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate (C.gates[idx.val]) = true)
  have hNL_card : NL.card = t := card_filter_fin_eq_countP C.gates nlGate
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
      intro a ha; rw [oneEach_length]; exact hrb' idx hidx a ha)
    rw [oneEach_length] at h
    rw [h]
  have hdep_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      dep (n + m + idx) =
        ((C.gates[idx]).inputs.map dep).foldr max 0 + (nlGate (C.gates[idx])).toNat := by
    intro idx hidx
    exact depthsOf_getD_gate (n + m) C.gates hidx (hrb' idx hidx)
  have hdecomp_wire : ∀ k : ℕ,
      ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) (c : NL → ZMod 2),
        (∀ p : NL, c p ≠ 0 → n + m + p.val.val ≤ k ∧ dep (n + m + p.val.val) ≤ dep k) ∧
        ∀ i j, val k i j = r i + s j + ∑ p : NL, c p * val (n + m + p.val.val) i j := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases hk1 : k < n + m
      · by_cases hk0 : k < n
        · refine ⟨fun i => b2z (decide (k = i.val)), fun _ => 0, fun _ => 0, by simp, fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_left i j hk0]
          simp
        · refine ⟨fun _ => 0, fun j => b2z (decide (k - n = j.val)), fun _ => 0, by simp, fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_right i j (by omega) hk1]
          simp
      · by_cases hk2 : k < n + m + C.gates.length
        · let idx : Fin C.gates.length := ⟨k - (n + m), by omega⟩
          have hkeq : k = n + m + idx.val := by simp [idx]; omega
          rw [hkeq]
          let g := C.gates[idx.val]
          by_cases hnl : nlGate g = true
          · have hmem : idx ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl⟩
            let p0 : NL := ⟨idx, hmem⟩
            refine ⟨fun _ => 0, fun _ => 0, fun p => if p = p0 then 1 else 0, ?_, fun i j => ?_⟩
            · intro p hp
              have : p = p0 := by by_contra hne; simp [hne] at hp
              subst this; exact ⟨le_rfl, le_rfl⟩
            · simp only [zero_add]
              rw [Finset.sum_eq_single p0]
              · simp [p0]
              · intro p _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ p0) h
          · have hnlf : nlGate g = false := by cases h : nlGate g <;> simp_all
            have hdg := hdep_gate idx.val idx.isLt
            have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
            match hg_in : g.inputs with
            | [] =>
              refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun _ => 0, by simp, fun i j => ?_⟩
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in]; simp
            | [a] =>
              have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
              have ha_d : dep a ≤ dep (n + m + idx.val) := by
                change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
                rw [hg_in] at hdg; simp at hdg; omega
              obtain ⟨ra, sa, ca, hca_supp, hca_eq⟩ := ih a (by omega)
              let c0 := b2z (g.op.eval [false])
              let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
              refine ⟨fun i => c0 + c1 * ra i, fun j => c1 * sa j, fun p => c1 * ca p, ?_, fun i j => ?_⟩
              · intro p hp
                have hne : ca p ≠ 0 := fun h => hp (by simp [h])
                have hs := hca_supp p hne
                exact ⟨by omega, by omega⟩
              · rw [hval_gate idx.val idx.isLt i j]
                change b2z (g.op.eval (g.inputs.map _)) = _
                rw [hg_in, List.map_cons, List.map_nil]
                have hanf := anf_one (fun x => g.op.eval [x])
                  ((wiresOf (oneEach i j) C.gates).getD a false)
                change b2z (g.op.eval [_]) = c0 + c1 * val a i j at hanf
                rw [hanf, hca_eq i j, mul_add, mul_add, Finset.mul_sum]
                have hsm : ∑ p : NL, c1 * (ca p * val (n + m + p.val.val) i j) =
                    ∑ p : NL, c1 * ca p * val (n + m + p.val.val) i j :=
                  Finset.sum_congr rfl fun p _ => by ring
                rw [hsm]; ring
            | [a, b] =>
              have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
              have hb_lt : b < n + m + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
              have hab_d : dep a ≤ dep (n + m + idx.val) ∧ dep b ≤ dep (n + m + idx.val) := by
                change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
                rw [hg_in] at hdg
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
                omega
              obtain ⟨ra, sa, ca, hca_supp, hca_eq⟩ := ih a (by omega)
              obtain ⟨rb, sb, cb, hcb_supp, hcb_eq⟩ := ih b (by omega)
              have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                unfold nlGate at hnlf; rw [hg_in] at hnlf; simpa using hnlf
              let c0 := b2z (g.op.eval [false, false])
              let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
              let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
              refine ⟨fun i => c0 + c1 * ra i + c2 * rb i,
                fun j => c1 * sa j + c2 * sb j,
                fun p => c1 * ca p + c2 * cb p, ?_, fun i j => ?_⟩
              · intro p hp
                by_cases h1 : ca p ≠ 0
                · have hs := hca_supp p h1; exact ⟨by omega, by omega⟩
                · push Not at h1
                  have h2 : cb p ≠ 0 := fun h => hp (by simp [h1, h])
                  have hs := hcb_supp p h2; exact ⟨by omega, by omega⟩
              · rw [hval_gate idx.val idx.isLt i j]
                change b2z (g.op.eval (g.inputs.map _)) = _
                rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
                have hanf := anf_two (fun x y => g.op.eval [x, y])
                  ((wiresOf (oneEach i j) C.gates).getD a false)
                  ((wiresOf (oneEach i j) C.gates).getD b false)
                rw [hxor] at hanf
                have hbf : b2z false = 0 := rfl
                change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
                rw [hbf, zero_mul, add_zero] at hanf
                rw [hanf, hca_eq i j, hcb_eq i j]
                have hsm : ∑ p : NL, (c1 * ca p + c2 * cb p) * val (n + m + p.val.val) i j =
                    c1 * (∑ p : NL, ca p * val (n + m + p.val.val) i j) +
                    c2 * (∑ p : NL, cb p * val (n + m + p.val.val) i j) := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl fun p _ => by ring
                rw [hsm]; ring
            | _ :: _ :: _ :: _ =>
              rw [hg_in] at hgl; simp at hgl
        · refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, by simp, fun i j => ?_⟩
          unfold val
          have hge : (wiresOf (oneEach i j) C.gates).length ≤ k := by
            rw [wiresOf_length, oneEach_length]; omega
          rw [List.getD_eq_default _ _ hge]; simp [b2z]
  have hNL_inputs : ∀ p : NL, ∃ a b : ℕ,
      (C.gates[p.val.val]).inputs = [a, b] ∧
      a < n + m + p.val.val ∧ b < n + m + p.val.val ∧
      dep a + 1 ≤ dep (n + m + p.val.val) ∧ dep b + 1 ≤ dep (n + m + p.val.val) := by
    intro p
    have hnl : nlGate (C.gates[p.val.val]) = true := (Finset.mem_filter.mp p.property).2
    have hlen2 : (C.gates[p.val.val]).inputs.length = 2 := by
      unfold nlGate at hnl; rw [Bool.and_eq_true] at hnl; simpa using hnl.1
    obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[p.val.val]).inputs = [a, b] := by
      match h : (C.gates[p.val.val]).inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [h] at hlen2; simp at hlen2
      | [_] => rw [h] at hlen2; simp at hlen2
      | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
    have ha := hrb' p.val.val p.val.isLt a (by rw [hab]; simp)
    have hb := hrb' p.val.val p.val.isLt b (by rw [hab]; simp)
    have hdg := hdep_gate p.val.val p.val.isLt
    rw [hab, hnl] at hdg
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdg
    exact ⟨a, b, hab, ha, hb, by omega, by omega⟩
  choose in1 in2 hin_eq hin1_lt hin2_lt hin1_d hin2_d using hNL_inputs
  choose rw1 sw1 cw1 hcw1_supp hcw1_eq using fun p : NL => hdecomp_wire (in1 p)
  choose rw2 sw2 cw2 hcw2_supp hcw2_eq using fun p : NL => hdecomp_wire (in2 p)
  let K := NL ⊕ NL
  let α : K → Fin n → ZMod 2 := fun x i =>
    match x with
    | Sum.inl p => rw1 p i + rw1 p u
    | Sum.inr p => rw2 p i + rw2 p u
  let β : K → Fin m → ZMod 2 := fun y j =>
    match y with
    | Sum.inl p => sw1 p j + sw1 p v
    | Sum.inr p => sw2 p j + sw2 p v
  have hα0 : ∀ x : K, α x u = 0 := by
    rintro (p | p) <;> simp [α, zmod2_add_self]
  have hβ0 : ∀ y : K, β y v = 0 := by
    rintro (p | p) <;> simp [β, zmod2_add_self]
  have hNL_poly : ∀ m_idx : ℕ, ∀ p : NL, p.val.val = m_idx →
      val (n + m + p.val.val) ∈ PolyDeg α β (2 ^ dep (n + m + p.val.val)) := by
    intro m_idx
    induction m_idx using Nat.strong_induction_on with
    | ind m_idx ih =>
      intro p hp_eq
      have hdp_pos : 1 ≤ dep (n + m + p.val.val) := by
        have := hin1_d p; omega
      have hpow_pos : 1 ≤ 2 ^ (dep (n + m + p.val.val) - 1) := Nat.one_le_two_pow
      have h1_in : val (in1 p) ∈ PolyDeg α β (2 ^ (dep (n + m + p.val.val) - 1)) := by
        have hfun : val (in1 p) =
            (fun _ _ => rw1 p u + sw1 p v) +
            (fun i _ => α (Sum.inl p) i) +
            (fun _ j => β (Sum.inl p) j) +
            ∑ q : NL, cw1 p q • val (n + m + q.val.val) := by
          funext i j
          rw [hcw1_eq p i j]
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, α, β]
          have h2 : rw1 p i + sw1 p j =
              (rw1 p u + sw1 p v) + (rw1 p i + rw1 p u) + (sw1 p j + sw1 p v) := by
            have : (rw1 p u + sw1 p v) + (rw1 p i + rw1 p u) + (sw1 p j + sw1 p v) =
                rw1 p i + sw1 p j + ((rw1 p u + rw1 p u) + (sw1 p v + sw1 p v)) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
          rw [h2]
        rw [hfun]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (polyDeg_const α β _ _) (polyDeg_alpha α β hpow_pos (Sum.inl p)))
          (polyDeg_beta α β hpow_pos (Sum.inl p))) ?_
        apply Submodule.sum_mem
        intro q _
        by_cases hq0 : cw1 p q = 0
        · rw [hq0, zero_smul]; exact Submodule.zero_mem _
        · apply Submodule.smul_mem
          have hsupp := hcw1_supp p q hq0
          have hqlt : q.val.val < m_idx := by have := hin1_lt p; omega
          have hqd : dep (n + m + q.val.val) ≤ dep (n + m + p.val.val) - 1 := by
            have := hin1_d p; omega
          exact polyDeg_mono α β (Nat.pow_le_pow_right (by norm_num) hqd) (ih q.val.val hqlt q rfl)
      have h2_in : val (in2 p) ∈ PolyDeg α β (2 ^ (dep (n + m + p.val.val) - 1)) := by
        have hfun : val (in2 p) =
            (fun _ _ => rw2 p u + sw2 p v) +
            (fun i _ => α (Sum.inr p) i) +
            (fun _ j => β (Sum.inr p) j) +
            ∑ q : NL, cw2 p q • val (n + m + q.val.val) := by
          funext i j
          rw [hcw2_eq p i j]
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, α, β]
          have h2 : rw2 p i + sw2 p j =
              (rw2 p u + sw2 p v) + (rw2 p i + rw2 p u) + (sw2 p j + sw2 p v) := by
            have : (rw2 p u + sw2 p v) + (rw2 p i + rw2 p u) + (sw2 p j + sw2 p v) =
                rw2 p i + sw2 p j + ((rw2 p u + rw2 p u) + (sw2 p v + sw2 p v)) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
          rw [h2]
        rw [hfun]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (polyDeg_const α β _ _) (polyDeg_alpha α β hpow_pos (Sum.inr p)))
          (polyDeg_beta α β hpow_pos (Sum.inr p))) ?_
        apply Submodule.sum_mem
        intro q _
        by_cases hq0 : cw2 p q = 0
        · rw [hq0, zero_smul]; exact Submodule.zero_mem _
        · apply Submodule.smul_mem
          have hsupp := hcw2_supp p q hq0
          have hqlt : q.val.val < m_idx := by have := hin2_lt p; omega
          have hqd : dep (n + m + q.val.val) ≤ dep (n + m + p.val.val) - 1 := by
            have := hin2_d p; omega
          exact polyDeg_mono α β (Nat.pow_le_pow_right (by norm_num) hqd) (ih q.val.val hqlt q rfl)
      let g := C.gates[p.val.val]
      have hnl : nlGate g = true := (Finset.mem_filter.mp p.property).2
      have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
        unfold nlGate at hnl; rw [Bool.and_eq_true] at hnl; exact hnl.2
      let c0 := b2z (g.op.eval [false, false])
      let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
      let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
      have hfun : val (n + m + p.val.val) =
          (fun _ _ => c0) + c1 • val (in1 p) + c2 • val (in2 p) +
          (fun i j => val (in1 p) i j * val (in2 p) i j) := by
        funext i j
        rw [hval_gate p.val.val p.val.isLt i j]
        change b2z (g.op.eval (g.inputs.map _)) = _
        rw [hin_eq p, List.map_cons, List.map_cons, List.map_nil]
        have hanf := anf_two (fun x y => g.op.eval [x, y])
          ((wiresOf (oneEach i j) C.gates).getD (in1 p) false)
          ((wiresOf (oneEach i j) C.gates).getD (in2 p) false)
        rw [hxor] at hanf
        have hbt : b2z true = 1 := rfl
        change b2z (g.op.eval [_, _]) =
          c0 + c1 * val (in1 p) i j + c2 * val (in2 p) i j +
          b2z true * (val (in1 p) i j * val (in2 p) i j) at hanf
        rw [hbt, one_mul] at hanf
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hanf
      have h2eq : 2 ^ (dep (n + m + p.val.val) - 1) + 2 ^ (dep (n + m + p.val.val) - 1) =
          2 ^ dep (n + m + p.val.val) := by
        have hsucc : dep (n + m + p.val.val) = (dep (n + m + p.val.val) - 1) + 1 := by omega
        conv_rhs => rw [hsucc, pow_succ]
        omega
      have hle_half : 2 ^ (dep (n + m + p.val.val) - 1) ≤ 2 ^ dep (n + m + p.val.val) := by
        omega
      rw [hfun]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (polyDeg_const α β _ _)
        (Submodule.smul_mem _ _ (polyDeg_mono α β hle_half h1_in)))
        (Submodule.smul_mem _ _ (polyDeg_mono α β hle_half h2_in))) ?_
      rw [← h2eq]
      exact polyDeg_mul α β h1_in h2_in
  obtain ⟨rout, sout, cout, hcout_supp, hcout_eq⟩ := hdecomp_wire C.output
  let f_poly : Fin n → Fin m → ZMod 2 := fun i j =>
    ∑ p : NL, cout p * val (n + m + p.val.val) i j
  have hf_in : f_poly ∈ PolyDeg α β (2 * 2 ^ d) := by
    have hfun : f_poly = ∑ p : NL, cout p • val (n + m + p.val.val) := by
      funext i j; simp [f_poly]
    rw [hfun]
    apply Submodule.sum_mem
    intro p _
    by_cases hp0 : cout p = 0
    · rw [hp0, zero_smul]; exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      have hdp : dep (n + m + p.val.val) ≤ d + 1 :=
        le_trans (hcout_supp p hp0).2 hdep
      have hpow : 2 ^ dep (n + m + p.val.val) ≤ 2 * 2 ^ d := by
        calc 2 ^ dep (n + m + p.val.val) ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) hdp
          _ = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
      exact polyDeg_mono α β hpow (hNL_poly p.val.val p rfl)
  have hAeq : anchor u v (fun i j => b2z (G i j)) = anchor u v f_poly := by
    have h1 : (fun i j => b2z (G i j)) = fun i j => (rout i + sout j) + f_poly i j := by
      funext i j
      have hval_out : b2z (G i j) = val C.output i j := by
        unfold val; rw [← hrep i j]; rfl
      rw [hval_out, hcout_eq i j]
    rw [h1, anchor_add, anchor_split, zero_add]
  rw [hAeq]
  have hKcard : Fintype.card K = 2 * t := by
    simp only [K, Fintype.card_sum, Fintype.card_coe, hNL_card]
    omega
  rw [← hKcard]
  exact rank_anchor_polyDeg u v α β hα0 hβ0 (2 ^ d) hf_in

def shiftWire (w0 off a : ℕ) : ℕ := if a < w0 then a else a + off

def shiftGate (w0 off : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire w0 off)⟩

lemma nlGate_shiftGate (w0 off : ℕ) (g : Gate) :
    nlGate (shiftGate w0 off g) = nlGate g := by
  simp [nlGate, shiftGate]

lemma shift_append_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs)
    (C : Circuit) (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (n + m) C) :
    let gs' := gs ++ C.gates.map (shiftGate (n + m) gs.length)
    Valid n m gs' ∧ gs'.length = gs.length + C.gates.length ∧
    gs'.countP nlGate = gs.countP nlGate + C.gates.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (∀ k < n + m + C.gates.length,
      (depthsOf (n + m) gs').getD (shiftWire (n + m) gs.length k) 0 =
        (depthsOf (n + m) C.gates).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + C.gates.length,
      (wiresOf (oneEach i j) gs').getD (shiftWire (n + m) gs.length k) false =
        (wiresOf (oneEach i j) C.gates).getD k false) := by
  intro gs'
  have hv' : Valid n m gs' := by
    refine ⟨?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hv.1 g hg
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
        simpa [shiftGate] using hlen g0 hg0
    · intro j hj a ha
      change j < gs'.length at hj
      change a ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs at ha
      by_cases hj' : j < gs.length
      · rw [List.getD_append _ _ _ _ hj'] at ha
        exact hv.2 j hj' a ha
      · have hlen_gs' : gs'.length = gs.length + C.gates.length := by simp [gs']
        have hj0 : j - gs.length < C.gates.length := by omega
        rw [List.getD_append_right _ _ _ _ (by omega)] at ha
        rw [List.getD_eq_getElem _ _ (by simp [hj0]), List.getElem_map] at ha
        obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
        have hrb0 : a0 < n + m + (j - gs.length) := by
          have h := hrb (j - gs.length) hj0 a0
          unfold gateAt at h
          rw [List.getD_eq_getElem _ _ hj0] at h
          exact h ha0
        unfold shiftWire
        split_ifs <;> omega
  have hlen' : gs'.length = gs.length + C.gates.length := by simp [gs']
  have hcnt' : gs'.countP nlGate = gs.countP nlGate + C.gates.countP nlGate := by
    simp only [gs', List.countP_append, List.countP_map]
    congr 1
    refine List.countP_congr fun g _ => ?_
    simp [nlGate_shiftGate]
  have hd_old : ∀ k < n + m + gs.length,
      (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0 :=
    fun k hk => depthsOf_append_getD_lt (n + m) gs _ hk
  have hw_old : ∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false :=
    fun i j k hk => wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  have hd_new : ∀ k < n + m + C.gates.length,
      (depthsOf (n + m) gs').getD (shiftWire (n + m) gs.length k) 0 =
        (depthsOf (n + m) C.gates).getD k 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      by_cases hkin : k < n + m
      · simp only [shiftWire, hkin, ite_true]
        rw [depthsOf_getD_input (n + m) gs' hkin, depthsOf_getD_input (n + m) C.gates hkin]
      · simp only [shiftWire, hkin, ite_false]
        let idx := k - (n + m)
        have hidx : idx < C.gates.length := by omega
        have hkeq : k = n + m + idx := by omega
        have hkshift : k + gs.length = n + m + (gs.length + idx) := by omega
        rw [hkshift]
        have hrb_idx : ∀ a ∈ (C.gates[idx]).inputs, a < n + m + idx := by
          intro a ha
          have h := hrb idx hidx a
          unfold gateAt at h
          rw [List.getD_eq_getElem _ _ hidx] at h
          exact h ha
        have hidx' : gs.length + idx < gs'.length := by omega
        have hget_gs' : gs'[gs.length + idx] = shiftGate (n + m) gs.length (C.gates[idx]) := by
          simp only [gs']
          rw [List.getElem_append_right (by omega)]
          simp only [Nat.add_sub_cancel_left, List.getElem_map]
        have hrb_gs' : ∀ a ∈ (gs'[gs.length + idx]).inputs, a < n + m + (gs.length + idx) := by
          intro a ha
          have h := hv'.2 (gs.length + idx) hidx' a
          unfold gateAt at h
          rw [List.getD_eq_getElem _ _ hidx'] at h
          exact h ha
        rw [depthsOf_getD_gate (n + m) gs' hidx' hrb_gs']
        conv_rhs => rw [hkeq, depthsOf_getD_gate (n + m) C.gates hidx hrb_idx]
        rw [hget_gs', nlGate_shiftGate]
        congr 2
        simp only [shiftGate, List.map_map]
        apply List.map_congr_left
        intro a ha
        have halt : a < n + m + idx := hrb_idx a ha
        exact ih a (by omega) (by omega)
  have hw_new : ∀ (i : Fin n) (j : Fin m), ∀ k < n + m + C.gates.length,
      (wiresOf (oneEach i j) gs').getD (shiftWire (n + m) gs.length k) false =
        (wiresOf (oneEach i j) C.gates).getD k false := by
    intro i j k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      by_cases hkin : k < n + m
      · simp only [shiftWire, hkin, ite_true]
        rw [wiresOf_getD_input _ gs' (by rw [oneEach_length]; exact hkin),
          wiresOf_getD_input _ C.gates (by rw [oneEach_length]; exact hkin)]
      · simp only [shiftWire, hkin, ite_false]
        let idx := k - (n + m)
        have hidx : idx < C.gates.length := by omega
        have hkeq : k = n + m + idx := by omega
        have hkshift : k + gs.length = (oneEach i j).length + (gs.length + idx) := by
          rw [oneEach_length]; omega
        rw [hkshift]
        have hrb_idx : ∀ a ∈ (C.gates[idx]).inputs, a < (oneEach i j).length + idx := by
          intro a ha
          rw [oneEach_length]
          have h := hrb idx hidx a
          unfold gateAt at h
          rw [List.getD_eq_getElem _ _ hidx] at h
          exact h ha
        have hidx' : gs.length + idx < gs'.length := by omega
        have hget_gs' : gs'[gs.length + idx] = shiftGate (n + m) gs.length (C.gates[idx]) := by
          simp only [gs']
          rw [List.getElem_append_right (by omega)]
          simp only [Nat.add_sub_cancel_left, List.getElem_map]
        have hrb_gs' : ∀ a ∈ (gs'[gs.length + idx]).inputs, a < (oneEach i j).length + (gs.length + idx) := by
          intro a ha
          rw [oneEach_length]
          have h := hv'.2 (gs.length + idx) hidx' a
          unfold gateAt at h
          rw [List.getD_eq_getElem _ _ hidx'] at h
          exact h ha
        rw [wiresOf_getD_gate (oneEach i j) gs' hidx' hrb_gs']
        have hkeq' : k = (oneEach i j).length + idx := by rw [oneEach_length]; exact hkeq
        conv_rhs => rw [hkeq', wiresOf_getD_gate (oneEach i j) C.gates hidx hrb_idx]
        rw [hget_gs']
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < n + m + idx := by rw [← oneEach_length i j]; exact hrb_idx a ha
        exact ih a (by omega) (by omega)
  exact ⟨hv', hlen', hcnt', hd_old, hw_old, hd_new, hw_new⟩

lemma build_and_tree {n m : ℕ} (d : ℕ) :
    ∀ (ws : List ℕ) (gs : List Gate),
      Valid n m gs → 1 ≤ ws.length → ws.length ≤ 2 ^ d →
      (∀ w ∈ ws, w < n + m + gs.length) →
      (∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 1) →
      ∃ (gs' : List Gate) (out : ℕ),
        Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
        gs'.countP nlGate = gs.countP nlGate + (ws.length - 1) ∧
        (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
        (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
          (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
        (depthsOf (n + m) gs').getD out 0 ≤ d + 1 ∧
        (∀ (i : Fin n) (j : Fin m),
          (wiresOf (oneEach i j) gs').getD out false =
            ws.all (fun w => (wiresOf (oneEach i j) gs).getD w false)) := by
  induction d with
  | zero =>
    intro ws gs hv hge1 hle1 hwb hwd
    match hws : ws with
    | [] => simp at hge1
    | [w] =>
      refine ⟨gs, w, hv, le_rfl, hwb w (by simp), by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
        hwd w (by simp), fun i j => by simp⟩
    | _ :: _ :: _ => simp at hle1
  | succ d ih =>
    intro ws gs hv hge1 hle hwb hwd
    by_cases hsmall : ws.length ≤ 2 ^ d
    · obtain ⟨gs', out, hv', hlen', hout, hcnt', hd', hw', hdout, hval⟩ :=
        ih ws gs hv hge1 hsmall hwb hwd
      exact ⟨gs', out, hv', hlen', hout, hcnt', hd', hw', by omega, hval⟩
    · let ws1 := ws.take (2 ^ d)
      let ws2 := ws.drop (2 ^ d)
      have hws_eq : ws = ws1 ++ ws2 := (List.take_append_drop (2 ^ d) ws).symm
      have hlen1 : ws1.length = 2 ^ d := List.length_take_of_le (by omega)
      have hlen2 : ws2.length = ws.length - 2 ^ d := List.length_drop
      have hpow_pos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have h2le : ws2.length ≤ 2 ^ d := by
        have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; omega
        omega
      have hmem1 : ∀ w ∈ ws1, w ∈ ws := fun w hw => by rw [hws_eq]; exact List.mem_append_left _ hw
      have hmem2 : ∀ w ∈ ws2, w ∈ ws := fun w hw => by rw [hws_eq]; exact List.mem_append_right _ hw
      obtain ⟨gs1, out1, hv1, hlen_g1, hout1, hcnt1, hd1, hw1, hdout1, hval1⟩ :=
        ih ws1 gs hv (by omega) (by omega) (fun w hw => hwb w (hmem1 w hw))
          (fun w hw => hwd w (hmem1 w hw))
      obtain ⟨gs2, out2, hv2, hlen_g2, hout2, hcnt2, hd2, hw2, hdout2, hval2⟩ :=
        ih ws2 gs1 hv1 (by omega) h2le
          (fun w hw => by have := hwb w (hmem2 w hw); omega)
          (fun w hw => by rw [hd1 w (hwb w (hmem2 w hw))]; exact hwd w (hmem2 w hw))
      have hout1_2 : out1 < n + m + gs2.length := by omega
      obtain ⟨hv3, hlen3, hcnt3, hd3, hw3, hdout3, hval3⟩ :=
        pushAnd_spec hv2 hout1_2 hout2
      refine ⟨pushAnd gs2 out1 out2, n + m + gs2.length, hv3, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · intro k hk
        rw [hd3 k (by omega), hd2 k (by omega), hd1 k hk]
      · intro i j k hk
        rw [hw3 i j k (by omega), hw2 i j k (by omega), hw1 i j k hk]
      · rw [hdout3, hd2 out1 hout1]
        omega
      · intro i j
        have hb := hval3 i j
        rw [hw2 i j out1 hout1, hval1 i j, hval2 i j] at hb
        have hws2_eq : ws2.all (fun w => (wiresOf (oneEach i j) gs1).getD w false) =
            ws2.all (fun w => (wiresOf (oneEach i j) gs).getD w false) := by
          rw [Bool.eq_iff_iff]
          simp only [List.all_eq_true]
          constructor
          · intro h w hw; rw [← hw1 i j w (hwb w (hmem2 w hw))]; exact h w hw
          · intro h w hw; rw [hw1 i j w (hwb w (hmem2 w hw))]; exact h w hw
        rw [hws2_eq] at hb
        apply b2z_inj
        rw [hb, hws_eq, List.all_append, b2z_and]

lemma slice_eq_rank {N off w : ℕ} (hN : 0 < N) (hw : 0 < w) :
    (anchor ⟨0, hN⟩ ⟨0, hN⟩ (fun i j =>
      b2z (decide ((i.val / 2 ^ off) % 2 ^ w = (j.val / 2 ^ off) % 2 ^ w)))).rank ≤
      2 * (2 ^ (w - 1) - 1) := by
  let W := 2 ^ w
  have hWpos : 0 < W := by positivity
  let proj : Fin N → Fin W := fun i => ⟨(i.val / 2 ^ off) % W, Nat.mod_lt _ hWpos⟩
  have hA : anchor ⟨0, hN⟩ ⟨0, hN⟩ (fun i j =>
      b2z (decide ((i.val / 2 ^ off) % W = (j.val / 2 ^ off) % W))) =
      Matrix.of (fun i j =>
        anchor (0 : Fin W) (0 : Fin W) (fun a b => b2z (decide (a = b))) (proj i) (proj j)) := by
    ext i j
    simp only [anchor, Matrix.of_apply]
    have h0 : (0 : Fin W).val = 0 := rfl
    have heq1 : ((i.val / 2 ^ off) % W = (j.val / 2 ^ off) % W) ↔ (proj i = proj j) := by
      simp [proj, Fin.ext_iff]
    have heq2 : ((i.val / 2 ^ off) % W = (0 / 2 ^ off) % W) ↔ (proj i = 0) := by
      simp [proj, Fin.ext_iff, h0]
    have heq3 : ((0 / 2 ^ off) % W = (j.val / 2 ^ off) % W) ↔ (0 = proj j) := by
      simp [proj, Fin.ext_iff, h0]
    simp only [heq1, heq2, heq3]
  rw [hA]
  have hr := le_trans (pullback_rank_le proj proj _) (eq_anchor_rank_le w hw)
  have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by
    have : w = (w - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  calc (Matrix.of (fun i j =>
      anchor (0 : Fin W) (0 : Fin W) (fun a b => b2z (decide (a = b))) (proj i) (proj j))).rank
      ≤ 2 ^ w - 2 := hr
    _ = 2 * (2 ^ (w - 1) - 1) := by omega

lemma build_blocks {N : ℕ} (hN : 0 < N) :
    ∀ (off : ℕ) (ws : List ℕ) (gs : List Gate),
      Valid N N gs → (∀ w ∈ ws, 1 ≤ w) →
      ∃ (gs' : List Gate) (outs : List ℕ),
        Valid N N gs' ∧ gs.length ≤ gs'.length ∧ outs.length = ws.length ∧
        gs'.countP nlGate ≤ gs.countP nlGate + (ws.map (fun w => 2 ^ (w - 1) - 1)).sum ∧
        (∀ k < N + N + gs.length, (depthsOf (N + N) gs').getD k 0 = (depthsOf (N + N) gs).getD k 0) ∧
        (∀ (i j : Fin N), ∀ k < N + N + gs.length,
          (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
        (∀ w ∈ outs, w < N + N + gs'.length) ∧
        (∀ w ∈ outs, (depthsOf (N + N) gs').getD w 0 ≤ 1) ∧
        (∀ (i j : Fin N),
          outs.all (fun w => (wiresOf (oneEach i j) gs').getD w false) = true ↔
          (i.val / 2 ^ off) % 2 ^ ws.sum = (j.val / 2 ^ off) % 2 ^ ws.sum) := by
  intro off ws
  induction ws generalizing off with
  | nil =>
    intro gs hv _
    exact ⟨gs, [], hv, le_rfl, rfl, by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
      by simp, by simp, fun i j => by simp [Nat.mod_one]⟩
  | cons w ws ih =>
    intro gs hv hw_pos
    have hw1 : 1 ≤ w := hw_pos w (by simp)
    let G0 : Fin N → Fin N → Bool := fun i j =>
      decide ((i.val / 2 ^ off) % 2 ^ w = (j.val / 2 ^ off) % 2 ^ w)
    have hrank : (anchor ⟨0, hN⟩ ⟨0, hN⟩ (fun i j => b2z (G0 i j))).rank ≤
        2 * (2 ^ (w - 1) - 1) := slice_eq_rank hN hw1
    obtain ⟨C0, ⟨hlen0, hrb0, hrep0⟩, hd0, hcnt0⟩ :=
      dir_ge G0 ⟨0, hN⟩ ⟨0, hN⟩ (2 ^ (w - 1) - 1) hrank
    have hstep1 : ∃ (gs1 : List Gate) (out1 : ℕ),
        Valid N N gs1 ∧ gs.length ≤ gs1.length ∧ out1 < N + N + gs1.length ∧
        gs1.countP nlGate ≤ gs.countP nlGate + (2 ^ (w - 1) - 1) ∧
        (∀ k < N + N + gs.length, (depthsOf (N + N) gs1).getD k 0 = (depthsOf (N + N) gs).getD k 0) ∧
        (∀ (i j : Fin N), ∀ k < N + N + gs.length,
          (wiresOf (oneEach i j) gs1).getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
        (depthsOf (N + N) gs1).getD out1 0 ≤ 1 ∧
        (∀ i j : Fin N, (wiresOf (oneEach i j) gs1).getD out1 false = G0 i j) := by
      by_cases hout_lt : C0.output < N + N + C0.gates.length
      · obtain ⟨hv1, hlen1, hcnt1, hd_old, hw_old, hd1, hw1'⟩ := shift_append_spec hv C0 hlen0 hrb0
        refine ⟨gs ++ C0.gates.map (shiftGate (N + N) gs.length),
          shiftWire (N + N) gs.length C0.output, hv1, by omega, ?_, by omega,
          hd_old, hw_old, ?_, ?_⟩
        · unfold shiftWire; split_ifs <;> omega
        · rw [hd1 C0.output hout_lt]; exact hd0
        · intro i j
          rw [hw1' i j C0.output hout_lt]
          exact hrep0 i j
      · obtain ⟨hv1, hlen1, hcnt1, hd_old, hw_old, hd1, hw1'⟩ := pushFalse_spec hv
        refine ⟨pushFalse gs, N + N + gs.length, hv1, by omega, by omega, by omega,
          hd_old, hw_old, by omega, fun i j => ?_⟩
        have hfalse : G0 i j = false := by
          have hr := hrep0 i j
          unfold Circuit.eval Circuit.wires at hr
          have hge : (wiresOf (oneEach i j) C0.gates).length ≤ C0.output := by
            rw [wiresOf_length, oneEach_length]; omega
          have hdef := List.getD_eq_default (wiresOf (oneEach i j) C0.gates) false hge
          exact hr.symm.trans hdef
        have hb := hw1' i j
        rw [hfalse]
        apply b2z_inj
        exact hb
    obtain ⟨gs1, out1, hv1, hlen1, hout1, hcnt1, hd_old1, hw_old1, hdout1, hval1⟩ := hstep1
    obtain ⟨gs2, outs2, hv2, hlen2, hlouts2, hcnt2, hd_old2, hw_old2, hout2_lt, hdout2, hall2⟩ :=
      ih (off + w) gs1 hv1 (fun w' hw' => hw_pos w' (by simp [hw']))
    refine ⟨gs2, out1 :: outs2, hv2, by omega, by simp [hlouts2], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · intro k hk
      rw [hd_old2 k (by omega), hd_old1 k hk]
    · intro i j k hk
      rw [hw_old2 i j k (by omega), hw_old1 i j k hk]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact hout2_lt x hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hd_old2 x hout1]; exact hdout1
      · exact hdout2 x hx
    · intro i j
      simp only [List.all_cons, Bool.and_eq_true, List.sum_cons, pow_add]
      rw [hw_old2 i j out1 hout1, hval1 i j, hall2 i j]
      simp only [G0, decide_eq_true_eq]
      have hsplit : ∀ z : ℕ, (z / 2 ^ off) % (2 ^ w * 2 ^ ws.sum) =
          (z / 2 ^ off) % 2 ^ w + 2 ^ w * ((z / 2 ^ (off + w)) % 2 ^ ws.sum) := by
        intro z
        rw [Nat.mod_mul, pow_add, Nat.div_div_eq_div_mul]
      rw [hsplit i.val, hsplit j.val]
      constructor
      · rintro ⟨h1, h2⟩; rw [h1, h2]
      · intro heq
        have hlt_i : (i.val / 2 ^ off) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
        have hlt_j : (j.val / 2 ^ off) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
        have hmod : ((i.val / 2 ^ off) % 2 ^ w + 2 ^ w * ((i.val / 2 ^ (off + w)) % 2 ^ ws.sum)) % 2 ^ w =
            ((j.val / 2 ^ off) % 2 ^ w + 2 ^ w * ((j.val / 2 ^ (off + w)) % 2 ^ ws.sum)) % 2 ^ w :=
          congrArg (· % 2 ^ w) heq
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hlt_i, Nat.mod_eq_of_lt hlt_j] at hmod
        refine ⟨hmod, ?_⟩
        have hpos : 0 < 2 ^ w := by positivity
        rw [hmod] at heq
        exact Nat.eq_of_mul_eq_mul_left hpos (Nat.add_left_cancel heq)

lemma upper_bound_eq (k d : ℕ) (hk : 0 < k) :
    let N := 2 ^ k
    let b := 2 ^ d
    let groups := min b k
    ∃ C : Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (N + N) C ∧
      Represents (fun u v : Fin N => decide (u = v)) C ∧
      (depthsOf (N + N) C.gates).getD C.output 0 ≤ d + 1 ∧
      C.gates.countP nlGate + 1 ≤ (groups + k % groups) * 2 ^ (k / groups - 1) := by
  intro N b groups
  have hNpos : 0 < N := by positivity
  have hbpos : 1 ≤ b := Nat.one_le_two_pow
  have hgpos : 1 ≤ groups := le_min hbpos hk
  have hgle_k : groups ≤ k := min_le_right b k
  have hgle_b : groups ≤ b := min_le_left b k
  let q := k / groups
  let rem := k % groups
  have hqpos : 1 ≤ q := Nat.div_pos hgle_k (by omega)
  have hrem_lt : rem < groups := Nat.mod_lt k (by omega)
  have hdiv : q * groups + rem = k := by
    dsimp only [q, rem]
    have := Nat.div_add_mod k groups
    linarith
  let ws : List ℕ := List.replicate rem (q + 1) ++ List.replicate (groups - rem) q
  have hws_len : ws.length = groups := by
    simp only [ws, List.length_append, List.length_replicate]
    omega
  have hws_sum : ws.sum = k := by
    simp only [ws, List.sum_append, List.sum_replicate, smul_eq_mul]
    have h1 : rem * (q + 1) + (groups - rem) * q = q * groups + rem := by
      have : rem * (q + 1) = rem * q + rem := by ring
      rw [this]
      have : rem * q + (groups - rem) * q = groups * q := by
        rw [← Nat.add_mul, Nat.add_sub_of_le (le_of_lt hrem_lt)]
      linarith
    omega
  have hws_pos : ∀ w ∈ ws, 1 ≤ w := by
    intro w hw
    simp only [ws, List.mem_append, List.mem_replicate] at hw
    rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  obtain ⟨gs1, outs, hv1, _, hlouts, hcnt1, _, _, hout_lt, hdout, hall⟩ :=
    build_blocks hNpos 0 ws [] (valid_nil N N) hws_pos
  obtain ⟨gs2, out, hv2, _, _, hcnt2, _, hw2, hdout2, hval2⟩ :=
    build_and_tree d outs gs1 hv1 (by omega) (by omega) hout_lt hdout
  refine ⟨⟨gs2, out⟩, hv2.1, hv2.2, ?_, hdout2, ?_⟩
  · intro u v
    change (wiresOf (oneEach u v) gs2).getD out false = decide (u = v)
    rw [hval2 u v]
    have hiff := hall u v
    rw [hws_sum, pow_zero, Nat.div_one, Nat.div_one,
      Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt v.isLt] at hiff
    rw [Bool.eq_iff_iff, hiff, decide_eq_true_eq, Fin.ext_iff]
  · change gs2.countP nlGate + 1 ≤ (groups + rem) * 2 ^ (q - 1)
    have hcost : (ws.map (fun w => 2 ^ (w - 1) - 1)).sum =
        rem * (2 ^ q - 1) + (groups - rem) * (2 ^ (q - 1) - 1) := by
      simp only [ws, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
        smul_eq_mul, Nat.add_sub_cancel]
    have h2q : 2 ^ q = 2 * 2 ^ (q - 1) := by
      have : q = (q - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ, mul_comm]
    have h2q1 : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
    have hcnt0 : ([] : List Gate).countP nlGate = 0 := rfl
    have hsum_eq : rem * (2 ^ q - 1) + (groups - rem) * (2 ^ (q - 1) - 1) + groups =
        (groups + rem) * 2 ^ (q - 1) := by
      rw [h2q]
      zify [h2q1, show 1 ≤ 2 * 2 ^ (q - 1) by omega, le_of_lt hrem_lt]
      ring
    omega

end PEqualNP.Outside.L_meta_25723


namespace PEqualNP.Outside.L_meta_25723

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.Outside.L_meta_25723.Base

lemma upper_bound_projected (k a d : ℕ) (hk : 0 < k) :
    let N := 2 ^ (k+a)
    let b := 2 ^ d
    let groups := min b k
    ∃ C : Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (N + N) C ∧
      Represents (fun u v : Fin N => decide (u.val % 2^k = v.val % 2^k)) C ∧
      (depthsOf (N + N) C.gates).getD C.output 0 ≤ d + 1 ∧
      C.gates.countP nlGate + 1 ≤ (groups + k % groups) * 2 ^ (k / groups - 1) := by
  intro N b groups
  have hNpos : 0 < N := by positivity
  have hbpos : 1 ≤ b := Nat.one_le_two_pow
  have hgpos : 1 ≤ groups := le_min hbpos hk
  have hgle_k : groups ≤ k := min_le_right b k
  have hgle_b : groups ≤ b := min_le_left b k
  let q := k / groups
  let rem := k % groups
  have hqpos : 1 ≤ q := Nat.div_pos hgle_k (by omega)
  have hrem_lt : rem < groups := Nat.mod_lt k (by omega)
  have hdiv : q * groups + rem = k := by
    dsimp only [q, rem]
    have := Nat.div_add_mod k groups
    linarith
  let ws : List ℕ := List.replicate rem (q + 1) ++ List.replicate (groups - rem) q
  have hws_len : ws.length = groups := by
    simp only [ws, List.length_append, List.length_replicate]
    omega
  have hws_sum : ws.sum = k := by
    simp only [ws, List.sum_append, List.sum_replicate, smul_eq_mul]
    have h1 : rem * (q + 1) + (groups - rem) * q = q * groups + rem := by
      have : rem * (q + 1) = rem * q + rem := by ring
      rw [this]
      have : rem * q + (groups - rem) * q = groups * q := by
        rw [← Nat.add_mul, Nat.add_sub_of_le (le_of_lt hrem_lt)]
      linarith
    omega
  have hws_pos : ∀ w ∈ ws, 1 ≤ w := by
    intro w hw
    simp only [ws, List.mem_append, List.mem_replicate] at hw
    rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  obtain ⟨gs1, outs, hv1, _, hlouts, hcnt1, _, _, hout_lt, hdout, hall⟩ :=
    build_blocks hNpos 0 ws [] (valid_nil N N) hws_pos
  obtain ⟨gs2, out, hv2, _, _, hcnt2, _, hw2, hdout2, hval2⟩ :=
    build_and_tree d outs gs1 hv1 (by omega) (by omega) hout_lt hdout
  refine ⟨⟨gs2, out⟩, hv2.1, hv2.2, ?_, hdout2, ?_⟩
  · intro u v
    change (wiresOf (oneEach u v) gs2).getD out false = decide (u.val % 2^k = v.val % 2^k)
    rw [hval2 u v]
    have hiff := hall u v
    rw [hws_sum, pow_zero, Nat.div_one, Nat.div_one] at hiff
    rw [Bool.eq_iff_iff, hiff, decide_eq_true_eq]
  · change gs2.countP nlGate + 1 ≤ (groups + rem) * 2 ^ (q - 1)
    have hcost : (ws.map (fun w => 2 ^ (w - 1) - 1)).sum =
        rem * (2 ^ q - 1) + (groups - rem) * (2 ^ (q - 1) - 1) := by
      simp only [ws, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
        smul_eq_mul, Nat.add_sub_cancel]
    have h2q : 2 ^ q = 2 * 2 ^ (q - 1) := by
      have : q = (q - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ, mul_comm]
    have h2q1 : 1 ≤ 2 ^ (q - 1) := Nat.one_le_two_pow
    have hcnt0 : ([] : List Gate).countP nlGate = 0 := rfl
    have hsum_eq : rem * (2 ^ q - 1) + (groups - rem) * (2 ^ (q - 1) - 1) + groups =
        (groups + rem) * 2 ^ (q - 1) := by
      rw [h2q]
      zify [h2q1, show 1 ≤ 2 * 2 ^ (q - 1) by omega, le_of_lt hrem_lt]
      ring
    omega

lemma projected_card (K A : ℕ) (hK : 0 < K) (i : Fin (K*A)) :
    ((Finset.univ : Finset (Fin (K*A))).filter (fun j => j.val % K = i.val % K)).card = A := by
  classical
  let S := (Finset.univ : Finset (Fin (K*A))).filter (fun j => j.val % K = i.val % K)
  have hi : i.val % K < K := Nat.mod_lt _ hK
  let φ : (j : Fin A) → Fin (K*A) := fun j => ⟨i.val % K + K*j.val, by
    have hv : j.val + 1 ≤ A := j.isLt
    have h := Nat.mul_le_mul_left K hv
    rw [Nat.mul_add,Nat.mul_one] at h
    omega⟩
  let e : Fin A ≃ S := {
    toFun := fun j => ⟨φ j, by simp [S,φ,Nat.mod_eq_of_lt hi]⟩
    invFun := fun j => ⟨j.val.val / K, (Nat.div_lt_iff_lt_mul hK).2 (by
      exact j.val.isLt.trans_le (Nat.le_of_eq (Nat.mul_comm K A)))⟩
    left_inv := by
      intro j
      apply Fin.ext
      change (i.val % K + K * j.val) / K = j.val
      rw [Nat.add_mul_div_left _ _ hK,Nat.div_eq_of_lt hi,Nat.zero_add]
    right_inv := by
      intro j
      apply Subtype.ext
      apply Fin.ext
      have eq : j.val.val % K = i.val % K := (Finset.mem_filter.mp j.property).2
      change i.val % K + K * (j.val.val / K) = j.val.val
      rw [← eq,Nat.add_comm,Nat.div_add_mod]
  }
  change S.card = A
  have hc := (Fintype.card_congr e).symm
  rw [Fintype.card_coe,Fintype.card_fin] at hc
  exact hc

end PEqualNP.Outside.L_meta_25723

namespace PEqualNP.Outside.L_meta_25723

open PEqualNP.Outside.L_meta_25723.Base

def boolMatrix {N : ℕ} (G : Fin N → Fin N → Bool) : Matrix (Fin N) (Fin N) (ZMod 2) :=
  fun i j => b2z (G i j)

def rowCount {N : ℕ} (G : Fin N → Fin N → Bool) (i : Fin N) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (fun j => G i j = true)).card

lemma rowCount_pos {N : ℕ} (G : Fin N → Fin N → Bool)
    (diag : ∀ i, G i i = true) (i : Fin N) : 0 < rowCount G i :=
  Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,diag i⟩⟩

def independentOnRestriction {N : ℕ} (G : Fin N → Fin N → Bool) (S : Finset (Fin N)) : Prop :=
  ∀ c : Fin N → ZMod 2,
    (∀ j ∈ S, ∑ i ∈ S, c i * boolMatrix G i j = 0) → ∀ i ∈ S, c i = 0

lemma greedyRank {N : ℕ} (G : Fin N → Fin N → Bool) (diag : ∀ i, G i i = true)
    (R : Finset (Fin N)) :
    ∃ S ⊆ R, independentOnRestriction G S ∧
      (∑ i ∈ R, (1 : ℝ) / rowCount G i) ≤ (S.card : ℝ) := by
  induction R using Finset.strongInduction with
  | H R ih =>
    by_cases empty : R = ∅
    · subst R
      exact ⟨∅,Finset.Subset.rfl,by simp [independentOnRestriction],by simp⟩
    have ne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image R (rowCount G) ne
    let gone := R.filter (fun j => G u j = true)
    let tail := R \ gone
    have goneSub : gone ⊆ R := Finset.filter_subset _ _
    have uGone : u ∈ gone := Finset.mem_filter.mpr ⟨hu,diag u⟩
    have uNot : u ∉ tail := fun h => (Finset.mem_sdiff.mp h).2 uGone
    have pSub : tail ⊂ R := by
      apply Finset.ssubset_iff_subset_ne.mpr
      exact ⟨Finset.sdiff_subset,fun h => uNot (h.symm ▸ hu)⟩
    obtain ⟨S,hS,cert,lower⟩ := ih tail pSub
    have notS : u ∉ S := fun h => uNot (hS h)
    have z (j : Fin N) (hj : j ∈ S) : boolMatrix G u j = 0 := by
      have hTail := Finset.mem_sdiff.mp (hS hj)
      cases g : G u j
      · simp [boolMatrix,b2z,g]
      · exact False.elim (hTail.2 (Finset.mem_filter.mpr ⟨hTail.1,g⟩))
    refine ⟨insert u S,Finset.insert_subset hu (hS.trans Finset.sdiff_subset),?_,?_⟩
    · intro c H j hj
      have hSzero : ∀ r ∈ S, ∑ s ∈ S, c s * boolMatrix G s r = 0 := by
        intro r hr
        have h := H r (Finset.mem_insert_of_mem hr)
        rw [Finset.sum_insert notS,z r hr,mul_zero,zero_add] at h
        exact h
      have coeff := cert c hSzero
      rcases Finset.mem_insert.mp hj with eq | hm
      · subst j
        have h := H u (Finset.mem_insert_self _ _)
        have sum0 : (∑ s ∈ S, c s * boolMatrix G s u) = 0 := by
          apply Finset.sum_eq_zero
          intro s hs
          rw [coeff s hs,zero_mul]
        rw [Finset.sum_insert notS,sum0,add_zero,show boolMatrix G u u = 1 by simp [boolMatrix,b2z,diag],mul_one] at h
        exact h
      · exact coeff j hm
    · have cGone : gone.card ≤ rowCount G u := Finset.card_le_card (by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩)
      have up : (0 : ℝ) < rowCount G u := by exact_mod_cast rowCount_pos G diag u
      have goneBound : (∑ j ∈ gone, (1 : ℝ) / rowCount G j) ≤ 1 := by
        calc
          _ ≤ ∑ _ ∈ gone, (1 : ℝ) / rowCount G u := by
            apply Finset.sum_le_sum
            intro j hj
            exact one_div_le_one_div_of_le up (by exact_mod_cast hmin j (goneSub hj))
          _ = (gone.card : ℝ) * (1 / rowCount G u) := by simp [nsmul_eq_mul]
          _ ≤ (rowCount G u : ℝ) * (1 / rowCount G u) := by
            apply mul_le_mul_of_nonneg_right (by exact_mod_cast cGone)
            positivity
          _ = 1 := by field_simp
      have eq := Finset.sum_sdiff (f := fun i => (1 : ℝ) / rowCount G i) goneSub
      change (∑ i ∈ tail, (1 : ℝ) / rowCount G i) + (∑ i ∈ gone, (1 : ℝ) / rowCount G i) =
        ∑ i ∈ R, (1 : ℝ) / rowCount G i at eq
      rw [Finset.card_insert_of_notMem notS,Nat.cast_add,Nat.cast_one,← eq]
      linarith

lemma independentCardLeRank {N : ℕ} (G : Fin N → Fin N → Bool) (S : Finset (Fin N))
    (tri : independentOnRestriction G S) : S.card ≤ (boolMatrix G).rank := by
  have li : LinearIndepOn (ZMod 2) (boolMatrix G).row S :=
    linearIndepOn_finset_iff.mpr (by
      intro c eq
      apply tri c
      intro j hj
      have h := congrFun eq j
      simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.row_apply,Pi.zero_apply] using h)
  let A : Matrix S (Fin N) (ZMod 2) := (boolMatrix G).submatrix Subtype.val id
  have lin : LinearIndependent (ZMod 2) A.row := li
  have hr : A.rank = S.card := by simpa using lin.rank_matrix
  rw [← hr]
  exact Matrix.rank_submatrix_le (boolMatrix G) Subtype.val id

lemma sparseRank {K A : ℕ} (hK : 0 < K) (hA : 0 < A)
    (G : Fin (K*A) → Fin (K*A) → Bool) (diag : ∀ i, G i i = true)
    (size : ∑ i : Fin (K*A), rowCount G i ≤ (K*A)*A) :
    K ≤ (boolMatrix G).rank := by
  classical
  obtain ⟨S,_,tri,lower⟩ := greedyRank G diag Finset.univ
  have pos (i : Fin (K*A)) : (0 : ℝ) < rowCount G i := by exact_mod_cast rowCount_pos G diag i
  have den : (0 : ℝ) < ∑ i : Fin (K*A), (rowCount G i : ℝ) := by
    apply Finset.sum_pos (fun i _ => pos i)
    exact ⟨⟨0,Nat.mul_pos hK hA⟩,Finset.mem_univ _⟩
  have cs := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin (K*A)))
    (fun _ => (1 : ℝ)) (g := fun i => (rowCount G i : ℝ)) (fun i _ => pos i)
  have cs' : ((K*A : ℕ) : ℝ)^2 / (∑ i : Fin (K*A), (rowCount G i : ℝ)) ≤
      ∑ i : Fin (K*A), (1 : ℝ) / rowCount G i := by simpa [nsmul_eq_mul] using cs
  have num : (K : ℝ) ≤ ((K*A : ℕ) : ℝ)^2 / (∑ i : Fin (K*A), (rowCount G i : ℝ)) := by
    apply (le_div_iff₀ den).mpr
    have bound : (∑ i : Fin (K*A), (rowCount G i : ℝ)) ≤ (((K*A)*A : ℕ):ℝ) := by exact_mod_cast size
    calc
      _ ≤ (K : ℝ) * (((K*A)*A : ℕ):ℝ) := mul_le_mul_of_nonneg_left bound (by positivity)
      _ = _ := by push_cast; ring
  have sc : K ≤ S.card := by exact_mod_cast num.trans (cs'.trans lower)
  exact sc.trans (independentCardLeRank G S tri)

lemma rankAdd {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (A+B).rank ≤ A.rank+B.rank := by
  let S1 : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range A.mulVecLin
  let S2 : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range B.mulVecLin
  have hrange : LinearMap.range (A+B).mulVecLin ≤ S1 ⊔ S2 := by
    rintro _ ⟨x,rfl⟩
    have hmul : (A+B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by
      simp only [Matrix.mulVecLin_apply,Matrix.add_mulVec]
    rw [hmul]
    exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S1 S2
  have hmono := Submodule.finrank_mono hrange
  change (A+B).rank ≤ Module.finrank (ZMod 2) ↥(S1 ⊔ S2) at hmono
  change Module.finrank (ZMod 2) ↥(S1 ⊔ S2) + Module.finrank (ZMod 2) ↥(S1 ⊓ S2) = A.rank+B.rank at hsup
  omega

lemma anchorRankGap {N : ℕ} (G : Fin N → Fin N → Bool) (u v : Fin N) :
    (boolMatrix G).rank ≤ (anchor u v (fun i j => b2z (G i j))).rank + 2 := by
  let M := boolMatrix G
  let B := anchor u v (fun i j => b2z (G i j))
  let P := Matrix.vecMulVec (fun i => M i v) (fun _ : Fin N => (1 : ZMod 2))
  let Q := Matrix.vecMulVec (fun _ : Fin N => (1 : ZMod 2)) (fun j => M u j + M u v)
  have e : M = B+P+Q := by
    ext i j
    simp only [B,P,Q,anchor,Matrix.add_apply,Matrix.vecMulVec_apply,mul_one,one_mul]
    change M i j = (M i j + M i v + M u j + M u v) + M i v + (M u j + M u v)
    calc
      _ = M i j + (M i v + M i v) + (M u j + M u j) + (M u v + M u v) := by
        rw [zmod2_add_self,zmod2_add_self,zmod2_add_self]
        simp
      _ = _ := by abel
  change M.rank ≤ B.rank+2
  rw [e]
  have two := rankAdd (B+P) Q
  have one := rankAdd B P
  have p : P.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have q : Q.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  omega

end PEqualNP.Outside.L_meta_25723

namespace PEqualNP.Outside.L_meta_25723

open PEqualNP.Outside.L_meta_25723.Base

lemma sparseRankN {N K A : ℕ} (sizeEq : N = K*A) (hK : 0 < K) (hA : 0 < A)
    (G : Fin N → Fin N → Bool) (diag : ∀ i, G i i = true)
    (size : ∑ i : Fin N, rowCount G i ≤ N*A) :
    K ≤ (boolMatrix G).rank := by
  subst N
  exact sparseRank hK hA G diag size

lemma projected_cardN {N K A : ℕ} (sizeEq : N = K*A) (hK : 0 < K) (i : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun j => j.val % K = i.val % K)).card = A := by
  subst N
  exact projected_card K A hK i

end PEqualNP.Outside.L_meta_25723

theorem PEqualNP.Outside.L_meta_25723 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (k a d : ℕ), 0 < k →
  let N := 2^(k+a)
  let b := 2^d
  let groups := min b k
  let value := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : Fin N) =>
    C.eval (PEqualNP.Represents.oneEach i j)
  let size := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin N) =>
    ((Finset.univ : Finset (Fin N)).filter (fun j => value C i j = true)).card
  let admissible := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
    depth (N+N) C ≤ d+1 ∧ (∀ i, value C i i = true) ∧
    (∑ i : Fin N, size C i) ≤ N * 2^a
  let price := fun (t B : ℕ) =>
    (∑ u ∈ Finset.range B, Nat.choose (2*t) (u+1)) +
    (∑ v ∈ Finset.range (B-1), Nat.choose (2*t) (v+1))
  (∀ C, admissible C → 2^k ≤ 2 + price (C.gates.countP nonlinear) b) ∧
  ∃ C, admissible C ∧ (∀ i, size C i = 2^a) ∧
    C.gates.countP nonlinear + 1 ≤ (groups + k % groups) * 2^(k / groups - 1)
) := by
  intro nonlinear depth k a d hk N b groups value size admissible price
  have eqN : N = 2^k * 2^a := pow_add 2 k a
  constructor
  · intro C hC
    let G : Fin N → Fin N → Bool := value C
    have hr : 2^k ≤ (PEqualNP.Outside.L_meta_25723.boolMatrix G).rank :=
      PEqualNP.Outside.L_meta_25723.sparseRankN eqN (by positivity) (by positivity) G hC.2.2.2.1 hC.2.2.2.2
    let z : Fin N := ⟨0,by positivity⟩
    have hgap := PEqualNP.Outside.L_meta_25723.anchorRankGap G z z
    have hbound := PEqualNP.Outside.L_meta_25723.lower_bound_general
      G z z C hC.1 hC.2.1 (fun _ _ => rfl) hC.2.2.1
    change (PEqualNP.Outside.L_meta_25723.Base.anchor z z
      (fun i j => PEqualNP.Outside.L_meta_25723.Base.b2z (G i j))).rank ≤
      price (C.gates.countP nonlinear) b at hbound
    omega
  · obtain ⟨C,hlen,hrb,hrep,hdep,hcost⟩ :=
      PEqualNP.Outside.L_meta_25723.upper_bound_projected k a d hk
    have card (i : Fin N) : size C i = 2^a := by
      change ((Finset.univ : Finset (Fin N)).filter (fun j => value C i j = true)).card = _
      have eq : (Finset.univ : Finset (Fin N)).filter (fun j => value C i j = true) =
          Finset.univ.filter (fun j => j.val % 2^k = i.val % 2^k) := by
        ext j
        change j ∈ Finset.univ.filter (fun t => C.eval (PEqualNP.Represents.oneEach i t) = true) ↔ _
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,hrep i j,decide_eq_true_eq]
        exact eq_comm
      rw [eq]
      exact PEqualNP.Outside.L_meta_25723.projected_cardN eqN (by positivity) i
    refine ⟨C,⟨hlen,hrb,hdep,?_,?_⟩,card,hcost⟩
    · intro i
      simp [value,hrep i i]
    · simp [card]
