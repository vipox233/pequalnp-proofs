import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33653

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

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open Module Submodule Matrix

variable {K : Type} [Field K]

theorem projection_loss {V W : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (s t : Submodule K V) (hs : s ≤ t) :
    finrank K (t.map f) + finrank K s ≤ finrank K t + finrank K (s.map f) := by
  have dim (v : Submodule K V) : finrank K (v.map f) + finrank K (v ⊓ LinearMap.ker f : Submodule K V) = finrank K v := by
    have h := (f.domRestrict v).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq v, Submodule.map_comap_subtype] at h
    exact h
  have hst := Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker f) hs)
  have hs' := dim s
  have ht' := dim t
  omega

def pull {ι ι' : Type} (r : ι' → ι) : (ι → K) →ₗ[K] (ι' → K) where
  toFun x := x ∘ r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def cols {ι κ : Type} (A : Matrix ι κ K) (S : Finset κ) : Submodule K (ι → K) :=
  Submodule.span K (Set.range (fun j : S => A.col j.val))

theorem cols_mono {ι κ : Type} (A : Matrix ι κ K) {S J : Finset κ} (hs : S ⊆ J) :
    cols A S ≤ cols A J := by
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨⟨j,hs j.property⟩,rfl⟩

theorem rank_pull {ι κ ι' : Type} [Fintype ι'] (A : Matrix ι κ K) (r : ι' → ι)
    (S : Finset κ) :
    (A.submatrix r (fun j : S => j.val)).rank = finrank K ((cols A S).map (pull r)) := by
  rw [Matrix.rank_eq_finrank_span_cols, cols, Submodule.map_span, ← Set.range_comp]
  rfl

theorem rank_id_cols {ι κ : Type} [Fintype ι] (A : Matrix ι κ K) (S : Finset κ) :
    (A.submatrix id (fun j : S => j.val)).rank = finrank K (cols A S) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  rfl

set_option maxHeartbeats 900000 in
theorem submatrix_rank_loss {ι κ ι' : Type} [Fintype ι] [Fintype ι']
    (A : Matrix ι κ K) (r : ι' → ι) {S J : Finset κ} (hs : S ⊆ J) :
    (A.submatrix r (fun j : J => j.val)).rank + (A.submatrix id (fun j : S => j.val)).rank ≤
    (A.submatrix id (fun j : J => j.val)).rank + (A.submatrix r (fun j : S => j.val)).rank := by
  have hh := projection_loss (K := K) (V := ι → K) (W := ι' → K) (pull (K := K) r)
    (cols A S) (cols A J) (cols_mono A hs)
  exact (congrArg₂ (fun x y : ℕ => x ≤ y)
    (congrArg₂ Nat.add (rank_pull A r J) (rank_id_cols A S))
    (congrArg₂ Nat.add (rank_id_cols A J) (rank_pull A r S))).mpr
      hh

noncomputable def extend {m : ℕ} (S : Finset (Fin m)) : (S → K) →ₗ[K] (Fin m → K) where
  toFun z j := if h : j ∈ S then z ⟨j,h⟩ else 0
  map_add' x y := by funext j; by_cases h : j ∈ S <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j ∈ S <;> simp [h]

theorem extend_injective {m : ℕ} (S : Finset (Fin m)) :
    Function.Injective (extend (K := K) S) := by
  intro z z' h
  funext j
  simpa [extend, j.property] using congrFun h j.val

theorem mulVec_extend {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m))
    (z : S → K) : G.mulVec (extend S z) = (G.submatrix id (fun j : S => j.val)).mulVec z := by
  classical
  funext x
  change (∑ j : Fin m, G x j * (extend S z) j) = ∑ j : S, G x j.val * z j
  calc
    _ = ∑ j ∈ S, G x j * (extend S z) j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [extend, hj]
    _ = ∑ j : S, G x j.val * z j := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro j _
      simp [extend, j.property]

noncomputable def cutKernel {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m)) :
    Submodule K (Fin m → K) :=
  (LinearMap.ker (G.submatrix id (fun j : S => j.val)).mulVecLin).map (extend S)

theorem mem_cutKernel {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m))
    (z : Fin m → K) :
    z ∈ cutKernel G S ↔ (∀ j ∉ S, z j = 0) ∧ G.mulVec z = 0 := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [extend,hj]
    · rw [mulVec_extend]
      exact hv
  · rintro ⟨hs,hz⟩
    let v : S → K := fun j => z j.val
    have he : extend S v = z := by
      funext j
      by_cases hj : j ∈ S <;> simp [extend, v, hj, hs]
    refine ⟨v, ?_, he⟩
    change (G.submatrix id (fun j : S => j.val)).mulVec v = 0
    rw [← mulVec_extend, he, hz]

theorem dim_cutKernel {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m)) :
    (G.submatrix id (fun j : S => j.val)).rank + finrank K (cutKernel G S) = S.card := by
  let M := (G.submatrix id (fun j : S => j.val)).mulVecLin
  have he := (Submodule.equivMapOfInjective (extend S) (extend_injective S) (LinearMap.ker M)).finrank_eq
  change finrank K (LinearMap.ker M) = finrank K (cutKernel G S) at he
  change finrank K (LinearMap.range M) + finrank K (cutKernel G S) = S.card
  rw [← he, M.finrank_range_add_finrank_ker]
  simp

noncomputable def rankOn {n m : ℕ} (B : Matrix (Fin n) (Fin m) K)
    (I : Finset (Fin n)) (J : Finset (Fin m)) :=
  (B.submatrix (fun i : I => i.val) (fun j : J => j.val)).rank

theorem agree_rank {n m : ℕ} (G T : Matrix (Fin n) (Fin m) K)
    (I : Finset (Fin n)) (J : Finset (Fin m))
    (h : ∀ x ∈ I, ∀ y ∈ J, G x y = T x y) : rankOn G I J = rankOn T I J := by
  apply congrArg Matrix.rank
  ext i j
  exact h i.val i.property j.val j.property

theorem local_necessity {n m r : ℕ} {G T : Matrix (Fin n) (Fin m) K}
    (R I : Finset (Fin n)) (B S : Finset (Fin m)) (hS : S ⊆ B)
    (hR : ∀ x ∈ R, ∀ y, G x y = T x y)
    (hI : ∀ x ∈ I, ∀ y ∈ B, G x y = T x y)
    (hG : G.rank ≤ r) :
    (∀ z ∈ cutKernel G S, (∀ j ∉ S, z j = 0) ∧ ∀ x ∈ I, T.mulVec z x = 0) ∧
    rankOn T R Finset.univ + rankOn T I B + S.card ≤
      r + rankOn T R B + rankOn T I S + finrank K (cutKernel G S) := by
  constructor
  · intro z hz
    obtain ⟨hs,hk⟩ := (mem_cutKernel G S z).mp hz
    refine ⟨hs, fun x hx => ?_⟩
    calc
      T.mulVec z x = G.mulVec z x := by
        change (∑ j, T x j * z j) = ∑ j, G x j * z j
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ S
        · rw [hI x hx j (hS hj)]
        · simp [hs j hj]
      _ = 0 := congrFun hk x
  · have h₁ := submatrix_rank_loss G (fun i : R => i.val) (Finset.subset_univ B)
    have h₂ := submatrix_rank_loss G (fun i : I => i.val) hS
    have h₃ := dim_cutKernel G S
    have big := G.rank_submatrix_le id (fun j : (Finset.univ : Finset (Fin m)) => j.val)
    have hrj := agree_rank G T R Finset.univ (fun x hx y _ => hR x hx y)
    have hrb := agree_rank G T R B (fun x hx y _ => hR x hx y)
    have hib := agree_rank G T I B hI
    have his := agree_rank G T I S (fun x hx y hy => hI x hx y (hS hy))
    dsimp only [rankOn] at hrj hrb hib his ⊢
    omega

theorem necessity : (∀ (K : Type) [Field K] (n m a r : ℕ) (T : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m)),
  (∀ i j k : Fin a, i ≤ j → j ≤ k → bags i.val ∩ bags k.val ⊆ bags j.val) →
  let cut := fun j : ℕ => if 0 < j ∧ j < a then bags (j-1) ∩ bags j else ∅
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let rk := fun (B : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let X := Fin m → K
  let State := Submodule K X
  let supported := fun (S : Finset (Fin m)) (z : X) => ∀ y ∉ S, z y = 0
  let agrees := fun (i : Fin a) (U V : State) =>
    ∀ z : X, supported (cut i.val ∩ cut (i.val+1)) z → (z ∈ U ↔ z ∈ V)
  let fits := fun (B : Matrix (Fin n) (Fin m) K) (i : Fin a) (j : ℕ) (U : State) =>
    (∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, B.mulVec z x = 0) ∧
    rk T R Finset.univ + rk B (rows i) (bags i.val) + (cut j).card ≤
      r + rk T R (bags i.val) + rk B (rows i) (cut j) + Module.finrank K U
  ((∃ G : Matrix (Fin n) (Fin m) K, Matrix.rank G ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ y ∈ bags i.val) → G x y = T x y) →
    rk T R Finset.univ ≤ r ∧ ∃ N : ℕ → State, ∀ i : Fin a,
      agrees i (N i.val) (N (i.val+1)) ∧
      fits T i i.val (N i.val) ∧ fits T i (i.val+1) (N (i.val+1)))) := by
  intro K k n m a r T row bags _interval cut R rows rk X State supported agrees fits
  rintro ⟨G,hgr,observed⟩
  have hr (x : Fin n) (hx : x ∈ R) (y : Fin m) : G x y = T x y :=
    observed x y (Or.inl (Finset.mem_filter.mp hx).2)
  have hi (i : Fin a) (x : Fin n) (hx : x ∈ rows i) (y : Fin m)
      (hy : y ∈ bags i.val) : G x y = T x y := by
    rcases Finset.mem_union.mp hx with h | h
    · exact hr x h y
    · exact observed x y (Or.inr ⟨i,(Finset.mem_filter.mp h).2,hy⟩)
  have left (i : Fin a) : cut i.val ⊆ bags i.val := by
    dsimp only [cut]
    split
    · exact Finset.inter_subset_right
    · exact Finset.empty_subset _
  have right (i : Fin a) : cut (i.val+1) ⊆ bags i.val := by
    dsimp only [cut]
    split
    · simp
    · exact Finset.empty_subset _
  refine ⟨?_, fun j => cutKernel G (cut j), fun i => ⟨?_,?_,?_⟩⟩
  · change rankOn T R Finset.univ ≤ r
    rw [← agree_rank G T R Finset.univ (fun x hx y _ => hr x hx y)]
    exact (G.rank_submatrix_le _ _).trans hgr
  · intro z hz
    rw [mem_cutKernel, mem_cutKernel]
    have hleft : ∀ j ∉ cut i.val, z j = 0 := fun j hj =>
      hz j (fun hm => hj (Finset.mem_inter.mp hm).1)
    have hright : ∀ j ∉ cut (i.val+1), z j = 0 := fun j hj =>
      hz j (fun hm => hj (Finset.mem_inter.mp hm).2)
    exact ⟨fun h => ⟨hright,h.2⟩, fun h => ⟨hleft,h.2⟩⟩
  · exact local_necessity R (rows i) (bags i.val) (cut i.val) (left i) hr (hi i) hgr
  · exact local_necessity R (rows i) (bags i.val) (cut (i.val+1)) (right i) hr (hi i) hgr

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem exists_outside_two (A B : Submodule K V) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    ∃ x : V, x ∉ A ∧ x ∉ B := by
  obtain ⟨a,ha⟩ := SetLike.exists_notMem_of_ne_top A hA rfl
  obtain ⟨b,hb⟩ := SetLike.exists_notMem_of_ne_top B hB rfl
  by_cases hab : a ∈ B
  · by_cases hba : b ∈ A
    · refine ⟨a+b, fun hm => ha ?_, fun hm => hb ?_⟩
      · simpa using A.sub_mem hm hba
      · simpa using B.sub_mem hm hab
    · exact ⟨b,hba,hb⟩
  · exact ⟨a,ha,hab⟩

theorem common_kernel [FiniteDimensional K V] (S T : Submodule K V) (s : ℕ)
    (hs : finrank K S ≤ s) (ht : finrank K T ≤ s) :
    ∃ W : Submodule K V, Disjoint W S ∧ Disjoint W T ∧ finrank K (V ⧸ W) ≤ s := by
  classical
  let good (d : ℕ) := ∃ W : Submodule K V, Disjoint W S ∧ Disjoint W T ∧ finrank K W = d
  have hz : good 0 := ⟨⊥, disjoint_bot_left, disjoint_bot_left, by simp⟩
  obtain ⟨W,hWS,hWT,hmax⟩ := Nat.findGreatest_spec (P:=good) (Nat.zero_le (finrank K V)) hz
  refine ⟨W,hWS,hWT,?_⟩
  by_contra hi
  have dimW := W.finrank_quotient_add_finrank
  have proper (U : Submodule K V) (hu : finrank K U ≤ s) : W ⊔ U ≠ ⊤ := by
    intro he
    have hdu := Submodule.finrank_sup_add_finrank_inf_eq W U
    rw [he] at hdu
    simp only [finrank_top] at hdu
    omega
  obtain ⟨x,hxS,hxT⟩ := exists_outside_two (W ⊔ S) (W ⊔ T) (proper S hs) (proper T ht)
  let L := Submodule.span K {x}
  have hL (U : Submodule K V) (hu : x ∉ W ⊔ U) (hw : Disjoint W U) : Disjoint (L ⊔ W) U :=
    hw.disjoint_sup_left_of_disjoint_sup_right (Submodule.disjoint_span_singleton_of_notMem hu).symm
  have hlt : W < L ⊔ W := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro he
    have hx : x ∈ L ⊔ W := (show L ≤ L ⊔ W from le_sup_left) (Submodule.subset_span (by simp))
    have hxw : x ∈ W := he.symm ▸ hx
    exact hxS ((show W ≤ W ⊔ S from le_sup_left) hxw)
  have larger := Submodule.finrank_lt_finrank_of_lt hlt
  have admissible : good (finrank K (L ⊔ W : Submodule K V)) :=
    ⟨L ⊔ W, hL S hxS hWS, hL T hxT hWT, rfl⟩
  have bound := Nat.le_findGreatest (P:=good) (Submodule.finrank_le (L ⊔ W : Submodule K V)) admissible
  omega

def pad (d s : ℕ) : (Fin d → K) →ₗ[K] (Fin s → K) where
  toFun x j := if h : j.val < d then x ⟨j.val,h⟩ else 0
  map_add' x y := by funext j; by_cases h : j.val < d <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j.val < d <;> simp [h]

theorem pad_injective {d s : ℕ} (h : d ≤ s) : Function.Injective (pad (K := K) d s) := by
  intro x y he
  funext j
  simpa [pad,j.isLt] using congrFun he (⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ : Fin s)

theorem common_map [FiniteDimensional K V] (S T : Submodule K V) (s : ℕ)
    (hs : finrank K S ≤ s) (ht : finrank K T ≤ s) :
    ∃ f : V →ₗ[K] (Fin s → K),
      Function.Injective (f.domRestrict S) ∧ Function.Injective (f.domRestrict T) := by
  obtain ⟨W,hS,hT,hw⟩ := common_kernel S T s hs ht
  let b := (Module.finBasis K (V ⧸ W)).equivFun
  let e := (pad (K := K) (finrank K (V ⧸ W)) s).comp b.toLinearMap
  have he : Function.Injective e := (pad_injective hw).comp b.injective
  have inj (U : Submodule K V) (hd : Disjoint W U) :
      Function.Injective (W.mkQ.domRestrict U) := by
    apply LinearMap.injective_domRestrict_iff.mpr
    simpa only [Submodule.ker_mkQ] using hd.symm
  exact ⟨e.comp W.mkQ, he.comp (inj S hS), he.comp (inj T hT)⟩

theorem enlarge_kernels [FiniteDimensional K V]
    (L R P Q : Submodule K V) (s : ℕ) (hP : P ≤ L) (hQ : Q ≤ R)
    (hagree : P ⊓ R = Q ⊓ L)
    (hL : finrank K L ≤ s + finrank K P) (hR : finrank K R ≤ s + finrank K Q) :
    ∃ W : Submodule K V, W ⊓ L = P ∧ W ⊓ R = Q ∧ finrank K (V ⧸ W) ≤ s := by
  let A := P ⊔ Q
  have hl : A ⊓ L = P := by
    change (P ⊔ Q) ⊓ L = P
    rw [sup_inf_assoc_of_le Q hP, ← hagree, sup_inf_self]
  have hr : A ⊓ R = Q := by
    change (P ⊔ Q) ⊓ R = Q
    rw [sup_comm, sup_inf_assoc_of_le P hQ, hagree, sup_inf_self]
  have dim (Y : Submodule K V) :
      finrank K (Y.map A.mkQ) + finrank K (A ⊓ Y : Submodule K V) = finrank K Y := by
    have hd := (A.mkQ.domRestrict Y).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
      ← Submodule.finrank_map_subtype_eq Y, Submodule.map_comap_subtype, inf_comm Y A] at hd
    exact hd
  have sl := dim L
  have sr := dim R
  rw [hl] at sl
  rw [hr] at sr
  obtain ⟨f,fl,fr⟩ := common_map (L.map A.mkQ) (R.map A.mkQ) s (by omega) (by omega)
  let F := f.comp A.mkQ
  have exactOn (Y : Submodule K V) (inj : Function.Injective (f.domRestrict (Y.map A.mkQ))) :
      LinearMap.ker F ⊓ Y = A ⊓ Y := by
    ext x
    constructor
    · rintro ⟨hk,hy⟩
      have hx : A.mkQ x ∈ Y.map A.mkQ := ⟨x,hy,rfl⟩
      have hh : (⟨A.mkQ x,hx⟩ : Y.map A.mkQ) = 0 := by
        apply inj
        change f (A.mkQ x) = f 0
        rw [map_zero]
        exact hk
      have hz : A.mkQ x = 0 := congrArg Subtype.val hh
      refine ⟨?_,hy⟩
      rw [← Submodule.ker_mkQ A]
      exact hz
    · rintro ⟨ha,hy⟩
      refine ⟨?_,hy⟩
      have hz : A.mkQ x = 0 := by
        change x ∈ LinearMap.ker A.mkQ
        rwa [Submodule.ker_mkQ]
      change f (A.mkQ x) = 0
      rw [hz,map_zero]
  refine ⟨LinearMap.ker F, (exactOn L fl).trans hl, (exactOn R fr).trans hr, ?_⟩
  rw [F.quotKerEquivRange.finrank_eq]
  simpa using (Submodule.finrank_le (LinearMap.range F))

theorem panel_kernel [FiniteDimensional K V] {Y : Type} [AddCommGroup Y] [Module K Y]
    (F : V →ₗ[K] Y) (L R P Q : Submodule K V) (budget : ℕ)
    (hP : P ≤ L) (hQ : Q ≤ R) (hp : P ≤ LinearMap.ker F) (hq : Q ≤ LinearMap.ker F)
    (hagree : P ⊓ R = Q ⊓ L)
    (hL : finrank K (LinearMap.range F) + finrank K L ≤
      budget + finrank K (L.map F) + finrank K P)
    (hR : finrank K (LinearMap.range F) + finrank K R ≤
      budget + finrank K (R.map F) + finrank K Q) :
    ∃ W : Submodule K V, W ≤ LinearMap.ker F ∧ W ⊓ L = P ∧ W ⊓ R = Q ∧
      finrank K (V ⧸ W) ≤ budget := by
  let A := LinearMap.ker F
  let lift := fun (U : Submodule K V) => U.comap A.subtype
  have dim_small (U : Submodule K V) (hu : U ≤ A) : finrank K (lift U) = finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq A (lift U)]
    change finrank K ((U.comap A.subtype).map A.subtype) = _
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hu]
  have dim_restrict (U : Submodule K V) : finrank K (U.map F) + finrank K (lift U) = finrank K U := by
    have hd := (F.domRestrict U).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype] at hd
    rw [← Submodule.finrank_map_subtype_eq A (lift U)]
    change finrank K (U.map F) + finrank K ((U.comap A.subtype).map A.subtype) = finrank K U
    rw [Submodule.map_comap_subtype, inf_comm A U]
    exact hd
  have pl : lift P ≤ lift L := Submodule.comap_mono hP
  have qr : lift Q ≤ lift R := Submodule.comap_mono hQ
  have ag : lift P ⊓ lift R = lift Q ⊓ lift L := by
    change (P ⊓ R).comap A.subtype = (Q ⊓ L).comap A.subtype
    rw [hagree]
  have dl := dim_restrict L
  have dr := dim_restrict R
  have dp := dim_small P hp
  have dq := dim_small Q hq
  have lp := Submodule.finrank_mono pl
  let s := budget - finrank K (LinearMap.range F)
  obtain ⟨B,bl,br,bc⟩ := enlarge_kernels (lift L) (lift R) (lift P) (lift Q) s pl qr ag
    (by dsimp [s]; omega) (by dsimp [s]; omega)
  have exactOn (U N : Submodule K V) (hh : B ⊓ lift U = lift N) (hn : N ≤ A) :
      B.map A.subtype ⊓ U = N := by
    rw [Submodule.map_inf_eq_map_inf_comap]
    change (B ⊓ lift U).map A.subtype = N
    rw [hh]
    change (N.comap A.subtype).map A.subtype = N
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hn]
  refine ⟨B.map A.subtype, ?_, exactOn L P bl hp, exactOn R Q br hq, ?_⟩
  · rintro _ ⟨v,_,rfl⟩
    exact v.property
  · have e₁ := (B.map A.subtype).finrank_quotient_add_finrank
    have e₂ := B.finrank_quotient_add_finrank
    have e₃ := F.finrank_range_add_finrank_ker
    rw [Submodule.finrank_map_subtype_eq] at e₁
    change finrank K (LinearMap.range F) + finrank K A = finrank K V at e₃
    dsimp only [s] at bc
    omega

theorem encode_kernel [FiniteDimensional K V] {Y : Type} [AddCommGroup Y] [Module K Y]
    (c : V →ₗ[K] Y) (W : Submodule K V) (hw : W ≤ LinearMap.ker c) (s : ℕ)
    (hs : finrank K (V ⧸ W) ≤ finrank K (LinearMap.range c) + s) :
    ∃ f : V →ₗ[K] (Fin s → K), LinearMap.ker (c.prod f) = W := by
  let b := W.liftQ c hw
  let L := LinearMap.ker b
  have hb : LinearMap.range b = LinearMap.range c := Submodule.range_liftQ W c hw
  have hd := b.finrank_range_add_finrank_ker
  rw [hb] at hd
  have hL : finrank K L ≤ s := by dsimp only [L]; omega
  let coord := (Module.finBasis K L).equivFun
  let e := (pad (K := K) (finrank K L) s).comp coord.toLinearMap
  have he : Function.Injective e := (pad_injective hL).comp coord.injective
  obtain ⟨J,hJ⟩ := L.exists_isCompl
  let π := L.projectionOnto J hJ
  let f := e.comp (π.comp W.mkQ)
  refine ⟨f, ?_⟩
  ext x
  change (c x, f x) = (0,0) ↔ x ∈ W
  constructor
  · intro h
    have hc : c x = 0 := congrArg Prod.fst h
    have hf : f x = 0 := congrArg Prod.snd h
    have hx : W.mkQ x ∈ L := hc
    let y : L := ⟨W.mkQ x,hx⟩
    have hp : π (W.mkQ x) = y := L.projectionOnto_apply_left hJ y
    have hy : y = 0 := by
      apply he
      rw [← hp, map_zero]
      exact hf
    rw [← W.ker_mkQ]
    exact congrArg Subtype.val hy
  · intro hx
    have hc : c x = 0 := hw hx
    have hz : W.mkQ x = 0 := by
      change x ∈ LinearMap.ker W.mkQ
      rwa [Submodule.ker_mkQ]
    have hf : f x = 0 := by change e (π (W.mkQ x)) = 0; rw [hz,map_zero,map_zero]
    rw [hc,hf]

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open Module Submodule
variable {K D A B : Type} [Field K] [AddCommGroup D] [Module K D]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem factor_on_image (f : D →ₗ[K] A) (g : D →ₗ[K] B)
    (hk : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ e : A →ₗ[K] B, ∀ x, e (f x) = g x := by
  obtain ⟨P,hP⟩ := (LinearMap.range f).exists_isCompl
  let π := (LinearMap.range f).projectionOnto P hP
  let onQuot := (LinearMap.ker f).liftQ g hk
  let e := (onQuot.comp f.quotKerEquivRange.symm.toLinearMap).comp π
  refine ⟨e,fun x => ?_⟩
  have hπ : π (f x) = f.rangeRestrict x := (LinearMap.range f).projectionOnto_apply_left hP (f.rangeRestrict x)
  have hf : f.quotKerEquivRange (Submodule.Quotient.mk x) = f.rangeRestrict x := rfl
  change onQuot (f.quotKerEquivRange.symm (π (f x))) = g x
  rw [hπ, ← hf, LinearEquiv.symm_apply_apply]
  rfl

theorem same_kernel_alignment [FiniteDimensional K B] (p q : D →ₗ[K] B)
    (hk : LinearMap.ker p = LinearMap.ker q) :
    ∃ e : B ≃ₗ[K] B, ∀ x, e (p x) = q x := by
  let i := Submodule.quotEquivOfEq _ _ hk
  let h := p.quotKerEquivRange.symm.trans (i.trans q.quotKerEquivRange)
  obtain ⟨e,he⟩ := Submodule.exists_linearEquiv_restrict_eq h
  refine ⟨e, fun x => ?_⟩
  have h₁ : p.quotKerEquivRange (Submodule.Quotient.mk x) = p.rangeRestrict x := rfl
  have h₂ : (h (p.rangeRestrict x) : B) = q x := by
    change (q.quotKerEquivRange (i (p.quotKerEquivRange.symm (p.rangeRestrict x))) : B) = q x
    rw [← h₁, LinearEquiv.symm_apply_apply]
    rfl
  exact (he (p.rangeRestrict x)).symm.trans h₂

theorem align_overlap [FiniteDimensional K B] (c : D →ₗ[K] A) (p q : D →ₗ[K] B)
    (hk : LinearMap.ker (c.prod p) = LinearMap.ker (c.prod q)) :
    ∃ (e : B ≃ₗ[K] B) (t : A →ₗ[K] B), ∀ x, e (p x) + t (c x) = q x := by
  let H := LinearMap.ker c
  have hloc : LinearMap.ker (p.domRestrict H) = LinearMap.ker (q.domRestrict H) := by
    ext y
    have hy : c y.val = 0 := y.property
    have hy' : y.val ∈ LinearMap.ker (c.prod p) ↔ y.val ∈ LinearMap.ker (c.prod q) := by rw [hk]
    change p y.val = 0 ↔ q y.val = 0
    change (c y.val,p y.val) = (0,0) ↔ (c y.val,q y.val) = (0,0) at hy'
    simpa [hy] using hy'
  obtain ⟨e,he⟩ := same_kernel_alignment (p.domRestrict H) (q.domRestrict H) hloc
  let δ := q - e.toLinearMap.comp p
  have hd : LinearMap.ker c ≤ LinearMap.ker δ := by
    intro x hx
    change q x - e (p x) = 0
    exact sub_eq_zero.mpr (he ⟨x,hx⟩).symm
  obtain ⟨t,ht⟩ := factor_on_image c δ hd
  refine ⟨e,t, fun x => ?_⟩
  rw [ht]
  change e (p x) + (q x - e (p x)) = q x
  abel

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open Module Submodule Matrix
variable {K : Type} [Field K] {n m : ℕ}

noncomputable def coord (K : Type) [Field K] {m : ℕ} (S : Finset (Fin m)) : Submodule K (Fin m → K) :=
  LinearMap.range (extend S)

theorem coord_mem (S : Finset (Fin m)) (z : Fin m → K) :
    z ∈ coord K S ↔ ∀ j ∉ S, z j = 0 := by
  constructor
  · rintro ⟨v,rfl⟩ j hj
    simp [extend,hj]
  · intro h
    refine ⟨fun j => z j.val, ?_⟩
    funext j
    by_cases hj : j ∈ S <;> simp [extend,hj,h]

theorem coord_mono {S B : Finset (Fin m)} (h : S ⊆ B) : coord K S ≤ coord K B := by
  intro z hz
  rw [coord_mem] at hz ⊢
  exact fun j hj => hz j (fun h' => hj (h h'))

theorem coord_dim (S : Finset (Fin m)) : finrank K (coord K S) = S.card := by
  have h : finrank K (coord K S) = finrank K (S → K) :=
    (LinearEquiv.ofInjective (extend (K := K) S) (extend_injective (K := K) S)).finrank_eq.symm
  exact h.trans (by simp)

theorem coord_all : coord K (Finset.univ : Finset (Fin m)) = ⊤ := by
  apply top_unique
  intro z _
  rw [coord_mem]
  simp

noncomputable def rowMap (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) :
    (Fin m → K) →ₗ[K] (I → K) := (T.submatrix (fun x : I => x.val) id).mulVecLin

theorem rowMap_apply (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (z : Fin m → K)
    (x : I) : rowMap T I z x = T.mulVec z x.val := rfl

theorem rank_image (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (S : Finset (Fin m)) :
    finrank K ((coord K S).map (rowMap T I)) = rankOn T I S := by
  have hf : (rowMap T I).comp (extend S) =
      (T.submatrix (fun x : I => x.val) (fun j : S => j.val)).mulVecLin := by
    apply LinearMap.ext
    intro z
    funext j
    exact congrFun (mulVec_extend T S z) j.val
  change finrank K ((LinearMap.range (extend S)).map (rowMap T I)) = _
  rw [← LinearMap.range_comp, hf]
  rfl

theorem rank_common (T : Matrix (Fin n) (Fin m) K) (R : Finset (Fin n)) :
    finrank K (LinearMap.range (rowMap T R)) = rankOn T R Finset.univ := by
  have h := rank_image T R Finset.univ
  rwa [coord_all, Submodule.map_top] at h

theorem visible_rank (T : Matrix (Fin n) (Fin m) K) (R : Finset (Fin n)) (B : Finset (Fin m)) :
    finrank K (LinearMap.range ((rowMap T R).rangeRestrict.domRestrict (coord K B))) = rankOn T R B := by
  let f := rowMap T R
  rw [LinearMap.range_domRestrict]
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.range f)]
  rw [← Submodule.map_comp]
  exact rank_image T R B

theorem observed_annihilation (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (z : Fin m → K) :
    rowMap T I z = 0 ↔ ∀ x ∈ I, T.mulVec z x = 0 := by
  constructor
  · intro h x hx
    exact congrFun h ⟨x,hx⟩
  · intro h
    funext x
    exact h x.val x.property

end PEqualNP.Outside.L_meta_33653
namespace PEqualNP.Outside.L_meta_33653

open Module Submodule Matrix
variable {K : Type} [Field K] {n m : ℕ}

theorem local_panel_data (T : Matrix (Fin n) (Fin m) K)
    (R I : Finset (Fin n)) (B Sl Sr : Finset (Fin m)) (P Q : Submodule K (Fin m → K)) (r : ℕ)
    (ri : R ⊆ I) (lb : Sl ⊆ B) (rb : Sr ⊆ B) (budget : rankOn T R Finset.univ ≤ r)
    (agree : ∀ z : Fin m → K, (∀ j ∉ Sl ∩ Sr, z j = 0) → (z ∈ P ↔ z ∈ Q))
    (hp : ∀ z ∈ P, (∀ j ∉ Sl, z j = 0) ∧ ∀ x ∈ I, T.mulVec z x = 0)
    (hq : ∀ z ∈ Q, (∀ j ∉ Sr, z j = 0) ∧ ∀ x ∈ I, T.mulVec z x = 0)
    (dimL : rankOn T R Finset.univ + rankOn T I B + Sl.card ≤
      r + rankOn T R B + rankOn T I Sl + finrank K P)
    (dimR : rankOn T R Finset.univ + rankOn T I B + Sr.card ≤
      r + rankOn T R B + rankOn T I Sr + finrank K Q) :
    ∃ h : (Fin m → K) →ₗ[K] (Fin (r - rankOn T R Finset.univ) → K),
      (∀ z : Fin m → K, (∀ j ∉ Sl, z j = 0) →
        (((rowMap T R).rangeRestrict.prod h) z = 0 ↔ z ∈ P)) ∧
      (∀ z : Fin m → K, (∀ j ∉ Sr, z j = 0) →
        (((rowMap T R).rangeRestrict.prod h) z = 0 ↔ z ∈ Q)) ∧
      (∀ z : Fin m → K, (∀ j ∉ B, z j = 0) →
        ((rowMap T R).rangeRestrict.prod h) z = 0 → ∀ x ∈ I, T.mulVec z x = 0) := by
  let Bag := coord K B
  let lift := fun (U : Submodule K (Fin m → K)) => U.comap Bag.subtype
  let cl := coord K Sl
  let cr := coord K Sr
  let F := (rowMap T I).domRestrict Bag
  let c := (rowMap T R).rangeRestrict
  let d := rankOn T R Finset.univ
  let s := r - d
  have pcl : P ≤ cl := fun z hz => (coord_mem Sl z).mpr (hp z hz).1
  have qcr : Q ≤ cr := fun z hz => (coord_mem Sr z).mpr (hq z hz).1
  have cbl : cl ≤ Bag := coord_mono lb
  have cbr : cr ≤ Bag := coord_mono rb
  have ints (z : Fin m → K) (l : z ∈ cl) (rr : z ∈ cr) : ∀ j ∉ Sl ∩ Sr, z j = 0 := by
    intro j hj
    by_cases hl : j ∈ Sl
    · exact (coord_mem Sr z).mp rr j (fun hr => hj (Finset.mem_inter.mpr ⟨hl,hr⟩))
    · exact (coord_mem Sl z).mp l j hl
  have agreement : P ⊓ cr = Q ⊓ cl := by
    ext z
    constructor
    · rintro ⟨p,rr⟩
      exact ⟨(agree z (ints z (pcl p) rr)).mp p,pcl p⟩
    · rintro ⟨q,l⟩
      exact ⟨(agree z (ints z l (qcr q))).mpr q,qcr q⟩
  have dimLift (U : Submodule K (Fin m → K)) (hu : U ≤ Bag) : finrank K (lift U) = finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq Bag (lift U)]
    change finrank K ((U.comap Bag.subtype).map Bag.subtype) = _
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hu]
  have image (U : Submodule K (Fin m → K)) (hu : U ≤ Bag) :
      (lift U).map F = U.map (rowMap T I) := by
    change (lift U).map ((rowMap T I).comp Bag.subtype) = _
    rw [Submodule.map_comp]
    change ((U.comap Bag.subtype).map Bag.subtype).map (rowMap T I) = _
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hu]
  have rangeF : finrank K (LinearMap.range F) = rankOn T I B := by
    rw [show LinearMap.range F = Bag.map (rowMap T I) from LinearMap.range_domRestrict ..]
    exact rank_image T I B
  have cutDim (S : Finset (Fin m)) (hS : coord K S ≤ Bag) :
      finrank K (lift (coord K S)) = S.card ∧
      finrank K ((lift (coord K S)).map F) = rankOn T I S :=
    ⟨(dimLift _ hS).trans (coord_dim S), by rw [image _ hS]; exact rank_image T I S⟩
  obtain ⟨dcl,irl⟩ := cutDim Sl cbl
  obtain ⟨dcr,irr⟩ := cutDim Sr cbr
  have dp := dimLift P (pcl.trans cbl)
  have dq := dimLift Q (qcr.trans cbr)
  have ap : lift P ≤ LinearMap.ker F := by
    intro z hz
    exact (observed_annihilation T I z).mpr (hp z.val hz).2
  have aq : lift Q ≤ LinearMap.ker F := by
    intro z hz
    exact (observed_annihilation T I z).mpr (hq z.val hz).2
  have ag : lift P ⊓ lift cr = lift Q ⊓ lift cl := by
    change (P ⊓ cr).comap Bag.subtype = (Q ⊓ cl).comap Bag.subtype
    rw [agreement]
  obtain ⟨W,wf,wl,wr,wd⟩ := panel_kernel F (lift cl) (lift cr) (lift P) (lift Q)
    (rankOn T R B + s) (Submodule.comap_mono pcl) (Submodule.comap_mono qcr) ap aq ag
    (by rw [rangeF,dp,show finrank K (lift cl) = Sl.card from dcl,show finrank K ((lift cl).map F) = rankOn T I Sl from irl]; dsimp [s,d]; omega)
    (by rw [rangeF,dq,show finrank K (lift cr) = Sr.card from dcr,show finrank K ((lift cr).map F) = rankOn T I Sr from irr]; dsimp [s,d]; omega)
  have wc : W ≤ LinearMap.ker (c.domRestrict Bag) := by
    intro z hz
    have ff : rowMap T I z.val = 0 := wf hz
    change (rowMap T R).rangeRestrict z.val = 0
    apply Subtype.ext
    funext j
    exact congrFun ff (⟨j.val,ri j.property⟩ : I)
  obtain ⟨v,hv⟩ := encode_kernel (c.domRestrict Bag) W wc s (by
    rw [show finrank K (LinearMap.range (c.domRestrict Bag)) = rankOn T R B from visible_rank T R B]
    exact wd)
  obtain ⟨J,hJ⟩ := Bag.exists_isCompl
  let π := Bag.projectionOnto J hJ
  let h := v.comp π
  have localEq (z : Bag) : (c.prod h) z.val = 0 ↔ z ∈ W := by
    change (c z.val, v (π z.val)) = 0 ↔ _
    rw [show π z.val = z from Bag.projectionOnto_apply_left hJ z]
    change z ∈ LinearMap.ker ((c.domRestrict Bag).prod v) ↔ z ∈ W
    rw [hv]
  have atCut (U N : Submodule K (Fin m → K)) (ub : U ≤ Bag) (wu : W ⊓ lift U = lift N)
      (z : Fin m → K) (zu : z ∈ U) : (c.prod h) z = 0 ↔ z ∈ N := by
    let zz : Bag := ⟨z,ub zu⟩
    constructor
    · intro hh
      have hm : zz ∈ W ⊓ lift U := ⟨(localEq zz).mp hh,zu⟩
      rw [wu] at hm
      exact hm
    · intro hn
      have hm : zz ∈ W ⊓ lift U := wu.symm ▸ (show zz ∈ lift N from hn)
      exact (localEq zz).mpr hm.1
  refine ⟨h, fun z hz => atCut cl P cbl wl z ((coord_mem Sl z).mpr hz),
    fun z hz => atCut cr Q cbr wr z ((coord_mem Sr z).mpr hz), ?_⟩
  intro z hz hh
  let zz : Bag := ⟨z,(coord_mem B z).mpr hz⟩
  exact (observed_annihilation T I z).mp (wf ((localEq zz).mp hh))

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open Module Submodule
variable {K A H : Type} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup H] [Module K H]

def bagSpace {m : ℕ} (S : Finset (Fin m)) : Submodule K (Fin m → K) :=
  { add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
    carrier := {z | ∀ y ∉ S, z y = 0}
    zero_mem' := by simp
    smul_mem' := by intro c x hx j hj; simp [hx j hj] }

theorem interval_overlap_subset {J : Type} [DecidableEq J] {a : ℕ}
    (bags : ℕ → Finset J)
    (interval : ∀ i j k : ℕ, i ≤ j → j ≤ k → k < a →
      bags i ∩ bags k ⊆ bags j)
    {i n : ℕ} (hin : i < n) (hna : n < a) :
    bags i ∩ bags n ⊆ bags (n-1) ∩ bags n := by
  intro x hx
  exact Finset.mem_inter.mpr
    ⟨interval i (n-1) n (by omega) (by omega) hna hx, (Finset.mem_inter.mp hx).2⟩

theorem linear_eq_on_bag {m : ℕ} (S : Finset (Fin m))
    (f g : (Fin m → K) →ₗ[K] H)
    (cols : ∀ j ∈ S, f (Pi.basisFun K (Fin m) j) = g (Pi.basisFun K (Fin m) j))
    (z : Fin m → K) (hz : ∀ j ∉ S, z j = 0) : f z = g z := by
  classical
  have expansion : z = ∑ j, z j • Pi.basisFun K (Fin m) j := by
    simpa using ((Pi.basisFun K (Fin m)).sum_repr z).symm
  rw [expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · rw [cols j hj]
  · simp [hz j hj]

theorem basis_in_bag {m : ℕ} {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) :
    Pi.basisFun K (Fin m) j ∈ bagSpace (K := K) S := by
  intro y hy
  have hne : y ≠ j := by intro h; exact hy (h ▸ hj)
  simp [Pi.basisFun_apply, hne]

theorem shear_kernel {m : ℕ} (c : (Fin m → K) →ₗ[K] A)
    (p : (Fin m → K) →ₗ[K] H) (e : H ≃ₗ[K] H) (t : A →ₗ[K] H)
    (z : Fin m → K) :
    (c.prod (e.toLinearMap.comp p + t.comp c)) z = 0 ↔ (c.prod p) z = 0 := by
  change (c z, e (p z) + t (c z)) = (0,0) ↔ (c z,p z) = (0,0)
  rw [Prod.mk.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨hc,hp⟩
    refine ⟨hc, e.injective ?_⟩
    simpa [hc] using hp
  · rintro ⟨hc,hp⟩
    simp [hc,hp]

theorem glue_interval_maps [FiniteDimensional K H] (a m : ℕ)
    (bags : ℕ → Finset (Fin m))
    (interval : ∀ i j k : ℕ, i ≤ j → j ≤ k → k < a →
      bags i ∩ bags k ⊆ bags j)
    (c : (Fin m → K) →ₗ[K] A) (hs : ℕ → (Fin m → K) →ₗ[K] H)
    (agree : ∀ i : ℕ, i+1 < a → ∀ z : Fin m → K,
      (∀ y ∉ bags i ∩ bags (i+1), z y = 0) →
      ((c.prod (hs i)) z = 0 ↔ (c.prod (hs (i+1))) z = 0)) :
    ∃ h : (Fin m → K) →ₗ[K] H, ∀ i : ℕ, i < a → ∀ z : Fin m → K,
      (∀ y ∉ bags i, z y = 0) →
      ((c.prod h) z = 0 ↔ (c.prod (hs i)) z = 0) := by
  classical
  have build : ∀ n : ℕ, n ≤ a → ∃ h : (Fin m → K) →ₗ[K] H,
      ∀ i : ℕ, i < n → ∀ z : Fin m → K,
      (∀ y ∉ bags i, z y = 0) →
      ((c.prod h) z = 0 ↔ (c.prod (hs i)) z = 0) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨0, fun i hi => False.elim (by omega)⟩
    | succ n ih =>
      intro hn
      by_cases nz : n = 0
      · subst n
        refine ⟨hs 0, ?_⟩
        intro i hi z _
        have hiz : i = 0 := by omega
        subst i
        rfl
      obtain ⟨old, hold⟩ := ih (by omega)
      let S := bags (n-1) ∩ bags n
      let U := bagSpace (K := K) S
      have hker : LinearMap.ker ((c.domRestrict U).prod ((hs n).domRestrict U)) =
          LinearMap.ker ((c.domRestrict U).prod (old.domRestrict U)) := by
        ext z
        change (c.prod (hs n)) z.val = 0 ↔ (c.prod old) z.val = 0
        have zS : ∀ y ∉ S, z.val y = 0 := z.property
        have zprev : ∀ y ∉ bags (n-1), z.val y = 0 := by
          intro y hy
          exact zS y (fun h => hy (Finset.mem_inter.mp h).1)
        have ha := agree (n-1) (by omega) z.val (by simpa [S, Nat.sub_add_cancel (by omega : 1 ≤ n)] using zS)
        have hb := hold (n-1) (by omega) z.val zprev
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using ha.symm.trans hb.symm
      obtain ⟨e,t,he⟩ := align_overlap (c.domRestrict U) ((hs n).domRestrict U)
        (old.domRestrict U) hker
      let fresh := e.toLinearMap.comp (hs n) + t.comp c
      have onCut : ∀ z : Fin m → K, (∀ y ∉ S, z y = 0) → fresh z = old z := by
        intro z hz
        exact he ⟨z,hz⟩
      let h := (Pi.basisFun K (Fin m)).constr K
        (fun j => if j ∈ bags n then fresh (Pi.basisFun K (Fin m) j)
          else old (Pi.basisFun K (Fin m) j))
      have onNew : ∀ z : Fin m → K, (∀ y ∉ bags n, z y = 0) → h z = fresh z := by
        apply linear_eq_on_bag
        intro j hj
        simp only [h, Basis.constr_basis, ite_eq_left hj]
      have onOld : ∀ i : ℕ, i < n → ∀ z : Fin m → K,
          (∀ y ∉ bags i, z y = 0) → h z = old z := by
        intro i hi
        apply linear_eq_on_bag
        intro j hj
        by_cases jn : j ∈ bags n
        · have jS : j ∈ S := interval_overlap_subset bags interval hi (by omega)
              (Finset.mem_inter.mpr ⟨hj,jn⟩)
          have eq := onCut (Pi.basisFun K (Fin m) j) (basis_in_bag jS)
          simpa only [h, Basis.constr_basis, ite_eq_left jn] using eq
        · simp only [h, Basis.constr_basis, ite_eq_right jn]
      refine ⟨h, ?_⟩
      intro i hi z hz
      by_cases hin : i = n
      · subst i
        change (c z,h z) = (0,0) ↔ (c z,hs n z) = (0,0)
        rw [onNew z hz]
        exact shear_kernel c (hs n) e t z
      · have eq := onOld i (by omega) z hz
        have prev := hold i (by omega) z hz
        change (c z,h z) = (0,0) ↔ (c z,hs i z) = (0,0)
        rw [eq]
        exact prev
  exact build a le_rfl

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open Module Submodule Matrix
variable {K Z : Type} [Field K] [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]

theorem complete_from_global_lift {n m r : ℕ} (T : Matrix (Fin n) (Fin m) K)
    (J : Fin n → Finset (Fin m)) (L : (Fin m → K) →ₗ[K] Z)
    (budget : finrank K Z ≤ r)
    (annihilates : ∀ x (v : Fin m → K), (∀ j ∉ J x, v j = 0) → L v = 0 →
      T.mulVec v x = 0) :
    ∃ G : Matrix (Fin n) (Fin m) K, G.rank ≤ r ∧ ∀ x j, j ∈ J x → G x j = T x j := by
  classical
  have rowFactor (x : Fin n) : ∃ e : Z →ₗ[K] K, ∀ (v : Fin m → K),
      (∀ j ∉ J x, v j = 0) → e (L v) = T.mulVec v x := by
    let P : Submodule K (Fin m → K) := bagSpace (J x)
    let b : (Fin m → K) →ₗ[K] K := (LinearMap.proj x).comp T.mulVecLin
    have inc : LinearMap.ker (L.comp P.subtype) ≤ LinearMap.ker (b.comp P.subtype) := by
      intro v hv
      exact annihilates x v v.property hv
    obtain ⟨e, he⟩ := factor_on_image (L.comp P.subtype) (b.comp P.subtype) inc
    exact ⟨e, fun v hv => he (⟨v,hv⟩ : P)⟩
  choose e he using rowFactor
  let out : Z →ₗ[K] (Fin n → K) := LinearMap.pi e
  refine ⟨LinearMap.toMatrix' (out.comp L), ?_, ?_⟩
  · change finrank K (LinearMap.range ((LinearMap.toMatrix' (out.comp L)).toLin')) ≤ r
    rw [Matrix.toLin'_toMatrix']
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range L out)).trans
      (LinearMap.finrank_range_le out |>.trans budget)
  · intro x j mem
    rw [LinearMap.toMatrix'_apply]
    change e x (L (Pi.single j 1)) = T x j
    have supp : ∀ k ∉ J x, (Pi.single j 1 : Fin m → K) k = 0 := by
      intro k hk
      exact Pi.single_eq_of_ne (fun h : k = j => hk (h ▸ mem)) _
    rw [he x _ supp, Matrix.mulVec_single_one]
    rfl

theorem finish_rows {n m a r d : ℕ} (T : Matrix (Fin n) (Fin m) K)
    (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m)) (R : Finset (Fin n))
    (allrows : ∀ x, row x = none → x ∈ R) (dr : d ≤ r)
    (visible_dim : finrank K (LinearMap.range (T.submatrix (fun x : R => x.val) id).mulVecLin) = d)
    (h : (Fin m → K) →ₗ[K] (Fin (r-d) → K))
    (localRows : ∀ i : Fin a, ∀ v : Fin m → K, (∀ j ∉ bags i.val, v j = 0) →
      (((T.submatrix (fun x : R => x.val) id).mulVecLin.rangeRestrict).prod h) v = 0 →
      ∀ x, row x = some i → T.mulVec v x = 0) :
    ∃ G : Matrix (Fin n) (Fin m) K, G.rank ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ y ∈ bags i.val) → G x y = T x y := by
  classical
  let J := fun x => (row x).elim (Finset.univ : Finset (Fin m)) (fun i => bags i.val)
  let c := (T.submatrix (fun x : R => x.val) id).mulVecLin
  let L := c.rangeRestrict.prod h
  have budget : finrank K ((LinearMap.range c) × (Fin (r-d) → K)) ≤ r := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, visible_dim]
    omega
  have zeroRows (x : Fin n) (v : Fin m → K) (supp : ∀ j ∉ J x, v j = 0)
      (zero : L v = 0) : T.mulVec v x = 0 := by
    cases eq : row x with
    | none =>
      have h0 : c.rangeRestrict v = 0 := congrArg Prod.fst zero
      have h1 : c v = 0 := congrArg Subtype.val h0
      exact congrFun h1 (⟨x,allrows x eq⟩ : R)
    | some i =>
      exact localRows i v (by simpa [J,eq] using supp) zero x eq
  obtain ⟨G,rank,eq⟩ := complete_from_global_lift T J L budget zeroRows
  refine ⟨G,rank,?_⟩
  intro x y obs
  apply eq x y
  rcases obs with h0 | ⟨i,hi,mem⟩
  · simp [J,h0]
  · simpa [J,hi] using mem

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

set_option maxHeartbeats 1500000 in
theorem completion : ∀ (K : Type) [Field K] (n m a r : ℕ) (T : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m)),
  (∀ i j k : Fin a, i ≤ j → j ≤ k → bags i.val ∩ bags k.val ⊆ bags j.val) →
  let cut := fun j : ℕ => if 0 < j ∧ j < a then bags (j-1) ∩ bags j else ∅
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let rk := fun (B : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let X := Fin m → K
  let State := Submodule K X
  let supported := fun (S : Finset (Fin m)) (z : X) => ∀ y ∉ S, z y = 0
  let agrees := fun (i : Fin a) (U V : State) =>
    ∀ z : X, supported (cut i.val ∩ cut (i.val+1)) z → (z ∈ U ↔ z ∈ V)
  let fits := fun (B : Matrix (Fin n) (Fin m) K) (i : Fin a) (j : ℕ) (U : State) =>
    (∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, B.mulVec z x = 0) ∧
    rk T R Finset.univ + rk B (rows i) (bags i.val) + (cut j).card ≤
      r + rk T R (bags i.val) + rk B (rows i) (cut j) + Module.finrank K U
  ((∃ G : Matrix (Fin n) (Fin m) K, Matrix.rank G ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ y ∈ bags i.val) → G x y = T x y) ↔
    rk T R Finset.univ ≤ r ∧ ∃ N : ℕ → State, ∀ i : Fin a,
      agrees i (N i.val) (N (i.val+1)) ∧
      fits T i i.val (N i.val) ∧ fits T i (i.val+1) (N (i.val+1))) := by
  intro K inst n m a r T row bags interval cut R rows rk X State supported agrees fits
  constructor
  · exact necessity K n m a r T row bags interval
  rintro ⟨budget, N, states⟩
  have left (i : Fin a) : cut i.val ⊆ bags i.val := by
    dsimp only [cut]
    split
    · exact Finset.inter_subset_right
    · exact Finset.empty_subset _
  have right (i : Fin a) : cut (i.val+1) ⊆ bags i.val := by
    dsimp only [cut]
    split
    · simp
    · exact Finset.empty_subset _
  let c := (rowMap T R).rangeRestrict
  let H := Fin (r-rankOn T R Finset.univ) → K
  have make (i : Fin a) := local_panel_data T R (rows i) (bags i.val)
    (cut i.val) (cut (i.val+1)) (N i.val) (N (i.val+1)) r
    Finset.subset_union_left (left i) (right i) budget (states i).1
    (states i).2.1.1 (states i).2.2.1 (states i).2.1.2 (states i).2.2.2
  choose h localProof using make
  let hs (i : ℕ) : (Fin m → K) →ₗ[K] H := if hi : i < a then h ⟨i,hi⟩ else 0
  have ordered (i j k : ℕ) (ij : i ≤ j) (jk : j ≤ k) (ka : k < a) :
      bags i ∩ bags k ⊆ bags j :=
    interval ⟨i,by omega⟩ ⟨j,by omega⟩ ⟨k,ka⟩ ij jk
  have neighboring (i : ℕ) (next : i+1 < a) (z : Fin m → K)
      (zs : ∀ j ∉ bags i ∩ bags (i+1), z j = 0) :
      (c.prod (hs i)) z = 0 ↔ (c.prod (hs (i+1))) z = 0 := by
    have ia : i < a := by omega
    have same : cut (i+1) = bags i ∩ bags (i+1) := by simp [cut, next]
    have onCut : ∀ j ∉ cut (i+1), z j = 0 := by simpa only [same] using zs
    have prev := (localProof ⟨i,ia⟩).2.1 z onCut
    have curr := (localProof ⟨i+1,next⟩).1 z onCut
    simpa only [hs, dite_eq_left ia, dite_eq_left next, c] using prev.trans curr.symm
  obtain ⟨globalH, glues⟩ := glue_interval_maps a m bags ordered c hs neighboring
  apply finish_rows T row bags R (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    budget (rank_common T R) globalH
  intro i z inBag ker x xi
  have same := (glues i.val i.isLt z inBag).mp ker
  have same' : (c.prod (h i)) z = 0 := by simpa [hs, i.isLt] using same
  exact (localProof i).2.2 z inBag same' x
    (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xi⟩))

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

theorem anchor_rows_eq {n m : ℕ} (T P : Fin n → Fin m → Bool) (u : Fin n) (q : Fin m)
    (R : Finset (Fin n)) (hu : u ∈ R) (hR : ∀ x ∈ R, ∀ y, P x y = T x y) (x : Fin n) (hx : x ∈ R)
    (y : Fin m) :
    anchor u q (fun i j => b2z (P i j)) x y
      = ((T x y).toNat : ZMod 2) + ((T x q).toNat : ZMod 2) + ((T u y).toNat : ZMod 2)
        + ((T u q).toNat : ZMod 2) := by
  simp only [anchor, hR x hx, hR u hu]
  cases T x y <;> cases T x q <;> cases T u y <;> cases T u q <;> simp [b2z]

theorem anchor_entry_eq {n m : ℕ} (T P : Fin n → Fin m → Bool) (u : Fin n) (q : Fin m)
    (hPu : ∀ y, P u y = T u y) (hPq : ∀ x, P x q = T x q) (x : Fin n) (y : Fin m) :
    anchor u q (fun i j => b2z (P i j)) x y
      = ((T x y).toNat : ZMod 2) + ((T x q).toNat : ZMod 2) + ((T u y).toNat : ZMod 2)
        + ((T u q).toNat : ZMod 2) + (if P x y ≠ T x y then 1 else 0) := by
  simp only [anchor, hPq x, hPq u, hPu y]
  cases P x y <;> cases T x y <;> cases T x q <;> cases T u y <;> cases T u q <;>
    first | (simp [b2z]; done) | decide

theorem rank_sub_congr {n m : ℕ} (M B : Matrix (Fin n) (Fin m) (ZMod 2)) (I : Finset (Fin n))
    (J : Finset (Fin m)) (h : ∀ x ∈ I, ∀ y ∈ J, M x y = B x y) :
    (M.submatrix (fun x : I => x.val) (fun y : J => y.val)).rank
      = (B.submatrix (fun x : I => x.val) (fun y : J => y.val)).rank := by
  congr 1
  ext x y
  exact h x.val x.property y.val y.property

theorem mulVec_congr_supp {n m : ℕ} (M B : Matrix (Fin n) (Fin m) (ZMod 2)) (S : Finset (Fin m))
    (z : Fin m → ZMod 2) (hz : ∀ y ∉ S, z y = 0) (x : Fin n) (h : ∀ y ∈ S, M x y = B x y) :
    M.mulVec z x = B.mulVec z x := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ S
  · rw [h y hy]
  · rw [hz y hy, mul_zero, mul_zero]

theorem rank_rows_le {n m t : ℕ} (T P : Fin n → Fin m → Bool) (u : Fin n) (q : Fin m)
    (R : Finset (Fin n)) (hu : u ∈ R) (hR : ∀ x ∈ R, ∀ y, P x y = T x y)
    (Q : Circuit) (hlen : ∀ g ∈ Q.gates, g.inputs.length ≤ 2) (hrb : ReadsBack (n + m) Q)
    (hrep : Represents P Q) (hd1 : (depthsOf (n + m) Q.gates).getD Q.output 0 ≤ 1)
    (hcnt : Q.gates.countP nlGate ≤ t) :
    Matrix.rank (Matrix.submatrix
      (fun x y => ((T x y).toNat : ZMod 2) + ((T x q).toNat : ZMod 2) + ((T u y).toNat : ZMod 2)
        + ((T u q).toNat : ZMod 2) : Matrix (Fin n) (Fin m) (ZMod 2))
      (fun x : R => x.val) (fun y : (Finset.univ : Finset (Fin m)) => y.val)) ≤ 2 * t := by
  have h := dir_le P u q t Q hlen hrb hrep hd1 hcnt
  have e : Matrix.submatrix
      (fun x y => ((T x y).toNat : ZMod 2) + ((T x q).toNat : ZMod 2) + ((T u y).toNat : ZMod 2)
        + ((T u q).toNat : ZMod 2) : Matrix (Fin n) (Fin m) (ZMod 2))
      (fun x : R => x.val) (fun y : (Finset.univ : Finset (Fin m)) => y.val)
      = (anchor u q (fun i j => b2z (P i j))).submatrix
        (fun x : R => x.val) (fun y : (Finset.univ : Finset (Fin m)) => y.val) := by
    ext x y
    exact (anchor_rows_eq T P u q R hu hR x.val x.property y.val).symm
  rw [e]
  exact (Matrix.rank_submatrix_le _ _ _).trans h

end PEqualNP.Outside.L_meta_33653

namespace PEqualNP.Outside.L_meta_33653

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

theorem toNat_b2z (b : Bool) : ((b.toNat : ℕ) : ZMod 2) = b2z b := by
  cases b <;> simp [b2z]

theorem xor_decide_b2z : ∀ (b : Bool) (g c : ZMod 2), b2z (xor b (decide (g ≠ c))) = b2z b + g + c := by
  decide

theorem xor_decide_ne (b : Bool) (p : Prop) [Decidable p] : (xor b (decide p) ≠ b) ↔ p := by
  cases b <;> by_cases h : p <;> simp [h]

theorem anchor_comb : ∀ a b c d g : ZMod 2,
    (a + g + (a + b + c + d)) + (b + 0 + (b + b + d + d)) + (c + 0 + (c + d + c + d))
      + (d + 0 + (d + d + d + d)) = g := by
  decide

theorem realize {n m t : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (q : Fin m)
    (G : Matrix (Fin n) (Fin m) (ZMod 2)) (hG : G.rank ≤ 2 * t) (hu : ∀ y, G u y = 0)
    (hq : ∀ x, G x q = 0) :
    ∃ (P : Fin n → Fin m → Bool) (Q : Circuit), (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (n + m) Q ∧ Represents P Q ∧ (depthsOf (n + m) Q.gates).getD Q.output 0 ≤ 1 ∧
      Q.gates.countP nlGate ≤ t ∧
      ∀ x y, (P x y ≠ T x y ↔ G x y ≠ ((T x y).toNat : ZMod 2) + ((T x q).toNat : ZMod 2)
        + ((T u y).toNat : ZMod 2) + ((T u q).toNat : ZMod 2)) := by
  let P : Fin n → Fin m → Bool := fun x y => xor (T x y) (decide (G x y ≠
    ((T x y).toNat : ZMod 2) + ((T x q).toNat : ZMod 2) + ((T u y).toNat : ZMod 2)
      + ((T u q).toNat : ZMod 2)))
  have hb : ∀ x y, b2z (P x y) = b2z (T x y) + G x y +
      (b2z (T x y) + b2z (T x q) + b2z (T u y) + b2z (T u q)) := by
    intro x y
    show b2z (xor (T x y) (decide (G x y ≠ _))) = _
    rw [xor_decide_b2z]
    simp only [toNat_b2z]
  have hanch : anchor u q (fun i j => b2z (P i j)) = G := by
    ext x y
    show b2z (P x y) + b2z (P x q) + b2z (P u y) + b2z (P u q) = G x y
    rw [hb x y, hb x q, hb u y, hb u q, hq x, hu y, hu q]
    exact anchor_comb _ _ _ _ _
  obtain ⟨Q, ⟨hlen, hrb, hrep⟩, hd, hc⟩ := dir_ge P u q t (by rw [hanch]; exact hG)
  exact ⟨P, Q, hlen, hrb, hrep, hd, hc, fun x y => xor_decide_ne _ _⟩

theorem main_bridge (n m a t E : ℕ) (T : Fin n → Fin m → Bool)
  (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m))
  (u : Fin n) (q : Fin m) (hu : row u = none) (w : Fin n × Fin m → ℕ) :
  (∀ i j k : Fin a, i ≤ j → j ≤ k → bags i.val ∩ bags k.val ⊆ bags j.val) →
  let cut := fun j : ℕ => if 0 < j ∧ j < a then bags (j-1) ∩ bags j else ∅
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let entry := fun x y => ((T x y).toNat : ZMod 2)
  let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => entry x y + entry x q + entry u y + entry u q
  let rk := fun (B : Matrix (Fin n) (Fin m) (ZMod 2)) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let X := Fin m → (ZMod 2)
  let State := Submodule (ZMod 2) X
  let supported := fun (S : Finset (Fin m)) (z : X) => ∀ y ∉ S, z y = 0
  let agrees := fun (i : Fin a) (U V : State) =>
    ∀ z : X, supported (cut i.val ∩ cut (i.val+1)) z → (z ∈ U ↔ z ∈ V)
  let fits := fun (B : Matrix (Fin n) (Fin m) (ZMod 2)) (i : Fin a) (j : ℕ) (U : State) =>
    (∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, B.mulVec z x = 0) ∧
    rk A R Finset.univ + rk B (rows i) (bags i.val) + (cut j).card ≤
      2*t + rk A R (bags i.val) + rk B (rows i) (cut j) + Module.finrank (ZMod 2) U
  let cells := fun i : Fin a => (Finset.univ : Finset (Fin n × Fin m)).filter
    (fun z => row z.1 = some i ∧ z.2 ∈ bags i.val ∧ z.2 ≠ q)
  ((∀ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q →
    PEqualNP.Represents.Represents P Q → (depthsOf (n+m) Q.gates).getD Q.output 0 ≤ 1 → Q.gates.countP nlGate ≤ t →
    (∀ x y, row x = none → P x y = T x y) → (∀ x, P x q = T x q) →
    E ≤ ∑ i : Fin a, ((cells i).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w) ↔
    2*t < rk A R Finset.univ ∨ ∃ h : ℕ → State → ℕ, h 0 ⊥ = 0 ∧ E ≤ h a ⊥ ∧
      ∀ (i : Fin a) (U V : State) (F : Finset (Fin n × Fin m)), F ⊆ cells i →
        let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => A x y + (if (x,y) ∈ F then 1 else 0)
        agrees i U V → fits B i i.val U → fits B i (i.val+1) V →
          h (i.val+1) V ≤ h i.val U + F.sum w) := by
  intro interval cut R rows entry A rk X State supported agrees fits cells
  constructor
  ·
    intro hall
    classical
    by_cases hbig : 2*t < rk A R Finset.univ
    · exact Or.inl hbig
    let Bof : Finset (Fin n × Fin m) → Matrix (Fin n) (Fin m) (ZMod 2) :=
      fun F x y => A x y + (if (x,y) ∈ F then 1 else 0)
    let Reach : ℕ → State → ℕ → Prop := fun j U c =>
      ∃ (N : ℕ → State) (Fs : ℕ → Finset (Fin n × Fin m)), N j = U ∧
        (∀ i : Fin a, i.val < j → Fs i.val ⊆ cells i ∧ agrees i (N i.val) (N (i.val+1)) ∧
          fits (Bof (Fs i.val)) i i.val (N i.val) ∧ fits (Bof (Fs i.val)) i (i.val+1) (N (i.val+1))) ∧
        c = ∑ k ∈ Finset.range j, (Fs k).sum w
    let S : ℕ → State → Set ℕ := fun j U => {c | Reach j U c ∨ c = E}
    let h : ℕ → State → ℕ := fun j U => sInf (S j U)
    have hmem : ∀ j U, Reach j U (h j U) ∨ h j U = E := fun j U =>
      Nat.sInf_mem (s := S j U) ⟨E, Or.inr rfl⟩
    have hle : ∀ j U c, (Reach j U c ∨ c = E) → h j U ≤ c := fun j U c hc =>
      Nat.sInf_le (s := S j U) hc
    refine Or.inr ⟨h, ?_, ?_, ?_⟩
    · exact Nat.le_zero.mp (hle 0 ⊥ 0 (Or.inl ⟨fun _ => ⊥, fun _ => ∅, rfl,
        fun i hi => absurd hi (Nat.not_lt_zero _), by simp⟩))
    · rcases hmem a ⊥ with hr | he
      · obtain ⟨N, Fs, -, hsteps, hc⟩ := hr
        refine le_of_le_of_eq ?_ hc.symm
        have hst := fun i : Fin a => hsteps i i.isLt
        let T' : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y =>
          A x y + (if ∃ k : Fin a, row x = some k ∧ (x,y) ∈ Fs k.val then 1 else 0)
        have hTA : ∀ x ∈ R, ∀ y, T' x y = A x y := by
          intro x hx y
          have hnone : row x = none := (Finset.mem_filter.mp hx).2
          have hno : ¬ ∃ k : Fin a, row x = some k ∧ (x,y) ∈ Fs k.val := by
            rintro ⟨k, hk, -⟩
            rw [hnone] at hk
            cases hk
          show A x y + (if ∃ k : Fin a, row x = some k ∧ (x,y) ∈ Fs k.val then 1 else 0) = A x y
          rw [if_neg hno, add_zero]
        have hTB : ∀ i : Fin a, ∀ x ∈ rows i, ∀ y, T' x y = Bof (Fs i.val) x y := by
          intro i x hx y
          have key : (∃ k : Fin a, row x = some k ∧ (x,y) ∈ Fs k.val) ↔ (x,y) ∈ Fs i.val := by
            constructor
            · rintro ⟨k, hk, hm⟩
              rcases Finset.mem_union.mp hx with hxR | hxi
              · have hn := (Finset.mem_filter.mp hxR).2
                rw [hn] at hk
                cases hk
              · have hn := (Finset.mem_filter.mp hxi).2
                rw [hn] at hk
                cases hk
                exact hm
            · intro hm
              have hcell := (hst i).1 hm
              exact ⟨i, (Finset.mem_filter.mp hcell).2.1, hm⟩
          show A x y + (if ∃ k : Fin a, row x = some k ∧ (x,y) ∈ Fs k.val then 1 else 0)
            = A x y + (if (x,y) ∈ Fs i.val then 1 else 0)
          by_cases hm : (x,y) ∈ Fs i.val
          · rw [if_pos (key.mpr hm), if_pos hm]
          · rw [if_neg (fun hh => hm (key.mp hh)), if_neg hm]
        have conv : ∀ (i : Fin a) (j : ℕ) (U : Submodule (ZMod 2) (Fin m → ZMod 2)),
            fits (Bof (Fs i.val)) i j U →
            ((∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, T'.mulVec z x = 0) ∧
              rk T' R Finset.univ + rk T' (rows i) (bags i.val) + (cut j).card ≤
                2*t + rk T' R (bags i.val) + rk T' (rows i) (cut j) + Module.finrank (ZMod 2) U) := by
          rintro i j U ⟨hz, hrk⟩
          refine ⟨fun z hzU => ⟨(hz z hzU).1, fun x hx => ?_⟩, ?_⟩
          · exact (mulVec_congr_supp T' (Bof (Fs i.val)) Finset.univ z
              (fun y hy => absurd (Finset.mem_univ y) hy) x (fun y _ => hTB i x hx y)).trans
              ((hz z hzU).2 x hx)
          · have r1 : rk T' R Finset.univ = rk A R Finset.univ :=
              rank_sub_congr T' A R Finset.univ (fun x hx y _ => hTA x hx y)
            have r2 : rk T' R (bags i.val) = rk A R (bags i.val) :=
              rank_sub_congr T' A R (bags i.val) (fun x hx y _ => hTA x hx y)
            have r3 : rk T' (rows i) (bags i.val) = rk (Bof (Fs i.val)) (rows i) (bags i.val) :=
              rank_sub_congr T' (Bof (Fs i.val)) (rows i) (bags i.val) (fun x hx y _ => hTB i x hx y)
            have r4 : rk T' (rows i) (cut j) = rk (Bof (Fs i.val)) (rows i) (cut j) :=
              rank_sub_congr T' (Bof (Fs i.val)) (rows i) (cut j) (fun x hx y _ => hTB i x hx y)
            rw [r1, r2, r3, r4]
            exact hrk
        have hrkR : rk T' R Finset.univ ≤ 2*t := by
          have r1 : rk T' R Finset.univ = rk A R Finset.univ :=
            rank_sub_congr T' A R Finset.univ (fun x hx y _ => hTA x hx y)
          exact r1.le.trans (Nat.not_lt.mp hbig)
        obtain ⟨G, hGr, hGe⟩ := (completion (ZMod 2) n m a (2*t) T' row bags interval).mpr
          ⟨hrkR, N, fun i => ⟨(hst i).2.1, conv i i.val _ (hst i).2.2.1,
            conv i (i.val+1) _ (hst i).2.2.2⟩⟩
        let G' : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => if y = q then 0 else G x y
        have hG'r : G'.rank ≤ 2*t := by
          have e : G' = G * Matrix.diagonal (fun y => if y = q then (0 : ZMod 2) else 1) := by
            ext x y
            rw [Matrix.mul_diagonal]
            show (if y = q then 0 else G x y) = G x y * (if y = q then 0 else 1)
            by_cases hy : y = q
            · rw [if_pos hy, if_pos hy, mul_zero]
            · rw [if_neg hy, if_neg hy, mul_one]
          rw [e]
          exact (Matrix.rank_mul_le_left _ _).trans hGr
        have hAq : ∀ x, A x q = 0 := by
          intro x
          show ((T x q).toNat : ZMod 2) + ((T x q).toNat : ZMod 2) + ((T u q).toNat : ZMod 2)
            + ((T u q).toNat : ZMod 2) = 0
          cases T x q <;> cases T u q <;> decide
        have hAu : ∀ y, A u y = 0 := by
          intro y
          show ((T u y).toNat : ZMod 2) + ((T u q).toNat : ZMod 2) + ((T u y).toNat : ZMod 2)
            + ((T u q).toNat : ZMod 2) = 0
          cases T u y <;> cases T u q <;> decide
        have hG'q : ∀ x, G' x q = 0 := by
          intro x
          show (if q = q then 0 else G x q) = 0
          rw [if_pos rfl]
        have hG'A : ∀ x y, row x = none → G' x y = A x y := by
          intro x y hx
          show (if y = q then 0 else G x y) = A x y
          by_cases hy : y = q
          · rw [if_pos hy, hy, hAq]
          · rw [if_neg hy, hGe x y (Or.inl hx)]
            exact hTA x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩) y
        obtain ⟨P, Q, hlen, hrb, hrep, hd, hcnt, hdiff⟩ := realize T u q G' hG'r
          (fun y => (hG'A u y hu).trans (hAu y)) hG'q
        have hP1 : ∀ x y, row x = none → P x y = T x y := by
          intro x y hx
          by_contra hne
          exact (hdiff x y).mp hne (hG'A x y hx)
        have hP2 : ∀ x, P x q = T x q := by
          intro x
          by_contra hne
          exact (hdiff x q).mp hne ((hG'q x).trans (hAq x).symm)
        have hEle := hall P Q hlen hrb hrep hd hcnt hP1 hP2
        refine hEle.trans ?_
        have hsum : ∑ i : Fin a, (Fs i.val).sum w = ∑ k ∈ Finset.range a, (Fs k).sum w :=
          Fin.sum_univ_eq_sum_range (fun k => (Fs k).sum w) a
        rw [← hsum]
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset ?_
        rintro ⟨x, y⟩ hz
        obtain ⟨hzc, hne⟩ := Finset.mem_filter.mp hz
        obtain ⟨-, hrow, hbag, hzq⟩ := Finset.mem_filter.mp hzc
        by_contra hnot
        apply (hdiff x y).mp hne
        show (if y = q then 0 else G x y) = A x y
        rw [if_neg hzq, hGe x y (Or.inr ⟨i, hrow, hbag⟩),
          hTB i x (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrow⟩)) y]
        show A x y + (if (x, y) ∈ Fs i.val then 1 else 0) = A x y
        rw [if_neg hnot, add_zero]
      · exact he.ge
    · intro i U V F hF B hag hf1 hf2
      rcases hmem i.val U with hr | he
      · obtain ⟨N, Fs, hNU, hsteps, hc⟩ := hr
        refine hle (i.val+1) V (h i.val U + F.sum w) (Or.inl ⟨Function.update N (i.val+1) V,
          Function.update Fs i.val F, Function.update_self _ _ _, ?_, ?_⟩)
        · intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
          · have e1 : Function.update N (i.val+1) V k.val = N k.val :=
              Function.update_of_ne (by omega) _ _
            have e2 : Function.update N (i.val+1) V (k.val+1) = N (k.val+1) :=
              Function.update_of_ne (by omega) _ _
            have e3 : Function.update Fs i.val F k.val = Fs k.val :=
              Function.update_of_ne (by omega) _ _
            rw [e1, e2, e3]
            exact hsteps k hlt
          · have hki : k = i := Fin.ext heq
            subst hki
            have e1 : Function.update N (k.val+1) V k.val = N k.val :=
              Function.update_of_ne (by omega) _ _
            have e2 : Function.update N (k.val+1) V (k.val+1) = V := Function.update_self _ _ _
            have e3 : Function.update Fs k.val F k.val = F := Function.update_self _ _ _
            rw [e1, e2, e3, hNU]
            exact ⟨hF, hag, hf1, hf2⟩
        · rw [Finset.sum_range_succ, Function.update_self, hc]
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Function.update_of_ne (by have := Finset.mem_range.mp hk; omega)]
      · rw [he]
        exact (hle _ _ E (Or.inr rfl)).trans (Nat.le_add_right _ _)
  · rintro (hbig | ⟨h, h0, hE, hstep⟩) P Q hlen hrb hrep hd1 hcnt hPR hPq
    · exfalso
      have hle := rank_rows_le T P u q R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
        (fun x hx y => hPR x y (Finset.mem_filter.mp hx).2) Q hlen hrb hrep hd1 hcnt
      exact absurd hbig (Nat.not_lt.mpr hle)
    ·
      let M : Matrix (Fin n) (Fin m) (ZMod 2) := anchor u q (fun i j => b2z (P i j))
      have hM : M.rank ≤ 2 * t := dir_le P u q t Q hlen hrb hrep hd1 hcnt
      obtain ⟨-, N, hN⟩ := (completion (ZMod 2) n m a (2*t) M row bags interval).mp
        ⟨M, hM, fun _ _ _ => rfl⟩
      have hRA : ∀ x ∈ R, ∀ y, M x y = A x y := fun x hx y =>
        anchor_rows_eq T P u q R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
          (fun x hx y => hPR x y (Finset.mem_filter.mp hx).2) x hx y
      have key : ∀ i : Fin a, h (i.val+1) (N (i.val+1)) ≤ h i.val (N i.val) +
          ((cells i).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w := by
        intro i
        let F : Finset (Fin n × Fin m) := (cells i).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)
        let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => A x y + (if (x,y) ∈ F then 1 else 0)
        have left : cut i.val ⊆ bags i.val := by
          dsimp only [cut]
          split
          · exact Finset.inter_subset_right
          · exact Finset.empty_subset _
        have right : cut (i.val+1) ⊆ bags i.val := by
          dsimp only [cut]
          split
          · simp
          · exact Finset.empty_subset _
        have hent : ∀ x ∈ rows i, ∀ y ∈ bags i.val, M x y = B x y := by
          intro x hx y hy
          have e := anchor_entry_eq T P u q (fun y => hPR u y hu) hPq x y
          have hiff : (P x y ≠ T x y) ↔ (x, y) ∈ F := by
            simp only [F, cells, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hne
              rcases Finset.mem_union.mp hx with hxR | hxi
              · exact absurd (hPR x y (Finset.mem_filter.mp hxR).2) hne
              · exact ⟨⟨(Finset.mem_filter.mp hxi).2, hy, fun hq => hne (by subst hq; exact hPq x)⟩, hne⟩
            · exact fun h => h.2
          show anchor u q (fun i j => b2z (P i j)) x y = A x y + (if (x,y) ∈ F then 1 else 0)
          rw [e]
          by_cases hd : P x y ≠ T x y
          · rw [if_pos hd, if_pos (hiff.mp hd)]
          · rw [if_neg hd, if_neg (fun h => hd (hiff.mpr h))]
        refine hstep i (N i.val) (N (i.val+1)) F (Finset.filter_subset _ _) (hN i).1 ?_ ?_
        · obtain ⟨hz, hrk⟩ := (hN i).2.1
          refine ⟨fun z hzU => ⟨(hz z hzU).1, fun x hx => ?_⟩, ?_⟩
          · rw [← mulVec_congr_supp M B (cut (i.val)) z (hz z hzU).1 x
              (fun y hy => hent x hx y (left hy))]
            exact (hz z hzU).2 x hx
          · have r1 : rk M R Finset.univ = rk A R Finset.univ :=
              rank_sub_congr M A R Finset.univ (fun x hx y _ => hRA x hx y)
            have r2 : rk M R (bags i.val) = rk A R (bags i.val) :=
              rank_sub_congr M A R (bags i.val) (fun x hx y _ => hRA x hx y)
            have r3 : rk M (rows i) (bags i.val) = rk B (rows i) (bags i.val) :=
              rank_sub_congr M B (rows i) (bags i.val) hent
            have r4 : rk M (rows i) (cut (i.val)) = rk B (rows i) (cut (i.val)) :=
              rank_sub_congr M B (rows i) (cut (i.val)) (fun x hx y hy => hent x hx y (left hy))
            show rk A R Finset.univ + rk B (rows i) (bags i.val) + (cut (i.val)).card ≤
              2*t + rk A R (bags i.val) + rk B (rows i) (cut (i.val)) + Module.finrank (ZMod 2) _
            rw [← r1, ← r2, ← r3, ← r4]
            exact hrk
        · obtain ⟨hz, hrk⟩ := (hN i).2.2
          refine ⟨fun z hzU => ⟨(hz z hzU).1, fun x hx => ?_⟩, ?_⟩
          · rw [← mulVec_congr_supp M B (cut (i.val+1)) z (hz z hzU).1 x
              (fun y hy => hent x hx y (right hy))]
            exact (hz z hzU).2 x hx
          · have r1 : rk M R Finset.univ = rk A R Finset.univ :=
              rank_sub_congr M A R Finset.univ (fun x hx y _ => hRA x hx y)
            have r2 : rk M R (bags i.val) = rk A R (bags i.val) :=
              rank_sub_congr M A R (bags i.val) (fun x hx y _ => hRA x hx y)
            have r3 : rk M (rows i) (bags i.val) = rk B (rows i) (bags i.val) :=
              rank_sub_congr M B (rows i) (bags i.val) hent
            have r4 : rk M (rows i) (cut (i.val+1)) = rk B (rows i) (cut (i.val+1)) :=
              rank_sub_congr M B (rows i) (cut (i.val+1)) (fun x hx y hy => hent x hx y (right hy))
            show rk A R Finset.univ + rk B (rows i) (bags i.val) + (cut (i.val+1)).card ≤
              2*t + rk A R (bags i.val) + rk B (rows i) (cut (i.val+1)) + Module.finrank (ZMod 2) _
            rw [← r1, ← r2, ← r3, ← r4]
            exact hrk
      rcases Nat.eq_zero_or_pos a with ha | ha
      · have hz : h a ⊥ = 0 := by rw [ha]; exact h0
        exact (hE.trans hz.le).trans (Nat.zero_le _)
      · have N0 : N 0 = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          have hs := ((hN ⟨0, ha⟩).2.1.1 z hz).1
          rw [Submodule.mem_bot]
          funext y
          exact hs y (by simp)
        have Na : N a = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          have hval : (⟨a-1, by omega⟩ : Fin a).val + 1 = a := by
            show a - 1 + 1 = a
            omega
          have hz' : z ∈ N ((⟨a-1, by omega⟩ : Fin a).val + 1) := by
            rw [hval]
            exact hz
          have hs := ((hN ⟨a-1, by omega⟩).2.2.1 z hz').1
          rw [Submodule.mem_bot]
          funext y
          exact hs y (by simp [hval])
        have tele : ∀ j, j ≤ a → h j (N j) ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin a => i.val < j),
            ((cells i).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w := by
          intro j
          induction j with
          | zero =>
            intro _
            rw [N0, h0]
            exact Nat.zero_le _
          | succ j ih =>
            intro hj
            have hja : j < a := hj
            have hsplit : Finset.univ.filter (fun i : Fin a => i.val < j+1)
                = insert (⟨j, hja⟩ : Fin a) (Finset.univ.filter (fun i : Fin a => i.val < j)) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
              omega
            rw [hsplit, Finset.sum_insert (by simp)]
            have k : h (j+1) (N (j+1)) ≤ h j (N j) +
                ((cells ⟨j, hja⟩).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w := key ⟨j, hja⟩
            have ih' := ih (by omega)
            refine k.trans ?_
            rw [add_comm]
            exact Nat.add_le_add_left ih' _
        have fin := tele a le_rfl
        rw [Na] at fin
        have hfull : Finset.univ.filter (fun i : Fin a => i.val < a) = Finset.univ := by
          ext i
          simp
        rw [hfull] at fin
        exact hE.trans fin

end PEqualNP.Outside.L_meta_33653

theorem PEqualNP.Outside.L_meta_33653 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m a t E : ℕ) (T : Fin n → Fin m → Bool)
  (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m))
  (u : Fin n) (q : Fin m) (_ : row u = none) (w : Fin n × Fin m → ℕ),
  (∀ i j k : Fin a, i ≤ j → j ≤ k → bags i.val ∩ bags k.val ⊆ bags j.val) →
  let cut := fun j : ℕ => if 0 < j ∧ j < a then bags (j-1) ∩ bags j else ∅
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let entry := fun x y => ((T x y).toNat : ZMod 2)
  let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => entry x y + entry x q + entry u y + entry u q
  let rk := fun (B : Matrix (Fin n) (Fin m) (ZMod 2)) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let X := Fin m → (ZMod 2)
  let State := Submodule (ZMod 2) X
  let supported := fun (S : Finset (Fin m)) (z : X) => ∀ y ∉ S, z y = 0
  let agrees := fun (i : Fin a) (U V : State) =>
    ∀ z : X, supported (cut i.val ∩ cut (i.val+1)) z → (z ∈ U ↔ z ∈ V)
  let fits := fun (B : Matrix (Fin n) (Fin m) (ZMod 2)) (i : Fin a) (j : ℕ) (U : State) =>
    (∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, B.mulVec z x = 0) ∧
    rk A R Finset.univ + rk B (rows i) (bags i.val) + (cut j).card ≤
      2*t + rk A R (bags i.val) + rk B (rows i) (cut j) + Module.finrank (ZMod 2) U
  let cells := fun i : Fin a => (Finset.univ : Finset (Fin n × Fin m)).filter
    (fun z => row z.1 = some i ∧ z.2 ∈ bags i.val ∧ z.2 ≠ q)
  ((∀ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q →
    PEqualNP.Represents.Represents P Q → depth (n+m) Q ≤ 1 → Q.gates.countP nonlinear ≤ t →
    (∀ x y, row x = none → P x y = T x y) → (∀ x, P x q = T x q) →
    E ≤ ∑ i : Fin a, ((cells i).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w) ↔
    2*t < rk A R Finset.univ ∨ ∃ h : ℕ → State → ℕ, h 0 ⊥ = 0 ∧ E ≤ h a ⊥ ∧
      ∀ (i : Fin a) (U V : State) (F : Finset (Fin n × Fin m)), F ⊆ cells i →
        let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => A x y + (if (x,y) ∈ F then 1 else 0)
        agrees i U V → fits B i i.val U → fits B i (i.val+1) V →
          h (i.val+1) V ≤ h i.val U + F.sum w)
) := by
  intro nonlinear depth n m a t E T row bags u q hu w
  exact PEqualNP.Outside.L_meta_33653.main_bridge n m a t E T row bags u q hu w
