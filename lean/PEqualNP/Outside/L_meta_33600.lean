import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33600

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


def rsum {n m : ℕ} (T : Fin n → Fin m → Bool) (U : Finset (Fin n)) (j : Fin m) : ZMod 2 :=
  ∑ i ∈ U, b2z (T i j)

def wt {n m : ℕ} (T : Fin n → Fin m → Bool) (U : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => (U.sum (fun i => (T i j).toNat)) % 2 = 1)).card

theorem b2z_cast (b : Bool) : b2z b = ((b.toNat : ℕ) : ZMod 2) := by
  cases b <;> simp [b2z]

theorem wt_eq {n m : ℕ} (T : Fin n → Fin m → Bool) (U : Finset (Fin n)) :
    wt T U = (Finset.univ.filter (fun j : Fin m => rsum T U j = 1)).card := by
  unfold wt
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h : rsum T U j = ((∑ i ∈ U, (T i j).toNat : ℕ) : ZMod 2) := by
    simp [rsum, b2z_cast, Nat.cast_sum]
  rw [h, ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]

def Cond (n m t : ℕ) (T : Fin n → Fin m → Bool) : Prop :=
  ∀ S : Finset (Fin n), S.card = 2*t+2 →
    ∃ U : Finset (Fin n), U ⊆ S ∧ U.Nonempty ∧ Even U.card ∧ (wt T U = 0 ∨ wt T U = m)

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

theorem wt_const_iff {n m : ℕ} (T : Fin n → Fin m → Bool) (U : Finset (Fin n)) :
    (wt T U = 0 ∨ wt T U = m) ↔ ∃ c : ZMod 2, ∀ j, rsum T U j = c := by
  rw [wt_eq]
  constructor
  · rintro (h | h)
    · refine ⟨0, fun j => ?_⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
      have := h (Finset.mem_univ j)
      rcases zmod2_cases (rsum T U j) with h0 | h1
      · exact h0
      · exact absurd h1 this
    · refine ⟨1, fun j => ?_⟩
      have h' : (Finset.univ.filter (fun j : Fin m => rsum T U j = 1)).card
          = (Finset.univ : Finset (Fin m)).card := by
        rw [h, Finset.card_univ, Fintype.card_fin]
      rw [Finset.card_filter_eq_iff] at h'
      exact h' j (Finset.mem_univ j)
  · rintro ⟨c, hc⟩
    rcases zmod2_cases c with h0 | h1
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      rw [hc j, h0]
      decide
    · right
      have h' : (Finset.univ.filter (fun j : Fin m => rsum T U j = 1)).card
          = (Finset.univ : Finset (Fin m)).card := by
        rw [Finset.card_filter_eq_iff]
        intro j _
        rw [hc j, h1]
      rw [h', Finset.card_univ, Fintype.card_fin]

theorem even_iff_sum_one {n : ℕ} (U : Finset (Fin n)) :
    Even U.card ↔ ∑ _i ∈ U, (1 : ZMod 2) = 0 := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even]

theorem anchor_sum {n m : ℕ} (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (U : Finset (Fin n)) (j : Fin m) :
    ∑ i ∈ U, anchor u v (fun i j => b2z (T i j)) i j =
      rsum T U j + rsum T U v + (∑ _i ∈ U, (1 : ZMod 2)) * (b2z (T u j) + b2z (T u v)) := by
  unfold anchor rsum
  rw [Finset.sum_mul]
  simp only [one_mul, Finset.sum_add_distrib]
  ring

theorem sum_support {n : ℕ} (S : Finset (Fin n)) (g : S → ZMod 2) (F : Fin n → ZMod 2) :
    ∑ i ∈ (Finset.univ.filter (fun i : S => g i ≠ 0)).map (Function.Embedding.subtype _), F i
      = ∑ i : S, g i * F i := by
  rw [Finset.sum_map, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases zmod2_cases (g i) with h | h
  · simp [h]
  · simp [h]

theorem rank_imp_cond {n m : ℕ} (t : ℕ) (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (hr : (anchor u v (fun i j => b2z (T i j))).rank ≤ 2 * t) : Cond n m t T := by
  obtain ⟨rowVec, colVec, hfac⟩ := factor_of_rank_le _ hr
  intro S hS
  let M : Matrix S (Option (Fin (2*t))) (ZMod 2) :=
    fun i c => match c with
      | none => 1
      | some k => rowVec k i.val
  have hlt : Module.finrank (ZMod 2) (Option (Fin (2*t)) → ZMod 2)
      < Module.finrank (ZMod 2) (S → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp [hS]
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := M.vecMulLinear) hlt
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨g, hg, hg0⟩ := hker
  rw [LinearMap.mem_ker] at hg
  have hgc : ∀ c, ∑ i : S, g i * M i c = 0 := by
    intro c
    have := congrFun hg c
    simpa [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] using this
  refine ⟨(Finset.univ.filter (fun i : S => g i ≠ 0)).map (Function.Embedding.subtype _),
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨x, _, rfl⟩ := hi
    exact x.2
  · have : ∃ i, g i ≠ 0 := by
      by_contra hne
      exact hg0 (funext (fun i => by_contra (fun h => hne ⟨i, h⟩)))
    obtain ⟨i, hi⟩ := this
    exact ⟨i.val, Finset.mem_map.2 ⟨i, by simp [hi], rfl⟩⟩
  · rw [even_iff_sum_one, sum_support S g (fun _ => 1)]
    have := hgc none
    simpa [M] using this
  · rw [wt_const_iff]
    refine ⟨rsum T ((Finset.univ.filter (fun i : S => g i ≠ 0)).map
      (Function.Embedding.subtype _)) v, fun j => ?_⟩
    have hs := anchor_sum T u v
      ((Finset.univ.filter (fun i : S => g i ≠ 0)).map (Function.Embedding.subtype _)) j
    have h1 : ∑ _i ∈ (Finset.univ.filter (fun i : S => g i ≠ 0)).map
        (Function.Embedding.subtype _), (1 : ZMod 2) = 0 := by
      rw [sum_support S g (fun _ => 1)]
      have := hgc none
      simpa [M] using this
    have h0 : ∑ i ∈ (Finset.univ.filter (fun i : S => g i ≠ 0)).map
        (Function.Embedding.subtype _), anchor u v (fun i j => b2z (T i j)) i j = 0 := by
      rw [sum_support S g (fun i => anchor u v (fun i j => b2z (T i j)) i j)]
      simp only [hfac, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have := hgc (some k)
      simp only [M] at this
      simp only [← mul_assoc]
      rw [← Finset.sum_mul, this, zero_mul]
    rw [h0, h1, zero_mul, add_zero] at hs
    have h2 := congrArg (fun x => x + rsum T
      ((Finset.univ.filter (fun i : S => g i ≠ 0)).map (Function.Embedding.subtype _)) v) hs
    simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at h2
    exact h2.symm

theorem cond_imp_rank {n m : ℕ} (t : ℕ) (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (hc : Cond n m t T) : (anchor u v (fun i j => b2z (T i j))).rank ≤ 2 * t := by
  by_contra hlt
  have hlt' : 2 * t + 1 ≤ (anchor u v (fun i j => b2z (T i j))).rank := by omega
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2)
    (anchor u v (fun i j => b2z (T i j))).row
  have : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = (anchor u v (fun i j => b2z (T i j))).rank := by
    rw [Matrix.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  have hRcard : 2 * t + 1 ≤ (Finset.univ.image a).card := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, hcard]
    exact hlt'
  obtain ⟨R', hR'sub, hR'card⟩ := Finset.exists_subset_card_eq hRcard
  have hrowu : (anchor u v (fun i j => b2z (T i j))).row u = 0 := by
    funext j
    simp only [Matrix.row, anchor, Pi.zero_apply]
    have := zmod2_add_self (b2z (T u j) + b2z (T u v))
    rw [← this]
    ring
  have huR : ∀ k, a k ≠ u := by
    intro k hk
    have := hli.ne_zero k
    apply this
    simp only [Function.comp_apply, hk, hrowu]
  have huR' : u ∉ R' := by
    intro hu
    have := hR'sub hu
    rw [Finset.mem_image] at this
    obtain ⟨k, _, hk⟩ := this
    exact huR k hk
  obtain ⟨U, hUS, hUne, hUeven, hUwt⟩ := hc (insert u R') (by
    rw [Finset.card_insert_of_notMem huR', hR'card])
  rw [wt_const_iff] at hUwt
  obtain ⟨c, hcst⟩ := hUwt
  rw [even_iff_sum_one] at hUeven
  have hsum0 : ∑ i ∈ U, (anchor u v (fun i j => b2z (T i j))).row i = 0 := by
    funext j
    rw [Finset.sum_apply]
    have := anchor_sum T u v U j
    simp only [Matrix.row, Pi.zero_apply]
    rw [this, hUeven, hcst j, hcst v, zero_mul, add_zero, zmod2_add_self]
  have hg := Fintype.linearIndependent_iff.1 hli (fun k => if a k ∈ U then 1 else 0) (by
    have h1 : ∑ k : κ, (if a k ∈ U then (1 : ZMod 2) else 0) •
        ((anchor u v (fun i j => b2z (T i j))).row ∘ a) k
        = ∑ i ∈ Finset.univ.image a,
          (if i ∈ U then (anchor u v (fun i j => b2z (T i j))).row i else 0) := by
      rw [Finset.sum_image (fun x _ y _ h => ha h)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : a k ∈ U
      · simp [hk]
      · simp [hk]
    rw [h1, Finset.sum_ite_mem, ← hsum0]
    refine Finset.sum_subset Finset.inter_subset_right (fun i hiU hni => ?_)
    have hiS := hUS hiU
    rw [Finset.mem_insert] at hiS
    rcases hiS with rfl | hiR
    · exact hrowu
    · exact absurd (Finset.mem_inter.2 ⟨hR'sub hiR, hiU⟩) hni)
  have hUsub : U ⊆ {u} := by
    intro i hiU
    have hiS := hUS hiU
    rw [Finset.mem_insert] at hiS
    rcases hiS with rfl | hiR
    · exact Finset.mem_singleton_self _
    · exfalso
      have := hR'sub hiR
      rw [Finset.mem_image] at this
      obtain ⟨k, _, hk⟩ := this
      have hgk := hg k
      rw [hk] at hgk
      simp [hiU] at hgk
  have hUeq : U = {u} := by
    rcases Finset.subset_singleton_iff.1 hUsub with h | h
    · exact absurd h hUne.ne_empty
    · exact h
  rw [hUeq] at hUeven
  simp at hUeven

theorem rank_iff_cond {n m : ℕ} (t : ℕ) (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) :
    (anchor u v (fun i j => b2z (T i j))).rank ≤ 2 * t ↔ Cond n m t T :=
  ⟨rank_imp_cond t T u v, cond_imp_rank t T u v⟩

theorem b2z_decide (p : Prop) [Decidable p] : b2z (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [b2z, h]

def par (t j : ℕ) : ZMod 2 := ∑ k ∈ Finset.range (2*t), b2z (j.testBit k)

def zG (c : ZMod 2) (t k j : ℕ) : ZMod 2 :=
  if j < 2^(2*t) then
    ((if k < 2*t then b2z (j.testBit k) else 0) + (if k = 2*t then c + par t j else 0))
  else 0

def tab (c : ZMod 2) (n m t : ℕ) : Fin n → Fin m → Bool :=
  fun i j => decide (zG c t i.val j.val = 1)

theorem rsum_tab (c : ZMod 2) (n m t : ℕ) (U : Finset (Fin n)) (j : Fin m) :
    rsum (tab c n m t) U j = ∑ k ∈ U.map Fin.valEmbedding, zG c t k j.val := by
  unfold rsum tab
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b2z_decide]
  exact zmod2_ite_eq _

theorem sum_zG (c : ZMod 2) (t j : ℕ) (V : Finset ℕ) (hj : j < 2^(2*t)) :
    ∑ k ∈ V, zG c t k j = ∑ k ∈ V.filter (fun k => k < 2*t), b2z (j.testBit k) +
      (if 2*t ∈ V then c + par t j else 0) := by
  simp only [zG, hj, if_true, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_ite_eq']

theorem zG_big (c : ZMod 2) (t k j : ℕ) (hj : ¬ j < 2^(2*t)) : zG c t k j = 0 := by
  simp [zG, hj]

theorem zG_row (c : ZMod 2) (t k j : ℕ) (hk : 2*t < k) : zG c t k j = 0 := by
  have h1 : ¬ k < 2*t := by omega
  have h2 : k ≠ 2*t := by omega
  simp [zG, h1, h2]

theorem wt_zero_of {n m : ℕ} (T : Fin n → Fin m → Bool) (U : Finset (Fin n))
    (h : ∀ j, rsum T U j = 0) : wt T U = 0 := by
  rw [wt_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  rw [h j]
  exact zero_ne_one

theorem condA (n m t : ℕ) : Cond n m t (tab 0 n m t) := by
  intro S hS
  by_cases h : ∀ k ≤ 2*t, k ∈ S.map Fin.valEmbedding
  · refine ⟨S, Finset.Subset.refl _, ?_, ⟨t+1, by omega⟩, Or.inl ?_⟩
    · exact Finset.card_pos.mp (by omega)
    · apply wt_zero_of
      intro j
      rw [rsum_tab]
      by_cases hj : j.val < 2^(2*t)
      · rw [sum_zG _ _ _ _ hj]
        have hf : (S.map Fin.valEmbedding).filter (fun k => k < 2*t) = Finset.range (2*t) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨fun h' => h'.2, fun h' => ⟨h k (by omega), h'⟩⟩
        rw [hf, if_pos (h _ le_rfl), zero_add]
        exact zmod2_add_self _
      · exact Finset.sum_eq_zero fun k _ => zG_big _ _ _ _ hj
  · push_neg at h
    obtain ⟨k0, hk0, hk0S⟩ := h
    have h1 : (S.filter (fun i : Fin n => i.val ≤ 2*t)).card ≤ 2*t := by
      have h0 : (S.filter (fun i : Fin n => i.val ≤ 2*t)).card ≤
          ((Finset.range (2*t+1)).erase k0).card := by
        apply Finset.card_le_card_of_injOn (fun i => i.val)
        · intro i hi
          have hi' := Finset.mem_filter.mp hi
          show i.val ∈ _
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (by omega)⟩
          rintro rfl
          exact hk0S (Finset.mem_map.mpr ⟨i, hi'.1, rfl⟩)
        · exact fun a _ b _ hab => Fin.ext hab
      rwa [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range,
        Nat.add_sub_cancel] at h0
    have h2 := Finset.card_filter_add_card_filter_not (s := S)
      (fun i : Fin n => i.val ≤ 2*t)
    have h3 : 1 < (S.filter (fun i : Fin n => ¬ i.val ≤ 2*t)).card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h3
    rw [Finset.mem_filter] at hx hy
    refine ⟨{x, y}, ?_, ⟨x, by simp⟩, ?_, Or.inl ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      exacts [hx.1, hy.1]
    · rw [Finset.card_pair hxy]
      exact ⟨1, rfl⟩
    · apply wt_zero_of
      intro j
      rw [rsum_tab]
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_map, Finset.mem_insert, Finset.mem_singleton,
        Fin.valEmbedding_apply] at hk
      obtain ⟨z, hz, rfl⟩ := hk
      apply zG_row
      rcases hz with rfl | rfl <;> omega

theorem not_condB (n m t : ℕ) (hn : 2*t+2 ≤ n) (hm : 2^(2*t)+1 ≤ m) :
    ¬ Cond n m t (tab 1 n m t) := by
  intro hC
  obtain ⟨U, hUS, hne, hev, hw⟩ := hC ((Finset.range (2*t+2)).attachFin
    (fun k hk => by rw [Finset.mem_range] at hk; omega))
    (by rw [Finset.card_attachFin, Finset.card_range])
  have hval : ∀ i ∈ U, i.val ≤ 2*t+1 := by
    intro i hi
    have := hUS hi
    rw [Finset.mem_attachFin, Finset.mem_range] at this
    omega
  have hpos : 0 < 2^(2*t) := by positivity
  rw [wt_eq] at hw
  rcases hw with hw | hw
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hw
    by_cases h2 : 2*t ∈ U.map Fin.valEmbedding
    · apply hw (Finset.mem_univ (⟨0, by omega⟩ : Fin m))
      rw [rsum_tab, sum_zG _ _ _ _ hpos, if_pos h2]
      simp [par, b2z]
    · have hex : ∃ i ∈ U, i.val < 2*t := by
        have hc : 1 < U.card := by
          obtain ⟨r, hr⟩ := hev
          have := Finset.card_pos.mpr hne
          omega
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
        have hx1 := hval x hx
        have hy1 := hval y hy
        have hx2 : x.val ≠ 2*t := fun h => h2 (Finset.mem_map.mpr ⟨x, hx, h⟩)
        have hy2 : y.val ≠ 2*t := fun h => h2 (Finset.mem_map.mpr ⟨y, hy, h⟩)
        have hxy' : x.val ≠ y.val := fun h => hxy (Fin.ext h)
        by_cases hx3 : x.val < 2*t
        · exact ⟨x, hx, hx3⟩
        · exact ⟨y, hy, by omega⟩
      obtain ⟨i, hi, hit⟩ := hex
      have hp : 2^i.val < 2^(2*t) := Nat.pow_lt_pow_right (by norm_num) hit
      apply hw (Finset.mem_univ (⟨2^i.val, by omega⟩ : Fin m))
      rw [rsum_tab, sum_zG _ _ _ _ hp, if_neg h2, add_zero]
      simp only [Nat.testBit_two_pow, b2z_decide]
      rw [Finset.sum_ite_eq, if_pos]
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨i, hi, rfl⟩, hit⟩
  · have huniv := Finset.eq_univ_of_card _ (hw.trans (Fintype.card_fin m).symm)
    have hmem : (⟨2^(2*t), by omega⟩ : Fin m) ∈
        Finset.univ.filter (fun j : Fin m => rsum (tab 1 n m t) U j = 1) := by
      rw [huniv]
      exact Finset.mem_univ _
    rw [Finset.mem_filter, rsum_tab,
      Finset.sum_eq_zero (fun k _ => zG_big _ _ _ _ (lt_irrefl _))] at hmem
    exact zero_ne_one hmem.2

theorem par_flip (t j i0 : ℕ) (h : i0 < 2*t) : par t (j ^^^ 2^i0) = par t j + 1 := by
  unfold par
  simp only [Nat.testBit_xor, Nat.testBit_two_pow, b2z_xor, b2z_decide, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr h)]

def flipBit (t i0 j : ℕ) : ℕ := if j < 2^(2*t) then j ^^^ 2^i0 else j

theorem flip_lt_iff (t i0 j : ℕ) (h : i0 < 2*t) : flipBit t i0 j < 2^(2*t) ↔ j < 2^(2*t) := by
  unfold flipBit
  by_cases hj : j < 2^(2*t)
  · simp only [hj, if_true, iff_true]
    exact Nat.xor_lt_two_pow hj (Nat.pow_lt_pow_right (by norm_num) h)
  · simp [hj]

theorem flip_flip (t i0 j : ℕ) (h : i0 < 2*t) : flipBit t i0 (flipBit t i0 j) = j := by
  by_cases hj : j < 2^(2*t)
  · have h' := (flip_lt_iff t i0 j h).2 hj
    have e : flipBit t i0 j = j ^^^ 2^i0 := by simp [flipBit, hj]
    rw [e] at h' ⊢
    simp [flipBit, h', Nat.xor_assoc]
  · simp [flipBit, hj]

theorem weights (n m t : ℕ) (hm : 2^(2*t)+1 ≤ m) (U : Finset (Fin n)) (hc : U.card ≤ 2*t) :
    wt (tab 0 n m t) U = wt (tab 1 n m t) U := by
  rw [wt_eq, wt_eq]
  by_cases h2 : 2*t ∈ U.map Fin.valEmbedding
  · have hex : ∃ i0 < 2*t, i0 ∉ U.map Fin.valEmbedding := by
      by_contra hcon
      push_neg at hcon
      have hsub : Finset.range (2*t+1) ⊆ U.map Fin.valEmbedding := by
        intro k hk
        rw [Finset.mem_range] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
        · exact hcon k h
        · rw [h]; exact h2
      have := Finset.card_le_card hsub
      rw [Finset.card_range, Finset.card_map] at this
      omega
    obtain ⟨i0, hi0, hi0U⟩ := hex
    have hflt : ∀ j : Fin m, flipBit t i0 j.val < m := by
      intro j
      by_cases hj : j.val < 2^(2*t)
      · have := (flip_lt_iff t i0 j.val hi0).2 hj
        omega
      · simp [flipBit, hj]
    have key : ∀ j : Fin m, rsum (tab 1 n m t) U j =
        rsum (tab 0 n m t) U ⟨flipBit t i0 j.val, hflt j⟩ := by
      intro j
      rw [rsum_tab, rsum_tab]
      by_cases hj : j.val < 2^(2*t)
      · have hj' : flipBit t i0 j.val < 2^(2*t) := (flip_lt_iff t i0 j.val hi0).2 hj
        have e : flipBit t i0 j.val = j.val ^^^ 2^i0 := by simp [flipBit, hj]
        rw [sum_zG _ _ _ _ hj, sum_zG _ _ _ _ hj', if_pos h2, if_pos h2, e, par_flip _ _ _ hi0]
        have hs : ∑ k ∈ (U.map Fin.valEmbedding).filter (fun k => k < 2*t),
            b2z ((j.val ^^^ 2^i0).testBit k) =
            ∑ k ∈ (U.map Fin.valEmbedding).filter (fun k => k < 2*t), b2z (j.val.testBit k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : i0 ≠ k := by
            rintro rfl
            exact hi0U (Finset.mem_filter.mp hk).1
          simp [Nat.testBit_xor, Nat.testBit_two_pow, hk']
        rw [hs]
        ring
      · have hj' : ¬ flipBit t i0 j.val < 2^(2*t) := fun h => hj ((flip_lt_iff t i0 j.val hi0).1 h)
        rw [Finset.sum_eq_zero (fun k _ => zG_big _ _ _ _ hj),
          Finset.sum_eq_zero (fun k _ => zG_big _ _ _ _ hj')]
    have key2 : ∀ j : Fin m, rsum (tab 0 n m t) U j =
        rsum (tab 1 n m t) U ⟨flipBit t i0 j.val, hflt j⟩ := by
      intro j
      have := key ⟨flipBit t i0 j.val, hflt j⟩
      simp only [flip_flip t i0 j.val hi0, Fin.eta] at this
      exact this.symm
    refine Finset.card_bij' (fun j _ => (⟨flipBit t i0 j.val, hflt j⟩ : Fin m))
      (fun j _ => (⟨flipBit t i0 j.val, hflt j⟩ : Fin m)) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, (key2 a).symm.trans ha.2⟩
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, (key a).symm.trans ha.2⟩
    · intro a _
      exact Fin.ext (flip_flip t i0 a.val hi0)
    · intro a _
      exact Fin.ext (flip_flip t i0 a.val hi0)
  · congr 1
    refine Finset.filter_congr fun j _ => ?_
    rw [rsum_tab, rsum_tab]
    have hs : ∑ k ∈ U.map Fin.valEmbedding, zG 0 t k j.val =
        ∑ k ∈ U.map Fin.valEmbedding, zG 1 t k j.val :=
      Finset.sum_congr rfl fun k hk => by
        have hk' : k ≠ 2*t := by
          rintro rfl
          exact h2 hk
        simp [zG, hk']
    rw [hs]

theorem construct {n m t : ℕ} (hn : 2*t+2 ≤ n) (hm : 2^(2*t)+1 ≤ m) :
    ∃ A B : Fin n → Fin m → Bool, Cond n m t A ∧ ¬ Cond n m t B ∧
      ∀ U : Finset (Fin n), Even U.card → U.card ≤ 2*t → wt A U = wt B U :=
  ⟨tab 0 n m t, tab 1 n m t, condA n m t, not_condB n m t hn hm,
    fun U _ hc => weights n m t hm U hc⟩

def chi (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

theorem chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  revert a b; decide

theorem chi_add_one (a : ZMod 2) : chi a + chi (a + 1) = 0 := by
  revert a; decide

theorem chi_pm (a : ZMod 2) : chi a = 1 ∨ chi a = -1 := by
  revert a; decide

theorem zmod2_ne (a b : ZMod 2) (h : a ≠ b) : a + b = 1 := by revert a b; decide

theorem zmod2_move (a b y : ZMod 2) (h : a + y = b) : a + b = y := by revert a b y; decide

theorem zmod2_cc (c : ZMod 2) : c + (c + 1) ≠ 0 := by revert c; decide

theorem zmod2_cc' (c : ZMod 2) : c ≠ c + 1 := by revert c; decide

theorem zmod2_eq_of_add (a b : ZMod 2) (h : a + b = 0) : a = b := by revert a b; decide

theorem even_iff_sum {n : ℕ} (U : Finset (Fin n)) :
    Even U.card ↔ ∑ _i ∈ U, (1 : ZMod 2) = 0 := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff_even]

theorem sum_symmDiff {n : ℕ} (f : Fin n → ZMod 2) (U V : Finset (Fin n)) :
    ∑ i ∈ symmDiff U V, f i = ∑ i ∈ U, f i + ∑ i ∈ V, f i := by
  have h : ∀ W : Finset (Fin n), ∑ i ∈ W, f i = ∑ i, if i ∈ W then f i else 0 := fun W => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h, h U, h V, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hU : i ∈ U <;> by_cases hV : i ∈ V <;>
    simp [Finset.mem_symmDiff, hU, hV, zmod2_add_self]

theorem sum_const_even {n : ℕ} (x : Fin n → ZMod 2) (U : Finset (Fin n))
    (hc : ∀ a ∈ U, ∀ b ∈ U, x a = x b) (he : Even U.card) : ∑ i ∈ U, x i = 0 := by
  rcases U.eq_empty_or_nonempty with h | ⟨i0, hi0⟩
  · simp [h]
  · rw [Finset.sum_congr rfl (fun i hi => hc i hi i0 hi0), Finset.sum_const, nsmul_eq_mul,
      (ZMod.natCast_eq_zero_iff_even).2 he, zero_mul]

def ES {n : ℕ} (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  S.powerset.filter (fun U => Even U.card)

theorem mem_ES {n : ℕ} (S U : Finset (Fin n)) : U ∈ ES S ↔ U ⊆ S ∧ Even U.card := by
  simp [ES]

theorem char_sum {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ZMod 2) :
    ∑ U ∈ ES S, chi (∑ i ∈ U, x i) =
      if (∀ a ∈ S, ∀ b ∈ S, x a = x b) then ((ES S).card : ℤ) else 0 := by
  split_ifs with h
  · have h1 : ∀ U ∈ ES S, chi (∑ i ∈ U, x i) = 1 := by
      intro U hU
      rw [mem_ES] at hU
      rw [sum_const_even x U (fun a ha b hb => h a (hU.1 ha) b (hU.1 hb)) hU.2]; rfl
    rw [Finset.sum_congr rfl h1]; simp
  · push Not at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have hne : a ≠ b := fun e => hab (by rw [e])
    have hP : ∑ i ∈ ({a, b} : Finset (Fin n)), x i = 1 := by
      rw [Finset.sum_pair hne]; exact zmod2_ne _ _ hab
    have hP1 : ∑ _i ∈ ({a, b} : Finset (Fin n)), (1 : ZMod 2) = 0 := by
      rw [Finset.sum_pair hne]; decide
    apply Finset.sum_involution (fun U _ => symmDiff U {a, b})
    · intro U _
      rw [sum_symmDiff, hP]; exact chi_add_one _
    · intro U _ _ heq
      have h1 := sum_symmDiff x U {a, b}
      rw [heq, hP] at h1
      have h2 := chi_add_one (∑ i ∈ U, x i)
      rw [← h1] at h2
      have h3 := chi_pm (∑ i ∈ U, x i)
      omega
    · intro U _
      exact symmDiff_symmDiff_cancel_right _ _
    · intro U hU
      rw [mem_ES] at hU ⊢
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨hi, _⟩ | ⟨hi, _⟩
        · exact hU.1 hi
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl <;> assumption
      · rw [even_iff_sum, sum_symmDiff, hP1, add_zero, ← even_iff_sum]; exact hU.2

theorem sum_chi_rsum {n m : ℕ} (T : Fin n → Fin m → Bool) (U : Finset (Fin n)) :
    ∑ j : Fin m, chi (rsum T U j) = (m : ℤ) - 2 * (wt T U : ℤ) := by
  rw [wt_eq]
  have h : ∀ j : Fin m, chi (rsum T U j) = 1 - 2 * (if rsum T U j = 1 then (1:ℤ) else 0) := by
    intro j
    rcases zmod2_cases (rsum T U j) with h | h <;> rw [h] <;> decide
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp

theorem phi_eq {n m : ℕ} (S : Finset (Fin n)) (T : Fin n → Fin m → Bool) (y : Fin n → ZMod 2) :
    ∑ j : Fin m, ∑ U ∈ ES S, chi (∑ i ∈ U, (b2z (T i j) + y i)) =
      ∑ U ∈ ES S, chi (∑ i ∈ U, y i) * ((m : ℤ) - 2 * (wt T U : ℤ)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U _
  rw [← sum_chi_rsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_add_distrib, chi_add, mul_comm]; rfl

theorem hit {n m t : ℕ} (A B : Fin n → Fin m → Bool) (S : Finset (Fin n)) (hS : S.card = 2*t+2)
    (hw : ∀ U : Finset (Fin n), Even U.card → U.card ≤ 2*t → wt A U = wt B U)
    (c : ZMod 2) (hAc : ∀ j, rsum A S j = c) (hne : wt A S ≠ wt B S)
    (y : Fin n → ZMod 2) (hy : ∑ i ∈ S, y i = c + 1) :
    ∃ j : Fin m, ∀ a ∈ S, ∀ b ∈ S, b2z (B a j) + y a = b2z (B b j) + y b := by
  by_contra hcon
  push Not at hcon
  have hSe : Even S.card := by rw [hS]; exact ⟨t+1, by ring⟩
  have hSmem : S ∈ ES S := by rw [mem_ES]; exact ⟨subset_rfl, hSe⟩
  have hB0 : ∑ j : Fin m, ∑ U ∈ ES S, chi (∑ i ∈ U, (b2z (B i j) + y i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [char_sum, if_neg]
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hcon j
    exact hab (h a ha b hb)
  have hA0 : ∑ j : Fin m, ∑ U ∈ ES S, chi (∑ i ∈ U, (b2z (A i j) + y i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [char_sum, if_neg]
    intro h
    have h0 := sum_const_even _ S h hSe
    rw [Finset.sum_add_distrib, hy] at h0
    have h1 := hAc j
    unfold rsum at h1
    rw [h1] at h0
    exact zmod2_cc c h0
  rw [phi_eq] at hB0 hA0
  have hdiff : ∑ U ∈ ES S, chi (∑ i ∈ U, y i) *
      (((m : ℤ) - 2 * (wt A U : ℤ)) - ((m : ℤ) - 2 * (wt B U : ℤ))) = 0 := by
    have h1 : ∀ U ∈ ES S, chi (∑ i ∈ U, y i) *
        (((m : ℤ) - 2 * (wt A U : ℤ)) - ((m : ℤ) - 2 * (wt B U : ℤ))) =
        chi (∑ i ∈ U, y i) * ((m : ℤ) - 2 * (wt A U : ℤ)) -
        chi (∑ i ∈ U, y i) * ((m : ℤ) - 2 * (wt B U : ℤ)) := fun U _ => mul_sub _ _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hA0, hB0]; rfl
  rw [Finset.sum_eq_single S] at hdiff
  · have hchi := chi_pm (∑ i ∈ S, y i)
    apply hne
    rcases hchi with h | h <;> rw [h] at hdiff <;> omega
  · intro U hU hUS
    rw [mem_ES] at hU
    have hlt : U.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hU.1, hUS⟩)
    have hle : U.card ≤ 2*t := by obtain ⟨k, hk⟩ := hU.2; omega
    rw [hw U hU.2 hle]; simp
  · intro h; exact absurd hSmem h

theorem necessity {n m t : ℕ} (A B : Fin n → Fin m → Bool) (hA : Cond n m t A)
    (hB : ¬ Cond n m t B)
    (hw : ∀ U : Finset (Fin n), Even U.card → U.card ≤ 2*t → wt A U = wt B U) :
    2*t+2 ≤ n ∧ 2^(2*t)+1 ≤ m := by
  unfold Cond at hB
  push Not at hB
  obtain ⟨S, hS, hBS⟩ := hB
  have hn : 2*t+2 ≤ n := by
    have h := Finset.card_le_univ S
    rw [Fintype.card_fin] at h; omega
  refine ⟨hn, ?_⟩
  obtain ⟨U0, hU0S, hU0ne, hU0e, hU0w⟩ := hA S hS
  have hSe : Even S.card := by rw [hS]; exact ⟨t+1, by ring⟩
  have hU0 : U0 = S := by
    by_contra hne
    have hlt : U0.card < S.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hU0S, hne⟩)
    have hle : U0.card ≤ 2*t := by obtain ⟨k, hk⟩ := hU0e; omega
    have h := hBS U0 hU0S hU0ne hU0e
    rw [← hw U0 hU0e hle] at h
    rcases hU0w with h' | h'
    · exact h.1 h'
    · exact h.2 h'
  rw [hU0] at hU0w
  have hSne : S.Nonempty := by rw [← Finset.card_pos]; omega
  have hBw := hBS S subset_rfl hSne hSe
  have hne : wt A S ≠ wt B S := by
    rcases hU0w with h | h
    · rw [h]; exact fun e => hBw.1 e.symm
    · rw [h]; exact fun e => hBw.2 e.symm
  obtain ⟨c, hAc⟩ : ∃ c : ZMod 2, ∀ j, rsum A S j = c := by
    rw [wt_eq] at hU0w
    rcases hU0w with h | h
    · refine ⟨0, fun j => ?_⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
      have h2 := h (Finset.mem_univ j)
      rcases zmod2_cases (rsum A S j) with h1 | h1
      · exact h1
      · exact absurd h1 h2
    · refine ⟨1, fun j => ?_⟩
      have h' : (Finset.univ.filter (fun j : Fin m => rsum A S j = 1)).card =
          (Finset.univ : Finset (Fin m)).card := by simpa using h
      rw [Finset.card_filter_eq_iff] at h'
      exact h' j (Finset.mem_univ j)
  have hj0 : ∃ j0, rsum B S j0 = c := by
    by_contra hcon
    push Not at hcon
    rcases zmod2_cases c with hc | hc
    · apply hBw.2
      rw [wt_eq]
      have h2 : Finset.univ.filter (fun j : Fin m => rsum B S j = 1) = Finset.univ := by
        rw [Finset.filter_eq_self]
        intro j _
        rcases zmod2_cases (rsum B S j) with h1 | h1
        · exact absurd (h1.trans hc.symm) (hcon j)
        · exact h1
      rw [h2]; simp
    · apply hBw.1
      rw [wt_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h1
      exact hcon j (h1.trans hc.symm)
  obtain ⟨j0, hj0⟩ := hj0
  obtain ⟨i0, hi0, i1, hi1, h01⟩ : ∃ i0 ∈ S, ∃ i1 ∈ S, i0 ≠ i1 :=
    Finset.one_lt_card.1 (by omega)
  have hS'card : ((S.erase i0).erase i1).card = 2*t := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨h01.symm, hi1⟩),
      Finset.card_erase_of_mem hi0]; omega
  have hsurj : Set.SurjOn
      (fun j : Fin m => ((S.erase i0).erase i1).filter
        (fun k => b2z (B k j) + b2z (B i0 j) = 1))
      ↑(Finset.univ.filter (fun j : Fin m => rsum B S j = c + 1))
      ↑((S.erase i0).erase i1).powerset := by
    intro W hW
    rw [Finset.mem_coe, Finset.mem_powerset] at hW
    have hWS : ∀ k ∈ W, k ∈ S ∧ k ≠ i1 ∧ k ≠ i0 := by
      intro k hk
      have h := hW hk
      rw [Finset.mem_erase, Finset.mem_erase] at h
      exact ⟨h.2.2, h.1, h.2.1⟩
    obtain ⟨y, hydef⟩ : ∃ y : Fin n → ZMod 2, y = fun i =>
        if i = i1 then c + 1 + (W.card : ZMod 2) else if i ∈ W then 1 else 0 := ⟨_, rfl⟩
    have hy : ∑ i ∈ S, y i = c + 1 := by
      rw [← Finset.add_sum_erase S y hi1]
      have h1 : y i1 = c + 1 + (W.card : ZMod 2) := by simp [hydef]
      have h2 : ∑ i ∈ S.erase i1, y i = (W.card : ZMod 2) := by
        have h3 : ∀ i ∈ S.erase i1, y i = if i ∈ W then 1 else 0 := by
          intro i hi; simp [hydef, Finset.ne_of_mem_erase hi]
        have h4 : S.erase i1 ∩ W = W := by
          rw [Finset.inter_eq_right]
          intro k hk
          exact Finset.mem_erase.2 ⟨(hWS k hk).2.1, (hWS k hk).1⟩
        rw [Finset.sum_congr rfl h3, Finset.sum_ite_mem, h4, Finset.sum_const, nsmul_eq_mul,
          mul_one]
      rw [h1, h2, add_assoc, zmod2_add_self, add_zero]
    obtain ⟨j, hj⟩ := hit A B S hS hw c hAc hne y hy
    have hi0W : i0 ∉ W := fun h => (hWS i0 h).2.2 rfl
    have hy0 : y i0 = 0 := by simp [hydef, h01, hi0W]
    refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      have h0 := sum_const_even _ S hj hSe
      rw [Finset.sum_add_distrib, hy] at h0
      exact zmod2_eq_of_add _ _ h0
    · ext k
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hk, hk1⟩
        rw [Finset.mem_erase, Finset.mem_erase] at hk
        have h := hj k hk.2.2 i0 hi0
        rw [hy0, add_zero] at h
        have hyk := zmod2_move _ _ _ h
        rw [hk1] at hyk
        by_contra hkW
        simp [hydef, hk.1, hkW] at hyk
      · intro hkW
        refine ⟨hW hkW, ?_⟩
        have h := hj k (hWS k hkW).1 i0 hi0
        rw [hy0, add_zero] at h
        rw [zmod2_move _ _ _ h]
        simp [hydef, (hWS k hkW).2.1, hkW]
  have hcard := Finset.card_le_card_of_surjOn _ hsurj
  rw [Finset.card_powerset, hS'card] at hcard
  have hJ : (Finset.univ.filter (fun j : Fin m => rsum B S j = c + 1)) ⊆
      Finset.univ.erase j0 := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_erase]
    refine ⟨fun e => ?_, Finset.mem_univ j⟩
    rw [e, hj0] at hj
    exact zmod2_cc' c hj.2
  have h5 := Finset.card_le_card hJ
  rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin] at h5
  have hm : 0 < m := Fin.pos j0
  omega

theorem fits_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (t : ℕ) (T : Fin n → Fin m → Bool) :
    (∃ C : Circuit,
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents T C ∧
        (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
        C.gates.countP nlGate ≤ t) ↔ Cond n m t T := by
  rw [← rank_iff_cond t T ⟨0, hn⟩ ⟨0, hm⟩, main n m T ⟨0, hn⟩ ⟨0, hm⟩ t]
  constructor
  · rintro ⟨C, h1, h2, h3, h4, h5⟩
    exact ⟨C, ⟨h1, h2, h3⟩, h4, h5⟩
  · rintro ⟨C, ⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨C, h1, h2, h3, h4, h5⟩

end PEqualNP.Outside.L_meta_33600

theorem PEqualNP.Outside.L_meta_33600 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (n m t : ℕ) (_ : 0 < n) (_ : 0 < m),
  let weight := fun (T : Fin n → Fin m → Bool) (U : Finset (Fin n)) =>
    (Finset.univ.filter (fun j : Fin m => (U.sum (fun i => (T i j).toNat)) % 2 = 1)).card
  let fits := fun (T : Fin n → Fin m → Bool) =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
      PEqualNP.Represents.Represents T C ∧ depth (n+m) C ≤ 1 ∧ C.gates.countP nonlinear ≤ t
  (∀ T, fits T ↔ ∀ S : Finset (Fin n), S.card = 2*t+2 →
    ∃ U : Finset (Fin n), U ⊆ S ∧ U.Nonempty ∧ Even U.card ∧
      (weight T U = 0 ∨ weight T U = m)) ∧
  ((∃ A B : Fin n → Fin m → Bool, fits A ∧ (¬ fits B) ∧
    ∀ U : Finset (Fin n), Even U.card → U.card ≤ 2*t → weight A U = weight B U) ↔
    2*t+2 ≤ n ∧ 2^(2*t)+1 ≤ m)) := by
  intro nonlinear depth n m t hn hm weight fits
  have hf : ∀ T, fits T ↔ PEqualNP.Outside.L_meta_33600.Cond n m t T :=
    fun T => PEqualNP.Outside.L_meta_33600.fits_iff hn hm t T
  refine ⟨hf, ?_⟩
  constructor
  · rintro ⟨A, B, hA, hB, hw⟩
    exact PEqualNP.Outside.L_meta_33600.necessity A B ((hf A).1 hA) (fun h => hB ((hf B).2 h)) hw
  · rintro ⟨h1, h2⟩
    obtain ⟨A, B, hA, hB, hw⟩ := PEqualNP.Outside.L_meta_33600.construct (t := t) h1 h2
    exact ⟨A, B, (hf A).2 hA, fun h => hB ((hf B).1 h), hw⟩
