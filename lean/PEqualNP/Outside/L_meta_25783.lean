import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25783_aux.Work.Ranks

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

end PEqualNP.Outside.L_meta_25783_aux.Work.Ranks
namespace PEqualNP.Outside.L_meta_25783_aux.Work.Sampling
open Matrix
theorem had_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (v : Fin n → ℝ) :
    ∑ j, (∑ i, v i * H i j) ^ 2 = n * ∑ i, v i ^ 2 := by
  calc ∑ j, (∑ i, v i * H i j) ^ 2 = ∑ j, ∑ i, ∑ k, (v i * v k) * (H i j * H k j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sq, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ i, ∑ k, (v i * v k) * ∑ j, H i j * H k j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
    _ = n * ∑ i, v i ^ 2 := by
        simp only [hH, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem col_orth {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) :
    ∀ c d, (∑ i, Hᵀ c i * Hᵀ d i) = if c = d then (n : ℝ) else 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : H * ((1 / (n : ℝ)) • Hᵀ) = 1 := by
    ext i j
    have e : (H * ((1 / (n : ℝ)) • Hᵀ)) i j = (∑ c, H i c * H j c) / n := by
      simp only [Matrix.mul_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [e, hH, Matrix.one_apply]
    split_ifs <;> simp [hn']
  have h2 : ((1 / (n : ℝ)) • Hᵀ) * H = 1 := mul_eq_one_comm.1 h1
  intro c d
  have e : (((1 / (n : ℝ)) • Hᵀ) * H) c d = (∑ i, H i c * H i d) / n := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h2, Matrix.one_apply, eq_div_iff hn'] at e
  simp only [transpose_apply]
  split_ifs at e ⊢ <;> linarith


theorem incidence : ∀ (m n : ℕ) (E : Fin m → Fin n → Bool) (a b : Fin m) (c d : Fin n),
  ((Finset.univ : Finset (Fin n)).filter (fun j => E a j ≠ E b j)).card +
    ((Finset.univ : Finset (Fin m)).filter (fun i => E i c ≠ E i d)).card ≤
    ((Finset.univ : Finset (Fin m × Fin n)).filter (fun z => E z.1 z.2 = true)).card + 2 := by
  classical
  intro m n E a b c d
  let A := Finset.univ.filter (fun j => E a j ≠ E b j)
  let B := Finset.univ.filter (fun i => E i c ≠ E i d)
  let C : Finset (Fin n) := {c,d}
  let T := (Finset.univ : Finset (Fin m × Fin n)).filter (fun z => E z.1 z.2 = true)
  let f (j : Fin n) : Fin m × Fin n := (if E a j then a else b,j)
  let g (i : Fin m) : Fin m × Fin n := (i,if E i c then c else d)
  let X := (A \ C).image f
  let Y := B.image g
  have hf : Function.Injective f := fun _ _ e => congrArg Prod.snd e
  have hg : Function.Injective g := fun _ _ e => congrArg Prod.fst e
  have dis : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hx hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi,h⟩ := Finset.mem_image.mp hy
    have pr := congrArg Prod.snd h
    have outside := (Finset.mem_sdiff.mp hj).2
    by_cases e : E i c = true
    · have eq : c = j := by simpa [g,f,e] using pr
      exact outside (by simp [C,← eq])
    · have eq : d = j := by simpa [g,f,e] using pr
      exact outside (by simp [C,← eq])
  have sub : X ∪ Y ⊆ T := by
    intro z hz
    rcases Finset.mem_union.mp hz with hx|hy
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      have diff := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
      cases ha : E a j <;> cases hb : E b j <;> simp_all [f,T]
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
      have diff := (Finset.mem_filter.mp hi).2
      cases hc : E i c <;> cases hd : E i d <;> simp_all [g,T]
  have lim := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at lim
  change ((A \ C).image f).card + (B.image g).card ≤ T.card at lim
  rw [Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ hg] at lim
  have split := Finset.card_sdiff_add_card_inter A C
  have small := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := C))
  have atmost : C.card ≤ 2 := by
    calc
      C.card ≤ ({d} : Finset (Fin n)).card+1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  change A.card + B.card ≤ T.card + 2
  omega

abbrev T (n : ℕ) := Fin n → Fin n → Bool
abbrev V (n : ℕ) := Fin n → Bool
def bit (a b : Bool) : ℕ := if a = b then 0 else 1
def dist {n} (a b : V n) := ∑ j, bit (a j) (b j)
def err {n} (A B : T n) := ∑ i, dist (A i) (B i)
def Had {n} (A : T n) := ∀ i j, i ≠ j → 2 * dist (A i) (A j) = n
def sam {n} (D : T n) (r c : Fin n → Fin n) (u v : V n) : T n :=
  fun i j => xor (xor (u i) (v j)) (D (r i) (c j))
def copy {n} (A B : T n) := ∃ i j, i ≠ j ∧ ∃ flip : Bool,
    ∀ x y, B x y = if x = i then xor flip (A j y) else A x y
def equivT {n} (H D : T n) := ∃ (f g : Equiv.Perm (Fin n)) (a b : V n), H = sam D f g a b
def signR (a : Bool) : ℝ := if a then -1 else 1
def M {n} (A : T n) : Matrix (Fin n) (Fin n) ℝ := fun i j => signR (A i j)
def dot {n} (a b : V n) : ℝ := ∑ j, signR (a j) * signR (b j)
def flipV {n} (u : Bool) (a : V n) : V n := fun j => xor u (a j)
theorem dist_card {n} (a b : V n) : dist a b = (Finset.univ.filter (fun j => a j ≠ b j)).card := by
  unfold dist bit
  trans ∑ j, if a j ≠ b j then 1 else 0
  swap
  · simp only [Finset.sum_boole,Nat.cast_id]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all
theorem dist_zero {n} {a b : V n} : dist a b = 0 ↔ a = b := by
  rw [dist_card]
  simp [funext_iff]
theorem dist_le {n} (a b : V n) : dist a b ≤ n := by
  rw [dist_card]; simpa using Finset.card_le_univ (Finset.univ.filter (fun j => a j ≠ b j))
theorem dot_dist {n} (a b : V n) : dot a b = n - 2 * (dist a b : ℝ) := by
  simp only [dot,dist,Nat.cast_sum,Finset.mul_sum]
  have h : ∀ j, signR (a j) * signR (b j) = 1 - 2 * (bit (a j) (b j) : ℝ) := by
    intro j; cases a j <;> cases b j <;> norm_num [signR,bit]
  simp [h, Finset.sum_sub_distrib]
theorem dot_flip {n} (a b : V n) (u : Bool) : dot (flipV u a) b = signR u * dot a b := by
  simp only [dot,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _; cases u <;> cases ha : a j <;> simp [flipV,ha,signR]
theorem dot_comm' {n} (a b : V n) : dot a b = dot b a := by simp [dot,mul_comm]
theorem had_orth {n} (H : T n) : Had H ↔ ∀ i j, dot (H i) (H j) = if i=j then (n:ℝ) else 0 := by
  constructor
  · intro hh i j
    rw [dot_dist]
    split_ifs with e
    · rw [e,(dist_zero.mpr rfl)]; simp
    · have h : (2:ℝ) * (dist (H i) (H j):ℝ) = n := by exact_mod_cast hh i j e
      linarith
  · intro hh i j h
    have eq := hh i j
    rw [dot_dist, if_neg h] at eq
    exact_mod_cast (show (2:ℝ) * (dist (H i) (H j):ℝ) = n by linarith)
theorem had_swap {n} {H : T n} (hn : 0<n) (hh : Had H) : Had (Function.swap H) := by
  exact (had_orth _).mpr (col_orth (M H) hn ((had_orth _).mp hh))
theorem err_swap {n} (H K : T n) : err (Function.swap H) (Function.swap K) = err H K := by
  exact Finset.sum_comm
theorem flip_dist {n} {H : T n} (hh : Had H) {i j} (hij : i≠j) (u : Bool) :
    2 * dist (H i) (flipV u (H j)) = n := by
  have e := (had_orth _).mp hh j i
  rw [if_neg hij.symm] at e
  have z := dot_dist (H i) (flipV u (H j))
  rw [dot_comm',dot_flip,e,mul_zero] at z
  exact_mod_cast (show (2:ℝ)*(dist (H i) (flipV u (H j)):ℝ)=n by linarith)
theorem pars {n} {H : T n} (hn : 0<n) (hh : Had H) (w : Fin n → ℝ) :
    ∑ i, (∑ j, w j * signR (H i j))^2 = n * ∑ j,w j^2 :=
  had_sum (M (Function.swap H)) ((had_orth _).mp (had_swap hn hh)) w
theorem bool_xors (a b c : Bool) : xor a (xor b c) = xor (xor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl
theorem flip2 {n} (u : Bool) (a : V n) : flipV u (flipV u a) = a := by
  funext j; cases u <;> cases ha : a j <;> simp [flipV,ha]
theorem flip_cancel {n} (u : Bool) (a b : V n) (h : flipV u a = flipV u b) : a = b := by
  simpa only [flip2] using congrArg (flipV u) h
theorem err_prod {n} (H K : T n) :
    err H K = (Finset.univ.filter (fun z : Fin n × Fin n => xor (H z.1 z.2) (K z.1 z.2) = true)).card := by
  trans ∑ z : Fin n × Fin n, if xor (H z.1 z.2) (K z.1 z.2) = true then 1 else 0
  swap
  · simp only [Finset.sum_boole,Nat.cast_id]
  rw [Fintype.sum_prod_type]
  unfold err dist
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases H i j <;> cases K i j <;> rfl


theorem uncertainty {n} (hn : 0<n) {H : T n} (hh : Had H) (a b : V n)
    (S : Finset (Fin n)) (hab : a ≠ b)
    (hz : ∀ i, i ∉ S → dot a (H i) = dot b (H i)) :
    n ≤ S.card * dist a b := by
  classical
  let w (j : Fin n) := (signR (a j) - signR (b j))/2
  let z (i : Fin n) := ∑ j, w j * signR (H i j)
  let e := dist a b
  have he : 0 < e := Nat.pos_of_ne_zero (fun h => hab (dist_zero.mp h))
  have w2 (j : Fin n) : (w j)^2 = (bit (a j) (b j):ℝ) := by
    cases ha : a j <;> cases hb : b j <;> norm_num [w,ha,hb,bit,signR]
  have wp (j i : Fin n) : |w j * signR (H i j)| = (bit (a j) (b j):ℝ) := by
    cases ha : a j <;> cases hb : b j <;> cases hc : H i j <;> norm_num [w,ha,hb,hc,bit,signR]
  have m (i : Fin n) : |z i| ≤ (e:ℝ) := by
    calc
      |z i| ≤ ∑ j, |w j * signR (H i j)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp [wp,e,dist]
  have z0 (i : Fin n) (hi : i ∉ S) : z i = 0 := by
    have h : 2*z i = dot a (H i) - dot b (H i) := by
      simp only [z,dot,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _; dsimp only [w]; ring
    rw [hz i hi] at h; linarith
  have squares : ∑ i, (z i)^2 ≤ ∑ i : Fin n, if i ∈ S then (e:ℝ)^2 else 0 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · rw [← sq_abs (z i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (m i) 2
    · simp [z0 i h]
  have eq := pars hn hh w
  change (∑ i, (z i)^2) = _ at eq
  simp only [w2,← Nat.cast_sum] at eq
  rw [eq,Finset.sum_ite] at squares
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,Finset.sum_const_zero,add_zero,
    nsmul_eq_mul,mul_zero] at squares
  change (n:ℝ) * e ≤ S.card * (e:ℝ)^2 at squares
  have pos : (0:ℝ) < e := by exact_mod_cast he
  have cap : (n:ℝ) ≤ (S.card:ℝ)*e := by
    by_contra! bad
    have := mul_lt_mul_of_pos_right bad pos
    nlinarith
  exact_mod_cast cap

theorem d_flip_bool {n} (A B : V n) (f : Bool) :
    dist A (flipV f B) = if f then n - dist A B else dist A B := by
  cases f
  · have z : flipV false B = B := by funext j; simp [flipV]
    rw [z]; rfl
  · simp only [Bool.true_eq,ite_true]
    have sum : dist A (flipV true B) + dist A B = n := by
      unfold dist
      rw [← Finset.sum_add_distrib]
      have per (j : Fin n) : bit (A j) (flipV true B j) + bit (A j) (B j) = 1 := by
        cases ha : A j <;> cases hb : B j <;> simp [flipV,ha,hb,bit]
      simp [per]
    omega
theorem xor_err_same {n} (a b x y : V n) (f : Bool) (h : y = flipV f x) :
    dist (fun j => xor (a j) (x j)) (fun j => xor (b j) (y j)) = dist a (flipV f b) := by
  subst y
  apply Finset.sum_congr rfl
  intro j _
  cases f <;> cases ha : a j <;> cases hb : b j <;> cases hx : x j <;> simp [flipV,ha,hb,hx,bit]
theorem sam_row {n} (D : T n) (r c : Fin n → Fin n) (u v : V n) {i j} (h : r i = r j) :
    sam D r c u v j = flipV (xor (u i) (u j)) (sam D r c u v i) := by
  funext k
  dsimp only [sam,flipV]
  rw [h]
  cases u i <;> cases u j <;> cases v k <;> cases D (r j) (c k) <;> rfl
theorem sam_swap {n} (D : T n) (r c : Fin n → Fin n) (u v : V n) :
    Function.swap (sam D r c u v) = sam (Function.swap D) c r v u := by
  funext i j
  simp [sam,Function.swap,Bool.xor_comm (u j) (v i)]
theorem double_bound {n} (hn : 0<n) {H : T n} (hh : Had H) (D : T n)
    (r c : Fin n → Fin n) (u v : V n) (hr : ¬Function.Injective r) (hc : ¬Function.Injective c) :
    n ≤ err H (sam D r c u v) + 2 := by
  classical
  simp only [Function.Injective] at hr hc
  push_neg at hr hc
  obtain ⟨a,b,e,ne⟩ := hr
  obtain ⟨k,l,ec,nc⟩ := hc
  let K := sam D r c u v
  let E : T n := fun i j => xor (H i j) (K i j)
  have ri := xor_err_same (H a) (H b) (K a) (K b) _ (sam_row D r c u v e)
  have cpy : Function.swap K l = flipV (xor (v k) (v l)) (Function.swap K k) := by
    dsimp only [K]
    rw [sam_swap]; exact sam_row _ _ _ _ _ ec
  have ci := xor_err_same (Function.swap H k) (Function.swap H l) (Function.swap K k) (Function.swap K l) _ cpy
  have rd := flip_dist hh ne (xor (u a) (u b))
  have cd := flip_dist (had_swap hn hh) nc (xor (v k) (v l))
  rw [←ri] at rd
  rw [←ci] at cd
  change 2 * dist (E a) (E b) = n at rd
  change 2 * dist (Function.swap E k) (Function.swap E l) = n at cd
  rw [dist_card] at rd cd
  have bound := incidence n n E a b k l
  rw [err_prod]
  change n ≤ (Finset.univ.filter (fun z : Fin n × Fin n => E z.1 z.2 = true)).card + 2
  change 2 * (Finset.univ.filter (fun i => E i k ≠ E i l)).card = n at cd
  omega
theorem row_had_signed {n} {D : T n} (hd : Had D) (g : Equiv.Perm (Fin n)) (v : V n) :
    Had (fun i j => xor (v j) (D i (g j))) := by
  intro i j ne
  have h : dist (fun k => xor (v k) (D i (g k))) (fun k => xor (v k) (D j (g k))) =
      dist (D i) (D j) := by
    unfold dist
    rw [← Equiv.sum_comp g (fun k => bit (D i k) (D j k))]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only
    cases v k <;> cases D i (g k) <;> cases D j (g k) <;> rfl
  exact h ▸ hd i j ne


theorem single_bank {n} (hn : 0<n) {H B : T n} (hh : Had H) (hb : Had B)
    (r : Fin n → Fin n) (u : V n) (K : T n)
    (defK : ∀ i, K i = flipV (u i) (B (r i))) (small : err H K < n) :
    (∃ (f : Equiv.Perm (Fin n)) (a : V n), ∀ i, H i = flipV (a i) (B (f i))) ∧
    (err H K = 0 ∨ (2 * err H K = n ∧ copy H K)) := by
  classical
  let S := Finset.univ.filter fun i => H i ≠ K i
  have outside (i : Fin n) (hi : i ∉ S) : H i = K i := by simpa [S] using hi
  have sameType (i j : Fin n) (ij : r i = r j) : K i = flipV (xor (u i) (u j)) (K j) := by
    rw [defK i,defK j,ij]
    funext x
    cases u i <;> cases u j <;> cases h : B (r j) x <;> simp [flipV,h]
  have distinct (i j : Fin n) (hi : i∉S) (hj : j∉S) (ij : i ≠ j) : r i ≠ r j := by
    intro eq
    have cp := sameType i j eq
    rw [←outside i hi,←outside j hj] at cp
    have q := flip_dist hh ij (xor (u i) (u j))
    rw [←cp,dist_zero.mpr rfl] at q
    omega
  have perp (i j : Fin n) (ne : r i ≠ r j) : dot (K i) (K j) = 0 := by
    rw [defK i,defK j,dot_flip,dot_comm',dot_flip,(had_orth _).mp hb,if_neg ne.symm]
    ring
  have few : S.card ≤ 1 := by
    by_contra! many
    have per (i : Fin n) (hi : i ∈ S) : n ≤ S.card * dist (H i) (K i) := by
      by_cases reused : ∃ j, j ∉ S ∧ r i = r j
      · obtain ⟨j,hj,eq⟩ := reused
        have ne : i ≠ j := fun e => hj (e ▸ hi)
        have cp := sameType i j eq
        rw [←outside j hj] at cp
        have cost := flip_dist hh ne (xor (u i) (u j))
        rw [←cp] at cost
        exact (le_of_eq cost.symm).trans (Nat.mul_le_mul_right _ many)
      · apply uncertainty hn hh (H i) (K i) S (Finset.mem_filter.mp hi).2
        intro j hj
        have ne : i ≠ j := fun e => hj (e ▸ hi)
        rw [(had_orth _).mp hh,if_neg ne,outside j hj,perp]
        exact fun eq => reused ⟨j,hj,eq⟩
    have p := Finset.sum_le_sum per
    have bound : (∑ i ∈ S, dist (H i) (K i)) ≤ err H K :=
      Finset.sum_le_univ_sum_of_nonneg (fun i => Nat.zero_le _)
    have pos : 0 < S.card := by omega
    simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at p
    have := Nat.le_of_mul_le_mul_left (p.trans (Nat.mul_le_mul_left _ bound)) pos
    omega
  by_cases empty : S=∅
  · have out (i : Fin n) : i ∉ S := by simp [empty]
    have inj : Function.Injective r := by
      intro i j eq; by_contra ne; exact distinct i j (out i) (out j) ne eq
    refine ⟨⟨Equiv.ofBijective _ ((Finite.injective_iff_bijective).mp inj),u,fun i => (outside i (out i)).trans (defK i)⟩,Or.inl ?_⟩
    unfold err
    simp [fun i => dist_zero.mpr (outside i (out i))]
  obtain ⟨i,hs⟩ := Finset.card_eq_one.mp (show S.card = 1 by
    have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty); omega)
  have unchanged (j : Fin n) (ne : j ≠ i) : H j = K j := outside j (by simpa [hs] using ne)
  have changed : H i ≠ K i := (Finset.mem_filter.mp (show i ∈ S by simp [hs])).2
  have sumE : err H K = dist (H i) (K i) := by
    unfold err
    apply Finset.sum_eq_single i
    · intro j _ ne; exact dist_zero.mpr (unchanged j ne)
    · simp
  have reused : ∃ j, j ≠ i ∧ r i = r j := by
    by_contra denied
    have q := uncertainty hn hh (H i) (K i) S changed (by
      intro j hj
      have ne : i ≠ j := by simpa [hs,ne_comm] using hj
      rw [(had_orth _).mp hh,if_neg ne,outside j hj,perp]
      exact fun eq => denied ⟨j,ne.symm,eq⟩)
    rw [hs,Finset.card_singleton,one_mul,←sumE] at q; omega
  obtain ⟨j,hj,eq⟩ := reused
  have cp := sameType i j eq
  rw [←unchanged j hj] at cp
  constructor
  · let A := (Finset.univ.erase i).image r
    have ca : A.card < n := by
      have ub := Finset.card_image_le (s := Finset.univ.erase i) (f := r)
      have eqn := Finset.card_erase_add_one (Finset.mem_univ i)
      simp only [Finset.card_univ,Fintype.card_fin] at eqn
      change A.card ≤ (Finset.univ.erase i).card at ub
      omega
    obtain ⟨t,ht⟩ : ∃ t, t ∉ A := by
      by_contra! full
      have : A = Finset.univ := Finset.eq_univ_of_forall full
      simp [this] at ca
    have missed (j : Fin n) (ne : j ≠ i) : r j ≠ t := fun e =>
      ht (Finset.mem_image.mpr ⟨j,Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩,e⟩)
    let f (j : Fin n) := if j=i then t else r j
    have fi : Function.Injective f := by
      intro a b e
      by_cases ha : a=i <;> by_cases hbb : b=i
      · exact ha.trans hbb.symm
      · exact False.elim ((missed b hbb) (by simpa [f,ha,hbb] using e.symm))
      · exact False.elim ((missed a ha) (by simpa [f,ha,hbb] using e))
      · by_contra ne
        exact distinct a b (by simpa [hs] using ha) (by simpa [hs] using hbb) ne (by simpa [f,ha,hbb] using e)
    have orth (j : Fin n) (ne : j ≠ i) : dot (B t) (H j) = 0 := by
      rw [unchanged j ne,defK j,dot_comm',dot_flip,(had_orth _).mp hb,if_neg (missed j ne),mul_zero]
    have ps := pars hn hh (fun x => signR (B t x))
    change (∑ k, (dot (B t) (H k))^2) = _ at ps
    have oneTerm := Finset.sum_eq_single (s := Finset.univ) (f := fun k => (dot (B t) (H k))^2) i
        (fun k _ ne => by simp [orth k ne]) (by simp)
    rw [oneTerm] at ps
    have sq1 (x : Fin n) : signR (B t x)^2 = 1 := by cases h : B t x <;> norm_num [signR,h]
    simp only [sq1,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at ps
    rw [dot_comm',dot_dist] at ps
    have alt : dist (H i) (B t) = 0 ∨ dist (H i) (B t) = n := by
      have p : ((dist (H i) (B t):ℝ))*((dist (H i) (B t):ℝ))-n*((dist (H i) (B t):ℝ))=0 := by nlinarith
      have q : ((dist (H i) (B t):ℝ))*((dist (H i) (B t):ℝ)-n)=0 := by nlinarith
      rcases mul_eq_zero.mp q with z|z
      · exact Or.inl (by exact_mod_cast z)
      · exact Or.inr (by exact_mod_cast sub_eq_zero.mp z)
    obtain ⟨sg,sign_ok⟩ : ∃ sg, H i = flipV sg (B t) := by
      rcases alt with z|z
      · refine ⟨false,?_⟩
        rw [dist_zero.mp z]; funext x; simp [flipV]
      · exact ⟨true,dist_zero.mp (by rw [d_flip_bool,z]; simp)⟩
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi),fun k => if k=i then sg else u k,?_⟩
    intro k
    change H k = flipV _ (B (f k))
    by_cases e : k=i
    · simpa [f,e] using sign_ok
    · simpa [f,e] using (unchanged k e).trans (defK k)
  · right
    constructor
    · rw [sumE,cp]; exact flip_dist hh hj.symm _
    · refine ⟨i,j,hj.symm,xor (u i) (u j),?_⟩
      intro x y
      by_cases hx : x=i
      · subst x; rw [if_pos rfl]; exact congrFun cp y
      · simpa [hx] using congrFun (unchanged x hx).symm y


theorem attained {n} (hn : 8 ≤ n) {H : T n} (hh : Had H) :
    ∃ (r c : Fin n → Fin n) (u v : V n), ¬Function.Injective r ∧ ¬Function.Injective c ∧
      err H (sam H r c u v) + 2 = n := by
  classical
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have ne : a ≠ b := fun e => by have h := congrArg Fin.val e; change 0=1 at h; omega
  let S := Finset.univ.filter fun j => H a j ≠ H b j
  have card := hh a b ne
  rw [dist_card] at card
  change 2*S.card=n at card
  obtain ⟨c,hc,d,hd,cd⟩ := Finset.one_lt_card.mp (show 1<S.card by omega)
  have xc := (Finset.mem_filter.mp hc).2
  have xd := (Finset.mem_filter.mp hd).2
  let s := !(xor (H a c) (H a d))
  let r (i : Fin n) := if i=a then b else i
  let g (j : Fin n) := if j=c then d else j
  let v (j : Fin n) := if j=c then s else false
  let K := sam H r g (fun _ => false) v
  refine ⟨r,g,(fun _ => false),v,fun inj => ne (inj (by simp [r,ne.symm])),
    fun inj => cd (inj (by simp [g,cd.symm])),?_⟩
  have pt (i j : Fin n) :
      bit (H i j) (K i j) + (if i=a ∧ j=c then 2 else 0) =
         (if i=a then bit (H a j) (H b j) else 0) +
         (if j=c then bit (H i c) (flipV s (Function.swap H d) i) else 0) := by
    by_cases eqi : i=a <;> by_cases eqj : j=c
    · subst i; subst j
      cases hac : H a c <;> cases hbc : H b c <;> cases had : H a d <;> cases hbd : H b d <;>
        simp_all [K,sam,r,g,v,s,flipV,Function.swap,bit]
    · subst i; simp [K,sam,r,g,v,eqj,bit]
    · subst j; simp [K,sam,r,g,v,eqi,flipV,Function.swap,bit] <;> rfl
    · simp [K,sam,r,g,v,eqi,eqj,bit]
  have eqs := congrArg (fun f : Fin n → Fin n → ℕ => ∑ i,∑ j, f i j) (funext fun i => funext (pt i))
  simp only [Finset.sum_add_distrib] at eqs
  have dbl : (∑ i : Fin n, ∑ j : Fin n, if i=a ∧ j=c then 2 else 0) = 2 := by
    simp only [ite_and]; simp
  have rows : (∑ i : Fin n, ∑ j : Fin n, if i=a then bit (H a j) (H b j) else 0) = dist (H a) (H b) := by
    rw [Finset.sum_comm]; simp [dist]
  have cols : (∑ i : Fin n, ∑ j : Fin n, if j=c then bit (H i c) (flipV s (Function.swap H d) i) else 0)
      = dist (Function.swap H c) (flipV s (Function.swap H d)) := by simp [dist,Function.swap]
  change err H K + _ = _ at eqs
  rw [dbl,rows,cols] at eqs
  have cr := hh a b ne
  have cc := flip_dist (had_swap (by omega) hh) cd s
  change err H K + 2 = n
  omega
theorem oriented {n} (hn : 0<n) {H D : T n} (hh : Had H) (hd : Had D)
    (r c : Fin n → Fin n) (u v : V n) (hc : Function.Injective c) (small : err H (sam D r c u v)<n) :
    equivT H D ∧ (err H (sam D r c u v) = 0 ∨ 2*err H (sam D r c u v)=n ∧ copy H (sam D r c u v)) := by
  let g : Equiv.Perm (Fin n) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc)
  let B : T n := fun i j => xor (v j) (D i (g j))
  have k (i : Fin n) : sam D r c u v i = flipV (u i) (B (r i)) := by
    funext j; exact (bool_xors (u i) (v j) (D (r i) (c j))).symm
  obtain ⟨⟨f,a,eq⟩,rest⟩ := single_bank hn hh (row_had_signed hd g v) r u _ k small
  refine ⟨⟨f,g,a,v,?_⟩,rest⟩
  funext i j
  exact (congrFun (eq i) j).trans (bool_xors _ _ _)
theorem unswap {n} {H D : T n} (e : equivT (Function.swap H) (Function.swap D)) : equivT H D := by
  obtain ⟨f,g,a,b,eq⟩ := e
  refine ⟨g,f,b,a,?_⟩
  have z := congrArg Function.swap eq
  rw [sam_swap] at z
  exact z


end PEqualNP.Outside.L_meta_25783_aux.Work.Sampling


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open CircuitLowerBounds Represents
open MetaComplexity.NestedCover
open Ranks Sampling
abbrev V2 (s : ℕ) := Fin (2*s) → ZMod 2
def predT {n s} (r c : Fin n → V2 s) (u v : V n) : T n :=
  fun i j => xor (xor (u i) (v j)) (decide ((∑ k, r i k*c j k)=1))
def valid2 (n s : ℕ) (C : Circuit) := (∀ g∈C.gates, g.inputs.length ≤ 2) ∧
  ReadsBack (n+n) C ∧ C.gates.countP nlGate ≤ s
theorem bit_dec (z : ZMod 2) : b2z (decide (z=1))=z := by revert z; decide
theorem sampled_implementation {n s} (hn : 0<n) (r c : Fin n → V2 s) (u v : V n) :
    ∃ C, valid2 n s C ∧ Represents (predT r c u v) C := by
  classical
  let o : Fin n := ⟨0,hn⟩
  let P : Matrix (Fin n) (Fin (2*s)) (ZMod 2) := fun i k => r i k + r o k
  let Q : Matrix (Fin (2*s)) (Fin n) (ZMod 2) := fun k j => c j k + c o k
  have factor : anchor o o (fun i j => b2z (predT r c u v i j))=P*Q := by
    ext i j
    change b2z (predT r c u v i j) + b2z (predT r c u v i o) + b2z (predT r c u v o j) + b2z (predT r c u v o o) = ∑ k, (r i k+r o k)*(c j k+c o k)
    simp only [predT,b2z_xor,bit_dec]
    simp only [add_mul,mul_add,Finset.sum_add_distrib]
    have z (x y a b d e f g : ZMod 2) :
      x+y+d+(x+b+e)+(a+y+f)+(a+b+g)=d+e+(f+g) := by
      linear_combination zmod2_add_self x + zmod2_add_self y + zmod2_add_self a + zmod2_add_self b
    rw [z]
    ring
  have cap := rank_of_factor P Q
  rw [←factor] at cap
  obtain ⟨C,⟨ar,rb,rep⟩,_,ct⟩ := dir_ge (predT r c u v) o o s cap
  exact ⟨C,⟨ar,rb,ct⟩,rep⟩
theorem reindex {n s} (r c : Fin n → V2 s) (u v : V n) (f g : Fin n→Fin n) (a b : V n) :
  sam (predT r c u v) f g a b = predT (r ∘ f) (c ∘ g) (fun i => xor (a i) (u (f i))) (fun j => xor (b j) (v (g j))) := by
  funext i j
  dsimp only [sam,predT,Function.comp_apply]
  cases a i <;> cases b j <;> cases u (f i) <;> cases v (g j) <;> simp
theorem attainBoth {n s} (hn : 8≤n) {H : T n} (hh : Had H)
    (r c : Fin n → V2 s) (u v : V n) (model : H=predT r c u v) :
    (∃ C, valid2 n s C ∧ 2 * err H (fun i j => C.eval (oneEach i j))=n) ∧
    (∃ C, valid2 n s C ∧ err H (fun i j => C.eval (oneEach i j))+2=n) := by
  have impl (f g : Fin n→Fin n) (a b : V n) : ∃ C, valid2 n s C ∧ Represents (sam H f g a b) C := by
    rw [model,reindex]; exact sampled_implementation (by omega) _ _ _ _
  constructor
  · let a : Fin n := ⟨0,by omega⟩
    let b : Fin n := ⟨1,by omega⟩
    have ne : a ≠ b := fun e => by have h := congrArg Fin.val e; change 0=1 at h; omega
    let f := fun x : Fin n => if x=a then b else x
    obtain ⟨C,hc,rep⟩ := impl f id (fun _ => false) (fun _ => false)
    refine ⟨C,hc,?_⟩
    have eq : (fun i j => C.eval (oneEach i j)) = fun i => H (f i) := by funext i j; exact (rep i j).trans (by simp [sam])
    rw [eq]
    have total : err H (fun i => H (f i)) = dist (H a) (H b) := by
      unfold err
      rw [Finset.sum_eq_single a]
      · simp [f]
      · intro x _ nx; simp [f,nx,dist_zero]
      · simp
    rw [total]; exact hh a b ne
  · obtain ⟨f,g,a,b,_,_,eq⟩ := attained hn hh
    obtain ⟨C,hc,rep⟩ := impl f g a b
    refine ⟨C,hc,?_⟩
    rw [show (fun i j => C.eval (oneEach i j))=sam H f g a b from funext (fun i => funext (rep i))]
    exact eq
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work.Projection

open Matrix

noncomputable def row {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => M i j)

theorem proj_ratio {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    (x a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ V) :
    (inner ℝ x a) ^ 2 / ‖a‖ ^ 2 ≤ ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x) ^ 2 := by
  set p := V.starProjection x with hp
  have hpV : p ∈ V := V.starProjection_apply_mem x
  have h1 : ∀ w ∈ V, inner ℝ (x - p) w = 0 := fun w hw => V.starProjection_inner_eq_zero x w hw
  have hpp : ‖p‖ ^ 2 = ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x) ^ 2 := by
    have := b.sum_sq_norm_inner_right ⟨p, hpV⟩
    have e : ‖(⟨p, hpV⟩ : V)‖ = ‖p‖ := rfl
    rw [e] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro t _
    have e2 : inner ℝ (b t) (⟨p, hpV⟩ : V) = inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) p := rfl
    rw [e2, Real.norm_eq_abs, sq_abs]
    have e3 := h1 _ (b t).2
    rw [real_inner_comm, inner_sub_right] at e3
    rw [show inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) p = inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x by linarith]
  rw [← hpp]
  have hxa : inner ℝ x a = inner ℝ p a := by
    have := h1 a ha
    rw [inner_sub_left] at this
    linarith
  rw [hxa]
  rcases eq_or_lt_of_le (sq_nonneg ‖a‖) with h0 | h0
  · rw [← h0, div_zero]; positivity
  · rw [div_le_iff₀ h0]
    have := abs_real_inner_le_norm p a
    have h2 : (inner ℝ p a) ^ 2 ≤ (‖p‖ * ‖a‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [h2]

theorem had_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (v : Fin n → ℝ) :
    ∑ j, (∑ i, v i * H i j) ^ 2 = n * ∑ i, v i ^ 2 := by
  calc ∑ j, (∑ i, v i * H i j) ^ 2 = ∑ j, ∑ i, ∑ k, (v i * v k) * (H i j * H k j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sq, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ i, ∑ k, (v i * v k) * ∑ j, H i j * H k j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
    _ = n * ∑ i, v i ^ 2 := by
        simp only [hH, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem col_orth {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) :
    ∀ c d, (∑ i, Hᵀ c i * Hᵀ d i) = if c = d then (n : ℝ) else 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : H * ((1 / (n : ℝ)) • Hᵀ) = 1 := by
    ext i j
    have e : (H * ((1 / (n : ℝ)) • Hᵀ)) i j = (∑ c, H i c * H j c) / n := by
      simp only [Matrix.mul_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [e, hH, Matrix.one_apply]
    split_ifs <;> simp [hn']
  have h2 : ((1 / (n : ℝ)) • Hᵀ) * H = 1 := mul_eq_one_comm.1 h1
  intro c d
  have e : (((1 / (n : ℝ)) • Hᵀ) * H) c d = (∑ i, H i c * H i d) / n := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h2, Matrix.one_apply, eq_div_iff hn'] at e
  simp only [transpose_apply]
  split_ifs at e ⊢ <;> linarith

theorem main {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, (∑ j, H i j * A i j) ^ 2 / (∑ j, (A i j) ^ 2)) ≤ (n : ℝ) * (A.rank : ℝ) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (LinearMap.range Aᵀ.mulVecLin).map (e : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hV : Module.finrank ℝ V = A.rank := by
    rw [← rank_transpose A]
    exact LinearEquiv.finrank_map_eq e _
  let b := stdOrthonormalBasis ℝ V
  have hmem : ∀ i, row A i ∈ V := by
    intro i
    refine Submodule.mem_map.2 ⟨Aᵀ *ᵥ Pi.single i 1, ⟨Pi.single i 1, rfl⟩, ?_⟩
    rw [mulVec_single_one]
    rfl
  have hin : ∀ i, inner ℝ (row H i) (row A i) = ∑ j, H i j * A i j := by
    intro i
    simp [row, PiLp.inner_apply, mul_comm]
  have hno : ∀ i, ‖row A i‖ ^ 2 = ∑ j, (A i j) ^ 2 := by
    intro i
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [row]
  have hbi : ∀ t i, inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (row H i) = ∑ c, ((b t : EuclideanSpace ℝ (Fin n)) c) * Hᵀ c i := by
    intro t i
    simp [row, PiLp.inner_apply, mul_comm]
  have hbt : ∀ t, ∑ i, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (row H i)) ^ 2 = n := by
    intro t
    simp only [hbi]
    rw [had_sum Hᵀ (col_orth H hn hH)]
    have : ‖(b t : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      have hn1 : ‖(b t : EuclideanSpace ℝ (Fin n))‖ = 1 := b.norm_eq_one t
      rw [hn1]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at this
    rw [this, mul_one]
  have step : ∀ i, (∑ j, H i j * A i j) ^ 2 / (∑ j, (A i j) ^ 2) ≤
      ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (row H i)) ^ 2 := by
    intro i
    rw [← hin, ← hno]
    exact proj_ratio V b _ _ (hmem i)
  refine le_trans (Finset.sum_le_sum (fun i _ => step i)) ?_
  rw [Finset.sum_comm]
  simp only [hbt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hV]
  rw [mul_comm]





end PEqualNP.Outside.L_meta_25783_aux.Work.Projection


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Sampling
theorem rankGap {n} (hn : 0<n) {H K : T n} (hh : Had H) (hE : err H K < n) :
    n < (M K).rank + 4 := by
  have cap := Projection.main (M H) hn ((had_orth H).mp hh) (M K)
  have norm (i : Fin n) : ∑ j, (M K i j)^2 = (n:ℝ) := by
    have sq (j : Fin n) : (M K i j)^2=1 := by cases h : K i j <;> norm_num [M,signR,h]
    simp [sq]
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have terms (i : Fin n) : (n:ℝ)-4*dist (H i) (K i) ≤
      (∑ j, M H i j * M K i j)^2 / (∑ j, (M K i j)^2) := by
    rw [norm,le_div_iff₀ hnR]
    change _ ≤ (dot (H i) (K i))^2
    rw [dot_dist]; nlinarith [sq_nonneg (dist (H i) (K i):ℝ)]
  have sum := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => terms i)).trans cap
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,←Finset.mul_sum,←Nat.cast_sum] at sum
  change (n:ℝ)*n-4*(err H K:ℝ) ≤ n*((M K).rank:ℝ) at sum
  have heR : (err H K:ℝ) < n := by exact_mod_cast hE
  by_contra! bad
  have badR : ((M K).rank:ℝ)+4 ≤ n := by exact_mod_cast bad
  nlinarith [mul_le_mul_of_nonneg_left badR hnR.le]
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work.Fourier
abbrev Cube (n : ℕ) := Fin n → ZMod 2
def sgn (b : ZMod 2) : ℤ := if b=0 then 1 else -1
def ch {n : ℕ} (a x : Cube n) : ℤ := sgn (dotProduct a x)

theorem sign_add (a b : ZMod 2) : sgn (a+b) = sgn a * sgn b := by
  revert a b
  decide

theorem symm {n : ℕ} (a x : Cube n) : ch a x = ch x a := by
  simp only [ch,dotProduct,mul_comm (a _) (x _)]

theorem ortho {n : ℕ} (a b : Cube n) :
    (∑ x : Cube n, ch a x * ch b x) = if a=b then (2:ℤ)^n else 0 := by
  classical
  by_cases eq : a=b
  · subst b
    have square (t : ZMod 2) : sgn t * sgn t = 1 := by revert t; decide
    simp [ch,square,ZMod.card]
  · rw [if_neg eq]
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
      by_contra! h
      exact eq (funext h)
    let e : Cube n := fun j => if j=i then 1 else 0
    have shift (p x : Cube n) : ch p (x+e) = ch p x * sgn (p i) := by
      have unit : dotProduct p e = p i := by simp [dotProduct,e,mul_ite]
      rw [ch,dotProduct_add,unit,sign_add]
      rfl
    have opposite : ∀ u v : ZMod 2, u ≠ v → sgn u * sgn v = -1 := by decide
    let f (x : Cube n) := ch a x * ch b x
    have flip (x : Cube n) : f (x+e) = -f x := by
      dsimp only [f]
      rw [shift,shift]
      calc
        _ = (ch a x * ch b x) * (sgn (a i) * sgn (b i)) := by ring
        _ = _ := by rw [opposite _ _ hi]; ring
    have same := Equiv.sum_comp (Equiv.addRight e) f
    change (∑ x : Cube n, f (x+e)) = ∑ x : Cube n, f x at same
    simp_rw [flip] at same
    rw [Finset.sum_neg_distrib] at same
    change (∑ x : Cube n, f x) = 0
    omega

def transform {n : ℕ} (f : Cube n → ℤ) (a : Cube n) := ∑ x : Cube n, f x * ch a x

theorem adj {n : ℕ} (f h : Cube n → ℤ) :
    (∑ a : Cube n, transform f a * h a) = ∑ z : Cube n, f z * transform h z := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  rw [symm x z]
  ring

theorem inv {n : ℕ} (f : Cube n → ℤ) (a : Cube n) :
    transform (transform f) a = (2:ℤ)^n * f a := by
  classical
  change (∑ x : Cube n, transform f x * ch a x) = _
  rw [adj]
  have lookup (z : Cube n) : transform (ch a) z = if a=z then (2:ℤ)^n else 0 := ortho a z
  simp_rw [lookup]
  simp [mul_ite,mul_comm]
end PEqualNP.Outside.L_meta_25783_aux.Work.Fourier


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Fourier
abbrev W (s : ℕ) := Cube s × Cube s
def χ {s} (x y : W s) := ch x.1 y.1 * ch x.2 y.2
def coeff {s} (f : W s → ℤ) (a : W s) := ∑ x, f x * χ a x
theorem paircard (s : ℕ) : Fintype.card (W s) = 4^s := by
  simp [W,Cube,ZMod.card,← mul_pow]
theorem ch_sym {s} (x y : W s) : χ x y=χ y x := by simp only [χ,symm]
theorem ch_add {s} (a x y : W s) : χ a (x+y)=χ a x*χ a y := by
  simp only [χ,Prod.fst_add,Prod.snd_add,ch,dotProduct_add,sign_add]; ring
theorem ch_ortho {s} (a b : W s) :
    ∑ x : W s, χ a x*χ b x = if a=b then (4:ℤ)^s else 0 := by
  rw [Fintype.sum_prod_type]
  change (∑ x,∑ y,ch a.1 x*ch a.2 y*(ch b.1 x*ch b.2 y))=_
  have turn (x y : Cube s) : ch a.1 x*ch a.2 y*(ch b.1 x*ch b.2 y)=
      ch a.1 x*ch b.1 x*(ch a.2 y*ch b.2 y) := by ring
  simp only [turn,←Finset.mul_sum,←Finset.sum_mul,ortho]
  by_cases h : a.1=b.1 <;> by_cases k : a.2=b.2 <;>
    simp [h,k,Prod.ext_iff,←mul_pow]
theorem pair_inv {s} (f : W s → ℤ) (x : W s) :
    ∑ a, coeff f a * χ a x = (4:ℤ)^s * f x := by
  simp only [coeff,Finset.sum_mul]
  rw [Finset.sum_comm]
  have one (y : W s) : (∑ a, f y*χ a y*χ a x)=f y*(if y=x then (4:ℤ)^s else 0) := by
    rw [←ch_ortho y x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; rw [ch_sym a y,ch_sym a x]; ring
  simp_rw [one]
  simp [mul_ite,mul_comm]
theorem sampleRank {s n} (f : W s→ℤ) (r c : Fin n → W s) (u v : Fin n→ℝ) :
  let S := Finset.univ.filter (fun a => coeff f a ≠ 0)
  Matrix.rank (m:=Fin n) (n:=Fin n) (R:=ℝ) (fun i j => u i*v j*(f (r i+c j):ℝ)) ≤ S.card := by
  classical
  intro S
  let P : Matrix (Fin n) S ℝ := fun i a => u i*(χ a.1 (r i):ℝ)*(coeff f a.1:ℝ)/(4:ℝ)^s
  let Q : Matrix S (Fin n) ℝ := fun a j => v j*(χ a.1 (c j):ℝ)
  have factor : (fun i j => u i*v j*(f (r i+c j):ℝ) : Matrix (Fin n) (Fin n) ℝ)=P*Q := by
    ext i j
    have ih := pair_inv f (r i+c j)
    have prune : (∑ a ∈ S, coeff f a * χ a (r i+c j))=∑ a, coeff f a * χ a (r i+c j) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ nx
      have zero : coeff f x = 0 := by simpa [S] using nx
      simp [zero]
    rw [←prune] at ih
    have real_eq : (∑ a ∈ S, (coeff f a:ℝ) * (χ a (r i+c j):ℝ)) =
       (4:ℝ)^s*(f (r i+c j):ℝ) := by exact_mod_cast ih
    have weight : (4:ℝ)^s ≠ 0 := by positivity
    rw [← Finset.sum_coe_sort] at real_eq
    rw [Matrix.mul_apply]
    calc
      u i*v j*(f (r i+c j):ℝ) =
        (u i*v j/(4:ℝ)^s)*∑ a : S, (coeff f a:ℝ)*(χ a (r i+c j):ℝ) := by
          rw [real_eq]; field_simp
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _; simp only [P,Q,ch_add,Int.cast_mul]; ring
  rw [factor]
  apply (Matrix.rank_mul_le_left P Q).trans
  calc P.rank ≤ Module.finrank ℝ (S→ℝ) := LinearMap.finrank_range_le P.mulVecLin
    _ = S.card := by simp
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work
abbrev F := ZMod 2
abbrev V (s : ℕ) := Fin s → F
def fr {s} (γ : V s) (A B : Fin s → V s) (p q : V s) (j : Fin s) :=
  γ j + ∑ i ∈ Finset.Ioi j, (p i*A i j+q i*B i j)
def fac {s} (γ : V s) (A B : Fin s → V s) (p q : V s) (j : Fin s) : ℤ :=
  if fr γ A B p q j = 0 then (if p j=0 ∧ q j=0 then 4 else 0) else
   2 * (if p j*q j=0 then 1 else -1)
theorem fullSupport {s : ℕ} (γ : V s) (A B : Fin s → V s)
    (full : ∀ p q, (∏ j, fac γ A B p q j) ≠ 0) :
    (∀ j, γ j=1) ∧ (∀ (i j : Fin s), j < i → A i j = 0 ∧ B i j = 0) := by
  have one : ∀ x : F, x ≠ 0 → x = 1 := by decide
  classical
  have forces (p q : V s) (j : Fin s) (hp : p j=1) : fr γ A B p q j=1 := by
    apply one _
    intro hz
    have zero : fac γ A B p q j=0 := by simp [fac,hz,hp]
    exact full p q (Finset.prod_eq_zero (Finset.mem_univ j) zero)
  have gamma (j : Fin s) : γ j=1 := by
    let p : V s := fun i => if i=j then 1 else 0
    have sum0 : ∑ i ∈ Finset.Ioi j,(p i * A i j + (0:F)*B i j)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [p,(Finset.mem_Ioi.mp hi).ne']
    have h := forces p (fun _ => 0) j (by simp [p])
    simpa only [fr,sum0,add_zero] using h
  refine ⟨gamma,?_⟩
  intro i j hij
  let p : V s := fun x => if x=j then 1 else 0
  let k : V s := fun x => if x=i then 1 else 0
  have asym : i ≠ j := hij.ne'
  have pick (a b : F) :
      (∑ x ∈ Finset.Ioi j, ((p x+a*k x)*A x j+(b*k x)*B x j))=a*A i j+b*B i j := by
    rw [Finset.sum_eq_single i]
    · simp [p,k,asym]
    · intro x hx ne
      simp [p,k,(Finset.mem_Ioi.mp hx).ne',ne]
    · intro denied; exact (denied (Finset.mem_Ioi.mpr hij)).elim
  have f (a b : F) : 1 + (a*A i j+b*B i j)=1 := by
    have h := forces (fun x => p x+a*k x) (fun x => b*k x) j (by simp [p,k,hij.ne])
    simpa only [fr,pick,gamma] using h
  constructor
  · simpa using f 1 0
  · simpa using f 0 1



theorem fourZeros {s : ℕ} (hs : 2 ≤ s) (γ : V s) (A B : Fin s → V s)
  (j : Fin s) (p q : V s) (z : fr γ A B p q j=0) :
    4 ≤ (Finset.univ.filter (fun t : V s × V s => (∏ i, fac γ A B t.1 t.2 i)=0)).card := by
  have ker : ∀ x y : F, ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧ a*x+b*y=0 := by decide
  classical
  let k : Fin s := if j.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have kj : k ≠ j := by
    intro h
    have eq := congrArg Fin.val h
    by_cases e : j.val=0 <;> simp [k,e] at eq <;> omega
  obtain ⟨a,b,ab,eq⟩ := ker (A k j) (B k j)
  let f (t : F×F) : V s × V s :=
    (fun x => if x=j then 1 else if x=k then p x+t.1*a else p x,
     fun x => if x=j then t.2 else if x=k then q x+t.1*b else q x)
  have inj : Function.Injective f := by
    intro x y e
    have aeq := congrArg (fun z : V s × V s => z.1 k) e
    have beq := congrArg (fun z : V s × V s => z.2 k) e
    have ceq := congrArg (fun z : V s × V s => z.2 j) e
    simp [f,kj] at aeq beq
    simp [f] at ceq
    exact Prod.ext (ab.elim (fun h => (aeq.resolve_right h)) (fun h => (beq.resolve_right h))) ceq
  have vanish (t : F×F) : fr γ A B (f t).1 (f t).2 j=0 := by
    rw [←z]; unfold fr
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have xj := (Finset.mem_Ioi.mp hx).ne'
    by_cases h : x=k
    · subst x
      simp [f,kj]
      linear_combination t.1 * eq
    · simp [f,xj,h]
  let Z := Finset.univ.filter (fun t : V s × V s => (∏ i, fac γ A B t.1 t.2 i)=0)
  have sub : Finset.univ.image f ⊆ Z := by
    intro v mem
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp mem
    apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,Finset.prod_eq_zero (Finset.mem_univ j) ?_⟩
    simp [fac,vanish t,f]
  have c := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj] at c
  simpa [F,ZMod.card,Z] using c


end PEqualNP.Outside.L_meta_25783_aux.Work

namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents
abbrev Table (n : ℕ) := Fin n → Fin n → ZMod 2
def Aff {n t} (z : Fin t → Table n) (gate : Fin t → ℕ) (k : ℕ) (f : Table n) :=
  ∃ (u v : Fin n → ZMod 2) (p : Fin t → ZMod 2),
  (∀ a, k < gate a → p a = 0) ∧ ∀ x y, f x y = u x + v y + ∑ a, p a * z a x y
theorem affSplit {n t} (z : Fin t → Table n) (gate : Fin t → ℕ) (k) (u v : Fin n → ZMod 2) :
    Aff z gate k (fun x y => u x + v y) := ⟨u,v,fun _ => 0,by simp,by simp⟩
theorem affConst {n t} (z : Fin t → Table n) (gate : Fin t → ℕ) (k) (a : ZMod 2) :
    Aff z gate k (fun _ _ => a) := by simpa using affSplit z gate k (fun _ => a) (fun _ => 0)
theorem affAdd {n t} {z : Fin t → Table n} {gate : Fin t → ℕ} {k} {f g : Table n} :
    Aff z gate k f → Aff z gate k g → Aff z gate k (fun x y => f x y+g x y) := by
  rintro ⟨u,v,p,hp,h⟩ ⟨U,V,P,hP,H⟩
  exact ⟨u+U,v+V,p+P,fun a ha => by simp [hp a ha,hP a ha],fun x y => by
    simp only [h,H,Pi.add_apply,add_mul,Finset.sum_add_distrib]; ring⟩
theorem affScale {n t} {z : Fin t → Table n} {gate : Fin t → ℕ} {k} {f : Table n} (a:ZMod 2) :
    Aff z gate k f → Aff z gate k (fun x y => a*f x y) := by
  rintro ⟨u,v,p,hp,h⟩
  refine ⟨fun x => a*u x,fun y => a*v y,fun i => a*p i,fun x hx => by simp [hp x hx],?_⟩
  intro x y; dsimp only; rw [h]; simp only [mul_add,Finset.mul_sum,mul_assoc]
theorem affRelax {n t} {z : Fin t → Table n} {gate : Fin t → ℕ} {k l} {f : Table n} (le : k ≤ l) :
    Aff z gate k f → Aff z gate l f := by
  rintro ⟨u,v,p,cap,eq⟩
  exact ⟨u,v,p,fun a h => cap a (le.trans_lt h),eq⟩
theorem affProduct {n t} (z : Fin t → Table n) (gate : Fin t → ℕ) (a : Fin t) :
    Aff z gate (gate a) (z a) := by
  classical
  refine ⟨fun _=>0,fun _=>0,fun i => if i=a then 1 else 0,?_,?_⟩
  · intro i hi; dsimp only; split_ifs with e
    · subst i; omega
    · rfl
  · intro x y; simp [ite_mul]
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Sampling CircuitLowerBounds Represents
theorem canonicalHad {n s} (hn : 0<n) (e : Fin n ≃ V2 s) :
    Had (predT e e (fun _ => false) (fun _ => false)) := by
  apply (had_orth _).mpr
  intro i j
  have sgnBool (a : ZMod 2) : signR (decide (a=1))=(Fourier.sgn a:ℝ) := by
    have sb (b : Bool) : signR b = (Fourier.sgn (Ranks.b2z b):ℝ) := by cases b <;> norm_num [signR,Fourier.sgn,Ranks.b2z]
    rw [sb,bit_dec]
  have each (a b : Fin n) : signR (predT e e (fun _=>false) (fun _=>false) a b)=
      (Fourier.ch (e a) (e b):ℝ) := by simpa [predT,Fourier.ch,dotProduct,sgnBool]
  rw [dot]
  simp only [each,←Int.cast_mul,←Int.cast_sum]
  rw [Equiv.sum_comp e (fun x => Fourier.ch (e i) x * Fourier.ch (e j) x),Fourier.ortho]
  have card := Fintype.card_congr e
  simp [V2,ZMod.card] at card
  split_ifs with p q <;> simp_all
theorem classifyPred {n s} (hn : 8≤n) (size : n=4^s) {H : T n} (hh : Had H)
    (r c : Fin n → V2 s) (u v : Sampling.V n) (sm : err H (predT r c u v)+2<n) :
    (∃ (row col : Fin n ≃ V2 s) (Q R : Sampling.V n), H=predT row col Q R) ∧
    (err H (predT r c u v)=0 ∨ 2*err H (predT r c u v)=n ∧
    (copy H (predT r c u v) ∨ copy (Function.swap H) (Function.swap (predT r c u v)))) := by
  classical
  have card : Fintype.card (Fin n)=Fintype.card (V2 s) := by
    simp [V2,ZMod.card,size,pow_mul] <;> norm_num
  let e := Fintype.equivOfCardEq card
  let D := predT e e (fun _=>false) (fun _=>false)
  have kd : sam D (e.symm ∘ r) (e.symm ∘ c) u v = predT r c u v := by
    funext i j; simp [D,sam,predT]
  have hD : Had D := canonicalHad (by omega : 0<n) e
  have orient : equivT H D ∧ (err H (predT r c u v)=0 ∨ 2*err H (predT r c u v)=n ∧
      (copy H (predT r c u v) ∨ copy (Function.swap H) (Function.swap (predT r c u v)))) := by
    rw [←kd] at sm ⊢
    by_cases hc : Function.Injective (e.symm ∘ c)
    · obtain ⟨eq,dis⟩ := oriented (by omega) hh hD (e.symm ∘ r) (e.symm ∘ c) u v hc (by omega)
      exact ⟨eq,dis.imp_right (fun ⟨d,cp⟩ => ⟨d,Or.inl cp⟩)⟩
    · have hr : Function.Injective (e.symm ∘ r) := by
        by_contra nr
        have z := double_bound (by omega) hh D (e.symm ∘ r) (e.symm ∘ c) u v nr hc; omega
      let K := sam D (e.symm ∘ r) (e.symm ∘ c) u v
      have swap := sam_swap D (e.symm ∘ r) (e.symm ∘ c) u v
      have es : err (Function.swap H) (sam (Function.swap D) (e.symm ∘ c) (e.symm ∘ r) v u)<n := by
        rw [←swap,err_swap]; omega
      obtain ⟨eq,dis⟩ := oriented (by omega) (had_swap (by omega) hh) (had_swap (by omega) hD) _ _ v u hr es
      rw [←swap,err_swap] at dis
      exact ⟨unswap eq,dis.imp_right (fun ⟨d,cp⟩ => ⟨d,Or.inr cp⟩)⟩
  obtain ⟨⟨f,g,a,b,eq⟩,ans⟩ := orient
  refine ⟨⟨f.trans e,g.trans e,a,b,?_⟩,ans⟩
  rw [eq]; funext i j; simp [D,sam,predT] <;> rfl
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents
def wire {n} (C : Circuit) (k : ℕ) : Table n :=
  fun i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
def nodes (C : Circuit) := Finset.univ.filter (fun i : Fin C.gates.length => nlGate C.gates[i.val]=true)
def enumNode (C : Circuit) := (nodes C).orderIsoOfFin rfl
def addr {n : ℕ} (C : Circuit) (a : Fin (nodes C).card) : ℕ := n+n+(enumNode C a).val.val
def pin (C : Circuit) (a : Fin (nodes C).card) (b : ℕ) : ℕ := (C.gates[(enumNode C a).val.val]).inputs.getD b 0
def mon {n} (C : Circuit) (a : Fin (nodes C).card) : Table n :=
  fun x y => wire C (pin C a 0) x y * wire C (pin C a 1) x y
theorem circuitAff {n} (C : Circuit) (ar : ∀ g∈C.gates,g.inputs.length≤2) (rb : ReadsBack (n+n) C)
    (k : ℕ) : Aff (mon (n:=n) C) (addr (n:=n) C) k (wire C k) := by
  classical
  have back (idx : Fin C.gates.length) {a : ℕ} (ha : a ∈ C.gates[idx.val].inputs) : a < n+n+idx.val := by
    have h := rb idx.val idx.isLt a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ idx.isLt] at h
    exact h ha
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases raw : k < n+n
    · by_cases left : k<n
      · have e : wire (n:=n) C k = fun i j => b2z (decide (k=i.val))+0 := by
          funext i j
          unfold wire
          rw [wiresOf_getD_input (oneEach i j) C.gates (by rw [oneEach_length];exact raw),oneEach_getD_left i j left,add_zero]
        rw [e]; apply affSplit
      · have e : wire (n:=n) C k = fun i j => 0+b2z (decide (k-n=j.val)) := by
          funext i j
          unfold wire
          rw [wiresOf_getD_input (oneEach i j) C.gates (by rw [oneEach_length];exact raw),oneEach_getD_right i j (by omega) raw,zero_add]
        rw [e]; apply affSplit
    by_cases live : k < n+n+C.gates.length
    · let idx : Fin C.gates.length := ⟨k-(n+n),by omega⟩
      let g := C.gates[idx.val]
      have eqk : n+n+idx.val=k := by dsimp [idx]; omega
      have arr := ar g (List.getElem_mem idx.isLt)
      have rv (a) (ha : a∈g.inputs) : a<k := (back idx ha).trans_eq eqk
      have val (i j : Fin n) : wire C k i j =
          b2z (g.op.eval (g.inputs.map fun a => (wiresOf (oneEach i j) C.gates).getD a false)) := by
        unfold wire; rw [←eqk]
        have h := wiresOf_getD_gate (oneEach i j) C.gates idx.isLt (by
          intro a ha; rw [oneEach_length]; exact back idx ha)
        simpa only [oneEach_length] using congrArg b2z h
      match pinEq : g.inputs with
      | [] =>
        have e : wire (n:=n) C k = fun _ _ => b2z (g.op.eval []) := by
          funext i j; rw [val,pinEq]; rfl
        rw [e]; apply affConst
      | [a] =>
        have ea : a<k := rv a (by simp [pinEq])
        let c0 := b2z (g.op.eval [false])
        let c1 := c0 + b2z (g.op.eval [true])
        have e : wire (n:=n) C k = fun i j => c0+c1*wire C a i j := by
          funext i j; rw [val,pinEq]
          exact anf_one (fun x => g.op.eval [x]) _
        rw [e]
        exact affAdd (affConst _ _ _ _) (affScale c1 (affRelax ea.le (ih a ea)))
      | [a,b] =>
        have ea : a<k := rv a (by simp [pinEq])
        have eb : b<k := rv b (by simp [pinEq])
        let c0 := b2z (g.op.eval [false,false])
        let c1 := c0+b2z (g.op.eval [true,false])
        let c2 := c0+b2z (g.op.eval [false,true])
        have e : wire (n:=n) C k = fun i j => c0+c1*wire C a i j+c2*wire C b i j+
            b2z (nlGate g)*(wire C a i j*wire C b i j) := by
          funext i j; rw [val,pinEq]
          simpa only [nlGate,pinEq,List.length_cons,List.length_nil,beq_self_eq_true,Bool.true_and,List.map_cons,List.map_nil,wire,c0,c1,c2] using
            anf_two (fun x y => g.op.eval [x,y]) ((wiresOf (oneEach i j) C.gates).getD a false)
                ((wiresOf (oneEach i j) C.gates).getD b false)
        have lin := affAdd (affAdd (affConst _ _ _ c0) (affScale c1 (affRelax ea.le (ih a ea)))) (affScale c2 (affRelax eb.le (ih b eb)))
        rw [e]; apply affAdd lin
        by_cases h : nlGate g = true
        · let t := (enumNode C).symm ⟨idx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
          have ti : (enumNode C t).val = idx := congrArg Subtype.val ((enumNode C).apply_symm_apply _)
          have atK : addr (n:=n) C t=k := by simp only [addr,ti,eqk]
          have m : mon (n:=n) C t = fun i j => b2z (nlGate g)*(wire C a i j*wire C b i j) := by
            funext i j
            simp only [mon,pin,ti,show C.gates[idx.val]=g from rfl,pinEq,h,b2z,ite_true,one_mul]
            rfl
          rw [←m,←atK]
          exact affProduct _ _ t
        · have hf : nlGate g=false := Bool.eq_false_iff.mpr h
          simp only [hf,b2z,Bool.false_eq_true,ite_false,zero_mul]
          apply affConst
      | _::_::_::_ =>
        rw [pinEq] at arr; simp at arr
    · have e : wire (n:=n) C k=fun _ _ => 0 := by
        funext i j; unfold wire
        rw [List.getD_eq_default _ _ (by rw [wiresOf_length,oneEach_length];omega)]; rfl
      rw [e]; apply affConst
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Ranks CircuitLowerBounds MetaComplexity.NestedCover Represents
structure Taps (n t : ℕ) where
  lrow : Fin n → V t
  lcol : Fin n → V t
  rrow : Fin n → V t
  rcol : Fin n → V t
  A : Fin t→V t
  B : Fin t→V t
  gamma : V t
  u : Fin n→F
  v : Fin n→F
def stage {t} (A B : Fin t→V t) (x y : V t) : V t :=
  wellFounded_lt.fix fun i rec =>
    (x i+∑ j ∈ Finset.Iio i, A i j * (if h : j < i then rec j h else 0)) *
    (y i+∑ j ∈ Finset.Iio i, B i j * (if h : j < i then rec j h else 0))
theorem stage_eq {t} (A B : Fin t→V t) (x y : V t) (i : Fin t) :
    stage A B x y i =
    (x i+∑ j ∈ Finset.Iio i, A i j * stage A B x y j) *
    (y i+∑ j ∈ Finset.Iio i, B i j * stage A B x y j) := by
  rw [stage,WellFounded.fix_eq]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro j hj <;> simp [Finset.mem_Iio.mp hj,stage]
def Taps.Fun {n t} (E : Taps n t) (p : W t) : F :=
  ∑ a, E.gamma a * stage E.A E.B p.1 p.2 a
def Taps.value {n t} (E : Taps n t) (x y : Fin n) : F :=
  E.u x + E.v y + E.Fun ((E.lrow x,E.rrow x)+(E.lcol y,E.rcol y))
theorem extract {n} (C : Circuit) (ar : ∀ g∈C.gates,g.inputs.length≤2) (rb : ReadsBack (n+n) C) :
    ∃ E : Taps n (nodes C).card, ∀ x y, wire C C.output x y=E.value x y := by
  classical
  let t := (nodes C).card
  have bound (i : Fin t) (v : ℕ) (hv : v<2) : pin C i v < addr (n:=n) C i := by
    let idx := (enumNode C i).val
    have hnl := (Finset.mem_filter.mp (enumNode C i).property).2
    have ar2 : (C.gates[idx.val]).inputs.length=2 := by
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hnl).1
    have live : v < C.gates[idx.val].inputs.length := by omega
    have h := rb idx.val idx.isLt (pin C i v)
    change pin C i v < n+n+idx.val
    apply h
    unfold gateAt pin
    rw [List.getD_eq_getElem _ _ idx.isLt,List.getD_eq_getElem _ _ live]
    exact List.getElem_mem _
  choose lr lc A suppL valL using fun i : Fin t => circuitAff (n:=n) C ar rb (pin C i 0)
  choose rr rc B suppR valR using fun i : Fin t => circuitAff (n:=n) C ar rb (pin C i 1)
  obtain ⟨u,v,gamma,_,out⟩ := circuitAff (n:=n) C ar rb C.output
  let E : Taps n t := ⟨fun x i => lr i x,fun y i => lc i y,fun x i => rr i x,fun y i => rc i y,
    A,B,gamma,u,v⟩
  refine ⟨E,?_⟩
  intro x y
  let X := fun i => lr i x + lc i y
  let Y := fun i => rr i x + rc i y
  have mono (a b : Fin t) (h : a≤b) : addr (n:=n) C a ≤ addr (n:=n) C b := by
    apply Nat.add_le_add_left
    exact (enumNode C).monotone h
  have corr (i : Fin t) : mon C i x y = stage A B X Y i := by
    refine @WellFounded.induction (Fin t) (· < ·) wellFounded_lt (fun a => mon C a x y = stage A B X Y a) i ?_
    intro i ih
    rw [mon,valL i x y,valR i x y,stage_eq]
    have cut (P : Fin t→V t) (cutoff : ∀ a, i≤a → P i a=0) :
        (∑ a, P i a*mon C a x y)=∑ a ∈ Finset.Iio i,P i a*stage A B X Y a := by
      rw [←Finset.sum_subset (Finset.subset_univ (Finset.Iio i)) (by
        intro a _ no
        simp [cutoff a (by simpa using no)])]
      exact Finset.sum_congr rfl fun a ha => by rw [ih a (Finset.mem_Iio.mp ha)]
    rw [cut A (fun a ha => suppL i a ((bound i 0 (by decide)).trans_le (mono i a ha))),
        cut B (fun a ha => suppR i a ((bound i 1 (by decide)).trans_le (mono i a ha)))]
  unfold Taps.value Taps.Fun
  change wire C C.output x y=u x+v y+∑ i,gamma i*stage A B X Y i
  rw [out]; simp only [corr]
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work.Product

abbrev K := ZMod 2
def sg (a : K) : ℤ := if a=0 then 1 else -1
theorem sg_add (a b : K) : sg (a+b) = sg a * sg b := by revert a b; decide
theorem twice (a : K) : a+a=0 := by revert a; decide
theorem sg_sum {ι : Type*} (S : Finset ι) (f : ι → K) :
    sg (∑ i ∈ S, f i) = ∏ i ∈ S, sg (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sg]
  | insert i S hi ih => simp [hi, sg_add, ih]
theorem localSum (c p q : K) :
    (∑ v : K × K, sg (c * (v.1*v.2) + p*v.1 + q*v.2)) =
      if c=0 then (if p=0 ∧ q=0 then 4 else 0) else 2*sg (p*q) := by
  revert c p q
  decide
theorem flipSum {s : ℕ} (f : Fin s → Fin s → K) :
    (∑ i, ∑ j ∈ Finset.Iio i, f i j) = ∑ j, ∑ i ∈ Finset.Ioi j, f i j := by
  classical
  have lo (i : Fin s) : Finset.Iio i = Finset.univ.filter (fun j => j < i) := by ext; simp
  have hi (j : Fin s) : Finset.Ioi j = Finset.univ.filter (fun i => j < i) := by ext; simp
  simp_rw [lo,hi,Finset.sum_filter]
  rw [Finset.sum_comm]
theorem transposeSum {s : ℕ} (p z : Fin s → K) (M : Fin s → Fin s → K) :
    (∑ i, p i * ∑ j ∈ Finset.Iio i, M i j * z j) =
    ∑ j, (∑ i ∈ Finset.Ioi j, p i * M i j) * z j := by
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  exact flipSum _

end PEqualNP.Outside.L_meta_25783_aux.Work.Product

namespace PEqualNP.Outside.L_meta_25783_aux.Work.Product

theorem triangular : ∀ s : ℕ,
  let V := Fin s → ZMod 2
  let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
  let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
  ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
  (∀ x y i, Z x y i =
    (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
    (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
  ∀ p q : V,
    let c := fun (j : Fin s) =>
      γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
    (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
      ∏ j : Fin s,
        if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
        else 2 * sign (p j * q j) := by
  classical
  intro s V dot sign A B γ Z hz p q c
  let Pair := Fin s → K × K
  let z : Pair → V := fun e i => (e i).1 * (e i).2
  let h := fun (M : Fin s → Fin s → K) (v : V) (i : Fin s) => ∑ j ∈ Finset.Iio i, M i j * v j
  let decode : Pair → V × V := fun e =>
    (fun i => (e i).1 + h A (z e) i, fun i => (e i).2 + h B (z e) i)
  let encode : V × V → Pair := fun u i => (u.1 i + h A (Z u.1 u.2) i, u.2 i + h B (Z u.1 u.2) i)
  have after (e : Pair) : Z (decode e).1 (decode e).2 = z e := by
    funext i
    refine @WellFounded.induction (Fin s) (· < ·) wellFounded_lt (fun j => Z (decode e).1 (decode e).2 j = z e j) i ?_
    intro i ih
    have ht (M : Fin s → Fin s → K) : h M (Z (decode e).1 (decode e).2) i = h M (z e) i :=
      Finset.sum_congr rfl (fun j hj => congrArg (fun a : K => M i j * a) (ih j (Finset.mem_Iio.mp hj)))
    rw [hz]
    change (((e i).1 + h A (z e) i) + h A _ i) * (((e i).2 + h B (z e) i) + h B _ i) = _
    rw [ht A,ht B]
    simp [add_assoc,twice,z]
  let bij : Pair ≃ V × V := {
    toFun := decode
    invFun := encode
    left_inv := by intro e; funext i; simp [encode,after,decode,add_assoc,twice]
    right_inv := by
      intro u
      have eqz : z (encode u) = Z u.1 u.2 := funext (fun i => (hz u.1 u.2 i).symm)
      apply Prod.ext <;> funext i <;> simp [decode,eqz,encode,add_assoc,twice] }
  let phase := fun (u : V × V) => sg (dot γ (Z u.1 u.2) + dot p u.1 + dot q u.2)
  let term := fun i (v : K × K) => sg (c i * (v.1*v.2) + p i*v.1 + q i*v.2)
  have decomp (e : Pair) : phase (bij e) = ∏ i, term i (e i) := by
    change sg (dot γ (Z (decode e).1 (decode e).2) + dot p (decode e).1 + dot q (decode e).2) = _
    rw [after]
    unfold term
    rw [← sg_sum]
    congr 1
    change _ = ∑ i, (c i * z e i + p i * (e i).1 + q i * (e i).2)
    dsimp only [dot,decode,h,c]
    simp only [mul_add,add_mul,Finset.sum_add_distrib]
    rw [transposeSum,transposeSum]
    abel
  calc
    _ = ∑ u : V × V, phase u := (Fintype.sum_prod_type phase).symm
    _ = ∑ e : Pair, phase (bij e) := (Equiv.sum_comp bij phase).symm
    _ = ∑ e : Pair, ∏ i, term i (e i) := Finset.sum_congr rfl (fun e _ => decomp e)
    _ = ∏ i, ∑ v : K × K, term i v := (Fintype.prod_sum term).symm
    _ = _ := Finset.prod_congr rfl (fun i _ => localSum _ _ _)

end PEqualNP.Outside.L_meta_25783_aux.Work.Product

namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Ranks Sampling Fourier
def Taps.sign {n t} (E : Taps n t) (p : W t) := sgn (E.Fun p)
theorem spectrum {n t} (E : Taps n t) (p q : V t) :
    coeff E.sign (p,q) = ∏ j, fac E.gamma E.A E.B p q j := by
  have th := Product.triangular t E.A E.B E.gamma (stage E.A E.B) (stage_eq E.A E.B) p q
  unfold fac fr
  rw [←th]
  unfold coeff; rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  change sgn _ * (sgn _ * sgn _) = sgn (_ + _ + _)
  rw [sign_add,sign_add]
  simp only [Taps.Fun,dotProduct]
  ring
theorem rankSupport {n t} {K : T n} (E : Taps n t) (val : ∀ x y, b2z (K x y)=E.value x y) :
    (M K).rank ≤ (Finset.univ.filter (fun p : W t => coeff E.sign p ≠ 0)).card := by
  have rr := sampleRank E.sign (fun i => (E.lrow i,E.rrow i)) (fun j => (E.lcol j,E.rcol j))
      (fun i => (sgn (E.u i):ℝ)) (fun j => (sgn (E.v j):ℝ))
  suffices e : M K = (fun i j => (sgn (E.u i):ℝ)*(sgn (E.v j):ℝ)*(E.sign ((E.lrow i,E.rrow i)+(E.lcol j,E.rcol j)):ℝ) : Matrix (Fin n) (Fin n) ℝ) by rw [e]; exact rr
  ext i j
  change signR (K i j)=_
  have flip (b : Bool) : signR b = (sgn (b2z b):ℝ) := by cases b <;> norm_num [signR,sgn,b2z]
  rw [flip,val]; simp [Taps.value,Taps.sign,sign_add]
def pack {s} (a b : V s) (i : Fin (2*s)) := Fin.append a b (Fin.cast (two_mul s) i)
theorem pack_dot {s} (a b c d : V s) :
    ∑ i, pack a b i * pack c d i = (∑ i, a i*c i) + ∑ i, b i*d i := by
  have e := Equiv.sum_comp (finCongr (two_mul s)) (fun i => Fin.append a b i*Fin.append c d i)
  rw [Fin.sum_univ_add] at e
  simpa only [pack,finCongr_apply,Fin.append_left,Fin.append_right] using e
theorem simpleTable {n s} (E : Taps n s) (H : T n)
    (he : ∀ x y,b2z (H x y)=E.value x y)
    (g : ∀ j, E.gamma j=1) (ab : ∀ i j, j < i → E.A i j=0 ∧ E.B i j=0) :
    ∃ (r c : Fin n → V2 s) (u v : Sampling.V n), H=predT r c u v := by
  let U (i : Fin n) := E.u i + ∑ k, E.lrow i k * E.rrow i k
  let Vv (j : Fin n) := E.v j + ∑ k, E.lcol j k * E.rcol j k
  let r (x : Fin n) := pack (E.lrow x) (E.rrow x)
  let c (y : Fin n) := pack (E.rcol y) (E.lcol y)
  refine ⟨r,c,fun i => decide (U i = 1),fun j => decide (Vv j=1),?_⟩
  funext x y
  apply b2z_inj
  rw [he]; simp only [Taps.value,Taps.Fun,predT,b2z_xor,bit_dec,g,one_mul]
  have mult (i : Fin s) (X Y : V s) : stage E.A E.B X Y i=X i*Y i := by
    rw [stage_eq]
    have a : (∑ j ∈ Finset.Iio i,E.A i j*stage E.A E.B X Y j)=0 :=
      Finset.sum_eq_zero (fun j h => by rw [(ab i j (Finset.mem_Iio.mp h)).1,zero_mul])
    have b : (∑ j ∈ Finset.Iio i,E.B i j*stage E.A E.B X Y j)=0 :=
      Finset.sum_eq_zero (fun j h => by rw [(ab i j (Finset.mem_Iio.mp h)).2,zero_mul])
    simp [a,b]
  simp only [r,c,pack_dot,mult,Prod.fst_add,Prod.snd_add,Pi.add_apply,U,Vv,add_mul,mul_add,Finset.sum_add_distrib]
  rw [show (∑ k,E.lcol y k*E.rrow x k)=∑ k,E.rrow x k*E.lcol y k by apply Finset.sum_congr rfl; intro k _; ring]
  ring
end PEqualNP.Outside.L_meta_25783_aux.Work


namespace PEqualNP.Outside.L_meta_25783_aux.Work
open Ranks Sampling CircuitLowerBounds
theorem normalNear {n s} (hs : 2 ≤ s) (hn : n = 4^s) {H : T n} (hh : Had H) (C : Circuit)
    (valid : valid2 n s C) (small : err H (fun i j => C.eval (PEqualNP.Represents.oneEach i j)) < n) :
    ∃ (r c : Fin n→V2 s) (u v : Sampling.V n), (fun i j => C.eval (PEqualNP.Represents.oneEach i j))=predT r c u v := by
  classical
  let K : T n := fun i j => C.eval (PEqualNP.Represents.oneEach i j)
  have pos : 0<n := by rw [hn]; positivity
  have kr : n < (M K).rank+4 := rankGap pos hh (by change err H K<n at small; exact small)
  let t := (nodes C).card
  have cap : t ≤ s := by
    have eq := card_filter_fin_eq_countP C.gates nlGate
    exact (le_of_eq eq).trans valid.2.2
  obtain ⟨E,ev⟩ := extract (n:=n) C valid.1 valid.2.1
  have evK (i j : Fin n) : b2z (K i j)=E.value i j := ev i j
  have rs := rankSupport E evK
  let S := Finset.univ.filter (fun p : W t => coeff E.sign p ≠ 0)
  change (M K).rank ≤ S.card at rs
  have size : S.card ≤ 4^t := (Finset.card_le_univ S).trans_eq (paircard t)
  have equal : t=s := by
    by_contra d
    have less : t < s := by omega
    have nbig : 4^t+4 ≤ n := by
      rw [hn]
      by_cases z : t=0
      · rw [z]; exact (by decide : 4^0+4≤4^2).trans (Nat.pow_le_pow_right (by decide) hs)
      · have pt : 1 ≤ t := by omega
        have bnd := Nat.pow_le_pow_right (by decide : 0<4) pt
        have st := Nat.pow_le_pow_right (by decide : 0<4) (show t+1 ≤ s by omega)
        rw [pow_succ] at st
        simp only [pow_one] at bnd
        omega
    omega
  have large : 2 ≤ t := by omega
  have nonzero (p q : V t) : (∏ j,fac E.gamma E.A E.B p q j) ≠ 0 := by
    intro bad
    obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp bad
    have zz : fr E.gamma E.A E.B p q j=0 := by
      by_contra nz
      simp [fac,nz] at hj
      split_ifs at hj <;> norm_num at hj
    have four := fourZeros large E.gamma E.A E.B j p q zz
    have zcap : 4 ≤ Sᶜ.card := by
      convert four using 2
      ext x
      rcases x with ⟨p,q⟩
      simp [S,spectrum] <;> rfl
    have gap : S.card + 4 ≤ n := by
      rw [hn,←equal,←paircard t]
      have := Finset.card_compl_add_card S
      omega
    omega
  obtain ⟨ones,bare⟩ := fullSupport _ _ _ nonzero
  have h := simpleTable E K evK ones bare
  change ∃ (r c : Fin n→V2 s) (u v : Sampling.V n), K=predT r c u v
  rw [←equal]; exact h
end PEqualNP.Outside.L_meta_25783_aux.Work



namespace PEqualNP.Outside.L_meta_25783_aux.Rigidity

private def sgn (b : Bool) : ℤ := if b then -1 else 1

private lemma sgn_false : sgn false = 1 := rfl

private lemma sgn_true : sgn true = -1 := rfl

private lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> rfl

private lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> rfl

private lemma sgn_inj {a b : Bool} (h : sgn a = sgn b) : a = b := by
  cases a <;> cases b <;> simp [sgn] at h <;> rfl

private lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by
  cases b <;> decide

private lemma sgn_abs (b : Bool) : |sgn b| = 1 := by
  cases b <;> decide

private lemma sgn_mul_eq_sub (a b : Bool) :
    sgn a * sgn b = 1 - 2 * (if a ≠ b then (1 : ℤ) else 0) := by
  cases a <;> cases b <;> decide

private def isHad {N : ℕ} (M : Fin N → Fin N → Bool) : Prop :=
  ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N

private def sampleFn {N : ℕ} (D : Fin N → Fin N → Bool) (r c : Fin N → Fin N)
    (u v : Fin N → Bool) (i j : Fin N) : Bool :=
  xor (xor (u i) (v j)) (D (r i) (c j))

private def errorsFn {N : ℕ} (A B : Fin N → Fin N → Bool) : ℕ :=
  ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => A i j ≠ B i j)).card

private def editFn {N : ℕ} (H : Fin N → Fin N → Bool) (i j k l : Fin N) (f g : Bool)
    (x y : Fin N) : Bool :=
  xor (xor (if x = i ∧ i ≠ j then f else false) (if y = k ∧ k ≠ l then g else false))
    (H (if x = i then j else x) (if y = k then l else y))

private def errInd {N : ℕ} (A B : Fin N → Fin N → Bool) (i j : Fin N) : ℕ :=
  if A i j ≠ B i j then 1 else 0

private lemma errors_eq_sum_ind {N : ℕ} (A B : Fin N → Fin N → Bool) :
    errorsFn A B = ∑ i : Fin N, ∑ j : Fin N, errInd A B i j := by
  simp only [errorsFn, errInd, Finset.card_filter]

private lemma had_row_dot_self {N : ℕ} (M : Fin N → Fin N → Bool) (a : Fin N) :
    ∑ j : Fin N, sgn (M a j) * sgn (M a j) = (N : ℤ) := by
  simp [sgn_mul_self]

private lemma had_row_dot_ne {N : ℕ} {M : Fin N → Fin N → Bool} (hM : isHad M)
    {a b : Fin N} (hab : a ≠ b) :
    ∑ j : Fin N, sgn (M a j) * sgn (M b j) = 0 := by
  have h1 : ∀ j : Fin N,
      sgn (M a j) * sgn (M b j) = 1 - 2 * (if M a j ≠ M b j then (1 : ℤ) else 0) :=
    fun j => sgn_mul_eq_sub (M a j) (M b j)
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.sum_boole]
  have h2 := hM a b hab
  omega

private lemma had_row_dot {N : ℕ} {M : Fin N → Fin N → Bool} (hM : isHad M) (a b : Fin N) :
    ∑ j : Fin N, sgn (M a j) * sgn (M b j) = if a = b then (N : ℤ) else 0 := by
  by_cases h : a = b
  · subst h
    simp [had_row_dot_self]
  · simp [h, had_row_dot_ne hM h]

private lemma had_col_dot {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    (j₁ j₂ : Fin N) :
    ∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) = if j₁ = j₂ then (N : ℤ) else 0 := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  let f : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) :=
    { toFun := fun v i => ∑ j : Fin N, (sgn (M i j) : ℚ) * v j
      map_add' := fun u v => by
        ext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring }
  let g : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) :=
    { toFun := fun v j => (N : ℚ)⁻¹ * ∑ i : Fin N, (sgn (M i j) : ℚ) * v i
      map_add' := fun u v => by
        ext j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        ext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum, Finset.mul_sum]
        have hterm : ∀ i : Fin N,
            (N : ℚ)⁻¹ * ((sgn (M i j) : ℚ) * (c * v i)) =
            c * ((N : ℚ)⁻¹ * ((sgn (M i j) : ℚ) * v i)) := fun i => by ring
        simp_rw [hterm, ← Finset.mul_sum] }
  have hfg : ∀ v : Fin N → ℚ, f (g v) = v := by
    intro v
    ext a
    simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk]
    calc
      ∑ j : Fin N, (sgn (M a j) : ℚ) * ((N : ℚ)⁻¹ * ∑ b : Fin N, (sgn (M b j) : ℚ) * v b)
          = ∑ j : Fin N, ∑ b : Fin N,
              (N : ℚ)⁻¹ * v b * ((sgn (M a j) : ℚ) * (sgn (M b j) : ℚ)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b : Fin N, ∑ j : Fin N,
            (N : ℚ)⁻¹ * v b * ((sgn (M a j) : ℚ) * (sgn (M b j) : ℚ)) := Finset.sum_comm
      _ = ∑ b : Fin N, (N : ℚ)⁻¹ * v b *
            ((∑ j : Fin N, sgn (M a j) * sgn (M b j) : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [← Finset.mul_sum]
            push_cast
            rfl
      _ = ∑ b : Fin N, (N : ℚ)⁻¹ * v b * ((if a = b then (N : ℤ) else 0 : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl fun b _ => by rw [had_row_dot hM a b]
      _ = (N : ℚ)⁻¹ * v a * (N : ℚ) := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro b _ hba
              simp [Ne.symm hba]
            · intro h
              exact absurd (Finset.mem_univ a) h
      _ = v a := by
            rw [mul_comm ((N : ℚ)⁻¹), mul_assoc, inv_mul_cancel₀ hNq, mul_one]
  have hsurj : Function.Surjective f := fun v => ⟨g v, hfg v⟩
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  have hgf : ∀ v : Fin N → ℚ, g (f v) = v := fun v => hinj (hfg (f v))
  let e : Fin N → ℚ := fun k => if k = j₂ then 1 else 0
  have he := congr_fun (hgf e) j₁
  simp only [f, g, LinearMap.coe_mk, AddHom.coe_mk] at he
  have hfe : ∀ i : Fin N, ∑ j : Fin N, (sgn (M i j) : ℚ) * e j = (sgn (M i j₂) : ℚ) := by
    intro i
    rw [Finset.sum_eq_single j₂]
    · simp [e]
    · intro j _ hne
      simp [e, hne]
    · intro h
      exact absurd (Finset.mem_univ j₂) h
  simp_rw [hfe] at he
  have hsum :
      (N : ℚ)⁻¹ * ((∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) : ℤ) : ℚ) =
      if j₁ = j₂ then 1 else 0 := by
    push_cast
    simpa only [e] using he
  have hmul : ((∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) : ℤ) : ℚ) =
      ((if j₁ = j₂ then (N : ℤ) else 0 : ℤ) : ℚ) := by
    have h1 := congr_arg (fun t => (N : ℚ) * t) hsum
    simp only [← mul_assoc, mul_inv_cancel₀ hNq, one_mul] at h1
    by_cases hj : j₁ = j₂
    · simp [hj] at h1 ⊢
      exact h1
    · simp [hj] at h1 ⊢
      exact h1
  exact Int.cast_injective hmul

private lemma had_transpose {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M) :
    isHad (fun j i => M i j) := by
  intro a b hab
  dsimp only
  have h0 := had_col_dot hN hM a b
  simp only [hab, ↓reduceIte] at h0
  have h1 : ∀ i : Fin N,
      sgn (M i a) * sgn (M i b) = 1 - 2 * (if M i a ≠ M i b then (1 : ℤ) else 0) :=
    fun i => sgn_mul_eq_sub (M i a) (M i b)
  simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum] at h0
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.sum_boole] at h0
  omega

private lemma had_row_flip_count {N : ℕ} {M : Fin N → Fin N → Bool} (hM : isHad M)
    {a b : Fin N} (hab : a ≠ b) (s : Bool) :
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor s (M b j))).card = N := by
  cases s
  · simpa using hM a b hab
  · have hdisj : Disjoint
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j)))
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      cases ha : M a j <;> cases hb : M b j <;> simp_all
    have hunion :
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j))) ∪
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)) = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases M a j <;> cases M b j <;> decide
    have hpart :
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j))).card +
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have h0 := hM a b hab
    omega

private lemma had_col_flip_count {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    {a b : Fin N} (hab : a ≠ b) (s : Bool) :
    2 * ((Finset.univ : Finset (Fin N)).filter (fun i => M i a ≠ xor s (M i b))).card = N :=
  had_row_flip_count (had_transpose hN hM) hab s

private lemma had_row_expand {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    (z : Fin N → ℤ) (j : Fin N) :
    (N : ℤ) * z j = ∑ a : Fin N, (∑ t : Fin N, z t * sgn (M a t)) * sgn (M a j) := by
  calc
    (N : ℤ) * z j = ∑ t : Fin N, z t * (if t = j then (N : ℤ) else 0) := by
      simp [mul_comm]
    _ = ∑ t : Fin N, z t * (∑ a : Fin N, sgn (M a t) * sgn (M a j)) := by
      refine Finset.sum_congr rfl fun t _ => by rw [had_col_dot hN hM t j]
    _ = ∑ t : Fin N, ∑ a : Fin N, z t * (sgn (M a t) * sgn (M a j)) := by
      refine Finset.sum_congr rfl fun t _ => Finset.mul_sum ..
    _ = ∑ a : Fin N, ∑ t : Fin N, z t * (sgn (M a t) * sgn (M a j)) := Finset.sum_comm
    _ = ∑ a : Fin N, (∑ t : Fin N, z t * sgn (M a t)) * sgn (M a j) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => by ring

private lemma had_uncertainty {N : ℕ} (hN : 0 < N) {M : Fin N → Fin N → Bool} (hM : isHad M)
    (x : Fin N → ℤ) (hx : x ≠ 0) :
    N ≤ ((Finset.univ : Finset (Fin N)).filter (fun j => x j ≠ 0)).card *
      ((Finset.univ : Finset (Fin N)).filter
        (fun a => ∑ j : Fin N, sgn (M a j) * x j ≠ 0)).card := by
  let y : Fin N → ℤ := fun a => ∑ j : Fin N, sgn (M a j) * x j
  let A : Finset (Fin N) := Finset.univ.filter (fun j => x j ≠ 0)
  let B : Finset (Fin N) := Finset.univ.filter (fun a => y a ≠ 0)
  have hpar : ∑ a : Fin N, y a ^ 2 = (N : ℤ) * ∑ j : Fin N, x j ^ 2 := by
    calc
      ∑ a : Fin N, y a ^ 2
          = ∑ a : Fin N, ∑ j₁ : Fin N, ∑ j₂ : Fin N,
              (x j₁ * x j₂) * (sgn (M a j₁) * sgn (M a j₂)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [y, sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j₁ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j₂ _ => by ring
      _ = ∑ j₁ : Fin N, ∑ a : Fin N, ∑ j₂ : Fin N,
            (x j₁ * x j₂) * (sgn (M a j₁) * sgn (M a j₂)) := Finset.sum_comm
      _ = ∑ j₁ : Fin N, ∑ j₂ : Fin N, ∑ a : Fin N,
            (x j₁ * x j₂) * (sgn (M a j₁) * sgn (M a j₂)) := by
            refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_comm
      _ = ∑ j₁ : Fin N, ∑ j₂ : Fin N,
            (x j₁ * x j₂) * (∑ a : Fin N, sgn (M a j₁) * sgn (M a j₂)) := by
            refine Finset.sum_congr rfl fun j₁ _ =>
              Finset.sum_congr rfl fun j₂ _ => (Finset.mul_sum ..).symm
      _ = ∑ j₁ : Fin N, ∑ j₂ : Fin N,
            (x j₁ * x j₂) * (if j₁ = j₂ then (N : ℤ) else 0) := by
            refine Finset.sum_congr rfl fun j₁ _ =>
              Finset.sum_congr rfl fun j₂ _ => by rw [had_col_dot hN hM j₁ j₂]
      _ = ∑ j₁ : Fin N, (N : ℤ) * x j₁ ^ 2 := by
            refine Finset.sum_congr rfl fun j₁ _ => ?_
            rw [Finset.sum_eq_single j₁]
            · simp [sq, mul_comm]
            · intro j₂ _ hne
              simp [Ne.symm hne]
            · intro h
              exact absurd (Finset.mem_univ j₁) h
      _ = (N : ℤ) * ∑ j : Fin N, x j ^ 2 := (Finset.mul_sum ..).symm
  have hy_bound : ∀ a : Fin N, |y a| ≤ ∑ j ∈ A, |x j| := by
    intro a
    calc
      |y a| ≤ ∑ j : Fin N, |sgn (M a j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin N, |x j| := by
            refine Finset.sum_congr rfl fun j _ => by rw [abs_mul, sgn_abs, one_mul]
      _ = ∑ j ∈ A, |x j| := by
            symm
            refine Finset.sum_subset (Finset.subset_univ A) ?_
            intro j _ hj
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
            simp [hj]
  have hy2 : ∑ a : Fin N, y a ^ 2 ≤ (B.card : ℤ) * (∑ j ∈ A, |x j|) ^ 2 := by
    have hsub : ∑ a : Fin N, y a ^ 2 = ∑ a ∈ B, y a ^ 2 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ B) ?_
      intro a _ ha
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
      simp [ha]
    rw [hsub]
    calc
      ∑ a ∈ B, y a ^ 2 ≤ ∑ _a ∈ B, (∑ j ∈ A, |x j|) ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hy_bound a) 2
      _ = (B.card : ℤ) * (∑ j ∈ A, |x j|) ^ 2 := by simp
  have hcs : (∑ j ∈ A, |x j|) ^ 2 ≤ (A.card : ℤ) * ∑ j : Fin N, x j ^ 2 := by
    have hnn : (0 : ℤ) ≤ ∑ j₁ ∈ A, ∑ j₂ ∈ A, (|x j₁| - |x j₂|) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp :
        ∑ j₁ ∈ A, ∑ j₂ ∈ A, (|x j₁| - |x j₂|) ^ 2 =
        2 * ((A.card : ℤ) * ∑ j ∈ A, |x j| ^ 2 - (∑ j ∈ A, |x j|) ^ 2) := by
      have h1 : ∀ j₁ j₂ : Fin N,
          (|x j₁| - |x j₂|) ^ 2 = |x j₁| ^ 2 + |x j₂| ^ 2 - 2 * (|x j₁| * |x j₂|) :=
        fun j₁ j₂ => by ring
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hA_le : (∑ j ∈ A, |x j|) ^ 2 ≤ (A.card : ℤ) * ∑ j ∈ A, x j ^ 2 := by
      have h2 : (∑ j ∈ A, |x j|) ^ 2 ≤ (A.card : ℤ) * ∑ j ∈ A, |x j| ^ 2 := by linarith
      simpa [sq_abs] using h2
    exact le_trans hA_le (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ => sq_nonneg _))
      (Nat.cast_nonneg _))
  have hQ : 0 < ∑ j : Fin N, x j ^ 2 := by
    have hex : ∃ j : Fin N, x j ≠ 0 := Function.ne_iff.mp hx
    rcases hex with ⟨j₀, hj₀⟩
    have hpos : 0 < x j₀ ^ 2 := sq_pos_of_ne_zero hj₀
    exact lt_of_lt_of_le hpos
      (Finset.single_le_sum (f := fun j => x j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j₀))
  have hkey : (N : ℤ) * ∑ j : Fin N, x j ^ 2 ≤
      ((A.card * B.card : ℕ) : ℤ) * ∑ j : Fin N, x j ^ 2 := by
    rw [← hpar]
    calc
      ∑ a : Fin N, y a ^ 2 ≤ (B.card : ℤ) * (∑ j ∈ A, |x j|) ^ 2 := hy2
      _ ≤ (B.card : ℤ) * ((A.card : ℤ) * ∑ j : Fin N, x j ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)
      _ = ((A.card * B.card : ℕ) : ℤ) * ∑ j : Fin N, x j ^ 2 := by
            push_cast
            ring
  have hle : (N : ℤ) ≤ ((A.card * B.card : ℕ) : ℤ) := le_of_mul_le_mul_right hkey hQ
  exact_mod_cast hle

private lemma extend_partial_bij {β : Type*} [Fintype β] [DecidableEq β]
    (S T : Finset β) (e1 : S ≃ T) :
    ∃ π : Equiv.Perm β, ∀ x (hx : x ∈ S), π x = (e1 ⟨x, hx⟩).1 := by
  have hcardST : S.card = T.card := by
    have h1 := Fintype.card_congr e1
    simpa [Fintype.card_coe] using h1
  have hcardC : Fintype.card (Sᶜ : Finset β) = Fintype.card (Tᶜ : Finset β) := by
    simp only [Fintype.card_coe, Finset.card_compl, hcardST]
  let e2 : (Sᶜ : Finset β) ≃ (Tᶜ : Finset β) := Fintype.equivOfCardEq hcardC
  let f : β → β := fun x =>
    if hx : x ∈ S then (e1 ⟨x, hx⟩).1 else (e2 ⟨x, Finset.mem_compl.mpr hx⟩).1
  have hinj : Function.Injective f := by
    intro x₁ x₂ h
    by_cases hx₁ : x₁ ∈ S <;> by_cases hx₂ : x₂ ∈ S
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hsub : e1 ⟨x₁, hx₁⟩ = e1 ⟨x₂, hx₂⟩ := Subtype.ext h
      exact congr_arg Subtype.val (e1.injective hsub)
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hm1 : (e1 ⟨x₁, hx₁⟩).1 ∈ T := (e1 ⟨x₁, hx₁⟩).2
      have hm2 : (e2 ⟨x₂, Finset.mem_compl.mpr hx₂⟩).1 ∈ Tᶜ :=
        (e2 ⟨x₂, Finset.mem_compl.mpr hx₂⟩).2
      rw [h] at hm1
      exact absurd hm1 (Finset.mem_compl.mp hm2)
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hm1 : (e2 ⟨x₁, Finset.mem_compl.mpr hx₁⟩).1 ∈ Tᶜ :=
        (e2 ⟨x₁, Finset.mem_compl.mpr hx₁⟩).2
      have hm2 : (e1 ⟨x₂, hx₂⟩).1 ∈ T := (e1 ⟨x₂, hx₂⟩).2
      rw [← h] at hm2
      exact absurd hm2 (Finset.mem_compl.mp hm1)
    · simp only [f, hx₁, hx₂, ↓reduceDIte] at h
      have hsub : e2 ⟨x₁, Finset.mem_compl.mpr hx₁⟩ = e2 ⟨x₂, Finset.mem_compl.mpr hx₂⟩ :=
        Subtype.ext h
      exact congr_arg Subtype.val (e2.injective hsub)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  intro x hx
  simp only [Equiv.ofBijective_apply, f, hx, ↓reduceDIte]

private lemma extend_injOn_perm {N : ℕ} (S : Finset (Fin N)) (f : Fin N → Fin N)
    (hinj : Set.InjOn f S) :
    ∃ p : Equiv.Perm (Fin N), ∀ x ∈ S, p x = f x := by
  let T : Finset (Fin N) := S.image f
  let g : S → T := fun x => ⟨f x.1, Finset.mem_image_of_mem f x.2⟩
  have hginj : Function.Injective g := by
    intro x₁ x₂ h
    exact Subtype.ext (hinj x₁.2 x₂.2 (congr_arg Subtype.val h))
  have hgsurj : Function.Surjective g := by
    intro y
    rcases Finset.mem_image.mp y.2 with ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  rcases extend_partial_bij S T (Equiv.ofBijective g ⟨hginj, hgsurj⟩) with ⟨p, hp⟩
  exact ⟨p, fun x hx => hp x hx⟩

private lemma extend_perm_on_finset {N : ℕ} (C : Finset (Fin N))
    (eC : Fin C.card ≃ C) (σ : Equiv.Perm (Fin C.card)) :
    ∃ c : Equiv.Perm (Fin N),
      (∀ j ∉ C, c j = j) ∧
      ∀ j (hj : j ∈ C), c j = (eC (σ (eC.symm ⟨j, hj⟩))).1 := by
  let f : Fin N → Fin N := fun j =>
    if hj : j ∈ C then (eC (σ (eC.symm ⟨j, hj⟩))).1 else j
  have hinj : Function.Injective f := by
    intro j₁ j₂ h
    by_cases h1 : j₁ ∈ C <;> by_cases h2 : j₂ ∈ C
    · simp only [f, h1, h2, ↓reduceDIte] at h
      have hs : eC (σ (eC.symm ⟨j₁, h1⟩)) = eC (σ (eC.symm ⟨j₂, h2⟩)) := Subtype.ext h
      have hs2 := eC.symm.injective (σ.injective (eC.injective hs))
      exact congr_arg Subtype.val hs2
    · simp only [f, h1, h2, ↓reduceDIte] at h
      have hm : (eC (σ (eC.symm ⟨j₁, h1⟩))).1 ∈ C := (eC (σ (eC.symm ⟨j₁, h1⟩))).2
      rw [h] at hm
      exact absurd hm h2
    · simp only [f, h1, h2, ↓reduceDIte] at h
      have hm : (eC (σ (eC.symm ⟨j₂, h2⟩))).1 ∈ C := (eC (σ (eC.symm ⟨j₂, h2⟩))).2
      rw [← h] at hm
      exact absurd hm h1
    · simp only [f, h1, h2, ↓reduceDIte] at h
      exact h
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_, ?_⟩
  · intro j hj
    simp only [Equiv.ofBijective_apply, f, hj, ↓reduceDIte]
  · intro j hj
    simp only [Equiv.ofBijective_apply, f, hj, ↓reduceDIte]

private def evenVec (a : Fin 4) (t : Fin 3) : Bool :=
  match a.val with
  | 0 => false
  | 1 => decide (t ≠ 0)
  | 2 => decide (t ≠ 1)
  | _ => decide (t ≠ 2)

private def xor4 (a b : Fin 4) : Fin 4 :=
  match a.val, b.val with
  | 0, _ => b
  | _, 0 => a
  | 1, 1 => 0
  | 1, 2 => 3
  | 1, 3 => 2
  | 2, 1 => 3
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 1 => 2
  | 3, 2 => 1
  | _, _ => 0

private lemma xor4_self (a : Fin 4) : xor4 a a = 0 := by
  fin_cases a <;> rfl

private lemma xor4_zero_left (a : Fin 4) : xor4 0 a = a := by
  fin_cases a <;> rfl

private lemma xor4_assoc (a b c : Fin 4) : xor4 a (xor4 b c) = xor4 (xor4 a b) c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

private lemma evenVec_xor4 (a b : Fin 4) (t : Fin 3) :
    evenVec (xor4 a b) t = xor (evenVec a t) (evenVec b t) := by
  fin_cases a <;> fin_cases b <;> fin_cases t <;> rfl

private lemma evenVec_succ (r t : Fin 3) :
    evenVec r.succ t = decide (t ≠ r) := by
  fin_cases r <;> fin_cases t <;> rfl

private lemma evenVec_dot (a b : Fin 4) :
    ∑ t : Fin 3, sgn (evenVec a t) * sgn (evenVec b t) = if a = b then 3 else -1 := by
  fin_cases a <;> fin_cases b <;> decide

private def par3 (v : Fin 3 → Bool) : Bool :=
  xor (v 0) (xor (v 1) (v 2))

private def code3 (v : Fin 3 → Bool) : Fin 4 :=
  match xor (par3 v) (v 0), xor (par3 v) (v 1) with
  | false, false => 0
  | false, true  => 1
  | true,  false => 2
  | true,  true  => 3

private lemma vec3_decomp (v : Fin 3 → Bool) (t : Fin 3) :
    v t = xor (par3 v) (evenVec (code3 v) t) := by
  have h : ∀ (b0 b1 b2 : Bool) (t : Fin 3),
      v 0 = b0 → v 1 = b1 → v 2 = b2 →
      v t = xor (par3 v) (evenVec (code3 v) t) := by
    intro b0 b1 b2 t h0 h1 h2
    fin_cases t
    · change v 0 = xor (par3 v) (evenVec (code3 v) 0)
      simp only [par3, code3, h0, h1, h2]
      cases b0 <;> cases b1 <;> cases b2 <;> rfl
    · change v 1 = xor (par3 v) (evenVec (code3 v) 1)
      simp only [par3, code3, h0, h1, h2]
      cases b0 <;> cases b1 <;> cases b2 <;> rfl
    · change v 2 = xor (par3 v) (evenVec (code3 v) 2)
      simp only [par3, code3, h0, h1, h2]
      cases b0 <;> cases b1 <;> cases b2 <;> rfl
  exact h (v 0) (v 1) (v 2) t rfl rfl rfl

private lemma dot3_formula (u v : Fin 3 → Bool) :
    ∑ t : Fin 3, sgn (u t) * sgn (v t) =
      sgn (par3 u) * sgn (par3 v) * (if code3 u = code3 v then 3 else -1) := by
  have h1 : ∀ t : Fin 3,
      sgn (u t) * sgn (v t) =
        sgn (par3 u) * sgn (par3 v) * (sgn (evenVec (code3 u) t) * sgn (evenVec (code3 v) t)) := by
    intro t
    rw [vec3_decomp u t, vec3_decomp v t, sgn_xor, sgn_xor]
    ring
  simp_rw [h1, ← Finset.mul_sum, evenVec_dot]

private lemma dot3_eq_iff (u v u' v' : Fin 3 → Bool)
    (h : ∑ t : Fin 3, sgn (u t) * sgn (v t) = ∑ t : Fin 3, sgn (u' t) * sgn (v' t)) :
    (code3 u = code3 v ↔ code3 u' = code3 v') ∧ (par3 u = par3 v ↔ par3 u' = par3 v') := by
  rw [dot3_formula, dot3_formula] at h
  by_cases hc1 : code3 u = code3 v <;> by_cases hc2 : code3 u' = code3 v' <;>
    cases hp1 : par3 u <;> cases hp2 : par3 v <;>
    cases hp3 : par3 u' <;> cases hp4 : par3 v' <;>
    simp [hc1, hc2, hp1, hp2, hp3, hp4, sgn] at h ⊢

private lemma realize_perm_fin4 (π : Equiv.Perm (Fin 4)) (s : Bool) :
    ∃ (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → Bool),
      ∀ v : Fin 3 → Bool, ∀ t : Fin 3,
        xor (w t) (v (σ t)) = xor (xor s (par3 v)) (evenVec (π (code3 v)) t) := by
  let j : Fin 4 := π 0
  let π' : Fin 4 → Fin 4 := fun i => xor4 j (π i)
  have hπ'0 : π' 0 = 0 := xor4_self j
  have hπ'inj : Function.Injective π' := by
    intro a b h
    have h1 := congr_arg (xor4 j) h
    simp only [π', xor4_assoc, xor4_self, xor4_zero_left] at h1
    exact π.injective h1
  have hne0 : ∀ r : Fin 3, π' r.succ ≠ 0 := by
    intro r h
    rw [← hπ'0] at h
    exact Fin.succ_ne_zero r (hπ'inj h)
  let τ_fun : Fin 3 → Fin 3 := fun r => (π' r.succ).pred (hne0 r)
  have hτ_succ : ∀ r : Fin 3, (τ_fun r).succ = π' r.succ := fun r => Fin.succ_pred _ _
  have hτ_inj : Function.Injective τ_fun := by
    intro r₁ r₂ h
    have h1 := congr_arg Fin.succ h
    rw [hτ_succ, hτ_succ] at h1
    exact Fin.succ_injective _ (hπ'inj h1)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective τ_fun (Finite.injective_iff_bijective.mp hτ_inj)
  let σ : Equiv.Perm (Fin 3) := τ.symm
  let w : Fin 3 → Bool := fun t => xor s (evenVec j t)
  have hact_even : ∀ i : Fin 4, ∀ t : Fin 3,
      xor (evenVec j t) (evenVec i (σ t)) = evenVec (π i) t := by
    intro i t
    refine Fin.cases ?_ ?_ i
    · have h0 : evenVec 0 (σ t) = false := rfl
      rw [h0, Bool.xor_false]
    · intro r
      rw [evenVec_succ]
      have hdec : decide (σ t ≠ r) = decide (t ≠ τ r) := by
        simp only [σ, ne_eq, Equiv.symm_apply_eq]
      rw [hdec, ← evenVec_succ (τ r) t]
      have hsucc : (τ r).succ = xor4 j (π r.succ) := hτ_succ r
      rw [hsucc, ← evenVec_xor4, xor4_assoc, xor4_self, xor4_zero_left]
  refine ⟨σ, w, ?_⟩
  intro v t
  rw [vec3_decomp v (σ t)]
  have hx : xor (xor s (evenVec j t)) (xor (par3 v) (evenVec (code3 v) (σ t))) =
      xor (xor s (par3 v)) (xor (evenVec j t) (evenVec (code3 v) (σ t))) := by
    cases s <;> cases evenVec j t <;> cases par3 v <;> cases evenVec (code3 v) (σ t) <;> rfl
  change xor (xor s (evenVec j t)) (xor (par3 v) (evenVec (code3 v) (σ t))) = _
  rw [hx, hact_even (code3 v) t]

private lemma bool2_unique :
    ∀ a0 a1 b0 b1 c0 c1 : Bool,
      c0 ≠ c1 →
      sgn a0 + sgn a1 = sgn b0 + sgn b1 →
      sgn a0 * sgn c0 + sgn a1 * sgn c1 = sgn b0 * sgn c0 + sgn b1 * sgn c1 →
      a0 = b0 ∧ a1 = b1 := by
  decide

private lemma bool2_diag :
    ∀ a0 a1 b0 b1 : Bool,
      a0 = a1 →
      sgn a0 + sgn a1 = sgn b0 + sgn b1 →
      a0 = b0 ∧ a1 = b1 := by
  decide

private lemma bool2_swap :
    ∀ a0 a1 b0 b1 : Bool,
      a0 ≠ a1 →
      sgn a0 + sgn a1 = sgn b0 + sgn b1 →
      (if a0 = b0 then b0 else b1) = a0 ∧ (if a0 = b0 then b1 else b0) = a1 := by
  decide

private lemma xor_cancel_align :
    ∀ a b c d : Bool, xor a c = xor b d → c = xor (xor a b) d := by
  decide

private lemma align_gram_two {α : Type*} (x y : α → Fin 2 → Bool)
    (hgram : ∀ a b : α,
      ∑ t : Fin 2, sgn (x a t) * sgn (x b t) = ∑ t : Fin 2, sgn (y a t) * sgn (y b t)) :
    ∃ (σ : Equiv.Perm (Fin 2)) (w : Fin 2 → Bool),
      ∀ a : α, ∀ t : Fin 2, x a t = xor (w t) (y a (σ t)) := by
  by_cases hne : Nonempty α
  · rcases hne with ⟨a₀⟩
    let x' : α → Fin 2 → Bool := fun a t => xor (x a₀ t) (x a t)
    let y' : α → Fin 2 → Bool := fun a t => xor (y a₀ t) (y a t)
    have hgram' : ∀ a b : α,
        ∑ t : Fin 2, sgn (x' a t) * sgn (x' b t) =
        ∑ t : Fin 2, sgn (y' a t) * sgn (y' b t) := by
      intro a b
      have hx : ∀ t : Fin 2, sgn (x' a t) * sgn (x' b t) = sgn (x a t) * sgn (x b t) := by
        intro t
        simp only [x', sgn_xor]
        have hsq := sgn_mul_self (x a₀ t)
        calc
          sgn (x a₀ t) * sgn (x a t) * (sgn (x a₀ t) * sgn (x b t))
              = (sgn (x a₀ t) * sgn (x a₀ t)) * (sgn (x a t) * sgn (x b t)) := by ring
          _ = sgn (x a t) * sgn (x b t) := by rw [hsq, one_mul]
      have hy : ∀ t : Fin 2, sgn (y' a t) * sgn (y' b t) = sgn (y a t) * sgn (y b t) := by
        intro t
        simp only [y', sgn_xor]
        have hsq := sgn_mul_self (y a₀ t)
        calc
          sgn (y a₀ t) * sgn (y a t) * (sgn (y a₀ t) * sgn (y b t))
              = (sgn (y a₀ t) * sgn (y a₀ t)) * (sgn (y a t) * sgn (y b t)) := by ring
          _ = sgn (y a t) * sgn (y b t) := by rw [hsq, one_mul]
      simp_rw [hx, hy]
      exact hgram a b
    have hx0 : ∀ t : Fin 2, x' a₀ t = false := fun t => Bool.xor_self (x a₀ t)
    have hy0 : ∀ t : Fin 2, y' a₀ t = false := fun t => Bool.xor_self (y a₀ t)
    have hsum0 : ∀ a : α, sgn (x' a 0) + sgn (x' a 1) = sgn (y' a 0) + sgn (y' a 1) := by
      intro a
      have h := hgram' a a₀
      simp only [Fin.sum_univ_two, hx0, hy0, sgn_false, mul_one] at h
      exact h
    by_cases h1 : ∃ a₁ : α, x' a₁ 0 ≠ x' a₁ 1
    · rcases h1 with ⟨a₁, ha₁⟩
      let σ : Equiv.Perm (Fin 2) :=
        if x' a₁ 0 = y' a₁ 0 then Equiv.refl _ else Equiv.swap 0 1
      let y'' : α → Fin 2 → Bool := fun a t => y' a (σ t)
      have hgram'' : ∀ a b : α,
          sgn (x' a 0) * sgn (x' b 0) + sgn (x' a 1) * sgn (x' b 1) =
          sgn (y'' a 0) * sgn (y'' b 0) + sgn (y'' a 1) * sgn (y'' b 1) := by
        intro a b
        have h := hgram' a b
        simp only [Fin.sum_univ_two] at h
        by_cases hc : x' a₁ 0 = y' a₁ 0
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.refl_apply]
          exact h
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.swap_apply_left, Equiv.swap_apply_right]
          linarith
      have hy''0 : y'' a₀ 0 = false ∧ y'' a₀ 1 = false := ⟨hy0 (σ 0), hy0 (σ 1)⟩
      have hy''1 : y'' a₁ 0 = x' a₁ 0 ∧ y'' a₁ 1 = x' a₁ 1 := by
        have hsw := bool2_swap (x' a₁ 0) (x' a₁ 1) (y' a₁ 0) (y' a₁ 1) ha₁ (hsum0 a₁)
        by_cases hc : x' a₁ 0 = y' a₁ 0
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.refl_apply] at hsw ⊢
          exact hsw
        · simp only [y'', σ, hc, ↓reduceIte, Equiv.swap_apply_left, Equiv.swap_apply_right] at hsw ⊢
          exact hsw
      have hxy : ∀ a : α, ∀ t : Fin 2, x' a t = y'' a t := by
        intro a t
        have hg0 := hgram'' a a₀
        have hg1 := hgram'' a a₁
        rw [hx0 0, hx0 1, hy''0.1, hy''0.2, sgn_false, mul_one, mul_one, mul_one, mul_one] at hg0
        rw [hy''1.1, hy''1.2] at hg1
        have hpair := bool2_unique (x' a 0) (x' a 1) (y'' a 0) (y'' a 1)
          (x' a₁ 0) (x' a₁ 1) ha₁ hg0 hg1
        fin_cases t
        · exact hpair.1
        · exact hpair.2
      refine ⟨σ, fun t => xor (x a₀ t) (y a₀ (σ t)), ?_⟩
      intro a t
      exact xor_cancel_align (x a₀ t) (y a₀ (σ t)) (x a t) (y a (σ t)) (hxy a t)
    · push Not at h1
      refine ⟨Equiv.refl _, fun t => xor (x a₀ t) (y a₀ t), ?_⟩
      intro a t
      have hpair := bool2_diag (x' a 0) (x' a 1) (y' a 0) (y' a 1) (h1 a) (hsum0 a)
      have ht : x' a t = y' a t := by
        fin_cases t
        · exact hpair.1
        · exact hpair.2
      exact xor_cancel_align (x a₀ t) (y a₀ t) (x a t) (y a t) ht
  · exact ⟨Equiv.refl _, fun _ => false, fun a => False.elim (hne ⟨a⟩)⟩

private lemma align_gram_three {α : Type*} (x y : α → Fin 3 → Bool)
    (hgram : ∀ a b : α,
      ∑ t : Fin 3, sgn (x a t) * sgn (x b t) = ∑ t : Fin 3, sgn (y a t) * sgn (y b t)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (w : Fin 3 → Bool),
      ∀ a : α, ∀ t : Fin 3, x a t = xor (w t) (y a (σ t)) := by
  classical
  by_cases hne : Nonempty α
  · rcases hne with ⟨a₀⟩
    have hiff : ∀ a b : α,
        (code3 (x a) = code3 (x b) ↔ code3 (y a) = code3 (y b)) ∧
        (par3 (x a) = par3 (x b) ↔ par3 (y a) = par3 (y b)) :=
      fun a b => dot3_eq_iff (x a) (x b) (y a) (y b) (hgram a b)
    let s : Bool := xor (par3 (x a₀)) (par3 (y a₀))
    have hpar : ∀ a : α, par3 (x a) = xor s (par3 (y a)) := by
      intro a
      have hp := (hiff a a₀).2
      simp only [s]
      cases h1 : par3 (x a) <;> cases h2 : par3 (x a₀) <;>
        cases h3 : par3 (y a) <;> cases h4 : par3 (y a₀) <;>
        simp_all
    let imgY : Finset (Fin 4) := Finset.univ.filter (fun u => ∃ a : α, code3 (y a) = u)
    let imgX : Finset (Fin 4) := Finset.univ.filter (fun u => ∃ a : α, code3 (x a) = u)
    have hmemY : ∀ u : Fin 4, u ∈ imgY ↔ ∃ a : α, code3 (y a) = u := by
      intro u
      simp [imgY]
    have hmemX : ∀ u : Fin 4, u ∈ imgX ↔ ∃ a : α, code3 (x a) = u := by
      intro u
      simp [imgX]
    let toFun : imgY → imgX := fun u =>
      ⟨code3 (x (Classical.choose ((hmemY u.1).mp u.2))),
       (hmemX _).mpr ⟨Classical.choose ((hmemY u.1).mp u.2), rfl⟩⟩
    let invFun : imgX → imgY := fun u =>
      ⟨code3 (y (Classical.choose ((hmemX u.1).mp u.2))),
       (hmemY _).mpr ⟨Classical.choose ((hmemX u.1).mp u.2), rfl⟩⟩
    have hto_eq : ∀ (u : imgY) (a : α), code3 (y a) = u.1 → (toFun u).1 = code3 (x a) := by
      intro u a ha
      have hc : code3 (y (Classical.choose ((hmemY u.1).mp u.2))) = u.1 :=
        Classical.choose_spec ((hmemY u.1).mp u.2)
      exact ((hiff _ a).1).mpr (hc.trans ha.symm)
    have hinv_eq : ∀ (u : imgX) (a : α), code3 (x a) = u.1 → (invFun u).1 = code3 (y a) := by
      intro u a ha
      have hc : code3 (x (Classical.choose ((hmemX u.1).mp u.2))) = u.1 :=
        Classical.choose_spec ((hmemX u.1).mp u.2)
      exact ((hiff _ a).1).mp (hc.trans ha.symm)
    let e1 : imgY ≃ imgX :=
      { toFun := toFun
        invFun := invFun
        left_inv := by
          intro u
          rcases (hmemY u.1).mp u.2 with ⟨a, ha⟩
          apply Subtype.ext
          rw [hinv_eq (toFun u) a (hto_eq u a ha).symm, ha]
        right_inv := by
          intro u
          rcases (hmemX u.1).mp u.2 with ⟨a, ha⟩
          apply Subtype.ext
          rw [hto_eq (invFun u) a (hinv_eq u a ha).symm, ha] }
    rcases extend_partial_bij imgY imgX e1 with ⟨π, hπ⟩
    have hπa : ∀ a : α, π (code3 (y a)) = code3 (x a) := by
      intro a
      have hm : code3 (y a) ∈ imgY := (hmemY _).mpr ⟨a, rfl⟩
      rw [hπ (code3 (y a)) hm]
      exact hto_eq ⟨code3 (y a), hm⟩ a rfl
    rcases realize_perm_fin4 π s with ⟨σ, w, hreal⟩
    refine ⟨σ, w, ?_⟩
    intro a t
    rw [hreal (y a) t, ← hpar a, hπa a, ← vec3_decomp (x a) t]
  · exact ⟨Equiv.refl _, fun _ => false, fun a => False.elim (hne ⟨a⟩)⟩

private lemma align_gram {α : Type*} {k : ℕ} (hk : k ≤ 3)
    (x y : α → Fin k → Bool)
    (hgram : ∀ a b : α,
      ∑ t : Fin k, sgn (x a t) * sgn (x b t) =
      ∑ t : Fin k, sgn (y a t) * sgn (y b t)) :
    ∃ (σ : Equiv.Perm (Fin k)) (w : Fin k → Bool),
      ∀ a : α, ∀ t : Fin k, x a t = xor (w t) (y a (σ t)) := by
  match k with
  | 0 =>
    exact ⟨Equiv.refl _, fun t => Fin.elim0 t, fun _ t => Fin.elim0 t⟩
  | 1 =>
    by_cases hne : Nonempty α
    · rcases hne with ⟨a₀⟩
      refine ⟨Equiv.refl _, fun _ => xor (x a₀ 0) (y a₀ 0), ?_⟩
      intro a t
      fin_cases t
      have h := hgram a a₀
      simp only [Fin.sum_univ_one] at h
      have hs : sgn (x a 0) = sgn (xor (xor (x a₀ 0) (y a₀ 0)) (y a 0)) := by
        rw [sgn_xor, sgn_xor]
        have hsq := sgn_mul_self (x a₀ 0)
        calc
          sgn (x a 0) = sgn (x a 0) * sgn (x a₀ 0) * sgn (x a₀ 0) := by
            rw [mul_assoc, hsq, mul_one]
          _ = sgn (y a 0) * sgn (y a₀ 0) * sgn (x a₀ 0) := by rw [h]
          _ = sgn (x a₀ 0) * sgn (y a₀ 0) * sgn (y a 0) := by ring
      exact sgn_inj hs
    · exact ⟨Equiv.refl _, fun _ => false, fun a => False.elim (hne ⟨a⟩)⟩
  | 2 => exact align_gram_two x y hgram
  | 3 => exact align_gram_three x y hgram
  | _ + 4 => omega

private lemma had_col_signed_perm {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    (c : Equiv.Perm (Fin N)) (v : Fin N → Bool) :
    isHad (fun i j => xor (v j) (D i (c j))) := by
  intro a b hab
  have hcard :
      ((Finset.univ : Finset (Fin N)).filter
        (fun j => xor (v j) (D a (c j)) ≠ xor (v j) (D b (c j)))).card =
      ((Finset.univ : Finset (Fin N)).filter (fun j => D a j ≠ D b j)).card := by
    refine Finset.card_bij (fun j _ => c j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro heq
      exact hj (by rw [heq])
    · intro j₁ _ j₂ _ h
      exact c.injective h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨c.symm j, ?_, c.apply_symm_apply j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, c.apply_symm_apply]
      intro heq
      have hx := congr_arg (xor (v (c.symm j))) heq
      simp only [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor] at hx
      exact hj hx
  rw [hcard]
  exact hD a b hab

private lemma had_row_signed_perm {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    (r : Equiv.Perm (Fin N)) (u : Fin N → Bool) :
    isHad (fun i j => xor (u i) (D (r i) j)) := by
  intro a b hab
  have hrab : r a ≠ r b := fun h => hab (r.injective h)
  have heq :
      (Finset.univ : Finset (Fin N)).filter
        (fun j => xor (u a) (D (r a) j) ≠ xor (u b) (D (r b) j)) =
      (Finset.univ : Finset (Fin N)).filter
        (fun j => D (r a) j ≠ xor (xor (u a) (u b)) (D (r b) j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases u a <;> cases u b <;> cases D (r a) j <;> cases D (r b) j <;> decide
  rw [heq]
  exact had_row_flip_count hD hrab (xor (u a) (u b))

private lemma had_sample_perm {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    (r c : Equiv.Perm (Fin N)) (u v : Fin N → Bool) :
    isHad (sampleFn D r c u v) := by
  have h1 := had_row_signed_perm (had_col_signed_perm hD c v) r u
  have hfun : (fun i j => xor (u i) (xor (v j) (D (r i) (c j)))) = sampleFn D r c u v := by
    ext i j
    simp only [sampleFn, Bool.xor_assoc]
  rwa [hfun] at h1

private lemma quad_dot_zero {N : ℕ} {D : Fin N → Fin N → Bool} (hD : isHad D)
    {R : Finset (Fin N)} (hR : R.card ≤ 3)
    {a b p q : Fin N} (ha : a ∈ R) (hb : b ∈ R) (hp : p ∈ R) (hq : q ∈ R)
    (hab : a ≠ b) (hpq : p ≠ q) (h1 : ¬(p = a ∧ q = b)) (h2 : ¬(p = b ∧ q = a)) :
    ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j) = 0 := by
  have hshare : p = a ∨ p = b ∨ q = a ∨ q = b := by
    by_contra h
    push Not at h
    rcases h with ⟨hpa, hpb, hqa, hqb⟩
    have hsub : ({a, b, p, q} : Finset (Fin N)) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hcard4 : ({a, b, p, q} : Finset (Fin N)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hpq]
      · simp [hpb.symm, hqb.symm]
      · simp [hab, hpa.symm, hqa.symm]
    have hle := Finset.card_le_card hsub
    omega
  rcases hshare with rfl | rfl | rfl | rfl
  · have hqb : b ≠ q := fun h => h1 ⟨rfl, h.symm⟩
    have hsim : ∀ j : Fin N,
        sgn (D p j) * sgn (D b j) * sgn (D p j) * sgn (D q j) = sgn (D b j) * sgn (D q j) := by
      intro j
      calc
        sgn (D p j) * sgn (D b j) * sgn (D p j) * sgn (D q j)
            = (sgn (D p j) * sgn (D p j)) * (sgn (D b j) * sgn (D q j)) := by ring
        _ = sgn (D b j) * sgn (D q j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hqb
  · have hqa : a ≠ q := fun h => h2 ⟨rfl, h.symm⟩
    have hsim : ∀ j : Fin N,
        sgn (D a j) * sgn (D p j) * sgn (D p j) * sgn (D q j) = sgn (D a j) * sgn (D q j) := by
      intro j
      calc
        sgn (D a j) * sgn (D p j) * sgn (D p j) * sgn (D q j)
            = (sgn (D p j) * sgn (D p j)) * (sgn (D a j) * sgn (D q j)) := by ring
        _ = sgn (D a j) * sgn (D q j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hqa
  · have hpb : b ≠ p := fun h => h2 ⟨h.symm, rfl⟩
    have hsim : ∀ j : Fin N,
        sgn (D q j) * sgn (D b j) * sgn (D p j) * sgn (D q j) = sgn (D b j) * sgn (D p j) := by
      intro j
      calc
        sgn (D q j) * sgn (D b j) * sgn (D p j) * sgn (D q j)
            = (sgn (D q j) * sgn (D q j)) * (sgn (D b j) * sgn (D p j)) := by ring
        _ = sgn (D b j) * sgn (D p j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hpb
  · have hpa : a ≠ p := fun h => h1 ⟨h.symm, rfl⟩
    have hsim : ∀ j : Fin N,
        sgn (D a j) * sgn (D q j) * sgn (D p j) * sgn (D q j) = sgn (D a j) * sgn (D p j) := by
      intro j
      calc
        sgn (D a j) * sgn (D q j) * sgn (D p j) * sgn (D q j)
            = (sgn (D q j) * sgn (D q j)) * (sgn (D a j) * sgn (D p j)) := by ring
        _ = sgn (D a j) * sgn (D p j) := by rw [sgn_mul_self, one_mul]
    simp_rw [hsim]
    exact had_row_dot_ne hD hpa

private lemma recover_one_row {N : ℕ} (hN : 0 < N)
    {H D : Fin N → Fin N → Bool} {R : Finset (Fin N)}
    (hH : isHad H) (hD : isHad D) (hR : R.card ≤ 3)
    (hagree : ∀ i ∉ R, ∀ j : Fin N, H i j = D i j)
    {i₀ : Fin N} (hi₀ : i₀ ∈ R) :
    ∃ a ∈ R, ∃ s : Bool, ∀ j : Fin N, H i₀ j = xor s (D a j) := by
  let α : Fin N → ℤ := fun a => ∑ t : Fin N, sgn (H i₀ t) * sgn (D a t)
  have hα_out : ∀ a ∉ R, α a = 0 := by
    intro a ha
    have hne : i₀ ≠ a := fun h => ha (h ▸ hi₀)
    have hcongr : ∀ t : Fin N, sgn (H i₀ t) * sgn (D a t) = sgn (H i₀ t) * sgn (H a t) := by
      intro t
      rw [hagree a ha t]
    simp only [α]
    simp_rw [hcongr]
    exact had_row_dot_ne hH hne
  have hexpand : ∀ j : Fin N, (N : ℤ) * sgn (H i₀ j) = ∑ a ∈ R, α a * sgn (D a j) := by
    intro j
    rw [had_row_expand hN hD (fun t => sgn (H i₀ t)) j]
    symm
    refine Finset.sum_subset (Finset.subset_univ R) ?_
    intro a _ ha
    simp [hα_out a ha]
  have hNz : (N : ℤ) ≠ 0 := by omega
  have hparseval : ∑ a ∈ R, α a * α a = (N : ℤ) * (N : ℤ) := by
    have h1 :
        ∑ j : Fin N, ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j)) =
        (N : ℤ) * ((N : ℤ) * (N : ℤ)) := by
      have hterm : ∀ j : Fin N,
          ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j)) = (N : ℤ) * (N : ℤ) := by
        intro j
        calc
          ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j))
              = (N : ℤ) * (N : ℤ) * (sgn (H i₀ j) * sgn (H i₀ j)) := by ring
          _ = (N : ℤ) * (N : ℤ) := by rw [sgn_mul_self, mul_one]
      simp_rw [hterm]
      simp [Finset.sum_const]
    have h2 :
        ∑ j : Fin N, ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j)) =
        (N : ℤ) * ∑ a ∈ R, α a * α a := by
      calc
        ∑ j : Fin N, ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j))
            = ∑ j : Fin N, (∑ a ∈ R, α a * sgn (D a j)) * (∑ b ∈ R, α b * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun j _ => by rw [hexpand j]
        _ = ∑ j : Fin N, ∑ a ∈ R, ∑ b ∈ R,
              (α a * α b) * (sgn (D a j) * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b _ => by ring
        _ = ∑ a ∈ R, ∑ j : Fin N, ∑ b ∈ R,
              (α a * α b) * (sgn (D a j) * sgn (D b j)) := Finset.sum_comm
        _ = ∑ a ∈ R, ∑ b ∈ R, ∑ j : Fin N,
              (α a * α b) * (sgn (D a j) * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ a ∈ R, ∑ b ∈ R, (α a * α b) * (∑ j : Fin N, sgn (D a j) * sgn (D b j)) := by
              refine Finset.sum_congr rfl fun a _ =>
                Finset.sum_congr rfl fun b _ => (Finset.mul_sum ..).symm
        _ = ∑ a ∈ R, ∑ b ∈ R, (α a * α b) * (if a = b then (N : ℤ) else 0) := by
              refine Finset.sum_congr rfl fun a _ =>
                Finset.sum_congr rfl fun b _ => by rw [had_row_dot hD a b]
        _ = ∑ a ∈ R, (N : ℤ) * (α a * α a) := by
              refine Finset.sum_congr rfl fun a ha => ?_
              rw [Finset.sum_eq_single a]
              · simp [mul_comm]
              · intro b _ hba
                simp [Ne.symm hba]
              · intro h
                exact absurd ha h
        _ = (N : ℤ) * ∑ a ∈ R, α a * α a := (Finset.mul_sum ..).symm
    exact mul_left_cancel₀ hNz (h2.symm.trans h1)
  have hoff_zero : ∀ j : Fin N,
      ∑ p ∈ R, ∑ q ∈ R,
        (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j)) = 0 := by
    intro j
    have hsq :
        (∑ p ∈ R, α p * sgn (D p j)) * (∑ q ∈ R, α q * sgn (D q j)) =
        (N : ℤ) * (N : ℤ) := by
      rw [← hexpand j]
      calc
        ((N : ℤ) * sgn (H i₀ j)) * ((N : ℤ) * sgn (H i₀ j))
            = (N : ℤ) * (N : ℤ) * (sgn (H i₀ j) * sgn (H i₀ j)) := by ring
        _ = (N : ℤ) * (N : ℤ) := by rw [sgn_mul_self, mul_one]
    have hsplit :
        (∑ p ∈ R, α p * sgn (D p j)) * (∑ q ∈ R, α q * sgn (D q j)) =
        (∑ p ∈ R, α p * α p) +
        ∑ p ∈ R, ∑ q ∈ R,
          (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mul_sum]
      have hterm : ∀ q : Fin N,
          α p * sgn (D p j) * (α q * sgn (D q j)) =
          (if p = q then α p * α p else 0) +
          (if p = q then 0 else α p * α q * sgn (D p j) * sgn (D q j)) := by
        intro q
        by_cases hpq : p = q
        · subst hpq
          simp only [↓reduceIte, add_zero]
          calc
            α p * sgn (D p j) * (α p * sgn (D p j))
                = α p * α p * (sgn (D p j) * sgn (D p j)) := by ring
            _ = α p * α p := by rw [sgn_mul_self, mul_one]
        · simp only [hpq, ↓reduceIte, zero_add]
          ring
      simp_rw [hterm, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hqp
        simp [Ne.symm hqp]
      · intro h
        exact absurd hp h
    rw [hsplit, hparseval] at hsq
    linarith
  have hprod_zero : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → α a * α b = 0 := by
    intro a ha b hb hab
    have hzero :
        ∑ j : Fin N, sgn (D a j) * sgn (D b j) *
          (∑ p ∈ R, ∑ q ∈ R,
            (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j))) = 0 := by
      simp_rw [hoff_zero, mul_zero, Finset.sum_const_zero]
    have hrew :
        ∑ j : Fin N, sgn (D a j) * sgn (D b j) *
          (∑ p ∈ R, ∑ q ∈ R,
            (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j))) =
        ∑ p ∈ R, ∑ q ∈ R,
          (if p = q then (0 : ℤ) else
            α p * α q *
              ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) := by
      calc
        ∑ j : Fin N, sgn (D a j) * sgn (D b j) *
            (∑ p ∈ R, ∑ q ∈ R,
              (if p = q then (0 : ℤ) else α p * α q * sgn (D p j) * sgn (D q j)))
            = ∑ j : Fin N, ∑ p ∈ R, ∑ q ∈ R,
                (if p = q then (0 : ℤ) else
                  α p * α q * (sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j))) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun q _ => ?_
              by_cases hpq : p = q
              · simp [hpq]
              · simp only [hpq, ↓reduceIte]
                ring
        _ = ∑ p ∈ R, ∑ j : Fin N, ∑ q ∈ R,
              (if p = q then (0 : ℤ) else
                α p * α q * (sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j))) :=
              Finset.sum_comm
        _ = ∑ p ∈ R, ∑ q ∈ R, ∑ j : Fin N,
              (if p = q then (0 : ℤ) else
                α p * α q * (sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j))) := by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
        _ = ∑ p ∈ R, ∑ q ∈ R,
              (if p = q then (0 : ℤ) else
                α p * α q *
                  ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) := by
              refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
              by_cases hpq : p = q
              · simp [hpq]
              · simp only [hpq, ↓reduceIte, ← Finset.mul_sum]
    rw [hrew] at hzero
    have hcollapse :
        ∑ p ∈ R, ∑ q ∈ R,
          (if p = q then (0 : ℤ) else
            α p * α q *
              ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) =
        2 * (N : ℤ) * (α a * α b) := by
      have hterm_ab :
          ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D a j) * sgn (D b j) = (N : ℤ) := by
        have h1 : ∀ j : Fin N,
            sgn (D a j) * sgn (D b j) * sgn (D a j) * sgn (D b j) = 1 := by
          intro j
          calc
            sgn (D a j) * sgn (D b j) * sgn (D a j) * sgn (D b j)
                = (sgn (D a j) * sgn (D a j)) * (sgn (D b j) * sgn (D b j)) := by ring
            _ = 1 := by rw [sgn_mul_self, sgn_mul_self, mul_one]
        simp [h1]
      have hterm_ba :
          ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D b j) * sgn (D a j) = (N : ℤ) := by
        have h1 : ∀ j : Fin N,
            sgn (D a j) * sgn (D b j) * sgn (D b j) * sgn (D a j) = 1 := by
          intro j
          calc
            sgn (D a j) * sgn (D b j) * sgn (D b j) * sgn (D a j)
                = (sgn (D a j) * sgn (D a j)) * (sgn (D b j) * sgn (D b j)) := by ring
            _ = 1 := by rw [sgn_mul_self, sgn_mul_self, mul_one]
        simp [h1]
      have hinner : ∀ p ∈ R,
          ∑ q ∈ R,
            (if p = q then (0 : ℤ) else
              α p * α q *
                ∑ j : Fin N, sgn (D a j) * sgn (D b j) * sgn (D p j) * sgn (D q j)) =
          if p = a then α a * α b * (N : ℤ)
          else if p = b then α b * α a * (N : ℤ)
          else 0 := by
        intro p hp
        by_cases hpa : p = a
        · subst hpa
          simp only [↓reduceIte]
          rw [Finset.sum_eq_single b]
          · simp [hab, hterm_ab]
          · intro q hq hqb
            by_cases hqp : p = q
            · simp [hqp]
            · simp only [hqp, ↓reduceIte]
              rw [quad_dot_zero hD hR ha hb ha hq hab hqp (fun h => hqb h.2)
                (fun h => hab h.1), mul_zero]
          · intro h
            exact absurd hb h
        · simp only [hpa, ↓reduceIte]
          by_cases hpb : p = b
          · subst hpb
            simp only [↓reduceIte]
            rw [Finset.sum_eq_single a]
            · simp [hab.symm, hterm_ba]
            · intro q hq hqa
              by_cases hqp : p = q
              · simp [hqp]
              · simp only [hqp, ↓reduceIte]
                rw [quad_dot_zero hD hR ha hb hb hq hab hqp (fun h => hpa h.1)
                  (fun h => hqa h.2), mul_zero]
            · intro h
              exact absurd ha h
          · simp only [hpb, ↓reduceIte]
            refine Finset.sum_eq_zero fun q hq => ?_
            by_cases hpq : p = q
            · simp [hpq]
            · simp only [hpq, ↓reduceIte]
              rw [quad_dot_zero hD hR ha hb hp hq hab hpq (fun h => hpa h.1)
                (fun h => hpb h.1), mul_zero]
      rw [Finset.sum_congr rfl hinner]
      have hsum_ab :
          ∑ p ∈ R, (if p = a then α a * α b * (N : ℤ)
            else if p = b then α b * α a * (N : ℤ) else 0) =
          α a * α b * (N : ℤ) + α b * α a * (N : ℤ) := by
        rw [← Finset.add_sum_erase _ _ ha]
        simp only [↓reduceIte]
        congr 1
        have hb' : b ∈ R.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
        rw [Finset.sum_eq_single b]
        · simp [hab.symm]
        · intro p hp hpb
          have hpa' : p ≠ a := (Finset.mem_erase.mp hp).1
          simp [hpa', hpb]
        · intro h
          exact absurd hb' h
      rw [hsum_ab]
      ring
    rw [hcollapse] at hzero
    have h2N : (2 : ℤ) * (N : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp hzero).resolve_left h2N
  have hex : ∃ a₀ ∈ R, α a₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsum0 : ∑ a ∈ R, α a * α a = 0 :=
      Finset.sum_eq_zero fun a ha => by rw [hall a ha, mul_zero]
    rw [hsum0] at hparseval
    have hpos : (0 : ℤ) < (N : ℤ) * (N : ℤ) := by positivity
    omega
  rcases hex with ⟨a₀, ha₀, hα0⟩
  have hother : ∀ b ∈ R, b ≠ a₀ → α b = 0 := by
    intro b hb hba
    have hp := hprod_zero a₀ ha₀ b hb hba.symm
    exact (mul_eq_zero.mp hp).resolve_left hα0
  have hsq : α a₀ * α a₀ = (N : ℤ) * (N : ℤ) := by
    rw [← hparseval, Finset.sum_eq_single a₀]
    · intro b hb hba
      rw [hother b hb hba, mul_zero]
    · intro h
      exact absurd ha₀ h
  have hval : α a₀ = (N : ℤ) ∨ α a₀ = -(N : ℤ) := by
    have hfac : (α a₀ - (N : ℤ)) * (α a₀ + (N : ℤ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hsingle : ∀ j : Fin N, (N : ℤ) * sgn (H i₀ j) = α a₀ * sgn (D a₀ j) := by
    intro j
    rw [hexpand j, Finset.sum_eq_single a₀]
    · intro b hb hba
      rw [hother b hb hba, zero_mul]
    · intro h
      exact absurd ha₀ h
  rcases hval with hpos | hneg
  · refine ⟨a₀, ha₀, false, ?_⟩
    intro j
    have hj := hsingle j
    rw [hpos] at hj
    have hs := mul_left_cancel₀ hNz hj
    rw [Bool.false_xor]
    exact sgn_inj hs
  · refine ⟨a₀, ha₀, true, ?_⟩
    intro j
    have hj := hsingle j
    rw [hneg] at hj
    have hj' : (N : ℤ) * sgn (H i₀ j) = (N : ℤ) * sgn (xor true (D a₀ j)) := by
      rw [sgn_xor, sgn_true]
      linarith
    exact sgn_inj (mul_left_cancel₀ hNz hj')

private lemma recover_missing_rows {N : ℕ} (hN : 0 < N)
    (H D : Fin N → Fin N → Bool) (R : Finset (Fin N))
    (hH : isHad H) (hD : isHad D) (hR : R.card ≤ 3)
    (hagree : ∀ i ∉ R, ∀ j : Fin N, H i j = D i j) :
    ∃ (r : Equiv.Perm (Fin N)) (u : Fin N → Bool),
      (∀ i ∉ R, r i = i ∧ u i = false) ∧
      ∀ i j, H i j = xor (u i) (D (r i) j) := by
  have hex : ∀ i : Fin N, ∃ a : Fin N, ∃ s : Bool,
      (i ∉ R → a = i ∧ s = false) ∧ ∀ j : Fin N, H i j = xor s (D a j) := by
    intro i
    by_cases hi : i ∈ R
    · rcases recover_one_row hN hH hD hR hagree hi with ⟨a, _, s, hs⟩
      exact ⟨a, s, fun h => absurd hi h, hs⟩
    · refine ⟨i, false, fun _ => ⟨rfl, rfl⟩, fun j => ?_⟩
      rw [Bool.false_xor]
      exact hagree i hi j
  let r_fun : Fin N → Fin N := fun i => Classical.choose (hex i)
  let u : Fin N → Bool := fun i => Classical.choose (Classical.choose_spec (hex i))
  have hspec : ∀ i : Fin N,
      (i ∉ R → r_fun i = i ∧ u i = false) ∧ ∀ j : Fin N, H i j = xor (u i) (D (r_fun i) j) :=
    fun i => Classical.choose_spec (Classical.choose_spec (hex i))
  have hinj : Function.Injective r_fun := by
    intro i₁ i₂ hEq
    by_contra hne
    have h0 := had_row_dot_ne hH hne
    have hsum :
        ∑ j : Fin N, sgn (H i₁ j) * sgn (H i₂ j) =
        sgn (u i₁) * sgn (u i₂) * (N : ℤ) := by
      have hterm : ∀ j : Fin N,
          sgn (H i₁ j) * sgn (H i₂ j) = sgn (u i₁) * sgn (u i₂) := by
        intro j
        rw [(hspec i₁).2 j, (hspec i₂).2 j, hEq, sgn_xor, sgn_xor]
        calc
          sgn (u i₁) * sgn (D (r_fun i₂) j) * (sgn (u i₂) * sgn (D (r_fun i₂) j))
              = sgn (u i₁) * sgn (u i₂) * (sgn (D (r_fun i₂) j) * sgn (D (r_fun i₂) j)) := by ring
          _ = sgn (u i₁) * sgn (u i₂) := by rw [sgn_mul_self, mul_one]
      simp_rw [hterm]
      simp [Finset.sum_const, mul_comm]
    rw [hsum] at h0
    have hNz : (N : ℤ) ≠ 0 := by omega
    have hprod : sgn (u i₁) * sgn (u i₂) * (N : ℤ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sgn_ne_zero _) (sgn_ne_zero _)) hNz
    exact hprod h0
  let r : Equiv.Perm (Fin N) := Equiv.ofBijective r_fun (Finite.injective_iff_bijective.mp hinj)
  refine ⟨r, u, ?_, ?_⟩
  · intro i hi
    exact (hspec i).1 hi
  · intro i j
    exact (hspec i).2 j

private lemma had_completion_3x3 {N : ℕ} (hN : 0 < N)
    (H D : Fin N → Fin N → Bool) (R C : Finset (Fin N))
    (hH : isHad H) (hD : isHad D) (hR : R.card ≤ 3) (hC : C.card ≤ 3)
    (hagree : ∀ i ∉ R, ∀ j ∉ C, H i j = D i j) :
    ∃ (r c : Equiv.Perm (Fin N)) (u v : Fin N → Bool),
      (∀ i ∉ R, r i = i ∧ u i = false) ∧
      (∀ j ∉ C, c j = j ∧ v j = false) ∧
      ∀ i j, H i j = sampleFn D r c u v i j := by
  have hgramC : ∀ a ∉ R, ∀ b ∉ R,
      ∑ j ∈ C, sgn (H a j) * sgn (H b j) = ∑ j ∈ C, sgn (D a j) * sgn (D b j) := by
    intro a ha b hb
    by_cases hab : a = b
    · subst hab
      simp [sgn_mul_self]
    · have hHtot :
          (∑ j ∈ C, sgn (H a j) * sgn (H b j)) +
          (∑ j ∈ Cᶜ, sgn (H a j) * sgn (H b j)) = 0 := by
        rw [Finset.sum_add_sum_compl]
        exact had_row_dot_ne hH hab
      have hDtot :
          (∑ j ∈ C, sgn (D a j) * sgn (D b j)) +
          (∑ j ∈ Cᶜ, sgn (D a j) * sgn (D b j)) = 0 := by
        rw [Finset.sum_add_sum_compl]
        exact had_row_dot_ne hD hab
      have hcompl :
          ∑ j ∈ Cᶜ, sgn (H a j) * sgn (H b j) = ∑ j ∈ Cᶜ, sgn (D a j) * sgn (D b j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ∉ C := Finset.mem_compl.mp hj
        rw [hagree a ha j hj', hagree b hb j hj']
      linarith
  let eC : Fin C.card ≃ C := C.equivFin.symm
  let x : {a : Fin N // a ∉ R} → Fin C.card → Bool := fun a t => H a.1 (eC t).1
  let y : {a : Fin N // a ∉ R} → Fin C.card → Bool := fun a t => D a.1 (eC t).1
  have hgram_xy : ∀ a b : {a : Fin N // a ∉ R},
      ∑ t : Fin C.card, sgn (x a t) * sgn (x b t) =
      ∑ t : Fin C.card, sgn (y a t) * sgn (y b t) := by
    intro a b
    have hxC : ∑ t : Fin C.card, sgn (x a t) * sgn (x b t) =
        ∑ j ∈ C, sgn (H a.1 j) * sgn (H b.1 j) := by
      rw [← Finset.sum_attach C]
      exact Fintype.sum_equiv eC (fun t => sgn (x a t) * sgn (x b t))
        (fun j => sgn (H a.1 j.1) * sgn (H b.1 j.1)) (fun _ => rfl)
    have hyC : ∑ t : Fin C.card, sgn (y a t) * sgn (y b t) =
        ∑ j ∈ C, sgn (D a.1 j) * sgn (D b.1 j) := by
      rw [← Finset.sum_attach C]
      exact Fintype.sum_equiv eC (fun t => sgn (y a t) * sgn (y b t))
        (fun j => sgn (D a.1 j.1) * sgn (D b.1 j.1)) (fun _ => rfl)
    rw [hxC, hyC]
    exact hgramC a.1 a.2 b.1 b.2
  rcases align_gram hC x y hgram_xy with ⟨σ, w, halign⟩
  rcases extend_perm_on_finset C eC σ with ⟨c, hc_out, hc_in⟩
  let v : Fin N → Bool := fun j => if hj : j ∈ C then w (eC.symm ⟨j, hj⟩) else false
  have hv_out : ∀ j ∉ C, v j = false := fun j hj => by simp [v, hj]
  let D1 : Fin N → Fin N → Bool := fun i j => xor (v j) (D i (c j))
  have hD1_had : isHad D1 := had_col_signed_perm hD c v
  have hD1_agree : ∀ i ∉ R, ∀ j : Fin N, H i j = D1 i j := by
    intro i hi j
    by_cases hj : j ∈ C
    · have ha := halign ⟨i, hi⟩ (eC.symm ⟨j, hj⟩)
      have heC : (eC (eC.symm ⟨j, hj⟩)).1 = j := congr_arg Subtype.val (eC.apply_symm_apply ⟨j, hj⟩)
      simp only [D1, v, hj, ↓reduceDIte, hc_in j hj]
      simpa only [x, y, heC] using ha
    · simp only [D1, hv_out j hj, hc_out j hj, Bool.false_xor]
      exact hagree i hi j hj
  rcases recover_missing_rows hN H D1 R hH hD1_had hR hD1_agree with ⟨r, u, hr_out, hr_eq⟩
  refine ⟨r, c, u, v, hr_out, fun j hj => ⟨hc_out j hj, hv_out j hj⟩, ?_⟩
  intro i j
  rw [hr_eq i j]
  simp only [D1, sampleFn, Bool.xor_assoc]

private lemma errors_edit_both_ne {N : ℕ} (hN : 0 < N) {H : Fin N → Fin N → Bool} (hH : isHad H)
    {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (f g : Bool) :
    errorsFn H (editFn H i j k l f g) +
      (if H i k ≠ xor f (H j k) then 1 else 0) +
      (if H i k ≠ xor g (H i l) then 1 else 0) =
    N + (if H i k ≠ xor (xor f g) (H j l) then 1 else 0) := by
  let E := editFn H i j k l f g
  have hE_out : ∀ x y : Fin N, x ≠ i → y ≠ k → E x y = H x y := by
    intro x y hx hy
    simp [E, editFn, hx, hy]
  have hE_row : ∀ y : Fin N, y ≠ k → E i y = xor f (H j y) := by
    intro y hy
    simp [E, editFn, hij, hy]
  have hE_col : ∀ x : Fin N, x ≠ i → E x k = xor g (H x l) := by
    intro x hx
    simp [E, editFn, hx, hkl]
  have hE_cor : E i k = xor (xor f g) (H j l) := by
    simp [E, editFn, hij, hkl]
  have hrow_sum :
      ∑ y : Fin N, errInd H E i y =
      ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card -
        (if H i k ≠ xor f (H j k) then 1 else 0) +
        (if H i k ≠ xor (xor f g) (H j l) then 1 else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have hrest :
        ∑ y ∈ Finset.univ.erase k, errInd H E i y =
        ∑ y ∈ Finset.univ.erase k, (if H i y ≠ xor f (H j y) then 1 else 0) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hyk : y ≠ k := (Finset.mem_erase.mp hy).1
      simp only [errInd, hE_row y hyk]
    rw [hrest]
    have hfull :
        ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card =
        (if H i k ≠ xor f (H j k) then 1 else 0) +
        ∑ y ∈ Finset.univ.erase k, (if H i y ≠ xor f (H j y) then 1 else 0) := by
      rw [Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    have hcor : errInd H E i k = if H i k ≠ xor (xor f g) (H j l) then 1 else 0 := by
      simp only [errInd, hE_cor]
    rw [hcor]
    omega
  have hother_sum :
      ∑ x ∈ Finset.univ.erase i, ∑ y : Fin N, errInd H E x y =
      ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card -
        (if H i k ≠ xor g (H i l) then 1 else 0) := by
    have hinner : ∀ x ∈ Finset.univ.erase i,
        ∑ y : Fin N, errInd H E x y = if H x k ≠ xor g (H x l) then 1 else 0 := by
      intro x hx
      have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
      rw [Finset.sum_eq_single k]
      · simp only [errInd, hE_col x hxi]
      · intro y _ hyk
        simp only [errInd, hE_out x y hxi hyk, ne_eq, not_true_eq_false, ↓reduceIte]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [Finset.sum_congr rfl hinner]
    have hfull :
        ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card =
        (if H i k ≠ xor g (H i l) then 1 else 0) +
        ∑ x ∈ Finset.univ.erase i, (if H x k ≠ xor g (H x l) then 1 else 0) := by
      rw [Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    omega
  have hrc : 2 * ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card = N :=
    had_row_flip_count hH hij f
  have hcc : 2 * ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card = N :=
    had_col_flip_count hN hH hkl g
  have hrc_ge : (if H i k ≠ xor f (H j k) then 1 else 0) ≤
      ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card := by
    split_ifs with h
    · exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩⟩
    · exact Nat.zero_le _
  have hcc_ge : (if H i k ≠ xor g (H i l) then 1 else 0) ≤
      ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card := by
    split_ifs with h
    · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
    · exact Nat.zero_le _
  rw [errors_eq_sum_ind, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hrow_sum, hother_sum]
  omega

private lemma errors_edit_cases {N : ℕ} (hN : 0 < N) {H : Fin N → Fin N → Bool} (hH : isHad H)
    (i j k l : Fin N) (f g : Bool) (he : errorsFn H (editFn H i j k l f g) < N) :
    errorsFn H (editFn H i j k l f g) = 0 ∨
    2 * errorsFn H (editFn H i j k l f g) = N ∨
    errorsFn H (editFn H i j k l f g) + 2 = N ∨
    errorsFn H (editFn H i j k l f g) + 1 = N := by
  by_cases hij : i = j
  · by_cases hkl : k = l
    · left
      subst hij
      subst hkl
      have hEq : editFn H i i k k f g = H := by
        ext x y
        simp only [editFn, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Bool.false_xor]
        split_ifs <;> subst_vars <;> rfl
      rw [hEq]
      simp [errorsFn]
    · right; left
      subst hij
      have hEq :
          errorsFn H (editFn H i i k l f g) =
          ((Finset.univ : Finset (Fin N)).filter (fun x => H x k ≠ xor g (H x l))).card := by
        rw [errors_eq_sum_ind, Finset.card_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hxx : (if x = i then i else x) = x := by
          split_ifs with h
          · exact h.symm
          · rfl
        rw [Finset.sum_eq_single k]
        · simp only [errInd, editFn, hxx, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            Bool.false_xor, hkl, true_and, not_false_eq_true]
        · intro y _ hyk
          simp only [errInd, editFn, hxx, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            hyk, false_and, Bool.false_xor]
        · intro h
          exact absurd (Finset.mem_univ k) h
      rw [hEq]
      exact had_col_flip_count hN hH hkl g
  · by_cases hkl : k = l
    · right; left
      subst hkl
      have hEq :
          errorsFn H (editFn H i j k k f g) =
          ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor f (H j y))).card := by
        rw [errors_eq_sum_ind, Finset.sum_eq_single i]
        · rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun y _ => ?_
          have hyy : (if y = k then k else y) = y := by
            split_ifs with h
            · exact h.symm
            · rfl
          simp only [errInd, editFn, hyy, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            Bool.xor_false, hij, true_and, not_false_eq_true]
        · intro x _ hxi
          refine Finset.sum_eq_zero fun y _ => ?_
          have hyy : (if y = k then k else y) = y := by
            split_ifs with h
            · exact h.symm
            · rfl
          simp only [errInd, editFn, hyy, hxi, false_and, ↓reduceIte, ne_eq, not_true_eq_false,
            and_false, Bool.false_xor]
        · intro h
          exact absurd (Finset.mem_univ i) h
      rw [hEq]
      exact had_row_flip_count hH hij f
    · right; right
      have hform := errors_edit_both_ne hN hH hij hkl f g
      split_ifs at hform <;> omega

private lemma exists_neg_edit {N : ℕ} (hN : 8 ≤ N) {H : Fin N → Fin N → Bool} (hH : isHad H) :
    ∃ (i j k l : Fin N) (f g : Bool),
      i ≠ j ∧ k ≠ l ∧ errorsFn H (editFn H i j k l f g) + 1 = N := by
  have hNpos : 0 < N := by omega
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congr_arg Fin.val h
    simp [i, j] at this
  have hdiff_card := had_row_flip_count hH hij false
  have hsame_card := had_row_flip_count hH hij true
  have hdiff_ne : ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor false (H j y))).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsame_ne : ((Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor true (H j y))).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hsame_ne with ⟨k, hk⟩
  rcases hdiff_ne with ⟨l, hl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_xor] at hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have hik_eq : H i k = H j k := by
    cases h1 : H i k <;> cases h2 : H j k <;> simp_all
  have hkl : k ≠ l := by
    intro h
    subst h
    exact hl hik_eq
  let f : Bool := true
  let g : Bool := xor (H i k) (H i l)
  have hform := errors_edit_both_ne hNpos hH hij hkl f g
  have h1 : H i k ≠ xor f (H j k) := by
    simp only [f, hik_eq]
    cases H j k <;> decide
  have h2 : ¬(H i k ≠ xor g (H i l)) := by
    simp only [g, not_not]
    cases H i k <;> cases H i l <;> decide
  have h3 : ¬(H i k ≠ xor (xor f g) (H j l)) := by
    simp only [f, g, not_not]
    cases ha : H i k <;> cases hb : H i l <;> cases hc : H j l <;> simp_all
  have hi1 : (if H i k ≠ xor f (H j k) then 1 else 0) = 1 := by
    split_ifs
    rfl
  have hi2 : (if H i k ≠ xor g (H i l) then 1 else 0) = 0 := by
    split_ifs
    rfl
  have hi3 : (if H i k ≠ xor (xor f g) (H j l) then 1 else 0) = 0 := by
    split_ifs
    rfl
  rw [hi1, hi2, hi3] at hform
  exact ⟨i, j, k, l, f, g, hij, hkl, by omega⟩

private lemma classify_col_inj {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H) (hD : isHad D)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    (hc_inj : Function.Injective c)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sampleFn D p q a b) ∧
    (∃ (i j k l : Fin N) (f g : Bool), sampleFn D r c u v = editFn H i j k l f g) := by
  have hNpos : 0 < N := by omega
  let cP : Equiv.Perm (Fin N) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc_inj)
  have hcP : ∀ j : Fin N, cP j = c j := fun _ => rfl
  let D1 : Fin N → Fin N → Bool := fun i j => xor (v j) (D i (cP j))
  have hD1 : isHad D1 := had_col_signed_perm hD cP v
  let K : Fin N → Fin N → Bool := sampleFn D r c u v
  have hK : ∀ i j : Fin N, K i j = xor (u i) (D1 (r i) j) := by
    intro i j
    simp only [K, sampleFn, D1, hcP, Bool.xor_assoc]
  let rowErr : Fin N → ℕ := fun i =>
    ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ K i j)).card
  have hsum_err : ∑ i : Fin N, rowErr i < N := he
  let Z : Finset (Fin N) := Finset.univ.filter (fun i => rowErr i = 0)
  have hZ_eq : ∀ i ∈ Z, ∀ j : Fin N, H i j = xor (u i) (D1 (r i) j) := by
    intro i hi j
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and, rowErr, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, not_not] at hi
    rw [hi trivial, hK i j]
  have hr_injZ : Set.InjOn r Z := by
    intro i₁ hi₁ i₂ hi₂ hEq
    by_contra hne
    have h0 := had_row_dot_ne hH hne
    have hsum :
        ∑ j : Fin N, sgn (H i₁ j) * sgn (H i₂ j) = sgn (u i₁) * sgn (u i₂) * (N : ℤ) := by
      have hterm : ∀ j : Fin N,
          sgn (H i₁ j) * sgn (H i₂ j) = sgn (u i₁) * sgn (u i₂) := by
        intro j
        rw [hZ_eq i₁ hi₁ j, hZ_eq i₂ hi₂ j, hEq, sgn_xor (u i₁), sgn_xor (u i₂)]
        calc
          sgn (u i₁) * sgn (D1 (r i₂) j) * (sgn (u i₂) * sgn (D1 (r i₂) j))
              = sgn (u i₁) * sgn (u i₂) * (sgn (D1 (r i₂) j) * sgn (D1 (r i₂) j)) := by ring
          _ = sgn (u i₁) * sgn (u i₂) := by rw [sgn_mul_self, mul_one]
      simp_rw [hterm]
      simp [Finset.sum_const, mul_comm]
    rw [hsum] at h0
    have hNz : (N : ℤ) ≠ 0 := by omega
    exact mul_ne_zero (mul_ne_zero (sgn_ne_zero _) (sgn_ne_zero _)) hNz h0
  let S1 : Finset (Fin N) := Zᶜ.filter (fun i => r i ∈ Z.image r)
  let S2 : Finset (Fin N) := Zᶜ.filter (fun i => r i ∉ Z.image r)
  have hS_disj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hS_union : S1 ∪ S2 = Zᶜ := by
    ext i
    simp only [S1, S2, Finset.mem_union, Finset.mem_filter]
    tauto
  have hS_card : S1.card + S2.card = Zᶜ.card := by
    rw [← Finset.card_union_of_disjoint hS_disj, hS_union]
  have hS1_err : ∀ i ∈ S1, 2 * rowErr i = N := by
    intro i hi
    simp only [S1, Finset.mem_filter, Finset.mem_compl] at hi
    rcases Finset.mem_image.mp hi.2 with ⟨j, hj, hrj⟩
    have hij : i ≠ j := fun h => hi.1 (h ▸ hj)
    have hKeq : ∀ y : Fin N, K i y = xor (xor (u i) (u j)) (H j y) := by
      intro y
      rw [hK i y, ← hrj, hZ_eq j hj y]
      cases u i <;> cases u j <;> cases D1 (r j) y <;> decide
    have hf :
        (Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ K i y) =
        (Finset.univ : Finset (Fin N)).filter (fun y => H i y ≠ xor (xor (u i) (u j)) (H j y)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hKeq y]
    simp only [rowErr, hf]
    exact had_row_flip_count hH hij (xor (u i) (u j))
  have hS2_err : ∀ i ∈ S2, N ≤ rowErr i * Zᶜ.card := by
    intro i hi
    simp only [S2, Finset.mem_filter, Finset.mem_compl] at hi
    have hpos : 0 < rowErr i := by
      have hne0 : rowErr i ≠ 0 := by
        intro h0
        exact hi.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0⟩)
      omega
    let x : Fin N → ℤ := fun y => sgn (H i y) - sgn (K i y)
    have hx_ne : x ≠ 0 := by
      rcases Finset.card_pos.mp hpos with ⟨y₀, hy₀⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₀
      intro h0
      have hx0 : x y₀ = 0 := congr_fun h0 y₀
      simp only [x, sub_eq_zero] at hx0
      exact hy₀ (sgn_inj hx0)
    have hunc := had_uncertainty hNpos hD1 x hx_ne
    have hA_eq :
        ((Finset.univ : Finset (Fin N)).filter (fun y => x y ≠ 0)).card = rowErr i := by
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, sub_ne_zero]
      exact ⟨fun h heq => h (by rw [heq]), fun h heq => h (sgn_inj heq)⟩
    have hB_sub :
        (Finset.univ : Finset (Fin N)).filter (fun a => ∑ y : Fin N, sgn (D1 a y) * x y ≠ 0) ⊆
        (Z.image r)ᶜ := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [Finset.mem_compl]
      intro himg
      rcases Finset.mem_image.mp himg with ⟨j, hj, hrj⟩
      have hij : i ≠ j := fun h => hi.1 (h ▸ hj)
      have hari : a ≠ r i := fun h => hi.2 (h ▸ himg)
      have hy0 : ∑ y : Fin N, sgn (D1 a y) * x y = 0 := by
        have hsplit :
            ∑ y : Fin N, sgn (D1 a y) * x y =
            (∑ y : Fin N, sgn (D1 a y) * sgn (H i y)) -
            (∑ y : Fin N, sgn (D1 a y) * sgn (K i y)) := by
          simp only [x, mul_sub, Finset.sum_sub_distrib]
        rw [hsplit]
        have hterm1 : ∑ y : Fin N, sgn (D1 a y) * sgn (H i y) = 0 := by
          have h1 : ∀ y : Fin N,
              sgn (D1 a y) * sgn (H i y) = sgn (u j) * (sgn (H i y) * sgn (H j y)) := by
            intro y
            have hzj := hZ_eq j hj y
            rw [hrj] at hzj
            have hd : sgn (D1 a y) = sgn (u j) * sgn (H j y) := by
              rw [hzj, sgn_xor (u j), ← mul_assoc, sgn_mul_self, one_mul]
            rw [hd]
            ring
          simp_rw [h1, ← Finset.mul_sum, had_row_dot_ne hH hij, mul_zero]
        have hterm2 : ∑ y : Fin N, sgn (D1 a y) * sgn (K i y) = 0 := by
          have h2 : ∀ y : Fin N,
              sgn (D1 a y) * sgn (K i y) = sgn (u i) * (sgn (D1 a y) * sgn (D1 (r i) y)) := by
            intro y
            rw [hK i y, sgn_xor (u i)]
            ring
          simp_rw [h2, ← Finset.mul_sum, had_row_dot_ne hD1 hari, mul_zero]
        rw [hterm1, hterm2, sub_self]
      exact ha hy0
    have hB_le :
        ((Finset.univ : Finset (Fin N)).filter
          (fun a => ∑ y : Fin N, sgn (D1 a y) * x y ≠ 0)).card ≤ Zᶜ.card := by
      calc
        ((Finset.univ : Finset (Fin N)).filter
            (fun a => ∑ y : Fin N, sgn (D1 a y) * x y ≠ 0)).card
            ≤ (Z.image r)ᶜ.card := Finset.card_le_card hB_sub
        _ = N - (Z.image r).card := by simp [Finset.card_compl]
        _ = N - Z.card := by rw [Finset.card_image_of_injOn hr_injZ]
        _ = Zᶜ.card := by simp [Finset.card_compl]
    rw [hA_eq] at hunc
    exact le_trans hunc (Nat.mul_le_mul_left (rowErr i) hB_le)
  have hS1_sum : 2 * ∑ i ∈ S1, rowErr i = S1.card * N := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hS1_err]
    simp
  have hS2_sum : S2.card * N ≤ Zᶜ.card * ∑ i ∈ S2, rowErr i := by
    calc
      S2.card * N = ∑ _i ∈ S2, N := by simp
      _ ≤ ∑ i ∈ S2, rowErr i * Zᶜ.card := Finset.sum_le_sum hS2_err
      _ = Zᶜ.card * ∑ i ∈ S2, rowErr i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsum_le : ∑ i ∈ S1, rowErr i + ∑ i ∈ S2, rowErr i ≤ ∑ i : Fin N, rowErr i := by
    rw [← Finset.sum_union hS_disj, hS_union]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hS1_le1 : S1.card ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ S1.card := by omega
    have : 2 * N ≤ 2 * ∑ i ∈ S1, rowErr i := by
      rw [hS1_sum]
      exact Nat.mul_le_mul_right N h2
    omega
  by_cases hZc : Zᶜ.card = 0
  · have hZ_univ : Z = Finset.univ := by
      have h1 : Zᶜ = ∅ := Finset.card_eq_zero.mp hZc
      ext i
      simp only [Finset.mem_univ, iff_true]
      by_contra h
      have hc : i ∈ Zᶜ := Finset.mem_compl.mpr h
      rw [h1] at hc
      exact Finset.notMem_empty i hc
    have hr_inj : Function.Injective r := by
      intro i₁ i₂ h
      exact hr_injZ (hZ_univ ▸ Finset.mem_univ i₁) (hZ_univ ▸ Finset.mem_univ i₂) h
    let rP : Equiv.Perm (Fin N) := Equiv.ofBijective r (Finite.injective_iff_bijective.mp hr_inj)
    have hHK : H = K := by
      ext i j
      rw [hZ_eq i (hZ_univ ▸ Finset.mem_univ i) j, hK i j]
    refine ⟨⟨rP, cP, u, v, ?_⟩, ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩,
      false, false, ?_⟩⟩
    · ext i j
      rw [hHK]
      rfl
    · ext x y
      rw [hHK]
      simp only [editFn, ne_eq, not_true_eq_false, and_false, ↓reduceIte, Bool.false_xor]
      split_ifs <;> subst_vars <;> rfl
  · have hS1_eq1 : S1.card = 1 := by
      by_contra h
      have hS1_0 : S1.card = 0 := by omega
      have hS2_eq : S2.card = Zᶜ.card := by omega
      rw [hS2_eq] at hS2_sum
      have hge : Zᶜ.card * N ≤ Zᶜ.card * ∑ i : Fin N, rowErr i :=
        le_trans hS2_sum (Nat.mul_le_mul_left _ (by omega))
      have hpos : 0 < Zᶜ.card := by omega
      have : N ≤ ∑ i : Fin N, rowErr i := Nat.le_of_mul_le_mul_left hge hpos
      omega
    have hS2_eq0 : S2.card = 0 := by
      by_contra h
      have hS2_pos : 1 ≤ S2.card := by omega
      have hm_ge2 : 2 ≤ Zᶜ.card := by omega
      have hmul :
          (3 * Zᶜ.card - 2) * N ≤ 2 * Zᶜ.card * (∑ i ∈ S1, rowErr i + ∑ i ∈ S2, rowErr i) := by
        have h1 : Zᶜ.card * N = Zᶜ.card * (2 * ∑ i ∈ S1, rowErr i) := by
          rw [hS1_sum, hS1_eq1, one_mul]
        have h2 : 2 * (S2.card * N) ≤ 2 * (Zᶜ.card * ∑ i ∈ S2, rowErr i) :=
          Nat.mul_le_mul_left 2 hS2_sum
        have h3 : 3 * Zᶜ.card - 2 = Zᶜ.card + 2 * S2.card := by omega
        rw [h3, add_mul, mul_assoc]
        linarith
      have hge2m : 2 * Zᶜ.card ≤ 3 * Zᶜ.card - 2 := by omega
      have hbound : 2 * Zᶜ.card * N ≤ 2 * Zᶜ.card * ∑ i : Fin N, rowErr i := by
        calc
          2 * Zᶜ.card * N ≤ (3 * Zᶜ.card - 2) * N := Nat.mul_le_mul_right N hge2m
          _ ≤ 2 * Zᶜ.card * (∑ i ∈ S1, rowErr i + ∑ i ∈ S2, rowErr i) := hmul
          _ ≤ 2 * Zᶜ.card * ∑ i : Fin N, rowErr i := Nat.mul_le_mul_left _ hsum_le
      have hpos : 0 < 2 * Zᶜ.card := by omega
      have : N ≤ ∑ i : Fin N, rowErr i := Nat.le_of_mul_le_mul_left hbound hpos
      omega
    rcases Finset.card_eq_one.mp hS1_eq1 with ⟨i₀, hi₀_eq⟩
    have hZc_eq : Zᶜ = {i₀} := by
      have hS2_empty : S2 = ∅ := Finset.card_eq_zero.mp hS2_eq0
      rw [← hS_union, hi₀_eq, hS2_empty, Finset.union_empty]
    have hi₀_S1 : i₀ ∈ S1 := by rw [hi₀_eq]; exact Finset.mem_singleton_self i₀
    have hi₀_nZ : i₀ ∉ Z := by
      have h1 : i₀ ∈ Zᶜ := by rw [hZc_eq]; exact Finset.mem_singleton_self i₀
      exact Finset.mem_compl.mp h1
    have hi₀_img : r i₀ ∈ Z.image r := (Finset.mem_filter.mp hi₀_S1).2
    rcases Finset.mem_image.mp hi₀_img with ⟨j₀, hj₀, hrj₀⟩
    have hij₀ : i₀ ≠ j₀ := fun h => hi₀_nZ (h ▸ hj₀)
    rcases extend_injOn_perm Z r hr_injZ with ⟨r0, hr0⟩
    let D2 : Fin N → Fin N → Bool := fun x y => xor (u x) (D1 (r0 x) y)
    have hD2 : isHad D2 := had_row_signed_perm hD1 r0 u
    have hD2_agree : ∀ x ∉ ({i₀} : Finset (Fin N)), ∀ y : Fin N, H x y = D2 x y := by
      intro x hx y
      have hxZ : x ∈ Z := by
        by_contra h
        have h1 : x ∈ Zᶜ := Finset.mem_compl.mpr h
        rw [hZc_eq] at h1
        exact hx h1
      simp only [D2, hr0 x hxZ]
      exact hZ_eq x hxZ y
    rcases recover_missing_rows hNpos H D2 {i₀} hH hD2 (by simp) hD2_agree with
      ⟨p1, a1, _, hp1_eq⟩
    refine ⟨⟨p1.trans r0, cP, fun x => xor (a1 x) (u (p1 x)), v, ?_⟩,
      ⟨i₀, j₀, ⟨0, by omega⟩, ⟨0, by omega⟩, xor (u i₀) (u j₀), false, ?_⟩⟩
    · ext x y
      rw [hp1_eq x y]
      simp only [D2, D1, sampleFn, Equiv.trans_apply, hcP, Bool.xor_assoc]
    · ext x y
      have hy0 : (if y = (⟨0, hNpos⟩ : Fin N) then (⟨0, hNpos⟩ : Fin N) else y) = y := by
        split_ifs with h
        · exact h.symm
        · rfl
      by_cases hxi : x = i₀
      · rw [hxi]
        have h1 : K i₀ y = xor (xor (u i₀) (u j₀)) (H j₀ y) := by
          rw [hK i₀ y, ← hrj₀, hZ_eq j₀ hj₀ y]
          cases u i₀ <;> cases u j₀ <;> cases D1 (r j₀) y <;> decide
        change K i₀ y = _
        rw [h1]
        simp only [editFn, hy0, hij₀, true_and, not_false_eq_true, ↓reduceIte, ne_eq,
          not_true_eq_false, and_false, Bool.xor_false]
      · have hxZ : x ∈ Z := by
          by_contra h
          have h1 : x ∈ Zᶜ := Finset.mem_compl.mpr h
          rw [hZc_eq, Finset.mem_singleton] at h1
          exact hxi h1
        change K x y = _
        rw [hK x y, ← hZ_eq x hxZ y]
        simp only [editFn, hy0, hxi, false_and, ↓reduceIte, ne_eq, not_true_eq_false, and_false,
          Bool.false_xor]

private lemma corner_bool_ineq :
    ∀ e11 e12 e21 e22 : Bool,
      (if xor e11 e21 then 1 else 0) + (if xor e12 e22 then 1 else 0) +
      (if xor e11 e12 then 1 else 0) + (if xor e21 e22 then 1 else 0) ≤
      2 + (if e11 then 1 else 0) + (if e12 then 1 else 0) +
      (if e21 then 1 else 0) + (if e22 then 1 else 0) := by
  decide

private lemma bool_ne_xor_iff :
    ∀ h1 h2 k1 k2 s : Bool,
      xor k1 k2 = s →
      (h1 ≠ xor s h2 ↔ xor (xor h1 k1) (xor h2 k2) = true) := by
  decide

private lemma bool_ne_ite_xor :
    ∀ a b : Bool, (if a ≠ b then 1 else 0) = (if xor a b = true then 1 else 0) := by
  decide

private lemma ab_force_one {N e a b : ℕ} (hN : 8 ≤ N) (he : e < N)
    (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (hineq : (a + b) * N ≤ 2 * e + 4 * a * b) :
    a = 1 ∧ b = 1 := by
  interval_cases a <;> interval_cases b <;> omega

private lemma both_coll_extract_RC {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    {i₁ i₂ k₁ k₂ : Fin N} (hi12 : i₁ ≠ i₂) (hri12 : r i₁ = r i₂)
    (hk12 : k₁ ≠ k₂) (hck12 : c k₁ = c k₂)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    ∃ R : Finset (Fin N),
      R.card ≤ 3 ∧ ∀ i ∉ R, ∀ j ∉ ({k₁, k₂} : Finset (Fin N)),
        H i j = sampleFn D r c u v i j := by
  have hNpos : 0 < N := by omega
  let K := sampleFn D r c u v
  have heK : errorsFn H K < N := he
  let badR : Fin N → ℕ := fun j => if H i₁ j ≠ xor (xor (u i₁) (u i₂)) (H i₂ j) then 1 else 0
  let badC : Fin N → ℕ := fun i => if H i k₁ ≠ xor (xor (v k₁) (v k₂)) (H i k₂) then 1 else 0
  have hbadR_tot : 2 * ∑ j : Fin N, badR j = N := by
    have h1 : ∑ j : Fin N, badR j =
        ((Finset.univ : Finset (Fin N)).filter
          (fun j => H i₁ j ≠ xor (xor (u i₁) (u i₂)) (H i₂ j))).card := by
      simp only [badR, Finset.card_filter]
    rw [h1]
    exact had_row_flip_count hH hi12 (xor (u i₁) (u i₂))
  have hbadC_tot : 2 * ∑ i : Fin N, badC i = N := by
    have h1 : ∑ i : Fin N, badC i =
        ((Finset.univ : Finset (Fin N)).filter
          (fun i => H i k₁ ≠ xor (xor (v k₁) (v k₂)) (H i k₂))).card := by
      simp only [badC, Finset.card_filter]
    rw [h1]
    exact had_col_flip_count hNpos hH hk12 (xor (v k₁) (v k₂))
  have hbadR_le : ∀ j : Fin N, badR j ≤ errInd H K i₁ j + errInd H K i₂ j := by
    intro j
    have hKxor : xor (K i₁ j) (K i₂ j) = xor (u i₁) (u i₂) := by
      simp only [K, sampleFn, hri12]
      cases u i₁ <;> cases u i₂ <;> cases v j <;> cases D (r i₂) (c j) <;> decide
    simp only [badR, errInd]
    cases ha : H i₁ j <;> cases hb : H i₂ j <;> cases hc : K i₁ j <;> cases hd : K i₂ j <;>
      cases hu1 : u i₁ <;> cases hu2 : u i₂ <;> simp_all
  have hbadC_le : ∀ i : Fin N, badC i ≤ errInd H K i k₁ + errInd H K i k₂ := by
    intro i
    have hKxor : xor (K i k₁) (K i k₂) = xor (v k₁) (v k₂) := by
      simp only [K, sampleFn, hck12]
      cases u i <;> cases v k₁ <;> cases v k₂ <;> cases D (r i) (c k₂) <;> decide
    simp only [badC, errInd]
    cases ha : H i k₁ <;> cases hb : H i k₂ <;> cases hc : K i k₁ <;> cases hd : K i k₂ <;>
      cases hv1 : v k₁ <;> cases hv2 : v k₂ <;> simp_all
  have hcorner :
      badR k₁ + badR k₂ + badC i₁ + badC i₂ ≤
      2 + errInd H K i₁ k₁ + errInd H K i₁ k₂ + errInd H K i₂ k₁ + errInd H K i₂ k₂ := by
    have hKr1 : xor (K i₁ k₁) (K i₂ k₁) = xor (u i₁) (u i₂) := by
      simp only [K, sampleFn, hri12]
      cases u i₁ <;> cases u i₂ <;> cases v k₁ <;> cases D (r i₂) (c k₁) <;> decide
    have hKr2 : xor (K i₁ k₂) (K i₂ k₂) = xor (u i₁) (u i₂) := by
      simp only [K, sampleFn, hri12]
      cases u i₁ <;> cases u i₂ <;> cases v k₂ <;> cases D (r i₂) (c k₂) <;> decide
    have hKc1 : xor (K i₁ k₁) (K i₁ k₂) = xor (v k₁) (v k₂) := by
      simp only [K, sampleFn, hck12]
      cases u i₁ <;> cases v k₁ <;> cases v k₂ <;> cases D (r i₁) (c k₂) <;> decide
    have hKc2 : xor (K i₂ k₁) (K i₂ k₂) = xor (v k₁) (v k₂) := by
      simp only [K, sampleFn, hck12]
      cases u i₂ <;> cases v k₁ <;> cases v k₂ <;> cases D (r i₂) (c k₂) <;> decide
    let e11 := xor (H i₁ k₁) (K i₁ k₁)
    let e12 := xor (H i₁ k₂) (K i₁ k₂)
    let e21 := xor (H i₂ k₁) (K i₂ k₁)
    let e22 := xor (H i₂ k₂) (K i₂ k₂)
    have h11 : errInd H K i₁ k₁ = if e11 then 1 else 0 := bool_ne_ite_xor (H i₁ k₁) (K i₁ k₁)
    have h12 : errInd H K i₁ k₂ = if e12 then 1 else 0 := bool_ne_ite_xor (H i₁ k₂) (K i₁ k₂)
    have h21 : errInd H K i₂ k₁ = if e21 then 1 else 0 := bool_ne_ite_xor (H i₂ k₁) (K i₂ k₁)
    have h22 : errInd H K i₂ k₂ = if e22 then 1 else 0 := bool_ne_ite_xor (H i₂ k₂) (K i₂ k₂)
    have hr1 : badR k₁ = if xor e11 e21 then 1 else 0 := by
      simp only [badR, bool_ne_xor_iff _ _ _ _ _ hKr1, e11, e21]
    have hr2 : badR k₂ = if xor e12 e22 then 1 else 0 := by
      simp only [badR, bool_ne_xor_iff _ _ _ _ _ hKr2, e12, e22]
    have hc1 : badC i₁ = if xor e11 e12 then 1 else 0 := by
      simp only [badC, bool_ne_xor_iff _ _ _ _ _ hKc1, e11, e12]
    have hc2 : badC i₂ = if xor e21 e22 then 1 else 0 := by
      simp only [badC, bool_ne_xor_iff _ _ _ _ _ hKc2, e21, e22]
    rw [h11, h12, h21, h22, hr1, hr2, hc1, hc2]
    exact corner_bool_ineq e11 e12 e21 e22
  let R0 : Finset (Fin N) := {i₁, i₂}
  let C0 : Finset (Fin N) := {k₁, k₂}
  have hsum_R0 : ∀ f : Fin N → ℕ, ∑ i ∈ R0, f i = f i₁ + f i₂ := by
    intro f
    simp [R0, Finset.sum_pair hi12]
  have hsum_C0 : ∀ f : Fin N → ℕ, ∑ j ∈ C0, f j = f k₁ + f k₂ := by
    intro f
    simp [C0, Finset.sum_pair hk12]
  have hsplit_tot :
      errorsFn H K =
      (∑ i ∈ R0, ∑ j ∈ C0, errInd H K i j) +
      (∑ i ∈ R0, ∑ j ∈ C0ᶜ, errInd H K i j) +
      (∑ i ∈ R0ᶜ, ∑ j ∈ C0, errInd H K i j) +
      (∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j) := by
    rw [errors_eq_sum_ind, ← Finset.sum_add_sum_compl R0]
    have h1 : ∀ i : Fin N,
        ∑ j : Fin N, errInd H K i j =
        (∑ j ∈ C0, errInd H K i j) + (∑ j ∈ C0ᶜ, errInd H K i j) :=
      fun i => (Finset.sum_add_sum_compl C0 _).symm
    simp_rw [h1, Finset.sum_add_distrib]
    omega
  have hbadR_split :
      ∑ j : Fin N, badR j = badR k₁ + badR k₂ + ∑ j ∈ C0ᶜ, badR j := by
    rw [← Finset.sum_add_sum_compl C0, hsum_C0]
  have hbadC_split :
      ∑ i : Fin N, badC i = badC i₁ + badC i₂ + ∑ i ∈ R0ᶜ, badC i := by
    rw [← Finset.sum_add_sum_compl R0, hsum_R0]
  have hUr_ge : ∑ j ∈ C0ᶜ, badR j ≤ ∑ i ∈ R0, ∑ j ∈ C0ᶜ, errInd H K i j := by
    rw [hsum_R0, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hbadR_le j
  have hUc_ge : ∑ i ∈ R0ᶜ, badC i ≤ ∑ i ∈ R0ᶜ, ∑ j ∈ C0, errInd H K i j := by
    calc
      ∑ i ∈ R0ᶜ, badC i ≤ ∑ i ∈ R0ᶜ, (errInd H K i k₁ + errInd H K i k₂) :=
        Finset.sum_le_sum fun i _ => hbadC_le i
      _ = ∑ i ∈ R0ᶜ, ∑ j ∈ C0, errInd H K i j := by
        refine Finset.sum_congr rfl fun i _ => (hsum_C0 _).symm
  have hU0_eq :
      ∑ i ∈ R0, ∑ j ∈ C0, errInd H K i j =
      errInd H K i₁ k₁ + errInd H K i₁ k₂ + errInd H K i₂ k₁ + errInd H K i₂ k₂ := by
    rw [hsum_R0, hsum_C0, hsum_C0]
    omega
  have hout_le1 : ∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j ≤ 1 := by
    omega
  by_cases h0 : ∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j = 0
  · refine ⟨R0, ?_, ?_⟩
    · simp [R0, Finset.card_pair hi12]
    · intro i hi j hj
      have h1 := Finset.sum_eq_zero_iff.mp h0 i (Finset.mem_compl.mpr hi)
      have h2 := Finset.sum_eq_zero_iff.mp h1 j (Finset.mem_compl.mpr hj)
      simp only [errInd, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h2
      exact h2
  · have hpos : 0 < ∑ i ∈ R0ᶜ, ∑ j ∈ C0ᶜ, errInd H K i j := by omega
    rcases Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos) with ⟨i₃, hi₃, hrow3⟩
    refine ⟨insert i₃ R0, ?_, ?_⟩
    · have hR0c : R0.card = 2 := Finset.card_pair hi12
      have := Finset.card_insert_le i₃ R0
      omega
    · intro i hi j hj
      have hiR0 : i ∈ R0ᶜ := Finset.mem_compl.mpr (fun h => hi (Finset.mem_insert_of_mem h))
      have hne3 : i ≠ i₃ := fun h => hi (h ▸ Finset.mem_insert_self i₃ R0)
      have hle_sum :
          (∑ y ∈ C0ᶜ, errInd H K i₃ y) + (∑ y ∈ C0ᶜ, errInd H K i y) ≤
          ∑ x ∈ R0ᶜ, ∑ y ∈ C0ᶜ, errInd H K x y := by
        rw [← Finset.add_sum_erase _ _ hi₃]
        refine Nat.add_le_add_left ?_ _
        exact Finset.single_le_sum (f := fun x => ∑ y ∈ C0ᶜ, errInd H K x y)
          (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne3, hiR0⟩)
      have hi3_ge1 : 1 ≤ ∑ y ∈ C0ᶜ, errInd H K i₃ y := Nat.pos_of_ne_zero hrow3
      have hi_zero : ∑ y ∈ C0ᶜ, errInd H K i y = 0 := by omega
      have h2 := Finset.sum_eq_zero_iff.mp hi_zero j (Finset.mem_compl.mpr hj)
      simp only [errInd, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h2
      exact h2

private lemma classify_both_coll {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H) (hD : isHad D)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    (hr_coll : ∃ i₁ i₂ : Fin N, i₁ ≠ i₂ ∧ r i₁ = r i₂)
    (hc_coll : ∃ k₁ k₂ : Fin N, k₁ ≠ k₂ ∧ c k₁ = c k₂)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sampleFn D p q a b) ∧
    (∃ (i j k l : Fin N) (f g : Bool), sampleFn D r c u v = editFn H i j k l f g) := by
  have hNpos : 0 < N := by omega
  rcases hr_coll with ⟨i₁, i₂, hi12, hri12⟩
  rcases hc_coll with ⟨k₁, k₂, hk12, hck12⟩
  let K := sampleFn D r c u v
  have heK : errorsFn H K < N := he
  let C0 : Finset (Fin N) := {k₁, k₂}
  rcases both_coll_extract_RC hN H D hH r c u v hi12 hri12 hk12 hck12 he with
    ⟨R, hR_card, hHK_agree⟩
  have hC0_card : C0.card ≤ 3 := by
    have : C0.card = 2 := Finset.card_pair hk12
    omega
  have hr_inj : Set.InjOn r (Rᶜ : Finset (Fin N)) := by
    intro a ha b hb hrab
    by_contra hab
    have hagree_row : ∀ j ∉ C0, H a j = xor (xor (u a) (u b)) (H b j) := by
      intro j hj
      rw [hHK_agree a (Finset.mem_compl.mp ha) j hj, hHK_agree b (Finset.mem_compl.mp hb) j hj]
      simp only [sampleFn, hrab]
      cases u a <;> cases u b <;> cases v j <;> cases D (r b) (c j) <;> decide
    have hsub :
        (Finset.univ : Finset (Fin N)).filter (fun j => H a j ≠ xor (xor (u a) (u b)) (H b j)) ⊆
        C0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hjC0
      exact hj (hagree_row j hjC0)
    have hfc := had_row_flip_count hH hab (xor (u a) (u b))
    have hle := Finset.card_le_card hsub
    have hC2 : C0.card = 2 := Finset.card_pair hk12
    omega
  have hc_inj : Set.InjOn c (C0ᶜ : Finset (Fin N)) := by
    intro a ha b hb hcab
    by_contra hab
    have hagree_col : ∀ i ∉ R, H i a = xor (xor (v a) (v b)) (H i b) := by
      intro i hi
      rw [hHK_agree i hi a (Finset.mem_compl.mp ha), hHK_agree i hi b (Finset.mem_compl.mp hb)]
      simp only [sampleFn, hcab]
      cases u i <;> cases v a <;> cases v b <;> cases D (r i) (c b) <;> decide
    have hsub :
        (Finset.univ : Finset (Fin N)).filter (fun i => H i a ≠ xor (xor (v a) (v b)) (H i b)) ⊆
        R := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hiR
      exact hi (hagree_col i hiR)
    have hfc := had_col_flip_count hNpos hH hab (xor (v a) (v b))
    have hle := Finset.card_le_card hsub
    omega
  rcases extend_injOn_perm (Rᶜ : Finset (Fin N)) r hr_inj with ⟨r0, hr0⟩
  rcases extend_injOn_perm (C0ᶜ : Finset (Fin N)) c hc_inj with ⟨c0, hc0⟩
  let D0 := sampleFn D r0 c0 u v
  have hD0 : isHad D0 := had_sample_perm hD r0 c0 u v
  have hHD0_agree : ∀ i ∉ R, ∀ j ∉ C0, H i j = D0 i j := by
    intro i hi j hj
    rw [hHK_agree i hi j hj]
    simp only [D0, sampleFn, hr0 i (Finset.mem_compl.mpr hi), hc0 j (Finset.mem_compl.mpr hj)]
  rcases had_completion_3x3 hNpos H D0 R C0 hH hD0 hR_card hC0_card hHD0_agree with
    ⟨p1, q1, a1, b1, hp1_out, hq1_out, hH_eq⟩
  let p : Equiv.Perm (Fin N) := p1.trans r0
  let q : Equiv.Perm (Fin N) := q1.trans c0
  let a : Fin N → Bool := fun i => xor (a1 i) (u (p1 i))
  let b : Fin N → Bool := fun j => xor (b1 j) (v (q1 j))
  have hH_sample : H = sampleFn D p q a b := by
    ext i j
    rw [hH_eq i j]
    simp only [D0, sampleFn, p, q, a, b, Equiv.trans_apply]
    cases a1 i <;> cases b1 j <;> cases u (p1 i) <;> cases v (q1 j) <;>
      cases D (r0 (p1 i)) (c0 (q1 j)) <;> decide
  let ρ : Fin N → Fin N := fun i => p.symm (r i)
  let γ : Fin N → Fin N := fun j => q.symm (c j)
  let α : Fin N → Bool := fun i => xor (u i) (a (ρ i))
  let β : Fin N → Bool := fun j => xor (v j) (b (γ j))
  have hK_H : ∀ i j : Fin N, K i j = sampleFn H ρ γ α β i j := by
    intro i j
    have hHρ : H (ρ i) (γ j) = xor (xor (a (ρ i)) (b (γ j))) (D (r i) (c j)) := by
      have := congr_fun (congr_fun hH_sample (ρ i)) (γ j)
      simpa only [sampleFn, ρ, γ, Equiv.apply_symm_apply] using this
    simp only [K, sampleFn, α, β, hHρ]
    cases u i <;> cases v j <;> cases a (ρ i) <;> cases b (γ j) <;>
      cases D (r i) (c j) <;> decide
  have hρ_out : ∀ i ∉ R, ρ i = i ∧ α i = false := by
    intro i hi
    have hp1i := hp1_out i hi
    have hpi : p i = r i := by
      simp only [p, Equiv.trans_apply, hp1i.1, hr0 i (Finset.mem_compl.mpr hi)]
    have hρi : ρ i = i := by
      simp only [ρ, ← hpi, Equiv.symm_apply_apply]
    refine ⟨hρi, ?_⟩
    simp only [α, hρi, a, hp1i.1, hp1i.2, Bool.false_xor, Bool.xor_self]
  have hγ_out : ∀ j ∉ C0, γ j = j ∧ β j = false := by
    intro j hj
    have hq1j := hq1_out j hj
    have hqj : q j = c j := by
      simp only [q, Equiv.trans_apply, hq1j.1, hc0 j (Finset.mem_compl.mpr hj)]
    have hγj : γ j = j := by
      simp only [γ, ← hqj, Equiv.symm_apply_apply]
    refine ⟨hγj, ?_⟩
    simp only [β, hγj, b, hq1j.1, hq1j.2, Bool.false_xor, Bool.xor_self]
  let A : Finset (Fin N) := Finset.univ.filter (fun i => ρ i ≠ i ∨ α i ≠ false)
  let B : Finset (Fin N) := Finset.univ.filter (fun j => γ j ≠ j ∨ β j ≠ false)
  have hA_sub : A ⊆ R := by
    intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hiR
    rcases hρ_out i hiR with ⟨h1, h2⟩
    rcases hi with h | h <;> exact h (by assumption)
  have hB_sub : B ⊆ C0 := by
    intro j hj
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hjC
    rcases hγ_out j hjC with ⟨h1, h2⟩
    rcases hj with h | h <;> exact h (by assumption)
  have hA_le3 : A.card ≤ 3 := le_trans (Finset.card_le_card hA_sub) hR_card
  have hB_le2 : B.card ≤ 2 := by
    have hC2 : C0.card = 2 := Finset.card_pair hk12
    exact le_trans (Finset.card_le_card hB_sub) (le_of_eq hC2)
  have hA_ge1 : 1 ≤ A.card := by
    by_contra h0
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by omega)
    have hρid : ∀ i : Fin N, ρ i = i := by
      intro i
      by_contra hne
      have : i ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hne⟩
      rw [hAe] at this
      exact Finset.notMem_empty i this
    have hEq : ρ i₁ = ρ i₂ := by simp [ρ, hri12]
    rw [hρid i₁, hρid i₂] at hEq
    exact hi12 hEq
  have hB_ge1 : 1 ≤ B.card := by
    by_contra h0
    have hBe : B = ∅ := Finset.card_eq_zero.mp (by omega)
    have hγid : ∀ j : Fin N, γ j = j := by
      intro j
      by_contra hne
      have : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ j, Or.inl hne⟩
      rw [hBe] at this
      exact Finset.notMem_empty j this
    have hEq : γ k₁ = γ k₂ := by simp [γ, hck12]
    rw [hγid k₁, hγid k₂] at hEq
    exact hk12 hEq
  have hrow_AB : ∀ i ∈ A, N ≤ 2 * (∑ j ∈ Bᶜ, errInd H K i j) + 2 * B.card := by
    intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hK_Bc : ∀ j ∈ Bᶜ, K i j = xor (α i) (H (ρ i) j) := by
      intro j hj
      simp only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hj
      rw [hK_H i j]
      simp [sampleFn, hj.1, hj.2]
    by_cases hρi : ρ i = i
    · have hαi : α i = true := by
        rcases hi with h | h
        · exact absurd hρi h
        · cases ha : α i <;> simp_all
      have hcnt : ∑ j ∈ Bᶜ, errInd H K i j = Bᶜ.card := by
        have h1 : ∀ j ∈ Bᶜ, errInd H K i j = 1 := by
          intro j hj
          simp only [errInd, hK_Bc j hj, hρi, hαi]
          cases H i j <;> decide
        rw [Finset.sum_congr rfl h1]
        simp
      rw [hcnt, Finset.card_compl, Fintype.card_fin]
      omega
    · have hfull := had_row_flip_count hH (Ne.symm hρi) (α i)
      have htot :
          ((Finset.univ : Finset (Fin N)).filter (fun j => H i j ≠ xor (α i) (H (ρ i) j))).card ≤
          (∑ j ∈ Bᶜ, errInd H K i j) + B.card := by
        rw [Finset.card_filter, ← Finset.sum_add_sum_compl B]
        have h1 : ∑ j ∈ B, (if H i j ≠ xor (α i) (H (ρ i) j) then 1 else 0) ≤ B.card := by
          calc
            ∑ j ∈ B, (if H i j ≠ xor (α i) (H (ρ i) j) then 1 else 0) ≤ ∑ _j ∈ B, 1 := by
              refine Finset.sum_le_sum fun j _ => by split_ifs <;> omega
            _ = B.card := by simp
        have h2 : ∑ j ∈ Bᶜ, (if H i j ≠ xor (α i) (H (ρ i) j) then 1 else 0) =
            ∑ j ∈ Bᶜ, errInd H K i j := by
          refine Finset.sum_congr rfl fun j hj => by simp only [errInd, hK_Bc j hj]
        omega
      omega
  have hcol_AB : ∀ j ∈ B, N ≤ 2 * (∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card := by
    intro j hj
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hK_Ac : ∀ i ∈ Aᶜ, K i j = xor (β j) (H i (γ j)) := by
      intro i hi
      simp only [A, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hi
      rw [hK_H i j]
      simp [sampleFn, hi.1, hi.2]
    by_cases hγj : γ j = j
    · have hβj : β j = true := by
        rcases hj with h | h
        · exact absurd hγj h
        · cases hb : β j <;> simp_all
      have hcnt : ∑ i ∈ Aᶜ, errInd H K i j = Aᶜ.card := by
        have h1 : ∀ i ∈ Aᶜ, errInd H K i j = 1 := by
          intro i hi
          simp only [errInd, hK_Ac i hi, hγj, hβj]
          cases H i j <;> decide
        rw [Finset.sum_congr rfl h1]
        simp
      rw [hcnt, Finset.card_compl, Fintype.card_fin]
      omega
    · have hfull := had_col_flip_count hNpos hH (Ne.symm hγj) (β j)
      have htot :
          ((Finset.univ : Finset (Fin N)).filter (fun i => H i j ≠ xor (β j) (H i (γ j)))).card ≤
          (∑ i ∈ Aᶜ, errInd H K i j) + A.card := by
        rw [Finset.card_filter, ← Finset.sum_add_sum_compl A]
        have h1 : ∑ i ∈ A, (if H i j ≠ xor (β j) (H i (γ j)) then 1 else 0) ≤ A.card := by
          calc
            ∑ i ∈ A, (if H i j ≠ xor (β j) (H i (γ j)) then 1 else 0) ≤ ∑ _i ∈ A, 1 := by
              refine Finset.sum_le_sum fun i _ => by split_ifs <;> omega
            _ = A.card := by simp
        have h2 : ∑ i ∈ Aᶜ, (if H i j ≠ xor (β j) (H i (γ j)) then 1 else 0) =
            ∑ i ∈ Aᶜ, errInd H K i j := by
          refine Finset.sum_congr rfl fun i hi => by simp only [errInd, hK_Ac i hi]
        omega
      omega
  have hsum_A : A.card * N ≤ 2 * (∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j) + 2 * A.card * B.card := by
    calc
      A.card * N = ∑ _i ∈ A, N := by simp
      _ ≤ ∑ i ∈ A, (2 * (∑ j ∈ Bᶜ, errInd H K i j) + 2 * B.card) := Finset.sum_le_sum hrow_AB
      _ = 2 * (∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j) + 2 * A.card * B.card := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp [mul_assoc, mul_left_comm]
  have hsum_B : B.card * N ≤ 2 * (∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card * B.card := by
    calc
      B.card * N = ∑ _j ∈ B, N := by simp
      _ ≤ ∑ j ∈ B, (2 * (∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card) := Finset.sum_le_sum hcol_AB
      _ = 2 * (∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j) + 2 * A.card * B.card := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp [mul_assoc, mul_comm]
  have hdisj_err :
      (∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j) + (∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j) ≤
      errorsFn H K := by
    rw [errors_eq_sum_ind, ← Finset.sum_add_sum_compl A]
    have h1 : ∑ i ∈ A, ∑ j ∈ Bᶜ, errInd H K i j ≤ ∑ i ∈ A, ∑ j : Fin N, errInd H K i j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have h2 : ∑ j ∈ B, ∑ i ∈ Aᶜ, errInd H K i j ≤ ∑ i ∈ Aᶜ, ∑ j : Fin N, errInd H K i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have hAB_ineq : (A.card + B.card) * N ≤ 2 * errorsFn H K + 4 * A.card * B.card := by
    have h4 : 2 * A.card * B.card + 2 * A.card * B.card = 4 * A.card * B.card := by ring
    rw [add_mul]
    omega
  have hAB1 := ab_force_one hN heK hA_ge1 hA_le3 hB_ge1 hB_le2 hAB_ineq
  have hA1 : A.card = 1 := hAB1.1
  have hB1 : B.card = 1 := hAB1.2
  rcases Finset.card_eq_one.mp hA1 with ⟨i₀, hi₀⟩
  rcases Finset.card_eq_one.mp hB1 with ⟨k₀, hk₀⟩
  have hρ_other : ∀ x : Fin N, x ≠ i₀ → ρ x = x ∧ α x = false := by
    intro x hx
    have hxA : x ∉ A := by rw [hi₀, Finset.mem_singleton]; exact hx
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hxA
    exact hxA
  have hγ_other : ∀ y : Fin N, y ≠ k₀ → γ y = y ∧ β y = false := by
    intro y hy
    have hyB : y ∉ B := by rw [hk₀, Finset.mem_singleton]; exact hy
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hyB
    exact hyB
  have hρ_ne : ρ i₀ ≠ i₀ := by
    intro heq
    have hρid : ∀ x : Fin N, ρ x = x := fun x => by
      by_cases hx : x = i₀
      · subst hx; exact heq
      · exact (hρ_other x hx).1
    have hEq : ρ i₁ = ρ i₂ := by simp [ρ, hri12]
    rw [hρid i₁, hρid i₂] at hEq
    exact hi12 hEq
  have hγ_ne : γ k₀ ≠ k₀ := by
    intro heq
    have hγid : ∀ y : Fin N, γ y = y := fun y => by
      by_cases hy : y = k₀
      · subst hy; exact heq
      · exact (hγ_other y hy).1
    have hEq : γ k₁ = γ k₂ := by simp [γ, hck12]
    rw [hγid k₁, hγid k₂] at hEq
    exact hk12 hEq
  refine ⟨⟨p, q, a, b, hH_sample⟩, ⟨i₀, ρ i₀, k₀, γ k₀, α i₀, β k₀, ?_⟩⟩
  ext x y
  change K x y = editFn H i₀ (ρ i₀) k₀ (γ k₀) (α i₀) (β k₀) x y
  rw [hK_H x y]
  by_cases hx : x = i₀ <;> by_cases hy : y = k₀
  · subst hx; subst hy
    simp [sampleFn, editFn, hρ_ne.symm, hγ_ne.symm]
  · subst hx
    rcases hγ_other y hy with ⟨h1, h2⟩
    simp [sampleFn, editFn, hρ_ne.symm, hy, h1, h2]
  · subst hy
    rcases hρ_other x hx with ⟨h1, h2⟩
    simp [sampleFn, editFn, hγ_ne.symm, hx, h1, h2]
  · rcases hρ_other x hx with ⟨h1, h2⟩
    rcases hγ_other y hy with ⟨h3, h4⟩
    simp [sampleFn, editFn, hx, hy, h1, h2, h3, h4]

private lemma classify_all {N : ℕ} (hN : 8 ≤ N)
    (H D : Fin N → Fin N → Bool) (hH : isHad H) (hD : isHad D)
    (r c : Fin N → Fin N) (u v : Fin N → Bool)
    (he : errorsFn H (sampleFn D r c u v) < N) :
    (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sampleFn D p q a b) ∧
    (∃ (i j k l : Fin N) (f g : Bool), sampleFn D r c u v = editFn H i j k l f g) := by
  have hNpos : 0 < N := by omega
  by_cases hc : Function.Injective c
  · exact classify_col_inj hN H D hH hD r c u v hc he
  · by_cases hr : Function.Injective r
    · let Ht : Fin N → Fin N → Bool := fun j i => H i j
      let Dt : Fin N → Fin N → Bool := fun j i => D i j
      have hHt : isHad Ht := had_transpose hNpos hH
      have hDt : isHad Dt := had_transpose hNpos hD
      have hsample_t : ∀ j i : Fin N, sampleFn Dt c r v u j i = sampleFn D r c u v i j := by
        intro j i
        simp only [sampleFn, Dt, Bool.xor_comm (v j) (u i)]
      have herr_t : errorsFn Ht (sampleFn Dt c r v u) = errorsFn H (sampleFn D r c u v) := by
        rw [errors_eq_sum_ind, errors_eq_sum_ind, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [errInd, Ht, hsample_t j i]
      rw [← herr_t] at he
      rcases classify_col_inj hN Ht Dt hHt hDt c r v u hr he with
        ⟨⟨q, p, b, a, hHt_eq⟩, ⟨k, l, i, j, g, f, hKt_eq⟩⟩
      refine ⟨⟨p, q, a, b, ?_⟩, ⟨i, j, k, l, f, g, ?_⟩⟩
      · ext x y
        have h1 := congr_fun (congr_fun hHt_eq y) x
        simp only [Ht, Dt, sampleFn, Bool.xor_comm (b y) (a x)] at h1
        exact h1
      · ext x y
        have h1 := congr_fun (congr_fun hKt_eq y) x
        rw [hsample_t y x] at h1
        rw [h1]
        simp only [editFn, Ht, Bool.xor_comm]
    · have hr_coll : ∃ i₁ i₂ : Fin N, i₁ ≠ i₂ ∧ r i₁ = r i₂ := by
        unfold Function.Injective at hr
        push Not at hr
        rcases hr with ⟨i₁, i₂, h1, h2⟩
        exact ⟨i₁, i₂, h2, h1⟩
      have hc_coll : ∃ k₁ k₂ : Fin N, k₁ ≠ k₂ ∧ c k₁ = c k₂ := by
        unfold Function.Injective at hc
        push Not at hc
        rcases hc with ⟨k₁, k₂, h1, h2⟩
        exact ⟨k₁, k₂, h2, h1⟩
      exact classify_both_coll hN H D hH hD r c u v hr_coll hc_coll he

end PEqualNP.Outside.L_meta_25783_aux.Rigidity


namespace PEqualNP.Outside.L_meta_25783_aux.Rigidity
theorem sharp : (∀ N : ℕ, 8 ≤ N →
  let T := Fin N → Fin N → Bool
  let had := fun (M : T) => ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N
  let sample := fun (D : T) (r c : Fin N → Fin N) (u v : Fin N → Bool) (i j : Fin N) =>
    xor (xor (u i) (v j)) (D (r i) (c j))
  let errors := fun (A B : T) =>
    ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => A i j ≠ B i j)).card
  let edit := fun (H : T) (i j k l : Fin N) (f g : Bool) (x y : Fin N) =>
    xor (xor (if x = i ∧ i ≠ j then f else false) (if y = k ∧ k ≠ l then g else false))
      (H (if x = i then j else x) (if y = k then l else y))
  ∀ H D : T, had H → had D →
    (∀ (r c : Fin N → Fin N) (u v : Fin N → Bool),
      let K := sample D r c u v
      let e := errors H K
      e < N →
        (∃ (p q : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sample D p q a b) ∧
        (∃ (i j k l : Fin N) (f g : Bool), K = edit H i j k l f g) ∧
        (e = 0 ∨ 2*e = N ∨ e+2 = N ∨ e+1 = N)) ∧
    (∃ (i j k l : Fin N) (f g : Bool),
      i ≠ j ∧ k ≠ l ∧ errors H (edit H i j k l f g) + 1 = N)) := by
  intro N hN T had sample errors edit H D hH hD
  have hNpos : 0 < N := by omega
  constructor
  · intro r c u v K e he
    rcases classify_all hN H D hH hD r c u v he with ⟨h1, ⟨i, j, k, l, f, g, h2⟩⟩
    refine ⟨h1, ⟨i, j, k, l, f, g, h2⟩, ?_⟩
    have hKeq : K = editFn H i j k l f g := h2
    have he' : errorsFn H (editFn H i j k l f g) < N := by
      have he0 : errorsFn H K < N := he
      rwa [← hKeq]
    have hcases := errors_edit_cases hNpos hH i j k l f g he'
    have hcases' : errorsFn H K = 0 ∨ 2 * errorsFn H K = N ∨
        errorsFn H K + 2 = N ∨ errorsFn H K + 1 = N := by
      rwa [hKeq]
    exact hcases'
  · exact exists_neg_edit hN hH

end PEqualNP.Outside.L_meta_25783_aux.Rigidity

namespace PEqualNP.Outside.L_meta_25783_aux
open Work Work.Sampling Work.Ranks
abbrev F2 := ZMod 2
abbrev Vec (k : ℕ) := Fin k → F2
abbrev Idx (s : ℕ) := Fin (4^s)
theorem size_eq (s : ℕ) : 4^s=2^(2*s) := by rw [pow_mul]; norm_num
def bits {k n} (x : Fin n) (a : Fin k) : F2 := b2z (x.val.testBit a.val)
theorem bitsInj {k n} (nsize : n=2^k) : Function.Injective (bits (n:=n) (k:=k)) := by
  intro x y eq; apply Fin.ext; apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < k
  · exact b2z_inj (congrFun eq ⟨i,hi⟩)
  · have en := Nat.pow_le_pow_right (by decide : 0<2) (by omega : k ≤ i)
    have lx : x.val<2^i := by rw [←nsize] at en; omega
    have ly : y.val<2^i := by rw [←nsize] at en; omega
    simp [Nat.testBit_lt_two_pow lx,Nat.testBit_lt_two_pow ly]
noncomputable def names {k n} (nsize : n=2^k) : Fin n ≃ Vec k :=
  Equiv.ofBijective bits ((Fintype.bijective_iff_injective_and_card _).2
    ⟨bitsInj nsize,by simp [Vec,F2,ZMod.card,nsize]⟩)
def ax (s : ℕ) (x y : Idx s) := decide ((∑ b : Fin (2*s),if x.val.testBit b.val && y.val.testBit b.val then 1 else 0) % 2=1)
def sw (s : ℕ) (x y : Idx s) := xor (ax s x y) (decide (x.val<4) && y.val.testBit 0 && y.val.testBit 1)
def ip {k} (u v : Vec k) := ∑ i,u i*v i
theorem ax_cast {s} (x y : Idx s) : b2z (ax s x y)=ip (bits x : Vec (2*s)) (bits y) := by
  let f (b : Fin (2*s)) := if x.val.testBit b.val && y.val.testBit b.val then (1:ℕ) else 0
  have cast (b : Fin (2*s)) : (f b : F2)=bits x b*bits y b := by
    unfold f bits; cases x.val.testBit b.val <;> cases y.val.testBit b.val <;> decide
  have total : ((∑ i,f i : ℕ):F2)=ip (bits x : Vec (2*s)) (bits y) := by simp only [Nat.cast_sum,cast,ip]
  rw [←total]
  have h : ((∑ i,f i : ℕ):F2)=1 ↔ (∑ i,f i : ℕ) % 2=1 := by
    rw [← Nat.cast_one (R:=F2),ZMod.natCast_eq_natCast_iff']
  change b2z (decide ((∑ i,f i) % 2=1))=_
  simp only [←h,Work.bit_dec]
theorem ax_repr {s} (x y : Idx s) : ax s x y=decide (ip (bits x : Vec (2*s)) (bits y)=1) := by
  apply b2z_inj; rw [Work.bit_dec,ax_cast]
theorem btrue (b : Bool) : b2z b=1 ↔ b=true := by cases b <;> decide
theorem bfalse (b : Bool) : b2z b=0 ↔ b=false := by cases b <;> decide
def oneOnly {k} (i : Fin k) : Vec k := fun j=>if i=j then 1 else 0
theorem ip_one {k} (u : Vec k) (i : Fin k) : ip u (oneOnly i)=u i := by
  simp [ip,oneOnly,mul_ite]
theorem ip_addr {k} (u v w : Vec k) : ip u (v+w)=ip u v+ip u w := by
  simp only [ip,Pi.add_apply,mul_add,Finset.sum_add_distrib]
theorem ip_addl {k} (u v w : Vec k) : ip (u+v) w=ip u w+ip v w := by
  simp only [ip,Pi.add_apply,add_mul,Finset.sum_add_distrib]


end PEqualNP.Outside.L_meta_25783_aux

namespace PEqualNP.Outside.L_meta_25783_aux
open Work Work.Sampling Work.Ranks
theorem hi_exists {k n} (hn:n=2^k) (x : Fin n) (hi : 4 ≤ x.val) :
    ∃ i : Fin k,2 ≤ i.val ∧ x.val.testBit i.val=true := by
  by_contra! no
  have e : x.val % 4=x.val := by
    apply Nat.eq_of_testBit_eq; intro i
    change (x.val % 2^2).testBit i=x.val.testBit i
    rw [Nat.testBit_mod_two_pow]
    by_cases lo:i<2
    · simp [lo]
    · by_cases inr : i < k
      · have zz:=no ⟨i,inr⟩ (show 2 ≤ i by omega); simpa [lo] using zz.symm
      · have cap:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : k ≤ i)
        have zz:=Nat.testBit_lt_two_pow (show x.val<2^i by rw [←hn] at cap;omega)
        simp [lo,zz]
  omega
theorem differing {s} (x z : Idx s) (ne:x≠z) :
    ∃ i : Fin (2*s),bits x i≠bits z i ∧ ((x.val<4 ↔ z.val<4) ∨ 2 ≤ i.val) := by
  by_cases same : x.val<4 ↔ z.val<4
  · have diff : bits x ≠ (bits z : Vec (2*s)) := fun h=>ne (bitsInj (size_eq s) h)
    by_contra! none
    apply diff; funext i
    by_contra nz; have h:=(none i nz).1; omega
  · have cross (a b : Idx s) (lo : a.val<4) (hi : 4 ≤ b.val) :
        ∃ i : Fin (2*s),bits a i≠bits b i ∧ 2 ≤ i.val := by
      obtain ⟨i,up,bit⟩:=hi_exists (size_eq s) b hi
      have cap:=Nat.pow_le_pow_right (by decide : 0<2) up
      have no:=Nat.testBit_lt_two_pow (show a.val<2^i.val by omega)
      exact ⟨i,by simp [bits,no,bit,b2z],up⟩
    by_cases lx:x.val<4
    · obtain ⟨i,nz,h⟩:=cross x z lx (by omega)
      exact ⟨i,nz,Or.inr h⟩
    · obtain ⟨i,nz,h⟩:=cross z x (by omega) (by omega)
      exact ⟨i,Ne.symm nz,Or.inr h⟩
noncomputable def flipName {s} (i : Fin (2*s)) (y : Idx s) : Idx s :=
  (names (size_eq s)).symm ((bits y : Vec (2*s))+oneOnly i)
theorem flip_bits {s} (i : Fin (2*s)) (y : Idx s) :
    bits (flipName i y)=(bits y : Vec (2*s))+oneOnly i := (names (size_eq s)).apply_symm_apply _
theorem flip_flip {s} (i : Fin (2*s)) (y : Idx s) : flipName i (flipName i y)=y := by
  apply bitsInj (size_eq s); rw [flip_bits,flip_bits]
  funext k; simp only [Pi.add_apply,add_assoc,zmod2_add_self,add_zero]
theorem quad_stable {s} (i : Fin (2*s)) (hi : 2 ≤ i.val) (y : Idx s) :
    (flipName i y).val.testBit 0=y.val.testBit 0 ∧
    (flipName i y).val.testBit 1=y.val.testBit 1 := by
  have eq (b : ℕ) (lb : b<2) : (flipName i y).val.testBit b=y.val.testBit b := by
    let j : Fin (2*s) := ⟨b,by omega⟩
    apply b2z_inj
    change bits (flipName i y) j=bits y j
    rw [flip_bits]; simp [oneOnly,show i≠j by intro e; have := congrArg Fin.val e; dsimp [j] at this;omega]
  exact ⟨eq 0 (by decide),eq 1 (by decide)⟩
theorem flip_diff {s} (x z : Idx s) (i : Fin (2*s)) (ne:bits x i≠bits z i)
    (ok : (x.val<4 ↔ z.val<4) ∨ 2 ≤ i.val) (y : Idx s) :
    sw s x (flipName i y)≠sw s z (flipName i y) ↔ sw s x y=sw s z y := by
  have flip (a : Idx s) : b2z (ax s a (flipName i y))=b2z (ax s a y)+bits a i := by
    rw [ax_cast,ax_cast,flip_bits,ip_addr,ip_one]
  have different : ∀ p q a b:F2, a≠b→(p+a≠q+b ↔ p=q) := by decide
  have inj (a b:Bool) : a=b ↔ b2z a=b2z b := ⟨fun e=>e ▸ rfl,b2z_inj⟩
  simp only [ne_eq,inj,sw,b2z_xor,flip]
  rcases ok with same|up
  · have eq : decide (x.val<4)=decide (z.val<4) := by simp [same]
    rw [eq]; simp only [add_left_inj]
    exact different _ _ _ _ ne
  · obtain ⟨h0,h1⟩:=quad_stable i up y
    rw [h0,h1,add_right_comm (b2z (ax s x y)) (bits x i),add_right_comm (b2z (ax s z y)) (bits z i)]
    exact different _ _ _ _ ne
theorem switchedHad (s : ℕ) : Work.Sampling.Had (sw s) := by
  classical
  intro x z ne
  obtain ⟨i,di,ok⟩:=differing x z ne
  let D:=Finset.univ.filter (fun y=>sw s x y≠sw s z y)
  have mem (y : Idx s) : y∈D ↔ sw s x y≠sw s z y := by simp [D]
  have toggle (y : Idx s) : flipName i y ∈D ↔ y∉D := by simpa only [mem,not_not] using flip_diff x z i di ok y
  have e : D.card=Dᶜ.card := by
    apply Finset.card_bij (fun y _=>flipName i y)
    · intro y hy; apply Finset.mem_compl.mpr; exact fun hf=>((toggle y).mp hf) hy
    · intro a _ b _ eq; rw [←flip_flip i a,←flip_flip i b,eq]
    · intro y hy; exact ⟨flipName i y,(toggle y).mpr (Finset.mem_compl.mp hy),flip_flip i y⟩
  rw [dist_card]
  have h:=Finset.card_compl_add_card D
  simp only [Fintype.card_fin] at h
  change 2*D.card=_; omega


end PEqualNP.Outside.L_meta_25783_aux

namespace PEqualNP.Outside.L_meta_25783_aux
open Work Work.Sampling Work.Ranks
def bigN {s} (hs : 2 ≤ s) : 16≤4^s := (by decide : 16≤4^2).trans (Nat.pow_le_pow_right (by decide) hs)
def fourRow {s} (hs : 2 ≤ s) : Idx s := ⟨4,by have := bigN hs;omega⟩
def eightRow {s} (hs : 2 ≤ s) : Idx s := ⟨8,by have := bigN hs;omega⟩
def twelveRow {s} (hs : 2 ≤ s) : Idx s := ⟨12,by have := bigN hs;omega⟩
theorem threeRows {s} (hs : 2 ≤ s) (y : Idx s) :
    b2z (sw s (fourRow hs) y)+b2z (sw s (eightRow hs) y)+b2z (sw s (twelveRow hs) y)=0 := by
  have eq : (bits (fourRow hs) : Vec (2*s))+bits (eightRow hs)=bits (twelveRow hs) := by
    funext i
    change b2z ((4:ℕ).testBit i.val)+b2z ((8:ℕ).testBit i.val)=b2z ((12:ℕ).testBit i.val)
    rw [←b2z_xor,←Nat.testBit_xor]; rfl
  have clean (x : Idx s) (cap : 4 ≤ x.val) : sw s x y=ax s x y := by simp [sw,show ¬x.val<4 by omega]
  rw [clean _ (by change 4≤4;decide),clean _ (by change 4≤8;decide),clean _ (by change 4≤12;decide),ax_cast,ax_cast,ax_cast,←ip_addl,eq,zmod2_add_self]
theorem nonconstant {s} (hs : 2 ≤ s) (x : Idx s) :
    ∃ a b,sw s x a≠sw s x b := by
  have hn:=bigN hs
  let z : Idx s := ⟨0,by omega⟩
  have bz : (bits z : Vec (2*s))=0 := by funext i; simp [bits,z,b2z]
  have base : sw s x z=false := by
    rw [sw,ax_repr,bz]; simp [ip,z]
  by_cases zero : x.val=0
  · let a : Idx s := ⟨3,by omega⟩
    have bx : (bits x : Vec (2*s))=0 := by funext i; simp [bits,zero,b2z]
    refine ⟨a,z,?_⟩; rw [base,sw,ax_repr,bx]
    simp [ip,zero,a] <;> decide
  · have nz : (bits x : Vec (2*s))≠0 := by
      intro bh; have en:=bitsInj (size_eq s) (bh.trans bz.symm); exact zero (congrArg Fin.val en)
    obtain ⟨i,bi⟩ : ∃ i : Fin (2*s),bits x i≠0 := by
      by_contra! h; exact nz (funext h)
    let a : Idx s := (names (size_eq s)).symm (oneOnly i)
    have ba : bits a = oneOnly i := (names (size_eq s)).apply_symm_apply _
    have unique : ¬(a.val.testBit 0=true ∧ a.val.testBit 1=true) := by
      rintro ⟨h0,h1⟩
      let u0 : Fin (2*s) := ⟨0,by omega⟩
      let u1 : Fin (2*s) := ⟨1,by omega⟩
      have coord (v : Fin (2*s)) (h : a.val.testBit v.val=true) : i=v := by
        by_contra e
        have m:=congrFun ba v
        simp [bits,h,oneOnly,e,b2z] at m
      have e0:=coord u0 h0; have e1:=coord u1 h1
      have e:=congrArg Fin.val (e0.symm.trans e1); change (0:ℕ)=1 at e;omega
    have veto : (decide (x.val<4) && a.val.testBit 0 && a.val.testBit 1)=false := by
      cases h0:a.val.testBit 0 <;> cases h1:a.val.testBit 1 <;> simp [h0,h1] at unique ⊢
    have one := (by decide : ∀ z:F2,z≠0 → z=1) _ bi
    exact ⟨a,z,by rw [base,sw,veto,ax_repr,ba,ip_one,one]; decide⟩
theorem notSylv {s} (hs:2 ≤ s) :
    ¬∃ (r c : Idx s ≃ Vec (2*s)) (u v : Idx s→Bool),∀ x y,
      sw s x y=xor (xor (u x) (v y)) (decide (ip (r x) (c y)=1)) := by
  rintro ⟨r,c,u,v,rep⟩
  let a:=fourRow hs;let b:=eightRow hs;let d:=twelveRow hs
  let k:=r.symm (r a+r b+r d)
  have eq (x y : Idx s) : b2z (sw s x y)=b2z (u x)+b2z (v y)+ip (r x) (c y) := by rw [rep,b2z_xor,b2z_xor,Work.bit_dec]
  have constant (y : Idx s) : b2z (sw s k y)=b2z (u k)+b2z (u a)+b2z (u b)+b2z (u d) := by
    have h:=threeRows hs y
    change b2z (sw s a y)+b2z (sw s b y)+b2z (sw s d y)=0 at h
    rw [eq a,eq b,eq d] at h
    rw [eq k,show r k=r a+r b+r d from r.apply_symm_apply _,ip_addl,ip_addl]
    linear_combination h - zmod2_add_self (b2z (v y)) - zmod2_add_self (b2z (u a)) -
      zmod2_add_self (b2z (u b)) - zmod2_add_self (b2z (u d))
  obtain ⟨x,y,ne⟩:=nonconstant hs k
  exact ne (b2z_inj ((constant x).trans (constant y).symm))


end PEqualNP.Outside.L_meta_25783_aux

namespace PEqualNP.Outside.L_meta_25783_aux
open Work Work.Sampling Work.Ranks
theorem two_bits (a : ℕ) : a.testBit 0=true ∧ a.testBit 1=true ↔ a % 4=3 := by
  have h0 : (a % 4).testBit 0=a.testBit 0 := by change (a % 2^2).testBit 0=_; simp [Nat.testBit_mod_two_pow]
  have h1 : (a % 4).testBit 1=a.testBit 1 := by
    change (a % 2^2).testBit 1=_
    rw [Nat.testBit_mod_two_pow]; simp
  rw [←h0,←h1]; generalize h : a % 4=b
  have cap : b<4 := by omega
  interval_cases b <;> decide
theorem switch_count {s} (hs : 2 ≤ s) : err (sw s) (ax s)=4^s := by
  classical
  let n:=4^s
  let m:=4^(s-1)
  have size : n=m*4 := by unfold n m; conv_lhs => rw [show s=(s-1)+1 by omega,pow_succ]
  let B := Finset.univ.filter (fun j : Idx s=>j.val % 4=3)
  have bc : B.card=m := by
    apply Eq.trans _ (show (Finset.univ : Finset (Fin m)).card=m by simp)
    apply Finset.card_bij (fun (j : Idx s) _ => (⟨j.val/4,by have hj:j.val < n := j.isLt;omega⟩ : Fin m))
    · simp
    · intro a ha b hb eq
      have e:=congrArg Fin.val eq
      have h1 : a.val % 4=3 := (Finset.mem_filter.mp ha).2
      have h2 : b.val % 4=3 := (Finset.mem_filter.mp hb).2
      apply Fin.ext; change a.val/4=b.val/4 at e;omega
    · intro a _
      let j : Idx s:=⟨4*a.val+3,by change 4*a.val+3 < n;have:=a.isLt;omega⟩
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [j];omega⟩,Fin.ext (by dsimp [j];omega)⟩
  let I := Finset.univ.filter (fun x : Idx s=>x.val<4)
  have ic : I.card=4 := by
    apply Eq.trans _ (show (Finset.univ : Finset (Fin 4)).card=4 by simp)
    apply Finset.card_bij (fun x hx=>(⟨x.val,(Finset.mem_filter.mp hx).2⟩ : Fin 4))
    · simp
    · intro a _ b _ h; exact Fin.ext (congrArg (fun x : Fin 4=>x.val) h)
    · intro j _; have hn:=bigN hs
      exact ⟨⟨j.val,by omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.isLt⟩,rfl⟩
  have row (x : Idx s) : dist (sw s x) (ax s x) = if x.val<4 then m else 0 := by
    rw [dist_card]
    by_cases h:x.val<4
    · rw [if_pos h,←bc]; congr 1; ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,B]
      have e : ∀ a b : Bool, xor a b≠a ↔ b=true := by decide
      simp only [sw,h,decide_true,Bool.true_and,e,Bool.and_eq_true,two_bits]
    · simp [sw,h]
  unfold err; simp only [row]
  calc
    _ = ∑ x∈I,m := by unfold I; rw [Finset.sum_filter]
    _ = n := by simp [ic,size,mul_comm]


end PEqualNP.Outside.L_meta_25783_aux

namespace PEqualNP.Outside.L_meta_25783_aux
open Work Work.Sampling Work.Ranks
theorem separate {s} (hs:2 ≤ s) (H : T (4^s)) (hh : Had H) (C) (vc : valid2 (4^s) s C)
    (small: err H (fun x y=>C.eval (PEqualNP.Represents.oneEach x y))<4^s) :
    ∃ (row col : Idx s ≃ Vec (2*s)) (Q R : Idx s→Bool),∀ i j,
       H i j=xor (xor (Q i) (R j)) (decide (ip (row i) (col j)=1)) := by
  classical
  have hn:=bigN hs
  let e := names (size_eq s)
  let D:=predT e e (fun _=>false) (fun _=>false)
  have hd : Had D:=canonicalHad (by omega) e
  obtain ⟨r,c,u,v,rep⟩:=normalNear hs rfl hh C vc small
  let r0:=e.symm ∘ r;let c0:=e.symm ∘ c
  have rs : sam D r0 c0 u v=predT r c u v := by funext i j; simp [r0,c0,D,predT,sam]
  have hadCard {A : T (4^s)} (h:Had A) (a b : Idx s) (d:a≠b) :
      2*(Finset.univ.filter (fun j=>A a j≠A b j)).card=4^s := by rw [←dist_card]; exact h a b d
  have th := Rigidity.sharp (4^s) (by omega) H D (hadCard hh) (hadCard hd)
  have ok : err H (sam D r0 c0 u v)<4^s := by rw [rs,←rep];exact small
  obtain ⟨⟨a,b,f,g,eq⟩,_,_⟩ := th.1 r0 c0 u v (by
    convert ok using 2
    apply Finset.sum_congr rfl
    intro i _; rw [dist_card]; congr 1)
  refine ⟨a.trans e,b.trans e,f,g,?_⟩
  intro x y; have he := congrFun (congrFun eq x) y
  rw [he]; simp [D,predT,ip] <;> rfl


end PEqualNP.Outside.L_meta_25783_aux

open PEqualNP.Outside.L_meta_25783_aux in
theorem PEqualNP.Outside.L_meta_25783 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
∀ s : ℕ, 2 ≤ s →
  let N := 4^s
  let T := Fin N → Fin N → Bool
  let V := Fin (2*s) → ZMod 2
  let had := fun (H : T) => ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => H a j ≠ H b j)).card = N
  let sylvester := fun (H : T) => ∃ (r c : Fin N ≃ V) (u v : Fin N → Bool),
    ∀ i j, H i j = xor (xor (u i) (v j)) (decide ((∑ b : Fin (2*s), r i b * c j b) = 1))
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.gates.countP nonlinear ≤ s
  let errors := fun (H : T) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j =>
      H i j ≠ C.eval (PEqualNP.Represents.oneEach i j))).card
  let dot := fun (i j : Fin N) => decide
    ((∑ b : Fin (2*s), if i.val.testBit b.val && j.val.testBit b.val then 1 else 0) % 2 = 1)
  let switched := fun (i j : Fin N) =>
    xor (dot i j) (decide (i.val < 4) && j.val.testBit 0 && j.val.testBit 1)
  (∀ H : T, had H → ¬ sylvester H → ∀ C, valid C → N ≤ errors H C) ∧
    had switched ∧ ¬ sylvester switched ∧
    (∃ C, valid C ∧ (∀ i j, C.eval (PEqualNP.Represents.oneEach i j) = dot i j) ∧
      errors switched C = N)
) := by
  classical
  intro nonlinear s hs N T V had sylvester valid errors dot switched
  have hd (A : T) : had A ↔ Work.Sampling.Had A := by
    constructor
    · intro h a b ne; rw [Work.Sampling.dist_card];exact h a b ne
    · intro h a b ne; rw [←Work.Sampling.dist_card];exact h a b ne
  have er (H : T) (C) : errors H C=Work.Sampling.err H (fun i j=>C.eval (PEqualNP.Represents.oneEach i j)) := by
    dsimp only [errors,Work.Sampling.err]; simp only [Work.Sampling.dist_card]
  refine ⟨?_,(hd _).mpr (switchedHad s),notSylv hs,?_⟩
  · intro H hh hn C hv
    by_contra! wrong
    rw [er] at wrong
    exact hn (separate hs H ((hd _).mp hh) C hv wrong)
  · let e:=names (size_eq s)
    obtain ⟨C,hc,rep⟩:=Work.sampled_implementation (n:=N) (s:=s) (by dsimp [N];positivity) e e (fun _=>false) (fun _=>false)
    have eq (i j : Idx s) : C.eval (PEqualNP.Represents.oneEach i j)=ax s i j := by
      rw [rep i j,ax_repr]; simp [Work.predT,ip,e,names] <;> rfl
    refine ⟨C,hc,eq,?_⟩
    rw [er]; change Work.Sampling.err (sw s) (fun i j=>C.eval (PEqualNP.Represents.oneEach i j))=4^s
    rw [show (fun i j=>C.eval (PEqualNP.Represents.oneEach i j))=ax s from funext (fun i=>funext (eq i))]
    exact switch_count hs

