import Mathlib.Data.Matrix.ColumnRowPartitioned
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33623_aux

-- The circuit criterion and its proof are adapted from ovolee37, L_meta_25647 (PR 39024).
section CircuitCriterion
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

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
end CircuitCriterion

section MatrixBounds
open Matrix
abbrev F := ZMod 2
abbrev Mat (i j : Nat) := Matrix (Fin i) (Fin j) F
abbrev Sq (r : Nat) := Mat r r

def bit (b : Bool) : F := (b.toNat : F)
theorem bit_eq (b : Bool) : bit b=b2z b := by cases b <;> rfl
theorem bit_dec (x : F) : bit (decide (x=1))=x := by revert x;decide
theorem xor_bit (a b : Bool) : bit (xor a b)=bit a-bit b := by cases a <;> cases b <;> decide
theorem two (a : F) : a+a=0 := by revert a;decide

theorem addRank (A B : Mat m n) : (A+B).rank≤A.rank+B.rank := by
  have h := LinearMap.rank_add_le A.mulVecLin B.mulVecLin
  simp only [LinearMap.rank, ← Submodule.finrank_eq_rank, ← Nat.cast_add] at h
  change Module.finrank F (LinearMap.range (A+B).mulVecLin)≤_
  rw [Matrix.mulVecLin_add]
  exact_mod_cast h

theorem dist (A B C : Mat m n) : (A-C).rank≤(A-B).rank+(B-C).rank := by
  simpa only [sub_add_sub_cancel] using addRank (A-B) (B-C)

theorem factor (A : Mat m n) (h : A.rank≤w) : ∃ U : Mat m w, ∃ V : Mat w n, U*V=A := by
  obtain ⟨u,v,eq⟩ := factor_of_rank_le A h
  exact ⟨fun i k => u k i,v,by ext i j;exact (eq i j).symm⟩

/-- The diagonal and successor products are identities after changing bases on each panel. -/
def Frames (k r w : Nat) (H : Sq r) :=
  ∃ (A : Fin (k+2) → Mat r w) (B : Fin (k+2) → Mat w r),
    (∀ i, A i * B i=1) ∧ (∀ j : Fin (k+1), A j.castSucc * B j.succ=1) ∧
    A (Fin.last (k+1)) * B 0=H

theorem necessary {H : Sq r} (h : Frames k r w H) :
    r≤w ∧ r≤H.rank+(w-r) ∧ (1-H).rank≤(k+1)*(w-r) := by
  obtain ⟨A,B,diag,next,last⟩ := h
  have leA (i) : r≤(A i).rank := by simpa [diag] using rank_mul_le_left (A i) (B i)
  have leB (i) : r≤(B i).rank := by simpa [diag] using rank_mul_le_right (A i) (B i)
  have rw' : r≤w := (leA 0).trans (by simpa using rank_le_card_width (A 0))
  have close := rank_mul_ge (A (Fin.last (k+1))) (B 0)
  rw [last,Fintype.card_fin] at close
  have lo := leA (Fin.last (k+1))
  have ro := leB 0
  refine ⟨rw',by omega,?_⟩
  let S := fun i => A i * B 0
  have step (j : Fin (k+1)) : (S j.castSucc-S j.succ).rank≤w-r := by
    have z : (A j.castSucc-A j.succ)*B j.succ=0 := by rw [Matrix.sub_mul,next,diag,sub_self]
    have d := rank_add_rank_le_card_of_mul_eq_zero z
    rw [Fintype.card_fin] at d
    have b := leB j.succ
    have v := rank_mul_le_left (A j.castSucc-A j.succ) (B 0)
    rw [Matrix.sub_mul] at v
    exact v.trans (by omega)
  have run (i : Fin (k+2)) : (S 0-S i).rank≤ i.val*(w-r) := by
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      have d := dist (S 0) (S j.castSucc) (S j.succ)
      have s := step j
      simpa [Fin.val_succ,Nat.succ_mul] using d.trans (Nat.add_le_add ih s)
  have h := run (Fin.last (k+1))
  simpa [S,diag,last] using h

def Anchor (P : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) : Mat n m :=
  fun a b => bit (P a b)+bit (P u b)+bit (P a v)+bit (P u v)

theorem criterion (P : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t) :
    (Anchor P u v).rank≤2*t ↔ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    ((∀ g∈C.gates,g.inputs.length≤2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    PEqualNP.Represents.Represents P C) ∧
    (depthsOf (n+m) C.gates).getD C.output 0≤1 ∧ C.gates.countP nlGate≤t := by
  have same : Anchor P u v=anchor u v (fun i j => b2z (P i j)) := by
    ext;unfold Anchor anchor;simp only [bit_eq];abel
  rw [same]
  exact main n m P u v t

def Rects (e : Nat) (D : Sq r) := ∃ X Y : Fin e → Finset (Fin r), ∀ a b,
  D a b=bit (decide ((Finset.univ.filter (fun j : Fin e => a ∈ X j ∧ b ∈ Y j)).card % 2=1))

theorem parity (s : Finset α) (p : α → Prop) [DecidablePred p] :
    bit (decide ((s.filter p).card % 2=1)) = ∑ k∈s, (if p k then 1 else 0 : F) := by
  rw [Finset.sum_boole]
  generalize (s.filter p).card=l
  have e : (l : F)=(l % 2 : Nat) := (ZMod.natCast_mod l 2).symm
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one l with h|h <;> simp [h,bit]

theorem rect_iff (D : Sq r) : Rects e D ↔ D.rank≤e := by
  classical
  constructor
  · rintro ⟨X,Y,eq⟩
    let U : Mat r e := fun a j => if a∈X j then 1 else 0
    let V : Mat e r := fun j b => if b∈Y j then 1 else 0
    have f : D=U*V := by
      ext a b;rw [eq,parity,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _;by_cases h : a∈X j <;> by_cases h' : b∈Y j <;> simp [U,V,h,h']
    rw [f];exact rank_of_factor _ _
  · intro h
    obtain ⟨U,V,eq⟩ := factor D h
    refine ⟨fun j => Finset.univ.filter (fun a => U a j=1),
            fun j => Finset.univ.filter (fun b => V j b=1),?_⟩
    intro a b
    rw [←eq,Matrix.mul_apply,parity]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    generalize U a j=x;generalize V j b=y;revert x y;decide
end MatrixBounds

section PanelEncoding
open Matrix

abbrev Idx (k : Nat) := Fin (k+2)
abbrev Panel (k r n : Nat) := Idx k × Fin r ↪ Fin n

def block (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (P : Fin n → Fin m → Bool) (i j : Idx k) : Sq r :=
  fun a b => Anchor P u v (rows (i,a)) (cols (j,b))

def errs (rows : Panel k r n) (cols : Panel k r m)
    (P T : Fin n → Fin m → Bool) (e : Nat) :=
  ∃ X Y : Fin e → Finset (Fin r), ∀ a b,
    xor (P (rows (Fin.last (k+1),a)) (cols (0,b))) (T (rows (Fin.last (k+1),a)) (cols (0,b))) =
      decide ((Finset.univ.filter (fun j : Fin e => a∈X j ∧ b∈Y j)).card % 2=1)

theorem errRank (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (P T : Fin n → Fin m → Bool) (col : ∀ a,P a v=T a v) (row : ∀ b,P u b=T u b) :
    errs rows cols P T e ↔ (block rows cols u v P (Fin.last _) 0-block rows cols u v T (Fin.last _) 0).rank≤e := by
  rw [←rect_iff]
  have bitInj : Function.Injective bit := by intro a b h;apply b2z_inj;simpa only [←bit_eq] using h
  have delta (a b) : (block rows cols u v P (Fin.last _) 0-block rows cols u v T (Fin.last _) 0) a b =
      bit (xor (P (rows (Fin.last _,a)) (cols (0,b))) (T (rows (Fin.last _,a)) (cols (0,b)))) := by
    simp only [Matrix.sub_apply,block,Anchor,col,row,xor_bit]
    abel
  constructor
  · rintro ⟨X,Y,h⟩;exact ⟨X,Y,fun a b => (delta a b).trans (congrArg bit (h a b))⟩
  · rintro ⟨X,Y,h⟩;exact ⟨X,Y,fun a b => bitInj ((delta a b).symm.trans (h a b))⟩

theorem extendPanel (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (ru : ∀ z,rows z≠u) (cv : ∀ z,cols z≠v) (T : Fin n → Fin m → Bool)
    (U : Idx k → Mat r w) (V : Idx k → Mat w r) :
    ∃ P, (∀ a,P a v=T a v) ∧ (∀ b,P u b=T u b) ∧
      (Anchor P u v).rank≤w ∧ ∀ i j,block rows cols u v P i j=U i*V j := by
  classical
  let A : Mat n w := Function.extend rows (fun z => U z.1 z.2) (fun _ => 0)
  let ys := Function.extend cols (fun z h => V z.1 h z.2) (fun _ _ => (0:F))
  let B : Mat w m := fun h b => ys b h
  have au : A u=0 := Function.extend_apply' _ _ _ (by simpa using ru)
  have bv (i) : B i v=0 := by
    have h : ys v=fun _ => 0 := Function.extend_apply' _ _ _ (by simpa using cv)
    exact congrFun h i
  let M := A*B
  have mu (j) : M u j=0 := by simp [M,Matrix.mul_apply,au]
  have mv (i) : M i v=0 := by simp [M,Matrix.mul_apply,bv]
  let P := fun a b => decide (M a b+bit (T a v)+bit (T u b)+bit (T u v)=1)
  have col (a) : P a v=T a v := by
    simp only [P,mv,zero_add,add_assoc,two,add_zero]
    cases T a v <;> decide
  have row (b) : P u b=T u b := by
    simp only [P,mu,zero_add,add_right_comm (bit (T u v)),two,zero_add]
    cases T u b <;> decide
  have eq : Anchor P u v=M := by
    ext a b
    simp only [Anchor,row,col,P,bit_dec]
    generalize bit (T u v)=x;generalize bit (T a v)=y;generalize bit (T u b)=z
    have := two x;have := two y;have := two z;linear_combination ‹x+x=0›+‹y+y=0›+‹z+z=0›
  refine ⟨P,col,row,eq ▸ rank_of_factor A B,?_⟩
  intro i j;ext a b
  change Anchor P u v _ _=_
  rw [eq]
  change (A*B) (rows (i,a)) (cols (j,b))=(U i*V j) a b
  rw [Matrix.mul_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro h _
  simp only [A,B,ys,rows.injective.extend_apply,cols.injective.extend_apply]

def PanelRank (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (T : Fin n → Fin m → Bool) (w e : Nat) :=
  ∃ P, (Anchor P u v).rank≤w ∧ (∀ a,P a v=T a v) ∧ (∀ b,P u b=T u b) ∧
    (∀ i,block rows cols u v P i i=block rows cols u v T i i) ∧
    (∀ j : Fin (k+1),block rows cols u v P j.castSucc j.succ=block rows cols u v T j.castSucc j.succ) ∧
    errs rows cols P T e

/-- Restrict the anchored matrix to the panels, or extend panel factors by zero at unused labels. -/
theorem panel_iff (rows : Panel k r n) (cols : Panel k r m) (u : Fin n) (v : Fin m)
    (ru : ∀ z,rows z≠u) (cv : ∀ z,cols z≠v) (T : Fin n → Fin m → Bool)
    (L R : Idx k → Sq r) (H : Sq r) (units : ∀ i,IsUnit (L i) ∧ IsUnit (R i))
    (diag : ∀ i,block rows cols u v T i i=L i*R i)
    (next : ∀ j : Fin (k+1),block rows cols u v T j.castSucc j.succ=L j.castSucc*R j.succ)
    (last : block rows cols u v T (Fin.last _) 0=L (Fin.last _)*H*R 0) :
    PanelRank rows cols u v T w e ↔ ∃ S : Sq r, Frames k r w S ∧ (S-H).rank≤e := by
  classical
  let l := Fin.last (k+1)
  have lu (i) := (L i).isUnit_iff_isUnit_det.mp (units i).1
  have rv (i) := (R i).isUnit_iff_isUnit_det.mp (units i).2
  have sameRank (D : Sq r) : (L l*D*R 0).rank=D.rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (rv 0), Matrix.rank_mul_eq_right_of_isUnit_det _ _ (lu l)]
  constructor
  · rintro ⟨P,pr,pc,pq,pd,pn,pe⟩
    obtain ⟨U,V,fac⟩ := factor _ pr
    let X : Idx k → Mat r w := fun i a h => U (rows (i,a)) h
    let Y : Idx k → Mat w r := fun i h b => V h (cols (i,b))
    have eq (i j) : X i*Y j=block rows cols u v P i j := by
      ext a b;exact congrFun (congrFun fac (rows (i,a))) (cols (j,b))
    let A : Idx k → Mat r w := fun i => (L i)⁻¹*X i
    let B : Idx k → Mat w r := fun j => Y j*(R j)⁻¹
    have scale (i j) : A i*B j=(L i)⁻¹*(block rows cols u v P i j)*(R j)⁻¹ := by
      rw [←eq];simp only [A,B,Matrix.mul_assoc]
    have norm (i j) (h : block rows cols u v P i j=L i*R j) : A i*B j=1 := by
      rw [scale,h,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (lu i),one_mul,Matrix.mul_nonsing_inv _ (rv j)]
    refine ⟨A l*B 0,⟨A,B,fun i => norm i i ((pd i).trans (diag i)),
      fun j => norm _ _ ((pn j).trans (next j)),rfl⟩,?_⟩
    have close := (errRank rows cols u v P T pc pq).mp pe
    have cancel : L l*(A l*B 0)*R 0=block rows cols u v P l 0 := by
      rw [scale];simp only [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ (rv 0),mul_one]
      rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (lu l),one_mul]
    rw [←sameRank, Matrix.mul_sub,Matrix.sub_mul,cancel,←last];exact close
  · rintro ⟨S,⟨A,B,ad,an,al⟩,err⟩
    obtain ⟨P,pc,pq,pr,h⟩ := extendPanel rows cols u v ru cv T (fun i => L i*A i) (fun j => B j*R j)
    have eq (i j) : block rows cols u v P i j=L i*(A i*B j)*R j := by rw [h];simp [Matrix.mul_assoc]
    refine ⟨P,pr,pc,pq,fun i => by rw [eq,ad,mul_one,diag],fun j => by rw [eq,an,mul_one,next],?_⟩
    apply (errRank rows cols u v P T pc pq).mpr
    rw [eq,al,last,←Matrix.sub_mul,←Matrix.mul_sub]
    exact (sameRank _).le.trans err
end PanelEncoding

section RankRepair
open LinearMap Submodule Module Matrix
abbrev Vect (r : Nat) := Fin r → F
abbrev Endo (r : Nat) := Vect r →ₗ[F] Vect r

private theorem outsideBoth (U W : Submodule F (Vect r)) (u : U≠⊤) (w : W≠⊤) :
    ∃ x, x∉U ∧ x∉W := by
  obtain ⟨a,_,ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr u)
  obtain ⟨b,_,hb⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr w)
  by_cases aw : a∈W
  · by_cases bu : b∈U
    · exact ⟨a+b,fun h => ha ((U.add_mem_iff_left bu).mp h),fun h => hb ((W.add_mem_iff_right aw).mp h)⟩
    · exact ⟨b,bu,hb⟩
  · exact ⟨a,ha,aw⟩

private theorem nzOne {x : F} : x≠0 → x=1 := by revert x;decide

/-- Fix one more vector by changing the map on a complement to a hyperplane.
The complement vector lies outside the image of the hyperplane, preserving or raising rank. -/
theorem repair_map (f : Endo r) (bad : f≠LinearMap.id) :
    ∃ (g : Endo r) (φ : Vect r →ₗ[F] F) (v : Vect r),
      g=f+φ.smulRight v ∧
      finrank F (range (LinearMap.id-g)) < finrank F (range (LinearMap.id-f)) ∧
      min r (finrank F (range f)+1) ≤ finrank F (range g) := by
  classical
  let K := ker (LinearMap.id-f)
  have km (y) : y∈K ↔ f y=y := by
    change y-f y=0 ↔ f y=y
    rw [sub_eq_zero];exact eq_comm
  have kp : K≠⊤ := by
    intro h
    apply bad;apply LinearMap.ext;intro y
    exact (km y).mp (h ▸ Submodule.mem_top)
  let sing := ¬ Function.Injective f
  obtain ⟨h, hk, hz⟩ : ∃ h, h∉K ∧ (sing → f h=0) := by
    by_cases s : Function.Injective f
    · obtain ⟨h,_,hn⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr kp)
      exact ⟨h,hn,fun hs => False.elim (hs s)⟩
    · have nz : ker f ≠ ⊥ := fun e => s (ker_eq_bot.mp e)
      obtain ⟨h,hin,hn⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr nz)
      have h0 : h≠0 := fun e => hn (by simp [e])
      have z : f h=0 := hin
      exact ⟨h,fun hf => h0 (((km h).mp hf).symm.trans z),fun _ => z⟩
  obtain ⟨φ,nonzero,ann⟩ := Submodule.exists_le_ker_of_notMem hk
  have ph := nzOne nonzero
  let W := ker φ
  have wp : W≠⊤ := by intro eq;exact nonzero (show h∈W from eq ▸ Submodule.mem_top)
  have wm : W.map f≠⊤ := by
    intro eq
    have a := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr wp)
    have b := Submodule.finrank_map_le f W
    rw [eq] at b
    omega
  obtain ⟨x,xw,xf⟩ := outsideBoth W (W.map f) wp wm
  have px : φ x=1 := nzOne xw
  let v := x-f x
  let g := f+φ.smulRight v
  have val (y) : g y=f y+φ y • v := rfl
  have fixx : g x=x := by rw [val,px,one_smul];dsimp [v];abel
  have fixed : K < ker (LinearMap.id-g) := by
    apply lt_of_le_of_ne
    · intro y hy
      have py : φ y=0 := ann hy
      simp [LinearMap.mem_ker,val,py,(km y).mp hy]
    · intro eq;apply xw;apply ann
      rw [eq]
      simp [LinearMap.mem_ker,fixx]
  refine ⟨g,φ,v,rfl,?_,?_⟩
  · have a := Submodule.finrank_lt_finrank_of_lt fixed
    have b := (LinearMap.id-f).finrank_range_add_finrank_ker
    have c := (LinearMap.id-g).finrank_range_add_finrank_ker
    change finrank F (ker (LinearMap.id-f)) < _ at a
    omega
  · by_cases s : Function.Injective f
    · have inj : Function.Injective g := by
        apply LinearMap.ker_eq_bot.mp
        apply le_antisymm _ bot_le
        intro y hy
        change y=0
        have gy : g y=0 := hy
        by_cases p : φ y=0
        · apply s;simpa [val,p] using gy
        · have py := nzOne p
          exfalso
          apply xf
          refine ⟨x-y,?_,?_⟩
          · simp [W,mem_ker,px,py]
          · rw [val,py,one_smul] at gy
            dsimp [v] at gy
            rw [map_sub];abel_nf at gy ⊢ <;> linear_combination (norm := abel) -gy
      have sur := (LinearMap.injective_iff_surjective (f:=g)).mp inj
      rw [range_eq_top.mpr sur,finrank_top,finrank_fin_fun]
      exact min_le_left _ _
    · have fh := hz s
      have incl : range f≤range g := by
        rintro _ ⟨y,rfl⟩
        refine ⟨y-φ y • h,?_⟩
        simp [val,map_sub,map_smul,ph,fh]
      have strict : range f<range g := by
        apply lt_of_le_of_ne incl
        intro eq
        have gh : g h=v := by simp [val,fh,ph]
        have vv : v∈range f := eq ▸ ⟨h,gh⟩
        have xx : x∈range f := by
          convert (range f).add_mem vv (show f x∈range f from ⟨x,rfl⟩) using 1
          dsimp [v];abel
        obtain ⟨y,ey⟩ := xx
        apply xf
        exact ⟨y-φ y • h,by simp [W,mem_ker,ph],by simp [fh,ey]⟩
      have hd := Submodule.finrank_lt_finrank_of_lt strict
      omega
end RankRepair

section PanelWalk
open Matrix LinearMap Module Function

theorem repair_one (A : Sq r) : ∃ B : Sq r, (B-A).rank≤1 ∧
    (1-B).rank≤(1-A).rank-1 ∧ min r (A.rank+1)≤B.rank := by
  classical
  by_cases eq : A=1
  · subst A;refine ⟨1,by simp,by simp,by simp⟩
  let f : Endo r := Matrix.toLin' A
  have ne : f≠LinearMap.id := by
    intro h;apply eq;simpa [f] using congrArg LinearMap.toMatrix' h
  obtain ⟨g,φ,v,gv,drop,grow⟩ := repair_map f ne
  let B : Sq r := LinearMap.toMatrix' g
  have bg : Matrix.toLin' B=g := Matrix.toLin'_toMatrix' g
  have rank_map (M : Sq r) : M.rank=finrank F (LinearMap.range (Matrix.toLin' M)) := rfl
  have db : (1-B).rank=finrank F (LinearMap.range (LinearMap.id-g)) := by rw [rank_map,map_sub,Matrix.toLin'_one,bg]
  have da : (1-A).rank=finrank F (LinearMap.range (LinearMap.id-f)) := by rw [rank_map,map_sub,Matrix.toLin'_one]
  have rb : B.rank=finrank F (LinearMap.range g) := by rw [rank_map,bg]
  have d : B-A=Matrix.vecMulVec v (fun j => φ (Pi.single j 1)) := by
    ext i j
    have h := congrArg (fun (T : Endo r) => T (Pi.single j 1) i) gv
    simp [f,Matrix.mulVec_single_one,LinearMap.smulRight_apply,Pi.smul_apply,smul_eq_mul] at h
    simp only [B,Matrix.sub_apply,LinearMap.toMatrix'_apply,Matrix.vecMulVec_apply]
    rw [h];ring
  exact ⟨B,d ▸ rank_vecMulVec_le _ _,by rw [db,da];omega,by rw [rb];exact grow⟩

noncomputable def repair (A : Sq r) : Sq r := Classical.choose (repair_one A)

theorem after (A : Sq r) (n : Nat) :
    ((repair^[n]) A-A).rank≤n ∧ (1-(repair^[n]) A).rank≤(1-A).rank-n ∧
    min r (A.rank+n)≤((repair^[n]) A).rank := by
  induction n with
  | zero => simp
  | succ n ih =>
    let X := (repair^[n]) A
    have h := Classical.choose_spec (repair_one X)
    change (repair X-X).rank≤1 ∧ (1-repair X).rank≤(1-X).rank-1 ∧ min r (X.rank+1)≤(repair X).rank at h
    rw [Function.iterate_succ_apply']
    have d := dist (repair X) X A
    change (X-A).rank≤n ∧ (1-X).rank≤_ ∧ _≤X.rank at ih
    change (repair X-A).rank≤_ ∧ (1-repair X).rank≤_ ∧ _≤(repair X).rank
    omega

/-- Read the repairs in reverse, grouping the steps into jumps of rank at most d. -/
theorem path_data (H : Sq r) (k d e : Nat) (full : r≤H.rank+d+e) (cost : (1-H).rank≤(k+1)*d+e) :
    ∃ S : Fin (k+2) → Sq r, S 0=1 ∧ ((S (Fin.last _))-H).rank≤e ∧
    ∀ j : Fin (k+1), IsUnit (S j.castSucc) ∧ (S j.castSucc-S j.succ).rank≤d := by
  let time := fun (i : Fin (k+2)) => (k+1-i.val)*d+e
  let S := fun i => (repair^[time i]) H
  have tz : time 0=(k+1)*d+e := by simp [time]
  have tl : time (Fin.last _) =e := by simp [time]
  have z := (after H (time 0)).2.1
  have rz : (1-S 0).rank=0 := by dsimp [S];rw [tz] at z ⊢;omega
  have zeroMat {M : Sq r} (h : M.rank=0) : M=0 := by
    have hh : finrank F (range (Matrix.toLin' M))=0 := h
    have hb : range (Matrix.toLin' M)=⊥ := Submodule.finrank_eq_zero.mp hh
    have h0 := LinearMap.range_eq_bot.mp hb
    simpa using congrArg LinearMap.toMatrix' h0
  refine ⟨S,(sub_eq_zero.mp (zeroMat rz)).symm,?_,?_⟩
  · simpa only [S,tl] using (after H e).1
  · intro j
    have ht : time j.castSucc=d+time j.succ := by
      have := j.isLt
      have ar : k+1-j.val=(k+1-(j.val+1))+1 := by omega
      simp [time,Fin.val_castSucc,Fin.val_succ,ar,Nat.add_mul];omega
    have hd : e≤time j.succ := by simp [time]
    have gr := (after H (time j.castSucc)).2.2
    have hi : (S j.castSucc).rank=r := by
      have up := rank_le_width (S j.castSucc)
      change min r (H.rank+time j.castSucc)≤(S j.castSucc).rank at gr
      omega
    refine ⟨Matrix.mulVec_surjective_iff_isUnit.mp (Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hi)),?_⟩
    change ((repair^[time j.castSucc]) H-(repair^[time j.succ]) H).rank≤d
    rw [ht,Function.iterate_add_apply];exact (after _ d).1
end PanelWalk

section PanelConstruction
open Matrix
/-- Lift a rank-bounded jump by factoring the difference through the auxiliary coordinates. -/
theorem frame_step {S D : Sq r} (hS : IsUnit S) (jump : (S-D).rank≤d)
    (U : Mat r d) : ∃ U' : Mat r d, ∃ X : Sq r, ∃ Y : Mat d r,
      S*X + U*Y=1 ∧ D*X + U'*Y=1 := by
  obtain ⟨J,V,h⟩ := factor _ jump
  let F := S⁻¹
  have sf : S*F=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  let G := F*U
  have sg : S*G=U := by rw [show S*G=(S*F)*U by exact (Matrix.mul_assoc ..).symm,sf,Matrix.one_mul]
  let Y := V*F
  refine ⟨D*G+J,F-G*Y,Y,?_,?_⟩
  · rw [Matrix.mul_sub,←Matrix.mul_assoc,sg,sf];abel
  · rw [Matrix.mul_sub,Matrix.add_mul,←Matrix.mul_assoc D G Y]
    have sum : D*F+J*Y=1 := by
      change D*F+J*(V*F)=1
      rw [←Matrix.mul_assoc,←Matrix.add_mul,h]
      have hs : D+(S-D)=S := by abel
      rw [hs,sf]
    rw [←sum];abel

theorem build_frames (S : Fin (k+2) → Sq r) (start : S 0=1)
    (step : ∀ j : Fin (k+1),IsUnit (S j.castSucc) ∧ (S j.castSucc-S j.succ).rank≤d) :
    Frames k r (r+d) (S (Fin.last _)) := by
  classical
  have opts (j : Fin (k+1)) (u : Mat r d) := frame_step (step j).1 (step j).2 u
  let U : Fin (k+2) → Mat r d := Fin.induction 0 (fun j u => Classical.choose (opts j u))
  let x := fun j => Classical.choose (Classical.choose_spec (opts j (U j.castSucc)))
  let y := fun j => Classical.choose (Classical.choose_spec (Classical.choose_spec (opts j (U j.castSucc))))
  let X : Fin (k+2) → Sq r := Fin.cases 1 x
  let Y : Fin (k+2) → Mat d r := Fin.cases 0 y
  have formulas (j : Fin (k+1)) : S j.castSucc * X j.succ + U j.castSucc * Y j.succ=1 ∧
      S j.succ * X j.succ + U j.succ * Y j.succ=1 := by
    simpa only [X,Y,Fin.cases_succ,U,Fin.induction_succ,x,y] using
      Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (opts j (U j.castSucc))))
  let equiv : Fin (r+d) ≃ (Fin r ⊕ Fin d) := finSumFinEquiv.symm
  let A := fun i => (Matrix.fromCols (S i) (U i)).submatrix id equiv
  let B := fun j => (Matrix.fromRows (X j) (Y j)).submatrix equiv id
  have mul (i j) : A i*B j=S i*X j+U i*Y j := by
    simp only [A,B,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id,Matrix.fromCols_mul_fromRows]
  refine ⟨A,B,?_,fun j => (mul _ _).trans (formulas j).1,?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simp [mul,X,Y,start]
    | succ j => exact (mul _ _).trans (formulas j).2
  · simp [mul,X,Y]

theorem rank_budget (H : Sq r) (w e k : Nat) :
    (∃ S : Sq r,Frames k r w S ∧ (S-H).rank≤e) ↔
    r≤w ∧ r≤H.rank+(w-r)+e ∧ (1-H).rank≤(k+1)*(w-r)+e := by
  constructor
  · rintro ⟨S,f,err⟩
    obtain ⟨rw,h,d⟩ := necessary f
    have sh := addRank (S-H) H
    rw [sub_add_cancel] at sh
    have one := dist 1 S H
    exact ⟨rw,by omega,by omega⟩
  · rintro ⟨rw,h,d⟩
    obtain ⟨S,start,err,steps⟩ := path_data H k (w-r) e h d
    exact ⟨_,Nat.add_sub_of_le rw ▸ build_frames S start steps,err⟩
end PanelConstruction

end PEqualNP.Outside.L_meta_33623_aux

open PEqualNP.Outside.L_meta_33623_aux

theorem PEqualNP.Outside.L_meta_33623 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m k r t e : ℕ) (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let I := Fin (k+2)
  let M := Matrix (Fin r) (Fin r) (ZMod 2)
  let last : I := Fin.last (k+1)
  ∀ (rows : I × Fin r ↪ Fin n) (cols : I × Fin r ↪ Fin m)
    (_ : ∀ z, rows z ≠ u) (_ : ∀ z, cols z ≠ v) (L R : I → M) (H : M),
    let block := fun (P : Fin n → Fin m → Bool) (i j : I) =>
      (fun a b => ((P (rows (i,a)) (cols (j,b))).toNat : ZMod 2) +
        ((P u (cols (j,b))).toNat : ZMod 2) + ((P (rows (i,a)) v).toNat : ZMod 2) +
        ((P u v).toNat : ZMod 2) : M)
    (∀ i, IsUnit (L i) ∧ IsUnit (R i)) →
    (∀ i, block T i i = L i * R i) →
    (∀ j : Fin (k+1), block T j.castSucc j.succ = L j.castSucc * R j.succ) →
    block T last 0 = L last * H * R 0 →
    ((∃ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q ∧
      PEqualNP.Represents.Represents P Q ∧ depth (n+m) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
      (∀ i, P i v = T i v) ∧ (∀ j, P u j = T u j) ∧
      (∀ i, block P i i = block T i i) ∧
      (∀ j : Fin (k+1), block P j.castSucc j.succ = block T j.castSucc j.succ) ∧
      ∃ X Y : Fin e → Finset (Fin r), ∀ a b : Fin r,
        xor (P (rows (last,a)) (cols (0,b))) (T (rows (last,a)) (cols (0,b))) =
          decide ((Finset.univ.filter (fun j : Fin e => a ∈ X j ∧ b ∈ Y j)).card % 2 = 1)) ↔
    r ≤ 2*t ∧ r ≤ Matrix.rank H + (2*t-r) + e ∧ Matrix.rank (1-H) ≤ (k+1)*(2*t-r)+e)
) := by
  intro nonlinear depth n m k r t e T u v I M last rows cols ru cv L R H blockT units diag next close
  rw [←rank_budget H (2*t) e k, ←panel_iff rows cols u v ru cv T L R H units diag next close]
  constructor
  · rintro ⟨P,C,fan,back,rep,dep,count,col,row,pd,pn,err⟩
    exact ⟨P,(criterion P u v t).mpr ⟨C,⟨fan,back,rep⟩,dep,count⟩,col,row,pd,pn,err⟩
  · rintro ⟨P,rank,col,row,pd,pn,err⟩
    obtain ⟨C,⟨fan,back,rep⟩,dep,count⟩ := (criterion P u v t).mp rank
    exact ⟨P,C,fan,back,rep,dep,count,col,row,pd,pn,err⟩
