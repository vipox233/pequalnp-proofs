import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projection
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33633_aux

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

section GeodesicPath

private lemma exists_func_vanish_one {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S : Submodule K E) (x : E) (hx : x ∉ S) :
    ∃ f : E →ₗ[K] K, (∀ u ∈ S, f u = 0) ∧ f x = 1 := by
  let qx : E ⧸ S := Submodule.mkQ S x
  have hqx_ne : qx ≠ 0 := by
    intro h0
    exact hx ((Submodule.Quotient.mk_eq_zero S).mp h0)
  let L : Submodule K (E ⧸ S) := Submodule.span K ({qx} : Set (E ⧸ S))
  obtain ⟨C, hLC⟩ := Submodule.exists_isCompl L
  let proj : (E ⧸ S) →ₗ[K] L := Submodule.projectionOnto L C hLC
  let inc : L →ₗ[K] LinearMap.range (LinearMap.toSpanSingleton K (E ⧸ S) qx) :=
    { toFun := fun y => ⟨y.1, by
        have hy := y.2
        rw [Submodule.mem_span_singleton] at hy
        rcases hy with ⟨c, hc⟩
        exact ⟨c, hc⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let coord : L →ₗ[K] K :=
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton K (E ⧸ S) qx |>.rangeRestrict)
      ⟨fun a b hab => by
        have hv : a • qx = b • qx := congrArg Subtype.val hab
        have hsub : (a - b) • qx = 0 := by rw [sub_smul, hv, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | h0
        · exact sub_eq_zero.mp h0
        · exact absurd h0 hqx_ne,
       fun ⟨y, hy⟩ => by
        rw [LinearMap.mem_range] at hy
        rcases hy with ⟨c, rfl⟩
        exact ⟨c, rfl⟩⟩).symm.toLinearMap.comp inc
  refine ⟨coord.comp (proj.comp (Submodule.mkQ S)), ?_, ?_⟩
  · intro u hu
    change coord (proj (Submodule.mkQ S u)) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).mpr hu, map_zero, map_zero]
  · simp only [LinearMap.comp_apply]
    have hqxL : qx ∈ L := Submodule.subset_span (Set.mem_singleton qx)
    have hpr : proj qx = ⟨qx, hqxL⟩ := Submodule.projectionOnto_apply_left hLC ⟨qx, hqxL⟩
    change coord (proj qx) = 1
    rw [hpr]
    dsimp only [coord, inc, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    apply (LinearEquiv.symm_apply_eq _).mpr
    apply Subtype.ext
    change qx = (1 : K) • qx
    rw [one_smul]

private lemma exists_func_vanish_two {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S : Submodule K E) (x y : E) (hx : x ∉ S) (hy : y ∉ S) :
    ∃ f : E →ₗ[K] K, (∀ u ∈ S, f u = 0) ∧ f x = 1 ∧ f y ≠ 0 := by
  obtain ⟨f1, hf1S, hf1x⟩ := exists_func_vanish_one S x hx
  by_cases hf1y : f1 y ≠ 0
  · exact ⟨f1, hf1S, hf1x, hf1y⟩
  · push Not at hf1y
    have hy_not : y ∉ S ⊔ Submodule.span K ({x} : Set E) := by
      intro hmem
      rcases Submodule.mem_sup.mp hmem with ⟨u, hu, w, hw, rfl⟩
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rw [map_add, map_smul, hf1S u hu, zero_add, hf1x, smul_eq_mul, mul_one] at hf1y
      rw [hf1y, zero_smul, add_zero] at hy
      exact hy hu
    obtain ⟨f2, hf2, hf2y⟩ := exists_func_vanish_one (S ⊔ Submodule.span K ({x} : Set E)) y hy_not
    refine ⟨f1 + f2, ?_, ?_, ?_⟩
    · intro u hu
      simp only [LinearMap.add_apply, hf1S u hu, hf2 u (Submodule.mem_sup_left hu), add_zero]
    · simp only [LinearMap.add_apply, hf1x,
        hf2 x (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))), add_zero]
    · simp only [LinearMap.add_apply, hf1y, zero_add, hf2y, ne_eq, one_ne_zero, not_false_eq_true]

private lemma exists_not_mem_two {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (S1 S2 : Submodule K E) (h1 : S1 ≠ ⊤) (h2 : S2 ≠ ⊤) :
    ∃ x : E, x ∉ S1 ∧ x ∉ S2 := by
  have hex1 : ∃ x1 : E, x1 ∉ S1 := by
    by_contra hall; push Not at hall
    exact h1 (Submodule.eq_top_iff'.mpr hall)
  have hex2 : ∃ x2 : E, x2 ∉ S2 := by
    by_contra hall; push Not at hall
    exact h2 (Submodule.eq_top_iff'.mpr hall)
  rcases hex1 with ⟨x1, hx1⟩
  rcases hex2 with ⟨x2, hx2⟩
  by_cases hx1_2 : x1 ∉ S2
  · exact ⟨x1, hx1, hx1_2⟩
  · push Not at hx1_2
    by_cases hx2_1 : x2 ∉ S1
    · exact ⟨x2, hx2_1, hx2⟩
    · push Not at hx2_1
      refine ⟨x1 + x2, ?_, ?_⟩
      · intro h; exact hx1 (by simpa using Submodule.sub_mem S1 h hx2_1)
      · intro h; exact hx2 (by simpa using Submodule.sub_mem S2 h hx1_2)

private lemma mulVecLin_add_geo {K : Type*} [Field K] {q r : ℕ}
    (A B : Matrix (Fin q) (Fin r) K) :
    (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by
  apply LinearMap.ext; intro v; funext i
  change (∑ j : Fin r, (A i j + B i j) * v j) =
    (∑ j : Fin r, A i j * v j) + ∑ j : Fin r, B i j * v j
  simp only [add_mul, Finset.sum_add_distrib]

private lemma mulVecLin_sub_geo {K : Type*} [Field K] {q r : ℕ}
    (A B : Matrix (Fin q) (Fin r) K) :
    (A - B).mulVecLin = A.mulVecLin - B.mulVecLin := by
  apply LinearMap.ext; intro v; funext i
  change (∑ j : Fin r, (A i j - B i j) * v j) =
    (∑ j : Fin r, A i j * v j) - ∑ j : Fin r, B i j * v j
  simp only [sub_mul, Finset.sum_sub_distrib]

private lemma rank_add_le_geo {K : Type*} [Field K] {q r : ℕ}
    (A B : Matrix (Fin q) (Fin r) K) :
    Matrix.rank (A + B) ≤ Matrix.rank A + Matrix.rank B := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    rw [mulVecLin_add_geo, LinearMap.add_apply]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have h1 := Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) + Module.finrank K (LinearMap.range B.mulVecLin)
  omega

theorem rank_elim_eq_finrank_sup {K : Type*} [Field K] {q r : ℕ}
    (A J : Matrix (Fin q) (Fin r) K) :
    Matrix.rank (fun i z => Sum.elim (A i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) =
      Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range J.mulVecLin) := by
  let M : Matrix (Fin q) (Fin r ⊕ Fin r) K := fun i z => Sum.elim (A i) (J i) z
  change Module.finrank K (LinearMap.range M.mulVecLin) = _
  have hrange : LinearMap.range M.mulVecLin = LinearMap.range A.mulVecLin ⊔ LinearMap.range J.mulVecLin := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      have hsplit : M.mulVecLin w =
          A.mulVecLin (fun j => w (Sum.inl j)) + J.mulVecLin (fun j => w (Sum.inr j)) := by
        funext i
        change (∑ z : Fin r ⊕ Fin r, M i z * w z) =
          (∑ j : Fin r, A i j * w (Sum.inl j)) + ∑ j : Fin r, J i j * w (Sum.inr j)
        rw [Fintype.sum_sum_type]
        rfl
      rw [hsplit]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    · intro hy
      rcases Submodule.mem_sup.mp hy with ⟨_, ⟨x1, rfl⟩, _, ⟨x2, rfl⟩, rfl⟩
      refine ⟨Sum.elim x1 x2, ?_⟩
      funext i
      change (∑ z : Fin r ⊕ Fin r, M i z * Sum.elim x1 x2 z) =
        (∑ j : Fin r, A i j * x1 j) + ∑ j : Fin r, J i j * x2 j
      rw [Fintype.sum_sum_type]
      rfl
  rw [hrange]

private lemma rank_one_matrix {K : Type*} [Field K] {q r : ℕ}
    (u : Fin q → K) (f : (Fin r → K) →ₗ[K] K) :
    let B : Matrix (Fin q) (Fin r) K := fun i j => u i * f (Pi.single j 1)
    B.mulVecLin = (LinearMap.toSpanSingleton K (Fin q → K) u).comp f := by
  intro B
  apply LinearMap.ext; intro v; funext i
  change (∑ j : Fin r, u i * f (Pi.single j 1) * v j) = f v * u i
  have hfv : f v = ∑ j : Fin r, v j * f (Pi.single j 1) := by
    have hv : v = ∑ j : Fin r, v j • Pi.single j (1 : K) := by
      funext j0
      rw [Finset.sum_apply, Finset.sum_eq_single j0]
      · simp
      · intro j _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
      · intro hnu; exact absurd (Finset.mem_univ _) hnu
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
  rw [hfv, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => by ring)

private lemma rank_update_dist {K : Type*} [Field K] {q r : ℕ}
    (A J : Matrix (Fin q) (Fin r) K)
    (x : Fin r → K) (f : (Fin r → K) →ₗ[K] K)
    (hfF : ∀ u ∈ LinearMap.ker (A.mulVecLin - J.mulVecLin), f u = 0)
    (hfx : f x = 1) :
    let w : Fin q → K := J.mulVecLin x - A.mulVecLin x
    let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
    let A' : Matrix (Fin q) (Fin r) K := A + B
    Matrix.rank (A - A') = 1 ∧ Matrix.rank (A' - J) = Matrix.rank (A - J) - 1 := by
  dsimp only
  let w : Fin q → K := J.mulVecLin x - A.mulVecLin x
  let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
  let A' : Matrix (Fin q) (Fin r) K := A + B
  have hx_notF : x ∉ LinearMap.ker (A.mulVecLin - J.mulVecLin) := by
    intro hxF
    have h0 := hfF x hxF
    rw [hfx] at h0
    exact one_ne_zero h0
  have hw_ne : w ≠ 0 := by
    intro h0
    apply hx_notF
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (sub_eq_zero.mp h0).symm
  have hB_lin : B.mulVecLin = (LinearMap.toSpanSingleton K (Fin q → K) w).comp f :=
    rank_one_matrix w f
  have hA'_lin : A'.mulVecLin = A.mulVecLin + B.mulVecLin := mulVecLin_add_geo A B
  have hrank1 : Matrix.rank (A - A') = 1 := by
    have hsub : A - A' = -B := by
      dsimp only [A']; abel
    rw [hsub]
    have hneg_lin : (-B).mulVecLin = -B.mulVecLin := by
      apply LinearMap.ext; intro v; funext i
      change (∑ j : Fin r, (-B i j) * v j) = -(∑ j : Fin r, B i j * v j)
      simp [Finset.sum_neg_distrib]
    change Module.finrank K (LinearMap.range (-B).mulVecLin) = 1
    rw [hneg_lin, LinearMap.range_neg, hB_lin]
    have hrange : LinearMap.range ((LinearMap.toSpanSingleton K (Fin q → K) w).comp f) =
        Submodule.span K ({w} : Set (Fin q → K)) := by
      ext y
      simp only [LinearMap.mem_range, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
        Submodule.mem_span_singleton]
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨f v, rfl⟩
      · rintro ⟨c, rfl⟩; exact ⟨c • x, by rw [map_smul, hfx, smul_eq_mul, mul_one]⟩
    rw [hrange, finrank_span_singleton hw_ne]
  have hrank_dec : Matrix.rank (A' - J) = Matrix.rank (A - J) - 1 := by
    have hker_lt : LinearMap.ker (A.mulVecLin - J.mulVecLin) <
        LinearMap.ker (A'.mulVecLin - J.mulVecLin) := by
      rw [lt_iff_le_and_ne]
      constructor
      · intro u hu
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hA'_lin, LinearMap.add_apply, hB_lin,
          LinearMap.comp_apply, hfF u hu, map_zero, add_zero]
        exact LinearMap.mem_ker.mp hu
      · intro heq
        have hx' : x ∈ LinearMap.ker (A'.mulVecLin - J.mulVecLin) := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, hA'_lin, LinearMap.add_apply, hB_lin,
            LinearMap.comp_apply, hfx, LinearMap.toSpanSingleton_apply, one_smul]
          dsimp only [w]
          abel
        exact hx_notF (heq.symm ▸ hx')
    have hker_dim : Module.finrank K (LinearMap.ker (A.mulVecLin - J.mulVecLin)) <
        Module.finrank K (LinearMap.ker (A'.mulVecLin - J.mulVecLin)) :=
      Submodule.finrank_lt_finrank_of_lt hker_lt
    have hrn1 := LinearMap.finrank_range_add_finrank_ker (A.mulVecLin - J.mulVecLin)
    have hrn2 := LinearMap.finrank_range_add_finrank_ker (A'.mulVecLin - J.mulVecLin)
    have hlin1 : (A - J).mulVecLin = A.mulVecLin - J.mulVecLin := mulVecLin_sub_geo A J
    have hlin2 : (A' - J).mulVecLin = A'.mulVecLin - J.mulVecLin := mulVecLin_sub_geo A' J
    have hle1 : Matrix.rank (A' - J) + 1 ≤ Matrix.rank (A - J) := by
      change Module.finrank K (LinearMap.range (A' - J).mulVecLin) + 1 ≤
        Module.finrank K (LinearMap.range (A - J).mulVecLin)
      rw [hlin1, hlin2]
      omega
    have hge1 : Matrix.rank (A - J) ≤ 1 + Matrix.rank (A' - J) := by
      have hsplit : A - J = (A - A') + (A' - J) := by abel
      calc Matrix.rank (A - J)
          = Matrix.rank ((A - A') + (A' - J)) := by rw [hsplit]
        _ ≤ Matrix.rank (A - A') + Matrix.rank (A' - J) := rank_add_le_geo _ _
        _ = 1 + Matrix.rank (A' - J) := by rw [hrank1]
    omega
  exact ⟨hrank1, hrank_dec⟩

private lemma exists_step {K : Type*} [Field K] {q r : ℕ}
    (A J : Matrix (Fin q) (Fin r) K) (hpos : 0 < Matrix.rank (A - J)) :
    let size := fun (M : Matrix (Fin q) (Fin r) K) =>
      Matrix.rank (fun i z => Sum.elim (M i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K)
    ∃ A' : Matrix (Fin q) (Fin r) K,
      Matrix.rank (A - A') = 1 ∧
      Matrix.rank (A' - J) = Matrix.rank (A - J) - 1 ∧
      size A' - Matrix.rank A' = size A - Matrix.rank A - 1 ∧
      size A' - Matrix.rank J = size A - Matrix.rank J - 1 := by
  dsimp only
  let LA := A.mulVecLin
  let LJ := J.mulVecLin
  let imA := LinearMap.range LA
  let imJ := LinearMap.range LJ
  let F := LinearMap.ker (LA - LJ)
  let Z := imA ⊓ imJ
  have hrankA_eq : Module.finrank K imA = Matrix.rank A := rfl
  have hmod : ∀ M : Matrix (Fin q) (Fin r) K,
      Module.finrank K ↥(LinearMap.range M.mulVecLin ⊔ imJ) +
        Module.finrank K ↥(LinearMap.range M.mulVecLin ⊓ imJ) =
      Matrix.rank M + Matrix.rank J := by
    intro M
    exact Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range M.mulVecLin) imJ
  have hF_ne_top : F ≠ ⊤ := by
    intro htop
    have hzero : Module.finrank K (LinearMap.range (A - J).mulVecLin) = 0 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (LA - LJ)
      rw [mulVecLin_sub_geo]
      change Module.finrank K (LinearMap.range (LA - LJ)) = 0
      rw [show LinearMap.ker (LA - LJ) = F from rfl, htop, finrank_top] at hrn
      omega
    exact absurd hzero (ne_of_gt hpos)
  by_cases hJle : imJ ≤ imA
  · by_cases hAle : imA ≤ imJ
    · have him_eq : imA = imJ := le_antisymm hAle hJle
      have hszA : Module.finrank K ↥(imA ⊔ imJ) = Matrix.rank A := by
        rw [him_eq, sup_idem, ← him_eq]; rfl
      have hszJ : Module.finrank K ↥(imA ⊔ imJ) = Matrix.rank J := by
        rw [him_eq, sup_idem]; rfl
      have hex_x : ∃ x : Fin r → K, x ∉ F := by
        by_contra hall; push Not at hall
        exact hF_ne_top (Submodule.eq_top_iff'.mpr hall)
      rcases hex_x with ⟨x, hxF⟩
      have hex_f : ∃ f : (Fin r → K) →ₗ[K] K, (∀ u ∈ F, f u = 0) ∧ f x = 1 ∧
          (let w := LJ x - LA x
           let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
           LinearMap.range (A + B).mulVecLin = imA) := by
        by_cases hker : LinearMap.ker LA ≤ F
        · have hLJ_mem : LJ x ∈ imA := him_eq ▸ ⟨x, rfl⟩
          rcases hLJ_mem with ⟨y, hy⟩
          have hyF : y ∉ F := by
            intro hyin
            have hLJy : LJ y = LA y := (sub_eq_zero.mp (LinearMap.mem_ker.mp hyin)).symm
            have hkerJ : y - x ∈ LinearMap.ker LJ := by
              rw [LinearMap.mem_ker, map_sub, hLJy, hy, sub_self]
            have hker_eq : LinearMap.ker LA = LinearMap.ker LJ := by
              have hle_J : LinearMap.ker LA ≤ LinearMap.ker LJ := by
                intro u hu
                have huF := hker hu
                have h1 : LA u - LJ u = 0 := LinearMap.mem_ker.mp huF
                rw [LinearMap.mem_ker.mp hu, zero_sub, neg_eq_zero] at h1
                exact h1
              have hdim_eq : Module.finrank K (LinearMap.ker LA) = Module.finrank K (LinearMap.ker LJ) := by
                have h1 := LinearMap.finrank_range_add_finrank_ker LA
                have h2 := LinearMap.finrank_range_add_finrank_ker LJ
                have h3 : Module.finrank K (LinearMap.range LA) = Module.finrank K (LinearMap.range LJ) := by
                  change Module.finrank K imA = Module.finrank K imJ; rw [him_eq]
                omega
              exact Submodule.eq_of_le_of_finrank_eq hle_J hdim_eq
            have hsubF : y - x ∈ F := hker (hker_eq.symm ▸ hkerJ)
            exact hxF (by simpa using Submodule.sub_mem F hyin hsubF)
          obtain ⟨f, hfF, hfx, hfy⟩ := exists_func_vanish_two F x y hxF hyF
          refine ⟨f, hfF, hfx, ?_⟩
          dsimp only
          let w := LJ x - LA x
          let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
          have hA'_lin : (A + B).mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
            rw [mulVecLin_add_geo, rank_one_matrix w f]
          apply le_antisymm
          · rintro _ ⟨v, rfl⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
            have hw_mem : w ∈ imA := Submodule.sub_mem imA (him_eq ▸ ⟨x, rfl⟩) ⟨x, rfl⟩
            exact Submodule.add_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ hw_mem)
          · have hw_in : w ∈ LinearMap.range (A + B).mulVecLin := by
              refine ⟨(f y)⁻¹ • (y - x), ?_⟩
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
                map_smul, map_sub, map_smul, map_sub, hy, hfx]
              have hcalc : (f y)⁻¹ • (LJ x - LA x) + ((f y)⁻¹ * (f y - 1)) • (LJ x - LA x) = LJ x - LA x := by
                rw [← add_smul]
                have hsc : (f y)⁻¹ + (f y)⁻¹ * (f y - 1) = 1 := by
                  field_simp [hfy]; ring
                rw [hsc, one_smul]
              simpa [w, smul_eq_mul] using hcalc
            rintro _ ⟨v, rfl⟩
            have h1 : (A + B).mulVecLin v - f v • w = LA v := by
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
              abel
            rw [← h1]
            exact Submodule.sub_mem _ ⟨v, rfl⟩ (Submodule.smul_mem _ _ hw_in)
        · have hex_u0 : ∃ u0 ∈ LinearMap.ker LA, u0 ∉ F := by
            by_contra hall; push Not at hall
            exact hker hall
          rcases hex_u0 with ⟨u0, hu0K, hu0F⟩
          obtain ⟨f, hfF, hfx, hfu0⟩ := exists_func_vanish_two F x u0 hxF hu0F
          refine ⟨f, hfF, hfx, ?_⟩
          dsimp only
          let w := LJ x - LA x
          let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
          have hA'_lin : (A + B).mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
            rw [mulVecLin_add_geo, rank_one_matrix w f]
          apply le_antisymm
          · rintro _ ⟨v, rfl⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
            have hw_mem : w ∈ imA := Submodule.sub_mem imA (him_eq ▸ ⟨x, rfl⟩) ⟨x, rfl⟩
            exact Submodule.add_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ hw_mem)
          · have hw_in : w ∈ LinearMap.range (A + B).mulVecLin := by
              refine ⟨(f u0)⁻¹ • u0, ?_⟩
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
                map_smul, LinearMap.mem_ker.mp hu0K, smul_zero, zero_add, map_smul, smul_eq_mul,
                inv_mul_cancel₀ hfu0, one_smul]
            rintro _ ⟨v, rfl⟩
            have h1 : (A + B).mulVecLin v - f v • w = LA v := by
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
              abel
            rw [← h1]
            exact Submodule.sub_mem _ ⟨v, rfl⟩ (Submodule.smul_mem _ _ hw_in)
      rcases hex_f with ⟨f, hfF, hfx, him_A'⟩
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hdist := rank_update_dist A J x f hfF hfx
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) -
            Module.finrank K (LinearMap.range A'.mulVecLin) =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank A - 1
        rw [him_A', hszA]
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank J - 1
        rw [him_A', hszJ]
        omega
    · have hex_x : ∃ x : Fin r → K, LA x ∉ imJ := by
        by_contra hall; push Not at hall
        apply hAle
        rintro _ ⟨x, rfl⟩; exact hall x
      rcases hex_x with ⟨x, hxJ⟩
      obtain ⟨g, hgJ, hgLAx⟩ := exists_func_vanish_one imJ (LA x) hxJ
      let f : (Fin r → K) →ₗ[K] K := g.comp LA
      have hfF : ∀ u ∈ F, f u = 0 := by
        intro u hu
        have heq : LA u = LJ u := sub_eq_zero.mp (LinearMap.mem_ker.mp hu)
        dsimp only [f]; rw [LinearMap.comp_apply, heq]; exact hgJ _ ⟨u, rfl⟩
      have hfx : f x = 1 := hgLAx
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hA'_lin : A'.mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
        rw [mulVecLin_add_geo, rank_one_matrix w f]
      let Hg : Submodule K (Fin q → K) := LinearMap.ker g ⊓ imA
      have hJleHg : imJ ≤ Hg := le_inf (fun y hy => LinearMap.mem_ker.mpr (hgJ y hy)) hJle
      have himA'_eq : LinearMap.range A'.mulVecLin = Hg := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have h1 : LA v + g (LA v) • (LJ x - LA x) = (LA v - g (LA v) • LA x) + g (LA v) • LJ x := by
            rw [smul_sub]; abel
          change LA v + g (LA v) • (LJ x - LA x) ∈ Hg
          rw [h1]
          refine Submodule.add_mem Hg ?_ (Submodule.smul_mem Hg _ (hJleHg ⟨x, rfl⟩))
          refine ⟨?_, Submodule.sub_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ ⟨x, rfl⟩)⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hgLAx, smul_eq_mul, mul_one, sub_self]
        · intro y hy
          rcases hy.2 with ⟨v, rfl⟩
          refine ⟨v, ?_⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have hgv : g (LA v) = 0 := LinearMap.mem_ker.mp hy.1
          change LA v + g (LA v) • w = LA v
          rw [hgv, zero_smul, add_zero]
      have hHg_dim : Module.finrank K Hg + 1 = Matrix.rank A := by
        let gA : imA →ₗ[K] K := g.comp imA.subtype
        have hgA_surj : Function.Surjective gA := by
          intro c
          refine ⟨⟨c • LA x, Submodule.smul_mem imA c ⟨x, rfl⟩⟩, ?_⟩
          change g (c • LA x) = c
          rw [map_smul, hgLAx, smul_eq_mul, mul_one]
        have hker_dim : Module.finrank K (LinearMap.ker gA) = Module.finrank K Hg := by
          let eK : LinearMap.ker gA ≃ₗ[K] Hg :=
            { toFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
              invFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          exact eK.finrank_eq
        have hrn := LinearMap.finrank_range_add_finrank_ker gA
        rw [LinearMap.range_eq_top.mpr hgA_surj, finrank_top, Module.finrank_self, hker_dim] at hrn
        change Module.finrank K Hg + 1 = Module.finrank K imA
        omega
      have hdist := rank_update_dist A J x f hfF hfx
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) -
            Module.finrank K (LinearMap.range A'.mulVecLin) =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank A - 1
        rw [himA'_eq, sup_eq_left.mpr hJleHg, sup_eq_left.mpr hJle]
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank J - 1
        rw [himA'_eq, sup_eq_left.mpr hJleHg, sup_eq_left.mpr hJle]
        have hJleA_dim : Matrix.rank J ≤ Matrix.rank A := Submodule.finrank_mono hJle
        have hJleHg_dim : Matrix.rank J ≤ Module.finrank K Hg := Submodule.finrank_mono hJleHg
        omega
  · by_cases hAle : imA ≤ imJ
    · have hex_x : ∃ x : Fin r → K, LJ x ∉ imA := by
        by_contra hall; push Not at hall
        apply hJle
        rintro _ ⟨x, rfl⟩; exact hall x
      rcases hex_x with ⟨x, hxA⟩
      have hxF : x ∉ F := by
        intro hx; exact hxA (by rw [← sub_eq_zero.mp (LinearMap.mem_ker.mp hx)]; exact ⟨x, rfl⟩)
      have hdim_lt : Module.finrank K imA < Module.finrank K imJ :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hAle (fun h => hJle h.symm.le))
      have hker_lt : Module.finrank K (LinearMap.ker LJ) < Module.finrank K (LinearMap.ker LA) := by
        have h1 := LinearMap.finrank_range_add_finrank_ker LA
        have h2 := LinearMap.finrank_range_add_finrank_ker LJ
        change Module.finrank K (LinearMap.range LA) < Module.finrank K (LinearMap.range LJ) at hdim_lt
        omega
      have hex_u0 : ∃ u0 ∈ LinearMap.ker LA, u0 ∉ F := by
        by_contra hall; push Not at hall
        have hle : LinearMap.ker LA ≤ LinearMap.ker LJ := by
          intro u hu
          have huF := hall u hu
          have h1 : LA u - LJ u = 0 := LinearMap.mem_ker.mp huF
          rw [LinearMap.mem_ker.mp hu, zero_sub, neg_eq_zero] at h1
          exact h1
        have := Submodule.finrank_mono hle
        omega
      rcases hex_u0 with ⟨u0, hu0K, hu0F⟩
      obtain ⟨f, hfF, hfx, hfu0⟩ := exists_func_vanish_two F x u0 hxF hu0F
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hA'_lin : A'.mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
        rw [mulVecLin_add_geo, rank_one_matrix w f]
      have himA'_eq : LinearMap.range A'.mulVecLin = imA ⊔ Submodule.span K ({LJ x} : Set (Fin q → K)) := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have h1 : LA v + f v • (LJ x - LA x) = (LA v - f v • LA x) + f v • LJ x := by
            rw [smul_sub]; abel
          change LA v + f v • (LJ x - LA x) ∈ _
          rw [h1]
          exact Submodule.add_mem_sup
            (Submodule.sub_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ ⟨x, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
        · have hw_in : w ∈ LinearMap.range A'.mulVecLin := by
            refine ⟨(f u0)⁻¹ • u0, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
              map_smul, LinearMap.mem_ker.mp hu0K, smul_zero, zero_add, map_smul, smul_eq_mul,
              inv_mul_cancel₀ hfu0, one_smul]
          refine sup_le ?_ ?_
          · rintro _ ⟨v, rfl⟩
            have h1 : A'.mulVecLin v - f v • w = LA v := by
              rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
              abel
            rw [← h1]
            exact Submodule.sub_mem _ ⟨v, rfl⟩ (Submodule.smul_mem _ _ hw_in)
          · rw [Submodule.span_singleton_le_iff_mem]
            refine ⟨x, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
              hfx, one_smul]
            dsimp only [w]
            abel
      have himA'_leJ : LinearMap.range A'.mulVecLin ≤ imJ := by
        rw [himA'_eq]
        exact sup_le hAle ((Submodule.span_singleton_le_iff_mem (LJ x) imJ).mpr ⟨x, rfl⟩)
      have himA'_dim : Matrix.rank A' = Matrix.rank A + 1 := by
        change Module.finrank K (LinearMap.range A'.mulVecLin) = Module.finrank K imA + 1
        rw [himA'_eq]
        have hinf : imA ⊓ Submodule.span K ({LJ x} : Set (Fin q → K)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          rcases Submodule.mem_span_singleton.mp hy.2 with ⟨c, rfl⟩
          by_cases hc : c = 0
          · rw [hc, zero_smul]; exact Submodule.zero_mem ⊥
          · exfalso
            have hmem : LJ x ∈ imA := by
              have := Submodule.smul_mem imA c⁻¹ hy.1
              rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
            exact hxA hmem
        have hLJ_ne : LJ x ≠ 0 := fun h0 => hxA (h0 ▸ Submodule.zero_mem imA)
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq imA (Submodule.span K ({LJ x} : Set (Fin q → K)))
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hLJ_ne] at hsup
        exact hsup
      have hdist := rank_update_dist A J x f hfF hfx
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank A' =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank A - 1
        rw [sup_eq_right.mpr himA'_leJ, sup_eq_right.mpr hAle, himA'_dim]
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(imA ⊔ imJ) - Matrix.rank J - 1
        rw [sup_eq_right.mpr himA'_leJ, sup_eq_right.mpr hAle]
        change Matrix.rank J - Matrix.rank J = Matrix.rank J - Matrix.rank J - 1
        omega
    · let S1 : Submodule K (Fin r → K) := Z.comap LA
      let S2 : Submodule K (Fin r → K) := Z.comap LJ
      have hS1_ne : S1 ≠ ⊤ := by
        intro htop
        apply hAle
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ S1 := htop ▸ Submodule.mem_top
        exact hx.2
      have hS2_ne : S2 ≠ ⊤ := by
        intro htop
        apply hJle
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ S2 := htop ▸ Submodule.mem_top
        exact hx.1
      obtain ⟨x, hx1, hx2⟩ := exists_not_mem_two S1 S2 hS1_ne hS2_ne
      have hxLA : LA x ∉ Z := hx1
      have hxLJ : LJ x ∉ Z := hx2
      obtain ⟨g, hgZ, hgLAx⟩ := exists_func_vanish_one Z (LA x) hxLA
      let f : (Fin r → K) →ₗ[K] K := g.comp LA
      have hfF : ∀ u ∈ F, f u = 0 := by
        intro u hu
        have heq : LA u = LJ u := sub_eq_zero.mp (LinearMap.mem_ker.mp hu)
        dsimp only [f]; rw [LinearMap.comp_apply]
        exact hgZ (LA u) ⟨⟨u, rfl⟩, heq ▸ ⟨u, rfl⟩⟩
      have hfx : f x = 1 := hgLAx
      let w := LJ x - LA x
      let B : Matrix (Fin q) (Fin r) K := fun i j => w i * f (Pi.single j 1)
      let A' := A + B
      have hA'_lin : A'.mulVecLin = LA + (LinearMap.toSpanSingleton K (Fin q → K) w).comp f := by
        rw [mulVecLin_add_geo, rank_one_matrix w f]
      let Hg : Submodule K (Fin q → K) := LinearMap.ker g ⊓ imA
      have hZleHg : Z ≤ Hg := le_inf (fun y hy => LinearMap.mem_ker.mpr (hgZ y hy)) inf_le_left
      have himA'_eq : LinearMap.range A'.mulVecLin = Hg ⊔ Submodule.span K ({LJ x} : Set (Fin q → K)) := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
          have h1 : LA v + g (LA v) • (LJ x - LA x) = (LA v - g (LA v) • LA x) + g (LA v) • LJ x := by
            rw [smul_sub]; abel
          change LA v + g (LA v) • (LJ x - LA x) ∈ _
          rw [h1]
          refine Submodule.add_mem_sup ?_ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
          refine ⟨?_, Submodule.sub_mem imA ⟨v, rfl⟩ (Submodule.smul_mem imA _ ⟨x, rfl⟩)⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hgLAx, smul_eq_mul, mul_one, sub_self]
        · refine sup_le ?_ ?_
          · intro y hy
            rcases hy.2 with ⟨v, rfl⟩
            refine ⟨v, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
            have hgv : g (LA v) = 0 := LinearMap.mem_ker.mp hy.1
            change LA v + g (LA v) • w = LA v
            rw [hgv, zero_smul, add_zero]
          · rw [Submodule.span_singleton_le_iff_mem]
            refine ⟨x, ?_⟩
            rw [hA'_lin, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
              hfx, one_smul]
            dsimp only [w]
            abel
      have hHg_dim : Module.finrank K Hg + 1 = Matrix.rank A := by
        let gA : imA →ₗ[K] K := g.comp imA.subtype
        have hgA_surj : Function.Surjective gA := by
          intro c
          refine ⟨⟨c • LA x, Submodule.smul_mem imA c ⟨x, rfl⟩⟩, ?_⟩
          change g (c • LA x) = c
          rw [map_smul, hgLAx, smul_eq_mul, mul_one]
        have hker_dim : Module.finrank K (LinearMap.ker gA) = Module.finrank K Hg := by
          let eK : LinearMap.ker gA ≃ₗ[K] Hg :=
            { toFun := fun z => ⟨z.1.1, z.2, z.1.2⟩
              invFun := fun z => ⟨⟨z.1, z.2.2⟩, z.2.1⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
          exact eK.finrank_eq
        have hrn := LinearMap.finrank_range_add_finrank_ker gA
        rw [LinearMap.range_eq_top.mpr hgA_surj, finrank_top, Module.finrank_self, hker_dim] at hrn
        change Module.finrank K Hg + 1 = Module.finrank K imA
        omega
      have hLJ_notHg : LJ x ∉ Hg := fun h => hxLJ ⟨h.2, ⟨x, rfl⟩⟩
      have hLJ_ne : LJ x ≠ 0 := fun h0 => hxLJ (h0 ▸ Submodule.zero_mem Z)
      have himA'_dim : Matrix.rank A' = Matrix.rank A := by
        change Module.finrank K (LinearMap.range A'.mulVecLin) = Matrix.rank A
        rw [himA'_eq]
        have hinf : Hg ⊓ Submodule.span K ({LJ x} : Set (Fin q → K)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          rcases Submodule.mem_span_singleton.mp hy.2 with ⟨c, rfl⟩
          by_cases hc : c = 0
          · rw [hc, zero_smul]; exact Submodule.zero_mem ⊥
          · exfalso
            have hmem : LJ x ∈ Hg := by
              have := Submodule.smul_mem Hg c⁻¹ hy.1
              rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
            exact hLJ_notHg hmem
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq Hg (Submodule.span K ({LJ x} : Set (Fin q → K)))
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hLJ_ne] at hsup
        omega
      have hZ'_eq : LinearMap.range A'.mulVecLin ⊓ imJ = Z ⊔ Submodule.span K ({LJ x} : Set (Fin q → K)) := by
        rw [himA'_eq]
        apply le_antisymm
        · intro y hy
          rcases Submodule.mem_sup.mp hy.1 with ⟨h, hh, s, hs, rfl⟩
          rcases Submodule.mem_span_singleton.mp hs with ⟨c, rfl⟩
          have hhJ : h ∈ imJ := by
            have := Submodule.sub_mem imJ hy.2 (Submodule.smul_mem imJ c ⟨x, rfl⟩)
            simpa using this
          exact Submodule.add_mem_sup ⟨hh.2, hhJ⟩ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _)))
        · exact sup_le (le_inf (le_trans hZleHg le_sup_left) inf_le_right)
            (le_inf le_sup_right ((Submodule.span_singleton_le_iff_mem (LJ x) imJ).mpr ⟨x, rfl⟩))
      have hZ'_dim : Module.finrank K ↥(LinearMap.range A'.mulVecLin ⊓ imJ) = Module.finrank K Z + 1 := by
        rw [hZ'_eq]
        have hinf : Z ⊓ Submodule.span K ({LJ x} : Set (Fin q → K)) = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          rcases Submodule.mem_span_singleton.mp hy.2 with ⟨c, rfl⟩
          by_cases hc : c = 0
          · rw [hc, zero_smul]; exact Submodule.zero_mem ⊥
          · exfalso
            have hmem : LJ x ∈ Z := by
              have := Submodule.smul_mem Z c⁻¹ hy.1
              rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
            exact hxLJ hmem
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq Z (Submodule.span K ({LJ x} : Set (Fin q → K)))
        rw [hinf, finrank_bot, add_zero, finrank_span_singleton hLJ_ne] at hsup
        exact hsup
      have hdist := rank_update_dist A J x f hfF hfx
      have hmodA := hmod A
      have hmodA' := hmod A'
      have hZ_lt_A : Module.finrank K Z < Matrix.rank A :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left
          (fun h => hAle (by change A.mulVecLin.range ≤ imJ; rw [← h]; exact inf_le_right)))
      have hZ_lt_J : Module.finrank K Z < Matrix.rank J :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_right
          (fun h => hJle (by change J.mulVecLin.range ≤ imA; rw [← h]; exact inf_le_left)))
      have hZ_def : Module.finrank K ↥(A.mulVecLin.range ⊓ imJ) = Module.finrank K Z := rfl
      refine ⟨A', hdist.1, hdist.2, ?_, ?_⟩
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(A'.mulVecLin.range ⊔ imJ) - Matrix.rank A' =
          Module.finrank K ↥(A.mulVecLin.range ⊔ imJ) - Matrix.rank A - 1
        omega
      · rw [rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
        change Module.finrank K ↥(A'.mulVecLin.range ⊔ imJ) - Matrix.rank J =
          Module.finrank K ↥(A.mulVecLin.range ⊔ imJ) - Matrix.rank J - 1
        omega

theorem path_exists_aux {K : Type*} [Field K] {q r : ℕ} :
    ∀ (d : ℕ) (H J : Matrix (Fin q) (Fin r) K),
      Matrix.rank (H - J) = d →
      let size := fun (A : Matrix (Fin q) (Fin r) K) =>
        Matrix.rank (fun i z => Sum.elim (A i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K)
      ∃ P : Fin (d + 1) → Matrix (Fin q) (Fin r) K,
        P 0 = H ∧ P (Fin.last d) = J ∧
        (∀ i j : Fin (d + 1), i ≤ j → Matrix.rank (P i - P j) = j.val - i.val) ∧
        ∀ i : Fin (d + 1),
          size (P i) - Matrix.rank (P i) = size H - Matrix.rank H - i.val ∧
          size (P i) - Matrix.rank J = size H - Matrix.rank J - i.val := by
  intro d
  induction d with
  | zero =>
    intro H J hd
    dsimp only
    have hHJ : H = J := by
      have h0 : LinearMap.range (H - J).mulVecLin = ⊥ :=
        Submodule.finrank_eq_zero.mp hd
      have hlin : (H - J).mulVecLin = 0 := LinearMap.range_eq_bot.mp h0
      have hsub0 : H - J = 0 := by
        ext i j
        have hv := congrFun (LinearMap.congr_fun hlin (Pi.single j 1)) i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using hv
      exact sub_eq_zero.mp hsub0
    refine ⟨fun _ => H, rfl, hHJ, ?_, ?_⟩
    · intro i j _
      simp
    · intro i
      simp
  | succ d ih =>
    intro H J hd
    dsimp only
    obtain ⟨H', hHH', hH'J, hdefJ, hdefA⟩ := exists_step H J (by omega)
    rw [hd] at hH'J
    have hH'J_eq : Matrix.rank (H' - J) = d := by omega
    obtain ⟨P', hP'0, hP'last, hP'dist, hP'def⟩ := ih H' J hH'J_eq
    let P : Fin (d + 2) → Matrix (Fin q) (Fin r) K := fun i =>
      Fin.cases H P' i
    refine ⟨P, rfl, ?_, ?_, ?_⟩
    · have hlast : Fin.last (d + 1) = Fin.succ (Fin.last d) := rfl
      rw [hlast]
      exact hP'last
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; simp [P]
        · intro _
          change Matrix.rank (H - P' j') = j'.val + 1
          have hle : Matrix.rank (H - P' j') ≤ j'.val + 1 := by
            have hsplit : H - P' j' = (H - H') + (H' - P' j') := by abel
            have hd' := hP'dist 0 j' (Fin.zero_le j')
            rw [hP'0] at hd'
            calc Matrix.rank (H - P' j')
                = Matrix.rank ((H - H') + (H' - P' j')) := by rw [hsplit]
              _ ≤ Matrix.rank (H - H') + Matrix.rank (H' - P' j') := rank_add_le_geo _ _
              _ = 1 + j'.val := by rw [hHH', hd']; simp
              _ = j'.val + 1 := by omega
          have hge : j'.val + 1 ≤ Matrix.rank (H - P' j') := by
            have hsplit : H - J = (H - P' j') + (P' j' - J) := by abel
            have hd' := hP'dist j' (Fin.last d) (Fin.le_last j')
            rw [hP'last] at hd'
            have h1 : d + 1 ≤ Matrix.rank (H - P' j') + Matrix.rank (P' j' - J) := by
              rw [← hd, hsplit]
              exact rank_add_le_geo _ _
            rw [hd'] at h1
            have hjlt : j'.val ≤ d := Nat.lt_succ_iff.mp j'.isLt
            dsimp [Fin.last] at h1
            omega
          omega
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact absurd hij (not_le.mpr (Fin.succ_pos i'))
        · intro hij
          have hij' : i' ≤ j' := Fin.succ_le_succ_iff.mp hij
          change Matrix.rank (P' i' - P' j') = (j'.val + 1) - (i'.val + 1)
          rw [hP'dist i' j' hij']
          omega
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [P]
      · have hdef' := hP'def i'
        dsimp only at hdef' hdefJ hdefA
        have hPsucc : P i'.succ = P' i' := rfl
        constructor
        · change Matrix.rank (fun i z => Sum.elim (P' i' i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank (P' i') =
            Matrix.rank (fun i z => Sum.elim (H i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank H - (i'.val + 1)
          rw [hdef'.1, hdefJ]
          omega
        · change Matrix.rank (fun i z => Sum.elim (P' i' i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank J =
            Matrix.rank (fun i z => Sum.elim (H i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K) -
              Matrix.rank J - (i'.val + 1)
          rw [hdef'.2, hdefA]
          omega
end GeodesicPath

section MatrixBounds
open Matrix
abbrev F := ZMod 2
abbrev Mat (i j : Nat) := Matrix (Fin i) (Fin j) F
abbrev Sq (r : Nat) := Mat r r

def bit (b : Bool) : F := (b.toNat : F)
theorem bit_eq (b : Bool) : bit b = b2z b := by cases b <;> rfl
theorem bit_dec (x : F) : bit (decide (x = 1)) = x := by revert x; decide
theorem xor_bit (a b : Bool) : bit (xor a b) = bit a - bit b := by cases a <;> cases b <;> decide
theorem two (a : F) : a + a = 0 := by revert a; decide

theorem sub_comm_F {m n : Nat} (A B : Mat m n) : A - B = B - A := by
  ext i j
  simp only [Matrix.sub_apply]
  generalize A i j = x
  generalize B i j = y
  revert x y
  decide

theorem addRank (A B : Mat m n) : (A + B).rank ≤ A.rank + B.rank := by
  have h := LinearMap.rank_add_le A.mulVecLin B.mulVecLin
  simp only [LinearMap.rank, ← Submodule.finrank_eq_rank, ← Nat.cast_add] at h
  change Module.finrank F (LinearMap.range (A + B).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_add]
  exact_mod_cast h

theorem dist (A B C : Mat m n) : (A - C).rank ≤ (A - B).rank + (B - C).rank := by
  simpa only [sub_add_sub_cancel] using addRank (A - B) (B - C)

theorem factor (A : Mat m n) (h : A.rank ≤ w) : ∃ U : Mat m w, ∃ V : Mat w n, U * V = A := by
  obtain ⟨u, v, eq⟩ := factor_of_rank_le A h
  exact ⟨fun i k => u k i, v, by ext i j; exact (eq i j).symm⟩

theorem zeroMat_of_rank_zero {m n : Nat} {M : Mat m n} (h : M.rank = 0) : M = 0 := by
  have hh : Module.finrank F (LinearMap.range M.mulVecLin) = 0 := h
  have hb : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hh
  have h0 : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hb
  ext i j
  have hv := congrFun (LinearMap.congr_fun h0 (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using hv

def Anchor (P : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) : Mat n m :=
  fun a b => bit (P a b) + bit (P u b) + bit (P a v) + bit (P u v)

theorem criterion (P : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t) :
    (Anchor P u v).rank ≤ 2 * t ↔ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C ∧
    PEqualNP.Represents.Represents P C) ∧
    (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧ C.gates.countP nlGate ≤ t := by
  have same : Anchor P u v = anchor u v (fun i j => b2z (P i j)) := by
    ext; unfold Anchor anchor; simp only [bit_eq]; abel
  rw [same]
  exact main n m P u v t

def Rects {q r : Nat} (e : Nat) (D : Mat q r) :=
  ∃ X : Fin e → Finset (Fin q), ∃ Y : Fin e → Finset (Fin r), ∀ a b,
    D a b = bit (decide ((Finset.univ.filter (fun h : Fin e => a ∈ X h ∧ b ∈ Y h)).card % 2 = 1))

theorem parity (s : Finset α) (p : α → Prop) [DecidablePred p] :
    bit (decide ((s.filter p).card % 2 = 1)) = ∑ k ∈ s, (if p k then 1 else 0 : F) := by
  rw [Finset.sum_boole]
  generalize (s.filter p).card = l
  have e : (l : F) = (l % 2 : Nat) := (ZMod.natCast_mod l 2).symm
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one l with h | h <;> simp [h, bit]

theorem rect_iff {q r e : Nat} (D : Mat q r) : Rects e D ↔ D.rank ≤ e := by
  classical
  constructor
  · rintro ⟨X, Y, eq⟩
    let U : Mat q e := fun a j => if a ∈ X j then 1 else 0
    let V : Mat e r := fun j b => if b ∈ Y j then 1 else 0
    have f : D = U * V := by
      ext a b; rw [eq, parity, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _; by_cases h : a ∈ X j <;> by_cases h' : b ∈ Y j <;> simp [U, V, h, h']
    rw [f]; exact rank_of_factor _ _
  · intro h
    obtain ⟨U, V, eq⟩ := factor D h
    refine ⟨fun j => Finset.univ.filter (fun a => U a j = 1),
            fun j => Finset.univ.filter (fun b => V j b = 1), ?_⟩
    intro a b
    rw [← eq, Matrix.mul_apply, parity]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    generalize U a j = x; generalize V j b = y; revert x y; decide

noncomputable def bothRank {q r : Nat} (A B : Mat q r) : Nat :=
  Matrix.rank (fun i z => Sum.elim (A i) (B i) z : Matrix (Fin q) (Fin r ⊕ Fin r) F)

def PathFrames (k r q w : Nat) (H' J : Mat q r) : Prop :=
  ∃ (A : Fin (k + 1) → Mat r w) (A_end : Mat q w) (B : Fin (k + 2) → Mat w r),
    (∀ i : Fin (k + 1), A i * B i.castSucc = 1 ∧ A i * B i.succ = 1) ∧
    A_end * B 0 = H' ∧ A_end * B (Fin.last (k + 1)) = J

end MatrixBounds

section PanelEncoding
open Matrix

abbrev RowPanel (k r q n : Nat) := ((Fin (k + 1) × Fin r) ⊕ Fin q) ↪ Fin n
abbrev ColPanel (k r m : Nat) := (Fin (k + 2) × Fin r) ↪ Fin m

def pblock (rows : RowPanel k r q n) (cols : ColPanel k r m) (u : Fin n) (v : Fin m)
    (P : Fin n → Fin m → Bool) (i : Fin (k + 1)) (j : Fin (k + 2)) : Sq r :=
  fun a b => Anchor P u v (rows (Sum.inl (i, a))) (cols (j, b))

def pends (rows : RowPanel k r q n) (cols : ColPanel k r m) (u : Fin n) (v : Fin m)
    (P : Fin n → Fin m → Bool) (j : Fin (k + 2)) : Mat q r :=
  fun a b => Anchor P u v (rows (Sum.inr a)) (cols (j, b))

def perrs (rows : RowPanel k r q n) (cols : ColPanel k r m)
    (P T : Fin n → Fin m → Bool) (e : Nat) : Prop :=
  ∃ X : Fin e → Finset (Fin q), ∃ Y : Fin e → Finset (Fin r), ∀ a b,
    xor (P (rows (Sum.inr a)) (cols (0, b))) (T (rows (Sum.inr a)) (cols (0, b))) =
      decide ((Finset.univ.filter (fun h : Fin e => a ∈ X h ∧ b ∈ Y h)).card % 2 = 1)

theorem errRank (rows : RowPanel k r q n) (cols : ColPanel k r m) (u : Fin n) (v : Fin m)
    (P T : Fin n → Fin m → Bool) (col : ∀ a, P a v = T a v) (row : ∀ b, P u b = T u b) :
    perrs rows cols P T e ↔ (pends rows cols u v P 0 - pends rows cols u v T 0).rank ≤ e := by
  rw [← rect_iff]
  have bitInj : Function.Injective bit := by intro a b h; apply b2z_inj; simpa only [← bit_eq] using h
  have delta (a b) : (pends rows cols u v P 0 - pends rows cols u v T 0) a b =
      bit (xor (P (rows (Sum.inr a)) (cols (0, b))) (T (rows (Sum.inr a)) (cols (0, b)))) := by
    simp only [Matrix.sub_apply, pends, Anchor, col, row, xor_bit]
    abel
  constructor
  · rintro ⟨X, Y, h⟩; exact ⟨X, Y, fun a b => (delta a b).trans (congrArg bit (h a b))⟩
  · rintro ⟨X, Y, h⟩; exact ⟨X, Y, fun a b => bitInj ((delta a b).symm.trans (h a b))⟩

theorem extendPanel (rows : RowPanel k r q n) (cols : ColPanel k r m) (u : Fin n) (v : Fin m)
    (ru : ∀ z, rows z ≠ u) (cv : ∀ z, cols z ≠ v) (T : Fin n → Fin m → Bool)
    (U : Fin (k + 1) → Mat r w) (U_end : Mat q w) (V : Fin (k + 2) → Mat w r) :
    ∃ P, (∀ a, P a v = T a v) ∧ (∀ b, P u b = T u b) ∧
      (Anchor P u v).rank ≤ w ∧
      (∀ i j, pblock rows cols u v P i j = U i * V j) ∧
      (∀ j, pends rows cols u v P j = U_end * V j) := by
  classical
  let A : Mat n w := Function.extend rows (Sum.elim (fun z => U z.1 z.2) (fun a => U_end a)) (fun _ => 0)
  let ys := Function.extend cols (fun z h => V z.1 h z.2) (fun _ _ => (0 : F))
  let B : Mat w m := fun h b => ys b h
  have au : A u = 0 := Function.extend_apply' _ _ _ (by simpa using ru)
  have bv (i) : B i v = 0 := by
    have h : ys v = fun _ => 0 := Function.extend_apply' _ _ _ (by simpa using cv)
    exact congrFun h i
  let M := A * B
  have mu (j) : M u j = 0 := by simp [M, Matrix.mul_apply, au]
  have mv (i) : M i v = 0 := by simp [M, Matrix.mul_apply, bv]
  let P := fun a b => decide (M a b + bit (T a v) + bit (T u b) + bit (T u v) = 1)
  have col (a) : P a v = T a v := by
    simp only [P, mv, zero_add, add_assoc, two, add_zero]
    cases T a v <;> decide
  have row (b) : P u b = T u b := by
    simp only [P, mu, zero_add, add_right_comm (bit (T u v)), two, zero_add]
    cases T u b <;> decide
  have eq : Anchor P u v = M := by
    ext a b
    simp only [Anchor, row, col, P, bit_dec]
    generalize bit (T u v) = x; generalize bit (T a v) = y; generalize bit (T u b) = z
    have := two x; have := two y; have := two z; linear_combination ‹x + x = 0› + ‹y + y = 0› + ‹z + z = 0›
  refine ⟨P, col, row, eq ▸ rank_of_factor A B, ?_, ?_⟩
  · intro i j; ext a b
    change Anchor P u v _ _ = _
    rw [eq]
    change (A * B) (rows (Sum.inl (i, a))) (cols (j, b)) = (U i * V j) a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro h _
    simp only [A, B, ys, rows.injective.extend_apply, cols.injective.extend_apply, Sum.elim_inl]
  · intro j; ext a b
    change Anchor P u v _ _ = _
    rw [eq]
    change (A * B) (rows (Sum.inr a)) (cols (j, b)) = (U_end * V j) a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro h _
    simp only [A, B, ys, rows.injective.extend_apply, cols.injective.extend_apply, Sum.elim_inr]

def PanelRank (rows : RowPanel k r q n) (cols : ColPanel k r m) (u : Fin n) (v : Fin m)
    (T : Fin n → Fin m → Bool) (w e : Nat) : Prop :=
  ∃ P, (Anchor P u v).rank ≤ w ∧ (∀ a, P a v = T a v) ∧ (∀ b, P u b = T u b) ∧
    (∀ i : Fin (k + 1),
      pblock rows cols u v P i i.castSucc = pblock rows cols u v T i i.castSucc ∧
      pblock rows cols u v P i i.succ = pblock rows cols u v T i i.succ) ∧
    pends rows cols u v P (Fin.last (k + 1)) = pends rows cols u v T (Fin.last (k + 1)) ∧
    perrs rows cols P T e

theorem panel_iff (rows : RowPanel k r q n) (cols : ColPanel k r m) (u : Fin n) (v : Fin m)
    (ru : ∀ z, rows z ≠ u) (cv : ∀ z, cols z ≠ v) (T : Fin n → Fin m → Bool)
    (L : Fin (k + 1) → Sq r) (R : Fin (k + 2) → Sq r) (H J : Mat q r)
    (hL : ∀ i, IsUnit (L i)) (hR : ∀ j, IsUnit (R j))
    (hblk : ∀ i : Fin (k + 1),
      pblock rows cols u v T i i.castSucc = L i * R i.castSucc ∧
      pblock rows cols u v T i i.succ = L i * R i.succ)
    (hend0 : pends rows cols u v T 0 = H * R 0)
    (hendL : pends rows cols u v T (Fin.last (k + 1)) = J * R (Fin.last (k + 1))) :
    PanelRank rows cols u v T w e ↔ ∃ H' : Mat q r, PathFrames k r q w H' J ∧ (H' - H).rank ≤ e := by
  classical
  let l : Fin (k + 2) := Fin.last (k + 1)
  have lu (i) := (L i).isUnit_iff_isUnit_det.mp (hL i)
  have rv (j) := (R j).isUnit_iff_isUnit_det.mp (hR j)
  have sameRank (D : Mat q r) : (D * R 0).rank = D.rank :=
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (rv 0)
  constructor
  · rintro ⟨P, pr, pc, pq, pbl, pel, pe⟩
    obtain ⟨U, V, fac⟩ := factor _ pr
    let X : Fin (k + 1) → Mat r w := fun i a h => U (rows (Sum.inl (i, a))) h
    let X_end : Mat q w := fun a h => U (rows (Sum.inr a)) h
    let Y : Fin (k + 2) → Mat w r := fun j h b => V h (cols (j, b))
    have eqB (i j) : X i * Y j = pblock rows cols u v P i j := by
      ext a b; exact congrFun (congrFun fac (rows (Sum.inl (i, a)))) (cols (j, b))
    have eqE (j) : X_end * Y j = pends rows cols u v P j := by
      ext a b; exact congrFun (congrFun fac (rows (Sum.inr a))) (cols (j, b))
    let A : Fin (k + 1) → Mat r w := fun i => (L i)⁻¹ * X i
    let B : Fin (k + 2) → Mat w r := fun j => Y j * (R j)⁻¹
    have scaleB (i j) : A i * B j = (L i)⁻¹ * (pblock rows cols u v P i j) * (R j)⁻¹ := by
      rw [← eqB]; simp only [A, B, Matrix.mul_assoc]
    have scaleE (j) : X_end * B j = (pends rows cols u v P j) * (R j)⁻¹ := by
      rw [← eqE]; simp only [B, Matrix.mul_assoc]
    have norm (i j) (h : pblock rows cols u v P i j = L i * R j) : A i * B j = 1 := by
      rw [scaleB, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (lu i), one_mul,
        Matrix.mul_nonsing_inv _ (rv j)]
    have hlast : X_end * B l = J := by
      rw [scaleE, pel, hendL, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (rv l), Matrix.mul_one]
    refine ⟨X_end * B 0, ⟨A, X_end, B,
      fun i => ⟨norm i i.castSucc ((pbl i).1.trans (hblk i).1),
                norm i i.succ ((pbl i).2.trans (hblk i).2)⟩,
      rfl, hlast⟩, ?_⟩
    have close := (errRank rows cols u v P T pc pq).mp pe
    have cancel : (X_end * B 0) * R 0 = pends rows cols u v P 0 := by
      rw [scaleE, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (rv 0), Matrix.mul_one]
    rw [← sameRank, Matrix.sub_mul, cancel, ← hend0]
    exact close
  · rintro ⟨H', ⟨A, A_end, B, hAB, h0, hL'⟩, err⟩
    obtain ⟨P, pc, pq, pr, hPB, hPE⟩ :=
      extendPanel rows cols u v ru cv T (fun i => L i * A i) A_end (fun j => B j * R j)
    have eqB (i j) : pblock rows cols u v P i j = L i * (A i * B j) * R j := by
      rw [hPB]; simp [Matrix.mul_assoc]
    have eqE (j) : pends rows cols u v P j = (A_end * B j) * R j := by
      rw [hPE]; simp [Matrix.mul_assoc]
    refine ⟨P, pr, pc, pq,
      fun i => ⟨by rw [eqB, (hAB i).1, mul_one, (hblk i).1],
                by rw [eqB, (hAB i).2, mul_one, (hblk i).2]⟩,
      by rw [eqE, hL', hendL], ?_⟩
    apply (errRank rows cols u v P T pc pq).mpr
    rw [eqE, h0, hend0, ← Matrix.sub_mul]
    exact (sameRank _).le.trans err

end PanelEncoding

section Necessity
open Matrix Module LinearMap Submodule

theorem pathFrames_necessary {k r q w : Nat} {H' J : Mat q r}
    (h : PathFrames k r q w H' J) :
    r ≤ w ∧ bothRank H' J ≤ H'.rank + (w - r) ∧ bothRank H' J ≤ J.rank + (w - r) ∧
      (H' - J).rank ≤ (k + 1) * (w - r) := by
  obtain ⟨A, A_end, B, hAB, h0, hL⟩ := h
  have leA (i : Fin (k + 1)) : r ≤ (A i).rank := by
    simpa [(hAB i).1] using rank_mul_le_left (A i) (B i.castSucc)
  have rw' : r ≤ w := (leA 0).trans (by simpa using rank_le_card_width (A 0))
  have injB0 : Function.Injective (B 0).mulVecLin := by
    have hAB0 : A 0 * B 0 = 1 := (hAB 0).1
    intro x y hxy
    have hcomp := congrArg (A 0).mulVecLin hxy
    change (A 0).mulVecLin ((B 0).mulVecLin x) = (A 0).mulVecLin ((B 0).mulVecLin y) at hcomp
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hAB0,
      Matrix.mulVecLin_one] at hcomp
    exact hcomp
  have injBL : Function.Injective (B (Fin.last (k + 1))).mulVecLin := by
    have hlast_eq : (Fin.last k).succ = Fin.last (k + 1) := by ext; simp
    have hprod : A (Fin.last k) * B (Fin.last (k + 1)) = 1 := by
      rw [← hlast_eq]; exact (hAB (Fin.last k)).2
    intro x y hxy
    have hcomp := congrArg (A (Fin.last k)).mulVecLin hxy
    change (A (Fin.last k)).mulVecLin ((B (Fin.last (k + 1))).mulVecLin x) =
      (A (Fin.last k)).mulVecLin ((B (Fin.last (k + 1))).mulVecLin y) at hcomp
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hprod,
      Matrix.mulVecLin_one] at hcomp
    exact hcomp
  have bound_from_endpoint : ∀ (idx : Fin (k + 2)) (X Y : Mat q r),
      Function.Injective (B idx).mulVecLin → A_end * B idx = X →
      LinearMap.range Y.mulVecLin ≤ LinearMap.range A_end.mulVecLin →
      bothRank X Y ≤ X.rank + (w - r) := by
    intro idx X Y hinj hX hY
    let W := LinearMap.range (B idx).mulVecLin
    have hWdim : finrank F W = r := by
      have h1 := LinearMap.finrank_range_of_inj hinj
      simpa [W] using h1
    obtain ⟨U, hWU⟩ := Submodule.exists_isCompl W
    have hUdim : finrank F U = w - r := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq W U
      rw [hWU.sup_eq_top, hWU.inf_eq_bot, finrank_top, finrank_bot, add_zero, finrank_fin_fun, hWdim] at hsup
      omega
    let S := U.map A_end.mulVecLin
    have hSdim : finrank F S ≤ w - r := (Submodule.finrank_map_le A_end.mulVecLin U).trans (by omega)
    have hmapW : W.map A_end.mulVecLin = LinearMap.range X.mulVecLin := by
      rw [← hX, Matrix.mulVecLin_mul, LinearMap.range_comp]
    have hrange_end : LinearMap.range A_end.mulVecLin = LinearMap.range X.mulVecLin ⊔ S := by
      calc LinearMap.range A_end.mulVecLin
          = Submodule.map A_end.mulVecLin ⊤ := by rw [Submodule.map_top]
        _ = Submodule.map A_end.mulVecLin (W ⊔ U) := by rw [hWU.sup_eq_top]
        _ = W.map A_end.mulVecLin ⊔ U.map A_end.mulVecLin := Submodule.map_sup _ _ _
        _ = LinearMap.range X.mulVecLin ⊔ S := by rw [hmapW]
    have hle : LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin ≤
        LinearMap.range X.mulVecLin ⊔ S := by
      refine sup_le le_sup_left ?_
      exact hY.trans (le_of_eq hrange_end)
    rw [bothRank, rank_elim_eq_finrank_sup]
    have hmono := Submodule.finrank_mono hle
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range X.mulVecLin) S
    change finrank F ↥(LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin) ≤
      finrank F (LinearMap.range X.mulVecLin) + (w - r)
    omega
  have hY_J : LinearMap.range J.mulVecLin ≤ LinearMap.range A_end.mulVecLin := by
    rw [← hL, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  have hY_H' : LinearMap.range H'.mulVecLin ≤ LinearMap.range A_end.mulVecLin := by
    rw [← h0, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  have hbH' : bothRank H' J ≤ H'.rank + (w - r) :=
    bound_from_endpoint 0 H' J injB0 h0 hY_J
  have hbJ : bothRank H' J ≤ J.rank + (w - r) := by
    have hsym : bothRank H' J = bothRank J H' := by
      rw [bothRank, bothRank, rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup, sup_comm]
    rw [hsym]
    exact bound_from_endpoint (Fin.last (k + 1)) J H' injBL hL hY_H'
  refine ⟨rw', hbH', hbJ, ?_⟩
  let S := fun j : Fin (k + 2) => A_end * B j
  have step (i : Fin (k + 1)) : (S i.castSucc - S i.succ).rank ≤ w - r := by
    have z : A i * (B i.castSucc - B i.succ) = 0 := by
      rw [Matrix.mul_sub, (hAB i).1, (hAB i).2, sub_self]
    have d := rank_add_rank_le_card_of_mul_eq_zero z
    rw [Fintype.card_fin] at d
    have a := leA i
    have v := rank_mul_le_right A_end (B i.castSucc - B i.succ)
    rw [Matrix.mul_sub] at v
    exact v.trans (by omega)
  have run (j : Fin (k + 2)) : (S 0 - S j).rank ≤ j.val * (w - r) := by
    induction j using Fin.induction with
    | zero => simp
    | succ i ih =>
      have d := dist (S 0) (S i.castSucc) (S i.succ)
      have st := step i
      simpa [Fin.val_succ, Nat.succ_mul] using d.trans (Nat.add_le_add ih st)
  have hrun := run (Fin.last (k + 1))
  simpa [S, h0, hL] using hrun

theorem necessary_with_err {k r q w e : Nat} {H H' J : Mat q r}
    (hf : PathFrames k r q w H' J) (herr : (H' - H).rank ≤ e) :
    r ≤ w ∧ bothRank H J ≤ H.rank + (w - r) + e ∧ bothRank H J ≤ J.rank + (w - r) + e ∧
      (H - J).rank ≤ (k + 1) * (w - r) + e := by
  obtain ⟨hrw, hbH', hbJ, hdist⟩ := pathFrames_necessary hf
  have hHH' : (H - H').rank ≤ e := by rw [sub_comm_F]; exact herr
  have hboth_tri : ∀ (X Y Z : Mat q r), bothRank X Z ≤ bothRank Y Z + (X - Y).rank := by
    intro X Y Z
    rw [bothRank, bothRank, rank_elim_eq_finrank_sup, rank_elim_eq_finrank_sup]
    have hXle : LinearMap.range X.mulVecLin ≤
        LinearMap.range Y.mulVecLin ⊔ LinearMap.range (X - Y).mulVecLin := by
      rintro y ⟨v, rfl⟩
      have h1 : X.mulVecLin v = Y.mulVecLin v + (X - Y).mulVecLin v := by
        rw [← LinearMap.add_apply, ← Matrix.mulVecLin_add, add_sub_cancel]
      rw [h1]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    have hle : LinearMap.range X.mulVecLin ⊔ LinearMap.range Z.mulVecLin ≤
        (LinearMap.range Y.mulVecLin ⊔ LinearMap.range Z.mulVecLin) ⊔ LinearMap.range (X - Y).mulVecLin := by
      refine sup_le ?_ (le_sup_right.trans le_sup_left)
      exact hXle.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    have hm := Submodule.finrank_mono hle
    have hs := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range Y.mulVecLin ⊔ LinearMap.range Z.mulVecLin) (LinearMap.range (X - Y).mulVecLin)
    change finrank F ↥(LinearMap.range X.mulVecLin ⊔ LinearMap.range Z.mulVecLin) ≤
      finrank F ↥(LinearMap.range Y.mulVecLin ⊔ LinearMap.range Z.mulVecLin) +
      finrank F (LinearMap.range (X - Y).mulVecLin)
    omega
  have h1 : bothRank H J ≤ H.rank + (w - r) + e := by
    have hle : LinearMap.range H'.mulVecLin ≤ LinearMap.range H.mulVecLin ⊔ LinearMap.range (H' - H).mulVecLin := by
      rintro y ⟨v, rfl⟩
      have heq : H'.mulVecLin v = H.mulVecLin v + (H' - H).mulVecLin v := by
        rw [← LinearMap.add_apply, ← Matrix.mulVecLin_add, add_sub_cancel]
      rw [heq]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    have hJle_aux : bothRank H J ≤ bothRank H' J + (H - H').rank := hboth_tri H H' J
    obtain ⟨A, A_end, B, hAB, h0, hL⟩ := hf
    have injB0 : Function.Injective (B 0).mulVecLin := by
      have hAB0 : A 0 * B 0 = 1 := (hAB 0).1
      intro x y hxy
      have hcomp := congrArg (A 0).mulVecLin hxy
      change (A 0).mulVecLin ((B 0).mulVecLin x) = (A 0).mulVecLin ((B 0).mulVecLin y) at hcomp
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hAB0,
        Matrix.mulVecLin_one] at hcomp
      exact hcomp
    let W := LinearMap.range (B 0).mulVecLin
    have hWdim : finrank F W = r := by simpa [W] using LinearMap.finrank_range_of_inj injB0
    obtain ⟨U, hWU⟩ := Submodule.exists_isCompl W
    have hUdim : finrank F U = w - r := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq W U
      rw [hWU.sup_eq_top, hWU.inf_eq_bot, finrank_top, finrank_bot, add_zero, finrank_fin_fun, hWdim] at hsup
      omega
    let S := U.map A_end.mulVecLin
    have hSdim : finrank F S ≤ w - r := (Submodule.finrank_map_le A_end.mulVecLin U).trans (by omega)
    have hmapW : W.map A_end.mulVecLin = LinearMap.range H'.mulVecLin := by
      rw [← h0, Matrix.mulVecLin_mul, LinearMap.range_comp]
    have hrange_end : LinearMap.range A_end.mulVecLin = LinearMap.range H'.mulVecLin ⊔ S := by
      calc LinearMap.range A_end.mulVecLin
          = Submodule.map A_end.mulVecLin ⊤ := by rw [Submodule.map_top]
        _ = Submodule.map A_end.mulVecLin (W ⊔ U) := by rw [hWU.sup_eq_top]
        _ = W.map A_end.mulVecLin ⊔ U.map A_end.mulVecLin := Submodule.map_sup _ _ _
        _ = LinearMap.range H'.mulVecLin ⊔ S := by rw [hmapW]
    have hJle : LinearMap.range J.mulVecLin ≤ LinearMap.range H'.mulVecLin ⊔ S := by
      rw [← hrange_end, ← hL, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    have hsup_le : LinearMap.range H.mulVecLin ⊔ LinearMap.range J.mulVecLin ≤
        (LinearMap.range H.mulVecLin ⊔ S) ⊔ LinearMap.range (H' - H).mulVecLin := by
      refine sup_le (le_sup_left.trans le_sup_left) ?_
      refine hJle.trans (sup_le ?_ (le_sup_right.trans le_sup_left))
      exact hle.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    rw [bothRank, rank_elim_eq_finrank_sup]
    have hm := Submodule.finrank_mono hsup_le
    have hs1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range H.mulVecLin ⊔ S)
      (LinearMap.range (H' - H).mulVecLin)
    have hs2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range H.mulVecLin) S
    change finrank F ↥(LinearMap.range H.mulVecLin ⊔ LinearMap.range J.mulVecLin) ≤
      finrank F (LinearMap.range H.mulVecLin) + (w - r) + e
    have herr' : finrank F (LinearMap.range (H' - H).mulVecLin) ≤ e := herr
    omega
  have h2 : bothRank H J ≤ J.rank + (w - r) + e := by
    have ht := hboth_tri H H' J
    omega
  have h3 : (H - J).rank ≤ (k + 1) * (w - r) + e := by
    have hd := dist H H' J
    omega
  exact ⟨hrw, h1, h2, h3⟩

end Necessity

section RankRepair
open LinearMap Submodule Module Matrix
abbrev Vect (r : Nat) := Fin r → F
abbrev Endo (r : Nat) := Vect r →ₗ[F] Vect r

theorem outsideBoth {r : Nat} (U W : Submodule F (Vect r)) (u : U ≠ ⊤) (w : W ≠ ⊤) :
    ∃ x, x ∉ U ∧ x ∉ W := by
  obtain ⟨a, _, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr u)
  obtain ⟨b, _, hb⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr w)
  by_cases aw : a ∈ W
  · by_cases bu : b ∈ U
    · exact ⟨a + b, fun h => ha ((U.add_mem_iff_left bu).mp h), fun h => hb ((W.add_mem_iff_right aw).mp h)⟩
    · exact ⟨b, bu, hb⟩
  · exact ⟨a, ha, aw⟩

private theorem nzOne {x : F} : x ≠ 0 → x = 1 := by revert x; decide

theorem repair_map (f : Endo r) (bad : f ≠ LinearMap.id) :
    ∃ (g : Endo r) (φ : Vect r →ₗ[F] F) (v : Vect r),
      g = f + φ.smulRight v ∧
      finrank F (range (LinearMap.id - g)) < finrank F (range (LinearMap.id - f)) ∧
      min r (finrank F (range f) + 1) ≤ finrank F (range g) := by
  classical
  let K := ker (LinearMap.id - f)
  have km (y) : y ∈ K ↔ f y = y := by
    change y - f y = 0 ↔ f y = y
    rw [sub_eq_zero]; exact eq_comm
  have kp : K ≠ ⊤ := by
    intro h
    apply bad; apply LinearMap.ext; intro y
    exact (km y).mp (h ▸ Submodule.mem_top)
  let sing := ¬ Function.Injective f
  obtain ⟨h, hk, hz⟩ : ∃ h, h ∉ K ∧ (sing → f h = 0) := by
    by_cases s : Function.Injective f
    · obtain ⟨h, _, hn⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr kp)
      exact ⟨h, hn, fun hs => False.elim (hs s)⟩
    · have nz : ker f ≠ ⊥ := fun e => s (ker_eq_bot.mp e)
      obtain ⟨h, hin, hn⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr nz)
      have h0 : h ≠ 0 := fun e => hn (by simp [e])
      have z : f h = 0 := hin
      exact ⟨h, fun hf => h0 (((km h).mp hf).symm.trans z), fun _ => z⟩
  obtain ⟨φ, nonzero, ann⟩ := Submodule.exists_le_ker_of_notMem hk
  have ph := nzOne nonzero
  let W := ker φ
  have wp : W ≠ ⊤ := by intro eq; exact nonzero (show h ∈ W from eq ▸ Submodule.mem_top)
  have wm : W.map f ≠ ⊤ := by
    intro eq
    have a := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr wp)
    have b := Submodule.finrank_map_le f W
    rw [eq] at b
    omega
  obtain ⟨x, xw, xf⟩ := outsideBoth W (W.map f) wp wm
  have px : φ x = 1 := nzOne xw
  let v := x - f x
  let g := f + φ.smulRight v
  have val (y) : g y = f y + φ y • v := rfl
  have fixx : g x = x := by rw [val, px, one_smul]; dsimp [v]; abel
  have fixed : K < ker (LinearMap.id - g) := by
    apply lt_of_le_of_ne
    · intro y hy
      have py : φ y = 0 := ann hy
      simp [LinearMap.mem_ker, val, py, (km y).mp hy]
    · intro eq; apply xw; apply ann
      rw [eq]
      simp [LinearMap.mem_ker, fixx]
  refine ⟨g, φ, v, rfl, ?_, ?_⟩
  · have a := Submodule.finrank_lt_finrank_of_lt fixed
    have b := (LinearMap.id - f).finrank_range_add_finrank_ker
    have c := (LinearMap.id - g).finrank_range_add_finrank_ker
    change finrank F (ker (LinearMap.id - f)) < _ at a
    omega
  · by_cases s : Function.Injective f
    · have inj : Function.Injective g := by
        apply LinearMap.ker_eq_bot.mp
        apply le_antisymm _ bot_le
        intro y hy
        change y = 0
        have gy : g y = 0 := hy
        by_cases p : φ y = 0
        · apply s; simpa [val, p] using gy
        · have py := nzOne p
          exfalso
          apply xf
          refine ⟨x - y, ?_, ?_⟩
          · simp [W, mem_ker, px, py]
          · rw [val, py, one_smul] at gy
            dsimp [v] at gy
            rw [map_sub]; abel_nf at gy ⊢; linear_combination (norm := abel) -gy
      have sur := (LinearMap.injective_iff_surjective (f := g)).mp inj
      rw [range_eq_top.mpr sur, finrank_top, finrank_fin_fun]
      exact min_le_left _ _
    · have fh := hz s
      have incl : range f ≤ range g := by
        rintro _ ⟨y, rfl⟩
        refine ⟨y - φ y • h, ?_⟩
        simp [val, map_sub, map_smul, ph, fh]
      have strict : range f < range g := by
        apply lt_of_le_of_ne incl
        intro eq
        have gh : g h = v := by simp [val, fh, ph]
        have vv : v ∈ range f := eq ▸ ⟨h, gh⟩
        have xx : x ∈ range f := by
          convert (range f).add_mem vv (show f x ∈ range f from ⟨x, rfl⟩) using 1
          dsimp [v]; abel
        obtain ⟨y, ey⟩ := xx
        apply xf
        exact ⟨y - φ y • h, by simp [W, mem_ker, ph], by simp [fh, ey]⟩
      have hd := Submodule.finrank_lt_finrank_of_lt strict
      omega

theorem exists_common_compl {r : Nat} :
    ∀ (c d₀ : Nat) (U₁ U₂ : Submodule F (Vect r)),
      finrank F U₁ = d₀ → finrank F U₂ = d₀ → r - d₀ = c →
      ∃ W : Submodule F (Vect r), finrank F W = c ∧ U₁ ⊓ W = ⊥ ∧ U₂ ⊓ W = ⊥ := by
  intro c
  induction c with
  | zero =>
    intro d₀ U₁ U₂ _ _ _
    exact ⟨⊥, finrank_bot F (Vect r), inf_bot_eq U₁, inf_bot_eq U₂⟩
  | succ c ih =>
    intro d₀ U₁ U₂ h1 h2 hc
    have hlt : d₀ < r := by omega
    have hU1_ne : U₁ ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, finrank_fin_fun] at h1
      omega
    have hU2_ne : U₂ ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, finrank_fin_fun] at h2
      omega
    obtain ⟨x, hx1, hx2⟩ := outsideBoth U₁ U₂ hU1_ne hU2_ne
    have hx_ne : x ≠ 0 := fun h0 => hx1 (h0 ▸ Submodule.zero_mem U₁)
    let L : Submodule F (Vect r) := Submodule.span F {x}
    have hLdim : finrank F L = 1 := finrank_span_singleton hx_ne
    have hinf1 : U₁ ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases Submodule.mem_span_singleton.mp hy.2 with ⟨a, rfl⟩
      by_cases ha : a = 0
      · rw [ha, zero_smul]; exact Submodule.zero_mem ⊥
      · exfalso
        have h1a := nzOne ha
        rw [h1a, one_smul] at hy
        exact hx1 hy.1
    have hinf2 : U₂ ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases Submodule.mem_span_singleton.mp hy.2 with ⟨a, rfl⟩
      by_cases ha : a = 0
      · rw [ha, zero_smul]; exact Submodule.zero_mem ⊥
      · exfalso
        have h1a := nzOne ha
        rw [h1a, one_smul] at hy
        exact hx2 hy.1
    have hdim1 : finrank F ↥(U₁ ⊔ L) = d₀ + 1 := by
      have hs := Submodule.finrank_sup_add_finrank_inf_eq U₁ L
      rw [h1, hLdim, hinf1, finrank_bot, add_zero] at hs
      exact hs
    have hdim2 : finrank F ↥(U₂ ⊔ L) = d₀ + 1 := by
      have hs := Submodule.finrank_sup_add_finrank_inf_eq U₂ L
      rw [h2, hLdim, hinf2, finrank_bot, add_zero] at hs
      exact hs
    obtain ⟨W', hW'dim, hW'1, hW'2⟩ := ih (d₀ + 1) (U₁ ⊔ L) (U₂ ⊔ L) hdim1 hdim2 (by omega)
    have hLW' : L ⊓ W' = ⊥ := le_bot_iff.mp ((inf_le_inf_right W' le_sup_right).trans hW'1.le)
    refine ⟨L ⊔ W', ?_, ?_, ?_⟩
    · have hs := Submodule.finrank_sup_add_finrank_inf_eq L W'
      rw [hLdim, hW'dim, hLW', finrank_bot, add_zero] at hs
      omega
    · rw [eq_bot_iff]
      intro y hy
      rcases Submodule.mem_sup.mp hy.2 with ⟨a, ha, b, hb, rfl⟩
      have hb_in : b ∈ (U₁ ⊔ L) ⊓ W' := by
        refine ⟨?_, hb⟩
        have heq : b = (a + b) - a := by abel
        rw [heq]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hy.1) (Submodule.mem_sup_right ha)
      rw [hW'1] at hb_in
      have hb0 : b = 0 := hb_in
      subst hb0
      rw [add_zero] at hy ⊢
      have ha_in : a ∈ U₁ ⊓ L := ⟨hy.1, ha⟩
      rw [hinf1] at ha_in
      exact ha_in
    · rw [eq_bot_iff]
      intro y hy
      rcases Submodule.mem_sup.mp hy.2 with ⟨a, ha, b, hb, rfl⟩
      have hb_in : b ∈ (U₂ ⊔ L) ⊓ W' := by
        refine ⟨?_, hb⟩
        have heq : b = (a + b) - a := by abel
        rw [heq]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hy.1) (Submodule.mem_sup_right ha)
      rw [hW'2] at hb_in
      have hb0 : b = 0 := hb_in
      subst hb0
      rw [add_zero] at hy ⊢
      have ha_in : a ∈ U₂ ⊓ L := ⟨hy.1, ha⟩
      rw [hinf2] at ha_in
      exact ha_in

theorem exists_between_finrank {r : Nat} :
    ∀ (c : Nat) (A B : Submodule F (Vect r)) (d₀ : Nat),
      A ≤ B → finrank F A ≤ d₀ → d₀ ≤ finrank F B → d₀ - finrank F A = c →
      ∃ U : Submodule F (Vect r), A ≤ U ∧ U ≤ B ∧ finrank F U = d₀ := by
  intro c
  induction c with
  | zero =>
    intro A B d₀ hAB h1 h2 hc
    exact ⟨A, le_rfl, hAB, by omega⟩
  | succ c ih =>
    intro A B d₀ hAB h1 h2 hc
    have hlt : finrank F A < finrank F B := by omega
    have hne : A ≠ B := fun heq => by rw [heq] at hlt; omega
    obtain ⟨x, hxB, hxA⟩ : ∃ x ∈ B, x ∉ A := by
      by_contra hall; push Not at hall
      exact hne (le_antisymm hAB hall)
    have hx_ne : x ≠ 0 := fun h0 => hxA (h0 ▸ Submodule.zero_mem A)
    let L : Submodule F (Vect r) := Submodule.span F {x}
    have hinf : A ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rcases Submodule.mem_span_singleton.mp hy.2 with ⟨a, rfl⟩
      by_cases ha : a = 0
      · rw [ha, zero_smul]; exact Submodule.zero_mem ⊥
      · exfalso
        have h1a := nzOne ha
        rw [h1a, one_smul] at hy
        exact hxA hy.1
    have hdim : finrank F ↥(A ⊔ L) = finrank F A + 1 := by
      have hs := Submodule.finrank_sup_add_finrank_inf_eq A L
      rw [finrank_span_singleton hx_ne, hinf, finrank_bot, add_zero] at hs
      exact hs
    have hALB : A ⊔ L ≤ B := sup_le hAB ((Submodule.span_singleton_le_iff_mem x B).mpr hxB)
    obtain ⟨U, hAU, hUB, hUdim⟩ := ih (A ⊔ L) B d₀ hALB (by omega) h2 (by omega)
    exact ⟨U, le_sup_left.trans hAU, hUB, hUdim⟩

theorem isCompl_of_inf_bot_finrank {r : Nat} {U W : Submodule F (Vect r)}
    (hinf : U ⊓ W = ⊥) (hdim : finrank F U + finrank F W = r) : IsCompl U W := by
  refine ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr ?_⟩
  have hs := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hinf, finrank_bot, add_zero] at hs
  have htop : finrank F ↥(U ⊔ W) = finrank F (⊤ : Submodule F (Vect r)) := by
    rw [finrank_top, finrank_fin_fun]; omega
  exact Submodule.eq_top_of_finrank_eq (by rw [finrank_fin_fun]; omega)

end RankRepair

section PanelWalk
open Matrix LinearMap Module Function

theorem repair_one (A : Sq r) : ∃ B : Sq r, (B - A).rank ≤ 1 ∧
    (1 - B).rank ≤ (1 - A).rank - 1 ∧ min r (A.rank + 1) ≤ B.rank := by
  classical
  by_cases eq : A = 1
  · subst A; refine ⟨1, by simp, by simp, by simp⟩
  let f : Endo r := Matrix.toLin' A
  have ne : f ≠ LinearMap.id := by
    intro h; apply eq; simpa [f] using congrArg LinearMap.toMatrix' h
  obtain ⟨g, φ, v, gv, drop, grow⟩ := repair_map f ne
  let B : Sq r := LinearMap.toMatrix' g
  have bg : Matrix.toLin' B = g := Matrix.toLin'_toMatrix' g
  have rank_map (M : Sq r) : M.rank = finrank F (LinearMap.range (Matrix.toLin' M)) := rfl
  have db : (1 - B).rank = finrank F (LinearMap.range (LinearMap.id - g)) := by rw [rank_map, map_sub, Matrix.toLin'_one, bg]
  have da : (1 - A).rank = finrank F (LinearMap.range (LinearMap.id - f)) := by rw [rank_map, map_sub, Matrix.toLin'_one]
  have rb : B.rank = finrank F (LinearMap.range g) := by rw [rank_map, bg]
  have d : B - A = Matrix.vecMulVec v (fun j => φ (Pi.single j 1)) := by
    ext i j
    have h := congrArg (fun (T : Endo r) => T (Pi.single j 1) i) gv
    simp [f, LinearMap.smulRight_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [B, Matrix.sub_apply, LinearMap.toMatrix'_apply, Matrix.vecMulVec_apply]
    rw [h]; ring
  exact ⟨B, d ▸ rank_vecMulVec_le _ _, by rw [db, da]; omega, by rw [rb]; exact grow⟩

noncomputable def repair (A : Sq r) : Sq r := Classical.choose (repair_one A)

theorem after (A : Sq r) (n : Nat) :
    ((repair^[n]) A - A).rank ≤ n ∧ (1 - (repair^[n]) A).rank ≤ (1 - A).rank - n ∧
    min r (A.rank + n) ≤ ((repair^[n]) A).rank := by
  induction n with
  | zero => simp
  | succ n ih =>
    let X := (repair^[n]) A
    have h := Classical.choose_spec (repair_one X)
    change (repair X - X).rank ≤ 1 ∧ (1 - repair X).rank ≤ (1 - X).rank - 1 ∧ min r (X.rank + 1) ≤ (repair X).rank at h
    rw [Function.iterate_succ_apply']
    have d := dist (repair X) X A
    change (X - A).rank ≤ n ∧ (1 - X).rank ≤ _ ∧ _ ≤ X.rank at ih
    change (repair X - A).rank ≤ _ ∧ (1 - repair X).rank ≤ _ ∧ _ ≤ (repair X).rank
    omega

theorem path_data (H : Sq r) (k d e : Nat) (full : r ≤ H.rank + d + e) (cost : (1 - H).rank ≤ (k + 1) * d + e) :
    ∃ S : Fin (k + 2) → Sq r, S 0 = 1 ∧ ((S (Fin.last _)) - H).rank ≤ e ∧
    ∀ j : Fin (k + 1), IsUnit (S j.castSucc) ∧ (S j.castSucc - S j.succ).rank ≤ d := by
  let time := fun (i : Fin (k + 2)) => (k + 1 - i.val) * d + e
  let S := fun i => (repair^[time i]) H
  have tz : time 0 = (k + 1) * d + e := by simp [time]
  have tl : time (Fin.last _) = e := by simp [time]
  have z := (after H (time 0)).2.1
  have rz : (1 - S 0).rank = 0 := by dsimp [S]; rw [tz] at z ⊢; omega
  refine ⟨S, (sub_eq_zero.mp (zeroMat_of_rank_zero rz)).symm, ?_, ?_⟩
  · simpa only [S, tl] using (after H e).1
  · intro j
    have ht : time j.castSucc = d + time j.succ := by
      have := j.isLt
      have ar : k + 1 - j.val = (k + 1 - (j.val + 1)) + 1 := by omega
      simp [time, Fin.val_castSucc, Fin.val_succ, ar, Nat.add_mul]; omega
    have hd : e ≤ time j.succ := by simp [time]
    have gr := (after H (time j.castSucc)).2.2
    have hi : (S j.castSucc).rank = r := by
      have up := rank_le_width (S j.castSucc)
      change min r (H.rank + time j.castSucc) ≤ (S j.castSucc).rank at gr
      omega
    refine ⟨Matrix.mulVec_surjective_iff_isUnit.mp (Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hi)), ?_⟩
    change ((repair^[time j.castSucc]) H - (repair^[time j.succ]) H).rank ≤ d
    rw [ht, Function.iterate_add_apply]; exact (after _ d).1

end PanelWalk

section Sufficiency
open Matrix Submodule Module

theorem frame_step {r d : Nat} {S D : Sq r} (hS : IsUnit S) (jump : (S - D).rank ≤ d)
    (U : Mat r d) : ∃ U' : Mat r d, ∃ X : Sq r, ∃ Y : Mat d r,
      S * X + U * Y = 1 ∧ D * X + U' * Y = 1 := by
  obtain ⟨J, V, h⟩ := factor _ jump
  let F0 := S⁻¹
  have sf : S * F0 = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  let G := F0 * U
  have sg : S * G = U := by rw [show S * G = (S * F0) * U by exact (Matrix.mul_assoc ..).symm, sf, Matrix.one_mul]
  let Y := V * F0
  refine ⟨D * G + J, F0 - G * Y, Y, ?_, ?_⟩
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc, sg, sf]; abel
  · rw [Matrix.mul_sub, Matrix.add_mul, ← Matrix.mul_assoc D G Y]
    have sum : D * F0 + J * Y = 1 := by
      change D * F0 + J * (V * F0) = 1
      rw [← Matrix.mul_assoc, ← Matrix.add_mul, h]
      have hs : D + (S - D) = S := by abel
      rw [hs, sf]
    rw [← sum]; abel

theorem build_frames_parts {k' r s : Nat} (S : Fin (k' + 2) → Sq r)
    (step : ∀ j : Fin (k' + 1), IsUnit (S j.castSucc) ∧ (S j.castSucc - S j.succ).rank ≤ s) :
    ∃ (U : Fin (k' + 2) → Mat r s) (X : Fin (k' + 1) → Sq r) (Y : Fin (k' + 1) → Mat s r),
      U 0 = 0 ∧
      ∀ j : Fin (k' + 1),
        S j.castSucc * X j + U j.castSucc * Y j = 1 ∧
        S j.succ * X j + U j.succ * Y j = 1 := by
  classical
  have opts (j : Fin (k' + 1)) (u : Mat r s) := frame_step (step j).1 (step j).2 u
  let U : Fin (k' + 2) → Mat r s := Fin.induction 0 (fun j u => Classical.choose (opts j u))
  let X : Fin (k' + 1) → Sq r := fun j => Classical.choose (Classical.choose_spec (opts j (U j.castSucc)))
  let Y : Fin (k' + 1) → Mat s r := fun j => Classical.choose (Classical.choose_spec (Classical.choose_spec (opts j (U j.castSucc))))
  refine ⟨U, X, Y, rfl, fun j => ?_⟩
  simpa only [U, Fin.induction_succ, X, Y] using
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (opts j (U j.castSucc))))

theorem lift_M0_to_pathFrames {k r q' s : Nat} (H_ext J_ext : Mat q' r) (M₀ : Sq r)
    (hunit : IsUnit M₀) (hdiff : (H_ext - J_ext * M₀).rank ≤ s) (hstep : (1 - M₀).rank ≤ k * s) :
    PathFrames k r q' (r + s) H_ext J_ext := by
  obtain ⟨U_spare, Y₀, hfac⟩ := factor (H_ext - J_ext * M₀) hdiff
  let equiv : Fin (r + s) ≃ (Fin r ⊕ Fin s) := finSumFinEquiv.symm
  let A_end : Mat q' (r + s) := (Matrix.fromCols J_ext U_spare).submatrix id equiv
  have mul_end (D : Sq r) (Y : Mat s r) :
      A_end * (Matrix.fromRows D Y).submatrix equiv id = J_ext * D + U_spare * Y := by
    simp only [A_end, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.fromCols_mul_fromRows]
  have mul_ab (X : Sq r) (Z : Mat r s) (D : Sq r) (Y : Mat s r) :
      (Matrix.fromCols X Z).submatrix id equiv * (Matrix.fromRows D Y).submatrix equiv id =
        X * D + Z * Y := by
    simp only [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.fromCols_mul_fromRows]
  cases k with
  | zero =>
    have hM0_rank : (1 - M₀).rank = 0 := by simpa using hstep
    have hM0_eq : M₀ = 1 := (sub_eq_zero.mp (zeroMat_of_rank_zero hM0_rank)).symm
    let A : Fin 1 → Mat r (r + s) := fun _ => (Matrix.fromCols (1 : Sq r) (0 : Mat r s)).submatrix id equiv
    let B : Fin 2 → Mat (r + s) r := Fin.cases
      ((Matrix.fromRows (1 : Sq r) Y₀).submatrix equiv id)
      (fun _ => (Matrix.fromRows (1 : Sq r) (0 : Mat s r)).submatrix equiv id)
    refine ⟨A, A_end, B, ?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Fin.ext (by omega)
      subst hi
      have hc0 : (0 : Fin 1).castSucc = 0 := rfl
      have hs0 : (0 : Fin 1).succ = Fin.succ (0 : Fin 1) := rfl
      constructor
      · rw [hc0]; simp only [A, B, Fin.cases_zero, mul_ab, mul_one, Matrix.zero_mul, add_zero]
      · rw [hs0]; simp only [A, B, Fin.cases_succ, mul_ab, mul_one, Matrix.zero_mul, add_zero]
    · simp only [B, Fin.cases_zero, mul_end, hfac, hM0_eq, Matrix.mul_one]
      abel
    · have hlast : Fin.last 1 = (0 : Fin 1).succ := rfl
      rw [hlast]
      simp only [B, Fin.cases_succ, mul_end, Matrix.mul_one, Matrix.mul_zero, add_zero]
  | succ k' =>
    have hM0_det : IsUnit M₀.det := (Matrix.isUnit_iff_isUnit_det M₀).mp hunit
    have hM0t_unit : IsUnit M₀ᵀ :=
      (Matrix.isUnit_iff_isUnit_det M₀ᵀ).mpr (by rw [Matrix.det_transpose]; exact hM0_det)
    have hM0t_rank : (M₀ᵀ).rank = r := by
      have hup := rank_le_width (M₀ᵀ)
      have hlo : r ≤ (M₀ᵀ).rank := by
        have h1 : (M₀ᵀ) * (M₀ᵀ)⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M₀ᵀ).mp hM0t_unit)
        simpa [h1] using rank_mul_le_left (M₀ᵀ) (M₀ᵀ)⁻¹
      omega
    have hcost : (1 - M₀ᵀ).rank ≤ (k' + 1) * s + 0 := by
      have htr : (1 - M₀ᵀ) = (1 - M₀)ᵀ := by simp [Matrix.transpose_sub, Matrix.transpose_one]
      rw [htr, Matrix.rank_transpose]
      simpa using hstep
    have hfull : r ≤ (M₀ᵀ).rank + s + 0 := by omega
    obtain ⟨S', hS'0, hS'last_err, hS'steps⟩ := path_data (M₀ᵀ) k' s 0 hfull hcost
    have hS'last : S' (Fin.last (k' + 1)) = M₀ᵀ := by
      have h0 : (S' (Fin.last (k' + 1)) - M₀ᵀ).rank = 0 := Nat.eq_zero_of_le_zero hS'last_err
      exact sub_eq_zero.mp (zeroMat_of_rank_zero h0)
    obtain ⟨U', X', Y', hU'0, hforms⟩ := build_frames_parts S' hS'steps
    let A_step : Fin (k' + 1) → Mat r (r + s) :=
      fun j => (Matrix.fromCols (X' j)ᵀ (Y' j)ᵀ).submatrix id equiv
    let B_node : Fin (k' + 2) → Mat (r + s) r :=
      fun i => (Matrix.fromRows (S' i)ᵀ (U' i)ᵀ).submatrix equiv id
    have hstep_mul (j : Fin (k' + 1)) :
        A_step j * B_node j.castSucc = 1 ∧ A_step j * B_node j.succ = 1 := by
      have hf := hforms j
      constructor
      · rw [mul_ab]
        have ht := congrArg Matrix.transpose hf.1
        simpa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_one] using ht
      · rw [mul_ab]
        have ht := congrArg Matrix.transpose hf.2
        simpa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_one] using ht
    let B : Fin (k' + 3) → Mat (r + s) r :=
      Fin.cases ((Matrix.fromRows M₀ Y₀).submatrix equiv id) (fun i => B_node i.rev)
    let A : Fin (k' + 2) → Mat r (r + s) :=
      Fin.cases ((Matrix.fromCols M₀⁻¹ (0 : Mat r s)).submatrix id equiv) (fun j => A_step j.rev)
    refine ⟨A, A_end, B, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · constructor
        · have hc : (0 : Fin (k' + 2)).castSucc = 0 := rfl
          rw [hc]
          simp only [A, B, Fin.cases_zero, mul_ab, Matrix.zero_mul, add_zero]
          exact Matrix.nonsing_inv_mul M₀ hM0_det
        · have hs : (0 : Fin (k' + 2)).succ = (0 : Fin (k' + 2)).succ := rfl
          simp only [A, B, Fin.cases_zero, Fin.cases_succ, Fin.rev_zero, B_node, mul_ab,
            Matrix.zero_mul, add_zero, hS'last, Matrix.transpose_transpose]
          exact Matrix.nonsing_inv_mul M₀ hM0_det
      · have h1 : j.succ.castSucc = (j.castSucc).succ := by ext; simp
        have h2 : (j.castSucc).rev = (j.rev).succ := by ext; simp; omega
        have h3 : (j.succ).rev = (j.rev).castSucc := by ext; simp
        constructor
        · rw [h1]
          simp only [A, B, Fin.cases_succ, h2]
          exact (hstep_mul j.rev).2
        · simp only [A, B, Fin.cases_succ, h3]
          exact (hstep_mul j.rev).1
    · simp only [B, Fin.cases_zero, mul_end, hfac]
      abel
    · have hlast : Fin.last (k' + 2) = (Fin.last (k' + 1)).succ := rfl
      rw [hlast]
      simp only [B, Fin.cases_succ, Fin.rev_last, B_node, hS'0, hU'0,
        Matrix.transpose_one, Matrix.transpose_zero, mul_end, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem exists_M0_of_injective {k r q' s : Nat} (H_ext J_ext : Mat q' r)
    (hHr : H_ext.rank = r) (hJr : J_ext.rank = r)
    (hboth : bothRank H_ext J_ext ≤ r + s) (hdist : (H_ext - J_ext).rank ≤ (k + 1) * s) :
    ∃ M₀ : Sq r, IsUnit M₀ ∧ (H_ext - J_ext * M₀).rank ≤ s ∧ (1 - M₀).rank ≤ k * s := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨1, isUnit_one, ?_, by simp⟩
    simpa using hdist
  by_cases hrs : r ≤ s
  · refine ⟨1, isUnit_one, ?_, by simp⟩
    have hle := rank_le_width (H_ext - J_ext)
    simpa using hle.trans hrs
  let h := H_ext.mulVecLin
  let j := J_ext.mulVecLin
  have hh_inj : Function.Injective h := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hrn := LinearMap.finrank_range_add_finrank_ker h
    rw [finrank_fin_fun] at hrn
    change H_ext.rank + finrank F (LinearMap.ker h) = r at hrn
    omega
  have hj_inj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hrn := LinearMap.finrank_range_add_finrank_ker j
    rw [finrank_fin_fun] at hrn
    change J_ext.rank + finrank F (LinearMap.ker j) = r at hrn
    omega
  let E_eq : Submodule F (Vect r) := LinearMap.ker (h - j)
  have hEdim : finrank F E_eq + (H_ext - J_ext).rank = r := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (h - j)
    rw [finrank_fin_fun] at hrn
    have hsub : (H_ext - J_ext).mulVecLin = h - j := mulVecLin_sub_geo H_ext J_ext
    have hr_eq : (H_ext - J_ext).rank = finrank F (LinearMap.range (h - j)) := by
      change finrank F (LinearMap.range (H_ext - J_ext).mulVecLin) = _
      rw [hsub]
    change finrank F (LinearMap.range (h - j)) + finrank F E_eq = r at hrn
    omega
  by_cases hEbig : r - s ≤ finrank F E_eq
  · refine ⟨1, isUnit_one, ?_, by simp⟩
    simpa using (show (H_ext - J_ext).rank ≤ s by omega)
  let W_int : Submodule F (Vect r) := Submodule.comap h (LinearMap.range h ⊓ LinearMap.range j)
  have hEW : E_eq ≤ W_int := by
    intro x hx
    have heq : h x = j x := sub_eq_zero.mp (LinearMap.mem_ker.mp hx)
    exact ⟨⟨x, rfl⟩, heq ▸ ⟨x, rfl⟩⟩
  have hW_map : W_int.map h = LinearMap.range h ⊓ LinearMap.range j := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · intro y hy
      rcases hy.1 with ⟨x, rfl⟩
      exact ⟨x, hy, rfl⟩
  have hWdim : finrank F W_int = finrank F ↥(LinearMap.range h ⊓ LinearMap.range j) := by
    rw [← hW_map]
    let eW : W_int ≃ₗ[F] W_int.map h :=
      LinearEquiv.ofBijective
        (LinearMap.codRestrict (W_int.map h) (h.comp W_int.subtype) (fun x => ⟨x.1, x.2, rfl⟩))
        ⟨fun a b hab => Subtype.ext (hh_inj (congrArg Subtype.val hab)),
         fun ⟨y, x, hx, hy⟩ => ⟨⟨x, hx⟩, Subtype.ext hy⟩⟩
    exact eW.finrank_eq
  have hWge : r - s ≤ finrank F W_int := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range h) (LinearMap.range j)
    have hboth' : finrank F ↥(LinearMap.range h ⊔ LinearMap.range j) ≤ r + s := by
      rw [bothRank, rank_elim_eq_finrank_sup] at hboth
      exact hboth
    change finrank F ↥(LinearMap.range h ⊔ LinearMap.range j) +
      finrank F ↥(LinearMap.range h ⊓ LinearMap.range j) = H_ext.rank + J_ext.rank at hsup
    omega
  obtain ⟨U₁, hEU, hU1W, hU1dim⟩ :=
    exists_between_finrank ((r - s) - finrank F E_eq) E_eq W_int (r - s) hEW (by omega) hWge rfl
  let j_equiv : Vect r ≃ₗ[F] LinearMap.range j := LinearEquiv.ofInjective j hj_inj
  let φ₀ : U₁ →ₗ[F] Vect r :=
    j_equiv.symm.toLinearMap.comp
      (LinearMap.codRestrict (LinearMap.range j) (h.comp U₁.subtype) (fun u => (hU1W u.2).2))
  have hφ_j (u : U₁) : j (φ₀ u) = h u.1 := by
    have h1 := j_equiv.apply_symm_apply ⟨h u.1, (hU1W u.2).2⟩
    exact congrArg Subtype.val h1
  have hφ_inj : Function.Injective φ₀ := by
    intro a b hab
    apply Subtype.ext
    apply hh_inj
    rw [← hφ_j a, ← hφ_j b, hab]
  have hφ_fix : ∀ (u : Vect r) (hu : u ∈ E_eq), φ₀ ⟨u, hEU hu⟩ = u := by
    intro u hu
    apply hj_inj
    rw [hφ_j]
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp hu)
  let U₂ : Submodule F (Vect r) := LinearMap.range φ₀
  have hU2dim : finrank F U₂ = r - s := by
    have h1 := LinearMap.finrank_range_of_inj hφ_inj
    rw [hU1dim] at h1
    exact h1
  obtain ⟨C_comp, hCdim, hU1C, hU2C⟩ :=
    exists_common_compl (r - (r - s)) (r - s) U₁ U₂ hU1dim hU2dim rfl
  have hCdim_s : finrank F C_comp = s := by omega
  have hcompl1 : IsCompl U₁ C_comp := isCompl_of_inf_bot_finrank hU1C (by omega)
  let p1 : Vect r →ₗ[F] U₁ := Submodule.projectionOnto U₁ C_comp hcompl1
  let q1 : Vect r →ₗ[F] C_comp := Submodule.projectionOnto C_comp U₁ hcompl1.symm
  have hpq (v : Vect r) : (p1 v).1 + (q1 v).1 = v := by
    have hmem : v ∈ U₁ ⊔ C_comp := by rw [hcompl1.sup_eq_top]; exact Submodule.mem_top
    rcases Submodule.mem_sup.mp hmem with ⟨u, hu, c, hc, rfl⟩
    have hp : p1 (u + c) = ⟨u, hu⟩ := by
      rw [map_add, Submodule.projectionOnto_apply_left hcompl1 ⟨u, hu⟩,
        Submodule.projectionOnto_apply_right hcompl1 ⟨c, hc⟩, add_zero]
    have hq : q1 (u + c) = ⟨c, hc⟩ := by
      rw [map_add, Submodule.projectionOnto_apply_right hcompl1.symm ⟨u, hu⟩,
        Submodule.projectionOnto_apply_left hcompl1.symm ⟨c, hc⟩, zero_add]
    rw [hp, hq]
  let m₀ : Endo r := φ₀.comp p1 + C_comp.subtype.comp q1
  have hm₀_U1 (u : Vect r) (hu : u ∈ U₁) : m₀ u = φ₀ ⟨u, hu⟩ := by
    change φ₀ (p1 u) + (q1 u).1 = φ₀ ⟨u, hu⟩
    rw [Submodule.projectionOnto_apply_left hcompl1 ⟨u, hu⟩,
      Submodule.projectionOnto_apply_right hcompl1.symm ⟨u, hu⟩]
    simp
  have hm₀_C (c : Vect r) (hc : c ∈ C_comp) : m₀ c = c := by
    change φ₀ (p1 c) + (q1 c).1 = c
    rw [Submodule.projectionOnto_apply_right hcompl1 ⟨c, hc⟩,
      Submodule.projectionOnto_apply_left hcompl1.symm ⟨c, hc⟩]
    simp
  have hm₀_inj : Function.Injective m₀ := by
    apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro v hv
    have hmv : φ₀ (p1 v) + (q1 v).1 = 0 := hv
    have hmem : φ₀ (p1 v) ∈ U₂ ⊓ C_comp := by
      refine ⟨⟨p1 v, rfl⟩, ?_⟩
      have heq : φ₀ (p1 v) = -(q1 v).1 := eq_neg_of_add_eq_zero_left hmv
      rw [heq]
      exact Submodule.neg_mem C_comp (q1 v).2
    rw [hU2C] at hmem
    have hφ0 : φ₀ (p1 v) = 0 := hmem
    have hp0 : p1 v = 0 := hφ_inj (by rw [hφ0, map_zero])
    have hq0 : (q1 v).1 = 0 := by rw [hφ0, zero_add] at hmv; exact hmv
    have hv0 : v = 0 := by
      rw [← hpq v, hp0, hq0]
      simp
    exact hv0
  let M₀ : Sq r := LinearMap.toMatrix' m₀
  have hM0_lin : M₀.mulVecLin = m₀ := Matrix.toLin'_toMatrix' m₀
  have hM0_unit : IsUnit M₀ := by
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    have hsur := (LinearMap.injective_iff_surjective (f := m₀)).mp hm₀_inj
    intro y
    obtain ⟨x, hx⟩ := hsur y
    exact ⟨x, by change M₀.mulVecLin x = y; rw [hM0_lin]; exact hx⟩
  have hdiff_M0 : (H_ext - J_ext * M₀).rank ≤ s := by
    have hsub_lin : (H_ext - J_ext * M₀).mulVecLin = h - j.comp m₀ := by
      rw [mulVecLin_sub_geo, Matrix.mulVecLin_mul, hM0_lin]
    have hU1_ker : U₁ ≤ LinearMap.ker (h - j.comp m₀) := by
      intro u hu
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, hm₀_U1 u hu, hφ_j ⟨u, hu⟩, sub_self]
    have hker_ge := Submodule.finrank_mono hU1_ker
    have hrn := LinearMap.finrank_range_add_finrank_ker (h - j.comp m₀)
    rw [finrank_fin_fun] at hrn
    change finrank F (LinearMap.range (H_ext - J_ext * M₀).mulVecLin) ≤ s
    rw [hsub_lin]
    have h1 : finrank F (LinearMap.range (h - j.comp m₀)) + finrank F (LinearMap.ker (h - j.comp m₀)) = r := hrn
    have h2 : r - s ≤ finrank F (LinearMap.ker (h - j.comp m₀)) := hU1dim ▸ hker_ge
    omega
  have hstep_M0 : (1 - M₀).rank ≤ k * s := by
    have hsub_lin : (1 - M₀).mulVecLin = LinearMap.id - m₀ := by
      rw [mulVecLin_sub_geo, Matrix.mulVecLin_one, hM0_lin]
    have hEC_ker : E_eq ⊔ C_comp ≤ LinearMap.ker (LinearMap.id - m₀) := by
      refine sup_le ?_ ?_
      · intro u hu
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hm₀_U1 u (hEU hu), hφ_fix u hu, sub_self]
      · intro c hc
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hm₀_C c hc, sub_self]
    have hEC_inf : E_eq ⊓ C_comp = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right C_comp hEU).trans hU1C.le)
    have hEC_dim : finrank F ↥(E_eq ⊔ C_comp) = finrank F E_eq + s := by
      have hs := Submodule.finrank_sup_add_finrank_inf_eq E_eq C_comp
      rw [hEC_inf, finrank_bot, add_zero, hCdim_s] at hs
      exact hs
    have hker_ge := Submodule.finrank_mono hEC_ker
    have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - m₀)
    rw [finrank_fin_fun] at hrn
    change finrank F (LinearMap.range (1 - M₀).mulVecLin) ≤ k * s
    rw [hsub_lin]
    have h1 : finrank F (LinearMap.range (LinearMap.id - m₀)) + finrank F (LinearMap.ker (LinearMap.id - m₀)) = r := hrn
    have h2 : finrank F E_eq + s ≤ finrank F (LinearMap.ker (LinearMap.id - m₀)) := hEC_dim ▸ hker_ge
    have h3 : finrank F E_eq + (H_ext - J_ext).rank = r := hEdim
    have h4 : (H_ext - J_ext).rank ≤ k * s + s := by rwa [Nat.add_mul, one_mul] at hdist
    have h5 : finrank F (LinearMap.range (LinearMap.id - m₀)) ≤ k * s := by omega
    exact h5
  exact ⟨M₀, hM0_unit, hdiff_M0, hstep_M0⟩

theorem pathFrames_of_clean {k r q s : Nat} (H' J : Mat q r)
    (hbH : bothRank H' J ≤ H'.rank + s) (hbJ : bothRank H' J ≤ J.rank + s)
    (hdist : (H' - J).rank ≤ (k + 1) * s) :
    PathFrames k r q (r + s) H' J := by
  let K_H : Submodule F (Vect r) := LinearMap.ker H'.mulVecLin
  let K_J : Submodule F (Vect r) := LinearMap.ker J.mulVecLin
  have hKH_dim : H'.rank + finrank F K_H = r := by
    have hrn := LinearMap.finrank_range_add_finrank_ker H'.mulVecLin
    rw [finrank_fin_fun] at hrn
    exact hrn
  have hKJ_dim : J.rank + finrank F K_J = r := by
    have hrn := LinearMap.finrank_range_add_finrank_ker J.mulVecLin
    rw [finrank_fin_fun] at hrn
    exact hrn
  let d_max := max (finrank F K_H) (finrank F K_J)
  have hd_le_r : d_max ≤ r := max_le (by omega) (by omega)
  have htop_dim : finrank F (⊤ : Submodule F (Vect r)) = r := by rw [finrank_top, finrank_fin_fun]
  obtain ⟨K'_H, hKH_le, _, hK'H_dim⟩ :=
    exists_between_finrank (d_max - finrank F K_H) K_H ⊤ d_max le_top (le_max_left _ _) (by omega) rfl
  obtain ⟨K'_J, hKJ_le, _, hK'J_dim⟩ :=
    exists_between_finrank (d_max - finrank F K_J) K_J ⊤ d_max le_top (le_max_right _ _) (by omega) rfl
  obtain ⟨W_comp, hW_dim, hHW_inf, hJW_inf⟩ :=
    exists_common_compl (r - d_max) d_max K'_H K'_J hK'H_dim hK'J_dim rfl
  have hcompl : IsCompl K'_H W_comp := isCompl_of_inf_bot_finrank hHW_inf (by omega)
  let π_pad : Endo r := K'_H.subtype.comp (Submodule.projectionOnto K'_H W_comp hcompl)
  have hπ_ker : LinearMap.ker π_pad = W_comp := by
    ext v
    simp only [π_pad, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      ZeroMemClass.coe_eq_zero]
    rw [Submodule.projectionOnto_apply_eq_zero_iff hcompl]
  have hπ_range : LinearMap.range π_pad = K'_H := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩; exact (Submodule.projectionOnto K'_H W_comp hcompl v).2
    · intro x hx
      refine ⟨x, ?_⟩
      change (Submodule.projectionOnto K'_H W_comp hcompl x).1 = x
      rw [Submodule.projectionOnto_apply_left hcompl ⟨x, hx⟩]
  let C_pad : Sq r := LinearMap.toMatrix' π_pad
  have hC_lin : C_pad.mulVecLin = π_pad := Matrix.toLin'_toMatrix' π_pad
  have hC_rank : C_pad.rank = d_max := by
    change finrank F (LinearMap.range C_pad.mulVecLin) = d_max
    rw [hC_lin, hπ_range, hK'H_dim]
  let H_ext : Mat (q + r) r := (Matrix.fromRows H' C_pad).submatrix finSumFinEquiv.symm id
  let J_ext : Mat (q + r) r := (Matrix.fromRows J C_pad).submatrix finSumFinEquiv.symm id
  have hHext_top (a : Fin q) (b : Fin r) : H_ext (finSumFinEquiv (Sum.inl a)) b = H' a b := by
    simp [H_ext]
  have hHext_bot (a : Fin r) (b : Fin r) : H_ext (finSumFinEquiv (Sum.inr a)) b = C_pad a b := by
    simp [H_ext]
  have hJext_top (a : Fin q) (b : Fin r) : J_ext (finSumFinEquiv (Sum.inl a)) b = J a b := by
    simp [J_ext]
  have hJext_bot (a : Fin r) (b : Fin r) : J_ext (finSumFinEquiv (Sum.inr a)) b = C_pad a b := by
    simp [J_ext]
  have hHext_rank : H_ext.rank = r := by
    have hker : LinearMap.ker H_ext.mulVecLin = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h1 : v ∈ K_H := by
        rw [LinearMap.mem_ker]
        funext a
        have hrow : (H_ext.mulVecLin v) (finSumFinEquiv (Sum.inl a)) = 0 :=
          congrFun hv (finSumFinEquiv (Sum.inl a))
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hHext_top] at hrow
        exact hrow
      have h2 : v ∈ W_comp := by
        rw [← hπ_ker, LinearMap.mem_ker, ← hC_lin]
        funext a
        have hrow : (H_ext.mulVecLin v) (finSumFinEquiv (Sum.inr a)) = 0 :=
          congrFun hv (finSumFinEquiv (Sum.inr a))
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hHext_bot] at hrow
        exact hrow
      have hmem : v ∈ K'_H ⊓ W_comp := ⟨hKH_le h1, h2⟩
      rw [hHW_inf] at hmem
      exact hmem
    have hrn := LinearMap.finrank_range_add_finrank_ker H_ext.mulVecLin
    rw [hker, finrank_bot, add_zero, finrank_fin_fun] at hrn
    exact hrn
  have hJext_rank : J_ext.rank = r := by
    have hker : LinearMap.ker J_ext.mulVecLin = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h1 : v ∈ K_J := by
        rw [LinearMap.mem_ker]
        funext a
        have hrow : (J_ext.mulVecLin v) (finSumFinEquiv (Sum.inl a)) = 0 :=
          congrFun hv (finSumFinEquiv (Sum.inl a))
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hJext_top] at hrow
        exact hrow
      have h2 : v ∈ W_comp := by
        rw [← hπ_ker, LinearMap.mem_ker, ← hC_lin]
        funext a
        have hrow : (J_ext.mulVecLin v) (finSumFinEquiv (Sum.inr a)) = 0 :=
          congrFun hv (finSumFinEquiv (Sum.inr a))
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hJext_bot] at hrow
        exact hrow
      have hmem : v ∈ K'_J ⊓ W_comp := ⟨hKJ_le h1, h2⟩
      rw [hJW_inf] at hmem
      exact hmem
    have hrn := LinearMap.finrank_range_add_finrank_ker J_ext.mulVecLin
    rw [hker, finrank_bot, add_zero, finrank_fin_fun] at hrn
    exact hrn
  let embedTop : (Fin q → F) →ₗ[F] (Fin (q + r) → F) :=
    { toFun := fun v i => Sum.elim v (fun _ => 0) (finSumFinEquiv.symm i)
      map_add' := fun x y => by
        funext i
        change Sum.elim (x + y) (fun _ => 0) (finSumFinEquiv.symm i) =
          Sum.elim x (fun _ => 0) (finSumFinEquiv.symm i) +
          Sum.elim y (fun _ => 0) (finSumFinEquiv.symm i)
        generalize finSumFinEquiv.symm i = z
        cases z <;> simp
      map_smul' := fun c x => by
        funext i
        change Sum.elim (c • x) (fun _ => 0) (finSumFinEquiv.symm i) =
          c • Sum.elim x (fun _ => 0) (finSumFinEquiv.symm i)
        generalize finSumFinEquiv.symm i = z
        cases z <;> simp }
  let embedBot : (Fin r → F) →ₗ[F] (Fin (q + r) → F) :=
    { toFun := fun v i => Sum.elim (fun _ => 0) v (finSumFinEquiv.symm i)
      map_add' := fun x y => by
        funext i
        change Sum.elim (fun _ => 0) (x + y) (finSumFinEquiv.symm i) =
          Sum.elim (fun _ => 0) x (finSumFinEquiv.symm i) +
          Sum.elim (fun _ => 0) y (finSumFinEquiv.symm i)
        generalize finSumFinEquiv.symm i = z
        cases z <;> simp
      map_smul' := fun c x => by
        funext i
        change Sum.elim (fun _ => 0) (c • x) (finSumFinEquiv.symm i) =
          c • Sum.elim (fun _ => 0) x (finSumFinEquiv.symm i)
        generalize finSumFinEquiv.symm i = z
        cases z <;> simp }
  have hdiff_ext : (H_ext - J_ext).rank ≤ (k + 1) * s := by
    have hfac_diff : (H_ext - J_ext).mulVecLin = embedTop.comp (H' - J).mulVecLin := by
      apply LinearMap.ext; intro v; funext i
      have hi := finSumFinEquiv.apply_symm_apply i
      rw [← hi]
      cases hsym : finSumFinEquiv.symm i with
      | inl a =>
        simp only [embedTop, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          Equiv.symm_apply_apply, Sum.elim_inl, Matrix.mulVecLin_apply, Matrix.mulVec,
          dotProduct, Matrix.sub_apply, hHext_top, hJext_top]
      | inr a =>
        simp only [embedTop, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
          Equiv.symm_apply_apply, Sum.elim_inr, Matrix.mulVecLin_apply, Matrix.mulVec,
          dotProduct, Matrix.sub_apply, hHext_bot, hJext_bot, sub_self, zero_mul,
          Finset.sum_const_zero]
    change finrank F (LinearMap.range (H_ext - J_ext).mulVecLin) ≤ (k + 1) * s
    rw [hfac_diff, LinearMap.range_comp]
    exact (Submodule.finrank_map_le embedTop _).trans hdist
  have hboth_ext : bothRank H_ext J_ext ≤ r + s := by
    let M_ext : Matrix (Fin (q + r)) (Fin r ⊕ Fin r) F := fun i z => Sum.elim (H_ext i) (J_ext i) z
    let M_HJ : Matrix (Fin q) (Fin r ⊕ Fin r) F := fun a z => Sum.elim (H' a) (J a) z
    let sumPair : (Fin r ⊕ Fin r → F) →ₗ[F] (Fin r → F) :=
      { toFun := fun w b => w (Sum.inl b) + w (Sum.inr b)
        map_add' := fun x y => by funext b; simp; abel
        map_smul' := fun c x => by funext b; simp [mul_add] }
    have hM_split : M_ext.mulVecLin =
        embedTop.comp M_HJ.mulVecLin + embedBot.comp (C_pad.mulVecLin.comp sumPair) := by
      apply LinearMap.ext; intro w; funext i
      have hi := finSumFinEquiv.apply_symm_apply i
      rw [← hi]
      cases hsym : finSumFinEquiv.symm i with
      | inl a =>
        simp only [embedTop, embedBot, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Equiv.symm_apply_apply,
          Sum.elim_inl, add_zero, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun z _ => ?_
        cases z with
        | inl b => simp only [M_ext, M_HJ, Sum.elim_inl, hHext_top]
        | inr b => simp only [M_ext, M_HJ, Sum.elim_inr, hJext_top]
      | inr a =>
        simp only [embedTop, embedBot, sumPair, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Equiv.symm_apply_apply,
          Sum.elim_inr, zero_add, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [M_ext, Sum.elim_inl, Sum.elim_inr, hHext_bot, hJext_bot]
        ring
    have hrange_le : LinearMap.range M_ext.mulVecLin ≤
        LinearMap.range (embedTop.comp M_HJ.mulVecLin) ⊔
        LinearMap.range (embedBot.comp (C_pad.mulVecLin.comp sumPair)) := by
      rintro y ⟨w, rfl⟩
      rw [hM_split, LinearMap.add_apply]
      exact Submodule.add_mem_sup ⟨w, rfl⟩ ⟨w, rfl⟩
    have h1 : finrank F (LinearMap.range (embedTop.comp M_HJ.mulVecLin)) ≤ bothRank H' J := by
      rw [LinearMap.range_comp]
      exact Submodule.finrank_map_le embedTop _
    have h2 : finrank F (LinearMap.range (embedBot.comp (C_pad.mulVecLin.comp sumPair))) ≤ d_max := by
      rw [LinearMap.range_comp]
      refine (Submodule.finrank_map_le embedBot _).trans ?_
      have hsub : LinearMap.range (C_pad.mulVecLin.comp sumPair) ≤ LinearMap.range C_pad.mulVecLin :=
        LinearMap.range_comp_le_range _ _
      exact (Submodule.finrank_mono hsub).trans (le_of_eq hC_rank)
    have hmono : finrank F (LinearMap.range M_ext.mulVecLin) ≤
        finrank F ↥(LinearMap.range (embedTop.comp M_HJ.mulVecLin) ⊔
          LinearMap.range (embedBot.comp (C_pad.mulVecLin.comp sumPair))) :=
      Submodule.finrank_mono hrange_le
    have hsup : finrank F ↥(LinearMap.range (embedTop.comp M_HJ.mulVecLin) ⊔
          LinearMap.range (embedBot.comp (C_pad.mulVecLin.comp sumPair))) +
        finrank F ↥(LinearMap.range (embedTop.comp M_HJ.mulVecLin) ⊓
          LinearMap.range (embedBot.comp (C_pad.mulVecLin.comp sumPair))) =
        finrank F (LinearMap.range (embedTop.comp M_HJ.mulVecLin)) +
        finrank F (LinearMap.range (embedBot.comp (C_pad.mulVecLin.comp sumPair))) :=
      Submodule.finrank_sup_add_finrank_inf_eq _ _
    change finrank F (LinearMap.range M_ext.mulVecLin) ≤ r + s
    have hd_max_cases : bothRank H' J + d_max ≤ r + s := by
      dsimp only [d_max]
      rcases le_total (finrank F K_H) (finrank F K_J) with hle | hle
      · rw [max_eq_right hle]; omega
      · rw [max_eq_left hle]; omega
    omega
  obtain ⟨M₀, hM0_unit, hM0_diff, hM0_step⟩ :=
    exists_M0_of_injective H_ext J_ext hHext_rank hJext_rank hboth_ext hdiff_ext
  obtain ⟨A, A_end_ext, B, hAB, h0, hL⟩ :=
    lift_M0_to_pathFrames H_ext J_ext M₀ hM0_unit hM0_diff hM0_step
  let A_end : Mat q (r + s) := fun a h => A_end_ext (finSumFinEquiv (Sum.inl a)) h
  refine ⟨A, A_end, B, hAB, ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun h0 (finSumFinEquiv (Sum.inl a))) b
    simp only [Matrix.mul_apply, hHext_top] at h
    exact h
  · ext a b
    have h := congrFun (congrFun hL (finSumFinEquiv (Sum.inl a))) b
    simp only [Matrix.mul_apply, hJext_top] at h
    exact h

theorem rank_budget {k r q w e : Nat} (H J : Mat q r) :
    (∃ H' : Mat q r, PathFrames k r q w H' J ∧ (H' - H).rank ≤ e) ↔
    r ≤ w ∧ bothRank H J ≤ H.rank + (w - r) + e ∧ bothRank H J ≤ J.rank + (w - r) + e ∧
      (H - J).rank ≤ (k + 1) * (w - r) + e := by
  constructor
  · rintro ⟨H', hf, herr⟩
    exact necessary_with_err hf herr
  · rintro ⟨hrw, hbH, hbJ, hdist⟩
    let s := w - r
    let d := (H - J).rank
    obtain ⟨P, hP0, hPlast, hPdist, hPdef⟩ := path_exists_aux d H J rfl
    let i₀ : Fin (d + 1) := ⟨min e d, Nat.lt_succ_of_le (Nat.min_le_right e d)⟩
    let H' := P i₀
    have hH'H : (H' - H).rank ≤ e := by
      have h0i := hPdist 0 i₀ (Fin.zero_le i₀)
      rw [hP0] at h0i
      rw [sub_comm_F]
      change (H - P i₀).rank ≤ e
      rw [h0i]
      simp only [Fin.val_zero, Nat.sub_zero, i₀]
      exact Nat.min_le_left e d
    have hH'J : (H' - J).rank ≤ (k + 1) * s := by
      have hil := hPdist i₀ (Fin.last d) (Fin.le_last i₀)
      rw [hPlast] at hil
      change (P i₀ - J).rank ≤ (k + 1) * s
      rw [hil]
      simp only [Fin.val_last, i₀]
      have hd_le : d ≤ (k + 1) * s + e := hdist
      omega
    have hcleanH : bothRank H' J ≤ H'.rank + s := by
      by_cases hed : e ≤ d
      · have hi0_val : i₀.val = e := Nat.min_eq_left hed
        have h1 := (hPdef i₀).1
        dsimp only at h1
        change bothRank H' J - H'.rank = bothRank H J - H.rank - i₀.val at h1
        rw [hi0_val] at h1
        dsimp only [s]
        omega
      · have hi0_eq : i₀ = Fin.last d := Fin.ext (Nat.min_eq_right (le_of_lt (not_le.mp hed)))
        have hH'eq : H' = J := by dsimp only [H']; rw [hi0_eq, hPlast]
        rw [hH'eq, bothRank, rank_elim_eq_finrank_sup, sup_idem]
        change J.rank ≤ J.rank + s
        omega
    have hcleanJ : bothRank H' J ≤ J.rank + s := by
      by_cases hed : e ≤ d
      · have hi0_val : i₀.val = e := Nat.min_eq_left hed
        have h2 := (hPdef i₀).2
        dsimp only at h2
        change bothRank H' J - J.rank = bothRank H J - J.rank - i₀.val at h2
        rw [hi0_val] at h2
        dsimp only [s]
        omega
      · have hi0_eq : i₀ = Fin.last d := Fin.ext (Nat.min_eq_right (le_of_lt (not_le.mp hed)))
        have hH'eq : H' = J := by dsimp only [H']; rw [hi0_eq, hPlast]
        rw [hH'eq, bothRank, rank_elim_eq_finrank_sup, sup_idem]
        change J.rank ≤ J.rank + s
        omega
    have hpf := pathFrames_of_clean H' J hcleanH hcleanJ hH'J
    have hrw_eq : r + s = w := Nat.add_sub_of_le hrw
    exact ⟨H', hrw_eq ▸ hpf, hH'H⟩

end Sufficiency

end PEqualNP.Outside.L_meta_33633_aux

open PEqualNP.Outside.L_meta_33633_aux

theorem PEqualNP.Outside.L_meta_33633 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (n m k r q t e : ℕ) (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let I := Fin (k+1)
  let V := Fin (k+2)
  let M := Matrix (Fin r) (Fin r) (ZMod 2)
  let Z := Matrix (Fin q) (Fin r) (ZMod 2)
  let last : V := Fin.last (k+1)
  ∀ (rows : ((I × Fin r) ⊕ Fin q) ↪ Fin n) (cols : V × Fin r ↪ Fin m)
    (_ : ∀ z, rows z ≠ u) (_ : ∀ z, cols z ≠ v) (L : I → M) (R : V → M) (H J : Z),
    let bit := fun (P : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) =>
      ((P i j).toNat : ZMod 2) + ((P u j).toNat : ZMod 2) +
        ((P i v).toNat : ZMod 2) + ((P u v).toNat : ZMod 2)
    let block := fun (P : Fin n → Fin m → Bool) (i : I) (j : V) =>
      (fun a b => bit P (rows (Sum.inl (i,a))) (cols (j,b)) : M)
    let ends := fun (P : Fin n → Fin m → Bool) (j : V) =>
      (fun a b => bit P (rows (Sum.inr a)) (cols (j,b)) : Z)
    let both := Matrix.rank (fun i z => Sum.elim (H i) (J i) z :
      Matrix (Fin q) (Fin r ⊕ Fin r) (ZMod 2))
    (∀ i, IsUnit (L i)) → (∀ j, IsUnit (R j)) →
    (∀ i, block T i i.castSucc = L i * R i.castSucc ∧ block T i i.succ = L i * R i.succ) →
    ends T 0 = H * R 0 → ends T last = J * R last →
    ((∃ (P : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
      PEqualNP.Represents.Represents P C ∧ depth (n+m) C ≤ 1 ∧ C.gates.countP nonlinear ≤ t ∧
      (∀ i, P i v = T i v) ∧ (∀ j, P u j = T u j) ∧
      (∀ i, block P i i.castSucc = block T i i.castSucc ∧ block P i i.succ = block T i i.succ) ∧
      ends P last = ends T last ∧
      ∃ X : Fin e → Finset (Fin q), ∃ Y : Fin e → Finset (Fin r), ∀ a b,
        xor (P (rows (Sum.inr a)) (cols (0,b))) (T (rows (Sum.inr a)) (cols (0,b))) =
          decide ((Finset.univ.filter (fun h : Fin e => a ∈ X h ∧ b ∈ Y h)).card % 2 = 1)) ↔
      r ≤ 2*t ∧ both ≤ Matrix.rank H + (2*t-r) + e ∧ both ≤ Matrix.rank J + (2*t-r) + e ∧
        Matrix.rank (H-J) ≤ (k+1)*(2*t-r)+e)) := by
  intro nonlinear depth n m k r q t e T u v I V M Z last rows cols ru cv L R H J
    bitF blockF endsF bothF hL hR hblk hend0 hendL
  dsimp only [bothF]
  change (_ ↔ r ≤ 2 * t ∧ bothRank H J ≤ H.rank + (2 * t - r) + e ∧
    bothRank H J ≤ J.rank + (2 * t - r) + e ∧ (H - J).rank ≤ (k + 1) * (2 * t - r) + e)
  rw [← rank_budget (k := k) (w := 2 * t) (e := e) H J,
      ← panel_iff rows cols u v ru cv T L R H J hL hR hblk hend0 hendL]
  constructor
  · rintro ⟨P, C, fan, back, rep, dep, count, col, row, pbl, pel, err⟩
    exact ⟨P, (criterion P u v t).mpr ⟨C, ⟨fan, back, rep⟩, dep, count⟩, col, row, pbl, pel, err⟩
  · rintro ⟨P, rank, col, row, pbl, pel, err⟩
    obtain ⟨C, ⟨fan, back, rep⟩, dep, count⟩ := (criterion P u v t).mp rank
    exact ⟨P, C, fan, back, rep, dep, count, col, row, pbl, pel, err⟩
