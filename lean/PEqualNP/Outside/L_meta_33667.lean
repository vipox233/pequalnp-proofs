import PEqualNP.Defs
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace PEqualNP.Outside.L_meta_33667

namespace Gates
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
end Gates

namespace Spectrum

open scoped BigOperators

abbrev F2 := ZMod 2

def chi (x : F2) : ℤ := if x = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := by decide

lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  revert x y; decide

private def orth {a : ℕ} (U : Submodule F2 (Fin a → F2)) : Submodule F2 (Fin a → F2) :=
  { carrier := {v | ∀ u ∈ U, dotProduct v u = 0},
    zero_mem' := fun u _ => by simp [dotProduct], add_mem' := fun {v w} hv hw u hu => by
      simp only [Set.mem_ofPred_eq] at hv hw ⊢
      rw [add_dotProduct, hv u hu, hw u hu, zero_add],
    smul_mem' := fun c {v} hv u hu => by
      simp only [Set.mem_ofPred_eq] at hv ⊢
      rw [smul_dotProduct, hv u hu, smul_zero] }

private lemma finrank_orth_add {a : ℕ} (U : Submodule F2 (Fin a → F2)) :
    Module.finrank F2 (orth U) + Module.finrank F2 U = a := by
  classical
  let d := Module.finrank F2 U
  let b : Module.Basis (Fin d) F2 U := Module.finBasis F2 U
  let ev : (Fin a → F2) →ₗ[F2] (Fin d → F2) :=
    { toFun := fun v j => dotProduct v (b j).1
      map_add' := fun v w => by funext j; exact add_dotProduct v w (b j).1
      map_smul' := fun c v => by funext j; exact smul_dotProduct c v (b j).1 }
  have hker : LinearMap.ker ev = orth U := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv u hu
      have hu_eq : ∑ j : Fin d, b.repr ⟨u, hu⟩ j • (b j).1 = u := by
        have h1 := congr_arg Subtype.val (b.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at h1
        exact h1
      rw [← hu_eq, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro j _
      have h0 : dotProduct v (b j).1 = 0 := congr_fun hv j
      rw [dotProduct_smul, h0, smul_zero]
    · intro hv
      funext j
      exact hv (b j).1 (b j).2
  have hsurj : Function.Surjective ev := by
    by_contra hns
    have hne : LinearMap.range ev ≠ ⊤ := fun htop => hns (LinearMap.range_eq_top.mp htop)
    have hdim_lt : Module.finrank F2 (LinearMap.range ev) < d := by
      calc Module.finrank F2 (LinearMap.range ev)
          < Module.finrank F2 (Fin d → F2) := Submodule.finrank_lt hne
        _ = d := Module.finrank_fin_fun F2
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range ev)
    have hW_pos : 0 < Module.finrank F2 W := by
      have hmod := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ev) W
      rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero,
        Module.finrank_fin_fun F2] at hmod
      omega
    have hW_ne : W ≠ ⊥ := fun hbot => by rw [hbot, finrank_bot] at hW_pos; omega
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne
    let pW : (Fin d → F2) →ₗ[F2] W := Submodule.projectionOnto W (LinearMap.range ev) hW.symm
    let bw := Module.finBasis F2 W
    have hex_i : ∃ i, bw.repr ⟨w, hwW⟩ i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hw0
      have h1 := congr_arg Subtype.val (bw.sum_repr ⟨w, hwW⟩)
      simp only [hall, zero_smul, Finset.sum_const_zero] at h1
      exact h1.symm
    rcases hex_i with ⟨i0, hi0⟩
    let φ : (Fin d → F2) →ₗ[F2] F2 := (bw.coord i0).comp pW
    let c : Fin d → F2 := fun j => φ (Pi.single j 1)
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hφw : φ w = bw.repr ⟨w, hwW⟩ i0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_left hW.symm ⟨w, hwW⟩]
        rfl
      have hφ_zero : φ w = 0 := by
        have hw_sum : w = ∑ j : Fin d, w j • Pi.single j (1 : F2) := by
          funext t; simp [Finset.sum_apply, Pi.single_apply]
        rw [hw_sum, map_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hcj : c j = 0 := congr_fun hc0 j
        rw [map_smul, show φ (Pi.single j 1) = c j from rfl, hcj, smul_zero]
      exact hi0 (hφw.symm.trans hφ_zero)
    have hcomb0 : ∑ j : Fin d, c j • (b j).1 = 0 := by
      funext t
      have hmem : ev (Pi.single t 1) ∈ LinearMap.range ev := ⟨Pi.single t 1, rfl⟩
      have hφ_ev : φ (ev (Pi.single t 1)) = 0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_right hW.symm ⟨_, hmem⟩, map_zero]
      have hev_sum : ev (Pi.single t 1) = ∑ j : Fin d, (b j).1 t • Pi.single j (1 : F2) := by
        funext j; simp [ev, dotProduct, Pi.single_apply, Finset.sum_apply]
      rw [hev_sum, map_sum] at hφ_ev
      simp only [map_smul, smul_eq_mul] at hφ_ev
      rw [Finset.sum_apply]
      calc ∑ j : Fin d, (c j • (b j).1) t
          = ∑ j : Fin d, (b j).1 t * c j :=
              Finset.sum_congr rfl fun j _ => by change c j * (b j).1 t = (b j).1 t * c j; ring
        _ = 0 := hφ_ev
    have hcombU : ∑ j : Fin d, c j • b j = 0 := by apply Subtype.ext; simpa using hcomb0
    exact hc_ne (funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hcombU))
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun F2,
    Module.finrank_fin_fun F2, hker, add_comm] at hrn
  exact hrn

noncomputable def gaussN (u d : ℕ) : ℕ :=
  Nat.card {W : Submodule F2 (Fin u → F2) // Module.finrank F2 W = d}

lemma gaussN_zero_right (u : ℕ) : gaussN u 0 = 1 := by
  classical
  have : Fintype (Submodule F2 (Fin u → F2)) := Fintype.ofFinite _
  simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq : (Finset.univ : Finset (Submodule F2 (Fin u → F2))).filter
      (fun W : Submodule F2 (Fin u → F2) => Module.finrank F2 W = 0) = {(⊥ : Submodule F2 (Fin u → F2))} := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact Submodule.finrank_eq_zero
  rw [heq, Finset.card_singleton]

private lemma gaussN_eq_zero_of_gt {u d : ℕ} (h : u < d) : gaussN u d = 0 := by
  classical
  have : Fintype (Submodule F2 (Fin u → F2)) := Fintype.ofFinite _
  simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro W _ hW
  have hle : Module.finrank F2 W ≤ u := by
    calc Module.finrank F2 W ≤ Module.finrank F2 (Fin u → F2) := Submodule.finrank_le _
      _ = u := Module.finrank_fin_fun F2
  omega

private lemma card_submodules_eq_gaussN {V : Type} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (u d : ℕ) (hV : Module.finrank F2 V = u) :
    Nat.card {W : Submodule F2 V // Module.finrank F2 W = d} = gaussN u d := by
  classical
  let e : V ≃ₗ[F2] (Fin u → F2) :=
    (Module.finBasis F2 V).equivFun.trans (LinearEquiv.funCongrLeft F2 F2 (finCongr hV.symm))
  refine Nat.card_congr
    { toFun := fun W => ⟨W.1.map e.toLinearMap, by rw [LinearEquiv.finrank_map_eq, W.2]⟩
      invFun := fun W => ⟨W.1.map e.symm.toLinearMap, by rw [LinearEquiv.finrank_map_eq, W.2]⟩
      left_inv := fun W => by
        apply Subtype.ext
        ext v
        simp only [Submodule.mem_map, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
        · intro hv; exact ⟨e v, ⟨v, hv, rfl⟩, e.symm_apply_apply v⟩
      right_inv := fun W => by
        apply Subtype.ext
        ext v
        simp only [Submodule.mem_map, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx
        · intro hv; exact ⟨e.symm v, ⟨v, hv, rfl⟩, e.apply_symm_apply v⟩ }

private lemma card_submodules_le_eq_gaussN {V : Type} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (U : Submodule F2 V) (d : ℕ) :
    Nat.card {W : Submodule F2 V // W ≤ U ∧ Module.finrank F2 W = d} =
      gaussN (Module.finrank F2 U) d := by
  classical
  rw [← card_submodules_eq_gaussN (V := U) (Module.finrank F2 U) d rfl]
  refine Nat.card_congr
    { toFun := fun W =>
        ⟨W.1.comap U.subtype, by
          have hmap : (W.1.comap U.subtype).map U.subtype = W.1 := by
            rw [Submodule.map_comap_subtype, inf_eq_right.mpr W.2.1]
          have hfin := Submodule.finrank_map_subtype_eq U (W.1.comap U.subtype)
          rw [hmap, W.2.2] at hfin
          exact hfin.symm⟩
      invFun := fun W =>
        ⟨W.1.map U.subtype, by
          refine ⟨Submodule.map_subtype_le U W.1, ?_⟩
          rw [Submodule.finrank_map_subtype_eq, W.2]⟩
      left_inv := fun W => by
        apply Subtype.ext
        dsimp only
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr W.2.1]
      right_inv := fun W => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective U) W.1 }

private lemma card_submodules_ge_eq_gaussN {V : Type} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (U : Submodule F2 V) (j : ℕ) (hj : Module.finrank F2 U ≤ j) :
    Nat.card {W : Submodule F2 V // U ≤ W ∧ Module.finrank F2 W = j} =
      gaussN (Module.finrank F2 V - Module.finrank F2 U) (j - Module.finrank F2 U) := by
  classical
  have hqdim : Module.finrank F2 (V ⧸ U) = Module.finrank F2 V - Module.finrank F2 U := by
    have := Submodule.finrank_quotient_add_finrank U
    omega
  rw [← card_submodules_eq_gaussN (V := V ⧸ U) _ _ hqdim]
  refine Nat.card_congr
    { toFun := fun W =>
        ⟨W.1.map (Submodule.mkQ U), by
          let f : W.1 →ₗ[F2] (V ⧸ U) := (Submodule.mkQ U).comp W.1.subtype
          have hrg : LinearMap.range f = W.1.map (Submodule.mkQ U) := by
            ext y
            simp only [LinearMap.mem_range, f, LinearMap.comp_apply, Submodule.coe_subtype,
              Submodule.mem_map, Subtype.exists]
            constructor
            · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
            · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
          have hker_eq : Module.finrank F2 (LinearMap.ker f) = Module.finrank F2 U := by
            let e : LinearMap.ker f ≃ₗ[F2] U :=
              { toFun := fun x => ⟨x.1.1, (Submodule.Quotient.mk_eq_zero U).mp x.2⟩
                invFun := fun u => ⟨⟨u.1, W.2.1 u.2⟩, (Submodule.Quotient.mk_eq_zero U).mpr u.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl
                map_add' := fun _ _ => rfl
                map_smul' := fun _ _ => rfl }
            exact e.finrank_eq
          have hrn := LinearMap.finrank_range_add_finrank_ker f
          rw [hrg, hker_eq, W.2.2] at hrn
          omega⟩
      invFun := fun Q =>
        ⟨Q.1.comap (Submodule.mkQ U), by
          refine ⟨fun u hu => ?_, ?_⟩
          · change Submodule.mkQ U u ∈ Q.1
            rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu]
            exact Q.1.zero_mem
          · let W := Q.1.comap (Submodule.mkQ U)
            have hUW : U ≤ W := fun u hu => by
              change Submodule.mkQ U u ∈ Q.1
              rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu]
              exact Q.1.zero_mem
            let f : W →ₗ[F2] (V ⧸ U) := (Submodule.mkQ U).comp W.subtype
            have hrg : LinearMap.range f = Q.1 := by
              ext y
              simp only [LinearMap.mem_range, f, LinearMap.comp_apply, Submodule.coe_subtype,
                Subtype.exists]
              constructor
              · rintro ⟨x, hxW, rfl⟩; exact hxW
              · intro hyQ
                obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U y
                exact ⟨x, hyQ, rfl⟩
            have hker_eq : Module.finrank F2 (LinearMap.ker f) = Module.finrank F2 U := by
              let e : LinearMap.ker f ≃ₗ[F2] U :=
                { toFun := fun x => ⟨x.1.1, (Submodule.Quotient.mk_eq_zero U).mp x.2⟩
                  invFun := fun u => ⟨⟨u.1, hUW u.2⟩, (Submodule.Quotient.mk_eq_zero U).mpr u.2⟩
                  left_inv := fun _ => rfl
                  right_inv := fun _ => rfl
                  map_add' := fun _ _ => rfl
                  map_smul' := fun _ _ => rfl }
              exact e.finrank_eq
            have hrn := LinearMap.finrank_range_add_finrank_ker f
            rw [hrg, hker_eq, Q.2] at hrn
            exact hrn.symm.trans (by omega)⟩
      left_inv := fun W => by
        apply Subtype.ext
        ext v
        simp only [Submodule.mem_comap, Submodule.mem_map]
        constructor
        · rintro ⟨w, hwW, hwq⟩
          have hsub : v - w ∈ U := by
            rw [← Submodule.Quotient.mk_eq_zero U]
            change Submodule.mkQ U (v - w) = 0
            rw [map_sub, hwq, sub_self]
          have hvw : v = w + (v - w) := by abel
          rw [hvw]
          exact W.1.add_mem hwW (W.2.1 hsub)
        · intro hvW
          exact ⟨v, hvW, rfl⟩
      right_inv := fun Q => by
        apply Subtype.ext
        ext y
        simp only [Submodule.mem_map, Submodule.mem_comap]
        constructor
        · rintro ⟨x, hxQ, rfl⟩; exact hxQ
        · intro hyQ
          obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective U y
          exact ⟨x, hyQ, rfl⟩ }

lemma gaussN_pascal (u d : ℕ) :
    gaussN (u + 1) (d + 1) = 2 ^ (d + 1) * gaussN u (d + 1) + gaussN u d := by
  classical
  have : Fintype (Submodule F2 (Fin (u + 1) → F2)) := Fintype.ofFinite _
  have : Fintype (Submodule F2 (Fin u → F2)) := Fintype.ofFinite _
  let e0 : Fin (u + 1) → F2 := Pi.single (Fin.last u) 1
  have he0_ne : e0 ≠ 0 := by
    intro h
    have := congr_fun h (Fin.last u)
    simp [e0] at this
  let All : Finset (Submodule F2 (Fin (u + 1) → F2)) :=
    (Finset.univ : Finset (Submodule F2 (Fin (u + 1) → F2))).filter
      (fun W : Submodule F2 (Fin (u + 1) → F2) => Module.finrank F2 W = d + 1)
  have hAll_card : All.card = gaussN (u + 1) (d + 1) := by
    simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype, All]
  let S1 := All.filter (fun W => e0 ∈ W)
  let S2 := All.filter (fun W => e0 ∉ W)
  have hsplit : S2.card + S1.card = All.card := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    calc ∑ W ∈ All, ((if e0 ∉ W then 1 else 0) + (if e0 ∈ W then 1 else 0))
        = ∑ _W ∈ All, 1 := Finset.sum_congr rfl fun W _ => by by_cases h : e0 ∈ W <;> simp [h]
      _ = All.card := by simp
  have hS1_card : S1.card = gaussN u d := by
    let U0 : Submodule F2 (Fin (u + 1) → F2) := Submodule.span F2 {e0}
    have hU0_dim : Module.finrank F2 U0 = 1 := finrank_span_singleton he0_ne
    have hge := card_submodules_ge_eq_gaussN U0 (d + 1) (by omega)
    rw [Module.finrank_fin_fun F2, hU0_dim, Nat.add_sub_cancel, Nat.add_sub_cancel] at hge
    rw [← hge, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp only [S1, All, Finset.mem_filter, Finset.mem_univ, true_and, U0, Submodule.span_le,
      Set.singleton_subset_iff]
    exact and_comm
  let proj : (Fin (u + 1) → F2) →ₗ[F2] (Fin u → F2) :=
    { toFun := fun v i => v i.castSucc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker_proj : LinearMap.ker proj = Submodule.span F2 {e0} := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hv
      refine ⟨v (Fin.last u), ?_⟩
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp [e0]
      · intro j
        have hj := congr_fun hv j
        simpa [e0, proj, Fin.castSucc_ne_last] using hj.symm
    · rintro ⟨c, rfl⟩
      funext j
      simp [proj, e0, Fin.castSucc_ne_last]
  let Base : Finset (Submodule F2 (Fin u → F2)) :=
    (Finset.univ : Finset (Submodule F2 (Fin u → F2))).filter
      (fun W' : Submodule F2 (Fin u → F2) => Module.finrank F2 W' = d + 1)
  have hBase_card : Base.card = gaussN u (d + 1) := by
    simp only [gaussN, Nat.card_eq_fintype_card, Fintype.card_subtype, Base]
  have hS2_card : S2.card = 2 ^ (d + 1) * gaussN u (d + 1) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun W : Submodule F2 (Fin (u + 1) → F2) => W.map proj)
      (s := S2) (t := Base)
    have hmaps : ∀ W ∈ S2, W.map proj ∈ Base := by
      intro W hW
      simp only [S2, All, Finset.mem_filter, Finset.mem_univ, true_and] at hW
      simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and]
      let f : W →ₗ[F2] (Fin u → F2) := proj.comp W.subtype
      have hker0 : LinearMap.ker f = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxker : x.1 ∈ LinearMap.ker proj := hx
        rw [hker_proj, Submodule.mem_span_singleton] at hxker
        rcases hxker with ⟨c, hc⟩
        by_cases hc0 : c = 0
        · apply Subtype.ext; rw [← hc, hc0, zero_smul]; rfl
        · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
          rw [hc1, one_smul] at hc
          exact absurd (hc ▸ x.2) hW.2
      have hrg : LinearMap.range f = W.map proj := by
        ext y; simp [f, LinearMap.mem_range, Submodule.mem_map]
      have hrn := LinearMap.finrank_range_add_finrank_ker f
      rw [hrg, hker0, finrank_bot, add_zero, hW.1] at hrn
      exact hrn
    rw [hfib hmaps]
    have hper : ∀ W' ∈ Base, (S2.filter (fun W => W.map proj = W')).card = 2 ^ (d + 1) := by
      intro W' hW'
      simp only [Base, Finset.mem_filter, Finset.mem_univ, true_and] at hW'
      letI : Finite (W' →ₗ[F2] F2) :=
        Finite.of_injective (fun f : W' →ₗ[F2] F2 => (f : W' → F2)) DFunLike.coe_injective
      letI : Fintype (W' →ₗ[F2] F2) := Fintype.ofFinite _
      have hdual_card : Fintype.card (W' →ₗ[F2] F2) = 2 ^ (d + 1) := by
        have hnc := Module.natCard_eq_pow_finrank (K := F2) (V := W' →ₗ[F2] F2)
        rw [Nat.card_eq_fintype_card, Nat.card_zmod, Module.finrank_linearMap,
          Module.finrank_self, mul_one, hW'] at hnc
        exact hnc
      rw [← hdual_card, ← Finset.card_univ]
      refine Finset.card_bij
        (fun W hW =>
          have hmem := (Finset.mem_filter.mp hW)
          have hW_dim := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem.1).1).2
          have hW_ne0 := (Finset.mem_filter.mp hmem.1).2
          have hW_map := hmem.2
          have hex : ∀ y : W', ∃ v : Fin (u + 1) → F2, v ∈ W ∧ proj v = y.1 := fun y => by
            have hy : y.1 ∈ W.map proj := hW_map.symm ▸ y.2
            exact Submodule.mem_map.mp hy
          have huniq : ∀ v1 v2 : Fin (u + 1) → F2, v1 ∈ W → v2 ∈ W → proj v1 = proj v2 → v1 = v2 := by
            intro v1 v2 hv1 hv2 hp
            have hdiff : v1 - v2 ∈ LinearMap.ker proj := by
              rw [LinearMap.mem_ker, map_sub, hp, sub_self]
            rw [hker_proj, Submodule.mem_span_singleton] at hdiff
            rcases hdiff with ⟨c, hc⟩
            by_cases hc0 : c = 0
            · rw [hc0, zero_smul] at hc; exact sub_eq_zero.mp hc.symm
            · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
              rw [hc1, one_smul] at hc
              exact absurd (hc ▸ W.sub_mem hv1 hv2) hW_ne0
          ({ toFun := fun y => (Classical.choose (hex y)) (Fin.last u)
             map_add' := fun y1 y2 => by
               have h1 := Classical.choose_spec (hex y1)
               have h2 := Classical.choose_spec (hex y2)
               have h12 := Classical.choose_spec (hex (y1 + y2))
               have heq := huniq _ _ h12.1 (W.add_mem h1.1 h2.1)
                 (by rw [h12.2, map_add, h1.2, h2.2]; rfl)
               exact congr_fun heq (Fin.last u)
             map_smul' := fun c y => by
               have h1 := Classical.choose_spec (hex y)
               have hc1 := Classical.choose_spec (hex (c • y))
               have heq := huniq _ _ hc1.1 (W.smul_mem c h1.1)
                 (by rw [hc1.2, map_smul, h1.2]; rfl)
               exact congr_fun heq (Fin.last u) } : W' →ₗ[F2] F2))
        ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro W1 hW1 W2 hW2 hφ
        have h1 := Finset.mem_filter.mp hW1
        have h2 := Finset.mem_filter.mp hW2
        have hW1_ne0 := (Finset.mem_filter.mp h1.1).2
        have hW2_ne0 := (Finset.mem_filter.mp h2.1).2
        have huniq1 : ∀ v1 v2 : Fin (u + 1) → F2, v1 ∈ W1 → v2 ∈ W1 → proj v1 = proj v2 → v1 = v2 := by
          intro v1 v2 hv1 hv2 hp
          have hdiff : v1 - v2 ∈ LinearMap.ker proj := by rw [LinearMap.mem_ker, map_sub, hp, sub_self]
          rw [hker_proj, Submodule.mem_span_singleton] at hdiff
          rcases hdiff with ⟨c, hc⟩
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact sub_eq_zero.mp hc.symm
          · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
            rw [hc1, one_smul] at hc; exact absurd (hc ▸ W1.sub_mem hv1 hv2) hW1_ne0
        have huniq2 : ∀ v1 v2 : Fin (u + 1) → F2, v1 ∈ W2 → v2 ∈ W2 → proj v1 = proj v2 → v1 = v2 := by
          intro v1 v2 hv1 hv2 hp
          have hdiff : v1 - v2 ∈ LinearMap.ker proj := by rw [LinearMap.mem_ker, map_sub, hp, sub_self]
          rw [hker_proj, Submodule.mem_span_singleton] at hdiff
          rcases hdiff with ⟨c, hc⟩
          by_cases hc0 : c = 0
          · rw [hc0, zero_smul] at hc; exact sub_eq_zero.mp hc.symm
          · have hc1 : c = 1 := by revert hc0; generalize c = z; revert z; decide
            rw [hc1, one_smul] at hc; exact absurd (hc ▸ W2.sub_mem hv1 hv2) hW2_ne0
        ext v
        constructor
        · intro hv1
          have hpW' : proj v ∈ W' := h1.2 ▸ Submodule.mem_map_of_mem hv1
          obtain ⟨v2, hv2, hp2⟩ := Submodule.mem_map.mp (h2.2.symm ▸ hpW')
          have hlast := LinearMap.congr_fun hφ ⟨proj v, hpW'⟩
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hlast
          have hex1 : ∃ w, w ∈ W1 ∧ proj w = proj v := ⟨v, hv1, rfl⟩
          have hex2 : ∃ w, w ∈ W2 ∧ proj w = proj v := ⟨v2, hv2, hp2⟩
          have hc1_eq : Classical.choose hex1 = v :=
            huniq1 _ _ (Classical.choose_spec hex1).1 hv1 (Classical.choose_spec hex1).2
          have hc2_eq : Classical.choose hex2 = v2 :=
            huniq2 _ _ (Classical.choose_spec hex2).1 hv2 ((Classical.choose_spec hex2).2.trans hp2.symm)
          rw [hc1_eq, hc2_eq] at hlast
          have hveq : v = v2 := by
            funext i
            refine Fin.lastCases hlast (fun j => (congr_fun hp2 j).symm) i
          exact hveq ▸ hv2
        · intro hv2
          have hpW' : proj v ∈ W' := h2.2 ▸ Submodule.mem_map_of_mem hv2
          obtain ⟨v1, hv1, hp1⟩ := Submodule.mem_map.mp (h1.2.symm ▸ hpW')
          have hlast := LinearMap.congr_fun hφ ⟨proj v, hpW'⟩
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hlast
          have hex1 : ∃ w, w ∈ W1 ∧ proj w = proj v := ⟨v1, hv1, hp1⟩
          have hex2 : ∃ w, w ∈ W2 ∧ proj w = proj v := ⟨v, hv2, rfl⟩
          have hc1_eq : Classical.choose hex1 = v1 :=
            huniq1 _ _ (Classical.choose_spec hex1).1 hv1 ((Classical.choose_spec hex1).2.trans hp1.symm)
          have hc2_eq : Classical.choose hex2 = v :=
            huniq2 _ _ (Classical.choose_spec hex2).1 hv2 (Classical.choose_spec hex2).2
          rw [hc1_eq, hc2_eq] at hlast
          have hveq : v = v1 := by
            funext i
            refine Fin.lastCases hlast.symm (fun j => (congr_fun hp1 j).symm) i
          exact hveq ▸ hv1
      · intro φ _
        let lift : W' →ₗ[F2] (Fin (u + 1) → F2) :=
          { toFun := fun y => Fin.snoc y.1 (φ y)
            map_add' := fun y1 y2 => by
              funext i
              refine Fin.lastCases ?_ ?_ i
              · simp [map_add]
              · intro j; simp
            map_smul' := fun c y => by
              funext i
              refine Fin.lastCases ?_ ?_ i
              · simp [map_smul]
              · intro j; simp }
        have hlift_inj : Function.Injective lift := by
          intro y1 y2 h
          apply Subtype.ext
          funext j
          have := congr_fun h j.castSucc
          simpa [lift] using this
        let W : Submodule F2 (Fin (u + 1) → F2) := LinearMap.range lift
        have hW_dim : Module.finrank F2 W = d + 1 := by
          rw [LinearMap.finrank_range_of_inj hlift_inj, hW']
        have hW_ne0 : e0 ∉ W := by
          rintro ⟨y, hy⟩
          have hy0 : y = 0 := by
            apply Subtype.ext
            funext j
            have := congr_fun hy j.castSucc
            simpa [lift, e0, Fin.castSucc_ne_last] using this
          rw [hy0, map_zero] at hy
          exact he0_ne hy.symm
        have hW_map : W.map proj = W' := by
          ext y
          simp only [Submodule.mem_map, W, LinearMap.mem_range]
          constructor
          · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
            have : proj (lift z) = z.1 := by funext j; simp [proj, lift]
            rw [this]; exact z.2
          · intro hy
            refine ⟨lift ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
            funext j; simp [proj, lift]
        refine ⟨W, ?_, ?_⟩
        · simp only [Finset.mem_filter, S2, All, Finset.mem_univ, true_and]
          exact ⟨⟨hW_dim, hW_ne0⟩, hW_map⟩
        · ext y
          dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
          have hspec := Classical.choose_spec (show ∃ v, v ∈ W ∧ proj v = y.1 from
            ⟨lift y, ⟨y, rfl⟩, by funext j; simp [proj, lift]⟩)
          rcases hspec.1 with ⟨z, hz⟩
          have hzy : z = y := by
            apply Subtype.ext
            funext j
            have := congr_fun hspec.2 j
            rw [← hz] at this
            simpa [proj, lift] using this
          rw [← hz, hzy]
          simp [lift]
    rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul, hBase_card, mul_comm]
  omega

private lemma gauss_mobius (k : ℕ) :
    (∑ d ∈ Finset.range (k + 1), (-1 : ℤ) ^ d * (2 : ℤ) ^ (Nat.choose d 2) * (gaussN k d : ℤ)) =
      if k = 0 then 1 else 0 := by
  cases k with
  | zero =>
    simp [gaussN_zero_right]
  | succ m =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    let f : ℕ → ℤ := fun r => (-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose (r + 1) 2) * (gaussN m r : ℤ)
    have hstep : ∀ r ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (r + 1) * (2 : ℤ) ^ (Nat.choose (r + 1) 2) * (gaussN (m + 1) (r + 1) : ℤ) =
          f (r + 1) - f r := by
      intro r _
      rw [gaussN_pascal m r]
      push_cast
      have hch : Nat.choose (r + 2) 2 = Nat.choose (r + 1) 2 + (r + 1) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      simp only [f, hch, pow_add, pow_succ]
      ring
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, gaussN_zero_right, Nat.cast_one]
    rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub f (m + 1)]
    have hf0 : f 0 = 1 := by simp [f, gaussN_zero_right]
    have hfm : f (m + 1) = 0 := by simp [f, gaussN_eq_zero_of_gt (Nat.lt_succ_self m)]
    rw [hf0, hfm]
    norm_num

open Classical in
private lemma pair_sum_over_subspace {a b : ℕ} (H : Matrix (Fin a) (Fin b) F2)
    (W : Submodule F2 (Fin a → F2)) :
    (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
        (fun D => LinearMap.range D.mulVecLin ≤ W),
      chi (∑ x, ∑ y, D x y * H x y)) =
    if W ≤ orth (LinearMap.range H.mulVecLin) then
      (2 : ℤ) ^ (b * Module.finrank F2 W)
    else 0 := by
  classical
  let S := (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
    (fun D => LinearMap.range D.mulVecLin ≤ W)
  have hcol_iff : ∀ D : Matrix (Fin a) (Fin b) F2,
      LinearMap.range D.mulVecLin ≤ W ↔ ∀ y : Fin b, (fun x => D x y) ∈ W := by
    intro D
    constructor
    · intro h y
      have hmem : D.mulVecLin (Pi.single y 1) ∈ LinearMap.range D.mulVecLin := ⟨Pi.single y 1, rfl⟩
      have heq : D.mulVecLin (Pi.single y 1) = fun x => D x y := by
        funext x; simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
      exact heq ▸ h hmem
    · rintro h _ ⟨v, rfl⟩
      have hsum : D.mulVecLin v = ∑ y : Fin b, v y • (fun x => D x y) := by
        funext x
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun y _ => mul_comm _ _
      rw [hsum]
      exact Submodule.sum_mem W fun y _ => W.smul_mem (v y) (h y)
  by_cases hW : W ≤ orth (LinearMap.range H.mulVecLin)
  · simp only [hW, ↓reduceIte]
    have hall0 : ∀ D ∈ S, chi (∑ x, ∑ y, D x y * H x y) = 1 := by
      intro D hD
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hcol_iff] at hD
      have h0 : (∑ x, ∑ y, D x y * H x y) = 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro y _
        have hHy : (fun x => H x y) ∈ LinearMap.range H.mulVecLin := by
          refine ⟨Pi.single y 1, ?_⟩
          funext x; simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
        exact hW (hD y) (fun x => H x y) hHy
      rw [h0, chi_zero]
    rw [Finset.sum_congr rfl hall0, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcardS : S.card = 2 ^ (b * Module.finrank F2 W) := by
      have hbij : S.card = Fintype.card (Fin b → W) := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun D hD y => ⟨fun x => D x y, (hcol_iff D).mp (Finset.mem_filter.mp hD).2 y⟩)
          ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro D1 _ D2 _ h
          ext x y
          exact congr_fun (congr_arg Subtype.val (congr_fun h y)) x
        · intro f _
          refine ⟨fun x y => (f y).1 x, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcol_iff _).mpr fun y => (f y).2⟩
          · funext y; apply Subtype.ext; rfl
      rw [hbij, Fintype.card_fun, Fintype.card_fin]
      have hWcard : Fintype.card W = 2 ^ Module.finrank F2 W := by
        have hnc := Module.natCard_eq_pow_finrank (K := F2) (V := W)
        rw [Nat.card_eq_fintype_card, Nat.card_zmod] at hnc
        exact hnc
      rw [hWcard, ← pow_mul, mul_comm]
    exact_mod_cast hcardS
  · simp only [hW, ↓reduceIte]
    have hex : ∃ w ∈ W, ∃ y0 : Fin b, dotProduct w (fun x => H x y0) = 1 := by
      by_contra hno
      push Not at hno
      apply hW
      intro w hwW u huH
      rcases huH with ⟨v, rfl⟩
      have hsum : H.mulVecLin v = ∑ y : Fin b, v y • (fun x => H x y) := by
        funext x
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun y _ => mul_comm _ _
      rw [hsum, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro y _
      have h0 : dotProduct w (fun x => H x y) = 0 := by
        have hne1 := hno w hwW y
        revert hne1; generalize dotProduct w (fun x => H x y) = z; revert z; decide
      rw [dotProduct_smul, h0, smul_zero]
    rcases hex with ⟨w, hwW, y0, hwH⟩
    let E : Matrix (Fin a) (Fin b) F2 := fun x y => if y = y0 then w x else 0
    have hES : ∀ D ∈ S, D + E ∈ S := by
      intro D hD
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hcol_iff] at hD ⊢
      intro y
      by_cases hy : y = y0
      · subst hy
        have : (fun x => (D + E) x y) = (fun x => D x y) + w := by
          funext x
          change D x y + E x y = D x y + w x
          simp [E]
        rw [this]
        exact W.add_mem (hD y) hwW
      · have : (fun x => (D + E) x y) = (fun x => D x y) := by
          funext x
          change D x y + E x y = D x y
          simp [E, hy]
        rw [this]
        exact hD y
    have hE_pair : (∑ x, ∑ y, E x y * H x y) = 1 := by
      rw [Finset.sum_comm, Finset.sum_eq_single y0]
      · simpa [E, dotProduct] using hwH
      · intro y _ hy; apply Finset.sum_eq_zero; intro x _; simp [E, hy]
      · intro h; exact absurd (Finset.mem_univ y0) h
    have hflip : ∀ D : Matrix (Fin a) (Fin b) F2,
        chi (∑ x, ∑ y, (D + E) x y * H x y) = - chi (∑ x, ∑ y, D x y * H x y) := by
      intro D
      have hadd : (∑ x, ∑ y, (D + E) x y * H x y) =
          (∑ x, ∑ y, D x y * H x y) + (∑ x, ∑ y, E x y * H x y) := by
        simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      rw [hadd, hE_pair, chi_add, chi_one]
      ring
    have hsum_neg : (∑ D ∈ S, chi (∑ x, ∑ y, D x y * H x y)) =
        -(∑ D ∈ S, chi (∑ x, ∑ y, D x y * H x y)) := by
      have hbij : (∑ D ∈ S, chi (∑ x, ∑ y, (D + E) x y * H x y)) =
          ∑ D ∈ S, chi (∑ x, ∑ y, D x y * H x y) := by
        refine Finset.sum_bij (fun D _ => D + E) hES ?_ ?_ (fun _ _ => rfl)
        · intro D1 _ D2 _ h; exact add_right_cancel h
        · intro D hD
          refine ⟨D + E, hES D hD, ?_⟩
          ext x y
          change (D x y + E x y) + E x y = D x y
          have : E x y + E x y = 0 := by generalize E x y = z; revert z; decide
          rw [add_assoc, this, add_zero]
      conv_lhs => rw [← hbij]
      simp_rw [hflip]
      rw [Finset.sum_neg_distrib]
    linarith

lemma rank_shell_sum {a b j : ℕ} (hja : j ≤ a) (H : Matrix (Fin a) (Fin b) F2) :
    (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
      chi (∑ x, ∑ y, D x y * H x y)) =
    ∑ d ∈ Finset.range (j + 1), (-1 : ℤ) ^ (j - d) * (2 : ℤ) ^ (Nat.choose (j - d) 2) *
      (2 : ℤ) ^ (b * d) * (gaussN (a - H.rank) d : ℤ) * (gaussN (a - d) (j - d) : ℤ) := by
  classical
  haveI : Fintype (Submodule F2 (Fin a → F2)) := Fintype.ofFinite _
  let f : Submodule F2 (Fin a → F2) → ℤ := fun W =>
    ∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
        (fun D => LinearMap.range D.mulVecLin = W),
      chi (∑ x, ∑ y, D x y * H x y)
  let g : Submodule F2 (Fin a → F2) → ℤ := fun W =>
    ∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter
        (fun D => LinearMap.range D.mulVecLin ≤ W),
      chi (∑ x, ∑ y, D x y * H x y)
  have hg_eq_sum_f : ∀ W : Submodule F2 (Fin a → F2),
      g W = ∑ U ∈ (Finset.univ : Finset (Submodule F2 (Fin a → F2))).filter (fun U => U ≤ W), f U := by
    intro W
    simp only [g, f]
    rw [← Finset.sum_biUnion]
    · congr 1
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hle; exact ⟨LinearMap.range D.mulVecLin, hle, rfl⟩
      · rintro ⟨U, hUW, rfl⟩; exact hUW
    · intro U1 _ U2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro D h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.symm.trans h2)
  have hmob_W : ∀ W : Submodule F2 (Fin a → F2), Module.finrank F2 W = j →
      f W = ∑ U ∈ (Finset.univ : Finset (Submodule F2 (Fin a → F2))).filter (fun U => U ≤ W),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U := by
    intro W hW
    simp_rw [hg_eq_sum_f]
    have hswap : (∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) *
          ∑ V ∈ Finset.univ.filter (fun V => V ≤ U), f V) =
        ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
          f V * ∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
            (-1 : ℤ) ^ (j - Module.finrank F2 U) *
              (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) := by
      calc ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) *
                ∑ V ∈ Finset.univ.filter (fun V => V ≤ U), f V
          = ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              ∑ V ∈ Finset.univ.filter (fun V => V ≤ U),
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * f V := by
              refine Finset.sum_congr rfl fun U _ => Finset.mul_sum _ _ _
        _ = ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
                if V ≤ U then
                  (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                    (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * f V
                else 0 := by
              refine Finset.sum_congr rfl fun U hU => ?_
              rw [← Finset.sum_filter]
              congr 1
              ext V
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
              exact ⟨fun h => ⟨le_trans h hU, h⟩, fun h => h.2⟩
        _ = ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
              ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
                if V ≤ U then
                  (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                    (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * f V
                else 0 := Finset.sum_comm
        _ = ∑ V ∈ Finset.univ.filter (fun V => V ≤ W),
              f V * ∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) := by
              refine Finset.sum_congr rfl fun V _ => ?_
              rw [Finset.mul_sum, ← Finset.sum_filter]
              refine Finset.sum_congr ?_ (fun _ _ => by ring)
              ext U
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact and_comm
    rw [hswap]
    have hinner : ∀ V ∈ Finset.univ.filter (fun V => V ≤ W),
        (∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
          (-1 : ℤ) ^ (j - Module.finrank F2 U) *
            (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2)) =
        if V = W then 1 else 0 := by
      intro V hV
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hV
      let k := j - Module.finrank F2 V
      have hVj : Module.finrank F2 V ≤ j := hW ▸ Submodule.finrank_mono hV
      have hfib : (∑ U ∈ Finset.univ.filter (fun U => V ≤ U ∧ U ≤ W),
            (-1 : ℤ) ^ (j - Module.finrank F2 U) *
              (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2)) =
          ∑ r ∈ Finset.range (k + 1),
            (-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose r 2) * (gaussN k r : ℤ) := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (g := fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U)
          (t := Finset.range (k + 1))]
        · refine Finset.sum_congr rfl fun r hr => ?_
          have hkr : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hconst : ∑ U ∈ (Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
              (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r),
              (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) =
              ((Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
                (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r)).card *
                ((-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose r 2)) := by
            have h1 : ∀ U ∈ (Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
                (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r),
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) =
                (-1 : ℤ) ^ r * (2 : ℤ) ^ (Nat.choose r 2) := by
              intro U hU
              rw [(Finset.mem_filter.mp hU).2]
            rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          have hcard_r : ((Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => V ≤ U ∧ U ≤ W)).filter
              (fun U : Submodule F2 (Fin a → F2) => j - Module.finrank F2 U = r)).card = gaussN k r := by
            let V' : Submodule F2 W := V.comap W.subtype
            have hV'_dim : Module.finrank F2 V' = Module.finrank F2 V := by
              have h1 := Submodule.finrank_map_subtype_eq W V'
              rw [Submodule.map_comap_subtype, inf_eq_right.mpr hV] at h1
              exact h1.symm
            have hge := card_submodules_ge_eq_gaussN (V := W) V' (j - r) (by omega)
            rw [hW, hV'_dim] at hge
            have hkr_sub : j - r - Module.finrank F2 V = k - r := by omega
            have hsym : gaussN k (k - r) = gaussN k r := by
              have horth_bij : Nat.card {X : Submodule F2 (Fin k → F2) // Module.finrank F2 X = k - r} =
                  Nat.card {X : Submodule F2 (Fin k → F2) // Module.finrank F2 X = r} := by
                refine Nat.card_congr
                  { toFun := fun X => ⟨orth X.1, by have := finrank_orth_add X.1; omega⟩
                    invFun := fun X => ⟨orth X.1, by have := finrank_orth_add X.1; omega⟩
                    left_inv := fun X => Subtype.ext (by
                      dsimp only
                      symm
                      apply Submodule.eq_of_le_of_finrank_eq
                      · intro u hu v hv; rw [dotProduct_comm]; exact hv u hu
                      · have h1 := finrank_orth_add X.1
                        have h2 := finrank_orth_add (orth X.1)
                        omega)
                    right_inv := fun X => Subtype.ext (by
                      dsimp only
                      symm
                      apply Submodule.eq_of_le_of_finrank_eq
                      · intro u hu v hv; rw [dotProduct_comm]; exact hv u hu
                      · have h1 := finrank_orth_add X.1
                        have h2 := finrank_orth_add (orth X.1)
                        omega) }
              exact horth_bij
            rw [hkr_sub, hsym] at hge
            rw [← hge, Nat.card_eq_fintype_card, Fintype.card_subtype]
            refine Finset.card_bij (fun U _ => U.comap W.subtype) ?_ ?_ ?_
            · intro U hU
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
              have hUW : U ≤ W := hU.1.2
              have hVU : V ≤ U := hU.1.1
              have hU_dim : Module.finrank F2 (U.comap W.subtype) = Module.finrank F2 U := by
                have h1 := Submodule.finrank_map_subtype_eq W (U.comap W.subtype)
                rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUW] at h1
                exact h1.symm
              have hU_le : Module.finrank F2 U ≤ j := hW ▸ Submodule.finrank_mono hUW
              refine ⟨fun x hx => hVU hx, ?_⟩
              omega
            · intro U1 hU1 U2 hU2 h
              have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hU1).1).2.2
              have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hU2).1).2.2
              have hm1 : (U1.comap W.subtype).map W.subtype = U1 := by
                rw [Submodule.map_comap_subtype, inf_eq_right.mpr h1]
              have hm2 : (U2.comap W.subtype).map W.subtype = U2 := by
                rw [Submodule.map_comap_subtype, inf_eq_right.mpr h2]
              rw [← hm1, ← hm2, h]
            · intro Q hQ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
              refine ⟨Q.map W.subtype, ?_, Submodule.comap_map_eq_of_injective (Submodule.subtype_injective W) Q⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hQ_dim : Module.finrank F2 (Q.map W.subtype) = j - r := by
                rw [Submodule.finrank_map_subtype_eq, hQ.2]
              refine ⟨⟨fun v hv => ?_, Submodule.map_subtype_le W Q⟩, ?_⟩
              · exact ⟨⟨v, hV hv⟩, hQ.1 hv, rfl⟩
              · omega
          rw [hcard_r]
          ring
        · intro U hU
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
          have h1 : Module.finrank F2 V ≤ Module.finrank F2 U := Submodule.finrank_mono hU.1
          rw [Finset.mem_range]
          omega
      rw [hfib, gauss_mobius k]
      have hk0 : k = 0 ↔ V = W := by
        constructor
        · intro h0
          exact Submodule.eq_of_le_of_finrank_eq hV (by omega)
        · intro heq; subst heq; simp [k, hW]
      by_cases heq : V = W
      · simp [heq, hk0.mpr heq]
      · have hne : k ≠ 0 := fun h0 => heq (hk0.mp h0)
        simp [heq, hne]
    rw [Finset.sum_congr rfl fun V hV => by rw [hinner V hV]]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hrank_split : (∑ D ∈ (Finset.univ : Finset (Matrix (Fin a) (Fin b) F2)).filter (fun D => D.rank = j),
        chi (∑ x, ∑ y, D x y * H x y)) =
      ∑ W ∈ (Finset.univ : Finset (Submodule F2 (Fin a → F2))).filter
          (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
        f W := by
    simp only [f]
    rw [← Finset.sum_biUnion]
    · congr 1
      ext D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hrk; exact ⟨LinearMap.range D.mulVecLin, hrk, rfl⟩
      · rintro ⟨W, hW, hDW⟩; change Module.finrank F2 (LinearMap.range D.mulVecLin) = j; rw [hDW, hW]
    · intro W1 _ W2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro D h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.symm.trans h2)
  rw [hrank_split]
  rw [Finset.sum_congr rfl fun W hW => hmob_W W (Finset.mem_filter.mp hW).2]
  have hswap_WU : (∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
        ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
          (-1 : ℤ) ^ (j - Module.finrank F2 U) *
            (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U) =
      ∑ U ∈ Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U ≤ j),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U *
          ((Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
            U ≤ W ∧ Module.finrank F2 W = j)).card : ℤ) := by
    calc ∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
            ∑ U ∈ Finset.univ.filter (fun U => U ≤ W),
              (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U
        = ∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
            ∑ U ∈ Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U ≤ j),
              if U ≤ W then
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U
              else 0 := by
            refine Finset.sum_congr rfl fun W hW => ?_
            rw [← Finset.sum_filter]
            congr 1
            ext U
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW ⊢
            exact ⟨fun h => ⟨hW ▸ Submodule.finrank_mono h, h⟩, fun h => h.2⟩
      _ = ∑ U ∈ Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U ≤ j),
            ∑ W ∈ Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) => Module.finrank F2 W = j),
              if U ≤ W then
                (-1 : ℤ) ^ (j - Module.finrank F2 U) *
                  (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U
              else 0 := Finset.sum_comm
      _ = _ := by
            refine Finset.sum_congr rfl fun U _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
            have hfilt : (Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
                Module.finrank F2 W = j)).filter (fun W => U ≤ W) =
              Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
                U ≤ W ∧ Module.finrank F2 W = j) := by
              ext W; simp [and_comm]
            rw [hfilt]
  rw [hswap_WU]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U)
    (t := Finset.range (j + 1))]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hdj : d ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hterm : ∀ U ∈ (Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) =>
        Module.finrank F2 U ≤ j)).filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U = d),
        (-1 : ℤ) ^ (j - Module.finrank F2 U) *
          (2 : ℤ) ^ (Nat.choose (j - Module.finrank F2 U) 2) * g U *
          ((Finset.univ.filter (fun W : Submodule F2 (Fin a → F2) =>
            U ≤ W ∧ Module.finrank F2 W = j)).card : ℤ) =
        (if U ≤ orth (LinearMap.range H.mulVecLin) then
          (-1 : ℤ) ^ (j - d) * (2 : ℤ) ^ (Nat.choose (j - d) 2) *
            (2 : ℤ) ^ (b * d) * (gaussN (a - d) (j - d) : ℤ)
         else 0) := by
      intro U hU
      have hUd : Module.finrank F2 U = d := (Finset.mem_filter.mp hU).2
      have hge := card_submodules_ge_eq_gaussN U j (by omega)
      rw [Module.finrank_fin_fun F2, hUd, Nat.card_eq_fintype_card, Fintype.card_subtype] at hge
      have hgU : g U = if U ≤ orth (LinearMap.range H.mulVecLin) then (2 : ℤ) ^ (b * d) else 0 := by
        rw [← hUd]
        exact pair_sum_over_subspace H U
      rw [hUd, hgU, hge]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : (((Finset.univ.filter (fun U : Submodule F2 (Fin a → F2) =>
        Module.finrank F2 U ≤ j)).filter (fun U : Submodule F2 (Fin a → F2) => Module.finrank F2 U = d)).filter
        (fun U : Submodule F2 (Fin a → F2) => U ≤ orth (LinearMap.range H.mulVecLin))).card = gaussN (a - H.rank) d := by
      have hle := card_submodules_le_eq_gaussN (orth (LinearMap.range H.mulVecLin)) d
      have horth_dim : Module.finrank F2 (orth (LinearMap.range H.mulVecLin)) = a - H.rank := by
        have := finrank_orth_add (LinearMap.range H.mulVecLin)
        change Module.finrank F2 (orth (LinearMap.range H.mulVecLin)) + H.rank = a at this
        omega
      rw [horth_dim, Nat.card_eq_fintype_card, Fintype.card_subtype] at hle
      rw [← hle]
      congr 1
      ext U
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, rfl⟩, hle'⟩; exact ⟨hle', rfl⟩
      · rintro ⟨hle', rfl⟩; exact ⟨⟨hdj, rfl⟩, hle'⟩
    rw [hcard_le]
    ring
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hU)

end Spectrum

end PEqualNP.Outside.L_meta_33667

namespace PEqualNP.Outside.L_meta_33667

open Matrix
open scoped BigOperators

abbrev F := ZMod 2
abbrev Mat (a b : ℕ) := Matrix (Fin a) (Fin b) F
abbrev Tab (a b : ℕ) := Fin (a+1) → Fin (b+1) → Bool
abbrev Off (a b : ℕ) := (Fin (a+1) → F) × (Fin b → F)

def entry {a b} (P : Tab a b) (i : Fin (a+1)) (j : Fin (b+1)) : F := Gates.b2z (P i j)

def core {a b} (P : Tab a b) : Mat a b :=
  (Gates.anchor 0 0 (entry P)).submatrix Fin.succ Fin.succ

def extendZero {a b} (D : Mat a b) : Mat (a+1) (b+1) :=
  Fin.cases (fun _ => 0) (fun i => Fin.cases 0 (D i))

def decode {a b} (z : Off a b) (D : Mat a b) : Tab a b :=
  fun i j => decide (extendZero D i j + z.1 i + Fin.cases 0 z.2 j = 1)

theorem entry_decode {a b} (z : Off a b) (D : Mat a b) (i j) :
    entry (decode z D) i j =
      extendZero D i j + z.1 i + Fin.cases 0 z.2 j := by
  simp [entry, decode, Gates.b2z, Gates.zmod2_ite_eq]

def offsets {a b} (P : Tab a b) : Off a b :=
  (fun i => entry P i 0, fun j => entry P 0 j.succ + entry P 0 0)

theorem core_decode {a b} (z : Off a b) (D : Mat a b) : core (decode z D) = D := by
  ext i j
  simp only [core, Gates.anchor, Matrix.submatrix_apply, entry_decode, extendZero,
    Fin.cases_zero, Fin.cases_succ, zero_add, add_zero]
  ring_nf <;> simp [Gates.zmod2_two, show (4 : F) = 0 by decide]

theorem offsets_decode {a b} (z : Off a b) (D : Mat a b) : offsets (decode z D) = z := by
  rcases z with ⟨r,c⟩
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · cases i using Fin.cases <;> simp [offsets, entry_decode, extendZero]
  · simp [offsets, entry_decode, extendZero, add_comm, add_left_comm, Gates.zmod2_add_self]

theorem decode_entry {a b} (P : Tab a b) : decode (offsets P) (core P) = P := by
  funext i j
  apply Gates.b2z_inj
  change entry _ i j = entry P i j
  rw [entry_decode]
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [extendZero, core, Gates.anchor, Matrix.submatrix_apply, offsets,
      Fin.cases_zero, Fin.cases_succ, zero_add, add_zero] <;>
    ring_nf <;> simp [Gates.zmod2_two, show (4 : F) = 0 by decide]

def tableEquiv (a b : ℕ) : Tab a b ≃ Off a b × Mat a b where
  toFun P := (offsets P, core P)
  invFun v := decode v.1 v.2
  left_inv := decode_entry
  right_inv v := Prod.ext (offsets_decode ..) (core_decode ..)

theorem anchor_extend {a b} (P : Tab a b) :
    Gates.anchor 0 0 (entry P) = extendZero (core P) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [extendZero, core, Matrix.submatrix_apply, Gates.anchor, Fin.cases_zero, Fin.cases_succ] <;>
    ring_nf <;> simp [Gates.zmod2_two, show (4 : F) = 0 by decide]

theorem extend_rank {a b} (D : Mat a b) : (extendZero D).rank = D.rank := by
  apply le_antisymm
  · let L : Mat (a+1) a := Fin.cases (fun _ => 0) (1 : Mat a a)
    let R : Mat b (b+1) := fun k => Fin.cases 0 (fun j => (1 : Mat b b) k j)
    have hx : extendZero D = L * D * R := by
      have hl : L * D = Fin.cases (fun _ => 0) D := by
        ext i j
        cases i using Fin.cases with
        | zero =>
          change (∑ k, 0 * D k j) = 0
          simp
        | succ i =>
          change ((1 : Mat a a) * D) i j = D i j
          rw [Matrix.one_mul]
      rw [hl]
      ext i j
      cases i using Fin.cases with
      | zero =>
        change 0 = ∑ k, 0 * R k j
        simp
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          change 0 = ∑ k, D i k * 0
          simp
        | succ j =>
          change D i j = (D * (1 : Mat b b)) i j
          rw [Matrix.mul_one]
    rw [hx]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · exact Matrix.rank_submatrix_le (extendZero D) Fin.succ Fin.succ

def allowed {a b} (t : ℕ) (P : Tab a b) : Prop :=
  ∃ Q : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (a+1+(b+1)) Q ∧ PEqualNP.Represents.Represents P Q ∧
    (Gates.depthsOf (a+1+(b+1)) Q.gates).getD Q.output 0 ≤ 1 ∧ Q.gates.countP Gates.nlGate ≤ t

theorem allowed_iff {a b} (P : Tab a b) (t : ℕ) :
    allowed t P ↔ (core P).rank ≤ 2*t := by
  have hc := Gates.main (a+1) (b+1) P 0 0 t
  change (Gates.anchor 0 0 (entry P)).rank ≤ 2*t ↔ _ at hc
  rw [anchor_extend, extend_rank] at hc
  rw [hc]
  unfold allowed
  constructor
  · rintro ⟨Q,h₁,h₂,h₃,h₄,h₅⟩
    exact ⟨Q, ⟨h₁,h₂,h₃⟩, h₄,h₅⟩
  · rintro ⟨Q,⟨h₁,h₂,h₃⟩,h₄,h₅⟩
    exact ⟨Q,h₁,h₂,h₃,h₄,h₅⟩

end PEqualNP.Outside.L_meta_33667

namespace PEqualNP.Outside.L_meta_33667

open Matrix
open scoped BigOperators

def ip {a b} (A H : Mat a b) : F := ∑ i, ∑ j, A i j * H i j
def rowSum {a b} (H : Mat a b) (i : Fin a) : F := ∑ j, H i j
def colSum {a b} (H : Mat a b) (j : Fin b) : F := ∑ i, H i j
def evenM {a b} (H : Mat a b) : Prop := (∀ i, rowSum H i = 0) ∧ (∀ j, colSum H j = 0)

theorem pair_decode {a b} (z : Off a b) (D : Mat a b) (H : Mat (a+1) (b+1)) :
    ip (entry (decode z D)) H = ip D (H.submatrix Fin.succ Fin.succ) +
      (∑ i, z.1 i * rowSum H i) + (∑ j, z.2 j * colSum H j.succ) := by
  simp only [ip, entry_decode, add_mul, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · simp [extendZero, Fin.sum_univ_succ]
    · simp [rowSum, Finset.mul_sum]
  · rw [Finset.sum_comm, Fin.sum_univ_succ]
    simp [colSum, Finset.mul_sum]

theorem border_even {a b} (H : Mat (a+1) (b+1)) :
    evenM H ↔ (∀ i, rowSum H i = 0) ∧ (∀ j : Fin b, colSum H j.succ = 0) := by
  constructor
  · exact fun h => ⟨h.1, fun j => h.2 j.succ⟩
  · rintro ⟨hr,hc⟩
    refine ⟨hr, ?_⟩
    intro j
    cases j using Fin.cases with
    | succ k => exact hc k
    | zero =>
      have h : (∑ i, rowSum H i) = ∑ j, colSum H j := Finset.sum_comm
      rw [Fin.sum_univ_succ (f := colSum H)] at h
      simpa [hr,hc] using h.symm

theorem vectorSigns {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → F) :
    (∑ x : ι → F, Spectrum.chi (∑ i, x i * k i)) =
      (if ∀ i, k i = 0 then (2 : ℤ)^Fintype.card ι else 0) := by
  classical
  by_cases h : ∀ i, k i = 0
  · simp [h, Spectrum.chi_zero, ZMod.card]
  · simp only [h, ite_false]
    obtain ⟨j,hj⟩ := not_forall.mp h
    have hj1 : k j = 1 := by generalize k j = u at *; revert hj; revert u; decide
    let d : ι → F := Pi.single j 1
    have hv (x : ι → F) : (∑ i, (x+d) i * k i) = (∑ i, x i * k i) + 1 := by
      simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, d, Pi.single_apply, ite_mul, hj1]
    have he := Equiv.sum_comp (Equiv.addRight d) (fun x : ι → F => Spectrum.chi (∑ i, x i * k i))
    change (∑ x : ι → F, Spectrum.chi (∑ i, (x+d) i * k i)) = _ at he
    simp_rw [hv, Spectrum.chi_add, Spectrum.chi_one, mul_neg_one] at he
    rw [Finset.sum_neg_distrib] at he
    omega

theorem offsetSigns {a b} (D : Mat a b) (H : Mat (a+1) (b+1)) :
    (∑ z : Off a b, Spectrum.chi (ip (entry (decode z D)) H)) =
      Spectrum.chi (ip D (H.submatrix Fin.succ Fin.succ)) *
        (if (∀ i, rowSum H i = 0) ∧ (∀ j, colSum H j = 0) then (2 : ℤ)^(a+b+1) else 0) := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [pair_decode, Spectrum.chi_add]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum, vectorSigns, vectorSigns]
  simp only [Fintype.card_fin]
  have he := border_even H
  unfold evenM at he
  by_cases hf : (∀ i, rowSum H i = 0) ∧ (∀ j, colSum H j = 0)
  · rcases he.mp hf with ⟨hr, hc⟩
    rw [if_pos hf, if_pos hr, if_pos hc]
    simp only [pow_add, pow_one]
    ring
  · rw [if_neg hf, mul_zero]
    by_cases hr : ∀ i, rowSum H i = 0
    · have hn : ¬ ∀ j : Fin b, colSum H j.succ = 0 := fun hc => hf (he.mpr ⟨hr,hc⟩)
      rw [if_neg hn, mul_zero]
    · rw [if_neg hr, mul_zero, zero_mul]

end PEqualNP.Outside.L_meta_33667
namespace PEqualNP.Outside.L_meta_33667

open scoped BigOperators
open Polynomial Matrix

noncomputable def shellValue (a b j h : ℕ) : ℤ :=
  let gauss := fun u d : ℕ =>
    (Nat.card {W : Submodule F (Fin u → F) // Module.finrank F W = d} : ℤ)
  ∑ d ∈ Finset.range (j+1), (-1 : ℤ)^(j-d) * 2^(Nat.choose (j-d) 2) *
    2^(b*d) * gauss (a-h) d * gauss (a-d) (j-d)

theorem boundedSpectrum {a b} (t : ℕ) (K : Mat a b) :
    (∑ D ∈ Finset.univ.filter (fun D : Mat a b => D.rank ≤ 2*t), Spectrum.chi (ip D K)) =
    ∑ j ∈ Finset.range (min a (2*t)+1), shellValue a b j K.rank := by
  classical
  rw [Finset.sum_filter]
  calc
    _ = ∑ D : Mat a b, ∑ j ∈ Finset.range (min a (2*t)+1),
            if D.rank = j then Spectrum.chi (ip D K) else 0 := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : D.rank ≤ 2*t
      · have hj : D.rank ∈ Finset.range (min a (2*t)+1) := by
          have ha := D.rank_le_height
          simp only [Finset.mem_range]
          omega
        simp [h, hj, Finset.sum_ite_eq]
      · have hj : D.rank ∉ Finset.range (min a (2*t)+1) := by
          simp only [Finset.mem_range]
          omega
        simp [h, hj, Finset.sum_ite_eq]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≤ a := by have := Finset.mem_range.mp hj; omega
      rw [← Finset.sum_filter]
      exact Spectrum.rank_shell_sum hja K

theorem tableSpectrum {a b} (t : ℕ) (H : Mat (a+1) (b+1)) :
    (∑ P ∈ Finset.univ.filter (fun P : Tab a b => (core P).rank ≤ 2*t),
      Spectrum.chi (ip (entry P) H)) =
    (if (∀ i, rowSum H i = 0) ∧ (∀ j, colSum H j = 0) then
      (2 : ℤ)^(a+b+1) * (∑ j ∈ Finset.range (min a (2*t)+1),
        shellValue a b j (H.submatrix Fin.succ Fin.succ).rank) else 0) := by
  classical
  rw [Finset.sum_filter]
  let f := fun P : Tab a b => if (core P).rank ≤ 2*t then Spectrum.chi (ip (entry P) H) else 0
  change (∑ P, f P) = _
  rw [← Equiv.sum_comp (tableEquiv a b).symm f]
  change (∑ v : Off a b × Mat a b, if (core (decode v.1 v.2)).rank ≤ 2*t then
    Spectrum.chi (ip (entry (decode v.1 v.2)) H) else 0) = _
  simp_rw [core_decode]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  let mult : ℤ := if (∀ i, rowSum H i = 0) ∧ (∀ j, colSum H j = 0) then 2^(a+b+1) else 0
  calc
    _ = ∑ D ∈ Finset.univ.filter (fun D : Mat a b => D.rank ≤ 2*t),
          Spectrum.chi (ip D (H.submatrix Fin.succ Fin.succ)) * mult := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : D.rank ≤ 2*t
      · simp only [h, ite_true]
        exact offsetSigns D H
      · simp [h]
    _ = _ := by
      rw [← Finset.sum_mul, boundedSpectrum]
      by_cases h : (∀ i, rowSum H i = 0) ∧ (∀ j, colSum H j = 0) <;> simp [mult,h,mul_comm]

theorem sumTests {a b m} (B : Fin m → Mat (a+1) (b+1)) (S : Finset (Fin m)) (P : Tab a b) :
    S.sum (fun i => ip (entry P) (B i)) = ip (entry P) (S.sum B) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [ip]
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi, ih]
    simp [ip, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

end PEqualNP.Outside.L_meta_33667

namespace PEqualNP.Outside.L_meta_33667
open Finset Spectrum

lemma odd_gauss (u d : ℕ) (h : d ≤ u) : Odd (gaussN u d) := by
  induction u generalizing d with
  | zero =>
    have he : d = 0 := by omega
    subst d
    simp [gaussN_zero_right]
  | succ u ih =>
    cases d with
    | zero => simp [gaussN_zero_right]
    | succ d =>
      obtain ⟨k,hk⟩ := ih d (by omega)
      rw [gaussN_pascal,hk,pow_succ]
      exact ⟨2^d * gaussN u (d+1) + k, by ring⟩

lemma tri (j : ℕ) : (j+1).choose 2 = j.choose 2 + j := by rw [Nat.choose_succ_succ]; simp [add_comm]
lemma expBound (l d : ℕ) : (l+d).choose 2 + d ≤ l.choose 2 + (l+d)*d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have he : (l+(d+1)).choose 2 = (l+d).choose 2 + (l+d) := tri (l+d)
    rw [he]; nlinarith

lemma shell_order (a b j h : ℕ) (hja : j ≤ a) (hjb : j ≤ b) :
    ∃ z : ℤ, Odd z ∧ shellValue a b j h = 2^(j.choose 2)*z := by
  let term (d : ℕ) : ℤ := (-1 : ℤ)^(j-d)*2^((j-d).choose 2)*2^(b*d)*
    (gaussN (a-h) d : ℤ)*(gaussN (a-d) (j-d) : ℤ)
  let S := (range (j+1)).erase 0
  have hdvd : (2:ℤ)^(j.choose 2+1) ∣ ∑ d ∈ S, term d := by
    apply dvd_sum
    intro d hd
    obtain ⟨hne,hr⟩ := mem_erase.mp hd
    have hdj : d ≤ j := by have := mem_range.mp hr; omega
    have he := expBound (j-d) d
    rw [Nat.sub_add_cancel hdj] at he
    have hb := Nat.mul_le_mul_right d hjb
    have hh : j.choose 2+1 ≤ (j-d).choose 2+b*d := by omega
    refine dvd_trans (pow_dvd_pow (2:ℤ) hh) ⟨(-1:ℤ)^(j-d)*(gaussN (a-h) d : ℤ)*(gaussN (a-d) (j-d) : ℤ),?_⟩
    simp only [term,pow_add]; ring
  obtain ⟨w,hw⟩ := hdvd
  let u : ℤ := (-1:ℤ)^j*(gaussN a j : ℤ)
  have ho : Odd u := by
    apply Odd.mul ((show Odd (-1:ℤ) from ⟨-1,by norm_num⟩).pow)
    exact_mod_cast odd_gauss a j hja
  refine ⟨2*w+u,?_,?_⟩
  · obtain ⟨k,hk⟩ := ho; exact ⟨w+k,by rw [hk]; ring⟩
  · change (∑ d ∈ range (j+1),term d) = _
    rw [← sum_erase_add _ _ (show 0 ∈ range (j+1) by simp)]
    change (∑ d ∈ S,term d) + term 0 = _
    rw [hw,pow_succ]
    simp only [term,u,Nat.sub_zero,Nat.mul_zero,pow_zero,gaussN_zero_right,Nat.cast_one,mul_one]; ring

lemma all_char {a b} (H : Mat a b) : (∑ D : Mat a b, chi (ip D H)) =
    (if H=0 then (2:ℤ)^(a*b) else 0) := by
  classical
  let e : (Fin a × Fin b → F) ≃ Mat a b := Equiv.curry _ _ _
  rw [← e.sum_comp (fun D => chi (ip D H))]
  let K := fun p : Fin a × Fin b => H p.1 p.2
  have hh (x : Fin a × Fin b → F) : ip (e x) H = ∑ p, x p * K p := by
    rw [Fintype.sum_prod_type]; rfl
  simp_rw [hh]
  rw [vectorSigns]
  have he : (∀ p, K p = 0) ↔ H = 0 := by
    constructor
    · intro h; ext i j; exact h (i,j)
    · rintro rfl; simp [K]
  simp only [he,Fintype.card_prod,Fintype.card_fin]

lemma rank_prefix {a b} (s : ℕ) (hs : s ≤ a) (H : Mat a b) :
    (∑ D ∈ univ.filter (fun D : Mat a b => D.rank ≤ s),chi (ip D H)) =
    ∑ j ∈ range (s+1), shellValue a b j H.rank := by
  classical
  calc
    _ = ∑ D : Mat a b, ∑ j ∈ range (s+1), if D.rank = j then chi (ip D H) else 0 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro D _
      by_cases h : D.rank ≤ s
      · have hb : D.rank ∈ range (s+1) := mem_range.mpr (by omega)
        simp [h,hb,sum_ite_eq]
      · have hb : D.rank ∉ range (s+1) := by simp; omega
        simp [h,hb,sum_ite_eq]
    _ = _ := by
      rw [sum_comm]; apply sum_congr rfl; intro j hj; rw [← sum_filter]
      exact Spectrum.rank_shell_sum (by have := mem_range.mp hj; omega) H

lemma ball_order {a b r} (hr : r < min a b) (H : Mat a b) :
    ∃ z : ℤ, Odd z ∧ (∑ j ∈ range (r+1),shellValue a b j H.rank) = 2^((r+1).choose 2)*z := by
  classical
  let B (s : ℕ) := ∑ j ∈ range (s+1),shellValue a b j H.rank
  let k := (r+1).choose 2
  let u : ℤ := 2^k
  let N := min a b
  have step s : B (s+1) = B s + shellValue a b (s+1) H.rank := sum_range_succ ..
  have tailDiv (s : ℕ) (lo : r+1 ≤ s) (hi : s ≤ N) : 2*u ∣ B s - B (r+1) := by
    induction s, lo using Nat.le_induction with
    | base => simp
    | succ s hs ih =>
      obtain ⟨z,_,hz⟩ := shell_order a b (s+1) H.rank (by dsimp [N] at hi; omega) (by dsimp [N] at hi; omega)
      have hb : k+1 ≤ (s+1).choose 2 := by
        have := Nat.choose_le_choose 2 hs
        rw [tri]; dsimp [k]; omega
      have hd : 2*u ∣ shellValue a b (s+1) H.rank := by
        rw [hz]; change 2 * (2:ℤ)^k ∣ _
        rw [← pow_succ']; exact dvd_mul_of_dvd_left (pow_dvd_pow _ hb) _
      rw [step,add_sub_right_comm]; exact dvd_add (ih (by omega)) hd
  have total : B N = (if H=0 then (2:ℤ)^(a*b) else 0) := by
    rw [← all_char]
    have hp := rank_prefix N (Nat.min_le_left a b) H
    have hh : ∀ D : Mat a b, D.rank ≤ N := fun D => le_min (by simpa using D.rank_le_height) (by simpa using D.rank_le_width)
    simpa [B,hh] using hp.symm
  have kd : k+1 ≤ a*b := by
    have h := expBound 0 (r+1)
    simp only [zero_add,Nat.choose_zero_succ,zero_add] at h
    have hh : (r+1)*(r+1) ≤ a*b := Nat.mul_le_mul (by omega) (by omega)
    dsimp [k]; omega
  have divis : 2*u ∣ B N := by
    rw [total]; split
    · change 2*(2:ℤ)^k ∣ _; rw [←pow_succ']; exact pow_dvd_pow _ kd
    · exact dvd_zero _
  obtain ⟨w,hw⟩ := dvd_sub divis (tailDiv N (by dsimp [N]; omega) le_rfl)
  obtain ⟨z,hoz,hz⟩ := shell_order a b (r+1) H.rank (by omega) (by omega)
  have heq : B (r+1) = (2*u)*w := by linarith
  rw [step,hz] at heq
  refine ⟨2*w-z,?_,?_⟩
  · obtain ⟨v,hv⟩ := hoz; refine ⟨w-v-1,?_⟩; rw [hv]; ring
  · change B r = u*(2*w-z)
    change B r + u*z = (2*u)*w at heq
    linarith

end PEqualNP.Outside.L_meta_33667

namespace PEqualNP.Outside.L_meta_33667
open Finset Spectrum

lemma sum_sub_chars {m : ℕ} (v : Fin m → F) :
    (∑ S : Finset (Fin m), chi (S.sum v)) = if ∀ i, v i = 0 then (2 : ℤ)^m else 0 := by
  classical
  have hprod : (∑ S : Finset (Fin m), chi (S.sum v)) = ∏ i : Fin m, (chi (v i) + 1) := by
    rw [Fintype.prod_add]
    refine sum_congr rfl fun S _ => ?_
    simp only [prod_const_one,mul_one]
    induction S using Finset.induction_on with
    | empty => simp [chi_zero]
    | insert a s ha ih => simp [ha,chi_add,ih]
  rw [hprod]
  by_cases hall : ∀ i, v i = 0
  · norm_num [hall,chi_zero]
  · rw [if_neg hall]
    obtain ⟨i,hi⟩ := not_forall.mp hall
    have hv : v i = 1 := by revert hi; generalize v i = x; revert x; decide
    exact prod_eq_zero (mem_univ i) (by simp [hv,chi_one])

noncomputable def hits {α : Type} {m : ℕ} (U : Finset α) (e : α → Fin m → F) (v : Fin m → F) : ℤ :=
  ∑ x ∈ U, if e x = v then 1 else 0

lemma uniform_iff {α : Type} {m : ℕ} (U : Finset α) (e : α → Fin m → F) :
    (∀ u v, hits U e u = hits U e v) ↔ ∀ S : Finset (Fin m), S.Nonempty →
       (∑ x ∈ U, chi (S.sum (e x))) = 0 := by
  classical
  let C (S : Finset (Fin m)) := ∑ x ∈ U, chi (S.sum (e x))
  have agg S : C S = ∑ v : Fin m → F, hits U e v * chi (S.sum v) := by
    simp only [hits,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    simp [ite_mul]
  constructor
  · intro hu S hs
    rw [← show C S = ∑ x ∈ U, chi (S.sum (e x)) from rfl,agg]
    simp_rw [fun v => hu v 0]
    rw [← mul_sum]
    suffices h : (∑ v : Fin m → F, chi (S.sum v)) = 0 by rw [h,mul_zero]
    let k (i : Fin m) : F := if i ∈ S then 1 else 0
    have hv v : S.sum v = ∑ i, v i * k i := by simp [k,mul_ite,sum_ite_mem]
    simp_rw [hv]
    rw [vectorSigns,if_neg]
    obtain ⟨i,hi⟩ := hs
    intro h; simpa [k,hi] using h i
  · intro hc
    have inv v : (2:ℤ)^m * hits U e v = ∑ S : Finset (Fin m), chi (S.sum v) * C S := by
      simp only [hits,C,mul_sum]
      rw [sum_comm (s:=univ) (t:=U)]
      apply sum_congr rfl
      intro x _
      have hsum : ∀ S : Finset (Fin m), chi (S.sum v) * chi (S.sum (e x)) =
          chi (S.sum (fun i => v i + e x i)) := by intro S; rw [sum_add_distrib,chi_add]
      simp_rw [hsum]
      rw [sum_sub_chars]
      have he : (∀ i, v i + e x i = 0) ↔ e x = v := by
        have hz : ∀ a b : F, a+b=0 ↔ b=a := by decide
        simp_rw [hz]; exact funext_iff.symm
      simp only [he]
      by_cases h : e x = v <;> simp [h]
    have collapse v : (2:ℤ)^m * hits U e v = C ∅ := by
      rw [inv, sum_eq_single (∅ : Finset (Fin m))]
      · simp [chi_zero]
      · intro S _ hn
        rw [show C S = 0 from hc S (nonempty_iff_ne_empty.mpr hn),mul_zero]
      · simp
    intro u v
    exact mul_left_cancel₀ (by positivity : (2:ℤ)^m ≠ 0) ((collapse u).trans (collapse v).symm)

end PEqualNP.Outside.L_meta_33667

namespace PEqualNP.Outside.L_meta_33667
open Finset Spectrum

noncomputable def testOf {a b} (P : Tab a b) (D : Mat (a+1) (b+1)) : F :=
  ∑ x, ∑ y, D x y * entry P x y
lemma commute_test {a b} (P : Tab a b) (D : Mat (a+1) (b+1)) : testOf P D = ip (entry P) D := by
  simp only [testOf,ip,mul_comm]

noncomputable def tests {a b m} (B : Fin m → Mat (a+1) (b+1)) (P : Tab a b) (i : Fin m) := testOf P (B i)
noncomputable def pool (a b t : ℕ) := univ.filter (fun P : Tab a b => (core P).rank ≤ 2*t)
noncomputable def charSum {a b} (t : ℕ) (D : Mat (a+1) (b+1)) :=
  ∑ P ∈ pool a b t, chi (ip (entry P) D)

noncomputable def countAns {a b m} (B : Fin m → Mat (a+1) (b+1)) (t : ℕ) (v : Fin m → F) : ℕ :=
  Nat.card {P : Tab a b // allowed t P ∧ ∀ i, testOf P (B i) = v i}
lemma card_hits {a b m} (B : Fin m → Mat (a+1) (b+1)) (t : ℕ) (v : Fin m → F) :
    (countAns B t v : ℤ) = hits (pool a b t) (tests B) v := by
  classical
  simp only [countAns,Nat.card_eq_fintype_card,Fintype.card_subtype,hits,sum_boole,pool,filter_filter]
  congr 2
  apply filter_congr
  intro P _
  rw [allowed_iff,funext_iff]
  rfl

noncomputable def chargeOf {a b} (t : ℕ) (D : Mat (a+1) (b+1)) :=
  (Nat.card {P : Tab a b // allowed t P ∧ testOf P D = 0} : ℤ) -
  (Nat.card {P : Tab a b // allowed t P ∧ testOf P D = 1} : ℤ)
lemma charge_char {a b} (t : ℕ) (D : Mat (a+1) (b+1)) : chargeOf t D = charSum t D := by
  classical
  have cn (v : F) : (Nat.card {P : Tab a b // allowed t P ∧ testOf P D = v} : ℤ) =
      ∑ P ∈ pool a b t, if ip (entry P) D = v then 1 else 0 := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,sum_boole,pool,filter_filter,allowed_iff,commute_test]
  rw [chargeOf,cn,cn,← sum_sub_distrib]
  apply sum_congr rfl
  intro P _
  have he : ∀ z : F, (if z=0 then (1:ℤ) else 0) - (if z=1 then 1 else 0) = chi z := by decide
  exact he _

lemma small_order {a b t} (hr : 2*t < min a b) (D : Mat (a+1) (b+1)) (he : evenM D) :
    ∃ z : ℤ, Odd z ∧ charSum t D = 2^(a+b+1+Nat.choose (2*t+1) 2)*z := by
  obtain ⟨z,ho,hz⟩ := ball_order hr (D.submatrix Fin.succ Fin.succ)
  refine ⟨z,ho,?_⟩
  unfold evenM at he
  rw [charSum,pool,tableSpectrum,ite_eq_left he,Nat.min_eq_right (by omega : 2*t ≤ a),hz,pow_add _ (a+b+1),mul_assoc]

lemma big_char {a b t} (hr : min a b ≤ 2*t) (D : Mat (a+1) (b+1)) :
    charSum t D = if D=0 then (2:ℤ)^((a+1)*(b+1)) else 0 := by
  classical
  have hu : pool a b t = univ := by
    apply filter_true_of_mem
    intro P _
    exact le_trans (le_min (by simpa using (core P).rank_le_height) (by simpa using (core P).rank_le_width)) hr
  let E : Tab a b ≃ Mat (a+1) (b+1) :=
    { toFun := entry, invFun := fun M i j => decide (M i j = 1)
      left_inv := fun P => by funext i j; cases h : P i j <;> simp [entry,Gates.b2z,h]
      right_inv := fun M => by ext i j; simp [entry,Gates.b2z,Gates.zmod2_ite_eq] }
  rw [charSum,hu,← all_char]
  exact E.sum_comp (fun M => chi (ip M D))

lemma vanishes {a b} (t : ℕ) (D : Mat (a+1) (b+1)) :
    charSum t D = 0 ↔ if 2*t < min a b then ¬ evenM D else D ≠ 0 := by
  classical
  split_ifs with h
  · by_cases he : evenM D
    · obtain ⟨z,ho,hz⟩ := small_order h D he
      have nz : z ≠ 0 := by obtain ⟨k,hk⟩ := ho; omega
      have hc : charSum t D ≠ 0 := by rw [hz]; exact mul_ne_zero (by positivity) nz
      exact iff_of_false hc (fun hh => hh he)
    · have hzero : charSum t D = 0 := by
        unfold evenM at he
        rw [charSum,pool,tableSpectrum,ite_eq_right he]
      exact iff_of_true hzero he
  · rw [big_char (by omega : min a b ≤ 2*t)]
    split_ifs <;> simp_all

lemma finish {a b m} (B : Fin m → Mat (a+1) (b+1)) (t : ℕ) :
    (((∀ u v, countAns B t u = countAns B t v) ↔ ∀ S : Finset (Fin m), S.Nonempty →
       (if 2*t < min a b then ¬ evenM (S.sum B) else S.sum B ≠ 0)) ∧
     (2*t < min a b → ∀ D : Mat (a+1) (b+1), evenM D → ∃ z : ℤ, Odd z ∧
       chargeOf t D = 2^(a+b+1+Nat.choose (2*t+1) 2)*z)) := by
  classical
  constructor
  · have hh : (∀ u v, countAns B t u = countAns B t v) ↔
        ∀ u v, hits (pool a b t) (tests B) u = hits (pool a b t) (tests B) v := by
      simp_rw [← card_hits]; norm_cast
    rw [hh, uniform_iff]
    apply forall_congr'; intro S; apply imp_congr_right; intro _
    have he (P : Tab a b) : S.sum (tests B P) = ip (entry P) (S.sum B) := by
      calc
        _ = S.sum (fun i => ip (entry P) (B i)) := sum_congr rfl fun i _ => commute_test P (B i)
        _ = _ := sumTests B S P
    simp_rw [he]
    exact vanishes t _
  · intro h D he
    rw [charge_char]
    exact small_order h D he

end PEqualNP.Outside.L_meta_33667

theorem PEqualNP.Outside.L_meta_33667 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun h => ds.getD h 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (a b m t : ℕ),
  let F := ZMod 2
  let M := Matrix (Fin (a+1)) (Fin (b+1)) F
  let T := Fin (a+1) → Fin (b+1) → Bool
  ∀ B : Fin m → M,
    let test := fun (P : T) (D : M) =>
      ∑ x, ∑ y, D x y * (if P x y then (1 : F) else 0)
    let realizable := fun (P : T) => ∃ Q : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (a+1+(b+1)) Q ∧ PEqualNP.Represents.Represents P Q ∧
      depth (a+1+(b+1)) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t
    let count := fun (v : Fin m → F) => Nat.card {P : T // realizable P ∧ ∀ i, test P (B i) = v i}
    let even := fun (D : M) => (∀ x, (∑ y, D x y) = 0) ∧ (∀ y, (∑ x, D x y) = 0)
    let r := 2*t
    let charge := fun (D : M) =>
      (Nat.card {P : T // realizable P ∧ test P D = 0} : ℤ) -
      (Nat.card {P : T // realizable P ∧ test P D = 1} : ℤ)
    (((∀ u v, count u = count v) ↔ ∀ S : Finset (Fin m), S.Nonempty →
       (if r < min a b then ¬ even (S.sum B) else S.sum B ≠ 0)) ∧
     (r < min a b → ∀ D : M, even D → ∃ z : ℤ, Odd z ∧
       charge D = 2^(a+b+1+Nat.choose (r+1) 2) * z))) := by
  intro nonlinear depth a b m t F M T B test realizable count even r charge
  exact PEqualNP.Outside.L_meta_33667.finish B t
