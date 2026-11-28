import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_32043_aux

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

end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
lemma eq_anchor_rank_le (W : ℕ) [NeZero W] (hW2 : 2 ≤ W) (hWeven : (W : ZMod 2) = 0) :
    (anchor (0 : Fin W) (0 : Fin W)
      (fun i j => b2z (decide (i = j)))).rank ≤ W - 2 := by
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

abbrev F := ZMod 2
abbrev Sq (N : ℕ) := Matrix (Fin N) (Fin N) F

def eqA (N : ℕ) [NeZero N] : Sq N :=
  anchor 0 0 (fun i j => b2z (decide (i = j)))

lemma eqA_le {N : ℕ} [NeZero N] : (eqA N).rank ≤ 2*((N-1)/2) := by
  let W := 2*((N-1)/2)+2
  have h : N ≤ W := by dsimp [W]; omega
  haveI : NeZero W := ⟨by dsimp [W]; omega⟩
  let f := Fin.castLE h
  have hr := Matrix.rank_submatrix_le (eqA W) f f
  have he : (eqA W).submatrix f f = eqA N := by
    ext i j
    have hf : Function.Injective f := Fin.castLE_injective h
    have hz : f 0 = 0 := Fin.ext rfl
    simp only [Matrix.submatrix_apply, eqA, anchor, ← hz, hf.eq_iff]
  rw [he] at hr
  exact hr.trans (eq_anchor_rank_le W (by dsimp [W]; omega) (by simp [W, Nat.cast_add, Nat.cast_mul, zmod2_two]))

lemma eqA_ge {N : ℕ} [NeZero N] : 2*((N-1)/2) ≤ (eqA N).rank := by
  let K := 2*((N-1)/2)
  let f : Fin K → Fin N := fun i => ⟨i.val+1, by have := i.isLt; dsimp [K] at *; omega⟩
  have hf : Function.Injective f := by intro i j h; apply Fin.ext; simpa [f,Fin.ext_iff] using h
  have hn (i : Fin K) : f i ≠ 0 := by simp [f, Fin.ext_iff]
  let J : Sq K := fun _ _ => 1
  have he : (eqA N).submatrix f f = 1 + J := by
    ext i j
    rw [Matrix.add_apply, Matrix.one_apply]
    simp [eqA, anchor, Matrix.submatrix, b2z, hn, Ne.symm (hn j), hf.eq_iff, Matrix.one_apply, J]
  have hj : J*J = 0 := by ext i j; rw [Matrix.mul_apply]; simp [J,K,zmod2_two]
  have hid : (1+J)*(1+J) = 1 := by simp only [add_mul,mul_add,one_mul,mul_one,hj,add_zero,add_assoc]; ext i j; simp [Matrix.add_apply,zmod2_add_self]
  have hr := Matrix.rank_mul_le_left (1+J) (1+J)
  rw [hid, Matrix.rank_one, Fintype.card_fin] at hr
  exact hr.trans (he ▸ Matrix.rank_submatrix_le (eqA N) f f)

def shift {N : ℕ} [NeZero N] : Sq N := fun _ j => if j = 0 then 1 else 0
def diff {N : ℕ} [NeZero N] : Sq N := 1 + shift
lemma anchor_as_mul {N : ℕ} [NeZero N] (A : Sq N) :
    anchor 0 0 A = diff*A*diff.transpose := by
  ext i j
  simp [diff, shift, Matrix.transpose_add, add_mul, mul_add, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.one_apply, anchor, mul_ite, ite_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
lemma diff_row {N : ℕ} [NeZero N] (P : Sq N) (h : ∀ i, ∑ j, P i j = 1) :
    diff*P*diff = diff*P := by
  have hp : P*shift = shift := by
    ext i j
    by_cases hj : j = 0 <;> simp [Matrix.mul_apply, shift, hj, h]
  have hs : (shift : Sq N)*shift = shift := by
    ext i j
    by_cases hj : j = 0 <;> simp [shift,Matrix.mul_apply,hj]
  have hz : (diff : Sq N)*shift = 0 := by
    rw [diff,add_mul,one_mul,hs]; ext i j; exact zmod2_add_self _
  calc diff*P*diff = diff*P + diff*(P*shift) := by rw [diff,mul_add,mul_one,Matrix.mul_assoc]
       _ = diff*P := by rw [hp,hz,add_zero]

lemma rank_cong_le {N : ℕ} [NeZero N] (P A : Sq N) (h : ∀ i, ∑ j, P i j = 1) :
    (anchor 0 0 (P*A*P.transpose)).rank ≤ (anchor 0 0 A).rank := by
  let U := diff*P
  have hu : U*diff = U := diff_row P h
  have hut : diff.transpose*U.transpose = U.transpose := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hu
  have hid : U*(diff*A*diff.transpose)*U.transpose =
      diff*(P*A*P.transpose)*diff.transpose := by
    calc U*(diff*A*diff.transpose)*U.transpose = (U*diff)*A*(diff.transpose*U.transpose) := by simp [Matrix.mul_assoc]
         _ = U*A*U.transpose := by rw [hu,hut]
         _ = _ := by simp [U,Matrix.transpose_mul, Matrix.mul_assoc]
  rw [anchor_as_mul, ← hid, ← anchor_as_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

lemma rank_cong_eq {N : ℕ} [NeZero N] (P A : Sq N) (hh : P*P=1) (h : ∀ i, ∑ j, P i j = 1) :
    (anchor 0 0 (P*A*P.transpose)).rank = (anchor 0 0 A).rank := by
  apply le_antisymm (rank_cong_le P A h)
  have ht : P.transpose*P.transpose=1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hh
  have he : P*(P*A*P.transpose)*P.transpose = A := by
    calc _ = (P*P)*A*(P.transpose*P.transpose) := by simp [Matrix.mul_assoc]
         _ = _ := by rw [hh,ht,one_mul,mul_one]
  simpa only [he] using rank_cong_le P (P*A*P.transpose) h

end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
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

def Fit {n : ℕ} (G : Fin n → Fin n → Bool) (d t : ℕ) :=
  ∃ C : Circuit, ReadsBack (n+n) C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    C.gates.countP nlGate ≤ t ∧ (depthsOf (n+n) C.gates).getD C.output 0 ≤ d ∧ Represents G C

lemma digit {N W : ℕ} [NeZero N] (f : Fin N → Fin W) :
    Fit (fun i j => decide (f i = f j)) 1 ((W+1)/2) := by
  let B := anchor (f 0) (f 0) (fun i j => b2z (decide (i=j)))
  have he : B.submatrix f f = anchor 0 0 (fun i j => b2z (decide (f i=f j))) := rfl
  have hr := Matrix.rank_submatrix_le B f f
  rw [he] at hr
  have hh := B.rank_le_width
  obtain ⟨C, ⟨hl,hb,hv⟩,hd,hc⟩ := dir_ge (fun i j => decide (f i=f j)) 0 0 ((W+1)/2) (by omega)
  exact ⟨C,hb,hl,hc,hd,hv⟩

lemma digit_bound {N W : ℕ} [NeZero N] (f g : Fin N → Fin W)
    (hinj : Function.Injective (fun i => (f i,g i))) :
    Fit (fun i j : Fin N => decide (i=j)) 2 (2*((W+1)/2)+1) := by
  obtain ⟨A,ba,la,ca,da,va⟩ := digit f
  obtain ⟨B,bb,lb,cb,db,vb⟩ := digit g
  have bound (C : Circuit) (d : Fin N → Fin W)
      (v : Represents (fun i j => decide (d i=d j)) C) : C.output < N+N+C.gates.length := by
    by_contra! hh
    have h := v 0 0
    change (wiresOf (oneEach (0 : Fin N) (0 : Fin N)) C.gates).getD C.output false = _ at h
    rw [List.getD_eq_default _ _ (by rw [wiresOf_length,oneEach_length]; exact hh)] at h
    simp at h
  have ha := bound A f va
  have hb := bound B g vb
  let gs := A.gates ++ B.gates.map (shiftGate (N+N) A.gates.length)
  let b := shiftWire (N+N) A.gates.length B.output
  obtain ⟨hv,hl,hc,do_,wo,dn,wn⟩ := shift_append_spec (n:=N) (m:=N) (gs:=A.gates) ⟨la,ba⟩ B lb bb
  change gs.length = _ at hl
  have ha' : A.output < N+N+gs.length := by omega
  have hb' : b < N+N+gs.length := by dsimp [b,shiftWire]; split <;> omega
  obtain ⟨hh,_,cc,_,_,dd,vv⟩ := pushAnd_spec hv ha' hb'
  refine ⟨⟨_,N+N+gs.length⟩,hh.2,hh.1,?_,?_,?_⟩
  · change (pushAnd gs A.output b).countP nlGate ≤ _
    change gs.countP nlGate = _ at hc
    rw [cc,hc]; omega
  · change (depthsOf (N+N) (pushAnd gs A.output b)).getD _ 0 ≤ _
    rw [dd,do_ _ ha,dn _ hb]; omega
  · intro i j
    apply b2z_inj
    change b2z ((wiresOf (oneEach i j) (pushAnd gs A.output b)).getD _ false) = _
    rw [vv,wo i j _ ha,wn i j _ hb]
    change b2z (A.eval _) * b2z (B.eval _) = _
    rw [va i j,vb i j]
    by_cases eq : i=j
    · subst j; simp [b2z]
    · have ne : ¬ (f i=f j ∧ g i=g j) := fun hh => eq (hinj (Prod.ext hh.1 hh.2))
      by_cases hf : f i=f j <;> simp_all [b2z]

lemma depth_two {N : ℕ} [NeZero N] :
    Fit (fun i j : Fin N => decide (i=j)) 2 (Nat.sqrt (N-1)+3) := by
  let W := Nat.sqrt (N-1)+1
  have hw : 0<W := Nat.zero_lt_succ _
  have hn : N ≤ W*W := by have h := Nat.lt_succ_sqrt (N-1); change N-1<W*W at h; omega
  let f : Fin N → Fin W := fun i => ⟨i.val % W,Nat.mod_lt _ hw⟩
  let g : Fin N → Fin W := fun i => ⟨i.val/W,(Nat.div_lt_iff_lt_mul hw).2 (i.isLt.trans_le hn)⟩
  have hi : Function.Injective (fun i => (f i,g i)) := by
    intro i j h
    have h1 := congrArg (fun p : Fin W × Fin W => p.1.val) h
    have h2 := congrArg (fun p : Fin W × Fin W => p.2.val) h
    apply Fin.ext
    change i.val % W=j.val % W at h1
    change i.val/W=j.val/W at h2
    rw [← Nat.mod_add_div i.val W,h1,h2,Nat.mod_add_div]
  obtain ⟨C,hb,hl,hc,hd,hv⟩ := digit_bound f g hi
  exact ⟨C,hb,hl,by dsimp [W] at hc; omega,hd,hv⟩

end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
def masks (m : ℕ) := (Finset.univ : Finset (Finset (Fin m × Fin m))).filter (fun S => S.card ≤ m^2/16)
lemma mask_count (m : ℕ) : (masks m).card^16 ≤ 2^(6*m^2) := by
  classical
  let L := m^2
  let r := L/16
  have hr : r ≤ L := Nat.div_le_self _ _
  have ht : 16*r ≤ L := by dsimp [r]; omega
  have cardL : Fintype.card (Fin m × Fin m) = L := by simp [L,pow_two]
  let w := fun S : Finset (Fin m × Fin m) => 8^(L-S.card)
  have hsum : (∑ S, w S) = 9^L := by
    have h := Fintype.prod_add (fun _ : Fin m × Fin m => (1:ℕ)) (fun _ => 8)
    simpa [w, Finset.card_compl,cardL] using h.symm
  have hlow : (masks m).card * 8^(L-r) ≤ 9^L := by
    rw [← hsum]
    calc _ = ∑ _S ∈ masks m, 8^(L-r) := by simp
         _ ≤ ∑ S ∈ masks m, w S := by
           apply Finset.sum_le_sum
           intro S hS
           have h : S.card ≤ r := (Finset.mem_filter.mp hS).2
           exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left h L)
         _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have h16 := Nat.pow_le_pow_left hlow 16
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm L 16, pow_mul 9] at h16
  have hc : (9:ℕ)^16 ≤ 2^51 := by decide
  have hu := h16.trans (Nat.pow_le_pow_left hc L)
  rw [← pow_mul] at hu
  have h8 : (8:ℕ)^((L-r)*16) = 2^(48*(L-r)) := by
    rw [show (8:ℕ)=2^3 by decide,← pow_mul]; congr 1; ring
  rw [h8] at hu
  apply Nat.le_of_mul_le_mul_right (c:=2^(48*(L-r))) _ (by positivity)
  refine hu.trans ?_
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  dsimp [L] at *; omega

lemma count_gap {m k : ℕ} (hm : 32 ≤ m) (hk : 8*k ≤ m) :
    16*(4*m*k+k*(k-1)+2*m+k)+6*m^2 < 16*(m*(m-1)) := by
  have hk2 : k*(k-1)+k=k*k := by cases k <;> simp [Nat.mul_add, Nat.add_mul] <;> ring
  have h1 := Nat.mul_le_mul_left m hk
  have h2 := Nat.mul_self_le_mul_self hk
  have h3 := Nat.mul_le_mul_left m hm
  have hm1 : m*(m-1)+m=m*m := by cases m <;> simp [Nat.mul_add, Nat.add_mul] <;> ring
  nlinarith

end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
abbrev Tab (m : ℕ) := Fin m × Fin m → ZMod 2
abbrev Plane (m : ℕ) := Submodule (ZMod 2) (Tab m)

def splitMap (m : ℕ) : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] Tab m where
  toFun p := fun x => p.1 x.1 + p.2 x.2
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [mul_add]

def initial (m : ℕ) := LinearMap.range (splitMap m)
def extendP {m} (U : Plane m) (a b : Tab m) := U ⊔ Submodule.span (ZMod 2) {a*b}

noncomputable def elems {m} (U : Plane m) : Finset (Tab m) := by
  classical exact Finset.univ.filter (fun x => x ∈ U)
lemma mem_elems {m} {U : Plane m} {a : Tab m} : a ∈ elems U ↔ a ∈ U := by
  classical simp [elems]
noncomputable def children {m} (U : Plane m) := by
  classical exact ((elems U) ×ˢ (elems U)).image (fun p => extendP U p.1 p.2)
noncomputable def family (m : ℕ) : ℕ → Finset (Plane m)
  | 0 => {initial m}
  | k+1 => by classical exact (family m k).biUnion children

lemma child_iff {m} {U V : Plane m} : V ∈ children U ↔ ∃ a ∈ U, ∃ b ∈ U, extendP U a b = V := by
  classical simp [children,Finset.mem_image,Prod.exists,mem_elems,and_assoc]

lemma step_mem {m k} {U : Plane m} (hu : U ∈ family m k) {a b} (ha : a ∈ U) (hb : b ∈ U) :
    extendP U a b ∈ family m (k+1) := by
  classical exact Finset.mem_biUnion.mpr ⟨U,hu,child_iff.mpr ⟨a,ha,b,hb,rfl⟩⟩

lemma fam_mono {m k t} (ht : k ≤ t) : family m k ⊆ family m t := by
  induction t,ht using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t _ ih =>
    intro U hu
    simpa [extendP] using step_mem (ih hu) U.zero_mem U.zero_mem

lemma data_dim {m k} {U : Plane m} (hu : U ∈ family m k) :
    Module.finrank (ZMod 2) U ≤ 2*m+k := by
  classical
  induction k generalizing U with
  | zero =>
    simp [family] at hu; subst U
    apply (splitMap m).finrank_range_le.trans
    simp [Module.finrank_prod, Module.finrank_fin_fun, two_mul]
  | succ k ih =>
    obtain ⟨V,hV,hU⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨a,_,b,_,rfl⟩ := child_iff.mp hU
    have hv := ih hV
    have hh := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span (ZMod 2) {a*b})
    have hs : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a*b}) ≤ 1 := by
      exact (finrank_span_le_card ({a*b} : Set (Tab m))).trans (by simp)
    unfold extendP
    omega
lemma elems_card {m k} {U : Plane m} (hu : U ∈ family m k) : (elems U).card ≤ 2^(2*m+k) := by
  classical
  have he : (elems U).card = Fintype.card U := by
    simpa [elems] using (Fintype.card_subtype (fun x : Tab m => x ∈ U)).symm
  rw [he, Module.card_eq_pow_finrank (K:=ZMod 2), ZMod.card]
  exact Nat.pow_le_pow_right (by decide) (data_dim hu)

lemma family_card {m k} : (family m k).card ≤ 2^(4*m*k+k*(k-1)) := by
  classical
  induction k with
  | zero => simp [family]
  | succ k ih =>
    have h := Finset.card_biUnion_le_card_mul (family m k) children (2^(2*(2*m+k))) (by
      intro U hu
      calc (children U).card ≤ ((elems U) ×ˢ elems U).card := Finset.card_image_le
           _ ≤ _ := by rw [Finset.card_product,two_mul,pow_add]; exact Nat.mul_le_mul (elems_card hu) (elems_card hu))
    have he : 4*m*(k+1)+(k+1)*(k+1-1) = (4*m*k+k*(k-1))+2*(2*m+k) := by
      cases k <;> simp [Nat.succ_eq_add_one] <;> ring
    rw [he,pow_add]
    exact h.trans (Nat.mul_le_mul_right _ ih)

noncomputable def predictions (m k : ℕ) : Finset (Tab m) := by classical exact (family m k).biUnion elems
lemma predictions_card (m k : ℕ) :
    (predictions m k).card ≤ 2^(4*m*k+k*(k-1)+2*m+k) := by
  classical
  have hh := Finset.card_biUnion_le_card_mul (family m k) elems (2^(2*m+k)) (by intro U hu; exact elems_card hu)
  rw [Nat.add_assoc,pow_add]
  exact hh.trans (Nat.mul_le_mul_right _ family_card)

end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

lemma const_mem {m} (c : ZMod 2) : (fun _ => c : Tab m) ∈ initial m :=
  ⟨(fun _ => c,fun _ => 0),by ext; simp [splitMap]⟩

lemma propagate {m k} {U : Plane m} (hU : U ∈ family m k) (hi : initial m ≤ U)
    (v : ℕ → Fin m × Fin m → Bool) (hm : ∀ w, (fun x => b2z (v w x)) ∈ U)
    (g : Gate) (hg : g.inputs.length ≤ 2) :
    ∃ V ∈ family m (k+(nlGate g).toNat), U ≤ V ∧
      (fun x => b2z (g.op.eval (g.inputs.map (fun w => v w x)))) ∈ V := by
  let f (w : ℕ) : Tab m := fun x => b2z (v w x)
  match he : g.inputs with
  | [] =>
    simp only [he,List.map_nil,nlGate,List.length_nil] at *
    exact ⟨U,hU,le_rfl,hi (const_mem _)⟩
  | [a] =>
    have hf : (fun x => b2z (g.op.eval [v a x])) =
        (fun _ => b2z (g.op.eval [false]) : Tab m) +
        (b2z (g.op.eval [false])+b2z (g.op.eval [true])) • f a := by
      funext x; exact anf_one (fun z => g.op.eval [z]) _
    refine ⟨U,by simpa [nlGate,he] using hU,le_rfl,?_⟩
    simpa only [he,List.map_cons,List.map_nil,hf] using
      (show (fun x => b2z (g.op.eval [v a x])) ∈ U from hf ▸ U.add_mem (hi (const_mem _)) (U.smul_mem _ (hm _)))
  | [a,b] =>
    let coef := xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
    have hn : nlGate g = coef := by simp [nlGate,he,coef]
    let aff : Tab m := (fun _ => b2z (g.op.eval [false,false])) +
        (b2z (g.op.eval [false,false])+b2z (g.op.eval [true,false])) • f a +
        (b2z (g.op.eval [false,false])+b2z (g.op.eval [false,true])) • f b
    have hf : (fun x => b2z (g.op.eval [v a x,v b x])) = aff + b2z coef • (f a*f b) := by
      funext x; exact anf_two (fun u w => g.op.eval [u,w]) _ _
    have hm' : aff ∈ U := U.add_mem (U.add_mem (hi (const_mem _)) (U.smul_mem _ (hm _))) (U.smul_mem _ (hm _))
    simp only [he,List.map_cons,List.map_nil,hf,hn]
    cases h : coef with
    | false =>
      exact ⟨U,hU,le_rfl,by simpa [b2z] using hm'⟩
    | true =>
      let V := extendP U (f a) (f b)
      have huv : U ≤ V := le_sup_left
      have hp : f a*f b ∈ V := (show Submodule.span (ZMod 2) {f a*f b} ≤ V from le_sup_right)
        (Submodule.subset_span (Set.mem_singleton _))
      exact ⟨V,step_mem hU (hm a) (hm b),huv,V.add_mem (huv hm') (V.smul_mem _ hp)⟩
  | _ :: _ :: _ :: _ => rw [he] at hg; simp at hg

def restriction {N m : ℕ} (l r : Fin m → Fin N) (gs : List Gate) (w : ℕ) : Tab m :=
  fun x => b2z ((wiresOf (oneEach (l x.1) (r x.2)) gs).getD w false)

lemma all_wires {N m} (l r : Fin m → Fin N) (gs : List Gate)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ U ∈ family m (gs.countP nlGate), initial m ≤ U ∧ ∀ w, restriction l r gs w ∈ U := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨initial m,by simp [family],le_rfl,?_⟩
    intro w
    by_cases hw : w<N
    · refine ⟨(fun i => b2z (decide (w=(l i).val)),fun _ => 0),?_⟩
      ext x
      change _ + 0 = b2z ((oneEach (l x.1) (r x.2)).getD w false)
      rw [oneEach_getD_left _ _ hw,add_zero]
    · by_cases ht : w<N+N
      · refine ⟨(fun _ => 0,fun j => b2z (decide (w-N=(r j).val))),?_⟩
        ext x
        change 0 + _ = b2z ((oneEach (l x.1) (r x.2)).getD w false)
        rw [oneEach_getD_right _ _ (Nat.le_of_not_gt hw) ht,zero_add]
      · apply (show (0 : Tab m) = restriction l r [] w from ?_) ▸ (initial m).zero_mem
        funext x
        simp only [restriction,wiresOf,List.foldl_nil]
        rw [List.getD_eq_default _ _ (by rw [oneEach_length];omega)]; rfl
  | append_singleton gs g ih =>
    obtain ⟨U,hu,hi,hm⟩ := ih (fun a ha => hlen a (by simp [ha]))
    let v := fun w (x : Fin m × Fin m) => (wiresOf (oneEach (l x.1) (r x.2)) gs).getD w false
    obtain ⟨V,hV,hUV,hg⟩ := propagate hu hi v hm g (hlen g (by simp))
    refine ⟨V,by simpa [List.countP_append,List.countP_cons,Bool.toNat] using hV,hi.trans hUV,?_⟩
    intro w
    let c := N+N+gs.length
    have hl (x : Fin m × Fin m) : (wiresOf (oneEach (l x.1) (r x.2)) gs).length = c := by rw [wiresOf_length,oneEach_length]
    by_cases hb : w<c
    · have he : restriction l r (gs++[g]) w = restriction l r gs w := by
        funext x
        simp only [restriction,wiresOf_append,List.foldl_cons,List.foldl_nil]
        rw [List.getD_append _ _ _ _ (by rw [hl];exact hb)]
      rw [he]; exact hUV (hm _)
    · by_cases he : w=c
      · subst w
        convert hg using 1
        funext x
        simp only [restriction,wiresOf_append,List.foldl_cons,List.foldl_nil]
        rw [List.getD_append_right _ _ _ _ (le_of_eq (hl x)) ,hl x,Nat.sub_self]; rfl
      · have hz : restriction l r (gs++[g]) w = 0 := by
          funext x
          simp only [restriction]
          rw [List.getD_eq_default _ _ (by rw [wiresOf_length,oneEach_length];simp;dsimp [c] at *;omega)]; rfl
        rw [hz]; exact V.zero_mem

lemma predicted {N m t} (l r : Fin m → Fin N) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hc : C.gates.countP nlGate ≤ t) :
    restriction l r C.gates C.output ∈ predictions m t := by
  classical
  obtain ⟨U,hu,_,h⟩ := all_wires l r C.gates hlen
  exact Finset.mem_biUnion.mpr ⟨U,fam_mono hc hu,mem_elems.mpr (h _)⟩
end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux

def fill {n} (a : Fin (n+1) → Fin n → ZMod 2) : Tab (n+1) :=
  fun x => Fin.lastCases (-(∑ j, a x.1 j)) (a x.1) x.2
lemma fill_sum {n} (a : Fin (n+1) → Fin n → ZMod 2) (i) : ∑ j, fill a (i,j) = 0 := by
  rw [Fin.sum_univ_castSucc]; simp [fill,zmod2_add_self]
lemma fill_inj {n} : Function.Injective (@fill n) := by
  intro a b h
  funext i j
  simpa [fill] using congrFun h (i,j.castSucc)

def mis {m} (a b : Tab m) := Finset.univ.filter (fun x => a x ≠ b x)
def flipT {m} (p : Tab m × Finset (Fin m × Fin m)) : Tab m := fun x =>
  if x ∈ p.2 then p.1 x+1 else p.1 x
lemma decode {m} (a b : Tab m) : flipT (b,mis a b) = a := by
  funext x
  have h : ∀ s t : ZMod 2, (if s=t then t else t+1)=s := by decide
  simpa [flipT, mis] using h (a x) (b x)

lemma hard_block (m k : ℕ) (hm : 32 ≤ m) (hk : 8*k ≤ m) :
    ∃ B : Tab m, (∀ i, ∑ j, B (i,j) = 0) ∧
      ∀ p ∈ predictions m k, m^2/16 < (mis B p).card := by
  classical
  cases m with
  | zero => omega
  | succ n =>
    let m := n+1
    let good := Finset.univ.image (@fill n)
    let bad := ((predictions m k) ×ˢ masks m).image flipT
    have gc : good.card = 2^(m*(m-1)) := by
      rw [Finset.card_image_of_injective _ fill_inj]
      simp [m, pow_mul, Fintype.card_fun, ZMod.card, ← pow_mul, Nat.mul_comm]
    have bc : bad.card ≤ (predictions m k).card*(masks m).card :=
      Finset.card_image_le.trans (Finset.card_product _ _).le
    have small : bad.card < good.card := by
      by_contra! h
      have he := Nat.pow_le_pow_left (h.trans bc) 16
      rw [gc,mul_pow,← pow_mul] at he
      have hh := he.trans (Nat.mul_le_mul (Nat.pow_le_pow_left (predictions_card m k) 16) (mask_count m))
      rw [← pow_mul,← pow_add] at hh
      have hl := count_gap hm hk
      have hb := (Nat.pow_lt_pow_right (by decide : 1 < 2) (by
        rw [Nat.mul_comm _ 16, Nat.mul_comm (m*(m-1)) 16]; exact hl :
         (4*m*k+k*(k-1)+2*m+k)*16+6*m^2 < m*(m-1)*16))
      omega
    obtain ⟨B,hg,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card small
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hg
    refine ⟨_,fill_sum a,?_⟩
    intro p hp
    by_contra! he
    apply hb
    exact Finset.mem_image.mpr ⟨(p,mis (fill a) p), Finset.mem_product.mpr
      ⟨hp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩,decode _ _⟩
end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
def leftI {m N : ℕ} (h : 2*m ≤ N) (i : Fin m) : Fin N := ⟨i.val, by have := i.isLt; omega⟩
def rightI {m N : ℕ} (h : 2*m ≤ N) (i : Fin m) : Fin N := ⟨m+i.val, by have := i.isLt; omega⟩

lemma block_matrix {m N : ℕ} (h : 2*m ≤ N) (B : Tab m) (hb : ∀ i, ∑ j, B (i,j) = 0) :
    ∃ P : Sq N, P*P = 1 ∧ (∀ x, ∑ j, P x j = 1) ∧
      ∀ i j, (P*P.transpose) (leftI h i) (rightI h j) = B (i,j) := by
  let D (i : Fin N) (t : Fin m) : F := if hi : i.val < m then B (⟨i.val,hi⟩,t) else 0
  let S : Sq N := fun i j => ∑ t : Fin m, if rightI h t = j then D i t else 0
  have hinj : Function.Injective (rightI h) := by intro x y hxy; apply Fin.ext; simpa [rightI,Fin.ext_iff] using hxy
  have hno (i j : Fin m) : leftI h i ≠ rightI h j := by
    intro he; have hh := congrArg Fin.val he; change i.val = m+j.val at hh; have := i.isLt; omega
  have hsr (i j : Fin N) (hi : m ≤ i.val) : S i j=0 := by
    simp [S,D,Nat.not_lt.mpr hi]
  have hsc (i j : Fin N) (hj : j.val < m) : S i j=0 := by
    have hn (t : Fin m) : rightI h t ≠ j := by intro he; have hh := congrArg Fin.val he; change m+t.val=j.val at hh; omega
    simp [S,hn]
  have hs2 : S*S=0 := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by
      by_cases hk : k.val < m
      · rw [hsc _ _ hk,zero_mul]
      · rw [hsr k j (by omega),mul_zero])
  have hsum (i : Fin N) : ∑ j, S i j=0 := by
    dsimp only [S]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    by_cases hi : i.val < m <;> simp [D,hi,hb]
  have hblock (i j : Fin m) : S (leftI h i) (rightI h j)=B (i,j) := by
    simp [S,hinj.eq_iff,D,leftI]
  refine ⟨1+S,?_,?_,?_⟩
  · simp only [add_mul,mul_add,one_mul,mul_one,hs2,add_zero,add_assoc]
    ext i j
    simp [Matrix.add_apply,zmod2_add_self]
  · intro x
    simp [Matrix.add_apply,Matrix.one_apply,Finset.sum_add_distrib,hsum]
  · intro i j
    rw [Matrix.transpose_add,Matrix.transpose_one,add_mul,one_mul,mul_add,mul_one]
    have hz : (S*S.transpose) (leftI h i) (rightI h j)=0 := by
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero (fun k _ => by rw [Matrix.transpose_apply,hsr (rightI h j) k (by simp [rightI]),mul_zero])
    simp [Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply,hno,hz,hsr _ _ (by simp [rightI] : m ≤ (rightI h j).val),hblock]

lemma b2z_nonzero (x : ZMod 2) : b2z (decide (x ≠ 0)) = x := by
  exact (by decide : ∀ a : ZMod 2, b2z (decide (a ≠ 0)) = a) x

end PEqualNP.Outside.L_meta_32043_aux
namespace PEqualNP.Outside.L_meta_32043_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

lemma fits_one {N : ℕ} [NeZero N] (G : Fin N → Fin N → Bool) (t : ℕ)
    (he : (anchor 0 0 (fun i j => b2z (G i j))).rank = (eqA N).rank) :
    Fit G 1 t ↔ (N-1)/2 ≤ t := by
  have h := main N N G 0 0 t
  rw [he] at h
  have hr := (eqA_ge (N:=N)).antisymm (eqA_le (N:=N))
  rw [← hr] at h
  constructor
  · rintro ⟨C,hb,hl,hc,hd,hv⟩
    have := h.mpr ⟨C,⟨hl,hb,hv⟩,hd,hc⟩; omega
  · intro ht
    obtain ⟨C,⟨hl,hb,hv⟩,hd,hc⟩ := h.mp (by omega)
    exact ⟨C,hb,hl,hc,hd,hv⟩

lemma fit_gram {N : ℕ} [NeZero N] (P : Sq N) (hi : P*P=1) (hs : ∀ i, ∑ j, P i j=1) (t : ℕ) :
    Fit (fun i j => decide ((P*P.transpose) i j ≠ 0)) 1 t ↔ (N-1)/2 ≤ t := by
  apply fits_one
  have he : (fun i j => b2z (decide ((P*P.transpose) i j ≠ 0))) = P*P.transpose := by
    funext i j; exact b2z_nonzero _
  have hid : (fun i j : Fin N => b2z (decide (i=j))) = (1 : Sq N) := by
    funext i j; simp [b2z,Matrix.one_apply]
  unfold eqA
  rw [he,hid]
  simpa using rank_cong_eq P 1 hi hs

end PEqualNP.Outside.L_meta_32043_aux
open PEqualNP.Outside.L_meta_32043_aux

theorem PEqualNP.Outside.L_meta_32043 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
∀ N : ℕ, 64 ≤ N →
  let F := ZMod 2
  let eqTab := fun (x y : Fin N) => decide (x = y)
  let fit := fun (G : Fin N → Fin N → Bool) (d t : ℕ) =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      (depths (N+N) C).getD C.output 0 ≤ d ∧ PEqualNP.Represents.Represents G C
  ∃ P : Matrix (Fin N) (Fin N) F,
    P*P = 1 ∧ (∀ x, ∑ j, P x j = 1) ∧
    let G := fun (x y : Fin N) => decide ((P*P.transpose) x y ≠ 0)
    (∀ t : ℕ, (fit eqTab 1 t ↔ (N-1)/2 ≤ t) ∧ (fit G 1 t ↔ (N-1)/2 ≤ t)) ∧
    fit eqTab 2 (Nat.sqrt (N-1) + 3) ∧
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C →
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) → C.gates.countP nonlinear ≤ N/16 →
      let wrong := (Finset.univ : Finset (Fin N × Fin N)).filter (fun xy =>
        C.eval (PEqualNP.Represents.oneEach xy.1 xy.2) ≠ G xy.1 xy.2)
      N^2 < 80 * wrong.card) := by
  intro nonlinear depths N hn F eqTab fit
  haveI : NeZero N := ⟨by omega⟩
  let m := N/2
  let t := N/16
  have hm : 32 ≤ m := by dsimp [m]; omega
  have ht : 8*t ≤ m := by dsimp [m,t]; omega
  have h : 2*m ≤ N := by dsimp [m]; omega
  obtain ⟨B,hB,hard⟩ := hard_block m t hm ht
  obtain ⟨P,hi,hs,hgram⟩ := block_matrix h B hB
  refine ⟨P,hi,hs,?_,depth_two,?_⟩
  · intro s
    exact ⟨fits_one eqTab s rfl,fit_gram P hi hs s⟩
  · intro C _ hl hc wrong
    let l := leftI h
    let r := rightI h
    let p := restriction l r C.gates C.output
    have hp := predicted l r C hl hc
    have hbad : m^2/16 < (mis B p).card := hard p hp
    have hw : (mis B p).card ≤ wrong.card := by
      apply Finset.card_le_card_of_injOn (fun xy => (l xy.1,r xy.2))
      · intro xy hxy
        have hne := (Finset.mem_filter.mp hxy).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        change C.eval (PEqualNP.Represents.oneEach (l xy.1) (r xy.2)) ≠ decide ((P*P.transpose) (l xy.1) (r xy.2) ≠ 0)
        rw [hgram]
        intro he
        apply hne
        change B xy = b2z (C.eval (PEqualNP.Represents.oneEach (l xy.1) (r xy.2)))
        rw [he,b2z_nonzero]
      · intro x _ y _ hxy
        apply Prod.ext
        · apply Fin.ext; exact congrArg (fun a : Fin N × Fin N => a.1.val) hxy
        · apply Fin.ext
          have hh := congrArg (fun a : Fin N × Fin N => a.2.val) hxy
          change m+x.2.val = m+y.2.val at hh
          omega
    have hmul : m^2 < 16*wrong.card := by omega
    have hu : N ≤ 2*m+1 := by dsimp [m]; omega
    have hu2 := Nat.pow_le_pow_left hu 2
    have hmm := Nat.mul_le_mul_left m hm
    nlinarith
