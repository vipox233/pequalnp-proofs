import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33615


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



private abbrev F := ZMod 2

private lemma rank_mul_le_card {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : Matrix α γ F) (Q : Matrix γ β F) :
    (P * Q).rank ≤ Fintype.card γ := by
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank F (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank F (γ → F) := LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card γ := Module.finrank_pi F

private lemma rank_add_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A B : Matrix α β F) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank F (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank F (LinearMap.range A.mulVecLin) + Module.finrank F (LinearMap.range B.mulVecLin)
  omega

private lemma rank_eq_of_mul_inv {α β α' β' : Type}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']
    (M : Matrix α β F)
    (U : Matrix α' α F) (U' : Matrix α α' F)
    (V : Matrix β β' F) (V' : Matrix β' β F)
    (hU : U' * U = 1) (hV : V * V' = 1) :
    (U * M * V).rank = M.rank := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left (U * M) V).trans (Matrix.rank_mul_le_right U M)
  · have hM : M = U' * (U * M * V) * V' := by
      calc M = (1 : Matrix α α F) * M * (1 : Matrix β β F) := by rw [Matrix.one_mul, Matrix.mul_one]
        _ = (U' * U) * M * (V * V') := by rw [hU, hV]
        _ = U' * (U * M * V) * V' := by simp only [Matrix.mul_assoc]
    conv_lhs => rw [hM]
    exact (Matrix.rank_mul_le_left (U' * (U * M * V)) V').trans
      (Matrix.rank_mul_le_right U' (U * M * V))

private lemma rank_submatrix_equiv {α β α' β' : Type}
    [Fintype α] [Fintype β] [Fintype α'] [Fintype β']
    [DecidableEq α] [DecidableEq β] [DecidableEq α'] [DecidableEq β']
    (M : Matrix α β F) (e₁ : α' ≃ α) (e₂ : β' ≃ β) :
    (M.submatrix e₁ e₂).rank = M.rank := by
  let U : Matrix α' α F := fun i' i => if e₁ i' = i then 1 else 0
  let U' : Matrix α α' F := fun i i' => if i = e₁ i' then 1 else 0
  let V : Matrix β β' F := fun j j' => if j = e₂ j' then 1 else 0
  let V' : Matrix β' β F := fun j' j => if e₂ j' = j then 1 else 0
  have hU : U' * U = 1 := by
    ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (e₁.symm i)]
    · simp [U, U']
    · intro b _ hb
      have : i ≠ e₁ b := fun h => hb (e₁.symm_apply_eq.mpr h).symm
      simp [U', this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hV : V * V' = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (e₂.symm j)]
    · simp [V, V']
    · intro b _ hb
      have : j ≠ e₂ b := fun h => hb (e₂.symm_apply_eq.mpr h).symm
      simp [V, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsub : M.submatrix e₁ e₂ = U * M * V := by
    ext i' j'
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single (e₂ j')]
    · rw [Matrix.mul_apply]
      have hv1 : V (e₂ j') j' = 1 := by simp [V]
      rw [hv1, mul_one]
      rw [Finset.sum_eq_single (e₁ i')]
      · simp [U]
      · intro b _ hb; simp [U, Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb; simp [V, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsub]
  exact rank_eq_of_mul_inv M U U' V V' hU hV

private lemma rank_fromBlocks_tl {α₁ α₂ β₁ β₂ : Type}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β₁] [DecidableEq β₂]
    (A : Matrix α₁ β₁ F) :
    (Matrix.fromBlocks A (0 : Matrix α₁ β₂ F) (0 : Matrix α₂ β₁ F) (0 : Matrix α₂ β₂ F)).rank =
      A.rank := by
  let U : Matrix (α₁ ⊕ α₂) α₁ F := fun i a => match i with | Sum.inl i₁ => if i₁ = a then 1 else 0 | Sum.inr _ => 0
  let U' : Matrix α₁ (α₁ ⊕ α₂) F := fun a i => match i with | Sum.inl i₁ => if a = i₁ then 1 else 0 | Sum.inr _ => 0
  let V : Matrix β₁ (β₁ ⊕ β₂) F := fun b j => match j with | Sum.inl j₁ => if b = j₁ then 1 else 0 | Sum.inr _ => 0
  let V' : Matrix (β₁ ⊕ β₂) β₁ F := fun j b => match j with | Sum.inl j₁ => if j₁ = b then 1 else 0 | Sum.inr _ => 0
  have hU : U' * U = 1 := by
    ext a₁ a₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [U, U']
  have hV : V * V' = 1 := by
    ext b₁ b₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [V, V']
  have heq : Matrix.fromBlocks A (0 : Matrix α₁ β₂ F) (0 : Matrix α₂ β₁ F) (0 : Matrix α₂ β₂ F) =
      U * A * V := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    cases i <;> cases j <;> simp [U, V]
  rw [heq]
  exact rank_eq_of_mul_inv A U U' V V' hU hV

private lemma rank_fromBlocks_tr {α₁ α₂ β₁ β₂ : Type}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β₁] [DecidableEq β₂]
    (B : Matrix α₁ β₂ F) :
    (Matrix.fromBlocks (0 : Matrix α₁ β₁ F) B (0 : Matrix α₂ β₁ F) (0 : Matrix α₂ β₂ F)).rank =
      B.rank := by
  let U : Matrix (α₁ ⊕ α₂) α₁ F := fun i a => match i with | Sum.inl i₁ => if i₁ = a then 1 else 0 | Sum.inr _ => 0
  let U' : Matrix α₁ (α₁ ⊕ α₂) F := fun a i => match i with | Sum.inl i₁ => if a = i₁ then 1 else 0 | Sum.inr _ => 0
  let V : Matrix β₂ (β₁ ⊕ β₂) F := fun b j => match j with | Sum.inl _ => 0 | Sum.inr j₂ => if b = j₂ then 1 else 0
  let V' : Matrix (β₁ ⊕ β₂) β₂ F := fun j b => match j with | Sum.inl _ => 0 | Sum.inr j₂ => if j₂ = b then 1 else 0
  have hU : U' * U = 1 := by
    ext a₁ a₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [U, U']
  have hV : V * V' = 1 := by
    ext b₁ b₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [V, V']
  have heq : Matrix.fromBlocks (0 : Matrix α₁ β₁ F) B (0 : Matrix α₂ β₁ F) (0 : Matrix α₂ β₂ F) =
      U * B * V := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    cases i <;> cases j <;> simp [U, V]
  rw [heq]
  exact rank_eq_of_mul_inv B U U' V V' hU hV

private lemma rank_fromBlocks_bl {α₁ α₂ β₁ β₂ : Type}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β₁] [DecidableEq β₂]
    (C : Matrix α₂ β₁ F) :
    (Matrix.fromBlocks (0 : Matrix α₁ β₁ F) (0 : Matrix α₁ β₂ F) C (0 : Matrix α₂ β₂ F)).rank =
      C.rank := by
  let U : Matrix (α₁ ⊕ α₂) α₂ F := fun i a => match i with | Sum.inl _ => 0 | Sum.inr i₂ => if i₂ = a then 1 else 0
  let U' : Matrix α₂ (α₁ ⊕ α₂) F := fun a i => match i with | Sum.inl _ => 0 | Sum.inr i₂ => if a = i₂ then 1 else 0
  let V : Matrix β₁ (β₁ ⊕ β₂) F := fun b j => match j with | Sum.inl j₁ => if b = j₁ then 1 else 0 | Sum.inr _ => 0
  let V' : Matrix (β₁ ⊕ β₂) β₁ F := fun j b => match j with | Sum.inl j₁ => if j₁ = b then 1 else 0 | Sum.inr _ => 0
  have hU : U' * U = 1 := by
    ext a₁ a₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [U, U']
  have hV : V * V' = 1 := by
    ext b₁ b₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [V, V']
  have heq : Matrix.fromBlocks (0 : Matrix α₁ β₁ F) (0 : Matrix α₁ β₂ F) C (0 : Matrix α₂ β₂ F) =
      U * C * V := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    cases i <;> cases j <;> simp [U, V]
  rw [heq]
  exact rank_eq_of_mul_inv C U U' V V' hU hV

private lemma rank_fromBlocks_br {α₁ α₂ β₁ β₂ : Type}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β₁] [DecidableEq β₂]
    (D : Matrix α₂ β₂ F) :
    (Matrix.fromBlocks (0 : Matrix α₁ β₁ F) (0 : Matrix α₁ β₂ F) (0 : Matrix α₂ β₁ F) D).rank =
      D.rank := by
  let U : Matrix (α₁ ⊕ α₂) α₂ F := fun i a => match i with | Sum.inl _ => 0 | Sum.inr i₂ => if i₂ = a then 1 else 0
  let U' : Matrix α₂ (α₁ ⊕ α₂) F := fun a i => match i with | Sum.inl _ => 0 | Sum.inr i₂ => if a = i₂ then 1 else 0
  let V : Matrix β₂ (β₁ ⊕ β₂) F := fun b j => match j with | Sum.inl _ => 0 | Sum.inr j₂ => if b = j₂ then 1 else 0
  let V' : Matrix (β₁ ⊕ β₂) β₂ F := fun j b => match j with | Sum.inl _ => 0 | Sum.inr j₂ => if j₂ = b then 1 else 0
  have hU : U' * U = 1 := by
    ext a₁ a₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [U, U']
  have hV : V * V' = 1 := by
    ext b₁ b₂
    rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
    simp [V, V']
  have heq : Matrix.fromBlocks (0 : Matrix α₁ β₁ F) (0 : Matrix α₁ β₂ F) (0 : Matrix α₂ β₁ F) D =
      U * D * V := by
    ext i j
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    cases i <;> cases j <;> simp [U, V]
  rw [heq]
  exact rank_eq_of_mul_inv D U U' V V' hU hV

private lemma rank_add_of_proj {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (D E : Matrix α β F) (PL : Matrix α α F) (PR : Matrix β β F)
    (hLD : PL * D = D) (hLE : PL * E = 0)
    (hRD : D * PR = D) (hRE : E * PR = 0) :
    (D + E).rank = D.rank + E.rank := by
  have hsup : LinearMap.range (D + E).mulVecLin =
      LinearMap.range D.mulVecLin ⊔ LinearMap.range E.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        refine ⟨PR.mulVec v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.add_mul, hRD, hRE, add_zero]
      · rintro _ ⟨v, rfl⟩
        refine ⟨(1 - PR).mulVec v, ?_⟩
        have hmul : (D + E) * (1 - PR) = E := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, hRD, hRE, add_zero, add_sub_cancel_left]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hmul]
        rfl
  have hinf : LinearMap.range D.mulVecLin ⊓ LinearMap.range E.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    change D.mulVec u = 0
    have h1 : PL.mulVec (D.mulVec u) = D.mulVec u := by
      rw [Matrix.mulVec_mulVec, hLD]
    have h2 : PL.mulVec (E.mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, hLE, Matrix.zero_mulVec]
    have hv' : E.mulVec v = D.mulVec u := hv
    rw [← h1, ← hv', h2]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range D.mulVecLin) (LinearMap.range E.mulVecLin)
  rw [← hsup, hinf, finrank_bot, add_zero] at h
  exact h

private lemma full_rank_factor {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix α β F) :
    ∃ (P : Matrix α (Fin M.rank) F) (Q : Matrix (Fin M.rank) β F)
      (L : Matrix (Fin M.rank) α F) (R : Matrix β (Fin M.rank) F),
      P * Q = M ∧ L * P = 1 ∧ Q * R = 1 := by
  let r := M.rank
  let b : Module.Basis (Fin r) F (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq F (LinearMap.range M.mulVecLin) rfl
  have hmem : ∀ k : Fin r, ∃ v : β → F, M.mulVec v = (b k).1 := by
    intro k
    obtain ⟨v, hv⟩ := (b k).2
    exact ⟨v, hv⟩
  choose rcol hrcol using hmem
  let P : Matrix α (Fin r) F := fun i k => (b k).1 i
  let R : Matrix β (Fin r) F := fun j k => rcol k j
  have hMR : M * R = P := by
    ext i k
    change ∑ j, M i j * rcol k j = (b k).1 i
    exact congrFun (hrcol k) i
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range M.mulVecLin)
  let proj : (α → F) →ₗ[F] LinearMap.range M.mulVecLin :=
    Submodule.projectionOnto (LinearMap.range M.mulVecLin) W hW
  let l : (α → F) →ₗ[F] (Fin r → F) := b.equivFun.toLinearMap.comp proj
  let L : Matrix (Fin r) α F := fun k i => l (Pi.single i 1) k
  have hLvec : ∀ v : α → F, L.mulVec v = l v := by
    intro v
    have hv : v = ∑ i : α, v i • Pi.single i (1 : F) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    ext k
    conv_rhs => rw [hv]
    rw [map_sum]
    simp [Matrix.mulVec, dotProduct, L, map_smul, Finset.sum_apply, mul_comm]
  have hLP : L * P = 1 := by
    ext k₁ k₂
    have hcol : (fun i => P i k₂) = (b k₂).1 := rfl
    have h1 : (L * P) k₁ k₂ = L.mulVec (fun i => P i k₂) k₁ := rfl
    rw [h1, hcol, hLvec]
    have hp : proj (b k₂).1 = b k₂ := Submodule.projectionOnto_apply_left hW (b k₂)
    have h2 : l (b k₂).1 k₁ = b.equivFun (b k₂) k₁ := by
      simp [l, hp]
    rw [h2, Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : k₁ = k₂
    · subst h; simp
    · simp [h, Ne.symm h]
  let Q : Matrix (Fin r) β F := L * M
  have hQR : Q * R = 1 := by
    rw [show Q * R = L * (M * R) by simp [Q, Matrix.mul_assoc], hMR, hLP]
  have hPQ : P * Q = M := by
    ext i j
    have hcol : M.mulVec (Pi.single j 1) ∈ LinearMap.range M.mulVecLin :=
      ⟨Pi.single j 1, rfl⟩
    let w : LinearMap.range M.mulVecLin := ⟨M.mulVec (Pi.single j 1), hcol⟩
    have h1 : (P * Q) i j = (P * Q).mulVec (Pi.single j 1) i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have h2 : M i j = w.1 i := by
      simp [w, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h1, h2]
    have h3 : (P * Q).mulVec (Pi.single j 1) = P.mulVec (L.mulVec w.1) := by
      simp only [Q, ← Matrix.mulVec_mulVec, w]
    rw [h3, hLvec]
    have hp : proj w.1 = w := Submodule.projectionOnto_apply_left hW w
    have hlw : l w.1 = b.equivFun w := by simp [l, hp]
    rw [hlw]
    have hsum : ∑ k : Fin r, b.equivFun w k • (b k).1 = w.1 := by
      have hr : ∑ k : Fin r, (b.repr w) k • (b k) = w := b.sum_repr w
      have hval := congrArg Subtype.val hr
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.equivFun_apply] using hval
    have hval := congrFun hsum i
    simpa [Matrix.mulVec, dotProduct, P, Finset.sum_apply, mul_comm] using hval
  exact ⟨P, Q, L, R, hPQ, hLP, hQR⟩

private lemma factor_of_rank_le_gen {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix α β F) {s : ℕ} (hs : M.rank ≤ s) :
    ∃ (L : Matrix α (Fin s) F) (R : Matrix (Fin s) β F), L * R = M := by
  obtain ⟨P, Q, _, _, hPQ, _, _⟩ := full_rank_factor M
  let L : Matrix α (Fin s) F := fun i k =>
    if hk : k.val < M.rank then P i ⟨k.val, hk⟩ else 0
  let R : Matrix (Fin s) β F := fun k j =>
    if hk : k.val < M.rank then Q ⟨k.val, hk⟩ j else 0
  refine ⟨L, R, ?_⟩
  ext i j
  rw [← hPQ, Matrix.mul_apply, Matrix.mul_apply]
  have hsplit : ∑ k : Fin s, L i k * R k j =
      ∑ k ∈ (Finset.univ : Finset (Fin s)).filter (fun k => k.val < M.rank), L i k * R k j := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hk => ?_)
    have hnot : ¬ k.val < M.rank := by simpa using hk
    simp [L, R, hnot]
  rw [hsplit]
  symm
  refine Finset.sum_bij (fun (k : Fin M.rank) _ => (⟨k.val, lt_of_lt_of_le k.isLt hs⟩ : Fin s))
    ?_ ?_ ?_ ?_
  · intro k _; simp [k.isLt]
  · intro a _ b _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro k hk
    have hlt : k.val < M.rank := (Finset.mem_filter.mp hk).2
    exact ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro k _
    simp [L, R, k.isLt]

private lemma rank_submatrix_add_le {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β F) (I : Finset α) (J : Finset β) :
    (M.submatrix id (fun j : J => j.val)).rank +
      (M.submatrix (fun i : I => i.val) id).rank ≤
      M.rank + (M.submatrix (fun i : I => i.val) (fun j : J => j.val)).rank := by
  let rI : (α → F) →ₗ[F] (I → F) :=
    { toFun := fun v i => v i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let V : Submodule F (α → F) := LinearMap.range M.mulVecLin
  let U : Submodule F (α → F) := LinearMap.range (M.submatrix id (fun j : J => j.val)).mulVecLin
  have hUV : U ≤ V := by
    rintro _ ⟨w, rfl⟩
    refine ⟨fun j => if hj : j ∈ J then w ⟨j, hj⟩ else 0, ?_⟩
    ext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
    have h1 : (∑ j : β, M i j * if hj : j ∈ J then w ⟨j, hj⟩ else 0) =
        ∑ j ∈ J, M i j * if hj : j ∈ J then w ⟨j, hj⟩ else 0 := by
      symm
      refine Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => ?_)
      simp [hj]
    rw [h1, ← Finset.sum_coe_sort J (fun j => M i j * if hj : j ∈ J then w ⟨j, hj⟩ else 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [j.2]
  have hmapV : Submodule.map rI V =
      LinearMap.range (M.submatrix (fun i : I => i.val) id).mulVecLin := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, V, rI, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨M.mulVec v, ⟨v, rfl⟩, rfl⟩
  have hmapU : Submodule.map rI U =
      LinearMap.range (M.submatrix (fun i : I => i.val) (fun j : J => j.val)).mulVecLin := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, U, rI, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨(M.submatrix id (fun j : J => j.val)).mulVec w, ⟨w, rfl⟩, rfl⟩
  let fV : V →ₗ[F] (I → F) := rI.domRestrict V
  let fU : U →ₗ[F] (I → F) := rI.domRestrict U
  have hrV : LinearMap.range fV = Submodule.map rI V := LinearMap.range_domRestrict V rI
  have hrU : LinearMap.range fU = Submodule.map rI U := LinearMap.range_domRestrict U rI
  have hker : Module.finrank F (LinearMap.ker fU) ≤ Module.finrank F (LinearMap.ker fV) := by
    let inc : LinearMap.ker fU →ₗ[F] LinearMap.ker fV :=
      { toFun := fun x => ⟨⟨x.1.1, hUV x.1.2⟩, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective inc := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1.1) h))
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have h1 := LinearMap.finrank_range_add_finrank_ker fU
  have h2 := LinearMap.finrank_range_add_finrank_ker fV
  rw [hrU, hmapU] at h1
  rw [hrV, hmapV] at h2
  have hU_rk : (M.submatrix id (fun j : J => j.val)).rank = Module.finrank F U := rfl
  have hV_rk : M.rank = Module.finrank F V := rfl
  have hI_rk : (M.submatrix (fun i : I => i.val) id).rank =
      Module.finrank F (LinearMap.range (M.submatrix (fun i : I => i.val) id).mulVecLin) := rfl
  have hIJ_rk : (M.submatrix (fun i : I => i.val) (fun j : J => j.val)).rank =
      Module.finrank F (LinearMap.range (M.submatrix (fun i : I => i.val) (fun j : J => j.val)).mulVecLin) := rfl
  omega

private noncomputable def rk {n m : ℕ} (B : Matrix (Fin n) (Fin m) F)
    (I : Finset (Fin n)) (J : Finset (Fin m)) : ℕ :=
  Matrix.rank (B.submatrix (fun i : I => i.val) (fun j : J => j.val))

private lemma rk_univ_left {n m : ℕ} (B : Matrix (Fin n) (Fin m) F) (J : Finset (Fin m)) :
    rk B Finset.univ J = (B.submatrix id (fun j : J => j.val)).rank := by
  let e : ↥(Finset.univ : Finset (Fin n)) ≃ Fin n :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact rank_submatrix_equiv (B.submatrix id (fun j : J => j.val)) e (Equiv.refl _)

private lemma rk_univ_right {n m : ℕ} (B : Matrix (Fin n) (Fin m) F) (I : Finset (Fin n)) :
    rk B I Finset.univ = (B.submatrix (fun i : I => i.val) id).rank := by
  let e : ↥(Finset.univ : Finset (Fin m)) ≃ Fin m :=
    { toFun := Subtype.val
      invFun := fun j => ⟨j, Finset.mem_univ j⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact rank_submatrix_equiv (B.submatrix (fun i : I => i.val) id) (Equiv.refl _) e

private lemma rk_strip_le {n m : ℕ} (M : Matrix (Fin n) (Fin m) F)
    (R : Finset (Fin n)) (C : Finset (Fin m)) :
    rk M Finset.univ C + rk M R Finset.univ ≤ M.rank + rk M R C := by
  rw [rk_univ_left, rk_univ_right]
  exact rank_submatrix_add_le M R C

private lemma rk_panel_le {n m : ℕ} (M : Matrix (Fin n) (Fin m) F)
    (R I : Finset (Fin n)) (C J : Finset (Fin m))
    (hRI : R ⊆ I) (hCJ : C ⊆ J) :
    rk M Finset.univ C + rk M R Finset.univ + rk M I J ≤
      M.rank + rk M I C + rk M R J := by
  have h1 := rk_strip_le M I C
  let MI : Matrix I (Fin m) F := M.submatrix (fun i : I => i.val) id
  let R' : Finset I := Finset.univ.filter (fun i : I => i.val ∈ R)
  have h2 := rank_submatrix_add_le MI R' J
  let eR : ↥R' ≃ ↥R :=
    { toFun := fun x => ⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩
      invFun := fun r => ⟨⟨r.1, hRI r.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2a : (MI.submatrix id (fun j : J => j.val)).rank = rk M I J := rfl
  have h2b : (MI.submatrix (fun i : R' => i.val) id).rank = rk M R Finset.univ := by
    rw [rk_univ_right]
    have hsub : MI.submatrix (fun i : R' => i.val) id =
        (M.submatrix (fun i : R => i.val) id).submatrix eR (Equiv.refl _) := rfl
    rw [hsub]
    exact rank_submatrix_equiv (M.submatrix (fun i : R => i.val) id) eR (Equiv.refl _)
  have h2c : MI.rank = rk M I Finset.univ := (rk_univ_right M I).symm
  have h2d : (MI.submatrix (fun i : R' => i.val) (fun j : J => j.val)).rank = rk M R J := by
    have hsub : MI.submatrix (fun i : R' => i.val) (fun j : J => j.val) =
        (M.submatrix (fun i : R => i.val) (fun j : J => j.val)).submatrix eR (Equiv.refl _) := rfl
    rw [hsub]
    exact rank_submatrix_equiv (M.submatrix (fun i : R => i.val) (fun j : J => j.val))
      eR (Equiv.refl _)
  rw [h2a, h2b, h2c, h2d] at h2
  have _ := hCJ
  omega

private lemma zero_corner_decomp {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (Xa : Matrix α γ F) (Ya : Matrix δ β F) (Za : Matrix α β F) :
    ∃ (Pa : Matrix γ β F) (Qa : Matrix α δ F) (Zrem : Matrix α β F),
      Za = Xa * Pa + Qa * Ya + Zrem ∧
      (Matrix.fromBlocks (0 : Matrix δ γ F) Ya Xa Za).rank =
        Xa.rank + Ya.rank + Zrem.rank := by
  obtain ⟨PX, QX, LX, RX, hPQX, hLPX, hQRX⟩ := full_rank_factor Xa
  obtain ⟨PY, QY, LY, RY, hPQY, hLPY, hQRY⟩ := full_rank_factor Ya
  let piX : Matrix α α F := PX * LX
  let rhoY : Matrix β β F := RY * QY
  let Pa : Matrix γ β F := RX * LX * Za
  let Qa : Matrix α δ F := (1 - piX) * Za * RY * LY
  let Zrem : Matrix α β F := (1 - piX) * Za * (1 - rhoY)
  have hXaPa : Xa * Pa = piX * Za := by
    calc Xa * Pa = (PX * QX) * (RX * LX * Za) := congrArg (· * Pa) hPQX.symm
      _ = PX * ((QX * RX) * (LX * Za)) := by simp only [Matrix.mul_assoc]
      _ = PX * (LX * Za) := by rw [hQRX, Matrix.one_mul]
      _ = piX * Za := by simp only [piX, Matrix.mul_assoc]
  have hQaYa : Qa * Ya = (1 - piX) * Za * rhoY := by
    calc Qa * Ya = ((1 - piX) * Za * RY * LY) * (PY * QY) := congrArg (Qa * ·) hPQY.symm
      _ = (1 - piX) * Za * RY * ((LY * PY) * QY) := by simp only [Matrix.mul_assoc]
      _ = (1 - piX) * Za * RY * QY := by rw [hLPY, Matrix.one_mul]
      _ = (1 - piX) * Za * rhoY := by simp only [rhoY, Matrix.mul_assoc]
  have hZa : Za = Xa * Pa + Qa * Ya + Zrem := by
    rw [hXaPa, hQaYa]
    simp only [Zrem, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have hpiX_Xa : piX * Xa = Xa := by
    calc piX * Xa = (PX * LX) * (PX * QX) := congrArg (piX * ·) hPQX.symm
      _ = PX * ((LX * PX) * QX) := by simp only [Matrix.mul_assoc]
      _ = PX * QX := by rw [hLPX, Matrix.one_mul]
      _ = Xa := hPQX
  have hpiX_sq : piX * piX = piX := by
    calc piX * piX = PX * ((LX * PX) * LX) := by simp only [piX, Matrix.mul_assoc]
      _ = piX := by rw [hLPX, Matrix.one_mul]
  have hpiX_rem : piX * Zrem = 0 := by
    have h0 : piX * (1 - piX) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hpiX_sq, sub_self]
    calc piX * Zrem = (piX * (1 - piX)) * (Za * (1 - rhoY)) := by simp only [Zrem, Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.zero_mul]
  have hYa_rhoY : Ya * rhoY = Ya := by
    calc Ya * rhoY = (PY * QY) * (RY * QY) := congrArg (· * rhoY) hPQY.symm
      _ = PY * ((QY * RY) * QY) := by simp only [Matrix.mul_assoc]
      _ = PY * QY := by rw [hQRY, Matrix.one_mul]
      _ = Ya := hPQY
  have hrhoY_sq : rhoY * rhoY = rhoY := by
    calc rhoY * rhoY = RY * ((QY * RY) * QY) := by simp only [rhoY, Matrix.mul_assoc]
      _ = rhoY := by rw [hQRY, Matrix.one_mul]
  have hrem_rhoY : Zrem * rhoY = 0 := by
    have h0 : (1 - rhoY) * rhoY = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hrhoY_sq, sub_self]
    calc Zrem * rhoY = ((1 - piX) * Za) * ((1 - rhoY) * rhoY) := by simp only [Zrem, Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  let U : Matrix (δ ⊕ α) (δ ⊕ α) F := Matrix.fromBlocks 1 0 (-Qa) 1
  let U' : Matrix (δ ⊕ α) (δ ⊕ α) F := Matrix.fromBlocks 1 0 Qa 1
  let V : Matrix (γ ⊕ β) (γ ⊕ β) F := Matrix.fromBlocks 1 (-Pa) 0 1
  let V' : Matrix (γ ⊕ β) (γ ⊕ β) F := Matrix.fromBlocks 1 Pa 0 1
  have hU : U' * U = 1 := by
    simp [U, U', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hV : V * V' = 1 := by
    simp [V, V', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hmul : U * Matrix.fromBlocks (0 : Matrix δ γ F) Ya Xa Za * V =
      Matrix.fromBlocks 0 Ya Xa Zrem := by
    simp only [U, V, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, add_zero, zero_add]
    refine Matrix.fromBlocks_inj.mpr ⟨rfl, by simp, rfl, ?_⟩
    rw [hZa]
    abel
  have hrank1 : (Matrix.fromBlocks (0 : Matrix δ γ F) Ya Xa Za).rank =
      (Matrix.fromBlocks (0 : Matrix δ γ F) Ya Xa Zrem).rank := by
    rw [← hmul]
    exact (rank_eq_of_mul_inv _ U U' V V' hU hV).symm
  let E1 : Matrix (δ ⊕ α) (γ ⊕ β) F := Matrix.fromBlocks 0 Ya 0 0
  let E2 : Matrix (δ ⊕ α) (γ ⊕ β) F := Matrix.fromBlocks 0 0 Xa 0
  let E3 : Matrix (δ ⊕ α) (γ ⊕ β) F := Matrix.fromBlocks 0 0 0 Zrem
  have hE123 : Matrix.fromBlocks (0 : Matrix δ γ F) Ya Xa Zrem = E1 + (E2 + E3) := by
    simp [E1, E2, E3, Matrix.fromBlocks_add]
  have hr1 : (E1 + (E2 + E3)).rank = E1.rank + (E2 + E3).rank := by
    refine rank_add_of_proj E1 (E2 + E3)
      (Matrix.fromBlocks (1 : Matrix δ δ F) 0 0 0)
      (Matrix.fromBlocks (0 : Matrix γ γ F) 0 0 rhoY) ?_ ?_ ?_ ?_
    · simp [E1, Matrix.fromBlocks_multiply]
    · simp [E2, E3, Matrix.fromBlocks_add, Matrix.fromBlocks_multiply]
    · simp [E1, Matrix.fromBlocks_multiply, hYa_rhoY]
    · simp [E2, E3, Matrix.fromBlocks_add, Matrix.fromBlocks_multiply, hrem_rhoY]
  have hr2 : (E2 + E3).rank = E2.rank + E3.rank := by
    refine rank_add_of_proj E2 E3
      (Matrix.fromBlocks (0 : Matrix δ δ F) 0 0 piX)
      (Matrix.fromBlocks (1 : Matrix γ γ F) 0 0 0) ?_ ?_ ?_ ?_
    · simp [E2, Matrix.fromBlocks_multiply, hpiX_Xa]
    · simp [E3, Matrix.fromBlocks_multiply, hpiX_rem]
    · simp [E2, Matrix.fromBlocks_multiply]
    · simp [E3, Matrix.fromBlocks_multiply]
  refine ⟨Pa, Qa, Zrem, hZa, ?_⟩
  rw [hrank1, hE123, hr1, hr2, rank_fromBlocks_tr, rank_fromBlocks_bl, rank_fromBlocks_br]
  omega

private lemma schur_rank_split {n m : ℕ}
    (A B : Matrix (Fin n) (Fin m) F)
    (R Ibar : Finset (Fin n)) (C Jbar : Finset (Fin m))
    (hRI : Disjoint R Ibar) (hCJ : Disjoint C Jbar)
    (P0 : Matrix ↥R (Fin (rk A R C)) F) (Q0 : Matrix (Fin (rk A R C)) ↥C F)
    (L0 : Matrix (Fin (rk A R C)) ↥R F) (R0 : Matrix ↥C (Fin (rk A R C)) F)
    (hPQ0 : P0 * Q0 = A.submatrix Subtype.val Subtype.val)
    (hLP0 : L0 * P0 = 1) (hQR0 : Q0 * R0 = 1)
    (hBR : ∀ i ∈ R, ∀ j ∈ C ∪ Jbar, B i j = A i j)
    (hBC : ∀ i ∈ R ∪ Ibar, ∀ j ∈ C, B i j = A i j) :
    let S0 : Matrix (Fin n) (Fin m) F :=
      (A.submatrix id (fun j : C => j.val) * R0) * (L0 * A.submatrix (fun i : R => i.val) id)
    rk B (R ∪ Ibar) (C ∪ Jbar) =
      rk A R C +
        (Matrix.fromBlocks (0 : Matrix ↥R ↥C F)
          ((B - S0).submatrix Subtype.val Subtype.val : Matrix ↥R ↥Jbar F)
          ((B - S0).submatrix Subtype.val Subtype.val : Matrix ↥Ibar ↥C F)
          ((B - S0).submatrix Subtype.val Subtype.val : Matrix ↥Ibar ↥Jbar F)).rank := by
  intro S0
  let eI : (↥R ⊕ ↥Ibar) ≃ ↥(R ∪ Ibar) :=
    { toFun := fun x => match x with
        | Sum.inl r => ⟨r.1, Finset.mem_union_left Ibar r.2⟩
        | Sum.inr i => ⟨i.1, Finset.mem_union_right R i.2⟩
      invFun := fun x =>
        if hx : x.1 ∈ R then Sum.inl ⟨x.1, hx⟩
        else Sum.inr ⟨x.1, (Finset.mem_union.mp x.2).resolve_left hx⟩
      left_inv := fun x => by
        cases x with
        | inl r => simp [r.2]
        | inr i =>
          have hi : i.1 ∉ R := Finset.disjoint_right.mp hRI i.2
          simp [hi]
      right_inv := fun x => by
        by_cases hx : x.1 ∈ R <;> simp [hx] }
  let eJ : (↥C ⊕ ↥Jbar) ≃ ↥(C ∪ Jbar) :=
    { toFun := fun x => match x with
        | Sum.inl c => ⟨c.1, Finset.mem_union_left Jbar c.2⟩
        | Sum.inr j => ⟨j.1, Finset.mem_union_right C j.2⟩
      invFun := fun x =>
        if hx : x.1 ∈ C then Sum.inl ⟨x.1, hx⟩
        else Sum.inr ⟨x.1, (Finset.mem_union.mp x.2).resolve_left hx⟩
      left_inv := fun x => by
        cases x with
        | inl c => simp [c.2]
        | inr j =>
          have hj : j.1 ∉ C := Finset.disjoint_right.mp hCJ j.2
          simp [hj]
      right_inv := fun x => by
        by_cases hx : x.1 ∈ C <;> simp [hx] }
  let A00 : Matrix ↥R ↥C F := A.submatrix Subtype.val Subtype.val
  let A01 : Matrix ↥R ↥Jbar F := A.submatrix Subtype.val Subtype.val
  let A10 : Matrix ↥Ibar ↥C F := A.submatrix Subtype.val Subtype.val
  let B11 : Matrix ↥Ibar ↥Jbar F := B.submatrix Subtype.val Subtype.val
  have hPQ0' : P0 * Q0 = A00 := hPQ0
  have hsub : (B.submatrix (fun i : ↥(R ∪ Ibar) => i.val)
      (fun j : ↥(C ∪ Jbar) => j.val)).submatrix eI eJ =
      Matrix.fromBlocks A00 A01 A10 B11 := by
    ext x y
    cases x with
    | inl r =>
      cases y with
      | inl c =>
        simp [eI, eJ, A00, hBR r.1 r.2 c.1 (Finset.mem_union_left _ c.2)]
      | inr j =>
        simp [eI, eJ, A01, hBR r.1 r.2 j.1 (Finset.mem_union_right _ j.2)]
    | inr i =>
      cases y with
      | inl c =>
        simp [eI, eJ, A10, hBC i.1 (Finset.mem_union_right _ i.2) c.1 c.2]
      | inr j =>
        simp [eI, eJ, B11]
  have hr_eq : rk B (R ∪ Ibar) (C ∪ Jbar) = (Matrix.fromBlocks A00 A01 A10 B11).rank := by
    rw [← hsub]
    exact (rank_submatrix_equiv _ eI eJ).symm
  have hS0_01 : S0.submatrix (fun r : ↥R => r.val) (fun j : ↥Jbar => j.val) = P0 * L0 * A01 := by
    have hAR0 : A00 * R0 = P0 := by
      calc A00 * R0 = (P0 * Q0) * R0 := congrArg (· * R0) hPQ0'.symm
        _ = P0 * (Q0 * R0) := Matrix.mul_assoc _ _ _
        _ = P0 := by rw [hQR0, Matrix.mul_one]
    ext r j
    calc S0 r.1 j.1 = ((A00 * R0) * (L0 * A01)) r j := by
          simp [S0, A00, A01, Matrix.mul_apply]
      _ = (P0 * L0 * A01) r j := by rw [hAR0, Matrix.mul_assoc]
  have hS0_10 : S0.submatrix (fun i : ↥Ibar => i.val) (fun c : ↥C => c.val) = A10 * R0 * Q0 := by
    have hL0A : L0 * A00 = Q0 := by
      calc L0 * A00 = L0 * (P0 * Q0) := congrArg (L0 * ·) hPQ0'.symm
        _ = (L0 * P0) * Q0 := (Matrix.mul_assoc _ _ _).symm
        _ = Q0 := by rw [hLP0, Matrix.one_mul]
    ext i c
    calc S0 i.1 c.1 = ((A10 * R0) * (L0 * A00)) i c := by
          simp [S0, A00, A10, Matrix.mul_apply]
      _ = (A10 * R0 * Q0) i c := by rw [hL0A, Matrix.mul_assoc]
  have hS0_11 : S0.submatrix (fun i : ↥Ibar => i.val) (fun j : ↥Jbar => j.val) =
      A10 * R0 * L0 * A01 := by
    ext i j
    have hassoc : (A10 * R0) * (L0 * A01) = A10 * R0 * L0 * A01 := by simp only [Matrix.mul_assoc]
    rw [← hassoc]
    simp [S0, A10, A01, Matrix.mul_apply]
  let B01' : Matrix ↥R ↥Jbar F := (B - S0).submatrix Subtype.val Subtype.val
  let B10' : Matrix ↥Ibar ↥C F := (B - S0).submatrix Subtype.val Subtype.val
  let B11' : Matrix ↥Ibar ↥Jbar F := (B - S0).submatrix Subtype.val Subtype.val
  have hB01' : B01' = A01 - P0 * L0 * A01 := by
    ext r j
    change B r.1 j.1 - S0 r.1 j.1 = A01 r j - (P0 * L0 * A01) r j
    rw [hBR r.1 r.2 j.1 (Finset.mem_union_right _ j.2)]
    exact congrArg (A r.1 j.1 - ·) (congrFun (congrFun hS0_01 r) j)
  have hB10' : B10' = A10 - A10 * R0 * Q0 := by
    ext i c
    change B i.1 c.1 - S0 i.1 c.1 = A10 i c - (A10 * R0 * Q0) i c
    rw [hBC i.1 (Finset.mem_union_right _ i.2) c.1 c.2]
    exact congrArg (A i.1 c.1 - ·) (congrFun (congrFun hS0_10 i) c)
  have hB11' : B11' = B11 - A10 * R0 * L0 * A01 := by
    ext i j
    change B i.1 j.1 - S0 i.1 j.1 = B11 i j - (A10 * R0 * L0 * A01) i j
    exact congrArg (B i.1 j.1 - ·) (congrFun (congrFun hS0_11 i) j)
  let U : Matrix (↥R ⊕ ↥Ibar) (↥R ⊕ ↥Ibar) F := Matrix.fromBlocks 1 0 (-(A10 * R0 * L0)) 1
  let U' : Matrix (↥R ⊕ ↥Ibar) (↥R ⊕ ↥Ibar) F := Matrix.fromBlocks 1 0 (A10 * R0 * L0) 1
  let V : Matrix (↥C ⊕ ↥Jbar) (↥C ⊕ ↥Jbar) F := Matrix.fromBlocks 1 (-(R0 * L0 * A01)) 0 1
  let V' : Matrix (↥C ⊕ ↥Jbar) (↥C ⊕ ↥Jbar) F := Matrix.fromBlocks 1 (R0 * L0 * A01) 0 1
  have hU : U' * U = 1 := by
    simp [U, U', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hV : V * V' = 1 := by
    simp [V, V', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  have hA00RL : A00 * (R0 * L0 * A01) = P0 * L0 * A01 := by
    calc A00 * (R0 * L0 * A01) = (P0 * Q0) * (R0 * L0 * A01) := congrArg (· * (R0 * L0 * A01)) hPQ0'.symm
      _ = P0 * ((Q0 * R0) * (L0 * A01)) := by simp only [Matrix.mul_assoc]
      _ = P0 * L0 * A01 := by rw [hQR0, Matrix.one_mul, Matrix.mul_assoc]
  have hRLA00 : A10 * R0 * L0 * A00 = A10 * R0 * Q0 := by
    calc A10 * R0 * L0 * A00 = (A10 * R0 * L0) * (P0 * Q0) := congrArg ((A10 * R0 * L0) * ·) hPQ0'.symm
      _ = A10 * R0 * ((L0 * P0) * Q0) := by simp only [Matrix.mul_assoc]
      _ = A10 * R0 * Q0 := by rw [hLP0, Matrix.one_mul]
  have hMid : A10 * R0 * L0 * A00 * (R0 * L0 * A01) = A10 * R0 * L0 * A01 := by
    calc A10 * R0 * L0 * A00 * (R0 * L0 * A01)
        = (A10 * R0 * L0 * A00) * (R0 * L0 * A01) := rfl
      _ = (A10 * R0 * Q0) * (R0 * L0 * A01) := congrArg (· * (R0 * L0 * A01)) hRLA00
      _ = A10 * R0 * ((Q0 * R0) * (L0 * A01)) := by simp only [Matrix.mul_assoc]
      _ = A10 * R0 * L0 * A01 := by rw [hQR0, Matrix.one_mul]; simp only [Matrix.mul_assoc]
  have hmul : U * Matrix.fromBlocks A00 A01 A10 B11 * V =
      Matrix.fromBlocks A00 0 0 0 + Matrix.fromBlocks 0 B01' B10' B11' := by
    simp only [U, V, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
      zero_add, add_zero]
    refine Matrix.fromBlocks_inj.mpr ⟨rfl, ?_, ?_, ?_⟩
    · rw [hB01', hA00RL, sub_eq_add_neg, add_comm]
    · rw [hB10', hRLA00, sub_eq_add_neg, add_comm]
    · simp only [Matrix.add_mul, Matrix.neg_mul, hMid, hB11']
      simp only [Matrix.mul_assoc]
      abel
  have hL0_B01' : L0 * B01' = 0 := by
    rw [hB01', Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hLP0, Matrix.one_mul, sub_self]
  have hB10'_R0 : B10' * R0 = 0 := by
    rw [hB10', Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQR0, Matrix.mul_one, sub_self]
  have hPL_A00 : (P0 * L0) * A00 = A00 := by
    calc (P0 * L0) * A00 = (P0 * L0) * (P0 * Q0) := congrArg ((P0 * L0) * ·) hPQ0'.symm
      _ = P0 * ((L0 * P0) * Q0) := by simp only [Matrix.mul_assoc]
      _ = P0 * Q0 := by rw [hLP0, Matrix.one_mul]
      _ = A00 := hPQ0'
  have hA00_PR : A00 * (R0 * Q0) = A00 := by
    calc A00 * (R0 * Q0) = (P0 * Q0) * (R0 * Q0) := congrArg (· * (R0 * Q0)) hPQ0'.symm
      _ = P0 * ((Q0 * R0) * Q0) := by simp only [Matrix.mul_assoc]
      _ = P0 * Q0 := by rw [hQR0, Matrix.one_mul]
      _ = A00 := hPQ0'
  have hsplit : (Matrix.fromBlocks A00 (0 : Matrix ↥R ↥Jbar F) (0 : Matrix ↥Ibar ↥C F)
      (0 : Matrix ↥Ibar ↥Jbar F) + Matrix.fromBlocks 0 B01' B10' B11').rank =
      (Matrix.fromBlocks A00 (0 : Matrix ↥R ↥Jbar F) (0 : Matrix ↥Ibar ↥C F)
        (0 : Matrix ↥Ibar ↥Jbar F)).rank +
      (Matrix.fromBlocks (0 : Matrix ↥R ↥C F) B01' B10' B11').rank := by
    refine rank_add_of_proj _ _
      (Matrix.fromBlocks (P0 * L0) (0 : Matrix ↥R ↥Ibar F) 0 0)
      (Matrix.fromBlocks (R0 * Q0) (0 : Matrix ↥C ↥Jbar F) 0 0) ?_ ?_ ?_ ?_
    · simp [Matrix.fromBlocks_multiply, hPL_A00]
    · simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, hL0_B01']
    · simp [Matrix.fromBlocks_multiply, hA00_PR]
    · simp [Matrix.fromBlocks_multiply, ← Matrix.mul_assoc, hB10'_R0]
  rw [hr_eq, ← rank_eq_of_mul_inv (Matrix.fromBlocks A00 A01 A10 B11) U U' V V' hU hV,
    hmul, hsplit, rank_fromBlocks_tl]
  rfl

private theorem block_completion {n m d k : ℕ}
    (A : Matrix (Fin n) (Fin m) F)
    (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d))
    (B : Fin d → Matrix (Fin n) (Fin m) F)
    (hB_out : ∀ a i j, (row i ≠ some a ∨ col j ≠ some a) → B a i j = A i j) :
    let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
    let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
    let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
    let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
    let strips := rk A Finset.univ C + rk A R Finset.univ
    strips ≤ k + rk A R C →
    (∀ a : Fin d, strips + rk (B a) (rows a) (cols a) ≤
      k + rk A (rows a) C + rk A R (cols a)) →
    ∃ M : Matrix (Fin n) (Fin m) F,
      M.rank ≤ k ∧
      (∀ i j, (row i = none ∨ col j = none) → M i j = A i j) ∧
      (∀ a i j, row i = some a → col j = some a → M i j = B a i j) := by
  intro R C rows cols strips hstrip hpanel
  let r0 := rk A R C
  obtain ⟨P0, Q0, L0, R0, hPQ0, hLP0, hQR0⟩ := full_rank_factor
    (A.submatrix (fun i : R => i.val) (fun j : C => j.val))
  let S0 : Matrix (Fin n) (Fin m) F :=
    (A.submatrix id (fun j : C => j.val) * R0) * (L0 * A.submatrix (fun i : R => i.val) id)
  let A' : Matrix (Fin n) (Fin m) F := A - S0
  let Rbar : Finset (Fin n) := Finset.univ.filter (fun i => row i ≠ none)
  let Cbar : Finset (Fin m) := Finset.univ.filter (fun j => col j ≠ none)
  have hRRbar : Disjoint R Rbar := by
    rw [Finset.disjoint_left]
    intro i hi h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp hi).2
  have hCCbar : Disjoint C Cbar := by
    rw [Finset.disjoint_left]
    intro j hj h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp hj).2
  have hR_union : R ∪ Rbar = Finset.univ := by
    ext i; simp only [R, Rbar, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact em (row i = none)
  have hC_union : C ∪ Cbar = Finset.univ := by
    ext j; simp only [C, Cbar, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact em (col j = none)
  let X : Matrix ↥Rbar ↥C F := A'.submatrix Subtype.val Subtype.val
  let Y : Matrix ↥R ↥Cbar F := A'.submatrix Subtype.val Subtype.val
  have hrkX : rk A Finset.univ C = r0 + X.rank := by
    have h := schur_rank_split A A R Rbar C ∅ hRRbar (Finset.disjoint_empty_right C)
      P0 Q0 L0 R0 hPQ0 hLP0 hQR0 (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    dsimp only at h
    rw [hR_union, Finset.union_empty] at h
    rw [h]
    congr 1
    have h01 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥R ↥(∅ : Finset (Fin m)) F) = 0 := by
      ext _ j; exact False.elim (Finset.notMem_empty j.1 j.2)
    have h11 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥Rbar ↥(∅ : Finset (Fin m)) F) = 0 := by
      ext _ j; exact False.elim (Finset.notMem_empty j.1 j.2)
    change (Matrix.fromBlocks 0 ((A - S0).submatrix Subtype.val Subtype.val) X
      ((A - S0).submatrix Subtype.val Subtype.val)).rank = X.rank
    rw [h01, h11, rank_fromBlocks_bl]
  have hrkY : rk A R Finset.univ = r0 + Y.rank := by
    have h := schur_rank_split A A R ∅ C Cbar (Finset.disjoint_empty_right R) hCCbar
      P0 Q0 L0 R0 hPQ0 hLP0 hQR0 (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    dsimp only at h
    rw [hC_union, Finset.union_empty] at h
    rw [h]
    congr 1
    have h10 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥(∅ : Finset (Fin n)) ↥C F) = 0 := by
      ext i _; exact False.elim (Finset.notMem_empty i.1 i.2)
    have h11 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥(∅ : Finset (Fin n)) ↥Cbar F) = 0 := by
      ext i _; exact False.elim (Finset.notMem_empty i.1 i.2)
    change (Matrix.fromBlocks 0 Y ((A - S0).submatrix Subtype.val Subtype.val)
      ((A - S0).submatrix Subtype.val Subtype.val)).rank = Y.rank
    rw [h10, h11, rank_fromBlocks_tr]
  have hk_ge : r0 + X.rank + Y.rank ≤ k := by
    have : strips = (r0 + X.rank) + (r0 + Y.rank) := by simp [strips, hrkX, hrkY]
    omega
  let s : ℕ := k - (r0 + X.rank + Y.rank)
  let Ra : Fin d → Finset (Fin n) := fun a => Finset.univ.filter (fun i => row i = some a)
  let Ca : Fin d → Finset (Fin m) := fun a => Finset.univ.filter (fun j => col j = some a)
  have hpiece : ∀ a : Fin d,
      ∃ (Pa : Matrix ↥C ↥(Ca a) F) (Qa : Matrix ↥(Ra a) ↥R F)
        (La : Matrix ↥(Ra a) (Fin s) F) (RaM : Matrix (Fin s) ↥(Ca a) F),
        (B a - S0).submatrix (fun i : Ra a => i.val) (fun j : Ca a => j.val) =
          (A'.submatrix (fun i : Ra a => i.val) (fun c : C => c.val)) * Pa +
          Qa * (A'.submatrix (fun r : R => r.val) (fun j : Ca a => j.val)) +
          La * RaM := by
    intro a
    have hRRa : Disjoint R (Ra a) := by
      rw [Finset.disjoint_left]
      intro i hi h2
      have h1 := (Finset.mem_filter.mp hi).2
      have h2' := (Finset.mem_filter.mp h2).2
      rw [h1] at h2'; simp at h2'
    have hCCa : Disjoint C (Ca a) := by
      rw [Finset.disjoint_left]
      intro j hj h2
      have h1 := (Finset.mem_filter.mp hj).2
      have h2' := (Finset.mem_filter.mp h2).2
      rw [h1] at h2'; simp at h2'
    let Xa : Matrix ↥(Ra a) ↥C F := A'.submatrix Subtype.val Subtype.val
    let Ya : Matrix ↥R ↥(Ca a) F := A'.submatrix Subtype.val Subtype.val
    let Za : Matrix ↥(Ra a) ↥(Ca a) F := (B a - S0).submatrix Subtype.val Subtype.val
    have hrkXa : rk A (rows a) C = r0 + Xa.rank := by
      have h := schur_rank_split A A R (Ra a) C ∅ hRRa (Finset.disjoint_empty_right C)
        P0 Q0 L0 R0 hPQ0 hLP0 hQR0 (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      dsimp only at h
      rw [Finset.union_empty] at h
      rw [show rows a = R ∪ Ra a from rfl, h]
      congr 1
      have h01 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥R ↥(∅ : Finset (Fin m)) F) = 0 := by
        ext _ j; exact False.elim (Finset.notMem_empty j.1 j.2)
      have h11 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥(Ra a) ↥(∅ : Finset (Fin m)) F) = 0 := by
        ext _ j; exact False.elim (Finset.notMem_empty j.1 j.2)
      change (Matrix.fromBlocks 0 ((A - S0).submatrix Subtype.val Subtype.val) Xa
        ((A - S0).submatrix Subtype.val Subtype.val)).rank = Xa.rank
      rw [h01, h11, rank_fromBlocks_bl]
    have hrkYa : rk A R (cols a) = r0 + Ya.rank := by
      have h := schur_rank_split A A R ∅ C (Ca a) (Finset.disjoint_empty_right R) hCCa
        P0 Q0 L0 R0 hPQ0 hLP0 hQR0 (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      dsimp only at h
      rw [Finset.union_empty] at h
      rw [show cols a = C ∪ Ca a from rfl, h]
      congr 1
      have h10 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥(∅ : Finset (Fin n)) ↥C F) = 0 := by
        ext i _; exact False.elim (Finset.notMem_empty i.1 i.2)
      have h11 : ((A - S0).submatrix Subtype.val Subtype.val : Matrix ↥(∅ : Finset (Fin n)) ↥(Ca a) F) = 0 := by
        ext i _; exact False.elim (Finset.notMem_empty i.1 i.2)
      change (Matrix.fromBlocks 0 Ya ((A - S0).submatrix Subtype.val Subtype.val)
        ((A - S0).submatrix Subtype.val Subtype.val)).rank = Ya.rank
      rw [h10, h11, rank_fromBlocks_tr]
    have hBaR : ∀ i ∈ R, ∀ j ∈ C ∪ Ca a, B a i j = A i j := by
      intro i hi j _
      apply hB_out a i j
      left
      rw [(Finset.mem_filter.mp hi).2]
      simp
    have hBaC : ∀ i ∈ R ∪ Ra a, ∀ j ∈ C, B a i j = A i j := by
      intro i _ j hj
      apply hB_out a i j
      right
      rw [(Finset.mem_filter.mp hj).2]
      simp
    have hrkBa : rk (B a) (rows a) (cols a) = r0 + (Matrix.fromBlocks 0 Ya Xa Za).rank := by
      have h := schur_rank_split A (B a) R (Ra a) C (Ca a) hRRa hCCa
        P0 Q0 L0 R0 hPQ0 hLP0 hQR0 hBaR hBaC
      dsimp only at h
      rw [show rows a = R ∪ Ra a from rfl, show cols a = C ∪ Ca a from rfl, h]
      congr 1
      have h01 : ((B a - S0).submatrix Subtype.val Subtype.val : Matrix ↥R ↥(Ca a) F) = Ya := by
        ext r j
        change B a r.1 j.1 - S0 r.1 j.1 = A r.1 j.1 - S0 r.1 j.1
        rw [hBaR r.1 r.2 j.1 (Finset.mem_union_right _ j.2)]
      have h10 : ((B a - S0).submatrix Subtype.val Subtype.val : Matrix ↥(Ra a) ↥C F) = Xa := by
        ext i c
        change B a i.1 c.1 - S0 i.1 c.1 = A i.1 c.1 - S0 i.1 c.1
        rw [hBaC i.1 (Finset.mem_union_right _ i.2) c.1 c.2]
      change (Matrix.fromBlocks 0 ((B a - S0).submatrix Subtype.val Subtype.val)
        ((B a - S0).submatrix Subtype.val Subtype.val) Za).rank =
        (Matrix.fromBlocks 0 Ya Xa Za).rank
      rw [h01, h10]
    obtain ⟨Pa, Qa, Zrem, hZa, hZrk⟩ := zero_corner_decomp Xa Ya Za
    have hrem_le : Zrem.rank ≤ s := by
      have hp := hpanel a
      rw [show strips = rk A Finset.univ C + rk A R Finset.univ from rfl,
        hrkX, hrkY, hrkBa, hrkXa, hrkYa, hZrk] at hp
      omega
    obtain ⟨La, RaM, hLR⟩ := factor_of_rank_le_gen Zrem hrem_le
    refine ⟨Pa, Qa, La, RaM, ?_⟩
    exact hZa.trans (by rw [hLR])
  choose Pa Qa La RaM hpiece_eq using hpiece
  let P : Matrix ↥C ↥Cbar F := fun c j =>
    match h : col j.1 with
    | none => 0
    | some b => Pa b c ⟨j.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  let Q : Matrix ↥Rbar ↥R F := fun i r =>
    match h : row i.1 with
    | none => 0
    | some a => Qa a ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ r
  let L : Matrix ↥Rbar (Fin s) F := fun i k =>
    match h : row i.1 with
    | none => 0
    | some a => La a ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ k
  let RM : Matrix (Fin s) ↥Cbar F := fun k j =>
    match h : col j.1 with
    | none => 0
    | some b => RaM b k ⟨j.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  let M'blk : Matrix (↥R ⊕ ↥Rbar) (↥C ⊕ ↥Cbar) F :=
    Matrix.fromBlocks 0 Y X (X * P + Q * Y + L * RM)
  have hM'rk : M'blk.rank ≤ X.rank + Y.rank + s := by
    have hdecomp : M'blk =
        Matrix.fromBlocks (0 : Matrix ↥R ↥C F) 0 X (X * P) +
        Matrix.fromBlocks 0 Y 0 (Q * Y) +
        Matrix.fromBlocks 0 0 0 (L * RM) := by
      simp [M'blk, Matrix.fromBlocks_add]
    have hr1 : (Matrix.fromBlocks (0 : Matrix ↥R ↥C F) 0 X (X * P)).rank ≤ X.rank := by
      have hfac : Matrix.fromBlocks (0 : Matrix ↥R ↥C F) 0 X (X * P) =
          Matrix.fromBlocks (0 : Matrix ↥R ↥C F) 0 X 0 *
            Matrix.fromBlocks (1 : Matrix ↥C ↥C F) P (0 : Matrix ↥Cbar ↥C F) 0 := by
        simp [Matrix.fromBlocks_multiply]
      rw [hfac]
      exact (Matrix.rank_mul_le_left _ _).trans (le_of_eq (rank_fromBlocks_bl X))
    have hr2 : (Matrix.fromBlocks (0 : Matrix ↥R ↥C F) Y 0 (Q * Y)).rank ≤ Y.rank := by
      have hfac : Matrix.fromBlocks (0 : Matrix ↥R ↥C F) Y 0 (Q * Y) =
          Matrix.fromBlocks (1 : Matrix ↥R ↥R F) (0 : Matrix ↥R ↥Rbar F) Q 0 *
            Matrix.fromBlocks (0 : Matrix ↥R ↥C F) Y 0 0 := by
        simp [Matrix.fromBlocks_multiply]
      rw [hfac]
      exact (Matrix.rank_mul_le_right _ _).trans (le_of_eq (rank_fromBlocks_tr Y))
    have hr3 : (Matrix.fromBlocks (0 : Matrix ↥R ↥C F) 0 0 (L * RM)).rank ≤ s := by
      rw [rank_fromBlocks_br]
      exact (rank_mul_le_card L RM).trans (by simp)
    rw [hdecomp]
    exact (rank_add_le _ _).trans (Nat.add_le_add ((rank_add_le _ _).trans (Nat.add_le_add hr1 hr2)) hr3)
  let eRow : (↥R ⊕ ↥Rbar) ≃ Fin n :=
    { toFun := fun x => match x with | Sum.inl r => r.1 | Sum.inr i => i.1
      invFun := fun i =>
        if hi : row i = none then Sum.inl ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        else Sum.inr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      left_inv := fun x => by
        cases x with
        | inl r =>
          have hr : row r.1 = none := (Finset.mem_filter.mp r.2).2
          simp [hr]
        | inr i =>
          have hi : row i.1 ≠ none := (Finset.mem_filter.mp i.2).2
          simp [hi]
      right_inv := fun i => by by_cases hi : row i = none <;> simp [hi] }
  let eCol : (↥C ⊕ ↥Cbar) ≃ Fin m :=
    { toFun := fun x => match x with | Sum.inl c => c.1 | Sum.inr j => j.1
      invFun := fun j =>
        if hj : col j = none then Sum.inl ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
        else Sum.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      left_inv := fun x => by
        cases x with
        | inl c =>
          have hc : col c.1 = none := (Finset.mem_filter.mp c.2).2
          simp [hc]
        | inr j =>
          have hj : col j.1 ≠ none := (Finset.mem_filter.mp j.2).2
          simp [hj]
      right_inv := fun j => by by_cases hj : col j = none <;> simp [hj] }
  let M' : Matrix (Fin n) (Fin m) F := M'blk.submatrix eRow.symm eCol.symm
  let M : Matrix (Fin n) (Fin m) F := S0 + M'
  have hS0_rk : S0.rank ≤ r0 := by
    exact (rank_mul_le_card (A.submatrix id (fun j : C => j.val) * R0)
      (L0 * A.submatrix (fun i : R => i.val) id)).trans (by simp [r0, rk])
  have hM'_rk' : M'.rank = M'blk.rank := rank_submatrix_equiv M'blk eRow.symm eCol.symm
  have hS0_RC : ∀ (i : Fin n) (hi : row i = none) (j : Fin m) (hj : col j = none),
      S0 i j = A i j := by
    intro i hi j hj
    let r : ↥R := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let c : ↥C := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    let A00 : Matrix ↥R ↥C F := A.submatrix Subtype.val Subtype.val
    have hPQ0' : P0 * Q0 = A00 := hPQ0
    have h1 : S0 i j = ((A00 * R0) * (L0 * A00)) r c := by
      simp [S0, A00, r, c, Matrix.mul_apply]
    have h2 : (A00 * R0) * (L0 * A00) = A00 := by
      have hAR : A00 * R0 = P0 := by
        calc A00 * R0 = (P0 * Q0) * R0 := congrArg (· * R0) hPQ0'.symm
          _ = P0 * (Q0 * R0) := Matrix.mul_assoc _ _ _
          _ = P0 := by rw [hQR0, Matrix.mul_one]
      have hLA : L0 * A00 = Q0 := by
        calc L0 * A00 = L0 * (P0 * Q0) := congrArg (L0 * ·) hPQ0'.symm
          _ = (L0 * P0) * Q0 := (Matrix.mul_assoc _ _ _).symm
          _ = Q0 := by rw [hLP0, Matrix.one_mul]
      rw [hAR, hLA, hPQ0']
    rw [h1, h2]; rfl
  refine ⟨M, ?_, ?_, ?_⟩
  · calc M.rank ≤ S0.rank + M'.rank := rank_add_le S0 M'
      _ ≤ r0 + (X.rank + Y.rank + s) := by rw [hM'_rk']; exact Nat.add_le_add hS0_rk hM'rk
      _ = k := by omega
  · intro i j hij
    by_cases hi : row i = none
    · by_cases hj : col j = none
      · have hM'0 : M' i j = 0 := by simp [M', M'blk, eRow, eCol, hi, hj]
        simp [M, hM'0, hS0_RC i hi j hj]
      · have hM'Y : M' i j = A i j - S0 i j := by
          simp [M', M'blk, eRow, eCol, hi, hj, Y, A']
        simp [M, hM'Y]
    · have hj : col j = none := hij.resolve_left hi
      have hM'X : M' i j = A i j - S0 i j := by
        simp [M', M'blk, eRow, eCol, hi, hj, X, A']
      simp [M, hM'X]
  · intro a i j hi hj
    have hi' : row i ≠ none := by rw [hi]; simp
    have hj' : col j ≠ none := by rw [hj]; simp
    let ib : ↥Rbar := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩⟩
    let jb : ↥Cbar := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩⟩
    let ia : ↥(Ra a) := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let ja : ↥(Ca a) := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    have hM'ij : M' i j = (X * P + Q * Y + L * RM) ib jb := by
      simp [M', M'blk, eRow, eCol, hi', hj', ib, jb]
    have hP_at : ∀ c : ↥C, P c jb = Pa a c ja := by
      intro c
      dsimp only [P, jb, ja]
      split
      · rename_i h; rw [hj] at h; simp at h
      · rename_i b h
        have hba : b = a := Option.some.inj (h.symm.trans hj)
        subst hba; rfl
    have hQ_at : ∀ r : ↥R, Q ib r = Qa a ia r := by
      intro r
      dsimp only [Q, ib, ia]
      split
      · rename_i h; rw [hi] at h; simp at h
      · rename_i b h
        have hba : b = a := Option.some.inj (h.symm.trans hi)
        subst hba; rfl
    have hL_at : ∀ k : Fin s, L ib k = La a ia k := by
      intro k
      dsimp only [L, ib, ia]
      split
      · rename_i h; rw [hi] at h; simp at h
      · rename_i b h
        have hba : b = a := Option.some.inj (h.symm.trans hi)
        subst hba; rfl
    have hRM_at : ∀ k : Fin s, RM k jb = RaM a k ja := by
      intro k
      dsimp only [RM, jb, ja]
      split
      · rename_i h; rw [hj] at h; simp at h
      · rename_i b h
        have hba : b = a := Option.some.inj (h.symm.trans hj)
        subst hba; rfl
    have hXP : (X * P) ib jb =
        ((A'.submatrix (fun i : Ra a => i.val) (fun c : C => c.val)) * Pa a) ia ja := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hP_at c]; rfl
    have hQY : (Q * Y) ib jb =
        (Qa a * (A'.submatrix (fun r : R => r.val) (fun j : Ca a => j.val))) ia ja := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [hQ_at r]; rfl
    have hLR : (L * RM) ib jb = (La a * RaM a) ia ja := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hL_at k, hRM_at k]
    have hval := congrFun (congrFun (hpiece_eq a) ia) ja
    have hM'eq : M' i j = B a i j - S0 i j := by
      rw [hM'ij]
      change (X * P) ib jb + (Q * Y) ib jb + (L * RM) ib jb = B a i j - S0 i j
      rw [hXP, hQY, hLR]
      exact hval.symm
    change S0 i j + M' i j = B a i j
    rw [hM'eq]
    abel



private lemma bool_toNat_zmod2 (b : Bool) : ((b.toNat : ℕ) : ZMod 2) = b2z b := by
  cases b <;> rfl

private lemma b2z_decide_eq_one (x : ZMod 2) : b2z (decide (x = 1)) = x := by
  fin_cases x <;> rfl

private lemma b2z_diff_ite (a b : Bool) :
    b2z a = b2z b + (if a ≠ b then (1 : ZMod 2) else 0) := by
  cases a <;> cases b <;> decide

private lemma b2z_add_one_ne (b : Bool) : b2z b + (1 : ZMod 2) ≠ b2z b := by
  cases b <;> decide

private lemma rk_congr {n m : ℕ} {M₁ M₂ : Matrix (Fin n) (Fin m) F}
    {I : Finset (Fin n)} {J : Finset (Fin m)}
    (h : ∀ i ∈ I, ∀ j ∈ J, M₁ i j = M₂ i j) :
    rk M₁ I J = rk M₂ I J := by
  unfold rk
  congr 1
  ext i j
  exact h i.1 i.2 j.1 j.2

private theorem main_bridge
    (n m d t : ℕ) (T : Fin n → Fin m → Bool)
    (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d))
    (u : Fin n) (v : Fin m) (hu : row u = none) (hv : col v = none)
    (w : Fin n × Fin m → ℕ) (e : Fin d → ℕ) :
    let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
    let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
    let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
    let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
    let cells := fun a : Fin d => (Finset.univ : Finset (Fin n × Fin m)).filter
      (fun z => row z.1 = some a ∧ col z.2 = some a)
    let entry := fun i j => ((T i j).toNat : ZMod 2)
    let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => entry i j + entry i v + entry u j + entry u v
    let strips := rk A Finset.univ C + rk A R Finset.univ
    (∃ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q ∧
      PEqualNP.Represents.Represents P Q ∧ (depthsOf (n+m) Q.gates).getD Q.output 0 ≤ 1 ∧
      Q.gates.countP nlGate ≤ t ∧
      (∀ i j, (row i = none ∨ col j = none) → P i j = T i j) ∧
      ∀ a, (((cells a).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w) ≤ e a) ↔
    strips ≤ 2*t + rk A R C ∧ ∀ a : Fin d, ∃ F0 : Finset (Fin n × Fin m),
      F0 ⊆ cells a ∧ F0.sum w ≤ e a ∧
      let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => A i j + (if (i,j) ∈ F0 then 1 else 0)
      strips + rk B (rows a) (cols a) ≤ 2*t + rk A (rows a) C + rk A R (cols a) := by
  intro R C rows cols cells entry A strips
  have hA_eq : ∀ i j, A i j = b2z (T i j) + b2z (T i v) + b2z (T u j) + b2z (T u v) := by
    intro i j
    simp only [A, entry, bool_toNat_zmod2]
  constructor
  · rintro ⟨P, Q, hlen, hrb, hrep, hdep, hcnt, hstrip_eq, herr⟩
    let M : Matrix (Fin n) (Fin m) F := anchor u v (fun i j => b2z (P i j))
    have hMrk : M.rank ≤ 2 * t := (main n m P u v t).mpr ⟨Q, ⟨hlen, hrb, hrep⟩, hdep, hcnt⟩
    have hM_diff : ∀ i j, M i j = A i j + (if P i j ≠ T i j then 1 else 0) := by
      intro i j
      have hiv : P i v = T i v := hstrip_eq i v (Or.inr hv)
      have huj : P u j = T u j := hstrip_eq u j (Or.inl hu)
      have huv : P u v = T u v := hstrip_eq u v (Or.inl hu)
      simp only [M, anchor, hiv, huj, huv, hA_eq]
      rw [b2z_diff_ite (P i j) (T i j)]
      abel
    have hM_strip : ∀ i j, (row i = none ∨ col j = none) → M i j = A i j := by
      intro i j hij
      rw [hM_diff i j, ite_eq_right_iff.mpr (fun h => absurd (hstrip_eq i j hij) h), add_zero]
    have hUC : rk M Finset.univ C = rk A Finset.univ C :=
      rk_congr (fun i _ j hj => hM_strip i j (Or.inr (Finset.mem_filter.mp hj).2))
    have hRU : rk M R Finset.univ = rk A R Finset.univ :=
      rk_congr (fun i hi j _ => hM_strip i j (Or.inl (Finset.mem_filter.mp hi).2))
    have hRC : rk M R C = rk A R C :=
      rk_congr (fun i hi j _ => hM_strip i j (Or.inl (Finset.mem_filter.mp hi).2))
    refine ⟨?_, ?_⟩
    · have h1 := rk_strip_le M R C
      rw [hUC, hRU, hRC] at h1
      change rk A Finset.univ C + rk A R Finset.univ ≤ 2 * t + rk A R C
      omega
    · intro a
      let F0 : Finset (Fin n × Fin m) := (cells a).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)
      refine ⟨F0, Finset.filter_subset _ _, herr a, ?_⟩
      intro B
      have hMB : rk M (rows a) (cols a) = rk B (rows a) (cols a) := by
        refine rk_congr (fun i hi j hj => ?_)
        by_cases hrc : row i = none ∨ col j = none
        · have hnot : (i, j) ∉ F0 := by
            intro hm
            have hc := (Finset.mem_filter.mp (Finset.filter_subset _ _ hm)).2
            rcases hrc with hr | hc'
            · rw [hr] at hc; exact absurd hc.1 (by simp)
            · rw [hc'] at hc; exact absurd hc.2 (by simp)
          simp only [B, hM_strip i j hrc, ite_eq_right_iff.mpr (fun hm => absurd hm hnot), add_zero]
        · push Not at hrc
          have hi' : row i = some a := by
            rcases Finset.mem_union.mp hi with h1 | h2
            · exact absurd (Finset.mem_filter.mp h1).2 hrc.1
            · exact (Finset.mem_filter.mp h2).2
          have hj' : col j = some a := by
            rcases Finset.mem_union.mp hj with h1 | h2
            · exact absurd (Finset.mem_filter.mp h1).2 hrc.2
            · exact (Finset.mem_filter.mp h2).2
          have hmem : (i, j) ∈ F0 ↔ P i j ≠ T i j := by
            simp [F0, cells, hi', hj']
          simp only [B, hM_diff i j, hmem]
      have hRaC : rk M (rows a) C = rk A (rows a) C :=
        rk_congr (fun i _ j hj => hM_strip i j (Or.inr (Finset.mem_filter.mp hj).2))
      have hRCa : rk M R (cols a) = rk A R (cols a) :=
        rk_congr (fun i hi j _ => hM_strip i j (Or.inl (Finset.mem_filter.mp hi).2))
      have h2 := rk_panel_le M R (rows a) C (cols a) Finset.subset_union_left Finset.subset_union_left
      rw [hUC, hRU, hMB, hRaC, hRCa] at h2
      change rk A Finset.univ C + rk A R Finset.univ + rk B (rows a) (cols a) ≤
        2 * t + rk A (rows a) C + rk A R (cols a)
      omega
  · rintro ⟨hstrip, hpanels⟩
    choose Fa hFa_sub hFa_w hFa_rk using hpanels
    let Ba : Fin d → Matrix (Fin n) (Fin m) F := fun a i j =>
      A i j + (if (i, j) ∈ Fa a then 1 else 0)
    have hB_out : ∀ a i j, (row i ≠ some a ∨ col j ≠ some a) → Ba a i j = A i j := by
      intro a i j hne
      have hnot : (i, j) ∉ Fa a := by
        intro hm
        have hc := (Finset.mem_filter.mp (hFa_sub a hm)).2
        rcases hne with h1 | h2
        · exact h1 hc.1
        · exact h2 hc.2
      simp [Ba, hnot]
    obtain ⟨M, hMrk, hM_strip, hM_diag⟩ :=
      block_completion A row col Ba hB_out hstrip hFa_rk
    let P : Fin n → Fin m → Bool := fun i j =>
      decide (M i j + entry i v + entry u j + entry u v = 1)
    have hP_b2z : ∀ i j, b2z (P i j) = M i j + entry i v + entry u j + entry u v := by
      intro i j
      exact b2z_decide_eq_one _
    have hA_u : ∀ j, A u j = 0 := by
      intro j
      have h1 : entry u j + entry u j = 0 := zmod2_add_self _
      have h2 : entry u v + entry u v = 0 := zmod2_add_self _
      calc A u j = (entry u j + entry u j) + (entry u v + entry u v) := by simp only [A]; abel
        _ = 0 := by rw [h1, h2, add_zero]
    have hA_v : ∀ i, A i v = 0 := by
      intro i
      have h1 : entry i v + entry i v = 0 := zmod2_add_self _
      have h2 : entry u v + entry u v = 0 := zmod2_add_self _
      calc A i v = (entry i v + entry i v) + (entry u v + entry u v) := by simp only [A]; abel
        _ = 0 := by rw [h1, h2, add_zero]
    have hM_u : ∀ j, M u j = 0 := fun j => (hM_strip u j (Or.inl hu)).trans (hA_u j)
    have hM_v : ∀ i, M i v = 0 := fun i => (hM_strip i v (Or.inr hv)).trans (hA_v i)
    have hP_u : ∀ j, b2z (P u j) = entry u j := by
      intro j
      rw [hP_b2z u j, hM_u j]
      have h2 : entry u v + entry u v = 0 := zmod2_add_self _
      calc 0 + entry u v + entry u j + entry u v = entry u j + (entry u v + entry u v) := by abel
        _ = entry u j := by rw [h2, add_zero]
    have hP_v : ∀ i, b2z (P i v) = entry i v := by
      intro i
      rw [hP_b2z i v, hM_v i]
      have h2 : entry u v + entry u v = 0 := zmod2_add_self _
      calc 0 + entry i v + entry u v + entry u v = entry i v + (entry u v + entry u v) := by abel
        _ = entry i v := by rw [h2, add_zero]
    have hanch : anchor u v (fun i j => b2z (P i j)) = M := by
      ext i j
      simp only [anchor]
      rw [hP_b2z i j, hP_v i, hP_u j, hP_u v]
      have h1 : entry i v + entry i v = 0 := zmod2_add_self _
      have h2 : entry u j + entry u j = 0 := zmod2_add_self _
      have h3 : entry u v + entry u v = 0 := zmod2_add_self _
      calc M i j + entry i v + entry u j + entry u v + entry i v + entry u j + entry u v
          = M i j + (entry i v + entry i v) + (entry u j + entry u j) + (entry u v + entry u v) := by abel
        _ = M i j := by rw [h1, h2, h3, add_zero, add_zero, add_zero]
    have hanch_rk : (anchor u v (fun i j => b2z (P i j))).rank ≤ 2 * t := by
      rw [hanch]; exact hMrk
    obtain ⟨Q, ⟨hlen, hrb, hrep⟩, hdep, hcnt⟩ := (main n m P u v t).mp hanch_rk
    refine ⟨P, Q, hlen, hrb, hrep, hdep, hcnt, ?_, ?_⟩
    · intro i j hij
      apply b2z_inj
      rw [hP_b2z i j, hM_strip i j hij, ← bool_toNat_zmod2]
      have h1 : entry i v + entry i v = 0 := zmod2_add_self _
      have h2 : entry u j + entry u j = 0 := zmod2_add_self _
      have h3 : entry u v + entry u v = 0 := zmod2_add_self _
      calc A i j + entry i v + entry u j + entry u v
          = entry i j + (entry i v + entry i v) + (entry u j + entry u j) + (entry u v + entry u v) := by
            simp only [A]; abel
        _ = entry i j := by rw [h1, h2, h3, add_zero, add_zero, add_zero]
    · intro a
      have hfilt : (cells a).filter (fun z => P z.1 z.2 ≠ T z.1 z.2) = Fa a := by
        ext ⟨i, j⟩
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hc, hne⟩
          have hrc := (Finset.mem_filter.mp hc).2
          by_contra hnot
          apply hne
          apply b2z_inj
          rw [hP_b2z i j, hM_diag a i j hrc.1 hrc.2]
          have hBa : Ba a i j = A i j := by simp [Ba, hnot]
          rw [hBa, ← bool_toNat_zmod2]
          have h1 : entry i v + entry i v = 0 := zmod2_add_self _
          have h2 : entry u j + entry u j = 0 := zmod2_add_self _
          have h3 : entry u v + entry u v = 0 := zmod2_add_self _
          calc A i j + entry i v + entry u j + entry u v
              = entry i j + (entry i v + entry i v) + (entry u j + entry u j) + (entry u v + entry u v) := by
                simp only [A]; abel
            _ = entry i j := by rw [h1, h2, h3, add_zero, add_zero, add_zero]
        · intro hm
          have hc : (i, j) ∈ cells a := hFa_sub a hm
          refine ⟨hc, ?_⟩
          have hrc := (Finset.mem_filter.mp hc).2
          intro heq
          have hb : b2z (P i j) = b2z (T i j) := congrArg b2z heq
          rw [hP_b2z i j, hM_diag a i j hrc.1 hrc.2] at hb
          have hBa : Ba a i j = A i j + 1 := by simp [Ba, hm]
          rw [hBa] at hb
          have h1 : entry i v + entry i v = 0 := zmod2_add_self _
          have h2 : entry u j + entry u j = 0 := zmod2_add_self _
          have h3 : entry u v + entry u v = 0 := zmod2_add_self _
          have hsimp : A i j + 1 + entry i v + entry u j + entry u v = b2z (T i j) + 1 := by
            calc A i j + 1 + entry i v + entry u j + entry u v
                = entry i j + 1 + (entry i v + entry i v) + (entry u j + entry u j) + (entry u v + entry u v) := by
                  simp only [A]; abel
              _ = entry i j + 1 := by rw [h1, h2, h3, add_zero, add_zero, add_zero]
              _ = b2z (T i j) + 1 := by simp [entry, bool_toNat_zmod2]
          rw [hsimp] at hb
          exact b2z_add_one_ne (T i j) hb
      rw [hfilt]
      exact hFa_w a


end PEqualNP.Outside.L_meta_33615

theorem PEqualNP.Outside.L_meta_33615 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (Q : PEqualNP.CircuitLowerBounds.Circuit) =>
  (Q.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD Q.output 0
∀ (n m d t : ℕ) (T : Fin n → Fin m → Bool)
  (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d))
  (u : Fin n) (v : Fin m) (_ : row u = none) (_ : col v = none)
  (w : Fin n × Fin m → ℕ) (e : Fin d → ℕ),
  let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
  let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
  let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
  let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
  let cells := fun a : Fin d => (Finset.univ : Finset (Fin n × Fin m)).filter
    (fun z => row z.1 = some a ∧ col z.2 = some a)
  let entry := fun i j => ((T i j).toNat : ZMod 2)
  let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => entry i j + entry i v + entry u j + entry u v
  let rk := fun (B : Matrix (Fin n) (Fin m) (ZMod 2)) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun i : I => i.val) (fun j : J => j.val))
  let strips := rk A Finset.univ C + rk A R Finset.univ
  (∃ (P : Fin n → Fin m → Bool) (Q : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ Q.gates, g.inputs.length ≤ 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) Q ∧
    PEqualNP.Represents.Represents P Q ∧ depth (n+m) Q ≤ 1 ∧ Q.gates.countP nonlinear ≤ t ∧
    (∀ i j, (row i = none ∨ col j = none) → P i j = T i j) ∧
    ∀ a, (((cells a).filter (fun z => P z.1 z.2 ≠ T z.1 z.2)).sum w) ≤ e a) ↔
  strips ≤ 2*t + rk A R C ∧ ∀ a : Fin d, ∃ F : Finset (Fin n × Fin m),
    F ⊆ cells a ∧ F.sum w ≤ e a ∧
    let B : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => A i j + (if (i,j) ∈ F then 1 else 0)
    strips + rk B (rows a) (cols a) ≤ 2*t + rk A (rows a) C + rk A R (cols a)
) := by
  intro nonlinear depth n m d t T row col u v hu hv w e
  exact PEqualNP.Outside.L_meta_33615.main_bridge n m d t T row col u v hu hv w e
