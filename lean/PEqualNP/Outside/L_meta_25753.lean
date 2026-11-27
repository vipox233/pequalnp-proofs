import PEqualNP.Defs
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace PEqualNP.Outside.L_meta_25753_aux

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

theorem rank_two_vv {n m : ℕ} (x z : Fin n → ZMod 2) (y w : Fin m → ZMod 2) :
    (Matrix.vecMulVec x y + Matrix.vecMulVec z w).rank ≤ 2 := by
  have h : Matrix.vecMulVec x y + Matrix.vecMulVec z w =
      (Matrix.of fun i (k : Fin 2) => ![x i, z i] k) *
      (Matrix.of fun (k : Fin 2) j => ![y j, w j] k) := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply]
  rw [h]
  exact rank_of_factor _ _

theorem decomp {n m : ℕ} (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hcnt : C.gates.countP nlGate ≤ t) :
    ∃ (K : ℕ) (N : Fin K → Matrix (Fin n) (Fin m) (ZMod 2)), K ≤ t ∧ (∀ g, (N g).rank ≤ 2) ∧
      ∀ w : ℕ, (depthsOf (n + m) C.gates).getD w 0 ≤ 1 →
        anchor u v (fun i j => b2z ((wiresOf (oneEach i j) C.gates).getD w false)) ∈
          Submodule.span (ZMod 2) (Set.range N) := by
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
  refine ⟨NL.card, fun g => anchor u v (val (n + m + (NL.equivFin.symm g).val.val)), hNL_card,
    fun g => ?_, fun w hw => ?_⟩
  · obtain ⟨r1, r2, s1, s2, h⟩ := hNL_outer _ (NL.equivFin.symm g).property
    simp only [h]
    exact rank_two_vv _ _ _ _
  · obtain ⟨coeff, hcoeff⟩ := hspan w hw
    change anchor u v (val w) ∈ _
    rw [hcoeff]
    refine Submodule.sum_mem _ fun idx hidx => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨NL.equivFin ⟨idx, hidx⟩, ?_⟩
    simp


theorem finrank_sup_le {ι E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (T : Finset ι) (U : ι → Submodule (ZMod 2) E) :
    Module.finrank (ZMod 2) (T.sup U : Submodule (ZMod 2) E) ≤
      ∑ g ∈ T, Module.finrank (ZMod 2) (U g) := by
  classical
  induction T using Finset.induction with
  | empty => rw [Finset.sup_empty, finrank_bot]; exact Nat.zero_le _
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    exact le_trans (Submodule.finrank_add_le_finrank_add_finrank _ _) (Nat.add_le_add_left ih _)

theorem lower {n m q K : ℕ} (A : Fin q → Matrix (Fin n) (Fin m) (ZMod 2))
    (N : Fin K → Matrix (Fin n) (Fin m) (ZMod 2))
    (hN : ∀ g, (N g).rank ≤ 2) (hA : ∀ j, A j ∈ Submodule.span (ZMod 2) (Set.range N))
    (hind : Matrix.rank (Matrix.of fun x (z : Fin q × Fin m) => A z.1 x z.2) = ∑ i, (A i).rank) :
    (Finset.univ.filter (fun j => (A j).rank = 1)).card +
      ((∑ i, (A i).rank) - (Finset.univ.filter (fun j => (A j).rank = 1)).card + 1) / 2 ≤ K := by
  classical
  set S := Finset.univ.filter (fun j => (A j).rank = 1) with hS
  set D := ∑ i, (A i).rank with hD
  let V : Fin q → Submodule (ZMod 2) (Fin n → ZMod 2) :=
    fun j => Submodule.span (ZMod 2) (Set.range (A j).col)
  have hV : ∀ j, Module.finrank (ZMod 2) (V j) = (A j).rank :=
    fun j => (Matrix.rank_eq_finrank_span_cols _).symm
  have hS1 : ∀ j ∈ S, (A j).rank = 1 := fun j hj => (Finset.mem_filter.mp hj).2
  let W1 : Submodule (ZMod 2) (Fin n → ZMod 2) := S.sup V
  let W2 : Submodule (ZMod 2) (Fin n → ZMod 2) := Sᶜ.sup V
  have h1 : Module.finrank (ZMod 2) W1 ≤ S.card := by
    refine le_trans (finrank_sup_le _ _) ?_
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [hV, hS1 j hj]
  have hsum : S.card + ∑ j ∈ Sᶜ, (A j).rank = D := by
    rw [hD, ← Finset.sum_add_sum_compl S]
    congr 1
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun j hj => (hS1 j hj).symm
  have h2 : Module.finrank (ZMod 2) W2 ≤ ∑ j ∈ Sᶜ, (A j).rank := by
    refine le_trans (finrank_sup_le _ _) ?_
    exact Finset.sum_le_sum fun j _ => (hV j).le
  have hsup : Module.finrank (ZMod 2) (W1 ⊔ W2 : Submodule (ZMod 2) (Fin n → ZMod 2)) = D := by
    have e : Submodule.span (ZMod 2)
        (Set.range (Matrix.of fun x (z : Fin q × Fin m) => A z.1 x z.2).col) = W1 ⊔ W2 := by
      change _ = S.sup V ⊔ Sᶜ.sup V
      rw [← Finset.sup_union, Finset.union_compl]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨z, rfl⟩
        exact (Finset.le_sup (f := V) (Finset.mem_univ z.1)) (Submodule.subset_span ⟨z.2, rfl⟩)
      · refine Finset.sup_le fun j _ => Submodule.span_mono ?_
        rintro _ ⟨y, rfl⟩
        exact ⟨(j, y), rfl⟩
    rw [← e, ← Matrix.rank_eq_finrank_span_cols]
    exact hind
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq W1 W2
  have hinf : W1 ⊓ W2 = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  have hW1 : Module.finrank (ZMod 2) W1 = S.card := by omega
  have hW2 : Module.finrank (ZMod 2) W2 = D - S.card := by omega
  let φ : Matrix (Fin n) (Fin m) (ZMod 2) →ₗ[ZMod 2] (Fin m → (Fin n → ZMod 2) ⧸ W1) :=
    { toFun := fun M y => W1.mkQ (fun x => M x y)
      map_add' := fun a b => by
        funext y
        exact map_add W1.mkQ (fun x => a x y) (fun x => b x y)
      map_smul' := fun c a => by
        funext y
        exact map_smul W1.mkQ c (fun x => a x y) }
  have hzero : ∀ j ∈ S, φ (A j) = 0 := by
    intro j hj
    funext y
    refine (Submodule.Quotient.mk_eq_zero W1).mpr ?_
    exact (Finset.le_sup (f := V) hj) (Submodule.subset_span ⟨y, rfl⟩)
  have hone : ∀ j : S, ∃ v : V j.1, v ≠ 0 ∧ ∀ w : V j.1, ∃ c : ZMod 2, c • v = w := by
    intro j
    exact finrank_eq_one_iff'.mp (by rw [hV]; exact hS1 j.1 j.2)
  choose v hv0 hv using hone
  have hli : LinearIndependent (ZMod 2) (fun j : S => (v j : Fin n → ZMod 2)) := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have e : Submodule.span (ZMod 2) (Set.range fun j : S => (v j : Fin n → ZMod 2)) = W1 := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact (Finset.le_sup (f := V) j.2) (v j).2
      · refine Finset.sup_le fun j hj x hx => ?_
        obtain ⟨c, hc⟩ := hv ⟨j, hj⟩ ⟨x, hx⟩
        have : c • (v ⟨j, hj⟩ : Fin n → ZMod 2) = x := congrArg Subtype.val hc
        rw [← this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    unfold Set.finrank
    rw [e, hW1, Fintype.card_coe]
  have hliA : LinearIndependent (ZMod 2) (fun j : S => A j.1) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j0
    have hne : A j0.1 ≠ 0 := by
      intro h
      have := hS1 j0.1 j0.2
      rw [h, Matrix.rank_zero] at this
      exact absurd this (by omega)
    obtain ⟨x0, y0, hxy⟩ : ∃ x y, A j0.1 x y ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (by ext x y; exact h x y)
    have hcol : ∀ j : S, ∃ l : ZMod 2, l • (v j : Fin n → ZMod 2) = fun x => A j.1 x y0 := by
      intro j
      obtain ⟨l, hl⟩ := hv j ⟨fun x => A j.1 x y0, Submodule.subset_span ⟨y0, rfl⟩⟩
      exact ⟨l, congrArg Subtype.val hl⟩
    choose l hl using hcol
    have hz : ∑ j : S, (c j * l j) • (v j : Fin n → ZMod 2) = 0 := by
      funext x
      have h := congrFun (congrFun hc x) y0
      rw [Matrix.sum_apply] at h
      rw [Finset.sum_apply, Pi.zero_apply]
      rw [Matrix.zero_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul, hl j]
      rfl
    have h0 := Fintype.linearIndependent_iff.mp hli (fun j => c j * l j) hz j0
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exfalso
      have := congrFun (hl j0) x0
      rw [h, zero_smul] at this
      exact hxy this.symm
  set VN := Submodule.span (ZMod 2) (Set.range N) with hVN
  have hVNK : Module.finrank (ZMod 2) VN ≤ K := by
    have := finrank_range_le_card (R := ZMod 2) N
    rwa [Fintype.card_fin] at this
  let Z := Submodule.span (ZMod 2) (Set.range fun j : S => A j.1)
  have hZ : Module.finrank (ZMod 2) Z = S.card := by
    rw [finrank_span_eq_card hliA, Fintype.card_coe]
  have hZle : Z ≤ VN := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hA j.1
  have hker : Z.comap VN.subtype ≤ LinearMap.ker (φ.domRestrict VN) := by
    intro a ha
    have : Z ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hzero j.1 j.2
    exact this ha
  have hker' := Submodule.finrank_mono hker
  rw [(Submodule.comapSubtypeEquivOfLe hZle).finrank_eq, hZ] at hker'
  have hrn := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict VN)
  rw [LinearMap.range_domRestrict] at hrn
  have hmap : VN.map φ = Submodule.span (ZMod 2) (Set.range (φ ∘ N)) := by
    rw [hVN, Submodule.map_span, Set.range_comp]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent (ZMod 2) (Set.range (φ ∘ N))
  have hbfin : b.Finite := (Set.finite_range (φ ∘ N)).subset hbsub
  have : Fintype b := hbfin.fintype
  have hbcard : Fintype.card b = Module.finrank (ZMod 2) (VN.map φ) := by
    rw [hmap, ← hbspan, finrank_span_set_eq_card hbli, Set.toFinset_card]
  have hpre : ∀ e : b, ∃ g, φ (N g) = e.1 := fun e => hbsub e.2
  choose f hf using hpre
  let T : Finset (Fin K) := Finset.univ.image f
  have hT : T.card ≤ Fintype.card b := le_trans Finset.card_image_le (by simp)
  let U : Fin K → Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ W1) :=
    fun g => (Submodule.span (ZMod 2) (Set.range (N g).col)).map W1.mkQ
  have hkey : W2.map W1.mkQ ≤ T.sup U := by
    rw [Submodule.map_le_iff_le_comap]
    refine Finset.sup_le fun j _ => ?_
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hmem : φ (A j) ∈ Submodule.span (ZMod 2) b := by
      rw [hbspan, ← hmap]
      exact Submodule.mem_map_of_mem (hA j)
    have hle : Submodule.span (ZMod 2) b ≤ (T.sup U).comap (LinearMap.proj y) := by
      rw [Submodule.span_le]
      intro e he
      have h := congrFun (hf ⟨e, he⟩) y
      change φ (N (f ⟨e, he⟩)) y = e y at h
      change e y ∈ T.sup U
      rw [← h]
      refine (Finset.le_sup (f := U) (Finset.mem_image_of_mem f (Finset.mem_univ (⟨e, he⟩ : b)))) ?_
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, rfl⟩)
    exact hle hmem
  have hinj : Function.Injective (W1.mkQ.domRestrict W2) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ h
    have : x ∈ W1 ⊓ W2 := ⟨(Submodule.Quotient.mk_eq_zero W1).mp h, hx⟩
    rw [hinf] at this
    exact Subtype.ext ((Submodule.mem_bot _).mp this)
  have hdim : Module.finrank (ZMod 2) (W2.map W1.mkQ) = D - S.card := by
    rw [← hW2, ← LinearMap.finrank_range_of_inj hinj, LinearMap.range_domRestrict]
  have hfin : D - S.card ≤ T.card * 2 := by
    rw [← hdim]
    refine le_trans (Submodule.finrank_mono hkey) (le_trans (finrank_sup_le _ _) ?_)
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun g _ => le_trans (Submodule.finrank_map_le _ _) ?_
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact hN g
  omega

theorem red {n m : ℕ} (C M : Matrix (Fin n) (Fin m) (ZMod 2)) (β : Fin m → ZMod 2)
    (hM : ∀ v, C.mulVec v = 0 → M.mulVec v = 0) (h0 : (C - M).mulVec β = 0)
    (h1 : C.mulVec β ≠ 0) : (C - M).rank < C.rank := by
  have hlt : LinearMap.ker C.mulVecLin < LinearMap.ker (C - M).mulVecLin := by
    refine lt_of_le_of_ne (fun v hv => ?_) (fun he => h1 ?_)
    · have hv' : C.mulVec v = 0 := hv
      change (C - M).mulVec v = 0
      rw [Matrix.sub_mulVec, hv', hM v hv', sub_zero]
    · have : β ∈ LinearMap.ker (C - M).mulVecLin := h0
      rw [← he] at this
      exact this
  have h := Submodule.finrank_lt_finrank_of_lt hlt
  have a := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  have b := LinearMap.finrank_range_add_finrank_ker (C - M).mulVecLin
  unfold Matrix.rank
  omega

theorem plane {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2))
    (h : (Matrix.fromRows A B).rank + 2 ≤ A.rank + B.rank) :
    ∃ (x : Fin n → ZMod 2) (y : Fin m → ZMod 2) (z : Fin n → ZMod 2) (w : Fin m → ZMod 2),
      (A - (Matrix.vecMulVec x y + Matrix.vecMulVec z w)).rank < A.rank ∧
      (B - (Matrix.vecMulVec x y + Matrix.vecMulVec z w)).rank < B.rank := by
  let RA := Submodule.span (ZMod 2) (Set.range A.row)
  let RB := Submodule.span (ZMod 2) (Set.range B.row)
  have hsup : (Matrix.fromRows A B).rank =
      Module.finrank (ZMod 2) (RA ⊔ RB : Submodule (ZMod 2) (Fin m → ZMod 2)) := by
    rw [Matrix.rank_eq_finrank_span_row,
      show (Matrix.fromRows A B).row = Sum.elim A.row B.row by funext i; cases i <;> rfl,
      Set.Sum.elim_range, Submodule.span_union]
  have hA : A.rank = Module.finrank (ZMod 2) RA := Matrix.rank_eq_finrank_span_row _
  have hB : B.rank = Module.finrank (ZMod 2) RB := Matrix.rank_eq_finrank_span_row _
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq RA RB
  have h2 : 2 ≤ Module.finrank (ZMod 2) (RA ⊓ RB : Submodule (ZMod 2) (Fin m → ZMod 2)) := by omega
  let b := Module.finBasis (ZMod 2) (RA ⊓ RB : Submodule (ZMod 2) (Fin m → ZMod 2))
  let Y : Matrix (Fin 2) (Fin m) (ZMod 2) :=
    Matrix.of fun k => ((b (Fin.castLE h2 k)) : Fin m → ZMod 2)
  have hli : LinearIndependent (ZMod 2) Y.row :=
    (b.linearIndependent.comp _ (Fin.castLE_injective h2)).map'
      (RA ⊓ RB : Submodule (ZMod 2) (Fin m → ZMod 2)).subtype (Submodule.ker_subtype _)
  have htop : LinearMap.range Y.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Y.rank = _
    rw [LinearIndependent.rank_matrix hli, Module.finrank_pi]
  have hsurj : ∀ t : Fin 2 → ZMod 2, ∃ β, Y.mulVec β = t := by
    intro t
    have : t ∈ LinearMap.range Y.mulVecLin := by rw [htop]; trivial
    exact this
  obtain ⟨βA, hβA⟩ := hsurj ![1, 0]
  obtain ⟨βB, hβB⟩ := hsurj ![0, 1]
  have a0 : dotProduct (Y 0) βA = 1 := congrFun hβA 0
  have a1 : dotProduct (Y 1) βA = 0 := congrFun hβA 1
  have b0 : dotProduct (Y 0) βB = 0 := congrFun hβB 0
  have b1 : dotProduct (Y 1) βB = 1 := congrFun hβB 1
  have hrow : ∀ (C : Matrix (Fin n) (Fin m) (ZMod 2)) (r : Fin m → ZMod 2),
      r ∈ Submodule.span (ZMod 2) (Set.range C.row) →
      ∀ v, C.mulVec v = 0 → dotProduct r v = 0 := by
    intro C r hr v hv
    rw [← range_vecMulLinear] at hr
    obtain ⟨α, rfl⟩ := hr
    change dotProduct (Matrix.vecMul α C) v = 0
    rw [← Matrix.dotProduct_mulVec, hv, dotProduct_zero]
  have hY : ∀ k, Y k ∈ RA ∧ Y k ∈ RB := fun k => (b (Fin.castLE h2 k)).2
  refine ⟨A.mulVec βA, Y 0, B.mulVec βB, Y 1, ?_⟩
  set M := Matrix.vecMulVec (A.mulVec βA) (Y 0) + Matrix.vecMulVec (B.mulVec βB) (Y 1) with hM
  have hMv : ∀ v, M.mulVec v = fun i =>
      A.mulVec βA i * dotProduct (Y 0) v + B.mulVec βB i * dotProduct (Y 1) v := by
    intro v
    funext i
    change dotProduct (fun j => M i j) v = _
    simp only [dotProduct, hM, Matrix.add_apply, Matrix.vecMulVec_apply, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  constructor
  · refine red A M βA (fun v hv => ?_) ?_ (fun h0 => ?_)
    · rw [hMv, hrow A _ (hY 0).1 v hv, hrow A _ (hY 1).1 v hv]
      funext i; simp
    · rw [Matrix.sub_mulVec, hMv, a0, a1]
      funext i; simp
    · have := hrow A _ (hY 0).1 βA h0
      rw [a0] at this
      exact one_ne_zero this
  · refine red B M βB (fun v hv => ?_) ?_ (fun h0 => ?_)
    · rw [hMv, hrow B _ (hY 0).2 v hv, hrow B _ (hY 1).2 v hv]
      funext i; simp
    · rw [Matrix.sub_mulVec, hMv, b0, b1]
      funext i; simp
    · have := hrow B _ (hY 1).2 βB h0
      rw [b1] at this
      exact one_ne_zero this

theorem realize {n m q : ℕ} (u : Fin n) (v : Fin m) (G : Fin q → Fin n → Fin m → Bool)
    {ι : Type} [Fintype ι] [DecidableEq ι] (x z : ι → Fin n → ZMod 2) (y w : ι → Fin m → ZMod 2)
    (S : Fin q → Finset ι)
    (hS : ∀ k, ∑ p ∈ S k, (Matrix.vecMulVec (x p) (y p) + Matrix.vecMulVec (z p) (w p)) =
      anchor u v (fun i j => b2z (G k i j))) :
    ∃ (C : Circuit) (tap : Fin q → ℕ), ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ Fintype.card ι ∧
      ∀ k, (depthsOf (n + m) C.gates).getD (tap k) 0 ≤ 1 ∧ Represents (G k) ⟨C.gates, tap k⟩ := by
  classical
  let P : ι → Fin n → Fin m → ZMod 2 := fun p i j => (x p i + w p j) * (z p i + y p j)
  have hprod : ∀ s : Finset ι, ∃ (gs : List Gate) (wp : ι → ℕ), Valid n m gs ∧
      gs.countP nlGate = s.card ∧ ∀ p ∈ s, wp p < n + m + gs.length ∧
        (depthsOf (n + m) gs).getD (wp p) 0 ≤ 1 ∧
        ∀ i j, b2z ((wiresOf (oneEach i j) gs).getD (wp p) false) = P p i j := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨[], fun _ => 0, valid_nil n m, rfl, by simp⟩
    | insert a s ha ih =>
      obtain ⟨gs, wp, hv, hc, hp⟩ := ih
      obtain ⟨gs', out, hv', hlen, hout, hc', hd, hw, hdo, hval⟩ :=
        build_pair_and (x a) (z a) (y a) (w a) gs hv
      refine ⟨gs', Function.update wp a out, hv', ?_, fun p hp' => ?_⟩
      · rw [hc', hc, Finset.card_insert_of_notMem ha]
      · by_cases hpa : p = a
        · subst hpa
          rw [Function.update_self]
          exact ⟨hout, hdo, hval⟩
        · rw [Function.update_of_ne hpa]
          obtain ⟨l1, l2, l3⟩ := hp p ((Finset.mem_insert.mp hp').resolve_left hpa)
          refine ⟨by omega, ?_, fun i j => ?_⟩
          · rw [hd _ l1]; exact l2
          · rw [hw i j _ l1]; exact l3 i j
  obtain ⟨gs0, wp, hv0, hc0, hp0⟩ := hprod Finset.univ
  let h : Fin q → Fin n → Fin m → ZMod 2 := fun k i j => ∑ p ∈ S k, P p i j
  let g : Fin q → Fin n → Fin m → ZMod 2 := fun k i j => b2z (G k i j) + h k i j
  have two : ∀ a : ZMod 2, a + a = 0 := by decide
  have hg : ∀ k i j, g k i j + g k i v + g k u j + g k u v = 0 := by
    intro k
    have hterm : ∀ p, anchor u v (P p) = anchor u v (fun i j =>
        (Matrix.vecMulVec (x p) (y p) + Matrix.vecMulVec (z p) (w p)) i j) := by
      intro p
      have e := anchor_prod_split u v (x p) (z p) (w p) (y p)
      change anchor u v (fun i j => (x p i + w p j) * (z p i + y p j)) = _
      rw [e]
      ext i j
      simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
      ring
    have hh : ∀ i j, h k i j + h k i v + h k u j + h k u v =
        b2z (G k i j) + b2z (G k i v) + b2z (G k u j) + b2z (G k u v) := by
      intro i j
      have e1 : h k i j + h k i v + h k u j + h k u v = ∑ p ∈ S k, anchor u v (P p) i j := by
        simp only [h, anchor, Finset.sum_add_distrib]
      have e2 : ∀ a b, ∑ p ∈ S k, (Matrix.vecMulVec (x p) (y p) +
          Matrix.vecMulVec (z p) (w p)) a b = anchor u v (fun i j => b2z (G k i j)) a b := by
        intro a b
        rw [← hS k, Matrix.sum_apply]
      have e3 : ∑ p ∈ S k, anchor u v (P p) i j =
          anchor u v (fun i j => b2z (G k i j)) i j + anchor u v (fun i j => b2z (G k i j)) i v +
          anchor u v (fun i j => b2z (G k i j)) u j + anchor u v (fun i j => b2z (G k i j)) u v := by
        rw [← e2, ← e2, ← e2, ← e2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hterm p]
        rfl
      have z1 : anchor u v (fun i j => b2z (G k i j)) i v = 0 := by
        simp only [anchor]
        linear_combination two (b2z (G k i v)) + two (b2z (G k u v))
      have z2 : anchor u v (fun i j => b2z (G k i j)) u j = 0 := by
        simp only [anchor]
        linear_combination two (b2z (G k u j)) + two (b2z (G k u v))
      have z3 : anchor u v (fun i j => b2z (G k i j)) u v = 0 := by
        simp only [anchor]
        linear_combination two (b2z (G k u v)) + two (b2z (G k u v))
      rw [e1, e3, z1, z2, z3, add_zero, add_zero, add_zero]
      rfl
    intro i j
    simp only [g]
    linear_combination hh i j +
      two (b2z (G k i j) + b2z (G k i v) + b2z (G k u j) + b2z (G k u v))
  have houts : ∀ s : Finset (Fin q), ∃ (gs : List Gate) (tap : Fin q → ℕ), Valid n m gs ∧
      gs0.length ≤ gs.length ∧ gs.countP nlGate = gs0.countP nlGate ∧
      (∀ a < n + m + gs0.length, (depthsOf (n + m) gs).getD a 0 = (depthsOf (n + m) gs0).getD a 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ a < n + m + gs0.length, (wiresOf (oneEach i j) gs).getD a false =
        (wiresOf (oneEach i j) gs0).getD a false) ∧
      ∀ k ∈ s, tap k < n + m + gs.length ∧ (depthsOf (n + m) gs).getD (tap k) 0 ≤ 1 ∧
        ∀ i j, b2z ((wiresOf (oneEach i j) gs).getD (tap k) false) = b2z (G k i j) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      exact ⟨gs0, fun _ => 0, hv0, le_refl _, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, by simp⟩
    | insert k s hk ih =>
      obtain ⟨gs1, tap, hv1, hl1, hc1, hd1, hw1, ht⟩ := ih
      obtain ⟨gs2, r, hv2, hl2, hr, hc2, hd2, hw2, hdr, hvr⟩ :=
        build_row_fn (fun i => g k i v + g k u v) gs1 hv1
      obtain ⟨gs3, c, hv3, hl3, hc, hc3, hd3, hw3, hdc, hvc⟩ :=
        build_col_fn (fun j => g k u j) gs2 hv2
      have hwp : ∀ p, wp p < n + m + gs0.length := fun p => (hp0 p (Finset.mem_univ _)).1
      have hb : ∀ a ∈ r :: c :: (S k).toList.map wp, a < n + m + gs3.length := by
        intro a ha
        simp only [List.mem_cons, List.mem_map] at ha
        rcases ha with rfl | rfl | ⟨p, _, rfl⟩
        · omega
        · exact hc
        · have := hwp p; omega
      have hd : ∀ a ∈ r :: c :: (S k).toList.map wp, (depthsOf (n + m) gs3).getD a 0 ≤ 1 := by
        intro a ha
        simp only [List.mem_cons, List.mem_map] at ha
        rcases ha with rfl | rfl | ⟨p, _, rfl⟩
        · rw [hd3 _ hr, hdr]; omega
        · rw [hdc]; omega
        · have := hwp p
          rw [hd3 _ (by omega), hd2 _ (by omega), hd1 _ this]
          exact (hp0 p (Finset.mem_univ _)).2.1
      obtain ⟨gs4, out, hv4, hl4, ho, hc4, hd4, hw4, hdo, hvo⟩ :=
        build_xor_list 1 (r :: c :: (S k).toList.map wp) gs3 hv3 hb hd
      refine ⟨gs4, Function.update tap k out, hv4, by omega, by rw [hc4, hc3, hc2, hc1],
        fun a ha => ?_, fun i j a ha => ?_, fun k' hk' => ?_⟩
      · rw [hd4 _ (by omega), hd3 _ (by omega), hd2 _ (by omega), hd1 _ ha]
      · rw [hw4 i j _ (by omega), hw3 i j _ (by omega), hw2 i j _ (by omega), hw1 i j _ ha]
      · by_cases hkk : k' = k
        · subst hkk
          rw [Function.update_self]
          refine ⟨ho, hdo, fun i j => ?_⟩
          rw [hvo i j, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hw3 i j _ hr,
            hvr i j, hvc i j, List.map_map]
          have hs : ((S k').toList.map ((fun a => b2z ((wiresOf (oneEach i j) gs3).getD a false)) ∘ wp)).sum
              = h k' i j := by
            rw [Finset.sum_map_toList]
            refine Finset.sum_congr rfl fun p _ => ?_
            have := hwp p
            simp only [Function.comp]
            rw [hw3 i j _ (by omega), hw2 i j _ (by omega), hw1 i j _ this]
            exact (hp0 p (Finset.mem_univ _)).2.2 i j
          rw [hs]
          have e := hg k' i j
          have e' : g k' i j = b2z (G k' i j) + h k' i j := rfl
          linear_combination e - e' + two (h k' i j) - two (g k' i j) +
            two (b2z (G k' i j)) - two (b2z (G k' i j))
        · rw [Function.update_of_ne hkk]
          obtain ⟨l1, l2, l3⟩ := ht k' ((Finset.mem_insert.mp hk').resolve_left hkk)
          refine ⟨by omega, ?_, fun i j => ?_⟩
          · rw [hd4 _ (by omega), hd3 _ (by omega), hd2 _ l1]; exact l2
          · rw [hw4 i j _ (by omega), hw3 i j _ (by omega), hw2 i j _ l1]; exact l3 i j
  obtain ⟨gs, tap, hv, _, hc, _, _, ht⟩ := houts Finset.univ
  refine ⟨⟨gs, 0⟩, tap, hv.2, hv.1, ?_, fun k => ?_⟩
  · change gs.countP nlGate ≤ _
    rw [hc, hc0, Finset.card_univ]
  · obtain ⟨_, l2, l3⟩ := ht k (Finset.mem_univ _)
    exact ⟨l2, fun i j => b2z_inj (l3 i j)⟩

theorem upper {n m q : ℕ} (u : Fin n) (v : Fin m) (G : Fin q → Fin n → Fin m → Bool)
    (A : Fin q → Matrix (Fin n) (Fin m) (ZMod 2))
    (hAG : ∀ k, A k = anchor u v (fun i j => b2z (G k i j)))
    (partner : Equiv.Perm (Fin q)) (hinv : ∀ i, partner (partner i) = i)
    (hpair : ∀ i, partner i ≠ i → (3 ≤ (A i).rank ∧ (A i).rank % 2 = 1) ∧
      (3 ≤ (A (partner i)).rank ∧ (A (partner i)).rank % 2 = 1) ∧
      (Matrix.fromRows (A i) (A (partner i))).rank + 2 ≤ (A i).rank + (A (partner i)).rank) :
    ∃ (C : Circuit) (tap : Fin q → ℕ), ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nlGate ≤ (∑ i : Fin q, ((A i).rank + 1) / 2) -
        (Finset.univ.filter (fun j : Fin q => partner j ≠ j)).card / 2 ∧
      ∀ k, (depthsOf (n + m) C.gates).getD (tap k) 0 ≤ 1 ∧ Represents (G k) ⟨C.gates, tap k⟩ := by
  classical
  have hsh : ∀ k : Fin q, ∃ (x : Fin n → ZMod 2) (y : Fin m → ZMod 2) (z : Fin n → ZMod 2)
      (w : Fin m → ZMod 2), partner k ≠ k →
      (A k - (Matrix.vecMulVec x y + Matrix.vecMulVec z w)).rank < (A k).rank ∧
      (A (partner k) - (Matrix.vecMulVec x y + Matrix.vecMulVec z w)).rank < (A (partner k)).rank := by
    intro k
    by_cases hk : partner k = k
    · exact ⟨0, 0, 0, 0, fun h => absurd hk h⟩
    · obtain ⟨x, y, z, w, h⟩ := plane _ _ (hpair k hk).2.2
      exact ⟨x, y, z, w, fun _ => h⟩
  choose X Y Z W hXW using hsh
  let M : Fin q → Matrix (Fin n) (Fin m) (ZMod 2) :=
    fun k => Matrix.vecMulVec (X k) (Y k) + Matrix.vecMulVec (Z k) (W k)
  let Nk : Fin q → Matrix (Fin n) (Fin m) (ZMod 2) :=
    fun k => if partner k = k then 0 else M (min k (partner k))
  let a : Fin q → ℕ := fun k => if partner k = k then ((A k).rank + 1) / 2 else ((A k).rank - 1) / 2
  have hrank : ∀ k, (A k - Nk k).rank ≤ a k + a k := by
    intro k
    by_cases hk : partner k = k
    · simp only [Nk, a, if_pos hk, sub_zero]
      omega
    · have hlt : (A k - M (min k (partner k))).rank < (A k).rank := by
        rcases lt_or_gt_of_ne hk with hlt | hlt
        · rw [min_eq_right hlt.le]
          have h := (hXW (partner k) (by rw [hinv]; exact Ne.symm hk)).2
          rw [hinv] at h
          exact h
        · rw [min_eq_left hlt.le]
          exact (hXW k hk).1
      have hodd := (hpair k hk).1
      simp only [Nk, a, if_neg hk]
      omega
  have hfac := fun k => factor_of_rank_le (A k - Nk k) (hrank k)
  choose rv cv hfac using hfac
  let ι := (Σ k : Fin q, Fin (a k)) ⊕ {j : Fin q // j < partner j}
  let x : ι → Fin n → ZMod 2 :=
    Sum.elim (fun s => rv s.1 (Fin.castAdd _ s.2)) (fun j => X j.1)
  let y : ι → Fin m → ZMod 2 :=
    Sum.elim (fun s => cv s.1 (Fin.castAdd _ s.2)) (fun j => Y j.1)
  let z : ι → Fin n → ZMod 2 :=
    Sum.elim (fun s => rv s.1 (Fin.natAdd _ s.2)) (fun j => Z j.1)
  let w : ι → Fin m → ZMod 2 :=
    Sum.elim (fun s => cv s.1 (Fin.natAdd _ s.2)) (fun j => W j.1)
  let S : Fin q → Finset ι := fun k =>
    (Finset.univ.image (fun l : Fin (a k) => (⟨k, l⟩ : Σ k : Fin q, Fin (a k)))).disjSum
      (Finset.univ.filter (fun j : {j : Fin q // j < partner j} =>
        partner k ≠ k ∧ j.1 = min k (partner k)))
  have hS : ∀ k, ∑ p ∈ S k, (Matrix.vecMulVec (x p) (y p) + Matrix.vecMulVec (z p) (w p)) =
      anchor u v (fun i j => b2z (G k i j)) := by
    intro k
    rw [← hAG]
    have h1 : ∑ l ∈ Finset.univ.image (fun l : Fin (a k) => (⟨k, l⟩ : Σ k : Fin q, Fin (a k))),
        (Matrix.vecMulVec (x (Sum.inl l)) (y (Sum.inl l)) +
          Matrix.vecMulVec (z (Sum.inl l)) (w (Sum.inl l))) = A k - Nk k := by
      rw [Finset.sum_image (fun l1 _ l2 _ h => by simpa using h)]
      ext i j
      rw [hfac k i j, Fin.sum_univ_add, Matrix.sum_apply]
      simp only [x, y, z, w, Sum.elim_inl, Matrix.add_apply, Matrix.vecMulVec_apply,
        Finset.sum_add_distrib]
    have h2 : ∑ j ∈ Finset.univ.filter (fun j : {j : Fin q // j < partner j} =>
          partner k ≠ k ∧ j.1 = min k (partner k)),
        (Matrix.vecMulVec (x (Sum.inr j)) (y (Sum.inr j)) +
          Matrix.vecMulVec (z (Sum.inr j)) (w (Sum.inr j))) = Nk k := by
      by_cases hk : partner k = k
      · rw [Finset.filter_false_of_mem (fun j _ h => h.1 hk), Finset.sum_empty]
        simp only [Nk, if_pos hk]
      · have hmin : min k (partner k) < partner (min k (partner k)) := by
          rcases lt_or_gt_of_ne hk with hlt | hlt
          · rw [min_eq_right hlt.le, hinv]; exact hlt
          · rw [min_eq_left hlt.le]; exact hlt
        have e : Finset.univ.filter (fun j : {j : Fin q // j < partner j} =>
            partner k ≠ k ∧ j.1 = min k (partner k)) = {⟨min k (partner k), hmin⟩} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h; exact Subtype.ext h.2
          · intro h; exact ⟨hk, congrArg Subtype.val h⟩
        rw [e, Finset.sum_singleton]
        simp only [Nk, if_neg hk]
        rfl
    change ∑ p ∈ Finset.disjSum _ _, _ = _
    rw [Finset.sum_disjSum, h1, h2, sub_add_cancel]
  obtain ⟨C, tap, h1, h2, h3, h4⟩ := realize u v G x z y w S hS
  refine ⟨C, tap, h1, h2, le_trans h3 ?_, h4⟩
  have hcard : Fintype.card ι =
      ∑ k, a k + (Finset.univ.filter (fun j : Fin q => j < partner j)).card := by
    simp only [ι, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Fintype.card_subtype]
  have hswap : (Finset.univ.filter (fun j : Fin q => partner j < j)).card =
      (Finset.univ.filter (fun j : Fin q => j < partner j)).card := by
    refine Finset.card_nbij' partner partner ?_ ?_ (fun j _ => hinv j) (fun j _ => hinv j)
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
      rw [hinv]; exact hj
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
      rw [hinv]; exact hj
  have hmoved : (Finset.univ.filter (fun j : Fin q => partner j ≠ j)).card =
      (Finset.univ.filter (fun j : Fin q => j < partner j)).card +
      (Finset.univ.filter (fun j : Fin q => partner j < j)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      rw [ne_comm, ne_iff_lt_or_gt]
    · rw [Finset.disjoint_filter]
      intro j _ h h'
      exact absurd (lt_trans h h') (lt_irrefl _)
  have hsum : ∑ i : Fin q, ((A i).rank + 1) / 2 =
      ∑ k, a k + (Finset.univ.filter (fun j : Fin q => partner j ≠ j)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : partner k = k
    · simp [a, hk]
    · have hodd := (hpair k hk).1
      simp only [a, if_neg hk, if_pos (show partner k ≠ k from hk)]
      omega
  omega

end PEqualNP.Outside.L_meta_25753_aux

theorem PEqualNP.Outside.L_meta_25753 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
∀ (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let F := ZMod 2
  let entry := fun j x y => if G j x y then (1 : F) else 0
  let A : Fin q → Matrix (Fin n) (Fin m) F := fun j x y =>
    entry j x y + entry j x v + entry j u y + entry j u v
  let allCols : Matrix (Fin n) (Fin q × Fin m) F := fun x z => A z.1 x z.2
  let r := fun i : Fin q => (A i).rank
  let total := ∑ i : Fin q, r i
  let singles := (Finset.univ.filter (fun j : Fin q => r j = 1)).card
  let oddBig := fun i : Fin q => 3 ≤ r i ∧ r i % 2 = 1
  allCols.rank = total →
  (∀ t : ℕ, fits n m q G t → singles+(total-singles+1)/2 ≤ t) ∧
  (∀ partner : Equiv.Perm (Fin q), (∀ i, partner (partner i) = i) →
    (∀ i, partner i ≠ i → oddBig i ∧ oddBig (partner i) ∧
      (Matrix.fromRows (A i) (A (partner i))).rank+2 ≤ r i + r (partner i)) →
    let moved := (Finset.univ.filter (fun j : Fin q => partner j ≠ j)).card
    fits n m q G ((∑ i : Fin q, (r i+1)/2) - moved/2))
) := by
  intro nonlinear depths fits n m q G u v F entry A allCols r total singles oddBig hind
  have hAG : ∀ k, A k = PEqualNP.Outside.L_meta_25753_aux.anchor u v
      (fun i j => PEqualNP.Outside.L_meta_25753_aux.b2z (G k i j)) := fun _ => rfl
  refine ⟨fun t hfit => ?_, fun partner hinv hpair => ?_⟩
  · obtain ⟨C, tap, hrb, hlen, hcnt, htap⟩ := hfit
    obtain ⟨K, N, hK, hN, hspan⟩ :=
      PEqualNP.Outside.L_meta_25753_aux.decomp u v t C hlen hrb hcnt
    have hmem : ∀ j, A j ∈ Submodule.span (ZMod 2) (Set.range N) := by
      intro j
      have h := hspan (tap j) (htap j).1
      have e : (fun i j' => PEqualNP.Outside.L_meta_25753_aux.b2z
            ((PEqualNP.Outside.L_meta_25753_aux.wiresOf
              (PEqualNP.Represents.oneEach i j') C.gates).getD (tap j) false)) =
          fun i j' => PEqualNP.Outside.L_meta_25753_aux.b2z (G j i j') := by
        funext i j'
        exact congrArg _ ((htap j).2 i j')
      rw [e] at h
      exact h
    exact le_trans (PEqualNP.Outside.L_meta_25753_aux.lower A N hN hmem hind) hK
  · exact PEqualNP.Outside.L_meta_25753_aux.upper u v G A hAG partner hinv hpair
