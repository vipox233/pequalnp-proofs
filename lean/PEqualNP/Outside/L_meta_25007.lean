import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25007_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem tb_full (q : ℕ) : (63 : ℕ).testBit q = decide (q < 6) :=
  Nat.testBit_two_pow_sub_one 6 q

def opM : GateOp → List ℕ → ℕ
  | .and, l => l.foldr (· &&& ·) 63
  | .or, l => l.foldr (· ||| ·) 0
  | .not, l => 63 ^^^ l.headD 0
  | _, _ => 0

def stpM (w : List ℕ) (g : Gate) : List ℕ := w ++ [opM g.op (g.inputs.map fun i => w.getD i 0)]

theorem opM_tb (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (l : List ℕ) (p : ℕ)
    (hp : p < 6) : (opM op l).testBit p = op.eval (l.map (·.testBit p)) := by
  rcases hop with rfl | rfl | rfl
  · induction l with
    | nil => simp [opM, GateOp.eval, tb_full, hp]
    | cons a l ih =>
      simp only [opM, GateOp.eval, List.foldr_cons, Nat.testBit_land, List.map_cons,
        List.all_cons, id] at ih ⊢
      rw [ih]
  · induction l with
    | nil => simp [opM, GateOp.eval]
    | cons a l ih =>
      simp only [opM, GateOp.eval, List.foldr_cons, Nat.testBit_lor, List.map_cons,
        List.any_cons, id] at ih ⊢
      rw [ih]
  · cases l <;> simp [opM, GateOp.eval, tb_full, hp, Nat.testBit_xor]

theorem getD_tb (w : List ℕ) (i p : ℕ) :
    (w.map (·.testBit p)).getD i false = (w.getD i 0).testBit p := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

theorem bridge (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (p : ℕ) (hp : p < 6) (w : List ℕ) :
    (gs.foldl stpM w).map (·.testBit p) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map (·.testBit p)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (fun g' h => hg g' (by simp [h]))]
    congr 1
    simp only [stpM, List.map_append, List.map_cons, List.map_nil, opM_tb _ (hg g (by simp)) _ p hp,
      List.map_map]
    congr 3
    apply List.map_congr_left
    intro i _
    exact (getD_tb w i p).symm

/-- The values one gate can produce from the values in `L`. -/
def nv (L : List ℕ) : List ℕ :=
  63 :: 0 :: (L.map (63 ^^^ ·) ++ L.flatMap fun x => L.flatMap fun y => [x &&& y, x ||| y])

def msk (l : List ℕ) (a : ℕ) : ℕ := l.foldl (fun a v => a ||| 1 <<< v) a

theorem msk_tb : ∀ (l : List ℕ) (a v : ℕ), (a.testBit v = true ∨ v ∈ l) → (msk l a).testBit v = true
  | [], a, v, h => by simpa [msk] using h
  | x :: l, a, v, h => by
    show (msk l (a ||| 1 <<< x)).testBit v = true
    apply msk_tb l
    rcases h with h | h
    · left; simp [Nat.testBit_lor, h]
    · rcases List.mem_cons.1 h with rfl | h
      · left; simp [Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow_self]
      · right; exact h

def hit (t : ℕ) (L : List ℕ) : Bool :=
  t == 63 || t == 0 || L.contains (63 ^^^ t) ||
  ((L.filter fun x => x &&& t == t).any fun x => (L.filter fun x => x &&& t == t).any fun y => x &&& y == t) ||
  ((L.filter fun x => x ||| t == t).any fun x => (L.filter fun x => x ||| t == t).any fun y => x ||| y == t)

theorem hit_of (L : List ℕ) (v : ℕ) (hv : v ∈ nv L) : hit v L = true := by
  simp only [nv, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl | rfl⟩
  · simp [hit]
  · simp [hit]
  · have e : 63 ^^^ (63 ^^^ x) = x := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    simp [hit, e, hx]
  · have e1 : x &&& (x &&& y) = x &&& y := Nat.eq_of_testBit_eq fun i => by
      simp only [Nat.testBit_land]; cases x.testBit i <;> cases y.testBit i <;> rfl
    have e2 : y &&& (x &&& y) = x &&& y := Nat.eq_of_testBit_eq fun i => by
      simp only [Nat.testBit_land]; cases x.testBit i <;> cases y.testBit i <;> rfl
    have : ((L.filter fun z => z &&& (x &&& y) == x &&& y).any fun a =>
        (L.filter fun z => z &&& (x &&& y) == x &&& y).any fun b => a &&& b == x &&& y) = true :=
      List.any_eq_true.2 ⟨x, List.mem_filter.2 ⟨hx, by simp [e1]⟩,
        List.any_eq_true.2 ⟨y, List.mem_filter.2 ⟨hy, by simp [e2]⟩, by simp⟩⟩
    simp only [hit, this, Bool.or_true, Bool.true_or]
  · have e1 : x ||| (x ||| y) = x ||| y := Nat.eq_of_testBit_eq fun i => by
      simp only [Nat.testBit_lor]; cases x.testBit i <;> cases y.testBit i <;> rfl
    have e2 : y ||| (x ||| y) = x ||| y := Nat.eq_of_testBit_eq fun i => by
      simp only [Nat.testBit_lor]; cases x.testBit i <;> cases y.testBit i <;> rfl
    have : ((L.filter fun z => z ||| (x ||| y) == x ||| y).any fun a =>
        (L.filter fun z => z ||| (x ||| y) == x ||| y).any fun b => a ||| b == x ||| y) = true :=
      List.any_eq_true.2 ⟨x, List.mem_filter.2 ⟨hx, by simp [e1]⟩,
        List.any_eq_true.2 ⟨y, List.mem_filter.2 ⟨hy, by simp [e2]⟩, by simp⟩⟩
    simp only [hit, this, Bool.or_true, Bool.true_or]

theorem nv_lt (L : List ℕ) (hL : ∀ x ∈ L, x < 64) : ∀ v ∈ nv L, v < 64 := by
  intro v hv
  simp only [nv, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl | rfl⟩
  · decide
  · decide
  · exact Nat.xor_lt_two_pow (n := 6) (by decide) (hL x hx)
  · exact Nat.and_lt_two_pow (n := 6) x (hL y hy)
  · exact Nat.or_lt_two_pow (n := 6) (hL x hx) (hL y hy)

theorem m63 (a : ℕ) (h : a < 64) : a &&& 63 = a :=
  (Nat.and_two_pow_sub_one_eq_mod a 6).trans (Nat.mod_eq_of_lt h)

theorem opM_mem (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (L : List ℕ)
    (hL : ∀ x ∈ L, x < 64) : ∀ vs : List ℕ, vs.length ≤ 2 → (∀ x ∈ vs, x ∈ L) →
    opM op vs ∈ L ∨ opM op vs ∈ nv L
  | [], _, _ => by right; rcases hop with rfl | rfl | rfl <;> simp [opM, nv]
  | [a], _, h => by
    have ha := h a (by simp)
    rcases hop with rfl | rfl | rfl
    · left; simp only [opM, List.foldr_cons, List.foldr_nil, m63 a (hL a ha)]; exact ha
    · left; simp only [opM, List.foldr_cons, List.foldr_nil, Nat.or_zero]; exact ha
    · right
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.2 ⟨a, ha, rfl⟩)))
  | [a, b], _, h => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    right
    rcases hop with rfl | rfl | rfl
    · simp only [opM, List.foldr_cons, List.foldr_nil, m63 b (hL b hb)]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, by simp⟩⟩)))
    · simp only [opM, List.foldr_cons, List.foldr_nil, Nat.or_zero]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, by simp⟩⟩)))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.2 ⟨a, ha, rfl⟩)))
  | _ :: _ :: _ :: _, h, _ => by simp at h

def good (t : ℕ) : ℕ → List ℕ → Bool
  | 0, L => !L.contains t
  | 1, L => !L.contains t && !hit t L
  | k + 2, L => !L.contains t && good t (k + 1) L &&
      (List.range 64).all fun v => !(msk (nv L) 0).testBit v || L.contains v || good t (k + 1) (L ++ [v])

theorem good_nt (t k : ℕ) (L : List ℕ) (h : good t k L = true) : t ∉ L := by
  match k with
  | 0 => simpa [good] using h
  | 1 => simp only [good, Bool.and_eq_true] at h; simpa using h.1
  | k + 2 => simp only [good, Bool.and_eq_true] at h; simpa using h.1.1

theorem inv (t : ℕ) : ∀ (gs : List Gate) (k : ℕ) (L W : List ℕ),
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → good t k L = true → (∀ x ∈ L, x < 64) → 0 ∈ L → (∀ x ∈ W, x ∈ L) →
    ∀ x ∈ gs.foldl stpM W, x ≠ t ∧ x < 64 := by
  intro gs
  induction gs with
  | nil =>
    intro k L W _ _ hg hL _ hW x hx
    exact ⟨fun e => good_nt t k L hg (e ▸ hW x hx), hL x (hW x hx)⟩
  | cons g gs ih =>
    intro k L W hgs hk hgood hL h0 hW
    obtain ⟨hop, h2⟩ := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or ∨ g'.op = .not) ∧ g'.inputs.length ≤ 2 :=
      fun g' h => hgs g' (by simp [h])
    rw [List.foldl_cons]
    have hB : ∀ v ∈ g.inputs.map (fun i => W.getD i 0), v ∈ L := by
      intro v hv
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hv
      rw [List.getD_eq_getElem?_getD]
      cases h : W[i]? with
      | none => simpa using h0
      | some y => exact hW y (List.mem_of_getElem? h)
    have hc := opM_mem g.op hop L hL _ (by simpa using h2) hB
    have hst : stpM W g = W ++ [opM g.op (g.inputs.map (fun i => W.getD i 0))] := rfl
    rw [hst]
    generalize opM g.op (g.inputs.map (fun i => W.getD i 0)) = v at hc
    rcases k with _ | _ | k
    · simp at hk
    · have e : gs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hk; omega)
      subst e
      simp only [good, Bool.and_eq_true, Bool.not_eq_true'] at hgood
      intro x hx
      rw [List.foldl_nil, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ⟨fun e => by simp [← e, hW x hx] at hgood, hL x (hW x hx)⟩
      · rcases hc with hc | hc
        · exact ⟨fun e => by simp [← e, hc] at hgood, hL x hc⟩
        · exact ⟨fun e => by rw [e] at hc; simp [hit_of L t hc] at hgood, nv_lt L hL x hc⟩
    · have hk' : gs.length ≤ k + 1 := by simp at hk; omega
      simp only [good, Bool.and_eq_true] at hgood
      by_cases hvL : v ∈ L
      · refine ih (k + 1) L _ hgs' hk' hgood.1.2 hL h0 ?_
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hW x hx
        · rw [List.mem_singleton.1 hx]; exact hvL
      · have hnv : v ∈ nv L := hc.resolve_left hvL
        have hv64 := nv_lt L hL v hnv
        have h3 := List.all_eq_true.1 hgood.2 v (List.mem_range.2 hv64)
        simp only [msk_tb (nv L) 0 v (Or.inr hnv), Bool.not_true, Bool.false_or, Bool.or_eq_true,
          List.contains_iff_mem, hvL, false_or] at h3
        refine ih (k + 1) _ _ hgs' hk' h3 ?_ (by simp [h0]) ?_
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hL x hx
          · rw [List.mem_singleton.1 hx]; exact hv64
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact List.mem_append_left _ (hW x hx)
          · exact List.mem_append_right _ hx

def B0 : List ℕ := [0, 7, 56, 9, 18, 36]

def tgt (b : Bool) : ℕ := if b then 21 else 49

theorem chk : ∀ b : Bool, good (tgt b) 3 B0 = true := by decide +kernel

def rm {n : ℕ} (a1 a2 i : Fin n) : ℕ :=
  if i = a1 then 7 else if i = a2 then 56 else 0

def cm {n : ℕ} (b1 b2 b3 j : Fin n) : ℕ :=
  if j = b1 then 9 else if j = b2 then 18 else if j = b3 then 36 else 0

theorem rm_tb {n : ℕ} (a1 a2 : Fin n) (h12 : a1 ≠ a2) (i : Fin n) :
    (rm a1 a2 i).testBit 0 = decide (i = a1) ∧ (rm a1 a2 i).testBit 1 = decide (i = a1) ∧
    (rm a1 a2 i).testBit 2 = decide (i = a1) ∧ (rm a1 a2 i).testBit 3 = decide (i = a2) ∧
    (rm a1 a2 i).testBit 4 = decide (i = a2) ∧ (rm a1 a2 i).testBit 5 = decide (i = a2) := by
  unfold rm
  by_cases x : i = a1
  · subst x; simp only [h12, ite_true, decide_true, decide_false]; decide
  by_cases y : i = a2
  · subst y; simp only [x, ite_true, ite_false, decide_true, decide_false]; decide
  simp only [x, y, ite_false, decide_false]; decide

theorem cm_tb {n : ℕ} (b1 b2 b3 : Fin n) (h12 : b1 ≠ b2) (h13 : b1 ≠ b3) (h23 : b2 ≠ b3)
    (j : Fin n) :
    (cm b1 b2 b3 j).testBit 0 = decide (j = b1) ∧ (cm b1 b2 b3 j).testBit 1 = decide (j = b2) ∧
    (cm b1 b2 b3 j).testBit 2 = decide (j = b3) ∧ (cm b1 b2 b3 j).testBit 3 = decide (j = b1) ∧
    (cm b1 b2 b3 j).testBit 4 = decide (j = b2) ∧ (cm b1 b2 b3 j).testBit 5 = decide (j = b3) := by
  unfold cm
  by_cases x : j = b1
  · subst x; simp only [h12, h13, ite_true, decide_true, decide_false]; decide
  by_cases y : j = b2
  · subst y; simp only [x, h23, ite_true, ite_false, decide_true, decide_false]; decide
  by_cases z : j = b3
  · subst z; simp only [x, y, ite_true, ite_false, decide_true, decide_false]; decide
  simp only [x, y, z, ite_false, decide_false]; decide

theorem pt {n : ℕ} (r c : Fin n → ℕ) (u v : Fin n) (p : ℕ)
    (hu : ∀ i, (r i).testBit p = decide (i = u)) (hv : ∀ j, (c j).testBit p = decide (j = v)) :
    oneEach u v = (List.ofFn r ++ List.ofFn c).map (·.testBit p) := by
  simp only [oneEach, List.map_append, List.map_ofFn]
  congr 1 <;> congr 1 <;> funext i
  · exact (hu i).symm
  · exact (hv i).symm

theorem three {n : ℕ} (hn : 3 ≤ n) (a1 a2 : Fin n) : ∃ a3 : Fin n, a1 ≠ a3 ∧ a2 ≠ a3 := by
  by_contra h
  push_neg at h
  have : (Finset.univ : Finset (Fin n)) ⊆ {a1, a2} := fun x _ => by
    by_cases e : a1 = x
    · simp [e]
    · simp [h x e]
  have := (Finset.card_le_card this).trans Finset.card_le_two
  simp at this; omega

end PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.Outside.L_meta_25007_aux PEqualNP.CircuitLowerBounds PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25007 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C := by
  rintro n S T hn ⟨a1, ha1⟩ ⟨a2, ha2⟩ ⟨b1, hb1⟩ ⟨b2, hb2⟩ ⟨C, hF, hs, hR⟩
  rw [Finset.mem_compl] at ha2 hb2
  have h12 : a1 ≠ a2 := fun e => ha2 (e ▸ ha1)
  have g12 : b1 ≠ b2 := fun e => hb2 (e ▸ hb1)
  obtain ⟨b3, g13, g23⟩ := three hn b1 b2
  have hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 :=
    fun g h => ⟨by simpa using (hF g h).1, (hF g h).2⟩
  have E : ∀ (u v : Fin n) (p : ℕ), p < 6 → (∀ i, (rm a1 a2 i).testBit p = decide (i = u)) →
      (∀ j, (cm b1 b2 b3 j).testBit p = decide (j = v)) →
      ((C.gates.foldl stpM (List.ofFn (rm a1 a2) ++ List.ofFn (cm b1 b2 b3))).getD
        C.output 0).testBit p = decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T)) := by
    intro u v p hp hu hv
    have e := hR u v
    simp only [Circuit.eval, Circuit.wires, pt _ _ u v p hu hv] at e
    rw [← bridge _ (fun g h => (hg g h).1) p hp, getD_tb] at e
    exact e
  have R := rm_tb a1 a2 h12
  have K := cm_tb b1 b2 b3 g12 g13 g23
  have hsub : ∀ x ∈ List.ofFn (rm a1 a2) ++ List.ofFn (cm b1 b2 b3), x ∈ B0 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx <;> obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    · unfold rm; split_ifs <;> simp [B0]
    · unfold cm; split_ifs <;> simp [B0]
  have I := inv (tgt (decide (b3 ∈ T))) C.gates 3 B0 _ hg hs (chk (decide (b3 ∈ T)))
    (by simp [B0]) (by simp [B0]) hsub
  have hO : ((C.gates.foldl stpM (List.ofFn (rm a1 a2) ++ List.ofFn (cm b1 b2 b3))).getD
      C.output 0) ≠ tgt (decide (b3 ∈ T)) ∧
      ((C.gates.foldl stpM (List.ofFn (rm a1 a2) ++ List.ofFn (cm b1 b2 b3))).getD
      C.output 0) < 64 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (C.gates.foldl stpM (List.ofFn (rm a1 a2) ++ List.ofFn (cm b1 b2 b3)))[C.output]? with
    | none => by_cases t : b3 ∈ T <;> simp [tgt, t]
    | some y => exact I y (List.mem_of_getElem? h)
  apply hO.1
  refine Nat.eq_of_testBit_eq fun p => ?_
  by_cases hp : p < 6
  · interval_cases p
    · rw [E a1 b1 0 (by omega) (fun i => (R i).1) (fun j => (K j).1)]
      by_cases t : b3 ∈ T <;> simp [t, ha1, ha2, hb1, hb2, tgt] <;> decide
    · rw [E a1 b2 1 (by omega) (fun i => (R i).2.1) (fun j => (K j).2.1)]
      by_cases t : b3 ∈ T <;> simp [t, ha1, ha2, hb1, hb2, tgt] <;> decide
    · rw [E a1 b3 2 (by omega) (fun i => (R i).2.2.1) (fun j => (K j).2.2.1)]
      by_cases t : b3 ∈ T <;> simp [t, ha1, ha2, hb1, hb2, tgt] <;> decide
    · rw [E a2 b1 3 (by omega) (fun i => (R i).2.2.2.1) (fun j => (K j).2.2.2.1)]
      by_cases t : b3 ∈ T <;> simp [t, ha1, ha2, hb1, hb2, tgt] <;> decide
    · rw [E a2 b2 4 (by omega) (fun i => (R i).2.2.2.2.1) (fun j => (K j).2.2.2.2.1)]
      by_cases t : b3 ∈ T <;> simp [t, ha1, ha2, hb1, hb2, tgt] <;> decide
    · rw [E a2 b3 5 (by omega) (fun i => (R i).2.2.2.2.2) (fun j => (K j).2.2.2.2.2)]
      by_cases t : b3 ∈ T <;> simp [t, ha1, ha2, hb1, hb2, tgt] <;> decide
  · have h64 : (64 : ℕ) ≤ 2 ^ p := (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hp) : 2 ^ 6 ≤ 2 ^ p)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hO.2 h64),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by by_cases t : b3 ∈ T <;> simp [tgt, t]) h64)]
