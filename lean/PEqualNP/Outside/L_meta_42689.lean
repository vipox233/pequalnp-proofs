import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42689

open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 8

def bit (r : Fin 8) (v : W) : Bool := v.getLsbD r.val

def gop : GateOp → List W → W
  | GateOp.and, l => l.foldr (fun a b => a &&& b) (BitVec.allOnes 8)
  | GateOp.or, l => l.foldr (fun a b => a ||| b) 0
  | GateOp.not, l => ~~~(l.headD 0)
  | _, _ => 0

def stepW (w : List W) (g : Gate) : List W :=
  w ++ [gop g.op (g.inputs.map fun i => w.getD i 0)]

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gop_bit (r : Fin 8) (op : GateOp)
    (h : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List W) :
    op.eval (l.map (bit r)) = bit r (gop op l) := by
  rcases h with rfl | rfl | rfl
  · show (l.map (bit r)).all id = bit r (l.foldr (fun a b => a &&& b) (BitVec.allOnes 8))
    induction l with
    | nil => revert r; decide
    | cons a t ih =>
      simp only [List.map_cons, List.all_cons, List.foldr_cons, id]
      rw [ih]
      simp [bit, BitVec.getLsbD_and]
  · show (l.map (bit r)).any id = bit r (l.foldr (fun a b => a ||| b) 0)
    induction l with
    | nil => revert r; decide
    | cons a t ih =>
      simp only [List.map_cons, List.any_cons, List.foldr_cons, id]
      rw [ih]
      simp [bit, BitVec.getLsbD_or]
  · show (!((l.map (bit r)).headD false)) = bit r (~~~(l.headD 0))
    cases l with
    | nil => revert r; decide
    | cons a t =>
      have hr := r.isLt
      simp [bit, BitVec.getLsbD_not, hr]

theorem getD_bit (r : Fin 8) (w : List W) (i : ℕ) :
    (w.map (bit r)).getD i false = bit r (w.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [bit]

theorem step_bit (r : Fin 8) (w : List W) (g : Gate) (hg : Legal g) :
    stepB (w.map (bit r)) g = (stepW w g).map (bit r) := by
  simp only [stepB, stepW, List.map_append, List.map_cons, List.map_nil]
  rw [← gop_bit r g.op hg.1, List.map_map]
  congr 3
  apply List.map_congr_left
  intro i _
  exact getD_bit r w i

theorem fold_bit (r : Fin 8) (gs : List Gate) (hl : ∀ g ∈ gs, Legal g) (w : List W) :
    gs.foldl stepB (w.map (bit r)) = (gs.foldl stepW w).map (bit r) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [step_bit r w g (hl g (by simp))]
    exact ih (fun g' h => hl g' (by simp [h])) _

def W0 : List W := [0xAA#8, 0xCC#8, 0xF0#8, 0#8, 0xFF#8]

def row (r : Fin 8) : Fin 3 → Bool := fun i => r.val.testBit i.val

theorem init_bit (r : Fin 8) : List.ofFn (row r) ++ [false, true] = W0.map (bit r) := by
  revert r; decide

theorem getD_mem (w : List W) (i : ℕ) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => right; rfl
  | some v => left; exact List.mem_of_getElem? h

def need (S : List ℕ) : ℕ :=
  (if S.any (fun v => v == 232) then 0 else 1) +
  (if S.any (fun v => v &&& 232 == 96) then 0 else 1) +
  (if S.any (fun v => v &&& 232 == 40) then 0 else 1)

def pairs : List ℕ → List ℕ
  | [] => []
  | a :: rest => (255 - a) :: ((rest.flatMap fun b => [a &&& b, a ||| b]) ++ pairs rest)

def kids (S : List ℕ) : List ℕ := (pairs S).filter (fun z => !S.contains z)

def search : ℕ → List ℕ → Bool
  | 0, S => need S == 0
  | k + 1, S =>
    if need S == 0 then true else if k + 1 < need S then false
    else (kids S).any (fun z => search k (z :: S))

theorem any_mono (f : ℕ → Bool) {T S : List ℕ} (h : ∀ v ∈ T, v ∈ S) :
    T.any f = true → S.any f = true := by
  simp only [List.any_eq_true]
  rintro ⟨v, hv, hf⟩
  exact ⟨v, h v hv, hf⟩

theorem ite_mono (a b : Bool) (h : b = true → a = true) :
    (if a then 0 else 1 : ℕ) ≤ (if b then 0 else 1) := by
  cases a <;> cases b <;> simp_all

theorem need_anti {T S : List ℕ} (h : ∀ v ∈ T, v ∈ S) : need S ≤ need T := by
  unfold need
  have h1 := ite_mono _ _ (any_mono (fun v => v == 232) h)
  have h2 := ite_mono _ _ (any_mono (fun v => v &&& 232 == 96) h)
  have h3 := ite_mono _ _ (any_mono (fun v => v &&& 232 == 40) h)
  omega

theorem arith (d1 d2 d3 c1 c2 c3 : Bool) (e12 : ¬(d1 = true ∧ d2 = true))
    (e13 : ¬(d1 = true ∧ d3 = true)) (e23 : ¬(d2 = true ∧ d3 = true)) :
    ((if c1 = true then 0 else 1) + (if c2 = true then 0 else 1) + (if c3 = true then 0 else 1) : ℕ) ≤
    ((if (d1 || c1) = true then 0 else 1) + (if (d2 || c2) = true then 0 else 1) +
      (if (d3 || c3) = true then 0 else 1)) + 1 := by
  cases d1 <;> cases d2 <;> cases d3 <;> cases c1 <;> cases c2 <;> cases c3 <;> simp_all

theorem need_cons (z : ℕ) (S : List ℕ) : need S ≤ need (z :: S) + 1 := by
  have e12 : ¬((z == 232) = true ∧ (z &&& 232 == 96) = true) := by
    rintro ⟨h1, h2⟩
    simp only [beq_iff_eq] at h1 h2
    subst h1
    exact absurd h2 (by decide)
  have e13 : ¬((z == 232) = true ∧ (z &&& 232 == 40) = true) := by
    rintro ⟨h1, h2⟩
    simp only [beq_iff_eq] at h1 h2
    subst h1
    exact absurd h2 (by decide)
  have e23 : ¬((z &&& 232 == 96) = true ∧ (z &&& 232 == 40) = true) := by
    rintro ⟨h1, h2⟩
    simp only [beq_iff_eq] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  simp only [need, List.any_cons]
  exact arith _ _ _ _ _ _ e12 e13 e23

theorem not_mem_pairs {a : ℕ} {S : List ℕ} (h : a ∈ S) : 255 - a ∈ pairs S := by
  induction S with
  | nil => simp at h
  | cons x rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih h))

theorem and_mem_pairs {a b : ℕ} {S : List ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    a &&& b ∈ pairs S ∨ a &&& b ∈ S := by
  induction S with
  | nil => simp at ha
  | cons x rest ih =>
    rcases List.mem_cons.mp ha with ha1 | ha1
    · rcases List.mem_cons.mp hb with hb1 | hb1
      · right; rw [ha1, hb1]; simp
      · left
        rw [ha1]
        exact List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨b, hb1, by simp⟩))
    · rcases List.mem_cons.mp hb with hb1 | hb1
      · left
        rw [hb1, Nat.and_comm]
        exact List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨a, ha1, by simp⟩))
      · rcases ih ha1 hb1 with h | h
        · left; exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
        · right; exact List.mem_cons_of_mem _ h

theorem or_mem_pairs {a b : ℕ} {S : List ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    a ||| b ∈ pairs S ∨ a ||| b ∈ S := by
  induction S with
  | nil => simp at ha
  | cons x rest ih =>
    rcases List.mem_cons.mp ha with ha1 | ha1
    · rcases List.mem_cons.mp hb with hb1 | hb1
      · right; rw [ha1, hb1]; simp
      · left
        rw [ha1]
        exact List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨b, hb1, by simp⟩))
    · rcases List.mem_cons.mp hb with hb1 | hb1
      · left
        rw [hb1, Nat.or_comm]
        exact List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨a, ha1, by simp⟩))
      · rcases ih ha1 hb1 with h | h
        · left; exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
        · right; exact List.mem_cons_of_mem _ h

theorem m255 : ∀ n : Fin 256, n.val &&& 255 = n.val := by
  decide +kernel

theorem closure (g : Gate) (hg : Legal g) (w : List W) (S : List ℕ)
    (hw : ∀ v ∈ w, v.toNat ∈ S) (h0 : 0 ∈ S) (h1 : 255 ∈ S) :
    (gop g.op (g.inputs.map fun i => w.getD i 0)).toNat ∈ pairs S ∨
    (gop g.op (g.inputs.map fun i => w.getD i 0)).toNat ∈ S := by
  have hget : ∀ i, (w.getD i 0).toNat ∈ S := by
    intro i
    rcases getD_mem w i with h | h
    · exact hw _ h
    · rw [h]; exact h0
  have e : ∀ v : W, v.toNat &&& 255 = v.toNat := fun v => m255 v.toFin
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · right; simpa [gop] using h1
    · right; simpa [gop] using h0
    · right; simpa [gop] using h1
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · right; simpa [gop, e] using hget i
    · right; simpa [gop] using hget i
    · left
      have := not_mem_pairs (hget i)
      simpa [gop, BitVec.toNat_not] using this
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · have := and_mem_pairs (hget i) (hget j)
      simpa [gop, e, BitVec.toNat_and] using this
    · have := or_mem_pairs (hget i) (hget j)
      simpa [gop, BitVec.toNat_or] using this
    · left
      have := not_mem_pairs (hget i)
      simpa [gop, BitVec.toNat_not] using this
  | _ :: _ :: _ :: _, h => simp at h

theorem search_need0 (k : ℕ) (S : List ℕ) (h : need S = 0) : search k S = true := by
  cases k <;> simp [search, h]

theorem need_le_of_search (k : ℕ) (S : List ℕ) (h : search k S = true) : need S ≤ k := by
  cases k with
  | zero => simp [search] at h; omega
  | succ k =>
    by_contra hc
    simp [search, show ¬(need S = 0) by omega, show k + 1 < need S by omega] at h

theorem reach (gs : List Gate) : ∀ (k : ℕ) (w : List W) (S : List ℕ), gs.length ≤ k →
    (∀ g ∈ gs, Legal g) → (∀ v ∈ w, v.toNat ∈ S) → 0 ∈ S → 255 ∈ S →
    need ((gs.foldl stepW w).map BitVec.toNat) = 0 → search k S = true := by
  induction gs with
  | nil =>
    intro k w S _ _ hw _ _ hn
    simp only [List.foldl_nil] at hn
    have h := need_anti (T := w.map BitVec.toNat) (S := S) (by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      exact hw u hu)
    exact search_need0 k S (by omega)
  | cons g gs ih =>
    intro k w S hk hl hw h0 h1 hn
    cases k with
    | zero => simp at hk
    | succ k =>
      have hg := hl g (by simp)
      have hl' : ∀ g' ∈ gs, Legal g' := fun g' h => hl g' (by simp [h])
      simp only [List.foldl_cons] at hn
      have hlen : gs.length ≤ k := by simpa using hk
      by_cases hzS : (gop g.op (g.inputs.map fun i => w.getD i 0)).toNat ∈ S
      · refine ih (k + 1) (stepW w g) S (by omega) hl' ?_ h0 h1 hn
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hw v hv
        · rw [List.mem_singleton.mp hv]; exact hzS
      · have hz : (gop g.op (g.inputs.map fun i => w.getD i 0)).toNat ∈ pairs S :=
          (closure g hg w S hw h0 h1).resolve_right hzS
        have hs := ih k (stepW w g) ((gop g.op (g.inputs.map fun i => w.getD i 0)).toNat :: S)
          hlen hl' (by
            intro v hv
            rcases List.mem_append.mp hv with hv | hv
            · exact List.mem_cons_of_mem _ (hw v hv)
            · rw [List.mem_singleton.mp hv]; exact List.mem_cons_self)
          (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h1) hn
        have hb := need_le_of_search k _ hs
        have hc := need_cons (gop g.op (g.inputs.map fun i => w.getD i 0)).toNat S
        by_cases hn0 : need S = 0
        · exact search_need0 _ S hn0
        · have hk1 : ¬(k + 1 < need S) := by omega
          simp only [search, beq_iff_eq, hn0, ite_false, hk1]
          exact List.any_eq_true.mpr ⟨_, List.mem_filter.mpr ⟨hz, by simpa using hzS⟩, hs⟩

theorem search_succ_false (k : ℕ) (S : List ℕ) (hn : need S ≠ 0)
    (h : (kids S).all (fun z => !search k (z :: S)) = true) : search (k + 1) S = false := by
  simp only [search, beq_iff_eq, hn, ite_false]
  split
  · rfl
  · rw [List.any_eq_false]
    intro z hz
    have := List.all_eq_true.mp h z hz
    simpa using this

theorem all_chunk {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

def S0 : List ℕ := [170, 204, 240, 0, 255]

def lvl1 : List (List ℕ) := (kids S0).map (fun z => z :: S0)

def lvl2 : List (List ℕ) := lvl1.flatMap (fun S => (kids S).map (fun z => z :: S))

theorem tab_maj : ∀ v : Fin 256, (∀ r : Fin 8, bit r (BitVec.ofFin v) =
    ((row r 0 && row r 1) || (row r 1 && row r 2) || (row r 0 && row r 2))) →
    v.val = 232 := by
  decide +kernel

theorem tab_p : ∀ v : Fin 256, (∀ r : Fin 8,
    ((row r 0 && row r 1) || (row r 1 && row r 2) || (row r 0 && row r 2)) = true →
    bit r (BitVec.ofFin v) = xor (row r 0) (row r 1)) → v.val &&& 232 = 96 := by
  decide +kernel

theorem tab_q : ∀ v : Fin 256, (∀ r : Fin 8,
    ((row r 0 && row r 1) || (row r 1 && row r 2) || (row r 0 && row r 2)) = true →
    bit r (BitVec.ofFin v) = xor (row r 1) (row r 2)) → v.val &&& 232 = 40 := by
  decide +kernel

theorem take1_all (p : List ℕ → Bool) (l : List (List ℕ)) (i : ℕ) (h : p (l.getD i []) = true) :
    ((l.drop i).take 1).all p = true := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simpa using h
    | succ j => simpa using ih j (by simpa using h)

theorem heavy (i : ℕ) (hn : (need (lvl2.getD i []) != 0) = true)
    (hk : (kids (lvl2.getD i [])).all (fun z => !search 3 (z :: lvl2.getD i [])) = true) :
    ((lvl2.drop i).take 1).all (fun S => !search 4 S) = true := by
  apply take1_all
  rw [search_succ_false 3 _ (by simpa using hn) hk]
  rfl

theorem c_0 : ((lvl2.drop 0).take 4).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_4 : ((lvl2.drop 4).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_6 : ((lvl2.drop 6).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_8 : ((lvl2.drop 8).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_9 : ((lvl2.drop 9).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_10 : ((lvl2.drop 10).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem hn_12 : (need (lvl2.getD 12 []) != 0) = true := by
  decide +kernel

theorem k_12_0 : (((kids (lvl2.getD 12 [])).drop 0).take 4).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem k_12_4 : (((kids (lvl2.getD 12 [])).drop 4).take 3).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem k_12_7 : (((kids (lvl2.getD 12 [])).drop 7).take 3).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem k_12_10 : (((kids (lvl2.getD 12 [])).drop 10).take 1).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem k_12_11 : (((kids (lvl2.getD 12 [])).drop 11).take 1).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem k_12_12 : (((kids (lvl2.getD 12 [])).drop 12).take 2).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem k_12_14 : ((kids (lvl2.getD 12 [])).drop 14).all (fun z => !search 3 (z :: lvl2.getD 12 [])) = true := by
  decide +kernel

theorem c_12 : ((lvl2.drop 12).take 1).all (fun S => !search 4 S) = true :=
  heavy 12 hn_12 (all_chunk _ (kids (lvl2.getD 12 [])) 0 4 k_12_0 (all_chunk _ (kids (lvl2.getD 12 [])) 4 3 k_12_4 (all_chunk _ (kids (lvl2.getD 12 [])) 7 3 k_12_7 (all_chunk _ (kids (lvl2.getD 12 [])) 10 1 k_12_10 (all_chunk _ (kids (lvl2.getD 12 [])) 11 1 k_12_11 (all_chunk _ (kids (lvl2.getD 12 [])) 12 2 k_12_12 (k_12_14)))))))

theorem c_13 : ((lvl2.drop 13).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_14 : ((lvl2.drop 14).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_15 : ((lvl2.drop 15).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_16 : ((lvl2.drop 16).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_17 : ((lvl2.drop 17).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_18 : ((lvl2.drop 18).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_19 : ((lvl2.drop 19).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem hn_20 : (need (lvl2.getD 20 []) != 0) = true := by
  decide +kernel

theorem k_20_0 : (((kids (lvl2.getD 20 [])).drop 0).take 1).all (fun z => !search 3 (z :: lvl2.getD 20 [])) = true := by
  decide +kernel

theorem k_20_1 : (((kids (lvl2.getD 20 [])).drop 1).take 4).all (fun z => !search 3 (z :: lvl2.getD 20 [])) = true := by
  decide +kernel

theorem k_20_5 : (((kids (lvl2.getD 20 [])).drop 5).take 1).all (fun z => !search 3 (z :: lvl2.getD 20 [])) = true := by
  decide +kernel

theorem k_20_6 : (((kids (lvl2.getD 20 [])).drop 6).take 9).all (fun z => !search 3 (z :: lvl2.getD 20 [])) = true := by
  decide +kernel

theorem k_20_15 : ((kids (lvl2.getD 20 [])).drop 15).all (fun z => !search 3 (z :: lvl2.getD 20 [])) = true := by
  decide +kernel

theorem c_20 : ((lvl2.drop 20).take 1).all (fun S => !search 4 S) = true :=
  heavy 20 hn_20 (all_chunk _ (kids (lvl2.getD 20 [])) 0 1 k_20_0 (all_chunk _ (kids (lvl2.getD 20 [])) 1 4 k_20_1 (all_chunk _ (kids (lvl2.getD 20 [])) 5 1 k_20_5 (all_chunk _ (kids (lvl2.getD 20 [])) 6 9 k_20_6 (k_20_15)))))

theorem c_21 : ((lvl2.drop 21).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_22 : ((lvl2.drop 22).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_23 : ((lvl2.drop 23).take 4).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_27 : ((lvl2.drop 27).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_29 : ((lvl2.drop 29).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_32 : ((lvl2.drop 32).take 5).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_37 : ((lvl2.drop 37).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_39 : ((lvl2.drop 39).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_42 : ((lvl2.drop 42).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_44 : ((lvl2.drop 44).take 5).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_49 : ((lvl2.drop 49).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_52 : ((lvl2.drop 52).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_55 : ((lvl2.drop 55).take 4).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_59 : ((lvl2.drop 59).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_60 : ((lvl2.drop 60).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_61 : ((lvl2.drop 61).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_63 : ((lvl2.drop 63).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_65 : ((lvl2.drop 65).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_67 : ((lvl2.drop 67).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem hn_68 : (need (lvl2.getD 68 []) != 0) = true := by
  decide +kernel

theorem k_68_0 : (((kids (lvl2.getD 68 [])).drop 0).take 4).all (fun z => !search 3 (z :: lvl2.getD 68 [])) = true := by
  decide +kernel

theorem k_68_4 : (((kids (lvl2.getD 68 [])).drop 4).take 3).all (fun z => !search 3 (z :: lvl2.getD 68 [])) = true := by
  decide +kernel

theorem k_68_7 : (((kids (lvl2.getD 68 [])).drop 7).take 1).all (fun z => !search 3 (z :: lvl2.getD 68 [])) = true := by
  decide +kernel

theorem k_68_8 : (((kids (lvl2.getD 68 [])).drop 8).take 3).all (fun z => !search 3 (z :: lvl2.getD 68 [])) = true := by
  decide +kernel

theorem k_68_11 : (((kids (lvl2.getD 68 [])).drop 11).take 3).all (fun z => !search 3 (z :: lvl2.getD 68 [])) = true := by
  decide +kernel

theorem k_68_14 : ((kids (lvl2.getD 68 [])).drop 14).all (fun z => !search 3 (z :: lvl2.getD 68 [])) = true := by
  decide +kernel

theorem c_68 : ((lvl2.drop 68).take 1).all (fun S => !search 4 S) = true :=
  heavy 68 hn_68 (all_chunk _ (kids (lvl2.getD 68 [])) 0 4 k_68_0 (all_chunk _ (kids (lvl2.getD 68 [])) 4 3 k_68_4 (all_chunk _ (kids (lvl2.getD 68 [])) 7 1 k_68_7 (all_chunk _ (kids (lvl2.getD 68 [])) 8 3 k_68_8 (all_chunk _ (kids (lvl2.getD 68 [])) 11 3 k_68_11 (k_68_14))))))

theorem c_69 : ((lvl2.drop 69).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_70 : ((lvl2.drop 70).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_71 : ((lvl2.drop 71).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem hn_72 : (need (lvl2.getD 72 []) != 0) = true := by
  decide +kernel

theorem k_72_0 : (((kids (lvl2.getD 72 [])).drop 0).take 1).all (fun z => !search 3 (z :: lvl2.getD 72 [])) = true := by
  decide +kernel

theorem k_72_1 : (((kids (lvl2.getD 72 [])).drop 1).take 4).all (fun z => !search 3 (z :: lvl2.getD 72 [])) = true := by
  decide +kernel

theorem k_72_5 : (((kids (lvl2.getD 72 [])).drop 5).take 1).all (fun z => !search 3 (z :: lvl2.getD 72 [])) = true := by
  decide +kernel

theorem k_72_6 : (((kids (lvl2.getD 72 [])).drop 6).take 9).all (fun z => !search 3 (z :: lvl2.getD 72 [])) = true := by
  decide +kernel

theorem k_72_15 : ((kids (lvl2.getD 72 [])).drop 15).all (fun z => !search 3 (z :: lvl2.getD 72 [])) = true := by
  decide +kernel

theorem c_72 : ((lvl2.drop 72).take 1).all (fun S => !search 4 S) = true :=
  heavy 72 hn_72 (all_chunk _ (kids (lvl2.getD 72 [])) 0 1 k_72_0 (all_chunk _ (kids (lvl2.getD 72 [])) 1 4 k_72_1 (all_chunk _ (kids (lvl2.getD 72 [])) 5 1 k_72_5 (all_chunk _ (kids (lvl2.getD 72 [])) 6 9 k_72_6 (k_72_15)))))

theorem c_73 : ((lvl2.drop 73).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_74 : ((lvl2.drop 74).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_75 : ((lvl2.drop 75).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_76 : ((lvl2.drop 76).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_77 : ((lvl2.drop 77).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_78 : ((lvl2.drop 78).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_80 : ((lvl2.drop 80).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_83 : ((lvl2.drop 83).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_86 : ((lvl2.drop 86).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_88 : ((lvl2.drop 88).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_90 : ((lvl2.drop 90).take 4).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_94 : ((lvl2.drop 94).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_95 : ((lvl2.drop 95).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_96 : ((lvl2.drop 96).take 3).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_99 : ((lvl2.drop 99).take 1).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_100 : ((lvl2.drop 100).take 2).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem c_102 : (lvl2.drop 102).all (fun S => !search 4 S) = true := by
  decide +kernel

theorem all2 : lvl2.all (fun S => !search 4 S) = true :=
  all_chunk _ lvl2 0 4 c_0 (all_chunk _ lvl2 4 2 c_4 (all_chunk _ lvl2 6 2 c_6 (all_chunk _ lvl2 8 1 c_8 (all_chunk _ lvl2 9 1 c_9 (all_chunk _ lvl2 10 2 c_10 (all_chunk _ lvl2 12 1 c_12 (all_chunk _ lvl2 13 1 c_13 (all_chunk _ lvl2 14 1 c_14 (all_chunk _ lvl2 15 1 c_15 (all_chunk _ lvl2 16 1 c_16 (all_chunk _ lvl2 17 1 c_17 (all_chunk _ lvl2 18 1 c_18 (all_chunk _ lvl2 19 1 c_19 (all_chunk _ lvl2 20 1 c_20 (all_chunk _ lvl2 21 1 c_21 (all_chunk _ lvl2 22 1 c_22 (all_chunk _ lvl2 23 4 c_23 (all_chunk _ lvl2 27 2 c_27 (all_chunk _ lvl2 29 3 c_29 (all_chunk _ lvl2 32 5 c_32 (all_chunk _ lvl2 37 2 c_37 (all_chunk _ lvl2 39 3 c_39 (all_chunk _ lvl2 42 2 c_42 (all_chunk _ lvl2 44 5 c_44 (all_chunk _ lvl2 49 3 c_49 (all_chunk _ lvl2 52 3 c_52 (all_chunk _ lvl2 55 4 c_55 (all_chunk _ lvl2 59 1 c_59 (all_chunk _ lvl2 60 1 c_60 (all_chunk _ lvl2 61 2 c_61 (all_chunk _ lvl2 63 2 c_63 (all_chunk _ lvl2 65 2 c_65 (all_chunk _ lvl2 67 1 c_67 (all_chunk _ lvl2 68 1 c_68 (all_chunk _ lvl2 69 1 c_69 (all_chunk _ lvl2 70 1 c_70 (all_chunk _ lvl2 71 1 c_71 (all_chunk _ lvl2 72 1 c_72 (all_chunk _ lvl2 73 1 c_73 (all_chunk _ lvl2 74 1 c_74 (all_chunk _ lvl2 75 1 c_75 (all_chunk _ lvl2 76 1 c_76 (all_chunk _ lvl2 77 1 c_77 (all_chunk _ lvl2 78 2 c_78 (all_chunk _ lvl2 80 3 c_80 (all_chunk _ lvl2 83 3 c_83 (all_chunk _ lvl2 86 2 c_86 (all_chunk _ lvl2 88 2 c_88 (all_chunk _ lvl2 90 4 c_90 (all_chunk _ lvl2 94 1 c_94 (all_chunk _ lvl2 95 1 c_95 (all_chunk _ lvl2 96 3 c_96 (all_chunk _ lvl2 99 1 c_99 (all_chunk _ lvl2 100 2 c_100 (c_102)))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem n1 : lvl1.all (fun S => need S != 0) = true := by
  decide +kernel

theorem none6 : search 6 S0 = false := by
  apply search_succ_false 5 S0 (by decide)
  rw [List.all_eq_true]
  intro z hz
  have hS : (z :: S0) ∈ lvl1 := List.mem_map.mpr ⟨z, hz, rfl⟩
  have hn := List.all_eq_true.mp n1 _ hS
  have h5 : search 5 (z :: S0) = false := by
    apply search_succ_false 4 _ (by simpa using hn)
    rw [List.all_eq_true]
    intro y hy
    exact List.all_eq_true.mp all2 (y :: z :: S0)
      (List.mem_flatMap.mpr ⟨z :: S0, hS, List.mem_map.mpr ⟨y, hy, rfl⟩⟩)
  simp [h5]

theorem no_circuit (C : Circuit) (p q : ℕ)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 6)
    (h : ∀ x : Fin 3 → Bool,
      C.eval (List.ofFn x ++ [false, true]) = ((x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) ∧
      (((x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) = true →
        (C.wires (List.ofFn x ++ [false, true])).getD p false = xor (x 0) (x 1) ∧
        (C.wires (List.ofFn x ++ [false, true])).getD q false = xor (x 1) (x 2))) : False := by
  have legal : ∀ g ∈ C.gates, Legal g := by
    intro g hg
    have h' := hfan g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h'.1, h'.2⟩
  have hw : ∀ r : Fin 8, C.wires (List.ofFn (row r) ++ [false, true]) =
      (C.gates.foldl stepW W0).map (bit r) := by
    intro r
    rw [init_bit]
    exact fold_bit r C.gates legal W0
  have rd : ∀ (r : Fin 8) (i : ℕ), (C.wires (List.ofFn (row r) ++ [false, true])).getD i false =
      bit r ((C.gates.foldl stepW W0).getD i 0) := by
    intro r i
    rw [hw r]
    exact getD_bit r _ i
  have z0 : (0 : W) ∈ C.gates.foldl stepW W0 := by
    have : ∀ (gs : List Gate) (w : List W), (0 : W) ∈ w → (0 : W) ∈ gs.foldl stepW w := by
      intro gs
      induction gs with
      | nil => intro w hw0; exact hw0
      | cons g gs ih => intro w hw0; exact ih _ (List.mem_append_left _ hw0)
    exact this C.gates W0 (by decide)
  have mem : ∀ i : ℕ, (C.gates.foldl stepW W0).getD i 0 ∈ C.gates.foldl stepW W0 := by
    intro i
    rcases getD_mem (C.gates.foldl stepW W0) i with h1 | h1
    · exact h1
    · rw [h1]; exact z0
  have e1 := tab_maj ((C.gates.foldl stepW W0).getD C.output 0).toFin (by
    intro r
    have := (h (row r)).1
    unfold Circuit.eval at this
    rw [rd r] at this
    exact this)
  have e2 := tab_p ((C.gates.foldl stepW W0).getD p 0).toFin (by
    intro r hr
    have := ((h (row r)).2 hr).1
    rw [rd r] at this
    exact this)
  have e3 := tab_q ((C.gates.foldl stepW W0).getD q 0).toFin (by
    intro r hr
    have := ((h (row r)).2 hr).2
    rw [rd r] at this
    exact this)
  have key : need ((C.gates.foldl stepW W0).map BitVec.toNat) = 0 := by
    have a1 : ((C.gates.foldl stepW W0).map BitVec.toNat).any (fun v => v == 232) = true :=
      List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, mem C.output, rfl⟩, by simpa using e1⟩
    have a2 : ((C.gates.foldl stepW W0).map BitVec.toNat).any (fun v => v &&& 232 == 96) = true :=
      List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, mem p, rfl⟩, by simpa using e2⟩
    have a3 : ((C.gates.foldl stepW W0).map BitVec.toNat).any (fun v => v &&& 232 == 40) = true :=
      List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨_, mem q, rfl⟩, by simpa using e3⟩
    simp only [need, a1, a2, a3, if_true]
  have r6 := reach C.gates 6 W0 S0 hsz legal (by decide) (by decide) (by decide) key
  rw [none6] at r6
  exact absurd r6 (by decide)

end PEqualNP.Outside.L_meta_42689

theorem PEqualNP.Outside.L_meta_42689 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p q : Fin (5 + C.size)),
  PEqualNP.MetaComplexity.FanInTwo C ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack 5 C ∧
  C.output < 5 + C.size ∧ C.size ≤ 6 ∧
  ∀ x : Fin 3 → Bool,
    let w := List.ofFn x ++ [false, true]
    let cover := (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)
    C.eval w = cover ∧
    (cover = true →
      (C.wires w).getD p.val false = xor (x 0) (x 1) ∧
      (C.wires w).getD q.val false = xor (x 1) (x 2)))) := by
  rintro ⟨C, p, q, hfan, -, -, hsz, h⟩
  exact PEqualNP.Outside.L_meta_42689.no_circuit C p.val q.val hfan hsz h
