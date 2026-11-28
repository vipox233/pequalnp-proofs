import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50358

open PEqualNP.CircuitLowerBounds

def ind (t : ℕ) (S : List ℕ) : ℕ := if S.contains t then 0 else 1

def miss (a b c : ℕ) (S : List ℕ) : ℕ := ind a S + (ind b S + ind c S)

def cands (S : List ℕ) : List ℕ :=
  ((S.flatMap fun x => S.flatMap fun y => [x &&& y, x ||| y]).filter fun m => !S.contains m).dedup

def ncands (S : List ℕ) : List ℕ :=
  ((S.map fun x => 63 ^^^ x).filter fun m => !S.contains m).dedup

def search (a b c : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, S => miss a b c S == 0
  | k + 1, n, S =>
    miss a b c S == 0 ||
    (decide (miss a b c S ≤ k + 1) &&
      (search a b c k n S || ((cands S).any (fun m => search a b c k n (m :: S)) ||
        (decide (0 < n) && (ncands S).any (fun m => search a b c k (n - 1) (m :: S))))))

def StepOk (S : List ℕ) (b : Bool) (m : ℕ) : Prop :=
  m ∈ S ∨ (b = false ∧ ∃ x ∈ S, ∃ y ∈ S, m = x &&& y ∨ m = x ||| y) ∨ (b = true ∧ ∃ x ∈ S, m = 63 ^^^ x)

inductive Chain : List ℕ → List (Bool × ℕ) → List ℕ → Prop
  | nil (S : List ℕ) : Chain S [] S
  | cons {S S' : List ℕ} {st : List (Bool × ℕ)} {b : Bool} {m : ℕ} :
      StepOk S b m → Chain (m :: S) st S' → Chain S ((b, m) :: st) S'

theorem ind_le_one (t : ℕ) (S : List ℕ) : ind t S ≤ 1 := by
  unfold ind; split_ifs <;> omega

theorem ind_zero_iff (t : ℕ) (S : List ℕ) : ind t S = 0 ↔ t ∈ S := by
  unfold ind
  by_cases h : t ∈ S
  · simp [h]
  · simp [h]

theorem ind_mono (t : ℕ) {L S : List ℕ} (h : ∀ x ∈ L, x ∈ S) : ind t S ≤ ind t L := by
  by_cases ht : t ∈ L
  · have := (ind_zero_iff t S).2 (h t ht); omega
  · have h1 : ind t L = 1 := by
      have := ind_le_one t L
      have h0 : ind t L ≠ 0 := fun e => ht ((ind_zero_iff t L).1 e)
      omega
    have := ind_le_one t S; omega

theorem ind_cons_ne {t m : ℕ} (h : t ≠ m) (S : List ℕ) : ind t (m :: S) = ind t S := by
  by_cases ht : t ∈ S
  · rw [(ind_zero_iff t S).2 ht, (ind_zero_iff t (m :: S)).2 (List.mem_cons_of_mem _ ht)]
  · have h1 : ind t S ≠ 0 := fun e => ht ((ind_zero_iff t S).1 e)
    have h2 : ind t (m :: S) ≠ 0 := fun e => by
      rcases List.mem_cons.1 ((ind_zero_iff t (m :: S)).1 e) with e | e
      · exact h e
      · exact ht e
    have := ind_le_one t S; have := ind_le_one t (m :: S); omega

theorem miss_cons_ge {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (m : ℕ) (S : List ℕ) :
    miss a b c S ≤ miss a b c (m :: S) + 1 := by
  unfold miss
  have ha := ind_le_one a S; have hb := ind_le_one b S; have hc := ind_le_one c S
  by_cases ea : a = m
  · have e1 := ind_cons_ne (t := b) (m := m) (fun e => hab (ea.trans e.symm)) S
    have e2 := ind_cons_ne (t := c) (m := m) (fun e => hac (ea.trans e.symm)) S
    omega
  · have e0 := ind_cons_ne ea S
    by_cases eb : b = m
    · have e2 := ind_cons_ne (t := c) (m := m) (fun e => hbc (eb.trans e.symm)) S
      omega
    · have e1 := ind_cons_ne eb S
      omega

theorem miss_mono (a b c : ℕ) {L S : List ℕ} (h : ∀ x ∈ L, x ∈ S) : miss a b c S ≤ miss a b c L := by
  unfold miss
  have := ind_mono a h; have := ind_mono b h; have := ind_mono c h; omega

theorem chain_miss {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ {S : List ℕ} {st : List (Bool × ℕ)} {S' : List ℕ}, Chain S st S' →
      miss a b c S ≤ miss a b c S' + st.length := by
  intro S st S' h
  induction h with
  | nil S => simp
  | @cons S S' st bb m hs _ ih =>
    have := miss_cons_ge hab hac hbc m S
    simp only [List.length_cons]; omega

theorem mem_cands {S : List ℕ} {x y m : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hm : m = x &&& y ∨ m = x ||| y)
    (hn : m ∉ S) : m ∈ cands S := by
  unfold cands
  rw [List.mem_dedup, List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨y, hy, ?_⟩⟩, by simpa using hn⟩
  rcases hm with rfl | rfl <;> simp

theorem mem_ncands {S : List ℕ} {x m : ℕ} (hx : x ∈ S) (hm : m = 63 ^^^ x) (hn : m ∉ S) : m ∈ ncands S := by
  unfold ncands
  rw [List.mem_dedup, List.mem_filter]
  exact ⟨List.mem_map.2 ⟨x, hx, hm.symm⟩, by simpa using hn⟩

theorem sound {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (k n : ℕ) (S T : List ℕ) (st : List (Bool × ℕ)) (S' : List ℕ), Chain S st S' →
      (∀ x ∈ S, x ∈ T) → st.length ≤ k → (st.filter fun s => s.1).length ≤ n →
      search a b c k n T = false → 0 < miss a b c S' := by
  intro k
  induction k with
  | zero =>
    intro n S T st S' hch hsub hlen _ hs
    have hst : st = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    subst hst
    cases hch
    have h1 : miss a b c T ≠ 0 := by simpa [search] using hs
    have := miss_mono a b c hsub
    omega
  | succ k ih =>
    intro n S T st S' hch hsub hlen hnot hs
    have hcm := chain_miss hab hac hbc hch
    have hST := miss_mono a b c hsub
    simp only [search, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      decide_eq_false_iff_not, not_le, not_lt] at hs
    obtain ⟨h0, hrest⟩ := hs
    rcases hrest with hbig | ⟨hskip, hany, hnotb⟩
    · omega
    · cases hch with
      | nil => omega
      | cons hstep hch' =>
        rename_i st' bb m
        simp only [List.length_cons] at hlen
        have hlen' : st'.length ≤ k := by omega
        by_cases hmT : m ∈ T
        · refine ih n (m :: S) T st' S' hch' ?_ hlen' ?_ hskip
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hmT
            · exact hsub x hx
          · refine le_trans ?_ hnot
            cases bb <;> simp
        · have hsub' : ∀ x ∈ m :: S, x ∈ m :: T := by
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hsub x hx)
          rcases hstep with hmS | ⟨hb, x, hx, y, hy, hm⟩ | ⟨hb, x, hx, hm⟩
          · exact absurd (hsub m hmS) hmT
          · have hc := mem_cands (hsub x hx) (hsub y hy) hm hmT
            have hsr : search a b c k n (m :: T) = false := by
              have := List.any_eq_false.1 hany m hc
              simpa using this
            refine ih n (m :: S) (m :: T) st' S' hch' hsub' hlen' ?_ hsr
            refine le_trans ?_ hnot
            cases bb <;> simp
          · subst hb
            simp only [List.filter_cons, ite_true, List.length_cons] at hnot
            have hc := mem_ncands (hsub x hx) hm hmT
            rcases hnotb with hn0 | hany2
            · omega
            · have hsr : search a b c k (n - 1) (m :: T) = false := by
                have := List.any_eq_false.1 hany2 m hc
                simpa using this
              exact ih (n - 1) (m :: S) (m :: T) st' S' hch' hsub' hlen' (by omega) hsr

def tb (t : ℕ) (m : ℕ) : Bool := m.testBit t

theorem tbfull (t : Fin 6) : (63 : ℕ).testBit t.val = true := by
  fin_cases t <;> decide

theorem getD_tb (L : List ℕ) (t i : ℕ) : (L.map (tb t)).getD i false = tb t (L.getD i 0) := by
  by_cases h : i < L.length
  · simp [List.getD, h]
  · simp [List.getD, h, tb]

theorem getD_mem {L : List ℕ} (h0 : 0 ∈ L) (i : ℕ) : L.getD i 0 ∈ L := by
  by_cases h : i < L.length
  · simp [List.getD, h]
  · simpa [List.getD, h] using h0

theorem gate_step (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (L : List ℕ) (hL : ∀ m ∈ L, m < 64) (h0 : 0 ∈ L) (hfull : 63 ∈ L) :
    ∃ m, m < 64 ∧ (g.op = GateOp.not → StepOk L true m) ∧ (g.op ≠ GateOp.not → StepOk L false m) ∧
      ∀ t : Fin 6, g.op.eval (g.inputs.map fun i => (L.map (tb t.val)).getD i false) = tb t.val m := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  have hv : ∀ i, L.getD i 0 ∈ L := getD_mem h0
  have hlt : ∀ i, L.getD i 0 < 64 := fun i => hL _ (hv i)
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨63, by norm_num, fun _ => Or.inl hfull, fun _ => Or.inl hfull, fun t => by simp [GateOp.eval, tb, tbfull t]⟩
    · exact ⟨0, by norm_num, fun _ => Or.inl h0, fun _ => Or.inl h0, fun t => by simp [GateOp.eval, tb]⟩
    · exact ⟨63, by norm_num, fun _ => Or.inl hfull, fun _ => Or.inl hfull, fun t => by simp [GateOp.eval, tb, tbfull t]⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨L.getD i 0, hlt i, fun _ => Or.inl (hv i), fun _ => Or.inl (hv i), fun t => by simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval]⟩
    · exact ⟨L.getD i 0, hlt i, fun _ => Or.inl (hv i), fun _ => Or.inl (hv i), fun t => by simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval]⟩
    · refine ⟨63 ^^^ L.getD i 0, Nat.xor_lt_two_pow (n := 6) (by norm_num) (hlt i),
        fun _ => Or.inr (Or.inr ⟨rfl, L.getD i 0, hv i, rfl⟩), fun hne => absurd rfl hne, fun t => ?_⟩
      simp only [List.map_cons, List.map_nil, getD_tb]
      simp [GateOp.eval, tb, Nat.testBit_xor, tbfull t]
  · rcases hop with rfl | rfl | rfl
    · refine ⟨L.getD i 0 &&& L.getD j 0, lt_of_le_of_lt Nat.and_le_left (hlt i),
        (fun he => nomatch he), fun _ => Or.inr (Or.inl ⟨rfl, L.getD i 0, hv i, L.getD j 0, hv j, Or.inl rfl⟩), fun t => ?_⟩
      simp only [List.map_cons, List.map_nil, getD_tb]
      simp [GateOp.eval, tb, Nat.testBit_and]
    · refine ⟨L.getD i 0 ||| L.getD j 0, Nat.or_lt_two_pow (n := 6) (hlt i) (hlt j),
        (fun he => nomatch he), fun _ => Or.inr (Or.inl ⟨rfl, L.getD i 0, hv i, L.getD j 0, hv j, Or.inr rfl⟩), fun t => ?_⟩
      simp only [List.map_cons, List.map_nil, getD_tb]
      simp [GateOp.eval, tb, Nat.testBit_or]
    · refine ⟨63 ^^^ L.getD i 0, Nat.xor_lt_two_pow (n := 6) (by norm_num) (hlt i),
        fun _ => Or.inr (Or.inr ⟨rfl, L.getD i 0, hv i, rfl⟩), fun hne => absurd rfl hne, fun t => ?_⟩
      simp only [List.map_cons, List.map_nil, getD_tb]
      simp [GateOp.eval, tb, Nat.testBit_xor, tbfull t]
  · simp at hlen

theorem stepOk_mono {L S : List ℕ} (h : ∀ x ∈ L, x ∈ S) {b : Bool} {m : ℕ} (hs : StepOk L b m) : StepOk S b m := by
  rcases hs with hm | ⟨hb, x, hx, y, hy, hm⟩ | ⟨hb, x, hx, hm⟩
  · exact Or.inl (h m hm)
  · exact Or.inr (Or.inl ⟨hb, x, h x hx, y, h y hy, hm⟩)
  · exact Or.inr (Or.inr ⟨hb, x, h x hx, hm⟩)

theorem run : ∀ (gs : List Gate) (L S : List ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ m ∈ L, m < 64) → 0 ∈ L → 63 ∈ L → (∀ x ∈ L, x ∈ S) →
    ∃ (st : List (Bool × ℕ)) (S' L' : List ℕ), Chain S st S' ∧ st.length = gs.length ∧
      (st.filter fun s => s.1).length = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ∧
      (∀ x ∈ L', x ∈ S') ∧ (∀ m ∈ L', m < 64) ∧ 0 ∈ L' ∧
      ∀ t : Fin 6, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (L.map (tb t.val)) = L'.map (tb t.val) := by
  intro gs
  induction gs with
  | nil =>
    intro L S _ hL h0 _ hsub
    exact ⟨[], S, L, Chain.nil S, rfl, by simp [PEqualNP.NotBracket.notCount], hsub, hL, h0, fun t => rfl⟩
  | cons g gs ih =>
    intro L S hg hL h0 hfull hsub
    obtain ⟨hgo, hgl⟩ := hg g List.mem_cons_self
    obtain ⟨m, hm, hstepT, hstepF, hval⟩ := gate_step g hgo hgl L hL h0 hfull
    have hL1 : ∀ x ∈ L ++ [m], x < 64 := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hL x hx
      · simp at hx; omega
    have hsub1 : ∀ x ∈ L ++ [m], x ∈ m :: S := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_cons_of_mem _ (hsub x hx)
      · simp at hx; simp [hx]
    obtain ⟨st, S', L', hch, hlen, hnot, hsub', hL', h0', hrun⟩ :=
      ih (L ++ [m]) (m :: S) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) hL1
        (List.mem_append_left _ h0) (List.mem_append_left _ hfull) hsub1
    have hfold : ∀ t : Fin 6, (g :: gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (L.map (tb t.val)) = L'.map (tb t.val) := by
      intro t
      rw [List.foldl_cons, hval t]
      have : L.map (tb t.val) ++ [tb t.val m] = (L ++ [m]).map (tb t.val) := by simp
      rw [this]
      exact hrun t
    by_cases hn : g.op = GateOp.not
    · refine ⟨(true, m) :: st, S', L', Chain.cons (stepOk_mono hsub (hstepT hn)) hch,
        by simp [hlen], ?_, hsub', hL', h0', hfold⟩
      simp only [PEqualNP.NotBracket.notCount] at hnot ⊢
      simp [hn, hnot]
    · refine ⟨(false, m) :: st, S', L', Chain.cons (stepOk_mono hsub (hstepF hn)) hch,
        by simp [hlen], ?_, hsub', hL', h0', hfold⟩
      simp only [PEqualNP.NotBracket.notCount] at hnot ⊢
      simp [hn, hnot]

theorem tb_inj : ∀ x y : Fin 64, (∀ t : Fin 6, tb t.val x.val = tb t.val y.val) → x = y := by
  unfold tb
  decide +kernel

theorem core {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a < 64) (hb : b < 64) (hc : c < 64)
    (k : ℕ) (hs : search a b c k 2 [62, 60, 56, 48, 32, 0, 63] = false)
    (D : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo D) (hn : PEqualNP.NotBracket.notCount D ≤ 2)
    (hk : D.size ≤ k) (p q r : ℕ)
    (h : ∀ t : Fin 6,
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD p false = a.testBit t.val ∧
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD q false = b.testBit t.val ∧
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD r false = c.testBit t.val) :
    False := by
  have hbase : ∀ t : Fin 6, (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]
      = ([62, 60, 56, 48, 32, 0, 63] : List ℕ).map (tb t.val) := by
    intro t; fin_cases t <;> decide
  have hfan : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hf g hg
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨st, S', L', hch, hlen, hnot, hsub', hL', h0', hrun⟩ :=
    run D.gates [62, 60, 56, 48, 32, 0, 63] [62, 60, 56, 48, 32, 0, 63] hfan (by decide) (by decide) (by decide)
      (fun x hx => hx)
  have hmiss := sound hab hac hbc k 2 _ _ st S' hch (fun x hx => hx)
    (by rw [hlen]; exact hk) (by rw [hnot]; exact hn) hs
  have hw : ∀ t : Fin 6, D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])
      = L'.map (tb t.val) := by
    intro t
    unfold Circuit.wires
    rw [hbase t]
    exact hrun t
  have key : ∀ (x i : ℕ), x < 64 → (∀ t : Fin 6, (L'.map (tb t.val)).getD i false = x.testBit t.val) → x ∈ S' := by
    intro x i hx hxi
    have hlt : L'.getD i 0 < 64 := hL' _ (getD_mem h0' i)
    have := tb_inj ⟨L'.getD i 0, hlt⟩ ⟨x, hx⟩ (fun t => by
      have := hxi t
      rw [getD_tb] at this
      exact this)
    have e : L'.getD i 0 = x := congrArg Fin.val this
    rw [← e]
    exact hsub' _ (getD_mem h0' i)
  have hA := key a p ha (fun t => by rw [← hw t]; exact (h t).1)
  have hB := key b q hb (fun t => by rw [← hw t]; exact (h t).2.1)
  have hC := key c r hc (fun t => by rw [← hw t]; exact (h t).2.2)
  have : miss a b c S' = 0 := by
    unfold miss
    rw [(ind_zero_iff a S').2 hA, (ind_zero_iff b S').2 hB, (ind_zero_iff c S').2 hC]
  omega

theorem reject : search 10 12 46 6 2 [62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_50358

theorem PEqualNP.Outside.L_meta_50358 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hf, -, hn, hk, h⟩
  exact PEqualNP.Outside.L_meta_50358.core (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 6
    PEqualNP.Outside.L_meta_50358.reject D hf hn hk p.val q.val r.val h
