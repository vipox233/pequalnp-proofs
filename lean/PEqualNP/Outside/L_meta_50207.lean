import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50207

open PEqualNP.CircuitLowerBounds

def gm (g : Gate) (m : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => 63
  | GateOp.and, [i] => m.getD i 0
  | GateOp.and, i :: j :: _ => m.getD i 0 &&& m.getD j 0
  | GateOp.or, [] => 0
  | GateOp.or, [i] => m.getD i 0
  | GateOp.or, i :: j :: _ => m.getD i 0 ||| m.getD j 0
  | GateOp.not, [] => 63
  | GateOp.not, i :: _ => 63 ^^^ m.getD i 0
  | _, _ => 0

def step (m : List ℕ) (g : Gate) : List ℕ := m ++ [gm g m]

def base : List ℕ := [62, 60, 56, 48, 32, 0, 63]

def Fan2 (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem t63 : ∀ t, t < 6 → (63 : ℕ).testBit t = true := by decide

theorem sim_gate (t : ℕ) (ht : t < 6) (w : List Bool) (m : List ℕ)
    (h : ∀ i, w.getD i false = (m.getD i 0).testBit t) (g : Gate) (hg : Fan2 g) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gm g m).testBit t := by
  have h' : ∀ i : ℕ, w[i]?.getD false = (m[i]?.getD 0).testBit t := by
    simpa [List.getD_eq_getElem?_getD] using h
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => simp [GateOp.eval, gm, t63 t ht]
    | [i], _ => simp [GateOp.eval, gm, h']
    | [i, j], _ => simp [GateOp.eval, gm, h']
  · match ins, hlen with
    | [], _ => simp [GateOp.eval, gm]
    | [i], _ => simp [GateOp.eval, gm, h']
    | [i, j], _ => simp [GateOp.eval, gm, h']
  · match ins, hlen with
    | [], _ => simp [GateOp.eval, gm, t63 t ht]
    | i :: _, _ => simp [GateOp.eval, gm, h', Nat.testBit_xor, t63 t ht]

theorem sim (t : ℕ) (ht : t < 6) :
    ∀ (gs : List Gate), (∀ g ∈ gs, Fan2 g) → ∀ (w : List Bool) (m : List ℕ),
      w.length = m.length → (∀ i, w.getD i false = (m.getD i 0).testBit t) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        i false = ((gs.foldl step m).getD i 0).testBit t := by
  intro gs
  induction gs with
  | nil => intro _ w m _ h i; exact h i
  | cons g gs ih =>
    intro hgs w m hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i
      rw [step, getD_snoc, getD_snoc, hl]
      split_ifs with h1 h2
      · exact h i
      · exact sim_gate t ht w m h g (hgs g (List.mem_cons_self))
      · simp

theorem bnd : ∀ x, x < 64 → ∀ y, y < 64 → x &&& y < 64 ∧ x ||| y < 64 ∧ 63 ^^^ x < 64 := by
  decide

theorem gm_lt (g : Gate) (m : List ℕ) (h : ∀ i, m.getD i 0 < 64) : gm g m < 64 := by
  obtain ⟨op, ins⟩ := g
  unfold gm
  split
  all_goals first
    | decide
    | exact h _
    | exact (bnd _ (h _) _ (h _)).1
    | exact (bnd _ (h _) _ (h _)).2.1
    | exact (bnd _ (h _) 0 (by decide)).2.2

theorem lt64 : ∀ (gs : List Gate) (m : List ℕ), (∀ i, m.getD i 0 < 64) →
    ∀ i, (gs.foldl step m).getD i 0 < 64 := by
  intro gs
  induction gs with
  | nil => intro m h; exact h
  | cons g gs ih =>
    intro m h
    apply ih
    intro i
    rw [step, getD_snoc]
    split_ifs
    · exact h i
    · exact gm_lt g m h
    · decide

def miss (a b c : ℕ) (L : List ℕ) : ℕ :=
  (if a ∈ L then 0 else 1) + (if b ∈ L then 0 else 1) + (if c ∈ L then 0 else 1)

def bits (l : List ℕ) : ℕ := l.foldr (fun u acc => acc ||| 2 ^ u) 0

theorem bits_spec (l : List ℕ) (v : ℕ) : (bits l).testBit v = decide (v ∈ l) := by
  induction l with
  | nil => simp [bits]
  | cons u l ih =>
    simp only [bits, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_lor, ih, Nat.testBit_two_pow]
    by_cases h : v = u
    · subst h; simp
    · simp [h, Ne.symm h]

def mono (L : List ℕ) : ℕ := bits (L.flatMap fun x => L.flatMap fun y => [x &&& y, x ||| y])

theorem mono_and {L : List ℕ} {x y : ℕ} (hx : x ∈ L) (hy : y ∈ L) :
    (mono L).testBit (x &&& y) = true := by
  rw [mono, bits_spec]
  simp only [List.mem_flatMap, decide_eq_true_eq]
  exact ⟨x, hx, y, hy, by simp⟩

theorem mono_or {L : List ℕ} {x y : ℕ} (hx : x ∈ L) (hy : y ∈ L) :
    (mono L).testBit (x ||| y) = true := by
  rw [mono, bits_spec]
  simp only [List.mem_flatMap, decide_eq_true_eq]
  exact ⟨x, hx, y, hy, by simp⟩

def ok (a b c : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, L => miss a b c L == 0
  | s + 1, n, L => miss a b c L == 0 || (decide (miss a b c L ≤ s + 1) &&
      (List.range 64).any fun v => !(L.contains v) &&
        (if (mono L).testBit v then ok a b c s n (v :: L)
         else (decide (0 < n) && L.contains (63 ^^^ v) && ok a b c s (n - 1) (v :: L))))

theorem ok_miss (a b c : ℕ) : ∀ s n L, ok a b c s n L = true → miss a b c L ≤ s := by
  intro s n L h
  cases s with
  | zero => simp [ok] at h; omega
  | succ s =>
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    omega

theorem miss_cons (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (v : ℕ) (L : List ℕ) :
    miss a b c L ≤ miss a b c (v :: L) + 1 := by
  unfold miss
  simp only [List.mem_cons]
  by_cases ha : a = v <;> by_cases hb : b = v <;> by_cases hc : c = v <;>
    simp_all <;> split_ifs <;> omega

def isNot : GateOp → ℕ
  | GateOp.not => 1
  | _ => 0

theorem notCount_cons (g : Gate) (gs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨g :: gs, o⟩ =
      isNot g.op + PEqualNP.NotBracket.notCount ⟨gs, o⟩ := by
  simp only [PEqualNP.NotBracket.notCount, List.filter_cons]
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [isNot]; omega

theorem xx : ∀ x, x < 64 → 63 ^^^ (63 ^^^ x) = x := by decide

theorem gm_cases (g : Gate) (m L : List ℕ) (hg : Fan2 g) (hm : ∀ i, m.getD i 0 ∈ L)
    (h0 : 0 ∈ L) (h63 : 63 ∈ L) :
    gm g m ∈ L ∨ (mono L).testBit (gm g m) = true ∨
      (g.op = GateOp.not ∧ ∃ x ∈ L, gm g m = 63 ^^^ x) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => exact Or.inl h63
    | [i], _ => exact Or.inl (hm i)
    | [i, j], _ => exact Or.inr (Or.inl (mono_and (hm i) (hm j)))
  · match ins, hlen with
    | [], _ => exact Or.inl h0
    | [i], _ => exact Or.inl (hm i)
    | [i, j], _ => exact Or.inr (Or.inl (mono_or (hm i) (hm j)))
  · match ins, hlen with
    | [], _ => exact Or.inl h63
    | i :: _, _ => exact Or.inr (Or.inr ⟨rfl, m.getD i 0, hm i, rfl⟩)

theorem sound (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (gs : List Gate) (m L : List ℕ) (n : ℕ), (∀ g ∈ gs, Fan2 g) →
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n →
      (∀ i, m.getD i 0 ∈ L) → 0 ∈ L → 63 ∈ L → (∀ x ∈ L, x < 64) →
      (∃ i, (gs.foldl step m).getD i 0 = a) → (∃ i, (gs.foldl step m).getD i 0 = b) →
      (∃ i, (gs.foldl step m).getD i 0 = c) →
      ∃ s ≤ gs.length, ok a b c s n L = true := by
  intro gs
  induction gs with
  | nil =>
    intro m L n _ _ hm _ _ _ ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩
    refine ⟨0, le_refl _, ?_⟩
    have ha := hm i; have hb := hm j; have hc := hm k
    simp only [List.foldl_nil] at hi hj hk
    rw [hi] at ha; rw [hj] at hb; rw [hk] at hc
    simp [ok, miss, ha, hb, hc]
  | cons g gs ih =>
    intro m L n hgs hn hm h0 h63 hL ha hb hc
    simp only [List.foldl_cons] at ha hb hc
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, Fan2 g' := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    rw [notCount_cons] at hn
    have hmlt : ∀ i, m.getD i 0 < 64 := fun i => hL _ (hm i)
    have hvlt : gm g m < 64 := gm_lt g m hmlt
    by_cases hv : gm g m ∈ L
    ·
      obtain ⟨s, hs, hok⟩ := ih (step m g) L n hgs' (by omega)
        (by intro i; rw [step, getD_snoc]; split_ifs <;> first | exact hm i | exact hv | exact h0)
        h0 h63 hL ha hb hc
      exact ⟨s, by simp; omega, hok⟩
    · have hm' : ∀ i, (step m g).getD i 0 ∈ gm g m :: L := by
        intro i; rw [step, getD_snoc]
        split_ifs
        · exact List.mem_cons_of_mem _ (hm i)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h0
      have hL' : ∀ x ∈ gm g m :: L, x < 64 := by
        intro x hx; rcases List.mem_cons.1 hx with rfl | hx
        · exact hvlt
        · exact hL x hx
      have hvr : gm g m ∈ List.range 64 := List.mem_range.2 hvlt
      have hvc : L.contains (gm g m) = false := by simpa using hv
      by_cases hmono : (mono L).testBit (gm g m) = true
      · obtain ⟨s, hs, hok⟩ := ih (step m g) (gm g m :: L) n hgs' (by omega) hm'
          (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h63) hL' ha hb hc
        refine ⟨s + 1, by simp; omega, ?_⟩
        have h1 := ok_miss a b c s n _ hok
        have h2 := miss_cons a b c hab hac hbc (gm g m) L
        simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
        right
        refine ⟨by omega, gm g m, hvr, ?_⟩
        simp [hv, hmono, hok]
      ·
        rcases gm_cases g m L hg hm h0 h63 with h | h | ⟨hop, x, hx, hvx⟩
        · exact absurd h hv
        · exact absurd h hmono
        rw [hop] at hn; simp only [isNot] at hn
        obtain ⟨s, hs, hok⟩ := ih (step m g) (gm g m :: L) (n - 1) hgs' (by omega) hm'
          (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h63) hL' ha hb hc
        refine ⟨s + 1, by simp; omega, ?_⟩
        have h1 := ok_miss a b c s _ _ hok
        have h2 := miss_cons a b c hab hac hbc (gm g m) L
        have hx' : L.contains (63 ^^^ gm g m) = true := by
          rw [hvx, xx x (hL x hx)]; simpa using hx
        simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
        right
        refine ⟨by omega, gm g m, hvr, ?_⟩
        simp only [hvc, hmono, hx', hok, Bool.not_false, Bool.and_true]
        simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq, true_and]
        omega

theorem base_ok : ∀ t : Fin 6, ∀ i : Fin 7,
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]).getD i.val false =
      (base.getD i.val 0).testBit t.val := by
  decide

theorem base_sim (t : Fin 6) (i : ℕ) :
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]).getD i false =
      (base.getD i 0).testBit t.val := by
  by_cases hi : i < 7
  · exact base_ok t ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [base]; omega)]
    simp

theorem eq5 : ∀ x, x < 64 → ∀ y, y < 64 → (∀ t : Fin 6, x.testBit t.val = y.testBit t.val) →
    x = y := by
  decide

theorem base_lt (i : ℕ) : base.getD i 0 < 64 := by
  by_cases hi : i < 7
  · have : ∀ j : Fin 7, base.getD j.val 0 < 64 := by decide
    exact this ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp [base]; omega)]; decide

theorem base_mem (i : ℕ) : base.getD i 0 ∈ base := by
  by_cases hi : i < 7
  · have : ∀ j : Fin 7, base.getD j.val 0 ∈ base := by decide
    exact this ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp [base]; omega)]; decide

end PEqualNP.Outside.L_meta_50207

theorem PEqualNP.Outside.L_meta_50207 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (16 : Nat).testBit t.val ∧
    w.getD q.val false = (20 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, hw⟩
  have hF : ∀ g ∈ D.gates, L_meta_50207.Fan2 g := fun g hg =>
    ⟨by simpa using (hfan g hg).1, (hfan g hg).2⟩
  have key : ∀ t : Fin 6, ∀ i, (D.wires
      (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true])).getD i false =
      ((D.gates.foldl L_meta_50207.step L_meta_50207.base).getD i 0).testBit t.val := fun t i =>
    L_meta_50207.sim t.val t.isLt D.gates hF _ _ (by simp [L_meta_50207.base])
      (L_meta_50207.base_sim t) i
  have hlt := L_meta_50207.lt64 D.gates L_meta_50207.base L_meta_50207.base_lt
  have hv : ∀ (o : ℕ) (x : ℕ), x < 64 →
      (∀ t : Fin 6, (D.wires (List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++
        [false, true])).getD o false = x.testBit t.val) →
      ∃ i, (D.gates.foldl L_meta_50207.step L_meta_50207.base).getD i 0 = x :=
    fun o x hx h => ⟨o, L_meta_50207.eq5 _ (hlt o) x hx (fun t => (key t o).symm.trans (h t))⟩
  obtain ⟨s, hs, hok⟩ := L_meta_50207.sound 16 20 54 (by decide) (by decide) (by decide) D.gates
    L_meta_50207.base L_meta_50207.base 2 hF hnot L_meta_50207.base_mem (by decide) (by decide)
    (by decide) (hv p.val 16 (by decide) (fun t => (hw t).1))
    (hv q.val 20 (by decide) (fun t => (hw t).2.1)) (hv r.val 54 (by decide) (fun t => (hw t).2.2))
  have hfalse : ∀ s, s ≤ 6 → L_meta_50207.ok 16 20 54 s 2 L_meta_50207.base = false := by
    decide +kernel
  rw [hfalse s (le_trans hs hsize)] at hok
  exact absurd hok (by decide)
