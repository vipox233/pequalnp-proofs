import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51302

open PEqualNP.CircuitLowerBounds

def Reach (full : ℕ) (tg : List ℕ) : ℕ → ℕ → List ℕ → Prop
  | 0, _, ws => ∀ m ∈ tg, m ∈ ws
  | s + 1, k, ws => Reach full tg s k ws ∨
      (∃ a ∈ ws, ∃ b ∈ ws,
        Reach full tg s k ((a &&& b) :: ws) ∨ Reach full tg s k ((a ||| b) :: ws)) ∨
      (∃ a ∈ ws, ∃ k', k = k' + 1 ∧ Reach full tg s k' ((full ^^^ a) :: ws))

theorem reach_base {full : ℕ} {tg ws : List ℕ} (h : ∀ m ∈ tg, m ∈ ws) :
    ∀ s k, Reach full tg s k ws
  | 0, _ => h
  | s + 1, k => Or.inl (reach_base h s k)

theorem reach_mono {full : ℕ} {tg : List ℕ} : ∀ (s k k' : ℕ) (ws ws' : List ℕ),
    (∀ x ∈ ws, x ∈ ws') → k ≤ k' → Reach full tg s k ws → Reach full tg s k' ws' := by
  intro s
  induction s with
  | zero => intro k k' ws ws' hsub _ h m hm; exact hsub m (h m hm)
  | succ s ih =>
    intro k k' ws ws' hsub hk h
    have hc : ∀ v, ∀ x ∈ v :: ws, x ∈ v :: ws' := by
      intro v x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (hsub x hx))
    rcases h with h | ⟨a, ha, b, hb, h | h⟩ | ⟨a, ha, k0, rfl, h⟩
    · exact Or.inl (ih k k' ws ws' hsub hk h)
    · exact Or.inr (Or.inl ⟨a, hsub a ha, b, hsub b hb, Or.inl (ih _ _ _ _ (hc _) hk h)⟩)
    · exact Or.inr (Or.inl ⟨a, hsub a ha, b, hsub b hb, Or.inr (ih _ _ _ _ (hc _) hk h)⟩)
    · obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 1 := ⟨k' - 1, by omega⟩
      exact Or.inr (Or.inr ⟨a, hsub a ha, k1, rfl, ih _ _ _ _ (hc _) (by omega) h⟩)

def mem (v : ℕ) (ws : List ℕ) : Bool := ws.any (fun w => Nat.beq v w)

theorem mem_iff {v : ℕ} {ws : List ℕ} : mem v ws = true ↔ v ∈ ws := by
  induction ws with
  | nil => simp [mem]
  | cons w ws ih =>
    have : mem v (w :: ws) = (Nat.beq v w || mem v ws) := rfl
    rw [this, Bool.or_eq_true, ih, List.mem_cons]
    exact ⟨fun h => h.elim (fun h => Or.inl (Nat.eq_of_beq_eq_true h)) Or.inr,
      fun h => h.elim (fun h => Or.inl (h ▸ Nat.beq_refl v)) Or.inr⟩

theorem mem_false {v : ℕ} {ws : List ℕ} (h : v ∉ ws) : mem v ws = false := by
  rw [← Bool.not_eq_true, mem_iff]; exact h

def miss (tg ws : List ℕ) : List ℕ := tg.filter (fun m => !mem m ws)

theorem miss_cons {tg : List ℕ} (hnd : tg.Nodup) (v : ℕ) (ws : List ℕ) :
    (miss tg ws).length ≤ (miss tg (v :: ws)).length + 1 := by
  have h1 : (miss tg ws).Nodup := hnd.filter _
  have h2 : miss tg ws ⊆ v :: miss tg (v :: ws) := by
    intro x hx
    have hx' := List.mem_filter.mp hx
    by_cases hxv : x = v
    · exact List.mem_cons.mpr (Or.inl hxv)
    · refine List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨hx'.1, ?_⟩))
      have hxw : x ∉ ws := by
        intro hin
        have := mem_iff.mpr hin
        simp [this] at hx'
      have : x ∉ v :: ws := by
        intro hin
        rcases List.mem_cons.mp hin with h | h
        · exact hxv h
        · exact hxw h
      simp [mem_false this]
  exact (List.subperm_of_subset h1 h2).length_le

theorem reach_miss {full : ℕ} {tg : List ℕ} (hnd : tg.Nodup) : ∀ (s k : ℕ) (ws : List ℕ),
    Reach full tg s k ws → (miss tg ws).length ≤ s := by
  intro s
  induction s with
  | zero =>
    intro k ws h
    have : miss tg ws = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro m hm
      simp [mem_iff.mpr (h m hm)]
    simp [this]
  | succ s ih =>
    intro k ws h
    rcases h with h | ⟨a, ha, b, hb, h | h⟩ | ⟨a, ha, k', rfl, h⟩
    · exact Nat.le_succ_of_le (ih _ _ h)
    · exact (miss_cons hnd _ ws).trans (Nat.succ_le_succ (ih _ _ h))
    · exact (miss_cons hnd _ ws).trans (Nat.succ_le_succ (ih _ _ h))
    · exact (miss_cons hnd _ ws).trans (Nat.succ_le_succ (ih _ _ h))

def frc (w : ℕ) (k : ℕ → Bool) : Bool :=
  match w with
  | 0 => k 0
  | m + 1 => k (Nat.succ m)

theorem frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by
  cases w <;> rfl

def Inv (ws : List ℕ) (bs : ℕ) : Prop := ∀ u, Nat.testBit bs u = mem u ws

theorem inv_cons {ws : List ℕ} {bs : ℕ} (h : Inv ws bs) (v : ℕ) :
    Inv (v :: ws) (bs ||| 1 <<< v) := by
  intro u
  have hc : mem u (v :: ws) = (Nat.beq u v || mem u ws) := rfl
  rw [hc, Nat.testBit_or, h u, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_comm]
  congr 1
  by_cases huv : u = v
  · subst huv; simp [Nat.beq_refl]
  · have hb : Nat.beq u v = false := by
      rw [← Bool.not_eq_true]; intro hb; exact huv (Nat.eq_of_beq_eq_true hb)
    rw [hb]
    exact decide_eq_false (fun hvu => huv hvu.symm)

def bits (ws : List ℕ) : ℕ := ws.foldr (fun v acc => acc ||| 1 <<< v) 0

theorem inv_bits : ∀ ws : List ℕ, Inv ws (bits ws)
  | [] => fun u => by simp [bits, mem]
  | v :: ws => inv_cons (inv_bits ws) v

def missB (tg : List ℕ) (bs : ℕ) : List ℕ := tg.filter (fun m => !Nat.testBit bs m)

theorem missB_eq {tg ws : List ℕ} {bs : ℕ} (h : Inv ws bs) : missB tg bs = miss tg ws := by
  unfold missB miss
  congr 1
  funext m
  rw [h m]

def tryV (ws : List ℕ) (bs : ℕ) (r : List ℕ → ℕ → Bool) (v : ℕ) : Bool :=
  frc v (fun v => !Nat.testBit bs v && frc (bs ||| 1 <<< v) (fun b => r (v :: ws) b))

theorem tryV_true {ws : List ℕ} {bs : ℕ} {r : List ℕ → ℕ → Bool} {v : ℕ} (hi : Inv ws bs)
    (hv : v ∉ ws) (h : r (v :: ws) (bs ||| 1 <<< v) = true) : tryV ws bs r v = true := by
  unfold tryV
  rw [frc_eq, frc_eq, hi v, mem_false hv, h]; rfl

def pairsAny (ws : List ℕ) (bs : ℕ) (r : List ℕ → ℕ → Bool) : Bool :=
  ws.any (fun a => ws.any (fun b =>
    Nat.ble a b && (tryV ws bs r (a &&& b) || tryV ws bs r (a ||| b))))

theorem pairsAny_true {ws : List ℕ} {bs : ℕ} {r : List ℕ → ℕ → Bool} {a b v : ℕ}
    (hi : Inv ws bs) (ha : a ∈ ws)
    (hb : b ∈ ws) (hv : v = a &&& b ∨ v = a ||| b) (hn : v ∉ ws)
    (h : r (v :: ws) (bs ||| 1 <<< v) = true) :
    pairsAny ws bs r = true := by
  have main : ∀ a b, a ∈ ws → b ∈ ws → a ≤ b → (v = a &&& b ∨ v = a ||| b) →
      pairsAny ws bs r = true := by
    intro a b ha hb hab hv
    unfold pairsAny
    rw [List.any_eq_true]
    refine ⟨a, ha, ?_⟩
    rw [List.any_eq_true]
    refine ⟨b, hb, ?_⟩
    rw [Nat.ble_eq_true_of_le hab]
    rcases hv with rfl | rfl
    · rw [tryV_true hi hn h]; rfl
    · rw [tryV_true hi hn h]; simp
  rcases Nat.le_total a b with hab | hab
  · exact main a b ha hb hab hv
  · refine main b a hb ha hab ?_
    rcases hv with rfl | rfl
    · exact Or.inl (Nat.and_comm a b)
    · exact Or.inr (Nat.or_comm a b)

def notsAny (full : ℕ) (ws : List ℕ) (bs : ℕ) (r : List ℕ → ℕ → Bool) : Bool :=
  ws.any (fun a => tryV ws bs r (full ^^^ a))

theorem notsAny_true {full : ℕ} {ws : List ℕ} {bs : ℕ} {r : List ℕ → ℕ → Bool} {a : ℕ}
    (hi : Inv ws bs) (ha : a ∈ ws) (hn : (full ^^^ a) ∉ ws)
    (h : r ((full ^^^ a) :: ws) (bs ||| 1 <<< (full ^^^ a)) = true) :
    notsAny full ws bs r = true := by
  unfold notsAny
  rw [List.any_eq_true]
  exact ⟨a, ha, tryV_true hi hn h⟩

def search (full : ℕ) (tg : List ℕ) : ℕ → ℕ → List ℕ → ℕ → Bool
  | 0, _, _, bs => tg.all (fun m => Nat.testBit bs m)
  | s + 1, 0, ws, bs => Nat.ble (missB tg bs).length (s + 1) &&
      (search full tg s 0 ws bs || pairsAny ws bs (fun l b => search full tg s 0 l b))
  | s + 1, k + 1, ws, bs => Nat.ble (missB tg bs).length (s + 1) &&
      (search full tg s (k + 1) ws bs ||
        pairsAny ws bs (fun l b => search full tg s (k + 1) l b) ||
        notsAny full ws bs (fun l b => search full tg s k l b))

theorem search_skip {full : ℕ} {tg : List ℕ} {s k : ℕ} {ws : List ℕ} {bs : ℕ}
    (hm : (missB tg bs).length ≤ s + 1)
    (h : search full tg s k ws bs = true) : search full tg (s + 1) k ws bs = true := by
  cases k with
  | zero => simp only [search, Nat.ble_eq_true_of_le hm, h, Bool.true_or, Bool.true_and]
  | succ k => simp only [search, Nat.ble_eq_true_of_le hm, h, Bool.true_or, Bool.true_and]

theorem search_pair {full : ℕ} {tg : List ℕ} {s k : ℕ} {ws : List ℕ} {bs : ℕ}
    (hm : (missB tg bs).length ≤ s + 1)
    (h : pairsAny ws bs (fun l b => search full tg s k l b) = true) :
    search full tg (s + 1) k ws bs = true := by
  cases k with
  | zero => simp only [search, Nat.ble_eq_true_of_le hm, h, Bool.or_true, Bool.true_and]
  | succ k =>
    simp only [search, Nat.ble_eq_true_of_le hm, h, Bool.or_true, Bool.true_or, Bool.true_and]

theorem search_not {full : ℕ} {tg : List ℕ} {s k : ℕ} {ws : List ℕ} {bs : ℕ}
    (hm : (missB tg bs).length ≤ s + 1)
    (h : notsAny full ws bs (fun l b => search full tg s k l b) = true) :
    search full tg (s + 1) (k + 1) ws bs = true := by
  simp only [search, Nat.ble_eq_true_of_le hm, h, Bool.or_true, Bool.true_and]

theorem search_of_reach {full : ℕ} {tg : List ℕ} (hnd : tg.Nodup) :
    ∀ (s k : ℕ) (ws : List ℕ) (bs : ℕ), Inv ws bs →
    Reach full tg s k ws → search full tg s k ws bs = true := by
  intro s
  induction s with
  | zero =>
    intro k ws bs hi h
    simp only [search, List.all_eq_true]
    intro m hm
    rw [hi m]
    exact mem_iff.mpr (h m hm)
  | succ s ih =>
    intro k ws bs hi h
    have hm : (missB tg bs).length ≤ s + 1 := by
      rw [missB_eq hi]; exact reach_miss hnd _ _ _ h
    have hdup : ∀ v k0, k0 ≤ k → v ∈ ws → Reach full tg s k0 (v :: ws) →
        search full tg (s + 1) k ws bs = true := by
      intro v k0 hk0 hv hr
      refine search_skip hm (ih k ws bs hi (reach_mono s k0 k _ _ ?_ hk0 hr))
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hv
      · exact hx
    rcases h with h | ⟨a, ha, b, hb, h | h⟩ | ⟨a, ha, k', rfl, h⟩
    · exact search_skip hm (ih k ws bs hi h)
    · by_cases hv : (a &&& b) ∈ ws
      · exact hdup _ k (Nat.le_refl _) hv h
      · exact search_pair hm
          (pairsAny_true hi ha hb (Or.inl rfl) hv (ih _ _ _ (inv_cons hi _) h))
    · by_cases hv : (a ||| b) ∈ ws
      · exact hdup _ k (Nat.le_refl _) hv h
      · exact search_pair hm
          (pairsAny_true hi ha hb (Or.inr rfl) hv (ih _ _ _ (inv_cons hi _) h))
    · by_cases hv : (full ^^^ a) ∈ ws
      · exact hdup _ k' (Nat.le_succ _) hv h
      · exact search_not hm (notsAny_true hi ha hv (ih _ _ _ (inv_cons hi _) h))

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem gate_mask (T full : ℕ) (hfull : full = 2 ^ T - 1) (ws : List ℕ) (W : ℕ → List Bool)
    (L : ℕ) (h0 : 0 ∈ ws) (h1 : full ∈ ws)
    (hrep : ∀ i < L, ∃ m ∈ ws, m < 2 ^ T ∧ ∀ t < T, m.testBit t = (W t).getD i false)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < L) :
    ∃ v, v < 2 ^ T ∧
      (∀ t < T, v.testBit t = g.op.eval (g.inputs.map fun i => (W t).getD i false)) ∧
      ((g.op ≠ GateOp.not ∧ ∃ a ∈ ws, ∃ b ∈ ws, v = a &&& b ∨ v = a ||| b) ∨
       (g.op = GateOp.not ∧ ∃ a ∈ ws, v = full ^^^ a)) := by
  have hpos : 0 < 2 ^ T := Nat.pos_of_ne_zero (by simp)
  have hfl : full < 2 ^ T := by omega
  have hft : ∀ t < T, full.testBit t = true := by
    intro t ht; rw [hfull, Nat.testBit_two_pow_sub_one]; simpa using ht
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen hin ⊢
  rcases hop with rfl | rfl | rfl
  · have hne : GateOp.and ≠ GateOp.not := by intro h; cases h
    match inputs, hlen, hin with
    | [], _, _ =>
      exact ⟨full, hfl, fun t ht => by simp [GateOp.eval, hft t ht],
        Or.inl ⟨hne, full, h1, full, h1, Or.inl (Nat.and_self _).symm⟩⟩
    | [i], _, hin =>
      obtain ⟨m, hm, hml, hmt⟩ := hrep i (hin i (by simp))
      exact ⟨m, hml, fun t ht => by simp [GateOp.eval, hmt t ht],
        Or.inl ⟨hne, m, hm, m, hm, Or.inl (Nat.and_self _).symm⟩⟩
    | [i, j], _, hin =>
      obtain ⟨m, hm, hml, hmt⟩ := hrep i (hin i (by simp))
      obtain ⟨n, hn, hnl, hnt⟩ := hrep j (hin j (by simp))
      exact ⟨m &&& n, Nat.and_lt_two_pow _ hnl,
        fun t ht => by simp [GateOp.eval, Nat.testBit_and, hmt t ht, hnt t ht],
        Or.inl ⟨hne, m, hm, n, hn, Or.inl rfl⟩⟩
    | _ :: _ :: _ :: _, hlen, _ => simp at hlen
  · have hne : GateOp.or ≠ GateOp.not := by intro h; cases h
    match inputs, hlen, hin with
    | [], _, _ =>
      exact ⟨0, hpos, fun t ht => by simp [GateOp.eval],
        Or.inl ⟨hne, 0, h0, 0, h0, Or.inl (Nat.and_self _).symm⟩⟩
    | [i], _, hin =>
      obtain ⟨m, hm, hml, hmt⟩ := hrep i (hin i (by simp))
      exact ⟨m, hml, fun t ht => by simp [GateOp.eval, hmt t ht],
        Or.inl ⟨hne, m, hm, m, hm, Or.inl (Nat.and_self _).symm⟩⟩
    | [i, j], _, hin =>
      obtain ⟨m, hm, hml, hmt⟩ := hrep i (hin i (by simp))
      obtain ⟨n, hn, hnl, hnt⟩ := hrep j (hin j (by simp))
      exact ⟨m ||| n, Nat.or_lt_two_pow hml hnl,
        fun t ht => by simp [GateOp.eval, Nat.testBit_or, hmt t ht, hnt t ht],
        Or.inl ⟨hne, m, hm, n, hn, Or.inr rfl⟩⟩
    | _ :: _ :: _ :: _, hlen, _ => simp at hlen
  · match inputs, hin with
    | [], _ =>
      exact ⟨full ^^^ 0, by simpa using hfl,
        fun t ht => by simp [GateOp.eval, hft t ht],
        Or.inr ⟨rfl, 0, h0, rfl⟩⟩
    | i :: rest, hin =>
      obtain ⟨m, hm, hml, hmt⟩ := hrep i (hin i (by simp))
      exact ⟨full ^^^ m, Nat.xor_lt_two_pow hfl hml,
        fun t ht => by simp [GateOp.eval, Nat.testBit_xor, hft t ht, hmt t ht],
        Or.inr ⟨rfl, m, hm, rfl⟩⟩

theorem reach_of_circuit (T full : ℕ) (hfull : full = 2 ^ T - 1) (tg : List ℕ)
    (htg : ∀ M ∈ tg, M < 2 ^ T) {dec : ∀ g : Gate, Decidable (g.op = GateOp.not)} :
    ∀ (gs : List Gate) (W : ℕ → List Bool) (L : ℕ) (ws : List ℕ) (s k : ℕ),
      (∀ t < T, (W t).length = L) →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + j) →
      (gs.filter fun g => @decide (g.op = GateOp.not) (dec g)).length ≤ k →
      gs.length ≤ s →
      0 ∈ ws → full ∈ ws →
      (∀ i < L, ∃ m ∈ ws, m < 2 ^ T ∧ ∀ t < T, m.testBit t = (W t).getD i false) →
      (∀ M ∈ tg, ∃ p < L + gs.length, ∀ t < T, (run gs (W t)).getD p false = M.testBit t) →
      Reach full tg s k ws := by
  intro gs
  induction gs with
  | nil =>
    intro W L ws s k hlen hop hrb hnot hs h0 h1 hrep hout
    apply reach_base
    intro M hM
    obtain ⟨p, hp, hpt⟩ := hout M hM
    obtain ⟨m, hm, hmlt, hmt⟩ := hrep p (by simpa using hp)
    have hmM : m = M := by
      apply Nat.eq_of_testBit_eq
      intro t
      by_cases ht : t < T
      · rw [hmt t ht, ← hpt t ht]; rfl
      · have hle : 2 ^ T ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hmlt hle),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (htg M hM) hle)]
    exact hmM ▸ hm
  | cons g gs ih =>
    intro W L ws s k hlen hop hrb hnot hs h0 h1 hrep hout
    obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by simp at hs; omega⟩
    have hg := hop g (List.mem_cons.mpr (Or.inl rfl))
    have hin : ∀ i ∈ g.inputs, i < L := by
      intro i hi
      have := hrb 0 (by simp) i (by simpa using hi)
      simpa using this
    obtain ⟨v, hvlt, hvt, hcase⟩ := gate_mask T full hfull ws W L h0 h1 hrep g hg.1 hg.2 hin
    have key : ∀ k', (gs.filter fun g => @decide (g.op = GateOp.not) (dec g)).length ≤ k' →
        Reach full tg s k' (v :: ws) := by
      intro k' hk'
      apply ih (fun t => W t ++ [g.op.eval (g.inputs.map fun i => (W t).getD i false)])
        (L + 1) (v :: ws) s k'
      · intro t ht; simp [hlen t ht]
      · intro g' hg'; exact hop g' (List.mem_cons.mpr (Or.inr hg'))
      · intro j hj i hi
        have := hrb (j + 1) (by simpa using hj) i (by simpa using hi)
        omega
      · exact hk'
      · simpa using hs
      · exact List.mem_cons.mpr (Or.inr h0)
      · exact List.mem_cons.mpr (Or.inr h1)
      · intro i hi
        by_cases hiL : i < L
        · obtain ⟨m, hm, hmlt, hmt⟩ := hrep i hiL
          refine ⟨m, List.mem_cons.mpr (Or.inr hm), hmlt, fun t ht => ?_⟩
          rw [hmt t ht, List.getD_append _ _ _ _ (by rw [hlen t ht]; exact hiL)]
        · have hiE : i = L := by omega
          subst hiE
          refine ⟨v, List.mem_cons.mpr (Or.inl rfl), hvlt, fun t ht => ?_⟩
          rw [hvt t ht, List.getD_append_right _ _ _ _ (by rw [hlen t ht]), hlen t ht]
          simp
      · intro M hM
        obtain ⟨p, hp, hpt⟩ := hout M hM
        exact ⟨p, by simp at hp; omega, hpt⟩
    rcases hcase with ⟨hne, a, ha, b, hb, hv⟩ | ⟨heq, a, ha, hv⟩
    · have hk : (gs.filter fun g => @decide (g.op = GateOp.not) (dec g)).length ≤ k := by
        simpa [List.filter_cons, hne] using hnot
      have hr := key k hk
      rcases hv with rfl | rfl
      · exact Or.inr (Or.inl ⟨a, ha, b, hb, Or.inl hr⟩)
      · exact Or.inr (Or.inl ⟨a, ha, b, hb, Or.inr hr⟩)
    · have hk : (gs.filter fun g => @decide (g.op = GateOp.not) (dec g)).length + 1 ≤ k := by
        simpa [List.filter_cons, heq] using hnot
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      subst hv
      exact Or.inr (Or.inr ⟨a, ha, k', rfl, key k' (by omega)⟩)

theorem base_inv : Inv [62, 60, 56, 48, 32, 0, 63] 15060318633198616577 :=
  (by decide +kernel : bits [62, 60, 56, 48, 32, 0, 63] = 15060318633198616577) ▸ inv_bits [62, 60, 56, 48, 32, 0, 63]

set_option maxHeartbeats 0 in
theorem no_prog : search 63 [10, 42, 50] 6 2 [62, 60, 56, 48, 32, 0, 63] 15060318633198616577 = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_51302

theorem PEqualNP.Outside.L_meta_51302 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (42 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hF, hR, hN, hS, hall⟩
  have hreach := PEqualNP.Outside.L_meta_51302.reach_of_circuit 6 63 (by norm_num) [10, 42, 50] (by decide) D.gates
    (fun t => (List.ofFn (fun i : Fin 5 => decide (i.val < t))) ++ [false, true]) 7
    [62, 60, 56, 48, 32, 0, 63] 6 2
    (by intro t _; simp)
    (fun g hg => ⟨by simpa using (hF g hg).1, (hF g hg).2⟩) hR hN hS (by decide) (by decide)
    (by decide +kernel)
    (by
      intro M hM
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
      rcases hM with rfl | rfl | rfl
      · exact ⟨p.val, p.isLt, fun t ht => (hall ⟨t, ht⟩).1⟩
      · exact ⟨q.val, q.isLt, fun t ht => (hall ⟨t, ht⟩).2.1⟩
      · exact ⟨r.val, r.isLt, fun t ht => (hall ⟨t, ht⟩).2.2⟩)
  have hs := PEqualNP.Outside.L_meta_51302.search_of_reach (by decide) _ _ _ _ PEqualNP.Outside.L_meta_51302.base_inv hreach
  exact Bool.false_ne_true (PEqualNP.Outside.L_meta_51302.no_prog.symm.trans hs)
