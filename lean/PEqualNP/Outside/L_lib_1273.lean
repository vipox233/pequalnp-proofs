import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1273_aux

def step {n : ℕ} (p : Fin n × Fin n) (v : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = p.1 then v p.1 && v p.2 else if i = p.2 then v p.1 || v p.2 else v i

def run {n : ℕ} (net : List (Fin n × Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  net.foldl (fun v p => step p v) x

theorem pn_step_mono {n : ℕ} (p : Fin n × Fin n) (v w : Fin n → Bool)
    (h : ∀ j, v j = true → w j = true) (j : Fin n) : step p v j = true → step p w j = true := by
  have h1 := h p.1
  have h2 := h p.2
  have h3 := h j
  unfold step
  split_ifs <;> intro hh <;> (try simp only [Bool.and_eq_true, Bool.or_eq_true] at hh ⊢) <;> tauto

theorem pn_run_mono {n : ℕ} (rest : List (Fin n × Fin n)) : ∀ (v w : Fin n → Bool),
    (∀ j, v j = true → w j = true) → ∀ j, run rest v j = true → run rest w j = true := by
  induction rest with
  | nil => intro v w h; exact h
  | cons p rest ih => intro v w h; exact ih _ _ (pn_step_mono p v w h)

theorem pn_or_absorb (x y : Bool) (h : x = true → y = true) : (x || y) = y := by
  cases x <;> cases y <;> simp_all

theorem pn_and_absorb (x y : Bool) (h : y = true → x = true) : (x && y) = y := by
  cases x <;> cases y <;> simp_all

theorem pn_step_self {n : ℕ} (a : Fin n) (v : Fin n → Bool) : step (a, a) v = v := by
  funext j
  unfold step
  by_cases hj : j = a <;> simp [hj]

theorem pn_step_away {n : ℕ} (a b i : Fin n) (c : Bool) (v : Fin n → Bool) (ha : i ≠ a) (hb : i ≠ b) :
    step (a, b) (Function.update v i c) = Function.update (step (a, b) v) i c := by
  funext j
  unfold step
  by_cases hja : j = a <;> by_cases hjb : j = b <;> by_cases hji : j = i <;>
    simp_all [Function.update, Ne.symm ha, Ne.symm hb]

theorem pn_upd_mono {n : ℕ} (u : Fin n → Bool) (a : Fin n) :
    ∀ j, u j = true → Function.update u a true j = true := by
  intro j hj
  by_cases h : j = a <;> simp [Function.update, h, hj]

theorem pn_upd_mono0 {n : ℕ} (u : Fin n → Bool) (a : Fin n) :
    ∀ j, Function.update u a false j = true → u j = true := by
  intro j hj
  by_cases h : j = a <;> simp_all [Function.update]

theorem pn_upd_same {n : ℕ} (u : Fin n → Bool) (a : Fin n) (c : Bool) (h : u a = c) :
    Function.update u a c = u := by
  rw [← h]; exact Function.update_eq_self a u

theorem pin_one {n : ℕ} (rest : List (Fin n × Fin n)) (k : Fin n) (p : Fin n × Fin n) (v : Fin n → Bool)
    (i : Fin n) :
    run rest (step p (Function.update v i true)) k =
      if i = p.1 then (run rest (Function.update (step p v) p.2 true) k ||
          (v p.2 && run rest (Function.update (step p v) p.1 true) k))
      else if i = p.2 then (run rest (Function.update (step p v) p.2 true) k ||
          (v p.1 && run rest (Function.update (step p v) p.1 true) k))
      else run rest (Function.update (step p v) i true) k := by
  obtain ⟨a, b⟩ := p
  dsimp only
  by_cases hia : i = a
  · subst hia
    by_cases hib : i = b
    · subst hib
      simp only [pn_step_self, ite_true]
      cases run rest (Function.update v i true) k <;> simp
    · have hne : b ≠ i := Ne.symm hib
      cases hv : v b
      · have e : step (i, b) (Function.update v i true) = Function.update (step (i, b) v) b true := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hjb : j = b <;> simp_all [Function.update]
        simp [e]
      · have e : step (i, b) (Function.update v i true) = Function.update (step (i, b) v) i true := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hjb : j = b <;> simp_all [Function.update]
        have e2 : Function.update (step (i, b) v) b true = step (i, b) v :=
          pn_upd_same _ _ _ (by unfold step; simp [hne, hv])
        simp only [e, e2, ite_true, Bool.true_and]
        exact (pn_or_absorb _ _ (pn_run_mono rest _ _ (pn_upd_mono _ i) k)).symm
  · by_cases hib : i = b
    · subst hib
      have hne : a ≠ i := Ne.symm hia
      cases hv : v a
      · have e : step (a, i) (Function.update v i true) = Function.update (step (a, i) v) i true := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hja : j = a <;> simp_all [Function.update]
        simp [e, hia]
      · have e : step (a, i) (Function.update v i true) = Function.update (step (a, i) v) a true := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hja : j = a <;> simp_all [Function.update]
        have e2 : Function.update (step (a, i) v) i true = step (a, i) v :=
          pn_upd_same _ _ _ (by unfold step; simp [hia, hv])
        simp only [e, e2, hia, ite_true, ite_false, Bool.true_and]
        exact (pn_or_absorb _ _ (pn_run_mono rest _ _ (pn_upd_mono _ a) k)).symm
    · simp [hia, hib, pn_step_away a b i true v hia hib]

theorem pin_zero {n : ℕ} (rest : List (Fin n × Fin n)) (k : Fin n) (p : Fin n × Fin n) (v : Fin n → Bool)
    (i : Fin n) :
    run rest (step p (Function.update v i false)) k =
      if i = p.1 then (run rest (Function.update (step p v) p.1 false) k &&
          (v p.2 || run rest (Function.update (step p v) p.2 false) k))
      else if i = p.2 then (run rest (Function.update (step p v) p.1 false) k &&
          (v p.1 || run rest (Function.update (step p v) p.2 false) k))
      else run rest (Function.update (step p v) i false) k := by
  obtain ⟨a, b⟩ := p
  dsimp only
  by_cases hia : i = a
  · subst hia
    by_cases hib : i = b
    · subst hib
      simp only [pn_step_self, ite_true]
      cases run rest (Function.update v i false) k <;> simp
    · have hne : b ≠ i := Ne.symm hib
      cases hv : v b
      · have e : step (i, b) (Function.update v i false) = Function.update (step (i, b) v) b false := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hjb : j = b <;> simp_all [Function.update]
        have e2 : Function.update (step (i, b) v) i false = step (i, b) v :=
          pn_upd_same _ _ _ (by unfold step; simp [hv])
        simp only [e, e2, ite_true, Bool.false_or]
        exact (pn_and_absorb _ _ (pn_run_mono rest _ _ (pn_upd_mono0 _ b) k)).symm
      · have e : step (i, b) (Function.update v i false) = Function.update (step (i, b) v) i false := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hjb : j = b <;> simp_all [Function.update]
        simp [e]
  · by_cases hib : i = b
    · subst hib
      have hne : a ≠ i := Ne.symm hia
      cases hv : v a
      · have e : step (a, i) (Function.update v i false) = Function.update (step (a, i) v) i false := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hja : j = a <;> simp_all [Function.update]
        have e2 : Function.update (step (a, i) v) a false = step (a, i) v :=
          pn_upd_same _ _ _ (by unfold step; simp [hv])
        simp only [e, e2, hia, ite_true, ite_false, Bool.false_or]
        exact (pn_and_absorb _ _ (pn_run_mono rest _ _ (pn_upd_mono0 _ i) k)).symm
      · have e : step (a, i) (Function.update v i false) = Function.update (step (a, i) v) a false := by
          funext j; unfold step
          by_cases hj : j = i <;> by_cases hja : j = a <;> simp_all [Function.update]
        simp [e, hia]
    · simp [hia, hib, pn_step_away a b i false v hia hib]

def cc_ev (G : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
  (PEqualNP.CircuitLowerBounds.Circuit.mk G 0).wires w

def cc_fw {n : ℕ} (p : Fin n × Fin n) (fw : Fin n → ℕ) (m : ℕ) : Fin n → ℕ :=
  fun i => if i = p.1 then m else if i = p.2 then m+1 else fw i

def cc_fL {n : ℕ} : List (Fin n × Fin n) → (Fin n → ℕ) → ℕ → Fin n → ℕ
  | [], fw, _ => fw
  | p :: rest, fw, m => cc_fL rest (cc_fw p fw m) (m+2)

def cc_P1 {n : ℕ} (k : Fin n) : List (Fin n × Fin n) → (Fin n → ℕ) → ℕ → Fin n → ℕ
  | [], fw, _ => fun i => if i = k then n+1 else fw k
  | p :: rest, fw, m => fun i => if i = p.1 then m+2+10*rest.length+1
      else if i = p.2 then m+2+10*rest.length+3 else cc_P1 k rest (cc_fw p fw m) (m+2) i

def cc_P0 {n : ℕ} (k : Fin n) : List (Fin n × Fin n) → (Fin n → ℕ) → ℕ → Fin n → ℕ
  | [], fw, _ => fun i => if i = k then n else fw k
  | p :: rest, fw, m => fun i => if i = p.1 then m+2+10*rest.length+5
      else if i = p.2 then m+2+10*rest.length+7 else cc_P0 k rest (cc_fw p fw m) (m+2) i

def cc_rev (fa fb p1a p1b p0a p0b M : ℕ) : List PEqualNP.CircuitLowerBounds.Gate :=
  [⟨.and, [fb, p1a]⟩, ⟨.or, [p1b, M]⟩, ⟨.and, [fa, p1a]⟩, ⟨.or, [p1b, M+2]⟩,
   ⟨.or, [fb, p0b]⟩, ⟨.and, [p0a, M+4]⟩, ⟨.or, [fa, p0b]⟩, ⟨.and, [p0a, M+6]⟩]

def cc_G {n : ℕ} (k : Fin n) :
    List (Fin n × Fin n) → (Fin n → ℕ) → ℕ → List PEqualNP.CircuitLowerBounds.Gate
  | [], _, _ => []
  | p :: rest, fw, m => [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] ++
      cc_G k rest (cc_fw p fw m) (m+2) ++
      cc_rev (fw p.1) (fw p.2) (cc_P1 k rest (cc_fw p fw m) (m+2) p.1)
        (cc_P1 k rest (cc_fw p fw m) (m+2) p.2) (cc_P0 k rest (cc_fw p fw m) (m+2) p.1)
        (cc_P0 k rest (cc_fw p fw m) (m+2) p.2) (m+2+10*rest.length)

def cc_rb (m : ℕ) : List PEqualNP.CircuitLowerBounds.Gate → Prop
  | [] => True
  | g :: G => (∀ i ∈ g.inputs, i < m) ∧ cc_rb (m+1) G

theorem cc_ev_nil (w : List Bool) : cc_ev [] w = w := rfl

theorem cc_ev_cons (g : PEqualNP.CircuitLowerBounds.Gate) (G : List PEqualNP.CircuitLowerBounds.Gate)
    (w : List Bool) :
    cc_ev (g :: G) w = cc_ev G (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem cc_ev_append (G1 G2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    cc_ev (G1 ++ G2) w = cc_ev G2 (cc_ev G1 w) := by
  simp [cc_ev, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_append]

theorem cc_ev_pre (G : List PEqualNP.CircuitLowerBounds.Gate) :
    ∀ w : List Bool, ∃ l, cc_ev G w = w ++ l ∧ l.length = G.length := by
  induction G with
  | nil => intro w; exact ⟨[], by simp [cc_ev_nil], rfl⟩
  | cons g G ih =>
    intro w
    obtain ⟨l, h1, h2⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: l, ?_, ?_⟩
    · rw [cc_ev_cons, h1]
      simp
    · simp [h2]

theorem cc_ev_len (G : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (cc_ev G w).length = w.length + G.length := by
  obtain ⟨l, h1, h2⟩ := cc_ev_pre G w
  rw [h1, List.length_append, h2]

theorem cc_ev_old (G : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (cc_ev G w).getD i false = w.getD i false := by
  obtain ⟨l, h1, -⟩ := cc_ev_pre G w
  rw [h1, List.getD_append _ _ _ _ hi]

theorem cc_ev_new (g : PEqualNP.CircuitLowerBounds.Gate) (G : List PEqualNP.CircuitLowerBounds.Gate)
    (w : List Bool) :
    (cc_ev (g :: G) w).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [cc_ev_cons, cc_ev_old _ _ _ (by simp)]
  simp

theorem cc_rb_append (G1 G2 : List PEqualNP.CircuitLowerBounds.Gate) :
    ∀ m, cc_rb m (G1 ++ G2) ↔ cc_rb m G1 ∧ cc_rb (m + G1.length) G2 := by
  induction G1 with
  | nil => intro m; simp [cc_rb]
  | cons g G ih =>
    intro m
    simp only [List.cons_append, cc_rb, ih, List.length_cons]
    rw [show m + 1 + G.length = m + (G.length + 1) by omega]
    tauto

theorem cc_rb_rb (G : List PEqualNP.CircuitLowerBounds.Gate) :
    ∀ m, cc_rb m G → ∀ j < G.length, ∀ i ∈ (G.getD j ⟨.or, []⟩).inputs, i < m + j := by
  induction G with
  | nil => intro m _ j hj; simp at hj
  | cons g G ih =>
    intro m h j hj i hi
    cases j with
    | zero => simpa using h.1 i hi
    | succ j =>
      have := ih (m+1) h.2 j (by simpa using hj) i (by simpa using hi)
      omega

theorem cc_G_len {n : ℕ} (k : Fin n) (net : List (Fin n × Fin n)) :
    ∀ fw m, (cc_G k net fw m).length = 10 * net.length := by
  induction net with
  | nil => intro fw m; rfl
  | cons p rest ih =>
    intro fw m
    simp [cc_G, cc_rev, ih]
    ring

theorem cc_bounds {n : ℕ} (k : Fin n) (net : List (Fin n × Fin n)) :
    ∀ fw m, (∀ i, fw i < m) → n+1 < m →
      (∀ i, cc_fL net fw m i < m + 10*net.length) ∧ (∀ i, cc_P1 k net fw m i < m + 10*net.length) ∧
      (∀ i, cc_P0 k net fw m i < m + 10*net.length) := by
  induction net with
  | nil =>
    intro fw m h1 h2
    simp only [cc_fL, cc_P1, cc_P0, List.length_nil, Nat.mul_zero, Nat.add_zero]
    refine ⟨h1, fun i => ?_, fun i => ?_⟩
    · split_ifs
      · omega
      · exact h1 k
    · split_ifs
      · omega
      · exact h1 k
  | cons p rest ih =>
    intro fw m h1 h2
    have hf : ∀ i, cc_fw p fw m i < m + 2 := by
      intro i; unfold cc_fw; split_ifs <;> [omega; omega; (have := h1 i; omega)]
    obtain ⟨a1, a2, a3⟩ := ih _ _ hf (by omega)
    simp only [cc_fL, cc_P1, cc_P0, List.length_cons]
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · have := a1 i; omega
    · split_ifs <;> [omega; omega; (have := a2 i; omega)]
    · split_ifs <;> [omega; omega; (have := a3 i; omega)]

theorem cc_fwd_vals {n : ℕ} (p : Fin n × Fin n) (fw : Fin n → ℕ) (w : List Bool) (V : Fin n → Bool)
    (hb : ∀ i, fw i < w.length) (hv : ∀ i, w.getD (fw i) false = V i) :
    ∀ i, (cc_ev [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w).getD
      (cc_fw p fw w.length i) false = step p V i := by
  intro i
  have e3 := cc_ev_old [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w (fw i) (hb i)
  have hv' : ∀ i, w[fw i]'(hb i) = V i := by
    intro i; rw [← hv i]; simp [hb]
  unfold cc_fw step
  split_ifs
  · simp [cc_ev_cons, cc_ev_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, hb, hv', List.getElem?_append_left]
  · simp [cc_ev_cons, cc_ev_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, hb, hv', List.getElem?_append_left]
  · rw [e3, hv]

theorem cc_rev_vals (fa fb p1a p1b p0a p0b : ℕ) (W R : List Bool)
    (hR : R = cc_ev (cc_rev fa fb p1a p1b p0a p0b W.length) W) (h1 : fa < W.length)
    (h2 : fb < W.length) (h3 : p1a < W.length) (h4 : p1b < W.length) (h5 : p0a < W.length)
    (h6 : p0b < W.length) :
    R.getD (W.length+1) false = (W.getD p1b false || (W.getD fb false && W.getD p1a false)) ∧
    R.getD (W.length+3) false = (W.getD p1b false || (W.getD fa false && W.getD p1a false)) ∧
    R.getD (W.length+5) false = (W.getD p0a false && (W.getD fb false || W.getD p0b false)) ∧
    R.getD (W.length+7) false = (W.getD p0a false && (W.getD fa false || W.getD p0b false)) := by
  subst hR
  simp [cc_rev, cc_ev_cons, cc_ev_nil, PEqualNP.CircuitLowerBounds.GateOp.eval, h1, h2, h3, h4, h5, h6, List.getElem?_append_left]

theorem cc_sem {n : ℕ} (k : Fin n) (net : List (Fin n × Fin n)) :
    ∀ (fw : Fin n → ℕ) (w : List Bool) (V : Fin n → Bool), (∀ i, fw i < w.length) →
      n+1 < w.length → (∀ i, w.getD (fw i) false = V i) → w.getD n false = false →
      w.getD (n+1) false = true →
      (∀ i, (cc_ev (cc_G k net fw w.length) w).getD (cc_fL net fw w.length i) false = run net V i) ∧
      (∀ j, (cc_ev (cc_G k net fw w.length) w).getD (cc_P1 k net fw w.length j) false =
        run net (Function.update V j true) k) ∧
      (∀ j, (cc_ev (cc_G k net fw w.length) w).getD (cc_P0 k net fw w.length j) false =
        run net (Function.update V j false) k) := by
  induction net with
  | nil =>
    intro fw w V hb hn hv h0 h1
    simp only [cc_G, cc_ev_nil, cc_fL, cc_P1, cc_P0]
    refine ⟨hv, fun j => ?_, fun j => ?_⟩
    · split_ifs with h
      · subst h; rw [h1]; simp [run]
      · rw [hv]; simp [run, Function.update_of_ne (Ne.symm h)]
    · split_ifs with h
      · subst h; rw [h0]; simp [run]
      · rw [hv]; simp [run, Function.update_of_ne (Ne.symm h)]
  | cons p rest ih =>
    intro fw w V hb hn hv h0 h1
    have hfw := cc_fwd_vals p fw w V hb hv
    have hl1 : (cc_ev [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w).length = w.length + 2 := by
      rw [cc_ev_len]; rfl
    have hb1 : ∀ i, cc_fw p fw w.length i <
        (cc_ev [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w).length := by
      intro i; rw [hl1]; unfold cc_fw; split_ifs <;> [omega; omega; (have := hb i; omega)]
    obtain ⟨i1, i2, i3⟩ := ih (cc_fw p fw w.length) _ (step p V) hb1 (by omega) hfw
      (by rw [cc_ev_old _ _ _ (by omega)]; exact h0) (by rw [cc_ev_old _ _ _ (by omega)]; exact h1)
    rw [hl1] at i1 i2 i3
    obtain ⟨b1, b2, b3⟩ := cc_bounds k rest (cc_fw p fw w.length) (w.length+2)
      (fun i => by have := hb1 i; omega) (by omega)
    have hWl := cc_ev_len (cc_G k rest (cc_fw p fw w.length) (w.length + 2))
      (cc_ev [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w)
    rw [hl1, cc_G_len] at hWl
    have hWf : ∀ x, (cc_ev (cc_G k rest (cc_fw p fw w.length) (w.length + 2))
        (cc_ev [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w)).getD (fw x) false = V x := by
      intro x
      rw [cc_ev_old _ _ _ (by have := hb x; omega), cc_ev_old _ _ _ (hb x), hv]
    obtain ⟨r1, r2, r3, r4⟩ := cc_rev_vals (fw p.1) (fw p.2)
      (cc_P1 k rest (cc_fw p fw w.length) (w.length+2) p.1)
      (cc_P1 k rest (cc_fw p fw w.length) (w.length+2) p.2)
      (cc_P0 k rest (cc_fw p fw w.length) (w.length+2) p.1)
      (cc_P0 k rest (cc_fw p fw w.length) (w.length+2) p.2) _
      (cc_ev (cc_G k (p :: rest) fw w.length) w)
      (by rw [hWl]; simp only [cc_G, cc_ev_append])
      (by have := hb p.1; omega) (by have := hb p.2; omega) (by have := b2 p.1; omega)
      (by have := b2 p.2; omega) (by have := b3 p.1; omega) (by have := b3 p.2; omega)
    rw [hWl] at r1 r2 r3 r4
    simp only [hWf, i2, i3] at r1 r2 r3 r4
    have hR : cc_ev (cc_G k (p :: rest) fw w.length) w =
        cc_ev (cc_rev (fw p.1) (fw p.2) (cc_P1 k rest (cc_fw p fw w.length) (w.length+2) p.1)
          (cc_P1 k rest (cc_fw p fw w.length) (w.length+2) p.2)
          (cc_P0 k rest (cc_fw p fw w.length) (w.length+2) p.1)
          (cc_P0 k rest (cc_fw p fw w.length) (w.length+2) p.2) (w.length+2+10*rest.length))
        (cc_ev (cc_G k rest (cc_fw p fw w.length) (w.length + 2))
          (cc_ev [⟨.and, [fw p.1, fw p.2]⟩, ⟨.or, [fw p.1, fw p.2]⟩] w)) := by
      simp only [cc_G, cc_ev_append]
    refine ⟨fun i => ?_, fun j => ?_, fun j => ?_⟩
    · simp only [cc_fL]
      rw [hR, cc_ev_old _ _ _ (by have := b1 i; omega)]
      exact i1 i
    · show _ = run rest (step p (Function.update V j true)) k
      rw [pin_one]
      simp only [cc_P1]
      split_ifs
      · exact r1
      · exact r2
      · rw [hR, cc_ev_old _ _ _ (by have := b2 j; omega), i2]
    · show _ = run rest (step p (Function.update V j false)) k
      rw [pin_zero]
      simp only [cc_P0]
      split_ifs
      · exact r3
      · exact r4
      · rw [hR, cc_ev_old _ _ _ (by have := b3 j; omega), i3]

theorem cc_G_mono {n : ℕ} (k : Fin n) (net : List (Fin n × Fin n)) :
    ∀ fw m, ∀ g ∈ cc_G k net fw m, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := by
  induction net with
  | nil => intro fw m g hg; simp [cc_G] at hg
  | cons p rest ih =>
    intro fw m g hg
    simp only [cc_G, cc_rev, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    obtain ((h | h) | h) | h | h | h | h | h | h | h | h := hg
    all_goals first | exact ih _ _ g h | (subst h; simp)

theorem cc_G_rb {n : ℕ} (k : Fin n) (net : List (Fin n × Fin n)) :
    ∀ fw m, (∀ i, fw i < m) → n+1 < m → cc_rb m (cc_G k net fw m) := by
  induction net with
  | nil => intro fw m _ _; simp [cc_G, cc_rb]
  | cons p rest ih =>
    intro fw m hb hn
    have hf : ∀ i, cc_fw p fw m i < m + 2 := by
      intro i; unfold cc_fw; split_ifs <;> [omega; omega; (have := hb i; omega)]
    obtain ⟨b1, b2, b3⟩ := cc_bounds k rest (cc_fw p fw m) (m+2) hf (by omega)
    simp only [cc_G]
    rw [cc_rb_append, cc_rb_append, List.length_append, cc_G_len]
    refine ⟨⟨?_, ih _ _ hf (by omega)⟩, ?_⟩
    · have := hb p.1; have := hb p.2
      simp only [cc_rb, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨?_, ?_, trivial⟩ <;> rintro i (rfl | rfl) <;> omega
    · have := hb p.1; have := hb p.2; have := b2 p.1; have := b2 p.2; have := b3 p.1
      have := b3 p.2
      simp only [cc_rb, cc_rev, List.mem_cons, List.not_mem_nil, or_false, List.length_cons,
        List.length_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> rintro i (rfl | rfl) <;> omega

theorem core (n : ℕ) (net : List (Fin n × Fin n)) (k : Fin n) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
      C.size ≤ 10*net.length ∧
      ∃ (out lo hi : Fin n → Fin (n+2+C.size)), ∀ x : Fin n → Bool,
        (∀ i, (C.wires (List.ofFn x ++ [false,true])).getD (out i).val false = run net x i) ∧
        (∀ j, (C.wires (List.ofFn x ++ [false,true])).getD (lo j).val false =
          run net (Function.update x j false) k) ∧
        (∀ j, (C.wires (List.ofFn x ++ [false,true])).getD (hi j).val false =
          run net (Function.update x j true) k) := by
  have hb0 : ∀ i : Fin n, (fun i : Fin n => i.val) i < n + 2 := fun i => by
    have := i.isLt; simp only; omega
  have hsz : (PEqualNP.CircuitLowerBounds.Circuit.mk (cc_G k net (fun i => i.val) (n+2)) 0).size =
      10 * net.length := cc_G_len k net _ _
  obtain ⟨b1, b2, b3⟩ := cc_bounds k net (fun i => i.val) (n+2) hb0 (by omega)
  refine ⟨⟨cc_G k net (fun i => i.val) (n+2), 0⟩, cc_G_mono k net _ _, ?_, by show 0 < _; omega, by omega,
    fun i => ⟨cc_fL net (fun i => i.val) (n+2) i, by rw [hsz]; exact b1 i⟩,
    fun i => ⟨cc_P0 k net (fun i => i.val) (n+2) i, by rw [hsz]; exact b3 i⟩,
    fun i => ⟨cc_P1 k net (fun i => i.val) (n+2) i, by rw [hsz]; exact b2 i⟩, fun x => ?_⟩
  · intro j hj i hi
    exact cc_rb_rb _ (n+2) (cc_G_rb k net _ _ hb0 (by omega)) j hj i hi
  · have hl : (List.ofFn x ++ [false,true]).length = n+2 := by simp
    have hv : ∀ i : Fin n, (List.ofFn x ++ [false,true]).getD i.val false = x i := by
      intro i; simp [List.getElem?_append_left]
    have := cc_sem k net (fun i => i.val) (List.ofFn x ++ [false,true]) x (by rw [hl]; exact hb0)
      (by rw [hl]; omega) hv (by simp) (by simp)
    rw [hl] at this
    exact ⟨this.1, this.2.2, this.2.1⟩

end PEqualNP.Outside.L_lib_1273_aux

theorem PEqualNP.Outside.L_lib_1273 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (net : List (Fin n × Fin n)) (k : Fin n),
  let forward := fun (x : Fin n → Bool) =>
    net.foldl (fun (v : Fin n → Bool) (p : Fin n × Fin n) (i : Fin n) =>
      if i = p.1 then v p.1 && v p.2 else if i = p.2 then v p.1 || v p.2 else v i) x
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    C.size ≤ 10*net.length ∧
    ∃ (out lo hi : Fin n → Fin (n+2+C.size)), ∀ x : Fin n → Bool,
      let w := C.wires (List.ofFn x ++ [false,true])
      (∀ i, w.getD (out i).val false = forward x i) ∧
      (∀ j, w.getD (lo j).val false = forward (fun i => if i=j then false else x i) k) ∧
      ∀ j, w.getD (hi j).val false = forward (fun i => if i=j then true else x i) k) := by
  intro n net k forward
  have hf : ∀ x, forward x = PEqualNP.Outside.L_lib_1273_aux.run net x := by
    intro x
    simp only [forward, PEqualNP.Outside.L_lib_1273_aux.run]
    congr
    funext v p i
    unfold PEqualNP.Outside.L_lib_1273_aux.step
    split_ifs <;> rfl
  obtain ⟨C, h1, h2, h3, h4, out, lo, hi, h⟩ := PEqualNP.Outside.L_lib_1273_aux.core n net k
  refine ⟨C, h1, h2, h3, h4, out, lo, hi, fun x => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h x
  refine ⟨fun i => by rw [hf]; exact e1 i, fun j => ?_, fun j => ?_⟩
  · rw [e2 j, hf]
    congr 2
    funext i
    split_ifs with h
    · subst h
      simp
    · simp [h]
  · rw [e3 j, hf]
    congr 2
    funext i
    split_ifs with h
    · subst h
      simp
    · simp [h]
