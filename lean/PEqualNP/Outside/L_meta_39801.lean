import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_39801
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section Gen
variable {α : Type} (A O D : α → α → α)
def Cand (L : List α) (s : α) : Prop :=
  ∃ x ∈ L, ∃ y ∈ L, s = A x y ∨ s = O x y ∨ s = D x y
theorem Cand.mono {L L' : List α} {s : α} (h : ∀ x ∈ L, x ∈ L') :
    Cand A O D L s → Cand A O D L' s := by
  rintro ⟨x, hx, y, hy, h2⟩
  exact ⟨x, h x hx, y, h y hy, h2⟩
theorem consSub {L L' : List α} (h : ∀ x ∈ L, x ∈ L') (s : α) :
    ∀ x ∈ s :: L, x ∈ s :: L' := by
  intro x hx
  simp only [List.mem_cons] at hx ⊢
  exact hx.imp id (h x)
def Reach (T : α) : ℕ → List α → Prop
  | 0, L => T ∈ L
  | k + 1, L => T ∈ L ∨ ∃ s, Cand A O D L s ∧ Reach T k (s :: L)
theorem Reach.monoL {T : α} : ∀ (k : ℕ) (L L' : List α), (∀ x ∈ L, x ∈ L') →
    Reach A O D T k L → Reach A O D T k L' := by
  intro k
  induction k with
  | zero => intro L L' h hr; exact h _ hr
  | succ k ih =>
    intro L L' h hr
    rcases hr with h1 | ⟨s, hc, hr⟩
    · exact Or.inl (h _ h1)
    · exact Or.inr ⟨s, hc.mono A O D h, ih _ _ (consSub h s) hr⟩
theorem Reach.monoK {T : α} : ∀ (k : ℕ) (L : List α), Reach A O D T k L →
    Reach A O D T (k + 1) L := by
  intro k
  induction k with
  | zero => intro L hr; exact Or.inl hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, hc, hr⟩
    · exact Or.inl h1
    · exact Or.inr ⟨s, hc, ih _ hr⟩
theorem Reach.monoLe {T : α} {k k' : ℕ} (h : k ≤ k') (L : List α) (hr : Reach A O D T k L) :
    Reach A O D T k' L := by
  induction h with
  | refl => exact hr
  | step _ ih => exact Reach.monoK A O D _ _ ih
theorem Reach.map {β : Type} (A' O' D' : β → β → β) (φ : α → β)
    (hc : ∀ x y s, (s = A x y ∨ s = O x y ∨ s = D x y) → ∀ L' : List β, φ x ∈ L' →
      φ y ∈ L' → Cand A' O' D' L' (φ s)) {T : α} : ∀ (k : ℕ) (L : List α),
    Reach A O D T k L → Reach A' O' D' (φ T) k (L.map φ) := by
  intro k
  induction k with
  | zero => intro L hr; exact List.mem_map_of_mem hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, ⟨x, hx, y, hy, hs⟩, hr⟩
    · exact Or.inl (List.mem_map_of_mem h1)
    · exact Or.inr ⟨φ s, hc x y s hs _ (List.mem_map_of_mem hx) (List.mem_map_of_mem hy),
        ih _ hr⟩
end Gen
abbrev BF (n : ℕ) : Type := (Fin n → Bool) → Bool
abbrev bDiff (a b : Bool) : Bool := a && !b
def x0 (n : ℕ) : Fin n → Bool := fun _ => false
def fT (n : ℕ) : BF n := fun _ => true
def fF (n : ℕ) : BF n := fun _ => false
def fV {n : ℕ} (p : Fin n) : BF n := fun x => x p
def fNot {n : ℕ} (a : BF n) : BF n := fun x => !(a x)
def fBin {n : ℕ} (c : Bool → Bool → Bool) (a b : BF n) : BF n := fun x => c (a x) (b x)
abbrev fAnd {n : ℕ} : BF n → BF n → BF n := fBin and
abbrev fOr {n : ℕ} : BF n → BF n → BF n := fBin or
abbrev fDiff {n : ℕ} : BF n → BF n → BF n := fBin bDiff
abbrev R {n : ℕ} (f : BF n) (k : ℕ) (L : List (BF n)) : Prop := Reach fAnd fOr fDiff f k L
def L0 (n : ℕ) : List (BF n) := fF n :: List.ofFn (fun p : Fin n => fV p)
def ph {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (g : BF n) : BF n :=
  fun z => xor (g (u z)) (g (u (x0 n)))
abbrev nz {n : ℕ} (g : BF n) : BF n := ph id g
theorem nz_cases (c : Bool → Bool → Bool) (hc : c = and ∨ c = or ∨ c = bDiff) (cx cy : Bool) :
    (∀ a b : Bool, xor (c a b) (c cx cy) = and (xor a cx) (xor b cy)) ∨
    (∀ a b : Bool, xor (c a b) (c cx cy) = or (xor a cx) (xor b cy)) ∨
    (∀ a b : Bool, xor (c a b) (c cx cy) = bDiff (xor a cx) (xor b cy)) ∨
    (∀ a b : Bool, xor (c a b) (c cx cy) = bDiff (xor b cy) (xor a cx)) := by
  rcases hc with rfl | rfl | rfl <;> cases cx <;> cases cy <;> decide
theorem ph_bin {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (hc : c = and ∨ c = or ∨ c = bDiff) (X Y : BF n) :
    ph u (fBin c X Y) = fAnd (ph u X) (ph u Y) ∨ ph u (fBin c X Y) = fOr (ph u X) (ph u Y) ∨
    ph u (fBin c X Y) = fDiff (ph u X) (ph u Y) ∨
    ph u (fBin c X Y) = fDiff (ph u Y) (ph u X) := by
  rcases nz_cases c hc (X (u (x0 n))) (Y (u (x0 n))) with h | h | h | h
  · exact Or.inl (by funext z; exact h _ _)
  · exact Or.inr (Or.inl (by funext z; exact h _ _))
  · exact Or.inr (Or.inr (Or.inl (by funext z; exact h _ _)))
  · exact Or.inr (Or.inr (Or.inr (by funext z; exact h _ _)))
theorem ph_cand {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (hc : c = and ∨ c = or ∨ c = bDiff) (X Y : BF n) (L : List (BF n)) (hX : ph u X ∈ L)
    (hY : ph u Y ∈ L) : Cand fAnd fOr fDiff L (ph u (fBin c X Y)) := by
  rcases ph_bin u c hc X Y with h | h | h | h
  · exact ⟨_, hX, _, hY, Or.inl h⟩
  · exact ⟨_, hX, _, hY, Or.inr (Or.inl h)⟩
  · exact ⟨_, hX, _, hY, Or.inr (Or.inr h)⟩
  · exact ⟨_, hY, _, hX, Or.inr (Or.inr h)⟩
theorem ph_pres {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (x y s : BF n)
    (hs : s = fAnd x y ∨ s = fOr x y ∨ s = fDiff x y) (L : List (BF n)) (hX : ph u x ∈ L)
    (hY : ph u y ∈ L) : Cand fAnd fOr fDiff L (ph u s) := by
  rcases hs with rfl | rfl | rfl
  · exact ph_cand u and (Or.inl rfl) x y L hX hY
  · exact ph_cand u or (Or.inr (Or.inl rfl)) x y L hX hY
  · exact ph_cand u bDiff (Or.inr (Or.inr rfl)) x y L hX hY
theorem nz_F {n : ℕ} : nz (fF n) = fF n := rfl
theorem nz_T {n : ℕ} : nz (fT n) = fF n := rfl
theorem nz_not {n : ℕ} (w : BF n) : nz (fNot w) = nz w := by
  funext z
  show xor (!(w z)) (!(w (x0 n))) = xor (w z) (w (x0 n))
  cases w z <;> cases w (x0 n) <;> rfl
def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false
def cnt : List Gate → ℕ
  | [] => 0
  | g :: gs => cond (isNot g.op) (cnt gs) (cnt gs + 1)
theorem cnt_le : ∀ gs : List Gate, cnt gs ≤ gs.length := by
  intro gs
  induction gs with
  | nil => exact Nat.le_refl _
  | cons g gs ih =>
    show cond (isNot g.op) (cnt gs) (cnt gs + 1) ≤ gs.length + 1
    cases isNot g.op
    · exact Nat.succ_le_succ ih
    · exact Nat.le_succ_of_le ih
theorem cnt_lt : ∀ gs : List Gate, (∃ g ∈ gs, g.op = GateOp.not) → cnt gs + 1 ≤ gs.length := by
  intro gs
  induction gs with
  | nil => rintro ⟨g, hg, _⟩; exact absurd hg List.not_mem_nil
  | cons g gs ih =>
    rintro ⟨g', hg', hn⟩
    show cond (isNot g.op) (cnt gs) (cnt gs + 1) + 1 ≤ gs.length + 1
    rcases List.mem_cons.mp hg' with rfl | hg'
    · rw [hn]
      exact Nat.succ_le_succ (cnt_le gs)
    · have := ih ⟨g', hg', hn⟩
      have h2 := cnt_le gs
      cases isNot g.op
      · exact Nat.succ_le_succ this
      · exact Nat.succ_le_succ h2
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wf {n : ℕ} (W : List (BF n)) (i : ℕ) : BF n := fun x => (W.map (fun w => w x)).getD i false
def gf {n : ℕ} (W : List (BF n)) (g : Gate) : BF n :=
  fun x => g.op.eval (g.inputs.map fun i => (W.map (fun w => w x)).getD i false)
theorem wf_mem {n : ℕ} {W L : List (BF n)} (hF : fF n ∈ L) (hW : ∀ w ∈ W, nz w ∈ L) (i : ℕ) :
    nz (wf W i) ∈ L := by
  by_cases h : i < W.length
  · have e : wf W i = W[i] := by
      funext x
      simp [wf, List.getD_eq_getElem?_getD, h]
    rw [e]
    exact hW _ (List.getElem_mem h)
  · have e : wf W i = fF n := by
      funext x
      have : W.length ≤ i := not_lt.mp h
      simp [wf, fF, List.getD_eq_getElem?_getD, this]
    rw [e]
    exact hF
theorem gf_step {n : ℕ} {W L : List (BF n)} (hF : fF n ∈ L) (hW : ∀ w ∈ W, nz w ∈ L)
    (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    nz (gf W g) ∈ L ∨ (isNot g.op = false ∧ Cand fAnd fOr fDiff L (nz (gf W g))) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  have hm := fun i => wf_mem hF hW i
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · left
    rcases hop with rfl | rfl | rfl
    · have e : gf W ⟨GateOp.and, []⟩ = fT n := by funext x; simp [gf, GateOp.eval, fT]
      rw [e]; exact hF
    · have e : gf W ⟨GateOp.or, []⟩ = fF n := by funext x; simp [gf, GateOp.eval, fF]
      rw [e]; exact hF
    · have e : gf W ⟨GateOp.not, []⟩ = fT n := by funext x; simp [gf, GateOp.eval, fT]
      rw [e]; exact hF
  · left
    rcases hop with rfl | rfl | rfl
    · have e : gf W ⟨GateOp.and, [a]⟩ = wf W a := by funext x; simp [gf, GateOp.eval, wf]
      rw [e]; exact hm a
    · have e : gf W ⟨GateOp.or, [a]⟩ = wf W a := by funext x; simp [gf, GateOp.eval, wf]
      rw [e]; exact hm a
    · have e : gf W ⟨GateOp.not, [a]⟩ = fNot (wf W a) := by
        funext x; simp [gf, GateOp.eval, wf, fNot]
      rw [e, nz_not]; exact hm a
  · rcases hop with rfl | rfl | rfl
    · right
      have e : gf W ⟨GateOp.and, [a, b]⟩ = fBin and (wf W a) (wf W b) := by
        funext x; simp [gf, GateOp.eval, wf, fBin]
      rw [e]
      exact ⟨rfl, ph_cand id and (Or.inl rfl) _ _ L (hm a) (hm b)⟩
    · right
      have e : gf W ⟨GateOp.or, [a, b]⟩ = fBin or (wf W a) (wf W b) := by
        funext x; simp [gf, GateOp.eval, wf, fBin]
      rw [e]
      exact ⟨rfl, ph_cand id or (Or.inr (Or.inl rfl)) _ _ L (hm a) (hm b)⟩
    · left
      have e : gf W ⟨GateOp.not, [a, b]⟩ = fNot (wf W a) := by
        funext x; simp [gf, GateOp.eval, wf, fNot]
      rw [e, nz_not]; exact hm a
  · simp at hlen
theorem prog_of_gates {n : ℕ} : ∀ (gs : List Gate) (W L : List (BF n)), fF n ∈ L →
    (∀ w ∈ W, nz w ∈ L) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    ∀ o : ℕ, R (nz (fun x => (gs.foldl stepW (W.map (fun w => w x))).getD o false))
      (cnt gs) L := by
  intro gs
  induction gs with
  | nil =>
    intro W L hF hW _ o
    exact wf_mem hF hW o
  | cons g gs ih =>
    intro W L hF hW hg o
    have e : (fun x : Fin n → Bool =>
          ((g :: gs).foldl stepW (W.map (fun w => w x))).getD o false)
        = (fun x => (gs.foldl stepW ((W ++ [gf W g]).map (fun w => w x))).getD o false) := by
      funext x
      simp [stepW, gf]
    rw [e]
    have hg' := fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')
    show R _ (cond (isNot g.op) (cnt gs) (cnt gs + 1)) L
    rcases gf_step hF hW g (hg g List.mem_cons_self) with hin | ⟨hn, hc⟩
    · have h := ih (W ++ [gf W g]) L hF (by
        intro w hw
        rcases List.mem_append.mp hw with h | h
        · exact hW w h
        · simp only [List.mem_singleton] at h
          rw [h]; exact hin) hg' o
      cases isNot g.op
      · exact Reach.monoK fAnd fOr fDiff _ _ h
      · exact h
    · rw [hn]
      refine Or.inr ⟨nz (gf W g), hc, ?_⟩
      refine ih (W ++ [gf W g]) (nz (gf W g) :: L) (List.mem_cons_of_mem _ hF) ?_ hg' o
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_cons_of_mem _ (hW w h)
      · simp only [List.mem_singleton] at h
        rw [h]; exact List.mem_cons_self
theorem prog_of_gatelist {n : ℕ} (f : BF n) (gates : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) :
    R (nz f) (cnt gates) (L0 n) := by
  have e : f = (fun x => (gates.foldl stepW
      ((List.ofFn (fun p : Fin n => fV p)).map (fun w => w x))).getD o false) := by
    funext x
    rw [← he x]
    have e2 : (List.ofFn (fun p : Fin n => fV p)).map (fun w => w x) = List.ofFn x := by
      rw [List.map_ofFn]; rfl
    rw [e2]
    rfl
  rw [e]
  refine prog_of_gates gates _ (L0 n) List.mem_cons_self ?_ hok o
  intro w hw
  obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hw
  have e3 : nz (fV q) = fV q := by
    funext z
    show xor (z q) false = z q
    cases z q <;> rfl
  rw [e3]
  exact List.mem_cons_of_mem _ ((List.mem_ofFn' _ _).mpr ⟨q, rfl⟩)
def upd {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = p then b else x i
def rho {n : ℕ} (p : Fin n) (b : Bool) (g : BF n) : BF n := fun x => g (upd p b x)
abbrev phi {n : ℕ} (p : Fin n) (b : Bool) (g : BF n) : BF n := ph (upd p b) g
def Fix {n : ℕ} (p : Fin n) (g : BF n) : Prop := (∀ b, rho p b g = g) ∧ g (x0 n) = false
def Good {n : ℕ} (p : Fin n) (L : List (BF n)) : Prop :=
  fF n ∈ L ∧ ∀ g ∈ L, g = fV p ∨ Fix p g
theorem fix_phi {n : ℕ} {p : Fin n} {g : BF n} (h : Fix p g) (b : Bool) : phi p b g = g := by
  funext z
  have h1 := congrFun (h.1 b) z
  have h2 := congrFun (h.1 b) (x0 n)
  simp only [rho] at h1 h2
  show xor (g (upd p b z)) (g (upd p b (x0 n))) = g z
  rw [h1, h2, h.2]
  cases g z <;> rfl
theorem upd_self {n : ℕ} (p : Fin n) (b : Bool) (w : Fin n → Bool) : upd p b w p = b := by
  simp [upd]
theorem phi_var {n : ℕ} (p : Fin n) (b : Bool) : phi p b (fV p) = fF n := by
  funext z
  show xor (upd p b z p) (upd p b (x0 n) p) = false
  rw [upd_self, upd_self]
  cases b <;> rfl
theorem fix_bin {n : ℕ} {p : Fin n} (c : Bool → Bool → Bool) (hc0 : c false false = false)
    {x y : BF n} (hx : Fix p x) (hy : Fix p y) : Fix p (fBin c x y) := by
  refine ⟨fun b => ?_, ?_⟩
  · show fBin c (rho p b x) (rho p b y) = _
    rw [hx.1 b, hy.1 b]
  · show c (x (x0 n)) (y (x0 n)) = false
    rw [hx.2, hy.2, hc0]
theorem xor_false_eq (a b : Bool) (h : xor a b = false) : a = b := by
  revert h; cases a <;> cases b <;> decide
theorem un_const (g : Bool → Bool) (h : g true = g false) (a b : Bool) :
    xor (g a) (g b) = false := by
  cases a <;> cases b <;> simp [h]
theorem un_inj (g : Bool → Bool) (h : ¬ g true = g false) (a b : Bool) :
    xor (g a) (g b) = xor a b := by
  cases a <;> cases b <;> revert h <;> cases g true <;> cases g false <;> decide
theorem absorb_l {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (X Y : BF n) (h : ph u X = fF n) :
    ph u (fBin c X Y) = fF n ∨ ph u (fBin c X Y) = ph u Y := by
  have hX : ∀ z, X (u z) = X (u (x0 n)) := fun z => xor_false_eq _ _ (congrFun h z)
  by_cases hcc : c (X (u (x0 n))) true = c (X (u (x0 n))) false
  · left
    funext z
    show xor (c (X (u z)) (Y (u z))) (c (X (u (x0 n))) (Y (u (x0 n)))) = false
    rw [hX z]
    exact un_const (c (X (u (x0 n)))) hcc _ _
  · right
    funext z
    show xor (c (X (u z)) (Y (u z))) (c (X (u (x0 n))) (Y (u (x0 n))))
      = xor (Y (u z)) (Y (u (x0 n)))
    rw [hX z]
    exact un_inj (c (X (u (x0 n)))) hcc _ _
theorem absorb_r {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (X Y : BF n) (h : ph u Y = fF n) :
    ph u (fBin c X Y) = fF n ∨ ph u (fBin c X Y) = ph u X :=
  absorb_l u (fun a b => c b a) Y X h
theorem Good.cons {n : ℕ} {p : Fin n} {L : List (BF n)} (h : Good p L) {t : BF n}
    (ht : Fix p t) : Good p (t :: L) := by
  obtain ⟨h2, h3⟩ := h
  refine ⟨List.mem_cons_of_mem _ h2, ?_⟩
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inr ht
  · exact h3 g hg
theorem phase2 {n : ℕ} (p : Fin n) (b : Bool) (f : BF n) (h1 : phi p b f ≠ fF n)
    (h3 : ¬ ∀ b, rho p b f = f) : ∀ (k : ℕ) (L : List (BF n)) (s : BF n),
    Good p L → phi p b s = fF n → R f k (s :: L) →
    ∃ k', k = k' + 1 ∧ R (phi p b f) k' L := by
  have hmemF : ∀ (L : List (BF n)) (s : BF n), Good p L → phi p b s = fF n →
      f ∈ s :: L → False := by
    intro L s hG hs hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h1 hs
    · rcases hG.2 f hf with rfl | h
      · exact h1 (phi_var p b)
      · exact h3 h.1
  intro k
  induction k with
  | zero => intro L s hG hs hr; exact (hmemF L s hG hs hr).elim
  | succ k ih =>
    intro L s hG hs hr
    rcases hr with hr | ⟨t, ⟨x, hx, y, hy, ht⟩, hr⟩
    · exact (hmemF L s hG hs hr).elim
    · obtain ⟨hGF, hGall⟩ := hG
      have cls : ∀ z ∈ s :: L, phi p b z = fF n ∨ (z ∈ L ∧ Fix p z) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl hs
        · rcases hGall z hz with rfl | h
          · exact Or.inl (phi_var p b)
          · exact Or.inr ⟨hz, h⟩
      have rmem : ∀ z ∈ s :: L, phi p b z ∈ L := by
        intro z hz
        rcases cls z hz with h | ⟨h, hi⟩
        · rw [h]; exact hGF
        · rw [fix_phi hi b]; exact h
      have red : phi p b t ∈ L → ∃ k', k + 1 = k' + 1 ∧ R (phi p b f) k' L := by
        intro htL
        refine ⟨k, rfl, ?_⟩
        have hm := Reach.map fAnd fOr fDiff fAnd fOr fDiff (phi p b) (ph_pres (upd p b)) k _ hr
        refine Reach.monoL fAnd fOr fDiff _ _ _ ?_ hm
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        rcases List.mem_cons.mp hw with rfl | hw
        · exact htL
        · exact rmem w hw
      have keep : Cand fAnd fOr fDiff L t → Fix p t →
          ∃ k', k + 1 = k' + 1 ∧ R (phi p b f) k' L := by
        intro hc hi
        have hr' : R f k (s :: t :: L) := by
          refine Reach.monoL fAnd fOr fDiff _ _ _ ?_ hr
          intro z hz
          simp only [List.mem_cons] at hz ⊢
          tauto
        obtain ⟨k', rfl, h⟩ := ih (t :: L) s (Good.cons ⟨hGF, hGall⟩ hi) hs hr'
        exact ⟨k' + 1, rfl, Or.inr ⟨t, hc, h⟩⟩
      have main : ∀ c : Bool → Bool → Bool, c false false = false → t = fBin c x y →
          (x ∈ L → y ∈ L → Cand fAnd fOr fDiff L t) →
          ∃ k', k + 1 = k' + 1 ∧ R (phi p b f) k' L := by
        intro c hc0 e hcand
        rcases cls x hx with hxc | ⟨hxL, hxi⟩
        · apply red
          rw [e]
          show ph (upd p b) (fBin c x y) ∈ L
          rcases (absorb_l (upd p b) c x y hxc :
              phi p b (fBin c x y) = fF n ∨ phi p b (fBin c x y) = phi p b y) with h | h
          · rw [h]; exact hGF
          · rw [h]; exact rmem y hy
        · rcases cls y hy with hyc | ⟨hyL, hyi⟩
          · apply red
            rw [e]
            show ph (upd p b) (fBin c x y) ∈ L
            rcases (absorb_r (upd p b) c x y hyc :
                phi p b (fBin c x y) = fF n ∨ phi p b (fBin c x y) = phi p b x) with h | h
            · rw [h]; exact hGF
            · rw [h]; exact rmem x hx
          · exact keep (hcand hxL hyL) (e ▸ fix_bin c hc0 hxi hyi)
      rcases ht with e | e | e
      · exact main and rfl e (fun a b => ⟨x, a, y, b, Or.inl e⟩)
      · exact main or rfl e (fun a b => ⟨x, a, y, b, Or.inr (Or.inl e)⟩)
      · exact main bDiff rfl e (fun a b => ⟨x, a, y, b, Or.inr (Or.inr e)⟩)
theorem one_gate {n : ℕ} (p : Fin n) (b : Bool) (f : BF n) (h1 : phi p b f ≠ fF n)
    (h3 : ¬ ∀ b, rho p b f = f) (k : ℕ) (L : List (BF n)) (hG : Good p L)
    (hr : R f k L) : ∃ k', k = k' + 1 ∧ R (phi p b f) k' L := by
  refine phase2 p b f h1 h3 k L (fF n) hG rfl ?_
  exact Reach.monoL fAnd fOr fDiff _ _ _ (fun x hx => List.mem_cons_of_mem _ hx) hr
theorem kill_l {n : ℕ} (p : Fin n) (b : Bool) (c : Bool → Bool → Bool)
    (hc : c b true = c b false) (y : BF n) : phi p b (fBin c (fV p) y) = fF n := by
  funext z
  show xor (c (upd p b z p) (y (upd p b z))) (c (upd p b (x0 n) p) (y (upd p b (x0 n)))) = false
  rw [upd_self, upd_self]
  exact un_const (c b) hc _ _
theorem kill_r {n : ℕ} (p : Fin n) (b : Bool) (c : Bool → Bool → Bool)
    (hc : c true b = c false b) (y : BF n) : phi p b (fBin c y (fV p)) = fF n :=
  kill_l p b (fun a d => c d a) hc y
theorem two_gates {n : ℕ} (p : Fin n) (f : BF n) (h0 : phi p false f ≠ fF n)
    (h1 : phi p true f ≠ fF n) (h3 : ¬ ∀ b, rho p b f = f) :
    ∀ (k : ℕ) (L : List (BF n)), Good p L → R f k L →
    ∃ k', k = k' + 2 ∧ (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
  have hmemF : ∀ (L : List (BF n)), Good p L → f ∈ L → False := by
    intro L hG hf
    rcases hG.2 f hf with rfl | h
    · exact h0 (phi_var p false)
    · exact h3 h.1
  intro k
  induction k with
  | zero => intro L hG hr; exact (hmemF L hG hr).elim
  | succ k ih =>
    intro L hG hr
    rcases hr with hr | ⟨t, ⟨x, hx, y, hy, ht⟩, hr⟩
    · exact (hmemF L hG hr).elim
    · have keep : Fix p t → ∃ k', k + 1 = k' + 2 ∧
          (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
        intro hi
        obtain ⟨k', rfl, h⟩ := ih (t :: L) (Good.cons hG hi) hr
        refine ⟨k' + 1, rfl, ?_⟩
        rcases h with h | h
        · exact Or.inl (Or.inr ⟨t, ⟨x, hx, y, hy, ht⟩, h⟩)
        · exact Or.inr (Or.inr ⟨t, ⟨x, hx, y, hy, ht⟩, h⟩)
      have kill : ∀ b : Bool, phi p b t = fF n → ∃ k', k + 1 = k' + 2 ∧
          (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
        intro b hc
        cases b
        · obtain ⟨k', rfl, h⟩ := phase2 p false f h0 h3 k L t hG hc hr
          exact ⟨k', rfl, Or.inl h⟩
        · obtain ⟨k', rfl, h⟩ := phase2 p true f h1 h3 k L t hG hc hr
          exact ⟨k', rfl, Or.inr h⟩
      have main : ∀ (c : Bool → Bool → Bool) (bl br : Bool), c false false = false →
          c bl true = c bl false → c true br = c false br → t = fBin c x y →
          ∃ k', k + 1 = k' + 2 ∧ (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
        intro c bl br hc0 hl hrr e
        rcases hG.2 x hx with rfl | hxi
        · exact kill bl (by rw [e]; exact kill_l p bl c hl y)
        · rcases hG.2 y hy with rfl | hyi
          · exact kill br (by rw [e]; exact kill_r p br c hrr x)
          · exact keep (e ▸ fix_bin c hc0 hxi hyi)
      rcases ht with e | e | e
      · exact main and false false rfl rfl rfl e
      · exact main or true true rfl rfl rfl e
      · exact main bDiff false true rfl rfl rfl e
theorem good_L0 {n : ℕ} (p : Fin n) : Good p (L0 n) := by
  refine ⟨List.mem_cons_self, ?_⟩
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inr ⟨fun _ => rfl, rfl⟩
  obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hg
  by_cases hq : q = p
  · exact Or.inl (by rw [hq])
  · refine Or.inr ⟨fun b => ?_, rfl⟩
    funext z
    simp [rho, upd, fV, hq]
theorem ne_F {n : ℕ} (g : BF n) (x : Fin n → Bool) (h : g x = true) : g ≠ fF n := by
  intro e; rw [e] at h; exact Bool.noConfusion h
theorem reads {n : ℕ} (p : Fin n) (g : BF n) (x : Fin n → Bool)
    (h : (rho p false g x != rho p true g x) = true) : ¬ ∀ b, rho p b g = g := by
  intro hi
  rw [hi false, hi true] at h
  simp at h
def pt {n : ℕ} (m : ℕ) : Fin n → Bool := fun i => Nat.testBit m i.val
theorem all_pts {n : ℕ} (P : (Fin n → Bool) → Prop) (h : ∀ m < 2 ^ n, P (pt m)) :
    ∀ x : Fin n → Bool, P x := by
  intro x
  have e : x = pt (Nat.ofBits x) := by
    funext i
    exact (Nat.testBit_ofBits_lt x i.val i.isLt).symm
  rw [e]
  exact h _ (Nat.ofBits_lt_two_pow x)
theorem not_shape {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ)
    (hWm : ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWl : Wg.length ≤ B + 1)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x)
    (gates : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = f x := by
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have h1 := hB _ (prog_of_gatelist f gates o hok he)
    have h2 := cnt_lt gates hn
    exact ⟨Wg, wo, hWm, by omega, hWe⟩
  · refine ⟨gates, o, ?_, Nat.le_refl _, he⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hok g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hn
def monoOK (g : Gate) : Bool :=
  (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length ≤ 2)
theorem monoOK_sound (Wg : List Gate) (h : Wg.all monoOK = true) :
    ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  obtain ⟨op, ins⟩ := g
  unfold monoOK at h1
  rw [Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨?_, of_decide_eq_true h3⟩
  cases op <;> simp at h2 ⊢
theorem mono_shape2 {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ)
    (hWm : ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWl : Wg.length ≤ B + 1)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x) :
    ∀ s : ℕ, HasCircuitSize n f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  rintro s ⟨⟨gates, o⟩, hC, hs, he⟩
  have hok : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  obtain ⟨g2, o2, hm, hl, he2⟩ := not_shape f B hB Wg wo hWm hWl hWe gates o hok he
  have hs2 : gates.length ≤ s := hs
  refine ⟨⟨g2, o2⟩, ?_, le_trans hl hs2, he2⟩
  intro g hg
  obtain ⟨h2, h3⟩ := hm g hg
  refine ⟨?_, h3⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h2

namespace Signed
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra fail
  have ha : ¬ differs i a := fun h => fail (.inl h)
  have hb : ¬ differs i b := fun h => fail (.inr h)
  apply hd
  unfold differs at ha hb
  have ha' : a.getLsbD (64 + i.val) = a.getLsbD i.val := Classical.byContradiction ha
  have hb' : b.getLsbD (64 + i.val) = b.getLsbD i.val := Classical.byContradiction hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha', hb']

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  grind

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchOp (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W)
    (base : BitVec 64) (w : W) : Bool :=
  if w ∈ a :: b :: r then false else
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any (dispatchOp extra next a b r base)

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hnew : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp only [dispatchOp, hnew, ite_false]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have fresh : z ∉ a :: b :: r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop fresh hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

end Signed

namespace CoreLeaf

open Signed

def packed {n : ℕ} (e : Fin 128 → Fin n → Bool) (g : BF n) : W := BitVec.ofNat 128 (Nat.ofBits (fun k => g (e k)))

theorem packedBit {n : ℕ} (e : Fin 128 → Fin n → Bool) (g : BF n) (i : ℕ) (hi : i < 128) :
    (packed e g)[i] = g (e ⟨i,hi⟩) := by
  rw [← BitVec.getLsbD_eq_getElem hi, packed, BitVec.getLsbD_ofNat]
  simp [hi, Nat.testBit_ofBits_lt _ _ hi]

theorem packAnd {n : ℕ} (e : Fin 128 → Fin n → Bool) (g h : BF n) :
    packed e (fAnd g h) = packed e g &&& packed e h := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, packedBit, fAnd, fBin]

theorem packOr {n : ℕ} (e : Fin 128 → Fin n → Bool) (g h : BF n) :
    packed e (fOr g h) = packed e g ||| packed e h := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, packedBit, fOr, fBin]

theorem packDiff {n : ℕ} (e : Fin 128 → Fin n → Bool) (g h : BF n) :
    packed e (fDiff g h) = packed e g &&& ~~~(packed e h) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, packedBit, fDiff, fBin, bDiff]

theorem buildUp {a b : ℕ} {u : W} {av : Finset W} (h : a ≤ b) (h0 : build basicOps u a av) : build basicOps u b av := by
  induction h with
  | refl => exact h0
  | step _ ih => exact Or.inl ih

theorem mapped {n : ℕ} (e : Fin 128 → Fin n → Bool) (f : BF n) (ef : packed e f = goal) :
    ∀ k L av, (∀ v ∈ L, holds av (packed e v)) → R f k L →
      ∃ u, (u = goal ∨ u = ~~~goal) ∧ build basicOps u k av := by
  have finish (k : ℕ) (av : Finset W) (h : holds av goal) :
      ∃ u, (u = goal ∨ u = ~~~goal) ∧ build basicOps u k av := by
    rcases h with ez | eo | ⟨u, hu, eu | eu⟩
    · exact False.elim ((by decide : goal ≠ 0) ez)
    · exact False.elim ((by decide : goal ≠ ~~~(0 : W)) eo)
    · exact ⟨u, Or.inl eu.symm, buildUp (Nat.zero_le k) (show build basicOps u 0 av from hu)⟩
    · have eq : u = ~~~goal := by rw [eu, BitVec.not_not]
      exact ⟨u, Or.inr eq, buildUp (Nat.zero_le k) (show build basicOps u 0 av from hu)⟩
  intro k
  induction k with
  | zero => intro L av h hr; exact finish _ _ (ef ▸ h f hr)
  | succ k ih =>
    intro L av h hr
    rcases hr with hm | ⟨s, ⟨a, ha, b, hb, hs⟩, tail⟩
    · exact finish _ _ (ef ▸ h f hm)
    · have hc : reachable av (packed e s) := by
        rcases hs with rfl | rfl | rfl
        · rw [packAnd]; exact and_reach (h a ha) (h b hb)
        · rw [packOr]; exact or_reach (h a ha) (h b hb)
        · rw [packDiff]; exact and_reach (h a ha) (holds_not (h b hb))
      rcases hc with h0 | ⟨u,hu,v,hv,ne,z,hz,hnew⟩
      · obtain ⟨w, hw, hp⟩ := ih (s :: L) av (by
          intro x hx; rcases List.mem_cons.mp hx with rfl | hh
          · exact h0
          · exact h x hh) tail
        exact ⟨w,hw,Or.inl hp⟩
      · obtain ⟨w, hw, hp⟩ := ih (s :: L) (insert z av) (by
          intro x hx; rcases List.mem_cons.mp hx with rfl | hh
          · exact hnew
          · exact holds_insert (h x hh)) tail
        exact ⟨w,hw,Or.inr ⟨u,hu,v,hv,ne,z,hz,hp⟩⟩

theorem lower {n : ℕ} (e : Fin 128 → Fin n → Bool) (f : BF n) (rows : List W) (k : ℕ)
    (ef : packed e f = goal) (empty : packed e (fF n) = 0)
    (rawCells : ∀ i : Fin n, packed e (fV i) = 0 ∨ packed e (fV i) ∈ rows)
    (nd : rows.Nodup) (reject : search k rows = false) :
    ∀ j, R f j (L0 n) → k+1 ≤ j := by
  intro j hj
  by_contra! hsmall
  have avail : ∀ v ∈ L0 n, holds rows.toFinset (packed e v) := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl empty
    · obtain ⟨i,rfl⟩ := (List.mem_ofFn' _ _).mp hv
      rcases rawCells i with hz | hm
      · exact Or.inl hz
      · exact Or.inr (Or.inr ⟨_,List.mem_toFinset.mpr hm,Or.inl rfl⟩)
  obtain ⟨u, hu, h⟩ := mapped e f ef j _ _ avail hj
  have h' := search_complete hu k rows nd (buildUp (by omega) h)
  simp [reject] at h'

end CoreLeaf



def spec : BF 6 := fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008241664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def tab : BF 6 := fun x => (17215830811738696192 : ℕ).testBit (Nat.ofBits x)

theorem sameTable : spec = tab := funext (all_pts (fun x => spec x = tab x) (by decide +kernel))

def raw0_0 : Signed.W := BitVec.ofNat 128 ((7908141450299680671 : ℕ) * 2^64 + 2274067392143524255)

def raw0_1 : Signed.W := BitVec.ofNat 128 ((13183931442769223142 : ℕ) * 2^64 + 2301374322035138022)

def raw0_2 : Signed.W := BitVec.ofNat 128 ((15816353083873126904 : ℕ) * 2^64 + 2305807828169810424)

def raw0_3 : Signed.W := BitVec.ofNat 128 ((16418767886418607787 : ℕ) * 2^64 + 16140901064621719040)

def raw0_4 : Signed.W := BitVec.ofNat 128 ((2048244724887687508 : ℕ) * 2^64 + 4429152256)

def rows0 : List Signed.W := [raw0_0, raw0_1, raw0_2, raw0_3, raw0_4]

def obs0 (v : Fin 128) (j : Fin 6) : Bool := (([raw0_0, raw0_1, raw0_2, raw0_3, raw0_4, 0] : List Signed.W).getD j.val 0).getLsbD v.val

namespace Part0
open Signed

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op0 : dispatchOp 3 (optimized 6) raw0_0 raw0_1 [raw0_2, raw0_3, raw0_4] (cuts [raw0_2, raw0_3, raw0_4]) (raw0_0 &&& raw0_1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op1 : dispatchOp 3 (optimized 6) raw0_0 raw0_1 [raw0_2, raw0_3, raw0_4] (cuts [raw0_2, raw0_3, raw0_4]) (raw0_0 ||| raw0_1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op2 : dispatchOp 3 (optimized 6) raw0_0 raw0_1 [raw0_2, raw0_3, raw0_4] (cuts [raw0_2, raw0_3, raw0_4]) (raw0_0 &&& ~~~raw0_1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op3 : dispatchOp 3 (optimized 6) raw0_0 raw0_1 [raw0_2, raw0_3, raw0_4] (cuts [raw0_2, raw0_3, raw0_4]) (raw0_1 &&& ~~~raw0_0) = false := by
  decide +kernel

theorem pair01 : dispatch 3 (optimized 6) raw0_0 raw0_1 [raw0_2, raw0_3, raw0_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair01Op0, pair01Op1, pair01Op2, pair01Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op0 : dispatchOp 3 (optimized 6) raw0_0 raw0_2 [raw0_1, raw0_3, raw0_4] (cuts [raw0_1, raw0_3, raw0_4]) (raw0_0 &&& raw0_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op1 : dispatchOp 3 (optimized 6) raw0_0 raw0_2 [raw0_1, raw0_3, raw0_4] (cuts [raw0_1, raw0_3, raw0_4]) (raw0_0 ||| raw0_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op2 : dispatchOp 3 (optimized 6) raw0_0 raw0_2 [raw0_1, raw0_3, raw0_4] (cuts [raw0_1, raw0_3, raw0_4]) (raw0_0 &&& ~~~raw0_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op3 : dispatchOp 3 (optimized 6) raw0_0 raw0_2 [raw0_1, raw0_3, raw0_4] (cuts [raw0_1, raw0_3, raw0_4]) (raw0_2 &&& ~~~raw0_0) = false := by
  decide +kernel

theorem pair02 : dispatch 3 (optimized 6) raw0_0 raw0_2 [raw0_1, raw0_3, raw0_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair02Op0, pair02Op1, pair02Op2, pair02Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op0 : dispatchOp 3 (optimized 6) raw0_0 raw0_3 [raw0_1, raw0_2, raw0_4] (cuts [raw0_1, raw0_2, raw0_4]) (raw0_0 &&& raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op1 : dispatchOp 3 (optimized 6) raw0_0 raw0_3 [raw0_1, raw0_2, raw0_4] (cuts [raw0_1, raw0_2, raw0_4]) (raw0_0 ||| raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op2 : dispatchOp 3 (optimized 6) raw0_0 raw0_3 [raw0_1, raw0_2, raw0_4] (cuts [raw0_1, raw0_2, raw0_4]) (raw0_0 &&& ~~~raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op3 : dispatchOp 3 (optimized 6) raw0_0 raw0_3 [raw0_1, raw0_2, raw0_4] (cuts [raw0_1, raw0_2, raw0_4]) (raw0_3 &&& ~~~raw0_0) = false := by
  decide +kernel

theorem pair03 : dispatch 3 (optimized 6) raw0_0 raw0_3 [raw0_1, raw0_2, raw0_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair03Op0, pair03Op1, pair03Op2, pair03Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op0 : dispatchOp 3 (optimized 6) raw0_0 raw0_4 [raw0_1, raw0_2, raw0_3] (cuts [raw0_1, raw0_2, raw0_3]) (raw0_0 &&& raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op1 : dispatchOp 3 (optimized 6) raw0_0 raw0_4 [raw0_1, raw0_2, raw0_3] (cuts [raw0_1, raw0_2, raw0_3]) (raw0_0 ||| raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op2 : dispatchOp 3 (optimized 6) raw0_0 raw0_4 [raw0_1, raw0_2, raw0_3] (cuts [raw0_1, raw0_2, raw0_3]) (raw0_0 &&& ~~~raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op3 : dispatchOp 3 (optimized 6) raw0_0 raw0_4 [raw0_1, raw0_2, raw0_3] (cuts [raw0_1, raw0_2, raw0_3]) (raw0_4 &&& ~~~raw0_0) = false := by
  decide +kernel

theorem pair04 : dispatch 3 (optimized 6) raw0_0 raw0_4 [raw0_1, raw0_2, raw0_3] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair04Op0, pair04Op1, pair04Op2, pair04Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op0 : dispatchOp 3 (optimized 6) raw0_1 raw0_2 [raw0_0, raw0_3, raw0_4] (cuts [raw0_0, raw0_3, raw0_4]) (raw0_1 &&& raw0_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op1 : dispatchOp 3 (optimized 6) raw0_1 raw0_2 [raw0_0, raw0_3, raw0_4] (cuts [raw0_0, raw0_3, raw0_4]) (raw0_1 ||| raw0_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op2 : dispatchOp 3 (optimized 6) raw0_1 raw0_2 [raw0_0, raw0_3, raw0_4] (cuts [raw0_0, raw0_3, raw0_4]) (raw0_1 &&& ~~~raw0_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op3 : dispatchOp 3 (optimized 6) raw0_1 raw0_2 [raw0_0, raw0_3, raw0_4] (cuts [raw0_0, raw0_3, raw0_4]) (raw0_2 &&& ~~~raw0_1) = false := by
  decide +kernel

theorem pair12 : dispatch 3 (optimized 6) raw0_1 raw0_2 [raw0_0, raw0_3, raw0_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair12Op0, pair12Op1, pair12Op2, pair12Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op0 : dispatchOp 3 (optimized 6) raw0_1 raw0_3 [raw0_0, raw0_2, raw0_4] (cuts [raw0_0, raw0_2, raw0_4]) (raw0_1 &&& raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op1 : dispatchOp 3 (optimized 6) raw0_1 raw0_3 [raw0_0, raw0_2, raw0_4] (cuts [raw0_0, raw0_2, raw0_4]) (raw0_1 ||| raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op2 : dispatchOp 3 (optimized 6) raw0_1 raw0_3 [raw0_0, raw0_2, raw0_4] (cuts [raw0_0, raw0_2, raw0_4]) (raw0_1 &&& ~~~raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op3 : dispatchOp 3 (optimized 6) raw0_1 raw0_3 [raw0_0, raw0_2, raw0_4] (cuts [raw0_0, raw0_2, raw0_4]) (raw0_3 &&& ~~~raw0_1) = false := by
  decide +kernel

theorem pair13 : dispatch 3 (optimized 6) raw0_1 raw0_3 [raw0_0, raw0_2, raw0_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair13Op0, pair13Op1, pair13Op2, pair13Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op0 : dispatchOp 3 (optimized 6) raw0_1 raw0_4 [raw0_0, raw0_2, raw0_3] (cuts [raw0_0, raw0_2, raw0_3]) (raw0_1 &&& raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op1 : dispatchOp 3 (optimized 6) raw0_1 raw0_4 [raw0_0, raw0_2, raw0_3] (cuts [raw0_0, raw0_2, raw0_3]) (raw0_1 ||| raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op2 : dispatchOp 3 (optimized 6) raw0_1 raw0_4 [raw0_0, raw0_2, raw0_3] (cuts [raw0_0, raw0_2, raw0_3]) (raw0_1 &&& ~~~raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op3 : dispatchOp 3 (optimized 6) raw0_1 raw0_4 [raw0_0, raw0_2, raw0_3] (cuts [raw0_0, raw0_2, raw0_3]) (raw0_4 &&& ~~~raw0_1) = false := by
  decide +kernel

theorem pair14 : dispatch 3 (optimized 6) raw0_1 raw0_4 [raw0_0, raw0_2, raw0_3] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair14Op0, pair14Op1, pair14Op2, pair14Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op0 : dispatchOp 3 (optimized 6) raw0_2 raw0_3 [raw0_0, raw0_1, raw0_4] (cuts [raw0_0, raw0_1, raw0_4]) (raw0_2 &&& raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op1 : dispatchOp 3 (optimized 6) raw0_2 raw0_3 [raw0_0, raw0_1, raw0_4] (cuts [raw0_0, raw0_1, raw0_4]) (raw0_2 ||| raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op2 : dispatchOp 3 (optimized 6) raw0_2 raw0_3 [raw0_0, raw0_1, raw0_4] (cuts [raw0_0, raw0_1, raw0_4]) (raw0_2 &&& ~~~raw0_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op3 : dispatchOp 3 (optimized 6) raw0_2 raw0_3 [raw0_0, raw0_1, raw0_4] (cuts [raw0_0, raw0_1, raw0_4]) (raw0_3 &&& ~~~raw0_2) = false := by
  decide +kernel

theorem pair23 : dispatch 3 (optimized 6) raw0_2 raw0_3 [raw0_0, raw0_1, raw0_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair23Op0, pair23Op1, pair23Op2, pair23Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op0 : dispatchOp 3 (optimized 6) raw0_2 raw0_4 [raw0_0, raw0_1, raw0_3] (cuts [raw0_0, raw0_1, raw0_3]) (raw0_2 &&& raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op1 : dispatchOp 3 (optimized 6) raw0_2 raw0_4 [raw0_0, raw0_1, raw0_3] (cuts [raw0_0, raw0_1, raw0_3]) (raw0_2 ||| raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op2 : dispatchOp 3 (optimized 6) raw0_2 raw0_4 [raw0_0, raw0_1, raw0_3] (cuts [raw0_0, raw0_1, raw0_3]) (raw0_2 &&& ~~~raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op3 : dispatchOp 3 (optimized 6) raw0_2 raw0_4 [raw0_0, raw0_1, raw0_3] (cuts [raw0_0, raw0_1, raw0_3]) (raw0_4 &&& ~~~raw0_2) = false := by
  decide +kernel

theorem pair24 : dispatch 3 (optimized 6) raw0_2 raw0_4 [raw0_0, raw0_1, raw0_3] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair24Op0, pair24Op1, pair24Op2, pair24Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op0 : dispatchOp 3 (optimized 6) raw0_3 raw0_4 [raw0_0, raw0_1, raw0_2] (cuts [raw0_0, raw0_1, raw0_2]) (raw0_3 &&& raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op1 : dispatchOp 3 (optimized 6) raw0_3 raw0_4 [raw0_0, raw0_1, raw0_2] (cuts [raw0_0, raw0_1, raw0_2]) (raw0_3 ||| raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op2 : dispatchOp 3 (optimized 6) raw0_3 raw0_4 [raw0_0, raw0_1, raw0_2] (cuts [raw0_0, raw0_1, raw0_2]) (raw0_3 &&& ~~~raw0_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op3 : dispatchOp 3 (optimized 6) raw0_3 raw0_4 [raw0_0, raw0_1, raw0_2] (cuts [raw0_0, raw0_1, raw0_2]) (raw0_4 &&& ~~~raw0_3) = false := by
  decide +kernel

theorem pair34 : dispatch 3 (optimized 6) raw0_3 raw0_4 [raw0_0, raw0_1, raw0_2] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair34Op0, pair34Op1, pair34Op2, pair34Op3]
  rfl

theorem topPairs : pairs rows0 =
  [(raw0_0, raw0_1, [raw0_2, raw0_3, raw0_4]),
   (raw0_0, raw0_2, [raw0_1, raw0_3, raw0_4]),
   (raw0_0, raw0_3, [raw0_1, raw0_2, raw0_4]),
   (raw0_0, raw0_4, [raw0_1, raw0_2, raw0_3]),
   (raw0_1, raw0_2, [raw0_0, raw0_3, raw0_4]),
   (raw0_1, raw0_3, [raw0_0, raw0_2, raw0_4]),
   (raw0_1, raw0_4, [raw0_0, raw0_2, raw0_3]),
   (raw0_2, raw0_3, [raw0_0, raw0_1, raw0_4]),
   (raw0_2, raw0_4, [raw0_0, raw0_1, raw0_3]),
   (raw0_3, raw0_4, [raw0_0, raw0_1, raw0_2])] := rfl

theorem rootReject : optimized 7 3 rows0 = false := by
  rw [optimized, topPairs]
  rw [show (rows0 == [goal] || rows0 == [~~~goal]) = false by decide]
  simp only [List.any_cons, List.any_nil, pair01, pair02, pair03, pair04, pair12, pair13, pair14, pair23, pair24, pair34]
  rfl

theorem fullInput : ∀ ws ∈ rows0.sublists, cuts ws = -1 → ws = rows0 := by decide +kernel

theorem reject5 : search 7 rows0 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h' : (rows0.sublists.any fun ws =>
      decide (ws.length ≤ 7 + 1) && (cuts ws == -1) && optimized 7 (7 + 1 - ws.length) ws) = true := h
  obtain ⟨ws, hw, hok⟩ := List.any_eq_true.mp h'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hc⟩, good⟩ := hok
  obtain rfl := fullInput ws hw hc
  change optimized 7 3 rows0 = true at good
  rw [rootReject] at good
  exact Bool.noConfusion good

end Part0

theorem unseen0 : Signed.search 7 rows0 = false := Part0.reject5

theorem side0 : ∀ j, R (phi (5 : Fin 6) false (nz tab)) j (L0 6) → 8 ≤ j :=
  CoreLeaf.lower obs0 _ rows0 7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) unseen0

def raw1_0 : Signed.W := BitVec.ofNat 128 ((16910284323873411935 : ℕ) * 2^64 + 532609499151)

def raw1_1 : Signed.W := BitVec.ofNat 128 ((6185341783831719601 : ℕ) * 2^64 + 540466590370729520)

def raw1_2 : Signed.W := BitVec.ofNat 128 ((15932586118169310434 : ℕ) * 2^64 + 17871374037491134656)

def raw1_3 : Signed.W := BitVec.ofNat 128 ((16608381854255562500 : ℕ) * 2^64 + 18445618174556651264)

def raw1_4 : Signed.W := BitVec.ofNat 128 ((9539499712608978952 : ℕ) * 2^64 + 822067200)

def rows1 : List Signed.W := [raw1_0, raw1_1, raw1_2, raw1_3, raw1_4]

def obs1 (v : Fin 128) (j : Fin 6) : Bool := (([raw1_0, raw1_1, raw1_2, raw1_3, raw1_4, 0] : List Signed.W).getD j.val 0).getLsbD v.val

namespace Part1
open Signed

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op0 : dispatchOp 3 (optimized 6) raw1_0 raw1_1 [raw1_2, raw1_3, raw1_4] (cuts [raw1_2, raw1_3, raw1_4]) (raw1_0 &&& raw1_1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op1 : dispatchOp 3 (optimized 6) raw1_0 raw1_1 [raw1_2, raw1_3, raw1_4] (cuts [raw1_2, raw1_3, raw1_4]) (raw1_0 ||| raw1_1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op2 : dispatchOp 3 (optimized 6) raw1_0 raw1_1 [raw1_2, raw1_3, raw1_4] (cuts [raw1_2, raw1_3, raw1_4]) (raw1_0 &&& ~~~raw1_1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair01Op3 : dispatchOp 3 (optimized 6) raw1_0 raw1_1 [raw1_2, raw1_3, raw1_4] (cuts [raw1_2, raw1_3, raw1_4]) (raw1_1 &&& ~~~raw1_0) = false := by
  decide +kernel

theorem pair01 : dispatch 3 (optimized 6) raw1_0 raw1_1 [raw1_2, raw1_3, raw1_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair01Op0, pair01Op1, pair01Op2, pair01Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op0 : dispatchOp 3 (optimized 6) raw1_0 raw1_2 [raw1_1, raw1_3, raw1_4] (cuts [raw1_1, raw1_3, raw1_4]) (raw1_0 &&& raw1_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op1 : dispatchOp 3 (optimized 6) raw1_0 raw1_2 [raw1_1, raw1_3, raw1_4] (cuts [raw1_1, raw1_3, raw1_4]) (raw1_0 ||| raw1_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op2 : dispatchOp 3 (optimized 6) raw1_0 raw1_2 [raw1_1, raw1_3, raw1_4] (cuts [raw1_1, raw1_3, raw1_4]) (raw1_0 &&& ~~~raw1_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair02Op3 : dispatchOp 3 (optimized 6) raw1_0 raw1_2 [raw1_1, raw1_3, raw1_4] (cuts [raw1_1, raw1_3, raw1_4]) (raw1_2 &&& ~~~raw1_0) = false := by
  decide +kernel

theorem pair02 : dispatch 3 (optimized 6) raw1_0 raw1_2 [raw1_1, raw1_3, raw1_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair02Op0, pair02Op1, pair02Op2, pair02Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op0 : dispatchOp 3 (optimized 6) raw1_0 raw1_3 [raw1_1, raw1_2, raw1_4] (cuts [raw1_1, raw1_2, raw1_4]) (raw1_0 &&& raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op1 : dispatchOp 3 (optimized 6) raw1_0 raw1_3 [raw1_1, raw1_2, raw1_4] (cuts [raw1_1, raw1_2, raw1_4]) (raw1_0 ||| raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op2 : dispatchOp 3 (optimized 6) raw1_0 raw1_3 [raw1_1, raw1_2, raw1_4] (cuts [raw1_1, raw1_2, raw1_4]) (raw1_0 &&& ~~~raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair03Op3 : dispatchOp 3 (optimized 6) raw1_0 raw1_3 [raw1_1, raw1_2, raw1_4] (cuts [raw1_1, raw1_2, raw1_4]) (raw1_3 &&& ~~~raw1_0) = false := by
  decide +kernel

theorem pair03 : dispatch 3 (optimized 6) raw1_0 raw1_3 [raw1_1, raw1_2, raw1_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair03Op0, pair03Op1, pair03Op2, pair03Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op0 : dispatchOp 3 (optimized 6) raw1_0 raw1_4 [raw1_1, raw1_2, raw1_3] (cuts [raw1_1, raw1_2, raw1_3]) (raw1_0 &&& raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op1 : dispatchOp 3 (optimized 6) raw1_0 raw1_4 [raw1_1, raw1_2, raw1_3] (cuts [raw1_1, raw1_2, raw1_3]) (raw1_0 ||| raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op2 : dispatchOp 3 (optimized 6) raw1_0 raw1_4 [raw1_1, raw1_2, raw1_3] (cuts [raw1_1, raw1_2, raw1_3]) (raw1_0 &&& ~~~raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair04Op3 : dispatchOp 3 (optimized 6) raw1_0 raw1_4 [raw1_1, raw1_2, raw1_3] (cuts [raw1_1, raw1_2, raw1_3]) (raw1_4 &&& ~~~raw1_0) = false := by
  decide +kernel

theorem pair04 : dispatch 3 (optimized 6) raw1_0 raw1_4 [raw1_1, raw1_2, raw1_3] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair04Op0, pair04Op1, pair04Op2, pair04Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op0 : dispatchOp 3 (optimized 6) raw1_1 raw1_2 [raw1_0, raw1_3, raw1_4] (cuts [raw1_0, raw1_3, raw1_4]) (raw1_1 &&& raw1_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op1 : dispatchOp 3 (optimized 6) raw1_1 raw1_2 [raw1_0, raw1_3, raw1_4] (cuts [raw1_0, raw1_3, raw1_4]) (raw1_1 ||| raw1_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op2 : dispatchOp 3 (optimized 6) raw1_1 raw1_2 [raw1_0, raw1_3, raw1_4] (cuts [raw1_0, raw1_3, raw1_4]) (raw1_1 &&& ~~~raw1_2) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair12Op3 : dispatchOp 3 (optimized 6) raw1_1 raw1_2 [raw1_0, raw1_3, raw1_4] (cuts [raw1_0, raw1_3, raw1_4]) (raw1_2 &&& ~~~raw1_1) = false := by
  decide +kernel

theorem pair12 : dispatch 3 (optimized 6) raw1_1 raw1_2 [raw1_0, raw1_3, raw1_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair12Op0, pair12Op1, pair12Op2, pair12Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op0 : dispatchOp 3 (optimized 6) raw1_1 raw1_3 [raw1_0, raw1_2, raw1_4] (cuts [raw1_0, raw1_2, raw1_4]) (raw1_1 &&& raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op1 : dispatchOp 3 (optimized 6) raw1_1 raw1_3 [raw1_0, raw1_2, raw1_4] (cuts [raw1_0, raw1_2, raw1_4]) (raw1_1 ||| raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op2 : dispatchOp 3 (optimized 6) raw1_1 raw1_3 [raw1_0, raw1_2, raw1_4] (cuts [raw1_0, raw1_2, raw1_4]) (raw1_1 &&& ~~~raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair13Op3 : dispatchOp 3 (optimized 6) raw1_1 raw1_3 [raw1_0, raw1_2, raw1_4] (cuts [raw1_0, raw1_2, raw1_4]) (raw1_3 &&& ~~~raw1_1) = false := by
  decide +kernel

theorem pair13 : dispatch 3 (optimized 6) raw1_1 raw1_3 [raw1_0, raw1_2, raw1_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair13Op0, pair13Op1, pair13Op2, pair13Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op0 : dispatchOp 3 (optimized 6) raw1_1 raw1_4 [raw1_0, raw1_2, raw1_3] (cuts [raw1_0, raw1_2, raw1_3]) (raw1_1 &&& raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op1 : dispatchOp 3 (optimized 6) raw1_1 raw1_4 [raw1_0, raw1_2, raw1_3] (cuts [raw1_0, raw1_2, raw1_3]) (raw1_1 ||| raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op2 : dispatchOp 3 (optimized 6) raw1_1 raw1_4 [raw1_0, raw1_2, raw1_3] (cuts [raw1_0, raw1_2, raw1_3]) (raw1_1 &&& ~~~raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair14Op3 : dispatchOp 3 (optimized 6) raw1_1 raw1_4 [raw1_0, raw1_2, raw1_3] (cuts [raw1_0, raw1_2, raw1_3]) (raw1_4 &&& ~~~raw1_1) = false := by
  decide +kernel

theorem pair14 : dispatch 3 (optimized 6) raw1_1 raw1_4 [raw1_0, raw1_2, raw1_3] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair14Op0, pair14Op1, pair14Op2, pair14Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op0 : dispatchOp 3 (optimized 6) raw1_2 raw1_3 [raw1_0, raw1_1, raw1_4] (cuts [raw1_0, raw1_1, raw1_4]) (raw1_2 &&& raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op1 : dispatchOp 3 (optimized 6) raw1_2 raw1_3 [raw1_0, raw1_1, raw1_4] (cuts [raw1_0, raw1_1, raw1_4]) (raw1_2 ||| raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op2 : dispatchOp 3 (optimized 6) raw1_2 raw1_3 [raw1_0, raw1_1, raw1_4] (cuts [raw1_0, raw1_1, raw1_4]) (raw1_2 &&& ~~~raw1_3) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair23Op3 : dispatchOp 3 (optimized 6) raw1_2 raw1_3 [raw1_0, raw1_1, raw1_4] (cuts [raw1_0, raw1_1, raw1_4]) (raw1_3 &&& ~~~raw1_2) = false := by
  decide +kernel

theorem pair23 : dispatch 3 (optimized 6) raw1_2 raw1_3 [raw1_0, raw1_1, raw1_4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair23Op0, pair23Op1, pair23Op2, pair23Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op0 : dispatchOp 3 (optimized 6) raw1_2 raw1_4 [raw1_0, raw1_1, raw1_3] (cuts [raw1_0, raw1_1, raw1_3]) (raw1_2 &&& raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op1 : dispatchOp 3 (optimized 6) raw1_2 raw1_4 [raw1_0, raw1_1, raw1_3] (cuts [raw1_0, raw1_1, raw1_3]) (raw1_2 ||| raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op2 : dispatchOp 3 (optimized 6) raw1_2 raw1_4 [raw1_0, raw1_1, raw1_3] (cuts [raw1_0, raw1_1, raw1_3]) (raw1_2 &&& ~~~raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair24Op3 : dispatchOp 3 (optimized 6) raw1_2 raw1_4 [raw1_0, raw1_1, raw1_3] (cuts [raw1_0, raw1_1, raw1_3]) (raw1_4 &&& ~~~raw1_2) = false := by
  decide +kernel

theorem pair24 : dispatch 3 (optimized 6) raw1_2 raw1_4 [raw1_0, raw1_1, raw1_3] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair24Op0, pair24Op1, pair24Op2, pair24Op3]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op0 : dispatchOp 3 (optimized 6) raw1_3 raw1_4 [raw1_0, raw1_1, raw1_2] (cuts [raw1_0, raw1_1, raw1_2]) (raw1_3 &&& raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op1 : dispatchOp 3 (optimized 6) raw1_3 raw1_4 [raw1_0, raw1_1, raw1_2] (cuts [raw1_0, raw1_1, raw1_2]) (raw1_3 ||| raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op2 : dispatchOp 3 (optimized 6) raw1_3 raw1_4 [raw1_0, raw1_1, raw1_2] (cuts [raw1_0, raw1_1, raw1_2]) (raw1_3 &&& ~~~raw1_4) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pair34Op3 : dispatchOp 3 (optimized 6) raw1_3 raw1_4 [raw1_0, raw1_1, raw1_2] (cuts [raw1_0, raw1_1, raw1_2]) (raw1_4 &&& ~~~raw1_3) = false := by
  decide +kernel

theorem pair34 : dispatch 3 (optimized 6) raw1_3 raw1_4 [raw1_0, raw1_1, raw1_2] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, pair34Op0, pair34Op1, pair34Op2, pair34Op3]
  rfl

theorem topPairs : pairs rows1 =
  [(raw1_0, raw1_1, [raw1_2, raw1_3, raw1_4]),
   (raw1_0, raw1_2, [raw1_1, raw1_3, raw1_4]),
   (raw1_0, raw1_3, [raw1_1, raw1_2, raw1_4]),
   (raw1_0, raw1_4, [raw1_1, raw1_2, raw1_3]),
   (raw1_1, raw1_2, [raw1_0, raw1_3, raw1_4]),
   (raw1_1, raw1_3, [raw1_0, raw1_2, raw1_4]),
   (raw1_1, raw1_4, [raw1_0, raw1_2, raw1_3]),
   (raw1_2, raw1_3, [raw1_0, raw1_1, raw1_4]),
   (raw1_2, raw1_4, [raw1_0, raw1_1, raw1_3]),
   (raw1_3, raw1_4, [raw1_0, raw1_1, raw1_2])] := rfl

theorem rootReject : optimized 7 3 rows1 = false := by
  rw [optimized, topPairs]
  rw [show (rows1 == [goal] || rows1 == [~~~goal]) = false by decide]
  simp only [List.any_cons, List.any_nil, pair01, pair02, pair03, pair04, pair12, pair13, pair14, pair23, pair24, pair34]
  rfl

theorem fullInput : ∀ ws ∈ rows1.sublists, cuts ws = -1 → ws = rows1 := by decide +kernel

theorem reject5 : search 7 rows1 = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have h' : (rows1.sublists.any fun ws =>
      decide (ws.length ≤ 7 + 1) && (cuts ws == -1) && optimized 7 (7 + 1 - ws.length) ws) = true := h
  obtain ⟨ws, hw, hok⟩ := List.any_eq_true.mp h'
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨_, hc⟩, good⟩ := hok
  obtain rfl := fullInput ws hw hc
  change optimized 7 3 rows1 = true at good
  rw [rootReject] at good
  exact Bool.noConfusion good

end Part1

theorem unseen1 : Signed.search 7 rows1 = false := Part1.reject5

theorem side1 : ∀ j, R (phi (5 : Fin 6) true (nz tab)) j (L0 6) → 8 ≤ j :=
  CoreLeaf.lower obs1 _ rows1 7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) unseen1

theorem floorAll : ∀ k, R (nz tab) k (L0 6) → 10 ≤ k := by
  intro k hk
  obtain ⟨j,rfl,hj|hj⟩ := two_gates (5 : Fin 6) (nz tab)
    (ne_F _ (pt 9) (by decide +kernel)) (ne_F _ (pt 3) (by decide +kernel))
    (reads (5 : Fin 6) _ (pt 3) (by decide +kernel)) k (L0 6) (good_L0 _) hk
  · have := side0 j hj
    omega
  · have := side1 j hj
    omega

def gatesW : List Gate := [⟨.and, [3, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [14, 15]⟩]

theorem witness_eval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gatesW, 16⟩ (List.ofFn x) = spec x := by
  rw [sameTable]
  exact all_pts (fun x => Circuit.eval ⟨gatesW, 16⟩ (List.ofFn x) = tab x) (by decide +kernel)

end PEqualNP.Outside.L_meta_39801

open PEqualNP.Outside.L_meta_39801 in
theorem PEqualNP.Outside.L_meta_39801 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008241664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008241664) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  refine mono_shape2 spec 10 ?_ gatesW 16 (monoOK_sound _ (by decide +kernel)) (by decide +kernel) witness_eval
  rw [sameTable]
  exact floorAll
