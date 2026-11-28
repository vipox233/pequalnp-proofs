import PEqualNP.Defs
import Mathlib.Tactic.Tauto
namespace PEqualNP.Outside.L_meta_43254_aux
namespace Logic
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
def ReachN (T : α) : ℕ → List α → List α → Prop
  | 0, L, _ => T ∈ L
  | k + 1, L, F => T ∈ L ∨ ∃ s, Cand A O D L s ∧ s ∉ F ∧ s ∉ L ∧ ReachN T k (s :: L) F
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
theorem ReachN.monoK {T : α} : ∀ (k : ℕ) (L F : List α), ReachN A O D T k L F →
    ReachN A O D T (k + 1) L F := by
  intro k
  induction k with
  | zero => intro L F hr; exact Or.inl hr
  | succ k ih =>
    intro L F hr
    rcases hr with h1 | ⟨s, hc, hf, hl, hr⟩
    · exact Or.inl h1
    · exact Or.inr ⟨s, hc, hf, hl, ih _ _ hr⟩
theorem ReachN.congrL {T : α} : ∀ (k : ℕ) (L L' F : List α), (∀ x, x ∈ L ↔ x ∈ L') →
    ReachN A O D T k L F → ReachN A O D T k L' F := by
  intro k
  induction k with
  | zero => intro L L' F h hr; exact (h _).1 hr
  | succ k ih =>
    intro L L' F h hr
    rcases hr with h1 | ⟨s, hc, hf, hl, hr⟩
    · exact Or.inl ((h _).1 h1)
    · refine Or.inr ⟨s, hc.mono A O D (fun x hx => (h x).1 hx), hf,
        fun hx => hl ((h s).2 hx), ?_⟩
      refine ih _ _ _ ?_ hr
      intro x
      simp only [List.mem_cons, h x]
theorem Reach.toN {T : α} : ∀ (k : ℕ) (L : List α), Reach A O D T k L →
    ReachN A O D T k L [] := by
  intro k
  induction k with
  | zero => intro L hr; exact hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, hc, hr⟩
    · exact Or.inl h1
    · by_cases hs : s ∈ L
      · refine ReachN.monoK A O D _ _ _ (ih L (Reach.monoL A O D _ _ _ ?_ hr))
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · exact hx
      · exact Or.inr ⟨s, hc, List.not_mem_nil, hs, ih _ hr⟩
theorem ReachN.dich {T c : α} : ∀ (k : ℕ) (L F : List α), Cand A O D L c → c ∉ L →
    ReachN A O D T k L F →
    ReachN A O D T k L (c :: F) ∨ ∃ k', k = k' + 1 ∧ ReachN A O D T k' (c :: L) F := by
  intro k
  induction k with
  | zero => intro L F _ _ hr; exact Or.inl hr
  | succ k ih =>
    intro L F hc hcL hr
    rcases hr with h1 | ⟨s, hs, hf, hl, hr⟩
    · exact Or.inl (Or.inl h1)
    · by_cases hsc : s = c
      · subst hsc
        exact Or.inr ⟨k, rfl, hr⟩
      · have hc' : Cand A O D (s :: L) c :=
          hc.mono A O D (fun x hx => List.mem_cons_of_mem _ hx)
        have hcL' : c ∉ s :: L := by
          intro hx
          rcases List.mem_cons.mp hx with h | h
          · exact hsc h.symm
          · exact hcL h
        rcases ih (s :: L) F hc' hcL' hr with h | ⟨k', hk, h⟩
        · refine Or.inl (Or.inr ⟨s, hs, ?_, hl, h⟩)
          intro hx
          rcases List.mem_cons.mp hx with h | h
          · exact hsc h
          · exact hf h
        · refine Or.inr ⟨k, rfl, ?_⟩
          subst hk
          refine Or.inr ⟨s, hs.mono A O D (fun x hx => List.mem_cons_of_mem _ hx), hf, ?_, ?_⟩
          · intro hx
            rcases List.mem_cons.mp hx with h | h
            · exact hsc h
            · exact hl h
          · refine ReachN.congrL A O D _ _ _ _ ?_ h
            intro x
            simp only [List.mem_cons]
            tauto
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
def nd (FULL x y : ℕ) : ℕ := Nat.land x (Nat.xor FULL y)
abbrev NCand (FULL : ℕ) (L : List ℕ) (s : ℕ) : Prop := Cand Nat.land Nat.lor (nd FULL) L s
abbrev NReach (FULL T k : ℕ) (L : List ℕ) : Prop := Reach Nat.land Nat.lor (nd FULL) T k L
abbrev NReachN (FULL T k : ℕ) (L F : List ℕ) : Prop :=
  ReachN Nat.land Nat.lor (nd FULL) T k L F
def memb (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => cond (Nat.beq a b) true (memb a l)
theorem memb_iff {a : ℕ} {l : List ℕ} : memb a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memb]
  | cons b l ih =>
    simp only [memb, List.mem_cons]
    by_cases h : a = b
    · subst h; rw [Nat.beq_refl]; simp
    · have : Nat.beq a b = false := by
        rw [← Bool.not_eq_true]; exact fun hb => h (Nat.eq_of_beq_eq_true hb)
      rw [this]; simp [ih, h]
def force (n : ℕ) (k : ℕ → Bool) : Bool :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem force_eq (n : ℕ) (k : ℕ → Bool) : force n k = k n := by
  cases n <;> rfl
def cands2 (FULL : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: l => l.flatMap (fun y => [Nat.land x y, Nat.lor x y, nd FULL x y, nd FULL y x]) ++
      cands2 FULL l
def cands (FULL : ℕ) (L : List ℕ) : List ℕ := L.map (fun x => nd FULL x x) ++ cands2 FULL L
theorem cands2_sound (FULL : ℕ) : ∀ (L : List ℕ) (s : ℕ), s ∈ cands2 FULL L →
    NCand FULL L s := by
  intro L
  induction L with
  | nil => intro s hs; exact absurd hs List.not_mem_nil
  | cons x l ih =>
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨y, hy, h⟩ := List.mem_flatMap.mp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have hx' : x ∈ x :: l := List.mem_cons_self
      have hy' : y ∈ x :: l := List.mem_cons_of_mem _ hy
      rcases h with h | h | h | h
      · exact ⟨x, hx', y, hy', Or.inl h⟩
      · exact ⟨x, hx', y, hy', Or.inr (Or.inl h)⟩
      · exact ⟨x, hx', y, hy', Or.inr (Or.inr h)⟩
      · exact ⟨y, hy', x, hx', Or.inr (Or.inr h)⟩
    · exact (ih s h).mono _ _ _ (fun z hz => List.mem_cons_of_mem _ hz)
theorem cands2_complete (FULL : ℕ) : ∀ (L : List ℕ) (x y : ℕ), x ∈ L → y ∈ L → x ≠ y →
    Nat.land x y ∈ cands2 FULL L ∧ Nat.lor x y ∈ cands2 FULL L ∧ nd FULL x y ∈ cands2 FULL L := by
  intro L
  induction L with
  | nil => intro x y hx; exact absurd hx List.not_mem_nil
  | cons a l ih =>
    intro x y hx hy hxy
    have key : ∀ z ∈ l, Nat.land a z ∈ cands2 FULL (a :: l) ∧ Nat.lor a z ∈ cands2 FULL (a :: l)
        ∧ nd FULL a z ∈ cands2 FULL (a :: l) ∧ nd FULL z a ∈ cands2 FULL (a :: l) := by
      intro z hz
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨z, hz, by simp⟩)
    rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx]; exact ⟨(key y hy).1, (key y hy).2.1, (key y hy).2.2.1⟩
    · rw [hy, show Nat.land x a = Nat.land a x from Nat.and_comm x a,
        show Nat.lor x a = Nat.lor a x from Nat.or_comm x a]
      exact ⟨(key x hx).1, (key x hx).2.1, (key x hx).2.2.2⟩
    · obtain ⟨h1, h2, h3⟩ := ih x y hx hy hxy
      exact ⟨List.mem_append_right _ h1, List.mem_append_right _ h2, List.mem_append_right _ h3⟩
theorem cands_sound {FULL : ℕ} {L : List ℕ} {s : ℕ} (h : s ∈ cands FULL L) :
    NCand FULL L s := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact ⟨x, hx, x, hx, Or.inr (Or.inr rfl)⟩
  · exact cands2_sound FULL L s h
theorem cands_complete {FULL : ℕ} {L : List ℕ} {s : ℕ} (h : NCand FULL L s) (hl : s ∉ L) :
    s ∈ cands FULL L := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  by_cases hxy : x = y
  · subst hxy
    rcases h with h | h | h
    · have e1 : Nat.land x x = x := Nat.and_self x
      rw [e1] at h; rw [h] at hl; exact absurd hx hl
    · have e1 : Nat.lor x x = x := Nat.or_self x
      rw [e1] at h; rw [h] at hl; exact absurd hx hl
    · rw [h]; exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · obtain ⟨h1, h2, h3⟩ := cands2_complete FULL L x y hx hy hxy
    rcases h with h | h | h
    · rw [h]; exact List.mem_append_right _ h1
    · rw [h]; exact List.mem_append_right _ h2
    · rw [h]; exact List.mem_append_right _ h3
def loop (f : ℕ → List ℕ → Bool) (L : List ℕ) : List ℕ → List ℕ → Bool
  | [], _ => false
  | c :: cs, F =>
    force c (fun c' => cond (memb c' L) (loop f L cs F)
      (cond (memb c' F) (loop f L cs F)
        (cond (f c' F) true (loop f L cs (c' :: F)))))
theorem loop_cons (f : ℕ → List ℕ → Bool) (L : List ℕ) (c : ℕ) (cs F : List ℕ) :
    loop f L (c :: cs) F = cond (memb c L) (loop f L cs F)
      (cond (memb c F) (loop f L cs F)
        (cond (f c F) true (loop f L cs (c :: F)))) := by
  simp only [loop, force_eq]
theorem land_abs1 (x y : ℕ) : Nat.beq (Nat.land x (Nat.land x y)) (Nat.land x y) = true := by
  have e : Nat.land x (Nat.land x y) = Nat.land x y := by
    show x &&& (x &&& y) = x &&& y
    rw [← Nat.and_assoc, Nat.and_self]
  rw [e]; exact Nat.beq_refl _
theorem land_abs2 (x y : ℕ) : Nat.beq (Nat.land y (Nat.land x y)) (Nat.land x y) = true := by
  have e : Nat.land y (Nat.land x y) = Nat.land x y := by
    show y &&& (x &&& y) = x &&& y
    rw [Nat.and_comm x y, ← Nat.and_assoc, Nat.and_self]
  rw [e]; exact Nat.beq_refl _
theorem lor_abs1 (x y : ℕ) : Nat.beq (Nat.lor x (Nat.lor x y)) (Nat.lor x y) = true := by
  have e : Nat.lor x (Nat.lor x y) = Nat.lor x y := by
    show x ||| (x ||| y) = x ||| y
    rw [← Nat.or_assoc, Nat.or_self]
  rw [e]; exact Nat.beq_refl _
theorem lor_abs2 (x y : ℕ) : Nat.beq (Nat.lor y (Nat.lor x y)) (Nat.lor x y) = true := by
  have e : Nat.lor y (Nat.lor x y) = Nat.lor x y := by
    show y ||| (x ||| y) = x ||| y
    rw [Nat.or_comm x y, ← Nat.or_assoc, Nat.or_self]
  rw [e]; exact Nat.beq_refl _
theorem nd_abs (FULL x y : ℕ) : Nat.beq (Nat.land x (nd FULL x y)) (nd FULL x y) = true :=
  land_abs1 x (Nat.xor FULL y)
def candCheck (FULL T : ℕ) (L U Dn : List ℕ) : Bool :=
  U.any (fun x => U.any (fun y => Nat.beq (Nat.land x y) T) ||
      L.any (fun y => Nat.beq (nd FULL x y) T)) ||
    Dn.any (fun x => Dn.any (fun y => Nat.beq (Nat.lor x y) T))
def upOf (T : ℕ) (L : List ℕ) : List ℕ := L.filter (fun x => Nat.beq (Nat.land x T) T)
def dnOf (T : ℕ) (L : List ℕ) : List ℕ := L.filter (fun x => Nat.beq (Nat.lor x T) T)
theorem candCheck_complete {FULL T : ℕ} {L : List ℕ} (h : NCand FULL L T) :
    candCheck FULL T L (upOf T L) (dnOf T L) = true := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  unfold candCheck
  rw [Bool.or_eq_true]
  rcases h with h | h | h
  · subst h
    left
    rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, land_abs1 x y⟩, ?_⟩
    rw [Bool.or_eq_true]
    left
    rw [List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, land_abs2 x y⟩, Nat.beq_refl _⟩
  · subst h
    right
    rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, lor_abs1 x y⟩, ?_⟩
    rw [List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, lor_abs2 x y⟩, Nat.beq_refl _⟩
  · subst h
    left
    rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, nd_abs FULL x y⟩, ?_⟩
    rw [Bool.or_eq_true]
    right
    rw [List.any_eq_true]
    exact ⟨y, hy, Nat.beq_refl _⟩
def test2 (FULL T : ℕ) (L U Dn : List ℕ) (c : ℕ) : Bool :=
  (Nat.beq (Nat.land c T) T &&
      (U.any (fun z => Nat.beq (Nat.land c z) T) || L.any (fun z => Nat.beq (nd FULL c z) T) ||
        Nat.beq (nd FULL c c) T)) ||
    (Nat.beq (Nat.lor c T) T && Dn.any (fun z => Nat.beq (Nat.lor c z) T)) ||
    U.any (fun z => Nat.beq (nd FULL z c) T)
def check2 (FULL T : ℕ) (L : List ℕ) : Bool :=
  cond (candCheck FULL T L (upOf T L) (dnOf T L)) true
    ((cands FULL L).any (test2 FULL T L (upOf T L) (dnOf T L)))
theorem check2_complete {FULL T : ℕ} {L F : List ℕ} (hT : T ∉ L) (h : NReachN FULL T 2 L F) :
    check2 FULL T L = true := by
  rcases h with h | ⟨s, hc, _, hl, hr⟩
  · exact absurd h hT
  · have left : NCand FULL L T → check2 FULL T L = true := by
      intro h
      unfold check2
      rw [candCheck_complete h]; rfl
    have key : test2 FULL T L (upOf T L) (dnOf T L) s = true → check2 FULL T L = true := by
      intro h
      have : (cands FULL L).any (test2 FULL T L (upOf T L) (dnOf T L)) = true := by
        rw [List.any_eq_true]
        exact ⟨s, cands_complete hc hl, h⟩
      unfold check2
      rw [this]
      cases candCheck FULL T L (upOf T L) (dnOf T L) <;> rfl
    have kA : ∀ y ∈ L, T = Nat.land s y → check2 FULL T L = true := by
      intro y hy h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true,
        List.any_eq_true]
      exact Or.inl (Or.inl ⟨land_abs1 s y,
        Or.inl (Or.inl ⟨y, List.mem_filter.mpr ⟨hy, land_abs2 s y⟩, Nat.beq_refl _⟩)⟩)
    have kO : ∀ y ∈ L, T = Nat.lor s y → check2 FULL T L = true := by
      intro y hy h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true (Nat.beq (Nat.lor s _) _),
        List.any_eq_true]
      exact Or.inl (Or.inr ⟨lor_abs1 s y, y, List.mem_filter.mpr ⟨hy, lor_abs2 s y⟩,
        Nat.beq_refl _⟩)
    have kD1 : ∀ y ∈ L, T = nd FULL s y → check2 FULL T L = true := by
      intro y hy h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true,
        List.any_eq_true (l := L)]
      exact Or.inl (Or.inl ⟨nd_abs FULL s y, Or.inl (Or.inr ⟨y, hy, Nat.beq_refl _⟩)⟩)
    have kD2 : ∀ x ∈ L, T = nd FULL x s → check2 FULL T L = true := by
      intro x hx h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨x, List.mem_filter.mpr ⟨hx, nd_abs FULL x s⟩, Nat.beq_refl _⟩
    have kD3 : T = nd FULL s s → check2 FULL T L = true := by
      intro h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true]
      exact Or.inl (Or.inl ⟨nd_abs FULL s s, Or.inr (Nat.beq_refl _)⟩)
    have hsT : T = s → check2 FULL T L = true := fun e => left (e ▸ hc)
    rcases hr with h | ⟨s2, hc2, _, _, hr2⟩
    · rcases List.mem_cons.mp h with h | h
      · exact hsT h
      · exact absurd h hT
    · have hr2' : T ∈ s2 :: s :: L := hr2
      rcases List.mem_cons.mp hr2' with h | h
      · subst h
        obtain ⟨x, hx, y, hy, hop⟩ := hc2
        have e1 : Nat.land s s = s := Nat.and_self s
        have e2 : Nat.lor s s = s := Nat.or_self s
        rcases hop with hop | hop | hop
        · rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
          · rw [hx, hy, e1] at hop; exact hsT hop
          · rw [hx] at hop; exact kA y hy hop
          · rw [hy, show Nat.land x s = Nat.land s x from Nat.and_comm x s] at hop
            exact kA x hx hop
          · exact left ⟨x, hx, y, hy, Or.inl hop⟩
        · rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
          · rw [hx, hy, e2] at hop; exact hsT hop
          · rw [hx] at hop; exact kO y hy hop
          · rw [hy, show Nat.lor x s = Nat.lor s x from Nat.or_comm x s] at hop
            exact kO x hx hop
          · exact left ⟨x, hx, y, hy, Or.inr (Or.inl hop)⟩
        · rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
          · rw [hx, hy] at hop; exact kD3 hop
          · rw [hx] at hop; exact kD1 y hy hop
          · rw [hy] at hop; exact kD2 x hx hop
          · exact left ⟨x, hx, y, hy, Or.inr (Or.inr hop)⟩
      · rcases List.mem_cons.mp h with h | h
        · exact hsT h
        · exact absurd h hT
def chk (FULL T : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, L, _ => memb T L
  | 1, L, _ => cond (memb T L) true (candCheck FULL T L (upOf T L) (dnOf T L))
  | 2, L, _ => cond (memb T L) true (check2 FULL T L)
  | k + 3, L, F =>
    cond (memb T L) true (loop (fun c F' => chk FULL T (k + 2) (c :: L) F') L (cands FULL L) F)
theorem loop_complete {FULL T : ℕ} (L : List ℕ) (f : ℕ → List ℕ → Bool) (k : ℕ)
    (ih : ∀ c F, NReachN FULL T k (c :: L) F → f c F = true) (hT : T ∉ L) :
    ∀ (cs F : List ℕ), (∀ c ∈ cs, NCand FULL L c) →
      (∀ s, NCand FULL L s → s ∉ L → s ∉ F → s ∈ cs) →
      NReachN FULL T (k + 1) L F → loop f L cs F = true := by
  intro cs
  induction cs with
  | nil =>
    intro F _ hcpl hr
    rcases hr with h | ⟨s, hc, hf, hl, _⟩
    · exact absurd h hT
    · exact absurd (hcpl s hc hl hf) List.not_mem_nil
  | cons c cs ihc =>
    intro F hs hcpl hr
    have hs' : ∀ c ∈ cs, NCand FULL L c := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    rw [loop_cons]
    have skip : c ∈ L ∨ c ∈ F → loop f L cs F = true := by
      intro hin
      refine ihc F hs' ?_ hr
      intro s hc hl hf
      rcases List.mem_cons.mp (hcpl s hc hl hf) with h | h
      · subst h
        rcases hin with h | h
        · exact absurd h hl
        · exact absurd h hf
      · exact h
    by_cases hcL : c ∈ L
    · rw [memb_iff.2 hcL]; exact skip (Or.inl hcL)
    · have hm : memb c L = false := by rw [← Bool.not_eq_true, memb_iff]; exact hcL
      rw [hm]
      by_cases hcF : c ∈ F
      · rw [memb_iff.2 hcF]; exact skip (Or.inr hcF)
      · have hm2 : memb c F = false := by rw [← Bool.not_eq_true, memb_iff]; exact hcF
        rw [hm2]
        rcases ReachN.dich Nat.land Nat.lor (nd FULL) _ _ _ (hs c List.mem_cons_self) hcL hr
          with h | ⟨k', hk, h⟩
        · have : loop f L cs (c :: F) = true := by
            refine ihc (c :: F) hs' ?_ h
            intro s hc hl hf
            rcases List.mem_cons.mp (hcpl s hc hl (fun hx => hf (List.mem_cons_of_mem _ hx)))
              with h | h
            · subst h; exact absurd List.mem_cons_self hf
            · exact h
          rw [this]; cases f c F <;> rfl
        · have hk' : k' = k := by omega
          subst hk'
          rw [ih c F h]; rfl
theorem chk_complete {FULL T : ℕ} : ∀ (k : ℕ) (L F : List ℕ),
    NReachN FULL T k L F → chk FULL T k L F = true := by
  intro k
  induction k with
  | zero => intro L F h; exact memb_iff.2 h
  | succ k ih =>
    intro L F h
    by_cases hT : T ∈ L
    · have hm : memb T L = true := memb_iff.2 hT
      rcases k with _ | _ | k <;> simp only [chk, hm, Bool.cond_true]
    · have hm : memb T L = false := by
        rw [← Bool.not_eq_true, memb_iff]; exact hT
      cases k with
      | zero =>
        simp only [chk, hm, Bool.cond_false]
        rcases h with h | ⟨s, hc, _, _, hr⟩
        · exact absurd h hT
        · rcases List.mem_cons.mp hr with h | h
          · subst h; exact candCheck_complete hc
          · exact absurd h hT
      | succ k =>
        cases k with
        | zero =>
          simp only [chk, hm, Bool.cond_false]
          exact check2_complete hT h
        | succ k =>
        simp only [chk, hm, Bool.cond_false]
        exact loop_complete L _ (k + 2) (fun c F' hr => ih (c :: L) F' hr) hT
          (cands FULL L) F (fun c hc => cands_sound hc)
          (fun s hc hl _ => cands_complete hc hl) h
def tt {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) : ℕ :=
  Nat.ofBits (fun j : Fin N => g (e j.val))
theorem tt_testBit {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) (i : ℕ) :
    (tt N e g).testBit i = (decide (i < N) && g (e i)) := by
  unfold tt
  by_cases h : i < N
  · rw [Nat.testBit_ofBits_lt _ _ h]; simp [h]
  · rw [Nat.testBit_ofBits_ge _ _ (not_lt.mp h)]; simp [h]
theorem tt_and {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    tt N e (fAnd a b) = Nat.land (tt N e a) (tt N e b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show _ = (tt N e a &&& tt N e b).testBit i
  rw [Nat.testBit_and, tt_testBit, tt_testBit, tt_testBit]
  by_cases h : i < N <;> simp [h, fBin]
theorem tt_or {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    tt N e (fOr a b) = Nat.lor (tt N e a) (tt N e b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show _ = (tt N e a ||| tt N e b).testBit i
  rw [Nat.testBit_or, tt_testBit, tt_testBit, tt_testBit]
  by_cases h : i < N <;> simp [h, fBin]
theorem tt_diff {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    tt N e (fDiff a b) = nd (2 ^ N - 1) (tt N e a) (tt N e b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show _ = (tt N e a &&& ((2 ^ N - 1) ^^^ tt N e b)).testBit i
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, tt_testBit, tt_testBit,
    tt_testBit]
  by_cases h : i < N <;> simp [h, fBin]
theorem tt_F {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) : tt N e (fF n) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [tt_testBit]
  simp [fF]
theorem leaf {n : ℕ} (N FULL : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) (T k : ℕ) (Ln : List ℕ)
    (hFULL : 2 ^ N - 1 = FULL) (hT : tt N e g = T) (hL0 : 0 ∈ Ln)
    (hLv : ∀ p : Fin n, tt N e (fV p) ∈ Ln)
    (hc : chk FULL T k Ln [] = false) : ∀ j : ℕ, R g j (L0 n) → k + 1 ≤ j := by
  intro j hr
  by_contra hlt
  have hjk : j ≤ k := by omega
  have h1 := Reach.monoLe fAnd fOr fDiff hjk _ hr
  have h2 := Reach.map fAnd fOr fDiff Nat.land Nat.lor (nd FULL) (tt N e) (by
    intro x y s hs L' hx hy
    rcases hs with rfl | rfl | rfl
    · exact ⟨_, hx, _, hy, Or.inl (tt_and N e x y)⟩
    · exact ⟨_, hx, _, hy, Or.inr (Or.inl (tt_or N e x y))⟩
    · exact ⟨_, hx, _, hy, Or.inr (Or.inr (by rw [tt_diff, hFULL]))⟩) k _ h1
  rw [hT] at h2
  have h3 : NReach FULL T k Ln := by
    refine Reach.monoL _ _ _ _ _ _ ?_ h2
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [tt_F]; exact hL0
    obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hw
    exact hLv q
  have h4 := chk_complete k Ln [] (Reach.toN Nat.land Nat.lor (nd FULL) k Ln h3)
  rw [hc] at h4
  exact Bool.false_ne_true h4
theorem lb_size {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k) :
    ∀ t : ℕ, HasCircuitSize n f t → B ≤ t := by
  rintro t ⟨C, hC, hs, he⟩
  have hok : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have h1 := hB _ (prog_of_gatelist f C.gates C.output hok he)
  have h2 := cnt_le C.gates
  have h3 : C.gates.length ≤ t := hs
  omega
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
def tblOK (c : ℕ) (F : List ℕ) : List (ℕ × List ℕ) → Bool
  | [] => false
  | e :: _ => decide (c = e.1 ∧ F = e.2)
def loopT (L : List ℕ) : List ℕ → List ℕ → List (ℕ × List ℕ) → Bool
  | [], _, _ => true
  | c :: cs, F, tbl =>
    cond (memb c L) (loopT L cs F tbl)
      (cond (memb c F) (loopT L cs F tbl)
        (cond (tblOK c F tbl) (loopT L cs (c :: F) tbl.tail) false))
def AllF (f : ℕ → List ℕ → Bool) : List (ℕ × List ℕ) → Prop
  | [] => True
  | e :: tl => f e.1 e.2 = false ∧ AllF f tl
theorem loop_false (f : ℕ → List ℕ → Bool) (L : List ℕ) : ∀ (cs F : List ℕ)
    (tbl : List (ℕ × List ℕ)), loopT L cs F tbl = true → AllF f tbl → loop f L cs F = false := by
  intro cs
  induction cs with
  | nil => intro F tbl _ _; rfl
  | cons c cs ih =>
    intro F tbl h ha
    rw [loop_cons]
    unfold loopT at h
    cases hL : memb c L
    · rw [hL] at h
      cases hF : memb c F
      · rw [hF] at h
        cases tbl with
        | nil => exact absurd h (by simp [tblOK])
        | cons e tl =>
          cases hk : tblOK c F (e :: tl)
          · rw [hk] at h; exact absurd h (by simp)
          · rw [hk] at h
            obtain ⟨h1, h2⟩ := of_decide_eq_true hk
            obtain ⟨ha1, ha2⟩ := ha
            rw [← h1, ← h2] at ha1
            simp only [Bool.cond_false, ha1]
            exact ih (c :: F) tl h ha2
      · rw [hF] at h
        simp only [Bool.cond_false, Bool.cond_true]
        exact ih F tbl h ha
    · rw [hL] at h
      simp only [Bool.cond_true]
      exact ih F tbl h ha
theorem chk_split (FULL T k : ℕ) (L F : List ℕ) (tbl : List (ℕ × List ℕ))
    (hT : memb T L = false) (hl : loopT L (cands FULL L) F tbl = true)
    (ha : AllF (fun c F' => chk FULL T (k + 2) (c :: L) F') tbl) :
    chk FULL T (k + 3) L F = false := by
  simp only [chk, hT, Bool.cond_false]
  exact loop_false _ L _ F tbl hl ha
theorem mono_shape {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ)
    (hWm : ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWl : Wg.length ≤ B)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x) :
    ∀ s : ℕ, HasCircuitSize n f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro s hs
  have h1 := lb_size f B hB s hs
  refine ⟨⟨Wg, wo⟩, ?_, le_trans hWl h1, hWe⟩
  intro g hg
  obtain ⟨h2, h3⟩ := hWm g hg
  refine ⟨?_, h3⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h2
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

end Logic
namespace Search
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem avail_mono {d:Nat} {bank:List Nat} {w:Nat} (h : Avail false d bank w) :
    Avail true d bank w:=by
  rcases h with h | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction
theorem reach_up {d:Nat} {roots:List Nat} {p bank} (h:NatReach false d roots p bank) :
    NatReach true d roots p bank:=by
  induction p generalizing bank with
  | zero=>exact h
  | succ p ih =>
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=h
    have hop' : allowedB true op = true:=by
      rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩ <;> first | decide | contradiction
    exact ⟨b,a,c,op,hop',rfl,ih hrb,avail_mono ha,avail_mono hc⟩
theorem lower_down {d:Nat} {roots:List Nat} {T L:Nat} (h : Lower true d roots T L) :
    Lower false d roots T L:=fun p bank hr ha=>h p bank (reach_up hr) (avail_mono ha)
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPool u dSub LSub s (stepOp u dSub (runOps u dSub (0,rootsSub) ops) g) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub,Avail u dSub rootsSub v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub) rootsSub rfl hsup0
  obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
theorem checkRootSub_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (hchk : checkPool u dSub LSub s (0,rootsSub) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub) rootsSub rfl (fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)) hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2,hp.2] at heq; contradiction
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def value6 (a b c d e f:Bool):Nat :=
  let x:=b.toNat + c.toNat
  let y:=(!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m:Bool,
    value6 (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m:Bool,
    value6 (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v:Nat → Nat) (hand : ∀ a b,v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b,v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩
    · simp only [opD,beq_self_eq_true,ite_true,kept,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hand]; exact ih'
    · simp only [opD,beq_self_eq_true,ite_true,ite_false,kept,Bool.false_eq_true,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hor]; exact ih'
    · contradiction
    · contradiction
def eval6 (a b c d e f v:Nat):=value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f:Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum:=by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,andD,Nat.testBit_and,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,orD,Nat.testBit_and,Nat.testBit_or,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def sumBelow (v:Nat → Nat):List Nat → Nat → Bool
  | [],n=>n != 0
  | w :: ws,n=>decide (v w < n)&&sumBelow v ws (n - v w)
theorem sumBelow_iff (v:Nat → Nat) (ws:List Nat) (n:Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n:=by
  induction ws generalizing n with
  | nil=>simp [sumBelow]
  | cons w ws ih=>rw [sumBelow,Bool.and_eq_true,decide_eq_true_eq,ih,List.map_cons,List.sum_cons]; omega
def scoreCheck (dm y s:Nat) (ws:List Nat) (code:Nat):Bool :=
  let a:=code&&&255
  let b:=(code >>> 8)&&&255
  let c:=(code >>> 16)&&&255
  let d:=(code >>> 24)&&&255
  let e:=(code >>> 32)&&&255
  let f:=(code >>> 40)&&&255
  dm.testBit a&&dm.testBit b&&dm.testBit c&&dm.testBit d&&dm.testBit e&&dm.testBit f &&
    ws.length==s + 1&&sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)
theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code:Nat) :
    scoreCheck dm y s ws code = false:=by
  unfold scoreCheck
  by_cases hok : dm.testBit (code&&&255) = true ∧ dm.testBit ((code >>> 8)&&&255) = true ∧
      dm.testBit ((code >>> 16)&&&255) = true ∧ dm.testBit ((code >>> 24)&&&255) = true ∧
      dm.testBit ((code >>> 32)&&&255) = true ∧ dm.testBit ((code >>> 40)&&&255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha,hb,hc,hd,he,hf,hl⟩:=hok
    simp only [ha,hb,hc,hd,he,hf,hl,beq_self_eq_true,Bool.true_and]
    by_contra hbad
    have hsum:=(sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht:=Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1,ht.1.1.1.1.1.1.2,ht.1.1.1.1.1.2,ht.1.1.1.1.2,ht.1.1.1.2,ht.1.1.2,ht.1.2⟩
def scr (u:Bool) (dm y s:Nat) (pool:List Nat) (zs:List Nat):Bool :=
  !u&&zs.length==s + 1&&pool.any (scoreCheck dm y s zs)
theorem scr_no {u:Bool} {dm y s:Nat} (pool:List Nat) {zs:List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false:=by
  cases u with
  | true=>simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false,Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&4294967295
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def bar (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(scr u dm Y s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
    | p :: ps =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          !((p :: ps).any fun e=>checkPool u e.1 e.2.1 s (stepOp u e.1 e.2.2 g) zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&(roots.map (·&&&d)).Nodup &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs⟩,hpairs⟩:=hinit
  have hnd_xs' : (roots.map (·&&&d)).Nodup:=by simpa using hnd_xs
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (u:Bool) (dm Y mp:Nat) (SD S N htAt idxH ori seed pool mkPools s i) :
    barP u dm Y mp SD S N htAt idxH ori seed pool mkPools s i =
      bar u dm Y mp SD S N htAt idxH ori seed pool
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool u e.1 e.2.1 (s' - 1) (stepOp u e.1 e.2.2 g) zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {u:Bool} {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD u dm (T&&&dm) v ys → RunD u dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD u dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar u dm (T&&&dm) mp SD S N htAt idxH ori seed pool mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD u dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP u pairs zs&&!(scr u dm (T&&&dm) s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD u dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,scr_no pool hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD u (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T&&&dm) s pool zs')&&!(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
def gvN (w:List Nat) (g : Gate):Nat :=
  match g.op with
  | .and=>g.inputs.foldr (fun i acc=>andD mask256 (w.getD i 0) acc) mask256
  | .or =>g.inputs.foldr (fun i acc=>orD mask256 (w.getD i 0) acc) 0
  | .not=>match g.inputs with | []=>mask256 | i :: _=>negD mask256 (w.getD i 0)
  | _=>0
def execN (gs:List Gate) (w:List Nat):List Nat :=
  gs.foldl (fun l g=>l ++ [gvN l g]) w
theorem gvN_bit (w:List Nat) (g : Gate) (r:Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i=>(w.map (·.testBit r)).getD i false):=by
  have hm : mask256.testBit r = true:=by simp [mask256_bit,hr]
  have hgd : ∀ i,(w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r:=by
    intro i; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? with | none=>simp | some v=>rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.all_cons,id_eq,andD,Nat.testBit_and,Nat.testBit_and,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.any_cons,id_eq,orD,Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    cases g.inputs with
    | nil=>simp [hm]
    | cons i l=>simp only [List.map_cons,List.headD_cons,negD,Nat.testBit_and,Nat.testBit_xor,hm,Bool.and_true,Bool.xor_true,hgd]
theorem execN_bit (gs:List Gate) (w:List Nat) (r:Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g=>l ++ [g.op.eval (g.inputs.map fun i=>l.getD i false)]) (w.map (·.testBit r)):=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [execN,List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]
def isNotGate (g : Gate):Bool:=match g.op with | .not=>true | _=>false
theorem execN_reach (u:Bool) (gs:List Gate) (roots:List Nat)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs,isNotGate g = false) :
    ∀ (p:Nat) (w bank:List Nat),NatReach u mask256 roots p bank →
      (∀ v ∈ w,Avail u mask256 bank v) →
      ∃ p' bank',p' ≤ p + gs.countP (fun g=>!isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w,Avail u mask256 bank' v:=by
  have hm256 : mask256&&&mask256 = mask256:=Nat.and_self _
  induction gs with
  | nil=>intro p w bank hr hsup; exact ⟨p,bank,by simp,hr,hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i,Avail u mask256 bank (w.getD i 0):=by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1,p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g],Avail u mask256 bank1 v):=by
      have hg:=hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      obtain ⟨hop,hlen⟩:=hg
      have hand_m : ∀ a,andD mask256 a mask256&&&mask256 = a&&&mask256:=fun a=>by
        simp [andD,Nat.and_assoc,Nat.and_self]
      have hor_0 : ∀ a,orD mask256 a 0&&&mask256 = a&&&mask256:=fun a=>by
        simp [orD,Nat.and_assoc,Nat.and_self]
      have lift_w : ∀ z,(∀ v ∈ w,Avail u mask256 (z :: bank) v):=fun z v hv=>avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,0,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by simp [opD,andD,Nat.and_assoc,Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,1,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by apply Nat.eq_of_testBit_eq; intro r; simp [opD,orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad:=hmono rfl g List.mem_cons_self
          simp [isNotGate,h] at hbad
        | true =>
          have hn : (!isNotGate g) = false:=by simp [isNotGate,h]
          rw [hn]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i,l⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1,bank1,hp1,hr1,hsup1⟩:=hstep
    obtain ⟨p2,bank2,hp2,hr2,hsup2⟩:=ih (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg'=>hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at hp1 ⊢ <;>
      exact ⟨p2,bank2,by omega,hr2,hsup2⟩
def xs256:List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def pt8 (r:Nat) : Fin 8 → Bool:=fun i=>r.testBit i.val
theorem xs256_bits : ∀ r : Fin 256,xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val):=by
  decide +kernel
theorem countP_not_lt {gs:List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x=>!isNotGate x) + 1 ≤ gs.length:=by
  induction gs with
  | nil=>simp at hg
  | cons x xs ih =>
    rw [List.countP_cons,List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn,Bool.not_true,Bool.false_eq_true,ite_false]
      have:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=xs); omega
    · have:=ih hxs; cases hb : !isNotGate x <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] <;> omega
theorem directSplit_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb:Nat)
    (hT : ∀ r : Fin 256,T.testBit r.val = f (pt8 r.val))
    (hS : Lower true mask256 xs256 T (lb - 1))
    (hM : Lower false mask256 xs256 T lb) :
    ∀ t : ℕ,HasCircuitSize 8 f t → lb ≤ t:=by
  rintro t ⟨C,hfan,hsz,hev⟩
  have hout : (execN C.gates xs256).getD C.output 0&&&mask256 = T&&&mask256:=by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and,Nat.testBit_and,mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt,decide_true,Bool.and_true]
      have h1:=execN_bit C.gates xs256 r hlt (fun g hg=>(hfan g hg).1)
      have h2:=congrArg (fun l=>l.getD C.output false) h1
      rw [xs256_bits ⟨r,hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r:=by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none=>simp | some v=>rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r):=hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r,hlt⟩).symm)
    · simp [hlt]
  by_cases hhas : ∃ g ∈ C.gates,isNotGate g = true
  · obtain ⟨g,hg,hgn⟩:=hhas
    have hsup0 : ∀ v ∈ xs256,Avail true mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach true C.gates xs256 hfan (fun h=>Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail true mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hS p bank hr (avail_of_eq hout hav_out)
    have hlt:=countP_not_lt hg hgn
    have : C.gates.length ≤ t:=hsz
    omega
  · push_neg at hhas
    have hmono : ∀ g ∈ C.gates,isNotGate g = false:=fun g hg=>Bool.eq_false_iff.2 (hhas g hg)
    have hsup0 : ∀ v ∈ xs256,Avail false mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach false C.gates xs256 hfan (fun _=>hmono) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail false mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hM p bank hr (avail_of_eq hout hav_out)
    have hle:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=C.gates)
    have : C.gates.length ≤ t:=hsz
    omega

end Search

namespace Case1
open Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_39:=0xff000000ff
def roots_39:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 5 0]
def dom_42:=0x50500000505
def roots_42:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_43:=0xf0f00000f0f
def roots_43:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_45:=0x333300003333
def roots_45:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_46:=0x555500005555
def roots_46:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_47:=0xffff0000ffff
def roots_47:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_15_32:=0xeaa8
def goal_39_8:=0xea000000a8
def goal_42_1:=0x50400000400
def goal_43_0:=0xa0800000800
def goal_45_2:=0x322200002220
def goal_46_1:=0x555400005450
def goal_47_0:=0xeaa80000a8a0
def goal_63_0:=0xeee8eaa8ece0a8a0
namespace S_15_32
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(2,3),(4,5),(6,7),(6,14),(8,9),(10,11),(10,14),(12,13),(12,14)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_32 &&& dom_15
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x8395cb231bc7e878
|3,0=>0xc7d0175b57e3d3b04f76fdd8345987042a96e68b29bc83021f3844161459a69c110046250a4a9b3404f8ca3e
|4,0=>0x57e3d3b047d996be2c89b5bf129291b90fdaabe907006be5029550b9006842cf
|5,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf000a0a000ccc8c844442222ff30cf00fcfcc0c0ffaaf0f0aa000f0afaf030300c0c7070ff005a5accccaaaa0ff0
|_,_=>0
def stPool:Nat → Nat
|0=>0x458824588245883222ec20b08b1048b106a472c4122c41891620d08b9848b1048b9460b1056f1048e6858b128820a48810481398820948218820
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>0xb9152264448790d216424839052064
|4,0=>0xaa94165ac6582af15bab25
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_32 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_32
theorem lowS_15_32:Lower true dom_15 roots_15 goal_15_32 6:=S_15_32.noCircuit
def isoMv_45_2:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]
theorem lowS_45_2:Lower true dom_45 roots_45 goal_45_2 6:=lower_iso isoMv_45_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_39_8:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)]
theorem lowS_39_8:Lower true dom_39 roots_39 goal_39_8 6:=lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
namespace S_42_1
def pairsG:List (Nat × Nat):=[(2,10),(2,34),(8,10),(8,40),(32,34),(32,40)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_42.map (· &&& dom_42)
def goalM:Nat:=goal_42_1 &&& dom_42
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x47202343
|3,0=>0x47202343
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x141400000002800000028040400000404
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 43 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_42 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_42 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_42==dom_42) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_42 goalM v ys):RunD true dom_42 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_42 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_42 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_42 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_42 roots_42 goal_42_1 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_42_1
theorem lowS_42_1:Lower true dom_42 roots_42 goal_42_1 4:=S_42_1.noCircuit
def dzo_42_1:=0xa0a00000a0a
def gzo_42_1_1:=0xa0800000800
theorem lowSh_42_1_1:Lower true dzo_42_1 roots_42 gzo_42_1_1 4:=lower_iso (d1:=dom_42) (roots1:=roots_42) (T1:=goal_42_1) [(dom_42,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
namespace S_43_0
def pairsG:List (Nat × Nat):=[(3,11),(3,35),(9,11),(9,41),(10,11),(33,35),(33,41),(34,35),(40,41),(42,43)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_43.map (· &&& dom_43)
def goalM:Nat:=goal_43_0 &&& dom_43
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_43 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_42_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_42_1 4 s (0,roots_42) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_43 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_42_1_1 h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_43==dom_43) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_43 goalM v ys):RunD true dom_43 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_43 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_43 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_43 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_43 roots_43 goal_43_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_43_0
theorem lowS_43_0:Lower true dom_43 roots_43 goal_43_0 5:=S_43_0.noCircuit
theorem lowS_46_1:Lower true dom_46 roots_46 goal_46_1 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x505000005050,0,4)] (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_45_2:=0xcccc0000cccc
def gzo_45_2_2:=0xc88800008880
theorem lowSh_45_2_2:Lower true dzo_45_2 roots_45 gzo_45_2_2 6:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=goal_45_2) [(dom_45,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_2
def dzo_39_8:=0xff000000ff00
def gzo_39_8_8:=0xea000000a800
theorem lowSh_39_8_8:Lower true dzo_39_8 roots_39 gzo_39_8_8 6:=lower_iso (d1:=dom_39) (roots1:=roots_39) (T1:=goal_39_8) [(dom_39,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_39_8
def dzo_15_32:=0xffff00000000
def gzo_15_32_32:=0xeaa800000000
theorem lowSh_15_32_32:Lower true dzo_15_32 roots_15 gzo_15_32_32 6:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_32) [(dom_15,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def dzo_46_1:=0xaaaa0000aaaa
def gzo_46_1_1:=0xaaa80000a8a0
theorem lowSh_46_1_1:Lower true dzo_46_1 roots_46 gzo_46_1_1 5:=lower_iso (d1:=dom_46) (roots1:=roots_46) (T1:=goal_46_1) [(dom_46,1)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_46_1
namespace S_47_0
def pairsG:List (Nat × Nat):=[(1,5),(3,7),(3,11),(3,35),(4,5),(6,7),(9,11),(9,13),(9,41),(10,11),(12,13),(14,15),(14,46),(33,35),(33,37),(33,41),(34,35),(36,37),(38,39),(38,46),(40,41),(42,43),(42,46),(44,45),(44,46)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_47.map (· &&& dom_47)
def goalM:Nat:=goal_47_0 &&& dom_47
def NN:Nat → Nat
|2=>6
|3=>76
|4=>197
|5=>288
|6=>66
|7=>10
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x9877705f522ffb503a7f53af0f10091e0c2464a2059b6764
|3,0=>0xd09dbd87940a10b5923b956c8a6be661838f622b835d3fdf7eab44247d19d66476f5cae075996af17268e1ba71f415d76a6bdc06601df8035a92e3c6580e6c1d561a848353d68f264efc48e64eedfb8c4d6e40ca4d2d75cc4b4f5f174a2b548546c60a6844639e32412fb58b4101e8df3c3592b83b114b3a3921bb7638d7876c36ccc0203590e69434749f4a33fb75ed330a679731876b632fda17bb2f297a632c7656bb2a23548a29c5de9726bd31c626232a2c25499c17231bc9e51fd609471afc62031abc5a0219a3f3e818c9adbc1778eb7d16f4037914c8220914adb585144ed5fe12df7c50108790100bf678fd0bbfbc5f0b79d8310b7642590abe971c099889b9082309a307a62ec906d32b66067c0b61062e3af903b39b3003b2ff1d034ee54f0260810d00b7d85a0041197a
|4,0=>0x441c100b43d21da7425b28c041a85aa740bd7c16408918493f10cad53f1026103eef83653cf3bae63af124b03aeaf5383a48f72439db5f0e39c5af17393f40f6383d3a3738346c4737751903356314d735094e7635020f2d34bd0ae833b1f8aa339676f5335ecf0431cb475a31c57ec73134e0a52fc9afe42f089c632e1fdc4a2d7d1ac52a1b78ec299af30e2975534928721c782808509927d4ffa426c1be1f2664888825f60e3125a55e24249604dc2456cf472438797a2368af74231f9973222f9ee422207b3c217b96e32176ef002145b2bf2143d3332125cdf3208e03791f9d19431f1e52231d73be161d58011c1d376ef11d0df4591bc07f031b8ef9ea1b8b7d581a81472f1a30019d19fc1e9719fb5f4d1900b7fb18d57ec418874a9716f572eb16cf394116240b351601716815c25b301405879c13d5d16613b62c2e139f1ae5126e267a120ed3da11d4367011b41c7a1099c8601091229d104c16ed0fb43ea40f4357ec0f2257630f0fe53c0effd3100ea5326a0e0257680ded5f0d0c933b900c636f560c5a7ad90b4f012d0a5baeea0a5681a9099604aa09920bfd09623c41095b00930808e46307f6a168074373c7072644b70724f7e3069c4d33067d9d93062a480905c4275f04865e870443de79037d215302f727a802dca3a002720f090179dd1400b4d761008f524c006470ba005369ad002cbb5f0017de53
|4,1=>0xeb14dd16d5dba21bbbd0bd52b90a5e1fb304da86aac56b0a9edb0c34981a8147980b421a979619d3965828849417f04f90ae43f58bc8dfb087e6499883ba2f3c83acc774806e89b67e3b4a537d8263127c5f738c75774a2673b6f0937320cde371d0714d719717ab6fe54a376f1d5fb76e4495ed6ccecbec6c6ba2ce6ac17a116945acfc68c363cb683e42736677a2816445b68e6431a6836428210962a01f765ead4e805e03bedd5cdb25bb5caea8fc5a1d6cae57503a405730e544570a3fbc559590ae551d8a4a5456b7525298cee1524c756d510d883250e988cc4f3763584af85ac549a39ef248f142124895639c47d79f1a47829a6b47736fa646c3bb0646a2913445ee67c045658efd45153bd044b1597b
|5,0=>0x1f98cae31f578da41ecc876f1e88faca1e2a3c7c1d7d57ab1d4accd71cedbed31c3e872a1bfea2541b20deb31ab629f71a92429c1a79ed131a6e4e961a4225c619674b1218874a97180f977317fa5bd417d439e117aec5791767da031729358f170d17a416cafe94161cc14316187ccc15ffcb4015b18a2f15acb727157c924d157750ca15386c3714a691f7146266ae1452320914313dd81422cecd13ded272138346ef136b1267134eceb7134d03c513498b201347c3c2132be0451314d20a12d601c912d5676c1260bdfe12483c3f12377128122d947911b9d9de118b2a751135b17d1120911c110e994010c157f610389a47100c6b930f354f3a0f2612410ef8541e0e83f7e50e80a81f0e6d39770e33b43b0dbaa2400d4466320d41b1970d29341c0ce130e40cbdd6eb0cbd6a9e0c9b81e60c9261e00bff5cdf0bb508d90bb454fd0b71c62d0b6492520b4000760b31de840aa6debb0aa1e3370967434809606f8f0931a3dd0918569a08d7399a0880cae808480d06082d3bb0082cb2a9078db4ad076e54e807269bbb06dccacf0602de5d05cb7e2105c60ffd05c51afb05ae6512056db486051c2402050eae8104d5d06c04bd4783049d822903c0f68b034d355602e281c802d0b78c027d8ce802795dfb0243a90301f1f94701eb3d65014e4e57014ce66b014352d90128bc9b00ed39e400e163ff00b71b7800121cc0
|5,1=>0x7690846075996e41713aecdf673055836641537664c36ba16377abe863089a2962fd812262efc71b6226a441615c41ba614f3d2a614005205f7febc25e8ea46c5e25b2eb5de8bce75dcfb8f25da33a355cf4cec35c7637c75bade3035ad564ce582df3de570a3fbc5682e8ee55ff75ab52e7e78d52d6927a5279df8551c8754f509100a4500deaf04fee9e374f64fde54f0039e94e7f7dd24e7420604d96d09a4d5c84914bd2f1294a8a90e14895639c44f7e9454496abb0446a3ef3446639c643592729427dc5f7425b28c0420d1f0b41fe5d1b41e1304541b826be416107c7402fc06d3ecc100e3e73f66b3e14c4673de21dbd3dd0f03d3d58c2f13cd9fc643c3e50cb3b3d4e333b119ada3afcc8723adb68233a94ae7139cb14e439981e00381dd95a37ab080337877930359b38fa354d5f6133da6f443339e43332ea8ff4322ee7642f5e57122f3d66202ebfc7192eac4bf52e9ba68a2e1fdc4a2dc891d02d854f712d648b0a2d3009212bd535ae2b6076df2b1414a12adc29952a96e4c32a7ea73829143c9a289fde9c277621ba2739cf1e271c02e026d795ba2609498825fae30625d675152575451525583eeb249a017f2487ab532483306f244a84bd240681a2238df6d822b62cdd221c622721d17b08212e498e211ae3ed210fac552078f40e20731fb3205b12cc2053f103203c741b1ff5b3881fea01171fa9daf4
|5,2=>0xcfdd3a9dc8114274c41a36d8be8e06e7b4f8c76baea4f9cdacb458d5ac520a3baa762056a75b5baba755bd53a6b2cef2a6a9ff26a05ae8bf9f3ea8229e4c4eeb9c209815979619d396489a2e923731848c770b268b677b58894190cd89299ec789114d668894ea7f852d914d84e6b9ea84b96e9d835abc047b05520a78e2d606
|6,0=>0xbbbc499caa7058ae9bc5e50594891ce4928010ea9185cfda8f6d2d8d8bf6bb2a88870dd7791f1f0e788c9c03767dbf456a12692562c64a3e5cf7708a5a8436fc5a5d08b44f64fde54f0039e9489a59ed44ecac6d44e5385d42b403ca3a170b4b36b25e0b342dd78032ea8ff432acd744312d15c83059e93d2feb7fd12f9f757d2f64ea6f2f3d66202e0e656f2e07c6d62c4a52472bbd03dc28b930c1241a3226217e04941beb6c4a1aa0ed1a18135522180c391d17fa5bd4168075a914e0fe6e137fdc2e1108d4d80f354f3a0e8c6c060e5a89690c4f02e709dfeacd08df91c3084d2848082d3bb0076c3f66075a67fa073a97d4069e79f605c60ffd04de6d670349ac300029f61a
|7,0=>0xfe6d716edb303c9f9fb6d0a998367241578aea253f84ea353b576e7932acd74414de6d04058847cc
|8,0=>0x3b576e79
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xffff00008800ff0f0000fff00f000000f000fffc0000f0f0f0f000000000cc000000cc00ff8800008800ffff0000ff0033cc0000cccceeaa0000cc00ff0000004c004c4c00000000ffff0000000036cc000036ccfa0000000000cccc0000cc0044440000444422220000222200ff0000ff0033000000000000cc0000cc0033cc0000cc0066aa000066aaf00f00000ff0cccc0000ccccf0f00000f0f055550000aaaa33cc000033cc0f0f0000f0f0ffcc00000000aaaa0000aaaa3cf000003cf0
|0,1=>0xcc4c0000cc443333000000000ff000000ff000000000cccc3030000030300c0c00000c0cfaf00000faf0a8a80000a8a8ff0c0000ffc055aa000055aacccc0000880044cc0000ccccff880000ff8866ee000066ee77cc00000000ffff00000c00bbcc0000bbcc22aa000022aaffaa000055aa55ff00000000fff00000fff0f0000000f000faf00000f0f05f0000005f00ffcc0000ffccff0f0000ff000f000000f0f0ff000000ff00cc0c0000ccc0ffaa0000ffaaaa000000aa0033330000cccc
|0,2=>0xf0ff0000ff0000f00000f0f032320000fafaf3000000ff00ecec0000ececaaa80000aaa8ff330000cccc33000000ff000f0a00000a0a44cc00000000f00f0000ff0000000000f0f0ffff0000cccca0ff00005f00bb330000ccccb3cc0000b3cccfcc0000ccccff880000cc003c3c00003c3c00000000ff3c0e0e00000a0acccc000000005f0000004c0033c8000033c8eeee0000eeee777700008888ff000000cc00cfcc00000f00c0c00000cccc03030000f0f0ec220000ec22ff0000000000
|0,3=>0xffff00008888ff880000ff0030300000f0f00c0c0000000005ff0000000000000000ff00cc0c0000cc000f0000000f00ffc80000ffc830f0000030f00c0000000c003f330000cccc00fa0000fa0055000000550000aa000022aaf3ff00000000f30000000000cf0c0000cc0037370000cccc55000000000000aa0000aaaafa000000fa00a8a80000a0a0ffcc0000a0805f0000000000ff050000cc04ffc800000000f3cc00000000c3ff00000000ffcc00000c00c00c0000c00c033000000330
|0,4=>0xf7000000ff00c0c000000c0c00cc00000000f1f50000f0f0af0f0000aa000c0c0000f0f0f8f80000f0f0eeaa0000eeaaeeaa00000000aaaa00000000aaa00000aaa0f3f300000000cccc000000cc77000000770050f00000f0f0cf000000cc00e0a00000f0f0cc4c0000cc0000fa0000fafa880000008800ffff0000f0f0f3f000003300f8f00000f8f0e0a00000a0a0fcfc0000f0f00fff0000f0f00f0f0000000044440000cccc00cc000000cc5f5f00000000331300003300bb3300000000
|0,5=>0x3c3c0000f0f0ff0c00000000f0000000ff00fffc0000fcfcc0c00000c0c0cfcf0000cccc333300000c0cf8f00000f0f0fcf00000fcf0c0cc0000c0cccc8800008888c8c80000c8c8bb880000330077000000ff0073ff00000000fafa0000fafaa0a00000a0a05a5a00005a5acc880000cc00ffcc0000050488880000888866660000666611330000000000f0000000f0fafa0000000033ff000000000f000000ff00eca00000eca0aa2200002222f3ff0000f0f0ff0000008800888800000000
|0,6=>0x5f0000000080800000ccccffa80000ffa0eeaa0000aaaaa0ff000080cc222200008888ff0c0000ff0caa880000ffcc00000000ffccffa00000ffa0f0f00000fcfc77ff00000000444c00004c4cffff00000ff00f0c00000000778800007788666600002222eecc0000ccccaaff0000aa00f0ff00000000333000003330dfdf0000ccccf3f30000f0f0aaa00000a0a0fcfc0000fcfcffff0000a0a0f8fc0000f0f0c3c30000cccc55550000000000000000aaaa33300000fff08a8800008a88
|0,7=>0xaa880000aa88afa00000a0a0005f0000004c4c4c00004c4cfcfc00000000c0f00000f0f000cc0000cccc44cc000044cc22220000aaaa3f3300000000e0a00000e0a00ff000000000fff00000f0f0c0cc0000cccc0f0c0000ffcccf0f00000000aaff0000000000a0000000aa000000000f0005000000ff0000fa0000000055000000ff0066660000aaaaf8f800000000f3000000f30070700000f0f032320000323200ff00000000fafa0000f0f0ff8800008888777700000000a0000000ff00
|0,8=>0x88cc000088ccccc00000ccc00c0c0000cccc88880000ccccfcf00000f0f0222200000000330000003300080800000808030000000300cc00000000003fff0000000000000000cc00eaaa0000aaaa888800008800ff0c0000ff0033cc0000ff00ffa00000cc802aaa0000aaaaffff000030f00f0f00000f000a0a00000a0aa0a00000aaaa30f00000f0f000000000fac8fcfc0000fcf04c0000004c000e0a00000a0a3f3300000c000f0000000000f2000000fa00ffff0000aaaa008800000088
|0,9=>0xa0000000000f0a00000a0a050000000ff00004c0000004c22aa0000aaaa1100000055000c000000cc00afaf000000003f3f00000000fff00000ff00c8c80000c0c0050f0000000000ff000000f0af000000af005050000050508c0000008c00f7f70000f0f0f3330000f000bb000000ff00ff5f0000ff00c0000000cccca2a20000a2a2773300000000cc0c00000c0cffff00000c0cfc000000f000ff0000000f00ffaa0000aaaac00000000000ffaa00000000b3000000b300ff300000fff0
|0,10=>0xa0aa0000a0aaffa0000000000c000000cccceecc0000aa00c0000000c000dd000000dd0000000000eeaa808000008888ff0c00000c0cc4c40000ccccee000000aa000a0a00000000ffc00000c0c0acac0000acac22aa00000000dd0000005500ff0500000000aa000000000033330000330000fa000000fa00000000fafa440000004400bb0000003300ffaa0000ff0088cc00000000020200000202c0cc000000000fff00000000cc0c0000cc0c88880000aaaac0000000f0f008aa000008aa
|0,11=>0xc0c000000000f8f80000f8f80c00000000008800000000005d5d0000000070f0000070f0000c00000c0c00c00000c0c0770000000000e0e00000a0a0440000000000dd550000cc00bbff0000aaaaeeee0000aaaa000a00000a0aa8a00000a8a00fff00000cccf2f20000fafacf000000cf0000ff000000a088aa000000aadcdc00005050ffff000000faffa00000a0a0a2aa0000a2aac8000000c8000a0000000a00f0f00000fff0
|_,_=>0
def stPool:Nat → Nat
|0=>0xd0e06e070080c3e06038d848291a8044806028d02633030c80c1a008c46006008102606178b85a06038b0562a008804829038140c01140802627008004c070089448230080c4406108803e06008103c0700874381b0d00432060380430060085c04060b0042a06008502606008482206080040c0f070340c010602c0c01050080c090401c0206028100204018080200
|1=>0xd004c8060d004486300934c4060d0040c011a034266100980be07009788a0600974265c009340c5b0083426060d168b2060096080100095c8a0600958aa0700950a606250d80c0700948480628804260628004484f0080c9c062500448012693048011012c0c4a009242606009204806239188a062200448430090826062080480061f804023e1e8f0023b1d0342639
|2=>0x8f826244401c0213439a80e011201c0286429000c014220c480600a09022403200023c3f9f80c070094c48013e9f00c07009ecf413031e40278098180e012484cee060d00404013b1d4a64a008f44806009d00c07009cc0c4a391c4e00600810de06080042606370044806009b4524a0d0040c10361ac266a039a4d0060d0040c100099ccc0625004262703024ca06
|3=>0x9a900e013c04c48065183c48a20d81c02a10301c02a00989c0c984604d3e060380448074f004065303004b09d098913807009000c074d804480700a153424202640e01138192e1a0084c4e060b004800603a592a244a01802840981926014904c4801488d00c90250050a40438183401098911e07008900c8e00a083006038051a13198188e8c4589114070084c4889
|4=>0x122ec02245d004f854098180e2c1b0900c4a00ae42624032ac6413122e00e01098916eb60084c48065a8042645032d002131201966010988912071094c0c4a00ac83e060380524240301c02b1098908007571000cad00a5958240301c02131201918aa12019204a0084c0c1a00aa4264f009e1507f122640e011229c5207008180e01532942606080045024038040683
|5=>0x8f426060d005a2130301c02d009a1c34013c04c480655b3c26220333842400301d9a016601834011f04c0e01658f44806650042813032f49e01123240e014104c48b003b20304063aec02c6138183401098918a070084c48066200404060d00586270306986c2098a80e016084c0c1a00b002624038057ebe0306802245e81c02030c0440c07009140c2a2500426bc
|6=>0x301d760106a2c48e80380404065e81c0213738192601099f80e017301802e5721e856407181c021371018340112018200170891120700b500c0700b81be2403005bc3e09b740c07009000c1a009f026066e01c4213038047a60098180e016d8900c4a00b6826d90306802130306802d8121c00e01579a80c0700b5c26d66a81c02240311d56d4098900c0169b482607
|7=>0x44805f01379004f0a82281894017b84c489903804480600bd8781313bd434010101834013a84c0e011ebd17c0603804ea133f2640e01798914e07009000c4a00a3026f3123c802130306802f1298900c44008900cf0038040c0777804b0400301c02ee6601c02a8768ac54011f0f00c0700bb1d6130301dd46b0989080065504c0c440d00426240301dd206008a07c3c
|8=>0x1860800600b940c5b00b90f4533f01894010989d121a0084c480600c1048070080e0613810180e018089c0c1a4b0180e0155834260623a4a005325004f0a8098980c4f0084c0c1a7f8b8262403bf802130301c02fd139c00c1a0084c480679004304003804ae531201802561201802fc6b84c0c016181026247d8049a13123e802f9138900e0101900be06038042624
|9=>0x878180e010101834014b04c480603c38306f0301c02240301c02d40c1000c017e0900c01533e40c0700834d6180301cd86b8689c0c1a009000c1a00bdc800603806180603804740d09891e4018584c48e303c28480700c250a240301c0308098920ebb0084dce065b0042627030060c2403004407c098900e01829140c4a009e00c07008b1d4243801c02761201c3401
|10=>0x98180e01502c826270301c02ea120180eef008f04806250055685098923606038048006038052c7a098900c0142468260603805d519099700c07009f026244a01c02af098900c018cc6026c7030680221098900cb600c5c48060392802a60989144060380426240301c0315120180e015345026240344c0e18200196801200180e018914e2206250042606038062013
|11=>0x23aad1813928180e01098900c0700bb02724200180e21098900c07918042624032f40e01098900e013e42e44240301c0296098900c079080426060380442f9098180e1a108b826240310c020e09c800c072500426240301c031f098ac54078f0043024538180e01098900c018cc7426060380442e4098900c4a00c702624030047c2e099a80c07009ec2627120188601
|12=>0x386802af3c04c480603cd40213120180e019a09080cc0301c028b1206c0e01999000c0725004b013120180e019804c492f0301c02131201834017e04c492e0301c0213120180f2d00cb04806038050413120180f2b0084c4806250065413120180e019484c480603ca00327120180e013e0900c0700b858413124980c070084c0c4a0d00442131231c0cb60084c4806
|13=>0x9d1000c0700884788b1206c0e018c84c48062d8680213120180e019c94c48062500442133f0180e015584c4806250041c13120180e0f170900c07254e002130301e64014184c44060392842531201894013e0908006038066e139b0180e1a009000c0700a14f013120180e014204c4887030680213200180e017c09080060380458400301c34014294c480625004e413
|14=>0x1201a861a0084c4806038068413200180e014604c4806790050a13120180f410084c48890301c0213122240e014604c4806038068013120180e019f84c48013b0e826240380556e609890813e0380516271206c0e01098900c0700cf44807250050b0b098900c017e4f0260603c580258098900c074d8058c24038050a13120180e019d84c0c07250045013120180e01
|15=>0x3884d6131201834018c0900c4a00a595613120180f490084c480600c64f948200180e014b04c4806038068e8b200180e013c0900c0700a09c813120189401a304c48400303c1c13120180ef200a2c48070080c26240301e8a01098900cb50084c562a039280213122dc0c07008900c4a00a5908240301c03443d04c48065d805f213121000e012b8900c0721804f413
|16=>0x938900c0700a148006250680213120197601a68900c0700a08f4130301c9401a604c48990380556240301c0283a59fc4806038054013888180e4a0084c4e060d00694131232436070084c4806252ac1c130301c02ea3c04de6240380474131201c02af3a84c4c0603804421312019b80700890800700a14bc13120192e070084c48065a0047c131221c0e013e04c4806
|17=>0xaa81c9401120180e01414642640350180e0109891c60700d504806250041c85098197a0700b902753120180e0109b9c0c07009e848870392802850c04c0c07008a04806250063285098900f52008e804240306c0e01098900c0700d4427250301c027809891ce0700c2c2624035400e0109890024d09b640c1a008e8262403005568409d3c0c0700d302606038069c83
|18=>0x301c0267098900d5a03804262403805cc13032600e21098900c1a009f0262420004763a098910e0700a1426245bac00e01098900e01a7244a624030a89401120180e4a009ac480603806b213120180e01ac04c480603805ee13ab8900c070084c0eb6009e15013120180e01a709c4806038050413120180f560084e220603804f8136c8183401120180e014119c2606
|19=>0x5584c480603806ba400301c0221610914e0603805c8131221c54070084c480600a987424033c00e01098180e011620c2607009e206a8098180e01462482624030063f19120180e4a00cdc2624035700e01120180e017020848060380442d4098e40c070d00426270306ab601098918e0600be026240301c02d4098900c4f009e026244381c0331098900c01420f82624
|20=>0x1201969620084c480603d7ec21312019e401099f80c0700a80260603804e458098900cb600aac26e70301c0278098197a0700c0c2624b00180e01630900c0700a0c4806038680359098900f5f3c42c26240301c0303098900c0700cdc26d6af0180e010989080066700426245b81eb601098900c07361ac26245801c34af098900c07460b826244c81c0213120180f2a
|21=>0xb40900e0142c2cf413121000c011a04c480603d880213120180e01b389c48060380696131201acc070094c480625005ee131201c02763a8900c07253bc0365098180e01a604ec8240301c0240660180e013c04c480623aad2424033c00e1a0084c48400316c02131201c02852f04cd4060392802130306c03194184c480625005ca13120180e01b184c48401481c0213
|22=>0x9892e4070084c48060380612131201c024b0989c0c1a00a9826240301c0371120180e016a04c4807008e8bcc6138900c070084c4806b801c0213120180f6f0084c4806b701d40531201894013c09080060390c0213120180e01b684c480603806d813120180e01b584c496a0301c02131201ad2070084c48e3038050a130301e2c011084c48070d4c616c6120180e01
|23=>0x98900cbd03804262403128023a120180e4a00a582624200180e018594c2624030a80e01098900c0700c7c2624030a80e018c84c48400301e2c01098900c07009f426240301c0379098900c0700a3426240301c037809890800679004480603c580285098900c0700ddc480700abd0a7a098900eae098900e1a00dd826240301c0375098900c0700dd026240301c0373
|24=>0x306c0e018c84c48064c01c0213120180e4abd8042624038050b0b098900c079900426240301c34019884c48060380442f8098900c0700a14f013122dc0c070084c4806038680285098900c0725004b08b1206c0e01098900c07009b026240301c0284098900c0700a9826240301c02858184c4806038052c3a09892f4060380426240301c0296a704c4806038697601
|25=>0x98900c0700c0c26240301c0337098900c1b0386802131201930070d00426240301c0228098908006038055e13120180e1a009d826240301c032a098916e06038680213120180e017b84c4806038047413120180e1a00a582624580180e4a0084c48065a00426245801d5e13120180e0110d8426240301c034e120180e014104c480603806543a098900c4a0d0042624
|26=>0x380426240301c023a098900c0700aac2624030a80e01098900c07008855613121000c07009ac26240301e2c01098900c070d0051813120e40c07008858c240301c0213121a80c070084c480603dec0213120180e01b084c480603928027c09890800603804d813120180e4a009c826240301c0285aa0900c0700d2c2624038055e85098900c075b004f0131201e630b
|27=>0x98900c070084c4806038066213120180e015784c4806038061613122c00c070084c4806038680213120180e010784c4806
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xf300c30093006300330003
|3,0=>0x10e410a4106410240fe40fa40f640f240ee40ea40e640e240de40da40d640d240ce40ca40c640c240be40ba40b640b240ae40aa40a640a2409e409a40964092408e408a40864082407e407a40764072406e406a40664062405e405a40564052404e404a40464042403e403a40364032402e402a40264022401e401a401640124
|3,1=>0x13e413a41364132412e412a41264122411e411a411641124
|4,0=>0x27d52785273526e52695264525f525a52555250524b52465241523c52375232522d52285223521e52195214520f520a5205520051fb51f651f151ec51e751e251dd51d851d351ce51c951c451bf51ba51b551b051ab51a651a1519c51975192518d51885183517e51795174516f516a51655160515b51565151514c514751425
|4,1=>0x3bc53b753b253ad53a853a3539e53995394538f538a53855380537b53765371536c53675362535d53585353534e53495344533f533a53355330532b53265321531c53175312530d5308530352fe52f952f452ef52ea52e552e052db52d652d152cc52c752c252bd52b852b352ae52a952a4529f529a52955291428c528752825
|4,2=>0x4fc54f754f254ed54e854e354de54d954d454cf54ca54c554c054bb54b654b154ac54a754a2549d54985493548e54895484547f547a54755470546b54665461545c54575452544d54485443543e54395434542f542a54255420541b54165411540c5407540253fd53f853f353ee53e953e453df53da53d553d053cb53c653c15
|4,3=>0x5155510550b550655015
|5,0=>0x693668d66876681667b6675666f66696663665d66576651664b6645663f66396633662d66276621661b6615660f6609660365fd65f855f265ec65e665e065da65d465ce65c865c265bc65b665b065aa65a4659e65986592658c65866580657a6574656e65686562655c65566550654a6544653e65386532652c65266520651a6
|5,1=>0x80f6809680367fd67f767f167eb67e567df67d967d367cd67c767c167bb67b657b067ab57a5679f67996793678d67876781677b6775676f67696763675d67576751674b67465740673a6734672e67286722671c67166711570b670566ff66f966f366ed66e766e166db66d566cf66c966c366bd66b766b166ab66a5669f66996
|5,2=>0x9886982697c69766971596c59666960695a6954694e69486942693d59376931692b6925691f69196913690d6908590268fc68f668f068ea68e468de68d868d268cc68c668c068ba68b468ae68a868a2689c68984892688c68866880687a6875586f68696863685d68576851684b6845683f68396833682d68276821681b68156
|5,3=>0xb056aff6af96af36aed6ae76ae16adb6ad56acf6ac96ac36abd6ab76ab16aab6aa56a9f6a996a936a8d6a876a816a7b6a756a705a6a6a646a5e6a586a526a4c6a466a406a3a6a346a2e6a286a226a1c6a166a106a0a6a0559ff69f969f369ed69e769e169dc59d669d069ca69c469be69b869b269ac69a669a0699a6994698e6
|5,4=>0xbc06bba6bb46bae6ba86ba26b9c6b984b926b8c6b866b806b7b5b756b705b6a6b646b5f5b596b536b4d6b476b416b3b6b356b2f6b296b236b1d6b176b116b0b6
|6,0=>0xd586d517d4a7d455d3f6d396d336d2c7d257d1e7d177d125d0c6d057d005cfa6cf46ced7ce67ce06cd97cd27ccc6cc57cbf6cb96cb27cab7ca65ca15c9a7c946c8f5c887c826c7b7c756c6e7c686c626c5b7c547c4d7c476c407c397c345c2e6c286c226c1b7c147c0e6c077c007bfa6bf46bee6be77be07bda6bd37bcc7bc66
|6,1=>0xd657d5e7
|7,0=>0xda16d9b6d956d8f6d896d836d7e5d786d726d6c6
|8,0=>0xda75
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 380 then fld (dictB (i / 512) (i / 32 % 16)) 48 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x122ac1201c0301e3501e0301e1201c038a31201c0301c0d0071201c03804098041201c0301e1201c1245b098685801c0300503804099d90306b0301e03abf030045801f0300503abd03004032310d004038040981d0306a032600d0050306a0301e03804098905801f03005038040981c0301e0301e03804098900981909805122ac03005582bf0300503004122ac0d0050d004120e80301e09a600d0051201c
|1=>0x9c2e03006120190301c0301e1201c1501e0301c0301e038040329b0986b122ac030061201c122ac0981c03abf0300409a9b0986b0301e0300400a9a0986b1201c0981e09abd03004124dc0301c09890038040d0061201c03007098901501e0301c1201c030690981c122af0380403a330d00409890122af09890120eb0301e120190301c0986b0981c1201c03cc803cc70300703abf03004122af12019120eb
|2=>0x1203f0981c09890038041201c032ad03068122af120e8122af1201c0301e120e80301e0d006120eb098900301e122af098e90301e1201c032ae098061201c0301e1201c09892030041201c12019122af5801f03005122ac099e11201b0301e098900981c1201c03abf030040d0071201f122af030690989003804030050306a03069122ac03804008e80301e1201c120040301e09890098191201c0301e1201f
|3=>0x98900981c0301e5b804030690d0061201c008e80301e09890030070300603abd030045801c03005098910d0060306a0306b098905801f03005202bd1201c03004099db0306b03abd030041201c0989009ac203005122d05801c0300500cab008eb120eb1201b120eb0301e120eb1201e09a620d0050301e03abd03004030680306903005030040d0060d004032ae038061201c038041201f1201c122af03804
|4=>0xd0051201c1201c030060301e03cc7030071201c03007122af038041201b0301e030691201c098900301e0986b1201c120190301c0d0071201c122af038040986b1201c0301e1201b032ad0380403804120eb0301e1201c0301e1201c1201c030060981d1203f038070301c098680306b1201c5812b03005098900989098c2d0300703006032330d004032980986b1201c1201c0986b0306b0989000a990986b
|5=>0x12004038040d0061201c098681201c0d0041201c0380403abd030045801c03005030681201c032ae038041201c1201c09890038070301e5801f030050301e03004120eb0301e0300703006120e81501e0301c0981c0301c0d0051201c03abf030041201c030040306b1201c008eb0301e030691201c0d0061201c09890038041201c030055801c03005030040300503804122ac008eb0301e0981c1201c0981e
|6=>0x30070300403006030051201c038070301e038040301c
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0x70800000000006100000000000588000000000000000010600000001c40000000000000000000000000000000000000000a400000000000000000190000024000000800000000000000000000000000000000000000000000000000000000000000000000000000
|4,1=>0x2e2000000000000000000000002a40000a08000000000000000024400000000000001110000000000000000000000000008080000000000000000000000000000000000000000000000f100000000000000000000000000
|4,2=>0xa480000001408000000000000000000026200000000000000000000484222000080800000000000003e200000000000000000000000000000000000000000000000003a400000000000000000d906840001910000000302000
|4,3=>0x1610ac4000000
|5,0=>0x2a114880005110000000a024d3259120c8a60002190000000000000000000000000010840000002010fc47a43c100000000003b11d08e440003810000000000371000000000035200000000003410000000644000000000000031100000006020001710000000000
|5,1=>0x23851848a2441218800085100021050268013f100000007c23d89e840000000001e080000000001dc40007610001d080007310001c84e2270100000000006f13691ac80006920000000cc600032898c8c246012f88000bc25c200000000005930001604000562
|5,2=>0x2d840000000002d456820005910000000000588800160200057100015a200000000015640000000001542a9153929840000005288001482a3100000014420000002844000a014f1274534697300025480000000000000000941498800124290200023c4000000
|5,3=>0x7a13c8800000078100000000007713b09d62e927318000000e427113845c020006f10000000db36c900000000006c0b54da82000698b449a020000003388000cc200032899040006388001886c31000000184200000030097e2be15e10000000ba25c8ae04000b71
|5,4=>0x440a1e200087080000010b384900020c6000828800000104100000020440000004008000ff17e90001f640007c90001ee4f61
|6,0=>0xbd15e0aee3752b995c4ade56e1b68dacad43682b31590ac45611af9574ab65592ab9554aa65512a7900029a54b2a4951ca8c345100050ca8254019f14f467653929b94d4a6653129794b4a565292939494a48323190948040011e28e146c63251818b14546283122
|6,1=>0x2fc57c2
|7,0=>0x3103871c30e1470838310006087023801
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xa659238a181f75c69961651349140f34b2892061440c2040
|1=>0xffcef5becaea
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x400000000000800800000000800000020000000000000800000000000000000000010000000000010400000400000400000000800040010000000000000000400000001c0040100000000000000000000000000000000000
|4,1=>0x1c20000000000000000010000800000000020000000000820020000000800000000000000000000000800000000810020001c0
|5,0=>0x104309a00200454d04001609d0000420000020070030040014440000040810130002003411c108104e00000f04d0021c30010006431c94c008000000000001900004459900001964d01900000200001a000002000140000002000140040000
|5,1=>0x470000800000410423c000108d1000400061400001030403417410020010010406806d900044000804e7c000504400100100001d0802000010403405401400000c000074514200034004e0403400050010814ca002000000002341101002000
|5,2=>0x310034000c0402407400010000400030010800c12802d9
|6,0=>0xe029a4569d22cd6617629906059d47273d09d030129e9e544546428e8cd9a541c54c28a59e8ca0859c20585de18e8c30d8
|7,0=>0x9679e72a39d88d8
|8,0=>0xa
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 6 (j % 128);fld (pmPalB (k / 32)) 6 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_45_2,6,runOps true dzo_45_2 (0,roots_45) ops)] else [])++(if pm.testBit 1 then [(dzo_39_8,6,runOps true dzo_39_8 (0,roots_39) ops)] else [])++(if pm.testBit 2 then [(dzo_42_1,4,runOps true dzo_42_1 (0,roots_42) ops)] else [])++(if pm.testBit 3 then [(dzo_15_32,6,runOps true dzo_15_32 (0,roots_15) ops)] else [])++(if pm.testBit 4 then [(dom_43,5,runOps true dom_43 (0,roots_43) ops)] else [])++(if pm.testBit 5 then [(dzo_46_1,5,runOps true dzo_46_1 (0,roots_46) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_47 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_45_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_39_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_42_1_1 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_32_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_43_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_46_1_1 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_45_2 6 s (0,roots_45) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_47 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_45_2_2 h
def symsG:List (List (Nat × Nat)):=[[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,30)],[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_47==dom_47) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_47 goalM v ys):RunD true dom_47 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 6 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 6 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 76 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 76 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 197 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 69 128=true)
private theorem z4:∀ i,0 ≤ i → i < 197 → Z 4 i=true:=(range_split z4_0 z4_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 288 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 32 256=true)
private theorem z5:∀ i,0 ≤ i → i < 288 → Z 5 i=true:=(range_split z5_0 (range_split z5_128 z5_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 66 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 66 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 10 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 10 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_47 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_47 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_47 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_47 roots_47 goal_47_0 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_47_0
theorem lowS_47_0:Lower true dom_47 roots_47 goal_47_0 9:=S_47_0.noCircuit
end Case1

namespace Case2
open Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def dom_13:=0x3333
def roots_13:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_26:=0x5050505
def roots_26:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_13_2:=0x3220
def goal_15_0:=0xeaa0
def goal_22_8:=0x540040
def goal_23_0:=0xee00a0
def goal_23_8:=0xfe00ea
def goal_26_4:=0x5040400
def goal_27_0:=0xe0e0a00
def goal_27_4:=0xf0e0e0a
def goal_29_0:=0x32222220
def goal_29_2:=0x33333220
def goal_30_0:=0x54444000
def goal_31_0:=0xfeeeeaa0
def goal_63_0:=0xfeeefee0feeeeaa0
namespace S_29_0
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(1,17),(4,5),(8,9),(12,13),(12,28),(16,17),(20,21),(20,28),(24,25),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_29.map (· &&& dom_29)
def goalM:Nat:=goal_29_0 &&& dom_29
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x83148db1045eb9c4
|3,0=>0xe8a74740865805664ce5c9db4658d5063537a6e520703c3a1ca9f09d1aa2ff7f159ce3aa1352da780a3445e4
|4,0=>0x8658056674bc402643d60cad3109826f2e4aa4b60e367e880d12eb640a23838c
|5,0=>0x86580566
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xccccc0c303000000000888a2002200444400033223322ccc0ccc3000300000cc008b0302020440044000220022cccc00c10103030c000c0c333322228888000030300000000c0c33332020c0c0c0c222222220cc00cc33330000cc00cc012121212
|_,_=>0
def stPool:Nat → Nat
|0=>0x20948209499104a4104b82082525c41292c209495104a438a8129053910412904524441810457b9a12904123041591412a42441cc12904418820
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>0xb9152264448790d216424839052064
|4,0=>0xaa94165ac6582af15bab25
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 26 then fld (dictB (i / 512) (i / 32 % 16)) 30 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_29 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_29 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_29==dom_29) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 goalM v ys):RunD true dom_29 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_29 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29_0 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_29_0
theorem lowS_29_0:Lower true dom_29 roots_29 goal_29_0 6:=S_29_0.noCircuit
namespace S_13_2
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(4,5),(4,12),(8,9),(8,12)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_13.map (· &&& dom_13)
def goalM:Nat:=goal_13_2 &&& dom_13
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xb9ef265f
|3,0=>0xb9ef265f
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x3300c0c2222
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 14 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_13 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_13 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_13==dom_13) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_13 goalM v ys):RunD true dom_13 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_13 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_13 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_13 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_13 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_13 roots_13 goal_13_2 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_13_2
theorem lowS_13_2:Lower true dom_13 roots_13 goal_13_2 4:=S_13_2.noCircuit
def isoMv_22_8:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_22_8:Lower true dom_22 roots_22 goal_22_8 4:=lower_iso isoMv_22_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
def isoMv_26_4:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_26_4:Lower true dom_26 roots_26 goal_26_4 4:=lower_iso isoMv_26_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
theorem lowS_23_8:Lower true dom_23 roots_23 goal_23_8 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa00aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_22_8
def isoMv_27_4:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_27_4:Lower true dom_27 roots_27 goal_27_4 5:=lower_iso isoMv_27_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_8
def dzo_13_2:=0xcccc
def gzo_13_2_2:=0xc880
theorem lowSh_13_2_2:Lower true dzo_13_2 roots_13 gzo_13_2_2 4:=lower_iso (d1:=dom_13) (roots1:=roots_13) (T1:=goal_13_2) [(dom_13,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
namespace S_15_0
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(3,7),(3,11),(4,5),(6,7),(6,14),(8,9),(10,11),(10,14),(12,13),(12,14)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_0 &&& dom_15
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_13_2,4,runOps true dzo_13_2 (0,roots_13) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_13_2_2 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_13_2 4 s (0,roots_13) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_13_2_2 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_0
theorem lowS_15_0:Lower true dom_15 roots_15 goal_15_0 5:=S_15_0.noCircuit
def dzo_26_4:=0x50505050
def gzo_26_4_4:=0x50404000
theorem lowSh_26_4_4:Lower true dzo_26_4 roots_26 gzo_26_4_4 4:=lower_iso (d1:=dom_26) (roots1:=roots_26) (T1:=goal_26_4) [(dom_26,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_26_4
namespace S_30_0
def pairsG:List (Nat × Nat):=[(2,18),(6,14),(6,22),(10,14),(10,26),(12,14),(12,28),(16,18),(20,22),(20,28),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_30.map (· &&& dom_30)
def goalM:Nat:=goal_30_0 &&& dom_30
def NN:Nat → Nat
|_=>0
def HT:Nat → Nat → Nat
|_,_=>0
def dictB:Nat → Nat → Nat
|_,_=>0
def stPool:Nat → Nat
|_=>0
def stOffB:Nat → Nat → Nat
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 0 then fld (dictB (i / 512) (i / 32 % 16)) 1 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 1 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 5 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 1 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 4 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 1),wireSAt ((code >>> 3) &&& 1))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_26_4,4,runOps true dzo_26_4 (0,roots_26) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_30 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_26_4_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_26_4 4 s (0,roots_26) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_30 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_26_4_4 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_30==dom_30) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_30 goalM v ys):RunD true dom_30 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_30 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_30 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_30 roots_30 goal_30_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_30_0
theorem lowS_30_0:Lower true dom_30 roots_30 goal_30_0 5:=S_30_0.noCircuit
namespace S_23_0
def pairsG:List (Nat × Nat):=[(1,5),(1,17),(2,18),(3,7),(3,19),(4,5),(6,7),(6,22),(16,17),(16,18),(20,21),(20,22)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_23.map (· &&& dom_23)
def goalM:Nat:=goal_23_0 &&& dom_23
def NN:Nat → Nat
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0xb98739f5
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xff0000f000f0cc00ccaa00aa
|_,_=>0
def stPool:Nat → Nat
|0=>0xe4
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 4 then fld (dictB (i / 512) (i / 32 % 16)) 24 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 2 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 7 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 2 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|_=>0
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_23 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_23 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_23==dom_23) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_23 goalM v ys):RunD true dom_23 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_23 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 1 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_23 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_23 roots_23 goal_23_0 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_23_0
theorem lowS_23_0:Lower true dom_23 roots_23 goal_23_0 4:=S_23_0.noCircuit
def isoMv_27_0:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_27_0:Lower true dom_27 roots_27 goal_27_0 4:=lower_iso isoMv_27_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_0
def isoMv_29_2:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_29_2:Lower true dom_29 roots_29 goal_29_2 5:=lower_iso isoMv_29_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_8
def dzo_22_8:=0x55005500
def gzo_22_8_8:=0x54004000
theorem lowSh_22_8_8:Lower true dzo_22_8 roots_22 gzo_22_8_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_8) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_8
def dzo_27_4:=0xf0f0f0f0
def gzo_27_4_4:=0xf0e0e0a0
theorem lowSh_27_4_4:Lower true dzo_27_4 roots_27 gzo_27_4_4 5:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_4) [(dom_27,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_4
def dzo_23_8:=0xff00ff00
def gzo_23_8_8:=0xfe00ea00
theorem lowSh_23_8_8:Lower true dzo_23_8 roots_23 gzo_23_8_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_8) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_8
def dzo_29_2:=0xcccccccc
def gzo_29_2_2:=0xccccc880
theorem lowSh_29_2_2:Lower true dzo_29_2 roots_29 gzo_29_2_2 5:=lower_iso (d1:=dom_29) (roots1:=roots_29) (T1:=goal_29_2) [(dom_29,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_2
namespace S_31_0
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(1,17),(2,18),(3,7),(3,11),(3,19),(4,5),(6,7),(6,14),(6,22),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(16,17),(16,18),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_0 &&& dom_31
def NN:Nat → Nat
|2=>4
|3=>47
|4=>226
|5=>438
|6=>187
|7=>24
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xc54bcf16a243e0075e483e851d10cd2f
|3,0=>0xcff5d3ecbe228f98a6edf9749fb3a03e978c9fb7933bc6c68b62dac183ad25496c96a30b6b7090ee680591f3671ead68662f2617619a1739615a82ee61505e2c5e4c53515da8fd374cd5023d4a191b6046fa4512453a62ed42bbd8253e8563cd3bc60e9c3a71281d394d67da37d66292371002fb321543812e3453572d8a0e452be1abbd29893cbe2788e9521f597f811dde67ef1a9bdefb19b4f7a8156fc58413119b3d113ae45710ab6ed70b26ef5607e3f72d079900be0672d874
|4,0=>0x5688d1d5565f41575601c9865564bb7255572d025548a99854faa626549deb2f5433b5d1540785fc536da4f7508cadf84db85ab84d1c67c34cd3c8534ba284bb4b41a5b04aa5f9c94a2030244a08ac6049b8a47e4913efec48eabe8948d486e04890ac3a47ab4461472553af46370c724480cc21423b9671414e41fe3fe1811d3fd2b3553fd03fc03f9c81bc3f2c6a703e1b1abf3db3243c3ba6254a3b89e5ff3a3010433895d721386acc3e3665bc8435320baa3520d90334ec33a53476ad5e33ec8d3d3393229c3323df3a32dd39c63201b7e93168ee1931435d37309739d93046a037301e69ba2fa823e32f2675922cd112912cb644502b8910672a62e81d2996df2428881a5c2856841228045d3d266ac617265bbe57264aacda23d0c22523be2a0a23ac3cea230fb29522844dea21df95cf214c89cf1f3b2d251f1938481ef9d35d1e781c9f1dde67ef1dc0ca9f1d7f5bb91cc658b61ca6ccbb1c3622d51bca36001ae9d3d21a1b5eae197998f419629db1189c4d351888cd1a183a375317fcbcf917f20b84178caf1b172dc58a1721e1451651cefe163ce418160fe99e15aea1aa1581cba411d4a3d211bca25e10e0f8130f47ace90e95c9f20dd0c53c0bcdac7c0bcb30b009df185b096d95de093086f90814333d07fcb05207f5938807b11aa7065bb6f905c8191104c297ab0479181602b24f6b01e65b6a00017a7d
|4,1=>0xff5e15baf94c1570f8078e8bf536a6dff39e311dee40bf51eb7e8c98e8e9d742e2d20566e268c367e1f41955e10c1333df8bef1adf12d2d3db81934bdb4dcf9dd9521e21d50a080ed3854b10d2a13e10cd2aeac4c9aecd25c920e23ac880bf94c70e3c0dc05fd933be15f70cbc65c425bb15a33eba3f7d71b9ceb912b87e64fbb80f843bb7ad5e91b77b94d8b671e6f5b382137db2ec2b0cb1c3e0dcaf631aa6a73316d0a62ef6d3a5ed6a75a13b7858a020f9209ec682e39c7721ab981fdbb396fc6fd6948ece2490f84e6a90378ca48ed99d898c4064838ba2056e89f7f247898b23b086f66efc86cb1d9986856b88854ecfac84c6cd0383471d7d81ed4c488106b7ab80f18c6880d48b487cfea5077c45fdcc79f5538e79bef57478e5d41878bd6e307718b71676dd6d8a766de0ce74c145257371314671dcc57e71c31bfb70c41c7a6ba4262e6a81649168ed873b68c46f746890d4ea65af13e8652174aa634c7c5a62d0254f6273eddf617e4acc60cd72c35e7533f25e46a5fe5cabb78859d6400d5950245e
|5,0=>0x2687932226459f34254d28b1252796d1251b3b4324fd62b824f97944241448e0240d8b88240cc3eb23c9b0e223a68e3d23439fef232ff52823269a28232697d922fe11fc22888f8c228408f72254f67621aa4f512172df1b215e695d20328dad20212b0920084a331e9075211e489d4d1e012f001dedd7871dc83cfa1d7f5bb91d41a3051d2275031c9d34911c77b5a01bc09f241b9f46241b0358021af5a9aa1ad5ead31aaeeec71a30055d19e421be19ccc01e199f328e199abba7197507f61960f370193c0e4418e5eeb6184a452f17e3ce9917afaa5517a9ccea1757f7b91674a63f16458e301601b38a158854d81585c5021516daa71506f0ca147cdb0e1442cb061399108312a984e312a8ee7711f747091141317210efe97d1081f18d0f8132da0f002be90e3925870e1b53ae0d8cbd270d2b81f70cdec94d0cca5d2a0ca0ba860c39a23b0c19c63b0bbfd2620b8630760b859ff30b8523220b82be3e0b726d460af8c57c0a9327e409b71d7b09afb07d0964c27809592de1090060e708ed0bf308dd7da2084bdf690843a76f0838847f082d1ee40803aa5b06ede68906d2f52206c0c2db06b483420696a89d065e29090640b94e063e19b505d9187d055409fa054221c704a56fc80434110f040b3db90398b6d701e0d145016d92120114eff000ed62ef00dc4a1200d6aac400cb1a3500570e2b0046f4b60005e794
|5,1=>0x5d8d85835d51b01d5b5ed8a75adca08d5aa3dacd5a379a0a5a0c325658937c70583705b8581e847757ed152f57dad993570680925705627e565349ba55cef0d0556b85ef541ed8c0540785fc527ea26f5223e11a5207303c51d1493250dacc1b506d53ad502d3f544f96b06d4f5e53984ee59cff4dfa6d184dd7fad74d9c88004d831e704d0930a24c8880ec4be91a194bc8fc3f4bc5935c4ab190e84a77aca249e1a73248773af648666ef147f935f2476754ef47256c6946f158b246eb458c46601b224656db6845e30b2445d287d2453e13f743cab68a43c09be843897dda431deb01430c83f94307246542292037417027cb41088dd540c20d1c3fecef013fb5070f3f8bba8b3f28308d3dc7b9163dacf2873d54498d3cdcf3663c9cfad33c7656ab3bc019b63bb221af3b49228a39ab8f23396f874b392492a138e89bda38c49e9138b77c213873b6c6380d8fb337bde90e37b1fffe378ab6123745d2ac3673b32435b5e6c534cb8c5d33af60193361118e3349baee3263407831faa9a731b1baed318bef8b31283349311f2159311274c03100485330fdd29c30c6e64e3046a037300207d42f85b4322f39ec6f2f3177ac2e6c6c0f2e6a8a592df97b672dc0bcd32d92e0092ceb07162b88c2252b209e822ad95bcd2a96e6c92a5caa8929fd635529a16d5229141a6228b1add528a5dfd9289c9507285684122829abae
|5,2=>0xadfe94f5ad3e8844acd54760abe2f73cabaf62b6ab2cecb8aa226dcaa9c1b7cea6bb0535a69b29f1a5c68f7da4ab08d5a4649c60a3dd0af1a2dee3f7a21326d9a1afea60a0c5401f9ebff2249e6e4af99e4291d29d72ffe69d277c629cd5e3c19bb361bb9b11c62f9a19852c97b8ba2097898185963376b095d97151953b56df951e490a942fb7359420197f941bf36193adbdf192580d1b90df6b85903b97678f4bd6578eb0c02d8eaa40c08ea91e798d4d92058d272b098b2e49b489bb14b287f50b0787deda818784f84a8758390886d335778663fd8885e5c09984920124831c5169828e879881f04f20819fa6db817af2b0811ebb7080ead4d080e48c5980906d03805559377fe116217f04d6617eb9dba97e3b8a5b7d5169007c3564527bc8b5e57b63edf3794fb1037876cea27837384077b5d47476a37afa7521e344749a54417372e193733b2dfc72ce72ac729b5cea71db98bb70fd1b66709f56a56f7717e56f3772156f0d47df6efcc0aa6ea31bd76d6f1d036d2a97be6d24d0946cc496896c80bbe36c3153126b9241616b19ad756aba06bb69fe365469f8ebd369f0834769e692e469dec52a69996eca6902527e68a8efdf67295bb066f8175166c290d0658bf4f4643ac4c363c90a0663192b69628f8b6561d839c3616f74bd613162ec6052e0565ffe437d5feb76b35fdcd7955ed4a50a5eabd1f45e6955ba
|5,3=>0xff2e3ab3fc2fe23bf83017e4f6767ddbf56be69ff555f6abf545783af3bc1a1cefb8dc81eecdfda7eeca1433ec658252e728f097e526253de264b1f3e0a7d313db17c451d9448a4dd5d67c54d4d421f2d4a232a3d3150e8dd2c8117bd09b624ece474655ce400decce12aa8ecd33e168cc8e5474c9c8a910c874c52ac4cec356c4a3e741c3f36677c0927103bef02a58be32de3dbae03efdb909b478b8760e6bb835eec8b7ee7d16b7db4d7db7a3286bb75c608eb58372c9b4e85e13b47d5b59b3d0b876b27fe350b157e592b0fd4e37b03e20e4b0290123
|6,0=>0x922a2e5090a07136904980188f9570a78d2f93368cf1d972892610a88765ed6c8692decc8331771e812b82c580efcea87fe116217f2d989a7c2eb45a79238a6e78deacde745f33c174064f5d71732e196f89a1c16a1bbc4866df346c64400b45642b4f8d63dcfeaa62bee6be6294c3f261a6321d5f84236f5f4048c95d1dc51e5d129b915cf6f3ef5bed828b5aa3dacd59b24c68592043355836681f56c458c6569c8b9056832b8c556b85ef51a243e150ce08e54e7d552d4c7b51494c35739b4c1113e3489b25d1469194cd44e04f8d44b7c790431deb0142c210404268d4dc3f4a3df73f28308d3b48076237d49b57378ab61236eb4c6e3673b3243646b8aa35e7b9213542372833c935fc3349e1f533445ff732ab71923213461930d5ae122ee8d5252ea1a60e2d9fc0262d0a477b2be693e62b5199d62a305cf828bc231828ae69ed2785873c26de1cbf26d55d0d2581e49d238725b1238307f12382e75722c5a1b5220d77ad21b4f2fa20d08b5f20b0149c1f7108561b25f3a91b0358021af425c0199abba7193c0e4418a6ebd11727f37417232ed7164de1ce162fa60516032cd515ecb7e815dede7515af50bf14e19db81495c97612a8ee771141317210efe97d0d5df6510d2b81f70c5ebf740a03e2b509a0ff5b090f691808f6698f08669b7e086127e6081d8fae072515d905aa6454055409fa051c01440046f4b6
|6,1=>0xfd90d141f466fa6bf3bc1a1cf2c3a399f290fc61f114d409ec18059eeb858de9e98fcadbe86364c4e81ff617e631ca24e526253de4fb2e48e4c8ff09e3f418aee264b1f3de4158b8d9c4f616d8f0e129d869ccccd3e5f5cece6c23d6cd96d6cdcd3587faccac53a3c85d9b0cc7f014cdc4c918ffc2f34662c0a4267ebfced975bf55ea1abdf5a666bb285d15b98e8086b803f3d9b7db4d7db600566cb58372c9b4374d10b30c4674b2b1ba1ead2136f0ac6dc52babea8af4abde234eaaecc24aaaae09fca941d0dfa7a7eaf9a78f0814a74692fba6bb0535a5ec9609a18c65939abc05fe9a48487798993a0a
|7,0=>0xe39fa026d5d7a2ced4201d1eb98e8086a78f08149069c14a8fd54a87894af9796432baff579c512c569c8b90519fbd2549a52f422e0794482c56ab27258c480e21a8620b20b0149c205f4d0c1f16380d1495c9760d59fc0a09e2bbbd090d6eb4
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xccccc0c0fafafafaa0a0a0a00ff03ff0ccccc0003300ff00f0f00ff000ff0000f00f000000000ff0faf0faf0f0000f00000f00f0ffff03305500550000aa00aaf0a0f0a0ffa0ffa0eeeeeaeaff00ff00cccccc005a5a5a5af00f0ff0ccccccccaaaaaaaaeeeeeaaef0f0f0f055aa55aa3333ccccffff0000eeeeeaaa0ff00ff0
|0,1=>0x333300000000cccc5f005f00ccccc00c0ff00000ff0ffff00f00f000ececa0a0cccccffc1a1a5a5afff0fff0f000f000ffff0ff00fff0000feccfa000f5ff0a00f0a0f0affffcccccccc0000fccf0000fa00fa00f0f000f000ff0f0033336c6cf0f0a0a0f0f0fff000fff000112255aaffaaffaaeecceac0fffffa00faaaaaaa
|0,2=>0xa0a0f0f0f000f030eeeeaaaa00fa00fa00f000f0eeeeeeaaff00aa0033333222ffff0f00bb33aa00faf0fbf0eeeeeeeeffffe000f000fff0aaffff00cecece0afafaaaaaff000f00faaaeaaa33333000ffffa0a0faaafaaa0000ff00ccccc0cc00ffff00fffff0a0fcecccccffffaaaaeeeee000ffaaeeaa0f0ff0f00cccc0cc
|0,3=>0xfafa0a0affff00f00f0f00000000f000cf00cf00afff00000000f0f0fa000000f3f3f0f0b0b0b0b03333302050505050ffffeecccccc8800ccfe00faf0fffff0aa00aa003030f0f00f00fff0ffffff00ffaaaaaa4444400050f050f0ff00fff0ee00aa005f5f0000f0f0000011005500ffffaa00aaaaffaaaaaafafa00ff00f0
|0,4=>0xcc00ff00fffff0000000ffaacccc4000aa00faf03020f0a0fa00ea0005ff0000333330f055ff0000ffff5500ffc0fff005055050ccee00aa0fff0ccceeccee0050f040f0302030200c4c0c4cfafaeaea0f003f0044444444e0e0e0e0ff00f0000f5f00000000f0a00000fff0f0f0c0c00f000f00ff0fcc0cecececa0fccceccc
|0,5=>0xf00fafac8c80000faaa00f0f0000fffff00f4444444afaffafabb33bb00ff0f0000cffccffc00ff55003232fafaafaff0f0ff00000000f0f0f00f0f0a0a0000feee544444443320ffa0f0a0ffa0faaa0000ccccc800ffa0a0a00fff0aaa0fff00f0fffffaaa0444ccccfcccfccc11111000f0f0e0e000005500fa0afa0a
|0,6=>0xf0f0c0c5f5f4c4c0cccccccffffc0c0f000ff00ff88ff8800cc00ccff00cc00aaaa00aa0000f030afaf0000feee0000bbbbb000ccc0fff0cccceeaaccccc888eaaaeaaa3c3c3c3c03300330aaaafaaabbbbbaaa103050f0333310000000aaaaf000c000aaaa55aa044444440a0a0a0afeeecccc0ccc4cccf000f0f0c444c000
|0,7=>0xf00ff0000f050f0cc88ffaa33f300f0ffccffccfac8fac84444f4f4f0ffc0cc30303030ff30ff30afaaafaaee00ee00bbaabbaaaa00fa00c0c0f0f04f4f4444fffff0f00050505050005000ff55cc44aa00ff000c0c0c0cf300f300c000f000000050505050f0f0aafafafafafaaafa555500005555aaaabbbbaaaab0b0a0a0
|0,8=>0x7700eeaaffaaf500f5000000f0504c4c4c4cff0aff0afaf0aa00ffccff005555005033332020ff0fff0c00f0fff0feeefeee54445444f0fcf0fc70707070fcecfcec3f000f00ccfcccfcc0c0c0c0ff33ff0051515050ff00ffa033003300c8fac8faf4f4f4f40f0affaaf0f0f000f00000004444cc448888ff883b3b0a0a
|0,9=>0xff0ff000fff0ccc055004400ff00aaaac4c4c4c4cccc4c4cff44444455555000c0f0c0f0550005000000b0b05f000f0044cc44ccf300f0000aaaaaaaa0f0a0f0eecceeccfa00fafaeafaeafa04cc04ccbabababa1f001f00450045000000a0a00f0f0f00fbfbfafadcccdcccff0a0a0a00005f00afffaaaafff000f0a0a0ffa0
|0,10=>0x32223222f0ccf0ccffff500030003000baaabaaa00500050fafa00fa0c0cff0cf0f0a0f0aaaa0000fccccccc0eee0eeeffffafaa0a0afafacfcccfcca0f0f0f0f0f050f055554444a0a0b0b005550000fcfcfcfceeeeccee0cfc0cfcf555f000ccccecec4400550011001100a000f00045444544f333f000e000e000ff005500
|0,11=>0xeeeeccccffaa0000cccc00cc55445544505000000000aa00fc00fc00ffaaff00cc00cc00f3f0f3f0cccceeeef0fff0f0fff000004444cccc33303330cc44cc4432323232cccc4444ff5500003333303088888888aaaa8888afafaaaacecececeffff00aa00c000f0cceecceecd00cd000a0aff0afaaaffaa00005000f000a000
|0,12=>0x222222228888aaaa000000f00000cc00
|_,_=>0
def stPool:Nat → Nat
|0=>0x170c40a07060200e300601c062f170305a0a160200e00158140e03150200e29060140e28010304e0d130200e250101410240108c0a22108800a08010303e0a060783a03010200e1c0106c0e0001020141a010300a010c8200e180b8200e16060540e030a0200e13090200e00028440610010301e01010380a0d0102c0e0001030160a048200e02030000a04018080200
|1=>0x78200e0c029580e3e01030aa080394c18052a01c0a080389492530601410070282c0e470114868080381410510380818052801c040e2781410022703c1007010d49a080101c9800259281049029200e47230308a07220300a43011082a080601c8240028107e3e0281c7a03010f00e00198200e3b1d0200e39170303c38010dc0e00010301036010d46801198200e32
|2=>0x238084608379b804340401cda6c358780a08010300a0735008100734868d00c0401c820211814ce08060143e073311818650401c040504190206306014106206020c20720830100720980042b0401cbe050401c5249010d4bc08038b80a2d0397018140401c820202974105c0103c10070d03010072096c880206014b4022c9280a08010304e1f03808180503960ae02
|3=>0x410300a2d0380818050d81c040c02a040e020607c0e6901031000503808187f041d00431028200e0c0a81c7e3e3f0300a0b039a010073e9f0040f3d8200e0c041e80e79109e00a080380818773b01c040f2a01c9205088fc203e010301e073a80818050081410073a11c040f0401c92020603c3e07011280a5424808180816828e60c029c80e02029c41007380141007
|4=>0x3a286449060783a3f1f008181e1c020040c02a400e0c1a0200e41010301007478081807472340a2a0401c8e2e0603c5a07221f818052a008188c04074040803a2cb60206128a889010301e5d040300e8a20808184a4482018880401c8202060800a080105c100700030100743a180a480386092340401c64852583108080380810071f800040c040287e1e028200e47
|5=>0x401c5605038fc7c02159dc100701030541f03808fe2b0401c040c0290c0e021a0200e9b0108c180506808180803a68040e0401cdc021a8d016070102c0e832d80932050401c422b0401cf2020613c1e080281d14472481410074c124040c0281d2e0c0287c0e964a9640a080380928340401c180803905260202a481011170305a07348086a0803a44040c2e820d205
|6=>0x10303c272a0cc040803800040c029515002060800a8a010302a0b03808180506874180803a9cf20c3287c0e605300818052a008180503a9404a40401c0002060140ea325831440803814100723a84040c040287c02060146801012801007248300e3f178f8040f0427c0e9e010200e004f008180500808680803a14045902820c40c02974109d010300a9c038081c84
|7=>0x3282008020287c2210010303208038084605059bd6e0c0282c0e9e0609c1007012d81007001640a0803ad4040c04075680c042cc0e790281c7a3f1f008181e0587404b2028200802158200eb1158200e983c808181f03ac018050401d5e02060140eae01014100756809580f0401c1808039042644062ac0a08010200e6e2e00856055501c04351a06c0e02548303c08
|8=>0x2480818052d310040c618140e02060140ec2010ad8208038081007000ec040c02b000e23060140e03010200e32000b818151681d3c4406014a80206054ba08170145a11080a810070c2fc0408038002c0c5f0145a07258300a0b0380818052a2f40a080391d78050401d6a49028200ebb2480818ba0281c040c0a87c0e0c042e40e41010300ab8038b80405040100405
|9=>0x401c8ebf010300a5467808180708b3804050f81c7a020401c00cd4f0d010074280818052a330040c02b2c0e02590200e00060200e413e008180803b28040c0281d9202060800ac5010300a0d6400810740d310040c268141002060140207010305448038cc04340401c040c0f81c5e021ab1c1007010300a0863008180503b14960c0287c0e2e060785a1d010141004
|10=>0x3a2c040c02821aea1010300a0803aa0040c130200e79010300a0803b58ae0206014a807010300a0d03808181e0401d62020701410071f1b1640503a2818050401c8e02060a810075f83010d5039e4ae0206014100701030ee340401c04351a01c980c6a0141007010300ad30380868086901c96340401c92021a0200e16010300ad10380818056801c5c020401c0005
|11=>0x401c040c0282c0e740601410e2010300a087001c0a08038c8920206014bc080380818050401dbc021183c100724808180503b74044e028200e492b83164050401c04050401c7a3e01030b2052a01db80c028200e7901015b60803924ae02118141007010303c270401c04da028200e49011380a0803b64040c0401d06b1362c80a340401c040c2c8141007010300a08
|12=>0x10300a07451e418340401cfa79010300a0778229de0c328200e11010300a0803bb8040c02820f407013b018050401c040c028200eeb011386808039e404e9028200e49010300a087401c880206014a8e70108c0a0803868040c138200e830103094052a008180803b98f20c03a28fa7901030100734924040c078205a07010300a0b03874040c02821ca0701031c805
|13=>0x130200e7c010306808039e4040c028200eb40101468f40401d3c0c028200ee3010300af303a2804d8028200e10010300a0b0396c0459028200e49010d564340401c04b20401d065b010300e74451e4040c0f014160701030102d039a4040c028200ef2011640a0803b64040c029500ee70108c0a0803bac040c02bc40e8a010300a0803b9c0a080391c920202b6c1007
|14=>0x380810074196cf2020401c00020601416073780818fa028200e020601410077c8081e0803924040c7c014100701030100a0108c0a54039240a080391cfc02060140e8a013d80a340401c0423028200e490103068087881c040c1a1500e79010300a0b03a0c0405078200e490101468547a01c040c043d40e79010301e08038fc040c029ec1007010d418050f81c040c
|15=>0x3b01cf202060143e07248300a0803a589202060141007808b804351a0200e7e010306808038b8040803a0cb602060141007800081808039a47e02060140e8a588080a0803845fe020601410077f0081805043f40e02062ac0a08038080a08039707c73318300a08038089c050401cb6020601410077e008181e03a28f20202b6c10072d808d60c0f014100211814f608
|16=>0x10309e0503a28042b028200f08010300a088381c040c830200e790101410d70892404b20282022102b8080a080396c040c028200f05010d01007249e41805040b40e9d010309c0503a29de02064101007010300a2703a28180803844fa79011ac1805041bc040c0286c0e0206015b6074500818074520cf202060140e8a3e00818058181d1402060140f02248081808
|17=>0x28200e02060141007488080a0808840f221010ac0a080380818050401e24020644410073c8b8460c028b40e02060200edf2d808180803c40f2020643c1e080380818050401d7a020601410078700818be028200e020609c68080380818050f81ce802060800a08010300b0d8601c042306014ba08010300a0803c280509028200e79010780a08038688802060141061
|18=>0x10302a080380818b20281e36028d014100724808181e0287c0e0206054ca0803808181e608200e02064640a080380a301e028200e020601410078b9f81805040b40e02060145454038b8040504044204b0601410078b00a2a0c028200e020605410073c80818052a1840e02028200eeb2d8080a650404420020601454080380818050401e2802060141061038081913
|19=>0x401cae0c028200e49010300a0803c8c040c59078101d010300a078d9e4040c028224407010301e08038f804056d81d14020401ce85b2480a420c028200e0206015120803808184a028d0a8020601410079000818050401e3e02060163c0803a78880c028200e02029500e5b2480818051a02c0e02060140eeb4500a3a050401c9202028200e5b2480818050401e382e
|20=>0x601468540107810072d924042359014106f010303c080e9e404681a0200e79010300a0803ca4040c0f020e879010300a0b03b10040c028200ea7362c80b040401c040c02820c328362c80a0803c9c040c1a01d1479010324c050401c04340401cde79010300b250401c5c0c028b40e740101410078a124040c0f0a810070101410073012404340401d0679014901805
|21=>0x3a84040c520141007010309e05041d0040c02cbc0e79010325c050401c040c02cb41007011ac180504310042302820de790103010613a1e56e0c028200e794f00818052a01c042b028200f2c010d0100700278040c028200e2e010303c080e808680803a140423028213e07010300a0895874040c029500f2a01030107484310040c028225674010300a0803ca88802
|22=>0x601410623792c18050401cf22e010ac0a08038085605328200e020601410079a8300a0803a747c021581410074c00818050401e6802028200f142d80818b20401c5e02060140f333c8080a340401dd602064c80a080380819040401cf20206014681b038081805044c53c020601436072583164050401c040c03845eeea4f03164050401c04050401e6049011640a08
|23=>0x38b8040c0401c5e020612810073c80818050401d0c020605410072480818050401e7a44064f00a080380818b202cec0e021a8d010071f80810071fa0cb62e258300a080395c04050401c229e170300a08038081805041580e02060200e2f3c80818059d01cf2029c8300a074500818050401e70020282022102480818089b81ce80211c2c0a080380818050401e6c02
|24=>0x3a2a8a4b060144e080380818050401e8802061dc0b0c038081805043300e02060141007a18081942028200e0206014a941038080a0803bac220206054102d038081805a08200e02028213e072d8086ad8028200e02060143e07620080a0816844207e0601410071f00a80050401c92020601416076401410070c1257e029f8300a0803808b2050401c22029f0300a08
|25=>0x10300a0803d30d8ef010d010074f008180503a28040c1a0200ea7010300a0830b9dde0c0401c8202061fc10073c80818150401c7e025901410071e808194b078200e020601694072480818050401e92ef010304e08038080a08088fc2002029500e11248081948028200e02060168e073c81410620386092050401c30493e00818050401e8c02028200e11248081805
|26=>0x2a01ea8021aa9068080380818050401ea80215814100724d4c040c028200e02060141007a927804351a0200e020601410613a00a160c0281d140206016a2074500818050401ea06c010300a0b038b804050401c7a44060141007193bc040c0282c0e02060165e0724808180803bb4f2020653c100724808d0340401c040c0f0205a1d010300a0803d34050b028200e5b
|27=>0x2480818059d81c927e060141007718081959028200eef11830ca080380818081681c5e02060141007190084608038bc9202060141007ac0081805ab8200e4401030940504110180504388880206014160701031b00503a28040caa8140e026c0141007378081805043480e6c011380a08038081827044300e026c01410074192c18050401c920206078101d1f8081805
|28=>0x10300a0726014100741860920c028200e413c8780a0803860920206014115b03808840c028200e02060200e3f1780818050401dfe6c59014160701014109f03844046b060141007258300a08038fc460c0281c7e3e4f0300a08038fc040c078200e7d010300ac70401c184e0401cfa791080818050401c04340401d8849361ac0a08038080a08088407c02028200f5a
|29=>0x43cc0eef0103068080380818050401ec602065880a0803808180503a286402060141007b0910fc0c028200e0206078fe0803bbc18270401c040c100141007010300b600401dde0c328200e5b1301410070c124040c028200f5f7780818260401c1808039f4f2e701030ee08039d0040c0f0203a3e010300b5e0401c04050401c7a49ae80818050401cd8021a0200e79
|30=>0x380818050581c040c590140e8a010300a0803b64920c028200e66010300b68038081859028200f67010300a080395c040c028200ea6010300a080380818050401ecc02061280a540400818051a01c980206016ca073c80818052a01cf89e010300a072600818050401cf844010300a272a00818050f81cf20c028200e963c8081805b20200e021a8d01007190081805
|31=>0x6014a8020601410070e92404230601410071f8086a0c028200e3f010300a5403924040c0401cd202060146808039e4040c028200e742480818050401ed649010300a0803844fa020601410072480818050401dce0202b6c1007010300a07451e4040c5901468080380818050401dd6020603c1007010300a0803da8040c02822d207010300a0f0401c042306014102d
|32=>0x10300a0803b10040c028200f6f010300a650401d88020601410074192404fb0601410073a00818b2028200e11010300a080396c920206016dc07010300a0803b10f20206016ca080380ada0c028200e02060780a0803924040c0281ed80206014a807010300a0803b7c5c020601468080380846050401c9202062c80a0803b10040c029ec1007010306808039e48802
|33=>0x60141007418081805150200e02060980a0803924040c02820c207010300a0803980040c028200f5c220300a0803860040c028200e8a248b8040c028200e11363bc040c028200e027d8303c050401c040c02994100708808180503dc8040c028200e1d1f80818050401ee2020601410073a0fc040c028a81007248081805b801c040c02b041007010300a08039bc922e
|34=>0x3808181e028200e18010300a340401c96020601410074f00818050401c040cba0200e02062200a080380818050401c92a1010300a0803d14040c0401dcc0206014109f0380818050401cf2c8012dc18050401c040c028d0a8080380818052a2240e0206015120803808460c028200e3e0108c18050401dee02b98300a08038080a080396c92020601410071f96c04fb
|35=>0x401c040c028200e3f6200818d8028200e6c010300a08039e5de020601410073c80818050401c2249010300a0803d38040c028d010071f80818050401dae490142c18050401c040c02d441007010d468080380810074196c040c02822ee073c809f60c028d0100701032ec050401c040c028200e830c00818a4028200e0206014100762124040c02dd40e02060146854
|36=>0x38081805045f40e49010300a0803df0040c52014680803910040c0289c10070601410070c124040c0f0203a02060141007bda78040c028d01007010300a3403a28040c02cbc1007010300a078d8081805044300e79010300a340401c300206014100724de804050401c224901032f2050401c040c0281d1418010302a0803910040c028200e790101410110800af005
|37=>0x28200eef0601410073c80818050401dfe0206014100733008d60c028200e0206014100775124040c028200e793e1b018b2028200e44010300a0803b9c040c250141007028200e182480818050401c9380010303c05045dc0e02060200e2f0601410e36412c18050401dde02060141007010300a0803845ee02060141007190081805bf81c057e060141007010300b2f
|38=>0x401dde02060d01007010300a340401c64020601410074e910180504558040c5901410070e80818050401c927917008460c028200e2e010d418050401c042306014ca080380818050401dda021a8300a08039e4040c028d010077180818050401cf381010300a0771a280423062c80a08038086a0c59014100777830ca08038081805043840e44010300a5403910040c
|39=>0x401c040c028200e49010300a540401c0423060141007010d418050401c040c028200e85010300a0803e08040c028200e7c010300b030401c5c020601410072d910040c028d0100722008180503a28040c0f01410073c8081805041880e49010300a546400818b2028200e831700818050401c3a020601410f3038081805328200e1d0103164050401cb602061280a34
|40=>0x10300a08038b8040c028200e02062c80a080380818050401f0644010300a0803bbc040c028200e020601410077180818050401eac020601410076400818050401d88020601410077b80818051a0200e02060140e8a010300a0803860040c028200e5b010300a08038fc04fb060141007010300a0803874040c029500e020601410073a0081805
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x498018c00660003
|3,0=>0x311018080bc405c202d1016080ac4054202910140809c404c202510120808c4044202110100807c403c201d100e0806c40342019100c0805c402c2015100a0804c4024201110080803c401c200d10060802c4014200910040801c400c200510020800c4
|4,0=>0x100287ed43eca1f150f62879d43c4a1dd50ec2874d439ca1c950e2286fd4374a1b550d8286ad434e81a250cea86614326a18e50c4a861142fea17a50baa85c142d6a16650b0a857142aea15250a6a85214286a13e509ca84d1425ea12a5092a84814236a1165088a8431420ea102507ea83e141e6a0ee5074a839141c080db506ba0349419aa0c85
|4,1=>0x19fa8ce9466aa3305195a8c994642a31c518ba8c49461aa3085181a8bf945f2a2f45177a8ba945caa2e0516da8b5945a2a2cc5163a8b09457aa2b85159a8ab94552a2a4514fa8a69452aa2905145a8a194502a27c513ba89c944daa2685131a897944b2a2545127a8929448aa240511da88dd0464a22d51142888d443ca219510a2883d4414a2055
|4,2=>0x23fa91e948eaa4705235a919948c2a45c522ba9149489aa4485221a90f94872a4345217a90a9484aa420520da90594822a40c5203a900947faa3f851f9a8fb947d2a3e451efa8f6947aaa3d051e5a8f194782a3bc51dba8ec9475aa3a851d1a8e794732a39451c7a8e29470aa38051bda8dd946e2a36c51b3a8d8946baa35851a9a8d394692a3445
|4,3=>0xa52a524528fa94694a2aa5105285a94194a02a4fc527ba93c949daa4e85271a937949b2a4d45267a9329498aa4c0525da92d94962a4ac5253a9289493aa4985249a92394912a4845
|5,0=>0x34e31a598d20c68a6342a9a014cf4c6746337319a18cc4c65c632b319418c94c644631f318e18c64c62c6313a98858c38a6166308318298c08c5fe62fc317d10bdcc5e952f1b17758baec5d252e6317198b80c5ba62da316b98b50c5a262ce316598b20c58a62c2315f98af0c57262b6315998ac0c55b52aab153d8a94a545529fb14e94a68c52e6
|5,1=>0x40ab203d9012c80363feb1fdd8fe2c7eb63f2b1f7d8fb2c7d363e6b1f1d8f82c7bb63dab1ebd8f52c7a363ceb1e5d8f22c78b63c2b1dfd8ef2c77543b7b1da58ec6c75e53ac31d510e9cc74a43a231cf98e70c732639631c998e40c71a638a31c398e10c702637e31bd98de0c6ea637231b798db0c6d2636631b198d80c6ba635a31ab98d50c6a26
|5,2=>0x4c9b2635930ec98164bdb25d592dec96964b1b257592aec95164a5b2515927ec9396499b24b5924ec921648db2455921ec9096481b23f591eec8f16475b239591bec8d96469b2335918ec8c1645db22d5915ec8a964522a2799130c8926446322199100c87a643a321b990d0c862642e3215990a0c84a6422320f99070c8326416320999042a81b6
|5,3=>0x58832c299608cafe657c32bc995d8cae6657032b6995a8cace656432b099578cab75558b2aad954caaa0654d32a51951cca886541329f194ecca7065353299194bcca58652932931948cca40651d328d1945cca28651132871942cca1065053281193fcc9f864f9327b193ccc9e064ed32755539ec9c964e1b26f5936ec9b164d5b2695933ec9996
|5,4=>0x647b32259906cc7d663bb31c598d6cc65662fb316598a6cc4d6623b31059876cc356617b30a59846cc1d660bb30459816cc0565ffb2fe597e6cbed65f3b2f8597b6cbd565e7b2f259786cbbd65dbb2ec59756cba565cfb2e659726cb8d65c3b2e0596f6cb7565b7b2da596c6cb5d65abb2d459696cb45659fb2ce59666cb2d6593b2c895638cb166
|5,5=>0x705ab8159bfecdf966f9b37b59bcecde166edb37559b9ecdc966e1b36f95b70cdb266d6ab69d9b42cd9b66cab363d9b12cd8366beb35dd9ae2cd6b66b2b357d9ab2cd5366a6b351d9a82cd3b669ab34bd9a52cd23668eb345d9a24ad0c66833340199f4ccf46677333a199c4ccdd566bb33459996ccc5665fb32e59966ccad6653b32859936cc956
|5,6=>0x1e96cf45679fb3ce59e66cf2d6793b3c859e36cf156787b3c259e06cefd677bb3bc59dd6cee5676fb3b659da6cece576433b099d78ceb6675833aa99d48ce9e674c33a499d18ce866740339ed5ceace6f6734b398d9cbace576728b39315c8cce40671d338d19c5cce286711338719c2cce106
|6,0=>0x86e34359a19ef0c87860bc2e9e166f0ae5853bc285a134f09378472c221a102f07a783a341b5e0ccf05f782c3c145e098b045781fb40e5a064f02d58142c089a036f01568073c021a004cffd57fb3bfbddfd0efe267eeabf59df9eefc877e0bbeed9f6acfb057d533e8ddf3acf9857c933e319f0ccf7f77bd2bdd19edaef6857b1abd759eaecf516
|6,1=>0x935bc991e4bcd2595929b4931e48cd240691dac8d1e45af226791034869a428d20f59043c80d63fcb1f778f8b47a9e3c6f1dc78eb3473de390f1c268de346dd6364b1ab78d23c679a32ef19168c53c61562fed17878b9345b1a2ccd16158adb4551e29cd14958a1b44f1e26cd12f7894b448da238f1157887b4425a204f0fb787ab43b9e1d0d0e26
|6,2=>0x4f81a7b4d3d469e734f1de780f3ba69d9bceb1e74eb3a079ccbce4da718f38579bf3cde1a6e2f36b69b32cd7de6b0f35179a53cd0de67ad3367997bcca1e644d31b798a3cc3d6612d303697eb4bdda5e2d2eb6972b4b79e5aef2d169653cb11a57eb2b87958bcab1654eb2a2594e34a55e51ed28a5942349fd64f0f2726
|7,0=>0xa36b519da8c2d45b6a2ab513da892d4436a1eb50dda862d42c5a1335081a834d4146a07350256806d3fe59fc34fc9a7d8d3e66
|8,0=>0x14735
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 388 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x281c22014010160292522014010146c01601016061e5010160101501014060750281c0401f0101401017010470601f010231a8d3060140601502926060234196d06017060160281f0281e0100101016010d30392601016010314196d0601706016060770281c0101422014010230103101020029504196d0601706016010141181401016010141a01d0401d01020029260291f0281c02924010140601f01016
|1=>0x10160101406014063dd060140101606014010320281d060140401d01023010160281d060140401d0281e0101601016010200392502b8f01017010d3060140401f0101701031013b7173130281e0601c01016063ab010161a0ff06014010200101d1a01d060140401d0601f0401f01016010200281c0101571b210101f0101e02b84038fd01023060140637f170770281c010d006014061e7010160601706077
|2=>0x1017010140281d0116d06016010750281c0607501014250210103d5201f060140281d01016220140601f06014060160281d8581f0281d22016118140601d028230116d06014010200281d7783022014010330601c01014010d106014010d00601401016010160601c06014060150116d06017060161fb110281e0101401128258210281d4196d06017060160601c010157d8780281d0101601032118140281d
|3=>0x101f7783001015010d006014060140101406023060140101d0601f010140281c0281d063df0281e010140101606017010d1060141a8d30601506014060140281d0281c0601c028230601f03bdd02823060140281e01015060170101401014010168581d010230281f010167783301014060170101601014060140401f041d20281f1a01d060140401d01016010d10401f02b8f0101601021010140601d06075
|4=>0x601401016010310601d0101403927220140601f010160601401017010160101d06014028fd06016060141a150060140601f02b8f010201a150060140601e01015010200116d06016010160101e01015029260601422014010160101601016010140601506014010230601706016010750281c01021010d1060140e8fd010230281c01016060230601d010230101603924010160601d010160281d0101406014
|5=>0x101606014060140101703d71060146c01d01021010140601f0102322014010750281c010d10601417014010210281d060140101601014010160103101020010d32255b0101c0101d060140281c061e7220140101d06017010160281d0281c1a15206014060150601406014010d10601f01016060770281c0601401031010150601c01016061e5010160102002d3b1701f06016010230112b0103106014010d1
|6=>0x6015010230401d010160601401016010160281f01014220160101d0401f010160601402b8f0101f118140281d1701c0102101017118140281d010200281d01015010140401f01016010770281c0281e220140101d013110281e0116d06016010d1858161a01d060140281e010d2010d1060140401d0101d778200281c010d30281f010d36081d010d30101d0116d010312201406014220d0061e5010330601f
|7=>0x6017028210292701016039250101677833010151a023060140101d01017010160281f0102101031010150281d028210281f0101c010230281c06015010230281f029270281e01017010160281e01021118230281d0601e060170281f028210601f0101401016043230101e0601e0281e013130281e77823010151701701021060140601d010160281e01014063df06014010160401d0101d010160281d01023
|8=>0x1701401021010160601f010161701f010210601401016028fd010230416d0601606015060140601706016010160601402821063dd02823010171a0210601401016043210101e060140401d0281d010170296f06016010750281c010d10601401017778300101501016041d20281f02d5b0101c028ff01023010160116f0601606014029500401d029500281d0601d02823010d40601506016010160601601023
|9=>0x401d0101d013210101e0101601014010770281c010140101601016010140101d1a01d0601401017010160281d118170281d0101f0101e010750281c010170281f010d3060140101c0108c0281d0281c010167d81f02821060140101d010170281d0281c011d00281f010d106014060140401f040750281c040770281c0101601017010160601f010167d814028210401f0101706075010160101d010230281e
|10=>0x101e0281e060140101706016028210281c0281f010160281d06015010d606015038ff0102301016010d00601406016010210401f0101d0601d03925010160401d0101e060170281c0102103bdd028230601c01014010141a01d060140101506014060140108e0281d0101c0101d0281c01014010160281d0102106015010210281d01014061d00281f06014010160401f0101f010140101401031038fd01023
|11=>0x10140101d010150101f0101c
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0x34400000000000000000000000000000000000000000000000000b2000000000000a100000000208071000000000000000000000000000000000000000000000000000000000000061000000001440000000000000000000000000000041000000000c4000008400000080000000000
|4,1=>0x14100000000000000000000000000000000000000000000000000000000000000004c41210000000000000000000000000000000000000000000000000000011100000000000000000000000000000000000038c000
|4,2=>0x7c4000000000000000000000000000000000001d2000000000001c10000000000000000000000000000064c000000000005c80000000000000000000000000000000000000000000000000161054400000000000000000000000000000000000000
|4,3=>0xa4c281000027100002430000000000000000000000000000000022200000000000211000000008040000000000
|5,0=>0x6a100000001a4467219840001944641000063118485f200005d216c80001684591158c55115045311484502000000000004d3128c4911204462000044210884110fc83e10f443c100003b1000000000000000e843910e040000dc436100003510d043220c082f100002d200002c1
|5,1=>0x264898125c40002584000250893124488f20000000238400000008d100008c10000000000000022c40000000883218884220c480300000001fc47e100007c200007b11e480001dc87520000741000000000007311c8470200000001bc40001b8400000006d100006c11ac4000
|5,2=>0x3148c41000000030c4c210000c113004bf12f84bd10000bb200000002e480002e0400000000000000b710000b6100000002d44b320000b210000b11000000000000002c04af12b84ad12b04ab10000aa12a4400029c8a6100000000000a510000a4128880002844a0127c49d226c8000
|5,3=>0x3e04f710000f610000f423cc4f213c44ef20000ee13b44eb20000e8339c4e52000000038c80000000e030000df10000000000000000000003748dc136c40003684d9135c80000000d613544000350400034c4d213444d010000cf10000ce100000003308c9332040000000c710000000
|5,4=>0x4d040004cc53214c440004c052f14b492b24a852820000000498925148c922148091f147851d1000000047051b146840000001191458d142444c00043c90c300010b1000000000010a1420800041c5052000104140c5021000000000010110000ff20000fd20000fb23e84f91
|5,5=>0x5a84000000169100000005a0567159840000000000000163300000005885611000160157895d157055a256095625544000000000055055220000000000000054094f153494c100014b15249481518944250c54124fc80004f853d14f040004ec40004e840004e440004dc93610001351
|5,6=>0x664598165880006545941648800064098f1638400063458c162c4000628589100018720001852610583100000000001821604580100000005fc40005f857d100000005f057a25e0800000017715d497415c880005c080005b880005b456b2
|6,0=>0x7d89f427cc5f127bc9ed27b05eb17a49e817989e517905e317885e027789dd17705da27609d717549d4174c5d120001cf20001cd27305ca27209c717149c327085c026f89bc20001ba20001b916e05b716d480006cc9b216c09ae26b09ab16a49a726985a4268c5a1268059e267099a2
|6,1=>0x97065b19686582958a542948a502938a4d193064b1924a472914a441908800000024028f880008f463b28e4a3818dc63528cca3128bca2e18b0a2a28a462728986242888a202878a1c2868a19185ca161850a122840a0f1834a0c1828a0918206062810a0228009fe27f080007e89f82
|6,2=>0x2b32ac4ab01ab8aac20002aa2aa46a72a94aa41a88aa02a78a9d1a6ca992a606962a50a922a4468f2a34a8b2a248000a206871a14a841a0c6821a00a7e29f0a7b19e867829dc67619d467419cc67129c066f19b866c29a8a68299c6661990a631984a60197c65d2
|7,0=>0x2c410002c31b086c11b006bf1af84000af44000af06bb10002ba1ae44000ae04000adc4000ad86b51
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 14 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x620c01782c0520a013826048088108200340640c01602a0500901001c030050090100180280400600800800
|1=>0x1001fc3f07c0f61dc3a8740e419c310600ae1582a8520a01382584708c114220430841042003d0780d019832
|2=>0x27e4f49e1382644889011021a420831012003fc7d8d119e32c630bf1702784c0941222404688c11021842081
|3=>0x44a8850ea194308550a21342282d04a0840e80900a0039e718df9bd378660c798e310600bc15f29e538a6146
|4=>0x622c2582b015febe577adf5b2b0556aaa50e9f53d2774ea9d137a6b4ce9952ca574a2925222414808f518a2d
|5=>0x1a96e7dccb7b662c7d8db112d6483fb7f2f7dedb7d6f2dbd97b2d
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x400000000040000000000000000000000000004020000000000000000003f0000000000020014000000003f000000010002000000000000000000000000000025000000020004070600000000000000000000000000000000000c00001400000000040000001400000c00020016000400
|4,1=>0x114000400010000000000000000000100000007000002000400000000000000000007000000000000000000000d0000000400000404000000000100000001000000000000000000000000000002290000000004000000000000
|5,0=>0x502011a0c00015601010000250000040002070004004600070501010160000625160001000c16000e7404020007006601740070700003000029002b11000025000020220c0001040041012f3f1b01040207630c1e02020107070019051e70010015470c0135010c002900000700277002000c0100052501205b00220007
|5,1=>0x40c000700311411041604290c17004514010a008500028400180000040000040111533f5302740a000153000c07021102270414001e000083612700000400002f27000002020007070229010001000001000a0000040053000600040971007000013f000000060a1e011f703f012517085300000007071172000c2904370100
|5,2=>0x200000020007040bab000000063614001e70000c01702701050170075300432a00000014011e15143f02682b157b0611010740230700270014000c0034143f0200002700070c01007170172f2b7e0000082b012815140c270000422502001e0208010500012600011400002579002750000a0170070000530411005800171402
|5,3=>0x6700500140401000a0c0c004371070048060055040e1404000000110470000027001114000c02717400005a0e16010001040f007525
|6,0=>0x710a5b2d4cae63994e0167273d923e2e3c2b3887824b12329077277d8045570154a0567f278fa213ac52af5d242794397d386d738d8b159d5e5d9f549743985eb23d15725c760d31877f7a492ca82786a31c49933253330a8d3e07828a827e6537956b9027787c914d6a44150ea71d233e493b6e90a4a621153b59518c3e3e6c
|6,1=>0x5e8896aa9c063a0a308e118a993853b06ba9a536376a729e4a6f0710403353532388903a129a519b1b665b0ab1207e0162394f8972af8fa88b7ea7
|7,0=>0x8124363a243a3a3a2d95ad2c5f6977a14f8b4f64248b6357
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 8 (j % 128);fld (pmPalB (k / 32)) 11 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_29,6,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 1 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 2 then [(dzo_26_4,4,runOps true dzo_26_4 (0,roots_26) ops)] else [])++(if pm.testBit 3 then [(dzo_27_4,5,runOps true dzo_27_4 (0,roots_27) ops)] else [])++(if pm.testBit 4 then [(dom_15,5,runOps true dom_15 (0,roots_15) ops)] else [])++(if pm.testBit 5 then [(dzo_13_2,4,runOps true dzo_13_2 (0,roots_13) ops)] else [])++(if pm.testBit 6 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 7 then [(dom_27,4,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 8 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 9 then [(dzo_29_2,5,runOps true dzo_29_2 (0,roots_29) ops)] else [])++(if pm.testBit 10 then [(dom_23,4,runOps true dom_23 (0,roots_23) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_29_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_26_4_4 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_4_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_13_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_29_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_0 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_29 6 s (0,roots_29) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_29_0 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 4 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 4 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 47 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 47 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 226 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 98 128=true)
private theorem z4:∀ i,0 ≤ i → i < 226 → Z 4 i=true:=(range_split z4_0 z4_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 384 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 256=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_384:∀ i,384 ≤ i → i < 438 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 54 384=true)
private theorem z5:∀ i,0 ≤ i → i < 438 → Z 5 i=true:=(range_split (range_split z5_0 z5_128) (range_split z5_256 z5_384))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 128 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_128:∀ i,128 ≤ i → i < 187 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 59 128=true)
private theorem z6:∀ i,0 ≤ i → i < 187 → Z 6 i=true:=(range_split z6_0 z6_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 24 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 24 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
  · exact z7 i (Nat.zero_le i) hi
  · exact z8 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_31 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_31 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_31 roots_31 goal_31_0 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_31_0
theorem lowS_31_0:Lower true dom_31 roots_31 goal_31_0 9:=S_31_0.noCircuit
end Case2

open Logic Search
def obs (d : Nat) (e : Nat → Fin 6 → Bool) (f : BF 6) := (tt 64 e f) &&& d
theorem obs_op (d : Nat) (e : Nat → Fin 6 → Bool) (a b : BF 6) :
    obs d e (fAnd a b) = opD d 0 (obs d e a) (obs d e b) ∧
    obs d e (fOr a b) = opD d 1 (obs d e a) (obs d e b) ∧
    obs d e (fDiff a b) = opD d 2 (obs d e a) (obs d e b) := by
  have zero (u v : Nat) : opD d 0 u v = (u &&& v) &&& d := rfl
  have one (u v : Nat) : opD d 1 u v = (u ||| v) &&& d := rfl
  have two (u v : Nat) : opD d 2 u v = (u &&& ((v ^^^ mask256) &&& d)) &&& d := rfl
  simp only [zero,one,two]
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [obs,opD,andD,orD,negD,tt_testBit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
      fAnd,fOr,fDiff,fBin,bDiff,mask256,Nat.testBit_two_pow_sub_one] <;>
    by_cases h : i < 64 <;> by_cases h' : i < 256 <;>
    cases ha : a (e i) <;> cases hb : b (e i) <;> cases hd : d.testBit i <;>
    simp_all <;> omega

theorem simulate (d : Nat) (e : Nat → Fin 6 → Bool) (roots : List Nat) (f : BF 6) :
    ∀ k (L : List (BF 6)) n bank, NatReach true d roots n bank →
      (∀ x ∈ L, Avail true d bank (obs d e x)) → R f k L →
      ∃ q B, q ≤ n+k ∧ NatReach true d roots q B ∧ Avail true d B (obs d e f) := by
  intro k
  induction k with
  | zero =>
    intro L n B hr hsup h
    exact ⟨n,B,by omega,hr,hsup f h⟩
  | succ k ih =>
    intro L n B hr hsup h
    rcases h with hm | ⟨s,⟨a,ha,b,hb,hop⟩,next⟩
    · exact ⟨n,B,by omega,hr,hsup f hm⟩
    have build (op : Nat) (ok : allowedB true op=true)
        (eq : obs d e s=opD d op (obs d e a) (obs d e b)) :
        NatReach true d roots (n+1) (obs d e s :: B) := by
      exact ⟨B,obs d e a,obs d e b,op,ok,by rw [eq],hr,hsup a ha,hsup b hb⟩
    have newB : NatReach true d roots (n+1) (obs d e s :: B) := by
      rcases hop with rfl | rfl | rfl
      · exact build 0 (by decide) (obs_op d e a b).1
      · exact build 1 (by decide) (obs_op d e a b).2.1
      · exact build 2 (by decide) (obs_op d e a b).2.2
    obtain ⟨q,T,le,reach,hit⟩ := ih (s::L) (n+1) _ newB (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
      · exact avail_cons _ _ (hsup x hx)) next
    exact ⟨q,T,by omega,reach,hit⟩

theorem observedFloor (d : Nat) (e : Nat → Fin 6 → Bool) (f : BF 6) (roots : List Nat) (T lb : Nat)
    (sup : (L0 6).all (fun x => availB true d roots (obs d e x))=true)
    (eq : obs d e f &&& d = T &&& d) (lower : Lower true d roots T lb) :
    ∀ k, R f k (L0 6) → lb ≤ k := by
  intro k h
  obtain ⟨q,B,le,hr,hit⟩ := simulate d e roots f k (L0 6) 0 roots rfl
    (fun a ha => (availB_iff ..).mp (List.all_eq_true.mp sup a ha)) h
  exact le_trans (lower q B hr (avail_of_eq eq hit)) (by omega)

theorem observedFloorDual (d : Nat) (e : Nat → Fin 6 → Bool) (f : BF 6) (roots : List Nat) (T lb : Nat)
    (sup : (L0 6).all (fun x => availB true d roots (obs d e x))=true)
    (eq : negD d (obs d e f) &&& d = T &&& d) (hmask : d &&& mask256 = d)
    (lower : Lower true d roots T lb) : ∀ k, R f k (L0 6) → lb ≤ k := by
  intro k h
  obtain ⟨q,B,le,hr,hit⟩ := simulate d e roots f k (L0 6) 0 roots rfl
    (fun a ha => (availB_iff ..).mp (List.all_eq_true.mp sup a ha)) h
  exact le_trans (lower q B hr (avail_of_eq eq (avail_neg hmask hit))) (by omega)

open Logic Search

open Logic Search
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def posted : BF 6 := fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4203268232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def tab : BF 6 := fun x => Nat.testBit 18368752179101616264 (Nat.ofBits x)
theorem targetEq : posted=tab := funext (all_pts _ (by decide +kernel))
def points_1 (k : Nat) : Fin 6 → Bool := fun j => (k.testBit (([0, 2, 99, 1, 3, 5] : List Nat).getD j.val 99))
theorem floor_1 : ∀ k, R (phi (2 : Fin 6) false (nz tab)) k (L0 6) → 9 ≤ k := observedFloor Case1.dom_47 points_1 _ Case1.roots_47 Case1.goal_47_0 9 (by decide +kernel) (by decide +kernel) Case1.lowS_47_0
def points_2 (k : Nat) : Fin 6 → Bool := fun j => (k.testBit (([2, 0, 99, 4, 1, 3] : List Nat).getD j.val 99))
theorem floor_2 : ∀ k, R (phi (2 : Fin 6) true (nz tab)) k (L0 6) → 9 ≤ k := observedFloor Case2.dom_31 points_2 _ Case2.roots_31 Case2.goal_31_0 9 (by decide +kernel) (by decide +kernel) Case2.lowS_31_0
theorem floor_0 : ∀ k, R (nz tab) k (L0 6) → 11 ≤ k := by
  intro k h
  obtain ⟨k1,rfl,h1 | h1⟩ := two_gates (2 : Fin 6) (nz tab) (ne_F _ (pt 3) (by decide +kernel)) (ne_F _ (pt 3) (by decide +kernel)) (reads (2 : Fin 6) _ (pt 10) (by decide +kernel)) k (L0 6) (good_L0 _) h
  · have bound := floor_1 k1 h1
    omega
  · have bound := floor_2 k1 h1
    omega
def witness : List Gate := [⟨.and,[2,3]⟩,⟨.or,[6,0]⟩,⟨.and,[3,4]⟩,⟨.or,[8,1]⟩,⟨.and,[9,7]⟩,⟨.or,[8,2]⟩,⟨.and,[11,1]⟩,⟨.or,[4,3]⟩,⟨.and,[13,0]⟩,⟨.or,[14,12]⟩,⟨.and,[5,15]⟩,⟨.or,[10,16]⟩]
theorem witOK : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,17⟩ (List.ofFn x) = posted x := by
  rw [targetEq]
  exact all_pts _ (by decide +kernel)
end PEqualNP.Outside.L_meta_43254_aux
open PEqualNP.Outside.L_meta_43254_aux PEqualNP.Outside.L_meta_43254_aux.Logic in
theorem PEqualNP.Outside.L_meta_43254 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4203268232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4203268232) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  apply mono_shape2 posted 11 _ witness 17 (monoOK_sound _ (by decide +kernel)) (by decide +kernel) witOK
  rw [targetEq]
  exact floor_0
