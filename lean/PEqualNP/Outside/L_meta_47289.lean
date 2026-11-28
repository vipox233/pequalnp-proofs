import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47289_aux
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
def dom_13:=0x3333
def roots_13:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_25:=0x3030303
def roots_25:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_41:=0x30300000303
def roots_41:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_45:=0x333300003333
def roots_45:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 5 0]
def dom_53:=0x33003300330033
def roots_53:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_57:=0x303030303030303
def roots_57:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_60:=0x1111111111111111
def roots_60:List Nat:=[xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def dom_61:=0x3333333333333333
def roots_61:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_13_2:=0x3220
def goal_25_34:=0x3020200
def goal_27_32:=0xe080a00
def goal_29_2:=0x32303220
def goal_29_34:=0x33323230
def goal_41_18:=0x30200000200
def goal_45_2:=0x323000003220
def goal_45_18:=0x333200003230
def goal_53_2:=0x32003000300020
def goal_57_2:=0x302020002000200
def goal_60_2:=0x1110101010101000
def goal_61_2:=0x3332323032303220
namespace S_53_2
def pairsG:List (Nat × Nat):=[(1,5),(4,5),(4,20),(4,36),(16,20),(17,21),(17,49),(32,36),(33,37),(33,49),(48,49),(48,52)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_53.map (· &&& dom_53)
def goalM:Nat:=goal_53_2 &&& dom_53
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x55100071171404d1
|3,0=>0x531db19e50a540c03fdbe7602f79f19627a8300425d57a16245d5cae224197bc1c84809a11b1c69002f8fc78
|4,0=>0x9c09c6a7531db19e43ca2f91218c661019ee6e7715d5e5001529b30e0ae8eb5e
|5,0=>0x531db19e
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xc0000000c000033003300220022cc00c000cc00c03000300000000880000008800000000000220022880088008000832003200320032800080008000833003300330000cc00000000000020002002200220000cc0000000000000003300008800000088008a20033002200220c0000000c000000030000000304400440040004330033003000008800880088008b00030003000304400880044008b3003300000000cc000000cc00012001200120012
|_,_=>0
def stPool:Nat → Nat
|0=>0x2090a20932510485c082428ae121441216c2090b510485a08242a0412144124c419460f21441238856b04122c41228454a04121cc12144418820
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>0xb9152264448790d216424839052064
|4,0=>0xa8b4125ac6582af15bab25
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 26 then fld (dictB (i / 512) (i / 32 % 16)) 54 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 5 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_53 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_53 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)],[(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa,31)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa,15)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_53==dom_53) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_53 goalM v ys):RunD true dom_53 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_53 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_53 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_53 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_53 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_53 roots_53 goal_53_2 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_53_2
theorem lowS_53_2:Lower true dom_53 roots_53 goal_53_2 6:=S_53_2.noCircuit
def isoMv_60_2:List (Nat × Nat):=[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_60_2:Lower true dom_60 roots_60 goal_60_2 6:=lower_iso isoMv_60_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_53_2
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
def isoMv_25_34:List (Nat × Nat):=[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_25_34:Lower true dom_25 roots_25 goal_25_34 4:=lower_iso isoMv_25_34 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
def isoMv_41_18:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00,8),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)]
theorem lowS_41_18:Lower true dom_41 roots_41 goal_41_18 4:=lower_iso isoMv_41_18 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
def dzo_25_2:=0xc0c0c0c
def gzo_25_34_2:=0xc080800
theorem lowSh_25_34_2:Lower true dzo_25_2 roots_25 gzo_25_34_2 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_34) [(dom_25,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_34
namespace S_27_32
def pairsG:List (Nat × Nat):=[(1,9),(3,11),(3,19),(8,9),(10,11),(10,26),(17,19),(17,25),(18,19),(18,26),(24,25),(24,26)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_27.map (· &&& dom_27)
def goalM:Nat:=goal_27_32 &&& dom_27
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
    (if pm.testBit 0 then [(dzo_25_2,4,runOps true dzo_25_2 (0,roots_25) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_27 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_25_34_2 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_25_2 4 s (0,roots_25) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_27 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_25_34_2 h
def symsG:List (List (Nat × Nat)):=[[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc,14),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_27==dom_27) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 goalM v ys):RunD true dom_27 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_27 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_27_32
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 5:=S_27_32.noCircuit
def isoMv_57_2:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)]
theorem lowS_57_2:Lower true dom_57 roots_57 goal_57_2 5:=lower_iso isoMv_57_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
theorem lowS_29_34:Lower true dom_29 roots_29 goal_29_34 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x30303030,0,4)] (by decide +kernel) (by decide +kernel) lowS_25_34
def isoMv_45_18:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_45_18:Lower true dom_45 roots_45 goal_45_18 5:=lower_iso isoMv_45_18 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_34
theorem lowS_29_2:Lower true dom_29 roots_29 goal_29_2 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0x33330000,4,20)] (by decide +kernel) (by decide +kernel) lowS_13_2
def isoMv_45_2:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)]
theorem lowS_45_2:Lower true dom_45 roots_45 goal_45_2 5:=lower_iso isoMv_45_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_2
def dzo_25_32:=0x303030300000000
def gzo_25_34_32:=0x302020000000000
theorem lowSh_25_34_32:Lower true dzo_25_32 roots_25 gzo_25_34_32 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_34) [(dom_25,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_34
def dzo_41_16:=0x303000003030000
def gzo_41_18_16:=0x302000002000000
theorem lowSh_41_18_16:Lower true dzo_41_16 roots_41 gzo_41_18_16 4:=lower_iso (d1:=dom_41) (roots1:=roots_41) (T1:=goal_41_18) [(dom_41,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_41_18
def dzo_45_16:=0x3333000033330000
def gzo_45_18_16:=0x3332000032300000
theorem lowSh_45_18_16:Lower true dzo_45_16 roots_45 gzo_45_18_16 5:=lower_iso (d1:=dom_45) (roots1:=roots_45) (T1:=goal_45_18) [(dom_45,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_45_18
def dzo_29_32:=0x3333333300000000
def gzo_29_34_32:=0x3332323000000000
theorem lowSh_29_34_32:Lower true dzo_29_32 roots_29 gzo_29_34_32 5:=lower_iso (d1:=dom_29) (roots1:=roots_29) (T1:=goal_29_34) [(dom_29,32)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_34
namespace S_61_2
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(4,5),(4,12),(4,20),(4,36),(8,9),(8,12),(16,20),(17,21),(17,25),(17,49),(24,25),(24,28),(24,56),(32,36),(33,37),(33,41),(33,49),(40,41),(40,44),(40,56),(48,49),(48,52),(48,56)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_61.map (· &&& dom_61)
def goalM:Nat:=goal_61_2 &&& dom_61
def NN:Nat → Nat
|2=>5
|3=>45
|4=>116
|5=>209
|6=>82
|7=>13
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xc864e9c4aeccc5cfa1bb927d600e75460eb74b99
|3,0=>0xef88654dcfb9d3dfcbe3b3c2c5d8ae23c240e7efa459b494a0ee06ffa09b45539da828329a60232895302f63938a12019096f4e0848266fb82c2f6187dafdade75476432741ba7716c0648af6ab4622d60e4bc955ef5155d4ba1d29f3b3d227d30645dd52dd112c52dbf23062d423aa72cfa44f72c180595256002aa23532a8320adefb4205cd8c1203107551979ffc818b86c42181b5f6e1341689e0ba738f0075bdc44061ec65c0556a260023c6d51012b25ab
|4,0=>0xe80a1602db1bc2a6d3ebefc2ccce654cc8b1e81cbe7d3ecebb9fc206bae5789ab2a6cbfbae8e8eb49d519e5599e0db759628341894ac5c739467682c933516f790b535e98fed11ed8c2ea2ac893b858b874cb6348448ff9782077dfe80fc1c9480c38cbc7f7ed4e27cc4b6957b386754784fe4dd7160efb66f4248d36b758f206b02f1fa6afb288a6ac8d59569433837682494d466bc02a76422890b61f06e8460dac18b604150f25e1913ec5b68e16c59aacf555799a6085465bade541df4a251c103a350c610914d63023648d9ab2346aba62941ae8b2f413405883ffda8ad3f8ad29a3ecc77ec3a8a23813a4a26913414731033d4e4d93378a4bd3144f866313dc8802f8cbf042f2de7862f2a32ab2e8248402e7bb1f82e6bb51c2dba24442db476e52db38dfc2d694c9e2c1b7bfd299620f12973be0626d07fd625dbf7d22433c514234c11cb22cf296c22a645a122948b29223e749c2149490e2058194c1bf7bb2e1952805f191ae84418d598001803140616a82ec7146c4ba614327a4013d3f89f120167fd117b458d10703f071049c0de0f6e51280eb5e7560e455b070d5394c00d3f5f1d0c084dc507df1aea076b3e1805f5f54b050d5d21044bc99b03af05a502199e450128cc01007fa102
|5,0=>0x504c4b734f8427774f1011e34e3f79b64c9f01464c73e1574bac98f547acd2b946c49eb3451cdb72446570154233a8604161ff3840cac9f44075b1fd404259253fa37f903f7a64c43f71dbea3e190dce3d5460fc3c4aeeb43c30e43b3b8eafbe3b71b2783b33fffb3ac2f32639e48b9b39c3114839853ea0389921ca385f982837bdabe5373656313714c44034c05548343203f332703e5f31e4b80031ad735530f5c45730b8a9362f8059272ee3c2e02da78db12da24cd22d3148b32c0bf1412be611d12ae3ee8c2a874e742a7d20292a7689e12a5420802985f46a2944076a26d1e72b2695ac6a26577c0d25dab2ad2418e05723e28564234165aa221150c32149490e20c412741f88a3c81f820d801f0743131e4dcda71dff5a661cd855bf1cd2ec541c9586a71c8ef05f1c5166ae1c1b4d4c1c0bcc891b6f7cdf1b63e0e21b2085ce19d4700a1969fcc818fca9f717f939a017bee220175df5961729b458164d184716225a9815f3a8b2154c5f0414f3a80014d5854c14318491141eed8d141d8dd813c5b0e5135ae498128c65ab1263f81012299e97114978bb1123281410707e5e0ef27bdb0edf6f240eacabda0e6286c50e39a2fa0dbb6bb70cd798600cbdaa570c804fbb0a619bc30a6066390a2923e708bd4b4108aeb07a0892d43f06e74acc0680f69d06669036055ee9150545efdd03aeac5b00d3cdf20023fead
|5,1=>0xeeb6a6e0e8bef322e80a1602e519ff4cdf30a1eadab6dbf0d4575dc2c34ffc19be9c0aa7bd669eb7ba2a80f2b581d988b523398bb40a2d93b12cb0cbb072675fae1c5f8facac817ba93e7f6ca7331f5fa5a7d477a4cfaef8a2540340a217deb39deb6f5d9a3cf31c97a5cab796c797c6920484478c34dbea8a1b7f32898cb5f688f1db1088c280fe880d976d87ced4f786934b588687ab9b84ebe1a181bb917180fc1c947ec8745079dc84a478061ef975876549751c3468749a5b7c7441c52c730730dd70c5c3a76ff1ad4f6e75c3c26e5ab8e96e3de48a6ab08ecb69a42faa68f69e3a67c95f5b64d5cde062527d115f3219615d0412f25cfedd585c9834ba5c48f16c5b9493435b51bcee5a42181f589005f957fb2fe157b3941157a40f69549f5d85547fa8e7547be43b53b7f22d524f600051e6dcdc51d73fea51bdb33750b37a9b
|6,0=>0xf749d42ce47a6b4add9704c7db85c7e1d74bdcbbd57fd0f9ce7684aec7187c85bebb79dcb96fcdeab03256dbac56ab13aab028509dd9129f9cc00e249becd55b99ebc3da920484478f5576688ba50619880d976d86efc41b80a971297d625a047d2bce9173a1431d703a811470097ce96f7faa976bf58b9669411bc5691cd88468a83f286643943a5e21b6525c73915b596f70fc532183e14e85d0a54d2a9b7e4c9a62504c47235c4802857047dc4ec546c49eb34233ae3a4152a6fb3fcb7acf3e5f89da3a8d207b374cc9c935d21cdf359d8b9f34600d3130b8a9362ad05f1d29ffff9d26ebf77d21fb1360207ce3d11e8166351c2725051a99d51218f03a6113497f3e1342e8f61265448410f0cfa7109941f60cd798600aafb74e0a5d9504099eb42509348533089c0ff10840eccc07bd23a4071be3b70700ce0b06446e7d062cf77b035cc4ba
|7,0=>0xd1fc5a0ea8b9c74e7a05803b643a05095c5723ae562a1064530291eb43c51693427001d62d7423e112b8996b0773644f06a221b4
|8,0=>0x643a0509
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x8800cccccccc8801132112211321122cc88cccc0000000000033330000000000000000cccc0003300330033003300040cc0c0040cc0c3333303033330000cc88cccccc88cc8a2112210221122100400040004000400012001200120012cccc0000c0c000022002200220022000c0cc0c00c0cc0c1100110011001100008800880088008b3320000333200008888888888888888330033003300330ccccc0c0ccccc0c3230220032302200044804480448044b322332233223322c0c0c0c0c0c0c0c0000333333330000cccccccc000000032303230323032300044cc880044cc8b3330000333300004488448844884488303030330303030
|0,1=>0x44004400444444033333333303000000c080c080c080c0b333333322222222cc88cc880000cc89122112211331122cccc00000000000111111001111110000cc00cc00880088000000030303030c0c00000c0c00000132013211221122004400440000000000000003322332200000000ccccc0c0303333300000000040c40c0040c40c3333323022002200ccc8ccc8cc88cc88011001100100010ccc0ccc0ccc0ccc322232223222322288008800c8c0c8c03030303000000008844880088448800000332200003322cccccccc0044000332233223020302084808480848084800320032003200328080808080808080132013201320132
|0,2=>0xc0c0c0c0ccc8cccb3003300323232320c0c0000cccc00022003230220032308800cccc88008803333330033333300cccc004400000002222333322222222ccccccccc0c0c0c32303230220022004444444400000002233223322322232cc88c0c0cc88c0c00003333332233224848484848484849110110011101100084808480848084b330222233302222cccccc88cccccc8b32200003322000000cc00cc00c800ca200333320003030ccccc0c4cccc0003332332233323322888088008880880020202020202020200cc00cccc00cc033333333000033228800cccc8800c8c0000000033323332ccc8ccc800000003232323232323232
|0,3=>0xccc80000cccb333002233330022cc00cccccc00cc03333333333223322cccc00000044000333300113333000088888888c8c8c8cb33022203330222000000000ccc8c0c01030103000000004444444440404043332000033330000cc88ccc800000000000303000003030c8c0c8c00000000323232322222222288cc888888cc88880110011332233228880888088808881111111011101110000800880008008803300330000000004040404c8c8c8c811001100110011044cc44cc00000001133103011331030c080c080c080c0803130000031300000c080000cccc00032323232000000004440444044404440000333300003030
|0,4=>0xccccc0c000000002233223322222222ccc8ccc8cc00cc00032003200000000cccccccccc00cc03300330000000000ccccc0c0c0c0c0c3333333033303330ccc00000ccc00000000222200002222000c000c0000000000000003330333044004400cccc4400303020202020202cccc8888cccc8888000333300002222ccc0ccc0888088800330030003300300c4c0c4c00000000000000022222222ccccccccc8c8c8ca233223222332232c0ccc0ccc0c0c0c3322332203020302cc00c800cc00c8033333333333300000000cc88cc88cc8b320332033203320c8c80000c8c800022112211220022000040004000400040312031203120312
|0,5=>0x8800c8008800c8202020203030202ccc0cc00ccc0cc00001000100000000cc00cc00ccc0ccc3200320022002200c4c4c400c4c4c40330033003333330044004400c4c0c4c3131303031313030cccccc88cc88cc8b033303300000000cccccc00cc00cc0222222223333222288008800cccc880101010101010101044cc44cc40c040c32323333323232320044004000440041133000011330000888c8888888c888b331333133303330ccc0ccc0cc00cc01110111011001100ccccccc0ccccccc0101010101000100cc88cc8800000003333222230302020cc00cc008888888b3330000333333220000ccc0ccc0ccc3000300030003000
|0,6=>0x8000800080008011000000110000040400000404000320032003200320044444040404040433113300331133000c08cc880c08cc8b2023202320232020000000044444400300030003000300cc04cc040000000223222322232223200c400c400c000c3333220033332200cccccccc88008801111110011001100c8c88888c8c8888b32200003333000000c000c000c000c33323332333233320c040c000c040c030313030303130300404040400000003200320032323232ccc8c0c0ccc8c0c3322333233223332cc88cc88cccccc8b3332222330022004444000044440000303030003030300cccc88888888888b333003322220022
|0,7=>0xc0c08080c0c080b31033103310331000000000cccccc03333323233333232c0c0c0c0000000033002200330022000c0c00000c0c000003300000033000000cc008800cc0088300030033003300c0c40000c0c400033333020333330200c080c0800000000000030200000302
|_,_=>0
def stPool:Nat → Nat
|0=>0x2c050e2b2a250208040208292805072726250207010507120305022404021d08040502232208041c1b05180804050221201a070d1f0502071e021d070107011c1b051a0d19051807010502170405130804050207160502151405130701020812000510110f07100f06050e0d0c050b080a050209080406070106050403020100
|1=>0xd050248074702070d46454402080712051a070d430e1a070d4202411a4021050217071205130807120502073f0f3e0207100f05020d3d223c391a073805023b040502073a3907383702012836050b35011a040d0605020734020804310208043008071206020433320207013102070130051a0d2f2e02080705022d04050204
|2=>0x2240712050b35100f05020701361a040d1c1b05181a040d05021a045857021a560d05022b2a5502411a070d0502070133021d0807120807121c1b050207540f051808071202070d373205531a070d021a070d5205021a5122050207500f05021a404f054e1a070d054d4c07120502070d4b051a070d4a05491a070d05131a04
|3=>0x76c050207506b05021a516a021a070d6905022b0d681a070d6760051a350d660508071264051a070d6305021a625102411a076105020804360507100f60021a5f0d36021a5e070d0507105d0f05081a0d11051a0d101105022b402a081a070d06050208075c1a070d100605020804331a070d5b1b5a591a070d0210280f3605
|4=>0x7c7b1a070d2e021a070d577a1a070d051307100f021a0779320502781a40021a070d77021a0d763605022d071205021a0475570502080405741a070d02731a070d050207122c021a0d29280502070d20591a070d7257050207012502080712251a070d2657021a710d05021a70040502076f22021a070d6e050e1a076d05021a
|5=>0x3b0712058783070d861a070d851a070d7f420208122836050208041c050b0835120502076122050207011c05020738370502844083021a040d3105022b2a610502211522021a040d30051a0d12111a070d120602080712310208071230050208078207100f1c1b05021a0d80051a070d7f0207123332057e7d070d410e1a070d
|6=>0x622105181a070d1205021a0758120502081a0738054d021a070d25021a070d05021a070d92055a1a070d9005028f1a070d0502070d8e0f02081a070d8d05021a07388c0502080735128b021a070d6a05021a078a0d3c021a406207051a07350d263c021a89070d0502081a077905021a5f070d0502881a070d05022b08400502
|7=>0x22ba00d619f021a070d1205911a83073c05022b1a405902081a070d055a02070d370502081a079e05029d1a070d05021a070d9c9b029a070d46021a070d33323c021a40076a0598021a070d05021a04350d05971a070d96050207100f1c7c02391a070d05020e1a070d021a070d959405021a070d931a070d121c1b05021a40
|8=>0xd05a7971a070d02081a070d31021a070d1031021a0d280f36057a081a070d05021a070da6050208071236055a971a070d02081a070d30021a070d10307c02a51a070d05a4021a070d05021a40216a050b1a350d0f05022b0807613c021aa3070d05022b400d2205a2081a070d050208071233021a070d323605021a070da105
|9=>0x21ab4070d3c91391a070d3cb3021a070d051a070dac7205021a070d3f05021a070db105022b080db0021a070d8d3e02081a070d3e021a070d1005021a40076f055a1a07580d05021a070daf05021a040d3605021aae070d05021a070dad051a070dac3605021a07ab0d0502aa1a070d05021a070d5c0502a9070da802411a07
|10=>0x1a070d05021a070d50051a070dc3c205c102081a0705a21a070d05c0021a070d05391a070d3805021a070dbf05021a070dbe0502481a070d05022b1a890d59021a070d05021a070dbc02411a40070d05021a402a070502bb070d1005021a70ba0705021ab9070d05022bb8070d05021a070db705021ab6070d05b5021a070d3c
|11=>0x74626051a0d111a070d060502081a403d050b081a350d3c021a070d320508ce1a070d05021a070d850502bd070d0f05021a400dcd02cc411a070d05021a0a070d05021a070dcb05021aca070d9b021a070dc9051a070dc38e05021ac8070d05021a07c3610502c71a070d0502c61a070d0502c51a070d05021a70071205c402
|12=>0xd21a070d1b05081a070d7f02a51a070d360502cc1a650d05022b0807465705021a040d0502081acf0757051a070dac44021a070d26050b1a83070d05021a0d3d81054d02080712d10b021a070d0502081a0761054d1a070d2605021a070dd005021a07127557050208071205022b08400d02081a0d28360502481acf0705021a
|13=>0x1a070d05021a07b210021a070d1231051a070d7f021a070d12301a070d0f1c1b057b1a070d320502bd070d6b051a070dc32605021a070dd905021a40d80d05c1021a40079b91391a070d05021a070dd705023b1a070d9b02070d55d605ce1a070d0502d51a070d0502081a07d457021a07580d05021a070dd305131a070d0f05
|14=>0x21a070de1081a070d1c1b05021a40072605020807121c05021a070de005cc1a070d7f021a070d1c3205021a0761df050e081a070d0502cc1a07610513081a070d051a40070d7f05021a070d3d05021a400761050b1a070dde05021a4021dd050b1a070dac05020840dc070502cc1a070d050207100f3605021a070ddb050bda
|15=>0xd0f1c0502da1a070d9b05021a070d4605021a07650d0502bd1a070d05911a070d1c86021a070d320502cc1a0d3d05022b084005021a406505e21a070d05021a400d3d0599021a400d0502081a406505021ae3070d05e2081a070d0502241a070d8639081a070d05022b084007021a0d12283605021a040d1c050b1a350d1205
|16=>0x21a62070d055a0b1a070d0502081a070de705021a070de505911a070de605021a070d329b050b021a070d0591021a070de5050b02081a070d050b021a070d1005021a070d123605022b1a070d6105021a07b20d054d021a070d05021a070dde05021a070d220502070de405022b08070d0591021a40070502a9070d05021a07
|17=>0x5ea021a070d05021a07e90d12055a911a070d05021a40070d6a05024c1a070d3e021a070d055a391a070d5705021a070d1205021a400dcd9b0591021a070d021a070d3105021a4062070d021a070d300502081a070d1c3c05022b1a070d0591021ae8070d055a1a070de7050239081a070d05021ab6070d0502084c1a070d05
|18=>0x5022b1a070d9505021a070d3d05021a07790d0599021a070d0502cc1a070d860502081a070d055a021a070d8c05021a070d0f3605021a070d75021a0d28360502081a070d3d050b1a350d7c0502081a070d0502391a40070d05021a070d9505021a07350d0f57021a070d6a0502cc081a070d0502ec1a070d055a021a070deb
|19=>0x70d05021a070dc305021a07e90d5705021a070d3c05021a070d05021a070d810502081a07650d05022b1a400d0502081a070d2686391a070d0502081a070d811a070d1c1b05c1021a070d05021a070ded05131a070d0502081a070d360502081a070d3305022b1a40070d0502cc1a40070d05021a070d121c0502081a07350d
|20=>0x5021a070d05021a070d368605021a070d05021a40070d05021a070d05021a070d1c0502391a070d05021a070db005021a070de70502081a
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0xc30093006300330003
|3,0=>0xbf40bb40b740b340af40ab40a740a3409f409b40974093408f408b40874083407f407b40774073406f406b40674063405f405b40574053404f404b40474043403f403b40374033402f402b40274023401f401b40174013400f4
|4,0=>0x1fe51f951f451ef51ea51e551e051db51d651d151cc51c751c251bd51b851b351ae51a951a4519f519a51955190518b51865181517c51775172516d51685163515e51595154514f514a51455140513b51365131512c51275122511d51185113510e5109510450ff50fa50f550f050eb50e650e150dc50d750d250cd50c850c35
|4,1=>0x30252fd52f852f352ee52e952e452df52da52d552d052cb52c652c152bc52b752b252ad52a852a3529e52995294528f528a52855280527b52765271526c52675262525d52585253524e52495244523f523a52355230522b52265221521c52175212520d520852035
|5,0=>0x47f54796473646d64676461645b6455644f64496443643d64376431642b6425641f64196413640d6407640163fb63f563f053ea63e463de63d863d263cc63c663c063ba63b463ae63a863a2639c63966390638a6384637e63786372636c63666361535b6355634f63496343633d63376331632b6325631f63196313630d63076
|5,1=>0x5f945f545ef65e965e365dd65d765d165cb65c565bf65b965b365ad65a765a1659b6595658f65896583657d65776571656b65665560655a6554654e65486542653d55376531652b6525651f65196513650d6507650164fb64f564ef64e964e364dd64d764d254cc64c664c064ba64b464ae64a864a2649c64966490648a64846
|5,2=>0x775676f67696763675d67576751674b6745673f67396733672d67276721671b6715670f6709670366fd66f766f166ec56e666e066da66d466ce66c866c266bc66b666b066aa66a4669f56996693668d66876681667b6675666f66696663665d66576651664b6645663f66396633662d66276621661b6615660f6609660365fd6
|5,3=>0x7d867d267cd57c857c357bd67b767b167ab67a5679f67996793678d67876781677b6
|6,0=>0x96d69676961695a7953794c79466941593a7935592e79277921691a7914690d7907690078fa68f378ed68e678e068db58d568ce78c868c178bc58b578b058a978a2789b7895688e78886881787b6875686e78686862685c6855784e7847784078397832782c68266820681a6815580f6809680457fd77f767f077ea67e467de6
|6,1=>0x9e069d979d369cc79c759c079bb59b569af69aa59a3799c7995798e79877980797979736
|7,0=>0xa2d6a276a216a1c5a166a106a0a6a0469fe69f869f269ec69e66
|8,0=>0xa335
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 238 then fld (dictB (i / 512) (i / 32 % 16)) 62 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 8 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 1000003 zs)
def opPool:Nat → Nat
|0=>0x20886835051a408350208c6835070d46902020d46835990d4e41d05020081c070d468350240c68340240068341a0d068353c1ac68350591808353c2b0681d020d46837020701501070d468351a0d4081e070d81c351a0d409001a0d068340208cf60508078201f1a0d41c351a07408351a0d068354021c1c34070d409000265c201c020780821020800835052640822
|1=>0x406ac1c351a40868351a0d46ac9050286834bd0dce435050206835020d40835bd0d4081c0240c1c351a0d469012b0801c35a90d0681f0d1c4140a051a40835050201408020786aca050281c37070d46835021ac1c351a0d0081d1a0d0081e054041c35050b8081d1a0d4081e070d40835070d01c352b0dc1c35020d4ac37070d41c351a0d01435024001c35020d4149b
|2=>0x1a22469021a0d40b321a404681d1a40868350207468351a0d868341a0d068350208820d70207103371a078e435070d66e46020d468350807868350d1c46836050280b3208074201d0807068350207468350207068341a0d40900070d4201e0807c082102074201d0208868351a0d01c35a90d408228639c140905020201f1a0d4081c0207408221a0d468361a408081c
|3=>0x20746834020786902070d434710502808350208c68351a4081c35020706835070d41c35020d4081c1a0d8140a1ac3408371a07c083508070683502070140a020d4683508074201f1a0d41c35070d4201c1a0d40995080706835cc07c6901070d4e41d05020201c023dc201f02654201c1a0d468350502414081a0d41c351a0d0140a1a0d068351a0d4683502cc0201d
|4=>0x1a0d41c35050200903070d4081c050dc081d0807468351ab041c37020d408351a0d0081c051a40835021ac1c35020806835020d414081a0d0081d1a0781c35021a40835020740900070d4081c1a0d4681d020d4f068020d4141f020d46835050201f0d020dc08201a0d40900070d4141d020d468350207cf06b020d4146b020d408221a0d408353c1ac08351a0d4081d
|5=>0x20781409070d4140a050201c370207c083702070081d020d4201e1a0d4201c1a0d4681d070d408221a0d4140905020201e1a0d4e43505020f01f020d55c080207468350207868351a0741c351a4041c351a0d0140a1a0d4081c0240c1c350807c683502078e41d050206901070d4683505024086a1a0d8081e570dc081d02078201f1a0d4141c
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0x126081000000000006200000000000000000000000000000000000000002880000000000000000000000000000000000000000000000000000000000000000000000000000000000000320000000000000000008400400000000000000000000000000000
|4,1=>0xd100000001910000000000000000000000018100000000000000b885840000000a880002460000000000000000000044400000007180000000000000000000000000034400000000000001820000000000000000
|5,0=>0x1508a440000001444000501278800000000027093080004a224891c800000000000008c245121190447c63c21d10e447023711b08000666321188800060200017880005c22d11608ac452400014080004c423311080000002110f900000001e10000708000000
|5,1=>0x224d0e48524208001062821408800100200000000000007e23e89f04f627923c08000ee20003a91d04e627210000000e046e23689b040006a20001a44d0266200000000000003199884c226012f897480005c1000168800058200000000005710000000ac2000
|5,2=>0x3104000c310003084000c025f12f457640005c92e04000b710002d840000000002d456820005988001642000588abc95a4ab20002a4950200000000014c4a510002905462a1200027c93c29d14d926853229724a9250526292148100011e200047080011a28c1
|5,3=>0xe217013789b66d836b134cda42d026713345946c82638b1858a2000
|6,0=>0xa78d34a965492a40d18a885431a0950067e33d29d94e867053629a14cc66433029714b0a544000941498a485222908c7ca3c31d18d9464a2e5152899444a1e50d2859424a0e5052820c08a004ff17e93ec9f24f817b13d09e62f127793b85d84ea27413989ca2e32
|6,1=>0x2de56d2b595a4ace565200058cac255f2ae95706b45582ab1550aa45502
|7,0=>0x17b1bd0de44001781bb8dd86ea2000ba0dcc6e43711
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 18 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 255),wireSAt ((code >>> 10) &&& 255))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xfc3b0d8330ac290a02408c220841d06c1705815050120400d0300b02809020060140400c0200400
|1=>0x4c1244811d465184451042104400dd334c4300ac290812007c1a0661805414849120451104210440
|2=>0xc02ae95a45801ed775cd705bb6b5a466d9964d90625816017d5f1745c55d5654d521475194550536
|3=>0x3e9f777fdf779dbf6dd7f5dd7326
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>0x1000004000000000000010000000223c000020008000000000010000520000000000000008000000020000000000000382000000100000000000000000000002000000000000000000000000000000000000000000000010000000000808000000000000000
|5,0=>0x1e50a8102026b5020008000000071ad912e3a01a800e343db0001b8c4634007007409600000005c04084022003800f404100800040000080003c080001000108000007e1c0085a6400000003a8200925f0a1068208027010801000040280254c50806c012974001001168000f0024000
|5,1=>0x350278d1a0344088023611a3a20e80003402000d4001021808002106810238000081138080010000204ad040dd0000000ab500180810004a8874d9018020408142001001001c01
|6,0=>0xf1a3d06415a14b1603610d0868ec313cd589dc84572af35282518806f153d1529f6831e3ec228f46ba4aa3214225cf790662c739ec478699088386b22b784d81e92bd9bc067aad7
|7,0=>0x68d27b559a67a608796b463
|8,0=>8
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_60,6,runOps true dom_60 (0,roots_60) ops)] else [])++(if pm.testBit 1 then [(dzo_25_32,4,runOps true dzo_25_32 (0,roots_25) ops)] else [])++(if pm.testBit 2 then [(dom_13,4,runOps true dom_13 (0,roots_13) ops)] else [])++(if pm.testBit 3 then [(dom_53,6,runOps true dom_53 (0,roots_53) ops)] else [])++(if pm.testBit 4 then [(dzo_41_16,4,runOps true dzo_41_16 (0,roots_41) ops)] else [])++(if pm.testBit 5 then [(dom_57,5,runOps true dom_57 (0,roots_57) ops)] else [])++(if pm.testBit 6 then [(dzo_45_16,5,runOps true dzo_45_16 (0,roots_45) ops)] else [])++(if pm.testBit 7 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 8 then [(dom_45,5,runOps true dom_45 (0,roots_45) ops)] else [])++(if pm.testBit 9 then [(dzo_29_32,5,runOps true dzo_29_32 (0,roots_29) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_61 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_60_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_25_34_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_13_2 _ g hchk
    · exact cpcs (by decide +kernel) lowS_53_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_41_18_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_57_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_45_18_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_2 _ g hchk
    · exact cpcs (by decide +kernel) lowS_45_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_29_34_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_60 6 s (0,roots_60) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_61 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_60_2 h
def symsG:List (List (Nat × Nat)):=[[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_61==dom_61) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 1000003 zs symsG zs (hk 1000003 zs)
theorem ori_ok {v ys} (h:RunD true dom_61 goalM v ys):RunD true dom_61 goalM v (ori ys):=pickMin_runD 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h
def Z (s:Nat):=barP true dom_61 goalM mpG SD SS NN htAt idxH ori 1000003 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 5 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 5 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 45 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 45 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 116 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 116 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 209 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 81 128=true)
private theorem z5:∀ i,0 ≤ i → i < 209 → Z 5 i=true:=(range_split z5_0 z5_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 82 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 82 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 13 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 13 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z8:∀ i,0 ≤ i → i < 1 → Z 8 i=true:=span_ok (by decide +kernel:span (Z 8) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 8):∀ i < NN s,bar true dom_61 goalM mpG SD SS NN htAt idxH ori 1000003 pool6G mkCut s i=true:=by
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
def RootG (s:Nat):Bool:=scr true dom_61 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 5 4=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 8) (h:RunD true dom_61 goalM s xsM):False:=by
  have hmin:4 ≤ s:=by have hl:=run_len h;change 5 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_61 roots_61 goal_61_2 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_61_2
theorem lowS_61_2:Lower true dom_61 roots_61 goal_61_2 9:=S_61_2.noCircuit
namespace S_63_0
end S_63_0
def dom_31 : Nat := 0xffffffff
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]
def goal_31_from_61 : Nat := 0xfef8fae0
theorem lowS_31_from_61 : Lower true dom_31 roots_31 goal_31_from_61 9 := lower_iso [(0xcccccccc,30)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_61_2

end Case1

namespace Case2
open Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def dom_7:=0xff
def roots_7:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0]
def dom_11:=0xf0f
def roots_11:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0]
def dom_13:=0x3333
def roots_13:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_14:=0x5555
def roots_14:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_25:=0x3030303
def roots_25:List Nat:=[xs256.getD 0 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_42:=0x50500000505
def roots_42:List Nat:=[xs256.getD 1 0,xs256.getD 3 0,xs256.getD 5 0]
def goal_7_48:=0xe8
def goal_11_48:=0xe08
def goal_13_48:=0x3220
def goal_14_48:=0x5440
def goal_15_48:=0xfee8
def goal_22_40:=0x540040
def goal_23_32:=0xe800c8
def goal_23_40:=0xfe00ea
def goal_25_36:=0x3020200
def goal_27_32:=0xe080a08
def goal_27_36:=0xf0e0e0c
def goal_29_32:=0x32202200
def goal_30_32:=0x54404040
def goal_31_32:=0xfee8eac8
def goal_42_1:=0x50400000400
namespace S_51_8
end S_51_8
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
def isoMv_25_36:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_25_36:Lower true dom_25 roots_25 goal_25_36 4:=lower_iso isoMv_25_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_25_4:=0x30303030
def gzo_25_36_4:=0x30202000
theorem lowSh_25_36_4:Lower true dzo_25_4 roots_25 gzo_25_36_4 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_36) [(dom_25,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_36
namespace S_29_32
def pairsG:List (Nat × Nat):=[(1,9),(5,13),(5,21),(8,9),(12,13),(12,28),(17,21),(17,25),(20,21),(20,28),(24,25),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_29.map (· &&& dom_29)
def goalM:Nat:=goal_29_32 &&& dom_29
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
    (if pm.testBit 0 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_29 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_25_4 4 s (0,roots_25) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_29 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_25_36_4 h
def symsG:List (List (Nat × Nat)):=[[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_29==dom_29) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 goalM v ys):RunD true dom_29 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_29 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_29_32
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 5:=S_29_32.noCircuit
def isoMv_22_40:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_22_40:Lower true dom_22 roots_22 goal_22_40 4:=lower_iso isoMv_22_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
theorem lowS_23_40:Lower true dom_23 roots_23 goal_23_40 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa00aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_22_40
def isoMv_7_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_7_48:Lower true dom_7 roots_7 goal_7_48 4:=lower_iso isoMv_7_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def dzo_7_16:=0xff0000
def gzo_7_48_16:=0xe80000
theorem lowSh_7_48_16:Lower true dzo_7_16 roots_7 gzo_7_48_16 4:=lower_iso (d1:=dom_7) (roots1:=roots_7) (T1:=goal_7_48) [(dom_7,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_48
namespace S_23_32
def pairsG:List (Nat × Nat):=[(1,3),(2,3),(2,6),(4,6),(5,7),(5,21),(17,19),(17,21),(18,19),(18,22),(20,21),(20,22)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_23.map (· &&& dom_23)
def goalM:Nat:=goal_23_32 &&& dom_23
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
    (if pm.testBit 0 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_23 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_7_48_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_7_16 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_23 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_7_48_16 h
def symsG:List (List (Nat × Nat)):=[[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_23==dom_23) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_23 goalM v ys):RunD true dom_23 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_23 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_23 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_23 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_23 roots_23 goal_23_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_23_32
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 5:=S_23_32.noCircuit
namespace S_15_16
end S_15_16
namespace S_55_8
end S_55_8
namespace S_62_0
end S_62_0
namespace S_61_0
end S_61_0
namespace S_43_0
end S_43_0
def isoMv_27_32:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 5:=lower_iso isoMv_27_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_32
namespace S_59_0
end S_59_0
def isoMv_13_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_13_48:Lower true dom_13 roots_13 goal_13_48 4:=lower_iso isoMv_13_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_14_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)]
theorem lowS_14_48:Lower true dom_14 roots_14 goal_14_48 4:=lower_iso isoMv_14_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
def isoMv_11_48:List (Nat × Nat):=[(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16),(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00,24),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_11_48:Lower true dom_11 roots_11 goal_11_48 4:=lower_iso isoMv_11_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_42_1
namespace S_15_48
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(2,3),(2,6),(2,10),(4,5),(4,6),(4,12),(8,9),(8,10),(8,12)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_48 &&& dom_15
def NN:Nat → Nat
|3=>2
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x804d157017d4d0b
|4,0=>0x443fc56f3770bdeb2f2504b62e12f4272b8d2b7e262ad8c118ab9c7114e1c470
|5,0=>0x57e3d3b0129291b907006be5
|6,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xffaafefe00fc00f000fa4444ff00fafaf0f000feccccfff0ffccfcfcaaaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x86408640e864081640387408d6408640c8140b8640a38140286098174064053210
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x22004
|4,0=>0x56a9950a9c52ea4946a885
|5,0=>0xe91aab05
|6,0=>0x3e4
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 15 then fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 4 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 11 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 5 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x80501605018690160d01
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>1
|4,0=>0x5141003100211100
|5,0=>0x7161
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 8 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xf7653210
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>3
|4,0=>0x8420d5
|5,0=>0x1bf
|6,0=>7
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 1 then [(dom_13,4,runOps true dom_13 (0,roots_13) ops)] else [])++(if pm.testBit 2 then [(dom_14,4,runOps true dom_14 (0,roots_14) ops)] else [])++(if pm.testBit 3 then [(dom_11,4,runOps true dom_11 (0,roots_11) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_7_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_13_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_14_48 _ g hchk
    · exact cpcs (by decide +kernel) lowS_11_48 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_7 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_7_48 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)],[(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0x2222222222222222222222222222222222222222222222222222222222222222,1)],[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3)],[(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_15==dom_15) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_15 goalM v ys):RunD true dom_15 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 2 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 3 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 3 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 1 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 6):∀ i < NN s,bar true dom_15 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
  · exact z6 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_15 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 4 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 6) (h:RunD true dom_15 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_15 roots_15 goal_15_48 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_48
theorem lowS_15_48:Lower true dom_15 roots_15 goal_15_48 7:=S_15_48.noCircuit
def isoMv_30_32:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 5:=lower_iso isoMv_30_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_32
def isoMv_27_36:List (Nat × Nat):=[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]
theorem lowS_27_36:Lower true dom_27 roots_27 goal_27_36 5:=lower_iso isoMv_27_36 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_15_16:=0xffff0000
def gzo_15_48_16:=0xfee80000
theorem lowSh_15_48_16:Lower true dzo_15_16 roots_15 gzo_15_48_16 7:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def dzo_22_8:=0x55005500
def gzo_22_40_8:=0x54004000
theorem lowSh_22_40_8:Lower true dzo_22_8 roots_22 gzo_22_40_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
def dzo_23_8:=0xff00ff00
def gzo_23_40_8:=0xfe00ea00
theorem lowSh_23_40_8:Lower true dzo_23_8 roots_23 gzo_23_40_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_13_16:=0x33330000
def gzo_13_48_16:=0x32200000
theorem lowSh_13_48_16:Lower true dzo_13_16 roots_13 gzo_13_48_16 4:=lower_iso (d1:=dom_13) (roots1:=roots_13) (T1:=goal_13_48) [(dom_13,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_48
def dzo_14_16:=0x55550000
def gzo_14_48_16:=0x54400000
theorem lowSh_14_48_16:Lower true dzo_14_16 roots_14 gzo_14_48_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_11_16:=0xf0f0000
def gzo_11_48_16:=0xe080000
theorem lowSh_11_48_16:Lower true dzo_11_16 roots_11 gzo_11_48_16 4:=lower_iso (d1:=dom_11) (roots1:=roots_11) (T1:=goal_11_48) [(dom_11,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_11_48
def dzo_27_4:=0xf0f0f0f0
def gzo_27_36_4:=0xf0e0e0c0
theorem lowSh_27_36_4:Lower true dzo_27_4 roots_27 gzo_27_36_4 5:=lower_iso (d1:=dom_27) (roots1:=roots_27) (T1:=goal_27_36) [(dom_27,4)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_36
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(2,3),(2,6),(4,6),(5,7),(5,13),(5,21),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(17,19),(17,21),(17,25),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>7
|3=>131
|4=>302
|5=>258
|6=>84
|7=>14
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xf56a1f9cd4b6d4718ec34ef78c5fec1e84cb36aa5e483e8534479cc6
|3,0=>0xca410ae5c5510f74c4f1028dbb05676fb68b2110b34bde55b0c90f16b02600acacb08d0bacaf0b77aa4a833ba98bd46aa1c581329d354eda9c1996d09a4922e099fdf6f89596f062939e38a391a329069161d1649126ee9e9122537e8fa5ae848cd93f208bd5b2f289f7fdcd89c3c46386bf0a3f82b5db707f62a33b7d6166916dec5a0a6d98ab276bc4904469ef5dbe68a7fc9d681b91a064fcbe5763b3cc1d62d9b6dd61c330f560120a2f6007a5455d1238125cf465f25ad289835a375d155924bc4d58b575a7587e57c756e89399552ab1c4509a7f6c501b78f74fa8a7b04e05812e4b3c7a804a97c9ac49754ed647c6fa82470a5cc645a36502459b00204535264144c701f640c0e7c6409e5e513f9fcc513f5dcc413da1d1603d9645c73d4d68483b36d6993a2501ca3888b023364ac10934b24baa3426ec7c341cd23d327a6fe6318acd9130f9833230b82b90307d48ca2e2240232d6317072c6d059e2c37be842c2731042a69ac7e28ff4e1c27dcd34626b7fa1024812a8522624656202b40fc1e109a031c430be91c0955d01b8d6a361a275a1319dcd7c61861eee916e05e5515ed589f136de1a21346ad641184cb1e113cbe53106281700ea95a0e0ea2f8410deba9d50d0a76280bcfa8760ae8822e0aa7b6b009cc5dd4098a08c608bf775506a9f90f04e9f8c704d89e9d0427963002cbca3d0264d830014ddb2e
|3,1=>0xe4680b7ee19c44e3dacf3814
|4,0=>0x3f5dcc413e9a767d3e92c9913e54fa973da1d1603d893b2c3d86ab1e3c1a10233c109fc33a2f451f38f076f337c31de5379f53e63786d9bf366e3bbf3662cb6a36374edd362ce41d35f20157359a4ad234d2bbf333e8e3c733954b5a331f1062327a6fe63201a3d131c07e7731a3e9523170e96430b82b902fe3cb7c2f9385a62e5608a12e4499be2bda19dd2bcb972c2b2553822a4bb8ce2a2a4ff12a1dc82e286e5510273b64d4272f99e92654e857252e722e24f9772124a6669623863d5722b1f1752298ee68216bd392216a342f2016343e1f7e35a31ef9d35d1ef6f8651eba38e61e46f3821de0f1b11ddb8fcc1d953a641d51fb051d4595111d1e44c11d1cf1cd1d1729471ce965801c0955d01bd0fa9f1b92ecfe1a6f6b6f1a3f88121a33fbe319b6c12a18b9ff74189b0920185caaf5181cb76217d88cd6177d02341742191d16d9650a16621c6c163ecc2815feb1a915d5aaba1519cabf151720b414f9da3314c83fdd149ee5ce13936ff7132d6ea811a6453e11982b5b1192a17f0e616dc10deba9d50de343b40c71fe630c39d32b0af493e30a91a3ed0a673ee109d66ab60995131409701b2d095a304e093d1a6708c6b48c082bb2f907d288fa0795c01807711ece07044c8606d5d98006bff29b0653e7fd061ff50f04526d98044d1ef6030fac4c030deb0602ff50a202b55aa10220e3de01f6885100ac2075
|4,1=>0x999430e898b8184397db5c1497d7e165967af1b49596f06294aa391a91a329069126ee9e903a00d88fb4e2818faad6bf8f89dd9f8f5c78898ea7cf768dc32e798c1bd8ee8be654fe8bbcacfc89f7fdcd8769f47e86bf0a3f859221d8856ca5c9835bd69682ac1a80826199ba81d2980c814c2fc7812ed8c180f8a0fd7fff301f7fa595617fa4738b7f620e257d0379b27bf112d87bec798b7baa0aa17ae562da796e0e3778e8a7a878c00d1e780b9354766690ac757539bf753bb4ad751fdd9774944693739e532a7358b0df73496e1870ea08487090d91e6f64164b6edf4c7f6e5009296e2162966e1db5af6df55a3c6dd24e0f6d0ca7d56c37d5ca6b6a41286b220e5a6a0ce04069eea2bf681d274b66c7162865d2413a6539b3396446456663ce8b446378063a6373dbe2632c3f68631dab3262420584610a451360a6b92c5f02e12e5ecc106a5ea28f925e9974da5e4ac6625dc393f95d5fefa75ce5d5965b9591b15a61957858b575a75867a6165797230855d202a455058d5a54f85fc3543bd6f1533c64e252e3179452b9fb6452824ed4527f189e50adef194f3a5f034e0658254aff15cf4abb9ddd4a447f0248233c2547d6c2924779ad824751c4f5466bb67545d6b026455f5d1544c701f6447230f54337887342cc454242994b4a42269b13417856d040bacd3b407e69994056b4ba40022f313fc3a61e3f66498d
|4,2=>0xfadb57f2f94c1570eaa42c48e37626bce1de62c4e10c1333da93bc79d4e5d36cce838bb9cc40ac2ec89f9dddc8360337c7b89038c6df32aec6526190c645282bc3e010efc17965a9be44c5e7bd4c59b8bc2b9dc9bb63907fb76d4208b4bb271bb3a5ec8baf1a4984ae03d8e4ad9665efad881b03abf5347aabc7dc7aaa48da52a8537a75a70c652da6d5b928a4c5ce06a3b57be7a1a6335da0b7a2c2a09ebea09fed8d6d9eca1beb9c89c2f89b5d5b159a9d9a389a6aca22
|5,0=>0x43dfabe24358f550431deb014319edeb427b26d8425b66cf4244a0e240f8329b40dd29da40d49df040c8b4c140bd4fd5408f88274073ea4b3f8718b73ebe0cb33de06abd3d67fb903a5d89983a3cbe7d39bdffda39398c8438e89bda383e6c7137cda7f237b1fffe3775142c366b3531362ce41d35b5e6c535a080f03567479334ff69903475e8c93349baee32512a9431bea6153123a890310354fe30e877f630c2fcda306e337b2f12aa542eece4332c0031742bfa7ecb2b373e1f2a37788328cfa3f6274dc3c326439a1a25bfc91825516548240843682301ae1321faf87021f54f5721d08c112194ce9b2115b8de20e5646a1ebffd381e6b8a021e489d4d1de044ca1d853eac1d2275031c6866fd1c0850591ba036781b67e75e1b13165d1a80579d1a466b8b197366b7192a467a186ed88f179d969315e918d415cb7182153b5be514c83fdd145cce64145953b51442b6c81400b75b134c3aee12ef47ae12b1852b11a6453e10d02a870e290ae80e00f47e0d574f4c0d1f19440c3b303a0bf274900bc415b80bc1162909e08ade09a7d8f709951314097b662508d28bee086b9afb0867c74e084bb8820811cecc072cd911070adda606c005bf063fd312060752a90500130004f9784904f6ee0903fd00cd0362d51d03486bd803026ea402174f7101df929b01d6939901c638ea01a2813b015a593100ec9e360067d350
|5,1=>0xec927571e47a6982e3d4fe57d704caf4d28b70f2d0fe898ed080abebc76d0723bea8a026bceebcd0baf049d3b744f36caf930799aed8f1e2ae6025cdab5a7594a7fc7918a684b1daa5dd5bf1a4ce50bca3368cc4a2643d33a236c81aa1c44cfda129948a9fbe3e359ec076b19d69ed2d9c55d9d49c233cba9c051afd9ad150299a19852c99cfb3d0999e641d99989b97997cc6bd97b096a9964edcee949e29b294580ad79392a0479337e7069252a89a9161d1648f89dd9f8e366e858e127b088d2d5fe58d0267a78ca00cef8c4e38768c3a8743897949ca8946e502891e5fbc8860caa984aaed5884a647a883ff3e6e829619e27f36ccf17f30454d7ea82caf7defba927db5bc9878180520780e9d697780d6c176a33ec775a848c075746e58751696de74656a0273dc95fb73cdae277372e193712a1940710c45666de7fdbd6dd977086c37d5ca69896e1d680000fa66159e9f65fb51eb656c93bf647d74b3636fcea262a2f7be5ee7f2835ec37a3c5e342b405d8d85835d716bf35d5fefa75d4222545d2650f05d0e99285ce5e66c5ce5d5965c5c98925c3db75c5adf94395ac3cbe45a64fcf859c8630959967f3a5966f1845762308c5761180d56994abe5653f03252fb5306527f189e5270c80551c7b8e5506d53ad4ff701f34ec2c2d84ead54614d553f164c7b51494aebb28649df6f9248398ccd47c0752346912e38
|5,2=>0xf483970feeee01a8
|6,0=>0xf2d7842ae2f6cc52dc943f54d97bde48c6adaa0ac649b516b70b8c48ace40d3fabe6e128a8c42078a7848147a74692fba2e1b633a0acd41c9ffc183a9be1e518906efd648f9570a78215fd6d7f482aa17c00ecf67b3a363b79238a6e723bc33370098edb6f02c2726efe5e576dd427ae680ad10c6501036f64dcc446642830f25f9423af5f84236f5f4048c95e12612d5c56672d5aa3dacd5a4a0be5584d6a3b572d3d6a565fc1da52b9fb6450606b134c7b51494b36dbf445e0152944e04f8d431deb014268d4dc3e67f4813abf154634b0cb8f32ccbb283161aefe2eb642ba2b039043241cb7b223c89a0a22c5a1b521b4f2fa205f4d0c1edb55471be11d8c18907b5416e0a50516032cd515e918d414e19db8138b8c9513195c2512b3d679118433b6117fcf9b10de97a00ea311090e61fd760e5dbbed0de343b40d59fc0a0ca6363d0a93ed5809e2bbbd090f6918
|7,0=>0xab95585a579c512c569c8b903e49a49334b0cb8f2e079448258c480e21a8620b205f4d0c202fbf56129dfe450d59fc0a09e2bbbd090d6eb4
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0x1414141444cc44ccffff2200ffaaffaafaf0faf0ffaa000044444444cc88cc8855ee55ee50f050f0000055aac4c8c4c8ff000000fcfccccceaeaeaeaffffaa00eecceecc15ea15eafca8fca8eac0eac0aa5555aaaaaaaaaa00ffff00cccccccca55aa55aff00ff0096969696f0f0f0f03333ccccffff000055aa55aa3c3c3c3c
|0,1=>0x152a152a565656563cfc3cfc0000ffaafcfc0000faf0f0f0c0c0fcfc3c3cfcfcffff8800f3f3000030303c3c555500000000aaaafcfcc0c03cff0000ffffc0c0ffc0ffc0aa00aa8855ffaa00fcfcfcfc55aa0000ffeeccccfcf8f0f0ff3cff3c3c003c00f0e0f0e0c0c0c0c003fc03fcf0a0f0a0ccc8ccc8aa00aa0082828282
|0,2=>0xffaa55aa0000ffeeffffa00077bb000070f070f03c3c3f3cffffaaaaaaaa0000c300c300003c003cf0f0c0c0eecccccc00ff00aaf8f0f8f0ffff3c3c3c3c0000ffffff00ff3c0000ddeeddee448844885656aaaafcfc3c3c00fe00feffeac0c033cc33ccddaaddaa0000fcfc3f3f00003f003f00d5aad5aa0000f5fa55ff0000
|0,3=>0x30303030babababa2c2c2c2c55145514ecccecccff00ff0cffee0000cfcf00000c0c3c3c9a9a9a9a0c0c0c0caaff550000aa00aaaa44aa4433223322aaaaeaeac3c3000000003c3c0f5af0f00000fffa2a2aaaaa151500001c3c1c3cffc0c0c0fffcff00feaaaaaaffaaaa0055fa55fa7f7f00005af05af0555455543e3c3e3c
|0,4=>0xa2a2a2a255aa5500cc00cc00fefefefea8a8a8a8f8f8f8f8aeaeaeaeffeaffeaea00ea00ffff55005500000000440044000000aaf0c0f0c000aa00003300330000cc00ccee00ee00bbaabbaaaa00000080808080550055000000f5f0fffa0000f0f0f050d5ead5eac2c2c2c2ffccffccffff8844ff300000aaa8aaa8ffffc300
|0,5=>0xf0f00a000a00fefe0a0afcfc8888aa88aa880000c0c0fffffcfcf5f0f5f0c000c000333300000000cccce0c0e0c0fff0ff0050a050a0ff003300c0c00000ff0cff0c3070f0f0ffff55aa2a002a00bb00bb003f2a000000003030ffaaaaaa00ee00eeeeeeeeee3e3e3e3e2020202000550000fffff0f0f0f000000f0c0f0c
|0,6=>0xff44ff44ff50ff50332200000044cccc888888880f0a00000050f0f00000fffc0f0a0f0a3f2a3f2aaa55aa00707070700c000c00ffff0c0cc080ffaafc000000005000500302ffaaa000a000545454542222222244004400fceccccc50005000f4f40000fcfc00fcfff0fff0f000f00002aaaaaa040404040000aa000f0f0000
|0,7=>0xffc0ff00153f0000323232321f3f00000a00aa00fefeaaaaa8a800001e1e1e1e28282828f300f30000fe00aaffbb0000f2f2fafa000a000a4444cccc22002200fffcfffcff00f300ffff00aaa0f0a0f005000500feaa000000aa55aa11221122eeaaaaaa40404040fe00aa00ffea000050505050ffff0044f050f050ae0cae0c
|0,8=>0xfefcdcfc0000fca80000fcfcfffc0088008850f0f0f00f0e0f0e00fc00fcfe00fe00fc00fc00fffc000074740000dcdcdcdcf0faf0fa00a000a0f8f8f0f0bfaa0000aa00ffaa55f00000fefcaa00af00af00cf00cf00faaafaaa5050f0f0ff55000054ff00001133000077007700e0e0e0e0103010300e0c0e0cffaaff00
|0,9=>0xa0a0a0a00220022fcccfcccfeeefeeefffaf0f05444544400000c0cccfc000088cc88ccbfaabfaa0202020254fc54fc0ff00ff0fafafafaa0a0a0a05a5a5a5a3030000011001100ffff3030acacacaceeaaeeaaeeaa000066666666545400000f000f00ddcccccc0000ff00003f000010101010eaea000000f000f0feee0000
|0,10=>0xff30ff30aaff0000fc54fc5403030000f0a000000eee0eee3020302030103010b0a0b0a0ddccddccab00ab00ffffffaacceeccee44cc000073507350cc44cc440202aaaaff303030405040500300ff00cccc00003f000000131300001f001f000c0c0000ccaaccaafcecfceca8fca8fc8c0c8c0cffcc000088008800ffffcccc
|0,11=>0xfafa0000fff0000077770000c0f0c0f0afaaafaaff3300002a2a2a2aff88ff880cae0caec0e0c0e050550000fcdcfcdc
|_,_=>0
def stPool:Nat → Nat
|0=>0x160c8140213020021a020043c06050c4003017828001a020205c1c020205a020e0b0181a0203c0204040ac2a2a030a41402140284e04040042a021306042021282848020e0840002118884202030803e10020043c1d0e06c101a0203c3202020602e08008582a020205002060984822100203c0202020201c02068300808058280009010200e02030140801018080200
|1=>0x400456020203c0202021349806020209602179281402050009248030b01408008ac2c3b020288e020d9181006090ec2230178b0140202088020a218008a020510c000a2210c000202108100404004821b041000202020207e02030947c02178287a1c0d8202a1b04004782f1d82800021d02002061c82800300302870370202002061b0286a020d82002061a000662f
|2=>0x2020021a03028001a02020c8060518c00020e020c40203184000203028c05f02020800404004bc5d0e06c102f160448a300510c00020e06c1e040417002020416c0204200043c0400878782c12828120203028b40407900025903160001c0203c2a040780478022b828ac022a82002100e010a80205000a602290200202020043c5103028a04f09828004e030280004
|3=>0x30280002009fcea02068944202031f8fa02031f000100e0e810020e06cf6060510000060500078023d02800790202002063c028ee1a020200202031d8ea06050008a02030280006051100004041d0e602021c8e202178b0e00637828dc1a0203c140604028da1002020020404004d80203000d60211820c80609044d40203028d24f340b0143b0510c0067330101065
|4=>0x101010014a00838041108404040400526020315c1400030ed240805040380404100041c0d82002020202002911d8101490478080c04089c40404470211a0242018581101010108c0087036081090004060522c00020302868000101814580013c262c128280808451cd12880202002024382002020221810061da141484030ec22830202002820302800061d8950280
|5=>0x30b014a50e0101021158080c7e521d404060526c00020302886000202042a31e21034040402944a104228e6061d82014a001018149f00008080800a28040605000ac1a030a4100a01010109e3981010010a8080c0a3f9d5083b022741402032704a9b0d01934080501876084c82804980225c100616028004501018580a0025808084a9cc0c2c051100002030b10a0a
|6=>0x201fcea0203028007301070080f0c808080800ac8040404005461a58810100a1801858b0050095e06050009e020302800020302800900106c10010d018100a572b4040404004041c02021581a02021560a42018762505018147f3a8f0041b0202002023d028fe7503010100a550080c0a002a5501a020204210030b04a0a0d010100a538c05e0616029081a022981402
|7=>0xf008080800b04108a601cd7e590101814000e01042400f008080800af8040407820021c02020022b032f408080500838040780438041087878065e010100a0d0185825050680c04042ec042f16029741c0203c42400202042010aae404060500004b8020200202030344a0a01018582530870080f108f0042f162dc1404452d8e6b50101858b4052cc0808052540c0a
|8=>0x4081826a1088203404040847802020219a01010b00808008080c0a6600034060206596020202002ca41018147f3a8184a0a0011434066481014025c0219073010184a0a000184a0a22000200202020020663810100a010198c25050700808109798a1a620201430178b01430030b01400030ec0808618083608108040404040043c020510c00020302800c2010700801
|9=>0xb5c04060982800020202042d60107008086aa10340405064040605001961a0302014d401070360f0400808010f008340404004380410ad96a06160ec14000d0180811040080c0a0034da402030280002030b04a6b010181400228080c9905000040605110000602021a20a33b40080805010100115808080800b3c0c04040299c02178185811010101e0101018080f
|10=>0x40085e2c0539860061282800e51d810100a720180811040403804040840c3b04029c6e20e01010210101042010f008381b0781876e104028040670028fe1a6f810100a0d3780808050101021008ac0c0405375b8020203c42010d01808a66d8080c2c12828380810b017e0616094144408008381b040187608050580c3b08820140604029b4d9030b04a0a6c0080808
|11=>0xe06c1e210101814007b818f00a3aaa404067b028003b0202014f57a0700808108703404040840c3b7982014020202002f2030ec080a78808080800bc00404040058002020204a0177818762505009dc0a3f9d40406050d4eaed02021149101021d8eb39819d40404028048a3f9d4e60616094144001010108a7480950130203c04280302800020202002e80d01808e7
|12=>0x541434040402a0802032981400030ee06080501808110410004060540a0202031bc14008004c08080501814503f9d4041c02020c806051fcea6e0306c100a22009fe2c1282804980202042060202014fe0107036210f0187604053f40c2c05000dc060203c14fc0107008087d819f404043e40468030b014790e0101021030ed340805018762505000040604029f002
|13=>0x1070085410868080800810110f0510c0c0a001140c0a22000380404438429601010100103010100a868083808108580d0c02020140254018080f010bc580a21868080885828040685028000202084e2940d0101e0a01070427f3a8400808008080d090203c0c3b0402a100202134100101070080c040080c0a811d60e040422926020202002bf03010100a8304c080f
|14=>0xd0101490178b04a0a228080c0a00140760404228e6028b8b04a0a010104608008080c0a001b804a80203c04ef8b0941515030b04a0a42068089d05018080805450041c040042c020301023130d0101490478680808108643808109002c0605000a075010184a0a1c07010210b0f005120422a220404004e6150101814200001877100402804061b0280002420181400
|15=>0x40840c3b0409414020202002b5034800808050080c040784404ef03028000203270140001018148a00018080f0547d500602020b00204084021601070582510818580a222e8340404085280602478100a010184c110401a3a0404028381a0d8204202034704a0a0101010018d8185825051b8041c0408634020e0204319010101e0a8c040381b040840406051fcfa84
|16=>0x50080d0a051fcea1a03010100a108083804040843c02030125408050090804040292a0203248100a3f8080c0494808080f052280c3b0202015280d01808080549c041c0202042c1010180926040280406051fceb2503010100a22490040602044112301071ec0404028040602488100a01018582505114041c0202042be0d018080805484040616094144401070080f
|17=>0x12100c0a3f9d4041c0203c4202020211475398080c045336e4602030b0080f050083804040859a0202020028a01070580404084040447020152e968080c0a3f9d40c3b0202014cb030114c080511020020e010102101018112c0538c04060203d680a0101876080538c040604264147f0e01808080511004061602800020304c5825053140c040402888020301010e0
|18=>0x202042d701018080c040280406044c1c6020402a660203028fea43a8080808451cde4020302260020e0101021388680c0404029b4061d811420805008380410878041c0d010102101010108a601cc380602020144001018080f4e8280404040951473010182208600187604040297e0202020148a4801876040402a5e020e010102167a1034040402804061b028fe75
|19=>0x101808a6042340c040402880e3010111c08052280406024e0100a010101137451ce001a03010100a034c8080805110340602020147f0d01808c4040280404044d81443014580808051cc04060203c14900101826040882108060202014440101808110432c0c0404028808f010185825054d40404042299073010180808054d004040402920a351008380404084041c
|20=>0xe0101025108080c0407828ea02020211495398080c040408598024c018081104500040404228e6020e01010213a8680c040402a7e0202284108a398680c040402922020202114739f0080c250500004069e010100a010194211044ec3406020201402030101e0a80818080805084880203010100a9d0080c0450844100203028fe759c8180808051124e02030280075
|21=>0x398083804045181402030b04a0a928080c040782a04061d8114c08050080d450202014060202014955b0080c0481820141c030ec0808050080c040402a881a03010100a453140c3b02020140203010100a350080c040782980020302015430b0080c0407a38140602020144435008380404085e14203010100a5b0080c040789414020e0101021600083804040868202
|22=>0x34f408a60501876040402a62061d810100aa63b4040404228e602098101e0805018760404029c6061d810100a6d80966040402914061d810114b05018080805112948409810100a5b0185825051140c2c12828880203010100aa48080c0408c88100203010100aa40080c040426d140203028fe75a3818080805100320203044100a3f8080c040402a5c02020201443
|23=>0x2022a08a39870340404084040605000fe7503010100a201fc0c3b02020154f010181a04040280c3b99010100a01010100a008180808051fc780202298108a398a83406020201484030ec080805008380404229200203029147f3a8080c040782a0a100e01010210101808a60882280020e0101021015380c04040283406020201433030ec100a718080c040402a9a02
|24=>0x48008095604228e6020e0104608108080c0a1a1fcea1a03010100a398080c0404554140203010220890d50041c02020420203028fe7519808095304228e6061d810100a0c818080805102a4020202114e339809080602044100203010100aa8818760404029f2020202114738d8080c0404229980202022968a3980808e104228e60202020152e538187604040284202
|25=>0x500838040452c420202021560a450080c0a3f9d5520203048080805008080845064e602178185825050680c0404028ea020302800020e0204216010185808050580406020280002034f4080a0c8080c2c0882014020e0101018108080c040402ab2020e01010210b0080c04044d8140203010100aac2a03406020201402030101157050080808453ace61c0d010100a
|26=>0x20201444398080c04078296c02030118811040083804040856c02778185825050080c9c160941402030b04a0a450080808451ce220202021152e398083804078280406ae810100a010185825055700c3b02020153f0d018095b040280c2c04029c64501018080f0538c340404028e60203010100aad0080c0407d2c140257818147f3a93c0406051fcea02030b04ab0
|27=>0x4028040602020147f658080c04051fcea020e0180808050080c04118201402030114d290101808080558c042c0202114730304c0808054bc0c3b020201490030ec08084e828040602022c40a010180808055840c2c1d810100a0101ac00404028040602044108a010185825050cc04060882014c00157c0c0a3f9d40404045791473010bc5825050080c2c128280006
|28=>0x51cc04060254c100a0101a64040402a4a0203010100a71818080805110040602384100a010180808a8028040404029147301018100a0b008080805229200203010100a453000406020204a0a450080c0404060140203010100a0b0080c040402aca020301022080500ac80404028040602298100a718080c0404029147501018260404028fe0203028fe750101808a6
|29=>0x457814061d810100a010180808b3828056603010100a010185825050080c04040941473010180808054b80406020201475398080c0453020147f0101808c453020140203012060805008380602020147f01018091304028040602298100a970080c04040284202420180808052d804060229a0608050080c04ab02014020301010ab050080c040402a3002030b00808
|30=>0x20201402034c81131010700c2c020201402030114cdb010180808052296c06020201569010183608050080c0805350040602020148a718080c0404594040602044100203010114b05228040699020147f010180808b402804060202014b63f8080c040cb2c042f03010100a01315880805008100a93c84048403010100a3f8080c04958201402034f40808050080c04
|31=>0x536c040602020148f0101808a604028041c03010100a013140c0404028040699284100a01018273202020140203010100a978080c040409414212c8080d3202020140203021c73f010700c0404228040616010100a108080c0404029c6900101ad6040402acc0602020140203010100a451fc04060202014710101a240404028040404028428a0101858080538ed406
|32=>0x80c04040280406020201473010180808051fc040602310100a01018080805064040602020142101018080805484048403010100a010180808054c404060202014e3010180808
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x48c01e600c300498018c00660003
|3,0=>0x88a0435021281054080a03f501f280f54078a03b501d280e54070a037501b280d54068a0335019280c54060a02f5017280b54058a02b5015280a54050a0275013280954048a0235011280854040a01f500f280754038a01b500d280654030a017500b280554028a0135009280454020a00f5007280354018a00b5005280254010a0075003280154
|3,1=>0x108a0835041282054100a07f503f281f540f8a07b503d281e540f0a077503b281d540e8a0735039281c540e0a06f5037281b540d8a06b5035281a540d0a06750332819540c8a06350312818540c0a05f502f2817540b8a05b502d2816540b0a057502b2815540a8a05350292814540a0a04f5027281354098a04b5025281254090a0475023281154
|3,2=>0x875043282154
|4,0=>0x1ad28d5546a0a34c41a3a8d09467aa3385199a8cb94652a324518fa8c69462aa3105185a8c194602a2fc517ba8bc945daa2e85171a8b7945b2a2d45167a8b29458aa2c0515da8add0564a2ad515428a8d453ca299514a28a3d4514a2855140289ed44eca27151362899d44c4a25d512c2894d449ca2495122288fd4474a2355118288ad444ca2215
|4,1=>0x24ba1249491aa4885242211fd48f4a4755238291ad48cca461522e2915d48a4a44d52242910d487ca439521a290bd4854a4255210a1071482ea4125206a90250808a3ff51fd28fd547e0a3eb51f328f8547b8a3d751e928f354790a3c351df28ee54768a3af51d528e954740a39b51cb28e454718a38751c128df546f0a37351b728da546c8a35f5
|4,2=>0x2ea2973d4b94a5c552e0296ed4b6ca5b152d62969d4b44a59d52cc2964d4b1ca58952c2295fd4af4a57552b8295ad4acca56152ae2955d4aa6854e52a4a95114a7ea53a529aa94c14a56a5265290a94714a2ea5125286a94214a06a4fe527ca93d149dea4ea5272a938149b6a4d74269293354990a4c3525f292e54968a4af5255292954940a49b5
|4,3=>0x387a9c294e0aa700537da9bdd0de4a6ee437521b954dc0a6db536b29b454d98a6c7536129af54d70a6b44357a9aad0d4ca6a1534e29a5d4d24a68d534429a0d4cfca679533a299bd4cd4a66553302996d4caca65153262991d4c84a63d531c298cd4c5ca62953122987d4c34a61553082982d4c0ca60152fe297dd4be4a5ed52f42978d4bbca5d95
|4,4=>0xfe8a7ef53f529f954fc0a7db53eb29f454f98a7c753e129ef54f70a7b353d729ea54f48a79f53cd29e554f20a78b53c329e054ef8a77753b929db54ed0a76353af29d690eaaa75053a5a9d194e82a73c539ba9cc94e5aa7285391a9c794e32a7145
|5,0=>0x4b3b258592ba895764a8b252d928ca940649d324d1925cc9286491aa475922ec9116485b24195200c8fa647aaa3bd91d2c8e3646eb236151a4c8cc6463323019174c8b46457322a19144c89c644b322455116c885643fb21e590e6c86d6433b218590b6c85744292a131908cc840641d320d1905cc828641132071902cc8106405320118ffcc7f95
|5,1=>0x570b2b6d95aacacf6564b2b0d957acab76558b2aad954aca9f654cb2a4d951aca876540b29ed94eaca6f6534b298d94baca576528b292d948aca3f651d2a8d1945eaa296511b2875942eca116505b28159400a9fa64fa327b993d0c9e264ee3275993a0c9ca64e2326f99370c9b264d6326999340c99a64ca326399310c98264be325d992e2a96d4
|5,2=>0x62db3155989ecc496621b30f5986ecc316615b3095983ecc196609b3035980ecc0165fdb2fd957e0cbea65f232f7997b0cbd355e6b2f1d9782cbbb65dab2ebd9752cba455cf32e619724cb8c65c3aae0596f6cb7565b7b2da596c6cb5d65abb2d459696cb45659fb2ce9566aab2f6594b2c8d963acb176588b2c2d960acaff657cb2bcd95dacae76
|5,3=>0x6ea337399b90cdc266de336d99b60cdaa66d2336799b30cd9266c63361d5b02cd7b66bab35bd9ad2cd6366aeb355d9aa2cd4b66a32b5019a74cd346697334a19a44cd1d568bb34459a16cd05667fb33e599e6cced6673b338599b6ccd56668a3331598cccc1565db32d5995ecca96651b3275992ecc916645b321598fecc796639b31b598cecc616
|5,4=>0x1bc0adda6
|6,0=>0x7b2bbd815eb6af5657a7bbd295e8aaf3e779c33cc99e56ef26579033c6d5e2caf0f7784b3c0d9dfacef8577933bb19dceaee0776d33b4ddd98eec5775fb3ae1dd64ceab7752b3a79dd2eee916745b3a159cfcee786738bb9ad9cccae60672d339519c9eae4967213b8eddc6ace2f6714b388d9c3cae1777083b825dc08adfe66fbbb7c59bd6cde56
|6,1=>0x7f033f65dfa6cfcc77e2bbf015f74cfb377d63be999f42af9a77ca33e399f10cf8267beabde15ee2ef6c5
|7,0=>0x2068d02e681434089a038d016680834029a008cffe67fc33fc99fd8cfe66
|8,0=>0x103a5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 364 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>0x302801070030295082103029030285082101070020210302b0302a0408503028030290329a451cd030280302b0302a0302b0302a0302b0302a508210302903028030290302801070030290302803029010700302903028451cd030290302b0302a010700302903028010700302b0302a030290302b0302a0202002021030280107003029030280302903028010700302b0302a010700302b0302a0302b0302a
|1=>0x3013030120302b0302a994c7020290202803029030280302b0302a020210302802028030280302b0302a03028030290302903028020290107003029040850302803029030280302b0302a030290202103028032980229b040290302803029030280302904085030280302b03028020200302a020200107003029014ac0202842010030210302b5336f040280402902023010700302903028030280302803029
|2=>0x3028030290302801023020290408503028030290302803029030280302b0302a02020030290302b0302a0302201070030290302b0302a010709e829620290301001010030280302803028030280438d0202b040290302302298040290302b0302b0302a03029030280107004059030280202b040850302803028030280202a03028160870202103028030230302903029030281288502020030280302393c85
|3=>0x208703028030290202201070021c70e0230302903028030290302803029030280302b0302a020230302b0302a0229b0302803029030280e0b00202103029020220408503028030290302803028030290302803029010b0030290344f0438d0202b04029030100302b0302a040850302803029098110302b0302801018020290302802022118210e010030290302b03028020230107003028040850302803028
|4=>0x202202087030280202b0302b0302b030280302b0e0200302902087030280408703028040850302804029020230302a0302b0402a0302b0302b0302b0e010030295336f0402804029030290302b0302a0302a0202103029040850302b0302a04085030280302803029030280202101070030230202201070040850302803029030280232f0402a0302b0302b02022010700202102087030280302b0302804059
|5=>0x302904028040290302b0402802085030280236f0402803028030280302b020290302b0338f0202b0302b0208503028030110301003013030120302b044c50202862029030100302b04485030120202a020200302a0302b020220302a0302b0402902298040290438d0202b0229b0302b0102302029040290302b030670402a0e01303029020210302a041cd0302a020290202903028021cf0302a041cf0302a
|6=>0x302a0302b030100402a030280301202029020280202b040280202a04029030290301102029020290302b020200302802029030230302b0202103028030230202b020290202a0302b0e02303029021cd0302a0302b03023030290131403011020290202802021
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>0xd30000000182000051000000000004101c40a4000000000000000000000000000000000104000000000000004400000000000000000000000000000000000000000000000000000000000000000002
|4,1=>0x6500001810000000000000000000000000000000002c41510000000000000000000000000000004c80000000000000000000000000024200000000000000000000000000000000000020400000000000000000000000000000
|4,2=>0x16a000000000015900000000000000a48502000000000000000000000004c40001210000000000000000000000000000004620001090000000000100800000000000000000001f10000000000000000074800000000000000000000000000000000
|4,3=>0xe8800000000000007220000000000000372000000000000000000000003520000000664000000000000000000000000000000000000000000000000000000000000000000000000c8400031100000000000000000000000000
|4,4=>0xf04000000000000000000000000000000000000000000000
|5,0=>0x1f08f2600000000000007723a91cc8e426f337080000006d13591a4800000000000000006633211888be65c30000000b625922c09588000551000000000054129100009e6000269000094647323080008a2432000000084200000010440003f21f080000003d1
|5,1=>0x641b1c58c20000003108000c316093004000bf15e92ec9724b725a90000000b3258900015e4000561aa89522000000298d48400000028c4000a2100028440009e34e8a68c0009824b8a58400095149900012068f14708001184000000224d0e4852000208d0227e3
|5,2=>0x7b8bd480000007a08000000f310000001e24f017710001da2ec10003a8800000000039cc000e6100000000000000000001c84e22708b7c8000de16e1364dae40000003549a64000690b408000cf1669000000000066080000000000000000000cb10000000000000
|5,3=>0x90180000000008f880023a40008e080000000008d100000000008c145c62a400000000000000008a0800000000089880022431020004388000000000430a126000840c1c4001061000000206702100040440000000003f8c000fd100000000000000000001f64f83
|5,4=>0x2466000
|6,0=>0xbe0dec6f257720005d86ea3741b915c0ade2000b695acad25681b31590ac62000b0958040015e2ae8d6cab43591ab90002aa5541a98d44aa034f1a6952ca925472a30d146883422a014fc67a53b29d0ce0a6c53429914c080012f19694b040012b1950ca46503262
|6,1=>0xcd0e647303962ca8e507263912c7963871a38c1c51620b0e3852c19604afe57d2
|7,0=>0x3503a71d30e947483a31d10e8474039f1cf0e7473839b1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0x4582241100830408200080021010007c03a01b00d006002c014008804001e00e0068030016009004001c00a0040018008002000
|1=>0x245922890040820310004bc24e0cf867431a18b0c3861830a1840c0846421a10c0840414202100071828013e09d04a024412008e
|2=>0x8cbc62e3111818c0447620108f846c2020330114de267531490d450a08100a8044001aa8b1e58b2c4940097a4ab250127c93a492
|3=>0x56feb5f5abacdd65eb0151d8cfc676337198
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
|3,1=>0
|4,0=>0x4380000800000080400700000000800000000008400000040000004080400408001000808b8000002020010000040008000000000438000000000400080000000000000000100003800200000021c08000000001408000001c000000008000387070000004000000000102000000001
|4,1=>0x83800000040000800c800000707001020004000013200080000000000000100000000001000000100001c5c01a080000000380000e00219060000002100000004c800400000000008002102000000002001038002000002e0000000008070000004000400000000000000000
|4,2=>0xc8000000000000200003800000080070010700080000000000000064000040020004002000008380
|5,0=>0x5204d000048c9702a02170a0d2010a000014200080120438700aa180013801a012c0080e24005032c00498002972e0030008140811caa89c0020e0e0000201021820d4c002171e4c0000800d150a147830000b813454046000004b5600a044c0111c18002010000b80005c0052000217
|5,1=>0x2380003400c001c000000200000026808000003847000000140038700040000004f005e1c01000114e500e870008a800100107041c0091c34040072e6403a000040e021c1560e3c00000040390000000080008174047017aa560000040802e0401736000002e000000e000042000000
|5,2=>0xe00
|6,0=>0x2069c903442d864060304b882bebf72a1f02febc7232a181c0a67bec7718a3d140080cd9c02e54f0eb2903af02549edb7d36aaa402a673682e56a0025a1351715f5d773406a3b67237
|7,0=>0xad267105dfc2d2f3fcefcb5f
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 13 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_15_16,7,runOps true dzo_15_16 (0,roots_15) ops)] else [])++(if pm.testBit 1 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 2 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 3 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 4 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 5 then [(dzo_13_16,4,runOps true dzo_13_16 (0,roots_13) ops)] else [])++(if pm.testBit 6 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])++(if pm.testBit 7 then [(dzo_25_4,4,runOps true dzo_25_4 (0,roots_25) ops)] else [])++(if pm.testBit 8 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 9 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 10 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 11 then [(dzo_11_16,4,runOps true dzo_11_16 (0,roots_11) ops)] else [])++(if pm.testBit 12 then [(dzo_27_4,5,runOps true dzo_27_4 (0,roots_27) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_15_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_13_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_7_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_25_36_4 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_11_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_27_36_4 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_15_16 7 s (0,roots_15) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_15_48_16 h
def symsG:List (List (Nat × Nat)):=[[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4),(0x2222222222222222222222222222222222222222222222222222222222222222,1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 7 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 7 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_0:∀ i,0 ≤ i → i < 64 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_64:∀ i,64 ≤ i → i < 128 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_128:∀ i,128 ≤ i → i < 131 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 3 128=true)
private theorem z3:∀ i,0 ≤ i → i < 131 → Z 3 i=true:=(range_split z3_0 (range_split z3_64 z3_128))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 64 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_64:∀ i,64 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 192 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_192:∀ i,192 ≤ i → i < 256 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_256:∀ i,256 ≤ i → i < 302 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 46 256=true)
private theorem z4:∀ i,0 ≤ i → i < 302 → Z 4 i=true:=(range_split (range_split z4_0 z4_64) (range_split z4_128 (range_split z4_192 z4_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 64 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_64:∀ i,64 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 64=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 192 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_192:∀ i,192 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 64 192=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 258 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 2 256=true)
private theorem z5:∀ i,0 ≤ i → i < 258 → Z 5 i=true:=(range_split (range_split z5_0 z5_64) (range_split z5_128 (range_split z5_192 z5_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_0:∀ i,0 ≤ i → i < 64 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 64 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6_64:∀ i,64 ≤ i → i < 84 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 20 64=true)
private theorem z6:∀ i,0 ≤ i → i < 84 → Z 6 i=true:=(range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 14 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 14 0=true)
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
theorem noCircuit:Lower true dom_31 roots_31 goal_31_32 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull

end S_31_32

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
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def posted : BF 6 := fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4243095552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def tab : BF 6 := fun x => Nat.testBit 18368189229188022272 (Nat.ofBits x)
theorem targetEq : posted=tab := funext (all_pts _ (by decide +kernel))
def points1 (k : Nat) (j : Fin 6) := xor (([true,true,true,true,true,false] : List Bool).getD j.val false) (k.testBit (([1, 0, 3, 4, 2, 99] : List Nat).getD j.val 99))
theorem floor1 : ∀ k, R (phi (5 : Fin 6) false (nz tab)) k (L0 6) → 9 ≤ k := by
  intro k hk
  have bound := observedFloorDual Case1.dom_31 points1 _ Case1.roots_31 Case1.goal_31_from_61 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) Case1.lowS_31_from_61 k hk
  omega
def points2 (k : Nat) (j : Fin 6) := xor (([false,false,false,false,false,false] : List Bool).getD j.val false) (k.testBit (([0, 1, 2, 3, 4, 99] : List Nat).getD j.val 99))
theorem floor2 : ∀ k, R (phi (5 : Fin 6) true (nz tab)) k (L0 6) → 9 ≤ k := by
  intro k hk
  have bound := observedFloor Case2.dom_31 points2 _ Case2.roots_31 Case2.goal_31_32 9 (by decide +kernel) (by decide +kernel) Case2.S_31_32.noCircuit k hk
  omega
theorem floor0 : ∀ k, R (nz tab) k (L0 6) → 11 ≤ k := by
  intro k h
  obtain ⟨k1,rfl,h1 | h1⟩ := two_gates (5 : Fin 6) (nz tab) (ne_F _ (pt 15) (by decide +kernel)) (ne_F _ (pt 3) (by decide +kernel)) (reads (5 : Fin 6) _ (pt 3) (by decide +kernel)) k (L0 6) (good_L0 _) h
  · have bound := floor1 k1 h1
    omega
  · have bound := floor2 k1 h1
    omega
def witness : List Gate := [⟨.and,[2,1]⟩,⟨.and,[6,0]⟩,⟨.or,[1,3]⟩,⟨.and,[8,5]⟩,⟨.or,[6,0]⟩,⟨.or,[1,2]⟩,⟨.and,[11,4]⟩,⟨.or,[12,9]⟩,⟨.and,[13,10]⟩,⟨.or,[7,12]⟩,⟨.and,[15,3]⟩,⟨.or,[16,14]⟩]
theorem witOK : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,17⟩ (List.ofFn x) = posted x := by
  rw [targetEq]
  exact all_pts _ (by decide +kernel)
end PEqualNP.Outside.L_meta_47289_aux
open PEqualNP.Outside.L_meta_47289_aux PEqualNP.Outside.L_meta_47289_aux.Logic in
theorem PEqualNP.Outside.L_meta_47289 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4243095552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4243095552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  apply mono_shape2 posted 11 _ witness 17 (monoOK_sound _ (by decide +kernel)) (by decide +kernel) witOK
  rw [targetEq]
  exact floor0
