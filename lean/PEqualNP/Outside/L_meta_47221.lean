import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47221_aux
def packedNat (xs : List Nat) : Nat := xs.foldl (fun a b => Nat.shiftLeft a 64 + b) 0
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
  [(OfNat.ofNat (packedNat [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),
   (OfNat.ofNat (packedNat [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),
   (OfNat.ofNat (packedNat [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),
   (OfNat.ofNat (packedNat [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),
   (OfNat.ofNat (packedNat [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),
   (OfNat.ofNat (packedNat [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),
   (OfNat.ofNat (packedNat [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),
   (OfNat.ofNat (packedNat [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0]))]
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

namespace Case0
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
|3,0=>(OfNat.ofNat (packedNat [0xe8a74740,0x865805664ce5c9db,0x4658d5063537a6e5,0x20703c3a1ca9f09d,0x1aa2ff7f159ce3aa,0x1352da780a3445e4]))
|4,0=>(OfNat.ofNat (packedNat [0x8658056674bc4026,0x43d60cad3109826f,0x2e4aa4b60e367e88,0xd12eb640a23838c]))
|5,0=>0x86580566
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0xccc,0xcc0c303000000000,0x888a200220044440,0x33223322ccc0cc,0xc3000300000cc008,0xb030202044004400,0x220022cccc00c10,0x103030c000c0c333,0x3222288880000303,0xc0c33332,0x20c0c0c0c222222,0x220cc00cc3333000,0xcc00cc012121212]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x2094,0x8209499104a4104b,0x82082525c41292c2,0x9495104a438a812,0x9053910412904524,0x441810457b9a1290,0x4123041591412a42,0x441cc12904418820]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>(OfNat.ofNat (packedNat [0xb9152264448790,0xd216424839052064]))
|4,0=>(OfNat.ofNat (packedNat [0xaa9416,0x5ac6582af15bab25]))
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
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]]
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
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)]]
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
def isoMv_22_8:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
theorem lowS_22_8:Lower true dom_22 roots_22 goal_22_8 4:=lower_iso isoMv_22_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
def isoMv_26_4:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
theorem lowS_26_4:Lower true dom_26 roots_26 goal_26_4 4:=lower_iso isoMv_26_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_2
theorem lowS_23_8:Lower true dom_23 roots_23 goal_23_8 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa00aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_22_8
def isoMv_27_4:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]
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
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]]
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
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc])),14)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc])),14)]]
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
|0,0=>(OfNat.ofNat (packedNat [0xff0000f0,0xf0cc00ccaa00aa]))
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
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0xaaaa0000aaaa,0xaaaa0000aaaa,0xaaaa0000aaaa,0xaaaa0000aaaa])),15)]]
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
def isoMv_27_0:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]
theorem lowS_27_0:Lower true dom_27 roots_27 goal_27_0 4:=lower_iso isoMv_27_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_0
def isoMv_29_2:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
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
|2,0=>(OfNat.ofNat (packedNat [0xc54bcf16a243e007,0x5e483e851d10cd2f]))
|3,0=>(OfNat.ofNat (packedNat [0xcff5d3ec,0xbe228f98a6edf974,0x9fb3a03e978c9fb7,0x933bc6c68b62dac1,0x83ad25496c96a30b,0x6b7090ee680591f3,0x671ead68662f2617,0x619a1739615a82ee,0x61505e2c5e4c5351,0x5da8fd374cd5023d,0x4a191b6046fa4512,0x453a62ed42bbd825,0x3e8563cd3bc60e9c,0x3a71281d394d67da,0x37d66292371002fb,0x321543812e345357,0x2d8a0e452be1abbd,0x29893cbe2788e952,0x1f597f811dde67ef,0x1a9bdefb19b4f7a8,0x156fc58413119b3d,0x113ae45710ab6ed7,0xb26ef5607e3f72d,0x79900be0672d874]))
|4,0=>(OfNat.ofNat (packedNat [0x5688d1d5565f4157,0x5601c9865564bb72,0x55572d025548a998,0x54faa626549deb2f,0x5433b5d1540785fc,0x536da4f7508cadf8,0x4db85ab84d1c67c3,0x4cd3c8534ba284bb,0x4b41a5b04aa5f9c9,0x4a2030244a08ac60,0x49b8a47e4913efec,0x48eabe8948d486e0,0x4890ac3a47ab4461,0x472553af46370c72,0x4480cc21423b9671,0x414e41fe3fe1811d,0x3fd2b3553fd03fc0,0x3f9c81bc3f2c6a70,0x3e1b1abf3db3243c,0x3ba6254a3b89e5ff,0x3a3010433895d721,0x386acc3e3665bc84,0x35320baa3520d903,0x34ec33a53476ad5e,0x33ec8d3d3393229c,0x3323df3a32dd39c6,0x3201b7e93168ee19,0x31435d37309739d9,0x3046a037301e69ba,0x2fa823e32f267592,0x2cd112912cb64450,0x2b8910672a62e81d,0x2996df2428881a5c,0x2856841228045d3d,0x266ac617265bbe57,0x264aacda23d0c225,0x23be2a0a23ac3cea,0x230fb29522844dea,0x21df95cf214c89cf,0x1f3b2d251f193848,0x1ef9d35d1e781c9f,0x1dde67ef1dc0ca9f,0x1d7f5bb91cc658b6,0x1ca6ccbb1c3622d5,0x1bca36001ae9d3d2,0x1a1b5eae197998f4,0x19629db1189c4d35,0x1888cd1a183a3753,0x17fcbcf917f20b84,0x178caf1b172dc58a,0x1721e1451651cefe,0x163ce418160fe99e,0x15aea1aa1581cba4,0x11d4a3d211bca25e,0x10e0f8130f47ace9,0xe95c9f20dd0c53c,0xbcdac7c0bcb30b0,0x9df185b096d95de,0x93086f90814333d,0x7fcb05207f59388,0x7b11aa7065bb6f9,0x5c8191104c297ab,0x479181602b24f6b,0x1e65b6a00017a7d]))
|4,1=>(OfNat.ofNat (packedNat [0xff5e15baf94c1570,0xf8078e8bf536a6df,0xf39e311dee40bf51,0xeb7e8c98e8e9d742,0xe2d20566e268c367,0xe1f41955e10c1333,0xdf8bef1adf12d2d3,0xdb81934bdb4dcf9d,0xd9521e21d50a080e,0xd3854b10d2a13e10,0xcd2aeac4c9aecd25,0xc920e23ac880bf94,0xc70e3c0dc05fd933,0xbe15f70cbc65c425,0xbb15a33eba3f7d71,0xb9ceb912b87e64fb,0xb80f843bb7ad5e91,0xb77b94d8b671e6f5,0xb382137db2ec2b0c,0xb1c3e0dcaf631aa6,0xa73316d0a62ef6d3,0xa5ed6a75a13b7858,0xa020f9209ec682e3,0x9c7721ab981fdbb3,0x96fc6fd6948ece24,0x90f84e6a90378ca4,0x8ed99d898c406483,0x8ba2056e89f7f247,0x898b23b086f66efc,0x86cb1d9986856b88,0x854ecfac84c6cd03,0x83471d7d81ed4c48,0x8106b7ab80f18c68,0x80d48b487cfea507,0x7c45fdcc79f5538e,0x79bef57478e5d418,0x78bd6e307718b716,0x76dd6d8a766de0ce,0x74c1452573713146,0x71dcc57e71c31bfb,0x70c41c7a6ba4262e,0x6a81649168ed873b,0x68c46f746890d4ea,0x65af13e8652174aa,0x634c7c5a62d0254f,0x6273eddf617e4acc,0x60cd72c35e7533f2,0x5e46a5fe5cabb788,0x59d6400d5950245e]))
|5,0=>(OfNat.ofNat (packedNat [0x2687932226459f34,0x254d28b1252796d1,0x251b3b4324fd62b8,0x24f97944241448e0,0x240d8b88240cc3eb,0x23c9b0e223a68e3d,0x23439fef232ff528,0x23269a28232697d9,0x22fe11fc22888f8c,0x228408f72254f676,0x21aa4f512172df1b,0x215e695d20328dad,0x20212b0920084a33,0x1e9075211e489d4d,0x1e012f001dedd787,0x1dc83cfa1d7f5bb9,0x1d41a3051d227503,0x1c9d34911c77b5a0,0x1bc09f241b9f4624,0x1b0358021af5a9aa,0x1ad5ead31aaeeec7,0x1a30055d19e421be,0x19ccc01e199f328e,0x199abba7197507f6,0x1960f370193c0e44,0x18e5eeb6184a452f,0x17e3ce9917afaa55,0x17a9ccea1757f7b9,0x1674a63f16458e30,0x1601b38a158854d8,0x1585c5021516daa7,0x1506f0ca147cdb0e,0x1442cb0613991083,0x12a984e312a8ee77,0x11f7470911413172,0x10efe97d1081f18d,0xf8132da0f002be9,0xe3925870e1b53ae,0xd8cbd270d2b81f7,0xcdec94d0cca5d2a,0xca0ba860c39a23b,0xc19c63b0bbfd262,0xb8630760b859ff3,0xb8523220b82be3e,0xb726d460af8c57c,0xa9327e409b71d7b,0x9afb07d0964c278,0x9592de1090060e7,0x8ed0bf308dd7da2,0x84bdf690843a76f,0x838847f082d1ee4,0x803aa5b06ede689,0x6d2f52206c0c2db,0x6b483420696a89d,0x65e29090640b94e,0x63e19b505d9187d,0x55409fa054221c7,0x4a56fc80434110f,0x40b3db90398b6d7,0x1e0d145016d9212,0x114eff000ed62ef,0xdc4a1200d6aac4,0xcb1a3500570e2b,0x46f4b60005e794]))
|5,1=>(OfNat.ofNat (packedNat [0x5d8d85835d51b01d,0x5b5ed8a75adca08d,0x5aa3dacd5a379a0a,0x5a0c325658937c70,0x583705b8581e8477,0x57ed152f57dad993,0x570680925705627e,0x565349ba55cef0d0,0x556b85ef541ed8c0,0x540785fc527ea26f,0x5223e11a5207303c,0x51d1493250dacc1b,0x506d53ad502d3f54,0x4f96b06d4f5e5398,0x4ee59cff4dfa6d18,0x4dd7fad74d9c8800,0x4d831e704d0930a2,0x4c8880ec4be91a19,0x4bc8fc3f4bc5935c,0x4ab190e84a77aca2,0x49e1a73248773af6,0x48666ef147f935f2,0x476754ef47256c69,0x46f158b246eb458c,0x46601b224656db68,0x45e30b2445d287d2,0x453e13f743cab68a,0x43c09be843897dda,0x431deb01430c83f9,0x4307246542292037,0x417027cb41088dd5,0x40c20d1c3fecef01,0x3fb5070f3f8bba8b,0x3f28308d3dc7b916,0x3dacf2873d54498d,0x3cdcf3663c9cfad3,0x3c7656ab3bc019b6,0x3bb221af3b49228a,0x39ab8f23396f874b,0x392492a138e89bda,0x38c49e9138b77c21,0x3873b6c6380d8fb3,0x37bde90e37b1fffe,0x378ab6123745d2ac,0x3673b32435b5e6c5,0x34cb8c5d33af6019,0x3361118e3349baee,0x3263407831faa9a7,0x31b1baed318bef8b,0x31283349311f2159,0x311274c031004853,0x30fdd29c30c6e64e,0x3046a037300207d4,0x2f85b4322f39ec6f,0x2f3177ac2e6c6c0f,0x2e6a8a592df97b67,0x2dc0bcd32d92e009,0x2ceb07162b88c225,0x2b209e822ad95bcd,0x2a96e6c92a5caa89,0x29fd635529a16d52,0x29141a6228b1add5,0x28a5dfd9289c9507,0x285684122829abae]))
|5,2=>(OfNat.ofNat (packedNat [0xadfe94f5ad3e8844,0xacd54760abe2f73c,0xabaf62b6ab2cecb8,0xaa226dcaa9c1b7ce,0xa6bb0535a69b29f1,0xa5c68f7da4ab08d5,0xa4649c60a3dd0af1,0xa2dee3f7a21326d9,0xa1afea60a0c5401f,0x9ebff2249e6e4af9,0x9e4291d29d72ffe6,0x9d277c629cd5e3c1,0x9bb361bb9b11c62f,0x9a19852c97b8ba20,0x97898185963376b0,0x95d97151953b56df,0x951e490a942fb735,0x9420197f941bf361,0x93adbdf192580d1b,0x90df6b85903b9767,0x8f4bd6578eb0c02d,0x8eaa40c08ea91e79,0x8d4d92058d272b09,0x8b2e49b489bb14b2,0x87f50b0787deda81,0x8784f84a87583908,0x86d335778663fd88,0x85e5c09984920124,0x831c5169828e8798,0x81f04f20819fa6db,0x817af2b0811ebb70,0x80ead4d080e48c59,0x80906d0380555937,0x7fe116217f04d661,0x7eb9dba97e3b8a5b,0x7d5169007c356452,0x7bc8b5e57b63edf3,0x794fb1037876cea2,0x7837384077b5d474,0x76a37afa7521e344,0x749a54417372e193,0x733b2dfc72ce72ac,0x729b5cea71db98bb,0x70fd1b66709f56a5,0x6f7717e56f377215,0x6f0d47df6efcc0aa,0x6ea31bd76d6f1d03,0x6d2a97be6d24d094,0x6cc496896c80bbe3,0x6c3153126b924161,0x6b19ad756aba06bb,0x69fe365469f8ebd3,0x69f0834769e692e4,0x69dec52a69996eca,0x6902527e68a8efdf,0x67295bb066f81751,0x66c290d0658bf4f4,0x643ac4c363c90a06,0x63192b69628f8b65,0x61d839c3616f74bd,0x613162ec6052e056,0x5ffe437d5feb76b3,0x5fdcd7955ed4a50a,0x5eabd1f45e6955ba]))
|5,3=>(OfNat.ofNat (packedNat [0xff2e3ab3fc2fe23b,0xf83017e4f6767ddb,0xf56be69ff555f6ab,0xf545783af3bc1a1c,0xefb8dc81eecdfda7,0xeeca1433ec658252,0xe728f097e526253d,0xe264b1f3e0a7d313,0xdb17c451d9448a4d,0xd5d67c54d4d421f2,0xd4a232a3d3150e8d,0xd2c8117bd09b624e,0xce474655ce400dec,0xce12aa8ecd33e168,0xcc8e5474c9c8a910,0xc874c52ac4cec356,0xc4a3e741c3f36677,0xc0927103bef02a58,0xbe32de3dbae03efd,0xb909b478b8760e6b,0xb835eec8b7ee7d16,0xb7db4d7db7a3286b,0xb75c608eb58372c9,0xb4e85e13b47d5b59,0xb3d0b876b27fe350,0xb157e592b0fd4e37,0xb03e20e4b0290123]))
|6,0=>(OfNat.ofNat (packedNat [0x922a2e5090a07136,0x904980188f9570a7,0x8d2f93368cf1d972,0x892610a88765ed6c,0x8692decc8331771e,0x812b82c580efcea8,0x7fe116217f2d989a,0x7c2eb45a79238a6e,0x78deacde745f33c1,0x74064f5d71732e19,0x6f89a1c16a1bbc48,0x66df346c64400b45,0x642b4f8d63dcfeaa,0x62bee6be6294c3f2,0x61a6321d5f84236f,0x5f4048c95d1dc51e,0x5d129b915cf6f3ef,0x5bed828b5aa3dacd,0x59b24c6859204335,0x5836681f56c458c6,0x569c8b9056832b8c,0x556b85ef51a243e1,0x50ce08e54e7d552d,0x4c7b51494c35739b,0x4c1113e3489b25d1,0x469194cd44e04f8d,0x44b7c790431deb01,0x42c210404268d4dc,0x3f4a3df73f28308d,0x3b48076237d49b57,0x378ab61236eb4c6e,0x3673b3243646b8aa,0x35e7b92135423728,0x33c935fc3349e1f5,0x33445ff732ab7192,0x3213461930d5ae12,0x2ee8d5252ea1a60e,0x2d9fc0262d0a477b,0x2be693e62b5199d6,0x2a305cf828bc2318,0x28ae69ed2785873c,0x26de1cbf26d55d0d,0x2581e49d238725b1,0x238307f12382e757,0x22c5a1b5220d77ad,0x21b4f2fa20d08b5f,0x20b0149c1f710856,0x1b25f3a91b035802,0x1af425c0199abba7,0x193c0e4418a6ebd1,0x1727f37417232ed7,0x164de1ce162fa605,0x16032cd515ecb7e8,0x15dede7515af50bf,0x14e19db81495c976,0x12a8ee7711413172,0x10efe97d0d5df651,0xd2b81f70c5ebf74,0xa03e2b509a0ff5b,0x90f691808f6698f,0x8669b7e086127e6,0x81d8fae072515d9,0x5aa6454055409fa,0x51c01440046f4b6]))
|6,1=>(OfNat.ofNat (packedNat [0xfd90d141,0xf466fa6bf3bc1a1c,0xf2c3a399f290fc61,0xf114d409ec18059e,0xeb858de9e98fcadb,0xe86364c4e81ff617,0xe631ca24e526253d,0xe4fb2e48e4c8ff09,0xe3f418aee264b1f3,0xde4158b8d9c4f616,0xd8f0e129d869cccc,0xd3e5f5cece6c23d6,0xcd96d6cdcd3587fa,0xccac53a3c85d9b0c,0xc7f014cdc4c918ff,0xc2f34662c0a4267e,0xbfced975bf55ea1a,0xbdf5a666bb285d15,0xb98e8086b803f3d9,0xb7db4d7db600566c,0xb58372c9b4374d10,0xb30c4674b2b1ba1e,0xad2136f0ac6dc52b,0xabea8af4abde234e,0xaaecc24aaaae09fc,0xa941d0dfa7a7eaf9,0xa78f0814a74692fb,0xa6bb0535a5ec9609,0xa18c65939abc05fe,0x9a48487798993a0a]))
|7,0=>(OfNat.ofNat (packedNat [0xe39fa026d5d7a2ce,0xd4201d1eb98e8086,0xa78f08149069c14a,0x8fd54a87894af979,0x6432baff579c512c,0x569c8b90519fbd25,0x49a52f422e079448,0x2c56ab27258c480e,0x21a8620b20b0149c,0x205f4d0c1f16380d,0x1495c9760d59fc0a,0x9e2bbbd090d6eb4]))
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0xccccc0c0fafafafa,0xa0a0a0a00ff03ff0,0xccccc0003300ff00,0xf0f00ff000ff0000,0xf00f000000000ff0,0xfaf0faf0f0000f00,0xf00f0ffff0330,0x5500550000aa00aa,0xf0a0f0a0ffa0ffa0,0xeeeeeaeaff00ff00,0xcccccc005a5a5a5a,0xf00f0ff0cccccccc,0xaaaaaaaaeeeeeaae,0xf0f0f0f055aa55aa,0x3333ccccffff0000,0xeeeeeaaa0ff00ff0]))
|0,1=>(OfNat.ofNat (packedNat [0x333300000000cccc,0x5f005f00ccccc00c,0xff00000ff0ffff0,0xf00f000ececa0a0,0xcccccffc1a1a5a5a,0xfff0fff0f000f000,0xffff0ff00fff0000,0xfeccfa000f5ff0a0,0xf0a0f0affffcccc,0xcccc0000fccf0000,0xfa00fa00f0f000f0,0xff0f0033336c6c,0xf0f0a0a0f0f0fff0,0xfff000112255aa,0xffaaffaaeecceac0,0xfffffa00faaaaaaa]))
|0,2=>(OfNat.ofNat (packedNat [0xa0a0f0f0f000f030,0xeeeeaaaa00fa00fa,0xf000f0eeeeeeaa,0xff00aa0033333222,0xffff0f00bb33aa00,0xfaf0fbf0eeeeeeee,0xffffe000f000fff0,0xaaffff00cecece0a,0xfafaaaaaff000f00,0xfaaaeaaa33333000,0xffffa0a0faaafaaa,0xff00ccccc0cc,0xffff00fffff0a0,0xfcecccccffffaaaa,0xeeeee000ffaaeeaa,0xf0ff0f00cccc0cc]))
|0,3=>(OfNat.ofNat (packedNat [0xfafa0a0affff00f0,0xf0f00000000f000,0xcf00cf00afff0000,0xf0f0fa000000,0xf3f3f0f0b0b0b0b0,0x3333302050505050,0xffffeecccccc8800,0xccfe00faf0fffff0,0xaa00aa003030f0f0,0xf00fff0ffffff00,0xffaaaaaa44444000,0x50f050f0ff00fff0,0xee00aa005f5f0000,0xf0f0000011005500,0xffffaa00aaaaffaa,0xaaaafafa00ff00f0]))
|0,4=>(OfNat.ofNat (packedNat [0xcc00ff00fffff000,0xffaacccc4000,0xaa00faf03020f0a0,0xfa00ea0005ff0000,0x333330f055ff0000,0xffff5500ffc0fff0,0x5055050ccee00aa,0xfff0ccceeccee00,0x50f040f030203020,0xc4c0c4cfafaeaea,0xf003f0044444444,0xe0e0e0e0ff00f000,0xf5f00000000f0a0,0xfff0f0f0c0c0,0xf000f00ff0fcc0c,0xecececa0fccceccc]))
|0,5=>(OfNat.ofNat (packedNat [0xf00fafac8c8,0xfaaa00f0f000,0xfffff00f4444444,0xafaffafabb33bb00,0xff0f0000cffccffc,0xff55003232fafa,0xafaff0f0ff000000,0xf0f0f00f0f0a0a,0xfeee54444444,0x3320ffa0f0a0ffa0,0xfaaa0000ccccc800,0xffa0a0a00fff0aaa,0xfff00f0fffffaaa,0x444ccccfcccfccc,0x11111000f0f0e0e0,0x5500fa0afa0a]))
|0,6=>(OfNat.ofNat (packedNat [0xf0f0c0c5f5f4c4c,0xcccccccffffc0c0,0xf000ff00ff88ff88,0xcc00ccff00cc00,0xaaaa00aa0000f030,0xafaf0000feee0000,0xbbbbb000ccc0fff0,0xcccceeaaccccc888,0xeaaaeaaa3c3c3c3c,0x3300330aaaafaaa,0xbbbbbaaa103050f0,0x333310000000aaaa,0xf000c000aaaa55aa,0x44444440a0a0a0a,0xfeeecccc0ccc4ccc,0xf000f0f0c444c000]))
|0,7=>(OfNat.ofNat (packedNat [0xf00ff0000f050f0,0xcc88ffaa33f300f0,0xffccffccfac8fac8,0x4444f4f4f0ffc0cc,0x30303030ff30ff30,0xafaaafaaee00ee00,0xbbaabbaaaa00fa00,0xc0c0f0f04f4f4444,0xfffff0f000505050,0x50005000ff55cc44,0xaa00ff000c0c0c0c,0xf300f300c000f000,0x50505050f0f0,0xaafafafafafaaafa,0x555500005555aaaa,0xbbbbaaaab0b0a0a0]))
|0,8=>(OfNat.ofNat (packedNat [0x7700eeaaffaa,0xf500f5000000f050,0x4c4c4c4cff0aff0a,0xfaf0aa00ffccff00,0x5555005033332020,0xff0fff0c00f0fff0,0xfeeefeee54445444,0xf0fcf0fc70707070,0xfcecfcec3f000f00,0xccfcccfcc0c0c0c0,0xff33ff0051515050,0xff00ffa033003300,0xc8fac8faf4f4f4f4,0xf0affaaf0f0f000,0xf00000004444cc44,0x8888ff883b3b0a0a]))
|0,9=>(OfNat.ofNat (packedNat [0xff0ff000fff0ccc0,0x55004400ff00aaaa,0xc4c4c4c4cccc4c4c,0xff44444455555000,0xc0f0c0f055000500,0xb0b05f000f00,0x44cc44ccf300f000,0xaaaaaaaa0f0a0f0,0xeecceeccfa00fafa,0xeafaeafa04cc04cc,0xbabababa1f001f00,0x450045000000a0a0,0xf0f0f00fbfbfafa,0xdcccdcccff0a0a0a,0x5f00afffaaaa,0xfff000f0a0a0ffa0]))
|0,10=>(OfNat.ofNat (packedNat [0x32223222f0ccf0cc,0xffff500030003000,0xbaaabaaa00500050,0xfafa00fa0c0cff0c,0xf0f0a0f0aaaa0000,0xfccccccc0eee0eee,0xffffafaa0a0afafa,0xcfcccfcca0f0f0f0,0xf0f050f055554444,0xa0a0b0b005550000,0xfcfcfcfceeeeccee,0xcfc0cfcf555f000,0xccccecec44005500,0x11001100a000f000,0x45444544f333f000,0xe000e000ff005500]))
|0,11=>(OfNat.ofNat (packedNat [0xeeeeccccffaa0000,0xcccc00cc55445544,0x505000000000aa00,0xfc00fc00ffaaff00,0xcc00cc00f3f0f3f0,0xcccceeeef0fff0f0,0xfff000004444cccc,0x33303330cc44cc44,0x32323232cccc4444,0xff55000033333030,0x88888888aaaa8888,0xafafaaaacececece,0xffff00aa00c000f0,0xcceecceecd00cd00,0xa0aff0afaaaffaa,0x5000f000a000]))
|0,12=>(OfNat.ofNat (packedNat [0x222222228888aaaa,0xf00000cc00]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x170c40a07060200e,0x300601c062f17030,0x5a0a160200e00158,0x140e03150200e290,0x60140e28010304e0,0xd130200e25010141,0x240108c0a221088,0xa08010303e0a06,0x783a03010200e1c,0x106c0e000102014,0x1a010300a010c820,0xe180b8200e16060,0x540e030a0200e130,0x90200e0002844061,0x10301e01010380,0xa0d0102c0e000103,0x160a048200e0203,0xa04018080200]))
|1=>(OfNat.ofNat (packedNat [0x78200e0c029580e,0x3e01030aa080394c,0x18052a01c0a08038,0x9492530601410070,0x282c0e4701148680,0x8038141051038081,0x8052801c040e2781,0x410022703c100701,0xd49a080101c9800,0x259281049029200e,0x47230308a0722030,0xa43011082a08060,0x1c8240028107e3e0,0x281c7a03010f00e0,0x198200e3b1d0200,0xe39170303c38010d,0xc0e0001030103601,0xd46801198200e32]))
|2=>(OfNat.ofNat (packedNat [0x238084608379b804,0x340401cda6c35878,0xa08010300a07350,0x8100734868d00c0,0x401c820211814ce0,0x8060143e07331181,0x8650401c04050419,0x206306014106206,0x20c207208301007,0x20980042b0401cbe,0x50401c5249010d4,0xbc08038b80a2d039,0x7018140401c82020,0x2974105c0103c100,0x70d03010072096c8,0x80206014b4022c92,0x80a08010304e1f03,0x808180503960ae02]))
|3=>(OfNat.ofNat (packedNat [0x410300a2d0380818,0x50d81c040c02a04,0xe020607c0e69010,0x31000503808187f0,0x41d00431028200e0,0xc0a81c7e3e3f0300,0xa0b039a010073e9f,0x40f3d8200e0c04,0x1e80e79109e00a08,0x380818773b01c04,0xf2a01c9205088fc,0x203e010301e073a8,0x818050081410073,0xa11c040f0401c920,0x20603c3e07011280,0xa542480818081682,0x8e60c029c80e0202,0x9c41007380141007]))
|4=>(OfNat.ofNat (packedNat [0x3a286449060783a,0x3f1f008181e1c020,0x40c02a400e0c1a0,0x200e410103010074,0x78081807472340a2,0xa0401c8e2e0603c5,0xa07221f818052a00,0x8188c04074040803,0xa2cb60206128a889,0x10301e5d040300e,0x8a20808184a44820,0x18880401c8202060,0x800a080105c10070,0x30100743a180a4,0x80386092340401c6,0x4852583108080380,0x810071f800040c04,0x287e1e028200e47]))
|5=>(OfNat.ofNat (packedNat [0x401c5605038fc7c,0x2159dc100701030,0x541f03808fe2b040,0x1c040c0290c0e021,0xa0200e9b0108c180,0x506808180803a680,0x40e0401cdc021a8d,0x16070102c0e832d,0x80932050401c422b,0x401cf2020613c1e,0x80281d144724814,0x10074c124040c028,0x1d2e0c0287c0e964,0xa9640a0803809283,0x40401c1808039052,0x60202a4810111703,0x5a07348086a0803,0xa44040c2e820d205]))
|6=>(OfNat.ofNat (packedNat [0x10303c272a0cc04,0x803800040c02951,0x5002060800a8a010,0x302a0b0380818050,0x6874180803a9cf20,0xc3287c0e60530081,0x8052a008180503a9,0x404a40401c000206,0x140ea3258314408,0x3814100723a8404,0xc040287c0206014,0x6801012801007248,0x300e3f178f8040f0,0x427c0e9e010200e0,0x4f0081805008086,0x80803a1404590282,0xc40c02974109d01,0x300a9c038081c84]))
|7=>(OfNat.ofNat (packedNat [0x3282008020287c22,0x1001030320803808,0x4605059bd6e0c028,0x2c0e9e0609c10070,0x12d81007001640a0,0x803ad4040c040756,0x80c042cc0e790281,0xc7a3f1f008181e05,0x87404b2028200802,0x158200eb1158200e,0x983c808181f03ac0,0x18050401d5e02060,0x140eae0101410075,0x6809580f0401c180,0x8039042644062ac0,0xa08010200e6e2e00,0x856055501c04351a,0x6c0e02548303c08]))
|8=>(OfNat.ofNat (packedNat [0x2480818052d31004,0xc618140e0206014,0xec2010ad8208038,0x81007000ec040c0,0x2b000e23060140e0,0x3010200e32000b81,0x8151681d3c440601,0x4a80206054ba0817,0x145a11080a81007,0xc2fc0408038002c,0xc5f0145a0725830,0xa0b0380818052a2,0xf40a080391d78050,0x401d6a49028200eb,0xb2480818ba0281c0,0x40c0a87c0e0c042e,0x40e41010300ab803,0x8b80405040100405]))
|9=>(OfNat.ofNat (packedNat [0x401c8ebf010300a,0x5467808180708b38,0x4050f81c7a02040,0x1c00cd4f0d010074,0x280818052a330040,0xc02b2c0e02590200,0xe00060200e413e00,0x8180803b28040c02,0x81d9202060800ac5,0x10300a0d6400810,0x740d310040c26814,0x1002060140207010,0x305448038cc04340,0x401c040c0f81c5e0,0x21ab1c1007010300,0xa0863008180503b1,0x4960c0287c0e2e06,0x785a1d010141004]))
|10=>(OfNat.ofNat (packedNat [0x3a2c040c02821ae,0xa1010300a0803aa0,0x40c130200e79010,0x300a0803b58ae020,0x6014a807010300a0,0xd03808181e0401d6,0x2020701410071f1b,0x1640503a28180504,0x1c8e02060a81007,0x5f83010d5039e4ae,0x206014100701030,0xee340401c04351a0,0x1c980c6a01410070,0x10300ad303808680,0x86901c96340401c9,0x2021a0200e160103,0xad103808180568,0x1c5c020401c0005]))
|11=>(OfNat.ofNat (packedNat [0x401c040c0282c0e,0x740601410e201030,0xa087001c0a08038,0xc8920206014bc080,0x380818050401dbc0,0x21183c1007248081,0x80503b74044e0282,0xe492b831640504,0x1c04050401c7a3e,0x1030b2052a01db8,0xc028200e7901015,0xb60803924ae02118,0x141007010303c270,0x401c04da028200e4,0x9011380a0803b640,0x40c0401d06b1362c,0x80a340401c040c2c,0x8141007010300a08]))
|12=>(OfNat.ofNat (packedNat [0x10300a07451e418,0x340401cfa7901030,0xa0778229de0c328,0x200e11010300a080,0x3bb8040c02820f40,0x7013b018050401c0,0x40c028200eeb0113,0x86808039e404e902,0x8200e49010300a08,0x7401c880206014a8,0xe70108c0a0803868,0x40c138200e83010,0x3094052a00818080,0x3b98f20c03a28fa7,0x9010301007349240,0x40c078205a070103,0xa0b03874040c02,0x821ca0701031c805]))
|13=>(OfNat.ofNat (packedNat [0x130200e7c0103068,0x8039e4040c02820,0xeb40101468f4040,0x1d3c0c028200ee30,0x10300af303a2804d,0x8028200e10010300,0xa0b0396c04590282,0xe49010d5643404,0x1c04b20401d065b,0x10300e74451e404,0xc0f014160701030,0x102d039a4040c028,0x200ef2011640a080,0x3b64040c029500ee,0x70108c0a0803bac0,0x40c02bc40e8a0103,0xa0803b9c0a0803,0x91c920202b6c1007]))
|14=>(OfNat.ofNat (packedNat [0x380810074196cf2,0x20401c000206014,0x16073780818fa028,0x200e020601410077,0xc8081e0803924040,0xc7c0141007010301,0xa0108c0a540392,0x40a080391cfc0206,0x140e8a013d80a34,0x401c0423028200e,0x490103068087881c,0x40c1a1500e79010,0x300a0b03a0c04050,0x78200e4901014685,0x47a01c040c043d40,0xe79010301e08038f,0xc040c029ec100701,0xd418050f81c040c]))
|15=>(OfNat.ofNat (packedNat [0x3b01cf202060143e,0x7248300a0803a58,0x9202060141007808,0xb804351a0200e7e0,0x10306808038b8040,0x803a0cb602060141,0x7800081808039a,0x47e02060140e8a58,0x8080a0803845fe02,0x601410077f00818,0x5043f40e02062ac,0xa08038080a08039,0x707c73318300a080,0x38089c050401cb60,0x20601410077e0081,0x81e03a28f20202b6,0xc10072d808d60c0f,0x14100211814f608]))
|16=>(OfNat.ofNat (packedNat [0x10309e0503a2804,0x2b028200f0801030,0xa088381c040c830,0x200e790101410d70,0x892404b202820221,0x2b8080a080396c0,0x40c028200f05010d,0x1007249e4180504,0xb40e9d010309c05,0x3a29de020641010,0x7010300a2703a28,0x180803844fa79011,0xac1805041bc040c0,0x286c0e0206015b60,0x74500818074520cf,0x202060140e8a3e00,0x818058181d140206,0x140f02248081808]))
|17=>(OfNat.ofNat (packedNat [0x28200e020601410,0x7488080a0808840,0xf221010ac0a08038,0x818050401e24020,0x644410073c8b8460,0xc028b40e02060200,0xedf2d808180803c4,0xf2020643c1e0803,0x80818050401d7a02,0x601410078700818,0xbe028200e020609c,0x68080380818050f8,0x1ce802060800a080,0x10300b0d8601c042,0x306014ba08010300,0xa0803c2805090282,0xe79010780a0803,0x8688802060141061]))
|18=>(OfNat.ofNat (packedNat [0x10302a080380818,0xb20281e36028d014,0x100724808181e028,0x7c0e0206054ca080,0x3808181e608200e0,0x2064640a080380a3,0x1e028200e020601,0x410078b9f8180504,0xb40e02060145454,0x38b804050404420,0x4b0601410078b00a,0x2a0c028200e02060,0x5410073c80818052,0xa1840e02028200ee,0xb2d8080a65040442,0x20601454080380,0x818050401e280206,0x141061038081913]))
|19=>(OfNat.ofNat (packedNat [0x401cae0c028200e,0x49010300a0803c8c,0x40c59078101d010,0x300a078d9e4040c0,0x28224407010301e0,0x8038f804056d81d1,0x4020401ce85b2480,0xa420c028200e0206,0x15120803808184a,0x28d0a8020601410,0x79000818050401e,0x3e02060163c0803a,0x78880c028200e020,0x29500e5b24808180,0x51a02c0e02060140,0xeeb4500a3a050401,0xc9202028200e5b24,0x80818050401e382e]))
|20=>(OfNat.ofNat (packedNat [0x601468540107810,0x72d924042359014,0x106f010303c080e9,0xe404681a0200e790,0x10300a0803ca4040,0xc0f020e879010300,0xa0b03b10040c0282,0xea7362c80b0404,0x1c040c02820c328,0x362c80a0803c9c04,0xc1a01d147901032,0x4c050401c0434040,0x1cde79010300b250,0x401c5c0c028b40e7,0x40101410078a1240,0x40c0f0a810070101,0x4100730124043404,0x1d0679014901805]))
|21=>(OfNat.ofNat (packedNat [0x3a84040c5201410,0x7010309e05041d0,0x40c02cbc0e79010,0x325c050401c040c0,0x2cb41007011ac180,0x504310042302820d,0xe790103010613a1e,0x56e0c028200e794f,0x818052a01c042b,0x28200f2c010d010,0x700278040c02820,0xe2e010303c080e8,0x8680803a1404230,0x28213e07010300a0,0x895874040c029500,0xf2a0103010748431,0x40c02822567401,0x300a0803ca88802]))
|22=>(OfNat.ofNat (packedNat [0x601410623792c18,0x50401cf22e010ac,0xa08038085605328,0x200e020601410079,0xa8300a0803a747c0,0x21581410074c0081,0x8050401e68020282,0xf142d80818b204,0x1c5e02060140f33,0x3c8080a340401dd6,0x2064c80a0803808,0x19040401cf202060,0x14681b0380818050,0x44c53c0206014360,0x72583164050401c0,0x40c03845eeea4f03,0x164050401c040504,0x1e6049011640a08]))
|23=>(OfNat.ofNat (packedNat [0x38b8040c0401c5e,0x20612810073c808,0x18050401d0c02060,0x5410072480818050,0x401e7a44064f00a0,0x80380818b202cec0,0xe021a8d010071f80,0x810071fa0cb62e25,0x8300a080395c0405,0x401c229e170300a,0x803808180504158,0xe02060200e2f3c8,0x818059d01cf2029,0xc8300a0745008180,0x50401e7002028202,0x2102480818089b81,0xce80211c2c0a0803,0x80818050401e6c02]))
|24=>(OfNat.ofNat (packedNat [0x3a2a8a4b060144e,0x80380818050401e,0x8802061dc0b0c038,0x81805043300e020,0x60141007a1808194,0x2028200e0206014a,0x941038080a0803ba,0xc220206054102d03,0x8081805a08200e02,0x28213e072d8086a,0xd8028200e0206014,0x3e07620080a08168,0x44207e0601410071,0xf00a80050401c920,0x2060141607640141,0x70c1257e029f83,0xa0803808b20504,0x1c22029f0300a08]))
|25=>(OfNat.ofNat (packedNat [0x10300a0803d30d8,0xef010d010074f008,0x180503a28040c1a0,0x200ea7010300a083,0xb9dde0c0401c820,0x2061fc10073c8081,0x8150401c7e025901,0x410071e808194b07,0x8200e02060169407,0x2480818050401e92,0xef010304e0803808,0xa08088fc2002029,0x500e112480819480,0x28200e02060168e0,0x73c8141062038609,0x2050401c30493e00,0x818050401e8c0202,0x8200e11248081805]))
|26=>(OfNat.ofNat (packedNat [0x2a01ea8021aa9068,0x80380818050401e,0xa80215814100724d,0x4c040c028200e020,0x60141007a9278043,0x51a0200e02060141,0x613a00a160c0281,0xd140206016a20745,0x818050401ea06c,0x10300a0b038b804,0x50401c7a4406014,0x1007193bc040c028,0x2c0e02060165e072,0x4808180803bb4f20,0x20653c100724808d,0x340401c040c0f02,0x5a1d010300a0803,0xd34050b028200e5b]))
|27=>(OfNat.ofNat (packedNat [0x2480818059d81c92,0x7e06014100771808,0x1959028200eef118,0x30ca080380818081,0x681c5e0206014100,0x7190084608038bc9,0x202060141007ac00,0x81805ab8200e4401,0x309405041101805,0x438888020601416,0x701031b00503a28,0x40caa8140e026c0,0x1410073780818050,0x43480e6c011380a0,0x8038081827044300,0xe026c01410074192,0xc18050401c920206,0x78101d1f8081805]))
|28=>(OfNat.ofNat (packedNat [0x10300a072601410,0x741860920c02820,0xe413c8780a08038,0x60920206014115b0,0x3808840c028200e0,0x2060200e3f178081,0x8050401dfe6c5901,0x4160701014109f03,0x844046b060141007,0x258300a08038fc46,0xc0281c7e3e4f030,0xa08038fc040c078,0x200e7d010300ac70,0x401c184e0401cfa7,0x91080818050401c0,0x4340401d8849361a,0xc0a08038080a0808,0x8407c02028200f5a]))
|29=>(OfNat.ofNat (packedNat [0x43cc0eef0103068,0x80380818050401e,0xc602065880a08038,0x8180503a2864020,0x60141007b0910fc0,0xc028200e0206078f,0xe0803bbc18270401,0xc040c10014100701,0x300b600401dde0c,0x328200e5b1301410,0x70c124040c02820,0xf5f778081826040,0x1c1808039f4f2e70,0x1030ee08039d0040,0xc0f0203a3e010300,0xb5e0401c04050401,0xc7a49ae808180504,0x1cd8021a0200e79]))
|30=>(OfNat.ofNat (packedNat [0x380818050581c04,0xc590140e8a01030,0xa0803b64920c028,0x200e66010300b680,0x38081859028200f6,0x7010300a080395c0,0x40c028200ea60103,0xa0803808180504,0x1ecc02061280a54,0x400818051a01c98,0x206016ca073c808,0x18052a01cf89e010,0x300a072600818050,0x401cf844010300a2,0x72a00818050f81cf,0x20c028200e963c80,0x81805b20200e021a,0x8d01007190081805]))
|31=>(OfNat.ofNat (packedNat [0x6014a8020601410,0x70e924042306014,0x10071f8086a0c028,0x200e3f010300a540,0x3924040c0401cd20,0x2060146808039e40,0x40c028200e742480,0x818050401ed64901,0x300a0803844fa02,0x601410072480818,0x50401dce0202b6c,0x1007010300a07451,0xe4040c5901468080,0x380818050401dd60,0x20603c1007010300,0xa0803da8040c0282,0x2d207010300a0f04,0x1c042306014102d]))
|32=>(OfNat.ofNat (packedNat [0x10300a0803b1004,0xc028200f6f01030,0xa650401d8802060,0x1410074192404fb0,0x601410073a00818b,0x2028200e11010300,0xa080396c92020601,0x6dc07010300a0803,0xb10f20206016ca08,0x380ada0c028200e,0x2060780a0803924,0x40c0281ed802060,0x14a807010300a080,0x3b7c5c0206014680,0x80380846050401c9,0x202062c80a0803b1,0x40c029ec100701,0x306808039e48802]))
|33=>(OfNat.ofNat (packedNat [0x601410074180818,0x5150200e0206098,0xa0803924040c028,0x20c207010300a080,0x3980040c028200f5,0xc220300a08038600,0x40c028200e8a248b,0x8040c028200e1136,0x3bc040c028200e02,0x7d8303c050401c04,0xc02994100708808,0x180503dc8040c028,0x200e1d1f80818050,0x401ee20206014100,0x73a0fc040c028a81,0x7248081805b801,0xc040c02b04100701,0x300a08039bc922e]))
|34=>(OfNat.ofNat (packedNat [0x3808181e028200e,0x18010300a340401c,0x96020601410074f0,0x818050401c040cb,0xa0200e02062200a0,0x80380818050401c9,0x2a1010300a0803d1,0x4040c0401dcc0206,0x14109f038081805,0x401cf2c8012dc18,0x50401c040c028d0,0xa8080380818052a2,0x240e020601512080,0x3808460c028200e3,0xe0108c18050401de,0xe02b98300a080380,0x80a080396c920206,0x1410071f96c04fb]))
|35=>(OfNat.ofNat (packedNat [0x401c040c028200e,0x3f6200818d802820,0xe6c010300a08039,0xe5de020601410073,0xc80818050401c224,0x9010300a0803d380,0x40c028d010071f80,0x818050401dae4901,0x42c18050401c040c,0x2d441007010d468,0x80380810074196c,0x40c02822ee073c8,0x9f60c028d010070,0x1032ec050401c040,0xc028200e830c0081,0x8a4028200e020601,0x4100762124040c02,0xdd40e02060146854]))
|36=>(OfNat.ofNat (packedNat [0x38081805045f40e,0x49010300a0803df0,0x40c520146808039,0x10040c0289c10070,0x601410070c124040,0xc0f0203a02060141,0x7bda78040c028d,0x1007010300a3403,0xa28040c02cbc1007,0x10300a078d80818,0x5044300e7901030,0xa340401c3002060,0x14100724de804050,0x401c224901032f20,0x50401c040c0281d1,0x418010302a080391,0x40c028200e7901,0x1410110800af005]))
|37=>(OfNat.ofNat (packedNat [0x28200eef0601410,0x73c80818050401d,0xfe02060141007330,0x8d60c028200e020,0x6014100775124040,0xc028200e793e1b01,0x8b2028200e440103,0xa0803b9c040c25,0x141007028200e18,0x2480818050401c93,0x80010303c05045dc,0xe02060200e2f060,0x1410e36412c18050,0x401dde0206014100,0x7010300a0803845e,0xe020601410071900,0x81805bf81c057e06,0x141007010300b2f]))
|38=>(OfNat.ofNat (packedNat [0x401dde02060d010,0x7010300a340401c,0x64020601410074e9,0x10180504558040c5,0x901410070e808180,0x50401c9279170084,0x60c028200e2e010d,0x418050401c042306,0x14ca08038081805,0x401dda021a8300a,0x8039e4040c028d0,0x1007718081805040,0x1cf381010300a077,0x1a280423062c80a0,0x8038086a0c590141,0x777830ca080380,0x81805043840e4401,0x300a5403910040c]))
|39=>(OfNat.ofNat (packedNat [0x401c040c028200e,0x49010300a540401c,0x423060141007010,0xd418050401c040c0,0x28200e85010300a0,0x803e08040c028200,0xe7c010300b030401,0xc5c020601410072d,0x910040c028d01007,0x22008180503a2804,0xc0f01410073c808,0x1805041880e49010,0x300a546400818b20,0x28200e8317008180,0x50401c3a02060141,0xf30380818053282,0xe1d01031640504,0x1cb602061280a34]))
|40=>(OfNat.ofNat (packedNat [0x10300a08038b8,0x40c028200e02062,0xc80a080380818050,0x401f0644010300a0,0x803bbc040c028200,0xe020601410077180,0x818050401eac0206,0x141007640081805,0x401d88020601410,0x77b80818051a020,0xe02060140e8a010,0x300a0803860040c0,0x28200e5b010300a0,0x8038fc04fb060141,0x7010300a080387,0x4040c029500e0206,0x1410073a0081805]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x498018c00660003
|3,0=>(OfNat.ofNat (packedNat [0x3110180,0x80bc405c202d1016,0x80ac40542029101,0x40809c404c202510,0x120808c404420211,0x100807c403c201d,0x100e0806c4034201,0x9100c0805c402c20,0x15100a0804c40242,0x1110080803c401c,0x200d10060802c401,0x4200910040801c40,0xc200510020800c4]))
|4,0=>(OfNat.ofNat (packedNat [0x100287ed43eca1f1,0x50f62879d43c4a1d,0xd50ec2874d439ca1,0xc950e2286fd4374a,0x1b550d8286ad434e,0x81a250cea8661432,0x6a18e50c4a861142,0xfea17a50baa85c14,0x2d6a16650b0a8571,0x42aea15250a6a852,0x14286a13e509ca84,0xd1425ea12a5092a8,0x4814236a1165088a,0x8431420ea102507e,0xa83e141e6a0ee507,0x4a839141c080db50,0x6ba0349419aa0c85]))
|4,1=>(OfNat.ofNat (packedNat [0x19fa8ce9466aa330,0x5195a8c994642a31,0xc518ba8c49461aa3,0x85181a8bf945f2a,0x2f45177a8ba945ca,0xa2e0516da8b5945a,0x2a2cc5163a8b0945,0x7aa2b85159a8ab94,0x552a2a4514fa8a69,0x452aa2905145a8a1,0x94502a27c513ba89,0xc944daa2685131a8,0x97944b2a2545127a,0x8929448aa240511d,0xa88dd0464a22d511,0x42888d443ca21951,0xa2883d4414a2055]))
|4,2=>(OfNat.ofNat (packedNat [0x23fa91e948eaa470,0x5235a919948c2a45,0xc522ba9149489aa4,0x485221a90f94872a,0x4345217a90a9484a,0xa420520da9059482,0x2a40c5203a900947,0xfaa3f851f9a8fb94,0x7d2a3e451efa8f69,0x47aaa3d051e5a8f1,0x94782a3bc51dba8e,0xc9475aa3a851d1a8,0xe794732a39451c7a,0x8e29470aa38051bd,0xa8dd946e2a36c51b,0x3a8d8946baa35851,0xa9a8d394692a3445]))
|4,3=>(OfNat.ofNat (packedNat [0xa52a524528fa9469,0x4a2aa5105285a941,0x94a02a4fc527ba93,0xc949daa4e85271a9,0x37949b2a4d45267a,0x9329498aa4c0525d,0xa92d94962a4ac525,0x3a9289493aa49852,0x49a92394912a4845]))
|5,0=>(OfNat.ofNat (packedNat [0x34e31a598d20c68a,0x6342a9a014cf4c67,0x46337319a18cc4c6,0x5c632b319418c94c,0x644631f318e18c64,0xc62c6313a98858c3,0x8a6166308318298c,0x8c5fe62fc317d10,0xbdcc5e952f1b1775,0x8baec5d252e63171,0x98b80c5ba62da316,0xb98b50c5a262ce31,0x6598b20c58a62c23,0x15f98af0c57262b6,0x315998ac0c55b52a,0xab153d8a94a54552,0x9fb14e94a68c52e6]))
|5,1=>(OfNat.ofNat (packedNat [0x40ab203d9012c803,0x63feb1fdd8fe2c7e,0xb63f2b1f7d8fb2c7,0xd363e6b1f1d8f82c,0x7bb63dab1ebd8f52,0xc7a363ceb1e5d8f2,0x2c78b63c2b1dfd8e,0xf2c77543b7b1da58,0xec6c75e53ac31d51,0xe9cc74a43a231cf,0x98e70c732639631c,0x998e40c71a638a31,0xc398e10c702637e3,0x1bd98de0c6ea6372,0x31b798db0c6d2636,0x631b198d80c6ba63,0x5a31ab98d50c6a26]))
|5,2=>(OfNat.ofNat (packedNat [0x4c9b2635930ec981,0x64bdb25d592dec96,0x964b1b257592aec9,0x5164a5b2515927ec,0x9396499b24b5924e,0xc921648db2455921,0xec9096481b23f591,0xeec8f16475b23959,0x1bec8d96469b2335,0x918ec8c1645db22d,0x5915ec8a964522a2,0x799130c892644632,0x2199100c87a643a3,0x21b990d0c862642e,0x3215990a0c84a642,0x2320f99070c83264,0x16320999042a81b6]))
|5,3=>(OfNat.ofNat (packedNat [0x58832c299608cafe,0x657c32bc995d8cae,0x6657032b6995a8ca,0xce656432b099578c,0xab75558b2aad954c,0xaaa0654d32a51951,0xcca886541329f194,0xecca706535329919,0x4bcca58652932931,0x948cca40651d328d,0x1945cca286511328,0x71942cca10650532,0x81193fcc9f864f93,0x27b193ccc9e064ed,0x32755539ec9c964e,0x1b26f5936ec9b164,0xd5b2695933ec9996]))
|5,4=>(OfNat.ofNat (packedNat [0x647b32259906cc7d,0x663bb31c598d6cc6,0x5662fb316598a6cc,0x4d6623b31059876c,0xc356617b30a59846,0xcc1d660bb3045981,0x6cc0565ffb2fe597,0xe6cbed65f3b2f859,0x7b6cbd565e7b2f25,0x9786cbbd65dbb2ec,0x59756cba565cfb2e,0x659726cb8d65c3b2,0xe0596f6cb7565b7b,0x2da596c6cb5d65ab,0xb2d459696cb45659,0xfb2ce59666cb2d65,0x93b2c895638cb166]))
|5,5=>(OfNat.ofNat (packedNat [0x705ab8159bfecdf9,0x66f9b37b59bcecde,0x166edb37559b9ecd,0xc966e1b36f95b70c,0xdb266d6ab69d9b42,0xcd9b66cab363d9b1,0x2cd8366beb35dd9a,0xe2cd6b66b2b357d9,0xab2cd5366a6b351d,0x9a82cd3b669ab34b,0xd9a52cd23668eb34,0x5d9a24ad0c668333,0x40199f4ccf466773,0x33a199c4ccdd566b,0xb33459996ccc5665,0xfb32e59966ccad66,0x53b32859936cc956]))
|5,6=>(OfNat.ofNat (packedNat [0x1e96cf,0x45679fb3ce59e66c,0xf2d6793b3c859e36,0xcf156787b3c259e0,0x6cefd677bb3bc59d,0xd6cee5676fb3b659,0xda6cece576433b09,0x9d78ceb6675833aa,0x99d48ce9e674c33a,0x499d18ce86674033,0x9ed5ceace6f6734b,0x398d9cbace576728,0xb39315c8cce40671,0xd338d19c5cce2867,0x11338719c2cce106]))
|6,0=>(OfNat.ofNat (packedNat [0x86e34359a19ef0c8,0x7860bc2e9e166f0a,0xe5853bc285a134f0,0x9378472c221a102f,0x7a783a341b5e0cc,0xf05f782c3c145e09,0x8b045781fb40e5a0,0x64f02d58142c089a,0x36f01568073c021,0xa004cffd57fb3bfb,0xddfd0efe267eeabf,0x59df9eefc877e0bb,0xeed9f6acfb057d53,0x3e8ddf3acf9857c9,0x33e319f0ccf7f77b,0xd2bdd19edaef6857,0xb1abd759eaecf516]))
|6,1=>(OfNat.ofNat (packedNat [0x935bc991e4bcd259,0x5929b4931e48cd24,0x691dac8d1e45af2,0x26791034869a428d,0x20f59043c80d63fc,0xb1f778f8b47a9e3c,0x6f1dc78eb3473de3,0x90f1c268de346dd6,0x364b1ab78d23c679,0xa32ef19168c53c61,0x562fed17878b9345,0xb1a2ccd16158adb4,0x551e29cd14958a1b,0x44f1e26cd12f7894,0xb448da238f115788,0x7b4425a204f0fb78,0x7ab43b9e1d0d0e26]))
|6,2=>(OfNat.ofNat (packedNat [0x4f81a7b4d3d,0x469e734f1de780f3,0xba69d9bceb1e74eb,0x3a079ccbce4da718,0xf38579bf3cde1a6e,0x2f36b69b32cd7de6,0xb0f35179a53cd0de,0x67ad3367997bcca1,0xe644d31b798a3cc3,0xd6612d303697eb4b,0xdda5e2d2eb6972b4,0xb79e5aef2d169653,0xcb11a57eb2b87958,0xbcab1654eb2a2594,0xe34a55e51ed28a59,0x42349fd64f0f2726]))
|7,0=>(OfNat.ofNat (packedNat [0xa36b51,0x9da8c2d45b6a2ab5,0x13da892d4436a1eb,0x50dda862d42c5a13,0x35081a834d4146a0,0x7350256806d3fe59,0xfc34fc9a7d8d3e66]))
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
|0=>(OfNat.ofNat (packedNat [0x281c22014010160,0x292522014010146c,0x1601016061e5010,0x1601015010140607,0x50281c0401f01014,0x1017010470601f0,0x10231a8d30601406,0x150292606023419,0x6d06017060160281,0xf0281e0100101016,0x10d303926010160,0x10314196d0601706,0x16060770281c010,0x1422014010230103,0x101020029504196d,0x601706016010141,0x181401016010141a,0x1d0401d01020029,0x260291f0281c0292,0x4010140601f01016]))
|1=>(OfNat.ofNat (packedNat [0x101601014060140,0x63dd060140101606,0x14010320281d060,0x140401d010230101,0x60281d060140401d,0x281e01016010160,0x10200392502b8f01,0x17010d306014040,0x1f0101701031013b,0x7173130281e0601c,0x1016063ab010161,0xa0ff060140102001,0x1d1a01d06014040,0x1d0601f0401f0101,0x6010200281c01015,0x71b210101f0101e0,0x2b84038fd0102306,0x140637f17077028,0x1c010d006014061e,0x7010160601706077]))
|2=>(OfNat.ofNat (packedNat [0x1017010140281d0,0x116d060160107502,0x81c0607501014250,0x210103d5201f0601,0x40281d0101622014,0x601f06014060160,0x281d8581f0281d22,0x16118140601d028,0x230116d060140102,0x281d7783022014,0x10330601c010140,0x10d106014010d006,0x140101601016060,0x1c06014060150116,0xd06017060161fb11,0x281e01014011282,0x58210281d4196d06,0x17060160601c010,0x157d8780281d0101,0x601032118140281d]))
|3=>(OfNat.ofNat (packedNat [0x101f77830010150,0x10d0060140601401,0x140602306014010,0x1d0601f010140281,0xc0281d063df0281e,0x101401016060170,0x10d1060141a8d306,0x150601406014028,0x1d0281c0601c0282,0x30601f03bdd02823,0x60140281e010150,0x6017010140101401,0x168581d01023028,0x1f01016778330101,0x4060170101601014,0x60140401f041d20,0x281f1a01d0601404,0x1d01016010d1040,0x1f02b8f010160102,0x1010140601d06075]))
|4=>(OfNat.ofNat (packedNat [0x601401016010310,0x601d010140392722,0x140601f01016060,0x1401017010160101,0xd06014028fd06016,0x60141a150060140,0x601f02b8f010201a,0x150060140601e010,0x15010200116d0601,0x6010160101e01015,0x292606014220140,0x1016010160101601,0x140601506014010,0x2306017060160107,0x50281c01021010d1,0x60140e8fd010230,0x281c010160602306,0x1d0102301016039,0x24010160601d0101,0x60281d0101406014]))
|5=>(OfNat.ofNat (packedNat [0x101606014060140,0x101703d71060146c,0x1d0102101014060,0x1f01023220140107,0x50281c010d106014,0x17014010210281d0,0x6014010160101401,0x160103101020010,0xd32255b0101c0101,0xd060140281c061e7,0x220140101d060170,0x10160281d0281c1a,0x1520601406015060,0x1406014010d10601,0xf01016060770281c,0x601401031010150,0x601c01016061e501,0x160102002d3b170,0x1f06016010230112,0xb0103106014010d1]))
|6=>(OfNat.ofNat (packedNat [0x6015010230401d0,0x1016060140101601,0x160281f01014220,0x160101d0401f0101,0x60601402b8f0101f,0x118140281d1701c0,0x1021010171181402,0x81d010200281d010,0x15010140401f0101,0x6010770281c0281e,0x220140101d013110,0x281e0116d0601601,0xd1858161a01d060,0x140281e010d2010d,0x1060140401d0101d,0x778200281c010d30,0x281f010d36081d01,0xd30101d0116d010,0x312201406014220d,0x61e5010330601f]))
|7=>(OfNat.ofNat (packedNat [0x601702821029270,0x1016039250101677,0x833010151a023060,0x140101d010170101,0x60281f0102101031,0x10150281d028210,0x281f0101c0102302,0x81c0601501023028,0x1f029270281e0101,0x7010160281e01021,0x118230281d0601e0,0x60170281f0282106,0x1f0101401016043,0x230101e0601e0281,0xe013130281e77823,0x101517017010210,0x60140601d0101602,0x81e01014063df060,0x14010160401d0101,0xd010160281d01023]))
|8=>(OfNat.ofNat (packedNat [0x1701401021010160,0x601f010161701f01,0x210601401016028,0xfd010230416d0601,0x6060150601406017,0x601601016060140,0x2821063dd0282301,0x171a02106014010,0x16043210101e0601,0x40401d0281d01017,0x296f06016010750,0x281c010d10601401,0x177783001015010,0x16041d20281f02d5,0xb0101c028ff01023,0x10160116f060160,0x6014029500401d02,0x9500281d0601d028,0x23010d4060150601,0x6010160601601023]))
|9=>(OfNat.ofNat (packedNat [0x401d0101d013210,0x101e010160101401,0x770281c01014010,0x1601016010140101,0xd1a01d0601401017,0x10160281d118170,0x281d0101f0101e01,0x750281c01017028,0x1f010d3060140101,0xc0108c0281d0281c,0x10167d81f028210,0x60140101d0101702,0x81d0281c011d0028,0x1f010d1060140601,0x40401f040750281c,0x40770281c010160,0x1017010160601f01,0x167d81402821040,0x1f01017060750101,0x60101d010230281e]))
|10=>(OfNat.ofNat (packedNat [0x101e0281e060140,0x1017060160282102,0x81c0281f01016028,0x1d06015010d60601,0x5038ff0102301016,0x10d006014060160,0x10210401f0101d06,0x1d0392501016040,0x1d0101e060170281,0xc0102103bdd02823,0x601c01014010141,0xa01d060140101506,0x14060140108e028,0x1d0101c0101d0281,0xc01014010160281d,0x102106015010210,0x281d01014061d002,0x81f0601401016040,0x1f0101f010140101,0x401031038fd01023]))
|11=>(OfNat.ofNat (packedNat [0x10140101,0xd010150101f0101c]))
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>(OfNat.ofNat (packedNat [0x344000000000000,0x0,0x0,0xb200000000,0xa10000000020,0x8071000000000000,0x0,0x0,0x0,0x610000000014400,0x0,0x41000,0xc400000840,0x80000000000]))
|4,1=>(OfNat.ofNat (packedNat [0x14100000000,0x0,0x0,0x0,0x4c412100,0x0,0x0,0x0,0x1110000000000,0x0,0x38c000]))
|4,2=>(OfNat.ofNat (packedNat [0x7c4,0x0,0x0,0x1d20000000000,0x1c1000000000000,0x0,0x64c000000000005,0xc800000000000000,0x0,0x0,0x1610544000000,0x0,0x0]))
|4,3=>(OfNat.ofNat (packedNat [0xa4c2810000,0x2710000243000000,0x0,0x222000,0x21100000,0x8040000000000]))
|5,0=>(OfNat.ofNat (packedNat [0x6a100000001a,0x4467219840001944,0x641000063118485f,0x200005d216c80001,0x684591158c551150,0x4531148450200000,0x4d3128c491,0x1204462000044210,0x884110fc83e10f44,0x3c100003b1000000,0xe843910,0xe040000dc4361000,0x3510d043220c082,0xf100002d200002c1]))
|5,1=>(OfNat.ofNat (packedNat [0x264898125,0xc400025840002508,0x93124488f2000000,0x238400000008d10,0x8c10000000000,0x22c400000008,0x83218884220c4803,0x1fc47e100,0x7c200007b11e48,0x1dc8752000074,0x1000000000007311,0xc8470200000001bc,0x40001b8400000006,0xd100006c11ac4000]))
|5,2=>(OfNat.ofNat (packedNat [0x3148c41000000030,0xc4c210000c113004,0xbf12f84bd10000bb,0x200000002e480002,0xe040000000000000,0xb710000b6100000,0x2d44b320000b21,0xb11000000000,0x2c04af12b84,0xad12b04ab10000aa,0x12a4400029c8a610,0xa51000,0xa4128880002844a,0x127c49d226c8000]))
|5,3=>(OfNat.ofNat (packedNat [0x3e04f710000f6100,0xf423cc4f213c44,0xef20000ee13b44eb,0x20000e8339c4e520,0x38c8000000,0xe030000df100000,0x0,0x3748dc136c400036,0x84d9135c80000000,0xd613544000350400,0x34c4d213444d010,0xcf10000ce1000,0x3308c9332040,0xc710000000]))
|5,4=>(OfNat.ofNat (packedNat [0x4d040004c,0xc53214c440004c05,0x2f14b492b24a8528,0x2000000049892514,0x8c922148091f1478,0x51d1000000047051,0xb146840000001191,0x458d142444c00043,0xc90c300010b10000,0x10a1420800,0x41c505200010414,0xc50210000000000,0x10110000ff20000f,0xd20000fb23e84f91]))
|5,5=>(OfNat.ofNat (packedNat [0x5a84000000169100,0x5a056715984,0x163,0x3000000058856110,0x160157895d1570,0x55a2560956255440,0x5505522,0x54,0x94f153494c10001,0x4b15249481518944,0x250c54124fc80004,0xf853d14f040004ec,0x40004e840004e440,0x4dc93610001351]))
|5,6=>(OfNat.ofNat (packedNat [0x6645981658800,0x654594164880006,0x4098f16384000634,0x58c162c400062858,0x9100018720001852,0x6105831000000000,0x182160458010000,0x5fc40005f857d,0x100000005f057a25,0xe0800000017715d4,0x97415c880005c080,0x5b880005b456b2]))
|6,0=>(OfNat.ofNat (packedNat [0x7d89f427cc5f127b,0xc9ed27b05eb17a49,0xe817989e517905e3,0x17885e027789dd17,0x705da27609d71754,0x9d4174c5d120001c,0xf20001cd27305ca2,0x7209c717149c3270,0x85c026f89bc20001,0xba20001b916e05b7,0x16d480006cc9b216,0xc09ae26b09ab16a4,0x9a726985a4268c5a,0x1268059e267099a2]))
|6,1=>(OfNat.ofNat (packedNat [0x97065b1968658295,0x8a542948a502938a,0x4d193064b1924a47,0x2914a44190880000,0x24028f880008f4,0x63b28e4a3818dc63,0x528cca3128bca2e1,0x8b0a2a28a4627289,0x86242888a202878a,0x1c2868a19185ca16,0x1850a122840a0f18,0x34a0c1828a091820,0x6062810a0228009f,0xe27f080007e89f82]))
|6,2=>(OfNat.ofNat (packedNat [0x2b32ac4ab01ab8a,0xac20002aa2aa46a7,0x2a94aa41a88aa02a,0x78a9d1a6ca992a60,0x6962a50a922a4468,0xf2a34a8b2a248000,0xa206871a14a841a0,0xc6821a00a7e29f0a,0x7b19e867829dc676,0x19d467419cc67129,0xc066f19b866c29a8,0xa68299c6661990a6,0x31984a60197c65d2]))
|7,0=>(OfNat.ofNat (packedNat [0x2,0xc410002c31b086c1,0x1b006bf1af84000a,0xf44000af06bb1000,0x2ba1ae44000ae040,0xadc4000ad86b51]))
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 14 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x620c017,0x82c0520a01382604,0x8088108200340640,0xc01602a050090100,0x1c03005009010018,0x280400600800800]))
|1=>(OfNat.ofNat (packedNat [0x1001fc3f,0x7c0f61dc3a8740e,0x419c310600ae1582,0xa8520a0138258470,0x8c11422043084104,0x2003d0780d019832]))
|2=>(OfNat.ofNat (packedNat [0x27e4f49e,0x1382644889011021,0xa420831012003fc7,0xd8d119e32c630bf1,0x702784c094122240,0x4688c11021842081]))
|3=>(OfNat.ofNat (packedNat [0x44a8850e,0xa194308550a21342,0x282d04a0840e8090,0xa0039e718df9bd3,0x78660c798e310600,0xbc15f29e538a6146]))
|4=>(OfNat.ofNat (packedNat [0x622c2582,0xb015febe577adf5b,0x2b0556aaa50e9f53,0xd2774ea9d137a6b4,0xce9952ca574a2925,0x222414808f518a2d]))
|5=>(OfNat.ofNat (packedNat [0x1a96e,0x7dccb7b662c7d8db,0x112d6483fb7f2f7d,0xedb7d6f2dbd97b2d]))
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>(OfNat.ofNat (packedNat [0x4,0x4000000,0x0,0x40200000000,0x3f0000,0x200140000,0x3f0000000100,0x200000000000000,0x25,0x200040706,0x0,0x0,0xc000014000000,0x4000000140000,0xc00020016000400]))
|4,1=>(OfNat.ofNat (packedNat [0x114,0x4000100000000,0x10000,0x7000002000400,0x0,0x700000000000000,0xd00000004,0x40400000000,0x100000001000000,0x0,0x229000000,0x4000000000000]))
|5,0=>(OfNat.ofNat (packedNat [0x502011a0c00,0x156010100002500,0x4000207000400,0x4600070501010160,0x625160001000c,0x16000e7404020007,0x66017400707000,0x3000029002b1100,0x25000020220c00,0x1040041012f3f1b,0x1040207630c1e02,0x20107070019051e,0x70010015470c0135,0x10c002900000700,0x277002000c010005,0x2501205b00220007]))
|5,1=>(OfNat.ofNat (packedNat [0x40c000700311411,0x41604290c170045,0x14010a0085000284,0x18000004000004,0x111533f5302740a,0x153000c070211,0x2270414001e0000,0x8361270000040000,0x2f27000002020007,0x702290100010000,0x1000a0000040053,0x6000409710070,0x13f000000060a,0x1e011f703f012517,0x853000000070711,0x72000c2904370100]))
|5,2=>(OfNat.ofNat (packedNat [0x200000020007040b,0xab00000006361400,0x1e70000c01702701,0x50170075300432a,0x14011e1514,0x3f02682b157b0611,0x107402307002700,0x14000c0034143f02,0x2700070c0100,0x7170172f2b7e0000,0x82b012815140c27,0x422502001e02,0x801050001260001,0x1400002579002750,0xa017007000053,0x411005800171402]))
|5,3=>(OfNat.ofNat (packedNat [0x67005001404,0x1000a0c0c004371,0x70048060055040e,0x1404000000110470,0x27001114000c,0x2717400005a0e16,0x10001040f007525]))
|6,0=>(OfNat.ofNat (packedNat [0x710a5b2d4cae6399,0x4e0167273d923e2e,0x3c2b3887824b1232,0x9077277d80455701,0x54a0567f278fa213,0xac52af5d24279439,0x7d386d738d8b159d,0x5e5d9f549743985e,0xb23d15725c760d31,0x877f7a492ca82786,0xa31c49933253330a,0x8d3e07828a827e65,0x37956b9027787c91,0x4d6a44150ea71d23,0x3e493b6e90a4a621,0x153b59518c3e3e6c]))
|6,1=>(OfNat.ofNat (packedNat [0x5e8896,0xaa9c063a0a308e11,0x8a993853b06ba9a5,0x36376a729e4a6f07,0x1040335353238890,0x3a129a519b1b665b,0xab1207e0162394f,0x8972af8fa88b7ea7]))
|7,0=>(OfNat.ofNat (packedNat [0x8124363a243a3a3a,0x2d95ad2c5f6977a1,0x4f8b4f64248b6357]))
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
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]]
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
end Case0
namespace Case1
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
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_7_16:=0xe8
def goal_11_16:=0xe08
def goal_13_16:=0x3220
def goal_14_16:=0x5440
def goal_15_16:=0xfee8
def goal_22_8:=0x540040
def goal_23_0:=0xe800e0
def goal_23_8:=0xfe00ea
def goal_25_2:=0x3020200
def goal_27_0:=0xe080a00
def goal_29_0:=0x32202220
def goal_29_2:=0x33323230
def goal_30_0:=0x54404040
def goal_31_0:=0xfee8eae0
def goal_63_0:=0xfee8eee8fee8eae0
namespace S_7_16
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_7.map (· &&& dom_7)
def goalM:Nat:=goal_7_16 &&& dom_7
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xd4bda944
|3,0=>0xd4bda944
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0ccaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 8 (i % 32) else 0
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
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_7 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_7 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)],[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)],[((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_7==dom_7) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_7 goalM v ys):RunD true dom_7 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_7 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_7 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_7 roots_7 goal_7_16 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_7_16
theorem lowS_7_16:Lower true dom_7 roots_7 goal_7_16 4:=S_7_16.noCircuit
def isoMv_13_16:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6)]
theorem lowS_13_16:Lower true dom_13 roots_13 goal_13_16 4:=lower_iso isoMv_13_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_16
def isoMv_14_16:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)]
theorem lowS_14_16:Lower true dom_14 roots_14 goal_14_16 4:=lower_iso isoMv_14_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_16
def isoMv_11_16:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]
theorem lowS_11_16:Lower true dom_11 roots_11 goal_11_16 4:=lower_iso isoMv_11_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_16
namespace S_15_16
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(2,3),(2,6),(2,10),(4,5),(4,6),(4,12),(8,9),(8,10),(8,12)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_15.map (· &&& dom_15)
def goalM:Nat:=goal_15_16 &&& dom_15
def NN:Nat → Nat
|3=>2
|4=>8
|5=>3
|6=>1
|_=>0
def HT:Nat → Nat → Nat
|3,0=>0x804d157017d4d0b
|4,0=>(OfNat.ofNat (packedNat [0x443fc56f3770bdeb,0x2f2504b62e12f427,0x2b8d2b7e262ad8c1,0x18ab9c7114e1c470]))
|5,0=>(OfNat.ofNat (packedNat [0x57e3d3b0,0x129291b907006be5]))
|6,0=>0x57e3d3b0
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0xffaafefe00fc,0xf000fa4444fafa,0xf0f000feccccff00,0xfff0ffccfcfcaaaa]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x47,0x504750e475041750,0x348504d7504750c4,0x150b4750a3415024,0x7094185075063210]))
|_=>0
def stOffB:Nat → Nat → Nat
|3,0=>0x22004
|4,0=>(OfNat.ofNat (packedNat [0x56a995,0xa9c52ea4946a885]))
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
|0=>(OfNat.ofNat (packedNat [0x40541707954794,0x1405c34550150501]))
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>2
|4,0=>0x9181007100524122
|5,0=>0xb1a1
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 10 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 15),wireSAt ((code >>> 6) &&& 15))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 8 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0xfd653210
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>3
|4,0=>0xa810cc
|5,0=>0x1bf
|6,0=>7
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 3 (j % 128);fld (pmPalB (k / 32)) 4 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_13,4,runOps true dom_13 (0,roots_13) ops)] else [])++(if pm.testBit 1 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 2 then [(dom_14,4,runOps true dom_14 (0,roots_14) ops)] else [])++(if pm.testBit 3 then [(dom_11,4,runOps true dom_11 (0,roots_11) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_15 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_13_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_7_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_14_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_11_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_13 4 s (0,roots_13) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_15 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_13_16 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)],[((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6)],[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)],[((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6)]]
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
theorem noCircuit:Lower true dom_15 roots_15 goal_15_16 7:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_15_16
theorem lowS_15_16:Lower true dom_15 roots_15 goal_15_16 7:=S_15_16.noCircuit
def isoMv_25_2:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6)]
theorem lowS_25_2:Lower true dom_25 roots_25 goal_25_2 4:=lower_iso isoMv_25_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_16
def isoMv_22_8:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)]
theorem lowS_22_8:Lower true dom_22 roots_22 goal_22_8 4:=lower_iso isoMv_22_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_16
def dzo_25_2:=0xc0c0c0c
def gzo_25_2_2:=0xc080800
theorem lowSh_25_2_2:Lower true dzo_25_2 roots_25 gzo_25_2_2 4:=lower_iso (d1:=dom_25) (roots1:=roots_25) (T1:=goal_25_2) [(dom_25,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_25_2
namespace S_27_0
def pairsG:List (Nat × Nat):=[(1,9),(3,11),(3,19),(8,9),(10,11),(10,26),(17,19),(17,25),(18,19),(18,26),(24,25),(24,26)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_27.map (· &&& dom_27)
def goalM:Nat:=goal_27_0 &&& dom_27
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
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_25_2_2 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_25_2 4 s (0,roots_25) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_27 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_25_2_2 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc])),14)],[((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)],[((OfNat.ofNat (packedNat [0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc])),14),((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)]]
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
theorem noCircuit:Lower true dom_27 roots_27 goal_27_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_27_0
theorem lowS_27_0:Lower true dom_27 roots_27 goal_27_0 5:=S_27_0.noCircuit
def isoMv_30_0:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)]
theorem lowS_30_0:Lower true dom_30 roots_30 goal_30_0 5:=lower_iso isoMv_30_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_0
theorem lowS_23_8:Lower true dom_23 roots_23 goal_23_8 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaa00aa,0,1)] (by decide +kernel) (by decide +kernel) lowS_22_8
def dzo_7_16:=0xff0000
def gzo_7_16_16:=0xe80000
theorem lowSh_7_16_16:Lower true dzo_7_16 roots_7 gzo_7_16_16 4:=lower_iso (d1:=dom_7) (roots1:=roots_7) (T1:=goal_7_16) [(dom_7,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_16
namespace S_23_0
def pairsG:List (Nat × Nat):=[(1,5),(2,6),(3,7),(3,19),(4,5),(4,6),(17,19),(17,21),(18,19),(18,22),(20,21),(20,22)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_23.map (· &&& dom_23)
def goalM:Nat:=goal_23_0 &&& dom_23
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
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_7_16_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_7_16 4 s (0,roots_7) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_23 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_7_16_16 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]]
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
theorem noCircuit:Lower true dom_23 roots_23 goal_23_0 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_23_0
theorem lowS_23_0:Lower true dom_23 roots_23 goal_23_0 5:=S_23_0.noCircuit
def isoMv_29_0:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)]
theorem lowS_29_0:Lower true dom_29 roots_29 goal_29_0 5:=lower_iso isoMv_29_0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_0
def isoMv_29_2:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
theorem lowS_29_2:Lower true dom_29 roots_29 goal_29_2 5:=lower_iso isoMv_29_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_8
def dzo_15_16:=0xffff0000
def gzo_15_16_16:=0xfee80000
theorem lowSh_15_16_16:Lower true dzo_15_16 roots_15 gzo_15_16_16 7:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_16) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_22_8:=0x55005500
def gzo_22_8_8:=0x54004000
theorem lowSh_22_8_8:Lower true dzo_22_8 roots_22 gzo_22_8_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_8) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_8
def dzo_23_8:=0xff00ff00
def gzo_23_8_8:=0xfe00ea00
theorem lowSh_23_8_8:Lower true dzo_23_8 roots_23 gzo_23_8_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_8) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_8
def dzo_14_16:=0x55550000
def gzo_14_16_16:=0x54400000
theorem lowSh_14_16_16:Lower true dzo_14_16 roots_14 gzo_14_16_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_16) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_16
def dzo_11_16:=0xf0f0000
def gzo_11_16_16:=0xe080000
theorem lowSh_11_16_16:Lower true dzo_11_16 roots_11 gzo_11_16_16 4:=lower_iso (d1:=dom_11) (roots1:=roots_11) (T1:=goal_11_16) [(dom_11,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_11_16
def dzo_13_16:=0x33330000
def gzo_13_16_16:=0x32200000
theorem lowSh_13_16_16:Lower true dzo_13_16 roots_13 gzo_13_16_16 4:=lower_iso (d1:=dom_13) (roots1:=roots_13) (T1:=goal_13_16) [(dom_13,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_13_16
def dzo_29_2:=0xcccccccc
def gzo_29_2_2:=0xccc8c8c0
theorem lowSh_29_2_2:Lower true dzo_29_2 roots_29 gzo_29_2_2 5:=lower_iso (d1:=dom_29) (roots1:=roots_29) (T1:=goal_29_2) [(dom_29,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_2
namespace S_31_0
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(2,6),(3,7),(3,11),(3,19),(4,5),(4,6),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(17,19),(17,21),(17,25),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_0 &&& dom_31
def NN:Nat → Nat
|2=>7
|3=>143
|4=>323
|5=>290
|6=>98
|7=>14
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>(OfNat.ofNat (packedNat [0xf56a1f9c,0xe388ee56d4b6d471,0x84cb36aa7bb05bcf,0x5e483e8534479cc6]))
|3,0=>(OfNat.ofNat (packedNat [0xa5998f8da1c58132,0x9e7ef27d9b3f860d,0x9a4922e09872b673,0x9596f062939e38a3,0x9340ae2d91a32906,0x9161d1649126ee9e,0x90b6a85c8e783023,0x8bd5b2f288b05ec2,0x86bf0a3f82b5db70,0x80a051da7ff6420b,0x7f62a33b7da75560,0x7d616691753c810f,0x72ac31ee7066f57d,0x7061bf8d6f252f4a,0x6dff893f6c2e6c05,0x6bc49044685f823d,0x681b91a064fcbe57,0x634471a962d9b6dd,0x61c330f560120a2f,0x6007a5455d123812,0x5cf465f25a375d15,0x58b575a75402a5e3,0x4e05812e4b3c7a80,0x4a97c9ac49ade01b,0x49754ed6488f9557,0x47c6fa8245a36502,0x459b002044f06bc0,0x4457721642e9811f,0x40c0e7c6409e5e51,0x3fbee53c3f5dcc41,0x3da1d1603d4d6848,0x3bb3f6be3a2501ca,0x3928768a3888b023,0x35959dcb34e923ed,0x34b24baa348ec628,0x318acd9130f98332,0x30b82b90307d48ca,0x2f0006652dd75f91,0x2c6d059e2c37be84,0x2c2731042a15072b,0x28ff4e1c27dcd346,0x26439fb2249dad0d,0x24812a852268120e,0x22624656213d51f7,0x202b40fc1e8c187f,0x1e36244b1c430be9,0x1c0955d01b8d6a36,0x1a858df71a8129dc,0x19dcd7c6193f1b50,0x1861eee916e05e55,0x1346ad641184cb1e,0x113cbe5310caba5a,0x106281700f68fd5b,0xf33933e0edce93d,0xea95a0e0ea2f841,0xdf089df0deba9d5,0xd0a76280bcfa876,0xae8822e0aa7b6b0,0x9cc5dd409baec86,0x9b6886b098a08c6,0x96f711c08bf7755,0x790868104e9f8c7,0x3f782650264d830,0x14ddb2e00f84ad7]))
|3,1=>(OfNat.ofNat (packedNat [0xe32cdce9,0xdacf3814d8e8cc01,0xcedd2ccdc94ca805,0xc4bc75adbe687f96,0xb8e8f837b7f35602,0xb767e31eb68b2110,0xb34bde55b0c90f16,0xb02600aca8d2361a]))
|4,0=>(OfNat.ofNat (packedNat [0x3cc2c6ae3c1a1023,0x3b4857d23ac3811c,0x3a74d3093a2f451f,0x38f076f337c31de5,0x379f53e6366e97ec,0x366e3bbf3662cb6a,0x36374edd362ce41d,0x35f20157359a4ad2,0x33954b5a3333839c,0x331f1062327b013f,0x3201a3d131a3e952,0x312b01e130b82b90,0x30b141222f9385a6,0x2e5608a12ceeddbf,0x2cbb30282bda19dd,0x2bcb972c2b255382,0x2b18ff9f2a4bb8ce,0x2a2a4ff1286e5510,0x273b64d42654e857,0x26439fb224a66696,0x23863d5722b1f175,0x2298ee6821885f9c,0x216ccf50216bd392,0x216a342f209a8325,0x2032a1b22016343e,0x1ffdd4321ef9d35d,0x1e46f3821de0f1b1,0x1d953a641d51fb05,0x1d1e44c11d172947,0x1c7237e61c0955d0,0x1bf0bf9c1bd0fa9f,0x1b92ecfe1b1d551e,0x1a7cc27c1a4d0c3d,0x19cde64018c706b0,0x18c2a6ed18b9ff74,0x185caaf5185a85d1,0x17e0bfc017d88cd6,0x1742191d17005845,0x16d9f663163ecc28,0x15feb1a915d5aaba,0x155902a11519cabf,0x151720b414f9da33,0x149ee5ce13e2484a,0x132d6ea812c7958e,0x11982b5b1192a17f,0xfc2207d0f6982fc,0xeb91e870deba9d5,0xde110280cb64ed9,0xc71fe630c39d32b,0xa673ee109d66ab6,0x9951314095a304e,0x94c7257091689d9,0x8d6b37608c6b48c,0x8b7e663085b8806,0x82bb2f907d288fa,0x7ad0a600795c018,0x7044c8606d5d980,0x6666ee20653e7fd,0x61ff50f03e18d2a,0x320060e030fac4c,0x30deb0602ff50a2,0x2f6c7fb02cf3191,0x2b55aa10220e3de,0x1f688510145409a]))
|4,1=>(OfNat.ofNat (packedNat [0x917f822e9126ee9e,0x903a00d88fab35c1,0x8f89dd9f8f5c7889,0x8c1bd8ee8be654fe,0x8bbcacfc8bb5058e,0x8b98de5989ff6c7f,0x894e4ee98769f47e,0x86e162cd86bf0a3f,0x86196e82860be0d4,0x8561086683cfcd0d,0x82ac1a80814c2fc7,0x7f6330067e30beb9,0x7d79bd277d538d00,0x7bf112d87bec798b,0x7baa0aa17b59080b,0x796e0e377964e210,0x78e8a7a878c00d1e,0x766690ac76579b01,0x7619871375d415aa,0x753bb4ad751fdd97,0x73c799e773496e18,0x70ea084870cbafe8,0x6faf16176f64164b,0x6f52ec756efe5e57,0x6e5009296e1db5af,0x6dd24e0f6d0ca7d5,0x6c37d5ca6a0ce040,0x69eea2bf685f823d,0x673f855566c71628,0x65d2413a64d44b53,0x63ce8b446378063a,0x6373dbe263305d9a,0x632c3f68631dab32,0x62420584619d8709,0x6164219060fb284b,0x60a6b92c5fe5253d,0x5e9974da5e0d1a5b,0x5d5fefa75cba3a1f,0x5bfcdd8c5b9591b1,0x5a6195785a5a1285,0x59ad790259819d79,0x5956c0d858da6ed4,0x58b575a75724440a,0x55661f4b54f85fc3,0x54b6ec1f54a079d7,0x543bd6f1533c64e2,0x52e3179452b9fb64,0x527f189e52702379,0x512bae185126b054,0x50adef194f37a896,0x4bf025444aff15cf,0x48233c2547d6c292,0x4779ad8245c78195,0x447230f543929f7e,0x4337887342f391e7,0x42cc454242cbe354,0x42994b4a4250a9cd,0x41f87bda412696ed,0x40bacd3b407e6999,0x40022f313f66498d,0x3f5dcc413ee19682,0x3ebda9fb3ea07320,0x3e9a767d3e92c991,0x3e54fa973da1d160]))
|4,2=>(OfNat.ofNat (packedNat [0xfc825878,0xf07dbd2eecc57779,0xe9bb6c98e37626bc,0xe2343d26e1de62c4,0xe16ba2f6dfcb4783,0xd63cccbed3f1aa0d,0xd0ad4622d06c3d4b,0xcd6716b4cc40ac2e,0xcb536bb3ca9a52b3,0xc90bb0b8c89f9ddd,0xc6526190c645282b,0xc48e7dbbc345186e,0xbe44c5e7bd4e65a8,0xbcd0ec8cbbf0c899,0xb8fb40e9b8e8f837,0xb7783ac7b76d4208,0xb5ff2787b53d33c5,0xb131663daf5dcf0f,0xae03d8e4ad9665ef,0xacf5443dabc7dc7a,0xa8537a75a8335278,0xa48506e9a3f1c699,0xa3aa24ada2e37950,0xa2bf42cba1878bf9,0xa15ed27a9fed8d6d,0x9e83582a9e80fae8,0x9c89c2f89c1767f3,0x9b5d5b159b278f8d,0x9a24896599e4a209,0x99954ffd999430e8,0x993f6c9797db5c14,0x96aed7e395c08da0,0x9596f062943559be,0x92077f2c91a32906]))
|5,0=>(OfNat.ofNat (packedNat [0x39b22fe639398c84,0x38e89bda38723ae9,0x383e6c7137cda7f2,0x37cc19e237b1fffe,0x3766fe2f36c9608a,0x36902140366b3531,0x362ce41d35674793,0x354cd92534c74b8d,0x3475e8c933af6019,0x32165b4731bea615,0x3123a89030c2fcda,0x300483d92fe4f52f,0x2f61f1a42eece433,0x2eae38322e176abf,0x2ccea50d2c7e603a,0x2c0031742bfa7ecb,0x2b373e1f2a419e87,0x2a37788329ef7f84,0x28cfa3f627a9ec9c,0x274dc3c325bfc918,0x25733f9825516548,0x24b4c4c823e995ff,0x235ed6af2301ae13,0x21f5fa8321f54f57,0x21df249121d08c11,0x2115b8de20f08970,0x20e5646a209a8325,0x202b96fd20084a33,0x1f44ae4a1ebffd38,0x1e213aae1dee9d27,0x1de044ca1d853eac,0x1d2275031c6866fd,0x1ba036781b67e75e,0x1b13165d1b026d38,0x1a80579d1a466b8b,0x1a147844192a467a,0x18e7cd6b18c50e08,0x18309fce179d9693,0x16f49d6615cb7182,0x153b5be5145cce64,0x145bc5c21442b6c8,0x1400b75b132bb3a1,0x12b1852b12a9b40c,0x11e4918611c48365,0x11a6453e117fcf9b,0x10d02a87106e9586,0xf38d8d30e00f47e,0xd80586f0d7cdf9a,0xd1f19440c679047,0xc3b303a0c0f8f3b,0xbf820c70b60ca54,0xb44793209a7d8f7,0x9951314097b6625,0x8d28bee0867c74e,0x84bb8820811cecc,0x63fd3120517f4bd,0x500130004f97849,0x4f6ee0904ab1e8a,0x47ceec40362d51d,0x3486bd801df929b,0x1d6939901c638ea,0x1a2813b015a5931,0x145c58200ec9e36,0x5ec423005db616]))
|5,1=>(OfNat.ofNat (packedNat [0xa0acd41c9fbe3e35,0x9ec076b19d69ed2d,0x9ad150299a626401,0x99c05aac997cc6bd,0x992ce95f949e29b2,0x9252a89a9161d164,0x912cbebe90e058e5,0x8fd3bdbe8faee0f8,0x8f94ea038f89dd9f,0x8f82ab368cf300d5,0x8ca00cef8c305f5e,0x8c2d47208b6bddb7,0x891e5fbc86981ddb,0x8663fd8885204129,0x84aaed5883ff3e6e,0x82d67b2f829619e2,0x8161553f8146b1a0,0x7f9118fa7f30454d,0x7e0bb8d27db5bc98,0x7d9c82a27d9ba3bd,0x7d48f2997d47ab10,0x7c41c29e7c1d87db,0x7aba04427a6c9f6d,0x790528a1780e9d69,0x7756736174656a02,0x7372e1937245e4ec,0x71ec41be716885b9,0x712a19407017e5a0,0x6efe5e576e859716,0x6de7fdbd6c37d5ca,0x6a0d877d69896e1d,0x680000fa673ec676,0x66e92cea66159e9f,0x65fb51eb656c93bf,0x647d74b362a2f7be,0x61aa2a0f609625d2,0x5ee7f2835ec37a3c,0x5ded15465d8f4780,0x5d5fefa75d2650f0,0x5d0e99285befb514,0x5adf94395ac3cbe4,0x59e746ca59cae207,0x58fa937858f594fe,0x57ed152f5761180d,0x56994abe56664a68,0x543ce6f753f96e32,0x531d5d7552ffc6a6,0x52fb5306527f189e,0x51c7b8e54fc66cee,0x4e7b23bc4dd7fad7,0x4c93baa04bd53073,0x4b86000b4aebb286,0x4a4f8d9648398ccd,0x46912e384540e442,0x4527f70d452392f2,0x441c6bcd4319edeb,0x425b66cf4244a0e2,0x421812d340f8329b,0x40bd4fd5408f8827,0x40724c4f403a2db1,0x4022f7793ebe0cb3,0x3e6b44163de06abd,0x3d67fb903c7656ab,0x3a3cbe7d39bdffda]))
|5,2=>(OfNat.ofNat (packedNat [0xfb7b197cfb31dbdc,0xedb5bf10ec927571,0xe3d4fe57e0e03407,0xe0a5703cda867c97,0xda53df35d44d2190,0xd13850cfd12301f6,0xd080abebccd14753,0xc4776bc7c1dbd677,0xc0fb848cbfd86441,0xbea80d63bcd8270a,0xb92322edb4817c00,0xb4020fa9b1a9a38d,0xb053508caf80554c,0xae6025cdae4efbf7,0xa85b8c2da6af972d,0xa4ce50bca3368cc4,0xa2a221aea2490823]))
|6,0=>(OfNat.ofNat (packedNat [0xe41b7179d97bde48,0xd33acc35cd1cb5cf,0xc80e0e6cc649b516,0xb31a485ab202e6e6,0xaf9d2dd0ace40d3f,0xaaecc24aa9843f57,0xa8603dd9a75eb3a0,0xa2b21493a1e13694,0xa0acd41c9cdfe11f,0x9cb8d41e9ca9d801,0x97b6543a93b7475f,0x91863ebb8f9570a7,0x8e8b1e028d0173dd,0x8a1b71f686981ddb,0x8692decc822b4861,0x8215fd6d7ead8547,0x7b352e8b7832dcd8,0x76cfbdb26fc3bdc4,0x6efe5e576ee82497,0x6a06179069e4a475,0x697590b364bb7ab0,0x63da27395f9423af,0x5f84236f5f4048c9,0x5ee0303f5c56672d,0x58be28e558b5d875,0x584d6a3b572d3d6a,0x56affefe52b9fb64,0x5220d4c651b67c36,0x5091f7dc50606b13,0x4b36dbf44a36fcc9,0x469194cd419387d3,0x3f4a3df73e7db4da,0x3c811b2837cc19e2,0x371cec7634b0cb8f,0x340a509433337731,0x315e8b5630723928,0x2f61f1a42c356191,0x2a99417f2a4cb913,0x241cb7b223c89a0a,0x220d77ad1fc3c26e,0x1edb55471eae7a98,0x16032cd5138b8c95,0x13195c25118433b6,0x117fcf9b0e61fd76,0xe5dbbed0de343b4,0xa93ed5809e2bbbd,0x90f691808211c86,0x72515d903c100f3,0x2d98d7300fe00e4]))
|7,0=>(OfNat.ofNat (packedNat [0x9dcd98c66ec079dc,0x579c512c34b0cb8f,0x315e8b562e079448,0x2c356191258c480e,0x21a8620b205f4d0c,0x202fbf56129dfe45,0x9e2bbbd090d6eb4]))
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0x2a2a2a2affffc0c0,0x44cc44ccc3c0c3c0,0xfc00fcffff2200,0xffaaffaafaf0faf0,0xddee0000cc88cc88,0x55ee55eefcfc0000,0xeaeaeaea0a0a0a0a,0xffffaa00eecceecc,0x15ea15eaff00ff30,0xaaaaaaaafca8fca8,0xeac0eac099669966,0xccccccccaa5555aa,0x96969696ff00ff00,0x5555aaaaf0f0f0f0,0x3333ccccffff0000,0x55aa55aa3c3c3c3c]))
|0,1=>(OfNat.ofNat (packedNat [0xf3f3000030303c3c,0x555500000000aaaa,0xff00cf003cff0000,0x55ffaa00ffaa0000,0xcf30cf300c0c0c0c,0x55aa0000fc3cfc3c,0x5d5d0000cccc0000,0xfff0fff0ffcccccc,0xfcfcf0f0ffeecccc,0xfcf8f0f0ff3cff3c,0x3c003c00fcfcfcfc,0xfcfcc0c0000055aa,0xf0e0f0e0c0c0c0c0,0x3fc03fcf0a0f0a0,0xccc8ccc8aa00aa00,0x8282828214141414]))
|0,2=>(OfNat.ofNat (packedNat [0xfafafafaaaa0aaa0,0xffff3c3c3c3c0000,0xffffff00ff000000,0xffffa0005656aaaa,0xfe00feffa8ff00,0xfefeaaaaffeac0c0,0xe0e0e0e033cc33cc,0xfcfc3f3f0000,0x3f003f00fcfc3c3c,0xf5aaf5aa50f050f0,0x55ff0000152a152a,0x56565656ffffa2a2,0xffaafaf0f0f0,0xc0e0c0e0c0c0fcfc,0x3c3cfcfc5faf0000,0xff00000000ff00]))
|0,3=>(OfNat.ofNat (packedNat [0xf3f30c0c30303030,0xeaeaaaaa3f3c3f3c,0xffff00a00000ddee,0xf0faf0fa55a055a0,0xffc0c0c0ffaaaa00,0xd0e0d0e7f7f0000,0x5af05af055545554,0x3e3c3e3cffaa55aa,0xffeeffc0ffc0,0xd0e0d0e0ffffaaaa,0xaaaa0000dfdf0000,0xff5500aa55005500,0xc300c300003c003c,0xeecccccc00ff00aa,0xff550000550055aa,0xff30ff303c0c3c0c]))
|0,4=>(OfNat.ofNat (packedNat [0xaa00000080808080,0xfcf0fcf0fa00fa00,0xf000f00ffa0ffa0,0xfefe0000d5ead5ea,0xcceccceccc4ccc4c,0xffffa050ffc0ff00,0xaaa8aaa8ffffc300,0x7f007f00cc44cc44,0x55225522ffee0000,0xcccceecc9a9a9a9a,0xff00aa00eccceccc,0xc3c3000000003c3c,0xfffaffaaaaaa,0xf0f00002a2aaaaa,0x3366cccc55fa55fa,0x88cc88cc11aa11aa]))
|0,5=>(OfNat.ofNat (packedNat [0x3e3e3e3ebabababa,0x2020202000550000,0xfffff0f0f0f00000,0xaa00aaeeaaeeaa,0xa2a2a2a2fefa0000,0xfe00fe00afaaafaa,0xa0aaaaaffccffcc,0xcc00cc00fefefefe,0xa8a8a8a8ffeaffea,0xea00ea00ffaaa0a0,0xffaa3322cf00cf00,0x4400445f005f00,0xaa3f0c0000,0x3300330000cc00cc,0x33223322faaaaaaa,0xf4f4f4f4c8c8c8c8]))
|0,6=>(OfNat.ofNat (packedNat [0x50005000eeee0000,0xf000f0005f0a0000,0xeeeeeeee0000aa00,0x9999000066666666,0xcccceeee0a000a00,0x55505550fffffcfc,0xf5f0f5f0303c303c,0xfff0f0f011001100,0x333300000000cccc,0x50a050a0c0c00000,0x3070f0f0ffff55aa,0xececececccc8c0c0,0xffa0ff00aaeeaaee,0xc0c03f2a0000,0xffaaffeecfcc0f00,0xee00eef4fc0000]))
|0,7=>(OfNat.ofNat (packedNat [0xc000c0a000a000,0x5700ff00ba30ba30,0x332200000044cccc,0x8888888840404040,0xdd880000ff20ff20,0x3f3b0000ff000f00,0xf0a00000050f0f0,0x3f2a3f2aaa55aa00,0xfefc0000fffcff00,0xfc000000cececece,0x6666000000500050,0x302ffaa32303230,0xff5f000055885588,0x5454545444444444,0x2222222244004400,0x4cc04ccfceccccc]))
|0,8=>(OfNat.ofNat (packedNat [0xffff3030aa00ffaa,0xfefcaa00af00af00,0x3332333205fa05fa,0xf0f0ffaaff00,0x153f000033333030,0x32323232cceeccee,0xcfcf000000003030,0xfe00aaffbb0000,0x4444cccc22002200,0x88008800fffcfffc,0xffff00aa00aa0000,0xa0f0a0f005000500,0xfeaa0000a0a0a0a0,0xaa55aafffaf0f0,0xf0a00000cccc4444,0x2200aa00ffff0044]))
|0,9=>(OfNat.ofNat (packedNat [0x4040404fefafefa,0x3300ff0054540000,0x3f0000eaea0000,0xf000f0fcf8fcf8,0xea00ea000c000c,0x44aa44aa373f0000,0xff50fff0f5faf5fa,0xfca80000050f0000,0xddccddcc050a050a,0xfefc000a000a,0xc0c44cccccc,0xfc00fc0030003000,0xccc0ccc0c0f0c0f0,0xffffa0f0fcfc00f0,0xfcfe000050505050,0x1500150000300030]))
|0,10=>(OfNat.ofNat (packedNat [0xff3030300300ff00,0x3f000000ff00f000,0xfa50fa5045004500,0xf0ff000044ee44ee,0xffff550015150000,0xffccff0000fc0000,0x55000000ffffcccc,0xff444444afaa0000,0x220022c0eac0ea,0x8a008a00c0c8c0c8,0xb8b8b8b8bfaabfaa,0xfa00000000f0f0f0,0x54fc54fc0f0a0f0a,0xee44ee445a5a5a5a,0xfff0000003000300,0x30300000f3f3f0f0]))
|0,11=>(OfNat.ofNat (packedNat [0xf8f8f8f8ffcc0000,0x5f5f000032fa32fa,0xeeeeaaaa37370000,0x40c040c54005400,0xc000c00aeaeaeae,0xf0aaf0aa3a3a3a3a,0xffaa00aa4f444f44,0xfc54fc5403030000,0xc0c0000fcfefcfe,0x50f0000074747474,0xffffffaac0c4c0c4,0xcc88000080aa80aa,0xa8a80000f050f050,0xf4fcf4fc0b0b0000,0x202aaaa54505450,0x3330fff030ba30ba]))
|0,12=>(OfNat.ofNat (packedNat [0x1010101044440000,0x4c4c4c4cf0fcf0fc,0xbb00bb00ff0f0000]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0xc8a816380204002,0x21b8346c04048d4,0x5002030d02606068,0xcc0031180bc1a2e0,0x30b41a0216034560,0x6150a42604048045,0x21385844021303,0x44a020c888000212,0x8c440203084401e,0x30003e1e0304c00,0x11020043a020e034,0x361a0c86012040b8,0x240202020582a060,0xa04c241102040020,0x2020241e02070340,0x20602c04040501,0x1208010180e0602,0x8000801018080200]))
|1=>(OfNat.ofNat (packedNat [0x800498020208c02,0xd27800a2020693c,0xd2813c0002031,0x3826022682498180,0x492c020202024940,0x2030989248030340,0x190c02450180480,0x48e1e030a826110c,0x8603a02230240206,0xa1141a062203400,0x617850261e03034,0x860404908020d001,0x480061f8347c020,0xc02402061e800780,0x60a0003e060a04c0,0x21382402021d83,0x40038020043a0606,0x8e80019020247202]))
|2=>(OfNat.ofNat (packedNat [0x31c8000203034e2,0x7002024960404804,0xde6e1504ca2020c8,0x6020023682402040,0x812c026c031ac001,0x9020405006350340,0x4080048e690202,0x4d00233834cc110c,0x810ca0206800c863,0x2024c40230834c0,0x382f824bc5d03034,0xb85b2d0340059020,0x240204048046a020,0x2040020602024b00,0x2009303a0206800a,0xe562a8101254030a,0x81a060a14c241902,0x88061402034a402]))
|3=>(OfNat.ofNat (packedNat [0xc8611a380202402,0x2032306c0245834,0x606800a202030,0x3400060694000040,0x874500202228020,0x6448351002430601,0x2110202402040480,0x50e020993c00860c,0x250a02030010806,0x203506021202504,0x20220500063f834,0xfc1e030a8fa060a0,0x34f87b0202402040,0x4804f4023c824f05,0xb3b8a81a380c0241,0xa760202402380303,0x4000204804ea0606,0x9d000020c824e602]))
|4=>(OfNat.ofNat (packedNat [0x50034040404a7c02,0x190c024444b01018,0x1a9e000093a9c048,0x350c04049ad36020,0x30347a00010181a6,0xb0016cb42a130353,0x414020241a064c83,0x400020226012860c,0x2464020225c0209,0x258049809009308e,0x202258020204804,0x98950202402024a0,0x3400060a09926920,0x30340002009f86c0,0x2060984431030502,0x60206a4400060692,0xc000d27800b80202,0x2411e8e020240202]))
|5=>(OfNat.ofNat (packedNat [0x5a0101201140c470,0x906a6c700602025,0x66b20a011620d010,0x196026578095c045,0x68240c2a06800a20,0x2030a81a00030a81,0xa50002b00c040483,0x404ab02024443802,0x2a8120d010101201,0x548c4705f0483428,0x40483550020c810,0x4622010101201538,0x18080906a9804063,0x383400110c810124,0xb010643009008193,0x20450034280406a9,0x548020301026a31c,0x194404048080ca1]))
|6=>(OfNat.ofNat (packedNat [0x301012c60101854,0x1362808300404804,0xc04048358802618,0x1012222d01184090,0x6a18700404888700,0x4048358206600101,0xa1d1c01808092f00,0x80c2a06afc320404,0x8886a02032f97a36,0x10193aa0068080c,0xd5780004060693c,0x40488978475da,0xe812685c8080c185,0xc024040606adc000,0x65b010120d010181,0xa00330e00c2d0483,0x4048b069f86c025a,0x811400d010183009]))
|7=>(OfNat.ofNat (packedNat [0x303400026981012,0x13d81012685c808,0xc0d690d80406060,0x981a02030a84c721,0xc010120d4d809a29,0xc048343204080888,0xe0202205a0b9021a,0x19eb9670181a4b3f,0xd80406068017202,0x202402cd0101012,0x15e0780c2a66034,0xb6020303400311c0,0x10125e0106012010,0x10183009498e00c0,0x906b2d9402020240,0x2060a011920d1c01,0x808c8068080c2f50,0x3470c7020241a38]))
|8=>(OfNat.ofNat (packedNat [0x101012010c81012,0x2237a180c046f024,0x62386e8241a38020,0x24bc1e030a81a000,0x1060122200818080,0x906b70040d278006,0x23802025aa020c81,0x21d0101012016d,0x80c046cb607006,0x235c1a6c010181a,0xc810444b0e808,0x80900b587006020,0x25aa020204012010,0xc81012011a808320,0x4080043204110748,0xe38030a84c0d0f01,0x854130c810202225,0x8101222008a1a802]))
|9=>(OfNat.ofNat (packedNat [0x30340051010181a,0x50003b9da0404834,0x809008d40c14023,0xb01a0203011b0eb0,0x305008be06808080,0x900ba80c0404835d,0x2023701854130101,0x2001010181ae81b,0xe008091111dce04,0x49a17202308181a,0x101012e65c808,0x540404804040606b,0x94003803011c8e30,0x10101201710080c0,0x409b840c2606800a,0x23803380080d0134,0xc12df5c8080c2606,0x8000c26069400011]))
|10=>(OfNat.ofNat (packedNat [0x1100470060236df2,0x2030a84c0d030a8,0x4c0d280080c2a7c0,0x7c0c047b8241a027,0xb034fc3608808321,0x804818080906bd5e,0x814020241a060483,0x5e6f201018b40d00,0x80809113c40419,0x2025e0020202402,0xa3010e0080900808,0xf204048043204113,0x3d9c02030a826120,0x30a8280d00168300,0x906a1470060204c1,0x20677860120d010a,0x8262627a2c08de04,0x8340406150990802]))
|11=>(OfNat.ofNat (packedNat [0x2580808093441404,0x4048046c02030a8,0x8a0d01018541c068,0x858060680208068,0x18241a1e030981a0,0x30500813068443,0x204048880c140240,0x81a020c810130180,0x640809110080822,0x87404060c0255e,0x2030a826ff01018,0x54000f8640809112,0x1c0c141303424020,0xc86020020c86012f,0xe010643004080101,0x222008d428040483,0x5fa02033f01a3603,0x101afb7d0080810]))
|12=>(OfNat.ofNat (packedNat [0x101012785c808ee,0x6150351c1902024,0x440202258d0b91c0,0x11b6091101828260,0x68000c14024501a0,0x2030102609010643,0x101101a260d1b44,0x828040483623100c,0x81012220c8e00809,0x11018280406c3c04,0x4048061c380c024,0x1a02020261a01010,0x10122600c300c141,0x30350c060236c650,0xb02024d10a010261,0x3085c81a0e040483,0x470062f8260c0234,0x1f86cb9030a84c0d]))
|13=>(OfNat.ofNat (packedNat [0x303400400881012,0x1010184c000f808,0x80906c6804860c0,0x10120203034001f0,0x1064080b04808080,0x900c640406068005,0x6020306012e50103,0x81a7e1b008080931,0x2e40406448340118,0x2d010120d03034b8,0x7e1b008620606800,0xc0d3f0d910060c0,0x241a5103060120d2,0x8009282a130340c0,0x4048362e02030102,0x61601010d1165c8e,0x13804048340c1402,0x362a06150340088]))
|14=>(OfNat.ofNat (packedNat [0x348c0809068e00c,0x991048040404c85,0x7202030344200030,0xbd7409068080c3f0,0x680004aa068da400,0x21d834fc361c0101,0x201033000809068e,0x8090693c0c0d00,0x1463e02030340006,0x69400019020263c,0x2203050085306808,0x3209111300d1d020,0x241a3802026380d0,0x1019540d00008082,0x251aa40c0d199f86,0xc6e020241a4b0106,0x408228d818b40409,0x8c80419111f86c02]))
|15=>(OfNat.ofNat (packedNat [0x483658110c86012,0x2201010121600808,0xc0d004ac046106c,0xa06c02030a81a7c0,0x10181a002e050080,0x9342e404190208a5,0x4020303400880143,0x25226068080c0d00,0x4a00c99150981a06,0xa0124e0d010181a,0x4d818541313144,0x70040483550060a0,0x264c0d010181a005,0xe864122225930221,0x90c01012020317c1,0xa00010184c0d21c9,0x40809342e4320911,0x1308e0692010120d]))
|16=>(OfNat.ofNat (packedNat [0x3f4ac050c0303400,0x202026433701019,0x600d000080c0d004,0xd80404049a26a060,0xc0241b34012d4300,0x9068083218049300,0x40617c9c1a389981,0x120d01064542611,0x832186d8240532,0x202402020306026,0x9030a81a506281a,0x62040483432380c0,0x24445a0c0241b300,0x1010120191018542,0x606a20040497b897,0x20202024032e0101,0x81a0020818300906,0xcb40409009307004]))
|17=>(OfNat.ofNat (packedNat [0xc81012220e8080c,0x46c0080cb002280,0x1a060a010120d9e0,0xe00c040483536020,0xc81012226d0080c1,0x8048354a02030106,0x4be068080c0d3f0d,0x88006020241a509d,0x8080c049d0241a02,0x30a84c0d2880832,0x404889ac3803010,0x120d9c8080c2a130,0x34a0024301808db0,0x4808320408024440,0x2034e00809068080,0xc046da800c140236,0xc24020c89c122201,0x18547d130187e0d]))
|18=>(OfNat.ofNat (packedNat [0x2f82541060101012,0x1340080c0409824,0x1a020c8a80809110,0x18280413034048b0,0x236c120d8f8080c0,0xd3f0d804060204c1,0x33f01018be046da8,0xc046d8241a5001,0x1a7c04048342202,0xc81012220101808,0x10068f4047902024,0x1a683601808db190,0x340431020241b3d0,0xc818080906940040,0x6150340002031685,0x426068c40c040483,0x4a002032a81a7e1b,0xe00c04048344402]))
|19=>(OfNat.ofNat (packedNat [0x1107404191c01012,0x2201018be0d3f0d8,0x404049a10ab90c8,0x1808090692c04061,0x50101a1d01010122,0x6342e57743030101,0x20d010183009068d,0x80406150981b4203,0x50080906c640406,0x204d5a090305008,0x906d04041902024,0x44ea010187e0d3f0,0xd80406a0034fc020,0xc810202201010126,0x81b2e40c04190347,0xae4010640809113f,0x80406022f81acf1c,0x18080906b900406]))
|20=>(OfNat.ofNat (packedNat [0x204c640d0101a92,0x4048340c0404834,0x96a40101808131b0,0x808093437d72020,0x4835374801018080,0x906d1d76020c8101,0x2220127008095883,0x404190202445461c,0x10120d4d8080c0d,0x3f26c6c020c81154,0x9068080c1804835,0xa02030101609068,0x80c04a28241a020,0x30601226068080c0,0xd3f2f46c0202024d,0xb9960080c09a200,0x832040488946060a,0x117409068083204]))
|21=>(OfNat.ofNat (packedNat [0x25c880406020241b,0x4d01018b41804834,0x406020241b08010,0x101281342e404060,0x2026980d01018be0,0x9834fc0406150114,0xd03010640d1e9f,0xa303803010120d03,0x17c0809069407006,0x20241a7e01018be,0x9a20e00c046e824,0x1a0203012960d720,0x80809a50349e062,0xd011b6320680a520,0x4048357202031680,0x813048080c046c39,0x16406020241a5001,0x181a7e940d80406]))
|22=>(OfNat.ofNat (packedNat [0x3050080d720095c,0x60204c135201010,0x12685c8080c0d3f0,0xd882020c81012221,0xb0e00c0404834240,0x20c810120d4d8080,0x8ba049a17202a881,0x80809068080c0404,0xd401b4303010120d,0x428080809342e69e,0x2030981a00820e0,0xc04048340406020,0x269c0d03011bc090,0x69000c0404834445,0x101012685cc640,0x4060204c1acf0101,0x81a7e1b4ac0c0404,0x834a09b03010120d]))
|23=>(OfNat.ofNat (packedNat [0x68080c0404836b0,0x2030a84c0d0f808,0xc2a098981a02030,0x1026099b8640c140,0x20241a3803010120,0xd340c40c14020241,0xb570101012685c80,0x80c0404836ac0602,0x241a50ab0083204,0x488a1c02aa81012,0xd4d818280404836,0xa80203011400d528,0x83204048890a060,0x20241a4b9c808320,0x40488a1a020c8101,0x226110080c185d02,0x41a0202024d1535c,0x8080c0404889ca02]))
|24=>(OfNat.ofNat (packedNat [0x680862060204c12,0x20c81012228c818,0x2804048c81a06020,0x241a50ae808635c0,0x20241a0203011400,0xd1b1680809190353,0x60203011400d9f80,0x80c0d3f0d8240615,0x981a51030a84c0d,0x280080c0409ce812,0x20356c080906808,0x80900ae40406020,0x241b5a0356408090,0x68f40c14020241aa,0x4011683009068080,0x8090693d72020302,0x41b461b0080c2a13,0x3480060a011b609]))
|25=>(OfNat.ofNat (packedNat [0x3050080906ce404,0x6020241b6403050,0x80906d8c0406060,0x10120d03050be040,0x4834040404834020,0x20236c12685c8080,0xc0404836c4020301,0x120db08b8700602,0x241ab2030500809,0x68080c0d3f0da6c,0x203010120db0044,0x32040488aa4020c8,0x1012220157c0c040,0x48340419022e8122,0x203050080906c180,0xc14020241b5e0305,0x8db06808320602,0x4c12022d2700809]))
|26=>(OfNat.ofNat (packedNat [0x2026d20d0106430,0x40483404062f810,0x260901018bea1048,0x3404060c0241b220,0x1010120db413c040,0x48a024d0b90118c0,0x809342e40c140202,0x41b6701010123234,0x2e4c60602024640d,0x31680832069f870,0x602025620d01012,0xcc09342e40406020,0x4c12f90101808130,0x48180809069a0a00,0x60a010120d110647,0x4048880406b281,0x120d010181a003f,0xd80c0404834967e]))
|27=>(OfNat.ofNat (packedNat [0x48340419020242c,0x22010c5380404834,0x406b7010120d010,0x18300906a6d0c380,0x3010120d01019380,0x40483404060c0241,0xacf03010120d25db,0x40404049a210b901,0x125e09342e40406,0x20241b6c0106408,0x24048880d5902024,0x1a8501018081304a,0x6c04190c0241a380,0x3010120d5c8080c0,0x906802d6020c8101,0x2220101854045f03,0x4040602026d40d01,0x185426069047006]))
|28=>(OfNat.ofNat (packedNat [0x580a84c0d0101854,0x13130080c0404836,0xe402031e40809068,0x80d71020241a020,0x30a84c0db8018280,0x4048342438020241,0xab9010181a7e1b2e,0x404d103010120d01,0x185426660340c14,0x20241b6f010181a,0x7e1b448700602024,0x1a36010181a00030,0x50080906b3804060,0x204c13560305008d,0xd04834040606adcf,0xc360101808136780,0x8320911132860602,0x24640d010193a5f]))
|29=>(OfNat.ofNat (packedNat [0x1018097b04ae404,0x1902024447e030a8,0x2804048340406020,0x241b7a0101808130,0x68d80406022801ac,0xf01018300906de40,0x406020241b780101,0x81a7e1b5dc0406bb,0x34fc36010101268,0x5cc28049c020241a,0x9b010185e0406b90,0x4060c0241a7e010,0x1809750483404060,0x20241b7401018542,0x6068000406150122,0x80d360080c0d3f0d,0x805732d010120d01,0x4300c2a130340406]))
|30=>(OfNat.ofNat (packedNat [0x68080c0404834d0,0x3601018b40404834,0xfc0203034fc36010,0x18080d3f0d804190,0x3010120d01018082,0x4048340431030101,0x23206818080906df,0x4045a020241a9b01,0x1808db048348002,0x308180809069f804,0x406948040602024,0x1b7c01018081304a,0xc4042a02024d0b90,0x3050080906a94040,0x65f034fc36010183,0x9c0483404060203,0x62b3f03564080919,0x34057303010120d]))
|31=>(OfNat.ofNat (packedNat [0x1018080906a9572,0x203010120d11008,0xd7f020241b7e030,0x10120d0101808090,0x6a6c040602024640,0xd4d8080c04048361,0x20317c08090680,0x80c0404af81a7e01,0x180809588357202,0x3010120d0d8080c,0x2a020241ab90118c,0xc04048340406023,0x6c640d03010120d2,0x80080c0404889720,0x2030241a4c010180,0x80913034d0020301,0x1216068080c0404,0x8343e02030102609]))
|32=>(OfNat.ofNat (packedNat [0x30101ae4678080c,0x45c0241a0203010,0x12685c8080c04048,0x35f27e0305008090,0x68080c0404ad01a0,0x2030101232069f80,0x406150981a020301,0x15409069f8040602,0x241a855c8080c04,0x4835c89b0101808,0x913035720203010,0x120d1b2e40406020,0x27020d7200b00060,0x20241a0218818080,0x9069f80543030101,0x20d01018be040483,0x536020317c080906,0xc200419020241a9b]))
|33=>(OfNat.ofNat (packedNat [0x20241b840101ab2,0x40483404064e010,0x120d01018080dc18,0x80c0404834fc410,0x10640c2a020241a0,0x203011b609068f40,0x46e020241a020301,0x1acf3f0080c0404,0x835c87e0101b0404,0x483404060204c12,0x203011740906ae4,0x406020c81a7e010,0x180809069f936020,0x301012b406a6c040,0x62f810120d3f0080,0xc040483614023701,0x808090680862dd04,0x834040906a6e7202]))
|34=>(OfNat.ofNat (packedNat [0x68080c099104804,0x6020241b8501064,0x80906ae40406020,0x241a3d720080c2a0,0x20241a2201018be0,0x404ac41a020c8180,0x809068d804060259,0x8120d5c8080c0404,0x8368c0203010120d,0x1ea6c0406020343a,0x2031e4080906808,0xc0404c701a02030,0x10120d3f04804040,0x4834d09bc0018080,0x9068080c5f4e0101,0x20d5d80862060202,0x41a020317c130601,0x180809068740406]))
|35=>(OfNat.ofNat (packedNat [0x203010,0x120d010180809588,0x340406020241a680,0x10180809069f8040,0x6020241a22010180,0x80906a6c04060202,0x41b3901018be0404,0x83404b203010120d,0x1018080906c1804,0x6020241b2201018,0x80906be40406020,0x241aa4010640c040,0x4834043103010120,0xd010180809069f97,0x2020301012260688,0x804b2022c41a0202,0x354aa4012680809]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>(OfNat.ofNat (packedNat [0x48c01e600c30,0x498018c00660003]))
|3,0=>(OfNat.ofNat (packedNat [0x88a043502128105,0x4080a03f501f280f,0x54078a03b501d280,0xe54070a037501b28,0xd54068a03350192,0x80c54060a02f5017,0x280b54058a02b501,0x5280a54050a02750,0x13280954048a0235,0x11280854040a01f,0x500f280754038a01,0xb500d280654030a0,0x17500b280554028a,0x135009280454020,0xa00f500728035401,0x8a00b50052802540,0x10a0075003280154]))
|3,1=>(OfNat.ofNat (packedNat [0x108a083504128205,0x4100a07f503f281f,0x540f8a07b503d281,0xe540f0a077503b28,0x1d540e8a07350392,0x81c540e0a06f5037,0x281b540d8a06b503,0x5281a540d0a06750,0x332819540c8a0635,0x312818540c0a05f,0x502f2817540b8a05,0xb502d2816540b0a0,0x57502b2815540a8a,0x5350292814540a0,0xa04f502728135409,0x8a04b50252812540,0x90a0475023281154]))
|3,2=>(OfNat.ofNat (packedNat [0x935049282454120,0xa08f504728235411,0x8a08b50452822541,0x10a0875043282154]))
|4,0=>(OfNat.ofNat (packedNat [0x1c5a8e194702a37c,0x51bba8dc946daa36,0x851b1a8d7946b2a3,0x5451a7a8d29468aa,0x340519da8cd94662,0xa32c5193a8c89463,0xaa3185189a8c3946,0x12a304517fa8bed0,0x5eca2f1517628b9d,0x45c4a2dd516c28b4,0xd459ca2c9516228a,0xfd4574a2b5515828,0xaad454ca2a1514e2,0x8a5d4524a28d5144,0x28a0d44fca279513,0xa289bd44d4a26551,0x302896d44aca2515]))
|4,1=>(OfNat.ofNat (packedNat [0x263a9309497aa4b8,0x5259a92b94952a4a,0x4524fa9269492aa4,0x905245a92194902a,0x47c523ba91c948da,0xa46942322917d48b,0x4a4564228a913148,0x8ea442521ea90e14,0x866a42e5214a9091,0x483ea41a520aa904,0x148188407520128f,0xf547f0a3f351f728,0xfa547c8a3df51ed2,0x8f5547a0a3cb51e3,0x28f054778a3b751d,0x928eb54750a3a441,0xcfa8e69472aa3905]))
|4,2=>(OfNat.ofNat (packedNat [0x302297fd4bf4a5f5,0x52f8297ad4bcca5e,0x152ee2975d4ba4a5,0xcd52e42970d4b7ca,0x5b952da296bd4b54,0xa5a552d0a16714b2,0xea59252c6a96214b,0x6a57e52bca95d14,0xadea56a52b2a9581,0x4ab6a55652a8a953,0x14a8ea542529ea94,0xe14a66a52e5294a9,0x4914a3ea51a528aa,0x94414a16a5065280,0xa93f149eea4f2527,0x7213a549c8a4df52,0x6d2935549a0a4cc4]))
|4,3=>(OfNat.ofNat (packedNat [0x3a0a9cf50e70a733,0x539729ca54e48a71,0xf538d29c554e20a7,0xb538329c054df8a,0x6f84379a9bb94dd2,0xa6e4536fa9b694da,0xaa6d05365a9b194d,0x82a6bc535ba9ac94,0xd5aa6a85351a9a79,0x4d32a6945347a9a2,0x94d0aa680533da99,0xd94ce2a66c5333a9,0x9894cbaa6585329a,0x99394c92a644531f,0xa98e94c6aa631431,0x62989d4c44a61d53,0xc2984d4c1ca6095]))
|4,4=>(OfNat.ofNat (packedNat [0x43f2a1e550e8a86f,0x54352a19550c0a85,0xb542b2a1455098a8,0x4754212a0f55070a,0x83354172a0a55048,0xa81f540d2a055502,0xa80b54032a0090f,0xfaa7f853f9a9fb94,0xfd2a7e453efa9f69,0x4faaa7d053e5a9f1,0x94f82a7bc53dba9e,0xc94f5aa7a853d1a9,0xe794f32a79453c7a,0x9e294f0aa78053bd,0xa9dd94ee2a76c53b,0x3a9d894ebaa75853,0xaa21d3d4e94a7464]))
|4,5=>0x22355110a8835
|5,0=>(OfNat.ofNat (packedNat [0x501b27f953f0c9f2,0x64f63279993c0c9d,0xa64ea327399390c9,0xc264de326d99360c,0x9aa64d2aa6815334,0xc99464c732621930,0x4c97c64bbaa5c592,0xd6c96654b0325699,0x2a8c94e64a432509,0x9278c9366498324a,0x99248c91e648caa4,0x4d921ac9076480b2,0x3ed91ee88f16475b,0x239591bec8d96469,0xb2335918ec8c1645,0xdb22d5915ec8a964,0x51b2275912ec8925]))
|5,1=>(OfNat.ofNat (packedNat [0x5bdb2dd596decb69,0x65b1b2d7596aecb5,0x165a5b2d15967ecb,0x39659a2acb99650c,0xb22658e32c599620,0xcb0a658232bf995f,0xcaf2657632b9995,0xc0cada656a32b399,0x590cac2655e32add,0x5562caab6552b2a7,0xd9532ca9365472aa,0x219504ca7c653b32,0x9c194d6aa6565302,0xa96994a8ca4e6524,0x3290d547aca37651,0x8b28ad944aca1f65,0xcb284d941e8a096]))
|5,2=>(OfNat.ofNat (packedNat [0x67a333b999d0cce2,0x666eab35d99a2ccc,0xb6662b32fd9972cc,0xb366572b2a19944c,0xc9c664b332419916,0xac85663fb31e598e,0x6cc6d6633b318598,0xb6cc556627b31259,0x888ac3f561cb30cd,0x985cac2866113307,0x1982eac116605b30,0x1597fecbf965f9b2,0xfb597cecbe165edb,0x2f55979ecbc965e1,0xb2ef5976ecbb165d,0x5b2e95973ecb9965,0xc9b2e35970ecb816]))
|5,3=>(OfNat.ofNat (packedNat [0x735b39959cbece59,0x672a2b9399c90ce4,0x2671e338d99c60ce,0x2c4713338819c34c,0xe146707ab8295c08,0xcdfe66fc337c99bd,0x8cde666f0337699b,0xa8cdce66e4337099,0xb78cdb666d8336a9,0x9b4aad9f66cd2b65,0x19b1ccd8866c1335,0xf19aeccd7066b533,0x5919abccd5866a93,0x35319a8ccd40669d,0x334d19a5ccd28669,0x1ab4759a2ecd1256,0x86334199a00ccfa6]))
|5,4=>(OfNat.ofNat (packedNat [0x1,0xe6c8f30679533c91,0x9e3ccf18678933c3,0x19e0ccf00677d33b,0xd19ddccee8677133,0xb719dacced067653,0x3b119d7cceb86759,0x33ab19d4ccea0674,0xd33a519d1cce8867,0x41339f19ceeae716]))
|6,0=>(OfNat.ofNat (packedNat [0x8623c2f9a172b0b2,0x785634295e13cf09,0x77848b422da10cb0,0x81583db41d5a0ded,0x687831ac175a0ac,0xf05158253c10de07,0x8f03578173c09de0,0x42d01a780a34035e,0xcf00067fcbbfcd,0x9fdacfe857f133f6,0xddfaacfcf67e43bf,0x5df76cfb477d733,0xea19f46af9d67cc2,0xbe45df16cf8567bf,0xb3de1dee2ef6c57b,0x333d819eb4cf5377,0xa72bd219e82ef3a7]))
|6,1=>(OfNat.ofNat (packedNat [0x2,0x32af18e78c4ac611,0x62feb17a58ba345b,0x9a2cef16078acbc5,0x49e296f145689f3c,0x4e56266d12d68933,0xc481a236b1147886,0xbc4216204d0fc687,0xb343c1a1d6b0e478,0x6ebc359e1a2b0cb6]))
|7,0=>(OfNat.ofNat (packedNat [0x23d4d1e468ef,0x34761a3a4d1cc68e,0x334701a374d1b468,0xd7346a1a344d19c6]))
|8,0=>0x11f05
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 390 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 17 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 10 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x3035010640c0260,0x3035030342f82402,0xc90303603037030,0x36030372f8240106,0x4030350303401064,0x202503036030370,0x1064030360303703,0x340303503034010,0x1803035030340303,0x5030340303503034,0x208903034030100,0x3035030340236c01,0x640236e01064030,0x1003035030360303,0x7030360303703035,0x303503034030350,0x3034030350303403,0x36030370317d020,0x3403035010640303,0x50303503034030c9]))
|1=>(OfNat.ofNat (packedNat [0x2025030340488b0,0x2025030340303403,0x360303704835030,0x3503034030350303,0x5030340303604837,0x303503034010640,0x3036030370303402,0x250303503035048,0x35030342fac50302,0x4020350303503034,0x488903034020260,0x4835030cb0303403,0x340202401064030,0x35030100317d0483,0x7030350303403036,0x303403034030350,0x3034048360106402,0x590c82403035010,0x6402089030340236,0xf010640303603037]))
|2=>(OfNat.ofNat (packedNat [0x303603037020240,0x3035030360303701,0x640303603037010,0x1304835030360303,0x7030340303603037,0x303403034030360,0x2089030340303603,0x3503035030342fc,0x1b02035020340483,0x4030350207503034,0x483503034030130,0x303402089030342f,0x8240203503034010,0x18048371508b0202,0x5030340303503034,0x203501064048370,0x2089030341308902,0x240303403011020,0x8902024030340303,0x5030340303603037]))
|3=>(OfNat.ofNat (packedNat [0x203503034030350,0x3034020750488b03,0x34030350c8a8020,0x2503035020260303,0x5030340303503034,0x303503034030352,0xf824020350303403,0x3503034030345d8,0x18030372f8240203,0x501018048370317f,0x2f82402035030360,0x3034030360303702,0x890303402027020,0x2603035030130202,0x6010640303603037,0x303403034030350,0x3034030c90303503,0x340483603034030,0x3503034030350202,0x4030340208903034]))
|4=>(OfNat.ofNat (packedNat [0x30360317e048370,0x102402025030352f,0x8240203503036030,0x37030132f8240203,0x52d0350483403036,0x102403036020270,0x1064030350303403,0x340102403024020,0x352f824030350303,0x6048370208903034,0x303502089030340,0x2089030340303603,0x370483703034020,0x2502027010640303,0x6030350303404d1b,0xc81303035010640,0x2025030340203504,0x8370207702026030,0x3603037020260303,0x603036010642f824]))
|5=>(OfNat.ofNat (packedNat [0x483703036030360,0x3036048370303403,0x360202703037048,0x3603036048352f82,0x6030350483703036,0x23e504834012c80,0x3025048350483704,0x83702036030360c8,0x2703035030350303,0x6030360483503034,0x30360208b030340,0x2024030370c82403,0x350208b03034020,0x8903034020260303,0x7030360303603036,0xc81003035010240,0x4835020340101804,0x8370483503036592,0xc703024030250303,0x4030350303603037]))
|6=>(OfNat.ofNat (packedNat [0x302703026030360,0x3036048370202503,0x340203502025030,0x37030360c8130303,0x5048370488b03034,0x30360348b020360,0x3036030370483704,0x8362f82401011048,0x3502035020340488,0xb03034048370126f,0x48372f824020350,0x4c1b020340303602,0x250303504835048,0x8903034030360303,0x6022910302603034,0x303601024030360,0x3036048370303603,0x360488903034048,0x3504836048375883,0x5030240202603036]))
|7=>(OfNat.ofNat (packedNat [0x30240303703036,0x303404837048360,0x2035030250203402,0x360483403026030,0x3504835030360202,0x4030340302403025]))
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat (packedNat [0x12000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10,0x0,0x0,0x0,0x0]))
|3,1=>0
|3,2=>0
|4,0=>(OfNat.ofNat (packedNat [0xe2000000,0x18,0x400000000000000a,0x2041000000000000,0x7100000,0x0,0xa40,0x820000,0x0,0x0,0x0,0x31]))
|4,1=>(OfNat.ofNat (packedNat [0xd9000000019,0x200000000000000b,0x900000001610a880,0x0,0x0,0x1320,0x0,0x1120000000,0x0,0x101]))
|4,2=>(OfNat.ofNat (packedNat [0x544000000,0xa4,0x44e4000130890800,0x44400,0x0,0x0,0x0,0x0,0x1,0x100000001e20000,0x0,0x3a2,0x0]))
|4,3=>(OfNat.ofNat (packedNat [0x764000000,0x0,0x0,0xe8472200,0x0,0xdc800000000000,0x0,0x1a90cc80000,0x0,0x0,0x1890000,0x2f20000000000,0x16900000002c1]))
|4,4=>(OfNat.ofNat (packedNat [0x8c2000000000000,0x88400,0x0,0x84400000000,0x0,0x0,0x0,0x1,0x80003f10000f84,0x7a20000000000000,0x0]))
|4,5=>0
|5,0=>(OfNat.ofNat (packedNat [0x1044000401,0x1f88f667833b8800,0x7613a89d04e4,0x4000388800000070,0x13710000da200035,0x90000d0667133080,0x328988cc,0x45e22e89704b625,0xa10000000b220002,0xb18000aa25410001,0x4c4a240002808000,0x9e24e10001308944,0x8e6000]))
|5,1=>(OfNat.ofNat (packedNat [0x1744000000,0x2e44000b72000000,0x16a4b32000000000,0x590ac0800000,0x57880015a4ab200,0x154200054880,0x1502a71000290d4,0x62a2150127c40009,0xe14e8a7040009a24,0xc100012e20004a92,0x48d2048f10002348,0x459220d0e2,0x8430000000000000]))
|5,2=>(OfNat.ofNat (packedNat [0x1ea60007a0,0x8000000000000000,0x7913c0800,0xee2768800000000,0x7593a85d0400073,0x8b985c66e126f1b7,0x440000006e08001b,0x440000000001b04d,0x716a90000000d410,0x6910,0x1a04cf1670b309,0x96200000032498e4,0xc52611b0097c4bc2]))
|5,3=>(OfNat.ofNat (packedNat [0x961,0x958800,0x4a8400,0x948800250326,0x200049464652038f,0x8c74a36400000046,0x480000008c0c5c62,0xc3142898c4480010,0xe300043461830b18,0x4900021030718290,0x2083031810c044,0x7f90001fc2,0xfc27c98000000f81]))
|5,4=>(OfNat.ofNat (packedNat [0x2886000a18d00c0,0x13f10004f867a33,0xc100000027440000,0x4e080000000000,0x26c53339908002,0x6233010000000001,0x2e20000000000000]))
|6,0=>(OfNat.ofNat (packedNat [0xc98e44b2038f1c69,0x63071638a1c48e1c,0xb0c3851c20e08b02,0x38010005fc6fc200,0xbe8df06f63792bb,0x90002ec3751ba080,0x2e637120005c06d,0xc56c2b58da86d236,0x81b388002ca5632b,0x10d846c035f1ae95,0x6cab25572aa954ca,0xa42000a88d4069c5,0x4c2a58d24a903471]))
|6,1=>(OfNat.ofNat (packedNat [0x3883c22e016f880,0xde8ef07763b,0x92dc0ed8b6a3b32d,0x90ec0b5e3ad2d60e,0xa8b523a81d31690b,0x445a11cf9674b365,0x9a1cc165c72a5941]))
|7,0=>(OfNat.ofNat (packedNat [0x3a43d11e80f3c7,0x9c3cd1e60f2c7943,0xc91e40f1c78c3c51]))
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x4482201,0xa08204082000840,0x4102000980480210,0x10007403201800a0,0x480220100070034,0x12008003801800a,0x40018008002000]))
|1=>(OfNat.ofNat (packedNat [0x1478a2c5,0x122881438a1850a2,0x831410a0441e20a1,0x488044001800a00,0x4182000d105e02b0,0x13c09d04c8260128,0x90047823811a08c]))
|2=>(OfNat.ofNat (packedNat [0x501a8054,0x88f421a0450088,0x24001a3cc1e60b3,0x4936c93e48b2401,0x1bc884416208103c,0x81c409204101c80a,0x40018b0c4861c29f]))
|3=>(OfNat.ofNat (packedNat [0xd46ea174,0x3ba03c00531a1a10,0x8f812c042000f427,0x67bafdd32e97720b,0x87dc1ee087013801,0x9b6cd165caa7d532,0xa97546aa1943ea07]))
|4=>0x3d3fa8f
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat (packedNat [0x100000000,0x0,0x0,0x0,0x0,0x200000000,0x0,0x0]))
|3,1=>0
|4,0=>(OfNat.ofNat (packedNat [0x80008130004,0x1a000000,0x100040800080000,0x808082d01000808,0x40804000008,0x400000100000000,0x41a010000040c,0x800000417,0x1,0x100,0x1011a0000,0x200040000,0x100,0xc08000c080000,0x8000000000008,0x800000000000017]))
|4,1=>(OfNat.ofNat (packedNat [0x10008000000,0xc00000c00000008,0x4130000130000,0x1000000000000,0x1080000,0x8000c0800000000,0x800000c01000808,0x8150000011a0008,0x10000000000,0x2010008010800,0x10008080004,0x804000000,0x0,0x1000000001000001,0x0,0x4002d000c000008]))
|4,2=>(OfNat.ofNat (packedNat [0xc00,0x1e0000,0x80000040000,0x40100001a0400,0x8080800000000,0x80000000000,0x80000,0x1041700081a00,0xc000000]))
|5,0=>(OfNat.ofNat (packedNat [0x10000080401,0x2d00050900001a00,0x2f01000017080901,0x1a1c0202130117,0x76070f5730010017,0x412d00186c1a4d1a,0x1c0901570c100000,0x13308230008160c,0x80100010a3221,0x108002d4d2d0d00,0x5808000109002502,0x1f000d2f01000000,0x2d3601010801022d,0x170012082e02,0xc011a01002d17,0x9100031083202]))
|5,1=>(OfNat.ofNat (packedNat [0x8000000,0x1700000000170000,0x1908593c0c440d1f,0x11b01131a1b000c,0x18442a106b010003,0x1e084433081a08,0x1001301171a0808,0x6a00580d32000017,0x1002b000000,0x75000001010001,0x1700001a14440100,0x2d02030303440000,0x170809000800011a,0xe00000800000000,0x100001172d090200,0x11d091101010e]))
|5,2=>(OfNat.ofNat (packedNat [0x700,0x20100441a027b24,0x180000010000,0x1452d002444,0x10000d00000000]))
|6,0=>(OfNat.ofNat (packedNat [0x4756,0x5f3849496809015c,0x3a424751773d6773,0x44224c0607463e01,0x7f6d54795a01435b,0x5d704d016f442044,0x1664c7a013f265d,0x635e004b016227,0x34316e447d0b0429,0x1a535564817c7e72,0x471a652701012f09,0x5039404852372c00,0x747151604a78014f]))
|7,0=>(OfNat.ofNat (packedNat [0x3b28691f806e,0x4a644a4e35642861]))
|8,0=>1
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 8 (j % 128);fld (pmPalB (k / 32)) 13 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dzo_15_16,7,runOps true dzo_15_16 (0,roots_15) ops)] else [])++(if pm.testBit 1 then [(dzo_25_2,4,runOps true dzo_25_2 (0,roots_25) ops)] else [])++(if pm.testBit 2 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 3 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 4 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 5 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 6 then [(dzo_11_16,4,runOps true dzo_11_16 (0,roots_11) ops)] else [])++(if pm.testBit 7 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 8 then [(dzo_13_16,4,runOps true dzo_13_16 (0,roots_13) ops)] else [])++(if pm.testBit 9 then [(dom_29,5,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 10 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 11 then [(dzo_29_2,5,runOps true dzo_29_2 (0,roots_29) ops)] else [])++(if pm.testBit 12 then [(dzo_7_16,4,runOps true dzo_7_16 (0,roots_7) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowSh_15_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_25_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_8_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_11_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_13_16_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_0 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_0 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_29_2_2 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_7_16_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_15_16 7 s (0,roots_15) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_15_16_16 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 7 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 7 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_0:∀ i,0 ≤ i → i < 128 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3_128:∀ i,128 ≤ i → i < 143 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 15 128=true)
private theorem z3:∀ i,0 ≤ i → i < 143 → Z 3 i=true:=(range_split z3_0 z3_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 256 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 128 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_256:∀ i,256 ≤ i → i < 323 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 67 256=true)
private theorem z4:∀ i,0 ≤ i → i < 323 → Z 4 i=true:=(range_split z4_0 (range_split z4_128 z4_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 256 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 128=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_256:∀ i,256 ≤ i → i < 290 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 34 256=true)
private theorem z5:∀ i,0 ≤ i → i < 290 → Z 5 i=true:=(range_split z5_0 (range_split z5_128 z5_256))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 98 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 98 0=true)
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
theorem noCircuit:Lower true dom_31 roots_31 goal_31_0 9:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_31_0
theorem lowS_31_0:Lower true dom_31 roots_31 goal_31_0 9:=S_31_0.noCircuit
end Case1
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
def posted : BF 6 := fun x => Nat.testBit (4276677320 * 2 ^ 32 + 3974678528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def tab : BF 6 := fun x => Nat.testBit 18368189228919605248 (Nat.ofBits x)
theorem targetEq : posted = tab := funext (all_pts _ (by decide +kernel))
def sample0 (k : Nat) : Fin 6 → Bool := fun i => !k.testBit (([2, 0, 3, 1, 4, 99] : List Nat).getD i.val 99)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restricted0 : ∀ k, R (phi (5 : Fin 6) false (nz tab)) k (L0 6) → 9 ≤ k :=
  observedFloorDual Case0.dom_31 sample0 _ Case0.roots_31 Case0.goal_31_0 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) Case0.lowS_31_0
def sample1 (k : Nat) : Fin 6 → Bool := fun i => k.testBit (([0, 2, 1, 3, 4, 99] : List Nat).getD i.val 99)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restricted1 : ∀ k, R (phi (5 : Fin 6) true (nz tab)) k (L0 6) → 9 ≤ k :=
  observedFloor Case1.dom_31 sample1 _ Case1.roots_31 Case1.goal_31_0 9 (by decide +kernel) (by decide +kernel) Case1.lowS_31_0
theorem gateBound : ∀ k, R (nz tab) k (L0 6) → 11 ≤ k := by
  intro k h
  obtain ⟨q,rfl,hq | hq⟩ := two_gates (5 : Fin 6) (nz tab) (ne_F _ (pt 11) (by decide +kernel)) (ne_F _ (pt 3) (by decide +kernel)) (reads (5 : Fin 6) _ (pt 3) (by decide +kernel)) k (L0 6) (good_L0 _) h
  · have := restricted0 q hq
    omega
  · have := restricted1 q hq
    omega
def witness : List Gate := [⟨.and,[5,1]⟩,⟨.or,[5,1]⟩,⟨.or,[1,2]⟩,⟨.and,[7,3]⟩,⟨.or,[9,6]⟩,⟨.and,[1,2]⟩,⟨.and,[8,4]⟩,⟨.or,[10,12]⟩,⟨.and,[9,12]⟩,⟨.or,[11,14]⟩,⟨.or,[15,0]⟩,⟨.and,[13,16]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witOK : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,17⟩ (List.ofFn x) = posted x := by
  rw [targetEq]
  exact all_pts _ (by decide +kernel)
end PEqualNP.Outside.L_meta_47221_aux
open PEqualNP.Outside.L_meta_47221_aux PEqualNP.Outside.L_meta_47221_aux.Logic in
theorem PEqualNP.Outside.L_meta_47221 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3974678528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3974678528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  apply mono_shape2 posted 11 _ witness 17 (monoOK_sound _ (by decide +kernel)) (by decide +kernel) witOK
  rw [targetEq]
  exact gateBound
