import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27661_aux

namespace Lower
abbrev Fn (n : Nat) := (Fin n → Bool) → Bool
def start {n : Nat} : List (Fn n) :=
  [fun _ => false, fun _ => true] ++ (List.ofFn (fun i : Fin n => [fun x => x i, fun x => !(x i)])).flatten
inductive Run {n : Nat} : List (Fn n) → Nat → Fn n → Prop
  | stop {v k t} : t ∈ v → Run v k t
  | step {v k t a b} : a ∈ v → b ∈ v →
      Run (v ++ [fun x => a x && b x, fun x => !(a x && b x)]) k t → Run v (k + 1) t
end Lower

namespace Pin
open Lower
abbrev inv {n} (f : Fn n) : Fn n := fun x => !(f x)
abbrev meet {n} (a b : Fn n) : Fn n := fun x => a x && b x
abbrev Has {n} (S : List (Fn n)) (f : Fn n) := f ∈ S ∧ inv f ∈ S
abbrev Both {n} (S : List (Fn n)) := Has S (fun _ => false)
abbrev Const {n} (f : Fn n) := ∃ c, ∀ x, f x = c
def append {n} (S : List (Fn n)) (a b : Fn n) := S ++ [meet a b, inv (meet a b)]
private theorem neg2 {n} (f : Fn n) : inv (inv f) = f := by funext x; simp
private theorem swap {n S} {f : Fn n} (h : Has S f) : Has S (inv f) := ⟨h.2, by rw [neg2]; exact h.1⟩
private theorem old {n S} {f a b : Fn n} (h : Has S f) : Has (append S a b) f :=
  ⟨List.mem_append_left _ h.1, List.mem_append_left _ h.2⟩
private theorem fresh {n} (S : List (Fn n)) (a b : Fn n) : Has (append S a b) (meet a b) := by
  constructor <;> apply List.mem_append_right <;> simp
private theorem extend {n m} {S : List (Fn n)} {D : List (Fn m)} {a b : Fn n}
    (p : (Fin m → Bool) → (Fin n → Bool)) (base : ∀ f ∈ S, Has D (f ∘ p))
    (h : Has D ((meet a b) ∘ p)) : ∀ f ∈ append S a b, Has D (f ∘ p) := by
  intro f hf; rcases List.mem_append.mp hf with hf | hf; exact base _ hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; rcases hf with rfl | rfl; exact h; exact swap h
private theorem absorb {n} {S : List (Fn n)} {a b : Fn n} (z : Both S)
    (ha : Has S a) (hb : Has S b) (h : Const a ∨ Const b) : Has S (meet a b) := by
  rcases h with ⟨c, h⟩ | ⟨c, h⟩ <;> cases c
  · simpa only [show meet a b = fun _ => false by funext x; simp [meet, h]] using z
  · simpa only [show meet a b = b by funext x; simp [meet, h]] using hb
  · simpa only [show meet a b = fun _ => false by funext x; simp [meet, h]] using z
  · simpa only [show meet a b = a by funext x; simp [meet, h]] using ha

theorem weaken {n S k} {f : Fn n} (h : Run S k f) : ∀ {l}, k ≤ l → Run S l f := by
  induction h with
  | stop ht => intro l _; exact .stop ht
  | @step v k t a b ha hb h ih =>
    intro l hl; obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
    exact .step ha hb (ih (by omega))

theorem project {n m S k} {t : Fn n} (h : Run S k t) (p : (Fin m → Bool) → (Fin n → Bool))
    (D : List (Fn m)) (base : ∀ f ∈ S, Has D (f ∘ p)) : Run D k (t ∘ p) := by
  induction h generalizing D with
  | stop ht => exact .stop (base _ ht).1
  | @step v k t a b ha hb h ih =>
    apply Run.step (base _ ha).1 (base _ hb).1; apply ih
    exact extend p (fun f hf => old (base f hf)) (fresh _ _ _)

theorem save {n m S k} {t : Fn n} (h : Run S k t) (p : (Fin m → Bool) → (Fin n → Bool))
    (Stable : Fn n → Prop)
    (nand : ∀ a b, Stable a → Stable b → Stable (meet a b))
    (neg : ∀ f, Stable f → Stable (inv f))
    (nt : ¬Stable t) (nc : ¬Const (t ∘ p)) (bank : ∀ f ∈ S, Stable f ∨ Const (f ∘ p))
    (D : List (Fn m)) (constants : Both D) (base : ∀ f ∈ S, Has D (f ∘ p)) :
    ∃ l, l + 1 ≤ k ∧ Run D l (t ∘ p) := by
  classical
  induction h generalizing D with
  | stop ht => exact False.elim ((bank _ ht).elim nt nc)
  | @step v k t a b ha hb h ih =>
    by_cases sab : Stable a ∧ Stable b
    · have st := nand a b sab.1 sab.2
      have next : ∀ f ∈ append v a b, Stable f ∨ Const (f ∘ p) := by
        intro f hf; rcases List.mem_append.mp hf with hf | hf; exact bank _ hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl; exact Or.inl st; exact Or.inl (neg _ st)
      obtain ⟨l, hl, hr⟩ := ih nt nc next _ (old constants)
        (extend p (fun f hf => old (base f hf)) (fresh _ _ _))
      exact ⟨l + 1, by omega, .step (base _ ha).1 (base _ hb).1 hr⟩
    · have ca : Const (a ∘ p) ∨ Const (b ∘ p) := by
        rcases bank a ha with h | h <;> rcases bank b hb with j | j <;> tauto
      have hit := absorb constants (base _ ha) (base _ hb) ca
      exact ⟨k, by omega, project h p D (extend p base hit)⟩

theorem saveTwo {n m S k} {t : Fn n} (h : Run S k t) (p : Bool → (Fin m → Bool) → (Fin n → Bool))
    (Stable : Fn n → Prop)
    (nand : ∀ a b, Stable a → Stable b → Stable (meet a b))
    (neg : ∀ f, Stable f → Stable (inv f))
    (nt : ¬Stable t) (nc : ∀ c, ¬Const (t ∘ p c))
    (bank : ∀ f ∈ S, Stable f ∨ ((∀ c, Const (f ∘ p c)) ∧ ∃ c, ∀ x, f (p c x) = false))
    (D : Bool → List (Fn m)) (constants : ∀ c, Both (D c))
    (base : ∀ c, ∀ f ∈ S, Has (D c) (f ∘ p c)) :
    ∃ c l, l + 2 ≤ k ∧ Run (D c) l (t ∘ p c) := by
  classical
  induction h generalizing D with
  | stop ht => exact False.elim ((bank _ ht).elim nt fun h => nc false (h.1 false))
  | @step v k t a b ha hb h ih =>
    by_cases sab : Stable a ∧ Stable b
    · have st := nand a b sab.1 sab.2
      have next : ∀ f ∈ append v a b, Stable f ∨ ((∀ c, Const (f ∘ p c)) ∧ ∃ c, ∀ x, f (p c x) = false) := by
        intro f hf; rcases List.mem_append.mp hf with hf | hf; exact bank _ hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl; exact Or.inl st; exact Or.inl (neg _ st)
      obtain ⟨c, l, hl, hr⟩ := ih nt nc next (fun c => append (D c) (a ∘ p c) (b ∘ p c))
        (fun c => old (constants c)) (fun c => extend (p c) (fun f hf => old (base c f hf)) (fresh _ _ _))
      exact ⟨c, l + 1, by omega, .step (base c _ ha).1 (base c _ hb).1 hr⟩
    · have force : ∃ c, ∀ x, meet a b (p c x) = false := by
        by_cases sa : Stable a
        · obtain ⟨c, hc⟩ := ((bank _ hb).resolve_left (fun h => sab ⟨sa, h⟩)).2
          exact ⟨c, fun x => by simp [meet, hc]⟩
        · obtain ⟨c, hc⟩ := ((bank _ ha).resolve_left sa).2
          exact ⟨c, fun x => by simp [meet, hc]⟩
      obtain ⟨c, hc⟩ := force
      have hit : (meet a b ∘ p c) = fun _ => false := funext hc
      have next : ∀ f ∈ append v a b, Stable f ∨ Const (f ∘ p c) := by
        intro f hf; rcases List.mem_append.mp hf with hf | hf
        · exact (bank _ hf).imp_right (fun h => h.1 c)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with rfl | rfl
          · exact Or.inr ⟨false, hc⟩
          · exact Or.inr ⟨true, fun x => by simp [Function.comp_apply, inv, hc]⟩
      obtain ⟨l, hl, hr⟩ := save h (p c) Stable nand neg nt (nc c) next (D c) (constants c)
        (extend (p c) (base c) (hit ▸ constants c))
      exact ⟨c, l, by omega, hr⟩
end Pin

namespace Coord
open Lower Pin
abbrev Code (m : Nat) := Option (Fin m)
def pin {n m} (c : Fin n → Code m) (v : Bool) (x : Fin m → Bool) (i : Fin n) := (c i).elim v x
def stable {n m} (c : Fin n → Code m) (f : Fn n) := ∀ x, f (pin c false x) = f (pin c true x)
private theorem both {n} : Both (@start n) :=
  ⟨by simp [start], by change (fun _ => true) ∈ _; simp [start]⟩
private theorem lit {n} (i : Fin n) : Has start (fun x => x i) := by
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatten.mpr <;>
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, by simp⟩
private theorem casesStart {n} {f : Fn n} (h : f ∈ start) :
    (∃ b, f = fun _ => b) ∨ ∃ i : Fin n, f = (fun x => x i) ∨ f = (fun x => !(x i)) := by
  rcases List.mem_append.mp h with h | h
  · simp at h; rcases h with rfl | rfl; exact Or.inl ⟨false, rfl⟩; exact Or.inl ⟨true, rfl⟩
  · obtain ⟨l, hl, h⟩ := List.mem_flatten.mp h; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact Or.inr ⟨i, by simpa using h⟩
private theorem negHas {n S} {f : Fn n} (h : Has S f) : Has S (inv f) :=
  ⟨h.2, by rw [show inv (inv f) = f by funext x; simp [inv]]; exact h.1⟩
private theorem available {n m} (c : Fin n → Code m) (v : Bool) (f : Fn n) (hf : f ∈ start) :
    Has start (f ∘ pin c v) := by
  rcases casesStart hf with ⟨b, rfl⟩ | ⟨i, hi⟩
  · cases b; exact both; exact negHas both
  · cases h : c i with
    | none => rcases hi with rfl | rfl <;> cases v <;>
        simp only [Function.comp_def, pin, h, Option.elim, Bool.not_true, Bool.not_false] <;>
        first | exact both | exact negHas both
    | some j => rcases hi with rfl | rfl <;>
        simp only [Function.comp_def, pin, h, Option.elim] <;>
        first | exact lit j | exact negHas (lit j)
private theorem bank {n m} (c : Fin n → Code m) (f : Fn n) (hf : f ∈ start) :
    stable c f ∨ ((∀ b, Const (f ∘ pin c b)) ∧ ∃ b, ∀ x, f (pin c b x) = false) := by
  rcases casesStart hf with ⟨b, rfl⟩ | ⟨i, h⟩
  · exact Or.inl fun _ => rfl
  · cases he : c i with
    | some j => rcases h with rfl | rfl <;> exact Or.inl (by simp [stable, pin, he])
    | none => rcases h with rfl | rfl
              · exact Or.inr ⟨fun b => ⟨b, by simp [pin, he]⟩, false, by simp [pin, he]⟩
              · exact Or.inr ⟨fun b => ⟨!b, by simp [pin, he]⟩, true, by simp [pin, he]⟩
private theorem sand {n m} (c : Fin n → Code m) (a b : Fn n) (ha : stable c a) (hb : stable c b) :
    stable c (meet a b) := by intro x; simp only [meet, ha x, hb x]
private theorem sneg {n m} (c : Fin n → Code m) (a : Fn n) (h : stable c a) :
    stable c (inv a) := by intro x; simp only [inv, h x]
theorem one {n m k} (c : Fin n → Code m) (v : Bool) (f : Fn n) (h : Run start k f)
    (dep : ¬stable c f) (nc : ¬Const (f ∘ pin c v)) : ∃ l, l + 1 ≤ k ∧ Run start l (f ∘ pin c v) :=
  save h _ _ (sand c) (sneg c) dep nc (fun a ha => (bank c a ha).imp_right fun z => z.1 v) _ both (available c v)
theorem two {n m k} (c : Fin n → Code m) (f : Fn n) (h : Run start k f)
    (dep : ¬stable c f) (nc : ∀ b, ¬Const (f ∘ pin c b)) : ∃ b l, l + 2 ≤ k ∧ Run start l (f ∘ pin c b) :=
  saveTwo h _ _ (sand c) (sneg c) dep nc (bank c) _ (fun _ => both) (available c)
end Coord

namespace Alt
open Lower Pin Coord
def erase {n} (j i : Fin (n + 1)) : Code n :=
  if _ : i.val = j.val then none else if h : i.val < j.val then some ⟨i.val, by omega⟩
  else some ⟨i.val - 1, by omega⟩
inductive Tree : Nat → Type
  | leaf {n} : Tree n
  | fixOne {n} (j : Fin (n + 1)) (b : Bool) (rest : Tree n) : Tree (n + 1)
  | pick {n} (j : Fin (n + 1)) (lo hi : Tree n) : Tree (n + 1)
def weight {n} : Tree n → Nat
  | .leaf => 1
  | .fixOne _ _ rest => weight rest + 1
  | .pick _ lo hi => min (weight lo) (weight hi) + 2
def check {n} (tree : Tree n) : Fn n → Bool :=
  match tree with
  | .leaf => fun f => decide (f ∉ start)
  | .fixOne j b rest => fun f =>
    let c := erase j; let g := f ∘ pin c b
    decide (¬ ∀ x, f (pin c false x) = f (pin c true x)) &&
    decide (¬ ∃ v, ∀ x, g x = v) && check rest g
  | .pick j lo hi => fun f =>
    let c := erase j; let g := fun b => f ∘ pin c b
    decide (¬ ∀ x, f (pin c false x) = f (pin c true x)) &&
    decide (∀ b, ¬ ∃ v, ∀ x, g b x = v) && check lo (g false) && check hi (g true)
theorem sound {n} (tree : Tree n) (f : Fn n) {k} (h : Run start k f) (ok : check tree f = true) :
    weight tree ≤ k := by
  induction tree generalizing k with
  | leaf =>
    simp only [check, decide_eq_true_eq] at ok
    cases k with
    | zero => cases h with | stop hm => exact False.elim (ok hm)
    | succ k => simp [weight]
  | fixOne j b rest ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨l, hl, hr⟩ := one (erase j) b f h ok.1.1 ok.1.2
    have hw := ih _ hr ok.2; simp only [weight]; omega
  | pick j lo hi il ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨b, l, hl, hr⟩ := two (erase j) f h ok.1.1.1 ok.1.1.2
    cases b with
    | false => have hw := il _ hr ok.1.2; simp only [weight]; omega
    | true => have hw := ih _ hr ok.2; simp only [weight]; omega

def perm : Fn 9 := fun x =>
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)
def cofactor : Fn 8 := perm ∘ pin (erase (0 : Fin 9)) true
private def cert : Tree 8 := (.pick 3 (.fixOne 1 true (.pick 3 (.fixOne 0 true (.pick 1 (.fixOne 0 true .leaf) (.fixOne 0 true .leaf))) (.fixOne 4 false (.pick 0 (.fixOne 0 false .leaf) (.fixOne 0 true .leaf))))) (.pick 0 (.fixOne 1 true (.pick 1 (.fixOne 0 true (.fixOne 0 false .leaf)) (.fixOne 0 true (.fixOne 0 false .leaf)))) (.fixOne 1 false (.pick 0 (.fixOne 0 true (.fixOne 0 false .leaf)) (.fixOne 0 true (.fixOne 0 false .leaf))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower {k} (h : Run start k cofactor) : 10 ≤ k :=
  sound cert cofactor h (by decide +kernel)
end Alt

namespace Prefix
open PEqualNP.CircuitLowerBounds Lower
private def neg {n} (f : Fn n) : Fn n := fun x => !(f x)
private def Dual {n} (v : List (Fn n)) (f : Fn n) := f ∈ v ∧ neg f ∈ v
private abbrev zeroF {n} : Fn n := fun _ => false
private theorem dualNeg {n} {v : List (Fn n)} {f} (h : Dual v f) : Dual v (neg f) := by
  have e : neg (neg f) = f := by funext x; simp [neg]
  exact ⟨h.2, e.symm ▸ h.1⟩
private theorem dualIncl {n} {v w : List (Fn n)} {f} (sub : v ⊆ w) (h : Dual v f) : Dual w f :=
  ⟨sub h.1, sub h.2⟩
private theorem raise {n} {v : List (Fn n)} {k t} (h : Run v k t) : Run v (k + 1) t := by
  induction h with
  | stop hm => exact .stop hm
  | step ha hb _ ih => exact .step ha hb ih
private def value {n} (ws : List (Fn n)) (g : Gate) : Fn n := fun x =>
  g.op.eval (g.inputs.map fun i => (ws.getD i zeroF) x)
private def extend {n} (ws : List (Fn n)) (g : Gate) := ws ++ [value ws g]
private def scalar (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
private abbrev Good (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
private def cost (g : Gate) := match g.op with | .not => 0 | _ => 1
private theorem takeGate {n k} {v ws : List (Fn n)} {t : Fn n} (g : Gate) (ok : Good g)
    (hz : Dual v zeroF) (hw : ∀ i, Dual v (ws.getD i zeroF))
    (cont : ∀ u : List (Fn n), v ⊆ u → Dual u (value ws g) → Run u k t) : Run v (k + cost g) t := by
  rcases g with ⟨op, ins⟩; obtain ⟨hOp, hlen⟩ := ok
  cases ins with
  | nil => rcases hOp with rfl | rfl | rfl
           · exact raise (cont v (fun _ h => h) (dualNeg hz))
           · exact raise (cont v (fun _ h => h) hz)
           · exact cont v (fun _ h => h) (dualNeg hz)
  | cons a l => cases l with
    | nil => rcases hOp with rfl | rfl | rfl
             · apply raise; apply cont _ (fun _ h => h); convert hw a using 1; funext x; simp [value, GateOp.eval]
             · apply raise; apply cont _ (fun _ h => h); convert hw a using 1; funext x; simp [value, GateOp.eval]
             · apply cont _ (fun _ h => h); convert dualNeg (hw a) using 1; funext x; simp [value, GateOp.eval, neg]
    | cons b r => cases r with
      | nil =>
        rcases hOp with rfl | rfl | rfl
        · apply Run.step (hw a).1 (hw b).1
          apply cont _ (List.subset_append_left ..)
          have h0 : value ws ⟨.and, [a, b]⟩ = fun x => ws.getD a zeroF x && ws.getD b zeroF x := by
            funext x; simp [value, GateOp.eval]
          rw [h0]
          constructor
          · apply List.mem_append_right; simp
          · apply List.mem_append_right; exact List.mem_cons_of_mem _ List.mem_cons_self
        · apply Run.step (hw a).2 (hw b).2
          apply cont _ (List.subset_append_left ..)
          have h1 : value ws ⟨.or, [a, b]⟩ = fun x => !(neg (ws.getD a zeroF) x && neg (ws.getD b zeroF) x) := by
            funext x; simp [value, GateOp.eval, neg]
          rw [h1]
          constructor
          · apply List.mem_append_right; simp
          · apply List.mem_append_right
            rw [show neg (fun x => !(neg (ws.getD a zeroF) x && neg (ws.getD b zeroF) x)) = fun x => neg (ws.getD a zeroF) x && neg (ws.getD b zeroF) x by funext x; simp [neg]]
            exact List.mem_cons_self
        · apply cont _ (fun _ h => h)
          convert dualNeg (hw a) using 1; funext x; simp [value, GateOp.eval, neg]
      | cons _ _ => simp at hlen

private theorem compile {n} (gs : List Gate) (o : Nat) (ws v : List (Fn n))
    (ok : ∀ g ∈ gs, Good g) (hz : Dual v zeroF) (hw : ∀ f ∈ ws, Dual v f) :
    Run v (gs.map cost).sum ((gs.foldl extend ws).getD o zeroF) := by
  induction gs generalizing ws v with
  | nil =>
    by_cases ho : o < ws.length
    · rw [List.foldl_nil, List.getD_eq_getElem _ _ ho]; exact .stop (hw _ (List.getElem_mem ho)).1
    · rw [List.foldl_nil, List.getD_eq_default _ _ (Nat.le_of_not_gt ho)]; exact .stop hz.1
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    rw [Nat.add_comm]
    refine takeGate (ws := ws) g (ok g List.mem_cons_self) hz (fun i => ?_) (fun u sub hu => ?_)
    · by_cases hi : i < ws.length
      · rw [List.getD_eq_getElem _ _ hi]; exact hw _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]; exact hz
    · refine ih (extend ws g) u (fun x hx => ok x (List.mem_cons_of_mem _ hx)) (dualIncl sub hz) ?_
      intro f hf; rcases List.mem_append.mp hf with hf | hf
      · exact dualIncl sub (hw f hf)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; rwa [hf]

private theorem cost_le (gs : List Gate) : (gs.map cost).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; cases h : g.op <;> (simp [cost, h]; omega)

private theorem readMap {n} (ws : List (Fn n)) (o : Nat) (x : Fin n → Bool) :
    (ws.map fun f => f x).getD o false = (ws.getD o zeroF) x := by
  by_cases ho : o < ws.length
  · rw [List.getD_eq_getElem _ _ (by simp [ho]), List.getElem_map, List.getD_eq_getElem _ _ ho]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem foldMap {n} (gs : List Gate) (ws : List (Fn n)) (x : Fin n → Bool) :
    (gs.foldl extend ws).map (fun f => f x) = gs.foldl scalar (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1; simp only [extend, scalar, List.map_append, List.map_cons, List.map_nil]
    congr 2; simp only [value]; congr 1; apply List.map_congr_left; intro i _; exact (readMap ws i x).symm

private def g0 : Gate := ⟨.or, [0, 1]⟩
private def g1 : Gate := ⟨.not, [9]⟩
private def inFns : List (Fn 9) := List.ofFn fun i : Fin 9 => fun x : Fin 9 → Bool => x i
private def f0 : Fn 9 := value inFns g0
private def f1 : Fn 9 := value (inFns ++ [f0]) g1
private def orig : List (Fn 9) := inFns ++ [f0, f1]
private def bank : List (Fn 9) := (@start 9) ++ [f0, neg f0, f1, neg f1]

private theorem lit {n} (i : Fin n) : Dual (@start n) (fun x => x i) := by
  constructor
  · apply List.mem_append_right; apply List.mem_flatten.mpr
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_cons_self⟩
  · apply List.mem_append_right; apply List.mem_flatten.mpr
    exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_cons_of_mem _ List.mem_cons_self⟩

private theorem each {P : Fn 9 → Prop} (z : P zeroF) (n : ∀ f, P f → P (neg f))
    (l : ∀ i : Fin 9, P fun x => x i) (p0 : P f0) (p1 : P f1) : ∀ f ∈ bank, P f := by
  intro f hf; rcases List.mem_append.mp hf with h | h
  · rcases List.mem_append.mp h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl; exact z; exact n _ z
    · obtain ⟨a, ha, hf⟩ := List.mem_flatten.mp h; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl; exact l i; exact n _ (l i)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl; exact p0; exact n _ p0; exact p1; exact n _ p1

private abbrev cPin : Fin 9 → Coord.Code 8 := Alt.erase (0 : Fin 9)
private abbrev plug : (Fin 8 → Bool) → (Fin 9 → Bool) := Coord.pin cPin true
private abbrev stab : Fn 9 → Prop := Coord.stable cPin

theorem pinPrefix (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (sz : C.size ≤ 12) (rep : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = Alt.perm x)
    (h0 : C.gates.head? = some g0) (h1 : C.gates.tail.head? = some g1) :
    Run start 9 Alt.cofactor := by
  rcases C with ⟨gs, o⟩
  cases gs with
  | nil => simp at h0
  | cons a gs =>
    cases gs with
    | nil => simp at h1
    | cons b tail =>
      have ha : a = g0 := Option.some.inj h0
      have hb : b = g1 := Option.some.inj h1
      subst a; subst b
      have ht : ∀ g ∈ tail, Good g := fun g hg =>
        ⟨by simpa using (fan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))).1,
         (fan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))).2⟩
      have hz : Dual bank zeroF := ⟨List.mem_append_left _ List.mem_cons_self,
        List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      have availBank : ∀ f ∈ orig, Dual bank f := by
        intro f hf; rcases List.mem_append.mp hf with hr | hs
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr; exact dualIncl (List.subset_append_left ..) (lit i)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · exact ⟨List.mem_append_right _ List.mem_cons_self,
              List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
          · exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
              List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
      have h := compile tail o orig bank ht hz availBank
      have eq : (tail.foldl extend orig).getD o zeroF = Alt.perm := by
        have inputs : ∀ x : Fin 9 → Bool, orig.map (fun f => f x) = scalar (scalar (List.ofFn x) g0) g1 := by
          decide +kernel
        funext x; rw [← readMap, foldMap, inputs]; exact rep x
      rw [eq] at h
      have z' : Dual (@start 8) zeroF := ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      have base : ∀ f ∈ bank, Pin.Has start (f ∘ plug) := by
        apply each (P := fun f => Pin.Has start (f ∘ plug)) z' (fun _ hf => dualNeg hf)
        · intro i; fin_cases i
          · change Dual start ((fun x : Fin 9 → Bool => x 0) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 0) ∘ plug) = neg (@zeroF 8) by funext x; revert x; decide +kernel]; exact dualNeg z'
          · change Dual start ((fun x : Fin 9 → Bool => x 1) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 1) ∘ plug) = (fun x : Fin 8 → Bool => x 0) by funext x; revert x; decide +kernel]; exact lit 0
          · change Dual start ((fun x : Fin 9 → Bool => x 2) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 2) ∘ plug) = (fun x : Fin 8 → Bool => x 1) by funext x; revert x; decide +kernel]; exact lit 1
          · change Dual start ((fun x : Fin 9 → Bool => x 3) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 3) ∘ plug) = (fun x : Fin 8 → Bool => x 2) by funext x; revert x; decide +kernel]; exact lit 2
          · change Dual start ((fun x : Fin 9 → Bool => x 4) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 4) ∘ plug) = (fun x : Fin 8 → Bool => x 3) by funext x; revert x; decide +kernel]; exact lit 3
          · change Dual start ((fun x : Fin 9 → Bool => x 5) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 5) ∘ plug) = (fun x : Fin 8 → Bool => x 4) by funext x; revert x; decide +kernel]; exact lit 4
          · change Dual start ((fun x : Fin 9 → Bool => x 6) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 6) ∘ plug) = (fun x : Fin 8 → Bool => x 5) by funext x; revert x; decide +kernel]; exact lit 5
          · change Dual start ((fun x : Fin 9 → Bool => x 7) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 7) ∘ plug) = (fun x : Fin 8 → Bool => x 6) by funext x; revert x; decide +kernel]; exact lit 6
          · change Dual start ((fun x : Fin 9 → Bool => x 8) ∘ plug); rw [show ((fun x : Fin 9 → Bool => x 8) ∘ plug) = (fun x : Fin 8 → Bool => x 7) by funext x; revert x; decide +kernel]; exact lit 7
        · change Dual start (f0 ∘ plug)
          rw [show f0 ∘ plug = neg (@zeroF 8) by funext x; revert x; decide +kernel]
          exact dualNeg z'
        · change Dual start (f1 ∘ plug)
          rw [show f1 ∘ plug = fun _ => false by funext x; revert x; decide +kernel]
          exact z'
      have bound := cost_le tail; change tail.length + 1 + 1 ≤ 12 at sz
      have dep : ¬stab Alt.perm := by
        intro h; exact absurd (h (fun j : Fin 8 => j.val == 3 || j.val == 7)) (by decide)
      have nc : ¬Pin.Const (Alt.perm ∘ plug) := by
        rintro ⟨c, hc⟩
        have h0 : (Alt.perm ∘ plug) (fun _ => false) = false := by decide
        have h1 : (Alt.perm ∘ plug) (fun j : Fin 8 => j.val == 3 || j.val == 7) = true := by decide
        rw [hc] at h0 h1; exact Bool.false_ne_true (h0.symm.trans h1)
      have all : ∀ f ∈ bank, stab f ∨ Pin.Const (f ∘ plug) := by
        apply each (P := fun f => stab f ∨ Pin.Const (f ∘ plug))
        · exact Or.inl fun _ => rfl
        · intro f hf; rcases hf with h | ⟨c, h⟩
          · exact Or.inl fun x => congrArg Bool.not (h x)
          · exact Or.inr ⟨!c, fun x => congrArg Bool.not (h x)⟩
        · intro i; fin_cases i
          · exact Or.inr ⟨true, by intro x; revert x; decide +kernel⟩
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
          · exact Or.inl (by intro x; revert x; decide +kernel)
        · exact Or.inr ⟨true, by intro x; revert x; decide +kernel⟩
        · exact Or.inr ⟨false, by intro x; revert x; decide +kernel⟩
      have z : Pin.Both (@start 8) := ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      obtain ⟨l, hl, small⟩ := Pin.save h plug stab
        (fun a b ha hb x => by simp only [Pin.meet, ha x, hb x])
        (fun f hf x => by simp only [Pin.inv, hf x]) dep nc all start z base
      exact Pin.weaken small (by omega)
end Prefix

end PEqualNP.Outside.L_meta_27661_aux

open PEqualNP.Outside.L_meta_27661_aux in
theorem PEqualNP.Outside.L_meta_27661 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩) := by
  rintro ⟨C, fan, sz, rep, _, _, _, _, h0, h1⟩
  have h := Prefix.pinPrefix C fan sz rep h0 h1
  have := Alt.lower h
  omega
