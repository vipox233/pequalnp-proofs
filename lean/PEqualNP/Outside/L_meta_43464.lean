import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43464

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

abbrev W := BitVec 192

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 96 := ((x >>> 96) ^^^ x).setWidth 96
def cuts (ws : List W) : BitVec 96 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 96) ++ (0 : BitVec 96)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem take_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem take_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := take_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := take_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 96) (w : W) : Prop :=
  w.getLsbD (96+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 96) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 96+i.val < 192 := by omega
  have hi' : i.val < 192 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 96) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 96)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keeps (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem kept_of_set {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keeps a b r, kept.Nodup ∧ kept.toFinset = needed := by
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
  · refine ⟨a :: b :: r, by simp [keeps], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keeps], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keeps], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keeps], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem single_of_set {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

noncomputable section Kern

def maskW : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffff
def maskC : ℕ := 0xffffffffffffffffffffffff
def powC : ℕ := 0x1000000000000000000000000
def goalN : ℕ := 0xffffffffffffffffffffffff000000000000000000000000

def sepN (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 96) x) powC

def cutsN (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (sepN w) ih) ws

def lenN (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def atGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (Bool.rec (Nat.beq w maskC) true (Nat.beq w goalN)) (fun _ _ _ => false) t) ws

def force (w : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k Nat.zero) (fun m _ => k (Nat.succ m)) w

def revC (xs : List ℕ) (acc : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc) (fun x _ ih acc => ih (x :: acc))
    xs acc

def insC (w : ℕ) (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [w])
    (fun x xs ih k => Bool.rec (ih (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x)) l k

def callC (next : List ℕ → Bool) (c : List ℕ) : Bool := Bool.rec false true (next c)

def orC (x y : Bool) : Bool := Bool.rec y true x

def tryT (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (force w (fun w2 => revC mid post (fun m => revC pre m (fun r =>
      insC w2 r (fun c => callC next c)))))
    (Nat.beq (Nat.lor (sepN w) base) maskC)

def pairT (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orC (tryT next base pre mid post (Nat.land a b))
  (orC (tryT next base pre mid post (Nat.lor a b))
  (orC (tryT next base pre mid post (Nat.land a (Nat.sub maskW b)))
    (tryT next base pre mid post (Nat.land b (Nat.sub maskW a)))))

def rebuild (pre mid post : List ℕ) (k : List ℕ → Bool) : Bool :=
  revC mid post (fun m => revC pre m k)

def tryL (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    Bool :=
  force w (fun w2 =>
    orC (Bool.rec false (rebuild pre mid post (fun r => insC w2 r (fun c => callC next c)))
      (Nat.beq (Nat.lor (sepN w2) base) maskC))
    (orC (Bool.rec false
        (rebuild pre mid post (fun r => insC a r (fun r1 => insC w2 r1 (fun c => callC next c))))
      (Nat.beq (Nat.lor (Nat.lor (sepN w2) base) sa) maskC))
    (orC (Bool.rec false
        (rebuild pre mid post (fun r => insC b r (fun r1 => insC w2 r1 (fun c => callC next c))))
      (Nat.beq (Nat.lor (Nat.lor (sepN w2) base) sb) maskC))
      (Bool.rec false
        (rebuild pre mid post (fun r =>
          insC b r (fun r1 => insC a r1 (fun r2 => insC w2 r2 (fun c => callC next c)))))
        (Nat.ble 2 extra)))))

def pairL (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orC (tryL next extra a b sa sb base pre mid post (Nat.land a b))
  (orC (tryL next extra a b sa sb base pre mid post (Nat.lor a b))
  (orC (tryL next extra a b sa sb base pre mid post (Nat.land a (Nat.sub maskW b)))
    (tryL next extra a b sa sb base pre mid post (Nat.land b (Nat.sub maskW a)))))

def scanIn (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a sa : ℕ)
    (pre : List ℕ) (preCut : ℕ) (rest mid : List ℕ) (midCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun b post ih mid midCut =>
      Bool.rec (ih (b :: mid) (Nat.lor midCut (sepN b))) true
        (P a b sa (sepN b) (Nat.lor (Nat.lor preCut midCut) (cutsN post)) pre mid post))
    rest mid midCut

def scanOut (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws pre : List ℕ)
    (preCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun a rest ih pre preCut =>
      Bool.rec (ih (a :: pre) (Nat.lor preCut (sepN a))) true
        (scanIn P a (sepN a) pre preCut rest [] 0))
    ws pre preCut

def stepS (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec (scanOut (pairL next (Nat.sub (Nat.succ (Nat.succ k1)) (lenN ws))) ws [] 0)
      (scanOut (pairT next) ws [] 0) (Nat.beq (lenN ws) (Nat.succ (Nat.succ k1))))
    true (atGoal ws)

def refS (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => atGoal ws)
    (fun k1 ih ws => stepS k1 ih ws) k ws

def insN (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: insN w xs

def cutsR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (sepN x)) 0

def baseS (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutsR pre) (cutsR mid)) (cutsN post)

def restS (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)

def opsS (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.sub maskW b), Nat.land b (Nat.sub maskW a)]

abbrev Cut5 := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def splitsIn (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Cut5
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: splitsIn pre a post (b :: mid)

def splitsOut : List ℕ → List ℕ → List Cut5
  | [], _ => []
  | a :: rest, pre => splitsIn pre a rest [] ++ splitsOut rest (a :: pre)

def nextT (base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if Nat.beq (Nat.lor (sepN w) base) maskC = true then [insN w r] else []

def nextL (extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if Nat.beq (Nat.lor (sepN w) base) maskC = true then [insN w r] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (sepN w) base) sa) maskC = true then [insN w (insN a r)] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (sepN w) base) sb) maskC = true then [insN w (insN b r)] else []) ++
   (if Nat.ble 2 extra = true then [insN w (insN a (insN b r))] else [])))

def nextPT (t : Cut5) : List (List ℕ) :=
  (opsS t.2.1 t.2.2.2.1).flatMap (nextT (baseS t.1 t.2.2.1 t.2.2.2.2) (restS t.1 t.2.2.1 t.2.2.2.2))

def nextPL (extra : ℕ) (t : Cut5) : List (List ℕ) :=
  (opsS t.2.1 t.2.2.2.1).flatMap
    (nextL extra t.2.1 t.2.2.2.1 (sepN t.2.1) (sepN t.2.2.2.1) (baseS t.1 t.2.2.1 t.2.2.2.2)
      (restS t.1 t.2.2.1 t.2.2.2.2))

def nextAll (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (lenN ws) (Nat.succ (Nat.succ k1)) = true then (splitsOut ws []).flatMap nextPT
  else (splitsOut ws []).flatMap (nextPL (Nat.sub (Nat.succ (Nat.succ k1)) (lenN ws)))

theorem brec_eq {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

theorem force_eq (w : ℕ) (k : ℕ → Bool) : force w k = k w := by
  cases w <;> rfl

theorem revC_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revC xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revC (x :: xs) acc k = revC xs (x :: acc) k := rfl
    rw [e, ih]
    simp

theorem insC_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insC w l k = k (insN w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insC w (x :: xs) k =
        Bool.rec (insC w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec_eq, ih]
    by_cases h : Nat.ble w x = true <;> simp [insN, h]

theorem callC_eq (next : List ℕ → Bool) (c : List ℕ) : callC next c = next c := by
  unfold callC
  cases next c <;> rfl

theorem orC_eq (x y : Bool) : orC x y = (x || y) := by
  cases x <;> rfl

theorem tryT_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    tryT next base pre mid post w = (nextT base (restS pre mid post) w).any next := by
  unfold tryT nextT restS
  rw [brec_eq]
  generalize Nat.beq (Nat.lor (sepN w) base) maskC = c
  cases c <;> simp [force_eq, revC_eq, insC_eq, callC_eq]

theorem tryL_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ)
    (w : ℕ) :
    tryL next extra a b sa sb base pre mid post w =
      (nextL extra a b sa sb base (restS pre mid post) w).any next := by
  unfold tryL nextL restS rebuild
  simp only [force_eq, revC_eq, insC_eq, callC_eq, orC_eq, brec_eq, List.any_append]
  generalize Nat.beq (Nat.lor (sepN w) base) maskC = c1
  generalize Nat.beq (Nat.lor (Nat.lor (sepN w) base) sa) maskC = c2
  generalize Nat.beq (Nat.lor (Nat.lor (sepN w) base) sb) maskC = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

theorem pairT_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairT next a b sa sb base pre mid post =
      ((opsS a b).flatMap (nextT base (restS pre mid post))).any next := by
  unfold pairT opsS
  simp only [orC_eq, tryT_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

theorem pairL_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairL next extra a b sa sb base pre mid post =
      ((opsS a b).flatMap (nextL extra a b sa sb base (restS pre mid post))).any next := by
  unfold pairL opsS
  simp only [orC_eq, tryL_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

def hp5 (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Cut5) : Bool :=
  P t.2.1 t.2.2.2.1 (sepN t.2.1) (sepN t.2.2.2.1) (baseS t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

theorem scanIn_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a : ℕ)
    (pre : List ℕ) : ∀ rest mid : List ℕ,
    scanIn P a (sepN a) pre (cutsR pre) rest mid (cutsR mid) =
      (splitsIn pre a rest mid).any (hp5 P) := by
  intro rest
  induction rest with
  | nil => intro mid; rfl
  | cons b post ih =>
    intro mid
    have e : scanIn P a (sepN a) pre (cutsR pre) (b :: post) mid (cutsR mid) =
        Bool.rec (scanIn P a (sepN a) pre (cutsR pre) post (b :: mid)
            (Nat.lor (cutsR mid) (sepN b)))
          true (P a b (sepN a) (sepN b) (Nat.lor (Nat.lor (cutsR pre) (cutsR mid)) (cutsN post))
            pre mid post) := rfl
    have c : Nat.lor (cutsR mid) (sepN b) = cutsR (b :: mid) := rfl
    rw [e, brec_eq, c, ih]
    simp only [splitsIn, List.any_cons, hp5, baseS]
    cases P a b (sepN a) (sepN b) (Nat.lor (Nat.lor (cutsR pre) (cutsR mid)) (cutsN post))
      pre mid post <;> simp

theorem scanOut_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ ws pre : List ℕ, scanOut P ws pre (cutsR pre) = (splitsOut ws pre).any (hp5 P) := by
  intro ws
  induction ws with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have e : scanOut P (a :: rest) pre (cutsR pre) =
        Bool.rec (scanOut P rest (a :: pre) (Nat.lor (cutsR pre) (sepN a))) true
          (scanIn P a (sepN a) pre (cutsR pre) rest [] 0) := rfl
    have c : Nat.lor (cutsR pre) (sepN a) = cutsR (a :: pre) := rfl
    have z : (0 : ℕ) = cutsR [] := rfl
    rw [e, brec_eq, c, ih, z, scanIn_eq]
    simp only [splitsOut, List.any_append]
    cases (splitsIn pre a rest []).any (hp5 P) <;> simp

theorem hp5_T (next : List ℕ → Bool) :
    hp5 (pairT next) = fun t => (nextPT t).any next := by
  funext t
  simp only [hp5, pairT_eq, nextPT]

theorem hp5_L (next : List ℕ → Bool) (extra : ℕ) :
    hp5 (pairL next extra) = fun t => (nextPL extra t).any next := by
  funext t
  simp only [hp5, pairL_eq, nextPL]

theorem stepS_eq (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    stepS k1 next ws = (atGoal ws || (nextAll k1 ws).any next) := by
  have z : (0 : ℕ) = cutsR [] := rfl
  unfold stepS nextAll
  rw [brec_eq, brec_eq, z, scanOut_eq, scanOut_eq, hp5_T, hp5_L]
  cases atGoal ws
  · cases Nat.beq (lenN ws) (Nat.succ (Nat.succ k1)) <;> simp [List.any_flatMap]
  · simp

theorem refS_zero (ws : List ℕ) : refS 0 ws = atGoal ws := rfl

theorem refS_succ (k : ℕ) (ws : List ℕ) :
    refS (k + 1) ws = (atGoal ws || (nextAll k ws).any (refS k)) := by
  rw [← stepS_eq]
  rfl

end Kern

noncomputable section Link

theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem allOnesC : (-1 : BitVec 96).toNat = maskC := by decide

theorem sepN_toNat (w : W) : sepN w.toNat = (sep w).toNat := by
  simp only [sepN, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

theorem cutsN_cons (w : ℕ) (ws : List ℕ) : cutsN (w :: ws) = Nat.lor (sepN w) (cutsN ws) := rfl

theorem cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

theorem cutsN_map (l : List W) : cutsN (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, cutsN_cons, cuts_cons, BitVec.toNat_or, ih, sepN_toNat]
    rfl

theorem cutsN_append (l1 l2 : List ℕ) : cutsN (l1 ++ l2) = Nat.lor (cutsN l1) (cutsN l2) := by
  induction l1 with
  | nil =>
    have e : cutsN ([] : List ℕ) = 0 := rfl
    rw [List.nil_append, e]
    exact (Nat.zero_or _).symm
  | cons a l ih =>
    rw [List.cons_append, cutsN_cons, ih, cutsN_cons]
    exact (Nat.or_assoc _ _ _).symm

theorem cutsR_eq (l : List ℕ) : cutsR l = cutsN l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutsR (a :: l) = Nat.lor (cutsR l) (sepN a) := rfl
    rw [e, ih, cutsN_cons]
    exact Nat.or_comm _ _

theorem cutsN_reverse (l : List ℕ) : cutsN l.reverse = cutsN l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : cutsN [a] = sepN a ||| 0 := rfl
    have e2 : cutsN (a :: l) = sepN a ||| cutsN l := rfl
    rw [List.reverse_cons, cutsN_append, ih, e1, e2]
    change (cutsN l ||| (sepN a ||| 0)) = (sepN a ||| cutsN l)
    rw [Nat.or_zero, Nat.or_comm]

theorem baseS_map (xs ys zs : List W) :
    baseS (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← cutsN_map, List.map_append, List.map_append, cutsN_append, cutsN_append]
  unfold baseS
  rw [cutsR_eq, cutsR_eq, cutsN_reverse, cutsN_reverse]
  exact Nat.or_assoc _ _ _

theorem opsS_map (a b : W) : opsS a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsS, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_not]
  rfl

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : lenN (a :: l) = Nat.succ (lenN l) := rfl
    rw [e, ih]
    rfl

def insWd (w : W) : List W → List W
  | [] => [w]
  | x :: xs => if Nat.ble w.toNat x.toNat = true then w :: x :: xs else x :: insWd w xs

theorem insWd_map (w : W) (l : List W) :
    (insWd w l).map BitVec.toNat = insN w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insWd, insN, List.map_cons]
    split_ifs
    · rfl
    · rw [List.map_cons, ih]

theorem insWd_perm (w : W) (l : List W) : (insWd w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insWd]
    split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem mem_splitsIn (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ splitsIn pre a (ys ++ b :: zs) mid := by
  intro ys
  induction ys with
  | nil => intro mid; simp [splitsIn]
  | cons y ys ih =>
    intro mid
    simp only [List.cons_append, splitsIn, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

theorem mem_splitsOut (a b : ℕ) (ys zs : List ℕ) : ∀ xs pre : List ℕ,
    (xs.reverse ++ pre, a, ys.reverse, b, zs) ∈ splitsOut (xs ++ a :: (ys ++ b :: zs)) pre := by
  intro xs
  induction xs with
  | nil =>
    intro pre
    simp only [List.nil_append, List.reverse_nil, splitsOut]
    exact List.mem_append_left _ (by simpa using mem_splitsIn pre a b zs ys [])
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, splitsOut, List.reverse_cons, List.append_assoc]
    exact List.mem_append_right _ (ih (x :: pre))

theorem cut_pair {α : Type} {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (∃ xs ys zs, l = xs ++ a :: (ys ++ b :: zs)) ∨ (∃ xs ys zs, l = xs ++ b :: (ys ++ a :: zs)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h
    exact .inr ⟨s1, s2, t, by simp⟩
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem h
      exact .inl ⟨s, t1, t2, rfl⟩

theorem atGoal_goal {g : W} (hg : g = goal ∨ g = ~~~goal) : atGoal [g.toNat] = true := by
  rcases hg with rfl | rfl <;> decide +kernel

theorem mem_nextT {base w : ℕ} {r : List ℕ} (h : Nat.beq (Nat.lor (sepN w) base) maskC = true) :
    insN w r ∈ nextT base r w := by
  unfold nextT
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_nextL1 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (sepN w) base) maskC = true) :
    insN w r ∈ nextL extra a b sa sb base r w := by
  unfold nextL
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_nextL2 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (sepN w) base) sa) maskC = true) :
    insN w (insN a r) ∈ nextL extra a b sa sb base r w := by
  unfold nextL
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_nextL3 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (sepN w) base) sb) maskC = true) :
    insN w (insN b r) ∈ nextL extra a b sa sb base r w := by
  unfold nextL
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_nextL4 {extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    insN w (insN a (insN b r)) ∈ nextL extra a b sa sb base r w := by
  unfold nextL
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_nextAll {k : ℕ} {wsN : List ℕ} {t : Cut5} {w : ℕ} {c : List ℕ}
    (ht : t ∈ splitsOut wsN []) (hw : w ∈ opsS t.2.1 t.2.2.2.1)
    (h0 : Nat.beq (lenN wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ nextT (baseS t.1 t.2.2.1 t.2.2.2.2) (restS t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (lenN wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ nextL (Nat.sub (Nat.succ (Nat.succ k)) (lenN wsN)) t.2.1 t.2.2.2.1 (sepN t.2.1)
        (sepN t.2.2.2.1) (baseS t.1 t.2.2.1 t.2.2.2.2) (restS t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ nextAll k wsN := by
  unfold nextAll
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, hG hd⟩⟩

theorem full_one {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (sepN z.toNat) (cuts r).toNat) maskC = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← sepN_toNat, allOnesC] at e
  exact beq_true e

theorem full_two {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (sepN z.toNat) (cuts r).toNat) (sepN a.toNat)) maskC = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← sepN_toNat, ← sepN_toNat, allOnesC] at e
  refine beq_true (Eq.trans ?_ e)
  change (sepN z.toNat ||| (cuts r).toNat ||| sepN a.toNat) =
    (sepN z.toNat ||| (sepN a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

theorem succ_of_cut {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ nextAll k (ws.map BitVec.toNat) := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := kept_of_set perm hn hs
  have hznew : z ∉ kept := by
    intro hu
    apply hout
    rw [hs]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl2 : live basicOps g k (z :: kept).toFinset := by
    simpa [hfin] using tail
  have hc := live_card hl2
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have hcut := cuts_full hg hl2
  have hlen2 := perm.length_eq
  simp only [List.length_cons] at hlen2
  have hmap : ws.map BitVec.toNat = xs.map BitVec.toNat ++
      a.toNat :: (ys.map BitVec.toNat ++ b.toNat :: zs.map BitVec.toNat) := by
    rw [hsplit]
    simp
  have ht := mem_splitsOut a.toNat b.toNat (ys.map BitVec.toNat) (zs.map BitVec.toNat)
    (xs.map BitVec.toNat) []
  rw [List.append_nil, ← hmap] at ht
  have hzN : z.toNat ∈ opsS a.toNat b.toNat := by
    rw [opsS_map]
    exact List.mem_map_of_mem (List.mem_toFinset.mp hz)
  have hr : restS (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse
      (zs.map BitVec.toNat) = (xs ++ (ys ++ zs)).map BitVec.toNat := by
    simp [restS]
  have hbase := baseS_map xs ys zs
  have hlenN : lenN (ws.map BitVec.toNat) = ws.length := by
    rw [lenN_eq, List.length_map]
  have live_of (cW : List W) (hp : cW.Perm (z :: kept)) :
      cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset := by
    refine ⟨hp.nodup_iff.mpr hnd, ?_, ?_⟩
    · rw [hp.length_eq, List.length_cons]
      exact hc
    · have e : cW.toFinset = (z :: kept).toFinset := List.toFinset_eq_of_perm _ _ hp
      rw [e]
      exact hl2
  simp only [keeps, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insWd z (xs ++ (ys ++ zs)), (live_of _ (insWd_perm _ _)).1, (live_of _ (insWd_perm _ _)).2.1,
      (live_of _ (insWd_perm _ _)).2.2, ?_⟩
    rw [insWd_map]
    refine mem_nextAll ht hzN ?_ ?_
    · intro _
      simp only [hr, hbase]
      exact mem_nextT (full_one hcut)
    · intro _
      simp only [hr, hbase]
      exact mem_nextL1 (full_one hcut)
  · have hp : (insWd z (insWd a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insWd_perm _ _).trans ((insWd_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insWd_map, insWd_map]
    refine mem_nextAll ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_nextL2 (full_two hcut)
  · have hp : (insWd z (insWd b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insWd_perm _ _).trans ((insWd_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insWd_map, insWd_map]
    refine mem_nextAll ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_nextL3 (full_two hcut)
  · have hp : (insWd z (insWd a (insWd b (xs ++ (ys ++ zs))))).Perm
        (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insWd_perm _ _).trans (((insWd_perm _ _).trans ((insWd_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insWd_map, insWd_map, insWd_map]
    simp only [List.length_cons] at hc
    refine mem_nextAll ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      omega
    · intro _
      simp only [hr]
      refine mem_nextL4 ?_
      rw [hlenN]
      apply Nat.ble_eq_true_of_le
      change 2 ≤ k + 2 - ws.length
      omega

theorem succ_exists {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (hl : live basicOps g (k + 1) ws.toFinset) :
    ws = [g] ∨ ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ nextAll k (ws.map BitVec.toNat) := by
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (single_of_set hn done)
  · right
    rcases cut_pair (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
      ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
    · exact succ_of_cut hg hn e hz hout hs tail
    · exact succ_of_cut hg hn e (ops_swap a b ▸ hz) hout
        (by rw [hs, Finset.insert_comm]) tail

theorem refS_complete {g : W} (hg : g = goal ∨ g = ~~~goal) : ∀ (k : ℕ) (ws : List W),
    ws.Nodup → live basicOps g k ws.toFinset → refS k (ws.map BitVec.toNat) = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    have e := single_of_set hn h
    rw [e]
    exact atGoal_goal hg
  | succ k ih =>
    intro ws hn hl
    rw [refS_succ]
    rcases succ_exists hg hn hl with e | ⟨cW, hcn, _, hcl, hmem⟩
    · rw [e]
      have := atGoal_goal hg
      simp only [List.map_cons, List.map_nil, this, Bool.true_or]
    · have := ih cW hcn hcl
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)

def seeds (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (cutsN ws) maskC)

def frontier (m : ℕ) (insN : List ℕ) : List (List ℕ) := (seeds (m + 1) insN).flatMap (nextAll m)

def sortN (l : List ℕ) : List ℕ := l.foldr insN []

def sortC (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => force x (fun x2 => insC x2 s k))) l k

theorem sortC_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortC l k = k (sortN l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortC (x :: xs) k = sortC xs (fun s => force x (fun x2 => insC x2 s k)) := rfl
    rw [e, ih, force_eq, insC_eq]
    rfl

def sortW (l : List W) : List W := l.foldr insWd []

theorem sortW_map (l : List W) :
    (sortW l).map BitVec.toNat = sortN (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : sortW (x :: xs) = insWd x (sortW xs) := rfl
    have e2 : sortN (x.toNat :: xs.map BitVec.toNat) =
        insN x.toNat (sortN (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insWd_map, ih]

theorem sortW_perm (l : List W) : (sortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insWd_perm x (sortW xs)).trans (ih.cons x)

def shut (m : ℕ) (c : List ℕ) : Bool := sortC c (fun c2 => Bool.rec true false (refS m c2))

theorem shut_eq (m : ℕ) (c : List ℕ) : shut m c = !refS m (sortN c) := by
  unfold shut
  rw [sortC_eq, brec_eq]
  cases refS m (sortN c) <;> rfl

theorem no_build (m : ℕ) (rowsW : List W) (hnd : rowsW.Nodup)
    (h0 : (seeds (m + 1) (rowsW.map BitVec.toNat)).all (fun ws => !atGoal ws) = true)
    (hk : (frontier m (rowsW.map BitVec.toNat)).all (shut m) = true) :
    ∀ t, t = goal ∨ t = ~~~goal → build basicOps t (m + 1) rowsW.toFinset → False := by
  intro g hg hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := rowsW.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd2 : ws.Nodup := hnd.filter _
  have hl2 : live basicOps g (m + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl2
  rw [List.toFinset_card_of_nodup hnd2] at sz
  have hroot : ws.map BitVec.toNat ∈ seeds (m + 1) (rowsW.map BitVec.toNat) := by
    unfold seeds
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr ((List.filter_sublist).map _), ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply Nat.ble_eq_true_of_le
      rw [List.length_map]
      exact sz
    · rw [cutsN_map, cuts_full hg hl2, allOnesC]
      exact Nat.beq_refl _
  rcases succ_exists hg hnd2 hl2 with e | ⟨cW, hcn, _, hcl, hmem⟩
  · have h1 := List.all_eq_true.mp h0 _ hroot
    rw [e] at h1
    have h2 := atGoal_goal hg
    simp only [List.map_cons, List.map_nil, h2] at h1
    exact absurd h1 (by decide)
  · have hd := List.all_eq_true.mp hk _ (List.mem_flatMap.mpr ⟨_, hroot, hmem⟩)
    have hp := sortW_perm cW
    have e : (sortW cW).toFinset = cW.toFinset := List.toFinset_eq_of_perm _ _ hp
    have run := refS_complete hg m (sortW cW) (hp.nodup_iff.mpr hcn) (e ▸ hcl)
    rw [sortW_map] at run
    rw [shut_eq, run] at hd
    exact absurd hd (by decide)

theorem all_split {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

end Link
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 192 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 192)
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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 192) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 192) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 192) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#192)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have lenN : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [lenN]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def rowsW : List W := [0x5a72e5a72fffdd5756ee524700000007fff70c0702ee0007, 0x755b2354ab99b731cde3ce89e07f00000388b330cde1ce00, 0xec91b6ca64fa78f23c3fc5d2e000fe00007870f03c1fc1c0, 0x3ff7ee391d27f00ffe44bfe41ffffe000007f00ffc003fc0, 0xe38f1ffefe400ffffd99293f000001fffc000ffffc00003f, 0xffbf7ff9fc0422acabfffffffffffffffc00000003ffffff]

def negRows : List W := rowsW.map (fun w => ~~~w)

def tfun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808426 * 2 ^ 32 + 4272472064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_ok : ∀ j : Fin 192,
    tfun (fun i => (negRows.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

theorem lower_of_none (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n rowsW.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tfun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ negRows, holds rowsW.toFinset u := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    exact .inr (.inr ⟨w, List.mem_toFinset.mpr hw, .inr rfl⟩)
  have evaluate (k : Fin 192) :
      (gs.foldl step (negRows.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (negRows.getD i.val 0)
    have width : negRows.length = 6 := rfl
    have same : List.ofFn x = negRows.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < negRows.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (negRows.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact rows_ok k
  obtain ⟨t,ht,run⟩ := compile gs o hg negRows rowsW.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a rowsW.toFinset) :
      build basicOps t b rowsW.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)


set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seeds_ok :
    (seeds (8 + 1) (rowsW.map BitVec.toNat)).all (fun ws => !atGoal ws) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg0 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 0).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg1 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 1).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg2 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 2).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg3 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 3).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg4 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 4).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg5 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 5).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg6 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 6).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg7 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 7).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg8 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 8).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg9 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 9).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg10 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 10).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg11 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 11).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg12 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 12).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg13 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 13).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg14 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 14).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg15 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 15).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg16 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 16).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg17 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 17).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg18 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 18).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg19 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 19).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg20 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 20).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg21 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 21).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg22 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 22).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg23 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 23).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg24 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 24).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg25 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 25).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg26 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 26).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg27 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 27).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg28 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 28).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg29 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 29).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg30 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 30).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg31 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 31).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg32 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 32).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg33 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 33).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg34 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 34).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg35 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 35).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg36 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 36).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg37 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 37).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg38 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 38).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg39 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 39).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg40 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 40).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg41 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 41).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg42 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 42).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg43 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 43).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg44 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 44).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg45 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 45).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg46 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 46).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg47 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 47).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg48 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 48).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg49 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 49).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg50 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 50).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg51 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 51).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg52 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 52).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg53 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 53).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg54 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 54).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg55 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 55).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg56 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 56).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg57 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 57).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg58 :
    (((frontier 8 (rowsW.map BitVec.toNat)).drop 58).take 1).all (shut 8) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem seg59 :
    ((frontier 8 (rowsW.map BitVec.toNat)).drop 59).all (shut 8) = true := by
  decide +kernel

theorem front_ok : (frontier 8 (rowsW.map BitVec.toNat)).all (shut 8) = true :=
  (all_split _ _ 0 1 seg0 (all_split _ _ 1 1 seg1 (all_split _ _ 2 1 seg2 (all_split _ _ 3 1 seg3 (all_split _ _ 4 1 seg4 (all_split _ _ 5 1 seg5 (all_split _ _ 6 1 seg6 (all_split _ _ 7 1 seg7 (all_split _ _ 8 1 seg8 (all_split _ _ 9 1 seg9 (all_split _ _ 10 1 seg10 (all_split _ _ 11 1 seg11 (all_split _ _ 12 1 seg12 (all_split _ _ 13 1 seg13 (all_split _ _ 14 1 seg14 (all_split _ _ 15 1 seg15 (all_split _ _ 16 1 seg16 (all_split _ _ 17 1 seg17 (all_split _ _ 18 1 seg18 (all_split _ _ 19 1 seg19 (all_split _ _ 20 1 seg20 (all_split _ _ 21 1 seg21 (all_split _ _ 22 1 seg22 (all_split _ _ 23 1 seg23 (all_split _ _ 24 1 seg24 (all_split _ _ 25 1 seg25 (all_split _ _ 26 1 seg26 (all_split _ _ 27 1 seg27 (all_split _ _ 28 1 seg28 (all_split _ _ 29 1 seg29 (all_split _ _ 30 1 seg30 (all_split _ _ 31 1 seg31 (all_split _ _ 32 1 seg32 (all_split _ _ 33 1 seg33 (all_split _ _ 34 1 seg34 (all_split _ _ 35 1 seg35 (all_split _ _ 36 1 seg36 (all_split _ _ 37 1 seg37 (all_split _ _ 38 1 seg38 (all_split _ _ 39 1 seg39 (all_split _ _ 40 1 seg40 (all_split _ _ 41 1 seg41 (all_split _ _ 42 1 seg42 (all_split _ _ 43 1 seg43 (all_split _ _ 44 1 seg44 (all_split _ _ 45 1 seg45 (all_split _ _ 46 1 seg46 (all_split _ _ 47 1 seg47 (all_split _ _ 48 1 seg48 (all_split _ _ 49 1 seg49 (all_split _ _ 50 1 seg50 (all_split _ _ 51 1 seg51 (all_split _ _ 52 1 seg52 (all_split _ _ 53 1 seg53 (all_split _ _ 54 1 seg54 (all_split _ _ 55 1 seg55 (all_split _ _ 56 1 seg56 (all_split _ _ 57 1 seg57 (all_split _ _ 58 1 seg58 seg59)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem none_at (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 9 rowsW.toFinset) : False :=
  no_build 8 rowsW (by decide) seeds_ok front_ok t ht run

def wg : List Gate :=
  [⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [14, 15]⟩]

def wo : ℕ := 16

theorem wg_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wg, wo⟩ := by simp [Monotone2, wg]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem wg_eval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wo⟩ (List.ofFn x) = tfun x := by
  decide +kernel

end PEqualNP.Outside.L_meta_43464

theorem PEqualNP.Outside.L_meta_43464 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272472064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272472064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C, hfan, hsz, hev⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have fits : ∀ g' ∈ C.gates, PEqualNP.Outside.L_meta_43464.legal g' := fun g' hg' => by
      have h' := hfan g' hg'
      exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h'.1, h'.2⟩
    have short : PEqualNP.Outside.L_meta_43464.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_43464.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_43464.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_43464.lower_of_none
      9 PEqualNP.Outside.L_meta_43464.none_at C.gates C.output fits hev
    have hcsz : C.gates.length ≤ s := hsz
    refine ⟨⟨PEqualNP.Outside.L_meta_43464.wg, PEqualNP.Outside.L_meta_43464.wo⟩, PEqualNP.Outside.L_meta_43464.wg_mono, ?_, PEqualNP.Outside.L_meta_43464.wg_eval⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
    rcases ops with h | h | h
    · exact ⟨Or.inl h, hlen⟩
    · exact ⟨Or.inr h, hlen⟩
    · exact False.elim (hasNot ⟨g, hg, h⟩)
