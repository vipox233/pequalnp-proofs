import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45558_aux

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

set_option maxRecDepth 16000 in
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

set_option maxRecDepth 16000 in
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

set_option maxRecDepth 16000 in
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

set_option maxRecDepth 16000 in
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

abbrev W := BitVec 500

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 250 := ((x >>> 250) ^^^ x).setWidth 250
def cuts (ws : List W) : BitVec 250 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 250) ++ (0 : BitVec 250)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 16000 in
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

set_option maxRecDepth 16000 in
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

def differs (i : Fin 250) (w : W) : Prop :=
  w.getLsbD (250+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 16000 in
theorem ops_differs (i : Fin 250) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 250+i.val < 500 := by omega
  have hi' : i.val < 500 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 16000 in
theorem cuts_spec (ws : List W) (i : Fin 250) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 16000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 250)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 16000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 16000 in
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

set_option maxRecDepth 16000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

noncomputable section Fast

def M120 : ℕ := ((((((((0xfffff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff)
def M60 : ℕ := ((((0x3ff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff)
def P60 : ℕ := ((((0x400 * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def gN : ℕ := ((((((((0xfffff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xffffffffffffc00) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)

def nsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 250) x) P60

def ncuts (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (nsep w) ih) ws

def len (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def nisGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (Bool.rec (Nat.beq w M60) true (Nat.beq w gN)) (fun _ _ _ => false) t) ws

def frc (w : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k Nat.zero) (fun m _ => k (Nat.succ m)) w

def revK (xs : List ℕ) (acc : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc) (fun x _ ih acc => ih (x :: acc))
    xs acc

def insK (w : ℕ) (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [w])
    (fun x xs ih k => Bool.rec (ih (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x)) l k

def call (next : List ℕ → Bool) (c : List ℕ) : Bool := Bool.rec false true (next c)

def orB (x y : Bool) : Bool := Bool.rec y true x

def one0 (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
      insK w2 r (fun c => call next c)))))
    (Nat.beq (Nat.lor (nsep w) base) M60)

def pair0 (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (one0 next base pre mid post (Nat.land a b))
  (orB (one0 next base pre mid post (Nat.lor a b))
  (orB (one0 next base pre mid post (Nat.land a (Nat.sub M120 b)))
    (one0 next base pre mid post (Nat.land b (Nat.sub M120 a)))))

def reb (pre mid post : List ℕ) (k : List ℕ → Bool) : Bool :=
  revK mid post (fun m => revK pre m k)

def oneG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    Bool :=
  frc w (fun w2 =>
    orB (Bool.rec false (reb pre mid post (fun r => insK w2 r (fun c => call next c)))
      (Nat.beq (Nat.lor (nsep w2) base) M60))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK a r (fun r1 => insK w2 r1 (fun c => call next c))))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sa) M60))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK b r (fun r1 => insK w2 r1 (fun c => call next c))))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sb) M60))
      (Bool.rec false
        (reb pre mid post (fun r =>
          insK b r (fun r1 => insK a r1 (fun r2 => insK w2 r2 (fun c => call next c)))))
        (Nat.ble 2 extra)))))

def pairG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (oneG next extra a b sa sb base pre mid post (Nat.land a b))
  (orB (oneG next extra a b sa sb base pre mid post (Nat.lor a b))
  (orB (oneG next extra a b sa sb base pre mid post (Nat.land a (Nat.sub M120 b)))
    (oneG next extra a b sa sb base pre mid post (Nat.land b (Nat.sub M120 a)))))

def innerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a sa : ℕ)
    (pre : List ℕ) (preCut : ℕ) (rest mid : List ℕ) (midCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun b post ih mid midCut =>
      Bool.rec (ih (b :: mid) (Nat.lor midCut (nsep b))) true
        (P a b sa (nsep b) (Nat.lor (Nat.lor preCut midCut) (ncuts post)) pre mid post))
    rest mid midCut

def outerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws pre : List ℕ)
    (preCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun a rest ih pre preCut =>
      Bool.rec (ih (a :: pre) (Nat.lor preCut (nsep a))) true
        (innerAux P a (nsep a) pre preCut rest [] 0))
    ws pre preCut

def stepF (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec (outerAux (pairG next (Nat.sub (Nat.succ (Nat.succ k1)) (len ws))) ws [] 0)
      (outerAux (pair0 next) ws [] 0) (Nat.beq (len ws) (Nat.succ (Nat.succ k1))))
    true (nisGoal ws)

def nopt (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => nisGoal ws)
    (fun k1 ih ws => stepF k1 ih ws) k ws

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: ins w xs

def cutR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (nsep x)) 0

def baseOf (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post)

def rOf (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)

def opsN (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.sub M120 b), Nat.land b (Nat.sub M120 a)]

abbrev Split := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def innerS (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Split
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: innerS pre a post (b :: mid)

def outerS : List ℕ → List ℕ → List Split
  | [], _ => []
  | a :: rest, pre => innerS pre a rest [] ++ outerS rest (a :: pre)

def kids0 (base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if Nat.beq (Nat.lor (nsep w) base) M60 = true then [ins w r] else []

def kidsG (extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if Nat.beq (Nat.lor (nsep w) base) M60 = true then [ins w r] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true then [ins w (ins a r)] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true then [ins w (ins b r)] else []) ++
   (if Nat.ble 2 extra = true then [ins w (ins a (ins b r))] else [])))

def kidsPair0 (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap (kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (extra : ℕ) (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap
    (kidsG extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.succ (Nat.succ k1)) = true then (outerS ws []).flatMap kidsPair0
  else (outerS ws []).flatMap (kidsPairG (Nat.sub (Nat.succ (Nat.succ k1)) (len ws)))

set_option maxRecDepth 16000 in
theorem brec {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

set_option maxRecDepth 16000 in
theorem frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by
  cases w <;> rfl

set_option maxRecDepth 16000 in
theorem revK_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revK xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revK (x :: xs) acc k = revK xs (x :: acc) k := rfl
    rw [e, ih]
    simp

set_option maxRecDepth 16000 in
theorem insK_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insK w l k = k (ins w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insK w (x :: xs) k =
        Bool.rec (insK w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec, ih]
    by_cases h : Nat.ble w x = true <;> simp [ins, h]

set_option maxRecDepth 16000 in
theorem call_eq (next : List ℕ → Bool) (c : List ℕ) : call next c = next c := by
  unfold call
  cases next c <;> rfl

set_option maxRecDepth 16000 in
theorem orB_eq (x y : Bool) : orB x y = (x || y) := by
  cases x <;> rfl

set_option maxRecDepth 16000 in
theorem one0_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 next base pre mid post w = (kids0 base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf
  rw [brec]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

set_option maxRecDepth 16000 in
theorem oneG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ)
    (w : ℕ) :
    oneG next extra a b sa sb base pre mid post w =
      (kidsG extra a b sa sb base (rOf pre mid post) w).any next := by
  unfold oneG kidsG rOf reb
  simp only [frc_eq, revK_eq, insK_eq, call_eq, orB_eq, brec, List.any_append]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c1
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = c2
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

set_option maxRecDepth 16000 in
theorem pair0_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 next a b sa sb base pre mid post =
      ((opsN a b).flatMap (kids0 base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

set_option maxRecDepth 16000 in
theorem pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      ((opsN a b).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  unfold pairG opsN
  simp only [orB_eq, oneG_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

def HP (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Split) : Bool :=
  P t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

set_option maxRecDepth 16000 in
theorem innerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a : ℕ)
    (pre : List ℕ) : ∀ rest mid : List ℕ,
    innerAux P a (nsep a) pre (cutR pre) rest mid (cutR mid) =
      (innerS pre a rest mid).any (HP P) := by
  intro rest
  induction rest with
  | nil => intro mid; rfl
  | cons b post ih =>
    intro mid
    have e : innerAux P a (nsep a) pre (cutR pre) (b :: post) mid (cutR mid) =
        Bool.rec (innerAux P a (nsep a) pre (cutR pre) post (b :: mid)
            (Nat.lor (cutR mid) (nsep b)))
          true (P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
            pre mid post) := rfl
    have c : Nat.lor (cutR mid) (nsep b) = cutR (b :: mid) := rfl
    rw [e, brec, c, ih]
    simp only [innerS, List.any_cons, HP, baseOf]
    cases P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
      pre mid post <;> simp

set_option maxRecDepth 16000 in
theorem outerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ ws pre : List ℕ, outerAux P ws pre (cutR pre) = (outerS ws pre).any (HP P) := by
  intro ws
  induction ws with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have e : outerAux P (a :: rest) pre (cutR pre) =
        Bool.rec (outerAux P rest (a :: pre) (Nat.lor (cutR pre) (nsep a))) true
          (innerAux P a (nsep a) pre (cutR pre) rest [] 0) := rfl
    have c : Nat.lor (cutR pre) (nsep a) = cutR (a :: pre) := rfl
    have z : (0 : ℕ) = cutR [] := rfl
    rw [e, brec, c, ih, z, innerAux_eq]
    simp only [outerS, List.any_append]
    cases (innerS pre a rest []).any (HP P) <;> simp

set_option maxRecDepth 16000 in
theorem HP_pair0 (next : List ℕ → Bool) :
    HP (pair0 next) = fun t => (kidsPair0 t).any next := by
  funext t
  simp only [HP, pair0_eq, kidsPair0]

set_option maxRecDepth 16000 in
theorem HP_pairG (next : List ℕ → Bool) (extra : ℕ) :
    HP (pairG next extra) = fun t => (kidsPairG extra t).any next := by
  funext t
  simp only [HP, pairG_eq, kidsPairG]

set_option maxRecDepth 16000 in
theorem stepF_eq (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    stepF k1 next ws = (nisGoal ws || (kidsL k1 ws).any next) := by
  have z : (0 : ℕ) = cutR [] := rfl
  unfold stepF kidsL
  rw [brec, brec, z, outerAux_eq, outerAux_eq, HP_pair0, HP_pairG]
  cases nisGoal ws
  · cases Nat.beq (len ws) (Nat.succ (Nat.succ k1)) <;> simp [List.any_flatMap]
  · simp

set_option maxRecDepth 16000 in
theorem nopt_zero (ws : List ℕ) : nopt 0 ws = nisGoal ws := rfl

set_option maxRecDepth 16000 in
theorem nopt_succ (k : ℕ) (ws : List ℕ) :
    nopt (k + 1) ws = (nisGoal ws || (kidsL k ws).any (nopt k)) := by
  rw [← stepF_eq]
  rfl

end Fast

noncomputable section Bridge

set_option maxRecDepth 16000 in
theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

set_option maxRecDepth 16000 in
theorem negOne60 : (-1 : BitVec 250).toNat = M60 := by decide +kernel

set_option maxRecDepth 16000 in
theorem nsep_toNat (w : W) : nsep w.toNat = (sep w).toNat := by
  simp only [nsep, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

set_option maxRecDepth 16000 in
theorem ncuts_cons (w : ℕ) (ws : List ℕ) : ncuts (w :: ws) = Nat.lor (nsep w) (ncuts ws) := rfl

set_option maxRecDepth 16000 in
theorem cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

set_option maxRecDepth 16000 in
theorem ncuts_map (l : List W) : ncuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ncuts_cons, cuts_cons, BitVec.toNat_or, ih, nsep_toNat]
    rfl

set_option maxRecDepth 16000 in
theorem ncuts_append (l1 l2 : List ℕ) : ncuts (l1 ++ l2) = Nat.lor (ncuts l1) (ncuts l2) := by
  induction l1 with
  | nil =>
    have e : ncuts ([] : List ℕ) = 0 := rfl
    rw [List.nil_append, e]
    exact (Nat.zero_or _).symm
  | cons a l ih =>
    rw [List.cons_append, ncuts_cons, ih, ncuts_cons]
    exact (Nat.or_assoc _ _ _).symm

set_option maxRecDepth 16000 in
theorem cutR_eq (l : List ℕ) : cutR l = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutR (a :: l) = Nat.lor (cutR l) (nsep a) := rfl
    rw [e, ih, ncuts_cons]
    exact Nat.or_comm _ _

set_option maxRecDepth 16000 in
theorem ncuts_reverse (l : List ℕ) : ncuts l.reverse = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : ncuts [a] = nsep a ||| 0 := rfl
    have e2 : ncuts (a :: l) = nsep a ||| ncuts l := rfl
    rw [List.reverse_cons, ncuts_append, ih, e1, e2]
    change (ncuts l ||| (nsep a ||| 0)) = (nsep a ||| ncuts l)
    rw [Nat.or_zero, Nat.or_comm]

set_option maxRecDepth 16000 in
theorem baseOf_map (xs ys zs : List W) :
    baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← ncuts_map, List.map_append, List.map_append, ncuts_append, ncuts_append]
  unfold baseOf
  rw [cutR_eq, cutR_eq, ncuts_reverse, ncuts_reverse]
  exact Nat.or_assoc _ _ _

set_option maxRecDepth 16000 in
theorem opsN_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsN, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_not]
  rfl

set_option maxRecDepth 16000 in
theorem len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : len (a :: l) = Nat.succ (len l) := rfl
    rw [e, ih]
    rfl

def insW (w : W) : List W → List W
  | [] => [w]
  | x :: xs => if Nat.ble w.toNat x.toNat = true then w :: x :: xs else x :: insW w xs

set_option maxRecDepth 16000 in
theorem insW_map (w : W) (l : List W) :
    (insW w l).map BitVec.toNat = ins w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insW, ins, List.map_cons]
    split_ifs
    · rfl
    · rw [List.map_cons, ih]

set_option maxRecDepth 16000 in
theorem insW_perm (w : W) (l : List W) : (insW w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insW]
    split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

set_option maxRecDepth 16000 in
theorem mem_innerS (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ innerS pre a (ys ++ b :: zs) mid := by
  intro ys
  induction ys with
  | nil => intro mid; simp [innerS]
  | cons y ys ih =>
    intro mid
    simp only [List.cons_append, innerS, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

set_option maxRecDepth 16000 in
theorem mem_outerS (a b : ℕ) (ys zs : List ℕ) : ∀ xs pre : List ℕ,
    (xs.reverse ++ pre, a, ys.reverse, b, zs) ∈ outerS (xs ++ a :: (ys ++ b :: zs)) pre := by
  intro xs
  induction xs with
  | nil =>
    intro pre
    simp only [List.nil_append, List.reverse_nil, outerS]
    exact List.mem_append_left _ (by simpa using mem_innerS pre a b zs ys [])
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, outerS, List.reverse_cons, List.append_assoc]
    exact List.mem_append_right _ (ih (x :: pre))

set_option maxRecDepth 16000 in
theorem split_two {α : Type} {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (∃ xs ys zs, l = xs ++ a :: (ys ++ b :: zs)) ∨ (∃ xs ys zs, l = xs ++ b :: (ys ++ a :: zs)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h
    exact .inr ⟨s1, s2, t, by simp⟩
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem h
      exact .inl ⟨s, t1, t2, rfl⟩

set_option maxRecDepth 16000 in
theorem nisGoal_goal {g : W} (hg : g = goal ∨ g = ~~~goal) : nisGoal [g.toNat] = true := by
  rcases hg with rfl | rfl <;> decide +kernel

set_option maxRecDepth 16000 in
theorem mem_kids0 {base w : ℕ} {r : List ℕ} (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kids0 base r w := by
  unfold kids0
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG1 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG2 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true) :
    ins w (ins a r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG3 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true) :
    ins w (ins b r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG4 {extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    ins w (ins a (ins b r)) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsL {k : ℕ} {wsN : List ℕ} {t : Split} {w : ℕ} {c : List ℕ}
    (ht : t ∈ outerS wsN []) (hw : w ∈ opsN t.2.1 t.2.2.2.1)
    (h0 : Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kidsG (Nat.sub (Nat.succ (Nat.succ k)) (len wsN)) t.2.1 t.2.2.2.1 (nsep t.2.1)
        (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ kidsL k wsN := by
  unfold kidsL
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, hG hd⟩⟩

set_option maxRecDepth 16000 in
theorem guard1 {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (nsep z.toNat) (cuts r).toNat) M60 = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← nsep_toNat, negOne60] at e
  exact beq_of_eq e

set_option maxRecDepth 16000 in
theorem guard2 {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) M60 = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat, negOne60] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change (nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) =
    (nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

set_option maxRecDepth 16000 in
theorem child_of_split {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hs
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
  have ht := mem_outerS a.toNat b.toNat (ys.map BitVec.toNat) (zs.map BitVec.toNat)
    (xs.map BitVec.toNat) []
  rw [List.append_nil, ← hmap] at ht
  have hzN : z.toNat ∈ opsN a.toNat b.toNat := by
    rw [opsN_map]
    exact List.mem_map_of_mem (List.mem_toFinset.mp hz)
  have hr : rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse
      (zs.map BitVec.toNat) = (xs ++ (ys ++ zs)).map BitVec.toNat := by
    simp [rOf]
  have hbase := baseOf_map xs ys zs
  have hlenN : len (ws.map BitVec.toNat) = ws.length := by
    rw [len_eq, List.length_map]
  have live_of (cW : List W) (hp : cW.Perm (z :: kept)) :
      cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset := by
    refine ⟨hp.nodup_iff.mpr hnd, ?_, ?_⟩
    · rw [hp.length_eq, List.length_cons]
      exact hc
    · have e : cW.toFinset = (z :: kept).toFinset := List.toFinset_eq_of_perm _ _ hp
      rw [e]
      exact hl2
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insW z (xs ++ (ys ++ zs)), (live_of _ (insW_perm _ _)).1, (live_of _ (insW_perm _ _)).2.1,
      (live_of _ (insW_perm _ _)).2.2, ?_⟩
    rw [insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro _
      simp only [hr, hbase]
      exact mem_kids0 (guard1 hcut)
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG1 (guard1 hcut)
  · have hp : (insW z (insW a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG2 (guard2 hcut)
  · have hp : (insW z (insW b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG3 (guard2 hcut)
  · have hp : (insW z (insW a (insW b (xs ++ (ys ++ zs))))).Perm
        (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans (((insW_perm _ _).trans ((insW_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map, insW_map]
    simp only [List.length_cons] at hc
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      omega
    · intro _
      simp only [hr]
      refine mem_kidsG4 ?_
      rw [hlenN]
      apply Nat.ble_eq_true_of_le
      change 2 ≤ k + 2 - ws.length
      omega

set_option maxRecDepth 16000 in
theorem child_exists {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (hl : live basicOps g (k + 1) ws.toFinset) :
    ws = [g] ∨ ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (singleton_list hn done)
  · right
    rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
      ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
    · exact child_of_split hg hn e hz hout hs tail
    · exact child_of_split hg hn e (ops_swap a b ▸ hz) hout
        (by rw [hs, Finset.insert_comm]) tail

set_option maxRecDepth 16000 in
theorem nopt_complete {g : W} (hg : g = goal ∨ g = ~~~goal) : ∀ (k : ℕ) (ws : List W),
    ws.Nodup → live basicOps g k ws.toFinset → nopt k (ws.map BitVec.toNat) = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    have e := singleton_list hn h
    rw [e]
    exact nisGoal_goal hg
  | succ k ih =>
    intro ws hn hl
    rw [nopt_succ]
    rcases child_exists hg hn hl with e | ⟨cW, hcn, _, hcl, hmem⟩
    · rw [e]
      have := nisGoal_goal hg
      simp only [List.map_cons, List.map_nil, this, Bool.true_or]
    · have := ih cW hcn hcl
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)

def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (ncuts ws) M60)

def allKids (m : ℕ) (insN : List ℕ) : List (List ℕ) := (rootsN (m + 1) insN).flatMap (kidsL m)

def isort (l : List ℕ) : List ℕ := l.foldr ins []

def sortK (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => frc x (fun x2 => insK x2 s k))) l k

set_option maxRecDepth 16000 in
theorem sortK_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortK l k = k (isort l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortK (x :: xs) k = sortK xs (fun s => frc x (fun x2 => insK x2 s k)) := rfl
    rw [e, ih, frc_eq, insK_eq]
    rfl

def isortW (l : List W) : List W := l.foldr insW []

set_option maxRecDepth 16000 in
theorem isortW_map (l : List W) :
    (isortW l).map BitVec.toNat = isort (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : isortW (x :: xs) = insW x (isortW xs) := rfl
    have e2 : isort (x.toNat :: xs.map BitVec.toNat) =
        ins x.toNat (isort (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insW_map, ih]

set_option maxRecDepth 16000 in
theorem isortW_perm (l : List W) : (isortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insW_perm x (isortW xs)).trans (ih.cons x)

def dead (m : ℕ) (c : List ℕ) : Bool := sortK c (fun c2 => Bool.rec true false (nopt m c2))

set_option maxRecDepth 16000 in
theorem dead_eq (m : ℕ) (c : List ℕ) : dead m c = !nopt m (isort c) := by
  unfold dead
  rw [sortK_eq, brec]
  cases nopt m (isort c) <;> rfl

set_option maxRecDepth 16000 in
theorem refute (m : ℕ) (inputs : List W) (hnd : inputs.Nodup)
    (h0 : (rootsN (m + 1) (inputs.map BitVec.toNat)).all (fun ws => !nisGoal ws) = true)
    (hk : (allKids m (inputs.map BitVec.toNat)).all (dead m) = true) :
    ∀ t, t = goal ∨ t = ~~~goal → build basicOps t (m + 1) inputs.toFinset → False := by
  intro g hg hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd2 : ws.Nodup := hnd.filter _
  have hl2 : live basicOps g (m + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl2
  rw [List.toFinset_card_of_nodup hnd2] at sz
  have hroot : ws.map BitVec.toNat ∈ rootsN (m + 1) (inputs.map BitVec.toNat) := by
    unfold rootsN
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr ((List.filter_sublist).map _), ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply Nat.ble_eq_true_of_le
      rw [List.length_map]
      exact sz
    · rw [ncuts_map, cuts_full hg hl2, negOne60]
      exact Nat.beq_refl _
  rcases child_exists hg hnd2 hl2 with e | ⟨cW, hcn, _, hcl, hmem⟩
  · have h1 := List.all_eq_true.mp h0 _ hroot
    rw [e] at h1
    have h2 := nisGoal_goal hg
    simp only [List.map_cons, List.map_nil, h2] at h1
    exact absurd h1 (by decide)
  · have hd := List.all_eq_true.mp hk _ (List.mem_flatMap.mpr ⟨_, hroot, hmem⟩)
    have hp := isortW_perm cW
    have e : (isortW cW).toFinset = cW.toFinset := List.toFinset_eq_of_perm _ _ hp
    have run := nopt_complete hg m (isortW cW) (hp.nodup_iff.mpr hcn) (e ▸ hcl)
    rw [isortW_map] at run
    rw [dead_eq, run] at hd
    exact absurd hd (by decide)

set_option maxRecDepth 16000 in
theorem all_chunk {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

end Bridge
def w0 : Nat := ((((((((0xd577a * 2^60 + 0xbfabb76f07dbb76) * 2^60 + 0xe3babd79aeaaf55) * 2^60 + 0xfc5bb66e5b372f8) * 2^60 + 0xbe2ff12793fb8aa) * 2^60 + 0x1c01c18307c000) * 2^60 + 0xfe00003f83f8) * 2^60 + 0x7f0f8000038001c) * 2^60 + 0xf03c0fc00e07ee)
def w1 : Nat := ((((((((0xbcfef * 2^60 + 0xdefdfba17beddb1) * 2^60 + 0xeddf5cdaf79f7ab) * 2^60 + 0xdeaddbf6adfb55d) * 2^60 + 0x5ffcba5cae4fd0c) * 2^60 + 0x60060003f80000) * 2^60 + 0x7f00001fc00000) * 2^60 + 0x7ff000003c001e0) * 2^60 + 0x3ff00070380f)
def w2 : Nat := ((((((((0x73fbf * 2^60 + 0xebfed0f7bdf68fb) * 2^60 + 0x76ee6ebd7bd5f3e) * 2^60 + 0xef36efbb37dd9bf) * 2^60 + 0xf7555ce974bce30) * 2^60 + 0x1801801fc000003) * 2^60 + 0xf80000fe00003ff) * 2^60 + 0x80000003c001e00) * 2^60 + 0xffc0000381c0f0)
def w3 : Nat := ((((((((0xfd7e * 2^60 + 0xf5487dfbdec7edd) * 2^60 + 0xbb73972e5ee7bcf) * 2^60 + 0x75c77ccdc777fea) * 2^60 + 0x6a9a67927fd13c0) * 2^60 + 0xe001ffe000001fc) * 2^60 + 0xffffffc00) * 2^60 + 0x1c0001fff) * 2^60 + 0xf0000001c01ff00)
def w4 : Nat := ((((((((0xffe54 * 2^60 + 0x87ef7efdef78f1e) * 2^60 + 0x3c7be7cf9cf9df3) * 2^60 + 0xb9f87eeffe66e33) * 2^60 + 0x8ce387ffc922000) * 2^60 + 0xfffe000000001ff) * 2^60 + 0xffffff000000000) * 2^60 + 0x1ffffe000) * 2^60 + 0x1ffe0000)
def w5 : Nat := ((((((((0x9476a * 2^60 + 0x9ea9b32103c9930) * 2^60 + 0xe19a1c58a68a701) * 2^60 + 0xdc0992660933058) * 2^60 + 0x1e2cb004824b808) * 2^60 + 0x3000000) * 2^60 + 0x0) * 2^60 + 0x7f0000000000000) * 2^60 + 0x3c000000000e)
def w6 : Nat := ((((((((0xfdfff * 2^60 + 0xffffffef7fffff7) * 2^60 + 0xeffffdfbffbffff) * 2^60 + 0xfefffffeffff7fd) * 2^60 + 0xfffffb7fbfffdae) * 2^60 + 0x7c07c183ffc000) * 2^60 + 0x7ffe001fff83f8) * 2^60 + 0x7fff80003f801fc) * 2^60 + 0xf03fffc07e3fef)
def w7 : Nat := ((((((((0x41010 * 2^60 + 0x2102044e0412246) * 2^60 + 0x220a1210820854) * 2^60 + 0x2052240852042a0) * 2^60 + 0xa003412311b00a2) * 2^60 + 0x1c01c18007c000) * 2^60 + 0xfe00003f83f8) * 2^60 + 0xf8000038001c) * 2^60 + 0xf0000fc00e07e0)
def w8 : Nat := ((((((((0x28885 * 2^60 + 0x405448807824481) * 2^60 + 0xc45408251150aa) * 2^60 + 0x2a44990a4c8505) * 2^60 + 0x41d00a582c04504) * 2^60 + 0x60060000f80000) * 2^60 + 0x7f00001fc00000) * 2^60 + 0xf000003c001e0) * 2^60 + 0x3f000703801)
def w9 : Nat := ((((((((0x5173a * 2^60 + 0xabaa906705d2872) * 2^60 + 0x62aa2c392a80f14) * 2^60 + 0xec12a62a13150b8) * 2^60 + 0xb605502110b8820) * 2^60 + 0x180000000) * 2^60 + 0x3f8) * 2^60 + 0x0) * 2^60 + 0xf00000000000e0)
def w10 : Nat := ((((((((0xf7fff * 2^60 + 0xfffff7ffbfffbff) * 2^60 + 0xf7fefffdfffff7f) * 2^60 + 0xff7fffff7fffbff) * 2^60 + 0xff7ffdeff7ffeba) * 2^60 + 0x19c19c1ff07c003) * 2^60 + 0xf80fe0fe03f83ff) * 2^60 + 0xff0f8003c381e1c) * 2^60 + 0xfffc0fc38fc7fe)
def w11 : Nat := ((((((((0x84040 * 2^60 + 0x140127080209304) * 2^60 + 0x81109140842a041) * 2^60 + 0x104910444822240) * 2^60 + 0x82aa106834308a) * 2^60 + 0x1c01c00307c000) * 2^60 + 0xfe00003f8000) * 2^60 + 0x7f0f8000038001c) * 2^60 + 0x3c0fc00e070e)
def w12 : Nat := ((((((((0x22885 * 2^60 + 0x40544090b824089) * 2^60 + 0x14444284515502a) * 2^60 + 0x324499124c8907) * 2^60 + 0x41500cc86404610) * 2^60 + 0x18018007c000003) * 2^60 + 0xf80000fe0000007) * 2^60 + 0x80000003c001e00) * 2^60 + 0xfc0000381c010)
def w13 : Nat := ((((((((0x557a * 2^60 + 0xb508356b06c3a54) * 2^60 + 0xa33295280ea2b45) * 2^60 + 0x7443344c43372e8) * 2^60 + 0x2a0a610213d1080) * 2^60 + 0x1c000000000) * 2^60 + 0x3f8000) * 2^60 + 0x1c) * 2^60 + 0x700)
def w14 : Nat := ((((((((0xdff7e * 2^60 + 0xffebffffdfdffff) * 2^60 + 0xfbfbbf7ffeeffdf) * 2^60 + 0xfddffeefdf77ffa) * 2^60 + 0xfebff7b7fffbbea) * 2^60 + 0xe1c1fff8307c1fc) * 2^60 + 0xfe0ffffffff8) * 2^60 + 0x7f0f801c0381fff) * 2^60 + 0xff03c0fdc0fffee)
def w15 : Nat := ((((((((0xd0200 * 2^60 + 0xaa382040118122) * 2^60 + 0x40882851a008410) * 2^60 + 0x881882221800010) * 2^60 + 0x94259025802a82a) * 2^60 + 0x1c00018307c000) * 2^60 + 0xfe00000003f8) * 2^60 + 0x7f0f80000380000) * 2^60 + 0xf03c0fc00e00ee)
def w16 : Nat := ((((((((0xa804 * 2^60 + 0x40404890d804489) * 2^60 + 0x18410206504508a) * 2^60 + 0x18448818440d02) * 2^60 + 0x409006906c00340) * 2^60 + 0xe001e3e000001fc) * 2^60 + 0xfffc07c00) * 2^60 + 0x1c0001fe3) * 2^60 + 0xf0000001c01f800)
def w17 : Nat := ((((((((0xd5650 * 2^60 + 0x87ab366d0758b16) * 2^60 + 0x203aa5498ca8d51) * 2^60 + 0xb858366e5a26230) * 2^60 + 0x8c2381278122000) * 2^60 + 0x1c000000000000) * 2^60 + 0xfe0000000000) * 2^60 + 0x380000) * 2^60 + 0xe0000)
def w18 : Nat := ((((((((0xfff7e * 2^60 + 0xbfefffffeffbf7e) * 2^60 + 0xfffbffffbefbff7) * 2^60 + 0xfdfbfeefff77efb) * 2^60 + 0xbeeff7ffdbfb8aa) * 2^60 + 0xfffe1c18307c1ff) * 2^60 + 0xffffff0003f83f8) * 2^60 + 0x7f0f801ffffe01c) * 2^60 + 0xf03c0fdffe07ee)
def w19 : Nat := ((((((((0x12a * 2^60 + 0x380081020083060) * 2^60 + 0xc38018302202204) * 2^60 + 0x4403800001110c8) * 2^60 + 0x320c700012d98aa) * 2^60 + 0x1c18307c000) * 2^60 + 0x3f83f8) * 2^60 + 0x7f0f8000000001c) * 2^60 + 0xf03c0fc00007ee)
def w20 : Nat := ((((((((0x2a804 * 2^60 + 0x444890e820408) * 2^60 + 0x1c41428610510a2) * 2^60 + 0x1a04881a440c03) * 2^60 + 0xc006d84800000) * 2^60 + 0xfe3e000000001ff) * 2^60 + 0xfff01f000000000) * 2^60 + 0x1ffc7e000) * 2^60 + 0x1ff00000)
def w21 : Nat := ((((((((0x30faf * 2^60 + 0xcafcd0a139e48b1) * 2^60 + 0x64ce4c98739572a) * 2^60 + 0xce24cbb225d911d) * 2^60 + 0x57541848240cc00) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w22 : Nat := ((((((((0xfffff * 2^60 + 0xfffffbf7ffffdfb) * 2^60 + 0xffff7effffdffbf) * 2^60 + 0xffbfffffbfffdff) * 2^60 + 0xfffdfefdfefff3c) * 2^60 + 0x1e01e01fff80003) * 2^60 + 0xfff000fffc003ff) * 2^60 + 0xfff00003fc01fe0) * 2^60 + 0xfffff003f1f8ff)
def w23 : Nat := ((((((((0x8c040 * 2^60 + 0x14012b004209500) * 2^60 + 0x89111042840a081) * 2^60 + 0x108910448822440) * 2^60 + 0x8a8a2148a4310c) * 2^60 + 0x60060003f80000) * 2^60 + 0x7f00001fc00000) * 2^60 + 0x7ff000003c001e0) * 2^60 + 0x3ff00070380f)
def w24 : Nat := ((((((((0x43010 * 2^60 + 0x21020056841204a) * 2^60 + 0x122022250840814) * 2^60 + 0x2112240912048a2) * 2^60 + 0xa00144a150b0230) * 2^60 + 0x1801801fc000003) * 2^60 + 0xf80000fe00003ff) * 2^60 + 0x80000003c001e00) * 2^60 + 0xffc0000381c0f0)
def w25 : Nat := ((((((((0xcd6e * 2^60 + 0xd44879a15ac5c91) * 2^60 + 0xa953140a568738b) * 2^60 + 0x548558c48573548) * 2^60 + 0x4a9822102e41100) * 2^60 + 0x60000000000) * 2^60 + 0x1fc00000) * 2^60 + 0x1e0) * 2^60 + 0x3800)
def w26 : Nat := ((((((((0xbffff * 2^60 + 0xfffdfffbffefffd) * 2^60 + 0xffffdffefffffef) * 2^60 + 0xffefffffeffffff) * 2^60 + 0x7ffeffdeffdffcc) * 2^60 + 0xe601ffe03f801fc) * 2^60 + 0x7f000ffffffc00) * 2^60 + 0x7ff0001c3c01fff) * 2^60 + 0xf003ff01c71ff0f)
def w27 : Nat := ((((((((0xb0281 * 2^60 + 0xab582002128120) * 2^60 + 0x448c48d0a118420) * 2^60 + 0x8a2883322888015) * 2^60 + 0x1564984c800ec0c) * 2^60 + 0x60000003f80000) * 2^60 + 0x7f000000000000) * 2^60 + 0x7ff000003c00000) * 2^60 + 0x3ff00070000f)
def w28 : Nat := ((((((((0x3010 * 2^60 + 0x2100045a840224c) * 2^60 + 0x122083240860844) * 2^60 + 0x214224094204aa2) * 2^60 + 0x2002458251902c0) * 2^60 + 0xe0019fe000001fc) * 2^60 + 0xfe03ffc00) * 2^60 + 0x1c0001e1f) * 2^60 + 0xf0000001c01c700)
def w29 : Nat := ((((((((0xbce44 * 2^60 + 0x86ed7aa16b68d10) * 2^60 + 0x2c5b44ca94995a3) * 2^60 + 0x98a85ae6ac62411) * 2^60 + 0xce0825c8802000) * 2^60 + 0x60000000000000) * 2^60 + 0x7f000000000000) * 2^60 + 0x3c00000) * 2^60 + 0x700000)
def w30 : Nat := ((((((((0xfffff * 2^60 + 0xdffffffdfffdfbf) * 2^60 + 0xfdffffdfffffffb) * 2^60 + 0xfffdfffffffff7f) * 2^60 + 0xdfffbfffef6fd0c) * 2^60 + 0xfffe60003f801ff) * 2^60 + 0xffffff01fc00000) * 2^60 + 0x7ff0001ffffe1e0) * 2^60 + 0x3ff01ffe380f)
def w31 : Nat := ((((((((0x1ab * 2^60 + 0x5810810010850a1) * 2^60 + 0xc18418106306208) * 2^60 + 0x46058110019914c) * 2^60 + 0x531c3800264dd0c) * 2^60 + 0x60003f80000) * 2^60 + 0x1fc00000) * 2^60 + 0x7ff0000000001e0) * 2^60 + 0x3ff00000380f)
def w32 : Nat := ((((((((0x43010 * 2^60 + 0x102045c841020e) * 2^60 + 0x1020a3050860850) * 2^60 + 0x215024095204a22) * 2^60 + 0x800305a34120000) * 2^60 + 0xf9fe000000001ff) * 2^60 + 0xf80fff000000000) * 2^60 + 0x1fc3fe000) * 2^60 + 0x1f8e0000)
def w33 : Nat := ((((((((0x3d3e * 2^60 + 0xe14850f39cc68d9) * 2^60 + 0x3262062c5ac5b0e) * 2^60 + 0x65066c8907559aa) * 2^60 + 0x621044807490200) * 2^60 + 0x180000000000) * 2^60 + 0xfe0000000) * 2^60 + 0x1e00) * 2^60 + 0x1c000)
def w34 : Nat := ((((((((0x7ffff * 2^60 + 0xfffefdfffff7eff) * 2^60 + 0xffffffbf7ff7fff) * 2^60 + 0xfff7fffff7fffff) * 2^60 + 0xffdf7ffb7ffdff0) * 2^60 + 0xf801ffffc0001ff) * 2^60 + 0xf80000fffffffff) * 2^60 + 0x8000001fc001fff) * 2^60 + 0xfffc0001f81fff0)
def w35 : Nat := ((((((((0x70281 * 2^60 + 0xab680042130022) * 2^60 + 0x448c68912110430) * 2^60 + 0x8a3083323088015) * 2^60 + 0x95451869002cc30) * 2^60 + 0x1800001fc000003) * 2^60 + 0xf800000000003ff) * 2^60 + 0x80000003c000000) * 2^60 + 0xffc000038000f0)
def w36 : Nat := ((((((((0xc040 * 2^60 + 0x14002d084201604) * 2^60 + 0x8911910204220c1) * 2^60 + 0x10c11044c022640) * 2^60 + 0x88a23120b411c0) * 2^60 + 0xe0007fe000001fc) * 2^60 + 0x1ffffc00) * 2^60 + 0x1c00001ff) * 2^60 + 0xf0000001c003f00)
def w37 : Nat := ((((((((0x73e14 * 2^60 + 0x83ee50f5ad7081a) * 2^60 + 0x346a668d18d1d32) * 2^60 + 0xa9306eab3644833) * 2^60 + 0x844104e94020000) * 2^60 + 0x180000000000003) * 2^60 + 0xf80000000000000) * 2^60 + 0x3c000000) * 2^60 + 0x3800000)
def w38 : Nat := ((((((((0xfffff * 2^60 + 0xeffffefffffefff) * 2^60 + 0x7effeffffffdfff) * 2^60 + 0xfffefffffffffbf) * 2^60 + 0xfff7dffffdbee30) * 2^60 + 0xffff801fc0001ff) * 2^60 + 0xfffffffe00003ff) * 2^60 + 0x8000001fffffe00) * 2^60 + 0xffc0001fffc0f0)
def w39 : Nat := ((((((((0x1ab * 2^60 + 0x6810800210860e1) * 2^60 + 0x42840830630420c) * 2^60 + 0x46068110019918c) * 2^60 + 0x73145800349ce30) * 2^60 + 0x1801fc000000) * 2^60 + 0xfe00003ff) * 2^60 + 0x800000000001e00) * 2^60 + 0xffc0000001c0f0)
def w40 : Nat := ((((((((0x8c040 * 2^60 + 0x4012e084208704) * 2^60 + 0x811814284280c1) * 2^60 + 0x10c81044c822600) * 2^60 + 0x8a283168902000) * 2^60 + 0xe7fe000000001fc) * 2^60 + 0x7ffff000000000) * 2^60 + 0x1c3ffe000) * 2^60 + 0x1c7e0000)
def w41 : Nat := ((((((((0xfc54 * 2^60 + 0x85487cf9ce40e1c) * 2^60 + 0x3873870e1ce19c3) * 2^60 + 0x31c07ccdc666e22) * 2^60 + 0x88207924900000) * 2^60 + 0xe000000000001fc) * 2^60 + 0x0) * 2^60 + 0x1c0000000) * 2^60 + 0x1c000000)
def w42 : Nat := ((((((((0xfff7e * 2^60 + 0xf7ef7ffffffffdf) * 2^60 + 0xbf7bf7efdefffff) * 2^60 + 0xfdff7eefff77ffb) * 2^60 + 0xeefbe7fffff33c0) * 2^60 + 0xffffffe000001ff) * 2^60 + 0xffffffffffffc00) * 2^60 + 0x1ffffffff) * 2^60 + 0xf0000001fffff00)
def w43 : Nat := ((((((((0x12a * 2^60 + 0x7000010210870c1) * 2^60 + 0x83001020420620c) * 2^60 + 0x4407000001111c8) * 2^60 + 0x6218600036d13c0) * 2^60 + 0x1ffe00000000) * 2^60 + 0xffffffc00) * 2^60 + 0x1fff) * 2^60 + 0xf0000000001ff00)
def w44 : Nat := ((((((((0xf0200 * 2^60 + 0x2a702042138102) * 2^60 + 0x40860c18018430) * 2^60 + 0x883802223800011) * 2^60 + 0x8461806d8022000) * 2^60 + 0x1ffe00000000003) * 2^60 + 0xffffff000000000) * 2^60 + 0x3fffe000) * 2^60 + 0x3fe0000)
def nums : List Nat := [w0,w1,w2,w3,w4]
def s0 : List Nat := [w3,w2,w5,w1,w0,w4]
def q0 := kidsL 6 s0
def s1 : List Nat := [w3,w2,w1,w0,w6,w4]
def q1 := kidsL 6 s1
def s2 : List Nat := [w3,w7,w2,w1,w0,w4]
def q2 := kidsL 6 s2
def s3 : List Nat := [w3,w8,w2,w1,w0,w4]
def q3 := kidsL 6 s3
def s4 : List Nat := [w3,w9,w2,w1,w0,w4]
def q4 := kidsL 6 s4
def s5 : List Nat := [w3,w2,w1,w0,w10,w4]
def q5 := kidsL 6 s5
def s6 : List Nat := [w3,w2,w11,w1,w0,w4]
def q6 := kidsL 6 s6
def s7 : List Nat := [w3,w12,w2,w1,w0,w4]
def q7 := kidsL 6 s7
def s8 : List Nat := [w13,w3,w2,w1,w0,w4]
def q8 := kidsL 6 s8
def s9 : List Nat := [w3,w2,w1,w0,w14,w4]
def q9 := kidsL 6 s9
def s10 : List Nat := [w3,w2,w1,w15,w0,w4]
def q10 := kidsL 6 s10
def s11 : List Nat := [w16,w3,w2,w1,w0,w4]
def q11 := kidsL 6 s11
def s12 : List Nat := [w3,w2,w1,w17,w0,w4]
def q12 := kidsL 6 s12
def s13 : List Nat := [w3,w2,w1,w0,w4,w18]
def q13 := kidsL 6 s13
def s14 : List Nat := [w19,w3,w2,w1,w0,w4]
def q14 := kidsL 6 s14
def s15 : List Nat := [w3,w20,w2,w1,w0,w4]
def q15 := kidsL 6 s15
def s16 : List Nat := [w3,w21,w2,w1,w0,w4]
def q16 := kidsL 6 s16
def s17 : List Nat := [w3,w2,w1,w0,w4,w22]
def q17 := kidsL 6 s17
def s18 : List Nat := [w3,w2,w23,w1,w0,w4]
def q18 := kidsL 6 s18
def s19 : List Nat := [w3,w24,w2,w1,w0,w4]
def q19 := kidsL 6 s19
def s20 : List Nat := [w25,w3,w2,w1,w0,w4]
def q20 := kidsL 6 s20
def s21 : List Nat := [w3,w2,w1,w26,w0,w4]
def q21 := kidsL 6 s21
def s22 : List Nat := [w3,w2,w27,w1,w0,w4]
def q22 := kidsL 6 s22
def s23 : List Nat := [w28,w3,w2,w1,w0,w4]
def q23 := kidsL 6 s23
def s24 : List Nat := [w3,w2,w29,w1,w0,w4]
def q24 := kidsL 6 s24
def s25 : List Nat := [w3,w2,w1,w0,w4,w30]
def q25 := kidsL 6 s25
def s26 : List Nat := [w31,w3,w2,w1,w0,w4]
def q26 := kidsL 6 s26
def s27 : List Nat := [w3,w32,w2,w1,w0,w4]
def q27 := kidsL 6 s27
def s28 : List Nat := [w33,w3,w2,w1,w0,w4]
def q28 := kidsL 6 s28
def s29 : List Nat := [w3,w2,w34,w1,w0,w4]
def q29 := kidsL 6 s29
def s30 : List Nat := [w3,w35,w2,w1,w0,w4]
def q30 := kidsL 6 s30
def s31 : List Nat := [w36,w3,w2,w1,w0,w4]
def q31 := kidsL 6 s31
def s32 : List Nat := [w3,w37,w2,w1,w0,w4]
def q32 := kidsL 6 s32
def s33 : List Nat := [w3,w2,w1,w0,w4,w38]
def q33 := kidsL 6 s33
def s34 : List Nat := [w39,w3,w2,w1,w0,w4]
def q34 := kidsL 6 s34
def s35 : List Nat := [w3,w2,w40,w1,w0,w4]
def q35 := kidsL 6 s35
def s36 : List Nat := [w41,w3,w2,w1,w0,w4]
def q36 := kidsL 6 s36
def s37 : List Nat := [w3,w2,w1,w0,w4,w42]
def q37 := kidsL 6 s37
def s38 : List Nat := [w43,w3,w2,w1,w0,w4]
def q38 := kidsL 6 s38
def s39 : List Nat := [w3,w2,w1,w0,w44,w4]
def q39 := kidsL 6 s39

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_0 : ((q0.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_5 : ((q0.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_9 : ((q0.drop 9).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_16 : ((q0.drop 16).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_22 : ((q0.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_26 : ((q0.drop 26).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_31 : ((q0.drop 31).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_38 : ((q0.drop 38).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_45 : ((q0.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_49 : ((q0.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_52 : ((q0.drop 52).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_57 : ((q0.drop 57).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_60 : ((q0.drop 60).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_63 : ((q0.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_67 : ((q0.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_71 : ((q0.drop 71).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_77 : ((q0.drop 77).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_86 : ((q0.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok0 : nopt 7 s0 = false := by
  have h : q0.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p0_0 (all_chunk _ _ 5 4 p0_5 (all_chunk _ _ 9 7 p0_9 (all_chunk _ _ 16 6 p0_16 (all_chunk _ _ 22 4 p0_22 (all_chunk _ _ 26 5 p0_26 (all_chunk _ _ 31 7 p0_31 (all_chunk _ _ 38 7 p0_38 (all_chunk _ _ 45 4 p0_45 (all_chunk _ _ 49 3 p0_49 (all_chunk _ _ 52 5 p0_52 (all_chunk _ _ 57 3 p0_57 (all_chunk _ _ 60 3 p0_60 (all_chunk _ _ 63 4 p0_63 (all_chunk _ _ 67 4 p0_67 (all_chunk _ _ 71 6 p0_71 (all_chunk _ _ 77 9 p0_77 (all_chunk _ _ 86 4 p0_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s0 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_0 : ((q1.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_9 : ((q1.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_15 : ((q1.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_19 : ((q1.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_25 : ((q1.drop 25).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_32 : ((q1.drop 32).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_37 : ((q1.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_41 : ((q1.drop 41).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_50 : ((q1.drop 50).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_56 : ((q1.drop 56).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_60 : ((q1.drop 60).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_62 : ((q1.drop 62).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_70 : ((q1.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_73 : ((q1.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_76 : ((q1.drop 76).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_82 : ((q1.drop 82).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_87 : ((q1.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_91 : ((q1.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok1 : nopt 7 s1 = false := by
  have h : q1.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p1_0 (all_chunk _ _ 9 6 p1_9 (all_chunk _ _ 15 4 p1_15 (all_chunk _ _ 19 6 p1_19 (all_chunk _ _ 25 7 p1_25 (all_chunk _ _ 32 5 p1_32 (all_chunk _ _ 37 4 p1_37 (all_chunk _ _ 41 9 p1_41 (all_chunk _ _ 50 6 p1_50 (all_chunk _ _ 56 4 p1_56 (all_chunk _ _ 60 2 p1_60 (all_chunk _ _ 62 8 p1_62 (all_chunk _ _ 70 3 p1_70 (all_chunk _ _ 73 3 p1_73 (all_chunk _ _ 76 6 p1_76 (all_chunk _ _ 82 5 p1_82 (all_chunk _ _ 87 4 p1_87 (all_chunk _ _ 91 1 p1_91 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s1 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_0 : ((q2.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_5 : ((q2.drop 5).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_13 : ((q2.drop 13).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_21 : ((q2.drop 21).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_27 : ((q2.drop 27).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_32 : ((q2.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_34 : ((q2.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_39 : ((q2.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_42 : ((q2.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_46 : ((q2.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_49 : ((q2.drop 49).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_51 : ((q2.drop 51).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_56 : ((q2.drop 56).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_61 : ((q2.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_69 : ((q2.drop 69).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_79 : ((q2.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_88 : ((q2.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok2 : nopt 7 s2 = false := by
  have h : q2.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p2_0 (all_chunk _ _ 5 8 p2_5 (all_chunk _ _ 13 8 p2_13 (all_chunk _ _ 21 6 p2_21 (all_chunk _ _ 27 5 p2_27 (all_chunk _ _ 32 2 p2_32 (all_chunk _ _ 34 5 p2_34 (all_chunk _ _ 39 3 p2_39 (all_chunk _ _ 42 4 p2_42 (all_chunk _ _ 46 3 p2_46 (all_chunk _ _ 49 2 p2_49 (all_chunk _ _ 51 5 p2_51 (all_chunk _ _ 56 5 p2_56 (all_chunk _ _ 61 8 p2_61 (all_chunk _ _ 69 10 p2_69 (all_chunk _ _ 79 9 p2_79 (all_chunk _ _ 88 4 p2_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s2 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_0 : ((q3.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_5 : ((q3.drop 5).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_11 : ((q3.drop 11).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_19 : ((q3.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_25 : ((q3.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_29 : ((q3.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_34 : ((q3.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_37 : ((q3.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_40 : ((q3.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_44 : ((q3.drop 44).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_49 : ((q3.drop 49).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_53 : ((q3.drop 53).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_57 : ((q3.drop 57).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_61 : ((q3.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_69 : ((q3.drop 69).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_79 : ((q3.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_88 : ((q3.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok3 : nopt 7 s3 = false := by
  have h : q3.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p3_0 (all_chunk _ _ 5 6 p3_5 (all_chunk _ _ 11 8 p3_11 (all_chunk _ _ 19 6 p3_19 (all_chunk _ _ 25 4 p3_25 (all_chunk _ _ 29 5 p3_29 (all_chunk _ _ 34 3 p3_34 (all_chunk _ _ 37 3 p3_37 (all_chunk _ _ 40 4 p3_40 (all_chunk _ _ 44 5 p3_44 (all_chunk _ _ 49 4 p3_49 (all_chunk _ _ 53 4 p3_53 (all_chunk _ _ 57 4 p3_57 (all_chunk _ _ 61 8 p3_61 (all_chunk _ _ 69 10 p3_69 (all_chunk _ _ 79 9 p3_79 (all_chunk _ _ 88 2 p3_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s3 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_0 : ((q4.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_3 : ((q4.drop 3).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_8 : ((q4.drop 8).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_17 : ((q4.drop 17).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_24 : ((q4.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_28 : ((q4.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_31 : ((q4.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_36 : ((q4.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_40 : ((q4.drop 40).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_45 : ((q4.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_48 : ((q4.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_51 : ((q4.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_55 : ((q4.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_59 : ((q4.drop 59).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_64 : ((q4.drop 64).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_73 : ((q4.drop 73).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_82 : ((q4.drop 82).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok4 : nopt 7 s4 = false := by
  have h : q4.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p4_0 (all_chunk _ _ 3 5 p4_3 (all_chunk _ _ 8 9 p4_8 (all_chunk _ _ 17 7 p4_17 (all_chunk _ _ 24 4 p4_24 (all_chunk _ _ 28 3 p4_28 (all_chunk _ _ 31 5 p4_31 (all_chunk _ _ 36 4 p4_36 (all_chunk _ _ 40 5 p4_40 (all_chunk _ _ 45 3 p4_45 (all_chunk _ _ 48 3 p4_48 (all_chunk _ _ 51 4 p4_51 (all_chunk _ _ 55 4 p4_55 (all_chunk _ _ 59 5 p4_59 (all_chunk _ _ 64 9 p4_64 (all_chunk _ _ 73 9 p4_73 (all_chunk _ _ 82 8 p4_82 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s4 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_0 : ((q5.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_9 : ((q5.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_15 : ((q5.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_19 : ((q5.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_25 : ((q5.drop 25).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_33 : ((q5.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_38 : ((q5.drop 38).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_42 : ((q5.drop 42).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_44 : ((q5.drop 44).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_52 : ((q5.drop 52).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_58 : ((q5.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_61 : ((q5.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_65 : ((q5.drop 65).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_71 : ((q5.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_75 : ((q5.drop 75).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_77 : ((q5.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_83 : ((q5.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_87 : ((q5.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_91 : ((q5.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok5 : nopt 7 s5 = false := by
  have h : q5.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p5_0 (all_chunk _ _ 9 6 p5_9 (all_chunk _ _ 15 4 p5_15 (all_chunk _ _ 19 6 p5_19 (all_chunk _ _ 25 8 p5_25 (all_chunk _ _ 33 5 p5_33 (all_chunk _ _ 38 4 p5_38 (all_chunk _ _ 42 2 p5_42 (all_chunk _ _ 44 8 p5_44 (all_chunk _ _ 52 6 p5_52 (all_chunk _ _ 58 3 p5_58 (all_chunk _ _ 61 4 p5_61 (all_chunk _ _ 65 6 p5_65 (all_chunk _ _ 71 4 p5_71 (all_chunk _ _ 75 2 p5_75 (all_chunk _ _ 77 6 p5_77 (all_chunk _ _ 83 4 p5_83 (all_chunk _ _ 87 4 p5_87 (all_chunk _ _ 91 1 p5_91 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s5 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_0 : ((q6.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_7 : ((q6.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_12 : ((q6.drop 12).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_21 : ((q6.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_25 : ((q6.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_30 : ((q6.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_33 : ((q6.drop 33).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_39 : ((q6.drop 39).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_48 : ((q6.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_54 : ((q6.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_59 : ((q6.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_63 : ((q6.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_66 : ((q6.drop 66).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_71 : ((q6.drop 71).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_76 : ((q6.drop 76).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_84 : ((q6.drop 84).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok6 : nopt 7 s6 = false := by
  have h : q6.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p6_0 (all_chunk _ _ 7 5 p6_7 (all_chunk _ _ 12 9 p6_12 (all_chunk _ _ 21 4 p6_21 (all_chunk _ _ 25 5 p6_25 (all_chunk _ _ 30 3 p6_30 (all_chunk _ _ 33 6 p6_33 (all_chunk _ _ 39 9 p6_39 (all_chunk _ _ 48 6 p6_48 (all_chunk _ _ 54 5 p6_54 (all_chunk _ _ 59 4 p6_59 (all_chunk _ _ 63 3 p6_63 (all_chunk _ _ 66 5 p6_66 (all_chunk _ _ 71 5 p6_71 (all_chunk _ _ 76 8 p6_76 (all_chunk _ _ 84 8 p6_84 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s6 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_0 : ((q7.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_5 : ((q7.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_10 : ((q7.drop 10).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_18 : ((q7.drop 18).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_25 : ((q7.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_29 : ((q7.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_32 : ((q7.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_36 : ((q7.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_40 : ((q7.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_44 : ((q7.drop 44).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_49 : ((q7.drop 49).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_53 : ((q7.drop 53).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_57 : ((q7.drop 57).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_61 : ((q7.drop 61).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_70 : ((q7.drop 70).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_80 : ((q7.drop 80).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_88 : ((q7.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok7 : nopt 7 s7 = false := by
  have h : q7.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p7_0 (all_chunk _ _ 5 5 p7_5 (all_chunk _ _ 10 8 p7_10 (all_chunk _ _ 18 7 p7_18 (all_chunk _ _ 25 4 p7_25 (all_chunk _ _ 29 3 p7_29 (all_chunk _ _ 32 4 p7_32 (all_chunk _ _ 36 4 p7_36 (all_chunk _ _ 40 4 p7_40 (all_chunk _ _ 44 5 p7_44 (all_chunk _ _ 49 4 p7_49 (all_chunk _ _ 53 4 p7_53 (all_chunk _ _ 57 4 p7_57 (all_chunk _ _ 61 9 p7_61 (all_chunk _ _ 70 10 p7_70 (all_chunk _ _ 80 8 p7_80 (all_chunk _ _ 88 2 p7_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s7 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_0 : ((q8.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_3 : ((q8.drop 3).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_5 : ((q8.drop 5).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_7 : ((q8.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_10 : ((q8.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_13 : ((q8.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_17 : ((q8.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_20 : ((q8.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_23 : ((q8.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_27 : ((q8.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_30 : ((q8.drop 30).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_32 : ((q8.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_34 : ((q8.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_37 : ((q8.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_40 : ((q8.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_42 : ((q8.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_45 : ((q8.drop 45).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_51 : ((q8.drop 51).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_56 : ((q8.drop 56).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_57 : ((q8.drop 57).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_58 : ((q8.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_62 : ((q8.drop 62).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_64 : ((q8.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_68 : ((q8.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_71 : ((q8.drop 71).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_78 : ((q8.drop 78).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_84 : ((q8.drop 84).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_90 : ((q8.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_94 : ((q8.drop 94).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok8 : nopt 7 s8 = false := by
  have h : q8.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p8_0 (all_chunk _ _ 3 2 p8_3 (all_chunk _ _ 5 2 p8_5 (all_chunk _ _ 7 3 p8_7 (all_chunk _ _ 10 3 p8_10 (all_chunk _ _ 13 4 p8_13 (all_chunk _ _ 17 3 p8_17 (all_chunk _ _ 20 3 p8_20 (all_chunk _ _ 23 4 p8_23 (all_chunk _ _ 27 3 p8_27 (all_chunk _ _ 30 2 p8_30 (all_chunk _ _ 32 2 p8_32 (all_chunk _ _ 34 3 p8_34 (all_chunk _ _ 37 3 p8_37 (all_chunk _ _ 40 2 p8_40 (all_chunk _ _ 42 3 p8_42 (all_chunk _ _ 45 6 p8_45 (all_chunk _ _ 51 5 p8_51 (all_chunk _ _ 56 1 p8_56 (all_chunk _ _ 57 1 p8_57 (all_chunk _ _ 58 4 p8_58 (all_chunk _ _ 62 2 p8_62 (all_chunk _ _ 64 4 p8_64 (all_chunk _ _ 68 3 p8_68 (all_chunk _ _ 71 7 p8_71 (all_chunk _ _ 78 6 p8_78 (all_chunk _ _ 84 6 p8_84 (all_chunk _ _ 90 4 p8_90 (all_chunk _ _ 94 1 p8_94 (by decide +kernel))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s8 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_0 : ((q9.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_5 : ((q9.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_9 : ((q9.drop 9).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_10 : ((q9.drop 10).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_11 : ((q9.drop 11).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_13 : ((q9.drop 13).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_16 : ((q9.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_19 : ((q9.drop 19).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_21 : ((q9.drop 21).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_23 : ((q9.drop 23).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_25 : ((q9.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_28 : ((q9.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_32 : ((q9.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_34 : ((q9.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_39 : ((q9.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_43 : ((q9.drop 43).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_45 : ((q9.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_49 : ((q9.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_54 : ((q9.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_59 : ((q9.drop 59).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_61 : ((q9.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_65 : ((q9.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_69 : ((q9.drop 69).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_71 : ((q9.drop 71).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_73 : ((q9.drop 73).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_75 : ((q9.drop 75).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_77 : ((q9.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_81 : ((q9.drop 81).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_84 : ((q9.drop 84).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_85 : ((q9.drop 85).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_86 : ((q9.drop 86).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_89 : ((q9.drop 89).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_91 : ((q9.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_94 : ((q9.drop 94).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok9 : nopt 7 s9 = false := by
  have h : q9.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p9_0 (all_chunk _ _ 5 4 p9_5 (all_chunk _ _ 9 1 p9_9 (all_chunk _ _ 10 1 p9_10 (all_chunk _ _ 11 2 p9_11 (all_chunk _ _ 13 3 p9_13 (all_chunk _ _ 16 3 p9_16 (all_chunk _ _ 19 2 p9_19 (all_chunk _ _ 21 2 p9_21 (all_chunk _ _ 23 2 p9_23 (all_chunk _ _ 25 3 p9_25 (all_chunk _ _ 28 4 p9_28 (all_chunk _ _ 32 2 p9_32 (all_chunk _ _ 34 5 p9_34 (all_chunk _ _ 39 4 p9_39 (all_chunk _ _ 43 2 p9_43 (all_chunk _ _ 45 4 p9_45 (all_chunk _ _ 49 5 p9_49 (all_chunk _ _ 54 5 p9_54 (all_chunk _ _ 59 2 p9_59 (all_chunk _ _ 61 4 p9_61 (all_chunk _ _ 65 4 p9_65 (all_chunk _ _ 69 2 p9_69 (all_chunk _ _ 71 2 p9_71 (all_chunk _ _ 73 2 p9_73 (all_chunk _ _ 75 2 p9_75 (all_chunk _ _ 77 4 p9_77 (all_chunk _ _ 81 3 p9_81 (all_chunk _ _ 84 1 p9_84 (all_chunk _ _ 85 1 p9_85 (all_chunk _ _ 86 3 p9_86 (all_chunk _ _ 89 2 p9_89 (all_chunk _ _ 91 3 p9_91 (all_chunk _ _ 94 1 p9_94 (by decide +kernel)))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s9 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_0 : ((q10.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_9 : ((q10.drop 9).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_12 : ((q10.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_15 : ((q10.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_18 : ((q10.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_22 : ((q10.drop 22).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_28 : ((q10.drop 28).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_33 : ((q10.drop 33).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_39 : ((q10.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_44 : ((q10.drop 44).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_54 : ((q10.drop 54).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_60 : ((q10.drop 60).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_70 : ((q10.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_73 : ((q10.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_76 : ((q10.drop 76).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_79 : ((q10.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_83 : ((q10.drop 83).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_86 : ((q10.drop 86).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_91 : ((q10.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok10 : nopt 7 s10 = false := by
  have h : q10.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p10_0 (all_chunk _ _ 9 3 p10_9 (all_chunk _ _ 12 3 p10_12 (all_chunk _ _ 15 3 p10_15 (all_chunk _ _ 18 4 p10_18 (all_chunk _ _ 22 6 p10_22 (all_chunk _ _ 28 5 p10_28 (all_chunk _ _ 33 6 p10_33 (all_chunk _ _ 39 5 p10_39 (all_chunk _ _ 44 10 p10_44 (all_chunk _ _ 54 6 p10_54 (all_chunk _ _ 60 10 p10_60 (all_chunk _ _ 70 3 p10_70 (all_chunk _ _ 73 3 p10_73 (all_chunk _ _ 76 3 p10_76 (all_chunk _ _ 79 4 p10_79 (all_chunk _ _ 83 3 p10_83 (all_chunk _ _ 86 5 p10_86 (all_chunk _ _ 91 1 p10_91 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s10 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_0 : ((q11.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_3 : ((q11.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_6 : ((q11.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_8 : ((q11.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_11 : ((q11.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_16 : ((q11.drop 16).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_21 : ((q11.drop 21).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_26 : ((q11.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_29 : ((q11.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_31 : ((q11.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_35 : ((q11.drop 35).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_38 : ((q11.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_41 : ((q11.drop 41).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_44 : ((q11.drop 44).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_51 : ((q11.drop 51).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_57 : ((q11.drop 57).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_63 : ((q11.drop 63).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_71 : ((q11.drop 71).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_81 : ((q11.drop 81).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_88 : ((q11.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok11 : nopt 7 s11 = false := by
  have h : q11.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p11_0 (all_chunk _ _ 3 3 p11_3 (all_chunk _ _ 6 2 p11_6 (all_chunk _ _ 8 3 p11_8 (all_chunk _ _ 11 5 p11_11 (all_chunk _ _ 16 5 p11_16 (all_chunk _ _ 21 5 p11_21 (all_chunk _ _ 26 3 p11_26 (all_chunk _ _ 29 2 p11_29 (all_chunk _ _ 31 4 p11_31 (all_chunk _ _ 35 3 p11_35 (all_chunk _ _ 38 3 p11_38 (all_chunk _ _ 41 3 p11_41 (all_chunk _ _ 44 7 p11_44 (all_chunk _ _ 51 6 p11_51 (all_chunk _ _ 57 6 p11_57 (all_chunk _ _ 63 8 p11_63 (all_chunk _ _ 71 10 p11_71 (all_chunk _ _ 81 7 p11_81 (all_chunk _ _ 88 4 p11_88 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s11 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_0 : ((q12.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_6 : ((q12.drop 6).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_10 : ((q12.drop 10).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_12 : ((q12.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_15 : ((q12.drop 15).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_17 : ((q12.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_20 : ((q12.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_23 : ((q12.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_26 : ((q12.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_30 : ((q12.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_34 : ((q12.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_39 : ((q12.drop 39).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_45 : ((q12.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_49 : ((q12.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_52 : ((q12.drop 52).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_56 : ((q12.drop 56).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_63 : ((q12.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_66 : ((q12.drop 66).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_68 : ((q12.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_71 : ((q12.drop 71).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_74 : ((q12.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_77 : ((q12.drop 77).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_79 : ((q12.drop 79).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_82 : ((q12.drop 82).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_85 : ((q12.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_88 : ((q12.drop 88).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_89 : ((q12.drop 89).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_90 : ((q12.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_94 : ((q12.drop 94).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok12 : nopt 7 s12 = false := by
  have h : q12.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p12_0 (all_chunk _ _ 6 4 p12_6 (all_chunk _ _ 10 2 p12_10 (all_chunk _ _ 12 3 p12_12 (all_chunk _ _ 15 2 p12_15 (all_chunk _ _ 17 3 p12_17 (all_chunk _ _ 20 3 p12_20 (all_chunk _ _ 23 3 p12_23 (all_chunk _ _ 26 4 p12_26 (all_chunk _ _ 30 4 p12_30 (all_chunk _ _ 34 5 p12_34 (all_chunk _ _ 39 6 p12_39 (all_chunk _ _ 45 4 p12_45 (all_chunk _ _ 49 3 p12_49 (all_chunk _ _ 52 4 p12_52 (all_chunk _ _ 56 7 p12_56 (all_chunk _ _ 63 3 p12_63 (all_chunk _ _ 66 2 p12_66 (all_chunk _ _ 68 3 p12_68 (all_chunk _ _ 71 3 p12_71 (all_chunk _ _ 74 3 p12_74 (all_chunk _ _ 77 2 p12_77 (all_chunk _ _ 79 3 p12_79 (all_chunk _ _ 82 3 p12_82 (all_chunk _ _ 85 3 p12_85 (all_chunk _ _ 88 1 p12_88 (all_chunk _ _ 89 1 p12_89 (all_chunk _ _ 90 4 p12_90 (all_chunk _ _ 94 1 p12_94 (by decide +kernel))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s12 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_0 : ((q13.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_5 : ((q13.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_10 : ((q13.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_14 : ((q13.drop 14).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_17 : ((q13.drop 17).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_18 : ((q13.drop 18).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_19 : ((q13.drop 19).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_22 : ((q13.drop 22).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_24 : ((q13.drop 24).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_26 : ((q13.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_29 : ((q13.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_34 : ((q13.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_39 : ((q13.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_43 : ((q13.drop 43).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_45 : ((q13.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_49 : ((q13.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_54 : ((q13.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_59 : ((q13.drop 59).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_61 : ((q13.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_65 : ((q13.drop 65).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_66 : ((q13.drop 66).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_67 : ((q13.drop 67).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_69 : ((q13.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_72 : ((q13.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_75 : ((q13.drop 75).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_77 : ((q13.drop 77).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_79 : ((q13.drop 79).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_81 : ((q13.drop 81).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_84 : ((q13.drop 84).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_86 : ((q13.drop 86).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_88 : ((q13.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_90 : ((q13.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_92 : ((q13.drop 92).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok13 : nopt 7 s13 = false := by
  have h : q13.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p13_0 (all_chunk _ _ 5 5 p13_5 (all_chunk _ _ 10 4 p13_10 (all_chunk _ _ 14 3 p13_14 (all_chunk _ _ 17 1 p13_17 (all_chunk _ _ 18 1 p13_18 (all_chunk _ _ 19 3 p13_19 (all_chunk _ _ 22 2 p13_22 (all_chunk _ _ 24 2 p13_24 (all_chunk _ _ 26 3 p13_26 (all_chunk _ _ 29 5 p13_29 (all_chunk _ _ 34 5 p13_34 (all_chunk _ _ 39 4 p13_39 (all_chunk _ _ 43 2 p13_43 (all_chunk _ _ 45 4 p13_45 (all_chunk _ _ 49 5 p13_49 (all_chunk _ _ 54 5 p13_54 (all_chunk _ _ 59 2 p13_59 (all_chunk _ _ 61 4 p13_61 (all_chunk _ _ 65 1 p13_65 (all_chunk _ _ 66 1 p13_66 (all_chunk _ _ 67 2 p13_67 (all_chunk _ _ 69 3 p13_69 (all_chunk _ _ 72 3 p13_72 (all_chunk _ _ 75 2 p13_75 (all_chunk _ _ 77 2 p13_77 (all_chunk _ _ 79 2 p13_79 (all_chunk _ _ 81 3 p13_81 (all_chunk _ _ 84 2 p13_84 (all_chunk _ _ 86 2 p13_86 (all_chunk _ _ 88 2 p13_88 (all_chunk _ _ 90 2 p13_90 (all_chunk _ _ 92 3 p13_92 (by decide +kernel))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s13 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_0 : ((q14.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_3 : ((q14.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_6 : ((q14.drop 6).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_10 : ((q14.drop 10).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_15 : ((q14.drop 15).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_21 : ((q14.drop 21).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_26 : ((q14.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_29 : ((q14.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_31 : ((q14.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_34 : ((q14.drop 34).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_36 : ((q14.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_39 : ((q14.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_43 : ((q14.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_46 : ((q14.drop 46).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_55 : ((q14.drop 55).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_60 : ((q14.drop 60).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_65 : ((q14.drop 65).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_75 : ((q14.drop 75).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_85 : ((q14.drop 85).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_89 : ((q14.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok14 : nopt 7 s14 = false := by
  have h : q14.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p14_0 (all_chunk _ _ 3 3 p14_3 (all_chunk _ _ 6 4 p14_6 (all_chunk _ _ 10 5 p14_10 (all_chunk _ _ 15 6 p14_15 (all_chunk _ _ 21 5 p14_21 (all_chunk _ _ 26 3 p14_26 (all_chunk _ _ 29 2 p14_29 (all_chunk _ _ 31 3 p14_31 (all_chunk _ _ 34 2 p14_34 (all_chunk _ _ 36 3 p14_36 (all_chunk _ _ 39 4 p14_39 (all_chunk _ _ 43 3 p14_43 (all_chunk _ _ 46 9 p14_46 (all_chunk _ _ 55 5 p14_55 (all_chunk _ _ 60 5 p14_60 (all_chunk _ _ 65 10 p14_65 (all_chunk _ _ 75 10 p14_75 (all_chunk _ _ 85 4 p14_85 (all_chunk _ _ 89 3 p14_89 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s14 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_0 : ((q15.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_3 : ((q15.drop 3).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_7 : ((q15.drop 7).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_16 : ((q15.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_20 : ((q15.drop 20).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_26 : ((q15.drop 26).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_31 : ((q15.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_36 : ((q15.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_41 : ((q15.drop 41).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_44 : ((q15.drop 44).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_46 : ((q15.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_50 : ((q15.drop 50).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_53 : ((q15.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_56 : ((q15.drop 56).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_59 : ((q15.drop 59).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_61 : ((q15.drop 61).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_64 : ((q15.drop 64).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_73 : ((q15.drop 73).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_83 : ((q15.drop 83).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_88 : ((q15.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok15 : nopt 7 s15 = false := by
  have h : q15.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p15_0 (all_chunk _ _ 3 4 p15_3 (all_chunk _ _ 7 9 p15_7 (all_chunk _ _ 16 4 p15_16 (all_chunk _ _ 20 6 p15_20 (all_chunk _ _ 26 5 p15_26 (all_chunk _ _ 31 5 p15_31 (all_chunk _ _ 36 5 p15_36 (all_chunk _ _ 41 3 p15_41 (all_chunk _ _ 44 2 p15_44 (all_chunk _ _ 46 4 p15_46 (all_chunk _ _ 50 3 p15_50 (all_chunk _ _ 53 3 p15_53 (all_chunk _ _ 56 3 p15_56 (all_chunk _ _ 59 2 p15_59 (all_chunk _ _ 61 3 p15_61 (all_chunk _ _ 64 9 p15_64 (all_chunk _ _ 73 10 p15_73 (all_chunk _ _ 83 5 p15_83 (all_chunk _ _ 88 4 p15_88 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s15 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_0 : ((q16.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_2 : ((q16.drop 2).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_4 : ((q16.drop 4).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_5 : ((q16.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_8 : ((q16.drop 8).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_10 : ((q16.drop 10).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_12 : ((q16.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_16 : ((q16.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_20 : ((q16.drop 20).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_22 : ((q16.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_26 : ((q16.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_29 : ((q16.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_31 : ((q16.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_33 : ((q16.drop 33).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_35 : ((q16.drop 35).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_37 : ((q16.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_40 : ((q16.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_42 : ((q16.drop 42).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_44 : ((q16.drop 44).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_46 : ((q16.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_48 : ((q16.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_51 : ((q16.drop 51).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_53 : ((q16.drop 53).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_54 : ((q16.drop 54).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_57 : ((q16.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_59 : ((q16.drop 59).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_61 : ((q16.drop 61).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_64 : ((q16.drop 64).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_66 : ((q16.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_69 : ((q16.drop 69).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_71 : ((q16.drop 71).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_73 : ((q16.drop 73).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_75 : ((q16.drop 75).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_76 : ((q16.drop 76).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_78 : ((q16.drop 78).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_81 : ((q16.drop 81).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_85 : ((q16.drop 85).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_89 : ((q16.drop 89).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_93 : ((q16.drop 93).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_97 : ((q16.drop 97).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_101 : ((q16.drop 101).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok16 : nopt 7 s16 = false := by
  have h : q16.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p16_0 (all_chunk _ _ 2 2 p16_2 (all_chunk _ _ 4 1 p16_4 (all_chunk _ _ 5 3 p16_5 (all_chunk _ _ 8 2 p16_8 (all_chunk _ _ 10 2 p16_10 (all_chunk _ _ 12 4 p16_12 (all_chunk _ _ 16 4 p16_16 (all_chunk _ _ 20 2 p16_20 (all_chunk _ _ 22 4 p16_22 (all_chunk _ _ 26 3 p16_26 (all_chunk _ _ 29 2 p16_29 (all_chunk _ _ 31 2 p16_31 (all_chunk _ _ 33 2 p16_33 (all_chunk _ _ 35 2 p16_35 (all_chunk _ _ 37 3 p16_37 (all_chunk _ _ 40 2 p16_40 (all_chunk _ _ 42 2 p16_42 (all_chunk _ _ 44 2 p16_44 (all_chunk _ _ 46 2 p16_46 (all_chunk _ _ 48 3 p16_48 (all_chunk _ _ 51 2 p16_51 (all_chunk _ _ 53 1 p16_53 (all_chunk _ _ 54 3 p16_54 (all_chunk _ _ 57 2 p16_57 (all_chunk _ _ 59 2 p16_59 (all_chunk _ _ 61 3 p16_61 (all_chunk _ _ 64 2 p16_64 (all_chunk _ _ 66 3 p16_66 (all_chunk _ _ 69 2 p16_69 (all_chunk _ _ 71 2 p16_71 (all_chunk _ _ 73 2 p16_73 (all_chunk _ _ 75 1 p16_75 (all_chunk _ _ 76 2 p16_76 (all_chunk _ _ 78 3 p16_78 (all_chunk _ _ 81 4 p16_81 (all_chunk _ _ 85 4 p16_85 (all_chunk _ _ 89 4 p16_89 (all_chunk _ _ 93 4 p16_93 (all_chunk _ _ 97 4 p16_97 (all_chunk _ _ 101 2 p16_101 (by decide +kernel))))))))))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s16 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_0 : ((q17.drop 0).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_8 : ((q17.drop 8).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_13 : ((q17.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_18 : ((q17.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_21 : ((q17.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_25 : ((q17.drop 25).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_27 : ((q17.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_31 : ((q17.drop 31).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_39 : ((q17.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_43 : ((q17.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_46 : ((q17.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_48 : ((q17.drop 48).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_52 : ((q17.drop 52).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_60 : ((q17.drop 60).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_62 : ((q17.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_65 : ((q17.drop 65).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_67 : ((q17.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_71 : ((q17.drop 71).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_76 : ((q17.drop 76).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_79 : ((q17.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_83 : ((q17.drop 83).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_86 : ((q17.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_90 : ((q17.drop 90).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok17 : nopt 7 s17 = false := by
  have h : q17.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 8 p17_0 (all_chunk _ _ 8 5 p17_8 (all_chunk _ _ 13 5 p17_13 (all_chunk _ _ 18 3 p17_18 (all_chunk _ _ 21 4 p17_21 (all_chunk _ _ 25 2 p17_25 (all_chunk _ _ 27 4 p17_27 (all_chunk _ _ 31 8 p17_31 (all_chunk _ _ 39 4 p17_39 (all_chunk _ _ 43 3 p17_43 (all_chunk _ _ 46 2 p17_46 (all_chunk _ _ 48 4 p17_48 (all_chunk _ _ 52 8 p17_52 (all_chunk _ _ 60 2 p17_60 (all_chunk _ _ 62 3 p17_62 (all_chunk _ _ 65 2 p17_65 (all_chunk _ _ 67 4 p17_67 (all_chunk _ _ 71 5 p17_71 (all_chunk _ _ 76 3 p17_76 (all_chunk _ _ 79 4 p17_79 (all_chunk _ _ 83 3 p17_83 (all_chunk _ _ 86 4 p17_86 (all_chunk _ _ 90 1 p17_90 (by decide +kernel))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s17 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_0 : ((q18.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_7 : ((q18.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_12 : ((q18.drop 12).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_21 : ((q18.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_25 : ((q18.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_29 : ((q18.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_31 : ((q18.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_35 : ((q18.drop 35).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_40 : ((q18.drop 40).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_49 : ((q18.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_54 : ((q18.drop 54).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_57 : ((q18.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_59 : ((q18.drop 59).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_61 : ((q18.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_65 : ((q18.drop 65).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_70 : ((q18.drop 70).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_75 : ((q18.drop 75).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_83 : ((q18.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok18 : nopt 7 s18 = false := by
  have h : q18.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p18_0 (all_chunk _ _ 7 5 p18_7 (all_chunk _ _ 12 9 p18_12 (all_chunk _ _ 21 4 p18_21 (all_chunk _ _ 25 4 p18_25 (all_chunk _ _ 29 2 p18_29 (all_chunk _ _ 31 4 p18_31 (all_chunk _ _ 35 5 p18_35 (all_chunk _ _ 40 9 p18_40 (all_chunk _ _ 49 5 p18_49 (all_chunk _ _ 54 3 p18_54 (all_chunk _ _ 57 2 p18_57 (all_chunk _ _ 59 2 p18_59 (all_chunk _ _ 61 4 p18_61 (all_chunk _ _ 65 5 p18_65 (all_chunk _ _ 70 5 p18_70 (all_chunk _ _ 75 8 p18_75 (all_chunk _ _ 83 7 p18_83 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s18 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_0 : ((q19.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_5 : ((q19.drop 5).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_12 : ((q19.drop 12).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_21 : ((q19.drop 21).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_27 : ((q19.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_30 : ((q19.drop 30).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_32 : ((q19.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_34 : ((q19.drop 34).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_36 : ((q19.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_40 : ((q19.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_44 : ((q19.drop 44).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_47 : ((q19.drop 47).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_52 : ((q19.drop 52).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_57 : ((q19.drop 57).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_62 : ((q19.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_67 : ((q19.drop 67).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_76 : ((q19.drop 76).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_86 : ((q19.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok19 : nopt 7 s19 = false := by
  have h : q19.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p19_0 (all_chunk _ _ 5 7 p19_5 (all_chunk _ _ 12 9 p19_12 (all_chunk _ _ 21 6 p19_21 (all_chunk _ _ 27 3 p19_27 (all_chunk _ _ 30 2 p19_30 (all_chunk _ _ 32 2 p19_32 (all_chunk _ _ 34 2 p19_34 (all_chunk _ _ 36 4 p19_36 (all_chunk _ _ 40 4 p19_40 (all_chunk _ _ 44 3 p19_44 (all_chunk _ _ 47 5 p19_47 (all_chunk _ _ 52 5 p19_52 (all_chunk _ _ 57 5 p19_57 (all_chunk _ _ 62 5 p19_62 (all_chunk _ _ 67 9 p19_67 (all_chunk _ _ 76 10 p19_76 (all_chunk _ _ 86 4 p19_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s19 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_0 : ((q20.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_4 : ((q20.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_7 : ((q20.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_12 : ((q20.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_16 : ((q20.drop 16).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_21 : ((q20.drop 21).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_24 : ((q20.drop 24).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_27 : ((q20.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_31 : ((q20.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_35 : ((q20.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_39 : ((q20.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_43 : ((q20.drop 43).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_50 : ((q20.drop 50).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_59 : ((q20.drop 59).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_66 : ((q20.drop 66).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_73 : ((q20.drop 73).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_82 : ((q20.drop 82).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok20 : nopt 7 s20 = false := by
  have h : q20.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p20_0 (all_chunk _ _ 4 3 p20_4 (all_chunk _ _ 7 5 p20_7 (all_chunk _ _ 12 4 p20_12 (all_chunk _ _ 16 5 p20_16 (all_chunk _ _ 21 3 p20_21 (all_chunk _ _ 24 3 p20_24 (all_chunk _ _ 27 4 p20_27 (all_chunk _ _ 31 4 p20_31 (all_chunk _ _ 35 4 p20_35 (all_chunk _ _ 39 4 p20_39 (all_chunk _ _ 43 7 p20_43 (all_chunk _ _ 50 9 p20_50 (all_chunk _ _ 59 7 p20_59 (all_chunk _ _ 66 7 p20_66 (all_chunk _ _ 73 9 p20_73 (all_chunk _ _ 82 8 p20_82 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s20 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_0 : ((q21.drop 0).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_8 : ((q21.drop 8).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_15 : ((q21.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_18 : ((q21.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_21 : ((q21.drop 21).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_27 : ((q21.drop 27).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_34 : ((q21.drop 34).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_40 : ((q21.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_44 : ((q21.drop 44).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_53 : ((q21.drop 53).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_55 : ((q21.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_59 : ((q21.drop 59).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_61 : ((q21.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_69 : ((q21.drop 69).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_75 : ((q21.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_79 : ((q21.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_83 : ((q21.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_87 : ((q21.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok21 : nopt 7 s21 = false := by
  have h : q21.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 8 p21_0 (all_chunk _ _ 8 7 p21_8 (all_chunk _ _ 15 3 p21_15 (all_chunk _ _ 18 3 p21_18 (all_chunk _ _ 21 6 p21_21 (all_chunk _ _ 27 7 p21_27 (all_chunk _ _ 34 6 p21_34 (all_chunk _ _ 40 4 p21_40 (all_chunk _ _ 44 9 p21_44 (all_chunk _ _ 53 2 p21_53 (all_chunk _ _ 55 4 p21_55 (all_chunk _ _ 59 2 p21_59 (all_chunk _ _ 61 8 p21_61 (all_chunk _ _ 69 6 p21_69 (all_chunk _ _ 75 4 p21_75 (all_chunk _ _ 79 4 p21_79 (all_chunk _ _ 83 4 p21_83 (all_chunk _ _ 87 5 p21_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s21 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_0 : ((q22.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_5 : ((q22.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_10 : ((q22.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_13 : ((q22.drop 13).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_20 : ((q22.drop 20).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_28 : ((q22.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_32 : ((q22.drop 32).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_37 : ((q22.drop 37).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_42 : ((q22.drop 42).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_52 : ((q22.drop 52).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_56 : ((q22.drop 56).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_59 : ((q22.drop 59).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_64 : ((q22.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_68 : ((q22.drop 68).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_73 : ((q22.drop 73).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_77 : ((q22.drop 77).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_87 : ((q22.drop 87).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok22 : nopt 7 s22 = false := by
  have h : q22.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p22_0 (all_chunk _ _ 5 5 p22_5 (all_chunk _ _ 10 3 p22_10 (all_chunk _ _ 13 7 p22_13 (all_chunk _ _ 20 8 p22_20 (all_chunk _ _ 28 4 p22_28 (all_chunk _ _ 32 5 p22_32 (all_chunk _ _ 37 5 p22_37 (all_chunk _ _ 42 10 p22_42 (all_chunk _ _ 52 4 p22_52 (all_chunk _ _ 56 3 p22_56 (all_chunk _ _ 59 5 p22_59 (all_chunk _ _ 64 4 p22_64 (all_chunk _ _ 68 5 p22_68 (all_chunk _ _ 73 4 p22_73 (all_chunk _ _ 77 10 p22_77 (all_chunk _ _ 87 3 p22_87 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s22 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_0 : ((q23.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_4 : ((q23.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_7 : ((q23.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_12 : ((q23.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_17 : ((q23.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_20 : ((q23.drop 20).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_25 : ((q23.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_29 : ((q23.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_33 : ((q23.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_38 : ((q23.drop 38).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_43 : ((q23.drop 43).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_51 : ((q23.drop 51).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_60 : ((q23.drop 60).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_67 : ((q23.drop 67).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_76 : ((q23.drop 76).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_86 : ((q23.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok23 : nopt 7 s23 = false := by
  have h : q23.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p23_0 (all_chunk _ _ 4 3 p23_4 (all_chunk _ _ 7 5 p23_7 (all_chunk _ _ 12 5 p23_12 (all_chunk _ _ 17 3 p23_17 (all_chunk _ _ 20 5 p23_20 (all_chunk _ _ 25 4 p23_25 (all_chunk _ _ 29 4 p23_29 (all_chunk _ _ 33 5 p23_33 (all_chunk _ _ 38 5 p23_38 (all_chunk _ _ 43 8 p23_43 (all_chunk _ _ 51 9 p23_51 (all_chunk _ _ 60 7 p23_60 (all_chunk _ _ 67 9 p23_67 (all_chunk _ _ 76 10 p23_76 (all_chunk _ _ 86 6 p23_86 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s23 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_0 : ((q24.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_5 : ((q24.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_9 : ((q24.drop 9).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_16 : ((q24.drop 16).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_22 : ((q24.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_26 : ((q24.drop 26).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_31 : ((q24.drop 31).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_38 : ((q24.drop 38).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_45 : ((q24.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_49 : ((q24.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_52 : ((q24.drop 52).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_56 : ((q24.drop 56).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_60 : ((q24.drop 60).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_65 : ((q24.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_68 : ((q24.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_71 : ((q24.drop 71).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_79 : ((q24.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_88 : ((q24.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok24 : nopt 7 s24 = false := by
  have h : q24.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p24_0 (all_chunk _ _ 5 4 p24_5 (all_chunk _ _ 9 7 p24_9 (all_chunk _ _ 16 6 p24_16 (all_chunk _ _ 22 4 p24_22 (all_chunk _ _ 26 5 p24_26 (all_chunk _ _ 31 7 p24_31 (all_chunk _ _ 38 7 p24_38 (all_chunk _ _ 45 4 p24_45 (all_chunk _ _ 49 3 p24_49 (all_chunk _ _ 52 4 p24_52 (all_chunk _ _ 56 4 p24_56 (all_chunk _ _ 60 5 p24_60 (all_chunk _ _ 65 3 p24_65 (all_chunk _ _ 68 3 p24_68 (all_chunk _ _ 71 8 p24_71 (all_chunk _ _ 79 9 p24_79 (all_chunk _ _ 88 2 p24_88 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s24 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_0 : ((q25.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_9 : ((q25.drop 9).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_16 : ((q25.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_19 : ((q25.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_23 : ((q25.drop 23).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_30 : ((q25.drop 30).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_38 : ((q25.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_41 : ((q25.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_45 : ((q25.drop 45).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_54 : ((q25.drop 54).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_60 : ((q25.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_64 : ((q25.drop 64).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_66 : ((q25.drop 66).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_72 : ((q25.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_76 : ((q25.drop 76).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_80 : ((q25.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_83 : ((q25.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_87 : ((q25.drop 87).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_89 : ((q25.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok25 : nopt 7 s25 = false := by
  have h : q25.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p25_0 (all_chunk _ _ 9 7 p25_9 (all_chunk _ _ 16 3 p25_16 (all_chunk _ _ 19 4 p25_19 (all_chunk _ _ 23 7 p25_23 (all_chunk _ _ 30 8 p25_30 (all_chunk _ _ 38 3 p25_38 (all_chunk _ _ 41 4 p25_41 (all_chunk _ _ 45 9 p25_45 (all_chunk _ _ 54 6 p25_54 (all_chunk _ _ 60 4 p25_60 (all_chunk _ _ 64 2 p25_64 (all_chunk _ _ 66 6 p25_66 (all_chunk _ _ 72 4 p25_72 (all_chunk _ _ 76 4 p25_76 (all_chunk _ _ 80 3 p25_80 (all_chunk _ _ 83 4 p25_83 (all_chunk _ _ 87 2 p25_87 (all_chunk _ _ 89 3 p25_89 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s25 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_0 : ((q26.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_5 : ((q26.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_9 : ((q26.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_13 : ((q26.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_18 : ((q26.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_21 : ((q26.drop 21).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_24 : ((q26.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_29 : ((q26.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_33 : ((q26.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_36 : ((q26.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_41 : ((q26.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_45 : ((q26.drop 45).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_54 : ((q26.drop 54).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_61 : ((q26.drop 61).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_70 : ((q26.drop 70).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_79 : ((q26.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_88 : ((q26.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok26 : nopt 7 s26 = false := by
  have h : q26.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p26_0 (all_chunk _ _ 5 4 p26_5 (all_chunk _ _ 9 4 p26_9 (all_chunk _ _ 13 5 p26_13 (all_chunk _ _ 18 3 p26_18 (all_chunk _ _ 21 3 p26_21 (all_chunk _ _ 24 5 p26_24 (all_chunk _ _ 29 4 p26_29 (all_chunk _ _ 33 3 p26_33 (all_chunk _ _ 36 5 p26_36 (all_chunk _ _ 41 4 p26_41 (all_chunk _ _ 45 9 p26_45 (all_chunk _ _ 54 7 p26_54 (all_chunk _ _ 61 9 p26_61 (all_chunk _ _ 70 9 p26_70 (all_chunk _ _ 79 9 p26_79 (all_chunk _ _ 88 2 p26_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s26 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_0 : ((q27.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_5 : ((q27.drop 5).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_13 : ((q27.drop 13).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_22 : ((q27.drop 22).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_27 : ((q27.drop 27).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_32 : ((q27.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_34 : ((q27.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_39 : ((q27.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_42 : ((q27.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_46 : ((q27.drop 46).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_51 : ((q27.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_55 : ((q27.drop 55).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_58 : ((q27.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_63 : ((q27.drop 63).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_73 : ((q27.drop 73).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_83 : ((q27.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_91 : ((q27.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok27 : nopt 7 s27 = false := by
  have h : q27.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p27_0 (all_chunk _ _ 5 8 p27_5 (all_chunk _ _ 13 9 p27_13 (all_chunk _ _ 22 5 p27_22 (all_chunk _ _ 27 5 p27_27 (all_chunk _ _ 32 2 p27_32 (all_chunk _ _ 34 5 p27_34 (all_chunk _ _ 39 3 p27_39 (all_chunk _ _ 42 4 p27_42 (all_chunk _ _ 46 5 p27_46 (all_chunk _ _ 51 4 p27_51 (all_chunk _ _ 55 3 p27_55 (all_chunk _ _ 58 5 p27_58 (all_chunk _ _ 63 10 p27_63 (all_chunk _ _ 73 10 p27_73 (all_chunk _ _ 83 8 p27_83 (all_chunk _ _ 91 1 p27_91 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s27 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_0 : ((q28.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_4 : ((q28.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_7 : ((q28.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_12 : ((q28.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_16 : ((q28.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_19 : ((q28.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_23 : ((q28.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_27 : ((q28.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_31 : ((q28.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_35 : ((q28.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_39 : ((q28.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_43 : ((q28.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_49 : ((q28.drop 49).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_58 : ((q28.drop 58).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_65 : ((q28.drop 65).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_73 : ((q28.drop 73).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_82 : ((q28.drop 82).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_89 : ((q28.drop 89).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok28 : nopt 7 s28 = false := by
  have h : q28.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p28_0 (all_chunk _ _ 4 3 p28_4 (all_chunk _ _ 7 5 p28_7 (all_chunk _ _ 12 4 p28_12 (all_chunk _ _ 16 3 p28_16 (all_chunk _ _ 19 4 p28_19 (all_chunk _ _ 23 4 p28_23 (all_chunk _ _ 27 4 p28_27 (all_chunk _ _ 31 4 p28_31 (all_chunk _ _ 35 4 p28_35 (all_chunk _ _ 39 4 p28_39 (all_chunk _ _ 43 6 p28_43 (all_chunk _ _ 49 9 p28_49 (all_chunk _ _ 58 7 p28_58 (all_chunk _ _ 65 8 p28_65 (all_chunk _ _ 73 9 p28_73 (all_chunk _ _ 82 7 p28_82 (all_chunk _ _ 89 1 p28_89 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s28 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_0 : ((q29.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_9 : ((q29.drop 9).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_12 : ((q29.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_15 : ((q29.drop 15).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_21 : ((q29.drop 21).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_28 : ((q29.drop 28).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_34 : ((q29.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_37 : ((q29.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_40 : ((q29.drop 40).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_45 : ((q29.drop 45).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_54 : ((q29.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_59 : ((q29.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_63 : ((q29.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_67 : ((q29.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_71 : ((q29.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_75 : ((q29.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_79 : ((q29.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_87 : ((q29.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok29 : nopt 7 s29 = false := by
  have h : q29.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p29_0 (all_chunk _ _ 9 3 p29_9 (all_chunk _ _ 12 3 p29_12 (all_chunk _ _ 15 6 p29_15 (all_chunk _ _ 21 7 p29_21 (all_chunk _ _ 28 6 p29_28 (all_chunk _ _ 34 3 p29_34 (all_chunk _ _ 37 3 p29_37 (all_chunk _ _ 40 5 p29_40 (all_chunk _ _ 45 9 p29_45 (all_chunk _ _ 54 5 p29_54 (all_chunk _ _ 59 4 p29_59 (all_chunk _ _ 63 4 p29_63 (all_chunk _ _ 67 4 p29_67 (all_chunk _ _ 71 4 p29_71 (all_chunk _ _ 75 4 p29_75 (all_chunk _ _ 79 8 p29_79 (all_chunk _ _ 87 5 p29_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s29 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_0 : ((q30.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_2 : ((q30.drop 2).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_6 : ((q30.drop 6).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_9 : ((q30.drop 9).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_16 : ((q30.drop 16).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_25 : ((q30.drop 25).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_32 : ((q30.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_36 : ((q30.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_39 : ((q30.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_43 : ((q30.drop 43).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_47 : ((q30.drop 47).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_52 : ((q30.drop 52).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_56 : ((q30.drop 56).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_61 : ((q30.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_65 : ((q30.drop 65).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_73 : ((q30.drop 73).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_83 : ((q30.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok30 : nopt 7 s30 = false := by
  have h : q30.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p30_0 (all_chunk _ _ 2 4 p30_2 (all_chunk _ _ 6 3 p30_6 (all_chunk _ _ 9 7 p30_9 (all_chunk _ _ 16 9 p30_16 (all_chunk _ _ 25 7 p30_25 (all_chunk _ _ 32 4 p30_32 (all_chunk _ _ 36 3 p30_36 (all_chunk _ _ 39 4 p30_39 (all_chunk _ _ 43 4 p30_43 (all_chunk _ _ 47 5 p30_47 (all_chunk _ _ 52 4 p30_52 (all_chunk _ _ 56 5 p30_56 (all_chunk _ _ 61 4 p30_61 (all_chunk _ _ 65 8 p30_65 (all_chunk _ _ 73 10 p30_73 (all_chunk _ _ 83 7 p30_83 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s30 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_0 : ((q31.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_4 : ((q31.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_7 : ((q31.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_12 : ((q31.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_17 : ((q31.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_21 : ((q31.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_25 : ((q31.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_30 : ((q31.drop 30).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_35 : ((q31.drop 35).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_40 : ((q31.drop 40).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_45 : ((q31.drop 45).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_54 : ((q31.drop 54).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_62 : ((q31.drop 62).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_70 : ((q31.drop 70).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_80 : ((q31.drop 80).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_90 : ((q31.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok31 : nopt 7 s31 = false := by
  have h : q31.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p31_0 (all_chunk _ _ 4 3 p31_4 (all_chunk _ _ 7 5 p31_7 (all_chunk _ _ 12 5 p31_12 (all_chunk _ _ 17 4 p31_17 (all_chunk _ _ 21 4 p31_21 (all_chunk _ _ 25 5 p31_25 (all_chunk _ _ 30 5 p31_30 (all_chunk _ _ 35 5 p31_35 (all_chunk _ _ 40 5 p31_40 (all_chunk _ _ 45 9 p31_45 (all_chunk _ _ 54 8 p31_54 (all_chunk _ _ 62 8 p31_62 (all_chunk _ _ 70 10 p31_70 (all_chunk _ _ 80 10 p31_80 (all_chunk _ _ 90 2 p31_90 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s31 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_0 : ((q32.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_3 : ((q32.drop 3).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_8 : ((q32.drop 8).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_17 : ((q32.drop 17).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_24 : ((q32.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_28 : ((q32.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_31 : ((q32.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_36 : ((q32.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_40 : ((q32.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_44 : ((q32.drop 44).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_48 : ((q32.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_53 : ((q32.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_56 : ((q32.drop 56).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_59 : ((q32.drop 59).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_65 : ((q32.drop 65).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_74 : ((q32.drop 74).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_83 : ((q32.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok32 : nopt 7 s32 = false := by
  have h : q32.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p32_0 (all_chunk _ _ 3 5 p32_3 (all_chunk _ _ 8 9 p32_8 (all_chunk _ _ 17 7 p32_17 (all_chunk _ _ 24 4 p32_24 (all_chunk _ _ 28 3 p32_28 (all_chunk _ _ 31 5 p32_31 (all_chunk _ _ 36 4 p32_36 (all_chunk _ _ 40 4 p32_40 (all_chunk _ _ 44 4 p32_44 (all_chunk _ _ 48 5 p32_48 (all_chunk _ _ 53 3 p32_53 (all_chunk _ _ 56 3 p32_56 (all_chunk _ _ 59 6 p32_59 (all_chunk _ _ 65 9 p32_65 (all_chunk _ _ 74 9 p32_74 (all_chunk _ _ 83 7 p32_83 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s32 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_0 : ((q33.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_9 : ((q33.drop 9).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_16 : ((q33.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_19 : ((q33.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_23 : ((q33.drop 23).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_31 : ((q33.drop 31).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_40 : ((q33.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_42 : ((q33.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_46 : ((q33.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_48 : ((q33.drop 48).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_55 : ((q33.drop 55).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_62 : ((q33.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_65 : ((q33.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_69 : ((q33.drop 69).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_75 : ((q33.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_78 : ((q33.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_82 : ((q33.drop 82).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_85 : ((q33.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_88 : ((q33.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok33 : nopt 7 s33 = false := by
  have h : q33.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p33_0 (all_chunk _ _ 9 7 p33_9 (all_chunk _ _ 16 3 p33_16 (all_chunk _ _ 19 4 p33_19 (all_chunk _ _ 23 8 p33_23 (all_chunk _ _ 31 9 p33_31 (all_chunk _ _ 40 2 p33_40 (all_chunk _ _ 42 4 p33_42 (all_chunk _ _ 46 2 p33_46 (all_chunk _ _ 48 7 p33_48 (all_chunk _ _ 55 7 p33_55 (all_chunk _ _ 62 3 p33_62 (all_chunk _ _ 65 4 p33_65 (all_chunk _ _ 69 6 p33_69 (all_chunk _ _ 75 3 p33_75 (all_chunk _ _ 78 4 p33_78 (all_chunk _ _ 82 3 p33_82 (all_chunk _ _ 85 3 p33_85 (all_chunk _ _ 88 4 p33_88 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s33 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_0 : ((q34.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_5 : ((q34.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_10 : ((q34.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_13 : ((q34.drop 13).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_16 : ((q34.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_20 : ((q34.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_24 : ((q34.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_29 : ((q34.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_33 : ((q34.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_36 : ((q34.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_41 : ((q34.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_45 : ((q34.drop 45).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_54 : ((q34.drop 54).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_61 : ((q34.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_69 : ((q34.drop 69).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_79 : ((q34.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_88 : ((q34.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok34 : nopt 7 s34 = false := by
  have h : q34.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p34_0 (all_chunk _ _ 5 5 p34_5 (all_chunk _ _ 10 3 p34_10 (all_chunk _ _ 13 3 p34_13 (all_chunk _ _ 16 4 p34_16 (all_chunk _ _ 20 4 p34_20 (all_chunk _ _ 24 5 p34_24 (all_chunk _ _ 29 4 p34_29 (all_chunk _ _ 33 3 p34_33 (all_chunk _ _ 36 5 p34_36 (all_chunk _ _ 41 4 p34_41 (all_chunk _ _ 45 9 p34_45 (all_chunk _ _ 54 7 p34_54 (all_chunk _ _ 61 8 p34_61 (all_chunk _ _ 69 10 p34_69 (all_chunk _ _ 79 9 p34_79 (all_chunk _ _ 88 2 p34_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s34 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_0 : ((q35.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_7 : ((q35.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_12 : ((q35.drop 12).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_21 : ((q35.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_25 : ((q35.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_30 : ((q35.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_33 : ((q35.drop 33).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_39 : ((q35.drop 39).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_49 : ((q35.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_54 : ((q35.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_59 : ((q35.drop 59).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_64 : ((q35.drop 64).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_69 : ((q35.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_72 : ((q35.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_75 : ((q35.drop 75).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_83 : ((q35.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_91 : ((q35.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok35 : nopt 7 s35 = false := by
  have h : q35.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p35_0 (all_chunk _ _ 7 5 p35_7 (all_chunk _ _ 12 9 p35_12 (all_chunk _ _ 21 4 p35_21 (all_chunk _ _ 25 5 p35_25 (all_chunk _ _ 30 3 p35_30 (all_chunk _ _ 33 6 p35_33 (all_chunk _ _ 39 10 p35_39 (all_chunk _ _ 49 5 p35_49 (all_chunk _ _ 54 5 p35_54 (all_chunk _ _ 59 5 p35_59 (all_chunk _ _ 64 5 p35_64 (all_chunk _ _ 69 3 p35_69 (all_chunk _ _ 72 3 p35_72 (all_chunk _ _ 75 8 p35_75 (all_chunk _ _ 83 8 p35_83 (all_chunk _ _ 91 1 p35_91 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s35 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_0 : ((q36.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_3 : ((q36.drop 3).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_5 : ((q36.drop 5).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_7 : ((q36.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_10 : ((q36.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_13 : ((q36.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_17 : ((q36.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_20 : ((q36.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_23 : ((q36.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_27 : ((q36.drop 27).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_29 : ((q36.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_31 : ((q36.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_34 : ((q36.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_37 : ((q36.drop 37).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_39 : ((q36.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_42 : ((q36.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_45 : ((q36.drop 45).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_52 : ((q36.drop 52).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_55 : ((q36.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_59 : ((q36.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_62 : ((q36.drop 62).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_63 : ((q36.drop 63).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_64 : ((q36.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_68 : ((q36.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_71 : ((q36.drop 71).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_77 : ((q36.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_83 : ((q36.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_90 : ((q36.drop 90).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_93 : ((q36.drop 93).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok36 : nopt 7 s36 = false := by
  have h : q36.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p36_0 (all_chunk _ _ 3 2 p36_3 (all_chunk _ _ 5 2 p36_5 (all_chunk _ _ 7 3 p36_7 (all_chunk _ _ 10 3 p36_10 (all_chunk _ _ 13 4 p36_13 (all_chunk _ _ 17 3 p36_17 (all_chunk _ _ 20 3 p36_20 (all_chunk _ _ 23 4 p36_23 (all_chunk _ _ 27 2 p36_27 (all_chunk _ _ 29 2 p36_29 (all_chunk _ _ 31 3 p36_31 (all_chunk _ _ 34 3 p36_34 (all_chunk _ _ 37 2 p36_37 (all_chunk _ _ 39 3 p36_39 (all_chunk _ _ 42 3 p36_42 (all_chunk _ _ 45 7 p36_45 (all_chunk _ _ 52 3 p36_52 (all_chunk _ _ 55 4 p36_55 (all_chunk _ _ 59 3 p36_59 (all_chunk _ _ 62 1 p36_62 (all_chunk _ _ 63 1 p36_63 (all_chunk _ _ 64 4 p36_64 (all_chunk _ _ 68 3 p36_68 (all_chunk _ _ 71 6 p36_71 (all_chunk _ _ 77 6 p36_77 (all_chunk _ _ 83 7 p36_83 (all_chunk _ _ 90 3 p36_90 (all_chunk _ _ 93 2 p36_93 (by decide +kernel))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s36 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_0 : ((q37.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_5 : ((q37.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_10 : ((q37.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_13 : ((q37.drop 13).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_14 : ((q37.drop 14).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_15 : ((q37.drop 15).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_17 : ((q37.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_20 : ((q37.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_23 : ((q37.drop 23).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_25 : ((q37.drop 25).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_27 : ((q37.drop 27).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_29 : ((q37.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_32 : ((q37.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_34 : ((q37.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_39 : ((q37.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_44 : ((q37.drop 44).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_47 : ((q37.drop 47).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_49 : ((q37.drop 49).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_53 : ((q37.drop 53).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_58 : ((q37.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_63 : ((q37.drop 63).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_65 : ((q37.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_69 : ((q37.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_73 : ((q37.drop 73).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_74 : ((q37.drop 74).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_75 : ((q37.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_78 : ((q37.drop 78).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_80 : ((q37.drop 80).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_82 : ((q37.drop 82).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_85 : ((q37.drop 85).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_87 : ((q37.drop 87).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_89 : ((q37.drop 89).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_91 : ((q37.drop 91).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_93 : ((q37.drop 93).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok37 : nopt 7 s37 = false := by
  have h : q37.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p37_0 (all_chunk _ _ 5 5 p37_5 (all_chunk _ _ 10 3 p37_10 (all_chunk _ _ 13 1 p37_13 (all_chunk _ _ 14 1 p37_14 (all_chunk _ _ 15 2 p37_15 (all_chunk _ _ 17 3 p37_17 (all_chunk _ _ 20 3 p37_20 (all_chunk _ _ 23 2 p37_23 (all_chunk _ _ 25 2 p37_25 (all_chunk _ _ 27 2 p37_27 (all_chunk _ _ 29 3 p37_29 (all_chunk _ _ 32 2 p37_32 (all_chunk _ _ 34 5 p37_34 (all_chunk _ _ 39 5 p37_39 (all_chunk _ _ 44 3 p37_44 (all_chunk _ _ 47 2 p37_47 (all_chunk _ _ 49 4 p37_49 (all_chunk _ _ 53 5 p37_53 (all_chunk _ _ 58 5 p37_58 (all_chunk _ _ 63 2 p37_63 (all_chunk _ _ 65 4 p37_65 (all_chunk _ _ 69 4 p37_69 (all_chunk _ _ 73 1 p37_73 (all_chunk _ _ 74 1 p37_74 (all_chunk _ _ 75 3 p37_75 (all_chunk _ _ 78 2 p37_78 (all_chunk _ _ 80 2 p37_80 (all_chunk _ _ 82 3 p37_82 (all_chunk _ _ 85 2 p37_85 (all_chunk _ _ 87 2 p37_87 (all_chunk _ _ 89 2 p37_89 (all_chunk _ _ 91 2 p37_91 (all_chunk _ _ 93 2 p37_93 (by decide +kernel)))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s37 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_0 : ((q38.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_3 : ((q38.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_6 : ((q38.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_8 : ((q38.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_11 : ((q38.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_16 : ((q38.drop 16).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_21 : ((q38.drop 21).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_26 : ((q38.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_30 : ((q38.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_33 : ((q38.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_36 : ((q38.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_39 : ((q38.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_43 : ((q38.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_46 : ((q38.drop 46).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_55 : ((q38.drop 55).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_61 : ((q38.drop 61).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_67 : ((q38.drop 67).take 11).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_78 : ((q38.drop 78).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_87 : ((q38.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok38 : nopt 7 s38 = false := by
  have h : q38.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p38_0 (all_chunk _ _ 3 3 p38_3 (all_chunk _ _ 6 2 p38_6 (all_chunk _ _ 8 3 p38_8 (all_chunk _ _ 11 5 p38_11 (all_chunk _ _ 16 5 p38_16 (all_chunk _ _ 21 5 p38_21 (all_chunk _ _ 26 4 p38_26 (all_chunk _ _ 30 3 p38_30 (all_chunk _ _ 33 3 p38_33 (all_chunk _ _ 36 3 p38_36 (all_chunk _ _ 39 4 p38_39 (all_chunk _ _ 43 3 p38_43 (all_chunk _ _ 46 9 p38_46 (all_chunk _ _ 55 6 p38_55 (all_chunk _ _ 61 6 p38_61 (all_chunk _ _ 67 11 p38_67 (all_chunk _ _ 78 9 p38_78 (all_chunk _ _ 87 5 p38_87 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s38 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_0 : ((q39.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_9 : ((q39.drop 9).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_14 : ((q39.drop 14).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_16 : ((q39.drop 16).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_18 : ((q39.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_21 : ((q39.drop 21).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_24 : ((q39.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_28 : ((q39.drop 28).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_34 : ((q39.drop 34).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_42 : ((q39.drop 42).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_48 : ((q39.drop 48).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_58 : ((q39.drop 58).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_64 : ((q39.drop 64).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_70 : ((q39.drop 70).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_74 : ((q39.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_77 : ((q39.drop 77).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_82 : ((q39.drop 82).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_85 : ((q39.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_88 : ((q39.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_91 : ((q39.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok39 : nopt 7 s39 = false := by
  have h : q39.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p39_0 (all_chunk _ _ 9 5 p39_9 (all_chunk _ _ 14 2 p39_14 (all_chunk _ _ 16 2 p39_16 (all_chunk _ _ 18 3 p39_18 (all_chunk _ _ 21 3 p39_21 (all_chunk _ _ 24 4 p39_24 (all_chunk _ _ 28 6 p39_28 (all_chunk _ _ 34 8 p39_34 (all_chunk _ _ 42 6 p39_42 (all_chunk _ _ 48 10 p39_48 (all_chunk _ _ 58 6 p39_58 (all_chunk _ _ 64 6 p39_64 (all_chunk _ _ 70 4 p39_70 (all_chunk _ _ 74 3 p39_74 (all_chunk _ _ 77 5 p39_77 (all_chunk _ _ 82 3 p39_82 (all_chunk _ _ 85 3 p39_85 (all_chunk _ _ 88 3 p39_88 (all_chunk _ _ 91 1 p39_91 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s39 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

def inputs : List W := nums.map (BitVec.ofNat 500)

set_option maxRecDepth 16000 in
theorem nums_eq : inputs.map BitVec.toNat = nums := by decide +kernel

set_option maxRecDepth 16000 in
theorem front_eq : (allKids 7 nums).map isort = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39] := by decide +kernel

set_option maxRecDepth 16000 in
theorem noEight (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 inputs.toFinset) : False := by
  apply refute 7 inputs (by decide +kernel) _ _ t ht run
  · rw [nums_eq]
    decide +kernel
  · rw [nums_eq]
    have h : ((allKids 7 nums).map isort).all (fun c => !nopt 7 c) = true := by
      rw [front_eq]
      simp only [List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, Bool.not_false, Bool.true_and]
    exact List.all_eq_true.mpr fun c hc => (dead_eq 7 c).trans
      (List.all_eq_true.mp h (isort c) (List.mem_map.mpr ⟨c, hc, rfl⟩))
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 16000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 16000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 16000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 500 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 500)
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

set_option maxRecDepth 16000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 500) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 500) :
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
set_option maxRecDepth 16000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 500) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#500)[k.val] = false; simp
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

set_option maxRecDepth 16000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
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
set_option maxRecDepth 16000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
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
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def targetTable : ℕ := 4276808392 * 2 ^ 32 + 4276676800

def targetSix (x : Fin 6 → Bool) : Bool :=
  targetTable.testBit (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def related (x y : W) : Prop := x = y ∨ x = 0 ∨ x = ~~~0

set_option maxRecDepth 16000 in
theorem related_read {w v : List W} (h : List.Forall₂ related w v) (i : ℕ) :
    related (w.getD i 0) (v.getD i 0) := by
  induction h generalizing i with
  | nil => exact .inl rfl
  | cons hxy _ ih =>
    cases i with
    | zero => exact hxy
    | succ i => exact ih i

set_option maxRecDepth 16000 in
theorem related_not {x y : W} (h : related x y) : related (~~~x) (~~~y) := by
  rcases h with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr rfl)
  · exact .inr (.inl BitVec.not_not)

set_option maxRecDepth 16000 in
theorem related_and {av : Finset W} {x y x' y' : W}
    (hx : holds av x) (hy : holds av y) (rx : related x x') (ry : related y y') :
    related (x &&& y) (x' &&& y') ∨ holds av (x &&& y) := by
  rcases rx with rfl | rfl | rfl
  · rcases ry with rfl | rfl | rfl
    · exact .inl (.inl rfl)
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inr (.inl rfl)
    · rw [show x &&& ~~~(0 : W) = x from BitVec.and_allOnes]; exact .inr hx
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inr (.inl rfl)
  · rw [show ~~~(0 : W) &&& y = y from BitVec.allOnes_and]; exact .inr hy

set_option maxRecDepth 16000 in
theorem related_or {av : Finset W} {x y x' y' : W}
    (hx : holds av x) (hy : holds av y) (rx : related x x') (ry : related y y') :
    related (x ||| y) (x' ||| y') ∨ holds av (x ||| y) := by
  rcases related_and (holds_not hx) (holds_not hy) (related_not rx) (related_not ry) with h | h
  · exact .inl (by simpa only [BitVec.not_and, BitVec.not_not] using related_not h)
  · exact .inr (by simpa only [BitVec.not_and, BitVec.not_not] using holds_not h)

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem gate_related (w v : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (hr : List.Forall₂ related w v) (g : Gate) (hg : legal g) :
    related (action w g) (action v g) ∨ (isBinary g = true ∧ holds av (action w g)) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [isBinary, action, List.map_nil, List.map_cons, List.head?_nil, List.head?_cons,
      List.foldr_nil, List.foldr_cons, Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some, true_and, Bool.false_eq_true, false_and, or_false,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl rfl
    | exact .inl (related_read hr _)
    | exact related_not (related_read hr _)
    | exact related_and (available_read hw _) (available_read hw _) (related_read hr _) (related_read hr _)
    | exact related_or (available_read hw _) (available_read hw _) (related_read hr _) (related_read hr _)

def probe : Fin 500 := 1

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem compile_strict (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w v : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u) (hr : List.Forall₂ related w v)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal)
    (hd : (gs.foldl step (v.map (bit probe))).getD out false ≠ bit probe goal) :
    ∃ t m, (t = goal ∨ t = ~~~goal) ∧ m < binaryCost gs ∧ build basicOps t m av := by
  induction gs generalizing w v av with
  | nil =>
    have eq : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have r := related_read hr out
    rw [eq] at r
    rcases r with same | zero | ones
    · exact False.elim (hd (by simp only [List.foldl_nil, read_bit, ← same]))
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
  | cons g gs ih =>
    let z := action w g
    let z' := action v g
    have ok := hg g (by simp)
    have good (g' : Gate) (h : g' ∈ gs) := hg g' (by simp [h])
    have he' (k) : (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      simpa only [List.foldl_cons, action_spec w g ok] using he k
    have hd' : (gs.foldl step ((v ++ [z']).map (bit probe))).getD out false ≠ bit probe goal := by
      simpa only [List.foldl_cons, action_spec v g ok] using hd
    have extend (A : Finset W) (old : ∀ u ∈ w, holds A u) (new : holds A z) :
        ∀ u ∈ w ++ [z], holds A u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact old u h
      · exact List.mem_singleton.mp h ▸ new
    rcases gate_related w v av hw hr g ok with rr | ⟨cost, free⟩
    · have rr' : List.Forall₂ related (w ++ [z]) (v ++ [z']) := List.rel_append hr (.cons rr .nil)
      have cont (A : Finset W) (old : ∀ u ∈ w, holds A u) (new : holds A z) :=
        ih good (w ++ [z]) (v ++ [z']) A (extend A old new) rr' he' hd'
      have reach := gate_reach w av hw g ok
      cases cost : isBinary g
      · simp only [cost, Bool.false_eq_true, ite_false] at reach
        simpa [binaryCost, cost] using cont av hw reach
      · simp only [cost, ite_true] at reach
        have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, cost]
        rcases reach with old | ⟨a, ha, b, hb, ne, p, hop, hp⟩
        · obtain ⟨t, m, ht, hm, run⟩ := cont av hw old
          exact ⟨t, m, ht, by omega, run⟩
        · obtain ⟨t, m, ht, hm, run⟩ := cont (insert p av) (fun u hu => holds_insert (hw u hu)) hp
          exact ⟨t, m+1, ht, by omega, Or.inr ⟨a, ha, b, hb, ne, p, hop, run⟩⟩
    · obtain ⟨t, ht, run⟩ := compile gs out good (w ++ [z]) av (extend av hw free) he'
      exact ⟨t, binaryCost gs, ht, by simp [binaryCost, cost], run⟩

def restricted : List W := [(inputs.getD 0 0), (inputs.getD 1 0), (inputs.getD 2 0), (inputs.getD 3 0), (inputs.getD 4 0), 0]
def flipped : List W := [(inputs.getD 0 0), (inputs.getD 1 0), (inputs.getD 2 0), (inputs.getD 3 0), (inputs.getD 4 0), (~~~0)]

theorem rows_related : List.Forall₂ related restricted flipped := by
  unfold restricted flipped
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inr (.inl rfl)) ?_
  exact .nil

set_option maxRecDepth 8000 in
set_option maxRecDepth 16000 in
theorem restricted_rows : ∀ k : Fin 500,
    targetSix (fun i => bit k (restricted.getD i.val 0)) = bit k goal := by decide +kernel

set_option maxRecDepth 16000 in
theorem flipped_row : targetSix (fun i => bit probe (flipped.getD i.val 0)) ≠ bit probe goal := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem six_lower_bound (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = targetSix x) :
    9 < binaryCost gs := by
  have evalRow (ws : List W) (width : ws.length = 6) (k : Fin 500) :
      (gs.foldl step (ws.map (bit k))).getD out false =
        targetSix (fun i => bit k (ws.getD i.val 0)) := by
    let x (i : Fin 6) := bit k (ws.getD i.val 0)
    have same : List.ofFn x = ws.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ws.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,out⟩ (ws.map (bit k)) = targetSix x
    rw [← same, he]
  have available : ∀ u ∈ restricted, holds inputs.toFinset u := by
    intro u hu
    simp only [restricted, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inr ⟨(inputs.getD 0 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 1 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 2 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 3 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 4 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inl rfl
  obtain ⟨t, m, ht, hm, run⟩ := compile_strict gs out hg restricted flipped inputs.toFinset available
    rows_related (fun k => (evalRow restricted rfl k).trans (restricted_rows k))
    (by rw [evalRow flipped rfl]; exact flipped_row)
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  by_contra! small
  exact noEight t ht (lift (by omega) run)

def upperCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [10, 2]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.or, [14, 11]⟩,
    ⟨.and, [15, 12]⟩], 16⟩

set_option maxRecDepth 16000 in
theorem elevenGateUpper : PEqualNP.MetaComplexity.Monotone2 upperCircuit ∧ upperCircuit.size = 11 ∧
    ∀ x : Fin 6 → Bool, upperCircuit.eval (List.ofFn x) = targetSix x := by
  refine ⟨?_, by decide, ?_⟩
  · simp [upperCircuit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

end PEqualNP.Outside.L_meta_45558_aux

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_45558 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4276676800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4276676800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_45558_aux.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_45558_aux.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_45558_aux.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_45558_aux.six_lower_bound C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_45558_aux.upperCircuit, PEqualNP.Outside.L_meta_45558_aux.elevenGateUpper.1,
      ?_, PEqualNP.Outside.L_meta_45558_aux.elevenGateUpper.2.2⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
