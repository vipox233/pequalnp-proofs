import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41498_aux

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
def w0 : Nat := ((((((((0xb55db * 2^60 + 0x4beaeaede0fb76e) * 2^60 + 0xdc772bcd7557557) * 2^60 + 0xf0b766672d9c5f1) * 2^60 + 0x7c2ff093cf7712a) * 2^60 + 0x803c0707060f800) * 2^60 + 0x1fc001fc1fc1) * 2^60 + 0xfc3f000001c0078) * 2^60 + 0x1e07c0fc0071ddc)
def w1 : Nat := ((((((((0x7f3fd * 2^60 + 0xfdff7f742f7dbb6) * 2^60 + 0x3dbbf5d7bcfbeaf) * 2^60 + 0x7d5bbbfb56eeaba) * 2^60 + 0xbffcbd2e519fe03) * 2^60 + 0xc0000007f0000) * 2^60 + 0xfe00000000001) * 2^60 + 0xffc000003e00000) * 2^60 + 0x7ff00038001f)
def w2 : Nat := ((((((((0xecfeb * 2^60 + 0xdebfb21ef7bed1f) * 2^60 + 0x6edd66ebdeaf4fb) * 2^60 + 0xb66dcfad9bb537f) * 2^60 + 0xed555674ba7944c) * 2^60 + 0x7001807f800000) * 2^60 + 0x7f00000fe001ffe) * 2^60 + 0x3c000f80) * 2^60 + 0x1ff800001c0e1e0)
def w3 : Nat := ((((((((0xe3f5f * 2^60 + 0xef521fbf7bd8fdb) * 2^60 + 0xb76eb972f73df3d) * 2^60 + 0xdb8efcd6e3dffd4) * 2^60 + 0xd69a6bc93fa2870) * 2^60 + 0x38001ff8000003f) * 2^60 + 0x8000000ffffe000) * 2^60 + 0x3c0000fff) * 2^60 + 0xe0000000e00fe00)
def w4 : Nat := ((((((((0x1ff92 * 2^60 + 0x887bdbdfbdef1e3) * 2^60 + 0xc78f3e7ce7ce7ce) * 2^60 + 0xe3f0eee7ff19c67) * 2^60 + 0x18e383ffe444380) * 2^60 + 0x3fffe000000003f) * 2^60 + 0xfffffff00000000) * 2^60 + 0x3fffff000) * 2^60 + 0xfff0000)
def w5 : Nat := ((((((((0x351d9 * 2^60 + 0x49ea6a642079326) * 2^60 + 0x1c3321c53453407) * 2^60 + 0x70132263048c0b0) * 2^60 + 0x3c2cb0024117002) * 2^60 + 0x600000) * 2^60 + 0x1) * 2^60 + 0xfc0000000000000) * 2^60 + 0x7c000000001c)
def w6 : Nat := ((((((((0xff7ff * 2^60 + 0xfffffffdefffffe) * 2^60 + 0xfdffffdffdfffff) * 2^60 + 0xfdffffff7ffeffb) * 2^60 + 0xfffffdbfdffff2b) * 2^60 + 0x80fc070707ff800) * 2^60 + 0xfffc001fc1fc1) * 2^60 + 0xffff00003fc0078) * 2^60 + 0x1e07fffc03f1ddf)
def w7 : Nat := ((((((((0x80402 * 2^60 + 0x2008089c082448) * 2^60 + 0xc0440a084104150) * 2^60 + 0x80a444042910541) * 2^60 + 0x400340918e60128) * 2^60 + 0x803c0707000f800) * 2^60 + 0x1fc001fc1fc0) * 2^60 + 0x3f000001c0078) * 2^60 + 0x1e0000fc0071dc0)
def w8 : Nat := ((((((((0x4a224 * 2^60 + 0xb41515100f04890) * 2^60 + 0x2188d41288a8aa8) * 2^60 + 0xd4899985262a0a) * 2^60 + 0x83d00d2c1088e01) * 2^60 + 0xc0000001f0000) * 2^60 + 0xfe00000000000) * 2^60 + 0x3c000003e00000) * 2^60 + 0x3f000380003)
def w9 : Nat := ((((((((0xa45cb * 2^60 + 0x4aaaa20ce0ba50e) * 2^60 + 0x4c5522c95407453) * 2^60 + 0xb02546250994171) * 2^60 + 0x6c0550108a71008) * 2^60 + 0x70000000) * 2^60 + 0x1fc0) * 2^60 + 0x0) * 2^60 + 0x1e00000000001c0)
def w10 : Nat := ((((((((0xfdffb * 2^60 + 0xdffffafff7fff7f) * 2^60 + 0xfeff6fefffff5ff) * 2^60 + 0xf6ffefefbfbd7ff) * 2^60 + 0xfd7ff6f7ff7f56e) * 2^60 + 0x873c1f07fe0f800) * 2^60 + 0x7f01fc0fffc1fff) * 2^60 + 0xfc3f0003c1c0ff8) * 2^60 + 0x1fffc0fc1c7fdfc)
def w11 : Nat := ((((((((0x11010 * 2^60 + 0x14048e10041260) * 2^60 + 0x902209042150104) * 2^60 + 0x409220422408480) * 2^60 + 0x102aa0834506122) * 2^60 + 0x803c0700060f800) * 2^60 + 0x1fc001fc0001) * 2^60 + 0xfc3f000001c0078) * 2^60 + 0x7c0fc0071c1c)
def w12 : Nat := ((((((((0x48a20 * 2^60 + 0x941510121704811) * 2^60 + 0x228844228aa80a8) * 2^60 + 0x6488988922120e) * 2^60 + 0x815006643008444) * 2^60 + 0x7001800f800000) * 2^60 + 0x7f00000fe00003e) * 2^60 + 0x3c000f80) * 2^60 + 0x1f800001c0e020)
def w13 : Nat := ((((((((0xa155b * 2^60 + 0x4b420aad60d874a) * 2^60 + 0x946629407515515) * 2^60 + 0xd0866446219c5d0) * 2^60 + 0x540a60810f22020) * 2^60 + 0x7000000000) * 2^60 + 0x1fc0000) * 2^60 + 0x78) * 2^60 + 0x1c00)
def w14 : Nat := ((((((((0xf7fdf * 2^60 + 0xeffafffffbfbfff) * 2^60 + 0xff7fbbfff77ff7f) * 2^60 + 0xfbbffef7efdfff5) * 2^60 + 0xfebffbdbfff797a) * 2^60 + 0xb83c1fff060f83f) * 2^60 + 0x8001fc0ffffffc1) * 2^60 + 0xfc3f003c01c0fff) * 2^60 + 0xfe07c0fce07ffdc)
def w15 : Nat := ((((((((0x14080 * 2^60 + 0xa8e0408023024) * 2^60 + 0x4811028d0042042) * 2^60 + 0x203102210c00021) * 2^60 + 0x28259012c05510a) * 2^60 + 0x803c0007060f800) * 2^60 + 0x1fc000001fc1) * 2^60 + 0xfc3f000001c0000) * 2^60 + 0x1e07c0fc00701dc)
def w16 : Nat := ((((((((0x42a04 * 2^60 + 0xa41015121b00891) * 2^60 + 0x230890328228a28) * 2^60 + 0xb089890c243a04) * 2^60 + 0x82900b483080850) * 2^60 + 0x380018f8000003f) * 2^60 + 0x8000000fe03e000) * 2^60 + 0x3c0000f87) * 2^60 + 0xe0000000e00e200)
def w17 : Nat := ((((((((0x15592 * 2^60 + 0x86acacda0eb162) * 2^60 + 0xc4072a4c6546546) * 2^60 + 0xe0b066672d18461) * 2^60 + 0x18238093c444100) * 2^60 + 0x3c00000000000) * 2^60 + 0x1fc000000000) * 2^60 + 0x1c0000) * 2^60 + 0x70000)
def w18 : Nat := ((((((((0xbffdb * 2^60 + 0xcbfbfbfffdff7ef) * 2^60 + 0xdfff3ffdf7df7df) * 2^60 + 0xf3f7eee7ff9ddf7) * 2^60 + 0x7ceff3ffef773aa) * 2^60 + 0xbfffe707060f83f) * 2^60 + 0xfffffff01fc1fc1) * 2^60 + 0xfc3f003fffff078) * 2^60 + 0x1e07c0fcfff1ddc)
def w19 : Nat := ((((((((0xa0049 * 2^60 + 0x43802020401060c) * 2^60 + 0x187001811011011) * 2^60 + 0x100700000084190) * 2^60 + 0x640c70000b3302a) * 2^60 + 0x80000707060f800) * 2^60 + 0x1fc1fc1) * 2^60 + 0xfc3f00000000078) * 2^60 + 0x1e07c0fc0001ddc)
def w20 : Nat := ((((((((0xaa00 * 2^60 + 0x801111121d04081) * 2^60 + 0x38814308288288) * 2^60 + 0x3408880d201806) * 2^60 + 0xc0036c2000280) * 2^60 + 0x3fc3e000000003f) * 2^60 + 0xfffe03f00000000) * 2^60 + 0x3ffe3f000) * 2^60 + 0xff80000)
def w21 : Nat := ((((((((0x6c3e9 * 2^60 + 0xdcbf3214273c916) * 2^60 + 0x2c9964c39cab4ab) * 2^60 + 0x34498ba912a423a) * 2^60 + 0xad5414241019400) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w22 : Nat := ((((((((0xfffff * 2^60 + 0xffffff7efffffbf) * 2^60 + 0x7ffff7fffeffeff) * 2^60 + 0xff7fffffdfffbff) * 2^60 + 0xfffdff7efbffe4f) * 2^60 + 0x7c01807fff0000) * 2^60 + 0x7ffe000fe001fff) * 2^60 + 0xffc00003fe00f80) * 2^60 + 0x1fffff001f8e1ff)
def w23 : Nat := ((((((((0x13014 * 2^60 + 0x21404d6008412a0) * 2^60 + 0x112291142050a04) * 2^60 + 0x49123052444a880) * 2^60 + 0x12a8a90a4186a03) * 2^60 + 0xc0000007f0000) * 2^60 + 0xfe00000000001) * 2^60 + 0xffc000003e00000) * 2^60 + 0x7ff00038001f)
def w24 : Nat := ((((((((0x80c02 * 2^60 + 0x200800ad082409) * 2^60 + 0x424402284204050) * 2^60 + 0x822444048911145) * 2^60 + 0x40014250aa6004c) * 2^60 + 0x7001807f800000) * 2^60 + 0x7f00000fe001ffe) * 2^60 + 0x3c000f80) * 2^60 + 0x1ff800001c0e1e0)
def w25 : Nat := ((((((((0x6335d * 2^60 + 0xed521f342b58b92) * 2^60 + 0x352ab152b439e2d) * 2^60 + 0x590ab8d242cea90) * 2^60 + 0x969829081182800) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w26 : Nat := ((((((((0xfffff * 2^60 + 0xffff7fff7ffdfff) * 2^60 + 0xbffffdf7fffffbf) * 2^60 + 0xffdffffff7ffffe) * 2^60 + 0xfffeffef7fbfe73) * 2^60 + 0x38c01ff807f003f) * 2^60 + 0x80fe000ffffe001) * 2^60 + 0xffc0003c3e00fff) * 2^60 + 0xe007ff00e38fe1f)
def w27 : Nat := ((((((((0x1c0a0 * 2^60 + 0x10ad60400425024) * 2^60 + 0x891448508c2082) * 2^60 + 0x24510329142002a) * 2^60 + 0x29649426401d603) * 2^60 + 0xc0000007f0000) * 2^60 + 0xfe00000000001) * 2^60 + 0xffc000003e00000) * 2^60 + 0x7ff00038001f)
def w28 : Nat := ((((((((0x80c02 * 2^60 + 0x200008b5080449) * 2^60 + 0x824408204304110) * 2^60 + 0x82844404a111544) * 2^60 + 0x400242c12e20070) * 2^60 + 0x38001ff8000003f) * 2^60 + 0x8000000ffffe000) * 2^60 + 0x3c0000fff) * 2^60 + 0xe0000000e00fe00)
def w29 : Nat := ((((((((0x1f390 * 2^60 + 0x887b5b542d6d1a2) * 2^60 + 0x58b3454a4ca68e) * 2^60 + 0x6150aae35608822) * 2^60 + 0x18e0812e4004200) * 2^60 + 0xc000000000000) * 2^60 + 0xfe00000000000) * 2^60 + 0x3e00000) * 2^60 + 0x380000)
def w30 : Nat := ((((((((0x7ffff * 2^60 + 0xfdffffffbfffbf7) * 2^60 + 0xffbffffffffffef) * 2^60 + 0xfffbffffffffeff) * 2^60 + 0xbfffbffff5dff83) * 2^60 + 0x3fffe00007f003f) * 2^60 + 0xfffffff00000001) * 2^60 + 0xffc0003fffff000) * 2^60 + 0x7ff00fff001f)
def w31 : Nat := ((((((((0x6006d * 2^60 + 0x758424200210a14) * 2^60 + 0x3830c1831831821) * 2^60 + 0x1c0b111800e6298) * 2^60 + 0xa71c3c00119bc03) * 2^60 + 0x7f0000) * 2^60 + 0x1) * 2^60 + 0xffc000000000000) * 2^60 + 0x7ff00000001f)
def w32 : Nat := ((((((((0xc02 * 2^60 + 0x808b9082041) * 2^60 + 0xc2040a284304140) * 2^60 + 0x82a04404a911445) * 2^60 + 0x302d1a440180) * 2^60 + 0x3f3fe000000003f) * 2^60 + 0xff01fff00000000) * 2^60 + 0x3fc1ff000) * 2^60 + 0xfc70000)
def w33 : Nat := ((((((((0xe0f4b * 2^60 + 0xce12121e7398d1b) * 2^60 + 0x264c2062d62d439) * 2^60 + 0x920ccc848395354) * 2^60 + 0xc41042403a20040) * 2^60 + 0x18000000000) * 2^60 + 0xfe000000) * 2^60 + 0xf80) * 2^60 + 0xe000)
def w34 : Nat := ((((((((0xeffff * 2^60 + 0xffffbfbffffefdf) * 2^60 + 0xfffffffbffbffff) * 2^60 + 0xffeffffffbfffff) * 2^60 + 0xffdf7ffdbffbc7c) * 2^60 + 0x3f001ffff80003f) * 2^60 + 0xff00000fffffffe) * 2^60 + 0x3fc000fff) * 2^60 + 0xfff80000fc0ffe0)
def w35 : Nat := ((((((((0xc0a0 * 2^60 + 0x10ada0008426004) * 2^60 + 0x4891468908820c2) * 2^60 + 0x24610329182002b) * 2^60 + 0x29451434805940c) * 2^60 + 0x7000007f800000) * 2^60 + 0x7f0000000001ffe) * 2^60 + 0x3c000000) * 2^60 + 0x1ff800001c001e0)
def w36 : Nat := ((((((((0x3014 * 2^60 + 0x21400da108402c0) * 2^60 + 0x912299102110b04) * 2^60 + 0x49823052604ac80) * 2^60 + 0x128a29890582830) * 2^60 + 0x380007f8000003f) * 2^60 + 0x800000001ffe000) * 2^60 + 0x3c000007f) * 2^60 + 0xe0000000e001e00)
def w37 : Nat := ((((((((0xcf82 * 2^60 + 0x883b921eb5ae103) * 2^60 + 0x468d2668c68e4ca) * 2^60 + 0xa260cea59b11067) * 2^60 + 0x8410274a040000) * 2^60 + 0x70000000000000) * 2^60 + 0x7f0000000000000) * 2^60 + 0x3c000000) * 2^60 + 0x1c00000)
def w38 : Nat := ((((((((0xffffb * 2^60 + 0xdefffbdfffffdff) * 2^60 + 0xefdf7effffef7ff) * 2^60 + 0xf7fdefefffbdf7f) * 2^60 + 0xfdf7d7fffe7d7cc) * 2^60 + 0x3ffff807f80003f) * 2^60 + 0xffffffffe001ffe) * 2^60 + 0x3ffffff80) * 2^60 + 0x1ff80000fffe1e0)
def w39 : Nat := ((((((((0xe0069 * 2^60 + 0x568420004210c1c) * 2^60 + 0x285040831821031) * 2^60 + 0x140d010800a4318) * 2^60 + 0xe51454001a3944c) * 2^60 + 0x1807f800000) * 2^60 + 0xfe001ffe) * 2^60 + 0xf80) * 2^60 + 0x1ff80000000e1e0)
def w40 : Nat := ((((((((0x13010 * 2^60 + 0x4049c108410e0) * 2^60 + 0x810218142140304) * 2^60 + 0x419020426408c00) * 2^60 + 0x10a2818b4404380) * 2^60 + 0x38ffe000000003f) * 2^60 + 0x80fffff00000000) * 2^60 + 0x3c3fff000) * 2^60 + 0xe3f0000)
def w41 : Nat := ((((((((0x3f12 * 2^60 + 0x88521b9f39c81c3) * 2^60 + 0x870e3870e70c70c) * 2^60 + 0xc380ecc6e319c44) * 2^60 + 0x108203c92400000) * 2^60 + 0x38000000000003f) * 2^60 + 0x800000000000000) * 2^60 + 0x3c0000000) * 2^60 + 0xe000000)
def w42 : Nat := ((((((((0xfffdf * 2^60 + 0xef7bdfffffffffb) * 2^60 + 0xf7efbf7ef7fffff) * 2^60 + 0xfbfefef7ffdfff7) * 2^60 + 0xdefbebffffe6bf0) * 2^60 + 0x3ffffff8000003f) * 2^60 + 0xfffffffffffe000) * 2^60 + 0x3ffffffff) * 2^60 + 0xe0000000ffffe00)
def w43 : Nat := ((((((((0xe004d * 2^60 + 0x670004204210e18) * 2^60 + 0x306081021031831) * 2^60 + 0x180e101000c6390) * 2^60 + 0xc61868001ba2870) * 2^60 + 0x1ff80000000) * 2^60 + 0xffffe000) * 2^60 + 0xfff) * 2^60 + 0xe0000000000fe00)
def w44 : Nat := ((((((((0x1c080 * 2^60 + 0x29c0408427020) * 2^60 + 0x4081060c00c20c2) * 2^60 + 0x207002211c00023) * 2^60 + 0x8618036c044380) * 2^60 + 0x7ffe0000000000) * 2^60 + 0x7ffffff00000000) * 2^60 + 0x3ffff000) * 2^60 + 0x1ff0000)
def nums : List Nat := [w0,w1,w2,w3,w4]
def s0 : List Nat := [w4,w5,w1,w0,w3,w2]
def q0 := kidsL 6 s0
def s1 : List Nat := [w4,w1,w0,w3,w2,w6]
def q1 := kidsL 6 s1
def s2 : List Nat := [w4,w1,w7,w0,w3,w2]
def q2 := kidsL 6 s2
def s3 : List Nat := [w4,w8,w1,w0,w3,w2]
def q3 := kidsL 6 s3
def s4 : List Nat := [w4,w1,w9,w0,w3,w2]
def q4 := kidsL 6 s4
def s5 : List Nat := [w4,w1,w0,w3,w2,w10]
def q5 := kidsL 6 s5
def s6 : List Nat := [w11,w4,w1,w0,w3,w2]
def q6 := kidsL 6 s6
def s7 : List Nat := [w4,w12,w1,w0,w3,w2]
def q7 := kidsL 6 s7
def s8 : List Nat := [w4,w1,w13,w0,w3,w2]
def q8 := kidsL 6 s8
def s9 : List Nat := [w4,w1,w0,w3,w2,w14]
def q9 := kidsL 6 s9
def s10 : List Nat := [w15,w4,w1,w0,w3,w2]
def q10 := kidsL 6 s10
def s11 : List Nat := [w4,w16,w1,w0,w3,w2]
def q11 := kidsL 6 s11
def s12 : List Nat := [w17,w4,w1,w0,w3,w2]
def q12 := kidsL 6 s12
def s13 : List Nat := [w4,w1,w0,w18,w3,w2]
def q13 := kidsL 6 s13
def s14 : List Nat := [w4,w1,w19,w0,w3,w2]
def q14 := kidsL 6 s14
def s15 : List Nat := [w20,w4,w1,w0,w3,w2]
def q15 := kidsL 6 s15
def s16 : List Nat := [w4,w21,w1,w0,w3,w2]
def q16 := kidsL 6 s16
def s17 : List Nat := [w4,w1,w0,w3,w2,w22]
def q17 := kidsL 6 s17
def s18 : List Nat := [w23,w4,w1,w0,w3,w2]
def q18 := kidsL 6 s18
def s19 : List Nat := [w4,w1,w24,w0,w3,w2]
def q19 := kidsL 6 s19
def s20 : List Nat := [w4,w25,w1,w0,w3,w2]
def q20 := kidsL 6 s20
def s21 : List Nat := [w4,w1,w0,w3,w2,w26]
def q21 := kidsL 6 s21
def s22 : List Nat := [w27,w4,w1,w0,w3,w2]
def q22 := kidsL 6 s22
def s23 : List Nat := [w4,w1,w28,w0,w3,w2]
def q23 := kidsL 6 s23
def s24 : List Nat := [w29,w4,w1,w0,w3,w2]
def q24 := kidsL 6 s24
def s25 : List Nat := [w4,w1,w30,w0,w3,w2]
def q25 := kidsL 6 s25
def s26 : List Nat := [w4,w31,w1,w0,w3,w2]
def q26 := kidsL 6 s26
def s27 : List Nat := [w32,w4,w1,w0,w3,w2]
def q27 := kidsL 6 s27
def s28 : List Nat := [w4,w1,w0,w33,w3,w2]
def q28 := kidsL 6 s28
def s29 : List Nat := [w4,w1,w0,w3,w2,w34]
def q29 := kidsL 6 s29
def s30 : List Nat := [w35,w4,w1,w0,w3,w2]
def q30 := kidsL 6 s30
def s31 : List Nat := [w36,w4,w1,w0,w3,w2]
def q31 := kidsL 6 s31
def s32 : List Nat := [w37,w4,w1,w0,w3,w2]
def q32 := kidsL 6 s32
def s33 : List Nat := [w4,w1,w0,w3,w2,w38]
def q33 := kidsL 6 s33
def s34 : List Nat := [w4,w1,w0,w39,w3,w2]
def q34 := kidsL 6 s34
def s35 : List Nat := [w40,w4,w1,w0,w3,w2]
def q35 := kidsL 6 s35
def s36 : List Nat := [w41,w4,w1,w0,w3,w2]
def q36 := kidsL 6 s36
def s37 : List Nat := [w4,w1,w0,w3,w2,w42]
def q37 := kidsL 6 s37
def s38 : List Nat := [w4,w1,w0,w43,w3,w2]
def q38 := kidsL 6 s38
def s39 : List Nat := [w44,w4,w1,w0,w3,w2]
def q39 := kidsL 6 s39

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_0 : ((q0.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_2 : ((q0.drop 2).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_7 : ((q0.drop 7).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_14 : ((q0.drop 14).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_23 : ((q0.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_27 : ((q0.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_30 : ((q0.drop 30).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_32 : ((q0.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_36 : ((q0.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_40 : ((q0.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_43 : ((q0.drop 43).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_47 : ((q0.drop 47).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_51 : ((q0.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_55 : ((q0.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_59 : ((q0.drop 59).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_65 : ((q0.drop 65).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_72 : ((q0.drop 72).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_80 : ((q0.drop 80).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_88 : ((q0.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok0 : nopt 7 s0 = false := by
  have h : q0.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p0_0 (all_chunk _ _ 2 5 p0_2 (all_chunk _ _ 7 7 p0_7 (all_chunk _ _ 14 9 p0_14 (all_chunk _ _ 23 4 p0_23 (all_chunk _ _ 27 3 p0_27 (all_chunk _ _ 30 2 p0_30 (all_chunk _ _ 32 4 p0_32 (all_chunk _ _ 36 4 p0_36 (all_chunk _ _ 40 3 p0_40 (all_chunk _ _ 43 4 p0_43 (all_chunk _ _ 47 4 p0_47 (all_chunk _ _ 51 4 p0_51 (all_chunk _ _ 55 4 p0_55 (all_chunk _ _ 59 6 p0_59 (all_chunk _ _ 65 7 p0_65 (all_chunk _ _ 72 8 p0_72 (all_chunk _ _ 80 8 p0_80 (all_chunk _ _ 88 2 p0_88 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s0 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_0 : ((q1.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_5 : ((q1.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_10 : ((q1.drop 10).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_15 : ((q1.drop 15).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_21 : ((q1.drop 21).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_24 : ((q1.drop 24).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_30 : ((q1.drop 30).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_37 : ((q1.drop 37).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_43 : ((q1.drop 43).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_45 : ((q1.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_49 : ((q1.drop 49).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_55 : ((q1.drop 55).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_61 : ((q1.drop 61).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_66 : ((q1.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_69 : ((q1.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_72 : ((q1.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_76 : ((q1.drop 76).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_81 : ((q1.drop 81).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_84 : ((q1.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_88 : ((q1.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_91 : ((q1.drop 91).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_95 : ((q1.drop 95).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok1 : nopt 7 s1 = false := by
  have h : q1.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p1_0 (all_chunk _ _ 5 5 p1_5 (all_chunk _ _ 10 5 p1_10 (all_chunk _ _ 15 6 p1_15 (all_chunk _ _ 21 3 p1_21 (all_chunk _ _ 24 6 p1_24 (all_chunk _ _ 30 7 p1_30 (all_chunk _ _ 37 6 p1_37 (all_chunk _ _ 43 2 p1_43 (all_chunk _ _ 45 4 p1_45 (all_chunk _ _ 49 6 p1_49 (all_chunk _ _ 55 6 p1_55 (all_chunk _ _ 61 5 p1_61 (all_chunk _ _ 66 3 p1_66 (all_chunk _ _ 69 3 p1_69 (all_chunk _ _ 72 4 p1_72 (all_chunk _ _ 76 5 p1_76 (all_chunk _ _ 81 3 p1_81 (all_chunk _ _ 84 4 p1_84 (all_chunk _ _ 88 3 p1_88 (all_chunk _ _ 91 4 p1_91 (all_chunk _ _ 95 1 p1_95 (by decide +kernel)))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s1 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_0 : ((q2.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_6 : ((q2.drop 6).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_10 : ((q2.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_14 : ((q2.drop 14).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_23 : ((q2.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_27 : ((q2.drop 27).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_32 : ((q2.drop 32).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_35 : ((q2.drop 35).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_41 : ((q2.drop 41).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_48 : ((q2.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_54 : ((q2.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_58 : ((q2.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_61 : ((q2.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_65 : ((q2.drop 65).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_70 : ((q2.drop 70).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_74 : ((q2.drop 74).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_79 : ((q2.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_87 : ((q2.drop 87).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_95 : ((q2.drop 95).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok2 : nopt 7 s2 = false := by
  have h : q2.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p2_0 (all_chunk _ _ 6 4 p2_6 (all_chunk _ _ 10 4 p2_10 (all_chunk _ _ 14 9 p2_14 (all_chunk _ _ 23 4 p2_23 (all_chunk _ _ 27 5 p2_27 (all_chunk _ _ 32 3 p2_32 (all_chunk _ _ 35 6 p2_35 (all_chunk _ _ 41 7 p2_41 (all_chunk _ _ 48 6 p2_48 (all_chunk _ _ 54 4 p2_54 (all_chunk _ _ 58 3 p2_58 (all_chunk _ _ 61 4 p2_61 (all_chunk _ _ 65 5 p2_65 (all_chunk _ _ 70 4 p2_70 (all_chunk _ _ 74 5 p2_74 (all_chunk _ _ 79 8 p2_79 (all_chunk _ _ 87 8 p2_87 (all_chunk _ _ 95 1 p2_95 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s2 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_0 : ((q3.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_3 : ((q3.drop 3).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_5 : ((q3.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_8 : ((q3.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_11 : ((q3.drop 11).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_17 : ((q3.drop 17).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_24 : ((q3.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_29 : ((q3.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_32 : ((q3.drop 32).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_35 : ((q3.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_39 : ((q3.drop 39).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_41 : ((q3.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_45 : ((q3.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_48 : ((q3.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_51 : ((q3.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_55 : ((q3.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_59 : ((q3.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_63 : ((q3.drop 63).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_68 : ((q3.drop 68).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_74 : ((q3.drop 74).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_79 : ((q3.drop 79).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_85 : ((q3.drop 85).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_91 : ((q3.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok3 : nopt 7 s3 = false := by
  have h : q3.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p3_0 (all_chunk _ _ 3 2 p3_3 (all_chunk _ _ 5 3 p3_5 (all_chunk _ _ 8 3 p3_8 (all_chunk _ _ 11 6 p3_11 (all_chunk _ _ 17 7 p3_17 (all_chunk _ _ 24 5 p3_24 (all_chunk _ _ 29 3 p3_29 (all_chunk _ _ 32 3 p3_32 (all_chunk _ _ 35 4 p3_35 (all_chunk _ _ 39 2 p3_39 (all_chunk _ _ 41 4 p3_41 (all_chunk _ _ 45 3 p3_45 (all_chunk _ _ 48 3 p3_48 (all_chunk _ _ 51 4 p3_51 (all_chunk _ _ 55 4 p3_55 (all_chunk _ _ 59 4 p3_59 (all_chunk _ _ 63 5 p3_63 (all_chunk _ _ 68 6 p3_68 (all_chunk _ _ 74 5 p3_74 (all_chunk _ _ 79 6 p3_79 (all_chunk _ _ 85 6 p3_85 (all_chunk _ _ 91 3 p3_91 (by decide +kernel))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s3 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_0 : ((q4.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_5 : ((q4.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_9 : ((q4.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_13 : ((q4.drop 13).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_21 : ((q4.drop 21).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_27 : ((q4.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_31 : ((q4.drop 31).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_37 : ((q4.drop 37).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_43 : ((q4.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_49 : ((q4.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_52 : ((q4.drop 52).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_54 : ((q4.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_58 : ((q4.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_62 : ((q4.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_67 : ((q4.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_70 : ((q4.drop 70).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_72 : ((q4.drop 72).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_78 : ((q4.drop 78).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_84 : ((q4.drop 84).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok4 : nopt 7 s4 = false := by
  have h : q4.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p4_0 (all_chunk _ _ 5 4 p4_5 (all_chunk _ _ 9 4 p4_9 (all_chunk _ _ 13 8 p4_13 (all_chunk _ _ 21 6 p4_21 (all_chunk _ _ 27 4 p4_27 (all_chunk _ _ 31 6 p4_31 (all_chunk _ _ 37 6 p4_37 (all_chunk _ _ 43 6 p4_43 (all_chunk _ _ 49 3 p4_49 (all_chunk _ _ 52 2 p4_52 (all_chunk _ _ 54 4 p4_54 (all_chunk _ _ 58 4 p4_58 (all_chunk _ _ 62 5 p4_62 (all_chunk _ _ 67 3 p4_67 (all_chunk _ _ 70 2 p4_70 (all_chunk _ _ 72 6 p4_72 (all_chunk _ _ 78 6 p4_78 (all_chunk _ _ 84 8 p4_84 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s4 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_0 : ((q5.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_6 : ((q5.drop 6).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_13 : ((q5.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_17 : ((q5.drop 17).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_19 : ((q5.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_23 : ((q5.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_26 : ((q5.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_30 : ((q5.drop 30).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_35 : ((q5.drop 35).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_40 : ((q5.drop 40).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_45 : ((q5.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_48 : ((q5.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_53 : ((q5.drop 53).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_58 : ((q5.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_63 : ((q5.drop 63).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_65 : ((q5.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_69 : ((q5.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_73 : ((q5.drop 73).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_78 : ((q5.drop 78).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_81 : ((q5.drop 81).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_84 : ((q5.drop 84).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_87 : ((q5.drop 87).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_90 : ((q5.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_92 : ((q5.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok5 : nopt 7 s5 = false := by
  have h : q5.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p5_0 (all_chunk _ _ 6 7 p5_6 (all_chunk _ _ 13 4 p5_13 (all_chunk _ _ 17 2 p5_17 (all_chunk _ _ 19 4 p5_19 (all_chunk _ _ 23 3 p5_23 (all_chunk _ _ 26 4 p5_26 (all_chunk _ _ 30 5 p5_30 (all_chunk _ _ 35 5 p5_35 (all_chunk _ _ 40 5 p5_40 (all_chunk _ _ 45 3 p5_45 (all_chunk _ _ 48 5 p5_48 (all_chunk _ _ 53 5 p5_53 (all_chunk _ _ 58 5 p5_58 (all_chunk _ _ 63 2 p5_63 (all_chunk _ _ 65 4 p5_65 (all_chunk _ _ 69 4 p5_69 (all_chunk _ _ 73 5 p5_73 (all_chunk _ _ 78 3 p5_78 (all_chunk _ _ 81 3 p5_81 (all_chunk _ _ 84 3 p5_84 (all_chunk _ _ 87 3 p5_87 (all_chunk _ _ 90 2 p5_90 (all_chunk _ _ 92 4 p5_92 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s5 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_0 : ((q6.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_5 : ((q6.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_10 : ((q6.drop 10).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_15 : ((q6.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_19 : ((q6.drop 19).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_22 : ((q6.drop 22).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_24 : ((q6.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_29 : ((q6.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_34 : ((q6.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_37 : ((q6.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_41 : ((q6.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_45 : ((q6.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_53 : ((q6.drop 53).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_62 : ((q6.drop 62).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_70 : ((q6.drop 70).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_79 : ((q6.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_88 : ((q6.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok6 : nopt 7 s6 = false := by
  have h : q6.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p6_0 (all_chunk _ _ 5 5 p6_5 (all_chunk _ _ 10 5 p6_10 (all_chunk _ _ 15 4 p6_15 (all_chunk _ _ 19 3 p6_19 (all_chunk _ _ 22 2 p6_22 (all_chunk _ _ 24 5 p6_24 (all_chunk _ _ 29 5 p6_29 (all_chunk _ _ 34 3 p6_34 (all_chunk _ _ 37 4 p6_37 (all_chunk _ _ 41 4 p6_41 (all_chunk _ _ 45 8 p6_45 (all_chunk _ _ 53 9 p6_53 (all_chunk _ _ 62 8 p6_62 (all_chunk _ _ 70 9 p6_70 (all_chunk _ _ 79 9 p6_79 (all_chunk _ _ 88 4 p6_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s6 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_0 : ((q7.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_4 : ((q7.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_7 : ((q7.drop 7).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_13 : ((q7.drop 13).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_19 : ((q7.drop 19).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_27 : ((q7.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_31 : ((q7.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_35 : ((q7.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_39 : ((q7.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_43 : ((q7.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_46 : ((q7.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_50 : ((q7.drop 50).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_54 : ((q7.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_58 : ((q7.drop 58).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_60 : ((q7.drop 60).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_66 : ((q7.drop 66).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_73 : ((q7.drop 73).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_82 : ((q7.drop 82).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_89 : ((q7.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok7 : nopt 7 s7 = false := by
  have h : q7.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p7_0 (all_chunk _ _ 4 3 p7_4 (all_chunk _ _ 7 6 p7_7 (all_chunk _ _ 13 6 p7_13 (all_chunk _ _ 19 8 p7_19 (all_chunk _ _ 27 4 p7_27 (all_chunk _ _ 31 4 p7_31 (all_chunk _ _ 35 4 p7_35 (all_chunk _ _ 39 4 p7_39 (all_chunk _ _ 43 3 p7_43 (all_chunk _ _ 46 4 p7_46 (all_chunk _ _ 50 4 p7_50 (all_chunk _ _ 54 4 p7_54 (all_chunk _ _ 58 2 p7_58 (all_chunk _ _ 60 6 p7_60 (all_chunk _ _ 66 7 p7_66 (all_chunk _ _ 73 9 p7_73 (all_chunk _ _ 82 7 p7_82 (all_chunk _ _ 89 3 p7_89 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s7 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_0 : ((q8.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_5 : ((q8.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_9 : ((q8.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_13 : ((q8.drop 13).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_21 : ((q8.drop 21).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_27 : ((q8.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_31 : ((q8.drop 31).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_37 : ((q8.drop 37).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_43 : ((q8.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_49 : ((q8.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_52 : ((q8.drop 52).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_54 : ((q8.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_59 : ((q8.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_62 : ((q8.drop 62).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_64 : ((q8.drop 64).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_69 : ((q8.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_73 : ((q8.drop 73).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_79 : ((q8.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_87 : ((q8.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok8 : nopt 7 s8 = false := by
  have h : q8.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p8_0 (all_chunk _ _ 5 4 p8_5 (all_chunk _ _ 9 4 p8_9 (all_chunk _ _ 13 8 p8_13 (all_chunk _ _ 21 6 p8_21 (all_chunk _ _ 27 4 p8_27 (all_chunk _ _ 31 6 p8_31 (all_chunk _ _ 37 6 p8_37 (all_chunk _ _ 43 6 p8_43 (all_chunk _ _ 49 3 p8_49 (all_chunk _ _ 52 2 p8_52 (all_chunk _ _ 54 5 p8_54 (all_chunk _ _ 59 3 p8_59 (all_chunk _ _ 62 2 p8_62 (all_chunk _ _ 64 5 p8_64 (all_chunk _ _ 69 4 p8_69 (all_chunk _ _ 73 6 p8_73 (all_chunk _ _ 79 8 p8_79 (all_chunk _ _ 87 5 p8_87 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s8 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_0 : ((q9.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_6 : ((q9.drop 6).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_13 : ((q9.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_17 : ((q9.drop 17).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_19 : ((q9.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_23 : ((q9.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_26 : ((q9.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_30 : ((q9.drop 30).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_35 : ((q9.drop 35).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_40 : ((q9.drop 40).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_45 : ((q9.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_48 : ((q9.drop 48).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_52 : ((q9.drop 52).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_58 : ((q9.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_63 : ((q9.drop 63).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_65 : ((q9.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_69 : ((q9.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_73 : ((q9.drop 73).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_78 : ((q9.drop 78).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_80 : ((q9.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_84 : ((q9.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_88 : ((q9.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_91 : ((q9.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_94 : ((q9.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok9 : nopt 7 s9 = false := by
  have h : q9.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p9_0 (all_chunk _ _ 6 7 p9_6 (all_chunk _ _ 13 4 p9_13 (all_chunk _ _ 17 2 p9_17 (all_chunk _ _ 19 4 p9_19 (all_chunk _ _ 23 3 p9_23 (all_chunk _ _ 26 4 p9_26 (all_chunk _ _ 30 5 p9_30 (all_chunk _ _ 35 5 p9_35 (all_chunk _ _ 40 5 p9_40 (all_chunk _ _ 45 3 p9_45 (all_chunk _ _ 48 4 p9_48 (all_chunk _ _ 52 6 p9_52 (all_chunk _ _ 58 5 p9_58 (all_chunk _ _ 63 2 p9_63 (all_chunk _ _ 65 4 p9_65 (all_chunk _ _ 69 4 p9_69 (all_chunk _ _ 73 5 p9_73 (all_chunk _ _ 78 2 p9_78 (all_chunk _ _ 80 4 p9_80 (all_chunk _ _ 84 4 p9_84 (all_chunk _ _ 88 3 p9_88 (all_chunk _ _ 91 3 p9_91 (all_chunk _ _ 94 2 p9_94 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s9 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_0 : ((q10.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_5 : ((q10.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_10 : ((q10.drop 10).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_15 : ((q10.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_19 : ((q10.drop 19).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_22 : ((q10.drop 22).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_24 : ((q10.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_28 : ((q10.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_32 : ((q10.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_36 : ((q10.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_39 : ((q10.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_44 : ((q10.drop 44).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_51 : ((q10.drop 51).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_60 : ((q10.drop 60).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_69 : ((q10.drop 69).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_78 : ((q10.drop 78).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_86 : ((q10.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok10 : nopt 7 s10 = false := by
  have h : q10.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p10_0 (all_chunk _ _ 5 5 p10_5 (all_chunk _ _ 10 5 p10_10 (all_chunk _ _ 15 4 p10_15 (all_chunk _ _ 19 3 p10_19 (all_chunk _ _ 22 2 p10_22 (all_chunk _ _ 24 4 p10_24 (all_chunk _ _ 28 4 p10_28 (all_chunk _ _ 32 4 p10_32 (all_chunk _ _ 36 3 p10_36 (all_chunk _ _ 39 5 p10_39 (all_chunk _ _ 44 7 p10_44 (all_chunk _ _ 51 9 p10_51 (all_chunk _ _ 60 9 p10_60 (all_chunk _ _ 69 9 p10_69 (all_chunk _ _ 78 8 p10_78 (all_chunk _ _ 86 6 p10_86 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s10 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_0 : ((q11.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_4 : ((q11.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_7 : ((q11.drop 7).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_13 : ((q11.drop 13).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_19 : ((q11.drop 19).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_27 : ((q11.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_31 : ((q11.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_35 : ((q11.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_39 : ((q11.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_43 : ((q11.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_46 : ((q11.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_50 : ((q11.drop 50).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_52 : ((q11.drop 52).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_57 : ((q11.drop 57).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_61 : ((q11.drop 61).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_67 : ((q11.drop 67).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_75 : ((q11.drop 75).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_83 : ((q11.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_91 : ((q11.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok11 : nopt 7 s11 = false := by
  have h : q11.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p11_0 (all_chunk _ _ 4 3 p11_4 (all_chunk _ _ 7 6 p11_7 (all_chunk _ _ 13 6 p11_13 (all_chunk _ _ 19 8 p11_19 (all_chunk _ _ 27 4 p11_27 (all_chunk _ _ 31 4 p11_31 (all_chunk _ _ 35 4 p11_35 (all_chunk _ _ 39 4 p11_39 (all_chunk _ _ 43 3 p11_43 (all_chunk _ _ 46 4 p11_46 (all_chunk _ _ 50 2 p11_50 (all_chunk _ _ 52 5 p11_52 (all_chunk _ _ 57 4 p11_57 (all_chunk _ _ 61 6 p11_61 (all_chunk _ _ 67 8 p11_67 (all_chunk _ _ 75 8 p11_75 (all_chunk _ _ 83 8 p11_83 (all_chunk _ _ 91 1 p11_91 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s11 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_0 : ((q12.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_3 : ((q12.drop 3).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_5 : ((q12.drop 5).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_7 : ((q12.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_11 : ((q12.drop 11).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_13 : ((q12.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

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
theorem p12_30 : ((q12.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_33 : ((q12.drop 33).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_37 : ((q12.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_40 : ((q12.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_42 : ((q12.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_46 : ((q12.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_48 : ((q12.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_53 : ((q12.drop 53).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_54 : ((q12.drop 54).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_56 : ((q12.drop 56).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_61 : ((q12.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_65 : ((q12.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_68 : ((q12.drop 68).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_73 : ((q12.drop 73).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_75 : ((q12.drop 75).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_80 : ((q12.drop 80).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_85 : ((q12.drop 85).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_89 : ((q12.drop 89).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_93 : ((q12.drop 93).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_97 : ((q12.drop 97).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_101 : ((q12.drop 101).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok12 : nopt 7 s12 = false := by
  have h : q12.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p12_0 (all_chunk _ _ 3 2 p12_3 (all_chunk _ _ 5 2 p12_5 (all_chunk _ _ 7 4 p12_7 (all_chunk _ _ 11 2 p12_11 (all_chunk _ _ 13 4 p12_13 (all_chunk _ _ 17 3 p12_17 (all_chunk _ _ 20 3 p12_20 (all_chunk _ _ 23 3 p12_23 (all_chunk _ _ 26 4 p12_26 (all_chunk _ _ 30 3 p12_30 (all_chunk _ _ 33 4 p12_33 (all_chunk _ _ 37 3 p12_37 (all_chunk _ _ 40 2 p12_40 (all_chunk _ _ 42 4 p12_42 (all_chunk _ _ 46 2 p12_46 (all_chunk _ _ 48 5 p12_48 (all_chunk _ _ 53 1 p12_53 (all_chunk _ _ 54 2 p12_54 (all_chunk _ _ 56 5 p12_56 (all_chunk _ _ 61 4 p12_61 (all_chunk _ _ 65 3 p12_65 (all_chunk _ _ 68 5 p12_68 (all_chunk _ _ 73 2 p12_73 (all_chunk _ _ 75 5 p12_75 (all_chunk _ _ 80 5 p12_80 (all_chunk _ _ 85 4 p12_85 (all_chunk _ _ 89 4 p12_89 (all_chunk _ _ 93 4 p12_93 (all_chunk _ _ 97 4 p12_97 (all_chunk _ _ 101 2 p12_101 (by decide +kernel))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s12 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_0 : ((q13.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_5 : ((q13.drop 5).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_7 : ((q13.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_12 : ((q13.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_15 : ((q13.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_18 : ((q13.drop 18).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_20 : ((q13.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_24 : ((q13.drop 24).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_31 : ((q13.drop 31).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_37 : ((q13.drop 37).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_39 : ((q13.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_42 : ((q13.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_45 : ((q13.drop 45).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_51 : ((q13.drop 51).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_54 : ((q13.drop 54).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_57 : ((q13.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_59 : ((q13.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_63 : ((q13.drop 63).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_70 : ((q13.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_73 : ((q13.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_76 : ((q13.drop 76).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_78 : ((q13.drop 78).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_80 : ((q13.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_84 : ((q13.drop 84).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_86 : ((q13.drop 86).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_89 : ((q13.drop 89).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok13 : nopt 7 s13 = false := by
  have h : q13.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p13_0 (all_chunk _ _ 5 2 p13_5 (all_chunk _ _ 7 5 p13_7 (all_chunk _ _ 12 3 p13_12 (all_chunk _ _ 15 3 p13_15 (all_chunk _ _ 18 2 p13_18 (all_chunk _ _ 20 4 p13_20 (all_chunk _ _ 24 7 p13_24 (all_chunk _ _ 31 6 p13_31 (all_chunk _ _ 37 2 p13_37 (all_chunk _ _ 39 3 p13_39 (all_chunk _ _ 42 3 p13_42 (all_chunk _ _ 45 6 p13_45 (all_chunk _ _ 51 3 p13_51 (all_chunk _ _ 54 3 p13_54 (all_chunk _ _ 57 2 p13_57 (all_chunk _ _ 59 4 p13_59 (all_chunk _ _ 63 7 p13_63 (all_chunk _ _ 70 3 p13_70 (all_chunk _ _ 73 3 p13_73 (all_chunk _ _ 76 2 p13_76 (all_chunk _ _ 78 2 p13_78 (all_chunk _ _ 80 4 p13_80 (all_chunk _ _ 84 2 p13_84 (all_chunk _ _ 86 3 p13_86 (all_chunk _ _ 89 2 p13_89 (by decide +kernel)))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s13 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_0 : ((q14.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_6 : ((q14.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_8 : ((q14.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_12 : ((q14.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_15 : ((q14.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_19 : ((q14.drop 19).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_26 : ((q14.drop 26).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_34 : ((q14.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_39 : ((q14.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_43 : ((q14.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_49 : ((q14.drop 49).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_58 : ((q14.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_61 : ((q14.drop 61).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_64 : ((q14.drop 64).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_67 : ((q14.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_71 : ((q14.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_75 : ((q14.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_79 : ((q14.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_83 : ((q14.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_91 : ((q14.drop 91).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok14 : nopt 7 s14 = false := by
  have h : q14.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p14_0 (all_chunk _ _ 6 2 p14_6 (all_chunk _ _ 8 4 p14_8 (all_chunk _ _ 12 3 p14_12 (all_chunk _ _ 15 4 p14_15 (all_chunk _ _ 19 7 p14_19 (all_chunk _ _ 26 8 p14_26 (all_chunk _ _ 34 5 p14_34 (all_chunk _ _ 39 4 p14_39 (all_chunk _ _ 43 6 p14_43 (all_chunk _ _ 49 9 p14_49 (all_chunk _ _ 58 3 p14_58 (all_chunk _ _ 61 3 p14_61 (all_chunk _ _ 64 3 p14_64 (all_chunk _ _ 67 4 p14_67 (all_chunk _ _ 71 4 p14_71 (all_chunk _ _ 75 4 p14_75 (all_chunk _ _ 79 4 p14_79 (all_chunk _ _ 83 8 p14_83 (all_chunk _ _ 91 5 p14_91 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s14 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_0 : ((q15.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_3 : ((q15.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_6 : ((q15.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_8 : ((q15.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_11 : ((q15.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_15 : ((q15.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_19 : ((q15.drop 19).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_21 : ((q15.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_25 : ((q15.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_28 : ((q15.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_31 : ((q15.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_35 : ((q15.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_39 : ((q15.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_43 : ((q15.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_49 : ((q15.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_54 : ((q15.drop 54).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_62 : ((q15.drop 62).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_69 : ((q15.drop 69).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_77 : ((q15.drop 77).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_86 : ((q15.drop 86).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_94 : ((q15.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok15 : nopt 7 s15 = false := by
  have h : q15.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p15_0 (all_chunk _ _ 3 3 p15_3 (all_chunk _ _ 6 2 p15_6 (all_chunk _ _ 8 3 p15_8 (all_chunk _ _ 11 4 p15_11 (all_chunk _ _ 15 4 p15_15 (all_chunk _ _ 19 2 p15_19 (all_chunk _ _ 21 4 p15_21 (all_chunk _ _ 25 3 p15_25 (all_chunk _ _ 28 3 p15_28 (all_chunk _ _ 31 4 p15_31 (all_chunk _ _ 35 4 p15_35 (all_chunk _ _ 39 4 p15_39 (all_chunk _ _ 43 6 p15_43 (all_chunk _ _ 49 5 p15_49 (all_chunk _ _ 54 8 p15_54 (all_chunk _ _ 62 7 p15_62 (all_chunk _ _ 69 8 p15_69 (all_chunk _ _ 77 9 p15_77 (all_chunk _ _ 86 8 p15_86 (all_chunk _ _ 94 2 p15_94 (by decide +kernel))))))))))))))))))))))
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
theorem p16_4 : ((q16.drop 4).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_6 : ((q16.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_8 : ((q16.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_11 : ((q16.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_14 : ((q16.drop 14).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_18 : ((q16.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

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
theorem p16_35 : ((q16.drop 35).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_38 : ((q16.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_41 : ((q16.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_43 : ((q16.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_46 : ((q16.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_48 : ((q16.drop 48).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_50 : ((q16.drop 50).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_52 : ((q16.drop 52).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_54 : ((q16.drop 54).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_56 : ((q16.drop 56).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

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
theorem p16_66 : ((q16.drop 66).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_68 : ((q16.drop 68).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_70 : ((q16.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_73 : ((q16.drop 73).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_77 : ((q16.drop 77).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_80 : ((q16.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_83 : ((q16.drop 83).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_88 : ((q16.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_92 : ((q16.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_96 : ((q16.drop 96).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_100 : ((q16.drop 100).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok16 : nopt 7 s16 = false := by
  have h : q16.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p16_0 (all_chunk _ _ 2 2 p16_2 (all_chunk _ _ 4 2 p16_4 (all_chunk _ _ 6 2 p16_6 (all_chunk _ _ 8 3 p16_8 (all_chunk _ _ 11 3 p16_11 (all_chunk _ _ 14 4 p16_14 (all_chunk _ _ 18 4 p16_18 (all_chunk _ _ 22 4 p16_22 (all_chunk _ _ 26 3 p16_26 (all_chunk _ _ 29 2 p16_29 (all_chunk _ _ 31 2 p16_31 (all_chunk _ _ 33 2 p16_33 (all_chunk _ _ 35 3 p16_35 (all_chunk _ _ 38 3 p16_38 (all_chunk _ _ 41 2 p16_41 (all_chunk _ _ 43 3 p16_43 (all_chunk _ _ 46 2 p16_46 (all_chunk _ _ 48 2 p16_48 (all_chunk _ _ 50 2 p16_50 (all_chunk _ _ 52 2 p16_52 (all_chunk _ _ 54 2 p16_54 (all_chunk _ _ 56 3 p16_56 (all_chunk _ _ 59 2 p16_59 (all_chunk _ _ 61 3 p16_61 (all_chunk _ _ 64 2 p16_64 (all_chunk _ _ 66 2 p16_66 (all_chunk _ _ 68 2 p16_68 (all_chunk _ _ 70 3 p16_70 (all_chunk _ _ 73 4 p16_73 (all_chunk _ _ 77 3 p16_77 (all_chunk _ _ 80 3 p16_80 (all_chunk _ _ 83 5 p16_83 (all_chunk _ _ 88 4 p16_88 (all_chunk _ _ 92 4 p16_92 (all_chunk _ _ 96 4 p16_96 (all_chunk _ _ 100 2 p16_100 (by decide +kernel))))))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s16 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_0 : ((q17.drop 0).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_8 : ((q17.drop 8).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_17 : ((q17.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_21 : ((q17.drop 21).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_28 : ((q17.drop 28).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_34 : ((q17.drop 34).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_41 : ((q17.drop 41).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_44 : ((q17.drop 44).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_47 : ((q17.drop 47).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_52 : ((q17.drop 52).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_60 : ((q17.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_64 : ((q17.drop 64).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_69 : ((q17.drop 69).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_74 : ((q17.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_77 : ((q17.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_81 : ((q17.drop 81).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_83 : ((q17.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_87 : ((q17.drop 87).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_89 : ((q17.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok17 : nopt 7 s17 = false := by
  have h : q17.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 8 p17_0 (all_chunk _ _ 8 9 p17_8 (all_chunk _ _ 17 4 p17_17 (all_chunk _ _ 21 7 p17_21 (all_chunk _ _ 28 6 p17_28 (all_chunk _ _ 34 7 p17_34 (all_chunk _ _ 41 3 p17_41 (all_chunk _ _ 44 3 p17_44 (all_chunk _ _ 47 5 p17_47 (all_chunk _ _ 52 8 p17_52 (all_chunk _ _ 60 4 p17_60 (all_chunk _ _ 64 5 p17_64 (all_chunk _ _ 69 5 p17_69 (all_chunk _ _ 74 3 p17_74 (all_chunk _ _ 77 4 p17_77 (all_chunk _ _ 81 2 p17_81 (all_chunk _ _ 83 4 p17_83 (all_chunk _ _ 87 2 p17_87 (all_chunk _ _ 89 3 p17_89 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s17 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_0 : ((q18.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_4 : ((q18.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_7 : ((q18.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_11 : ((q18.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_14 : ((q18.drop 14).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_16 : ((q18.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_19 : ((q18.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_23 : ((q18.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_26 : ((q18.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_29 : ((q18.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_33 : ((q18.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_36 : ((q18.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_41 : ((q18.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_45 : ((q18.drop 45).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_52 : ((q18.drop 52).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_61 : ((q18.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_69 : ((q18.drop 69).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_76 : ((q18.drop 76).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_85 : ((q18.drop 85).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok18 : nopt 7 s18 = false := by
  have h : q18.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p18_0 (all_chunk _ _ 4 3 p18_4 (all_chunk _ _ 7 4 p18_7 (all_chunk _ _ 11 3 p18_11 (all_chunk _ _ 14 2 p18_14 (all_chunk _ _ 16 3 p18_16 (all_chunk _ _ 19 4 p18_19 (all_chunk _ _ 23 3 p18_23 (all_chunk _ _ 26 3 p18_26 (all_chunk _ _ 29 4 p18_29 (all_chunk _ _ 33 3 p18_33 (all_chunk _ _ 36 5 p18_36 (all_chunk _ _ 41 4 p18_41 (all_chunk _ _ 45 7 p18_45 (all_chunk _ _ 52 9 p18_52 (all_chunk _ _ 61 8 p18_61 (all_chunk _ _ 69 7 p18_69 (all_chunk _ _ 76 9 p18_76 (all_chunk _ _ 85 5 p18_85 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s18 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_0 : ((q19.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_6 : ((q19.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_11 : ((q19.drop 11).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_19 : ((q19.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_25 : ((q19.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_30 : ((q19.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_33 : ((q19.drop 33).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_40 : ((q19.drop 40).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_47 : ((q19.drop 47).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_53 : ((q19.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_56 : ((q19.drop 56).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_60 : ((q19.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_64 : ((q19.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_68 : ((q19.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_72 : ((q19.drop 72).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_74 : ((q19.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_77 : ((q19.drop 77).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_85 : ((q19.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok19 : nopt 7 s19 = false := by
  have h : q19.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p19_0 (all_chunk _ _ 6 5 p19_6 (all_chunk _ _ 11 8 p19_11 (all_chunk _ _ 19 6 p19_19 (all_chunk _ _ 25 5 p19_25 (all_chunk _ _ 30 3 p19_30 (all_chunk _ _ 33 7 p19_33 (all_chunk _ _ 40 7 p19_40 (all_chunk _ _ 47 6 p19_47 (all_chunk _ _ 53 3 p19_53 (all_chunk _ _ 56 4 p19_56 (all_chunk _ _ 60 4 p19_60 (all_chunk _ _ 64 4 p19_64 (all_chunk _ _ 68 4 p19_68 (all_chunk _ _ 72 2 p19_72 (all_chunk _ _ 74 3 p19_74 (all_chunk _ _ 77 8 p19_77 (all_chunk _ _ 85 7 p19_85 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s19 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_0 : ((q20.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_2 : ((q20.drop 2).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_4 : ((q20.drop 4).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_6 : ((q20.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_8 : ((q20.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_11 : ((q20.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_14 : ((q20.drop 14).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_18 : ((q20.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_22 : ((q20.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_26 : ((q20.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_29 : ((q20.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_31 : ((q20.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_33 : ((q20.drop 33).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_35 : ((q20.drop 35).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_38 : ((q20.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_41 : ((q20.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_43 : ((q20.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_46 : ((q20.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_48 : ((q20.drop 48).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_50 : ((q20.drop 50).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_53 : ((q20.drop 53).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_55 : ((q20.drop 55).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_58 : ((q20.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_61 : ((q20.drop 61).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_63 : ((q20.drop 63).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_65 : ((q20.drop 65).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_67 : ((q20.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_70 : ((q20.drop 70).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_72 : ((q20.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_75 : ((q20.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_79 : ((q20.drop 79).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_84 : ((q20.drop 84).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_87 : ((q20.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_91 : ((q20.drop 91).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_95 : ((q20.drop 95).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_99 : ((q20.drop 99).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok20 : nopt 7 s20 = false := by
  have h : q20.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p20_0 (all_chunk _ _ 2 2 p20_2 (all_chunk _ _ 4 2 p20_4 (all_chunk _ _ 6 2 p20_6 (all_chunk _ _ 8 3 p20_8 (all_chunk _ _ 11 3 p20_11 (all_chunk _ _ 14 4 p20_14 (all_chunk _ _ 18 4 p20_18 (all_chunk _ _ 22 4 p20_22 (all_chunk _ _ 26 3 p20_26 (all_chunk _ _ 29 2 p20_29 (all_chunk _ _ 31 2 p20_31 (all_chunk _ _ 33 2 p20_33 (all_chunk _ _ 35 3 p20_35 (all_chunk _ _ 38 3 p20_38 (all_chunk _ _ 41 2 p20_41 (all_chunk _ _ 43 3 p20_43 (all_chunk _ _ 46 2 p20_46 (all_chunk _ _ 48 2 p20_48 (all_chunk _ _ 50 3 p20_50 (all_chunk _ _ 53 2 p20_53 (all_chunk _ _ 55 3 p20_55 (all_chunk _ _ 58 3 p20_58 (all_chunk _ _ 61 2 p20_61 (all_chunk _ _ 63 2 p20_63 (all_chunk _ _ 65 2 p20_65 (all_chunk _ _ 67 3 p20_67 (all_chunk _ _ 70 2 p20_70 (all_chunk _ _ 72 3 p20_72 (all_chunk _ _ 75 4 p20_75 (all_chunk _ _ 79 5 p20_79 (all_chunk _ _ 84 3 p20_84 (all_chunk _ _ 87 4 p20_87 (all_chunk _ _ 91 4 p20_91 (all_chunk _ _ 95 4 p20_95 (all_chunk _ _ 99 3 p20_99 (by decide +kernel)))))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s20 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_0 : ((q21.drop 0).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_8 : ((q21.drop 8).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_17 : ((q21.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_21 : ((q21.drop 21).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_28 : ((q21.drop 28).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_33 : ((q21.drop 33).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_40 : ((q21.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_42 : ((q21.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_46 : ((q21.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_48 : ((q21.drop 48).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_55 : ((q21.drop 55).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_62 : ((q21.drop 62).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_66 : ((q21.drop 66).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_73 : ((q21.drop 73).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_75 : ((q21.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_79 : ((q21.drop 79).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_81 : ((q21.drop 81).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_85 : ((q21.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_88 : ((q21.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok21 : nopt 7 s21 = false := by
  have h : q21.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 8 p21_0 (all_chunk _ _ 8 9 p21_8 (all_chunk _ _ 17 4 p21_17 (all_chunk _ _ 21 7 p21_21 (all_chunk _ _ 28 5 p21_28 (all_chunk _ _ 33 7 p21_33 (all_chunk _ _ 40 2 p21_40 (all_chunk _ _ 42 4 p21_42 (all_chunk _ _ 46 2 p21_46 (all_chunk _ _ 48 7 p21_48 (all_chunk _ _ 55 7 p21_55 (all_chunk _ _ 62 4 p21_62 (all_chunk _ _ 66 7 p21_66 (all_chunk _ _ 73 2 p21_73 (all_chunk _ _ 75 4 p21_75 (all_chunk _ _ 79 2 p21_79 (all_chunk _ _ 81 4 p21_81 (all_chunk _ _ 85 3 p21_85 (all_chunk _ _ 88 4 p21_88 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s21 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_0 : ((q22.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_4 : ((q22.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_7 : ((q22.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_11 : ((q22.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_14 : ((q22.drop 14).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_16 : ((q22.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_19 : ((q22.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_23 : ((q22.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_26 : ((q22.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_29 : ((q22.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_34 : ((q22.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_37 : ((q22.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_40 : ((q22.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_44 : ((q22.drop 44).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_51 : ((q22.drop 51).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_60 : ((q22.drop 60).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_68 : ((q22.drop 68).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_76 : ((q22.drop 76).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_84 : ((q22.drop 84).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok22 : nopt 7 s22 = false := by
  have h : q22.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p22_0 (all_chunk _ _ 4 3 p22_4 (all_chunk _ _ 7 4 p22_7 (all_chunk _ _ 11 3 p22_11 (all_chunk _ _ 14 2 p22_14 (all_chunk _ _ 16 3 p22_16 (all_chunk _ _ 19 4 p22_19 (all_chunk _ _ 23 3 p22_23 (all_chunk _ _ 26 3 p22_26 (all_chunk _ _ 29 5 p22_29 (all_chunk _ _ 34 3 p22_34 (all_chunk _ _ 37 3 p22_37 (all_chunk _ _ 40 4 p22_40 (all_chunk _ _ 44 7 p22_44 (all_chunk _ _ 51 9 p22_51 (all_chunk _ _ 60 8 p22_60 (all_chunk _ _ 68 8 p22_68 (all_chunk _ _ 76 8 p22_76 (all_chunk _ _ 84 6 p22_84 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s22 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_0 : ((q23.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_6 : ((q23.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_11 : ((q23.drop 11).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_19 : ((q23.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_25 : ((q23.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_30 : ((q23.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_33 : ((q23.drop 33).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_40 : ((q23.drop 40).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_48 : ((q23.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_54 : ((q23.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_58 : ((q23.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_62 : ((q23.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_65 : ((q23.drop 65).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_67 : ((q23.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_70 : ((q23.drop 70).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_74 : ((q23.drop 74).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_78 : ((q23.drop 78).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_87 : ((q23.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok23 : nopt 7 s23 = false := by
  have h : q23.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p23_0 (all_chunk _ _ 6 5 p23_6 (all_chunk _ _ 11 8 p23_11 (all_chunk _ _ 19 6 p23_19 (all_chunk _ _ 25 5 p23_25 (all_chunk _ _ 30 3 p23_30 (all_chunk _ _ 33 7 p23_33 (all_chunk _ _ 40 8 p23_40 (all_chunk _ _ 48 6 p23_48 (all_chunk _ _ 54 4 p23_54 (all_chunk _ _ 58 4 p23_58 (all_chunk _ _ 62 3 p23_62 (all_chunk _ _ 65 2 p23_65 (all_chunk _ _ 67 3 p23_67 (all_chunk _ _ 70 4 p23_70 (all_chunk _ _ 74 4 p23_74 (all_chunk _ _ 78 9 p23_78 (all_chunk _ _ 87 5 p23_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s23 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_0 : ((q24.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_4 : ((q24.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_7 : ((q24.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_12 : ((q24.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_16 : ((q24.drop 16).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_18 : ((q24.drop 18).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_23 : ((q24.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_27 : ((q24.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_31 : ((q24.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_35 : ((q24.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_39 : ((q24.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_43 : ((q24.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_49 : ((q24.drop 49).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_57 : ((q24.drop 57).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_66 : ((q24.drop 66).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_73 : ((q24.drop 73).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_81 : ((q24.drop 81).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_89 : ((q24.drop 89).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok24 : nopt 7 s24 = false := by
  have h : q24.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p24_0 (all_chunk _ _ 4 3 p24_4 (all_chunk _ _ 7 5 p24_7 (all_chunk _ _ 12 4 p24_12 (all_chunk _ _ 16 2 p24_16 (all_chunk _ _ 18 5 p24_18 (all_chunk _ _ 23 4 p24_23 (all_chunk _ _ 27 4 p24_27 (all_chunk _ _ 31 4 p24_31 (all_chunk _ _ 35 4 p24_35 (all_chunk _ _ 39 4 p24_39 (all_chunk _ _ 43 6 p24_43 (all_chunk _ _ 49 8 p24_49 (all_chunk _ _ 57 9 p24_57 (all_chunk _ _ 66 7 p24_66 (all_chunk _ _ 73 8 p24_73 (all_chunk _ _ 81 8 p24_81 (all_chunk _ _ 89 1 p24_89 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s24 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_0 : ((q25.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_7 : ((q25.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_10 : ((q25.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_13 : ((q25.drop 13).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_16 : ((q25.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_20 : ((q25.drop 20).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_25 : ((q25.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_30 : ((q25.drop 30).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_35 : ((q25.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_39 : ((q25.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_42 : ((q25.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_45 : ((q25.drop 45).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_51 : ((q25.drop 51).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_58 : ((q25.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_63 : ((q25.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_66 : ((q25.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_69 : ((q25.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_72 : ((q25.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_76 : ((q25.drop 76).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_79 : ((q25.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_83 : ((q25.drop 83).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_89 : ((q25.drop 89).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok25 : nopt 7 s25 = false := by
  have h : q25.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p25_0 (all_chunk _ _ 7 3 p25_7 (all_chunk _ _ 10 3 p25_10 (all_chunk _ _ 13 3 p25_13 (all_chunk _ _ 16 4 p25_16 (all_chunk _ _ 20 5 p25_20 (all_chunk _ _ 25 5 p25_25 (all_chunk _ _ 30 5 p25_30 (all_chunk _ _ 35 4 p25_35 (all_chunk _ _ 39 3 p25_39 (all_chunk _ _ 42 3 p25_42 (all_chunk _ _ 45 6 p25_45 (all_chunk _ _ 51 7 p25_51 (all_chunk _ _ 58 5 p25_58 (all_chunk _ _ 63 3 p25_63 (all_chunk _ _ 66 3 p25_66 (all_chunk _ _ 69 3 p25_69 (all_chunk _ _ 72 4 p25_72 (all_chunk _ _ 76 3 p25_76 (all_chunk _ _ 79 4 p25_79 (all_chunk _ _ 83 6 p25_83 (all_chunk _ _ 89 7 p25_89 (by decide +kernel)))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s25 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_0 : ((q26.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_2 : ((q26.drop 2).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_6 : ((q26.drop 6).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_9 : ((q26.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_13 : ((q26.drop 13).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_19 : ((q26.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_25 : ((q26.drop 25).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_31 : ((q26.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_34 : ((q26.drop 34).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_36 : ((q26.drop 36).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_38 : ((q26.drop 38).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_42 : ((q26.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_45 : ((q26.drop 45).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_47 : ((q26.drop 47).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_51 : ((q26.drop 51).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_53 : ((q26.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_56 : ((q26.drop 56).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_60 : ((q26.drop 60).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_63 : ((q26.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_67 : ((q26.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_72 : ((q26.drop 72).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_77 : ((q26.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_83 : ((q26.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_90 : ((q26.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok26 : nopt 7 s26 = false := by
  have h : q26.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p26_0 (all_chunk _ _ 2 4 p26_2 (all_chunk _ _ 6 3 p26_6 (all_chunk _ _ 9 4 p26_9 (all_chunk _ _ 13 6 p26_13 (all_chunk _ _ 19 6 p26_19 (all_chunk _ _ 25 6 p26_25 (all_chunk _ _ 31 3 p26_31 (all_chunk _ _ 34 2 p26_34 (all_chunk _ _ 36 2 p26_36 (all_chunk _ _ 38 4 p26_38 (all_chunk _ _ 42 3 p26_42 (all_chunk _ _ 45 2 p26_45 (all_chunk _ _ 47 4 p26_47 (all_chunk _ _ 51 2 p26_51 (all_chunk _ _ 53 3 p26_53 (all_chunk _ _ 56 4 p26_56 (all_chunk _ _ 60 3 p26_60 (all_chunk _ _ 63 4 p26_63 (all_chunk _ _ 67 5 p26_67 (all_chunk _ _ 72 5 p26_72 (all_chunk _ _ 77 6 p26_77 (all_chunk _ _ 83 7 p26_83 (all_chunk _ _ 90 4 p26_90 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s26 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_0 : ((q27.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_4 : ((q27.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_7 : ((q27.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_12 : ((q27.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_17 : ((q27.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_21 : ((q27.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_25 : ((q27.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_30 : ((q27.drop 30).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_35 : ((q27.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_39 : ((q27.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_44 : ((q27.drop 44).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_50 : ((q27.drop 50).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_55 : ((q27.drop 55).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_62 : ((q27.drop 62).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_69 : ((q27.drop 69).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_77 : ((q27.drop 77).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_85 : ((q27.drop 85).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_94 : ((q27.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok27 : nopt 7 s27 = false := by
  have h : q27.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p27_0 (all_chunk _ _ 4 3 p27_4 (all_chunk _ _ 7 5 p27_7 (all_chunk _ _ 12 5 p27_12 (all_chunk _ _ 17 4 p27_17 (all_chunk _ _ 21 4 p27_21 (all_chunk _ _ 25 5 p27_25 (all_chunk _ _ 30 5 p27_30 (all_chunk _ _ 35 4 p27_35 (all_chunk _ _ 39 5 p27_39 (all_chunk _ _ 44 6 p27_44 (all_chunk _ _ 50 5 p27_50 (all_chunk _ _ 55 7 p27_55 (all_chunk _ _ 62 7 p27_62 (all_chunk _ _ 69 8 p27_69 (all_chunk _ _ 77 8 p27_77 (all_chunk _ _ 85 9 p27_85 (all_chunk _ _ 94 2 p27_94 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s27 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_0 : ((q28.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_5 : ((q28.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_9 : ((q28.drop 9).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_12 : ((q28.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_16 : ((q28.drop 16).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_23 : ((q28.drop 23).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_29 : ((q28.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_33 : ((q28.drop 33).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_37 : ((q28.drop 37).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_44 : ((q28.drop 44).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_46 : ((q28.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_49 : ((q28.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_54 : ((q28.drop 54).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_61 : ((q28.drop 61).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_64 : ((q28.drop 64).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_67 : ((q28.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_71 : ((q28.drop 71).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_74 : ((q28.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_77 : ((q28.drop 77).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_79 : ((q28.drop 79).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_84 : ((q28.drop 84).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_87 : ((q28.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok28 : nopt 7 s28 = false := by
  have h : q28.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p28_0 (all_chunk _ _ 5 4 p28_5 (all_chunk _ _ 9 3 p28_9 (all_chunk _ _ 12 4 p28_12 (all_chunk _ _ 16 7 p28_16 (all_chunk _ _ 23 6 p28_23 (all_chunk _ _ 29 4 p28_29 (all_chunk _ _ 33 4 p28_33 (all_chunk _ _ 37 7 p28_37 (all_chunk _ _ 44 2 p28_44 (all_chunk _ _ 46 3 p28_46 (all_chunk _ _ 49 5 p28_49 (all_chunk _ _ 54 7 p28_54 (all_chunk _ _ 61 3 p28_61 (all_chunk _ _ 64 3 p28_64 (all_chunk _ _ 67 4 p28_67 (all_chunk _ _ 71 3 p28_71 (all_chunk _ _ 74 3 p28_74 (all_chunk _ _ 77 2 p28_77 (all_chunk _ _ 79 5 p28_79 (all_chunk _ _ 84 3 p28_84 (all_chunk _ _ 87 4 p28_87 (by decide +kernel)))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s28 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_0 : ((q29.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_5 : ((q29.drop 5).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_11 : ((q29.drop 11).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_17 : ((q29.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_20 : ((q29.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_24 : ((q29.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_29 : ((q29.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_34 : ((q29.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_39 : ((q29.drop 39).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_41 : ((q29.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_43 : ((q29.drop 43).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_47 : ((q29.drop 47).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_54 : ((q29.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_59 : ((q29.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_63 : ((q29.drop 63).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_65 : ((q29.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_68 : ((q29.drop 68).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_74 : ((q29.drop 74).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_76 : ((q29.drop 76).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_80 : ((q29.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_84 : ((q29.drop 84).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_86 : ((q29.drop 86).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_89 : ((q29.drop 89).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_91 : ((q29.drop 91).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok29 : nopt 7 s29 = false := by
  have h : q29.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p29_0 (all_chunk _ _ 5 6 p29_5 (all_chunk _ _ 11 6 p29_11 (all_chunk _ _ 17 3 p29_17 (all_chunk _ _ 20 4 p29_20 (all_chunk _ _ 24 5 p29_24 (all_chunk _ _ 29 5 p29_29 (all_chunk _ _ 34 5 p29_34 (all_chunk _ _ 39 2 p29_39 (all_chunk _ _ 41 2 p29_41 (all_chunk _ _ 43 4 p29_43 (all_chunk _ _ 47 7 p29_47 (all_chunk _ _ 54 5 p29_54 (all_chunk _ _ 59 4 p29_59 (all_chunk _ _ 63 2 p29_63 (all_chunk _ _ 65 3 p29_65 (all_chunk _ _ 68 6 p29_68 (all_chunk _ _ 74 2 p29_74 (all_chunk _ _ 76 4 p29_76 (all_chunk _ _ 80 4 p29_80 (all_chunk _ _ 84 2 p29_84 (all_chunk _ _ 86 3 p29_86 (all_chunk _ _ 89 2 p29_89 (all_chunk _ _ 91 4 p29_91 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s29 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_0 : ((q30.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_5 : ((q30.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_9 : ((q30.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_13 : ((q30.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_17 : ((q30.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_21 : ((q30.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_25 : ((q30.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_29 : ((q30.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_33 : ((q30.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_36 : ((q30.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_40 : ((q30.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_42 : ((q30.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_46 : ((q30.drop 46).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_55 : ((q30.drop 55).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_64 : ((q30.drop 64).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_71 : ((q30.drop 71).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_80 : ((q30.drop 80).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_88 : ((q30.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok30 : nopt 7 s30 = false := by
  have h : q30.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p30_0 (all_chunk _ _ 5 4 p30_5 (all_chunk _ _ 9 4 p30_9 (all_chunk _ _ 13 4 p30_13 (all_chunk _ _ 17 4 p30_17 (all_chunk _ _ 21 4 p30_21 (all_chunk _ _ 25 4 p30_25 (all_chunk _ _ 29 4 p30_29 (all_chunk _ _ 33 3 p30_33 (all_chunk _ _ 36 4 p30_36 (all_chunk _ _ 40 2 p30_40 (all_chunk _ _ 42 4 p30_42 (all_chunk _ _ 46 9 p30_46 (all_chunk _ _ 55 9 p30_55 (all_chunk _ _ 64 7 p30_64 (all_chunk _ _ 71 9 p30_71 (all_chunk _ _ 80 8 p30_80 (all_chunk _ _ 88 4 p30_88 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s30 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_0 : ((q31.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_5 : ((q31.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_9 : ((q31.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_13 : ((q31.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_17 : ((q31.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_21 : ((q31.drop 21).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_26 : ((q31.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_29 : ((q31.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_31 : ((q31.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_35 : ((q31.drop 35).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_37 : ((q31.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_41 : ((q31.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_45 : ((q31.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_53 : ((q31.drop 53).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_62 : ((q31.drop 62).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_71 : ((q31.drop 71).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_78 : ((q31.drop 78).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_87 : ((q31.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok31 : nopt 7 s31 = false := by
  have h : q31.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p31_0 (all_chunk _ _ 5 4 p31_5 (all_chunk _ _ 9 4 p31_9 (all_chunk _ _ 13 4 p31_13 (all_chunk _ _ 17 4 p31_17 (all_chunk _ _ 21 5 p31_21 (all_chunk _ _ 26 3 p31_26 (all_chunk _ _ 29 2 p31_29 (all_chunk _ _ 31 4 p31_31 (all_chunk _ _ 35 2 p31_35 (all_chunk _ _ 37 4 p31_37 (all_chunk _ _ 41 4 p31_41 (all_chunk _ _ 45 8 p31_45 (all_chunk _ _ 53 9 p31_53 (all_chunk _ _ 62 9 p31_62 (all_chunk _ _ 71 7 p31_71 (all_chunk _ _ 78 9 p31_78 (all_chunk _ _ 87 5 p31_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s31 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_0 : ((q32.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_4 : ((q32.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_7 : ((q32.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_12 : ((q32.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_16 : ((q32.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_20 : ((q32.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_24 : ((q32.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_28 : ((q32.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_32 : ((q32.drop 32).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_37 : ((q32.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_40 : ((q32.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_42 : ((q32.drop 42).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_48 : ((q32.drop 48).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_52 : ((q32.drop 52).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_61 : ((q32.drop 61).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_67 : ((q32.drop 67).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_73 : ((q32.drop 73).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_80 : ((q32.drop 80).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_88 : ((q32.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok32 : nopt 7 s32 = false := by
  have h : q32.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p32_0 (all_chunk _ _ 4 3 p32_4 (all_chunk _ _ 7 5 p32_7 (all_chunk _ _ 12 4 p32_12 (all_chunk _ _ 16 4 p32_16 (all_chunk _ _ 20 4 p32_20 (all_chunk _ _ 24 4 p32_24 (all_chunk _ _ 28 4 p32_28 (all_chunk _ _ 32 5 p32_32 (all_chunk _ _ 37 3 p32_37 (all_chunk _ _ 40 2 p32_40 (all_chunk _ _ 42 6 p32_42 (all_chunk _ _ 48 4 p32_48 (all_chunk _ _ 52 9 p32_52 (all_chunk _ _ 61 6 p32_61 (all_chunk _ _ 67 6 p32_67 (all_chunk _ _ 73 7 p32_73 (all_chunk _ _ 80 8 p32_80 (all_chunk _ _ 88 4 p32_88 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s32 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_0 : ((q33.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_4 : ((q33.drop 4).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_10 : ((q33.drop 10).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_16 : ((q33.drop 16).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_22 : ((q33.drop 22).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_24 : ((q33.drop 24).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_27 : ((q33.drop 27).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_29 : ((q33.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_33 : ((q33.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_38 : ((q33.drop 38).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_43 : ((q33.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_48 : ((q33.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_51 : ((q33.drop 51).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_56 : ((q33.drop 56).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_62 : ((q33.drop 62).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_64 : ((q33.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_68 : ((q33.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_71 : ((q33.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_75 : ((q33.drop 75).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_80 : ((q33.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_83 : ((q33.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_87 : ((q33.drop 87).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_90 : ((q33.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_92 : ((q33.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok33 : nopt 7 s33 = false := by
  have h : q33.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p33_0 (all_chunk _ _ 4 6 p33_4 (all_chunk _ _ 10 6 p33_10 (all_chunk _ _ 16 6 p33_16 (all_chunk _ _ 22 2 p33_22 (all_chunk _ _ 24 3 p33_24 (all_chunk _ _ 27 2 p33_27 (all_chunk _ _ 29 4 p33_29 (all_chunk _ _ 33 5 p33_33 (all_chunk _ _ 38 5 p33_38 (all_chunk _ _ 43 5 p33_43 (all_chunk _ _ 48 3 p33_48 (all_chunk _ _ 51 5 p33_51 (all_chunk _ _ 56 6 p33_56 (all_chunk _ _ 62 2 p33_62 (all_chunk _ _ 64 4 p33_64 (all_chunk _ _ 68 3 p33_68 (all_chunk _ _ 71 4 p33_71 (all_chunk _ _ 75 5 p33_75 (all_chunk _ _ 80 3 p33_80 (all_chunk _ _ 83 4 p33_83 (all_chunk _ _ 87 3 p33_87 (all_chunk _ _ 90 2 p33_90 (all_chunk _ _ 92 4 p33_92 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s33 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_0 : ((q34.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_6 : ((q34.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_11 : ((q34.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_15 : ((q34.drop 15).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_17 : ((q34.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_21 : ((q34.drop 21).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_29 : ((q34.drop 29).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_38 : ((q34.drop 38).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_43 : ((q34.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_48 : ((q34.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_54 : ((q34.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_58 : ((q34.drop 58).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_60 : ((q34.drop 60).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_67 : ((q34.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_72 : ((q34.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_76 : ((q34.drop 76).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_80 : ((q34.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_83 : ((q34.drop 83).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_85 : ((q34.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok34 : nopt 7 s34 = false := by
  have h : q34.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p34_0 (all_chunk _ _ 6 5 p34_6 (all_chunk _ _ 11 4 p34_11 (all_chunk _ _ 15 2 p34_15 (all_chunk _ _ 17 4 p34_17 (all_chunk _ _ 21 8 p34_21 (all_chunk _ _ 29 9 p34_29 (all_chunk _ _ 38 5 p34_38 (all_chunk _ _ 43 5 p34_43 (all_chunk _ _ 48 6 p34_48 (all_chunk _ _ 54 4 p34_54 (all_chunk _ _ 58 2 p34_58 (all_chunk _ _ 60 7 p34_60 (all_chunk _ _ 67 5 p34_67 (all_chunk _ _ 72 4 p34_72 (all_chunk _ _ 76 4 p34_76 (all_chunk _ _ 80 3 p34_80 (all_chunk _ _ 83 2 p34_83 (all_chunk _ _ 85 7 p34_85 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s34 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_0 : ((q35.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_4 : ((q35.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_7 : ((q35.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_12 : ((q35.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_17 : ((q35.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_20 : ((q35.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_24 : ((q35.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_29 : ((q35.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_34 : ((q35.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_37 : ((q35.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_41 : ((q35.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_45 : ((q35.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_53 : ((q35.drop 53).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_62 : ((q35.drop 62).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_71 : ((q35.drop 71).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_79 : ((q35.drop 79).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_88 : ((q35.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok35 : nopt 7 s35 = false := by
  have h : q35.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p35_0 (all_chunk _ _ 4 3 p35_4 (all_chunk _ _ 7 5 p35_7 (all_chunk _ _ 12 5 p35_12 (all_chunk _ _ 17 3 p35_17 (all_chunk _ _ 20 4 p35_20 (all_chunk _ _ 24 5 p35_24 (all_chunk _ _ 29 5 p35_29 (all_chunk _ _ 34 3 p35_34 (all_chunk _ _ 37 4 p35_37 (all_chunk _ _ 41 4 p35_41 (all_chunk _ _ 45 8 p35_45 (all_chunk _ _ 53 9 p35_53 (all_chunk _ _ 62 9 p35_62 (all_chunk _ _ 71 8 p35_71 (all_chunk _ _ 79 9 p35_79 (all_chunk _ _ 88 4 p35_88 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s35 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_0 : ((q36.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_4 : ((q36.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_7 : ((q36.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_12 : ((q36.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_16 : ((q36.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_20 : ((q36.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_24 : ((q36.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_29 : ((q36.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_32 : ((q36.drop 32).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_34 : ((q36.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_39 : ((q36.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_43 : ((q36.drop 43).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_50 : ((q36.drop 50).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_55 : ((q36.drop 55).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_60 : ((q36.drop 60).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_69 : ((q36.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_73 : ((q36.drop 73).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_81 : ((q36.drop 81).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_89 : ((q36.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok36 : nopt 7 s36 = false := by
  have h : q36.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p36_0 (all_chunk _ _ 4 3 p36_4 (all_chunk _ _ 7 5 p36_7 (all_chunk _ _ 12 4 p36_12 (all_chunk _ _ 16 4 p36_16 (all_chunk _ _ 20 4 p36_20 (all_chunk _ _ 24 5 p36_24 (all_chunk _ _ 29 3 p36_29 (all_chunk _ _ 32 2 p36_32 (all_chunk _ _ 34 5 p36_34 (all_chunk _ _ 39 4 p36_39 (all_chunk _ _ 43 7 p36_43 (all_chunk _ _ 50 5 p36_50 (all_chunk _ _ 55 5 p36_55 (all_chunk _ _ 60 9 p36_60 (all_chunk _ _ 69 4 p36_69 (all_chunk _ _ 73 8 p36_73 (all_chunk _ _ 81 8 p36_81 (all_chunk _ _ 89 3 p36_89 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s36 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_0 : ((q37.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_4 : ((q37.drop 4).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_10 : ((q37.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_14 : ((q37.drop 14).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_20 : ((q37.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_24 : ((q37.drop 24).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_27 : ((q37.drop 27).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_29 : ((q37.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_33 : ((q37.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_38 : ((q37.drop 38).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_43 : ((q37.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_48 : ((q37.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_51 : ((q37.drop 51).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_57 : ((q37.drop 57).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_62 : ((q37.drop 62).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_64 : ((q37.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_68 : ((q37.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_71 : ((q37.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_75 : ((q37.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_79 : ((q37.drop 79).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_82 : ((q37.drop 82).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_84 : ((q37.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_88 : ((q37.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_91 : ((q37.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_94 : ((q37.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok37 : nopt 7 s37 = false := by
  have h : q37.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p37_0 (all_chunk _ _ 4 6 p37_4 (all_chunk _ _ 10 4 p37_10 (all_chunk _ _ 14 6 p37_14 (all_chunk _ _ 20 4 p37_20 (all_chunk _ _ 24 3 p37_24 (all_chunk _ _ 27 2 p37_27 (all_chunk _ _ 29 4 p37_29 (all_chunk _ _ 33 5 p37_33 (all_chunk _ _ 38 5 p37_38 (all_chunk _ _ 43 5 p37_43 (all_chunk _ _ 48 3 p37_48 (all_chunk _ _ 51 6 p37_51 (all_chunk _ _ 57 5 p37_57 (all_chunk _ _ 62 2 p37_62 (all_chunk _ _ 64 4 p37_64 (all_chunk _ _ 68 3 p37_68 (all_chunk _ _ 71 4 p37_71 (all_chunk _ _ 75 4 p37_75 (all_chunk _ _ 79 3 p37_79 (all_chunk _ _ 82 2 p37_82 (all_chunk _ _ 84 4 p37_84 (all_chunk _ _ 88 3 p37_88 (all_chunk _ _ 91 3 p37_91 (all_chunk _ _ 94 2 p37_94 (by decide +kernel))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s37 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_0 : ((q38.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_6 : ((q38.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_11 : ((q38.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_15 : ((q38.drop 15).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_17 : ((q38.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_21 : ((q38.drop 21).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_29 : ((q38.drop 29).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_38 : ((q38.drop 38).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_43 : ((q38.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_48 : ((q38.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_54 : ((q38.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_58 : ((q38.drop 58).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_60 : ((q38.drop 60).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_66 : ((q38.drop 66).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_72 : ((q38.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_75 : ((q38.drop 75).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_77 : ((q38.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_81 : ((q38.drop 81).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_85 : ((q38.drop 85).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_91 : ((q38.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok38 : nopt 7 s38 = false := by
  have h : q38.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p38_0 (all_chunk _ _ 6 5 p38_6 (all_chunk _ _ 11 4 p38_11 (all_chunk _ _ 15 2 p38_15 (all_chunk _ _ 17 4 p38_17 (all_chunk _ _ 21 8 p38_21 (all_chunk _ _ 29 9 p38_29 (all_chunk _ _ 38 5 p38_38 (all_chunk _ _ 43 5 p38_43 (all_chunk _ _ 48 6 p38_48 (all_chunk _ _ 54 4 p38_54 (all_chunk _ _ 58 2 p38_58 (all_chunk _ _ 60 6 p38_60 (all_chunk _ _ 66 6 p38_66 (all_chunk _ _ 72 3 p38_72 (all_chunk _ _ 75 2 p38_75 (all_chunk _ _ 77 4 p38_77 (all_chunk _ _ 81 4 p38_81 (all_chunk _ _ 85 6 p38_85 (all_chunk _ _ 91 1 p38_91 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s38 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_0 : ((q39.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_4 : ((q39.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_7 : ((q39.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_12 : ((q39.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_17 : ((q39.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_20 : ((q39.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_24 : ((q39.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_28 : ((q39.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_32 : ((q39.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_36 : ((q39.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_39 : ((q39.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_44 : ((q39.drop 44).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_51 : ((q39.drop 51).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_60 : ((q39.drop 60).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_69 : ((q39.drop 69).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_77 : ((q39.drop 77).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_86 : ((q39.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok39 : nopt 7 s39 = false := by
  have h : q39.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p39_0 (all_chunk _ _ 4 3 p39_4 (all_chunk _ _ 7 5 p39_7 (all_chunk _ _ 12 5 p39_12 (all_chunk _ _ 17 3 p39_17 (all_chunk _ _ 20 4 p39_20 (all_chunk _ _ 24 4 p39_24 (all_chunk _ _ 28 4 p39_28 (all_chunk _ _ 32 4 p39_32 (all_chunk _ _ 36 3 p39_36 (all_chunk _ _ 39 5 p39_39 (all_chunk _ _ 44 7 p39_44 (all_chunk _ _ 51 9 p39_51 (all_chunk _ _ 60 9 p39_60 (all_chunk _ _ 69 8 p39_69 (all_chunk _ _ 77 9 p39_77 (all_chunk _ _ 86 6 p39_86 (by decide +kernel))))))))))))))))))
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

def targetTable : ℕ := 4276813544 * 2 ^ 32 + 4276808896

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

def probe : Fin 500 := 2

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

def restricted : List W := [(inputs.getD 0 0), (inputs.getD 1 0), (inputs.getD 2 0), (inputs.getD 3 0), 0, (inputs.getD 4 0)]
def flipped : List W := [(inputs.getD 0 0), (inputs.getD 1 0), (inputs.getD 2 0), (inputs.getD 3 0), (~~~0), (inputs.getD 4 0)]

theorem rows_related : List.Forall₂ related restricted flipped := by
  unfold restricted flipped
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inr (.inl rfl)) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
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
    · exact .inl rfl
    · exact .inr (.inr ⟨(inputs.getD 4 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
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
    ⟨.and, [2, 3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [7, 1]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.and, [12, 5]⟩,
    ⟨.or, [13, 4]⟩,
    ⟨.and, [9, 14]⟩,
    ⟨.or, [11, 15]⟩], 16⟩

set_option maxRecDepth 16000 in
theorem elevenGateUpper : PEqualNP.MetaComplexity.Monotone2 upperCircuit ∧ upperCircuit.size = 11 ∧
    ∀ x : Fin 6 → Bool, upperCircuit.eval (List.ofFn x) = targetSix x := by
  refine ⟨?_, by decide, ?_⟩
  · simp [upperCircuit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

end PEqualNP.Outside.L_meta_41498_aux

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_41498 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813544 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813544 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_41498_aux.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_41498_aux.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_41498_aux.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_41498_aux.six_lower_bound C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_41498_aux.upperCircuit, PEqualNP.Outside.L_meta_41498_aux.elevenGateUpper.1,
      ?_, PEqualNP.Outside.L_meta_41498_aux.elevenGateUpper.2.2⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
