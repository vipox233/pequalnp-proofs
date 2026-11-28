import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39683_aux

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
def w0 : Nat := ((((((((0xfffdf * 2^60 + 0xfff7ffbfdfe1ffd) * 2^60 + 0xbb7dbfafbbfbdfb) * 2^60 + 0xff5bd57bdeb7bd6) * 2^60 + 0xf597ffaa699ff80) * 2^60 + 0x800000000000f0) * 2^60 + 0x0) * 2^60 + 0x3c0000000000) * 2^60 + 0x7e000000f)
def w1 : Nat := ((((((((0xfdabf * 2^60 + 0xba9bd4da6e3efa6) * 2^60 + 0xddb3d9d76d5d6af) * 2^60 + 0x47adeaa53b5a76b) * 2^60 + 0xdafe58d5d774409) * 2^60 + 0x50007803c1e0f00) * 2^60 + 0x7e0007e03f) * 2^60 + 0x1fc0000000f801) * 2^60 + 0xf07c1f800071dd0)
def w2 : Nat := ((((((((0xb673 * 2^60 + 0xc9bd4dec42ef6af) * 2^60 + 0x68f6ea9b5e6aba5) * 2^60 + 0x5b36cfc7686ed0d) * 2^60 + 0xefaaa9669a78852) * 2^60 + 0x6387803c01ff000) * 2^60 + 0x7e03f8003f8003f) * 2^60 + 0xfe00001fc1f003e) * 2^60 + 0x7fe00019861e0)
def w3 : Nat := ((((((((0x71f4 * 2^60 + 0x9dde8886f777b34) * 2^60 + 0x7edb74e5974cf36) * 2^60 + 0x6dc773ee318f7bf) * 2^60 + 0x434d32791fa1063) * 2^60 + 0x83f8003ffe00000) * 2^60 + 0x7ffc00003ffffc0) * 2^60 + 0x1ffe0003f) * 2^60 + 0xff8000001e07e00)
def w4 : Nat := ((((((((0xff9 * 2^60 + 0x1110eef77bbbdc7) * 2^60 + 0x8f1c78f9e78f3c7) * 2^60 + 0x8ef87cf7bdfc631) * 2^60 + 0x8c71c47fe44207c) * 2^60 + 0x3ffffc00000000) * 2^60 + 0x7fffffffc000000) * 2^60 + 0x1ffffffc0) * 2^60 + 0x1ff8000)
def w5 : Nat := ((((((((0xfda9f * 2^60 + 0xba93d49a4e20fa4) * 2^60 + 0x9931998729594ab) * 2^60 + 0x4709c0211a12342) * 2^60 + 0xd09658804114400) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w6 : Nat := ((((((((0xfffff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffff89) * 2^60 + 0x58007803c1e0ff0) * 2^60 + 0x7e0007e03f) * 2^60 + 0x1ffc000000f801) * 2^60 + 0xf07c1ffe0071ddf)
def w7 : Nat := ((((((((0x2540 * 2^60 + 0x45642b2591c1059) * 2^60 + 0x224c262892a2950) * 2^60 + 0xb852155ac4a5894) * 2^60 + 0x2501a72a288bb80) * 2^60 + 0x800000000000f0) * 2^60 + 0x0) * 2^60 + 0x3c0000000000) * 2^60 + 0x7e000000f)
def w8 : Nat := ((((((((0x20 * 2^60 + 0x80040201e002) * 2^60 + 0x448240504404204) * 2^60 + 0xa42a842148429) * 2^60 + 0xa6800559660009) * 2^60 + 0x50007803c1e0f00) * 2^60 + 0x7e0007e03f) * 2^60 + 0x1fc0000000f801) * 2^60 + 0xf07c1f800071dd0)
def w9 : Nat := ((((((((0xb653 * 2^60 + 0xc9b54dac42e16ad) * 2^60 + 0x2874aa8b1a6a9a1) * 2^60 + 0x5b12c5434826904) * 2^60 + 0xe582a9220818800) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w10 : Nat := ((((((((0xfffff * 2^60 + 0xffffffffdfeffff) * 2^60 + 0xfbffffbffffbfff) * 2^60 + 0xff7fdffffefffdf) * 2^60 + 0xffbfffeefbfffd2) * 2^60 + 0x6b87803c01ff0f0) * 2^60 + 0x7e03f8003f8003f) * 2^60 + 0xfe03c01fc1f003e) * 2^60 + 0x7fe07e19861ef)
def w11 : Nat := ((((((((0xf498c * 2^60 + 0x3642b2139d00950) * 2^60 + 0x93091524a19145a) * 2^60 + 0xa449103896912d2) * 2^60 + 0x101556886187780) * 2^60 + 0x800000000000f0) * 2^60 + 0x0) * 2^60 + 0x3c0000000000) * 2^60 + 0x7e000000f)
def w12 : Nat := ((((((((0x20 * 2^60 + 0x80040000e002) * 2^60 + 0x408240104400204) * 2^60 + 0x240a842048409) * 2^60 + 0xa2800449260052) * 2^60 + 0x6387803c01ff000) * 2^60 + 0x7e03f8003f8003f) * 2^60 + 0xfe00001fc1f003e) * 2^60 + 0x7fe00019861e0)
def w13 : Nat := ((((((((0x71d4 * 2^60 + 0x9dd68886d761b34) * 2^60 + 0x3a5934a59348d32) * 2^60 + 0x6d43516a1087396) * 2^60 + 0x410532280981000) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w14 : Nat := ((((((((0xfffff * 2^60 + 0xffffffbffff7ffd) * 2^60 + 0xffffffefbffffff) * 2^60 + 0xffdff7ffffbffff) * 2^60 + 0xf7dffffb7fbffe3) * 2^60 + 0x8bf8003ffe000f0) * 2^60 + 0x7ffc00003ffffc0) * 2^60 + 0x3c01ffe0003f) * 2^60 + 0xff80007e1e07e0f)
def w15 : Nat := ((((((((0xf8e0b * 2^60 + 0x6221773908804c9) * 2^60 + 0x81248b0a28b30c9) * 2^60 + 0x92188411ce30840) * 2^60 + 0xb492cd82601ef80) * 2^60 + 0x800000000000f0) * 2^60 + 0x0) * 2^60 + 0x3c0000000000) * 2^60 + 0x7e000000f)
def w16 : Nat := ((((((((0x20 * 2^60 + 0x800002016000) * 2^60 + 0x448240400404204) * 2^60 + 0x8422842108429) * 2^60 + 0x24800511620063) * 2^60 + 0x83f8003ffe00000) * 2^60 + 0x7ffc00003ffffc0) * 2^60 + 0x1ffe0003f) * 2^60 + 0xff8000001e07e00)
def w17 : Nat := ((((((((0xfd9 * 2^60 + 0x1110eeb75ba1dc5) * 2^60 + 0x8b1c38a9a38b1c3) * 2^60 + 0x8e5854739cb4210) * 2^60 + 0x8411c42a6002000) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w18 : Nat := ((((((((0xfffff * 2^60 + 0xfff7fffffffbfff) * 2^60 + 0xbf7dfffffffffff) * 2^60 + 0xfffbfdffffffff7) * 2^60 + 0xfdf7ffffeddfffc) * 2^60 + 0xbffffc000000f0) * 2^60 + 0x7fffffffc000000) * 2^60 + 0x3c01ffffffc0) * 2^60 + 0x7e1ff800f)
def w19 : Nat := ((((((((0xff006 * 2^60 + 0xeee711088440238) * 2^60 + 0x306187061870c38) * 2^60 + 0x7103810842039c6) * 2^60 + 0x71863b80099df80) * 2^60 + 0x800000000000f0) * 2^60 + 0x0) * 2^60 + 0x3c0000000000) * 2^60 + 0x7e000000f)
def w20 : Nat := ((((((((0x20 * 2^60 + 0x40201a002) * 2^60 + 0x40040504404204) * 2^60 + 0xa028842148421) * 2^60 + 0x8600055844007c) * 2^60 + 0x3ffffc00000000) * 2^60 + 0x7fffffffc000000) * 2^60 + 0x1ffffffc0) * 2^60 + 0x1ff8000)
def w21 : Nat := ((((((((0x9233 * 2^60 + 0x889944c8422e6a6) * 2^60 + 0x48b2c8934c482a5) * 2^60 + 0x4324ca85284a509) * 2^60 + 0xcaaa08449270000) * 2^60 + 0x4000000001e0000) * 2^60 + 0x3f) * 2^60 + 0x0) * 2^60 + 0x7c000000001c0)
def w22 : Nat := ((((((((0xffeff * 2^60 + 0xfbbfddfe6efffaf) * 2^60 + 0xfdf7fbdf7f7ffaf) * 2^60 + 0x5fbfefe77b7ef6f) * 2^60 + 0xfffef9f7df7cc5b) * 2^60 + 0x7387f83fc1fff00) * 2^60 + 0x7e03ffe03ffe03f) * 2^60 + 0xfffc001fc1ff83f) * 2^60 + 0xf07fff8019f7df0)
def w23 : Nat := ((((((((0xf488c * 2^60 + 0x320290122c10900) * 2^60 + 0x95011144211540a) * 2^60 + 0x48920201310262) * 2^60 + 0x105450914504409) * 2^60 + 0x10007803c000f00) * 2^60 + 0x7e0007e000) * 2^60 + 0x1fc0000000f801) * 2^60 + 0xf0001f800071c10)
def w24 : Nat := ((((((((0x2440 * 2^60 + 0x4124092400c1009) * 2^60 + 0x204422081222900) * 2^60 + 0x181205424024804) * 2^60 + 0x2500a1220808852) * 2^60 + 0x2387803c001f000) * 2^60 + 0x7e03f8003f80000) * 2^60 + 0xfe00001fc1f003e) * 2^60 + 0x3e0001986020)
def w25 : Nat := ((((((((0x50b4 * 2^60 + 0x989a80826636b24) * 2^60 + 0x5c9350c5054c626) * 2^60 + 0x458562a4310a72b) * 2^60 + 0x424c10511720001) * 2^60 + 0x3c000000) * 2^60 + 0x7e000) * 2^60 + 0x1) * 2^60 + 0xf00000000001c00)
def w26 : Nat := ((((((((0xffbff * 2^60 + 0xbfdfdcdeff7ffb6) * 2^60 + 0xfffbfdf7ff5dfbf) * 2^60 + 0x6feffbef3bdf7ff) * 2^60 + 0xdbff7afddff546b) * 2^60 + 0xd3f8783fffe0f00) * 2^60 + 0x7ffc07e03ffffff) * 2^60 + 0x1fc001ffe0f83f) * 2^60 + 0xfffc1f801e77fd0)
def w27 : Nat := ((((((((0xf8a0b * 2^60 + 0x220154580808482) * 2^60 + 0x812089126811089) * 2^60 + 0x22888010a50040) * 2^60 + 0x98b24884c054408) * 2^60 + 0x5000780001e0f00) * 2^60 + 0x7e0000003f) * 2^60 + 0x1fc0000000f800) * 2^60 + 0x7c1f8000701d0)
def w28 : Nat := ((((((((0x2140 * 2^60 + 0x54408049141010) * 2^60 + 0x224824209200910) * 2^60 + 0x2842114a0085094) * 2^60 + 0x10122280881062) * 2^60 + 0x83f8003c3e00000) * 2^60 + 0x7ffc00003f81fc0) * 2^60 + 0x1ffe0003e) * 2^60 + 0xf8000001e06200)
def w29 : Nat := ((((((((0xab9 * 2^60 + 0x1010c4d26a3ad86) * 2^60 + 0x8d1058d1650d287) * 2^60 + 0x6a868a53958621) * 2^60 + 0x88704055c440008) * 2^60 + 0x78000000000) * 2^60 + 0x7e00000000) * 2^60 + 0xf800) * 2^60 + 0x70000)
def w30 : Nat := ((((((((0xfdfff * 2^60 + 0xbb9bfeff7fbffe7) * 2^60 + 0xdfbff9ffefdf7ef) * 2^60 + 0xcffdfef7bffe77b) * 2^60 + 0xdeffdcfff77647d) * 2^60 + 0x53ffffc3c1e0f00) * 2^60 + 0x7fffffffc07e03f) * 2^60 + 0x1fc001ffffffc1) * 2^60 + 0xf07c1f801ff9dd0)
def w31 : Nat := ((((((((0xfd006 * 2^60 + 0xaa8b10080404220) * 2^60 + 0x50a381060850428) * 2^60 + 0x41058200020214a) * 2^60 + 0x528e18801334401) * 2^60 + 0x50000003c1e0f00) * 2^60 + 0x7e03f) * 2^60 + 0x1fc00000000001) * 2^60 + 0xf07c1f800001dd0)
def w32 : Nat := ((((((((0x540 * 2^60 + 0x1002a251181041) * 2^60 + 0x20c20288282140) * 2^60 + 0x8850145284a4010) * 2^60 + 0x401842a2002074) * 2^60 + 0x3ff87c00000000) * 2^60 + 0x7ffff81fc000000) * 2^60 + 0x1ffff07c0) * 2^60 + 0x1f88000)
def w33 : Nat := ((((((((0x3070 * 2^60 + 0x899c08844267224) * 2^60 + 0x68d260811648b24) * 2^60 + 0x490643c6200e50d) * 2^60 + 0x430820601a20042) * 2^60 + 0x380003c0000000) * 2^60 + 0x7e0000003f80000) * 2^60 + 0x1fc00003e) * 2^60 + 0x1806000)
def w34 : Nat := ((((((((0xf7f7 * 2^60 + 0xddffcdeef7fffbf) * 2^60 + 0x7efffeffdf6efb7) * 2^60 + 0x7ff7ffef79effbf) * 2^60 + 0xefefbb7f9ff9873) * 2^60 + 0xe3ff803fffff000) * 2^60 + 0x7ffff8003ffffff) * 2^60 + 0xfe00001ffff003f) * 2^60 + 0xffffe0001f87fe0)
def w35 : Nat := ((((((((0x8603 * 2^60 + 0x40214568008848b) * 2^60 + 0x248a1a4822081) * 2^60 + 0x12308c014860800) * 2^60 + 0xaca289068058810) * 2^60 + 0x6007800001ff000) * 2^60 + 0x3f800000003f) * 2^60 + 0xfe00000001f0000) * 2^60 + 0x7fe00001801e0)
def w36 : Nat := ((((((((0x4184 * 2^60 + 0x14428002b510910) * 2^60 + 0x160914648104412) * 2^60 + 0x24c1302811812b2) * 2^60 + 0x4512190581021) * 2^60 + 0x80780003fe00000) * 2^60 + 0x1fc0000007ffc0) * 2^60 + 0x3e00001) * 2^60 + 0xff8000000601e00)
def w37 : Nat := ((((((((0x671 * 2^60 + 0x1104ce442ab487) * 2^60 + 0x8146899460a385) * 2^60 + 0xa304cc7286c401) * 2^60 + 0x8c2080668040050) * 2^60 + 0x38780000000000) * 2^60 + 0x7e03f8000000000) * 2^60 + 0x1fc1f0000) * 2^60 + 0x1980000)
def w38 : Nat := ((((((((0xbffb * 2^60 + 0xd9bdefff7bfffef) * 2^60 + 0xeffefafbffefbe7) * 2^60 + 0xdffefff7fdfef3d) * 2^60 + 0xeffbed7ffe7a87e) * 2^60 + 0x63fffffc01ff000) * 2^60 + 0x7fffffffff8003f) * 2^60 + 0xfe00001fffffffe) * 2^60 + 0x7fe0001ffe1e0)
def w39 : Nat := ((((((((0xb002 * 2^60 + 0xc8ad01080044228) * 2^60 + 0x60e282021860820) * 2^60 + 0x51068300400290c) * 2^60 + 0x638a29001a38802) * 2^60 + 0x6000003c01ff000) * 2^60 + 0x3f8003f) * 2^60 + 0xfe000000000003e) * 2^60 + 0x7fe00000061e0)
def w40 : Nat := ((((((((0x988 * 2^60 + 0x1000a2133910940) * 2^60 + 0x87081060a185042) * 2^60 + 0x84c830309590230) * 2^60 + 0x514419640202c) * 2^60 + 0x787fc00000000) * 2^60 + 0x1fc07ffc000000) * 2^60 + 0x3e0ffc0) * 2^60 + 0x678000)
def w41 : Nat := ((((((((0x1f0 * 2^60 + 0x111088867333904) * 2^60 + 0xe1870e1870c306) * 2^60 + 0xcc070e6318c631) * 2^60 + 0x4100790400060) * 2^60 + 0x3f800000000000) * 2^60 + 0x7ffc00000000000) * 2^60 + 0x1ffe00000) * 2^60 + 0x1e00000)
def w42 : Nat := ((((((((0x7ffd * 2^60 + 0x9ddeeef7ffffff7) * 2^60 + 0xffdf7cfdf7cfff7) * 2^60 + 0xefff7fffbdff7bf) * 2^60 + 0xcf7df67fffe307f) * 2^60 + 0x83fffffffe00000) * 2^60 + 0x7ffffffffffffc0) * 2^60 + 0x1ffffffff) * 2^60 + 0xff8000001fffe00)
def w43 : Nat := ((((((((0x7004 * 2^60 + 0x8cce00008444230) * 2^60 + 0x70c304041040c30) * 2^60 + 0x61070308000318e) * 2^60 + 0x430c32001ba1003) * 2^60 + 0x8000003ffe00000) * 2^60 + 0x3ffffc0) * 2^60 + 0x3f) * 2^60 + 0xff8000000007e00)
def w44 : Nat := ((((((((0xe09 * 2^60 + 0x667108884c3) * 2^60 + 0x8104081860830c1) * 2^60 + 0x82380c118c70000) * 2^60 + 0x8c30c406e04201c) * 2^60 + 0x7ffc00000000) * 2^60 + 0x3ffffc000000) * 2^60 + 0x1fffc0) * 2^60 + 0x1f8000)
def nums : List Nat := [w0,w1,w2,w3,w4]
def s0 : List Nat := [w4,w3,w2,w5,w1,w0]
def q0 := kidsL 6 s0
def s1 : List Nat := [w4,w3,w2,w1,w0,w6]
def q1 := kidsL 6 s1
def s2 : List Nat := [w4,w7,w3,w2,w1,w0]
def q2 := kidsL 6 s2
def s3 : List Nat := [w8,w4,w3,w2,w1,w0]
def q3 := kidsL 6 s3
def s4 : List Nat := [w4,w3,w9,w2,w1,w0]
def q4 := kidsL 6 s4
def s5 : List Nat := [w4,w3,w2,w1,w0,w10]
def q5 := kidsL 6 s5
def s6 : List Nat := [w4,w3,w2,w11,w1,w0]
def q6 := kidsL 6 s6
def s7 : List Nat := [w12,w4,w3,w2,w1,w0]
def q7 := kidsL 6 s7
def s8 : List Nat := [w4,w13,w3,w2,w1,w0]
def q8 := kidsL 6 s8
def s9 : List Nat := [w4,w3,w2,w1,w0,w14]
def q9 := kidsL 6 s9
def s10 : List Nat := [w4,w3,w2,w15,w1,w0]
def q10 := kidsL 6 s10
def s11 : List Nat := [w16,w4,w3,w2,w1,w0]
def q11 := kidsL 6 s11
def s12 : List Nat := [w17,w4,w3,w2,w1,w0]
def q12 := kidsL 6 s12
def s13 : List Nat := [w4,w3,w2,w1,w0,w18]
def q13 := kidsL 6 s13
def s14 : List Nat := [w4,w3,w2,w1,w19,w0]
def q14 := kidsL 6 s14
def s15 : List Nat := [w20,w4,w3,w2,w1,w0]
def q15 := kidsL 6 s15
def s16 : List Nat := [w4,w3,w21,w2,w1,w0]
def q16 := kidsL 6 s16
def s17 : List Nat := [w4,w3,w2,w1,w22,w0]
def q17 := kidsL 6 s17
def s18 : List Nat := [w4,w3,w2,w23,w1,w0]
def q18 := kidsL 6 s18
def s19 : List Nat := [w4,w24,w3,w2,w1,w0]
def q19 := kidsL 6 s19
def s20 : List Nat := [w4,w25,w3,w2,w1,w0]
def q20 := kidsL 6 s20
def s21 : List Nat := [w4,w3,w2,w1,w26,w0]
def q21 := kidsL 6 s21
def s22 : List Nat := [w4,w3,w2,w27,w1,w0]
def q22 := kidsL 6 s22
def s23 : List Nat := [w4,w28,w3,w2,w1,w0]
def q23 := kidsL 6 s23
def s24 : List Nat := [w29,w4,w3,w2,w1,w0]
def q24 := kidsL 6 s24
def s25 : List Nat := [w4,w3,w2,w1,w30,w0]
def q25 := kidsL 6 s25
def s26 : List Nat := [w4,w3,w2,w31,w1,w0]
def q26 := kidsL 6 s26
def s27 : List Nat := [w32,w4,w3,w2,w1,w0]
def q27 := kidsL 6 s27
def s28 : List Nat := [w4,w33,w3,w2,w1,w0]
def q28 := kidsL 6 s28
def s29 : List Nat := [w4,w3,w2,w34,w1,w0]
def q29 := kidsL 6 s29
def s30 : List Nat := [w4,w3,w35,w2,w1,w0]
def q30 := kidsL 6 s30
def s31 : List Nat := [w4,w36,w3,w2,w1,w0]
def q31 := kidsL 6 s31
def s32 : List Nat := [w37,w4,w3,w2,w1,w0]
def q32 := kidsL 6 s32
def s33 : List Nat := [w4,w3,w2,w38,w1,w0]
def q33 := kidsL 6 s33
def s34 : List Nat := [w4,w3,w39,w2,w1,w0]
def q34 := kidsL 6 s34
def s35 : List Nat := [w40,w4,w3,w2,w1,w0]
def q35 := kidsL 6 s35
def s36 : List Nat := [w41,w4,w3,w2,w1,w0]
def q36 := kidsL 6 s36
def s37 : List Nat := [w4,w3,w42,w2,w1,w0]
def q37 := kidsL 6 s37
def s38 : List Nat := [w4,w43,w3,w2,w1,w0]
def q38 := kidsL 6 s38
def s39 : List Nat := [w44,w4,w3,w2,w1,w0]
def q39 := kidsL 6 s39

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_0 : ((q0.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_5 : ((q0.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_9 : ((q0.drop 9).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_12 : ((q0.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_15 : ((q0.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_18 : ((q0.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_21 : ((q0.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_25 : ((q0.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_30 : ((q0.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_34 : ((q0.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_37 : ((q0.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_40 : ((q0.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_43 : ((q0.drop 43).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_47 : ((q0.drop 47).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_52 : ((q0.drop 52).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_55 : ((q0.drop 55).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

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
theorem p0_67 : ((q0.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_72 : ((q0.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_75 : ((q0.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_78 : ((q0.drop 78).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_80 : ((q0.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_84 : ((q0.drop 84).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_87 : ((q0.drop 87).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_90 : ((q0.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_94 : ((q0.drop 94).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_97 : ((q0.drop 97).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_101 : ((q0.drop 101).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok0 : nopt 7 s0 = false := by
  have h : q0.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p0_0 (all_chunk _ _ 5 4 p0_5 (all_chunk _ _ 9 3 p0_9 (all_chunk _ _ 12 3 p0_12 (all_chunk _ _ 15 3 p0_15 (all_chunk _ _ 18 3 p0_18 (all_chunk _ _ 21 4 p0_21 (all_chunk _ _ 25 5 p0_25 (all_chunk _ _ 30 4 p0_30 (all_chunk _ _ 34 3 p0_34 (all_chunk _ _ 37 3 p0_37 (all_chunk _ _ 40 3 p0_40 (all_chunk _ _ 43 4 p0_43 (all_chunk _ _ 47 5 p0_47 (all_chunk _ _ 52 3 p0_52 (all_chunk _ _ 55 2 p0_55 (all_chunk _ _ 57 3 p0_57 (all_chunk _ _ 60 3 p0_60 (all_chunk _ _ 63 4 p0_63 (all_chunk _ _ 67 5 p0_67 (all_chunk _ _ 72 3 p0_72 (all_chunk _ _ 75 3 p0_75 (all_chunk _ _ 78 2 p0_78 (all_chunk _ _ 80 4 p0_80 (all_chunk _ _ 84 3 p0_84 (all_chunk _ _ 87 3 p0_87 (all_chunk _ _ 90 4 p0_90 (all_chunk _ _ 94 3 p0_94 (all_chunk _ _ 97 4 p0_97 (all_chunk _ _ 101 1 p0_101 (by decide +kernel)))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s0 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_0 : ((q1.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_4 : ((q1.drop 4).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_8 : ((q1.drop 8).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_13 : ((q1.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_18 : ((q1.drop 18).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_20 : ((q1.drop 20).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_22 : ((q1.drop 22).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_25 : ((q1.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_28 : ((q1.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_31 : ((q1.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_36 : ((q1.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_41 : ((q1.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_45 : ((q1.drop 45).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_47 : ((q1.drop 47).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_50 : ((q1.drop 50).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_53 : ((q1.drop 53).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_55 : ((q1.drop 55).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_60 : ((q1.drop 60).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_65 : ((q1.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_68 : ((q1.drop 68).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_70 : ((q1.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_73 : ((q1.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_76 : ((q1.drop 76).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_80 : ((q1.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_83 : ((q1.drop 83).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_88 : ((q1.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_91 : ((q1.drop 91).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_93 : ((q1.drop 93).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_97 : ((q1.drop 97).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_100 : ((q1.drop 100).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_103 : ((q1.drop 103).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_105 : ((q1.drop 105).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok1 : nopt 7 s1 = false := by
  have h : q1.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p1_0 (all_chunk _ _ 4 4 p1_4 (all_chunk _ _ 8 5 p1_8 (all_chunk _ _ 13 5 p1_13 (all_chunk _ _ 18 2 p1_18 (all_chunk _ _ 20 2 p1_20 (all_chunk _ _ 22 3 p1_22 (all_chunk _ _ 25 3 p1_25 (all_chunk _ _ 28 3 p1_28 (all_chunk _ _ 31 5 p1_31 (all_chunk _ _ 36 5 p1_36 (all_chunk _ _ 41 4 p1_41 (all_chunk _ _ 45 2 p1_45 (all_chunk _ _ 47 3 p1_47 (all_chunk _ _ 50 3 p1_50 (all_chunk _ _ 53 2 p1_53 (all_chunk _ _ 55 5 p1_55 (all_chunk _ _ 60 5 p1_60 (all_chunk _ _ 65 3 p1_65 (all_chunk _ _ 68 2 p1_68 (all_chunk _ _ 70 3 p1_70 (all_chunk _ _ 73 3 p1_73 (all_chunk _ _ 76 4 p1_76 (all_chunk _ _ 80 3 p1_80 (all_chunk _ _ 83 5 p1_83 (all_chunk _ _ 88 3 p1_88 (all_chunk _ _ 91 2 p1_91 (all_chunk _ _ 93 4 p1_93 (all_chunk _ _ 97 3 p1_97 (all_chunk _ _ 100 3 p1_100 (all_chunk _ _ 103 2 p1_103 (all_chunk _ _ 105 3 p1_105 (by decide +kernel)))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s1 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_0 : ((q2.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_3 : ((q2.drop 3).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_9 : ((q2.drop 9).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_19 : ((q2.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_25 : ((q2.drop 25).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_31 : ((q2.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_35 : ((q2.drop 35).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_41 : ((q2.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_45 : ((q2.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_49 : ((q2.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_54 : ((q2.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_58 : ((q2.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_62 : ((q2.drop 62).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_71 : ((q2.drop 71).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_81 : ((q2.drop 81).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok2 : nopt 7 s2 = false := by
  have h : q2.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p2_0 (all_chunk _ _ 3 6 p2_3 (all_chunk _ _ 9 10 p2_9 (all_chunk _ _ 19 6 p2_19 (all_chunk _ _ 25 6 p2_25 (all_chunk _ _ 31 4 p2_31 (all_chunk _ _ 35 6 p2_35 (all_chunk _ _ 41 4 p2_41 (all_chunk _ _ 45 4 p2_45 (all_chunk _ _ 49 5 p2_49 (all_chunk _ _ 54 4 p2_54 (all_chunk _ _ 58 4 p2_58 (all_chunk _ _ 62 9 p2_62 (all_chunk _ _ 71 10 p2_71 (all_chunk _ _ 81 9 p2_81 (by decide +kernel))))))))))))))))
  rw [nopt_succ, show nisGoal s2 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_0 : ((q3.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_5 : ((q3.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_9 : ((q3.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_15 : ((q3.drop 15).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_21 : ((q3.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_25 : ((q3.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_29 : ((q3.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_33 : ((q3.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_36 : ((q3.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_40 : ((q3.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_44 : ((q3.drop 44).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_49 : ((q3.drop 49).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_58 : ((q3.drop 58).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_66 : ((q3.drop 66).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_75 : ((q3.drop 75).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_84 : ((q3.drop 84).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_90 : ((q3.drop 90).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok3 : nopt 7 s3 = false := by
  have h : q3.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p3_0 (all_chunk _ _ 5 4 p3_5 (all_chunk _ _ 9 6 p3_9 (all_chunk _ _ 15 6 p3_15 (all_chunk _ _ 21 4 p3_21 (all_chunk _ _ 25 4 p3_25 (all_chunk _ _ 29 4 p3_29 (all_chunk _ _ 33 3 p3_33 (all_chunk _ _ 36 4 p3_36 (all_chunk _ _ 40 4 p3_40 (all_chunk _ _ 44 5 p3_44 (all_chunk _ _ 49 9 p3_49 (all_chunk _ _ 58 8 p3_58 (all_chunk _ _ 66 9 p3_66 (all_chunk _ _ 75 9 p3_75 (all_chunk _ _ 84 6 p3_84 (all_chunk _ _ 90 6 p3_90 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s3 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_0 : ((q4.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_5 : ((q4.drop 5).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_7 : ((q4.drop 7).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_9 : ((q4.drop 9).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_12 : ((q4.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_15 : ((q4.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_18 : ((q4.drop 18).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_24 : ((q4.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_29 : ((q4.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_31 : ((q4.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_33 : ((q4.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_36 : ((q4.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_39 : ((q4.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_42 : ((q4.drop 42).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_48 : ((q4.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_53 : ((q4.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_56 : ((q4.drop 56).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_59 : ((q4.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_62 : ((q4.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_65 : ((q4.drop 65).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_67 : ((q4.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_70 : ((q4.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_73 : ((q4.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_76 : ((q4.drop 76).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_79 : ((q4.drop 79).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_82 : ((q4.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_86 : ((q4.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_90 : ((q4.drop 90).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_93 : ((q4.drop 93).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_97 : ((q4.drop 97).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_102 : ((q4.drop 102).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok4 : nopt 7 s4 = false := by
  have h : q4.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p4_0 (all_chunk _ _ 5 2 p4_5 (all_chunk _ _ 7 2 p4_7 (all_chunk _ _ 9 3 p4_9 (all_chunk _ _ 12 3 p4_12 (all_chunk _ _ 15 3 p4_15 (all_chunk _ _ 18 6 p4_18 (all_chunk _ _ 24 5 p4_24 (all_chunk _ _ 29 2 p4_29 (all_chunk _ _ 31 2 p4_31 (all_chunk _ _ 33 3 p4_33 (all_chunk _ _ 36 3 p4_36 (all_chunk _ _ 39 3 p4_39 (all_chunk _ _ 42 6 p4_42 (all_chunk _ _ 48 5 p4_48 (all_chunk _ _ 53 3 p4_53 (all_chunk _ _ 56 3 p4_56 (all_chunk _ _ 59 3 p4_59 (all_chunk _ _ 62 3 p4_62 (all_chunk _ _ 65 2 p4_65 (all_chunk _ _ 67 3 p4_67 (all_chunk _ _ 70 3 p4_70 (all_chunk _ _ 73 3 p4_73 (all_chunk _ _ 76 3 p4_76 (all_chunk _ _ 79 3 p4_79 (all_chunk _ _ 82 4 p4_82 (all_chunk _ _ 86 4 p4_86 (all_chunk _ _ 90 3 p4_90 (all_chunk _ _ 93 4 p4_93 (all_chunk _ _ 97 5 p4_97 (all_chunk _ _ 102 2 p4_102 (by decide +kernel))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s4 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_0 : ((q5.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_6 : ((q5.drop 6).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_15 : ((q5.drop 15).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_20 : ((q5.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_23 : ((q5.drop 23).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_28 : ((q5.drop 28).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_37 : ((q5.drop 37).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_42 : ((q5.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_45 : ((q5.drop 45).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_52 : ((q5.drop 52).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_58 : ((q5.drop 58).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_64 : ((q5.drop 64).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_69 : ((q5.drop 69).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_75 : ((q5.drop 75).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_80 : ((q5.drop 80).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_85 : ((q5.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_88 : ((q5.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_92 : ((q5.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok5 : nopt 7 s5 = false := by
  have h : q5.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p5_0 (all_chunk _ _ 6 9 p5_6 (all_chunk _ _ 15 5 p5_15 (all_chunk _ _ 20 3 p5_20 (all_chunk _ _ 23 5 p5_23 (all_chunk _ _ 28 9 p5_28 (all_chunk _ _ 37 5 p5_37 (all_chunk _ _ 42 3 p5_42 (all_chunk _ _ 45 7 p5_45 (all_chunk _ _ 52 6 p5_52 (all_chunk _ _ 58 6 p5_58 (all_chunk _ _ 64 5 p5_64 (all_chunk _ _ 69 6 p5_69 (all_chunk _ _ 75 5 p5_75 (all_chunk _ _ 80 5 p5_80 (all_chunk _ _ 85 3 p5_85 (all_chunk _ _ 88 4 p5_88 (all_chunk _ _ 92 4 p5_92 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s5 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_0 : ((q6.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_9 : ((q6.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_15 : ((q6.drop 15).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_24 : ((q6.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_29 : ((q6.drop 29).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_35 : ((q6.drop 35).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_44 : ((q6.drop 44).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_47 : ((q6.drop 47).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_51 : ((q6.drop 51).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_58 : ((q6.drop 58).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_67 : ((q6.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_72 : ((q6.drop 72).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_78 : ((q6.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_82 : ((q6.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_86 : ((q6.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_90 : ((q6.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok6 : nopt 7 s6 = false := by
  have h : q6.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p6_0 (all_chunk _ _ 9 6 p6_9 (all_chunk _ _ 15 9 p6_15 (all_chunk _ _ 24 5 p6_24 (all_chunk _ _ 29 6 p6_29 (all_chunk _ _ 35 9 p6_35 (all_chunk _ _ 44 3 p6_44 (all_chunk _ _ 47 4 p6_47 (all_chunk _ _ 51 7 p6_51 (all_chunk _ _ 58 9 p6_58 (all_chunk _ _ 67 5 p6_67 (all_chunk _ _ 72 6 p6_72 (all_chunk _ _ 78 4 p6_78 (all_chunk _ _ 82 4 p6_82 (all_chunk _ _ 86 4 p6_86 (all_chunk _ _ 90 2 p6_90 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s6 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_0 : ((q7.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_3 : ((q7.drop 3).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_9 : ((q7.drop 9).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_14 : ((q7.drop 14).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_19 : ((q7.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_23 : ((q7.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_26 : ((q7.drop 26).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_31 : ((q7.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_35 : ((q7.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_39 : ((q7.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_44 : ((q7.drop 44).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_49 : ((q7.drop 49).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_55 : ((q7.drop 55).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_65 : ((q7.drop 65).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_72 : ((q7.drop 72).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_81 : ((q7.drop 81).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_86 : ((q7.drop 86).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok7 : nopt 7 s7 = false := by
  have h : q7.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p7_0 (all_chunk _ _ 3 6 p7_3 (all_chunk _ _ 9 5 p7_9 (all_chunk _ _ 14 5 p7_14 (all_chunk _ _ 19 4 p7_19 (all_chunk _ _ 23 3 p7_23 (all_chunk _ _ 26 5 p7_26 (all_chunk _ _ 31 4 p7_31 (all_chunk _ _ 35 4 p7_35 (all_chunk _ _ 39 5 p7_39 (all_chunk _ _ 44 5 p7_44 (all_chunk _ _ 49 6 p7_49 (all_chunk _ _ 55 10 p7_55 (all_chunk _ _ 65 7 p7_65 (all_chunk _ _ 72 9 p7_72 (all_chunk _ _ 81 5 p7_81 (all_chunk _ _ 86 10 p7_86 (by decide +kernel))))))))))))))))))
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
theorem p8_5 : ((q8.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_8 : ((q8.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_11 : ((q8.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_14 : ((q8.drop 14).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_19 : ((q8.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_25 : ((q8.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_29 : ((q8.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_32 : ((q8.drop 32).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_35 : ((q8.drop 35).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_38 : ((q8.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_41 : ((q8.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_43 : ((q8.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_46 : ((q8.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_49 : ((q8.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_52 : ((q8.drop 52).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_55 : ((q8.drop 55).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_58 : ((q8.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_61 : ((q8.drop 61).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_64 : ((q8.drop 64).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_67 : ((q8.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_70 : ((q8.drop 70).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_74 : ((q8.drop 74).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_79 : ((q8.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_83 : ((q8.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_87 : ((q8.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_92 : ((q8.drop 92).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_97 : ((q8.drop 97).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_102 : ((q8.drop 102).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok8 : nopt 7 s8 = false := by
  have h : q8.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p8_0 (all_chunk _ _ 3 2 p8_3 (all_chunk _ _ 5 3 p8_5 (all_chunk _ _ 8 3 p8_8 (all_chunk _ _ 11 3 p8_11 (all_chunk _ _ 14 5 p8_14 (all_chunk _ _ 19 6 p8_19 (all_chunk _ _ 25 4 p8_25 (all_chunk _ _ 29 3 p8_29 (all_chunk _ _ 32 3 p8_32 (all_chunk _ _ 35 3 p8_35 (all_chunk _ _ 38 3 p8_38 (all_chunk _ _ 41 2 p8_41 (all_chunk _ _ 43 3 p8_43 (all_chunk _ _ 46 3 p8_46 (all_chunk _ _ 49 3 p8_49 (all_chunk _ _ 52 3 p8_52 (all_chunk _ _ 55 3 p8_55 (all_chunk _ _ 58 3 p8_58 (all_chunk _ _ 61 3 p8_61 (all_chunk _ _ 64 3 p8_64 (all_chunk _ _ 67 3 p8_67 (all_chunk _ _ 70 4 p8_70 (all_chunk _ _ 74 5 p8_74 (all_chunk _ _ 79 4 p8_79 (all_chunk _ _ 83 4 p8_83 (all_chunk _ _ 87 5 p8_87 (all_chunk _ _ 92 5 p8_92 (all_chunk _ _ 97 5 p8_97 (all_chunk _ _ 102 2 p8_102 (by decide +kernel)))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s8 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_0 : ((q9.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_7 : ((q9.drop 7).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_15 : ((q9.drop 15).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_20 : ((q9.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_23 : ((q9.drop 23).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_28 : ((q9.drop 28).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_36 : ((q9.drop 36).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_42 : ((q9.drop 42).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_48 : ((q9.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_53 : ((q9.drop 53).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_60 : ((q9.drop 60).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_66 : ((q9.drop 66).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_70 : ((q9.drop 70).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_77 : ((q9.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_81 : ((q9.drop 81).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_86 : ((q9.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_90 : ((q9.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_94 : ((q9.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok9 : nopt 7 s9 = false := by
  have h : q9.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p9_0 (all_chunk _ _ 7 8 p9_7 (all_chunk _ _ 15 5 p9_15 (all_chunk _ _ 20 3 p9_20 (all_chunk _ _ 23 5 p9_23 (all_chunk _ _ 28 8 p9_28 (all_chunk _ _ 36 6 p9_36 (all_chunk _ _ 42 6 p9_42 (all_chunk _ _ 48 5 p9_48 (all_chunk _ _ 53 7 p9_53 (all_chunk _ _ 60 6 p9_60 (all_chunk _ _ 66 4 p9_66 (all_chunk _ _ 70 7 p9_70 (all_chunk _ _ 77 4 p9_77 (all_chunk _ _ 81 5 p9_81 (all_chunk _ _ 86 4 p9_86 (all_chunk _ _ 90 4 p9_90 (all_chunk _ _ 94 2 p9_94 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s9 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_0 : ((q10.drop 0).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_9 : ((q10.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_15 : ((q10.drop 15).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_24 : ((q10.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_29 : ((q10.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_34 : ((q10.drop 34).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_38 : ((q10.drop 38).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_47 : ((q10.drop 47).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_54 : ((q10.drop 54).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_60 : ((q10.drop 60).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_69 : ((q10.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_72 : ((q10.drop 72).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_78 : ((q10.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_82 : ((q10.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_86 : ((q10.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_90 : ((q10.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok10 : nopt 7 s10 = false := by
  have h : q10.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 9 p10_0 (all_chunk _ _ 9 6 p10_9 (all_chunk _ _ 15 9 p10_15 (all_chunk _ _ 24 5 p10_24 (all_chunk _ _ 29 5 p10_29 (all_chunk _ _ 34 4 p10_34 (all_chunk _ _ 38 9 p10_38 (all_chunk _ _ 47 7 p10_47 (all_chunk _ _ 54 6 p10_54 (all_chunk _ _ 60 9 p10_60 (all_chunk _ _ 69 3 p10_69 (all_chunk _ _ 72 6 p10_72 (all_chunk _ _ 78 4 p10_78 (all_chunk _ _ 82 4 p10_82 (all_chunk _ _ 86 4 p10_86 (all_chunk _ _ 90 2 p10_90 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s10 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_0 : ((q11.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_3 : ((q11.drop 3).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_9 : ((q11.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_13 : ((q11.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_17 : ((q11.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_20 : ((q11.drop 20).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_25 : ((q11.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_30 : ((q11.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_34 : ((q11.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_39 : ((q11.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_44 : ((q11.drop 44).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_48 : ((q11.drop 48).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_56 : ((q11.drop 56).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_65 : ((q11.drop 65).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_71 : ((q11.drop 71).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_77 : ((q11.drop 77).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_87 : ((q11.drop 87).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok11 : nopt 7 s11 = false := by
  have h : q11.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p11_0 (all_chunk _ _ 3 6 p11_3 (all_chunk _ _ 9 4 p11_9 (all_chunk _ _ 13 4 p11_13 (all_chunk _ _ 17 3 p11_17 (all_chunk _ _ 20 5 p11_20 (all_chunk _ _ 25 5 p11_25 (all_chunk _ _ 30 4 p11_30 (all_chunk _ _ 34 5 p11_34 (all_chunk _ _ 39 5 p11_39 (all_chunk _ _ 44 4 p11_44 (all_chunk _ _ 48 8 p11_48 (all_chunk _ _ 56 9 p11_56 (all_chunk _ _ 65 6 p11_65 (all_chunk _ _ 71 6 p11_71 (all_chunk _ _ 77 10 p11_77 (all_chunk _ _ 87 9 p11_87 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s11 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_0 : ((q12.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_2 : ((q12.drop 2).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_5 : ((q12.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_8 : ((q12.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_12 : ((q12.drop 12).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_14 : ((q12.drop 14).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_16 : ((q12.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_19 : ((q12.drop 19).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_22 : ((q12.drop 22).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_25 : ((q12.drop 25).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_27 : ((q12.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_30 : ((q12.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_33 : ((q12.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_36 : ((q12.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_39 : ((q12.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_42 : ((q12.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_45 : ((q12.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_48 : ((q12.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_51 : ((q12.drop 51).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_54 : ((q12.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_58 : ((q12.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_63 : ((q12.drop 63).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_68 : ((q12.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_72 : ((q12.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_76 : ((q12.drop 76).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_81 : ((q12.drop 81).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_87 : ((q12.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_92 : ((q12.drop 92).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_97 : ((q12.drop 97).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_102 : ((q12.drop 102).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok12 : nopt 7 s12 = false := by
  have h : q12.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p12_0 (all_chunk _ _ 2 3 p12_2 (all_chunk _ _ 5 3 p12_5 (all_chunk _ _ 8 4 p12_8 (all_chunk _ _ 12 2 p12_12 (all_chunk _ _ 14 2 p12_14 (all_chunk _ _ 16 3 p12_16 (all_chunk _ _ 19 3 p12_19 (all_chunk _ _ 22 3 p12_22 (all_chunk _ _ 25 2 p12_25 (all_chunk _ _ 27 3 p12_27 (all_chunk _ _ 30 3 p12_30 (all_chunk _ _ 33 3 p12_33 (all_chunk _ _ 36 3 p12_36 (all_chunk _ _ 39 3 p12_39 (all_chunk _ _ 42 3 p12_42 (all_chunk _ _ 45 3 p12_45 (all_chunk _ _ 48 3 p12_48 (all_chunk _ _ 51 3 p12_51 (all_chunk _ _ 54 4 p12_54 (all_chunk _ _ 58 5 p12_58 (all_chunk _ _ 63 5 p12_63 (all_chunk _ _ 68 4 p12_68 (all_chunk _ _ 72 4 p12_72 (all_chunk _ _ 76 5 p12_76 (all_chunk _ _ 81 6 p12_81 (all_chunk _ _ 87 5 p12_87 (all_chunk _ _ 92 5 p12_92 (all_chunk _ _ 97 5 p12_97 (all_chunk _ _ 102 2 p12_102 (by decide +kernel)))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s12 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_0 : ((q13.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_7 : ((q13.drop 7).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_14 : ((q13.drop 14).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_20 : ((q13.drop 20).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_27 : ((q13.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_31 : ((q13.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_35 : ((q13.drop 35).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_42 : ((q13.drop 42).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_50 : ((q13.drop 50).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_54 : ((q13.drop 54).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_62 : ((q13.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_67 : ((q13.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_70 : ((q13.drop 70).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_77 : ((q13.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_81 : ((q13.drop 81).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_86 : ((q13.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_90 : ((q13.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_94 : ((q13.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok13 : nopt 7 s13 = false := by
  have h : q13.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p13_0 (all_chunk _ _ 7 7 p13_7 (all_chunk _ _ 14 6 p13_14 (all_chunk _ _ 20 7 p13_20 (all_chunk _ _ 27 4 p13_27 (all_chunk _ _ 31 4 p13_31 (all_chunk _ _ 35 7 p13_35 (all_chunk _ _ 42 8 p13_42 (all_chunk _ _ 50 4 p13_50 (all_chunk _ _ 54 8 p13_54 (all_chunk _ _ 62 5 p13_62 (all_chunk _ _ 67 3 p13_67 (all_chunk _ _ 70 7 p13_70 (all_chunk _ _ 77 4 p13_77 (all_chunk _ _ 81 5 p13_81 (all_chunk _ _ 86 4 p13_86 (all_chunk _ _ 90 4 p13_90 (all_chunk _ _ 94 2 p13_94 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s13 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_0 : ((q14.drop 0).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_10 : ((q14.drop 10).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_15 : ((q14.drop 15).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_20 : ((q14.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_24 : ((q14.drop 24).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_34 : ((q14.drop 34).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_42 : ((q14.drop 42).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_48 : ((q14.drop 48).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_57 : ((q14.drop 57).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_60 : ((q14.drop 60).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_66 : ((q14.drop 66).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_72 : ((q14.drop 72).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_78 : ((q14.drop 78).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_84 : ((q14.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_88 : ((q14.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok14 : nopt 7 s14 = false := by
  have h : q14.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 10 p14_0 (all_chunk _ _ 10 5 p14_10 (all_chunk _ _ 15 5 p14_15 (all_chunk _ _ 20 4 p14_20 (all_chunk _ _ 24 10 p14_24 (all_chunk _ _ 34 8 p14_34 (all_chunk _ _ 42 6 p14_42 (all_chunk _ _ 48 9 p14_48 (all_chunk _ _ 57 3 p14_57 (all_chunk _ _ 60 6 p14_60 (all_chunk _ _ 66 6 p14_66 (all_chunk _ _ 72 6 p14_72 (all_chunk _ _ 78 6 p14_78 (all_chunk _ _ 84 4 p14_84 (all_chunk _ _ 88 4 p14_88 (by decide +kernel))))))))))))))))
  rw [nopt_succ, show nisGoal s14 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_0 : ((q15.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_4 : ((q15.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_7 : ((q15.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_10 : ((q15.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_13 : ((q15.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_18 : ((q15.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_22 : ((q15.drop 22).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_28 : ((q15.drop 28).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_33 : ((q15.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_36 : ((q15.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_41 : ((q15.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_45 : ((q15.drop 45).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_50 : ((q15.drop 50).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_56 : ((q15.drop 56).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_63 : ((q15.drop 63).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_70 : ((q15.drop 70).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_79 : ((q15.drop 79).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_89 : ((q15.drop 89).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok15 : nopt 7 s15 = false := by
  have h : q15.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p15_0 (all_chunk _ _ 4 3 p15_4 (all_chunk _ _ 7 3 p15_7 (all_chunk _ _ 10 3 p15_10 (all_chunk _ _ 13 5 p15_13 (all_chunk _ _ 18 4 p15_18 (all_chunk _ _ 22 6 p15_22 (all_chunk _ _ 28 5 p15_28 (all_chunk _ _ 33 3 p15_33 (all_chunk _ _ 36 5 p15_36 (all_chunk _ _ 41 4 p15_41 (all_chunk _ _ 45 5 p15_45 (all_chunk _ _ 50 6 p15_50 (all_chunk _ _ 56 7 p15_56 (all_chunk _ _ 63 7 p15_63 (all_chunk _ _ 70 9 p15_70 (all_chunk _ _ 79 10 p15_79 (all_chunk _ _ 89 7 p15_89 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s15 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_0 : ((q16.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_5 : ((q16.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_9 : ((q16.drop 9).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_14 : ((q16.drop 14).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_22 : ((q16.drop 22).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_27 : ((q16.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_31 : ((q16.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_36 : ((q16.drop 36).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_44 : ((q16.drop 44).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_51 : ((q16.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_55 : ((q16.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_59 : ((q16.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_63 : ((q16.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_66 : ((q16.drop 66).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_71 : ((q16.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_75 : ((q16.drop 75).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_83 : ((q16.drop 83).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_88 : ((q16.drop 88).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok16 : nopt 7 s16 = false := by
  have h : q16.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p16_0 (all_chunk _ _ 5 4 p16_5 (all_chunk _ _ 9 5 p16_9 (all_chunk _ _ 14 8 p16_14 (all_chunk _ _ 22 5 p16_22 (all_chunk _ _ 27 4 p16_27 (all_chunk _ _ 31 5 p16_31 (all_chunk _ _ 36 8 p16_36 (all_chunk _ _ 44 7 p16_44 (all_chunk _ _ 51 4 p16_51 (all_chunk _ _ 55 4 p16_55 (all_chunk _ _ 59 4 p16_59 (all_chunk _ _ 63 3 p16_63 (all_chunk _ _ 66 5 p16_66 (all_chunk _ _ 71 4 p16_71 (all_chunk _ _ 75 8 p16_75 (all_chunk _ _ 83 5 p16_83 (all_chunk _ _ 88 8 p16_88 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s16 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_0 : ((q17.drop 0).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_10 : ((q17.drop 10).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_16 : ((q17.drop 16).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_21 : ((q17.drop 21).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_31 : ((q17.drop 31).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_37 : ((q17.drop 37).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_45 : ((q17.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_53 : ((q17.drop 53).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_57 : ((q17.drop 57).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_61 : ((q17.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_69 : ((q17.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_72 : ((q17.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_76 : ((q17.drop 76).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_81 : ((q17.drop 81).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_87 : ((q17.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_91 : ((q17.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok17 : nopt 7 s17 = false := by
  have h : q17.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 10 p17_0 (all_chunk _ _ 10 6 p17_10 (all_chunk _ _ 16 5 p17_16 (all_chunk _ _ 21 10 p17_21 (all_chunk _ _ 31 6 p17_31 (all_chunk _ _ 37 8 p17_37 (all_chunk _ _ 45 8 p17_45 (all_chunk _ _ 53 4 p17_53 (all_chunk _ _ 57 4 p17_57 (all_chunk _ _ 61 8 p17_61 (all_chunk _ _ 69 3 p17_69 (all_chunk _ _ 72 4 p17_72 (all_chunk _ _ 76 5 p17_76 (all_chunk _ _ 81 6 p17_81 (all_chunk _ _ 87 4 p17_87 (all_chunk _ _ 91 3 p17_91 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s17 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_0 : ((q18.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_6 : ((q18.drop 6).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_13 : ((q18.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_17 : ((q18.drop 17).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_26 : ((q18.drop 26).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_33 : ((q18.drop 33).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_37 : ((q18.drop 37).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_42 : ((q18.drop 42).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_49 : ((q18.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_54 : ((q18.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_58 : ((q18.drop 58).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_66 : ((q18.drop 66).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_72 : ((q18.drop 72).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_77 : ((q18.drop 77).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_80 : ((q18.drop 80).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_85 : ((q18.drop 85).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_90 : ((q18.drop 90).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_96 : ((q18.drop 96).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok18 : nopt 7 s18 = false := by
  have h : q18.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p18_0 (all_chunk _ _ 6 7 p18_6 (all_chunk _ _ 13 4 p18_13 (all_chunk _ _ 17 9 p18_17 (all_chunk _ _ 26 7 p18_26 (all_chunk _ _ 33 4 p18_33 (all_chunk _ _ 37 5 p18_37 (all_chunk _ _ 42 7 p18_42 (all_chunk _ _ 49 5 p18_49 (all_chunk _ _ 54 4 p18_54 (all_chunk _ _ 58 8 p18_58 (all_chunk _ _ 66 6 p18_66 (all_chunk _ _ 72 5 p18_72 (all_chunk _ _ 77 3 p18_77 (all_chunk _ _ 80 5 p18_80 (all_chunk _ _ 85 5 p18_85 (all_chunk _ _ 90 6 p18_90 (all_chunk _ _ 96 2 p18_96 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s18 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_0 : ((q19.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_3 : ((q19.drop 3).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_5 : ((q19.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_8 : ((q19.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_11 : ((q19.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_16 : ((q19.drop 16).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_22 : ((q19.drop 22).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_28 : ((q19.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_31 : ((q19.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_33 : ((q19.drop 33).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_37 : ((q19.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_40 : ((q19.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_43 : ((q19.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_46 : ((q19.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_49 : ((q19.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_52 : ((q19.drop 52).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_57 : ((q19.drop 57).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_60 : ((q19.drop 60).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_63 : ((q19.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_67 : ((q19.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_71 : ((q19.drop 71).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_77 : ((q19.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_83 : ((q19.drop 83).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_89 : ((q19.drop 89).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_94 : ((q19.drop 94).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_99 : ((q19.drop 99).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok19 : nopt 7 s19 = false := by
  have h : q19.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p19_0 (all_chunk _ _ 3 2 p19_3 (all_chunk _ _ 5 3 p19_5 (all_chunk _ _ 8 3 p19_8 (all_chunk _ _ 11 5 p19_11 (all_chunk _ _ 16 6 p19_16 (all_chunk _ _ 22 6 p19_22 (all_chunk _ _ 28 3 p19_28 (all_chunk _ _ 31 2 p19_31 (all_chunk _ _ 33 4 p19_33 (all_chunk _ _ 37 3 p19_37 (all_chunk _ _ 40 3 p19_40 (all_chunk _ _ 43 3 p19_43 (all_chunk _ _ 46 3 p19_46 (all_chunk _ _ 49 3 p19_49 (all_chunk _ _ 52 5 p19_52 (all_chunk _ _ 57 3 p19_57 (all_chunk _ _ 60 3 p19_60 (all_chunk _ _ 63 4 p19_63 (all_chunk _ _ 67 4 p19_67 (all_chunk _ _ 71 6 p19_71 (all_chunk _ _ 77 6 p19_77 (all_chunk _ _ 83 6 p19_83 (all_chunk _ _ 89 5 p19_89 (all_chunk _ _ 94 5 p19_94 (all_chunk _ _ 99 1 p19_99 (by decide +kernel)))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s19 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_0 : ((q20.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_2 : ((q20.drop 2).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_7 : ((q20.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_11 : ((q20.drop 11).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_18 : ((q20.drop 18).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_27 : ((q20.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_31 : ((q20.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_35 : ((q20.drop 35).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_38 : ((q20.drop 38).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_42 : ((q20.drop 42).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_47 : ((q20.drop 47).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_50 : ((q20.drop 50).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_54 : ((q20.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_58 : ((q20.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_62 : ((q20.drop 62).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_66 : ((q20.drop 66).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_73 : ((q20.drop 73).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_79 : ((q20.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_87 : ((q20.drop 87).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_95 : ((q20.drop 95).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok20 : nopt 7 s20 = false := by
  have h : q20.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p20_0 (all_chunk _ _ 2 5 p20_2 (all_chunk _ _ 7 4 p20_7 (all_chunk _ _ 11 7 p20_11 (all_chunk _ _ 18 9 p20_18 (all_chunk _ _ 27 4 p20_27 (all_chunk _ _ 31 4 p20_31 (all_chunk _ _ 35 3 p20_35 (all_chunk _ _ 38 4 p20_38 (all_chunk _ _ 42 5 p20_42 (all_chunk _ _ 47 3 p20_47 (all_chunk _ _ 50 4 p20_50 (all_chunk _ _ 54 4 p20_54 (all_chunk _ _ 58 4 p20_58 (all_chunk _ _ 62 4 p20_62 (all_chunk _ _ 66 7 p20_66 (all_chunk _ _ 73 6 p20_73 (all_chunk _ _ 79 8 p20_79 (all_chunk _ _ 87 8 p20_87 (all_chunk _ _ 95 1 p20_95 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s20 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_0 : ((q21.drop 0).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_10 : ((q21.drop 10).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_16 : ((q21.drop 16).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_21 : ((q21.drop 21).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_31 : ((q21.drop 31).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_37 : ((q21.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_41 : ((q21.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_45 : ((q21.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_53 : ((q21.drop 53).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_60 : ((q21.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_64 : ((q21.drop 64).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_71 : ((q21.drop 71).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_76 : ((q21.drop 76).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_81 : ((q21.drop 81).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_87 : ((q21.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_91 : ((q21.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok21 : nopt 7 s21 = false := by
  have h : q21.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 10 p21_0 (all_chunk _ _ 10 6 p21_10 (all_chunk _ _ 16 5 p21_16 (all_chunk _ _ 21 10 p21_21 (all_chunk _ _ 31 6 p21_31 (all_chunk _ _ 37 4 p21_37 (all_chunk _ _ 41 4 p21_41 (all_chunk _ _ 45 8 p21_45 (all_chunk _ _ 53 7 p21_53 (all_chunk _ _ 60 4 p21_60 (all_chunk _ _ 64 7 p21_64 (all_chunk _ _ 71 5 p21_71 (all_chunk _ _ 76 5 p21_76 (all_chunk _ _ 81 6 p21_81 (all_chunk _ _ 87 4 p21_87 (all_chunk _ _ 91 3 p21_91 (by decide +kernel)))))))))))))))))
  rw [nopt_succ, show nisGoal s21 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_0 : ((q22.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_7 : ((q22.drop 7).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_13 : ((q22.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_17 : ((q22.drop 17).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_26 : ((q22.drop 26).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_33 : ((q22.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_38 : ((q22.drop 38).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_42 : ((q22.drop 42).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_50 : ((q22.drop 50).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_56 : ((q22.drop 56).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_62 : ((q22.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_67 : ((q22.drop 67).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_75 : ((q22.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_78 : ((q22.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_82 : ((q22.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_86 : ((q22.drop 86).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_91 : ((q22.drop 91).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok22 : nopt 7 s22 = false := by
  have h : q22.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p22_0 (all_chunk _ _ 7 6 p22_7 (all_chunk _ _ 13 4 p22_13 (all_chunk _ _ 17 9 p22_17 (all_chunk _ _ 26 7 p22_26 (all_chunk _ _ 33 5 p22_33 (all_chunk _ _ 38 4 p22_38 (all_chunk _ _ 42 8 p22_42 (all_chunk _ _ 50 6 p22_50 (all_chunk _ _ 56 6 p22_56 (all_chunk _ _ 62 5 p22_62 (all_chunk _ _ 67 8 p22_67 (all_chunk _ _ 75 3 p22_75 (all_chunk _ _ 78 4 p22_78 (all_chunk _ _ 82 4 p22_82 (all_chunk _ _ 86 5 p22_86 (all_chunk _ _ 91 7 p22_91 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s22 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_0 : ((q23.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_3 : ((q23.drop 3).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_5 : ((q23.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_8 : ((q23.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_11 : ((q23.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_16 : ((q23.drop 16).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_22 : ((q23.drop 22).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_28 : ((q23.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_31 : ((q23.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_34 : ((q23.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_37 : ((q23.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_41 : ((q23.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_43 : ((q23.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_46 : ((q23.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_49 : ((q23.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_52 : ((q23.drop 52).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_57 : ((q23.drop 57).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_60 : ((q23.drop 60).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_63 : ((q23.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_67 : ((q23.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_71 : ((q23.drop 71).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_77 : ((q23.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_83 : ((q23.drop 83).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_89 : ((q23.drop 89).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_95 : ((q23.drop 95).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok23 : nopt 7 s23 = false := by
  have h : q23.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p23_0 (all_chunk _ _ 3 2 p23_3 (all_chunk _ _ 5 3 p23_5 (all_chunk _ _ 8 3 p23_8 (all_chunk _ _ 11 5 p23_11 (all_chunk _ _ 16 6 p23_16 (all_chunk _ _ 22 6 p23_22 (all_chunk _ _ 28 3 p23_28 (all_chunk _ _ 31 3 p23_31 (all_chunk _ _ 34 3 p23_34 (all_chunk _ _ 37 4 p23_37 (all_chunk _ _ 41 2 p23_41 (all_chunk _ _ 43 3 p23_43 (all_chunk _ _ 46 3 p23_46 (all_chunk _ _ 49 3 p23_49 (all_chunk _ _ 52 5 p23_52 (all_chunk _ _ 57 3 p23_57 (all_chunk _ _ 60 3 p23_60 (all_chunk _ _ 63 4 p23_63 (all_chunk _ _ 67 4 p23_67 (all_chunk _ _ 71 6 p23_71 (all_chunk _ _ 77 6 p23_77 (all_chunk _ _ 83 6 p23_83 (all_chunk _ _ 89 6 p23_89 (all_chunk _ _ 95 5 p23_95 (by decide +kernel))))))))))))))))))))))))))
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
theorem p24_7 : ((q24.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_11 : ((q24.drop 11).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_13 : ((q24.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_18 : ((q24.drop 18).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_20 : ((q24.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_24 : ((q24.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_29 : ((q24.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_32 : ((q24.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_36 : ((q24.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_40 : ((q24.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_44 : ((q24.drop 44).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_48 : ((q24.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_54 : ((q24.drop 54).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_61 : ((q24.drop 61).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_67 : ((q24.drop 67).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_74 : ((q24.drop 74).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_82 : ((q24.drop 82).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_91 : ((q24.drop 91).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok24 : nopt 7 s24 = false := by
  have h : q24.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p24_0 (all_chunk _ _ 4 3 p24_4 (all_chunk _ _ 7 4 p24_7 (all_chunk _ _ 11 2 p24_11 (all_chunk _ _ 13 5 p24_13 (all_chunk _ _ 18 2 p24_18 (all_chunk _ _ 20 4 p24_20 (all_chunk _ _ 24 5 p24_24 (all_chunk _ _ 29 3 p24_29 (all_chunk _ _ 32 4 p24_32 (all_chunk _ _ 36 4 p24_36 (all_chunk _ _ 40 4 p24_40 (all_chunk _ _ 44 4 p24_44 (all_chunk _ _ 48 6 p24_48 (all_chunk _ _ 54 7 p24_54 (all_chunk _ _ 61 6 p24_61 (all_chunk _ _ 67 7 p24_67 (all_chunk _ _ 74 8 p24_74 (all_chunk _ _ 82 9 p24_82 (all_chunk _ _ 91 5 p24_91 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s24 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_0 : ((q25.drop 0).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_10 : ((q25.drop 10).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_17 : ((q25.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_21 : ((q25.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_25 : ((q25.drop 25).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_33 : ((q25.drop 33).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_42 : ((q25.drop 42).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_47 : ((q25.drop 47).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_56 : ((q25.drop 56).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_62 : ((q25.drop 62).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_70 : ((q25.drop 70).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_74 : ((q25.drop 74).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_78 : ((q25.drop 78).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_85 : ((q25.drop 85).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_89 : ((q25.drop 89).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok25 : nopt 7 s25 = false := by
  have h : q25.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 10 p25_0 (all_chunk _ _ 10 7 p25_10 (all_chunk _ _ 17 4 p25_17 (all_chunk _ _ 21 4 p25_21 (all_chunk _ _ 25 8 p25_25 (all_chunk _ _ 33 9 p25_33 (all_chunk _ _ 42 5 p25_42 (all_chunk _ _ 47 9 p25_47 (all_chunk _ _ 56 6 p25_56 (all_chunk _ _ 62 8 p25_62 (all_chunk _ _ 70 4 p25_70 (all_chunk _ _ 74 4 p25_74 (all_chunk _ _ 78 7 p25_78 (all_chunk _ _ 85 4 p25_85 (all_chunk _ _ 89 5 p25_89 (by decide +kernel))))))))))))))))
  rw [nopt_succ, show nisGoal s25 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_0 : ((q26.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_7 : ((q26.drop 7).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_13 : ((q26.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_18 : ((q26.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_22 : ((q26.drop 22).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_30 : ((q26.drop 30).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_36 : ((q26.drop 36).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_42 : ((q26.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_46 : ((q26.drop 46).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_51 : ((q26.drop 51).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_58 : ((q26.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_62 : ((q26.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_67 : ((q26.drop 67).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_75 : ((q26.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_78 : ((q26.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_82 : ((q26.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_86 : ((q26.drop 86).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_91 : ((q26.drop 91).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok26 : nopt 7 s26 = false := by
  have h : q26.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p26_0 (all_chunk _ _ 7 6 p26_7 (all_chunk _ _ 13 5 p26_13 (all_chunk _ _ 18 4 p26_18 (all_chunk _ _ 22 8 p26_22 (all_chunk _ _ 30 6 p26_30 (all_chunk _ _ 36 6 p26_36 (all_chunk _ _ 42 4 p26_42 (all_chunk _ _ 46 5 p26_46 (all_chunk _ _ 51 7 p26_51 (all_chunk _ _ 58 4 p26_58 (all_chunk _ _ 62 5 p26_62 (all_chunk _ _ 67 8 p26_67 (all_chunk _ _ 75 3 p26_75 (all_chunk _ _ 78 4 p26_78 (all_chunk _ _ 82 4 p26_82 (all_chunk _ _ 86 5 p26_86 (all_chunk _ _ 91 7 p26_91 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s26 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_0 : ((q27.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_3 : ((q27.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_6 : ((q27.drop 6).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_9 : ((q27.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_13 : ((q27.drop 13).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_15 : ((q27.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_18 : ((q27.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_21 : ((q27.drop 21).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_24 : ((q27.drop 24).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_27 : ((q27.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_30 : ((q27.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_33 : ((q27.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_36 : ((q27.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_41 : ((q27.drop 41).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_44 : ((q27.drop 44).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_47 : ((q27.drop 47).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_51 : ((q27.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_55 : ((q27.drop 55).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_60 : ((q27.drop 60).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_67 : ((q27.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_72 : ((q27.drop 72).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_77 : ((q27.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_83 : ((q27.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_90 : ((q27.drop 90).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_96 : ((q27.drop 96).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok27 : nopt 7 s27 = false := by
  have h : q27.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p27_0 (all_chunk _ _ 3 3 p27_3 (all_chunk _ _ 6 3 p27_6 (all_chunk _ _ 9 4 p27_9 (all_chunk _ _ 13 2 p27_13 (all_chunk _ _ 15 3 p27_15 (all_chunk _ _ 18 3 p27_18 (all_chunk _ _ 21 3 p27_21 (all_chunk _ _ 24 3 p27_24 (all_chunk _ _ 27 3 p27_27 (all_chunk _ _ 30 3 p27_30 (all_chunk _ _ 33 3 p27_33 (all_chunk _ _ 36 5 p27_36 (all_chunk _ _ 41 3 p27_41 (all_chunk _ _ 44 3 p27_44 (all_chunk _ _ 47 4 p27_47 (all_chunk _ _ 51 4 p27_51 (all_chunk _ _ 55 5 p27_55 (all_chunk _ _ 60 7 p27_60 (all_chunk _ _ 67 5 p27_67 (all_chunk _ _ 72 5 p27_72 (all_chunk _ _ 77 6 p27_77 (all_chunk _ _ 83 7 p27_83 (all_chunk _ _ 90 6 p27_90 (all_chunk _ _ 96 4 p27_96 (by decide +kernel))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s27 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_0 : ((q28.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_3 : ((q28.drop 3).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_4 : ((q28.drop 4).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_5 : ((q28.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_8 : ((q28.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_11 : ((q28.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_16 : ((q28.drop 16).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_22 : ((q28.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_26 : ((q28.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_30 : ((q28.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_33 : ((q28.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_36 : ((q28.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_40 : ((q28.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_43 : ((q28.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_46 : ((q28.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_49 : ((q28.drop 49).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_51 : ((q28.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_55 : ((q28.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_59 : ((q28.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_62 : ((q28.drop 62).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_64 : ((q28.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_68 : ((q28.drop 68).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_69 : ((q28.drop 69).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_70 : ((q28.drop 70).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_74 : ((q28.drop 74).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_79 : ((q28.drop 79).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_84 : ((q28.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_88 : ((q28.drop 88).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_93 : ((q28.drop 93).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok28 : nopt 7 s28 = false := by
  have h : q28.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p28_0 (all_chunk _ _ 3 1 p28_3 (all_chunk _ _ 4 1 p28_4 (all_chunk _ _ 5 3 p28_5 (all_chunk _ _ 8 3 p28_8 (all_chunk _ _ 11 5 p28_11 (all_chunk _ _ 16 6 p28_16 (all_chunk _ _ 22 4 p28_22 (all_chunk _ _ 26 4 p28_26 (all_chunk _ _ 30 3 p28_30 (all_chunk _ _ 33 3 p28_33 (all_chunk _ _ 36 4 p28_36 (all_chunk _ _ 40 3 p28_40 (all_chunk _ _ 43 3 p28_43 (all_chunk _ _ 46 3 p28_46 (all_chunk _ _ 49 2 p28_49 (all_chunk _ _ 51 4 p28_51 (all_chunk _ _ 55 4 p28_55 (all_chunk _ _ 59 3 p28_59 (all_chunk _ _ 62 2 p28_62 (all_chunk _ _ 64 4 p28_64 (all_chunk _ _ 68 1 p28_68 (all_chunk _ _ 69 1 p28_69 (all_chunk _ _ 70 4 p28_70 (all_chunk _ _ 74 5 p28_74 (all_chunk _ _ 79 5 p28_79 (all_chunk _ _ 84 4 p28_84 (all_chunk _ _ 88 5 p28_88 (all_chunk _ _ 93 2 p28_93 (by decide +kernel))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s28 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_0 : ((q29.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_2 : ((q29.drop 2).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_6 : ((q29.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_8 : ((q29.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_12 : ((q29.drop 12).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_14 : ((q29.drop 14).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_17 : ((q29.drop 17).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_22 : ((q29.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_26 : ((q29.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_29 : ((q29.drop 29).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_30 : ((q29.drop 30).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_31 : ((q29.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_36 : ((q29.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_39 : ((q29.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_42 : ((q29.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_45 : ((q29.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_49 : ((q29.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_54 : ((q29.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_58 : ((q29.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_62 : ((q29.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_65 : ((q29.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_68 : ((q29.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_72 : ((q29.drop 72).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_77 : ((q29.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_81 : ((q29.drop 81).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_86 : ((q29.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_90 : ((q29.drop 90).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_93 : ((q29.drop 93).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_96 : ((q29.drop 96).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_101 : ((q29.drop 101).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok29 : nopt 7 s29 = false := by
  have h : q29.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p29_0 (all_chunk _ _ 2 4 p29_2 (all_chunk _ _ 6 2 p29_6 (all_chunk _ _ 8 4 p29_8 (all_chunk _ _ 12 2 p29_12 (all_chunk _ _ 14 3 p29_14 (all_chunk _ _ 17 5 p29_17 (all_chunk _ _ 22 4 p29_22 (all_chunk _ _ 26 3 p29_26 (all_chunk _ _ 29 1 p29_29 (all_chunk _ _ 30 1 p29_30 (all_chunk _ _ 31 5 p29_31 (all_chunk _ _ 36 3 p29_36 (all_chunk _ _ 39 3 p29_39 (all_chunk _ _ 42 3 p29_42 (all_chunk _ _ 45 4 p29_45 (all_chunk _ _ 49 5 p29_49 (all_chunk _ _ 54 4 p29_54 (all_chunk _ _ 58 4 p29_58 (all_chunk _ _ 62 3 p29_62 (all_chunk _ _ 65 3 p29_65 (all_chunk _ _ 68 4 p29_68 (all_chunk _ _ 72 5 p29_72 (all_chunk _ _ 77 4 p29_77 (all_chunk _ _ 81 5 p29_81 (all_chunk _ _ 86 4 p29_86 (all_chunk _ _ 90 3 p29_90 (all_chunk _ _ 93 3 p29_93 (all_chunk _ _ 96 5 p29_96 (all_chunk _ _ 101 2 p29_101 (by decide +kernel)))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s29 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_0 : ((q30.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_5 : ((q30.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_10 : ((q30.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_14 : ((q30.drop 14).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_22 : ((q30.drop 22).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_27 : ((q30.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_31 : ((q30.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_34 : ((q30.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_39 : ((q30.drop 39).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_47 : ((q30.drop 47).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_55 : ((q30.drop 55).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_58 : ((q30.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_62 : ((q30.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_65 : ((q30.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_69 : ((q30.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_73 : ((q30.drop 73).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_79 : ((q30.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_87 : ((q30.drop 87).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok30 : nopt 7 s30 = false := by
  have h : q30.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p30_0 (all_chunk _ _ 5 5 p30_5 (all_chunk _ _ 10 4 p30_10 (all_chunk _ _ 14 8 p30_14 (all_chunk _ _ 22 5 p30_22 (all_chunk _ _ 27 4 p30_27 (all_chunk _ _ 31 3 p30_31 (all_chunk _ _ 34 5 p30_34 (all_chunk _ _ 39 8 p30_39 (all_chunk _ _ 47 8 p30_47 (all_chunk _ _ 55 3 p30_55 (all_chunk _ _ 58 4 p30_58 (all_chunk _ _ 62 3 p30_62 (all_chunk _ _ 65 4 p30_65 (all_chunk _ _ 69 4 p30_69 (all_chunk _ _ 73 6 p30_73 (all_chunk _ _ 79 8 p30_79 (all_chunk _ _ 87 9 p30_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s30 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_0 : ((q31.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_3 : ((q31.drop 3).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_7 : ((q31.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_12 : ((q31.drop 12).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_20 : ((q31.drop 20).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_27 : ((q31.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_31 : ((q31.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_35 : ((q31.drop 35).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_38 : ((q31.drop 38).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_42 : ((q31.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_46 : ((q31.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_50 : ((q31.drop 50).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_54 : ((q31.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_58 : ((q31.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_63 : ((q31.drop 63).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_68 : ((q31.drop 68).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_76 : ((q31.drop 76).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_85 : ((q31.drop 85).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_94 : ((q31.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok31 : nopt 7 s31 = false := by
  have h : q31.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p31_0 (all_chunk _ _ 3 4 p31_3 (all_chunk _ _ 7 5 p31_7 (all_chunk _ _ 12 8 p31_12 (all_chunk _ _ 20 7 p31_20 (all_chunk _ _ 27 4 p31_27 (all_chunk _ _ 31 4 p31_31 (all_chunk _ _ 35 3 p31_35 (all_chunk _ _ 38 4 p31_38 (all_chunk _ _ 42 4 p31_42 (all_chunk _ _ 46 4 p31_46 (all_chunk _ _ 50 4 p31_50 (all_chunk _ _ 54 4 p31_54 (all_chunk _ _ 58 5 p31_58 (all_chunk _ _ 63 5 p31_63 (all_chunk _ _ 68 8 p31_68 (all_chunk _ _ 76 9 p31_76 (all_chunk _ _ 85 9 p31_85 (all_chunk _ _ 94 2 p31_94 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s31 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_0 : ((q32.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_3 : ((q32.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_6 : ((q32.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_8 : ((q32.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_12 : ((q32.drop 12).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_14 : ((q32.drop 14).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_15 : ((q32.drop 15).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_16 : ((q32.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_19 : ((q32.drop 19).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_22 : ((q32.drop 22).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_25 : ((q32.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_28 : ((q32.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_31 : ((q32.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_35 : ((q32.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_39 : ((q32.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_43 : ((q32.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_46 : ((q32.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_48 : ((q32.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_53 : ((q32.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_56 : ((q32.drop 56).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_57 : ((q32.drop 57).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_58 : ((q32.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_62 : ((q32.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_67 : ((q32.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_72 : ((q32.drop 72).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_78 : ((q32.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_82 : ((q32.drop 82).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_87 : ((q32.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_92 : ((q32.drop 92).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok32 : nopt 7 s32 = false := by
  have h : q32.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p32_0 (all_chunk _ _ 3 3 p32_3 (all_chunk _ _ 6 2 p32_6 (all_chunk _ _ 8 4 p32_8 (all_chunk _ _ 12 2 p32_12 (all_chunk _ _ 14 1 p32_14 (all_chunk _ _ 15 1 p32_15 (all_chunk _ _ 16 3 p32_16 (all_chunk _ _ 19 3 p32_19 (all_chunk _ _ 22 3 p32_22 (all_chunk _ _ 25 3 p32_25 (all_chunk _ _ 28 3 p32_28 (all_chunk _ _ 31 4 p32_31 (all_chunk _ _ 35 4 p32_35 (all_chunk _ _ 39 4 p32_39 (all_chunk _ _ 43 3 p32_43 (all_chunk _ _ 46 2 p32_46 (all_chunk _ _ 48 5 p32_48 (all_chunk _ _ 53 3 p32_53 (all_chunk _ _ 56 1 p32_56 (all_chunk _ _ 57 1 p32_57 (all_chunk _ _ 58 4 p32_58 (all_chunk _ _ 62 5 p32_62 (all_chunk _ _ 67 5 p32_67 (all_chunk _ _ 72 6 p32_72 (all_chunk _ _ 78 4 p32_78 (all_chunk _ _ 82 5 p32_82 (all_chunk _ _ 87 5 p32_87 (all_chunk _ _ 92 3 p32_92 (by decide +kernel))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s32 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_0 : ((q33.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_2 : ((q33.drop 2).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_6 : ((q33.drop 6).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_7 : ((q33.drop 7).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_8 : ((q33.drop 8).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_9 : ((q33.drop 9).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_14 : ((q33.drop 14).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_17 : ((q33.drop 17).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_20 : ((q33.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_23 : ((q33.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_27 : ((q33.drop 27).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_32 : ((q33.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_36 : ((q33.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_40 : ((q33.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_44 : ((q33.drop 44).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_46 : ((q33.drop 46).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_49 : ((q33.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_54 : ((q33.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_58 : ((q33.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_62 : ((q33.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_65 : ((q33.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_68 : ((q33.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_72 : ((q33.drop 72).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_77 : ((q33.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_81 : ((q33.drop 81).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_86 : ((q33.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_90 : ((q33.drop 90).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_93 : ((q33.drop 93).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_96 : ((q33.drop 96).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_101 : ((q33.drop 101).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok33 : nopt 7 s33 = false := by
  have h : q33.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p33_0 (all_chunk _ _ 2 4 p33_2 (all_chunk _ _ 6 1 p33_6 (all_chunk _ _ 7 1 p33_7 (all_chunk _ _ 8 1 p33_8 (all_chunk _ _ 9 5 p33_9 (all_chunk _ _ 14 3 p33_14 (all_chunk _ _ 17 3 p33_17 (all_chunk _ _ 20 3 p33_20 (all_chunk _ _ 23 4 p33_23 (all_chunk _ _ 27 5 p33_27 (all_chunk _ _ 32 4 p33_32 (all_chunk _ _ 36 4 p33_36 (all_chunk _ _ 40 4 p33_40 (all_chunk _ _ 44 2 p33_44 (all_chunk _ _ 46 3 p33_46 (all_chunk _ _ 49 5 p33_49 (all_chunk _ _ 54 4 p33_54 (all_chunk _ _ 58 4 p33_58 (all_chunk _ _ 62 3 p33_62 (all_chunk _ _ 65 3 p33_65 (all_chunk _ _ 68 4 p33_68 (all_chunk _ _ 72 5 p33_72 (all_chunk _ _ 77 4 p33_77 (all_chunk _ _ 81 5 p33_81 (all_chunk _ _ 86 4 p33_86 (all_chunk _ _ 90 3 p33_90 (all_chunk _ _ 93 3 p33_93 (all_chunk _ _ 96 5 p33_96 (all_chunk _ _ 101 2 p33_101 (by decide +kernel)))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s33 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_0 : ((q34.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_5 : ((q34.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_9 : ((q34.drop 9).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_12 : ((q34.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_17 : ((q34.drop 17).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_25 : ((q34.drop 25).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_32 : ((q34.drop 32).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_37 : ((q34.drop 37).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_41 : ((q34.drop 41).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_49 : ((q34.drop 49).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_56 : ((q34.drop 56).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_60 : ((q34.drop 60).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_63 : ((q34.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_67 : ((q34.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_71 : ((q34.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_75 : ((q34.drop 75).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_81 : ((q34.drop 81).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_90 : ((q34.drop 90).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok34 : nopt 7 s34 = false := by
  have h : q34.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p34_0 (all_chunk _ _ 5 4 p34_5 (all_chunk _ _ 9 3 p34_9 (all_chunk _ _ 12 5 p34_12 (all_chunk _ _ 17 8 p34_17 (all_chunk _ _ 25 7 p34_25 (all_chunk _ _ 32 5 p34_32 (all_chunk _ _ 37 4 p34_37 (all_chunk _ _ 41 8 p34_41 (all_chunk _ _ 49 7 p34_49 (all_chunk _ _ 56 4 p34_56 (all_chunk _ _ 60 3 p34_60 (all_chunk _ _ 63 4 p34_63 (all_chunk _ _ 67 4 p34_67 (all_chunk _ _ 71 4 p34_71 (all_chunk _ _ 75 6 p34_75 (all_chunk _ _ 81 9 p34_81 (all_chunk _ _ 90 6 p34_90 (by decide +kernel)))))))))))))))))))
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
theorem p35_7 : ((q35.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_10 : ((q35.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_14 : ((q35.drop 14).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_18 : ((q35.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_22 : ((q35.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_26 : ((q35.drop 26).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_29 : ((q35.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_34 : ((q35.drop 34).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_38 : ((q35.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_41 : ((q35.drop 41).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_47 : ((q35.drop 47).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_53 : ((q35.drop 53).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_60 : ((q35.drop 60).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_68 : ((q35.drop 68).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_77 : ((q35.drop 77).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_87 : ((q35.drop 87).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok35 : nopt 7 s35 = false := by
  have h : q35.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p35_0 (all_chunk _ _ 4 3 p35_4 (all_chunk _ _ 7 3 p35_7 (all_chunk _ _ 10 4 p35_10 (all_chunk _ _ 14 4 p35_14 (all_chunk _ _ 18 4 p35_18 (all_chunk _ _ 22 4 p35_22 (all_chunk _ _ 26 3 p35_26 (all_chunk _ _ 29 5 p35_29 (all_chunk _ _ 34 4 p35_34 (all_chunk _ _ 38 3 p35_38 (all_chunk _ _ 41 6 p35_41 (all_chunk _ _ 47 6 p35_47 (all_chunk _ _ 53 7 p35_53 (all_chunk _ _ 60 8 p35_60 (all_chunk _ _ 68 9 p35_68 (all_chunk _ _ 77 10 p35_77 (all_chunk _ _ 87 9 p35_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s35 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_0 : ((q36.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_3 : ((q36.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_6 : ((q36.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_8 : ((q36.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_12 : ((q36.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_15 : ((q36.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_18 : ((q36.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_21 : ((q36.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_25 : ((q36.drop 25).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_26 : ((q36.drop 26).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_27 : ((q36.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_30 : ((q36.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_33 : ((q36.drop 33).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_35 : ((q36.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_39 : ((q36.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_43 : ((q36.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_46 : ((q36.drop 46).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_48 : ((q36.drop 48).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_52 : ((q36.drop 52).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_53 : ((q36.drop 53).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_54 : ((q36.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_58 : ((q36.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_63 : ((q36.drop 63).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_68 : ((q36.drop 68).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_74 : ((q36.drop 74).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_79 : ((q36.drop 79).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_84 : ((q36.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_88 : ((q36.drop 88).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_93 : ((q36.drop 93).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok36 : nopt 7 s36 = false := by
  have h : q36.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p36_0 (all_chunk _ _ 3 3 p36_3 (all_chunk _ _ 6 2 p36_6 (all_chunk _ _ 8 4 p36_8 (all_chunk _ _ 12 3 p36_12 (all_chunk _ _ 15 3 p36_15 (all_chunk _ _ 18 3 p36_18 (all_chunk _ _ 21 4 p36_21 (all_chunk _ _ 25 1 p36_25 (all_chunk _ _ 26 1 p36_26 (all_chunk _ _ 27 3 p36_27 (all_chunk _ _ 30 3 p36_30 (all_chunk _ _ 33 2 p36_33 (all_chunk _ _ 35 4 p36_35 (all_chunk _ _ 39 4 p36_39 (all_chunk _ _ 43 3 p36_43 (all_chunk _ _ 46 2 p36_46 (all_chunk _ _ 48 4 p36_48 (all_chunk _ _ 52 1 p36_52 (all_chunk _ _ 53 1 p36_53 (all_chunk _ _ 54 4 p36_54 (all_chunk _ _ 58 5 p36_58 (all_chunk _ _ 63 5 p36_63 (all_chunk _ _ 68 6 p36_68 (all_chunk _ _ 74 5 p36_74 (all_chunk _ _ 79 5 p36_79 (all_chunk _ _ 84 4 p36_84 (all_chunk _ _ 88 5 p36_88 (all_chunk _ _ 93 2 p36_93 (by decide +kernel))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s36 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_0 : ((q37.drop 0).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_1 : ((q37.drop 1).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_2 : ((q37.drop 2).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_3 : ((q37.drop 3).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_8 : ((q37.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_11 : ((q37.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_14 : ((q37.drop 14).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_17 : ((q37.drop 17).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_22 : ((q37.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_26 : ((q37.drop 26).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_31 : ((q37.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_36 : ((q37.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_40 : ((q37.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_43 : ((q37.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_46 : ((q37.drop 46).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_51 : ((q37.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_55 : ((q37.drop 55).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_60 : ((q37.drop 60).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_65 : ((q37.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_68 : ((q37.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_72 : ((q37.drop 72).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_76 : ((q37.drop 76).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_80 : ((q37.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_84 : ((q37.drop 84).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_87 : ((q37.drop 87).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_92 : ((q37.drop 92).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_97 : ((q37.drop 97).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_102 : ((q37.drop 102).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok37 : nopt 7 s37 = false := by
  have h : q37.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 1 p37_0 (all_chunk _ _ 1 1 p37_1 (all_chunk _ _ 2 1 p37_2 (all_chunk _ _ 3 5 p37_3 (all_chunk _ _ 8 3 p37_8 (all_chunk _ _ 11 3 p37_11 (all_chunk _ _ 14 3 p37_14 (all_chunk _ _ 17 5 p37_17 (all_chunk _ _ 22 4 p37_22 (all_chunk _ _ 26 5 p37_26 (all_chunk _ _ 31 5 p37_31 (all_chunk _ _ 36 4 p37_36 (all_chunk _ _ 40 3 p37_40 (all_chunk _ _ 43 3 p37_43 (all_chunk _ _ 46 5 p37_46 (all_chunk _ _ 51 4 p37_51 (all_chunk _ _ 55 5 p37_55 (all_chunk _ _ 60 5 p37_60 (all_chunk _ _ 65 3 p37_65 (all_chunk _ _ 68 4 p37_68 (all_chunk _ _ 72 4 p37_72 (all_chunk _ _ 76 4 p37_76 (all_chunk _ _ 80 4 p37_80 (all_chunk _ _ 84 3 p37_84 (all_chunk _ _ 87 5 p37_87 (all_chunk _ _ 92 5 p37_92 (all_chunk _ _ 97 5 p37_97 (all_chunk _ _ 102 1 p37_102 (by decide +kernel)))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s37 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_0 : ((q38.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_3 : ((q38.drop 3).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_7 : ((q38.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_12 : ((q38.drop 12).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_19 : ((q38.drop 19).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_28 : ((q38.drop 28).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_34 : ((q38.drop 34).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_38 : ((q38.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_41 : ((q38.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_45 : ((q38.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_49 : ((q38.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_54 : ((q38.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_58 : ((q38.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_61 : ((q38.drop 61).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_67 : ((q38.drop 67).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_73 : ((q38.drop 73).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_82 : ((q38.drop 82).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_91 : ((q38.drop 91).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok38 : nopt 7 s38 = false := by
  have h : q38.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p38_0 (all_chunk _ _ 3 4 p38_3 (all_chunk _ _ 7 5 p38_7 (all_chunk _ _ 12 7 p38_12 (all_chunk _ _ 19 9 p38_19 (all_chunk _ _ 28 6 p38_28 (all_chunk _ _ 34 4 p38_34 (all_chunk _ _ 38 3 p38_38 (all_chunk _ _ 41 4 p38_41 (all_chunk _ _ 45 4 p38_45 (all_chunk _ _ 49 5 p38_49 (all_chunk _ _ 54 4 p38_54 (all_chunk _ _ 58 3 p38_58 (all_chunk _ _ 61 6 p38_61 (all_chunk _ _ 67 6 p38_67 (all_chunk _ _ 73 9 p38_73 (all_chunk _ _ 82 9 p38_82 (all_chunk _ _ 91 5 p38_91 (by decide +kernel)))))))))))))))))))
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
theorem p39_7 : ((q39.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_10 : ((q39.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_14 : ((q39.drop 14).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_18 : ((q39.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_21 : ((q39.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_25 : ((q39.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_29 : ((q39.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_34 : ((q39.drop 34).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_38 : ((q39.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_41 : ((q39.drop 41).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_47 : ((q39.drop 47).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_54 : ((q39.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_59 : ((q39.drop 59).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_67 : ((q39.drop 67).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_75 : ((q39.drop 75).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_85 : ((q39.drop 85).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_94 : ((q39.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok39 : nopt 7 s39 = false := by
  have h : q39.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p39_0 (all_chunk _ _ 4 3 p39_4 (all_chunk _ _ 7 3 p39_7 (all_chunk _ _ 10 4 p39_10 (all_chunk _ _ 14 4 p39_14 (all_chunk _ _ 18 3 p39_18 (all_chunk _ _ 21 4 p39_21 (all_chunk _ _ 25 4 p39_25 (all_chunk _ _ 29 5 p39_29 (all_chunk _ _ 34 4 p39_34 (all_chunk _ _ 38 3 p39_38 (all_chunk _ _ 41 6 p39_41 (all_chunk _ _ 47 7 p39_47 (all_chunk _ _ 54 5 p39_54 (all_chunk _ _ 59 8 p39_59 (all_chunk _ _ 67 8 p39_67 (all_chunk _ _ 75 10 p39_75 (all_chunk _ _ 85 9 p39_85 (all_chunk _ _ 94 2 p39_94 (by decide +kernel))))))))))))))))))))
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

def targetTable : ℕ := 4008372904 * 2 ^ 32 + 3938511360

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

def probe : Fin 500 := 250

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

def restricted : List W := inputs ++ [~~~0]
def flipped : List W := inputs ++ [0]

set_option maxRecDepth 16000 in
theorem rows_related : List.Forall₂ related restricted flipped := by
  change List.Forall₂ related (inputs ++ [~~~0]) (inputs ++ [0])
  have same (xs : List W) : List.Forall₂ related xs xs := by
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons (.inl rfl) ih
  exact List.rel_append (same inputs) (.cons (.inr (.inr rfl)) .nil)

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
    rcases List.mem_append.mp hu with h | h
    · exact .inr (.inr ⟨u, List.mem_toFinset.mpr h, .inl rfl⟩)
    · exact .inr (.inl (List.mem_singleton.mp h))
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
    ⟨.and, [2, 4]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.and, [12, 5]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.or, [15, 11]⟩], 16⟩

set_option maxRecDepth 16000 in
theorem circuitUpper : PEqualNP.MetaComplexity.Monotone2 upperCircuit ∧ upperCircuit.size = 11 ∧
    ∀ x : Fin 6 → Bool, upperCircuit.eval (List.ofFn x) = targetSix x := by
  refine ⟨?_, by decide, ?_⟩
  · simp [upperCircuit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

end PEqualNP.Outside.L_meta_39683_aux

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_39683 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3938511360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_39683_aux.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_39683_aux.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_39683_aux.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_39683_aux.six_lower_bound C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_39683_aux.upperCircuit, PEqualNP.Outside.L_meta_39683_aux.circuitUpper.1,
      ?_, PEqualNP.Outside.L_meta_39683_aux.circuitUpper.2.2⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
