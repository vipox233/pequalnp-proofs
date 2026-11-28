import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29874

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

abbrev W := BitVec 184

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 92 := ((x >>> 92) ^^^ x).setWidth 92
def cuts (ws : List W) : BitVec 92 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 92) ++ (0 : BitVec 92)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

def differs (i : Fin 92) (w : W) : Prop :=
  w.getLsbD (92+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 92) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 92+i.val < 184 := by omega
  have hi' : i.val < 184 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 92) :
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
  change (cuts ws)[j] = (BitVec.allOnes 92)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

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

def M120 : ℕ := 24519928653854221733733552434404946937899825954937634815
def M60 : ℕ := 4951760157141521099596496895
def P60 : ℕ := 4951760157141521099596496896
def gN : ℕ := 24519928653854221733733552429453186780758304855341137920

def nsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 92) x) P60

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

def fresh2 (a b w : ℕ) : Bool := !(w == a) && !(w == b)

def pair0 (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  let check w := fresh2 a b w && one0 next base pre mid post w
  orB (check (Nat.land a b)) (orB (check (Nat.lor a b))
    (orB (check (Nat.land a (Nat.sub M120 b))) (check (Nat.land b (Nat.sub M120 a)))))

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
  let check w := fresh2 a b w && oneG next extra a b sa sb base pre mid post w
  orB (check (Nat.land a b)) (orB (check (Nat.lor a b))
    (orB (check (Nat.land a (Nat.sub M120 b))) (check (Nat.land b (Nat.sub M120 a)))))

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
  ((opsN t.2.1 t.2.2.2.1).filter (fresh2 t.2.1 t.2.2.2.1)).flatMap (kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (extra : ℕ) (t : Split) : List (List ℕ) :=
  ((opsN t.2.1 t.2.2.2.1).filter (fresh2 t.2.1 t.2.2.2.1)).flatMap
    (kidsG extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.succ (Nat.succ k1)) = true then (outerS ws []).flatMap kidsPair0
  else (outerS ws []).flatMap (kidsPairG (Nat.sub (Nat.succ (Nat.succ k1)) (len ws)))

theorem brec {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

theorem frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by
  cases w <;> rfl

theorem revK_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revK xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revK (x :: xs) acc k = revK xs (x :: acc) k := rfl
    rw [e, ih]
    simp

theorem insK_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insK w l k = k (ins w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insK w (x :: xs) k =
        Bool.rec (insK w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec, ih]
    by_cases h : Nat.ble w x = true <;> simp [ins, h]

theorem call_eq (next : List ℕ → Bool) (c : List ℕ) : call next c = next c := by
  unfold call
  cases next c <;> rfl

theorem orB_eq (x y : Bool) : orB x y = (x || y) := by
  cases x <;> rfl

theorem one0_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 next base pre mid post w = (kids0 base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf
  rw [brec]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

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

theorem pair0_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 next a b sa sb base pre mid post =
      (((opsN a b).filter (fresh2 a b)).flatMap (kids0 base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.any_flatMap, List.any_filter, List.any_cons,
    List.any_nil, Bool.or_false]

theorem pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      (((opsN a b).filter (fresh2 a b)).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  unfold pairG opsN
  simp only [orB_eq, oneG_eq, List.any_flatMap, List.any_filter, List.any_cons,
    List.any_nil, Bool.or_false]

def HP (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Split) : Bool :=
  P t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

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

theorem HP_pair0 (next : List ℕ → Bool) :
    HP (pair0 next) = fun t => (kidsPair0 t).any next := by
  funext t
  simp only [HP, pair0_eq, kidsPair0]

theorem HP_pairG (next : List ℕ → Bool) (extra : ℕ) :
    HP (pairG next extra) = fun t => (kidsPairG extra t).any next := by
  funext t
  simp only [HP, pairG_eq, kidsPairG]

theorem stepF_eq (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    stepF k1 next ws = (nisGoal ws || (kidsL k1 ws).any next) := by
  have z : (0 : ℕ) = cutR [] := rfl
  unfold stepF kidsL
  rw [brec, brec, z, outerAux_eq, outerAux_eq, HP_pair0, HP_pairG]
  cases nisGoal ws
  · cases Nat.beq (len ws) (Nat.succ (Nat.succ k1)) <;> simp [List.any_flatMap]
  · simp

theorem nopt_zero (ws : List ℕ) : nopt 0 ws = nisGoal ws := rfl

theorem nopt_succ (k : ℕ) (ws : List ℕ) :
    nopt (k + 1) ws = (nisGoal ws || (kidsL k ws).any (nopt k)) := by
  rw [← stepF_eq]
  rfl

end Fast

noncomputable section Bridge

theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem negOne60 : (-1 : BitVec 92).toNat = M60 := by decide

theorem nsep_toNat (w : W) : nsep w.toNat = (sep w).toNat := by
  simp only [nsep, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

theorem ncuts_cons (w : ℕ) (ws : List ℕ) : ncuts (w :: ws) = Nat.lor (nsep w) (ncuts ws) := rfl

theorem cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

theorem ncuts_map (l : List W) : ncuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ncuts_cons, cuts_cons, BitVec.toNat_or, ih, nsep_toNat]
    rfl

theorem ncuts_append (l1 l2 : List ℕ) : ncuts (l1 ++ l2) = Nat.lor (ncuts l1) (ncuts l2) := by
  induction l1 with
  | nil =>
    have e : ncuts ([] : List ℕ) = 0 := rfl
    rw [List.nil_append, e]
    exact (Nat.zero_or _).symm
  | cons a l ih =>
    rw [List.cons_append, ncuts_cons, ih, ncuts_cons]
    exact (Nat.or_assoc _ _ _).symm

theorem cutR_eq (l : List ℕ) : cutR l = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutR (a :: l) = Nat.lor (cutR l) (nsep a) := rfl
    rw [e, ih, ncuts_cons]
    exact Nat.or_comm _ _

theorem ncuts_reverse (l : List ℕ) : ncuts l.reverse = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : ncuts [a] = nsep a ||| 0 := rfl
    have e2 : ncuts (a :: l) = nsep a ||| ncuts l := rfl
    rw [List.reverse_cons, ncuts_append, ih, e1, e2]
    change (ncuts l ||| (nsep a ||| 0)) = (nsep a ||| ncuts l)
    rw [Nat.or_zero, Nat.or_comm]

theorem baseOf_map (xs ys zs : List W) :
    baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← ncuts_map, List.map_append, List.map_append, ncuts_append, ncuts_append]
  unfold baseOf
  rw [cutR_eq, cutR_eq, ncuts_reverse, ncuts_reverse]
  exact Nat.or_assoc _ _ _

theorem opsN_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsN, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_not]
  rfl

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

theorem insW_map (w : W) (l : List W) :
    (insW w l).map BitVec.toNat = ins w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insW, ins, List.map_cons]
    split_ifs
    · rfl
    · rw [List.map_cons, ih]

theorem insW_perm (w : W) (l : List W) : (insW w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insW]
    split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem mem_innerS (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ innerS pre a (ys ++ b :: zs) mid := by
  intro ys
  induction ys with
  | nil => intro mid; simp [innerS]
  | cons y ys ih =>
    intro mid
    simp only [List.cons_append, innerS, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

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

theorem nisGoal_goal {g : W} (hg : g = goal ∨ g = ~~~goal) : nisGoal [g.toNat] = true := by
  rcases hg with rfl | rfl <;> decide +kernel

theorem mem_kids0 {base w : ℕ} {r : List ℕ} (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kids0 base r w := by
  unfold kids0
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG1 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG2 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true) :
    ins w (ins a r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG3 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true) :
    ins w (ins b r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG4 {extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    ins w (ins a (ins b r)) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsL {k : ℕ} {wsN : List ℕ} {t : Split} {w : ℕ} {c : List ℕ}
    (ht : t ∈ outerS wsN []) (hw : w ∈ opsN t.2.1 t.2.2.2.1)
    (hf : fresh2 t.2.1 t.2.2.2.1 w = true)
    (h0 : Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kidsG (Nat.sub (Nat.succ (Nat.succ k)) (len wsN)) t.2.1 t.2.2.2.1 (nsep t.2.1)
        (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ kidsL k wsN := by
  unfold kidsL
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨hw, hf⟩, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨hw, hf⟩, hG hd⟩⟩

theorem guard1 {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (nsep z.toNat) (cuts r).toNat) M60 = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← nsep_toNat, negOne60] at e
  exact beq_of_eq e

theorem guard2 {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) M60 = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat, negOne60] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change (nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) =
    (nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

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
  have fza : z.toNat ≠ a.toNat := by
    intro e
    apply hout
    rw [BitVec.eq_of_toNat_eq e, hs]
    exact Finset.mem_insert_self ..
  have fzb : z.toNat ≠ b.toNat := by
    intro e
    apply hout
    rw [BitVec.eq_of_toNat_eq e, hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  have hfresh : fresh2 a.toNat b.toNat z.toNat = true := by simp [fresh2, fza, fzb]
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
    refine mem_kidsL ht hzN hfresh ?_ ?_
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
    refine mem_kidsL ht hzN hfresh ?_ ?_
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
    refine mem_kidsL ht hzN hfresh ?_ ?_
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
    refine mem_kidsL ht hzN hfresh ?_ ?_
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


lemma ncuts_mono {s l : List ℕ} (h : s.Sublist l) : ncuts s ||| ncuts l = ncuts l := by
  induction h with
  | slnil => rfl
  | @cons s l a h ih =>
    rw [ncuts_cons]
    change ncuts s ||| (nsep a ||| ncuts l) = nsep a ||| ncuts l
    rw [← Nat.or_assoc, Nat.or_comm (ncuts s) (nsep a), Nat.or_assoc, ih]
  | @cons_cons s l a h ih =>
    simp only [ncuts_cons]
    change (nsep a ||| ncuts s) ||| (nsep a ||| ncuts l) = nsep a ||| ncuts l
    rw [Nat.or_assoc, ← Nat.or_assoc (ncuts s) (nsep a) (ncuts l),
      Nat.or_comm (ncuts s) (nsep a), Nat.or_assoc (nsep a) (ncuts s) (ncuts l),
      ← Nat.or_assoc, Nat.or_self, ih]

lemma ncuts_bound (s : List ℕ) : ncuts s < P60 := by
  induction s with
  | nil => decide
  | cons a s ih =>
    rw [ncuts_cons]
    exact Nat.or_lt_two_pow (n := 92) (Nat.mod_lt _ (by decide : 0 < P60)) ih

lemma full_or (a : ℕ) (ha : a < P60) : M60 ||| a = M60 := by
  have hm : M60 < 2^92 := by decide
  have h := Nat.or_lt_two_pow (n := 92) hm ha
  have e : BitVec.ofNat 92 (M60 ||| a) = BitVec.ofNat 92 M60 := by
    have ec : BitVec.ofNat 92 M60 = BitVec.allOnes 92 := by decide
    rw [BitVec.ofNat_or, ec, BitVec.allOnes_or]
  have en := congrArg BitVec.toNat e
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hm] using en

lemma cover_superset {s l : List ℕ} (h : s.Sublist l) (seen : ℕ)
    (hcover : seen ||| ncuts s = M60) : seen ||| ncuts l = M60 := by
  have eq : (seen ||| ncuts s) ||| ncuts l = seen ||| ncuts l := by
    rw [Nat.or_assoc, ncuts_mono h]
  rw [hcover, full_or _ (ncuts_bound l)] at eq
  exact eq.symm

def rootsAux : ℕ → ℕ → List ℕ → List (List ℕ)
  | _, seen, [] => if Nat.beq seen M60 then [[]] else []
  | k, seen, a :: rest =>
    if Nat.beq (seen ||| ncuts (a :: rest)) M60 then
      rootsAux k seen rest ++
        (if k = 0 then [] else (rootsAux (k-1) (seen ||| nsep a) rest).map (a :: ·))
    else []

lemma rootsAux_complete {s l : List ℕ} (h : s.Sublist l) (k seen : ℕ)
    (hsize : s.length ≤ k) (hcover : seen ||| ncuts s = M60) :
    s ∈ rootsAux k seen l := by
  induction h generalizing k seen with
  | slnil =>
    have e : Nat.beq seen M60 = true := beq_of_eq (by simpa [ncuts] using hcover)
    simp [rootsAux, e]
  | @cons s l a h ih =>
    have e := beq_of_eq (cover_superset (.cons a h) seen hcover)
    rw [rootsAux, if_pos e]
    exact List.mem_append_left _ (ih k seen hsize hcover)
  | @cons_cons s l a h ih =>
    have e := beq_of_eq (cover_superset (.cons_cons a h) seen hcover)
    have hlen : s.length + 1 ≤ k := hsize
    have hnext : (seen ||| nsep a) ||| ncuts s = M60 := by
      rw [Nat.or_assoc]
      exact hcover
    rw [rootsAux, if_pos e]
    apply List.mem_append_right
    rw [if_neg (by omega : k ≠ 0)]
    exact List.mem_map.mpr ⟨s, ih (k-1) (seen ||| nsep a) (by omega) hnext, rfl⟩

def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  rootsAux (n + 1) 0 insN

def allKids (m : ℕ) (insN : List ℕ) : List (List ℕ) := (rootsN (m + 1) insN).flatMap (kidsL m)

def isort (l : List ℕ) : List ℕ := l.foldr ins []

def sortK (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => frc x (fun x2 => insK x2 s k))) l k

theorem sortK_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortK l k = k (isort l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortK (x :: xs) k = sortK xs (fun s => frc x (fun x2 => insK x2 s k)) := rfl
    rw [e, ih, frc_eq, insK_eq]
    rfl

def isortW (l : List W) : List W := l.foldr insW []

theorem isortW_map (l : List W) :
    (isortW l).map BitVec.toNat = isort (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : isortW (x :: xs) = insW x (isortW xs) := rfl
    have e2 : isort (x.toNat :: xs.map BitVec.toNat) =
        ins x.toNat (isort (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insW_map, ih]

theorem isortW_perm (l : List W) : (isortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insW_perm x (isortW xs)).trans (ih.cons x)

def dead (m : ℕ) (c : List ℕ) : Bool := sortK c (fun c2 => Bool.rec true false (nopt m c2))

theorem dead_eq (m : ℕ) (c : List ℕ) : dead m c = !nopt m (isort c) := by
  unfold dead
  rw [sortK_eq, brec]
  cases nopt m (isort c) <;> rfl

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
    refine rootsAux_complete ((List.filter_sublist).map _) _ _ ?_ ?_
    · rw [List.length_map]
      exact sz
    · rw [Nat.zero_or, ncuts_map, cuts_full hg hl2, negOne60]
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

theorem all_chunk {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

end Bridge

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
  · change reachable av (BitVec.allOnes 184 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 184)
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

private def bit (k : Fin 184) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 184) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 184) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#184)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def runW (gs : List Gate) (w : List W) : List W :=
  gs.foldl (fun w g => w ++ [action w g]) w

theorem runW_length (gs : List Gate) (w : List W) :
    (runW gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runW]
  | cons g gs ih => simpa [runW, List.foldl_cons, Nat.add_assoc, Nat.add_comm] using ih (w ++ [action w g])

theorem runW_stable (gs : List Gate) (w : List W) (i : ℕ) (hi : i < w.length) :
    (runW gs w).getD i 0 = w.getD i 0 := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runW gs (w ++ [action w g])).getD i 0 = _
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem runW_bits (gs : List Gate) (w : List W) (hg : ∀ g ∈ gs, legal g) (k : Fin 184) :
    (runW gs w).map (bit k) = gs.foldl step (w.map (bit k)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runW gs (w ++ [action w g])).map (bit k) = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, action_spec w g (hg g (by simp)) k]

theorem holds_mono {av av' : Finset W} (hsub : av ⊆ av') {z : W} (h : holds av z) :
    holds av' z := by
  rcases h with h | h | ⟨a, ha, hz⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨a, hsub ha, hz⟩)

theorem holds_append (w : List W) (av : Finset W) (z : W)
    (hw : ∀ i, i ≠ 0 → holds av (w.getD i 0)) (hz : holds av z) :
    ∀ i, i ≠ 0 → holds av ((w ++ [z]).getD i 0) := by
  intro i hi
  by_cases h : i < w.length
  · rw [List.getD_append _ _ _ _ h]
    exact hw i hi
  · by_cases he : i = w.length
    · subst i
      simpa [List.getD_append_right _ _ _ _ (Nat.le_refl _)] using hz
    · have hb : w.length + 1 ≤ i := by omega
      rw [List.getD_eq_default _ _ (by simpa using hb)]
      exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach_reads (w : List W) (av : Finset W) (g : Gate) (hg : legal g)
    (hw : ∀ i ∈ g.inputs, holds av (w.getD i 0)) : reachable av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,
      List.foldr_nil,List.foldr_cons,Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inl (hw i (by simp))
    | exact .inl (holds_not (hw i (by simp)))
    | exact and_reach (hw i (by simp)) (hw j (by simp))
    | exact or_reach (hw i (by simp)) (hw j (by simp))

def price (free : ℕ → Bool) : ℕ → List Gate → ℕ
  | _, [] => 0
  | p, _ :: gs => price free (p+1) gs + if free p then 0 else 1

def emptyGate : Gate := ⟨.or, []⟩

set_option maxRecDepth 5000 in
theorem compile_free (free : ℕ → Bool) (gs : List Gate) (p out : ℕ) (w : List W) (av : Finset W)
    (hfree : ∀ v, free v ≠ true → v ≠ 6)
    (hg : ∀ g ∈ gs, legal g)
    (hout : out ≠ 0)
    (hw : ∀ i, i ≠ 0 → holds av (w.getD i 0))
    (hr : ∀ j < gs.length, p+j ≠ 6 → 0 ∉ (gs.getD j emptyGate).inputs)
    (hf : ∀ j < gs.length, free (p+j) = true →
      holds av (action (runW (gs.take j) w) (gs.getD j emptyGate)))
    (he : (runW gs w).getD out 0 = ~~~goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (price free p gs) av := by
  induction gs generalizing p w av with
  | nil =>
    have h := he ▸ hw out hout
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have tailLegal : ∀ a ∈ gs, legal a := fun a ha => hg a (by simp [ha])
    have tailRead : ∀ j < gs.length, p+1+j ≠ 6 → 0 ∉ (gs.getD j emptyGate).inputs := by
      intro j hj hp
      simpa [Nat.add_assoc] using hr (j+1) (by simp; omega) (by omega)
    have tailFree : ∀ j < gs.length, free (p+1+j) = true →
        holds av (action (runW (gs.take j) (w ++ [z])) (gs.getD j emptyGate)) := by
      intro j hj hp
      simpa [List.take_succ_cons, runW, z, Nat.add_assoc] using
        hf (j+1) (by simp; omega) (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hp)
    have tailEval : (runW gs (w ++ [z])).getD out 0 = ~~~goal := he
    have cont (A : Finset W) (sub : av ⊆ A) (new : holds A z) :=
      ih (p+1) (w ++ [z]) A tailLegal
        (holds_append w A z (fun i hi => holds_mono sub (hw i hi)) new) tailRead
        (fun j hj hp => holds_mono sub (tailFree j hj hp)) tailEval
    by_cases hp : free p = true
    · have hz : holds av z := by
        simpa [runW] using hf 0 (by simp) (by simpa using hp)
      simpa [price, hp] using cont av (fun _ h => h) hz
    · have nr : 0 ∉ g.inputs := by
        have hne : p ≠ 6 := hfree p hp
        simpa using hr 0 (by simp) (by simpa using hne)
      have reach := gate_reach_reads w av g (hg g (by simp)) (fun i hi =>
        hw i (fun eq => nr (eq ▸ hi)))
      rw [price, ite_eq_right hp]
      rcases reach with old | ⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av (fun _ h => h) old
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (Finset.subset_insert _ _) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


def primary : List W := [
  2697001295985832427867453296985210735966616007,
  723970772699681184295575324801352220208828476220999773,
  11493738479040940202955932547368578044781571263634150392,
  5962972329935505299752146891689958624288970776247968,
  12253978016220603658653699315333137953184481382709994496,
  45671925996449532737192591142555456639196463104,
  12259964281255184700276060025813202520833789888311607554]

def sensitiveRows : W := 820523787952633833819114252485908743108226847900434432

def witnessRows : W := 12259964326949498895822950748064680171923250793870263328

def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def row (k : Fin 184) (i : Fin 7) : Bool := bit k (primary.getD i.val 0)

def mark (x : Fin 7 → Bool) (i : Fin 7) : Bool := if i = 0 then true else x i

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma sample_target : ∀ k : Fin 184, target (row k) = bit k (~~~goal) := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma sample_sensitive : ∀ k : Fin 184, bit k sensitiveRows = true →
    target (row k) = false ∧ target (mark (row k)) = true := by
  decide +kernel

def witnessInput (r : Fin 16) (i : Fin 7) : Bool :=
  if 2 ≤ i.val ∧ i.val ≤ 5 then r.val.testBit (i.val - 2) else false

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma witness_exhaustive : ∀ x : Fin 7 → Bool, x 0 = false → x 1 = false → x 6 = false →
    ∃ r : Fin 16, witnessInput r = x := by
  decide +kernel

def witnessIndex (r : Fin 16) : Fin 184 :=
  ([183, 96, 101, 5, 110, 120, 10, 29, 127, 136, 144, 45, 19, 30, 53, 91] : List (Fin 184)).getD r.val 0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma sample_witness : ∀ r : Fin 16,
    bit (witnessIndex r) witnessRows = true ∧ row (witnessIndex r) = witnessInput r := by
  decide +kernel


def initialN : List ℕ := 0 :: (primary.drop 1).map BitVec.toNat

def rawGateValues (ws : List ℕ) : List ℕ :=
  0 :: M120 :: (ws ++ (ws.map fun a => M120 - a) ++
    (ws.flatMap fun a => ws.flatMap fun b => [Nat.land a b, Nat.lor a b]))

def gateValues (ws : List ℕ) : List ℕ := (rawGateValues ws).dedup

def goodMask (u : ℕ) : Bool :=
  ((u &&& sensitiveRows.toNat) == 0) && !((u &&& witnessRows.toNat) == 0)

def canonicalN (u : ℕ) : ℕ := min u (M120 - u)

def canonical (u : W) : W := BitVec.ofNat 184 (canonicalN u.toNat)

def pairKey (u a b : ℕ) : ℕ × ℕ × ℕ :=
  let a' := canonicalN a
  let b' := canonicalN b
  (u, min a' b', max a' b')

def shortBuckets : List (List ℕ) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [3094850098213450692079648768],
  [],
  [3095011840495569810025943712],
  [3796027076050101990859472896],
  [3136274699460148616508089344],
  [],
  [],
  [],
  [3713820117857337103012069376],
  [2475880081029725946342539264],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [22213632912598866608711574646499002764230656],
  [2475880079800841382395904000],
  [],
  [],
  [],
  []]

def longBuckets : List (List (ℕ × ℕ × ℕ)) := [
  [(660394618430422670165550080, 45671925996449532737192591142555456639196463104, 12253978016220603658653699311537110877134379391850521600), (3136436441742267734454384288, 718357284780885403601626415480076183567915972432167000, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 723970772699681184295575324801352220208828476220999773, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 11493738524690652566492866417952457612690528900066382840, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964281255184870415945414543680626644887919562482946), (3423839663430748947995497120, 718357284780885403601626415479924402604454719448547328, 724320257110820908901378562332626501240328890059587232), (3423840327513836867725366008, 3136274699460148616508089344, 724321535924835241209493075209209072142546598398263037), (3796631691145556709643649024, 723970729882168734101430747414256912657316433130160128, 12259591461321886990399654893315829096390509625333392384), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964281255184870415945414543680626644887919562482946), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259962911097312760409825833328974313578154875879948280), (22213632912598866691560943160600929436172288, 1320791768985116173695713280, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 723970729882168734101430747414256913810539206372556888, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12253999938767377255110073689573720796696133639558084600, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 45649625421392185573200137633743093395842138112, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 11493738524690652566492866417952457612690528900066382840), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12217709251740621387251507871840950661091759348901977085), (12259964329781524583263347831204649109514524023535187616, 3796027076050101990859472896, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 3094850098213450692079648768, 3095011840495569810025943712), (3095011839265488977428217856, 5962926680310083906271037254641402222192955438294016, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 718357284780885403601626415479924402604454719448547328, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12253978061892529655103232048729702019689836031046984704, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960), (22213632912598866690918532839263890611634176, 5962972352236080357099310884143467436652214130572960, 12253999938767377255110073689573720796696133639558084600), (22213632912598866937691177391916622924546136, 0, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 5612209104781448385834396483833106690570848598984704, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 11493716556494166606499558173127995201269919006786060288), (2854413547502675280134804977542466972917694464, 350763225154056913917750407856851933718122177263264, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 5962972329935505299752146891689958624288970776247968, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 12259964281255184700276060025813202520833789888311607554, 12259964324072697150470204603200297828385301931402447199)],
  [(3095001215093824025333399552, 5612209104781448385834399581119946162304664941865984, 12259591504139399439347648224654565770788855139482446941), (3136436441742267734454384288, 1320791768985116173695713280, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259613426686173035804022598894996833337046143346917373), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259940988550539163953451459088553212348621736978153120), (3796671850016043105776041984, 328979603898640390953173080, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 45671925996449532737192591142555456639196463104, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259591504139399439347648224654565770788855139482446941), (22213632912598866937691177391916622924546136, 42817512448946857457057786165012989666278768640, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259591506993812986850323501070714927042403796116286557), (22213632912598867227843335341227430394270368, 45649625421392185573200137633743093395842138112, 5962972352236080357099310884143467436652214130572960), (22213801724556786128122975153446818488062712, 5962972352236080357099310884143467436652214130572960, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 42817512450194144577387095307551512043090839645, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11499701451370875708255684691165256162910290424384454648)],
  [(2475880081029725951243985920, 3136274699460148616508089344, 12259964281255184700276060025813202520833789888311607554), (2553251333485066611704463360, 45649707089160246598508740243678481574480838656, 724321535924835241209493075209209072142546598398263037), (3095011839265488977428217856, 3095011840495569810025943712, 12259964281255184870415945414543680626644887919562482946), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964324072697150470204603200297828385301931402447199), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964324072697319363938745882417301043233433711537503), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964324072697150470204603200297828385301931402447199), (168811955467160195937355453490998018048, 170139885388730478105811098031250875392, 12259964281255184700276060025813202520833789888311607554), (22213632912598866690918532839263890611634176, 22213632912598866608711574646499002764230656, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 11499701451370875708255684691165256162910290424384454648, 12253999938767377255110073689573720796696133639558084600), (22213632912598867227843335341227430394270368, 0, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5612209104781448385834396483833106690570848598984704, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962926680310083906271036098910843417982113052377088, 5962972352236080357099310884143467436652214130572960)],
  [(3423840327513836867725366008, 718357284780885403601626415479924402604454719448547328, 724321535924835241209493075209209072142546598398263037), (3796027077203324761652330496, 328979603898640390953173080, 12253978016220603658653699315333289734147942635693614168), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 11499701451370962650400432991024878176876996047370452984), (22213632912598866691560943160600929436172288, 5962972352236080357099310884143467436652214130572960, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 42817512448946857457057786165012989666278768640, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 11493738479040940202955932547368578044781571263634150392), (22213801724556786128122975153446818488062712, 22213632912598866608711574646499002764230656, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 11499701451370875708255684691165256162910290424384454648, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 12259964281255184870415945414543680626644887919562482946, 12259964324072697150470204603200297828385301931402447199)],
  [(3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259962911097312760409825833328974313578154875879948280), (3423840327513836867725366008, 328979603898640390953173080, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 45671925996449532737192591142555456639196463104, 724321535924835241209493075209209072142546598398263037), (3791191372618520777587687424, 12212073841275052010101184588279091780939194588265054208, 12217709251740621387251507871840950661091759348901977085), (3796027073591131886892089344, 3796027076050101990859472896, 12259964281277398502000616811941325495987236706799670266), (3796027076048901005121683456, 45649625421392185574520287155968608504700207104, 12259964326904810121669541137926131158265611854893547426), (4456421694479323675287233536, 1320791768985116173695713280, 5962972329935505299752148211839480849804079634316960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 724321535924835241209493075209209072142546598398263037), (22213632912598866937691177391916622924546136, 328979603898640390953173080, 22213632912598866608711574646499002764230656), (22213632912598866937691177391916622924546136, 5962926680310083906271034778761321192467004194308096, 723970775554094731798250604936157197751295449138694237), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 11493738479018726401231375761240455069628124445146087680), (22213632912598867269106195535887069474071552, 3136274699460148616508089344, 22213632912598866608711574646499002764230656), (22218907289286138683850898876975064715624448, 724321535924835241209493075209209072142546598398263037, 724321535924835241209493075209209072142546598398263037), (2832194640213389141450954078665491908202070016, 2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773)],
  [(2476522327789327011180183552, 5962926680310083906271037254641402222192955438294016, 12259964281255184870415945414543680626644887919562482946), (3136436441742267734454384288, 5962972352236080357099310884143467436652214130572960, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037), (3713822480271855629419675648, 22213632912598866608711574646499002764230656, 12259964326904810121669541137926131158265611854893547426), (3796671850016043105776041984, 1320791768985116173695713280, 12253978016220603658653699315333782727150422497626563584), (22213632912598866690918532839263890611634176, 22213632912598866608711574646499002764230656, 12253978016242817291566298178228029409973643282462155776), (22213632912598866691560943160600929436172288, 22213632912598866608711574646499002764230656, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 11499701451370875708255684691165256162910290424384454648, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964326927023923394097921578374053618217286153797626), (22213632912598866937691177391916622924546136, 718357284780885403601626419198580223893373035732402176, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12217709254572821301841584285367044065140950089848298493), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259940988550539163953451459088553212348621736978153120), (2854413547502675280212780845093257958883065856, 42817512450194144577387095307551512043090839645, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 5962972329935505299752146891689958624288970776247968, 12259964324072697150470204603200297828385301931402447199)],
  [(3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259591504139399439347648224654565770788855139482446941), (3796671850016043105776041984, 11493738479018726401231375761240455069628124445146087680, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 3136274699460148616508089344, 45671925996449532737852985760985879309362013184), (4456421694480524661025022976, 5612209104863116153895421792435716625959027237685248, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259591504139399439347648224654565770788855139482446941), (22213632912598862894891456789161899752161280, 45671925996449532733396564066505354648336990208, 12253978016220603658653699315333137953184481382709994496), (22213632912598866690918532839263890611634176, 724321535924835241209493075209209072142546598398263037, 12253999938767377255110073689573720796696133639558084600), (22213632912598866937691177391916622924546136, 3796027076050101990859472896, 723970775554094731798250604936157197751295449138694237), (22213632912598867227843335341227430394270368, 5962926680310083906271034778761321192467004194308096, 5962972352236080357099310884143467436652214130572960), (22213801724556786128122975153446818488062712, 11535993551373015966174629278398945608176473455181447426, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554, 12259964326904810121669541137926131158265611854893547426), (12259964329781524583263347831204649109514524023535187616, 12259591504139399439347648224654565770788855139482446941, 12259964324072697150470204603200297828385301931402447199)],
  [(2514867938712297737294053376, 718357284780885403601626419198580223893373035732402176, 723970775554094731798250604936157197751295449138694237), (3136436441742267734454384288, 22213632912598866608711574646499002764230656, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 11499701451370875708255684691165256162910290424384454648, 12253999938767377255110073689573720796696133639558084600), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12217709251740621387251507871840950661091759348901977085), (22213632912598866690918532839263890611634176, 3796027076050101990859472896, 11493738479040940202955932547450785002974336151481553912), (22213632912598866690918532839263890611634176, 22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600), (22213632912598866937691177391916622924546136, 22213632912598866608711574646499002764230656, 723970772721894817208174191410063793702104708192372829), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 11499701451370875708255684691165256162910290424384454648), (22213801724556786128122975153446818488062712, 724321535924835241209493075209209072142546598398263037, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554, 12259964326927110696725592761685001894404130353812357378), (2854413547502675280134804977542466972917694464, 3095011840495569810025943712, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12253978016220603488513813926602659847373383351459119104)],
  [(3796671850016043105776041984, 3796027076050101990859472896, 12259964281255184700276060028289082601864716820391936258), (3796671850016043105776041984, 3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 723970772699681184295575324801352220208828476220999773, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 11493738524690652566492866417952457612690528900066382840, 12259964281255184870415945414543680626644887919562482946), (4457066468445264790203802624, 1320791768985116173695713280, 3136274699460148616508089344), (22213632912598867227843335341227430394270368, 3796027076050101990859472896, 5962972352236080357099310884143467436652214130572960), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11535993551373015966174629278398945608176473455181447426), (12259964329781524414369613688522529636856592521226097312, 12259964281255184870415945414543680626644887919562482946, 12259964324072697319363938745882417301043233433711537503)],
  [(3097286839471733816342881280, 350763225154056913917750407856851933718122177263264, 723970772699681184295575324801352220208828476220999773), (3791191372618520777587687424, 42839726081859456323666497738506265898250141696, 12217709251740621387251507871840950661091759348901977085), (4456421694480524661025022976, 45649625421392185573200137633743093395842138112, 5962972352236080357099310884143467436652214130572960), (22213632912598866690918532839263890611634176, 11493738479040940202955932547368578044781571263634150392, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 724321535924835241209493075209209072142546598398263037, 12259964281277398502000616811941325495987236706799670266), (22213801724556787366065375624461065511834360, 12259964281255184700276060024492410751848673714615894274, 12259964281255184700276060025813202520833789888311607554)],
  [(3094850100672416088623939584, 3136274699460148616508089344, 11493738524690652566492866417952457612690528900066382840), (3094850100672416088623939584, 11493716556494166606499558173210202159462683894633463808, 11493738524690652566492866417952457612690528900066382840), (3136425816340521949761840128, 328979603898640390953173080, 12253978016220603658653699315333289734147942635693614168), (3423840327513836867725366008, 3095011840495569810025943712, 723970772699681184295575327896212943824024952993192701), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964281277398502000616811941325495987236706799670266), (3796671850016043105776041984, 1320791768985116173695713280, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12253999938767377255110073689573720796696133639558084600, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 0, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5612209104781448385834396483833106690570848598984704, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962926680310083906271036098910843417982113052377088, 5962972352236080357099310884143467436652214130572960), (22213632912598866691560945619571033403555840, 12259964281255184870415945414543680626644887919562482946, 12259964281277398503328546733511607664442881247052527610), (22213801724556786128122975153446818488062712, 11493738479040940202955932547368578044781571263634150392, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970729882168734101430747414256912657316433130160128, 723970772699681184295575324801352220208828476220999773)],
  [(41424601246697924428440576, 3136274699460148616508089344, 11493738479040940202955932547368578044781571263634150392), (3094850099443531524677304320, 45649625421392185573860532252173516066007688192, 12253978061892529655103232048729702019689836031046984704), (3095654087255170874863588000, 1320791768985116173695713280, 11493738479040940202955932547451427413295673190306092024), (3136436441742267734454384288, 724321535924835241209493075209209072142546598398263037, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 723970772699681184295575324801352220208828476220999773, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12218060014965775444165425619153946789410280994307047421), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964281255184700276060025813202520833789888311607554), (4456421694480524661025022976, 42817512448946857457057786165012989666278768640, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 11493738479040940202955932547368578044781571263634150392), (22213632912598866608862690373950831411134464, 5612209104781448385834396483833106690570848598984704, 5612211959276663656570701927240694168426000155379712), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964326927110865537550682442355695382092416559961082), (2854413547502675280134804977542466972917694464, 3136274699460148616508089344, 723970772699681184295575324801352220208828476220999773), (12259964329781524414369613688522529636856592521226097312, 12259591504139399439347648224654565770788855139482446941, 12259964324072697319363938745882417301043233433711537503), (12259964329781524583263347831204649109514524023535187616, 11493716556494166606499558173127995201269919006786060288, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 3713820117857337103012069376, 3796027076050101990859472896), (2476031195528293211042807808, 5612211936976088599223537934787185356062756801054720, 723970775554094731798250604936157197751295449138694237), (3136436441742267734454384288, 22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600), (3796027073591131886892089344, 12253978016220603657325769393762855784728836842457137152, 12259964281277398502000616811941325495987236706799670266), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964326904810291809426524180729183046983934900436898), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 11493738479018726401231375761240455069628124445146087680), (22213632912598866691560943160600929436172288, 11493738479040940202955932547368578044781571263634150392, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 5962972329935505299752146891689958624288970776247968, 723970775554094731798250604936157197751295449138694237), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 724321535947054148498779213893059971019521663113887485), (22213801724556786128122975153446818488062712, 45671925996449532735871799373570340465500749824, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11535620731439718255052072899853213550580026663261447168), (12259964329781524583263347831204649109514524023535187616, 3095011840495569810025943712, 12259964324072697150470204603200297828385301931402447199)],
  [(161742282119117946294944, 5962972329935505299752143755415259164140354268158624, 12253978016220603658653699315333137953184481382709994496), (2553251333485066611704463360, 3796027076050101990859472896, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 1320791768985116173695713280, 724321535924835241209493075209209072142546598398263037), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12253978016220603488513813926602659847373383351459119104), (22213801724556786128122975153446818488062712, 11493738479018726401231375761240455069628124445146087680, 11493738479018726401231375761240455069628124445146087680), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11493738479040940202955932547039598440882930872680977312), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964324072697150470204603200297828385301931402447199)],
  [(2476031195528293211042807808, 22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237), (3133837958201865492244856832, 5612209104781448385834399578693830305767325371177632, 12217709251740621387251507871840950661091759348901977085), (3136436441742267734454384288, 11493738479040940202955932547368578044781571263634150392, 12253999938767377255110073689573720796696133639558084600), (3713820120316302499556360192, 11493716556494166606499558173169419802516616931214500864, 11499701451370875708255684691165256162910290424384454648), (3796671847557073001808658432, 11493716556494166606499558173127995201269919006786060288, 12259964281255184869088015492973398458189243379309625602), (3796671850016043105776041984, 5962972352236080357099310884143467436652214130572960, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 5962926680310083906271034778761321192467004194308096, 5962972352236080357099310884143467436652214130572960), (22213632912598865370769174175484755740459008, 22213632912598866608711574646499002764230656, 12259964281255184700276060025813202520833789888311607554), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 5962972329935505299752146891689958624288970776247968, 5962972352236080357099310884143467436652214130572960), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12253978016220603658653699315333137953184481382709994496)],
  [(3136274697001183219894190080, 12253978016220603657325769393762855784728836842457137152, 12259964281277398502000616811941325495987236706799670266), (3796027076048901005121683456, 3796027076050101990859472896, 12259964326904810121669541137926131158265611854893547426), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964281277398503328546733511607664442881247052527610), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964326904810121669541137926131158265611854893547426), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 11499701451370875708255684691165256162910290424384454648), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12259940988550539163953451459088553212348621736978153120, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 718357284780885403601626415479924402604454719448547328, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 723970729882168734101430747414256912657316433130160128, 12259964324072697150470204603200297828385301931402447199)],
  [(3718655821288918316283854848, 723970772699681184295575324801352220208828476220999773, 11535620731439718255052072899853213550580026663261447168), (3796671850016043105776041984, 22213632912598866608711574646499002764230656, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 11499701451370875708255684691165256162910290424384454648, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964326927110696725592761685001894404130353812357378), (4456421694480524661025022976, 3796027076050101990859472896, 5962972352236080357099310884143467436652214130572960), (168811955467160195937355453490998018048, 22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554), (22213632912598862894891456789161899752161280, 21922546773596456374374240582843511652256848090104, 12253978016220603658653699315333137953184481382709994496), (22213632912598866690918532839263890611634176, 12217709251740621387251507871840950661091759348901977085, 12253999938767377255110073689573720796696133639558084600), (2854413547502675280134804977542466972917694464, 328979603898640390953173080, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 45671925996449532737192591142555456639196463104, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 3136274699460148616508089344, 12259964324072697150470204603200297828385301931402447199)],
  [(619131760694728427630039712, 3095011840495569810025943712, 45671925996449532737192591142555456639196463104), (2475880078570760549798248448, 3713820117857337103012069376, 22213632912598866608711574646499002764230656), (3423840327513836867725366008, 5962972352236080357099310884143467436652214130572960, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12253978061892529655103232048729702019689836031046984704), (168811955467160195937355453490998018048, 11493716556494166606499558173127995201269919006786060288, 12259964281255184700276060025813202520833789888311607554), (22213632912598866691560943160600929436172288, 12259940988550539163953451459088553212348621736978153120, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259940988572839739010798621760859726140608935815544480), (22213801724556786128122975153446818488062712, 12217709251740621387251507871840950661091759348901977085, 12259964281255184700276060025813202520833789888311607554), (2832194640213548865426545056331972765817255584, 12259964324072697150470204603200297828385301931402447199, 12259964324072697150470204603200297828385301931402447199), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259964326904810121669541137926131158265611854893547426), (12259964326927111035760672552312660033406382238347835040, 12259964324072697150470204603200297828385301931402447199, 12259964326927110697972879882092286904493443716589799775), (12259964329759310781538791045076526135514299978289521664, 12259964324072697150470204603200297828385301931402447199, 12259964324094910952194761389328420802385525976648113151), (12259964329781524583263347831204649109514524023535187616, 12259964281277398502000616811941325495987236706799670266, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 3094850098213450692079648768, 11493716556494166606499558173127995201269919006786060288), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964281255184870415945414543680626644887919562482946), (3713822480271855629419675648, 45649625421392185574520287155968608504700207104, 12259964326904810121669541137926131158265611854893547426), (3796671850016043105776041984, 11493738479018726570043331228400651006983577936144105728, 12259964281255184870415945414543680626644887919562482946), (4332954240966584057049715360, 1320791768985116173695713280, 5962972329935505299752148211839480849804079634316960), (22213632912598864132831494845657620368326656, 22300575057347163992453508812363243354324992, 5962972329935505299752146891689958624288970776247968), (2854413547502675276416149156253548656633839616, 12259591504139399439347648224654565770788855139482446941, 12259591504139399439347648224654565770788855139482446941), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259964326927110696725592761685001894404130353812357378), (12259964329781524414369613688522529636856592521226097312, 12259964324072697150470204603200297828385301931402447199, 12259964324072697319363938745882417301043233433711537503), (12259964329781524583263347831204649109514524023535187616, 723970772699681184295575324801352220208828476220999773, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964326904891790683753468626842884717274697219702783)],
  [(1320146995020376044516933632, 5962972329935505299752146891689958624288970776247968, 12253978016220603658653699312196863253724332766201905152), (3423840327513836867725366008, 22213632912598866608711574646499002764230656, 724321535924835241209493075209209072142546598398263037), (3713820120316302499556360192, 3796027076050101990859472896, 11499701451370875708255684691165256162910290424384454648), (3718655821288918316283854848, 2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773), (4332790137500027245293469696, 4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960), (22213632912598866690918532839263890611634176, 45649625421392185573200137633743093395842138112, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 12217709251740621387251507871840950661091759348901977085, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 3095011840495569810025943712, 723970775554094731798250604936157197751295449138694237), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 723970729882168734101430747414256912657316433130160128), (2854413547502675280134804977542466972917694464, 2854413547502675280134804977542466972917694464, 45671925996449532737192591142555456639196463104), (12259964329781524583263347831204649109514524023535187616, 42817512448946857458300602066447314854009110528, 12259964324072697150470204603200297828385301931402447199)],
  [(3097286839471733816342881280, 3136274699460148616508089344, 723970772699681184295575324801352220208828476220999773), (3423840327513836867725366008, 328979603898640390953173080, 3095011840495569810025943712), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12253999938767377255110073689573720796696133639558084600), (3713820120316302499556360192, 45671839054304784437332969128588751016210464768, 11499701451370875708255684691165256162910290424384454648), (3796671850016043105776041984, 724321535924835241209493075209209072142546598398263037, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 724321535947054148498779213893059971019521663113887485), (22213632912598866686082829407682677339848704, 718357284780885403601626415479924402604454719448547328, 12212095763821825606557558962519674624450846845113144312), (22213632912598866690918532839263890611634176, 0, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 5612209104781448385834396483833106690570848598984704, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 1320791768985116173695713280, 11493738479040940202955932547451427413295673190306092024), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12253978016220603658653699315333137953184481382709994496), (22213801724556786128122975153446818488062712, 45649625421392185573200137633743093395842138112, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804978695689743710552064, 723970772699681184295575324472372616310188085267826693, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 718357284780885403601626415479924402604454719448547328, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 12253978061892529655103232048729702019689836031046984704, 12259964324072697150470204603200297828385301931402447199)],
  [(82206958192764887847403520, 45649712363536933870583879567908957636432232448, 11493738479040940202955932547368578044781571263634150392), (660394618430422670165550080, 3136274699460148616508089344, 45671925996449532737192591142555456639196463104), (3097286839471733816342881280, 723970772699681184295575324801352220208828476220999773, 11535620731439718255052072899853213550580026663261447168), (3136436440512186901856658432, 11493738479018726401231375761240455069628124445146087680, 12253999938745163622197472370605793758898140312068039936), (3136436441742267734454384288, 12217709251740621387251507871840950661091759348901977085, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964324072697150470204603200297828385301931402447199), (3713822480271855629419675648, 11493738479018726401231375763716335149428965832373900192, 12259964326904810121669541137926131158265611854893547426), (3796671850016043105776041984, 1320791768985116173695713280, 3796027076050101990859472896), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12253978016220603488513813926602659847373383351459119104), (22213632912598866690918532839263890611634176, 42817512448946857457057786165012989666278768640, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 723970775554094731798250604936157197751295449138694237, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 22213632912598866608711574646499002764230656, 12259964281277398333188658891183971695009274644052066562), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12253978061892529655103232048729702019689836031046984704), (22213632912598867227843335341227430394270368, 3095011840495569810025943712, 5962972352236080357099310884143467436652214130572960), (22213801724556786128122975153446818488062712, 0, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 5612209104781448385834396483833106690570848598984704, 12259964281255184700276060025813202520833789888311607554), (12259964326949329943049798965778104053182551257717932032, 12259964326904810121669541137926131158265611854893547426, 12259964326904891790683753468626842884717274697219702783), (12259964329759310781538791045076526135514299978289521664, 12259964281277398502000616811941325495987236706799670266, 12259964324094910952194761389328420802385525976648113151), (12259964329781524583263347831204649109514524023535187616, 328979603898640390953173080, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 45671925996449532737192591142555456639196463104, 12259964324072697150470204603200297828385301931402447199)],
  [(1320146995020376044516933632, 3796027076050101990859472896, 5962972329935505299752146891689958624288970776247968), (3136436441742267734454384288, 3095011840495569810025943712, 12253978016220603658653699315333299695466600500656289440), (3835014933732673781810987008, 5612209104781448385834396483833106690570848598984704, 5612211959276663656570701927240694168426000155379712), (4415158837974911251087168160, 3095011840495569810025943712, 3796027076050101990859472896), (4456421694480524661025022976, 5962972329935505299752146891689958624288970776247968, 5962972352236080357099310884143467436652214130572960), (168811957920757353800977962062747603704, 12259964326927110696725592761685001894404130353812357378, 12259964326927110696725592761685001894404130353812357378), (22213632912598866690918532839263890611634176, 3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253978016220603488513813926602659847373383351459119104, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 45649625421392185573200137633743093395842138112, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964324094910952194761389328420802385525976648113151), (22213632912598866937691177391916622924546136, 328979603898640390953173080, 45671925996449532737521570745300874259356778584), (22213632912598866937691177391916622924546136, 723970729882168734101430747414256912657316433130160128, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964281255184870415945414543680626644887919562482946), (22213801724556786128122975153446818488062712, 42817512448946857457057786165012989666278768640, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 723970775554094731798250604936157197751295449138694237, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970729882168735348717867743566055195838809942231133, 723970772699681184295575324801352220208828476220999773)],
  [(82206958192764887847403520, 760261459726437052154141142205142751914562375923934208, 11493738479040940202955932547368578044781571263634150392), (2476522327789327011180183552, 3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 724321535924835241209493075209209072142546598398263037), (3796671850016043105776041984, 11493738479040940202955932547368578044781571263634150392, 12259964281255184870415945414543680626644887919562482946), (22213632912598865370769174175484755740459008, 45671925996449532735871799373570340465500749824, 12259964281255184700276060025813202520833789888311607554), (22213632912598866691560943160600929436172288, 0, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 1320791768985116173695713280, 22213632912598866608711574646499002764230656), (22213632912598866691560943160600929436172288, 5612209104781448385834396483833106690570848598984704, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 3136274699460148616508089344, 723970775554094731798250604936157197751295449138694237), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964326904810121669541137926131158265611854893547426), (22213801724556786128122975153446818488062712, 12253978016220603488513813926602659847373383351459119104, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 718358563594899735909740928317519113518257627622015069, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11493738524690652566492866417952457612690528900066382840)],
  [(3136274697001183219894190080, 3136274699460148616508089344, 12259964281277398502000616811941325495987236706799670266), (3136436441742267734454384288, 45649625421392185573200137633743093395842138112, 12253999938767377255110073689573720796696133639558084600), (3796027073591131886892089344, 22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266), (3796027076048901005121683456, 12253978016220603488513813929078539928403109302703105024, 12259964326904810121669541137926131158265611854893547426), (22213632912598866690918532839263890611634176, 5962926680310083906271034778761321192467004194308096, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 42817512448946857457057786165012989666278768640, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 723970775554094731798250604936157197751295449138694237, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560945619571033403555840, 12259964281277398502000616811941325495987236706799670266, 12259964281277398503328546733511607664442881247052527610), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12253999938767377255110073689573720796696133639558084600), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964326927110696725592761685001894404130353812357378), (22213801724556786128122975153446818488062712, 170139885388730478105811098031250875392, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12254001354574874616369788991034441199641322884117299458, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11493716556494166606499558173127995201269919006786060288)],
  [(2476522326560442447233548288, 22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266), (2514867938712297737294053376, 3136274699460148616508089344, 723970775554094731798250604936157197751295449138694237), (3136436441742267734454384288, 0, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 5612209104781448385834396483833106690570848598984704, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259591504139399439347648224654565770788855139482446941), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259940988572839739010798621760859726140608935815544480), (22213632912598864132831494845657620368326656, 5962972329935505299752146891689958624288970776247968, 11493738479040940202955932544273566204286001453608206680), (22213632912598866690918532839263890611634176, 12253978016220603658653699315333137953184481382709994496, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 12253978016220603488513813926602659847373383351459119104, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964324072697150470204603200297828385301931402447199), (22213632912598867227843335341227430394270368, 3136274699460148616508089344, 5962972352236080357099310884143467436652214130572960), (22213801724556786128122975153446818488062712, 5962926680310083906271034778761321192467004194308096, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 1320791768985116173695713280, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 723970775554094731798250604936157197751295449138694237)],
  [(2475880081030926932080328704, 45671925996449532735871799373570340465500749824, 12259964281255184700276060025813202520833789888311607554), (3136436441742267734454384288, 42817512448946857457057786165012989666278768640, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 723970775554094731798250604936157197751295449138694237, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12217709251740621387251507871840950661091759348901977085), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964326904891790683753468626842884717274697219702783), (3713820119087417935609724928, 45649625421392185574520284628763469440359071744, 12259940988550539163953451459088553212348621736978153120), (3796029437235735962984120320, 11493738479018726401231375761240455069628124445146087680, 12253999938745163622197472370605793758898140312068039936), (3796671850016043105776041984, 723970729882168735347581993462615545810482962071945216, 12259964281255184870415945414543680626644887919562482946), (22213632912598866690918532839263890611634176, 3796027076050101990859472896, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964281277398503328546733511607664442881247052527610), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964326904810121669541137926131158265611854893547426), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964281277398503328546733511607664442881247052527610), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964326904810121669541137926131158265611854893547426), (22213801724556786128122975153446818488062712, 5986265034581211762246099210542673460406536852488450, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12253978016220603658653699315333137953184481382709994496, 12259964281255184700276060025813202520833789888311607554), (12259964326949329943049798965778104053182551257717932032, 12259964324072697150470204603200297828385301931402447199, 12259964326904891790683753468626842884717274697219702783), (12259964329781524583263347831204649109514524023535187616, 11493738479018726401231375761240455069628124445146087680, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 12253978016220603489759965172651018480526549880400904192, 12259964324072697150470204603200297828385301931402447199)],
  [(2553251333485066611704463360, 718357284780885403601626418577211242076188535791428608, 724321535924835241209493075209209072142546598398263037), (3094850099443531524677304320, 11493716556516380239412157036022886658059080906538221568, 12253978061892529655103232048729702019689836031046984704), (3095001215093824025333399552, 3095011840495569810025943712, 12259591504139399439347648224654565770788855139482446941), (3136436439283302337840485024, 12253978016220603488513813926602659847373383351459119104, 12253999938767377253782143768003438628240489099305227256), (3136436441742267734454384288, 3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253978016220603488513813926602659847373383351459119104, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 328979603898640390953173080, 5962972329935505299752147220518445642556028475670264), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 723970729882168734101430747414256912657316433130160128), (22213632912598862894891456789161899752161280, 22213632912598866608711574646499002764230656, 12253978016220603658653699315333137953184481382709994496), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964326927110696725592761685001894404130353812357378), (22213632912598866691560943160600929436172288, 5962926680310083906271034778761321192467004194308096, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964326927110696725592761685001894404130353812357378), (22213632912598866937691177391916622924546136, 718357284780885403601626415479924402604454719448547328, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 724321535924835241209493075209209072142546598398263037), (22213801724556786128122975153446818488062712, 3796027076050101990859472896, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554, 12259964281277398502000616811941325495987236706799670266)],
  [(3095011839265488977428217856, 11493738479018726570043331228400651006983577936144105728, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12259940988550539163953451459088553212348621736978153120, 12259964281255184870415945414543680626644887919562482946), (4456421694480524656123576320, 5962926680310083906271034778761321192467004194308096, 5962972352236080355803771970710216988322578553126912), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12253978016220603658653699315333137953184481382709994496), (22213632912598866691560943160600929436172288, 12253978016220603658653699315333137953184481382709994496, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 328979603898640390953173080, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 45671925996449532737192591142555456639196463104, 723970775554094731798250604936157197751295449138694237), (22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 723970772699681184295575324801352220208828476220999773, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 11493738524690652566492866417952457612690528900066382840, 12259964324072697150470204603200297828385301931402447199)],
  [(2476522326560442447233548288, 5962926680310083906271037254641400993308391422120608, 12259964281277398502000616811941325495987236706799670266), (3136436441742267734454384288, 5962926680310083906271034778761321192467004194308096, 12253999938767377255110073689573720796696133639558084600), (4456421694480524661025022976, 3095011840495569810025943712, 5962972352236080357099310884143467436652214130572960), (22213632912598866691560943160600929436172288, 3796027076050101990859472896, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259591504139399439347648224654565770788855139482446941), (22213632912598867227843335341227430394270368, 22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 723970772699681184295575324801352220208828476220999773), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 11493738524690652566492866417952457612690528900066382840), (22213801724556786128122975153446818488062712, 45649625421393481112112928637431821966581939872, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 5962972352236080357099310884143467436652214130572960, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259940988550539163953451459088553212348621736978153120), (12259964329781524583263347831204649109514524023535187616, 5962969497740865086203281465144902292316204958992384, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964324072697319363938745882417301043233433711537503)],
  [(2475880078570760549798248448, 3095011840495569810025943712, 3796027076050101990859472896), (3136436441742267734454384288, 12253978016220603658653699315333137953184481382709994496, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 11493738479040940202955932547368578044781571263634150392), (3796671850016043105776041984, 12217709251740621387251507871840950661091759348901977085, 12259964281255184870415945414543680626644887919562482946), (22213632912598866691560943160600929436172288, 12259964281255184700276060025813202520833789888311607554, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12217709251740621387251507871840950661091759348901977085), (22213632912598867227843335341227430394270368, 328979603898640390953173080, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 45671925996449532737192591142555456639196463104, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 11493716556494166606499558173127995201269919006786060288), (12259964329781524583263347831204649109514524023535187616, 1320791768985116173695713280, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 12253999938767377255110073689573720796696133639558084600, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880079801142648581914624, 3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037), (3094850100672416088623939584, 45649625421392185573819269394437821823472177824, 11493738524690652566492866417952457612690528900066382840), (3136274697001183219894190080, 5962926680310083906271037254641400993308391422120608, 12259964281277398502000616811941325495987236706799670266), (3136274699460148611606642688, 12253978016220603488513813929078539928404310283539447808, 12259964326927110696725592761685001894404130353812357378), (3136436441742267734454384288, 3796027076050101990859472896, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964281277398503328546733511607664442881247052527610), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964326904810121669541137926131158265611854893547426), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 11493738479018726401231375761240455069628124445146087680), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964326904810121669541137926131158265611854893547426), (22213632912598866609353821406100067601874944, 5962926680310083906271034778761321192467004194308096, 11499701405721250286862203581528207605279309845030327288), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 723970775554094731798250604936157197751295449138694237), (2854413547502675280134804977542466972917694464, 22213632912598866608711574646499002764230656, 723970772699681184295575324801352220208828476220999773)],
  [(2475880079800841387227812512, 45649625421393481112112928637431821966581939872, 12259964281255184700276060025813202520833789888311607554), (3094860723615196476772192928, 350763225154056913917750407856851933718122177263264, 723970772699681184295575324801352220208828476220999773), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964326927110696725592761685001894404130353812357378), (3423840327513836867725366008, 45649707089160246598508740243678481574480838656, 724321535924835241209493075209209072142546598398263037), (4124854898985281128829026304, 328979603898640390953173080, 45671925996449532737521570745300874259356778584), (4125006679948742381812645976, 328979603898640390953173080, 3796027076050101990859472896), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964326927110696725592761685001894404130353812357378), (22213632912598864132831494845657620368326656, 22213632912598866608711574646499002764230656, 5962972329935505299752146891689958624288970776247968), (22213632912598866690918532839263890611634176, 5962972329935505299752146891689958624288970776247968, 12253999938767377255110073689573720796696133639558084600), (22213632912598867556671822359193221907682040, 5962972352236080357099310884143467436652214130572960, 724321535947054148498779213893059971019521663113887485)],
  [(3133999700483984610191151776, 718357284780885403601626415479924402604454719448547328, 12212095763821825606557558962519674624450846845113144312), (3796671850014842120038252544, 3136274699460148616508089344, 12259964281255184700276060028289082601863515839555593474), (3796671850016043105776041984, 45649625421392185573200137633743093395842138112, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 3136274699460148616508089344, 5962972352236080357099310884143467436652214130572960), (22213632912598866691560943160600929436172288, 12259964281255184870415945414543680626644887919562482946, 12259964281277398502000616811941325495987236706799670266), (22213801724556786128122975153446818488062712, 5962972329935505299752146891689958624288970776247968, 12259964281255184700276060025813202520833789888311607554)],
  [(3095001215093824025333399552, 11493716556494166606499558173128146982233380259769679960, 12259591504139399439347648224654565770788855139482446941), (3423840327513836867725366008, 724321490275128150801799632395568708259061789490167808, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 11499701451370875708255684691165256162910290424384454648), (3796671850016043105776041984, 0, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 5612209104781448385834396483833106690570848598984704, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 3796027076050101990859472896, 5962972329935505299752148211836953644665015293181600), (22213632912598866608711573493276231971373056, 723970772699681184295575324801352220208828476220999773, 11493738479040940202955932547039598440882930872680977312), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 11493738479040940202955932547368578044781571263634150392), (22213632912601318967927037797993327490044664, 12259964281255184870415945414543680626644887919562482946, 12259964281255184870415945414543680626644887919562482946), (22213801724556786128122975153446818488062712, 42817512450194144577387095307551512043090839645, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12259591504139399439347648224654565770788855139482446941, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 5962972352236080357099310884143467436652214130572960, 12259964324072697150470204603200297828385301931402447199)],
  [(3136916946219749681345733632, 1320791768985116173695713280, 12253978016220603658653699315333782727150422497626563584), (3796671850016043105776041984, 42817512448946857457057786165012989666278768640, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 723970775554094731798250604936157197751295449138694237, 12259964281255184870415945414543680626644887919562482946), (22213632912598866691560943160600929436172288, 5962972329935505299752146891689958624288970776247968, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 723970772699681184295575324801352220208828476220999773, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 11493738479018726401231375761240455069628124445146087680), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259940988550539163953451459088553212348621736978153120), (22213632912598867351474892321724846125823648, 5962972352236080357099310884143467436652214130572960, 12253999938767377255110073689573720796696133639558084600), (22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554, 12259964281255184870415945414543680626644887919562482946)],
  [(41424601246697924428440576, 760261459726437052154141142205142751914562375923934208, 11493738479040940202955932547368578044781571263634150392), (3133837958201865492244856832, 3136274699460148616508089344, 12217709251740621387251507871840950661091759348901977085), (3423840327513836867725366008, 45649625421392185573200137633743093395842138112, 724321535924835241209493075209209072142546598398263037), (3713822479042971075136716800, 3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12253978016220603488513813926602659847373383351459119104, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964281277398502000616811941325495987236706799670266), (168893734142682119472657931502309090304, 12259964324072697150470204603200297828385301931402447199, 12259964324072697150470204603200297828385301931402447199), (22213632912598866608711573493276231971373056, 2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773), (22213632912598866691560943160600929436172288, 12259591504139399439347648224654565770788855139482446941, 12259964281277398502000616811941325495987236706799670266), (12259964329781524583263347831204649109514524023535187616, 22213632912598866608711574646499002764230656, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 11499701451370875708255684691165256162910290424384454648, 12259964324072697150470204603200297828385301931402447199)],
  [(2476031195528293211042807808, 3095011840495569810025943712, 723970775554094731798250604936157197751295449138694237), (3136436441742267734454384288, 5962972329935505299752146891689958624288970776247968, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 0, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 5612209104781448385834396483833106690570848598984704, 724321535924835241209493075209209072142546598398263037), (3796027077280182823457128448, 3095011840495569810025943712, 12253978016220603658653699315333299695466600500656289440), (4456421694480524661025022976, 22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 723970772699681184295575324801352220208828476220999773), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 11493738524690652566492866417952457612690528900066382840), (22213632912598866691560943160600929436172288, 12253978016220603657325769393762855784728836842457137152, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560945619571033403555840, 12253999938767377255110073689573720796696133639558084600, 12259964281277398503328546733511607664442881247052527610), (22213632912598866937691177391916622924546136, 1320791768985116173695713280, 723970775554094731798250604936157197751295449138694237), (2832194640213389141450954078665491908202070016, 45649625421392185573200137633743093395842138112, 723970772699681184295575324801352220208828476220999773)],
  [(619131760694728427630039712, 45671925996449532737192591142555456639196463104, 11493738479018726570043333680759866470135072260869919736), (2475880078570760549798248448, 45649625421392185573200137633743093395842138112, 11493716556494166606499558173127995201269919006786060288), (2475880081030926932080328704, 170139885388730478105811098031250875392, 12259964281255184700276060025813202520833789888311607554), (2475880082259806778940194816, 22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600), (3133837958201865492244856832, 12212073841275052010101184588279091780939194588265054208, 12217709251740621387251507871840950661091759348901977085), (3423840327513836867725366008, 42817512448946857457057786165012989666278768640, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 723970775554094731798250604936157197751295449138694237, 724321535924835241209493075209209072142546598398263037), (3796671850016043105776041984, 5962926680310083906271034778761321192467004194308096, 12259964281255184870415945414543680626644887919562482946), (4415803609480685983721656992, 1320791768985116173695713280, 3095011840495569810025943712), (4456421694480524661025022976, 328979603898640390953173080, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 45671925996449532737192591142555456639196463104, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 11493716556494166606499558173127995201269919006786060288), (22213632912598866690918532839263890611634176, 11493716556494166606499558173127995201269919006786060288, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259940988550539163953451459088553212348621736978153120), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 11499701451370875708255684691165256162910290424384454648), (22213632912598867556671822359193221907682040, 724321535924835241209493075209209072142546598398263037, 724321535947054148498779213893059971019521663113887485), (22213801724556786128122975153446818488062712, 22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554, 12259964324072697150470204603200297828385301931402447199), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259964281277398502000616811941325495987236706799670266), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964324094910952194761389328420802385525976648113151), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964326927110697972879882092286904493443716589799775)],
  [(2475880078570760549798248448, 3136274699460148616508089344, 22213632912598866608711574646499002764230656), (3094860723615196476772192928, 3095011840495569810025943712, 723970772699681184295575324801352220208828476220999773), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 724321535947054148498779213893059971019521663113887485), (3796671850016043105776041984, 12253978016220603658653699315333137953184481382709994496, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 723970775554094731798250604936157197751295449138694237), (22213632912598866690918532839263890611634176, 3095011840495569810025943712, 12253999938767377255110073689573720796696133639558084600), (22213632912598867227681594289189145045630976, 3136274699460148616508089344, 45671925996449532737852985760985879309362013184), (22213632912598867227843335341227430394270368, 1320791768985116173695713280, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964326927110696726888300598435144852459989389803426), (22213801724556786128122975153446818488062712, 11493716556494166606499558173127995201269919006786060288, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259964281255184700276060025813202520833789888311607554)],
  [(2475880078570760549798248448, 3713820117857337103012069376, 11493716556494166606499558173127995201269919006786060288), (3423840327513535599089881760, 723970729882168734101430747414256912657316433130160128, 724321535924753572195280744508497345690883756072107680), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12253978016220603488513813926602659847373383351459119104), (3713820119010559873804926976, 11493716556494166606499558173128146982233380259769679960, 12259591504139399439347648224654565770788855139482446941), (3796671850016043105776041984, 3796027076050101990859472896, 12259964281255184870415945414543680626644887919562482946), (22213632912598866690918532839263890611634176, 3796027076050101990859472896, 22213632912598866608711574646499002764230656), (22213801724556786128122975153446818488062712, 3095011840495569810025943712, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 724321535924835241209493075209209072142546598398263037, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880079800841387227812512, 22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554), (2475880081030926932080328704, 3796027076050101990859472896, 12259964281255184700276060025813202520833789888311607554), (3423840327513836867725366008, 5962926680310083906271034778761321192467004194308096, 724321535924835241209493075209209072142546598398263037), (3796671850016043105776041984, 12259964281255184700276060025813202520833789888311607554, 12259964281255184870415945414543680626644887919562482946), (22213632912598866691560943160600929436172288, 11493716556494166606499558173127995201269919006786060288, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 5962972352236080357099310884143467436652214130572960, 723970775554094731798250604936157197751295449138694237), (12259964329781524583263347831204649109514524023535187616, 11493738479018726401231375761240455070781347218388484440, 12259964324072697150470204603200297828385301931402447199)],
  [(41424601246697924428440576, 5962972329935505299752143796678118128719160750304256, 11493738479040940202955932547368578044781571263634150392), (82206958192764887847403520, 3796027076050101990859472896, 11493738479040940202955932547368578044781571263634150392), (3713820119087417935609724928, 22213632912598866608711574646499002764230656, 12259940988550539163953451459088553212348621736978153120), (22213632912598866690918532839263890611634176, 723970729882168734101430747414256912657316433130160128, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 3095011840495569810025943712, 12259964281277398502000616811941325495987236706799670266), (22213801724556786747254735848175241286193912, 12254001354574874616369788991034441199641322884117299458, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964326904810121669541137926131158265611854893547426)],
  [(161742282119117946294944, 3095011840495569810025943712, 12253978016220603658653699315333137953184481382709994496), (2475880079800841387227812512, 3095011840495569810025943712, 12259964281255184700276060025813202520833789888311607554), (2475880081029725951243985920, 170139885388730478105811098031250875392, 12259964281255184700276060025813202520833789888311607554), (3095011840495569805194035200, 3095011840495569810025943712, 12259964326927110696725592761685001894404130353812357378), (3136436441742267734454384288, 11493716556494166606499558173127995201269919006786060288, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259940988550539163953451459088553212348621736978153120), (3423840327513836867725366008, 3796027076050101990859472896, 724321535924835241209493075209209072142546598398263037), (4414997095692792133140873216, 3095011840495569810025943712, 45671925996449532737811722903250185066826502816), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259940988550539163953451459088553212348621736978153120), (22213632912598866690918532839263890611634176, 3136274699460148616508089344, 12253999938767377255110073689573720796696133639558084600), (22213632912598866937691177391916622924546136, 22213632912598866608711574646499002764230656, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 724321535947054148498779213893059971019521663113887485), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 5962972352236080357099310884143467436652214130572960), (22213801724556786128122975153446818488062712, 723970729882168734101430747414256912657316433130160128, 12259964281255184700276060025813202520833789888311607554), (12259964329781524583263347831204649109514524023535187616, 11493738479040940202955932547368578044781571263634150392, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 12259964324072697150470204603200297828385301931402447199, 12259964326927110696725592761685001894404130353812357378)],
  [(3136436441742267734454384288, 3095011840495569810025943712, 12253999938767377255110073689573720796696133639558084600), (3713822479042971075136716800, 22213632912598866608711574646499002764230656, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964281255184870415945414543680626644887919562482946), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12253978016220603488513813926602659847373383351459119104), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964281277398502000616811941325495987236706799670266), (22213801724556786128122975153446818488062712, 3136274699460148616508089344, 12259964281255184700276060025813202520833789888311607554)],
  [(1320146995020376044516933632, 22300575057347163992453508812363243354324992, 5962972329935505299752146891689958624288970776247968), (2475880079801142648581914624, 22213632912598866608711574646499002764230656, 724321535924835241209493075209209072142546598398263037), (2804859682546560268742230104, 45649625421392185573200137633743093395842138112, 723970775531875824508964466252306298874320384423069789), (3094860723615196476772192928, 723970772699681184295575324801352220208828476220999773, 11493738479040940202955932547039598440882930872680977312), (4042647940792516240981622784, 22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237), (4042799721755977493965242456, 3796027076050101990859472896, 723970772699681184295575328520008041497746792504854621), (22213632912598866690918530380293786644250624, 12253978016220603488513813926602659847373383351459119104, 12253999938767377253782143768003438628240489099305227256), (22213632912598866691560943160600929436172288, 723970729882168734101430747414256912657316433130160128, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 22213632912598866608711574646499002764230656, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12253978061892529655103232048729702019689836031046984704)],
  [(3095011840495569805194035200, 11493738479040940034143974626611224243803609200886546688, 12259964326927110696725592761685001894404130353812357378), (3713822479042971075136716800, 11493738479018726570043331228400651006983577936144105728, 12259964281255184870415945414543680626644887919562482946), (3791191372618520777587687424, 3796027076050101990859472896, 12217709251740621387251507871840950661091759348901977085), (3796671850016043105776041984, 5962972329935505299752146891689958624288970776247968, 12259964281255184870415945414543680626644887919562482946), (4332951879782146363239764640, 3796027076050101990859472896, 5962972329935505299752148211836953644665015293181600), (22213632912598866691560943160600929436172288, 3136274699460148616508089344, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 3095011840495569810025943712, 22213632912598866608711574646499002764230656), (22213801724556783652242895352605431260250200, 12259964326904810121669541137926131158265611854893547426, 12259964326904810121669541137926131158265611854893547426), (22213801724556786128122974000224045245665952, 12259964324072697150470204603200297828385301931402447199, 12259964324072697150470204603200297828385301931402447199), (2832199914590076413526093404049190740946321408, 12217709251740621387251507871840950661091759348901977085, 12217709251740621387251507871840950661091759348901977085), (2854413547502675278891989076108141785187352576, 12259964324072697150470204603200297828385301931402447199, 12259964324072697150470204603200297828385301931402447199), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259964281255184870415945414543680626644887919562482946), (2854413547502675280212176232303650647493312512, 5613487918795780693948909321427817604373756772452445, 723970772699681184295575324801352220208828476220999773)],
  [(3094850099443531524677304320, 3095011840495569810025943712, 12253978061892529655103232048729702019689836031046984704), (3095011840495569805194035200, 5962972329935505298456607978256708175959335198801920, 12259964326927110696725592761685001894404130353812357378), (3136436441742267734454384288, 723970729882168734101430747414256912657316433130160128, 12253999938767377255110073689573720796696133639558084600), (3423677921148629830049202176, 718357284780885403601626418577211242076188535791428608, 724321535924835241209493075209209072142546598398263037), (3423677921148629830049202176, 724321535924835241209493075209209072142546598398263037, 11493716556494166606499558173127995201269919006786060288), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12253978016220603658653699315333137953184481382709994496), (3796671850016043105776041984, 12259591504139399439347648224654565770788855139482446941, 12259964281255184870415945414543680626644887919562482946), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964324072697150470204603200297828385301931402447199), (4456421694480524661025022976, 1320791768985116173695713280, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964326927110696726888300598435144852459989389803426), (22213632912598866608711577105464399308521472, 3136274699460148616508089344, 11493738479040940202955932547410002646028269188062590968), (22213632912598866690918532839263890611634176, 718357284780885403601626415479924402604454719448547328, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253978061892529655103232048729702019689836031046984704, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916620475006976, 723970729882168734101430747414256912657316433130160128, 723970775554094730550963484528872187661982086361251840), (22213632912598866937691177391916622924546136, 723970729882168734101430748657072814091641620860502016, 723970775554094731798250604936157197751295449138694237)],
  [(2475880081029725951243985920, 45649625421393481112112928637431821966581939872, 12259964281255184700276060025813202520833789888311607554), (2476522327789327011180183552, 45649625421392185573200137633743093395842138112, 12259964281255184870415945414543680626644887919562482946), (3136436441742267734454384288, 3136274699460148616508089344, 12253999938767377255110073689573720796696133639558084600), (3796671850016043105776041984, 12259964281255184870415945414543680626644887919562482946, 12259964326927110866865478147939599919184301452982904066), (22213632912598866690918532839263890611634176, 328979603898640390953173080, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 45671925996449532737192591142555456639196463104, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 718357284780885403601626415479924402604454719448547328, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12253978061892529655103232048729702019689836031046984704, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 45649625421392185573200137633743093395842138112, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12253999938767377255110073689573720796696133639558084600), (12259964329781524583263347831204649109514524023535187616, 12259940988550539163953451459088553212348621736978153120, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 2475880081029725946342539264, 3136274699460148616508089344), (3095011840495871076211954336, 42817512448946857457057786165012989666278768640, 5962972330017173067813172200292568559677149414948512), (3423829702112091083032821848, 3136274699460148616508089344, 723970772699681184295575327898639059680562292563881053), (3423840327513836867725366008, 5962972329935505299752146891689958624288970776247968, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259942267364553496261565971965135783250839445316828925), (4042647940792516240981622784, 723970775554094731798250604936157197751295449138694237, 11493716556494166606499558173127995201269919006786060288), (22213632912598865370769174175484755740459008, 22213801724556786128122975153446818488062712, 12259964281255184700276060025813202520833789888311607554), (22213632912598866690918532839263890611634176, 12253999938745163452057586981875315653087042280817164544, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937539397581678140733784064, 718357284780885403601626415479924402604454719448547328, 718357330452811400051159152595144290398727684069392384), (22213801724556786128122975153446818488062712, 328979603898640390953173080, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 45671925996449532737192591142555456639196463104, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 0, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 5612209104781448385834396483833106690570848598984704, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 2475880079800841382395904000, 45649625421392185573200137633743093395842138112), (2475880078570760549798248448, 2475880081029725946342539264, 3796027076050101990859472896), (2475880078570760549798248448, 3094850098213450692079648768, 3136274699460148616508089344), (2475880082259806778940194816, 45649625421392185573200137633743093395842138112, 12253999938767377255110073689573720796696133639558084600), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964326904810121669541137926131158265611854893547426), (22213632912598866691560943160600929436172288, 718357284780885403601626415479924402604454719448547328, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12253978061892529655103232048729702019689836031046984704, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964326927110697972879882092286904493443716589799775), (2832194640213389141450954078665491908202070016, 350763225154056913917750407856851933718122177263264, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 42817512448946857457057786165012989666278768640, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 12217709251740621387251507871840950661091759348901977085, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 2475880079800841382395904000, 22213632912598866608711574646499002764230656), (3136274700690229449105744896, 22213632912598866608711574646499002764230656, 12253978016242817291566298178228029409973643282462155776), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 12259964326927110696725592761685001894404130353812357378), (3796671850016043105776041984, 5962926680310083906271037254641402222192955438294016, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 5962972352236080357099310884143467436652214130572960), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12253999984417089618647007560075393406412326388142913528), (22213632912598866691560943160600929436172288, 328979603898640390953173080, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 45671925996449532737192591142555456639196463104, 12259964281277398502000616811941325495987236706799670266), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12253978016220603658653699315333137953184481382709994496), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 718357284780885403601626415479924402604454719448547328), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12253978061892529655103232048729702019689836031046984704), (22213801724556786457102577898864436198839032, 11535993551373015966174629278398945608176473455181447426, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 724321535924835241209493075209209072142546598398263037)],
  [(619131760694728427630039712, 45671925996449532737192591142555456639196463104, 5962926680310083907566573691552324881195574934109856), (660394618430422670165550080, 45671925996449532737192591142555456639196463104, 5962926680310083907566573691552324881195574934109856), (3136436441742267734454384288, 3095011840495569810025943712, 3136274699460148616508089344), (3136436441742267734454384288, 718357284780885403601626415479924402604454719448547328, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253978061892529655103232048729702019689836031046984704, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964281277398502000616811941325495987236706799670266), (3465102522395327754477642752, 328979603898640390953173080, 5962972329935505299752147220518445642556028475670264), (3796671850016043105776041984, 11493716556494166606499558173127995201269919006786060288, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964281277398502000616811941325495987236706799670266), (22213632912598866608711573493276231971373056, 22213632912598866608711574646499002764230656, 723970772699681184295575324801352220208828476220999773), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964281255184870415945414543680626644887919562482946), (22213801724556786128122975153446818488062712, 12259964281255184700276060024492410751848673714615894274, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 42817512448946857457057786165012989666278768640, 42817512448946857457057786165012989666278768640)],
  [(2475880082259806778940194816, 3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600), (3095011842954535206570234528, 3796027076050101990859472896, 11493738479040940202955932547450785002974336151481553912), (3136436441742267734454384288, 328979603898640390953173080, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 45671925996449532737192591142555456639196463104, 12253999938767377255110073689573720796696133639558084600), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12259964281255184700276060025813202520833789888311607554), (3796671850016043105776041984, 3095011840495569810025943712, 12259964281255184870415945414543680626644887919562482946), (4456421694480524661025022976, 3136274699460148616508089344, 3796027076050101990859472896), (4456421694480524661025022976, 22213632912598866608711574646499002764230656, 5962972352236080357099310884143467436652214130572960), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12259964281255184700276060025813202520833789888311607554), (22213632912598866690918532839263890611634176, 11493738479018726401231375761240455069628124445146087680, 12253999938767377255110073689573720796696133639558084600), (22213632912598866691560943160600929436172288, 5962926680310083906271037254641400993308391422120608, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960), (22213632912598867556671822359193221907682040, 723970775554094731798250604936157197751295449138694237, 724321535947054148498779213893059971019521663113887485), (2854413547502675280134804977542466972917694464, 5962926680310083906271034778761321192467004194308096, 723970772699681184295575324801352220208828476220999773), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12259591504139399439347648224654565770788855139482446941), (12259964326949329943049798965778104053182551257717932032, 724321535924835241209493075209209072142546598398263037, 12259964326904891790683753468626842884717274697219702783), (12259964329781524583263347831204649109514524023535187616, 45649625421392185573200137633743093395842138112, 12259964324072697150470204603200297828385301931402447199)],
  [(2475880078570760549798248448, 2475880081029725946342539264, 45649625421392185573200137633743093395842138112), (3136274699460148611606642688, 3136274699460148616508089344, 12259964326927110696725592761685001894404130353812357378), (3136274699460148611606642688, 5962972329935505298456607978256708175959335198801920, 12259964326927110696725592761685001894404130353812357378), (3136436441742267734454384288, 12253999938745163452057586981875315653087042280817164544, 12253999938767377255110073689573720796696133639558084600), (3213645951915489281870013440, 42817512448946857457057786165012989666278768640, 5962972330017173067813172200292568559677149414948512), (3713820119010559873804926976, 42817512448946857460776441986301907982562623488, 12259591504139399439347648224654565770788855139482446941), (4042647940792516240981622784, 718357284780885403601626419198580223893373035732402176, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964326904810121669541137926131158265611854893547426), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12253999938767377255110073689573720796696133639558084600), (22213801724556786128122975153446818488062712, 11493738479018726401231375761240455069628124445146087680, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 12217709251740621387251507871840950661091759348901977085), (12259964329759310781538791045076526135514299978289521664, 12217709251740621387251507871840950661091759348901977085, 12259964324094910952194761389328420802385525976648113151), (12259964329781524583263347831204649109514524023535187616, 0, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 5612209104781448385834396483833106690570848598984704, 12259964324072697150470204603200297828385301931402447199)],
  [(22213632912598866686687442197289988729602048, 723970729882168734101430747414256912657316433130160128, 12217709208923108937057363294453855354693470079053534200), (22213632912598866690918532839263890611634176, 718357284780885403601626415480076183567915972432167000, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 723970772699681184295575324801352220208828476220999773, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 11493738524690652566492866417952457612690528900066382840, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964281255184870415945414543680626644887919562482946), (22213632912598866937691177391916622924546136, 5612211936976088599223537934787185356062756801054720, 723970775554094731798250604936157197751295449138694237), (22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237, 12259964326927110696725592761685001894404130353812357378), (22213632912598867227843335341227425562361856, 5962926680310083906271034778761321192467004194308096, 5962972352236080355803771970710216988322578553126912), (22213632912598867227843335341227430394270368, 3095011840495569810025943712, 45671925996449532737811722903250185066826502816), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259964324072697150470204603200297828385301931402447199), (2854413547502675280134804977542466972917694464, 3796027076050101990859472896, 723970772699681184295575324801352220208828476220999773), (12259964329781524583263347831204649109514524023535187616, 42817512448946857457057786165012989666278768640, 12259964324072697150470204603200297828385301931402447199), (12259964329781524583263347831204649109514524023535187616, 723970775554094731798250604936157197751295449138694237, 12259964324072697150470204603200297828385301931402447199)],
  [(161742282119117946294944, 21922546773596456374374240582843511652256848090104, 12253978016220603658653699315333137953184481382709994496), (2475880078570760549798248448, 2475880079800841382395904000, 3095011840495569810025943712), (3136436441742267734454384288, 12253999938767377255110073689573720796696133639558084600, 12253999984417089618647007560075393406412326388142913528), (3423677921148629830049202176, 3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 3095011840495569810025943712, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 11493738524690652566492866417952457612690528900066382840), (3796671850016043105776041984, 723970729882168734101430747414256912657316433130160128, 12259964281255184870415945414543680626644887919562482946), (4332790137500027245293469696, 22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960), (22213632912598866691560943160600929436172288, 11493738479018726401231375761240455069628124445146087680, 12259964281277398502000616811941325495987236706799670266), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 11499701451370962650400432991024878176876996047370452984), (22213801724556786128122975153446818488062712, 723970772699681184295575324801352220208828476220999773, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 766225802236458299044684264572747451205665443165519874, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 11493738524690652566492866417952457612690528900066382840, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324472372616310188085267826693, 723970772699681184295575324801352220208828476220999773), (12259964326927111035760672552312660033406382238347835040, 12259964326927110696725592761685001894404130353812357378, 12259964326927110697972879882092286904493443716589799775), (12259964329781524583263347831204649109514524023535187616, 12253978016220603488513813926602659847373383351459119104, 12259964324072697150470204603200297828385301931402447199)],
  [(2514867938712297737294053376, 5612211936976088599223537934787185356062756801054720, 723970775554094731798250604936157197751295449138694237), (3423840327513836867725366008, 718357284780885403601626418577211242076188535791428608, 724321535924835241209493075209209072142546598398263037), (3423840327513836867725366008, 724321535924835241209493075209209072142546598398263037, 11493716556494166606499558173127995201269919006786060288), (3465254303358789007461262424, 328979603898640390953173080, 3136274699460148616508089344), (3713820119010559873804926976, 22213632912598866608711574646499002764230656, 12259591504139399439347648224654565770788855139482446941), (3713820119087417935609724928, 11493716556494166606499558173128156943552038124732355232, 12259940988550539163953451459088553212348621736978153120), (3796669322809703055697117184, 5962926680310083906271034778761321192467004194308096, 12259940942900913742559970349451504655946525721640199168), (3796671850016043105776041984, 3136274699460148616508089344, 12259964281255184870415945414543680626644887919562482946), (4332790137500027245293469696, 5962972352236080357099310884143467436652214130572960, 11493716556494166606499558173127995201269919006786060288), (22213632912598866690918532839263890611634176, 1320791768985116173695713280, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12253999938767377255110073689573720796696133639558084600), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259613426686173035804022598894996833337046143346917373), (22213632912598866937691177391916622924546136, 22213632912598866937691177391916622924546136, 723970775554094731798250604936157197751295449138694237), (22213632912598867227843335341227430394270368, 22213632912598866608711574646499002764230656, 5962972352149138212351011024521453469946591144574624), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 724321535924835241209493075209209072142546598398263037), (22213801724556786128122975153446818488062712, 22213801724556786128122975153446818488062712, 11493738479040940202955932547368578044781571263634150392), (2854413547502675280134804977542466972917694464, 5613487918795780693948909321427817604373756772452445, 723970772699681184295575324801352220208828476220999773)],
  [(2475880079801142648581914624, 45649707089160246598508740243678481574480838656, 724321535924835241209493075209209072142546598398263037), (3136436441742267734454384288, 11493738479018726401231375761240455069628124445146087680, 12253999938767377255110073689573720796696133639558084600), (3796671848785957556091617280, 3095011840495569810025943712, 12259964281255184700276060028289082600634631275539420066), (4374214738746725169721910272, 22213632912598866608711574646499002764230656, 5962972352149138212351011024521453469946591144574624), (22213632912598866690918532839263890611634176, 12253999938767377255110073689573720796696133639558084600, 12259964324072697150470204603200297828385301931402447199), (22213632912598866691560943160600929436172288, 723970772699681184295575324801352220208828476220999773, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 11493738524690652566492866417952457612690528900066382840, 12259964281277398502000616811941325495987236706799670266), (22213632912598866691560943160600929436172288, 12259964281277398502000616811941325495987236706799670266, 12259964324072697150470204603200297828385301931402447199), (22213801724556786128122975153446818488062712, 1320791768985116173695713280, 12259964281255184700276060025813202520833789888311607554), (22213801724556786128122975153446818488062712, 12253999938767377255110073689573720796696133639558084600, 12259964281255184700276060025813202520833789888311607554), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11493738479040940202955932547368578044781571263634150392), (12259964329781524583263347831204649109514524023535187616, 5962926680310083906271034778761321192467004194308096, 12259964324072697150470204603200297828385301931402447199)],
  [(2476522326560442447233548288, 45649625421392185573200137633743093395842138112, 12259964281277398502000616811941325495987236706799670266), (3136436441742267734454384288, 3136274699460148616508089344, 11493738479040940202955932547410002646028269188062590968), (3423840327513836867725366008, 723970729882168734101430747414256912657316433130160128, 724321535924835241209493075209209072142546598398263037), (3718655821288918316283854848, 3796027076050101990859472896, 723970772699681184295575324801352220208828476220999773), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 718357284780885403601626415479924402604454719448547328), (4456421694480524661025022976, 5962972352236080357099310884143467436652214130572960, 12253978061892529655103232048729702019689836031046984704), (22213632912598867227843335341227430394270368, 5612209104863116153895421792435716625959027237685248, 5962972352236080357099310884143467436652214130572960), (22213632912598867227843335341227430394270368, 5962972352236080357099310884143467436652214130572960, 12259591504139399439347648224654565770788855139482446941), (2854413547502675280134804977542466972917694464, 723970772699681184295575324801352220208828476220999773, 11493738479018726401231375761240455069628124445146087680), (12259964326927111035760672552312660033406382238347835040, 723970775554094731798250604936157197751295449138694237, 12259964326927110697972879882092286904493443716589799775), (12259964329781524583263347831204649109514524023535187616, 12253978016220603658653699315333137953184481382709994496, 12259964324072697150470204603200297828385301931402447199)]]

def shortMember (u : ℕ) : Bool := (shortBuckets.getD (u % 31) []).contains u

def longMember (t : ℕ × ℕ × ℕ) : Bool :=
  (longBuckets.getD ((t.1 + 3 * t.2.1 + 7 * t.2.2) % 61) []).contains t

def verifyPrefix (a : ℕ) : Bool :=
  frc a fun a =>
    (gateValues (initialN ++ [a])).all fun b => frc b fun b =>
      (rawGateValues (initialN ++ [a, b])).all fun u => frc u fun u =>
        !goodMask u || shortMember u || longMember (pairKey u a b)

def seedValues (u : W) (extra : List W) : List W :=
  (primary.getD 0 0 ||| u) :: (primary.drop 1 ++ (u :: extra))

def sources (u : W) (extra : List W) : List W :=
  (((seedValues u extra).map canonical).filter (fun w => w != 0)).dedup

def checkReach (m : ℕ) (src : List W) : Bool :=
  let values := src.map BitVec.toNat
  (rootsN (m+1) values).all (fun ws => !nisGoal ws) &&
    (allKids m values).all (dead m)

def checkShort (u : ℕ) : Bool := checkReach 7 (sources (BitVec.ofNat 184 u) [])

def checkLong (t : ℕ × ℕ × ℕ) : Bool :=
  checkReach 5 (sources (BitVec.ofNat 184 t.1) [BitVec.ofNat 184 t.2.1, BitVec.ofNat 184 t.2.2])

lemma nat_not (w : W) : (~~~w).toNat = M120 - w.toNat := by
  rw [BitVec.toNat_not]
  rfl

lemma zero_value (ws : List ℕ) : 0 ∈ gateValues ws := by simp [gateValues, rawGateValues]

lemma one_value (ws : List ℕ) : M120 ∈ gateValues ws := by simp [gateValues, rawGateValues]

lemma read_value {ws : List ℕ} {a : ℕ} (h : a ∈ ws) : a ∈ gateValues ws := by
  simp only [gateValues, rawGateValues, List.mem_dedup, List.mem_cons, List.mem_append]
  exact .inr (.inr (.inl (.inl h)))

lemma not_value {ws : List ℕ} {a : ℕ} (h : a ∈ ws) :
    M120 - a ∈ gateValues ws := by
  simp only [gateValues, rawGateValues, List.mem_dedup, List.mem_cons, List.mem_append]
  exact .inr (.inr (.inl (.inr (List.mem_map.mpr ⟨a, h, rfl⟩))))

lemma binary_value {ws : List ℕ} {a b c : ℕ} (ha : a ∈ ws) (hb : b ∈ ws)
    (hc : c ∈ [Nat.land a b, Nat.lor a b]) : c ∈ gateValues ws := by
  simp only [gateValues, rawGateValues, List.mem_dedup, List.mem_cons, List.mem_append]
  exact .inr (.inr (.inr (List.mem_flatMap.mpr
    ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, hc⟩⟩)))

lemma action_value (g : Gate) (w : List W) (vals : List ℕ) (hg : legal g)
    (hr : ∀ j ∈ g.inputs, (w.getD j 0).toNat ∈ vals) :
    (action w g).toNat ∈ gateValues vals := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,
      List.foldr_nil,List.foldr_cons,Option.map_none,Option.map_some,
      Option.getD_none,Option.getD_some,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes,
      BitVec.toNat_and, BitVec.toNat_or, nat_not]
  all_goals first
    | exact zero_value vals
    | exact one_value vals
    | exact read_value (hr i (by simp))
    | exact not_value (hr i (by simp))
    | exact binary_value (hr i (by simp)) (hr j (by simp)) (by simp)

lemma prefix_read (more : List W) (j : ℕ) (hj : j ≠ 0) :
    ((primary ++ more).getD j 0).toNat ∈ initialN ++ more.map BitVec.toNat := by
  cases j with
  | zero => contradiction
  | succ j =>
    let src := primary.drop 1 ++ more
    have eq : (primary ++ more).getD (j+1) 0 = src.getD j 0 := by
      change ((primary.getD 0 0 :: primary.drop 1) ++ more).getD (j+1) 0 = _
      simp [src]
    rw [eq]
    change (src.getD j 0).toNat ∈ 0 :: ((primary.drop 1).map BitVec.toNat ++ more.map BitVec.toNat)
    rw [← List.map_append]
    by_cases h : j < src.length
    · apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨src.getD j 0, by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        exact List.getElem_mem h, rfl⟩
    · rw [List.getD_eq_default _ _ (by omega)]
      exact List.mem_cons_self ..

def atGate (gs : List Gate) (j : ℕ) : W :=
  action (runW (gs.take j) primary) (gs.getD j emptyGate)

lemma prefix_values (gs : List Gate) (hlen : gs.length = 10) (hg : ∀ g ∈ gs, legal g)
    (hr : ∀ j < gs.length, j ≠ 6 → 0 ∉ (gs.getD j emptyGate).inputs) :
    let a := (atGate gs 0).toNat
    let b := (atGate gs 1).toNat
    let u := (atGate gs 2).toNat
    a ∈ gateValues initialN ∧ b ∈ gateValues (initialN ++ [a]) ∧
      u ∈ gateValues (initialN ++ [a,b]) := by
  rcases gs with _|⟨g,_|⟨h,_|⟨l,gs⟩⟩⟩ <;> simp at hlen
  let a := action primary g
  let b := action (primary ++ [a]) h
  change a.toNat ∈ gateValues initialN ∧ (b.toNat ∈ gateValues (initialN ++ [a.toNat])) ∧
    (action (primary ++ [a,b]) l).toNat ∈ gateValues (initialN ++ [a.toNat,b.toNat])
  refine ⟨action_value _ _ _ (hg g (by simp)) ?_, action_value _ _ _ (hg h (by simp)) ?_,
    action_value _ _ _ (hg l (by simp)) ?_⟩
  · intro j hj
    have hn : 0 ∉ g.inputs := hr 0 (by simp) (by decide)
    simpa using prefix_read [] j (fun e => hn (e ▸ hj))
  · intro j hj
    have hn : 0 ∉ h.inputs := hr 1 (by simp) (by decide)
    simpa using prefix_read [a] j (fun e => hn (e ▸ hj))
  · intro j hj
    have hn : 0 ∉ l.inputs := hr 2 (by simp) (by decide)
    simpa using prefix_read [a,b] j (fun e => hn (e ▸ hj))

lemma vector_at (gs : List Gate) (w : List W) (j : ℕ) (hj : j < gs.length) :
    (runW gs w).getD (w.length+j) 0 =
      action (runW (gs.take j) w) (gs.getD j emptyGate) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (runW gs (w ++ [action w g])).getD (w.length+0) 0 = action w g
      rw [Nat.add_zero, runW_stable _ _ _ (by simp)]
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      rfl
    | succ j =>
      change (runW gs (w ++ [action w g])).getD (w.length+(j+1)) 0 = _
      rw [show w.length+(j+1) = (w ++ [action w g]).length+j by simp; omega,
        ih _ j (by simp at hj; omega)]
      rfl

lemma atGate_read (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (runW gs primary).getD (7+j) 0 = atGate gs j := by
  exact vector_at gs primary j hj

lemma vector_initial (k : Fin 184) : List.ofFn (row k) = primary.map (bit k) := by
  apply List.ext_getElem
  · simp [primary]
  · intro i hi hj
    have hlt : i < primary.length := by simpa using hj
    simp only [List.getElem_ofFn, List.getElem_map, row, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some]

lemma vector_read (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (j : ℕ) (k : Fin 184) :
    bit k ((runW gs primary).getD j 0) =
      (Circuit.wires ⟨gs,0⟩ (List.ofFn (row k))).getD j false := by
  rw [← read_bit, runW_bits _ _ hg, ← vector_initial]
  rfl

lemma vectors_compute (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x) :
    (runW gs primary).getD out 0 = ~~~goal := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 184 := ⟨j,hj⟩
  change bit k ((runW gs primary).getD out 0) = bit k (~~~goal)
  rw [vector_read _ hg]
  exact (he (row k)).trans (sample_target k)

lemma stable (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD j false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hj

def Agree (w v : List Bool) : Prop := ∀ j, j ≠ 0 → w.getD j false = v.getD j false

lemma extend (w v : List Bool) (b : Bool) (hl : w.length = v.length)
    (h : Agree w v) : Agree (w ++ [b]) (v ++ [b]) := by
  intro j hj
  by_cases lt : j < w.length
  · have lt' : j < v.length := hl ▸ lt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h j hj
  · have le : w.length ≤ j := by omega
    have le' : v.length ≤ j := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right le,
      List.getElem?_append_right le', hl]

lemma input_agree (x : Fin 7 → Bool) : Agree (List.ofFn x) (List.ofFn (mark x)) := by
  intro j hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i h
    have nz : (⟨j,h⟩ : Fin 7) ≠ 0 := fun he => hj (congrArg Fin.val he)
    simp [mark, nz]
  · rfl

lemma masking_agree (gs : List Gate) (p : ℕ) (w v : List Bool)
    (hwl : w.length = 7+p) (hvl : v.length = w.length) (ha : Agree w v)
    (hw : (gs.foldl step w).getD 9 false = true)
    (hr : ∀ j < gs.length, 0 ∈ (gs.getD j emptyGate).inputs →
      p+j = 6 ∧ (gs.getD j emptyGate).op = .or ∧ 9 ∈ (gs.getD j emptyGate).inputs) :
    Agree (gs.foldl step w) (gs.foldl step v) := by
  induction gs generalizing p w v with
  | nil => exact ha
  | cons g gs ih =>
    have ev : g.op.eval (g.inputs.map fun j => w.getD j false) =
        g.op.eval (g.inputs.map fun j => v.getD j false) := by
      by_cases hm : 0 ∈ g.inputs
      · obtain ⟨hp, hop, h9⟩ : p = 6 ∧ g.op = .or ∧ 9 ∈ g.inputs := by
          simpa using hr 0 (by simp) hm
        have ht : w.getD 9 false = true :=
          (stable (g :: gs) w 9 (by omega)).symm.trans hw
        have htv : v.getD 9 false = true := (ha 9 (by decide)).symm.trans ht
        have go (s : List Bool) (hs : s.getD 9 false = true) :
            g.op.eval (g.inputs.map fun j => s.getD j false) = true := by
          rw [hop]
          exact List.any_eq_true.mpr
            ⟨true, List.mem_map.mpr ⟨9, h9, hs⟩, rfl⟩
        rw [go w ht, go v htv]
      · congr 1
        exact List.map_congr_left fun j hj => ha j (fun e => hm (e ▸ hj))
    change Agree (gs.foldl step (step w g)) (gs.foldl step (step v g))
    refine ih (p+1) _ _ (by simp [step, hwl, Nat.add_assoc]) (by simp [step,hvl]) ?_ hw ?_
    · simpa only [step, ev] using extend w v (g.op.eval (g.inputs.map fun j => v.getD j false)) hvl.symm ha
    · intro j hj hread
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hr (j+1) (by simp; omega) hread

lemma forbidden_mask (gs : List Gate) (out : ℕ) (ho : out ≠ 0)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x)
    (hr : ∀ j < gs.length, 0 ∈ (gs.getD j emptyGate).inputs →
      j = 6 ∧ (gs.getD j emptyGate).op = .or ∧ 9 ∈ (gs.getD j emptyGate).inputs)
    (x : Fin 7 → Bool) (hx : target x = false) (hy : target (mark x) = true) :
    (Circuit.wires ⟨gs,out⟩ (List.ofFn x)).getD 9 false = false := by
  cases hw : (Circuit.wires ⟨gs,out⟩ (List.ofFn x)).getD 9 false
  · rfl
  · have ha := masking_agree gs 0 (List.ofFn x) (List.ofFn (mark x)) (by simp) (by simp)
        (input_agree x) hw (by simpa using hr) out ho
    change Circuit.eval ⟨gs,out⟩ (List.ofFn x) =
      Circuit.eval ⟨gs,out⟩ (List.ofFn (mark x)) at ha
    rw [he, he, hx, hy] at ha
    contradiction

lemma mask_good (gs : List Gate) (out : ℕ) (hlen : gs.length = 10) (ho : out ≠ 0)
    (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x)
    (hr : ∀ j < gs.length, 0 ∈ (gs.getD j emptyGate).inputs →
      j = 6 ∧ (gs.getD j emptyGate).op = .or ∧ 9 ∈ (gs.getD j emptyGate).inputs)
    (x : Fin 7 → Bool) (h0 : x 0 = false) (h1 : x 1 = false) (h6 : x 6 = false)
    (hx : (Circuit.wires ⟨gs,out⟩ (List.ofFn x)).getD 9 false = true) :
    goodMask (atGate gs 2).toNat = true := by
  let u := atGate gs 2
  have hu : ∀ k, bit k u = (Circuit.wires ⟨gs,out⟩ (List.ofFn (row k))).getD 9 false := by
    intro k
    change bit k (atGate gs 2) = _
    rw [← atGate_read gs 2 (by omega)]
    exact vector_read gs hg 9 k
  have sens : u &&& sensitiveRows = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    let k : Fin 184 := ⟨j,hj⟩
    change bit k (u &&& sensitiveRows) = bit k 0
    have e : bit k (u &&& sensitiveRows) = (bit k u && bit k sensitiveRows) :=
      BitVec.getElem_and k.isLt
    rw [e]
    cases hs : bit k sensitiveRows
    · simp [bit]
    · obtain ⟨a,b⟩ := sample_sensitive k hs
      rw [hu, forbidden_mask gs out ho he hr (row k) a b]
      simp [bit]
  obtain ⟨r, rfl⟩ := witness_exhaustive x h0 h1 h6
  obtain ⟨hs, hr'⟩ := sample_witness r
  have hw : bit (witnessIndex r) u = true := by
    rw [hu, hr']
    exact hx
  have nonzero : u &&& witnessRows ≠ 0 := by
    intro e
    have contra := congrArg (bit (witnessIndex r)) e
    change (u &&& witnessRows)[(witnessIndex r).val] = (0 : W)[(witnessIndex r).val] at contra
    rw [BitVec.getElem_and] at contra
    have zeroBit : bit (witnessIndex r) (0 : W) = false := by
      change (0#184)[(witnessIndex r).val] = false
      exact BitVec.getElem_zero (witnessIndex r).isLt
    change (bit (witnessIndex r) u && bit (witnessIndex r) witnessRows) =
      bit (witnessIndex r) (0 : W) at contra
    rw [zeroBit] at contra
    rw [hw, hs] at contra
    contradiction
  have natNonzero : (u &&& witnessRows).toNat ≠ 0 :=
    fun h => nonzero (BitVec.eq_of_toNat_eq h)
  change goodMask u.toNat = true
  unfold goodMask
  rw [← BitVec.toNat_and, ← BitVec.toNat_and, sens]
  have eqFalse : ((u &&& witnessRows).toNat == 0) = false := by
    exact beq_eq_false_iff_ne.mpr natNonzero
  rw [eqFalse]
  rfl

lemma canonical_eq (u : W) : canonical u = u ∨ canonical u = ~~~u := by
  unfold canonical canonicalN
  rw [← nat_not]
  rcases le_total u.toNat (~~~u).toNat with h | h
  · left
    rw [min_eq_left h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · right
    rw [min_eq_right h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

lemma source_holds (u v : W) (extra : List W) (hv : v ∈ seedValues u extra) :
    holds (sources u extra).toFinset v := by
  have hc := canonical_eq v
  by_cases hz : canonical v = 0
  · rcases hc with h | h
    · exact .inl (h.symm.trans hz)
    · have e : ~~~v = 0 := h.symm.trans hz
      exact .inr (.inl (by simpa only [BitVec.not_not] using congrArg (fun x : W => ~~~x) e))
  · refine .inr (.inr ⟨canonical v, ?_, ?_⟩)
    · simp only [sources, List.mem_toFinset, List.mem_dedup, List.mem_filter, List.mem_map,
        ne_eq, bne_iff_ne]
      exact ⟨⟨v,hv,rfl⟩,hz⟩
    · rcases hc with h | h
      · exact .inl h.symm
      · exact .inr (by simp [h])

lemma canonical_source (u v : W) (extra : List W) (hv : canonical v ∈ seedValues u extra) :
    holds (sources u extra).toFinset v := by
  have h := source_holds u (canonical v) extra hv
  rcases canonical_eq v with e | e
  · rwa [e] at h
  · rw [e] at h
    simpa using holds_not h

lemma initial_holds (u : W) (extra : List W) :
    ∀ i, i ≠ 0 → holds (sources u extra).toFinset (primary.getD i 0) := by
  intro i hi
  by_cases hb : i < 7
  · apply source_holds
    have mem : primary.getD i 0 ∈ primary.drop 1 := by
      interval_cases i <;> simp_all [primary]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ mem)
  · rw [List.getD_eq_default _ _ (by simpa [primary] using Nat.le_of_not_gt hb)]
    exact .inl rfl

lemma take_read (gs : List Gate) (w : List W) (j i : ℕ)
    (hi : i < (runW (gs.take j) w).length) :
    (runW (gs.take j) w).getD i 0 = (runW gs w).getD i 0 := by
  have eq : runW gs w = runW (gs.drop j) (runW (gs.take j) w) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    simp only [runW, List.foldl_append]
  rw [eq, runW_stable _ _ _ hi]

lemma two_inputs (g : Gate) (hg : legal g) (h0 : 0 ∈ g.inputs) (h9 : 9 ∈ g.inputs) :
    g.inputs = [0,9] ∨ g.inputs = [9,0] := by
  obtain ⟨op,args⟩ := g
  have cap : args.length ≤ 2 := hg.2
  rcases args with _|⟨a,_|⟨b,_|⟨c,tail⟩⟩⟩ <;> simp_all <;> omega

lemma special_value (gs : List Gate) (hlen : gs.length = 10)
    (hop : (gs.getD 6 emptyGate).op = .or)
    (hargs : (gs.getD 6 emptyGate).inputs = [0,9] ∨
      (gs.getD 6 emptyGate).inputs = [9,0]) :
    atGate gs 6 = (primary.getD 0 0 ||| atGate gs 2) := by
  have read0 : (runW (gs.take 6) primary).getD 0 0 = primary.getD 0 0 :=
    runW_stable _ _ _ (by decide)
  have read9 : (runW (gs.take 6) primary).getD 9 0 = atGate gs 2 := by
    rw [take_read gs primary 6 9 (by simp [runW_length, primary, hlen])]
    exact atGate_read gs 2 (by omega)
  unfold atGate at *
  rcases hargs with ha | ha <;>
    simp only [action, hop, ha, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      read0, read9, show ∀ a : W, a ||| (0 : W) = a from fun a => BitVec.or_zero]
  first | rfl | exact BitVec.or_comm _ _

def gratis (early : Bool) (j : ℕ) : Bool :=
  (j == 6) || (j == 2) || (early && decide (j < 2))

def cost (free : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | p, n+1 => cost free (p+1) n + if free p then 0 else 1

lemma price_length (free : ℕ → Bool) (gs : List Gate) (p : ℕ) :
    price free p gs = cost free p gs.length := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih => simp [price, cost, ih]

lemma compile_special (gs : List Gate) (out : ℕ) (hlen : gs.length = 10) (hout : out ≠ 0)
    (hg : ∀ g ∈ gs, legal g)
    (hr : ∀ j < gs.length, j ≠ 6 → 0 ∉ (gs.getD j emptyGate).inputs)
    (hop : atGate gs 6 = (primary.getD 0 0 ||| atGate gs 2))
    (he : (runW gs primary).getD out 0 = ~~~goal) (early : Bool) (extra : List W)
    (hEarly : early = true → holds (sources (atGate gs 2) extra).toFinset (atGate gs 0) ∧
      holds (sources (atGate gs 2) extra).toFinset (atGate gs 1)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧
      build basicOps t (if early then 6 else 8) (sources (atGate gs 2) extra).toFinset := by
  let u := atGate gs 2
  let available := (sources u extra).toFinset
  have hf : ∀ j < gs.length, gratis early (0+j) = true → holds available (atGate gs j) := by
    intro j hj h
    simp [gratis] at h
    rcases h with (rfl | rfl) | ⟨hEarly',hj'⟩
    · rw [hop]
      apply source_holds
      exact List.mem_cons_self ..
    · apply source_holds
      simp [seedValues, u]
    · interval_cases j
      · exact (hEarly hEarly').1
      · exact (hEarly hEarly').2
  have hfree : ∀ v, gratis early v ≠ true → v ≠ 6 := by
    intro v hv eq
    subst v
    exact hv (by simp [gratis])
  obtain ⟨t, ht, hb⟩ := compile_free (gratis early) gs 0 out primary available hfree hg hout
    (initial_holds u extra) (by simpa using hr) hf he
  rw [price_length, hlen] at hb
  have e : cost (gratis early) 0 10 = if early then 6 else 8 := by cases early <;> decide
  rw [e] at hb
  exact ⟨t, ht, hb⟩

lemma checked_refutes (m : ℕ) (u : W) (extra : List W)
    (chk : checkReach m (sources u extra) = true) (t : W)
    (ht : t = goal ∨ t = ~~~goal)
    (hb : build basicOps t (m+1) (sources u extra).toFinset) : False := by
  simp only [checkReach, Bool.and_eq_true] at chk
  exact refute m (sources u extra) (List.nodup_dedup _) chk.1 chk.2 t ht hb


lemma bucket_valid {α : Type} [BEq α] [LawfulBEq α] (buckets : List (List α)) (p : α → Bool)
    (hv : buckets.all (fun b => b.all p) = true) (i : ℕ) (v : α)
    (hm : (buckets.getD i []).contains v = true) : p v = true := by
  have mem := List.contains_iff_mem.mp hm
  by_cases hi : i < buckets.length
  · have hb : buckets.getD i [] ∈ buckets := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    exact List.all_eq_true.mp (List.all_eq_true.mp hv _ hb) _ mem
  · rw [List.getD_eq_default _ _ (by omega)] at mem
    simp at mem

def extrasFor (t : ℕ × ℕ × ℕ) : List W :=
  [BitVec.ofNat 184 t.2.1, BitVec.ofNat 184 t.2.2]

lemma extras_include (u a b : W) :
    canonical a ∈ extrasFor (pairKey u.toNat a.toNat b.toNat) ∧
      canonical b ∈ extrasFor (pairKey u.toNat a.toNat b.toNat) := by
  unfold extrasFor pairKey canonical
  dsimp only
  rcases le_total (canonicalN a.toNat) (canonicalN b.toNat) with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h]

lemma classified (a b u : ℕ) (ha : a ∈ gateValues initialN)
    (hb : b ∈ gateValues (initialN ++ [a]))
    (hu : u ∈ gateValues (initialN ++ [a,b])) (hg : goodMask u = true)
    (cert : (gateValues initialN).all verifyPrefix = true) :
    shortMember u = true ∨ longMember (pairKey u a b) = true := by
  have ea := List.all_eq_true.mp cert a ha
  simp only [verifyPrefix, frc_eq] at ea
  have eb := List.all_eq_true.mp ea b hb
  have hraw : u ∈ rawGateValues (initialN ++ [a,b]) := List.mem_dedup.mp hu
  have eu := List.all_eq_true.mp eb u hraw
  simpa [hg] using eu

set_option maxRecDepth 10000 in
lemma impossible (gs : List Gate) (out : ℕ) (hlen : gs.length = 10)
    (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x)
    (hr : ∀ j < gs.length, 0 ∈ (gs.getD j emptyGate).inputs →
      j = 6 ∧ (gs.getD j emptyGate).op = .or ∧ 9 ∈ (gs.getD j emptyGate).inputs)
    (hop : (gs.getD 6 emptyGate).op = .or)
    (hargs : (gs.getD 6 emptyGate).inputs = [0,9] ∨
      (gs.getD 6 emptyGate).inputs = [9,0])
    (x : Fin 7 → Bool) (h0 : x 0 = false) (h1 : x 1 = false) (h6 : x 6 = false)
    (hx : (Circuit.wires ⟨gs,out⟩ (List.ofFn x)).getD 9 false = true)
    (certPrefix : (gateValues initialN).all verifyPrefix = true)
    (certShort : shortBuckets.all (fun b => b.all checkShort) = true)
    (certLong : longBuckets.all (fun b => b.all checkLong) = true) : False := by
  let a := atGate gs 0
  let b := atGate gs 1
  let u := atGate gs 2
  have hv := vectors_compute gs out hg he
  have hn : out ≠ 0 := by
    intro e
    subst out
    rw [runW_stable _ _ _ (by decide)] at hv
    exact (by decide : primary.getD 0 0 ≠ ~~~goal) hv
  have hnoread : ∀ j < gs.length, j ≠ 6 → 0 ∉ (gs.getD j emptyGate).inputs :=
    fun j hj hne hm => hne (hr j hj hm).1
  have horValue := special_value gs hlen hop hargs
  obtain ⟨ha,hb,hu⟩ := prefix_values gs hlen hg hnoread
  have hgood := mask_good gs out hlen hn hg he hr x h0 h1 h6 hx
  rcases classified a.toNat b.toNat u.toNat ha hb hu hgood certPrefix with hs | hl
  · have check := bucket_valid shortBuckets checkShort certShort _ _ hs
    have hs' : checkReach 7 (sources u []) = true := by
      simpa only [checkShort, BitVec.ofNat_toNat, BitVec.setWidth_eq] using check
    obtain ⟨t,ht,hrun⟩ := compile_special gs out hlen hn hg hnoread horValue hv false []
      (by simp)
    exact checked_refutes 7 u [] hs' t ht hrun
  · let t := pairKey u.toNat a.toNat b.toNat
    let extra := extrasFor t
    have check := bucket_valid longBuckets checkLong certLong _ _ hl
    have hl' : checkReach 5 (sources u extra) = true := by
      simp only [checkLong] at check
      change checkReach 5 (sources (BitVec.ofNat 184 u.toNat) extra) = true at check
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using check
    have hm := extras_include u a b
    have hEarly : true = true → holds (sources u extra).toFinset a ∧
        holds (sources u extra).toFinset b := by
      intro _
      exact ⟨canonical_source u a extra (by simp [seedValues, hm.1, extra, t]),
        canonical_source u b extra (by simp [seedValues, hm.2, extra, t])⟩
    obtain ⟨v,hv',hrun⟩ := compile_special gs out hlen hn hg hnoread horValue hv true extra hEarly
    exact checked_refutes 5 u extra hl' v hv' hrun


set_option maxRecDepth 10000 in
lemma refute_gap
    (certPrefix : (gateValues initialN).all verifyPrefix = true)
    (certShort : shortBuckets.all (fun b => b.all checkShort) = true)
    (certLong : longBuckets.all (fun b => b.all checkLong) = true) :
    ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 6 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 9 ∈ (C.gates.get i).inputs ∧ 9 ≠ 0 ∧ 9 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 9 false = true) := by
  rintro ⟨⟨gs,out⟩, i, k, hi, hfan, hsize, he, h0, honly, hop, _, _, _, h9, _, _,
    x, hx0, hx1, hx6, hx⟩
  have hlen : gs.length = 10 := hsize
  have hg : ∀ g ∈ gs, legal g := by
    intro g hm
    obtain ⟨ops, len⟩ := hfan g hm
    exact ⟨by simpa using ops, len⟩
  have getEq (j : Fin gs.length) : gs.get j = gs.getD j.val emptyGate := by
    simp only [List.get_eq_getElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem j.isLt, Option.getD_some]
  have hiG : gs.get i = gs.getD 6 emptyGate := by rw [getEq, hi]
  change 0 ∈ (gs.get i).inputs at h0
  change (gs.get i).op = _ at hop
  change 9 ∈ (gs.get i).inputs at h9
  have hr : ∀ j < gs.length, 0 ∈ (gs.getD j emptyGate).inputs →
      j = 6 ∧ (gs.getD j emptyGate).op = .or ∧ 9 ∈ (gs.getD j emptyGate).inputs := by
    intro j hj hm
    have e := honly ⟨j,hj⟩ (by rwa [getEq])
    have hv := congrArg Fin.val e
    change j = i.val at hv
    refine ⟨hv.trans hi, ?_, ?_⟩
    · rw [← getEq ⟨j,hj⟩, e]
      exact hop
    · rw [← getEq ⟨j,hj⟩, e]
      exact h9
  have hlg : legal (gs.getD 6 emptyGate) := by
    rw [← hiG]
    exact hg _ (List.get_mem ..)
  rw [hiG] at h0 hop h9
  exact impossible gs out hlen hg he hr hop (two_inputs _ hlg h0 h9)
    x hx0 hx1 hx6 hx certPrefix certShort certLong

def prefixCase0 := ((gateValues initialN).drop 0).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma prefixBlock0 : prefixCase0.all (verifyPrefix) = true := by
  have h11 : (prefixCase0.drop 11).all (verifyPrefix) = true := by
    decide +kernel
  have h10 := all_chunk (verifyPrefix) prefixCase0 10 1 (by decide +kernel) h11
  have h9 := all_chunk (verifyPrefix) prefixCase0 9 1 (by decide +kernel) h10
  have h8 := all_chunk (verifyPrefix) prefixCase0 8 1 (by decide +kernel) h9
  have h7 := all_chunk (verifyPrefix) prefixCase0 7 1 (by decide +kernel) h8
  have h6 := all_chunk (verifyPrefix) prefixCase0 6 1 (by decide +kernel) h7
  have h5 := all_chunk (verifyPrefix) prefixCase0 5 1 (by decide +kernel) h6
  have h4 := all_chunk (verifyPrefix) prefixCase0 4 1 (by decide +kernel) h5
  have h3 := all_chunk (verifyPrefix) prefixCase0 3 1 (by decide +kernel) h4
  have h2 := all_chunk (verifyPrefix) prefixCase0 2 1 (by decide +kernel) h3
  have h1 := all_chunk (verifyPrefix) prefixCase0 1 1 (by decide +kernel) h2
  have h0 := all_chunk (verifyPrefix) prefixCase0 0 1 (by decide +kernel) h1
  exact h0

def prefixCase11 := ((gateValues initialN).drop 11).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma prefixBlock11 : prefixCase11.all (verifyPrefix) = true := by
  have h11 : (prefixCase11.drop 11).all (verifyPrefix) = true := by
    decide +kernel
  have h10 := all_chunk (verifyPrefix) prefixCase11 10 1 (by decide +kernel) h11
  have h9 := all_chunk (verifyPrefix) prefixCase11 9 1 (by decide +kernel) h10
  have h8 := all_chunk (verifyPrefix) prefixCase11 8 1 (by decide +kernel) h9
  have h7 := all_chunk (verifyPrefix) prefixCase11 7 1 (by decide +kernel) h8
  have h6 := all_chunk (verifyPrefix) prefixCase11 6 1 (by decide +kernel) h7
  have h5 := all_chunk (verifyPrefix) prefixCase11 5 1 (by decide +kernel) h6
  have h4 := all_chunk (verifyPrefix) prefixCase11 4 1 (by decide +kernel) h5
  have h3 := all_chunk (verifyPrefix) prefixCase11 3 1 (by decide +kernel) h4
  have h2 := all_chunk (verifyPrefix) prefixCase11 2 1 (by decide +kernel) h3
  have h1 := all_chunk (verifyPrefix) prefixCase11 1 1 (by decide +kernel) h2
  have h0 := all_chunk (verifyPrefix) prefixCase11 0 1 (by decide +kernel) h1
  exact h0

def prefixCase22 := ((gateValues initialN).drop 22).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma prefixBlock22 : prefixCase22.all (verifyPrefix) = true := by
  have h11 : (prefixCase22.drop 11).all (verifyPrefix) = true := by
    decide +kernel
  have h10 := all_chunk (verifyPrefix) prefixCase22 10 1 (by decide +kernel) h11
  have h9 := all_chunk (verifyPrefix) prefixCase22 9 1 (by decide +kernel) h10
  have h8 := all_chunk (verifyPrefix) prefixCase22 8 1 (by decide +kernel) h9
  have h7 := all_chunk (verifyPrefix) prefixCase22 7 1 (by decide +kernel) h8
  have h6 := all_chunk (verifyPrefix) prefixCase22 6 1 (by decide +kernel) h7
  have h5 := all_chunk (verifyPrefix) prefixCase22 5 1 (by decide +kernel) h6
  have h4 := all_chunk (verifyPrefix) prefixCase22 4 1 (by decide +kernel) h5
  have h3 := all_chunk (verifyPrefix) prefixCase22 3 1 (by decide +kernel) h4
  have h2 := all_chunk (verifyPrefix) prefixCase22 2 1 (by decide +kernel) h3
  have h1 := all_chunk (verifyPrefix) prefixCase22 1 1 (by decide +kernel) h2
  have h0 := all_chunk (verifyPrefix) prefixCase22 0 1 (by decide +kernel) h1
  exact h0

def prefixCase33 := ((gateValues initialN).drop 33).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma prefixBlock33 : prefixCase33.all (verifyPrefix) = true := by
  have h11 : (prefixCase33.drop 11).all (verifyPrefix) = true := by
    decide +kernel
  have h10 := all_chunk (verifyPrefix) prefixCase33 10 1 (by decide +kernel) h11
  have h9 := all_chunk (verifyPrefix) prefixCase33 9 1 (by decide +kernel) h10
  have h8 := all_chunk (verifyPrefix) prefixCase33 8 1 (by decide +kernel) h9
  have h7 := all_chunk (verifyPrefix) prefixCase33 7 1 (by decide +kernel) h8
  have h6 := all_chunk (verifyPrefix) prefixCase33 6 1 (by decide +kernel) h7
  have h5 := all_chunk (verifyPrefix) prefixCase33 5 1 (by decide +kernel) h6
  have h4 := all_chunk (verifyPrefix) prefixCase33 4 1 (by decide +kernel) h5
  have h3 := all_chunk (verifyPrefix) prefixCase33 3 1 (by decide +kernel) h4
  have h2 := all_chunk (verifyPrefix) prefixCase33 2 1 (by decide +kernel) h3
  have h1 := all_chunk (verifyPrefix) prefixCase33 1 1 (by decide +kernel) h2
  have h0 := all_chunk (verifyPrefix) prefixCase33 0 1 (by decide +kernel) h1
  exact h0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma prefix_checked : (gateValues initialN).all (verifyPrefix) = true := by
  have h44 : ((gateValues initialN).drop 44).all (verifyPrefix) = true := by
    decide +kernel
  have h33 := all_chunk (verifyPrefix) (gateValues initialN) 33 11 (by simpa only [prefixCase33] using prefixBlock33) h44
  have h22 := all_chunk (verifyPrefix) (gateValues initialN) 22 11 (by simpa only [prefixCase22] using prefixBlock22) h33
  have h11 := all_chunk (verifyPrefix) (gateValues initialN) 11 11 (by simpa only [prefixCase11] using prefixBlock11) h22
  have h0 := all_chunk (verifyPrefix) (gateValues initialN) 0 11 (by simpa only [prefixCase0] using prefixBlock0) h11
  exact h0

def shortCase0 := ((shortBuckets).drop 0).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma shortBlock0 : shortCase0.all (fun b => b.all checkShort) = true := by
  have h11 : (shortCase0.drop 11).all (fun b => b.all checkShort) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkShort) shortCase0 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkShort) shortCase0 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkShort) shortCase0 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkShort) shortCase0 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkShort) shortCase0 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkShort) shortCase0 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkShort) shortCase0 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkShort) shortCase0 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkShort) shortCase0 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkShort) shortCase0 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkShort) shortCase0 0 1 (by decide +kernel) h1
  exact h0

def shortCase11 := ((shortBuckets).drop 11).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma shortBlock11 : shortCase11.all (fun b => b.all checkShort) = true := by
  have h11 : (shortCase11.drop 11).all (fun b => b.all checkShort) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkShort) shortCase11 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkShort) shortCase11 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkShort) shortCase11 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkShort) shortCase11 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkShort) shortCase11 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkShort) shortCase11 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkShort) shortCase11 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkShort) shortCase11 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkShort) shortCase11 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkShort) shortCase11 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkShort) shortCase11 0 1 (by decide +kernel) h1
  exact h0

def shortCase22 := ((shortBuckets).drop 22).take 9

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma shortBlock22 : shortCase22.all (fun b => b.all checkShort) = true := by
  have h9 : (shortCase22.drop 9).all (fun b => b.all checkShort) = true := by
    decide +kernel
  have h8 := all_chunk (fun b => b.all checkShort) shortCase22 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkShort) shortCase22 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkShort) shortCase22 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkShort) shortCase22 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkShort) shortCase22 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkShort) shortCase22 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkShort) shortCase22 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkShort) shortCase22 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkShort) shortCase22 0 1 (by decide +kernel) h1
  exact h0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma short_checked : (shortBuckets).all (fun b => b.all checkShort) = true := by
  have h31 : ((shortBuckets).drop 31).all (fun b => b.all checkShort) = true := by
    decide +kernel
  have h22 := all_chunk (fun b => b.all checkShort) (shortBuckets) 22 9 (by simpa only [shortCase22] using shortBlock22) h31
  have h11 := all_chunk (fun b => b.all checkShort) (shortBuckets) 11 11 (by simpa only [shortCase11] using shortBlock11) h22
  have h0 := all_chunk (fun b => b.all checkShort) (shortBuckets) 0 11 (by simpa only [shortCase0] using shortBlock0) h11
  exact h0

def longCase0 := ((longBuckets).drop 0).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma longBlock0 : longCase0.all (fun b => b.all checkLong) = true := by
  have h11 : (longCase0.drop 11).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkLong) longCase0 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkLong) longCase0 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkLong) longCase0 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkLong) longCase0 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkLong) longCase0 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkLong) longCase0 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkLong) longCase0 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkLong) longCase0 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkLong) longCase0 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkLong) longCase0 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkLong) longCase0 0 1 (by decide +kernel) h1
  exact h0

def longCase11 := ((longBuckets).drop 11).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma longBlock11 : longCase11.all (fun b => b.all checkLong) = true := by
  have h11 : (longCase11.drop 11).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkLong) longCase11 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkLong) longCase11 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkLong) longCase11 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkLong) longCase11 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkLong) longCase11 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkLong) longCase11 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkLong) longCase11 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkLong) longCase11 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkLong) longCase11 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkLong) longCase11 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkLong) longCase11 0 1 (by decide +kernel) h1
  exact h0

def longCase22 := ((longBuckets).drop 22).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma longBlock22 : longCase22.all (fun b => b.all checkLong) = true := by
  have h11 : (longCase22.drop 11).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkLong) longCase22 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkLong) longCase22 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkLong) longCase22 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkLong) longCase22 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkLong) longCase22 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkLong) longCase22 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkLong) longCase22 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkLong) longCase22 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkLong) longCase22 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkLong) longCase22 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkLong) longCase22 0 1 (by decide +kernel) h1
  exact h0

def longCase33 := ((longBuckets).drop 33).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma longBlock33 : longCase33.all (fun b => b.all checkLong) = true := by
  have h11 : (longCase33.drop 11).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkLong) longCase33 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkLong) longCase33 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkLong) longCase33 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkLong) longCase33 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkLong) longCase33 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkLong) longCase33 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkLong) longCase33 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkLong) longCase33 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkLong) longCase33 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkLong) longCase33 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkLong) longCase33 0 1 (by decide +kernel) h1
  exact h0

def longCase44 := ((longBuckets).drop 44).take 11

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma longBlock44 : longCase44.all (fun b => b.all checkLong) = true := by
  have h11 : (longCase44.drop 11).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h10 := all_chunk (fun b => b.all checkLong) longCase44 10 1 (by decide +kernel) h11
  have h9 := all_chunk (fun b => b.all checkLong) longCase44 9 1 (by decide +kernel) h10
  have h8 := all_chunk (fun b => b.all checkLong) longCase44 8 1 (by decide +kernel) h9
  have h7 := all_chunk (fun b => b.all checkLong) longCase44 7 1 (by decide +kernel) h8
  have h6 := all_chunk (fun b => b.all checkLong) longCase44 6 1 (by decide +kernel) h7
  have h5 := all_chunk (fun b => b.all checkLong) longCase44 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkLong) longCase44 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkLong) longCase44 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkLong) longCase44 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkLong) longCase44 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkLong) longCase44 0 1 (by decide +kernel) h1
  exact h0

def longCase55 := ((longBuckets).drop 55).take 6

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma longBlock55 : longCase55.all (fun b => b.all checkLong) = true := by
  have h6 : (longCase55.drop 6).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h5 := all_chunk (fun b => b.all checkLong) longCase55 5 1 (by decide +kernel) h6
  have h4 := all_chunk (fun b => b.all checkLong) longCase55 4 1 (by decide +kernel) h5
  have h3 := all_chunk (fun b => b.all checkLong) longCase55 3 1 (by decide +kernel) h4
  have h2 := all_chunk (fun b => b.all checkLong) longCase55 2 1 (by decide +kernel) h3
  have h1 := all_chunk (fun b => b.all checkLong) longCase55 1 1 (by decide +kernel) h2
  have h0 := all_chunk (fun b => b.all checkLong) longCase55 0 1 (by decide +kernel) h1
  exact h0

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma long_checked : (longBuckets).all (fun b => b.all checkLong) = true := by
  have h61 : ((longBuckets).drop 61).all (fun b => b.all checkLong) = true := by
    decide +kernel
  have h55 := all_chunk (fun b => b.all checkLong) (longBuckets) 55 6 (by simpa only [longCase55] using longBlock55) h61
  have h44 := all_chunk (fun b => b.all checkLong) (longBuckets) 44 11 (by simpa only [longCase44] using longBlock44) h55
  have h33 := all_chunk (fun b => b.all checkLong) (longBuckets) 33 11 (by simpa only [longCase33] using longBlock33) h44
  have h22 := all_chunk (fun b => b.all checkLong) (longBuckets) 22 11 (by simpa only [longCase22] using longBlock22) h33
  have h11 := all_chunk (fun b => b.all checkLong) (longBuckets) 11 11 (by simpa only [longCase11] using longBlock11) h22
  have h0 := all_chunk (fun b => b.all checkLong) (longBuckets) 0 11 (by simpa only [longCase0] using longBlock0) h11
  exact h0

end PEqualNP.Outside.L_meta_29874

open PEqualNP.Outside.L_meta_29874

theorem PEqualNP.Outside.L_meta_29874 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 6 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 9 ∈ (C.gates.get i).inputs ∧ 9 ≠ 0 ∧ 9 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 9 false = true) := by
  exact refute_gap prefix_checked short_checked long_checked
