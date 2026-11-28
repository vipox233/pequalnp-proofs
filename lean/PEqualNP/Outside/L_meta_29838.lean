import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29838.PrefixCertificate

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

abbrev W := BitVec 214

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 107 := ((x >>> 107) ^^^ x).setWidth 107
def cuts (ws : List W) : BitVec 107 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 107) ++ (0 : BitVec 107)
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

def differs (i : Fin 107) (w : W) : Prop :=
  w.getLsbD (107+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 107) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 107+i.val < 214 := by omega
  have hi' : i.val < 214 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 107) :
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
  change (cuts ws)[j] = (BitVec.allOnes 107)[j]
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

def M120 : ℕ := 2 ^ 214 - 1
def M60 : ℕ := 2 ^ 107 - 1
def P60 : ℕ := 2 ^ 107
def gN : ℕ := (2 ^ 107 - 1) * 2 ^ 107

def nsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 107) x) P60

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
      ((opsN a b).flatMap (kids0 base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

theorem pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      ((opsN a b).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  unfold pairG opsN
  simp only [orB_eq, oneG_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
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

theorem negOne60 : (-1 : BitVec 107).toNat = M60 := by decide

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

def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (ncuts ws) M60)

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
  · change reachable av (BitVec.allOnes 214 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 214)
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

private def bit (k : Fin 214) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 214) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 214) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#214)[k.val] = false; simp
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
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def inputs : List W := [((259711777799 * 2 ^ 64 + 9497555300359147794) * 2 ^ 64 + 10344488962922445255), (((3 * 2 ^ 64 + 14375617279045402744) * 2 ^ 64 + 2017718434103095342) * 2 ^ 64 + 8683255781515298909), (((35004 * 2 ^ 64 + 2111064464441216) * 2 ^ 64 + 4368652955558644) * 2 ^ 64 + 1233970938861655032), (((65792 * 2 ^ 64 + 574213348388765696) * 2 ^ 64 + 2301346308413390656) * 2 ^ 64 + 9219466576454483616), (((3135 * 2 ^ 64 + 17870283321406144511) * 2 ^ 64 + 16140909336737039360) * 2 ^ 64 + 2460166406839084032), (((114688 * 2 ^ 64 + 4398046494720) * 2 ^ 64 + 8521286715529) * 2 ^ 64 + 9223372012297650176), (((63 * 2 ^ 64 + 18446739675663040512) * 2 ^ 64 + 134217727) * 2 ^ 64 + 14143704799001985282)]
def witnessMask : W := (((4194240 * 2 ^ 64 + 15158264704) * 2 ^ 64 + 6931470587046920192) * 2 ^ 64 + 13616387969517088)

def targetFun (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def sample (k : Fin 214) (i : Fin 7) : Bool := bit k (inputs.getD i.val 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sample_rows : ∀ k, targetFun (sample k) = bit k (~~~goal) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sample_witness : ∀ x : Fin 7 → Bool,
    x 0 = false → x 1 = false → x 6 = false →
      ∃ k : Fin 214, sample k = x ∧ bit k witnessMask = true := by
  decide +kernel

def choices (av : List W) : List W :=
  ([0, ~~~0] ++ av ++ av.map (fun a => ~~~a) ++
    av.flatMap (fun a => av.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

def base : List W := inputs.tail
def available (a b : W) : List W :=
  (base ++ [a, b, inputs.getD 0 0 ||| b]).dedup

def viable (a b : W) : Bool :=
  decide (b &&& witnessMask ≠ 0) && decide (cuts (available a b) = -1)

def prefixes : List (W × W) :=
  (choices base).flatMap fun a =>
    ((choices (base ++ [a])).filter (viable a)).map fun b => (a,b)

def certificate (p : W × W) : Bool :=
  let ins := (available p.1 p.2).map BitVec.toNat
  (rootsN 7 ins).all (fun ws => !nisGoal ws) && (allKids 6 ins).all (dead 6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def firstChoices : List W := [0,(((4194303 * 2 ^ 64 + 18446744073709551615) * 2 ^ 64 + 18446744073709551615) * 2 ^ 64 + 18446744073709551615),(((3 * 2 ^ 64 + 14375617279045402744) * 2 ^ 64 + 2017718434103095342) * 2 ^ 64 + 8683255781515298909),(((35004 * 2 ^ 64 + 2111064464441216) * 2 ^ 64 + 4368652955558644) * 2 ^ 64 + 1233970938861655032),(((65792 * 2 ^ 64 + 574213348388765696) * 2 ^ 64 + 2301346308413390656) * 2 ^ 64 + 9219466576454483616),(((3135 * 2 ^ 64 + 17870283321406144511) * 2 ^ 64 + 16140909336737039360) * 2 ^ 64 + 2460166406839084032),(((114688 * 2 ^ 64 + 4398046494720) * 2 ^ 64 + 8521286715529) * 2 ^ 64 + 9223372012297650176),(((63 * 2 ^ 64 + 18446739675663040512) * 2 ^ 64 + 134217727) * 2 ^ 64 + 14143704799001985282),(((4194300 * 2 ^ 64 + 4071126794664148871) * 2 ^ 64 + 16429025639606456273) * 2 ^ 64 + 9763488292194252706),(((4159299 * 2 ^ 64 + 18444633009245110399) * 2 ^ 64 + 18442375420753992971) * 2 ^ 64 + 17212773134847896583),(((4128511 * 2 ^ 64 + 17872530725320785919) * 2 ^ 64 + 16145397765296160959) * 2 ^ 64 + 9227277497255067999),(((4191168 * 2 ^ 64 + 576460752303407104) * 2 ^ 64 + 2305834736972512255) * 2 ^ 64 + 15986577666870467583),(((4079615 * 2 ^ 64 + 18446739675663056895) * 2 ^ 64 + 18446735552422836086) * 2 ^ 64 + 9223372061411901439),(((4194240 * 2 ^ 64 + 4398046511103) * 2 ^ 64 + 18446744073575333888) * 2 ^ 64 + 4303039274707566333),(17834020 * 2 ^ 64 + 1153222773242396760),(((35007 * 2 ^ 64 + 14377728343509843960) * 2 ^ 64 + 2022087087040819966) * 2 ^ 64 + 8764003947134557181),((540436078453063680 * 2 ^ 64 + 2017612633064140800) * 2 ^ 64 + 8682940081637656576),(((65795 * 2 ^ 64 + 14409394548981104760) * 2 ^ 64 + 2301452109452345198) * 2 ^ 64 + 9219782276332125949),(((3 * 2 ^ 64 + 13835058055282163832) * 2 ^ 64 + 24657920) * 2 ^ 64 + 2305847409928962048),(((3135 * 2 ^ 64 + 18410842545169383423) * 2 ^ 64 + 18158627770815476782) * 2 ^ 64 + 8837574778425420893),((4123176468480 * 2 ^ 64 + 4227080) * 2 ^ 64 + 8683255778980659200),(((114691 * 2 ^ 64 + 14375617553915428984) * 2 ^ 64 + 2017726955385583791) * 2 ^ 64 + 9223372014832289885),(((3 * 2 ^ 64 + 14375613155868934144) * 2 ^ 64 + 24703022) * 2 ^ 64 + 4611694814520410112),(((63 * 2 ^ 64 + 18446743798839509112) * 2 ^ 64 + 2017718434212610047) * 2 ^ 64 + 18215265765996874079),(4691211592256 * 2 ^ 64 + 1230080837429564064),(((100796 * 2 ^ 64 + 576324412853206912) * 2 ^ 64 + 2305710270157357044) * 2 ^ 64 + 9223356677886574584),(((2108 * 2 ^ 64 + 16256) * 2 ^ 64 + 5514864885760) * 2 ^ 64 + 1196302775877632),(((36031 * 2 ^ 64 + 17872394385870569471) * 2 ^ 64 + 16145272474827712244) * 2 ^ 64 + 3692941042924861432),(((32768 * 2 ^ 64 + 2139095040) * 2 ^ 64 + 5772503154816) * 2 ^ 64 + 1233970914400403456),(((116924 * 2 ^ 64 + 2115460371840896) * 2 ^ 64 + 4371401739119357) * 2 ^ 64 + 9223372036758901752),(((60 * 2 ^ 64 + 2111062325329920) * 2 ^ 64 + 126886644) * 2 ^ 64 + 2392554481910016),(((35007 * 2 ^ 64 + 18446739677802151808) * 2 ^ 64 + 4368652962889727) * 2 ^ 64 + 15375283183381730298),(6622875370496 * 2 ^ 64 + 2458965401445737472),(((68927 * 2 ^ 64 + 18444496669794910207) * 2 ^ 64 + 18442249022275059520) * 2 ^ 64 + 9220667581847830176),(((65536 * 2 ^ 64 + 4395899027456) * 2 ^ 64 + 6871947708416) * 2 ^ 64 + 9219466571552915456),(((114944 * 2 ^ 64 + 574213350536232960) * 2 ^ 64 + 2301347957752397769) * 2 ^ 64 + 9223372017199218336),((574208952489738240 * 2 ^ 64 + 35848000) * 2 ^ 64 + 4917930793088598016),(((65855 * 2 ^ 64 + 18446744071562067968) * 2 ^ 64 + 2301346308511760383) * 2 ^ 64 + 18445240582367870882),(8246408773632 * 2 ^ 64 + 2460166382282080256),(((117823 * 2 ^ 64 + 17870287719452639231) * 2 ^ 64 + 16140909611614981257) * 2 ^ 64 + 9223372036854653952),(((63 * 2 ^ 64 + 17870283321406128128) * 2 ^ 64 + 134169600) * 2 ^ 64 + 17188257792),(((3135 * 2 ^ 64 + 18446739675663056895) * 2 ^ 64 + 16140909336737087487) * 2 ^ 64 + 16603871188652811522),(71600265 * 2 ^ 64 + 4920332744958935040),(((114751 * 2 ^ 64 + 18446744073709535232) * 2 ^ 64 + 8521349332991) * 2 ^ 64 + 18446744066340700418)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem firstChoices_eq : choices base = firstChoices := by decide +kernel

def firstCert (a : W) : Bool :=
  (((choices (base ++ [a])).filter (viable a)).map fun b => (a,b)).all certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_0 : firstCert (0 : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_1 : firstCert ((((4194303 * 2 ^ 64 + 18446744073709551615) * 2 ^ 64 + 18446744073709551615) * 2 ^ 64 + 18446744073709551615) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_2 : firstCert ((((3 * 2 ^ 64 + 14375617279045402744) * 2 ^ 64 + 2017718434103095342) * 2 ^ 64 + 8683255781515298909) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3 : firstCert ((((35004 * 2 ^ 64 + 2111064464441216) * 2 ^ 64 + 4368652955558644) * 2 ^ 64 + 1233970938861655032) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_4 : firstCert ((((65792 * 2 ^ 64 + 574213348388765696) * 2 ^ 64 + 2301346308413390656) * 2 ^ 64 + 9219466576454483616) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_5 : firstCert ((((3135 * 2 ^ 64 + 17870283321406144511) * 2 ^ 64 + 16140909336737039360) * 2 ^ 64 + 2460166406839084032) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_6 : firstCert ((((114688 * 2 ^ 64 + 4398046494720) * 2 ^ 64 + 8521286715529) * 2 ^ 64 + 9223372012297650176) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_7 : firstCert ((((63 * 2 ^ 64 + 18446739675663040512) * 2 ^ 64 + 134217727) * 2 ^ 64 + 14143704799001985282) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_8 : firstCert ((((4194300 * 2 ^ 64 + 4071126794664148871) * 2 ^ 64 + 16429025639606456273) * 2 ^ 64 + 9763488292194252706) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_9 : firstCert ((((4159299 * 2 ^ 64 + 18444633009245110399) * 2 ^ 64 + 18442375420753992971) * 2 ^ 64 + 17212773134847896583) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_10 : firstCert ((((4128511 * 2 ^ 64 + 17872530725320785919) * 2 ^ 64 + 16145397765296160959) * 2 ^ 64 + 9227277497255067999) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_11 : firstCert ((((4191168 * 2 ^ 64 + 576460752303407104) * 2 ^ 64 + 2305834736972512255) * 2 ^ 64 + 15986577666870467583) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_12 : firstCert ((((4079615 * 2 ^ 64 + 18446739675663056895) * 2 ^ 64 + 18446735552422836086) * 2 ^ 64 + 9223372061411901439) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_13 : firstCert ((((4194240 * 2 ^ 64 + 4398046511103) * 2 ^ 64 + 18446744073575333888) * 2 ^ 64 + 4303039274707566333) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_14 : firstCert ((17834020 * 2 ^ 64 + 1153222773242396760) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_15 : firstCert ((((35007 * 2 ^ 64 + 14377728343509843960) * 2 ^ 64 + 2022087087040819966) * 2 ^ 64 + 8764003947134557181) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_16 : firstCert (((540436078453063680 * 2 ^ 64 + 2017612633064140800) * 2 ^ 64 + 8682940081637656576) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_17 : firstCert ((((65795 * 2 ^ 64 + 14409394548981104760) * 2 ^ 64 + 2301452109452345198) * 2 ^ 64 + 9219782276332125949) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_18 : firstCert ((((3 * 2 ^ 64 + 13835058055282163832) * 2 ^ 64 + 24657920) * 2 ^ 64 + 2305847409928962048) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_19 : firstCert ((((3135 * 2 ^ 64 + 18410842545169383423) * 2 ^ 64 + 18158627770815476782) * 2 ^ 64 + 8837574778425420893) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_20 : firstCert (((4123176468480 * 2 ^ 64 + 4227080) * 2 ^ 64 + 8683255778980659200) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_21 : firstCert ((((114691 * 2 ^ 64 + 14375617553915428984) * 2 ^ 64 + 2017726955385583791) * 2 ^ 64 + 9223372014832289885) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_22 : firstCert ((((3 * 2 ^ 64 + 14375613155868934144) * 2 ^ 64 + 24703022) * 2 ^ 64 + 4611694814520410112) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_23 : firstCert ((((63 * 2 ^ 64 + 18446743798839509112) * 2 ^ 64 + 2017718434212610047) * 2 ^ 64 + 18215265765996874079) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_24 : firstCert ((4691211592256 * 2 ^ 64 + 1230080837429564064) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_25 : firstCert ((((100796 * 2 ^ 64 + 576324412853206912) * 2 ^ 64 + 2305710270157357044) * 2 ^ 64 + 9223356677886574584) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_26 : firstCert ((((2108 * 2 ^ 64 + 16256) * 2 ^ 64 + 5514864885760) * 2 ^ 64 + 1196302775877632) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_27 : firstCert ((((36031 * 2 ^ 64 + 17872394385870569471) * 2 ^ 64 + 16145272474827712244) * 2 ^ 64 + 3692941042924861432) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_28 : firstCert ((((32768 * 2 ^ 64 + 2139095040) * 2 ^ 64 + 5772503154816) * 2 ^ 64 + 1233970914400403456) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_29 : firstCert ((((116924 * 2 ^ 64 + 2115460371840896) * 2 ^ 64 + 4371401739119357) * 2 ^ 64 + 9223372036758901752) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_30 : firstCert ((((60 * 2 ^ 64 + 2111062325329920) * 2 ^ 64 + 126886644) * 2 ^ 64 + 2392554481910016) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_31 : firstCert ((((35007 * 2 ^ 64 + 18446739677802151808) * 2 ^ 64 + 4368652962889727) * 2 ^ 64 + 15375283183381730298) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_32 : firstCert ((6622875370496 * 2 ^ 64 + 2458965401445737472) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_33 : firstCert ((((68927 * 2 ^ 64 + 18444496669794910207) * 2 ^ 64 + 18442249022275059520) * 2 ^ 64 + 9220667581847830176) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_34 : firstCert ((((65536 * 2 ^ 64 + 4395899027456) * 2 ^ 64 + 6871947708416) * 2 ^ 64 + 9219466571552915456) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_35 : firstCert ((((114944 * 2 ^ 64 + 574213350536232960) * 2 ^ 64 + 2301347957752397769) * 2 ^ 64 + 9223372017199218336) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_36 : firstCert (((574208952489738240 * 2 ^ 64 + 35848000) * 2 ^ 64 + 4917930793088598016) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_37 : firstCert ((((65855 * 2 ^ 64 + 18446744071562067968) * 2 ^ 64 + 2301346308511760383) * 2 ^ 64 + 18445240582367870882) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_38 : firstCert ((8246408773632 * 2 ^ 64 + 2460166382282080256) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_39 : firstCert ((((117823 * 2 ^ 64 + 17870287719452639231) * 2 ^ 64 + 16140909611614981257) * 2 ^ 64 + 9223372036854653952) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_40 : firstCert ((((63 * 2 ^ 64 + 17870283321406128128) * 2 ^ 64 + 134169600) * 2 ^ 64 + 17188257792) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_41 : firstCert ((((3135 * 2 ^ 64 + 18446739675663056895) * 2 ^ 64 + 16140909336737087487) * 2 ^ 64 + 16603871188652811522) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_42 : firstCert ((71600265 * 2 ^ 64 + 4920332744958935040) : W) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_43 : firstCert ((((114751 * 2 ^ 64 + 18446744073709535232) * 2 ^ 64 + 8521349332991) * 2 ^ 64 + 18446744066340700418) : W) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificates : prefixes.all certificate = true := by
  simp only [prefixes, List.all_flatMap, firstChoices_eq]
  change firstChoices.all firstCert = true
  simp only [firstChoices, List.all_cons, List.all_nil, cert_0,cert_1,cert_2,cert_3,cert_4,cert_5,cert_6,cert_7,cert_8,cert_9,cert_10,cert_11,cert_12,cert_13,cert_14,cert_15,cert_16,cert_17,cert_18,cert_19,cert_20,cert_21,cert_22,cert_23,cert_24,cert_25,cert_26,cert_27,cert_28,cert_29,cert_30,cert_31,cert_32,cert_33,cert_34,cert_35,cert_36,cert_37,cert_38,cert_39,cert_40,cert_41,cert_42,cert_43, Bool.and_self]

theorem read_tail {α : Type} (d x : α) (xs : List α) (i : ℕ) (hi : i ≠ 0) :
    (x :: xs).getD i d ∈ d :: xs := by
  cases i with
  | zero => contradiction
  | succ i =>
    simp only [List.getD_cons_succ]
    by_cases h : i < xs.length
    · rw [List.getD_eq_getElem xs d h]
      exact List.mem_cons_of_mem _ (List.getElem_mem h)
    · rw [List.getD_eq_default xs d (n := i) (by omega)]
      exact List.mem_cons_self

theorem choice_const (av : List W) : (0 : W) ∈ choices av ∧ (~~~0 : W) ∈ choices av := by
  simp [choices]

theorem choice_not {av : List W} {a : W} (ha : a ∈ 0 :: av) :
    ~~~a ∈ choices av := by
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact (choice_const av).2
  · simp only [choices, List.mem_eraseDups, List.mem_append]
    exact Or.inl (Or.inr (List.mem_map.mpr ⟨a,ha,rfl⟩))

theorem choice_and {av : List W} {a b : W} (ha : a ∈ 0 :: av) (hb : b ∈ 0 :: av) :
    a &&& b ∈ choices av := by
  rcases List.mem_cons.mp ha with rfl | ha
  · simpa using (choice_const av).1
  rcases List.mem_cons.mp hb with rfl | hb
  · simpa using (choice_const av).1
  simp only [choices, List.mem_eraseDups, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b,hb,by simp⟩⟩)

theorem choice_or {av : List W} {a b : W} (ha : a ∈ 0 :: av) (hb : b ∈ 0 :: av) :
    a ||| b ∈ choices av := by
  rcases List.mem_cons.mp ha with rfl | ha
  · rw [show (0 : W) ||| b = b from BitVec.zero_or]
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (choice_const av).1
    · simp [choices, hb]
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [choices, ha]
  simp only [choices, List.mem_eraseDups, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b,hb,by simp⟩⟩)

theorem choice_read {av : List W} {a : W} (ha : a ∈ 0 :: av) : a ∈ choices av := by
  rcases List.mem_cons.mp ha with rfl | ha
  · exact (choice_const av).1
  · simp [choices,ha]

theorem action_choice (w av : List W) (g : Gate) (hg : legal g)
    (hr : ∀ i ∈ g.inputs, w.getD i 0 ∈ 0 :: av) : action w g ∈ choices av := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,
      List.foldr_cons,Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact (choice_const av).1
    | exact (choice_const av).2
    | exact choice_read (hr i (by simp))
    | exact choice_not (hr i (by simp))
    | exact choice_and (hr i (by simp)) (hr j (by simp))
    | exact choice_or (hr i (by simp)) (hr j (by simp))

theorem pair_inputs (g : Gate) (cap : g.inputs.length ≤ 2)
    (h0 : 0 ∈ g.inputs) (h8 : 8 ∈ g.inputs) :
    g.inputs = [0,8] ∨ g.inputs = [8,0] := by
  obtain ⟨op,args⟩ := g
  rcases args with _|⟨a,_|⟨b,_|⟨c,tail⟩⟩⟩ <;> simp_all <;> omega

theorem action_pair (w : List W) (g : Gate) (cap : g.inputs.length ≤ 2)
    (h0 : 0 ∈ g.inputs) (h8 : 8 ∈ g.inputs) (hop : g.op = .or) :
    action w g = w.getD 0 0 ||| w.getD 8 0 := by
  rcases pair_inputs g cap h0 h8 with h | h <;>
    simp [action,hop,h,BitVec.or_comm]

theorem step_ignore_zero (g : Gate) (hn : 0 ∉ g.inputs) (x y : Bool) (s : List Bool) :
    ∃ t, step (x :: s) g = x :: t ∧ step (y :: s) g = y :: t := by
  have h : g.inputs.map (fun i => (x :: s).getD i false) =
      g.inputs.map (fun i => (y :: s).getD i false) := by
    apply List.map_congr_left
    intro i hi
    cases i with
    | zero => exact False.elim (hn hi)
    | succ i => rfl
  refine ⟨s ++ [g.op.eval (g.inputs.map (fun i => (x :: s).getD i false))], rfl, ?_⟩
  simp only [step, h, List.cons_append]

theorem fold_ignore_zero (gs : List Gate) (hn : ∀ g ∈ gs, 0 ∉ g.inputs)
    (x y : Bool) (s : List Bool) :
    ∃ t, gs.foldl step (x :: s) = x :: t ∧ gs.foldl step (y :: s) = y :: t := by
  induction gs generalizing s with
  | nil => exact ⟨s,rfl,rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,ht'⟩ := step_ignore_zero g (hn g (by simp)) x y s
    obtain ⟨u,hu,hu'⟩ := ih (fun g hg => hn g (by simp [hg])) t
    exact ⟨u,by simpa only [List.foldl_cons,ht], by simpa only [List.foldl_cons,ht']⟩

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨t,ht⟩ := ih (step w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,
      by simpa [step,List.append_assoc] using ht⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem impossible_prefix (a b : W) (ha : a ∈ choices base)
    (hb : b ∈ choices (base ++ [a])) (hw : b &&& witnessMask ≠ 0)
    (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 7 (available a b).toFinset) : False := by
  have hc : cuts (available a b) = -1 := by
    obtain ⟨s,hs,hl⟩ := compress run
    have hs' : ∀ w ∈ s, w ∈ (available a b) := fun w hw =>
      List.mem_toFinset.mp (hs hw)
    apply BitVec.eq_of_getElem_eq
    intro j hj
    have hds : ∀ i, differs i t := by
      rcases ht with rfl | rfl <;> unfold differs <;> decide +kernel
    have hd := hds ⟨j,hj⟩
    obtain ⟨w,hws,hdw⟩ := live_separates (differs ⟨j,hj⟩) hd (ops_differs ⟨j,hj⟩) hl
    have hbit := (cuts_spec (available a b) ⟨j,hj⟩).mpr ⟨w,hs' w hws,hdw⟩
    change (cuts (available a b))[j] = (BitVec.allOnes 107)[j]
    rw [BitVec.getElem_allOnes]
    simpa only [BitVec.getLsbD_eq_getElem hj] using hbit
  have hp : (a,b) ∈ prefixes := by
    apply List.mem_flatMap.mpr
    refine ⟨a,ha,List.mem_map.mpr ⟨b,?_,rfl⟩⟩
    refine List.mem_filter.mpr ⟨hb,?_⟩
    change (decide (b &&& witnessMask ≠ 0) && decide (cuts (available a b) = -1)) = true
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hw,decide_eq_true hc⟩
  have cert := List.all_eq_true.mp certificates (a,b) hp
  change (_ && _) = true at cert
  rw [Bool.and_eq_true] at cert
  obtain ⟨h0,hk⟩ := cert
  exact refute 6 (available a b) (List.nodup_dedup _) h0 hk t ht run

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem main (g0 g1 g2 : Gate) (gs : List Gate) (o : ℕ) (hlen : gs.length = 7)
    (hlegal : ∀ g ∈ g0 :: g1 :: g2 :: gs, legal g)
    (hn0 : 0 ∉ g0.inputs) (hn1 : 0 ∉ g1.inputs) (hngs : ∀ g ∈ gs, 0 ∉ g.inputs)
    (h20 : 0 ∈ g2.inputs) (h28 : 8 ∈ g2.inputs) (h2op : g2.op = .or)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨g0 :: g1 :: g2 :: gs,o⟩ (List.ofFn x) = targetFun x)
    (hwit : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      (Circuit.wires ⟨g0 :: g1 :: g2 :: gs,o⟩ (List.ofFn x)).getD 8 false = true) : False := by
  let a := action inputs g0
  let b := action (inputs ++ [a]) g1
  let y := inputs.getD 0 0 ||| b
  have hg0 := hlegal g0 (by simp)
  have hg1 := hlegal g1 (by simp)
  have hg2 := hlegal g2 (by simp)
  have ha : a ∈ choices base := action_choice inputs base g0 hg0 (by
    intro i hi
    exact read_tail 0 (inputs.getD 0 0) base i (fun h => hn0 (h ▸ hi)))
  have hb : b ∈ choices (base ++ [a]) := action_choice (inputs ++ [a]) (base ++ [a]) g1 hg1 (by
    intro i hi
    exact read_tail 0 (inputs.getD 0 0) (base ++ [a]) i (fun h => hn1 (h ▸ hi)))
  have act2 : action (inputs ++ [a,b]) g2 = y := by
    rw [action_pair _ g2 hg2.2 h20 h28 h2op]
    rfl
  have initial (k : Fin 214) : List.ofFn (sample k) = inputs.map (bit k) := by
    apply List.ext_getElem
    · rfl
    · intro i hi hj
      have hlt : i < inputs.length := by simpa using hj
      simp only [List.getElem_ofFn,List.getElem_map,sample,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt,Option.getD_some]
  have wires_model (k : Fin 214) :
      Circuit.wires ⟨g0 :: g1 :: g2 :: gs,o⟩ (List.ofFn (sample k)) =
        gs.foldl step ((inputs ++ [a,b,y]).map (bit k)) := by
    rw [initial]
    change (g0 :: g1 :: g2 :: gs).foldl step (inputs.map (bit k)) = _
    simp only [List.foldl_cons]
    rw [action_spec inputs g0 hg0 k]
    change gs.foldl step (step (step ((inputs ++ [a]).map (bit k)) g1) g2) = _
    rw [action_spec (inputs ++ [a]) g1 hg1 k]
    change gs.foldl step (step ((inputs ++ [a,b]).map (bit k)) g2) = _
    rw [action_spec (inputs ++ [a,b]) g2 hg2 k,act2]
    rfl
  have evaluate (k : Fin 214) :
      (gs.foldl step ((inputs ++ [a,b,y]).map (bit k))).getD o false = bit k (~~~goal) := by
    rw [← wires_model]
    exact (he (sample k)).trans (sample_rows k)
  have hout : o ≠ 0 := by
    intro h
    subst o
    have bad : ∃ k : Fin 214, bit k (inputs.getD 0 0) ≠ bit k (~~~goal) := by decide +kernel
    obtain ⟨k,hk⟩ := bad
    obtain ⟨t,ht⟩ := fold_prefix gs ((inputs ++ [a,b,y]).map (bit k))
    have e := evaluate k
    rw [ht] at e
    exact hk e
  have wmask : b &&& witnessMask ≠ 0 := by
    obtain ⟨x,hx0,hx1,hx6,hx⟩ := hwit
    obtain ⟨k,hk,hmask⟩ := sample_witness x hx0 hx1 hx6
    rw [← hk,wires_model] at hx
    obtain ⟨t,ht⟩ := fold_prefix gs ((inputs ++ [a,b,y]).map (bit k))
    rw [ht,List.getD_append _ _ _ _ (by simp [inputs])] at hx
    change bit k b = true at hx
    intro h
    have eh := congrArg (bit k) h
    change (b &&& witnessMask)[k.val] = (0 : W)[k.val] at eh
    rw [BitVec.getElem_and] at eh
    have hz : (0 : W)[k.val] = false := by simp
    rw [hz] at eh
    change (bit k b && bit k witnessMask) = false at eh
    simp [hx,hmask] at eh
  let w := (0 :: base) ++ [a,b,y]
  have reduced (k : Fin 214) :
      (gs.foldl step (w.map (bit k))).getD o false = bit k (~~~goal) := by
    obtain ⟨t,h,h'⟩ := fold_ignore_zero gs hngs
      (bit k (inputs.getD 0 0)) false ((base ++ [a,b,y]).map (bit k))
    have e := evaluate k
    change (gs.foldl step (bit k (inputs.getD 0 0) ::
      (base ++ [a,b,y]).map (bit k))).getD o false = _ at e
    rw [h] at e
    change (gs.foldl step (bit k (0 : W) :: (base ++ [a,b,y]).map (bit k))).getD o false = _
    have hz : bit k (0 : W) = false := by simp [bit]
    rw [hz,h']
    cases o with
    | zero => contradiction
    | succ o => exact e
  have hav : ∀ u ∈ w, holds (available a b).toFinset u := by
    intro u hu
    change u ∈ 0 :: (base ++ [a,b,y]) at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact .inl rfl
    · exact .inr (.inr ⟨u,
        by simpa only [available,List.mem_toFinset,List.mem_dedup] using hu, .inl rfl⟩)
  obtain ⟨t,ht,run⟩ := compile gs o (fun g hg => hlegal g (by simp [hg]))
    w (available a b).toFinset hav reduced
  have cost : binaryCost gs ≤ 7 := by
    unfold binaryCost
    exact (List.length_filter_le _ _).trans (by omega)
  have lift {n m : ℕ} (h : n ≤ m) (hr : build basicOps t n (available a b).toFinset) :
      build basicOps t m (available a b).toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible_prefix a b ha hb wmask t ht (lift cost run)

end PEqualNP.Outside.L_meta_29838.PrefixCertificate

namespace PEqualNP.Outside.L_meta_29838.Relocation

open PEqualNP.CircuitLowerBounds

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def advance (w : List Bool) (g : Gate) : List Bool := w ++ [value w g]

def relabel (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def shift (i : ℕ) : ℕ := if i < 9 then i else i + 1

def rotate (h i : ℕ) : ℕ :=
  if i < 9 then i else if i < 9 + h then i + 1 else if i = 9 + h then 9 else i

theorem appendRead (a b : List Bool) (i : ℕ) :
    (a ++ b).getD i false = if i < a.length then a.getD i false else b.getD (i-a.length) false := by
  induction a generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa only [List.cons_append, List.getD_cons_succ, List.length_cons,
        Nat.add_lt_add_iff_right, Nat.add_sub_add_right] using ih i

theorem inserted (v rest : List Bool) (y : Bool) (hv : v.length = 9) (i : ℕ) :
    ((v ++ [y]) ++ rest).getD (shift i) false = (v ++ rest).getD i false := by
  by_cases hi : i < 9
  · simp only [shift, hi, if_true, List.append_assoc, appendRead, hv]
  · have h₁ : ¬ i + 1 < 9 := by omega
    have h₂ : i + 1 - 9 = (i - 9) + 1 := by omega
    simp only [shift, if_neg hi, List.append_assoc, List.singleton_append, appendRead, hv, if_neg h₁, h₂, List.getD_cons_succ]

theorem rotated (v mid tail : List Bool) (y : Bool) (hv : v.length = 9) (i : ℕ) :
    ((v ++ [y] ++ mid) ++ tail).getD (rotate mid.length i) false =
      ((v ++ mid ++ [y]) ++ tail).getD i false := by
  by_cases h0 : i < 9
  · simp only [rotate,if_pos h0,List.append_assoc,appendRead,hv]
  by_cases h1 : i < 9 + mid.length
  · have ha : ¬ i+1 < 9 := by omega
    have hb : i+1-9 = (i-9)+1 := by omega
    have hc : i-9 < mid.length := by omega
    simp only [rotate,if_neg h0,if_pos h1,List.append_assoc,List.singleton_append,appendRead,hv,if_neg ha,hb,if_pos hc,List.getD_cons_succ,List.length_cons,Nat.add_lt_add_iff_right]
  by_cases h2 : i = 9 + mid.length
  · subst i
    have ha : ¬ 9 + mid.length < 9 := by omega
    simp only [rotate,if_neg ha,lt_irrefl,if_false,if_true,List.append_assoc,List.singleton_append,appendRead,hv,Nat.add_sub_cancel_left,Nat.sub_self,List.getD_cons_zero,List.length_cons,Nat.zero_lt_succ,if_true]
  · have ha : ¬ i-9 < mid.length := by omega
    have hb : i-9 = (i-10)+1 := by omega
    have hc : ¬ i-10 < mid.length := by omega
    have hd : (i-9)-mid.length = ((i-10)-mid.length)+1 := by omega
    simp only [rotate,if_neg h0,if_neg h1,if_neg h2,List.append_assoc,List.singleton_append,
      appendRead,hv,if_neg h0]
    simp only [List.length_cons,if_neg (by omega : ¬i-9 < mid.length+1),if_neg ha,hd,List.getD_cons_succ]
    congr 1 <;> omega

theorem valueRelabel (w w' : List Bool) (f : ℕ → ℕ) (g : Gate)
    (reads : ∀ i, w'.getD (f i) false = w.getD i false) :
    value w' (relabel f g) = value w g := by
  simp only [value, relabel, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact reads i

theorem commonTrace (a b : List Bool) (f : ℕ → ℕ)
    (reads : ∀ extra i, (b ++ extra).getD (f i) false = (a ++ extra).getD i false)
    (gs : List Gate) (extra : List Bool) :
    ∃ more : List Bool, more.length = gs.length ∧
      gs.foldl advance (a ++ extra) = a ++ (extra ++ more) ∧
      (gs.map (relabel f)).foldl advance (b ++ extra) = b ++ (extra ++ more) := by
  induction gs generalizing extra with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons g gs ih =>
    let z := value (a ++ extra) g
    have he : value (b ++ extra) (relabel f g) = z := valueRelabel _ _ _ _ (reads extra)
    obtain ⟨more,length,old,new⟩ := ih (extra ++ [z])
    refine ⟨z :: more, by simp [length], ?_, ?_⟩
    · simpa only [List.foldl_cons,advance, List.append_assoc, List.singleton_append,z] using old
    · simpa only [List.map_cons,List.foldl_cons,advance,he,List.append_assoc,List.singleton_append] using new

def moved (g0 g1 reader : Gate) (pre tail : List Gate) (o : ℕ) : Circuit :=
  ⟨g0 :: g1 :: reader :: (pre.map (relabel shift) ++ tail.map (relabel (rotate pre.length))),
    rotate pre.length o⟩

def original (g0 g1 reader : Gate) (pre tail : List Gate) (o : ℕ) : Circuit :=
  ⟨g0 :: g1 :: (pre ++ reader :: tail),o⟩

theorem relocation (g0 g1 reader : Gate) (pre tail : List Gate) (o : ℕ)
    (onlyOld : ∀ j ∈ reader.inputs, j < 9) (x : Fin 7 → Bool) (i : ℕ) :
    ((moved g0 g1 reader pre tail o).wires (List.ofFn x)).getD (rotate pre.length i) false =
      ((original g0 g1 reader pre tail o).wires (List.ofFn x)).getD i false := by
  let v := advance (advance (List.ofFn x) g0) g1
  have hv : v.length = 9 := by simp [v,advance]
  let y := value v reader
  obtain ⟨mid,hm,oldPre,newPre⟩ := commonTrace v (v ++ [y]) shift
    (fun extra i => inserted v extra y hv i) pre []
  simp only [List.append_nil,List.nil_append] at oldPre newPre
  have gateValue : value (v ++ mid) reader = y := by
    change reader.op.eval _ = reader.op.eval _
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [appendRead,if_pos (hv.symm ▸ onlyOld j hj)]
  obtain ⟨more,_,oldTail,newTail⟩ := commonTrace (v ++ mid ++ [y]) (v ++ [y] ++ mid)
    (rotate mid.length) (fun extra i => rotated v mid extra y hv i) tail []
  simp only [List.append_nil,List.nil_append] at oldTail newTail
  change (((pre.map (relabel shift)) ++ (tail.map (relabel (rotate pre.length)))).foldl advance
    (advance v reader)).getD _ false =
    ((pre ++ reader :: tail).foldl advance v).getD i false
  simp only [List.foldl_append, List.foldl_cons, advance, newPre, oldPre, gateValue]
  rw [show value v reader = y from rfl, newPre, ← hm,oldTail,newTail]
  exact rotated v mid more y hv i

theorem shift_preserves_zero (i : ℕ) (h : shift i = 0) : i = 0 := by
  unfold shift at h
  split at h <;> omega

theorem rotate_preserves_zero (n i : ℕ) (h : rotate n i = 0) : i = 0 := by
  unfold rotate at h
  split_ifs at h <;> omega

end PEqualNP.Outside.L_meta_29838.Relocation

namespace PEqualNP.Outside.L_meta_29838.Relocation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_29838.PrefixCertificate (legal targetFun)

theorem legalRelabel (f : ℕ → ℕ) (g : Gate) (hg : legal g) : legal (relabel f g) := by
  simpa only [legal,relabel,List.length_map] using hg

theorem avoidsZero (f : ℕ → ℕ) (hf : ∀ i, f i = 0 → i = 0) (g : Gate)
    (hg : 0 ∉ g.inputs) : 0 ∉ (relabel f g).inputs := by
  intro h
  obtain ⟨i,hm,hi⟩ := List.mem_map.mp h
  exact hg ((hf i hi) ▸ hm)

theorem eliminate (g0 g1 reader : Gate) (pre tail : List Gate) (o : ℕ)
    (len : pre.length + tail.length = 7)
    (leg : ∀ g ∈ (original g0 g1 reader pre tail o).gates, legal g)
    (hn0 : 0 ∉ g0.inputs) (hn1 : 0 ∉ g1.inputs)
    (noPre : ∀ g ∈ pre, 0 ∉ g.inputs) (noTail : ∀ g ∈ tail, 0 ∉ g.inputs)
    (h0 : 0 ∈ reader.inputs) (h8 : 8 ∈ reader.inputs) (hop : reader.op = .or)
    (he : ∀ x : Fin 7 → Bool, (original g0 g1 reader pre tail o).eval (List.ofFn x) = targetFun x)
    (hw : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      ((original g0 g1 reader pre tail o).wires (List.ofFn x)).getD 8 false = true) : False := by
  have readerLegal := leg reader (by simp [original])
  have oldInputs : ∀ j ∈ reader.inputs, j < 9 := by
    rcases PEqualNP.Outside.L_meta_29838.PrefixCertificate.pair_inputs reader readerLegal.2 h0 h8 with hr | hr <;>
      intro j hj <;> simp [hr] at hj <;> omega
  let rest := pre.map (relabel shift) ++ tail.map (relabel (rotate pre.length))
  have renamedLegal : ∀ g ∈ rest, legal g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      exact legalRelabel _ _ (leg a (by simp [original,ha]))
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      exact legalRelabel _ _ (leg a (by simp [original,ha]))
  have renamedZero : ∀ g ∈ rest, 0 ∉ g.inputs := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      exact avoidsZero _ shift_preserves_zero _ (noPre a ha)
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      exact avoidsZero _ (rotate_preserves_zero _) _ (noTail a ha)
  apply PEqualNP.Outside.L_meta_29838.PrefixCertificate.main g0 g1 reader rest (rotate pre.length o) (by simpa [rest] using len) ?_
    hn0 hn1 renamedZero h0 h8 hop ?_ ?_
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact leg _ (by simp [original])
    rcases List.mem_cons.mp h with rfl | h
    · exact leg _ (by simp [original])
    rcases List.mem_cons.mp h with rfl | h
    · exact readerLegal
    · exact renamedLegal _ h
  · intro x
    exact (relocation g0 g1 reader pre tail o oldInputs x o).trans (he x)
  · obtain ⟨x,hx0,hx1,hx6,hx⟩ := hw
    exact ⟨x,hx0,hx1,hx6,(relocation g0 g1 reader pre tail o oldInputs x 8).trans hx⟩

end PEqualNP.Outside.L_meta_29838.Relocation

theorem PEqualNP.Outside.L_meta_29838 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 4 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 8 ∈ (C.gates.get i).inputs ∧ 8 ≠ 0 ∧ 8 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 8 false = true) := by
  rintro ⟨C,i,k,hi,hfan,hsize,he,h0,huniq,hop,_,_,_,h8,_,_,hwit⟩
  obtain ⟨gates,o⟩ := C
  rcases gates with _|⟨g0,_|⟨g1,_|⟨g2,_|⟨g3,_|⟨reader,tail⟩⟩⟩⟩⟩
  all_goals try { simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hsize }
  have total : (g0 :: g1 :: g2 :: g3 :: reader :: tail).length = 10 := hsize
  have uniq (j : Fin (g0 :: g1 :: g2 :: g3 :: reader :: tail).length) (h : 0 ∈ ((g0 :: g1 :: g2 :: g3 :: reader :: tail).get j).inputs) : j.val = 4 :=
    (congrArg Fin.val (huniq j h)).trans hi
  have gi : (g0 :: g1 :: g2 :: g3 :: reader :: tail).get i = reader := by simp [List.get_eq_getElem,hi]
  have noTail (g) (hg : g ∈ tail) : 0 ∉ g.inputs := by
    intro hz
    obtain ⟨j,hj⟩ := List.get_of_mem hg
    let q : Fin (g0 :: g1 :: g2 :: g3 :: reader :: tail).length := ⟨j.val+5,by simp only [List.length_cons]; omega⟩
    have hget : (g0 :: g1 :: g2 :: g3 :: reader :: tail).get q = g := by
      simpa [q,List.get_eq_getElem,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hj
    have h := uniq q (hget.symm ▸ hz)
    change j.val+5 = 4 at h
    omega
  have hn0 : 0 ∉ g0.inputs := by
    intro h
    have e := uniq ⟨0,by simp⟩ h
    norm_num at e
  have hn1 : 0 ∉ g1.inputs := by
    intro h
    have e := uniq ⟨1,by simp⟩ h
    norm_num at e
  have hn2 : 0 ∉ g2.inputs := by
    intro h
    have e := uniq ⟨2,by simp⟩ h
    norm_num at e
  have hn3 : 0 ∉ g3.inputs := by
    intro h
    have e := uniq ⟨3,by simp⟩ h
    norm_num at e
  apply PEqualNP.Outside.L_meta_29838.Relocation.eliminate g0 g1 reader [g2,g3] tail o ?_ ?_ hn0 hn1 ?_ noTail
    (gi ▸ h0) (gi ▸ h8) (gi ▸ hop) he hwit
  · simp only [List.length_cons,List.length_nil] at total ⊢
    omega
  · intro g hg
    obtain ⟨ho,hc⟩ := hfan g hg
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ho,hc⟩
  · intro g hg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl <;> assumption
