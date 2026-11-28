import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29842_aux

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

def buildM (ops : α → α → Finset α) (N : Finset α) : ℕ → Finset α → Prop
  | 0, available => N ⊆ available
  | k + 1, available => buildM ops N k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, buildM ops N k (insert z available)

def liveM (ops : α → α → Finset α) (N : Finset α) : ℕ → Finset α → Prop
  | 0, s => s = N
  | k + 1, s => liveM ops N k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ liveM ops N k (insert z rest)

def Reach (ops : α → α → Finset α) : ℕ → Finset α → Finset α → Prop
  | 0, av, av' => av' = av
  | k + 1, av, av' => Reach ops k av av' ∨
    ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ ops a b, Reach ops k (insert z av) av'

theorem buildM_of_reach {ops : α → α → Finset α} {N : Finset α} {k : ℕ} {av av' : Finset α}
    (h : Reach ops k av av') (hN : N ⊆ av') : buildM ops N k av := by
  induction k generalizing av with
  | zero => change av' = av at h; subst h; exact hN
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨a, ha, b, hb, hab, z, hz, ih h⟩

theorem compressM {ops : α → α → Finset α} {N : Finset α} {k : ℕ} {available : Finset α}
    (h : buildM ops N k available) : ∃ s ⊆ available, liveM ops N k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨N, h, rfl⟩
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

theorem liveM_card {ops : α → α → Finset α} {N : Finset α} {k : ℕ} {s : Finset α}
    (h : liveM ops N k s) : s.card ≤ N.card + k := by
  induction k generalizing s with
  | zero => change s = N at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem liveM_separates {ops : α → α → Finset α} {N : Finset α} (D : α → Prop)
    (hd : ∃ w ∈ N, D w) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : liveM ops N k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = N at h; subst h; exact hd
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_liveM {ops : α → α → Finset α} {N : Finset α} {k : ℕ} {s : Finset α}
    (h : liveM ops N (k + 1) s) :
    s = N ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ liveM ops N k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

theorem reach_mono {ops : α → α → Finset α} {k : ℕ} {av av' : Finset α}
    (h : Reach ops k av av') : av ⊆ av' := by
  induction k generalizing av with
  | zero => change av' = av at h; subst h; exact fun _ h => h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h⟩
    · exact ih h
    · exact (Finset.subset_insert z av).trans (ih h)

theorem reach_inv {ops : α → α → Finset α} (P : α → Prop)
    (hops : ∀ a b, ∀ z ∈ ops a b, P a → P b → P z) {k : ℕ} {av av' : Finset α}
    (h : Reach ops k av av') (hav : ∀ w ∈ av, P w) : ∀ w ∈ av', P w := by
  induction k generalizing av with
  | zero => change av' = av at h; subst h; exact hav
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h⟩
    · exact ih h hav
    · refine ih h ?_
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hops a b w hz (hav a ha) (hav b hb)
      · exact hav w hw

theorem reach_skip {ops : α → α → Finset α} {k : ℕ} {av av' : Finset α}
    (h : Reach ops k av av') : Reach ops (k + 1) av av' := Or.inl h

theorem reach_step {ops : α → α → Finset α} {k : ℕ} {av av' : Finset α} {a b z : α}
    (ha : a ∈ av) (hb : b ∈ av) (hab : a ≠ b) (hz : z ∈ ops a b)
    (h : Reach ops k (insert z av) av') : Reach ops (k + 1) av av' :=
  Or.inr ⟨a, ha, b, hb, hab, z, hz, h⟩

end Live

abbrev W := BitVec 198

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 91 := ((x >>> 91) ^^^ x).setWidth 91
def cuts (ws : List W) : BitVec 91 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := 11328207038080650440984901224692609605231148830631389036544
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 91) (w : W) : Prop :=
  w.getLsbD (91+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 91) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 91+i.val < 198 := by omega
  have hi' : i.val < 198 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 91) :
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
  change (cuts ws)[j] = (BitVec.allOnes 91)[j]
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

def MW : ℕ := 401734511064747568885490523085290650630550748445698208825343
def M60 : ℕ := 2475880078570760549798248447
def P60 : ℕ := 2475880078570760549798248448
def P182 : ℕ := 6129982163463555433433388108601236734474956488734408704
def cycN : ℕ := 390406304026666918444505621860598041025319599615066819788799
def gN : ℕ := 11328207038080650440984901224692609605231148830631389036544
def M2 : ℕ := 2475879874767114810372906941
def MH : ℕ := 43672528398563828429297201
def QX0 : ℕ := 504593386426335863096173780238715138063034482688
def X0N : ℕ := 108127943042819982939350881080971389801757685283632755

def nsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 91) x) P60

def ncuts (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (nsep w) ih) ws

def len (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def okM (MM x : ℕ) : Bool := Nat.beq (Nat.land x MM) MM

def nisGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (Bool.rec (Nat.beq w cycN) true (Nat.beq w gN)) (fun _ _ _ => false) t) ws

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

def one0 (MM : ℕ) (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
      insK w2 r (fun c => call next c)))))
    (okM MM (Nat.lor (nsep w) base))

def pair0 (MM : ℕ) (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (one0 MM next base pre mid post (Nat.land a b))
  (orB (one0 MM next base pre mid post (Nat.lor a b))
  (orB (one0 MM next base pre mid post (Nat.land a (Nat.sub MW b)))
    (one0 MM next base pre mid post (Nat.land b (Nat.sub MW a)))))

def reb (pre mid post : List ℕ) (k : List ℕ → Bool) : Bool :=
  revK mid post (fun m => revK pre m k)

def oneG (MM : ℕ) (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ)
    (w : ℕ) : Bool :=
  frc w (fun w2 =>
    orB (Bool.rec false (reb pre mid post (fun r => insK w2 r (fun c => call next c)))
      (okM MM (Nat.lor (nsep w2) base)))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK a r (fun r1 => insK w2 r1 (fun c => call next c))))
      (okM MM (Nat.lor (Nat.lor (nsep w2) base) sa)))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK b r (fun r1 => insK w2 r1 (fun c => call next c))))
      (okM MM (Nat.lor (Nat.lor (nsep w2) base) sb)))
      (Bool.rec false
        (reb pre mid post (fun r =>
          insK b r (fun r1 => insK a r1 (fun r2 => insK w2 r2 (fun c => call next c)))))
        (Nat.ble 2 extra)))))

def pairG (MM : ℕ) (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    Bool :=
  orB (oneG MM next extra a b sa sb base pre mid post (Nat.land a b))
  (orB (oneG MM next extra a b sa sb base pre mid post (Nat.lor a b))
  (orB (oneG MM next extra a b sa sb base pre mid post (Nat.land a (Nat.sub MW b)))
    (oneG MM next extra a b sa sb base pre mid post (Nat.land b (Nat.sub MW a)))))

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

def stepF (MM off : ℕ) (leaf : List ℕ → Bool) (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    Bool :=
  Bool.rec
    (Bool.rec (outerAux (pairG MM next (Nat.sub (Nat.add k1 off) (len ws))) ws [] 0)
      (outerAux (pair0 MM next) ws [] 0) (Nat.beq (len ws) (Nat.add k1 off)))
    true (leaf ws)

def srch (MM off : ℕ) (leaf : List ℕ → Bool) (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => leaf ws)
    (fun k1 ih ws => stepF MM off leaf k1 ih ws) k ws

def nopt (k : ℕ) (ws : List ℕ) : Bool := srch M60 2 nisGoal k ws

def rOf (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)

def opsN (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.sub MW b), Nat.land b (Nat.sub MW a)]

def elig (g : ℕ) : Bool := Bool.rec false (Nat.ble P182 g) (Nat.beq (Nat.land g QX0) 0)

def tryL (L : List ℕ) : Bool :=
  Bool.rec false (Bool.rec false (nopt 5 L) (Nat.beq (ncuts L) M60)) (Nat.ble (len L) 6)

def withG (g : ℕ) (body : ℕ → Bool) : Bool := Bool.rec false (body (Nat.lor X0N g)) (elig g)

def bothG (z : ℕ) (body : ℕ → Bool) : Bool := orB (withG z body) (withG (Nat.sub MW z) body)

def anyL (l : List ℕ) (p : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (p z) ih) l

def anyLL (l : List (List ℕ)) (p : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (p z) ih) l

def new7P (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  Bool.rec false
    (anyL (opsN a b) (fun z => bothG z (fun h => tryL (h :: rOf pre mid post))))
    (okM MH base)

def keepN (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

def newSP (a b _sa _sb _base : ℕ) (pre mid post : List ℕ) : Bool :=
  anyL (opsN a b) (fun z => bothG z (fun h =>
    anyLL (keepN a b (rOf pre mid post)) (fun t => orB (tryL (h :: t)) (tryL (h :: z :: t)))))

def oldS (whole : List ℕ) : List ℕ → List ℕ → Bool
  | [], _ => false
  | c :: post, pre =>
    orB (bothG c (fun h => orB (tryL (h :: (pre.reverse ++ post))) (tryL (h :: whole))))
      (oldS whole post (c :: pre))

def leaf (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec false (orB (oldS ws ws []) (outerAux newSP ws [] 0)) (Nat.ble (len ws) 6))
    (outerAux new7P ws [] 0)
    (Nat.beq (len ws) 7)

def phase1 (k : ℕ) (ws : List ℕ) : Bool := srch M2 8 leaf k ws

def srcN : List ℕ := [2109462146286497281275762427496173706061735200676771967,267822006713672658716473456937055197514969502696830669016988,321383447183229534647473642916240533373775427135837317238752,378102663655723382313997458349782443658030231947392256569344,400165563100803768277519819739467707703775302253814980018176,5802512054688288397636121551134704833597920394222764032]

def rootsP : List (List ℕ) := srcN.sublists.filter (fun ws => okM M2 (ncuts ws))

end Fast

noncomputable section FastSpec

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: ins w xs

def cutR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (nsep x)) 0

def baseOf (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post)

abbrev Split := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def innerS (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Split
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: innerS pre a post (b :: mid)

def outerS : List ℕ → List ℕ → List Split
  | [], _ => []
  | a :: rest, pre => innerS pre a rest [] ++ outerS rest (a :: pre)

def kids0 (MM base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if okM MM (Nat.lor (nsep w) base) = true then [ins w r] else []

def kidsG (MM extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if okM MM (Nat.lor (nsep w) base) = true then [ins w r] else []) ++
  ((if okM MM (Nat.lor (Nat.lor (nsep w) base) sa) = true then [ins w (ins a r)] else []) ++
  ((if okM MM (Nat.lor (Nat.lor (nsep w) base) sb) = true then [ins w (ins b r)] else []) ++
   (if Nat.ble 2 extra = true then [ins w (ins a (ins b r))] else [])))

def kidsPair0 (MM : ℕ) (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap (kids0 MM (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (MM extra : ℕ) (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap
    (kidsG MM extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (MM off k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.add k1 off) = true then (outerS ws []).flatMap (kidsPair0 MM)
  else (outerS ws []).flatMap (kidsPairG MM (Nat.sub (Nat.add k1 off) (len ws)))

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

theorem one0_eq (MM : ℕ) (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 MM next base pre mid post w = (kids0 MM base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf
  rw [brec]
  generalize okM MM (Nat.lor (nsep w) base) = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

theorem oneG_eq (MM : ℕ) (next : List ℕ → Bool) (extra a b sa sb base : ℕ)
    (pre mid post : List ℕ) (w : ℕ) :
    oneG MM next extra a b sa sb base pre mid post w =
      (kidsG MM extra a b sa sb base (rOf pre mid post) w).any next := by
  unfold oneG kidsG rOf reb
  simp only [frc_eq, revK_eq, insK_eq, call_eq, orB_eq, brec, List.any_append]
  generalize okM MM (Nat.lor (nsep w) base) = c1
  generalize okM MM (Nat.lor (Nat.lor (nsep w) base) sa) = c2
  generalize okM MM (Nat.lor (Nat.lor (nsep w) base) sb) = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

theorem pair0_eq (MM : ℕ) (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 MM next a b sa sb base pre mid post =
      ((opsN a b).flatMap (kids0 MM base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

theorem pairG_eq (MM : ℕ) (next : List ℕ → Bool) (extra a b sa sb base : ℕ)
    (pre mid post : List ℕ) :
    pairG MM next extra a b sa sb base pre mid post =
      ((opsN a b).flatMap (kidsG MM extra a b sa sb base (rOf pre mid post))).any next := by
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

theorem outerAux_nil (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws : List ℕ) :
    outerAux P ws [] 0 = (outerS ws []).any (HP P) := outerAux_eq P ws []

theorem HP_pair0 (MM : ℕ) (next : List ℕ → Bool) :
    HP (pair0 MM next) = fun t => (kidsPair0 MM t).any next := by
  funext t
  simp only [HP, pair0_eq, kidsPair0]

theorem HP_pairG (MM : ℕ) (next : List ℕ → Bool) (extra : ℕ) :
    HP (pairG MM next extra) = fun t => (kidsPairG MM extra t).any next := by
  funext t
  simp only [HP, pairG_eq, kidsPairG]

theorem stepF_eq (MM off : ℕ) (leaf : List ℕ → Bool) (k1 : ℕ) (next : List ℕ → Bool)
    (ws : List ℕ) :
    stepF MM off leaf k1 next ws = (leaf ws || (kidsL MM off k1 ws).any next) := by
  have z : (0 : ℕ) = cutR [] := rfl
  unfold stepF kidsL
  rw [brec, brec, z, outerAux_eq, outerAux_eq, HP_pair0, HP_pairG]
  cases leaf ws
  · cases Nat.beq (len ws) (Nat.add k1 off) <;> simp [List.any_flatMap]
  · simp

theorem srch_zero (MM off : ℕ) (leaf : List ℕ → Bool) (ws : List ℕ) :
    srch MM off leaf 0 ws = leaf ws := rfl

theorem srch_succ (MM off : ℕ) (leaf : List ℕ → Bool) (k : ℕ) (ws : List ℕ) :
    srch MM off leaf (k + 1) ws = (leaf ws || (kidsL MM off k ws).any (srch MM off leaf k)) := by
  rw [← stepF_eq]
  rfl

end FastSpec

noncomputable section Bridge

theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem negOne60 : (-1 : BitVec 91).toNat = M60 := by decide

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

theorem mem_kids0 {MM base w : ℕ} {r : List ℕ} (h : okM MM (Nat.lor (nsep w) base) = true) :
    ins w r ∈ kids0 MM base r w := by
  unfold kids0
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG1 {MM extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : okM MM (Nat.lor (nsep w) base) = true) :
    ins w r ∈ kidsG MM extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG2 {MM extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : okM MM (Nat.lor (Nat.lor (nsep w) base) sa) = true) :
    ins w (ins a r) ∈ kidsG MM extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG3 {MM extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : okM MM (Nat.lor (Nat.lor (nsep w) base) sb) = true) :
    ins w (ins b r) ∈ kidsG MM extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsG4 {MM extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    ins w (ins a (ins b r)) ∈ kidsG MM extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

theorem mem_kidsL {MM off k : ℕ} {wsN : List ℕ} {t : Split} {w : ℕ} {c : List ℕ}
    (ht : t ∈ outerS wsN []) (hw : w ∈ opsN t.2.1 t.2.2.2.1)
    (h0 : Nat.beq (len wsN) (Nat.add k off) = true →
      c ∈ kids0 MM (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (len wsN) (Nat.add k off) = true →
      c ∈ kidsG MM (Nat.sub (Nat.add k off) (len wsN)) t.2.1 t.2.2.2.1 (nsep t.2.1)
        (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ kidsL MM off k wsN := by
  unfold kidsL
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, hG hd⟩⟩

theorem guard1 {mask : BitVec 91} {z : W} {r : List W} (h : cuts (z :: r) &&& mask = mask) :
    okM mask.toNat (Nat.lor (nsep z.toNat) (cuts r).toNat) = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_or, ← nsep_toNat] at e
  exact beq_of_eq e

theorem guard2 {mask : BitVec 91} {z a : W} {r : List W}
    (h : cuts (z :: a :: r) &&& mask = mask) :
    okM mask.toNat (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change ((nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) &&& mask.toNat) =
    ((nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat)) &&& mask.toNat)
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

theorem child_of_split (mask : BitVec 91) (off : ℕ) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (hcut : ∀ l : List W, l.toFinset = insert z needed → cuts l &&& mask = mask)
    (hcard : (insert z needed).card + 1 ≤ k + off) :
    ∃ cW : List W, cW.Nodup ∧ cW.toFinset = insert z needed ∧
      cW.map BitVec.toNat ∈ kidsL mask.toNat off k (ws.map BitVec.toNat) := by
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
  have hfin2 : (z :: kept).toFinset = insert z needed := by
    rw [List.toFinset_cons, hfin]
  have hc : (z :: kept).length + 1 ≤ k + off := by
    rw [← List.toFinset_card_of_nodup hnd, hfin2]
    exact hcard
  have hcut2 := hcut (z :: kept) hfin2
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
      cW.Nodup ∧ cW.toFinset = insert z needed :=
    ⟨hp.nodup_iff.mpr hnd, (List.toFinset_eq_of_perm _ _ hp).trans hfin2⟩
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insW z (xs ++ (ys ++ zs)), (live_of _ (insW_perm _ _)).1,
      (live_of _ (insW_perm _ _)).2, ?_⟩
    rw [insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro _
      simp only [hr, hbase]
      exact mem_kids0 (guard1 hcut2)
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG1 (guard1 hcut2)
  · have hp : (insW z (insW a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      change ws.length = k + off at this
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG2 (guard2 hcut2)
  · have hp : (insW z (insW b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      change ws.length = k + off at this
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG3 (guard2 hcut2)
  · have hp : (insW z (insW a (insW b (xs ++ (ys ++ zs))))).Perm
        (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans (((insW_perm _ _).trans ((insW_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2, ?_⟩
    rw [insW_map, insW_map, insW_map]
    simp only [List.length_cons] at hc
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      change ws.length = k + off at this
      omega
    · intro _
      simp only [hr]
      refine mem_kidsG4 ?_
      rw [hlenN]
      apply Nat.ble_eq_true_of_le
      change 2 ≤ k + off - ws.length
      omega

theorem child_exists (mask : BitVec 91) (off : ℕ) {k : ℕ} {ws : List W} {a b z : W}
    {needed : Finset W} (hn : ws.Nodup) (ha : a ∈ ws.toFinset) (hb : b ∈ ws.toFinset)
    (hab : a ≠ b) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (hcut : ∀ l : List W, l.toFinset = insert z needed → cuts l &&& mask = mask)
    (hcard : (insert z needed).card + 1 ≤ k + off) :
    ∃ cW : List W, cW.Nodup ∧ cW.toFinset = insert z needed ∧
      cW.map BitVec.toNat ∈ kidsL mask.toNat off k (ws.map BitVec.toNat) := by
  rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
    ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
  · exact child_of_split mask off hn e hz hout hs hcut hcard
  · exact child_of_split mask off hn e (ops_swap a b ▸ hz) hout
      (by rw [hs, Finset.insert_comm]) hcut hcard

theorem cuts_all1 {ws : List W} (h : cuts ws = -1) : cuts ws &&& (-1 : BitVec 91) = -1 := by
  rw [h]; exact BitVec.and_self

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
    unfold nopt
    rw [srch_succ]
    rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rw [singleton_list hn done]
      have := nisGoal_goal hg
      simp only [List.map_cons, List.map_nil, this, Bool.true_or]
    · have hcut : ∀ l : List W, l.toFinset = insert z needed →
          cuts l &&& (-1 : BitVec 91) = -1 := by
        intro l hl2
        exact cuts_all1 (cuts_full hg (hl2 ▸ tail))
      have hcard : (insert z needed).card + 1 ≤ k + 2 := by
        have := live_card tail
        omega
      obtain ⟨cW, hcn, hcf, hmem⟩ := child_exists (-1 : BitVec 91) 2 hn ha hb hab hz hout hs
        hcut hcard
      rw [negOne60] at hmem
      have := ih cW hcn (hcf ▸ tail)
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)


def M2v : BitVec 91 := 2475879874767114810372906941
def MHv : BitVec 91 := 43672528398563828429297201
def X0v : W := 108127943042819982939350881080971389801757685283632755

theorem M2v_toNat : M2v.toNat = M2 := rfl
theorem MHv_toNat : MHv.toNat = MH := rfl
theorem X0v_toNat : X0v.toNat = X0N := rfl

theorem nbeq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem cuts_mask {mask : BitVec 91} {l : List W}
    (h : ∀ i : Fin 91, mask.getLsbD i.val = true → ∃ w ∈ l, differs i w) :
    cuts l &&& mask = mask := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and]
  by_cases hm : mask.getLsbD j = true
  · rw [hm, (cuts_spec l ⟨j, hj⟩).mpr (h ⟨j, hj⟩ hm)]
    rfl
  · simp only [Bool.not_eq_true] at hm
    simp [hm]

theorem phase1_complete (T : Finset W) (hT : T.card ≤ 7)
    (hsep : ∀ i : Fin 91, M2v.getLsbD i.val = true → ∃ w ∈ T, differs i w)
    (hleaf : ∀ ws : List W, ws.Nodup → ws.toFinset = T → leaf (ws.map BitVec.toNat) = true) :
    ∀ (k : ℕ) (ws : List W), ws.Nodup → liveM basicOps T k ws.toFinset →
      phase1 k (ws.map BitVec.toNat) = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    exact hleaf ws hn h
  | succ k ih =>
    intro ws hn hl
    unfold phase1
    rw [srch_succ]
    rcases first_liveM hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rw [hleaf ws hn done, Bool.true_or]
    · have hcut : ∀ l : List W, l.toFinset = insert z needed → cuts l &&& M2v = M2v := by
        intro l hl2
        apply cuts_mask
        intro i hi
        obtain ⟨w, hw, hd⟩ := liveM_separates (differs i) (hsep i hi) (ops_differs i) tail
        exact ⟨w, List.mem_toFinset.mp (hl2 ▸ hw), hd⟩
      have hcard : (insert z needed).card + 1 ≤ k + 8 := by
        have := liveM_card tail
        omega
      obtain ⟨cW, hcn, hcf, hmem⟩ := child_exists M2v 8 hn ha hb hab hz hout hs hcut hcard
      rw [M2v_toNat] at hmem
      have := ih cW hcn (hcf ▸ tail)
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)

theorem not_toNat (z : W) : (~~~z).toNat = Nat.sub MW z.toNat := by
  rw [BitVec.toNat_not]
  rfl

theorem or_toNat (g : W) : (X0v ||| g).toNat = Nat.lor X0N g.toNat := by
  rw [BitVec.toNat_or]
  rfl

theorem tryL_complete {gl : W} (hgl : gl = goal ∨ gl = ~~~goal) (L : List W) (hn : L.Nodup)
    (hl : live basicOps gl 5 L.toFinset) : tryL (L.map BitVec.toNat) = true := by
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hn] at hc
  have h1 : Nat.ble (len (L.map BitVec.toNat)) 6 = true := by
    rw [len_eq, List.length_map]
    exact Nat.ble_eq_true_of_le hc
  have h2 : Nat.beq (ncuts (L.map BitVec.toNat)) M60 = true := by
    rw [ncuts_map, cuts_full hgl hl, negOne60]
    exact Nat.beq_refl _
  have h3 := nopt_complete hgl 5 L hn hl
  unfold tryL
  rw [brec, brec, if_pos h1, if_pos h2]
  exact h3

theorem withG_true {g : ℕ} {body : ℕ → Bool} (he : elig g = true)
    (hb : body (Nat.lor X0N g) = true) : withG g body = true := by
  unfold withG
  rw [brec, if_pos he]
  exact hb

theorem bothG_of {z : W} {g : W} (hgz : g = z ∨ g = ~~~z) {body : ℕ → Bool}
    (he : elig g.toNat = true) (hb : body (X0v ||| g).toNat = true) :
    bothG z.toNat body = true := by
  unfold bothG
  rw [orB_eq, Bool.or_eq_true]
  rcases hgz with rfl | rfl
  · exact .inl (withG_true he (by rw [← or_toNat]; exact hb))
  · rw [not_toNat] at he
    refine .inr (withG_true he ?_)
    rw [← not_toNat, ← or_toNat]
    exact hb

theorem anyL_of {l : List ℕ} {p : ℕ → Bool} {x : ℕ} (hx : x ∈ l) (hp : p x = true) :
    anyL l p = true := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    change orB (p y) (anyL ys p) = true
    rw [orB_eq, Bool.or_eq_true]
    rcases List.mem_cons.mp hx with rfl | h
    · exact .inl hp
    · exact .inr (ih h)

theorem anyLL_of {l : List (List ℕ)} {p : List ℕ → Bool} {x : List ℕ} (hx : x ∈ l)
    (hp : p x = true) : anyLL l p = true := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    change orB (p y) (anyLL ys p) = true
    rw [orB_eq, Bool.or_eq_true]
    rcases List.mem_cons.mp hx with rfl | h
    · exact .inl hp
    · exact .inr (ih h)

theorem oldS_of (whole : List ℕ) (c : ℕ) (ys : List ℕ) : ∀ (xs pre : List ℕ),
    bothG c (fun h => orB (tryL (h :: ((xs.reverse ++ pre).reverse ++ ys)))
      (tryL (h :: whole))) = true →
    oldS whole (xs ++ c :: ys) pre = true := by
  intro xs
  induction xs with
  | nil =>
    intro pre h
    simp only [List.nil_append, List.reverse_nil] at h ⊢
    rw [oldS, orB_eq, h, Bool.true_or]
  | cons x xs ih =>
    intro pre h
    rw [List.cons_append, oldS, orB_eq, ih (x :: pre) (by simpa using h), Bool.or_true]

theorem leaf_old {gl : W} (hgl : gl = goal ∨ gl = ~~~goal) (ws : List W) (hn : ws.Nodup)
    (hlen : ws.length ≤ 6) (c : W) (hc : c ∈ ws) (g : W) (hgc : g = c ∨ g = ~~~c)
    (he : elig g.toNat = true) (L : Finset W) (hl : live basicOps gl 5 L)
    (hL : L = insert (X0v ||| g) (ws.toFinset.erase c) ∨ L = insert (X0v ||| g) ws.toFinset)
    (hh : X0v ||| g ∉ ws.toFinset) : leaf (ws.map BitVec.toNat) = true := by
  obtain ⟨xs, ys, rfl⟩ := List.append_of_mem hc
  have hlenN : len ((xs ++ c :: ys).map BitVec.toNat) = (xs ++ c :: ys).length := by
    rw [len_eq, List.length_map]
  have h7 : Nat.beq (len ((xs ++ c :: ys).map BitVec.toNat)) 7 = false := by
    rw [hlenN]
    exact nbeq_false (by omega)
  have h6 : Nat.ble (len ((xs ++ c :: ys).map BitVec.toNat)) 6 = true := by
    rw [hlenN]
    exact Nat.ble_eq_true_of_le hlen
  have hcx : c ∉ xs := by
    intro hm
    have := (List.nodup_middle.mp hn)
    exact (List.nodup_cons.mp this).1 (List.mem_append_left _ hm)
  have hcy : c ∉ ys := by
    intro hm
    have := (List.nodup_middle.mp hn)
    exact (List.nodup_cons.mp this).1 (List.mem_append_right _ hm)
  have hnr : (xs ++ ys).Nodup := (List.nodup_cons.mp (List.nodup_middle.mp hn)).2
  have hhm : X0v ||| g ∉ xs ++ c :: ys := fun hm => hh (List.mem_toFinset.mpr hm)
  have hold : oldS ((xs ++ c :: ys).map BitVec.toNat) ((xs ++ c :: ys).map BitVec.toNat) [] =
      true := by
    rw [List.map_append, List.map_cons]
    apply oldS_of
    refine bothG_of hgc he ?_
    simp only [List.reverse_append, List.reverse_nil, List.nil_append, List.reverse_reverse]
    rw [orB_eq, Bool.or_eq_true]
    rcases hL with rfl | rfl
    · left
      have e : (List.map BitVec.toNat xs ++ List.map BitVec.toNat ys) = (xs ++ ys).map BitVec.toNat :=
        by simp
      rw [e, ← List.map_cons]
      refine tryL_complete hgl _ ?_ ?_
      · refine List.nodup_cons.mpr ⟨fun hm => hhm ?_, hnr⟩
        rcases List.mem_append.mp hm with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · have e2 : ((X0v ||| g) :: (xs ++ ys)).toFinset =
            insert (X0v ||| g) ((xs ++ c :: ys).toFinset.erase c) := by
          ext v
          simp only [List.toFinset_cons, List.toFinset_append, Finset.mem_insert,
            Finset.mem_union, List.mem_toFinset, Finset.mem_erase, List.mem_cons]
          constructor
          · rintro (h | h | h)
            · exact .inl h
            · exact .inr ⟨fun e => hcx (e ▸ h), .inl h⟩
            · exact .inr ⟨fun e => hcy (e ▸ h), .inr (.inr h)⟩
          · rintro (h | ⟨hne, h | h | h⟩)
            · exact .inl h
            · exact .inr (.inl h)
            · exact absurd h hne
            · exact .inr (.inr h)
        rw [e2]
        exact hl
    · right
      have e : (BitVec.toNat (X0v ||| g) :: (List.map BitVec.toNat xs ++ BitVec.toNat c ::
          List.map BitVec.toNat ys)) = ((X0v ||| g) :: (xs ++ c :: ys)).map BitVec.toNat := by simp
      rw [e]
      refine tryL_complete hgl _ (List.nodup_cons.mpr ⟨hhm, hn⟩) ?_
      rw [List.toFinset_cons]
      exact hl
  unfold leaf
  rw [brec, brec, h7, h6]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [orB_eq, hold, Bool.true_or]


theorem allOnes_bit : ∀ i : Fin 91, (-1 : BitVec 91).getLsbD i.val = true := by decide +kernel

theorem keepN_map (a b : W) (r : List W) :
    keepN a.toNat b.toNat (r.map BitVec.toNat) = (keepChoices a b r).map (List.map BitVec.toNat) :=
  rfl

theorem leaf_new_split {gl : W} (hgl : gl = goal ∨ gl = ~~~goal) (ws xs ys zs : List W)
    (hn : ws.Nodup) (a b z : W) (hsplit : ws = xs ++ a :: (ys ++ b :: zs))
    (hz : z ∈ basicOps a b) (hzout : z ∉ ws.toFinset) (g : W) (hgz : g = z ∨ g = ~~~z)
    (he : elig g.toNat = true) (needed : Finset W)
    (hs : ws.toFinset = insert a (insert b needed)) (hh : X0v ||| g ∉ ws.toFinset)
    (hhz : X0v ||| g ≠ z)
    (hl : live basicOps gl 5 (insert (X0v ||| g) needed) ∨
      live basicOps gl 5 (insert (X0v ||| g) (insert z needed)))
    (hMH : ∀ i : Fin 91, MHv.getLsbD i.val = true → ¬ differs i (X0v ||| g)) :
    leaf (ws.map BitVec.toNat) = true := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hs
  set h := X0v ||| g with hdef
  have hlen2 := perm.length_eq
  simp only [List.length_cons] at hlen2
  have habr := perm.nodup_iff.mp hn
  have hsub : ∀ v ∈ kept, v ∈ ws := by
    intro v hv
    have : v ∈ needed := hfin ▸ List.mem_toFinset.mpr hv
    have : v ∈ ws.toFinset := by rw [hs]; simp [this]
    exact List.mem_toFinset.mp this
  have hhk : h ∉ kept := fun hm => hh (List.mem_toFinset.mpr (hsub h hm))
  have hzk : z ∉ kept := fun hm => hzout (List.mem_toFinset.mpr (hsub z hm))
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
  -- the two candidate final lists
  have L1 : (h :: kept).Nodup ∧ (h :: kept).toFinset = insert h needed :=
    ⟨List.nodup_cons.mpr ⟨hhk, hnk⟩, by rw [List.toFinset_cons, hfin]⟩
  have L2 : (h :: z :: kept).Nodup ∧ (h :: z :: kept).toFinset = insert h (insert z needed) := by
    refine ⟨List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hzk, hnk⟩⟩, ?_⟩
    · intro hm
      rcases List.mem_cons.mp hm with e | e
      · exact hhz e
      · exact hhk e
    · rw [List.toFinset_cons, List.toFinset_cons, hfin]
  have cardL : ∀ L : List W, L.Nodup → live basicOps gl 5 L.toFinset → L.length ≤ 6 := by
    intro L hnd hlv
    have := live_card hlv
    rwa [List.toFinset_card_of_nodup hnd] at this
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  by_cases h7 : ws.length = 7
  · -- only the shape h :: rest fits
    have hkr : kept = xs ++ (ys ++ zs) := by
      rcases hl with hl | hl
      · have c1 := cardL _ L1.1 (L1.2 ▸ hl)
        simp only [List.length_cons] at c1
        rcases hk with rfl | rfl | rfl | rfl
        · rfl
        all_goals (try simp only [List.length_cons] at c1)
        all_goals omega
      · have c1 := cardL _ L2.1 (L2.2 ▸ hl)
        simp only [List.length_cons] at c1
        rcases hk with rfl | rfl | rfl | rfl
        all_goals (try simp only [List.length_cons] at c1)
        all_goals omega
    subst hkr
    have hl1 : live basicOps gl 5 (insert h needed) := by
      rcases hl with hl | hl
      · exact hl
      · have c1 := cardL _ L2.1 (L2.2 ▸ hl)
        simp only [List.length_cons] at c1
        omega
    have hcov : cuts (xs ++ (ys ++ zs)) &&& MHv = MHv := by
      apply cuts_mask
      intro i hi
      have hfull := cuts_full hgl (L1.2 ▸ hl1)
      have hb := (cuts_spec (h :: (xs ++ (ys ++ zs))) i).mp (by rw [hfull]; exact allOnes_bit i)
      obtain ⟨w, hw, hd⟩ := hb
      rcases List.mem_cons.mp hw with rfl | hw
      · exact absurd hd (hMH i hi)
      · exact ⟨w, hw, hd⟩
    have hok : okM MH (cuts (xs ++ (ys ++ zs))).toNat = true := by
      have e := congrArg BitVec.toNat hcov
      rw [BitVec.toNat_and, MHv_toNat] at e
      exact beq_of_eq e
    have hP : HP new7P ((xs.map BitVec.toNat).reverse, a.toNat, (ys.map BitVec.toNat).reverse,
        b.toNat, zs.map BitVec.toNat) = true := by
      unfold HP new7P
      simp only
      rw [hbase, brec, if_pos hok, hr]
      refine anyL_of hzN (bothG_of hgz he ?_)
      rw [← List.map_cons]
      exact tryL_complete hgl _ L1.1 (L1.2 ▸ hl1)
    unfold leaf
    rw [brec, hlenN, if_pos (by rw [h7]; rfl), outerAux_nil]
    exact List.any_eq_true.mpr ⟨_, ht, hP⟩
  · have hle : ws.length ≤ 6 := by
      rcases hl with hl | hl
      · have c1 := cardL _ L1.1 (L1.2 ▸ hl)
        simp only [List.length_cons] at c1
        rcases hk with rfl | rfl | rfl | rfl
        all_goals (try simp only [List.length_cons] at c1)
        all_goals omega
      · have c1 := cardL _ L2.1 (L2.2 ▸ hl)
        simp only [List.length_cons] at c1
        rcases hk with rfl | rfl | rfl | rfl
        all_goals (try simp only [List.length_cons] at c1)
        all_goals omega
    have hP : HP newSP ((xs.map BitVec.toNat).reverse, a.toNat, (ys.map BitVec.toNat).reverse,
        b.toNat, zs.map BitVec.toNat) = true := by
      unfold HP newSP
      simp only
      rw [hr]
      refine anyL_of hzN (bothG_of hgz he ?_)
      have hkm : kept.map BitVec.toNat ∈ keepN a.toNat b.toNat ((xs ++ (ys ++ zs)).map BitVec.toNat) := by
        rw [keepN_map]
        refine List.mem_map_of_mem ?_
        simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false]
        exact hk
      refine anyLL_of hkm ?_
      rw [orB_eq, Bool.or_eq_true]
      rcases hl with hl | hl
      · left
        rw [← List.map_cons]
        exact tryL_complete hgl _ L1.1 (L1.2 ▸ hl)
      · right
        rw [← List.map_cons, ← List.map_cons]
        exact tryL_complete hgl _ L2.1 (L2.2 ▸ hl)
    have hne7 : Nat.beq (len (ws.map BitVec.toNat)) 7 = false := by
      rw [hlenN]
      exact nbeq_false h7
    have h6 : Nat.ble (len (ws.map BitVec.toNat)) 6 = true := by
      rw [hlenN]
      exact Nat.ble_eq_true_of_le hle
    unfold leaf
    rw [brec, brec, hne7, h6]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [orB_eq, outerAux_nil]
    exact Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨_, ht, hP⟩))

theorem leaf_new {gl : W} (hgl : gl = goal ∨ gl = ~~~goal) (ws : List W) (hn : ws.Nodup)
    (a b z : W) (ha : a ∈ ws.toFinset) (hb : b ∈ ws.toFinset) (hab : a ≠ b)
    (hz : z ∈ basicOps a b) (hzout : z ∉ ws.toFinset) (g : W) (hgz : g = z ∨ g = ~~~z)
    (he : elig g.toNat = true) (needed : Finset W)
    (hs : ws.toFinset = insert a (insert b needed)) (hh : X0v ||| g ∉ ws.toFinset)
    (hhz : X0v ||| g ≠ z)
    (hl : live basicOps gl 5 (insert (X0v ||| g) needed) ∨
      live basicOps gl 5 (insert (X0v ||| g) (insert z needed)))
    (hMH : ∀ i : Fin 91, MHv.getLsbD i.val = true → ¬ differs i (X0v ||| g)) :
    leaf (ws.map BitVec.toNat) = true := by
  rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
    ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
  · exact leaf_new_split hgl ws xs ys zs hn a b z e hz hzout g hgz he needed hs hh hhz hl hMH
  · exact leaf_new_split hgl ws xs ys zs hn b a z e (ops_swap a b ▸ hz) hzout g hgz he needed
      (by rw [hs, Finset.insert_comm]) hh hhz hl hMH

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
  · change reachable av (BitVec.allOnes 198 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 198)
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

def bit (k : Fin 198) (z : W) : Bool := z[k.val]
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_bit (w : List W) (i : ℕ) (k : Fin 198) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 198) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#198)[k.val] = false; simp
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

theorem runW_bits (gs : List Gate) (w : List W) (hg : ∀ g ∈ gs, legal g) (k : Fin 198) :
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



def emptyGate : Gate := ⟨.or, []⟩

def srcL : List W := [2109462146286497281275762427496173706061735200676771967,267822006713672658716473456937055197514969502696830669016988,321383447183229534647473642916240533373775427135837317238752,378102663655723382313997458349782443658030231947392256569344,400165563100803768277519819739467707703775302253814980018176,5802512054688288397636121551134704833597920394222764032]

def primary : List W := X0v :: srcL

def X0P : BitVec 91 := 203803645739425341506
def QX0v : W := 504593386426335863096173780238715138063034482688

theorem QX0v_toNat : QX0v.toNat = QX0 := rfl
theorem srcL_map : srcL.map BitVec.toNat = srcN := rfl

theorem ne_of_bit {a b : W} (j : ℕ) (h : a.getLsbD j ≠ b.getLsbD j) : a ≠ b :=
  fun e => h (e ▸ rfl)

theorem ng_ne0 : ~~~goal ≠ 0 := ne_of_bit 0 (by decide +kernel)
theorem ng_ne1 : ~~~goal ≠ ~~~0 := ne_of_bit 91 (by decide +kernel)

theorem compile_plain (gs : List Gate) (out : ℕ) (w : List W) (av : Finset W)
    (hg : ∀ g ∈ gs, legal g) (hout : out ≠ 0)
    (hw : ∀ i, i ≠ 0 → holds av (w.getD i 0))
    (hr : ∀ g ∈ gs, 0 ∉ g.inputs)
    (he : (runW gs w).getD out 0 = ~~~goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have h := he ▸ hw out hout
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (ng_ne0 zero)
    · exact False.elim (ng_ne1 ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    have nr : 0 ∉ g.inputs := hr g (by simp)
    have reach := gate_reach_reads w av g (hg g (by simp))
      (fun i hi => hw i (fun eq => nr (eq ▸ hi)))
    have tailEval : (runW gs (w ++ [action w g])).getD out 0 = ~~~goal := he
    have cont (A : Finset W) (sub : av ⊆ A) (new : holds A (action w g)) :=
      ih (w ++ [action w g]) A (fun a ha => hg a (by simp [ha]))
        (holds_append w A _ (fun i hi => holds_mono sub (hw i hi)) new)
        (fun a ha => hr a (by simp [ha])) tailEval
    rw [List.length_cons]
    rcases reach with old | ⟨a,ha,b,hb,ne,new,op,rep⟩
    · obtain ⟨t,ht,run⟩ := cont av (fun _ h => h) old
      exact ⟨t,ht,Or.inl run⟩
    · obtain ⟨t,ht,run⟩ := cont (insert new av) (Finset.subset_insert _ _) rep
      exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

theorem chain (gs : List Gate) (w : List W) (av : Finset W)
    (hg : ∀ g ∈ gs, legal g) (hw : ∀ i, i ≠ 0 → holds av (w.getD i 0))
    (hr : ∀ g ∈ gs, 0 ∉ g.inputs) :
    ∃ av', Reach basicOps gs.length av av' ∧ ∀ i, i ≠ 0 → holds av' ((runW gs w).getD i 0) := by
  induction gs generalizing w av with
  | nil => exact ⟨av, rfl, hw⟩
  | cons g gs ih =>
    have nr : 0 ∉ g.inputs := hr g (by simp)
    have reach := gate_reach_reads w av g (hg g (by simp))
      (fun i hi => hw i (fun eq => nr (eq ▸ hi)))
    have cont (A : Finset W) (sub : av ⊆ A) (new : holds A (action w g)) :=
      ih (w ++ [action w g]) A (fun a ha => hg a (by simp [ha]))
        (holds_append w A _ (fun i hi => holds_mono sub (hw i hi)) new)
        (fun a ha => hr a (by simp [ha]))
    rcases reach with old | ⟨a,ha,b,hb,ne,new,op,rep⟩
    · obtain ⟨av', hR, hh⟩ := cont av (fun _ h => h) old
      exact ⟨av', Or.inl hR, hh⟩
    · obtain ⟨av', hR, hh⟩ := cont (insert new av) (Finset.subset_insert _ _) rep
      exact ⟨av', Or.inr ⟨a, ha, b, hb, ne, new, op, hR⟩, hh⟩

theorem gate3_cases {av : Finset W} {g : W} (h : reachable av g) :
    holds av g ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ basicOps a b, z ∉ av ∧ (g = z ∨ g = ~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, hab, w, hw, hh⟩
  · exact .inl h
  · rcases hh with h0 | h1 | ⟨c, hc, hgc⟩
    · exact .inl (.inl h0)
    · exact .inl (.inr (.inl h1))
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · by_cases hin : c ∈ av
        · exact .inl (.inr (.inr ⟨c, hin, hgc⟩))
        · exact .inr ⟨a, ha, b, hb, hab, c, hw, hin, hgc⟩
      · exact .inl (.inr (.inr ⟨c, hc, hgc⟩))

set_option maxRecDepth 20000 in
theorem F1b : ∀ i : Fin 91, X0P.getLsbD i.val = true →
    srcL.all (fun w => w.getLsbD (91 + i.val) == w.getLsbD i.val) = true := by decide +kernel

theorem F1 : ∀ w ∈ srcL, ∀ i : Fin 91, X0P.getLsbD i.val = true → ¬ differs i w := by
  intro w hw i hi
  have := List.all_eq_true.mp (F1b i hi) w hw
  unfold differs
  simpa using this

set_option maxRecDepth 20000 in
theorem F2 : ∀ i : Fin 91, X0P.getLsbD i.val = true →
    X0v.getLsbD i.val = true ∧ X0v.getLsbD (91 + i.val) = false := by decide +kernel

set_option maxRecDepth 20000 in
theorem F3b : ∀ j : Fin 198,
    (!QX0v.getLsbD j.val || (Nat.ble 91 j.val && X0P.getLsbD (j.val - 91))) = true := by
  decide +kernel

theorem F3 : ∀ j : Fin 198, QX0v.getLsbD j.val = true →
    91 ≤ j.val ∧ X0P.getLsbD (j.val - 91) = true := by
  intro j hj
  have := F3b j
  rw [hj] at this
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
  exact ⟨Nat.le_of_ble_eq_true this.1, this.2⟩

set_option maxRecDepth 20000 in
theorem F4 : ∀ i : Fin 91, MHv.getLsbD i.val = true →
    X0v.getLsbD i.val = true ∧ X0v.getLsbD (91 + i.val) = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem F5 : ∀ i : Fin 91, M2v.getLsbD i.val = true →
    X0v.getLsbD i.val = X0v.getLsbD (91 + i.val) := by decide +kernel

theorem F7 : X0P.getLsbD 1 = true := by decide +kernel

theorem srcL_nodup : srcL.Nodup := by decide +kernel

theorem goal_differs {t : W} (ht : t = goal ∨ t = ~~~goal) : ∀ i : Fin 91, differs i t := by
  rcases ht with rfl | rfl <;> unfold differs <;> decide +kernel

theorem differs_not (i : Fin 91) (w : W) : differs i (~~~w) ↔ differs i w := by
  unfold differs
  have h1 : 91 + i.val < 198 := by omega
  have h2 : i.val < 198 := by omega
  simp only [BitVec.getLsbD_not, h1, h2, decide_true, Bool.true_and]
  cases w.getLsbD (91 + i.val) <;> cases w.getLsbD i.val <;> simp

theorem or_differs (i : Fin 91) (g : W) (hi : M2v.getLsbD i.val = true)
    (hd : differs i (X0v ||| g)) : differs i g := by
  have e := F5 i hi
  unfold differs at hd ⊢
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, e] at hd
  intro hg
  rw [hg] at hd
  exact hd rfl

theorem or_blind_MH (i : Fin 91) (g : W) (hi : MHv.getLsbD i.val = true) :
    ¬ differs i (X0v ||| g) := by
  obtain ⟨e1, e2⟩ := F4 i hi
  unfold differs
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, e1, e2]
  simp

theorem M2_lt (s : Finset W) (hs : ∀ i : Fin 91, M2v.getLsbD i.val = true → ∃ w ∈ s, differs i w)
    (l : List W) (hl : l.toFinset = s) : okM M2 (ncuts (l.map BitVec.toNat)) = true := by
  have hc : cuts l &&& M2v = M2v := by
    apply cuts_mask
    intro i hi
    obtain ⟨w, hw, hd⟩ := hs i hi
    exact ⟨w, List.mem_toFinset.mp (hl ▸ hw), hd⟩
  have e := congrArg BitVec.toNat hc
  rw [BitVec.toNat_and, M2v_toNat] at e
  rw [ncuts_map]
  exact beq_of_eq e


def rootN : List ℕ := srcN

def kids1 : List (List ℕ) := kidsL M2 8 2 rootN

set_option maxRecDepth 100000 in
theorem roots_one : rootsP = [rootN] := by decide +kernel

set_option maxRecDepth 100000 in
theorem kids1_len : kids1.length ≤ 60 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem leaf_root : leaf rootN = false := by decide +kernel

theorem all_chunk {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk0 : ((kids1.drop 0).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk1 : ((kids1.drop 5).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk2 : ((kids1.drop 10).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk3 : ((kids1.drop 15).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk4 : ((kids1.drop 20).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk5 : ((kids1.drop 25).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk6 : ((kids1.drop 30).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk7 : ((kids1.drop 35).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk8 : ((kids1.drop 40).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk9 : ((kids1.drop 45).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk10 : ((kids1.drop 50).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunk11 : ((kids1.drop 55).take 5).all (fun c => !phase1 2 c) = true := by
  decide +kernel

theorem chunk_end : (kids1.drop 60).all (fun c => !phase1 2 c) = true := by
  rw [List.drop_eq_nil_of_le kids1_len]
  rfl

theorem kids1_all : kids1.all (fun c => !phase1 2 c) = true := by
  have h := (all_chunk _ kids1 0 5 chunk0 (all_chunk _ kids1 5 5 chunk1 (all_chunk _ kids1 10 5 chunk2 (all_chunk _ kids1 15 5 chunk3 (all_chunk _ kids1 20 5 chunk4 (all_chunk _ kids1 25 5 chunk5 (all_chunk _ kids1 30 5 chunk6 (all_chunk _ kids1 35 5 chunk7 (all_chunk _ kids1 40 5 chunk8 (all_chunk _ kids1 45 5 chunk9 (all_chunk _ kids1 50 5 chunk10 (all_chunk _ kids1 55 5 chunk11 chunk_end))))))))))))
  simpa using h

theorem search_all : rootsP.all (fun ws => !phase1 3 ws) = true := by
  rw [roots_one]
  have h : phase1 3 rootN = false := by
    unfold phase1
    rw [srch_succ]
    change (leaf rootN || kids1.any (srch M2 8 leaf 2)) = false
    rw [leaf_root, Bool.false_or]
    have := kids1_all
    rw [List.all_eq_true] at this
    rw [List.any_eq_false]
    intro c hc
    have := this c hc
    unfold phase1 at this
    simpa using this
  simp [h]


theorem finish (av3 : Finset W) (hreach : Reach basicOps 3 srcL.toFinset av3) (T : Finset W)
    (hTsub : T ⊆ av3) (hcard : T.card ≤ 7)
    (hsep : ∀ i : Fin 91, M2v.getLsbD i.val = true → ∃ w ∈ T, differs i w)
    (hleaf : ∀ ws : List W, ws.Nodup → ws.toFinset = T → leaf (ws.map BitVec.toNat) = true) :
    False := by
  classical
  obtain ⟨s, hs, hl⟩ := compressM (buildM_of_reach hreach hTsub)
  let sW := srcL.filter (· ∈ s)
  have eq : sW.toFinset = s := by
    ext w
    simp only [sW, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : sW.Nodup := srcL_nodup.filter _
  have run := phase1_complete T hcard hsep hleaf 3 sW hnd (eq ▸ hl)
  have hroot : sW.map BitVec.toNat ∈ rootsP := by
    unfold rootsP
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← srcL_map]
      exact List.mem_sublists.mpr ((List.filter_sublist).map _)
    · have hsepS : ∀ i : Fin 91, M2v.getLsbD i.val = true → ∃ w ∈ s, differs i w :=
        fun i hi => liveM_separates (differs i) (hsep i hi) (ops_differs i) hl
      exact M2_lt s hsepS sW eq
  have := List.all_eq_true.mp search_all _ hroot
  rw [run] at this
  exact absurd this (by decide)

theorem core (av3 : Finset W) (hreach : Reach basicOps 3 srcL.toFinset av3) (g : W)
    (hwit : ∃ r : Fin 16, g.getLsbD (182 + r.val) = true) (t : W) (ht : t = goal ∨ t = ~~~goal)
    (hcase : (holds av3 g ∧ build basicOps t 5 (insert (X0v ||| g) av3)) ∨
      (∃ a ∈ av3, ∃ b ∈ av3, a ≠ b ∧ ∃ z ∈ basicOps a b, z ∉ av3 ∧ (g = z ∨ g = ~~~z) ∧
        build basicOps t 5 (insert (X0v ||| g) (insert z av3)))) : False := by
  classical
  let Blind : W → Prop := fun w => ∀ i : Fin 91, X0P.getLsbD i.val = true → ¬ differs i w
  have bops : ∀ a b, ∀ z ∈ basicOps a b, Blind a → Blind b → Blind z := by
    intro a b z hz ha hb i hi hd
    rcases ops_differs i a b z hz hd with h1 | h1
    · exact ha i hi h1
    · exact hb i hi h1
  have b3 : ∀ w ∈ av3, Blind w :=
    reach_inv Blind bops hreach (fun w hw => F1 w (List.mem_toFinset.mp hw))
  have hdT := goal_differs ht
  have b3sub : ∀ T : Finset W, T ⊆ av3 → ∀ w ∈ T, Blind w := fun T hT w hw => b3 w (hT hw)
  -- the analysis of the gates after the OR gate
  have analyze : ∀ av4 : Finset W, (∀ w ∈ av4, Blind w) →
      build basicOps t 5 (insert (X0v ||| g) av4) →
      ∃ L ⊆ insert (X0v ||| g) av4, live basicOps t 5 L ∧ (X0v ||| g) ∈ L ∧
        (X0v ||| g) ∉ av4 ∧
        (∀ i : Fin 91, X0P.getLsbD i.val = true → differs i (X0v ||| g)) := by
    intro av4 hb4 hbuild
    obtain ⟨L, hLsub, hl⟩ := compress hbuild
    have hx : ∀ i : Fin 91, X0P.getLsbD i.val = true → (X0v ||| g) ∈ L ∧ differs i (X0v ||| g) := by
      intro i hi
      obtain ⟨w, hw, hd⟩ := live_separates (differs i) (hdT i) (ops_differs i) hl
      rcases Finset.mem_insert.mp (hLsub hw) with rfl | hw4
      · exact ⟨hw, hd⟩
      · exact absurd hd (hb4 w hw4 i hi)
    refine ⟨L, hLsub, hl, (hx 1 F7).1, ?_, fun i hi => (hx i hi).2⟩
    intro hm
    exact hb4 _ hm 1 F7 (hx 1 F7).2
  -- eligibility of g
  have helig : (∀ i : Fin 91, X0P.getLsbD i.val = true → differs i (X0v ||| g)) →
      elig g.toNat = true := by
    intro hxd
    have hq : ∀ i : Fin 91, X0P.getLsbD i.val = true → g.getLsbD (91 + i.val) = false := by
      intro i hi
      have hd := hxd i hi
      obtain ⟨e1, e2⟩ := F2 i hi
      unfold differs at hd
      rw [BitVec.getLsbD_or, BitVec.getLsbD_or, e1, e2] at hd
      simpa using hd
    have hz : g &&& QX0v = 0#198 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_and]
      by_cases hm : QX0v.getLsbD j = true
      · obtain ⟨h91, hp⟩ := F3 ⟨j, hj⟩ hm
        simp only [Fin.val_mk] at h91 hp
        have hlt := BitVec.lt_of_getLsbD hp
        have := hq ⟨j - 91, hlt⟩ hp
        have e : 91 + (j - 91) = j := by omega
        simp only [e] at this
        simp [this]
      · simp only [Bool.not_eq_true] at hm
        simp [hm]
    have hz2 : Nat.land g.toNat QX0 = 0 := by
      have := congrArg BitVec.toNat hz
      rw [BitVec.toNat_and, QX0v_toNat] at this
      simpa using this
    obtain ⟨r, hr⟩ := hwit
    have hb : P182 ≤ g.toNat := by
      have h1 : 2 ^ (182 + r.val) ≤ g.toNat := Nat.ge_two_pow_of_testBit hr
      have h2 : 2 ^ 182 ≤ 2 ^ (182 + r.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact le_trans h2 h1
    unfold elig
    rw [brec, if_pos (beq_of_eq hz2)]
    exact Nat.ble_eq_true_of_le hb
  rcases hcase with ⟨hold, hbuild⟩ | ⟨a, ha, b, hb, hab, z, hz, hzout, hgz, hbuild⟩
  · obtain ⟨L, hLsub, hl, hhL, hhav, hxd⟩ := analyze av3 b3 hbuild
    have he := helig hxd
    rcases hold with h0 | h1 | ⟨c, hc, hgc⟩
    · obtain ⟨r, hr⟩ := hwit
      rw [h0] at hr
      simp at hr
    · have := hxd 1 F7
      rw [h1] at this
      revert this
      unfold differs
      decide +kernel
    · let T := insert c (L.erase (X0v ||| g))
      have hTsub : T ⊆ av3 := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hc
        · have hw' := Finset.mem_erase.mp hw
          exact (Finset.mem_insert.mp (hLsub hw'.2)).resolve_left hw'.1
      have hLc := live_card hl
      have hcardE : (L.erase (X0v ||| g)).card + 1 = L.card := Finset.card_erase_add_one hhL
      have hcard : T.card ≤ 6 := by
        have := Finset.card_insert_le c (L.erase (X0v ||| g))
        change (insert c (L.erase (X0v ||| g))).card ≤ 6
        omega
      have hhT : (X0v ||| g) ∉ T := fun hm => hhav (hTsub hm)
      refine finish av3 hreach T hTsub (by omega) ?_ ?_
      · intro i hi
        obtain ⟨w, hw, hd⟩ := live_separates (differs i) (hdT i) (ops_differs i) hl
        by_cases hwh : w = (X0v ||| g)
        · subst hwh
          have hg := or_differs i g hi hd
          refine ⟨c, Finset.mem_insert_self _ _, ?_⟩
          rcases hgc with rfl | rfl
          · exact hg
          · exact (differs_not i c).mp hg
        · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwh, hw⟩), hd⟩
      · intro ws hn hws
        have hlen : ws.length ≤ 6 := by
          rw [← List.toFinset_card_of_nodup hn, hws]
          exact hcard
        have hcw : c ∈ ws := List.mem_toFinset.mp (hws ▸ Finset.mem_insert_self _ _)
        have hgc' : g = c ∨ g = ~~~c := hgc
        refine leaf_old ht ws hn hlen c hcw g hgc' he L hl ?_ (hws ▸ hhT)
        have hL : L = insert (X0v ||| g) (L.erase (X0v ||| g)) := (Finset.insert_erase hhL).symm
        rw [hws]
        by_cases hcL : c ∈ L.erase (X0v ||| g)
        · right
          have : T = L.erase (X0v ||| g) := Finset.insert_eq_of_mem hcL
          rw [this]
          exact hL
        · left
          have : T.erase c = L.erase (X0v ||| g) := Finset.erase_insert hcL
          rw [this]
          exact hL
  · have b4 : ∀ w ∈ insert z av3, Blind w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact bops a b w hz (b3 a ha) (b3 b hb)
      · exact b3 w hw
    obtain ⟨L, hLsub, hl, hhL, hhav, hxd⟩ := analyze (insert z av3) b4 hbuild
    have he := helig hxd
    let needed := (L.erase (X0v ||| g)).erase z
    let T := insert a (insert b needed)
    have hNsub : needed ⊆ av3 := by
      intro w hw
      have hw1 := Finset.mem_erase.mp hw
      have hw2 := Finset.mem_erase.mp hw1.2
      rcases Finset.mem_insert.mp (hLsub hw2.2) with h | h
      · exact absurd h hw2.1
      · exact (Finset.mem_insert.mp h).resolve_left hw1.1
    have hTsub : T ⊆ av3 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ha
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hb
      exact hNsub hw
    have hLc := live_card hl
    have hcardE : (L.erase (X0v ||| g)).card + 1 = L.card := Finset.card_erase_add_one hhL
    have hcardN : needed.card ≤ (L.erase (X0v ||| g)).card := Finset.card_erase_le
    have hcard : T.card ≤ 7 := by
      have h1 := Finset.card_insert_le a (insert b needed)
      have h2 := Finset.card_insert_le b needed
      change (insert a (insert b needed)).card ≤ 7
      omega
    have hhT : (X0v ||| g) ∉ T := fun hm => hhav (Finset.mem_insert_of_mem (hTsub hm))
    have hzT : z ∉ T := fun hm => hzout (hTsub hm)
    have hhz : (X0v ||| g) ≠ z := fun e => hhav (e ▸ Finset.mem_insert_self _ _)
    refine finish av3 hreach T hTsub hcard ?_ ?_
    · intro i hi
      obtain ⟨w, hw, hd⟩ := live_separates (differs i) (hdT i) (ops_differs i) hl
      have viaZ : differs i z → ∃ w ∈ T, differs i w := by
        intro hdz
        rcases ops_differs i a b z hz hdz with h1 | h1
        · exact ⟨a, Finset.mem_insert_self _ _, h1⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h1⟩
      by_cases hwh : w = (X0v ||| g)
      · subst hwh
        have hg := or_differs i g hi hd
        apply viaZ
        rcases hgz with rfl | rfl
        · exact hg
        · exact (differs_not i z).mp hg
      · by_cases hwz : w = z
        · subst hwz
          exact viaZ hd
        · refine ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_), hd⟩
          exact Finset.mem_erase.mpr ⟨hwz, Finset.mem_erase.mpr ⟨hwh, hw⟩⟩
    · intro ws hn hws
      have hL : L = insert (X0v ||| g) (L.erase (X0v ||| g)) := (Finset.insert_erase hhL).symm
      refine leaf_new ht ws hn a b z (by rw [hws]; exact Finset.mem_insert_self _ _)
        (by rw [hws]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hab hz
        (hws ▸ hzT) g hgz he needed hws (hws ▸ hhT) hhz ?_ (fun i hi => or_blind_MH i g hi)
      by_cases hzL : z ∈ L.erase (X0v ||| g)
      · right
        have : insert z needed = L.erase (X0v ||| g) := Finset.insert_erase hzL
        rw [this, ← hL]
        exact hl
      · left
        have : needed = L.erase (X0v ||| g) := Finset.erase_eq_of_notMem hzL
        rw [this, ← hL]
        exact hl


def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem sample_target : ∀ k : Fin 198,
    target (fun i => bit k (primary.getD i.val 0)) = bit k (~~~goal) := by
  decide +kernel

theorem vectors_compute (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x) :
    (runW gs primary).getD out 0 = ~~~goal := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 198 := ⟨j,hj⟩
  change bit k ((runW gs primary).getD out 0) = bit k (~~~goal)
  rw [← read_bit, runW_bits gs primary hg k]
  let x (i : Fin 7) := bit k (primary.getD i.val 0)
  have same : List.ofFn x = primary.map (bit k) := by
    apply List.ext_getElem
    · simp [primary, srcL]
    · intro i hi hj
      have hlt : i < primary.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [← same]
  change Circuit.eval ⟨gs,out⟩ (List.ofFn x) = _
  rw [he]
  exact sample_target k

def witIn (r : Fin 16) (i : Fin 7) : Bool :=
  if 2 ≤ i.val ∧ i.val ≤ 5 then r.val.testBit (i.val - 2) else false

set_option maxRecDepth 32000 in
theorem wit_table : ∀ r : Fin 16, ∀ i : Fin 7,
    bit ⟨182 + r.val, by omega⟩ (primary.getD i.val 0) = witIn r i := by
  decide +kernel

set_option maxRecDepth 32000 in
theorem wit_key : ∀ b2 b3 b4 b5 : Bool, ∃ r : Fin 16, witIn r 2 = b2 ∧ witIn r 3 = b3 ∧
    witIn r 4 = b4 ∧ witIn r 5 = b5 ∧ witIn r 0 = false ∧ witIn r 1 = false ∧
    witIn r 6 = false := by
  decide +kernel

theorem wit_points (x : Fin 7 → Bool) (h0 : x 0 = false) (h1 : x 1 = false) (h6 : x 6 = false) :
    ∃ r : Fin 16, ∀ i : Fin 7, x i = bit ⟨182 + r.val, by omega⟩ (primary.getD i.val 0) := by
  obtain ⟨r, e2, e3, e4, e5, e0, e1, e6⟩ := wit_key (x 2) (x 3) (x 4) (x 5)
  refine ⟨r, fun i => ?_⟩
  rw [wit_table]
  match i with
  | ⟨0, _⟩ => exact h0.trans e0.symm
  | ⟨1, _⟩ => exact h1.trans e1.symm
  | ⟨2, _⟩ => exact e2.symm
  | ⟨3, _⟩ => exact e3.symm
  | ⟨4, _⟩ => exact e4.symm
  | ⟨5, _⟩ => exact e5.symm
  | ⟨6, _⟩ => exact h6.trans e6.symm

theorem witness_bit (gs : List Gate) (out : ℕ) (hg : ∀ a ∈ gs, legal a) (x : Fin 7 → Bool)
    (h0 : x 0 = false) (h1 : x 1 = false) (h6 : x 6 = false)
    (hx : (Circuit.wires ⟨gs, out⟩ (List.ofFn x)).getD 10 false = true) :
    ∃ r : Fin 16, ((runW gs primary).getD 10 0).getLsbD (182 + r.val) = true := by
  obtain ⟨r, hr⟩ := wit_points x h0 h1 h6
  refine ⟨r, ?_⟩
  let k : Fin 198 := ⟨182 + r.val, by omega⟩
  have same : List.ofFn x = primary.map (bit k) := by
    apply List.ext_getElem
    · simp [primary, srcL]
    · intro i hi hj
      have hlt : i < primary.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
      have := hr ⟨i, by simpa using hi⟩
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt] using this
  have hb : bit k ((runW gs primary).getD 10 0) = true := by
    rw [← read_bit, runW_bits gs primary hg k, ← same]
    exact hx
  rw [BitVec.getLsbD_eq_getElem (by omega)]
  exact hb

theorem two_inputs (g : Gate) (hg : legal g) (h0 : 0 ∈ g.inputs) (h10 : 10 ∈ g.inputs) :
    g.inputs = [0,10] ∨ g.inputs = [10,0] := by
  obtain ⟨op,args⟩ := g
  have cap : args.length ≤ 2 := hg.2
  rcases args with _|⟨a,_|⟨b,_|⟨c,tail⟩⟩⟩ <;> simp_all
  all_goals omega

theorem initial_holds : ∀ i, i ≠ 0 → holds srcL.toFinset (primary.getD i 0) := by
  intro i hi
  by_cases hb : i < 7
  · refine .inr (.inr ⟨primary.getD i 0, ?_, .inl rfl⟩)
    rw [List.mem_toFinset]
    interval_cases i <;> simp_all [primary, srcL]
  · rw [List.getD_eq_default _ _ (by simpa [primary, srcL] using Nat.le_of_not_gt hb)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem impossible (gs : List Gate) (out : ℕ)
    (hlen : gs.length = 10)
    (hg : ∀ a ∈ gs, legal a)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,out⟩ (List.ofFn x) = target x)
    (hr : ∀ j < gs.length, j ≠ 4 → 0 ∉ (gs.getD j emptyGate).inputs)
    (hop : (gs.getD 4 emptyGate).op = .or)
    (hargs : (gs.getD 4 emptyGate).inputs = [0,10] ∨ (gs.getD 4 emptyGate).inputs = [10,0])
    (x : Fin 7 → Bool) (h0 : x 0 = false) (h1 : x 1 = false) (h6 : x 6 = false)
    (hx : (Circuit.wires ⟨gs, out⟩ (List.ofFn x)).getD 10 false = true) : False := by
  have hev := vectors_compute gs out hg he
  have hwit := witness_bit gs out hg x h0 h1 h6 hx
  have hout : out ≠ 0 := by
    intro e
    subst out
    rw [runW_stable _ _ _ (by decide +kernel)] at hev
    exact (ne_of_bit 91 (by decide +kernel) : primary.getD 0 0 ≠ ~~~goal) hev
  obtain ⟨g0, g1, g2, g3, g4, rest, rfl⟩ :
      ∃ g0 g1 g2 g3 g4 rest, gs = g0 :: g1 :: g2 :: g3 :: g4 :: rest := by
    match gs, hlen with
    | g0 :: g1 :: g2 :: g3 :: g4 :: rest, _ => exact ⟨g0, g1, g2, g3, g4, rest, rfl⟩
  have hrest : rest.length = 5 := by simpa using hlen
  have hr0 : ∀ j, j < 10 → j ≠ 4 →
      0 ∉ ((g0 :: g1 :: g2 :: g3 :: g4 :: rest).getD j emptyGate).inputs := by
    intro j hj hne
    exact hr j (by simp; omega) hne
  have hpre : ∀ g ∈ [g0, g1, g2], 0 ∉ g.inputs := by
    intro g hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl
    · simpa using hr0 0 (by omega) (by omega)
    · simpa using hr0 1 (by omega) (by omega)
    · simpa using hr0 2 (by omega) (by omega)
  have hpost : ∀ g ∈ rest, 0 ∉ g.inputs := by
    intro g hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
    have := hr0 (j + 5) (by omega) (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using this
  have hg3 : 0 ∉ g3.inputs := by simpa using hr0 3 (by omega) (by omega)
  have legal_of : ∀ a ∈ (g0 :: g1 :: g2 :: g3 :: g4 :: rest), legal a := hg
  -- the first three gates
  obtain ⟨av3, hR3, hw3⟩ := chain [g0, g1, g2] primary srcL.toFinset
    (fun a ha => legal_of a (by simp at ha; rcases ha with rfl | rfl | rfl <;> simp))
    initial_holds hpre
  let w3 := runW [g0, g1, g2] primary
  have hw3len : w3.length = 10 := by
    simp only [w3, runW_length]; simp [primary, srcL]
  let gv := action w3 g3
  have reach3 := gate_reach_reads w3 av3 g3 (legal_of g3 (by simp))
    (fun i hi => hw3 i (fun eq => hg3 (eq ▸ hi)))
  let w4 := w3 ++ [gv]
  have r0 : w4.getD 0 0 = X0v := by
    simp only [w4]
    rw [List.getD_append _ _ _ _ (by omega)]
    simp only [w3]
    rw [runW_stable _ _ _ (by simp [primary])]
    rfl
  have r10 : w4.getD 10 0 = gv := by
    simp only [w4]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hw3len]
  have hv : action w4 g4 = X0v ||| gv := by
    have hop' : g4.op = .or := by simpa using hop
    have hargs' : g4.inputs = [0,10] ∨ g4.inputs = [10,0] := by simpa using hargs
    rcases hargs' with ha | ha <;>
      simp only [action, hop', ha, List.map_cons, List.map_nil,
        List.foldr_cons, List.foldr_nil, r0, r10,
        show ∀ a : W, a ||| (0 : W) = a from fun a => BitVec.or_zero]
    exact BitVec.or_comm _ _
  let w5 := w4 ++ [X0v ||| gv]
  have hrun : runW (g0 :: g1 :: g2 :: g3 :: g4 :: rest) primary = runW rest w5 := by
    change runW rest (w4 ++ [action w4 g4]) = _
    rw [hv]
  have hg10 : (runW (g0 :: g1 :: g2 :: g3 :: g4 :: rest) primary).getD 10 0 = gv := by
    rw [hrun]
    simp only [w5]
    rw [runW_stable _ _ _ (by simp [w4, hw3len]), List.getD_append _ _ _ _ (by simp [w4, hw3len])]
    exact r10
  rw [hg10] at hwit
  rw [hrun] at hev
  have hwlen4 : w4.length = 11 := by simp [w4, hw3len]
  have holds5 : ∀ av4 : Finset W, av3 ⊆ av4 → holds av4 gv →
      ∀ i, i ≠ 0 → holds (insert (X0v ||| gv) av4) (w5.getD i 0) := by
    intro av4 hsub hgv i hi
    have hw4 : ∀ i, i ≠ 0 → holds av4 (w4.getD i 0) :=
      holds_append w3 av4 gv (fun i hi => holds_mono hsub (hw3 i hi)) hgv
    exact holds_append w4 (insert (X0v ||| gv) av4) (X0v ||| gv)
      (fun i hi => holds_mono (Finset.subset_insert _ _) (hw4 i hi))
      (.inr (.inr ⟨_, Finset.mem_insert_self _ _, .inl rfl⟩)) i hi
  have legal_rest : ∀ a ∈ rest, legal a := fun a ha => legal_of a (by simp [ha])
  rcases gate3_cases reach3 with hold | ⟨a, ha, b, hb, hab, z, hz, hzout, hgz⟩
  · obtain ⟨t, ht, hbuild⟩ := compile_plain rest out w5 (insert (X0v ||| gv) av3) legal_rest hout
      (holds5 av3 (fun _ h => h) hold) hpost hev
    rw [hrest] at hbuild
    exact core av3 hR3 gv hwit t ht (.inl ⟨hold, hbuild⟩)
  · have hgvz : holds (insert z av3) gv := .inr (.inr ⟨z, Finset.mem_insert_self _ _, hgz⟩)
    obtain ⟨t, ht, hbuild⟩ := compile_plain rest out w5 (insert (X0v ||| gv) (insert z av3))
      legal_rest hout (holds5 (insert z av3) (Finset.subset_insert _ _) hgvz) hpost hev
    rw [hrest] at hbuild
    exact core av3 hR3 gv hwit t ht (.inr ⟨a, ha, b, hb, hab, z, hz, hzout, hgz, hbuild⟩)

end PEqualNP.Outside.L_meta_29842_aux

theorem PEqualNP.Outside.L_meta_29842 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 4 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 10 ∈ (C.gates.get i).inputs ∧ 10 ≠ 0 ∧ 10 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 10 false = true) := by
  rintro ⟨⟨gates,out⟩,i,k,hi,hfan,hsize,he,h0,honly,hop,hkop,hik,hki,h10,h100,h10i,x,hx0,hx1,hx6,hx⟩
  have hlen : gates.length = 10 := hsize
  have hg : ∀ a ∈ gates, PEqualNP.Outside.L_meta_29842_aux.legal a := by
    intro a ha
    obtain ⟨ops,len⟩ := hfan a ha
    exact ⟨by simpa using ops,len⟩
  have hget (j : Fin gates.length) :
      gates.get j = gates.getD j.val PEqualNP.Outside.L_meta_29842_aux.emptyGate := by
    simp only [List.get_eq_getElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem j.isLt, Option.getD_some]
  have hgi : gates.get i = gates.getD 4 PEqualNP.Outside.L_meta_29842_aux.emptyGate := by
    rw [hget,hi]
  have hr : ∀ j < gates.length, j ≠ 4 →
      0 ∉ (gates.getD j PEqualNP.Outside.L_meta_29842_aux.emptyGate).inputs := by
    intro j hj hne hm
    have hmem : 0 ∈ (gates.get ⟨j,hj⟩).inputs := by
      rw [hget]
      exact hm
    have heq := honly ⟨j,hj⟩ hmem
    have hv := congrArg Fin.val heq
    simp only [hi] at hv
    exact hne hv
  change (gates.get i).op = _ at hop
  change 0 ∈ (gates.get i).inputs at h0
  change 10 ∈ (gates.get i).inputs at h10
  rw [hgi] at hop h0 h10
  have hlegal4 : PEqualNP.Outside.L_meta_29842_aux.legal
      (gates.getD 4 PEqualNP.Outside.L_meta_29842_aux.emptyGate) := by
    rw [← hgi]
    exact hg _ (List.get_mem ..)
  have hargs := PEqualNP.Outside.L_meta_29842_aux.two_inputs _ hlegal4 h0 h10
  have het : ∀ x : Fin 7 → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates,out⟩ (List.ofFn x) =
        PEqualNP.Outside.L_meta_29842_aux.target x := he
  exact PEqualNP.Outside.L_meta_29842_aux.impossible gates out hlen hg het hr hop hargs
    x hx0 hx1 hx6 hx
