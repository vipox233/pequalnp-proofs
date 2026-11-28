import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45300

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
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
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

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
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276677312 * 2 ^ 32 + 4238928000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x030d8af088361b60#64 ++ 0x50186c578441b0db#64 ++ 0x071f9ff088fe3ff7#64 ++ 0xd038fcff8447f1ff#64 : BitVec 256),
   (0x1862a617038ac5a0#64 ++ 0x20c31530b81c562d#64 ++ 0x38e3e63f0f8fc7fb#64 ++ 0xf1c71f31f87c7e3f#64 : BitVec 256),
   (0xc0b4582b30d168c1#64 ++ 0x0605a2c159868b46#64 ++ 0xc0fc783ff0f1f8fd#64 ++ 0xfe07e3c1ff878fc7#64 : BitVec 256),
   (0x6d007540dd01b602#64 ++ 0x0b6803aa06e80db0#64 ++ 0xff007fc1ff01ff1f#64 ++ 0x7ff803fe0ff80ff8#64 : BitVec 256),
   (0xb7fb0001eeec0004#64 ++ 0x8dbfd8000f776000#64 ++ 0xffff8001fffe001f#64 ++ 0xaffffc000ffff000#64 : BitVec 256),
   (0xfedfffbc00000008#64 ++ 0xcff6fffde0000000#64 ++ 0xfffffffe0000001e#64 ++ 0xcffffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [9, 5]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f9ff088fe3ff7 0xd038fcff8447f1ff

def z1 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e63f0f8fc7fb 0xf1c71f31f87c7e3f

def z2 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff007fc1ff01ff1f 0x7ff803fe0ff80ff8

def z3 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff8001fffe001f 0xaffffc000ffff000

def z4 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc783ff0f1f8fd 0xfe07e3c1ff878fc7

def z5 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffe0000001e 0xcffffffff0000000

def z6 : W := mkw 0xfedfffbc00020128 0xcff6fffde0001009 0xfffffffe088e07ff 0xdffffffff044703f

def z7 : W := mkw 0x374b0000ce2c0004 0x89ba580006716000 0x3f0380000f0e0002 0x01f81c0000787000

def z8 : W := mkw 0xbffba617efeec5a4 0xadffdd30bf7f762d 0xffffe63fffffc7ff 0xffffff31fffffe3f

def z9 : W := mkw 0xb7fb0003eeec4084 0x8dbfd8001f776204 0xffffe03fffffc0ff 0xffffff01fffffe07

def z10 : W := mkw 0x25000000cc000000 0x0928000006600000 0xff000001ff00001f 0x2ff800000ff80000

def z11 : W := mkw 0xfffb7541ffedb606 0x8fffdbaa0fff6db0 0xffffffc1ffffff1f 0xfffffffe0ffffff8

def z12 : W := mkw 0x030d8ab088360960 0x50186c558441b04b 0x071f803088fe00f7 0x8038fc018447f007

def z13 : W := mkw 0x020d8ab000000000 0x40106c5580000000 0x071f9ff000000016 0xc038fcff80000000

def z14 : W := mkw 0xffdffffc88361b68 0xdffeffffe441b0db 0xfffffffe88fe3fff 0xdffffffff447f1ff

def z15 : W := mkw 0x3e4ba79400000008 0xc9f25d3ca0000000 0x3f0387c000000002 0x01f81c3e00000000

def z16 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x00e3e63e008fc7e0 0xd0071f31f0047e3f

def z17 : W := mkw 0x01200043fdd1fec3 0x000900021fee8ff6 0x00000001fff1ffe1 0x300000000fff8fff

def z18 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x001f803088fe3fe1 0x9000fc018447f1ff

def z19 : W := mkw 0x10628217028a41a0 0x20831410b814520d 0x00e3803e008e00e0 0x80071c01f0047007

def z20 : W := mkw 0x65005140dc013202 0x0b28028a06e00990 0xc70019c0f0003804 0x0e3800ce078001c0

def z21 : W := mkw 0xa7b90001eeec0004 0x8d3dc8000f776000 0xc71c0001fffe0005 0x2e38e0000ffff000

def z22 : W := mkw 0x3f4b2540cf2c9606 0x89fa592a067964b0 0x3f0387c00f0e0702 0x01f81c3e00787038

def z23 : W := mkw 0x0000821000020120 0x0000041080001009 0x00038630088e07f3 0xd0001c318044703f

def z24 : W := mkw 0x1b6faef78bbedfe0 0x70db7d77bc5df6ff 0x3fffffff8fffffff 0xf1fffffffc7fffff

def z25 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e0663f0701c7e8 0x71c70331f8380e3f

def z26 : W := mkw 0x0004082000100840 0x0000204100008042 0x001c183080f038f5 0xd000e0c1840781c7

def z27 : W := mkw 0x030982d088261320 0x50184c1684413099 0x070387c0080e0702 0x00381c3e00407038

def z28 : W := mkw 0xfeffffbf00804088 0xcff7fffdf8040204 0xffffffff0081c0ff 0xfffffffff8040e07

def z29 : W := mkw 0x0020000300804080 0x0001000018040204 0x00e0603f0081c0f9 0xf0070301f8040e07

def z30 : W := mkw 0xd8f6fe3f33dbede1 0x26c7b7f1f99edf6f 0xf8fffe3fffffffff 0xffc7fff1ffffffff

def z31 : W := mkw 0x000408e000101a40 0x50002047000080d2 0x000019c000003800 0x000000ce000001c0

def z32 : W := mkw 0xc2bddabb30f769e1 0x5615eed5d987bb4f 0xc0fff83ff0fff8fd 0xfe07ffc1ff87ffc7

def z33 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff001fc0ff003f06 0x0ff800fe07f801f8

def z34 : W := mkw 0x270d8af0cc361b60 0x59386c578661b0db 0xff1f9ff1fffe3fff 0xfff8fcff8ffff1ff

def z35 : W := mkw 0x1862a61733dbede1 0x20c31530b99edf6f 0x38e3e63ffffffffb 0xf1c71f31ffffffff

def z36 : W := mkw 0xbfffaef7effedfe4 0xfdfffd77bf7ff6ff 0xffffffffffffffff 0xffffffffffffffff

def z37 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3863e0f8e07e2 0x81c71c31f07c703f

def z38 : W := mkw 0x2f0daff0cd369f62 0x59786d7f8669b4fb 0x3f1f9ff08ffe3ff7 0xd1f8fcff847ff1ff

def z39 : W := mkw 0x7e4bf79400000008 0xcbf25fbca0000000 0xff03ffc00000001e 0x4ff81ffe00000000

def z40 : W := mkw 0x7f4b7540df2db606 0x8bfa5baa06f96db0 0xff03ffc1ff0fff1f 0x7ff81ffe0ff87ff8

def z41 : W := mkw 0x6d207543fdd1fec3 0x0b6903aa1fee8ff6 0xff007fc1fff1ffff 0x7ff803fe0fff8fff

def z42 : W := mkw 0x5866ffbf038ac5a8 0x62c337fdf81c562d 0x38e3ffff0f8fc7fb 0xf1c71ffff87c7e3f

def z43 : W := mkw 0x186224070388c480 0x20c31120381c4624 0x38e3e00f0f8fc01b 0xa1c71f00787c7e00

def z44 : W := mkw 0x4004582a101168c1 0x020022c150808b46 0x001c783e80f1f8f5 0xd000e3c1f4078fc7

def z45 : W := mkw 0x6d007540dd37bf62 0x1b6803aa06e9bdfb 0xff007fc1ffffffff 0x7ff803fe0fffffff

def z46 : W := mkw 0x0800a6160102c5a0 0x20400530b008162d 0x0000663e0001c7e0 0x50000331f0000e3f

def z47 : W := mkw 0xa7990000ec640004 0x8d3cc80007632000 0xc71c0000f0700004 0x0e38e00007838000

def z48 : W := mkw 0xe69d59a800000008 0xcf34eacd40000000 0xc7fc79fe0000001c 0xce3fe3cff0000000

def z49 : W := mkw 0x4020500310816080 0x0201028018840b04 0xc0e0783ff081f8fd 0xfe0703c1ff840fc7

def z50 : W := mkw 0x032d8af38bbedfe0 0x70196c579c5df6ff 0x071f9ff18ffffff7 0xf038fcff8c7fffff

def z51 : W := mkw 0x0800254001009602 0x0040012a000804b0 0x000007c000000700 0x0000003e00000038

def z52 : W := mkw 0x1866ae37039acde0 0x20c33571b81cd66f 0x38fffe3f8fffffff 0xf1c7fff1fc7fffff

def z53 : W := mkw 0x0800240001008400 0x0040012000080420 0x380066010f01c71b 0x71c0033008780e38

def z54 : W := mkw 0x7c42f71400000000 0x0be217b8a0000000 0xffe3fffe0000001e 0xcfff1ffff0000000

def z55 : W := mkw 0x7d62f757df8bf7a2 0x2beb17babefc5fbd 0xffe3ffffff8fffff 0xffff1ffffffc7fff

def z56 : W := mkw 0x1842a614030a8520 0x20c21530a0185429 0x380386000f0e0702 0x01c01c3000787038

def z57 : W := mkw 0xef9d7de8dd01b60a 0xcf7cebef46e80db0 0xff1c7fc1ff01ff1f 0x7ff8e3fe0ff80ff8

def z58 : W := mkw 0xc094582800000000 0x0604a2c140000000 0xc0fc783e0000001c 0xce07e3c1f0000000

def z59 : W := mkw 0xfeffffbf30d168c9 0xcff7fffdf9868b46 0xfffffffff0f1f8ff 0xffffffffff878fc7

def z60 : W := mkw 0x00048af000121b60 0x50002457800090db 0x00001ff000003fe0 0x500000ff800001ff

def z61 : W := mkw 0xc0b0500b30c16081 0x0605828059860b04 0xc0e0600f7001c008 0x2e0703007b800e00

def z62 : W := mkw 0xc3bddafbb8f77be1 0x561deed7ddc7bbdf 0xc7fffffff8ffffff 0xfe3fffffffc7ffff

def z63 : W := mkw 0x01000040dc013202 0x0008000206e00990 0x00000000f0003800 0x00000000078001c0

def z64 : W := mkw 0xb7ff8ab1eeec0004 0xcdbffc558f776000 0xffff9ff1fffe001f 0xeffffcff8ffff000

def z65 : W := mkw 0x92db000000000000 0x8496d80000000000 0x00ff800000000000 0x8007fc0000000000

def z66 : W := mkw 0xffdffffcdd01b60a 0xcffeffffe6e80db0 0xffffffffff01ff1f 0xfffffffffff80ff8

def z67 : W := mkw 0x0000821000000000 0x0000041080000000 0x0003863000000012 0xc0001c3180000000

def z68 : W := mkw 0x4804fff01113bf62 0x524027ff80889dfb 0x00007ff00001ffe0 0x500003ff80000fff

def z69 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0e0783f7001f8e8 0x7e0703c1fb800fc7

def z70 : W := mkw 0x6d007500dd01a402 0x0b6803a806e80d20 0xff006001ff01c01f 0x2ff803000ff80e00

def z71 : W := mkw 0xfedfffbc030a8528 0xeff6fffde0185429 0xfffffffe0f0e071e 0xcffffffff0787038

def z72 : W := mkw 0x92ff082b22fc48c5 0x8497f8415917e246 0x00ff803e00fe00e0 0x8007fc01f007f007

def z73 : W := mkw 0xe69d59a830512849 0xcf34eacd41828942 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z74 : W := mkw 0xb6fb000120c00000 0x8db7d80009060000 0xffff8001f0f0001f 0xaffffc000f878000

def z75 : W := mkw 0x0804aef60112dfe0 0x70402577b00896ff 0x00007ffe0001ffe0 0x500003fff0000fff

def z76 : W := mkw 0xffdffffc88261328 0xdffeffffe4413099 0xfffffffe080e071e 0xcffffffff0407038

def z77 : W := mkw 0x374b0000ce2c0004 0x89ba580006716000 0x3f1f80008ffe0017 0x81f8fc00047ff000

def z78 : W := mkw 0xfcd2750c00000008 0x8fe693a860000000 0xf8e0600e00000008 0x0fc7030070000000

def z79 : W := mkw 0xfeffffbf038ac5a8 0xeff7fffdf81c562d 0xffffffff0f8fc7ff 0xfffffffff87c7e3f

def z80 : W := mkw 0xc094582810012000 0x0604a2c140800900 0xc0fc783ff001f81d 0xfe07e3c1ff800fc0

def z81 : W := mkw 0x364b000000000000 0x89b2580000000000 0x3f03800000000002 0x01f81c0000000000

def z82 : W := mkw 0x6c00750010012000 0x0b6003a800800900 0xff007fc1f001f81f 0x7ff803fe0f800fc0

def z83 : W := mkw 0x0100004088001200 0x0008000204400090 0x07001fc088003f17 0x503800fe044001f8

def z84 : W := mkw 0x6f0dfff0dd37bf62 0x5b786fff86e9bdfb 0xff1ffff1ffffffff 0xfff8ffff8fffffff

def z85 : W := mkw 0x1842a614030a8520 0x20c21530a0185429 0x380386300f8e07f3 0xd1c01c31807c703f

def z86 : W := mkw 0xd8d6fe3c00000000 0x06c6b7f1e0000000 0xf8fffe3e0000001e 0xcfc7fff1f0000000

def z87 : W := mkw 0x6f097540dd25b602 0x0b784baa06e92db0 0xff1fffc1ffffff1f 0xfff8fffe0ffffff8

def z88 : W := mkw 0x1a4faeb400000000 0x40d27d75a0000000 0x3ffffffe0000001e 0xc1fffffff0000000

def z89 : W := mkw 0xc094582830512841 0x0604a2c141828942 0xc01c1800f0703804 0x0e00e0c0078381c0

def z90 : W := mkw 0x430ddaf098373b60 0x52186ed784c1b9db 0xc71ffff1f8ffffff 0xfe38ffff8fc7ffff

def z91 : W := mkw 0x4000500010012000 0x0200028000800900 0xc0007801f001f81d 0x7e0003c00f800fc0

def z92 : W := mkw 0xbedfafbc00000008 0xcdf6fd7de0000000 0x3fff87fe00000002 0x81fffc3ff0000000

def z93 : W := mkw 0xb6db000000000000 0x8db6d80000000000 0xffff80000000001e 0x8ffffc0000000000

def z94 : W := mkw 0xe79d59a8ec64000c 0xcf3ceacd47632000 0xc71c19c0f0700004 0x0e38e0ce07838000

def z95 : W := mkw 0xfeffffbf0388c488 0xeff7fffdf81c4624 0xffffffff0701c01e 0xeffffffff8380e00

def z96 : W := mkw 0x18622407038ac5a0 0x20c31120381c562d 0x38e0600f0f8fc7e9 0x31c70300787c7e3f

def z97 : W := mkw 0x8299000020640004 0x8414c80001032000 0x001c000000700000 0x0000e00000038000

def z98 : W := mkw 0x01200043df8bf7a2 0x200900021efc5fbd 0x00000001ff8fffe1 0x300000000ffc7fff

def z99 : W := mkw 0x4b0dfff09937bf62 0x52586fff84c9bdfb 0x071ffff088fffff7 0xd038ffff8447ffff

def z100 : W := mkw 0xb4f2000166c80004 0x8da790000b364000 0xf8e0000177000008 0x2fc700000bb80000

def z101 : W := mkw 0x00208213008241a0 0x000104109804120d 0x00e3e63f088fc7fb 0xf0071f31f8447e3f

def z102 : W := mkw 0xbedba61400000000 0x8df6dd30a0000000 0xffffe63e0000001e 0xcfffff31f0000000

def z103 : W := mkw 0x93fb0001eeec0004 0x849fd8000f776000 0x00ff8001fffe0001 0xa007fc000ffff000

def z104 : W := mkw 0xb7fb82d1eeee1324 0xddbfdc168f777099 0xffff87c1fffe071f 0xaffffc3e0ffff038

def z105 : W := mkw 0x00208213038ac5a0 0x20010410981c562d 0x000386310f8fc7f3 0xf0001c31887c7e3f

def z106 : W := mkw 0xfedfffbc01008408 0xcff6fffde0080420 0xffffffff0f01c71f 0xfffffffff8780e38

def z107 : W := mkw 0xfdf6ff7fffdbffe3 0x2fefb7fbfffedfff 0xffffffffffffffff 0xffffffffffffffff

def z108 : W := mkw 0x4004582a101168c1 0x020022c150808b46 0x0000783e0001f8e0 0x500003c1f0000fc7

def z109 : W := mkw 0xc0b0500b30d168c1 0x0605828059868b46 0xc0e0600ff0f1f8e9 0x3e0703007f878fc7

def z110 : W := mkw 0x00200003038ac5a0 0x20010000181c562d 0x000000010f8fc7e1 0x30000000087c7e3f

def z111 : W := mkw 0x1842a61400000000 0x00c21530a0000000 0x38e3e63e0000001a 0xc1c71f31f0000000

def z112 : W := mkw 0x3e6ba797038ac5a8 0xe9f35d3cb81c562d 0x3fe3e7ff0f8fc7fb 0xf1ff1f3ff87c7e3f

def z113 : W := mkw 0x0004082000100840 0x0000204100008042 0x001c003000f000e0 0x8000e00180078007

def z114 : W := mkw 0x01200043b8f77be1 0x100900021dc7bbdf 0x00000001f8ffffe1 0x300000000fc7ffff

def z115 : W := mkw 0xbffba795eeec000c 0xcdffdd3caf776000 0xffff87c1fffe001f 0xaffffc3e0ffff000

def z116 : W := mkw 0x10428214020a0120 0x20821410a0105009 0x00038000000e0000 0x00001c0000007000

def z117 : W := mkw 0xfedfffbc30512849 0xcff6fffde1828942 0xfffffffef070381e 0xcffffffff78381c0

def z118 : W := mkw 0xbffb2541efec9606 0x8dffd92a0f7f64b0 0xffff87c1fffe071f 0xaffffc3e0ffff038

def z119 : W := mkw 0x83bd8afba8f65be1 0x541dec57dd47b2df 0x07ff9ffe88fe3ff7 0xd03ffcfff447f1ff

def z120 : W := mkw 0x0100004088361b60 0x100800020441b0db 0x0000000088fe3fe1 0x100000000447f1ff

def z121 : W := mkw 0xa79d8af0ec761b64 0xdd3cec578763b0db 0xc71f9ff0f8fe3ff7 0xde38fcff87c7f1ff

def z122 : W := mkw 0x186224070388c480 0x20c31120381c4624 0x38e0600f0701c008 0x21c7030078380e00

def z123 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xf8ffe03e00000008 0x8fc7ff01f0000000

def z124 : W := mkw 0xffdffffcdc01320a 0xcffeffffe6e00990 0xfffffffef000381e 0xcffffffff78001c0

def z125 : W := mkw 0x0020000100800000 0x0001000008040000 0x00e0000100800019 0xa007000008040000

def z126 : W := mkw 0x01048af088361b60 0x500824578441b0db 0x00001ff088fe3fe1 0x500000ff8447f1ff

def z127 : W := mkw 0x0020000166c80004 0x000100000b364000 0x0000000177000000 0x200000000bb80000

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000180080003815 0x500000c0040001c0

def z129 : W := mkw 0x670d59e0dc353a42 0x5b386acf06e1a9d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z130 : W := mkw 0x7d42f754df0bb722 0x2bea17baa6f85db9 0xff03ffc1ff0fff1f 0x7ff81ffe0ff87ff8

def z131 : W := mkw 0xb7db0000ec640004 0x8dbed80007632000 0xffff8000f070001e 0x8ffffc0007838000

def z132 : W := mkw 0x2d002540cd009602 0x0968012a066804b0 0x3f0007c00f000702 0x01f8003e00780038

def z133 : W := mkw 0xedb47d6bfdd1fec3 0x0f6da3eb5fee8ff6 0xfffc7ffffff1ffff 0xffffe3ffffff8fff

def z134 : W := mkw 0x80b4082120d00840 0x0405a04109068042 0xc0fc1831f0f038fd 0xfe07e0c18f8781c7

def z135 : W := mkw 0xfedbf79c00000008 0xcff6dfbce0000000 0xffe3e7ce0000000a 0x0fff1f3e70000000

def z136 : W := mkw 0x9adfaebc00000008 0xc4d6fd75e0000000 0x38ffe63e0000001a 0xc1c7ff31f0000000

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z138 : W := mkw 0xc29ddab800000000 0x4614eed5c0000000 0xc7fffffe0000001e 0xce3ffffff0000000

def z139 : W := mkw 0x0800240000000000 0x0040012000000000 0x380066000000001a 0x41c0033000000000

def z140 : W := mkw 0xb7fb0003efeec5a4 0xadbfd8001f7f762d 0xffff8001ffffc7ff 0xbffffc000ffffe3f

def z141 : W := mkw 0xfeffffbf20d048c9 0xcff7fffdf9068246 0xfffffffe00f000fe 0xcffffffff0078007

def z142 : W := mkw 0x030d8ab088240000 0x40186c5584412000 0x071f9ff088fe0017 0xc038fcff8447f000

def z143 : W := mkw 0x93ff8af1aafe1b64 0xd49ffc578d57f0db 0x07ff9ff088fe3ff7 0xd03ffcff8447f1ff

def z144 : W := mkw 0x020d08a000000000 0x4010684500000000 0x071c19c000000004 0x0038e0ce00000000

def z145 : W := mkw 0xc094582830512841 0x0604a2c141828942 0xc0fc783ef070381c 0xce07e3c1f78381c0

def z146 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e03f078fc0e8 0xa1c71f01f83c7e07

def z147 : W := mkw 0x90f2000122c80000 0x0487900009164000 0xf8ff8001fffe001f 0xafc7fc000ffff000

def z148 : W := mkw 0x030d08e088341a40 0x501868470441a0d2 0x071c19f080f038f5 0xd038e0cf840781c7

def z149 : W := mkw 0xe6bd59ab30d168c9 0xcf35eacd59868b46 0xc7fc79fff0f1f8fd 0xfe3fe3cfff878fc7

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x00038000088e0013 0x80001c0000447000

def z151 : W := mkw 0xc090500800000000 0x0604828040000000 0xc0e0600e00000008 0x0e07030070000000

def z152 : W := mkw 0x7d42f754dd01b602 0x0bea17baa6e80db0 0xffe3ffffff01ff1f 0xffff1ffffff80ff8

def z153 : W := mkw 0xb5f20001eec80004 0x8daf90000f764000 0xffe00001ff00001f 0x2fff00000ff80000

def z154 : W := mkw 0x80b4082b20d048c1 0x0405a04159068246 0xc0fc003ff0f000fd 0xae07e001ff878007

def z155 : W := mkw 0x0020000122ec0004 0x0001000009176000 0x0000000000fe0000 0x000000000007f000

def z156 : W := mkw 0x80b4082b20d048c1 0x0405a04159068246 0x00fc003e00f000e0 0x8007e001f0078007

def z157 : W := mkw 0x01000000ce2c0004 0x0008000006716000 0x000000000f0e0000 0x0000000000787000

def z158 : W := mkw 0x030982d088361b60 0x50184c168441b0db 0x070387c088fe3fe3 0x10381c3e0447f1ff

def z159 : W := mkw 0x020d8ab000360960 0x50106c558001b04b 0x001f803000fe00e0 0x8000fc018007f007

def z160 : W := mkw 0xfedfffbc00360968 0xdff6fffde001b04b 0xfffffffe00fe00fe 0xcffffffff007f007

def z161 : W := mkw 0x90f68a3f22da49e1 0x2487b451f916d24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z162 : W := mkw 0x01000000cc000000 0x0008000006600000 0x00000001ff000001 0x200000000ff80000

def z163 : W := mkw 0x480075401101b602 0x024003aa00880db0 0xc0007fc1f001ff1d 0x7e0003fe0f800ff8

def z164 : W := mkw 0x4804ffbe101168c9 0x424027fdf0808b46 0x00007ffe0001f8e0 0x500003fff0000fc7

def z165 : W := mkw 0x0000821000020120 0x0000041080001009 0x00000630000007e0 0x500000318000003f

def z166 : W := mkw 0x4000500a10016081 0x0200028050800b04 0x0000600e0001c000 0x0000030070000e00

def z167 : W := mkw 0x0800a6160102c5a0 0x20400530b008162d 0x0003e63e088fc7f3 0xd0001f31f0447e3f

def z168 : W := mkw 0xfedffffc1101b60a 0xcff6ffffe0880db0 0xfffffffe0001ff1e 0xdffffffff0000ff8

def z169 : W := mkw 0x1062000102880000 0x0083100008144000 0x38e380010f8e001b 0xa1c71c00087c7000

def z170 : W := mkw 0xe69d59a800000008 0xcf34eacd40000000 0xc71c19c000000004 0x0e38e0ce00000000

def z171 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xc7ff8000f0fe0004 0x8e3ffc000787f000

def z172 : W := mkw 0xfffbf757ffeff7a6 0xafffdfbabfff7fbd 0xffffffffffffffff 0xffffffffffffffff

def z173 : W := mkw 0x80b0000120c00000 0x0405800009060000 0xc0fc0001f0f0001d 0xae07e0000f878000

def z174 : W := mkw 0xb7db0000ee6c0004 0x8dbed80007736000 0xff1f8000ff7e0006 0x0ff8fc0007fbf000

def z175 : W := mkw 0x01200001eeec0004 0x000900000f776000 0x00000001fffe0001 0x200000000ffff000

def z176 : W := mkw 0xc39ddaf888361b60 0x561ceed7c441b0db 0xc7fffffe88fe3fff 0xde3ffffff447f1ff

def z177 : W := mkw 0x030900c088241200 0x5018480604412090 0x070001c000000000 0x0038000e00000000

def z178 : W := mkw 0xfffffe3fffffede5 0xaffffff1ffffff6f 0xfffffe3fffffffff 0xfffffff1ffffffff

def z179 : W := mkw 0x032d8af388b65be0 0x50196c579c45b2df 0x07ffffff88ffffff 0xf03ffffffc47ffff

def z180 : W := mkw 0x3f4ba794ce2c000c 0xc9fa5d3ca6716000 0x3f0387c00f0e0002 0x01f81c3e00787000

def z181 : W := mkw 0xc094582830512841 0x0604a2c141828942 0xc01c1830f0f038f5 0xde00e0c1878781c7

def z182 : W := mkw 0x92df8abc00000008 0xc496fc55e0000000 0x00ff803e00000000 0x8007fc01f0000000

def z183 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff0079c1f701f80c 0x2ff803ce0fb80fc0

def z184 : W := mkw 0x1b4ba6d48b2e9720 0x70da5d36a45974b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z185 : W := mkw 0x1a6faeb703becde0 0x70d37d75b81df66f 0x38ffe63f0fffc7fb 0xf1c7ff31f87ffe3f

def z186 : W := mkw 0x6d04fff0dd13bf62 0x5b6827ff86e89dfb 0xff007ff1ff01ffff 0x7ff803ff8ff80fff

def z187 : W := mkw 0x0004082000100840 0x0000204100008042 0x00001830000038e0 0x500000c1800001c7

def z188 : W := mkw 0xfeffffbd02880008 0xcff7fffde8144000 0xffffffff0f8e001f 0xeffffffff87c7000

def z189 : W := mkw 0xc0b0500b30c16081 0x0605828059860b04 0xc0e0603f7081c0f9 0xfe070301fb840e07

def z190 : W := mkw 0x6d00754088001200 0x0b6803aa04400090 0xff007fc088003f1f 0x5ff803fe044001f8

def z191 : W := mkw 0x480075401101b602 0x024003aa00880db0 0x38007fc10f01ff1b 0x71c003fe08780ff8

def z192 : W := mkw 0x4000500010012000 0x0200028000800900 0xc00060017001c008 0x2e0003000b800e00

def z193 : W := mkw 0xc39d58e8b8753a41 0x561ceac745c3a9d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z194 : W := mkw 0x25000000cc000000 0x0928000006600000 0xc7000000f0000004 0x0e38000007800000

def z195 : W := mkw 0x480075401101b602 0x024003aa00880db0 0x00007fc00001ff00 0x500003fe00000ff8

def z196 : W := mkw 0x92fb000122ec0004 0x8497d80009176000 0x00ff800000fe0000 0x8007fc000007f000

def z197 : W := mkw 0x0104086088101a40 0x00082043044080d2 0x071c1ff088f03ff7 0xd038e0ff844781ff

def z198 : W := mkw 0xa5b00001ecc00000 0x0d2d80000f660000 0xfffc0001fff0001f 0xafffe0000fff8000

def z199 : W := mkw 0x020d8ab000360960 0x50106c558001b04b 0x001f983080fe38f5 0xd000fcc18407f1c7

def z200 : W := mkw 0xe490510800000008 0x8f24828840000000 0xc000000000000000 0x0e00000000000000

def z201 : W := mkw 0x1062000102880000 0x0083100008144000 0x00e38000008e0000 0x80071c0000047000

def z202 : W := mkw 0x1842a614030a8520 0x20c21530a0185429 0x38e3e63e0f0e071a 0xc1c71f31f0787038

def z203 : W := mkw 0x0b0daef68936dfe0 0x70586d77b449b6ff 0x071ffffe88fffff7 0xd038fffff447ffff

def z204 : W := mkw 0xfedfffbe101168c9 0xcff6fffdf0808b46 0xfffffffe0001f8fe 0xdffffffff0000fc7

def z205 : W := mkw 0x1062000102880000 0x0083100008144000 0x38e0000107000008 0x21c7000008380000

def z206 : W := mkw 0x4804fffc00121b68 0x524027ffe00090db 0x00007ffe00003fe0 0x500003fff00001ff

def z207 : W := mkw 0xf7fb5141feed3206 0x8fbfda8a0ff76990 0xffff99c1fffe381f 0xaffffcce0ffff1c0

def z208 : W := mkw 0x0100000088000000 0x0008000004400000 0x0700000088000017 0x0038000004400000

def z209 : W := mkw 0x4804ffbc00000008 0x424027fde0000000 0x00007ffe00000000 0x400003fff0000000

def z210 : W := mkw 0xfcd2f71c00000008 0x8fe697b8e0000000 0xf8e3e63e0000001a 0xcfc71f31f0000000

def z211 : W := mkw 0x030d08e088341a40 0x501868470441a0d2 0x071c19c080703804 0x0038e0ce040381c0

def z212 : W := mkw 0x5862f617138be5a0 0x22c317b0b89c5f2d 0xf8e3fe3fff8fffff 0xffc71ff1fffc7fff

def z213 : W := mkw 0x98f6ae3f23dacde1 0x24c7b571f91ed66f 0x38ffe63f0fffc7fb 0xf1c7ff31f87ffe3f

def z214 : W := mkw 0x83bd8af1a8f61b60 0x541dec578d47b0db 0xc7ff9ff1f8fe3fff 0xfe3ffcff8fc7f1ff

def z215 : W := mkw 0x000000005501a402 0x0000000002a80d20 0x000000017701c000 0x200000000bb80e00

def z216 : W := mkw 0x6f0dfff0dd01b602 0x4b786fff86e80db0 0xff1ffff1ff01ff1f 0xfff8ffff8ff80ff8

def z217 : W := mkw 0xb7ff8af1eefe1b64 0xddbffc578f77f0db 0xffff9ff1fffe3fff 0xfffffcff8ffff1ff

def z218 : W := mkw 0x6c0075005501a402 0x0b6003a802a80d20 0xf8007801f701f81d 0x7fc003c00fb80fc0

def z219 : W := mkw 0x000000020102c5a0 0x200000001008162d 0x000000000001c7e0 0x1000000000000e3f

def z220 : W := mkw 0x92fb000122ec0004 0x8497d80009176000 0xc0ff8001f0fe001d 0xae07fc000f87f000

def z221 : W := mkw 0x6d00f756dd03f7a2 0x2b6807bab6e81fbd 0xff007fffff01ffff 0x7ff803fffff80fff

def z222 : W := mkw 0x4020500330d168c1 0x0201028019868b46 0xc0007801f0f1f8fd 0x7e0003c00f878fc7

def z223 : W := mkw 0x6d007540cd009602 0x0b6803aa066804b0 0xff007fc00f00071e 0x4ff803fe00780038

def z224 : W := mkw 0x1842240403088400 0x20c2112020184420 0x3800000007000000 0x01c0000000380000

def z225 : W := mkw 0x3c42250400000008 0x89e2112820000000 0x3800000000000000 0x01c0000000000000

def z226 : W := mkw 0x25000000cc000000 0x0928000006600000 0x3f0000000f000002 0x01f8000000780000

def z227 : W := mkw 0x93df8afc88361b68 0xd49efc57e441b0db 0x07ff9ffe88fe3ff7 0xd03ffcfff447f1ff

def z228 : W := mkw 0xedb07541fdc1b602 0x0f6d83aa0fee0db0 0xfffc7fc1fff1ff1f 0xffffe3fe0fff8ff8

def z229 : W := mkw 0x01000040dd01b602 0x0008000206e80db0 0x00000001ff01ff01 0x300000000ff80ff8

def z230 : W := mkw 0x8094082800000000 0x0404a04140000000 0x00fc003e00000000 0x8007e001f0000000

def z231 : W := mkw 0x10628217038ac5a0 0x20831410b81c562d 0x00e3803f0f8fc7e1 0xb0071c01f87c7e3f

def z232 : W := mkw 0x012000438bbedfe0 0x300900021c5df6ff 0x000000018fffffe1 0x300000000c7fffff

def z233 : W := mkw 0x01000000ec640004 0x0008000007632000 0x00000000f0700000 0x0000000007838000

def z234 : W := mkw 0x1b4faef488361b60 0x50da7d77a441b0db 0x3ffffffe88fe3fff 0xd1fffffff447f1ff

def z235 : W := mkw 0x020d8af000121b60 0x50106c57800090db 0x071f9ff000003ff6 0xd038fcff800001ff

def z236 : W := mkw 0xb6fb000122ec0004 0x8db7d80009176000 0xffff800000fe001e 0x8ffffc000007f000

def z237 : W := mkw 0xe69ddbb800000008 0xcf34eeddc0000000 0xc71f9ff000000016 0xce38fcff80000000

def z238 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc603f70f1c0e8 0xae07e301fb878e07

def z239 : W := mkw 0x3442000046080004 0x89a2100002304000 0x3800000007000000 0x01c0000000380000

def z240 : W := mkw 0x00048a3000120960 0x000024518000904b 0x001f9e3088fe3ff7 0xd000fcf18447f1ff

def z241 : W := mkw 0xffffffbdeeec000c 0xcffffffdef776000 0xfffffffffffe001f 0xeffffffffffff000

def z242 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc183ef0f038e4 0x8e07e0c1f78781c7

def z243 : W := mkw 0xffffffffdf8bf7aa 0xeffffffffefc5fbd 0xffffffffff8fffff 0xfffffffffffc7fff

def z244 : W := mkw 0x3f6ba617cfaec5a4 0xa9fb5d30be7d762d 0x3fe3e63f0f8fc7fb 0xf1ff1f31f87c7e3f

def z245 : W := mkw 0x7d627541df89b602 0x0beb13aa0efc4db0 0xffe3ffc1ff8fff1f 0xffff1ffe0ffc7ff8

def z246 : W := mkw 0xfdf27541ffc9b606 0x8fef93aa0ffe4db0 0xffe07fc1ff01ff1f 0x7fff03fe0ff80ff8

def z247 : W := mkw 0xe5b4582bfcd168c1 0x0f2da2c15fe68b46 0xfffc783ffff1f8ff 0xffffe3c1ffff8fc7

def z248 : W := mkw 0x082024030180c480 0x00410120180c0624 0x38e0663f0f81c7fb 0xf1c70331f87c0e3f

def z249 : W := mkw 0xffdb7540dd01b602 0x8ffedbaa06e80db0 0xffffffc1ff01ff1f 0xfffffffe0ff80ff8

def z250 : W := mkw 0x90f2000122c80004 0x8487900009164000 0x00e0000000000000 0x0007000000000000

def z251 : W := mkw 0x03290001eeec0004 0x001948000f776000 0x071f8001fffe0017 0xa038fc000ffff000

def z252 : W := mkw 0xd2ff582b32fd68c5 0x8697fac15997eb46 0xc0fff83ff0fff8fd 0xfe07ffc1ff87ffc7

def z253 : W := mkw 0xfeffffbf028a41a8 0xeff7fffdf814520d 0xfffffffe008e00fe 0xcffffffff0047007

def z254 : W := mkw 0x01200003efeec5a4 0x200900001f7f762d 0x00000001ffffc7e1 0x300000000ffffe3f

def z255 : W := mkw 0xfcf2750177c9a406 0x8fe793a80bbe4d20 0xf8e060017701c008 0x2fc703000bb80e00

def z256 : W := mkw 0x6400510054012002 0x0b20028802a00900 0xc000000070000000 0x0e00000003800000

def z257 : W := mkw 0xa7990000ec640004 0x8d3cc80007632000 0xc71f8000f8fe0017 0x8e38fc0007c7f000

def z258 : W := mkw 0x000082d000021320 0x5000041680001099 0x000007c000000700 0x0000003e00000038

def z259 : W := mkw 0xf7fb500bfeed6085 0x8fbfda805ff76b04 0xffffe00fffffc01f 0xafffff007ffffe00

def z260 : W := mkw 0xe79d59e888341a48 0xdf3ceacf4441a0d2 0xc71c19c080703804 0x0e38e0ce040381c0

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000010f00001b 0x21c0000008780000

def z262 : W := mkw 0x0004082000000000 0x0000204100000000 0x001c183000000014 0xc000e0c180000000

def z263 : W := mkw 0xc8b4fe3f31d3ede1 0x2645a7f1f98e9f6f 0xc0fc7e3ff0f1fffd 0xfe07e3f1ff878fff

def z264 : W := mkw 0x00240823009048c0 0x0001204118048246 0x00fc783f80f1f8fd 0xf007e3c1fc078fc7

def z265 : W := mkw 0x6d207541ffedb606 0x0b6903aa0fff6db0 0xff007fc1ffffff1f 0x7ff803fe0ffffff8

def z266 : W := mkw 0x6c00750000000000 0x0b6003a800000000 0xff007fc00000001e 0x4ff803fe00000000

def z267 : W := mkw 0x80b4082b20d048c1 0x0405a04159068246 0x00fc183e80f038f5 0xd007e0c1f40781c7

def z268 : W := mkw 0xf7ff582bfefd68c5 0x8fbffac15ff7eb46 0xfffff83ffffff8ff 0xffffffc1ffffffc7

def z269 : W := mkw 0x92ff8ab122fe0964 0xd497fc558917f04b 0x00ff803000fe00e0 0x8007fc018007f007

def z270 : W := mkw 0xb6fb000166ec0004 0x8db7d8000b376000 0xf8ff800177fe0008 0xafc7fc000bbff000

def z271 : W := mkw 0x93fb0001aaec0004 0x849fd8000d576000 0x07ff800088fe0017 0x803ffc000447f000

def z272 : W := mkw 0xfffffffdeefe1b6c 0xdfffffffef77f0db 0xfffffffffffe3fff 0xfffffffffffff1ff

def z273 : W := mkw 0xc1b4586bb8d17ac1 0x060da2c35dc68bd6 0xc7fc7ffff8f1ffff 0xfe3fe3ffffc78fff

def z274 : W := mkw 0xfffb750deeec000c 0x8fffdba86f776000 0xffffe00ffffe001f 0xafffff007ffff000

def z275 : W := mkw 0x6400510000000000 0x0b20028800000000 0xc70019c000000004 0x0e3800ce00000000

def z276 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f87f008fe07e2 0x8038fc3f8047f03f

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x001c000080f00015 0x8000e00004078000

def z278 : W := mkw 0x7c6275075789e482 0x2be313a83abc4f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z279 : W := mkw 0x80b0000320c04080 0x0405800019060204 0xc0fc603ff0f1c0fd 0xfe07e301ff878e07

def z280 : W := mkw 0x80b0000120c00000 0x0405800009060000 0x00fc000000f00000 0x8007e00000078000

def z281 : W := mkw 0x01200003fefd68c5 0x000900001ff7eb46 0x00000001fffff8e1 0x300000000fffffc7

def z282 : W := mkw 0xb4f2000166c80004 0x8da790000b364000 0xf8fc0001f7f0001d 0xafc7e0000fbf8000

def z283 : W := mkw 0x01000040dd01b602 0x0008000206e80db0 0x07001fc1ff01ff17 0x703800fe0ff80ff8

def z284 : W := mkw 0x0000000030512841 0x0000000001828942 0x00000000f0703800 0x00000000078381c0

def z285 : W := mkw 0x1962a657df8bf7a2 0x20cb1532befc5fbd 0x38e3e63fff8ffffb 0xf1c71f31fffc7fff

def z286 : W := mkw 0x0020000300804080 0x0001000018040204 0x00e0600f0001c008 0x2007030078000e00

def z287 : W := mkw 0x430ddafa98377be1 0x52186ed7d4c1bbdf 0x071ffffe88fffff7 0xd038fffff447ffff

def z288 : W := mkw 0x002000030388c480 0x20010000181c4624 0x000000010701c000 0x2000000008380e00

def z289 : W := mkw 0xf7ff5829eeec0004 0x8fbffac14f776000 0xfffff83ffffe001f 0xefffffc1fffff000

def z290 : W := mkw 0x8090000000000000 0x0404800000000000 0xc0fc00000000001c 0x8e07e00000000000

def z291 : W := mkw 0x92fb821722ee41a4 0xa497dc10b917720d 0x00ff803e00fe00e0 0x8007fc01f007f007

def z292 : W := mkw 0x0020000102880000 0x0001000008144000 0x000000010f8e0001 0x20000000087c7000

def z293 : W := mkw 0x6d207543df8bf7a2 0x2b6903aa1efc5fbd 0xff007fc1ff8fffff 0x7ff803fe0ffc7fff

def z294 : W := mkw 0x1962a6578b8ad7a0 0x20cb1532bc5c56bd 0x3fe3ffff8f8fffff 0xf1ff1ffffc7c7fff

def z295 : W := mkw 0x01200041eefe1b64 0x100900020f77f0db 0x00000001fffe3fe1 0x300000000ffff1ff

def z296 : W := mkw 0x0020000333dbede1 0x20010000199edf6f 0x00000001ffffffe1 0x300000000fffffff

def z297 : W := mkw 0xb6fb000102880000 0x8db7d80008144000 0xffff80010f8e001f 0xaffffc00087c7000

def z298 : W := mkw 0xfffffff1ffffbf66 0xdfffffff8ffffdfb 0xfffffff1ffffffff 0xffffffff8fffffff

def z299 : W := mkw 0x80b0000120c00000 0x0405800009060000 0xc0e0000170000008 0x2e0700000b800000

def z300 : W := mkw 0xffdfffbcec64000c 0xcffefffde7632000 0xfffffffef070001e 0xcffffffff7838000

def z301 : W := mkw 0x7f4bf7d4dd01b60a 0xcbfa5fbea6e80db0 0xff03ffc1ff01ff1f 0x7ff81ffe0ff80ff8

def z302 : W := mkw 0xfffb7501ffeda406 0x8fffdba80fff6d20 0xffffe001ffffc01f 0xafffff000ffffe00

def z303 : W := mkw 0xfedb750000000000 0x8ff6dba800000000 0xffffffc00000001e 0xcffffffe00000000

def z304 : W := mkw 0x4004582800000000 0x020022c140000000 0x0000783e00000000 0x400003c1f0000000

def z305 : W := mkw 0x1842240400000000 0x00c2112020000000 0x38e0600e00000008 0x01c7030070000000

def z306 : W := mkw 0x6d207543dd81f682 0x0b6903aa1eec0fb4 0xffe07fffff81ffff 0xffff03fffffc0fff

def z307 : W := mkw 0x030d08e088361b60 0x501868470441b0db 0x071c19c088fe3fe5 0x1038e0ce0447f1ff

def z308 : W := mkw 0xfcd2750c00000008 0x8fe693a860000000 0xffe07fce0000001e 0x4fff03fe70000000

def z309 : W := mkw 0x1062000302884080 0x0083100018144204 0x38e3e03f0f8fc0fb 0xf1c71f01f87c7e07

def z310 : W := mkw 0x8090000020400000 0x0404800001020000 0xc01c0000f0700004 0x0e00e00007838000

def z311 : W := mkw 0x10620003038ac5a0 0x20831000181c562d 0x38e380010f8fc7fb 0xb1c71c00087c7e3f

def z312 : W := mkw 0x83b90001a8e40000 0x041dc8000d472000 0xc7ff8001f8fe001f 0xae3ffc000fc7f000

def z313 : W := mkw 0x92ff8abf20d048c9 0xc497fc55f9068246 0x00ff803e00f000e0 0x8007fc01f0078007

def z314 : W := mkw 0xc0b4582b00804080 0x0605a2c158040204 0xc0fc783f0081c0fd 0xfe07e3c1f8040e07

def z315 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0x3fff80000ffe0002 0x81fffc00007ff000

def z316 : W := mkw 0x1842a61401008400 0x00c21530a0080420 0x38e3e63f0f01c71b 0xf1c71f31f8780e38

def z317 : W := mkw 0xbffba615eeec0004 0x8dffdd30af776000 0xffffe63ffffe001f 0xefffff31fffff000

def z318 : W := mkw 0x0020000320d048c1 0x0001000019068246 0x0000000000f000e0 0x0000000000078007

def z319 : W := mkw 0x3e4ba79400000008 0xc9f25d3ca0000000 0x3fe3e7fe0000001a 0xc1ff1f3ff0000000

def z320 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x07039ff0080e3fe2 0x50381cff804071ff

def z321 : W := mkw 0x3f4faff488361b68 0xd9fa7d7fa441b0db 0x3f1f9ff088fe3ff7 0xd1f8fcff8447f1ff

def z322 : W := mkw 0x0309000088240000 0x0018480004412000 0x071f800088fe0017 0x8038fc000447f000

def z323 : W := mkw 0xc0b4dafb30d37be1 0x5605a6d7d9869bdf 0xc0fc7ffff0f1fffd 0xfe07e3ffff878fff

def z324 : W := mkw 0x25000140cc001202 0x0928000a06600090 0x070001c000000000 0x0038000e00000000

def z325 : W := mkw 0x0309821088260120 0x00184c1084413009 0x071f863088fe07f7 0xd038fc318447f03f

def z326 : W := mkw 0x4804fe3e1113ede1 0x224027f1f0889f6f 0x00007e3e0001ffe0 0x500003f1f0000fff

def z327 : W := mkw 0xb7db0000ce2c0004 0x8dbed80006716000 0xffff80000f0e001e 0x8ffffc0000787000

def z328 : W := mkw 0x374f8af0ce3e1b64 0xd9ba7c578671f0db 0x3f1f9ff08ffe3ff7 0xd1f8fcff847ff1ff

def z329 : W := mkw 0x6c04ffbc00000008 0x4b6027fde0000000 0xff007ffe0000001e 0x4ff803fff0000000

def z330 : W := mkw 0x0000004000001200 0x0000000200000090 0x00001fc000003f00 0x500000fe000001f8

def z331 : W := mkw 0xfedfffbc00100848 0xcff6fffde0008042 0xfffffffe80f038ff 0xdffffffff40781c7

def z332 : W := mkw 0xe7995140fc653206 0x8f3cca8a07e32990 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z333 : W := mkw 0x2f09a7d0cd269722 0x59784d3e866934b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z334 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffe380017f0e000a 0x2fff1c000bf87000

def z335 : W := mkw 0x3e4fafb400000008 0xc9f27d7da0000000 0x3f1f9ff000000016 0xc1f8fcff80000000

def z336 : W := mkw 0x5862f757138bf7a2 0x22c317bab89c5fbd 0x38e3ffff0f8ffffb 0xf1c71ffff87c7fff

def z337 : W := mkw 0x5866fe3f139bede1 0x22c337f1f89cdf6f 0x38e3fe3f0f8ffffb 0xf1c71ff1f87c7fff

def z338 : W := mkw 0x2d002400cd008400 0x0968012006680420 0xff006601ff01c71f 0x7ff803300ff80e38

def z339 : W := mkw 0x0020000120c00000 0x0001000009060000 0x00000001f0f00001 0x200000000f878000

def z340 : W := mkw 0x030d082088340840 0x001868410441a042 0x071f983088fe38f7 0xd038fcc18447f1c7

def z341 : W := mkw 0xfedfffbc5501a40a 0xcff6fffde2a80d20 0xffffffff7701c01e 0xeffffffffbb80e00

def z342 : W := mkw 0x670ddbf0dc373b62 0x5b386edf86e1b9db 0xc71f9ff0f8fe3ff7 0xde38fcff87c7f1ff

def z343 : W := mkw 0x7c62f717578be5a2 0x2be317b8babc5f2d 0xf8e3e63f7f8fc7fb 0xffc71f31fbfc7e3f

def z344 : W := mkw 0x92fb000122ec0004 0x8497d80009176000 0x38ff80010ffe001b 0xa1c7fc00087ff000

def z345 : W := mkw 0x0800a6160102c5a0 0x20400530b008162d 0x3800663f0f01c7fb 0x71c00331f8780e3f

def z346 : W := mkw 0x01000040dd37bf62 0x1008000206e9bdfb 0x00000001ffffffe1 0x300000000fffffff

def z347 : W := mkw 0xd8f6fe3f30d168c1 0x06c7b7f1f9868b46 0xf8fffe3ff0f1f8ff 0xffc7fff1ff878fc7

def z348 : W := mkw 0xf7ffdafbfeff7be5 0xdfbffed7dff7fbdf 0xffffffffffffffff 0xffffffffffffffff

def z349 : W := mkw 0xc0b4582b20d048c1 0x0605a2c159068246 0xc0fc783e00f000fc 0xce07e3c1f0078007

def z350 : W := mkw 0x00200003028a41a0 0x200100001814520d 0x00000000008e00e0 0x0000000000047007

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x00e0603e00000018 0xc0070301f0000000

def z352 : W := mkw 0x80b4082b30d168c1 0x0405a04159868b46 0x00fc003ff0f1f8e1 0xb007e001ff878fc7

def z353 : W := mkw 0x6d007500cc000000 0x0b6803a806600000 0xff007fc1ff00001f 0x6ff803fe0ff80000

def z354 : W := mkw 0x0100000088240000 0x0008000004412000 0x0000000088fe0001 0x000000000447f000

def z355 : W := mkw 0x25000040cc001200 0x0928000206600090 0xff001fc1ff003f1f 0x7ff800fe0ff801f8

def z356 : W := mkw 0x030d8af088341a40 0x50186c578441a0d2 0x071f9ff080703816 0xc038fcff840381c0

def z357 : W := mkw 0xfffffffdffedb60e 0xcfffffffefff6db0 0xffffffffffffff1f 0xfffffffffffffff8

def z358 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff0067c17f01c70a 0x2ff8033e0bf80e38

def z359 : W := mkw 0x2d002540cd009602 0x0968012a066804b0 0x3f001fc08f003f17 0x51f800fe047801f8

def z360 : W := mkw 0x0020000330d168c1 0x0001000019868b46 0x00000001f0f1f8e1 0x300000000f878fc7

def z361 : W := mkw 0x1842a6160102c5a0 0x20c21530b008162d 0x38e3e63e0001c7fa 0xd1c71f31f0000e3f

def z362 : W := mkw 0xd8f6fe3f038ac5a0 0x26c7b7f1f81c562d 0xf8fffe3f0f8fc7ff 0xffc7fff1f87c7e3f

def z363 : W := mkw 0xffdffffc88341a48 0xdffeffffe441a0d2 0xfffffffe8070381e 0xcffffffff40381c0

def z364 : W := mkw 0x6f0dfff088361b60 0x5b786fff8441b0db 0xff1ffff088fe3fff 0xdff8ffff8447f1ff

def z365 : W := mkw 0x0004082000100840 0x0000204100008042 0x001c180080703804 0x0000e0c0040381c0

def z366 : W := mkw 0x6c0075005501a402 0x0b6003a802a80d20 0xf80060017701c008 0x2fc003000bb80e00

def z367 : W := mkw 0x1b6ba6d78baed7a0 0x70db5d36bc5d76bd 0x3fe3e7ff0f8fc7fb 0xf1ff1f3ff87c7e3f

def z368 : W := mkw 0xb7df8af088361b60 0xddbefc578441b0db 0xffff9ff088fe3fff 0xdffffcff8447f1ff

def z369 : W := mkw 0x0800a79400000008 0x4040053ca0000000 0x000007c000000000 0x0000003e00000000

def z370 : W := mkw 0xffffffbfefeec5ac 0xeffffffdff7f762d 0xffffffffffffc7ff 0xfffffffffffffe3f

def z371 : W := mkw 0xb6df8abc00000008 0xcdb6fc55e0000000 0xffff803e0000001e 0x8ffffc01f0000000

def z372 : W := mkw 0x4804fffc1101b60a 0x424027ffe0880db0 0x00007ffe0001ff00 0x500003fff0000ff8

def z373 : W := mkw 0x020d8ab000360960 0x50106c558001b04b 0x071f9ff000fe00f6 0xc038fcff8007f007

def z374 : W := mkw 0xc1b4586bfdd1fec3 0x060da2c35fee8ff6 0xc0fc783ffff1fffd 0xfe07e3c1ffff8fff

def z375 : W := mkw 0x00200003038ac5a0 0x20010000181c562d 0x00e0603f0f8fc7f9 0xf0070301f87c7e3f

def z376 : W := mkw 0xffdfffbc88240008 0xcffefffde4412000 0xfffffffe88fe001f 0xcffffffff447f000

def z377 : W := mkw 0xf6df59a800000008 0xcfb6facd40000000 0xffff99c00000001e 0x8ffffcce00000000

def z378 : W := mkw 0x020d8af000361b60 0x50106c578001b0db 0x001f9ff000fe3fe0 0xd000fcff8007f1ff

def z379 : W := mkw 0xffff7d6bfffdfec7 0x8ffffbeb5fffeff6 0xffffffffffffffff 0xffffffffffffffff

def z380 : W := mkw 0x2c00250000000000 0x0960012800000000 0x3f0007c000000002 0x01f8003e00000000

def z381 : W := mkw 0x1862a61502880000 0x00c31530a8144000 0x38e3e63f0f8e001b 0xe1c71f31f87c7000

def z382 : W := mkw 0xfeffffbf30c16089 0xcff7fffdf9860b04 0xffffffff7001c01e 0xeffffffffb800e00

def z383 : W := mkw 0x0020000300804080 0x0001000018040204 0x00e0003e008000e0 0x80070001f0040007

def z384 : W := mkw 0x1862a615038a8520 0x20c31530a81c5429 0x38e386010f8e071b 0xa1c71c30087c7038

def z385 : W := mkw 0xee9dffbc00000008 0xcf74effde0000000 0xc71c7ffe00000004 0x4e38e3fff0000000

def z386 : W := mkw 0xc894ffbc00000008 0x4644a7fde0000000 0xc0fc7ffe0000001c 0xce07e3fff0000000

def z387 : W := mkw 0x0100004088001200 0x0008000204400090 0x070007c008000702 0x0038003e00400038

def z388 : W := mkw 0x0209829000260120 0x50104c1480013009 0x00038000000e0000 0x00001c0000007000

def z389 : W := mkw 0x6f09f7d0dd27b722 0x5b784fbe86e93db9 0xff03ffc1ff0fff1f 0x7ff81ffe0ff87ff8

def z390 : W := mkw 0xbffba615efee8524 0xadffdd30af7f7429 0xffff8601fffe071f 0xaffffc300ffff038

def z391 : W := mkw 0xe79d59e8dc01320a 0xcf3ceacf46e00990 0xc71c19c0f0003804 0x0e38e0ce078001c0

def z392 : W := mkw 0x80b0000b20c04081 0x0405800059060204 0x00e0000e00000000 0x0007000070000000

def z393 : W := mkw 0xd0f6da3f32db69e1 0x2687b6d1f996db4f 0xc0fff83ff0fff8fd 0xfe07ffc1ff87ffc7

def z394 : W := mkw 0xa490000064400004 0x8d24800003220000 0xc000000070000000 0x0e00000003800000

def z395 : W := mkw 0x4100504098013200 0x0208028204c00990 0xc7007fc1f801ff1f 0x7e3803fe0fc00ff8

def z396 : W := mkw 0x1042821400000000 0x00821410a0000000 0x00e3803e00000000 0x80071c01f0000000

def z397 : W := mkw 0x65005140dd01b602 0x0b28028a06e80db0 0xc70019c1ff01ff05 0x3e3800ce0ff80ff8

def z398 : W := mkw 0xec947d2800000000 0x0f64a3e940000000 0xfffc7ffe0000001e 0xcfffe3fff0000000

def z399 : W := mkw 0x030982d088261320 0x50184c1684413099 0x071f87c088fe0717 0x8038fc3e0447f038

def z400 : W := mkw 0x032d8af1eefe1b64 0x50196c578f77f0db 0x071f9ff1fffe3ff7 0xf038fcff8ffff1ff

def z401 : W := mkw 0x490075409901b602 0x024803aa04c80db0 0x07007fc08801ff17 0x503803fe04400ff8

def z402 : W := mkw 0x09002440dd01b602 0x0048012206e80db0 0x38006601ff01ff1b 0x71c003300ff80ff8

def z403 : W := mkw 0x4024582b109168c1 0x020122c158848b46 0x00e0783f0081f8f9 0xf00703c1f8040fc7

def z404 : W := mkw 0x49007540dd01b602 0x024803aa06e80db0 0x00007fc1ff01ff01 0x700003fe0ff80ff8

def z405 : W := mkw 0xd8f2f61f33cbe5a1 0x26c797b0f99e5f2d 0xf8e3e63f7f8fc7fb 0xffc71f31fbfc7e3f

def z406 : W := mkw 0xbffb2401efec8404 0x8dffd9200f7f6420 0xffffe601ffffc71f 0xffffff300ffffe38

def z407 : W := mkw 0x27090000cc240000 0x0938480006612000 0xff1f8001fffe001f 0xaff8fc000ffff000

def z408 : W := mkw 0x82bd8abb20f649e1 0x5415ec55d907b24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z409 : W := mkw 0x6d007540dc013202 0x0b6803aa06e00990 0xff007fc0f000381e 0x4ff803fe078001c0

def z410 : W := mkw 0x00000002101168c1 0x0000000010808b46 0x000000000001f8e0 0x1000000000000fc7

def z411 : W := mkw 0x92df8abc00000008 0xc496fc55e0000000 0x07ff9ffe00000016 0xc03ffcfff0000000

def z412 : W := mkw 0x030d08e088341a40 0x501868470441a0d2 0x071f99c088fe3817 0x8038fcce0447f1c0

def z413 : W := mkw 0xc3bd58ebb8f57ac1 0x561deac75dc7abd6 0xc7fc79fff0f1f8fd 0xfe3fe3cfff878fc7

def z414 : W := mkw 0xedb0754bfdc1f683 0x0f6d83aa5fee0fb4 0xffe07fcfff01ff1f 0x7fff03fe7ff80ff8

def z415 : W := mkw 0xc094582a305168c1 0x0604a2c151828b46 0xc01c783ef071f8e4 0x5e00e3c1f7838fc7

def z416 : W := mkw 0x80b0000330d168c1 0x0405800019868b46 0xc0fc0001f0f1f8fd 0xbe07e0000f878fc7

def z417 : W := mkw 0x376b0001ceac0004 0x89bb58000e756000 0x3fe380010f8e001b 0xa1ff1c00087c7000

def z418 : W := mkw 0xffdffffc88001208 0xcffeffffe4400090 0xfffffffe88003f1f 0xdffffffff44001f8

def z419 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071c1ff080703fe4 0x5038e0ff840381ff

def z420 : W := mkw 0x0000821000020120 0x0000041080001009 0x00038600080e0702 0x00001c3000407038

def z421 : W := mkw 0x1842a616030ac5a0 0x20c21530b018562d 0x3803e63e0f0fc7e2 0x51c01f31f0787e3f

def z422 : W := mkw 0x0100825088361b60 0x100804128441b0db 0x0003863088fe3ff3 0xd0001c318447f1ff

def z423 : W := mkw 0x0000821000020120 0x0000041080001009 0x00038030008e00e0 0x80001c0180047007

def z424 : W := mkw 0xbcf2a61767cac5a4 0xade79530bb3e562d 0xf8e3e63f7f8fc7fb 0xffc71f31fbfc7e3f

def z425 : W := mkw 0xb7ff0821eefc0844 0x8dbff8410f77e042 0xffff9831fffe38ff 0xfffffcc18ffff1c7

def z426 : W := mkw 0x3d42a754cf0a9722 0x29ea153aa67854b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z427 : W := mkw 0xfcf2750d66c8000c 0x8fe793a86b364000 0xf8e0600f77000008 0x2fc703007bb80000

def z428 : W := mkw 0x0000004000121b60 0x10000002000090db 0x0000000000003fe0 0x10000000000001ff

def z429 : W := mkw 0xc8b47c2b31d1ecc1 0x0645a3e1598e8f66 0xf8fc7e3ffff1ffff 0xffc7e3f1ffff8fff

def z430 : W := mkw 0x5846ffbc00000008 0x42c237fde0000000 0x38e3fffe0000001a 0xc1c71ffff0000000

def z431 : W := mkw 0x1862a617028a41a0 0x20c31530b814520d 0x38e3e63e008e00fa 0xc1c71f31f0047007

def z432 : W := mkw 0xbedba79400000008 0xcdf6dd3ca0000000 0xffff87c00000001e 0x8ffffc3e00000000

def z433 : W := mkw 0x0000000010012000 0x0000000000800900 0x00000001f001f801 0x300000000f800fc0

def z434 : W := mkw 0x0800a61001028520 0x0040053080081429 0x3803e6310f8fc7fb 0xf1c01f31887c7e3f

def z435 : W := mkw 0x020d8ab000360960 0x50106c558001b04b 0x001f863008fe07f3 0xd000fc318047f03f

def z436 : W := mkw 0x3f4ba7d4cd00960a 0xc9fa5d3ea66804b0 0x3f0387c00f000702 0x01f81c3e00780038

def z437 : W := mkw 0x0209000000000000 0x0010480000000000 0x071f800000000016 0x8038fc0000000000

def z438 : W := mkw 0x080024060100c480 0x2040012030080624 0x0000600e0001c000 0x0000030070000e00

def z439 : W := mkw 0x4800750000000000 0x024003a800000000 0x00007fc000000000 0x400003fe00000000

def z440 : W := mkw 0xb6fb000166c80004 0x8db7d8000b364000 0xffff80017700001e 0xaffffc000bb80000

def z441 : W := mkw 0xc8b4ffbf30d168c9 0x4645a7fdf9868b46 0xc0fc7ffff0f1f8fd 0xfe07e3ffff878fc7

def z442 : W := mkw 0xc090500830412001 0x0604828041820900 0xc000000070000000 0x0e00000003800000

def z443 : W := mkw 0xb7fb0041eefe1b64 0x9dbfd8020f77f0db 0xffff8001fffe3fff 0xbffffc000ffff1ff

def z444 : W := mkw 0x030982d088261320 0x50184c1684413099 0x07039fc0880e3f17 0x50381cfe044071f8

def z445 : W := mkw 0xffdfffbcce2c000c 0xcffefffde6716000 0xfffffffe0f0e001e 0xcffffffff0787000

def z446 : W := mkw 0x4804ffbe0102c5a8 0x624027fdf008162d 0x00007ffe0001c7e0 0x500003fff0000e3f

def z447 : W := mkw 0x6d00f750dd03b722 0x0b6807ba86e81db9 0xff03fff1ff8fffff 0xfff81fff8ffc7fff

def z448 : W := mkw 0xc1b4586bb8f77be1 0x160da2c35dc7bbdf 0xc0fc783ff8fffffd 0xfe07e3c1ffc7ffff

def z449 : W := mkw 0xc0b4582930d12841 0x0605a2c149868942 0xc0fc1801f0f0381d 0xae07e0c00f8781c0

def z450 : W := mkw 0xffffffff8bbedfe8 0xfffffffffc5df6ff 0xffffffff8fffffff 0xfffffffffc7fffff

def z451 : W := mkw 0xfcf2f71f038ac5a8 0xafe797b8f81c562d 0xf8e3e63f0f8fc7fb 0xffc71f31f87c7e3f

def z452 : W := mkw 0x6c0075401101b602 0x0b6003aa00880db0 0xff007fc00001ff1e 0x5ff803fe00000ff8

def z453 : W := mkw 0x136b00018aac0000 0x009b58000c556000 0x3fff80018ffe001f 0xa1fffc000c7ff000

def z454 : W := mkw 0x0800240001008400 0x0040012000080420 0x000066000001c700 0x5000033000000e38

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x000060010001c019 0x7000030008000e00

def z456 : W := mkw 0xecb47d2b30d168c1 0x0f65a3e959868b46 0xfffc7ffff0f1f8ff 0xffffe3ffff878fc7

def z457 : W := mkw 0xf4f2500b76c96085 0x8fa792805bb64b04 0xf8e0600f7701c008 0x2fc703007bb80e00

def z458 : W := mkw 0xfcf2750f30c16089 0x8fe793a879860b04 0xf8e0600f7001c008 0x2fc703007b800e00

def z459 : W := mkw 0x6c0075405501b602 0x0b6003aa02a80db0 0xf8007fc17701ff08 0x7fc003fe0bb80ff8

def z460 : W := mkw 0x0309000088240000 0x0018480004412000 0x071c000080700004 0x0038e00004038000

def z461 : W := mkw 0x0b0daef089369f60 0x50586d778449b4fb 0x3f1ffff18fffffff 0xf1f8ffff8c7fffff

def z462 : W := mkw 0x400459a800000008 0x420022cd40000000 0x000019c000000000 0x000000ce00000000

def z463 : W := mkw 0x0004082a001048c1 0x0000204150008246 0x0000003e000000e0 0x00000001f0000007

def z464 : W := mkw 0x01000040cd009602 0x00080002066804b0 0x000000000f000700 0x0000000000780038

def z465 : W := mkw 0x81b00001eeec0004 0x040d80000f776000 0xc0fc0001fffe001d 0xae07e0000ffff000

def z466 : W := mkw 0x0800240001008400 0x0040012000080420 0x380006000f000702 0x01c0003000780038

def z467 : W := mkw 0x90d2000c00000008 0x8486900060000000 0x00e0000e00000000 0x0007000070000000

def z468 : W := mkw 0xc0b4582b33dbede1 0x2605a2c1599edf6f 0xc0fc783ffffffffd 0xfe07e3c1ffffffff

def z469 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xfffc0001f770000c 0x2fffe0000fbb8000

def z470 : W := mkw 0xb7db000088240000 0x8dbed80004412000 0xffff800088fe001f 0x8ffffc000447f000

def z471 : W := mkw 0x6c00750000000000 0x0b6003a800000000 0xf800600000000008 0x0fc0030000000000

def z472 : W := mkw 0xd2dfdabc00000008 0xc696fed5e0000000 0xc0fff83e0000001c 0xce07ffc1f0000000

def z473 : W := mkw 0xfedfffbc10012008 0xcff6fffde0800900 0xfffffffff001f81f 0xffffffffff800fc0

def z474 : W := mkw 0x1042000000000000 0x0082100000000000 0x38e380000000001a 0x81c71c0000000000

def z475 : W := mkw 0x0020000300804080 0x0001000018040204 0x000000010081c0e1 0x3000000008040e07

def z476 : W := mkw 0x3d62a617cf8ac5a0 0x29eb1530be7c562d 0xffe3e63fff8fc7ff 0xffff1f31fffc7e3f

def z477 : W := mkw 0xefbdfffbfdf7ffe3 0x5f7defffdfefbfff 0xffffffffffffffff 0xffffffffffffffff

def z478 : W := mkw 0x030d8af0dd37bf62 0x50186c5786e9bdfb 0x071f9ff1fffffff7 0xf038fcff8fffffff

def z479 : W := mkw 0x00048ab000000000 0x4000245580000000 0x00001ff000000000 0x400000ff80000000

def z480 : W := mkw 0x0100825088021320 0x0008041284401099 0x07039ff0888e3ff7 0xd0381cff844471ff

def z481 : W := mkw 0x020d8ab000100840 0x40106c5580008042 0x071f9ff080f038f7 0xd038fcff840781c7

def z482 : W := mkw 0x92df8abc00360968 0xd496fc55e001b04b 0x00ff803e00fe00e0 0x8007fc01f007f007

def z483 : W := mkw 0xf6df582800000000 0x8fb6fac140000000 0xfffff83e0000001e 0xcfffffc1f0000000

def z484 : W := mkw 0x10628217028a41a0 0x20831410b814520d 0x00e3863e088e07f3 0xd0071c31f044703f

def z485 : W := mkw 0x9afba61723eec5a4 0xa4d7dd30b91f762d 0x38ffe63f0fffc7fb 0xf1c7ff31f87ffe3f

def z486 : W := mkw 0x0820a6170182c5a0 0x20410530b80c162d 0x00e0663f0081c7f9 0xf0070331f8040e3f

def z487 : W := mkw 0xc0b0500130c12000 0x0605828009860900 0xc0fc7801f0f1f81d 0xfe07e3c00f878fc0

def z488 : W := mkw 0x6e0dffb000000000 0x4b706ffd80000000 0xff1ffff00000001e 0xcff8ffff80000000

def z489 : W := mkw 0x0900244089009600 0x00480122044804b0 0x3f007fc18f01ff1f 0x71f803fe0c780ff8

def z490 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f9fc0887e3f06 0x0038fcfe0443f1f8

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x07001fc000000016 0x403800fe00000000

def z492 : W := mkw 0xffdffffcdd37bf6a 0xdffeffffe6e9bdfb 0xffffffffffffffff 0xffffffffffffffff

def z493 : W := mkw 0x2609018000000008 0xc930480c00000000 0x070001c000000000 0x0038000e00000000

def z494 : W := mkw 0xed947d68dd01b602 0x0f6ca3eb46e80db0 0xfffc7fffff01ff1f 0xffffe3fffff80ff8

def z495 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc780ff071f80c 0x2e07e3c07f838fc0

def z496 : W := mkw 0x186224070388c480 0x20c31120381c4624 0x38e0660f0f01c71b 0x71c7033078780e38

def z497 : W := mkw 0x6f0d7de0dd35be42 0x5b786bef06e9adf2 0xff1c7fc1ff71ff1f 0x7ff8e3fe0ffb8ff8

def z498 : W := mkw 0x2d002540dd01b602 0x0968012a06e80db0 0x3f0007c1ff01ff03 0x31f8003e0ff80ff8

def z499 : W := mkw 0xfeffffbd20c00008 0xcff7fffde9060000 0xfffffffff0f0001f 0xefffffffff878000

def z500 : W := mkw 0x0024082330d168c1 0x0001204119868b46 0x001c1831f0f1f8f5 0xf000e0c18f878fc7

def z501 : W := mkw 0x4800f7561103f7a2 0x224007bab0881fbd 0x00007ffe0001ffe0 0x500003fff0000fff

def z502 : W := mkw 0x829d08a800000008 0xc414e84540000000 0x001c000000000000 0x0000e00000000000

def z503 : W := mkw 0x136f8af78abe5be0 0x709b7c57bc55f2df 0x07ff9ffe88fe3ff7 0xd03ffcfff447f1ff

def z504 : W := mkw 0x25200001eeec0004 0x092900000f776000 0xff000001fffe001f 0x2ff800000ffff000

def z505 : W := mkw 0x2d002540cd009602 0x0968012a066804b0 0xff0007c1ff00071f 0x2ff8003e0ff80038

def z506 : W := mkw 0x4000500010012000 0x0200028000800900 0x000078000001f800 0x500003c000000fc0

def z507 : W := mkw 0xe5945968fc513a43 0x0f2ca2cb47e289d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z508 : W := mkw 0x7c62f717038ac5a0 0x2be317b8b81c562d 0xffe3ffff0f8fc7ff 0xffff1ffff87c7e3f

def z509 : W := mkw 0xf6dfdbbc00000008 0xcfb6fedde0000000 0xc7ff99fe00000004 0x8e3ffccff0000000

def z510 : W := mkw 0x4000500000000000 0x0200028000000000 0xc00078000000001c 0x4e0003c000000000

def z511 : W := mkw 0xc0b4582920c00000 0x0605a2c149060000 0xc0fc783ff0f0001d 0xee07e3c1ff878000

def z512 : W := mkw 0xfdd2754cdd01b60a 0x8fee93aa66e80db0 0xffe07fcfff01ff1f 0x7fff03fe7ff80ff8

def z513 : W := mkw 0xfedf7dac00000008 0xcff6fbed60000000 0xfffc79ce0000000c 0x0fffe3ce70000000

def z514 : W := mkw 0x0309000088240000 0x0018480004412000 0x07038000080e0002 0x00381c0000407000

def z515 : W := mkw 0xa7b90001ece40004 0x8d3dc8000f672000 0xc7fc0001f0f0001d 0xae3fe0000f878000

def z516 : W := mkw 0x0800240001008400 0x0040012000080420 0x380060010701c008 0x21c0030008380e00

def z517 : W := mkw 0x1042000002080000 0x0082100000104000 0x380380000f0e0002 0x01c01c0000787000

def z518 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc01c1801f0f1f8e5 0x3e00e0c00f878fc7

def z519 : W := mkw 0xd2ffdabf30d168c9 0xc697fed5f9868b46 0xc0fff83ff0f1f8fd 0xfe07ffc1ff878fc7

def z520 : W := mkw 0x0020000330c16081 0x0001000019860b04 0x000000017001c000 0x200000000b800e00

def z521 : W := mkw 0x1866aef7039adfe0 0x70c33577b81cd6ff 0x38e3ffff0f8ffffb 0xf1c71ffff87c7fff

def z522 : W := mkw 0xfeffffbd22ec000c 0xcff7fffde9176000 0xfffffffe00fe001e 0xcffffffff007f000

def z523 : W := mkw 0xa79d08e0ec741a44 0xdd3ce8470763a0d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z524 : W := mkw 0xf7ff5829fefd2845 0x8fbffac14ff7e942 0xffff9801fffe381f 0xaffffcc00ffff1c0

def z525 : W := mkw 0x030d8af088261320 0x50186c5784413099 0x071f9ff0080e0716 0xc038fcff80407038

def z526 : W := mkw 0xb7fb0041eeec1204 0x8dbfd8020f776090 0xffff9fc1fffe3f1f 0xfffffcfe0ffff1f8

def z527 : W := mkw 0x0820a617038ac5a0 0x20410530b81c562d 0x0000663f0f8fc7e1 0x70000331f87c7e3f

def z528 : W := mkw 0x1862a61700804080 0x00c31530b8040204 0x38e3e63f0081c0fb 0xf1c71f31f8040e07

def z529 : W := mkw 0xfedffffc00121b68 0xdff6ffffe00090db 0xfffffffe00003ffe 0xdffffffff00001ff

def z530 : W := mkw 0xfcd67d2c00000008 0x8fe6b3e960000000 0xf8fc783e0000001c 0xcfc7e3c1f0000000

def z531 : W := mkw 0xc2bddabb30d168c1 0x4615eed5d9868b46 0xc7fffffff0f1f8ff 0xfe3fffffff878fc7

def z532 : W := mkw 0x4004dafa10137be1 0x520026d7d0809bdf 0x00007ffe0001ffe0 0x500003fff0000fff

def z533 : W := mkw 0x126f8ab702be49e0 0x70937c55b815f24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z534 : W := mkw 0x6c0075005501a402 0x0b6003a802a80d20 0xf80066017f01c71b 0x7fc003300bf80e38

def z535 : W := mkw 0xc094582800100840 0x0604a2c140008042 0xc0fc783e80f038fd 0xde07e3c1f40781c7

def z536 : W := mkw 0x0104086088361b60 0x100820430441b0db 0x001c183088fe3ff5 0xd000e0c18447f1ff

def z537 : W := mkw 0x3f4ba7d488261328 0xd9fa5d3ea4413099 0x3f0387c0080e0702 0x01f81c3e00407038

def z538 : W := mkw 0x10628217028a41a0 0x20831410b814520d 0x00e3e03f008fc0f9 0xf0071f01f8047e07

def z539 : W := mkw 0xffffffbffefd68cd 0xcffffffdfff7eb46 0xfffffffffffff8ff 0xffffffffffffffc7

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000060008000713 0x5000003000400038

def z541 : W := mkw 0x1a6faeb7038ac5a0 0x60d37d75b81c562d 0x3fffffff0f8fc7ff 0xf1fffffff87c7e3f

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000030008000f1 0xd000000180040007

def z543 : W := mkw 0x0100004088341a40 0x100800020441a0d2 0x0000000080703800 0x00000000040381c0

def z544 : W := mkw 0x1962a6578bbedfe0 0x30cb1532bc5df6ff 0x38e3e63f8ffffffb 0xf1c71f31fc7fffff

def z545 : W := mkw 0xc0b4582b30c16081 0x0605a2c159860b04 0xc0fc783f7001c01c 0xee07e3c1fb800e00

def z546 : W := mkw 0xc094582800000000 0x0604a2c140000000 0xc01c180000000004 0x0e00e0c000000000

def z547 : W := mkw 0x374b82d0ce2e1324 0xd9ba5c1686717099 0x3f0387c00f0e0702 0x01f81c3e00787038

def z548 : W := mkw 0x10628217028a41a0 0x20831410b814520d 0x38e3803f0f8e00fb 0xa1c71c01f87c7007

def z549 : W := mkw 0x6d04fffcdd01b60a 0x4b6827ffe6e80db0 0xff007fffff01ff1f 0x7ff803fffff80ff8

def z550 : W := mkw 0xecb47d2b75d1ecc3 0x0f65a3e95bae8f66 0xf8fc783ff7f1f8fd 0xffc7e3c1ffbf8fc7

def z551 : W := mkw 0xe79ddbf888361b68 0xdf3ceedfc441b0db 0xc71f9ff088fe3ff7 0xde38fcff8447f1ff

def z552 : W := mkw 0x4b0dfffc88361b68 0x52586fffe441b0db 0x071ffffe88fe3ff7 0xd038fffff447f1ff

def z553 : W := mkw 0x6d047d60dd11be42 0x0b6823eb06e88df2 0xff1c7ff1fff1ffff 0xfff8e3ff8fff8fff

def z554 : W := mkw 0x4000500010012000 0x0200028000800900 0xc0001800f0003804 0x0e0000c0078001c0

def z555 : W := mkw 0xe5b4596bfcd17ac3 0x0f2da2cb5fe68bd6 0xc7fc79fff0f1f8fd 0xfe3fe3cfff878fc7

def z556 : W := mkw 0xd0f6582b32d968c1 0x0687b2c15996cb46 0xf8fff83ffffff8ff 0xffc7ffc1ffffffc7

def z557 : W := mkw 0x6c00750001008400 0x0b6003a800080420 0xff007fc10f01c71f 0x7ff803fe08780e38

def z558 : W := mkw 0xc1b4582bfefd68c5 0x060da2c15ff7eb46 0xc0fc783ffffff8fd 0xfe07e3c1ffffffc7

def z559 : W := mkw 0x020d08a000340840 0x501068450001a042 0x001c000000700000 0x0000e00000038000

def z560 : W := mkw 0x0100004088261320 0x1008000204413099 0x00000000080e0700 0x0000000000407038

def z561 : W := mkw 0x0309004088361b60 0x101848020441b0db 0x071f800088fe3ff7 0x9038fc000447f1ff

def z562 : W := mkw 0x00048ab000120960 0x500024558000904b 0x00000030000000e0 0x0000000180000007

def z563 : W := mkw 0x0000000000360960 0x100000000001b04b 0x0000000000fe00e0 0x000000000007f007

def z564 : W := mkw 0xfeffffbd66c8000c 0xcff7fffdeb364000 0xffffffff7700001e 0xeffffffffbb80000

def z565 : W := mkw 0x10628211028a0120 0x0083141088145009 0x38e386310f8e07fb 0xf1c71c31887c703f

def z566 : W := mkw 0x1b6ba6178baec5a0 0x20db5d30bc5d762d 0x3fffe63f8fffc7ff 0xf1ffff31fc7ffe3f

def z567 : W := mkw 0xc0b0500b30c16081 0x0605828059860b04 0xc0fc600ff0f1c01d 0xae07e3007f878e00

def z568 : W := mkw 0x01200041ffedb606 0x000900020fff6db0 0x00000001ffffff01 0x300000000ffffff8

def z569 : W := mkw 0xc0b4da3b30d369e1 0x0605a6d1d9869b4f 0xc0fffe3ff8ffffff 0xfe07fff1ffc7ffff

def z570 : W := mkw 0x1062000702884080 0x2083100038144204 0x00e0000e00000000 0x0007000070000000

def z571 : W := mkw 0x4a0dffbc00000008 0x42506ffde0000000 0x071ffffe00000016 0xc038fffff0000000

def z572 : W := mkw 0xffdfffbccc000008 0xcffefffde6600000 0xffffffffff00001f 0xeffffffffff80000

def z573 : W := mkw 0xecb0750b75c1e483 0x0f6583a85bae0f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z574 : W := mkw 0xb7ff8abdeeec000c 0xcdbffc55ef776000 0xffff803ffffe001f 0xaffffc01fffff000

def z575 : W := mkw 0x0209000000240000 0x0010480000012000 0x001f800000fe0000 0x8000fc000007f000

def z576 : W := mkw 0x020d8ab000000000 0x40106c5580000000 0x001f803000000000 0x8000fc0180000000

def z577 : W := mkw 0xfedb750c00000008 0x8ff6dba860000000 0xffffe00e0000001e 0x8fffff0070000000

def z578 : W := mkw 0xc094582a101168c1 0x0604a2c150808b46 0xc0fc783e0001f8fc 0xde07e3c1f0000fc7

def z579 : W := mkw 0x27090000cc240004 0x8938480006612000 0x0700000000000000 0x0038000000000000

def z580 : W := mkw 0x1862240103888400 0x00c31120081c4420 0x38e3e6010f8fc71b 0xf1c71f30087c7e38

def z581 : W := mkw 0xc8b47d6b31d1fec3 0x0645a3eb598e8ff6 0xc0fc7ffff0f1fffd 0xfe07e3ffff878fff

def z582 : W := mkw 0x25000040dd01b602 0x0928000206e80db0 0xff000001ff01ff1f 0x3ff800000ff80ff8

def z583 : W := mkw 0x00048af000121b60 0x50002457800090db 0x00039ff0088e3ff3 0xd0001cff804471ff

def z584 : W := mkw 0x1b4faef48b3e9f60 0x70da7d77a459f4fb 0x3f1f9ff08ffe3ff7 0xd1f8fcff847ff1ff

def z585 : W := mkw 0x1962a617efeec5a4 0x20cb1530bf7f762d 0x38e3e63fffffc7fb 0xf1c71f31fffffe3f

def z586 : W := mkw 0x4004582010112840 0x020022c100808942 0xc01c7831f0f1f8fd 0xfe00e3c18f878fc7

def z587 : W := mkw 0x3e4ba794030a8528 0xe9f25d3ca0185429 0x3f0387c00f0e0702 0x01f81c3e00787038

def z588 : W := mkw 0xfffb7501eeec0004 0x8fffdba80f776000 0xffffffc1fffe001f 0xeffffffe0ffff000

def z589 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x380386010f8fc7e3 0x31c01c30087c7e3f

def z590 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xf8006001ff01ff09 0x3fc003000ff80ff8

def z591 : W := mkw 0x1842a61400000000 0x00c21530a0000000 0x3803860000000002 0x01c01c3000000000

def z592 : W := mkw 0xfcf2750f0388c488 0xafe793a8781c4624 0xf8e0600f0701c008 0x2fc7030078380e00

def z593 : W := mkw 0x3d62a757cf8ad7a2 0x29eb153abe7c56bd 0x3fe3e7ff0f8fc7fb 0xf1ff1f3ff87c7e3f

def z594 : W := mkw 0x65005000dc012000 0x0b28028006e00900 0xff007801ff01f81f 0x7ff803c00ff80fc0

def z595 : W := mkw 0xb4f2000166c80004 0x8da790000b364000 0xf8e380017f8e001b 0xafc71c000bfc7000

def z596 : W := mkw 0x65005140dc013202 0x0b28028a06e00990 0xc7001fc0f8003f17 0x5e3800fe07c001f8

def z597 : W := mkw 0xf4f6582b76d968c5 0x8fa7b2c15bb6cb46 0xf8fc783ff7f1f8fd 0xffc7e3c1ffbf8fc7

def z598 : W := mkw 0xfcf67d2f30d168c9 0x8fe7b3e979868b46 0xf8fc783ff0f1f8fd 0xffc7e3c1ff878fc7

def z599 : W := mkw 0x136f8af18abe1b60 0x509b7c578c55f0db 0x3fff9ff18ffe3fff 0xf1fffcff8c7ff1ff

def z600 : W := mkw 0x65005140dc013202 0x0b28028a06e00990 0xff0019c1ff00381f 0x2ff800ce0ff801c0

def z601 : W := mkw 0x6c0075005501a402 0x0b6003a802a80d20 0xff007fc17701c01e 0x6ff803fe0bb80e00

def z602 : W := mkw 0x0000000001008400 0x0000000000080420 0x000000010f01c701 0x3000000008780e38

def z603 : W := mkw 0x11620001eeec0004 0x008b10000f776000 0x38e38001fffe001b 0xa1c71c000ffff000

def z604 : W := mkw 0xdbfffeffbbffffe1 0x76dffff7fddfffff 0xffffffffffffffff 0xffffffffffffffff

def z605 : W := mkw 0xb4d2000000000000 0x8da6900000000000 0xf8e0000000000008 0x0fc7000000000000

def z606 : W := mkw 0x80b4082b20d048c1 0x0405a04159068246 0x00fc603f00f1c0f9 0xf007e301f8078e07

def z607 : W := mkw 0xfffffffffdd1fecb 0xcfffffffffee8ff6 0xfffffffffff1ffff 0xffffffffffff8fff

def z608 : W := mkw 0x0100004088001200 0x0008000204400090 0x070019c080003804 0x003800ce040001c0

def z609 : W := mkw 0xfcd6ffbc00000008 0xcfe6b7fde0000000 0xf8e07ffe00000008 0x4fc703fff0000000

def z610 : W := mkw 0x0020000330d168c1 0x0001000019868b46 0x00e0603ff0f1f8f9 0xf0070301ff878fc7

def z611 : W := mkw 0x08202403038ac5a0 0x20410120181c562d 0x380066010f8fc7fb 0x71c00330087c7e3f

def z612 : W := mkw 0xc094582830512841 0x0604a2c141828942 0xc01c7801f071f81d 0x7e00e3c00f838fc0

def z613 : W := mkw 0x2d002540cd009602 0x0968012a066804b0 0x3f0067c10f01c71b 0x71f8033e08780e38

def z614 : W := mkw 0x2400000000000000 0x0920000000000000 0xff0000000000001e 0x0ff8000000000000

def z615 : W := mkw 0x4024582b30d168c1 0x020122c159868b46 0x0000783ff0f1f8e1 0x700003c1ff878fc7

def z616 : W := mkw 0x92ff8abd22ec000c 0xc497fc55e9176000 0x00ff803e00fe0000 0x8007fc01f007f000

def z617 : W := mkw 0x186224070388c480 0x20c31120381c4624 0x38e0603f0781c0f9 0xf1c70301f83c0e07

def z618 : W := mkw 0x030d08e088341a40 0x501868470441a0d2 0x071c1fc088703f17 0x5038e0fe044381f8

def z619 : W := mkw 0xbffb2407efecc484 0xadffd9203f7f6624 0xffffe00fffffc01f 0xafffff007ffffe00

def z620 : W := mkw 0xb5f20001eeec0004 0x8daf90000f776000 0xf8e00001fffe0009 0x2fc700000ffff000

def z621 : W := mkw 0x01048af088121b60 0x50082457844090db 0x07001ff088003ff7 0x503800ff844001ff

def z622 : W := mkw 0x4004582a101168c1 0x020022c150808b46 0xc000783ff001f8fd 0x7e0003c1ff800fc7

def z623 : W := mkw 0x0100004088361b60 0x100800020441b0db 0x07001fc088fe3ff7 0x503800fe0447f1ff

def z624 : W := mkw 0xc0b0500b30c16081 0x0605828059860b04 0xc0e0780ff001f81d 0x7e0703c07f800fc0

def z625 : W := mkw 0x2400000044000000 0x0920000002200000 0xf800000177000008 0x2fc000000bb80000

def z626 : W := mkw 0x4800750c00000008 0x024003a860000000 0x0000600e00000000 0x0000030070000000

def z627 : W := mkw 0x2c00250045008402 0x0960012802280420 0x3800000007000000 0x01c0000000380000

def z628 : W := mkw 0xf7ff59a9eeec000c 0xcfbffacd4f776000 0xffff99c1fffe001f 0xaffffcce0ffff000

def z629 : W := mkw 0x7d627547df89f682 0x2beb13aa3efc4fb4 0xffe07fcfff01ff1f 0x7fff03fe7ff80ff8

def z630 : W := mkw 0xb7fb8211eeee0124 0x8dbfdc108f777009 0xffff8631fffe07ff 0xfffffc318ffff03f

def z631 : W := mkw 0x376b0001eeec0004 0x89bb58000f776000 0x3f038001fffe0003 0x21f81c000ffff000

def z632 : W := mkw 0xee9d7da800000008 0xcf74ebed40000000 0xff1c7fc00000001e 0x4ff8e3fe00000000

def z633 : W := mkw 0x0309004088241200 0x0018480204412090 0x071f9fc088fe3f17 0xd038fcfe0447f1f8

def z634 : W := mkw 0x030d8af088001200 0x40186c5784400090 0x071f9ff088003f17 0xd038fcff844001f8

def z635 : W := mkw 0x124b829400000008 0xc0925c14a0000000 0x0003800000000000 0x00001c0000000000

def z636 : W := mkw 0x374b0000ce2c0004 0x89ba580006716000 0xff038001ff0e001f 0x2ff81c000ff87000

def z637 : W := mkw 0xb7fb0003fefd68c5 0x8dbfd8001ff7eb46 0xffff8001fffff8ff 0xbffffc000fffffc7

def z638 : W := mkw 0xbcf2240767c8c484 0xade791203b3e4624 0xf8e0600f7701c008 0x2fc703007bb80e00

def z639 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xff1f9fc000000006 0x0ff8fcfe00000000

def z640 : W := mkw 0x41005040dd01b602 0x0208028206e80db0 0xc0007801ff01ff1d 0x7e0003c00ff80ff8

def z641 : W := mkw 0xb7ff8ab1eefe0964 0xddbffc558f77f04b 0xffff8031fffe00ff 0xaffffc018ffff007

def z642 : W := mkw 0x7f6ffff7dfbfffe2 0x7bfb7fffbefdffff 0xffffffffffffffff 0xffffffffffffffff

def z643 : W := mkw 0x35620001ce880000 0x09ab10000e744000 0xffe38001ff8e001f 0xafff1c000ffc7000

def z644 : W := mkw 0x8094082820500841 0x0404a04141028042 0x001c000000700000 0x0000e00000038000

def z645 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xc7007fc0f001ff04 0x5e3803fe07800ff8

def z646 : W := mkw 0xb6df8ab000000000 0xcdb6fc5580000000 0xffff9ff00000001e 0xcffffcff80000000

def z647 : W := mkw 0xfedfffbe0102c5a8 0xeff6fffdf008162d 0xfffffffe0001c7fe 0xdffffffff0000e3f

def z648 : W := mkw 0x00000000030a8520 0x2000000000185429 0x000000000f0e0700 0x0000000000787038

def z649 : W := mkw 0x020d8ab000020120 0x40106c5580001009 0x071f9ff0088e07f7 0xd038fcff8044703f

def z650 : W := mkw 0xdadfffbc00000008 0xc6d6fffde0000000 0x00fffffe00000000 0xc007fffff0000000

def z651 : W := mkw 0x032d8af3b8f77be1 0x50196c579dc7bbdf 0x071f9ff1f8fffff7 0xf038fcff8fc7ffff

def z652 : W := mkw 0x92ff8abf028a41a8 0xe497fc55f814520d 0x00ff803e008e00e0 0x8007fc01f0047007

def z653 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0000001f000001d 0x2e0000000f800000

def z654 : W := mkw 0x98f2a61723cac5a0 0x24c79530b91e562d 0xf8ffe63fffffc7ff 0xffc7ff31fffffe3f

def z655 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f99f080fe38e4 0x8038fccf8407f1c7

def z656 : W := mkw 0x124b0000022c0004 0x8092580000116000 0x00038000000e0000 0x00001c0000007000

def z657 : W := mkw 0xe79d5828fc752845 0x8f3ceac147e3a942 0xc71c1800f0703804 0x0e38e0c0078381c0

def z658 : W := mkw 0x480075001101a402 0x024003a800880d20 0x000060000001c000 0x0000030000000e00

def z659 : W := mkw 0x0209829000000000 0x40104c1480000000 0x070387c000000002 0x00381c3e00000000

def z660 : W := mkw 0x1842a61400020120 0x00c21530a0001009 0x38e3e63e088e07fb 0xd1c71f31f044703f

def z661 : W := mkw 0xf7fb5001feed2004 0x8fbfda800ff76900 0xfffff801fffff81f 0xffffffc00fffffc0

def z662 : W := mkw 0xc3bd582bb8f568c1 0x061deac15dc7ab46 0xc7fff83ff8fff8ff 0xfe3fffc1ffc7ffc7

def z663 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e60f0f0fc70a 0x21c71f3078787e38

def z664 : W := mkw 0xffdffffccd00960a 0xcffeffffe66804b0 0xfffffffe0f00071e 0xcffffffff0780038

def z665 : W := mkw 0x0100004088001200 0x0008000204400090 0x0000000088003f01 0x10000000044001f8

def z666 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0x00fc783e00f1f8e0 0xd007e3c1f0078fc7

def z667 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0x3f007fc00f01ff02 0x51f803fe00780ff8

def z668 : W := mkw 0x7e4fffbc00000008 0xcbf27ffde0000000 0x3f03fffe00000002 0x41f81ffff0000000

def z669 : W := mkw 0x0000000000100840 0x0000000000008042 0x0000000080f038e1 0x10000000040781c7

def z670 : W := mkw 0xb7ff082beefc48c5 0x8dbff8415f77e246 0xffff803ffffe00ff 0xaffffc01fffff007

def z671 : W := mkw 0xb7db0000cc000000 0x8dbed80006600000 0xffff8001ff00001f 0xaffffc000ff80000

def z672 : W := mkw 0x0000000200004080 0x0000000010000204 0x0000603e0001c0e0 0x50000301f0000e07

def z673 : W := mkw 0xc39ddaf8b8773b61 0x561ceed7c5c3b9db 0xc71f9ff0f8fe3ff7 0xde38fcff87c7f1ff

def z674 : W := mkw 0x030982d088261320 0x50184c1684413099 0x070387f0088e07f3 0xd0381c3f8044703f

def z675 : W := mkw 0xbefba617038ac5a0 0xadf7dd30b81c562d 0xffffe63f0f8fc7ff 0xffffff31f87c7e3f

def z676 : W := mkw 0x6d047d6add11fec3 0x0b6823eb56e88ff6 0xff007fffff01ffff 0x7ff803fffff80fff

def z677 : W := mkw 0x4000514010013202 0x0200028a00800990 0x000019c000003800 0x000000ce000001c0

def z678 : W := mkw 0x3f4ba614cf2e8524 0xa9fa5d30a6797429 0x3f0386000f0e0702 0x01f81c3000787038

def z679 : W := mkw 0x4004582810112841 0x020022c140808942 0x0000180000003800 0x000000c0000001c0

def z680 : W := mkw 0xef997540fd65b606 0x8f7ccbaa07eb2db0 0xff1c7fc1ff71ff1f 0x7ff8e3fe0ffb8ff8

def z681 : W := mkw 0x00048af000121b60 0x50002457800090db 0x001c1ff080f03ff5 0xd000e0ff840781ff

def z682 : W := mkw 0x0000000000020120 0x0000000000001009 0x00000000088e07e1 0x100000000044703f

def z683 : W := mkw 0xa7990000ec640004 0x8d3cc80007632000 0xff1c0001ff70001f 0x2ff8e0000ffb8000

def z684 : W := mkw 0xfcd2750c5501a40a 0x8fe693a862a80d20 0xf8e0600f7701c008 0x2fc703007bb80e00

def z685 : W := mkw 0xffffffffb8f77be9 0xdffffffffdc7bbdf 0xfffffffff8ffffff 0xffffffffffc7ffff

def z686 : W := mkw 0x1842a614030a8520 0x20c21530a0185429 0x3803e6010f0fc71b 0x71c01f3008787e38

def z687 : W := mkw 0x9affaebf038ac5a8 0xe4d7fd75f81c562d 0x38ffe63f0f8fc7fb 0xf1c7ff31f87c7e3f

def z688 : W := mkw 0xd8f67c2f33d9ecc1 0x26c7b3e1799ecf66 0xf8fc783ff7f1f8fd 0xffc7e3c1ffbf8fc7

def z689 : W := mkw 0xfeffffbf33dbede9 0xeff7fffdf99edf6f 0xffffffffffffffff 0xffffffffffffffff

def z690 : W := mkw 0x65005140dc013202 0x0b28028a06e00990 0xc70079c1f001f81d 0x7e3803ce0f800fc0

def z691 : W := mkw 0x1862a6170388c480 0x20c31530b81c4624 0x38e3e63f0701c01a 0xe1c71f31f8380e00

def z692 : W := mkw 0xb7fb8217eeee41a4 0xadbfdc10bf77720d 0xffff803ffffe00ff 0xaffffc01fffff007

def z693 : W := mkw 0x480074001101a400 0x024003a000880d20 0xf8007e01ff01ff1f 0x7fc003f00ff80ff8

def z694 : W := mkw 0x0800a61400000000 0x00400530a0000000 0x0000663e00000000 0x40000331f0000000

def z695 : W := mkw 0xa699000000000000 0x8d34c80000000000 0xc71c000000000004 0x0e38e00000000000

def z696 : W := mkw 0xf6ff582b30d168c1 0x8fb7fac159868b46 0xfffff83ff0f1f8ff 0xffffffc1ff878fc7

def z697 : W := mkw 0x00008216000241a0 0x20000410b000120d 0x0000003e000000e0 0x00000001f0000007

def z698 : W := mkw 0x0800a61401028520 0x20400530a0081429 0x0000060000000700 0x0000003000000038

def z699 : W := mkw 0xe7bd582bfcf568c5 0x8f3deac15fe7ab46 0xc7fc783ff0f1f8fd 0xfe3fe3c1ff878fc7

def z700 : W := mkw 0x48047d6a1111fec3 0x024023eb50888ff6 0x00007ffe0001ffe0 0x500003fff0000fff

def z701 : W := mkw 0xed947d68fd51be43 0x0f6ca3eb47ea8df2 0xff1c7fc1ff71ff1f 0x7ff8e3fe0ffb8ff8

def z702 : W := mkw 0x00048abc00000008 0x40002455e0000000 0x0000003e00000000 0x00000001f0000000

def z703 : W := mkw 0xb7ff08e1eefc1a44 0xddbff8470f77e0d2 0xffff99c1fffe381f 0xaffffcce0ffff1c0

def z704 : W := mkw 0xd8f2740f33c9e481 0x26c793a0799e4f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z705 : W := mkw 0x000000401101b602 0x0000000200880db0 0x000000000001ff00 0x1000000000000ff8

def z706 : W := mkw 0xb7fb0041ffedb606 0x8dbfd8020fff6db0 0xffff8001ffffff1f 0xbffffc000ffffff8

def z707 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff8031fffe00ff 0xfffffc018ffff007

def z708 : W := mkw 0x376b0001ceac0000 0x09bb58000e756000 0xffff8001fffe001f 0xaffffc000ffff000

def z709 : W := mkw 0xfedfffbc30412009 0xcff6fffde1820900 0xfffffffe7000001e 0xcffffffff3800000

def z710 : W := mkw 0xe6bd59ab038ac5a8 0xef35eacd581c562d 0xc71c19c10f8fc7e5 0x3e38e0ce087c7e3f

def z711 : W := mkw 0x10620003038ac5a0 0x20831000181c562d 0x38e3e03f0f8fc7fb 0xf1c71f01f87c7e3f

def z712 : W := mkw 0x4804fffc1113bf6a 0x524027ffe0889dfb 0x00007ffe0001ffe0 0x500003fff0000fff

def z713 : W := mkw 0xb4f68af166da1b64 0xdda7b4578b36d0db 0xf8e01ff177003fe8 0x7fc700ff8bb801ff

def z714 : W := mkw 0x1942a654dd01b602 0x00ca1532a6e80db0 0x38e3e63fff01ff1b 0xf1c71f31fff80ff8

def z715 : W := mkw 0x93df8afcdd01b60a 0xc49efc57e6e80db0 0x00ff803fff01ff01 0xb007fc01fff80ff8

def z716 : W := mkw 0x1862a61723cac5a0 0x20c31530b91e562d 0x38e3e63fffffc7fb 0xf1c71f31fffffe3f

def z717 : W := mkw 0x7c42750400000000 0x0be213a820000000 0xffe07fce0000001e 0x4fff03fe70000000

def z718 : W := mkw 0xfedfffbc1101a40a 0xcff6fffde0880d20 0xfffffffe0001c01e 0xcffffffff0000e00

def z719 : W := mkw 0xfedfffbc30512849 0xcff6fffde1828942 0xfffffffff071f81f 0xffffffffff838fc0

def z720 : W := mkw 0x91f20001eeec0004 0x048f90000f776000 0xf8ff8001fffe001f 0xafc7fc000ffff000

def z721 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38ffe63f8fffc7ff 0xf1c7ff31fc7ffe3f

def z722 : W := mkw 0x774f582ade3d68c5 0x8bba7ac156f1eb46 0x3f03f83e0f0ff8e2 0x51f81fc1f0787fc7

def z723 : W := mkw 0x6c0075405501b602 0x0b6003aa02a80db0 0xff007fc17701ff1e 0x7ff803fe0bb80ff8

def z724 : W := mkw 0xfedfffbc10012008 0xcff6fffde0800900 0xfffffffe0001f81e 0xdffffffff0000fc0

def z725 : W := mkw 0xe69d59a800000008 0xcf34eacd40000000 0xc7fc19fe00000004 0x8e3fe0cff0000000

def z726 : W := mkw 0x3e6ba79730d168c9 0xc9f35d3cb9868b46 0x3f0387c1f0f1f8e3 0x31f81c3e0f878fc7

def z727 : W := mkw 0x0820a6130182c5a0 0x00410530980c162d 0x38e3e63f0f8fc7fb 0xf1c71f31f87c7e3f

def z728 : W := mkw 0xb5f20001eec80000 0x0daf90000f764000 0xffff8001fffe001f 0xaffffc000ffff000

def z729 : W := mkw 0x124f8ab400000000 0x40927c55a0000000 0x07ff9ffe00000016 0xc03ffcfff0000000

def z730 : W := mkw 0xfcf2750b77c9e487 0x8fe793a85bbe4f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z731 : W := mkw 0xf6dfdbbc00000008 0xcfb6fedde0000000 0xc7ff9ffe00000016 0xce3ffcfff0000000

def z732 : W := mkw 0xfedfffbc01028528 0xeff6fffde0081429 0xfffffffe0000071e 0xcffffffff0000038

def z733 : W := mkw 0xe6bd59ab30d168c9 0xcf35eacd59868b46 0xc71c19c1f0f1f8e5 0x3e38e0ce0f878fc7

def z734 : W := mkw 0xa7b90001ece40000 0x0d3dc8000f672000 0xffff8001fffe001f 0xaffffc000ffff000

def z735 : W := mkw 0xfedfffbc20400008 0xcff6fffde1020000 0xfffffffef070001e 0xcffffffff7838000

def z736 : W := mkw 0xdafb754133edb606 0x86d7dbaa099f6db0 0x00ffffc000ffff00 0xd007fffe0007fff8

def z737 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071ffff188ffffff 0xf038ffff8c47ffff

def z738 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xffff9ffe00000006 0x8ffffcfff0000000

def z739 : W := mkw 0x01048a7088121b60 0x00082453844090db 0x071f9ff088fe3ff7 0xd038fcff8447f1ff

def z740 : W := mkw 0x01200043fcd17ac3 0x000900021fe68bd6 0x00000001f0f1f8e1 0x300000000f878fc7

def z741 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffe008000ff 0xdffffffff0040007

def z742 : W := mkw 0x01200043b8d17ac1 0x000900021dc68bd6 0x00000001f8f1ffe1 0x300000000fc78fff

def z743 : W := mkw 0x5a4fffbc00000008 0x42d27ffde0000000 0x3ffffffe0000001e 0xc1fffffff0000000

def z744 : W := mkw 0x6e0dffb05537ad62 0x5b706ffd82a9bd6b 0xf81fe03177ffc0e8 0xafc0ff018bbffe07

def z745 : W := mkw 0xfedfffbc00100848 0xcff6fffde0008042 0xfffffffe00f000fe 0xcffffffff0078007

def z746 : W := mkw 0x3f4ba754cf2e9726 0xa9fa5d3aa67974b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z747 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e63e0f8fc7e2 0xd1c71f31f07c7e3f

def z748 : W := mkw 0xb7fb000deeec000c 0x8dbfd8006f776000 0xffff800ffffe001f 0xaffffc007ffff000

def z749 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc7fc7ffff0f1f8ff 0xfe3fe3ffff878fc7

def z750 : W := mkw 0x01200043dd81f682 0x000900021eec0fb4 0x00000001ff81ffe1 0x300000000ffc0fff

def z751 : W := mkw 0xfcd2750c00000008 0x8fe693a860000000 0xffe067ce0000000a 0x0fff033e70000000

def z752 : W := mkw 0x4804fefe1113ffe1 0x724027f7f0889fff 0x00007ffe0001ffe0 0x500003fff0000fff

def z753 : W := mkw 0xee9dffb800000000 0x4f74effdc0000000 0xfffffffe0000001e 0xcffffffff0000000

def z754 : W := mkw 0x93df8afc88361b68 0xd49efc57e441b0db 0x00ff803e88fe3fe1 0x9007fc01f447f1ff

def z755 : W := mkw 0xfedfffbc01008408 0xcff6fffde0080420 0xfffffffe0001c71e 0xdffffffff0000e38

def z756 : W := mkw 0x7562d357de8b73a2 0x2bab169abef45b9d 0xc7e399fef08e38e4 0x8e3f1ccff78471c7

def z757 : W := mkw 0xfedf7d2800000000 0x8ff6fbe940000000 0xfffffffe0000001e 0xcffffffff0000000

def z758 : W := mkw 0xc1945868dd01b602 0x060ca2c346e80db0 0xc0fc783fff01ff1d 0xfe07e3c1fff80ff8

def z759 : W := mkw 0xb6fb000166ec0004 0x8db7d8000b376000 0xffff800177fe001e 0xaffffc000bbff000

def z760 : W := mkw 0xc3b9d2dbb8e773a1 0x561dce96ddc73b9d 0xc7e3e7cf780fc70a 0x2e3f1f3e7bc07e38

def z761 : W := mkw 0xfcd2750c00000008 0x8fe693a860000000 0xffe079ce0000000c 0x0fff03ce70000000

def z762 : W := mkw 0xbedba79400000008 0xcdf6dd3ca0000000 0xffffe7fe0000001e 0xcfffff3ff0000000

def z763 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xff1f8001fffe0007 0x2ff8fc000ffff000

def z764 : W := mkw 0xd8d6fe3c335bad61 0x26c6b7f1e19add6b 0xf81f9e00ff7e3f06 0x0fc0fcf007fbf1f8

def z765 : W := mkw 0x4924ffbdeeec000c 0x424927fdef776000 0x00007ffffffe0001 0x600003fffffff000

def z766 : W := mkw 0x1b6f2ce78bbcdec0 0x70db79673c5de6f6 0x3ffc79cf8771f80c 0x21ffe3ce7c3b8fc0

def z767 : W := mkw 0xfdd2754c88361b68 0x9fee93aa6441b0db 0xf8e0600e88fe3fe9 0x1fc703007447f1ff

def z768 : W := mkw 0x88b0a61721c2c5a0 0x24458530b90e162d 0xc0fc663ff0f1c7fd 0xfe07e331ff878e3f

def z769 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e03f0f8fc7e9 0xb1c71f01f87c7e3f

def z770 : W := mkw 0xc094582a305168c1 0x0604a2c151828b46 0xc0fc783ef071f8fc 0xde07e3c1f7838fc7

def z771 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffffe03ffffe001f 0xefffff01fffff000

def z772 : W := mkw 0x030d8afc88361b68 0x50186c57e441b0db 0x071f9ffe88fe3ff7 0xd038fcfff447f1ff

def z773 : W := mkw 0xb7fb0007eeec4084 0xadbfd8003f776204 0xffff800ffffe001f 0xaffffc007ffff000

def z774 : W := mkw 0x0309004088361b60 0x101848020441b0db 0x071f9fc088fe3ff7 0xd038fcfe0447f1ff

def z775 : W := mkw 0xfcf2750777c9e486 0xafe793a83bbe4f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z776 : W := mkw 0xfedbf71400000000 0x8ff6dfb8a0000000 0xfffffffe0000001e 0xcffffffff0000000

def z777 : W := mkw 0xb7db0000ee6c0004 0x8dbed80007736000 0xff1f8001ff7e001f 0x2ff8fc000ffbf000

def z778 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc783ff0f1f8ec 0xae07e3c1ff878fc7

def z779 : W := mkw 0x012000438baed7a0 0x300900021c5d76bd 0x000000010f8fc7e1 0x30000000087c7e3f

def z780 : W := mkw 0x022d8ab330d168c1 0x40116c5599868b46 0x071f9ff1f0f1f8f7 0xf038fcff8f878fc7

def z781 : W := mkw 0xfedbf79c00000008 0xcff6dfbce0000000 0xffffe7ce0000001e 0x8fffff3e70000000

def z782 : W := mkw 0xb7fb0041eeec1204 0x8dbfd8020f776090 0xffff87c1fffe071f 0xaffffc3e0ffff038

def z783 : W := mkw 0x186224030388c480 0x00c31120181c4624 0x38e3e63f0f8fc7fb 0xf1c71f31f87c7e3f

def z784 : W := mkw 0x9adfaebc00000008 0xc4d6fd75e0000000 0x3ffffffe0000001e 0xc1fffffff0000000

def z785 : W := mkw 0xc094582810112840 0x0604a2c140808942 0xc0fc783ff0f1f8fd 0xfe07e3c1ff878fc7

def z786 : W := mkw 0xfedb758c00000008 0xcff6dbac60000000 0xffe061ce00000008 0x0fff030e70000000

def z787 : W := mkw 0xb7fb0003eeec4084 0x8dbfd8001f776204 0xffffe00fffffc01f 0xafffff007ffffe00

def z788 : W := mkw 0xfcd6ffbc00000008 0xcfe6b7fde0000000 0xffe07ffe0000001e 0x4fff03fff0000000

def z789 : W := mkw 0x0309825088261320 0x00184c1284413099 0x071f9ff088fe3ff7 0xd038fcff8447f1ff

def z790 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fff83ff8fff8ff 0xfe07ffc1ffc7ffc7

def z791 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xffffffff0001c01f 0xfffffffff8000e00

def z792 : W := mkw 0x3f4ba6d4cf2e9724 0xf9fa5d36a67974b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z793 : W := mkw 0xfedfffbc44000008 0xcff6fffde2200000 0xffffffff7700001e 0xeffffffffbb80000

def z794 : W := mkw 0xadb42d6bedd0dec3 0x0d6da16b5f6e86f6 0x3ffc07fe0ff007e2 0x81ffe03ff07f803f

def z795 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffe0800071f 0xdffffffff0400038

def z796 : W := mkw 0xbedfafbc00000008 0xcdf6fd7de0000000 0x3fffe7fe0000001a 0xc1ffff3ff0000000

def z797 : W := mkw 0xdadfffbc00000008 0xc6d6fffde0000000 0x07fffffe00000016 0xc03ffffff0000000

def z798 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffffe001ffffc01f 0xffffff000ffffe00

def z799 : W := mkw 0x3e4ba79400000008 0xc9f25d3ca0000000 0x3fe3e7ce0000000a 0x01ff1f3e70000000

def z800 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xffffe7fe0000000a 0x8fffff3ff0000000

def z801 : W := mkw 0xe494592800000000 0x0f24a2c940000000 0xc7fc79fe0000001c 0xce3fe3cff0000000

def z802 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffe80f0001f 0xcffffffff4078000

def z803 : W := mkw 0xaf99a616ed66c5a4 0xad7ccd30b76b362d 0xc71c663ef071c7e4 0x5e38e331f7838e3f

def z804 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xffffffce0000000e 0x0ffffffe70000000

def z805 : W := mkw 0xec94ffbc00000008 0x4f64a7fde0000000 0xfffc7ffe0000001e 0xcfffe3fff0000000

def z806 : W := mkw 0x01200043b8f57ac1 0x100900021dc7abd6 0x00000001f0f1f8e1 0x300000000f878fc7

def z807 : W := mkw 0xfcd67d2c00000008 0x8fe6b3e960000000 0xfffc7ffe0000001e 0xcfffe3fff0000000

def z808 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff8000fffe0006 0x8ffffc0007fff000

def z809 : W := mkw 0x01200043fdf7ffe3 0x100900021fefbfff 0x00000001ffffffe1 0x300000000fffffff

def z810 : W := mkw 0x6d00754cdd01b60a 0x0b6803aa66e80db0 0xff007fcfff01ff1f 0x7ff803fe7ff80ff8

def z811 : W := mkw 0x012000438abe5be0 0x300900021c55f2df 0x0000000088fe3fe1 0x100000000447f1ff

def z812 : W := mkw 0x5066582b129968c1 0x028332c15894cb46 0x38e3f83f0f8ff8fb 0xf1c71fc1f87c7fc7

def z813 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffff9fe0000000c 0x8fffffcff0000000

def z814 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff007ff1ff81ffff 0xfff803ff8ffc0fff

def z815 : W := mkw 0x93fb0001aaec0000 0x049fd8000d576000 0xffff8001fffe001f 0xaffffc000ffff000

def z816 : W := mkw 0x3e4fafb400000008 0xc9f27d7da0000000 0x3ffffffe0000001e 0xc1fffffff0000000

def z817 : W := mkw 0xb6fb000166ec0004 0x8db7d8000b376000 0xf8ff80017ffe001b 0xafc7fc000bfff000

def z818 : W := mkw 0xfedfffbc01008408 0xcff6fffde0080420 0xffffffff0701c01e 0xeffffffff8380e00

def z819 : W := mkw 0xfcd6ff3c00000000 0x0fe6b7f9e0000000 0xfffffffe0000001e 0xcffffffff0000000

def z820 : W := mkw 0xe79d59e8fc753a43 0x5f3ceacf47e3a9d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z821 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff001fc1ff01ff07 0x3ff800fe0ff80ff8

def z822 : W := mkw 0xb6fb000122c80000 0x8db7d80009164000 0xffff8001fffe001f 0xaffffc000ffff000

def z823 : W := mkw 0xbedfaeb400000000 0xcdf6fd75a0000000 0xfffffffe0000001e 0xcffffffff0000000

def z824 : W := mkw 0xf6df59ac00000008 0xcfb6facd60000000 0xc7fc19ce00000004 0x0e3fe0ce70000000

def z825 : W := mkw 0xe79d58e8fc753a45 0xdf3ceac747e3a9d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z826 : W := mkw 0x020d8af000361b60 0x50106c578001b0db 0x071f9ff000fe3ff6 0xd038fcff8007f1ff

def z827 : W := mkw 0xfedfffbc01008408 0xcff6fffde0080420 0xfffffffe0f00071e 0xcffffffff0780038

def z828 : W := mkw 0xb7fb00c1eeec1204 0xddbfd8060f776090 0xffff81c1fffe001f 0xaffffc0e0ffff000

def z829 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xc7fffffe00000004 0xce3ffffff0000000

def z830 : W := mkw 0x0120004388b65be0 0x100900021c45b2df 0x0000000188ffffe1 0x300000000c47ffff

def z831 : W := mkw 0xb7db0000ee6c0004 0x8dbed80007736000 0xffff8000ff7e001e 0x8ffffc0007fbf000

def z832 : W := mkw 0x92ff8ab722fe49e4 0xf497fc55b917f24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z833 : W := mkw 0x7e4fffbc00000008 0xcbf27ffde0000000 0x3fe3fffe0000001a 0xc1ff1ffff0000000

def z834 : W := mkw 0xb7db0000cc240000 0x8dbed80006612000 0xffff8001fffe001f 0xaffffc000ffff000

def z835 : W := mkw 0x3c42a71400000000 0x09e21538a0000000 0x3fe3e7fe0000001a 0xc1ff1f3ff0000000

def z836 : W := mkw 0xfedfffbc01028528 0xcff6fffde0081429 0xffffffff0f8fc7ff 0xfffffffff87c7e3f

def z837 : W := mkw 0xe69ddbb800000008 0xcf34eeddc0000000 0xc7fffffe0000001e 0xce3ffffff0000000

def z838 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xffe07fffff01ff1f 0xffff03fffff80ff8

def z839 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0xf8e3e63fff8fc7ff 0xffc71f31fffc7e3f

def z840 : W := mkw 0x01200043cf8ad7a2 0x200900021e7c56bd 0x000000010f8fc7e1 0x30000000087c7e3f

def z841 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffe088e001f 0xcffffffff0447000

def z842 : W := mkw 0x2d002440cd009600 0x09680122066804b0 0xff007fc1ff01ff1f 0x7ff803fe0ff80ff8

def z843 : W := mkw 0x25000040dd01b602 0x0928000206e80db0 0xff001fc1ff01ff1f 0x7ff800fe0ff80ff8

def z844 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc783ef0f1f8e4 0xde07e3c1f7878fc7

def z845 : W := mkw 0xc0b0500330c16080 0x0605828019860b04 0xc0fc783ff0f1f8fd 0xfe07e3c1ff878fc7

def z846 : W := mkw 0xfedf7dac00000008 0xcff6fbed60000000 0xfffc7fce0000001e 0x4fffe3fe70000000

def z847 : W := mkw 0xc29d58a800000000 0x4614eac540000000 0xc7fc79fe0000001c 0xce3fe3cff0000000

def z848 : W := mkw 0x92df8abc00000008 0xc496fc55e0000000 0x07ff87fe00000002 0x803ffc3ff0000000

def z849 : W := mkw 0xec90750800000000 0x0f6483a840000000 0xffe07fce0000001e 0x4fff03fe70000000

def z850 : W := mkw 0xf6df59a800000008 0xcfb6facd40000000 0xfffff9fe0000001e 0xcfffffcff0000000

def z851 : W := mkw 0x6c0075001101a400 0x0b6003a800880d20 0xff007fc1ff01ff1f 0x7ff803fe0ff80ff8

def z852 : W := mkw 0xfedfffbc5401200a 0xcff6fffde2a00900 0xfffffffe7000001e 0xcffffffff3800000

def z853 : W := mkw 0xfdd2754cdd01b60a 0x8fee93aa66e80db0 0xf8e0600fff01ff09 0x3fc703007ff80ff8

def z854 : W := mkw 0x7e4bf79400000008 0xcbf25fbca0000000 0xffe3fffe0000001e 0xcfff1ffff0000000

def z855 : W := mkw 0xb6df8bbc00000008 0xcdb6fc5de0000000 0x07ff81fe00000000 0x803ffc0ff0000000

def z856 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff80017ffe000a 0xaffffc000bfff000

def z857 : W := mkw 0xfedfffbc00100848 0xcff6fffde0008042 0xfffffffe000038fe 0xdffffffff00001c7

def z858 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff8601fffe071f 0xfffffc300ffff038

def z859 : W := mkw 0x1842a61401028520 0x00c21530a0081429 0x38e3e63f0f8fc7fb 0xf1c71f31f87c7e3f

def z860 : W := mkw 0x01200043feff7be5 0x100900021ff7fbdf 0x00000001ffffffe1 0x300000000fffffff

def z861 : W := mkw 0x7e4fffb400000000 0x4bf27ffda0000000 0xfffffffe0000001e 0xcffffffff0000000

def z862 : W := mkw 0x01200043fdc1f683 0x000900021fee0fb4 0x00000001ff01ff01 0x300000000ff80ff8

def z863 : W := mkw 0xfedb750c00000008 0x8ff6dba860000000 0xffffffce0000001e 0xcffffffe70000000

def z864 : W := mkw 0x1942a65488361b60 0x10ca1532a441b0db 0x38e3e63e88fe3ffb 0xd1c71f31f447f1ff

def z865 : W := mkw 0xf6dfdbbc00000008 0xcfb6fedde0000000 0xffff99fe0000001e 0x8ffffccff0000000

def z866 : W := mkw 0xb7fb0141eeec1206 0x8dbfd80a0f776090 0xffff81c1fffe001f 0xaffffc0e0ffff000

def z867 : W := mkw 0xdadffebc00000000 0x46d6fff5e0000000 0xfffffffe0000001e 0xcffffffff0000000

def z868 : W := mkw 0xfedf7dac00000008 0xcff6fbed60000000 0xfffff9ce0000001e 0x8fffffce70000000

def z869 : W := mkw 0xb4f2000166c80004 0x8da790000b364000 0xf8ff8001fffe001f 0xafc7fc000ffff000

def z870 : W := mkw 0xfedfffbc4500840a 0xcff6fffde2280420 0xfffffffe0700001e 0xcffffffff0380000

def z871 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xffe3fffe0000000a 0x4fff1ffff0000000

def z872 : W := mkw 0x01200043dfbfffe2 0x300900021efdffff 0x00000001ffffffe1 0x300000000fffffff

def z873 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e63f0f8fc7ea 0xa1c71f31f87c7e3f

def z874 : W := mkw 0x3f4ba7d4cd26972a 0xd9fa5d3ea66934b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z875 : W := mkw 0x65005040dc013200 0x0b28028206e00990 0xff007fc1ff01ff1f 0x7ff803fe0ff80ff8

def z876 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f9fc088fe3fe7 0x1038fcfe0447f1ff

def z877 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x3f1f9ff18ffe3fff 0xf1f8fcff8c7ff1ff

def z878 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xffffffff0f00001f 0xeffffffff8780000

def z879 : W := mkw 0xbedfafbc00000008 0xcdf6fd7de0000000 0xffff87fe0000001e 0x8ffffc3ff0000000

def z880 : W := mkw 0xfedfffbc4608000c 0xcff6fffde2304000 0xfffffffe0700001e 0xcffffffff0380000

def z881 : W := mkw 0x6c00750000000000 0x0b6003a800000000 0xffe07ffe0000001e 0xcfff03fff0000000

def z882 : W := mkw 0xfedfffbc022c000c 0xcff6fffde0116000 0xfffffffe000e001e 0xcffffffff0007000

def z883 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc783ff071f8ec 0x7e07e3c1ff838fc7

def z884 : W := mkw 0x25048af0cc121b60 0x59282457866090db 0xff001ff1ff003fff 0x7ff800ff8ff801ff

def z885 : W := mkw 0x7c46ffbc00000008 0x4be237fde0000000 0xffe3fffe0000001e 0xcfff1ffff0000000

def z886 : W := mkw 0x01200043ffdbffe3 0x200900021ffedfff 0x00000001ffffffe1 0x300000000fffffff

def z887 : W := mkw 0xbedfafbc00000008 0xcdf6fd7de0000000 0x3fff9ffe00000016 0xc1fffcfff0000000

def z888 : W := mkw 0xc0b459ab30d168c9 0x4605a2cd59868b46 0xc0fc79fff0f1f8fd 0xfe07e3cfff878fc7

def z889 : W := mkw 0x6c207503038ac5a0 0x2b6103a8181c562d 0xff007fc10f8fc7ff 0x7ff803fe087c7e3f

def z890 : W := mkw 0x01200043fffdfec7 0x000900021fffeff6 0x00000001ffffffe1 0x300000000fffffff

def z891 : W := mkw 0xfedfffbc5501a40a 0xcff6fffde2a80d20 0xfffffffff701f81f 0xffffffffffb80fc0

def z892 : W := mkw 0xfedfffbc02080008 0xcff6fffde0104000 0xfffffffe0f0e001e 0xcffffffff0787000

def z893 : W := mkw 0xb7fb0041eeec1204 0x8dbfd8020f776090 0xffff8001fffe3f1f 0xbffffc000ffff1f8

def z894 : W := mkw 0x1a4ba69400000000 0x40d25d34a0000000 0x3fe3e7fe0000001a 0xc1ff1f3ff0000000

def z895 : W := mkw 0x022d8ab3038ac5a0 0x60116c55981c562d 0x071f9ff10f8fc7f7 0xf038fcff887c7e3f

def z896 : W := mkw 0xfedfffbc00020128 0xcff6fffde0001009 0xfffffffe000007fe 0xdffffffff000003f

def z897 : W := mkw 0x829d8ab800000000 0x4414ec55c0000000 0x07ff9ffe00000016 0xc03ffcfff0000000

def z898 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff007fc1ff01ff0e 0x2ff803fe0ff80ff8

def z899 : W := mkw 0xee9d7da800000008 0xcf74ebed40000000 0xfffc7ffe0000001e 0xcfffe3fff0000000

def z900 : W := mkw 0xb7fb0003eeec4084 0x8dbfd8001f776204 0xffff8001ffffc0ff 0xbffffc000ffffe07

def z901 : W := mkw 0xb6fb000166ec0004 0x8db7d8000b376000 0xf8ff8001f7fe001d 0xafc7fc000fbff000

def z902 : W := mkw 0x4804ffbe1113ede9 0x624027fdf0889f6f 0x00007ffe0001ffe0 0x500003fff0000fff

def z903 : W := mkw 0xfedfffbc00360968 0xdff6fffde001b04b 0xfffffffe80fe38ff 0xdffffffff407f1c7

def z904 : W := mkw 0xfedfffbc2064000c 0xcff6fffde1032000 0xfffffffe0070001e 0xcffffffff0038000

def z905 : W := mkw 0x92ff8abb22fe49e5 0xd497fc55d917f24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z906 : W := mkw 0xfedfffbc10112849 0xcff6fffde0808942 0xfffffffe0000381e 0xcffffffff00001c0

def z907 : W := mkw 0xfedfffbc00340848 0xdff6fffde001a042 0xfffffffe0070001e 0xcffffffff0038000

def z908 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff9fc1fffe001f 0xeffffcfe0ffff000

def z909 : W := mkw 0xfedfffbc10112848 0xcff6fffde0808942 0xfffffffff0f1f8ff 0xffffffffff878fc7

def z910 : W := mkw 0x6d007540dd25b602 0x0b6803aa06e92db0 0xff007fc1ffffff1f 0x7ff803fe0ffffff8

def z911 : W := mkw 0xfedfffbc00240008 0xcff6fffde0012000 0xfffffffe00fe001e 0xcffffffff007f000

def z912 : W := mkw 0xb7fb0181eeec000c 0xcdbfd80c0f776000 0xffff81c1fffe001f 0xaffffc0e0ffff000

def z913 : W := mkw 0xfedfffbc6440000c 0xcff6fffde3220000 0xfffffffe7000001e 0xcffffffff3800000

def z914 : W := mkw 0xfedfffbc5501a40a 0xcff6fffde2a80d20 0xffffffff7f01c71f 0xfffffffffbf80e38

def z915 : W := mkw 0x01200043df89f682 0x200900021efc4fb4 0x00000001ff01ff01 0x300000000ff80ff8

def z916 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f9ff080fe3fe4 0xd038fcff8407f1ff

def z917 : W := mkw 0x030d8af0cc361b60 0x50186c578661b0db 0x071f9ff1fffe3ff7 0xf038fcff8ffff1ff

def z918 : W := mkw 0x80b4082320d048c0 0x0405a04119068246 0xc0fc783ff0f1f8fd 0xfe07e3c1ff878fc7

def z919 : W := mkw 0x3e4ba79400000008 0xc9f25d3ca0000000 0x3fe387fe00000002 0x81ff1c3ff0000000

def z920 : W := mkw 0xfcf2750f33c9e489 0xafe793a8799e4f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z921 : W := mkw 0x01200043a8f65be1 0x100900021d47b2df 0x0000000088fe3fe1 0x100000000447f1ff

def z922 : W := mkw 0x3f4ba7d4cf2e9722 0x79fa5d3ea67974b9 0x3f0387c00f0e0702 0x01f81c3e00787038

def z923 : W := mkw 0x490074409901b600 0x024803a204c80db0 0xff007fc1ff01ff1f 0x7ff803fe0ff80ff8

def z924 : W := mkw 0x1842a61400000000 0x00c21530a0000000 0x3fe3fffe0000001e 0xc1ff1ffff0000000

def z925 : W := mkw 0x10628213028a41a0 0x008314109814520d 0x38e3e63f0f8fc7fb 0xf1c71f31f87c7e3f

def z926 : W := mkw 0x3e6ba797038ac5a8 0xe9f35d3cb81c562d 0x3f0387c10f8fc7e3 0x31f81c3e087c7e3f

def z927 : W := mkw 0xb7db0000ee6c0004 0x8dbed80007736000 0xff1f8000fffe0017 0x8ff8fc0007fff000

def z928 : W := mkw 0xfedfffbc03088408 0xeff6fffde0184420 0xfffffffe0700001e 0xcffffffff0380000

def z929 : W := mkw 0xfedfffbc00360968 0xdff6fffde001b04b 0xfffffffe08fe07ff 0xdffffffff047f03f

def z930 : W := mkw 0x020d8ab000000000 0x40106c5580000000 0x07fffffe0000001e 0xc03ffffff0000000

def z931 : W := mkw 0x1842a616030ac5a0 0x20c21530b018562d 0x38e3e63e0f0fc7fa 0xd1c71f31f0787e3f

def z932 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffe8000381f 0xdffffffff40001c0

def z933 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff8001f7fe000c 0xaffffc000fbff000

def z934 : W := mkw 0xfedfffbc00100848 0xcff6fffde0008042 0xfffffffe8070381e 0xcffffffff40381c0

def z935 : W := mkw 0xc094582800000000 0x0604a2c140000000 0xc7fc7ffe0000001e 0xce3fe3fff0000000

def z936 : W := mkw 0xfedfffbc00120968 0xdff6fffde000904b 0xfffffffe000000fe 0xcffffffff0000007

def z937 : W := mkw 0xc194586888361b60 0x160ca2c34441b0db 0xc0fc783e88fe3ffd 0xde07e3c1f447f1ff

def z938 : W := mkw 0x92ff8abf22fe49e1 0x7497fc55f917f24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z939 : W := mkw 0xfedfffbc00020128 0xcff6fffde0001009 0xfffffffe008e00fe 0xcffffffff0047007

def z940 : W := mkw 0x4804fff61113ffe2 0x724027ffb0889fff 0x00007ffe0001ffe0 0x500003fff0000fff

def z941 : W := mkw 0xb7fb0041eeec1204 0x8dbfd8020f776090 0xffff99c1fffe381f 0xaffffcce0ffff1c0

def z942 : W := mkw 0xe79d59e8dc353a4a 0xdf3ceacf46e1a9d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z943 : W := mkw 0x27290001eeec0004 0x093948000f776000 0xff1f8001fffe001f 0xaff8fc000ffff000

def z944 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f9ff008fe3fe2 0xd038fcff8047f1ff

def z945 : W := mkw 0xfedfffbc10012008 0xcff6fffde0800900 0xfffffffef000381e 0xcffffffff78001c0

def z946 : W := mkw 0x6c20750330d168c1 0x0b6103a819868b46 0xff007fc1f0f1f8ff 0x7ff803fe0f878fc7

def z947 : W := mkw 0xfedfffbc030a8528 0xeff6fffde0185429 0xfffffffe0f8e07ff 0xdffffffff07c703f

def z948 : W := mkw 0xfedfffbc020a0128 0xeff6fffde0105009 0xfffffffe000e001e 0xcffffffff0007000

def z949 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x3fe3ffff0f8fc7ff 0xf1ff1ffff87c7e3f

def z950 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x071f9ff088fe3fe6 0x8038fcff8447f1ff

def z951 : W := mkw 0x020d8ab000120960 0x40106c558000904b 0x071f9ff088fe3ff7 0xd038fcff8447f1ff

def z952 : W := mkw 0x92df8abc00000008 0xc496fc55e0000000 0x07ff99fe00000004 0x803ffccff0000000

def z953 : W := mkw 0xfedfffbc00260128 0xdff6fffde0013009 0xfffffffe000e001e 0xcffffffff0007000

def z954 : W := mkw 0xe69d59a800000008 0xcf34eacd40000000 0xc7fc79ce0000000c 0x0e3fe3ce70000000

def z955 : W := mkw 0x80b0000330d168c1 0x0405800019868b46 0xc0fc603ff0f1f8fd 0xfe07e301ff878fc7

def z956 : W := mkw 0xfedfffbc00120968 0xcff6fffde000904b 0xfffffffe88fe3fff 0xdffffffff447f1ff

def z957 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0xc71f9ff1f8fe3fff 0xfe38fcff8fc7f1ff

def z958 : W := mkw 0x40245823109168c0 0x020122c118848b46 0xc0fc783ff0f1f8fd 0xfe07e3c1ff878fc7

def z959 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffc7ffe0000000c 0x4fffe3fff0000000

def z960 : W := mkw 0xb7fb000beeec4085 0x8dbfd8005f776204 0xffff800ffffe001f 0xaffffc007ffff000

def z961 : W := mkw 0xc0b4582b32d968c1 0x0605a2c15996cb46 0xc0fc783ffffff8fd 0xfe07e3c1ffffffc7

def z962 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff03ffc1ff8fff1f 0xfff81ffe0ffc7ff8

def z963 : W := mkw 0xfedfffbc10012008 0xcff6fffde0800900 0xffffffff7001c01e 0xeffffffffb800e00

def z964 : W := mkw 0x01200043bbffffe1 0x300900021ddfffff 0x00000001ffffffe1 0x300000000fffffff

def z965 : W := mkw 0xd2dfdabc00000008 0xc696fed5e0000000 0xc7fffffe0000001e 0xce3ffffff0000000

def z966 : W := mkw 0x4b0975409925b602 0x02584baa04c92db0 0x071fffc088ffff17 0xd038fffe0447fff8

def z967 : W := mkw 0xf6dfdbbc00000008 0xcfb6fedde0000000 0xc7fff9fe0000001c 0xce3fffcff0000000

def z968 : W := mkw 0x030d8af088361b60 0x50186c578441b0db 0x07fffffe88fe3fff 0xd03ffffff447f1ff

def z969 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff007fc1f701ff0c 0x7ff803fe0fb80ff8

def z970 : W := mkw 0x92fb000122ec0004 0x8497d80009176000 0xf8ff8001fffe001f 0xafc7fc000ffff000

def z971 : W := mkw 0xfcd2f71c00000008 0x8fe697b8e0000000 0xffe3fffe0000001e 0xcfff1ffff0000000

def z972 : W := mkw 0xfedfffbc30512849 0xcff6fffde1828942 0xfffffffef0f038ff 0xdffffffff78781c7

def z973 : W := mkw 0xfcf2750f77c9e483 0x2fe793a87bbe4f24 0xf8e0600f7701c008 0x2fc703007bb80e00

def z974 : W := mkw 0xb6df8abc00000008 0xcdb6fc55e0000000 0xffff9ffe0000001e 0xcffffcfff0000000

def z975 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3fe3f8f8fffff 0xf1c71ff1fc7c7fff

def z976 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc603ff0f1f8e9 0xbe07e301ff878fc7

def z977 : W := mkw 0x01200043ffeff7a6 0x200900021fff7fbd 0x00000001ffffffe1 0x300000000fffffff

def z978 : W := mkw 0x1862a617038ac5a0 0x20c31530b81c562d 0x38e3e63f0f0fc7ea 0x71c71f31f8787e3f

def z979 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff8001ff7e000e 0x2ffffc000ffbf000

def z980 : W := mkw 0x01200043effedfe4 0x300900021f7ff6ff 0x00000001ffffffe1 0x300000000fffffff

def z981 : W := mkw 0x92ff8abf22da49e9 0xe497fc55f916d24f 0x00ff803e00fe00e0 0x8007fc01f007f007

def z982 : W := mkw 0x1862a797038ac5a8 0x60c3153cb81c562d 0x38e3e7ff0f8fc7fb 0xf1c71f3ff87c7e3f

def z983 : W := mkw 0x374b0000ce2c0004 0x89ba580006716000 0xff1f8001fffe001f 0xaff8fc000ffff000

def z984 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff1c7fc1fff1ff1f 0xfff8e3fe0fff8ff8

def z985 : W := mkw 0x012000438b8ad7a0 0x200900021c5c56bd 0x000000018f8fffe1 0x300000000c7c7fff

def z986 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xf8ff8001fffe0009 0xafc7fc000ffff000

def z987 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0x3ffffffe00000002 0xc1fffffff0000000

def z988 : W := mkw 0xfedbf79c00000008 0xcff6dfbce0000000 0xffe3e7fe0000001a 0xcfff1f3ff0000000

def z989 : W := mkw 0xfedfffbc1101a408 0xcff6fffde0880d20 0xffffffffff01ff1f 0xfffffffffff80ff8

def z990 : W := mkw 0xe79d5968fc753a47 0x8f3ceacb47e3a9d2 0xc71c19c0f0703804 0x0e38e0ce078381c0

def z991 : W := mkw 0xfedfffbc00020128 0xcff6fffde0001009 0xfffffffe080e071e 0xcffffffff0407038

def z992 : W := mkw 0x4804fffa1113ffe3 0x524027ffd0889fff 0x00007ffe0001ffe0 0x500003fff0000fff

def z993 : W := mkw 0xfedbf79c00000008 0xcff6dfbce0000000 0xffe3ffce0000001e 0x4fff1ffe70000000

def z994 : W := mkw 0x4804ff7e1113ffe3 0x224027fbf0889fff 0x00007ffe0001ffe0 0x500003fff0000fff

def z995 : W := mkw 0xb7fb0003eeec4084 0x8dbfd8001f776204 0xffff803ffffe00ff 0xaffffc01fffff007

def z996 : W := mkw 0xee9dffbc00000008 0xcf74effde0000000 0xc7fc7ffe0000001c 0xce3fe3fff0000000

def z997 : W := mkw 0xfedfffbc030a8528 0xeff6fffde0185429 0xffffffff0f0fc71f 0xfffffffff8787e38

def z998 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xc0fc7e3ff8f1ffff 0xfe07e3f1ffc78fff

def z999 : W := mkw 0xfedf7dac00000008 0xcff6fbed60000000 0xfffc79fe0000001c 0xcfffe3cff0000000

def z1000 : W := mkw 0xbedba79c00000008 0xcdf6dd3ce0000000 0x3fe387ce00000002 0x01ff1c3e70000000

def z1001 : W := mkw 0xc0b4582b30d168c1 0x0605a2c159868b46 0xf8fc783ffff1f8ff 0xffc7e3c1ffff8fc7

def z1002 : W := mkw 0xf6dfdab800000000 0xcfb6fed5c0000000 0xfffffffe0000001e 0xcffffffff0000000

def z1003 : W := mkw 0xfedfffbc20500849 0xcff6fffde1028042 0xfffffffe0070001e 0xcffffffff0038000

def z1004 : W := mkw 0xb7fb0001eeec0004 0x8dbfd8000f776000 0xffff9801fffe381f 0xfffffcc00ffff1c0

def z1005 : W := mkw 0x6d007540dd01b602 0x0b6803aa06e80db0 0xff007fc17f01ff0a 0x7ff803fe0bf80ff8

def z1006 : W := mkw 0xca9dffbc00000008 0x4654effde0000000 0xc7fffffe0000001e 0xce3ffffff0000000

def z1007 : W := mkw 0xfedfffbc00000008 0xcff6fffde0000000 0xfffffffff000001f 0xefffffffff800000

def z1008 : W := mkw 0x030d086088341a40 0x001868430441a0d2 0x071f9ff088fe3ff7 0xd038fcff8447f1ff

def z1009 : W := mkw 0xa7990000ec640004 0x8d3cc80007632000 0xff1f8001fffe001f 0xaff8fc000ffff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z2,z8,z4,z5]),(0,[z0,z1,z2,z3,z9,z4,z5]),(0,[z0,z1,z10,z2,z4,z5,z11]),(0,[z12,z0,z1,z2,z3,z4,z5])],[(1,[z13,z1,z2,z3,z4,z14]),(0,[z0,z1,z15,z2,z3,z4,z14]),(0,[z0,z16,z1,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z3,z4,z5]),(0,[z18,z0,z1,z2,z3,z4,z5])],[(0,[z0,z19,z20,z2,z3,z4,z5]),(0,[z0,z1,z2,z21,z3,z4,z5]),(0,[z0,z1,z22,z2,z3,z4,z5])],[(0,[z23,z0,z24,z2,z3,z4,z5]),(0,[z0,z25,z1,z2,z3,z4,z5]),(0,[z26,z27,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z28]),(1,[z29,z0,z2,z3,z30,z5])],[(0,[z31,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z32,z5]),(0,[z0,z1,z33,z2,z3,z4,z5]),(0,[z0,z1,z34,z2,z3,z4,z5]),(0,[z0,z1,z35,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z36,z4,z5]),(0,[z0,z37,z1,z2,z3,z4,z5]),(0,[z0,z1,z38,z2,z3,z4,z5]),(0,[z0,z1,z2,z39,z3,z4,z5]),(0,[z0,z1,z2,z40,z3,z4,z5]),(0,[z0,z1,z2,z41,z3,z4,z5])],[],[(0,[z0,z1,z42,z2,z3,z4,z5])]],
   [[(0,[z0,z43,z1,z2,z3,z4,z5]),(0,[z0,z1,z44,z2,z3,z4,z5]),(0,[z0,z1,z2,z45,z3,z4,z5]),(1,[z0,z46,z2,z47,z4,z5]),(0,[z0,z1,z2,z3,z4,z48,z5])],[(1,[z23,z24,z2,z3,z4,z5]),(0,[z0,z1,z49,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z5]),(0,[z0,z51,z1,z2,z3,z4,z5])],[(0,[z0,z1,z52,z2,z3,z4,z5]),(0,[z0,z53,z19,z2,z3,z4,z5]),(0,[z0,z1,z2,z54,z55,z3,z4]),(0,[z0,z56,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z57,z5]),(1,[z0,z1,z2,z3,z58,z59])],[(0,[z60,z0,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z61,z4,z62,z5]),(0,[z63,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z64,z4,z5]),(0,[z0,z1,z2,z65,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z59,z66])],[(0,[z67,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z68,z2,z4,z5]),(0,[z0,z1,z2,z3,z69,z4,z5]),(0,[z0,z1,z70,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z71]),(0,[z0,z1,z2,z72,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z73,z5]),(0,[z0,z1,z2,z74,z3,z4,z5])],[(0,[z0,z75,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z76]),(0,[z0,z1,z77,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z78,z79]),(0,[z0,z1,z2,z3,z80,z4,z5]),(0,[z0,z1,z81,z2,z3,z4,z5]),(0,[z0,z1,z82,z2,z3,z4,z5])],[(0,[z83,z1,z2,z84,z3,z4,z5]),(0,[z0,z85,z1,z2,z3,z4,z5]),(0,[z13,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z86,z5]),(0,[z0,z1,z2,z3,z4,z5,z71])]],
   [[(0,[z0,z1,z2,z87,z3,z4,z5])],[(1,[z0,z1,z88,z2,z3,z4]),(0,[z0,z2,z3,z89,z4,z30,z5]),(0,[z0,z1,z90,z2,z3,z4,z5]),(0,[z0,z1,z91,z2,z3,z92,z4]),(0,[z0,z1,z2,z93,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z94,z5])],[(0,[z0,z1,z2,z3,z4,z5,z95]),(0,[z0,z96,z1,z2,z3,z4,z5]),(0,[z0,z19,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z97,z3,z4,z5]),(0,[z98,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z79,z66]),(0,[z0,z1,z99,z2,z3,z4,z5])],[(0,[z60,z0,z1,z2,z100,z4,z5]),(0,[z101,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z102,z4,z5]),(0,[z0,z1,z2,z103,z3,z4,z5])],[(0,[z26,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z62,z5]),(0,[z0,z1,z2,z3,z104,z4,z5]),(0,[z105,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z106]),(0,[z0,z1,z2,z3,z4,z107,z5]),(1,[z0,z1,z7,z108,z2,z5])],[(0,[z0,z1,z2,z3,z109,z4,z5]),(0,[z110,z13,z0,z1,z2,z3,z4]),(0,[z0,z111,z1,z2,z3,z4,z79]),(0,[z0,z1,z112,z2,z3,z4,z5])],[(0,[z113,z0,z1,z2,z3,z4,z5]),(1,[z114,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z115,z4,z5])],[(0,[z0,z116,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z117]),(0,[z0,z1,z2,z3,z118,z4,z5]),(0,[z0,z1,z2,z119,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z120,z0,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z121,z3,z4,z5])],[(0,[z0,z122,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z123,z5]),(0,[z0,z1,z2,z3,z4,z5,z124]),(0,[z125,z0,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z127,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z79])],[(0,[z128,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z129,z2,z3,z4,z5]),(0,[z0,z1,z2,z130,z3,z4,z5]),(0,[z0,z1,z2,z131,z3,z4,z5]),(0,[z0,z1,z2,z3,z92,z4,z5]),(0,[z0,z1,z132,z2,z3,z133,z5])],[(0,[z0,z1,z2,z134,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z135]),(0,[z0,z1,z2,z136,z3,z4,z5])],[(0,[z137,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z138,z62]),(0,[z0,z139,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z2,z3,z4,z106]),(0,[z0,z1,z2,z3,z140,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z141]),(0,[z142,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z143,z3,z4,z5])],[(0,[z144,z0,z1,z2,z3,z4,z5]),(0,[z0,z111,z1,z2,z3,z4,z59]),(0,[z0,z1,z2,z3,z145,z4,z5])]],
   [[(0,[z0,z146,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z147,z4,z30,z5]),(0,[z148,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z149,z5])],[(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z84,z3,z4,z5]),(0,[z0,z1,z2,z3,z151,z4,z5]),(1,[z0,z1,z2,z9,z4,z5]),(0,[z0,z56,z1,z2,z3,z4,z71]),(0,[z0,z1,z2,z152,z3,z4,z5])],[(0,[z0,z1,z2,z153,z3,z4,z5]),(0,[z0,z1,z2,z154,z3,z4,z5]),(0,[z155,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z156,z3,z4,z5]),(0,[z157,z0,z1,z2,z3,z4,z5]),(0,[z158,z0,z1,z2,z3,z4,z5])],[(0,[z159,z0,z1,z2,z3,z4,z160]),(0,[z0,z1,z15,z2,z3,z4,z78]),(0,[z0,z1,z2,z161,z3,z4,z5]),(0,[z162,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z163,z2,z3,z4,z5]),(0,[z0,z1,z164,z2,z3,z4,z5])],[(0,[z165,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z166,z2,z3,z4,z5]),(0,[z0,z167,z1,z2,z3,z4,z5]),(0,[z110,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z168]),(0,[z0,z1,z156,z3,z4,z133,z5])],[(0,[z0,z169,z1,z2,z8,z4,z5])],[(0,[z110,z0,z2,z3,z4,z170,z5])],[(0,[z0,z1,z2,z171,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z172]),(0,[z0,z46,z1,z2,z173,z4,z5]),(0,[z0,z1,z2,z174,z3,z4,z5]),(0,[z175,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z176,z5])],[(0,[z177,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z178]),(0,[z0,z179,z1,z2,z3,z4,z5]),(0,[z0,z1,z180,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z181,z4,z5]),(0,[z0,z1,z15,z2,z182,z3,z4]),(0,[z0,z1,z15,z2,z3,z5,z59])],[(0,[z0,z1,z183,z2,z3,z4,z5]),(0,[z0,z1,z184,z2,z3,z4,z5]),(0,[z0,z1,z185,z2,z3,z4,z5]),(0,[z0,z1,z2,z186,z3,z4,z5]),(0,[z187,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z135,z5]),(0,[z0,z1,z2,z3,z4,z5,z188])],[(0,[z0,z1,z2,z3,z189,z4,z5]),(0,[z27,z0,z1,z2,z3,z62,z5]),(0,[z0,z1,z190,z2,z3,z4,z5]),(0,[z0,z1,z191,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z58,z4,z59])],[(1,[z0,z1,z2,z3,z4,z160]),(0,[z0,z1,z192,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z193,z5]),(0,[z0,z1,z194,z2,z3,z4,z5]),(0,[z0,z1,z195,z2,z196,z4,z5]),(0,[z197,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z198,z3,z4,z5]),(0,[z199,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z200,z5]),(0,[z114,z0,z1,z2,z3,z4,z5]),(0,[z0,z201,z1,z2,z3,z4,z5]),(0,[z0,z202,z1,z2,z3,z4,z5])],[(0,[z159,z0,z1,z2,z3,z4,z5]),(1,[z27,z1,z2,z3,z61,z5]),(0,[z0,z203,z1,z2,z3,z4,z5]),(0,[z0,z1,z91,z2,z3,z133,z5]),(0,[z0,z1,z2,z3,z4,z5,z204])]],
   [[(0,[z0,z205,z1,z2,z3,z4,z5]),(0,[z0,z1,z206,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z207,z5])],[(0,[z208,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z108,z2,z173,z3,z5]),(0,[z0,z1,z209,z2,z93,z3,z4])],[(0,[z0,z1,z2,z3,z4,z210,z5]),(0,[z211,z0,z122,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z170,z14]),(0,[z0,z1,z212,z2,z3,z4,z5]),(0,[z0,z1,z2,z213,z3,z4,z5]),(0,[z0,z1,z2,z214,z3,z4,z5])],[(0,[z215,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z216,z3,z4,z5]),(0,[z0,z53,z1,z20,z3,z4,z5]),(0,[z0,z46,z1,z108,z2,z4,z5])],[(0,[z83,z0,z1,z2,z3,z4,z5]),(0,[z60,z0,z1,z2,z217,z4,z5]),(0,[z0,z1,z218,z2,z3,z4,z5]),(0,[z219,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z196,z3,z4,z5]),(0,[z0,z1,z2,z220,z3,z4,z5])],[(0,[z0,z1,z2,z221,z3,z4,z5]),(0,[z0,z1,z222,z2,z3,z4,z5]),(0,[z0,z1,z223,z2,z3,z4,z5])],[(0,[z0,z224,z1,z2,z3,z4,z5]),(0,[z159,z0,z1,z84,z3,z4,z5]),(0,[z1,z2,z100,z3,z217,z4,z5]),(0,[z0,z1,z225,z2,z3,z4,z5]),(0,[z0,z1,z226,z2,z3,z4,z5]),(0,[z0,z1,z2,z227,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z228,z5])],[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z229,z0,z111,z1,z2,z3,z4]),(0,[z0,z1,z2,z230,z3,z4,z5]),(0,[z0,z231,z1,z2,z3,z4,z5])]],
   [[(1,[z232,z0,z1,z2,z3,z4]),(0,[z233,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z234,z2,z3,z4,z5]),(0,[z235,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z236,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z237,z5]),(0,[z0,z1,z2,z3,z238,z4,z5]),(0,[z0,z1,z239,z2,z3,z4,z5]),(0,[z120,z0,z1,z2,z3,z4,z78]),(1,[z0,z1,z2,z54,z3,z4]),(0,[z240,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z93,z4,z241])],[(0,[z83,z0,z1,z84,z3,z4,z5]),(0,[z0,z1,z2,z3,z242,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z243]),(0,[z0,z1,z244,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z4,z5,z241])],[(0,[z0,z1,z2,z196,z100,z4,z5]),(0,[z0,z1,z2,z245,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z246,z5]),(0,[z0,z1,z2,z3,z4,z247,z5]),(0,[z0,z248,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z249])],[(0,[z0,z1,z2,z250,z3,z4,z5]),(0,[z0,z251,z1,z2,z3,z4,z5]),(1,[z0,z53,z55,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z252,z5])],[(0,[z0,z1,z88,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z253]),(0,[z254,z0,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z30,z5]),(0,[z0,z1,z2,z3,z4,z255,z5])]],
   [[(0,[z0,z1,z256,z2,z3,z4,z5]),(0,[z0,z1,z2,z257,z3,z4,z5]),(0,[z258,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z259,z5]),(0,[z0,z1,z2,z3,z4,z260,z5]),(0,[z261,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z262,z0,z1,z2,z3,z4,z5]),(0,[z13,z0,z111,z1,z2,z3,z4]),(0,[z120,z0,z1,z2,z182,z3,z4]),(0,[z0,z1,z2,z3,z4,z263,z5])],[(0,[z264,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z7,z108,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z5,z241]),(0,[z0,z1,z2,z265,z3,z4,z5])],[(1,[z26,z1,z2,z3,z62,z5]),(0,[z229,z0,z1,z2,z3,z4,z14]),(0,[z0,z111,z1,z266,z2,z3,z4]),(0,[z0,z1,z2,z3,z58,z4,z5])],[(0,[z0,z1,z2,z267,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z268,z5])],[(0,[z0,z1,z2,z269,z3,z4,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z270,z4,z5]),(0,[z0,z1,z2,z271,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z272]),(0,[z110,z0,z1,z2,z3,z4,z79])],[(0,[z0,z1,z2,z3,z4,z273,z5]),(0,[z0,z1,z2,z3,z4,z5,z274]),(0,[z0,z1,z275,z2,z3,z4,z5])]],
   [[(0,[z276,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z270,z3,z4,z5]),(0,[z277,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z278,z3,z4,z5]),(0,[z0,z1,z2,z279,z3,z4,z5]),(0,[z110,z229,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z280,z3,z4,z5]),(0,[z0,z1,z2,z173,z3,z4,z5]),(0,[z281,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z282,z3,z4,z5]),(0,[z283,z0,z1,z2,z3,z4,z5]),(0,[z284,z0,z1,z2,z3,z4,z5]),(1,[z110,z0,z2,z3,z4,z170]),(0,[z0,z1,z285,z2,z3,z4,z5])],[(0,[z286,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z287,z2,z3,z4,z5])],[(0,[z288,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z289,z5])],[(1,[z83,z1,z84,z3,z4,z5]),(0,[z13,z0,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z290,z3,z4,z5])],[(0,[z122,z1,z24,z2,z3,z4,z5])],[(0,[z23,z211,z1,z2,z3,z4,z5]),(0,[z0,z19,z1,z55,z3,z4,z5]),(0,[z0,z1,z2,z291,z3,z4,z5])]],
   [[(0,[z292,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z293,z3,z4,z5]),(0,[z110,z0,z1,z2,z3,z4,z59])],[(0,[z211,z122,z1,z2,z3,z4,z5]),(0,[z0,z1,z294,z2,z3,z4,z5]),(0,[z295,z0,z1,z2,z3,z4,z5]),(0,[z296,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z297,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z298]),(0,[z0,z1,z2,z299,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z300]),(0,[z0,z111,z1,z15,z2,z3,z4]),(0,[z0,z1,z2,z301,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z302]),(0,[z0,z1,z2,z100,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z170,z78])],[(0,[z0,z1,z2,z3,z4,z303,z5]),(0,[z0,z1,z195,z196,z3,z4,z5]),(0,[z0,z1,z304,z2,z3,z4,z5])],[(0,[z0,z305,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z61,z5]),(0,[z0,z1,z2,z306,z3,z4,z5]),(0,[z307,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z173,z3,z268,z5])],[(1,[z211,z122,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z78,z5,z14]),(0,[z0,z1,z2,z55,z3,z4,z5]),(1,[z17,z0,z1,z2,z3,z4])]],
   [[(0,[z159,z0,z1,z2,z3,z4,z308]),(0,[z0,z309,z1,z2,z3,z4,z5])],[(0,[z211,z0,z24,z2,z3,z4,z5]),(0,[z0,z1,z2,z310,z3,z4,z5]),(0,[z0,z311,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z312,z3,z4,z5]),(0,[z229,z0,z1,z182,z3,z4,z5]),(0,[z0,z1,z2,z313,z3,z4,z5])],[(0,[z0,z1,z2,z3,z314,z4,z5]),(0,[z0,z1,z2,z315,z3,z4,z5]),(0,[z0,z316,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z3,z4,z241])],[(0,[z0,z56,z1,z2,z3,z30,z5]),(0,[z0,z1,z2,z3,z317,z4,z5]),(0,[z318,z0,z1,z2,z3,z4,z5])],[(0,[z60,z0,z1,z10,z2,z4,z5]),(1,[z0,z1,z319,z2,z3,z4]),(0,[z320,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z321,z2,z3,z4,z5])],[(0,[z322,z0,z1,z195,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z323,z5]),(0,[z0,z1,z2,z3,z4,z138,z5]),(0,[z0,z111,z2,z3,z4,z5,z79])],[(0,[z0,z1,z324,z2,z3,z4,z5]),(0,[z325,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z326,z2,z4,z30,z5]),(0,[z0,z1,z2,z327,z3,z4,z5])]],
   [[],[(0,[z0,z1,z2,z3,z8,z4,z5]),(0,[z0,z1,z10,z2,z3,z4,z5]),(0,[z0,z1,z328,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z308]),(0,[z120,z0,z1,z2,z3,z58,z4]),(0,[z0,z1,z329,z2,z3,z4,z5])],[(0,[z330,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z331]),(0,[z0,z1,z2,z3,z4,z332,z5])],[(0,[z0,z1,z333,z2,z3,z4,z5]),(0,[z0,z1,z2,z334,z3,z4,z5]),(0,[z0,z1,z335,z2,z3,z4,z5]),(0,[z0,z169,z1,z2,z47,z4,z5]),(0,[z0,z2,z3,z4,z170,z5,z79]),(0,[z0,z1,z336,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z3,z4,z133]),(0,[z0,z1,z337,z2,z3,z4,z5])],[(0,[z229,z0,z1,z2,z3,z4,z78]),(0,[z0,z1,z338,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z58,z4,z79])],[(0,[z339,z0,z1,z2,z3,z4,z5]),(0,[z340,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z341]),(0,[z0,z1,z266,z2,z3,z4,z14]),(0,[z0,z1,z342,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z343,z3,z4,z5]),(0,[z0,z1,z2,z344,z3,z4,z5])],[(0,[z0,z345,z1,z2,z3,z4,z5])],[(0,[z346,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z347,z5])],[(0,[z0,z1,z2,z3,z4,z348,z5])],[(0,[z23,z1,z24,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z349,z4,z5])],[(0,[z0,z1,z88,z24,z2,z3,z4]),(0,[z350,z0,z1,z2,z3,z4,z5]),(0,[z351,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z352,z3,z4,z5]),(0,[z0,z1,z353,z2,z3,z4,z5])],[(0,[z354,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z355,z2,z3,z4,z5]),(0,[z356,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z357])],[(0,[z0,z1,z358,z2,z3,z4,z5]),(0,[z0,z1,z359,z2,z3,z4,z5]),(0,[z0,z1,z2,z182,z3,z4,z5]),(0,[z360,z0,z1,z2,z3,z58,z5])]],
   [[(1,[z0,z1,z2,z3,z4,z48]),(0,[z0,z361,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z362,z5]),(0,[z360,z0,z1,z2,z3,z4,z59])],[(0,[z0,z1,z2,z3,z4,z5,z363]),(0,[z0,z1,z2,z364,z3,z4,z5])],[(0,[z365,z0,z1,z2,z3,z4,z5]),(0,[z159,z1,z366,z2,z3,z4,z5]),(0,[z0,z1,z367,z2,z3,z4,z5]),(0,[z0,z1,z7,z108,z2,z4,z5]),(0,[z0,z1,z2,z368,z3,z4,z5]),(0,[z175,z0,z1,z2,z3,z4,z241])],[(0,[z0,z369,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z370]),(0,[z110,z0,z1,z266,z2,z3,z4]),(0,[z0,z1,z2,z371,z3,z4,z5]),(0,[z0,z1,z372,z2,z3,z4,z5]),(0,[z373,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z374,z5]),(0,[z375,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z376]),(0,[z0,z1,z2,z3,z4,z377,z5]),(0,[z0,z111,z1,z2,z3,z4,z170]),(0,[z378,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z379]),(0,[z0,z1,z380,z2,z3,z4,z5]),(0,[z229,z0,z1,z266,z3,z4,z5]),(0,[z0,z1,z2,z173,z4,z268,z5]),(0,[z0,z381,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z382]),(0,[z383,z0,z1,z2,z3,z4,z5]),(0,[z0,z384,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z385,z5]),(0,[z0,z1,z2,z3,z4,z386,z5])]],
   [[(0,[z360,z13,z0,z1,z2,z3,z4]),(0,[z0,z46,z1,z2,z3,z4,z5])],[(0,[z387,z0,z1,z2,z3,z4,z5]),(0,[z388,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z389,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z14]),(0,[z0,z1,z2,z3,z390,z4,z5]),(0,[z0,z1,z2,z3,z89,z4,z117]),(0,[z0,z1,z2,z3,z4,z391,z5])],[(0,[z0,z1,z2,z392,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z393,z5])],[(0,[z0,z1,z2,z394,z3,z4,z5]),(0,[z0,z1,z395,z2,z3,z4,z5]),(0,[z0,z396,z1,z2,z3,z4,z5]),(0,[z0,z1,z397,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z398]),(0,[z399,z0,z1,z2,z3,z4,z5]),(0,[z0,z400,z1,z2,z3,z4,z5])],[(0,[z0,z1,z401,z2,z3,z4,z5]),(0,[z0,z402,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z398,z5]),(0,[z0,z1,z15,z2,z3,z4,z66])],[(0,[z0,z1,z2,z8,z4,z268,z5]),(0,[z0,z1,z10,z195,z3,z4,z5])],[(0,[z211,z0,z1,z2,z3,z4,z5]),(0,[z0,z46,z169,z2,z3,z4,z5]),(0,[z0,z46,z1,z2,z8,z4,z5]),(0,[z0,z1,z403,z2,z3,z4,z5])],[(0,[z26,z0,z1,z2,z3,z4,z331]),(0,[z0,z1,z404,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z405,z5]),(0,[z0,z1,z2,z3,z406,z4,z5]),(0,[z0,z1,z15,z2,z3,z4,z5])],[(1,[z0,z1,z407,z2,z4,z5]),(0,[z0,z1,z68,z2,z3,z4,z5]),(0,[z0,z1,z2,z408,z3,z4,z5]),(0,[z0,z1,z409,z2,z3,z4,z5]),(0,[z410,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z411,z3,z4]),(0,[z412,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z58,z4,z170])],[(0,[z0,z1,z2,z3,z4,z413,z5]),(0,[z0,z1,z2,z3,z4,z414,z5]),(0,[z0,z1,z2,z3,z415,z4,z5]),(0,[z110,z0,z1,z15,z2,z3,z4]),(1,[z0,z1,z10,z4,z5,z11]),(0,[z0,z1,z2,z416,z3,z4,z5])],[(0,[z83,z0,z1,z2,z270,z4,z5]),(0,[z0,z1,z2,z3,z217,z4,z5]),(0,[z0,z56,z1,z2,z3,z4,z48]),(0,[z0,z1,z417,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z418]),(0,[z0,z53,z1,z2,z3,z4,z5]),(0,[z419,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z174,z4,z5])],[(0,[z420,z0,z1,z2,z3,z4,z5]),(0,[z83,z159,z1,z2,z3,z4,z5]),(0,[z0,z421,z1,z2,z3,z4,z5])],[(0,[z422,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z196,z3,z4,z5,z11]),(0,[z360,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z423,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z424,z4,z5]),(0,[z0,z1,z2,z3,z425,z4,z5]),(0,[z0,z1,z426,z2,z3,z4,z5]),(1,[z0,z169,z2,z8,z4,z5]),(0,[z0,z1,z2,z3,z4,z427,z5]),(1,[z360,z0,z1,z15,z2,z3])],[(0,[z0,z1,z366,z2,z3,z4,z5]),(0,[z428,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z4,z429,z5]),(0,[z0,z1,z430,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z30,z5])],[(0,[z0,z1,z24,z2,z3,z4,z5]),(1,[z0,z1,z195,z196,z4,z5]),(0,[z0,z431,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z432,z4,z5])],[(0,[z60,z322,z1,z2,z3,z4,z5]),(0,[z98,z0,z1,z2,z55,z3,z4]),(0,[z0,z46,z2,z47,z3,z4,z5]),(0,[z433,z0,z1,z2,z3,z4,z5])],[(0,[z0,z434,z1,z2,z3,z4,z5]),(0,[z435,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z436,z2,z3,z4,z5])],[(0,[z437,z0,z1,z2,z3,z4,z5])],[(0,[z0,z438,z1,z2,z3,z4,z5]),(0,[z0,z169,z2,z3,z8,z4,z5]),(0,[z0,z1,z439,z2,z3,z4,z5]),(0,[z0,z1,z15,z2,z3,z58,z4])],[(0,[z0,z1,z2,z217,z4,z5,z11]),(0,[z0,z1,z2,z440,z3,z4,z5]),(0,[z0,z1,z91,z3,z4,z133,z5]),(0,[z0,z1,z2,z3,z4,z441,z5])]],
   [[(0,[z0,z1,z2,z3,z442,z4,z5]),(0,[z0,z1,z2,z3,z443,z4,z5]),(0,[z444,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z445])],[(0,[z0,z1,z2,z3,z4,z59,z14]),(0,[z0,z1,z2,z182,z3,z4,z79]),(0,[z0,z1,z446,z2,z3,z4,z5]),(0,[z0,z1,z132,z2,z156,z3,z5])],[(0,[z0,z1,z2,z447,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z448,z5]),(0,[z0,z1,z2,z3,z449,z4,z5]),(0,[z29,z0,z1,z2,z9,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z450]),(0,[z120,z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z451,z5]),(0,[z0,z1,z452,z2,z3,z4,z5])],[(0,[z0,z453,z1,z2,z3,z4,z5]),(0,[z0,z454,z1,z2,z3,z4,z5]),(0,[z455,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z456,z5]),(0,[z360,z0,z1,z266,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z457,z5]),(0,[z0,z1,z2,z3,z4,z458,z5])],[(0,[z0,z1,z459,z2,z3,z4,z5]),(0,[z0,z1,z10,z2,z196,z4,z5])],[(0,[z460,z0,z1,z2,z3,z4,z5]),(0,[z120,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z79,z14]),(0,[z0,z461,z1,z2,z3,z4,z5]),(0,[z0,z169,z1,z108,z2,z4,z5]),(0,[z0,z1,z462,z2,z3,z4,z5]),(0,[z0,z1,z319,z2,z3,z4,z5]),(0,[z0,z1,z195,z2,z4,z5,z11]),(0,[z463,z0,z1,z2,z3,z4,z5]),(0,[z464,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z465,z3,z4,z5])]],
   [[(0,[z0,z466,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z467,z3,z4,z5]),(0,[z159,z0,z1,z366,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z468,z5])],[(0,[z0,z1,z2,z469,z3,z4,z5]),(0,[z0,z1,z2,z470,z3,z4,z5])],[(0,[z0,z1,z471,z2,z3,z4,z5]),(0,[z322,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z472,z5]),(0,[z0,z1,z2,z182,z3,z4,z59])],[(0,[z0,z1,z91,z2,z3,z4,z473]),(0,[z175,z0,z1,z2,z93,z4,z5])],[(0,[z0,z1,z2,z3,z61,z4,z5]),(0,[z0,z474,z1,z2,z3,z4,z5]),(0,[z475,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z476,z2,z3,z4,z5])],[(0,[z83,z0,z1,z366,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z477,z5]),(0,[z0,z478,z1,z2,z3,z4,z5])],[(0,[z479,z0,z1,z2,z3,z4,z5]),(0,[z26,z1,z2,z3,z4,z62,z5]),(0,[z480,z0,z1,z2,z3,z4,z5]),(0,[z481,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z196,z217,z4,z5]),(0,[z0,z1,z2,z482,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z483,z5])],[(0,[z0,z484,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z485,z3,z4,z5]),(0,[z0,z486,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z487,z4,z5])],[(0,[z0,z1,z2,z488,z3,z4,z5]),(0,[z322,z0,z1,z2,z100,z4,z5]),(0,[z110,z120,z0,z1,z2,z3,z4]),(0,[z360,z0,z1,z15,z2,z3,z4])],[(0,[z0,z489,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z331]),(0,[z490,z0,z1,z2,z3,z4,z5])],[(0,[z491,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z492]),(0,[z0,z1,z493,z2,z3,z4,z5]),(0,[z0,z1,z91,z2,z156,z3,z5]),(1,[z0,z1,z266,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z494,z5])],[(0,[z29,z0,z56,z2,z3,z4,z5]),(0,[z110,z0,z111,z2,z3,z4,z5]),(0,[z110,z0,z1,z2,z3,z4,z170])],[]],
   [[(0,[z0,z1,z2,z3,z495,z4,z5]),(0,[z0,z496,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z341])],[(0,[z0,z1,z2,z497,z3,z4,z5]),(0,[z360,z0,z1,z2,z3,z4,z79]),(0,[z0,z1,z498,z2,z3,z4,z5])],[(0,[z114,z0,z1,z2,z3,z4,z62]),(0,[z0,z1,z319,z2,z3,z89,z4]),(0,[z0,z1,z7,z2,z173,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z499])],[(0,[z0,z1,z2,z411,z3,z4,z5]),(0,[z500,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z501,z2,z3,z4,z5]),(0,[z0,z1,z2,z502,z3,z4,z5])],[(0,[z0,z503,z1,z2,z3,z4,z5]),(0,[z360,z229,z0,z1,z2,z3,z4]),(0,[z0,z1,z504,z2,z3,z4,z5]),(0,[z0,z1,z505,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z170,z66]),(0,[z0,z1,z506,z2,z3,z4,z5])],[(0,[z26,z0,z1,z2,z3,z62,z5]),(1,[z229,z0,z1,z182,z3,z4])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(1,[z0,z19,z20,z3,z4,z5]),(0,[z0,z1,z2,z147,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z507,z5]),(0,[z0,z1,z2,z508,z3,z4,z5]),(0,[z229,z0,z1,z2,z182,z3,z4])]],
   [[(1,[z0,z1,z2,z3,z4,z509]),(0,[z0,z1,z510,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z511,z4,z5])],[(0,[z0,z1,z407,z2,z3,z4,z5]),(1,[z120,z1,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z4,z512,z5]),(0,[z0,z1,z108,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z513,z5]),(1,[z159,z1,z366,z3,z4,z5]),(0,[z514,z0,z1,z2,z3,z4,z5]),(0,[z13,z0,z1,z2,z3,z4,z78]),(1,[z98,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z515,z3,z4,z5]),(0,[z0,z1,z182,z3,z4,z5,z66])],[(0,[z0,z516,z1,z2,z3,z4,z5]),(0,[z0,z517,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z518,z4,z5]),(0,[z0,z1,z2,z3,z4,z519,z5])],[(0,[z520,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z521,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z522]),(1,[z0,z1,z2,z3,z92,z4])],[(0,[z0,z1,z2,z523,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z138]),(0,[z0,z1,z2,z3,z4,z524,z5]),(0,[z525,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z526,z4,z5]),(0,[z0,z1,z68,z2,z84,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z11]),(0,[z0,z1,z7,z2,z3,z4,z5]),(0,[z0,z527,z1,z2,z3,z4,z5]),(0,[z0,z528,z1,z2,z3,z4,z5])]],
   [[],[(0,[z0,z1,z2,z3,z4,z5,z529]),(0,[z0,z1,z2,z3,z4,z530,z5]),(0,[z0,z1,z2,z3,z4,z531,z5]),(0,[z13,z0,z1,z2,z182,z3,z4])],[(0,[z0,z1,z532,z2,z3,z4,z5])],[(0,[z0,z533,z1,z2,z3,z4,z5]),(0,[z0,z1,z534,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z535,z4,z5]),(0,[z536,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z537,z2,z3,z4,z5]),(0,[z0,z1,z132,z91,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z473]),(0,[z0,z538,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z539])],[(0,[z540,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z541,z2,z3,z4,z5]),(0,[z0,z46,z1,z2,z47,z4,z5])],[(0,[z229,z0,z1,z2,z3,z4,z66])],[(0,[z542,z0,z1,z2,z3,z4,z5]),(0,[z543,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z544,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z545,z4,z5]),(0,[z0,z1,z2,z3,z546,z4,z5])]],
   [[(0,[z0,z1,z547,z2,z3,z4,z5]),(0,[z0,z19,z1,z20,z3,z4,z5]),(0,[z0,z548,z1,z2,z3,z4,z5]),(0,[z0,z1,z266,z3,z4,z5,z66]),(0,[z0,z1,z2,z549,z3,z4,z5]),(0,[z360,z0,z1,z15,z2,z3,z5])],[(0,[z0,z1,z2,z3,z4,z550,z5]),(0,[z0,z1,z2,z3,z4,z551,z5]),(0,[z0,z1,z552,z2,z3,z4,z5])],[(0,[z0,z1,z2,z553,z3,z4,z5]),(0,[z0,z53,z1,z55,z3,z4,z5]),(0,[z0,z20,z2,z55,z3,z4,z5]),(0,[z0,z1,z554,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z555,z5]),(0,[z0,z1,z2,z47,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z556,z5]),(0,[z0,z1,z557,z2,z3,z4,z5]),(0,[z229,z0,z1,z2,z3,z4,z5])],[(0,[z360,z120,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z558,z5])],[(0,[z559,z0,z1,z2,z3,z4,z5]),(0,[z1,z366,z2,z84,z3,z4,z5]),(0,[z322,z0,z1,z2,z217,z4,z5]),(0,[z560,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z132,z2,z3,z4,z5]),(0,[z0,z1,z7,z2,z3,z268,z5]),(0,[z561,z0,z1,z2,z3,z4,z5])],[(0,[z562,z0,z1,z2,z3,z4,z5]),(0,[z563,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z564])],[(0,[z232,z0,z1,z2,z3,z4,z5]),(0,[z0,z565,z1,z2,z3,z4,z5]),(0,[z360,z0,z1,z2,z3,z4,z170])],[(0,[z0,z1,z566,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z567,z4,z5]),(0,[z29,z0,z2,z3,z4,z30,z5]),(0,[z568,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z209,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z569,z5]),(0,[z0,z570,z1,z2,z3,z4,z5]),(0,[z0,z1,z571,z2,z3,z4,z5]),(0,[z13,z0,z1,z2,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z509,z5]),(0,[z0,z1,z2,z3,z4,z5,z572]),(0,[z0,z1,z2,z3,z4,z573,z5])],[(0,[z120,z0,z111,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z574,z4,z5])],[(0,[z575,z0,z1,z2,z3,z4,z5]),(0,[z576,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z577,z5]),(0,[z0,z1,z2,z3,z578,z4,z5])],[(0,[z0,z1,z2,z3,z4,z308,z5]),(0,[z0,z1,z579,z2,z3,z4,z5]),(0,[z0,z580,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z581,z5]),(1,[z0,z1,z91,z3,z133,z5]),(0,[z0,z1,z582,z2,z3,z4,z5])],[(0,[z583,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z584,z2,z3,z4,z5]),(0,[z0,z1,z132,z156,z3,z4,z5])],[(0,[z0,z1,z585,z2,z3,z4,z5])],[(0,[z0,z1,z586,z2,z3,z4,z5]),(0,[z60,z0,z1,z195,z2,z4,z5]),(0,[z0,z1,z587,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z588]),(0,[z0,z589,z1,z2,z3,z4,z5])],[(0,[z0,z1,z590,z2,z3,z4,z5]),(0,[z0,z169,z1,z2,z173,z4,z5]),(0,[z0,z591,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z592,z5]),(0,[z0,z1,z593,z2,z3,z4,z5]),(0,[z0,z1,z594,z2,z3,z4,z5])]],
   [[(0,[z229,z0,z1,z2,z3,z58,z4])],[(0,[z0,z1,z2,z595,z3,z4,z5]),(0,[z0,z1,z596,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z597,z5]),(0,[z0,z1,z2,z3,z4,z598,z5]),(0,[z0,z599,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z133,z5])],[(0,[z23,z0,z1,z2,z3,z4,z513]),(0,[z0,z1,z366,z2,z411,z3,z4])],[(0,[z83,z0,z1,z2,z526,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z106]),(0,[z0,z1,z600,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z182,z3,z4])],[(0,[z0,z1,z601,z2,z3,z4,z5]),(0,[z602,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z54,z3,z4,z5]),(0,[z0,z603,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z604,z5]),(0,[z60,z1,z2,z100,z3,z4,z5]),(0,[z0,z1,z2,z605,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z78,z59]),(1,[z0,z1,z132,z156,z3,z5])],[(0,[z0,z1,z2,z606,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z117]),(0,[z0,z1,z2,z3,z4,z5,z607]),(0,[z175,z0,z1,z209,z2,z3,z4])],[(0,[z608,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z609,z5]),(0,[z610,z0,z1,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z526,z4,z5]),(0,[z26,z0,z1,z2,z3,z61,z5]),(0,[z0,z1,z91,z2,z3,z4,z5])],[(0,[z322,z1,z2,z3,z217,z4,z5]),(0,[z0,z611,z1,z2,z3,z4,z5])],[(0,[z13,z0,z1,z2,z3,z58,z4]),(0,[z0,z1,z2,z3,z612,z4,z5]),(0,[z29,z0,z1,z2,z3,z89,z5]),(0,[z0,z1,z613,z2,z3,z4,z5]),(0,[z0,z1,z614,z2,z3,z4,z5]),(0,[z0,z1,z615,z2,z3,z4,z5]),(0,[z0,z1,z2,z616,z3,z4,z5])],[(0,[z0,z617,z1,z2,z3,z4,z5]),(0,[z618,z0,z1,z2,z3,z4,z5])],[(0,[z23,z0,z122,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z619,z4,z5]),(0,[z0,z1,z2,z620,z3,z4,z5]),(0,[z0,z169,z1,z2,z3,z4,z5]),(0,[z621,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z622,z2,z3,z4,z5]),(0,[z623,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z624,z4,z5]),(0,[z0,z1,z625,z2,z3,z4,z5]),(0,[z0,z1,z626,z2,z3,z4,z5]),(1,[z60,z1,z2,z100,z4,z5]),(1,[z0,z111,z2,z3,z4,z79]),(0,[z0,z1,z108,z2,z4,z268,z5])],[(0,[z0,z1,z627,z2,z3,z4,z5]),(0,[z120,z13,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z628,z5])],[(0,[z0,z1,z2,z629,z3,z4,z5]),(1,[z0,z56,z2,z3,z89,z5]),(0,[z0,z1,z2,z3,z4,z398,z133])]],
   [[(0,[z0,z1,z2,z3,z630,z4,z5]),(0,[z175,z0,z1,z209,z2,z4,z5]),(0,[z0,z1,z631,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z632,z5]),(0,[z633,z0,z1,z2,z3,z4,z5]),(0,[z634,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z59])],[(1,[z322,z1,z2,z217,z4,z5]),(0,[z0,z1,z20,z2,z3,z4,z5]),(0,[z0,z635,z1,z2,z3,z4,z5]),(0,[z0,z1,z636,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z66]),(0,[z0,z1,z2,z3,z637,z4,z5])],[(1,[z0,z1,z2,z3,z4,z513])],[(0,[z0,z1,z2,z3,z638,z4,z5]),(0,[z0,z1,z2,z3,z4,z639,z5]),(0,[z0,z1,z640,z2,z3,z4,z5])],[(0,[z23,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z641,z4,z5]),(0,[z0,z2,z47,z3,z8,z4,z5])],[(0,[z0,z1,z2,z642,z3,z4,z5]),(0,[z0,z1,z643,z2,z3,z4,z5]),(0,[z0,z1,z2,z644,z3,z4,z5]),(0,[z0,z1,z645,z2,z3,z4,z5]),(0,[z0,z1,z266,z2,z3,z4,z5])],[(0,[z0,z1,z407,z2,z84,z4,z5]),(0,[z0,z1,z2,z646,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z647]),(0,[z648,z0,z1,z2,z3,z4,z5]),(0,[z649,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z650,z5]),(0,[z0,z651,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z652,z3,z4,z5]),(0,[z653,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z654,z3,z4,z5])],[(0,[z27,z1,z2,z3,z61,z4,z5]),(0,[z655,z0,z1,z2,z3,z4,z5]),(0,[z0,z656,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z657,z5])],[(0,[z0,z53,z2,z55,z3,z4,z5]),(1,[z0,z1,z326,z2,z4,z5])],[(0,[z0,z1,z658,z2,z3,z4,z5]),(0,[z659,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z160]),(0,[z0,z1,z2,z3,z4,z78,z5]),(0,[z0,z660,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z661,z5])],[(0,[z23,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z662,z5]),(0,[z322,z0,z1,z10,z2,z4,z5]),(0,[z0,z663,z1,z2,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z664]),(0,[z0,z1,z2,z3,z58,z5,z59])],[(0,[z0,z1,z2,z47,z4,z268,z5]),(0,[z0,z1,z326,z2,z3,z4,z5])],[(0,[z665,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z666,z4,z5]),(0,[z0,z1,z667,z2,z3,z4,z5]),(0,[z0,z1,z2,z668,z3,z4,z5])]],
   [[(0,[z669,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z147,z4,z5]),(0,[z0,z1,z2,z3,z670,z4,z5]),(0,[z0,z1,z2,z671,z3,z4,z5])],[(0,[z672,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z673,z5]),(0,[z674,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z182,z3,z4,z170]),(0,[z0,z1,z2,z3,z675,z4,z5]),(0,[z0,z1,z209,z2,z4,z5,z241])],[(0,[z0,z1,z2,z100,z4,z5,z11])],[(0,[z0,z111,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z676,z3,z4,z5])],[(0,[z232,z0,z1,z24,z2,z3,z4]),(0,[z0,z1,z677,z2,z3,z4,z5]),(0,[z0,z1,z678,z2,z3,z4,z5]),(0,[z0,z1,z679,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z680,z5]),(0,[z0,z1,z2,z3,z4,z170,z5]),(0,[z0,z1,z266,z2,z3,z58,z4]),(0,[z0,z1,z2,z3,z4,z5,z66]),(0,[z681,z0,z1,z2,z3,z4,z5])],[(0,[z682,z0,z1,z2,z3,z4,z5]),(1,[z175,z0,z1,z209,z2,z4])],[(0,[z0,z1,z2,z683,z3,z4,z5]),(0,[z29,z0,z1,z2,z174,z4,z5]),(0,[z0,z56,z2,z3,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z684,z5]),(1,[z0,z1,z2,z173,z268,z5])],[(0,[z26,z0,z1,z2,z3,z4,z135]),(0,[z0,z1,z2,z3,z4,z5,z685]),(0,[z0,z56,z1,z2,z3,z89,z5]),(0,[z0,z686,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z687,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z688,z5]),(0,[z0,z1,z366,z2,z3,z4,z341]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z2,z3,z4,z5,z689]),(0,[z0,z1,z690,z2,z3,z4,z5]),(0,[z0,z1,z195,z2,z3,z4,z5])],[(0,[z0,z691,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z692,z4,z5])],[(0,[z120,z1,z2,z3,z4,z78,z5]),(0,[z0,z1,z693,z2,z3,z4,z5])],[(0,[z0,z694,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z695,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z696,z5])],[(0,[z0,z53,z1,z2,z3,z4,z509]),(0,[z697,z0,z1,z2,z3,z4,z5]),(0,[z0,z698,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z699,z5]),(0,[z0,z1,z7,z2,z47,z4,z5]),(0,[z0,z1,z700,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z701,z5]),(1,[z0,z1,z2,z3,z4,z473])],[(0,[z0,z1,z10,z3,z4,z5,z11]),(0,[z702,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z703,z4,z5]),(0,[z13,z1,z2,z3,z4,z5,z14]),(0,[z0,z1,z2,z3,z4,z704,z5]),(0,[z705,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z706,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z4,z5]),(0,[z0,z1,z708,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z709]),(0,[z322,z1,z34,z2,z4,z5]),(0,[z0,z1,z401,z196,z4,z5]),(0,[z0,z2,z3,z4,z710,z5]),(0,[z0,z402,z1,z182,z3,z4]),(0,[z0,z1,z91,z3,z398,z133])],[(0,[z83,z1,z84,z270,z4,z5]),(0,[z0,z711,z2,z3,z4,z5])],[(0,[z0,z1,z712,z2,z4,z5]),(0,[z1,z2,z713,z3,z4,z5]),(0,[z0,z1,z714,z2,z3,z4]),(0,[z0,z1,z715,z3,z4,z5]),(0,[z0,z716,z2,z3,z4,z5])],[(0,[z0,z1,z2,z717,z3,z4]),(0,[z0,z1,z2,z3,z4,z718]),(0,[z0,z1,z2,z3,z4,z719]),(0,[z0,z1,z2,z720,z4,z5])]],
   [[(0,[z60,z1,z2,z100,z4,z5]),(0,[z0,z721,z2,z3,z4,z5]),(0,[z120,z1,z2,z3,z4,z684]),(0,[z0,z111,z2,z3,z4,z79]),(0,[z0,z1,z15,z2,z3,z518]),(0,[z0,z1,z108,z2,z722,z5])],[(0,[z159,z1,z366,z3,z4,z341]),(0,[z0,z1,z2,z9,z4,z5])],[(0,[z0,z1,z723,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z2,z3,z4,z725]),(0,[z0,z1,z726,z2,z3,z58])],[(0,[z83,z1,z407,z84,z4,z5]),(0,[z0,z727,z2,z3,z4,z5]),(0,[z0,z1,z2,z728,z4,z5]),(0,[z0,z729,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z730,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z731]),(0,[z0,z1,z2,z3,z4,z331]),(0,[z360,z0,z1,z2,z3,z448]),(0,[z0,z1,z2,z3,z4,z732]),(0,[z0,z1,z2,z3,z4,z733])],[(0,[z322,z1,z2,z217,z4,z5])],[(0,[z0,z1,z2,z3,z4,z513]),(0,[z159,z1,z366,z3,z4,z160]),(0,[z13,z1,z234,z2,z3,z4])],[(0,[z0,z1,z2,z734,z4,z5]),(0,[z0,z1,z2,z3,z4,z735]),(0,[z0,z1,z3,z4,z736,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z341]),(0,[z737,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z738]),(0,[z739,z1,z2,z3,z4,z5]),(0,[z740,z0,z1,z2,z3,z4]),(0,[z110,z0,z2,z3,z4,z73])],[(0,[z0,z1,z2,z3,z4,z741]),(0,[z742,z0,z1,z2,z3,z4])],[(0,[z0,z1,z743,z2,z3,z4]),(0,[z0,z1,z744,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z745]),(0,[z105,z0,z2,z3,z4,z170]),(0,[z0,z1,z746,z2,z3,z5]),(0,[z0,z747,z2,z3,z4,z5]),(0,[z0,z1,z266,z3,z4,z494])],[(0,[z0,z1,z2,z748,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z749,z5]),(0,[z750,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z751])],[(0,[z0,z1,z752,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z160]),(0,[z322,z1,z2,z713,z4,z5]),(0,[z0,z1,z2,z713,z4,z5]),(0,[z0,z1,z326,z2,z4,z5]),(0,[z0,z1,z91,z3,z92,z133])],[(0,[z0,z1,z2,z3,z4,z753]),(0,[z26,z1,z2,z3,z62,z331]),(0,[z29,z0,z2,z9,z30,z5]),(0,[z0,z1,z266,z152,z3,z4]),(0,[z229,z0,z1,z182,z3,z4]),(0,[z0,z1,z15,z222,z2,z3])],[(0,[z83,z1,z84,z526,z4,z5]),(0,[z621,z1,z2,z100,z4,z5]),(0,[z27,z1,z2,z3,z61,z5]),(0,[z0,z1,z2,z754,z3,z4]),(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z19,z756,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z2,z3,z4,z758])]],
   [[(0,[z0,z1,z2,z759,z4,z5])],[(0,[z60,z1,z99,z2,z4,z5]),(0,[z1,z2,z3,z61,z760,z5]),(0,[z120,z1,z2,z3,z4,z78]),(0,[z0,z111,z541,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z761]),(0,[z0,z1,z2,z3,z762,z4]),(0,[z0,z1,z2,z763,z4,z5]),(0,[z0,z56,z2,z3,z764,z5]),(0,[z0,z1,z765,z2,z3,z4])],[(0,[z211,z766,z2,z3,z4,z5]),(0,[z159,z1,z366,z3,z4,z5]),(0,[z120,z1,z2,z3,z4,z767]),(0,[z0,z1,z2,z768,z4,z5])],[(0,[z0,z769,z2,z3,z4,z5]),(0,[z373,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z3,z4,z48]),(0,[z29,z0,z2,z3,z764,z5])]],
   [[(0,[z0,z53,z54,z55,z3,z4])],[(0,[z18,z1,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z770,z5]),(0,[z0,z1,z2,z771,z4,z5]),(0,[z772,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z92,z4])],[(0,[z0,z1,z2,z773,z4,z5]),(0,[z0,z1,z2,z3,z4,z138]),(0,[z110,z0,z544,z2,z3,z4]),(0,[z774,z1,z2,z3,z4,z5])],[(0,[z83,z1,z744,z3,z4,z5]),(0,[z1,z2,z3,z4,z775,z5]),(0,[z0,z1,z2,z3,z4,z776])]],
   [[(0,[z0,z1,z2,z777,z4,z5]),(1,[z0,z2,z3,z4,z710]),(0,[z175,z0,z1,z209,z2,z4])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z778,z5]),(0,[z159,z1,z744,z3,z4,z5]),(0,[z779,z0,z1,z2,z3,z4]),(0,[z780,z0,z1,z2,z3,z4]),(0,[z0,z316,z2,z3,z4,z79]),(0,[z0,z1,z2,z3,z80,z59]),(0,[z0,z1,z2,z173,z268,z5])],[(0,[z0,z1,z2,z3,z4,z781]),(0,[z0,z1,z2,z54,z3,z4]),(0,[z0,z1,z2,z93,z4,z241])],[(0,[z0,z1,z2,z782,z4,z5]),(0,[z0,z1,z765,z2,z4,z5])]],
   [[(0,[z0,z783,z2,z3,z4,z5]),(0,[z0,z1,z182,z715,z3,z4])],[(0,[z0,z1,z2,z784,z3,z4]),(0,[z0,z1,z2,z3,z785,z5]),(0,[z649,z1,z2,z3,z4,z14]),(0,[z120,z651,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z786]),(0,[z0,z56,z2,z3,z89,z117])],[(0,[z0,z1,z2,z787,z4,z5]),(0,[z0,z2,z3,z4,z710,z79]),(0,[z0,z1,z2,z722,z4,z5])],[(0,[z0,z1,z2,z3,z4,z788]),(0,[z789,z1,z2,z3,z4,z5]),(0,[z0,z169,z2,z654,z4,z5]),(0,[z360,z0,z1,z726,z2,z3])]],
   [[(0,[z1,z2,z3,z4,z78,z767]),(0,[z0,z1,z2,z3,z4,z473])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z790,z5]),(1,[z1,z2,z3,z760,z5]),(0,[z13,z1,z2,z3,z4,z176]),(0,[z0,z1,z2,z3,z4,z791])],[(0,[z0,z1,z792,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z793])],[(0,[z26,z1,z2,z3,z62,z5]),(0,[z0,z1,z196,z4,z736,z5]),(0,[z0,z1,z91,z794,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z407,z2,z4,z5]),(0,[z13,z1,z2,z3,z4,z14]),(1,[z1,z2,z3,z4,z767]),(0,[z229,z0,z1,z482,z3,z4]),(0,[z0,z1,z2,z3,z796,z4])],[(0,[z0,z1,z2,z3,z4,z797]),(0,[z0,z1,z2,z798,z4,z5]),(0,[z0,z309,z2,z8,z4,z5])],[(0,[z0,z1,z799,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z800]),(0,[z0,z1,z2,z3,z4,z801]),(0,[z29,z0,z2,z3,z30,z5]),(0,[z0,z1,z10,z4,z5,z11])],[(0,[z0,z1,z2,z3,z4,z802]),(0,[z1,z2,z713,z217,z4,z5]),(0,[z0,z1,z2,z803,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z804]),(0,[z0,z1,z2,z3,z4,z805]),(0,[z0,z1,z765,z2,z93,z4]),(0,[z0,z1,z765,z2,z4,z241])],[(0,[z806,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z807]),(0,[z0,z1,z195,z186,z4,z5]),(0,[z60,z1,z2,z713,z4,z5]),(0,[z27,z1,z2,z3,z760,z5]),(0,[z0,z1,z2,z808,z4,z5]),(0,[z0,z1,z794,z3,z4,z5]),(0,[z0,z1,z15,z726,z2,z3])],[(0,[z809,z0,z1,z2,z3,z4]),(0,[z0,z1,z355,z4,z5,z11]),(0,[z0,z1,z810,z3,z4,z5]),(0,[z0,z1,z2,z3,z58,z531]),(0,[z811,z0,z1,z2,z3,z4]),(0,[z0,z1,z812,z2,z4,z5]),(0,[z0,z46,z337,z2,z4,z5]),(0,[z110,z0,z2,z3,z4,z170])],[(0,[z0,z1,z2,z3,z4,z813]),(0,[z0,z1,z814,z3,z4,z5]),(0,[z0,z1,z2,z815,z4,z5]),(0,[z0,z1,z816,z2,z3,z4]),(0,[z0,z1,z2,z817,z4,z5]),(0,[z1,z2,z3,z4,z760,z5]),(0,[z0,z169,z2,z8,z4,z5]),(0,[z0,z1,z2,z722,z268,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z818]),(0,[z26,z1,z2,z3,z138,z62]),(0,[z0,z1,z2,z3,z4,z819])],[(0,[z0,z2,z3,z4,z820,z5]),(0,[z0,z1,z821,z3,z4,z5]),(0,[z0,z1,z2,z822,z4,z5]),(0,[z0,z1,z2,z3,z58,z59])],[(0,[z0,z1,z2,z3,z823,z4]),(0,[z0,z1,z2,z3,z4,z824]),(0,[z0,z2,z3,z4,z825,z5]),(0,[z0,z1,z266,z3,z4,z512]),(0,[z826,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z827])]],
   [[(0,[z0,z1,z2,z828,z4,z5]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z830,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z71]),(0,[z0,z1,z2,z831,z4,z5])],[(0,[z0,z1,z832,z3,z4,z5]),(0,[z98,z0,z53,z55,z3,z4]),(0,[z0,z46,z2,z803,z4,z5]),(0,[z0,z1,z2,z833,z3,z4])],[(0,[z0,z1,z2,z834,z4,z5]),(0,[z13,z1,z2,z227,z3,z4]),(0,[z0,z2,z756,z3,z4,z5]),(0,[z0,z1,z91,z3,z133,z473])],[(0,[z0,z1,z10,z87,z4,z5]),(0,[z0,z1,z835,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z836])],[(0,[z0,z1,z2,z3,z4,z837]),(0,[z0,z486,z2,z47,z4,z5]),(0,[z0,z1,z838,z3,z4,z5]),(0,[z0,z839,z2,z3,z4,z5]),(0,[z0,z1,z132,z156,z3,z5]),(0,[z17,z0,z1,z91,z3,z133]),(0,[z840,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z841]),(0,[z0,z1,z842,z3,z4,z5]),(0,[z0,z1,z843,z3,z4,z5]),(0,[z0,z1,z2,z3,z844,z5]),(0,[z0,z1,z2,z3,z845,z5])],[(0,[z211,z122,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z846]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z1,z2,z848,z3,z4]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z20,z756,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z850]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z0,z1,z132,z794,z3,z5]),(0,[z0,z1,z266,z715,z3,z4]),(0,[z0,z1,z7,z108,z2,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z2,z526,z4,z5]),(0,[z0,z1,z2,z3,z4,z853]),(0,[z0,z1,z2,z854,z3,z4]),(0,[z0,z1,z2,z855,z3,z4])],[(0,[z0,z1,z2,z856,z4,z5]),(0,[z0,z1,z2,z3,z4,z857]),(0,[z114,z0,z1,z2,z3,z4]),(0,[z0,z56,z2,z3,z89,z48])],[(0,[z0,z1,z2,z858,z4,z5]),(0,[z0,z859,z2,z3,z4,z5]),(0,[z860,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z760,z5]),(0,[z0,z2,z47,z803,z4,z5]),(1,[z0,z1,z4,z736,z5])],[(0,[z0,z1,z2,z861,z3,z4]),(0,[z159,z1,z366,z3,z4,z308]),(0,[z862,z0,z1,z2,z3,z4])]],
   [[(0,[z1,z744,z84,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z863]),(0,[z0,z1,z864,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z865]),(0,[z0,z53,z55,z3,z4,z106]),(0,[z0,z1,z2,z866,z4,z5])],[(0,[z0,z1,z2,z3,z4,z867]),(0,[z0,z1,z2,z3,z4,z767]),(0,[z0,z1,z319,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z710]),(0,[z0,z111,z2,z508,z3,z4])],[(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z1,z2,z869,z4,z5]),(0,[z122,z766,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z870]),(0,[z0,z1,z2,z3,z4,z871]),(0,[z0,z1,z2,z279,z268,z5])],[(0,[z872,z0,z1,z2,z3,z4]),(0,[z0,z873,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z135]),(0,[z0,z56,z2,z3,z89,z5]),(0,[z0,z2,z3,z764,z30,z5]),(0,[z0,z111,z2,z3,z4,z710]),(0,[z0,z2,z3,z4,z170,z710])]],
   [[(0,[z0,z1,z874,z2,z3,z5]),(0,[z0,z1,z875,z3,z4,z5]),(0,[z876,z1,z2,z3,z4,z5])],[(0,[z877,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z878]),(0,[z0,z756,z55,z3,z4,z5]),(0,[z0,z589,z2,z3,z4,z170]),(0,[z0,z1,z2,z3,z879,z4])],[(0,[z0,z1,z2,z3,z4,z308]),(0,[z0,z1,z2,z3,z4,z880]),(0,[z0,z1,z881,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z882])],[(0,[z0,z1,z2,z3,z883,z5]),(0,[z0,z1,z884,z2,z4,z5]),(0,[z0,z1,z2,z885,z3,z4]),(0,[z886,z0,z1,z2,z3,z4]),(0,[z110,z0,z285,z2,z3,z4]),(0,[z0,z1,z794,z3,z133,z5]),(0,[z0,z1,z640,z182,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z887,z4]),(0,[z0,z1,z2,z3,z888,z5]),(0,[z0,z2,z3,z89,z764,z5]),(0,[z0,z1,z889,z2,z3,z4]),(0,[z890,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z891]),(0,[z0,z1,z2,z3,z4,z892]),(1,[z0,z2,z803,z4,z5]),(0,[z0,z1,z7,z2,z722,z5]),(0,[z0,z1,z726,z2,z3,z5])],[(0,[z0,z1,z2,z893,z4,z5]),(0,[z0,z1,z894,z2,z3,z4]),(0,[z1,z2,z3,z4,z767,z5]),(0,[z895,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z145,z59]),(0,[z0,z1,z2,z4,z736,z5])],[(0,[z0,z1,z2,z3,z4,z896]),(0,[z13,z1,z2,z3,z4,z767]),(0,[z1,z2,z3,z4,z767,z14]),(0,[z0,z1,z756,z3,z4,z5]),(0,[z0,z1,z2,z897,z3,z4]),(0,[z0,z1,z2,z715,z3,z4])]],
   [[(0,[z0,z1,z898,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z899]),(0,[z0,z1,z2,z900,z4,z5]),(0,[z0,z611,z2,z3,z4,z170]),(0,[z0,z1,z266,z3,z4,z66])],[(0,[z0,z1,z2,z901,z4,z5]),(0,[z26,z1,z2,z3,z62,z135]),(0,[z0,z1,z902,z2,z4,z5])],[(0,[z0,z1,z590,z182,z3,z4]),(0,[z0,z1,z2,z3,z4,z903])],[(0,[z0,z1,z2,z3,z4,z904])]],
   [[(0,[z23,z88,z24,z2,z3,z4]),(0,[z83,z1,z68,z84,z4,z5]),(0,[z0,z1,z905,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z906]),(0,[z110,z0,z2,z3,z4,z710])],[(0,[z0,z1,z2,z3,z4,z907]),(0,[z1,z366,z744,z3,z4,z5])],[(0,[z0,z1,z2,z908,z4,z5]),(0,[z0,z1,z2,z3,z4,z909]),(0,[z0,z1,z910,z3,z4,z5]),(0,[z500,z0,z1,z15,z2,z3]),(0,[z0,z202,z2,z3,z4,z79])],[(0,[z0,z1,z2,z3,z4,z911]),(0,[z481,z1,z2,z3,z4,z14]),(0,[z0,z1,z2,z912,z4,z5]),(0,[z229,z0,z1,z715,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z913]),(0,[z0,z1,z2,z3,z4,z914]),(0,[z915,z0,z1,z2,z3,z4]),(0,[z916,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z147,z4,z5]),(0,[z917,z1,z2,z3,z4,z5]),(0,[z0,z1,z82,z3,z4,z66])],[(0,[z0,z1,z2,z918,z3,z5]),(0,[z0,z1,z919,z2,z3,z4]),(0,[z1,z2,z3,z4,z920,z5])],[(1,[z766,z2,z3,z4,z5]),(0,[z766,z24,z2,z3,z4,z5]),(0,[z0,z19,z20,z3,z4,z5]),(0,[z0,z53,z756,z3,z4,z5]),(0,[z921,z0,z1,z2,z3,z4])],[(0,[z0,z1,z922,z2,z3,z5]),(0,[z0,z1,z923,z3,z4,z5]),(0,[z0,z924,z1,z2,z3,z4]),(0,[z0,z925,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z509]),(0,[z0,z1,z926,z2,z3,z4])]],
   [[(0,[z1,z766,z2,z3,z4,z5]),(0,[z0,z1,z2,z927,z4,z5]),(0,[z1,z2,z3,z760,z62,z5]),(0,[z0,z1,z2,z173,z556,z5])],[(0,[z0,z1,z2,z3,z4,z928]),(0,[z98,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z930,z0,z1,z2,z3,z4]),(0,[z0,z931,z2,z3,z4,z5]),(0,[z0,z1,z209,z765,z2,z4])],[(0,[z23,z24,z2,z3,z4,z513]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z0,z56,z2,z3,z89,z71])],[(0,[z0,z1,z2,z933,z4,z5]),(0,[z0,z1,z2,z3,z4,z934]),(0,[z0,z1,z2,z3,z935,z4]),(0,[z0,z1,z2,z3,z4,z936]),(0,[z1,z2,z100,z713,z4,z5]),(0,[z0,z1,z2,z3,z4,z937]),(0,[z29,z0,z326,z2,z30,z5])]],
   [[(0,[z0,z1,z938,z3,z4,z5]),(0,[z0,z53,z55,z3,z4,z509]),(0,[z0,z1,z2,z3,z764,z5])],[(0,[z0,z1,z2,z3,z4,z939]),(0,[z0,z1,z2,z3,z535,z59])],[(0,[z23,z232,z24,z2,z3,z4]),(0,[z0,z1,z940,z2,z4,z5]),(0,[z0,z1,z2,z941,z4,z5]),(0,[z0,z2,z3,z4,z942,z5]),(0,[z0,z1,z943,z2,z4,z5]),(0,[z944,z1,z2,z3,z4,z5])],[(0,[z232,z0,z1,z2,z3,z4]),(0,[z159,z1,z366,z411,z3,z4]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z2,z3,z4,z398]),(1,[z0,z1,z726,z2,z3])]],
   [[(1,[z0,z1,z794,z3,z5]),(0,[z0,z1,z946,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z947]),(0,[z0,z1,z2,z3,z4,z948]),(0,[z29,z0,z2,z147,z30,z5]),(0,[z0,z111,z112,z2,z3,z4])],[(0,[z0,z949,z2,z3,z4,z5]),(0,[z1,z2,z744,z3,z4,z5]),(0,[z950,z1,z2,z3,z4,z5]),(0,[z0,z1,z108,z2,z263,z5]),(0,[z951,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z952,z3,z4]),(0,[z0,z1,z2,z3,z4,z953]),(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z2,z955,z3,z5]),(0,[z0,z1,z2,z3,z4,z956]),(0,[z957,z1,z2,z3,z4,z5])]],
   [[(0,[z23,z766,z2,z3,z4,z5]),(0,[z0,z1,z958,z2,z3,z5]),(0,[z26,z114,z1,z2,z3,z62]),(0,[z0,z2,z3,z4,z764,z5]),(0,[z0,z1,z4,z736,z5,z11]),(1,[z0,z1,z2,z722,z5])],[(0,[z0,z1,z2,z3,z4,z959]),(0,[z0,z1,z2,z960,z4,z5]),(0,[z0,z53,z55,z3,z4,z5]),(0,[z0,z1,z2,z3,z961,z5]),(0,[z0,z1,z2,z722,z173,z5]),(0,[z175,z0,z1,z765,z2,z4])],[(0,[z0,z1,z2,z411,z3,z4]),(0,[z0,z1,z195,z4,z736,z5])],[(0,[z0,z1,z962,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z963]),(0,[z360,z0,z1,z2,z3,z374])]],
   [[(0,[z964,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z1,z966,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z967]),(0,[z968,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z58,z149])],[(0,[z0,z1,z969,z3,z4,z5]),(1,[z0,z756,z3,z4,z5]),(0,[z0,z1,z2,z174,z4,z5]),(0,[z0,z2,z803,z3,z4,z5])],[(0,[z0,z1,z2,z970,z4,z5])],[(0,[z0,z1,z2,z3,z4,z971]),(0,[z0,z1,z2,z3,z4,z972]),(0,[z633,z1,z2,z217,z4,z5]),(0,[z26,z1,z2,z3,z760,z5]),(0,[z229,z0,z1,z41,z3,z4])]],
   [[(0,[z1,z2,z3,z4,z973,z5]),(0,[z0,z46,z2,z47,z4,z5]),(0,[z0,z1,z2,z794,z3,z5]),(0,[z360,z0,z1,z15,z2,z3])],[(0,[z23,z24,z2,z3,z4,z5]),(0,[z0,z1,z2,z270,z4,z5]),(0,[z0,z1,z2,z974,z3,z4]),(0,[z0,z660,z2,z3,z4,z79])],[(0,[z0,z975,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z976,z5]),(0,[z120,z50,z1,z2,z3,z4]),(0,[z0,z1,z195,z196,z4,z5])],[(0,[z0,z766,z2,z3,z4,z5]),(0,[z977,z0,z1,z2,z3,z4]),(0,[z0,z2,z803,z8,z4,z5]),(0,[z0,z1,z7,z403,z2,z5]),(0,[z0,z1,z726,z2,z3,z4])]],
   [[(0,[z0,z978,z2,z3,z4,z5])],[(0,[z0,z1,z2,z979,z4,z5]),(0,[z0,z1,z68,z2,z4,z5]),(0,[z0,z1,z557,z3,z4,z66])],[(0,[z0,z1,z91,z3,z133,z5]),(0,[z0,z1,z2,z722,z3,z5])],[(0,[z980,z0,z1,z2,z3,z4]),(0,[z0,z1,z981,z3,z4,z5]),(0,[z0,z1,z2,z3,z58,z456]),(0,[z0,z982,z2,z3,z4,z5])]],
   [[(0,[z83,z1,z84,z3,z4,z5]),(0,[z0,z1,z983,z2,z4,z5]),(0,[z0,z1,z984,z3,z4,z5]),(0,[z0,z169,z2,z803,z4,z5]),(0,[z0,z1,z156,z794,z3,z5])],[(0,[z23,z24,z2,z3,z4,z6]),(0,[z0,z1,z88,z2,z3,z4]),(0,[z985,z0,z1,z2,z3,z4]),(1,[z1,z744,z3,z4,z5]),(0,[z422,z1,z2,z3,z4,z78]),(0,[z360,z0,z1,z587,z2,z3]),(0,[z0,z1,z10,z4,z736,z5]),(0,[z0,z1,z726,z2,z3,z59])],[(0,[z0,z1,z2,z986,z4,z5]),(0,[z29,z0,z2,z174,z30,z5]),(0,[z0,z1,z2,z3,z4,z987])],[(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z1,z2,z3,z4,z989]),(0,[z0,z56,z319,z2,z3,z89]),(0,[z0,z2,z3,z4,z990,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z991]),(1,[z1,z2,z713,z4,z5]),(0,[z0,z1,z2,z3,z4,z106])],[(0,[z0,z1,z992,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z993]),(0,[z0,z1,z994,z2,z4,z5]),(0,[z0,z1,z2,z995,z4,z5]),(0,[z0,z1,z2,z3,z4,z996]),(0,[z229,z0,z1,z293,z3,z4]),(0,[z0,z1,z2,z3,z4,z997]),(1,[z0,z1,z765,z2,z4])],[(1,[z0,z2,z3,z764,z5])],[(0,[z0,z1,z2,z3,z998,z5]),(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1,z2,z3,z1000,z4]),(0,[z536,z1,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z1001,z5]),(0,[z0,z1,z2,z3,z4,z117])]],
   [[(0,[z0,z1,z2,z3,z4,z1002]),(0,[z0,z1,z601,z3,z4,z66]),(0,[z0,z1,z2,z3,z4,z1003]),(1,[z0,z1,z715,z3,z4])],[(0,[z0,z1,z2,z1004,z4,z5]),(0,[z0,z1,z1005,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1006]),(0,[z0,z1,z2,z3,z4,z1007]),(0,[z1008,z1,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z3,z4]),(0,[z0,z1,z715,z3,z4,z66])],[(0,[z0,z1,z2,z1009,z4,z5])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 573) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 573).take 413) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 986)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [573, 413] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 122).take 6).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [122, 6] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_45300

theorem PEqualNP.Outside.L_meta_45300 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677312 * 2 ^ 32 + 4238928000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677312 * 2 ^ 32 + 4238928000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45300.solve