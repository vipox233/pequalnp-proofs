import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45838

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
  Nat.testBit (4008372960 * 2 ^ 32 + 4006135808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x800ac578661e1e18#64 ++ 0x100158af0cc3c3c3#64 ++ 0xe89fcff8ee3e3e3b#64 ++ 0x7d13f9ff1dc7c7c7#64 : BitVec 256),
   (0x0326131b00c2eae8#64 ++ 0x2064c26360185d5d#64 ++ 0xf766331f11c7ffff#64 ++ 0xfeecc663e238ffff#64 : BitVec 256),
   (0x18582c0dbe074740#64 ++ 0x830b0581b7c0e8e8#64 ++ 0xd8783c1ffe07c7c5#64 ++ 0xbb0f0783ffc0f8f8#64 : BitVec 256),
   (0x3d803ea01b6805b0#64 ++ 0x47b007d4036d00b6#64 ++ 0xbf803fe01ff807ff#64 ++ 0xf7f007fc03ff00ff#64 : BitVec 256),
   (0x7efd40001db5b001#64 ++ 0x0fdfa80003b6b600#64 ++ 0xffffc0001ffff801#64 ++ 0xdffff80003ffff00#64 : BitVec 256),
   (0x5ff7bbd6c0000002#64 ++ 0x0bfef77ad8000000#64 ++ 0x5fffffffe0000001#64 ++ 0xebfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xf766331f11c7ffff 0xfeecc663e238ffff

def z1 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z2 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z3 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x5fffffffe0000001 0xebfffffffc000000

def z4 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xffffc0001ffff801 0xdffff80003ffff00

def z5 : W := mkw 0x800ac55866161e08 0x100158ab0cc2c3c1 0xc81fcc18ee063e01 0x3903f9831dc0c7c0

def z6 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z7 : W := mkw 0x47a793d240000002 0x08f4f27a48000000 0x0787c3e000000000 0x40f0f87c00000000

def z8 : W := mkw 0x5fffbfdffe074742 0x8bfff7fbffc0e8e8 0xdffffffffe07c7c5 0xfbffffffffc0f8f8

def z9 : W := mkw 0x7ff53a8699a1a003 0x0ffea750d3343400 0x1760300711c1c000 0x82ec0600e2383800

def z10 : W := mkw 0x0002011800020a08 0x0000402300004141 0x4006001800063800 0x0800c0030000c700

def z11 : W := mkw 0x5cd1a8c4c0000002 0x0b9a351898000000 0x0899cce0e0000000 0x0113399c1c000000

def z12 : W := mkw 0x3d803ea91beaeff8 0x67b007d5237d5dff 0xbf803fe01fffffff 0xf7f007fc03ffffff

def z13 : W := mkw 0x800ac178641e1a18 0x1001582f0c83c343 0x609fc3f8e03e383a 0x4c13f87f1c07c707

def z14 : W := mkw 0x1850280480000000 0x030a050090000000 0x58783c1fe0000001 0xab0f0783fc000000

def z15 : W := mkw 0x3d883ea93f6f47f0 0xc7b107d527ede8fe 0xbf803fe01fffc7ff 0xf7f007fc03fff8ff

def z16 : W := mkw 0x8002817040080818 0x1000502e08010103 0x000003e00000003a 0x0000007c00000007

def z17 : W := mkw 0x0102131b00424ae8 0x202042636008495d 0xe006331f00063fff 0x7c00c663e000c7ff

def z18 : W := mkw 0x7ff53ea01b6805b0 0x4ffea7d4036d00b6 0xffffffe01ff807ff 0xfffffffc03ff00ff

def z19 : W := mkw 0x0102bbd6c0000002 0x0020577ad8000000 0x00003fffe0000000 0x200007fffc000000

def z20 : W := mkw 0x200840001db5b001 0x0401080003b6b600 0xa00000001ffff800 0x1400000003ffff00

def z21 : W := mkw 0x7eff411b1db7fa49 0x2fdfe82363b6ff49 0xffffc01f1ffff801 0xdffff803e3ffff00

def z22 : W := mkw 0x1850280d80024240 0x030a0501b0004848 0xd8783c1ff007c7c5 0xbb0f0783fe00f8f8

def z23 : W := mkw 0x5ff7bbdfc0c2eaea 0x2bfef77bf8185d5d 0xfffffffff1c7ffff 0xfffffffffe38ffff

def z24 : W := mkw 0x800a4538261e1e18 0x100148a704c3c3c3 0xe00603180e3e3e3b 0x7c00c06301c7c7c7

def z25 : W := mkw 0x66fd400005b5b001 0x0cdfa80000b6b600 0x67ffc00001fff800 0x4cfff800003fff00

def z26 : W := mkw 0x000804093e074740 0x8001008127c0e8e8 0x800000001e07c7c4 0x1000000003c0f8f8

def z27 : W := mkw 0x0326131b0082ea48 0x2064c26360105d49 0x5766331f0007f801 0xeaecc663e000ff00

def z28 : W := mkw 0x1850280598014140 0x830a0500b3002828 0x58783c1ff001c1c5 0xab0f0783fe003838

def z29 : W := mkw 0x800ac579661e5e58 0x100158af2cc3cbcb 0xf8fffffffe3fffff 0xff1fffffffc7ffff

def z30 : W := mkw 0x022c40000494b000 0x0045880000929600 0xffffc0001ffff801 0xdffff80003ffff00

def z31 : W := mkw 0x832ed77b66defef8 0x3065daef6cdbdfdf 0xffffffffffffffff 0xffffffffffffffff

def z32 : W := mkw 0x7ef5000019a1a001 0x0fdea00003343400 0x1760000011c1c000 0x82ec000002383800

def z33 : W := mkw 0x80028578620a0e18 0x100050af0c4141c3 0x00000ff8e000063a 0x200001ff1c0000c7

def z34 : W := mkw 0x0002011800020a08 0x0000402300004141 0xe006031800063e3b 0x7c00c0630000c7c7

def z35 : W := mkw 0x47f793d6c0000002 0x08fef27ad8000000 0x47ffc3ffe0000000 0x48fff87ffc000000

def z36 : W := mkw 0xfefd44283fbfbe19 0x1fdfa88507f7f7c3 0xffffc0001ffffe3b 0xdffff80003ffffc7

def z37 : W := mkw 0x0000042002080410 0x0000008400410082 0xa8800fe00e38063b 0x751001fc01c700c7

def z38 : W := mkw 0x1858280dbc074340 0x830b0501b780e868 0x5078301ff007c1c4 0x8a0f0603fe00f838

def z39 : W := mkw 0x0002815040000000 0x0000502a08000000 0x489fcff8e0000001 0x6913f9ff1c000000

def z40 : W := mkw 0x7ffffbd6ddb5b003 0x0fffff7adbb6b600 0xfffffffffffff801 0xffffffffffffff00

def z41 : W := mkw 0x258012a0016800b0 0x44b00254002d0016 0xb78033e011f807ff 0xf6f0067c023f00ff

def z42 : W := mkw 0x0324120300c0e0e0 0x2064824060181c1c 0x1760300711c1c1c4 0x82ec0600e2383838

def z43 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0x1f803ce01ff801c4 0x83f0079c03ff0038

def z44 : W := mkw 0x1850280d98034340 0x830a0501b3006868 0xd060301f1007c7c5 0xba0c0603e200f8f8

def z45 : W := mkw 0x3cd82c0dbf274740 0x879b0581b7e4e8e8 0xfff83c1fffffc7c5 0xffff0783fffff8f8

def z46 : W := mkw 0x00020538020a0e18 0x000040a7004141c3 0xe8860ff80e3e3e3b 0x7d10c1ff01c7c7c7

def z47 : W := mkw 0x0326131200000000 0x0064c26240000000 0x5766331f00000001 0xeaecc663e0000000

def z48 : W := mkw 0x0058000da4074240 0x800b0001b480e848 0x4078001fe007c000 0x080f0003fc00f800

def z49 : W := mkw 0x258012a0016800b0 0x44b00254002d0016 0x278003e001f8003a 0x44f0007c003f0007

def z50 : W := mkw 0x0580128000000000 0x00b0025000000000 0x078003e000000000 0x40f0007c00000000

def z51 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xa0000ff8ee3e3e3a 0x340001ff1dc7c7c7

def z52 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xb76000001ffff800 0x96ec000003ffff00

def z53 : W := mkw 0x3cd82cadbf2f4750 0xc79b0595b7e5e8ea 0xd8f83cfffe3fc7c5 0xbb1f079fffc7f8f8

def z54 : W := mkw 0x1800280018000100 0x0300050003000020 0x10003000100001c4 0x8200060002000038

def z55 : W := mkw 0x18502c0dba034740 0x830a0581b74068e8 0x10603c1ff001c7c4 0xa20c0783fe0038f8

def z56 : W := mkw 0x0326131200c0a8a8 0x2064c26240181515 0x2706030001c0383a 0x44e0c06000380707

def z57 : W := mkw 0x5ff7bbd6c0c0a8aa 0x2bfef77ad8181515 0x7fffffffe1c0383b 0xeffffffffc380707

def z58 : W := mkw 0x66a5400001b0b001 0x0cd4a80000361600 0x2787c00001f83800 0x44f0f800003f0700

def z59 : W := mkw 0x2000000019200000 0x0400000003240000 0xa00000001ff80000 0x1400000003ff0000

def z60 : W := mkw 0x3c8840001d341000 0x0791080003a68200 0xff9fc0001ffe3801 0xdff3f80003ffc700

def z61 : W := mkw 0x832ed35b64d6fae8 0x3065da6b6c9adf5d 0xf77ff31ff1c7ffff 0xfeeffe63fe38ffff

def z62 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x0f9fcfe0e0000000 0x41f3f9fc1c000000

def z63 : W := mkw 0x7ff7bff6db6805b2 0x4ffef7fedb6d00b6 0xfffffffffff807ff 0xffffffffffff00ff

def z64 : W := mkw 0x800ac57966defef8 0x300158af2cdbdfdf 0xe89fcff8ffffffff 0x7d13f9ff1fffffff

def z65 : W := mkw 0x185800091c074240 0x030b00012380e848 0xd878301f1e07c7c5 0xbb0f0603e3c0f8f8

def z66 : W := mkw 0x0008040826060600 0x0001008104c0c0c0 0xc8180c18ee060601 0x390301831dc0c0c0

def z67 : W := mkw 0x985aed7dfe1f5f58 0x930b5dafbfc3ebeb 0xf8fffffffe3fffff 0xff1fffffffc7ffff

def z68 : W := mkw 0x1d803a8000000000 0x03b0075000000000 0x1f803fe000000001 0xe3f007fc00000000

def z69 : W := mkw 0x200004201b6805b0 0x44000084036d00b6 0xa00000001ff807fe 0x1400000003ff00ff

def z70 : W := mkw 0x80084428261e1e18 0x1001088504c3c3c3 0xa8800fe00e3e3e3b 0x751001fc01c7c7c7

def z71 : W := mkw 0x0002011000000808 0x0000402200000101 0x200603000000383a 0x4400c06000000707

def z72 : W := mkw 0x0050000480000000 0x000a000090000000 0x4078001fe0000000 0x080f0003fc000000

def z73 : W := mkw 0x66ad40001db5b001 0x0cd5a80003b6b600 0xa787c0001ffff800 0x54f0f80003ffff00

def z74 : W := mkw 0x01003ea0024805b0 0x402007d4004900b6 0x00003fe0000007fe 0x200007fc000000ff

def z75 : W := mkw 0x427d40000495b001 0x084fa8000092b600 0x407fc0000007f800 0x080ff8000000ff00

def z76 : W := mkw 0x5ef5000000000000 0x0bdea00000000000 0x5fffc00000000001 0xcbfff80000000000

def z77 : W := mkw 0x185aad5dfe074740 0x830b55abbfc0e8e8 0xd8fffffffe07c7c5 0xfb1fffffffc0f8f8

def z78 : W := mkw 0x00082c0da6064740 0x80010581b4c0c8e8 0xc8183c1fee0607c5 0x39030783fdc0c0f8

def z79 : W := mkw 0x0000000900024240 0x0000000120004848 0xd060301f1007c7c5 0xba0c0603e200f8f8

def z80 : W := mkw 0x1b7e3f1fbec7efe8 0xa36fc7e3f7d8fdfd 0xff7e3f1fffc7ffff 0xffefc7e3fff8ffff

def z81 : W := mkw 0x19003e001a4005a0 0x032007c0034800b4 0xbf003f001fc007ff 0xf7e007e003f800ff

def z82 : W := mkw 0x18002c001a000500 0x03000580034000a0 0x08000c000e000000 0x0100018001c00000

def z83 : W := mkw 0x5ff7bbd6c04000a2 0x0bfef77ad8080014 0xfffffffff1c007ff 0xfffffffffe3800ff

def z84 : W := mkw 0x7efd6ca01fbdb511 0x4fdfad9403f7b6a2 0xffffcce01ffff801 0xdffff99c03ffff00

def z85 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0x6766031f01c7f83a 0x4cecc063e038ff07

def z86 : W := mkw 0x7fffd3d25db5b003 0x0ffffa7a4bb6b600 0xffffc3e01ffff801 0xdffff87c03ffff00

def z87 : W := mkw 0x800844293e1f5f58 0x9001088527c3ebeb 0xa00000001e3ffffe 0x1400000003c7ffff

def z88 : W := mkw 0x8008442926defef8 0x3001088524dbdfdf 0xa00000001ffffffe 0x1400000003ffffff

def z89 : W := mkw 0x0000000900024240 0x0000000120004848 0x0000301f000007c4 0x20000603e00000f8

def z90 : W := mkw 0x01023fbb024a4ff8 0x602047f7604949ff 0x00003fff000007fe 0x200007ffe00000ff

def z91 : W := mkw 0x7cd940001d351001 0x0f9b280003a6a200 0x0899c0000e380000 0x0113380001c70000

def z92 : W := mkw 0x7fff531b1df7fae9 0x2fffea6363beff5d 0xfffff31f1fffffff 0xfffffe63e3ffffff

def z93 : W := mkw 0x7fffbfffff6f47f2 0xcffff7ffffede8fe 0xffffffffffffc7ff 0xfffffffffffff8ff

def z94 : W := mkw 0x0008000824060200 0x000100010480c040 0x40180018e0060000 0x080300031c00c000

def z95 : W := mkw 0x0008000004040000 0x0001000000808000 0xc81800000e060001 0x1903000001c0c000

def z96 : W := mkw 0x7ffffff6dffdb5b3 0x4ffffffedbffb6b6 0xffffffffffffffff 0xffffffffffffffff

def z97 : W := mkw 0x3c802ca01b280510 0x47900594036500a2 0xbf800ce01ff80001 0xd7f0019c03ff0000

def z98 : W := mkw 0x0226011b0082ea48 0x2044c02360105d49 0xf766001f11c7f801 0xdeecc003e238ff00

def z99 : W := mkw 0x01001200004000a0 0x0020024000080014 0xb700330011c007ff 0xf6e00660023800ff

def z100 : W := mkw 0x5ef7a9d6c0000002 0x0bdef53ad8000000 0x48ffccffe0000000 0x091ff99ffc000000

def z101 : W := mkw 0x0224000000000000 0x0044800000000000 0x5766000000000001 0xcaecc00000000000

def z102 : W := mkw 0x022400000080a000 0x0044800000101400 0xf766000011c7f801 0xdeecc0000238ff00

def z103 : W := mkw 0x3d823fb81b6a0fb8 0x47b047f7036d41f7 0xff863ff81ffe3fff 0xfff0c7ff03ffc7ff

def z104 : W := mkw 0x1b7e131b1cc7eae8 0x236fc2636398fd5d 0xff7e331f1fc7ffff 0xffefc663e3f8ffff

def z105 : W := mkw 0x42778156c0000002 0x084ef02ad8000000 0x407fc01fe0000000 0x080ff803fc000000

def z106 : W := mkw 0x5ef78156c0000002 0x0bdef02ad8000000 0x5fffc01fe0000001 0xcbfff803fc000000

def z107 : W := mkw 0x80084428261e1e18 0x1001088504c3c3c3 0xa00000000e3e3e3a 0x1400000001c7c7c7

def z108 : W := mkw 0x27a613b201e8a8b8 0x64f4c276403d1517 0x278603e001f8383a 0x44f0c07c003f0707

def z109 : W := mkw 0x5cd1a8c4c0000002 0x0b9a351898000000 0x58f9fcffe0000001 0xab1f3f9ffc000000

def z110 : W := mkw 0x0058000da4074240 0x800b0001b480e848 0xd078301ff007c7c5 0xba0f0603fe00f8f8

def z111 : W := mkw 0x3c802ca01b280510 0x47900594036500a2 0x08800ce00e380000 0x0110019c01c70000

def z112 : W := mkw 0x1800000018000000 0x0300000003000000 0x980000001e000001 0x9300000003c00000

def z113 : W := mkw 0x032e171b3ec7efe8 0xa065c2e367d8fdfd 0xf766331f1fc7ffff 0xfeecc663e3f8ffff

def z114 : W := mkw 0x3fa63b9b19e2ebe8 0x67f4c773633c5d7d 0xf766331f11c7ffff 0xfeecc663e238ffff

def z115 : W := mkw 0xbd82bff87b6a0fb8 0x57b057ff0f6d41f7 0xbf803ff8fff807ff 0xf7f007ff1fff00ff

def z116 : W := mkw 0x5dd1bac4c0000002 0x0bba375898000000 0x1f99ffe0e0000001 0xe3f33ffc1c000000

def z117 : W := mkw 0x5ff7bbd6c080a002 0x0bfef77ad8101400 0xfffffffff1c7f801 0xfffffffffe38ff00

def z118 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0x1ff9c0001ff9c000 0x83ff380003ff3800

def z119 : W := mkw 0x1800280000000000 0x0300050000000000 0x18003c0000000001 0xa300078000000000

def z120 : W := mkw 0x1850280598014140 0x830a0500b3002828 0x106030071001c1c4 0x820c0600e2003838

def z121 : W := mkw 0x027e011fa487ea48 0xa04fc023f490fd49 0x407e001fe007f800 0x080fc003fc00ff00

def z122 : W := mkw 0x00002c04a2000500 0x80000580944000a0 0x00000c00e0000000 0x000001801c000000

def z123 : W := mkw 0x18582c04be050500 0x830b058097c0a0a0 0x98183c00fe0007c5 0xb30307801fc000f8

def z124 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xa706030011c7fffe 0x54e0c0600238ffff

def z125 : W := mkw 0x4377bbd6c0000002 0x086ef77ad8000000 0x407fffffe0000000 0x280ffffffc000000

def z126 : W := mkw 0x3c80000019200000 0x0790000003240000 0xbf8000001ff80001 0xd7f0000003ff0000

def z127 : W := mkw 0x7ffd7ea01ffdb5b1 0x4fffafd403ffb6b6 0xffffffe01fffffff 0xfffffffc03ffffff

def z128 : W := mkw 0x800ac15864161a08 0x1001582b0c82c341 0x401fc018e0063800 0x0803f8031c00c700

def z129 : W := mkw 0xbd8afff87f7e1fb8 0x57b15fff0fefc3f7 0xff9ffff8fffe3fff 0xfff3ffff1fffc7ff

def z130 : W := mkw 0x0008400004141000 0x0001080000828200 0xe89fc0000e3e3801 0x5d13f80001c7c700

def z131 : W := mkw 0x210016201b6805b0 0x442002c4036d00b6 0xb70033001ff807ff 0xf6e0066003ff00ff

def z132 : W := mkw 0x00080428260e0610 0x0001008504c1c0c2 0xe8980ff8ee3e063b 0x7d1301ff1dc7c0c7

def z133 : W := mkw 0x0008440826161600 0x0001088104c2c2c0 0xe89fcc18ee3e3e01 0x7d13f9831dc7c7c0

def z134 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0x5766301f11c7f9c4 0x8aecc603e238ff38

def z135 : W := mkw 0x8008c468661e1610 0x1001188d0cc3c2c2 0xc899ccf8ee3e0601 0x3913399f1dc7c0c0

def z136 : W := mkw 0x0008040926064640 0x0001008124c0c8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z137 : W := mkw 0x3dd83eadbf6f47f0 0xc7bb07d5b7ede8fe 0xfff83fffffffc7ff 0xffff07fffffff8ff

def z138 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x577ff01fe0000000 0x8aeffe03fc000000

def z139 : W := mkw 0x21003ea01b6805b0 0x442007d4036d00b6 0xa0003fe01ff807fe 0x340007fc03ff00ff

def z140 : W := mkw 0x98586c2dbe1f5f58 0x930b0d85b7c3ebeb 0xf8783c1ffe3fffff 0xbf0f0783ffc7ffff

def z141 : W := mkw 0x1b7e3f1fbe074740 0x836fc7e3f7c0e8e8 0xdf7e3f1ffe07c7c5 0xfbefc7e3ffc0f8f8

def z142 : W := mkw 0x0000000000000000 0x0000000000000000 0xa88000000e380001 0x5510000001c70000

def z143 : W := mkw 0xdffffffee61e1e1a 0x1bffffffdcc3c3c3 0xffffffffee3e3e3b 0xfffffffffdc7c7c7

def z144 : W := mkw 0x01001200004000a0 0x0020024000080014 0x00003300000007fe 0x20000660000000ff

def z145 : W := mkw 0x0000042002080410 0x0000008400410082 0x08800ce00e380000 0x0110019c01c70000

def z146 : W := mkw 0x0102131b00424ae8 0x202042636008495d 0x0000331f000007fe 0x20000663e00000ff

def z147 : W := mkw 0x3dd03ea59b6945f0 0xc7ba07d4b36d28be 0xbfe03fe71ff9c7ff 0xf7fc07fce3ff38ff

def z148 : W := mkw 0x7ff7bbd6d9200002 0x0ffef77adb240000 0xfffffffffff80001 0xffffffffffff0000

def z149 : W := mkw 0x00028156c0000002 0x0000502ad8000000 0x0000001fe0000000 0x00000003fc000000

def z150 : W := mkw 0xfffffff87fffbfb9 0x5fffffff0ffff7f7 0xfffffff8ffffffff 0xffffffff1fffffff

def z151 : W := mkw 0x18002c0dba024740 0x83000581b74048e8 0x98003c1ffe0007c5 0xb3000783ffc000f8

def z152 : W := mkw 0x000ac15044141000 0x0001582a08828200 0xe89fcff8ee3e3801 0x7d13f9ff1dc7c700

def z153 : W := mkw 0x7efd6c0dbfb7f741 0x8fdfad81b7f6fee8 0xfffffc1fffffffc5 0xffffff83fffffff8

def z154 : W := mkw 0xfeffc5787fbfbe19 0x1fdff8af0ff7f7c3 0xffffcff8fffffe3b 0xfffff9ff1fffffc7

def z155 : W := mkw 0x022601120080a808 0x2044c02240101501 0x0006000000003800 0x0000c00000000700

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0xe006000000063801 0x5c00c0000000c700

def z157 : W := mkw 0x00002c0da2024740 0x80000581b44048e8 0x00003c1fe00007c4 0x20000783fc0000f8

def z158 : W := mkw 0x0058040dbe074740 0x800b0081b7c0e8e8 0xc078001ffe07c7c4 0x180f0003ffc0f8f8

def z159 : W := mkw 0x822ec57b669efe58 0x3045d8af6cd3dfcb 0xe8ffcfffee3ffe3b 0x7d1ff9fffdc7ffc7

def z160 : W := mkw 0x0324120b00c2e2e0 0x2064824160185c5c 0xd760301f11c7c7c5 0xbaec0603e238f8f8

def z161 : W := mkw 0x7efd00001da5a001 0x0fdfa00003b4b400 0xdf7800001fc7c001 0x9bef000003f8f800

def z162 : W := mkw 0x3d803a80196001a0 0x47b00750032c0034 0x1700300011c001c4 0x82e0060002380038

def z163 : W := mkw 0x7ff7bbd6d96001a2 0x4ffef77adb2c0034 0x5ffffffff1c001c5 0xebfffffffe380038

def z164 : W := mkw 0x18582c04be050500 0x830b058097c0a0a0 0x58783c1fee000001 0xab0f0783fdc00000

def z165 : W := mkw 0x7ff53a8019e1a1a1 0x4ffea750033c3434 0x1760300011c1c1c4 0x82ec060002383838

def z166 : W := mkw 0x185828049c050000 0x030b05009380a000 0xd8783c1ffe07c001 0xbb0f0783ffc0f800

def z167 : W := mkw 0x195abfdffe074742 0x832b57fbffc0e8e8 0xd8783ffffe07c7c5 0xbb0f07ffffc0f8f8

def z168 : W := mkw 0x9858ec6dfe1f5750 0x930b1d8dbfc3eaea 0xd8f9fcfffe3fc7c5 0xbb1f3f9fffc7f8f8

def z169 : W := mkw 0x66ad400005b4b001 0x0cd5a80000b69600 0xef9fc0000ffe3801 0x5df3f80001ffc700

def z170 : W := mkw 0x0226011b0082ea48 0x2044c02360105d49 0x4066001f0007f800 0x080cc003e000ff00

def z171 : W := mkw 0x80028578620a0e18 0x100050af0c4141c3 0xe0060ff8e0063e3b 0x7c00c1ff1c00c7c7

def z172 : W := mkw 0x0326131300c0e8e8 0x2064c26260181d1d 0x3766330711c1f9fe 0xc6ecc660e2383f3f

def z173 : W := mkw 0x185840001c151000 0x030b08000382a200 0xf8ffc0001e3ff801 0xdf1ff80003c7ff00

def z174 : W := mkw 0xc7a7d3f24018181a 0x18f4fa7e48030303 0x2787c3e00038383a 0x44f0f87c00070707

def z175 : W := mkw 0xfefdc4607fbdb411 0x1fdfb88c0ff7b682 0xffffcce0fffff801 0xdffff99c1fffff00

def z176 : W := mkw 0x8002c57042181c18 0x100058ae08430383 0xa887cfe00e383e3b 0x7510f9fc01c707c7

def z177 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0x489fccf8ee3e3800 0x0913f99f1dc7c700

def z178 : W := mkw 0x0000000900c2eae8 0x2000000120185d5d 0xa000000011c7fffe 0x140000000238ffff

def z179 : W := mkw 0x985aed7ce61e1e18 0x130b5daf9cc3c3c3 0xf8ffffffee3e3e3b 0xff1ffffffdc7c7c7

def z180 : W := mkw 0x0326935240000000 0x0064d26a48000000 0x5fffffffe0000001 0xebfffffffc000000

def z181 : W := mkw 0x985ac5787e1f1e18 0x130b58af0fc3e3c3 0xf8ffcff8fe3ffe3b 0xff1ff9ff1fc7ffc7

def z182 : W := mkw 0x18582c04be050500 0x830b058097c0a0a0 0x08180c00ee000000 0x010301801dc00000

def z183 : W := mkw 0x67a7531201f0b8a9 0x2cf4ea62403e1715 0x2787c30001f8383a 0x44f0f860003f0707

def z184 : W := mkw 0x00002c0da2024740 0x80000581b44048e8 0xd0603c1ff007c7c5 0xba0c0783fe00f8f8

def z185 : W := mkw 0x8008c460661c1410 0x1001188c0cc38282 0x0899cce0ee380000 0x0113399c1dc70000

def z186 : W := mkw 0x000004001a000500 0x00000080034000a0 0x800000001e0007c4 0x1000000003c000f8

def z187 : W := mkw 0x0326935b40c2eae8 0x2064d26b68185d5d 0xfffffffff1c7ffff 0xfffffffffe38ffff

def z188 : W := mkw 0x7efd40001d351001 0x0fdfa80003a6a200 0x5fffc0000e380001 0xcbfff80001c70000

def z189 : W := mkw 0x7ffd52a01dfdb0b1 0x4fffaa5403bfb616 0xffffc3e01ffff83b 0xdffff87c03ffff07

def z190 : W := mkw 0xe6afc57867bebe19 0x1cd5f8af0cf7d7c3 0xef9fcff8effe3e3b 0x7df3f9ff1dffc7c7

def z191 : W := mkw 0x00000000004000a0 0x0000000000080014 0xa000000011c007fe 0x14000000023800ff

def z192 : W := mkw 0x2000400001b0b001 0x0400080000361600 0x2000000001f83800 0x04000000003f0700

def z193 : W := mkw 0x5ef5000000000000 0x0bdea00000000000 0x1760000000000000 0x82ec000000000000

def z194 : W := mkw 0x0102bbdfc0424aea 0x2020577bf808495d 0x00003fffe00007fe 0x200007fffc0000ff

def z195 : W := mkw 0x3d883ea83f6e07b0 0x47b107d507edc0f6 0xff983ff8fffe07ff 0xfff307ff1fffc0ff

def z196 : W := mkw 0x7ff53ea69b6805b2 0x4ffea7d4d36d00b6 0xbfe03fe71ff807ff 0xf7fc07fce3ff00ff

def z197 : W := mkw 0x18586c0dbe175740 0x830b0d81b7c2eae8 0xf8fffc1ffe3fffc5 0xff1fff83ffc7fff8

def z198 : W := mkw 0xbd88fee07f7c15b0 0x57b11fdc0fef82b6 0xbf99ffe0fff807ff 0xf7f33ffc1fff00ff

def z199 : W := mkw 0x000a855866060600 0x000150ab0cc0c0c0 0xc89fcff8ee060601 0x7913f9ff1dc0c0c0

def z200 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x48780c1fee07c000 0x090f0183fdc0f800

def z201 : W := mkw 0x00002ca002080510 0x40000594004100a2 0x00000ce000000000 0x0000019c00000000

def z202 : W := mkw 0x7efd40091df7fae9 0x2fdfa80123beff5d 0xffffc0001fffffff 0xdffff80003ffffff

def z203 : W := mkw 0x27a613bb01eaeaf8 0x64f4c277603d5d5f 0xf7e633ff11ffffff 0xfefcc67fe23fffff

def z204 : W := mkw 0x0000000118014140 0x8000000023002828 0x000000001001c1c4 0x0000000002003838

def z205 : W := mkw 0x5cd9accdfe074742 0x8b9b3599bfc0e8e8 0xd8f9fcfffe07c7c5 0xbb1f3f9fffc0f8f8

def z206 : W := mkw 0x1a7c00001c85a000 0x034f80000390b400 0xff7e00001fc7f801 0xdfefc00003f8ff00

def z207 : W := mkw 0x5fffbbd6dc050002 0x0bfff77adb80a000 0xdffffffffe07c001 0xfbffffffffc0f800

def z208 : W := mkw 0x5ff53a8680000002 0x0bfea750d0000000 0x1760300700000000 0x82ec0600e0000000

def z209 : W := mkw 0x6481400001301001 0x0c90280000260200 0x0081c00000380000 0x0010380000070000

def z210 : W := mkw 0x7ffffbd6dd351003 0x0fffff7adba6a200 0x5fffffffee380001 0xebfffffffdc70000

def z211 : W := mkw 0x0102bfdfe2024742 0x802057fbfc4048e8 0x00003fffe00007c4 0x200007fffc0000f8

def z212 : W := mkw 0x022400090082e240 0x0044800120105c48 0xf766301f11c7ffc5 0xfeecc603e238fff8

def z213 : W := mkw 0x19583e0dbe4747e0 0x832b07c1b7c8e8fc 0xff783f1fffc7c7ff 0xffef07e3fff8f8ff

def z214 : W := mkw 0x8008c460661c1410 0x1001188c0cc38282 0xa899cfe0ee38063b 0x751339fc1dc700c7

def z215 : W := mkw 0x822ec15b6496fa48 0x3045d82b6c92df49 0x407fc01fe007f800 0x080ff803fc00ff00

def z216 : W := mkw 0x010293d240000002 0x0020527a48000000 0x000003e000000000 0x0000007c00000000

def z217 : W := mkw 0x8002ad7de20a4f58 0x900055afbc4149eb 0x00003fffe00007fe 0x200007fffc0000ff

def z218 : W := mkw 0x1858280da4074240 0x830b0501b480e848 0x58783c1fe007c001 0xab0f0783fc00f800

def z219 : W := mkw 0x3fa63fbb1beaeff8 0x67f4c7f7637d5dff 0xffe63fff1fffffff 0xfffcc7ffe3ffffff

def z220 : W := mkw 0x5cd1288480000002 0x0b9a251090000000 0x0000000000000000 0x0000000000000000

def z221 : W := mkw 0x0326bbdfc0c2eaea 0x2064d77bf8185d5d 0xf7663ffff1c7ffff 0xfeecc7fffe38ffff

def z222 : W := mkw 0x5ef500000080a000 0x0bdea00000101400 0xffffc00011c7f801 0xdffff8000238ff00

def z223 : W := mkw 0x2480000001200000 0x0490000000240000 0x2780000001f80000 0x44f00000003f0000

def z224 : W := mkw 0x4275000680000002 0x084ea000d0000000 0x0060000700000000 0x000c0000e0000000

def z225 : W := mkw 0x5dd3bbd6c0000002 0x0bba777ad8000000 0x0899ffffe0000000 0x21133ffffc000000

def z226 : W := mkw 0x385840001db5b001 0x070b080003b6b600 0xf87800001ffff801 0x9f0f000003ffff00

def z227 : W := mkw 0x000000090082ea48 0x2000000120105d49 0x000000000007f800 0x000000000000ff00

def z228 : W := mkw 0x800aed7de61e5f58 0x90015dafbcc3cbeb 0xe89fffffee3e3fff 0x7d13fffffdc7c7ff

def z229 : W := mkw 0xc27fc1586497ba09 0x184ff82b0c92f741 0x407fc018e007f800 0x080ff8031c00ff00

def z230 : W := mkw 0x810afffee61e1e1a 0x10215fffdcc3c3c3 0xe89fffffee3e3e3b 0x7d13fffffdc7c7c7

def z231 : W := mkw 0x0326131b00424ae8 0x2064c2636008495d 0x5766331f000007ff 0xeaecc663e00000ff

def z232 : W := mkw 0x3c80000019200000 0x0790000003240000 0x088000000e380000 0x0110000001c70000

def z233 : W := mkw 0x0326131b00024240 0x0064c26360004848 0xd766331f1007c7c5 0xfaecc663e200f8f8

def z234 : W := mkw 0x0102bff6c24805b2 0x402057fed84900b6 0x00003fffe00007fe 0x200007fffc0000ff

def z235 : W := mkw 0x0324120000c0a0a0 0x0064824000181414 0xf766330011c7ffff 0xfeecc6600238ffff

def z236 : W := mkw 0x800ac570661c1c18 0x100158ae0cc38383 0x289fcfe0ee38383a 0x4513f9fc1dc70707

def z237 : W := mkw 0x185800001c050000 0x030b00000380a000 0x081800000e000000 0x0103000001c00000

def z238 : W := mkw 0x5ff7bbdfc082ea4a 0x2bfef77bf8105d49 0x5fffffffe007f801 0xebfffffffc00ff00

def z239 : W := mkw 0xfeffc1705dbdb819 0x1fdff82e0bb7b703 0xffffc3e01ffff83b 0xdffff87c03ffff07

def z240 : W := mkw 0x800ac15864161a08 0x1001582b0c82c341 0x489fcff8e0063801 0x6913f9ff1c00c700

def z241 : W := mkw 0x7efd68049db5b001 0x0fdfad0093b6b600 0xfffffc1ffffff801 0xffffff83ffffff00

def z242 : W := mkw 0x185800001c050000 0x030b00000380a000 0xd87800001e07c001 0x9b0f000003c0f800

def z243 : W := mkw 0x985aad7dfe0f4f58 0x930b55afbfc1e9eb 0xd8783ffffe07c7ff 0xbb0f07ffffc0f8ff

def z244 : W := mkw 0x7fffffdfffb7f743 0x8ffffffbfff6fee8 0xffffffffffffffc5 0xfffffffffffffff8

def z245 : W := mkw 0x5efd40000495b001 0x0bdfa8000092b600 0x5fffc0000007f801 0xcbfff8000000ff00

def z246 : W := mkw 0x7ff5120319e1e0e1 0x2ffea240633c3c1c 0x1760300711c1c1c4 0x82ec0600e2383838

def z247 : W := mkw 0x8102977b624a4ef8 0x302052ef6c4949df 0x00003fffe00007fe 0x200007fffc0000ff

def z248 : W := mkw 0x3cd800001d250000 0x079b000003a4a000 0xfff800001fffc001 0xdfff000003fff800

def z249 : W := mkw 0x25803ea0036805b0 0x44b007d4006d00b6 0x27803fe001f807fe 0x64f007fc003f00ff

def z250 : W := mkw 0x5ff53a8680000002 0x0bfea750d0000000 0x5f783c1fe0000001 0xabef0783fc000000

def z251 : W := mkw 0x7cd940001db5b001 0x0f9b280003b6b600 0xa899c0001ffff800 0x1513380003ffff00

def z252 : W := mkw 0x47a793d240c0a8aa 0x28f4f27a48181515 0x2787c3e001c0383a 0x44f0f87c00380707

def z253 : W := mkw 0x0000a8c4c0000002 0x0000151898000000 0x00000ce0e0000000 0x0000019c1c000000

def z254 : W := mkw 0x000804003e050500 0x8001008007c0a0a0 0x000000000e000000 0x0000000001c00000

def z255 : W := mkw 0x000a411804161a08 0x000148230082c341 0xe89fc3180e3e3e3b 0x7d13f86301c7c7c7

def z256 : W := mkw 0x01001620024804b0 0x002002c400490096 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z257 : W := mkw 0x8002c17040181818 0x1000582e08030303 0x2087c3e00038383a 0x4410f87c00070707

def z258 : W := mkw 0x5ff7131b00c2eae8 0x2bfee26360185d5d 0xfffff31f11c7ffff 0xfffffe63e238ffff

def z259 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0x08803fe00e3807fe 0x211007fc01c700ff

def z260 : W := mkw 0x4275000000000000 0x084ea00000000000 0x407fc00000000000 0x080ff80000000000

def z261 : W := mkw 0x448180c040000002 0x0890301808000000 0x0081c0e000000000 0x0010381c00000000

def z262 : W := mkw 0x5ff7bfdfe2024742 0x8bfef7fbfc4048e8 0x5fffffffe00007c5 0xebfffffffc0000f8

def z263 : W := mkw 0x0102bbd6c0000002 0x0020577ad8000000 0x489fffffe0000001 0x6913fffffc000000

def z264 : W := mkw 0x3d803a80196001a0 0x47b00750032c0034 0x1f803fe011c001c5 0xe3f007fc02380038

def z265 : W := mkw 0x40518044c0000002 0x080a300898000000 0x0019c000e0000000 0x000338001c000000

def z266 : W := mkw 0x4277815fc082ea4a 0x284ef02bf8105d49 0x407fc01fe007f800 0x080ff803fc00ff00

def z267 : W := mkw 0x0226011200000000 0x0044c02240000000 0x4066001f00000000 0x080cc003e0000000

def z268 : W := mkw 0x5cd1000000000000 0x0b9a200000000000 0x0899c00000000000 0x0113380000000000

def z269 : W := mkw 0x8008c460661c1410 0x1001188c0cc38282 0xe89fcce0ee3e3801 0x5d13f99c1dc7c700

def z270 : W := mkw 0x0000000900c2eae8 0x2000000120185d5d 0xf060301f11c7ffff 0xbe0c0603e238ffff

def z271 : W := mkw 0x427d40000495b001 0x084fa8000092b600 0xf77fc00011c7f801 0xdeeff8000238ff00

def z272 : W := mkw 0x0324120200000000 0x0064824040000000 0x1760300700000000 0x82ec0600e0000000

def z273 : W := mkw 0x18582c0dbec7efe8 0xa30b0581b7d8fdfd 0xf8783c1fffc7ffff 0xbf0f0783fff8ffff

def z274 : W := mkw 0x18002c001a000500 0x03000580034000a0 0x98003c001e0007c5 0xb300078003c000f8

def z275 : W := mkw 0x3ea4000019a0a000 0x07d4800003341400 0xffe600001ffff801 0xdffcc00003ffff00

def z276 : W := mkw 0x3c802ca01b280510 0x47900594036500a2 0xa8800fe00e38063b 0x751001fc01c700c7

def z277 : W := mkw 0x200004201b6805b0 0x44000084036d00b6 0xa8800fe01ff807ff 0x751001fc03ff00ff

def z278 : W := mkw 0x5ff53a8780c0e0e2 0x2bfea750f0181c1c 0x1760300711c1c1c4 0x82ec0600e2383838

def z279 : W := mkw 0x18582c05be054540 0x830b0580b7c0a8a8 0x18783c07fe01c1c4 0x830f0780ffc03838

def z280 : W := mkw 0x7efd68059db5f141 0x8fdfad00b3b6be28 0xfffff0071ffff9c5 0xdffffe00e3ffff38

def z281 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x17603fffe0000000 0xa2ec07fffc000000

def z282 : W := mkw 0x5ff53a8000000000 0x0bfea75000000000 0x5fffffe000000001 0xebfffffc00000000

def z283 : W := mkw 0x810ad77b665e5ef8 0x30215aef6ccbcbdf 0xe89fffffee3e3fff 0x7d13fffffdc7c7ff

def z284 : W := mkw 0x7cd940001d351001 0x0f9b280003a6a200 0xe89fc0000e3e3801 0x5d13f80001c7c700

def z285 : W := mkw 0x1850280480000000 0x030a050090000000 0x1060300700000000 0x820c0600e0000000

def z286 : W := mkw 0x7fff53121db5b001 0x0fffea6243b6b600 0xfffff31f1ffff801 0xfffffe63e3ffff00

def z287 : W := mkw 0x01001203004040e0 0x202002406008081c 0x00003007000001c4 0x00000600e0000038

def z288 : W := mkw 0x258016a0036804b0 0x44b002d4006d0096 0xaf800fe00ff8063b 0x75f001fc01ff00c7

def z289 : W := mkw 0x0102131b00424ae8 0x202042636008495d 0xb700331f11c007ff 0xf6e00663e23800ff

def z290 : W := mkw 0x985aed7cfe1f1f18 0x930b5daf9fc3e3e3 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z291 : W := mkw 0x0008400004141000 0x0001080000828200 0x0899c0000e380000 0x0113380001c70000

def z292 : W := mkw 0x7cd1000019210001 0x0f9a200003242000 0x0000000000000000 0x0000000000000000

def z293 : W := mkw 0x7ffd7eadbffff7f1 0xcfffafd5b7fffefe 0xffffffffffffffff 0xffffffffffffffff

def z294 : W := mkw 0x0102131b00424ae8 0x202042636008495d 0xd060331f1007c7ff 0xba0c0663e200f8ff

def z295 : W := mkw 0x8102bff8624a0fb8 0x502057ff0c4941f7 0x00003ff8e00007fe 0x200007ff1c0000ff

def z296 : W := mkw 0x18082c093e074740 0x8301058127c0e8e8 0x98003c001e07c7c5 0xb300078003c0f8f8

def z297 : W := mkw 0x01003a8680000002 0x00200750d0000000 0x0000300700000000 0x00000600e0000000

def z298 : W := mkw 0x1fa63b9200000000 0x03f4c77240000000 0x5fe63fff00000001 0xebfcc7ffe0000000

def z299 : W := mkw 0x5ff73b9680000002 0x0bfee772d0000000 0x5766331f00000001 0xeaecc663e0000000

def z300 : W := mkw 0x0002857042080410 0x000050ae08410082 0xe89fcff8ee38063b 0x7d13f9ff1dc700c7

def z301 : W := mkw 0x42778156c0000002 0x084ef02ad8000000 0x48ffcfffe0000001 0x691ff9fffc000000

def z302 : W := mkw 0x0008400004141000 0x0001080000828200 0x401fc00000063800 0x0803f8000000c700

def z303 : W := mkw 0x0102131200000000 0x0020426240000000 0x0000331f00000000 0x20000663e0000000

def z304 : W := mkw 0x8008400824161a08 0x100108010482c341 0x0000000000063800 0x000000000000c700

def z305 : W := mkw 0x427fc156c495b003 0x084ff82ad892b600 0x407fc01fe007f800 0x080ff803fc00ff00

def z306 : W := mkw 0x1d803ea002080410 0x03b007d400410082 0xbf803fe00e38063b 0xf7f007fc01c700c7

def z307 : W := mkw 0x437f531b04d7fae9 0x286fea63609aff5d 0xf77ff31f11c7ffff 0xfeeffe63e238ffff

def z308 : W := mkw 0x7efd40091db7f241 0x0fdfa80123b6fe48 0xfffff01f1fffffc5 0xfffffe03e3fffff8

def z309 : W := mkw 0x7ff7bfffdbeaeffa 0x6ffef7fffb7d5dff 0xffffffffffffffff 0xffffffffffffffff

def z310 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xa087c3e00e3e3e3a 0x5410f87c01c7c7c7

def z311 : W := mkw 0x7fa7bff25b6805b2 0x4ff4f7fe4b6d00b6 0xbf87ffe01ff807ff 0xf7f0fffc03ff00ff

def z312 : W := mkw 0x00582c0da6074740 0x800b0581b4c0e8e8 0x40783c1fe007c7c4 0x280f0783fc00f8f8

def z313 : W := mkw 0x38002c201b6805b0 0x47000584036d00b6 0xb8003c001ff807ff 0xb700078003ff00ff

def z314 : W := mkw 0x8326d37b40dafaf8 0x3064da6f681b5f5f 0xf7e7f3ff11ffffff 0xfefcfe7fe23fffff

def z315 : W := mkw 0x3fa6131b19e2eae8 0x27f4c263633c5d5d 0xffe6331f1fffffff 0xfffcc663e3ffffff

def z316 : W := mkw 0x5ff7bff6c2080412 0x0bfef7fed8410082 0xffffffffee38063b 0xfffffffffdc700c7

def z317 : W := mkw 0x1850000000000000 0x030a000000000000 0x5878000000000001 0x8b0f000000000000

def z318 : W := mkw 0x1852a954c0000000 0x030a552a98000000 0x58ffffffe0000001 0xeb1ffffffc000000

def z319 : W := mkw 0x7effc156ddb5b003 0x0fdff82adbb6b600 0xffffc01ffffff801 0xdffff803ffffff00

def z320 : W := mkw 0x00084420061c1410 0x0001088400c38282 0xe89fcfe00e3e3e3b 0x7d13f9fc01c7c7c7

def z321 : W := mkw 0xc27fc578669fbe19 0x184ff8af0cd3f7c3 0xe8ffcff8ee3ffe3b 0x7d1ff9ff1dc7ffc7

def z322 : W := mkw 0x427d40000495b001 0x084fa8000092b600 0xe8ffc0000e3ff801 0x5d1ff80001c7ff00

def z323 : W := mkw 0x0002011000000000 0x0000402200000000 0x4006031800000001 0x6800c06300000000

def z324 : W := mkw 0x0058000004050000 0x000b00000080a000 0x407800000007c000 0x080f00000000f800

def z325 : W := mkw 0x800ac15864161a08 0x1001582b0c82c341 0xe89fc018ee3e3801 0x5d13f8031dc7c700

def z326 : W := mkw 0x0000000900024240 0x0000000120004848 0x4060001f0007c000 0x080c0003e000f800

def z327 : W := mkw 0x7fff53121df5b8a9 0x2fffea6243beb715 0xffffc3001ffff83b 0xdffff86003ffff07

def z328 : W := mkw 0x0100120000000000 0x0020024000000000 0x1700330000000001 0xe2e0066000000000

def z329 : W := mkw 0x4059400004151001 0x080b28000082a200 0x0019c00000000000 0x0003380000000000

def z330 : W := mkw 0x427f411b0497fa49 0x284fe8236092ff49 0x407fc01f0007f800 0x080ff803e000ff00

def z331 : W := mkw 0x0000002000080010 0x0000000400010002 0x208003e00038003a 0x4410007c00070007

def z332 : W := mkw 0x7fa57ea01bf8b5b1 0x4ff4afd4037f16b6 0xbf87ffe01ff83fff 0xf7f0fffc03ff07ff

def z333 : W := mkw 0x0000400000101000 0x0000080000020200 0x2087c00000383800 0x4410f80000070700

def z334 : W := mkw 0x1fa63b9b00c2eae8 0x23f4c77360185d5d 0xffe63fff11c7ffff 0xfffcc7ffe238ffff

def z335 : W := mkw 0x3d887ea01f7c15b0 0x47b10fd403ef82b6 0xff9fffe01ffe3fff 0xfff3fffc03ffc7ff

def z336 : W := mkw 0x8326977b62caeef8 0x3064d2ef6c595ddf 0xf7663ffff1c7ffff 0xfeecc7fffe38ffff

def z337 : W := mkw 0x5cd9acc4fe050502 0x8b9b35989fc0a0a0 0x0899cce0ee000000 0x0113399c1dc00000

def z338 : W := mkw 0x5ff53a8798014142 0x8bfea750f3002828 0x176030071001c1c4 0x82ec0600e2003838

def z339 : W := mkw 0x1b763b1f98c3ebe8 0xa36ec763f3187d7d 0xf766331f11c7ffff 0xfeecc663e238ffff

def z340 : W := mkw 0x0102131800420aa8 0x0020426300084155 0xf706331811c63fff 0xfee0c6630238c7ff

def z341 : W := mkw 0x7efd400dbdb7f241 0x8fdfa801b7b6fe48 0xffffc01ffffff801 0xdffff803ffffff00

def z342 : W := mkw 0x0002011900024a48 0x0000402320004949 0xf066331f1007ffff 0xfe0cc663e200ffff

def z343 : W := mkw 0x7cd96c0dbf375741 0x8f9b2d81b7e6eae8 0xd8f9fc1ffe3fc7c5 0xbb1f3f83ffc7f8f8

def z344 : W := mkw 0x00002c0002000500 0x00000580004000a0 0x00003c00000007c4 0x20000780000000f8

def z345 : W := mkw 0xdff7fbf6c018181a 0x1bfeff7ed8030303 0x7fffffffe038383b 0xeffffffffc070707

def z346 : W := mkw 0x7ef5400001b0b001 0x0fdea80000361600 0x7fffc00001f83801 0xcffff800003f0700

def z347 : W := mkw 0x3dd83e8dbf6747e0 0xc7bb07d1b7ece8fc 0xdf783c1fffc7c7c5 0xbbef0783fff8f8f8

def z348 : W := mkw 0xdeffc578661e1e18 0x1bdff8af0cc3c3c3 0xffffcff8ee3e3e3b 0xfffff9ff1dc7c7c7

def z349 : W := mkw 0x7ef5000019a1a001 0x0fdea00003343400 0xbfe000001ff9c001 0xd7fc000003ff3800

def z350 : W := mkw 0x3c80288019200100 0x4790051003240020 0x0000000000000000 0x0000000000000000

def z351 : W := mkw 0x0000000900424ae8 0x200000012008495d 0x00000000000007fe 0x00000000000000ff

def z352 : W := mkw 0x20000000196001a0 0x44000000032c0034 0x0000000011c001c4 0x0000000002380038

def z353 : W := mkw 0x0000000900024240 0x0000000120004848 0x800000001007c7c4 0x100000000200f8f8

def z354 : W := mkw 0x7cd940001d351001 0x0f9b280003a6a200 0xd8f9c0001e3fc001 0x9b1f380003c7f800

def z355 : W := mkw 0x47a5128200000002 0x08f4a25040000000 0x0700000000000000 0x00e0000000000000

def z356 : W := mkw 0x47a793d240000002 0x08f4f27a48000000 0x57e7f3ff00000001 0xeafcfe7fe0000000

def z357 : W := mkw 0x0326131a00c2aaa8 0x2064c26340185555 0xe706031801c63e3b 0x7ce0c0630038c7c7

def z358 : W := mkw 0x01001200004000a0 0x0020024000080014 0x2700030001c0003a 0x44e0006000380007

def z359 : W := mkw 0x0000000800020a08 0x0000000100004141 0xa000000000063e3a 0x140000000000c7c7

def z360 : W := mkw 0x5ef5280480000000 0x0bdea50090000000 0x5ffffc1fe0000001 0xebffff83fc000000

def z361 : W := mkw 0x0226011b0082ea48 0x2044c02360105d49 0xe066031f0007fe3b 0x7c0cc063e000ffc7

def z362 : W := mkw 0x5ff73b9f80c2eaea 0x2bfee773f0185d5d 0xf766331f11c7ffff 0xfeecc663e238ffff

def z363 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0x2f800fe00ff8003a 0x45f001fc01ff0007

def z364 : W := mkw 0x43779356c0000002 0x086ef26ad8000000 0x577ff31fe0000001 0xeaeffe63fc000000

def z365 : W := mkw 0x1850000018010000 0x030a000003002000 0x106000001001c000 0x820c000002003800

def z366 : W := mkw 0x80084428261e1e18 0x1001088504c3c3c3 0xe8180c18ee3e3e3b 0x3d0301831dc7c7c7

def z367 : W := mkw 0x67a7531b01f2fae9 0x2cf4ea63603e5f5d 0xf7e7f31f11ffffff 0xfefcfe63e23fffff

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0xb700000011c00001 0xd6e0000002380000

def z369 : W := mkw 0x5ff7131200000000 0x0bfee26240000000 0x5ffff31f00000001 0xebfffe63e0000000

def z370 : W := mkw 0x0000040922024740 0x80000081244048e8 0x00000000000007c4 0x00000000000000f8

def z371 : W := mkw 0x03263f1fa2c2efe8 0xa064c7e3f4585dfd 0xf7663f1ff1c7ffff 0xfeecc7e3fe38ffff

def z372 : W := mkw 0x0324120b00c2eae8 0x2064824160185d5d 0xb760300711c7fffe 0x96ec0600e238ffff

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0xd06000001007c001 0x9a0c00000200f800

def z374 : W := mkw 0x8326d37240d8b8b8 0x3064da6e481b1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z375 : W := mkw 0x8002c15040101808 0x1000582a08020301 0x0007c00000003800 0x0000f80000000700

def z376 : W := mkw 0x01003a80004001a0 0x4020075000080034 0x00003000000001c4 0x0000060000000038

def z377 : W := mkw 0x1b263f1b1ac2efe8 0x2364c7e363585dfd 0xff663f1f1fc7ffff 0xffecc7e3e3f8ffff

def z378 : W := mkw 0x5fa7bbd240000002 0x0bf4f77a48000000 0x1f87ffe000000001 0xe3f0fffc00000000

def z379 : W := mkw 0x985aed5dfe175f48 0x930b5dabbfc2ebe9 0xd87ffc1ffe07ffc5 0xbb0fff83ffc0fff8

def z380 : W := mkw 0xdff7bffee20a0e1a 0x1bfef7ffdc4141c3 0x5fffffffe000063b 0xebfffffffc0000c7

def z381 : W := mkw 0x1b743a0798c1e1e0 0xa36e8740f3183c3c 0x1760300711c1c1c4 0x82ec0600e2383838

def z382 : W := mkw 0x200804293f6f47f0 0xc401008527ede8fe 0xa00000001fffc7fe 0x1400000003fff8ff

def z383 : W := mkw 0x9858ec64fe1d1510 0x930b1d8c9fc3a2a2 0x0899cce0ee380000 0x0113399c1dc70000

def z384 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0x577fc00011c7f800 0x8aeff8000238ff00

def z385 : W := mkw 0x18502c059a014540 0x830a0580b34028a8 0x98603c071e01c7c5 0xb30c0780e3c038f8

def z386 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xb70030001ff807fe 0x96e0060003ff00ff

def z387 : W := mkw 0x0324120300c0e0e0 0x2064824060181c1c 0xf766300711c7f9c5 0xdeecc600e238ff38

def z388 : W := mkw 0x1dd03a8480000000 0x03ba075090000000 0x5ff83fffe0000001 0xebff07fffc000000

def z389 : W := mkw 0x032e171b26c6eee8 0x2065c2e364d8dddd 0xff7e3f1fffc7ffff 0xffefc7e3fff8ffff

def z390 : W := mkw 0x627d40001db5b001 0x0c4fa80003b6b600 0xe07fc0001ffff800 0x1c0ff80003ffff00

def z391 : W := mkw 0x67a7d3d241b0b003 0x0cf4fa7a48361600 0x2787c3e001f83800 0x44f0f87c003f0700

def z392 : W := mkw 0x00580004a4050000 0x800b00009480a000 0x00180000e0000000 0x000300001c000000

def z393 : W := mkw 0xbddafffdff7f5ff8 0xd7bb5fffbfefebff 0xffffffffffffffff 0xffffffffffffffff

def z394 : W := mkw 0x7cd9e8c4dd351003 0x0f9b3d189ba6a200 0x0899cce0ee380000 0x0113399c1dc70000

def z395 : W := mkw 0x01001200004000a0 0x0020024000080014 0x1700300011c001c4 0x82e0060002380038

def z396 : W := mkw 0x0226011b0082ea48 0x2044c02360105d49 0xd066301f1007ffc5 0xba0cc603e200fff8

def z397 : W := mkw 0x232e531b1df7fae9 0x2465ca6363beff5d 0xf766331f1fffffff 0xfeecc663e3ffffff

def z398 : W := mkw 0x0008400004141000 0x0001080000828200 0xa00000000e3e3800 0x1400000001c7c700

def z399 : W := mkw 0x0000000100004040 0x0000000020000808 0x106030071001c1c4 0x820c0600e2003838

def z400 : W := mkw 0x0002815040000000 0x0000502a08000000 0x0087c3e000000000 0x4010f87c00000000

def z401 : W := mkw 0x1d803a8000000000 0x03b0075000000000 0x1700300000000000 0x82e0060000000000

def z402 : W := mkw 0x7ff53a86996001a2 0x4ffea750d32c0034 0x1760300711c001c4 0x82ec0600e2380038

def z403 : W := mkw 0x18582c2dbe0f4750 0x830b0585b7c1e8ea 0xf8f83ffffe3fc7ff 0xff1f07ffffc7f8ff

def z404 : W := mkw 0x000a051826060e08 0x000140a304c0c1c1 0xe81e0f18ee063e3b 0x7d03c1e31dc0c7c7

def z405 : W := mkw 0x1850280498010100 0x830a050093002020 0x0000000000000000 0x0000000000000000

def z406 : W := mkw 0x5a7d40001c95b001 0x0b4fa8000392b600 0xd87fc0001e07f801 0x9b0ff80003c0ff00

def z407 : W := mkw 0x0326131200c0a8a8 0x2064c26240181515 0x7766331f01c0383b 0xeeecc663e0380707

def z408 : W := mkw 0x7efd44083fb7b601 0x0fdfa88107f6f6c0 0xffffcc18fffffe01 0xfffff9831fffffc0

def z409 : W := mkw 0xa00844283f7e1fb8 0x5401088507efc3f7 0xa00000001ffe3ffe 0x1400000003ffc7ff

def z410 : W := mkw 0x01003ea0024805b0 0x402007d4004900b6 0xa8803fe00e3807ff 0x751007fc01c700ff

def z411 : W := mkw 0x5fffbfdffec7efea 0xabfff7fbffd8fdfd 0xffffffffffc7ffff 0xfffffffffff8ffff

def z412 : W := mkw 0x5ff7bbd7c0c0e0e2 0x2bfef77af8181c1c 0x5ffffffff1c1c1c5 0xebfffffffe383838

def z413 : W := mkw 0x032e531b04d6fae8 0x2065ca63609adf5d 0xfffff31f1fffffff 0xfffffe63e3ffffff

def z414 : W := mkw 0x9b7eff7ffedffff8 0xb36fdfefffdbffff 0xffffffffffffffff 0xffffffffffffffff

def z415 : W := mkw 0x2326173b1beaeff8 0x6464c2e7637d5dff 0xf766331f1fffffff 0xfeecc663e3ffffff

def z416 : W := mkw 0x00000420024805b0 0x40000084004900b6 0x00000000000007fe 0x00000000000000ff

def z417 : W := mkw 0x18082c083e060700 0x0301058107c0c0e0 0xd8183c18fe0607c5 0xbb0307831fc0c0f8

def z418 : W := mkw 0x3dd03ea49b6805b0 0x47ba07d4936d00b6 0xfff83ffffff807ff 0xffff07ffffff00ff

def z419 : W := mkw 0x0058040da6074640 0x800b0081b4c0e8c8 0xc8780c1fee07c601 0x390f0183fdc0f8c0

def z420 : W := mkw 0x5efd2c0dbe074740 0x8bdfa581b7c0e8e8 0xdffffc1ffe07c7c5 0xfbffff83ffc0f8f8

def z421 : W := mkw 0x7effc1505db5b001 0x0fdff82a0bb6b600 0xffffcff8fffff801 0xfffff9ff1fffff00

def z422 : W := mkw 0x5a77a956c0000002 0x0b4ef52ad8000000 0x587ffc1fe0000001 0xab0fff83fc000000

def z423 : W := mkw 0xc7afd7fa661e1e1a 0x18f5faff4cc3c3c3 0xef9fcff8ee3e3e3b 0x7df3f9ff1dc7c7c7

def z424 : W := mkw 0x0324120200c0a0a0 0x2064824040181414 0x0700000001c00000 0x00e0000000380000

def z425 : W := mkw 0x8008c04064141000 0x100118080c828200 0x0019c000e0000000 0x000338001c000000

def z426 : W := mkw 0x822ec578669ebe18 0x1045d8af0cd3d7c3 0xffffcff8fffffe3b 0xfffff9ff1fffffc7

def z427 : W := mkw 0x022400030080e040 0x2044800060101c08 0x006000070001c000 0x000c0000e0003800

def z428 : W := mkw 0x0326131200c0a8a8 0x2064c26240181515 0xb706330011c03fff 0xf6e0c660023807ff

def z429 : W := mkw 0x000800001c050000 0x000100000380a000 0x800000001e07c000 0x1000000003c0f800

def z430 : W := mkw 0x47a7bbd6c0000002 0x08f4f77ad8000000 0x0787ffffe0000000 0x60f0fffffc000000

def z431 : W := mkw 0x38582c2dbf6f47f0 0xc70b0585b7ede8fe 0xf8783c1fffffc7ff 0xbf0f0783fffff8ff

def z432 : W := mkw 0x800ac570661c1410 0x100158ae0cc38282 0x489fcff8ee380001 0x6913f9ff1dc70000

def z433 : W := mkw 0x3d801200196000a0 0x07b00240032c0014 0xbf8033001ff807ff 0xf7f0066003ff00ff

def z434 : W := mkw 0x47a793db40c2eaea 0x28f4f27b68185d5d 0xf7e7f3ff11c7ffff 0xfefcfe7fe238ffff

def z435 : W := mkw 0x5efd00001c050000 0x0bdfa0000380a000 0xdfffc0001e07c001 0xdbfff80003c0f800

def z436 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x08183c1fee0007c4 0x21030783fdc000f8

def z437 : W := mkw 0x0000040002000400 0x0000008000400080 0x88000c000e000601 0x3100018001c000c0

def z438 : W := mkw 0x0000040822020600 0x00000081044040c0 0x00000c18e0000600 0x200001831c0000c0

def z439 : W := mkw 0x4377935fc0c2eaea 0x286ef26bf8185d5d 0xf77ff31ff1c7ffff 0xfeeffe63fe38ffff

def z440 : W := mkw 0x80084428261e1e18 0x1001088504c3c3c3 0xe89fc0000e3e3e3b 0x5d13f80001c7c7c7

def z441 : W := mkw 0x18582c0ca6060600 0x030b058194c0c0c0 0xd8783c1fee060601 0xbb0f0783fdc0c0c0

def z442 : W := mkw 0xc27fc15ee4161a0a 0x184ff82bdc82c341 0x407fc01fe0063800 0x080ff803fc00c700

def z443 : W := mkw 0x0008040826060600 0x0001008104c0c0c0 0x800000000e060600 0x1000000001c0c0c0

def z444 : W := mkw 0xbd887ea83f7e1fb8 0x57b10fd507efc3f7 0xbf803fe01ffe3fff 0xf7f007fc03ffc7ff

def z445 : W := mkw 0x3dd83ea01f6d05b0 0x47bb07d403eda0b6 0xfff83fe01fffc7ff 0xffff07fc03fff8ff

def z446 : W := mkw 0x1d82bbd040000000 0x03b0577a08000000 0x5f9ffff8e0000001 0xebf3ffff1c000000

def z447 : W := mkw 0x7ffd7a869db5b003 0x0fffaf50d3b6b600 0xfffff0071ffff801 0xdffffe00e3ffff00

def z448 : W := mkw 0x8000c06040181010 0x1000180c08030202 0x0081c0e000380000 0x0010381c00070000

def z449 : W := mkw 0x7ff7bbf6c16800b2 0x4ffef77ed82d0016 0x7fffffffe1f8003b 0xeffffffffc3f0007

def z450 : W := mkw 0x800ac170441c1818 0x1001582e08838303 0xe89fc3e00e3e383b 0x5d13f87c01c7c707

def z451 : W := mkw 0x80028578620a0e18 0x100050af0c4141c3 0xa8800ff8ee38063b 0x751001ff1dc700c7

def z452 : W := mkw 0x0224000900c2eae8 0x2044800120185d5d 0xf766000011c7ffff 0xdeecc0000238ffff

def z453 : W := mkw 0x0002815040000000 0x0000502a08000000 0x00000ff8e0000000 0x200001ff1c000000

def z454 : W := mkw 0x0008040026040400 0x0001008004c08080 0x08180c00ee000000 0x010301801dc00000

def z455 : W := mkw 0x427f815fe4074242 0x884ff02bfc80e848 0x407fc01fe007c000 0x080ff803fc00f800

def z456 : W := mkw 0xfeffed7dffbfff59 0x9fdffdafbff7ffeb 0xffffffffffffffff 0xffffffffffffffff

def z457 : W := mkw 0x800a8578660e0e18 0x100150af0cc1c1c3 0xc8180ff8ee06063b 0x390301ff1dc0c0c7

def z458 : W := mkw 0x5fffbfdee6060602 0x0bfff7fbdcc0c0c0 0xdfffffffee060601 0xfbfffffffdc0c0c0

def z459 : W := mkw 0x5a7fad5ffe074742 0x8b4ff5abffc0e8e8 0xd87ffc1ffe07c7c5 0xbb0fff83ffc0f8f8

def z460 : W := mkw 0x01003ea0024805b0 0x402007d4004900b6 0xb7003fe011c007ff 0xf6e007fc023800ff

def z461 : W := mkw 0x3fa43ea31be8e5f0 0x67f487d4637d1cbe 0xbfe03fe71ff9c7ff 0xf7fc07fce3ff38ff

def z462 : W := mkw 0xbd82fff05b781db8 0x57b05ffe0b6f03b7 0xbf87ffe01ff83fff 0xf7f0fffc03ff07ff

def z463 : W := mkw 0x7cd1ace4db280512 0x4f9a359c9b6500a2 0x0899cce0ee380000 0x0113399c1dc70000

def z464 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0x48ffc0000e3ff800 0x091ff80001c7ff00

def z465 : W := mkw 0x805ac15de4175a48 0x900b582bbc82eb49 0x407fc01fe007f800 0x080ff803fc00ff00

def z466 : W := mkw 0x5efd400004141000 0x0bdfa80000828200 0xffffc0000e3e3801 0xdffff80001c7c700

def z467 : W := mkw 0x7efd2c0dbfa7e741 0x8fdfa581b7f4fce8 0xdf783c1fffc7c7c5 0xbbef0783fff8f8f8

def z468 : W := mkw 0x222c40001db5b001 0x0445880003b6b600 0xf76600001ffff801 0xdeecc00003ffff00

def z469 : W := mkw 0x18582c001e050500 0x030b058003c0a0a0 0xd8783c001e07c7c5 0xbb0f078003c0f8f8

def z470 : W := mkw 0xdffffbdee4161a0a 0x1bffff7bdc82c341 0x5fffffffe0063801 0xebfffffffc00c700

def z471 : W := mkw 0xdcdbedfce61e1e1a 0x1b9b7dbf9cc3c3c3 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z472 : W := mkw 0x19003ea01a4805b0 0x432007d4034900b6 0x98003fe01e0007ff 0xb30007fc03c000ff

def z473 : W := mkw 0x0002815040000000 0x0000502a08000000 0x401fc018e0000000 0x0803f8031c000000

def z474 : W := mkw 0x7fff7f1fbff7ffe9 0xafffefe3f7fefffd 0xffffff1fffffffff 0xffffffe3ffffffff

def z475 : W := mkw 0x5ff7bfd6da000502 0x0bfef7fadb4000a0 0xdffffffffe0007c5 0xfbffffffffc000f8

def z476 : W := mkw 0x7cd96c04bf351501 0x8f9b2d8097e6a2a0 0x0899cc00ee380000 0x011339801dc70000

def z477 : W := mkw 0x1b763b1680000000 0x036ec762d0000000 0x5f7e3f1fe0000001 0xebefc7e3fc000000

def z478 : W := mkw 0x7ffffbdfddf7faeb 0x2fffff7bfbbeff5d 0xffffffffffffffff 0xffffffffffffffff

def z479 : W := mkw 0x5ff7bff6c24805b2 0x4bfef7fed84900b6 0x5fffffffe00007ff 0xebfffffffc0000ff

def z480 : W := mkw 0x7ef5280599a1e141 0x8fdea500b3343c28 0x1760300711c1c1c4 0x82ec0600e2383838

def z481 : W := mkw 0x8002815860020a08 0x1000502b0c004141 0x00000018e0000000 0x000000031c000000

def z482 : W := mkw 0x8002c578621a1e18 0x100058af0c4343c3 0x2087cff8e0383e3a 0x6410f9ff1c0707c7

def z483 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x906030071e07c7c4 0x920c0600e3c0f8f8

def z484 : W := mkw 0x3ffe3fbfbfefeff8 0xe7ffc7f7f7fdfdff 0xfffe3fffffffffff 0xffffc7ffffffffff

def z485 : W := mkw 0x3dd83ea4bf6d05b0 0xc7bb07d497eda0b6 0xbf983fe0fff807ff 0xf7f307fc1fff00ff

def z486 : W := mkw 0x1850280480000000 0x030a050090000000 0x08180c00e0000000 0x010301801c000000

def z487 : W := mkw 0x46a5000000000000 0x08d4a00000000000 0x0787c00000000000 0x40f0f80000000000

def z488 : W := mkw 0x18502c049a000500 0x030a0580934000a0 0xd8783c1ffe0007c5 0xbb0f0783ffc000f8

def z489 : W := mkw 0x7ea5400019b0b001 0x0fd4a80003361600 0xbf87c0001ff83801 0xd7f0f80003ff0700

def z490 : W := mkw 0x0100120900c2eae8 0x2020024120185d5d 0xb700330011c7ffff 0xf6e006600238ffff

def z491 : W := mkw 0x67a552a001f8b0b1 0x4cf4aa54003f1616 0x2787c3e001f8383a 0x44f0f87c003f0707

def z492 : W := mkw 0x980aed787e1e1f18 0x13015daf0fc3c3e3 0xf89ffff8fe3e3fff 0xff13ffff1fc7c7ff

def z493 : W := mkw 0x1952bbd6c0000002 0x032a577ad8000000 0x58783fffe0000001 0xab0f07fffc000000

def z494 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0x401fcff8e0063e3a 0x2803f9ff1c00c7c7

def z495 : W := mkw 0x0000280580004140 0x80000500b0000828 0x00003007000001c4 0x00000600e0000038

def z496 : W := mkw 0x7ff7131b19e3eae9 0x2ffee263633c7d5d 0xf766331f11c7ffff 0xfeecc663e238ffff

def z497 : W := mkw 0x185828059c054140 0x830b0500b380a828 0xd87830071e07c1c5 0x9b0f0600e3c0f838

def z498 : W := mkw 0xa00844283fbfbe19 0x1401088507f7f7c3 0xa00000001ffffe3a 0x1400000003ffffc7

def z499 : W := mkw 0x185a2d1dbe074f48 0x830b45a3b7c0e9e9 0xf87e3f1ffe07ffff 0xff0fc7e3ffc0ffff

def z500 : W := mkw 0x037e131fa4c7eae8 0xa06fc263f498fd5d 0xf77e331ff1c7ffff 0xfeefc663fe38ffff

def z501 : W := mkw 0x832e573b26defef8 0x3065cae764dbdfdf 0xf766331f1fffffff 0xfeecc663e3ffffff

def z502 : W := mkw 0x3c802c001b200500 0x07900580036400a0 0xbf803c001ff807c5 0xf7f0078003ff00f8

def z503 : W := mkw 0x7cd96ca01f3d1511 0x4f9b2d9403e7a2a2 0x0899cce00e380000 0x0113399c01c70000

def z504 : W := mkw 0x5ef7815040000000 0x0bdef02a08000000 0x5fffcff8e0000001 0xebfff9ff1c000000

def z505 : W := mkw 0x66a5400001b0b001 0x0cd4a80000361600 0xf7e7c00011fff801 0xdefcf800023fff00

def z506 : W := mkw 0x1b763b1f80c2eae8 0x236ec763f0185d5d 0xff7e3f1ff1c7ffff 0xffefc7e3fe38ffff

def z507 : W := mkw 0x7efd44201ffdb5b1 0x4fdfa88403ffb6b6 0xffffc0001fffffff 0xdffff80003ffffff

def z508 : W := mkw 0x3c8840001db5b001 0x0791080003b6b600 0xbf8000001ffff801 0xd7f0000003ffff00

def z509 : W := mkw 0x3d82bff6db6805b2 0x47b057fedb6d00b6 0xbf803ffffff807ff 0xf7f007ffffff00ff

def z510 : W := mkw 0x80084420261c1410 0x1001088404c38282 0x000000000e380000 0x0000000001c70000

def z511 : W := mkw 0xbc8ac5787f3e1e18 0x179158af0fe7c3c3 0xff9fcff8fffe3e3b 0xfff3f9ff1fffc7c7

def z512 : W := mkw 0x185804093e074740 0x830b008127c0e8e8 0xd87800001e07c7c5 0x9b0f000003c0f8f8

def z513 : W := mkw 0x258016a01b6805b0 0x44b002d4036d00b6 0xa78003e01ff807fe 0x54f0007c03ff00ff

def z514 : W := mkw 0x3d803ea01b280510 0x47b007d4036500a2 0x1f803fe00e380001 0xe3f007fc01c70000

def z515 : W := mkw 0x7efd6c001fb5b501 0x0fdfad8003f6b6a0 0xfffffc001fffffc5 0xffffff8003fffff8

def z516 : W := mkw 0x4227815240000002 0x0844f02a48000000 0x0007c00000000000 0x0000f80000000000

def z517 : W := mkw 0x18582c0cbe070700 0x830b058197c0e0e0 0xc8180c18ee060601 0x390301831dc0c0c0

def z518 : W := mkw 0x3d823fbb1b6a4ff8 0x67b047f7636d49ff 0xbf803fff1ff807ff 0xf7f007ffe3ff00ff

def z519 : W := mkw 0x000840000495b001 0x000108000092b600 0x000000000007f800 0x000000000000ff00

def z520 : W := mkw 0xfffffffeff7e1fba 0x5fffffffdfefc3f7 0xfffffffffffe3fff 0xffffffffffffc7ff

def z521 : W := mkw 0x3c8004201b6805b0 0x47900084036d00b6 0xbf8000001ff807ff 0xd7f0000003ff00ff

def z522 : W := mkw 0x18502c0da2024740 0x830a0581b44048e8 0x58783c1fe00007c5 0xab0f0783fc0000f8

def z523 : W := mkw 0x0000000000c0a8a8 0x2000000000181515 0x2000000001c0383a 0x0400000000380707

def z524 : W := mkw 0x5cd3a9d4c0000002 0x0b9a753a98000000 0x489fcff8e0000001 0x6913f9ff1c000000

def z525 : W := mkw 0x9d8afff8661e1e18 0x13b15fff0cc3c3c3 0xff9ffff8ee3e3e3b 0xfff3ffff1dc7c7c7

def z526 : W := mkw 0x3c802ca01b6805b0 0x47900594036d00b6 0xa8800ce01ff807fe 0x1510019c03ff00ff

def z527 : W := mkw 0x1a7c2c0dbe87e740 0x834f8581b7d0fce8 0xff7e3c1fffc7ffc5 0xffefc783fff8fff8

def z528 : W := mkw 0x7efd6c04bfb5b501 0x8fdfad8097f6b6a0 0xffffcc00fffff801 0xdffff9801fffff00

def z529 : W := mkw 0x03261312004000a0 0x0064c26240080014 0xf766331f11c007ff 0xfeecc663e23800ff

def z530 : W := mkw 0x5ff7bbdfc0024242 0x0bfef77bf8004848 0xdffffffff007c7c5 0xfbfffffffe00f8f8

def z531 : W := mkw 0x1c80000000000000 0x0390000000000000 0x1f80000000000001 0xc3f0000000000000

def z532 : W := mkw 0xc27fc57ee61e1e1a 0x184ff8afdcc3c3c3 0xe8ffcfffee3e3e3b 0x7d1ff9fffdc7c7c7

def z533 : W := mkw 0xa582d3f0417818b8 0x54b05a7e082f0317 0x2787c3e001f8383a 0x44f0f87c003f0707

def z534 : W := mkw 0xbc8aedf87f3e1f18 0x57915dbf0fe7c3e3 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z535 : W := mkw 0x0000280480000000 0x0000050090000000 0x00003c1fe0000000 0x20000783fc000000

def z536 : W := mkw 0x1c80288000000000 0x0390051000000000 0x08800ce000000000 0x0110019c00000000

def z537 : W := mkw 0xdcd9ece4e61c1412 0x1b9b3d9c9cc38282 0x0899cce0ee380000 0x0113399c1dc70000

def z538 : W := mkw 0x0002011800020a08 0x0000402300004141 0x000003180000063a 0x20000063000000c7

def z539 : W := mkw 0x25801280016000a0 0x44b00250002c0014 0x0700000001c00000 0x00e0000000380000

def z540 : W := mkw 0x427d400da497f241 0x884fa801b492fe48 0x407fc01fe007f800 0x080ff803fc00ff00

def z541 : W := mkw 0x5a7d6c0dbe97f741 0x8b4fad81b7d2fee8 0xd87ffc1ffe07ffc5 0xbb0fff83ffc0fff8

def z542 : W := mkw 0x3fa63fb21be8adb8 0x67f4c7f6437d15b7 0xbf863fe01ff83fff 0xf7f0c7fc03ff07ff

def z543 : W := mkw 0x810ad778665e1eb8 0x10215aef0ccbc3d7 0xff9ffff8fffe3fff 0xfff3ffff1fffc7ff

def z544 : W := mkw 0x195a3f1fbe474fe8 0xa32b47e3f7c8e9fd 0xd8783f1ffe07c7ff 0xbb0f07e3ffc0f8ff

def z545 : W := mkw 0x3d803a80196001a0 0x47b00750032c0034 0xb700330011c007ff 0xf6e00660023800ff

def z546 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0x2706331f01c03ffe 0x64e0c663e03807ff

def z547 : W := mkw 0x19583eadbe4f47f0 0xc32b07d5b7c9e8fe 0xd8783ffffe07c7ff 0xbb0f07ffffc0f8ff

def z548 : W := mkw 0x38586c0dbfb7f741 0x870b0d81b7f6fee8 0xf8783c1fffffffc5 0xbf0f0783fffffff8

def z549 : W := mkw 0x7eff41181db7ba09 0x0fdfe82303b6f741 0xffffc3181ffffe3b 0xfffff86303ffffc7

def z550 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0x4066331f0007fffe 0x280cc663e000ffff

def z551 : W := mkw 0x01021312004008a8 0x2020426240080115 0x000003000000003a 0x0000006000000007

def z552 : W := mkw 0x7ff7fbd6c1b0b003 0x0ffeff7ad8361600 0x7fffffffe1f83801 0xeffffffffc3f0700

def z553 : W := mkw 0xdfffffffe6defefa 0x3bfffffffcdbdfdf 0xffffffffffffffff 0xffffffffffffffff

def z554 : W := mkw 0x18582c04be050500 0x830b058097c0a0a0 0xd8780c00fe07c001 0x9b0f01801fc0f800

def z555 : W := mkw 0xa00ac5787f7e1fb8 0x540158af0fefc3f7 0xe89fcff8fffe3fff 0x7d13f9ff1fffc7ff

def z556 : W := mkw 0x0326131300c0e0e0 0x2064c26260181c1c 0x5766331f11c1c1c5 0xeaecc663e2383838

def z557 : W := mkw 0x248000a001280010 0x4490001400250002 0x008000e000380000 0x0010001c00070000

def z558 : W := mkw 0x0000000da0024240 0x80000001b4004848 0x0000001fe0000000 0x00000003fc000000

def z559 : W := mkw 0x5ff5bac6c0000002 0x0bfeb758d8000000 0x1ff9fce7e0000000 0x83ff3f9cfc000000

def z560 : W := mkw 0x5ffd3e8fbe074742 0x8bffa7d1f7c0e8e8 0xdf783c1ffe07c7c5 0xbbef0783ffc0f8f8

def z561 : W := mkw 0x7dd1bee4db6805b2 0x4fba37dc9b6d00b6 0xbf99ffe0fff807ff 0xf7f33ffc1fff00ff

def z562 : W := mkw 0x805ac57de61f5e58 0x900b58afbcc3ebcb 0xe8ffcfffee3ffe3b 0x7d1ff9fffdc7ffc7

def z563 : W := mkw 0x032613120080a000 0x0064c26240101400 0xf766331f11c7f801 0xfeecc663e238ff00

def z564 : W := mkw 0x5ffffbd6c4141002 0x0bffff7ad8828200 0xffffffffee3e3801 0xfffffffffdc7c700

def z565 : W := mkw 0x000804093ec7efe8 0xa001008127d8fdfd 0xa00000001fc7fffe 0x1400000003f8ffff

def z566 : W := mkw 0x1d803ea0024805b0 0x43b007d4004900b6 0x1f803fe0000007ff 0xe3f007fc000000ff

def z567 : W := mkw 0x7ffd52001df5b0a1 0x0fffaa4003beb614 0xfffff3001fffffff 0xfffffe6003ffffff

def z568 : W := mkw 0x3dd03a85996141e0 0xc7ba0750b32c283c 0x1760300711c1c1c4 0x82ec0600e2383838

def z569 : W := mkw 0x7ef5400019b1b001 0x0fdea80003363600 0x37e7c00011f9f800 0xc6fcf800023f3f00

def z570 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0x0899cff8ee38063a 0x211339ff1dc700c7

def z571 : W := mkw 0x8000846062080410 0x1000108c0c410082 0x00000ce0e0000000 0x0000019c1c000000

def z572 : W := mkw 0x8002c17040181818 0x1000582e08030303 0x689fcff8e038383b 0x6d13f9ff1c070707

def z573 : W := mkw 0x00082c0dbe074740 0x80010581b7c0e8e8 0x80003c1ffe07c7c4 0x30000783ffc0f8f8

def z574 : W := mkw 0x5ff53a8680000002 0x0bfea750d0000000 0x5ffff00700000001 0xcbfffe00e0000000

def z575 : W := mkw 0x5fffbfd6fe050502 0x8bfff7fadfc0a0a0 0x5fffffffee000001 0xebfffffffdc00000

def z576 : W := mkw 0x810afff8665e1fb8 0x50215fff0ccbc3f7 0xe89ffff8ee3e3fff 0x7d13ffff1dc7c7ff

def z577 : W := mkw 0x7ff7bbd6d9a1a003 0x0ffef77adb343400 0x5ffffffff1c1c001 0xebfffffffe383800

def z578 : W := mkw 0x0226011b00c2eae8 0x2044c02360185d5d 0xe066001f11c7fffe 0x1c0cc003e238ffff

def z579 : W := mkw 0x67a793f2416800b2 0x4cf4f27e482d0016 0x2787c3e001f8003a 0x44f0f87c003f0007

def z580 : W := mkw 0x0000000800020200 0x0000000100004040 0xc000001800060601 0x380000030000c0c0

def z581 : W := mkw 0x200840001d351001 0x0401080003a6a200 0x000000000e380000 0x0000000001c70000

def z582 : W := mkw 0x1b7c3e0fbec7e7e0 0xa36f87c1f7d8fcfc 0xdf783c1fffc7c7c5 0xbbef0783fff8f8f8

def z583 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xe01fc018ee3e3e3a 0x1c03f8031dc7c7c7

def z584 : W := mkw 0x3d803a80196001a0 0x47b00750032c0034 0xbf8030001ff801c5 0xd7f0060003ff0038

def z585 : W := mkw 0x01003a8000000000 0x0020075000000000 0x00003fe000000000 0x200007fc00000000

def z586 : W := mkw 0xe6a7c17041b8b819 0x1cd4f82e08371703 0x2787c3e001f8383a 0x44f0f87c003f0707

def z587 : W := mkw 0x7ffd52031df5f0e1 0x2fffaa4063bebe1c 0xfffff0071ffff9c5 0xdffffe00e3ffff38

def z588 : W := mkw 0x1d82bbd6c0000002 0x03b0577ad8000000 0x1f803fffe0000001 0xe3f007fffc000000

def z589 : W := mkw 0x832ed77a661e1e18 0x1065daef4cc3c3c3 0xffffffffee3e3e3b 0xfffffffffdc7c7c7

def z590 : W := mkw 0xfcdbc5787f3f1e19 0x1f9b78af0fe7e3c3 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z591 : W := mkw 0x01001209004242e0 0x002002412008485c 0xf760331f11c7c7ff 0xfeec0663e238f8ff

def z592 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0x1760331f11c1c7fe 0xa2ec0663e23838ff

def z593 : W := mkw 0x200004201b280510 0x44000084036500a2 0x000000000e380000 0x0000000001c70000

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x48180c18e0000001 0x290301831c000000

def z595 : W := mkw 0x8102bffee20a0e1a 0x102057ffdc4141c3 0x00003fffe000063a 0x200007fffc0000c7

def z596 : W := mkw 0x7ef5000019a1a001 0x0fdea00003343400 0xf766000011c7f801 0xdeecc0000238ff00

def z597 : W := mkw 0xa58ad7f8677e1eb8 0x54b15aff0cefc3d7 0xef9fcff8effe3e3b 0x7df3f9ff1dffc7c7

def z598 : W := mkw 0x0326173b02caeef8 0x2064c2e760595ddf 0xffe63fff1fffffff 0xfffcc7ffe3ffffff

def z599 : W := mkw 0x5ff7bbdec0020a0a 0x0bfef77bd8004141 0xffffffffe0063e3b 0xfffffffffc00c7c7

def z600 : W := mkw 0xdffffff6e61c1412 0x1bfffffedcc38282 0x5fffffffee380001 0xebfffffffdc70000

def z601 : W := mkw 0x0050000580014040 0x800a0000b0002808 0x006000070001c000 0x000c0000e0003800

def z602 : W := mkw 0x8008c468661e1e18 0x1001188d0cc3c3c3 0xa899cce0ee3e3e3a 0x1513399c1dc7c7c7

def z603 : W := mkw 0x7dd97ea01f7d15b1 0x4fbb2fd403efa2b6 0xbf99ffe01ff807ff 0xf7f33ffc03ff00ff

def z604 : W := mkw 0x3c8004201b280410 0x0790008403650082 0xbf800fe01ff8063b 0xf7f001fc03ff00c7

def z605 : W := mkw 0x7ff53ea01be9a5b1 0x4ffea7d4037d34b6 0xbfe03fe01ff9c7ff 0xf7fc07fc03ff38ff

def z606 : W := mkw 0x0002815840020a08 0x0000502b08004141 0xe89fcff8e0063e3b 0x7d13f9ff1c00c7c7

def z607 : W := mkw 0x0008000924074240 0x800100012480e848 0x000000000007c000 0x000000000000f800

def z608 : W := mkw 0x3d803aa0016800b0 0x47b00754002d0016 0x3f803fe001f8003b 0xe7f007fc003f0007

def z609 : W := mkw 0xbc88ece07f3c1510 0x57911d9c0fe782a2 0x0899cce0ee380000 0x0113399c1dc70000

def z610 : W := mkw 0x832ed77a66debeb8 0x3065daef4cdbd7d7 0xef9fcff8effe3e3b 0x7df3f9ff1dffc7c7

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00003000000063b 0x74000060000000c7

def z612 : W := mkw 0x3d887ea01ffdb5b1 0x47b10fd403ffb6b6 0xbf803fe01fffffff 0xf7f007fc03ffffff

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x5060301f00000001 0xaa0c0603e0000000

def z614 : W := mkw 0x200840091df7fae9 0x2401080123beff5d 0xa00000001ffffffe 0x1400000003ffffff

def z615 : W := mkw 0x422540000090b001 0x0844a80000121600 0x0007c00000003800 0x0000f80000000700

def z616 : W := mkw 0x7efd44093fb7f741 0x8fdfa88127f6fee8 0xffffc0001fffffc5 0xdffff80003fffff8

def z617 : W := mkw 0x0000042002080410 0x0000008400410082 0x00000fe00000063a 0x200001fc000000c7

def z618 : W := mkw 0xfffffffeffbfbe1b 0x1fffffffdff7f7c3 0xfffffffffffffe3b 0xffffffffffffffc7

def z619 : W := mkw 0x022400000080a000 0x0044800000101400 0x2706000001c03800 0x44e0c00000380700

def z620 : W := mkw 0x200840001db5b001 0x0401080003b6b600 0xe89fc0001ffff801 0x5d13f80003ffff00

def z621 : W := mkw 0x022400000080a000 0x0044800000101400 0x406600000007f800 0x080cc0000000ff00

def z622 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x17e7f3e700000000 0xc2fcfe7ce0000000

def z623 : W := mkw 0x022601180082aa08 0x0044c02300105541 0xf766031811c7fe3b 0xfeecc0630238ffc7

def z624 : W := mkw 0x200844201ffdb5b1 0x4401088403ffb6b6 0xa00000001ffffffe 0x1400000003ffffff

def z625 : W := mkw 0x7cd940001d351001 0x0f9b280003a6a200 0xbf99c0001ff80001 0xd7f3380003ff0000

def z626 : W := mkw 0x1d803e801a000500 0x03b007d0034000a0 0x9f803fe01e0007c5 0xf3f007fc03c000f8

def z627 : W := mkw 0x0102131b00c2eae8 0x2020426360185d5d 0xa000331f11c7fffe 0x34000663e238ffff

def z628 : W := mkw 0x200004291beaeff8 0x64000085237d5dff 0xa00000001ffffffe 0x1400000003ffffff

def z629 : W := mkw 0xbfaefffb7ffefff8 0x77f5dfff6fffdfff 0xffffffffffffffff 0xffffffffffffffff

def z630 : W := mkw 0x5ff7bbdfc0424aea 0x2bfef77bf808495d 0x5fffffffe00007ff 0xebfffffffc0000ff

def z631 : W := mkw 0x0326131200c0a8a8 0x2064c26240181515 0xf766030011c7f83b 0xdeecc0600238ff07

def z632 : W := mkw 0x7ef5000019a1a001 0x0fdea00003343400 0x5fffc00011c1c001 0xcbfff80002383800

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x90003000100007c5 0xb2000600020000f8

def z634 : W := mkw 0x01003eada24a47f0 0xc02007d5b44948fe 0x00003fffe00007fe 0x200007fffc0000ff

def z635 : W := mkw 0x18002c201a080510 0x03000584034100a2 0xb8803fe01e3807ff 0xf71007fc03c700ff

def z636 : W := mkw 0x80028578620a0e18 0x100050af0c4141c3 0x489fcff8e000063b 0x6913f9ff1c0000c7

def z637 : W := mkw 0x000804093e074740 0x8001008127c0e8e8 0xc8180c18fe07c7c5 0x390301831fc0f8f8

def z638 : W := mkw 0x18002c091a024740 0x03000581234048e8 0xd8603c1f1e07c7c5 0xbb0c0783e3c0f8f8

def z639 : W := mkw 0x010012a0004800b0 0x4020025400090016 0x000003e00000003a 0x0000007c00000007

def z640 : W := mkw 0x0002011900c2eae8 0x2000402320185d5d 0xe006031811c7ffff 0x7c00c0630238ffff

def z641 : W := mkw 0x0326131200000000 0x0064c26240000000 0x0706030000000000 0x40e0c06000000000

def z642 : W := mkw 0x800ac15864161a08 0x1001582b0c82c341 0xe01fc318e0063e3b 0x7c03f8631c00c7c7

def z643 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x88180c00fe07c7c4 0x110301801fc0f8f8

def z644 : W := mkw 0x3d803aa0196801b0 0x47b00754032d0036 0x378033e011f801fe 0xc6f0067c023f003f

def z645 : W := mkw 0x5fffbbdfe4074242 0x8bfff77bfc80e848 0x5fffffffe007c001 0xebfffffffc00f800

def z646 : W := mkw 0x66a5000001a0a001 0x0cd4a00000341400 0x0700000001c00000 0x00e0000000380000

def z647 : W := mkw 0x5ffffbd6c495b003 0x0bffff7ad892b600 0x5fffffffe007f801 0xebfffffffc00ff00

def z648 : W := mkw 0x3d803e801b6005a0 0x47b007d0036c00b4 0x9f003c001fc007c5 0xb3e0078003f800f8

def z649 : W := mkw 0xa00ac5787fbfbe19 0x140158af0ff7f7c3 0xe89fcff8fffffe3b 0x7d13f9ff1fffffc7

def z650 : W := mkw 0x0000804040000000 0x0000100808000000 0x0899cce0e0000000 0x0113399c1c000000

def z651 : W := mkw 0x000804093e074740 0x8001008127c0e8e8 0xd060301f1e07c7c5 0xba0c0603e3c0f8f8

def z652 : W := mkw 0x7efd44201fbdb411 0x0fdfa88403f7b682 0xffffcfe01ffffe3b 0xfffff9fc03ffffc7

def z653 : W := mkw 0x3fa63fb21b6805b0 0x47f4c7f6436d00b6 0xffe63fff1ff807ff 0xfffcc7ffe3ff00ff

def z654 : W := mkw 0x8000402000181818 0x1000080400030303 0x200000000038383a 0x0400000000070707

def z655 : W := mkw 0x185804083e070600 0x030b008107c0e0c0 0xd8780c18fe07c601 0xbb0f01831fc0f8c0

def z656 : W := mkw 0x022400000080a000 0x0044800000101400 0x1760000011c1c000 0x82ec000002383800

def z657 : W := mkw 0x0324120300c0e0e0 0x2064824060181c1c 0xb760330711c1c7ff 0xf6ec0660e23838ff

def z658 : W := mkw 0x3c802ca01b280510 0x47900594036500a2 0x98803ce01e3807c5 0xb310079c03c700f8

def z659 : W := mkw 0xdffffffffe1f5f5a 0x9bffffffffc3ebeb 0xfffffffffe3fffff 0xffffffffffc7ffff

def z660 : W := mkw 0x5ff7bbd7d8014142 0x8bfef77afb002828 0x5ffffffff001c1c5 0xebfffffffe003838

def z661 : W := mkw 0x3d803a8019200000 0x07b0075003240000 0xbf803fe01ff80001 0xf7f007fc03ff0000

def z662 : W := mkw 0x8002c178401a1a18 0x1000582f08034343 0xe087c3f8003e3e3b 0x7c10f87f0007c7c7

def z663 : W := mkw 0x47a793d240000002 0x08f4f27a48000000 0x4f9fcff8e0000001 0x69f3f9ff1c000000

def z664 : W := mkw 0x7ffd7a801db5b001 0x0fffaf5003b6b600 0xffffffe01ffff801 0xfffffffc03ffff00

def z665 : W := mkw 0xfcd9c4607f3d1411 0x1f9b388c0fe7a282 0x0899cce0ee380000 0x0113399c1dc70000

def z666 : W := mkw 0x3c80000019200000 0x0790000003240000 0x1700000011c00000 0x82e0000002380000

def z667 : W := mkw 0x3d803ea91b6a47f0 0x47b007d5236d48fe 0xffe03fff1fffc7ff 0xfffc07ffe3fff8ff

def z668 : W := mkw 0x7ffd7a801df5b1a1 0x4fffaf5003beb634 0xfffff0001ffff9c5 0xdffffe0003ffff38

def z669 : W := mkw 0x200844093fb7f741 0x8401088127f6fee8 0xa00000001fffffc4 0x1400000003fffff8

def z670 : W := mkw 0x1858000dbc074240 0x830b0001b780e848 0xd878001ffe07c001 0x9b0f0003ffc0f800

def z671 : W := mkw 0x0000000100c0e0e0 0x2000000020181c1c 0x0000000011c1c1c4 0x0000000002383838

def z672 : W := mkw 0xffffd77b7ffffef9 0x3ffffaef6fffffdf 0xffffffffffffffff 0xffffffffffffffff

def z673 : W := mkw 0x0326bbd6c0000002 0x0064d77ad8000000 0x57663fffe0000001 0xeaecc7fffc000000

def z674 : W := mkw 0x3cd82ca4bf2d0510 0xc79b059497e5a0a2 0x08980ce0ee380000 0x0113019c1dc70000

def z675 : W := mkw 0x0002011b00024a48 0x2000402360004949 0x0000001f00000000 0x00000003e0000000

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z677 : W := mkw 0x000000000080a000 0x0000000000101400 0xa000000011c7f800 0x140000000238ff00

def z678 : W := mkw 0x3d8012a0196800b0 0x47b00254032d0016 0xbf8003e01ff8003b 0xd7f0007c03ff0007

def z679 : W := mkw 0x0000000000000000 0x0000000000000000 0x08800fe000000001 0x611001fc00000000

def z680 : W := mkw 0x7fff7fbb1ffffff9 0x6fffeff763ffffff 0xffffffff1fffffff 0xffffffffe3ffffff

def z681 : W := mkw 0x5ef5a8c4c0000002 0x0bdeb51898000000 0x5fffcce0e0000001 0xcbfff99c1c000000

def z682 : W := mkw 0x20000020016800b0 0x44000004002d0016 0x2000000001f8003a 0x04000000003f0007

def z683 : W := mkw 0xfeffc1587db7ba09 0x1fdff82b0fb6f741 0xffffc018fffff801 0xdffff8031fffff00

def z684 : W := mkw 0x1a7e2d1fbe87ef48 0xa34fc5a3f7d0fde9 0xd87e3c1ffe07ffc5 0xbb0fc783ffc0fff8

def z685 : W := mkw 0x7efde8c4ddb5b003 0x0fdfbd189bb6b600 0xffffcce0fffff801 0xdffff99c1fffff00

def z686 : W := mkw 0x800ac5797e1f5f58 0x900158af2fc3ebeb 0xe89fcff8fe3fffff 0x7d13f9ff1fc7ffff

def z687 : W := mkw 0x3fa43a8319e0e1e0 0x67f48750633c1c3c 0x1760300711c1c1c4 0x82ec0600e2383838

def z688 : W := mkw 0x3fa43ea01be8a5b0 0x47f487d4037d14b6 0xffe63fe01fffffff 0xfffcc7fc03ffffff

def z689 : W := mkw 0x5ff793d240000002 0x0bfef27a48000000 0x5fffc3e000000001 0xcbfff87c00000000

def z690 : W := mkw 0x427500000081a001 0x084ea00000103400 0x006000000001c000 0x000c000000003800

def z691 : W := mkw 0x2000000019a1a001 0x0400000003343400 0x0000000011c1c000 0x0000000002383800

def z692 : W := mkw 0x7ff7bff6db280512 0x4ffef7fedb6500a2 0x5fffffffee380001 0xebfffffffdc70000

def z693 : W := mkw 0x1dd83e8dbe074740 0x83bb07d1b7c0e8e8 0xdff83ffffe07c7c5 0xfbff07ffffc0f8f8

def z694 : W := mkw 0x0326131a00020a08 0x0064c26340004141 0xf766331f00063e3b 0xfeecc663e000c7c7

def z695 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0x17003fe011c007fe 0xa2e007fc023800ff

def z696 : W := mkw 0x01023f1fa2424fe8 0xa02047e3f44849fd 0x00003f1fe00007fe 0x200007e3fc0000ff

def z697 : W := mkw 0x0000042002080410 0x0000008400410082 0xa00000000e38063a 0x1400000001c700c7

def z698 : W := mkw 0x03263fbb02caeff8 0x6064c7f760595dff 0xf7663fff11c7ffff 0xfeecc7ffe238ffff

def z699 : W := mkw 0x7ef5000019200000 0x0fdea00003240000 0xffffc0001ff80001 0xdffff80003ff0000

def z700 : W := mkw 0x3d82bff05b6805b0 0x47b057fe0b6d00b6 0xff9ffff8fff807ff 0xfff3ffff1fff00ff

def z701 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0x2f9fc0000ff83800 0x45f3f80001ff0700

def z702 : W := mkw 0x3d803eadbb6a47f0 0xc7b007d5b76d48fe 0xbf803ffffff807ff 0xf7f007ffffff00ff

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x489fc00000000001 0x4913f80000000000

def z704 : W := mkw 0x80000428220a0e18 0x10000085044141c3 0x000000000000063a 0x00000000000000c7

def z705 : W := mkw 0x1d803a80004000a0 0x03b0075000080014 0xbf803fe011c007ff 0xf7f007fc023800ff

def z706 : W := mkw 0x5ff53a8680000002 0x0bfea750d0000000 0x1fe03fe700000001 0xe3fc07fce0000000

def z707 : W := mkw 0x5ff7bbd6d8000002 0x0bfef77adb000000 0xdffffffffe000001 0xfbffffffffc00000

def z708 : W := mkw 0x4327935240c0a8aa 0x2864f26a48181515 0x2707c30001c0383a 0x44e0f86000380707

def z709 : W := mkw 0xbd8afbd87d761ba8 0x57b15f7b0faec375 0x571ff018f1c639c4 0x8ae3fe031e38c738

def z710 : W := mkw 0x210afbd6ddb5b003 0x04215f7adbb6b600 0xa0003ffffffff800 0x340007ffffffff00

def z711 : W := mkw 0x1b76bb56c0000000 0x036ed76ad8000000 0x5fffffffe0000001 0xebfffffffc000000

def z712 : W := mkw 0x5ff7bbd6c080a002 0x0bfef77ad8101400 0x7fffffffe1c03801 0xeffffffffc380700

def z713 : W := mkw 0x5cd92c0dbe074740 0x8b9b2581b7c0e8e8 0xd8f9fc1ffe07c7c5 0xbb1f3f83ffc0f8f8

def z714 : W := mkw 0x7ff7bbd6d96000a2 0x0ffef77adb2c0014 0xfffffffffff807ff 0xffffffffffff00ff

def z715 : W := mkw 0x832cd66366dcf4f0 0x30659acc6cdb9e9e 0x1ff9fce7fff9c1c4 0x83ff3f9cffff3838

def z716 : W := mkw 0x800ac579661e5e58 0x100158af2cc3cbcb 0xe8ffcfffee3ffe3b 0x7d1ff9fffdc7ffc7

def z717 : W := mkw 0x5ff7bbd6d8010102 0x8bfef77adb002020 0x5fffffffe0000001 0xebfffffffc000000

def z718 : W := mkw 0x7ddb531b1d775ae9 0x2fbb6a6363aeeb5d 0x0899f31f0e3807fe 0x21133e63e1c700ff

def z719 : W := mkw 0x3d803ea49b6805b0 0x47b007d4936d00b6 0xbf803ffffff807ff 0xf7f007ffffff00ff

def z720 : W := mkw 0x9852e975d8195958 0x930a5d2ebb032b2b 0x30e7f3e71039f9fe 0xc61cfe7ce2073f3f

def z721 : W := mkw 0x5cd3a9d6c0000002 0x0b9a753ad8000000 0x0899ccffe0000000 0x0113399ffc000000

def z722 : W := mkw 0x18502c0dba034740 0x830a0581b74068e8 0x58783c1ff001c7c5 0xab0f0783fe0038f8

def z723 : W := mkw 0x7ff7bbd6d9200002 0x0ffef77adb240000 0x5fffffffee380001 0xebfffffffdc70000

def z724 : W := mkw 0x0058040da6074640 0x800b0081b4c0e8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z725 : W := mkw 0x000804093e074740 0x8001008127c0e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z726 : W := mkw 0x5ff7bbd6d8010002 0x0bfef77adb002000 0x5ffffffff001c001 0xebfffffffe003800

def z727 : W := mkw 0x66a56c0da3b2f741 0x8cd4ad81b4765ee8 0x2787fc1fe1f83fc4 0x64f0ff83fc3f07f8

def z728 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0x489fcff8ee3e3e3a 0x2913f9ff1dc7c7c7

def z729 : W := mkw 0x5cd1a8cdc0c2eaea 0x2b9a3519b8185d5d 0xa899cce0f1c7fffe 0x1513399c1e38ffff

def z730 : W := mkw 0x62778576db6805b2 0x4c4ef0aedb6d00b6 0xe07fc01ffff807fe 0x1c0ff803ffff00ff

def z731 : W := mkw 0x18586c0dbe175740 0x830b0d81b7c2eae8 0xd87ffc1ffe07ffc5 0xbb0fff83ffc0fff8

def z732 : W := mkw 0x5dd3bbd6c0000002 0x0bba777ad8000000 0x1f99ffffe0000001 0xe3f33ffffc000000

def z733 : W := mkw 0x18582c2dbe0f4750 0x830b0585b7c1e8ea 0xd8f83cfffe3fc7c5 0xbb1f079fffc7f8f8

def z734 : W := mkw 0x18582c0da6064640 0x030b0581b4c0c8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z735 : W := mkw 0x7dd13ea01b6905b1 0x4fba27d4036d20b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z736 : W := mkw 0x5dd3bbd6c0000002 0x0bba777ad8000000 0x489fffffe0000001 0x6913fffffc000000

def z737 : W := mkw 0x200844293ffff7f1 0xc401088527fffefe 0xa00000001ffffffe 0x1400000003ffffff

def z738 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xd8fffc1ffe07c7c5 0xfb1fff83ffc0f8f8

def z739 : W := mkw 0xfef785787babae19 0x1fdef0af0f7575c3 0x17600ff8f1c1c63a 0xa2ec01ff1e3838c7

def z740 : W := mkw 0x3cd82c0dbf274740 0x879b0581b7e4e8e8 0xd8f83c1ffe3fc7c5 0xbb1f0783ffc7f8f8

def z741 : W := mkw 0x21003ea01b6805b0 0x442007d4036d00b6 0xb7003fe01ff807ff 0xf6e007fc03ff00ff

def z742 : W := mkw 0x7ff7bbd6d9a1a003 0x0ffef77adb343400 0xfffffffff1c7f801 0xfffffffffe38ff00

def z743 : W := mkw 0x5ff53a8480000000 0x0bfea75090000000 0x5fffffffe0000001 0xebfffffffc000000

def z744 : W := mkw 0x1d82bbd6c0000002 0x03b0577ad8000000 0x5f9fffffe0000001 0xebf3fffffc000000

def z745 : W := mkw 0x5cd3a9d4c0000002 0x0b9a753a98000000 0x58ffffffe0000001 0xeb1ffffffc000000

def z746 : W := mkw 0x3ea62dbb1baaef58 0x67d4c5b763755deb 0x48e60cff0e3ff800 0x091cc19fe1c7ff00

def z747 : W := mkw 0xc7a7d3f240d8b8ba 0x38f4fa7e481b1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z748 : W := mkw 0x437d7ea006ddb5b1 0x486fafd400dbb6b6 0x407fffe00007fffe 0x280ffffc0000ffff

def z749 : W := mkw 0x1858280d9c074240 0x030b0501b380e848 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z750 : W := mkw 0x7ff53a8799e1e0e3 0x2ffea750f33c3c1c 0x1760300711c1c1c4 0x82ec0600e2383838

def z751 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0xffffffffe0063801 0xfffffffffc00c700

def z752 : W := mkw 0x00002c0da2024740 0x80000581b44048e8 0x10603c1ff001c7c4 0xa20c0783fe0038f8

def z753 : W := mkw 0x0326131200c0a0a0 0x0064c26240181414 0xf766331f11c7ffff 0xfeecc663e238ffff

def z754 : W := mkw 0x18502c059a014540 0x830a0580b34028a8 0xd8783c1ffe01c7c5 0xbb0f0783ffc038f8

def z755 : W := mkw 0x1858280dbc074340 0x830b0501b780e868 0xd878301ffe07c1c5 0x9b0f0603ffc0f838

def z756 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0x289fcff8ee383e3a 0x6513f9ff1dc707c7

def z757 : W := mkw 0x7efd68049db5b001 0x0fdfad0093b6b600 0xffffcc00fffff801 0xdffff9801fffff00

def z758 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xf89ffff8fe3e3fff 0xff13ffff1fc7c7ff

def z759 : W := mkw 0x627d40001db5b001 0x0c4fa80003b6b600 0xf77fc0001ffff801 0xdeeff80003ffff00

def z760 : W := mkw 0x47f793d6c0000002 0x08fef27ad8000000 0x4fffcfffe0000001 0x69fff9fffc000000

def z761 : W := mkw 0x0100120900c2eae8 0x2020024120185d5d 0xf760331f11c7ffff 0xfeec0663e238ffff

def z762 : W := mkw 0x47af97db7e074742 0x88f5f2fb6fc0e8e8 0x8787c3e01e07c7c4 0x50f0f87c03c0f8f8

def z763 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0x6fffc0000ffff800 0x4dfff80001ffff00

def z764 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xaf9fc0001ffff800 0x55f3f80003ffff00

def z765 : W := mkw 0x5ff7bbd6c04008aa 0x2bfef77ad8080115 0x5fffffffe000003b 0xebfffffffc000007

def z766 : W := mkw 0x3d8016201b6804b0 0x07b002c4036d0096 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z767 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xb78033e01ff807fe 0xd6f0067c03ff00ff

def z768 : W := mkw 0xdffd7eaea61e1e1a 0x1bffafd5d4c3c3c3 0xb76030070e3e3e3a 0x96ec0600e1c7c7c7

def z769 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xf8783f1ffe07c7ff 0xff0f07e3ffc0f8ff

def z770 : W := mkw 0x00028156c0000002 0x0000502ad8000000 0x489fcfffe0000001 0x6913f9fffc000000

def z771 : W := mkw 0x5ff7bbd6c081a003 0x0bfef77ad8103400 0x5fffffffe001c001 0xebfffffffc003800

def z772 : W := mkw 0x3d803a80196000a0 0x07b00750032c0014 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z773 : W := mkw 0x3cd82cadbf2f4750 0xc79b0595b7e5e8ea 0xf8f83ffffe3fc7ff 0xff1f07ffffc7f8ff

def z774 : W := mkw 0x1858280dbc074340 0x830b0501b780e868 0x58783c1ff007c1c5 0xab0f0783fe00f838

def z775 : W := mkw 0xa7a6d3f241f8b8b8 0x74f4da7e483f1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z776 : W := mkw 0x18586c0dbe175740 0x830b0d81b7c2eae8 0xd8f9fc1ffe3fc7c5 0xbb1f3f83ffc7f8f8

def z777 : W := mkw 0x47f7bbd6c0000002 0x08fef77ad8000000 0x47ffffffe0000000 0x68fffffffc000000

def z778 : W := mkw 0x800ac570661c1c18 0x100158ae0cc38383 0xe89fcfe0ee3e383b 0x5d13f9fc1dc7c707

def z779 : W := mkw 0x66ad40001db5b001 0x0cd5a80003b6b600 0xf7e7c0001ffff801 0xdefcf80003ffff00

def z780 : W := mkw 0x25d812ada56f42f0 0xc4bb0255b4ade85e 0x67f803ffe1ffc03a 0x4cff007ffc3ff807

def z781 : W := mkw 0x7ff7bbd6c1200002 0x0ffef77ad8240000 0x7fffffffe1f80001 0xeffffffffc3f0000

def z782 : W := mkw 0x3dd03ea01b6805b0 0x47ba07d4036d00b6 0xfff83fe01ff807ff 0xffff07fc03ff00ff

def z783 : W := mkw 0x7ff7bbd6d96001a2 0x4ffef77adb2c0034 0xfffffffffff801c5 0xffffffffffff0038

def z784 : W := mkw 0x5ff7bbd6c080a80a 0x2bfef77ad8101501 0x5fffffffe0003801 0xebfffffffc000700

def z785 : W := mkw 0x5ff7bbd6c0c0a0a2 0x2bfef77ad8181414 0x5fffffffe1c00001 0xebfffffffc380000

def z786 : W := mkw 0x67a793f241e8a8ba 0x6cf4f27e483d1517 0x2787c3e001f8383a 0x44f0f87c003f0707

def z787 : W := mkw 0x5efd40000494b000 0x0bdfa80000929600 0xffffc0001ffff801 0xdffff80003ffff00

def z788 : W := mkw 0x00082c0da6064740 0x80010581b4c0c8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z789 : W := mkw 0x4327935b40c2eaea 0x2864f26b68185d5d 0xf767f31f11c7ffff 0xfeecfe63e238ffff

def z790 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xff783c1fffc7c7c5 0xffef0783fff8f8f8

def z791 : W := mkw 0x5cd92c8dbe074742 0x8b9b2591b7c0e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z792 : W := mkw 0x800ac579661f5e58 0x900158af2cc3ebcb 0xe89fcff8ee3ffe3b 0x7d13f9ff1dc7ffc7

def z793 : W := mkw 0x18582c2dbe0f4750 0x830b0585b7c1e8ea 0xd8783ffffe07c7ff 0xbb0f07ffffc0f8ff

def z794 : W := mkw 0x8326d35240d0b8a8 0x3064da6a481a1715 0x2707c30001c0383a 0x44e0f86000380707

def z795 : W := mkw 0x0000280d80024240 0x00000501b0004848 0xd0603c1ff007c7c5 0xba0c0783fe00f8f8

def z796 : W := mkw 0x8102bf7fe24a4ff8 0xb02057effc4949ff 0x00003fffe00007fe 0x200007fffc0000ff

def z797 : W := mkw 0x1858280da4074240 0x830b0501b480e848 0xd8783c1ff007c7c5 0xbb0f0783fe00f8f8

def z798 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xff863fe01ffe3fff 0xfff0c7fc03ffc7ff

def z799 : W := mkw 0x01003ea0024805b0 0x402007d4004900b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z800 : W := mkw 0x032693db40c2eaea 0x2064d27b68185d5d 0xf76633ff11c7ffff 0xfeecc67fe238ffff

def z801 : W := mkw 0x1850280598014140 0x830a0500b3002828 0x5078301ff001c1c4 0x8a0f0603fe003838

def z802 : W := mkw 0x0002815040000000 0x0000502a08000000 0x58ffffffe0000001 0xeb1ffffffc000000

def z803 : W := mkw 0x7cd96c0dbf375741 0x8f9b2d81b7e6eae8 0xfff9fc1fffffc7c5 0xffff3f83fffff8f8

def z804 : W := mkw 0x0058000da4074240 0x800b0001b480e848 0x4078301fe007c7c4 0x280f0603fc00f8f8

def z805 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xff7e3f1ff1c7ffff 0xffefc7e3fe38ffff

def z806 : W := mkw 0x7ff7bbd6d9200002 0x0ffef77adb240000 0x5ffffffff1c00001 0xebfffffffe380000

def z807 : W := mkw 0x0058280da4074340 0x800b0501b480e868 0x4078301fe007c1c4 0x080f0603fc00f838

def z808 : W := mkw 0x1b7e3f16bec5ada8 0xa36fc7e2d7d8b5b5 0x2f1e0f00efc0383a 0x45e3c1e01df80707

def z809 : W := mkw 0x18582c2dbe0f4750 0x830b0585b7c1e8ea 0xf8783c1ffe3fc7ff 0xbf0f0783ffc7f8ff

def z810 : W := mkw 0x66ad400005b4b001 0x0cd5a80000b69600 0xffffc0001ffff801 0xdffff80003ffff00

def z811 : W := mkw 0x7ff7bbd6d9a1a003 0x0ffef77adb343400 0xfffffffffff9c001 0xffffffffffff3800

def z812 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xb760331f11c7fffe 0xb6ec0663e238ffff

def z813 : W := mkw 0x7efd68801db5b101 0x4fdfad1003b6b620 0xffffc0001ffff801 0xdffff80003ffff00

def z814 : W := mkw 0x0102131900424ae8 0x002042632008495d 0xf766331f11c7ffff 0xfeecc663e238ffff

def z815 : W := mkw 0x185828059c054140 0x830b0500b380a828 0xd8783c1ffe07c1c5 0xbb0f0783ffc0f838

def z816 : W := mkw 0x3c8004201b6805b0 0x47900084036d00b6 0xbf800fe01ff807ff 0xf7f001fc03ff00ff

def z817 : W := mkw 0x18502c0da2024740 0x830a0581b44048e8 0xd8783c1ff007c7c5 0xbb0f0783fe00f8f8

def z818 : W := mkw 0xc27fc15de497fa49 0x984ff82bbc92ff49 0x407fc01fe007f800 0x080ff803fc00ff00

def z819 : W := mkw 0x18582cadbe0f4750 0xc30b0595b7c1e8ea 0xd8783cfffe07c7c5 0xbb0f079fffc0f8f8

def z820 : W := mkw 0x8102bffde24a4ff8 0xd02057ffbc4949ff 0x00003fffe00007fe 0x200007fffc0000ff

def z821 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x90603c1ffe07c7c4 0xb20c0783ffc0f8f8

def z822 : W := mkw 0x5ff7bbd6c080a002 0x0bfef77ad8101400 0x5ffffffff1c1c001 0xebfffffffe383800

def z823 : W := mkw 0x5a77a956c0000002 0x0b4ef52ad8000000 0x58ffffffe0000001 0xeb1ffffffc000000

def z824 : W := mkw 0x18582c0da6074740 0x830b0581b4c0e8e8 0x58783c1fe007c7c5 0xab0f0783fc00f8f8

def z825 : W := mkw 0x7efd68049db5b101 0x8fdfad0093b6b620 0xffffc0001ffff801 0xdffff80003ffff00

def z826 : W := mkw 0x3cd82c8dbf274740 0xc79b0591b7e4e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z827 : W := mkw 0x0058000da4074240 0x800b0001b480e848 0x5078301ff007c1c4 0x8a0f0603fe00f838

def z828 : W := mkw 0x5ff7bbd6d8000102 0x0bfef77adb000020 0x5ffffffff00001c5 0xebfffffffe000038

def z829 : W := mkw 0x0002a954c0000000 0x0000552a98000000 0x489fffffe0000001 0x6913fffffc000000

def z830 : W := mkw 0x0008000924064240 0x000100012480c848 0xd078301ff007c7c5 0xba0f0603fe00f8f8

def z831 : W := mkw 0x800ac579661e5e58 0x100158af2cc3cbcb 0xe89fffffee3e3fff 0x7d13fffffdc7c7ff

def z832 : W := mkw 0x800ac570661c1c18 0x100158ae0cc38383 0xa89fcfe0ee383e3b 0x7513f9fc1dc707c7

def z833 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xfffff01f1ffff801 0xfffffe03e3ffff00

def z834 : W := mkw 0x427d40000495b001 0x084fa8000092b600 0xffffc0001ffff801 0xdffff80003ffff00

def z835 : W := mkw 0x47a793d240c0a0a2 0x28f4f27a48181414 0x0787c3e001c00000 0x40f0f87c00380000

def z836 : W := mkw 0x00582c0dbe074740 0x800b0581b7c0e8e8 0xc0783c1ffe07c7c4 0x380f0783ffc0f8f8

def z837 : W := mkw 0x0000040922024640 0x00000081244048c8 0xd0603c1ff007c7c5 0xba0c0783fe00f8f8

def z838 : W := mkw 0x800ac579661e5e58 0x100158af2cc3cbcb 0xe89fcff8fe3fffff 0x7d13f9ff1fc7ffff

def z839 : W := mkw 0x7dd13ea01b6805b0 0x4fba27d4036d00b6 0xbf99ffe01ff807ff 0xf7f33ffc03ff00ff

def z840 : W := mkw 0xa00844293fbfff59 0x9401088527f7ffeb 0xa00000001ffffffe 0x1400000003ffffff

def z841 : W := mkw 0x98586c0dbe175f48 0x930b0d81b7c2ebe9 0xd8783c1ffe07ffc5 0xbb0f0783ffc0fff8

def z842 : W := mkw 0x0324120b00c2eae8 0x2064824160185d5d 0xb760330711c7ffff 0xf6ec0660e238ffff

def z843 : W := mkw 0xa00844293ffefff8 0x7401088527ffdfff 0xa00000001ffffffe 0x1400000003ffffff

def z844 : W := mkw 0xa00844293f7f5ff8 0xd401088527efebff 0xa00000001ffffffe 0x1400000003ffffff

def z845 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xff983ff8fff807ff 0xfff307ff1fff00ff

def z846 : W := mkw 0x98582c2dbe0f4f58 0x930b0585b7c1e9eb 0xd8783c1ffe07c7ff 0xbb0f0783ffc0f8ff

def z847 : W := mkw 0x800ac170441c1818 0x1001582e08838303 0xe89fcff8ee3e383b 0x7d13f9ff1dc7c707

def z848 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xf77fc0001ffff800 0x9eeff80003ffff00

def z849 : W := mkw 0x0102bfffc24a4ffa 0x602057fff84949ff 0x00003fffe00007fe 0x200007fffc0000ff

def z850 : W := mkw 0x66fd400005b5b001 0x0cdfa80000b6b600 0xefffc0000ffff801 0x5dfff80001ffff00

def z851 : W := mkw 0x98586c2dbe1f5f58 0x930b0d85b7c3ebeb 0xf8fffc1ffe3fffff 0xff1fff83ffc7ffff

def z852 : W := mkw 0x1d803ea0024804b0 0x03b007d400490096 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z853 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xb766330711c7fffe 0xd6ecc660e238ffff

def z854 : W := mkw 0x827ec15fe497fa48 0xb04fd82bfc92ff49 0x407fc01fe007f800 0x080ff803fc00ff00

def z855 : W := mkw 0x1fa6bbd240000000 0x03f4d77a48000000 0x5fffffffe0000001 0xebfffffffc000000

def z856 : W := mkw 0x5ef7a9d6c0000002 0x0bdef53ad8000000 0x5fffccffe0000001 0xcbfff99ffc000000

def z857 : W := mkw 0x7cd96cadbf3f5751 0xcf9b2d95b7e7eaea 0xd8f9fcfffe3fc7c5 0xbb1f3f9fffc7f8f8

def z858 : W := mkw 0x8008c460661c1410 0x1001188c0cc38282 0xe89fcfe0ee3e3e3b 0x7d13f9fc1dc7c7c7

def z859 : W := mkw 0x00002c0da2024740 0x80000581b44048e8 0x40603c1fe007c7c4 0x280c0783fc00f8f8

def z860 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xfffff0001fffffc5 0xfffffe0003fffff8

def z861 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x1ff9ffffe0000000 0xa3ff3ffffc000000

def z862 : W := mkw 0x258016a01b6805b0 0x44b002d4036d00b6 0xaf800fe01ff807ff 0x75f001fc03ff00ff

def z863 : W := mkw 0x7cd96ca4bf3d1511 0xcf9b2d9497e7a2a2 0x0899cce0ee380000 0x0113399c1dc70000

def z864 : W := mkw 0x5cd1a8c4c0000002 0x0b9a351898000000 0x0899fcffe0000000 0x21133f9ffc000000

def z865 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x48ffffffe0000000 0x291ffffffc000000

def z866 : W := mkw 0x3dd03ea49b6805b0 0x47ba07d4936d00b6 0xbfe03fe71ff807ff 0xf7fc07fce3ff00ff

def z867 : W := mkw 0x38582c0dbf274740 0x870b0581b7e4e8e8 0xf8783c1fffffc7c5 0xbf0f0783fffff8f8

def z868 : W := mkw 0x000ac15844161a08 0x0001582b0882c341 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z869 : W := mkw 0x47a7bbd6c0000002 0x08f4f77ad8000000 0x4f9fffffe0000001 0x69f3fffffc000000

def z870 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0xffffffffee380001 0xfffffffffdc70000

def z871 : W := mkw 0x98586c2dbe1f5f58 0x930b0d85b7c3ebeb 0xf8f83ffffe3fffff 0xff1f07ffffc7ffff

def z872 : W := mkw 0x7efd68001db5b001 0x0fdfad0003b6b600 0xfffffc001ffff801 0xffffff8003ffff00

def z873 : W := mkw 0x00084428261e1610 0x0001088504c3c2c2 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z874 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xffe03fff1ff807ff 0xfffc07ffe3ff00ff

def z875 : W := mkw 0x5ef7a9d6c0000002 0x0bdef53ad8000000 0x48ffcfffe0000001 0x691ff9fffc000000

def z876 : W := mkw 0xa00844293ffffef9 0x3401088527ffffdf 0xa00000001ffffffe 0x1400000003ffffff

def z877 : W := mkw 0x80084429261e5f58 0x9001088524c3cbeb 0xa00000000e3e3ffe 0x1400000001c7c7ff

def z878 : W := mkw 0x7ff53a8699e1a1a3 0x4ffea750d33c3434 0x1760300711c1c1c4 0x82ec0600e2383838

def z879 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x0f9fffffe0000000 0x61f3fffffc000000

def z880 : W := mkw 0x7efd4004bdb5b001 0x8fdfa80097b6b600 0xffffc000fffff801 0xdffff8001fffff00

def z881 : W := mkw 0x7ef5000019a0a000 0x0fdea00003341400 0xffffc0001ffff801 0xdffff80003ffff00

def z882 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xd8f83ffffe07c7c5 0xfb1f07ffffc0f8f8

def z883 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x577fffffe0000000 0xaaeffffffc000000

def z884 : W := mkw 0x0226815240000000 0x0044d02a48000000 0x48ffcfffe0000001 0x691ff9fffc000000

def z885 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xffffcfe01ffff801 0xfffff9fc03ffff00

def z886 : W := mkw 0x800ac570661c1c18 0x100158ae0cc38383 0x689fcff8ee38383b 0x6d13f9ff1dc70707

def z887 : W := mkw 0x7efd68849db5b003 0x0fdfad1093b6b600 0xffffc0001ffff801 0xdffff80003ffff00

def z888 : W := mkw 0x7cd92c0dbf274741 0x8f9b2581b7e4e8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z889 : W := mkw 0x1cd82c8dbe074740 0x839b0591b7c0e8e8 0xd8f83cfffe07c7c5 0xbb1f079fffc0f8f8

def z890 : W := mkw 0x18502c0dba034740 0x830a0581b74068e8 0x98603c1ffe01c7c5 0xb30c0783ffc038f8

def z891 : W := mkw 0x5ff7bbd6c04000a2 0x0bfef77ad8080014 0x7fffffffe1c0003b 0xeffffffffc380007

def z892 : W := mkw 0x5ff7bbd6c000080a 0x0bfef77ad8000101 0x7fffffffe000383b 0xeffffffffc000707

def z893 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0x5fffc0001ffff800 0x8bfff80003ffff00

def z894 : W := mkw 0x7ff53a8799e0e1e2 0x6ffea750f33c1c3c 0x1760300711c1c1c4 0x82ec0600e2383838

def z895 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xf8f83c1ffe3fc7c5 0xff1f0783ffc7f8f8

def z896 : W := mkw 0x66fd40001db5b001 0x0cdfa80003b6b600 0xe7ffc0001ffff800 0x5cfff80003ffff00

def z897 : W := mkw 0xe7a7d37241f8b8b9 0x3cf4fa6e483f1717 0x2787c3e001f8383a 0x44f0f87c003f0707

def z898 : W := mkw 0x67a7d3d241f0b8ab 0x2cf4fa7a483e1715 0x2787c3e001f8383a 0x44f0f87c003f0707

def z899 : W := mkw 0x1850280580004040 0x030a0500b0000808 0x58783c1ff001c1c5 0xab0f0783fe003838

def z900 : W := mkw 0x7ea5400019b0b001 0x0fd4a80003361600 0xffe7c0001ffff801 0xdffcf80003ffff00

def z901 : W := mkw 0x7dd13ea49b6805b2 0x4fba27d4936d00b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z902 : W := mkw 0x1952bbd6c0000002 0x032a577ad8000000 0x58ffffffe0000001 0xeb1ffffffc000000

def z903 : W := mkw 0x8002c57042181c18 0x100058ae08430383 0xe89fcff8ee383e3b 0x7d13f9ff1dc707c7

def z904 : W := mkw 0x7ff7bbd6c16000a2 0x4ffef77ad82c0014 0x5fffffffe1c00001 0xebfffffffc380000

def z905 : W := mkw 0x5ff7bbd6c0c0a0a2 0x0bfef77ad8181414 0xfffffffff1c7ffff 0xfffffffffe38ffff

def z906 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x58783c1ffe07c1c4 0x8b0f0783ffc0f838

def z907 : W := mkw 0x80084429265e5ef8 0x3001088524cbcbdf 0xa00000000e3e3ffe 0x1400000001c7c7ff

def z908 : W := mkw 0x42778156c0000002 0x084ef02ad8000000 0x407fcfffe0000000 0x280ff9fffc000000

def z909 : W := mkw 0x3dd03ea49b6905b0 0xc7ba07d4936d20b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z910 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0x1f803fe01ff807fe 0xa3f007fc03ff00ff

def z911 : W := mkw 0x1850280db8034340 0x830a0501b7006868 0x1060301ff001c1c4 0x820c0603fe003838

def z912 : W := mkw 0x0326935240c0a8a8 0x2064d26a48181515 0x2787c3e001c0383a 0x44f0f87c00380707

def z913 : W := mkw 0x8326937240c8a8b8 0x3064d26e48191517 0x270603e001c0383a 0x44e0c07c00380707

def z914 : W := mkw 0x1a7c40001c95b000 0x034f88000392b600 0xffffc0001ffff801 0xdffff80003ffff00

def z915 : W := mkw 0x800844293edffff8 0xb001088527dbffff 0xa00000001ffffffe 0x1400000003ffffff

def z916 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0xfffffffff1c00001 0xfffffffffe380000

def z917 : W := mkw 0xc27fc15fe496fa4a 0x384ff82bfc92df49 0x407fc01fe007f800 0x080ff803fc00ff00

def z918 : W := mkw 0x66ad40001db5b001 0x0cd5a80003b6b600 0xef9fc0001ffff801 0x5df3f80003ffff00

def z919 : W := mkw 0x7ff53a8599e1e1e1 0xcffea750b33c3c3c 0x1760300711c1c1c4 0x82ec0600e2383838

def z920 : W := mkw 0x18502c0d9a024740 0x030a0581b34048e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z921 : W := mkw 0x18502c0dba034740 0x830a0581b74068e8 0xd0603c1ff007c7c5 0xba0c0783fe00f8f8

def z922 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0xdffffffff00007c5 0xfbfffffffe0000f8

def z923 : W := mkw 0x4153bbd6c0000002 0x082a777ad8000000 0x0019ffffe0000000 0x20033ffffc000000

def z924 : W := mkw 0xfcd9ec64ff3d1511 0x9f9b3d8c9fe7a2a2 0x0899cce0ee380000 0x0113399c1dc70000

def z925 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x48783c1fee07c7c4 0x290f0783fdc0f8f8

def z926 : W := mkw 0x7cd96c0dbf375741 0x8f9b2d81b7e6eae8 0xf8fffc1ffe3fffc5 0xff1fff83ffc7fff8

def z927 : W := mkw 0x7efd68801db5b001 0x0fdfad1003b6b600 0xffffcce01ffff801 0xdffff99c03ffff00

def z928 : W := mkw 0x3d8016a01b6805b0 0x47b002d4036d00b6 0xbf8003e01ff807ff 0xd7f0007c03ff00ff

def z929 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xffffcc18fffff801 0xfffff9831fffff00

def z930 : W := mkw 0x5ef7a954c0000000 0x0bdef52a98000000 0x5fffffffe0000001 0xebfffffffc000000

def z931 : W := mkw 0x1858000dbc074240 0x830b0001b780e848 0xd878301ffe07c7c5 0xbb0f0603ffc0f8f8

def z932 : W := mkw 0x3c8840001db5b001 0x0791080003b6b600 0xff9fc0001ffff801 0xdff3f80003ffff00

def z933 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0x2f803fe00ff807fe 0x65f007fc01ff00ff

def z934 : W := mkw 0x5ff5bac6c0000002 0x0bfeb758d8000000 0x5ff9fcffe0000001 0xabff3f9ffc000000

def z935 : W := mkw 0x3cd82c2dbf2f4750 0x879b0585b7e5e8ea 0xfff83fffffffc7ff 0xffff07fffffff8ff

def z936 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x18783c1ffe01c7c4 0xa30f0783ffc038f8

def z937 : W := mkw 0x0326935b40c2eae8 0x2064d26b68185d5d 0xf77ff31ff1c7ffff 0xfeeffe63fe38ffff

def z938 : W := mkw 0x47a793d240000002 0x08f4f27a48000000 0x5fffffffe0000001 0xebfffffffc000000

def z939 : W := mkw 0x0050000d80024240 0x000a0001b0004848 0xd078301ff007c7c5 0xba0f0603fe00f8f8

def z940 : W := mkw 0x0326bbd6c0000002 0x0064d77ad8000000 0x5fffffffe0000001 0xebfffffffc000000

def z941 : W := mkw 0x0102bbd6c0000002 0x0020577ad8000000 0x0899ffffe0000000 0x21133ffffc000000

def z942 : W := mkw 0x25803ea0036805b0 0x44b007d4006d00b6 0xaf803fe00ff807ff 0x75f007fc01ff00ff

def z943 : W := mkw 0x1dd2bbd4c0000000 0x03ba577a98000000 0x5fffffffe0000001 0xebfffffffc000000

def z944 : W := mkw 0x5b77bbd6c0000002 0x0b6ef77ad8000000 0x587fffffe0000001 0xab0ffffffc000000

def z945 : W := mkw 0x80084429261f5e58 0x9001088524c3ebcb 0xa00000000e3ffe3a 0x1400000001c7ffc7

def z946 : W := mkw 0x7cd9ece4df3d1513 0x4f9b3d9c9be7a2a2 0x0899cce0ee380000 0x0113399c1dc70000

def z947 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xb7e7c0001ffff800 0xd6fcf80003ffff00

def z948 : W := mkw 0x5ff7bbd6c0c0a8aa 0x2bfef77ad8181515 0xfffffffff1c7f83b 0xfffffffffe38ff07

def z949 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xff9fcff8fffe3e3b 0xfff3f9ff1fffc7c7

def z950 : W := mkw 0x1850a844c0000000 0x030a150898000000 0x58f9fcffe0000001 0xab1f3f9ffc000000

def z951 : W := mkw 0x0326935b40c2eae8 0x2064d26b68185d5d 0xf7663ffff1c7ffff 0xfeecc7fffe38ffff

def z952 : W := mkw 0x18582c0dbe074f48 0x830b0581b7c0e9e9 0xf8783c1ffe07ffff 0xbf0f0783ffc0ffff

def z953 : W := mkw 0x3cd82cadbf2f4750 0xc79b0595b7e5e8ea 0xfff83cffffffc7c5 0xffff079ffffff8f8

def z954 : W := mkw 0x1850280598014140 0x830a0500b3002828 0x10603c1ff001c1c4 0xa20c0783fe003838

def z955 : W := mkw 0x210016201b6805b0 0x442002c4036d00b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z956 : W := mkw 0x0102935240000000 0x0020526a48000000 0x489fffffe0000001 0x6913fffffc000000

def z957 : W := mkw 0x7ff7bbd6d9210003 0x0ffef77adb242000 0x5fffffffe0000001 0xebfffffffc000000

def z958 : W := mkw 0x7efd40069db5b003 0x0fdfa800d3b6b600 0xffffc0071ffff801 0xdffff800e3ffff00

def z959 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0xffffffffe000063b 0xfffffffffc0000c7

def z960 : W := mkw 0x5ef5a8c4c0000002 0x0bdeb51898000000 0x5ffffcffe0000001 0xebffff9ffc000000

def z961 : W := mkw 0xc27fc15b6497fa49 0x384ff82b6c92ff49 0x407fc01fe007f800 0x080ff803fc00ff00

def z962 : W := mkw 0x022601190082ea48 0x0044c02320105d49 0xf766331f11c7ffff 0xfeecc663e238ffff

def z963 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xd078301ffe07c7c4 0x9a0f0603ffc0f8f8

def z964 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xaf800fe01ff807fe 0x55f001fc03ff00ff

def z965 : W := mkw 0x3dd03ea49b6805b0 0x47ba07d4936d00b6 0xbf983fe0fff807ff 0xf7f307fc1fff00ff

def z966 : W := mkw 0x8102bfffe24a4efa 0x302057fffc4949df 0x00003fffe00007fe 0x200007fffc0000ff

def z967 : W := mkw 0x8102bffb624a4ff8 0x702057ff6c4949ff 0x00003fffe00007fe 0x200007fffc0000ff

def z968 : W := mkw 0x1850280d98034340 0x830a0501b3006868 0xd8783c1ff007c7c5 0xbb0f0783fe00f8f8

def z969 : W := mkw 0x0324120b00c2eae8 0x2064824160185d5d 0xf760301f11c7ffff 0xbeec0603e238ffff

def z970 : W := mkw 0x3c802c201b280510 0x07900584036500a2 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z971 : W := mkw 0x5ff7bbd6c080a002 0x0bfef77ad8101400 0x5fffffffe007f801 0xebfffffffc00ff00

def z972 : W := mkw 0x98586c2dbe1f5750 0x930b0d85b7c3eaea 0xd8783c1ffe3fc7c5 0xbb0f0783ffc7f8f8

def z973 : W := mkw 0x7efd68049db5b001 0x0fdfad0093b6b600 0xfffff0071ffff801 0xdffffe00e3ffff00

def z974 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xb7003fe01ff807fe 0xb6e007fc03ff00ff

def z975 : W := mkw 0x3cd82c0dbf274740 0x879b0581b7e4e8e8 0xdf783c1fffc7c7c5 0xbbef0783fff8f8f8

def z976 : W := mkw 0x258016a01b6805b0 0x44b002d4036d00b6 0xb78033e01ff807ff 0xf6f0067c03ff00ff

def z977 : W := mkw 0x258016a0036804b0 0x44b002d4006d0096 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z978 : W := mkw 0x00528154c0000000 0x000a502a98000000 0x48ffcfffe0000001 0x691ff9fffc000000

def z979 : W := mkw 0x000ac570461c1410 0x000158ae08c38282 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z980 : W := mkw 0x0000000900024240 0x0000000120004848 0xd8783c1ff007c7c5 0xbb0f0783fe00f8f8

def z981 : W := mkw 0x80084429269efe58 0x3001088524d3dfcb 0xa00000000e3ffe3a 0x1400000001c7ffc7

def z982 : W := mkw 0x18582c049e050500 0x030b058093c0a0a0 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z983 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xffe03fe01fffc7ff 0xfffc07fc03fff8ff

def z984 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xf766301f11c7fffe 0x9eecc603e238ffff

def z985 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0x50783c1ff007c7c4 0xaa0f0783fe00f8f8

def z986 : W := mkw 0x3d803ea69b6805b2 0x47b007d4d36d00b6 0xbf803fe71ff807ff 0xf7f007fce3ff00ff

def z987 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xa89fcfe0ee3e3e3a 0x5513f9fc1dc7c7c7

def z988 : W := mkw 0x5ef7a9d6c0000002 0x0bdef53ad8000000 0x58fffcffe0000001 0xab1fff9ffc000000

def z989 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x5ffffcffe0000000 0x8bffff9ffc000000

def z990 : W := mkw 0xbcd8ece4ff3d1510 0xd79b1d9c9fe7a2a2 0x0899cce0ee380000 0x0113399c1dc70000

def z991 : W := mkw 0x7ead40001db5b001 0x0fd5a80003b6b600 0xbf87c0001ffff801 0xd7f0f80003ffff00

def z992 : W := mkw 0x80084429261e5e58 0x1001088524c3cbcb 0xa00000001e3ffffe 0x1400000003c7ffff

def z993 : W := mkw 0x19003e201a4805b0 0x032007c4034900b6 0xbf803fe01ff807ff 0xf7f007fc03ff00ff

def z994 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0xdffffffff007c001 0xfbfffffffe00f800

def z995 : W := mkw 0x0224000900c2eae8 0x2044800120185d5d 0xf766301f11c7ffff 0xfeecc603e238ffff

def z996 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xf8ffffffee3e3e3b 0xff1ffffffdc7c7c7

def z997 : W := mkw 0x800844293e1f5750 0x9001088527c3eaea 0x800000001e3fc7c4 0x1000000003c7f8f8

def z998 : W := mkw 0x0324120300c0e0e0 0x2064824060181c1c 0xf766330711c7ffff 0xfeecc660e238ffff

def z999 : W := mkw 0x5ff7bbd6c04001a2 0x4bfef77ad8080034 0x5fffffffe00001c5 0xebfffffffc000038

def z1000 : W := mkw 0x38582c2dbf2f4750 0xc70b0585b7e5e8ea 0xd8783c1ffe3fc7c5 0xbb0f0783ffc7f8f8

def z1001 : W := mkw 0x18582c0dbe074740 0x830b0581b7c0e8e8 0xf87e3c1ffe07ffc5 0xff0fc783ffc0fff8

def z1002 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0xf8ffcff8fe3ffe3b 0xff1ff9ff1fc7ffc7

def z1003 : W := mkw 0x1858280dbc074340 0x830b0501b780e868 0xd078301ff007c7c5 0xba0f0603fe00f8f8

def z1004 : W := mkw 0x38586c0dbf375741 0x870b0d81b7e6eae8 0xd8783c1ffe3fc7c5 0xbb0f0783ffc7f8f8

def z1005 : W := mkw 0x5ff7bbd6c04000a2 0x0bfef77ad8080014 0x5ffffffff1c001c5 0xebfffffffe380038

def z1006 : W := mkw 0x7ff7bbd6d9a0a002 0x0ffef77adb341400 0xfffffffffffff801 0xffffffffffffff00

def z1007 : W := mkw 0x427fc15fc497fa4b 0x284ff82bf892ff49 0x407fc01fe007f800 0x080ff803fc00ff00

def z1008 : W := mkw 0x3cd840001d351000 0x079b080003a6a200 0xffffc0001ffff801 0xdffff80003ffff00

def z1009 : W := mkw 0x1cd82c0dbe074740 0x839b0581b7c0e8e8 0xdff83c1ffe07c7c5 0xfbff0783ffc0f8f8

def z1010 : W := mkw 0x3d8012a0196800b0 0x47b00254032d0016 0xbf8033e01ff807ff 0xf7f0067c03ff00ff

def z1011 : W := mkw 0x58596c0dbe175741 0x8b0b2d81b7c2eae8 0xd879fc1ffe07c7c5 0xbb0f3f83ffc0f8f8

def z1012 : W := mkw 0x5ff7935240000000 0x0bfef26a48000000 0x5fffffffe0000001 0xebfffffffc000000

def z1013 : W := mkw 0x7ff7bbd6d96001a2 0x4ffef77adb2c0034 0xfffffffff1c007ff 0xfffffffffe3800ff

def z1014 : W := mkw 0x67a7d3f241f8b0b3 0x4cf4fa7e483f1616 0x2787c3e001f8383a 0x44f0f87c003f0707

def z1015 : W := mkw 0x0324120b00c2eae8 0x2064824160185d5d 0xf766300711c7ffff 0xdeecc600e238ffff

def z1016 : W := mkw 0x8326935b60c2eae8 0x3064d26b6c185d5d 0xf766331ff1c7ffff 0xfeecc663fe38ffff

def z1017 : W := mkw 0x7ff7bbd6d9200102 0x4ffef77adb240020 0x5fffffffe0000001 0xebfffffffc000000

def z1018 : W := mkw 0x25803ea01b6805b0 0x44b007d4036d00b6 0xa7803fe01ff807fe 0x74f007fc03ff00ff

def z1019 : W := mkw 0x800ac579661e5f58 0x900158af2cc3cbeb 0xe89fcff8ee3e3fff 0x7d13f9ff1dc7c7ff

def z1020 : W := mkw 0x7ff7bbd6c1a0a003 0x0ffef77ad8341400 0x5fffffffe1c00001 0xebfffffffc380000

def z1021 : W := mkw 0x00502c0da2034740 0x800a0581b44068e8 0x00603c1fe001c7c4 0x200c0783fc0038f8

def z1022 : W := mkw 0x00082c0dbe074740 0x80010581b7c0e8e8 0xd0603c1ffe07c7c5 0xba0c0783ffc0f8f8

def z1023 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xffe6331f1fffffff 0xfffcc663e3ffffff

def z1024 : W := mkw 0x0000000da0024240 0x80000001b4004848 0xd060301ff007c7c5 0xba0c0603fe00f8f8

def z1025 : W := mkw 0x7efd40001db5b001 0x0fdfa80003b6b600 0xffffc3001ffffe3b 0xfffff86003ffffc7

def z1026 : W := mkw 0x0058040dbe074740 0x800b0081b7c0e8e8 0xd078301ffe07c7c5 0xba0f0603ffc0f8f8

def z1027 : W := mkw 0x00582c0da6074740 0x800b0581b4c0e8e8 0xd0783c1ff007c7c5 0xba0f0783fe00f8f8

def z1028 : W := mkw 0x222c40001db5b001 0x0445880003b6b600 0xffffc0001ffff801 0xdffff80003ffff00

def z1029 : W := mkw 0x7efd68001db5b101 0x0fdfad0003b6b620 0xfffff0001ffff9c5 0xdffffe0003ffff38

def z1030 : W := mkw 0x032693d240c0a8aa 0x2064d27a48181515 0x270603e001c0383a 0x44e0c07c00380707

def z1031 : W := mkw 0x42778156c0000002 0x084ef02ad8000000 0x48ffccffe0000000 0x091ff99ffc000000

def z1032 : W := mkw 0x5cd1a8c4c0000002 0x0b9a351898000000 0x48f9ccffe0000000 0x091f399ffc000000

def z1033 : W := mkw 0x4377bbd6c0000002 0x086ef77ad8000000 0x48ffffffe0000001 0x691ffffffc000000

def z1034 : W := mkw 0x18586c2dbe1f5750 0x830b0d85b7c3eaea 0xf8fffffffe3fffff 0xff1fffffffc7ffff

def z1035 : W := mkw 0x3d803ea4bb6805b0 0xc7b007d4976d00b6 0xbf803fe0fff807ff 0xf7f007fc1fff00ff

def z1036 : W := mkw 0x7ff7bbd6d9e1a1a3 0x4ffef77adb3c3434 0x5ffffffff1c1c1c5 0xebfffffffe383838

def z1037 : W := mkw 0x5dd1bac4c0000002 0x0bba375898000000 0x5ff9ffffe0000001 0xebff3ffffc000000

def z1038 : W := mkw 0x43779356c0000002 0x086ef26ad8000000 0x5fffffffe0000001 0xebfffffffc000000

def z1039 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xfffff31f11c7ffff 0xfffffe63e238ffff

def z1040 : W := mkw 0x18586c0dbe175740 0x830b0d81b7c2eae8 0xf8783c1ffe3fffc5 0xbf0f0783ffc7fff8

def z1041 : W := mkw 0x18002c0dba024740 0x83000581b74048e8 0xd8603c1ffe07c7c5 0xbb0c0783ffc0f8f8

def z1042 : W := mkw 0x800ac57b661e5e58 0x300158af6cc3cbcb 0xe89fcfffee3e3e3b 0x7d13f9fffdc7c7c7

def z1043 : W := mkw 0x4277a9d6c0000002 0x084ef53ad8000000 0x407fccffe0000000 0x080ff99ffc000000

def z1044 : W := mkw 0x3d803ea01b6805b0 0x47b007d4036d00b6 0xff9fffe01ff807ff 0xfff3fffc03ff00ff

def z1045 : W := mkw 0x185804093e074640 0x030b008127c0e8c8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z1046 : W := mkw 0x0324120900c2e2e0 0x0064824120185c5c 0xf766331f11c7ffff 0xfeecc663e238ffff

def z1047 : W := mkw 0x18082c093e064740 0x0301058127c0c8e8 0xd8783c1ffe07c7c5 0xbb0f0783ffc0f8f8

def z1048 : W := mkw 0x0326935b40c2eae8 0x2064d26b68185d5d 0xf7e7f3ff11c7ffff 0xfefcfe7fe238ffff

def z1049 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0x5766331f11c7fffe 0xaaecc663e238ffff

def z1050 : W := mkw 0x0102bbd6c0000002 0x0020577ad8000000 0x401fffffe0000000 0x2803fffffc000000

def z1051 : W := mkw 0x5ff7bbd6c0000002 0x0bfef77ad8000000 0x4fffcfffe0000000 0x49fff9fffc000000

def z1052 : W := mkw 0x4377bbd6c0000002 0x086ef77ad8000000 0x577fffffe0000001 0xeaeffffffc000000

def z1053 : W := mkw 0x7efd40049db5b001 0x0fdfa80093b6b600 0xffffc01ffffff801 0xdffff803ffffff00

def z1054 : W := mkw 0x00582c0da6074740 0x800b0581b4c0e8e8 0xc8783c1fee07c7c5 0x390f0783fdc0f8f8

def z1055 : W := mkw 0x3eac40001db4b000 0x07d5880003b69600 0xffffc0001ffff801 0xdffff80003ffff00

def z1056 : W := mkw 0x18582c05be054540 0x830b0580b7c0a8a8 0x58783c1ffe01c1c5 0xab0f0783ffc03838

def z1057 : W := mkw 0x5ff7bbd6c0c0a8aa 0x2bfef77ad8181515 0xfffffffff1c03fff 0xfffffffffe3807ff

def z1058 : W := mkw 0x800ac578661e1e18 0x100158af0cc3c3c3 0x689fcff8ee3e383a 0x4d13f9ff1dc7c707

def z1059 : W := mkw 0x0326131b00c2eae8 0x2064c26360185d5d 0xffe63fff11c7ffff 0xfffcc7ffe238ffff

def z1060 : W := mkw 0x3cd86c0dbf375740 0x879b0d81b7e6eae8 0xfffffc1fffffffc5 0xffffff83fffffff8

def z1061 : W := mkw 0x5ff7bbd6c04000a2 0x0bfef77ad8080014 0x5fffffffe00007ff 0xebfffffffc0000ff

def z1062 : W := mkw 0x5ef78156c0000002 0x0bdef02ad8000000 0x5fffcfffe0000001 0xebfff9fffc000000

def z1063 : W := mkw 0x5dd3bbd6c0000002 0x0bba777ad8000000 0x58f9ffffe0000001 0xab1f3ffffc000000

def z1064 : W := mkw 0x00028578420a0e18 0x000050af084141c3 0xe89fcff8ee3e3e3b 0x7d13f9ff1dc7c7c7

def z1065 : W := mkw 0x3dd03ea01b6905b0 0x47ba07d4036d20b6 0xbfe03fe01ff9c7ff 0xf7fc07fc03ff38ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z7,z3,z8,z4,z6]),(0,[z0,z1,z2,z3,z4,z9,z6])],[(0,[z10,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z11,z3,z4,z6]),(0,[z0,z1,z2,z12,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z13,z6]),(0,[z0,z14,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z15,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z16,z6]),(0,[z17,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z18,z6]),(1,[z19,z0,z1,z20,z2,z6])],[(0,[z0,z1,z2,z3,z4,z21,z6]),(0,[z0,z22,z2,z3,z23,z4,z6]),(0,[z0,z1,z2,z3,z4,z24,z6]),(0,[z0,z1,z2,z3,z25,z4,z6]),(0,[z26,z0,z1,z2,z3,z4,z6]),(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z0,z28,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z29]),(0,[z30,z0,z1,z2,z3,z6,z31]),(0,[z0,z1,z2,z3,z32,z4,z33])],[(0,[z34,z0,z1,z2,z3,z4,z31]),(0,[z0,z1,z2,z35,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z36])],[(0,[z37,z0,z38,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z4,z40,z6]),(1,[z0,z28,z2,z3,z4,z6])],[(0,[z0,z1,z41,z2,z3,z4,z6]),(0,[z42,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z43,z2,z3,z4,z6]),(0,[z0,z44,z1,z2,z3,z4,z6]),(1,[z0,z45,z2,z3,z4,z6])]],
   [[(0,[z46,z0,z1,z2,z3,z4,z6]),(0,[z39,z47,z0,z1,z2,z4,z6]),(0,[z48,z0,z49,z2,z3,z4,z6]),(0,[z0,z50,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z51,z6]),(0,[z0,z1,z2,z3,z52,z4,z6])],[(0,[z0,z1,z53,z2,z3,z4,z6]),(0,[z0,z54,z1,z2,z3,z4,z6]),(1,[z0,z55,z2,z3,z4,z6])],[(0,[z56,z0,z1,z2,z57,z4,z6]),(0,[z0,z14,z2,z3,z8,z4,z6]),(0,[z0,z1,z20,z2,z3,z58,z6]),(0,[z0,z1,z59,z2,z3,z4,z6]),(0,[z0,z1,z60,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z61])],[(0,[z0,z1,z2,z62,z3,z4,z6]),(0,[z0,z1,z2,z23,z4,z63,z6]),(0,[z0,z1,z2,z3,z4,z6,z64]),(0,[z0,z65,z1,z2,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z67]),(0,[z0,z1,z68,z69,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z6])],[(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z72,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z73,z6]),(0,[z74,z0,z1,z75,z3,z4,z6]),(0,[z0,z1,z20,z2,z76,z3,z6]),(0,[z0,z1,z77,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z33,z6]),(0,[z78,z0,z1,z2,z3,z4,z6])],[(1,[z79,z80,z2,z3,z4,z6]),(0,[z0,z1,z81,z2,z3,z4,z6]),(0,[z0,z82,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z83,z4,z6]),(0,[z0,z1,z2,z3,z4,z84,z6]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z86,z6]),(1,[z0,z1,z2,z4,z87,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z88,z6]),(0,[z0,z1,z2,z3,z32,z33,z6])],[(0,[z89,z0,z1,z2,z3,z4,z6]),(0,[z90,z0,z1,z2,z3,z4,z6]),(0,[z1,z2,z11,z3,z23,z4,z6]),(0,[z1,z2,z3,z91,z4,z92,z6]),(0,[z0,z1,z2,z3,z4,z93,z6]),(0,[z94,z0,z1,z2,z3,z4,z6]),(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z96,z6])]],
   [[(0,[z0,z1,z97,z2,z3,z4,z6]),(0,[z98,z0,z1,z2,z3,z4,z6])],[(0,[z99,z0,z1,z2,z100,z4,z6]),(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z102,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z103,z3,z4,z6]),(0,[z0,z1,z104,z2,z3,z4,z6]),(0,[z0,z1,z2,z105,z4,z40,z6]),(0,[z0,z1,z2,z106,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z107])],[(0,[z0,z1,z108,z2,z3,z4,z6])],[(0,[z56,z0,z1,z2,z109,z4,z6]),(0,[z110,z0,z111,z2,z3,z4,z6]),(0,[z0,z112,z1,z2,z3,z4,z6]),(0,[z0,z113,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z114,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z115])],[(0,[z0,z1,z2,z100,z3,z4,z6]),(0,[z0,z1,z2,z116,z3,z4,z6]),(0,[z0,z1,z2,z105,z23,z4,z6]),(0,[z0,z1,z2,z105,z11,z4,z6]),(1,[z0,z1,z2,z117,z4,z6]),(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z0,z119,z1,z2,z3,z4,z6]),(0,[z0,z120,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z105,z4,z6])],[(0,[z121,z0,z1,z2,z3,z4,z6]),(0,[z122,z0,z1,z2,z3,z4,z6]),(0,[z0,z123,z1,z2,z3,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z125,z4,z6]),(1,[z0,z1,z126,z3,z127,z6]),(0,[z0,z1,z3,z4,z128,z6,z129]),(0,[z130,z0,z1,z2,z3,z4,z33])],[(0,[z0,z1,z131,z2,z3,z4,z6]),(0,[z132,z0,z1,z2,z3,z4,z6]),(0,[z133,z0,z1,z2,z3,z4,z6]),(0,[z134,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z135,z6]),(1,[z136,z0,z2,z3,z4,z6]),(0,[z0,z1,z137,z3,z4,z63,z6])]],
   [[(0,[z56,z0,z14,z2,z3,z4,z6]),(0,[z0,z1,z2,z138,z3,z4,z6]),(0,[z0,z1,z139,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z107,z6,z140]),(1,[z0,z1,z2,z3,z32,z33])],[(0,[z0,z1,z141,z2,z3,z4,z6]),(0,[z142,z0,z1,z2,z3,z4,z6]),(1,[z39,z0,z1,z2,z4,z143])],[(0,[z144,z0,z1,z2,z3,z4,z6]),(0,[z145,z0,z1,z2,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z91,z6]),(0,[z0,z2,z137,z3,z4,z6,z67]),(0,[z0,z1,z2,z147,z3,z4,z6]),(0,[z0,z1,z126,z2,z4,z148,z6])],[(0,[z149,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z150]),(0,[z0,z151,z1,z2,z3,z4,z6]),(1,[z0,z38,z2,z3,z4,z6]),(0,[z152,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z20,z2,z3,z153,z6]),(0,[z130,z0,z1,z2,z3,z4,z154])],[(0,[z155,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z109,z3,z4,z6]),(0,[z156,z0,z1,z2,z3,z4,z6]),(0,[z157,z0,z2,z3,z58,z4,z6]),(0,[z158,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z159]),(0,[z160,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z161,z4,z6]),(0,[z0,z1,z162,z2,z4,z163,z6])],[(0,[z0,z164,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z165,z6]),(0,[z0,z166,z1,z2,z3,z4,z6]),(0,[z0,z1,z167,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z3,z169,z4,z6]),(0,[z0,z1,z105,z3,z4,z63,z6]),(0,[z39,z0,z1,z2,z4,z63,z6])],[(0,[z170,z1,z111,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z23,z4,z6]),(0,[z0,z1,z2,z3,z4,z171,z6]),(0,[z0,z120,z2,z7,z3,z4,z6]),(0,[z172,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z173,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z174])],[(0,[z0,z1,z2,z3,z4,z6,z175]),(0,[z0,z1,z2,z3,z4,z176,z6])],[(0,[z0,z1,z2,z3,z4,z177,z6]),(0,[z178,z0,z1,z2,z23,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z179])],[(0,[z0,z180,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z181])],[(1,[z56,z182,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z183,z4,z6]),(0,[z184,z0,z2,z3,z91,z4,z6]),(0,[z42,z0,z1,z2,z3,z4,z185]),(0,[z186,z0,z1,z2,z3,z4,z6]),(0,[z0,z187,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z188,z4,z6]),(1,[z48,z0,z49,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z189,z6]),(0,[z0,z1,z2,z3,z4,z6,z190])],[(0,[z191,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z192,z2,z3,z4,z6]),(0,[z0,z1,z2,z193,z3,z4,z6])]],
   [[(0,[z178,z47,z1,z2,z3,z4,z6]),(0,[z194,z0,z1,z2,z3,z4,z6]),(0,[z0,z14,z1,z2,z8,z4,z6]),(0,[z0,z1,z2,z195,z3,z4,z6]),(1,[z66,z0,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z4,z196,z6])],[(0,[z178,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z128,z6]),(1,[z0,z197,z2,z3,z4,z6])],[(0,[z136,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z198]),(0,[z199,z0,z1,z2,z3,z4,z6])],[(0,[z0,z200,z1,z2,z3,z4,z6]),(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z0,z1,z203,z2,z3,z4,z6]),(0,[z204,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z205,z3,z4,z6]),(0,[z42,z0,z1,z2,z3,z4,z31]),(0,[z0,z120,z2,z3,z4,z153,z6])],[(0,[z0,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z207,z4,z6]),(0,[z157,z0,z2,z3,z4,z6,z67]),(0,[z39,z0,z1,z2,z208,z4,z6])],[(0,[z0,z1,z2,z3,z209,z4,z6]),(0,[z0,z1,z2,z3,z4,z210,z6]),(0,[z211,z0,z1,z2,z3,z4,z6]),(0,[z212,z0,z1,z2,z3,z4,z6]),(1,[z74,z0,z1,z75,z3,z6]),(0,[z0,z1,z2,z3,z32,z4,z6])],[(0,[z0,z1,z213,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z214,z6])]],
   [[(0,[z34,z42,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z215]),(0,[z0,z1,z2,z3,z58,z4,z6])],[(0,[z178,z1,z2,z3,z4,z6,z31]),(0,[z216,z0,z1,z2,z3,z4,z6]),(0,[z39,z19,z0,z1,z2,z4,z6])],[(0,[z157,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z217,z6]),(0,[z0,z218,z1,z2,z3,z4,z6])],[(0,[z99,z1,z2,z219,z3,z4,z6]),(0,[z42,z1,z2,z3,z23,z4,z6]),(0,[z0,z1,z2,z220,z3,z4,z6]),(0,[z26,z0,z1,z2,z7,z4,z6]),(0,[z0,z221,z1,z2,z3,z4,z6])],[(0,[z79,z0,z182,z2,z3,z4,z6]),(0,[z0,z1,z2,z222,z3,z4,z6]),(0,[z0,z1,z223,z2,z3,z4,z6]),(0,[z0,z1,z2,z224,z3,z4,z6]),(0,[z0,z1,z75,z3,z4,z127,z6])],[(0,[z178,z1,z2,z11,z3,z4,z6]),(0,[z0,z1,z2,z225,z3,z4,z6]),(0,[z0,z1,z226,z2,z3,z4,z6])],[(0,[z79,z1,z80,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z73,z4,z6])],[(0,[z227,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z228]),(0,[z0,z1,z2,z3,z4,z6,z229])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z230]),(0,[z231,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z232,z2,z3,z4,z6]),(0,[z233,z0,z1,z2,z3,z4,z6]),(0,[z234,z0,z1,z2,z3,z4,z6]),(0,[z235,z0,z1,z2,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z236,z6]),(1,[z0,z1,z2,z57,z4,z6]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z238,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z239]),(0,[z0,z1,z2,z3,z4,z240,z6])],[],[(0,[z99,z0,z1,z2,z83,z4,z6]),(0,[z0,z1,z2,z3,z4,z241,z6]),(0,[z0,z242,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z243])],[(0,[z0,z1,z2,z3,z4,z244,z6]),(0,[z0,z1,z2,z245,z3,z4,z6]),(0,[z0,z1,z2,z76,z3,z4,z6])],[(1,[z0,z1,z2,z4,z163,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z246,z6]),(0,[z0,z120,z2,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z67])],[],[(0,[z0,z1,z2,z3,z6,z247,z31]),(0,[z0,z1,z248,z2,z3,z4,z6]),(0,[z0,z14,z1,z2,z3,z73,z6]),(0,[z0,z1,z249,z2,z3,z4,z6]),(0,[z0,z1,z2,z250,z3,z4,z6])],[(0,[z0,z1,z2,z3,z251,z4,z6]),(0,[z74,z0,z1,z2,z3,z127,z6])],[(1,[z0,z2,z252,z3,z4,z6]),(0,[z253,z0,z1,z2,z3,z4,z6]),(0,[z0,z126,z45,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z143])],[(0,[z254,z0,z1,z2,z3,z4,z6]),(0,[z255,z0,z1,z2,z3,z4,z6]),(1,[z256,z0,z1,z3,z4,z6]),(0,[z48,z0,z2,z3,z4,z153,z6]),(0,[z66,z0,z1,z2,z3,z4,z257]),(0,[z0,z1,z162,z3,z4,z128,z6]),(0,[z0,z1,z2,z258,z3,z4,z6])],[],[(0,[z0,z1,z259,z2,z3,z4,z6]),(0,[z0,z1,z2,z260,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z261,z3,z4,z6]),(0,[z1,z111,z2,z219,z3,z4,z6]),(0,[z0,z1,z2,z3,z262,z4,z6]),(1,[z0,z1,z162,z3,z4,z128]),(1,[z263,z0,z1,z2,z4,z6])],[(0,[z0,z1,z264,z2,z3,z4,z6])],[(0,[z0,z1,z2,z265,z3,z4,z6]),(0,[z0,z1,z2,z266,z3,z4,z6])],[(0,[z267,z0,z1,z2,z3,z4,z6]),(0,[z157,z48,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z257,z6])],[(1,[z0,z1,z2,z3,z4,z236]),(0,[z0,z1,z2,z268,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6]),(0,[z270,z0,z1,z2,z3,z4,z6])],[(0,[z79,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z271,z3,z4,z6]),(0,[z272,z0,z1,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z4,z107,z6]),(0,[z0,z1,z273,z2,z3,z4,z6]),(0,[z0,z274,z1,z137,z3,z4,z6])],[(0,[z0,z1,z2,z3,z8,z4,z6])],[]],
   [[(0,[z0,z1,z2,z275,z3,z4,z6]),(0,[z0,z1,z276,z2,z3,z4,z6]),(0,[z0,z1,z277,z2,z3,z4,z6])],[(0,[z157,z0,z1,z2,z3,z58,z6]),(0,[z0,z1,z126,z3,z4,z127,z6])],[(0,[z0,z1,z2,z278,z3,z4,z6]),(0,[z0,z279,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z7,z3,z4,z6]),(0,[z66,z0,z120,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z280,z6]),(0,[z39,z0,z1,z2,z3,z4,z6])],[(0,[z79,z0,z2,z3,z4,z257,z6]),(0,[z74,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z281,z3,z4,z6])],[(0,[z0,z1,z68,z2,z105,z4,z6]),(0,[z0,z1,z2,z282,z3,z4,z6]),(0,[z19,z0,z1,z20,z2,z3,z6])],[(0,[z102,z0,z1,z2,z3,z91,z6]),(0,[z0,z1,z2,z3,z4,z92,z6]),(0,[z0,z1,z2,z3,z4,z6,z283]),(0,[z0,z1,z2,z3,z284,z4,z6]),(0,[z0,z285,z1,z2,z3,z4,z6]),(0,[z0,z242,z2,z3,z4,z153,z6])],[(0,[z0,z1,z2,z3,z4,z286,z6]),(0,[z287,z0,z1,z2,z3,z4,z6]),(1,[z184,z0,z2,z3,z4,z6]),(0,[z0,z1,z288,z2,z3,z4,z6]),(0,[z289,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z290]),(0,[z99,z0,z1,z2,z3,z4,z6]),(0,[z99,z0,z1,z219,z3,z4,z6]),(0,[z291,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z292,z4,z6]),(1,[z30,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z293,z6]),(0,[z294,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z295]),(0,[z19,z0,z1,z2,z76,z4,z6])]],
   [[(0,[z0,z296,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z163,z6]),(0,[z297,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z298,z2,z3,z4,z6]),(0,[z0,z1,z2,z299,z3,z4,z6]),(0,[z300,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z301,z4,z6])],[(0,[z79,z0,z2,z7,z3,z4,z6]),(0,[z102,z0,z1,z2,z117,z4,z6])],[(0,[z66,z0,z2,z3,z4,z6,z67]),(0,[z302,z0,z1,z2,z3,z4,z6])],[(0,[z303,z0,z1,z2,z3,z4,z6]),(0,[z0,z242,z1,z2,z3,z58,z6]),(0,[z0,z1,z2,z3,z4,z304,z6])],[(0,[z56,z182,z1,z2,z3,z4,z6]),(0,[z56,z0,z2,z3,z4,z257,z6]),(0,[z0,z1,z2,z105,z3,z4,z6]),(0,[z0,z1,z2,z305,z3,z4,z6]),(0,[z19,z0,z1,z2,z3,z40,z6]),(0,[z0,z1,z306,z2,z3,z4,z6])],[(0,[z99,z0,z1,z111,z3,z4,z6]),(0,[z157,z0,z2,z137,z3,z4,z6]),(0,[z0,z1,z2,z307,z3,z4,z6]),(0,[z37,z0,z1,z162,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z308,z6]),(1,[z0,z120,z2,z3,z4,z257]),(0,[z0,z1,z2,z3,z4,z127,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z309,z6]),(0,[z0,z1,z2,z3,z4,z310,z6]),(0,[z0,z1,z2,z3,z4,z311,z6]),(0,[z312,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z126,z2,z75,z3,z6])],[(0,[z0,z1,z313,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z314]),(0,[z0,z1,z2,z315,z3,z4,z6]),(0,[z0,z1,z2,z3,z316,z4,z6])],[(0,[z0,z317,z1,z2,z3,z4,z6]),(1,[z0,z318,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z319,z6]),(0,[z320,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z321]),(0,[z0,z1,z2,z322,z3,z4,z6])],[(0,[z323,z0,z1,z2,z3,z4,z6]),(0,[z324,z0,z1,z2,z3,z4,z6]),(0,[z157,z0,z1,z2,z3,z153,z6])],[(0,[z0,z1,z2,z3,z4,z325,z6])],[(0,[z326,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z327,z6]),(0,[z328,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z329,z3,z4,z6]),(0,[z19,z0,z1,z2,z11,z4,z6]),(0,[z0,z1,z2,z330,z3,z4,z6]),(0,[z331,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z14,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z332,z6]),(0,[z333,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z334,z2,z3,z4,z6]),(1,[z0,z1,z2,z4,z148,z6]),(0,[z0,z1,z2,z335,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z336])],[(0,[z0,z1,z2,z337,z3,z4,z6]),(0,[z0,z1,z2,z338,z3,z4,z6]),(0,[z0,z1,z339,z2,z3,z4,z6]),(0,[z340,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z341,z6]),(0,[z342,z0,z1,z2,z3,z4,z6])]],
   [[(1,[z0,z2,z3,z343,z4,z6]),(0,[z344,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z345])],[(0,[z0,z111,z53,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z257,z185]),(0,[z0,z274,z1,z49,z3,z4,z6]),(0,[z0,z1,z2,z3,z346,z4,z6]),(0,[z39,z26,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z87,z6])],[(0,[z0,z22,z1,z2,z3,z4,z6]),(0,[z0,z274,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z347,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z348]),(0,[z0,z1,z2,z4,z107,z6,z143])],[(0,[z0,z1,z2,z3,z349,z4,z6])],[(0,[z0,z1,z350,z2,z3,z4,z6]),(0,[z351,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z352,z2,z3,z4,z6])],[(0,[z353,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z354,z4,z6]),(0,[z0,z1,z2,z355,z3,z4,z6])],[(0,[z0,z1,z2,z356,z3,z4,z6]),(0,[z1,z2,z3,z4,z185,z6,z31]),(0,[z0,z242,z1,z2,z3,z153,z6]),(0,[z357,z0,z1,z2,z3,z4,z6])],[(0,[z358,z0,z1,z2,z3,z4,z6]),(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z2,z360,z3,z4,z6]),(0,[z361,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z362,z3,z4,z6])]],
   [[(0,[z0,z1,z363,z2,z3,z4,z6]),(0,[z0,z1,z2,z364,z3,z4,z6]),(0,[z0,z1,z2,z3,z117,z4,z6]),(0,[z184,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z257,z31]),(1,[z0,z14,z2,z8,z4,z6]),(0,[z0,z365,z1,z2,z3,z4,z6]),(0,[z19,z0,z1,z2,z105,z4,z6])],[(0,[z102,z1,z2,z3,z4,z92,z6]),(0,[z0,z1,z2,z3,z4,z366,z6]),(0,[z0,z1,z2,z3,z367,z4,z6])],[(0,[z368,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z369,z3,z4,z6]),(0,[z370,z0,z1,z2,z3,z4,z6]),(0,[z0,z371,z1,z2,z3,z4,z6]),(1,[z372,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z154])],[(0,[z373,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z374]),(0,[z0,z1,z2,z3,z4,z375,z6]),(1,[z157,z0,z2,z3,z58,z6]),(0,[z0,z1,z69,z2,z105,z4,z6]),(0,[z0,z1,z2,z125,z3,z4,z6]),(0,[z376,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z377,z2,z3,z4,z6]),(0,[z0,z1,z2,z378,z3,z4,z6]),(0,[z0,z14,z1,z2,z7,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z379]),(0,[z0,z28,z2,z3,z4,z107,z6]),(0,[z0,z1,z2,z3,z4,z6,z380])],[(0,[z0,z1,z381,z2,z3,z4,z6]),(0,[z47,z0,z1,z2,z11,z4,z6]),(0,[z47,z0,z1,z2,z23,z4,z6]),(0,[z0,z1,z382,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z383]),(0,[z0,z1,z2,z3,z384,z4,z6]),(0,[z0,z385,z1,z2,z3,z4,z6]),(0,[z0,z1,z386,z2,z3,z4,z6]),(0,[z387,z0,z1,z2,z3,z4,z6])],[(0,[z30,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z388,z2,z3,z4,z6]),(0,[z0,z389,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z390,z4,z6]),(0,[z0,z1,z2,z3,z391,z4,z6])],[(0,[z392,z0,z1,z2,z3,z4,z6]),(0,[z26,z0,z1,z2,z11,z4,z6]),(0,[z0,z2,z3,z4,z6,z374,z31]),(0,[z0,z1,z2,z3,z4,z6,z393]),(0,[z0,z1,z2,z3,z394,z4,z6])]],
   [[(0,[z395,z0,z1,z2,z3,z4,z6]),(0,[z396,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z397,z2,z3,z4,z6]),(0,[z398,z0,z1,z2,z3,z4,z6])],[(0,[z79,z0,z1,z2,z3,z4,z29]),(0,[z399,z0,z1,z2,z3,z4,z6]),(0,[z79,z0,z2,z137,z3,z4,z6]),(0,[z178,z42,z1,z2,z3,z4,z6]),(0,[z400,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z401,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z402,z6]),(0,[z0,z1,z403,z2,z3,z4,z6])],[(0,[z404,z0,z1,z2,z3,z4,z6]),(0,[z0,z405,z1,z2,z3,z4,z6]),(1,[z170,z1,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z185,z6]),(0,[z0,z2,z137,z3,z4,z153,z6]),(0,[z0,z1,z2,z406,z3,z4,z6]),(0,[z407,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z408,z6]),(0,[z0,z1,z2,z3,z4,z6,z409]),(0,[z410,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z411,z4,z6]),(0,[z0,z1,z2,z3,z412,z4,z6]),(0,[z0,z1,z162,z2,z301,z4,z6]),(0,[z0,z413,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z414]),(0,[z0,z120,z1,z2,z3,z4,z67])],[(0,[z0,z1,z415,z2,z3,z4,z6]),(0,[z416,z0,z1,z2,z3,z4,z6]),(0,[z0,z417,z1,z2,z3,z4,z6])],[(1,[z0,z1,z418,z3,z4,z6]),(1,[z312,z0,z2,z3,z4,z6]),(0,[z419,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z420,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z421,z6]),(0,[z0,z1,z2,z208,z4,z107,z6])],[(0,[z48,z56,z0,z2,z3,z4,z6]),(0,[z256,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z422,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z423])]],
   [[(0,[z424,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z425,z6]),(0,[z0,z1,z2,z3,z4,z6,z426]),(1,[z0,z1,z69,z105,z4,z6]),(0,[z0,z1,z69,z105,z3,z4,z6]),(0,[z19,z0,z1,z2,z4,z107,z6])],[(0,[z56,z0,z182,z2,z3,z4,z6]),(0,[z427,z0,z1,z2,z3,z4,z6]),(0,[z26,z0,z14,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z6,z140])],[(1,[z99,z1,z219,z3,z4,z6]),(0,[z428,z0,z1,z2,z3,z4,z6]),(0,[z39,z187,z1,z2,z3,z4,z6]),(0,[z130,z0,z1,z2,z3,z4,z6])],[(0,[z429,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z430,z3,z4,z6]),(0,[z0,z1,z431,z2,z3,z4,z6])],[(0,[z157,z56,z0,z2,z3,z4,z6]),(1,[z110,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z432,z6]),(0,[z0,z1,z433,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z31,z67]),(0,[z0,z1,z2,z418,z3,z4,z6]),(0,[z0,z1,z2,z434,z3,z4,z6]),(0,[z372,z0,z1,z2,z3,z4,z6])],[(0,[z178,z39,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z435,z3,z4,z6]),(0,[z130,z0,z1,z2,z3,z6,z154])],[(0,[z0,z1,z111,z2,z3,z4,z6]),(0,[z0,z436,z1,z2,z3,z4,z6]),(0,[z437,z0,z1,z2,z3,z4,z6]),(0,[z438,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z439,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z440,z6]),(0,[z0,z441,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z442])],[(1,[z0,z1,z2,z109,z4,z6]),(1,[z0,z1,z2,z3,z6,z247]),(0,[z443,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z1,z2,z3,z4,z6]),(1,[z102,z1,z2,z3,z92,z6]),(0,[z130,z102,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z444])],[(0,[z0,z1,z2,z445,z3,z4,z6]),(0,[z0,z1,z446,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z447,z6])],[(0,[z0,z1,z2,z3,z4,z448,z6]),(0,[z0,z1,z2,z3,z4,z449,z6]),(0,[z0,z1,z2,z3,z4,z450,z6]),(0,[z0,z1,z2,z75,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z451,z6])],[(0,[z452,z0,z1,z2,z3,z4,z6]),(0,[z453,z0,z1,z2,z3,z4,z6])],[(0,[z454,z0,z1,z2,z3,z4,z6]),(0,[z42,z1,z2,z3,z4,z185,z6]),(1,[z0,z274,z137,z3,z4,z6])],[(0,[z0,z1,z2,z455,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z456]),(0,[z0,z1,z2,z3,z4,z457,z6]),(0,[z0,z1,z2,z3,z458,z4,z6]),(0,[z0,z1,z2,z459,z3,z4,z6])],[(1,[z0,z53,z2,z3,z4,z6])]],
   [[(0,[z170,z0,z1,z2,z3,z4,z6]),(1,[z0,z22,z2,z3,z4,z6]),(0,[z460,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z461,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z129])],[(0,[z26,z0,z1,z2,z4,z107,z6]),(0,[z0,z1,z2,z3,z4,z6,z462]),(0,[z0,z1,z2,z3,z463,z4,z6])],[(0,[z0,z1,z2,z3,z464,z4,z6]),(0,[z0,z1,z2,z3,z153,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z465]),(0,[z0,z1,z2,z466,z3,z4,z6]),(0,[z0,z1,z2,z3,z467,z4,z6])],[(0,[z0,z1,z468,z2,z3,z4,z6]),(0,[z0,z469,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z470])],[(0,[z0,z1,z2,z3,z4,z6,z471]),(0,[z0,z1,z472,z2,z3,z4,z6]),(0,[z473,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z474,z6]),(0,[z0,z1,z2,z3,z475,z4,z6]),(0,[z0,z274,z2,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z476,z4,z6])],[(0,[z0,z1,z477,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z57,z4,z6]),(0,[z170,z0,z1,z111,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z478,z6]),(1,[z146,z1,z2,z3,z91,z6]),(0,[z0,z1,z2,z3,z479,z4,z6])]],
   [[(0,[z0,z2,z252,z3,z23,z4,z6]),(0,[z0,z1,z2,z3,z480,z4,z6]),(0,[z0,z1,z2,z3,z4,z481,z6])],[(1,[z0,z1,z2,z3,z241,z6]),(0,[z0,z1,z2,z3,z4,z482,z6]),(0,[z0,z483,z1,z2,z3,z4,z6])],[(0,[z56,z0,z1,z2,z3,z4,z6]),(0,[z182,z1,z80,z2,z3,z4,z6]),(0,[z0,z1,z2,z484,z3,z4,z6]),(0,[z0,z1,z2,z485,z3,z4,z6]),(0,[z0,z486,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z487,z3,z4,z6]),(0,[z0,z488,z1,z2,z3,z4,z6])],[],[(0,[z37,z99,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z489,z4,z6]),(0,[z0,z1,z2,z4,z63,z107,z6]),(0,[z490,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z491,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z492]),(0,[z0,z1,z493,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z494,z6]),(0,[z130,z0,z197,z2,z3,z4,z6])],[(0,[z495,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z208,z3,z4,z143]),(0,[z0,z1,z2,z3,z4,z496,z6]),(0,[z0,z497,z1,z2,z3,z4,z6])],[(1,[z178,z1,z2,z11,z4,z6]),(1,[z0,z1,z2,z225,z4,z6]),(0,[z136,z0,z2,z3,z4,z6,z31]),(0,[z0,z1,z20,z2,z4,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z498])]],
   [[(0,[z0,z1,z499,z2,z3,z4,z6]),(0,[z0,z500,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z153,z6]),(0,[z0,z1,z2,z4,z87,z6,z67])],[(0,[z0,z1,z2,z3,z4,z6,z501])],[(0,[z0,z1,z502,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z503,z4,z6]),(0,[z0,z1,z2,z504,z3,z4,z6])],[(0,[z0,z1,z2,z3,z505,z4,z6]),(0,[z0,z1,z506,z2,z3,z4,z6]),(0,[z66,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z68,z2,z4,z63,z6]),(0,[z0,z1,z2,z3,z4,z507,z6]),(0,[z0,z1,z197,z2,z3,z4,z6])],[(0,[z0,z1,z508,z2,z3,z4,z6]),(0,[z0,z1,z2,z509,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z510,z6]),(0,[z0,z1,z2,z3,z4,z6,z511]),(0,[z0,z1,z2,z3,z33,z6,z154])],[(0,[z0,z1,z49,z2,z3,z4,z6]),(0,[z0,z1,z162,z2,z3,z4,z129]),(0,[z0,z512,z1,z2,z3,z4,z6])],[(0,[z56,z0,z2,z7,z3,z4,z6]),(0,[z47,z1,z2,z3,z23,z4,z6]),(0,[z1,z2,z3,z23,z4,z6,z31]),(0,[z0,z1,z513,z2,z3,z4,z6])]],
   [[(0,[z79,z0,z2,z3,z4,z153,z6]),(0,[z19,z0,z1,z2,z23,z4,z6]),(0,[z0,z1,z514,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z515,z6]),(1,[z0,z1,z2,z208,z4,z107])],[(0,[z79,z48,z0,z2,z3,z4,z6]),(1,[z0,z1,z513,z3,z4,z6])],[(0,[z0,z1,z2,z516,z3,z4,z6]),(0,[z0,z1,z2,z76,z3,z40,z6])],[(0,[z256,z0,z1,z3,z4,z6,z31]),(0,[z0,z517,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z518,z3,z4,z6])],[(0,[z146,z102,z1,z2,z3,z4,z6]),(0,[z519,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z520]),(0,[z74,z0,z1,z126,z3,z4,z6]),(0,[z0,z1,z521,z2,z3,z4,z6]),(0,[z0,z522,z1,z2,z3,z4,z6])],[(0,[z523,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z524,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z525]),(0,[z0,z1,z2,z208,z3,z4,z107])],[(0,[z99,z0,z1,z3,z4,z128,z6]),(0,[z0,z1,z526,z2,z3,z4,z6]),(0,[z0,z1,z527,z2,z3,z4,z6]),(0,[z0,z1,z2,z301,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z528,z6]),(0,[z157,z0,z242,z2,z3,z4,z6]),(0,[z529,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z530,z4,z6]),(0,[z0,z1,z531,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z532]),(0,[z0,z1,z2,z3,z4,z6,z533])],[(0,[z56,z0,z2,z3,z4,z153,z6]),(0,[z0,z1,z2,z3,z4,z6,z534]),(1,[z0,z1,z2,z4,z88,z6]),(0,[z535,z0,z1,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z4,z129])],[(0,[z0,z1,z536,z2,z3,z4,z6]),(0,[z0,z1,z126,z2,z3,z127,z6]),(0,[z0,z1,z2,z3,z4,z6,z537])],[(0,[z0,z1,z2,z137,z3,z4,z6]),(0,[z0,z14,z1,z418,z3,z4,z6])],[(0,[z0,z1,z2,z11,z4,z40,z6]),(0,[z538,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z539,z2,z3,z4,z6]),(0,[z0,z1,z2,z540,z3,z4,z6])],[(0,[z146,z0,z1,z2,z3,z33,z6]),(0,[z0,z120,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z541,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z107,z6]),(0,[z130,z0,z1,z2,z3,z32,z6])],[(0,[z0,z1,z2,z542,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z543]),(0,[z0,z1,z544,z2,z3,z4,z6]),(1,[z0,z180,z1,z2,z4,z6]),(0,[z0,z180,z1,z2,z4,z6,z31]),(0,[z0,z1,z545,z2,z3,z4,z6]),(0,[z546,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z547,z2,z3,z4,z6]),(0,[z0,z1,z548,z2,z3,z4,z6])]],
   [[(0,[z0,z182,z1,z2,z3,z4,z6]),(0,[z0,z14,z1,z2,z11,z4,z6]),(0,[z0,z1,z2,z3,z4,z549,z6]),(0,[z550,z0,z1,z2,z3,z4,z6]),(0,[z263,z0,z1,z2,z3,z4,z6])],[(0,[z551,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z552,z6]),(0,[z37,z0,z1,z3,z4,z6,z129])],[(0,[z26,z0,z1,z2,z23,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z553]),(0,[z0,z554,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z555]),(0,[z556,z0,z1,z2,z3,z4,z6]),(0,[z0,z55,z1,z2,z3,z4,z6])],[(0,[z0,z1,z557,z2,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z92,z6]),(0,[z558,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z559,z3,z4,z6]),(1,[z0,z242,z2,z3,z153,z6]),(0,[z0,z1,z2,z3,z560,z4,z6])],[(0,[z47,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z252,z3,z4,z6]),(0,[z0,z1,z2,z3,z561,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z562]),(0,[z563,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z564,z4,z6])],[(0,[z565,z0,z1,z2,z3,z4,z6]),(0,[z19,z0,z1,z2,z4,z63,z6]),(0,[z0,z1,z566,z2,z3,z4,z6]),(0,[z263,z0,z1,z2,z32,z4,z6])]],
   [[(0,[z79,z56,z1,z2,z3,z4,z6]),(1,[z26,z0,z2,z7,z4,z6]),(0,[z130,z0,z55,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z567,z6]),(0,[z0,z1,z2,z4,z63,z40,z6]),(0,[z0,z1,z2,z3,z4,z148,z6])],[(0,[z0,z1,z2,z568,z3,z4,z6]),(0,[z0,z1,z2,z3,z569,z4,z6]),(0,[z0,z1,z69,z2,z4,z63,z6]),(0,[z0,z1,z162,z2,z3,z4,z128])],[(0,[z0,z1,z2,z3,z4,z570,z6]),(0,[z0,z1,z2,z3,z4,z571,z6]),(0,[z0,z1,z2,z3,z4,z572,z6]),(0,[z0,z1,z126,z2,z3,z4,z6]),(0,[z573,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z574,z3,z4,z6])],[(0,[z0,z1,z2,z3,z575,z4,z6]),(1,[z47,z1,z2,z23,z4,z6]),(0,[z0,z1,z45,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z576]),(0,[z0,z1,z2,z32,z4,z577,z6])],[(0,[z578,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z579,z4,z6])],[(0,[z580,z0,z1,z2,z3,z4,z6]),(0,[z56,z0,z2,z137,z3,z4,z6]),(0,[z0,z1,z581,z2,z3,z4,z6]),(0,[z0,z1,z582,z2,z3,z4,z6]),(0,[z0,z2,z3,z58,z4,z153,z6]),(0,[z0,z2,z3,z4,z153,z6,z67]),(0,[z0,z1,z2,z3,z4,z583,z6]),(1,[z0,z1,z2,z4,z577,z6]),(0,[z0,z1,z584,z2,z3,z4,z6])],[]],
   [[(1,[z0,z1,z2,z100,z4,z6]),(0,[z0,z2,z3,z91,z343,z4,z6]),(0,[z48,z0,z274,z2,z3,z4,z6]),(0,[z585,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z586]),(0,[z0,z1,z2,z3,z32,z4,z154])],[(0,[z0,z1,z2,z3,z4,z587,z6]),(0,[z0,z1,z588,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z589]),(0,[z0,z1,z2,z3,z4,z6,z590]),(0,[z591,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z49,z3,z4,z63,z6]),(0,[z0,z2,z3,z4,z257,z6,z67]),(0,[z0,z1,z126,z2,z125,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z143]),(0,[z592,z0,z1,z2,z3,z4,z6])],[(0,[z79,z0,z14,z2,z3,z4,z6]),(0,[z0,z1,z593,z2,z3,z4,z6]),(0,[z594,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z595])],[(0,[z0,z1,z2,z3,z596,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z597]),(0,[z0,z598,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z599,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z600]),(0,[z48,z0,z1,z137,z3,z4,z6]),(0,[z601,z0,z1,z2,z3,z4,z6]),(0,[z26,z0,z2,z7,z3,z4,z6])],[(0,[z79,z0,z1,z2,z3,z4,z236]),(0,[z0,z1,z2,z3,z4,z602,z6]),(0,[z0,z1,z2,z3,z603,z4,z6]),(0,[z37,z0,z1,z2,z3,z4,z128]),(0,[z0,z1,z604,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z605,z6])],[(0,[z606,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z11,z4,z63,z6]),(0,[z0,z14,z1,z2,z3,z241,z6]),(1,[z0,z1,z68,z4,z63,z6])]],
   [[(0,[z37,z170,z0,z1,z3,z4,z6]),(0,[z0,z49,z2,z137,z3,z4,z6]),(0,[z607,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z608,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z609])],[(0,[z0,z1,z2,z3,z4,z6,z610]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z611,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z219,z3,z4,z6]),(0,[z0,z1,z2,z612,z3,z4,z6])],[(0,[z613,z0,z1,z2,z3,z4,z6]),(0,[z110,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z614,z2,z3,z4,z6]),(0,[z0,z1,z2,z615,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z616,z6]),(0,[z617,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z618])],[(0,[z619,z0,z1,z2,z3,z4,z6]),(0,[z170,z0,z1,z219,z3,z4,z6]),(0,[z0,z14,z1,z2,z4,z107,z6]),(0,[z0,z1,z620,z2,z3,z4,z6])],[(0,[z621,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z622,z3,z4,z6]),(0,[z623,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z68,z2,z3,z4,z6]),(0,[z0,z1,z624,z2,z3,z4,z6])],[(0,[z79,z157,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z625,z4,z6]),(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z626,z2,z3,z4,z6]),(0,[z627,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z628,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z629]),(0,[z0,z1,z69,z137,z3,z4,z6]),(0,[z0,z120,z2,z3,z4,z257,z6])]],
   [[(0,[z0,z1,z2,z3,z630,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z632,z4,z6])],[],[(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z634,z0,z1,z2,z3,z4,z6]),(1,[z130,z0,z1,z2,z3,z154])],[(0,[z146,z1,z2,z3,z91,z4,z6]),(0,[z0,z1,z2,z3,z4,z40,z6])],[(0,[z48,z0,z120,z2,z3,z4,z6]),(0,[z0,z635,z1,z2,z3,z4,z6]),(0,[z19,z0,z1,z20,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z636,z6]),(0,[z637,z0,z1,z2,z3,z4,z6])],[(0,[z0,z638,z1,z2,z3,z4,z6]),(0,[z639,z0,z1,z2,z3,z4,z6]),(0,[z640,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z80,z2,z3,z4,z6]),(0,[z641,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z642,z6]),(0,[z0,z643,z1,z2,z3,z4,z6]),(0,[z0,z1,z644,z2,z3,z4,z6]),(0,[z0,z318,z1,z2,z3,z4,z6]),(0,[z312,z0,z126,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z645,z4,z6]),(0,[z0,z14,z1,z513,z3,z4,z6]),(0,[z0,z1,z2,z3,z58,z40,z6]),(0,[z0,z1,z2,z3,z646,z4,z6]),(0,[z0,z1,z2,z3,z647,z4,z6]),(0,[z0,z1,z2,z3,z4,z577,z6])]],
   [[(0,[z178,z0,z1,z2,z11,z4,z6]),(0,[z34,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z648,z2,z3,z4,z6]),(1,[z0,z1,z2,z76,z40,z6]),(0,[z0,z1,z2,z3,z4,z6,z649])],[(0,[z650,z0,z1,z2,z3,z4,z6]),(0,[z157,z0,z120,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z343,z4,z6]),(0,[z0,z1,z2,z3,z4,z185,z67])],[(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z652,z6])],[(0,[z0,z1,z2,z653,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z654,z6]),(0,[z0,z38,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z40,z107,z6]),(0,[z0,z655,z1,z2,z3,z4,z6])],[(0,[z102,z0,z1,z2,z225,z4,z6]),(0,[z48,z0,z2,z3,z4,z6,z67]),(1,[z37,z0,z1,z3,z4,z129])],[(0,[z79,z0,z80,z2,z3,z4,z6]),(0,[z656,z0,z1,z2,z3,z4,z6]),(0,[z657,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z658,z2,z3,z4,z6]),(0,[z26,z0,z1,z2,z8,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z659]),(0,[z0,z1,z2,z3,z660,z4,z6]),(0,[z0,z1,z661,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z662,z6]),(0,[z170,z0,z1,z3,z4,z128,z6]),(0,[z34,z1,z2,z3,z4,z6,z31]),(0,[z0,z1,z2,z3,z4,z6,z247]),(0,[z0,z1,z2,z663,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z664,z6]),(0,[z0,z1,z2,z3,z4,z6,z665])],[(0,[z48,z0,z1,z49,z3,z4,z6])],[(0,[z48,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z666,z2,z3,z4,z6]),(0,[z37,z0,z403,z2,z3,z4,z6])],[(0,[z0,z1,z2,z667,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z668,z6]),(0,[z0,z1,z20,z2,z3,z4,z6])],[(0,[z0,z1,z669,z2,z3,z4,z6]),(0,[z0,z1,z2,z105,z4,z107,z6])],[(0,[z0,z1,z162,z2,z3,z4,z6])],[(0,[z0,z670,z1,z2,z3,z4,z6])],[(0,[z671,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z672]),(0,[z0,z673,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z208,z3,z4,z6])]],
   [[(0,[z56,z0,z80,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z215,z31]),(0,[z0,z1,z674,z2,z3,z4,z6]),(0,[z74,z0,z1,z2,z75,z3,z6])],[(0,[z675,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z23,z4,z40,z6]),(0,[z102,z0,z1,z2,z3,z33,z6]),(0,[z0,z1,z2,z4,z88,z6,z31]),(0,[z19,z0,z1,z2,z3,z4,z6])],[(0,[z676,z0,z1,z2,z3,z4,z6]),(0,[z677,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z7,z3,z4,z6,z67]),(0,[z0,z1,z678,z2,z3,z4,z6]),(0,[z679,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z76,z4,z40,z6])],[(0,[z0,z1,z2,z3,z4,z680,z6]),(0,[z0,z1,z2,z681,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z215]),(0,[z0,z1,z682,z2,z3,z4,z6]),(0,[z0,z1,z69,z49,z3,z4,z6]),(0,[z0,z14,z120,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z683])],[(1,[z0,z1,z2,z83,z4,z6]),(0,[z0,z1,z684,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z685,z6]),(0,[z0,z1,z69,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z66,z56,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z686]),(0,[z0,z1,z2,z3,z4,z63,z6]),(0,[z39,z0,z1,z2,z4,z6,z143])],[(0,[z0,z1,z2,z687,z3,z4,z6]),(0,[z0,z1,z2,z688,z3,z4,z6]),(0,[z130,z146,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z689,z3,z4,z6]),(0,[z0,z1,z2,z690,z3,z4,z6]),(0,[z0,z1,z691,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z692,z6]),(0,[z102,z0,z1,z2,z3,z92,z6]),(0,[z0,z318,z1,z2,z4,z6,z67])]],
   [[(0,[z0,z1,z693,z2,z3,z4,z6]),(0,[z694,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z695,z2,z3,z4,z6])],[(0,[z696,z0,z1,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z6,z374]),(0,[z0,z1,z68,z3,z4,z63,z6]),(0,[z697,z0,z1,z2,z3,z4,z6]),(0,[z0,z698,z1,z2,z3,z4,z6]),(0,[z37,z0,z1,z2,z3,z4,z6]),(0,[z39,z372,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z91,z4,z6]),(0,[z0,z1,z2,z3,z699,z4,z6]),(0,[z0,z1,z2,z700,z3,z4,z6])],[(0,[z0,z14,z1,z2,z23,z4,z6]),(0,[z178,z0,z1,z2,z4,z107,z6]),(1,[z187,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z140])],[(0,[z0,z1,z2,z3,z701,z4,z6]),(0,[z0,z14,z2,z3,z4,z6,z67]),(0,[z0,z1,z2,z702,z3,z4,z6]),(0,[z703,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z31]),(0,[z0,z1,z2,z3,z4,z704,z6])],[(0,[z0,z1,z705,z2,z3,z4,z6]),(0,[z34,z0,z1,z2,z3,z4,z185]),(0,[z0,z1,z2,z706,z3,z4,z6])],[(0,[z79,z66,z0,z2,z3,z4,z6]),(0,[z99,z170,z1,z2,z3,z4,z6]),(1,[z34,z1,z2,z3,z4,z31]),(1,[z0,z403,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z707,z4,z6]),(0,[z0,z1,z2,z301,z4,z6]),(0,[z0,z2,z708,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z709]),(0,[z19,z0,z1,z710,z2,z6])],[(0,[z0,z1,z711,z2,z4,z6]),(0,[z0,z1,z2,z712,z4,z6]),(0,[z178,z187,z1,z2,z4,z6]),(0,[z0,z2,z713,z3,z4,z6]),(0,[z0,z1,z2,z4,z714,z6]),(0,[z34,z1,z2,z3,z4,z715]),(0,[z256,z0,z3,z4,z6,z374]),(0,[z157,z0,z2,z3,z489,z6]),(0,[z0,z1,z710,z2,z3,z6]),(0,[z19,z0,z1,z2,z52,z6]),(0,[z130,z0,z1,z2,z3,z154])],[(0,[z0,z1,z2,z3,z4,z716]),(0,[z56,z182,z2,z109,z4,z6]),(0,[z0,z1,z2,z717,z4,z6]),(0,[z1,z2,z3,z718,z4,z6]),(0,[z30,z0,z1,z3,z6,z215]),(0,[z0,z1,z719,z3,z4,z6]),(0,[z0,z2,z3,z4,z257,z720]),(0,[z0,z1,z2,z721,z4,z6]),(0,[z0,z722,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z723,z6]),(0,[z724,z0,z2,z3,z4,z6]),(0,[z407,z1,z2,z23,z4,z6]),(0,[z725,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z726,z4,z6]),(0,[z0,z242,z2,z3,z727,z6]),(0,[z0,z1,z2,z4,z402,z107])]],
   [[(0,[z0,z1,z2,z3,z4,z728]),(1,[z1,z2,z729,z4,z6]),(0,[z0,z2,z3,z241,z6,z67]),(0,[z0,z1,z68,z730,z4,z6]),(0,[z0,z731,z2,z3,z4,z6])],[(0,[z0,z1,z2,z732,z4,z6]),(1,[z0,z2,z3,z4,z720]),(0,[z0,z45,z2,z4,z148,z6])],[(0,[z0,z733,z2,z3,z4,z6]),(0,[z0,z734,z2,z3,z4,z6]),(0,[z0,z1,z3,z735,z4,z6]),(0,[z0,z2,z3,z4,z366,z67]),(0,[z0,z120,z2,z3,z4,z257]),(0,[z0,z1,z126,z125,z127,z6])],[(0,[z0,z1,z2,z736,z4,z6]),(0,[z34,z1,z2,z4,z88,z31]),(0,[z0,z14,z418,z8,z4,z6]),(0,[z0,z1,z3,z4,z6,z709])]],
   [[(0,[z0,z2,z3,z354,z153,z6]),(0,[z34,z256,z1,z3,z4,z31]),(0,[z0,z1,z4,z88,z6,z215]),(0,[z0,z1,z737,z2,z4,z6]),(1,[z0,z2,z3,z727,z6]),(0,[z0,z2,z4,z87,z6,z140]),(0,[z0,z1,z3,z4,z709,z129]),(0,[z0,z738,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z739])],[(0,[z56,z182,z2,z3,z4,z6]),(0,[z0,z740,z2,z3,z4,z6]),(0,[z178,z1,z2,z4,z6,z501]),(0,[z0,z1,z741,z3,z4,z6]),(0,[z0,z1,z2,z4,z742,z6]),(0,[z0,z1,z2,z743,z4,z6]),(0,[z0,z318,z1,z2,z4,z6]),(0,[z0,z1,z744,z2,z4,z6]),(0,[z0,z1,z710,z2,z4,z6])],[(0,[z0,z1,z2,z745,z4,z6]),(0,[z1,z111,z746,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z747]),(0,[z48,z0,z49,z3,z4,z6]),(0,[z74,z0,z1,z748,z3,z6]),(0,[z0,z1,z2,z4,z9,z107])],[(0,[z79,z0,z2,z3,z241,z6]),(0,[z0,z749,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z750]),(0,[z0,z1,z2,z751,z4,z6]),(0,[z34,z180,z1,z2,z4,z31]),(0,[z752,z0,z2,z3,z4,z6]),(0,[z66,z0,z2,z3,z4,z67]),(0,[z0,z1,z2,z4,z148,z6]),(0,[z753,z1,z2,z3,z4,z6]),(0,[z0,z754,z2,z3,z4,z6]),(0,[z0,z755,z2,z3,z4,z6]),(0,[z0,z1,z2,z208,z4,z107])],[(0,[z0,z1,z2,z3,z4,z756]),(0,[z66,z0,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z757,z6]),(0,[z0,z1,z2,z222,z40,z6]),(0,[z0,z197,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z2,z3,z759,z6]),(0,[z0,z1,z2,z760,z4,z6]),(0,[z761,z1,z2,z3,z4,z6]),(0,[z0,z418,z3,z4,z6,z67]),(0,[z0,z2,z762,z3,z4,z6])],[(0,[z0,z2,z3,z343,z4,z6]),(0,[z130,z0,z1,z2,z3,z426]),(0,[z39,z0,z1,z418,z4,z6]),(1,[z0,z2,z762,z4,z6]),(0,[z0,z2,z3,z4,z6,z720]),(0,[z0,z1,z2,z632,z40,z6])]],
   [[(0,[z0,z1,z2,z3,z763,z6]),(0,[z0,z1,z2,z3,z764,z6]),(0,[z0,z1,z2,z765,z4,z6]),(0,[z0,z1,z3,z4,z128,z159]),(0,[z0,z14,z2,z252,z4,z6]),(0,[z0,z14,z2,z205,z4,z6]),(0,[z0,z1,z766,z3,z4,z6]),(0,[z34,z1,z3,z4,z215,z31]),(0,[z256,z0,z1,z4,z88,z6])],[(0,[z563,z1,z2,z23,z4,z6]),(0,[z0,z1,z513,z3,z73,z6]),(0,[z0,z1,z767,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z768])],[(0,[z56,z0,z2,z3,z241,z6]),(0,[z0,z769,z2,z3,z4,z6]),(0,[z74,z0,z1,z75,z3,z6]),(0,[z770,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z771,z4,z6])],[(0,[z606,z1,z2,z3,z4,z31]),(0,[z0,z1,z772,z3,z4,z6]),(0,[z180,z187,z1,z2,z4,z6]),(0,[z0,z773,z2,z3,z4,z6]),(0,[z0,z774,z2,z3,z4,z6]),(0,[z37,z0,z403,z3,z4,z129]),(0,[z187,z1,z2,z4,z40,z6])]],
   [[(0,[z0,z2,z3,z4,z6,z775]),(0,[z0,z1,z3,z4,z6,z215]),(0,[z1,z2,z729,z3,z4,z6]),(0,[z26,z0,z2,z252,z4,z6]),(0,[z0,z776,z2,z3,z4,z6]),(0,[z0,z2,z4,z88,z6,z374]),(0,[z0,z180,z1,z2,z6,z247]),(0,[z0,z1,z2,z777,z4,z6]),(0,[z130,z0,z1,z2,z3,z739])],[(0,[z0,z1,z2,z3,z4,z778]),(0,[z0,z1,z2,z3,z779,z6]),(0,[z0,z180,z2,z4,z6,z374]),(0,[z0,z780,z137,z3,z4,z6]),(0,[z0,z1,z2,z4,z781,z6]),(0,[z0,z1,z782,z3,z4,z6]),(0,[z0,z14,z2,z8,z73,z6]),(0,[z0,z2,z3,z727,z4,z6]),(0,[z0,z1,z710,z2,z76,z6]),(0,[z0,z1,z2,z4,z783,z6])],[(0,[z0,z1,z2,z784,z4,z6]),(0,[z0,z1,z2,z785,z4,z6]),(0,[z0,z2,z3,z786,z4,z6]),(0,[z170,z1,z3,z4,z6,z61]),(0,[z0,z1,z2,z4,z88,z6]),(0,[z0,z1,z2,z787,z3,z6]),(0,[z788,z0,z2,z3,z4,z6]),(0,[z1,z2,z789,z3,z4,z6]),(0,[z0,z1,z730,z4,z63,z6]),(1,[z0,z1,z3,z4,z709]),(0,[z0,z1,z2,z3,z32,z739])],[(0,[z0,z790,z2,z3,z4,z6]),(0,[z0,z2,z791,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z792]),(0,[z0,z14,z2,z8,z4,z6]),(0,[z0,z793,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z794]),(0,[z795,z0,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z6,z796]),(0,[z0,z2,z252,z57,z4,z6]),(0,[z0,z797,z2,z3,z4,z6]),(0,[z452,z1,z2,z11,z4,z6]),(0,[z0,z1,z798,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z715]),(0,[z0,z1,z2,z241,z107,z6])],[(0,[z372,z1,z2,z3,z4,z6]),(0,[z529,z1,z2,z23,z4,z6]),(0,[z799,z0,z1,z3,z4,z6]),(0,[z136,z256,z0,z3,z4,z6]),(0,[z800,z1,z2,z3,z4,z6]),(0,[z0,z801,z2,z3,z4,z6])],[(0,[z802,z0,z1,z2,z4,z29]),(0,[z0,z2,z3,z803,z4,z6]),(0,[z804,z0,z2,z3,z4,z6]),(1,[z0,z780,z3,z4,z6]),(0,[z805,z1,z2,z3,z4,z6]),(0,[z157,z0,z2,z3,z58,z6]),(0,[z0,z1,z2,z4,z806,z6]),(0,[z807,z0,z2,z3,z4,z6])],[(0,[z79,z808,z2,z3,z4,z6]),(0,[z0,z180,z1,z2,z4,z6]),(0,[z0,z809,z2,z3,z4,z6])]],
   [[(0,[z0,z14,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z810,z6]),(0,[z0,z1,z2,z3,z718,z6]),(0,[z0,z44,z2,z3,z4,z257]),(0,[z0,z1,z2,z4,z811,z6]),(0,[z812,z1,z2,z3,z4,z6])],[(1,[z1,z746,z3,z4,z6]),(0,[z0,z1,z2,z3,z813,z6]),(0,[z1,z2,z3,z4,z715,z31]),(0,[z34,z1,z2,z3,z247,z31]),(0,[z814,z1,z2,z3,z4,z6]),(1,[z0,z1,z748,z3,z6]),(0,[z0,z815,z2,z3,z4,z6]),(0,[z0,z1,z816,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z29]),(0,[z56,z2,z434,z3,z4,z6]),(0,[z0,z817,z2,z3,z4,z6]),(0,[z48,z0,z288,z3,z4,z6]),(0,[z0,z1,z513,z3,z241,z6]),(0,[z0,z1,z3,z4,z6,z818])],[(0,[z0,z819,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z739])]],
   [[(0,[z0,z2,z3,z4,z6,z374]),(0,[z99,z1,z219,z100,z4,z6]),(0,[z0,z248,z2,z3,z153,z6]),(0,[z0,z1,z2,z3,z6,z820]),(0,[z0,z821,z2,z3,z4,z6])],[(0,[z170,z1,z111,z3,z4,z6]),(0,[z170,z1,z746,z3,z4,z6]),(0,[z47,z2,z252,z23,z4,z6]),(0,[z0,z1,z2,z822,z4,z6]),(0,[z1,z2,z3,z91,z718,z6]),(0,[z0,z1,z2,z823,z4,z6]),(1,[z0,z1,z730,z4,z6]),(0,[z0,z824,z2,z3,z4,z6]),(0,[z187,z1,z2,z105,z4,z6])],[(0,[z48,z0,z363,z3,z4,z6]),(0,[z56,z808,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z825,z6]),(0,[z0,z826,z2,z3,z4,z6]),(0,[z187,z1,z2,z3,z4,z6]),(0,[z0,z180,z1,z4,z6,z215]),(0,[z827,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z828,z4,z6]),(0,[z0,z120,z2,z3,z4,z176]),(0,[z0,z14,z2,z8,z241,z6])],[(0,[z829,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z163,z6]),(0,[z830,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z768])]],
   [[(0,[z0,z1,z2,z3,z4,z831]),(0,[z110,z170,z111,z3,z4,z6]),(0,[z0,z635,z137,z3,z4,z6]),(0,[z26,z0,z2,z7,z4,z6]),(0,[z0,z1,z3,z730,z4,z6]),(0,[z0,z1,z126,z748,z3,z6])],[(0,[z0,z1,z2,z3,z4,z832]),(0,[z0,z1,z2,z3,z833,z6]),(0,[z0,z1,z2,z834,z3,z6]),(0,[z0,z2,z835,z3,z4,z6]),(0,[z312,z0,z2,z3,z4,z6]),(0,[z0,z1,z418,z3,z4,z6]),(0,[z836,z0,z2,z3,z4,z6]),(0,[z837,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z1,z3,z839,z4,z6]),(0,[z136,z0,z2,z3,z4,z67]),(0,[z0,z1,z2,z4,z6,z840]),(0,[z0,z2,z3,z4,z6,z841]),(0,[z842,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z4,z6,z843]),(0,[z34,z136,z2,z3,z4,z31]),(0,[z0,z1,z2,z4,z6,z844]),(0,[z0,z1,z845,z3,z4,z6]),(0,[z0,z1,z69,z105,z4,z6]),(0,[z39,z0,z1,z2,z4,z532]),(0,[z0,z2,z3,z4,z6,z846])]],
   [[(0,[z47,z1,z2,z23,z4,z6]),(0,[z0,z2,z3,z4,z6,z140]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z0,z126,z45,z3,z127,z6]),(0,[z0,z1,z162,z3,z4,z709])],[(0,[z0,z1,z388,z4,z63,z6]),(0,[z0,z1,z2,z3,z848,z6])],[(0,[z849,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z850,z6]),(0,[z0,z1,z2,z4,z577,z6]),(0,[z0,z2,z3,z4,z6,z851])],[(0,[z0,z1,z852,z3,z4,z6]),(0,[z853,z1,z2,z3,z4,z6]),(0,[z130,z0,z197,z2,z3,z154])]],
   [[(0,[z0,z2,z7,z57,z4,z6]),(0,[z133,z0,z2,z3,z4,z67]),(0,[z312,z0,z2,z125,z4,z6])],[(0,[z0,z1,z3,z4,z6,z854]),(0,[z0,z1,z855,z2,z4,z6]),(0,[z490,z1,z2,z11,z4,z6]),(0,[z146,z1,z2,z3,z6,z336]),(0,[z0,z28,z2,z3,z4,z6]),(0,[z0,z120,z2,z3,z4,z450]),(0,[z0,z2,z3,z58,z727,z6])],[(0,[z0,z1,z2,z856,z4,z6]),(0,[z0,z45,z2,z3,z4,z6]),(0,[z66,z0,z2,z3,z4,z720]),(0,[z0,z2,z3,z857,z4,z6]),(0,[z39,z372,z1,z2,z4,z143])],[(0,[z0,z808,z2,z3,z4,z6]),(0,[z99,z598,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z858]),(0,[z859,z0,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z236]),(0,[z0,z14,z2,z660,z4,z6]),(0,[z0,z55,z2,z3,z4,z6]),(0,[z0,z1,z661,z4,z63,z6])],[(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z2,z861,z4,z6]),(0,[z0,z1,z862,z3,z4,z6]),(0,[z0,z1,z2,z699,z40,z6])],[(0,[z0,z274,z780,z3,z4,z6]),(0,[z0,z780,z2,z3,z4,z6]),(0,[z1,z2,z3,z863,z4,z6]),(0,[z0,z14,z513,z8,z4,z6]),(0,[z0,z14,z2,z4,z87,z6]),(0,[z0,z1,z2,z864,z4,z6]),(0,[z0,z1,z2,z4,z107,z768])],[(0,[z0,z1,z2,z865,z4,z6]),(0,[z0,z274,z137,z3,z4,z6]),(0,[z0,z1,z2,z3,z73,z6]),(0,[z0,z1,z866,z3,z4,z6]),(0,[z0,z867,z2,z3,z4,z6])]],
   [[(0,[z79,z80,z2,z3,z4,z6]),(0,[z0,z658,z137,z3,z4,z6]),(0,[z868,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z107,z64]),(0,[z0,z1,z418,z4,z107,z6]),(0,[z0,z1,z2,z4,z87,z6]),(0,[z0,z1,z2,z869,z4,z6]),(0,[z0,z1,z2,z870,z4,z6])],[(0,[z102,z1,z2,z117,z92,z6]),(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z2,z3,z4,z6,z871]),(0,[z0,z45,z2,z125,z4,z6]),(1,[z0,z1,z2,z3,z739])],[(0,[z0,z2,z3,z4,z153,z29]),(0,[z79,z506,z2,z3,z4,z6]),(0,[z0,z53,z2,z3,z4,z6])],[(0,[z48,z0,z2,z3,z4,z29]),(0,[z34,z30,z1,z2,z3,z31]),(0,[z136,z0,z2,z3,z6,z247]),(0,[z0,z1,z2,z3,z872,z6]),(0,[z873,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z874,z3,z4,z6]),(0,[z0,z1,z2,z875,z4,z6]),(0,[z178,z180,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z6,z876]),(0,[z0,z1,z2,z4,z877,z6]),(0,[z0,z1,z2,z3,z4,z878])],[(0,[z0,z1,z2,z879,z4,z6]),(0,[z0,z1,z2,z3,z880,z6]),(0,[z0,z1,z2,z3,z881,z6])],[(0,[z0,z1,z131,z105,z4,z6]),(0,[z0,z882,z2,z3,z4,z6]),(0,[z0,z1,z2,z883,z4,z6]),(0,[z0,z1,z162,z301,z4,z128])],[(0,[z884,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z117,z4,z6]),(0,[z0,z1,z2,z3,z885,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z886]),(0,[z0,z1,z2,z3,z887,z6]),(0,[z0,z2,z3,z888,z4,z6]),(0,[z0,z1,z2,z125,z4,z6]),(0,[z0,z1,z126,z3,z127,z6]),(0,[z39,z0,z1,z2,z4,z768])],[(0,[z0,z889,z2,z3,z4,z6]),(0,[z48,z0,z678,z3,z4,z6]),(0,[z0,z890,z2,z3,z4,z6])],[(0,[z136,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z891,z4,z6]),(0,[z0,z1,z2,z892,z4,z6]),(0,[z0,z1,z2,z3,z893,z6]),(0,[z0,z1,z2,z3,z4,z894]),(0,[z102,z413,z1,z2,z3,z6]),(0,[z0,z895,z2,z3,z4,z6])],[(0,[z256,z30,z0,z1,z3,z6]),(0,[z0,z1,z2,z3,z896,z6]),(0,[z0,z1,z2,z3,z4,z720]),(0,[z130,z0,z55,z2,z3,z154]),(0,[z0,z1,z2,z32,z577,z33])]],
   [[(0,[z39,z0,z1,z2,z4,z589]),(0,[z102,z1,z2,z225,z92,z6]),(1,[z1,z2,z3,z718,z6]),(0,[z0,z2,z3,z4,z6,z897]),(0,[z0,z1,z2,z3,z241,z6]),(0,[z0,z1,z75,z748,z3,z6])],[(0,[z0,z2,z3,z898,z4,z6]),(0,[z0,z899,z2,z3,z4,z6]),(0,[z0,z1,z69,z730,z4,z6]),(0,[z0,z1,z748,z3,z127,z6])],[(0,[z1,z808,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z900,z6]),(0,[z124,z1,z2,z11,z4,z6]),(0,[z0,z1,z3,z901,z4,z6]),(0,[z0,z1,z2,z3,z727,z6])],[(0,[z0,z1,z902,z2,z4,z6]),(0,[z0,z1,z2,z3,z739,z154])]],
   [[(0,[z0,z1,z2,z3,z4,z903]),(0,[z0,z14,z2,z4,z6,z140]),(0,[z26,z187,z1,z2,z4,z6]),(0,[z0,z1,z2,z76,z40,z6])],[(0,[z0,z1,z493,z20,z2,z6])],[(0,[z178,z1,z2,z11,z4,z6]),(0,[z0,z1,z2,z225,z4,z6]),(0,[z0,z2,z3,z727,z153,z6])],[(0,[z0,z1,z2,z4,z904,z6]),(0,[z0,z14,z2,z762,z4,z6]),(0,[z0,z1,z2,z905,z4,z6]),(0,[z0,z28,z2,z208,z4,z107])]],
   [[(0,[z0,z906,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z907,z6]),(0,[z136,z30,z0,z2,z3,z6]),(0,[z26,z0,z2,z4,z6,z140]),(0,[z0,z1,z2,z908,z4,z6])],[(0,[z0,z1,z2,z762,z4,z6]),(0,[z37,z0,z1,z3,z4,z129])],[(0,[z0,z2,z137,z3,z4,z29]),(0,[z0,z1,z909,z3,z4,z6]),(0,[z0,z1,z910,z3,z4,z6]),(0,[z146,z2,z3,z91,z343,z6]),(0,[z0,z1,z2,z748,z3,z6]),(0,[z0,z911,z2,z3,z4,z6]),(0,[z912,z187,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z913])],[(0,[z0,z1,z914,z2,z3,z6]),(0,[z1,z2,z729,z23,z4,z6]),(0,[z178,z1,z2,z524,z4,z6]),(0,[z26,z0,z2,z762,z4,z6]),(0,[z157,z0,z2,z3,z727,z6])]],
   [[(0,[z0,z1,z2,z4,z915,z6]),(0,[z99,z1,z219,z83,z4,z6]),(0,[z0,z1,z2,z916,z4,z6]),(0,[z0,z1,z3,z4,z6,z917]),(0,[z0,z1,z2,z3,z918,z6])],[(0,[z79,z371,z2,z3,z4,z6]),(0,[z56,z674,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z919]),(0,[z0,z522,z2,z3,z58,z6])],[(0,[z0,z920,z2,z3,z4,z6]),(0,[z0,z921,z2,z3,z4,z6]),(0,[z66,z0,z2,z4,z87,z67]),(0,[z0,z1,z2,z730,z4,z6]),(0,[z0,z2,z208,z4,z107,z140])],[(0,[z0,z1,z2,z922,z4,z6]),(0,[z157,z0,z2,z3,z701,z6]),(0,[z0,z1,z2,z923,z4,z6]),(0,[z0,z1,z2,z3,z33,z283]),(0,[z1,z2,z3,z4,z6,z924]),(0,[z0,z1,z20,z710,z2,z6]),(0,[z19,z187,z1,z2,z4,z6])]],
   [[(0,[z0,z925,z2,z3,z4,z6]),(0,[z0,z3,z4,z6,z215,z374]),(0,[z0,z2,z3,z926,z4,z6]),(0,[z0,z1,z513,z3,z4,z6]),(0,[z0,z912,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z927,z6]),(0,[z0,z1,z928,z3,z4,z6]),(0,[z0,z1,z2,z3,z929,z6]),(0,[z0,z1,z2,z930,z4,z6]),(0,[z0,z1,z748,z3,z4,z6])],[(0,[z0,z931,z2,z3,z4,z6]),(0,[z0,z1,z932,z2,z3,z6])],[(0,[z0,z1,z933,z3,z4,z6]),(1,[z808,z2,z3,z4,z6]),(0,[z0,z1,z2,z934,z4,z6]),(0,[z0,z935,z2,z3,z4,z6])]],
   [[(0,[z0,z936,z2,z3,z4,z6]),(0,[z0,z1,z780,z3,z4,z6]),(0,[z0,z488,z137,z3,z4,z6]),(0,[z0,z120,z418,z3,z4,z6]),(0,[z937,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z938,z4,z6]),(0,[z1,z2,z746,z3,z4,z6]),(0,[z19,z0,z1,z468,z2,z6]),(0,[z939,z0,z2,z3,z4,z6])],[(0,[z0,z940,z1,z2,z4,z6]),(0,[z0,z1,z2,z88,z6,z247]),(0,[z941,z0,z1,z2,z4,z6]),(0,[z39,z0,z1,z2,z4,z179]),(0,[z0,z2,z7,z762,z4,z6]),(0,[z0,z1,z942,z3,z4,z6])],[(0,[z0,z1,z943,z2,z4,z6]),(0,[z0,z1,z2,z944,z4,z6])]],
   [[(0,[z0,z1,z2,z83,z4,z6]),(0,[z180,z1,z2,z23,z4,z6]),(0,[z0,z1,z2,z4,z945,z6]),(0,[z1,z2,z3,z946,z4,z6]),(0,[z0,z1,z3,z4,z128,z709])],[(0,[z0,z1,z3,z6,z247,z215]),(0,[z39,z0,z1,z2,z241,z6]),(0,[z0,z1,z2,z3,z947,z6]),(0,[z0,z1,z2,z948,z4,z6]),(0,[z157,z0,z2,z3,z169,z6])],[(0,[z0,z1,z2,z3,z4,z949]),(0,[z256,z0,z180,z1,z4,z6]),(0,[z0,z950,z1,z2,z4,z6]),(0,[z0,z1,z105,z730,z4,z6]),(0,[z951,z1,z2,z3,z4,z6])],[(0,[z0,z952,z2,z3,z4,z6]),(0,[z0,z953,z2,z3,z4,z6]),(0,[z0,z1,z2,z360,z40,z6]),(0,[z0,z1,z521,z105,z4,z6]),(0,[z0,z954,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z418,z23,z4,z6]),(0,[z0,z1,z705,z4,z63,z6]),(0,[z0,z1,z418,z11,z4,z6]),(0,[z0,z1,z955,z3,z4,z6]),(0,[z956,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z957,z6]),(0,[z0,z1,z2,z3,z958,z6])],[(0,[z0,z1,z2,z959,z4,z6]),(0,[z0,z1,z162,z4,z163,z128])],[(0,[z0,z1,z2,z960,z4,z6]),(0,[z0,z1,z3,z4,z6,z961]),(0,[z962,z1,z2,z3,z4,z6]),(0,[z0,z963,z2,z3,z4,z6])],[(0,[z0,z1,z964,z3,z4,z6]),(0,[z0,z1,z965,z3,z4,z6]),(0,[z47,z1,z2,z729,z4,z6]),(0,[z0,z1,z2,z3,z6,z966]),(0,[z19,z0,z1,z508,z2,z6])]],
   [[(0,[z79,z80,z2,z3,z4,z29]),(0,[z0,z14,z2,z57,z4,z6]),(0,[z0,z1,z2,z3,z6,z967]),(0,[z0,z1,z2,z729,z4,z6]),(0,[z0,z968,z2,z3,z4,z6]),(0,[z136,z0,z2,z3,z4,z257]),(0,[z136,z0,z3,z4,z6,z215]),(0,[z969,z1,z2,z3,z4,z6]),(0,[z0,z1,z970,z3,z4,z6])],[(0,[z0,z2,z3,z4,z257,z29]),(0,[z0,z1,z2,z971,z4,z6]),(0,[z0,z2,z3,z4,z6,z972]),(0,[z146,z1,z2,z3,z718,z6]),(0,[z0,z1,z2,z3,z973,z6]),(0,[z0,z1,z2,z4,z107,z686]),(0,[z37,z0,z1,z3,z4,z709]),(0,[z0,z1,z974,z3,z4,z6])],[(0,[z0,z1,z2,z57,z4,z6]),(0,[z808,z80,z2,z3,z4,z6]),(0,[z136,z0,z2,z4,z88,z6]),(0,[z30,z0,z1,z2,z88,z6]),(0,[z0,z1,z386,z105,z4,z6]),(0,[z0,z975,z2,z3,z4,z6])],[(0,[z0,z1,z976,z3,z4,z6]),(0,[z0,z1,z977,z3,z4,z6]),(0,[z47,z187,z1,z2,z4,z6]),(0,[z34,z1,z2,z3,z4,z31]),(0,[z136,z0,z180,z2,z4,z6]),(0,[z0,z403,z2,z3,z4,z6]),(0,[z978,z0,z1,z2,z4,z6]),(0,[z979,z0,z1,z2,z3,z4]),(0,[z980,z187,z2,z3,z4,z6])]],
   [[(0,[z157,z0,z2,z3,z4,z29]),(0,[z0,z1,z2,z4,z981,z6]),(0,[z0,z242,z2,z3,z153,z6]),(0,[z0,z982,z2,z3,z4,z6])],[(0,[z0,z1,z983,z3,z4,z6]),(0,[z0,z2,z3,z6,z247,z374]),(0,[z256,z0,z1,z3,z6,z247]),(0,[z0,z166,z2,z3,z153,z6]),(0,[z0,z2,z3,z4,z720,z67]),(0,[z984,z1,z2,z3,z4,z6]),(0,[z0,z985,z2,z3,z4,z6]),(0,[z0,z1,z986,z3,z4,z6]),(0,[z980,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z987]),(0,[z0,z1,z2,z988,z4,z6]),(0,[z99,z1,z219,z3,z4,z6]),(0,[z0,z1,z2,z989,z4,z6]),(0,[z1,z2,z3,z4,z6,z990]),(0,[z0,z1,z2,z3,z991,z6]),(0,[z0,z1,z418,z3,z73,z6]),(0,[z0,z1,z126,z148,z127,z6]),(0,[z19,z0,z1,z20,z2,z6])],[(0,[z0,z1,z2,z4,z992,z29]),(0,[z0,z1,z993,z3,z4,z6])]],
   [[(0,[z110,z0,z2,z3,z4,z6]),(0,[z0,z2,z7,z3,z4,z29]),(0,[z1,z2,z3,z718,z92,z6]),(0,[z0,z120,z2,z3,z4,z310])],[(0,[z0,z1,z2,z994,z4,z6]),(0,[z995,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z996]),(0,[z136,z0,z2,z3,z4,z29]),(0,[z79,z500,z2,z3,z4,z6]),(0,[z1,z746,z219,z3,z4,z6]),(0,[z0,z1,z2,z4,z997,z6]),(0,[z0,z14,z77,z2,z4,z6]),(0,[z998,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z999,z4,z6])],[(0,[z0,z1,z2,z109,z4,z6]),(0,[z0,z2,z252,z3,z4,z6]),(0,[z170,z111,z53,z3,z4,z6]),(0,[z0,z1000,z2,z3,z4,z6]),(0,[z0,z1001,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z247]),(0,[z34,z2,z3,z4,z374,z31]),(0,[z39,z0,z1,z2,z4,z230])]],
   [[(0,[z0,z1,z2,z3,z4,z1002]),(0,[z256,z0,z1,z3,z4,z6]),(0,[z0,z1003,z2,z3,z4,z6]),(0,[z0,z1004,z2,z3,z4,z6]),(0,[z1,z2,z11,z729,z4,z6]),(0,[z102,z1,z2,z3,z92,z6])],[(0,[z0,z1,z2,z1005,z4,z6]),(0,[z99,z1,z746,z3,z4,z6]),(0,[z0,z1,z2,z4,z1006,z6]),(0,[z47,z22,z2,z23,z4,z6]),(0,[z0,z1,z1007,z3,z4,z6]),(0,[z0,z1,z1008,z2,z3,z6]),(0,[z48,z0,z780,z3,z4,z6]),(0,[z0,z1009,z2,z3,z4,z6])],[(0,[z802,z0,z1,z2,z4,z6]),(0,[z0,z1,z1010,z3,z4,z6]),(0,[z0,z2,z1011,z3,z4,z6]),(0,[z0,z120,z2,z3,z4,z720])],[(0,[z0,z1,z2,z100,z4,z6]),(0,[z37,z0,z1,z3,z4,z543]),(0,[z0,z1,z2,z1012,z4,z6]),(0,[z0,z1,z2,z4,z1013,z6]),(0,[z0,z502,z137,z3,z4,z6]),(0,[z0,z120,z2,z3,z241,z6]),(0,[z0,z2,z3,z1014,z4,z6]),(0,[z312,z0,z126,z3,z127,z6]),(0,[z0,z1,z162,z3,z4,z128]),(0,[z263,z0,z1,z2,z4,z6]),(0,[z1015,z1,z2,z3,z4,z6])]],
   [[(0,[z79,z0,z418,z3,z4,z6]),(0,[z0,z218,z49,z3,z4,z6]),(0,[z187,z1,z2,z4,z63,z6]),(0,[z1,z2,z3,z4,z6,z1016])],[(0,[z0,z2,z3,z4,z257,z610]),(0,[z0,z1,z2,z4,z1017,z6]),(0,[z0,z1,z1018,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1019]),(0,[z0,z1,z2,z4,z1020,z6]),(0,[z1021,z0,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z79,z80,z2,z3,z4,z236]),(0,[z182,z808,z2,z3,z4,z6]),(0,[z1022,z0,z2,z3,z4,z6]),(0,[z0,z49,z780,z3,z4,z6]),(0,[z0,z2,z762,z8,z4,z6]),(0,[z187,z14,z1,z2,z4,z6]),(0,[z1023,z1,z2,z3,z4,z6]),(0,[z1024,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z768,z143])],[(0,[z56,z2,z3,z476,z4,z6]),(0,[z0,z1,z2,z3,z1025,z6]),(0,[z1026,z0,z2,z3,z4,z6]),(0,[z1027,z0,z2,z3,z4,z6]),(0,[z0,z1,z1028,z2,z3,z6]),(0,[z102,z1,z2,z3,z718,z6]),(0,[z184,z146,z2,z3,z91,z6]),(0,[z0,z1,z2,z3,z1029,z6]),(0,[z0,z1,z69,z422,z4,z6]),(0,[z0,z1,z418,z3,z241,z6]),(0,[z0,z1030,z2,z3,z4,z6])]],
   [[(0,[z0,z22,z2,z3,z4,z6]),(0,[z0,z1,z2,z1031,z4,z6]),(0,[z0,z1,z2,z1032,z4,z6]),(0,[z0,z1,z2,z1033,z4,z6])],[(0,[z30,z0,z2,z3,z6,z374]),(0,[z0,z1034,z2,z3,z4,z6]),(0,[z0,z1,z710,z2,z40,z6])],[(0,[z0,z1,z1035,z3,z4,z6]),(0,[z0,z1,z68,z4,z63,z6]),(0,[z0,z1,z2,z4,z1036,z6])],[(0,[z0,z1,z2,z1037,z4,z6]),(0,[z56,z0,z418,z3,z4,z6]),(0,[z0,z1,z2,z1038,z4,z6]),(0,[z0,z1,z2,z23,z241,z6]),(0,[z0,z1,z2,z11,z241,z6]),(0,[z66,z0,z318,z2,z4,z67]),(0,[z0,z1,z264,z4,z63,z6]),(0,[z1039,z1,z2,z3,z4,z6]),(0,[z0,z1040,z2,z3,z4,z6])]],
   [[(0,[z79,z389,z2,z3,z4,z6]),(0,[z0,z1041,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1042]),(0,[z0,z1,z2,z1043,z4,z6]),(0,[z37,z0,z38,z3,z4,z129]),(0,[z0,z1,z1044,z3,z4,z6])],[(0,[z56,z182,z2,z57,z4,z6]),(0,[z0,z1,z746,z3,z4,z6]),(0,[z0,z1045,z2,z3,z4,z6]),(0,[z1046,z1,z2,z3,z4,z6]),(0,[z263,z0,z1,z2,z32,z33])],[(0,[z0,z14,z2,z530,z4,z6]),(0,[z0,z1047,z2,z3,z4,z6]),(0,[z1048,z1,z2,z3,z4,z6]),(0,[z1049,z1,z2,z3,z4,z6]),(0,[z1050,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z1051,z4,z6]),(0,[z56,z2,z3,z4,z6,z314]),(0,[z0,z1,z2,z1052,z4,z6]),(0,[z146,z1,z2,z3,z91,z6]),(0,[z0,z1,z2,z3,z1053,z6]),(0,[z1054,z0,z2,z3,z4,z6]),(0,[z39,z187,z1,z2,z4,z143])]],
   [[(0,[z0,z1,z2,z1055,z3,z6]),(0,[z0,z1056,z2,z3,z4,z6]),(0,[z0,z1,z2,z1057,z4,z6]),(0,[z312,z0,z2,z4,z148,z6]),(1,[z0,z1,z710,z2,z6]),(0,[z0,z1,z2,z3,z32,z33])],[(0,[z0,z1,z2,z3,z4,z1058]),(0,[z184,z0,z2,z3,z4,z6]),(0,[z178,z1,z2,z729,z4,z6]),(0,[z342,z1,z2,z3,z4,z31]),(0,[z30,z0,z180,z1,z2,z6]),(0,[z1059,z1,z2,z3,z4,z6]),(0,[z0,z1060,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z4,z143])],[(0,[z0,z1,z2,z4,z992,z6]),(0,[z0,z1,z2,z1061,z4,z6]),(0,[z30,z0,z1,z2,z3,z6]),(0,[z132,z0,z2,z3,z4,z67]),(0,[z0,z2,z7,z4,z87,z6]),(0,[z0,z1,z2,z1062,z4,z6]),(1,[z0,z1,z2,z4,z768]),(0,[z0,z1,z2,z208,z4,z768])],[(0,[z0,z1,z2,z1063,z4,z6]),(0,[z1064,z0,z1,z2,z3,z4]),(0,[z0,z38,z2,z3,z4,z6]),(0,[z0,z1,z1065,z3,z4,z6]),(0,[z0,z173,z2,z3,z153,z6]),(0,[z0,z1,z2,z3,z33,z739])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 561) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 561).take 472) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1033)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [561, 472] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 102).take 26).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [102, 26] = true :=
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

end PEqualNP.Outside.L_meta_45838

theorem PEqualNP.Outside.L_meta_45838 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4006135808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4006135808) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45838.solve