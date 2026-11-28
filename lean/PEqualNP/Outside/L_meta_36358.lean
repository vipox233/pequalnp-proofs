import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36358

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
  Nat.testBit (4278124200 * 2 ^ 32 + 4274846856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x14040c0cd8723228#64 ++ 0x228081819b0e4645#64 ++ 0xfa141c1ff8f2327e#64 ++ 0xff428383ff1e464f#64 : BitVec 256),
   (0x080822222004c0d1#64 ++ 0x410104444400981a#64 ++ 0xf7286262311fc3ff#64 ++ 0xdee50c4c4623f87f#64 : BitVec 256),
   (0x500d82834a1c5461#64 ++ 0x8a01b05069438a8c#64 ++ 0xafcf8383ce1c7c65#64 ++ 0xb5f9f07079c38f8c#64 : BitVec 256),
   (0xa070015405a02b02#64 ++ 0x140e002a80b40560#64 ++ 0x9ff003fc0fe07f87#64 ++ 0xf3fe007f81fc0ff0#64 : BitVec 256),
   (0xc076d4000fdb0002#64 ++ 0x180eda8001fb6000#64 ++ 0x7e7ffc000fff8003#64 ++ 0x8fcfff8001fff000#64 : BitVec 256),
   (0x00fb7bfbb0000003#64 ++ 0xe01f6f7f76000000#64 ++ 0xfefffffff0000000#64 ++ 0x7fdffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x9720026001004387 0xd2e4004c00200870

def z1 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf7286262311fc3ff 0xdee50c4c4623f87f

def z2 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff11fc3ff 0xfffffffffe23f87f

def z3 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa141c1ff8f2327e 0xff428383ff1e464f

def z4 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383ce1c7c65 0xb5f9f07079c38f8c

def z5 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff003fc0fe07f87 0xf3fe007f81fc0ff0

def z6 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z7 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff0000000 0x7fdffffffe000000

def z8 : W := mkw 0xd476d4044ffb322a 0x1a8eda8089ff6645 0x7e7ffc000fffb27f 0x8fcfff8001fff64f

def z9 : W := mkw 0x40098283020c4441 0x8801305060418888 0x05cb8380060c4c01 0x00b9707000c18980

def z10 : W := mkw 0x1004000048101020 0x0200800009020204 0xaa040003c8103064 0xb54080007902060c

def z11 : W := mkw 0xc072d40007cb0002 0x180e5a8000f96000 0x547bfc0007ef8003 0x0a8f7f8000fdf000

def z12 : W := mkw 0x0070095890000002 0x200e012b12000000 0xfef41ffff0000000 0x7fde83fffe000000

def z13 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x600ffc00001f8000 0x0c01ff800003f000

def z14 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x08d79d9dc0000000 0x211af3b3b8000000

def z15 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x2e5f9c000efc0001 0x85cbf38001df8000

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0x0e4000000e000001 0x81c8000001c00000

def z17 : W := mkw 0x0000000000000000 0x0000000000000000 0x8fc003800e007c05 0xb1f8007001c00f80

def z18 : W := mkw 0x0009028300000001 0x8001205060000000 0xaecf8383c0000000 0x35d9f07078000000

def z19 : W := mkw 0x00f27978b0000002 0x601e4f2f16000000 0x50307c7c30000000 0x4a060f8f86000000

def z20 : W := mkw 0x50fffbfbfa1c5463 0xea1fff7f7f438a8c 0xfffffffffe1c7c65 0xffffffffffc38f8c

def z21 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc023fff827f 0xdfcfff8047fff04f

def z22 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x05286260010dc181 0x00a50c4c0021b830

def z23 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x08141c1dc8e03000 0x21028383b91c0600

def z24 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x08d0019c0ee03c00 0x211a003381dc0780

def z25 : W := mkw 0xb4740d5cddf23b2a 0x368e81ab9bbe4765 0xfff41ffffff27fff 0xfffe83fffffe4fff

def z26 : W := mkw 0xf0fffbffffbc7f63 0xfe1fff7ffff78fec 0xfffffffffffc7fe7 0xffffffffffff8ffc

def z27 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x54fbfffc30000000 0x4a9f7fff86000000

def z28 : W := mkw 0x540d8e8fda7e7669 0xaa81b1d1fb4fcecd 0xffdf9f9ffefe7e7f 0xfffbf3f3ffdfcfcf

def z29 : W := mkw 0x40098283020c4441 0x8801305060418888 0x000b8000000c0000 0x0001700000018000

def z30 : W := mkw 0x007903d300000003 0x800f207a60000000 0xbeff83ffc0000000 0x77dff07ff8000000

def z31 : W := mkw 0x14000c0cd0623228 0x228001819a0c4645 0xd0101c1ff0e2327e 0x7a020383fe1c464f

def z32 : W := mkw 0x140c2e2ef8723229 0x628185c5df0e4645 0xfe3c7e7ff8f2327e 0xffc78fcfff1e464f

def z33 : W := mkw 0x0001008100000000 0x8000201020000000 0x08c78181c0000000 0x2118f03038000000

def z34 : W := mkw 0x00fb73f320000003 0xc01f6e7e64000000 0x04ebe3e000000000 0x009d7c7c00000000

def z35 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x08c78181ce003c00 0x2118f03039c00780

def z36 : W := mkw 0x0400040400622208 0x00800080800c4441 0x0000000000e2021a 0x00000000001c4043

def z37 : W := mkw 0x0008020200044041 0x0001004040008808 0x05080200000c4001 0x00a1004000018800

def z38 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ad0019c0ee03e06 0xf35a003381dc07c0

def z39 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0x60041c03f0120078 0x0c0083807e02400f

def z40 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x818003fc00007f84 0x7030007f80000ff0

def z41 : W := mkw 0x8072540005c30002 0x100e4a8000b86000 0x50307c0001e38002 0x0a060f80003c7000

def z42 : W := mkw 0x180922a36004d4f1 0xc30124546c009a9e 0xf7a863e3f11fffff 0xfef50c7c7e23ffff

def z43 : W := mkw 0x540d86874a7e7669 0x8a81b0d0e94fcecd 0xafcf8383cefe7e7f 0xb5f9f07079dfcfcf

def z44 : W := mkw 0x1c0c2e2ef876f2f9 0x638185c5df0ede5f 0xff3c7e7ff9fff3ff 0xffe78fcfff3ffe7f

def z45 : W := mkw 0xc07ed6020fdf4043 0x180fdac041fbe808 0xff7ffe020fffc067 0x9fefffc041fff80c

def z46 : W := mkw 0x0800202020008090 0x4100040404001012 0x502060603103839a 0x4a040c0c06207073

def z47 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffefe3e3ff1fffff 0xfffdfc7c7fe3ffff

def z48 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe3c7c1ff9ffb27f 0xffc78f83ff3ff64f

def z49 : W := mkw 0x180c22226814d0f1 0x430184444d029a1e 0xff2c6263f91ff3ff 0xffe58c4c7f23fe7f

def z50 : W := mkw 0xc0fffffbbfdb0003 0xf81fffff77fb6000 0xfeffffffffff8003 0xffdffffffffff000

def z51 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xafcf8383cf1fffff 0xb5f9f07079e3ffff

def z52 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x55286260310fc39b 0x4aa50c4c0621f873

def z53 : W := mkw 0x0008222220000001 0x4001044444000000 0xf628626230000000 0x5ec50c4c46000000

def z54 : W := mkw 0x0070015000000002 0x000e002a00000000 0x9ef003fc00000000 0x73de007f80000000

def z55 : W := mkw 0x0072500000000002 0x000e4a0000000000 0x7e7ffc0000000000 0x0fcfff8000000000

def z56 : W := mkw 0x0000000400202200 0x0000000080040440 0x0000000008e03206 0x80000000011c0640

def z57 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff10dc181 0x7ffffffffe21b830

def z58 : W := mkw 0xc80484000fdfc0d0 0x1900908001fbf81a 0x010000000fffc3ff 0x8020000001fff87f

def z59 : W := mkw 0x04000c0c90622208 0x20800181920c4441 0x50101c1c30e2021a 0x4a020383861c4043

def z60 : W := mkw 0xd07fd6834fdf5463 0x9a0ffad069fbea8c 0xffffff83cffffc67 0xbffffff079ffff8c

def z61 : W := mkw 0x080000000004c0d0 0x010000000000981a 0x01000000011fc3ff 0x802000000023f87f

def z62 : W := mkw 0x1404040048521028 0x02808080090a4205 0x0000000000120078 0x000000000002400f

def z63 : W := mkw 0x8070015005800002 0x100e002a00b00000 0x9ef003fc0fe00003 0xf3de007f81fc0000

def z64 : W := mkw 0xa87823722584c9d3 0x550f046e44b0993a 0x05e863e0070dcd81 0x00bd0c7c00e1b9b0

def z65 : W := mkw 0x0008020200044041 0x0001004040008808 0xafc803820e1c7c65 0xb5f9007041c38f8c

def z66 : W := mkw 0x2000015000000900 0x0400002a00000120 0x018003e000004d80 0x0030007c000009b0

def z67 : W := mkw 0x0009028300000001 0x8001205060000000 0xafcf8383ce007c05 0xb5f9f07079c00f80

def z68 : W := mkw 0xa0fb7bffb5a02b03 0xf41f6f7ff6b40560 0xffffffffffe07f87 0xfffffffffffc0ff0

def z69 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x08579c000fff8003 0x810af38001fff000

def z70 : W := mkw 0x080922a32004c0d1 0xc10124546400981a 0xffefe3e3f11fc3ff 0xfffdfc7c7e23f87f

def z71 : W := mkw 0xf07581d54fb83f22 0x9e0eb03aa9f707e4 0x9ff783fdcfe07f87 0xf3fef07fb9fc0ff0

def z72 : W := mkw 0xc87af222278dc0d3 0x590f5e4444f1b81a 0x056be260070dc181 0x00ad7c4c00e1b830

def z73 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xffffff800ffffc07 0xbffffff001ffff80

def z74 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x703ffc0001ff8002 0x0e07ff80003ff000

def z75 : W := mkw 0x1009028340045461 0x8201205068008a8c 0x81800383c0007c64 0x3030007078000f8c

def z76 : W := mkw 0x400480000a180000 0x0800900001430000 0x2e4f80000e1c0001 0x85c9f00001c38000

def z77 : W := mkw 0xa000015405a02b00 0x1400002a80b40560 0x818003fc0fe07f87 0xf030007f81fc0ff0

def z78 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff11f8003 0xffdffffffe23f000

def z79 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf7286262310dc181 0x5ee50c4c4621b830

def z80 : W := mkw 0x0004040008520000 0x00008080010a4000 0x0000000008f20002 0x80000000011e4000

def z81 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xbfef83e3cf1c7fe7 0xf7fdf07c79e38ffc

def z82 : W := mkw 0xd476dc0cdffb322a 0x3a8edb819bff6645 0xfe7ffc1fffffb27f 0xffcfff83fffff64f

def z83 : W := mkw 0x1404040448723228 0x02808080890e4645 0x0000000008f2327e 0x80000000011e464f

def z84 : W := mkw 0xb4740d5cddf23b2a 0x368e81ab9bbe4765 0x9ff41ffdcfe07f87 0xf3fe83ffb9fc0ff0

def z85 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x08579c000ee00000 0x010af38001dc0000

def z86 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x60086002301f8078 0x0c010c004603f00f

def z87 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x8fc78381ce007c05 0xb1f8f07039c00f80

def z88 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0xf62ffe63f0000000 0x5ec5ffcc7e000000

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0x010000000e007c05 0x8020000001c00f80

def z90 : W := mkw 0xc072d00007890002 0x180e5a0000f12000 0x0043800006000000 0x0008700000c00000

def z91 : W := mkw 0xd47fde8fdfff766b 0xba8ffbd1fbffeecd 0xffffff9ffffffe7f 0xfffffff3ffffffcf

def z92 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0x09c78181ce1c7c65 0xa138f03039c38f8c

def z93 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0xaecf8383ce003c00 0x35d9f07079c00780

def z94 : W := mkw 0x0000080890000000 0x2000010112000000 0xfa141c1ff0000000 0x7f428383fe000000

def z95 : W := mkw 0x540d8e8fda7e7669 0xaa81b1d1fb4fcecd 0xafdf9f9fcefc7c65 0xb5fbf3f3f9df8f8c

def z96 : W := mkw 0x08082a2ab004c0d1 0x610105455600981a 0xff3c7e7ff11fc3ff 0xffe78fcffe23f87f

def z97 : W := mkw 0xd4fffffffffb322b 0xfa9fffffffff6645 0xfeffffffffffb27f 0xffdffffffffff64f

def z98 : W := mkw 0x500480004a181420 0x0a00900009430284 0x000000000e003c00 0x0000000001c00780

def z99 : W := mkw 0x14ff7ffff872322b 0xe29fefffff0e4645 0xfefffffff8f2327e 0xffdfffffff1e464f

def z100 : W := mkw 0x1001008140001420 0x8200201028000284 0x00800181c0003c00 0x2010003038000780

def z101 : W := mkw 0xa878237625a4ebd3 0x550f046ec4b49d7a 0xfff863fe3fffffff 0xffff0c7fc7ffffff

def z102 : W := mkw 0x08f27978b0008092 0x611e4f2f16001012 0x50307c7c3103839a 0x4a060f8f86207073

def z103 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a141c0000000000 0x0f42838000000000

def z104 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0xe08ffffff0000000 0x7c11fffffe000000

def z105 : W := mkw 0x8070000005800002 0x100e000000b00000 0x1e7000000fe00003 0x83ce000001fc0000

def z106 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x05286260011fc3ff 0x80a50c4c0023f87f

def z107 : W := mkw 0x500480004a1c5460 0x0a00900009438a8c 0x010000000e1c7c65 0x8020000001c38f8c

def z108 : W := mkw 0x94765c0cddf3322a 0x328ecb819bbe6645 0xfa347c1ff9f3b27e 0xff468f83ff3e764f

def z109 : W := mkw 0xd4048c0cdffb3228 0x3a8091819bff6645 0xfa141c1fffffb27f 0xff428383fffff64f

def z110 : W := mkw 0xc87ef6222fdfc0d3 0x590fdec445fbf81a 0xff7ffe623fffc3ff 0xdfefffcc47fff87f

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7286260011fc387 0xdee50c4c0023f870

def z112 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x2e4f8003ce1c0061 0x85c9f00079c3800c

def z113 : W := mkw 0x00f351d100000002 0x801e6a3a20000000 0x00c3818000000000 0x0018703000000000

def z114 : W := mkw 0xc00484000fdb0000 0x1800908001fb6000 0x762860000fff8003 0x8ec50c0001fff000

def z115 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x1030007c01e00382 0x4206000f803c0070

def z116 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffff01c4065 0xfffffffffe03880c

def z117 : W := mkw 0x8072540005c30002 0x100e4a8000b86000 0x76387c0001ff8003 0x8ec70f80003ff000

def z118 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x2ecf8181ce1c3c01 0xa5d9f03039c38780

def z119 : W := mkw 0x50098283420c5461 0x8a01305068418a8c 0x85cb8383c60c7c65 0x30b9707078c18f8c

def z120 : W := mkw 0xf00480044fbc7f60 0x1e00900089f78fec 0x010000000ffc7fe7 0x8020000001ff8ffc

def z121 : W := mkw 0xc0f7ddd99fdb0002 0xb81efbbb33fb6000 0x7efffd9dcfff8003 0xafdfffb3b9fff000

def z122 : W := mkw 0x088b7aabb004c0d1 0xe1116f557600981a 0xf72ffe63f11fc3ff 0xdee5ffcc7e23f87f

def z123 : W := mkw 0xe076d4040ffb2b02 0x1c0eda8081ff6560 0x7f7ffc000fffff87 0x8fefff8001fffff0

def z124 : W := mkw 0x180922a36004d4f1 0xc30124546c009a9e 0x818003e3f0007ffc 0x7030007c7e000fff

def z125 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x9b9003fc08e07f86 0xf372007f811c0ff0

def z126 : W := mkw 0xd00d86834fdf5461 0x9a01b0d069fbea8c 0xafcf8383cffffc67 0xb5f9f07079ffff8c

def z127 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x0cfffffdc0000000 0x219fffffb8000000

def z128 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x28cf8183ce1c3c60 0x2519f03079c3878c

def z129 : W := mkw 0xb4ff7ffffdf23b2b 0xf69fefffffbe4765 0xfffffffffff27fff 0xfffffffffffe4fff

def z130 : W := mkw 0x0000000000000000 0x0000000000000000 0x8ec0038000000000 0x31d8007000000000

def z131 : W := mkw 0x400484000a5a0000 0x08009080014b4000 0x7e5f9c000efe0003 0x8fcbf38001dfc000

def z132 : W := mkw 0xa0fb73f725a02b03 0xd41f6e7ee4b40560 0x9ffbe3fc0fe07f87 0xf3ff7c7f81fc0ff0

def z133 : W := mkw 0x8072540005c30002 0x100e4a8000b86000 0x00101c0000e00000 0x00020380001c0000

def z134 : W := mkw 0x280823762024ebd1 0x4501046ec4049d7a 0x818003fe30007ffc 0x7030007fc6000fff

def z135 : W := mkw 0x4000800002080000 0x0800100000410000 0x044b8000060c0001 0x0089700000c18000

def z136 : W := mkw 0x1c0c26266876f2f9 0x438184c4cd0ede5f 0xf728626239fff3ff 0xdee50c4c473ffe7f

def z137 : W := mkw 0x00892bfbb0000001 0xe011257f76000000 0x808003fff0000000 0x7010007ffe000000

def z138 : W := mkw 0xc00484000fdb0000 0x1800908001fb6000 0x000000000fff8003 0x8000000001fff000

def z139 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0xfad79d9ff0000000 0x7f5af3b3fe000000

def z140 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0x600fe003f01f8078 0x0c01fc007e03f00f

def z141 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xa7286262011dc1e5 0x94e50c4c4023b83c

def z142 : W := mkw 0x1400080cd0203228 0x228001019a040645 0x8000001ff000327c 0x70000003fe00064f

def z143 : W := mkw 0xc072d00007890002 0x180e5a0000f12000 0x046be000070d8001 0x008d7c0000e1b000

def z144 : W := mkw 0x0009028300044041 0x8001205060008808 0xafcf8383c01c4065 0xb5f9f0707803880c

def z145 : W := mkw 0xa000000405a02b00 0x1400000080b40560 0x972002600fe07f87 0xd2e4004c01fc0ff0

def z146 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x210f8003ce1c7c65 0x8421f00079c38f8c

def z147 : W := mkw 0x100c020248145061 0x0201804049028a0c 0xaf0c0203c81c7065 0xb5e1804079038e0c

def z148 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x15f003fc07e04f83 0x42be007f80fc09f0

def z149 : W := mkw 0x080822262024e2d1 0x41010444c4049c5a 0xff38627e39fff3ff 0xffe70c4fc73ffe7f

def z150 : W := mkw 0x94740c0cddf2322a 0x328e81819bbe4645 0xfe741c1ffff2327f 0xffce8383fffe464f

def z151 : W := mkw 0x08fb73f32004c0d3 0xc11f6e7e6400981a 0x05ebe3e0010dc181 0x00bd7c7c0021b830

def z152 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x05e003e007004d81 0x00bc007c00e009b0

def z153 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x70286062311f83fa 0x4e050c0c4623f07f

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x76286000011f8003 0x8ec50c000023f000

def z155 : W := mkw 0xe07983d707ac6f43 0x9c0f307ae0f58de8 0x9ffb83fc0fec7f87 0xf3ff707f81fd8ff0

def z156 : W := mkw 0x00892bfbb0000001 0xe011257f76000000 0xfa941ffff0000000 0x7f5283fffe000000

def z157 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfefffffff103839a 0x7fdffffffe207073

def z158 : W := mkw 0xc07480000f980002 0x180e900001f30000 0x3e7f80000ffc0003 0x87cff00001ff8000

def z159 : W := mkw 0x1004040048521020 0x02008080090a4204 0xfa141c03c8f23066 0xbf428380791e460c

def z160 : W := mkw 0x00f27978b0000002 0x601e4f2f16000000 0xdef07ffc30000000 0x7bde0fff86000000

def z161 : W := mkw 0xa0f2797cb5a02b02 0x741e4f2f96b40560 0xdff07ffc3fe07f87 0xfbfe0fff87fc0ff0

def z162 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x81000262300043fc 0x5020004c4600087f

def z163 : W := mkw 0xc0fbfbfbb7890003 0xf81f7f7f76f12000 0xfefffffff70d8001 0x7fdffffffee1b000

def z164 : W := mkw 0xa0f2797cb5a02b02 0x741e4f2f96b40560 0x50307c7c31e00382 0x4a060f8f863c0070

def z165 : W := mkw 0x1404040448723228 0x02808080890e4645 0x9a10001c08f2327e 0xf3420003811e464f

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0xf20000023012027e 0xde4000004602404f

def z167 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x0df003fc0fe07d81 0x21be007f81fc0fb0

def z168 : W := mkw 0x10fb7bfbf0045463 0xe21f6f7f7e008a8c 0xfffffffff0007c64 0x7ffffffffe000f8c

def z169 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xffefe3e3fe1c7c65 0xfffdfc7c7fc38f8c

def z170 : W := mkw 0x507d83d34a1c5463 0x8a0fb07a69438a8c 0xbfff83ffce1c7c65 0xf7fff07ff9c38f8c

def z171 : W := mkw 0x500d86834a5e5461 0x8a01b0d0694bca8c 0xffdf9f83cefe7c67 0xbffbf3f079dfcf8c

def z172 : W := mkw 0xd40484044ffb3228 0x1a80908089ff6645 0x000000000fffb27f 0x8000000001fff64f

def z173 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0xeecfff83f0000000 0x3dd9fff07e000000

def z174 : W := mkw 0x507fd2834a1c5463 0x8a0ffa5069438a8c 0xffffff83ce1c7c65 0xbffffff079c38f8c

def z175 : W := mkw 0x0800202020008090 0x4100040404001012 0x0020606001018180 0x00040c0c00203030

def z176 : W := mkw 0x14ff7ffff872322b 0xe29fefffff0e4645 0xfefffffff8e03000 0x7fdfffffff1c0600

def z177 : W := mkw 0x00f27978b0000002 0x601e4f2f16000000 0xfa347c7ff0000000 0x7f468f8ffe000000

def z178 : W := mkw 0x54048c0cda7a3228 0x2a8091819b4f4645 0xfe5f9c1ffefe327f 0xffcbf383ffdfc64f

def z179 : W := mkw 0x0008222220000001 0x4001044444000000 0x0428626000000000 0x00850c4c00000000

def z180 : W := mkw 0xa870015405a4ebd2 0x150e002a80b49d7a 0x9ff003fc0fffffff 0xf3fe007f81ffffff

def z181 : W := mkw 0xc876d4000fdfc0d2 0x190eda8001fbf81a 0x7f7ffc000fffc3ff 0x8fefff8001fff87f

def z182 : W := mkw 0xa000000405a02b00 0x1400000080b40560 0x9b10001c0fe07f87 0xf362000381fc0ff0

def z183 : W := mkw 0x10892bfbf0045461 0xe211257f7e008a8c 0x818003fff0007c64 0x7030007ffe000f8c

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x1020006001000382 0x4204000c00200070

def z185 : W := mkw 0xd07d82834f9c5463 0x9a0fb05069f38a8c 0xbfff8383cffc7c67 0xb7fff07079ff8f8c

def z186 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0xfa1ffc1ff0000000 0x7f43ff83fe000000

def z187 : W := mkw 0xe0ffffffbffb2b03 0xfc1ffffff7ff6560 0xffffffffffffff87 0xfffffffffffffff0

def z188 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x7efffd9dc0000000 0x2fdfffb3b8000000

def z189 : W := mkw 0x0004040408722200 0x00008080810e4440 0xfa141c1c08f23206 0xff428383811e4640

def z190 : W := mkw 0xc076d5500fdb0002 0x180edaaa01fb6000 0xfefffffc0fff8003 0xffdfffff81fff000

def z191 : W := mkw 0x0000000000000000 0x0000000000000000 0xa200000200100064 0x944000004002000c

def z192 : W := mkw 0xb4740d5cddf23b2a 0x368e81ab9bbe4765 0xfad41d9ffef23e7e 0xff5a83b3ffde47cf

def z193 : W := mkw 0x0c082e2eb066e2d9 0x618105c5d60cdc5b 0xf7387e7e31ffc3ff 0xdee70fcfc63ff87f

def z194 : W := mkw 0x807654000dd30002 0x100eca8001ba6000 0x7a347c0009f38002 0x8f468f80013e7000

def z195 : W := mkw 0xb07903d745a47f63 0x960f207ae8b48fec 0x9ff003ffcfe07fe7 0xf3fe007ff9fc0ffc

def z196 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000023000027c 0x500000004600004f

def z197 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x00078001c0000000 0x0000f00038000000

def z198 : W := mkw 0x0004040008520000 0x00008080010a4000 0xfa141c0238f2027e 0xdf428380471e404f

def z199 : W := mkw 0x0800202020008090 0x4100040404001012 0xf2206062311383fe 0xde440c0c4622707f

def z200 : W := mkw 0x0004040008520000 0x00008080010a4000 0x7a141c0008f20002 0x8f428380011e4000

def z201 : W := mkw 0x0000000400202200 0x0000000080040440 0x9a10001c08e03206 0xf3420003811c0640

def z202 : W := mkw 0xc00484000fdb0000 0x1800908001fb6000 0x7a141c000fff8003 0x8f42838001fff000

def z203 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0x600ffc03f0000000 0x0c01ff807e000000

def z204 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x0dcf8381ce0c7c01 0x21b9f07039c18f80

def z205 : W := mkw 0xc072d00007890002 0x180e5a0000f12000 0x1e7be0000fed8003 0x83cf7c0001fdb000

def z206 : W := mkw 0x0008222220000001 0x4001044444000000 0x6008600230000000 0x0c010c0046000000

def z207 : W := mkw 0x2000000400202b00 0x0400000080040560 0x0100000000007f84 0x0020000000000ff0

def z208 : W := mkw 0x0000000000000000 0x0000000000000000 0x8700020000004005 0x90e0004000000800

def z209 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffefe383cf1ffc67 0xbffdfc7079e3ff8c

def z210 : W := mkw 0x00802978b0000000 0x6010052f16000000 0x0000007c30000000 0x4000000f86000000

def z211 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xefcfe383fe1ffc7d 0xbdf9fc707fc3ff8f

def z212 : W := mkw 0xc07bd283078d4443 0x980f7a5060f1a888 0x05ebe380070dcc01 0x00bd7c7000e1b980

def z213 : W := mkw 0x0000080c90202200 0x2000010192040440 0xfa141c1ff8e03206 0xff428383ff1c0640

def z214 : W := mkw 0xdc7efe2efffff2fb 0x7b8fdfc5dffffe5f 0xff7ffe7ffffff3ff 0xffefffcffffffe7f

def z215 : W := mkw 0xc076d4040ffb2202 0x180eda8081ff6440 0xfe7ffc1c0fffb207 0xffcfff8381fff640

def z216 : W := mkw 0x00fb73f320000003 0xc01f6e7e64000000 0x7effffe000000000 0x0fdffffc00000000

def z217 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x97200262310043ff 0xd2e4004c4620087f

def z218 : W := mkw 0x100d028348101021 0x8201a05069020204 0xaecf8383c8103064 0xb5d9f0707902060c

def z219 : W := mkw 0xc0fbf3f327890003 0xd81f7e7e64f12000 0x04ebe3e0070d8001 0x009d7c7c00e1b000

def z220 : W := mkw 0x400480000a180000 0x0800900001430000 0x7e6fe0000f1f8003 0x8fcdfc0001e3f000

def z221 : W := mkw 0x00f2595890000002 0x201e4b2b12000000 0x00101c1c00000000 0x0002038380000000

def z222 : W := mkw 0x807404000dd20002 0x100e808001ba4000 0x7e741c000ff20003 0x8fce838001fe4000

def z223 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff012027e 0xffdffffffe02404f

def z224 : W := mkw 0xd07fd6834fdf5463 0x9a0ffad069fbea8c 0xafdf9f83cefc7c65 0xb5fbf3f079df8f8c

def z225 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xffe863e23f1fffff 0xfffd0c7c47e3ffff

def z226 : W := mkw 0xa8fb7bffb5a4ebd3 0xf51f6f7ff6b49d7a 0xffffffffffffffff 0xffffffffffffffff

def z227 : W := mkw 0x8000040005c30000 0x1000008000b86000 0x0000000001e38002 0x00000000003c7000

def z228 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x685ffc000eff8000 0x0d0bff8001dff000

def z229 : W := mkw 0x0008020200044041 0x0001004040008808 0xb7280262011c43e7 0xd6e5004c4023887c

def z230 : W := mkw 0x1404080cd8303228 0x228081019b060645 0xaa04001ff810327c 0xf5408003ff02064f

def z231 : W := mkw 0x10ff7bfbf8101023 0xe21fef7f7f020204 0xfefffffff8103064 0xffdfffffff02060c

def z232 : W := mkw 0xe076d5540ffb2b02 0x1c0edaaa81ff6560 0xfffffffc0fffff87 0xffffffff81fffff0

def z233 : W := mkw 0x0000080890000000 0x2000010112000000 0x8000001ff0000000 0x70000003fe000000

def z234 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xff341e7ff9f273ff 0xffe683cfff3e4e7f

def z235 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x68141c1ff8f23078 0x2d028383ff1e460f

def z236 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xd12062623103c3fe 0x5a240c4c4620787f

def z237 : W := mkw 0xc07ef6222fdb0003 0x580fdec445fb6000 0xfe7ffe623fff8003 0xdfcfffcc47fff000

def z238 : W := mkw 0x40098283020c4441 0x8801305060418888 0xafcf8383c60c4c01 0x35f9f07078c18980

def z239 : W := mkw 0xa000000405a02b00 0x1400000080b40560 0x010000000fe07f87 0x8020000001fc0ff0

def z240 : W := mkw 0xc8fffffbbfdfc0d3 0xf91fffff77fbf81a 0xffffffffffffc3ff 0xfffffffffffff87f

def z241 : W := mkw 0xc072d00007890002 0x180e5a0000f12000 0x7e7ffc00070d8001 0x0fcfff8000e1b000

def z242 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x25cf8383c61c4c61 0x04b9f07078c3898c

def z243 : W := mkw 0x007b528300000003 0x800f6a5060000000 0xfeffff83c0000000 0x3fdffff078000000

def z244 : W := mkw 0xa000000405a02b00 0x1400000080b40560 0x000000000ee03c00 0x0000000001dc0780

def z245 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff1004387 0xfffffffffe200870

def z246 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x9ef79ffdc0000000 0x73def3ffb8000000

def z247 : W := mkw 0x04000c0890420008 0x2080018112084001 0x40001c0030020018 0x0800038006004003

def z248 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x200f8003c01c0060 0x0401f0007803800c

def z249 : W := mkw 0x20fb7bffb0202b03 0xe41f6f7ff6040560 0xfffffffff0007f84 0x7ffffffffe000ff0

def z250 : W := mkw 0xc07fd6830fdf4443 0x980ffad061fbe888 0x7fffff800fffcc03 0x8ffffff001fff980

def z251 : W := mkw 0xc0fffeabbfdb0003 0xf81fffd577fb6000 0x7e7ffc03ffff8003 0x8fcfff807ffff000

def z252 : W := mkw 0xf07d83d34f9c5d63 0x9e0fb07a69f38bac 0xafef83e3cf1c7de5 0xb5fdf07c79e38fbc

def z253 : W := mkw 0x04040c0c98722208 0x20808181930e4441 0x7a141c1c38f2021a 0xcf428383871e4043

def z254 : W := mkw 0xe00484040ffb2b00 0x1c00908081ff6560 0x010000000fffff87 0x8020000001fffff0

def z255 : W := mkw 0x0008222220000001 0x4001044444000000 0x8000026230000000 0x5000004c46000000

def z256 : W := mkw 0xc0fff7f32fdb0003 0xd81ffefe65fb6000 0x7effffe00fff8003 0x8fdffffc01fff000

def z257 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x68dffd9ff0000000 0x2d1bffb3fe000000

def z258 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0xf2041c03f012027e 0xde4083807e02404f

def z259 : W := mkw 0x540484044a7e7668 0x0a809080894fcecd 0x010000000efe7e7f 0x8020000001dfcfcf

def z260 : W := mkw 0x40fbfbfbb20c4443 0xe81f7f7f76418888 0xfffffffff60c4c01 0x7ffffffffec18980

def z261 : W := mkw 0xa0fb7bfbb5800903 0xf41f6f7f76b00120 0xfffffffff7004d81 0x7ffffffffee009b0

def z262 : W := mkw 0x1c0404044876f2f8 0x03808080890ede5f 0x0100000009fff3ff 0x80200000013ffe7f

def z263 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff00043fc 0x7ffffffffe00087f

def z264 : W := mkw 0x8070000005800002 0x100e000000b00000 0x0460000007000001 0x008c000000e00000

def z265 : W := mkw 0x0009028300000001 0x8001205060000000 0x04cb838000000000 0x0099707000000000

def z266 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x0000007c00000380 0x4000000f80000070

def z267 : W := mkw 0x0070015000000002 0x000e002a00000000 0x1030007c00000000 0x4206000f80000000

def z268 : W := mkw 0x148d2ffff8723229 0xe291a5ffff0e4645 0xfa941ffff8f2327e 0xff5283ffff1e464f

def z269 : W := mkw 0x140c0e0ed8767269 0x228181c1db0ece4d 0xff1c1e1ff8fe727f 0xffe383c3ff1fce4f

def z270 : W := mkw 0xf47d8fdfdffe7f6b 0xbe8fb1fbfbffcfed 0xffff9ffffffe7fff 0xfffff3ffffffcfff

def z271 : W := mkw 0x14892bfff0203229 0xe291257ffe040645 0x808003fff000327c 0x7010007ffe00064f

def z272 : W := mkw 0x14f67d7cf872322a 0x629ecfaf9f0e4645 0xfa347c7ff8f2327e 0xff468f8fff1e464f

def z273 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff003fe3ff27fff 0xfffe007fc7fe4fff

def z274 : W := mkw 0x1c0c2e2af856d0f9 0x638185c55f0ada1f 0xf72c7e63f11fc3ff 0xdee58fcc7e23f87f

def z275 : W := mkw 0x080020202004c0d0 0x410004040400981a 0x51206060311fc3ff 0xca240c0c0623f87f

def z276 : W := mkw 0x04000c0c90622208 0x20800181920c4441 0xf2101c1e30f2027e 0xde420383c61e404f

def z277 : W := mkw 0xb4740d5cddf23b2a 0x368e81ab9bbe4765 0x08d41d9dcee03c00 0x211a83b3b9dc0780

def z278 : W := mkw 0xf07d83d74fbc7f63 0x9e0fb07ae9f78fec 0xbfff83ffcffc7fe7 0xf7fff07ff9ff8ffc

def z279 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x89d003fc0ee07f84 0x713a007f81dc0ff0

def z280 : W := mkw 0x400d82830a1c4441 0x8801b05061438888 0x2fcf83800e1c4c01 0x85f9f07001c38980

def z281 : W := mkw 0x080000000004c0d0 0x010000000000981a 0xf3000002311fc3ff 0xde6000004623f87f

def z282 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xf72fe263f11fc3ff 0xdee5fc4c7e23f87f

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x9620026000000000 0x52c4004c00000000

def z284 : W := mkw 0x0070015000000002 0x000e002a00000000 0x08d0019c00000000 0x211a003380000000

def z285 : W := mkw 0xb47405544df23b2a 0x168e80aa89be4765 0x9ff003fc0ff27fff 0xf3fe007f81fe4fff

def z286 : W := mkw 0xa000000405a02b00 0x1400000080b40560 0x8fc003800fe07f87 0xb1f8007001fc0ff0

def z287 : W := mkw 0xa07405540df22b02 0x140e80aa81be4560 0xfff41ffc0ff27f87 0xfffe83ff81fe4ff0

def z288 : W := mkw 0x1404040448723228 0x02808080890e4645 0xf200000238f2327e 0xde400000471e464f

def z289 : W := mkw 0x14f75dddd872322a 0xa29eebbbbb0e4645 0x08d79d9dc8e03000 0x211af3b3b91c0600

def z290 : W := mkw 0x0008020200044041 0x0001004040008808 0x8100020200004064 0x102000404000080c

def z291 : W := mkw 0x0072580890000002 0x200e4b0112000000 0xfe7ffc1ff0000000 0x7fcfff83fe000000

def z292 : W := mkw 0x1400080cd0203228 0x228001019a040645 0x9a10001ff8e0327e 0xf3420003ff1c064f

def z293 : W := mkw 0xc07fd6830fdb0003 0x980ffad061fb6000 0xfeffff83cfff8003 0xbfdffff079fff000

def z294 : W := mkw 0x400484000a5b0000 0x08009080014b6000 0x00000000001f8000 0x000000000003f000

def z295 : W := mkw 0x1cff7ffff876f2fb 0xe39fefffff0ede5f 0xfffffffff9fff3ff 0xffffffffff3ffe7f

def z296 : W := mkw 0x1404040448723228 0x02808080890e4645 0x7a141c0008f2327e 0x8f428380011e464f

def z297 : W := mkw 0x508dabfbfa1c5461 0xea11b57f7f438a8c 0xafcf83fffe1c7c65 0xf5f9f07fffc38f8c

def z298 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x00079c0000000000 0x0000f38000000000

def z299 : W := mkw 0x40098283020c4441 0x8801305060418888 0x8fcb83800e0c7c05 0xb1f9707001c18f80

def z300 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x703ffc7ff0000000 0x4e07ff8ffe000000

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0xf200000230000000 0x5e40000046000000

def z302 : W := mkw 0x50ffdbdbda1c5463 0xaa1ffb7b7b438a8c 0xafdf9f9fce1c7c65 0xb5fbf3f3f9c38f8c

def z303 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x05cb83800e1c7c65 0x80b9707001c38f8c

def z304 : W := mkw 0x508ffaabfa1c5461 0xea11ff557f438a8c 0xefcfff83fe1c7c65 0xbdf9fff07fc38f8c

def z305 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x88141c1ff8e0327c 0x71028383ff1c064f

def z306 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff863fc0fffff87 0xffff0c7f81fffff0

def z307 : W := mkw 0x0000000400202200 0x0000000080040440 0x9fd0039c0ee07e07 0xf3fa007381dc0fc0

def z308 : W := mkw 0x480ef6222a5fc0d1 0x4901dec4454bf81a 0xf72ffe62311fc3ff 0xdee5ffcc4623f87f

def z309 : W := mkw 0x00082a2ab0000001 0x6001054556000000 0xfe3c7e7ff0000000 0x7fc78fcffe000000

def z310 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x65286262311fc1f9 0x0ca50c4c4623f83f

def z311 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000001004387 0x8020000000200870

def z312 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x8000001ff8f2327e 0xf0000003ff1e464f

def z313 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafcf83e3fe1c7ffd 0xf5f9f07c7fc38fff

def z314 : W := mkw 0x080000000004c0d0 0x010000000000981a 0x00000000001f8078 0x000000000003f00f

def z315 : W := mkw 0xa070000405a02b02 0x140e000080b40560 0x1f7000000fe07f87 0x83ee000001fc0ff0

def z316 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0xaedf9f9fc0000000 0x35dbf3f3f8000000

def z317 : W := mkw 0x00fa7b7ab0000003 0x601f4f6f56000000 0xf6387e7e30000000 0x5ec70fcfc6000000

def z318 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffffe007c05 0xffffffffffc00f80

def z319 : W := mkw 0x8872742025c38092 0x510e4e8404b87012 0x50307c6031e3839a 0x4a060f8c063c7073

def z320 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x08141c1dc8f2327e 0xa1028383b91e464f

def z321 : W := mkw 0xa072555405e32b02 0x140e4aaa80bc6560 0xdff07ffc0fe3ff87 0xfbfe0fff81fc7ff0

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000011f8003 0x800000000023f000

def z323 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x1130007c0fe07f87 0xc226000f81fc0ff0

def z324 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9a30007c09e03386 0xf346000f813c0670

def z325 : W := mkw 0x14ff7ffbf852102b 0xe29fefff7f0a4205 0xfefffffff0120078 0x7fdffffffe02400f

def z326 : W := mkw 0x400480000a180000 0x0800900001430000 0x000000000e1c0001 0x8000000001c38000

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x08c001800e003c00 0x2118003001c00780

def z328 : W := mkw 0xa0f359dd95a02b02 0xb41e6b3bb2b40560 0x9ff79ffdcfe07f87 0xf3fef3ffb9fc0ff0

def z329 : W := mkw 0xe076d5540ffb2b02 0x1c0edaaa81ff6560 0x7efffd9c0fffbc03 0xafdfffb381fff780

def z330 : W := mkw 0x40fffffbba5b0003 0xe81fffff774b6000 0xfefffffff01f8000 0x7fdffffffe03f000

def z331 : W := mkw 0x0072500000000002 0x000e4a0000000000 0x08579c0000000000 0x010af38000000000

def z332 : W := mkw 0x500480004a1c5460 0x0a00900009438a8c 0x00000000001c0060 0x000000000003800c

def z333 : W := mkw 0xd87ff6a36fdfd4f3 0xdb0ffed46dfbfa9e 0xffffffe3ffffffff 0xfffffffc7fffffff

def z334 : W := mkw 0x8072540005c30002 0x100e4a8000b86000 0x5e707c000fe38003 0x8bce0f8001fc7000

def z335 : W := mkw 0xc0f6fd78bfdb0002 0x781edfaf17fb6000 0x7e7ffc7c3fff8003 0xcfcfff8f87fff000

def z336 : W := mkw 0x40098283020c4441 0x8801305060418888 0xa7cb8382061c4c65 0x94f9707040c3898c

def z337 : W := mkw 0xc876f4202fdb8092 0x590ede8405fb7012 0x7e7ffc603fff839b 0xcfcfff8c07fff073

def z338 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x89c78383ce007c64 0x3138f07079c00f8c

def z339 : W := mkw 0x500c82024a1c5461 0x0a01904049438a8c 0xa70802020e1c7c65 0x94e1004041c38f8c

def z340 : W := mkw 0x400c82020a1c4041 0x0801904041438808 0xaf4f82020e1c4065 0x95e9f04041c3880c

def z341 : W := mkw 0xd077d4814fdb1422 0x9a0efa9029fb6284 0x08d79d81cee03c00 0x211af3b039dc0780

def z342 : W := mkw 0x500480004a181020 0x0a00900009430204 0xae4f8003ce1c3065 0xb5c9f00079c3860c

def z343 : W := mkw 0xc87ef6222fdfc0d3 0x590fdec445fbf81a 0x7f7ffe600fffc183 0x8fefffcc01fff830

def z344 : W := mkw 0x0008020200044041 0x0001004040008808 0xa7080202001c4065 0x94e100404003880c

def z345 : W := mkw 0x54058c8dda7a3628 0xaa80b191bb4f46c5 0xfad79d9ffef23e7e 0xff5af3b3ffde47cf

def z346 : W := mkw 0xa0fb7bffb5a02b03 0xf41f6f7ff6b40560 0xfefffffff1e00382 0x7fdffffffe3c0070

def z347 : W := mkw 0x500480004a1c5460 0x0a00900009438a8c 0x8fc003800e1c7c65 0xb1f8007001c38f8c

def z348 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffcf8383fe1e7e7f 0xfff9f0707fc3cfcf

def z349 : W := mkw 0xe076d5540ffb2b02 0x1c0edaaa81ff6560 0x9ff79ffc0fe07f87 0xf3fef3ff81fc0ff0

def z350 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xaecf8383c01c0060 0x35d9f0707803800c

def z351 : W := mkw 0x0000000000044040 0x0000000000008808 0x01000000001c4065 0x802000000003880c

def z352 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc000ee00000 0x0fcfff8001dc0000

def z353 : W := mkw 0xa072515405a02b02 0x140e4a2a80b40560 0xfffffffc0fe07f87 0xffffffff81fc0ff0

def z354 : W := mkw 0x1004000048101020 0x0200800009020204 0x08040001c8003000 0x2100800039000600

def z355 : W := mkw 0xd476dc0cdffb322a 0x3a8edb819bff6645 0xfa579c1ffef2327e 0xff4af383ffde464f

def z356 : W := mkw 0xe07983d3078c4d43 0x9c0f307a60f189a8 0x05eb83e0070c4d81 0x00bd707c00e189b0

def z357 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf6286262301f8078 0x5ec50c4c4603f00f

def z358 : W := mkw 0xbc7c2f7efdf6fbfb 0x778f85efdfbedf7f 0xfffc7fffffffffff 0xffff8fffffffffff

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa040003c0000000 0x3540800078000000

def z360 : W := mkw 0xa000000405a02b00 0x1400000080b40560 0x0000000001e00382 0x00000000003c0070

def z361 : W := mkw 0xa878237625a4ebd3 0x550f046ec4b49d7a 0x9ff863fc0fedff87 0xf3ff0c7f81fdbff0

def z362 : W := mkw 0xd476dc0cdffb322a 0x3a8edb819bff6645 0x7e7ffc1dcfffb003 0xafcfff83b9fff600

def z363 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x70141c1ff0f2027a 0x4e028383fe1e404f

def z364 : W := mkw 0x40fffbfbba180003 0xe81fff7f77430000 0xfefffffffe1c0001 0xffdfffffffc38000

def z365 : W := mkw 0x1c0c2e2af856d0f9 0x638185c55f0ada1f 0x600c7c03f01f8078 0x0c018f807e03f00f

def z366 : W := mkw 0x5406dc08da5b1028 0x2a80db811b4b6205 0x600ffc03f01f8078 0x0c01ff807e03f00f

def z367 : W := mkw 0x04000c0c90622208 0x20800181920c4441 0x00101c1c00e00000 0x00020383801c0000

def z368 : W := mkw 0x300903d740247f61 0x8601207ae8048fec 0x818003ffc0007fe4 0x7030007ff8000ffc

def z369 : W := mkw 0x008b72a320000001 0xc0116e5464000000 0x000be00000000000 0x00017c0000000000

def z370 : W := mkw 0x4809a2a3220cc4d1 0xc90134546441989a 0x05ebe3e0070dcd81 0x00bd7c7c00e1b9b0

def z371 : W := mkw 0xf476dd5cdffb3b2a 0x3e8edbab9bff6765 0xffffffffffffffff 0xffffffffffffffff

def z372 : W := mkw 0x540d8e8fda7e7669 0xaa81b1d1fb4fcecd 0xfa1f9c1ff8fe327e 0xff43f383ff1fc64f

def z373 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x50307c000fff8003 0x8a060f8001fff000

def z374 : W := mkw 0x580480004a1cd4f0 0x0b00900009439a9e 0x010000000f1fffff 0x8020000001e3ffff

def z375 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x61086002311fc3ff 0x8c210c004623f87f

def z376 : W := mkw 0xa078035605a46b43 0x140f006ac0b48d68 0xbff803fe0ffc7fe7 0xf7ff007fc1ff8ffc

def z377 : W := mkw 0x000922a320000001 0xc001245464000000 0xfeefe3e3f0000000 0x7fddfc7c7e000000

def z378 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xffd41f9ffef27e7f 0xfffa83f3ffde4fcf

def z379 : W := mkw 0x500fd6834a5f5461 0x8a01fad0694bea8c 0xefcfff83ce1ffc65 0xbdf9fff079c3ff8c

def z380 : W := mkw 0x508ffaabfa1c5461 0xea11ff557f438a8c 0x600ffc03f01c0060 0x0c01ff807e03800c

def z381 : W := mkw 0xa0f92bffb5a02b03 0xf41f257ff6b40560 0x9ff003ffffe07f87 0xf3fe007ffffc0ff0

def z382 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x7a1ffc0008ff8002 0x8f43ff80011ff000

def z383 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x91b003fc01e07f86 0x7236007f803c0ff0

def z384 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa141c1ff8e03000 0x7f428383ff1c0600

def z385 : W := mkw 0x00fb73f320000003 0xc01f6e7e64000000 0xf6ebe3e230000000 0x5edd7c7c46000000

def z386 : W := mkw 0x54058c8dda7a3628 0xaa80b191bb4f46c5 0x08d79d9dcee03c00 0x211af3b3b9dc0780

def z387 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x5877fc000fe38002 0x0b0eff8001fc7000

def z388 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xff7ffe600fffc387 0xdfefffcc01fff870

def z389 : W := mkw 0x0009028300044441 0x8001205060008888 0x0180038000004c00 0x0030007000000980

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7200262311243ff 0xdee4004c4622487f

def z391 : W := mkw 0x0002500000000000 0x00004a0000000000 0x600ffc0000000000 0x0c01ff8000000000

def z392 : W := mkw 0xb4040c0cddf23b28 0x368081819bbe4765 0xfb141c1ffff27fff 0xff628383fffe4fff

def z393 : W := mkw 0x500580814a181420 0x8a00b01029430284 0xaac78183ce103c64 0xb558f03079c2078c

def z394 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x0100026000004180 0x0020004c00000830

def z395 : W := mkw 0x0400080c90202208 0x2080010192040441 0x0000001c30000218 0x4000000386000043

def z396 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180038000007c04 0x3030007000000f80

def z397 : W := mkw 0x1000000040045460 0x0200000008008a8c 0x0100000000007c64 0x0020000000000f8c

def z398 : W := mkw 0x0002540000430000 0x00004a8000086000 0x40007c0000038000 0x08000f8000007000

def z399 : W := mkw 0x0c002c2cb062a298 0x61800585960c5453 0x50307c7c31e3839a 0x4a060f8f863c7073

def z400 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0x00041c01c0000000 0x0000838038000000

def z401 : W := mkw 0xa870217425a0ab92 0x550e042e84b41572 0x5030607c31e3839a 0x4a060c0f863c7073

def z402 : W := mkw 0xf07d83d74fbc7f63 0x9e0fb07ae9f78fec 0xafdf839fcefc7c65 0xb5fbf073f9df8f8c

def z403 : W := mkw 0x4002d00002090000 0x08005a0000412000 0x000be000000d8000 0x00017c000001b000

def z404 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x77286260011fc183 0x8ee50c4c0023f830

def z405 : W := mkw 0xc0fffffbbfdb0003 0xf81fffff77fb6000 0xfefffffffee00000 0x7fdfffffffdc0000

def z406 : W := mkw 0x500480004a1c5460 0x0a00900009438a8c 0xab040003ce1c7c65 0xb560800079c38f8c

def z407 : W := mkw 0x10040808d8101020 0x220081011b020204 0xfa141c1ff8103064 0xff428383ff02060c

def z408 : W := mkw 0x480ef6222a5fc0d1 0x4901dec4454bf81a 0x600ffc02301f8078 0x0c01ff804603f00f

def z409 : W := mkw 0x08fa7b7ab004c0d3 0x611f4f6f5600981a 0xf7387e7e311fc3ff 0xdee70fcfc623f87f

def z410 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x97e003e007004f87 0xd2fc007c00e009f0

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x9fe003e00f007f87 0xf3fc007c01e00ff0

def z412 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x88d79ffff0000000 0x711af3fffe000000

def z413 : W := mkw 0x14000808d0001028 0x228001011a000205 0x00000003f0000078 0x000000007e00000f

def z414 : W := mkw 0x1004000048101020 0x0200800009020204 0xfa040003f812327e 0xff4080007f02464f

def z415 : W := mkw 0x1004000448303220 0x0200800089060644 0xba14001fc8f03266 0xf7428003f91e064c

def z416 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x05e003e00fe07f87 0x80bc007c01fc0ff0

def z417 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x00086000000d8000 0x00010c000001b000

def z418 : W := mkw 0x1004000048101020 0x0200800009020204 0xafc40383ce107c65 0xb5f8807079c20f8c

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000012027e 0x800000000002404f

def z420 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x0c7ffc000fed8001 0x018fff8001fdb000

def z421 : W := mkw 0x0000000400202200 0x0000000080040440 0x9f30027c09e07387 0xf3e6004f813c0e70

def z422 : W := mkw 0xc072d00007890002 0x180e5a0000f12000 0x766be000071f8003 0x8ecd7c0000e3f000

def z423 : W := mkw 0x1404040448723228 0x02808080890e4645 0x0000000008e03000 0x00000000011c0600

def z424 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x60041c03f8f2327e 0x8c0083807f1e464f

def z425 : W := mkw 0x1009028340045461 0x8201205068008a8c 0xa7880383c01c7c65 0xb4f1007078038f8c

def z426 : W := mkw 0xd476dc08dfdb102a 0x3a8edb811bfb6205 0x7e7ffc03ffff807b 0x8fcfff807ffff00f

def z427 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x81800383ce1c7c65 0xb030007079c38f8c

def z428 : W := mkw 0x00040c0898520000 0x20008181130a4000 0xfa141c1ff8f20002 0xff428383ff1e4000

def z429 : W := mkw 0x5c0daeaffa7ef6f9 0xeb81b5d5ff4fdedf 0xffffffffffffffff 0xffffffffffffffff

def z430 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf2086002301f827e 0xde410c004603f04f

def z431 : W := mkw 0x080802020004c0d1 0x010100404000981a 0xa7080202011fc3ff 0x94e100404023f87f

def z432 : W := mkw 0x50fffbfbfa181423 0xea1fff7f7f430284 0xfefffffffe003c00 0x7fdfffffffc00780

def z433 : W := mkw 0x40fbf3f3220c4443 0xc81f7e7e64418888 0x05ebe3e0060c4c01 0x00bd7c7c00c18980

def z434 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafefe3e3cf1dfde5 0xb5fdfc7c79e3bfbc

def z435 : W := mkw 0xc87af222278dc0d3 0x590f5e4444f1b81a 0xf76be262371fc3ff 0xdeed7c4c46e3f87f

def z436 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x09d0019c0fe07f87 0xa13a003381fc0ff0

def z437 : W := mkw 0x1004000048101020 0x0200800009020204 0x0000000008103064 0x800000000102060c

def z438 : W := mkw 0x00fb73f320000003 0xc01f6e7e64000000 0xaeefe3e3c0000000 0x35ddfc7c78000000

def z439 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x8fe003e00f007d85 0xb1fc007c01e00fb0

def z440 : W := mkw 0x0004040008520000 0x00008080010a4000 0x60041c0000120000 0x0c00838000024000

def z441 : W := mkw 0x580ca2226a1cd4f1 0x4b0194444d439a9e 0xf72862623f1fffff 0xdee50c4c47e3ffff

def z442 : W := mkw 0xc006d4000fdb0000 0x1800da8001fb6000 0x600ffc000fff8003 0x8c01ff8001fff000

def z443 : W := mkw 0x00892aabb0000001 0xe011255576000000 0x00000003f0000000 0x000000007e000000

def z444 : W := mkw 0xc80ca6222fdfc0d1 0x590194c445fbf81a 0xf72862623fffc3ff 0xdee50c4c47fff87f

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z446 : W := mkw 0xa07903d705a02b03 0x940f207ae0b40560 0xbfff83ffcfe07f87 0xf7fff07ff9fc0ff0

def z447 : W := mkw 0x14f75dddd872322a 0xa29eebbbbb0e4645 0xfad79d9ff8f2327e 0xff5af3b3ff1e464f

def z448 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0x7a141c03f8f2007a 0x8f4283807f1e400f

def z449 : W := mkw 0x0070015400202202 0x000e002a80040440 0x9ef003fc08e03206 0xf3de007f811c0640

def z450 : W := mkw 0x400480000a180000 0x0800900001430000 0x200f8000001c0000 0x0401f00000038000

def z451 : W := mkw 0xe072d15007890902 0x1c0e5a2a00f12120 0x05ebe3e0070dcd81 0x00bd7c7c00e1b9b0

def z452 : W := mkw 0x0800000000008090 0x0100000000001012 0x000000000103839a 0x0000000000207073

def z453 : W := mkw 0x0000080890000000 0x2000010112000000 0x60041c03f0000000 0x0c0083807e000000

def z454 : W := mkw 0x4001808102080400 0x8800301020410080 0x00c3818006000c00 0x0018703000c00180

def z455 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9730027c01e04387 0xd2e6004f803c0870

def z456 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x9a141c1dc8e03206 0xf3428383b91c0640

def z457 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xaa0f8003c81c3064 0xb541f0007903860c

def z458 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x8fd0039c0ee07c05 0xb1fa007381dc0f80

def z459 : W := mkw 0x400480000a180000 0x0800900001430000 0x084780000e000000 0x0108f00001c00000

def z460 : W := mkw 0xa070095c95a02b02 0x340e012b92b40560 0xfff41fffffe07f87 0xfffe83fffffc0ff0

def z461 : W := mkw 0xc000800007890000 0x1800100000f12000 0x00000000070d8001 0x0000000000e1b000

def z462 : W := mkw 0x0009028300000001 0x8001205060000000 0x200f8003c0000000 0x0401f00078000000

def z463 : W := mkw 0x54048c0cda7e7668 0x2a8091819b4fcecd 0xfb141c1ffefe7e7f 0xff628383ffdfcfcf

def z464 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x8fc003fc0e007f85 0xf1f8007f81c00ff0

def z465 : W := mkw 0xd076d4004fdf5462 0x1a0eda8009fbea8c 0x7f7ffc000ffffc67 0x8fefff8001ffff8c

def z466 : W := mkw 0x4809a2a3220cc4d1 0xc90134546441989a 0xf7ebe3e2371fcfff 0xdefd7c7c46e3f9ff

def z467 : W := mkw 0x0076540008520002 0x000eca80010a4000 0x7e7ffc0008f20002 0x8fcfff80011e4000

def z468 : W := mkw 0x0072500000000002 0x000e4a0000000000 0x046be00000000000 0x008d7c0000000000

def z469 : W := mkw 0x480ca2222a1cc0d1 0x490194444543981a 0xff6fe2623f1fc3ff 0xdfedfc4c47e3f87f

def z470 : W := mkw 0x0004040008520000 0x00008080010a4000 0x08141c0008e00000 0x01028380011c0000

def z471 : W := mkw 0x0070015000000002 0x000e002a00000000 0x9ff003fc0e007c05 0xf3fe007f81c00f80

def z472 : W := mkw 0x8072500005800002 0x100e4a0000b00000 0x7e7ffc000fe00003 0x8fcfff8001fc0000

def z473 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xe7086202301fc07d 0x9ce10c404603f80f

def z474 : W := mkw 0x0008020200000001 0x0001004040000000 0xa608020200000000 0x14c1004040000000

def z475 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x00c0018006000c00 0x0018003000c00180

def z476 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfefffffff01f8078 0x7fdffffffe03f00f

def z477 : W := mkw 0x080000000004c0d0 0x010000000000981a 0x01000000000043fc 0x002000000000087f

def z478 : W := mkw 0x087823722004c0d3 0x410f046e4400981a 0xfff863fe311fc3ff 0xffff0c7fc623f87f

def z479 : W := mkw 0xe076d5500fdb0902 0x1c0edaaa01fb6120 0x7fffffe00fffcd83 0x8ffffffc01fff9b0

def z480 : W := mkw 0x080000000004c0d0 0x010000000000981a 0x77286000011fc3ff 0x8ee50c000023f87f

def z481 : W := mkw 0x2070015400202b02 0x040e002a80040560 0x9ff003fc00007f84 0x73fe007f80000ff0

def z482 : W := mkw 0xf87da3f76fbcfff3 0xdf0fb47eedf79ffe 0xffffe3ffffffffff 0xfffffc7fffffffff

def z483 : W := mkw 0x04f27d7cb062220a 0x609e4faf960c4441 0x50307c7c30e2021a 0x4a060f8f861c4043

def z484 : W := mkw 0x8000000005800000 0x1000000000b00000 0x000000000fe00003 0x8000000001fc0000

def z485 : W := mkw 0xf07581d54fb83f22 0x9e0eb03aa9f707e4 0x08d7819dcee03c00 0x211af033b9dc0780

def z486 : W := mkw 0x0000000000000000 0x0000000000000000 0xf6286002311f827f 0xdec50c004623f04f

def z487 : W := mkw 0x08fb73f32004c0d3 0xc11f6e7e6400981a 0xf7ebe3e2311fc3ff 0xdefd7c7c4623f87f

def z488 : W := mkw 0x0808222220008091 0x4101044444001012 0xf62862623103839a 0x5ec50c4c46207073

def z489 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x84ebe3fff0000000 0x709d7c7ffe000000

def z490 : W := mkw 0x8070000005800002 0x100e000000b00000 0x9ff003800fe07c07 0xb3fe007001fc0f80

def z491 : W := mkw 0x0800202020008090 0x4100040404001012 0x4000600030038018 0x08000c0006007003

def z492 : W := mkw 0xd076d4004fdb1022 0x1a0eda8009fb6204 0xfe7ffc03cfffb067 0xbfcfff8079fff60c

def z493 : W := mkw 0x14765c0cd872322a 0x228ecb819b0e4645 0xfe7ffc1ff8f2327e 0xffcfff83ff1e464f

def z494 : W := mkw 0x0004000008100000 0x0000800001020000 0x2a04000008100000 0x8540800001020000

def z495 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x0020006001000180 0x0004000c00200030

def z496 : W := mkw 0xd0fffffbffdf5463 0xfa1fffff7ffbea8c 0xfffffffffffffc67 0xffffffffffffff8c

def z497 : W := mkw 0x540d8a8fda3c7669 0xaa81b151fb478ecd 0xafcf839ffe1c7e7d 0xf5f9f073ffc38fcf

def z498 : W := mkw 0x1004000048101020 0x0200800009020204 0x20040003c0100060 0x040080007802000c

def z499 : W := mkw 0x20892bffb0202b01 0xe411257ff6040560 0x818003fff0007f84 0x7030007ffe000ff0

def z500 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0xea041c03f812307c 0xbd4083807f02460f

def z501 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xfeffffffffe00003 0xffdffffffffc0000

def z502 : W := mkw 0x400d82830a180001 0x8801b05061430000 0xaecf8383ce1c0001 0xb5d9f07079c38000

def z503 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf7286262300043fc 0x5ee50c4c4600087f

def z504 : W := mkw 0x088b7aabb004c0d1 0xe1116f557600981a 0x600ffc03f01f8078 0x0c01ff807e03f00f

def z505 : W := mkw 0x0000000400202200 0x0000000080040440 0xfa10001e38f2327e 0xff420003c71e464f

def z506 : W := mkw 0x0000000000000000 0x0000000000000000 0x60086000001f8000 0x0c010c000003f000

def z507 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x97a003fc01007f87 0xf2f4007f80200ff0

def z508 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x64efffe3f0000000 0x0c9dfffc7e000000

def z509 : W := mkw 0x1404040448723228 0x02808080890e4645 0xaa040003c8f2327e 0xb5408000791e464f

def z510 : W := mkw 0x0008222220000001 0x4001044444000000 0xf728626231004387 0xdee50c4c46200870

def z511 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x0010001c00e00000 0x00020003801c0000

def z512 : W := mkw 0x58fffbfbfa1cd4f3 0xeb1fff7f7f439a9e 0xffffffffff1fffff 0xffffffffffe3ffff

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x05c0038006004c01 0x00b8007000c00980

def z514 : W := mkw 0x04000c0c90622208 0x20800181920c4441 0xda101c1c38e2321e 0xfb420383871c4643

def z515 : W := mkw 0x1009028340045461 0x8201205068008a8c 0x00000003c0000060 0x000000007800000c

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x5020600001038002 0x0a040c0000207000

def z517 : W := mkw 0xa878237625a4ebd3 0x550f046ec4b49d7a 0x9ff003fe3fe07fff 0xf3fe007fc7fc0fff

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x1a10000008e00002 0x83420000011c0000

def z519 : W := mkw 0x50f7d9d9da181422 0xaa1efb3b3b430284 0x08d79d9dce003c00 0x211af3b3b9c00780

def z520 : W := mkw 0x00827828b0000000 0x60104f0516000000 0x40007c0030000000 0x08000f8006000000

def z521 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xa70f8203c01c4065 0x94e1f0407803880c

def z522 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x1ff003e00fe04d83 0x83fe007c01fc09b0

def z523 : W := mkw 0x0008222220000001 0x4001044444000000 0xf6286262311f8003 0xdec50c4c4623f000

def z524 : W := mkw 0xc076dc089fdb0002 0x380edb8113fb6000 0xfe7ffc1fffff8003 0xffcfff83fffff000

def z525 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0x58f7fdfdf0000000 0x6b1effbfbe000000

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x1620000001000003 0x82c4000000200000

def z527 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x1ef0019c0fe03c03 0xa3de003381fc0780

def z528 : W := mkw 0x1400080cd0203228 0x228001019a040645 0x0000001dc0003000 0x20000003b8000600

def z529 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x18f001fc0fe03f82 0x631e003f81fc07f0

def z530 : W := mkw 0x1c082a2ef024f2f9 0x63810545de049e5f 0xf728627ff11ff3ff 0xfee50c4ffe23fe7f

def z531 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xa18f8383c01c7c64 0x3431f07078038f8c

def z532 : W := mkw 0x0078237220000003 0x400f046e44000000 0xfef863fe30000000 0x7fdf0c7fc6000000

def z533 : W := mkw 0x00f27978b0000002 0x601e4f2f16000000 0x7e7ffc7c30000000 0x4fcfff8f86000000

def z534 : W := mkw 0xa808222625a4ebd1 0x55010444c4b49d7a 0xf72862623fffffff 0xdee50c4c47ffffff

def z535 : W := mkw 0x00090a8b90000001 0xa001215172000000 0xfedf9f9ff0000000 0x7fdbf3f3fe000000

def z536 : W := mkw 0xc076d0000f990002 0x180eda0001f32000 0x2e6fe0000f1d8001 0x85cdfc0001e3b000

def z537 : W := mkw 0x140d0e8fd8767669 0xa281a1d1fb0ececd 0xfb941f9ff8f27e7e 0xff7283f3ff1e4fcf

def z538 : W := mkw 0x08892bfbb004c0d1 0xe111257f7600981a 0x818003fff00043fc 0x7030007ffe00087f

def z539 : W := mkw 0x008109d990000000 0xa010213b32000000 0x0080019dc0000000 0x20100033b8000000

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x8100026000004384 0x5020004c00000870

def z541 : W := mkw 0x14090a8fd0247669 0xa2812151fa048ecd 0x8180039ff0007e7c 0x70300073fe000fcf

def z542 : W := mkw 0xd00484004fdf5460 0x1a00908009fbea8c 0x010000000ffffc67 0x8020000001ffff8c

def z543 : W := mkw 0x04000c0c90622208 0x20800181920c4441 0xfa141c1ff0e2021a 0x7f428383fe1c4043

def z544 : W := mkw 0x0000015000000000 0x0000002a00000000 0x808003fc00000000 0x7010007f80000000

def z545 : W := mkw 0xa000000005800900 0x1400000000b00120 0x0100000007004d81 0x0020000000e009b0

def z546 : W := mkw 0xc00484000fdb0000 0x1800908001fb6000 0x000000000ee00000 0x0000000001dc0000

def z547 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ef003fc0ee03c00 0x73de007f81dc0780

def z548 : W := mkw 0x0008222220044041 0x4001044444008808 0xf7286262301c4065 0xdee50c4c4603880c

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x04286000010d8001 0x00850c000021b000

def z550 : W := mkw 0xa4700d5c95e22b0a 0x348e01ab92bc4561 0x50301c7c31e2039a 0x4a06038f863c4073

def z551 : W := mkw 0x0008020200044041 0x0001004040008808 0xf7286202011fc067 0x9ee50c404023f80c

def z552 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x85e003fc07007f85 0x70bc007f80e00ff0

def z553 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf3000262301243fe 0xde60004c4602487f

def z554 : W := mkw 0xf07fd7d74fff7f63 0x9e0ffafae9ffefec 0xffffffffcfffffe7 0xfffffffff9fffffc

def z555 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x046be0000fff8003 0x808d7c0001fff000

def z556 : W := mkw 0x54fffffffa7e766b 0xea9fffffff4fcecd 0xfffffffffefe7e7f 0xffffffffffdfcfcf

def z557 : W := mkw 0x008923f320000001 0xc011247e64000000 0x008003e000000000 0x0010007c00000000

def z558 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7a579c000ef20002 0x8f4af38001de4000

def z559 : W := mkw 0x1c0c2e2ef876f2f9 0x638185c5df0ede5f 0xfa1c7c1ff8ffb27e 0xff438f83ff1ff64f

def z560 : W := mkw 0x8070000005800002 0x100e000000b00000 0x9f7002600fe04387 0xd3ee004c01fc0870

def z561 : W := mkw 0xe076d5540ffb2b02 0x1c0edaaa81ff6560 0x7e7ffc7c0fff8383 0xcfcfff8f81fff070

def z562 : W := mkw 0xa800000405a4ebd0 0x1500000080b49d7a 0x010000000fffffff 0x8020000001ffffff

def z563 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x50101c1c38f2327e 0xca020383871e464f

def z564 : W := mkw 0x3400095cd0203b28 0x2680012b9a040765 0x818003fff0007ffc 0x7030007ffe000fff

def z565 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x85286262310dc3fd 0x50a50c4c4621b87f

def z566 : W := mkw 0x8070000405a02202 0x100e000080b40440 0x9e70001c0fe03207 0xf3ce000381fc0640

def z567 : W := mkw 0x00ff7ffbb8520003 0xe01fefff770a4000 0xfefffffff8f20002 0xffdfffffff1e4000

def z568 : W := mkw 0x100d028348145461 0x8201a05069028a8c 0xab840383c8107c64 0xb570807079020f8c

def z569 : W := mkw 0x50fff3f36a1c5463 0xca1ffe7e6d438a8c 0xafefe3e3ce1c7c65 0xb5fdfc7c79c38f8c

def z570 : W := mkw 0x0072500000000002 0x000e4a0000000000 0x50307c0000000000 0x0a060f8000000000

def z571 : W := mkw 0x500d8a8bda1c5461 0xaa01b1517b438a8c 0xffdf9f9ffe1c7c65 0xfffbf3f3ffc38f8c

def z572 : W := mkw 0x007a722220000003 0x400f4e4444000000 0xfe7ffe6230000000 0x5fcfffcc46000000

def z573 : W := mkw 0xa870217425a0ab92 0x550e042e84b41572 0xdff063fc3fe3ff9f 0xfbfe0c7f87fc7ff3

def z574 : W := mkw 0x1400080cd0203228 0x228001019a040645 0xf200001ff012327e 0xfe400003fe02464f

def z575 : W := mkw 0x0083588990000000 0xa0106b1132000000 0x00079c01c0000000 0x0000f38038000000

def z576 : W := mkw 0xc00484000fdb0000 0x1800908001fb6000 0x2e4f80000fff8003 0x85c9f00001fff000

def z577 : W := mkw 0x1009028340045461 0x8201205068008a8c 0x8fc00383ce007c65 0xb1f8007079c00f8c

def z578 : W := mkw 0x0008020200044041 0x0001004040008808 0x20080002001c0060 0x040100004003800c

def z579 : W := mkw 0x0000000400202200 0x0000000080040440 0x1010001c00e00202 0x42020003801c0040

def z580 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x646ffc00071f8001 0x0c8dff8000e3f000

def z581 : W := mkw 0xf07481544fbc7f62 0x1e0e902a89f78fec 0x9ff003fc0ffc7fe7 0xf3fe007f81ff8ffc

def z582 : W := mkw 0x1c042c2cf872b2b8 0x638085859f0e5657 0xfa347c7ff9f3b3fe 0xff468f8fff3e767f

def z583 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x0080019c00003c00 0x2010003380000780

def z584 : W := mkw 0xa072555405e32b02 0x140e4aaa80bc6560 0x50307c7c01e38382 0x4a060f8f803c7070

def z585 : W := mkw 0xa0fb73f325800903 0xd41f6e7e64b00120 0x05ebe3e007004d81 0x00bd7c7c00e009b0

def z586 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xd0b07ffff0000000 0x7a160ffffe000000

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x9a10001c00000000 0x7342000380000000

def z588 : W := mkw 0x500fd6834a5f5461 0x8a01fad0694bea8c 0x600ffc03c01f8060 0x0c01ff807803f00c

def z589 : W := mkw 0x280823762024ebd1 0x4501046ec4049d7a 0xf7a863fe311fffff 0xfef50c7fc623ffff

def z590 : W := mkw 0xf00d82874fbc7f61 0x9e01b050e9f78fec 0xafcf8383cffc7fe7 0xb5f9f07079ff8ffc

def z591 : W := mkw 0x087a72222004c0d3 0x410f4e444400981a 0xff7ffe62311fc3ff 0xdfefffcc4623f87f

def z592 : W := mkw 0xd07fd6834fdf5463 0x9a0ffad069fbea8c 0x7e7ffc03cfff8063 0x8fcfff8079fff00c

def z593 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x1e70007c0fe00383 0xc3ce000f81fc0070

def z594 : W := mkw 0x0070015000000002 0x000e002a00000000 0x9ff003fc01004387 0xf3fe007f80200870

def z595 : W := mkw 0x0008222220000001 0x4001044444000000 0xf62862623012027e 0xdec50c4c4602404f

def z596 : W := mkw 0xa878237625a4ebd3 0x550f046ec4b49d7a 0xf738627e31ffc3ff 0xdee70c4fc63ff87f

def z597 : W := mkw 0xd07fd2834f9d5463 0x9a0ffa5069f3aa8c 0xafefe383cf1dfc65 0xb5fdfc7079e3bf8c

def z598 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x81000262311fc3ff 0xd020004c4623f87f

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x0520026001004181 0x00a4004c00200830

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x8a00000008003004 0xb140000001000600

def z601 : W := mkw 0x0072500000000002 0x000e4a0000000000 0x7e7ffc00011f8003 0x8fcfff800023f000

def z602 : W := mkw 0xb470095cd5a03b2a 0x368e012b9ab40765 0x9ff003ffffe07fff 0xf3fe007ffffc0fff

def z603 : W := mkw 0xd077d4814fdb1422 0x9a0efa9029fb6284 0x7efffd81cfffbc03 0xafdfffb039fff780

def z604 : W := mkw 0x1000000040001020 0x0200000008000204 0x80000003c0003064 0x300000007800060c

def z605 : W := mkw 0x04fb7fffb062220b 0xe09f6ffff60c4441 0xfefffffff0e2021a 0x7fdffffffe1c4043

def z606 : W := mkw 0x0000040000420000 0x0000008000084000 0x50101c0000e20002 0x0a020380001c4000

def z607 : W := mkw 0x400480000a180000 0x0800900001430000 0xafcf83800e1c7c05 0xb5f9f07001c38f80

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0x9200000000000206 0xd240000000000040

def z609 : W := mkw 0xc476dc0c9ffb220a 0x388edb8193ff6441 0x7e7ffc1c3fff821b 0xcfcfff8387fff043

def z610 : W := mkw 0x8070000005800002 0x100e000000b00000 0x7e7860000fff8003 0x8fcf0c0001fff000

def z611 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x0000000230000078 0x000000004600000f

def z612 : W := mkw 0x8070000005800002 0x100e000000b00000 0x085000000ee00000 0x010a000001dc0000

def z613 : W := mkw 0xb07401544db03b22 0x160e802a89b60764 0xbff403ffcff07fe7 0xf7fe807ff9fe0ffc

def z614 : W := mkw 0x540d8e8bda5e5469 0xaa81b1d17b4bca8d 0xefcf9f83fe1e7c7d 0xbdf9f3f07fc3cf8f

def z615 : W := mkw 0xe07481540fb82b02 0x1c0e902a81f70560 0xbfff83fc0ffc7f87 0xf7fff07f81ff8ff0

def z616 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x76286002311f807b 0x8ec50c004623f00f

def z617 : W := mkw 0xa0fb7bffb5a02b03 0xf41f6f7ff6b40560 0xfefffffffee03c00 0x7fdfffffffdc0780

def z618 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x97286260010dc387 0xd2e50c4c0021b870

def z619 : W := mkw 0xb40404044df23b28 0x1680808089be4765 0x010000000ff27fff 0x8020000001fe4fff

def z620 : W := mkw 0x700d83d74a3c7f61 0x8e01b07ae9478fec 0xafcf83ffce1c7fe5 0xf5f9f07ff9c38ffc

def z621 : W := mkw 0x00fb7bffb0202203 0xe01f6f7ff6040440 0xfefffffff8e03206 0xffdfffffff1c0640

def z622 : W := mkw 0x0070015000000002 0x000e002a00000000 0x04e003e000000000 0x009c007c00000000

def z623 : W := mkw 0x140d0e8fd8723229 0xa281a1d1fb0e4645 0xfedf9f9ff8f2327e 0xffdbf3f3ff1e464f

def z624 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ef003fc01e00382 0x73de007f803c0070

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x7200000000120002 0x8e40000000024000

def z626 : W := mkw 0x0000080890000000 0x2000010112000000 0xfa141c1ff012027e 0xff428383fe02404f

def z627 : W := mkw 0x14740d5cd872322a 0x228e81ab9b0e4645 0xfef41ffff8f2327e 0xffde83ffff1e464f

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x500000003002021a 0x4a00000006004043

def z629 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x58141c1df8e2321a 0x6b028383bf1c4643

def z630 : W := mkw 0x5406dc0cda7b3228 0x2a80db819b4f6645 0xfa1ffc1ff8ffb27e 0xff43ff83ff1ff64f

def z631 : W := mkw 0x1009028340045461 0x8201205068008a8c 0xafcf8383c0007c64 0x35f9f07078000f8c

def z632 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x6e4ffc000e1f8001 0x8dc9ff8001c3f000

def z633 : W := mkw 0xa0f359dd95a02b02 0xb41e6b3bb2b40560 0x08d79d9dcee03c00 0x211af3b3b9dc0780

def z634 : W := mkw 0x14fb7bfff020322b 0xe29f6f7ffe040645 0xfefffffff000327c 0x7fdffffffe00064f

def z635 : W := mkw 0x50fffbfbfa1c5463 0xea1fff7f7f438a8c 0xfefffffff01c0060 0x7fdffffffe03800c

def z636 : W := mkw 0x887822222584c0d3 0x510f044444b0981a 0xff7862623fffc3ff 0xdfef0c4c47fff87f

def z637 : W := mkw 0x08892bfbb004c0d1 0xe111257f7600981a 0xf7a863fff11fc3ff 0xfef50c7ffe23f87f

def z638 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xaa141c1fc8f03064 0xb5428383f91e060c

def z639 : W := mkw 0xe87ef7762fffebd3 0x5d0fdeeec5fffd7a 0xfffffffe3fffffff 0xffffffffc7ffffff

def z640 : W := mkw 0x00fb73f320000003 0xc01f6e7e64000000 0x9efbe3fc00000000 0x73df7c7f80000000

def z641 : W := mkw 0x80f27d78b5c30002 0x701e4faf16b86000 0x50307c7c31e38002 0x4a060f8f863c7000

def z642 : W := mkw 0x080c26222856c0d1 0x410184c4450ad81a 0xff3c7e6239ffc3ff 0xdfe78fcc473ff87f

def z643 : W := mkw 0xe076d5540ffb2b02 0x1c0edaaa81ff6560 0x08d79d9c0ee03c00 0x211af3b381dc0780

def z644 : W := mkw 0xa070015005800902 0x140e002a00b00120 0x9ff003fc07004d81 0x73fe007f80e009b0

def z645 : W := mkw 0x4076d4000a5b0002 0x080eda80014b6000 0x7e7ffc00001f8000 0x0fcfff800003f000

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x2e4f800000000000 0x05c9f00000000000

def z647 : W := mkw 0x0000000400202200 0x0000000080040440 0x8000001c00003204 0x7000000380000640

def z648 : W := mkw 0x0000202020000000 0x4000040404000000 0x5020606030000000 0x4a040c0c06000000

def z649 : W := mkw 0xe07485540ffb2b02 0x1c0e90aa81ff6560 0x9ff003fc0fffff87 0xf3fe007f81fffff0

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x26080000001c0001 0x84c1000000038000

def z651 : W := mkw 0x0072515000000002 0x000e4a2a00000000 0xfefffffc00000000 0x7fdfffff80000000

def z652 : W := mkw 0x0000080890000000 0x2000010112000000 0x50101c1c30000000 0x4a02038386000000

def z653 : W := mkw 0x1400080cd0203228 0x228001019a040645 0xfa141c1ff000327c 0x7f428383fe00064f

def z654 : W := mkw 0x0008020200044041 0x0001004040008808 0xf7080202301e427f 0xdee100404603c84f

def z655 : W := mkw 0x8072540005c30002 0x100e4a8000b86000 0x7e7ffc0001e38002 0x0fcfff80003c7000

def z656 : W := mkw 0x0000080890000000 0x2000010112000000 0x08141c1dc0000000 0x21028383b8000000

def z657 : W := mkw 0x40008000020c4440 0x0800100000418888 0x01000000060c4c01 0x0020000000c18980

def z658 : W := mkw 0x540d8e8bda5e5469 0xaa81b1d17b4bca8d 0x600f9c03f01e0078 0x0c01f3807e03c00f

def z659 : W := mkw 0x500d82874a3c7661 0x8a01b050e9478ecc 0xbfdf839fcefc7e67 0xf7fbf073f9df8fcc

def z660 : W := mkw 0xd476dc0cdffb322a 0x3a8edb819bff6645 0x08579c1dcee03000 0x210af383b9dc0600

def z661 : W := mkw 0x84725c0c95e3220a 0x308e4b8192bc6441 0x50307c1c31e3821a 0x4a060f83863c7043

def z662 : W := mkw 0x148f7eabf8521029 0xe291efd57f0a4205 0x600ffc03f0120078 0x0c01ff807e02400f

def z663 : W := mkw 0x0070000000000002 0x000e000000000000 0x1e70000000000000 0x03ce000000000000

def z664 : W := mkw 0xa87823722584c9d3 0x550f046e44b0993a 0xf7e863e2371fcfff 0xdefd0c7c46e3f9ff

def z665 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xa7080262301c43fd 0xd4e1004c4603887f

def z666 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xe0041c1ff012327c 0x7c008383fe02464f

def z667 : W := mkw 0x4076d0000a180002 0x080eda0001430000 0x7e7ffc000e1c0001 0x8fcfff8001c38000

def z668 : W := mkw 0x00892bfbb0000001 0xe011257f76000000 0xaecf83fff0000000 0x75d9f07ffe000000

def z669 : W := mkw 0x408ffeabba5b0001 0xe811ffd5774b6000 0x600ffc03f01f8000 0x0c01ff807e03f000

def z670 : W := mkw 0x8072500005810002 0x100e4a0000b02000 0x0020600001018000 0x00040c0000203000

def z671 : W := mkw 0x8070000005800002 0x100e000000b00000 0x1030000001e00002 0x02060000003c0000

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x7628600000000000 0x0ec50c0000000000

def z673 : W := mkw 0x080000000004c0d0 0x010000000000981a 0x97200260011fc3ff 0xd2e4004c0023f87f

def z674 : W := mkw 0x0004040008520000 0x00008080010a4000 0x7e3c7c0009ff8003 0x8fc78f80013ff000

def z675 : W := mkw 0xc87ef6222fdfc0d3 0x590fdec445fbf81a 0x7e7ffc023fff807b 0x8fcfff8047fff00f

def z676 : W := mkw 0xc07484000fdb0002 0x180e908001fb6000 0x1e7000000fff8003 0x83ce000001fff000

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000230120078 0x0c0000004602400f

def z678 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x1e779c000fe00003 0x83cef38001fc0000

def z679 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x762ffc00011f8003 0x8ec5ff800023f000

def z680 : W := mkw 0x0800202020008090 0x4100040404001012 0xd72062603103c39f 0xdae40c4c06207873

def z681 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xe1086262301fc3fc 0x5c210c4c4603f87f

def z682 : W := mkw 0x1400000440203228 0x0280000088040645 0x000000000000327c 0x000000000000064f

def z683 : W := mkw 0xc0f7ddd99fdb0002 0xb81efbbb33fb6000 0x08d79d9dcee00000 0x211af3b3b9dc0000

def z684 : W := mkw 0x34040d5cd8723b28 0x268081ab9b0e4765 0xfb941ffff8f27ffe 0xff7283ffff1e4fff

def z685 : W := mkw 0x0800202020008090 0x4100040404001012 0x0000006030000398 0x4000000c06000073

def z686 : W := mkw 0xb4740d5cddf23b2a 0x368e81ab9bbe4765 0xfa341c7ff9f233fe 0xff46838fff3e467f

def z687 : W := mkw 0x887a762225c7c0d3 0x510f4ec444b8f81a 0xf7387e6231ffc3ff 0xdee70fcc463ff87f

def z688 : W := mkw 0xa078237625a02b03 0x540f046ec4b40560 0xfff863fe3fe07f87 0xffff0c7fc7fc0ff0

def z689 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0xfa141c1ff0120078 0x7f428383fe02400f

def z690 : W := mkw 0x00fb7aabb0000003 0xe01f6f5576000000 0x7e7ffc03f0000000 0x0fcfff807e000000

def z691 : W := mkw 0x00f92bfbb0000003 0xe01f257f76000000 0x9ef003fff0000000 0x73de007ffe000000

def z692 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x7a141c1dc8f23002 0xaf428383b91e4600

def z693 : W := mkw 0x0800202020008090 0x4100040404001012 0x76286060311f839b 0xcec50c0c0623f073

def z694 : W := mkw 0x1c0c2e2ef876f2f9 0x638185c5df0ede5f 0xfb141e7ff8f273fe 0xff6283cfff1e4e7f

def z695 : W := mkw 0x80fb7ffbb5c30003 0xf01f6fff76b86000 0xfefffffff1e38002 0x7fdffffffe3c7000

def z696 : W := mkw 0x1c040c0cd876f2f8 0x238081819b0ede5f 0xfb141c1ff9fff3ff 0xff628383ff3ffe7f

def z697 : W := mkw 0x080000000004c0d0 0x010000000000981a 0x01000000010dc181 0x002000000021b830

def z698 : W := mkw 0x00f2717020000002 0x401e4e2e04000000 0x0020606000000000 0x00040c0c00000000

def z699 : W := mkw 0x148f7eaff8723229 0xe291efd5ff0e4645 0xfa1ffc1ff8f2327e 0xff43ff83ff1e464f

def z700 : W := mkw 0x1c082a2ef024f2f9 0x63810545de049e5f 0x8100027ff00073fc 0x7020004ffe000e7f

def z701 : W := mkw 0x0009028300000001 0x8001205060000000 0x80800383c0000000 0x3010007078000000

def z702 : W := mkw 0x00892bfbb0000001 0xe011257f76000000 0xf6a863fff0000000 0x7ed50c7ffe000000

def z703 : W := mkw 0xa4700d5c95e22b0a 0x348e01ab92bc4561 0xdff01ffc3fe27f9f 0xfbfe03ff87fc4ff3

def z704 : W := mkw 0x500480004a1c5460 0x0a00900009438a8c 0x2f4f80000e1c7c65 0x85e9f00001c38f8c

def z705 : W := mkw 0x0000000400202200 0x0000000080040440 0x0810001c08e03000 0x21020003811c0600

def z706 : W := mkw 0xe072d15407a92b02 0x1c0e5a2a80f52560 0x9ffbe3fc0fedff87 0xf3ff7c7f81fdbff0

def z707 : W := mkw 0x0083588990000000 0xa0106b1132000000 0x08179c1dc0000000 0x2102f383b8000000

def z708 : W := mkw 0x50f6f978fa1c5462 0x6a1edf2f1f438a8c 0x51307c7c3e1c7c65 0xca260f8f87c38f8c

def z709 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff01c0001 0xffdffffffe038000

def z710 : W := mkw 0xd076d4004fdb1422 0x1a0eda8009fb6284 0x7e7ffc000fffbc03 0x8fcfff8001fff780

def z711 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xbfdf8383cefc7c67 0xb7fbf07079df8f8c

def z712 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xafcf8383ce1ffc7d 0xb5f9f07079c3ff8f

def z713 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0x28cf8183ce003c00 0x2519f03079c00780

def z714 : W := mkw 0x0000080890000000 0x2000010112000000 0xfe5f9c1ff0000000 0x7fcbf383fe000000

def z715 : W := mkw 0x8072540005c30002 0x100e4a8000b86000 0x7e7ffc0001ff8003 0x8fcfff80003ff000

def z716 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x08d79ffdc0000000 0x211af3ffb8000000

def z717 : W := mkw 0x580da6a36a5ed4f1 0xcb01b4d46d4bda9e 0xffffffe3ffffffff 0xfffffffc7fffffff

def z718 : W := mkw 0x54048c0cda7a3228 0x2a8091819b4f4645 0xfe7ffc1fffffb27f 0xffcfff83fffff64f

def z719 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x89c78383ce1c7c65 0xb138f07079c38f8c

def z720 : W := mkw 0xd472d80cd7a9322a 0x3a8e5b019af52645 0x846be01ff70db27d 0x708d7c03fee1b64f

def z721 : W := mkw 0x0072580890000002 0x200e4b0112000000 0xfe7ffc1ff11f827f 0xffcfff83fe23f04f

def z722 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf6286262311f83fa 0x5ec50c4c4623f07f

def z723 : W := mkw 0xa0f2595c95a02b02 0x341e4b2b92b40560 0x00101c1c00e00000 0x00020383801c0000

def z724 : W := mkw 0x540484044a7a3628 0x0a809080894f46c5 0x000000000ef23e7e 0x8000000001de47cf

def z725 : W := mkw 0x500480004a181020 0x0a00900009430204 0xafcf8383ce1c7c65 0xb5f9f07079c38f8c

def z726 : W := mkw 0x6006d5540a7b2b00 0x0c00daaa814f6560 0xe18ffffc001fff84 0x7c31ffff8003fff0

def z727 : W := mkw 0x540484044a7a3628 0x0a809080894f46c5 0x000000000ee03c00 0x0000000001dc0780

def z728 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x7efffffdc0000000 0x2fdfffffb8000000

def z729 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x6e5ffc000eff8001 0x8dcbff8001dff000

def z730 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffffe003c00 0x7fdfffffffc00780

def z731 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x60141c1ff0f20078 0x0c028383fe1e400f

def z732 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfefffffff11f807b 0xffdffffffe23f00f

def z733 : W := mkw 0xc006d4000fdb0000 0x1800da8001fb6000 0x762ffc000fff8003 0x8ec5ff8001fff000

def z734 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff1038002 0x7fdffffffe207000

def z735 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xf2141c1ff0f2027e 0xde428383fe1e404f

def z736 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x78141c1ff8f2327a 0x6f028383ff1e464f

def z737 : W := mkw 0x087a7a2ab004c0d3 0x610f4f455600981a 0xff7ffe7ff11fc3ff 0xffefffcffe23f87f

def z738 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffefe3e3ff1dfde5 0xfffdfc7c7fe3bfbc

def z739 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383ce0c7c01 0x35f9f07079c18f80

def z740 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x8df003fc0fe07f85 0x71be007f81fc0ff0

def z741 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa347c1ff9f3b27e 0xff468f83ff3e764f

def z742 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffcf8383fe1c7c65 0xfff9f0707fc38f8c

def z743 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffff0004064 0x7ffffffffe00080c

def z744 : W := mkw 0x5c0ca6266a7ef6f9 0x4b8194c4cd4fdedf 0xf72862623fffffff 0xdee50c4c47ffffff

def z745 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xffffffe00fffff87 0xfffffffc01fffff0

def z746 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafefe3e3ff1dfffd 0xf5fdfc7c7fe3bfff

def z747 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xbfef83e3ce1c7c65 0xf7fdf07c79c38f8c

def z748 : W := mkw 0xa072515405a02b02 0x140e4a2a80b40560 0xdff07ffc0fe07f87 0xfbfe0fff81fc0ff0

def z749 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0xe00ffc1ff0000000 0x7c01ff83fe000000

def z750 : W := mkw 0xd076d4004fdb1022 0x1a0eda8009fb6204 0xfe7ffc03ffffb27f 0xffcfff807ffff64f

def z751 : W := mkw 0xa072515405a02b02 0x140e4a2a80b40560 0xfffffffc0fffff87 0xffffffff81fffff0

def z752 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x5cfffffdf0000000 0x6b9fffffbe000000

def z753 : W := mkw 0xf476dd5cdffb3b2a 0x3e8edbab9bff6765 0x08d79d9dcee03c00 0x211af3b3b9dc0780

def z754 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xaecf8383ce1c3c60 0x35d9f07079c3878c

def z755 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x2e7ffc000ffd8001 0x85cfff8001ffb000

def z756 : W := mkw 0x0001088990000000 0xa000211132000000 0xfad79d9ff0000000 0x7f5af3b3fe000000

def z757 : W := mkw 0x1c092aaff024f6f9 0xe3812555fe049edf 0x818003fff0007ffc 0x7030007ffe000fff

def z758 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff286262391ff3ff 0xffe50c4c4723fe7f

def z759 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc020fff8067 0x9fcfff8041fff00c

def z760 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf2286062311f83fe 0xde450c0c4623f07f

def z761 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0x80879ffff0000000 0x7010f3fffe000000

def z762 : W := mkw 0x14000c0cd0623228 0x228001819a0c4645 0x50101c1ff0e2027a 0x4a020383fe1c404f

def z763 : W := mkw 0x00fb7aabb0000003 0xe01f6f5576000000 0xfe7ffc1ff0000000 0x7fcfff83fe000000

def z764 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x1df003fc0fe07f83 0x63be007f81fc0ff0

def z765 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xefefe3e3ff1ffdfd 0xbdfdfc7c7fe3ffbf

def z766 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xf0bffffff0000000 0x7e17fffffe000000

def z767 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff6862623f1fc3ff 0xdfed0c4c47e3f87f

def z768 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe3c7c1ff8f2327e 0xffc78f83ff1e464f

def z769 : W := mkw 0x08f359d99004c0d2 0xa11e6b3b3200981a 0x09d79d9dc11fc3ff 0xa13af3b3b823f87f

def z770 : W := mkw 0x007b53d300000003 0x800f6a7a60000000 0xfeffffffc0000000 0x7fdffffff8000000

def z771 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf83e3ce1c7fe5 0xf5f9f07c79c38ffc

def z772 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x9ef79ffff0000000 0x73def3fffe000000

def z773 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x28c78183ce103c60 0x2518f03079c2078c

def z774 : W := mkw 0xa0fb7bfbb5800903 0xf41f6f7f76b00120 0xffffffffff007d85 0xffffffffffe00fb0

def z775 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff3c7e62311fc3ff 0xdfe78fcc4623f87f

def z776 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffff01e427f 0xfffffffffe03c84f

def z777 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfa3ffc7ff0000000 0x7f47ff8ffe000000

def z778 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7286262311fc3ff 0xdee50c4c4623f87f

def z779 : W := mkw 0x500580814a181420 0x8a00b01029430284 0xaac78183ce003c00 0x3558f03079c00780

def z780 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff000027c 0x7fdffffffe00004f

def z781 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc600fff8383 0xcfcfff8c01fff070

def z782 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7a3ffc0009ff8002 0x8f47ff80013ff000

def z783 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff8e00002 0xffdfffffff1c0000

def z784 : W := mkw 0xa878237625a4ebd3 0x550f046ec4b49d7a 0x68d8619e3effbc78 0x2d1b0c33c7dff78f

def z785 : W := mkw 0x080020202004c0d0 0x410004040400981a 0x50206060311f83fa 0x4a040c0c0623f07f

def z786 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff0000206 0xffdffffffe000040

def z787 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x681ffc0008ff8000 0x0d03ff80011ff000

def z788 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0x28df9d9fc0000000 0x251bf3b3f8000000

def z789 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0xafcf8383ce007c05 0xb5f9f07079c00f80

def z790 : W := mkw 0x14ff77f76872322b 0xc29feefeed0e4645 0x04ebe3e008f2327e 0x809d7c7c011e464f

def z791 : W := mkw 0x54048c0cda7b3228 0x2a8091819b4f6645 0xfa141c1ff8ffb27e 0xff428383ff1ff64f

def z792 : W := mkw 0xd076d4004fdb1022 0x1a0eda8009fb6204 0xffffff83cffffc67 0xbffffff079ffff8c

def z793 : W := mkw 0x500da2a36a181421 0xca01b4546d430284 0xfeefe3e3fe003c00 0x7fddfc7c7fc00780

def z794 : W := mkw 0xdc0484044ffff2f8 0x1b80908089fffe5f 0x010000000ffff3ff 0x8020000001fffe7f

def z795 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xffffffffff007f87 0xffffffffffe00ff0

def z796 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffefe3e3fe1c7ffd 0xfffdfc7c7fc38fff

def z797 : W := mkw 0x80f359d995800002 0xb01e6b3b32b00000 0x1ef79d9dcfe00003 0xa3def3b3b9fc0000

def z798 : W := mkw 0x400d82830a180001 0x8801b05061430000 0xafcf8383ce1c7c05 0xb5f9f07079c38f80

def z799 : W := mkw 0x1c892bfff024f2f9 0xe391257ffe049e5f 0x818003fff00073fc 0x7030007ffe000e7f

def z800 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xaa141c1ff8f0327c 0xf5428383ff1e064f

def z801 : W := mkw 0x2000015400202b00 0x0400002a80040560 0x9fd003fc0ee07f87 0xf3fa007f81dc0ff0

def z802 : W := mkw 0x5c0484044a7ef6f8 0x0b809080894fdedf 0x010000000fffffff 0x8020000001ffffff

def z803 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x0cfffd9dc0000000 0x219fffb3b8000000

def z804 : W := mkw 0xa000015405a02b00 0x1400002a80b40560 0x818003fc0ee07f84 0x7030007f81dc0ff0

def z805 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xbfef8383cf1c7c67 0xb7fdf07079e38f8c

def z806 : W := mkw 0x28892bffb024ebd1 0xe511257ff6049d7a 0x818003fff0007ffc 0x7030007ffe000fff

def z807 : W := mkw 0xa08b7aafb5a02b01 0xf4116f55f6b40560 0x610ffc03ffe07f87 0x8c21ff807ffc0ff0

def z808 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xbfdf839fce1c7c65 0xf7fbf073f9c38f8c

def z809 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff003fe3fe07f87 0xfffe007fc7fc0ff0

def z810 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0xaecf8383ce103c64 0xb5d9f07079c2078c

def z811 : W := mkw 0xa000015405a02b00 0x1400002a80b40560 0x8fc003fc0fe07f87 0xf1f8007f81fc0ff0

def z812 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xeedfff9ff0000000 0x3ddbfff3fe000000

def z813 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x2dcf8383ce1c7c61 0x25b9f07079c38f8c

def z814 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfefffffff0000398 0x7fdffffffe000073

def z815 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xf73ffe7ff11fc3ff 0xdee7ffcffe23f87f

def z816 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x85e003fc0fe07f87 0xf0bc007f81fc0ff0

def z817 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x28cf8181ce1c3c00 0x2519f03039c38780

def z818 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffe600fff8003 0xdfcfffcc01fff000

def z819 : W := mkw 0x1c0c2e2ef876f2f9 0x638185c5df0ede5f 0x0d3c7e7dc9edf181 0x21a78fcfb93dbe30

def z820 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7f7ffe600fffc183 0x8fefffcc01fff830

def z821 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff6004c01 0x7ffffffffec00980

def z822 : W := mkw 0xc076d5500fdb0002 0x180edaaa01fb6000 0x7effffe00fff8003 0x8fdffffc01fff000

def z823 : W := mkw 0xc87ef6222fdfc0d3 0x590fdec445fbf81a 0x89579e623ee043fc 0x512af3cc47dc087f

def z824 : W := mkw 0x54048c0cda7a3228 0x2a8091819b4f4645 0xfa579c1ffef2327e 0xff4af383ffde464f

def z825 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfefffffff01f827e 0xffdffffffe03f04f

def z826 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0x68dffd9ff01f8078 0x2d1bffb3fe03f00f

def z827 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383cf1c7fe7 0xb5f9f07079e38ffc

def z828 : W := mkw 0x0000000400202200 0x0000000080040440 0x9ff003fc0fe07f87 0xf3fe007f81fc0ff0

def z829 : W := mkw 0x0072580890000002 0x200e4b0112000000 0xfa579c1ff0000000 0x7f4af383fe000000

def z830 : W := mkw 0x0001008100000000 0x8000201020000000 0x8fc78381ce007c05 0xb1f8f07039c00f80

def z831 : W := mkw 0xa000015405a02b00 0x1400002a80b40560 0x97a003fc0fe07f87 0xf2f4007f81fc0ff0

def z832 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc000fed8001 0x0fcfff8001fdb000

def z833 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfb141c1ff9f273ff 0xff628383ff3e4e7f

def z834 : W := mkw 0xd076d4004fdb1022 0x1a0eda8009fb6204 0x7e7ffc000fffb067 0x8fcfff8001fff60c

def z835 : W := mkw 0x44098e8f926e6649 0xa88131d1f24dccc9 0x55db9f9c36ee4e1b 0x4abb73f386ddc9c3

def z836 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xf0141c1ff0f2327e 0x7e028383fe1e464f

def z837 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafcf8383fe1c7c7d 0xb5f9f0707fc38f8f

def z838 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x55286260311fc3ff 0xcaa50c4c0623f87f

def z839 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa341c7ff9f233fe 0xff46838fff3e467f

def z840 : W := mkw 0x100d028348101021 0x8201a05069020204 0xafcf8383ce107c65 0xb5f9f07079c20f8c

def z841 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfefffffff01c0060 0x7fdffffffe03800c

def z842 : W := mkw 0x088b7bfbb004c0d1 0xe1116f7f7600981a 0xf7affffff11fc3ff 0xfef5fffffe23f87f

def z843 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xaedf9ffff0000000 0x75dbf3fffe000000

def z844 : W := mkw 0x00790bdb90000003 0xa00f217b72000000 0xfeff9ffff0000000 0x7fdff3fffe000000

def z845 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x601ffc1ff0000000 0x0c03ff83fe000000

def z846 : W := mkw 0x00fb7bfbb0044443 0xe01f6f7f76008888 0xfffffffff0004c00 0x7ffffffffe000980

def z847 : W := mkw 0x500580814a181420 0x8a00b01029430284 0xafc78383ce107c65 0xb5f8f07079c20f8c

def z848 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x8ed79f9dc0000000 0x31daf3f3b8000000

def z849 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafcf83e3ce1c7de5 0xb5f9f07c79c38fbc

def z850 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x787ffc000fff8002 0x0f0fff8001fff000

def z851 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x29cf8183ce1c7c65 0xa539f03079c38f8c

def z852 : W := mkw 0x00fb5bdb90044043 0xa01f6b7b72008808 0xafdf9f9fc01c4065 0xb5fbf3f3f803880c

def z853 : W := mkw 0xdc0ca6266ffff2f9 0x5b8194c4cdfffe5f 0xf72862623ffff3ff 0xdee50c4c47fffe7f

def z854 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafcf83e3ff1fffff 0xf5f9f07c7fe3ffff

def z855 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x0ccf8181ce0c3c01 0x2199f03039c18780

def z856 : W := mkw 0x0002580890000000 0x20004b0112000000 0xfa1ffc1ff0000000 0x7f43ff83fe000000

def z857 : W := mkw 0x0009028300000001 0x8001205060000000 0xaecf8383ce003c00 0x35d9f07079c00780

def z858 : W := mkw 0xd076d4004fdb1022 0x1a0eda8009fb6204 0x7e7ffc03cfff8063 0x8fcfff8079fff00c

def z859 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff01fc3fc 0x7ffffffffe03f87f

def z860 : W := mkw 0x907b568345c75463 0x920f6ad068b8ea8c 0xd1b07f83c1e3fc66 0x3a360ff0783c7f8c

def z861 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x7efffd9dc11f8003 0xafdfffb3b823f000

def z862 : W := mkw 0x54048c0cda7a3228 0x2a8091819b4f4645 0xfa141c1ffefe327f 0xff428383ffdfc64f

def z863 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc0001ff8002 0x0fcfff80003ff000

def z864 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff10fc39b 0x7ffffffffe21f873

def z865 : W := mkw 0x0076540008520002 0x000eca80010a4000 0x7e7ffc0009ff8003 0x8fcfff80013ff000

def z866 : W := mkw 0x0001008100000000 0x8000201020000000 0x08c78181ce003c00 0x2118f03039c00780

def z867 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc000fff827f 0x8fcfff8001fff04f

def z868 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0x7efffdfdf0000000 0x6fdfffbfbe000000

def z869 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x89c78381ce007c04 0x3138f07039c00f80

def z870 : W := mkw 0x088b7bfbb004c0d1 0xe1116f7f7600981a 0xe18ffffff01fc3fc 0x7c31fffffe03f87f

def z871 : W := mkw 0xa072515405a02b02 0x140e4a2a80b40560 0x9ffbe3fc0fe07f87 0xf3ff7c7f81fc0ff0

def z872 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff863fc0fedff87 0xf3ff0c7f81fdbff0

def z873 : W := mkw 0xa8f2797cb5a0ab92 0x751e4f2f96b41572 0x50307c7c31e3839a 0x4a060f8f863c7073

def z874 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xaacf8183ce1c3c64 0xb559f03079c3878c

def z875 : W := mkw 0xc006d4000fdb0000 0x1800da8001fb6000 0x600ffc000eff8000 0x0c01ff8001dff000

def z876 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0x0ccf8381ce003c00 0x2199f07039c00780

def z877 : W := mkw 0x500d86834a5e5461 0x8a01b0d0694bca8c 0xffffff83cffffc67 0xbffffff079ffff8c

def z878 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfefffffff1018180 0x7fdffffffe203030

def z879 : W := mkw 0xa0f359d995800902 0xb41e6b3b32b00120 0x0df79ffdc7004d81 0x21bef3ffb8e009b0

def z880 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0xfedf9f9ff0000000 0x7fdbf3f3fe000000

def z881 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x00179c1dc0000000 0x0002f383b8000000

def z882 : W := mkw 0x080922a32004c0d1 0xc10124546400981a 0xffefe3e3ff1fffff 0xfffdfc7c7fe3ffff

def z883 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xffefe383cf1fffff 0xbffdfc7079e3ffff

def z884 : W := mkw 0x5805a0a16a1894b0 0xcb00b4142d431296 0x58e7e1e1ff03bf9a 0x6b1cfc3c3fe077f3

def z885 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0xfef79ffff0000000 0x7fdef3fffe000000

def z886 : W := mkw 0x500580814a181420 0x8a00b01029430284 0xfac78183fe123e7e 0xff58f0307fc247cf

def z887 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff01f8000 0x7fdffffffe03f000

def z888 : W := mkw 0x500580814a181420 0x8a00b01029430284 0xafcf8381ce1c7c05 0xb5f9f07039c38f80

def z889 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff01243fe 0xfffffffffe02487f

def z890 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfb941f9ff8f27e7e 0xff7283f3ff1e4fcf

def z891 : W := mkw 0x00f27978b0000002 0x601e4f2f16000000 0xfe7ffc7ff0000000 0x7fcfff8ffe000000

def z892 : W := mkw 0xc8fbf3f3278dc0d3 0xd91f7e7e64f1b81a 0x05ebe3e0070dc181 0x00bd7c7c00e1b830

def z893 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfefffffff0038018 0x7fdffffffe007003

def z894 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfad41d9ffef23e7e 0xff5a83b3ffde47cf

def z895 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x7e3ffc0009ff8003 0x8fc7ff80013ff000

def z896 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x08c78183ce003c60 0x2118f03079c0078c

def z897 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc1c0fff8003 0xffcfff8381fff000

def z898 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x8ff003fc0fe07d85 0xb1fe007f81fc0fb0

def z899 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa1c7c1ff8ffb27e 0xff438f83ff1ff64f

def z900 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffcf83e3fe1e7fff 0xfff9f07c7fc3cfff

def z901 : W := mkw 0x00090a8b90000001 0xa001215172000000 0xaedf9f9fc0000000 0x35dbf3f3f8000000

def z902 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffff11c43e7 0xfffffffffe23887c

def z903 : W := mkw 0x8072500005800002 0x100e4a0000b00000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z904 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0x48d7fd9df0000000 0x291affb3be000000

def z905 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xd8f7fffff0000000 0x7b1efffffe000000

def z906 : W := mkw 0x0800202020008090 0x4100040404001012 0xf6286062311f83ff 0xdec50c0c4623f07f

def z907 : W := mkw 0x080020202004c0d0 0x410004040400981a 0xf3206062311fc3ff 0xde640c0c4623f87f

def z908 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0xeecffffff0000000 0x7dd9fffffe000000

def z909 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff38627e311fc3ff 0xffe70c4fc623f87f

def z910 : W := mkw 0xc08daffbbfdb0001 0xf811b5ff77fb6000 0x808003ffffff8003 0xf010007ffffff000

def z911 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafefe383cf1dfc65 0xb5fdfc7079e3bf8c

def z912 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff11fc183 0xfffffffffe23f830

def z913 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x85cb8383ce1c7c65 0xb0b9707079c38f8c

def z914 : W := mkw 0x4076d4000a5b0002 0x080eda80014b6000 0x7e7ffc0008ff8002 0x8fcfff80011ff000

def z915 : W := mkw 0x500d86834a5f5461 0x8a01b0d0694bea8c 0xafcf8383ce1ffc65 0xb5f9f07079c3ff8c

def z916 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff10d8001 0x7fdffffffe21b000

def z917 : W := mkw 0xa8fb7bfbb584c9d3 0xf51f6f7f76b0993a 0xfffffffff71fcfff 0xfffffffffee3f9ff

def z918 : W := mkw 0x0001088990000000 0xa000211132000000 0x08d79d9dc0000000 0x211af3b3b8000000

def z919 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x9efffffdc0000000 0x73dfffffb8000000

def z920 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfefffffff0000078 0x7fdffffffe00000f

def z921 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff103c3fe 0x7ffffffffe20787f

def z922 : W := mkw 0x50098283420c5461 0x8a01305068418a8c 0x81c38383c6007c64 0x3038707078c00f8c

def z923 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0xabc78183ce1c7c65 0xb578f03079c38f8c

def z924 : W := mkw 0x540d86834a5e5469 0x8a81b0d0694bca8d 0xafcf8383ce1e7c7d 0xb5f9f07079c3cf8f

def z925 : W := mkw 0x0072580890000002 0x200e4b0112000000 0x7e7ffc1dc0000000 0x2fcfff83b8000000

def z926 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff003fc0ee07f84 0x73fe007f81dc0ff0

def z927 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc000fffb007 0xbfcfff8001fff600

def z928 : W := mkw 0x14000c0cd0623228 0x228001819a0c4645 0xf2101c1ff0f2327e 0xfe420383fe1e464f

def z929 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xffffffffff1fffff 0xffffffffffe3ffff

def z930 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff0100064 0xffdffffffe02000c

def z931 : W := mkw 0xf07d83d74fbc7f63 0x9e0fb07ae9f78fec 0x303f807fc1fc03e2 0x4607f00ff83f807c

def z932 : W := mkw 0xa8fb73f32584c9d3 0xd51f6e7e64b0993a 0x05ebe3e0070dcd81 0x00bd7c7c00e1b9b0

def z933 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x08c78181ce1c3c01 0xa118f03039c38780

def z934 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x6cfffffff0000000 0x2d9ffffffe000000

def z935 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x601ffc0000ff8000 0x0c03ff80001ff000

def z936 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x1ff003fc0fe07d83 0xa3fe007f81fc0fb0

def z937 : W := mkw 0xa0f2595c95a02b02 0x341e4b2b92b40560 0x10301c7c01e00382 0x4206038f803c0070

def z938 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0x08d79dfdf0000000 0x611af3bfbe000000

def z939 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x85286262311fc3ff 0xd0a50c4c4623f87f

def z940 : W := mkw 0xf00484044fff7f60 0x1e00908089ffefec 0x010000000fffffe7 0x8020000001fffffc

def z941 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x8ec78381ce003c00 0x31d8f07039c00780

def z942 : W := mkw 0x500d86834a5e5461 0x8a01b0d0694bca8c 0xefcf9f83ce1e7c65 0xbdf9f3f079c3cf8c

def z943 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x0c7ffc000fff8003 0x818fff8001fff000

def z944 : W := mkw 0x14000c0cd0623228 0x228001819a0c4645 0xfa141c1ff0e2327e 0x7f428383fe1c464f

def z945 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe341c1ff9f2327f 0xffc68383ff3e464f

def z946 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0x600ffc7ff0000000 0x4c01ff8ffe000000

def z947 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x74fffffff0000000 0x4e9ffffffe000000

def z948 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x08cf8181ce0c3c00 0x2119f03039c18780

def z949 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383ce007c64 0x35f9f07079c00f8c

def z950 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfb141c1ffef27e7f 0xff628383ffde4fcf

def z951 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x7ad79d9dc0000000 0x2f5af3b3b8000000

def z952 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc03cfff8003 0xbfcfff8079fff000

def z953 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7f7ffc000ffffc07 0x8fefff8001ffff80

def z954 : W := mkw 0x540484044a7e7668 0x0a809080894fcecd 0x010000000efc7c65 0x8020000001df8f8c

def z955 : W := mkw 0xa072515405a02b02 0x140e4a2a80b40560 0x9ff79ffc0fe07f87 0xf3fef3ff81fc0ff0

def z956 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0x608ffd9ff0000000 0x2c11ffb3fe000000

def z957 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x7e7ffc7ff0000000 0x4fcfff8ffe000000

def z958 : W := mkw 0xe076d4000fdb0902 0x1c0eda8001fb6120 0x7f7ffc000fffcd83 0x8fefff8001fff9b0

def z959 : W := mkw 0xc006d4000fdb0000 0x1800da8001fb6000 0x7a1ffc000fff8003 0x8f43ff8001fff000

def z960 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff11fc387 0xfffffffffe23f870

def z961 : W := mkw 0xe076d5500fdb0902 0x1c0edaaa01fb6120 0x7efffd800fff8c03 0x8fdfffb001fff180

def z962 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x9fe783e1cf007f87 0xf3fcf07c39e00ff0

def z963 : W := mkw 0x080922a32004c4d1 0xc10124546400989a 0xf7a863e2311fcfff 0xdef50c7c4623f9ff

def z964 : W := mkw 0x08f379f9b0008092 0xe11e6f3f36001012 0x58f7fdfdf103839a 0x6b1effbfbe207073

def z965 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xdff003fc3fe27f9f 0xfbfe007f87fc4ff3

def z966 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7a5ffc000eff8002 0x8f4bff8001dff000

def z967 : W := mkw 0x04000c0c90622208 0x20800181920c4441 0xfa141c1ff0f2027e 0xff428383fe1e404f

def z968 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x99f003fc0fe07f86 0x733e007f81fc0ff0

def z969 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0x68cfe183fe1fbc78 0x2d19fc307fc3f78f

def z970 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffefe383ff1ffe7f 0xfffdfc707fe3ffcf

def z971 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc000eff8000 0x0fcfff8001dff000

def z972 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x0df003fc0fe07f87 0xa1be007f81fc0ff0

def z973 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff003fc0fffff87 0xf3fe007f81fffff0

def z974 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x58d79d9df0000000 0x6b1af3b3be000000

def z975 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7efffd800fffbc03 0xafdfffb001fff780

def z976 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0x703ffc7ff11f83fa 0x4e07ff8ffe23f07f

def z977 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffefe3e3cf1fffe7 0xfffdfc7c79e3fffc

def z978 : W := mkw 0x007b5a8b90000003 0xa00f6b5172000000 0xfeffff9ff0000000 0x7fdffff3fe000000

def z979 : W := mkw 0x580580814a1cd4f0 0x8b00b01029439a9e 0x09c78181cf1fffff 0xa138f03039e3ffff

def z980 : W := mkw 0x500d86834a5e5461 0x8a01b0d0694bca8c 0xafcf8383cefe7c67 0xb5f9f07079dfcf8c

def z981 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x9ff79ffdc1004387 0xf3fef3ffb8200870

def z982 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xe8dffffff0000000 0x7d1bfffffe000000

def z983 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa141c1ff0f2027a 0x7f428383fe1e404f

def z984 : W := mkw 0x0072580890000002 0x200e4b0112000000 0x08579c1dc0000000 0x210af383b8000000

def z985 : W := mkw 0xc076d5500fdb0002 0x180edaaa01fb6000 0xfffffffc0ffffc07 0xffffffff81ffff80

def z986 : W := mkw 0xb4740d58ddd2192a 0x368e81ab1bba4325 0x65e41fe3f7124df9 0x0cbc83fc7ee249bf

def z987 : W := mkw 0xc076d5500fdb0002 0x180edaaa01fb6000 0x7efffd9c0fff8003 0xafdfffb381fff000

def z988 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffefe3e3fe1ffc7d 0xfffdfc7c7fc3ff8f

def z989 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xbff003fe0ff07fe7 0xf7fe007fc1fe0ffc

def z990 : W := mkw 0xe076d5500fdb0902 0x1c0edaaa01fb6120 0xfffffffc0fffcd83 0xffffffff81fff9b0

def z991 : W := mkw 0xa8fa7b7eb5a4ebd3 0x751f4f6fd6b49d7a 0xf7387e7e31ffc3ff 0xdee70fcfc63ff87f

def z992 : W := mkw 0xa4725d5c95e32b0a 0x348e4bab92bc6561 0x50307c7c31e3839a 0x4a060f8f863c7073

def z993 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa141c1ff9ffb27f 0xff428383ff3ff64f

def z994 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff41ffc0fe07f87 0xfffe83ff81fc0ff0

def z995 : W := mkw 0x080922a32004c0d1 0xc10124546400981a 0xf7a863e3f11fc3ff 0xfef50c7c7e23f87f

def z996 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x0dc78381ce007c01 0x21b8f07039c00f80

def z997 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfefffffff11f83fa 0x7fdffffffe23f07f

def z998 : W := mkw 0x54048c0cda7a3228 0x2a8091819b4f4645 0xfa1f9c1ff8fe327e 0xff43f383ff1fc64f

def z999 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xbff803fc0ffc7f87 0xf7ff007f81ff8ff0

def z1000 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x2ecf8183ce1c3c61 0xa5d9f03079c3878c

def z1001 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0x08c78181ce1c3c60 0x2118f03039c3878c

def z1002 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff002021a 0x7fdffffffe004043

def z1003 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff0007c04 0x7ffffffffe000f80

def z1004 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x70141c1ff8f2327e 0xce028383ff1e464f

def z1005 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xafcf83e3fe1c7c65 0xf5f9f07c7fc38f8c

def z1006 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xea141c1ff8f2307c 0xbd428383ff1e460f

def z1007 : W := mkw 0xe076d5500fdb0902 0x1c0edaaa01fb6120 0xffffffe00ffffd87 0xbffffffc01ffffb0

def z1008 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xefcfe3e3fe1ffffd 0xfdf9fc7c7fc3ffff

def z1009 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x8fd003fc0ee07f85 0xf1fa007f81dc0ff0

def z1010 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfadffd9ff0000000 0x7f5bffb3fe000000

def z1011 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x703ffc000fff8003 0x8e07ff8001fff000

def z1012 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xabc78383ce107c64 0xb578f07079c20f8c

def z1013 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x88d79ffdc0000000 0x711af3ffb8000000

def z1014 : W := mkw 0x080922a32004c0d1 0xc10124546400981a 0xf72fe263f11fc3ff 0xdee5fc4c7e23f87f

def z1015 : W := mkw 0x54048c0cda7a3628 0x2a8091819b4f46c5 0xfa141c1ffef23e7e 0xff428383ffde47cf

def z1016 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383cf1ffc67 0xb5f9f07079e3ff8c

def z1017 : W := mkw 0x50098283420c5461 0x8a01305068418a8c 0xa7cb8383c61c7c65 0xb4f9707078c38f8c

def z1018 : W := mkw 0xc076d5500fdb0002 0x180edaaa01fb6000 0xfffffffc0fffc387 0xffffffff81fff870

def z1019 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfefffffff00d8000 0x7fdffffffe01b000

def z1020 : W := mkw 0x50098283420c5461 0x8a01305068418a8c 0x8fcb8383ce0c7c65 0xb1f9707079c18f8c

def z1021 : W := mkw 0xd076d4004fdb1022 0x1a0eda8009fb6204 0x7e7ffc01cfffb003 0xafcfff8039fff600

def z1022 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe1c1c1ff8fe327f 0xffc38383ff1fc64f

def z1023 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0xfaf7fdfff0000000 0x7f5effbffe000000

def z1024 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff01c43fd 0xfffffffffe03887f

def z1025 : W := mkw 0x14000c0cd0623228 0x228001819a0c4645 0x80101c1ff0e0327c 0x70020383fe1c064f

def z1026 : W := mkw 0xa0f2797cb5a02b02 0x741e4f2f96b40560 0x50307c7c30e00000 0x4a060f8f861c0000

def z1027 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0x0defe3e1cf0dfd81 0x21bdfc7c39e1bfb0

def z1028 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x08d79d9ff0000000 0x211af3b3fe000000

def z1029 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0xfefffffdc0000000 0x7fdfffffb8000000

def z1030 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x763ffc0001ff8003 0x8ec7ff80003ff000

def z1031 : W := mkw 0x1400080cd0203228 0x228001019a040645 0xfa141c1ff8e0327e 0xff428383ff1c064f

def z1032 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0x0cdf9f9dc0000000 0x219bf3f3b8000000

def z1033 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffefe383ce1c7c65 0xbffdfc7079c38f8c

def z1034 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0xfe3ffe7ff0000000 0x7fc7ffcffe000000

def z1035 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffefe383ff1ffc7f 0xbffdfc707fe3ff8f

def z1036 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x7efffd9ff0000000 0x2fdfffb3fe000000

def z1037 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff10dc3fd 0x7ffffffffe21b87f

def z1038 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0x89d79ffff00043fc 0x713af3fffe00087f

def z1039 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xff7ffe623fffc3ff 0xdfefffcc47fff87f

def z1040 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffffe000001 0xffdfffffffc00000

def z1041 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xbfcf8383ce1c7e67 0xf7f9f07079c38fcc

def z1042 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x0cf79ffdc0000000 0x219ef3ffb8000000

def z1043 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff1004181 0x7ffffffffe200830

def z1044 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x085ffc000eed8000 0x010bff8001ddb000

def z1045 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xd0101c1ff8f2327e 0xfa020383ff1e464f

def z1046 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x08c78181ce103c64 0xa118f03039c2078c

def z1047 : W := mkw 0xc076d5500fdb0002 0x180edaaa01fb6000 0x7e7ffc7c0fff8003 0xcfcfff8f81fff000

def z1048 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff38626239ffc3ff 0xdfe70c4c473ff87f

def z1049 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xbff403ffcfe07f87 0xf7fe807ff9fc0ff0

def z1050 : W := mkw 0x080020202004c0d0 0x410004040400981a 0x77286060311fc3ff 0xcee50c0c0623f87f

def z1051 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x8fc78383ce007c65 0xb1f8f07079c00f8c

def z1052 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x8ac78181ce003c04 0xb158f03039c00780

def z1053 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xefcfe383ff1fffff 0xbdf9fc707fe3ffff

def z1054 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffcf8383ce1e7c67 0xbff9f07079c3cf8c

def z1055 : W := mkw 0x00892bfbb0000001 0xe011257f76000000 0xfedf9ffff0000000 0x7fdbf3fffe000000

def z1056 : W := mkw 0x5809a2a3620cd4f1 0xcb0134546c419a9e 0xf7ebe3e3f71fffff 0xfefd7c7c7ee3ffff

def z1057 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe5f9c1ff8f2327e 0xffcbf383ff1e464f

def z1058 : W := mkw 0x80fb7bfbb5810003 0xf01f6f7f76b02000 0xfefffffff1018000 0x7fdffffffe203000

def z1059 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafefe3e3cf1fffff 0xb5fdfc7c79e3ffff

def z1060 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0x09c78181ce0c7c01 0x2138f03039c18f80

def z1061 : W := mkw 0x008359d990000000 0xa0106b3b32000000 0x00879d9dc0000000 0x2010f3b3b8000000

def z1062 : W := mkw 0xa000015405a02b00 0x1400002a80b40560 0x9b9003fc0fe07f87 0xf372007f81fc0ff0

def z1063 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x91b003fc0fe07f87 0xf236007f81fc0ff0

def z1064 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xd8141c1ff8e2327e 0x7b028383ff1c464f

def z1065 : W := mkw 0x40098283020c4441 0x8801305060418888 0xafcf8383ce0c7c05 0xb5f9f07079c18f80

def z1066 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfb141e7ff8f273fe 0xff6283cfff1e4e7f

def z1067 : W := mkw 0x400484000a5a0000 0x08009080014b4000 0x7e7ffc000fff8003 0x8fcfff8001fff000

def z1068 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383ce1e7e7f 0xb5f9f07079c3cfcf

def z1069 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x2ecf8181ce003c00 0x25d9f03039c00780

def z1070 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x1ef79d9dc0000000 0x23def3b3b8000000

def z1071 : W := mkw 0xa0f27d7cb5e32b02 0x741e4faf96bc6560 0x50307c7c31e38382 0x4a060f8f863c7070

def z1072 : W := mkw 0xe076d5500fdb0902 0x1c0edaaa01fb6120 0x7e7ffc600fff8183 0x8fcfff8c01fff030

def z1073 : W := mkw 0x14000c0cd0623228 0x228001819a0c4645 0xda101c1ff8e2327e 0xfb420383ff1c464f

def z1074 : W := mkw 0xf40484044ffe7f68 0x1e80908089ffcfed 0x010000000ffe7fff 0x8020000001ffcfff

def z1075 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff11dc1e5 0xfffffffffe23b83c

def z1076 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xaeffffffc0000000 0x35dffffff8000000

def z1077 : W := mkw 0x50098283420c5461 0x8a01305068418a8c 0x05cb8381c60c7c01 0x20b9707038c18f80

def z1078 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x75286262311fc3fb 0x4ea50c4c4623f87f

def z1079 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xe4effffff0000000 0x7c9dfffffe000000

def z1080 : W := mkw 0xc072d40007cb0002 0x180e5a8000f96000 0x7e7ffc0007ef8003 0x0fcfff8000fdf000

def z1081 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff0004180 0x7ffffffffe000830

def z1082 : W := mkw 0xa8fb7bfbb584c9d3 0xf51f6f7f76b0993a 0xfffffffff70dcd81 0x7ffffffffee1b9b0

def z1083 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x68141c1ff8f2327e 0xad028383ff1e464f

def z1084 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x0dcf8381ce1c7c65 0xa1b9f07039c38f8c

def z1085 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x7a141c1ff8f2307a 0xaf428383ff1e460f

def z1086 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe541c1ffef2327f 0xffca8383ffde464f

def z1087 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x5c7ffc000fef8003 0x0b8fff8001fdf000

def z1088 : W := mkw 0x08092aabb004c0d1 0xe10125557600981a 0xfffffffff11fc3ff 0xfffffffffe23f87f

def z1089 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfe341e7ff8f2327e 0xffc683cfff1e464f

def z1090 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xffefe3e3ff1c7fe7 0xfffdfc7c7fe38ffc

def z1091 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x8fcf8381ce0c7c05 0xb1f9f07039c18f80

def z1092 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x08d79d9dce003c00 0x211af3b3b9c00780

def z1093 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x747ffc0007ff8003 0x0e8fff8000fff000

def z1094 : W := mkw 0x080922a32004c0d1 0xc10124546400981a 0xf7ebe3e2311fc3ff 0xdefd7c7c4623f87f

def z1095 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff01fc07d 0xfffffffffe03f80f

def z1096 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xe5286262311fc3fd 0x5ca50c4c4623f87f

def z1097 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x7e5ffc000eff8003 0x8fcbff8001dff000

def z1098 : W := mkw 0x500584814a5a1420 0x8a00b090294b4284 0x7ad79d81cef23c02 0xaf5af3b039de4780

def z1099 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf7a863e2311fffff 0xfef50c7c4623ffff

def z1100 : W := mkw 0x0072595890000002 0x200e4b2b12000000 0xfefffffff0000000 0x7fdffffffe000000

def z1101 : W := mkw 0x088b7aabb004c0d1 0xe1116f557600981a 0xfa1ffc1ff01f827e 0xff43ff83fe03f04f

def z1102 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x8cfffffff0000000 0x719ffffffe000000

def z1103 : W := mkw 0xc072d40007cb0002 0x180e5a8000f96000 0x5e7bfc000fef8003 0x8bcf7f8001fdf000

def z1104 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x15f003fc0fe07f87 0xc2be007f81fc0ff0

def z1105 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xbfff83fc0fe07f87 0xf7fff07f81fc0ff0

def z1106 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x09c78181ce007c05 0xa138f03039c00f80

def z1107 : W := mkw 0xc072d40007cb0002 0x180e5a8000f96000 0x767bfc0007ff8003 0x8ecf7f8000fff000

def z1108 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xbfefe3e3cf1dffe7 0xf7fdfc7c79e3bffc

def z1109 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf7e863e2371fcfff 0xdefd0c7c46e3f9ff

def z1110 : W := mkw 0x540484044a7b3228 0x0a809080894f6645 0x0000000008ffb27e 0x80000000011ff64f

def z1111 : W := mkw 0x5c0daeabfa5ed4f9 0xeb81b5d57f4bda9f 0x600ffc03f01f8078 0x0c01ff807e03f00f

def z1112 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0xfeffff9fc0000000 0x3fdffff3f8000000

def z1113 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffffe1c7c65 0xffffffffffc38f8c

def z1114 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc023fff8003 0xdfcfff8047fff000

def z1115 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffff11fc067 0xfffffffffe23f80c

def z1116 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x71286062311fc3ff 0xce250c0c4623f87f

def z1117 : W := mkw 0x5001808142081420 0x8a00301028410284 0x00c38181c6003c00 0x2018703038c00780

def z1118 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x547bfc000fff8003 0x8a8f7f8001fff000

def z1119 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x65286262311fc3ff 0x8ca50c4c4623f87f

def z1120 : W := mkw 0x00090a8b90044041 0xa001215172008808 0xffdf9f9ff01e427f 0xfffbf3f3fe03c84f

def z1121 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x8fd79f9dce007c05 0xb1faf3f3b9c00f80

def z1122 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfed41f9ff8f2327e 0xffda83f3ff1e464f

def z1123 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x78fffdfff0000000 0x6f1fffbffe000000

def z1124 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x9ad79d9dc0000000 0x735af3b3b8000000

def z1125 : W := mkw 0x00090a8b90000001 0xa001215172000000 0xfa1f9c1ff0000000 0x7f43f383fe000000

def z1126 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff1000382 0x7fdffffffe200070

def z1127 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xfefffffff1e00002 0x7fdffffffe3c0000

def z1128 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x89d003fc0fe07f87 0xf13a007f81fc0ff0

def z1129 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff863fe3fffffff 0xffff0c7fc7ffffff

def z1130 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffefe3e3cf1ffde7 0xbffdfc7c79e3ffbc

def z1131 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff003fc0ff27fff 0xf3fe007f81fe4fff

def z1132 : W := mkw 0xa0fb7bfbb5800903 0xf41f6f7f76b00120 0xffffffffffe04d83 0xfffffffffffc09b0

def z1133 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfffffffff103c39f 0xfffffffffe207873

def z1134 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xfefffffff7000001 0x7fdffffffee00000

def z1135 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x68d79d9ff0000000 0x2d1af3b3fe000000

def z1136 : W := mkw 0xc072d00007890002 0x180e5a0000f12000 0x7e7ffc000fed8003 0x8fcfff8001fdb000

def z1137 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfff41ffffff27fff 0xfffe83fffffe4fff

def z1138 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff0120078 0x7fdffffffe02400f

def z1139 : W := mkw 0x00040c0898520000 0x20008181130a4000 0xfa141c1ff8f2027e 0xff428383ff1e404f

def z1140 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xff3c7e7ff9fff3ff 0xffe78fcfff3ffe7f

def z1141 : W := mkw 0x00fb7bfbb0044043 0xe01f6f7f76008808 0xfffffffff00c4001 0x7ffffffffe018800

def z1142 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafef83e3cf1c7de5 0xb5fdf07c79e38fbc

def z1143 : W := mkw 0x540484044a7e7668 0x0a809080894fcecd 0x0000000008fe327e 0x80000000011fc64f

def z1144 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x2edf9d9dc0000000 0x25dbf3b3b8000000

def z1145 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x685ffc000fff8003 0x8d0bff8001fff000

def z1146 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc003fff821b 0xcfcfff8007fff043

def z1147 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff0120002 0xffdffffffe024000

def z1148 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0xbeff9fffc0000000 0x77dff3fff8000000

def z1149 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x7a141c1ff8f2027a 0xcf428383ff1e404f

def z1150 : W := mkw 0xd476d4004fdb102a 0x1a8eda8009fb6205 0x7e7ffc000fff807b 0x8fcfff8001fff00f

def z1151 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff11f827f 0xffdffffffe23f04f

def z1152 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff10043ff 0xfffffffffe20087f

def z1153 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x6c7ffc000fff8001 0x0d8fff8001fff000

def z1154 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0x8fc78381ce1c7c65 0xb1f8f07039c38f8c

def z1155 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xafcf8383cf1dfde5 0xb5f9f07079e3bfbc

def z1156 : W := mkw 0xd40484044ffb3228 0x1a80908089ff6645 0x000000000ee03000 0x0000000001dc0600

def z1157 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x09c78381ce007c00 0x2138f07039c00f80

def z1158 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff2c6263f11fc3ff 0xffe58c4c7e23f87f

def z1159 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xfefffffffee00000 0x7fdfffffffdc0000

def z1160 : W := mkw 0x0009028300044041 0x8001205060008808 0xafcf8383ce1c7c65 0xb5f9f07079c38f8c

def z1161 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa141c1ff8e0327c 0x7f428383ff1c064f

def z1162 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xefcfe383ce1ffc65 0xbdf9fc7079c3ff8c

def z1163 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0x08dffd9dc0000000 0x211bffb3b8000000

def z1164 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff1000003 0xffdffffffe200000

def z1165 : W := mkw 0x0083588990000000 0xa0106b1132000000 0xfa179c1ff0000000 0x7f42f383fe000000

def z1166 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xffe863e2311fc3ff 0xfffd0c7c4623f87f

def z1167 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xff141e1ff8f2727f 0xffe283c3ff1e4e4f

def z1168 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xdff063fc0fe3ff87 0xfbfe0c7f81fc7ff0

def z1169 : W := mkw 0x14040c08d8521028 0x228081811b0a4205 0xfa141c1ff8f2007a 0xff428383ff1e400f

def z1170 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0x08f7fdfdc0000000 0x211effbfb8000000

def z1171 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xe8141c1ff8f2327c 0x7d028383ff1e464f

def z1172 : W := mkw 0x00fb5bdb90000003 0xa01f6b7b72000000 0x88d79f9fc0000000 0x311af3f3f8000000

def z1173 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x0ec78181ce003c01 0xa1d8f03039c00780

def z1174 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x2fcf8381ce1c7c01 0xa5f9f07039c38f80

def z1175 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0xfa141c1ff8f23078 0x7f428383ff1e460f

def z1176 : W := mkw 0x0000080c90202200 0x2000010192040440 0xfa141c1ff8f2327e 0xff428383ff1e464f

def z1177 : W := mkw 0x540484044a7a3228 0x0a809080894f4645 0x000000000efe327f 0x8000000001dfc64f

def z1178 : W := mkw 0xc006d4000fdb0000 0x1800da8001fb6000 0x6e4ffc000fff8003 0x8dc9ff8001fff000

def z1179 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0x88c78383ce003c00 0x3118f07079c00780

def z1180 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffef83e3ff1e7fff 0xfffdf07c7fe3cfff

def z1181 : W := mkw 0xd40484044ffb3228 0x1a80908089ff6645 0x000000000ef2327e 0x8000000001de464f

def z1182 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff863fc0fe07f87 0xffff0c7f81fc0ff0

def z1183 : W := mkw 0xc072d40007cb0002 0x180e5a8000f96000 0x047bfc0007ed8001 0x008f7f8000fdb000

def z1184 : W := mkw 0x500d86834a5e5461 0x8a01b0d0694bca8c 0xafdf9f83cefc7c65 0xb5fbf3f079df8f8c

def z1185 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0xfa9ffffff0000000 0x7f53fffffe000000

def z1186 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xefcfe383fe1c7c65 0xbdf9fc707fc38f8c

def z1187 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xf63ffe7ff0000000 0x5ec7ffcffe000000

def z1188 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xffefe3e3ff1ffc67 0xfffdfc7c7fe3ff8c

def z1189 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x58f7fd9dc0000000 0x2b1effb3b8000000

def z1190 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xffcf8383ff1fffff 0xfff9f0707fe3ffff

def z1191 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x09d003fc0ee07d80 0x213a007f81dc0fb0

def z1192 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xafefe3e3ce1c7c65 0xb5fdfc7c79c38f8c

def z1193 : W := mkw 0x80f359d995800002 0xb01e6b3b32b00000 0x08d79d9dcee00000 0x211af3b3b9dc0000

def z1194 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xafcf8383ce1c7ffd 0xb5f9f07079c38fff

def z1195 : W := mkw 0xa4f27d7cb5e22b0a 0x749e4faf96bc4561 0x50307c7c31e2039a 0x4a060f8f863c4073

def z1196 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7f7ffc000fffc387 0x8fefff8001fff870

def z1197 : W := mkw 0x580d82834a1cd4f1 0x8b01b05069439a9e 0xbfef83e3cf1fffff 0xf7fdf07c79e3ffff

def z1198 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfe7ffc000fff8207 0xdfcfff8001fff040

def z1199 : W := mkw 0xd40484044ffb3228 0x1a80908089ff6645 0xf62860023fffb27f 0xdec50c0047fff64f

def z1200 : W := mkw 0x500d82834a181421 0x8a01b05069430284 0xaecf8383ce1c3c01 0xb5d9f07079c38780

def z1201 : W := mkw 0xd40484044ffb3228 0x1a80908089ff6645 0x000000000fffb003 0x8000000001fff600

def z1202 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0x5037fc7df0000000 0x4a06ff8fbe000000

def z1203 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x2ac78181ce103c00 0xa558f03039c20780

def z1204 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x88c78183ce003c64 0x3118f03079c0078c

def z1205 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xa9cf8383ce1c7c64 0x3539f07079c38f8c

def z1206 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf1286262311fc3fe 0x5e250c4c4623f87f

def z1207 : W := mkw 0xa0fb7bfbb5800903 0xf41f6f7f76b00120 0xfffffffff7004f87 0xfffffffffee009f0

def z1208 : W := mkw 0xc072d40007cb0002 0x180e5a8000f96000 0x503bfc0001ef8002 0x0a077f80003df000

def z1209 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xafcfe383ce1dfc65 0xb5f9fc7079c3bf8c

def z1210 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfefffffff8003004 0xffdfffffff000600

def z1211 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0x701ffc1ff0000000 0x4e03ff83fe000000

def z1212 : W := mkw 0x007a7a2ab0000003 0x600f4f4556000000 0xfe7ffe7ff0000000 0x7fcfffcffe000000

def z1213 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xffffffffffe07c07 0xfffffffffffc0f80

def z1214 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff0004005 0xfffffffffe000800

def z1215 : W := mkw 0x1009028340045461 0x8201205068008a8c 0xafcf8383ce007c65 0xb5f9f07079c00f8c

def z1216 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x1e7ffc000fed8003 0x83cfff8001fdb000

def z1217 : W := mkw 0x88fb7bfbb584c0d3 0xf11f6f7f76b0981a 0xffffffffffffc3ff 0xfffffffffffff87f

def z1218 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0x89c783e3fe007ffc 0x7138f07c7fc00fff

def z1219 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xfeffffffffff8003 0xffdffffffffff000

def z1220 : W := mkw 0x080822222004c0d1 0x410104444400981a 0x76286062311f83fb 0xcec50c0c4623f07f

def z1221 : W := mkw 0x080020202004c0d0 0x410004040400981a 0xd7206260311fc3ff 0xdae40c4c0623f87f

def z1222 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xf72862623f1fffff 0xdee50c4c47e3ffff

def z1223 : W := mkw 0x00092aabb0000001 0xe001255576000000 0xfefffffff0000000 0x7fdffffffe000000

def z1224 : W := mkw 0xa072515405a12b02 0x140e4a2a80b42560 0x9ff063fc0fe1ff87 0xf3fe0c7f81fc3ff0

def z1225 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x18f79dfdc0000000 0x631ef3bfb8000000

def z1226 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0x0dfffffdc10dc181 0x21bfffffb821b830

def z1227 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfefffffff11f839b 0xffdffffffe23f073

def z1228 : W := mkw 0xa0fb7bfbb5800903 0xf41f6f7f76b00120 0xfefffffff6000c00 0x7fdffffffec00180

def z1229 : W := mkw 0xd40484044fff7668 0x1a80908089ffeecd 0x010000000ffffe7f 0x8020000001ffffcf

def z1230 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x600ffc0008ff8002 0x8c01ff80011ff000

def z1231 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfad79ffff0000000 0x7f5af3fffe000000

def z1232 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xff7ffe000fffc007 0x9fefffc001fff800

def z1233 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0xfad79d9ff012027e 0xff5af3b3fe02404f

def z1234 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x646ffc000fff8003 0x8c8dff8001fff000

def z1235 : W := mkw 0x000922a320000001 0xc001245464000000 0xffefe3e3ff007f87 0xfffdfc7c7fe00ff0

def z1236 : W := mkw 0x500d86834a5e5461 0x8a01b0d0694bca8c 0xffdf9f83fefe7e7f 0xfffbf3f07fdfcfcf

def z1237 : W := mkw 0x54048c0cda7a3228 0x2a8091819b4f4645 0xffdf9f9ffefe7e7f 0xfffbf3f3ffdfcfcf

def z1238 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff003fe3fe07fff 0xf3fe007fc7fc0fff

def z1239 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0xfefffd9ff0000000 0x7fdfffb3fe000000

def z1240 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff10dc387 0xfffffffffe21b870

def z1241 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xbfef83e3ff1c7fff 0xf7fdf07c7fe38fff

def z1242 : W := mkw 0x4006d4000a5b0000 0x0800da80014b6000 0x701ffc0000ff8002 0x0e03ff80001ff000

def z1243 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xa5cf8383c61c7c65 0x34b9f07078c38f8c

def z1244 : W := mkw 0x500da2a36a1c5461 0xca01b4546d438a8c 0xffefe3e3fe1e7e7f 0xfffdfc7c7fc3cfcf

def z1245 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x8dcf8383ce0c7c65 0x31b9f07079c18f8c

def z1246 : W := mkw 0x5809a2a3620cd4f1 0xcb0134546c419a9e 0x85ebe3e3f70dfffd 0x70bd7c7c7ee1bfff

def z1247 : W := mkw 0x00f379f9b0000002 0xe01e6f3f36000000 0xdef7fffdf0000000 0x7bdeffffbe000000

def z1248 : W := mkw 0xa0f359d995800902 0xb41e6b3b32b00120 0x08d79d9dc6000c00 0x211af3b3b8c00180

def z1249 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0x09c78181ce007c64 0x2138f03039c00f8c

def z1250 : W := mkw 0xa0fb7bfbb5800903 0xf41f6f7f76b00120 0xfefffffff1000180 0x7fdffffffe200030

def z1251 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff0004384 0x7ffffffffe000870

def z1252 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0xfedfff9ff0000000 0x7fdbfff3fe000000

def z1253 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xff6fe262311fc3ff 0xdfedfc4c4623f87f

def z1254 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x08141c1ff8e03078 0x21028383ff1c060f

def z1255 : W := mkw 0xf40484044ffb3b28 0x1e80908089ff6765 0x010000000fffffff 0x8020000001ffffff

def z1256 : W := mkw 0x34040c0cd8723b28 0x268081819b0e4765 0xfb141c1ff8f27ffe 0xff628383ff1e4fff

def z1257 : W := mkw 0x580da2a36a1cd4f1 0xcb01b4546d439a9e 0xffcfe383fe1ffe7f 0xfff9fc707fc3ffcf

def z1258 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0xfeffff800fff8003 0xbfdffff001fff000

def z1259 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0x25cf8383ce1c7c65 0x84b9f07079c38f8c

def z1260 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x68dffd9dc0000000 0x2d1bffb3b8000000

def z1261 : W := mkw 0x00fb7bfbb0000003 0xe01f6f7f76000000 0xfffffffff11243ff 0xfffffffffe22487f

def z1262 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xffdf9f83ce1c7c65 0xbffbf3f079c38f8c

def z1263 : W := mkw 0x500580814a1c5460 0x8a00b01029438a8c 0x2fcf8181ce1c7c65 0xa5f9f03039c38f8c

def z1264 : W := mkw 0x540c86064a7e7669 0x0a8190c0c94fcecd 0xf70802023efe7e7f 0xdee1004047dfcfcf

def z1265 : W := mkw 0x50098283420c5461 0x8a01305068418a8c 0xafcf8383c60c7c65 0x35f9f07078c18f8c

def z1266 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xafcf8383fe1c7e7d 0xf5f9f0707fc38fcf

def z1267 : W := mkw 0x008b7aabb0000001 0xe0116f5576000000 0x681ffc1ff0000000 0x2d03ff83fe000000

def z1268 : W := mkw 0x500580814a181420 0x8a00b01029430284 0x7eefe181cf1fbc03 0xafddfc3039e3f780

def z1269 : W := mkw 0x08fb7bfbb0008093 0xe11f6f7f76001012 0xfefffffff11383fe 0xffdffffffe22707f

def z1270 : W := mkw 0x20fb7bfbb0000903 0xe41f6f7f76000120 0xfffffffff0004d80 0x7ffffffffe0009b0

def z1271 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x9a141c1ff8e0327e 0xf3428383ff1c064f

def z1272 : W := mkw 0x088b7aabb004c0d1 0xe1116f557600981a 0xff3ffe7ff11fc3ff 0xffe7ffcffe23f87f

def z1273 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0xaad79d9fc0000000 0x355af3b3f8000000

def z1274 : W := mkw 0xa0fa7b7eb5a02b03 0x741f4f6fd6b40560 0xf7387e7e31e04387 0xdee70fcfc63c0870

def z1275 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0xfff003fc0ff27f87 0xfffe007f81fe4ff0

def z1276 : W := mkw 0xe076d5500fdb0902 0x1c0edaaa01fb6120 0xffffffe00fffcf87 0xdffffffc01fff9f0

def z1277 : W := mkw 0x080822222004c0d1 0x410104444400981a 0xd1206262311fc3ff 0xda240c4c4623f87f

def z1278 : W := mkw 0x08fb7bfbb004c0d3 0xe11f6f7f7600981a 0xfffffffff11fc1f9 0x7ffffffffe23f83f

def z1279 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7e7ffc023fff807b 0x8fcfff8047fff00f

def z1280 : W := mkw 0x500d82834a1c5461 0x8a01b05069438a8c 0xefcf8383fe1e7c7d 0xbdf9f0707fc3cf8f

def z1281 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9bd003fc0ee07f86 0xf37a007f81dc0ff0

def z1282 : W := mkw 0xc076d4000fdb0002 0x180eda8001fb6000 0x7fffff800fffcc03 0x8ffffff001fff980

def z1283 : W := mkw 0x80fb7bfbb5800003 0xf01f6f7f76b00000 0xffffffffffe04387 0xfffffffffffc0870

def z1284 : W := mkw 0xc006d4000fdb0000 0x1800da8001fb6000 0x600ffc0001ff8002 0x0c01ff80003ff000

def z1285 : W := mkw 0x008b7bfbb0000001 0xe0116f7f76000000 0xf6affffff0000000 0x7ed5fffffe000000

def z1286 : W := mkw 0x500584814a5a1420 0x8a00b090294b4284 0x08d79d81cee03c00 0x211af3b039dc0780

def z1287 : W := mkw 0x14040c0cd8723228 0x228081819b0e4645 0x88141c1ff8f2327e 0xf1028383ff1e464f

def z1288 : W := mkw 0xa070015405a02b02 0x140e002a80b40560 0x9ff003fc0fe07d81 0x73fe007f81fc0fb0

def z1289 : W := mkw 0x500580814a181420 0x8a00b01029430284 0xaecf8183ce1c3c65 0xb5d9f03079c3878c

def z1290 : W := mkw 0x00f359d990000002 0xa01e6b3b32000000 0x88d79d9ff0000000 0x711af3b3fe000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z8]),(0,[z7,z1,z3,z9,z4,z5,z6]),(0,[z7,z1,z10,z3,z4,z5,z11]),(0,[z12,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z13,z4,z5,z6])],[(0,[z14,z7,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z15,z6]),(0,[z16,z7,z1,z3,z4,z5,z6])],[(0,[z17,z18,z7,z1,z3,z5,z6]),(0,[z19,z7,z1,z3,z20,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z21]),(0,[z7,z22,z1,z23,z4,z5,z6]),(0,[z7,z1,z3,z4,z24,z25,z6])],[(0,[z7,z1,z3,z4,z5,z6,z26]),(0,[z7,z1,z3,z4,z24,z5,z6]),(0,[z27,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z10,z4,z28,z5,z6]),(0,[z7,z1,z3,z29,z4,z5,z6]),(0,[z30,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z31,z3,z4,z5,z6])],[(0,[z7,z1,z3,z32,z4,z5,z6]),(0,[z33,z14,z1,z3,z4,z5,z6]),(0,[z34,z7,z1,z3,z35,z5,z6]),(0,[z7,z36,z1,z3,z4,z5,z6]),(0,[z37,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z38,z5,z6]),(0,[z7,z1,z39,z3,z35,z5,z6]),(0,[z7,z1,z3,z40,z35,z5,z6]),(0,[z7,z1,z3,z35,z41,z5,z6]),(0,[z7,z1,z3,z42,z4,z5,z6])],[(0,[z7,z1,z3,z4,z43,z5,z6]),(0,[z7,z22,z1,z44,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z45]),(0,[z7,z46,z1,z3,z47,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z48,z4,z5,z6]),(0,[z7,z1,z3,z49,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z6,z50]),(0,[z7,z1,z3,z4,z51,z5,z6]),(0,[z7,z52,z1,z3,z4,z5,z6])],[(0,[z53,z7,z1,z3,z47,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z56,z7,z1,z3,z4,z5,z6]),(1,[z1,z57,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z41,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z58]),(0,[z7,z59,z1,z10,z4,z5,z6]),(0,[z7,z1,z3,z9,z5,z6,z60])]],
   [[(0,[z7,z1,z3,z35,z35,z5,z6])],[(0,[z7,z61,z46,z3,z4,z5,z6]),(0,[z7,z1,z62,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z63,z5,z6]),(0,[z7,z1,z3,z4,z5,z64,z6]),(0,[z65,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z66,z4,z5,z6])],[(0,[z67,z7,z1,z3,z5,z68,z6])],[(0,[z7,z1,z3,z4,z5,z69,z6]),(1,[z7,z70,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z71]),(0,[z7,z1,z3,z4,z5,z6,z72]),(0,[z7,z1,z3,z4,z5,z6,z73]),(0,[z7,z1,z3,z4,z5,z74,z6]),(0,[z7,z1,z75,z3,z76,z5,z6])],[(0,[z14,z1,z3,z76,z4,z5,z6]),(0,[z54,z7,z1,z3,z4,z5,z6]),(0,[z55,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z77,z6]),(0,[z7,z78,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z74])],[(1,[z7,z2,z3,z47,z5,z6]),(0,[z7,z79,z1,z3,z4,z5,z6]),(0,[z80,z7,z1,z3,z4,z5,z6]),(1,[z7,z22,z23,z4,z5,z6]),(1,[z7,z1,z3,z81,z5,z6]),(0,[z7,z59,z1,z4,z5,z6,z82])],[(0,[z1,z2,z83,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z84,z6]),(0,[z7,z1,z3,z35,z5,z85,z6]),(0,[z7,z59,z1,z3,z35,z5,z6]),(0,[z7,z86,z1,z3,z87,z5,z6]),(0,[z88,z7,z1,z3,z4,z5,z6])],[(0,[z89,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z90,z6]),(0,[z7,z1,z3,z4,z5,z6,z91])]],
   [[(0,[z7,z1,z3,z92,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z6]),(0,[z7,z61,z1,z3,z93,z5,z6]),(0,[z94,z7,z1,z3,z35,z5,z6]),(0,[z18,z1,z83,z3,z4,z5,z6]),(0,[z18,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z95,z5,z6])],[(0,[z7,z1,z96,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z97]),(0,[z7,z1,z3,z13,z4,z5,z50]),(0,[z7,z1,z3,z47,z5,z85,z6]),(0,[z7,z1,z75,z3,z9,z5,z6])],[(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z99,z4,z5,z6]),(0,[z7,z1,z100,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z101,z25,z6])],[(0,[z1,z102,z2,z3,z4,z5,z6]),(0,[z103,z7,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z47,z5,z101,z6]),(0,[z104,z1,z3,z4,z105,z5,z6])],[(0,[z33,z7,z1,z3,z4,z5,z6]),(0,[z7,z106,z1,z3,z4,z5,z6]),(0,[z34,z7,z1,z3,z47,z5,z6]),(1,[z19,z1,z3,z107,z5,z6]),(0,[z7,z1,z39,z3,z47,z5,z6]),(0,[z7,z1,z3,z35,z5,z25,z6]),(0,[z0,z7,z1,z3,z4,z101,z6]),(0,[z7,z1,z3,z4,z108,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z109]),(0,[z7,z23,z3,z44,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z110]),(0,[z111,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z112,z4,z5,z6])],[(0,[z113,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z114,z6]),(0,[z18,z7,z1,z3,z115,z5,z6]),(0,[z7,z1,z23,z4,z5,z25,z6]),(0,[z7,z116,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z117,z5,z6]),(1,[z7,z1,z3,z118,z5,z6]),(1,[z7,z1,z3,z119,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z120])],[(0,[z7,z7,z1,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z6,z121]),(0,[z19,z7,z1,z3,z115,z5,z6]),(0,[z7,z1,z122,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z123]),(0,[z7,z1,z3,z47,z5,z25,z6]),(0,[z7,z1,z3,z124,z4,z5,z6]),(0,[z7,z1,z3,z125,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z6,z126]),(0,[z127,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z128,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z129,z6]),(0,[z130,z7,z1,z3,z4,z5,z6]),(0,[z7,z3,z35,z4,z47,z5,z6]),(0,[z7,z1,z3,z131,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z132,z6]),(0,[z7,z1,z23,z3,z47,z5,z6]),(0,[z7,z1,z3,z47,z133,z5,z6]),(0,[z7,z1,z3,z134,z4,z5,z6]),(0,[z7,z1,z3,z135,z4,z5,z6])],[(0,[z14,z1,z3,z35,z4,z5,z6]),(0,[z7,z1,z3,z136,z4,z5,z6]),(0,[z7,z1,z3,z35,z20,z5,z6]),(0,[z137,z1,z3,z4,z5,z138,z6]),(1,[z139,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z140,z47,z5,z6]),(0,[z7,z141,z1,z3,z4,z5,z6]),(1,[z7,z1,z142,z4,z5,z143])],[(0,[z144,z1,z2,z3,z4,z5,z6]),(0,[z7,z46,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z145,z5,z6]),(0,[z14,z34,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z146,z4,z5,z6]),(0,[z7,z1,z147,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z148,z5,z6]),(0,[z7,z1,z149,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z82]),(0,[z7,z1,z3,z4,z150,z5,z6])],[(0,[z1,z151,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z152,z5,z6]),(0,[z14,z7,z1,z3,z35,z5,z6]),(0,[z55,z7,z1,z3,z4,z5,z50]),(0,[z17,z7,z153,z3,z4,z5,z6])],[(0,[z53,z7,z2,z3,z4,z5,z6]),(0,[z7,z61,z1,z3,z35,z5,z6]),(0,[z154,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z155]),(0,[z156,z7,z1,z3,z4,z5,z6])],[(0,[z14,z1,z142,z3,z4,z5,z6]),(0,[z46,z1,z157,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z158,z6]),(0,[z7,z1,z159,z3,z4,z5,z6])]],
   [[(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z105,z5,z6]),(0,[z94,z7,z1,z3,z47,z5,z6]),(0,[z160,z7,z1,z3,z4,z5,z6])],[(0,[z144,z7,z1,z3,z4,z5,z6]),(1,[z14,z61,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z161,z6]),(0,[z55,z137,z1,z3,z4,z5,z6]),(0,[z7,z162,z3,z4,z5,z85,z6]),(0,[z7,z1,z3,z4,z5,z6,z163])],[(0,[z7,z1,z3,z5,z164,z68,z6]),(0,[z7,z1,z165,z3,z4,z5,z6]),(0,[z166,z7,z1,z3,z4,z167,z6]),(0,[z7,z1,z168,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z169,z5,z6]),(0,[z7,z1,z3,z4,z170,z5,z6]),(0,[z7,z1,z3,z4,z171,z5,z6])],[(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z7,z1,z3,z13,z4,z5,z138]),(1,[z7,z1,z3,z4,z5,z21]),(0,[z7,z1,z3,z4,z5,z6,z172]),(0,[z173,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z174,z5,z6]),(0,[z7,z175,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z176,z4,z5,z6]),(0,[z7,z1,z3,z13,z47,z5,z6]),(0,[z177,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z178,z5,z6]),(1,[z7,z1,z31,z4,z5,z6])],[(0,[z179,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z180,z6]),(0,[z7,z1,z3,z4,z5,z6,z181]),(0,[z7,z1,z3,z4,z182,z5,z6]),(0,[z7,z1,z183,z3,z4,z5,z6]),(0,[z184,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z4,z152,z5,z25,z6]),(0,[z7,z1,z3,z4,z5,z6,z185])],[(0,[z186,z1,z3,z4,z152,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z6,z187]),(0,[z7,z1,z142,z23,z4,z5,z6]),(0,[z188,z7,z1,z3,z4,z5,z6]),(0,[z189,z7,z1,z3,z4,z5,z6])],[(0,[z1,z2,z39,z3,z4,z5,z6]),(0,[z18,z1,z3,z4,z20,z5,z6]),(0,[z54,z7,z1,z3,z4,z5,z190]),(0,[z191,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z167,z5,z6]),(1,[z7,z1,z3,z128,z5,z6]),(0,[z7,z1,z3,z4,z5,z192,z6]),(0,[z7,z1,z193,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z194,z5,z6]),(0,[z1,z3,z4,z5,z6,z172,z82]),(0,[z7,z1,z3,z4,z5,z195,z6])],[(0,[z196,z7,z1,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z197,z35,z5,z6]),(0,[z198,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z142,z4,z28,z5,z6]),(0,[z7,z199,z1,z3,z4,z5,z6]),(0,[z200,z7,z1,z4,z5,z6,z82])],[(0,[z201,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z202,z6]),(0,[z203,z7,z1,z3,z4,z68,z6]),(0,[z7,z1,z3,z204,z4,z5,z6]),(0,[z7,z1,z142,z44,z4,z5,z6]),(0,[z200,z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z205,z6])],[(0,[z206,z7,z1,z3,z4,z5,z6]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z83,z3,z35,z5,z6]),(0,[z7,z1,z3,z207,z4,z5,z6]),(0,[z208,z7,z1,z3,z4,z5,z6]),(0,[z7,z162,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z209,z5,z6])],[(0,[z210,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z211,z5,z6]),(1,[z7,z1,z3,z4,z5,z73])],[(0,[z7,z1,z3,z4,z5,z143,z110]),(0,[z7,z1,z3,z4,z5,z6,z212])],[(0,[z1,z2,z23,z3,z4,z5,z6]),(0,[z213,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z214]),(0,[z7,z1,z3,z4,z5,z6,z215]),(0,[z216,z7,z1,z3,z4,z5,z6]),(0,[z7,z217,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z218,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z219]),(0,[z166,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z220,z4,z5,z6]),(0,[z7,z1,z3,z98,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z143,z85])],[(1,[z53,z2,z3,z4,z5,z6]),(0,[z221,z14,z1,z3,z4,z5,z6]),(0,[z54,z7,z1,z3,z47,z5,z6]),(0,[z55,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z35,z24,z5,z6]),(0,[z7,z1,z3,z4,z222,z5,z6])],[(1,[z223,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z224]),(0,[z7,z1,z225,z3,z4,z5,z6]),(0,[z7,z1,z76,z4,z178,z5,z6]),(0,[z7,z1,z3,z40,z13,z4,z5])],[(0,[z1,z2,z3,z4,z5,z226,z6]),(0,[z1,z83,z3,z107,z4,z5,z6]),(0,[z7,z1,z3,z4,z227,z5,z6]),(0,[z1,z3,z4,z5,z138,z6,z50]),(0,[z17,z7,z1,z3,z35,z5,z6]),(0,[z7,z86,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z228,z6]),(0,[z229,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z230,z3,z4,z5,z6])],[(0,[z7,z1,z3,z47,z24,z5,z6]),(0,[z7,z1,z231,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z232])],[(0,[z233,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z70,z3,z4,z5,z6]),(1,[z7,z1,z234,z4,z5,z6]),(0,[z7,z1,z235,z3,z4,z5,z6]),(0,[z7,z236,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z237]),(0,[z201,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z238,z4,z5,z6]),(0,[z203,z1,z3,z4,z239,z5,z6]),(0,[z7,z1,z75,z3,z4,z5,z60])],[(0,[z7,z1,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z240]),(0,[z14,z1,z3,z4,z5,z6,z60]),(0,[z7,z1,z3,z4,z5,z241,z6]),(0,[z7,z1,z3,z242,z4,z5,z6]),(0,[z17,z7,z225,z3,z4,z5,z6]),(0,[z243,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z244,z5,z6]),(0,[z7,z1,z3,z107,z4,z5,z6]),(0,[z0,z245,z1,z3,z4,z5,z6]),(0,[z246,z7,z1,z3,z4,z5,z6]),(0,[z154,z7,z3,z4,z5,z6,z110])],[(0,[z7,z1,z3,z35,z5,z6,z71]),(0,[z7,z1,z3,z4,z5,z101,z6]),(0,[z154,z7,z1,z48,z4,z5,z6]),(0,[z7,z247,z1,z3,z4,z5,z6]),(0,[z17,z7,z1,z3,z248,z5,z6]),(0,[z7,z1,z3,z249,z4,z5,z6])],[(0,[z53,z7,z1,z3,z35,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z1,z2,z3,z13,z4,z5,z6]),(1,[z203,z1,z3,z4,z239,z6]),(0,[z0,z7,z1,z3,z4,z24,z6]),(0,[z7,z1,z3,z4,z5,z6,z250]),(0,[z201,z7,z1,z3,z4,z25,z6]),(0,[z7,z1,z142,z3,z13,z4,z5]),(0,[z7,z1,z3,z248,z4,z5,z6])],[(0,[z94,z7,z1,z83,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z251]),(0,[z7,z1,z3,z4,z28,z5,z6]),(0,[z201,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z252]),(0,[z7,z153,z1,z3,z4,z5,z6]),(0,[z17,z7,z1,z3,z4,z5,z74]),(0,[z7,z253,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z254])],[(0,[z255,z7,z1,z3,z4,z5,z6]),(0,[z14,z22,z1,z3,z4,z5,z6]),(0,[z34,z7,z1,z99,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z256]),(0,[z7,z1,z83,z3,z47,z5,z6]),(0,[z7,z1,z3,z40,z4,z68,z6]),(0,[z7,z1,z3,z44,z4,z5,z6]),(1,[z257,z1,z3,z4,z5,z6]),(0,[z7,z1,z258,z3,z4,z5,z6]),(1,[z1,z3,z4,z259,z5,z6]),(0,[z7,z1,z3,z260,z4,z5,z6]),(0,[z1,z3,z4,z152,z5,z261,z6])],[(0,[z7,z1,z3,z262,z4,z5,z6]),(1,[z1,z263,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z264,z5,z6])],[(0,[z94,z203,z1,z3,z4,z5,z6]),(0,[z137,z1,z3,z4,z5,z68,z6]),(0,[z7,z162,z1,z3,z118,z5,z6]),(0,[z7,z1,z3,z119,z4,z5,z6])],[(0,[z265,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z266,z4,z5,z6])]],
   [[(0,[z267,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z268,z4,z5,z6]),(0,[z7,z1,z3,z269,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z11,z6]),(0,[z7,z1,z3,z4,z5,z6,z270])],[(0,[z14,z1,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z271,z4,z5,z6]),(0,[z7,z1,z3,z272,z4,z5,z6]),(1,[z7,z1,z3,z4,z273,z6]),(0,[z7,z1,z3,z274,z4,z5,z6])],[(0,[z18,z7,z275,z3,z4,z5,z6]),(0,[z7,z86,z1,z3,z4,z101,z6])],[(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z18,z14,z1,z3,z4,z5,z6]),(1,[z34,z1,z83,z4,z5,z6]),(0,[z17,z7,z1,z3,z47,z5,z6]),(0,[z7,z46,z3,z4,z5,z101,z6]),(0,[z7,z1,z3,z35,z5,z6,z110]),(0,[z7,z276,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z277,z6]),(0,[z17,z7,z1,z3,z4,z6,z278])],[(0,[z19,z14,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z87,z5,z6]),(0,[z7,z1,z3,z4,z279,z5,z6]),(0,[z7,z1,z3,z280,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z138,z6]),(0,[z7,z281,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z115,z5,z6]),(0,[z7,z1,z3,z4,z282,z5,z6])],[(0,[z283,z7,z1,z3,z4,z5,z6]),(0,[z284,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z285,z6]),(0,[z7,z1,z3,z4,z286,z5,z6]),(0,[z7,z1,z3,z47,z5,z6,z110]),(0,[z7,z1,z3,z4,z211,z5,z6]),(0,[z7,z1,z10,z3,z28,z5,z6]),(0,[z7,z1,z3,z4,z5,z287,z6]),(0,[z7,z1,z142,z3,z4,z5,z82])],[(0,[z7,z1,z288,z3,z4,z5,z6]),(0,[z7,z1,z3,z289,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z6]),(0,[z290,z7,z1,z3,z4,z5,z6]),(0,[z7,z86,z3,z4,z47,z5,z6]),(1,[z7,z46,z3,z35,z5,z6]),(1,[z291,z1,z3,z4,z5,z6]),(1,[z7,z1,z75,z3,z41,z5]),(0,[z7,z1,z292,z3,z4,z5,z6])]],
   [[(0,[z94,z7,z1,z99,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z293]),(0,[z1,z3,z4,z239,z5,z68,z6]),(0,[z7,z1,z3,z294,z4,z5,z6])],[(0,[z113,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z77,z5,z6])],[(0,[z7,z1,z3,z295,z4,z5,z6]),(0,[z14,z7,z61,z3,z4,z5,z6]),(0,[z7,z61,z1,z3,z51,z5,z6]),(0,[z7,z1,z296,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z297,z5,z6]),(0,[z7,z1,z3,z35,z5,z6,z82]),(0,[z7,z245,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z298,z4,z5,z6]),(0,[z17,z7,z1,z3,z4,z115,z6])],[(0,[z14,z46,z1,z3,z4,z5,z6]),(0,[z166,z7,z1,z3,z4,z273,z6]),(0,[z7,z1,z3,z299,z4,z5,z6]),(0,[z300,z7,z1,z3,z4,z5,z6])],[(0,[z301,z7,z1,z3,z4,z5,z6]),(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z302,z5,z6]),(0,[z7,z1,z3,z303,z4,z5,z6]),(0,[z7,z1,z3,z4,z304,z5,z6]),(0,[z7,z1,z23,z4,z5,z6,z82]),(0,[z154,z7,z1,z305,z4,z5,z6]),(0,[z154,z7,z1,z3,z4,z306,z6])],[(1,[z7,z1,z3,z169,z5,z6]),(0,[z55,z1,z3,z4,z5,z6,z50]),(0,[z7,z1,z23,z3,z35,z5,z6]),(0,[z7,z1,z3,z47,z5,z6,z82]),(0,[z307,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z171,z5,z6]),(0,[z7,z1,z3,z13,z4,z6,z232]),(0,[z7,z1,z3,z308,z4,z5,z6])],[(0,[z18,z1,z2,z3,z4,z5,z6]),(0,[z309,z7,z1,z3,z4,z5,z6]),(0,[z7,z310,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z110]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z311,z7,z1,z3,z4,z5,z6]),(0,[z54,z203,z1,z3,z4,z5,z6]),(0,[z7,z1,z312,z3,z4,z5,z6]),(0,[z7,z162,z1,z3,z313,z5,z6]),(0,[z7,z1,z142,z4,z5,z143,z6]),(0,[z7,z1,z3,z4,z5,z6,z278])]],
   [[(0,[z7,z314,z1,z3,z4,z5,z6]),(0,[z1,z83,z3,z99,z4,z5,z6]),(0,[z7,z1,z3,z4,z315,z5,z6]),(1,[z316,z1,z3,z4,z5,z6]),(0,[z317,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z24,z6,z232]),(1,[z318,z1,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z143,z6]),(0,[z154,z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z319,z5,z6])],[(0,[z7,z1,z320,z3,z4,z5,z6]),(0,[z94,z34,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z321,z6])],[(0,[z322,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z323,z5,z6]),(0,[z7,z1,z3,z4,z324,z5,z6]),(0,[z7,z1,z3,z325,z4,z5,z6])],[(0,[z19,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z326,z4,z5,z6]),(0,[z327,z7,z1,z3,z35,z5,z6])],[(0,[z14,z1,z3,z4,z5,z328,z6]),(0,[z14,z1,z3,z4,z47,z5,z6]),(0,[z17,z19,z7,z1,z3,z5,z6]),(0,[z22,z1,z57,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z329]),(1,[z7,z1,z3,z4,z279,z6]),(0,[z7,z1,z3,z330,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z82]),(0,[z331,z14,z1,z3,z4,z5,z6]),(0,[z284,z7,z1,z3,z4,z5,z6]),(1,[z7,z61,z3,z47,z5,z6]),(0,[z7,z1,z3,z332,z4,z5,z6]),(0,[z7,z1,z3,z28,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z333]),(1,[z7,z1,z235,z4,z5,z6]),(1,[z7,z1,z3,z209,z5,z6]),(0,[z7,z1,z3,z4,z334,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z335]),(0,[z54,z7,z1,z3,z4,z239,z6]),(0,[z7,z1,z3,z336,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z337]),(1,[z7,z1,z3,z338,z5,z6])]],
   [[(0,[z14,z1,z3,z339,z4,z5,z6]),(0,[z203,z1,z83,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z50]),(0,[z7,z1,z3,z13,z35,z5,z6]),(0,[z7,z1,z3,z9,z35,z5,z6]),(0,[z7,z1,z3,z340,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z341])],[(0,[z200,z7,z1,z3,z13,z4,z5]),(0,[z7,z1,z3,z342,z4,z5,z6])],[(0,[z14,z1,z39,z3,z4,z5,z6]),(0,[z14,z1,z3,z40,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z343]),(1,[z344,z7,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z345,z5,z6]),(0,[z7,z1,z3,z4,z5,z346,z6])],[(0,[z94,z1,z3,z4,z5,z68,z6]),(0,[z7,z1,z3,z347,z4,z5,z6]),(0,[z166,z7,z1,z3,z348,z5,z6]),(1,[z7,z1,z3,z4,z167,z6]),(0,[z7,z1,z3,z4,z5,z6,z349])],[(0,[z7,z1,z75,z3,z47,z5,z6]),(0,[z201,z7,z1,z4,z5,z25,z6])],[(0,[z1,z2,z3,z4,z5,z85,z6]),(0,[z7,z1,z3,z107,z47,z5,z6]),(0,[z7,z1,z3,z350,z4,z5,z6]),(0,[z0,z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z76,z4,z5,z60])],[(0,[z7,z2,z3,z4,z47,z5,z6]),(0,[z351,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z142,z3,z4,z5,z232]),(0,[z7,z1,z3,z76,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z352,z6]),(0,[z55,z7,z1,z3,z4,z353,z6]),(0,[z7,z1,z354,z3,z4,z5,z6]),(0,[z7,z162,z1,z3,z4,z5,z110]),(0,[z7,z1,z3,z4,z5,z6,z355]),(0,[z7,z1,z3,z4,z5,z6,z356]),(0,[z7,z1,z3,z4,z105,z5,z232])]],
   [[(0,[z14,z1,z3,z4,z239,z5,z6]),(0,[z7,z357,z1,z3,z4,z5,z6]),(0,[z166,z7,z22,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z358,z6]),(0,[z201,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z101,z6,z232]),(0,[z7,z1,z4,z28,z5,z25,z6])],[(0,[z359,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z360,z5,z6]),(0,[z203,z19,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z361,z6]),(0,[z7,z1,z3,z4,z5,z6,z362]),(0,[z7,z1,z3,z4,z140,z5,z6]),(0,[z257,z7,z1,z3,z4,z5,z6]),(0,[z7,z162,z1,z3,z4,z5,z85]),(1,[z7,z1,z363,z4,z5,z6]),(0,[z7,z1,z3,z364,z4,z5,z6]),(1,[z104,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z365,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z6,z232]),(0,[z7,z1,z3,z4,z366,z5,z6])],[(0,[z1,z2,z3,z4,z5,z25,z6]),(0,[z166,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z39,z23,z4,z5,z6]),(0,[z7,z367,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z368,z4,z5,z6]),(0,[z7,z1,z3,z13,z4,z41,z5])],[(0,[z14,z59,z1,z3,z4,z5,z6]),(0,[z369,z7,z1,z3,z4,z5,z6]),(0,[z54,z7,z1,z3,z35,z5,z6]),(0,[z55,z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z370,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z371]),(0,[z7,z1,z3,z4,z372,z5,z6])],[(0,[z7,z1,z3,z4,z5,z373,z6]),(0,[z7,z1,z3,z374,z47,z5,z6]),(0,[z7,z1,z3,z47,z5,z6,z232]),(0,[z7,z1,z39,z4,z28,z5,z6]),(0,[z7,z59,z1,z39,z4,z5,z6]),(0,[z200,z7,z1,z3,z4,z5,z82]),(0,[z7,z1,z142,z3,z4,z5,z143]),(0,[z7,z1,z3,z76,z5,z6,z60])],[(0,[z331,z7,z1,z3,z4,z5,z6]),(0,[z7,z375,z1,z3,z4,z5,z6]),(0,[z7,z1,z39,z44,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z376,z6]),(0,[z221,z7,z1,z3,z47,z5,z6]),(0,[z377,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z157,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z81,z5,z6]),(1,[z188,z1,z3,z4,z5,z6]),(1,[z7,z1,z378,z4,z5,z6]),(0,[z7,z1,z3,z4,z379,z5,z6])],[(0,[z53,z7,z61,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z380,z5,z6]),(0,[z7,z1,z3,z4,z5,z381,z6]),(0,[z7,z1,z3,z35,z5,z101,z6]),(0,[z7,z1,z3,z338,z4,z5,z6]),(0,[z7,z1,z10,z3,z9,z5,z6]),(1,[z7,z1,z3,z382,z4,z5]),(0,[z7,z1,z3,z4,z383,z5,z6])]],
   [[(0,[z14,z1,z3,z4,z5,z68,z6]),(0,[z7,z1,z384,z3,z4,z5,z6]),(0,[z18,z7,z1,z3,z35,z5,z6]),(0,[z385,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z9,z47,z5,z6]),(0,[z0,z7,z3,z4,z5,z101,z6]),(0,[z7,z86,z1,z3,z4,z24,z6]),(0,[z7,z1,z3,z4,z386,z5,z6])],[(1,[z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z121]),(0,[z34,z1,z83,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z387,z6]),(0,[z7,z1,z3,z35,z28,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z388]),(0,[z389,z7,z1,z3,z4,z5,z6]),(0,[z390,z7,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z20,z5,z6]),(0,[z7,z1,z2,z3,z35,z5,z6]),(0,[z7,z1,z3,z99,z35,z5,z6]),(0,[z391,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z392,z6]),(0,[z7,z22,z1,z3,z393,z5,z6]),(0,[z7,z394,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z5,z101,z6]),(0,[z7,z395,z1,z3,z4,z5,z6]),(0,[z396,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z397,z3,z4,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z228]),(0,[z7,z1,z3,z382,z4,z5,z6]),(0,[z398,z7,z1,z3,z4,z5,z6])],[(0,[z55,z7,z1,z3,z4,z77,z6]),(0,[z7,z1,z399,z3,z4,z5,z6]),(0,[z7,z1,z400,z3,z4,z5,z6]),(0,[z33,z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z401,z6]),(0,[z7,z1,z3,z4,z5,z6,z402]),(0,[z7,z1,z3,z403,z4,z5,z6]),(0,[z7,z404,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z35,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z405])],[(0,[z166,z1,z2,z3,z4,z5,z6]),(1,[z46,z2,z3,z4,z5,z6]),(0,[z94,z18,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z406,z4,z5,z6]),(0,[z7,z1,z407,z3,z4,z5,z6]),(0,[z344,z7,z3,z4,z47,z5,z6]),(0,[z7,z1,z3,z408,z4,z5,z6])],[(0,[z7,z1,z3,z4,z152,z5,z6])]],
   [[(0,[z7,z1,z409,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z410,z5,z6]),(0,[z7,z1,z3,z4,z5,z60,z82])],[(0,[z1,z2,z3,z4,z5,z6,z240]),(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z203,z1,z3,z4,z20,z5,z6]),(0,[z411,z7,z1,z3,z4,z5,z6]),(0,[z7,z46,z86,z3,z4,z5,z6]),(0,[z412,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z413,z3,z4,z5,z6]),(0,[z7,z1,z142,z3,z4,z5,z6])],[(0,[z1,z2,z3,z107,z4,z5,z6]),(0,[z7,z1,z414,z3,z4,z5,z6]),(1,[z7,z86,z3,z4,z24,z6]),(0,[z7,z1,z415,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z105,z5,z6])],[(0,[z1,z2,z3,z4,z5,z101,z6]),(0,[z7,z1,z3,z4,z416,z5,z6]),(0,[z7,z1,z44,z4,z5,z25,z6]),(0,[z7,z417,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z115,z5,z6]),(0,[z7,z1,z418,z3,z4,z5,z6])],[(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z14,z61,z1,z3,z4,z5,z6]),(0,[z419,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z420,z6]),(0,[z421,z7,z1,z3,z4,z5,z6]),(0,[z7,z59,z1,z142,z4,z5,z6]),(0,[z200,z7,z1,z3,z171,z5,z6])],[(0,[z19,z1,z3,z107,z4,z5,z6]),(0,[z104,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z422,z6]),(0,[z7,z1,z3,z47,z115,z5,z6]),(1,[z7,z59,z1,z9,z5,z6]),(1,[z1,z3,z4,z5,z6,z172])],[(1,[z7,z1,z3,z92,z5,z6]),(0,[z7,z1,z423,z3,z4,z5,z6]),(0,[z7,z1,z424,z3,z4,z5,z6]),(0,[z7,z46,z3,z35,z4,z5,z6]),(0,[z7,z1,z425,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z426]),(0,[z7,z1,z3,z13,z4,z105,z5])]],
   [[(0,[z18,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z427,z4,z5,z6]),(0,[z428,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z429,z5,z6]),(0,[z7,z430,z1,z3,z4,z5,z6])],[],[(0,[z7,z1,z3,z99,z47,z5,z6]),(0,[z7,z431,z1,z3,z4,z5,z6]),(0,[z166,z7,z1,z3,z4,z5,z420]),(0,[z7,z1,z3,z4,z432,z5,z6])],[(0,[z94,z1,z3,z4,z5,z138,z6])],[(0,[z7,z1,z3,z433,z4,z5,z6]),(0,[z7,z1,z3,z4,z434,z5,z6]),(0,[z7,z1,z305,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z435])],[(0,[z7,z1,z3,z4,z436,z5,z6]),(0,[z7,z1,z437,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z353,z6]),(0,[z7,z1,z3,z35,z5,z6,z278]),(0,[z7,z1,z3,z4,z5,z306,z6]),(0,[z438,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z439,z5,z6]),(0,[z440,z7,z1,z3,z4,z5,z6]),(0,[z200,z7,z1,z3,z4,z5,z232])],[(0,[z7,z1,z3,z4,z441,z5,z6]),(0,[z54,z7,z1,z3,z4,z5,z442]),(0,[z443,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z444])],[(0,[z1,z2,z3,z4,z115,z5,z6]),(0,[z7,z1,z3,z124,z47,z5,z6]),(1,[z7,z1,z3,z76,z5,z60])]],
   [[(0,[z1,z2,z3,z4,z24,z5,z6]),(0,[z445,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z446,z6]),(0,[z7,z1,z3,z47,z5,z6,z278]),(0,[z200,z7,z1,z3,z119,z5,z6])],[(0,[z14,z1,z3,z447,z4,z5,z6]),(0,[z139,z7,z1,z3,z4,z5,z6])],[(0,[z14,z162,z1,z3,z4,z5,z6]),(0,[z14,z1,z83,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z4,z5,z6]),(0,[z0,z7,z1,z3,z128,z5,z6]),(0,[z154,z7,z162,z3,z4,z5,z6]),(0,[z7,z1,z448,z3,z4,z5,z6])],[(0,[z53,z7,z1,z3,z169,z5,z6]),(0,[z449,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z450,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z451])],[(0,[z14,z1,z3,z4,z41,z5,z6]),(0,[z7,z452,z1,z3,z4,z5,z6]),(0,[z453,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z138,z232]),(0,[z154,z7,z1,z3,z4,z5,z110]),(0,[z200,z7,z1,z3,z4,z5,z143])],[(0,[z7,z1,z3,z454,z4,z5,z6]),(0,[z7,z1,z3,z4,z455,z5,z6]),(0,[z7,z1,z456,z3,z4,z5,z6]),(0,[z1,z3,z4,z259,z28,z5,z6]),(0,[z7,z1,z3,z457,z4,z5,z6]),(1,[z300,z1,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z5,z190]),(0,[z7,z1,z3,z35,z5,z6,z50]),(0,[z7,z1,z3,z4,z458,z5,z6]),(0,[z7,z1,z3,z459,z4,z5,z6]),(0,[z7,z3,z4,z24,z5,z101,z6]),(0,[z154,z7,z1,z3,z4,z5,z85])],[(0,[z7,z1,z3,z4,z5,z460,z6]),(0,[z7,z1,z3,z4,z5,z461,z6]),(0,[z462,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z463,z5,z6]),(0,[z7,z1,z3,z47,z5,z6,z333]),(0,[z7,z1,z3,z4,z41,z5,z143]),(0,[z7,z1,z3,z464,z4,z5,z6])]],
   [[(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z465]),(0,[z166,z7,z1,z3,z35,z5,z6]),(0,[z7,z22,z1,z3,z434,z5,z6]),(1,[z7,z1,z3,z393,z5,z6]),(0,[z7,z1,z3,z35,z345,z5,z6]),(0,[z7,z1,z3,z118,z4,z5,z6]),(0,[z7,z1,z3,z466,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z60,z232])],[(0,[z467,z7,z1,z3,z4,z5,z6]),(0,[z468,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z5,z6,z50]),(0,[z7,z1,z3,z469,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z60])],[(1,[z18,z1,z3,z20,z5,z6]),(0,[z470,z7,z1,z3,z4,z5,z6]),(0,[z316,z46,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z115,z5,z6,z278])],[(0,[z445,z1,z2,z3,z4,z5,z6]),(0,[z203,z14,z1,z3,z4,z5,z6]),(0,[z137,z14,z1,z3,z4,z5,z6]),(0,[z471,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z472,z5,z6]),(0,[z7,z86,z1,z3,z35,z5,z6]),(1,[z7,z1,z3,z4,z5,z388]),(0,[z7,z1,z3,z13,z4,z5,z110]),(0,[z7,z473,z1,z3,z4,z5,z6]),(0,[z7,z1,z75,z3,z41,z5,z6])],[(0,[z474,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z475,z5,z6])],[(0,[z344,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z476,z3,z4,z5,z6]),(0,[z7,z1,z3,z13,z4,z5,z85]),(0,[z7,z1,z10,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z85,z6]),(0,[z7,z477,z1,z3,z4,z5,z6]),(0,[z7,z1,z478,z3,z4,z5,z6]),(0,[z7,z22,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z99,z4,z5,z6]),(0,[z7,z1,z75,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z110,z82]),(0,[z7,z1,z3,z4,z5,z6,z479])]],
   [[(0,[z445,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z107,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z164,z6]),(0,[z7,z480,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z481,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z482]),(0,[z7,z59,z1,z3,z9,z5,z6]),(0,[z17,z7,z1,z363,z4,z5,z6])],[(0,[z7,z483,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z484,z5,z6]),(0,[z7,z1,z3,z234,z4,z5,z6]),(0,[z200,z7,z1,z142,z4,z5,z6])],[(0,[z1,z83,z3,z4,z5,z138,z6]),(0,[z7,z1,z3,z4,z5,z6,z485])],[(0,[z7,z1,z1,z3,z4,z5,z6]),(0,[z201,z7,z1,z3,z35,z5,z6]),(0,[z486,z7,z1,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z25,z6]),(0,[z7,z1,z487,z3,z4,z5,z6]),(0,[z7,z488,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z348,z5,z6]),(0,[z7,z1,z3,z44,z35,z5,z6]),(0,[z489,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z490,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z7,z491,z1,z3,z4,z5,z6])],[(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z492]),(0,[z7,z1,z4,z28,z5,z6,z82]),(0,[z7,z1,z3,z41,z5,z6,z60])],[(0,[z7,z1,z3,z493,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z138,z6]),(0,[z7,z1,z414,z3,z47,z5,z6]),(0,[z246,z86,z1,z3,z4,z5,z6]),(0,[z7,z1,z39,z3,z4,z152,z6])]],
   [[(0,[z344,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z76,z4,z5,z6]),(0,[z166,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z220,z47,z5,z6]),(0,[z494,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z495,z5,z6]),(1,[z186,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z496]),(0,[z7,z1,z10,z3,z4,z5,z492]),(0,[z7,z1,z39,z4,z152,z5,z6]),(0,[z7,z1,z3,z40,z4,z5,z232])],[(0,[z7,z1,z3,z4,z497,z5,z6]),(0,[z7,z1,z75,z3,z4,z41,z5])],[(0,[z14,z1,z3,z4,z20,z5,z6]),(1,[z7,z275,z3,z4,z5,z6]),(0,[z203,z7,z1,z3,z4,z5,z6]),(0,[z137,z7,z1,z3,z4,z5,z6]),(0,[z7,z86,z1,z3,z47,z5,z6]),(0,[z7,z276,z1,z3,z35,z5,z6]),(0,[z86,z1,z476,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z261,z6])],[(1,[z14,z1,z3,z4,z5,z6]),(0,[z54,z7,z1,z3,z4,z68,z6]),(0,[z344,z116,z1,z3,z4,z5,z6]),(1,[z245,z1,z3,z4,z5,z6]),(0,[z7,z1,z498,z3,z4,z5,z6])],[(0,[z7,z1,z3,z499,z4,z5,z6]),(0,[z7,z223,z1,z3,z4,z5,z6]),(0,[z344,z7,z1,z3,z4,z5,z6]),(0,[z7,z46,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z152,z5,z6]),(0,[z7,z1,z500,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z501,z5,z6])],[(1,[z55,z1,z3,z4,z5,z50]),(0,[z7,z1,z3,z502,z4,z5,z6]),(0,[z7,z503,z1,z3,z4,z5,z6])],[(0,[z1,z504,z2,z3,z4,z5,z6]),(0,[z505,z7,z1,z3,z4,z5,z6]),(1,[z412,z1,z3,z4,z5,z6]),(0,[z17,z7,z1,z3,z4,z5,z73])]],
   [[(0,[z7,z1,z3,z47,z152,z5,z6]),(0,[z7,z1,z3,z35,z105,z5,z6]),(0,[z506,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z507,z4,z5,z6]),(0,[z508,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z509,z3,z4,z5,z6]),(0,[z510,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z511,z5,z6]),(1,[z78,z1,z3,z4,z5,z6])],[(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z75,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z512,z5,z6]),(0,[z7,z1,z3,z248,z47,z5,z6]),(0,[z513,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z248,z4,z6,z278]),(0,[z7,z514,z1,z3,z4,z5,z6]),(0,[z7,z1,z515,z3,z4,z5,z6])],[(0,[z14,z1,z23,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z105,z5,z6]),(0,[z516,z7,z1,z3,z4,z5,z6]),(0,[z7,z86,z3,z4,z24,z5,z6]),(0,[z154,z7,z1,z3,z209,z5,z6]),(0,[z7,z1,z3,z4,z5,z517,z6]),(0,[z518,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z143,z6])],[(0,[z7,z1,z3,z4,z519,z5,z6]),(0,[z520,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z44,z47,z5,z6]),(0,[z7,z1,z3,z4,z152,z24,z6]),(0,[z7,z1,z3,z521,z4,z5,z6]),(0,[z154,z7,z1,z3,z338,z5,z6]),(0,[z7,z1,z3,z4,z522,z5,z6])],[(0,[z523,z7,z1,z3,z4,z5,z6]),(1,[z7,z86,z3,z47,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z524]),(1,[z7,z1,z3,z434,z5,z6]),(0,[z344,z525,z1,z3,z4,z5,z6]),(0,[z526,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z527,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z328,z6]),(0,[z7,z1,z3,z4,z5,z6,z190]),(0,[z7,z1,z528,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z529,z5,z6]),(0,[z7,z1,z3,z4,z47,z5,z6]),(0,[z7,z1,z3,z530,z4,z5,z6]),(0,[z7,z1,z3,z531,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z374,z5,z6]),(0,[z7,z1,z3,z35,z432,z5,z6]),(0,[z317,z7,z1,z3,z35,z5,z6]),(0,[z532,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z263,z3,z4,z5,z6])],[(0,[z7,z1,z44,z4,z5,z6,z82]),(0,[z7,z1,z3,z47,z429,z5,z6]),(1,[z7,z1,z48,z4,z5,z6]),(0,[z7,z1,z3,z248,z4,z115,z6]),(0,[z533,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z339,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z534,z6]),(0,[z535,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z536,z6])],[(1,[z116,z1,z3,z4,z5,z6]),(1,[z7,z3,z35,z47,z5,z6]),(0,[z7,z1,z39,z3,z4,z25,z6]),(0,[z7,z1,z3,z4,z41,z5,z82]),(0,[z7,z1,z3,z537,z4,z5,z6])],[(0,[z1,z2,z3,z4,z105,z5,z6]),(0,[z7,z1,z538,z3,z4,z5,z6]),(0,[z539,z7,z1,z3,z4,z5,z6]),(0,[z34,z7,z1,z3,z4,z5,z6]),(0,[z19,z7,z1,z3,z35,z5,z6]),(0,[z137,z7,z1,z3,z4,z5,z50]),(0,[z166,z7,z1,z3,z204,z5,z6]),(0,[z540,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z541,z4,z5,z6]),(0,[z7,z1,z39,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z542]),(0,[z7,z1,z3,z40,z4,z5,z6])],[(0,[z53,z7,z1,z3,z92,z5,z6]),(0,[z7,z1,z3,z20,z47,z5,z6]),(0,[z7,z543,z1,z3,z4,z5,z6]),(0,[z544,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z348,z5,z6]),(0,[z7,z22,z23,z3,z4,z5,z6])],[(0,[z14,z1,z3,z9,z4,z5,z6]),(0,[z14,z1,z3,z13,z4,z5,z6]),(0,[z7,z1,z3,z4,z545,z5,z6]),(1,[z0,z7,z3,z4,z101,z6])],[(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z546,z6]),(0,[z54,z1,z3,z4,z5,z68,z6]),(1,[z7,z1,z3,z4,z105,z232])]],
   [[(0,[z7,z1,z3,z4,z547,z5,z6]),(0,[z548,z7,z1,z3,z4,z5,z6]),(0,[z549,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z550,z6]),(0,[z551,z7,z1,z3,z4,z5,z6])],[(0,[z1,z2,z423,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z232]),(0,[z14,z1,z3,z4,z24,z5,z6]),(0,[z166,z127,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z479]),(0,[z291,z7,z1,z3,z4,z5,z6])],[(0,[z18,z7,z70,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z239,z5,z6]),(0,[z7,z1,z10,z3,z47,z5,z6]),(0,[z7,z59,z1,z3,z28,z5,z6]),(0,[z7,z1,z3,z4,z552,z5,z6]),(0,[z7,z553,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z554])],[(0,[z7,z1,z3,z4,z5,z555,z6]),(0,[z7,z1,z3,z4,z556,z5,z6]),(0,[z557,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z420]),(0,[z7,z1,z3,z4,z5,z558,z6]),(0,[z7,z22,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z35,z455,z5,z6]),(0,[z7,z1,z3,z559,z4,z5,z6]),(0,[z7,z1,z3,z4,z560,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z561])],[(0,[z7,z1,z3,z4,z512,z5,z6]),(0,[z7,z1,z3,z4,z5,z562,z6]),(0,[z17,z300,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z244,z5,z6]),(0,[z14,z14,z1,z3,z4,z5,z6]),(0,[z1,z83,z3,z4,z5,z68,z6]),(0,[z7,z1,z563,z3,z4,z5,z6]),(0,[z7,z1,z57,z3,z4,z5,z6]),(1,[z525,z1,z3,z4,z5,z6]),(0,[z445,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z85,z82]),(0,[z7,z1,z3,z564,z4,z5,z6]),(0,[z7,z565,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z566,z5,z6]),(1,[z7,z1,z3,z40,z13,z4])],[(0,[z7,z1,z3,z4,z5,z226,z6]),(0,[z7,z1,z3,z76,z35,z5,z6]),(0,[z7,z59,z1,z3,z4,z5,z6]),(0,[z7,z567,z1,z3,z4,z5,z6]),(0,[z7,z1,z568,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z569,z5,z6]),(0,[z570,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z354,z3,z35,z5,z6]),(0,[z7,z1,z3,z35,z5,z6,z60]),(0,[z7,z1,z3,z4,z152,z5,z479]),(0,[z7,z1,z3,z382,z4,z152,z5]),(1,[z200,z7,z1,z4,z5,z82])]],
   [[(0,[z1,z2,z3,z4,z28,z5,z6]),(0,[z94,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z571,z5,z6]),(0,[z572,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z492])],[(0,[z1,z2,z3,z44,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z68,z6]),(1,[z67,z7,z1,z3,z5,z6]),(1,[z7,z1,z3,z5,z164,z6]),(0,[z7,z1,z3,z47,z5,z6,z60]),(0,[z7,z1,z3,z4,z5,z573,z6]),(0,[z7,z1,z100,z3,z4,z5,z6]),(0,[z7,z1,z574,z3,z4,z5,z6]),(0,[z1,z3,z4,z105,z501,z5,z6])],[(0,[z7,z1,z3,z40,z4,z101,z6])],[(0,[z575,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z576,z6]),(0,[z19,z7,z1,z3,z47,z5,z6]),(1,[z7,z1,z3,z4,z353,z6]),(1,[z7,z1,z3,z4,z306,z6]),(1,[z201,z7,z1,z4,z25,z6]),(0,[z7,z1,z577,z3,z4,z5,z6])],[],[(0,[z18,z7,z1,z3,z20,z5,z6]),(0,[z578,z7,z1,z3,z4,z5,z6])],[(0,[z137,z7,z1,z3,z4,z5,z138]),(0,[z7,z1,z3,z4,z5,z273,z6]),(0,[z579,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z580,z6]),(0,[z7,z1,z3,z4,z105,z6,z232])]],
   [[(0,[z14,z1,z2,z3,z4,z5,z6]),(2,[z2,z3,z47,z5,z6]),(0,[z14,z1,z3,z99,z4,z5,z6]),(0,[z203,z7,z1,z3,z47,z5,z6]),(0,[z137,z7,z1,z3,z47,z5,z6])],[(1,[z14,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z581]),(1,[z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z47,z5,z6,z482]),(0,[z316,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z582,z4,z5,z6]),(0,[z7,z1,z3,z4,z152,z101,z6]),(0,[z7,z1,z3,z583,z4,z5,z6]),(0,[z7,z1,z3,z76,z4,z41,z5]),(0,[z7,z1,z3,z4,z5,z584,z6])],[(0,[z7,z1,z3,z4,z5,z585,z6]),(0,[z344,z7,z1,z3,z47,z5,z6]),(0,[z162,z1,z263,z3,z4,z5,z6]),(1,[z7,z162,z3,z4,z5,z85]),(0,[z17,z318,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z378,z4,z5,z6]),(0,[z586,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z40,z4,z105,z6])],[(0,[z1,z2,z3,z4,z5,z6,z60]),(0,[z14,z1,z3,z4,z5,z6,z110]),(0,[z200,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z41,z5,z232])],[(0,[z7,z1,z151,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z114,z6]),(0,[z587,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z393,z4,z5,z6]),(0,[z7,z1,z3,z4,z588,z5,z6]),(0,[z7,z1,z3,z589,z4,z5,z6])],[(0,[z14,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z590]),(0,[z7,z1,z591,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z138,z6]),(1,[z7,z225,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z592]),(0,[z7,z1,z3,z4,z593,z5,z6])],[(0,[z7,z61,z1,z3,z4,z5,z6]),(0,[z594,z1,z2,z3,z4,z5,z6]),(0,[z595,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z76,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z596,z6])],[(0,[z1,z2,z3,z295,z4,z5,z6]),(0,[z1,z2,z10,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z597])]],
   [[(0,[z7,z1,z3,z4,z68,z6,z232]),(0,[z7,z1,z3,z47,z5,z138,z6])],[(0,[z55,z1,z83,z3,z4,z5,z6]),(0,[z7,z598,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z50,z232]),(0,[z599,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z142,z3,z35,z5,z6]),(1,[z246,z1,z3,z4,z5,z6]),(0,[z600,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z4,z178,z5,z6])],[(0,[z601,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z145,z5,z6]),(0,[z14,z1,z3,z4,z5,z6,z82]),(0,[z7,z1,z3,z4,z5,z602,z6])],[(0,[z594,z7,z1,z3,z4,z5,z6]),(0,[z17,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z603]),(0,[z7,z1,z3,z35,z248,z5,z6]),(0,[z7,z1,z604,z3,z4,z5,z6]),(0,[z7,z605,z1,z3,z4,z5,z6]),(0,[z606,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z607,z4,z5,z6])],[(1,[z1,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z278]),(0,[z608,z7,z1,z3,z4,z5,z6]),(1,[z154,z7,z3,z4,z5,z110]),(1,[z17,z7,z1,z3,z6,z278])],[(0,[z7,z1,z3,z4,z5,z85,z232]),(0,[z7,z1,z3,z4,z5,z6,z609])],[(0,[z200,z1,z2,z3,z4,z5,z6]),(0,[z377,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z610,z5,z6]),(0,[z535,z1,z3,z4,z28,z5,z6])],[(0,[z601,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z228]),(0,[z7,z611,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z612,z5,z6]),(0,[z7,z1,z3,z4,z5,z613,z6]),(0,[z186,z7,z1,z3,z4,z5,z6])]],
   [[],[(0,[z1,z2,z3,z4,z5,z138,z6]),(1,[z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z40,z47,z5,z6]),(0,[z7,z1,z3,z35,z5,z143,z6]),(0,[z0,z7,z1,z234,z4,z5,z6]),(1,[z535,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z614,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z615]),(0,[z7,z616,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z40,z13,z4,z6])],[(0,[z53,z14,z1,z3,z4,z5,z6]),(0,[z67,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z511,z5,z6]),(0,[z7,z1,z3,z197,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z617,z6])],[(0,[z7,z1,z3,z447,z4,z5,z6]),(0,[z7,z618,z1,z3,z4,z5,z6]),(0,[z200,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z4,z5,z143,z6,z82])],[(0,[z7,z1,z83,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z5,z143,z6]),(0,[z7,z162,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z619,z6]),(0,[z7,z1,z363,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z50]),(0,[z7,z1,z3,z35,z47,z5,z6]),(0,[z7,z1,z3,z4,z620,z5,z6])],[(0,[z17,z1,z2,z3,z4,z5,z6]),(0,[z18,z19,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z41,z5,z6])],[(0,[z7,z1,z3,z87,z4,z5,z6]),(0,[z7,z59,z1,z4,z5,z25,z6]),(0,[z7,z621,z1,z3,z4,z5,z6])]],
   [[(1,[z14,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z98,z4,z5,z6]),(0,[z622,z7,z1,z3,z4,z5,z6]),(0,[z525,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z47,z5,z6]),(0,[z0,z257,z1,z3,z4,z5,z6]),(0,[z17,z7,z1,z378,z4,z5,z6])],[(0,[z94,z1,z3,z107,z4,z5,z6]),(0,[z7,z1,z3,z623,z4,z5,z6]),(0,[z7,z1,z3,z4,z624,z5,z6]),(0,[z625,z7,z1,z3,z4,z5,z6]),(0,[z166,z7,z3,z44,z4,z5,z6]),(0,[z7,z1,z142,z3,z47,z5,z6]),(0,[z411,z7,z1,z3,z47,z5,z6]),(0,[z0,z7,z86,z3,z4,z5,z6])],[(0,[z626,z1,z2,z3,z4,z5,z6]),(0,[z7,z61,z3,z4,z47,z5,z6]),(0,[z7,z1,z3,z627,z4,z5,z6]),(0,[z628,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z629,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z630,z5,z6])],[(1,[z94,z1,z99,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z442]),(0,[z7,z1,z631,z3,z4,z5,z6]),(0,[z7,z59,z1,z3,z47,z5,z6]),(0,[z17,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z632,z4,z5,z6])],[(0,[z94,z55,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z633,z6]),(0,[z203,z1,z3,z4,z5,z6,z50]),(1,[z7,z1,z3,z4,z5,z11])],[(0,[z53,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z7,z1,z3,z454,z35,z5,z6]),(0,[z7,z1,z3,z634,z4,z5,z6])],[(0,[z1,z3,z4,z5,z68,z6,z50]),(0,[z137,z203,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z459,z35,z5,z6])],[(0,[z626,z7,z1,z3,z4,z5,z6]),(0,[z539,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z93,z4,z5,z6]),(0,[z7,z275,z1,z3,z4,z5,z6]),(1,[z1,z476,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z635,z5,z6]),(0,[z7,z1,z31,z76,z4,z5,z6]),(0,[z7,z1,z3,z4,z636,z5,z6])]],
   [[(0,[z7,z1,z3,z35,z239,z5,z6]),(0,[z7,z1,z637,z3,z4,z5,z6]),(0,[z344,z7,z46,z3,z4,z5,z6]),(0,[z7,z1,z638,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z639]),(0,[z7,z1,z3,z4,z5,z85,z6]),(0,[z640,z7,z1,z3,z4,z5,z6])],[(0,[z14,z86,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z641,z5,z6]),(0,[z7,z1,z3,z40,z4,z24,z6]),(0,[z7,z1,z642,z3,z4,z5,z6])],[(0,[z53,z7,z1,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z6,z232]),(0,[z7,z3,z4,z5,z85,z6,z110]),(0,[z7,z1,z3,z4,z5,z6,z643])],[(0,[z7,z1,z3,z4,z644,z5,z6]),(0,[z7,z1,z3,z47,z239,z5,z6]),(0,[z7,z1,z3,z4,z81,z5,z6]),(0,[z201,z7,z1,z3,z4,z152,z6])],[(0,[z7,z1,z3,z645,z4,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z388]),(1,[z7,z1,z3,z313,z5,z6])],[(0,[z646,z7,z1,z3,z4,z5,z6]),(1,[z137,z1,z3,z4,z5,z138]),(1,[z7,z1,z3,z204,z5,z6]),(0,[z7,z1,z10,z3,z35,z5,z6]),(0,[z154,z7,z1,z3,z4,z279,z6]),(0,[z188,z162,z1,z3,z4,z5,z6]),(0,[z647,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z143,z60])],[(0,[z648,z7,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z40,z4,z5,z6]),(0,[z14,z1,z3,z107,z4,z5,z6]),(0,[z203,z7,z1,z3,z4,z239,z6]),(0,[z7,z1,z3,z4,z5,z6,z649]),(0,[z7,z22,z1,z3,z35,z5,z6]),(0,[z650,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z25,z6]),(0,[z651,z7,z1,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z5,z101,z6]),(0,[z652,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z5,z6]),(0,[z7,z1,z653,z3,z4,z5,z6]),(0,[z166,z7,z1,z23,z4,z5,z6]),(0,[z654,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z14,z1,z3,z248,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z68,z6]),(0,[z445,z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z117,z5,z6])],[(0,[z1,z2,z3,z4,z5,z546,z6]),(0,[z154,z14,z1,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z28,z5,z6]),(0,[z7,z1,z3,z4,z133,z5,z6])],[(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z14,z1,z3,z44,z4,z5,z6]),(0,[z14,z7,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z655,z5,z6]),(0,[z7,z1,z3,z4,z5,z442,z6]),(1,[z127,z1,z3,z4,z5,z6]),(0,[z166,z7,z1,z44,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z110,z232]),(0,[z7,z1,z3,z4,z259,z5,z6]),(0,[z201,z7,z1,z39,z4,z5,z6])],[(0,[z7,z1,z504,z3,z4,z5,z6]),(0,[z94,z14,z1,z3,z4,z5,z6]),(0,[z7,z61,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z47,z5,z68,z6]),(0,[z166,z7,z1,z3,z4,z5,z21]),(0,[z7,z1,z1,z3,z35,z5,z6]),(0,[z17,z7,z1,z3,z5,z6,z278])],[(0,[z1,z2,z3,z4,z152,z5,z6]),(0,[z1,z2,z3,z4,z239,z5,z6]),(0,[z656,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z657,z4,z5,z6]),(0,[z34,z7,z1,z83,z4,z5,z6]),(0,[z1,z3,z107,z4,z20,z5,z6]),(0,[z1,z3,z4,z20,z5,z68,z6]),(0,[z154,z412,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z658,z5,z6]),(0,[z7,z1,z3,z4,z659,z5,z6])],[(1,[z7,z1,z3,z51,z5,z6]),(0,[z7,z1,z3,z4,z20,z5,z6]),(0,[z55,z7,z1,z3,z4,z5,z138]),(1,[z1,z3,z4,z5,z261,z6])],[(0,[z1,z2,z3,z4,z512,z5,z6]),(0,[z1,z2,z142,z3,z4,z5,z6]),(0,[z154,z78,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z660]),(0,[z7,z1,z3,z4,z661,z5,z6]),(1,[z7,z153,z3,z4,z5,z6])],[(0,[z575,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z662,z4,z5,z6]),(0,[z663,z7,z1,z3,z4,z5,z6]),(1,[z54,z1,z3,z4,z68,z6]),(0,[z7,z1,z3,z4,z5,z664,z6]),(0,[z7,z665,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z501,z5,z6]),(0,[z7,z1,z666,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z667,z4,z5,z6]),(0,[z7,z1,z75,z3,z28,z5,z6]),(0,[z668,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z669,z4,z5,z6]),(0,[z7,z59,z1,z9,z4,z5,z6])],[(0,[z0,z7,z1,z235,z4,z5,z6]),(0,[z7,z1,z9,z4,z28,z5,z6]),(0,[z7,z1,z3,z4,z670,z5,z6]),(0,[z7,z1,z3,z4,z671,z5,z6])],[(0,[z672,z7,z1,z3,z4,z5,z6]),(1,[z2,z3,z4,z47,z5,z6]),(0,[z14,z1,z3,z4,z115,z5,z6]),(0,[z7,z673,z1,z3,z4,z5,z6]),(0,[z203,z7,z1,z3,z35,z5,z6]),(0,[z137,z7,z1,z3,z35,z5,z6]),(0,[z674,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z675])],[(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z68,z6]),(1,[z14,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z676,z6]),(0,[z677,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z678,z6]),(0,[z7,z1,z3,z679,z4,z5,z6]),(0,[z7,z1,z75,z3,z4,z5,z6])],[(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z288,z3,z4,z5,z6]),(0,[z0,z14,z1,z3,z4,z5,z6]),(0,[z18,z7,z1,z3,z107,z5,z6]),(0,[z7,z1,z23,z3,z4,z5,z6]),(0,[z344,z7,z1,z3,z35,z5,z6]),(0,[z7,z46,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z28,z5,z6,z60]),(0,[z7,z680,z1,z3,z4,z5,z6]),(0,[z7,z681,z1,z3,z4,z5,z6])],[(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z102,z3,z4,z5,z6]),(1,[z7,z1,z3,z93,z5,z6]),(0,[z94,z1,z3,z99,z4,z5,z6]),(0,[z7,z1,z682,z3,z4,z5,z6]),(0,[z19,z7,z1,z3,z107,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z683])],[(0,[z19,z1,z3,z4,z5,z68,z6]),(0,[z7,z1,z3,z40,z4,z239,z6]),(0,[z7,z86,z1,z3,z211,z5,z6]),(0,[z7,z1,z3,z684,z4,z5,z6])]],
   [[(0,[z14,z1,z10,z3,z4,z5,z6]),(0,[z139,z22,z1,z3,z4,z5,z6]),(0,[z200,z7,z1,z3,z47,z5,z6])],[(0,[z166,z223,z1,z3,z4,z5,z6]),(0,[z7,z162,z1,z3,z47,z5,z6]),(0,[z7,z685,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z6,z603]),(0,[z154,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z10,z28,z5,z6]),(0,[z291,z1,z3,z4,z5,z6,z82]),(0,[z7,z1,z3,z4,z5,z686,z6]),(0,[z7,z1,z3,z4,z687,z5,z6])],[(0,[z7,z1,z3,z4,z5,z688,z6]),(0,[z14,z1,z3,z4,z302,z5,z6]),(0,[z7,z1,z689,z3,z4,z5,z6]),(0,[z690,z7,z1,z3,z4,z5,z6]),(0,[z691,z7,z1,z3,z4,z5,z6])],[(0,[z7,z367,z1,z3,z4,z5,z6]),(0,[z7,z1,z1,z3,z47,z5,z6]),(1,[z1,z157,z3,z4,z5,z6]),(0,[z7,z1,z692,z3,z4,z5,z6]),(0,[z7,z693,z1,z3,z4,z5,z6])],[(0,[z656,z7,z1,z3,z4,z5,z6]),(0,[z54,z14,z1,z3,z4,z5,z6]),(0,[z55,z14,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z370,z4,z5,z6]),(0,[z327,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z694,z4,z5,z6]),(0,[z7,z1,z3,z4,z695,z5,z6])],[(0,[z14,z1,z3,z4,z5,z6,z278]),(0,[z7,z1,z3,z696,z4,z5,z6]),(0,[z7,z697,z1,z3,z4,z5,z6]),(0,[z698,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z699,z4,z5,z6]),(0,[z7,z1,z3,z700,z4,z5,z6]),(1,[z7,z3,z47,z5,z101,z6]),(0,[z7,z1,z3,z4,z313,z5,z6]),(0,[z7,z1,z3,z248,z115,z5,z6])],[(0,[z221,z7,z1,z3,z4,z5,z6]),(0,[z701,z7,z1,z3,z4,z5,z6]),(1,[z166,z7,z44,z4,z5,z6]),(0,[z702,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z703,z6]),(0,[z7,z318,z1,z3,z4,z5,z6])],[(1,[z1,z2,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z239,z6,z232]),(0,[z7,z1,z3,z704,z4,z5,z6]),(0,[z705,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z305,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z706]),(0,[z7,z1,z3,z13,z4,z5,z60])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z656,z1,z447,z4,z5,z6]),(0,[z707,z1,z3,z4,z5,z6]),(0,[z1,z3,z107,z708,z5,z6]),(0,[z709,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z710]),(0,[z7,z1,z3,z711,z5,z6])],[(0,[z2,z3,z47,z511,z5,z6]),(0,[z7,z1,z3,z712,z5,z6]),(0,[z7,z1,z3,z4,z5,z442]),(0,[z7,z1,z3,z713,z5,z6]),(0,[z7,z637,z3,z47,z5,z6]),(0,[z535,z1,z10,z28,z5,z6]),(0,[z714,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z715,z5]),(0,[z54,z1,z3,z4,z328,z6]),(0,[z7,z1,z3,z4,z5,z11]),(0,[z1,z3,z4,z501,z5,z232])],[(0,[z14,z122,z3,z4,z5,z6]),(0,[z716,z1,z3,z4,z5,z6])],[(0,[z14,z153,z3,z4,z5,z6]),(0,[z7,z1,z3,z717,z5,z6]),(0,[z17,z7,z1,z3,z73,z278])],[(0,[z7,z1,z4,z718,z5,z6]),(0,[z7,z1,z3,z171,z5,z82])],[(0,[z1,z2,z3,z204,z5,z6]),(0,[z166,z2,z44,z4,z5,z6]),(0,[z7,z1,z3,z4,z353,z138]),(0,[z1,z3,z4,z5,z353,z50]),(0,[z7,z3,z432,z47,z5,z6])],[(0,[z7,z1,z3,z719,z5,z6]),(0,[z201,z7,z1,z47,z25,z6])],[(1,[z7,z1,z4,z5,z720])],[(0,[z1,z504,z3,z4,z244,z6]),(0,[z523,z2,z3,z4,z5,z6]),(0,[z1,z57,z3,z393,z5,z6])],[(0,[z721,z1,z3,z4,z5,z6]),(0,[z7,z722,z3,z4,z5,z6]),(0,[z7,z1,z3,z313,z5,z6])],[],[(0,[z7,z504,z3,z47,z5,z6]),(0,[z7,z1,z3,z5,z723,z6]),(0,[z166,z7,z44,z348,z5,z6]),(0,[z7,z1,z3,z128,z5,z6]),(0,[z535,z1,z3,z35,z5,z6])],[(0,[z7,z375,z3,z47,z5,z6])],[(0,[z1,z83,z4,z463,z5,z6]),(0,[z1,z3,z35,z724,z5,z6]),(0,[z7,z1,z3,z725,z5,z6]),(0,[z7,z1,z642,z4,z5,z82]),(1,[z7,z1,z3,z4,z726])]],
   [[(0,[z2,z3,z47,z5,z546,z6]),(0,[z1,z3,z4,z727,z5,z6]),(0,[z7,z22,z23,z393,z5,z6]),(0,[z46,z476,z3,z4,z5,z6])],[(0,[z7,z3,z47,z5,z180,z6]),(0,[z728,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z73])],[(0,[z14,z480,z3,z4,z5,z6]),(0,[z7,z1,z414,z28,z5,z6]),(0,[z7,z1,z3,z4,z5,z729]),(0,[z730,z1,z3,z4,z5,z6])],[(0,[z2,z3,z47,z239,z5,z6]),(0,[z7,z1,z731,z47,z5,z6]),(0,[z1,z732,z3,z4,z5,z6])],[(0,[z7,z1,z3,z51,z5,z6]),(0,[z14,z1,z3,z4,z5,z733]),(0,[z14,z3,z47,z5,z101,z6]),(0,[z734,z1,z3,z4,z5,z6])],[(0,[z2,z3,z47,z512,z5,z6]),(0,[z1,z3,z4,z472,z5,z50])],[(0,[z94,z2,z3,z47,z5,z6]),(0,[z14,z1,z305,z4,z5,z6]),(0,[z7,z1,z735,z35,z5,z6]),(0,[z7,z3,z42,z35,z5,z6])],[(0,[z7,z1,z736,z4,z5,z6]),(0,[z1,z737,z3,z4,z5,z6])],[(0,[z7,z1,z3,z738,z5,z6]),(0,[z55,z1,z3,z4,z353,z50])],[(0,[z7,z1,z3,z739,z5,z6]),(0,[z67,z54,z1,z3,z68,z6]),(0,[z7,z1,z3,z4,z740,z6]),(0,[z7,z430,z3,z47,z5,z6])],[(0,[z154,z78,z3,z4,z5,z110])],[(0,[z2,z3,z47,z5,z68,z6]),(0,[z7,z1,z741,z4,z5,z6]),(0,[z78,z1,z305,z4,z5,z6])],[],[(0,[z535,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z726,z5])],[(0,[z7,z1,z3,z742,z5,z6]),(0,[z743,z1,z3,z4,z5,z6])],[]],
   [[(0,[z1,z3,z4,z744,z5,z6]),(0,[z7,z1,z342,z28,z5,z6])],[(0,[z1,z263,z3,z4,z5,z6]),(1,[z70,z3,z20,z5,z6]),(1,[z1,z3,z708,z5,z6]),(0,[z7,z1,z3,z47,z5,z745]),(0,[z7,z162,z3,z313,z5,z85]),(0,[z7,z1,z3,z746,z5,z6])],[(0,[z7,z1,z3,z747,z5,z6])],[(0,[z53,z2,z3,z92,z5,z6]),(0,[z14,z1,z3,z4,z77,z6]),(0,[z7,z1,z3,z4,z273,z21]),(0,[z7,z1,z48,z4,z306,z6]),(0,[z1,z3,z40,z4,z501,z6])],[(0,[z14,z2,z3,z47,z5,z6]),(0,[z17,z7,z1,z3,z446,z6]),(0,[z7,z1,z3,z4,z748,z6]),(0,[z749,z1,z3,z4,z5,z6])],[(0,[z55,z1,z3,z4,z77,z50]),(0,[z7,z1,z3,z47,z5,z750]),(0,[z7,z310,z3,z47,z5,z6])],[(0,[z1,z2,z3,z4,z751,z6]),(0,[z752,z1,z3,z4,z5,z6])],[(0,[z34,z1,z83,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z753])],[(0,[z7,z1,z3,z754,z5,z6]),(0,[z7,z1,z3,z4,z5,z755]),(0,[z7,z1,z3,z47,z5,z11]),(0,[z756,z1,z3,z4,z5,z6])],[(0,[z7,z3,z519,z47,z5,z6]),(0,[z7,z1,z3,z757,z4,z5]),(0,[z245,z1,z3,z4,z5,z228]),(0,[z7,z758,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z759]),(0,[z7,z760,z3,z4,z5,z6])],[(0,[z7,z46,z3,z35,z5,z6]),(0,[z761,z1,z3,z4,z5,z6]),(0,[z7,z1,z75,z3,z41,z5]),(0,[z7,z1,z762,z4,z5,z6])],[(0,[z1,z2,z3,z169,z5,z6]),(0,[z166,z7,z44,z4,z5,z420]),(0,[z763,z1,z3,z4,z5,z6]),(0,[z318,z1,z363,z4,z5,z6])],[(0,[z2,z3,z98,z47,z5,z6]),(0,[z236,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z118,z5,z6]),(0,[z344,z116,z3,z47,z5,z6]),(0,[z0,z7,z3,z35,z101,z6]),(0,[z300,z1,z3,z4,z5,z73])],[(0,[z102,z2,z3,z47,z5,z6]),(0,[z1,z57,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z77,z6]),(0,[z67,z19,z1,z3,z5,z6]),(0,[z7,z22,z23,z434,z5,z6])],[]],
   [[(0,[z7,z357,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z764,z6]),(0,[z7,z1,z3,z765,z5,z6]),(0,[z766,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z171,z5,z6]),(0,[z7,z767,z3,z4,z5,z6])],[(0,[z7,z1,z768,z4,z5,z6]),(0,[z769,z2,z3,z4,z5,z6]),(0,[z7,z1,z75,z3,z194,z5]),(0,[z770,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z178,z5,z60])],[(0,[z7,z96,z3,z47,z5,z6]),(0,[z7,z1,z3,z771,z5,z6]),(0,[z772,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z773,z5,z6])],[(0,[z144,z1,z3,z512,z5,z6]),(0,[z2,z3,z42,z4,z5,z6]),(0,[z7,z22,z23,z4,z5,z6]),(0,[z7,z1,z3,z124,z133,z5]),(0,[z1,z3,z4,z5,z774,z6])],[(0,[z14,z1,z363,z4,z5,z6]),(0,[z7,z775,z3,z4,z5,z6]),(0,[z776,z1,z3,z4,z5,z6])],[(0,[z70,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z484,z232]),(0,[z7,z1,z305,z4,z306,z6])],[(0,[z651,z1,z3,z4,z5,z50]),(0,[z65,z7,z3,z47,z5,z6]),(0,[z777,z1,z3,z4,z5,z6]),(0,[z778,z7,z3,z4,z5,z6])],[(0,[z1,z2,z3,z118,z5,z6]),(0,[z7,z1,z3,z779,z5,z6]),(0,[z780,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z781])],[(0,[z18,z1,z3,z571,z5,z6]),(0,[z7,z1,z3,z40,z645,z4]),(0,[z111,z7,z3,z4,z101,z6])],[(0,[z166,z7,z44,z35,z5,z6]),(0,[z7,z404,z23,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z782]),(0,[z783,z1,z3,z4,z5,z6])],[(0,[z642,z2,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z5,z21]),(0,[z7,z1,z3,z4,z239,z190]),(0,[z137,z1,z3,z4,z353,z6]),(0,[z7,z1,z3,z338,z5,z6]),(0,[z7,z1,z3,z35,z306,z6]),(0,[z7,z1,z234,z4,z5,z388]),(0,[z7,z3,z4,z784,z101,z6])],[(0,[z14,z1,z31,z4,z5,z6]),(0,[z7,z488,z3,z35,z5,z6]),(0,[z411,z7,z1,z3,z6,z482])],[(0,[z7,z785,z3,z4,z5,z6]),(0,[z786,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z787,z4,z5]),(0,[z7,z616,z3,z4,z24,z6]),(0,[z7,z1,z3,z119,z5,z6])],[(0,[z7,z149,z3,z47,z5,z6])],[(1,[z116,z3,z47,z5,z6]),(0,[z7,z1,z3,z13,z4,z552])]],
   [[(0,[z1,z2,z363,z4,z5,z6])],[(0,[z225,z2,z3,z4,z5,z6]),(0,[z46,z157,z3,z35,z5,z6]),(0,[z788,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z789,z5,z6]),(0,[z7,z106,z3,z47,z5,z6]),(0,[z94,z1,z790,z4,z5,z6]),(0,[z7,z1,z4,z791,z5,z6]),(0,[z1,z3,z35,z5,z261,z6]),(0,[z257,z1,z3,z4,z5,z388]),(0,[z7,z1,z3,z4,z5,z792]),(0,[z7,z1,z142,z4,z5,z143])],[(0,[z61,z769,z3,z4,z5,z6]),(0,[z7,z61,z3,z793,z5,z6]),(0,[z1,z3,z4,z5,z6,z794]),(0,[z7,z3,z47,z5,z6,z341])],[(0,[z2,z39,z3,z47,z5,z6]),(0,[z2,z3,z40,z47,z5,z6]),(0,[z14,z1,z3,z211,z5,z6]),(0,[z203,z1,z3,z4,z145,z6]),(0,[z1,z3,z35,z501,z5,z6])],[(0,[z104,z1,z3,z4,z5,z6]),(0,[z1,z3,z47,z5,z261,z6]),(0,[z795,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z21]),(0,[z310,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z796,z5,z6]),(0,[z154,z7,z3,z4,z306,z110])],[(0,[z1,z2,z31,z4,z5,z6]),(0,[z1,z3,z4,z797,z5,z6]),(0,[z7,z1,z3,z798,z5,z6]),(0,[z1,z3,z47,z501,z5,z6]),(0,[z7,z1,z142,z4,z5,z451])],[(0,[z1,z2,z3,z799,z4,z5]),(0,[z411,z7,z3,z4,z101,z6])],[(0,[z7,z1,z800,z4,z5,z6]),(0,[z7,z1,z3,z801,z4,z6])],[(0,[z2,z23,z3,z47,z5,z6]),(0,[z2,z3,z47,z133,z5,z6]),(0,[z1,z83,z4,z5,z585,z6]),(0,[z166,z7,z44,z47,z5,z6]),(0,[z1,z3,z4,z802,z5,z6]),(0,[z803,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z804,z6]),(0,[z7,z431,z3,z47,z5,z6]),(0,[z7,z3,z47,z101,z6,z232]),(0,[z7,z1,z3,z47,z306,z6]),(0,[z7,z1,z3,z382,z4,z5])],[(0,[z14,z1,z234,z4,z5,z6]),(0,[z7,z1,z75,z3,z117,z5])],[(0,[z601,z2,z3,z47,z5,z6])],[(0,[z377,z1,z3,z512,z5,z6]),(0,[z7,z1,z3,z35,z5,z228]),(0,[z7,z1,z234,z4,z24,z6]),(0,[z7,z1,z3,z805,z5,z6])],[(0,[z1,z2,z3,z211,z5,z6]),(0,[z1,z2,z3,z806,z4,z5]),(0,[z1,z3,z4,z807,z68,z6]),(0,[z7,z1,z414,z429,z5,z6])]],
   [[(0,[z86,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z808,z5,z6]),(0,[z7,z1,z10,z28,z5,z11])],[(0,[z7,z1,z3,z4,z809,z6]),(0,[z137,z1,z3,z4,z5,z114]),(0,[z7,z1,z3,z810,z5,z6]),(0,[z67,z7,z785,z3,z5,z6]),(0,[z7,z3,z47,z5,z376,z6])],[],[(0,[z2,z3,z4,z169,z5,z6]),(0,[z7,z1,z3,z135,z5,z60]),(0,[z7,z1,z4,z178,z41,z5])],[],[(0,[z7,z1,z4,z28,z5,z492])],[(0,[z7,z1,z3,z4,z811,z6]),(0,[z812,z1,z3,z4,z5,z6]),(0,[z7,z86,z3,z4,z24,z6])],[(0,[z14,z2,z3,z35,z5,z6]),(0,[z1,z2,z234,z4,z5,z6]),(0,[z548,z2,z3,z4,z5,z6]),(0,[z7,z70,z3,z47,z5,z6]),(0,[z7,z1,z3,z813,z5,z6]),(0,[z1,z814,z3,z4,z5,z6]),(0,[z1,z10,z259,z28,z5,z6]),(0,[z1,z815,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z273,z6]),(0,[z7,z1,z3,z4,z816,z6]),(0,[z7,z1,z3,z817,z5,z6])],[(0,[z7,z1,z3,z4,z5,z818]),(1,[z7,z819,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z820]),(0,[z7,z22,z23,z47,z5,z6]),(0,[z821,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z35,z5,z442]),(0,[z0,z245,z3,z4,z101,z6])],[(0,[z1,z102,z3,z98,z5,z6]),(0,[z14,z1,z3,z87,z5,z6]),(0,[z7,z1,z3,z4,z5,z822]),(0,[z705,z7,z1,z4,z25,z6]),(0,[z7,z1,z3,z35,z5,z11]),(0,[z7,z1,z48,z4,z5,z110])],[(0,[z1,z70,z3,z20,z5,z6]),(0,[z7,z3,z4,z5,z6,z823]),(0,[z7,z1,z3,z464,z13,z4])],[(0,[z14,z409,z3,z4,z5,z6]),(0,[z7,z1,z4,z824,z5,z6])],[(0,[z166,z7,z44,z204,z5,z6]),(0,[z7,z1,z3,z47,z5,z228]),(0,[z1,z825,z3,z4,z5,z6])],[(0,[z1,z826,z3,z4,z5,z6]),(0,[z7,z1,z3,z827,z5,z6])]],
   [[(0,[z828,z7,z1,z3,z4,z6])],[(0,[z829,z1,z3,z4,z5,z6])],[(0,[z830,z14,z1,z3,z5,z6])],[(0,[z1,z2,z3,z4,z273,z6]),(0,[z200,z14,z1,z4,z5,z82]),(0,[z17,z7,z70,z3,z5,z6]),(0,[z221,z1,z3,z374,z5,z6]),(0,[z1,z3,z4,z501,z6,z232])],[(0,[z14,z1,z3,z169,z5,z6]),(0,[z7,z1,z3,z4,z831,z6]),(0,[z18,z318,z1,z3,z5,z6]),(0,[z7,z276,z1,z454,z5,z6])],[],[(0,[z1,z2,z3,z87,z5,z6]),(0,[z7,z1,z3,z4,z5,z832]),(0,[z7,z1,z833,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z834]),(0,[z7,z1,z3,z835,z5,z6]),(0,[z7,z1,z836,z4,z5,z6])],[(0,[z7,z1,z142,z47,z5,z143]),(0,[z245,z1,z3,z81,z5,z6])],[(0,[z7,z1,z3,z837,z5,z6]),(0,[z7,z59,z1,z299,z5,z6])],[(0,[z300,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z73]),(0,[z7,z1,z3,z209,z279,z6])],[(0,[z7,z838,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z5,z442]),(0,[z730,z1,z3,z35,z5,z6])],[(0,[z1,z57,z3,z434,z5,z6]),(0,[z7,z1,z839,z4,z5,z6])],[(0,[z2,z83,z3,z47,z5,z6]),(0,[z14,z1,z3,z4,z279,z6]),(0,[z7,z1,z3,z393,z5,z6])],[(0,[z445,z2,z3,z47,z5,z6]),(0,[z14,z1,z3,z209,z5,z6]),(0,[z7,z3,z793,z47,z5,z6]),(0,[z7,z1,z840,z3,z5,z6]),(0,[z841,z1,z3,z4,z5,z6])],[(0,[z1,z842,z3,z4,z5,z6])],[(0,[z67,z1,z83,z3,z5,z6])]],
   [[(0,[z843,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z306,z85]),(0,[z844,z1,z3,z4,z5,z6])],[(0,[z78,z1,z3,z4,z279,z6]),(0,[z412,z1,z3,z338,z5,z6])],[(0,[z845,z1,z3,z4,z5,z6]),(0,[z78,z1,z3,z209,z5,z6]),(0,[z846,z1,z3,z4,z5,z6])],[(0,[z14,z598,z3,z4,z5,z6]),(0,[z7,z1,z3,z847,z5,z6]),(0,[z848,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z849,z5,z6]),(0,[z7,z1,z3,z4,z5,z850]),(0,[z7,z162,z3,z4,z5,z823]),(0,[z318,z1,z378,z4,z5,z6])],[(0,[z7,z1,z3,z851,z5,z6]),(0,[z2,z3,z4,z282,z5,z6])],[(0,[z852,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z279,z6]),(0,[z203,z2,z3,z47,z5,z6]),(0,[z1,z3,z107,z43,z5,z6]),(0,[z1,z3,z4,z5,z6,z853])],[(0,[z1,z2,z3,z209,z5,z6]),(0,[z154,z14,z3,z4,z5,z110]),(0,[z17,z14,z1,z3,z6,z278]),(1,[z1,z3,z4,z353,z50])],[(0,[z7,z1,z3,z47,z5,z73]),(0,[z1,z263,z3,z35,z5,z6]),(0,[z7,z1,z3,z342,z5,z60])],[(0,[z7,z1,z3,z854,z5,z6])],[(0,[z7,z1,z48,z338,z5,z6]),(0,[z7,z1,z3,z855,z5,z6]),(0,[z856,z1,z3,z4,z5,z6])],[(0,[z2,z3,z4,z302,z5,z6]),(0,[z857,z7,z1,z3,z5,z6])],[(0,[z7,z61,z3,z47,z5,z6]),(0,[z14,z1,z378,z4,z5,z6]),(0,[z7,z1,z235,z4,z5,z6])],[(0,[z1,z3,z4,z5,z807,z6]),(0,[z7,z1,z3,z4,z5,z858]),(0,[z1,z859,z3,z4,z5,z6])],[(0,[z7,z275,z3,z4,z5,z6]),(0,[z34,z1,z83,z35,z5,z6]),(0,[z7,z1,z3,z4,z612,z232]),(1,[z7,z1,z3,z860,z5]),(0,[z7,z1,z75,z3,z860,z5])]],
   [[(0,[z756,z1,z3,z35,z5,z6])],[(0,[z14,z487,z3,z4,z5,z6])],[(0,[z861,z1,z3,z4,z5,z6]),(0,[z7,z1,z4,z862,z5,z6]),(0,[z7,z1,z3,z4,z167,z6])],[(0,[z412,z1,z3,z4,z5,z6]),(0,[z411,z2,z3,z47,z5,z6]),(0,[z14,z1,z3,z4,z105,z232]),(0,[z34,z1,z288,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z863]),(0,[z245,z1,z3,z128,z5,z6]),(0,[z1,z864,z3,z4,z5,z6])],[(0,[z865,z1,z2,z3,z4,z5])],[(0,[z866,z7,z1,z3,z5,z6])],[(0,[z7,z1,z3,z4,z5,z867]),(0,[z94,z1,z623,z4,z5,z6]),(0,[z1,z3,z4,z5,z138,z8]),(0,[z1,z57,z3,z35,z5,z6]),(0,[z868,z1,z3,z4,z5,z6]),(0,[z17,z300,z1,z3,z6,z278]),(0,[z7,z1,z3,z869,z5,z6])],[(0,[z1,z870,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z871,z6]),(0,[z7,z1,z3,z4,z872,z6])],[(0,[z594,z1,z3,z4,z226,z6]),(0,[z1,z2,z3,z5,z873,z6]),(0,[z1,z2,z378,z4,z5,z6]),(0,[z54,z1,z3,z4,z68,z442]),(0,[z7,z276,z1,z9,z5,z6])],[(0,[z14,z61,z3,z51,z5,z6]),(0,[z7,z1,z3,z874,z5,z6]),(0,[z1,z263,z3,z47,z5,z6]),(0,[z229,z7,z3,z47,z5,z6])],[(0,[z2,z3,z47,z5,z25,z6]),(0,[z7,z1,z3,z4,z5,z875]),(0,[z7,z1,z3,z876,z5,z6]),(0,[z7,z70,z3,z35,z5,z6]),(0,[z7,z1,z3,z434,z5,z6]),(0,[z7,z1,z3,z877,z5,z6]),(0,[z1,z878,z3,z4,z5,z6]),(0,[z7,z1,z3,z131,z5,z60])],[(0,[z200,z7,z1,z119,z5,z82])],[(0,[z488,z2,z3,z4,z5,z6]),(0,[z137,z2,z3,z47,z5,z6]),(0,[z1,z3,z4,z5,z879,z6]),(0,[z94,z67,z1,z3,z5,z6]),(0,[z880,z1,z3,z4,z5,z6]),(0,[z7,z22,z23,z35,z5,z6])],[(0,[z2,z3,z107,z47,z5,z6]),(0,[z14,z59,z1,z9,z5,z6]),(0,[z7,z217,z3,z4,z5,z85])],[(0,[z14,z1,z3,z92,z5,z6]),(0,[z1,z2,z3,z4,z105,z232])],[(0,[z881,z1,z3,z4,z5,z6]),(0,[z34,z1,z83,z47,z5,z6]),(0,[z7,z3,z35,z47,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z6]),(0,[z59,z1,z2,z9,z5,z6]),(0,[z70,z83,z3,z4,z5,z6])],[(0,[z1,z3,z35,z259,z5,z6])],[(0,[z14,z61,z3,z93,z5,z6]),(0,[z7,z882,z3,z5,z68,z6]),(0,[z7,z1,z3,z883,z5,z6])],[(0,[z55,z1,z3,z4,z5,z121]),(0,[z7,z46,z3,z884,z5,z6]),(0,[z7,z1,z3,z459,z5,z603])],[(0,[z7,z769,z3,z4,z5,z6]),(0,[z885,z1,z3,z4,z5,z6])],[(0,[z46,z2,z3,z4,z5,z6]),(0,[z2,z3,z47,z5,z6,z232]),(0,[z2,z3,z374,z47,z5,z6]),(0,[z390,z7,z3,z4,z101,z6]),(0,[z7,z1,z3,z4,z5,z479])],[(0,[z503,z2,z3,z4,z5,z6]),(0,[z1,z57,z3,z47,z5,z6]),(0,[z7,z153,z3,z4,z5,z73])],[(0,[z7,z1,z3,z886,z5,z6]),(0,[z845,z1,z3,z47,z5,z6]),(0,[z887,z1,z3,z4,z5,z6])],[(0,[z67,z1,z3,z20,z5,z6]),(0,[z86,z476,z3,z4,z24,z6]),(0,[z7,z1,z3,z888,z5,z6]),(0,[z7,z1,z3,z28,z5,z492])],[(0,[z525,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z92,z5,z6]),(0,[z1,z889,z3,z4,z5,z6]),(0,[z7,z1,z890,z4,z5,z6]),(0,[z7,z1,z3,z40,z13,z4])],[(0,[z53,z769,z3,z4,z5,z6]),(0,[z548,z7,z3,z47,z5,z6]),(0,[z7,z1,z142,z35,z5,z143]),(0,[z891,z1,z3,z4,z5,z6])],[(0,[z7,z3,z469,z35,z5,z6])],[(0,[z626,z2,z3,z47,z5,z6]),(0,[z1,z2,z4,z5,z6,z892]),(0,[z221,z70,z3,z4,z5,z6]),(0,[z1,z893,z3,z4,z5,z6]),(0,[z7,z1,z894,z4,z5,z6])],[(0,[z1,z83,z4,z5,z6,z109]),(0,[z166,z7,z44,z4,z5,z21]),(0,[z7,z1,z3,z895,z4,z5]),(0,[z104,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z896,z5,z6])],[(0,[z7,z1,z3,z5,z164,z6]),(0,[z154,z7,z3,z338,z5,z110]),(0,[z200,z291,z1,z4,z5,z82])],[(0,[z7,z1,z3,z4,z5,z897]),(0,[z7,z1,z3,z4,z898,z6]),(0,[z7,z1,z899,z4,z5,z6]),(0,[z7,z1,z149,z4,z25,z6]),(0,[z7,z1,z3,z900,z5,z6])]],
   [[(0,[z1,z83,z3,z4,z353,z6]),(0,[z901,z1,z3,z4,z5,z6]),(0,[z17,z318,z1,z3,z6,z278]),(0,[z902,z1,z3,z4,z5,z6])],[(0,[z0,z7,z234,z4,z101,z6])],[(0,[z7,z1,z3,z4,z903,z5]),(0,[z14,z1,z3,z4,z5,z388]),(0,[z7,z1,z235,z47,z5,z6]),(0,[z7,z1,z171,z5,z6,z82]),(0,[z904,z1,z3,z4,z5,z6])],[(0,[z1,z790,z99,z4,z5,z6]),(0,[z116,z3,z4,z47,z5,z6]),(0,[z905,z1,z3,z4,z5,z6]),(0,[z505,z7,z1,z4,z25,z6])],[(0,[z575,z1,z3,z4,z145,z6]),(0,[z54,z1,z3,z4,z807,z6]),(0,[z7,z1,z3,z4,z24,z388]),(0,[z7,z906,z3,z4,z5,z6])],[(0,[z7,z907,z3,z4,z5,z6]),(0,[z908,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z490,z232])],[(0,[z7,z909,z3,z4,z5,z6]),(0,[z55,z1,z3,z4,z5,z910]),(0,[z7,z1,z3,z911,z5,z6]),(0,[z7,z162,z3,z4,z5,z85]),(0,[z1,z912,z3,z4,z5,z6]),(0,[z7,z1,z3,z76,z5,z60])],[(0,[z18,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z913,z5,z6]),(0,[z7,z1,z3,z914,z4,z5]),(0,[z7,z1,z3,z915,z5,z6]),(0,[z7,z1,z3,z47,z167,z6]),(0,[z916,z1,z3,z4,z5,z6]),(0,[z7,z1,z28,z5,z60,z82])],[(0,[z7,z1,z3,z4,z63,z232]),(0,[z7,z86,z3,z4,z784,z6]),(0,[z7,z1,z3,z4,z5,z823])],[(0,[z1,z3,z4,z5,z917,z6]),(0,[z918,z1,z3,z4,z5,z6]),(0,[z919,z1,z3,z4,z5,z6]),(0,[z1,z920,z3,z4,z5,z6]),(0,[z1,z921,z3,z4,z5,z6])],[(0,[z94,z1,z699,z4,z5,z6]),(0,[z7,z1,z3,z922,z5,z6])],[(0,[z7,z1,z3,z923,z5,z6])],[(0,[z7,z1,z3,z924,z5,z6]),(0,[z925,z1,z3,z4,z5,z6]),(0,[z7,z3,z47,z152,z101,z6])],[(0,[z246,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z388]),(0,[z7,z1,z3,z4,z926,z6]),(0,[z7,z1,z3,z4,z5,z190]),(0,[z7,z1,z3,z348,z167,z6]),(0,[z7,z3,z819,z4,z5,z6]),(0,[z795,z1,z3,z47,z5,z6]),(0,[z104,z1,z3,z47,z5,z6])],[(0,[z2,z3,z4,z441,z5,z6]),(0,[z2,z3,z4,z5,z6,z444]),(0,[z7,z1,z3,z4,z807,z6]),(0,[z7,z46,z3,z87,z5,z6]),(0,[z7,z1,z3,z4,z5,z927])],[(0,[z2,z3,z124,z47,z5,z6]),(0,[z149,z2,z3,z4,z5,z6]),(0,[z865,z7,z1,z3,z4,z5]),(0,[z7,z476,z3,z47,z5,z6])]],
   [[(0,[z144,z1,z3,z20,z5,z6]),(0,[z7,z478,z3,z47,z5,z6]),(0,[z411,z7,z3,z47,z101,z6]),(0,[z245,z1,z235,z4,z5,z6]),(0,[z154,z7,z3,z4,z5,z110]),(0,[z7,z225,z3,z4,z5,z73])],[],[(0,[z14,z591,z3,z4,z5,z6]),(0,[z7,z367,z1,z370,z5,z6]),(0,[z7,z1,z928,z4,z5,z6]),(1,[z7,z3,z4,z784,z6])],[(0,[z200,z1,z2,z4,z5,z82]),(0,[z1,z929,z3,z4,z5,z6]),(0,[z930,z1,z3,z4,z5,z6]),(0,[z7,z1,z4,z5,z720,z82]),(0,[z7,z1,z3,z6,z931,z278])],[(0,[z0,z7,z3,z4,z101,z388]),(0,[z7,z1,z159,z4,z5,z82])],[(0,[z7,z1,z3,z47,z5,z6]),(0,[z166,z2,z3,z47,z5,z6]),(0,[z7,z1,z4,z5,z932,z6]),(0,[z7,z1,z3,z933,z5,z6]),(0,[z934,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z935])],[(0,[z7,z61,z3,z169,z5,z6]),(0,[z7,z1,z3,z4,z936,z6]),(0,[z246,z86,z3,z4,z24,z6])],[(0,[z19,z318,z1,z3,z5,z6]),(0,[z7,z86,z3,z4,z458,z6]),(0,[z7,z1,z10,z835,z5,z6])],[],[(0,[z2,z3,z469,z4,z5,z6]),(0,[z2,z3,z47,z5,z6,z50]),(0,[z7,z1,z10,z345,z5,z6]),(0,[z7,z1,z3,z9,z5,z492]),(0,[z7,z1,z131,z4,z5,z82])],[(0,[z504,z2,z3,z47,z5,z6]),(0,[z601,z1,z3,z4,z5,z50]),(0,[z7,z1,z3,z5,z937,z6]),(0,[z166,z7,z44,z4,z273,z6])],[(0,[z7,z1,z3,z348,z5,z6]),(0,[z7,z1,z3,z204,z167,z6])],[(0,[z14,z86,z3,z47,z5,z6]),(0,[z938,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z726,z6])],[(0,[z470,z7,z1,z4,z5,z82]),(0,[z7,z1,z3,z124,z41,z5]),(0,[z7,z1,z234,z81,z5,z6])],[(0,[z7,z1,z3,z793,z5,z6]),(0,[z203,z1,z3,z4,z315,z6]),(0,[z7,z86,z3,z47,z24,z6])],[(0,[z94,z1,z99,z4,z5,z6]),(0,[z7,z939,z3,z4,z5,z6]),(0,[z7,z1,z23,z4,z5,z21]),(0,[z1,z3,z4,z5,z6,z940])]],
   [[(0,[z7,z1,z3,z941,z5,z6]),(0,[z127,z1,z3,z4,z167,z6]),(0,[z7,z1,z3,z942,z5,z6])],[(0,[z7,z1,z3,z4,z5,z943]),(0,[z7,z1,z944,z4,z5,z6]),(0,[z300,z1,z3,z35,z5,z6]),(0,[z7,z1,z945,z4,z5,z6]),(0,[z946,z1,z3,z4,z5,z6])],[(0,[z7,z1,z44,z4,z5,z21]),(0,[z7,z1,z234,z4,z5,z228]),(0,[z947,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z948,z5,z6]),(0,[z200,z7,z1,z171,z5,z82])],[(0,[z245,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z949,z5,z6]),(0,[z7,z1,z950,z4,z5,z6]),(0,[z412,z1,z48,z4,z5,z6]),(0,[z951,z1,z3,z4,z5,z6])],[(0,[z7,z618,z23,z4,z5,z6]),(0,[z257,z1,z3,z81,z5,z6])],[(0,[z7,z1,z3,z4,z5,z910]),(0,[z7,z86,z3,z81,z5,z6]),(0,[z300,z225,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z952]),(0,[z7,z1,z3,z4,z5,z953]),(0,[z1,z3,z4,z954,z5,z6])],[],[(0,[z2,z3,z220,z47,z5,z6]),(0,[z17,z1,z2,z3,z6,z278]),(0,[z14,z1,z3,z4,z955,z6]),(0,[z956,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z607,z5,z60])],[(0,[z331,z1,z3,z4,z5,z121]),(0,[z7,z1,z882,z3,z5,z6]),(0,[z137,z1,z3,z4,z5,z138]),(0,[z7,z1,z3,z204,z5,z6]),(0,[z257,z1,z3,z4,z5,z228]),(0,[z957,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z958]),(0,[z7,z1,z3,z4,z5,z959]),(0,[z377,z1,z3,z20,z5,z6]),(0,[z960,z1,z3,z4,z5,z6])],[(0,[z1,z3,z35,z5,z6,z172]),(0,[z7,z1,z76,z178,z5,z60])],[(0,[z7,z1,z3,z4,z167,z420]),(0,[z7,z1,z3,z4,z5,z961]),(0,[z7,z1,z3,z962,z5,z6])],[(0,[z14,z637,z3,z4,z5,z6]),(0,[z18,z1,z3,z302,z5,z6]),(0,[z7,z963,z3,z4,z5,z6])],[(0,[z127,z1,z3,z4,z5,z6]),(0,[z1,z964,z3,z4,z5,z6]),(0,[z1,z3,z47,z5,z6,z172]),(0,[z1,z263,z3,z118,z5,z6])],[(0,[z7,z1,z3,z4,z965,z6]),(0,[z7,z1,z3,z4,z5,z966]),(0,[z7,z1,z142,z4,z5,z536])]],
   [[(0,[z2,z3,z47,z152,z5,z6]),(0,[z967,z1,z2,z4,z5,z6]),(0,[z55,z1,z3,z4,z5,z524]),(0,[z7,z1,z48,z4,z5,z6]),(0,[z7,z1,z3,z209,z306,z6])],[(0,[z7,z1,z3,z4,z968,z6]),(0,[z7,z1,z3,z969,z5,z6]),(0,[z300,z1,z3,z47,z5,z6]),(0,[z7,z1,z305,z338,z5,z6]),(0,[z7,z1,z3,z970,z5,z6])],[(0,[z7,z153,z3,z4,z5,z6])],[(0,[z2,z3,z47,z105,z5,z6]),(0,[z59,z2,z3,z47,z5,z6]),(0,[z14,z1,z3,z4,z306,z6])],[(0,[z2,z3,z4,z519,z5,z6])],[(1,[z769,z3,z4,z5,z6]),(0,[z154,z2,z3,z4,z5,z110]),(0,[z1,z2,z3,z93,z5,z6]),(0,[z7,z1,z3,z4,z5,z971]),(0,[z7,z1,z235,z35,z5,z6])],[(0,[z201,z2,z3,z47,z5,z6]),(0,[z284,z1,z3,z4,z328,z6]),(0,[z1,z3,z4,z105,z501,z232])],[(0,[z7,z275,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z6,z931])],[(0,[z7,z1,z3,z4,z972,z6]),(0,[z7,z1,z3,z4,z973,z6]),(0,[z78,z1,z3,z4,z306,z6]),(0,[z974,z1,z3,z4,z5,z6]),(0,[z1,z3,z13,z4,z501,z5])],[(0,[z2,z3,z47,z429,z5,z6]),(0,[z14,z375,z3,z4,z5,z6]),(0,[z7,z1,z234,z128,z5,z6])],[(0,[z2,z3,z4,z5,z534,z6]),(0,[z7,z1,z3,z4,z5,z420]),(0,[z7,z1,z3,z35,z167,z6]),(0,[z7,z1,z3,z47,z5,z935]),(0,[z7,z1,z3,z4,z5,z975]),(0,[z7,z1,z178,z5,z6,z60])],[(0,[z412,z1,z3,z35,z5,z6]),(0,[z7,z1,z35,z178,z5,z6]),(0,[z7,z1,z159,z28,z5,z6])],[(0,[z1,z976,z3,z4,z5,z6]),(0,[z7,z1,z23,z4,z273,z6])],[(0,[z2,z3,z20,z47,z5,z6]),(0,[z830,z7,z1,z3,z5,z6]),(0,[z7,z23,z819,z4,z5,z6]),(0,[z7,z1,z10,z28,z5,z6]),(0,[z7,z1,z3,z977,z5,z6])],[(0,[z1,z2,z3,z4,z306,z6]),(0,[z978,z1,z3,z4,z5,z6]),(0,[z200,z7,z1,z4,z5,z82])],[(0,[z7,z1,z3,z979,z5,z6]),(0,[z1,z157,z3,z4,z5,z6]),(0,[z221,z1,z3,z107,z5,z6]),(0,[z7,z1,z3,z980,z5,z6]),(0,[z7,z1,z44,z4,z273,z6]),(0,[z7,z1,z3,z4,z5,z492])]],
   [[(0,[z981,z1,z3,z4,z5,z6]),(0,[z14,z1,z4,z178,z5,z6]),(0,[z257,z1,z3,z128,z5,z6]),(0,[z982,z1,z3,z4,z5,z6])],[(0,[z7,z1,z983,z4,z5,z6]),(0,[z7,z673,z3,z47,z5,z6])],[(0,[z2,z10,z3,z47,z5,z6]),(0,[z984,z1,z3,z4,z5,z6]),(0,[z1,z3,z382,z4,z5,z261])],[(0,[z61,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z985]),(0,[z7,z1,z3,z4,z353,z6]),(0,[z7,z1,z305,z4,z5,z6]),(0,[z7,z1,z4,z986,z25,z6])],[(0,[z7,z3,z47,z5,z226,z6]),(0,[z7,z1,z3,z4,z5,z987])],[],[(0,[z14,z1,z3,z4,z5,z228]),(0,[z7,z1,z3,z988,z5,z6]),(0,[z7,z1,z3,z4,z989,z6]),(0,[z139,z22,z23,z4,z5,z6]),(0,[z7,z1,z3,z4,z610,z232])],[(0,[z1,z2,z3,z4,z5,z710]),(0,[z7,z1,z3,z4,z5,z990]),(0,[z7,z275,z3,z47,z5,z6]),(0,[z7,z1,z3,z5,z991,z6]),(0,[z7,z1,z3,z4,z101,z479]),(0,[z7,z1,z3,z5,z992,z6])],[(0,[z7,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z76,z5,z603])],[],[(0,[z19,z1,z3,z339,z5,z6]),(0,[z1,z3,z4,z353,z6,z50])],[(0,[z1,z2,z4,z178,z5,z6]),(0,[z7,z1,z993,z4,z5,z6]),(0,[z412,z1,z3,z47,z5,z6]),(0,[z881,z225,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z994,z6]),(0,[z7,z995,z3,z4,z5,z6]),(0,[z7,z225,z3,z4,z5,z6])],[(0,[z46,z2,z3,z35,z5,z6]),(0,[z680,z2,z3,z4,z5,z6])],[(0,[z300,z153,z3,z4,z5,z6])],[(1,[z1,z3,z4,z807,z6]),(0,[z7,z553,z3,z4,z5,z85]),(0,[z7,z1,z3,z996,z5,z6])]],
   [[(0,[z7,z281,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z77,z6]),(1,[z476,z3,z47,z5,z6]),(0,[z154,z7,z48,z4,z5,z110]),(0,[z7,z1,z3,z4,z5,z74])],[(0,[z2,z3,z47,z5,z6,z482]),(0,[z162,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z228]),(0,[z525,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z382,z35,z5]),(0,[z153,z997,z3,z4,z5,z6]),(0,[z7,z1,z4,z998,z5,z6])],[(0,[z14,z1,z3,z4,z5,z442]),(0,[z7,z1,z3,z4,z999,z6]),(0,[z7,z1,z3,z1000,z5,z6])],[(0,[z2,z3,z47,z5,z6,z278]),(0,[z14,z1,z3,z4,z5,z11]),(0,[z7,z1,z3,z1001,z5,z6]),(0,[z1002,z1,z3,z4,z5,z6]),(0,[z17,z7,z1,z3,z6,z278]),(0,[z1003,z1,z3,z4,z5,z6])],[(0,[z7,z1,z1004,z4,z5,z6]),(0,[z7,z3,z47,z5,z596,z6]),(0,[z7,z1,z894,z35,z5,z6]),(0,[z7,z1,z4,z5,z143,z720])],[(0,[z852,z2,z3,z4,z5,z6]),(0,[z7,z70,z3,z115,z5,z6]),(0,[z1,z3,z4,z5,z6,z910]),(0,[z7,z1,z48,z47,z5,z6])],[(0,[z7,z1,z3,z1005,z5,z6]),(0,[z2,z3,z76,z47,z5,z6]),(0,[z7,z1,z1006,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1007]),(0,[z7,z1,z3,z13,z171,z5])],[(0,[z7,z1,z3,z1008,z5,z6])],[(0,[z7,z1,z3,z4,z1009,z6]),(0,[z318,z1,z3,z4,z5,z73]),(0,[z848,z153,z3,z4,z5,z6])],[(0,[z127,z1,z3,z348,z5,z6]),(1,[z7,z1,z171,z5,z82])],[(0,[z19,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z167,z21]),(0,[z7,z1,z3,z118,z5,z6])],[(0,[z14,z1,z3,z313,z5,z6]),(0,[z18,z1,z3,z432,z5,z6]),(0,[z1010,z1,z3,z4,z5,z6])],[(0,[z316,z61,z3,z4,z5,z6]),(0,[z7,z225,z3,z5,z6,z278])],[(0,[z46,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z5,z442]),(0,[z7,z1,z3,z4,z5,z1011]),(0,[z7,z1,z3,z1012,z5,z6]),(0,[z7,z1,z3,z47,z5,z479]),(0,[z1013,z1,z3,z4,z5,z6])],[(0,[z52,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z11]),(0,[z14,z96,z3,z4,z5,z6]),(0,[z7,z1014,z3,z4,z5,z6]),(0,[z7,z1,z35,z1015,z5,z6]),(0,[z7,z162,z3,z35,z5,z85])],[(0,[z139,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1016,z5,z6]),(0,[z7,z1,z3,z47,z5,z420]),(0,[z7,z1,z3,z1017,z5,z6])]],
   [[(0,[z7,z1,z3,z40,z13,z47])],[(0,[z1,z2,z3,z4,z5,z1018]),(0,[z7,z3,z93,z47,z5,z6]),(0,[z1,z1019,z3,z4,z5,z6]),(0,[z525,z1,z3,z47,z5,z6]),(0,[z7,z1,z3,z1020,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1021]),(0,[z7,z1,z1022,z4,z5,z6])],[(0,[z1023,z1,z3,z4,z5,z6]),(0,[z200,z7,z1,z47,z5,z82]),(0,[z1,z1024,z3,z4,z5,z6])],[(0,[z2,z3,z47,z5,z143,z6]),(0,[z14,z1,z3,z51,z5,z6]),(0,[z7,z1,z3,z47,z5,z492])],[(0,[z14,z61,z3,z4,z5,z6]),(0,[z2,z3,z35,z47,z5,z6]),(0,[z79,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z190]),(0,[z7,z1,z3,z348,z5,z420]),(0,[z7,z1,z1025,z4,z5,z6]),(0,[z246,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z5,z1026,z6]),(0,[z198,z7,z1,z4,z5,z82])],[(0,[z1,z2,z3,z313,z5,z6]),(0,[z1,z476,z3,z4,z5,z6]),(0,[z344,z14,z3,z47,z5,z6]),(1,[z1,z3,z4,z5,z910]),(0,[z7,z1,z3,z1027,z5,z6]),(0,[z486,z7,z44,z4,z5,z6]),(0,[z7,z1,z577,z3,z41,z5]),(0,[z1028,z1,z3,z4,z5,z6])],[],[(0,[z2,z3,z47,z47,z5,z6]),(0,[z7,z1,z3,z4,z715,z5]),(0,[z7,z1,z3,z47,z353,z6]),(0,[z223,z1,z3,z4,z167,z6]),(0,[z154,z7,z3,z35,z5,z110]),(0,[z188,z1,z3,z313,z5,z6])],[(0,[z2,z142,z3,z47,z5,z6]),(0,[z7,z3,z386,z47,z5,z6]),(0,[z7,z1,z363,z4,z5,z73])],[(0,[z7,z1,z928,z35,z5,z6]),(0,[z0,z7,z3,z4,z784,z6]),(0,[z1029,z1,z3,z4,z5,z6])],[(0,[z539,z1,z3,z4,z5,z114])],[(0,[z2,z3,z4,z5,z633,z6]),(0,[z7,z1,z3,z4,z5,z1030]),(0,[z300,z1,z3,z4,z5,z74])],[(0,[z14,z1,z3,z93,z5,z6]),(0,[z14,z106,z3,z4,z5,z6]),(0,[z7,z1,z1031,z4,z5,z6]),(0,[z7,z1,z3,z884,z5,z6]),(0,[z1032,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z1033,z5,z6]),(0,[z1,z2,z4,z1015,z5,z6]),(0,[z1,z3,z790,z4,z5,z6]),(0,[z544,z1,z3,z4,z68,z6]),(0,[z7,z162,z3,z47,z5,z85]),(0,[z7,z1,z378,z4,z5,z73])],[(0,[z2,z423,z3,z47,z5,z6]),(0,[z1,z2,z3,z51,z5,z6]),(0,[z7,z1,z3,z860,z5,z60])]],
   [[(0,[z1,z769,z3,z4,z5,z6]),(0,[z7,z1,z28,z5,z6,z492]),(0,[z7,z1,z3,z860,z5,z6])],[(0,[z1,z102,z3,z107,z5,z6]),(0,[z1034,z1,z3,z4,z5,z6]),(0,[z7,z681,z3,z47,z5,z6])],[(0,[z1,z3,z4,z63,z68,z6]),(0,[z316,z46,z3,z35,z5,z6]),(0,[z7,z1,z3,z1035,z5,z6])],[(0,[z7,z1,z3,z204,z5,z420]),(0,[z7,z1,z3,z81,z5,z388]),(0,[z1036,z1,z3,z4,z5,z6]),(0,[z1,z1037,z3,z4,z5,z6])],[(0,[z1,z1038,z3,z4,z5,z6]),(0,[z94,z70,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z261,z6]),(0,[z691,z1,z3,z4,z5,z138]),(0,[z7,z1,z3,z4,z5,z1039]),(0,[z1040,z1,z3,z4,z5,z6])],[(0,[z53,z2,z3,z4,z5,z6]),(0,[z55,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z47,z5,z190]),(0,[z7,z1,z3,z1041,z5,z6]),(0,[z116,z46,z3,z4,z5,z6]),(0,[z246,z1,z3,z47,z5,z6]),(0,[z1042,z1,z3,z4,z5,z6])],[(0,[z162,z2,z3,z4,z5,z85]),(0,[z223,z1,z3,z4,z5,z6]),(0,[z14,z431,z3,z4,z5,z6]),(0,[z54,z1,z3,z4,z68,z6]),(0,[z1,z3,z4,z501,z5,z6]),(0,[z1043,z1,z3,z4,z5,z6]),(0,[z606,z7,z1,z4,z5,z82]),(0,[z7,z1,z3,z4,z5,z720])],[(0,[z2,z3,z47,z5,z226,z6]),(0,[z94,z1,z99,z35,z5,z6]),(0,[z7,z3,z49,z35,z5,z6])],[(0,[z367,z2,z3,z47,z5,z6]),(0,[z127,z1,z3,z4,z5,z420]),(0,[z154,z7,z3,z47,z5,z110])],[(0,[z33,z1,z3,z302,z5,z6]),(0,[z412,z1,z305,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1044])],[(0,[z7,z86,z3,z211,z24,z6]),(0,[z486,z7,z3,z4,z5,z110])],[(0,[z1,z538,z3,z4,z5,z546]),(0,[z7,z1,z1045,z4,z5,z6]),(0,[z245,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z76,z860,z5])],[(0,[z7,z1,z3,z1046,z5,z6]),(0,[z7,z3,z47,z5,z6,z660]),(0,[z7,z253,z1,z9,z5,z6])],[(0,[z7,z1,z790,z4,z5,z6]),(0,[z1,z83,z790,z4,z5,z6]),(0,[z7,z3,z47,z5,z664,z6])],[(0,[z7,z70,z3,z98,z5,z6]),(0,[z139,z1,z3,z393,z5,z6]),(0,[z7,z1,z3,z171,z5,z232])],[(0,[z7,z1,z3,z4,z5,z1047]),(0,[z7,z1048,z3,z4,z5,z6]),(0,[z714,z1,z4,z178,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z1049,z6]),(0,[z7,z1050,z3,z4,z5,z6]),(0,[z7,z1,z3,z1051,z5,z6])],[(0,[z137,z1,z3,z35,z5,z138]),(0,[z7,z1,z3,z1052,z5,z6])],[(0,[z199,z2,z3,z4,z5,z6]),(0,[z14,z70,z3,z4,z5,z6]),(0,[z1,z3,z708,z20,z5,z6])],[(0,[z67,z14,z1,z3,z5,z6]),(0,[z7,z1,z3,z1053,z5,z6])],[(0,[z14,z22,z23,z4,z5,z6]),(0,[z14,z1,z3,z81,z5,z6]),(0,[z7,z1,z3,z4,z5,z733]),(0,[z7,z1,z3,z1054,z5,z6]),(0,[z7,z3,z47,z5,z101,z6]),(0,[z1,z3,z4,z724,z5,z6]),(0,[z1055,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1056,z5,z6])],[(0,[z7,z1,z1057,z4,z5,z6]),(0,[z18,z1,z3,z519,z5,z6]),(0,[z551,z7,z3,z47,z5,z6]),(0,[z7,z1,z3,z171,z5,z143]),(1,[z7,z1,z178,z5,z60])],[(0,[z1,z3,z4,z1058,z5,z6])],[(0,[z7,z1,z3,z1059,z5,z6]),(0,[z94,z1,z99,z47,z5,z6]),(0,[z7,z1,z3,z1060,z5,z6]),(0,[z7,z3,z140,z47,z101,z6]),(0,[z7,z1,z3,z338,z279,z6])],[(0,[z1061,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z1062,z6]),(0,[z7,z1,z3,z87,z5,z6]),(0,[z7,z1,z48,z35,z5,z6]),(0,[z7,z3,z4,z5,z784,z6])],[(0,[z578,z7,z3,z47,z5,z6]),(0,[z7,z430,z3,z4,z24,z6])],[(0,[z54,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z1063,z6]),(0,[z7,z1,z1064,z4,z5,z6]),(0,[z7,z3,z35,z884,z5,z6]),(0,[z7,z153,z3,z35,z5,z6])],[(0,[z7,z1,z3,z4,z751,z6]),(0,[z291,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1065,z5,z6]),(0,[z245,z1,z3,z47,z5,z6]),(0,[z1,z476,z3,z47,z5,z6]),(0,[z7,z1,z1066,z4,z5,z6])],[(0,[z7,z1,z3,z1067,z47,z5]),(0,[z7,z1,z10,z28,z5,z492])],[(0,[z14,z1,z3,z119,z5,z6]),(0,[z7,z1,z3,z1068,z5,z6]),(0,[z7,z1,z3,z1069,z5,z6]),(0,[z7,z3,z35,z282,z5,z6])],[(0,[z19,z1,z3,z5,z346,z6]),(0,[z0,z257,z3,z4,z101,z6])],[(0,[z1,z2,z3,z81,z5,z6]),(0,[z1,z3,z4,z644,z68,z6]),(0,[z7,z1,z3,z128,z5,z388])]],
   [[(0,[z7,z1,z3,z35,z5,z479]),(0,[z1070,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z726,z105])],[(0,[z7,z1,z3,z169,z5,z6]),(0,[z137,z1,z3,z47,z5,z138]),(0,[z7,z86,z3,z87,z24,z6])],[(0,[z14,z1,z142,z4,z5,z143]),(0,[z7,z1,z3,z5,z1071,z6]),(0,[z7,z1,z3,z35,z5,z420]),(0,[z7,z1,z3,z35,z5,z975]),(0,[z7,z1,z3,z4,z5,z1072]),(0,[z7,z1,z142,z171,z5,z6])],[(0,[z153,z2,z3,z4,z5,z6]),(0,[z54,z1,z3,z4,z68,z190]),(0,[z7,z1,z835,z28,z5,z6]),(0,[z7,z1,z1073,z4,z5,z6])],[(0,[z7,z2,z3,z47,z5,z6]),(0,[z1,z3,z4,z5,z6,z1074])],[(0,[z2,z3,z49,z4,z5,z6]),(0,[z18,z1,z3,z512,z5,z6]),(0,[z113,z1,z288,z4,z5,z6])],[(0,[z127,z1,z3,z47,z5,z6]),(0,[z200,z7,z1,z35,z5,z82]),(0,[z0,z7,z3,z81,z101,z6]),(0,[z1,z1075,z3,z4,z5,z6])],[(0,[z2,z3,z47,z41,z5,z6]),(0,[z1,z157,z3,z35,z5,z6]),(0,[z7,z1,z3,z35,z5,z492]),(0,[z7,z1,z835,z4,z5,z6]),(0,[z7,z1,z3,z4,z986,z6])],[(0,[z151,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z119,z5,z6]),(0,[z1076,z1,z3,z4,z5,z6]),(0,[z7,z1,z39,z4,z410,z6]),(0,[z7,z1,z3,z1077,z5,z6]),(0,[z7,z1078,z3,z4,z5,z6]),(0,[z1079,z1,z3,z4,z5,z6])],[(0,[z7,z122,z3,z47,z5,z6]),(0,[z7,z3,z47,z5,z6,z71]),(0,[z317,z1,z3,z98,z5,z6])],[(0,[z7,z153,z3,z47,z5,z6]),(0,[z7,z1,z3,z209,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1080]),(0,[z7,z1,z3,z35,z353,z6]),(0,[z7,z1,z305,z35,z5,z6]),(0,[z0,z7,z3,z4,z101,z228])],[(0,[z139,z1,z3,z434,z5,z6]),(0,[z1,z1081,z3,z4,z5,z6]),(0,[z654,z7,z3,z47,z5,z6]),(0,[z1,z3,z4,z5,z1082,z6]),(0,[z7,z1,z3,z507,z13,z4]),(0,[z7,z1,z3,z5,z6,z931])],[(0,[z7,z1,z1083,z4,z5,z6]),(0,[z1,z2,z142,z4,z5,z143]),(0,[z7,z1,z3,z4,z68,z190]),(0,[z7,z1,z258,z4,z152,z6]),(0,[z154,z7,z3,z4,z5,z823])],[(0,[z200,z2,z3,z47,z5,z6])],[(0,[z166,z223,z44,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z1084,z5,z6]),(0,[z14,z1,z3,z128,z5,z6]),(0,[z7,z1,z1085,z4,z5,z6])],[(0,[z2,z3,z47,z5,z85,z6]),(0,[z223,z1,z3,z348,z5,z6]),(0,[z7,z1,z1086,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1087]),(0,[z1,z1088,z3,z4,z5,z6])],[(0,[z7,z1,z1089,z4,z5,z6]),(0,[z7,z1,z3,z1090,z5,z6])],[(0,[z14,z1,z3,z4,z5,z73]),(0,[z94,z1,z493,z4,z5,z6]),(0,[z7,z225,z3,z35,z5,z6]),(0,[z7,z3,z4,z24,z784,z6])],[(0,[z1,z3,z4,z5,z138,z910]),(0,[z7,z1,z3,z1091,z5,z6]),(0,[z7,z1,z363,z4,z5,z6]),(0,[z1092,z1,z3,z4,z5,z6])],[(0,[z154,z7,z305,z4,z5,z110]),(0,[z7,z1,z3,z4,z5,z1093])],[(0,[z1,z157,z3,z47,z5,z6]),(0,[z7,z473,z3,z47,z5,z6]),(0,[z33,z1,z3,z432,z5,z6]),(0,[z7,z1,z3,z4,z860,z5])],[(0,[z510,z2,z3,z4,z5,z6]),(0,[z7,z1094,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z74]),(0,[z1,z1095,z3,z4,z5,z6])],[(0,[z594,z1,z3,z4,z68,z6]),(0,[z1,z538,z3,z4,z5,z138]),(0,[z1,z3,z4,z239,z807,z6]),(0,[z7,z1096,z3,z4,z5,z6]),(0,[z1,z997,z3,z4,z5,z6])],[(0,[z127,z1,z3,z204,z5,z6]),(0,[z7,z1,z3,z4,z560,z232]),(0,[z7,z1,z3,z1097,z4,z5]),(0,[z7,z225,z3,z248,z5,z6])],[(0,[z1,z2,z3,z128,z5,z6]),(0,[z2,z3,z136,z4,z5,z6]),(0,[z1,z3,z4,z708,z5,z6]),(0,[z67,z318,z1,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z21]),(0,[z7,z1,z305,z47,z5,z6]),(0,[z7,z193,z3,z47,z5,z6]),(0,[z7,z1,z3,z1098,z5,z6]),(0,[z7,z1099,z3,z4,z5,z6])],[(0,[z7,z1,z31,z4,z5,z6]),(0,[z1100,z1,z3,z4,z5,z6]),(0,[z7,z225,z3,z4,z5,z74])],[(0,[z1,z1101,z3,z4,z5,z6]),(0,[z7,z1,z3,z799,z4,z5]),(0,[z1102,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1103])],[],[(0,[z1,z2,z3,z4,z5,z73]),(0,[z7,z1,z3,z4,z1104,z6]),(0,[z7,z1,z3,z4,z1105,z6]),(0,[z203,z1,z3,z4,z286,z6])]],
   [[(0,[z7,z1,z3,z4,z804,z6]),(0,[z1,z3,z4,z5,z68,z190]),(0,[z7,z1,z3,z1106,z5,z6]),(0,[z7,z1,z3,z220,z5,z60]),(0,[z257,z1,z235,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1107])],[(0,[z19,z1,z3,z441,z5,z6]),(0,[z7,z1,z100,z3,z117,z5]),(0,[z0,z7,z3,z128,z101,z6]),(0,[z7,z1,z3,z1108,z5,z6]),(0,[z7,z1,z3,z13,z4,z726])],[(0,[z18,z70,z3,z20,z5,z6]),(0,[z18,z1,z3,z708,z5,z6]),(0,[z7,z162,z3,z118,z5,z85]),(0,[z7,z1109,z3,z4,z5,z6]),(0,[z1,z3,z4,z1110,z5,z6])],[(0,[z7,z1,z3,z806,z4,z5]),(0,[z14,z1,z3,z4,z831,z6]),(0,[z7,z1,z3,z4,z1111,z6]),(0,[z7,z225,z3,z47,z5,z6]),(0,[z7,z1,z3,z211,z5,z6]),(0,[z1112,z1,z3,z4,z5,z6]),(0,[z1113,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1114]),(0,[z7,z967,z1,z4,z5,z6])],[(0,[z601,z1,z3,z4,z5,z240]),(0,[z7,z59,z1,z835,z5,z6]),(0,[z1115,z1,z3,z4,z5,z6])],[(0,[z7,z1116,z3,z4,z5,z6]),(0,[z137,z1,z3,z4,z5,z676]),(0,[z139,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z1117,z5,z6]),(0,[z327,z7,z1,z3,z6,z71])],[(0,[z357,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1118]),(0,[z7,z1119,z3,z4,z5,z6]),(0,[z7,z1,z3,z47,z77,z6]),(0,[z7,z1,z3,z47,z5,z74])],[(0,[z7,z199,z3,z35,z5,z6]),(1,[z7,z1,z835,z5,z6])],[(0,[z1120,z1,z3,z4,z5,z6]),(0,[z0,z14,z3,z4,z101,z6]),(0,[z1121,z1,z3,z4,z5,z6]),(0,[z7,z1,z1122,z4,z5,z6]),(0,[z7,z882,z3,z4,z5,z6]),(0,[z1123,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z35,z5,z1021]),(0,[z7,z59,z1,z9,z5,z6])],[(0,[z7,z1,z3,z92,z5,z6]),(0,[z1124,z1,z3,z4,z5,z6])],[(0,[z14,z1,z3,z393,z5,z6]),(0,[z7,z1,z234,z4,z5,z6]),(0,[z7,z1,z235,z4,z5,z388]),(0,[z1,z3,z4,z5,z261,z479]),(0,[z1125,z1,z3,z4,z5,z6])],[(0,[z594,z2,z3,z47,z5,z6]),(0,[z14,z61,z3,z35,z5,z6]),(0,[z7,z1,z48,z4,z5,z85])],[(0,[z14,z46,z3,z35,z5,z6]),(0,[z14,z1,z75,z3,z41,z5]),(0,[z1126,z1,z3,z4,z5,z6]),(0,[z1,z476,z3,z35,z5,z6]),(0,[z1,z3,z4,z1127,z5,z6])],[(0,[z7,z1,z3,z4,z1128,z6]),(0,[z7,z1,z3,z4,z1129,z6])]],
   [[(0,[z86,z2,z3,z4,z24,z6]),(0,[z7,z46,z3,z93,z5,z6]),(0,[z223,z1,z3,z4,z5,z420]),(0,[z7,z1,z3,z220,z5,z333]),(0,[z7,z1,z3,z35,z715,z5])],[(0,[z648,z2,z3,z4,z5,z6]),(0,[z203,z1,z3,z4,z239,z6]),(0,[z7,z1,z3,z1130,z5,z6]),(0,[z300,z1,z363,z4,z5,z6])],[(0,[z7,z1,z31,z76,z5,z60])],[(0,[z257,z1,z3,z4,z5,z6]),(0,[z344,z2,z3,z47,z5,z6]),(0,[z1,z3,z4,z259,z5,z6])],[(0,[z2,z3,z47,z24,z5,z6]),(0,[z14,z1,z3,z171,z5,z6]),(0,[z7,z1,z3,z4,z1131,z6]),(0,[z7,z1,z3,z35,z5,z1030]),(0,[z1,z3,z4,z5,z1132,z6]),(0,[z1,z1133,z3,z4,z5,z6])],[],[(0,[z316,z275,z3,z4,z5,z6]),(0,[z7,z3,z35,z441,z5,z6]),(0,[z1,z3,z4,z1134,z5,z6]),(0,[z300,z1,z378,z4,z5,z6])],[(0,[z1,z2,z3,z393,z5,z6]),(0,[z139,z1,z3,z47,z5,z6]),(0,[z1135,z1,z3,z4,z5,z6])],[(0,[z201,z14,z1,z4,z25,z6]),(0,[z7,z1,z3,z4,z5,z1136]),(0,[z7,z1,z3,z4,z273,z6]),(0,[z7,z1,z1137,z4,z5,z6]),(0,[z7,z3,z81,z5,z101,z6])],[(0,[z2,z3,z4,z5,z6,z683]),(0,[z1,z2,z75,z3,z41,z5]),(0,[z690,z1,z3,z4,z239,z6]),(0,[z127,z1,z3,z35,z5,z6]),(0,[z1138,z1,z3,z4,z5,z6]),(0,[z225,z929,z3,z4,z5,z6]),(0,[z7,z1,z75,z178,z5,z6])],[],[(0,[z1139,z7,z1,z4,z5,z6]),(0,[z7,z1,z234,z4,z101,z6]),(0,[z7,z1,z1140,z4,z5,z6])],[(0,[z1141,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1142,z5,z6]),(0,[z1,z3,z4,z1143,z5,z6])],[(0,[z53,z2,z3,z35,z5,z6]),(0,[z14,z1,z235,z4,z5,z6]),(0,[z14,z61,z3,z47,z5,z6]),(0,[z7,z1,z1025,z47,z5,z6]),(0,[z1144,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1145]),(0,[z14,z1,z3,z338,z5,z6]),(0,[z54,z1,z3,z35,z68,z6]),(0,[z223,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z5,z1146]),(0,[z1147,z1,z3,z4,z5,z6]),(0,[z7,z3,z962,z47,z5,z6]),(0,[z1148,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z306,z110])],[(0,[z154,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z171,z5,z6]),(0,[z14,z275,z3,z4,z5,z6]),(0,[z166,z127,z44,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z388]),(0,[z412,z1,z3,z4,z279,z6]),(0,[z7,z1,z568,z3,z41,z5]),(0,[z7,z1,z1149,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z1150]),(0,[z7,z1,z3,z47,z5,z21]),(0,[z344,z525,z3,z47,z5,z6]),(0,[z7,z616,z3,z47,z5,z6]),(0,[z412,z1,z3,z209,z5,z6]),(0,[z1151,z1,z3,z4,z5,z6])],[(0,[z7,z1,z31,z47,z5,z6]),(0,[z246,z1,z3,z211,z5,z6]),(0,[z1,z1152,z3,z4,z5,z6])],[(0,[z14,z1,z3,z4,z167,z6])],[(0,[z1,z3,z4,z5,z910,z50]),(0,[z78,z1,z3,z338,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1153]),(0,[z17,z7,z1,z3,z74,z278])],[(1,[z2,z3,z47,z5,z6]),(0,[z7,z153,z3,z4,z5,z74])],[(0,[z7,z1,z3,z1154,z5,z6]),(0,[z2,z3,z47,z5,z6,z110]),(0,[z7,z1,z3,z348,z5,z21])],[(0,[z316,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1155,z5,z6]),(0,[z318,z1,z3,z4,z5,z6])],[(0,[z1,z2,z235,z4,z5,z6])],[(0,[z221,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z338,z5,z6]),(0,[z1,z3,z4,z5,z6,z1156]),(0,[z7,z1,z3,z1157,z5,z6])],[(0,[z7,z1158,z3,z4,z5,z6]),(0,[z391,z1,z3,z4,z5,z50]),(0,[z7,z1,z3,z481,z13,z4]),(0,[z1,z3,z4,z1159,z5,z6]),(0,[z7,z1,z48,z209,z5,z6]),(0,[z186,z1,z3,z382,z4,z5])],[(0,[z17,z2,z3,z47,z5,z6]),(0,[z1160,z7,z1,z3,z5,z6]),(0,[z14,z478,z3,z4,z5,z6]),(0,[z1,z3,z47,z802,z5,z6]),(0,[z7,z1,z3,z4,z501,z232])],[(0,[z7,z1,z1161,z4,z5,z6]),(0,[z186,z1,z3,z4,z5,z6]),(0,[z19,z1,z3,z374,z5,z6]),(0,[z7,z1,z3,z4,z279,z6]),(0,[z7,z1,z3,z1162,z5,z6]),(0,[z1163,z1,z3,z4,z5,z6])],[(0,[z53,z2,z3,z47,z5,z6]),(0,[z1,z2,z3,z4,z167,z6]),(0,[z2,z3,z47,z5,z6,z82]),(0,[z1,z151,z83,z4,z5,z6]),(0,[z67,z7,z882,z3,z5,z6]),(0,[z7,z3,z47,z5,z6,z485])],[(0,[z14,z1,z3,z382,z4,z5]),(0,[z54,z1,z3,z47,z68,z6]),(0,[z223,z1,z3,z47,z5,z6]),(0,[z1164,z1,z3,z4,z5,z6])],[]],
   [[(0,[z14,z1,z3,z4,z5,z6]),(0,[z94,z1,z447,z4,z5,z6]),(0,[z1165,z1,z3,z4,z5,z6])],[(0,[z7,z1166,z3,z4,z5,z6]),(0,[z344,z7,z3,z47,z5,z6]),(0,[z7,z1,z1167,z4,z5,z6]),(0,[z7,z1,z234,z47,z5,z6]),(0,[z7,z1,z3,z4,z1168,z6])],[(0,[z55,z1,z3,z4,z5,z50])],[(0,[z1139,z1,z2,z4,z5,z6]),(0,[z7,z1,z1169,z4,z5,z6]),(0,[z291,z1,z3,z35,z5,z6])],[(0,[z14,z769,z3,z4,z5,z6]),(0,[z7,z1,z3,z204,z5,z21]),(0,[z1170,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z875]),(0,[z19,z1,z3,z98,z5,z6]),(0,[z78,z1,z3,z4,z5,z6])],[(0,[z2,z3,z28,z47,z5,z6]),(0,[z203,z1,z3,z47,z239,z6]),(1,[z7,z3,z4,z5,z823]),(0,[z7,z1,z230,z4,z5,z143])],[],[(0,[z626,z1,z99,z4,z5,z6]),(0,[z257,z1,z3,z47,z5,z6]),(0,[z246,z1,z3,z87,z5,z6])],[(0,[z1,z2,z3,z382,z4,z5]),(0,[z14,z86,z3,z4,z24,z6]),(0,[z127,z1,z3,z4,z5,z21]),(0,[z7,z86,z3,z47,z5,z6]),(0,[z17,z7,z153,z3,z6,z278])],[(0,[z351,z7,z3,z47,z5,z6]),(0,[z7,z480,z3,z47,z5,z6]),(0,[z7,z1,z1171,z4,z5,z6]),(0,[z1172,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z1173,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z34,z2,z3,z47,z5,z6]),(0,[z7,z1,z3,z35,z77,z6]),(0,[z7,z1,z3,z1174,z5,z6]),(0,[z7,z1,z35,z824,z5,z6]),(1,[z7,z1,z28,z5,z492]),(0,[z201,z7,z1,z4,z986,z6]),(0,[z104,z1,z3,z4,z105,z232])],[(0,[z2,z75,z3,z47,z5,z6]),(0,[z19,z1,z3,z347,z5,z6])],[(0,[z188,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z5,z873,z6]),(0,[z7,z1,z1175,z4,z5,z6]),(0,[z7,z1,z3,z47,z273,z6]),(0,[z7,z1,z1137,z47,z5,z6]),(0,[z7,z1,z378,z4,z5,z6])],[(0,[z2,z3,z140,z47,z5,z6]),(0,[z7,z1,z3,z338,z306,z6])],[(0,[z116,z1,z3,z4,z5,z6]),(0,[z245,z1,z234,z4,z5,z6]),(0,[z200,z7,z1,z4,z5,z720])]],
   [[(0,[z1,z151,z423,z4,z5,z6])],[],[(0,[z1176,z1,z2,z4,z5,z6]),(0,[z7,z409,z3,z47,z5,z6]),(0,[z223,z1,z3,z204,z5,z6])],[(0,[z1160,z1,z2,z3,z5,z6]),(0,[z7,z1,z3,z348,z273,z6]),(0,[z291,z1,z3,z47,z5,z6]),(0,[z1,z3,z4,z1177,z5,z6]),(0,[z7,z1,z3,z4,z105,z232])],[(0,[z2,z3,z370,z47,z5,z6]),(0,[z275,z2,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z955,z6]),(0,[z18,z7,z225,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z1178]),(0,[z7,z3,z47,z5,z534,z6]),(0,[z7,z1,z3,z1179,z5,z6])],[(0,[z14,z1,z3,z76,z5,z60])],[(0,[z7,z59,z1,z370,z5,z6]),(0,[z7,z1,z3,z1180,z5,z6])],[(0,[z2,z3,z47,z5,z6,z240]),(0,[z2,z3,z13,z47,z5,z6]),(0,[z2,z3,z9,z47,z5,z6]),(0,[z7,z86,z3,z47,z101,z6]),(0,[z7,z1,z4,z5,z6,z720])],[(0,[z2,z3,z47,z244,z5,z6]),(0,[z166,z7,z819,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1181]),(0,[z7,z1,z604,z28,z5,z6])],[(0,[z2,z3,z47,z5,z101,z6]),(0,[z7,z3,z466,z35,z5,z6]),(0,[z7,z1,z3,z81,z5,z228]),(0,[z1,z4,z1177,z178,z5,z6])],[(0,[z7,z1,z3,z4,z1182,z6]),(0,[z377,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1183]),(0,[z7,z1,z3,z41,z860,z5])],[(0,[z316,z1,z3,z47,z5,z6]),(0,[z318,z1,z3,z47,z5,z6]),(0,[z154,z7,z3,z4,z279,z110]),(0,[z1,z263,z3,z313,z5,z6]),(0,[z7,z1,z4,z5,z986,z6]),(0,[z7,z1,z3,z4,z636,z232])],[(0,[z14,z1,z3,z4,z5,z190]),(0,[z1,z3,z4,z5,z6,z172]),(0,[z7,z70,z3,z20,z5,z6]),(0,[z22,z57,z23,z4,z5,z6]),(0,[z7,z1,z3,z1184,z5,z6]),(0,[z7,z1,z363,z35,z5,z6]),(0,[z154,z7,z3,z209,z5,z110]),(0,[z1185,z1,z3,z4,z5,z6])],[(0,[z67,z7,z1,z3,z5,z6]),(0,[z1,z476,z3,z87,z5,z6])],[(0,[z7,z1,z3,z1186,z5,z6]),(0,[z7,z3,z47,z5,z562,z6]),(0,[z1187,z1,z3,z4,z5,z6])]],
   [[(0,[z18,z275,z3,z20,z5,z6]),(0,[z7,z1,z3,z1188,z5,z6]),(0,[z7,z86,z3,z962,z5,z6]),(0,[z201,z7,z1,z4,z25,z6]),(0,[z1189,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z76,z5,z60]),(0,[z7,z1,z4,z5,z6,z892]),(1,[z1,z790,z4,z5,z6]),(0,[z7,z1,z3,z47,z279,z6]),(0,[z7,z1,z9,z835,z5,z6]),(0,[z7,z225,z363,z4,z5,z6])],[(0,[z7,z1,z3,z1190,z5,z6]),(0,[z7,z1,z3,z4,z1191,z6])],[(0,[z7,z1,z3,z1192,z5,z6]),(0,[z54,z1,z3,z164,z68,z6]),(0,[z7,z1,z3,z35,z5,z21]),(0,[z154,z412,z3,z4,z5,z110]),(0,[z188,z162,z3,z4,z5,z85])],[(0,[z476,z3,z4,z47,z5,z6]),(0,[z7,z1,z31,z35,z5,z6]),(0,[z1,z3,z4,z1193,z5,z6])],[(0,[z7,z1,z3,z1194,z5,z6]),(0,[z7,z1,z3,z5,z1195,z6]),(0,[z7,z1,z354,z345,z5,z6])],[(0,[z2,z3,z47,z115,z5,z6]),(0,[z7,z1,z3,z4,z5,z1196]),(0,[z19,z1,z3,z708,z5,z6]),(0,[z7,z1,z3,z1197,z5,z6]),(0,[z7,z1,z3,z4,z5,z1198])],[(0,[z1,z3,z4,z5,z6,z1199]),(0,[z7,z1,z3,z1200,z5,z6]),(1,[z7,z882,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z1201])],[(0,[z1,z2,z3,z4,z5,z190]),(0,[z7,z598,z3,z47,z5,z6]),(0,[z7,z236,z3,z35,z5,z6]),(0,[z1202,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z710]),(0,[z7,z1,z3,z757,z47,z5]),(0,[z7,z1,z3,z35,z5,z1107]),(0,[z7,z1,z3,z4,z726,z232])],[(0,[z2,z2,z3,z47,z5,z6]),(0,[z2,z3,z99,z47,z5,z6]),(0,[z14,z1,z3,z5,z937,z6]),(0,[z166,z14,z44,z4,z5,z6]),(0,[z7,z1,z3,z1203,z5,z6]),(0,[z7,z1,z3,z1204,z5,z6])],[(0,[z22,z2,z3,z47,z5,z6]),(0,[z14,z1,z3,z348,z5,z6]),(0,[z7,z22,z819,z4,z5,z6]),(0,[z7,z1,z731,z4,z5,z6]),(0,[z7,z1,z3,z1205,z5,z6])],[(0,[z14,z673,z3,z4,z5,z6]),(0,[z7,z1,z3,z1067,z4,z5]),(0,[z7,z1,z574,z4,z5,z143]),(0,[z7,z1206,z3,z4,z5,z6])],[(0,[z565,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1207,z6]),(0,[z7,z1,z363,z47,z5,z6]),(0,[z7,z967,z1,z35,z5,z6]),(0,[z7,z153,z3,z87,z5,z6]),(0,[z7,z1,z3,z40,z679,z4]),(0,[z7,z59,z1,z280,z5,z6]),(0,[z7,z1,z3,z4,z5,z1208]),(0,[z7,z1,z3,z4,z522,z232])],[(0,[z7,z1,z3,z1209,z5,z6]),(0,[z7,z693,z3,z35,z5,z6]),(0,[z1210,z1,z3,z4,z5,z6]),(0,[z1211,z1,z3,z4,z5,z6])],[(0,[z1212,z1,z3,z4,z5,z6]),(0,[z17,z7,z1,z3,z6,z71]),(0,[z200,z1,z4,z5,z172,z82]),(0,[z1,z3,z4,z1213,z5,z6])]],
   [[(0,[z7,z2,z3,z169,z5,z6]),(0,[z1,z2,z4,z5,z932,z6])],[(0,[z18,z1,z3,z20,z5,z6])],[(0,[z7,z1,z3,z4,z273,z420]),(0,[z1214,z1,z3,z4,z5,z6]),(0,[z188,z1,z3,z47,z5,z6]),(0,[z7,z1,z378,z47,z5,z6]),(0,[z7,z1,z3,z40,z4,z726])],[(0,[z316,z2,z3,z4,z5,z6]),(0,[z7,z1,z1215,z3,z5,z6]),(0,[z7,z1,z3,z4,z5,z1216]),(0,[z7,z819,z44,z4,z5,z6])],[(0,[z1,z3,z4,z1217,z5,z6]),(0,[z1,z3,z4,z68,z6,z190]),(0,[z486,z7,z3,z47,z5,z6]),(0,[z7,z1,z234,z35,z5,z6])],[(0,[z7,z314,z3,z47,z5,z6]),(0,[z535,z1,z3,z4,z5,z6]),(0,[z111,z7,z3,z4,z5,z110])],[(0,[z1,z2,z3,z348,z5,z6]),(0,[z67,z1,z2,z3,z5,z6]),(0,[z7,z487,z3,z47,z5,z6]),(0,[z651,z1,z3,z4,z68,z6]),(0,[z7,z1,z3,z1218,z5,z6]),(0,[z7,z1,z3,z128,z5,z228]),(0,[z1,z3,z4,z1219,z5,z6]),(0,[z7,z1220,z3,z4,z5,z6])],[(0,[z2,z3,z47,z5,z6,z333]),(0,[z0,z2,z3,z4,z101,z6]),(0,[z34,z1,z790,z4,z5,z6])],[(0,[z2,z3,z466,z4,z5,z6]),(0,[z201,z1,z2,z4,z25,z6]),(0,[z7,z1221,z3,z4,z5,z6]),(0,[z7,z1222,z3,z4,z5,z6])],[(0,[z203,z1,z3,z35,z239,z6]),(0,[z1223,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z745]),(0,[z7,z1,z3,z4,z1224,z6]),(0,[z318,z153,z3,z4,z5,z6])],[(0,[z2,z3,z289,z4,z5,z6]),(0,[z33,z1,z3,z20,z5,z6]),(0,[z1225,z1,z3,z4,z5,z6])],[(0,[z1,z1226,z3,z4,z5,z6]),(0,[z14,z281,z3,z4,z5,z6]),(0,[z421,z7,z1,z4,z25,z6]),(0,[z7,z116,z3,z47,z5,z6]),(0,[z257,z1,z3,z35,z5,z6])],[(0,[z7,z1,z3,z47,z1111,z6]),(0,[z7,z1,z48,z4,z279,z6]),(1,[z1,z3,z4,z501,z232])],[(0,[z1176,z7,z1,z4,z5,z6]),(0,[z14,z1,z3,z434,z5,z6]),(0,[z7,z1,z3,z4,z5,z750])],[(0,[z7,z1,z819,z4,z5,z6]),(0,[z7,z1,z735,z4,z5,z6])],[(0,[z674,z7,z1,z4,z5,z82]),(0,[z7,z1,z3,z40,z13,z35])]],
   [[(0,[z626,z1,z295,z4,z5,z6]),(0,[z377,z2,z3,z47,z5,z6]),(0,[z14,z1,z48,z4,z5,z6]),(0,[z7,z1,z3,z35,z273,z6]),(0,[z7,z3,z884,z47,z5,z6]),(0,[z7,z1,z3,z47,z5,z1183])],[(1,[z1,z3,z4,z68,z190]),(0,[z7,z665,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z101,z388]),(0,[z1,z1227,z3,z4,z5,z6])],[(0,[z14,z3,z35,z47,z5,z6]),(0,[z0,z7,z235,z4,z101,z6]),(0,[z307,z7,z1,z4,z25,z6])],[(0,[z7,z1,z3,z4,z5,z1018]),(0,[z7,z1,z4,z171,z5,z82])],[(0,[z144,z7,z3,z47,z5,z6]),(0,[z186,z1,z3,z4,z5,z479])],[(0,[z94,z1,z3,z4,z353,z6]),(0,[z1,z3,z4,z5,z1228,z6]),(0,[z78,z1,z48,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1229])],[(0,[z7,z1,z3,z1230,z4,z5]),(0,[z1231,z1,z3,z4,z5,z6]),(0,[z7,z1,z718,z47,z5,z6])],[(0,[z2,z414,z3,z47,z5,z6]),(0,[z7,z1,z3,z4,z5,z1232]),(0,[z7,z1,z3,z35,z5,z388])],[(0,[z1233,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z434,z5,z6]),(0,[z14,z1,z3,z4,z5,z479]),(0,[z7,z1,z3,z4,z5,z1234]),(0,[z1235,z7,z1,z3,z5,z6]),(0,[z7,z1,z3,z1236,z5,z6]),(0,[z7,z1,z4,z1237,z5,z6])],[(0,[z7,z275,z3,z93,z5,z6]),(0,[z7,z1,z3,z4,z1238,z6]),(0,[z1239,z1,z3,z4,z5,z6]),(0,[z1,z1240,z3,z4,z5,z6]),(0,[z7,z1,z3,z1241,z5,z6])],[(0,[z538,z2,z3,z47,z5,z6]),(0,[z14,z1,z3,z4,z5,z420]),(0,[z7,z3,z47,z636,z5,z6]),(0,[z1,z476,z3,z211,z5,z6]),(0,[z7,z1,z3,z4,z24,z479]),(0,[z7,z1,z3,z1242,z4,z5]),(0,[z7,z153,z363,z4,z5,z6]),(0,[z17,z7,z1,z378,z6,z278])],[(0,[z1,z2,z48,z4,z5,z6]),(0,[z86,z476,z3,z47,z5,z6]),(0,[z7,z1,z3,z382,z47,z5])],[(0,[z7,z1,z3,z1243,z5,z6])],[(0,[z0,z2,z3,z47,z5,z6]),(0,[z14,z1,z10,z28,z5,z6])],[(0,[z70,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z1244,z5,z6]),(0,[z1,z409,z3,z107,z5,z6]),(0,[z7,z1,z3,z1245,z5,z6]),(0,[z7,z1,z3,z1246,z5,z6])],[(0,[z14,z1,z3,z4,z5,z492]),(0,[z1247,z1,z3,z4,z5,z6]),(0,[z316,z1,z3,z35,z5,z6]),(0,[z318,z1,z3,z35,z5,z6]),(0,[z7,z1,z305,z4,z279,z6]),(0,[z7,z59,z1,z4,z5,z492]),(0,[z1,z3,z4,z5,z1248,z6]),(0,[z7,z153,z378,z4,z5,z6])]],
   [[(0,[z7,z1,z4,z1015,z5,z6]),(0,[z7,z141,z3,z47,z5,z6]),(0,[z7,z1,z305,z209,z5,z6])],[(0,[z221,z1,z3,z339,z5,z6]),(0,[z14,z1,z3,z5,z164,z6]),(0,[z7,z1,z3,z1249,z5,z6]),(0,[z223,z1,z3,z4,z5,z21]),(0,[z17,z7,z225,z3,z6,z278])],[(0,[z2,z3,z248,z47,z5,z6]),(0,[z17,z7,z1,z3,z6,z931])],[(0,[z1,z2,z3,z4,z5,z479]),(0,[z14,z1,z3,z4,z353,z6]),(0,[z318,z225,z3,z4,z5,z6])],[(0,[z2,z3,z44,z47,z5,z6]),(0,[z14,z1,z3,z4,z5,z987]),(0,[z7,z70,z3,z107,z5,z6]),(0,[z166,z7,z44,z4,z167,z6]),(0,[z7,z1,z3,z35,z279,z6]),(0,[z186,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z4,z784,z6]),(0,[z1,z3,z4,z5,z1250,z6]),(0,[z7,z1,z142,z4,z5,z720])],[(0,[z1,z2,z3,z4,z5,z420]),(0,[z0,z7,z3,z4,z101,z6]),(0,[z1251,z1,z3,z4,z5,z6]),(0,[z1252,z1,z3,z4,z5,z6])],[(0,[z7,z1253,z3,z4,z5,z6]),(0,[z1,z3,z4,z68,z50,z232]),(0,[z412,z1,z3,z4,z306,z6]),(0,[z7,z1,z1254,z4,z5,z6])],[(0,[z2,z3,z4,z47,z5,z6]),(0,[z7,z1,z3,z47,z5,z388]),(0,[z1,z3,z4,z5,z6,z1255]),(0,[z318,z1,z3,z4,z5,z74])],[(0,[z14,z1,z3,z35,z5,z6]),(0,[z1,z2,z10,z28,z5,z6]),(0,[z7,z1,z1256,z4,z5,z6])],[(0,[z14,z162,z3,z4,z5,z85]),(0,[z344,z7,z3,z884,z5,z6]),(0,[z7,z1,z3,z1257,z5,z6])],[(0,[z7,z1,z3,z93,z5,z6]),(0,[z1,z2,z3,z4,z5,z492]),(0,[z55,z1,z3,z35,z5,z50]),(0,[z137,z1,z3,z4,z5,z910]),(0,[z7,z1,z418,z28,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1258]),(0,[z7,z3,z4,z5,z823,z110])],[(0,[z1,z2,z3,z5,z164,z6]),(0,[z14,z225,z3,z4,z5,z6]),(0,[z7,z1,z3,z1259,z5,z6])],[(0,[z203,z1,z3,z4,z416,z6]),(0,[z7,z3,z40,z47,z101,z6]),(0,[z78,z1,z3,z35,z5,z6]),(0,[z1260,z1,z3,z4,z5,z6])],[(0,[z1,z2,z305,z4,z5,z6]),(0,[z595,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z353,z6]),(0,[z1223,z1,z3,z47,z5,z6]),(0,[z7,z1,z235,z81,z5,z6])],[(0,[z1261,z1,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z903,z5]),(0,[z14,z1,z3,z4,z5,z74]),(0,[z7,z1,z3,z708,z5,z6]),(0,[z828,z7,z1,z3,z47,z6])],[(0,[z221,z2,z3,z47,z5,z6])],[(0,[z2,z3,z295,z47,z5,z6]),(0,[z7,z1,z3,z1262,z5,z6]),(0,[z166,z7,z44,z4,z5,z6]),(0,[z7,z225,z3,z197,z5,z6])],[(0,[z7,z1,z3,z1263,z5,z6]),(0,[z1,z2,z3,z35,z5,z6]),(0,[z1,z3,z4,z1264,z5,z6]),(0,[z7,z1,z3,z1265,z5,z6]),(0,[z7,z1,z235,z4,z5,z228]),(0,[z7,z1,z3,z4,z306,z6])],[(0,[z7,z1,z3,z204,z273,z6]),(0,[z7,z1,z3,z1266,z5,z6]),(0,[z1267,z1,z3,z4,z5,z6]),(0,[z186,z1,z3,z47,z5,z6]),(0,[z7,z3,z47,z687,z5,z6])],[(0,[z188,z1,z3,z35,z5,z6]),(0,[z7,z1,z378,z35,z5,z6]),(0,[z245,z1,z3,z4,z5,z388]),(0,[z17,z7,z1,z363,z6,z278])],[(0,[z7,z1,z3,z4,z472,z232]),(0,[z7,z3,z589,z47,z5,z6])],[(0,[z7,z591,z3,z47,z5,z6]),(0,[z116,z1,z3,z35,z5,z6]),(0,[z7,z1,z3,z1268,z5,z6]),(0,[z1,z1269,z3,z4,z5,z6]),(0,[z200,z7,z1,z4,z630,z5])],[(0,[z14,z1,z3,z47,z5,z6]),(0,[z19,z7,z225,z3,z5,z6]),(0,[z1,z3,z1270,z4,z5,z6]),(0,[z7,z1,z363,z4,z5,z74])],[(0,[z144,z2,z3,z47,z5,z6]),(0,[z127,z1,z3,z4,z273,z6]),(0,[z246,z86,z3,z47,z5,z6]),(0,[z7,z680,z3,z35,z5,z6]),(0,[z7,z1,z1271,z4,z5,z6]),(0,[z1,z1272,z3,z4,z5,z6]),(0,[z7,z225,z378,z4,z5,z6])],[(0,[z2,z3,z47,z5,z6,z60]),(0,[z55,z1,z3,z47,z5,z50]),(0,[z1273,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z74]),(0,[z7,z1,z3,z5,z1274,z6]),(1,[z7,z3,z884,z5,z6]),(0,[z7,z1,z3,z35,z105,z232])],[(0,[z70,z3,z4,z20,z5,z6]),(0,[z7,z1,z3,z4,z1275,z6]),(0,[z257,z1,z234,z4,z5,z6])],[(0,[z78,z1,z3,z47,z5,z6]),(0,[z7,z1,z378,z4,z5,z74])],[(0,[z223,z1,z3,z4,z273,z6]),(0,[z7,z1,z3,z4,z5,z1276])],[(0,[z7,z70,z3,z4,z5,z6]),(0,[z7,z1277,z3,z4,z5,z6]),(0,[z317,z1,z3,z107,z5,z6]),(0,[z162,z263,z3,z4,z5,z85]),(0,[z7,z1,z4,z178,z5,z60])]],
   [[(0,[z203,z1,z3,z4,z5,z190]),(0,[z7,z1,z4,z178,z5,z6]),(0,[z1,z1278,z3,z4,z5,z6])],[(1,[z2,z3,z169,z5,z6]),(0,[z203,z1,z3,z4,z807,z6]),(0,[z7,z1,z3,z81,z5,z6])],[(0,[z1,z504,z3,z4,z239,z6]),(0,[z7,z1,z3,z4,z5,z1279])],[(0,[z1,z2,z3,z47,z5,z6]),(0,[z693,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z1280,z5,z6]),(0,[z7,z1,z3,z4,z1281,z6]),(0,[z7,z1,z3,z4,z5,z1282])],[(0,[z7,z1,z3,z4,z353,z50]),(0,[z7,z3,z197,z47,z5,z6]),(0,[z1,z3,z4,z1283,z5,z6])],[(0,[z7,z1,z3,z4,z5,z1284]),(0,[z1285,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z85,z823]),(0,[z7,z1,z3,z1286,z5,z6])],[(0,[z7,z1,z3,z4,z5,z228])],[(0,[z7,z1,z1287,z4,z5,z6]),(0,[z7,z1,z3,z4,z1288,z6]),(0,[z116,z1,z3,z47,z5,z6]),(0,[z1187,z1,z3,z35,z5,z6]),(0,[z188,z1,z3,z118,z5,z6])],[(0,[z2,z3,z47,z5,z138,z6]),(0,[z19,z70,z3,z4,z5,z6]),(0,[z19,z1,z3,z107,z5,z6]),(0,[z7,z1,z142,z4,z5,z422]),(0,[z7,z1,z178,z47,z5,z6]),(0,[z201,z7,z1,z35,z25,z6])],[(0,[z53,z2,z3,z169,z5,z6]),(0,[z7,z3,z87,z47,z5,z6])],[(0,[z7,z3,z98,z47,z5,z6]),(0,[z0,z7,z3,z47,z101,z6]),(0,[z7,z1,z235,z128,z5,z6])],[(0,[z7,z1,z3,z47,z105,z232]),(0,[z1,z3,z259,z47,z5,z6]),(0,[z411,z7,z1,z3,z6,z278])],[(0,[z852,z46,z3,z4,z5,z6]),(0,[z14,z1,z3,z204,z5,z6]),(0,[z7,z3,z4,z884,z5,z6])],[(0,[z471,z1,z3,z4,z68,z6]),(0,[z390,z7,z44,z4,z5,z6]),(0,[z7,z3,z47,z101,z25,z6]),(0,[z7,z52,z3,z35,z5,z6])],[],[(0,[z14,z2,z3,z4,z5,z6]),(0,[z7,z1,z3,z1289,z5,z6]),(0,[z1290,z1,z3,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 509) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 509).take 500) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1009).take 406) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1415)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [509, 500, 406] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 116).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 116).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 222).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 328).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 427).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [116, 106, 106, 99, 85] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_36358

theorem PEqualNP.Outside.L_meta_36358 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4274846856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4274846856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36358.solve