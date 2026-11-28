import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42546

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
  Nat.testBit (4276812992 * 2 ^ 32 + 4243122368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0c578c6440d8de52#64 ++ 0x0418af18c881b1bc#64 ++ 0x1cff8c6441f9fe7d#64 ++ 0x1c39ff18c883f3fc#64 : BitVec 256),
   (0x213005a81a2a2a84#64 ++ 0x0042600b50345455#64 ++ 0x63300ff87e3e3ffb#64 ++ 0xecc6601ff0fc7c7f#64 : BitVec 256),
   (0x82c0b05185454518#64 ++ 0x09058160a30a8a8a#64 ++ 0x83c1f07f87c7c7f7#64 ++ 0x7f0783e0ff0f8f8f#64 : BitVec 256),
   (0x5c015a86e807b060#64 ++ 0x12b802b50dd00f60#64 ++ 0xfc01ff87f807f86f#64 ++ 0xf7f803ff0ff00ff0#64 : BitVec 256),
   (0xf7aa000777b00000#64 ++ 0x23ef54000eef6000#64 ++ 0xfffe0007fff8005f#64 ++ 0xbbfffc000ffff000#64 : BitVec 256),
   (0xfbfdef7800000000#64 ++ 0x43f7fbdef0000000#64 ++ 0xfffffff80000003f#64 ++ 0xc3fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6441f9fe7d 0x1c39ff18c883f3fc

def z1 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87e3e3ffb 0xecc6601ff0fc7c7f

def z2 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f807f86f 0xf7f803ff0ff00ff0

def z3 : W := mkw 0x5c115ea6e80fba60 0x12b822bd4dd01f74 0xfc31ffe7f83ffe7f 0xfff863ffcff07ffc

def z4 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f87c7c7f7 0x7f0783e0ff0f8f8f

def z5 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007fff8005f 0xbbfffc000ffff000

def z6 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff80000003f 0xc3fffffff0000000

def z7 : W := mkw 0x0c01080440009040 0x0018021008800120 0x1c018c044001f86d 0x14380318088003f0

def z8 : W := mkw 0xf3a8000337200000 0x23e75000066e4000 0xe3000003be000002 0xa3c60000077c0000

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300001806060182 0x60060000300c0c03

def z10 : W := mkw 0x0040804000404410 0x0000810080008088 0x03c1807c07c7c7f7 0x7c078300f80f8f8f

def z11 : W := mkw 0x5402000660900000 0x02a804000cc12000 0xfcfe0007f9f8005f 0xbbf9fc000ff3f000

def z12 : W := mkw 0x08014a800802b060 0x1010029500100560 0x00000f8000003800 0x0000001f00000070

def z13 : W := mkw 0x7d3d4fae6802b060 0x52fa7a9f5cd00560 0x7c3e0f8078003808 0x80f87c1f00f00070

def z14 : W := mkw 0x7d3f4f2e72b00000 0x62fa7e9e5ce56000 0x7c3e0f8078380008 0x80f87c1f00f07000

def z15 : W := mkw 0x50005282a8072020 0x12a000a505500e40 0xe0007383b8060002 0xe3c000e707700c00

def z16 : W := mkw 0xffab5a87ffb7b060 0x33ff56b50fff6f60 0xffffff87fffff87f 0xffffffff0ffffff0

def z17 : W := mkw 0x0402000440900000 0x0008040008812000 0x1cfe000441f8005d 0x1839fc000883f000

def z18 : W := mkw 0xffffef7f77b00000 0x63ffffdefeef6000 0xfffffffffff8007f 0xfbfffffffffff000

def z19 : W := mkw 0xf3a8631800000000 0x43e750c630000000 0xe300739800000002 0xc3c600e730000000

def z20 : W := mkw 0x000000801a2a2a84 0x0000000100345455 0x0000000078383800 0x0000000000f07070

def z21 : W := mkw 0x0c170c2440989a42 0x04182e1848813134 0x1cfe0c0441f8385d 0x1839fc180883f070

def z22 : W := mkw 0x2120010800000000 0x0042400210000000 0x6300039800000002 0xc0c6000730000000

def z23 : W := mkw 0x0c011886e807b060 0x101802310dd00f60 0x1c018c07f807f86d 0x343803180ff00ff0

def z24 : W := mkw 0x50005282a8072020 0x12a000a505500e40 0xe001f387b807c067 0xf7c003e70f700f80

def z25 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc007f83f806380a 0xe3f800ff07f00c70

def z26 : W := mkw 0x29758de81a6afed6 0x0452eb1bd034d5fd 0x63318ff87e3ffffb 0xecc6631ff0fc7fff

def z27 : W := mkw 0x08558c6000000000 0x0010ab18c0000000 0x1cff8c600000003d 0x0039ff18c0000000

def z28 : W := mkw 0xffffef7c40d8de52 0x47ffffdef881b1bc 0xfffffffc41f9fe7f 0xdffffffff883f3fc

def z29 : W := mkw 0xf7eab057f7f54518 0x2befd560afefea8a 0xfffff007fff9c05f 0xbbffffe00ffff380

def z30 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0x9c01f007f807f844 0x373803e00ff00ff0

def z31 : W := mkw 0x2130052800000000 0x0042600a50000000 0x63300ff80000003b 0xc0c6601ff0000000

def z32 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0x9ccff00000000004 0x03399fe000000000

def z33 : W := mkw 0xffffff7ff7f54518 0x6bfffffeffefea8a 0xffffffffffffc7ff 0xffffffffffffff8f

def z34 : W := mkw 0xa3f0b5f99f6f6f9c 0x0947e16bf33ededf 0xe3f1ffffffffffff 0xffc7e3ffffffffff

def z35 : W := mkw 0x5c014a866802b060 0x12b802950cd00560 0x7c000f8078003808 0x80f8001f00f00070

def z36 : W := mkw 0x82c0a05105404518 0x09058140a20a808a 0x03c0007807c00790 0x08078000f00f800f

def z37 : W := mkw 0x58014a0000000000 0x02b0029400000000 0xfc01ff800000002f 0xc3f803ff00000000

def z38 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0x7c3e0f8000000008 0x80f87c1f00000000

def z39 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x60300ff8783e3fa8 0xc4c0601ff0f07c7f

def z40 : W := mkw 0x2170b5f89a6f6f9c 0x0842e16bf134dedf 0x6331fff87e3ffffb 0xecc663fff0fc7fff

def z41 : W := mkw 0xfbfdef7800404410 0x43f7fbdef0008088 0xfffffffc01c1c67f 0xdffffffff803838c

def z42 : W := mkw 0x0855ef7800000000 0x4010abdef0000000 0x1cfffff80000003d 0x4039fffff0000000

def z43 : W := mkw 0x0c170c2440989a42 0x04182e1848813134 0x1c3e0c6040383e79 0x0c387c18c080707c

def z44 : W := mkw 0x82c0a05000000000 0x01058140a0000000 0x80c1f00000000004 0x030183e000000000

def z45 : W := mkw 0x0000100080050000 0x0000002001000a00 0x8001f0078007c067 0x770003e00f000f80

def z46 : W := mkw 0xdec1fad7ed47f578 0x1bbd83f5afda8fea 0xffc1ffffffc7ffff 0xffff83ffffff8fff

def z47 : W := mkw 0x0040804000404410 0x0000810080008088 0x00c1800401c1c004 0x1001830008038380

def z48 : W := mkw 0x0000000012200000 0x0000000000244000 0x000000007e380040 0x2800000000fc7000

def z49 : W := mkw 0x0402000440900000 0x0008040008812000 0x1cce000401c00004 0x10399c0008038000

def z50 : W := mkw 0xf3b8052800000000 0x03e7700a50000000 0xfffe0ff80000003f 0xc3fffc1ff0000000

def z51 : W := mkw 0x04001086e807b060 0x100800210dd00f60 0x00000007f807f840 0x340000000ff00ff0

def z52 : W := mkw 0xdecfea5440d0d452 0x47bd9fd4a881a1a8 0x9ccff00401c1c004 0x13399fe008038380

def z53 : W := mkw 0xfbfdfff88807b060 0x53f7fbfff1100f60 0xfffffff80007f83f 0xc7fffffff0000ff0

def z54 : W := mkw 0x0402000777b00000 0x200804000eef6000 0x00000007fff80040 0x380000000ffff000

def z55 : W := mkw 0xf3a8000000000000 0x03e7500000000000 0xfffe00000000001f 0x83fffc0000000000

def z56 : W := mkw 0x0c01080440009040 0x0018021008800120 0x1c0180040001c004 0x1038030008000380

def z57 : W := mkw 0x5c57cee668dafe72 0x16b8af9dccd1b5fc 0x7cff8fe479f9fe7d 0x9cf9ff1fc8f3f3fc

def z58 : W := mkw 0x79314fa81a2a2a84 0x02f2629f50345455 0xff31fff87e3e3fff 0xeffe63fff0fc7c7f

def z59 : W := mkw 0x8280201105000108 0x09050040220a0002 0x0300001806000180 0x00060000300c0003

def z60 : W := mkw 0x00001082a8072020 0x1000002105500e40 0x00000003b8060000 0x2000000007700c00

def z61 : W := mkw 0x213005a81a222084 0x0042600b50344441 0x63300ff83e0601bb 0xe0c6601ff07c0c03

def z62 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0xfccfff800000002f 0xc3f99fff00000000

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000078060607f3 0x6c060000f00c0c0f

def z64 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x80c1f00781c1c004 0x130183e00f038380

def z65 : W := mkw 0x08015a808807b060 0x101002b501100f60 0x0001ff800007f820 0x440003ff00000ff0

def z66 : W := mkw 0x5400000660000000 0x02a800000cc00000 0xfc000007f800004f 0xb3f800000ff00000

def z67 : W := mkw 0xa3aa000117b00000 0x21475400022f6000 0x03fe000007f80010 0x0807fc00000ff000

def z68 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x00018c6441f9fe60 0x1c000318c883f3fc

def z69 : W := mkw 0x0040804000404410 0x0000810080008088 0x000180600001c620 0x04000300c000038c

def z70 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xe301fff800000022 0xc3c603fff0000000

def z71 : W := mkw 0x2120000012200000 0x0042400000244000 0x633000007e38005b 0xa8c6600000fc7000

def z72 : W := mkw 0xfbfdef7812200000 0x43f7fbdef0244000 0xfffffff87e38007f 0xebfffffff0fc7000

def z73 : W := mkw 0xde8b5a87ed97b060 0x33bd16b50fdb2f60 0xfccfff87f9c7f86f 0xf7f99fff0ff38ff0

def z74 : W := mkw 0x213015a99f6f6f9c 0x0842602b533ededf 0x63300ffffffffffb 0xfcc6601fffffffff

def z75 : W := mkw 0x8ec7b855c5d5d55a 0x0d1d8f70ab8babaa 0x9ccff00781c1c004 0x13399fe00f038380

def z76 : W := mkw 0x7d314fae7a2abae4 0x12fa629f5cf45575 0x7c300f8078383808 0x80f8601f00f07070

def z77 : W := mkw 0xffffef7f65900000 0x63ffffdefecb2000 0xffffffff81c0003f 0xd3ffffffff038000

def z78 : W := mkw 0xfbfdff7985454518 0x4bf7fbfef30a8a8a 0xffffffff87c7c7ff 0xffffffffff0f8f8f

def z79 : W := mkw 0xfffdffffed47f578 0x5bfffbffffda8fea 0xffffffffffc7ffff 0xffffffffffff8fff

def z80 : W := mkw 0xd288000325000000 0x23a51000064a0000 0x8000000380000000 0x0300000007000000

def z81 : W := mkw 0xffff8c6777f8de52 0x27ffff18ceeff1bc 0xffff8c67fff9fe7f 0xbfffff18cffff3fc

def z82 : W := mkw 0xffbb5fafffbfbae4 0x33ff76bf5fff7f75 0xffffffffffffffff 0xffffffffffffffff

def z83 : W := mkw 0x752a000672b00000 0x22ea54000ce56000 0x7c3e000078380008 0x80f87c0000f07000

def z84 : W := mkw 0x8280000105000000 0x01050000020a0000 0x83c0000787c00057 0x3b0780000f0f8000

def z85 : W := mkw 0x0040804000404410 0x0000810080008088 0x00c1806401c1c675 0x1c018300c803838c

def z86 : W := mkw 0x8ed7bc75c5dddf5a 0x0d1daf78eb8bbbbe 0x9ffffc7fc7ffffff 0x7f3ffff8ff8fffff

def z87 : W := mkw 0x0402000777f8de52 0x240804000eeff1bc 0x00000007fff9fe40 0x3c0000000ffff3fc

def z88 : W := mkw 0xfba94a0000000000 0x03f7529400000000 0xffffff800000003f 0xc3ffffff00000000

def z89 : W := mkw 0x8280301185050108 0x09050060230a0a02 0x8000700380000000 0x030000e007000000

def z90 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x60300f8078383808 0x80c0601f00f07070

def z91 : W := mkw 0x2d778dec5afafed6 0x045aef1bd8b5f5fd 0x7cff8fe479f9fe7d 0x9cf9ff1fc8f3f3fc

def z92 : W := mkw 0x5c014a866802b060 0x12b802950cd00560 0x7c018f847801f86d 0x94f8031f08f003f0

def z93 : W := mkw 0x0456846440d84e12 0x0408ad08c881b09c 0x1cfe006441f8065d 0x1839fc00c883f00c

def z94 : W := mkw 0x29315fa89a2fbae4 0x105262bf51345f75 0x6331fff87e3ffffb 0xecc663fff0fc7fff

def z95 : W := mkw 0x82c0a05105000000 0x01058140a20a0000 0x83c1f07f87c00077 0x7b0783e0ff0f8000

def z96 : W := mkw 0xf3a8000337200000 0x23e75000066e4000 0xfffe0003be00001f 0xa3fffc00077c0000

def z97 : W := mkw 0x0402000440d8de52 0x040804000881b1bc 0x0000000441f9fe40 0x1c0000000883f3fc

def z98 : W := mkw 0xf3e8f35985454518 0x4be7d1e6b30a8a8a 0xe3c1f3ff87c7c7f7 0xffc783e7ff0f8f8f

def z99 : W := mkw 0x0456846440d8de52 0x0408ad08c881b1bc 0x00fe006441f9fe50 0x1c01fc00c883f3fc

def z100 : W := mkw 0xf7eab057f7f54518 0x2befd560afefea8a 0xfffff07fffffc7ff 0xffffffe0ffffff8f

def z101 : W := mkw 0x7d77dfeefafffef6 0x16faefbfddf5fffd 0xffffffffffffffff 0xffffffffffffffff

def z102 : W := mkw 0x752a000672b00000 0x22ea54000ce56000 0x7cfe000479f8005d 0x98f9fc0008f3f000

def z103 : W := mkw 0xde815a87ed07b060 0x13bd02b50fda0f60 0xffc1ff87ffc7f87f 0xffff83ff0fff8ff0

def z104 : W := mkw 0xfbfdeff81a2a2a84 0x43f7fbdff0345455 0xfffffff87e3e3fff 0xeffffffff0fc7c7f

def z105 : W := mkw 0xfbfdef7905404518 0x4bf7fbdef20a808a 0xfffffff807c007bf 0xcbfffffff00f800f

def z106 : W := mkw 0x797def7800000000 0x42f2fbdef0000000 0x7c3ffff800000028 0xc0f87ffff0000000

def z107 : W := mkw 0x0855ef7800000000 0x4010abdef0000000 0x0001fff800000020 0x400003fff0000000

def z108 : W := mkw 0xfbfdeff81a222084 0x43f7fbdff0344441 0xfffffff83e0601bf 0xe3fffffff07c0c03

def z109 : W := mkw 0x2130052812280a84 0x0042600a50245015 0x0330007806380790 0x08066000f00c700f

def z110 : W := mkw 0xd6cab057e5d54518 0x2bad9560afcbaa8a 0x9fcff07f87c7c7f7 0x7f3f9fe0ff0f8f8f

def z111 : W := mkw 0x000000801a222084 0x0000000100344441 0x000000003e060180 0x20000000007c0c03

def z112 : W := mkw 0x0402000440900000 0x0008040008812000 0x0000000441f80040 0x180000000883f000

def z113 : W := mkw 0x753a05ae7aba2a84 0x22ea740b5cf57455 0x7f3e0ff87e3e3ffb 0xecfe7c1ff0fc7c7f

def z114 : W := mkw 0xa3f0a5f81a2a2a84 0x0147e14bf0345455 0xe3f1fff87e3e3fff 0xefc7e3fff0fc7c7f

def z115 : W := mkw 0x0000008008022000 0x0000000100100440 0x60000f807806386b 0xe4c0001f00f00c70

def z116 : W := mkw 0x000000801a2a2a84 0x0000000100345455 0x000000007e3e3fc0 0x2c00000000fc7c7f

def z117 : W := mkw 0x08014a0000000000 0x0010029400000000 0x0001ff8000000020 0x400003ff00000000

def z118 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xff3e0003fe38000a 0xa3fe7c0007fc7000

def z119 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe007ffffe07ff 0xfffffc00fffffc0f

def z120 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x80c1f00787c7c7c4 0x3f0183e00f0f8f8f

def z121 : W := mkw 0x82c0b05080050000 0x01058160a1000a00 0x83c1f07f8007c077 0x770783e0ff000f80

def z122 : W := mkw 0xfbfdef780048de52 0x47f7fbdef00091bc 0xfffffff80001fe3f 0xc7fffffff00003fc

def z123 : W := mkw 0x0c47884440d0d452 0x04188f108881a1a8 0x1ccf800401c1c004 0x10399f0008038380

def z124 : W := mkw 0x212001881a222084 0x0042400310344441 0x630003983e060182 0xe0c60007307c0c03

def z125 : W := mkw 0xf3b867b81a2a2a84 0x43e770cf70345455 0xe3307ff87e3e3ffb 0xefc660fff0fc7c7f

def z126 : W := mkw 0x0c011804c0059040 0x0018023009800b20 0x9c01fc07c007f86f 0x773803f80f800ff0

def z127 : W := mkw 0x212a000012b00000 0x2042540000256000 0x003e000000380000 0x00007c0000007000

def z128 : W := mkw 0x0000108088072000 0x0000002101100e40 0xe001ff87f807f86f 0xf7c003ff0ff00ff0

def z129 : W := mkw 0x8280000105000000 0x01050000020a0000 0x80c0000781c00004 0x130180000f038000

def z130 : W := mkw 0x0010042000080a00 0x0000200840001014 0x00300c6040383e79 0x0c006018c080707c

def z131 : W := mkw 0x2d778dec5afafed6 0x045aef1bd8b5f5fd 0x7fff8ffc7fffffff 0xfcffff1ff8ffffff

def z132 : W := mkw 0x8280201000000000 0x0105004020000000 0x8300701800000002 0x430600e030000000

def z133 : W := mkw 0x7d315faefa2fbae4 0x12fa62bf5df45f75 0xff31fffffe3fffff 0xfffe63fffffc7fff

def z134 : W := mkw 0x79314f2800000000 0x02f2629e50000000 0xff31fff80000003f 0xc3fe63fff0000000

def z135 : W := mkw 0xdec1fa57e545d578 0x1bbd83f4afca8baa 0x9fc1f07f87c7c7f7 0x7f3f83e0ff0f8f8f

def z136 : W := mkw 0x82c0b0d19f6f6f9c 0x09058161a33ededf 0x83c1f07ffffffff7 0x7f0783e0ffffffff

def z137 : W := mkw 0xa3b035b99f2f2b8c 0x0947606b733e5e57 0xe3307ffbfe3e3ffb 0xefc660fff7fc7c7f

def z138 : W := mkw 0x82c0a05105404518 0x09058140a20a808a 0x03c0007807c607f3 0x6c078000f00f8c0f

def z139 : W := mkw 0xa3f0a57917684f9c 0x0947e14af22ed09f 0x03f0007807f80790 0x0807e000f00ff00f

def z140 : W := mkw 0x08558c6000080a00 0x0010ab18c0001014 0x1cff8c6040383e7d 0x0c39ff18c080707c

def z141 : W := mkw 0x0400000660000000 0x000800000cc00000 0x00000007f8000040 0x300000000ff00000

def z142 : W := mkw 0x0c170c2440989a42 0x04182e1848813134 0x1c3e0c0040383808 0x00387c1800807070

def z143 : W := mkw 0x001005a8080a2a84 0x0000200b50101455 0x00000ff800063fa0 0x4400001ff0000c7f

def z144 : W := mkw 0x86c2b057f7f54518 0x290d8560afefea8a 0x83c1f07fffffc7f7 0x7f0783e0ffffff8f

def z145 : W := mkw 0x8280301185050108 0x09050060230a0a02 0x8300701b86060182 0x630600e0370c0c03

def z146 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0x9c01ff878007f824 0x573803ff0f000ff0

def z147 : W := mkw 0xa3fca5f81a2a2a84 0x4147f94bf0345455 0x63fe0ff87e3e3ffb 0xecc7fc1ff0fc7c7f

def z148 : W := mkw 0x82c0a05000000000 0x01058140a0000000 0x83c1f07800000037 0x430783e0f0000000

def z149 : W := mkw 0x0000100185454518 0x08000020030a8a8a 0x0000000787c7c7c0 0x3c0000000f0f8f8f

def z150 : W := mkw 0x0c015a86e807b060 0x101802b50dd00f60 0x0001ff87f807f860 0x740003ff0ff00ff0

def z151 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x633003f83e3e0792 0xe8c66007f07c7c0f

def z152 : W := mkw 0x0000008008022000 0x0000000100100440 0x60000f8078003808 0x80c0001f00f00070

def z153 : W := mkw 0x82d0b5f98d4f6f9c 0x0905a16bf31a9edf 0x83c1ffff87c7fff7 0x7f0783ffff0f8fff

def z154 : W := mkw 0xf3aa000117b00000 0x23e75400022f6000 0xfffe000007f8001f 0x8bfffc00000ff000

def z155 : W := mkw 0xfbbd6f3800000000 0x43f77ade70000000 0xff3e7f980000000a 0xc3fe7cff30000000

def z156 : W := mkw 0x5c015a06e0059060 0x12b802b40dc00b20 0x9c01f0078001c004 0x133803e00f000380

def z157 : W := mkw 0xd6c0b057e5454518 0x0bad8160afca8a8a 0xffc1f07fffc7c7ff 0xffff83e0ffff8f8f

def z158 : W := mkw 0x0040b05080454518 0x08008160a1008a8a 0x0001f0780007c7a0 0x440003e0f0000f8f

def z159 : W := mkw 0x253205ac5aba2a84 0x004a640b58b57455 0x7ffe0ffc7ffe3fff 0xfcfffc1ff8fffc7f

def z160 : W := mkw 0x5c55dee6e84ffe72 0x16b8abbdcdd09ffc 0xfc01ffe7f807fe6f 0xf7f803ffcff00ffc

def z161 : W := mkw 0x2120000012200000 0x0042400000244000 0x6030000078380008 0x80c0600000f07000

def z162 : W := mkw 0x0c578c6440900000 0x0018af18c8812000 0x1cff8c6441f8007d 0x1839ff18c883f000

def z163 : W := mkw 0x0000100080050000 0x0000002001000a00 0x8000700380060002 0x630000e007000c00

def z164 : W := mkw 0x0040904080454410 0x0000812081008a88 0x80c1f06781c7c677 0x7f0183e0cf038f8c

def z165 : W := mkw 0x000000000048de52 0x04000000000091bc 0x000000000001fe00 0x04000000000003fc

def z166 : W := mkw 0xd2807293ad072128 0x1ba500e5275a0e42 0xe300739bbe060182 0xe3c600e7377c0c03

def z167 : W := mkw 0xfbfdef7800080a00 0x43f7fbdef0001014 0xfffffff840383e7f 0xcffffffff080707c

def z168 : W := mkw 0x5855ce6000000000 0x02b0ab9cc0000000 0xfcffffe00000003f 0xc3f9ffffc0000000

def z169 : W := mkw 0x2d778d6c52f8ded6 0x045aef1ad8a5f1bd 0x1fff8c7c47f9fffd 0x1c3fff18f88ff3ff

def z170 : W := mkw 0x0855eff8080a2a84 0x4010abdff0101455 0x0001fff800063fa0 0x440003fff0000c7f

def z171 : W := mkw 0x0040b05080454518 0x08008160a1008a8a 0x0301f0780607c7f3 0x6c0603e0f00c0f8f

def z172 : W := mkw 0xdec1fad6e807b060 0x13bd83f5add00f60 0xffc1fffff807f87f 0xf7ff83fffff00ff0

def z173 : W := mkw 0xf7aa3017f7b50108 0x2bef54602fef6a02 0xfffe701ffffe01df 0xfbfffce03ffffc03

def z174 : W := mkw 0xfbfdef7b37200000 0x63f7fbdef66e4000 0xfffffffbbe00003f 0xe3fffffff77c0000

def z175 : W := mkw 0x54005286e807b060 0x12a800a50dd00f60 0xe0007387f807f842 0xf7c000e70ff00ff0

def z176 : W := mkw 0x0402000777b00000 0x200804000eef6000 0x1cfe0007fff8005d 0x3839fc000ffff000

def z177 : W := mkw 0xfbedea5000000000 0x43f7dbd4a0000000 0xfffff0000000001f 0x83ffffe000000000

def z178 : W := mkw 0x08558c6000404410 0x0010ab18c0008088 0x1cff8c6401c1c67d 0x1c39ff18c803838c

def z179 : W := mkw 0xffffef7c40989a42 0x47ffffdef8813134 0xfffffff84038383f 0xc3fffffff0807070

def z180 : W := mkw 0x0c57ef7c40d8de52 0x4418afdef881b1bc 0x1cfffffc41f9fe7d 0x5c39fffff883f3fc

def z181 : W := mkw 0xffef884777f0d452 0x27ffdf108eefe1a8 0xffff8007fff9c05f 0xbbffff000ffff380

def z182 : W := mkw 0xf7eaa05777b00000 0x23efd540aeef6000 0xfffff07ffff8007f 0xfbffffe0fffff000

def z183 : W := mkw 0xfbfdfffaa8072020 0x53f7fbfff5500e40 0xfffffffbb806003f 0xe3fffffff7700c00

def z184 : W := mkw 0x54005286e8072020 0x12a800a50dd00e40 0xfc007387f806004f 0xf3f800e70ff00c00

def z185 : W := mkw 0xfffdfffee807b060 0x53fffbfffdd00f60 0xfffffffff807f87f 0xf7fffffffff00ff0

def z186 : W := mkw 0x793d4fa81a2a2a84 0x42f27a9f50345455 0x7f3e0ff87e3e3ffb 0xecfe7c1ff0fc7c7f

def z187 : W := mkw 0x217685e81afa6e96 0x0442ed0bd035f4dd 0x63fe0ff87ffe3ffb 0xecc7fc1ff0fffc7f

def z188 : W := mkw 0x08558c600048de52 0x0410ab18c00091bc 0x00018c600001fe20 0x04000318c00003fc

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300007806000790 0x08060000f00c000f

def z190 : W := mkw 0xdecfea5765900000 0x63bd9fd4aecb2000 0x9ccff00781c00004 0x13399fe00f038000

def z191 : W := mkw 0x213005a8080a2a84 0x0042600b50101455 0x63300ff800063fbb 0xc4c6601ff0000c7f

def z192 : W := mkw 0xf7a8000777200000 0x23ef50000eee4000 0xff000007fe00004f 0xb3fe00000ffc0000

def z193 : W := mkw 0x5c175ea6e89fba62 0x16b82ebd4dd13f74 0xfc3fff87f83ff86f 0xf7f87fff0ff07ff0

def z194 : W := mkw 0x5400000660000000 0x02a800000cc00000 0x7c00000078000008 0x80f8000000f00000

def z195 : W := mkw 0xf7aa1087ffb7b060 0x33ef54210fff6f60 0xfffe0007fffff85f 0xbffffc000ffffff0

def z196 : W := mkw 0x0c07080440909042 0x04180e1008812120 0x1c0e000000000000 0x00381c0000000000

def z197 : W := mkw 0xd68a000777b00000 0x23ad14000eef6000 0x9cce0007fff80044 0x3b399c000ffff000

def z198 : W := mkw 0x0c47884440d0d452 0x04188f108881a1a8 0x1ccf806401c1c675 0x1c399f00c803838c

def z199 : W := mkw 0xa3ba05a91fba2a84 0x2147740b523f7455 0x63fe0ff87ffe3ffb 0xecc7fc1ff0fffc7f

def z200 : W := mkw 0x29758d6800000000 0x0052eb1ad0000000 0x7fff8ff80000003f 0xc0ffff1ff0000000

def z201 : W := mkw 0xd288621000000000 0x43a510c420000000 0x8000700000000000 0x030000e000000000

def z202 : W := mkw 0xffffef7c40d0d452 0x47ffffdef881a1a8 0xfffffffc01c1c03f 0xd3fffffff8038380

def z203 : W := mkw 0xffab080777b09040 0x23ff56100eef6120 0xffff8c07fff9f87f 0xbfffff180ffff3f0

def z204 : W := mkw 0xffa95a86e807b060 0x13ff52b50dd00f60 0xffffff87f807f87f 0xf7ffffff0ff00ff0

def z205 : W := mkw 0x5c57dee6e8dffe72 0x16b8afbdcdd1bffc 0xfcffffe7f9fffe7f 0xfff9ffffcff3fffc

def z206 : W := mkw 0xde817a97ed07b168 0x1bbd02f52fda0f62 0xff01ff9ffe07f9ef 0xf7fe03ff3ffc0ff3

def z207 : W := mkw 0x8280301185454518 0x09050060230a8a8a 0x8300701f87c7c7c2 0x7f0600e03f0f8f8f

def z208 : W := mkw 0x04001006e0059060 0x100800200dc00b20 0x000000078001c000 0x100000000f000380

def z209 : W := mkw 0x82c0a05000000000 0x01058140a0000000 0x03c0007800000010 0x00078000f0000000

def z210 : W := mkw 0xdacdfa5185454518 0x4bb59bf4a30a8a8a 0x9ccff00781c1c004 0x13399fe00f038380

def z211 : W := mkw 0x0c57bc74c0dddf5a 0x0c18af78e981bbbe 0x1cfffc7c41fffffd 0x5c39fff8f883ffff

def z212 : W := mkw 0xa3fca57800000000 0x4147f94af0000000 0x03fe007800000010 0x0007fc00f0000000

def z213 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c0707b87c60792 0x6b0780e0f70f8c0f

def z214 : W := mkw 0x2130052812280a84 0x0042600a50245015 0x03300c7846383ff9 0x0c066018f08c707f

def z215 : W := mkw 0x82cca05000000000 0x41059940a0000000 0x00ce000000000000 0x00019c0000000000

def z216 : W := mkw 0x000010819f6f6f9c 0x08000021033ededf 0x00000007ffffffc0 0x3c0000000fffffff

def z217 : W := mkw 0xffffbc77f7fddf5a 0x2fffff78efeffbbe 0xfffffc7fffffffff 0xfffffff8ffffffff

def z218 : W := mkw 0x5400008668022000 0x02a800010cd00440 0xfc000f87f806386f 0xf7f8001f0ff00c70

def z219 : W := mkw 0xf3a8000012200000 0x03e7500000244000 0xfffe00007e38005f 0xabfffc0000fc7000

def z220 : W := mkw 0xdac1fa5185454518 0x0bb583f4a30a8a8a 0xffc1ffff87c7c7ff 0xffff83ffff0f8f8f

def z221 : W := mkw 0x0801080000000000 0x0010021000000000 0x1c018c000000002d 0x0038031800000000

def z222 : W := mkw 0x212001881a222084 0x0042400310344441 0x63000f987e0639eb 0xe4c6001f30fc0c73

def z223 : W := mkw 0x7128000232200000 0x22e2500004644000 0x6000000038000000 0x80c0000000700000

def z224 : W := mkw 0x0801080000009040 0x0010021000000120 0x00018c000001f820 0x04000318000003f0

def z225 : W := mkw 0x5c035a86e897b060 0x12b806b50dd12f60 0xfcffff87f9fff87f 0xfff9ffff0ff3fff0

def z226 : W := mkw 0x8ed7ac7440d8de52 0x051daf58e881b1bc 0x9ffffc7c41f9fe7f 0x5f3ffff8f883f3fc

def z227 : W := mkw 0x50005202a0050020 0x12a000a405400a00 0x8000700380000000 0x030000e007000000

def z228 : W := mkw 0x2d370dac5ababac6 0x045a6e1b58b57575 0x7c3e0f8078383808 0x80f87c1f00f07070

def z229 : W := mkw 0xa3fea57800d84e12 0x4547fd4af001b09c 0x03fe007801f80610 0x0807fc00f003f00c

def z230 : W := mkw 0x212000801a222000 0x0042400100344440 0x63300f807e3e387b 0xecc6601f00fc7c70

def z231 : W := mkw 0x001005a81a2a2a84 0x0000200b50345455 0x00000ff87e3e3fe0 0x6c00001ff0fc7c7f

def z232 : W := mkw 0xd68a000765900000 0x23ad14000ecb2000 0x9fce000787c00057 0x3b3f9c000f0f8000

def z233 : W := mkw 0x2130042012280a00 0x0042600840245014 0x63300c607e383e7b 0xacc66018c0fc707c

def z234 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300000006000053 0x28060000000c0000

def z235 : W := mkw 0xffffdee7fffffe72 0x37ffffbdcffffffc 0xffffffe7fffffe7f 0xffffffffcffffffc

def z236 : W := mkw 0xf7aa00877fb22000 0x23ef54010eff6440 0xfffe0f87fffe387f 0xfffffc1f0ffffc70

def z237 : W := mkw 0x82c0a05105404518 0x09058140a20a808a 0x83c0007f87c007d7 0x3b078000ff0f800f

def z238 : W := mkw 0x0056846000d84e12 0x0400ad08c001b09c 0x00fe006001f80610 0x0801fc00c003f00c

def z239 : W := mkw 0xa3fe846117f84e12 0x2547fd08c22ff09c 0x03fe006007f80610 0x0807fc00c00ff00c

def z240 : W := mkw 0x2130052812200000 0x0042600a50244000 0x63300ff87e38007b 0xe8c6601ff0fc7000

def z241 : W := mkw 0x0000000000000000 0x0000000000000000 0x1cfe00000000001d 0x0039fc0000000000

def z242 : W := mkw 0x82c0804105404410 0x01058100820a8088 0x83c1806787c1c677 0x3f078300cf0f838c

def z243 : W := mkw 0xd68a000765900000 0x23ad14000ecb2000 0xfcce0007f9c0004f 0xb3f99c000ff38000

def z244 : W := mkw 0x0056846000d84e12 0x0400ad08c001b09c 0x00fe0c6041f83e79 0x0c01fc18c083f07c

def z245 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f81c1c037 0x530783e0ff038380

def z246 : W := mkw 0x08558c600048de52 0x0410ab18c00091bc 0x00318c604039fe79 0x0c006318c08073fc

def z247 : W := mkw 0x82c0a05000000000 0x01058140a0000000 0x83c1f078060607f7 0x6f0783e0f00c0c0f

def z248 : W := mkw 0xfbfdff7880050000 0x43f7fbfef1000a00 0xffffffff8007c07f 0xf7ffffffff000f80

def z249 : W := mkw 0xdec1fa57e545d578 0x1bbd83f4afca8baa 0x9cc1f00781c1c004 0x133983e00f038380

def z250 : W := mkw 0xffffef7e72b00000 0x63ffffdefce56000 0xfffffff87838003f 0xc3fffffff0f07000

def z251 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff806401f9c614 0x1839ff00c803f38c

def z252 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff8060607ff 0xeffffffff00c0c0f

def z253 : W := mkw 0xa3b005a91f2a2a84 0x0147600b523e5455 0xe3f00ffffffe3fff 0xffc7e01ffffffc7f

def z254 : W := mkw 0xffff8c6440d8de52 0x07ffff18c881b1bc 0xffff8c6441f9fe7f 0x9fffff18c883f3fc

def z255 : W := mkw 0x0855dee0884ffe72 0x1410abbdc1109ffc 0x0001ffe00007fe20 0x440003ffc0000ffc

def z256 : W := mkw 0xf3a85283bf272020 0x33e750a5077e4e40 0xe3007383be060002 0xe3c600e7077c0c00

def z257 : W := mkw 0x0c57dee4c8dffe72 0x1418afbdc991bffc 0x1cffffe441fffe7d 0x5c39ffffc883fffc

def z258 : W := mkw 0xafffad7c40d8de52 0x455fff5af881b1bc 0x1fff8c7c41f9fe7d 0x1c3fff18f883f3fc

def z259 : W := mkw 0x8682000777b00000 0x210d04000eef6000 0x83c00007fff80057 0x3b0780000ffff000

def z260 : W := mkw 0x5c174ea6689aba62 0x16b82e9d4cd13574 0x7c3e0f8078383808 0x80f87c1f00f07070

def z261 : W := mkw 0xf3a8731985050108 0x4be750e6330a0a02 0xe300739b86060182 0xe3c600e7370c0c03

def z262 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x03c0007f87c7c7d0 0x3c078000ff0f8f8f

def z263 : W := mkw 0x0845884000000000 0x00108b1080000000 0x1ccf800000000004 0x00399f0000000000

def z264 : W := mkw 0xd680000765000000 0x03ad00000eca0000 0xffc00007ffc0005f 0xbbff80000fff8000

def z265 : W := mkw 0xf7aa1007f7f54518 0x2bef54200fefea8a 0xfffe0007ffffc7df 0xbffffc000fffff8f

def z266 : W := mkw 0x2522000452b00000 0x004a440008a56000 0x7ffe00047ff8005f 0xb8fffc0008fff000

def z267 : W := mkw 0xf7fe846777f84e12 0x27effd08ceeff09c 0xfffe0067fff8065f 0xbbfffc00cffff00c

def z268 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfcfe0007f9f8000c 0x93f9fc000ff3f000

def z269 : W := mkw 0xafff8c6557f8de52 0x255fff18caaff1bc 0x1fff8c6447f9fe7d 0x1c3fff18c88ff3fc

def z270 : W := mkw 0xf7ea804777f04410 0x23efd5008eefe088 0xffff8067fff9c67f 0xbfffff00cffff38c

def z271 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1fff8c7c47ffffff 0x7c3fff18f88fffff

def z272 : W := mkw 0x040200877fba2a84 0x200804010eff7455 0x00000007fffe3fc0 0x3c0000000ffffc7f

def z273 : W := mkw 0x04021086e8dffe72 0x140804210dd1bffc 0x00000007f9fffe40 0x3c0000000ff3fffc

def z274 : W := mkw 0xfbedeb5800000000 0x43f7dbd6b0000000 0xffcff39800000006 0xc3ff9fe730000000

def z275 : W := mkw 0xfffdeffe6802b060 0x53fffbdffcd00560 0xfffffff87800383f 0xc3fffffff0f00070

def z276 : W := mkw 0x0010042000000000 0x0000200840000000 0x00300c6000000039 0x00006018c0000000

def z277 : W := mkw 0xfbfdfff99f6f6f9c 0x4bf7fbfff33ededf 0xffffffffffffffff 0xffffffffffffffff

def z278 : W := mkw 0xf7ba05af7fba2a84 0x23ef740b5eff7455 0xfffe0ffffffe3fff 0xfffffc1ffffffc7f

def z279 : W := mkw 0x86c0b0d7ed47f578 0x190d8161afda8fea 0x83c1f07fffc7fff7 0x7f0783e0ffff8fff

def z280 : W := mkw 0x0010042000080a00 0x0000200840001014 0x00000c6000003e20 0x04000018c000007c

def z281 : W := mkw 0xf7aa5287ffb72020 0x33ef54a50fff6e40 0xfffe7387fffe005f 0xfbfffce70ffffc00

def z282 : W := mkw 0x5c035a87ffb7b060 0x32b806b50fff6f60 0xfc01ff87fffff86f 0xfff803ff0ffffff0

def z283 : W := mkw 0x7d7f8c6672f8de52 0x26faff18cce5f1bc 0x7cff8c6479f9fe7d 0x9cf9ff18c8f3f3fc

def z284 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030000040380059 0x0800600000807000

def z285 : W := mkw 0x0000100185454518 0x08000020030a8a8a 0x0300007f87c7c7f3 0x7c060000ff0f8f8f

def z286 : W := mkw 0x0000000000080a00 0x0000000000001014 0x0000000040383e40 0x0c0000000080707c

def z287 : W := mkw 0x212001881a2a2a84 0x0042400310345455 0x630003987e3e3fc2 0xecc6000730fc7c7f

def z288 : W := mkw 0xfbfdff7985050108 0x4bf7fbfef30a0a02 0xfffffffb860601bf 0xe3fffffff70c0c03

def z289 : W := mkw 0xf7aa631f77b00000 0x63ef54c63eef6000 0xfffe739ffff8005f 0xfbfffce73ffff000

def z290 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0xfc3fff800000002f 0xc3f87fff00000000

def z291 : W := mkw 0xffff8c6777b00000 0x23ffff18ceef6000 0xffff8c67fff8007f 0xbbffff18cffff000

def z292 : W := mkw 0x0000008008022000 0x0000000100100440 0x00000f8000063820 0x4400001f00000c70

def z293 : W := mkw 0x5c015a06e0059060 0x12b802b40dc00b20 0x9c01f0078007c067 0x773803e00f000f80

def z294 : W := mkw 0x0c579c64c0ddde52 0x0418af38c981bbbc 0x9cfffc67c1fffe7f 0x7f39fff8cf83fffc

def z295 : W := mkw 0x217085e81a6a6e94 0x0042e10bd034d4dd 0x63f18ffc7fffffff 0xfcc7e31ff8ffffff

def z296 : W := mkw 0xfbfd8c6000000000 0x03f7fb18c0000000 0xffff8c600000003f 0x83ffff18c0000000

def z297 : W := mkw 0x5c035a86e8dffe72 0x16b806b50dd1bffc 0xfc01ff87f9fffe6f 0xfff803ff0ff3fffc

def z298 : W := mkw 0xf3e8b053b7654518 0x2be7d160a76eca8a 0xe3c1f07fbfc7c7f7 0xffc783e0ff7f8f8f

def z299 : W := mkw 0x5c014a0660009060 0x12b802940cc00120 0x1c00000000000000 0x0038000000000000

def z300 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x8301f07b8607c7a2 0x670603e0f70c0f8f

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300007800000033 0x40060000f0000000

def z302 : W := mkw 0x5c57ce6440d8de52 0x06b8af9cc881b1bc 0xfcffffe441f9fe7f 0xdff9ffffc883f3fc

def z303 : W := mkw 0x0c578c6777f8de52 0x2418af18ceeff1bc 0x1cff8c67fff9fe7d 0x3c39ff18cffff3fc

def z304 : W := mkw 0x0000000000404410 0x0000000000008088 0x0000000401c1c640 0x1c0000000803838c

def z305 : W := mkw 0xa3e0b1d99f67659c 0x0947c163b33ececb 0xe3c1f3ffbfc7c7f7 0xffc783e7ff7f8f8f

def z306 : W := mkw 0xa7aa000777b00000 0x214f54000eef6000 0x03fe0007fff80050 0x3807fc000ffff000

def z307 : W := mkw 0x5c015a87ed47f578 0x1ab802b50fda8fea 0xfc01ff87ffc7ffef 0xfff803ff0fff8fff

def z308 : W := mkw 0x0855bc70804ddf5a 0x0c10ab78e1009bbe 0x0001fc780007ffa0 0x440003f8f0000fff

def z309 : W := mkw 0x5c55dee6e807b060 0x12b8abbdcdd00f60 0xfcffffe7f807f87f 0xf7f9ffffcff00ff0

def z310 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f801f80c 0x93f803ff0ff003f0

def z311 : W := mkw 0xfbfdff7985454518 0x4bf7fbfef30a8a8a 0xffffffff81c1c03f 0xd3ffffffff038380

def z312 : W := mkw 0xffffeffc5afafed6 0x47ffffdff8b5f5fd 0xfffffffc7fffffff 0xfffffffff8ffffff

def z313 : W := mkw 0x58015a82a807b060 0x12b002b505500f60 0xe001ff83b807f822 0xe7c003ff07700ff0

def z314 : W := mkw 0xffffffffffb7b060 0x73ffffffffff6f60 0xfffffffffffff87f 0xfffffffffffffff0

def z315 : W := mkw 0x5402000777b00000 0x22a804000eef6000 0xfc000007fff8004f 0xbbf800000ffff000

def z316 : W := mkw 0x8ac1fad18d47f578 0x191583f5a31a8fea 0x83c1ffff87c7fff7 0x7f0783ffff0f8fff

def z317 : W := mkw 0x0040b05080454518 0x08008160a1008a8a 0x8001f07f8007c7e7 0x770003e0ff000f8f

def z318 : W := mkw 0x04001086e807b060 0x100800210dd00f60 0x8001f007f807f867 0x770003e00ff00ff0

def z319 : W := mkw 0x2130052800080a00 0x0042600a50001014 0x63300ff840383e7b 0xccc6601ff080707c

def z320 : W := mkw 0x0c47884440d0d452 0x04188f108881a1a8 0x1ccf8c0441c1f86d 0x14399f18088383f0

def z321 : W := mkw 0x00000080080a2a84 0x0000000100101455 0x0000000000063f80 0x0400000000000c7f

def z322 : W := mkw 0x7d215b8efa27b0e4 0x12fa42b71df44f61 0xff01ff9ffe07f9ef 0xf7fe03ff3ffc0ff3

def z323 : W := mkw 0x2130052800000000 0x0042600a50000000 0x60300f8000000008 0x80c0601f00000000

def z324 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f00787c1c057 0x3b0783e00f0f8380

def z325 : W := mkw 0xa3fcb57985454518 0x4947f96af30a8a8a 0x83fff07f87c7c7f7 0x7f07ffe0ff0f8f8f

def z326 : W := mkw 0xfffdef7c40009040 0x43fffbdef8800120 0xfffffffc4001f87f 0xd7fffffff88003f0

def z327 : W := mkw 0x0000100185050108 0x08000020030a0a02 0x0000000386060180 0x20000000070c0c03

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x600000007800004b 0xa0c0000000f00000

def z329 : W := mkw 0x2130052812280a84 0x0042600a50245015 0x0030000000380000 0x0000600000007000

def z330 : W := mkw 0x58014a0000000000 0x02b0029400000000 0x9c01f00000000004 0x033803e000000000

def z331 : W := mkw 0xf7fab5ffffff6f9c 0x2beff56bfffffedf 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x0040904185454518 0x08008120830a8a8a 0x00c1806787c7c7f5 0x3c018300cf0f8f8f

def z333 : W := mkw 0xdedf8c6765d8de52 0x27bdbf18cecbb1bc 0x9cff8c67c1f9fe7d 0x1f39ff18cf83f3fc

def z334 : W := mkw 0x2120000012200000 0x0042400000244000 0x633000787e3e07fb 0xecc66000f0fc7c0f

def z335 : W := mkw 0x82c0b0d18d476518 0x09058161a31a8eca 0xe3c1ffffffc7ffff 0xffc783ffffff8fff

def z336 : W := mkw 0x08015a808807b060 0x101002b501100f60 0x6001ff807807f86b 0xe4c003ff00f00ff0

def z337 : W := mkw 0xa3fca57800000000 0x4147f94af0000000 0x83fff07800000037 0x4307ffe0f0000000

def z338 : W := mkw 0xfbfdef7905000000 0x43f7fbdef20a0000 0xffffffff87c0007f 0xfbffffffff0f8000

def z339 : W := mkw 0xfba96b1800000000 0x43f752d630000000 0xff01ff980000002f 0xc3fe03ff30000000

def z340 : W := mkw 0x08150c2000000000 0x00102a1840000000 0x1c3e0c0000000008 0x00387c1800000000

def z341 : W := mkw 0x797dcf6800000000 0x42f2fb9ed0000000 0x7cff8fe00000003d 0x80f9ff1fc0000000

def z342 : W := mkw 0xd68a000765900000 0x23ad14000ecb2000 0x9cce000781c00004 0x13399c000f038000

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000060607c0 0x2c000000000c0c0f

def z344 : W := mkw 0xffab4a877fb2b060 0x33ff56950eff6560 0xfffe0f87fff8385f 0xbbfffc1f0ffff070

def z345 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x03300ff8063e3fb0 0x4c06601ff00c7c7f

def z346 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0x7c01ff807807f828 0xc4f803ff00f00ff0

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x000180040001c065 0x1400030008000380

def z348 : W := mkw 0xf3a8018b3f222084 0x23e75003167e4441 0xe300039bbe060182 0xe3c60007377c0c03

def z349 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01f387b807c006 0xf3f803e70f700f80

def z350 : W := mkw 0x0046804000d04412 0x04008d008001a088 0x00ce000001c00000 0x00019c0000038000

def z351 : W := mkw 0x54001006e0050000 0x02a800200dc00a00 0xfc01f007f807c06f 0xf7f803e00ff00f80

def z352 : W := mkw 0x82c0a05105404518 0x09058140a20a808a 0x83c1f07807c007b7 0x4b0783e0f00f800f

def z353 : W := mkw 0x000000801a2a2a84 0x0000000100345455 0x60000f807e3e3feb 0xecc0001f00fc7c7f

def z354 : W := mkw 0x0402000440d8de52 0x040804000881b1bc 0x1cfe000441f9fe5d 0x1c39fc000883f3fc

def z355 : W := mkw 0x084588400040d452 0x04108b10800081a8 0x000180000001c000 0x0000030000000380

def z356 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63000ff83e063fa2 0xe4c6001ff07c0c7f

def z357 : W := mkw 0x0040b05080454518 0x08008160a1008a8a 0x0001f0000001c000 0x000003e000000380

def z358 : W := mkw 0x8ed78c6545d8de52 0x051daf18ca8bb1bc 0x9fff8c67c7f9fe7f 0x3f3fff18cf8ff3fc

def z359 : W := mkw 0x7128000000000000 0x02e2500000000000 0x7c3e000000000008 0x80f87c0000000000

def z360 : W := mkw 0x0040804000000000 0x0000810080000000 0x00c1806000000035 0x00018300c0000000

def z361 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xff01fffffe07ffff 0xfffe03fffffc0fff

def z362 : W := mkw 0xa3fea57917b00000 0x6147fd4af22f6000 0x03fe007807f80010 0x0807fc00f00ff000

def z363 : W := mkw 0x212001881a222084 0x0042400310344441 0x630003f83e0607f3 0xecc60007f07c0c0f

def z364 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0x7ffe0ff800000018 0x80fffc1ff0000000

def z365 : W := mkw 0x001005a8080a2a84 0x0000200b50101455 0x03000ff806063ff3 0x6c06001ff00c0c7f

def z366 : W := mkw 0xffffef7f77f8de52 0x67ffffdefeeff1bc 0xfffffffffff9fe7f 0xfffffffffffff3fc

def z367 : W := mkw 0x5c57de66e0ddde72 0x16b8afbccdc1bbbc 0x9cfffc67c1f9fe7d 0x1f39fff8cf83f3fc

def z368 : W := mkw 0x08558c600048de52 0x0410ab18c00091bc 0x00c18c6401c1fe75 0x1c018318c80383fc

def z369 : W := mkw 0x2130052812280a84 0x0042600a50245015 0x63300ff8063807bb 0xc8c6601ff00c700f

def z370 : W := mkw 0x5c47da46e0d5d472 0x16b88fb48dc1aba8 0x9ccff00781c1c004 0x13399fe00f038380

def z371 : W := mkw 0x752a000672b00000 0x22ea54000ce56000 0x7f3e00007e38005b 0xa8fe7c0000fc7000

def z372 : W := mkw 0x0054a57800000000 0x4000a94af0000000 0x0000007800000000 0x00000000f0000000

def z373 : W := mkw 0x08578c6000d84e12 0x0410af18c001b09c 0x1cff8c6001f8063d 0x0839ff18c003f00c

def z374 : W := mkw 0xfffffffee8dffe72 0x57fffffffdd1bffc 0xfffffffff9fffe7f 0xfffffffffff3fffc

def z375 : W := mkw 0x7d3f4f2c40989a42 0x46fa7e9e58813134 0x7c3e0f8040383808 0x80f87c1f00807070

def z376 : W := mkw 0x82c0b05080454518 0x09058160a1008a8a 0x83c1f0780007c7b7 0x470783e0f0000f8f

def z377 : W := mkw 0x54001086e807b060 0x12a800210dd00f60 0xfc000007f807f84f 0xb7f800000ff00ff0

def z378 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x03c1f07807c7c7b0 0x4c0783e0f00f8f8f

def z379 : W := mkw 0x0855fff88807b060 0x5010abfff1100f60 0x0001fff80007f820 0x440003fff0000ff0

def z380 : W := mkw 0xdaddef7800000000 0x43b5bbdef0000000 0x9ccffff800000024 0x43399ffff0000000

def z381 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300f807e38385b 0xa8c6601f00fc7070

def z382 : W := mkw 0x82d6a47105d84f1a 0x0d05ad48e20bb09e 0x03fe007807f80790 0x0807fc00f00ff00f

def z383 : W := mkw 0xffa95a87ff27b060 0x33ff52b50ffe4f60 0xff01ff87fe07f86f 0xf7fe03ff0ffc0ff0

def z384 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c0441f9f80c 0x1039ff180883f3f0

def z385 : W := mkw 0x753005ae7a2a2a84 0x02ea600b5cf45455 0xff300ffffe3e3fff 0xfffe601ffffc7c7f

def z386 : W := mkw 0x08015a808807b060 0x101002b501100f60 0x8001ff878007f867 0x770003ff0f000ff0

def z387 : W := mkw 0x0c558c644048de52 0x0418ab18c88091bc 0x1c018c644001fe6d 0x14380318c88003fc

def z388 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0x7c000f87f807f848 0xb4f8001f0ff00ff0

def z389 : W := mkw 0xd6cab057e5d54518 0x2bad9560afcbaa8a 0x9ccff00781c1c004 0x13399fe00f038380

def z390 : W := mkw 0x2975ef7800000000 0x4052ebdef0000000 0x6331fff80000003b 0xc0c663fff0000000

def z391 : W := mkw 0x040200845afafed6 0x0408040108b5f5fd 0x000000047fffffc0 0x3c00000008ffffff

def z392 : W := mkw 0xfbffef7800d84e12 0x47f7ffdef001b09c 0xfffffff801f8063f 0xcbfffffff003f00c

def z393 : W := mkw 0xf3a8000337200000 0x23e75000066e4000 0xe3c00007bfc00057 0xbbc780000f7f8000

def z394 : W := mkw 0xdecdfa56e0059060 0x53bd9bf4adc00b20 0x9ccff0078001c004 0x13399fe00f000380

def z395 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1c3f8c604039fe28 0x04387f18c08073fc

def z396 : W := mkw 0xded7fef7eddfff7a 0x1fbdaffdefdbbffe 0xffffffffffffffff 0xffffffffffffffff

def z397 : W := mkw 0xfbbd4f2800000000 0x43f77a9e50000000 0xfffe0f800000001f 0x83fffc1f00000000

def z398 : W := mkw 0x8280000105000000 0x01050000020a0000 0x8300000386000002 0x23060000070c0000

def z399 : W := mkw 0xf3a8631b37200000 0x63e750c6366e4000 0xe300739bbe000002 0xe3c600e7377c0000

def z400 : W := mkw 0xf7ba052f77b00000 0x23ef740a5eef6000 0xfffe0ffffff8007f 0xfbfffc1ffffff000

def z401 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0x7f3e0ff80000003b 0xc0fe7c1ff0000000

def z402 : W := mkw 0xffefea5777b00000 0x63ffdfd4aeef6000 0xfffff007fff8005f 0xbbffffe00ffff000

def z403 : W := mkw 0x0c579c65c5dddf5a 0x0c18af38cb8bbbbe 0x1cff8c67c7fffffd 0x3c39ff18cf8fffff

def z404 : W := mkw 0xf3b805a81a2a2a84 0x03e7700b50345455 0xfffe0ff87e3e3fff 0xeffffc1ff0fc7c7f

def z405 : W := mkw 0x0054846000484e12 0x0400a908c000909c 0x0000006000000600 0x00000000c000000c

def z406 : W := mkw 0xf7aa018f7fb22084 0x23ef54031eff6441 0xfffe039ffffe01df 0xfbfffc073ffffc03

def z407 : W := mkw 0x0c579ce6e8dffe72 0x1418af39cdd1bffc 0x1cff8c67f9fffe7d 0x3c39ff18cff3fffc

def z408 : W := mkw 0xa3f0b579976d4f9c 0x0947e16af32eda9f 0x83f1f07f87ffc7f7 0x7f07e3e0ff0fff8f

def z409 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfcffff800000000c 0x83f9ffff00000000

def z410 : W := mkw 0xa3a8000000000000 0x0147500000000000 0x03fe000000000010 0x0007fc0000000000

def z411 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0x9fcff07800000037 0x433f9fe0f0000000

def z412 : W := mkw 0x5c41dac6e847f470 0x12b883b58dd08fe8 0xfcc1ffe7f9c7fe7f 0xfff983ffcff38ffc

def z413 : W := mkw 0x001005a8080a2a84 0x0000200b50101455 0x00300ff8403e3ff9 0x4c00601ff0807c7f

def z414 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xe3000007fff80042 0xbbc600000ffff000

def z415 : W := mkw 0x253205ac5afafed6 0x044a640b58b5f5fd 0x63300ffc7ffffffb 0xfcc6601ff8ffffff

def z416 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000078000607a0 0x44000000f0000c0f

def z417 : W := mkw 0x5c015a06e0059060 0x12b802b40dc00b20 0x9c01fc07c001f86d 0x173803f80f8003f0

def z418 : W := mkw 0x0400000440000000 0x0008000008800000 0x1c0000044000004d 0x1038000008800000

def z419 : W := mkw 0x86c2b055c5d54518 0x090d8560ab8baa8a 0x9ffff07fc7ffc7ff 0x7f3fffe0ff8fff8f

def z420 : W := mkw 0x2130052800000000 0x0042600a50000000 0x0330007800000010 0x00066000f0000000

def z421 : W := mkw 0xa3fca57905404518 0x4947f94af20a808a 0x03fe007807c00790 0x0807fc00f00f800f

def z422 : W := mkw 0x0c015a84c807b060 0x101802b509900f60 0x1c01ff844007f86d 0x543803ff08800ff0

def z423 : W := mkw 0x8ad5bc7185454518 0x0915ab78e30a8a8a 0x9ffffc7f87c7c7ff 0x7f3ffff8ff0f8f8f

def z424 : W := mkw 0xdedfee7440d8de52 0x47bdbfdce881b1bc 0x9cfffc6441f9fe7d 0x1f39fff8c883f3fc

def z425 : W := mkw 0xfffdef7e60000000 0x43fffbdefcc00000 0xfffffffff800007f 0xf3fffffffff00000

def z426 : W := mkw 0x001004a0080a2a00 0x0000200940101454 0x60300fe0783e3e7b 0xecc0601fc0f07c7c

def z427 : W := mkw 0x7d314fae7a2abae4 0x12fa629f5cf45575 0x7f300ff87e3e3ffb 0xecfe601ff0fc7c7f

def z428 : W := mkw 0x5000420000000000 0x02a0008400000000 0xe000738000000002 0xc3c000e700000000

def z429 : W := mkw 0x0402000440900000 0x0008040008812000 0x1c3e000040380008 0x00387c0000807000

def z430 : W := mkw 0xf3a8631800000000 0x43e750c630000000 0xfffe73980000001f 0xc3fffce730000000

def z431 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f01f87c7c186 0x730783e03f0f8f83

def z432 : W := mkw 0x8ad5ac7000000000 0x0115ab58e0000000 0x9ffffc780000003f 0x433ffff8f0000000

def z433 : W := mkw 0xde8b5a07e5959060 0x33bd16b40fcb2b20 0x9ccff00781c1c004 0x13399fe00f038380

def z434 : W := mkw 0x0442804440d04410 0x000885008881a088 0x1cff806441f9c67d 0x1c39ff00c883f38c

def z435 : W := mkw 0x50005282a8072020 0x12a000a505500e40 0xe0007f83f806386b 0xe7c000ff07f00c70

def z436 : W := mkw 0x8ed7bc75c5dddf5a 0x0d1daf78eb8bbbbe 0x9cfffc67c1f9fe7d 0x1f39fff8cf83f3fc

def z437 : W := mkw 0x2120000000000000 0x0042400000000000 0x633000000000001b 0x80c6600000000000

def z438 : W := mkw 0xf3a83013b7250108 0x2be75060276e4a02 0xe300701bbe060182 0xe3c600e0377c0c03

def z439 : W := mkw 0x5c014a866802b060 0x12b802950cd00560 0xfc01ff807800382f 0xc3f803ff00f00070

def z440 : W := mkw 0x8280301185050108 0x09050060230a0a02 0x8300707b860607f3 0x6f0600e0f70c0c0f

def z441 : W := mkw 0xf3a863981a222084 0x43e750c730344441 0xe30073983e060182 0xe3c600e7307c0c03

def z442 : W := mkw 0x82d0b471854d4f18 0x0905a168e30a9a9e 0x83f1fc7fc7ffffff 0x7f07e3f8ff8fffff

def z443 : W := mkw 0x2120000012200000 0x0042400000244000 0x630000003e000002 0xa0c60000007c0000

def z444 : W := mkw 0x58015a82a8072020 0x12b002b505500e40 0xfc01ff83b806002f 0xe3f803ff07700c00

def z445 : W := mkw 0x0000100185454518 0x08000020030a8a8a 0x8001f00787c7c7e7 0x7f0003e00f0f8f8f

def z446 : W := mkw 0x5000000220000000 0x02a0000004400000 0xe0000003b8000002 0xa3c0000007700000

def z447 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0x7ffe00007ff80018 0x88fffc0000fff000

def z448 : W := mkw 0xffab4a0777b00000 0x23ff56940eef6000 0xffffff87fff8007f 0xfbffffff0ffff000

def z449 : W := mkw 0x0000528088072020 0x100000a501100e40 0x0000738000060000 0x400000e700000c00

def z450 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x60300fe078383e79 0x8cc0601fc0f0707c

def z451 : W := mkw 0xf7aa000440900000 0x03ef540008812000 0xfffe000441f8005f 0x9bfffc000883f000

def z452 : W := mkw 0xa3a031999f27218c 0x09474063333e4e43 0xe300739bbe060182 0xe3c600e7377c0c03

def z453 : W := mkw 0x0002000117b00000 0x20000400022f6000 0x0000000007f80000 0x08000000000ff000

def z454 : W := mkw 0xffab5a07f7b59060 0x33ff56b40fef6b20 0xfffff007fff9c05f 0xbbffffe00ffff380

def z455 : W := mkw 0x8ad5ef7800000000 0x4115abdef0000000 0x83c1fff800000037 0x430783fff0000000

def z456 : W := mkw 0xf3b8673800000000 0x43e770ce70000000 0xe3307ff80000003b 0xc3c660fff0000000

def z457 : W := mkw 0x8ec1b855c545d558 0x091d8370ab8a8baa 0x9fc1fc7fc7c7ffff 0x7f3f83f8ff8f8fff

def z458 : W := mkw 0x82d6b47185dd4f1a 0x0d05ad68e30bba9e 0x83fff07f87ffc7f7 0x7f07ffe0ff0fff8f

def z459 : W := mkw 0x29758de81a2a2a84 0x0052eb1bd0345455 0x7fff8ff87e3e3fff 0xecffff1ff0fc7c7f

def z460 : W := mkw 0xf7aa000777f8de52 0x27ef54000eeff1bc 0xfffe0007fff9fe5f 0xbffffc000ffff3fc

def z461 : W := mkw 0x58015a808807b060 0x12b002b501100f60 0xfc01ff800007f82f 0xc7f803ff00000ff0

def z462 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f87c1c794 0x1b0783e0ff0f838f

def z463 : W := mkw 0x0c01080440009040 0x0018021008800120 0x1c000c0040003808 0x0038001800800070

def z464 : W := mkw 0x08558c6000000000 0x0010ab18c0000000 0x00018c6000000020 0x00000318c0000000

def z465 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000060063 0x6400000000000c00

def z466 : W := mkw 0xfbfdeff8080a2a84 0x43f7fbdff0101455 0xfffffff800063fbf 0xc7fffffff0000c7f

def z467 : W := mkw 0xd288000000000000 0x03a5100000000000 0x9cce000000000004 0x03399c0000000000

def z468 : W := mkw 0x0c03080440909040 0x0018061008812120 0x1cff8c0441f9f87d 0x1c39ff180883f3f0

def z469 : W := mkw 0x0c558c6440009040 0x0018ab18c8800120 0x1cff8c644001f87d 0x1439ff18c88003f0

def z470 : W := mkw 0x0000100185454518 0x08000020030a8a8a 0x0000000781c1c000 0x100000000f038380

def z471 : W := mkw 0x0c4188444040d450 0x00188310888081a8 0x1cc18c6441c1fe7d 0x1c398318c88383fc

def z472 : W := mkw 0xffff8def7ffafed6 0x27ffff1bdefff5fd 0xffff8fffffffffff 0xffffff1fffffffff

def z473 : W := mkw 0xfbfdeff808022000 0x43f7fbdff0100440 0xfffffff87806387f 0xe7fffffff0f00c70

def z474 : W := mkw 0x5000000000000000 0x02a0000000000000 0xfc0000000000000f 0x83f8000000000000

def z475 : W := mkw 0xf7ba042777b80a00 0x23ef74084eef7014 0xfffe0c67fff83e7f 0xbffffc18cffff07c

def z476 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0x9ffe000787f80014 0x1b3ffc000f0ff000

def z477 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001f00000000027 0x430003e000000000

def z478 : W := mkw 0x8ec7b855c5d5d55a 0x0d1d8f70ab8babaa 0x9fcff07f87c7c7f7 0x7f3f9fe0ff0f8f8f

def z479 : W := mkw 0xa3fca57800000000 0x4147f94af0000000 0x63fe0ff80000003b 0xc0c7fc1ff0000000

def z480 : W := mkw 0x001005a8080a2a84 0x0000200b50101455 0x60000ff878063feb 0xe4c0001ff0f00c7f

def z481 : W := mkw 0x0000000337200000 0x20000000066e4000 0x00000003be000000 0x20000000077c0000

def z482 : W := mkw 0x04021087ffb7b060 0x300804210fff6f60 0x00000007fffff840 0x3c0000000ffffff0

def z483 : W := mkw 0xf7fea57f77b00000 0x63effd4afeef6000 0xfffe007ffff8005f 0xbbfffc00fffff000

def z484 : W := mkw 0x8280000000000000 0x0105000000000000 0x83c0000000000017 0x0307800000000000

def z485 : W := mkw 0x0855ff7880454518 0x4810abfef1008a8a 0x0001fff80007c7a0 0x440003fff0000f8f

def z486 : W := mkw 0x8280000105000000 0x01050000020a0000 0x83c0007f87c607f7 0x7f078000ff0f8c0f

def z487 : W := mkw 0x0010052800000000 0x0000200a50000000 0x00000ff800000020 0x4000001ff0000000

def z488 : W := mkw 0xf7aa00877fba2a84 0x23ef54010eff7455 0xfffe0007fffe3fdf 0xbffffc000ffffc7f

def z489 : W := mkw 0x58014a0000000000 0x02b0029400000000 0x7c000f8000000008 0x80f8001f00000000

def z490 : W := mkw 0xf3a8739aa8072020 0x53e750e735500e40 0xe300739bb8060002 0xe3c600e737700c00

def z491 : W := mkw 0xffffff7dc5dddf5a 0x4ffffffefb8bbbbe 0xffffffffc7ffffff 0xffffffffff8fffff

def z492 : W := mkw 0xfbfdef7812280a84 0x43f7fbdef0245015 0xfffffff8063807bf 0xcbfffffff00c700f

def z493 : W := mkw 0x2d778d6c40d8de52 0x045aef1ad881b1bc 0x7fff8ffc41f9fe7f 0xdcffff1ff883f3fc

def z494 : W := mkw 0x0c170c2440989a42 0x04182e1848813134 0x1c3f8c044039f86d 0x14387f18088073f0

def z495 : W := mkw 0xfbfdff7880454518 0x4bf7fbfef1008a8a 0xfffffff80007c7bf 0xc7fffffff0000f8f

def z496 : W := mkw 0x0054846000000000 0x0000a908c0000000 0x00fe006000000010 0x0001fc00c0000000

def z497 : W := mkw 0x0000008008022000 0x0000000100100440 0x0000000078063840 0x2400000000f00c70

def z498 : W := mkw 0xf7ba052f77b80a84 0x23ef740a5eef7015 0xfffe007ffff807df 0xbbfffc00fffff00f

def z499 : W := mkw 0x0c03080440d8de52 0x041806100881b1bc 0x1c018c0441f9fe6d 0x1c3803180883f3fc

def z500 : W := mkw 0x0040804000404410 0x0000810080008088 0x00c0006001c00610 0x08018000c003800c

def z501 : W := mkw 0x86c2b055c5dddf5a 0x0d0d8560ab8bbbbe 0x83c1f07fc7fffff7 0x7f0783e0ff8fffff

def z502 : W := mkw 0xa3eaa05117f04518 0x2947d540a22fe08a 0x03fe007807f80790 0x0807fc00f00ff00f

def z503 : W := mkw 0xf3a8000337200000 0x23e75000066e4000 0xe3300003fe38005b 0xabc6600007fc7000

def z504 : W := mkw 0x8ad5bc71854ddf5a 0x0d15ab78e30a9bbe 0x83c1fc7f87c7fff7 0x7f0783f8ff0f8fff

def z505 : W := mkw 0x08558de8084afed6 0x0410ab1bd01095fd 0x00018ff80007ffa0 0x4400031ff0000fff

def z506 : W := mkw 0xa3fca57812280a84 0x4147f94af0245015 0x03fe007806380790 0x0807fc00f00c700f

def z507 : W := mkw 0x0050b5f8884f6f9c 0x0800a16bf1109edf 0x0001fff80007ffa0 0x440003fff0000fff

def z508 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87e383f98 0x88c6601ff0fc707f

def z509 : W := mkw 0x2130052800000000 0x0042600a50000000 0x63300ff8060607fb 0xecc6601ff00c0c0f

def z510 : W := mkw 0x0016042000980a02 0x04002c0840013014 0x003e000000380000 0x00007c0000007000

def z511 : W := mkw 0x82c0b05185050108 0x09058160a30a0a02 0x83c1f07b860601b7 0x630783e0f70c0c03

def z512 : W := mkw 0x0000100080050000 0x0000002001000a00 0x8301f07f8607c7f7 0x7f0603e0ff0c0f8f

def z513 : W := mkw 0x2130052812280a84 0x0042600a50245015 0x03300078063e07f3 0x6c066000f00c7c0f

def z514 : W := mkw 0x0002000000d84e12 0x040004000001b09c 0x0000000001f80600 0x080000000003f00c

def z515 : W := mkw 0xffebfad7fff7f578 0x3bffd7f5afffefea 0xffffffffffffffff 0xffffffffffffffff

def z516 : W := mkw 0x0056846000d84e12 0x0400ad08c001b09c 0x00ff806401f9c675 0x1c01ff00c803f38c

def z517 : W := mkw 0xfbffef7917b00000 0x63f7ffdef22f6000 0xfffffff807f8003f 0xcbfffffff00ff000

def z518 : W := mkw 0x5c41fad6e847f578 0x1ab883f5add08fea 0xfc01fffff807ffef 0xf7f803fffff00fff

def z519 : W := mkw 0xf3aa000337b00000 0x23e75400066f6000 0xe3fe0003bff80012 0xabc7fc00077ff000

def z520 : W := mkw 0x5c014a866802b060 0x12b802950cd00560 0x7c000f807806386b 0xe4f8001f00f00c70

def z521 : W := mkw 0xabfdef7800000000 0x4157fbdef0000000 0x03fffff800000030 0x4007fffff0000000

def z522 : W := mkw 0x0000301080050108 0x0800006021000a02 0x0000701800060180 0x400000e030000c03

def z523 : W := mkw 0xf7eaa05777f04518 0x2befd540aeefe08a 0xfffe007ffff807df 0xbbfffc00fffff00f

def z524 : W := mkw 0x0c0108844802b040 0x0018021108900560 0x7c018f847807f86f 0xf4f8031f08f00ff0

def z525 : W := mkw 0x0040b05080454518 0x08008160a1008a8a 0x00c1f07c01c7c7f5 0x5c0183e0f8038f8f

def z526 : W := mkw 0xf7ba05af7fba2a84 0x23ef740b5eff7455 0xfffe0f87fff8385f 0xbbfffc1f0ffff070

def z527 : W := mkw 0xf7aa000765900000 0x23ef54000ecb2000 0xfffe000781c0001f 0x93fffc000f038000

def z528 : W := mkw 0x0402000765900000 0x200804000ecb2000 0x0000000781c00000 0x100000000f038000

def z529 : W := mkw 0x0c578c6440d0d452 0x0418af18c881a1a8 0x1cff8c6401c1c03d 0x1039ff18c8038380

def z530 : W := mkw 0x8682000545900000 0x010d04000a8b2000 0x9ffe0007c7f8005f 0x3b3ffc000f8ff000

def z531 : W := mkw 0x713057aaba2f2aa4 0x12e260af55745e55 0xe3307ffbfe3e3ffb 0xefc660fff7fc7c7f

def z532 : W := mkw 0xf3a8000000000000 0x03e7500000000000 0xe300000000000002 0x83c6000000000000

def z533 : W := mkw 0x828a000105900000 0x21051400020b2000 0x00ce000001c00000 0x00019c0000038000

def z534 : W := mkw 0x2d778c6452f8de52 0x045aef18c8a5f1bc 0x7fff8c647ff9fe7f 0xbcffff18c8fff3fc

def z535 : W := mkw 0x0000018808022084 0x0000000310100441 0x0000039800060180 0x4000000730000c03

def z536 : W := mkw 0x7120538aba2720a4 0x12e240a715744e41 0xe300739bbe060182 0xe3c600e7377c0c03

def z537 : W := mkw 0x5c015a86fa2fbae4 0x12b802b50df45f75 0xfc01ff87fe3fffef 0xfff803ff0ffc7fff

def z538 : W := mkw 0x5c015a06e0059060 0x12b802b40dc00b20 0xfc01ff878001c02f 0xd3f803ff0f000380

def z539 : W := mkw 0x08154f2800000000 0x40102a9e50000000 0x00000f8000000000 0x0000001f00000000

def z540 : W := mkw 0x8280100185454518 0x09050020030a8a8a 0x83c0000787c7c7d7 0x3f0780000f0f8f8f

def z541 : W := mkw 0xffa97b9ee807b060 0x53ff52f73dd00f60 0xff01ff9ff807f86f 0xf7fe03ff3ff00ff0

def z542 : W := mkw 0xa3ba052917b80a84 0x2147740a522f7015 0x03fe007807f80790 0x0807fc00f00ff00f

def z543 : W := mkw 0x08150c2000089a42 0x04102a1840001134 0x00000c0000003800 0x0000001800000070

def z544 : W := mkw 0xf7aa000672b00000 0x23ef54000ce56000 0xfffe00007838001f 0x83fffc0000f07000

def z545 : W := mkw 0x000010808807b060 0x1000002101100f60 0x000000000007f800 0x0400000000000ff0

def z546 : W := mkw 0x0000008008022000 0x0000000100100440 0x6000038038060002 0xe0c0000700700c00

def z547 : W := mkw 0x0c578ce45afafed6 0x0418af19c8b5f5fd 0x1cff8c647ffffffd 0x3c39ff18c8ffffff

def z548 : W := mkw 0x0412042440d8de52 0x040824084881b1bc 0x00300c6441f9fe79 0x1c006018c883f3fc

def z549 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x60300f807e3e3fc8 0xacc0601f00fc7c7f

def z550 : W := mkw 0xdec1fad7ed47f578 0x1bbd83f5afda8fea 0xfcc1ff87f9c7f86f 0xf7f983ff0ff38ff0

def z551 : W := mkw 0x5c47dac6e8d7f472 0x16b88fb58dd1afe8 0xfccfff87f9c7f86f 0xf7f99fff0ff38ff0

def z552 : W := mkw 0x58014a8008022000 0x02b0029500100440 0xfc01ff807806386f 0xe7f803ff00f00c70

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000780000047 0x330000000f000000

def z554 : W := mkw 0x08578c6000d8de52 0x0410af18c001b1bc 0x00ff8c6001f9fe30 0x0c01ff18c003f3fc

def z555 : W := mkw 0x5000428228022020 0x12a0008504500440 0x6000038038000000 0x80c0000700700000

def z556 : W := mkw 0x08015a0080059060 0x101002b401000b20 0x0001f0000001c000 0x000003e000000380

def z557 : W := mkw 0xffbf4f2f77b00000 0x63ff7e9e5eef6000 0xfffe0f87fff8005f 0xbbfffc1f0ffff000

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c0040003869 0x0400001800800070

def z559 : W := mkw 0x001005a8080a2a84 0x0000200b50101455 0x00000f8000003800 0x0000001f00000070

def z560 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x80c1f00781c7c067 0x770183e00f038f80

def z561 : W := mkw 0x7d215a86fa27b060 0x12fa42b50df44f60 0xff31ff87fe3ff87f 0xfffe63ff0ffc7ff0

def z562 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87838383b 0xc0c6601ff0f07070

def z563 : W := mkw 0xa3eab05197f54518 0x2947d560a32fea8a 0x83fff07f87ffc7f7 0x7f07ffe0ff0fff8f

def z564 : W := mkw 0x0000000012280a84 0x0000000000245015 0x0000000006380780 0x08000000000c700f

def z565 : W := mkw 0xf7aa1007f7b50000 0x23ef54200fef6a00 0xfffff007ffffc07f 0xffffffe00fffff80

def z566 : W := mkw 0x82c0a05105404518 0x09058140a20a808a 0x03c1807c07c1c7f5 0x1c078300f80f838f

def z567 : W := mkw 0xf3e8b05185454518 0x0be7d160a30a8a8a 0xfffff07f87c7c7ff 0xffffffe0ff0f8f8f

def z568 : W := mkw 0x8280301185050108 0x09050060230a0a02 0x83c0701f87c601d7 0x7b0780e03f0f8c03

def z569 : W := mkw 0x04021007f7f54518 0x280804200fefea8a 0x00000007ffffc7c0 0x3c0000000fffff8f

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c0000401c00055 0x1801800008038000

def z571 : W := mkw 0xf7a8000660000000 0x03ef50000cc00000 0xfffe0007f800005f 0xb3fffc000ff00000

def z572 : W := mkw 0xf3e8a05000000000 0x03e7d140a0000000 0xfffff0780000003f 0xc3ffffe0f0000000

def z573 : W := mkw 0xdacdfa5185454518 0x4bb59bf4a30a8a8a 0x9fcff07f87c7c7f7 0x7f3f9fe0ff0f8f8f

def z574 : W := mkw 0x8280100185050000 0x01050020030a0a00 0x83c1f00787c7c077 0x7f0783e00f0f8f80

def z575 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x80c1f06781c1c675 0x1f0183e0cf03838c

def z576 : W := mkw 0x0002000000900000 0x0000040000012000 0x00fe000001f80010 0x0801fc000003f000

def z577 : W := mkw 0x2d370dac5ababac6 0x045a6e1b58b57575 0x7f3e0ff87e3e3ffb 0xecfe7c1ff0fc7c7f

def z578 : W := mkw 0x8ed7ac7545d8df5a 0x0d1daf58ea8bb1be 0x1fff8c7c47f9fffd 0x1c3fff18f88ff3ff

def z579 : W := mkw 0x253015aefa2fbae4 0x104a602b5df45f75 0x63300ffffe3ffffb 0xfcc6601ffffc7fff

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000006000000671 0x0c000000c000000c

def z581 : W := mkw 0x04001086fa2fbae4 0x100800210df45f75 0x00000007fe3fffc0 0x3c0000000ffc7fff

def z582 : W := mkw 0x2120010812200084 0x0042400210244001 0x0300001806000180 0x00060000300c0003

def z583 : W := mkw 0x0010042000080a00 0x0000200840001014 0x03300c78463e3ffb 0x6c066018f08c7c7f

def z584 : W := mkw 0xffffef7c40900000 0x43ffffdef8812000 0xfffffffc41f8007f 0xdbfffffff883f000

def z585 : W := mkw 0x2522000777b00000 0x204a44000eef6000 0x63300007fff8005b 0xb8c660000ffff000

def z586 : W := mkw 0x5855ef7800000000 0x42b0abdef0000000 0xfc01fff80000002f 0xc3f803fff0000000

def z587 : W := mkw 0x0040b05185454518 0x08008160a30a8a8a 0x0001f07f87c7c7e0 0x7c0003e0ff0f8f8f

def z588 : W := mkw 0x0400000440009040 0x0008000008800120 0x000000044001f840 0x14000000088003f0

def z589 : W := mkw 0xa7aa000557b00000 0x214f54000aaf6000 0x1ffe000447f8005d 0x183ffc00088ff000

def z590 : W := mkw 0xf3e8e35800000000 0x43e7d1c6b0000000 0xe3c1f3f800000037 0xc3c783e7f0000000

def z591 : W := mkw 0xa3e0b05197654518 0x0947c160a32eca8a 0xe3f1f07fffffc7ff 0xffc7e3e0ffffff8f

def z592 : W := mkw 0x0402000672b00000 0x200804000ce56000 0x0000000078380000 0x0000000000f07000

def z593 : W := mkw 0x2120000012200000 0x0042400000244000 0x0330000006380010 0x08066000000c7000

def z594 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x60300f80783e386b 0xe4c0601f00f07c70

def z595 : W := mkw 0x0000000105404518 0x08000000020a808a 0x0000000007c00780 0x08000000000f800f

def z596 : W := mkw 0x04021005c5dddf5a 0x0c0804200b8bbbbe 0x00000007c7ffffc0 0x3c0000000f8fffff

def z597 : W := mkw 0x753a05ae7aba2a84 0x22ea740b5cf57455 0x7c3e0f8078383808 0x80f87c1f00f07070

def z598 : W := mkw 0xa3f0b57985454518 0x0947e16af30a8a8a 0xe3f1ffff87c7c7ff 0xffc7e3ffff0f8f8f

def z599 : W := mkw 0x0000100080050000 0x0000002001000a00 0x0001f0000007c020 0x440003e000000f80

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000f800000002b 0xc0c0001f00000000

def z601 : W := mkw 0x7d2b5a86fab7b060 0x32fa56b50df56f60 0xfc3fff87f83ff86f 0xf7f87fff0ff07ff0

def z602 : W := mkw 0x0010042000080a00 0x0000200840001014 0x00300c0040383808 0x0000601800807070

def z603 : W := mkw 0x2176856812f84e96 0x0442ed0ad025f09d 0x03fe007807f80790 0x0807fc00f00ff00f

def z604 : W := mkw 0x7d3f0c2672b89a42 0x26fa7e184ce57134 0x7c3e0c0078383808 0x80f87c1800f07070

def z605 : W := mkw 0x540a000660900000 0x22a814000cc12000 0x1c0e000000000000 0x00381c0000000000

def z606 : W := mkw 0xfbfdeff81a2a2a84 0x43f7fbdff0345455 0xfffffff87838383f 0xc3fffffff0f07070

def z607 : W := mkw 0x0c170c2440d8de52 0x04182e184881b1bc 0x1c3e0c0441f9fe48 0x1c387c180883f3fc

def z608 : W := mkw 0x0050846000484e10 0x0000a108c000909c 0x00f18c6441f9fe7d 0x1c01e318c883f3fc

def z609 : W := mkw 0xa3f0a57800000000 0x0147e14af0000000 0xe3f1fff80000003f 0xc3c7e3fff0000000

def z610 : W := mkw 0x0000008008022000 0x0000000100100440 0x63000ff87e063ffb 0xecc6001ff0fc0c7f

def z611 : W := mkw 0x0412042440980a00 0x0008240848813014 0x1cfe0c6441f83e7d 0x1c39fc18c883f07c

def z612 : W := mkw 0x8ad5ff7985454518 0x4915abfef30a8a8a 0x83c1ffff87c7c7f7 0x7f0783ffff0f8f8f

def z613 : W := mkw 0x5c015a06e0059060 0x12b802b40dc00b20 0xfc01f007f801c04f 0xb3f803e00ff00380

def z614 : W := mkw 0x213015a89a2f2a84 0x0042602b51345e55 0xe331fffffe3fffff 0xffc663fffffc7fff

def z615 : W := mkw 0x0040a05000000000 0x00008140a0000000 0x0001f07800000020 0x400003e0f0000000

def z616 : W := mkw 0x0c110c2440089a40 0x0018221848801134 0x1c318c644039fe7d 0x1c386318c88073fc

def z617 : W := mkw 0x04001087ed47f578 0x180800210fda8fea 0x00000007ffc7ffc0 0x3c0000000fff8fff

def z618 : W := mkw 0x5c014a0660000000 0x02b802940cc00000 0xfc01ff87f800006f 0xf3f803ff0ff00000

def z619 : W := mkw 0x82c0a05000404410 0x01058140a0008088 0x83c1f07c01c1c677 0x5f0783e0f803838c

def z620 : W := mkw 0x580d4a0000000000 0x42b01a9400000000 0x1c0e000000000000 0x00381c0000000000

def z621 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cfe0c6041f83e18 0x0839fc18c083f07c

def z622 : W := mkw 0xf3fca57800000000 0x43e7f94af0000000 0xfffe00780000001f 0x83fffc00f0000000

def z623 : W := mkw 0x7128430800000000 0x42e2508610000000 0x6000038000000000 0x80c0000700000000

def z624 : W := mkw 0x82c0a05105404518 0x09058140a20a808a 0x00c0000001c00000 0x0001800000038000

def z625 : W := mkw 0x0402000440989a42 0x0408040008813134 0x0000000040383800 0x0000000000807070

def z626 : W := mkw 0x04001086e807b060 0x100800210dd00f60 0x60000f87f807f86b 0xf4c0001f0ff00ff0

def z627 : W := mkw 0x0442804440d8de52 0x040885008881b1bc 0x00c1806441f9fe75 0x1c018300c883f3fc

def z628 : W := mkw 0x5c014a0440009040 0x02b8029408800120 0xfc01ff844001f86f 0xd7f803ff088003f0

def z629 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0x9ffff07800000014 0x033fffe0f0000000

def z630 : W := mkw 0x7520000672200000 0x02ea40000ce44000 0xff300007fe38005f 0xbbfe60000ffc7000

def z631 : W := mkw 0x0000100080454518 0x0800002001008a8a 0x000000000007c780 0x0400000000000f8f

def z632 : W := mkw 0xabfdad7800000000 0x4157fb5af0000000 0x1fff8c780000003d 0x003fff18f0000000

def z633 : W := mkw 0xdecf884765d0d452 0x27bd9f108ecba1a8 0x9ccf800781c1c004 0x13399f000f038380

def z634 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x033000787e3e3fd0 0x2c066000f0fc7c7f

def z635 : W := mkw 0x5400000660000000 0x02a800000cc00000 0x9c00000780000004 0x133800000f000000

def z636 : W := mkw 0xa3aa000117b00000 0x21475400022f6000 0x63fe00007ff8005b 0xa8c7fc0000fff000

def z637 : W := mkw 0x7d3d5faee807b060 0x52fa7abf5dd00f60 0xfc3fff87f807f86f 0xf7f87fff0ff00ff0

def z638 : W := mkw 0x5c115faee80fbae4 0x12b822bf5dd01f75 0xfc01fffff807ffef 0xf7f803fffff00fff

def z639 : W := mkw 0x58015a0080050000 0x02b002b401000a00 0xfc01ff878007c06f 0xf7f803ff0f000f80

def z640 : W := mkw 0x0010042000080a00 0x0000200840001014 0x0030006000380610 0x08006000c000700c

def z641 : W := mkw 0xdaddee7000000000 0x43b5bbdce0000000 0x9cfffc600000003d 0x0339fff8c0000000

def z642 : W := mkw 0x0c578dec48dafed6 0x0418af1bd891b5fd 0x1cff8ffc41fffffd 0x5c39ff1ff883ffff

def z643 : W := mkw 0xa3f0a5f91f6a6f9c 0x0947e14bf23ed4df 0x63f00ff87ffe3ffb 0xecc7e01ff0fffc7f

def z644 : W := mkw 0xfffdfffefa2fbae4 0x53fffbfffdf45f75 0xfffffffffe3fffff 0xfffffffffffc7fff

def z645 : W := mkw 0x040000866802b060 0x100800010cd00560 0x0000000078003800 0x0000000000f00070

def z646 : W := mkw 0x8280000105000000 0x01050000020a0000 0x03c0000007c00010 0x08078000000f8000

def z647 : W := mkw 0x0040a05000404518 0x08008140a000808a 0x0000007800000780 0x00000000f000000f

def z648 : W := mkw 0x5c01080660009040 0x02b802100cc00120 0xfc018c07f801f86f 0xb7f803180ff003f0

def z649 : W := mkw 0x0000000105000000 0x00000000020a0000 0x0000000787c00040 0x380000000f0f8000

def z650 : W := mkw 0x5c014a866802b060 0x12b802950cd00560 0xfc000f87f800384f 0xb3f8001f0ff00070

def z651 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300f987e3e398a 0xe0c6601f30fc7c73

def z652 : W := mkw 0x0855ef780048de52 0x4410abdef00091bc 0x0001fff80001fe20 0x440003fff00003fc

def z653 : W := mkw 0x0841fad08847f578 0x181083f5a1108fea 0x0001fff80007ffa0 0x440003fff0000fff

def z654 : W := mkw 0x212000801a2a2a84 0x0042400100345455 0x633000007e3e3fdb 0xacc6600000fc7c7f

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z656 : W := mkw 0x0402000440d0d452 0x040804000881a1a8 0x0000000401c1c000 0x1000000008038380

def z657 : W := mkw 0x213c052800000000 0x4042780a50000000 0x003e000000000000 0x00007c0000000000

def z658 : W := mkw 0x2975eff81a2a2a84 0x4052ebdff0345455 0x6331fff87e3e3ffb 0xecc663fff0fc7c7f

def z659 : W := mkw 0x212001881a222084 0x0042400310344441 0x633003987e3e01db 0xe8c6600730fc7c03

def z660 : W := mkw 0x001004a01a2a2a84 0x0000200940345455 0x00300c607e3e3ff9 0x2c006018c0fc7c7f

def z661 : W := mkw 0x793d4fa81a2a2a84 0x42f27a9f50345455 0x7c3e0f8078383808 0x80f87c1f00f07070

def z662 : W := mkw 0xa3a8211800000000 0x4147504230000000 0x0300001800000000 0x0006000030000000

def z663 : W := mkw 0x0c578ce448dafe52 0x0418af19c891b5fc 0x7cff8fe479fffe7f 0xfcf9ff1fc8f3fffc

def z664 : W := mkw 0xa3aa000117b00000 0x21475400022f6000 0x83fe000787f80057 0x3b07fc000f0ff000

def z665 : W := mkw 0x253205af7fba2a84 0x204a640b5eff7455 0x63300ffffffe3ffb 0xfcc6601ffffffc7f

def z666 : W := mkw 0x2130052812280a84 0x0042600a50245015 0x633000787e3807db 0xa8c66000f0fc700f

def z667 : W := mkw 0x0c578c6440989a42 0x0418af18c8813134 0x1cff8c604038383d 0x0039ff18c0807070

def z668 : W := mkw 0x212001881a222084 0x0042400310344441 0x6000038038000000 0x80c0000700700000

def z669 : W := mkw 0x8280301185050108 0x09050060230a0a02 0x8301f01f8607c1e7 0x770603e03f0c0f83

def z670 : W := mkw 0xd68a000765900000 0x23ad14000ecb2000 0x9cfe0007c1f8005d 0x1b39fc000f83f000

def z671 : W := mkw 0xf3fce77800000000 0x43e7f9cef0000000 0xe3fe73f800000012 0xc3c7fce7f0000000

def z672 : W := mkw 0xd2c0f2d3ad476538 0x1ba581e5a75a8eca 0xe3c1f3ffbfc7c7f7 0xffc783e7ff7f8f8f

def z673 : W := mkw 0x7d315faee807b060 0x12fa62bf5dd00f60 0xff31fffff807f87f 0xf7fe63fffff00ff0

def z674 : W := mkw 0xf3a8000105000000 0x03e75000020a0000 0xfffe000787c0005f 0xbbfffc000f0f8000

def z675 : W := mkw 0xa3a8000117200000 0x21475000022e4000 0x0300000006000000 0x00060000000c0000

def z676 : W := mkw 0x7d315faefa2fbae4 0x12fa62bf5df45f75 0xfc31ff87f83ff86f 0xf7f863ff0ff07ff0

def z677 : W := mkw 0x0845ea5000000000 0x40108bd4a0000000 0x0001f00000000000 0x000003e000000000

def z678 : W := mkw 0x5c55fffee807b060 0x52b8abfffdd00f60 0xfc01fffff807f86f 0xf7f803fffff00ff0

def z679 : W := mkw 0x7d2b4a867ab2b060 0x32fa56950cf56560 0x7c3e0f8078383808 0x80f87c1f00f07070

def z680 : W := mkw 0x08558c600048de52 0x0410ab18c00091bc 0x1cff8c600001fe3d 0x0439ff18c00003fc

def z681 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xffce0007bfc00006 0xb3ff9c000f7f8000

def z682 : W := mkw 0x5c578c6660d8de52 0x06b8af18ccc1b1bc 0xfcff8c67f9f9fe7f 0xbff9ff18cff3f3fc

def z683 : W := mkw 0xaff7bdfddfffffde 0x0d5fef7bfbbfffff 0xffffffffffffffff 0xffffffffffffffff

def z684 : W := mkw 0x0000100080050000 0x0000002001000a00 0x000000078007c040 0x340000000f000f80

def z685 : W := mkw 0x752a000672b00000 0x22ea54000ce56000 0xfc3e0007f838004f 0xb3f87c000ff07000

def z686 : W := mkw 0x0000631800000000 0x400000c630000000 0x0000739800000000 0x400000e730000000

def z687 : W := mkw 0xfff1ffffff6ffffc 0x1bffe3fffffedfff 0xfff1ffffffffffff 0xffffe3ffffffffff

def z688 : W := mkw 0x0010052800080a84 0x0000200a50001015 0x0000007800000780 0x00000000f000000f

def z689 : W := mkw 0x752a000777b00000 0x22ea54000eef6000 0x7c3e0007fff80048 0xb8f87c000ffff000

def z690 : W := mkw 0x7d7fcf6c40d8de52 0x46faff9ed881b1bc 0x7cff8fe441f9fe7d 0x9cf9ff1fc883f3fc

def z691 : W := mkw 0xffbf0c2777b89a42 0x27ff7e184eef7134 0xfffe0c07fff8385f 0xbbfffc180ffff070

def z692 : W := mkw 0xf3b805ab3f2a2a84 0x23e7700b567e5455 0xe3300ffbfe3e3ffb 0xefc6601ff7fc7c7f

def z693 : W := mkw 0xfffdff7ee0059060 0x53fffbfefdc00b20 0xffffffff8001c03f 0xd3ffffffff000380

def z694 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x80c1f07f81c7c7a4 0x570183e0ff038f8f

def z695 : W := mkw 0x213005a808022000 0x0042600b50100440 0x63300ff87806387b 0xe4c6601ff0f00c70

def z696 : W := mkw 0x08115fa8880fbae4 0x101022bf51101f75 0x0001fff80007ffa0 0x440003fff0000fff

def z697 : W := mkw 0x0000100080050000 0x0000002001000a00 0x8001f0078001c004 0x130003e00f000380

def z698 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1ccf8c6401c1fe24 0x14399f18c80383fc

def z699 : W := mkw 0x000000801a2a2a84 0x0000000100345455 0x030000787e3e3ff3 0x6c060000f0fc7c7f

def z700 : W := mkw 0x2d310dac5a2abac4 0x005a621b58b45575 0x7f318ffc7e3fffff 0xfcfe631ff8fc7fff

def z701 : W := mkw 0xdac1ea5000000000 0x03b583d4a0000000 0xffc1fff80000003f 0xc3ff83fff0000000

def z702 : W := mkw 0xa3a0000117200000 0x01474000022e4000 0xe3f00007fff8005f 0xbbc7e0000ffff000

def z703 : W := mkw 0xffffefff7fba2a84 0x63ffffdffeff7455 0xfffffffffffe3fff 0xfffffffffffffc7f

def z704 : W := mkw 0x0c47884440d0d452 0x04188f108881a1a8 0x1cff800441f9c05d 0x1839ff000883f380

def z705 : W := mkw 0x0c47884440d8de52 0x04188f108881b1bc 0x1ccf800441f9fe44 0x1c399f000883f3fc

def z706 : W := mkw 0xdecdfad6e807b060 0x53bd9bf5add00f60 0xfccfff87f807f86f 0xf7f99fff0ff00ff0

def z707 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f807f80e 0xf3f803ff0ff00ff0

def z708 : W := mkw 0x2975ef7800000000 0x4052ebdef0000000 0x7ffffff80000003f 0xc0fffffff0000000

def z709 : W := mkw 0xa3f0b5f99f6f6f9c 0x0947e16bf33ededf 0xe0f1ff87f9f9f80c 0x93c1e3ff0ff3f3f0

def z710 : W := mkw 0x0c57ad7c40d8de52 0x4418af5af881b1bc 0x1cff8c7c41f9fe7d 0x1c39ff18f883f3fc

def z711 : W := mkw 0x04021086fab7b060 0x300804210df56f60 0x00000007f83ff840 0x340000000ff07ff0

def z712 : W := mkw 0xfbfdef7800089a42 0x47f7fbdef0001134 0xfffffff80000383f 0xc3fffffff0000070

def z713 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0xffcffff80000003f 0xc3ff9ffff0000000

def z714 : W := mkw 0x793d5f2985454518 0x4af27abe530a8a8a 0x7c3e0f8787c7c7c8 0xbcf87c1f0f0f8f8f

def z715 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f801f86d 0x97f803ff0ff003f0

def z716 : W := mkw 0x0c57ef7c40d8de52 0x4418afdef881b1bc 0x0001fffc41f9fe60 0x5c0003fff883f3fc

def z717 : W := mkw 0xdec1ead76d42f578 0x1bbd83d5aeda85ea 0x7fc00ff87fc03f98 0x88ff801ff0ff807f

def z718 : W := mkw 0x756ab056f2f54518 0x2aead560ade5ea8a 0x7c3ff078783fc7a8 0xc4f87fe0f0f07f8f

def z719 : W := mkw 0xdaddef7800000000 0x43b5bbdef0000000 0x9ccfff8000000004 0x03399fff00000000

def z720 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0067fff8067f 0xbffffc00cffff00c

def z721 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc31ff87f83ff87f 0xfff863ff0ff07ff0

def z722 : W := mkw 0x58015a8088072000 0x02b002b501100e40 0xfc01ff87f807f86f 0xf7f803ff0ff00ff0

def z723 : W := mkw 0x0c170c2440d8de52 0x04182e184881b1bc 0x1cfe0c0441f9fe5d 0x1c39fc180883f3fc

def z724 : W := mkw 0xdecbfa57e5d5d578 0x3bbd97f4afcbabaa 0x9ccff00781c1c004 0x13399fe00f038380

def z725 : W := mkw 0xa7fcb5fee807b060 0x514ff96bfdd00f60 0x03fe007ff807f850 0x3407fc00fff00ff0

def z726 : W := mkw 0x5056d6e2a8df6e32 0x16a0adadc551bedc 0xe0fe73e3b9fe0612 0xebc1fce7c773fc0c

def z727 : W := mkw 0xf7aa201777b00000 0x23ef54402eef6000 0xfffe701ffff8005f 0xfbfffce03ffff000

def z728 : W := mkw 0x7d315f2ef22d9ae4 0x12fa62be5de45b35 0x9f31f07f8639c794 0x1b3e63e0ff0c738f

def z729 : W := mkw 0x0855fff8884f6f9c 0x4810abfff1109edf 0x0001fff80007ffa0 0x440003fff0000fff

def z730 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cfe0c6441f9fe58 0x1c39fc18c883f3fc

def z731 : W := mkw 0xfbfdef7905000108 0x4bf7fbdef20a0002 0xfffffff8060001bf 0xc3fffffff00c0003

def z732 : W := mkw 0x752a000777b00000 0x22ea54000eef6000 0x7cfe0007fff8005d 0xb8f9fc000ffff000

def z733 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x8301f07f87c7c7e2 0x7f0603e0ff0f8f8f

def z734 : W := mkw 0x58015a82a807b060 0x12b002b505500f60 0xe001ff87b807f867 0xf7c003ff0f700ff0

def z735 : W := mkw 0xfbfd8c633768de52 0x27f7fb18c66ed1bc 0xe3018c63be01fe22 0xa7c60318c77c03fc

def z736 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0xfccff38000000006 0xc3f99fe700000000

def z737 : W := mkw 0xfbfdef7905404410 0x43f7fbdef20a8088 0xffffffff87c1c67f 0xffffffffff0f838c

def z738 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfcfe0007fff8004c 0xbbf9fc000ffff000

def z739 : W := mkw 0x04021084c8dffe72 0x140804210991bffc 0x0000000441fffe40 0x1c0000000883fffc

def z740 : W := mkw 0x0c57ef7f77b00000 0x6018afdefeef6000 0x0001fffffff80060 0x780003fffffff000

def z741 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff806441f9fe54 0x1c39ff00c883f3fc

def z742 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0x7ffffff800000038 0xc0fffffff0000000

def z743 : W := mkw 0x2d6789cc5af2f4d6 0x045acf1398b5e5e9 0x7fcf839c3fc7c186 0xf0ff9f07387f8f83

def z744 : W := mkw 0xf7aa430f77b00000 0x63ef54861eef6000 0xfffe0387fff8005f 0xbbfffc070ffff000

def z745 : W := mkw 0x0c578d6c40d8de52 0x0418af1ad881b1bc 0x1cff8ffc41f9fe7d 0x5c39ff1ff883f3fc

def z746 : W := mkw 0xfbfdef7905404518 0x4bf7fbdef20a808a 0xffffffff87c007ff 0xfbffffffff0f800f

def z747 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfcffffe00000003d 0x83f9ffffc0000000

def z748 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xffff8007fff9c07f 0xbfffff000ffff380

def z749 : W := mkw 0x797dcf6800000000 0x42f2fb9ed0000000 0xfcffffe00000003f 0xc3f9ffffc0000000

def z750 : W := mkw 0x04021086e89fba62 0x140804210dd13f74 0x00000007f83ff840 0x340000000ff07ff0

def z751 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63000ff87e3e3fe2 0xecc6001ff0fc7c7f

def z752 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0xe3c1f07fffc7c7ff 0xffc783e0ffff8f8f

def z753 : W := mkw 0x58015a82a807b060 0x12b002b505500f60 0xe001ff83f807f86b 0xe7c003ff07f00ff0

def z754 : W := mkw 0x793d6f3800000000 0x42f27ade70000000 0x7c3e7f9800000008 0xc0f87cff30000000

def z755 : W := mkw 0x04021087ffbfbae4 0x300804210fff7f75 0x00000007ffffffc0 0x3c0000000fffffff

def z756 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xffffff800000001f 0x83ffffff00000000

def z757 : W := mkw 0x0855ce6000000000 0x0010ab9cc0000000 0x1cffffe00000003d 0x4039ffffc0000000

def z758 : W := mkw 0x5c035a86e897b060 0x12b806b50dd12f60 0xfc3fff87f83ff86f 0xf7f87fff0ff07ff0

def z759 : W := mkw 0xfbfdef7812200000 0x43f7fbdef0244000 0xfffffff87e3e07ff 0xeffffffff0fc7c0f

def z760 : W := mkw 0xfbfdef7800080a00 0x43f7fbdef0001014 0xfffffff80038063f 0xcbfffffff000700c

def z761 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6441fffe7f 0x7c39ff18c883fffc

def z762 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6441f9fe2c 0x1439ff18c883f3fc

def z763 : W := mkw 0xdacdead01a2a2a84 0x43b59bd5a0345455 0x9ccff0007e3e3fc4 0x2f399fe000fc7c7f

def z764 : W := mkw 0x58154e2000000000 0x02b02a9c40000000 0xfc3fff800000002f 0xc3f87fff00000000

def z765 : W := mkw 0xf7aa631c40d8de52 0x47ef54c63881b1bc 0xe300739c41f9fe42 0xdfc600e73883f3fc

def z766 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1fff8c6447f9fe7f 0x3c3fff18c88ff3fc

def z767 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe007ffff8007f 0xfbfffc00fffff000

def z768 : W := mkw 0xfbfdef7905000000 0x43f7fbdef20a0000 0xffffffff87c607ff 0xffffffffff0f8c0f

def z769 : W := mkw 0xabab5a819fb7b060 0x315756b5033f6f60 0x03ffff8007fff830 0x4c07ffff000ffff0

def z770 : W := mkw 0x04021086e897b060 0x100804210dd12f60 0x00000007f9fff840 0x3c0000000ff3fff0

def z771 : W := mkw 0x213c05a81a2a2a84 0x4042780b50345455 0x633e0ff87e3e3ffb 0xecc67c1ff0fc7c7f

def z772 : W := mkw 0x5c075a86e897b062 0x16b80eb50dd12f60 0xfc0fff87f807f86f 0xf7f81fff0ff00ff0

def z773 : W := mkw 0x0c130c2440989a40 0x0018261848813134 0x1cff8c6441f9fe7d 0x1c39ff18c883f3fc

def z774 : W := mkw 0x50005282a8072020 0x12a000a505500e40 0xe001ff87f807f86f 0xf7c003ff0ff00ff0

def z775 : W := mkw 0xdaddef7800000000 0x43b5bbdef0000000 0x9cfffff80000003d 0x4339fffff0000000

def z776 : W := mkw 0xf3a8319bbf27218c 0x2be75063377e4e43 0xe300739bbe060182 0xe3c600e7377c0c03

def z777 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87e3e3fd8 0xacc6601ff0fc7c7f

def z778 : W := mkw 0xfbfdef7800404410 0x43f7fbdef0008088 0xfffffff801c0063f 0xcbfffffff003800c

def z779 : W := mkw 0xfbfdef7905000000 0x43f7fbdef20a0000 0xfffffffb8600003f 0xe3fffffff70c0000

def z780 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6447fffffd 0x3c39ff18c88fffff

def z781 : W := mkw 0x8e973c35c59d9b4a 0x0d1d2e786b8b3b36 0x9f3e7c1bc63e398a 0x633e7cf8378c7c73

def z782 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f807f82c 0xd7f803ff0ff00ff0

def z783 : W := mkw 0xfbfdef7800080a00 0x43f7fbdef0001014 0xfffffff800003e3f 0xc7fffffff000007c

def z784 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f801f82f 0xd3f803ff0ff003f0

def z785 : W := mkw 0x0c578c6660d8de52 0x0418af18ccc1b1bc 0x1cff8c67f9f9fe7d 0x3c39ff18cff3f3fc

def z786 : W := mkw 0xfbbd6f3800000000 0x43f77ade70000000 0xff3e7ff80000003b 0xc3fe7cfff0000000

def z787 : W := mkw 0xf7aa211f77b00000 0x63ef54423eef6000 0xfffe001ffff8005f 0xbbfffc003ffff000

def z788 : W := mkw 0x580d4a0000000000 0x42b01a9400000000 0xfc0fff800000002f 0xc3f81fff00000000

def z789 : W := mkw 0xf3a87293bf272128 0x3be750e5277e4e42 0xe300739bbe060182 0xe3c600e7377c0c03

def z790 : W := mkw 0x5c014a0660009040 0x02b802940cc00120 0xfc01ff87f801f86f 0xf7f803ff0ff003f0

def z791 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0x9ffffff800000034 0x433ffffff0000000

def z792 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0x7c3fff8000000028 0xc0f87fff00000000

def z793 : W := mkw 0x0c57ce6440d8de52 0x0418af9cc881b1bc 0x1cffffe441f9fe7d 0x5c39ffffc883f3fc

def z794 : W := mkw 0x79294a0000000000 0x02f2529400000000 0xfc3fff800000002f 0xc3f87fff00000000

def z795 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0xe331fff87e3e3fff 0xefc663fff0fc7c7f

def z796 : W := mkw 0x0c57cf6c40d8de52 0x4418af9ed881b1bc 0x1cff8fe441f9fe7d 0x1c39ff1fc883f3fc

def z797 : W := mkw 0xfbedeb5800000000 0x43f7dbd6b0000000 0xfccff38000000004 0x83f99fe700000000

def z798 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007fffe07df 0xbffffc000ffffc0f

def z799 : W := mkw 0x797def7800000000 0x42f2fbdef0000000 0x7c3fff8000000008 0x80f87fff00000000

def z800 : W := mkw 0xf3a81083bf272020 0x33e75021077e4e40 0xe3000003be060002 0xa3c60000077c0c00

def z801 : W := mkw 0x8682000777b00000 0x210d04000eef6000 0x9ffe0007fff8005f 0x3b3ffc000ffff000

def z802 : W := mkw 0x0c47884440d0d452 0x04188f108881a1a8 0x1cff8c0441f9f87d 0x1c39ff180883f3f0

def z803 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfcfe0007f9f8005d 0x9bf9fc000ff3f000

def z804 : W := mkw 0xfbedeb5800000000 0x43f7dbd6b0000000 0xfffff3980000001f 0xc3ffffe730000000

def z805 : W := mkw 0x0040904080454410 0x0000812081008a88 0x83c1f07f87c7c7f7 0x7f0783e0ff0f8f8f

def z806 : W := mkw 0xfbfdef7800009040 0x43f7fbdef0000120 0xfffffff80001f83f 0xc7fffffff00003f0

def z807 : W := mkw 0xdad5ee7000000000 0x03b5abdce0000000 0xfffffff80000003f 0xc3fffffff0000000

def z808 : W := mkw 0xfbfdef7800404410 0x43f7fbdef0008088 0xfffffff80001c63f 0xc7fffffff000038c

def z809 : W := mkw 0xabfdef7800000000 0x4157fbdef0000000 0x1ffffff80000003d 0x403ffffff0000000

def z810 : W := mkw 0x7d3b4fae7ababae4 0x32fa769f5cf57575 0x7c3e0f8078383808 0x80f87c1f00f07070

def z811 : W := mkw 0x797def7800000000 0x42f2fbdef0000000 0x7f3ffff80000003b 0xc0fe7ffff0000000

def z812 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0c07fff8387f 0xbffffc180ffff070

def z813 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87e3e3faa 0xe4c6601ff0fc7c7f

def z814 : W := mkw 0x0855ef7800000000 0x4010abdef0000000 0x1c3ffff800000028 0x40387ffff0000000

def z815 : W := mkw 0xdacdeb5800000000 0x43b59bd6b0000000 0x9ccff39800000004 0x43399fe730000000

def z816 : W := mkw 0x8280100185050000 0x01050020030a0a00 0x83c1f07f87c7c7f7 0x7f0783e0ff0f8f8f

def z817 : W := mkw 0xfbfdef7800404518 0x4bf7fbdef000808a 0xfffffff8000007bf 0xc3fffffff000000f

def z818 : W := mkw 0xf3a8739bbf272020 0x73e750e7377e4e40 0xe300739bbe060002 0xe3c600e7377c0c00

def z819 : W := mkw 0xf3aa000337b00000 0x23e75400066f6000 0xfffe0003bff8001f 0xabfffc00077ff000

def z820 : W := mkw 0x001004a0080a2a00 0x0000200940101454 0x63300ff87e3e3ffb 0xecc6601ff0fc7c7f

def z821 : W := mkw 0xfbfdef7800080a00 0x43f7fbdef0001014 0xfffffff8463e3fff 0xeffffffff08c7c7f

def z822 : W := mkw 0x5c035a86e897b060 0x12b806b50dd12f60 0xfc01ff87f9fff86f 0xfff803ff0ff3fff0

def z823 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffff3f800000016 0xc3ffffe7f0000000

def z824 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xff01ff9ffe07f9ef 0xf7fe03ff3ffc0ff3

def z825 : W := mkw 0xa7a2000557b00000 0x014f44000aaf6000 0xfffe0007fff8005f 0xbbfffc000ffff000

def z826 : W := mkw 0x0402000440909040 0x0008040008812120 0x1cfe000441f9f85d 0x1c39fc000883f3f0

def z827 : W := mkw 0x7975cf6800000000 0x02f2eb9ed0000000 0xfffffff80000003f 0xc3fffffff0000000

def z828 : W := mkw 0xfbbd6f3800000000 0x43f77ade70000000 0xff3fff980000002f 0xc3fe7fff30000000

def z829 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c0441f9fe4c 0x1c39ff180883f3fc

def z830 : W := mkw 0xf3a8631800000000 0x43e750c630000000 0xff3e73980000000a 0xc3fe7ce730000000

def z831 : W := mkw 0xfbfdef7812200084 0x43f7fbdef0244001 0xfffffff8060001bf 0xc3fffffff00c0003

def z832 : W := mkw 0x0855dfe8884ffef6 0x1410abbfd1109ffd 0x0001fff80007ffa0 0x440003fff0000fff

def z833 : W := mkw 0xf7aa010f77b00084 0x23ef54021eef6001 0xfffe001ffff801df 0xbbfffc003ffff003

def z834 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x7cff8c6479f9fe7f 0xbcf9ff18c8f3f3fc

def z835 : W := mkw 0xfbfdef7905404518 0x4bf7fbdef20a808a 0xfffffff801c0003f 0xc3fffffff0038000

def z836 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff8000607bf 0xc7fffffff0000c0f

def z837 : W := mkw 0x585def7800000000 0x42b0bbdef0000000 0x1c0ffff800000020 0x40381ffff0000000

def z838 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f87c7c7a6 0x770783e0ff0f8f8f

def z839 : W := mkw 0xa7aa000777b00000 0x214f54000eef6000 0x1ffe0007fff8005d 0x383ffc000ffff000

def z840 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff80000001c 0x83fffffff0000000

def z841 : W := mkw 0xf3a8538bbf2720a4 0x33e750a7177e4e41 0xe300739bbe060182 0xe3c600e7377c0c03

def z842 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe001ffffe01df 0xfbfffc003ffffc03

def z843 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87e3e3f9a 0xe8c6601ff0fc7c7f

def z844 : W := mkw 0xf7aa201777b00108 0x2bef54402eef6002 0xfffe001ffff801df 0xbbfffc003ffff003

def z845 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f801f84f 0xb3f803ff0ff003f0

def z846 : W := mkw 0xfbfdef7917200000 0x63f7fbdef22e4000 0xfffffff80600003f 0xc3fffffff00c0000

def z847 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1fc7fc7c7ffff 0x7f0783f8ff8f8fff

def z848 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff8060007bf 0xcbfffffff00c000f

def z849 : W := mkw 0xfbfdef7917684f9c 0x4bf7fbdef22ed09f 0xfffffff807f807bf 0xcbfffffff00ff00f

def z850 : W := mkw 0x08578c6000d8de52 0x0410af18c001b1bc 0x1cff8c6001f9fe3d 0x0c39ff18c003f3fc

def z851 : W := mkw 0x000000801a2a2a84 0x0000000100345455 0x63000ff87e3e3ffb 0xecc6001ff0fc7c7f

def z852 : W := mkw 0xfbfdef7800484e10 0x43f7fbdef000909c 0xfffffffc41f9fe7f 0xdffffffff883f3fc

def z853 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff84000387f 0xc7fffffff0800070

def z854 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63318ffc7e3fffff 0xfcc6631ff8fc7fff

def z855 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe007ffff807df 0xbbfffc00fffff00f

def z856 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c7c41fffffd 0x5c39ff18f883ffff

def z857 : W := mkw 0x5c0d5a86e807b060 0x52b81ab50dd00f60 0xfc0fff87f807f86f 0xf7f81fff0ff00ff0

def z858 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfcfe0007f9f8004f 0xb3f9fc000ff3f000

def z859 : W := mkw 0xfbfdef780048de52 0x47f7fbdef00091bc 0xfffffffc01c1fe7f 0xdffffffff80383fc

def z860 : W := mkw 0xf3a8000117200000 0x03e75000022e4000 0xfffe0007fff8005f 0xbbfffc000ffff000

def z861 : W := mkw 0x58015a82a807b060 0x12b002b505500f60 0xfc01ff83b807f82f 0xe7f803ff07700ff0

def z862 : W := mkw 0xdaddef7800000000 0x43b5bbdef0000000 0xfccffff80000002f 0xc3f99ffff0000000

def z863 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6441f9fe1c 0x1839ff18c883f3fc

def z864 : W := mkw 0xfbfdef780048de52 0x47f7fbdef00091bc 0xfffffff84039fe7f 0xcffffffff08073fc

def z865 : W := mkw 0x04021086e8d7f472 0x140804210dd1afe8 0x00000007f9c7f840 0x340000000ff38ff0

def z866 : W := mkw 0xfbbd6f3800000000 0x43f77ade70000000 0xfffe7f980000001f 0xc3fffcff30000000

def z867 : W := mkw 0xfbfdef7812280a00 0x43f7fbdef0245014 0xfffffff87e383e7f 0xeffffffff0fc707c

def z868 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007f9f8001f 0x93fffc000ff3f000

def z869 : W := mkw 0x58014a0000000000 0x02b0029400000000 0xfcffff800000003f 0xc3f9ffff00000000

def z870 : W := mkw 0x08015a808807b060 0x101002b501100f60 0xe001ff87f807f86f 0xf7c003ff0ff00ff0

def z871 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0xfccfff800000000c 0x83f99fff00000000

def z872 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87b807f826 0xf7f803ff0f700ff0

def z873 : W := mkw 0xf7aa621777b00000 0x63ef54c42eef6000 0xfffe7007fff8005f 0xbbfffce00ffff000

def z874 : W := mkw 0x54001086e8072000 0x02a800210dd00e40 0xfc01ff87f807f86f 0xf7f803ff0ff00ff0

def z875 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0x7ffe0007fff80058 0xb8fffc000ffff000

def z876 : W := mkw 0xfbfdef7800080a00 0x43f7fbdef0001014 0xfffffff84038383f 0xc3fffffff0807070

def z877 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfcffff87f807f87f 0xf7f9ffff0ff00ff0

def z878 : W := mkw 0xfbb94f2800000000 0x03f7729e50000000 0xfffffff80000003f 0xc3fffffff0000000

def z879 : W := mkw 0xfbedea5000000000 0x43f7dbd4a0000000 0xffffff800000003f 0xc3ffffff00000000

def z880 : W := mkw 0x04001086e807b060 0x100800210dd00f60 0xe001ff87f807f86f 0xf7c003ff0ff00ff0

def z881 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x9cfffc6441f9fe7f 0x5f39fff8c883f3fc

def z882 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xff01fffff807f87f 0xf7fe03fffff00ff0

def z883 : W := mkw 0x0452846440d84e10 0x0008a508c881b09c 0x1cff8c6441f9fe7d 0x1c39ff18c883f3fc

def z884 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff83f807f82a 0xe7f803ff07f00ff0

def z885 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff87800007f 0xe3fffffff0f00000

def z886 : W := mkw 0x0c57ac7440d8df5a 0x0c18af58e881b1be 0x1cff8c7c41f9fffd 0x1c39ff18f883f3ff

def z887 : W := mkw 0x0402000660900000 0x000804000cc12000 0x1cfe0007f9f8005d 0x3839fc000ff3f000

def z888 : W := mkw 0x08559ce0884ffe72 0x1410ab39c1109ffc 0x00018c600007fe20 0x04000318c0000ffc

def z889 : W := mkw 0xfbedeb5800000000 0x43f7dbd6b0000000 0xffcfff980000002f 0xc3ff9fff30000000

def z890 : W := mkw 0x0855fff8884ffe72 0x5410abfff1109ffc 0x0001fff80007fe20 0x440003fff0000ffc

def z891 : W := mkw 0x04021087ed97b060 0x300804210fdb2f60 0x00000007f9c7f840 0x340000000ff38ff0

def z892 : W := mkw 0xfbbd6f3800000000 0x43f77ade70000000 0xfc3e7f8000000008 0x83f87cff00000000

def z893 : W := mkw 0xfbfdef7800484e12 0x47f7fbdef000909c 0xfffffff80000063f 0xc3fffffff000000c

def z894 : W := mkw 0xfbfdef7b37200000 0x63f7fbdef66e4000 0xffffffffbfc0007f 0xfbffffffff7f8000

def z895 : W := mkw 0xfbbd4f2800000000 0x43f77a9e50000000 0xffffff800000003f 0xc3ffffff00000000

def z896 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff80000067f 0xcffffffff000000c

def z897 : W := mkw 0x2522000777b00000 0x204a44000eef6000 0x7ffe0007fff8005f 0xb8fffc000ffff000

def z898 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c0441f9f86d 0x1439ff180883f3f0

def z899 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87fe07ffef 0xfff803ff0ffc0fff

def z900 : W := mkw 0xd69a05af6d9a2a84 0x23ad340b5edb3455 0x9cce0fff81c63fa4 0x57399c1fff038c7f

def z901 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xffffffff8000007f 0xf3ffffffff000000

def z902 : W := mkw 0x04021086fafffef6 0x140804210df5fffd 0x00000007ffffffc0 0x3c0000000fffffff

def z903 : W := mkw 0xfbfdef7800404410 0x43f7fbdef0008088 0xfffffffc01c1c03f 0xd3fffffff8038380

def z904 : W := mkw 0x04021087fffffe72 0x340804210ffffffc 0x00000007fffffe40 0x3c0000000ffffffc

def z905 : W := mkw 0x82ccb05185454518 0x49059960a30a8a8a 0x83cff07f87c7c7f7 0x7f079fe0ff0f8f8f

def z906 : W := mkw 0xdaddef7800000000 0x43b5bbdef0000000 0x9fcffff800000037 0x433f9ffff0000000

def z907 : W := mkw 0xfbfdef7b37200000 0x63f7fbdef66e4000 0xfffffffbfe38007f 0xebfffffff7fc7000

def z908 : W := mkw 0xfbfdef7a20000000 0x43f7fbdef4400000 0xfffffffbb800003f 0xe3fffffff7700000

def z909 : W := mkw 0xfbfdef7812280a84 0x43f7fbdef0245015 0xfffffff80038003f 0xc3fffffff0007000

def z910 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xffcffff800000026 0xc3ff9ffff0000000

def z911 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0f87fff8007f 0xfbfffc1f0ffff000

def z912 : W := mkw 0x0855fef0884fff7a 0x1c10abfde1109ffe 0x0001fff80007ffa0 0x440003fff0000fff

def z913 : W := mkw 0x04021087ffff6f9c 0x280804210ffffedf 0x00000007ffffffc0 0x3c0000000fffffff

def z914 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f87c7c7b4 0x5f0783e0ff0f8f8f

def z915 : W := mkw 0xfbfdef7917200000 0x43f7fbdef22e4000 0xfffffffffff8007f 0xfbfffffffffff000

def z916 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6041f9fe38 0x0c39ff18c083f3fc

def z917 : W := mkw 0x0456846440d8de52 0x0408ad08c881b1bc 0x1cfe006441f9fe5d 0x1c39fc00c883f3fc

def z918 : W := mkw 0x7522000672b00000 0x02ea44000ce56000 0xfffe0007fff8005f 0xbbfffc000ffff000

def z919 : W := mkw 0xfbfdef780040d452 0x47f7fbdef00081a8 0xfffffff80001c03f 0xc3fffffff0000380

def z920 : W := mkw 0x0c57ee7440d8de52 0x4418afdce881b1bc 0x1cfffc6441f9fe7d 0x1c39fff8c883f3fc

def z921 : W := mkw 0xfbfdef7812200000 0x43f7fbdef0244000 0xfffffff83e00003f 0xe3fffffff07c0000

def z922 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007fff8001c 0x9bfffc000ffff000

def z923 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0xfc3fff800000000c 0x83f87fff00000000

def z924 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xff01ff87fe07f87f 0xfffe03ff0ffc0ff0

def z925 : W := mkw 0xf7aa010f77b00000 0x23ef54021eef6000 0xfffe039ffff8005f 0xfbfffc073ffff000

def z926 : W := mkw 0xf7aa000777b09040 0x23ef54000eef6120 0xfffe0007fff9f85f 0xbffffc000ffff3f0

def z927 : W := mkw 0x752a000672b00000 0x22ea54000ce56000 0xfcfe0007f9f8005f 0xbbf9fc000ff3f000

def z928 : W := mkw 0xfbfdef7812280a84 0x43f7fbdef0245015 0xfffffff846383fff 0xcffffffff08c707f

def z929 : W := mkw 0xf7aa631f77b00000 0x63ef54c63eef6000 0xe300739ffff80042 0xfbc600e73ffff000

def z930 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff80006007f 0xe7fffffff0000c00

def z931 : W := mkw 0x21301528922d0a84 0x0042602a51245a15 0x8331f07f863fc7f7 0x7f0663e0ff0c7f8f

def z932 : W := mkw 0x0c43884440d0d450 0x001887108881a1a8 0x1cff8c6441f9fe7d 0x1c39ff18c883f3fc

def z933 : W := mkw 0x0c578c6440909040 0x0018af18c8812120 0x1cff8c6441f9f87d 0x1c39ff18c883f3f0

def z934 : W := mkw 0xfba96b1800000000 0x43f752d630000000 0xffffff980000003f 0xc3ffffff30000000

def z935 : W := mkw 0xf3e8e35800000000 0x43e7d1c6b0000000 0xfffff3f80000003f 0xc3ffffe7f0000000

def z936 : W := mkw 0xfbfdef7905404518 0x4bf7fbdef20a808a 0xfffffff807c607ff 0xeffffffff00f8c0f

def z937 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0xff3ffff80000003f 0xc3fe7ffff0000000

def z938 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007bff80016 0xbbfffc000f7ff000

def z939 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83f1f07fc7ffc7ff 0x7f07e3e0ff8fff8f

def z940 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xe001ff87f807f862 0xf7c003ff0ff00ff0

def z941 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff80600007f 0xebfffffff00c0000

def z942 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6441f9f83d 0x1039ff18c883f3f0

def z943 : W := mkw 0xa3f6a57917f84f9e 0x0d47ed4af22ff09f 0x03fe007807f80790 0x0807fc00f00ff00f

def z944 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfcc1ff87f9c7f87f 0xfff983ff0ff38ff0

def z945 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xff3ffff80000002a 0xc3fe7ffff0000000

def z946 : W := mkw 0xa3fea57917f84e12 0x6547fd4af22ff09c 0x03fe007807f80610 0x0807fc00f00ff00c

def z947 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfcffff800000002f 0xc3f9ffff00000000

def z948 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c6401f9fe34 0x1c39ff18c803f3fc

def z949 : W := mkw 0xd68a000777b00000 0x23ad14000eef6000 0x9cfe0007fff8005d 0x3b39fc000ffff000

def z950 : W := mkw 0x7d374fae7ababae6 0x16fa6e9f5cf57575 0x7c3e0f8078383808 0x80f87c1f00f07070

def z951 : W := mkw 0xd682000765900000 0x03ad04000ecb2000 0xfffe0007fff8005f 0xbbfffc000ffff000

def z952 : W := mkw 0xf3a873999f27218c 0x4be750e7333e4e43 0xe300739bbe060182 0xe3c600e7377c0c03

def z953 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffff007fff8007f 0xfbffffe00ffff000

def z954 : W := mkw 0x8ad5ef7800000000 0x4115abdef0000000 0x9ffffff80000003f 0x433ffffff0000000

def z955 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0x9ffe0007fff80054 0x3b3ffc000ffff000

def z956 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x9ffff07f87c7c7ff 0x7f3fffe0ff0f8f8f

def z957 : W := mkw 0x0855bdf8884fffde 0x0c10ab7bf1109fff 0x0001fff80007ffa0 0x440003fff0000fff

def z958 : W := mkw 0xabf5ad7800000000 0x0157eb5af0000000 0xfffffff80000003f 0xc3fffffff0000000

def z959 : W := mkw 0xfbfdef7a32200000 0x63f7fbdef4644000 0xfffffff83800003f 0xc3fffffff0700000

def z960 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63300ff87e3e3fb8 0xccc6601ff0fc7c7f

def z961 : W := mkw 0xdacdea5000000000 0x43b59bd4a0000000 0x9ccfff8000000024 0x43399fff00000000

def z962 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ffe7f807fe7f 0xfff803ffcff00ffc

def z963 : W := mkw 0x0c170c2440989a42 0x04182e1848813134 0x1cff8c0441f9f87d 0x1c39ff180883f3f0

def z964 : W := mkw 0x0c03080440d8de52 0x041806100881b1bc 0x1cff8c0441f9fe7d 0x1c39ff180883f3fc

def z965 : W := mkw 0xf3b8673800000000 0x43e770ce70000000 0xfffe7ff80000003f 0xc3fffcfff0000000

def z966 : W := mkw 0x797def7800000000 0x42f2fbdef0000000 0x7cfffff80000003d 0xc0f9fffff0000000

def z967 : W := mkw 0xfbfdef7812280a84 0x43f7fbdef0245015 0xfffffff87e3807ff 0xebfffffff0fc700f

def z968 : W := mkw 0x5c035a86e897b060 0x12b806b50dd12f60 0xfccfff87f9c7f86f 0xf7f99fff0ff38ff0

def z969 : W := mkw 0xfbfdef7b25000000 0x63f7fbdef64a0000 0xfffffffb8000003f 0xc3fffffff7000000

def z970 : W := mkw 0xa3faa57917f84f9c 0x2947f54af22ff09f 0x03fe007807f80790 0x0807fc00f00ff00f

def z971 : W := mkw 0x5c0b5a86e897b060 0x32b816b50dd12f60 0xfc0fff87f807f86f 0xf7f81fff0ff00ff0

def z972 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007fff8000e 0xb3fffc000ffff000

def z973 : W := mkw 0x04021087ffb72020 0x300804210fff6e40 0x00000007fffe0040 0x380000000ffffc00

def z974 : W := mkw 0x08558c6000484e10 0x0010ab18c000909c 0x1cff8c6441f9fe7d 0x1c39ff18c883f3fc

def z975 : W := mkw 0xfbfdef7812200000 0x43f7fbdef0244000 0xfffffff87838003f 0xc3fffffff0f07000

def z976 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x9cff8c67c1f9fe7f 0x3f39ff18cf83f3fc

def z977 : W := mkw 0x5845ca4000000000 0x02b08b9480000000 0xfccfff800000002f 0xc3f99fff00000000

def z978 : W := mkw 0x0c578d6c40d8ded6 0x0418af1ad881b1bd 0x1cff8c7c41f9fffd 0x1c39ff18f883f3ff

def z979 : W := mkw 0x0442804440d8de52 0x040885008881b1bc 0x1cff806441f9fe7d 0x1c39ff00c883f3fc

def z980 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffe7ff80000001a 0xc3fffcfff0000000

def z981 : W := mkw 0xfbfdef7905000000 0x43f7fbdef20a0000 0xffffffff81c0003f 0xd3ffffffff038000

def z982 : W := mkw 0x04021085dfffffde 0x0c0804210bbfffff 0x00000007ffffffc0 0x3c0000000fffffff

def z983 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x7cff8fe441f9fe7f 0xdcf9ff1fc883f3fc

def z984 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01ff87f807f84c 0xb7f803ff0ff00ff0

def z985 : W := mkw 0xa3fca57917684f9c 0x4947f94af22ed09f 0x03fe007807f80790 0x0807fc00f00ff00f

def z986 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffffc01c0007f 0xdbfffffff8038000

def z987 : W := mkw 0xfbad6b1800000000 0x43f75ad630000000 0xff0e739800000002 0xc3fe1ce730000000

def z988 : W := mkw 0x0000100185454518 0x08000020030a8a8a 0x8301f07f87c7c7f7 0x7f0603e0ff0f8f8f

def z989 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff84038007f 0xcbfffffff0807000

def z990 : W := mkw 0x04021087fff7f578 0x380804210fffefea 0x00000007ffffffc0 0x3c0000000fffffff

def z991 : W := mkw 0xfbfdce6000000000 0x03f7fb9cc0000000 0xffffffe00000003f 0xc3ffffffc0000000

def z992 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x7ffe0ff87e3e3fff 0xecfffc1ff0fc7c7f

def z993 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1cff8c0441f9f85d 0x1839ff180883f3f0

def z994 : W := mkw 0x0c47884440d8de52 0x04188f108881b1bc 0x1cff800441f9fe5d 0x1c39ff000883f3fc

def z995 : W := mkw 0x797def7800000000 0x42f2fbdef0000000 0xfc3ffff80000002f 0xc3f87ffff0000000

def z996 : W := mkw 0xfbfdef7800404410 0x43f7fbdef0008088 0xfffffffc07c7c7ff 0xfffffffff80f8f8f

def z997 : W := mkw 0x0855ef7800000000 0x4010abdef0000000 0x1ccffff800000024 0x40399ffff0000000

def z998 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f87c7c7d4 0x3f0783e0ff0f8f8f

def z999 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1fff8c7c41f9fe7f 0x5c3fff18f883f3fc

def z1000 : W := mkw 0x212000801a222000 0x0042400100344440 0x63300ff87e3e3ffb 0xecc6601ff0fc7c7f

def z1001 : W := mkw 0xfbfdef7812280a84 0x43f7fbdef0245015 0xfffffff8063e07ff 0xeffffffff00c7c0f

def z1002 : W := mkw 0x5855ef7800000000 0x42b0abdef0000000 0xfcfffff80000003f 0xc3f9fffff0000000

def z1003 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0xe3c1ffff87c7c7ff 0xffc783ffff0f8f8f

def z1004 : W := mkw 0xf3a8631800000000 0x43e750c630000000 0xffce739800000006 0xc3ff9ce730000000

def z1005 : W := mkw 0xf3a8420000000000 0x03e7508400000000 0xfffe73800000001f 0xc3fffce700000000

def z1006 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0x63f00ffc7ffe3fff 0xfcc7e01ff8fffc7f

def z1007 : W := mkw 0x82c0a0d10d426518 0x09058141a21a84ca 0x63c00ff87fc63ffb 0xecc7801ff0ff8c7f

def z1008 : W := mkw 0xfbedeb5800000000 0x43f7dbd6b0000000 0xffcff3f800000037 0xc3ff9fe7f0000000

def z1009 : W := mkw 0x5c015a86e807b060 0x12b802b50dd00f60 0xfc01fffff807ffef 0xf7f803fffff00fff

def z1010 : W := mkw 0x5402000777b00000 0x22a804000eef6000 0xfcfe0007fff8005f 0xbbf9fc000ffff000

def z1011 : W := mkw 0xf7aa420777b00000 0x23ef54840eef6000 0xfffe7387fff8005f 0xfbfffce70ffff000

def z1012 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfcfffff80000002c 0xc3f9fffff0000000

def z1013 : W := mkw 0x0c011884c807b040 0x0018023109900f60 0xfc01ff87f807f86f 0xf7f803ff0ff00ff0

def z1014 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffffc0001c07f 0xd7fffffff8000380

def z1015 : W := mkw 0x793d4f2800000000 0x42f27a9e50000000 0xfc3e7f800000000a 0xc3f87cff00000000

def z1016 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xffffff980000000e 0xc3ffffff30000000

def z1017 : W := mkw 0xf3fce77800000000 0x43e7f9cef0000000 0xfffe73f80000001f 0xc3fffce7f0000000

def z1018 : W := mkw 0xdec7fa57e5d5d57a 0x1fbd8ff4afcbabaa 0x9ccff00781c1c004 0x13399fe00f038380

def z1019 : W := mkw 0x0c578c6440d8de52 0x0418af18c881b1bc 0x1fff8c7c47f9fffd 0x1c3fff18f88ff3ff

def z1020 : W := mkw 0xda894a0000000000 0x03b5129400000000 0xfccfff800000002f 0xc3f99fff00000000

def z1021 : W := mkw 0xdaddee7000000000 0x43b5bbdce0000000 0xfcffffe00000003f 0xc3f9ffffc0000000

def z1022 : W := mkw 0xfbfdef7905404518 0x4bf7fbdef20a808a 0xfffffffc07c1c7ff 0xdffffffff80f838f

def z1023 : W := mkw 0xf3f8a57800000000 0x03e7f14af0000000 0xfffffff80000003f 0xc3fffffff0000000

def z1024 : W := mkw 0xfbfdef7905000000 0x43f7fbdef20a0000 0xfffffff807c0003f 0xcbfffffff00f8000

def z1025 : W := mkw 0x82c0b05185454518 0x09058160a30a8a8a 0x83c1f07f87c7c796 0x7b0783e0ff0f8f8f

def z1026 : W := mkw 0xd68a000765900000 0x23ad14000ecb2000 0xfcfe0007f9f8005f 0xbbf9fc000ff3f000

def z1027 : W := mkw 0xfbfdef7812200000 0x43f7fbdef0244000 0xfffffff80638003f 0xcbfffffff00c7000

def z1028 : W := mkw 0x213005a81a2a2a84 0x0042600b50345455 0xe3300ffffe3e3fff 0xffc6601ffffc7c7f

def z1029 : W := mkw 0xf7aa000660900000 0x03ef54000cc12000 0xfffe0007f9f8005f 0xbbfffc000ff3f000

def z1030 : W := mkw 0x04021087eddfff7a 0x1c0804210fdbbffe 0x00000007ffffffc0 0x3c0000000fffffff

def z1031 : W := mkw 0x0412042440d8de52 0x040824084881b1bc 0x1cfe0c6441f9fe7d 0x1c39fc18c883f3fc

def z1032 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0007fffe007f 0xfffffc000ffffc00

def z1033 : W := mkw 0xfbfdef7800000000 0x43f7fbdef0000000 0xfffffff8060601bf 0xe3fffffff00c0c03

def z1034 : W := mkw 0xf7aa000777b00000 0x23ef54000eef6000 0xfffe0003fff8001a 0xabfffc0007fff000

def z1035 : W := mkw 0xfbfdef7800080a84 0x43f7fbdef0001015 0xfffffff8000007bf 0xc3fffffff000000f

def z1036 : W := mkw 0xfbe9ea5000000000 0x03f7d3d4a0000000 0xfffffff80000003f 0xc3fffffff0000000

def z1037 : W := mkw 0x0c57ac7440d8de52 0x0418af58e881b1bc 0x1cfffc7c41f9fe7d 0x5c39fff8f883f3fc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z8,z5,z6])],[(0,[z9,z0,z1,z2,z4,z5,z6])],[(0,[z10,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z11,z2,z4,z6]),(0,[z12,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z13,z4,z5,z6]),(0,[z0,z1,z2,z14,z4,z5,z6])],[(0,[z0,z1,z15,z4,z5,z6,z16]),(0,[z17,z0,z1,z2,z4,z6,z18]),(0,[z0,z1,z2,z4,z19,z5,z6]),(0,[z20,z0,z1,z2,z4,z5,z6]),(0,[z21,z0,z1,z2,z4,z5,z6])],[(0,[z0,z22,z1,z2,z4,z5,z6]),(0,[z23,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z24,z2,z4,z5,z6])],[(0,[z0,z1,z25,z2,z4,z5,z6]),(0,[z0,z1,z26,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z28]),(0,[z0,z1,z2,z4,z5,z29,z6]),(0,[z0,z1,z30,z2,z4,z5,z6]),(0,[z0,z31,z1,z2,z4,z32,z5]),(0,[z0,z1,z2,z4,z5,z6,z33])],[(0,[z0,z1,z2,z4,z34,z5,z6]),(1,[z0,z1,z35,z36,z5,z6]),(0,[z0,z1,z37,z2,z38,z4,z5]),(0,[z0,z39,z1,z2,z4,z5,z6]),(0,[z0,z1,z40,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z41]),(0,[z42,z0,z1,z2,z4,z5,z6]),(0,[z43,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z44,z4,z5,z6]),(1,[z45,z0,z1,z46,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z47,z0,z1,z2,z4,z5,z6]),(0,[z48,z0,z1,z2,z4,z5,z6])],[(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z50,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z6]),(0,[z51,z0,z1,z2,z38,z4,z5])],[(0,[z0,z1,z2,z4,z52,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z53]),(0,[z54,z0,z1,z2,z4,z55,z6])],[(0,[z56,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z57,z4,z5,z6]),(0,[z0,z1,z2,z58,z4,z5,z6])],[(0,[z0,z1,z2,z59,z4,z5,z6]),(0,[z60,z0,z1,z2,z4,z5,z6]),(0,[z0,z61,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z62,z5]),(0,[z63,z0,z1,z2,z64,z5,z6]),(0,[z65,z0,z1,z66,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z67,z6]),(0,[z68,z0,z1,z2,z4,z5,z6])],[(0,[z69,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z70,z6]),(0,[z0,z71,z1,z2,z4,z5,z72]),(0,[z0,z1,z2,z4,z73,z5,z6]),(0,[z0,z1,z74,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z75,z5,z6]),(0,[z0,z1,z2,z76,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z77]),(0,[z0,z1,z2,z38,z5,z6,z78]),(0,[z0,z1,z2,z4,z5,z6,z78])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z79])],[(0,[z0,z1,z2,z4,z80,z5,z6]),(0,[z1,z2,z4,z8,z5,z6,z81]),(0,[z0,z1,z2,z4,z5,z6,z82]),(0,[z0,z1,z2,z83,z84,z4,z6])],[(0,[z85,z1,z2,z4,z86,z5,z6]),(0,[z87,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z88,z6])],[(0,[z0,z1,z2,z89,z4,z5,z6]),(0,[z63,z0,z90,z2,z4,z5,z6]),(0,[z0,z1,z91,z2,z4,z5,z6])],[(0,[z0,z1,z92,z2,z4,z5,z6]),(0,[z93,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z94,z2,z4,z5,z6]),(0,[z0,z1,z2,z95,z4,z5,z6])],[(0,[z0,z1,z2,z4,z96,z5,z6]),(1,[z0,z1,z66,z4,z6,z16])],[(0,[z17,z97,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z98,z5,z6]),(0,[z99,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z100,z6])],[(0,[z0,z1,z2,z101,z4,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z103,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z104,z28]),(0,[z0,z1,z2,z4,z5,z6,z105])],[(1,[z0,z1,z2,z106,z4,z5]),(0,[z54,z107,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z6,z108]),(0,[z45,z0,z109,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z110,z5,z6])],[(0,[z111,z0,z1,z2,z4,z5,z6]),(0,[z112,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z100,z6]),(0,[z0,z1,z2,z113,z4,z5,z6]),(0,[z0,z1,z2,z4,z114,z5,z6])],[],[(0,[z115,z0,z1,z36,z4,z5,z6]),(0,[z116,z0,z1,z2,z4,z32,z5]),(0,[z117,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z5,z6]),(0,[z0,z1,z2,z4,z55,z6,z18])],[(0,[z0,z1,z2,z4,z118,z5,z6]),(1,[z0,z1,z2,z4,z119,z6]),(1,[z63,z0,z2,z34,z5,z6]),(0,[z116,z0,z31,z2,z4,z5,z6]),(0,[z0,z1,z2,z120,z4,z5,z6]),(0,[z0,z1,z2,z121,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z122])]],
   [[(0,[z123,z0,z124,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z125,z5,z6])],[(0,[z126,z0,z1,z2,z4,z5,z6]),(0,[z0,z127,z1,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z5,z28]),(0,[z128,z0,z1,z4,z34,z5,z6]),(0,[z0,z1,z2,z129,z4,z5,z6])],[(0,[z130,z0,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z132,z4,z5,z6]),(0,[z0,z1,z2,z133,z4,z5,z6]),(0,[z0,z1,z2,z134,z4,z5,z6]),(0,[z0,z1,z2,z4,z135,z5,z6]),(0,[z0,z1,z2,z4,z136,z5,z6])],[(0,[z0,z1,z2,z4,z137,z5,z6]),(0,[z0,z1,z2,z138,z4,z5,z6]),(0,[z0,z1,z4,z139,z34,z5,z6]),(0,[z140,z0,z1,z2,z4,z5,z6]),(0,[z141,z0,z1,z2,z4,z5,z6])],[(0,[z85,z142,z1,z2,z4,z5,z6]),(0,[z143,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z144,z5,z6])],[(0,[z85,z0,z1,z2,z145,z5,z6]),(0,[z0,z1,z146,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z67,z5,z6]),(0,[z0,z1,z2,z4,z147,z5,z6]),(0,[z0,z1,z2,z38,z148,z4,z5]),(1,[z149,z0,z1,z2,z38,z5]),(0,[z150,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z131,z2,z4,z5,z6]),(0,[z0,z151,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z81]),(0,[z152,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z153,z5,z6]),(0,[z0,z1,z2,z4,z154,z5,z6]),(0,[z107,z0,z1,z2,z4,z5,z78])]],
   [[(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z0,z156,z2,z133,z4,z5,z6]),(0,[z0,z1,z2,z4,z157,z5,z6]),(0,[z158,z0,z1,z2,z83,z4,z6])],[(0,[z0,z1,z159,z2,z4,z5,z6]),(0,[z0,z1,z2,z160,z4,z5,z6]),(0,[z0,z161,z1,z2,z4,z5,z6]),(0,[z162,z0,z1,z2,z4,z5,z6])],[(0,[z163,z0,z1,z2,z4,z5,z6]),(0,[z0,z71,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z84,z100,z6])],[(0,[z164,z0,z1,z2,z4,z5,z6]),(0,[z165,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z166,z5,z6])],[(0,[z130,z0,z1,z2,z4,z5,z167]),(1,[z0,z1,z168,z2,z4,z5]),(0,[z0,z1,z169,z2,z4,z5,z6]),(0,[z0,z90,z2,z64,z4,z5,z6]),(0,[z170,z0,z1,z2,z4,z5,z6])],[(0,[z171,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z172,z5,z6])],[(0,[z0,z1,z2,z4,z5,z173,z6]),(0,[z0,z1,z2,z4,z5,z6,z174]),(0,[z0,z1,z175,z2,z4,z5,z6]),(0,[z176,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z177,z6]),(0,[z178,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z179]),(0,[z115,z0,z1,z133,z4,z5,z6]),(0,[z107,z180,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z181]),(0,[z0,z1,z4,z67,z5,z6,z16]),(0,[z0,z1,z2,z4,z5,z182,z6])],[(1,[z0,z1,z2,z4,z5,z167]),(0,[z0,z1,z2,z4,z5,z6,z183]),(0,[z0,z1,z184,z2,z4,z5,z6]),(1,[z0,z1,z37,z4,z5,z185]),(0,[z0,z1,z2,z186,z4,z5,z6]),(0,[z54,z0,z1,z2,z4,z5,z18])],[(0,[z0,z1,z187,z2,z4,z5,z6]),(0,[z54,z188,z0,z1,z2,z4,z6]),(0,[z189,z0,z1,z2,z4,z5,z6]),(1,[z128,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z190,z5,z6]),(0,[z0,z191,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z192,z5,z6]),(0,[z0,z1,z2,z193,z4,z5,z6]),(0,[z0,z1,z194,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z195,z6])],[(0,[z196,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z2,z4,z197,z5,z6])],[(1,[z142,z1,z2,z145,z5,z6]),(0,[z17,z1,z2,z4,z5,z6,z81]),(0,[z27,z1,z2,z4,z5,z6,z28]),(0,[z198,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z199,z5,z6])],[(0,[z0,z1,z200,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z201,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z202]),(0,[z0,z1,z2,z4,z5,z6,z203]),(0,[z0,z1,z156,z2,z4,z5,z6]),(1,[z65,z0,z1,z4,z67,z6]),(0,[z0,z1,z2,z4,z5,z6,z204])],[(0,[z0,z1,z2,z205,z4,z5,z6]),(0,[z142,z1,z2,z145,z4,z5,z6]),(0,[z0,z1,z2,z4,z206,z5,z6]),(0,[z17,z0,z1,z2,z4,z6,z81]),(0,[z0,z1,z2,z4,z5,z6,z72])]],
   [[(0,[z0,z1,z2,z145,z4,z5,z6]),(0,[z0,z1,z36,z4,z46,z5,z6])],[(0,[z0,z1,z2,z207,z4,z5,z6]),(0,[z208,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z209,z4,z5,z6]),(0,[z0,z1,z2,z4,z210,z5,z6])],[(0,[z0,z211,z1,z2,z4,z5,z6])],[(0,[z17,z0,z1,z2,z4,z8,z6]),(0,[z0,z1,z37,z2,z4,z212,z5])],[(0,[z0,z1,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z213,z4,z5,z6]),(0,[z0,z214,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z215,z5,z6]),(0,[z216,z0,z1,z2,z4,z5,z6]),(1,[z158,z0,z1,z2,z83,z6]),(0,[z107,z0,z1,z2,z4,z6,z18])],[(0,[z0,z1,z2,z4,z5,z6,z217]),(0,[z0,z1,z2,z4,z55,z19,z5]),(0,[z0,z1,z218,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z219,z5,z6]),(0,[z0,z1,z2,z4,z220,z5,z6])],[(0,[z221,z0,z1,z2,z4,z5,z6]),(0,[z1,z15,z2,z205,z4,z5,z6]),(0,[z51,z0,z1,z2,z4,z212,z5])],[(0,[z0,z222,z1,z2,z4,z5,z6]),(0,[z65,z0,z1,z15,z4,z5,z6]),(0,[z0,z1,z2,z223,z4,z5,z6])]],
   [[(0,[z224,z0,z1,z2,z4,z5,z6]),(0,[z17,z0,z1,z225,z4,z5,z6]),(0,[z0,z1,z2,z4,z226,z5,z6])],[(0,[z0,z1,z227,z2,z4,z5,z6]),(0,[z0,z1,z228,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z229,z5,z6]),(0,[z0,z230,z1,z2,z4,z5,z6]),(0,[z231,z0,z1,z2,z4,z5,z6])],[(0,[z115,z0,z109,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z232,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z104]),(1,[z0,z1,z2,z148,z5,z78])],[(0,[z0,z233,z1,z2,z4,z5,z6]),(0,[z234,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z235]),(0,[z0,z1,z2,z38,z4,z5,z28]),(0,[z0,z1,z2,z4,z5,z236,z6]),(0,[z107,z0,z1,z2,z4,z32,z5]),(0,[z0,z1,z2,z237,z4,z5,z6])],[(0,[z238,z1,z15,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z5,z6]),(0,[z27,z0,z1,z37,z2,z4,z5])],[(0,[z0,z1,z156,z4,z46,z5,z6]),(0,[z0,z1,z37,z2,z4,z32,z5]),(0,[z0,z240,z1,z2,z4,z5,z6])],[(0,[z241,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z242,z4,z5,z6]),(0,[z0,z1,z2,z4,z243,z5,z6]),(1,[z180,z1,z2,z4,z5,z6])]],
   [[(0,[z244,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z245,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z32,z5])],[(0,[z97,z0,z1,z2,z4,z19,z5]),(0,[z246,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z247,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z248]),(0,[z0,z1,z2,z4,z249,z5,z6]),(0,[z51,z0,z1,z4,z212,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z250])],[(0,[z0,z1,z2,z4,z5,z6,z185])],[(0,[z251,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z252]),(1,[z0,z31,z2,z4,z5,z104]),(0,[z0,z1,z2,z4,z253,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z254])],[(1,[z255,z0,z1,z2,z4,z6]),(0,[z65,z188,z0,z1,z2,z4,z6]),(0,[z143,z0,z71,z2,z4,z5,z6]),(1,[z1,z2,z4,z256,z5,z6]),(0,[z0,z257,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z258,z5,z6]),(0,[z0,z1,z2,z4,z259,z5,z6])],[(0,[z130,z0,z124,z2,z4,z5,z6]),(0,[z0,z1,z2,z260,z4,z5,z6]),(0,[z0,z1,z2,z4,z261,z5,z6])],[(0,[z0,z1,z2,z262,z4,z5,z6])]],
   [[(0,[z263,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z264,z5,z6]),(0,[z0,z1,z2,z4,z5,z265,z6])],[(0,[z0,z1,z266,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z267,z6]),(0,[z63,z0,z1,z2,z4,z268,z6]),(0,[z0,z1,z2,z4,z269,z5,z6])],[(0,[z0,z1,z2,z4,z5,z270,z6]),(0,[z63,z271,z1,z2,z4,z5,z6]),(0,[z272,z0,z1,z2,z4,z5,z6]),(0,[z54,z107,z0,z1,z2,z4,z6])],[(1,[z273,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z6]),(0,[z0,z1,z2,z4,z5,z6,z16]),(0,[z0,z1,z2,z38,z4,z5,z18])],[(0,[z130,z0,z1,z2,z4,z5,z274]),(0,[z0,z1,z2,z4,z5,z6,z275])],[(0,[z276,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z277]),(1,[z0,z71,z2,z4,z278,z6]),(0,[z0,z1,z2,z4,z279,z5,z6])],[(0,[z280,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z281,z6]),(0,[z45,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z282,z4,z5,z6])],[(0,[z0,z1,z2,z225,z4,z5,z6]),(0,[z0,z1,z66,z4,z5,z6,z16]),(0,[z0,z1,z2,z283,z4,z5,z6])]],
   [[(0,[z284,z0,z1,z2,z4,z5,z6]),(0,[z124,z1,z131,z2,z4,z5,z6]),(0,[z27,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z32,z5,z28]),(0,[z285,z0,z1,z2,z4,z5,z6])],[(0,[z286,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z274]),(0,[z97,z0,z1,z2,z4,z5,z6]),(0,[z0,z287,z1,z2,z4,z5,z6]),(0,[z0,z109,z1,z156,z4,z5,z6]),(0,[z0,z1,z2,z148,z4,z5,z78])],[(0,[z130,z123,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z288]),(0,[z17,z188,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z289,z6]),(0,[z0,z1,z2,z290,z4,z5,z6]),(1,[z0,z1,z2,z4,z55,z18])],[(0,[z0,z1,z2,z4,z5,z6,z291]),(0,[z0,z109,z1,z2,z4,z5,z6]),(0,[z292,z0,z1,z2,z4,z5,z6])],[],[(0,[z51,z97,z0,z1,z2,z4,z5]),(0,[z0,z1,z293,z2,z4,z5,z6]),(0,[z0,z294,z1,z2,z4,z5,z6])],[(0,[z0,z124,z1,z2,z4,z5,z6]),(0,[z0,z1,z295,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z296,z6]),(0,[z0,z1,z2,z4,z8,z5,z174]),(0,[z0,z1,z2,z297,z4,z5,z6])],[(0,[z0,z1,z2,z4,z298,z5,z6]),(0,[z0,z109,z1,z2,z4,z62,z5]),(0,[z0,z1,z299,z2,z4,z5,z6])]],
   [[(0,[z17,z0,z1,z66,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z78,z28])],[(0,[z54,z0,z1,z37,z2,z4,z5])],[(0,[z0,z1,z2,z300,z4,z5,z6]),(0,[z301,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z302,z4,z5,z6]),(0,[z0,z303,z1,z2,z4,z5,z6])],[(0,[z304,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z305,z5,z6]),(0,[z0,z1,z2,z4,z306,z5,z6]),(0,[z0,z1,z2,z307,z4,z5,z6])],[(0,[z308,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z309,z4,z5,z6]),(0,[z0,z1,z310,z2,z4,z5,z6])],[(0,[z142,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z311])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z18])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z312]),(0,[z17,z0,z1,z313,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z314]),(0,[z0,z1,z315,z2,z4,z5,z6])],[(0,[z142,z1,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z278,z100,z6]),(1,[z0,z1,z2,z290,z4,z5]),(0,[z51,z0,z1,z37,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z104,z18]),(0,[z0,z1,z2,z4,z316,z5,z6]),(0,[z317,z0,z1,z2,z4,z5,z6]),(0,[z318,z0,z1,z2,z4,z5,z6])],[(0,[z0,z319,z1,z2,z4,z5,z6]),(0,[z320,z0,z1,z2,z4,z5,z6]),(0,[z321,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z322,z4,z5,z6]),(0,[z17,z54,z0,z1,z2,z4,z6]),(0,[z0,z323,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z324,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z78]),(0,[z0,z1,z2,z4,z325,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z326]),(0,[z327,z0,z1,z2,z4,z5,z6]),(0,[z188,z0,z1,z2,z4,z6,z18]),(0,[z328,z0,z1,z2,z4,z5,z6]),(0,[z0,z329,z1,z2,z4,z5,z6]),(0,[z0,z1,z330,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z331,z6]),(0,[z45,z0,z1,z2,z4,z5,z6])],[(0,[z332,z0,z1,z2,z4,z5,z6]),(1,[z0,z109,z156,z4,z5,z6]),(0,[z0,z1,z2,z4,z333,z5,z6]),(0,[z0,z334,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z335,z5,z6]),(1,[z0,z1,z2,z4,z5,z252]),(0,[z336,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z337,z5,z6]),(0,[z51,z0,z1,z2,z4,z5,z78]),(1,[z0,z1,z2,z4,z5,z338]),(0,[z0,z1,z2,z4,z5,z78,z18])]],
   [[(0,[z238,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z339,z6]),(0,[z340,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z341,z4,z5,z6]),(0,[z143,z0,z1,z2,z4,z342,z6]),(0,[z0,z31,z1,z2,z4,z5,z6]),(1,[z116,z0,z2,z4,z32,z5])],[(0,[z0,z1,z2,z64,z4,z5,z6]),(0,[z343,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z139,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z344]),(0,[z0,z1,z35,z2,z36,z5,z6])],[(0,[z0,z1,z133,z4,z46,z5,z6]),(0,[z0,z345,z1,z2,z4,z5,z6]),(0,[z0,z1,z346,z2,z4,z5,z6])],[(0,[z347,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z348,z5,z6])],[(0,[z0,z1,z349,z2,z4,z5,z6]),(0,[z350,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z268,z6]),(0,[z0,z1,z351,z2,z4,z5,z6])],[(0,[z17,z0,z1,z2,z4,z5,z6]),(0,[z97,z1,z2,z4,z8,z5,z6]),(1,[z271,z1,z2,z4,z5,z6]),(0,[z0,z71,z1,z2,z4,z342,z6]),(0,[z0,z1,z2,z352,z4,z5,z6]),(0,[z353,z0,z1,z2,z4,z5,z6]),(0,[z354,z107,z1,z2,z4,z5,z6])],[(0,[z355,z0,z1,z2,z4,z5,z6]),(0,[z116,z0,z1,z2,z4,z5,z104])],[(0,[z0,z356,z1,z2,z4,z5,z6]),(0,[z357,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z35,z2,z46,z5,z6]),(0,[z0,z1,z2,z4,z358,z5,z6]),(0,[z0,z1,z2,z359,z4,z5,z6])]],
   [[(0,[z360,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z361,z4,z5,z6]),(0,[z0,z1,z2,z4,z362,z5,z6])],[],[(0,[z0,z363,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z119,z6])],[(1,[z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z364,z6]),(0,[z365,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z366]),(0,[z0,z1,z2,z4,z19,z5,z78]),(0,[z0,z1,z2,z367,z4,z5,z6]),(0,[z1,z2,z4,z256,z5,z6,z16]),(0,[z368,z0,z1,z2,z4,z5,z6])],[(1,[z85,z1,z2,z86,z5,z6]),(0,[z0,z369,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z370,z4,z5,z6]),(0,[z0,z1,z2,z371,z4,z5,z6]),(0,[z0,z1,z66,z2,z4,z6,z16]),(0,[z372,z0,z1,z2,z4,z5,z6]),(0,[z373,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z374]),(1,[z0,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z375,z4,z5,z6]),(0,[z0,z1,z2,z4,z342,z100,z6]),(0,[z0,z1,z2,z376,z4,z5,z6]),(0,[z0,z1,z377,z2,z4,z5,z6])]],
   [[(0,[z0,z90,z1,z2,z4,z5,z6]),(0,[z0,z2,z64,z4,z34,z5,z6]),(0,[z0,z1,z2,z378,z4,z5,z6]),(0,[z379,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z380,z5]),(0,[z0,z381,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z382,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z383]),(0,[z54,z0,z1,z2,z4,z19,z5]),(0,[z384,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z385,z4,z5,z6]),(0,[z386,z0,z1,z2,z4,z5,z6])],[(0,[z85,z0,z1,z2,z86,z5,z6]),(0,[z0,z1,z2,z4,z8,z5,z6]),(0,[z387,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z83,z4,z5,z6]),(0,[z0,z1,z2,z84,z4,z5,z338]),(0,[z0,z1,z388,z2,z4,z5,z6])],[(0,[z1,z2,z145,z4,z86,z5,z6]),(0,[z0,z1,z2,z4,z389,z5,z6])],[(0,[z0,z1,z390,z2,z4,z5,z6]),(0,[z0,z2,z4,z32,z5,z6,z104]),(0,[z0,z1,z2,z106,z84,z4,z5]),(0,[z0,z1,z2,z84,z5,z100,z6])],[(1,[z115,z0,z133,z4,z5,z6]),(0,[z0,z1,z2,z4,z342,z5,z6]),(0,[z0,z1,z2,z4,z5,z104,z78])],[(0,[z391,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z392]),(0,[z0,z1,z2,z4,z393,z5,z6]),(0,[z116,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z394,z5,z6]),(0,[z395,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z396,z5,z6]),(0,[z45,z0,z1,z35,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z397,z6])],[(0,[z0,z1,z2,z398,z4,z5,z6]),(1,[z27,z1,z2,z4,z5,z28]),(0,[z65,z0,z1,z4,z67,z5,z6]),(0,[z0,z1,z2,z4,z399,z5,z6])],[(0,[z123,z124,z1,z2,z4,z5,z6]),(0,[z1,z15,z2,z4,z8,z5,z6]),(0,[z0,z1,z2,z4,z5,z400,z6])],[(0,[z0,z1,z2,z4,z86,z5,z6]),(0,[z97,z27,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z401,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z402]),(1,[z0,z1,z2,z4,z5,z105]),(0,[z0,z403,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z404,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z405,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z35,z156,z4,z5,z6]),(0,[z143,z0,z1,z2,z4,z278,z6]),(0,[z51,z0,z1,z2,z4,z32,z5])],[(0,[z0,z1,z2,z4,z5,z406,z6]),(0,[z17,z1,z15,z2,z4,z5,z6]),(0,[z0,z407,z1,z2,z4,z5,z6])],[(0,[z255,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z408,z5,z6]),(0,[z0,z1,z2,z4,z5,z409,z6]),(0,[z0,z1,z35,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z410,z5,z6])],[(0,[z7,z0,z1,z205,z4,z5,z6]),(0,[z0,z1,z2,z4,z411,z5,z6]),(0,[z0,z1,z2,z4,z55,z5,z6])]],
   [[(0,[z0,z1,z2,z412,z4,z5,z6]),(0,[z413,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z414,z5,z6]),(0,[z0,z1,z415,z2,z4,z5,z6]),(0,[z63,z0,z1,z310,z4,z5,z6]),(0,[z416,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z66,z2,z4,z5,z6])],[(0,[z0,z1,z417,z2,z4,z5,z6]),(0,[z418,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z419,z5,z6]),(0,[z0,z420,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z409]),(0,[z0,z71,z1,z2,z4,z278,z6])],[(0,[z0,z1,z2,z4,z421,z5,z6])],[(0,[z123,z0,z1,z2,z4,z5,z6]),(0,[z422,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z423,z5,z6]),(0,[z0,z1,z2,z4,z424,z5,z6]),(0,[z45,z0,z1,z2,z36,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z105]),(0,[z0,z1,z2,z4,z5,z6,z425])],[(0,[z426,z0,z1,z2,z4,z5,z6]),(0,[z17,z65,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z427,z4,z5,z6])],[(0,[z0,z1,z428,z2,z4,z5,z6]),(0,[z429,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z430,z5,z6])],[(0,[z0,z1,z2,z431,z4,z5,z6]),(0,[z0,z1,z2,z4,z432,z5,z6]),(0,[z115,z0,z1,z156,z4,z5,z6]),(0,[z0,z1,z2,z4,z433,z5,z6]),(0,[z434,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z435,z2,z4,z5,z6]),(0,[z0,z1,z313,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z436,z5,z6]),(0,[z0,z437,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z438,z5,z6]),(0,[z0,z1,z439,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z440,z4,z5,z6]),(0,[z115,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z441,z5,z6])],[(0,[z0,z1,z2,z4,z442,z5,z6]),(0,[z0,z443,z1,z2,z4,z5,z6])],[(0,[z65,z0,z1,z205,z4,z5,z6]),(0,[z0,z1,z444,z2,z4,z5,z6]),(0,[z445,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z446,z2,z4,z5,z6]),(1,[z97,z1,z2,z4,z19,z5]),(0,[z0,z1,z2,z4,z447,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z448]),(1,[z354,z1,z2,z4,z5,z6])],[(0,[z449,z0,z1,z2,z4,z5,z6]),(0,[z0,z450,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z451,z5,z6]),(0,[z0,z1,z2,z4,z452,z5,z6]),(0,[z0,z1,z2,z4,z46,z5,z6])],[(0,[z107,z0,z1,z2,z4,z5,z104]),(0,[z453,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z148,z4,z5,z6])],[(0,[z142,z0,z1,z2,z145,z5,z6]),(0,[z97,z107,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z454]),(0,[z0,z1,z2,z4,z455,z5,z6])],[(0,[z0,z1,z2,z4,z456,z5,z6]),(0,[z0,z1,z2,z4,z457,z5,z6]),(0,[z0,z1,z2,z4,z458,z5,z6]),(0,[z0,z1,z459,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z460,z6]),(0,[z149,z0,z1,z2,z4,z5,z78]),(0,[z0,z1,z461,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z462,z4,z5,z6]),(1,[z0,z90,z2,z64,z5,z6])],[(0,[z463,z0,z1,z2,z4,z5,z6]),(0,[z188,z0,z1,z2,z4,z6,z81]),(0,[z464,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z28]),(0,[z465,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z466]),(0,[z0,z1,z2,z4,z467,z5,z6]),(1,[z468,z1,z2,z4,z5,z6]),(0,[z469,z0,z1,z2,z4,z5,z6])],[(0,[z470,z0,z1,z2,z4,z5,z6]),(0,[z0,z31,z1,z2,z4,z5,z104]),(0,[z471,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z472]),(0,[z85,z0,z1,z2,z4,z5,z41]),(0,[z0,z1,z2,z4,z5,z6,z473]),(0,[z0,z1,z474,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z475,z6]),(0,[z0,z1,z2,z38,z4,z19,z5]),(0,[z0,z1,z2,z4,z476,z5,z6]),(0,[z477,z0,z1,z2,z4,z5,z6])],[(1,[z130,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z478,z5,z6]),(0,[z188,z0,z1,z2,z4,z8,z6]),(0,[z0,z1,z2,z4,z479,z5,z6]),(0,[z480,z0,z1,z2,z4,z5,z6]),(0,[z0,z180,z1,z2,z4,z5,z6])],[(0,[z481,z0,z1,z2,z4,z5,z6]),(0,[z482,z0,z1,z2,z4,z5,z6]),(0,[z482,z0,z1,z2,z4,z5,z16]),(0,[z0,z1,z2,z4,z5,z483,z6]),(0,[z0,z1,z2,z484,z4,z5,z6]),(0,[z485,z0,z1,z2,z4,z5,z6])],[(0,[z85,z0,z1,z2,z4,z5,z155]),(0,[z97,z0,z1,z2,z4,z5,z28]),(0,[z128,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z486,z4,z5,z6]),(0,[z487,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z488,z6]),(0,[z0,z1,z489,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z490,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z6,z491]),(1,[z0,z1,z2,z4,z5,z492])],[(0,[z27,z0,z1,z2,z4,z19,z5]),(0,[z0,z1,z2,z4,z268,z5,z6]),(0,[z0,z1,z493,z2,z4,z5,z6]),(0,[z494,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z495])],[(0,[z496,z0,z1,z2,z4,z5,z6]),(0,[z497,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z498,z6]),(1,[z0,z1,z2,z4,z5,z72]),(0,[z499,z0,z1,z2,z4,z5,z6])],[(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z188,z0,z1,z2,z4,z5,z122]),(0,[z51,z27,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z501,z5,z6]),(1,[z0,z1,z4,z139,z5,z6]),(0,[z0,z1,z2,z4,z256,z5,z6]),(0,[z0,z1,z2,z4,z502,z5,z6])],[(0,[z255,z0,z1,z2,z205,z4,z6]),(0,[z107,z0,z1,z2,z4,z55,z5])],[(0,[z0,z1,z2,z4,z503,z5,z6]),(0,[z0,z1,z2,z4,z504,z5,z6]),(0,[z0,z1,z2,z290,z36,z4,z5])],[(0,[z505,z0,z1,z2,z4,z5,z6]),(0,[z115,z45,z0,z1,z4,z5,z6]),(1,[z143,z0,z2,z4,z342,z6]),(0,[z0,z1,z2,z4,z506,z5,z6]),(0,[z0,z1,z66,z2,z4,z67,z6]),(0,[z107,z0,z1,z2,z4,z5,z6])],[(0,[z507,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z238,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z18])],[(1,[z7,z1,z205,z4,z5,z6]),(0,[z0,z508,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z88]),(0,[z0,z509,z1,z2,z4,z5,z6])],[(0,[z123,z0,z131,z2,z4,z5,z6]),(0,[z510,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z511,z4,z5,z6]),(0,[z512,z0,z1,z2,z4,z5,z6]),(0,[z0,z513,z1,z2,z4,z5,z6]),(0,[z0,z1,z37,z4,z5,z6,z185])],[(0,[z514,z0,z1,z2,z4,z5,z6]),(0,[z115,z0,z2,z133,z4,z5,z6]),(1,[z0,z1,z310,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z515]),(0,[z516,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z517]),(0,[z0,z1,z2,z518,z4,z5,z6]),(0,[z354,z0,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z205,z4,z5,z6]),(0,[z0,z1,z168,z2,z4,z5,z6]),(1,[z188,z1,z2,z4,z8,z6]),(1,[z0,z1,z2,z4,z5,z409]),(0,[z468,z1,z2,z4,z5,z6,z16])],[(0,[z0,z1,z2,z4,z519,z5,z6]),(0,[z17,z7,z1,z2,z4,z5,z6]),(0,[z0,z1,z520,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z521,z5,z6])],[(0,[z522,z0,z1,z2,z4,z5,z6]),(0,[z97,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z523,z6]),(0,[z0,z1,z2,z148,z5,z6,z78])],[(0,[z524,z0,z1,z2,z4,z5,z6]),(0,[z123,z1,z2,z4,z86,z5,z6]),(0,[z525,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z526,z6]),(0,[z0,z1,z2,z4,z527,z5,z6])]],
   [[(0,[z27,z0,z1,z2,z4,z5,z6]),(0,[z528,z0,z1,z2,z4,z5,z6]),(0,[z529,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z530,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z338])],[(0,[z0,z1,z2,z531,z4,z5,z6]),(0,[z0,z1,z2,z4,z532,z5,z6])],[(0,[z0,z1,z2,z533,z4,z5,z6]),(0,[z0,z1,z534,z2,z4,z5,z6])],[(0,[z142,z123,z1,z2,z4,z5,z6]),(0,[z535,z0,z1,z2,z4,z5,z6]),(0,[z273,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z536,z4,z5,z6]),(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z0,z1,z538,z2,z4,z5,z6]),(0,[z539,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z540,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z541]),(0,[z0,z1,z2,z4,z542,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z167]),(0,[z543,z0,z1,z2,z4,z5,z6]),(1,[z51,z0,z1,z4,z212,z5]),(0,[z0,z1,z2,z4,z544,z5,z6])],[(0,[z545,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z546,z0,z1,z2,z4,z5,z6]),(0,[z238,z0,z1,z15,z4,z5,z6]),(0,[z45,z0,z1,z4,z46,z5,z6])],[(0,[z130,z0,z1,z2,z4,z5,z6]),(0,[z0,z547,z1,z2,z4,z5,z6]),(0,[z548,z0,z1,z2,z4,z5,z6]),(0,[z0,z549,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z550,z5,z6]),(0,[z158,z0,z1,z2,z83,z5,z6]),(0,[z107,z0,z1,z2,z38,z4,z5])],[(0,[z0,z1,z2,z551,z4,z5,z6]),(0,[z0,z1,z11,z2,z4,z5,z6]),(0,[z0,z1,z552,z2,z4,z5,z6]),(0,[z553,z0,z1,z2,z4,z5,z6]),(0,[z554,z0,z1,z2,z4,z5,z6])],[(0,[z130,z1,z131,z2,z4,z5,z6]),(0,[z0,z1,z555,z2,z4,z5,z6]),(0,[z556,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z557])],[(0,[z558,z0,z1,z2,z4,z5,z6]),(0,[z559,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z32,z5,z78]),(0,[z0,z1,z4,z212,z5,z6,z185])],[(0,[z0,z1,z2,z560,z4,z5,z6]),(0,[z0,z1,z2,z561,z4,z5,z6]),(0,[z0,z562,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z19,z5,z6,z28]),(0,[z0,z1,z2,z4,z380,z5,z6]),(0,[z468,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z563,z5,z6])],[],[(0,[z188,z0,z1,z66,z2,z4,z6]),(0,[z564,z0,z1,z2,z4,z5,z6]),(0,[z63,z384,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z565,z6]),(0,[z149,z0,z1,z2,z38,z5,z6])],[(0,[z0,z1,z2,z566,z4,z5,z6]),(1,[z482,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z567,z5,z6])],[(0,[z0,z1,z2,z568,z4,z5,z6]),(0,[z0,z109,z156,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z278,z6]),(0,[z116,z0,z2,z4,z32,z5,z6]),(0,[z569,z0,z1,z2,z4,z5,z6])],[(0,[z570,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z571,z5,z6])],[(0,[z1,z2,z4,z8,z5,z6,z28]),(0,[z0,z1,z2,z83,z4,z342,z6]),(0,[z0,z1,z2,z36,z4,z5,z6]),(0,[z0,z1,z2,z4,z572,z5,z6])],[(0,[z0,z1,z2,z4,z62,z5,z6]),(0,[z0,z1,z2,z4,z573,z5,z6]),(0,[z0,z1,z2,z574,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z88,z16])]],
   [[(0,[z1,z131,z2,z4,z86,z5,z6]),(0,[z0,z2,z4,z342,z5,z278,z6]),(0,[z0,z1,z35,z36,z4,z5,z6]),(0,[z158,z0,z1,z2,z4,z100,z6])],[(0,[z0,z1,z2,z575,z4,z5,z6]),(0,[z576,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z577,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z578,z5,z6]),(0,[z0,z1,z579,z2,z4,z5,z6])],[(0,[z580,z0,z1,z2,z4,z5,z6]),(0,[z188,z0,z1,z2,z4,z430,z5]),(0,[z176,z0,z1,z2,z4,z19,z6]),(0,[z63,z0,z1,z361,z4,z5,z6])],[(0,[z581,z0,z1,z2,z4,z5,z6]),(0,[z0,z271,z1,z2,z4,z5,z6])],[(1,[z0,z1,z225,z4,z5,z6]),(0,[z0,z90,z1,z2,z34,z5,z6]),(0,[z54,z0,z1,z2,z4,z5,z6])],[(0,[z0,z582,z1,z2,z4,z5,z6]),(0,[z583,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z584]),(1,[z0,z1,z2,z4,z5,z122]),(0,[z0,z1,z585,z2,z4,z5,z6]),(0,[z0,z1,z586,z2,z4,z5,z6]),(0,[z587,z0,z1,z2,z4,z5,z6])],[(0,[z588,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z589,z5,z6]),(0,[z0,z1,z2,z4,z590,z5,z6]),(0,[z0,z1,z2,z4,z591,z5,z6]),(0,[z592,z0,z1,z2,z4,z5,z6])],[(0,[z0,z593,z1,z2,z4,z5,z6]),(0,[z0,z594,z1,z2,z4,z5,z6]),(0,[z595,z0,z1,z2,z4,z5,z6]),(0,[z158,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z238,z0,z1,z205,z4,z5,z6]),(0,[z0,z1,z205,z4,z5,z6,z16]),(0,[z42,z0,z1,z2,z4,z8,z5])],[(0,[z596,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z597,z4,z5,z6])],[(0,[z0,z1,z2,z4,z598,z5,z6]),(0,[z599,z0,z1,z2,z4,z5,z6])],[(0,[z600,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z601,z4,z5,z6])],[(0,[z602,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z603,z2,z4,z5,z6]),(0,[z0,z1,z168,z2,z205,z4,z5]),(0,[z0,z1,z2,z604,z4,z5,z6]),(0,[z0,z1,z605,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z606]),(0,[z607,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z55,z5,z28]),(0,[z608,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z609,z5,z6]),(0,[z610,z0,z1,z2,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z6,z16])],[(0,[z611,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z612,z5,z6])],[(0,[z188,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z613,z2,z4,z5,z6]),(0,[z0,z1,z614,z2,z4,z5,z6]),(0,[z615,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z616,z0,z1,z2,z4,z5,z6]),(0,[z0,z109,z1,z36,z4,z5,z6]),(0,[z617,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z212,z5,z6]),(0,[z0,z1,z618,z2,z4,z5,z6])],[(0,[z0,z1,z11,z2,z205,z4,z6]),(0,[z0,z1,z2,z619,z4,z5,z6]),(0,[z0,z1,z620,z2,z4,z5,z6]),(0,[z621,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z622,z5,z6])],[(0,[z0,z1,z2,z623,z4,z5,z6]),(0,[z0,z1,z35,z133,z4,z5,z6]),(0,[z0,z1,z2,z624,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z104])],[(0,[z625,z0,z1,z2,z4,z5,z6]),(0,[z149,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z274,z6]),(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z273,z0,z1,z2,z205,z4,z5]),(1,[z0,z1,z2,z4,z5,z174]),(0,[z626,z0,z1,z2,z4,z5,z6]),(0,[z627,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z628,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z629,z6]),(0,[z0,z1,z2,z630,z4,z5,z6]),(0,[z63,z0,z2,z4,z34,z5,z6]),(0,[z0,z71,z1,z2,z4,z380,z5]),(0,[z51,z0,z1,z2,z4,z5,z104]),(0,[z0,z1,z2,z38,z4,z5,z104]),(0,[z631,z0,z1,z2,z4,z5,z6]),(1,[z54,z107,z0,z1,z2,z4])],[(0,[z0,z1,z2,z4,z632,z5,z6]),(0,[z0,z1,z2,z4,z633,z5,z6]),(0,[z97,z0,z1,z37,z2,z4,z5]),(0,[z63,z0,z1,z2,z4,z5,z6]),(0,[z143,z0,z2,z4,z342,z5,z6]),(0,[z0,z634,z1,z2,z4,z5,z6]),(0,[z149,z0,z1,z2,z148,z5,z6])],[(0,[z0,z1,z635,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z636,z5,z6]),(0,[z0,z1,z2,z637,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z638,z4,z5,z6]),(0,[z0,z1,z639,z2,z4,z5,z6])],[(0,[z640,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z641,z5,z6]),(0,[z0,z642,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z643,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z644]),(0,[z0,z90,z1,z2,z64,z5,z6]),(0,[z0,z1,z2,z83,z4,z278,z6]),(0,[z645,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z646,z4,z5,z6]),(0,[z647,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z648,z2,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z185]),(0,[z649,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z83,z5,z100,z6]),(0,[z0,z1,z650,z2,z4,z5,z6])],[(1,[z123,z124,z2,z4,z5,z6]),(1,[z238,z1,z15,z4,z5,z6]),(0,[z0,z651,z1,z2,z4,z5,z6]),(0,[z652,z0,z1,z2,z4,z5,z6]),(0,[z653,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z55,z5,z18]),(0,[z0,z654,z1,z2,z4,z5,z6])],[(0,[z655,z0,z1,z2,z4,z5,z6]),(0,[z656,z0,z1,z2,z4,z5,z6]),(1,[z384,z1,z2,z4,z5,z6]),(0,[z0,z31,z2,z4,z5,z6,z104]),(0,[z0,z1,z657,z2,z4,z5,z6]),(0,[z0,z1,z2,z106,z4,z5,z6])],[(0,[z85,z0,z1,z2,z4,z5,z6]),(0,[z0,z71,z2,z4,z5,z278,z6]),(0,[z51,z0,z1,z2,z4,z5,z185]),(0,[z0,z1,z658,z2,z4,z5,z6])],[(0,[z0,z659,z1,z2,z4,z5,z6]),(0,[z660,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z661,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z662,z5,z6]),(0,[z0,z663,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z664,z5,z6]),(0,[z0,z1,z665,z2,z4,z5,z6])],[(1,[z176,z0,z1,z2,z4,z6]),(0,[z0,z666,z1,z2,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z55,z5]),(0,[z667,z0,z1,z2,z4,z5,z6])],[(0,[z0,z668,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z669,z4,z5,z6]),(0,[z17,z1,z2,z4,z5,z6,z28]),(0,[z0,z1,z2,z4,z19,z5,z104]),(0,[z0,z109,z1,z133,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z492])],[(0,[z0,z1,z2,z4,z670,z5,z6]),(0,[z0,z1,z2,z4,z671,z5,z6]),(0,[z0,z1,z2,z4,z672,z5,z6]),(0,[z0,z1,z2,z673,z4,z5,z6]),(0,[z0,z1,z37,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z674,z5,z6])],[(0,[z0,z1,z2,z4,z675,z5,z6]),(0,[z0,z1,z2,z676,z4,z5,z6]),(0,[z677,z0,z1,z2,z4,z5,z6]),(0,[z51,z0,z1,z2,z4,z55,z5]),(0,[z0,z1,z2,z678,z4,z5,z6])],[(0,[z97,z1,z2,z4,z19,z5,z6]),(1,[z0,z1,z361,z4,z5,z6])],[(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z679,z4,z5,z6]),(0,[z51,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z4,z5,z6]),(0,[z680,z0,z1,z2,z4,z5,z6])],[(0,[z63,z0,z1,z2,z34,z5,z6]),(0,[z51,z54,z0,z1,z2,z4,z5]),(0,[z149,z0,z1,z2,z38,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z681,z5,z6]),(0,[z0,z1,z2,z4,z19,z289,z6]),(0,[z0,z1,z2,z682,z4,z5,z6])],[(0,[z0,z1,z2,z4,z683,z5,z6]),(0,[z684,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z685,z4,z5,z6])],[(0,[z686,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z687]),(0,[z688,z0,z1,z2,z4,z5,z6]),(0,[z0,z109,z1,z2,z4,z5,z492]),(0,[z0,z1,z2,z689,z4,z5,z6]),(0,[z0,z1,z2,z690,z4,z5,z6])],[(0,[z142,z0,z1,z2,z86,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z691]),(0,[z188,z1,z2,z4,z8,z5,z6]),(0,[z0,z1,z2,z4,z692,z5,z6]),(0,[z0,z1,z2,z4,z32,z19,z5]),(0,[z0,z1,z2,z4,z5,z6,z693]),(0,[z63,z0,z1,z2,z4,z119,z6]),(0,[z0,z1,z2,z694,z4,z5,z6]),(0,[z0,z695,z1,z2,z4,z5,z6])],[(1,[z0,z1,z313,z4,z5,z6]),(1,[z17,z1,z2,z4,z6,z81]),(1,[z0,z1,z2,z4,z430,z5]),(1,[z42,z0,z1,z2,z4,z5]),(0,[z696,z0,z1,z2,z4,z5,z6]),(0,[z697,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z252]),(0,[z698,z0,z1,z2,z4,z5,z6]),(0,[z699,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z700,z2,z4,z5,z6]),(0,[z27,z107,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z701,z5,z6])],[(1,[z0,z1,z2,z4,z289,z6]),(0,[z0,z1,z2,z4,z702,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z703]),(0,[z704,z0,z1,z2,z4,z5,z6])],[(0,[z705,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z706,z5,z6]),(0,[z158,z0,z1,z2,z84,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z4,z5,z274]),(0,[z384,z1,z361,z4,z5,z6]),(0,[z0,z71,z2,z4,z380,z278]),(0,[z0,z1,z37,z4,z5,z204])],[(0,[z0,z1,z707,z4,z5,z6]),(0,[z0,z1,z708,z2,z4,z5]),(0,[z0,z1,z2,z4,z268,z252]),(0,[z0,z2,z709,z34,z5,z6]),(0,[z710,z1,z2,z4,z5,z6]),(0,[z711,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z55,z18])],[(0,[z0,z1,z2,z4,z5,z712]),(0,[z0,z1,z2,z4,z713,z5]),(0,[z271,z1,z2,z4,z5,z252]),(0,[z0,z1,z2,z4,z119,z6]),(0,[z0,z1,z361,z4,z5,z252]),(0,[z0,z1,z310,z4,z268,z6]),(0,[z0,z1,z2,z714,z148,z5]),(0,[z180,z1,z2,z38,z4,z5])],[(0,[z0,z1,z715,z4,z5,z6]),(0,[z0,z716,z1,z2,z4,z5]),(0,[z660,z0,z2,z4,z32,z5]),(0,[z0,z1,z2,z4,z55,z289]),(0,[z271,z1,z310,z4,z5,z6]),(0,[z0,z1,z2,z4,z268,z409]),(1,[z0,z1,z717,z5,z6]),(1,[z0,z1,z2,z718,z6]),(0,[z0,z1,z2,z4,z719,z5])]],
   [[(0,[z0,z1,z2,z4,z720,z6]),(0,[z0,z1,z721,z4,z5,z6]),(0,[z271,z1,z2,z4,z5,z409]),(0,[z0,z1,z361,z4,z5,z409]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z723,z1,z2,z4,z5,z6])],[(0,[z0,z2,z4,z724,z5,z6]),(0,[z0,z1,z4,z212,z725,z5])],[(1,[z1,z726,z4,z5,z6]),(0,[z0,z1,z2,z4,z727,z6]),(0,[z97,z180,z1,z2,z4,z5]),(1,[z0,z728,z4,z5,z6]),(0,[z0,z2,z728,z4,z5,z6]),(0,[z63,z384,z2,z34,z5,z6]),(0,[z729,z0,z1,z2,z4,z6]),(0,[z730,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z731]),(0,[z0,z1,z2,z732,z4,z6]),(0,[z0,z1,z361,z4,z268,z6]),(1,[z0,z1,z2,z714,z5])]],
   [[(0,[z0,z1,z11,z168,z2,z4]),(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z728,z133,z4,z5,z6])],[(0,[z0,z1,z734,z4,z5,z6]),(0,[z1,z2,z4,z735,z6,z81])],[(0,[z1,z726,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z736,z5]),(0,[z0,z1,z2,z4,z5,z737]),(0,[z0,z1,z36,z408,z5,z6]),(0,[z0,z1,z2,z4,z738,z6]),(0,[z739,z0,z1,z2,z4,z5]),(0,[z149,z0,z1,z2,z38,z5]),(0,[z54,z0,z740,z1,z2,z4])],[(0,[z741,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z742]),(0,[z354,z54,z107,z1,z2,z4])]],
   [[(0,[z743,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z744,z6]),(0,[z0,z1,z2,z4,z5,z492]),(0,[z745,z1,z2,z4,z5,z6]),(0,[z0,z369,z2,z4,z5,z104]),(0,[z0,z1,z2,z4,z5,z746])],[(0,[z0,z1,z2,z4,z5,z747]),(0,[z0,z1,z2,z4,z748,z6]),(0,[z0,z1,z2,z749,z4,z5]),(0,[z0,z240,z2,z4,z5,z104]),(0,[z354,z1,z2,z4,z6,z18])],[(0,[z750,z0,z1,z2,z4,z5]),(0,[z0,z751,z2,z4,z5,z6]),(0,[z0,z1,z2,z752,z5,z6]),(0,[z0,z1,z2,z84,z100,z6])],[(0,[z0,z1,z753,z4,z5,z6]),(0,[z123,z363,z2,z4,z5,z6]),(0,[z0,z1,z2,z754,z4,z5]),(0,[z755,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z756]),(0,[z757,z0,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z758,z4,z5,z6]),(0,[z0,z1,z2,z290,z4,z5]),(0,[z0,z1,z2,z4,z5,z759])],[(0,[z0,z1,z2,z4,z5,z760]),(0,[z680,z1,z2,z4,z5,z28]),(0,[z761,z1,z2,z4,z5,z6]),(0,[z762,z1,z2,z4,z5,z6]),(0,[z0,z31,z2,z4,z763,z5])],[(0,[z0,z1,z764,z2,z4,z5]),(0,[z1,z2,z4,z5,z765,z28]),(0,[z51,z0,z1,z297,z4,z5]),(0,[z766,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z767,z6]),(0,[z143,z0,z2,z4,z342,z6]),(0,[z0,z1,z2,z4,z5,z768]),(0,[z0,z1,z2,z4,z769,z6]),(0,[z0,z1,z2,z4,z674,z18]),(0,[z0,z740,z1,z2,z4,z5])],[(0,[z123,z124,z2,z4,z5,z6]),(0,[z238,z1,z15,z4,z5,z6]),(0,[z93,z1,z15,z4,z5,z6]),(0,[z468,z1,z225,z4,z5,z6]),(0,[z770,z0,z1,z225,z4,z5]),(0,[z97,z42,z1,z2,z4,z5]),(0,[z178,z1,z2,z4,z5,z28]),(0,[z365,z0,z2,z4,z342,z6]),(0,[z0,z771,z2,z4,z5,z6])]],
   [[(0,[z384,z1,z2,z4,z5,z6]),(0,[z0,z1,z772,z4,z5,z6]),(0,[z17,z1,z2,z682,z4,z6]),(0,[z1,z2,z4,z8,z735,z6]),(0,[z0,z1,z2,z4,z289,z104]),(0,[z773,z1,z2,z4,z5,z6]),(0,[z0,z2,z64,z709,z5,z6])],[(0,[z0,z1,z774,z4,z5,z6]),(0,[z0,z1,z2,z4,z775,z5]),(0,[z97,z1,z2,z4,z5,z70]),(0,[z0,z109,z156,z4,z5,z6]),(0,[z1,z2,z4,z776,z5,z6]),(0,[z68,z0,z1,z2,z4,z18])],[(0,[z124,z743,z2,z4,z5,z6]),(0,[z85,z1,z2,z86,z5,z41]),(0,[z17,z1,z313,z4,z6,z81]),(1,[z1,z2,z4,z735,z6]),(0,[z97,z1,z2,z4,z399,z5]),(0,[z0,z1,z2,z4,z5,z252]),(0,[z0,z777,z2,z4,z5,z6]),(0,[z0,z1,z2,z718,z4,z6])],[(0,[z27,z180,z1,z2,z4,z5]),(0,[z97,z1,z2,z4,z19,z289]),(0,[z0,z1,z310,z4,z5,z6])]],
   [[(0,[z0,z1,z11,z225,z4,z6]),(0,[z0,z1,z2,z4,z5,z778]),(0,[z468,z1,z15,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z779]),(0,[z176,z1,z2,z4,z6,z28]),(0,[z0,z1,z2,z4,z96,z18]),(0,[z0,z1,z2,z4,z5,z409]),(0,[z780,z1,z2,z4,z5,z6])],[(0,[z85,z1,z2,z781,z5,z6]),(0,[z188,z42,z1,z2,z4,z8]),(0,[z652,z1,z2,z4,z8,z6]),(0,[z0,z1,z2,z38,z4,z289]),(0,[z0,z109,z156,z4,z62,z5]),(0,[z0,z1,z782,z4,z5,z6]),(0,[z0,z2,z4,z709,z5,z6]),(1,[z0,z1,z4,z769,z6])],[(0,[z0,z1,z2,z4,z5,z783]),(0,[z85,z1,z2,z86,z5,z155]),(0,[z0,z1,z784,z4,z5,z6]),(0,[z65,z0,z1,z4,z67,z6]),(0,[z785,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z786]),(0,[z17,z1,z2,z4,z460,z6]),(0,[z0,z1,z2,z619,z5,z78]),(0,[z610,z0,z133,z4,z5,z6]),(0,[z699,z0,z2,z4,z32,z5]),(0,[z54,z107,z180,z1,z2,z4])]],
   [[(0,[z130,z131,z2,z4,z5,z274]),(0,[z0,z1,z2,z4,z787,z6]),(0,[z0,z1,z788,z4,z139,z5]),(0,[z1,z2,z4,z789,z5,z6]),(0,[z1,z2,z4,z256,z5,z88])],[(0,[z0,z1,z790,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z791]),(0,[z512,z0,z1,z46,z5,z6]),(0,[z0,z71,z2,z4,z278,z72]),(0,[z0,z509,z2,z4,z5,z104]),(0,[z0,z1,z37,z4,z706,z5]),(0,[z0,z1,z2,z792,z4,z5]),(0,[z793,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z718,z84,z6])],[(0,[z0,z1,z2,z4,z289,z78]),(0,[z0,z1,z2,z794,z4,z5])],[(0,[z63,z128,z0,z34,z5,z6]),(0,[z0,z795,z2,z4,z5,z6]),(0,[z796,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z797]),(0,[z0,z1,z2,z4,z798,z6]),(0,[z0,z1,z2,z799,z4,z5]),(0,[z51,z0,z1,z4,z506,z5]),(0,[z1,z2,z4,z800,z5,z6]),(0,[z54,z180,z1,z2,z4,z5])],[(0,[z7,z1,z168,z205,z4,z5]),(0,[z0,z1,z2,z4,z801,z6]),(0,[z802,z1,z2,z4,z5,z6]),(0,[z65,z0,z1,z4,z769,z6])],[(0,[z0,z1,z2,z4,z803,z6]),(0,[z0,z1,z2,z4,z5,z41]),(0,[z51,z0,z1,z4,z212,z5])],[(0,[z0,z1,z2,z4,z5,z804]),(0,[z805,z0,z1,z2,z5,z6]),(0,[z0,z1,z2,z4,z5,z806]),(0,[z42,z0,z1,z2,z4,z5]),(0,[z27,z1,z2,z302,z4,z5]),(0,[z0,z1,z4,z717,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z807,z5]),(0,[z0,z1,z2,z4,z5,z808])],[(0,[z0,z1,z2,z4,z809,z5]),(0,[z0,z1,z2,z810,z5,z6]),(0,[z0,z1,z2,z811,z4,z5])],[(0,[z0,z1,z2,z4,z812,z6]),(0,[z7,z1,z11,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z155]),(0,[z0,z813,z2,z4,z5,z6]),(0,[z814,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z815,z5]),(0,[z0,z1,z2,z816,z5,z6]),(0,[z0,z1,z2,z4,z5,z817]),(0,[z1,z2,z4,z818,z5,z6]),(0,[z54,z0,z1,z2,z4,z195]),(0,[z107,z0,z1,z2,z4,z259])],[(0,[z0,z1,z2,z4,z819,z6]),(0,[z820,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z821]),(0,[z0,z1,z822,z4,z5,z6]),(0,[z188,z1,z2,z4,z8,z122]),(0,[z1,z2,z4,z414,z5,z28])]],
   [[(0,[z0,z1,z2,z4,z5,z823]),(0,[z0,z1,z824,z4,z5,z6]),(0,[z7,z1,z726,z4,z5,z6]),(0,[z0,z1,z2,z4,z380,z5]),(0,[z0,z740,z1,z2,z4,z18])],[(0,[z0,z1,z2,z4,z825,z6]),(0,[z97,z0,z1,z2,z4,z289]),(0,[z384,z1,z2,z4,z119,z6]),(0,[z0,z1,z2,z38,z262,z5]),(0,[z0,z1,z2,z4,z55,z448]),(0,[z826,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z718,z100,z6])],[(0,[z0,z1,z2,z827,z4,z5]),(0,[z0,z1,z2,z4,z5,z828]),(0,[z829,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z830,z5]),(1,[z0,z740,z1,z2,z4])],[(0,[z0,z1,z2,z4,z5,z831]),(0,[z65,z0,z1,z160,z4,z6]),(0,[z0,z1,z2,z4,z119,z252]),(0,[z63,z0,z2,z34,z5,z252]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z0,z1,z2,z486,z100,z6]),(0,[z354,z54,z1,z2,z4,z6])]],
   [[(0,[z832,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z833,z6]),(0,[z834,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z835]),(0,[z0,z1,z310,z4,z119,z6]),(0,[z0,z1,z2,z4,z5,z836]),(0,[z0,z1,z837,z2,z4,z5]),(0,[z0,z1,z4,z67,z769,z6])],[(0,[z0,z1,z2,z838,z5,z6]),(0,[z0,z1,z2,z4,z839,z6]),(0,[z0,z1,z2,z4,z5,z840]),(0,[z1,z2,z4,z841,z5,z6]),(0,[z0,z1,z2,z4,z119,z409])],[(0,[z0,z1,z2,z4,z842,z6]),(0,[z0,z843,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z844,z6]),(0,[z548,z1,z2,z4,z19,z5]),(0,[z0,z1,z845,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z846]),(0,[z188,z257,z1,z2,z4,z6]),(1,[z0,z2,z709,z5,z6]),(0,[z482,z0,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z847,z5,z6]),(0,[z468,z1,z205,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z848]),(0,[z0,z156,z728,z4,z5,z6]),(0,[z63,z0,z2,z34,z268,z6]),(0,[z0,z1,z4,z139,z5,z849]),(0,[z0,z1,z35,z36,z5,z105]),(0,[z850,z1,z2,z4,z5,z6]),(0,[z482,z1,z2,z4,z256,z5]),(0,[z0,z1,z2,z718,z5,z6])],[(0,[z0,z1,z361,z4,z119,z6]),(0,[z63,z0,z361,z34,z5,z6]),(0,[z851,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z725,z5])],[(0,[z17,z65,z1,z15,z4,z6]),(0,[z0,z1,z2,z4,z5,z105])],[(0,[z1,z2,z781,z86,z5,z6]),(0,[z0,z1,z2,z4,z5,z852]),(0,[z468,z1,z66,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z853]),(0,[z0,z854,z2,z4,z5,z6]),(0,[z17,z87,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z855,z6]),(0,[z0,z109,z156,z4,z5,z492]),(0,[z856,z1,z2,z4,z5,z6])],[(0,[z0,z740,z1,z2,z4,z55])],[(0,[z188,z1,z2,z4,z8,z174]),(0,[z0,z1,z857,z4,z5,z6]),(0,[z0,z1,z2,z4,z219,z18]),(0,[z0,z1,z2,z38,z540,z5])],[(0,[z130,z131,z2,z4,z5,z167]),(0,[z0,z1,z2,z4,z858,z6]),(0,[z0,z654,z2,z4,z32,z5]),(0,[z0,z1,z2,z4,z5,z859])]],
   [[(0,[z583,z131,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z860,z6]),(0,[z0,z1,z66,z4,z88,z16]),(1,[z0,z1,z4,z725,z5])],[(0,[z0,z1,z2,z4,z5,z122]),(0,[z0,z1,z861,z4,z5,z6]),(0,[z107,z0,z1,z2,z4,z414]),(0,[z0,z1,z2,z4,z862,z5]),(0,[z0,z1,z2,z717,z5,z6])],[(0,[z0,z1,z2,z781,z5,z6]),(0,[z27,z0,z1,z2,z4,z289]),(0,[z863,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z864]),(0,[z65,z468,z1,z2,z4,z6])],[(0,[z865,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z866]),(0,[z0,z1,z2,z4,z5,z867]),(0,[z0,z1,z2,z4,z868,z6])]],
   [[(0,[z0,z513,z156,z4,z5,z6]),(0,[z0,z1,z4,z769,z6,z16])],[(0,[z1,z15,z726,z4,z5,z6]),(0,[z1,z2,z4,z8,z281,z6]),(0,[z0,z1,z869,z225,z4,z5]),(0,[z384,z1,z2,z4,z5,z252]),(0,[z870,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z871,z5]),(0,[z0,z1,z2,z83,z718,z6])],[(0,[z0,z1,z872,z4,z5,z6]),(0,[z65,z0,z1,z225,z4,z6]),(0,[z384,z1,z310,z4,z5,z6]),(0,[z0,z1,z36,z717,z5,z6])],[(0,[z0,z1,z2,z4,z873,z6]),(0,[z45,z0,z1,z335,z5,z6]),(0,[z0,z1,z728,z4,z5,z6]),(0,[z384,z1,z2,z4,z5,z409]),(0,[z0,z1,z874,z4,z5,z6]),(0,[z0,z2,z4,z32,z763,z5])]],
   [[(0,[z255,z7,z1,z205,z4,z6]),(0,[z0,z1,z310,z4,z5,z252]),(0,[z0,z1,z2,z4,z875,z6]),(0,[z0,z1,z2,z106,z4,z5])],[(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z1,z877,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z878]),(0,[z0,z1,z2,z4,z5,z879]),(0,[z880,z0,z1,z4,z5,z6]),(1,[z0,z2,z4,z763,z5]),(0,[z180,z1,z2,z4,z32,z5]),(0,[z881,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z714,z4,z5])],[(0,[z241,z1,z2,z4,z5,z28]),(0,[z354,z1,z2,z4,z5,z6]),(0,[z0,z1,z310,z4,z5,z409]),(0,[z0,z1,z882,z4,z5,z6]),(0,[z883,z1,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z289]),(0,[z0,z1,z788,z2,z4,z5])]],
   [[(0,[z0,z1,z11,z4,z6,z16]),(0,[z0,z1,z884,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z765]),(0,[z1,z2,z4,z5,z765,z6]),(0,[z0,z1,z2,z4,z5,z885]),(0,[z271,z1,z2,z4,z268,z6]),(0,[z886,z1,z2,z4,z5,z6]),(0,[z887,z0,z1,z2,z4,z6]),(0,[z888,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z4,z5,z889]),(0,[z890,z0,z1,z2,z4,z6]),(0,[z271,z1,z361,z4,z5,z6]),(0,[z63,z0,z2,z34,z5,z6]),(0,[z0,z334,z2,z4,z278,z6]),(0,[z891,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z892]),(0,[z273,z7,z1,z205,z4,z5]),(0,[z0,z1,z2,z4,z5,z893]),(0,[z0,z1,z2,z4,z5,z894]),(0,[z0,z1,z2,z4,z5,z895]),(0,[z0,z1,z2,z106,z84,z100])],[(0,[z0,z1,z2,z4,z5,z896]),(0,[z0,z1,z897,z2,z4,z6]),(0,[z898,z1,z2,z4,z5,z6]),(0,[z0,z90,z2,z64,z5,z6]),(0,[z0,z1,z899,z4,z5,z6]),(0,[z0,z71,z2,z4,z900,z6]),(0,[z0,z1,z2,z4,z5,z901]),(0,[z51,z0,z1,z4,z421,z5])]],
   [[(0,[z902,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z903]),(0,[z468,z1,z2,z4,z5,z6]),(0,[z904,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z174]),(0,[z0,z1,z2,z905,z5,z6]),(0,[z0,z1,z2,z4,z906,z5]),(0,[z107,z0,z1,z585,z2,z4])],[(0,[z0,z1,z2,z4,z5,z907]),(0,[z0,z1,z2,z4,z5,z908]),(0,[z1,z2,z4,z781,z5,z6]),(0,[z0,z1,z2,z4,z5,z909]),(0,[z0,z1,z717,z46,z5,z6]),(0,[z51,z0,z1,z282,z4,z5]),(0,[z149,z0,z1,z2,z714,z5]),(0,[z54,z107,z0,z1,z2,z4])],[(0,[z0,z1,z2,z4,z5,z910]),(0,[z241,z0,z1,z2,z4,z18]),(0,[z0,z1,z2,z4,z911,z6]),(0,[z0,z1,z2,z714,z5,z78])],[(0,[z912,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z849]),(0,[z116,z0,z2,z4,z763,z5]),(0,[z0,z740,z1,z2,z4,z6])]],
   [[(0,[z130,z131,z2,z4,z5,z6]),(0,[z913,z0,z1,z2,z4,z5])],[(0,[z10,z1,z2,z86,z5,z6]),(0,[z0,z1,z66,z225,z4,z6]),(0,[z0,z1,z2,z914,z5,z6]),(0,[z0,z1,z2,z4,z5,z915]),(0,[z0,z1,z2,z95,z5,z78])],[(0,[z1,z2,z145,z781,z5,z6]),(0,[z0,z1,z869,z2,z4,z5]),(0,[z916,z1,z2,z4,z5,z6]),(0,[z0,z1,z4,z769,z5,z6]),(0,[z917,z1,z2,z4,z5,z6]),(0,[z107,z0,z740,z1,z2,z4])],[(0,[z0,z1,z2,z918,z4,z6]),(0,[z0,z1,z2,z4,z5,z919]),(0,[z920,z1,z2,z4,z5,z6]),(0,[z45,z0,z1,z717,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z921]),(0,[z1,z15,z225,z4,z5,z6]),(0,[z188,z1,z2,z4,z399,z6])],[(0,[z0,z1,z2,z4,z922,z6]),(0,[z0,z1,z2,z923,z4,z5]),(0,[z0,z1,z924,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z72]),(0,[z285,z0,z1,z2,z38,z5]),(0,[z0,z1,z2,z714,z5,z6])],[(0,[z0,z1,z4,z139,z5,z6])],[(0,[z0,z1,z2,z4,z925,z6]),(0,[z0,z1,z2,z4,z926,z6]),(0,[z0,z1,z168,z2,z4,z5]),(0,[z0,z1,z2,z927,z4,z6]),(0,[z255,z0,z1,z168,z2,z4]),(0,[z0,z1,z2,z4,z5,z928]),(0,[z17,z303,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z929]),(0,[z0,z1,z2,z4,z5,z930]),(0,[z0,z1,z931,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z338])]],
   [[(0,[z65,z0,z1,z4,z589,z6]),(0,[z116,z0,z2,z4,z32,z5]),(0,[z932,z1,z2,z4,z5,z6]),(0,[z0,z1,z35,z717,z5,z6]),(0,[z468,z1,z66,z4,z6,z16]),(0,[z933,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z934]),(0,[z0,z1,z2,z4,z935,z5]),(0,[z176,z0,z1,z2,z4,z6]),(0,[z17,z54,z1,z2,z4,z28]),(0,[z17,z97,z1,z2,z4,z18]),(0,[z1,z2,z4,z8,z5,z122]),(0,[z42,z180,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z936])],[(0,[z0,z1,z2,z937,z4,z5])],[(0,[z0,z1,z2,z4,z938,z6]),(0,[z0,z1,z2,z939,z5,z6]),(0,[z0,z1,z940,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z941]),(0,[z942,z1,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z167]),(0,[z0,z1,z4,z943,z5,z6]),(0,[z7,z1,z205,z4,z5,z6]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z945]),(1,[z1,z2,z781,z5,z6]),(0,[z0,z1,z4,z946,z5,z6]),(0,[z0,z1,z2,z4,z32,z289]),(0,[z0,z1,z2,z4,z5,z947]),(0,[z0,z1,z2,z4,z268,z6]),(0,[z0,z90,z2,z709,z5,z6]),(0,[z0,z1,z2,z4,z5,z88]),(0,[z0,z1,z37,z4,z5,z185]),(0,[z0,z1,z2,z352,z5,z78])],[(0,[z130,z743,z2,z4,z5,z6]),(0,[z271,z1,z2,z4,z5,z6]),(0,[z97,z176,z1,z2,z4,z6]),(0,[z128,z0,z1,z4,z5,z6]),(0,[z948,z1,z2,z4,z5,z6]),(0,[z0,z1,z361,z4,z5,z6]),(0,[z63,z271,z2,z34,z5,z6])],[(0,[z0,z1,z2,z4,z949,z6]),(0,[z63,z0,z2,z34,z119,z6])],[(0,[z0,z1,z2,z950,z5,z6]),(0,[z0,z1,z2,z4,z951,z6]),(0,[z188,z1,z2,z4,z8,z6]),(0,[z1,z2,z4,z952,z5,z6]),(0,[z0,z1,z2,z4,z953,z6]),(0,[z51,z0,z1,z4,z725,z5])]],
   [[(0,[z0,z743,z2,z4,z5,z6]),(0,[z142,z1,z2,z145,z5,z6]),(0,[z0,z1,z2,z4,z954,z5]),(0,[z0,z1,z2,z4,z955,z6]),(0,[z158,z0,z1,z2,z718,z6])],[(0,[z0,z1,z2,z956,z5,z6]),(0,[z188,z1,z2,z4,z8,z430]),(0,[z188,z1,z2,z4,z735,z6]),(0,[z180,z1,z2,z4,z5,z104]),(0,[z482,z468,z1,z2,z4,z5])],[(0,[z0,z319,z2,z4,z5,z104]),(0,[z482,z0,z1,z66,z4,z16])],[(0,[z957,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z958,z5]),(0,[z0,z2,z4,z763,z5,z104])]],
   [[(0,[z0,z1,z313,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z959]),(0,[z17,z1,z2,z4,z6,z81]),(0,[z0,z1,z2,z4,z430,z5]),(0,[z1,z2,z4,z19,z5,z765]),(0,[z0,z2,z4,z342,z900,z6]),(0,[z0,z960,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z961,z5])],[(0,[z0,z1,z962,z4,z5,z6]),(0,[z85,z1,z2,z86,z5,z6]),(0,[z770,z0,z1,z2,z4,z5]),(0,[z963,z1,z2,z4,z5,z6]),(0,[z964,z1,z2,z4,z5,z6]),(0,[z0,z1,z37,z4,z725,z5])],[(0,[z0,z1,z2,z4,z965,z5]),(0,[z0,z1,z2,z966,z4,z5]),(0,[z0,z1,z2,z4,z289,z6]),(1,[z1,z2,z4,z5,z765]),(0,[z97,z176,z1,z2,z4,z19]),(0,[z0,z1,z2,z4,z900,z6])],[(0,[z0,z2,z4,z900,z278,z6]),(0,[z0,z1,z2,z4,z5,z967]),(0,[z158,z0,z1,z2,z83,z6])]],
   [[(0,[z0,z1,z968,z4,z5,z6]),(0,[z171,z0,z1,z2,z83,z6])],[(0,[z0,z1,z2,z4,z5,z969]),(0,[z97,z1,z2,z4,z5,z765]),(0,[z627,z1,z2,z4,z19,z5]),(0,[z115,z0,z614,z4,z5,z6]),(0,[z0,z1,z4,z970,z5,z6]),(0,[z0,z1,z971,z4,z5,z6])],[(0,[z0,z1,z2,z4,z972,z6]),(0,[z0,z1,z11,z2,z4,z6]),(0,[z17,z1,z2,z4,z735,z6]),(0,[z54,z0,z1,z2,z4,z430]),(1,[z0,z2,z4,z900,z6]),(0,[z1,z66,z4,z256,z6,z16])],[(0,[z973,z0,z1,z2,z4,z5]),(0,[z974,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z975]),(0,[z976,z1,z2,z4,z5,z6]),(0,[z180,z1,z2,z4,z5,z78])]],
   [[(0,[z0,z1,z977,z2,z4,z5]),(0,[z0,z1,z726,z4,z5,z6]),(0,[z140,z1,z2,z4,z5,z28]),(0,[z115,z0,z728,z4,z5,z6]),(0,[z978,z1,z2,z4,z5,z6]),(0,[z979,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z980]),(0,[z188,z0,z1,z2,z4,z174]),(0,[z0,z109,z728,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z981]),(0,[z0,z1,z4,z725,z5,z185]),(0,[z0,z1,z2,z148,z5,z78])],[(0,[z982,z0,z1,z2,z4,z5]),(0,[z17,z1,z2,z4,z5,z122]),(0,[z0,z1,z37,z309,z4,z5]),(0,[z115,z0,z133,z4,z5,z6]),(0,[z983,z1,z2,z4,z5,z6]),(0,[z0,z1,z35,z138,z5,z6]),(0,[z0,z1,z984,z4,z5,z6]),(0,[z0,z1,z4,z985,z5,z6])],[(0,[z0,z1,z2,z4,z5,z986]),(0,[z54,z0,z1,z2,z4,z70]),(0,[z0,z1,z2,z4,z5,z987]),(0,[z0,z1,z35,z36,z5,z6])]],
   [[(0,[z988,z0,z1,z2,z5,z6]),(0,[z63,z0,z2,z709,z5,z6]),(0,[z45,z0,z1,z46,z5,z6]),(0,[z180,z1,z2,z4,z55,z5])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z27,z1,z2,z4,z5,z28]),(0,[z68,z1,z2,z4,z19,z5]),(0,[z0,z1,z66,z4,z769,z6])],[(0,[z0,z1,z2,z4,z5,z989]),(0,[z17,z1,z225,z4,z6,z81]),(0,[z180,z1,z2,z4,z5,z6]),(0,[z42,z1,z2,z4,z5,z28]),(0,[z271,z1,z2,z4,z119,z6])],[(0,[z17,z1,z2,z4,z6,z203]),(0,[z17,z1,z648,z2,z4,z6]),(0,[z63,z0,z310,z34,z5,z6]),(0,[z63,z0,z139,z34,z5,z6]),(0,[z990,z0,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z991]),(0,[z0,z992,z2,z4,z5,z6]),(0,[z332,z0,z1,z2,z38,z5]),(0,[z993,z1,z2,z4,z5,z6]),(0,[z63,z0,z2,z34,z5,z409]),(0,[z994,z1,z2,z4,z5,z6]),(0,[z0,z2,z4,z763,z5,z6]),(0,[z0,z1,z2,z995,z4,z5]),(0,[z468,z1,z2,z4,z5,z88]),(0,[z0,z1,z37,z637,z4,z5])],[(0,[z0,z1,z2,z4,z5,z996]),(0,[z997,z0,z1,z2,z4,z5]),(0,[z273,z255,z0,z1,z2,z4]),(0,[z142,z1,z2,z781,z5,z6]),(0,[z0,z1,z2,z4,z62,z5]),(0,[z0,z1,z2,z998,z5,z6]),(0,[z999,z1,z2,z4,z5,z6]),(0,[z0,z1000,z2,z4,z5,z6]),(0,[z0,z1,z4,z725,z5,z6])],[(0,[z1,z726,z205,z4,z5,z6]),(0,[z17,z0,z1,z2,z4,z174]),(0,[z0,z1,z2,z4,z5,z1001])],[(0,[z0,z1,z1002,z2,z4,z5]),(0,[z0,z1,z2,z1003,z5,z6]),(0,[z0,z1,z2,z4,z1004,z5]),(0,[z0,z31,z2,z4,z5,z104])]],
   [[(0,[z255,z0,z1,z2,z4,z6]),(0,[z1,z2,z4,z256,z5,z6]),(0,[z0,z1,z2,z4,z1005,z5]),(0,[z0,z1006,z2,z4,z5,z6]),(0,[z0,z1,z1007,z4,z5,z6]),(0,[z0,z109,z4,z643,z5,z6]),(0,[z0,z1,z2,z84,z100,z338])],[(0,[z0,z1,z2,z4,z5,z1008]),(0,[z123,z743,z2,z4,z5,z6]),(0,[z0,z1,z1009,z4,z5,z6])],[(0,[z0,z1,z1010,z2,z4,z6]),(0,[z0,z1,z2,z4,z1011,z6]),(0,[z1,z2,z4,z5,z735,z6]),(0,[z0,z1,z2,z4,z430,z18]),(0,[z27,z1,z2,z4,z5,z765]),(0,[z54,z652,z0,z1,z2,z4]),(0,[z0,z1,z2,z4,z5,z1012]),(0,[z0,z1,z35,z290,z36,z5])],[(0,[z1013,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1014]),(0,[z7,z1,z11,z205,z4,z6]),(0,[z65,z0,z1,z11,z4,z6]),(0,[z0,z1,z2,z1015,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z5,z1016]),(0,[z0,z1,z2,z4,z1017,z5]),(0,[z7,z1,z225,z4,z5,z6]),(0,[z0,z2,z4,z1018,z5,z6]),(0,[z449,z17,z1,z2,z4,z6]),(0,[z17,z1,z2,z4,z6,z366]),(0,[z0,z1,z2,z4,z735,z6]),(0,[z0,z1,z2,z4,z430,z289]),(0,[z1019,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1020,z5])],[(0,[z0,z1,z2,z4,z1021,z5]),(0,[z0,z1,z2,z4,z5,z1022]),(0,[z0,z1,z2,z4,z1023,z5]),(0,[z143,z0,z2,z4,z900,z6]),(0,[z0,z1,z2,z4,z5,z1024]),(0,[z0,z1,z66,z4,z6,z16])],[(0,[z0,z1,z2,z1025,z5,z6]),(1,[z743,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1026,z6]),(0,[z273,z0,z1,z2,z4,z5]),(0,[z273,z0,z1,z11,z2,z4]),(0,[z0,z1,z2,z4,z5,z1027]),(0,[z0,z1,z2,z4,z763,z5]),(0,[z0,z1,z2,z247,z5,z78]),(0,[z0,z1028,z2,z4,z5,z6]),(0,[z0,z1,z2,z38,z714,z5])],[(0,[z0,z1,z225,z4,z5,z6]),(0,[z0,z1,z2,z4,z1029,z6]),(0,[z238,z1,z726,z4,z5,z6]),(0,[z1,z15,z4,z5,z6,z383]),(0,[z97,z407,z1,z2,z4,z5])]],
   [[(0,[z1030,z0,z1,z2,z4,z5]),(0,[z0,z71,z2,z4,z278,z6]),(0,[z0,z2,z4,z900,z5,z6]),(0,[z1031,z1,z2,z4,z5,z6])],[(0,[z1,z743,z2,z4,z5,z6]),(0,[z0,z634,z2,z4,z32,z5])],[(0,[z142,z1,z2,z440,z5,z6]),(0,[z1,z15,z11,z2,z4,z6]),(0,[z0,z1,z2,z4,z1032,z6])],[(0,[z0,z1,z2,z4,z5,z1033]),(0,[z0,z1,z2,z4,z1034,z6]),(0,[z97,z1,z2,z4,z19,z5]),(0,[z0,z1,z2,z4,z5,z1035]),(0,[z384,z1,z2,z4,z268,z6]),(0,[z0,z1,z2,z4,z5,z1036]),(0,[z1037,z1,z2,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 560) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 560).take 458) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1018)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [560, 458] = true :=
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

end PEqualNP.Outside.L_meta_42546

theorem PEqualNP.Outside.L_meta_42546 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276812992 * 2 ^ 32 + 4243122368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276812992 * 2 ^ 32 + 4243122368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42546.solve