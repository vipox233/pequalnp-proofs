import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45788

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
  Nat.testBit (4008241896 * 2 ^ 32 + 4008241344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x2022831b031b1bca#64 ++ 0x02022831b031b1bc#64 ++ 0xe4679f3f473f3fcf#64 ++ 0xae4679f3f473f3fc#64 : BitVec 256),
   (0x0189284518454553#64 ++ 0x0018928451845455#64 ++ 0xfb99e8c7b8c7c7ff#64 ++ 0xffb99e8c7b8c7c7f#64 : BitVec 256),
   (0x4c1450a8c0a8a8ac#64 ++ 0x04c1450a8c0a8a8a#64 ++ 0x6c1e70f8c0f8f8fe#64 ++ 0xf6c1e70f8c0f8f8f#64 : BitVec 256),
   (0x8ec07d00ed00f600#64 ++ 0x08ec07d00ed00f60#64 ++ 0xbfe07f00ff00ff0d#64 ++ 0xdbfe07f00ff00ff0#64 : BitVec 256),
   (0x1f7f8000f6f60000#64 ++ 0x11f7f8000f6f6000#64 ++ 0xdfff8000ffff000b#64 ++ 0x9dfff8000ffff000#64 : BitVec 256),
   (0x1ffffef600000000#64 ++ 0x21ffffef60000000#64 ++ 0x1fffffff00000007#64 ++ 0xe1fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0189284400000000 0x0018928440000000 0x1b99e8c700000007 0xe1b99e8c70000000

def z1 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z2 : W := mkw 0x1ffffef718454553 0x21ffffef71845455 0xffffffffb8c7c7ff 0xfffffffffb8c7c7f

def z3 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe4679f3f473f3fcf 0xae4679f3f473f3fc

def z4 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z5 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z6 : W := mkw 0x0189284518454553 0x0018928451845455 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z7 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1fffffff00000007 0xe1fffffff0000000

def z8 : W := mkw 0x8ec07d00e500b200 0x08ec07d00e500b20 0x1fe07f0047003805 0xc1fe07f004700380

def z9 : W := mkw 0x0e400000e4000000 0x00e400000e400000 0x9fe00000ff000009 0x99fe00000ff00000

def z10 : W := mkw 0x4e5450a8e4a8a8ac 0x04e5450a8e4a8a8a 0xfffe70f8fff8f8ff 0xffffe70f8fff8f8f

def z11 : W := mkw 0x0e628000e6120000 0x00e628000e612000 0xdfe78000ff3f000b 0x9dfe78000ff3f000

def z12 : W := mkw 0x0022800002120000 0x0002280000212000 0xc4678000473f000b 0x8c4678000473f000

def z13 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x00007fff00000004 0x600007fff0000000

def z14 : W := mkw 0x400050a80008a8ac 0x0400050a80008a8a 0x200070f80000f8f4 0x6200070f80000f8f

def z15 : W := mkw 0x401400a800a808ac 0x0401400a800a808a 0x401e00f800f800f2 0x2401e00f800f800f

def z16 : W := mkw 0x0022821200000000 0x0002282120000000 0x04679f3f00000007 0xa04679f3f0000000

def z17 : W := mkw 0x2022821b021b09ca 0x02022821b021b09c 0x4007803f003f00c2 0x24007803f003f00c

def z18 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x240670f84038f8f4 0x6240670f84038f8f

def z19 : W := mkw 0x2022831303131342 0x0202283130313134 0x80618f0707070701 0x080618f070707070

def z20 : W := mkw 0x21abab5f1b5f5fdb 0x021abab5f1b5f5fd 0xffffffffffffffff 0xffffffffffffffff

def z21 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xec7fffffc7ffffff 0xfec7fffffc7fffff

def z22 : W := mkw 0x8e405500e500b200 0x08e405500e500b20 0x0460170047003800 0x0046017004700380

def z23 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0xdfffffffffff000f 0xfdfffffffffff000

def z24 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe0000000473f3fc8 0x0e0000000473f3fc

def z25 : W := mkw 0x1f5d0000f4e40000 0x11f5d0000f4e4000 0x1b980000b8c00000 0x11b980000b8c0000

def z26 : W := mkw 0x3f7f831bf7ff1bca 0x13f7f831bf7ff1bc 0xffff9f3fffff3fcf 0xbffff9f3fffff3fc

def z27 : W := mkw 0x8ec07c00ec00e400 0x08ec07c00ec00e40 0x9fe06000ff00c009 0xd9fe06000ff00c00

def z28 : W := mkw 0x0022821200000000 0x0002282120000000 0x0466173800000000 0x0046617380000000

def z29 : W := mkw 0x0ec07c0000000000 0x00ec07c000000000 0x1fe07f0000000005 0xc1fe07f000000000

def z30 : W := mkw 0x0fc97c4518454553 0x00fc97c451845455 0xfff9ffc7b8c7c7ff 0xffff9ffc7b8c7c7f

def z31 : W := mkw 0x0c005000c000a000 0x00c005000c000a00 0x2c007000c000f80c 0xd2c007000c000f80

def z32 : W := mkw 0x1ffffef608004400 0x21ffffef60800440 0xbfffffffb800c70f 0xfbfffffffb800c70

def z33 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0xb7e01f007f003f0d 0x8b7e01f007f003f0

def z34 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x13e18f0700000001 0x013e18f070000000

def z35 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x0466173800000000 0x0046617380000000

def z36 : W := mkw 0x0189284418444411 0x0018928441844441 0x1380000038000000 0x0138000003800000

def z37 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x17e79f3f00000001 0x017e79f3f0000000

def z38 : W := mkw 0x400050a80008a8ac 0x0400050a80008a8a 0x640670f84038f8fe 0xe640670f84038f8f

def z39 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe0618f07473f3fc9 0x0e0618f07473f3fc

def z40 : W := mkw 0x0c368000c2b20000 0x00c368000c2b2000 0xcc7f8000c7ff000b 0x9cc7f8000c7ff000

def z41 : W := mkw 0x00000000f6f60000 0x100000000f6f6000 0xc0000000ffff0008 0x1c0000000ffff000

def z42 : W := mkw 0x2000031b01091bca 0x02000031b01091bc 0x20001f3f00003fc4 0x220001f3f00003fc

def z43 : W := mkw 0x0189284518454553 0x0018928451845455 0xdb998807b8c7070b 0x9db998807b8c7070

def z44 : W := mkw 0x0c1450a000000000 0x00c1450a00000000 0x0c1e70f800000006 0xe0c1e70f80000000

def z45 : W := mkw 0xced47da0eda0f624 0x0ced47da0eda0f62 0xbff87fc0ffc0ff3d 0xdbff87fc0ffc0ff3

def z46 : W := mkw 0x1ffffef6c0a00000 0x21ffffef6c0a0000 0x5fffffffc0f8000f 0xf5fffffffc0f8000

def z47 : W := mkw 0x1f5d0000f4e40000 0x11f5d0000f4e4000 0xdb998000b8c7000b 0x9db998000b8c7000

def z48 : W := mkw 0x0080284400000000 0x0008028440000000 0x000068c700000004 0x6000068c70000000

def z49 : W := mkw 0x2022831203121200 0x0202283120312120 0x0060070007000000 0x0006007000700000

def z50 : W := mkw 0x5ffffefec0a8a8ac 0x25ffffefec0a8a8a 0x1fffffff40383807 0xe1fffffff4038380

def z51 : W := mkw 0x5f7fd0a8f6fea8ac 0x15f7fd0a8f6fea8a 0xfffff0f8fffff8ff 0xffffff0f8fffff8f

def z52 : W := mkw 0x800001000900f600 0x0800001000900f60 0x200000000000ff00 0x0200000000000ff0

def z53 : W := mkw 0x00802e5600000000 0x200802e560000000 0x00000f0700000000 0x000000f070000000

def z54 : W := mkw 0x2000021b000909ca 0x02000021b000909c 0x0000003f000000c0 0x20000003f000000c

def z55 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0x93e00f003f000701 0x093e00f003f00070

def z56 : W := mkw 0xced47da8eda8feac 0x0ced47da8eda8fea 0xfffe7ff8fff8ffff 0xffffe7ff8fff8fff

def z57 : W := mkw 0x0022821300010142 0x0002282130001014 0xe4679f3f000707cf 0xae4679f3f000707c

def z58 : W := mkw 0x1fdd7ce400000000 0x21fdd7ce40000000 0x1b9860c000000000 0x41b9860c00000000

def z59 : W := mkw 0x1fffa84400000000 0x01fffa8440000000 0x1fffe8c700000007 0xe1fffe8c70000000

def z60 : W := mkw 0x13eba8453e574553 0x113eba8453e57455 0x93e188073f070701 0x093e188073f07070

def z61 : W := mkw 0x0000010001001200 0x0000001000100120 0xa000000047003f08 0x0a000000047003f0

def z62 : W := mkw 0x80000100ed00f600 0x080000100ed00f60 0xa0000000ff00ff08 0x1a0000000ff00ff0

def z63 : W := mkw 0x21abaa5f1a5f4ddb 0x021abaa5f1a5f4dd 0xfb9fe8ffb8ffc7ff 0xffb9fe8ffb8ffc7f

def z64 : W := mkw 0x0109000010440000 0x0010900001044000 0xdb998000b8c7000b 0x9db998000b8c7000

def z65 : W := mkw 0x1e768000e6b20000 0x11e768000e6b2000 0x0466000047380000 0x0046600004738000

def z66 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00180000007000b 0x8c00180000007000

def z67 : W := mkw 0x0000000118454553 0x0000000011845455 0xe0000000b8c7c7f8 0x1e0000000b8c7c7f

def z68 : W := mkw 0x2022821a021a0888 0x02022821a021a088 0x0006003800380000 0x0000600380038000

def z69 : W := mkw 0x4d9d78edd8ededff 0x04d9d78edd8ededf 0xff9ff8fff8ffffff 0xfff9ff8fff8fffff

def z70 : W := mkw 0x400050a8c0a8a8ac 0x0400050a8c0a8a8a 0x600070f8c0f8f8fc 0x7600070f8c0f8f8f

def z71 : W := mkw 0x1f7f821200000000 0x01f7f82120000000 0x1fff9f3f00000007 0xa1fff9f3f0000000

def z72 : W := mkw 0x113f800012f60000 0x1113f800012f6000 0x401f800000ff0002 0x0401f800000ff000

def z73 : W := mkw 0x1ffffef612f60000 0x31ffffef612f6000 0x5fffffff00ff0007 0xe5fffffff00ff000

def z74 : W := mkw 0x20802b5f09095fdb 0x020802b5f09095fd 0x20007fff0000fff4 0x620007fff0000fff

def z75 : W := mkw 0x3f7f831af7fe1a88 0x13f7f831af7fe1a8 0xdfff9738ffff380b 0x9dfff9738ffff380

def z76 : W := mkw 0x1fdd7ce400000000 0x21fdd7ce40000000 0x1b99e8c700000007 0xe1b99e8c70000000

def z77 : W := mkw 0x0fc97c4400000000 0x00fc97c440000000 0x1ff9ffc700000007 0xe1ff9ffc70000000

def z78 : W := mkw 0x4c1450a0c0a0a024 0x04c1450a0c0a0a02 0x081860c080c0c030 0x5081860c080c0c03

def z79 : W := mkw 0x0c1450a0c0a00000 0x00c1450a0c0a0000 0x4c1e70f8c0f8000e 0xf4c1e70f8c0f8000

def z80 : W := mkw 0x2022831b01091bca 0x02022831b01091bc 0x24679f3f00003fc7 0xa24679f3f00003fc

def z81 : W := mkw 0x81897d451945f753 0x081897d451945f75 0xfb99ffc7b8c7ffff 0xffb99ffc7b8c7fff

def z82 : W := mkw 0x0189284518454553 0x0018928451845455 0xf3818807b8c7c7f9 0x1f3818807b8c7c7f

def z83 : W := mkw 0x0109004518454553 0x0010900451845455 0xe01980c7b8c7c7fa 0x3e01980c7b8c7c7f

def z84 : W := mkw 0x9e76d7b2e500b200 0x29e76d7b2e500b20 0x0466173847003800 0x0046617384700380

def z85 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xffffe0c0ffffc0ff 0xfffffe0c0ffffc0f

def z86 : W := mkw 0x6c36d3bbc3bbbbee 0x06c36d3bbc3bbbbe 0xec7fffffc7ffffff 0xfec7fffffc7fffff

def z87 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0x60079f3f003f3fc6 0x260079f3f003f3fc

def z88 : W := mkw 0x0022821200000000 0x0002282120000000 0x00618f0700000001 0x000618f070000000

def z89 : W := mkw 0x113f82f600000000 0x2113f82f60000000 0x047f9fff00000007 0xa047f9fff0000000

def z90 : W := mkw 0x0080280008004400 0x0008028000800440 0x9380080038000701 0x0938008003800070

def z91 : W := mkw 0x0c140000c0a00000 0x00c140000c0a0000 0x4c1e0000c0f8000a 0x94c1e0000c0f8000

def z92 : W := mkw 0x1f5d0000f6f60000 0x11f5d0000f6f6000 0xdb980000ffff0008 0x1db980000ffff000

def z93 : W := mkw 0x401400a000a00024 0x0401400a000a0002 0x001800c000c00030 0x0001800c000c0003

def z94 : W := mkw 0x0000010001001200 0x0000001000100120 0xa4601f0047003f0d 0x8a4601f0047003f0

def z95 : W := mkw 0xaee2ff1bef1bffca 0x0aee2ff1bef1bffc 0xffe7ff3fff3fffcf 0xfffe7ff3fff3fffc

def z96 : W := mkw 0x01090000f6f60000 0x101090000f6f6000 0xdb998000ffff000b 0x9db998000ffff000

def z97 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x97e01f007f003f01 0x097e01f007f003f0

def z98 : W := mkw 0x00807ce400000000 0x200807ce40000000 0x000060c000000000 0x4000060c00000000

def z99 : W := mkw 0x9ffffd00fff6f600 0x19ffffd00fff6f60 0xffffff00ffffff0f 0xdffffff00ffffff0

def z100 : W := mkw 0x1f7fd6b2f6f60000 0x31f7fd6b2f6f6000 0xdfff9738ffff000b 0x9dfff9738ffff000

def z101 : W := mkw 0x01aba8451a574553 0x001aba8451a57455 0xffffe8c7ffffc7ff 0xfffffe8c7ffffc7f

def z102 : W := mkw 0x13ebfef600000000 0x213ebfef60000000 0x13e1ffff00000005 0x613e1ffff0000000

def z103 : W := mkw 0x82c02c002c004400 0x082c02c002c00440 0x1380000038000000 0x0138000003800000

def z104 : W := mkw 0x0080284508014553 0x0008028450801455 0x0000080700000700 0x0000008070000070

def z105 : W := mkw 0x0189284400000000 0x0018928440000000 0x1b9860c000000000 0x41b9860c00000000

def z106 : W := mkw 0x418978ed184dedff 0x0418978ed184dedf 0xfb99f8ffb8c7ffff 0xffb99f8ffb8c7fff

def z107 : W := mkw 0x9ffffff60900f600 0x29ffffff60900f60 0x3fffffff0000ff07 0xe3fffffff0000ff0

def z108 : W := mkw 0x4c1400a8c0a808ac 0x04c1400a8c0a808a 0x4c1e00f8c0f800fa 0xb4c1e00f8c0f800f

def z109 : W := mkw 0x8ec07c00ec00e400 0x08ec07c00ec00e40 0x1b806000b800c000 0x51b806000b800c00

def z110 : W := mkw 0x9ffffff6ed00f600 0x29ffffff6ed00f60 0xbfffffffff00ff0f 0xfbfffffffff00ff0

def z111 : W := mkw 0x113f82f600000000 0x2113f82f60000000 0x001f80ff00000002 0x2001f80ff0000000

def z112 : W := mkw 0x4c1450a800a808ac 0x04c1450a800a808a 0x4c1e70f800f800f6 0xe4c1e70f800f800f

def z113 : W := mkw 0x0c36d2b200000000 0x00c36d2b20000000 0x0c7fffff00000007 0xe0c7fffff0000000

def z114 : W := mkw 0x0189284418444411 0x0018928441844441 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z115 : W := mkw 0x2022831a031a1a88 0x02022831a031a1a8 0x0466173847383800 0x0046617384738380

def z116 : W := mkw 0x1ffffef602120000 0x21ffffef60212000 0xdfffffff473f000f 0xedfffffff473f000

def z117 : W := mkw 0xa0807f1b0909ffca 0x0a0807f1b0909ffc 0x20007f3f0000ffc4 0x620007f3f0000ffc

def z118 : W := mkw 0x0109004510450153 0x0010900451045015 0x401980c700c700f2 0x2401980c700c700f

def z119 : W := mkw 0x0189284518454553 0x0018928451845455 0x6019e8c700c7c7f6 0x66019e8c700c7c7f

def z120 : W := mkw 0x1ffffef6c000a000 0x21ffffef6c000a00 0x3fffffffc000f80f 0xf3fffffffc000f80

def z121 : W := mkw 0x5ffff8edfeffedff 0x15ffff8edfeffedf 0xfffff8ffffffffff 0xffffff8fffffffff

def z122 : W := mkw 0x0080284508014553 0x0008028450801455 0x200068c70000c7f4 0x6200068c70000c7f

def z123 : W := mkw 0x0022800002120000 0x0002280000212000 0x0466000047380000 0x0046600004738000

def z124 : W := mkw 0x0022800000000000 0x0002280000000000 0x0467800000000003 0x8046780000000000

def z125 : W := mkw 0x80807d000900f600 0x080807d000900f60 0x20007f000000ff04 0x420007f000000ff0

def z126 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001880700000007 0xa000188070000000

def z127 : W := mkw 0x8ec07c00ec00e400 0x08ec07c00ec00e40 0x3f807000f800f80c 0xd3f807000f800f80

def z128 : W := mkw 0xcc1451a8eda8feac 0x0cc1451a8eda8fea 0xec1e70f8fff8fffe 0xfec1e70f8fff8fff

def z129 : W := mkw 0x0000000110450153 0x0000000011045015 0x4000000000c700f0 0x04000000000c700f

def z130 : W := mkw 0x5f7fd0a0f6f6a024 0x15f7fd0a0f6f6a02 0xdfffe0c0ffffc03b 0xddfffe0c0ffffc03

def z131 : W := mkw 0x9ffffef6ec00e400 0x29ffffef6ec00e40 0x1fffffffb800c007 0xf1fffffffb800c00

def z132 : W := mkw 0x0000000100010142 0x0000000010001014 0xe0018807000707cf 0xae0018807000707c

def z133 : W := mkw 0x0ec07c00c000a000 0x00ec07c00c000a00 0x3fe07f00c000f80d 0xd3fe07f00c000f80

def z134 : W := mkw 0x137f800036f60000 0x1137f800036f6000 0xd3ff80003fff0003 0x0d3ff80003fff000

def z135 : W := mkw 0x0000000000000000 0x0000000000000000 0x681860c080c0c0fe 0xf681860c080c0c0f

def z136 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x7fffffff80c0c0ff 0xf7fffffff80c0c0f

def z137 : W := mkw 0x0ec07c00e4000000 0x00ec07c00e400000 0x9fe07f00ff00000d 0xd9fe07f00ff00000

def z138 : W := mkw 0x0000000800080888 0x0000000080008088 0x64061038403838ce 0xa64061038403838c

def z139 : W := mkw 0x001400a000000000 0x0001400a00000000 0x001e00f800000002 0x2001e00f80000000

def z140 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x0406103840383800 0x0040610384038380

def z141 : W := mkw 0x1fdd7ce4f4e40000 0x31fdd7ce4f4e4000 0x1b9860c0b8c00000 0x51b9860c0b8c0000

def z142 : W := mkw 0x0c140008c0a80888 0x00c140008c0a8088 0x6c1e1038c0f838ce 0xb6c1e1038c0f838c

def z143 : W := mkw 0x3e76d7ba031a1a88 0x23e76d7ba031a1a8 0x0466173847383800 0x0046617384738380

def z144 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x24607f004700ff04 0x424607f004700ff0

def z145 : W := mkw 0x80000100e500b200 0x080000100e500b20 0x0000000047003800 0x0000000004700380

def z146 : W := mkw 0x0109000110450142 0x0010900011045014 0xfb998807b8c707cf 0xbfb998807b8c707c

def z147 : W := mkw 0x136b800036560000 0x1136b80003656000 0x93e180003f070001 0x093e180003f07000

def z148 : W := mkw 0x112b800012560000 0x1112b80001256000 0x0001800000070000 0x0000180000007000

def z149 : W := mkw 0x0189284418444411 0x0018928441844441 0x1b99e8c7b8c0c037 0xf1b99e8c7b8c0c03

def z150 : W := mkw 0x0189284518454553 0x0018928451845455 0x9b99e8c738070707 0xe9b99e8c73807070

def z151 : W := mkw 0x2022821302130142 0x0202282130213014 0x0001800700070000 0x0000180070007000

def z152 : W := mkw 0x1f7f8045f6f70153 0x11f7f8045f6f7015 0xdfff80c7ffff00fb 0xbdfff80c7ffff00f

def z153 : W := mkw 0x00000000c000a000 0x000000000c000a00 0x20000000c000f808 0x120000000c000f80

def z154 : W := mkw 0xc0000108eda8feac 0x0c0000108eda8fea 0xe0000000fff8fff8 0x1e0000000fff8fff

def z155 : W := mkw 0x0189284400000000 0x0018928440000000 0x1381880700000001 0x0138188070000000

def z156 : W := mkw 0x0109004400000000 0x0010900440000000 0x001980c700000002 0x2001980c70000000

def z157 : W := mkw 0x1ffffef618444411 0x21ffffef61844441 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z158 : W := mkw 0x0080280108014542 0x0008028010801454 0xfb81e807b807c7cf 0xffb81e807b807c7c

def z159 : W := mkw 0x1fffa845fef74553 0x11fffa845fef7455 0xffffe8c7ffffc7ff 0xfffffe8c7ffffc7f

def z160 : W := mkw 0x2c36831bc3bb1bca 0x02c36831bc3bb1bc 0xec7f9f3fc7ff3fcf 0xbec7f9f3fc7ff3fc

def z161 : W := mkw 0x8c005100ed00f600 0x08c005100ed00f60 0xac007000ff00ff0c 0xdac007000ff00ff0

def z162 : W := mkw 0x8fc97d44fd44f611 0x08fc97d44fd44f61 0xbff87fc0ffc0ff3d 0xdbff87fc0ffc0ff3

def z163 : W := mkw 0x0c145000c0a0a000 0x00c145000c0a0a00 0x6c1e7000c0f8f80e 0xd6c1e7000c0f8f80

def z164 : W := mkw 0x0189284518454553 0x0018928451845455 0x5b99e0c7b8c7c0f2 0x75b99e0c7b8c7c0f

def z165 : W := mkw 0x1ffffef610440000 0x21ffffef61044000 0xdfffffffb8c7000f 0xfdfffffffb8c7000

def z166 : W := mkw 0x0ec07c0008004400 0x00ec07c000800440 0xbfe07f00b800c70d 0xdbfe07f00b800c70

def z167 : W := mkw 0x0000000018444411 0x0000000001844441 0x00000000b8c0c030 0x100000000b8c0c03

def z168 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x04679f3f00000007 0xa04679f3f0000000

def z169 : W := mkw 0x408078ed0809edff 0x0408078ed0809edf 0x200078ff0000fff4 0x6200078ff0000fff

def z170 : W := mkw 0x4d9d78e4d8e4e435 0x04d9d78e4d8e4e43 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z171 : W := mkw 0x80807d450901f753 0x080807d450901f75 0x20007fc70000fff4 0x620007fc70000fff

def z172 : W := mkw 0x4c947efec0a8a8ac 0x24c947efec0a8a8a 0x6c1e7fffc0f8f8fe 0xf6c1e7fffc0f8f8f

def z173 : W := mkw 0xaec07d09ef1bffca 0x0aec07d09ef1bffc 0xffe07f00ff3fffcd 0xdffe07f00ff3fffc

def z174 : W := mkw 0x1f7f800000000000 0x01f7f80000000000 0x1fff800000000003 0x81fff80000000000

def z175 : W := mkw 0x4c140008c0a8a8ac 0x04c140008c0a8a8a 0x6c1e0000c0f8f8fa 0x96c1e0000c0f8f8f

def z176 : W := mkw 0xeef6ffbbefbbffee 0x0eef6ffbbefbbffe 0xffffffffffffffff 0xffffffffffffffff

def z177 : W := mkw 0x1fdd2845fce54553 0x11fdd2845fce5455 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z178 : W := mkw 0x1ffffef636560000 0x31ffffef63656000 0x9fffffff3f070007 0xe9fffffff3f07000

def z179 : W := mkw 0x200001091b5f5fdb 0x0200001091b5f5fd 0xe0000000fffffff8 0x1e0000000fffffff

def z180 : W := mkw 0x1f7f8100f7f61200 0x11f7f8100f7f6120 0xffff9f00ffff3f0f 0x9ffff9f00ffff3f0

def z181 : W := mkw 0x8fc97d45fd45f753 0x08fc97d45fd45f75 0xfff9ffc7ffc7ffff 0xffff9ffc7ffc7fff

def z182 : W := mkw 0x1f7fd0a0f6f60000 0x11f7fd0a0f6f6000 0xdffff0f8ffff000f 0xfdffff0f8ffff000

def z183 : W := mkw 0x8fc97d00fd44f600 0x08fc97d00fd44f60 0xfff9ff00ffc7ff0f 0xdfff9ff00ffc7ff0

def z184 : W := mkw 0x01abaa5600000000 0x001abaa560000000 0x1fffffff00000007 0xe1fffffff0000000

def z185 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0xbbe06f00bf00c70d 0xdbbe06f00bf00c70

def z186 : W := mkw 0x0000000800080888 0x0000000080008088 0x60000000403838c8 0x060000000403838c

def z187 : W := mkw 0x5ffffef6c0a0a024 0x25ffffef6c0a0a02 0x1fffffff80c0c037 0xf1fffffff80c0c03

def z188 : W := mkw 0x83c92d453d455753 0x083c92d453d45575 0x93e18f073f070701 0x093e18f073f07070

def z189 : W := mkw 0x8ec07ff6ed00f600 0x28ec07ff6ed00f60 0xbfe07fffff00ff0d 0xfbfe07fffff00ff0

def z190 : W := mkw 0x0c005000c000a000 0x00c005000c000a00 0x0400100040003800 0x0040010004000380

def z191 : W := mkw 0x2022831bf7ff1bca 0x12022831bf7ff1bc 0xe4679f3fffff3fcf 0xbe4679f3fffff3fc

def z192 : W := mkw 0x0c1450a800080888 0x00c1450a80008088 0x6c1e70f8403838ce 0xe6c1e70f8403838c

def z193 : W := mkw 0x1ffffef718454553 0x21ffffef71845455 0x9fffffff38070707 0xe9fffffff3807070

def z194 : W := mkw 0x1fffa800fef64400 0x11fffa800fef6440 0xffffe800ffffc70f 0xdffffe800ffffc70

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x8460000047000009 0x8846000004700000

def z196 : W := mkw 0x00a2fef600000000 0x200a2fef60000000 0x0467ffff00000007 0xe0467ffff0000000

def z197 : W := mkw 0x7fffffffc3bbbbee 0x27fffffffc3bbbbe 0xffffffffc7ffffff 0xfffffffffc7fffff

def z198 : W := mkw 0x40000000c0a0a024 0x040000000c0a0a02 0x0000000080c0c030 0x10000000080c0c03

def z199 : W := mkw 0x0000000100010142 0x0000000010001014 0xe0000000000707c8 0x0e0000000000707c

def z200 : W := mkw 0x4c1450a0c0a0a024 0x04c1450a0c0a0a02 0x0c1e70f880c0c036 0xf0c1e70f880c0c03

def z201 : W := mkw 0x40000008c0a8a8ac 0x040000008c0a8a8a 0x60000000c0f8f8f8 0x160000000c0f8f8f

def z202 : W := mkw 0x313f821b12ff09ca 0x1313f821b12ff09c 0x401f803f00ff00c2 0x2401f803f00ff00c

def z203 : W := mkw 0x82c07d002d00f600 0x082c07d002d00f60 0xb3e07f003f00ff05 0x4b3e07f003f00ff0

def z204 : W := mkw 0x1f7f800012f60000 0x11f7f800012f6000 0x5fff800000ff0003 0x85fff800000ff000

def z205 : W := mkw 0xa0000109ef1bffca 0x0a0000109ef1bffc 0xe0000000ff3fffc8 0x1e0000000ff3fffc

def z206 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x0c7e77f800000006 0xe0c7e77f80000000

def z207 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x447f800047ff0002 0x0447f800047ff000

def z208 : W := mkw 0x1036800002b20000 0x11036800002b2000 0x0006000000380000 0x0000600000038000

def z209 : W := mkw 0x8fc97d45fd45f753 0x08fc97d45fd45f75 0xbfe1ff07ff07ff0d 0xdbfe1ff07ff07ff0

def z210 : W := mkw 0x11bffef600000000 0x211bffef60000000 0x001fffff00000006 0x6001fffff0000000

def z211 : W := mkw 0x1f7f8212f6f60000 0x11f7f8212f6f6000 0xdfff9f3fffff000f 0xbdfff9f3fffff000

def z212 : W := mkw 0x0109000010440000 0x0010900001044000 0x9381800038070001 0x0938180003807000

def z213 : W := mkw 0x4d9d78ecc0a8a8ac 0x04d9d78ecc0a8a8a 0x7f9ff8ffc0f8f8ff 0xf7f9ff8ffc0f8f8f

def z214 : W := mkw 0x5ffffefec0a8a8ac 0x25ffffefec0a8a8a 0x7fffffffc0f8f8ff 0xf7fffffffc0f8f8f

def z215 : W := mkw 0x8e405400e400a000 0x08e405400e400a00 0x0000000000000000 0x0000000000000000

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0x081860c080c0c030 0x5081860c080c0c03

def z217 : W := mkw 0x0080280008004400 0x0008028000800440 0xbb806800b800c70d 0xdbb806800b800c70

def z218 : W := mkw 0x401400a800a808ac 0x0401400a800a808a 0x681e60f880f8c0fe 0xf681e60f880f8c0f

def z219 : W := mkw 0x5f7fd0a8c0a8a8ac 0x05f7fd0a8c0a8a8a 0x7ffff0f8c0f8f8ff 0xf7ffff0f8c0f8f8f

def z220 : W := mkw 0x1ffffc00f6f60000 0x11ffffc00f6f6000 0xdfffff00ffff000f 0xddfffff00ffff000

def z221 : W := mkw 0x4d9d78e5d8e5e577 0x04d9d78e5d8e5e57 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z222 : W := mkw 0x1d3f8000d2f60000 0x11d3f8000d2f6000 0x4c1f8000c0ff000a 0x94c1f8000c0ff000

def z223 : W := mkw 0x0c807800c800e400 0x00c807800c800e40 0xbf807800f800ff0d 0xdbf807800f800ff0

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x0406103800000006 0xa040610380000000

def z225 : W := mkw 0x0c140000f6f60000 0x10c140000f6f6000 0xcc1e0000ffff000a 0x9cc1e0000ffff000

def z226 : W := mkw 0xa022831bef1bffca 0x0a022831bef1bffc 0xe4679f3fff3fffcf 0xbe4679f3fff3fffc

def z227 : W := mkw 0x8ec07d01fd45f753 0x08ec07d01fd45f75 0xffe07f00ffc7fffd 0xdffe07f00ffc7fff

def z228 : W := mkw 0x212b825f125f09db 0x0212b825f125f09d 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z229 : W := mkw 0x0189284410440000 0x0018928441044000 0xdb99e8c7b8c7000f 0xfdb99e8c7b8c7000

def z230 : W := mkw 0x9febfd00ff56f600 0x19febfd00ff56f60 0xbfe1ff00ff07ff0d 0xdbfe1ff00ff07ff0

def z231 : W := mkw 0x20000009021b09ca 0x020000009021b09c 0x40000000003f00c0 0x040000000003f00c

def z232 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x9be06f00bf00c701 0x59be06f00bf00c70

def z233 : W := mkw 0x0c1450a000000000 0x00c1450a00000000 0x6c1e70f880c0c0fe 0xf6c1e70f880c0c0f

def z234 : W := mkw 0x21abab571b575753 0x021abab571b57575 0x93e18f073f070701 0x093e18f073f07070

def z235 : W := mkw 0x0189284518454553 0x0018928451845455 0x9381880738070701 0x0938188073807070

def z236 : W := mkw 0x113f800000000000 0x0113f80000000000 0x001f800000000002 0x0001f80000000000

def z237 : W := mkw 0xcc947da8c9a8feac 0x0cc947da8c9a8fea 0x6c1e7ff8c0f8fffe 0xf6c1e7ff8c0f8fff

def z238 : W := mkw 0x60000109c3bbbbee 0x060000109c3bbbbe 0xe0000000c7fffff8 0x1e0000000c7fffff

def z239 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x2c067038c038f80c 0xd2c067038c038f80

def z240 : W := mkw 0x13ebae5636560000 0x313ebae563656000 0x93e18f073f070001 0x093e18f073f07000

def z241 : W := mkw 0x0e400100e5001200 0x00e400100e500120 0xbfe01f00ff003f0d 0x9bfe01f00ff003f0

def z242 : W := mkw 0x3f7f831b031b1bca 0x03f7f831b031b1bc 0xffff9f3f473f3fcf 0xaffff9f3f473f3fc

def z243 : W := mkw 0x8c807d00c900f600 0x08c807d00c900f60 0x2c007f00c000ff0c 0xd2c007f00c000ff0

def z244 : W := mkw 0x2022821b021b09ca 0x02022821b021b09c 0xc467803f473f00cb 0xac467803f473f00c

def z245 : W := mkw 0x0022821200000000 0x0002282120000000 0x0007803f00000002 0x20007803f0000000

def z246 : W := mkw 0x1e540000e4a00000 0x11e540000e4a0000 0x0000000000000000 0x0000000000000000

def z247 : W := mkw 0x40000009d8ededff 0x040000009d8ededf 0xe0000000f8fffff8 0x1e0000000f8fffff

def z248 : W := mkw 0x3fffffff031b1bca 0x23fffffff031b1bc 0xffffffff473f3fcf 0xeffffffff473f3fc

def z249 : W := mkw 0x136b800036560000 0x1136b80003656000 0xd7e780007f3f000b 0x8d7e780007f3f000

def z250 : W := mkw 0x0189294519455753 0x0018929451945575 0xfff9ffc7ffc7ffff 0xffff9ffc7ffc7fff

def z251 : W := mkw 0x5f7fd0a8f6fea8ac 0x15f7fd0a8f6fea8a 0xdfff9038ffff380b 0x9dfff9038ffff380

def z252 : W := mkw 0x8ed47d00eda0f600 0x08ed47d00eda0f60 0xfffe7f00fff8ff0f 0xdfffe7f00fff8ff0

def z253 : W := mkw 0x2000010103131342 0x0200001010313134 0x8000000007070700 0x0800000000707070

def z254 : W := mkw 0x3ffffeff021b09ca 0x23ffffeff021b09c 0x5fffffff003f00c7 0xe5fffffff003f00c

def z255 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0x84679f3f473f3f01 0x084679f3f473f3f0

def z256 : W := mkw 0x1f7fd6f600000000 0x21f7fd6f60000000 0x047f97ff00000002 0x2047f97ff0000000

def z257 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xa0619f3f07073fc5 0x2a0619f3f07073fc

def z258 : W := mkw 0x6022831bc3bbbbee 0x06022831bc3bbbbe 0xe4679f3fc7ffffff 0xbe4679f3fc7fffff

def z259 : W := mkw 0x0000000100010142 0x0000000010001014 0x8001880700070701 0x0800188070007070

def z260 : W := mkw 0x8ec07d08ed08fe88 0x08ec07d08ed08fe8 0xffe67f38ff38ffcf 0xfffe67f38ff38ffc

def z261 : W := mkw 0x00000001fef74553 0x100000001fef7455 0xe0000000ffffc7f8 0x1e0000000ffffc7f

def z262 : W := mkw 0x000002f600000000 0x2000002f60000000 0x000000ff00000000 0x2000000ff0000000

def z263 : W := mkw 0x8ec07c00ec00e400 0x08ec07c00ec00e40 0x1fe07f00b800c005 0xd1fe07f00b800c00

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z265 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0x4467973f473f38c2 0x24467973f473f38c

def z266 : W := mkw 0x1ffffef6f4e40000 0x31ffffef6f4e4000 0x1fffffffb8c00007 0xf1fffffffb8c0000

def z267 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe0018807473f3fcf 0xae0018807473f3fc

def z268 : W := mkw 0xafebff5fff5fffdb 0x0afebff5fff5fffd 0xffffffffffffffff 0xffffffffffffffff

def z269 : W := mkw 0x336b831b375f1bca 0x1336b831b375f1bc 0xf7e79f3f7f3f3fcf 0xaf7e79f3f7f3f3fc

def z270 : W := mkw 0x1f7f82f600000000 0x21f7f82f60000000 0x1fff80ff00000003 0xa1fff80ff0000000

def z271 : W := mkw 0x0109004510450153 0x0010900451045015 0xe01988c700c707ff 0xae01988c700c707f

def z272 : W := mkw 0x603683bb03bb1bee 0x0603683bb03bb1be 0xe47f9fff47ff3fff 0xae47f9fff47ff3ff

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x4818000080c0000a 0x94818000080c0000

def z274 : W := mkw 0x1e768000e6b20000 0x11e768000e6b2000 0xc4678000473f000b 0x8c4678000473f000

def z275 : W := mkw 0x40000008f6fea8ac 0x140000008f6fea8a 0xe0000000fffff8f8 0x1e0000000fffff8f

def z276 : W := mkw 0x20a2ffff031b1bca 0x220a2ffff031b1bc 0xe467ffff473f3fcf 0xee467ffff473f3fc

def z277 : W := mkw 0x0080284508014553 0x0008028450801455 0xe001e8c70007c7ff 0xee001e8c70007c7f

def z278 : W := mkw 0x8ec07d002d005600 0x08ec07d002d00560 0x9fe07f003f000705 0xc9fe07f003f00070

def z279 : W := mkw 0x600053bb0109bbee 0x0600053bb0109bbe 0x20007fff0000fff4 0x620007fff0000fff

def z280 : W := mkw 0xae62d71ae71aba88 0x0ae62d71ae71aba8 0x0466173847383800 0x0046617384738380

def z281 : W := mkw 0x2022831a031a1a88 0x02022831a031a1a8 0x64661738473838ce 0xa64661738473838c

def z282 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x681860c0c0f8f8f8 0x5681860c0c0f8f8f

def z283 : W := mkw 0x136b800000000000 0x0136b80000000000 0x13e1800000000001 0x013e180000000000

def z284 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x3b807f00b800ff04 0x53b807f00b800ff0

def z285 : W := mkw 0x20000108031a1a88 0x020000108031a1a8 0x0000000047383800 0x0000000004738380

def z286 : W := mkw 0x800055000100b200 0x0800055000100b20 0x0000170000003800 0x0000017000000380

def z287 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1ffe77f800000000 0x41ffe77f80000000

def z288 : W := mkw 0x1ef6feb200000000 0x21ef6feb20000000 0x1fe67f3800000005 0xc1fe67f380000000

def z289 : W := mkw 0x5ffffefef6fea8ac 0x35ffffefef6fea8a 0xfffffffffffff8ff 0xffffffffffffff8f

def z290 : W := mkw 0x111d000010e40000 0x1111d000010e4000 0x0018000000c00000 0x00018000000c0000

def z291 : W := mkw 0x0240000024000000 0x0024000002400000 0x93e000003f000001 0x093e000003f00000

def z292 : W := mkw 0x0000000000000000 0x0000000000000000 0x401800c000c000f2 0x2401800c000c000f

def z293 : W := mkw 0x0022821202120000 0x0002282120212000 0xc4679f3f473f000f 0xac4679f3f473f000

def z294 : W := mkw 0xa0a2ff1b0b1bffca 0x0a0a2ff1b0b1bffc 0xe467ff3f473fffcf 0xee467ff3f473fffc

def z295 : W := mkw 0x4c1450a0c0a0a024 0x04c1450a0c0a0a02 0x681860c080c0c0fe 0xf681860c080c0c0f

def z296 : W := mkw 0x9febff56ed00f600 0x29febff56ed00f60 0xbfe1ff07ff00ff0d 0xdbfe1ff07ff00ff0

def z297 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe4601f00473f3fcd 0x8e4601f00473f3fc

def z298 : W := mkw 0x0022821a00080888 0x00022821a0008088 0x64679f3f403838cf 0xa64679f3f403838c

def z299 : W := mkw 0x5f5d50a8f4eca8ac 0x15f5d50a8f4eca8a 0x7f9e70f8f8f8f8fe 0xf7f9e70f8f8f8f8f

def z300 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x1ffe0000fff80000 0x11ffe0000fff8000

def z301 : W := mkw 0x9ffffff6fff6f600 0x39ffffff6fff6f60 0xffffffffffffff0f 0xfffffffffffffff0

def z302 : W := mkw 0x9ffffc00fef6e400 0x19ffffc00fef6e40 0xdfffe000ffffc00b 0xddfffe000ffffc00

def z303 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0x24661f3f47383fc4 0x224661f3f47383fc

def z304 : W := mkw 0x6c1451a9c3bbbbee 0x06c1451a9c3bbbbe 0xec1e70f8c7fffffe 0xfec1e70f8c7fffff

def z305 : W := mkw 0x3fffffff1b5f5fdb 0x23fffffff1b5f5fd 0xffffffffffffffff 0xffffffffffffffff

def z306 : W := mkw 0x9ffffff7fd45f753 0x29ffffff7fd45f75 0xffffffffffc7ffff 0xfffffffffffc7fff

def z307 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x441e10f840f838f2 0x2441e10f840f838f

def z308 : W := mkw 0x0c00500000000000 0x00c0050000000000 0x0c00700000000004 0xc0c0070000000000

def z309 : W := mkw 0x11bfaaf718454553 0x211bfaaf71845455 0xfb9fe8ffb8c7c7ff 0xffb9fe8ffb8c7c7f

def z310 : W := mkw 0x1f5d000000000000 0x01f5d00000000000 0x1b98000000000000 0x01b9800000000000

def z311 : W := mkw 0x0c947ef600000000 0x20c947ef60000000 0x0c1e7fff00000006 0xe0c1e7fff0000000

def z312 : W := mkw 0x313f82ff021b09ca 0x2313f82ff021b09c 0x401f80ff003f00c2 0x2401f80ff003f00c

def z313 : W := mkw 0x3fffab5fffff5fdb 0x13fffab5fffff5fd 0xffffffffffffffff 0xffffffffffffffff

def z314 : W := mkw 0x8e405500e500b200 0x08e405500e500b20 0x9fe01700ff003809 0x99fe01700ff00380

def z315 : W := mkw 0x3e76831be7bb1bca 0x13e76831be7bb1bc 0xe4679f3f473f3fcf 0xae4679f3f473f3fc

def z316 : W := mkw 0x1f7f8000e6b20000 0x11f7f8000e6b2000 0x1fff800047380003 0x81fff80004738000

def z317 : W := mkw 0x411d00ed10ed09ff 0x0411d00ed10ed09f 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z318 : W := mkw 0x5e76d0a8e6baa8ac 0x15e76d0a8e6baa8a 0x0466103847383800 0x0046610384738380

def z319 : W := mkw 0x00000000e6b20000 0x100000000e6b2000 0x0000000047380000 0x0000000004738000

def z320 : W := mkw 0x13eba8453e574553 0x113eba8453e57455 0xfbf9e8c7bfc7c7ff 0xffbf9e8c7bfc7c7f

def z321 : W := mkw 0x0189280018444400 0x0018928001844440 0xfb99e800b8c7c70f 0xdfb99e800b8c7c70

def z322 : W := mkw 0x0ec07ef600000000 0x20ec07ef60000000 0x1fe07fff00000005 0xe1fe07fff0000000

def z323 : W := mkw 0x6c36d2bbc2bba9ee 0x06c36d2bbc2bba9e 0x6c1ff0ffc0fff8fe 0xf6c1ff0ffc0fff8f

def z324 : W := mkw 0x1ffffef6e6b20000 0x31ffffef6e6b2000 0x1fffffff47380007 0xe1fffffff4738000

def z325 : W := mkw 0x113f800012f60000 0x1113f800012f6000 0xc47f800047ff000b 0x8c47f800047ff000

def z326 : W := mkw 0x0109000118454553 0x0010900011845455 0xfb998000b8c7c7fb 0x9fb998000b8c7c7f

def z327 : W := mkw 0x21abab5f1b5f5fdb 0x021abab5f1b5f5fd 0xf7e79f3f7f3f3fcf 0xaf7e79f3f7f3f3fc

def z328 : W := mkw 0x0000000008004400 0x0000000000800440 0xa0000000b800c708 0x1a0000000b800c70

def z329 : W := mkw 0xaee2ff1aef1afe88 0x0aee2ff1aef1afe8 0xbfe67f38ff38ff0d 0xdbfe67f38ff38ff0

def z330 : W := mkw 0x1fffae56f6f60000 0x31fffae56f6f6000 0xdfff8f07ffff000b 0x9dfff8f07ffff000

def z331 : W := mkw 0x8e400100ed00f600 0x08e400100ed00f60 0xbfe00000ff00ff09 0x9bfe00000ff00ff0

def z332 : W := mkw 0x0189284510450153 0x0018928451045015 0x5b99e8c700c700f7 0xe5b99e8c700c700f

def z333 : W := mkw 0xced47ca0eca0e424 0x0ced47ca0eca0e42 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z334 : W := mkw 0x012b800012560000 0x0012b80001256000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z335 : W := mkw 0x1fffa84518454553 0x01fffa8451845455 0xffffe8c7b8c7c7ff 0xfffffe8c7b8c7c7f

def z336 : W := mkw 0x00807c0000000000 0x000807c000000000 0x00007f0000000004 0x400007f000000000

def z337 : W := mkw 0x8240050025001200 0x0824005002500120 0x0060070007000000 0x0006007000700000

def z338 : W := mkw 0x11bfaaf600000000 0x211bfaaf60000000 0x1b9fe8ff00000007 0xe1b9fe8ff0000000

def z339 : W := mkw 0x1ef6fef600000000 0x21ef6fef60000000 0x04667fff00000004 0x604667fff0000000

def z340 : W := mkw 0xbfffffffef1bffca 0x2bfffffffef1bffc 0xffffffffff3fffcf 0xfffffffffff3fffc

def z341 : W := mkw 0x1fdd7ce518454553 0x21fdd7ce51845455 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z342 : W := mkw 0x1f7f8000c0a00000 0x01f7f8000c0a0000 0x5fff8000c0f8000b 0x95fff8000c0f8000

def z343 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x17e79f3f00000007 0xa17e79f3f0000000

def z344 : W := mkw 0x2022821b021b09ca 0x02022821b021b09c 0x6407903f403f38ce 0xa6407903f403f38c

def z345 : W := mkw 0x1f7f800002120000 0x01f7f80000212000 0xdfff8000473f000b 0x8dfff8000473f000

def z346 : W := mkw 0x0e540000e4a00000 0x00e540000e4a0000 0xdffe0000fff8000b 0x9dffe0000fff8000

def z347 : W := mkw 0x1f7f8001fef74553 0x11f7f8001fef7455 0xffff8000ffffc7fb 0x9ffff8000ffffc7f

def z348 : W := mkw 0x1f7f8008f6fe0888 0x11f7f8008f6fe088 0xffff9038ffff38cf 0xbffff9038ffff38c

def z349 : W := mkw 0x212b835f135f1bdb 0x0212b835f135f1bd 0xe47f9fff47ff3fff 0xae47f9fff47ff3ff

def z350 : W := mkw 0x6c1453bbc1a9bbee 0x06c1453bbc1a9bbe 0x6c1e7fffc0f8fffe 0xf6c1e7fffc0f8fff

def z351 : W := mkw 0x0080280008004400 0x0008028000800440 0x200068000000c704 0x4200068000000c70

def z352 : W := mkw 0x4c1450a9c0a9a9ee 0x04c1450a9c0a9a9e 0xec1ff8ffc0ffffff 0xfec1ff8ffc0fffff

def z353 : W := mkw 0x8e405500e500b200 0x08e405500e500b20 0x2c607700c700f80c 0xd2c607700c700f80

def z354 : W := mkw 0x0fc92845fc454553 0x00fc92845fc45455 0xfff9e8c7ffc7c7ff 0xffff9e8c7ffc7c7f

def z355 : W := mkw 0x113f82f612f60000 0x3113f82f612f6000 0x401f80ff00ff0002 0x2401f80ff00ff000

def z356 : W := mkw 0x4c1450a80008a8ac 0x04c1450a80008a8a 0x2c1e70f80000f8f6 0xe2c1e70f80000f8f

def z357 : W := mkw 0x13c92c4400000000 0x213c92c440000000 0x1380000000000000 0x0138000000000000

def z358 : W := mkw 0x1f7f8000f4e40000 0x11f7f8000f4e4000 0x1fff8000b8c00003 0x91fff8000b8c0000

def z359 : W := mkw 0x1262861200000000 0x2126286120000000 0x0060070000000000 0x0006007000000000

def z360 : W := mkw 0x2000031301011342 0x0200003130101134 0x00000f0700000700 0x000000f070000070

def z361 : W := mkw 0x5d3fd0a8d2fea8ac 0x15d3fd0a8d2fea8a 0x6c1ff0f8c0fff8fe 0xf6c1ff0f8c0fff8f

def z362 : W := mkw 0x800001002d005600 0x0800001002d00560 0x800000003f000700 0x0800000003f00070

def z363 : W := mkw 0x0ee2fe1200000000 0x00ee2fe120000000 0x1fe7ff3f00000007 0xe1fe7ff3f0000000

def z364 : W := mkw 0x0e40540000000000 0x00e4054000000000 0x0460170000000000 0x0046017000000000

def z365 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xfff87fc0ffc0ffff 0xffff87fc0ffc0fff

def z366 : W := mkw 0x9fdd7d00fde4f600 0x19fdd7d00fde4f60 0xbff87f00ffc0ff0d 0xdbff87f00ffc0ff0

def z367 : W := mkw 0x3fffffff01091bca 0x23fffffff01091bc 0x3fffffff00003fc7 0xe3fffffff00003fc

def z368 : W := mkw 0x9fffad00fff65600 0x19fffad00fff6560 0xdfff8f00ffff070b 0x9dfff8f00ffff070

def z369 : W := mkw 0x1fdd7ce418444411 0x21fdd7ce41844441 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z370 : W := mkw 0x9ef6ffb2ed00f600 0x29ef6ffb2ed00f60 0xbfe67f38ff00ff0d 0xdbfe67f38ff00ff0

def z371 : W := mkw 0x01abaa5718454553 0x001abaa571845455 0xffffffffb8c7c7ff 0xfffffffffb8c7c7f

def z372 : W := mkw 0x83c92d453d455753 0x083c92d453d45575 0xfbf9efc7bfc7c7ff 0xffbf9efc7bfc7c7f

def z373 : W := mkw 0x0000000012f60000 0x10000000012f6000 0x4000000000ff0000 0x04000000000ff000

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x240010004000380c 0x8240010004000380

def z375 : W := mkw 0x0000010001001200 0x0000001000100120 0x80600f0007000701 0x080600f000700070

def z376 : W := mkw 0x0189284518454553 0x0018928451845455 0xbb81e807b807c70d 0xdbb81e807b807c70

def z377 : W := mkw 0x20a2ab1b0b1b5fca 0x020a2ab1b0b1b5fc 0xffe7ff3fff3fffcf 0xfffe7ff3fff3fffc

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x440600004038000a 0x8440600004038000

def z379 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x281870f880c0f8f4 0x7281870f880c0f8f

def z380 : W := mkw 0x3f7f8109f7ff1bca 0x13f7f8109f7ff1bc 0xffff8000ffff3fcb 0x9ffff8000ffff3fc

def z381 : W := mkw 0x8ed47da0ed00f600 0x08ed47da0ed00f60 0xbffe7ff8ff00ff0f 0xfbffe7ff8ff00ff0

def z382 : W := mkw 0x2022831a031a1a88 0x02022831a031a1a8 0x04679f3f47383807 0xa04679f3f4738380

def z383 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x97e780007f3f0001 0x097e780007f3f000

def z384 : W := mkw 0x0189284518454553 0x0018928451845455 0xb381e8c73807c7f5 0x6b381e8c73807c7f

def z385 : W := mkw 0x401400a800a808ac 0x0401400a800a808a 0x0006003800380000 0x0000600380038000

def z386 : W := mkw 0x0e400000e4000000 0x00e400000e400000 0x1b800000b8000000 0x11b800000b800000

def z387 : W := mkw 0xcec07da8ed08feac 0x0cec07da8ed08fea 0xbfe07ff8ff00fffd 0xfbfe07ff8ff00fff

def z388 : W := mkw 0x0c005100c100b200 0x00c005100c100b20 0xac607f00c700ff0d 0xdac607f00c700ff0

def z389 : W := mkw 0x0080280008004400 0x0008028000800440 0x1b806000b800c000 0x51b806000b800c00

def z390 : W := mkw 0x5f5d50a0f4e4a024 0x15f5d50a0f4e4a02 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z391 : W := mkw 0x80000100ed00f600 0x080000100ed00f60 0xa4601f00ff00ff0d 0x9a4601f00ff00ff0

def z392 : W := mkw 0x0000000002120000 0x0000000000212000 0xc0000000473f0008 0x0c0000000473f000

def z393 : W := mkw 0x136b8000f6f60000 0x1136b8000f6f6000 0xd3e18000ffff0009 0x1d3e18000ffff000

def z394 : W := mkw 0x401400a8c0a8a8ac 0x0401400a8c0a8a8a 0x601e00f8c0f8f8fa 0x3601e00f8c0f8f8f

def z395 : W := mkw 0x13ffaef600000000 0x213ffaef60000000 0x13ff8fff00000003 0x213ff8fff0000000

def z396 : W := mkw 0x8e405500ed00f600 0x08e405500ed00f60 0xa4601700ff00ff08 0x1a4601700ff00ff0

def z397 : W := mkw 0x0000000800080888 0x0000000080008088 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z398 : W := mkw 0x20228109031b1bca 0x020228109031b1bc 0xe4678000473f3fcb 0x8e4678000473f3fc

def z399 : W := mkw 0xaec07f1bed09ffca 0x0aec07f1bed09ffc 0xbfe07f3fff00ffcd 0xfbfe07f3fff00ffc

def z400 : W := mkw 0x0000000100010142 0x0000000010001014 0x20000807000007c4 0x220000807000007c

def z401 : W := mkw 0x0080290009005600 0x0008029000900560 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z402 : W := mkw 0x82c02d00ed00f600 0x082c02d00ed00f60 0xb3e00f00ff00ff09 0x1b3e00f00ff00ff0

def z403 : W := mkw 0x1e76d6b2e6b20000 0x31e76d6b2e6b2000 0x0466173847380000 0x0046617384738000

def z404 : W := mkw 0x0014000000a00000 0x00014000000a0000 0x401e000000f80002 0x0401e000000f8000

def z405 : W := mkw 0x2189294d1b5f5fdb 0x02189294d1b5f5fd 0xfb99e8c7ffffffff 0xffb99e8c7fffffff

def z406 : W := mkw 0x1fdd2844fce44411 0x11fdd2844fce4441 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z407 : W := mkw 0x8fc97c44fc44e411 0x08fc97c44fc44e41 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z408 : W := mkw 0x1f7f8001f6f70142 0x11f7f8001f6f7014 0xffff8807ffff07cf 0xbffff8807ffff07c

def z409 : W := mkw 0x9f7f8100fff6f600 0x19f7f8100fff6f60 0xffff8000ffffff0b 0x9ffff8000ffffff0

def z410 : W := mkw 0x80802d0009005600 0x080802d000900560 0x00000f0000000700 0x000000f000000070

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x04601f0000000005 0x804601f000000000

def z412 : W := mkw 0x01897ef600000000 0x201897ef60000000 0x1b99ffff00000007 0xe1b99ffff0000000

def z413 : W := mkw 0x00000009000909ca 0x000000009000909c 0xe407983f403f3fcf 0xae407983f403f3fc

def z414 : W := mkw 0xcfdd7dedfdedffff 0x0cfdd7dedfdedfff 0xffffffffffffffff 0xffffffffffffffff

def z415 : W := mkw 0x0080284508014553 0x0008028450801455 0x681868c780c0c7fe 0xf681868c780c0c7f

def z416 : W := mkw 0x0189284518454553 0x0018928451845455 0xf3818807380707cf 0xaf3818807380707c

def z417 : W := mkw 0x13ebae5718454553 0x213ebae571845455 0x93e18f0738070701 0x093e18f073807070

def z418 : W := mkw 0x111d00e400000000 0x2111d00e40000000 0x001800c000000000 0x0001800c00000000

def z419 : W := mkw 0x0022800002120000 0x0002280000212000 0x8061800007070001 0x0806180000707000

def z420 : W := mkw 0xdffffda8fffefeac 0x1dffffda8fffefea 0xfffffff8ffffffff 0xffffffff8fffffff

def z421 : W := mkw 0x1f7f800036560000 0x11f7f80003656000 0x9fff80003f070003 0x89fff80003f07000

def z422 : W := mkw 0xce5455a8e5a8baac 0x0ce5455a8e5a8baa 0x0466173847383800 0x0046617384738380

def z423 : W := mkw 0x0ec02800ec004400 0x00ec02800ec00440 0xbfe06800ff00c70d 0xdbfe06800ff00c70

def z424 : W := mkw 0x1ffffef6e4000000 0x21ffffef6e400000 0x9fffffffff00000f 0xf9fffffffff00000

def z425 : W := mkw 0x9fdd7de4ed00f600 0x29fdd7de4ed00f60 0xbff87fc0ff00ff0d 0xdbff87fc0ff00ff0

def z426 : W := mkw 0x2c36d3bb031b1bca 0x02c36d3bb031b1bc 0xec7fffff473f3fcf 0xeec7fffff473f3fc

def z427 : W := mkw 0x1f7fd000f6f6a000 0x11f7fd000f6f6a00 0xfffff000fffff80f 0xdfffff000fffff80

def z428 : W := mkw 0x136b800036560000 0x1136b80003656000 0xdbf98000bfc7000b 0x9dbf98000bfc7000

def z429 : W := mkw 0xbfffff1bffffffca 0x1bfffff1bffffffc 0xffffff3fffffffcf 0xfffffff3fffffffc

def z430 : W := mkw 0xa2e2af132f135742 0x0a2e2af132f13574 0x93e18f073f070701 0x093e18f073f07070

def z431 : W := mkw 0x9ffffd00ed00f600 0x09ffffd00ed00f60 0xbfffff00ff00ff0f 0xdbfffff00ff00ff0

def z432 : W := mkw 0x313f831b13ff1bca 0x1313f831b13ff1bc 0xe47f9f3f47ff3fcf 0xae47f9f3f47ff3fc

def z433 : W := mkw 0x33ebaf5703131342 0x233ebaf570313134 0x93e18f0707070701 0x093e18f070707070

def z434 : W := mkw 0x2022831303131342 0x0202283130313134 0x84679f3f07070707 0xa84679f3f0707070

def z435 : W := mkw 0x1fdd7ce400000000 0x21fdd7ce40000000 0x1ff87fc000000005 0xc1ff87fc00000000

def z436 : W := mkw 0x0c140000c0a00000 0x00c140000c0a0000 0x6c1e60c0c0f8c0fe 0xf6c1e60c0c0f8c0f

def z437 : W := mkw 0x4c1450a0c0a0a024 0x04c1450a0c0a0a02 0x0000000000000000 0x0000000000000000

def z438 : W := mkw 0x336b831337571342 0x1336b83133757134 0x93e18f073f070701 0x093e18f073f07070

def z439 : W := mkw 0x0189284418444411 0x0018928441844441 0xdb99e0c0b8c7c03b 0xddb99e0c0b8c7c03

def z440 : W := mkw 0x1ffffefe00080888 0x21ffffefe0008088 0x7fffffff403838cf 0xe7fffffff403838c

def z441 : W := mkw 0x1e768000f6f60000 0x11e768000f6f6000 0xc4660000ffff0008 0x1c4660000ffff000

def z442 : W := mkw 0x8ec07d01ed01f742 0x08ec07d01ed01f74 0xffe1ff07ff07ffcf 0xfffe1ff07ff07ffc

def z443 : W := mkw 0x4ed47ca8c0a8a8ac 0x04ed47ca8c0a8a8a 0x7ffe7ff8c0f8f8ff 0xf7ffe7ff8c0f8f8f

def z444 : W := mkw 0x40000008c0a8a8ac 0x040000008c0a8a8a 0x0000000040383800 0x0000000004038380

def z445 : W := mkw 0x0e405000e400a000 0x00e405000e400a00 0xbfe07000ff00f80d 0xdbfe07000ff00f80

def z446 : W := mkw 0x1ffffce4f6f60000 0x31ffffce4f6f6000 0xdfffe0c0ffff000b 0xddfffe0c0ffff000

def z447 : W := mkw 0x80000101fd45f753 0x080000101fd45f75 0xe0000000ffc7fff8 0x1e0000000ffc7fff

def z448 : W := mkw 0x5e76d0a8e6baa8ac 0x15e76d0a8e6baa8a 0x6c7e70f8c7f8f8fe 0xf6c7e70f8c7f8f8f

def z449 : W := mkw 0x0e400000f6f60000 0x10e400000f6f6000 0xdfe00000ffff0009 0x9dfe00000ffff000

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00008000000070d 0x8a00008000000070

def z451 : W := mkw 0x3ffffffff7ff1bca 0x33ffffffff7ff1bc 0xffffffffffff3fcf 0xfffffffffffff3fc

def z452 : W := mkw 0x2000010901091bca 0x02000010901091bc 0x2000000000003fc0 0x02000000000003fc

def z453 : W := mkw 0x01897ef718454553 0x201897ef71845455 0xfb99ffffb8c7c7ff 0xffb99ffffb8c7c7f

def z454 : W := mkw 0x1f7f82f6f6f60000 0x31f7f82f6f6f6000 0xdfff80ffffff000b 0xbdfff80ffffff000

def z455 : W := mkw 0x1febfe5600000000 0x21febfe560000000 0x1fe1ff0700000005 0xc1fe1ff070000000

def z456 : W := mkw 0x4d1d50a8d0eca8ac 0x04d1d50a8d0eca8a 0xff9ff0f8f8fff8ff 0xfff9ff0f8f8fff8f

def z457 : W := mkw 0x400050a00000a024 0x0400050a00000a02 0x000060c00000c030 0x4000060c00000c03

def z458 : W := mkw 0x2000031b01091bca 0x02000031b01091bc 0xe0019f3f00073fcf 0xae0019f3f00073fc

def z459 : W := mkw 0x4c9478a8c8a8ecac 0x04c9478a8c8a8eca 0xff9e78f8f8f8ffff 0xfff9e78f8f8f8fff

def z460 : W := mkw 0x0022831201001200 0x0002283120100120 0xa4679f3f47003f0f 0xaa4679f3f47003f0

def z461 : W := mkw 0x0022800102130142 0x0002280010213014 0xe4678807473f07cf 0xae4678807473f07c

def z462 : W := mkw 0x113f82f710450153 0x2113f82f71045015 0x401f80ff00c700f2 0x2401f80ff00c700f

def z463 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x1fe07700ff00f800 0x51fe07700ff00f80

def z464 : W := mkw 0x0f490000f4440000 0x00f490000f444000 0xdff98000ffc7000b 0x9dff98000ffc7000

def z465 : W := mkw 0x00000000f4e40000 0x100000000f4e4000 0x00000000b8c00000 0x100000000b8c0000

def z466 : W := mkw 0x0000000118454553 0x0000000011845455 0xe81860c0b8c7c7fe 0xfe81860c0b8c7c7f

def z467 : W := mkw 0x0080280118454553 0x0008028011845455 0xfb806800b8c7c7fd 0xdfb806800b8c7c7f

def z468 : W := mkw 0x000056b200000000 0x2000056b20000000 0x0000173800000000 0x0000017380000000

def z469 : W := mkw 0x00000000c0a00000 0x000000000c0a0000 0x40000000c0f80008 0x140000000c0f8000

def z470 : W := mkw 0x0000021200000000 0x0000002120000000 0x00001f3f00000004 0x200001f3f0000000

def z471 : W := mkw 0x000050a000000000 0x0000050a00000000 0x000070f800000004 0x6000070f80000000

def z472 : W := mkw 0x0080284408004411 0x0008028440800441 0x000060c00000c030 0x4000060c00000c03

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000000080c0c0f8 0x16000000080c0c0f

def z474 : W := mkw 0x2022831303131342 0x0202283130313134 0xc4678f07473f070b 0x8c4678f07473f070

def z475 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x9bf98000bfc70001 0x19bf98000bfc7000

def z476 : W := mkw 0x6c36d3bac3babaac 0x06c36d3bac3babaa 0x0466173847383800 0x0046617384738380

def z477 : W := mkw 0x401400a800a808ac 0x0401400a800a808a 0x641e10f840f838fe 0xa641e10f840f838f

def z478 : W := mkw 0x40000008c0a8a8ac 0x040000008c0a8a8a 0x681860c0c0f8f8fe 0xf681860c0c0f8f8f

def z479 : W := mkw 0x8ec07d00fff6f600 0x18ec07d00fff6f60 0xffe07f00ffffff0d 0xdffe07f00ffffff0

def z480 : W := mkw 0x6022d3bb031bbbee 0x06022d3bb031bbbe 0xe467ffff473fffff 0xee467ffff473ffff

def z481 : W := mkw 0x1ffffc0000000000 0x01ffffc000000000 0x1fffff0000000007 0xc1fffff000000000

def z482 : W := mkw 0x603682bb02bb09ee 0x0603682bb02bb09e 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z483 : W := mkw 0x1e5454a000000000 0x21e5454a00000000 0x0000000000000000 0x0000000000000000

def z484 : W := mkw 0x0c1450a0c000a000 0x00c1450a0c000a00 0x2c1e70f8c000f80e 0xf2c1e70f8c000f80

def z485 : W := mkw 0x5d3fd2fec0a8a8ac 0x25d3fd2fec0a8a8a 0x6c1ff0ffc0f8f8fe 0xf6c1ff0ffc0f8f8f

def z486 : W := mkw 0x3e76d7bb031b1bca 0x23e76d7bb031b1bc 0xe4679f3f473f3fcf 0xae4679f3f473f3fc

def z487 : W := mkw 0x0109004510450153 0x0010900451045015 0xdb9980c7b8c700fb 0xbdb9980c7b8c700f

def z488 : W := mkw 0x1f6b8000f6560000 0x11f6b8000f656000 0x9fe18000ff070009 0x99fe18000ff07000

def z489 : W := mkw 0x9e76d500e7b2b200 0x19e76d500e7b2b20 0x0466170047383800 0x0046617004738380

def z490 : W := mkw 0x0d9d78e518454553 0x00d9d78e51845455 0xff9ff8ffb8c7c7ff 0xfff9ff8ffb8c7c7f

def z491 : W := mkw 0xdffffffeeda8feac 0x2dffffffeeda8fea 0xfffffffffff8ffff 0xffffffffffff8fff

def z492 : W := mkw 0x2ee2ff1b031b1bca 0x02ee2ff1b031b1bc 0xffe7ff3f473f3fcf 0xeffe7ff3f473f3fc

def z493 : W := mkw 0x0189284408004400 0x0018928440800440 0xbb99e8c7b800c70f 0xfbb99e8c7b800c70

def z494 : W := mkw 0x21892b5f194d5fdb 0x021892b5f194d5fd 0xfb99ffffb8c7ffff 0xffb99ffffb8c7fff

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x9b800000b8000009 0x99b800000b800000

def z496 : W := mkw 0x4d1d50edd0eda9ff 0x04d1d50edd0eda9f 0x6c1ff0ffc0fff8fe 0xf6c1ff0ffc0fff8f

def z497 : W := mkw 0x9f7fd500f7f6b200 0x19f7fd500f7f6b20 0xdfff9700ffff380b 0x9dfff9700ffff380

def z498 : W := mkw 0x01892845fef74553 0x101892845fef7455 0xfb99e8c7ffffc7ff 0xffb99e8c7ffffc7f

def z499 : W := mkw 0x6dbffbffdbffffff 0x06dbffbffdbfffff 0xffffffffffffffff 0xffffffffffffffff

def z500 : W := mkw 0x0000000118454553 0x0000000011845455 0xe0018807b8c7c7ff 0xbe0018807b8c7c7f

def z501 : W := mkw 0x1ffffef700010142 0x21ffffef70001014 0xffffffff000707cf 0xeffffffff000707c

def z502 : W := mkw 0x3ffffffe031a1a88 0x23ffffffe031a1a8 0x1fffffff47383807 0xe1fffffff4738380

def z503 : W := mkw 0x0000000800080888 0x0000000080008088 0x20001038000038c4 0x220001038000038c

def z504 : W := mkw 0x0000010001001200 0x0000001000100120 0x20001f0000003f04 0x020001f0000003f0

def z505 : W := mkw 0x8ee2ff12ed00f600 0x08ee2ff12ed00f60 0xbfe7ff3fff00ff0f 0xfbfe7ff3fff00ff0

def z506 : W := mkw 0x1ffffff601001200 0x21ffffff60100120 0xbfffffff47003f0f 0xebfffffff47003f0

def z507 : W := mkw 0x5f7f8008f6fea8ac 0x15f7f8008f6fea8a 0xffff8000fffff8fb 0x9ffff8000fffff8f

def z508 : W := mkw 0x419d28ed18ed4dff 0x0419d28ed18ed4df 0xfb9fe8ffb8ffc7ff 0xffb9fe8ffb8ffc7f

def z509 : W := mkw 0x2000031b01091bca 0x02000031b01091bc 0x64061f3f40383fce 0xa64061f3f40383fc

def z510 : W := mkw 0x5fdd7cecc0a8a8ac 0x25fdd7cecc0a8a8a 0x7f9e70f8c0f8f8fe 0xf7f9e70f8c0f8f8f

def z511 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe4061038473f3fce 0xae4061038473f3fc

def z512 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe007803f473f3fca 0x2e007803f473f3fc

def z513 : W := mkw 0x0000000800080888 0x0000000080008088 0x40060038003800c2 0x240060038003800c

def z514 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x5b9f8000b8ff0002 0x15b9f8000b8ff000

def z515 : W := mkw 0x2c22d31bc31bbbca 0x02c22d31bc31bbbc 0xec67ff3fc73fffcf 0xfec67ff3fc73fffc

def z516 : W := mkw 0x0109004510450153 0x0010900451045015 0x6819e0c780c7c0fe 0xf6819e0c780c7c0f

def z517 : W := mkw 0x0d9d78e400000000 0x00d9d78e40000000 0x1f9ff8ff00000007 0xe1f9ff8ff0000000

def z518 : W := mkw 0x0d9d2845d8e54553 0x00d9d2845d8e5455 0xff9fe8c7f8ffc7ff 0xfff9fe8c7f8ffc7f

def z519 : W := mkw 0x0c005000c000a000 0x00c005000c000a00 0x080060008000c000 0x5080060008000c00

def z520 : W := mkw 0x0000004500010153 0x0000000450001015 0x000000c7000000f0 0x2000000c7000000f

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x081860c000000006 0xe081860c00000000

def z522 : W := mkw 0x0080280000000000 0x0008028000000000 0x1b80680000000005 0xc1b8068000000000

def z523 : W := mkw 0x0189284518454553 0x0018928451845455 0xfb9860c0b8c7c7f8 0x5fb9860c0b8c7c7f

def z524 : W := mkw 0x513f80a812fe08ac 0x1513f80a812fe08a 0x401f80f800ff00f2 0x2401f80f800ff00f

def z525 : W := mkw 0x0000010801081a88 0x00000010801081a8 0xe4661f3847383fcf 0xae4661f3847383fc

def z526 : W := mkw 0x1ffffce400000000 0x21ffffce40000000 0x1fffe0c000000003 0xc1fffe0c00000000

def z527 : W := mkw 0x21abab571b575753 0x021abab571b57575 0xfbf9efc7bfc7c7ff 0xffbf9efc7bfc7c7f

def z528 : W := mkw 0x2e62831be71b1bca 0x02e62831be71b1bc 0xffe79f3fff3f3fcf 0xbffe79f3fff3f3fc

def z529 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe4661738473f3fc8 0x0e4661738473f3fc

def z530 : W := mkw 0x1e768000e6b20000 0x11e768000e6b2000 0x9fe60000ff380009 0x99fe60000ff38000

def z531 : W := mkw 0x1fdd7ef600000000 0x21fdd7ef60000000 0x1b987fff00000004 0x61b987fff0000000

def z532 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x64061038c0f8f8f8 0x164061038c0f8f8f

def z533 : W := mkw 0x3f7f8313f7f71342 0x13f7f8313f7f7134 0xdfff8f07ffff070b 0x9dfff8f07ffff070

def z534 : W := mkw 0x1fffa845fef74553 0x11fffa845fef7455 0xdfff8807ffff070b 0x9dfff8807ffff070

def z535 : W := mkw 0x0c14000000000000 0x00c1400000000000 0x0c1e000000000002 0x80c1e00000000000

def z536 : W := mkw 0x1f7f8000e4000000 0x01f7f8000e400000 0x9fff8000ff00000b 0x99fff8000ff00000

def z537 : W := mkw 0x00228000f6f60000 0x100228000f6f6000 0xc4678000ffff000b 0x9c4678000ffff000

def z538 : W := mkw 0xc0807da80908feac 0x0c0807da80908fea 0x20007ff80000fff4 0x620007ff80000fff

def z539 : W := mkw 0x0109000010440000 0x0010900001044000 0x1b980000b8c00000 0x11b980000b8c0000

def z540 : W := mkw 0x400050a80008a8ac 0x0400050a80008a8a 0x681870f880c0f8fe 0xf681870f880c0f8f

def z541 : W := mkw 0xce5455a8e5a8baac 0x0ce5455a8e5a8baa 0x6c7e77f8c7f8f8fe 0xf6c7e77f8c7f8f8f

def z542 : W := mkw 0x40000008c0a8a8ac 0x040000008c0a8a8a 0x64061038c0f8f8fe 0xb64061038c0f8f8f

def z543 : W := mkw 0x0ec07c0000000000 0x00ec07c000000000 0x1b80600000000000 0x41b8060000000000

def z544 : W := mkw 0x1fdd7ce400000000 0x21fdd7ce40000000 0x1f9e70f800000006 0xe1f9e70f80000000

def z545 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xc0678f3f073f07c3 0x2c0678f3f073f07c

def z546 : W := mkw 0x103682b200000000 0x2103682b20000000 0x0006003800000000 0x0000600380000000

def z547 : W := mkw 0x2022821b021b09ca 0x02022821b021b09c 0x44679f3f003f00c7 0xa44679f3f003f00c

def z548 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1bf9efc700000001 0x41bf9efc70000000

def z549 : W := mkw 0x80802900ed00f600 0x080802900ed00f60 0xbb806800ff00ff0d 0xdbb806800ff00ff0

def z550 : W := mkw 0x0000000108014553 0x0000000010801455 0x200000000000c7f0 0x0200000000000c7f

def z551 : W := mkw 0x80807d000900f600 0x080807d000900f60 0xa4607f004700ff0d 0xca4607f004700ff0

def z552 : W := mkw 0x4c1450a0c0a0a024 0x04c1450a0c0a0a02 0x4c1e60c0c0f8c03a 0xd4c1e60c0c0f8c03

def z553 : W := mkw 0x1262800026120000 0x1126280002612000 0x0060000007000000 0x0006000000700000

def z554 : W := mkw 0x1fffa844f6f60000 0x11fffa844f6f6000 0xdfffe8c7ffff000f 0xfdfffe8c7ffff000

def z555 : W := mkw 0xae62d71be71bbbca 0x0ae62d71be71bbbc 0xe4679f3f473f3fcf 0xae4679f3f473f3fc

def z556 : W := mkw 0x8ee2fd00ef12f600 0x08ee2fd00ef12f60 0xffe7ff00ff3fff0f 0xdffe7ff00ff3fff0

def z557 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbb806000ff00ff08 0x5bb806000ff00ff0

def z558 : W := mkw 0x0000000100010142 0x0000000010001014 0x40018007000700c2 0x240018007000700c

def z559 : W := mkw 0x00000000e4000000 0x000000000e400000 0x80000000ff000008 0x180000000ff00000

def z560 : W := mkw 0x401450a800a8a8ac 0x0401450a800a8a8a 0x601e70f800f8f8f6 0x6601e70f800f8f8f

def z561 : W := mkw 0x9fdd7c00fce4e400 0x19fdd7c00fce4e40 0x1b986000b8c0c000 0x51b986000b8c0c00

def z562 : W := mkw 0x0189284418444411 0x0018928441844441 0x7b9860c0b8c0c0fe 0xf7b9860c0b8c0c0f

def z563 : W := mkw 0x0000010101011342 0x0000001010101134 0xe4619f0747073fcf 0xae4619f0747073fc

def z564 : W := mkw 0x0189284518454553 0x0018928451845455 0x9b99e8c7b8c7c731 0x59b99e8c7b8c7c73

def z565 : W := mkw 0x5ffffefe00a808ac 0x25ffffefe00a808a 0x5fffffff00f800f7 0xe5fffffff00f800f

def z566 : W := mkw 0x0109000000000000 0x0010900000000000 0x1b99800000000003 0x81b9980000000000

def z567 : W := mkw 0x1fffae5600000000 0x21fffae560000000 0x1fff8f0700000003 0x81fff8f070000000

def z568 : W := mkw 0x5ffffeffd8ededff 0x25ffffeffd8ededf 0xfffffffff8ffffff 0xffffffffff8fffff

def z569 : W := mkw 0x0c005000c000a000 0x00c005000c000a00 0x6c1870c0c0c0f8fe 0xf6c1870c0c0c0f8f

def z570 : W := mkw 0x0022800002120000 0x0002280000212000 0x40078000003f0002 0x040078000003f000

def z571 : W := mkw 0x8fc97d44ed00f600 0x08fc97d44ed00f60 0xbff9ffc7ff00ff0f 0xfbff9ffc7ff00ff0

def z572 : W := mkw 0x1ffffef710450153 0x21ffffef71045015 0x5fffffff00c700f7 0xe5fffffff00c700f

def z573 : W := mkw 0x1349000034440000 0x1134900003444000 0x1380000038000000 0x0138000003800000

def z574 : W := mkw 0x000050000000a000 0x0000050000000a00 0x200070000000f804 0x4200070000000f80

def z575 : W := mkw 0x80000100fff6f600 0x180000100fff6f60 0xe0000000ffffff08 0x1e0000000ffffff0

def z576 : W := mkw 0x0022810003121200 0x0002281000312120 0xe4679f00473f3f0f 0x8e4679f00473f3f0

def z577 : W := mkw 0x4000000800a808ac 0x04000000800a808a 0x4000000000f800f0 0x04000000000f800f

def z578 : W := mkw 0x0c140000c0a00000 0x00c140000c0a0000 0x0818000080c00000 0x10818000080c0000

def z579 : W := mkw 0x80000000ec00e400 0x080000000ec00e40 0x00000000b800c000 0x100000000b800c00

def z580 : W := mkw 0x1ffffef708014553 0x21ffffef70801455 0x3fffffff0000c7f7 0xe3fffffff0000c7f

def z581 : W := mkw 0x0e400000e4000000 0x00e400000e400000 0x0460000047000000 0x0046000004700000

def z582 : W := mkw 0x4c36d2bac0a8a8ac 0x04c36d2bac0a8a8a 0x6c7fffffc0f8f8ff 0xf6c7fffffc0f8f8f

def z583 : W := mkw 0x0ec07d0001001200 0x00ec07d000100120 0xbfe07f0047003f0d 0xcbfe07f0047003f0

def z584 : W := mkw 0xcec07d08eda8feac 0x0cec07d08eda8fea 0xffe07f00fff8fffd 0xdffe07f00fff8fff

def z585 : W := mkw 0x1f5d0000f4e40000 0x11f5d0000f4e4000 0x9ff80000ffc00009 0x99ff80000ffc0000

def z586 : W := mkw 0x0080280008004400 0x0008028000800440 0xfb9868c0b8c0c7ff 0xffb9868c0b8c0c7f

def z587 : W := mkw 0x0c000000c0000000 0x00c000000c000000 0x0c000000c0000008 0x90c000000c000000

def z588 : W := mkw 0x20000109f7ff1bca 0x120000109f7ff1bc 0xe0000000ffff3fc8 0x1e0000000ffff3fc

def z589 : W := mkw 0x2022831a031a1a88 0x02022831a031a1a8 0xc4679738473f380b 0x8c4679738473f380

def z590 : W := mkw 0x8ec07d45ed01f753 0x08ec07d45ed01f75 0xbfe07fc7ff00fffd 0xfbfe07fc7ff00fff

def z591 : W := mkw 0x8ec07c00ec00e400 0x08ec07c00ec00e40 0xbb806800b800c70d 0xdbb806800b800c70

def z592 : W := mkw 0x113f8000f6f60000 0x1113f8000f6f6000 0xc01f8000ffff000a 0x1c01f8000ffff000

def z593 : W := mkw 0x2022831303131342 0x0202283130313134 0xe0618f07070707cf 0xae0618f07070707c

def z594 : W := mkw 0x13ebae5718454553 0x213ebae571845455 0xfbf9efc7b8c7c7ff 0xffbf9efc7b8c7c7f

def z595 : W := mkw 0x0000000010440000 0x0000000001044000 0xc0000000b8c70008 0x1c0000000b8c7000

def z596 : W := mkw 0x1e768000e6b20000 0x11e768000e6b2000 0x4c7e0000c7f8000a 0x94c7e0000c7f8000

def z597 : W := mkw 0x8ec02d00ed005600 0x08ec02d00ed00560 0x9fe00f00ff000709 0x99fe00f00ff00070

def z598 : W := mkw 0x4d9d78ecd8ececbd 0x04d9d78ecd8ececb 0x7f9e70f8f8f8f8fe 0xf7f9e70f8f8f8f8f

def z599 : W := mkw 0x0000000800080888 0x0000000080008088 0x0406103840383800 0x0040610384038380

def z600 : W := mkw 0x80807d00ed00f600 0x080807d00ed00f60 0xa0007f00ff00ff0c 0x5a0007f00ff00ff0

def z601 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x4c1e1038c0f8380a 0x94c1e1038c0f8380

def z602 : W := mkw 0x00807ef708014553 0x200807ef70801455 0x20007fff0000c7f4 0x620007fff0000c7f

def z603 : W := mkw 0x2022821b021b09ca 0x02022821b021b09c 0xe007883f003f07cf 0xae007883f003f07c

def z604 : W := mkw 0x1f7fd6b200000000 0x21f7fd6b20000000 0x1fff973800000003 0x81fff97380000000

def z605 : W := mkw 0x6c36d3bac3babaac 0x06c36d3bac3babaa 0x6c7e77f8c7f8f8fe 0xf6c7e77f8c7f8f8f

def z606 : W := mkw 0x4c36d0a8c2baa8ac 0x04c36d0a8c2baa8a 0xec7ff0f8c7fff8ff 0xfec7ff0f8c7fff8f

def z607 : W := mkw 0xa2e2af1b2f1b5fca 0x0a2e2af1b2f1b5fc 0xf7e79f3f7f3f3fcf 0xaf7e79f3f7f3f3fc

def z608 : W := mkw 0x9ffffff6e500b200 0x29ffffff6e500b20 0x1fffffff47003807 0xe1fffffff4700380

def z609 : W := mkw 0x0c1450a000000000 0x00c1450a00000000 0x081860c000000000 0x4081860c00000000

def z610 : W := mkw 0x4c005008c0a8a8ac 0x04c005008c0a8a8a 0x6c007000c0f8f8fc 0xd6c007000c0f8f8f

def z611 : W := mkw 0x1f7f800010440000 0x01f7f80001044000 0xdfff8000b8c7000b 0x9dfff8000b8c7000

def z612 : W := mkw 0x2000031b01091bca 0x02000031b01091bc 0xa4601f3f47003fcd 0xaa4601f3f47003fc

def z613 : W := mkw 0x1f5d0000f4e40000 0x11f5d0000f4e4000 0x5f9e0000f8f8000a 0x95f9e0000f8f8000

def z614 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x0c1e70f8c0f8f830 0x50c1e70f8c0f8f83

def z615 : W := mkw 0x2000031b031b1bca 0x02000031b031b1bc 0xe0001f3f473f3fcc 0x2e0001f3f473f3fc

def z616 : W := mkw 0x0000000036560000 0x1000000003656000 0x800000003f070000 0x0800000003f07000

def z617 : W := mkw 0x112b825600000000 0x2112b82560000000 0x0001800700000000 0x0000180070000000

def z618 : W := mkw 0x0189284518454553 0x0018928451845455 0xd39988c738c707f3 0x2d39988c738c707f

def z619 : W := mkw 0x0d1d0000d0e40000 0x00d1d0000d0e4000 0xdf9f8000f8ff000b 0x9df9f8000f8ff000

def z620 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x1bf9efc700000007 0xe1bf9efc70000000

def z621 : W := mkw 0x0189284500010142 0x0018928450001014 0xfb99e8c7000707cf 0xefb99e8c7000707c

def z622 : W := mkw 0x0189284400000000 0x0018928440000000 0x7b99e8c780c0c0ff 0xf7b99e8c780c0c0f

def z623 : W := mkw 0x2022831a031a1a88 0x02022831a031a1a8 0xa4661f3847383f0d 0x8a4661f3847383f0

def z624 : W := mkw 0x0080284508014553 0x0008028450801455 0xbb8068c7b800c7fd 0xfbb8068c7b800c7f

def z625 : W := mkw 0x113f804512f70153 0x1113f804512f7015 0x401f80c700ff00f2 0x2401f80c700ff00f

def z626 : W := mkw 0x0109004410440011 0x0010900441044001 0x001800c000c00030 0x0001800c000c0003

def z627 : W := mkw 0x9fdd7ce4ec00e400 0x29fdd7ce4ec00e40 0x1b9860c0b800c000 0x51b9860c0b800c00

def z628 : W := mkw 0x513f82fe00a808ac 0x2513f82fe00a808a 0x401f80ff00f800f2 0x2401f80ff00f800f

def z629 : W := mkw 0x0d897845d845e553 0x00d897845d845e55 0xff99f8c7f8c7ffff 0xfff99f8c7f8c7fff

def z630 : W := mkw 0x212b831b135f1bca 0x0212b831b135f1bc 0xffff9f3fffff3fcf 0xbffff9f3fffff3fc

def z631 : W := mkw 0xced47da8eda8feac 0x0ced47da8eda8fea 0xbfe67f38ff38ff0d 0xdbfe67f38ff38ff0

def z632 : W := mkw 0x4c1451a8c1a8baac 0x04c1451a8c1a8baa 0xec7e7ff8c7f8ffff 0xfec7e7ff8c7f8fff

def z633 : W := mkw 0x9ffffd45fff7f753 0x19ffffd45fff7f75 0xffffffc7ffffffff 0xfffffffc7fffffff

def z634 : W := mkw 0x80807ff60900f600 0x280807ff60900f60 0x20007fff0000ff04 0x620007fff0000ff0

def z635 : W := mkw 0x1ffffef7fef74553 0x31ffffef7fef7455 0xffffffffffffc7ff 0xfffffffffffffc7f

def z636 : W := mkw 0x11bfa8451af74553 0x111bfa8451af7455 0xfb9fe8c7b8ffc7ff 0xffb9fe8c7b8ffc7f

def z637 : W := mkw 0x2000031a01081a88 0x02000031a01081a8 0x0000173800003800 0x0000017380000380

def z638 : W := mkw 0x80807d000900f600 0x080807d000900f60 0xbb807f00b800ff0d 0xdbb807f00b800ff0

def z639 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1b9fe0ff00000002 0x61b9fe0ff0000000

def z640 : W := mkw 0x93ebad003f565600 0x193ebad003f56560 0x93e18f003f070701 0x093e18f003f07070

def z641 : W := mkw 0x2022831b1b5f5fdb 0x02022831b1b5f5fd 0xe4679f3fffffffff 0xbe4679f3ffffffff

def z642 : W := mkw 0x40807efe0008a8ac 0x240807efe0008a8a 0x20007fff0000f8f4 0x620007fff0000f8f

def z643 : W := mkw 0x0189284d184d4ddb 0x00189284d184d4dd 0xff9ff8fff8ffffff 0xfff9ff8fff8fffff

def z644 : W := mkw 0x4c9478edc8a9edff 0x04c9478edc8a9edf 0x6c1e78ffc0f8fffe 0xf6c1e78ffc0f8fff

def z645 : W := mkw 0x1fffa844fef64411 0x11fffa844fef6441 0xdfffe0c0ffffc03b 0xddfffe0c0ffffc03

def z646 : W := mkw 0x1f7fd0a000000000 0x01f7fd0a00000000 0x1ffff0f800000007 0xe1ffff0f80000000

def z647 : W := mkw 0x0109000010440000 0x0010900001044000 0xfb99e0c0b8c7c0ff 0xffb99e0c0b8c7c0f

def z648 : W := mkw 0x1d3fd2f600000000 0x21d3fd2f60000000 0x0c1ff0ff00000006 0xe0c1ff0ff0000000

def z649 : W := mkw 0x3e76831ae7ba1a88 0x13e76831ae7ba1a8 0x0466173847383800 0x0046617384738380

def z650 : W := mkw 0xaee2ff13ef13f742 0x0aee2ff13ef13f74 0xbfe1ff07ff07ff0d 0xdbfe1ff07ff07ff0

def z651 : W := mkw 0x8fc97c45fc45e553 0x08fc97c45fc45e55 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z652 : W := mkw 0x2022831303131342 0x0202283130313134 0xa4619f0747073f0d 0x8a4619f0747073f0

def z653 : W := mkw 0x6c36d3bbc3bbbbee 0x06c36d3bbc3bbbbe 0xe4679f3f473f3fcf 0xae4679f3f473f3fc

def z654 : W := mkw 0x7f7fd3bbf7ffbbee 0x17f7fd3bbf7ffbbe 0xffffffffffffffff 0xffffffffffffffff

def z655 : W := mkw 0x3ffffff703131342 0x23ffffff70313134 0x9fffffff07070707 0xe9fffffff0707070

def z656 : W := mkw 0x4c1450a0c0a0a024 0x04c1450a0c0a0a02 0x2c1870c0c0c0f83c 0xd2c1870c0c0c0f83

def z657 : W := mkw 0x02c02c0000000000 0x002c02c000000000 0x13e00f0000000001 0x013e00f000000000

def z658 : W := mkw 0x0109000010440000 0x0010900001044000 0x4019800000c70002 0x04019800000c7000

def z659 : W := mkw 0x4c1450a8f6fea8ac 0x14c1450a8f6fea8a 0xec1e70f8fffff8fe 0xfec1e70f8fffff8f

def z660 : W := mkw 0xced47ca8eca8ecac 0x0ced47ca8eca8eca 0x7f9e70f8f8f8f8fe 0xf7f9e70f8f8f8f8f

def z661 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x0c1e70f840383806 0xe0c1e70f84038380

def z662 : W := mkw 0x0000000118454553 0x0000000011845455 0x8000000038070700 0x0800000003807070

def z663 : W := mkw 0x5e76d6bac0a8a8ac 0x25e76d6bac0a8a8a 0x6c7e77f8c0f8f8fe 0xf6c7e77f8c0f8f8f

def z664 : W := mkw 0x0189284518454553 0x0018928451845455 0x3b9868c7b8c0c7f4 0x73b9868c7b8c0c7f

def z665 : W := mkw 0x400050a80008a8ac 0x0400050a80008a8a 0x0000103800003800 0x0000010380000380

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0x280060008000c00c 0xd280060008000c00

def z667 : W := mkw 0x8e405500e500b200 0x08e405500e500b20 0xa4601f0047003f0d 0x8a4601f0047003f0

def z668 : W := mkw 0x81892945fd45f753 0x081892945fd45f75 0xfb99e8c7ffc7ffff 0xffb99e8c7ffc7fff

def z669 : W := mkw 0x9ffffff62d005600 0x29ffffff62d00560 0x9fffffff3f000707 0xe9fffffff3f00070

def z670 : W := mkw 0x9ef6fd00efb2f600 0x19ef6fd00efb2f60 0xbfe67f00ff38ff0d 0xdbfe67f00ff38ff0

def z671 : W := mkw 0x400000080008a8ac 0x0400000080008a8a 0x200000000000f8f0 0x0200000000000f8f

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x200060c00000c0f4 0x6200060c00000c0f

def z673 : W := mkw 0x0000000100010142 0x0000000010001014 0xe819e8c780c7c7ff 0xfe819e8c780c7c7f

def z674 : W := mkw 0x313f83ff031b1bca 0x2313f83ff031b1bc 0xe47f9fff473f3fcf 0xae47f9fff473f3fc

def z675 : W := mkw 0x21abab5f031b1bca 0x021abab5f031b1bc 0xffffffff473f3fcf 0xeffffffff473f3fc

def z676 : W := mkw 0x0189284508014553 0x0018928450801455 0x3b99e8c70000c7f7 0xe3b99e8c70000c7f

def z677 : W := mkw 0x3f7f821bf6ff09ca 0x13f7f821bf6ff09c 0xdfff803fffff00cb 0xbdfff803fffff00c

def z678 : W := mkw 0x5f7f80a8f6fe08ac 0x15f7f80a8f6fe08a 0xdfff80f8ffff00fb 0xbdfff80f8ffff00f

def z679 : W := mkw 0x93ebaf562d005600 0x293ebaf562d00560 0x93e18f073f000701 0x093e18f073f00070

def z680 : W := mkw 0x5e76d6bac0a8a8ac 0x25e76d6bac0a8a8a 0x0466173840383800 0x0046617384038380

def z681 : W := mkw 0x4c1450a9d8ededff 0x04c1450a9d8ededf 0xec1e70f8f8fffffe 0xfec1e70f8f8fffff

def z682 : W := mkw 0x8ec07d000900f600 0x08ec07d000900f60 0x3fe07f000000ff05 0xc3fe07f000000ff0

def z683 : W := mkw 0x0c1450a000000000 0x00c1450a00000000 0x0406103800000000 0x0040610380000000

def z684 : W := mkw 0x400000a8000808ac 0x0400000a8000808a 0x000000f8000000f0 0x2000000f8000000f

def z685 : W := mkw 0x0ed47ca000000000 0x00ed47ca00000000 0x1ffe7ff800000007 0xe1ffe7ff80000000

def z686 : W := mkw 0x20a2ab5f0b1b5fdb 0x020a2ab5f0b1b5fd 0xe467ffff473fffff 0xee467ffff473ffff

def z687 : W := mkw 0x0109004510450153 0x0010900451045015 0x0001800700070000 0x0000180070007000

def z688 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x481e60f880f8c0f2 0x7481e60f880f8c0f

def z689 : W := mkw 0x1e76800000000000 0x01e7680000000000 0x0466000000000000 0x0046600000000000

def z690 : W := mkw 0x4189284dd8ededff 0x04189284dd8ededf 0xfb99e8c7f8ffffff 0xffb99e8c7f8fffff

def z691 : W := mkw 0x0080284518454553 0x0008028451845455 0xe00068c7b8c7c7fc 0x7e00068c7b8c7c7f

def z692 : W := mkw 0x20807fff01091bca 0x220807fff01091bc 0x20007fff00003fc4 0x620007fff00003fc

def z693 : W := mkw 0x0c140000c0a00000 0x00c140000c0a0000 0x0406000040380000 0x0040600004038000

def z694 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000000000000ce 0xa60000000000000c

def z695 : W := mkw 0x00228008021a0888 0x000228008021a088 0xe4679038473f38cf 0xae4679038473f38c

def z696 : W := mkw 0x5ffffefe0008a8ac 0x25ffffefe0008a8a 0x3fffffff0000f8f7 0xe3fffffff0000f8f

def z697 : W := mkw 0x0000010001001200 0x0000001000100120 0x0460170047003800 0x0046017004700380

def z698 : W := mkw 0x80807c000800e400 0x080807c000800e40 0x000060000000c000 0x4000060000000c00

def z699 : W := mkw 0x0e40000000000000 0x00e4000000000000 0x1fe0000000000001 0x81fe000000000000

def z700 : W := mkw 0x0189284418444411 0x0018928441844441 0xbb9868c0b8c0c73d 0xdbb9868c0b8c0c73

def z701 : W := mkw 0x5fdd7ce4c0a0a024 0x25fdd7ce4c0a0a02 0x1b9860c080c0c030 0x51b9860c080c0c03

def z702 : W := mkw 0x33ebaf5f031b1bca 0x233ebaf5f031b1bc 0xf7e79f3f473f3fcf 0xaf7e79f3f473f3fc

def z703 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x64061038403838ce 0xa64061038403838c

def z704 : W := mkw 0x4c0050a8c008a8ac 0x04c0050a8c008a8a 0x2c0070f8c000f8fc 0xf2c0070f8c000f8f

def z705 : W := mkw 0x113f800012f60000 0x1113f800012f6000 0xdb9f8000b8ff000b 0x9db9f8000b8ff000

def z706 : W := mkw 0x0c005008c008a888 0x00c005008c008a88 0x6c067038c038f8ce 0xf6c067038c038f8c

def z707 : W := mkw 0x1ef6fef6e6b20000 0x31ef6fef6e6b2000 0x04667fff47380004 0x604667fff4738000

def z708 : W := mkw 0x8ed47da0eda0f600 0x08ed47da0eda0f60 0xfffe7ff8fff8ff0f 0xffffe7ff8fff8ff0

def z709 : W := mkw 0x11abfef600000000 0x211abfef60000000 0x0001ffff00000004 0x60001ffff0000000

def z710 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe4679f3fc7ffffff 0xbe4679f3fc7fffff

def z711 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0x64679f3f473f3fc6 0x264679f3f473f3fc

def z712 : W := mkw 0x0e628000f6f60000 0x10e628000f6f6000 0xdfe78000ffff000b 0x9dfe78000ffff000

def z713 : W := mkw 0x1f7f8212f6f60000 0x11f7f8212f6f6000 0xdfff803fffff000b 0xbdfff803fffff000

def z714 : W := mkw 0x1f5d0000f6f60000 0x11f5d0000f6f6000 0xdff80000ffff0009 0x9dff80000ffff000

def z715 : W := mkw 0x21abab5e1b5e5e99 0x021abab5e1b5e5e9 0x1ffe77f8fff8f830 0x51ffe77f8fff8f83

def z716 : W := mkw 0x137f800036f60000 0x1137f800036f6000 0xd7ff80007fff000b 0x8d7ff80007fff000

def z717 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xffff8800ffff070f 0x9ffff8800ffff070

def z718 : W := mkw 0x208029090b1b5fca 0x0208029090b1b5fc 0xfb806800ff3fffcd 0xdfb806800ff3fffc

def z719 : W := mkw 0x8ec02d00ed00f600 0x08ec02d00ed00f60 0xbfe00f00ff00ff09 0x9bfe00f00ff00ff0

def z720 : W := mkw 0x1ffffef612560000 0x21ffffef61256000 0xdfffffffffff000f 0xfdfffffffffff000

def z721 : W := mkw 0x8ec07de4ed00f600 0x28ec07de4ed00f60 0xbfe07fc0ff00ff0d 0xdbfe07fc0ff00ff0

def z722 : W := mkw 0x8ed47da0ed00f600 0x08ed47da0ed00f60 0xfffe7ff8ffc0ffff 0xffffe7ff8ffc0fff

def z723 : W := mkw 0xdffffef6eca0e424 0x2dffffef6eca0e42 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z724 : W := mkw 0x0022821200000000 0x0002282120000000 0x0c7fffff00000007 0xe0c7fffff0000000

def z725 : W := mkw 0xa0807d090909ffca 0x0a0807d090909ffc 0x20007f000000ffc4 0x420007f000000ffc

def z726 : W := mkw 0x3fdd7ded031b1bca 0x23fdd7ded031b1bc 0xfb9860c0473f3fc8 0x4fb9860c0473f3fc

def z727 : W := mkw 0x1ffffef6c000a000 0x21ffffef6c000a00 0x1fffffff8000c007 0xf1fffffff8000c00

def z728 : W := mkw 0xaee2fe1bee1bedca 0x0aee2fe1bee1bedc 0x5b87e03fb83fc0c2 0x75b87e03fb83fc0c

def z729 : W := mkw 0x113f821200000000 0x0113f82120000000 0x047f9f3f00000007 0xa047f9f3f0000000

def z730 : W := mkw 0x8ed47da0ed00f600 0x08ed47da0ed00f60 0xbff87fc0ff00ff0d 0xdbff87fc0ff00ff0

def z731 : W := mkw 0x1febfe5600000000 0x21febfe560000000 0x1fe7ff3f00000007 0xe1fe7ff3f0000000

def z732 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xa4679f3f473f3fc5 0x2a4679f3f473f3fc

def z733 : W := mkw 0x000056f600000000 0x2000056f60000000 0x000017ff00000000 0x2000017ff0000000

def z734 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x04679f3f00000001 0x004679f3f0000000

def z735 : W := mkw 0xa0807f5f0909ffdb 0x0a0807f5f0909ffd 0x20007fff0000fff4 0x620007fff0000fff

def z736 : W := mkw 0x00a2fef600000000 0x200a2fef60000000 0x04667fff00000004 0x604667fff0000000

def z737 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xd7e780007f3f000b 0x8d7e780007f3f000

def z738 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbbe06f00ff00ff09 0x5bbe06f00ff00ff0

def z739 : W := mkw 0x913f83f6ed00f600 0x2913f83f6ed00f60 0xa01f80ffff00ff0a 0x3a01f80ffff00ff0

def z740 : W := mkw 0x11bffef612f60000 0x311bffef612f6000 0x401fffff00ff0006 0x6401fffff00ff000

def z741 : W := mkw 0x113f821212f60000 0x1113f821212f6000 0x447f9f3f00ff0007 0xa447f9f3f00ff000

def z742 : W := mkw 0x313f810913ff1bca 0x1313f810913ff1bc 0xe01f800047ff3fca 0x0e01f800047ff3fc

def z743 : W := mkw 0x20228109031b1bca 0x020228109031b1bc 0xe0618000473f3fc9 0x0e0618000473f3fc

def z744 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfff9038ffff000f 0xbdfff9038ffff000

def z745 : W := mkw 0x02c07ef600000000 0x202c07ef60000000 0x13e07fff00000005 0x613e07fff0000000

def z746 : W := mkw 0x012b825600000000 0x0012b82560000000 0x047f9fff00000007 0xa047f9fff0000000

def z747 : W := mkw 0x0189284518454553 0x0018928451845455 0xfff9ffc7b8c7c7ff 0xffff9ffc7b8c7c7f

def z748 : W := mkw 0x00807ef608004400 0x200807ef60800440 0xbb807fffb800c70d 0xfbb807fffb800c70

def z749 : W := mkw 0x1ffffef634440000 0x31ffffef63444000 0x1fffffff38000007 0xe1fffffff3800000

def z750 : W := mkw 0x1ffffef6e6b20000 0x31ffffef6e6b2000 0xdfffffff473f000f 0xedfffffff473f000

def z751 : W := mkw 0x1ffffef610e40000 0x31ffffef610e4000 0x1fffffff00c00007 0xe1fffffff00c0000

def z752 : W := mkw 0x6c36d3b3c3b3b366 0x06c36d3b3c3b3b36 0x8879efc787c7c731 0x58879efc787c7c73

def z753 : W := mkw 0x40000008c0a8a8ac 0x040000008c0a8a8a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z754 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0xb3e01f003f003f05 0x0b3e01f003f003f0

def z755 : W := mkw 0x112b825600000000 0x2112b82560000000 0x04679f3f00000007 0xa04679f3f0000000

def z756 : W := mkw 0x1ffffef610440000 0x21ffffef61044000 0xffffffffb8c7c0ff 0xfffffffffb8c7c0f

def z757 : W := mkw 0x60000109dbffffff 0x060000109dbfffff 0xe0000000fffffff8 0x1e0000000fffffff

def z758 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x08187fff00000006 0xe08187fff0000000

def z759 : W := mkw 0x1ffffef636f60000 0x31ffffef636f6000 0xdfffffff3fff0007 0xedfffffff3fff000

def z760 : W := mkw 0x0c22d21200000000 0x00c22d2120000000 0x0c67ff3f00000007 0xe0c67ff3f0000000

def z761 : W := mkw 0x1f7f82b2f6f60000 0x31f7f82b2f6f6000 0xdfff8038ffff000b 0x9dfff8038ffff000

def z762 : W := mkw 0x8ec07da0ed00f600 0x08ec07da0ed00f60 0xbfe07ff8ff00ff0d 0xfbfe07ff8ff00ff0

def z763 : W := mkw 0x0e400000e4000000 0x00e400000e400000 0x9fe01f00ff00000d 0x99fe01f00ff00000

def z764 : W := mkw 0x01090000f6f60000 0x101090000f6f6000 0xdb980000ffff0008 0x1db980000ffff000

def z765 : W := mkw 0x1ffffef6c0a00000 0x21ffffef6c0a0000 0x7fffffffc0f8c0ff 0xf7fffffffc0f8c0f

def z766 : W := mkw 0x0fc97ef600000000 0x20fc97ef60000000 0x1ff9ffff00000007 0xe1ff9ffff0000000

def z767 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0x1ffffffffff80007 0xf1ffffffffff8000

def z768 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0xbfffffff0000070f 0xebfffffff0000070

def z769 : W := mkw 0x1ffffef6c000a000 0x21ffffef6c000a00 0x7fffffffc0c0f8ff 0xf7fffffffc0c0f8f

def z770 : W := mkw 0x136b821200000000 0x0136b82120000000 0x17e79f3f00000007 0xa17e79f3f0000000

def z771 : W := mkw 0x1f7fd6f600000000 0x21f7fd6f60000000 0x0c7ff7ff00000006 0xe0c7ff7ff0000000

def z772 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xffff8000ffff00cf 0xbffff8000ffff00c

def z773 : W := mkw 0x00802e5600000000 0x200802e560000000 0x00001f3f00000004 0x200001f3f0000000

def z774 : W := mkw 0x11bfaef600000000 0x211bfaef60000000 0x001f8fff00000002 0x2001f8fff0000000

def z775 : W := mkw 0xc2d42da82da85eac 0x0c2d42da82da85ea 0xd3fe0ff83ff807f3 0x2d3fe0ff83ff807f

def z776 : W := mkw 0x0c807ef6c000a000 0x20c807ef6c000a00 0x2c007fffc000f80c 0xf2c007fffc000f80

def z777 : W := mkw 0x0189284518454553 0x0018928451845455 0xfb99e0c7b8c7c7fa 0x7fb99e0c7b8c7c7f

def z778 : W := mkw 0xae628109ef1bffca 0x0ae628109ef1bffc 0xffe78000ff3fffcb 0x9ffe78000ff3fffc

def z779 : W := mkw 0x0022821202120000 0x0002282120212000 0x44679f3f003f0007 0xa44679f3f003f000

def z780 : W := mkw 0x0c36d2b2c2b20000 0x00c36d2b2c2b2000 0xcc7fffffc7ff000f 0xfcc7fffffc7ff000

def z781 : W := mkw 0x1f7f82f600000000 0x21f7f82f60000000 0x1fff9fff00000007 0xa1fff9fff0000000

def z782 : W := mkw 0x2c140109c3bb1bca 0x02c140109c3bb1bc 0xec1e0000c7ff3fca 0x9ec1e0000c7ff3fc

def z783 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbfe1ff07ff00ff0f 0xfbfe1ff07ff00ff0

def z784 : W := mkw 0x00a2aa5600000000 0x000a2aa560000000 0x0467ffff00000007 0xe0467ffff0000000

def z785 : W := mkw 0x0d1d0000f6f60000 0x10d1d0000f6f6000 0xdf9f8000ffff000b 0x9df9f8000ffff000

def z786 : W := mkw 0x1ffffef602120000 0x21ffffef60212000 0x5fffffff003f0007 0xe5fffffff003f000

def z787 : W := mkw 0x2000010901091bca 0x02000010901091bc 0x6000000040383fc8 0x06000000040383fc

def z788 : W := mkw 0x1ef6a845eeb34553 0x11ef6a845eeb3455 0x246668c74738c7f4 0x6246668c74738c7f

def z789 : W := mkw 0x13ebfef600000000 0x213ebfef60000000 0x1bf9ffff00000007 0xe1bf9ffff0000000

def z790 : W := mkw 0x1f7fd6b2f6f60000 0x31f7fd6b2f6f6000 0xdfff9f3fffff000f 0xbdfff9f3fffff000

def z791 : W := mkw 0x012b821200000000 0x0012b82120000000 0x1fff9f3f00000007 0xa1fff9f3f0000000

def z792 : W := mkw 0x1262861200000000 0x2126286120000000 0x04679f3f00000007 0xa04679f3f0000000

def z793 : W := mkw 0x20000109135f1bca 0x020000109135f1bc 0xe0000000ffff3fc8 0x1e0000000ffff3fc

def z794 : W := mkw 0x136b821236560000 0x1136b82123656000 0x97e79f3f3f070007 0xa97e79f3f3f07000

def z795 : W := mkw 0x1ffffef6c0a00000 0x21ffffef6c0a0000 0x1fffffff40380007 0xe1fffffff4038000

def z796 : W := mkw 0xced47da0eda0f624 0x0ced47da0eda0f62 0xfff87fc0ffc0ffff 0xffff87fc0ffc0fff

def z797 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe0000800473f3fcd 0x8e0000800473f3fc

def z798 : W := mkw 0x103682b200000000 0x2103682b20000000 0x04679f3f00000007 0xa04679f3f0000000

def z799 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0xff9e70f8f8f8f8ff 0xfff9e70f8f8f8f8f

def z800 : W := mkw 0x8f495545f545b353 0x08f495545f545b35 0x447997c747c738f2 0x2447997c747c738f

def z801 : W := mkw 0x00807ef6f6f60000 0x300807ef6f6f6000 0xc0007fffffff000c 0x7c0007fffffff000

def z802 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x04067fff00000006 0xe04067fff0000000

def z803 : W := mkw 0x0c947ef600000000 0x20c947ef60000000 0x08187fff00000004 0x608187fff0000000

def z804 : W := mkw 0x1e768212e6b20000 0x11e768212e6b2000 0x04679f3f47380007 0xa04679f3f4738000

def z805 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0x84679f3f473f3f07 0xa84679f3f473f3f0

def z806 : W := mkw 0x1f7f8612f6f60000 0x31f7f8612f6f6000 0xdfff8700ffff000b 0x9dfff8700ffff000

def z807 : W := mkw 0x600001090109bbee 0x0600001090109bbe 0x200000000000fff0 0x0200000000000fff

def z808 : W := mkw 0x113f8000f6f60000 0x1113f8000f6f6000 0xdb9f8000ffff000b 0x9db9f8000ffff000

def z809 : W := mkw 0x82c02d00ed00f600 0x082c02d00ed00f60 0xb7e01f00ff00ff0d 0x9b7e01f00ff00ff0

def z810 : W := mkw 0xced47da0eda0f624 0x0ced47da0eda0f62 0xbffe7ff8ffc0ff3f 0xfbffe7ff8ffc0ff3

def z811 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xa4679f3f473f3f0d 0x8a4679f3f473f3f0

def z812 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x13e19f3f00000005 0x213e19f3f0000000

def z813 : W := mkw 0x1e76d6b318454553 0x21e76d6b31845455 0xe4661738b8c7c7f8 0x1e4661738b8c7c7f

def z814 : W := mkw 0x00a2fef602120000 0x200a2fef60212000 0xc467ffff473f000f 0xec467ffff473f000

def z815 : W := mkw 0x8e400100ed00f600 0x08e400100ed00f60 0xbfe01f00ff00ff0d 0x9bfe01f00ff00ff0

def z816 : W := mkw 0x312b821b125f09ca 0x1312b821b125f09c 0x4007803f003f00c2 0x24007803f003f00c

def z817 : W := mkw 0x20000109e7bb1bca 0x120000109e7bb1bc 0xe0000000473f3fc8 0x0e0000000473f3fc

def z818 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x5fffffff4038000f 0xe5fffffff4038000

def z819 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x6c1ff8ffc0f8f8ff 0xf6c1ff8ffc0f8f8f

def z820 : W := mkw 0x82c07d00ed00f600 0x082c07d00ed00f60 0xb3e07f00ff00ff0d 0x5b3e07f00ff00ff0

def z821 : W := mkw 0x200001090b1b5fdb 0x0200001090b1b5fd 0xe0000000473ffff8 0x0e0000000473ffff

def z822 : W := mkw 0x1ffffef6f4e40000 0x31ffffef6f4e4000 0xdfffffffb8c7000f 0xfdfffffffb8c7000

def z823 : W := mkw 0x0ee2fe12e6120000 0x00ee2fe12e612000 0xdfe7ff3fff3f000f 0xfdfe7ff3fff3f000

def z824 : W := mkw 0x000052b200000000 0x0000052b20000000 0x00007fff00000004 0x600007fff0000000

def z825 : W := mkw 0xaec07d09ef1bffca 0x0aec07d09ef1bffc 0xfb806000ff3fffc8 0x5fb806000ff3fffc

def z826 : W := mkw 0x0e400000e6120000 0x00e400000e612000 0xdfe00000ff3f0009 0x9dfe00000ff3f000

def z827 : W := mkw 0x1f7f8212f6f60000 0x11f7f8212f6f6000 0xdfff9738ffff000b 0x9dfff9738ffff000

def z828 : W := mkw 0x4d9d78edd8ededff 0x04d9d78edd8ededf 0x9787983f783f3f01 0x09787983f783f3f0

def z829 : W := mkw 0x00a2aa1200000000 0x000a2aa120000000 0x1fe7ff3f00000007 0xe1fe7ff3f0000000

def z830 : W := mkw 0x8e405500e500b200 0x08e405500e500b20 0xbfe01f00ff003f0d 0x9bfe01f00ff003f0

def z831 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe0000000c7fffff8 0x1e0000000c7fffff

def z832 : W := mkw 0x1ef6fef600000000 0x21ef6fef60000000 0x04661f3f00000000 0x004661f3f0000000

def z833 : W := mkw 0x1f7fd2b2f6f60000 0x11f7fd2b2f6f6000 0xdfffffffffff000f 0xfdfffffffffff000

def z834 : W := mkw 0x1ffffef610440000 0x21ffffef61044000 0x5fffffff00c70007 0xe5fffffff00c7000

def z835 : W := mkw 0x1ffffef618444411 0x21ffffef61844441 0xdfffffffb8c7c03f 0xfdfffffffb8c7c03

def z836 : W := mkw 0x1fffaa5600000000 0x01fffaa560000000 0x1fffffff00000007 0xe1fffffff0000000

def z837 : W := mkw 0x1ffffef624000000 0x21ffffef62400000 0x9fffffff3f000007 0xe9fffffff3f00000

def z838 : W := mkw 0x82c07d002d00f600 0x082c07d002d00f60 0xbbe07f00bf00ff0d 0xdbbe07f00bf00ff0

def z839 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfff8807ffff000f 0xbdfff8807ffff000

def z840 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfffe0c0ffff000f 0xfdfffe0c0ffff000

def z841 : W := mkw 0x1ffffef6c0a0a000 0x21ffffef6c0a0a00 0x7fffffffc0f8f80f 0xf7fffffffc0f8f80

def z842 : W := mkw 0x21090109135f1bca 0x021090109135f1bc 0xfb998000ffff3fcb 0x9fb998000ffff3fc

def z843 : W := mkw 0xa0000109ffffffca 0x1a0000109ffffffc 0xe0000000ffffffc8 0x1e0000000ffffffc

def z844 : W := mkw 0x82c02d00ed00f600 0x082c02d00ed00f60 0x93e00f007f003f01 0x093e00f007f003f0

def z845 : W := mkw 0x0c947ef600000000 0x20c947ef60000000 0x04067fff00000004 0x604067fff0000000

def z846 : W := mkw 0x00807ef608004400 0x200807ef60800440 0x20007fff0000c704 0x620007fff0000c70

def z847 : W := mkw 0x9ed47d00eda0f600 0x19ed47d00eda0f60 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z848 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfff9f00ffff000f 0x9dfff9f00ffff000

def z849 : W := mkw 0x1f7f82f6f6f60000 0x31f7f82f6f6f6000 0xdfff9fffffff000f 0xbdfff9fffffff000

def z850 : W := mkw 0x1f7f8212f6f60000 0x11f7f8212f6f6000 0xdfff8f07ffff000b 0x9dfff8f07ffff000

def z851 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xc4679f3f473f3fc3 0x2c4679f3f473f3fc

def z852 : W := mkw 0x0fdd7ce400000000 0x00fdd7ce40000000 0x1fffffff00000007 0xe1fffffff0000000

def z853 : W := mkw 0x0c947ef6c0a00000 0x20c947ef6c0a0000 0x4c1e7fffc0f8000e 0xf4c1e7fffc0f8000

def z854 : W := mkw 0x82c02d002d00f600 0x082c02d002d00f60 0xb3e00f003f00ff01 0x0b3e00f003f00ff0

def z855 : W := mkw 0x1ffffef6f6560000 0x31ffffef6f656000 0x9fffffffff07000f 0xf9fffffffff07000

def z856 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe4060000473f3fca 0x8e4060000473f3fc

def z857 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0x60000000003f3fc0 0x060000000003f3fc

def z858 : W := mkw 0x400050a80008a8ac 0x0400050a80008a8a 0x200060c00000f8f0 0x4200060c00000f8f

def z859 : W := mkw 0x1fffae56f6f60000 0x31fffae56f6f6000 0xdfff9f3fffff000f 0xbdfff9f3fffff000

def z860 : W := mkw 0x10b6fef600000000 0x210b6fef60000000 0x00067fff00000004 0x600067fff0000000

def z861 : W := mkw 0x00a2fef600000000 0x200a2fef60000000 0x0061ffff00000005 0x60061ffff0000000

def z862 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0xec7e70f8c7f8f8ff 0xfec7e70f8c7f8f8f

def z863 : W := mkw 0x1f7f8000e6120000 0x01f7f8000e612000 0xdfff8000ff3f000b 0x9dfff8000ff3f000

def z864 : W := mkw 0x0109000012560000 0x0010900001256000 0xdb998000ffff000b 0x9db998000ffff000

def z865 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe4679f3f473f3fc9 0x0e4679f3f473f3fc

def z866 : W := mkw 0x00802ef600000000 0x200802ef60000000 0x00000fff00000000 0x200000fff0000000

def z867 : W := mkw 0x536bd0a8365ea8ac 0x1536bd0a8365ea8a 0xb3e1f0f83f07f8f5 0x6b3e1f0f83f07f8f

def z868 : W := mkw 0x1f7f80a0f6f60000 0x11f7f80a0f6f6000 0xdfff80f8ffff000b 0xbdfff80f8ffff000

def z869 : W := mkw 0x212b821b125f09ca 0x0212b821b125f09c 0x401f803f00ff00c2 0x2401f803f00ff00c

def z870 : W := mkw 0x0000010901091bca 0x00000010901091bc 0xe4679f3f473f3fcf 0xae4679f3f473f3fc

def z871 : W := mkw 0x00807ef60000a000 0x200807ef60000a00 0x20007fff0000f804 0x620007fff0000f80

def z872 : W := mkw 0x0022821200000000 0x0002282120000000 0xc4679f3f0007000f 0xac4679f3f0007000

def z873 : W := mkw 0x0189284518454553 0x0018928451845455 0xbb99e8c7b8c7c7f5 0x7bb99e8c7b8c7c7f

def z874 : W := mkw 0x1ffffef6fce44411 0x31ffffef6fce4441 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z875 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x681e60f8c0f8f8fa 0x7681e60f8c0f8f8f

def z876 : W := mkw 0x02400000f6f60000 0x102400000f6f6000 0xd3e00000ffff0009 0x1d3e00000ffff000

def z877 : W := mkw 0x9fdd7ce4fce4e400 0x39fdd7ce4fce4e40 0x1b9860c0b8c0c000 0x51b9860c0b8c0c00

def z878 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe467ffff473fffff 0xee467ffff473ffff

def z879 : W := mkw 0x1dbffef600000000 0x21dbffef60000000 0x0c1fffff00000006 0xe0c1fffff0000000

def z880 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x5fff8000ffff0002 0x15fff8000ffff000

def z881 : W := mkw 0x613f82ff12ff09ff 0x0613f82ff12ff09f 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z882 : W := mkw 0xa3ebaf573f575753 0x0a3ebaf573f57575 0x93e18f073f070701 0x093e18f073f07070

def z883 : W := mkw 0x6c368109c3bbbbee 0x06c368109c3bbbbe 0xec7f8000c7fffffb 0x9ec7f8000c7fffff

def z884 : W := mkw 0x0022831203121200 0x0002283120312120 0xe4679f3f473f3f0f 0xae4679f3f473f3f0

def z885 : W := mkw 0x0022d6b200000000 0x20022d6b20000000 0x04679f3f00000007 0xa04679f3f0000000

def z886 : W := mkw 0x1f7fd6f6f6f60000 0x31f7fd6f6f6f6000 0xdfff97ffffff000b 0xbdfff97ffffff000

def z887 : W := mkw 0x401450a8c0a8a8ac 0x0401450a8c0a8a8a 0x601e70f8c0f8f8fe 0x7601e70f8c0f8f8f

def z888 : W := mkw 0x5ffffef6f4e4a024 0x35ffffef6f4e4a02 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z889 : W := mkw 0x53ebae5ec0a8a8ac 0x253ebae5ec0a8a8a 0x73e18f07c0f8f8f9 0x173e18f07c0f8f8f

def z890 : W := mkw 0x0022821200000000 0x0002282120000000 0x44679f3f4038000f 0xa44679f3f4038000

def z891 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x04661f3f00000004 0x204661f3f0000000

def z892 : W := mkw 0x20807fff09095fdb 0x220807fff09095fd 0x20007fff0000fff4 0x620007fff0000fff

def z893 : W := mkw 0x0f490000f6f60000 0x10f490000f6f6000 0xdff98000ffff000b 0x9dff98000ffff000

def z894 : W := mkw 0x5f7fd0a0f6f6a024 0x15f7fd0a0f6f6a02 0xfffff0c0fffff83f 0xdfffff0c0fffff83

def z895 : W := mkw 0x20000109194d5fdb 0x020000109194d5fd 0xe0000000b8c7fff8 0x1e0000000b8c7fff

def z896 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xb7e07f007f00ff05 0x4b7e07f007f00ff0

def z897 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0xec1e78f8c0f8ffff 0xfec1e78f8c0f8fff

def z898 : W := mkw 0x1ffffef618444411 0x21ffffef61844441 0x1fffffff38000007 0xe1fffffff3800000

def z899 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0x9fffffff7f3f0007 0xe9fffffff7f3f000

def z900 : W := mkw 0x4c1450a800a8a8ac 0x04c1450a800a8a8a 0x6c1e70f800f8f8f6 0xe6c1e70f800f8f8f

def z901 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x1fffffff00000007 0xe1fffffff0000000

def z902 : W := mkw 0x113f82f600000000 0x2113f82f60000000 0x007f8fff00000003 0x2007f8fff0000000

def z903 : W := mkw 0xa0802f1b09095fca 0x0a0802f1b09095fc 0x20001f3f00003fc4 0x220001f3f00003fc

def z904 : W := mkw 0x11bfaaf600000000 0x211bfaaf60000000 0x1fffffff00000007 0xe1fffffff0000000

def z905 : W := mkw 0x137f800036f60000 0x1137f800036f6000 0xdbff8000bfff000b 0x9dbff8000bfff000

def z906 : W := mkw 0x1f7fd000f6f6a000 0x11f7fd000f6f6a00 0xdfffe000ffffc00b 0xddfffe000ffffc00

def z907 : W := mkw 0x136b8000f6f60000 0x1136b8000f6f6000 0xdbf98000ffff000b 0x9dbf98000ffff000

def z908 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x6c1e70f8c0f8f8f8 0x56c1e70f8c0f8f8f

def z909 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x0001ffff00000007 0xe0001ffff0000000

def z910 : W := mkw 0x9ffffef6fce4e400 0x39ffffef6fce4e40 0x1fffffffb8c0c007 0xf1fffffffb8c0c00

def z911 : W := mkw 0x0ed47ef600000000 0x20ed47ef60000000 0x1ffe7fff00000007 0xe1ffe7fff0000000

def z912 : W := mkw 0x0ec07d0009005600 0x00ec07d000900560 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z913 : W := mkw 0x1f7fd000f6f6a000 0x11f7fd000f6f6a00 0xdfff9000ffff380b 0x9dfff9000ffff380

def z914 : W := mkw 0x0240010025001200 0x0024001002500120 0xb7e01f007f003f0d 0x8b7e01f007f003f0

def z915 : W := mkw 0x0022821200000000 0x0002282120000000 0x00079f3f00000006 0x200079f3f0000000

def z916 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xc4679f3f473f3f0b 0x8c4679f3f473f3f0

def z917 : W := mkw 0x9ed47da0ed00f600 0x29ed47da0ed00f60 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z918 : W := mkw 0x01090000f6f60000 0x101090000f6f6000 0xd3818000ffff0009 0x1d3818000ffff000

def z919 : W := mkw 0x1f7f8256f6f60000 0x31f7f8256f6f6000 0xdfff8007ffff000b 0x9dfff8007ffff000

def z920 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe4001000473f3fcc 0x8e4001000473f3fc

def z921 : W := mkw 0x1f7f8044f6f60000 0x11f7f8044f6f6000 0xdfff80c7ffff000b 0xbdfff80c7ffff000

def z922 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1fe7ff3f00000005 0xc1fe7ff3f0000000

def z923 : W := mkw 0x4c36d2b2c0a0a024 0x04c36d2b2c0a0a02 0x0c7fffff80c0c037 0xf0c7fffff80c0c03

def z924 : W := mkw 0x401450a800a8a8ac 0x0401450a800a8a8a 0x641e70f840f8f8fe 0xe641e70f840f8f8f

def z925 : W := mkw 0x4e5454a8c0a8a8ac 0x04e5454a8c0a8a8a 0x6c7e77f8c0f8f8fe 0xf6c7e77f8c0f8f8f

def z926 : W := mkw 0xbf7f8109ffffffca 0x1bf7f8109ffffffc 0xffff8000ffffffcb 0x9ffff8000ffffffc

def z927 : W := mkw 0x1fffaef600000000 0x21fffaef60000000 0x1fff8fff00000003 0xa1fff8fff0000000

def z928 : W := mkw 0x13ebaef600000000 0x213ebaef60000000 0x13e18fff00000001 0x213e18fff0000000

def z929 : W := mkw 0x8ed47da0ed00f600 0x08ed47da0ed00f60 0xbfe67f38ff00ff0d 0xdbfe67f38ff00ff0

def z930 : W := mkw 0x0c22d212c000a000 0x00c22d212c000a00 0x2c67ff3fc000f80f 0xf2c67ff3fc000f80

def z931 : W := mkw 0x012b821210440000 0x0012b82121044000 0xdfff9f3fb8c7000f 0xbdfff9f3fb8c7000

def z932 : W := mkw 0x3f5d0109f7ff1bca 0x13f5d0109f7ff1bc 0xfb980000ffff3fc8 0x1fb980000ffff3fc

def z933 : W := mkw 0x313f82ff12ff09ca 0x3313f82ff12ff09c 0x401f80ff00ff00c2 0x2401f80ff00ff00c

def z934 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x17ff9fff00000003 0x217ff9fff0000000

def z935 : W := mkw 0x1ffffef6d0e40000 0x21ffffef6d0e4000 0xdffffffff8ff000f 0xfdffffffff8ff000

def z936 : W := mkw 0xee76d7bae7babaac 0x0ee76d7bae7babaa 0x0466173847383800 0x0046617384738380

def z937 : W := mkw 0x136b800036560000 0x1136b80003656000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z938 : W := mkw 0x200001090b1b5fca 0x0200001090b1b5fc 0xe0000000ff3fffc8 0x1e0000000ff3fffc

def z939 : W := mkw 0x0ec07ef600000000 0x20ec07ef60000000 0x04607fff00000004 0x604607fff0000000

def z940 : W := mkw 0x1fffaa57fef74553 0x11fffaa57fef7455 0xffffffffffffc7ff 0xfffffffffffffc7f

def z941 : W := mkw 0x1ffffef612f60000 0x31ffffef612f6000 0xdfffffffb8ff000f 0xfdfffffffb8ff000

def z942 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1fff9f3f00000003 0x81fff9f3f0000000

def z943 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x00001f3f00000000 0x000001f3f0000000

def z944 : W := mkw 0x9ffffef6fef6e400 0x39ffffef6fef6e40 0xdfffffffffffc00f 0xfdfffffffffffc00

def z945 : W := mkw 0x1f7fd2b200000000 0x01f7fd2b20000000 0x1fffffff00000007 0xe1fffffff0000000

def z946 : W := mkw 0x20228109031b1bca 0x020228109031b1bc 0xe0078000473f3fca 0x0e0078000473f3fc

def z947 : W := mkw 0x8ec07ef6ec00e400 0x28ec07ef6ec00e40 0x1b807fffb800c004 0x71b807fffb800c00

def z948 : W := mkw 0x0189284518454553 0x0018928451845455 0xfff9e8c7ffc7c7ff 0xffff9e8c7ffc7c7f

def z949 : W := mkw 0x7e76d3bae7babaac 0x17e76d3bae7babaa 0x0466173847383800 0x0046617384738380

def z950 : W := mkw 0x4c947ef6c0a0a024 0x24c947ef6c0a0a02 0x08187fff80c0c034 0x708187fff80c0c03

def z951 : W := mkw 0x1ffffef6f6f6a000 0x31ffffef6f6f6a00 0xfffffffffffff80f 0xffffffffffffff80

def z952 : W := mkw 0x113f82f600000000 0x2113f82f60000000 0x001f9fff00000006 0x2001f9fff0000000

def z953 : W := mkw 0x1f7f80e4f6f60000 0x31f7f80e4f6f6000 0xdfff80c0ffff000b 0x9dfff80c0ffff000

def z954 : W := mkw 0x12e2fef600000000 0x212e2fef60000000 0x00607fff00000004 0x600607fff0000000

def z955 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x681e70f880f8f8f6 0x7681e70f880f8f8f

def z956 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdb9f8000ffff000a 0x1db9f8000ffff000

def z957 : W := mkw 0x60000109c1a9bbee 0x060000109c1a9bbe 0x60000000c0f8fff8 0x160000000c0f8fff

def z958 : W := mkw 0x20228109031b1bca 0x020228109031b1bc 0xe4660000473f3fc8 0x0e4660000473f3fc

def z959 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0xffffffffffffc0ff 0xfffffffffffffc0f

def z960 : W := mkw 0x1ffffef618444411 0x21ffffef61844441 0x7fffffffb8c0c0ff 0xf7fffffffb8c0c0f

def z961 : W := mkw 0x1fdd7ef600000000 0x21fdd7ef60000000 0x1b99ffff00000007 0xe1b99ffff0000000

def z962 : W := mkw 0x1e768000e6b20000 0x11e768000e6b2000 0xdfe78000ff3f000b 0x9dfe78000ff3f000

def z963 : W := mkw 0x20000109c31bbbca 0x020000109c31bbbc 0xe0000000c73fffc8 0x1e0000000c73fffc

def z964 : W := mkw 0x212b81091b5f5fdb 0x0212b81091b5f5fd 0xffff8000fffffffb 0x9ffff8000fffffff

def z965 : W := mkw 0x1f7f800036f60000 0x11f7f800036f6000 0xdfff80003fff0003 0x8dfff80003fff000

def z966 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xec67ff3fc73fffcf 0xfec67ff3fc73fffc

def z967 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xe47f9fff47ff3fff 0xae47f9fff47ff3ff

def z968 : W := mkw 0x1e76d6f600000000 0x21e76d6f60000000 0x046617ff00000000 0x2046617ff0000000

def z969 : W := mkw 0x1f7f8044f6f60011 0x11f7f8044f6f6001 0xdfff80c0ffff003b 0x9dfff80c0ffff003

def z970 : W := mkw 0x9ffffef6ec00e400 0x29ffffef6ec00e40 0x3ffffffff800f80f 0xf3ffffffff800f80

def z971 : W := mkw 0x0c1450a800080888 0x00c1450a80008088 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z972 : W := mkw 0x13ebfef600000000 0x213ebfef60000000 0x17e7ffff00000007 0xe17e7ffff0000000

def z973 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbff87fc0ff00ff0f 0xfbff87fc0ff00ff0

def z974 : W := mkw 0x1ffffef6ec004400 0x21ffffef6ec00440 0xbfffffffff00c70f 0xfbfffffffff00c70

def z975 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x9fe07f00ff00ff01 0x59fe07f00ff00ff0

def z976 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe81860c0c7fffffe 0xfe81860c0c7fffff

def z977 : W := mkw 0x1fdd7ef600000000 0x21fdd7ef60000000 0x1ff87fff00000005 0xe1ff87fff0000000

def z978 : W := mkw 0x20000109375f1bca 0x120000109375f1bc 0xe00000007f3f3fc8 0x0e00000007f3f3fc

def z979 : W := mkw 0x0022821200000000 0x0002282120000000 0x24679f3f4000380f 0xa24679f3f4000380

def z980 : W := mkw 0xa00001090909ffca 0x0a00001090909ffc 0x200000000000ffc0 0x0200000000000ffc

def z981 : W := mkw 0x01897ef600000000 0x201897ef60000000 0x1b987fff00000004 0x61b987fff0000000

def z982 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x9fffffff4700000f 0xe9fffffff4700000

def z983 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0xb3e00f007f003f09 0x0b3e00f007f003f0

def z984 : W := mkw 0x137f800036f60000 0x1137f800036f6000 0x93e780003f3f0001 0x093e780003f3f000

def z985 : W := mkw 0x136b8000f6f60000 0x1136b8000f6f6000 0x93e180007f3f0001 0x093e180007f3f000

def z986 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x9fe07f007f003f05 0xc9fe07f007f003f0

def z987 : W := mkw 0xced47da0eda0f624 0x0ced47da0eda0f62 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z988 : W := mkw 0x80802900ed00f600 0x080802900ed00f60 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z989 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1fffffff80c0c037 0xf1fffffff80c0c03

def z990 : W := mkw 0xa0000109ed09ffca 0x0a0000109ed09ffc 0xa0000000ff00ffc8 0x1a0000000ff00ffc

def z991 : W := mkw 0xa0807fff0909ffca 0x2a0807fff0909ffc 0x20007fff0000ffc4 0x620007fff0000ffc

def z992 : W := mkw 0x01897ef610440000 0x201897ef61044000 0xdb99ffffb8c7000f 0xfdb99ffffb8c7000

def z993 : W := mkw 0x1ffffef6f4e40000 0x31ffffef6f4e4000 0x5ffffffff8f8000f 0xf5ffffffff8f8000

def z994 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x17e7ffff00000005 0x617e7ffff0000000

def z995 : W := mkw 0x13ffaef600000000 0x213ffaef60000000 0x13e78f3f00000001 0x013e78f3f0000000

def z996 : W := mkw 0x8ec07d002d00f600 0x08ec07d002d00f60 0xbfe07f003f00ff05 0xcbfe07f003f00ff0

def z997 : W := mkw 0x82c02d00ed00f600 0x082c02d00ed00f60 0xbbe06f00ff00ff0d 0xdbbe06f00ff00ff0

def z998 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xffe67f00ff38ff0f 0xdffe67f00ff38ff0

def z999 : W := mkw 0x1d3fd2f600000000 0x21d3fd2f60000000 0x0c7fffff00000007 0xe0c7fffff0000000

def z1000 : W := mkw 0x01abfef600000000 0x201abfef60000000 0x1fffffff00000007 0xe1fffffff0000000

def z1001 : W := mkw 0x1f7f800012560000 0x01f7f80001256000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1002 : W := mkw 0x5ffffef6c0a0a024 0x25ffffef6c0a0a02 0x3fffffffc0c0f83f 0xf3fffffffc0c0f83

def z1003 : W := mkw 0x0c807ef600000000 0x20c807ef60000000 0x0c007fff00000004 0xe0c007fff0000000

def z1004 : W := mkw 0x1ffffef6fef64400 0x31ffffef6fef6440 0xffffffffffffc70f 0xfffffffffffffc70

def z1005 : W := mkw 0x13ebfef636560000 0x313ebfef63656000 0x93e1ffff3f070005 0x693e1ffff3f07000

def z1006 : W := mkw 0x5f7fd0a0f6f6a024 0x15f7fd0a0f6f6a02 0xdffff0f8ffffc03f 0xfdffff0f8ffffc03

def z1007 : W := mkw 0x13fffef600000000 0x213fffef60000000 0x13ffffff00000007 0x613ffffff0000000

def z1008 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x9fffffffb800000f 0xf9fffffffb800000

def z1009 : W := mkw 0x000002f600000000 0x2000002f60000000 0x00001fff00000004 0x200001fff0000000

def z1010 : W := mkw 0x1ffffef636560000 0x31ffffef63656000 0xdfffffff7f3f000f 0xedfffffff7f3f000

def z1011 : W := mkw 0x1ffffef612f60000 0x31ffffef612f6000 0xdfffffff47ff000f 0xedfffffff47ff000

def z1012 : W := mkw 0x1f7fd6f600000000 0x21f7fd6f60000000 0x0467973f00000000 0x00467973f0000000

def z1013 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1bffefff00000003 0x61bffefff0000000

def z1014 : W := mkw 0x13490000f6f60000 0x113490000f6f6000 0xd3800000ffff0008 0x1d3800000ffff000

def z1015 : W := mkw 0x1ffffe12f6f60000 0x11ffffe12f6f6000 0xdfffff3fffff000f 0xfdfffff3fffff000

def z1016 : W := mkw 0x113f821212f60000 0x1113f821212f6000 0x401f803f00ff0002 0x2401f803f00ff000

def z1017 : W := mkw 0x91bffd001bf6f600 0x191bffd001bf6f60 0x601fff0000ffff06 0x4601fff0000ffff0

def z1018 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdffe0000ffff0008 0x1dffe0000ffff000

def z1019 : W := mkw 0x5f7fd0a0f6f6a024 0x15f7fd0a0f6f6a02 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1020 : W := mkw 0x0e62821200000000 0x00e6282120000000 0x1fe79f3f00000007 0xa1fe79f3f0000000

def z1021 : W := mkw 0x119d7ef600000000 0x2119d7ef60000000 0x00187fff00000004 0x600187fff0000000

def z1022 : W := mkw 0x0e540000f6f60000 0x10e540000f6f6000 0xdffe0000ffff000b 0x9dffe0000ffff000

def z1023 : W := mkw 0x0189284518454553 0x0018928451845455 0xfb99e8c7b8c7c7f9 0x5fb99e8c7b8c7c7f

def z1024 : W := mkw 0x1ffffef6fef64411 0x31ffffef6fef6441 0xdfffffffffffc03f 0xfdfffffffffffc03

def z1025 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x0c7fffff00000007 0xe0c7fffff0000000

def z1026 : W := mkw 0x01abaa5600000000 0x001abaa560000000 0x17e79f3f00000007 0xa17e79f3f0000000

def z1027 : W := mkw 0x3f5d031bf5ed1bca 0x13f5d031bf5ed1bc 0x3b981f3fb8c03fc4 0x33b981f3fb8c03fc

def z1028 : W := mkw 0x4e5450a8e4a8a8ac 0x04e5450a8e4a8a8a 0x7f9e70f8f8f8f8fe 0xf7f9e70f8f8f8f8f

def z1029 : W := mkw 0x20802b1b09095fca 0x020802b1b09095fc 0x20007f3f0000ffc4 0x620007f3f0000ffc

def z1030 : W := mkw 0x713f82bb12ff09ee 0x1713f82bb12ff09e 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z1031 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x9fff8000ffff0001 0x19fff8000ffff000

def z1032 : W := mkw 0x1ffffef608004400 0x21ffffef60800440 0x9fffffff38000707 0xe9fffffff3800070

def z1033 : W := mkw 0x1f7fd4a0f6f60000 0x31f7fd4a0f6f6000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1034 : W := mkw 0x012b800012560000 0x0012b80001256000 0xd7e780007f3f000b 0x8d7e780007f3f000

def z1035 : W := mkw 0x11bffef600000000 0x211bffef60000000 0x047fffff00000007 0xe047fffff0000000

def z1036 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x68187fff80c0c0fe 0xf68187fff80c0c0f

def z1037 : W := mkw 0x60000109f7ffbbee 0x160000109f7ffbbe 0xe0000000fffffff8 0x1e0000000fffffff

def z1038 : W := mkw 0x80807d000900f600 0x080807d000900f60 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z1039 : W := mkw 0x0c140000c0a00000 0x00c140000c0a0000 0x4c1e1038c0f8000e 0xb4c1e1038c0f8000

def z1040 : W := mkw 0x9f7fd400f6f6a000 0x19f7fd400f6f6a00 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1041 : W := mkw 0x1ffffef602120000 0x21ffffef60212000 0x9fffffff07070007 0xe9fffffff0707000

def z1042 : W := mkw 0x2000010901091bca 0x02000010901091bc 0xa000000047003fc8 0x0a000000047003fc

def z1043 : W := mkw 0x1ffffef618444411 0x21ffffef61844441 0xbfffffffb8c0c73f 0xfbfffffffb8c0c73

def z1044 : W := mkw 0x5ffffef60000a024 0x25ffffef60000a02 0x1fffffff0000c037 0xe1fffffff0000c03

def z1045 : W := mkw 0x1f6b8000f6560000 0x11f6b8000f656000 0xdfe78000ff3f000b 0x9dfe78000ff3f000

def z1046 : W := mkw 0x13c97ef600000000 0x213c97ef60000000 0x13807fff00000004 0x613807fff0000000

def z1047 : W := mkw 0xe0807fbb0909ffee 0x0e0807fbb0909ffe 0x20007fff0000fff4 0x620007fff0000fff

def z1048 : W := mkw 0x0c140008c0a80888 0x00c140008c0a8088 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1049 : W := mkw 0x1e76d6b2e6b20000 0x31e76d6b2e6b2000 0xc4679f3f473f000f 0xac4679f3f473f000

def z1050 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0x5fffffffb8ff0007 0xf5fffffffb8ff000

def z1051 : W := mkw 0xcfdd7ce4fce4e435 0x0cfdd7ce4fce4e43 0x1b9860c0b8c0c030 0x51b9860c0b8c0c03

def z1052 : W := mkw 0x00807e1200000000 0x000807e120000000 0x00007f3f00000004 0x600007f3f0000000

def z1053 : W := mkw 0x2c005109c31bbbca 0x02c005109c31bbbc 0xec007000c73fffcc 0xdec007000c73fffc

def z1054 : W := mkw 0x8e405500ed00f600 0x08e405500ed00f60 0xbfe01700ff00ff09 0x9bfe01700ff00ff0

def z1055 : W := mkw 0x1e76821200000000 0x01e7682120000000 0x04679f3f00000007 0xa04679f3f0000000

def z1056 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0x40000000473f38c0 0x040000000473f38c

def z1057 : W := mkw 0x80807d000900f600 0x080807d000900f60 0x200060000000ff00 0x4200060000000ff0

def z1058 : W := mkw 0x1ffffef612560000 0x31ffffef61256000 0x1fffffff00070007 0xe1fffffff0007000

def z1059 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbfe67f38ff00ff0f 0xfbfe67f38ff00ff0

def z1060 : W := mkw 0x02e2ae1200000000 0x002e2ae120000000 0x17e79f3f00000007 0xa17e79f3f0000000

def z1061 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xec7f9f3fc7ff3fcf 0xbec7f9f3fc7ff3fc

def z1062 : W := mkw 0x8ec07d44ed00f600 0x08ec07d44ed00f60 0xbfe07fc7ff00ff0d 0xfbfe07fc7ff00ff0

def z1063 : W := mkw 0x313f82ff125f09db 0x2313f82ff125f09d 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z1064 : W := mkw 0x00807ef608004411 0x200807ef60800441 0x00007fff0000c034 0x600007fff0000c03

def z1065 : W := mkw 0x313f825f12ff09db 0x1313f825f12ff09d 0x401f80ff00ff00f2 0x2401f80ff00ff00f

def z1066 : W := mkw 0x1ffffef6e4a00000 0x21ffffef6e4a0000 0xdffffffffff8000f 0xfdffffffffff8000

def z1067 : W := mkw 0x13ffaef636f60000 0x313ffaef636f6000 0xd3ff8fff3fff0003 0x2d3ff8fff3fff000

def z1068 : W := mkw 0x2000010913ff1bca 0x12000010913ff1bc 0xe000000047ff3fc8 0x0e000000047ff3fc

def z1069 : W := mkw 0x00a2fe1200000000 0x000a2fe120000000 0x0467ff3f00000007 0xe0467ff3f0000000

def z1070 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdbf98000ffff0009 0x1dbf98000ffff000

def z1071 : W := mkw 0x5ffffef6c0a0a024 0x25ffffef6c0a0a02 0x1fffffff00000007 0xe1fffffff0000000

def z1072 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1bf9ffff00000005 0x61bf9ffff0000000

def z1073 : W := mkw 0x1fdd7ef600000000 0x21fdd7ef60000000 0x1f9e7fff00000006 0xe1f9e7fff0000000

def z1074 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x04607fff00000005 0xe04607fff0000000

def z1075 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x20007fff0000c0f4 0x620007fff0000c0f

def z1076 : W := mkw 0x0022821200000000 0x0002282120000000 0x04661f3f00000004 0x204661f3f0000000

def z1077 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbff87fc0ffc0ff3d 0xdbff87fc0ffc0ff3

def z1078 : W := mkw 0x0e405100e500b200 0x00e405100e500b20 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z1079 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xfff87f00ffc0ff0f 0xdfff87f00ffc0ff0

def z1080 : W := mkw 0x0d3f8000d2f60000 0x00d3f8000d2f6000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1081 : W := mkw 0x5f7fd0a0f6f6a024 0x15f7fd0a0f6f6a02 0xffffe0c0ffffc0ff 0xfffffe0c0ffffc0f

def z1082 : W := mkw 0xc0807ded0909ffff 0x0c0807ded0909fff 0x20007fff0000fff4 0x620007fff0000fff

def z1083 : W := mkw 0x0c36821200000000 0x00c3682120000000 0x0c7f9f3f00000007 0xa0c7f9f3f0000000

def z1084 : W := mkw 0x0c807900c900f600 0x00c807900c900f60 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z1085 : W := mkw 0x0ec07e1200000000 0x00ec07e120000000 0x1fe07f3f00000005 0xe1fe07f3f0000000

def z1086 : W := mkw 0x8ed47d00eda0f600 0x08ed47d00eda0f60 0xfffe7fc0fff8ffff 0xffffe7fc0fff8fff

def z1087 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x4c1e70f8c0f8f8f2 0x74c1e70f8c0f8f8f

def z1088 : W := mkw 0x1ffffef6e400a000 0x21ffffef6e400a00 0xbfffffffff00f80f 0xfbfffffffff00f80

def z1089 : W := mkw 0x136b8000f6f60000 0x1136b8000f6f6000 0xd7e78000ffff000b 0x9d7e78000ffff000

def z1090 : W := mkw 0x20000109ffff5fdb 0x120000109ffff5fd 0xe0000000fffffff8 0x1e0000000fffffff

def z1091 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x6c7e7ff8c0f8f8ff 0xf6c7e7ff8c0f8f8f

def z1092 : W := mkw 0x00a2aa1208004400 0x000a2aa120800440 0xbfe7ff3fb800c70f 0xfbfe7ff3fb800c70

def z1093 : W := mkw 0x01abaa5612560000 0x001abaa561256000 0xdfffffffffff000f 0xfdfffffffffff000

def z1094 : W := mkw 0x137f86f600000000 0x2137f86f60000000 0x007f87ff00000002 0x2007f87ff0000000

def z1095 : W := mkw 0x1f7f8212f4e40000 0x11f7f8212f4e4000 0x1fff9f3fb8c00007 0xb1fff9f3fb8c0000

def z1096 : W := mkw 0x0022821200000000 0x0002282120000000 0x00678f3f00000003 0x200678f3f0000000

def z1097 : W := mkw 0x1ffffef6e4000000 0x21ffffef6e400000 0x1fffffff47000007 0xe1fffffff4700000

def z1098 : W := mkw 0x1f7fd400f6f60000 0x11f7fd400f6f6000 0xdfff9700ffff000b 0x9dfff9700ffff000

def z1099 : W := mkw 0x5ffffef600a00024 0x25ffffef600a0002 0x1fffffff00c00037 0xe1fffffff00c0003

def z1100 : W := mkw 0x0ec07ef6e4000000 0x20ec07ef6e400000 0x9fe07fffff00000d 0xf9fe07fffff00000

def z1101 : W := mkw 0x9ffffef6ec00e400 0x29ffffef6ec00e40 0x9fffffffff00c00f 0xf9fffffffff00c00

def z1102 : W := mkw 0x1ffffef608004400 0x21ffffef60800440 0xffffffffb8c0c7ff 0xfffffffffb8c0c7f

def z1103 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x641e70f840f8f8f6 0x6641e70f840f8f8f

def z1104 : W := mkw 0x1ed47ef600000000 0x21ed47ef60000000 0x00007fff00000004 0x600007fff0000000

def z1105 : W := mkw 0x1ffffef626120000 0x31ffffef62612000 0x1fffffff07000007 0xe1fffffff0700000

def z1106 : W := mkw 0x00807ef600000000 0x200807ef60000000 0x1b807fff00000005 0xe1b807fff0000000

def z1107 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xa000000007073fc0 0x0a000000007073fc

def z1108 : W := mkw 0x00802a5600000000 0x000802a560000000 0x00007fff00000004 0x600007fff0000000

def z1109 : W := mkw 0x8ec07d44ed00f611 0x08ec07d44ed00f61 0xbfe07fc0ff00ff3d 0xdbfe07fc0ff00ff3

def z1110 : W := mkw 0x136b800036560000 0x1136b80003656000 0x97e780007f3f0001 0x097e780007f3f000

def z1111 : W := mkw 0x1ef6fef600000000 0x21ef6fef60000000 0x0c7e7fff00000006 0xe0c7e7fff0000000

def z1112 : W := mkw 0x1f5d0000f6f60000 0x11f5d0000f6f6000 0xdb998000ffff000b 0x9db998000ffff000

def z1113 : W := mkw 0x200001091b5f5fdb 0x0200001091b5f5fd 0xe00000007f3f3fc8 0x0e00000007f3f3fc

def z1114 : W := mkw 0xa00001090b1bffca 0x0a00001090b1bffc 0xe0000000473fffc8 0x0e0000000473fffc

def z1115 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xffe1ff00ff07ff0f 0xdffe1ff00ff07ff0

def z1116 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xffff8000ffffc0fb 0x9ffff8000ffffc0f

def z1117 : W := mkw 0x1ffffef6e4000000 0x21ffffef6e400000 0x1fffffffb8000007 0xf1fffffffb800000

def z1118 : W := mkw 0x33ebaf571b575753 0x233ebaf571b57575 0x93e18f073f070701 0x093e18f073f07070

def z1119 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0x5fffffff47ff0007 0xe5fffffff47ff000

def z1120 : W := mkw 0x1ffffef6c0a00000 0x21ffffef6c0a0000 0x1fffffff80c00007 0xf1fffffff80c0000

def z1121 : W := mkw 0x137f8000f6f60000 0x1137f8000f6f6000 0xd3ff8000ffff000b 0x1d3ff8000ffff000

def z1122 : W := mkw 0x1f7fd6f6f6f60000 0x31f7fd6f6f6f6000 0x447f97ff47ff0002 0x2447f97ff47ff000

def z1123 : W := mkw 0x1f7fd000f6f60000 0x11f7fd000f6f6000 0xdffff000ffff000f 0xddffff000ffff000

def z1124 : W := mkw 0x1f7f8000f6f6a000 0x11f7f8000f6f6a00 0xffff8000fffff80b 0x9ffff8000fffff80

def z1125 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1ffff7ff00000002 0x61ffff7ff0000000

def z1126 : W := mkw 0x0ec07d00e5001200 0x00ec07d00e500120 0xbfe07f00ff003f0d 0xdbfe07f00ff003f0

def z1127 : W := mkw 0x1fffae5600000000 0x21fffae560000000 0x1fff9f3f00000007 0xa1fff9f3f0000000

def z1128 : W := mkw 0x8ed47d00ed00f600 0x08ed47d00ed00f60 0xbffe7f00ff00ff0f 0xdbffe7f00ff00ff0

def z1129 : W := mkw 0x8ec07d002d005600 0x08ec07d002d00560 0xbfe07f007f003f0d 0xcbfe07f007f003f0

def z1130 : W := mkw 0x0000021200000000 0x0000002120000000 0x04061f3f00000006 0xa04061f3f0000000

def z1131 : W := mkw 0x1f6b8000f6f60000 0x11f6b8000f6f6000 0xdfe18000ffff0009 0x9dfe18000ffff000

def z1132 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbfe07fc0ff00fffd 0xfbfe07fc0ff00fff

def z1133 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xffe07f00ff00ffcf 0xfffe07f00ff00ffc

def z1134 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x5fffffff80c0000f 0xf5fffffff80c0000

def z1135 : W := mkw 0x2000010909095fdb 0x02000010909095fd 0x200000000000fff0 0x0200000000000fff

def z1136 : W := mkw 0x0c005008c008a888 0x00c005008c008a88 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1137 : W := mkw 0x80807ef60800e400 0x280807ef60800e40 0x00007fff0000c004 0x600007fff0000c00

def z1138 : W := mkw 0x2189294d1b5f5fdb 0x02189294d1b5f5fd 0xfb9860c0fffffff8 0x5fb9860c0fffffff

def z1139 : W := mkw 0x00228212f6f60000 0x100228212f6f6000 0xc4679f3fffff000f 0xbc4679f3fffff000

def z1140 : W := mkw 0x0189284518454553 0x0018928451845455 0xff99f8c7f8c7ffff 0xfff99f8c7f8c7fff

def z1141 : W := mkw 0x136b800036560000 0x1136b80003656000 0xd3e180007f3f0009 0x0d3e180007f3f000

def z1142 : W := mkw 0x1f7fd0a0f6f60000 0x11f7fd0a0f6f6000 0xdfff9038ffff000b 0x9dfff9038ffff000

def z1143 : W := mkw 0x1ef6fef600000000 0x21ef6fef60000000 0x1fe67fff00000005 0xe1fe67fff0000000

def z1144 : W := mkw 0x1f7fd6b200000000 0x21f7fd6b20000000 0x1fff9f3f00000007 0xa1fff9f3f0000000

def z1145 : W := mkw 0x0e62d61200000000 0x00e62d6120000000 0x04679f3f00000007 0xa04679f3f0000000

def z1146 : W := mkw 0x01892a5600000000 0x001892a560000000 0x1b99ffff00000007 0xe1b99ffff0000000

def z1147 : W := mkw 0x00000000f6f60000 0x100000000f6f6000 0xdb800000ffff0009 0x9db800000ffff000

def z1148 : W := mkw 0x1ffffef6e6120000 0x21ffffef6e612000 0xdfffffffff3f000f 0xfdfffffffff3f000

def z1149 : W := mkw 0x1f7fd000f6f6a000 0x11f7fd000f6f6a00 0xfffff0c0fffff8ff 0xffffff0c0fffff8f

def z1150 : W := mkw 0x401400a8c0a8a8ac 0x0401400a8c0a8a8a 0x681e60f8c0f8f8fe 0xf681e60f8c0f8f8f

def z1151 : W := mkw 0x0c36d2b200000000 0x00c36d2b20000000 0x04679f3f00000007 0xa04679f3f0000000

def z1152 : W := mkw 0x6000010903bb1bee 0x06000010903bb1be 0xe000000047ff3ff8 0x0e000000047ff3ff

def z1153 : W := mkw 0x1f7fd6f600000000 0x21f7fd6f60000000 0x1fff97ff00000003 0xa1fff97ff0000000

def z1154 : W := mkw 0x1ffffef610440011 0x21ffffef61044001 0x1fffffff00c00037 0xe1fffffff00c0003

def z1155 : W := mkw 0x00a2ae5600000000 0x200a2ae560000000 0x04679f3f00000007 0xa04679f3f0000000

def z1156 : W := mkw 0x5e5454a8c0a8a8ac 0x25e5454a8c0a8a8a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1157 : W := mkw 0x1fdd7ef6f4e40000 0x31fdd7ef6f4e4000 0x1b987fffb8c00004 0x71b987fffb8c0000

def z1158 : W := mkw 0x0109000010440000 0x0010900001044000 0xdb998807b8c7000f 0xbdb998807b8c7000

def z1159 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfffe0c0ffffc03b 0xddfffe0c0ffffc03

def z1160 : W := mkw 0x0022821200000000 0x0002282120000000 0xa4679f3f0000070f 0xaa4679f3f0000070

def z1161 : W := mkw 0x0022821200000000 0x0002282120000000 0x0467973f00000002 0x20467973f0000000

def z1162 : W := mkw 0x1f7fd6b2f6f60000 0x31f7fd6b2f6f6000 0xdffff7f8ffff000f 0xfdffff7f8ffff000

def z1163 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1b9fffff00000006 0x61b9fffff0000000

def z1164 : W := mkw 0x4e5450a8e4a8a8ac 0x04e5450a8e4a8a8a 0x6c7e70f8c7f8f8fe 0xf6c7e70f8c7f8f8f

def z1165 : W := mkw 0x01897ef600000000 0x201897ef60000000 0x0019ffff00000006 0x60019ffff0000000

def z1166 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xb7e01f007f003f0d 0x8b7e01f007f003f0

def z1167 : W := mkw 0xa00001092f1b5fca 0x0a00001092f1b5fc 0xe00000007f3f3fc8 0x0e00000007f3f3fc

def z1168 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xd7ff80007fff0003 0x0d7ff80007fff000

def z1169 : W := mkw 0x9ffffef60800e400 0x29ffffef60800e40 0x1fffffff0000c007 0xe1fffffff0000c00

def z1170 : W := mkw 0x0022821200000000 0x0002282120000000 0x00619f3f00000005 0x200619f3f0000000

def z1171 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0x80000000473f3f00 0x080000000473f3f0

def z1172 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1ffe7fff00000004 0x61ffe7fff0000000

def z1173 : W := mkw 0x0c368212c0a00000 0x00c368212c0a0000 0x4c7f9f3fc0f8000f 0xb4c7f9f3fc0f8000

def z1174 : W := mkw 0x0022821202120000 0x0002282120212000 0x84679f3f07070007 0xa84679f3f0707000

def z1175 : W := mkw 0x8ee2fe12ec00e400 0x08ee2fe12ec00e40 0x1fe7ff3fb800c007 0xf1fe7ff3fb800c00

def z1176 : W := mkw 0x1f7fd2f6f6f60000 0x31f7fd2f6f6f6000 0xdffff0ffffff000f 0xfdffff0ffffff000

def z1177 : W := mkw 0x0022800002120000 0x0002280000212000 0xdfe78000ff3f000b 0x9dfe78000ff3f000

def z1178 : W := mkw 0x0022821200000000 0x0002282120000000 0x04679f3f00000001 0x004679f3f0000000

def z1179 : W := mkw 0x60000109031bbbee 0x060000109031bbbe 0xe0000000473ffff8 0x0e0000000473ffff

def z1180 : W := mkw 0x5ffffef6c0a0a024 0x25ffffef6c0a0a02 0x5fffffffc0f8c03f 0xf5fffffffc0f8c03

def z1181 : W := mkw 0x0ef6feb200000000 0x00ef6feb20000000 0x1fffffff00000007 0xe1fffffff0000000

def z1182 : W := mkw 0x1ffffef6e6b20000 0x31ffffef6e6b2000 0x9fffffffff38000f 0xf9fffffffff38000

def z1183 : W := mkw 0x40807ef60000a024 0x240807ef60000a02 0x00007fff0000c034 0x600007fff0000c03

def z1184 : W := mkw 0x1e76d6b200000000 0x21e76d6b20000000 0x0467973f00000002 0x20467973f0000000

def z1185 : W := mkw 0x33ebab573f575753 0x133ebab573f57575 0x93e18f073f070701 0x093e18f073f07070

def z1186 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0x97e01f007f003f01 0x097e01f007f003f0

def z1187 : W := mkw 0x113fd6f600000000 0x2113fd6f60000000 0x001f97ff00000002 0x2001f97ff0000000

def z1188 : W := mkw 0x0022821202120000 0x0002282120212000 0x04679f3f47380007 0xa04679f3f4738000

def z1189 : W := mkw 0xa0000109e71bbbca 0x0a0000109e71bbbc 0xe0000000473f3fc8 0x0e0000000473f3fc

def z1190 : W := mkw 0x5ffffef6c0a0a024 0x25ffffef6c0a0a02 0x7fffffff80c0c0ff 0xf7fffffff80c0c0f

def z1191 : W := mkw 0x1ffffef602120000 0x21ffffef60212000 0x1fffffff47380007 0xe1fffffff4738000

def z1192 : W := mkw 0x0109000110450142 0x0010900011045014 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z1193 : W := mkw 0x0022d2b200000000 0x00022d2b20000000 0x0467ffff00000007 0xe0467ffff0000000

def z1194 : W := mkw 0x13ebfef600000000 0x213ebfef60000000 0x13e19f3f00000001 0x013e19f3f0000000

def z1195 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xec7fffff473f3fcf 0xeec7fffff473f3fc

def z1196 : W := mkw 0x012b8000f6f60000 0x1012b8000f6f6000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1197 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x3fffffff4000380f 0xe3fffffff4000380

def z1198 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbfe07700ff00ff08 0x5bfe07700ff00ff0

def z1199 : W := mkw 0x1e768212e6b20000 0x11e768212e6b2000 0x0466173847380000 0x0046617384738000

def z1200 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0x2c1e70f8c0f8f8f4 0x72c1e70f8c0f8f8f

def z1201 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0x97e79f3f7f3f0001 0x097e79f3f7f3f000

def z1202 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x5fffffff00c000f7 0xe5fffffff00c000f

def z1203 : W := mkw 0x01897ef600000000 0x201897ef60000000 0x1381ffff00000005 0x61381ffff0000000

def z1204 : W := mkw 0x0c1452b200000000 0x00c1452b20000000 0x0c1e7fff00000006 0xe0c1e7fff0000000

def z1205 : W := mkw 0x1f5d0000f6f60000 0x11f5d0000f6f6000 0xdf9e0000ffff000a 0x9df9e0000ffff000

def z1206 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x1fffffff00000001 0x41fffffff0000000

def z1207 : W := mkw 0x0ec02900ed005600 0x00ec02900ed00560 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z1208 : W := mkw 0x60000109c3bbbbee 0x060000109c3bbbbe 0xe0000000473f3fc8 0x0e0000000473f3fc

def z1209 : W := mkw 0x8ec07d00eda0f600 0x08ec07d00eda0f60 0xffe07f00fff8ff0d 0xdffe07f00fff8ff0

def z1210 : W := mkw 0xcec07d00eda0f624 0x0cec07d00eda0f62 0xbfe07f00ffc0ff3d 0xdbfe07f00ffc0ff3

def z1211 : W := mkw 0x1f7fd0a0f6f60000 0x11f7fd0a0f6f6000 0xdfffe0c0ffff000b 0xddfffe0c0ffff000

def z1212 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x9fff80007f3f0003 0x89fff80007f3f000

def z1213 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xbbe07f00bf00ff05 0x5bbe07f00bf00ff0

def z1214 : W := mkw 0x0022821200000000 0x0002282120000000 0x64679f3f000000cf 0xa64679f3f000000c

def z1215 : W := mkw 0x0e768000e6b20000 0x00e768000e6b2000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1216 : W := mkw 0x0000021200000000 0x0000002120000000 0x00019f3f00000007 0xa00019f3f0000000

def z1217 : W := mkw 0x9fffff12fff6f600 0x19fffff12fff6f60 0xffffff3fffffff0f 0xfffffff3fffffff0

def z1218 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xffe07f00ffc0fffd 0xdffe07f00ffc0fff

def z1219 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x047fffff00000006 0x6047fffff0000000

def z1220 : W := mkw 0x3f7f8109ffff5fdb 0x13f7f8109ffff5fd 0xffff8000fffffffb 0x9ffff8000fffffff

def z1221 : W := mkw 0x1ffffef6f4e40000 0x31ffffef6f4e4000 0x9fffffffffc0000f 0xf9fffffffffc0000

def z1222 : W := mkw 0x9ffffef62c004400 0x29ffffef62c00440 0x1fffffff38000007 0xe1fffffff3800000

def z1223 : W := mkw 0x5e5450a8e4a8a8ac 0x15e5450a8e4a8a8a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1224 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x3fffffff8000c00f 0xf3fffffff8000c00

def z1225 : W := mkw 0x400050a80008a8ac 0x0400050a80008a8a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1226 : W := mkw 0x1fffaa56f6f60000 0x11fffaa56f6f6000 0xdfffffffffff000f 0xfdfffffffffff000

def z1227 : W := mkw 0x0febfe5600000000 0x00febfe560000000 0x1fffffff00000007 0xe1fffffff0000000

def z1228 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0xb7e01f00ff00ff09 0x1b7e01f00ff00ff0

def z1229 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdbff8000bfff0003 0x1dbff8000bfff000

def z1230 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0xdfffffff0007000f 0xedfffffff0007000

def z1231 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x9fe01f00ff003f09 0x99fe01f00ff003f0

def z1232 : W := mkw 0x0dbffaf600000000 0x00dbffaf60000000 0x1fffffff00000007 0xe1fffffff0000000

def z1233 : W := mkw 0x0189284518454553 0x0018928451845455 0xdb99e8c7b8c7c7f3 0x7db99e8c7b8c7c7f

def z1234 : W := mkw 0x01897ef618444411 0x201897ef61844441 0x1b987fffb8c0c034 0x71b987fffb8c0c03

def z1235 : W := mkw 0x2080294d09095fdb 0x02080294d09095fd 0x200068c70000fff4 0x6200068c70000fff

def z1236 : W := mkw 0x1e768000f6f60000 0x11e768000f6f6000 0xdfe60000ffff0009 0x9dfe60000ffff000

def z1237 : W := mkw 0x0189284518454553 0x0018928451845455 0xff9fe8c7f8ffc7ff 0xfff9fe8c7f8ffc7f

def z1238 : W := mkw 0x60807bff0909ffff 0x060807bff0909fff 0x20007fff0000fff4 0x620007fff0000fff

def z1239 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0x2000000047383fc0 0x02000000047383fc

def z1240 : W := mkw 0x4c1450a8e4a8a8ac 0x04c1450a8e4a8a8a 0xec1e70f8fff8f8fe 0xfec1e70f8fff8f8f

def z1241 : W := mkw 0x0189284518454553 0x0018928451845455 0x7b99e8c7b8c7c7f6 0x77b99e8c7b8c7c7f

def z1242 : W := mkw 0x336b8109375f1bca 0x1336b8109375f1bc 0xf3e180007f3f3fc9 0x0f3e180007f3f3fc

def z1243 : W := mkw 0x8ed47d00eda0f600 0x08ed47d00eda0f60 0xbfe67f00ff38ff0d 0xdbfe67f00ff38ff0

def z1244 : W := mkw 0x13ffaef600000000 0x213ffaef60000000 0x1bffefff00000007 0xe1bffefff0000000

def z1245 : W := mkw 0x5ffffef6f6f6a024 0x35ffffef6f6f6a02 0xdfffffffffffc03f 0xfdfffffffffffc03

def z1246 : W := mkw 0x1ffffef610440000 0x21ffffef61044000 0x1fffffffb8c00007 0xf1fffffffb8c0000

def z1247 : W := mkw 0x9ffffef6e400a000 0x29ffffef6e400a00 0x1fffffff00000007 0xe1fffffff0000000

def z1248 : W := mkw 0x1ffffef608004400 0x21ffffef60800440 0x3fffffff0000c707 0xe3fffffff0000c70

def z1249 : W := mkw 0x1ffffef6c2b20000 0x21ffffef6c2b2000 0xdfffffffc7ff000f 0xfdfffffffc7ff000

def z1250 : W := mkw 0xa0000109ff5fffdb 0x0a0000109ff5fffd 0xe0000000fffffff8 0x1e0000000fffffff

def z1251 : W := mkw 0x1ffffef600a00000 0x21ffffef600a0000 0x5fffffff00f80007 0xe5fffffff00f8000

def z1252 : W := mkw 0x00a2fef600000000 0x200a2fef60000000 0x0007ffff00000006 0x60007ffff0000000

def z1253 : W := mkw 0x1f7fd6f600000000 0x21f7fd6f60000000 0x047f9fff00000007 0xa047f9fff0000000

def z1254 : W := mkw 0x0cb6fef600000000 0x20cb6fef60000000 0x0c7fffff00000007 0xe0c7fffff0000000

def z1255 : W := mkw 0x0080284508014553 0x0008028450801455 0x200060c00000c7f0 0x4200060c00000c7f

def z1256 : W := mkw 0x82c07d002d00f600 0x082c07d002d00f60 0xb7e07f007f00ff0d 0xcb7e07f007f00ff0

def z1257 : W := mkw 0x1ffffef6c800e400 0x21ffffef6c800e40 0xbffffffff800ff0f 0xfbffffffff800ff0

def z1258 : W := mkw 0x1ffffe1200000000 0x01ffffe120000000 0x1fffff3f00000007 0xe1fffff3f0000000

def z1259 : W := mkw 0x5f7f8000f6f6a024 0x15f7f8000f6f6a02 0xdfff8000ffffc03b 0x9dfff8000ffffc03

def z1260 : W := mkw 0x0022821200000000 0x0002282120000000 0x84679f3f4700000f 0xa84679f3f4700000

def z1261 : W := mkw 0x13ffaef600000000 0x213ffaef60000000 0x17ff9fff00000007 0xa17ff9fff0000000

def z1262 : W := mkw 0x000056b200000000 0x2000056b20000000 0x00001f3f00000004 0x200001f3f0000000

def z1263 : W := mkw 0x0ec07ef600000000 0x20ec07ef60000000 0x1b807fff00000004 0x61b807fff0000000

def z1264 : W := mkw 0x1ffffef6d2f60000 0x31ffffef6d2f6000 0x5fffffffc0ff000f 0xf5fffffffc0ff000

def z1265 : W := mkw 0x9ffffef6ec00e400 0x29ffffef6ec00e40 0xbfffffffb800c70f 0xfbfffffffb800c70

def z1266 : W := mkw 0x1ffffef60000a000 0x21ffffef60000a00 0x3fffffff0000f807 0xe3fffffff0000f80

def z1267 : W := mkw 0x0080280108014542 0x0008028010801454 0xfb99e8c7b8c7c7ff 0xffb99e8c7b8c7c7f

def z1268 : W := mkw 0x1ffffef6e4a00000 0x31ffffef6e4a0000 0x1fffffff00000007 0xe1fffffff0000000

def z1269 : W := mkw 0x002282f600000000 0x2002282f60000000 0x04679fff00000007 0xa04679fff0000000

def z1270 : W := mkw 0x1ffffef608004411 0x21ffffef60800441 0x1fffffff0000c037 0xe1fffffff0000c03

def z1271 : W := mkw 0x2e400109e71b1bca 0x02e400109e71b1bc 0xffe00000ff3f3fc9 0x9ffe00000ff3f3fc

def z1272 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0x9fffffffbfc70007 0xf9fffffffbfc7000

def z1273 : W := mkw 0x0ee2fef600000000 0x20ee2fef60000000 0x1fe7ffff00000007 0xe1fe7ffff0000000

def z1274 : W := mkw 0x0262800026120000 0x0026280002612000 0xd7e780007f3f000b 0x8d7e780007f3f000

def z1275 : W := mkw 0x01abaa5618444411 0x001abaa561844441 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z1276 : W := mkw 0x5ffffef6d8e4e435 0x25ffffef6d8e4e43 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z1277 : W := mkw 0x0080290009005600 0x0008029000900560 0xb7e01f007f003f0d 0x8b7e01f007f003f0

def z1278 : W := mkw 0x3e768109e7bb1bca 0x13e768109e7bb1bc 0xe4660000473f3fc8 0x0e4660000473f3fc

def z1279 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xdfff80c0ffff00fb 0xbdfff80c0ffff00f

def z1280 : W := mkw 0x4e5450a8c0a8a8ac 0x04e5450a8c0a8a8a 0x7ffe70f8c0f8f8ff 0xf7ffe70f8c0f8f8f

def z1281 : W := mkw 0x113f82f612f60000 0x3113f82f612f6000 0xc47f9fff47ff000f 0xac47f9fff47ff000

def z1282 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xc0000000073f07c0 0x0c0000000073f07c

def z1283 : W := mkw 0x0f6b8000f6560000 0x00f6b8000f656000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1284 : W := mkw 0x1ffffef6f4440000 0x21ffffef6f444000 0xdfffffffffc7000f 0xfdfffffffffc7000

def z1285 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x17e79f3f00000001 0x017e79f3f0000000

def z1286 : W := mkw 0x2000010901091bca 0x02000010901091bc 0xe000000000073fc8 0x0e000000000073fc

def z1287 : W := mkw 0x0e628212e4000000 0x00e628212e400000 0x9fe79f3fff00000f 0xb9fe79f3fff00000

def z1288 : W := mkw 0x212b825f125f09db 0x0212b825f125f09d 0x4007803f003f00c2 0x24007803f003f00c

def z1289 : W := mkw 0x00947ef600000000 0x200947ef60000000 0x001e7fff00000006 0x6001e7fff0000000

def z1290 : W := mkw 0x1ffffef636560000 0x31ffffef63656000 0xdfffffffbfc7000f 0xfdfffffffbfc7000

def z1291 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x3fffffff0000c0f7 0xe3fffffff0000c0f

def z1292 : W := mkw 0x5f7fd2baf6fea8ac 0x15f7fd2baf6fea8a 0xfffffffffffff8ff 0xffffffffffffff8f

def z1293 : W := mkw 0x401400a800a808ac 0x0401400a800a808a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1294 : W := mkw 0x20802b5f09095fdb 0x020802b5f09095fd 0x20001f3f00003fc4 0x220001f3f00003fc

def z1295 : W := mkw 0x2022831b031b1bca 0x02022831b031b1bc 0xffe79f3fff3f3fcf 0xbffe79f3fff3f3fc

def z1296 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xffffe000ffffc00f 0xdffffe000ffffc00

def z1297 : W := mkw 0x136b800036560000 0x1136b80003656000 0xd3e780003f3f0003 0x0d3e780003f3f000

def z1298 : W := mkw 0x003682b200000000 0x0003682b20000000 0x047f9fff00000007 0xa047f9fff0000000

def z1299 : W := mkw 0x4c1450a8c0a8a8ac 0x04c1450a8c0a8a8a 0xec1ff0f8c0fff8ff 0xfec1ff0f8c0fff8f

def z1300 : W := mkw 0x0022821200000000 0x0002282120000000 0x6c7fffff80c0c0ff 0xf6c7fffff80c0c0f

def z1301 : W := mkw 0x20000109e71b1bca 0x020000109e71b1bc 0xe0000000ff3f3fc8 0x1e0000000ff3f3fc

def z1302 : W := mkw 0x1ffffef6e6b20000 0x31ffffef6e6b2000 0x5fffffffc7f8000f 0xf5fffffffc7f8000

def z1303 : W := mkw 0x20000109c3bb1bca 0x020000109c3bb1bc 0xe0000000c7ff3fc8 0x1e0000000c7ff3fc

def z1304 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xffff9000ffff380f 0x9ffff9000ffff380

def z1305 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe0018000473f3fcb 0x8e0018000473f3fc

def z1306 : W := mkw 0x1fffaef6f6f60000 0x31fffaef6f6f6000 0xdfff8fffffff000b 0xbdfff8fffffff000

def z1307 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0xd7e78000ffff0009 0x1d7e78000ffff000

def z1308 : W := mkw 0x1ef6fef600000000 0x21ef6fef60000000 0x0467ffff00000007 0xe0467ffff0000000

def z1309 : W := mkw 0x136b821236560000 0x1136b82123656000 0x93e18f073f070001 0x093e18f073f07000

def z1310 : W := mkw 0x9ffffef6fc44e411 0x29ffffef6fc44e41 0x1fffffffb8c0c037 0xf1fffffffb8c0c03

def z1311 : W := mkw 0x8ec02d00ed005600 0x08ec02d00ed00560 0xbfe01f00ff003f0d 0x9bfe01f00ff003f0

def z1312 : W := mkw 0x13ebae5600000000 0x213ebae560000000 0x13e78f3f00000003 0x213e78f3f0000000

def z1313 : W := mkw 0x13ebae5636560000 0x313ebae563656000 0xd7e79f3f7f3f000f 0xad7e79f3f7f3f000

def z1314 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe4600000473f3fc9 0x8e4600000473f3fc

def z1315 : W := mkw 0xced47da0eda0f624 0x0ced47da0eda0f62 0xfffe7fc0fff8ff3f 0xdfffe7fc0fff8ff3

def z1316 : W := mkw 0xc0000109fdedffff 0x0c0000109fdedfff 0xe0000000fffffff8 0x1e0000000fffffff

def z1317 : W := mkw 0x1ffffef6c0000000 0x21ffffef6c000000 0x1fffffffc000000f 0xf1fffffffc000000

def z1318 : W := mkw 0x8ed47d00eda0f600 0x08ed47d00eda0f60 0xbff87f00ffc0ff0d 0xdbff87f00ffc0ff0

def z1319 : W := mkw 0x7f7f8109f7ffbbee 0x17f7f8109f7ffbbe 0xffff8000fffffffb 0x9ffff8000fffffff

def z1320 : W := mkw 0x82c02d002d005600 0x082c02d002d00560 0xbfe07f00ff00ff0d 0xdbfe07f00ff00ff0

def z1321 : W := mkw 0x1ffffef6f6f60000 0x31ffffef6f6f6000 0xdfff9f3fffff000b 0x9dfff9f3fffff000

def z1322 : W := mkw 0xe0000109efbbffee 0x0e0000109efbbffe 0xe0000000fffffff8 0x1e0000000fffffff

def z1323 : W := mkw 0x0d9d7ef600000000 0x20d9d7ef60000000 0x1f9fffff00000007 0xe1f9fffff0000000

def z1324 : W := mkw 0x82c07d002d00f600 0x082c07d002d00f60 0x93e01f003f003f01 0x093e01f003f003f0

def z1325 : W := mkw 0x0189284518454553 0x0018928451845455 0xff9ff8ffb8c7c7ff 0xfff9ff8ffb8c7c7f

def z1326 : W := mkw 0x401450a800a8a8ac 0x0401450a800a8a8a 0x681e70f880f8f8fe 0xf681e70f880f8f8f

def z1327 : W := mkw 0x20000109135f1bdb 0x020000109135f1bd 0xe000000047ff3ff8 0x0e000000047ff3ff

def z1328 : W := mkw 0x3f7f8109031b1bca 0x03f7f8109031b1bc 0xffff8000473f3fcb 0x8ffff8000473f3fc

def z1329 : W := mkw 0x8ec07d00ed00f600 0x08ec07d00ed00f60 0x3fe07f00ff00ff04 0x53fe07f00ff00ff0

def z1330 : W := mkw 0x0000010001001200 0x0000001000100120 0xbfe01f00ff003f0d 0x9bfe01f00ff003f0

def z1331 : W := mkw 0x1ef6feb200000000 0x21ef6feb20000000 0x1fe7ff3f00000007 0xe1fe7ff3f0000000

def z1332 : W := mkw 0x11bffef600000000 0x211bffef60000000 0x1b9fffff00000007 0xe1b9fffff0000000

def z1333 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x7fffffff000000cf 0xe7fffffff000000c

def z1334 : W := mkw 0x1f7f800036560000 0x11f7f80003656000 0xdfff80007f3f000b 0x8dfff80007f3f000

def z1335 : W := mkw 0x1f7fd0a0f6f60000 0x11f7fd0a0f6f6000 0xfffff0f8ffffc0ff 0xffffff0f8ffffc0f

def z1336 : W := mkw 0x1febfef600000000 0x21febfef60000000 0x1fe1ffff00000005 0xe1fe1ffff0000000

def z1337 : W := mkw 0x1f7f8000f6f60000 0x11f7f8000f6f6000 0x9fe78000ff3f0009 0x99fe78000ff3f000

def z1338 : W := mkw 0x1ffffef610440000 0x21ffffef61044000 0x9fffffff38070007 0xe9fffffff3807000

def z1339 : W := mkw 0x20000109031b1bca 0x020000109031b1bc 0xe0000000473f3fce 0xae0000000473f3fc

def z1340 : W := mkw 0x6c1451a9c3bbbbee 0x06c1451a9c3bbbbe 0xe81860c0c7fffff8 0x5e81860c0c7fffff

def z1341 : W := mkw 0x113f800012f60000 0x1113f800012f6000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1342 : W := mkw 0x1f7fd0a0f6f6a000 0x11f7fd0a0f6f6a00 0xfffff0f8fffff80f 0xffffff0f8fffff80

def z1343 : W := mkw 0xcec07da0ed00f624 0x0cec07da0ed00f62 0xbfe07fc0ff00ff3d 0xdbfe07fc0ff00ff3

def z1344 : W := mkw 0x1ffffef6c000a000 0x21ffffef6c000a00 0x1fffffff40003807 0xe1fffffff4000380

def z1345 : W := mkw 0x0000021200000000 0x0000002120000000 0x04601f3f00000005 0xa04601f3f0000000

def z1346 : W := mkw 0x0e400000f6f60000 0x10e400000f6f6000 0xdb800000ffff0008 0x1db800000ffff000

def z1347 : W := mkw 0xce5454a8e4a8a8ac 0x0ce5454a8e4a8a8a 0x6c1e70f8c0f8f8fe 0xf6c1e70f8c0f8f8f

def z1348 : W := mkw 0x1ffffef600000000 0x21ffffef60000000 0x17e79f3f00000007 0xa17e79f3f0000000

def z1349 : W := mkw 0x1ffffef618444400 0x21ffffef61844440 0xffffffffb8c7c70f 0xfffffffffb8c7c70

def z1350 : W := mkw 0x0f5d0000f4e40000 0x00f5d0000f4e4000 0xdfff8000ffff000b 0x9dfff8000ffff000

def z1351 : W := mkw 0x5f7f80a0f6f60024 0x15f7f80a0f6f6002 0xdfff80c0ffff003b 0x9dfff80c0ffff003

def z1352 : W := mkw 0x1ffffef602b20000 0x31ffffef602b2000 0x1fffffff00380007 0xe1fffffff0038000

def z1353 : W := mkw 0x1ffffef608004400 0x21ffffef60800440 0x1fffffffb800c007 0xf1fffffffb800c00

def z1354 : W := mkw 0x113f82f600000000 0x2113f82f60000000 0x047f97ff00000002 0x2047f97ff0000000

def z1355 : W := mkw 0x136b800036f60000 0x1136b800036f6000 0xd3e180003fff0001 0x0d3e180003fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z8,z5]),(0,[z6,z9,z1,z7,z3,z10,z5]),(1,[z6,z11,z7,z3,z4,z5])],[(0,[z12,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z14,z15,z5]),(0,[z16,z6,z1,z17,z3,z4,z5])],[(0,[z6,z1,z7,z3,z18,z4,z5]),(0,[z6,z1,z7,z19,z20,z4,z5]),(1,[z6,z1,z7,z21,z4,z5]),(0,[z13,z6,z1,z3,z4,z22,z5]),(0,[z6,z1,z23,z24,z3,z4,z5]),(0,[z6,z25,z1,z7,z26,z4,z5]),(0,[z6,z1,z7,z3,z4,z27,z5]),(0,[z16,z6,z1,z3,z14,z4,z5]),(0,[z28,z16,z6,z1,z3,z4,z5]),(0,[z6,z29,z1,z24,z3,z4,z5]),(0,[z6,z30,z1,z7,z3,z4,z5]),(0,[z6,z31,z1,z7,z3,z4,z5])],[(1,[z6,z1,z32,z3,z4,z5]),(0,[z6,z1,z24,z24,z3,z4,z5]),(1,[z6,z1,z7,z3,z4,z33])],[(0,[z6,z34,z35,z1,z3,z4,z5]),(0,[z36,z6,z1,z7,z3,z4,z5]),(1,[z6,z1,z37,z3,z4,z5]),(0,[z6,z1,z7,z3,z38,z4,z5]),(0,[z6,z1,z7,z39,z3,z4,z5]),(0,[z6,z40,z1,z7,z3,z4,z5])],[(0,[z41,z6,z1,z23,z3,z4,z5]),(0,[z6,z7,z42,z3,z26,z4,z5]),(0,[z43,z6,z1,z7,z3,z4,z5]),(0,[z6,z44,z34,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z45]),(0,[z6,z1,z7,z3,z4,z33,z5])],[(1,[z6,z1,z46,z3,z4,z5])],[(0,[z6,z47,z1,z7,z3,z4,z5])]],
   [[(0,[z48,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z49,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z50,z5]),(0,[z6,z7,z23,z3,z4,z51,z5]),(0,[z6,z1,z7,z3,z4,z52,z5]),(0,[z53,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z54,z3,z4,z5]),(0,[z6,z1,z7,z3,z55,z5,z56])],[(0,[z57,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z58,z23,z3,z4,z5])],[(0,[z6,z1,z59,z7,z3,z4,z5]),(0,[z6,z60,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z51,z5]),(0,[z61,z6,z1,z7,z3,z4,z5]),(0,[z6,z29,z1,z7,z3,z4,z62]),(0,[z6,z1,z7,z3,z63,z4,z5])],[(0,[z64,z6,z65,z7,z3,z4,z5]),(0,[z66,z6,z1,z7,z3,z4,z5]),(0,[z67,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z7,z68,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z69,z5]),(0,[z6,z1,z7,z3,z70,z4,z5]),(0,[z6,z1,z71,z3,z26,z4,z5]),(0,[z6,z1,z24,z3,z4,z51,z5]),(0,[z6,z72,z1,z73,z3,z4,z5]),(0,[z6,z1,z7,z17,z3,z4,z56])],[(1,[z6,z7,z3,z74,z4,z5]),(0,[z6,z1,z7,z3,z75,z4,z5]),(0,[z6,z1,z76,z7,z3,z4,z5]),(0,[z6,z77,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z78,z4,z5]),(0,[z6,z79,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z80,z3,z4,z5]),(0,[z12,z16,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z81,z5]),(0,[z6,z1,z58,z7,z24,z4,z5]),(0,[z82,z6,z1,z7,z3,z4,z5]),(0,[z83,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z84])],[(1,[z6,z85,z7,z3,z4,z5]),(0,[z6,z44,z1,z23,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z86,z5]),(0,[z6,z1,z7,z87,z3,z4,z5]),(0,[z88,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z78,z4,z5]),(0,[z6,z1,z7,z78,z4,z86,z5]),(0,[z6,z89,z1,z7,z3,z4,z5])],[(0,[z90,z6,z1,z7,z3,z4,z5]),(0,[z6,z91,z1,z23,z3,z4,z5]),(1,[z16,z6,z92,z3,z4,z5]),(0,[z6,z1,z7,z3,z93,z4,z5]),(1,[z94,z6,z1,z7,z4,z95])],[(1,[z96,z6,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z97,z5]),(0,[z98,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z51,z5,z56]),(0,[z6,z1,z7,z3,z4,z5,z99])]],
   [[(1,[z6,z100,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z22,z5]),(0,[z6,z101,z1,z7,z3,z4,z5]),(0,[z12,z6,z1,z7,z42,z4,z5]),(0,[z6,z102,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z103,z5])],[(0,[z104,z6,z1,z7,z3,z4,z5]),(0,[z105,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z22,z5]),(0,[z6,z1,z7,z3,z106,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z107]),(0,[z6,z1,z7,z3,z108,z4,z5]),(0,[z6,z1,z7,z17,z3,z4,z109])],[(0,[z6,z65,z1,z23,z3,z4,z5]),(0,[z6,z34,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z55,z110]),(1,[z6,z111,z1,z3,z4,z62]),(0,[z6,z1,z7,z3,z112,z4,z5]),(0,[z6,z113,z1,z3,z4,z86,z5])],[(0,[z114,z1,z7,z115,z3,z4,z5]),(0,[z12,z6,z1,z116,z3,z4,z5]),(1,[z6,z7,z3,z4,z5,z117])],[(0,[z118,z6,z1,z7,z17,z3,z4]),(1,[z13,z6,z23,z3,z4,z5]),(0,[z41,z6,z9,z7,z3,z4,z5]),(0,[z6,z25,z1,z7,z42,z4,z5]),(0,[z119,z6,z1,z7,z3,z4,z5]),(1,[z6,z1,z120,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z121,z5]),(0,[z122,z6,z1,z24,z3,z4,z5]),(0,[z123,z6,z1,z7,z3,z4,z5]),(0,[z124,z6,z1,z7,z3,z4,z5]),(0,[z41,z6,z7,z3,z4,z125,z5]),(0,[z6,z91,z102,z1,z3,z4,z5]),(0,[z126,z16,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z127,z5])],[(0,[z13,z6,z29,z1,z3,z4,z5]),(0,[z12,z6,z7,z3,z4,z51,z5]),(0,[z16,z6,z1,z3,z15,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z128])],[(0,[z129,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z110]),(1,[z6,z113,z1,z3,z4,z5]),(0,[z6,z7,z3,z78,z4,z130,z5]),(0,[z6,z1,z7,z3,z4,z5,z131])]],
   [[(0,[z132,z114,z1,z7,z3,z4,z5]),(0,[z6,z133,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z62,z5]),(0,[z6,z31,z134,z7,z3,z4,z5])],[(1,[z64,z6,z23,z3,z4,z5]),(0,[z135,z6,z1,z136,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z69,z5]),(0,[z6,z137,z1,z23,z3,z4,z5]),(0,[z138,z6,z1,z24,z3,z4,z5])],[(0,[z122,z13,z6,z1,z3,z4,z5]),(0,[z122,z6,z7,z42,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z69,z5]),(0,[z139,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z62,z5,z110]),(0,[z6,z1,z7,z3,z4,z5,z95])],[(0,[z0,z6,z1,z24,z3,z4,z5]),(0,[z13,z6,z1,z115,z3,z4,z5]),(0,[z16,z6,z1,z3,z140,z4,z5]),(0,[z6,z1,z23,z3,z4,z86,z5]),(0,[z6,z1,z141,z7,z3,z4,z5]),(0,[z6,z142,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z143,z4,z5])],[(0,[z6,z1,z7,z3,z4,z144,z5]),(0,[z6,z1,z7,z3,z4,z145,z5]),(0,[z146,z6,z1,z7,z3,z4,z5]),(0,[z6,z147,z1,z7,z3,z51,z5]),(0,[z6,z148,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z86,z5]),(0,[z149,z6,z1,z7,z3,z4,z5]),(0,[z150,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z151,z3,z4,z5])],[(0,[z135,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z152,z7,z3,z4,z5]),(0,[z153,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z154])],[(0,[z155,z6,z1,z7,z3,z4,z5]),(0,[z156,z6,z1,z7,z3,z4,z5]),(0,[z138,z13,z6,z1,z3,z4,z5]),(0,[z16,z6,z1,z3,z26,z4,z5])],[(1,[z6,z1,z157,z3,z4,z5]),(0,[z158,z6,z1,z7,z3,z4,z5])]],
   [[(0,[z64,z1,z159,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z160,z4,z5]),(0,[z16,z6,z9,z1,z3,z4,z5]),(0,[z16,z6,z31,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z161,z5]),(0,[z6,z1,z7,z3,z15,z4,z56])],[(0,[z6,z1,z7,z3,z4,z5,z162]),(1,[z6,z1,z7,z3,z10,z5]),(0,[z6,z163,z1,z7,z3,z4,z5]),(0,[z164,z6,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z165,z3,z4,z5]),(0,[z6,z166,z1,z7,z3,z4,z5]),(0,[z167,z6,z1,z7,z3,z4,z5]),(0,[z6,z168,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z169,z4,z5]),(0,[z6,z1,z7,z3,z4,z170,z5]),(0,[z6,z1,z7,z3,z4,z171,z5]),(0,[z6,z1,z7,z3,z4,z172,z5]),(0,[z6,z1,z24,z3,z4,z5,z173]),(0,[z6,z1,z7,z17,z3,z4,z55])],[(0,[z13,z6,z1,z159,z3,z4,z5]),(0,[z6,z174,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z175,z4,z5]),(0,[z6,z1,z24,z3,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z176])],[(0,[z6,z1,z177,z7,z3,z4,z5]),(0,[z6,z147,z1,z178,z3,z4,z5]),(0,[z16,z6,z72,z1,z3,z4,z5])],[(0,[z6,z1,z7,z179,z3,z4,z5]),(0,[z6,z1,z7,z20,z4,z86,z5]),(0,[z6,z1,z7,z3,z4,z51,z5]),(0,[z6,z1,z180,z7,z3,z4,z5])],[(0,[z16,z6,z35,z1,z3,z4,z5]),(0,[z6,z1,z7,z32,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z55,z181]),(1,[z6,z182,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z5,z183]),(0,[z6,z184,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z185,z5]),(0,[z16,z6,z1,z3,z4,z5,z181]),(0,[z186,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z78,z4,z5]),(0,[z6,z1,z3,z78,z4,z187,z5])]],
   [[(0,[z6,z1,z7,z3,z21,z4,z5])],[(0,[z6,z1,z7,z3,z4,z188,z5]),(0,[z13,z6,z1,z3,z4,z5,z189])],[(0,[z132,z6,z1,z23,z3,z4,z5]),(0,[z6,z190,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z191,z4,z5]),(0,[z6,z7,z3,z14,z4,z51,z5]),(1,[z6,z1,z73,z3,z4,z5]),(0,[z6,z192,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z15,z55,z5])],[(0,[z6,z1,z7,z193,z3,z4,z5]),(0,[z6,z1,z194,z7,z3,z4,z5]),(0,[z195,z6,z1,z7,z3,z4,z5]),(0,[z196,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z197,z5]),(0,[z6,z1,z7,z3,z198,z4,z5]),(0,[z199,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z24,z3,z200,z4,z5]),(0,[z6,z111,z1,z7,z3,z4,z110]),(0,[z6,z7,z3,z4,z5,z117,z95])],[(0,[z122,z65,z1,z7,z3,z4,z5]),(0,[z67,z6,z1,z7,z3,z4,z5]),(0,[z118,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z23,z3,z201,z4,z5]),(0,[z6,z1,z7,z3,z202,z26,z4]),(0,[z6,z91,z1,z7,z3,z4,z203]),(0,[z16,z6,z34,z1,z3,z4,z5]),(0,[z6,z204,z1,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z205,z95])],[(0,[z1,z7,z3,z140,z4,z69,z5]),(0,[z6,z206,z1,z7,z3,z4,z5]),(0,[z6,z207,z1,z7,z3,z4,z5]),(1,[z6,z23,z3,z26,z4,z5]),(0,[z6,z1,z24,z3,z201,z4,z5]),(1,[z6,z134,z7,z3,z4,z5])],[(0,[z6,z208,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z209]),(0,[z41,z6,z174,z7,z3,z4,z5]),(1,[z6,z210,z1,z3,z4,z5]),(1,[z16,z6,z211,z3,z4,z5])],[(0,[z212,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z213,z5]),(0,[z6,z35,z1,z3,z4,z214,z5]),(0,[z6,z1,z7,z3,z4,z215,z5]),(0,[z216,z6,z1,z7,z3,z4,z5]),(0,[z217,z1,z7,z3,z4,z5,z181]),(0,[z6,z1,z7,z3,z218,z4,z5]),(0,[z6,z1,z7,z3,z4,z219,z5]),(0,[z6,z1,z220,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z221,z5]),(0,[z6,z222,z1,z7,z3,z4,z5])]],
   [[(0,[z6,z223,z1,z7,z3,z4,z5]),(0,[z13,z6,z147,z1,z3,z4,z5]),(0,[z224,z6,z1,z7,z3,z4,z5]),(0,[z6,z225,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z226]),(0,[z6,z1,z7,z3,z78,z4,z45])],[(1,[z64,z159,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z227]),(0,[z6,z1,z7,z3,z228,z20,z4]),(0,[z229,z6,z1,z23,z3,z4,z5]),(0,[z13,z6,z1,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z230]),(0,[z6,z1,z231,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z232,z5])],[(0,[z64,z6,z1,z7,z3,z4,z5]),(0,[z6,z233,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z234,z20,z5]),(0,[z235,z1,z7,z3,z140,z4,z5]),(0,[z6,z236,z1,z7,z3,z4,z5]),(0,[z16,z6,z25,z1,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z125,z5]),(0,[z6,z1,z7,z3,z4,z5,z237]),(0,[z6,z1,z7,z3,z4,z238,z5])],[],[(0,[z6,z1,z7,z3,z239,z4,z5]),(0,[z16,z6,z1,z23,z3,z4,z5]),(0,[z6,z240,z1,z7,z3,z4,z5]),(0,[z13,z6,z1,z58,z3,z4,z5]),(0,[z6,z1,z7,z116,z3,z4,z5]),(0,[z6,z241,z1,z7,z3,z4,z5]),(0,[z6,z34,z1,z3,z4,z5,z110])],[(0,[z6,z1,z7,z3,z242,z4,z5]),(0,[z6,z1,z7,z3,z4,z243,z5]),(0,[z6,z1,z7,z244,z3,z4,z5]),(0,[z245,z16,z6,z1,z3,z4,z5])],[(0,[z64,z6,z7,z23,z3,z4,z5]),(0,[z6,z246,z1,z7,z3,z4,z5]),(0,[z67,z0,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z247,z4,z5]),(0,[z16,z6,z1,z3,z248,z4,z5])],[(0,[z6,z31,z1,z23,z3,z4,z5]),(0,[z16,z6,z1,z7,z24,z4,z5]),(1,[z6,z29,z1,z3,z4,z110]),(0,[z6,z249,z7,z3,z78,z4,z5]),(0,[z6,z250,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z15,z4,z55])]],
   [[(1,[z6,z1,z7,z3,z234,z5]),(0,[z6,z1,z7,z3,z4,z251,z5]),(0,[z12,z6,z25,z7,z3,z4,z5]),(1,[z6,z1,z7,z3,z4,z252]),(0,[z6,z1,z253,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z254,z4,z5])],[(0,[z6,z9,z1,z7,z3,z4,z5])],[(1,[z6,z1,z7,z255,z4,z5]),(0,[z6,z1,z256,z7,z3,z4,z5]),(0,[z6,z1,z7,z257,z3,z4,z5]),(0,[z6,z72,z147,z7,z3,z4,z5]),(0,[z6,z7,z3,z4,z125,z5,z99]),(1,[z6,z211,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z55,z5])],[(0,[z6,z147,z1,z24,z3,z4,z5]),(0,[z6,z72,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z258,z5])],[(0,[z259,z6,z1,z7,z3,z4,z5]),(0,[z13,z6,z44,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z125,z56]),(0,[z6,z1,z7,z3,z4,z5,z260])],[(0,[z261,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z20,z4,z5]),(0,[z41,z16,z6,z1,z3,z4,z5]),(0,[z262,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z263,z5])],[(0,[z264,z6,z1,z7,z3,z4,z5]),(0,[z132,z6,z1,z7,z115,z4,z5]),(0,[z114,z6,z1,z7,z115,z4,z5]),(0,[z6,z1,z7,z265,z3,z4,z5]),(0,[z6,z1,z7,z266,z3,z4,z5]),(1,[z16,z6,z1,z248,z4,z5])],[(0,[z6,z1,z7,z267,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z268]),(0,[z12,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z269,z4,z5]),(0,[z6,z1,z270,z7,z3,z4,z5]),(0,[z271,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z272,z5])]],
   [[(0,[z6,z147,z7,z42,z3,z4,z5]),(0,[z6,z31,z1,z7,z3,z15,z5])],[(0,[z273,z6,z1,z7,z3,z4,z5]),(0,[z35,z1,z7,z2,z3,z4,z5]),(0,[z6,z1,z23,z2,z3,z4,z5]),(0,[z6,z274,z1,z7,z3,z4,z5]),(1,[z6,z23,z3,z4,z125,z5]),(0,[z6,z79,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z275,z4,z5]),(0,[z94,z6,z1,z7,z3,z4,z5])],[(0,[z6,z35,z1,z7,z3,z4,z5]),(0,[z16,z0,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z157,z3,z4,z5]),(0,[z6,z1,z7,z3,z276,z4,z5]),(0,[z277,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z278,z5]),(0,[z6,z1,z7,z3,z4,z279,z5]),(0,[z6,z1,z7,z3,z4,z5,z280])],[(0,[z96,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z281,z3,z4,z5]),(0,[z138,z235,z6,z1,z7,z3,z5]),(0,[z6,z25,z1,z24,z3,z4,z5]),(0,[z16,z6,z1,z211,z3,z4,z5]),(0,[z6,z1,z7,z3,z282,z4,z5])],[(0,[z65,z1,z159,z7,z3,z4,z5]),(0,[z6,z283,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z284,z5]),(0,[z6,z1,z285,z24,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z286,z5]),(0,[z6,z1,z287,z7,z3,z4,z5]),(0,[z6,z288,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z289,z5]),(0,[z6,z290,z1,z7,z3,z4,z5]),(0,[z6,z291,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z19,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z56])],[(0,[z6,z1,z7,z285,z3,z4,z5]),(0,[z292,z6,z1,z7,z3,z4,z5]),(0,[z293,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z294])],[(0,[z6,z1,z7,z3,z295,z4,z5]),(0,[z41,z6,z7,z3,z4,z51,z5]),(0,[z6,z1,z7,z3,z201,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z296]),(0,[z6,z1,z7,z297,z3,z4,z5])]],
   [[(0,[z67,z35,z1,z7,z3,z4,z5]),(0,[z13,z235,z6,z1,z3,z4,z5]),(0,[z6,z25,z7,z42,z3,z4,z5]),(0,[z298,z6,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z299,z5]),(0,[z6,z1,z7,z178,z3,z4,z5])],[(0,[z6,z300,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z5,z301]),(0,[z6,z1,z7,z3,z4,z109,z5]),(0,[z6,z1,z7,z3,z4,z5,z302])],[(0,[z6,z1,z7,z303,z3,z4,z5]),(0,[z6,z1,z58,z7,z248,z4,z5]),(0,[z6,z1,z24,z3,z4,z304,z5]),(0,[z6,z31,z1,z7,z3,z4,z56])],[(0,[z6,z1,z7,z3,z305,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z306]),(0,[z6,z1,z7,z3,z307,z4,z5]),(0,[z13,z6,z174,z1,z3,z4,z5]),(0,[z6,z9,z1,z7,z3,z4,z99]),(0,[z94,z6,z9,z1,z7,z3,z4]),(0,[z6,z308,z1,z7,z3,z4,z5]),(0,[z6,z309,z1,z7,z3,z4,z5])],[(0,[z6,z310,z1,z7,z3,z4,z5]),(0,[z6,z311,z147,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z55,z99]),(0,[z6,z1,z7,z3,z312,z4,z5])],[(0,[z6,z1,z7,z3,z313,z4,z5]),(0,[z6,z1,z7,z3,z4,z314,z5]),(0,[z122,z6,z65,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z315,z4,z5]),(0,[z6,z316,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z317,z4,z5]),(0,[z6,z1,z7,z3,z4,z318,z5]),(0,[z6,z72,z1,z7,z3,z4,z99]),(0,[z16,z6,z1,z3,z4,z5,z99]),(1,[z6,z92,z7,z3,z4,z5]),(0,[z138,z6,z1,z7,z3,z86,z5])],[(0,[z319,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z214,z5]),(0,[z6,z320,z1,z7,z3,z4,z5]),(0,[z321,z6,z1,z7,z3,z4,z5]),(1,[z6,z322,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z323,z5])]],
   [[(0,[z6,z1,z7,z324,z3,z4,z5]),(0,[z217,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z141,z23,z3,z4,z5]),(0,[z6,z91,z7,z3,z4,z51,z5]),(0,[z6,z9,z210,z1,z3,z4,z5]),(0,[z94,z6,z72,z1,z7,z3,z4]),(0,[z6,z1,z24,z3,z4,z214,z5]),(0,[z6,z325,z1,z7,z3,z4,z5])],[(1,[z132,z1,z7,z20,z4,z5]),(0,[z6,z7,z3,z74,z20,z4,z5]),(0,[z13,z326,z6,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z327,z4,z5]),(0,[z16,z6,z111,z1,z3,z4,z5])],[(0,[z328,z6,z1,z7,z3,z4,z5]),(0,[z67,z6,z35,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z329]),(0,[z6,z1,z7,z42,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z125,z55]),(0,[z6,z1,z330,z7,z3,z4,z5]),(0,[z6,z111,z1,z7,z3,z4,z5])],[(0,[z6,z65,z7,z3,z4,z51,z5]),(0,[z114,z6,z168,z1,z3,z4,z5]),(0,[z13,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z331,z5]),(1,[z6,z34,z1,z3,z201,z5]),(0,[z332,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z333])],[(0,[z334,z6,z7,z3,z20,z4,z5]),(0,[z135,z16,z6,z1,z3,z4,z5]),(0,[z217,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z335,z7,z3,z4,z5]),(0,[z336,z6,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z337,z5]),(0,[z6,z338,z1,z7,z3,z4,z5]),(0,[z13,z6,z1,z17,z3,z4,z5]),(0,[z6,z9,z1,z7,z17,z3,z4]),(0,[z16,z6,z1,z3,z4,z5,z110])],[(0,[z64,z6,z339,z1,z3,z4,z5]),(0,[z6,z1,z159,z7,z3,z4,z5]),(0,[z132,z13,z6,z1,z3,z4,z5]),(0,[z13,z6,z1,z3,z14,z4,z5]),(0,[z16,z6,z1,z3,z4,z62,z5]),(0,[z6,z1,z7,z3,z4,z5,z340]),(0,[z6,z1,z341,z7,z3,z4,z5]),(0,[z6,z342,z1,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z214,z5,z110]),(0,[z6,z343,z1,z3,z78,z4,z5]),(1,[z6,z89,z1,z3,z4,z5]),(1,[z6,z31,z1,z7,z3,z56]),(0,[z6,z1,z7,z344,z3,z4,z5])]],
   [[(0,[z6,z174,z1,z23,z3,z4,z5]),(0,[z13,z6,z7,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z15,z51,z5]),(0,[z6,z72,z1,z7,z17,z3,z4]),(0,[z6,z345,z1,z7,z3,z4,z5]),(0,[z6,z346,z1,z7,z3,z4,z5])],[(0,[z6,z1,z347,z7,z3,z4,z5]),(0,[z217,z6,z1,z32,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z5,z95]),(0,[z6,z1,z348,z7,z3,z4,z5]),(0,[z6,z113,z1,z7,z3,z4,z5])],[(1,[z6,z1,z7,z3,z4,z5]),(0,[z0,z6,z1,z2,z3,z4,z5]),(0,[z6,z1,z7,z3,z349,z4,z5]),(0,[z6,z1,z7,z3,z4,z350,z5]),(0,[z6,z91,z1,z7,z3,z51,z5]),(0,[z6,z1,z7,z3,z4,z110,z56])],[(0,[z351,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z352,z5]),(0,[z6,z1,z7,z3,z4,z353,z5]),(0,[z6,z354,z1,z7,z3,z4,z5]),(1,[z6,z1,z3,z4,z187,z5])],[(0,[z6,z1,z7,z2,z3,z4,z5]),(1,[z6,z1,z256,z3,z4,z5]),(0,[z217,z6,z1,z7,z3,z4,z22]),(0,[z6,z355,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z356,z4,z5]),(1,[z6,z1,z7,z3,z202,z4]),(0,[z6,z7,z42,z3,z4,z125,z5]),(0,[z6,z357,z1,z7,z3,z4,z5]),(0,[z6,z358,z1,z24,z3,z4,z5])],[(1,[z122,z6,z23,z3,z4,z5]),(1,[z138,z6,z1,z7,z86,z5])],[(0,[z6,z359,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z360,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z361,z5]),(0,[z6,z1,z7,z253,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z362,z5]),(1,[z6,z363,z1,z3,z4,z5])],[(0,[z6,z364,z1,z7,z3,z4,z5]),(0,[z135,z6,z1,z7,z3,z4,z365]),(0,[z235,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z366]),(0,[z6,z1,z7,z3,z367,z4,z5]),(1,[z6,z7,z3,z4,z130,z5]),(0,[z94,z6,z1,z7,z3,z4,z95]),(0,[z6,z1,z7,z3,z4,z5,z368])]],
   [[(0,[z6,z1,z369,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z370]),(0,[z6,z1,z7,z3,z74,z4,z5]),(0,[z6,z371,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z372,z5])],[(0,[z122,z6,z159,z7,z3,z4,z5]),(0,[z67,z6,z1,z23,z3,z4,z5]),(0,[z373,z6,z1,z7,z3,z4,z5]),(0,[z16,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z62,z56]),(0,[z374,z6,z1,z7,z3,z4,z5]),(0,[z375,z6,z1,z7,z3,z4,z5]),(0,[z376,z6,z1,z7,z3,z4,z5])],[(1,[z122,z65,z7,z3,z4,z5]),(0,[z6,z1,z2,z3,z4,z5,z110]),(0,[z132,z16,z6,z1,z3,z4,z5]),(0,[z6,z44,z1,z7,z3,z201,z5]),(0,[z6,z29,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z377,z4,z5]),(0,[z378,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z379,z4,z5]),(1,[z6,z1,z7,z3,z4,z45])],[(0,[z6,z1,z100,z7,z3,z4,z5]),(0,[z6,z1,z23,z17,z3,z4,z5]),(0,[z6,z25,z1,z266,z3,z4,z5]),(1,[z6,z25,z7,z42,z4,z5]),(0,[z16,z6,z1,z3,z4,z51,z5]),(0,[z6,z1,z7,z3,z14,z5,z56])],[(1,[z6,z1,z3,z380,z4,z5]),(0,[z6,z1,z24,z17,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z304,z5]),(0,[z6,z44,z1,z7,z3,z4,z381])],[(0,[z16,z64,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z382,z3,z4,z5]),(0,[z135,z6,z383,z7,z3,z4,z5]),(1,[z217,z1,z7,z3,z4,z181]),(0,[z384,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z14,z4,z5]),(0,[z16,z6,z1,z3,z78,z4,z5])],[(0,[z64,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z385,z4,z5]),(0,[z6,z386,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z387]),(0,[z6,z388,z1,z7,z3,z4,z5])]],
   [[(0,[z389,z6,z1,z7,z3,z4,z5]),(1,[z6,z91,z7,z3,z51,z5]),(0,[z6,z1,z7,z3,z4,z390,z5]),(0,[z6,z1,z7,z3,z4,z391,z5]),(0,[z392,z6,z1,z24,z3,z4,z5]),(0,[z6,z44,z393,z7,z3,z4,z5])],[(0,[z6,z6,z1,z7,z3,z4,z5]),(0,[z6,z240,z1,z23,z3,z4,z5]),(0,[z41,z6,z25,z7,z3,z4,z5]),(1,[z6,z1,z71,z3,z4,z5]),(0,[z16,z6,z91,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z394,z4,z5]),(0,[z6,z395,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z396,z5]),(0,[z397,z6,z1,z7,z3,z4,z5]),(0,[z6,z174,z7,z23,z3,z4,z5]),(0,[z13,z6,z1,z398,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z399]),(0,[z6,z1,z7,z3,z4,z214,z5])],[(0,[z400,z6,z1,z7,z3,z4,z5]),(0,[z401,z6,z1,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z22,z5,z181]),(0,[z13,z6,z1,z3,z15,z4,z5]),(0,[z6,z1,z7,z3,z4,z10,z5]),(0,[z6,z1,z3,z4,z109,z5,z131])],[(0,[z12,z64,z6,z7,z3,z4,z5]),(0,[z6,z1,z23,z115,z3,z4,z5]),(0,[z6,z1,z7,z46,z3,z4,z5]),(0,[z16,z16,z6,z1,z3,z4,z5]),(0,[z6,z44,z1,z7,z3,z4,z402])],[(0,[z12,z122,z6,z7,z3,z4,z5]),(0,[z6,z1,z24,z115,z3,z4,z5]),(0,[z6,z403,z1,z7,z3,z4,z5]),(0,[z404,z6,z1,z7,z3,z4,z5])],[(0,[z0,z1,z7,z2,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z22,z5]),(0,[z6,z9,z1,z23,z3,z4,z5])],[(0,[z6,z1,z24,z3,z405,z4,z5])]],
   [[(0,[z6,z1,z406,z7,z3,z4,z5]),(0,[z13,z6,z1,z3,z140,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z407]),(0,[z6,z72,z1,z23,z3,z4,z5]),(0,[z41,z6,z1,z24,z3,z4,z5]),(1,[z6,z1,z398,z3,z4,z5])],[(0,[z6,z1,z408,z7,z3,z4,z5]),(0,[z6,z311,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z409])],[(0,[z16,z6,z65,z1,z3,z4,z5]),(1,[z6,z1,z58,z24,z4,z5]),(0,[z138,z6,z1,z7,z4,z86,z5]),(0,[z6,z11,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z5,z365]),(0,[z264,z6,z1,z23,z3,z4,z5]),(1,[z6,z23,z3,z4,z51,z5]),(0,[z13,z6,z1,z3,z26,z4,z5]),(0,[z6,z1,z7,z3,z4,z410,z5])],[(0,[z6,z147,z65,z7,z3,z4,z5]),(0,[z135,z6,z1,z7,z3,z4,z97]),(0,[z6,z1,z58,z24,z3,z4,z5])],[(0,[z122,z6,z1,z7,z3,z4,z5]),(0,[z16,z118,z6,z1,z3,z4,z5]),(0,[z41,z13,z6,z1,z3,z4,z5]),(0,[z13,z6,z9,z1,z3,z4,z5]),(0,[z13,z6,z31,z1,z3,z4,z5]),(0,[z411,z6,z1,z7,z3,z4,z5])],[(0,[z6,z412,z65,z1,z3,z4,z5]),(0,[z94,z6,z1,z23,z3,z4,z5]),(0,[z16,z6,z1,z7,z248,z4,z5])],[(0,[z6,z35,z1,z23,z3,z4,z5]),(1,[z397,z6,z1,z7,z3,z5]),(0,[z114,z6,z1,z157,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z69,z5]),(0,[z413,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z414]),(0,[z6,z1,z7,z3,z4,z203,z5])]],
   [[(0,[z6,z7,z3,z4,z51,z5,z99]),(0,[z415,z6,z1,z7,z3,z4,z5]),(0,[z6,z44,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z62,z55]),(0,[z416,z6,z1,z7,z3,z4,z5])],[(0,[z6,z417,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z15,z4,z5]),(0,[z13,z6,z72,z1,z3,z4,z5]),(0,[z6,z91,z1,z24,z3,z4,z5]),(0,[z6,z9,z1,z7,z3,z4,z125]),(0,[z16,z6,z1,z3,z4,z55,z5]),(0,[z6,z418,z1,z7,z3,z4,z5]),(0,[z138,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z86,z5])],[(0,[z6,z111,z35,z1,z3,z4,z5]),(0,[z419,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z420]),(0,[z88,z16,z6,z1,z3,z4,z5]),(0,[z6,z1,z24,z3,z15,z4,z5]),(0,[z6,z421,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z120,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z422])],[(0,[z6,z423,z1,z7,z3,z4,z5]),(0,[z0,z6,z1,z7,z3,z4,z5]),(0,[z13,z6,z35,z1,z3,z4,z5]),(0,[z293,z6,z1,z23,z3,z4,z5]),(0,[z6,z72,z1,z7,z3,z4,z125])],[(0,[z16,z6,z1,z3,z20,z4,z5]),(0,[z13,z6,z1,z3,z4,z5,z181]),(0,[z6,z241,z1,z7,z3,z26,z4]),(1,[z6,z1,z424,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z425]),(0,[z6,z1,z7,z3,z426,z4,z5]),(0,[z6,z1,z427,z7,z3,z4,z5])],[(0,[z6,z65,z1,z24,z3,z4,z5]),(0,[z6,z428,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z429]),(0,[z6,z34,z1,z24,z3,z4,z5]),(0,[z6,z29,z1,z7,z3,z4,z110]),(0,[z6,z1,z7,z3,z4,z5,z430])],[(0,[z6,z339,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z181,z56]),(0,[z6,z1,z7,z3,z4,z5,z431]),(0,[z6,z1,z7,z3,z432,z4,z5]),(0,[z6,z1,z7,z3,z433,z4,z5]),(0,[z6,z1,z7,z434,z3,z4,z5]),(1,[z6,z1,z3,z4,z5,z205]),(0,[z6,z1,z435,z7,z3,z4,z5])],[(1,[z6,z339,z1,z3,z4,z5]),(0,[z6,z436,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z437,z4,z5]),(0,[z6,z1,z7,z3,z438,z4,z5]),(0,[z439,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z173]),(0,[z6,z1,z7,z440,z3,z4,z5]),(0,[z6,z363,z1,z7,z3,z4,z5])]],
   [[(0,[z6,z441,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z442]),(0,[z6,z1,z7,z115,z4,z86,z5]),(0,[z6,z9,z7,z23,z3,z4,z5]),(0,[z6,z72,z7,z3,z4,z125,z5]),(0,[z6,z111,z34,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z443,z5])],[(0,[z6,z1,z7,z3,z444,z4,z5]),(0,[z6,z1,z23,z3,z26,z4,z5]),(0,[z13,z6,z34,z1,z3,z4,z5]),(0,[z6,z445,z1,z7,z3,z4,z5])],[(0,[z6,z1,z24,z3,z26,z4,z5]),(0,[z16,z6,z1,z3,z282,z4,z5]),(0,[z6,z1,z446,z7,z3,z4,z5]),(0,[z6,z44,z1,z3,z4,z214,z5])],[(0,[z6,z1,z7,z3,z4,z447,z5]),(0,[z6,z147,z1,z7,z3,z14,z5]),(0,[z6,z322,z1,z7,z3,z4,z5])],[(0,[z16,z6,z1,z19,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z5,z56])],[(0,[z6,z1,z7,z3,z4,z448,z5]),(0,[z6,z91,z1,z46,z3,z4,z5]),(0,[z6,z449,z1,z7,z3,z4,z5])],[(0,[z450,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z451,z4,z5]),(1,[z6,z1,z452,z3,z4,z5]),(0,[z13,z6,z453,z1,z3,z4,z5]),(0,[z16,z6,z1,z3,z201,z4,z5]),(0,[z6,z111,z454,z7,z3,z4,z5]),(0,[z6,z1,z455,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z456,z5]),(0,[z6,z147,z159,z7,z3,z4,z5]),(0,[z6,z1,z7,z115,z3,z4,z5]),(0,[z13,z6,z25,z1,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z125,z5]),(0,[z6,z1,z7,z3,z457,z4,z5]),(0,[z186,z6,z1,z7,z3,z4,z5])]],
   [[(0,[z6,z1,z7,z458,z3,z4,z5]),(0,[z135,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z459,z5]),(0,[z6,z111,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z200,z4,z5]),(0,[z460,z6,z1,z7,z3,z4,z5])],[(0,[z461,z6,z1,z7,z3,z4,z5]),(0,[z6,z462,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z463,z5]),(0,[z6,z464,z1,z7,z3,z4,z5]),(0,[z13,z6,z1,z23,z3,z4,z5]),(0,[z465,z6,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z109,z5]),(0,[z6,z1,z7,z231,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z381]),(0,[z466,z6,z1,z7,z3,z4,z5]),(0,[z467,z6,z1,z7,z3,z4,z5])],[(0,[z468,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z5,z181]),(0,[z469,z6,z1,z7,z3,z4,z5]),(0,[z470,z13,z6,z1,z3,z4,z5]),(0,[z471,z6,z1,z7,z3,z4,z5]),(0,[z94,z6,z1,z7,z3,z4,z56])],[(0,[z472,z6,z1,z7,z3,z4,z5]),(0,[z199,z6,z1,z7,z3,z4,z5]),(0,[z473,z6,z1,z7,z3,z4,z5]),(1,[z6,z1,z136,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z5,z181]),(0,[z13,z6,z1,z3,z248,z4,z5]),(0,[z6,z1,z7,z474,z3,z4,z5]),(0,[z6,z475,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z476,z5]),(0,[z6,z1,z7,z3,z477,z4,z5])],[(0,[z6,z1,z159,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z478,z4,z5]),(0,[z6,z1,z7,z17,z4,z109,z5])],[(0,[z96,z6,z35,z7,z3,z4,z5]),(0,[z135,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z479]),(0,[z12,z6,z7,z3,z26,z4,z5]),(0,[z6,z1,z7,z3,z4,z480,z5]),(0,[z6,z1,z481,z7,z3,z4,z5]),(1,[z6,z454,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z482,z5])],[(0,[z6,z483,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z19,z115,z4,z5]),(1,[z6,z147,z23,z3,z4,z5]),(0,[z6,z1,z23,z452,z3,z4,z5]),(0,[z6,z7,z42,z3,z4,z51,z5]),(0,[z6,z1,z211,z7,z3,z4,z5]),(0,[z6,z484,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z485,z5])],[(0,[z6,z1,z7,z3,z486,z4,z5]),(1,[z6,z1,z23,z3,z4,z5]),(0,[z487,z6,z1,z7,z3,z4,z5]),(0,[z6,z488,z1,z7,z3,z4,z5])]],
   [[(0,[z6,z1,z7,z3,z4,z5,z489]),(0,[z6,z1,z7,z73,z3,z4,z5]),(0,[z6,z490,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z491]),(0,[z6,z1,z7,z3,z492,z4,z5]),(0,[z493,z6,z1,z7,z3,z4,z5]),(1,[z6,z249,z7,z3,z4,z5]),(0,[z94,z6,z1,z7,z3,z4,z109])],[(0,[z6,z355,z1,z23,z3,z4,z5])],[(0,[z135,z6,z1,z37,z3,z4,z5]),(0,[z235,z6,z1,z7,z3,z69,z5]),(0,[z6,z1,z7,z3,z494,z4,z5]),(0,[z16,z6,z1,z42,z3,z4,z5])],[(0,[z495,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z496,z5])],[(0,[z6,z1,z7,z3,z4,z5,z497]),(0,[z6,z498,z1,z7,z3,z4,z5])],[(0,[z28,z6,z1,z7,z3,z4,z5]),(0,[z132,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z499,z5]),(0,[z114,z6,z1,z24,z3,z4,z5]),(1,[z6,z383,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z125,z5]),(0,[z6,z1,z7,z3,z4,z5,z189]),(0,[z470,z16,z6,z1,z3,z4,z5])],[(1,[z6,z102,z1,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z125,z5]),(0,[z500,z6,z1,z7,z3,z4,z5])],[(0,[z13,z0,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z501,z3,z4,z5]),(0,[z6,z1,z7,z3,z502,z4,z5]),(0,[z118,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z23,z23,z3,z4,z5]),(0,[z6,z29,z1,z23,z3,z4,z5]),(0,[z503,z6,z1,z7,z3,z4,z5]),(0,[z504,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z505]),(0,[z6,z1,z7,z506,z3,z4,z5]),(0,[z6,z89,z1,z3,z4,z109,z5])]],
   [[(0,[z41,z13,z6,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z507,z5]),(0,[z6,z1,z7,z3,z508,z4,z5])],[(0,[z67,z16,z6,z1,z3,z4,z5]),(0,[z6,z35,z1,z3,z4,z5,z110]),(0,[z6,z1,z7,z509,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z510,z5]),(0,[z6,z1,z7,z511,z3,z4,z5]),(0,[z6,z1,z7,z512,z3,z4,z5]),(0,[z513,z6,z1,z7,z3,z4,z5]),(0,[z6,z514,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z515,z4,z5]),(0,[z516,z6,z1,z7,z3,z4,z5])],[(0,[z6,z517,z1,z7,z3,z4,z5]),(0,[z6,z518,z1,z7,z3,z4,z5]),(0,[z6,z9,z7,z3,z4,z5,z99]),(0,[z6,z1,z7,z3,z4,z263,z5]),(0,[z6,z519,z1,z7,z3,z4,z5])],[(0,[z520,z6,z1,z7,z3,z4,z5]),(0,[z521,z6,z1,z7,z3,z4,z5]),(0,[z522,z6,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z2,z3,z4,z5]),(0,[z16,z217,z6,z1,z3,z4,z5]),(0,[z6,z1,z452,z42,z3,z4,z5]),(0,[z6,z147,z1,z7,z3,z4,z5]),(0,[z16,z523,z6,z1,z3,z4,z5]),(0,[z6,z11,z7,z3,z4,z5,z95])],[(0,[z217,z6,z1,z7,z3,z4,z181]),(0,[z6,z1,z7,z3,z4,z524,z5]),(0,[z525,z6,z1,z7,z3,z4,z5])],[(0,[z41,z64,z6,z7,z3,z4,z5]),(0,[z6,z1,z526,z7,z3,z4,z5]),(0,[z224,z16,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z527,z4,z5])],[(0,[z41,z122,z6,z7,z3,z4,z5]),(0,[z16,z114,z6,z1,z3,z4,z5]),(0,[z12,z6,z147,z7,z3,z4,z5]),(0,[z6,z9,z1,z424,z3,z4,z5]),(0,[z6,z1,z7,z3,z528,z4,z5]),(1,[z6,z1,z211,z3,z4,z5]),(0,[z6,z44,z1,z7,z3,z214,z5]),(1,[z6,z343,z1,z3,z4,z5])],[(0,[z326,z6,z1,z7,z3,z4,z5]),(0,[z12,z6,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z24,z3,z4,z5])]],
   [[],[(0,[z6,z1,z7,z529,z3,z4,z5]),(0,[z6,z530,z1,z7,z3,z4,z5]),(0,[z94,z118,z6,z1,z7,z3,z4]),(0,[z6,z1,z7,z3,z451,z4,z5]),(1,[z6,z1,z531,z3,z4,z5]),(0,[z12,z6,z7,z3,z4,z125,z5]),(0,[z196,z6,z25,z1,z3,z4,z5]),(0,[z94,z6,z1,z7,z3,z4,z55])],[(0,[z0,z6,z35,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z532,z4,z5]),(0,[z6,z403,z1,z23,z3,z4,z5]),(0,[z6,z31,z1,z24,z3,z4,z5])],[(0,[z122,z64,z1,z7,z3,z4,z5]),(0,[z135,z235,z1,z7,z3,z4,z5]),(1,[z6,z1,z7,z3,z4,z97]),(0,[z6,z1,z7,z3,z4,z289,z5]),(0,[z13,z6,z1,z3,z4,z5,z99]),(0,[z6,z25,z1,z7,z3,z4,z5]),(0,[z6,z34,z1,z7,z3,z214,z5]),(1,[z6,z449,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z533,z4,z5]),(0,[z6,z31,z1,z7,z3,z5,z56])],[(0,[z6,z1,z85,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z4,z5]),(0,[z6,z1,z534,z7,z3,z4,z5]),(0,[z6,z44,z182,z7,z3,z4,z5])],[(0,[z6,z535,z1,z7,z3,z4,z5]),(0,[z6,z536,z1,z7,z3,z4,z5]),(0,[z6,z31,z1,z7,z3,z4,z55])],[],[(0,[z6,z25,z7,z23,z3,z4,z5]),(0,[z13,z6,z111,z1,z3,z4,z5]),(0,[z537,z6,z1,z7,z3,z4,z5]),(0,[z6,z34,z1,z3,z201,z4,z5]),(0,[z6,z1,z7,z19,z3,z78,z5]),(0,[z94,z6,z1,z7,z17,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z538])]],
   [[(0,[z539,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z540,z4,z5]),(0,[z126,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z541]),(0,[z6,z1,z23,z3,z14,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z301]),(0,[z6,z322,z72,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z542,z4,z5]),(0,[z6,z543,z1,z7,z3,z4,z5]),(0,[z6,z1,z452,z24,z3,z4,z5]),(0,[z6,z1,z544,z7,z3,z4,z5]),(0,[z6,z1,z7,z545,z3,z4,z5])],[(0,[z6,z546,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z214,z5]),(0,[z6,z1,z7,z547,z3,z4,z5]),(0,[z6,z1,z548,z7,z3,z4,z5])],[(0,[z122,z6,z1,z23,z3,z4,z5]),(0,[z16,z122,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z549,z5]),(1,[z6,z174,z23,z3,z4,z5]),(0,[z61,z6,z1,z24,z3,z4,z5]),(0,[z6,z34,z1,z7,z3,z201,z5]),(0,[z6,z1,z7,z3,z4,z5,z117])],[(0,[z550,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z2,z24,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z5,z110]),(0,[z6,z1,z7,z3,z4,z551,z5]),(0,[z6,z1,z7,z3,z552,z4,z5]),(0,[z264,z16,z6,z1,z3,z4,z5]),(0,[z6,z111,z1,z3,z4,z62,z5])],[(0,[z6,z553,z1,z7,z3,z4,z5]),(0,[z6,z1,z554,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z555]),(0,[z13,z6,z1,z3,z4,z62,z5]),(0,[z6,z1,z7,z3,z4,z5,z556]),(0,[z6,z1,z7,z3,z4,z557,z5]),(0,[z6,z31,z395,z1,z3,z4,z5])],[(0,[z558,z6,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z22,z5]),(0,[z559,z6,z1,z7,z3,z4,z5]),(0,[z48,z13,z6,z1,z3,z4,z5]),(0,[z53,z13,z6,z1,z3,z4,z5]),(0,[z98,z6,z1,z7,z3,z4,z5]),(1,[z6,z1,z7,z3,z4,z203]),(0,[z6,z1,z7,z3,z560,z4,z5])],[(0,[z6,z1,z1,z7,z3,z4,z5]),(1,[z401,z6,z1,z7,z3,z4]),(0,[z138,z6,z1,z23,z3,z4,z5]),(1,[z470,z6,z1,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z5,z95]),(0,[z6,z1,z7,z3,z4,z5,z561]),(0,[z94,z16,z6,z1,z3,z4,z5]),(0,[z562,z6,z1,z7,z3,z4,z5])],[(0,[z6,z1,z179,z3,z20,z4,z5])]],
   [[(0,[z6,z65,z1,z324,z3,z4,z5]),(0,[z0,z6,z1,z23,z3,z4,z5]),(0,[z217,z6,z1,z7,z3,z4,z5]),(0,[z563,z6,z1,z7,z3,z4,z5]),(0,[z6,z147,z7,z3,z14,z4,z5]),(0,[z564,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z565,z5])],[(0,[z566,z6,z1,z7,z3,z4,z5]),(0,[z135,z6,z1,z7,z3,z140,z5]),(1,[z41,z13,z6,z3,z4,z5]),(0,[z6,z1,z567,z7,z3,z4,z5]),(1,[z6,z9,z7,z3,z4,z99]),(0,[z6,z1,z24,z3,z380,z4,z5]),(1,[z6,z1,z3,z4,z5,z131])],[(0,[z6,z1,z7,z3,z4,z568,z5]),(0,[z132,z6,z1,z7,z20,z4,z5]),(0,[z114,z6,z1,z7,z20,z4,z5]),(0,[z6,z569,z1,z7,z3,z4,z5]),(0,[z570,z6,z1,z7,z3,z4,z5]),(0,[z6,z72,z7,z3,z4,z51,z5])],[(0,[z6,z1,z7,z3,z4,z5,z571]),(0,[z6,z1,z7,z572,z3,z4,z5]),(0,[z6,z573,z1,z7,z3,z4,z5]),(0,[z574,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z575,z5]),(0,[z6,z1,z7,z3,z4,z130,z5])],[(0,[z1,z7,z115,z3,z20,z4,z5]),(0,[z6,z1,z531,z7,z3,z4,z5])],[(0,[z6,z1,z2,z3,z4,z214,z5]),(0,[z576,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z577,z4,z5]),(0,[z6,z29,z111,z1,z3,z4,z5])],[(0,[z16,z6,z1,z3,z4,z69,z5]),(0,[z13,z13,z6,z1,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z172,z5]),(0,[z6,z578,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z579,z5])],[(0,[z6,z1,z7,z580,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z22,z56]),(0,[z13,z6,z1,z3,z175,z4,z5]),(0,[z336,z13,z6,z1,z3,z4,z5]),(0,[z6,z91,z1,z7,z3,z4,z252])]],
   [[(0,[z6,z581,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z86,z5]),(0,[z6,z1,z7,z3,z4,z582,z5]),(0,[z6,z583,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z584]),(0,[z6,z111,z1,z7,z3,z4,z62]),(0,[z6,z585,z1,z7,z3,z4,z5]),(0,[z586,z6,z1,z7,z3,z4,z5])],[(1,[z6,z168,z1,z3,z4,z5]),(0,[z135,z138,z6,z1,z7,z3,z5]),(1,[z293,z6,z1,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z5,z110]),(0,[z13,z6,z1,z3,z4,z51,z5]),(0,[z6,z29,z1,z3,z4,z5,z110])],[(0,[z6,z1,z23,z3,z4,z62,z5]),(0,[z6,z587,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z5,z110]),(0,[z6,z134,z1,z7,z3,z4,z5])],[(0,[z13,z64,z6,z1,z3,z4,z5]),(1,[z6,z1,z7,z3,z228,z4]),(0,[z135,z6,z1,z7,z3,z69,z5]),(0,[z13,z6,z1,z3,z78,z4,z5]),(1,[z6,z1,z588,z3,z4,z5]),(0,[z470,z6,z1,z42,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z62,z5])],[(1,[z6,z1,z165,z3,z4,z5]),(0,[z6,z1,z7,z589,z3,z4,z5]),(0,[z122,z6,z7,z23,z3,z4,z5]),(0,[z6,z34,z1,z2,z3,z4,z5]),(1,[z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z5,z95]),(0,[z6,z358,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z5,z590]),(0,[z6,z1,z7,z3,z4,z591,z5]),(0,[z6,z1,z24,z3,z4,z5,z95]),(0,[z6,z1,z182,z7,z3,z4,z5]),(0,[z6,z592,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z593,z3,z4,z5]),(0,[z41,z6,z7,z3,z26,z4,z5]),(0,[z13,z6,z91,z1,z3,z4,z5]),(0,[z6,z594,z1,z7,z3,z4,z5]),(0,[z6,z249,z1,z7,z3,z4,z5])],[(0,[z595,z6,z1,z7,z3,z4,z5]),(1,[z6,z1,z179,z3,z4,z5]),(0,[z235,z6,z1,z7,z3,z4,z5]),(0,[z6,z596,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z597,z5]),(0,[z16,z6,z1,z3,z3,z4,z5])]],
   [[(0,[z6,z412,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z228,z4,z5]),(0,[z6,z1,z7,z3,z4,z598,z5]),(0,[z599,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z600,z5]),(1,[z12,z6,z7,z26,z4,z5])],[(0,[z6,z1,z7,z3,z601,z4,z5]),(0,[z602,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z140,z4,z5]),(0,[z6,z1,z7,z603,z3,z4,z5]),(0,[z6,z91,z1,z7,z3,z14,z5]),(0,[z16,z6,z29,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z187,z5]),(1,[z6,z395,z1,z3,z4,z5])],[(0,[z6,z1,z604,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z605,z5]),(0,[z6,z1,z24,z3,z140,z4,z5]),(0,[z6,z7,z23,z3,z26,z4,z5]),(0,[z6,z1,z7,z17,z3,z4,z5])],[(0,[z6,z174,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z606,z5]),(0,[z6,z1,z7,z3,z14,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z607])],[(0,[z6,z1,z7,z255,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z608]),(0,[z6,z9,z72,z7,z3,z4,z5])],[(0,[z124,z16,z6,z1,z3,z4,z5]),(0,[z6,z609,z1,z7,z3,z4,z5]),(1,[z6,z44,z1,z3,z214,z5]),(0,[z6,z1,z7,z3,z610,z4,z5])],[(0,[z6,z611,z1,z7,z3,z4,z5]),(0,[z334,z6,z1,z7,z3,z4,z5]),(1,[z114,z1,z7,z115,z4,z5]),(0,[z16,z6,z1,z115,z3,z4,z5]),(0,[z6,z1,z7,z612,z3,z4,z5]),(0,[z6,z613,z1,z7,z3,z4,z5])],[(0,[z13,z6,z65,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z614,z4,z5]),(0,[z397,z6,z1,z7,z3,z20,z5]),(0,[z94,z217,z6,z1,z7,z3,z4]),(0,[z6,z1,z7,z615,z3,z4,z5]),(0,[z616,z6,z1,z7,z3,z4,z5]),(1,[z16,z6,z1,z3,z4,z5]),(0,[z6,z617,z1,z7,z3,z4,z5]),(0,[z618,z6,z1,z7,z3,z4,z5])]],
   [[(0,[z135,z6,z1,z7,z255,z4,z5]),(0,[z6,z619,z1,z7,z3,z4,z5]),(0,[z6,z620,z1,z7,z3,z4,z5]),(0,[z392,z6,z1,z7,z3,z4,z5]),(0,[z245,z6,z1,z7,z3,z4,z5]),(0,[z621,z6,z1,z7,z3,z4,z5]),(0,[z622,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z3,z201,z4,z214,z5])],[(0,[z132,z1,z7,z3,z20,z4,z5]),(0,[z6,z1,z7,z623,z3,z4,z5]),(0,[z6,z1,z588,z3,z26,z4,z5])],[(0,[z13,z118,z6,z1,z3,z4,z5]),(0,[z624,z6,z1,z7,z3,z4,z5])],[(0,[z6,z625,z1,z7,z3,z4,z5]),(0,[z626,z6,z1,z7,z3,z4,z5]),(0,[z135,z6,z1,z7,z19,z3,z5]),(0,[z235,z6,z1,z7,z3,z140,z5]),(0,[z6,z1,z7,z3,z380,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z627])],[(0,[z67,z6,z1,z24,z3,z4,z5]),(0,[z6,z383,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z405,z4,z5]),(0,[z6,z1,z7,z3,z4,z628,z5]),(1,[z6,z1,z3,z4,z238,z5]),(1,[z6,z1,z7,z17,z4,z109])],[(0,[z217,z6,z1,z7,z17,z3,z4]),(0,[z6,z629,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z630,z4,z5]),(0,[z16,z6,z1,z159,z3,z4,z5]),(1,[z334,z6,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z631]),(0,[z13,z6,z1,z3,z4,z55,z5]),(1,[z6,z1,z116,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z632,z5])],[(1,[z135,z1,z7,z3,z69,z5]),(0,[z41,z6,z147,z7,z3,z4,z5]),(0,[z6,z393,z1,z7,z3,z4,z5])]],
   [[(0,[z6,z1,z7,z3,z4,z5,z633]),(0,[z41,z6,z1,z7,z3,z4,z5]),(0,[z6,z147,z1,z23,z3,z4,z5]),(0,[z16,z6,z92,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z634,z5]),(0,[z6,z1,z7,z3,z78,z4,z33]),(0,[z6,z31,z427,z7,z3,z4,z5])],[(0,[z67,z13,z6,z1,z3,z4,z5]),(0,[z13,z6,z1,z3,z20,z4,z5]),(1,[z6,z1,z7,z3,z4,z365]),(0,[z6,z1,z23,z635,z3,z4,z5]),(0,[z6,z636,z1,z7,z3,z4,z5]),(2,[z6,z211,z3,z4,z5])],[(0,[z64,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z637,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z638,z5]),(0,[z135,z6,z1,z7,z21,z4,z5]),(1,[z6,z9,z23,z3,z4,z5]),(0,[z6,z1,z639,z7,z3,z4,z5])],[(1,[z67,z35,z1,z3,z4,z5]),(0,[z12,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z640]),(0,[z6,z1,z58,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z641,z4,z5]),(0,[z6,z1,z7,z3,z234,z4,z5]),(1,[z196,z6,z1,z3,z4,z5]),(1,[z6,z1,z7,z3,z560,z5]),(0,[z6,z1,z7,z3,z4,z99,z56]),(0,[z6,z1,z7,z3,z642,z4,z5]),(0,[z6,z643,z1,z7,z3,z4,z5])],[(0,[z6,z7,z23,z3,z4,z125,z5]),(0,[z13,z6,z1,z3,z276,z4,z5]),(0,[z6,z1,z7,z398,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z5,z505])],[(0,[z64,z6,z1,z165,z3,z4,z5]),(0,[z64,z6,z7,z42,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z644,z5]),(0,[z6,z1,z645,z7,z3,z4,z5]),(0,[z6,z1,z7,z19,z3,z86,z5]),(0,[z6,z1,z7,z3,z15,z4,z5])]],
   [[(0,[z6,z25,z1,z23,z3,z4,z5]),(1,[z6,z1,z266,z3,z4,z5]),(0,[z6,z91,z147,z7,z3,z4,z5]),(0,[z6,z1,z646,z7,z3,z4,z5]),(0,[z6,z92,z1,z7,z3,z4,z5]),(0,[z6,z44,z1,z7,z3,z4,z5])],[(0,[z13,z6,z1,z19,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z5,z56]),(0,[z6,z91,z1,z7,z3,z4,z5]),(0,[z647,z6,z1,z7,z3,z4,z5]),(0,[z6,z9,z1,z24,z3,z4,z5]),(0,[z6,z363,z1,z3,z4,z5,z95]),(0,[z6,z648,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z649,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z252]),(0,[z6,z1,z7,z3,z4,z5,z650]),(0,[z6,z1,z7,z3,z4,z5,z651]),(0,[z6,z1,z7,z652,z3,z4,z5])],[(0,[z64,z6,z159,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z653,z5]),(0,[z13,z6,z1,z3,z201,z4,z5]),(0,[z6,z1,z7,z3,z4,z654,z5]),(0,[z16,z6,z147,z1,z3,z4,z5]),(0,[z6,z72,z1,z24,z3,z4,z5]),(0,[z138,z6,z1,z7,z3,z78,z5]),(0,[z6,z1,z7,z3,z655,z4,z5]),(0,[z94,z6,z1,z7,z4,z5,z95]),(0,[z6,z1,z7,z3,z656,z4,z5])],[(0,[z401,z6,z1,z7,z3,z20,z4]),(0,[z6,z1,z7,z3,z140,z4,z5]),(0,[z6,z1,z23,z3,z4,z55,z5]),(0,[z6,z1,z23,z3,z248,z4,z5]),(1,[z6,z241,z1,z7,z3,z4]),(0,[z6,z657,z1,z7,z3,z4,z5])],[(0,[z6,z65,z1,z7,z3,z4,z5]),(0,[z658,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z659,z5]),(0,[z6,z1,z24,z3,z248,z4,z5]),(0,[z6,z1,z24,z3,z4,z55,z5]),(0,[z6,z34,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z660])],[(0,[z6,z1,z7,z3,z661,z4,z5]),(0,[z135,z6,z85,z7,z3,z4,z5]),(1,[z235,z1,z7,z3,z140,z5]),(0,[z13,z6,z1,z3,z4,z109,z5]),(0,[z6,z1,z7,z588,z3,z4,z5]),(0,[z6,z9,z7,z42,z3,z4,z5]),(0,[z264,z6,z1,z24,z3,z4,z5])],[(0,[z662,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z663,z5]),(0,[z6,z1,z23,z3,z20,z4,z5]),(0,[z664,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z26,z4,z5]),(0,[z16,z6,z211,z7,z3,z4,z5]),(0,[z16,z6,z1,z58,z3,z4,z5]),(0,[z6,z1,z7,z4,z109,z5,z95])]],
   [[(0,[z6,z1,z7,z3,z665,z4,z5]),(0,[z6,z1,z24,z3,z20,z4,z5]),(0,[z666,z6,z1,z7,z3,z4,z5]),(0,[z550,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z17,z3,z4,z95])],[(0,[z6,z1,z7,z3,z4,z667,z5]),(0,[z94,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z454,z7,z3,z4,z5])],[(0,[z6,z35,z1,z24,z3,z4,z5]),(0,[z6,z147,z7,z23,z3,z4,z5]),(0,[z262,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z424,z3,z4,z5]),(1,[z6,z72,z7,z3,z4,z125]),(0,[z411,z16,z6,z1,z3,z4,z5])],[(0,[z118,z6,z1,z7,z3,z4,z181]),(0,[z6,z1,z1,z23,z3,z4,z5]),(0,[z264,z13,z6,z1,z3,z4,z5]),(0,[z12,z6,z9,z7,z3,z4,z5]),(1,[z6,z1,z178,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z668,z5]),(0,[z6,z1,z7,z3,z4,z5,z669])],[(0,[z6,z1,z7,z3,z4,z5,z670]),(0,[z6,z1,z23,z3,z671,z4,z5]),(0,[z6,z137,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z202,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z205])],[(0,[z672,z6,z1,z7,z3,z4,z5]),(0,[z235,z6,z1,z7,z19,z3,z5]),(0,[z217,z6,z1,z23,z3,z4,z5]),(1,[z6,z25,z23,z3,z4,z5]),(0,[z470,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z238,z86,z5]),(1,[z6,z427,z7,z3,z4,z5])],[(0,[z118,z6,z1,z7,z3,z4,z22]),(0,[z6,z1,z7,z3,z4,z55,z22]),(0,[z94,z13,z6,z1,z3,z4,z5]),(0,[z12,z6,z1,z531,z3,z4,z5]),(0,[z138,z16,z6,z1,z3,z4,z5]),(0,[z673,z6,z1,z7,z3,z4,z5])],[(0,[z6,z184,z1,z3,z20,z4,z5]),(0,[z114,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z23,z19,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z5,z56]),(0,[z13,z6,z1,z42,z3,z4,z5]),(1,[z6,z311,z1,z3,z4,z5]),(0,[z16,z6,z44,z1,z3,z4,z5]),(1,[z6,z1,z7,z3,z4,z381]),(0,[z6,z1,z7,z3,z674,z4,z5])]],
   [[(0,[z6,z1,z7,z3,z675,z4,z5]),(0,[z135,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z181]),(0,[z676,z6,z1,z7,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z331,z5]),(0,[z6,z1,z24,z19,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z5,z56]),(0,[z6,z1,z7,z3,z677,z4,z5]),(0,[z6,z1,z7,z3,z4,z678,z5])],[],[(1,[z6,z1,z324,z3,z4,z5]),(1,[z6,z393,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z679])],[(0,[z16,z6,z1,z3,z4,z557,z5]),(0,[z6,z1,z7,z3,z4,z680,z5])],[(0,[z6,z1,z7,z635,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z681,z5]),(0,[z6,z1,z23,z3,z4,z109,z5]),(0,[z6,z1,z7,z452,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z682,z5]),(0,[z468,z13,z6,z1,z3,z4,z5]),(0,[z471,z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z71,z7,z3,z4,z5]),(0,[z16,z6,z371,z1,z3,z4,z5]),(0,[z6,z1,z7,z19,z78,z4,z5])],[(0,[z6,z683,z1,z7,z3,z4,z5]),(0,[z217,z118,z1,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z52,z5]),(0,[z6,z1,z7,z3,z684,z4,z5]),(0,[z6,z1,z24,z3,z4,z109,z5])],[(1,[z6,z1,z7,z3,z4,z402]),(0,[z6,z685,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z686,z4,z5]),(0,[z6,z111,z1,z2,z3,z4,z5]),(0,[z687,z6,z1,z7,z3,z4,z5])]],
   [[(0,[z13,z6,z1,z2,z3,z4,z5]),(0,[z6,z343,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z688,z4,z5])],[(0,[z6,z1,z7,z136,z3,z4,z5])],[],[(0,[z13,z114,z6,z1,z3,z4,z5]),(0,[z16,z235,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z125,z5]),(0,[z16,z6,z92,z7,z3,z4,z5]),(0,[z6,z111,z1,z24,z3,z4,z5])],[(0,[z6,z1,z37,z7,z3,z4,z5]),(0,[z235,z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z5,z99]),(0,[z13,z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z402,z5])],[(0,[z6,z689,z1,z7,z3,z4,z5]),(0,[z132,z6,z1,z7,z3,z4,z5]),(0,[z114,z6,z1,z7,z3,z4,z5]),(0,[z217,z6,z1,z256,z3,z4,z5]),(0,[z6,z1,z23,z42,z3,z4,z5]),(0,[z6,z1,z7,z23,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z5,z99]),(0,[z6,z1,z7,z3,z690,z4,z5])],[(0,[z135,z1,z7,z3,z4,z69,z5]),(0,[z691,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z24,z42,z3,z4,z5]),(0,[z6,z1,z7,z3,z692,z4,z5])],[(0,[z6,z159,z7,z3,z4,z51,z5]),(0,[z6,z1,z159,z24,z3,z4,z5]),(0,[z6,z693,z1,z7,z3,z4,z5]),(0,[z694,z6,z1,z7,z3,z4,z5]),(0,[z118,z6,z1,z7,z3,z4,z5]),(0,[z16,z6,z174,z1,z3,z4,z5]),(0,[z6,z9,z1,z7,z3,z560,z5]),(0,[z16,z6,z1,z3,z4,z582,z5]),(0,[z6,z1,z7,z3,z248,z4,z5])]],
   [[(0,[z6,z35,z100,z7,z3,z4,z5]),(0,[z695,z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z696,z5]),(1,[z6,z1,z7,z3,z15,z55])],[(0,[z697,z6,z1,z7,z3,z4,z5]),(0,[z6,z453,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z698,z5])],[(0,[z6,z699,z1,z7,z3,z4,z5]),(1,[z6,z1,z24,z3,z4,z5]),(0,[z700,z6,z1,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z701,z5]),(0,[z6,z1,z7,z3,z702,z4,z5]),(0,[z6,z449,z111,z7,z3,z4,z5])],[(1,[z6,z184,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z703,z4,z5]),(0,[z6,z1,z7,z3,z4,z5,z5]),(0,[z118,z1,z7,z3,z4,z22,z5]),(0,[z229,z6,z1,z7,z3,z4,z5]),(0,[z6,z147,z7,z3,z4,z5,z99]),(0,[z138,z6,z1,z7,z19,z4,z5]),(1,[z6,z1,z7,z19,z78,z5])],[(0,[z6,z1,z7,z3,z704,z4,z5]),(0,[z6,z111,z1,z3,z4,z214,z5])],[(1,[z6,z412,z1,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z214,z5]),(0,[z12,z6,z1,z7,z26,z4,z5]),(1,[z6,z147,z7,z3,z14,z5]),(0,[z6,z210,z1,z7,z3,z4,z5])],[(0,[z6,z705,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z671,z4,z5]),(1,[z16,z6,z1,z24,z4,z5]),(0,[z523,z6,z1,z7,z3,z4,z5]),(0,[z16,z6,z1,z7,z3,z4,z5]),(0,[z149,z6,z1,z24,z3,z4,z5]),(0,[z6,z706,z1,z7,z3,z4,z5]),(0,[z6,z31,z1,z120,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z6,z707,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z708]),(0,[z6,z1,z42,z398,z4,z5]),(0,[z16,z6,z182,z3,z4,z5]),(0,[z16,z6,z454,z3,z4,z5]),(0,[z6,z709,z1,z3,z4,z5])],[(0,[z6,z1,z7,z710,z4,z5]),(0,[z6,z1,z24,z255,z4,z5]),(0,[z6,z211,z24,z3,z4,z5])],[(0,[z6,z1,z7,z711,z4,z5]),(0,[z6,z241,z1,z23,z3,z4]),(0,[z6,z712,z7,z3,z4,z5])],[(0,[z6,z1,z157,z3,z4,z5]),(0,[z6,z25,z452,z3,z4,z5]),(0,[z6,z393,z23,z3,z4,z5])],[(0,[z6,z270,z23,z3,z4,z5]),(0,[z16,z6,z3,z4,z130,z5])],[(0,[z12,z6,z588,z26,z4,z5]),(0,[z6,z1,z7,z3,z10,z5]),(0,[z6,z713,z7,z3,z4,z5]),(0,[z53,z6,z182,z3,z4,z5])],[(0,[z6,z714,z7,z3,z4,z5])],[(0,[z6,z1,z23,z3,z4,z402])],[(0,[z1,z7,z715,z20,z4,z5]),(0,[z135,z16,z1,z3,z69,z5]),(0,[z6,z241,z1,z24,z3,z4]),(0,[z6,z716,z7,z3,z4,z5])],[(0,[z6,z23,z3,z4,z644,z5]),(0,[z6,z717,z7,z3,z4,z5]),(0,[z6,z1,z3,z718,z4,z5]),(0,[z48,z453,z1,z3,z4,z5]),(0,[z13,z6,z11,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z719]),(0,[z6,z445,z1,z7,z3,z56]),(0,[z6,z31,z211,z3,z4,z5])],[(0,[z6,z1,z720,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z721])],[(0,[z6,z1,z7,z3,z4,z722]),(0,[z6,z1,z37,z255,z4,z5]),(0,[z6,z211,z3,z4,z214,z5])],[(0,[z397,z6,z1,z7,z3,z228]),(0,[z12,z6,z7,z3,z10,z5]),(0,[z6,z1,z427,z7,z3,z56])],[(0,[z6,z72,z211,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z723])],[(0,[z235,z1,z7,z3,z527,z5]),(0,[z6,z311,z1,z3,z4,z5]),(0,[z6,z7,z3,z4,z10,z99]),(0,[z6,z1,z7,z3,z4,z381])],[(0,[z6,z35,z211,z3,z4,z5]),(0,[z6,z358,z452,z3,z4,z5])]],
   [[(0,[z724,z6,z1,z21,z4,z5]),(0,[z6,z24,z3,z4,z5,z725])],[(0,[z6,z585,z23,z3,z4,z5]),(0,[z196,z6,z23,z3,z4,z5]),(1,[z6,z1,z726,z4,z5]),(0,[z6,z454,z24,z3,z4,z5]),(0,[z6,z1,z727,z3,z4,z5]),(0,[z6,z1,z7,z17,z4,z728])],[(0,[z6,z210,z1,z3,z4,z5]),(0,[z6,z729,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z730]),(0,[z6,z1,z731,z3,z4,z5])],[(0,[z6,z1,z7,z732,z4,z5])],[(0,[z6,z85,z7,z255,z4,z5]),(0,[z733,z6,z1,z3,z4,z5]),(0,[z16,z6,z11,z3,z4,z5]),(0,[z6,z249,z24,z3,z4,z5]),(0,[z6,z734,z1,z3,z4,z5])],[(0,[z6,z7,z3,z4,z5,z735]),(0,[z736,z6,z1,z3,z4,z5]),(0,[z6,z92,z24,z3,z4,z5]),(0,[z6,z34,z211,z3,z4,z5])],[(0,[z6,z737,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z738]),(0,[z6,z1,z3,z4,z62,z739]),(0,[z6,z1,z7,z3,z688,z55])],[(0,[z6,z1,z23,z3,z228,z4]),(0,[z6,z740,z1,z3,z4,z5]),(0,[z6,z741,z1,z3,z4,z5]),(0,[z6,z1,z3,z742,z4,z5])],[(0,[z293,z6,z1,z24,z4,z5]),(0,[z6,z1,z743,z3,z4,z5]),(0,[z6,z744,z7,z3,z4,z5]),(0,[z6,z745,z1,z3,z4,z5])],[(0,[z746,z6,z1,z3,z4,z5]),(0,[z470,z6,z25,z42,z4,z5]),(0,[z16,z747,z1,z3,z4,z5]),(0,[z6,z1,z3,z4,z62,z173])],[(0,[z748,z6,z1,z3,z4,z5]),(0,[z336,z6,z23,z3,z4,z5]),(0,[z6,z240,z1,z3,z671,z5]),(0,[z6,z23,z3,z4,z678,z5]),(0,[z6,z1,z749,z3,z4,z5]),(0,[z6,z346,z7,z3,z51,z5]),(0,[z6,z211,z3,z4,z86,z5])],[(0,[z6,z1,z750,z3,z4,z5]),(0,[z6,z1,z751,z3,z4,z5]),(0,[z6,z25,z211,z3,z4,z5]),(0,[z6,z147,z7,z3,z4,z252]),(0,[z6,z29,z1,z3,z4,z110])],[(0,[z6,z23,z3,z4,z5,z538]),(0,[z470,z6,z92,z3,z4,z5]),(0,[z6,z1,z7,z78,z752,z5])],[(0,[z6,z249,z7,z3,z4,z33])],[(0,[z6,z1,z7,z3,z753,z5]),(0,[z6,z1,z7,z3,z4,z754]),(0,[z6,z755,z1,z3,z4,z5])],[(0,[z6,z342,z23,z3,z4,z5]),(0,[z6,z1,z756,z3,z4,z5])]],
   [[],[(0,[z0,z6,z100,z3,z4,z5]),(0,[z6,z1,z3,z4,z757,z5]),(0,[z758,z6,z383,z3,z4,z5]),(0,[z6,z34,z1,z3,z175,z5]),(0,[z6,z1,z759,z3,z4,z5]),(0,[z6,z760,z1,z3,z4,z5])],[(0,[z6,z761,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z762]),(0,[z6,z763,z211,z3,z4,z5])],[(0,[z57,z6,z1,z24,z4,z5]),(0,[z53,z6,z1,z3,z175,z5])],[],[(0,[z764,z6,z168,z3,z4,z5]),(0,[z6,z241,z7,z23,z3,z4]),(0,[z6,z147,z7,z3,z14,z5]),(0,[z6,z1,z17,z4,z109,z131])],[(0,[z6,z1,z765,z3,z4,z5]),(0,[z6,z766,z1,z3,z4,z5]),(0,[z6,z1,z767,z3,z4,z5]),(0,[z6,z1,z768,z3,z4,z5]),(0,[z6,z1,z769,z3,z4,z5]),(0,[z6,z770,z1,z3,z4,z5]),(0,[z138,z6,z211,z3,z4,z5]),(0,[z16,z6,z1,z24,z4,z5])],[(0,[z94,z6,z363,z1,z4,z95])],[(0,[z415,z65,z7,z3,z4,z5]),(0,[z6,z211,z115,z3,z4,z5]),(0,[z6,z1,z771,z3,z4,z5]),(0,[z6,z23,z3,z692,z4,z5]),(0,[z6,z23,z3,z4,z130,z5]),(0,[z6,z1,z23,z17,z4,z109])],[(0,[z326,z35,z1,z3,z4,z5]),(0,[z6,z772,z7,z3,z4,z5]),(0,[z6,z1,z7,z21,z4,z5]),(0,[z773,z6,z1,z3,z4,z5])],[(0,[z16,z6,z449,z3,z4,z5])],[(0,[z6,z1,z37,z3,z4,z5]),(0,[z6,z774,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z775,z56])],[(0,[z94,z6,z1,z7,z377,z4]),(0,[z6,z776,z1,z3,z4,z5]),(0,[z16,z777,z1,z3,z4,z5]),(0,[z6,z1,z7,z19,z78,z45])],[(0,[z6,z1,z23,z3,z4,z365]),(0,[z6,z1,z3,z4,z5,z778])],[(0,[z6,z355,z23,z3,z4,z125]),(0,[z12,z6,z531,z26,z4,z5])],[(0,[z6,z7,z3,z51,z99,z56]),(0,[z779,z6,z1,z3,z4,z5]),(0,[z6,z7,z3,z4,z130,z33])]],
   [[(0,[z6,z211,z159,z3,z4,z5]),(0,[z6,z780,z1,z3,z4,z5]),(0,[z6,z1,z781,z3,z4,z5]),(0,[z6,z1,z3,z782,z4,z5]),(0,[z16,z6,z1,z3,z4,z783]),(0,[z6,z1,z7,z726,z4,z5])],[(0,[z784,z6,z1,z3,z4,z5]),(0,[z122,z403,z23,z3,z4,z5]),(0,[z6,z785,z7,z3,z4,z5]),(0,[z6,z1,z786,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z203]),(0,[z6,z1,z787,z3,z4,z5])],[(0,[z122,z788,z7,z3,z4,z5]),(0,[z6,z789,z1,z3,z4,z5]),(0,[z16,z217,z1,z3,z4,z181])],[(0,[z6,z1,z3,z4,z263,z110])],[(0,[z6,z85,z7,z3,z4,z5]),(0,[z401,z13,z6,z1,z3,z4]),(0,[z6,z168,z790,z3,z4,z5]),(0,[z13,z235,z1,z3,z140,z5])],[(0,[z791,z6,z1,z3,z4,z5]),(0,[z397,z16,z6,z1,z3,z5]),(0,[z13,z114,z1,z115,z4,z5]),(0,[z6,z792,z1,z3,z4,z5]),(0,[z6,z23,z3,z4,z600,z5]),(0,[z6,z9,z24,z3,z4,z99]),(0,[z94,z6,z1,z7,z4,z95])],[(0,[z6,z1,z793,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z203])],[(0,[z64,z6,z452,z3,z4,z5]),(0,[z6,z794,z1,z3,z4,z5]),(0,[z94,z6,z11,z7,z3,z4])],[(0,[z122,z6,z452,z3,z4,z5]),(0,[z6,z1,z795,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z796]),(0,[z6,z1,z797,z3,z4,z5]),(0,[z6,z798,z1,z3,z4,z5]),(0,[z13,z6,z454,z3,z4,z5]),(0,[z6,z211,z3,z4,z5,z505]),(0,[z6,z34,z1,z3,z201,z5])],[(0,[z6,z1,z7,z3,z799,z5]),(0,[z217,z1,z7,z3,z4,z800]),(0,[z801,z6,z174,z3,z4,z5]),(0,[z460,z6,z1,z24,z4,z5])],[(0,[z6,z7,z3,z4,z5,z117]),(0,[z802,z6,z1,z3,z4,z5]),(0,[z6,z803,z249,z3,z4,z5])],[(0,[z6,z804,z1,z3,z4,z5]),(0,[z6,z1,z7,z805,z4,z5]),(0,[z574,z6,z1,z7,z3,z56]),(0,[z6,z111,z211,z3,z4,z5]),(0,[z6,z34,z1,z3,z4,z381]),(0,[z6,z1,z120,z3,z4,z5])],[(0,[z6,z806,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z807,z5]),(0,[z13,z6,z3,z4,z130,z5])],[(0,[z6,z808,z7,z3,z4,z5]),(0,[z6,z1,z7,z19,z327,z5]),(0,[z6,z211,z3,z26,z4,z5]),(0,[z6,z1,z46,z3,z4,z203]),(0,[z6,z1,z7,z3,z4,z809]),(0,[z6,z1,z3,z4,z5,z739])],[(0,[z64,z101,z7,z3,z4,z5]),(0,[z6,z23,z3,z75,z4,z5])],[(0,[z135,z1,z7,z3,z69,z97]),(0,[z16,z235,z1,z3,z140,z5]),(0,[z6,z25,z7,z80,z4,z5])]],
   [[(0,[z16,z114,z1,z115,z4,z5]),(0,[z6,z47,z23,z3,z4,z5]),(0,[z196,z6,z25,z42,z4,z5]),(0,[z6,z34,z1,z3,z610,z5])],[(0,[z6,z427,z23,z3,z4,z5])],[(0,[z6,z436,z7,z3,z51,z5]),(0,[z6,z363,z1,z3,z4,z5])],[(0,[z6,z23,z3,z630,z4,z5]),(0,[z6,z166,z1,z3,z4,z110]),(0,[z6,z613,z23,z3,z4,z5]),(0,[z196,z6,z92,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z810])],[(0,[z6,z1,z7,z811,z4,z5]),(0,[z6,z11,z7,z17,z3,z4])],[(0,[z6,z23,z3,z4,z634,z5]),(0,[z6,z812,z1,z3,z4,z5])],[(0,[z122,z65,z7,z3,z4,z5]),(0,[z67,z813,z1,z3,z4,z5]),(0,[z814,z6,z23,z3,z4,z5]),(0,[z6,z1,z24,z80,z4,z5]),(0,[z13,z6,z1,z3,z4,z815]),(0,[z6,z46,z3,z4,z51,z5]),(0,[z6,z1,z7,z3,z816,z4])],[(0,[z6,z1,z817,z3,z4,z5]),(0,[z6,z1,z179,z3,z228,z4]),(0,[z293,z6,z211,z3,z4,z5])],[(0,[z6,z25,z7,z42,z4,z5]),(0,[z6,z1,z818,z3,z4,z5]),(0,[z16,z6,z1,z3,z819,z5])],[(0,[z16,z6,z1,z3,z15,z55])],[(0,[z64,z159,z23,z3,z4,z5]),(0,[z758,z6,z1,z3,z4,z5]),(0,[z217,z1,z7,z3,z4,z181]),(0,[z6,z1,z7,z3,z4,z820]),(0,[z6,z23,z3,z642,z4,z5]),(0,[z13,z6,z211,z3,z4,z5]),(0,[z16,z6,z1,z39,z4,z5])],[(0,[z6,z1,z821,z3,z4,z5]),(0,[z132,z7,z74,z20,z4,z5]),(0,[z6,z25,z116,z3,z4,z5])],[(0,[z6,z1,z822,z3,z4,z5]),(0,[z94,z293,z6,z1,z4,z5]),(0,[z6,z823,z1,z3,z4,z5]),(0,[z41,z6,z211,z3,z4,z5]),(0,[z824,z6,z1,z3,z4,z5]),(0,[z13,z6,z249,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z825]),(0,[z6,z826,z24,z3,z4,z5]),(0,[z6,z449,z111,z3,z4,z62])],[(0,[z6,z827,z7,z3,z4,z5]),(0,[z1,z7,z3,z140,z828,z5]),(0,[z829,z6,z1,z3,z4,z5]),(0,[z6,z182,z7,z3,z4,z5]),(0,[z6,z1,z58,z398,z4,z5]),(0,[z6,z72,z7,z3,z10,z5]),(0,[z6,z31,z134,z7,z3,z56])],[(0,[z6,z23,z3,z4,z144,z5]),(0,[z6,z1,z7,z3,z4,z830]),(0,[z6,z1,z831,z21,z4,z5])],[(0,[z64,z6,z211,z3,z4,z5]),(0,[z764,z6,z7,z3,z4,z5]),(0,[z6,z832,z1,z3,z4,z5]),(0,[z6,z833,z3,z4,z86,z5])]],
   [[(0,[z6,z1,z834,z3,z4,z5]),(0,[z401,z6,z1,z7,z3,z234]),(0,[z6,z23,z3,z4,z654,z5]),(0,[z6,z1,z835,z3,z4,z5]),(0,[z6,z147,z73,z3,z4,z5]),(0,[z6,z31,z427,z7,z3,z56])],[(0,[z6,z1,z836,z3,z4,z5]),(0,[z122,z7,z3,z494,z4,z5]),(0,[z6,z1,z23,z3,z234,z5]),(0,[z293,z6,z1,z42,z4,z5]),(0,[z6,z1,z23,z3,z4,z252]),(0,[z6,z1,z837,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z838]),(0,[z6,z839,z7,z3,z4,z5]),(0,[z6,z840,z7,z3,z4,z5]),(0,[z334,z6,z24,z3,z4,z5]),(0,[z6,z91,z211,z3,z4,z5]),(0,[z6,z1,z841,z3,z4,z5])],[(0,[z6,z1,z3,z842,z4,z5]),(0,[z6,z211,z23,z3,z4,z5]),(0,[z6,z9,z7,z3,z560,z99]),(1,[z6,z427,z7,z3,z56])],[(0,[z6,z1,z3,z4,z5,z843]),(0,[z6,z134,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z844]),(0,[z16,z6,z211,z3,z4,z5]),(0,[z6,z29,z454,z3,z4,z5]),(0,[z6,z427,z7,z3,z4,z56])],[(0,[z16,z6,z1,z675,z4,z5]),(0,[z6,z845,z1,z3,z4,z5]),(0,[z846,z6,z1,z3,z4,z5]),(0,[z6,z9,z7,z3,z4,z479]),(0,[z6,z1,z58,z24,z4,z5])],[(0,[z6,z1,z7,z3,z4,z847]),(0,[z293,z6,z1,z248,z4,z5]),(0,[z16,z6,z249,z3,z4,z5]),(0,[z6,z848,z7,z3,z4,z5]),(0,[z6,z849,z3,z4,z109,z5])],[(1,[z813,z1,z3,z4,z5]),(0,[z67,z35,z100,z3,z4,z5]),(0,[z6,z1,z23,z19,z78,z5]),(0,[z6,z102,z1,z3,z4,z252]),(0,[z16,z6,z850,z3,z4,z5])],[(0,[z6,z211,z3,z4,z582,z5])],[(0,[z6,z1,z136,z21,z4,z5])],[(0,[z6,z65,z211,z3,z4,z5]),(0,[z132,z6,z211,z3,z4,z5]),(0,[z397,z6,z1,z7,z3,z5]),(0,[z6,z1,z7,z851,z4,z5]),(0,[z6,z79,z7,z3,z51,z5]),(0,[z94,z6,z11,z7,z4,z95])],[(0,[z6,z383,z24,z3,z4,z5]),(0,[z6,z852,z1,z3,z4,z5]),(0,[z6,z853,z1,z3,z4,z5]),(0,[z6,z11,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z854]),(0,[z6,z9,z7,z3,z10,z99]),(0,[z6,z1,z3,z4,z443,z110]),(0,[z6,z1,z855,z3,z4,z5])],[(0,[z6,z1,z856,z3,z4,z5]),(0,[z6,z1,z857,z3,z4,z5]),(0,[z6,z211,z3,z858,z4,z5])],[(0,[z132,z334,z7,z20,z4,z5]),(0,[z118,z6,z211,z3,z4,z5]),(0,[z13,z6,z1,z3,z560,z5]),(0,[z126,z6,z211,z3,z4,z5]),(0,[z16,z6,z827,z3,z4,z5]),(0,[z6,z454,z3,z4,z214,z5]),(0,[z6,z1,z859,z3,z4,z5])],[(0,[z6,z484,z1,z3,z214,z5])]],
   [[(0,[z16,z6,z1,z242,z4,z5]),(0,[z16,z6,z713,z3,z4,z5])],[(0,[z6,z347,z23,z3,z4,z5]),(0,[z6,z23,z3,z4,z219,z5])],[(0,[z235,z1,z24,z3,z140,z5]),(0,[z6,z860,z1,z3,z4,z5]),(0,[z13,z6,z449,z3,z4,z5]),(0,[z94,z6,z1,z7,z528,z4]),(0,[z6,z393,z7,z3,z4,z402]),(0,[z861,z6,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z862,z5]),(0,[z6,z863,z7,z3,z4,z5]),(0,[z864,z6,z24,z3,z4,z5])],[(0,[z6,z1,z7,z865,z4,z5]),(0,[z6,z383,z7,z21,z4,z5]),(0,[z866,z6,z1,z3,z4,z5]),(0,[z6,z241,z7,z42,z3,z4]),(0,[z6,z1,z7,z3,z867,z5]),(0,[z6,z211,z3,z14,z4,z5])],[(0,[z6,z85,z136,z3,z4,z5]),(0,[z16,z6,z1,z248,z4,z5])],[(0,[z6,z383,z37,z3,z4,z5]),(0,[z6,z868,z7,z3,z4,z5])],[(0,[z6,z23,z3,z242,z4,z5]),(0,[z6,z92,z23,z3,z4,z5]),(0,[z6,z343,z1,z19,z78,z5])],[(0,[z13,z6,z91,z3,z51,z5]),(0,[z126,z371,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z869,z4]),(0,[z870,z6,z1,z7,z4,z5]),(0,[z1,z7,z3,z4,z5,z800]),(0,[z6,z147,z452,z3,z4,z5]),(0,[z16,z6,z1,z3,z560,z5]),(0,[z16,z6,z1,z702,z4,z5]),(0,[z871,z6,z1,z3,z4,z5])],[(0,[z132,z1,z23,z20,z4,z5]),(0,[z6,z23,z3,z4,z251,z5]),(0,[z6,z427,z7,z3,z5,z56])],[(0,[z872,z6,z1,z3,z4,z5]),(0,[z96,z6,z23,z3,z4,z5]),(0,[z6,z25,z23,z26,z4,z5]),(0,[z873,z1,z7,z3,z4,z5])],[(0,[z6,z1,z874,z3,z4,z5]),(0,[z16,z6,z1,z3,z875,z5]),(0,[z411,z6,z1,z3,z4,z505]),(0,[z6,z876,z7,z3,z4,z5])],[(0,[z135,z1,z7,z3,z69,z365]),(0,[z6,z1,z23,z4,z5,z877]),(0,[z186,z6,z1,z3,z304,z5]),(0,[z6,z7,z3,z4,z5,z725])],[(0,[z401,z334,z6,z7,z3,z4]),(0,[z6,z23,z3,z4,z125,z56]),(0,[z6,z536,z23,z3,z4,z5])],[(0,[z6,z1,z7,z878,z4,z5]),(0,[z6,z1,z790,z3,z4,z5])]],
   [[(0,[z788,z159,z7,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z381]),(0,[z6,z879,z1,z3,z4,z5])],[(0,[z6,z241,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z656,z56])],[(0,[z6,z880,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z881]),(0,[z16,z6,z1,z3,z10,z5])],[(0,[z6,z1,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z5,z882]),(0,[z6,z79,z1,z3,z289,z5]),(0,[z6,z1,z3,z4,z883,z5]),(0,[z16,z6,z91,z3,z51,z5]),(0,[z576,z6,z9,z7,z3,z4])],[(0,[z12,z13,z6,z26,z4,z5]),(0,[z6,z25,z452,z42,z4,z5])],[(0,[z6,z9,z23,z3,z560,z5]),(0,[z884,z6,z1,z7,z4,z5]),(0,[z28,z6,z211,z3,z4,z5]),(0,[z6,z211,z3,z4,z5,z110]),(0,[z6,z484,z1,z7,z3,z56])],[(0,[z885,z6,z1,z3,z4,z5]),(0,[z6,z1,z886,z3,z4,z5]),(0,[z6,z1,z7,z3,z887,z5]),(0,[z6,z322,z1,z3,z4,z5]),(0,[z6,z1,z3,z4,z888,z5]),(0,[z6,z44,z1,z3,z889,z5])],[(0,[z94,z6,z1,z23,z4,z95]),(0,[z890,z6,z1,z3,z4,z5])],[(0,[z6,z211,z3,z15,z4,z5]),(0,[z298,z6,z1,z24,z4,z5])],[(0,[z6,z1,z7,z19,z295,z5]),(0,[z6,z891,z1,z3,z4,z5]),(0,[z6,z44,z1,z3,z214,z381])],[(0,[z6,z7,z3,z892,z4,z5]),(0,[z6,z893,z7,z3,z4,z5]),(0,[z6,z102,z1,z3,z4,z5]),(0,[z41,z801,z6,z3,z4,z5])],[(0,[z6,z23,z3,z4,z299,z5]),(0,[z16,z6,z1,z3,z4,z381]),(0,[z6,z7,z3,z4,z894,z5])],[(0,[z13,z334,z6,z3,z4,z5]),(0,[z6,z1,z895,z3,z4,z5]),(0,[z6,z1,z24,z3,z15,z55])],[(0,[z6,z1,z7,z3,z4,z896]),(0,[z98,z6,z23,z3,z4,z5]),(0,[z6,z79,z1,z3,z214,z5]),(0,[z94,z6,z1,z24,z4,z95])],[(0,[z6,z1,z7,z3,z897,z5]),(0,[z334,z6,z720,z3,z4,z5]),(0,[z6,z1,z898,z3,z4,z5]),(0,[z6,z1,z899,z3,z4,z5]),(0,[z6,z9,z23,z3,z10,z5])],[(0,[z64,z6,z116,z3,z4,z5])]],
   [[(0,[z293,z6,z1,z452,z4,z5]),(0,[z6,z3,z4,z130,z187,z5])],[(0,[z622,z1,z2,z3,z4,z5]),(0,[z6,z1,z179,z3,z234,z5]),(0,[z6,z91,z23,z3,z51,z5]),(0,[z6,z1,z7,z3,z900,z5]),(0,[z13,z6,z1,z3,z15,z55])],[(0,[z6,z901,z1,z3,z4,z5]),(1,[z1,z7,z3,z828,z5]),(0,[z6,z343,z1,z3,z4,z5]),(0,[z6,z1,z3,z4,z187,z5]),(0,[z773,z6,z3,z4,z130,z5])],[(0,[z64,z339,z159,z3,z4,z5]),(0,[z6,z1,z7,z3,z202,z4]),(0,[z16,z6,z1,z3,z4,z738]),(0,[z138,z6,z1,z238,z86,z5])],[(0,[z6,z184,z1,z3,z228,z4]),(0,[z217,z6,z211,z3,z4,z5]),(0,[z523,z6,z211,z3,z4,z5]),(0,[z6,z902,z1,z3,z4,z5]),(0,[z6,z7,z3,z4,z5,z903])],[(0,[z6,z904,z1,z3,z4,z5]),(0,[z6,z905,z7,z3,z4,z5]),(0,[z471,z6,z1,z3,z172,z5]),(0,[z6,z906,z7,z3,z4,z5])],[(0,[z6,z907,z7,z3,z4,z5]),(0,[z6,z23,z3,z4,z331,z5])],[(0,[z6,z604,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z908,z5]),(0,[z229,z1,z2,z3,z4,z5]),(0,[z909,z6,z1,z3,z4,z5]),(0,[z16,z334,z6,z3,z4,z5]),(0,[z114,z6,z211,z3,z4,z5]),(0,[z6,z449,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z910]),(0,[z6,z850,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z33])],[(0,[z6,z1,z24,z191,z4,z5]),(0,[z6,z911,z1,z3,z4,z5]),(0,[z6,z73,z3,z4,z125,z5])],[(0,[z293,z64,z6,z3,z4,z5]),(0,[z6,z912,z1,z7,z3,z4])],[(0,[z6,z913,z7,z3,z4,z5]),(0,[z6,z23,z3,z15,z51,z5]),(0,[z6,z914,z1,z7,z3,z4]),(0,[z915,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z45]),(0,[z6,z11,z363,z3,z4,z5]),(0,[z6,z849,z7,z3,z4,z5])],[(0,[z13,z6,z1,z21,z4,z5])],[(0,[z6,z1,z7,z916,z4,z5]),(0,[z6,z1,z7,z3,z4,z917]),(0,[z918,z6,z7,z3,z4,z5]),(0,[z6,z1,z3,z380,z4,z5]),(0,[z6,z137,z1,z3,z4,z301]),(0,[z6,z240,z1,z3,z201,z5]),(0,[z41,z6,z7,z3,z10,z5]),(0,[z13,z6,z1,z3,z4,z33]),(0,[z6,z919,z7,z3,z4,z5]),(0,[z6,z1,z920,z3,z4,z5])],[(0,[z64,z6,z707,z3,z4,z5]),(0,[z6,z921,z7,z3,z4,z5]),(0,[z114,z1,z24,z115,z4,z5]),(0,[z6,z1,z922,z3,z4,z5]),(0,[z16,z6,z211,z24,z4,z5]),(0,[z6,z1,z3,z4,z923,z5])],[(0,[z6,z133,z1,z3,z4,z110])],[(0,[z217,z1,z256,z3,z4,z181]),(0,[z293,z6,z9,z3,z4,z5]),(0,[z6,z1,z7,z3,z924,z5]),(0,[z6,z7,z3,z4,z130,z45])]],
   [[(0,[z6,z1,z7,z3,z925,z5]),(0,[z6,z1,z71,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z926])],[(0,[z6,z1,z927,z3,z4,z5])],[],[(0,[z122,z6,z211,z3,z4,z5]),(0,[z12,z6,z3,z380,z4,z5]),(0,[z6,z928,z1,z3,z4,z5])],[(0,[z6,z100,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z929]),(0,[z6,z7,z3,z74,z228,z4]),(0,[z94,z13,z6,z1,z4,z95]),(0,[z6,z211,z3,z4,z125,z5]),(0,[z6,z930,z1,z3,z4,z5])],[(0,[z931,z6,z1,z3,z4,z5]),(0,[z235,z1,z7,z3,z828,z5]),(0,[z6,z1,z3,z932,z4,z5]),(0,[z6,z9,z73,z3,z4,z5])],[(0,[z16,z6,z1,z21,z4,z5]),(0,[z6,z1,z23,z255,z4,z5])],[(0,[z16,z6,z1,z529,z4,z5]),(0,[z6,z1,z398,z3,z4,z5]),(0,[z293,z6,z23,z26,z4,z5]),(0,[z6,z1,z23,z3,z933,z4]),(0,[z470,z6,z1,z276,z4,z5]),(0,[z16,z6,z1,z3,z4,z33])],[(0,[z6,z240,z23,z3,z51,z5])],[(0,[z6,z1,z934,z3,z4,z5]),(0,[z6,z29,z1,z3,z4,z189]),(0,[z6,z1,z7,z4,z752,z5])],[(0,[z132,z1,z179,z20,z4,z5]),(0,[z6,z1,z935,z3,z4,z5]),(0,[z6,z23,z3,z4,z51,z5]),(0,[z1,z7,z3,z4,z5,z936])],[(0,[z64,z6,z324,z3,z4,z5]),(0,[z6,z1,z7,z17,z432,z4]),(0,[z6,z1,z120,z3,z4,z55])],[(0,[z6,z937,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z560,z5])],[(0,[z397,z6,z1,z23,z3,z5]),(0,[z6,z646,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z51,z252]),(0,[z16,z6,z1,z726,z4,z5])],[(0,[z1,z7,z3,z715,z4,z5]),(0,[z6,z7,z3,z867,z51,z5])],[(0,[z6,z1,z938,z3,z4,z5]),(0,[z6,z939,z1,z3,z4,z5]),(0,[z6,z488,z23,z3,z4,z5]),(0,[z6,z1,z588,z3,z4,z5]),(1,[z6,z1,z3,z4,z739])]],
   [[(0,[z6,z211,z940,z3,z4,z5])],[(0,[z122,z412,z65,z3,z4,z5]),(0,[z6,z1,z941,z3,z4,z5]),(1,[z6,z7,z3,z51,z252])],[(0,[z6,z1,z942,z3,z4,z5]),(0,[z943,z6,z1,z3,z4,z5]),(0,[z94,z6,z1,z4,z205,z95])],[(0,[z6,z1,z179,z3,z4,z5]),(0,[z397,z6,z1,z24,z3,z5]),(0,[z6,z452,z3,z380,z4,z5]),(0,[z6,z1,z424,z3,z4,z5]),(0,[z88,z6,z1,z3,z282,z5]),(0,[z16,z6,z31,z1,z3,z56])],[(0,[z493,z1,z2,z3,z4,z5]),(0,[z6,z44,z1,z3,z172,z5]),(0,[z12,z6,z7,z26,z4,z5])],[(0,[z6,z619,z23,z3,z4,z5]),(0,[z277,z6,z23,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z944]),(0,[z6,z1,z945,z3,z4,z5]),(0,[z6,z1,z24,z3,z10,z5]),(0,[z6,z1,z946,z3,z4,z5])],[(0,[z6,z454,z23,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z947]),(0,[z948,z1,z7,z3,z4,z5]),(0,[z12,z6,z7,z528,z4,z5]),(0,[z1,z7,z3,z4,z949,z5])],[(0,[z6,z1,z3,z4,z950,z5])],[(0,[z6,z707,z1,z3,z4,z5])],[(0,[z217,z250,z1,z7,z3,z4]),(0,[z6,z249,z23,z3,z4,z5]),(0,[z468,z326,z1,z3,z4,z5]),(0,[z6,z7,z42,z4,z5,z294]),(0,[z6,z427,z951,z3,z4,z5])],[(0,[z6,z1,z7,z255,z4,z97]),(0,[z217,z13,z1,z3,z4,z181]),(0,[z6,z23,z3,z4,z243,z5]),(0,[z13,z6,z1,z3,z10,z5]),(0,[z6,z7,z42,z3,z10,z5]),(0,[z6,z952,z1,z3,z4,z5]),(0,[z6,z29,z211,z3,z4,z5]),(0,[z6,z953,z7,z3,z4,z5])],[(0,[z48,z6,z23,z3,z4,z5]),(0,[z6,z954,z1,z3,z4,z5]),(0,[z293,z6,z3,z4,z51,z5]),(0,[z6,z1,z7,z3,z955,z5]),(1,[z6,z7,z3,z867,z5]),(0,[z6,z291,z7,z3,z4,z99])],[(0,[z6,z7,z3,z10,z5,z99])],[(0,[z67,z6,z100,z3,z4,z5]),(0,[z6,z464,z23,z3,z4,z5]),(0,[z118,z1,z7,z3,z63,z4]),(0,[z6,z956,z7,z3,z4,z5])],[(0,[z6,z9,z452,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z719]),(0,[z537,z13,z6,z3,z4,z5]),(0,[z6,z7,z3,z4,z125,z399]),(0,[z6,z1,z3,z4,z957,z5]),(0,[z6,z147,z178,z3,z14,z5]),(0,[z6,z1,z24,z3,z4,z381])],[(0,[z6,z1,z958,z3,z4,z5]),(0,[z6,z1,z959,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z721]),(0,[z6,z1,z960,z3,z4,z5])]],
   [[(0,[z6,z1,z961,z3,z4,z5]),(0,[z6,z962,z7,z3,z4,z5])],[(0,[z6,z1,z963,z3,z4,z5])],[(0,[z6,z1,z3,z964,z4,z5]),(0,[z114,z1,z157,z115,z4,z5]),(0,[z6,z386,z23,z3,z4,z5]),(0,[z6,z241,z1,z588,z3,z4]),(0,[z6,z965,z7,z3,z4,z5])],[(0,[z135,z1,z7,z3,z69,z5]),(0,[z6,z1,z7,z966,z4,z5]),(0,[z293,z6,z25,z3,z4,z5])],[(0,[z6,z1,z7,z967,z4,z5]),(0,[z6,z968,z1,z3,z4,z5])],[(0,[z6,z969,z7,z3,z4,z5]),(0,[z6,z1,z3,z4,z889,z5]),(0,[z6,z1,z7,z19,z752,z5])],[(1,[z6,z790,z3,z4,z5]),(0,[z6,z72,z7,z3,z4,z243]),(0,[z16,z6,z147,z3,z14,z5]),(0,[z6,z1,z3,z4,z5,z970])],[(0,[z6,z971,z1,z7,z3,z5]),(0,[z6,z452,z3,z26,z4,z5]),(0,[z884,z6,z1,z23,z4,z5]),(0,[z6,z972,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z973]),(0,[z6,z1,z3,z4,z214,z381]),(0,[z6,z249,z3,z4,z187,z5])],[(0,[z6,z23,z3,z4,z456,z5]),(0,[z6,z1,z974,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z975]),(0,[z6,z1,z976,z3,z4,z5]),(0,[z196,z6,z1,z3,z4,z5]),(0,[z6,z211,z3,z4,z62,z5])],[(0,[z6,z1,z977,z3,z4,z5]),(0,[z6,z1,z978,z3,z4,z5]),(0,[z979,z6,z1,z3,z4,z5])],[(0,[z6,z339,z23,z3,z4,z5]),(0,[z6,z23,z3,z4,z5,z294]),(0,[z13,z801,z6,z3,z4,z5]),(0,[z16,z6,z1,z492,z4,z5])],[],[(0,[z397,z6,z1,z7,z19,z5]),(1,[z6,z886,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z980]),(0,[z16,z6,z134,z3,z4,z5])],[(0,[z397,z6,z184,z1,z3,z5]),(0,[z6,z981,z1,z3,z4,z5]),(0,[z16,z6,z1,z297,z4,z5]),(0,[z6,z1,z7,z3,z4,z739])],[(0,[z94,z6,z9,z23,z3,z4]),(0,[z6,z1,z982,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z983])]],
   [[(0,[z6,z984,z7,z3,z4,z5]),(0,[z6,z71,z211,z3,z4,z5]),(0,[z16,z6,z427,z3,z4,z5]),(0,[z6,z249,z7,z3,z4,z45])],[(0,[z6,z985,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z986]),(0,[z6,z1,z7,z3,z4,z987]),(0,[z6,z1,z7,z3,z14,z252]),(0,[z264,z6,z211,z3,z4,z5])],[(0,[z6,z1,z24,z434,z4,z5])],[(0,[z6,z23,z3,z4,z314,z5]),(0,[z122,z6,z116,z3,z4,z5]),(0,[z67,z96,z35,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z988]),(0,[z6,z1,z989,z3,z4,z5]),(0,[z12,z6,z241,z7,z3,z4]),(0,[z6,z1,z3,z4,z5,z990]),(0,[z6,z7,z3,z4,z5,z991])],[(0,[z6,z147,z211,z3,z4,z5]),(0,[z6,z31,z395,z1,z3,z56])],[(0,[z6,z992,z1,z3,z4,z5]),(0,[z6,z147,z24,z3,z14,z5])],[(0,[z16,z6,z85,z3,z4,z5]),(0,[z801,z6,z23,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z203]),(0,[z6,z42,z3,z380,z4,z5]),(0,[z6,z72,z7,z3,z4,z125]),(0,[z6,z1,z993,z3,z4,z5])],[(0,[z6,z1,z994,z3,z4,z5]),(0,[z788,z1,z7,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z762]),(0,[z149,z1,z285,z3,z4,z5])],[(0,[z472,z6,z23,z3,z4,z5]),(0,[z6,z995,z1,z3,z4,z5]),(0,[z6,z1,z531,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z996])],[(0,[z6,z1,z7,z3,z4,z997]),(0,[z6,z1,z24,z21,z4,z5]),(0,[z6,z1,z7,z3,z218,z55]),(0,[z6,z1,z7,z3,z4,z998]),(0,[z6,z1,z3,z201,z304,z5]),(0,[z6,z454,z3,z4,z62,z5]),(0,[z6,z999,z1,z3,z4,z5])],[(0,[z6,z1000,z1,z3,z4,z5]),(0,[z6,z1001,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z97]),(0,[z6,z9,z23,z3,z4,z99]),(0,[z6,z1,z19,z78,z187,z5])],[(0,[z6,z452,z3,z4,z125,z5]),(0,[z6,z1,z3,z4,z1002,z5]),(0,[z6,z1003,z134,z3,z4,z5])],[(0,[z6,z1,z1004,z3,z4,z5]),(0,[z16,z6,z211,z248,z4,z5]),(0,[z6,z1,z3,z200,z214,z5])],[(0,[z132,z16,z1,z20,z4,z5]),(0,[z6,z291,z23,z3,z4,z5]),(0,[z6,z102,z1,z3,z4,z203])],[(0,[z6,z7,z3,z74,z234,z5]),(0,[z6,z393,z7,z3,z4,z5]),(0,[z6,z1005,z1,z3,z4,z5]),(0,[z6,z24,z3,z4,z1006,z5])],[(0,[z6,z1007,z1,z3,z4,z5])]],
   [[(0,[z135,z13,z1,z3,z69,z5]),(0,[z487,z6,z23,z3,z4,z5]),(0,[z6,z210,z1,z3,z560,z5]),(0,[z6,z44,z211,z3,z4,z5]),(0,[z6,z1,z24,z726,z4,z5])],[(0,[z6,z1,z1008,z3,z4,z5]),(0,[z1009,z6,z1,z3,z4,z5]),(0,[z6,z1,z1010,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z402]),(0,[z6,z1,z1011,z3,z4,z5]),(0,[z6,z1,z1012,z3,z4,z5])],[(0,[z6,z316,z23,z3,z4,z5]),(0,[z16,z401,z6,z1,z3,z4]),(0,[z6,z1,z37,z21,z4,z5]),(0,[z6,z1,z1013,z3,z4,z5]),(0,[z6,z113,z1014,z3,z4,z5]),(0,[z6,z1,z1015,z3,z4,z5])],[(0,[z6,z85,z24,z3,z4,z5]),(0,[z6,z9,z23,z17,z3,z4]),(0,[z13,z6,z446,z3,z4,z5]),(0,[z6,z72,z7,z3,z677,z4]),(0,[z6,z1016,z211,z3,z4,z5])],[(0,[z470,z6,z1,z3,z4,z5]),(0,[z6,z23,z3,z533,z4,z5]),(0,[z6,z9,z7,z3,z4,z1017]),(0,[z6,z371,z211,z3,z4,z5])],[(0,[z122,z65,z324,z3,z4,z5]),(0,[z6,z24,z3,z74,z4,z5]),(0,[z135,z1,z7,z255,z69,z5]),(0,[z6,z7,z3,z4,z125,z1017]),(0,[z28,z523,z1,z3,z4,z5])],[(0,[z6,z1018,z7,z3,z4,z5])],[(0,[z6,z1,z7,z255,z4,z365]),(0,[z138,z16,z6,z1,z86,z5])],[(0,[z6,z7,z3,z4,z1019,z5]),(0,[z6,z210,z1,z3,z10,z5]),(0,[z6,z72,z73,z3,z4,z125])],[(0,[z6,z1,z7,z3,z828,z5]),(0,[z404,z6,z7,z3,z51,z5]),(0,[z6,z1020,z1,z3,z4,z5]),(0,[z6,z182,z7,z3,z4,z381]),(0,[z6,z1021,z1,z3,z4,z5])],[(0,[z6,z1,z951,z3,z4,z5]),(0,[z13,z6,z31,z1,z3,z56]),(0,[z6,z211,z3,z4,z55,z5]),(0,[z6,z343,z3,z4,z130,z5])],[(0,[z6,z85,z7,z21,z4,z5]),(0,[z6,z23,z3,z4,z5,z117]),(0,[z6,z1022,z7,z3,z4,z5])],[(0,[z149,z1,z2,z3,z4,z5]),(0,[z6,z23,z3,z4,z390,z5]),(0,[z777,z1,z7,z3,z4,z5])],[(0,[z104,z6,z23,z3,z4,z5]),(0,[z6,z211,z3,z20,z4,z5]),(0,[z6,z85,z37,z3,z4,z5]),(0,[z94,z6,z1,z7,z4,z607])],[(0,[z122,z6,z324,z3,z4,z5]),(0,[z6,z7,z3,z4,z5,z1017]),(0,[z16,z1023,z1,z3,z4,z5])]],
   [[(0,[z566,z6,z23,z3,z4,z5]),(0,[z6,z184,z1,z3,z4,z5]),(0,[z6,z168,z1,z3,z4,z5]),(0,[z6,z1,z1024,z3,z4,z5]),(0,[z6,z1025,z1,z3,z4,z5]),(0,[z6,z1026,z1,z3,z4,z5]),(0,[z6,z174,z211,z3,z4,z5]),(0,[z6,z7,z3,z1027,z4,z5]),(0,[z6,z1,z7,z3,z1028,z5])],[(0,[z6,z100,z3,z4,z214,z5]),(0,[z94,z6,z1,z7,z3,z10])],[(0,[z6,z1,z7,z3,z228,z4]),(0,[z6,z7,z3,z1029,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1030]),(0,[z6,z1,z24,z3,z4,z810])],[(0,[z6,z1031,z7,z3,z4,z5]),(0,[z401,z6,z7,z3,z74,z4]),(0,[z135,z1,z136,z3,z69,z5]),(0,[z6,z1,z1032,z3,z4,z5]),(0,[z6,z211,z3,z282,z4,z5])],[(0,[z96,z6,z339,z3,z4,z5]),(0,[z6,z1033,z7,z3,z4,z5]),(0,[z13,z6,z1,z3,z202,z4])],[(0,[z122,z65,z24,z3,z4,z5]),(0,[z466,z35,z1,z3,z4,z5]),(0,[z6,z184,z3,z74,z4,z5]),(0,[z1034,z6,z7,z3,z4,z5]),(0,[z6,z23,z3,z4,z5,z409]),(0,[z13,z6,z220,z3,z4,z5]),(0,[z6,z1035,z1,z3,z4,z5])],[(0,[z6,z1,z32,z3,z4,z5]),(0,[z334,z6,z23,z3,z4,z5]),(0,[z1036,z6,z1,z3,z4,z5]),(0,[z6,z1,z3,z4,z1037,z5]),(0,[z576,z16,z6,z1,z4,z5]),(0,[z199,z1,z3,z405,z4,z5]),(0,[z6,z1,z7,z3,z4,z775])],[(0,[z6,z1,z7,z3,z4,z1038]),(0,[z6,z23,z3,z4,z410,z5]),(0,[z6,z25,z24,z42,z4,z5]),(0,[z6,z211,z3,z201,z4,z5]),(0,[z6,z395,z1,z3,z4,z5])],[(0,[z6,z147,z46,z3,z4,z5]),(0,[z16,z6,z72,z3,z4,z125]),(0,[z6,z1039,z211,z3,z4,z5])],[(0,[z6,z7,z3,z4,z5,z1040]),(0,[z217,z1,z24,z3,z4,z181]),(0,[z6,z180,z23,z3,z4,z5])],[(0,[z6,z1,z1041,z3,z4,z5]),(0,[z6,z1,z1042,z3,z4,z5]),(0,[z6,z211,z3,z4,z109,z5]),(0,[z6,z1,z1043,z3,z4,z5])],[(0,[z813,z1,z2,z3,z4,z5]),(1,[z1,z7,z715,z4,z5]),(0,[z13,z6,z1,z3,z4,z45]),(0,[z6,z1,z3,z4,z1044,z5])],[(0,[z6,z182,z24,z3,z4,z5]),(0,[z6,z1045,z7,z3,z4,z5])],[(0,[z814,z6,z1,z3,z4,z5]),(0,[z6,z1,z726,z248,z4,z5]),(0,[z6,z1046,z1,z3,z4,z5])],[]],
   [[(0,[z6,z7,z3,z74,z4,z5]),(0,[z13,z6,z3,z4,z5,z117]),(0,[z16,z6,z1,z3,z202,z4]),(0,[z6,z7,z3,z4,z5,z1047]),(0,[z6,z89,z1,z17,z4,z109])],[(0,[z6,z1048,z1,z7,z3,z5]),(0,[z6,z383,z23,z3,z4,z5]),(0,[z12,z6,z7,z202,z26,z4])],[(0,[z6,z1049,z1,z3,z4,z5]),(0,[z6,z1,z1050,z3,z4,z5])],[(0,[z6,z813,z1,z3,z4,z5]),(0,[z48,z6,z100,z3,z4,z5]),(0,[z6,z147,z23,z3,z51,z5]),(0,[z6,z1,z3,z4,z238,z5]),(0,[z6,z1,z7,z17,z4,z109])],[(0,[z16,z64,z159,z3,z4,z5]),(0,[z6,z1,z7,z4,z5,z1051]),(0,[z6,z23,z3,z438,z4,z5]),(0,[z6,z147,z116,z3,z4,z5]),(0,[z6,z134,z24,z3,z4,z5]),(0,[z1052,z6,z3,z4,z5,z117]),(0,[z6,z134,z759,z3,z4,z5])],[(0,[z13,z6,z134,z3,z4,z5]),(0,[z6,z1,z3,z1053,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1054]),(0,[z6,z1055,z1,z3,z4,z5]),(0,[z6,z1,z1056,z3,z4,z5]),(0,[z6,z211,z3,z4,z1057,z5])],[(0,[z235,z1,z23,z3,z140,z5]),(0,[z6,z9,z23,z3,z4,z125]),(0,[z6,z1,z1058,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z45]),(0,[z6,z1,z7,z3,z4,z1059]),(0,[z6,z182,z3,z4,z214,z5]),(0,[z6,z1060,z1,z3,z4,z5])],[(0,[z6,z1,z7,z1061,z4,z5]),(0,[z6,z1,z7,z3,z4,z365]),(0,[z13,z6,z427,z3,z4,z5]),(0,[z6,z9,z210,z3,z4,z99])],[(0,[z6,z1,z7,z3,z4,z1062]),(0,[z6,z1,z7,z3,z1063,z4]),(0,[z1064,z6,z1,z3,z4,z5]),(0,[z6,z355,z7,z3,z4,z125])],[(0,[z6,z324,z3,z4,z51,z5]),(0,[z586,z1,z7,z3,z4,z181]),(0,[z6,z1,z7,z17,z349,z4]),(0,[z6,z9,z424,z3,z4,z99])],[(0,[z67,z35,z1,z3,z4,z5]),(0,[z6,z1,z136,z3,z4,z97]),(0,[z6,z137,z1,z3,z4,z110]),(0,[z6,z355,z1,z3,z4,z62]),(0,[z224,z6,z1,z3,z582,z5]),(0,[z16,z6,z3,z4,z5,z117])],[(0,[z6,z1,z7,z3,z1065,z4]),(0,[z122,z403,z7,z3,z4,z5]),(0,[z6,z383,z899,z3,z4,z5]),(0,[z6,z141,z23,z26,z4,z5])],[(0,[z6,z211,z2,z3,z4,z5]),(0,[z397,z13,z6,z1,z3,z5]),(0,[z6,z1,z1066,z3,z4,z5])],[(0,[z13,z6,z85,z3,z4,z5]),(0,[z6,z1067,z1,z3,z4,z5]),(0,[z6,z1,z1068,z3,z4,z5])],[(0,[z6,z1014,z7,z3,z4,z5])]],
   [[(0,[z6,z1,z23,z3,z4,z381]),(0,[z1069,z6,z1,z3,z4,z5])],[(0,[z6,z184,z1,z3,z234,z5]),(0,[z293,z6,z1,z451,z4,z5]),(0,[z6,z1070,z7,z3,z4,z5])],[(0,[z6,z1,z3,z4,z1071,z5]),(0,[z6,z1,z7,z19,z21,z5]),(1,[z6,z241,z23,z3,z4]),(0,[z6,z1,z1072,z3,z4,z5])],[],[(0,[z470,z6,z1,z398,z4,z5]),(0,[z6,z1,z1073,z3,z4,z5]),(0,[z12,z6,z7,z269,z4,z5]),(0,[z1074,z6,z1,z3,z4,z5])],[(0,[z1075,z6,z1,z3,z4,z5])],[(0,[z135,z6,z211,z3,z4,z5])],[(0,[z1076,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1077]),(0,[z6,z1078,z1,z7,z3,z4]),(0,[z6,z1,z231,z3,z4,z263]),(0,[z6,z249,z1010,z3,z4,z5])],[(0,[z6,z790,z7,z3,z4,z5]),(0,[z53,z6,z23,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1079]),(0,[z6,z1080,z7,z3,z4,z5]),(0,[z6,z7,z3,z4,z1081,z5]),(0,[z6,z7,z3,z4,z5,z1082]),(0,[z6,z23,z3,z4,z5,z497]),(0,[z6,z25,z266,z42,z4,z5]),(0,[z6,z1083,z1,z3,z4,z5]),(0,[z6,z9,z211,z3,z4,z5]),(0,[z6,z3,z4,z5,z205,z117])],[(0,[z6,z1084,z1,z7,z3,z4]),(0,[z6,z1085,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1086]),(0,[z293,z122,z6,z3,z4,z5]),(0,[z6,z34,z100,z3,z4,z5]),(0,[z6,z1,z7,z3,z1087,z5]),(0,[z6,z1,z1088,z3,z4,z5]),(0,[z6,z1089,z7,z3,z4,z5]),(0,[z6,z134,z395,z3,z4,z5])],[(0,[z6,z1,z1090,z3,z4,z5]),(0,[z6,z25,z23,z3,z4,z5]),(0,[z6,z427,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z1091,z5])],[(0,[z6,z34,z1,z3,z478,z5]),(0,[z1092,z6,z1,z3,z4,z5]),(0,[z6,z23,z3,z4,z507,z5])],[(0,[z6,z1093,z1,z3,z4,z5]),(0,[z6,z1094,z1,z3,z4,z5]),(0,[z6,z1,z73,z3,z4,z5]),(0,[z6,z1,z7,z1027,z4,z5]),(0,[z6,z1,z1095,z3,z4,z5]),(0,[z6,z7,z42,z4,z390,z5]),(0,[z6,z134,z120,z3,z4,z5])],[(0,[z6,z211,z3,z4,z22,z5]),(0,[z6,z488,z7,z3,z14,z5]),(0,[z1096,z6,z1,z3,z4,z5])]],
   [[(0,[z6,z147,z324,z3,z4,z5]),(0,[z6,z1,z1097,z3,z4,z5]),(0,[z6,z1098,z7,z3,z4,z5]),(0,[z1023,z1,z7,z3,z4,z5]),(0,[z6,z1,z58,z726,z4,z5])],[(0,[z6,z23,z3,z26,z4,z5]),(0,[z6,z1,z23,z3,z15,z55]),(0,[z6,z147,z7,z3,z379,z5]),(0,[z6,z111,z1,z3,z4,z739]),(0,[z6,z1,z3,z4,z1099,z5])],[],[(0,[z6,z23,z3,z528,z4,z5]),(0,[z6,z1100,z1,z3,z4,z5]),(0,[z41,z6,z3,z380,z4,z5]),(0,[z16,z6,z1,z512,z4,z5])],[(0,[z6,z1,z3,z4,z5,z1101])],[(0,[z64,z159,z7,z3,z4,z5]),(0,[z1,z7,z3,z4,z828,z5]),(0,[z6,z1,z1102,z3,z4,z5])],[(0,[z6,z1,z7,z3,z1103,z5]),(0,[z334,z6,z1104,z3,z4,z5])],[(0,[z6,z1,z1105,z3,z4,z5]),(0,[z334,z6,z179,z3,z4,z5]),(0,[z1106,z6,z1,z3,z4,z5]),(0,[z229,z1,z635,z3,z4,z5]),(0,[z6,z1,z141,z24,z4,z5]),(0,[z41,z6,z71,z3,z4,z5]),(0,[z6,z1,z1107,z3,z4,z5]),(0,[z336,z6,z454,z3,z4,z5])],[(0,[z132,z401,z1,z7,z20,z4]),(0,[z1108,z6,z1,z3,z4,z5]),(0,[z6,z211,z3,z4,z69,z5]),(0,[z6,z358,z23,z3,z4,z5]),(0,[z336,z6,z1,z3,z4,z189]),(0,[z12,z6,z116,z26,z4,z5]),(0,[z6,z1,z7,z3,z10,z99])],[(0,[z6,z1,z7,z3,z4,z1109]),(0,[z6,z311,z147,z3,z14,z5])],[(0,[z122,z13,z65,z3,z4,z5]),(0,[z132,z184,z1,z20,z4,z5]),(0,[z6,z1110,z7,z3,z4,z5]),(0,[z6,z699,z23,z3,z4,z5]),(0,[z6,z23,z3,z677,z4,z5]),(0,[z6,z163,z7,z3,z51,z5])],[(0,[z6,z1111,z1,z3,z4,z5]),(0,[z6,z1,z369,z24,z4,z5])],[(0,[z6,z1,z7,z3,z234,z5]),(0,[z6,z1,z23,z3,z4,z33]),(0,[z6,z1,z7,z3,z4,z252]),(0,[z16,z6,z1,z4,z5,z561])],[(0,[z16,z6,z1112,z3,z4,z5])],[(0,[z1108,z6,z3,z74,z4,z5]),(0,[z6,z1,z1113,z3,z4,z5]),(0,[z6,z348,z23,z3,z4,z5]),(0,[z6,z1,z424,z3,z560,z5]),(0,[z6,z1,z3,z4,z5,z1114])],[(0,[z6,z1,z7,z3,z4,z1115]),(0,[z6,z1,z24,z547,z4,z5])]],
   [[(0,[z6,z1116,z7,z3,z4,z5]),(0,[z6,z23,z3,z4,z551,z5])],[(0,[z6,z23,z3,z686,z4,z5]),(0,[z13,z6,z72,z3,z4,z125]),(0,[z6,z211,z3,z3,z4,z5]),(0,[z6,z3,z4,z5,z980,z117])],[(0,[z114,z1,z23,z115,z4,z5]),(0,[z293,z6,z3,z26,z4,z5]),(0,[z6,z1,z1117,z3,z4,z5])],[(0,[z6,z1,z7,z3,z1118,z5]),(0,[z6,z1,z1119,z3,z4,z5]),(0,[z415,z6,z23,z3,z4,z5]),(0,[z6,z1,z24,z3,z202,z4]),(0,[z6,z1,z1120,z3,z4,z5]),(0,[z6,z1121,z7,z3,z4,z5]),(0,[z6,z1,z7,z19,z78,z5])],[],[(0,[z6,z412,z1,z3,z4,z5]),(0,[z6,z1,z1122,z3,z4,z5]),(0,[z6,z23,z3,z4,z125,z5]),(0,[z6,z1123,z7,z3,z4,z5]),(0,[z6,z1124,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z15,z775])],[(0,[z6,z7,z3,z4,z1017,z99])],[(0,[z6,z1,z1125,z3,z4,z5]),(0,[z13,z6,z25,z42,z4,z5]),(0,[z6,z11,z7,z3,z4,z5]),(0,[z16,z6,z714,z3,z4,z5]),(0,[z6,z449,z24,z3,z4,z5]),(0,[z6,z1,z7,z4,z5,z728])],[(0,[z6,z1126,z1,z7,z3,z4]),(0,[z41,z6,z210,z3,z4,z5])],[(0,[z6,z100,z23,z3,z4,z5]),(0,[z6,z1,z136,z3,z4,z365]),(0,[z13,z6,z330,z3,z4,z5]),(0,[z6,z1,z1127,z3,z4,z5]),(0,[z6,z24,z3,z4,z130,z5]),(0,[z6,z1,z24,z4,z5,z627])],[(0,[z132,z1,z7,z234,z20,z5]),(0,[z6,z1,z7,z3,z4,z1128]),(0,[z13,z6,z92,z3,z4,z5]),(0,[z6,z91,z7,z3,z51,z252]),(0,[z6,z1,z24,z3,z4,z45])],[(0,[z0,z6,z211,z3,z4,z5]),(0,[z6,z23,z3,z4,z698,z5]),(0,[z6,z1,z7,z3,z4,z1129]),(0,[z6,z7,z3,z4,z1006,z5]),(0,[z6,z1,z3,z4,z187,z33]),(0,[z6,z343,z1,z3,z4,z33])],[(0,[z13,z64,z159,z3,z4,z5]),(0,[z6,z147,z7,z3,z540,z5]),(0,[z13,z6,z1,z3,z4,z97]),(0,[z6,z345,z23,z3,z4,z5]),(0,[z1130,z6,z1,z3,z4,z5]),(0,[z6,z1131,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1132])],[],[(0,[z6,z1,z7,z3,z4,z1133]),(0,[z401,z6,z1,z179,z3,z4]),(0,[z6,z705,z23,z3,z4,z5])]],
   [[],[(0,[z6,z111,z100,z3,z4,z5]),(0,[z114,z6,z790,z3,z4,z5]),(0,[z135,z383,z7,z3,z69,z5]),(0,[z6,z1,z23,z3,z560,z5])],[(0,[z6,z9,z7,z3,z4,z556]),(0,[z16,z6,z25,z42,z4,z5]),(0,[z6,z1,z7,z3,z752,z5])],[(0,[z6,z1,z1134,z3,z4,z5]),(0,[z495,z6,z23,z3,z4,z5]),(0,[z6,z1,z24,z641,z4,z5]),(0,[z6,z383,z7,z3,z4,z365])],[(0,[z6,z1135,z3,z74,z4,z5]),(0,[z6,z7,z3,z51,z5,z252]),(0,[z6,z91,z7,z3,z867,z5])],[(0,[z0,z371,z1,z3,z4,z5]),(0,[z132,z1,z7,z20,z4,z5]),(0,[z6,z1136,z1,z7,z3,z5]),(0,[z217,z6,z886,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z708]),(0,[z16,z6,z92,z3,z4,z5]),(0,[z6,z1,z3,z4,z1137,z5])],[(0,[z96,z6,z7,z3,z4,z5]),(0,[z6,z408,z23,z3,z4,z5]),(0,[z6,z1,z3,z1138,z4,z5]),(0,[z293,z6,z3,z4,z125,z5]),(0,[z1139,z6,z1,z3,z4,z5]),(0,[z1140,z1,z7,z3,z4,z5])],[(0,[z397,z334,z6,z7,z3,z5]),(0,[z16,z6,z1,z3,z4,z97]),(0,[z6,z428,z23,z3,z4,z5]),(0,[z16,z6,z1,z3,z908,z5]),(0,[z6,z1141,z7,z3,z4,z5])],[(0,[z6,z355,z1,z3,z4,z52]),(0,[z6,z1,z7,z4,z5,z877]),(0,[z411,z6,z211,z3,z4,z5])],[(0,[z6,z1142,z7,z3,z4,z5]),(0,[z6,z9,z116,z3,z4,z5]),(0,[z6,z111,z1,z3,z4,z62])],[(0,[z6,z1143,z1,z3,z4,z5]),(0,[z6,z1,z1144,z3,z4,z5]),(0,[z16,z6,z1,z267,z4,z5]),(0,[z6,z111,z1,z3,z4,z549]),(0,[z6,z1,z23,z3,z10,z5])],[(0,[z6,z1145,z1,z3,z4,z5]),(0,[z13,z6,z23,z3,z4,z5]),(0,[z6,z1146,z1,z3,z4,z5]),(0,[z6,z648,z1,z3,z4,z62]),(0,[z6,z31,z1,z7,z3,z56])],[(0,[z1147,z6,z7,z3,z4,z5]),(0,[z6,z475,z23,z3,z4,z5]),(0,[z470,z6,z211,z3,z4,z5]),(0,[z6,z11,z1148,z3,z4,z5])],[(0,[z6,z1149,z7,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z1150,z5]),(0,[z6,z1151,z1,z3,z4,z5]),(0,[z6,z113,z1,z3,z4,z5])],[(0,[z6,z300,z23,z3,z4,z5]),(0,[z293,z6,z1,z26,z4,z5]),(0,[z16,z6,z1,z3,z4,z402]),(0,[z6,z1,z7,z3,z5,z775]),(0,[z6,z1,z3,z4,z1152,z5])]],
   [[(0,[z64,z6,z23,z3,z4,z5]),(0,[z13,z6,z100,z3,z4,z5]),(0,[z6,z23,z3,z380,z4,z5]),(0,[z245,z6,z1,z3,z4,z557])],[(0,[z122,z6,z23,z3,z4,z5]),(0,[z6,z1,z1153,z3,z4,z5]),(0,[z138,z6,z1,z7,z86,z5]),(0,[z138,z6,z113,z1,z86,z5])],[(0,[z6,z1,z1154,z3,z4,z5]),(0,[z6,z573,z23,z3,z4,z5]),(0,[z1155,z6,z1,z3,z4,z5]),(0,[z88,z6,z211,z3,z4,z5])],[(0,[z132,z397,z1,z7,z20,z5]),(0,[z6,z886,z7,z3,z4,z5]),(0,[z6,z569,z1,z7,z3,z56]),(0,[z41,z6,z241,z7,z3,z4]),(0,[z6,z7,z3,z4,z130,z5])],[(0,[z12,z6,z24,z26,z4,z5])],[(0,[z6,z1,z7,z3,z1156,z5]),(0,[z6,z1,z7,z3,z10,z125])],[(0,[z6,z1,z1157,z3,z4,z5]),(0,[z293,z6,z147,z3,z4,z5]),(0,[z13,z6,z592,z3,z4,z5]),(1,[z6,z1,z7,z752,z5])],[(1,[z293,z6,z26,z4,z5])],[(0,[z6,z383,z7,z3,z4,z97]),(0,[z1158,z6,z211,z3,z4,z5])],[(0,[z6,z1159,z7,z3,z4,z5]),(0,[z1160,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z752,z86,z5])],[(0,[z1161,z6,z1,z3,z4,z5]),(0,[z6,z211,z452,z3,z4,z5]),(0,[z6,z427,z7,z3,z15,z5])],[(0,[z16,z6,z100,z3,z4,z5]),(0,[z6,z100,z3,z4,z5,z110]),(0,[z6,z1162,z7,z3,z4,z5]),(0,[z6,z111,z454,z3,z4,z62]),(0,[z6,z11,z3,z4,z5,z205])],[(0,[z114,z168,z1,z115,z4,z5]),(0,[z6,z7,z23,z3,z10,z5]),(0,[z6,z1,z1163,z3,z4,z5]),(0,[z6,z91,z7,z3,z51,z5])],[(0,[z6,z1,z7,z3,z1164,z5]),(0,[z6,z211,z3,z4,z557,z5])],[(0,[z6,z1165,z1,z3,z4,z5]),(0,[z119,z6,z23,z3,z4,z5])],[(0,[z16,z6,z1,z3,z228,z4]),(0,[z6,z1,z7,z3,z4,z1166]),(0,[z6,z363,z3,z4,z5,z117]),(0,[z6,z1,z3,z4,z5,z1167])]],
   [[(0,[z64,z498,z7,z3,z4,z5]),(0,[z813,z1,z7,z3,z4,z5]),(0,[z6,z454,z2,z3,z4,z5]),(0,[z6,z1168,z7,z3,z4,z5])],[(0,[z6,z1,z3,z4,z5,z1169])],[(0,[z6,z7,z42,z686,z4,z5]),(0,[z6,z163,z1,z7,z3,z56])],[(0,[z135,z1,z24,z3,z69,z5]),(0,[z6,z116,z3,z4,z51,z5])],[(0,[z6,z23,z3,z169,z4,z5]),(0,[z6,z23,z3,z4,z172,z5]),(0,[z98,z6,z1,z398,z4,z5]),(0,[z12,z6,z241,z7,z26,z4]),(0,[z1170,z6,z1,z3,z4,z5])],[(0,[z6,z1,z1171,z255,z4,z5]),(1,[z6,z7,z1027,z4,z5]),(0,[z16,z6,z1,z674,z4,z5]),(0,[z6,z685,z1,z3,z4,z110])],[(0,[z6,z1,z1172,z3,z4,z5]),(0,[z16,z96,z6,z3,z4,z5]),(0,[z334,z6,z7,z3,z228,z4])],[(0,[z6,z1173,z1,z3,z4,z5]),(0,[z1174,z6,z1,z3,z4,z5])],[(0,[z12,z6,z7,z1027,z4,z5]),(0,[z6,z1,z3,z4,z5,z1175]),(0,[z6,z1,z3,z201,z889,z5]),(0,[z6,z1176,z7,z3,z4,z5])],[(0,[z6,z1,z24,z4,z701,z5]),(0,[z6,z249,z7,z19,z78,z5])],[(0,[z13,z6,z1,z3,z4,z365]),(0,[z6,z147,z23,z3,z14,z5])],[(0,[z6,z393,z7,z3,z4,z381])],[(0,[z397,z401,z6,z1,z7,z3]),(0,[z1177,z6,z7,z3,z4,z5])],[(0,[z1178,z6,z1,z255,z4,z5]),(0,[z6,z1,z3,z4,z1179,z5])],[(0,[z212,z6,z23,z3,z4,z5]),(0,[z6,z1,z23,z21,z4,z5]),(0,[z6,z23,z3,z202,z26,z4]),(0,[z6,z1,z3,z4,z1180,z5]),(0,[z6,z91,z102,z3,z51,z5])],[(1,[z6,z7,z3,z10,z99]),(0,[z6,z1,z24,z3,z4,z983]),(0,[z6,z1181,z1,z3,z4,z5])]],
   [[(0,[z16,z6,z1,z17,z4,z109])],[(0,[z6,z1,z7,z255,z4,z5]),(0,[z6,z1,z1182,z3,z4,z5]),(0,[z6,z283,z23,z3,z4,z5]),(0,[z6,z211,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z108,z55]),(0,[z6,z1,z3,z1183,z4,z5]),(0,[z6,z1184,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z1185,z5]),(0,[z6,z179,z3,z74,z4,z5]),(0,[z6,z1,z7,z3,z4,z1186]),(0,[z293,z6,z7,z26,z4,z5]),(0,[z6,z1,z7,z3,z933,z4]),(0,[z13,z6,z9,z3,z4,z99])],[(0,[z6,z339,z1,z3,z4,z5]),(0,[z6,z1187,z1,z3,z4,z5]),(0,[z1188,z6,z1,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z1189]),(0,[z6,z445,z7,z3,z4,z99]),(0,[z6,z211,z17,z3,z4,z5])],[(0,[z6,z1,z3,z4,z1190,z5])],[(0,[z6,z1,z1191,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z365]),(0,[z1192,z1,z7,z3,z4,z5]),(0,[z1193,z6,z1,z3,z4,z5]),(0,[z6,z1,z849,z3,z4,z5])],[(0,[z6,z1194,z1,z3,z4,z5]),(0,[z6,z1,z7,z1195,z4,z5]),(0,[z6,z311,z23,z3,z4,z5]),(0,[z6,z72,z24,z3,z4,z125])],[(0,[z6,z147,z7,z3,z704,z5])],[(1,[z788,z7,z3,z4,z5]),(0,[z1196,z6,z7,z3,z4,z5]),(0,[z724,z6,z1,z3,z4,z5]),(0,[z1,z7,z3,z4,z800,z181]),(0,[z6,z7,z1027,z26,z4,z5]),(0,[z6,z1,z1197,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1198]),(0,[z6,z85,z23,z3,z4,z5]),(1,[z6,z849,z3,z4,z5])],[(0,[z6,z1,z24,z3,z4,z97]),(0,[z6,z1,z452,z3,z4,z5]),(0,[z6,z1126,z1,z23,z3,z4]),(0,[z6,z1,z424,z3,z10,z5]),(0,[z6,z1199,z211,z3,z4,z5])],[(0,[z6,z1,z7,z3,z1200,z5]),(0,[z6,z1,z1201,z3,z4,z5])],[(0,[z132,z1,z7,z228,z20,z4]),(0,[z6,z1,z1202,z3,z4,z5]),(0,[z6,z427,z7,z3,z4,z55])],[(0,[z6,z1203,z1,z3,z4,z5]),(0,[z16,z6,z9,z3,z4,z99]),(0,[z16,z6,z92,z24,z4,z5])],[(0,[z801,z6,z1,z3,z4,z5]),(0,[z6,z514,z23,z3,z4,z5]),(0,[z6,z1,z7,z17,z3,z10]),(0,[z6,z393,z24,z3,z4,z5])],[(0,[z6,z1,z136,z3,z4,z5]),(0,[z6,z740,z23,z3,z4,z5]),(0,[z6,z1204,z1,z3,z4,z5]),(0,[z16,z6,z1070,z3,z4,z5]),(0,[z6,z1205,z7,z3,z4,z5])]],
   [[],[(0,[z6,z611,z23,z3,z4,z5]),(0,[z6,z1,z1206,z3,z4,z5]),(0,[z6,z23,z3,z269,z4,z5]),(0,[z6,z454,z7,z3,z4,z5]),(0,[z6,z322,z72,z3,z4,z125]),(0,[z16,z6,z1205,z3,z4,z5])],[(0,[z6,z1207,z1,z7,z3,z4]),(0,[z6,z1,z7,z21,z4,z97]),(0,[z6,z147,z23,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z402])],[(0,[z6,z1,z3,z4,z1208,z5]),(0,[z6,z1,z7,z3,z4,z1209]),(0,[z6,z1,z7,z3,z4,z1210]),(0,[z6,z1211,z7,z3,z4,z5])],[(0,[z6,z1212,z7,z3,z4,z5]),(0,[z6,z1,z37,z3,z4,z97]),(0,[z6,z249,z7,z3,z4,z5])],[(0,[z6,z1,z1171,z3,z4,z5]),(0,[z6,z92,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1213]),(0,[z6,z1,z7,z4,z109,z728])],[(0,[z1214,z6,z1,z3,z4,z5]),(0,[z6,z241,z23,z3,z26,z4]),(0,[z6,z34,z1,z3,z282,z5]),(0,[z6,z1,z253,z3,z200,z5])],[(0,[z65,z788,z7,z3,z4,z5]),(0,[z13,z6,z383,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z402])],[(0,[z6,z137,z23,z3,z4,z125]),(0,[z6,z1215,z7,z3,z4,z5])],[(0,[z1216,z6,z1,z3,z4,z5]),(0,[z6,z7,z3,z552,z51,z5]),(0,[z6,z7,z3,z14,z867,z5]),(0,[z16,z6,z1,z3,z1091,z5]),(0,[z866,z6,z427,z3,z4,z5])],[(0,[z0,z453,z1,z3,z4,z5]),(0,[z943,z6,z85,z3,z4,z5])],[(0,[z122,z65,z23,z3,z4,z5])],[],[(0,[z6,z85,z7,z3,z4,z97]),(0,[z1178,z6,z1,z3,z4,z5]),(0,[z6,z211,z3,z140,z4,z5]),(0,[z6,z530,z23,z3,z4,z5]),(0,[z6,z25,z23,z42,z4,z5]),(0,[z6,z31,z1,z23,z3,z56]),(0,[z6,z211,z3,z4,z5,z1217]),(0,[z6,z1,z7,z3,z55,z775])],[(0,[z6,z1,z24,z382,z4,z5]),(0,[z6,z1,z7,z3,z4,z1218]),(0,[z6,z89,z1,z3,z4,z5])],[(0,[z217,z1,z23,z3,z4,z181]),(0,[z6,z1,z141,z452,z4,z5])]],
   [[(0,[z6,z1,z1219,z3,z4,z5]),(0,[z6,z1,z3,z1220,z4,z5]),(0,[z864,z6,z7,z3,z4,z5]),(0,[z6,z44,z1,z3,z214,z402]),(0,[z6,z29,z1,z3,z4,z739]),(0,[z6,z1,z1221,z3,z4,z5])],[(0,[z673,z1,z7,z20,z4,z5]),(0,[z1147,z6,z256,z3,z4,z5]),(1,[z6,z23,z3,z10,z5])],[(0,[z6,z1,z24,z3,z228,z4]),(0,[z16,z6,z383,z3,z4,z5]),(0,[z6,z1,z211,z3,z4,z5]),(0,[z6,z182,z23,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z1222])],[(0,[z6,z1,z256,z3,z4,z5]),(0,[z138,z6,z1,z23,z86,z5]),(0,[z6,z31,z1,z24,z3,z56])],[(0,[z6,z1,z7,z3,z1223,z5]),(0,[z6,z1,z1224,z3,z4,z5]),(0,[z6,z23,z3,z51,z5,z56]),(0,[z94,z6,z1,z7,z4,z728]),(0,[z6,z1,z120,z3,z4,z56])],[(0,[z6,z445,z23,z3,z4,z5]),(0,[z13,z6,z1,z19,z78,z5]),(0,[z6,z89,z849,z3,z4,z5])],[(0,[z6,z1,z7,z3,z1225,z5]),(0,[z334,z6,z184,z3,z4,z5]),(0,[z6,z1,z1226,z3,z4,z5])],[(0,[z6,z1,z7,z715,z4,z5]),(0,[z13,z6,z1,z3,z228,z4]),(0,[z16,z6,z1,z511,z4,z5])],[(0,[z6,z1227,z1,z3,z4,z5])],[(0,[z6,z211,z3,z4,z5,z181]),(0,[z6,z134,z23,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z252]),(0,[z138,z6,z1,z24,z86,z5])],[(0,[z6,z1,z7,z3,z4,z1228]),(0,[z6,z1229,z7,z3,z4,z5])],[(0,[z6,z1,z1230,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1231]),(0,[z6,z1232,z1,z3,z4,z5]),(0,[z1233,z1,z7,z3,z4,z5]),(0,[z6,z7,z19,z78,z130,z5]),(0,[z6,z1,z3,z4,z187,z45]),(0,[z6,z343,z1,z3,z4,z45])],[(0,[z135,z643,z1,z7,z3,z5])],[(0,[z397,z6,z1,z7,z86,z5]),(0,[z6,z1234,z1,z3,z4,z5]),(0,[z6,z24,z3,z1235,z4,z5])],[(0,[z6,z1236,z7,z3,z4,z5]),(0,[z13,z96,z6,z3,z4,z5]),(0,[z1237,z1,z7,z3,z4,z5]),(0,[z94,z6,z211,z3,z4,z5]),(0,[z6,z1,z7,z3,z889,z5])],[(0,[z6,z7,z3,z4,z1238,z5])]],
   [[(0,[z6,z79,z23,z3,z51,z5]),(0,[z16,z6,z1,z19,z78,z5])],[(0,[z6,z1,z1239,z3,z4,z5]),(0,[z801,z6,z7,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z854]),(0,[z6,z1,z7,z3,z1240,z5]),(0,[z1241,z1,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z203]),(0,[z6,z1,z7,z3,z4,z1017]),(0,[z224,z6,z211,z3,z4,z5])],[(0,[z401,z6,z1,z7,z3,z4]),(0,[z6,z1,z136,z255,z4,z5]),(0,[z6,z1,z71,z3,z202,z4]),(0,[z6,z1,z3,z1242,z4,z5])],[(0,[z6,z204,z23,z3,z4,z5]),(0,[z6,z7,z3,z4,z51,z252]),(0,[z6,z1,z24,z17,z4,z109])],[(0,[z6,z1,z7,z3,z4,z1243]),(0,[z6,z1244,z1,z3,z4,z5]),(0,[z6,z9,z180,z7,z3,z4])],[(0,[z132,z13,z1,z20,z4,z5]),(0,[z41,z13,z6,z3,z4,z5]),(0,[z41,z6,z311,z3,z4,z5]),(0,[z6,z9,z7,z3,z4,z99]),(0,[z6,z1,z3,z4,z5,z131]),(0,[z6,z3,z4,z130,z1245,z5])],[(0,[z6,z1,z1246,z3,z4,z5]),(0,[z122,z229,z23,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z1247]),(0,[z6,z833,z7,z3,z4,z5]),(0,[z6,z1,z1148,z3,z4,z5])],[(0,[z6,z1,z1248,z3,z4,z5]),(0,[z6,z23,z3,z4,z171,z5]),(0,[z6,z1,z3,z4,z1245,z5]),(0,[z124,z6,z211,z3,z4,z5]),(0,[z747,z1,z7,z3,z4,z5]),(0,[z6,z1,z1249,z3,z4,z5])],[(0,[z122,z64,z23,z3,z4,z5]),(0,[z6,z233,z1,z3,z214,z5]),(0,[z6,z1,z3,z4,z5,z1250]),(0,[z6,z1,z24,z3,z4,z365]),(0,[z13,z6,z1,z17,z4,z109]),(0,[z6,z1,z1251,z3,z4,z5]),(0,[z6,z211,z3,z248,z4,z5]),(0,[z1252,z6,z1,z3,z4,z5])],[(0,[z6,z1112,z7,z3,z4,z5]),(0,[z6,z1,z24,z4,z258,z5])],[(0,[z6,z1,z1253,z3,z4,z5]),(0,[z262,z6,z1,z3,z4,z331]),(0,[z6,z1254,z1,z3,z4,z5]),(0,[z1255,z6,z211,z3,z4,z5])],[(0,[z13,z6,z554,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z1054]),(0,[z245,z6,z211,z3,z4,z5])],[(0,[z6,z383,z7,z255,z4,z5])],[(0,[z550,z403,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1256]),(0,[z6,z7,z3,z4,z867,z5])],[(0,[z135,z1,z7,z21,z69,z5]),(0,[z6,z1,z1257,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z1062]),(0,[z6,z1,z1258,z3,z4,z5]),(0,[z6,z7,z3,z4,z1259,z5]),(1,[z6,z1,z7,z3,z775])],[(0,[z6,z91,z7,z3,z51,z203]),(0,[z1260,z6,z1,z3,z4,z5]),(0,[z6,z1261,z1,z3,z4,z5])]],
   [[(0,[z6,z1,z7,z3,z228,z234]),(0,[z1262,z6,z1,z3,z4,z5]),(0,[z135,z1,z37,z3,z69,z5]),(0,[z6,z1,z7,z21,z4,z365]),(0,[z138,z13,z6,z1,z86,z5]),(0,[z16,z6,z848,z3,z4,z5])],[(0,[z41,z196,z6,z3,z4,z5]),(0,[z6,z1,z588,z3,z202,z4])],[(0,[z6,z1,z37,z3,z4,z365]),(0,[z16,z6,z839,z3,z4,z5]),(0,[z6,z1263,z1,z3,z4,z5])],[(0,[z647,z6,z23,z3,z4,z5]),(0,[z138,z6,z1,z7,z752,z5]),(0,[z6,z1,z1264,z3,z4,z5])],[],[(0,[z1,z7,z115,z715,z4,z5]),(0,[z6,z85,z959,z3,z4,z5]),(0,[z6,z211,z211,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z205]),(0,[z6,z111,z1,z3,z4,z161])],[(0,[z6,z1,z3,z4,z5,z1265]),(0,[z6,z1,z831,z3,z4,z5]),(0,[z6,z147,z7,z3,z867,z5]),(0,[z6,z1,z1266,z3,z4,z5]),(0,[z1267,z1,z7,z3,z4,z5])],[(0,[z6,z1,z1268,z3,z4,z5]),(0,[z6,z23,z3,z4,z5,z237]),(0,[z6,z25,z7,z1027,z4,z5]),(0,[z1269,z6,z1,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z1059]),(0,[z16,z6,z1,z426,z4,z5])],[(0,[z16,z6,z744,z3,z4,z5])],[(0,[z135,z85,z7,z3,z69,z5])],[(0,[z114,z1,z7,z715,z4,z5]),(0,[z293,z6,z1,z4,z109,z5])],[(0,[z16,z6,z1,z3,z4,z5]),(0,[z6,z1,z1270,z3,z4,z5]),(0,[z6,z85,z7,z3,z4,z365]),(0,[z6,z1,z3,z1271,z4,z5]),(0,[z6,z1,z7,z3,z4,z728])],[(0,[z12,z16,z6,z26,z4,z5]),(0,[z6,z346,z7,z3,z4,z99]),(0,[z16,z6,z92,z248,z4,z5]),(0,[z6,z427,z24,z3,z4,z5]),(0,[z6,z826,z7,z3,z4,z5]),(0,[z6,z1,z1272,z3,z4,z5])],[(0,[z397,z6,z7,z3,z74,z5]),(0,[z138,z6,z1,z7,z21,z5]),(0,[z6,z210,z23,z3,z4,z5]),(0,[z6,z249,z343,z3,z4,z5])],[(0,[z6,z1273,z1,z3,z4,z5]),(0,[z6,z1274,z7,z3,z4,z5])],[(0,[z6,z1275,z1,z3,z4,z5])]],
   [[(0,[z6,z1,z3,z4,z1276,z5]),(0,[z1277,z6,z1,z7,z3,z4]),(0,[z16,z6,z1,z276,z4,z5]),(0,[z6,z211,z3,z4,z5,z99]),(0,[z6,z1,z3,z889,z214,z5])],[(0,[z351,z6,z23,z3,z4,z5]),(0,[z16,z6,z3,z74,z4,z5]),(0,[z6,z71,z23,z3,z4,z5])],[(0,[z334,z6,z7,z3,z4,z5]),(0,[z6,z1,z3,z1278,z4,z5]),(0,[z6,z1279,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z1280,z5]),(0,[z6,z1,z116,z3,z4,z5]),(0,[z13,z6,z393,z3,z4,z5]),(1,[z6,z1,z3,z889,z5])],[(0,[z13,z6,z225,z3,z4,z5]),(0,[z6,z7,z42,z1027,z4,z5])],[(0,[z6,z853,z23,z3,z4,z5]),(0,[z6,z1281,z1,z3,z4,z5]),(0,[z6,z1,z1282,z3,z4,z5])],[(0,[z64,z159,z24,z3,z4,z5]),(0,[z6,z1283,z7,z3,z4,z5]),(0,[z6,z1,z1284,z3,z4,z5]),(0,[z6,z9,z740,z3,z4,z5])],[(0,[z6,z1285,z1,z3,z4,z5])],[(0,[z41,z6,z339,z3,z4,z5]),(0,[z6,z1,z1286,z3,z4,z5]),(0,[z67,z6,z211,z3,z4,z5]),(0,[z6,z9,z23,z3,z4,z5]),(0,[z6,z23,z3,z276,z4,z5])],[(0,[z6,z1,z23,z3,z202,z4]),(0,[z16,z6,z241,z1,z3,z4])],[(0,[z146,z6,z23,z3,z4,z5]),(0,[z6,z92,z211,z3,z4,z5]),(0,[z16,z6,z956,z3,z4,z5]),(0,[z6,z1003,z1,z3,z4,z5])],[(0,[z64,z159,z165,z3,z4,z5]),(0,[z0,z813,z1,z3,z4,z5]),(0,[z6,z35,z454,z3,z4,z5]),(0,[z6,z73,z3,z4,z51,z5]),(0,[z6,z1287,z1,z3,z4,z5])],[(0,[z647,z159,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z1288,z4]),(0,[z6,z211,z3,z4,z5,z95]),(0,[z1289,z6,z1,z3,z4,z5])],[(0,[z6,z383,z7,z3,z4,z5]),(0,[z6,z1,z24,z3,z234,z5]),(0,[z6,z1,z1290,z3,z4,z5]),(0,[z6,z449,z23,z3,z4,z5]),(0,[z6,z1,z24,z3,z4,z252])],[(0,[z6,z1,z1291,z3,z4,z5]),(0,[z6,z211,z3,z4,z1292,z5]),(0,[z16,z6,z393,z3,z4,z5]),(0,[z392,z6,z3,z380,z4,z5])],[(0,[z6,z1104,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z1293,z5])],[(0,[z135,z1,z7,z3,z828,z5]),(0,[z6,z7,z3,z1294,z4,z5]),(0,[z6,z256,z886,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z45]),(1,[z6,z1,z7,z4,z728])]],
   [[(0,[z6,z1,z7,z1295,z4,z5]),(0,[z6,z788,z7,z3,z4,z5]),(0,[z6,z1296,z7,z3,z4,z5]),(0,[z6,z241,z1,z7,z3,z4]),(0,[z6,z34,z182,z3,z4,z5]),(0,[z6,z34,z454,z3,z4,z5]),(0,[z6,z1297,z7,z3,z4,z5]),(0,[z1298,z6,z1,z3,z4,z5])],[(0,[z132,z1,z7,z715,z4,z5]),(0,[z13,z6,z1,z3,z234,z5]),(0,[z814,z6,z25,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z252])],[(0,[z6,z1,z7,z3,z1299,z5]),(0,[z235,z1,z7,z3,z140,z5]),(0,[z1300,z6,z1,z3,z4,z5]),(0,[z6,z853,z147,z3,z4,z5]),(0,[z6,z1,z1301,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z783]),(0,[z13,z6,z1,z255,z4,z5]),(0,[z6,z1,z1302,z3,z4,z5]),(0,[z6,z1,z1303,z3,z4,z5]),(0,[z16,z6,z1018,z3,z4,z5]),(0,[z6,z1,z24,z19,z78,z5]),(0,[z6,z11,z1021,z3,z4,z5])],[],[(0,[z6,z310,z23,z3,z4,z5]),(0,[z6,z1304,z7,z3,z4,z5])],[(0,[z6,z1,z1305,z3,z4,z5]),(0,[z6,z211,z3,z4,z51,z5]),(0,[z6,z1,z3,z4,z739,z110]),(0,[z94,z6,z7,z4,z117,z95]),(0,[z6,z427,z120,z3,z4,z5]),(0,[z6,z1,z1306,z3,z4,z5])],[(0,[z6,z1,z178,z3,z4,z5]),(0,[z6,z11,z24,z3,z4,z5])],[(0,[z523,z35,z1,z3,z4,z5]),(0,[z6,z23,z3,z4,z125,z55]),(0,[z6,z1,z46,z3,z4,z252]),(0,[z6,z211,z3,z78,z4,z5])],[(0,[z6,z1307,z7,z3,z4,z5]),(1,[z6,z211,z3,z4,z5])],[(0,[z6,z1308,z1,z3,z4,z5]),(0,[z6,z116,z3,z26,z4,z5]),(0,[z6,z1309,z211,z3,z4,z5])],[(0,[z6,z1,z3,z4,z5,z1310]),(0,[z6,z147,z7,z3,z356,z5]),(0,[z6,z1,z7,z3,z4,z1311]),(0,[z6,z1312,z1,z3,z4,z5])],[(0,[z35,z813,z1,z3,z4,z5]),(0,[z16,z6,z1,z3,z234,z5]),(0,[z12,z6,z211,z3,z4,z5]),(0,[z6,z1,z7,z3,z15,z597]),(0,[z94,z16,z6,z1,z4,z95]),(0,[z6,z1,z7,z19,z78,z33])],[(0,[z6,z31,z1,z120,z3,z56])],[(0,[z6,z1,z324,z3,z4,z5]),(0,[z16,z6,z1,z255,z4,z5]),(0,[z6,z346,z23,z3,z4,z5])],[(0,[z98,z6,z211,z3,z4,z5])]],
   [[(0,[z6,z1313,z1,z3,z4,z5]),(0,[z6,z1,z1314,z3,z4,z5])],[(0,[z16,z122,z65,z3,z4,z5]),(0,[z602,z6,z23,z3,z4,z5]),(0,[z6,z174,z23,z3,z4,z5]),(0,[z6,z1,z24,z4,z5,z226]),(0,[z6,z803,z1,z3,z4,z5])],[(0,[z6,z1,z7,z3,z4,z1315])],[(0,[z334,z6,z7,z3,z234,z5]),(0,[z6,z1,z3,z4,z5,z1316]),(0,[z6,z1,z1317,z3,z4,z5])],[(0,[z401,z6,z1,z23,z3,z4]),(0,[z6,z1,z7,z3,z4,z1318])],[(0,[z13,z6,z441,z3,z4,z5]),(0,[z132,z1,z24,z20,z4,z5]),(0,[z6,z23,z3,z74,z4,z5]),(0,[z6,z1,z3,z4,z1319,z5])],[(0,[z12,z6,z7,z630,z4,z5]),(0,[z96,z6,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1320]),(0,[z6,z1,z7,z3,z4,z800]),(0,[z326,z6,z23,z3,z4,z5]),(0,[z16,z6,z1,z3,z4,z1198]),(0,[z6,z657,z1,z3,z4,z110])],[(0,[z6,z1,z1135,z3,z4,z5]),(0,[z6,z1,z1321,z3,z4,z5]),(0,[z6,z1141,z24,z3,z4,z5])],[(1,[z6,z7,z3,z4,z1017])],[(0,[z12,z6,z23,z26,z4,z5]),(0,[z6,z72,z7,z3,z4,z1017])],[(0,[z401,z6,z1,z24,z3,z4]),(0,[z16,z6,z1,z398,z4,z5]),(0,[z6,z1,z833,z3,z4,z5]),(0,[z6,z1,z3,z4,z5,z1322])],[(0,[z6,z1,z7,z3,z819,z5])],[(0,[z539,z6,z23,z3,z4,z5]),(0,[z235,z6,z211,z3,z4,z5]),(0,[z6,z1,z7,z3,z15,z55])],[(0,[z6,z1323,z1,z3,z4,z5]),(0,[z6,z311,z393,z3,z4,z5]),(0,[z6,z24,z3,z4,z5,z117])],[(0,[z6,z1,z24,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1324]),(0,[z6,z116,z3,z4,z125,z5]),(0,[z6,z29,z1,z3,z4,z505]),(1,[z6,z833,z3,z4,z5]),(0,[z6,z31,z1,z7,z3,z775])],[]],
   [[(0,[z67,z1,z3,z405,z4,z5]),(0,[z293,z6,z1,z3,z4,z5]),(0,[z6,z23,z3,z4,z10,z5]),(0,[z1325,z1,z7,z3,z4,z5]),(0,[z6,z111,z1,z3,z4,z557])],[(0,[z6,z1,z7,z3,z1326,z5]),(0,[z6,z182,z7,z3,z4,z402])],[(0,[z6,z152,z23,z3,z4,z5]),(0,[z6,z1,z1327,z3,z4,z5]),(0,[z6,z1,z3,z1328,z4,z5]),(0,[z6,z421,z23,z3,z4,z5])],[(0,[z6,z1,z165,z3,z4,z5]),(0,[z13,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1329])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z691,z6,z23,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z815]),(0,[z6,z1,z7,z3,z112,z55])],[(0,[z1330,z6,z1,z7,z3,z4])],[(0,[z562,z1,z7,z115,z4,z5]),(0,[z6,z211,z19,z3,z4,z5]),(0,[z6,z211,z3,z4,z5,z56])],[(0,[z6,z1331,z1,z3,z4,z5]),(0,[z1052,z6,z1,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z33]),(0,[z6,z1,z7,z4,z728,z95])],[(0,[z135,z1,z23,z3,z69,z5])],[(0,[z6,z1332,z1,z3,z4,z5]),(0,[z13,z6,z3,z74,z4,z5])],[(0,[z6,z1,z1333,z3,z4,z5]),(0,[z6,z1,z46,z3,z4,z5]),(0,[z6,z449,z210,z3,z4,z5]),(0,[z6,z1334,z7,z3,z4,z5]),(0,[z6,z7,z3,z1235,z4,z5])],[],[(0,[z6,z1335,z7,z3,z4,z5]),(0,[z6,z1,z1336,z3,z4,z5]),(0,[z6,z91,z24,z3,z51,z5]),(0,[z6,z44,z1,z3,z214,z5])],[(0,[z114,z1,z7,z115,z4,z5]),(0,[z6,z383,z136,z3,z4,z5]),(0,[z6,z1337,z7,z3,z4,z5]),(0,[z1,z7,z3,z828,z69,z5])],[(0,[z6,z1,z1338,z3,z4,z5]),(0,[z64,z788,z7,z3,z4,z5]),(0,[z6,z1,z1339,z3,z4,z5]),(0,[z6,z1,z3,z4,z1340,z5])],[]],
   [[(0,[z6,z1341,z7,z3,z4,z5]),(0,[z13,z6,z241,z1,z3,z4]),(0,[z6,z1,z3,z726,z4,z5]),(0,[z61,z6,z1,z3,z4,z173])],[(0,[z6,z1342,z7,z3,z4,z5])],[],[(0,[z217,z1,z32,z3,z4,z181]),(0,[z6,z111,z1,z3,z4,z331]),(0,[z6,z222,z7,z3,z4,z125])],[(0,[z6,z100,z7,z3,z4,z5]),(0,[z6,z1,z7,z3,z4,z1343]),(0,[z6,z211,z42,z3,z4,z5])],[(0,[z401,z6,z184,z1,z3,z4]),(0,[z6,z1,z1344,z3,z4,z5]),(0,[z13,z6,z182,z3,z4,z5])],[(0,[z6,z1,z398,z26,z4,z5]),(0,[z12,z6,z71,z26,z4,z5]),(0,[z6,z9,z7,z54,z3,z4]),(0,[z1345,z6,z1,z3,z4,z5]),(0,[z16,z1325,z1,z3,z4,z5]),(0,[z6,z1346,z7,z3,z4,z5])],[(0,[z16,z6,z1,z615,z4,z5]),(1,[z801,z6,z3,z4,z5]),(0,[z6,z44,z1,z3,z582,z5])],[(0,[z397,z6,z1,z179,z3,z5]),(0,[z6,z1,z7,z3,z5,z1347]),(0,[z6,z1,z1348,z3,z4,z5]),(0,[z6,z91,z46,z3,z51,z5])],[(0,[z397,z6,z1,z7,z21,z5]),(0,[z6,z1,z1349,z3,z4,z5])],[(0,[z6,z1346,z89,z3,z4,z5])],[(0,[z6,z1350,z7,z3,z4,z5]),(0,[z6,z72,z23,z3,z4,z125]),(0,[z6,z7,z3,z4,z1351,z5])],[(0,[z6,z1,z1352,z3,z4,z5]),(0,[z6,z1,z7,z3,z560,z5]),(0,[z6,z1,z7,z17,z4,z333])],[(0,[z67,z403,z1,z3,z4,z5]),(0,[z16,z6,z1,z486,z4,z5]),(0,[z6,z452,z3,z4,z51,z5]),(0,[z6,z113,z833,z3,z4,z5]),(0,[z6,z395,z427,z3,z4,z5])],[(0,[z467,z35,z1,z3,z4,z5]),(0,[z6,z241,z1,z71,z3,z4]),(0,[z16,z6,z1,z3,z4,z203]),(0,[z6,z211,z58,z3,z4,z5]),(0,[z6,z44,z182,z3,z214,z5]),(0,[z6,z44,z393,z3,z214,z5]),(0,[z6,z34,z1,z3,z889,z5])],[(0,[z6,z1,z1353,z3,z4,z5]),(0,[z6,z1354,z1,z3,z4,z5]),(0,[z6,z1,z23,z3,z4,z97]),(0,[z6,z1,z266,z3,z4,z5]),(0,[z6,z1,z7,z3,z875,z5]),(0,[z6,z1355,z7,z3,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 498).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 995).take 413) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1408)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [498, 497, 413] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 105).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 214).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 322).take 110).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 432).take 80).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [105, 109, 108, 110, 80] = true :=
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

end PEqualNP.Outside.L_meta_45788

theorem PEqualNP.Outside.L_meta_45788 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4008241344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4008241344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45788.solve