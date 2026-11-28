import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37153

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
  Nat.testBit (4276813032 * 2 ^ 32 + 4274572488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa0089e20dc0e348c#64 ++ 0x740113c41b81c691#64 ++ 0xdc19fe21fc1e749b#64 ++ 0x7b833fc43f83ce93#64 : BitVec 256),
   (0x4022400a2020c131#64 ++ 0x0804480144041826#64 ++ 0xb466403e3063ffff#64 ++ 0xf68cc807c60c7fff#64 : BitVec 256),
   (0x808582c54d8318c6#64 ++ 0x5010b058a9b06318#64 ++ 0x7b8787c7cf8398e7#64 ++ 0xef70f0f8f9f0731c#64 : BitVec 256),
   (0x0158077006d41e00#64 ++ 0x602b00ee00da83c0#64 ++ 0xfff807f80ffc1f06#64 ++ 0xdfff00ff01ff83e0#64 : BitVec 256),
   (0x05f7e8000b7be007#64 ++ 0x80befd00016f7c00#64 ++ 0xfdfff8000fffe006#64 ++ 0x3fbfff0001fffc00#64 : BitVec 256),
   (0x03ff75bfb0000000#64 ++ 0x007feeb7f6000000#64 ++ 0xf3fffffff0000001#64 ++ 0xfe7ffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [13, 12]⟩, ⟨.and, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0008077004841e00 0x600100ee009083c0 0x020007f800001f00 0xc04000ff000003e0

def z1 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f80ffc1f06 0xdfff00ff01ff83e0

def z2 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z3 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb466403e3063ffff 0xf68cc807c60c7fff

def z4 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf8398e7 0xef70f0f8f9f0731c

def z5 : W := mkw 0xa0081620d4041488 0x740102c41a808291 0x00000621f0001499 0x400000c43e000293

def z6 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe21fc1e749b 0x7b833fc43f83ce93

def z7 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000fffe006 0x3fbfff0001fffc00

def z8 : W := mkw 0xa4affe20dd2ff48f 0xf495ffc41ba5fe91 0xdc1ffe21fc1ff49b 0x7b83ffc43f83fe93

def z9 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xffe787ffcfe39fe7 0xfffcf0fff9fc73fc

def z10 : W := mkw 0x0158053002540600 0x202b00a6004a80c0 0x84780038007c0700 0x108f0007000f80e0

def z11 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x4b9807c00f9c0000 0x097300f801f38000

def z12 : W := mkw 0x05ffee200f7ff407 0xe0bffdc401effe80 0xfdfffe200ffff406 0x7fbfffc401fffe80

def z13 : W := mkw 0x01588f700ede3e04 0x602b11ee01dbc7c0 0xfff9fff80ffe7f06 0xffff3fff01ffcfe0

def z14 : W := mkw 0x0285308590000000 0x0050a610b2000000 0x0001b801c0000000 0x0000370038000000

def z15 : W := mkw 0x0150000002500000 0x002a0000004a0000 0xfdf800000ffc0006 0x1fbf000001ff8000

def z16 : W := mkw 0x02af75bfb0000000 0x0055eeb7f6000000 0x0207fffff0000001 0xe040fffffe000000

def z17 : W := mkw 0x4172415a22f0cb31 0x082e482b445e1966 0x23e601de03e18b64 0x847cc03bc07c316c

def z18 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19be21cc1c1402 0x5b8337c439838280

def z19 : W := mkw 0xe022d80af82ae1bd 0x1c045b015f055c37 0xb467f83ff063ffff 0xf68cff07fe0c7fff

def z20 : W := mkw 0x4000000a2020c131 0x0800000144041826 0x0400003e3063ffff 0xc0800007c60c7fff

def z21 : W := mkw 0x040000000371c003 0x80800000006e3800 0x0000000003e18004 0x00000000007c3000

def z22 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x4399bfc1c0000000 0x087337f838000000

def z23 : W := mkw 0xa0008a004c0e348c 0x740011400981c691 0x0c0000000c1e749a 0x018000000183ce93

def z24 : W := mkw 0x0085800009030006 0x0010b00001206000 0x798780000f838006 0x2f30f00001f07000

def z25 : W := mkw 0x85f7eac54ffbf8c7 0xd0befd58a9ff7f18 0xffffffc7cffff8e7 0xfffffff8f9ffff1c

def z26 : W := mkw 0xe0008a004c2ef5bd 0x7c0011400985deb7 0x0c0000000c7ffffe 0x01800000018fffff

def z27 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x2066001e00618b64 0x840cc003c00c316c

def z28 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4819be01cc1c0000 0x090337c039838000

def z29 : W := mkw 0x4000024006f4df31 0x6800004800de9be6 0x0c0000000ffffffe 0x0180000001ffffff

def z30 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x000640063003e0f9 0x2000c800c6007c1f

def z31 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e3fffffff 0xffbfff07c7ffffff

def z32 : W := mkw 0x420815bfb0000130 0x084102b7f6000026 0x020007fff0001ff9 0xc04000fffe0003ff

def z33 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff063ffff 0xfefffffffe0c7fff

def z34 : W := mkw 0x45f7600a2371c133 0x88beec01446e3826 0x21e6001e03e18b64 0x843cc003c07c316c

def z35 : W := mkw 0xa0001000d0000088 0x140002001a000011 0x00000001f0000099 0x000000003e000013

def z36 : W := mkw 0x077a7d3ab278e001 0x80ef4fa7564f1c00 0x84787838307c6000 0x108f0f07060f8c00

def z37 : W := mkw 0xa000020044041488 0x7400004008808291 0x0000000000001498 0x0000000000000293

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0x30060006000398e7 0xe600c000c000731c

def z39 : W := mkw 0xc0a7c2cf6da3d9f7 0x5814f859edb47b3e 0xffe7c7ffffe3ffff 0xfffcf8fffffc7fff

def z40 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x8460403830606718 0x108c0807060c0ce3

def z41 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8187c1cf800000 0x097030f839f00000

def z42 : W := mkw 0xa08d9ee5dd8f3cce 0x7411b3dcbbb1e799 0xff9fffe7ff9ffcff 0xfff3fffcfff3ff9f

def z43 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x63ffbfdfc0000000 0x8c7ff7fbf8000000

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0x940040203002749b 0x7280080406004e93

def z45 : W := mkw 0x05f7e800092be007 0x80befd0001257c00 0xf1fff8000003e000 0x3e3fff0000007c00

def z46 : W := mkw 0x0000024004801800 0x4000004800900300 0x080000000f801806 0x0100000001f00300

def z47 : W := mkw 0x03ff75bfb2500000 0x007feeb7f64a0000 0xfffffffffffc0007 0xffffffffffff8000

def z48 : W := mkw 0x0022400a20000000 0x0004480144000000 0xb066403e30000001 0xf60cc807c6000000

def z49 : W := mkw 0x4572680a2278e131 0x88ae4d01444f1c26 0x84787838307c6718 0x108f0f07060f8ce3

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0xb460003800601f06 0xd68c0007000c03e0

def z51 : W := mkw 0x417a477a26f4df31 0x682f48ef44de9be6 0xfffe47fe3fffffff 0xffffc8ffc7ffffff

def z52 : W := mkw 0x020815bfb0000000 0x004102b7f6000000 0x020007fff0000001 0xc04000fffe000000

def z53 : W := mkw 0x44a7e80a292be137 0x8894fd0145257c26 0x0007f8063003e0f9 0x2000ff00c6007c1f

def z54 : W := mkw 0x0550280002582000 0x80aa0500004b0400 0x00183800001c0000 0x0003070000038000

def z55 : W := mkw 0x01dd07f507d51e42 0x603ba0fea0faa3c8 0xfffe07fe0ffd9f66 0xdfffc0ffc1ffb3ec

def z56 : W := mkw 0x07ffffffbffffe07 0xe0fffffff7ffffc0 0xffffffffffffff07 0xffffffffffffffe0

def z57 : W := mkw 0xa0089e60dc8e3c8c 0x740113cc1b91c791 0xff99ffe1ff9e7c9f 0xfff33ffc3ff3cf93

def z58 : W := mkw 0xa0081770d4841e88 0x740102ee1a9083d1 0x020007f9f0001f99 0xc04000ff3e0003f3

def z59 : W := mkw 0x02af74afb0000000 0x0055ee95f6000000 0xd01ffe27f0000001 0x7a03ffc4fe000000

def z60 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x8c7800380ffc1f06 0x118f000701ff83e0

def z61 : W := mkw 0xa2a7f88ff80a208c 0x1454ff11ff014411 0x0007f807f0026099 0x2000ff00fe004c13

def z62 : W := mkw 0xa00816e5d4841cc8 0x740102dcba908399 0x020007e7f0001cf9 0xc04000fcfe00039f

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0x798000000f800006 0x0f30000001f00000

def z64 : W := mkw 0x0000000000000000 0x0000000000000000 0x2060001800600b04 0x840c0003000c0160

def z65 : W := mkw 0x00008800080a2004 0x0000110001014400 0xdc19f8000c1e6002 0x3b833f000183cc00

def z66 : W := mkw 0xa5fffe20df7ff48f 0xf4bfffc41beffe91 0xfdfffe21fffff49f 0x7fbfffc43ffffe93

def z67 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfffe07fe0fff9fe7 0xffffc0ffc1fff3fc

def z68 : W := mkw 0xa0008800480a208c 0x1400110009014411 0x0000000000026098 0x0000000000004c13

def z69 : W := mkw 0x0000024004801800 0x4000004800900300 0x4b8007c00f800000 0x097000f801f00000

def z70 : W := mkw 0x0150011002500200 0x002a0022004a0040 0x0060001800600300 0x000c0003000c0060

def z71 : W := mkw 0xa5f7f800db7be08f 0x94beff001b6f7c11 0xfdfff801ffffe09f 0x3fbfff003ffffc13

def z72 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x238601c603818864 0x8470c038c070310c

def z73 : W := mkw 0x037a753ab0000000 0x006f4ea756000000 0x8078783830000000 0x100f0f0706000000

def z74 : W := mkw 0x20081c20900c2408 0x2401038412018481 0xd419fe21f01c6419 0x7a833fc43e038c83

def z75 : W := mkw 0x800082404d8318c6 0x5000104809b06318 0x080000000f8398e6 0x0100000001f0731c

def z76 : W := mkw 0x0000024004801800 0x4000004800900300 0x7b8007c00f801806 0xcf7000f801f00300

def z77 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x4999b8000f9c0000 0x0933370001f38000

def z78 : W := mkw 0x0158053002540600 0x202b00a6004a80c0 0xfdf800380ffc0706 0x1fbf000701ff80e0

def z79 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xa3fe79fe30000000 0x947fcf3fc6000000

def z80 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xfdf9b8000ffc0006 0x1fbf370001ff8000

def z81 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x940640263003f4fb 0x7280c804c6007e9f

def z82 : W := mkw 0xa0008a004c0e348c 0x740011400981c691 0x080000000c1c0000 0x0100000001838000

def z83 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xcc19fe21fc1c6418 0x19833fc43f838c83

def z84 : W := mkw 0x01f7600000000000 0x003eec0000000000 0xf1fff80000000000 0x3e3fff0000000000

def z85 : W := mkw 0x0358353090000000 0x006b06a612000000 0x0018380000000000 0x0003070000000000

def z86 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0xf3ffffc1c0000000 0x3e7ffff838000000

def z87 : W := mkw 0x4000000a20000130 0x0800000144000026 0x0000003e30001ff9 0xc0000007c60003ff

def z88 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8063fffe0ff 0x3fbfff00c7fffc1f

def z89 : W := mkw 0x800002c5448018c0 0x50000058a8900318 0x320607c7c00398e7 0xe640c0f8f800731c

def z90 : W := mkw 0x80858ac54d8b38c6 0x5010b158a9b16718 0xff9fffc7cf9ff8e7 0xfff3fff8f9f3ff1c

def z91 : W := mkw 0x417a477a26f4df31 0x682f48ef44de9be6 0xfffe07fe0ffd9f66 0xdfffc0ffc1ffb3ec

def z92 : W := mkw 0x0000024004841e00 0x60000048009083c0 0x0000000000001f00 0x00000000000003e0

def z93 : W := mkw 0x0000004002d00a00 0x00000008005a0140 0x0000000003e00b04 0x00000000007c0160

def z94 : W := mkw 0x01f7600002500000 0x003eec00004a0000 0xfdfff8000ffc0006 0x3fbfff0001ff8000

def z95 : W := mkw 0x03ff77ffb6d41e00 0x607feefff6da83c0 0xfffffffffffc1f07 0xffffffffffff83e0

def z96 : W := mkw 0xa1589f70dede3e8c 0x742b13ee1bdbc7d1 0xfff9fff9fffe7f9f 0xffff3fff3fffcff3

def z97 : W := mkw 0x07fffdbfbb7be007 0x80ffffb7f76f7c00 0xffffffffffffe007 0xfffffffffffffc00

def z98 : W := mkw 0xe5fffe2aff7ff5bf 0xfcbfffc55feffeb7 0xfdfffe3fffffffff 0xffbfffc7ffffffff

def z99 : W := mkw 0x04a7e800092be007 0x8094fd0001257c00 0x0007f8000003e000 0x2000ff0000007c00

def z100 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf7fffffff063e007 0xfefffffffe0c7c00

def z101 : W := mkw 0x80008000490300c6 0x1000100009206018 0x00000000000380e0 0x000000000000701c

def z102 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0xdc19f801fc1e609b 0x3b833f003f83cc13

def z103 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8187c1cf801806 0xcf7030f839f00300

def z104 : W := mkw 0x81dd87f54fd71ec6 0x703bb0fea9fae3d8 0xffff87ffcfff9fe7 0xfffff0fff9fff3fc

def z105 : W := mkw 0xa0858ac54d8f3cce 0x7410b158a9b1e799 0x7f8787c7cf9ffcff 0xeff0f0f8f9f3ff9f

def z106 : W := mkw 0x002240000020c001 0x0004480000041800 0xb46640000063e006 0x368cc800000c7c00

def z107 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4819be21fc1c1499 0x490337c43f838293

def z108 : W := mkw 0x0000024006d41e00 0x6000004800da83c0 0x0c0000000ffc1f06 0x0180000001ff83e0

def z109 : W := mkw 0x0008142090000000 0x0001028412000000 0xd019fe21f0000001 0x7a033fc43e000000

def z110 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xd399ffe1f0000001 0x7a733ffc3e000000

def z111 : W := mkw 0xa0009a00dc0a308c 0x540013401b814611 0x5801fe01fc02709b 0x6b003fc03f804e13

def z112 : W := mkw 0x040088000b7be007 0x80801100016f7c00 0x0c0000000fffe006 0x0180000001fffc00

def z113 : W := mkw 0x040088000b7be007 0x80801100016f7c00 0xdc19f8000fffe006 0x3b833f0001fffc00

def z114 : W := mkw 0x05f760000371c003 0x80beec00006e3800 0x21e6000003e18004 0x043cc000007c3000

def z115 : W := mkw 0x07ff75bfb371c003 0x80ffeeb7f66e3800 0xf3fffffff3e18005 0xfe7ffffffe7c3000

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0xb060003800000000 0xd60c000700000000

def z117 : W := mkw 0x02a7608f20000000 0x0054ec11e4000000 0x0006000600000000 0x0000c000c0000000

def z118 : W := mkw 0x035815bfb0000000 0x006b02b7f6000000 0xf3f807fff0000001 0xde7f00fffe000000

def z119 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8787c7cf8380e1 0x2970f0f8f9f0701c

def z120 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0x0001f801f0026099 0x20003f003e004c13

def z121 : W := mkw 0xe0089e20dc2ef5bd 0x7c0113c41b85deb7 0xdc19fe21fc7fffff 0x7b833fc43f8fffff

def z122 : W := mkw 0x0158077004801800 0x402b00ee00900300 0xfbf807f80f801806 0xdf7f00ff01f00300

def z123 : W := mkw 0x0085800009030006 0x0010b00001206000 0x798780060f8398e7 0xef30f000c1f0731c

def z124 : W := mkw 0x800082004c021084 0x5000104009804210 0x78078607cc0398e7 0xef00f0c0f980731c

def z125 : W := mkw 0x05f7ea400ffbf807 0xc0befd4801ff7f00 0xffffffc00ffff806 0xfffffff801ffff00

def z126 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x23e007f803e01f04 0xc47c00ff007c03e0

def z127 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xff87c7e7ff83fcff 0xfff0f8fcfff07f9f

def z128 : W := mkw 0x00088e200c0e3404 0x600111c40181c680 0xdc19fe200c1e7402 0x7b833fc40183ce80

def z129 : W := mkw 0x808d87f54d871ec6 0x7011b0fea9b0e3d8 0x7b8787ffcf839fe7 0xef70f0fff9f073fc

def z130 : W := mkw 0xa1fffe20dc0e348c 0x743fffc41b81c691 0xfdfffe21fc1e749b 0x7fbfffc43f83ce93

def z131 : W := mkw 0x80000240448018c0 0x5000004808900318 0x00000000000018e0 0x000000000000031c

def z132 : W := mkw 0x0150035006d01a00 0x402a006a00da0340 0x7be007d80fe01b06 0xcf7c00fb01fc0360

def z133 : W := mkw 0x808582404d8318c6 0x5010b04809b06318 0x798780000f8398e6 0x2f30f00001f0731c

def z134 : W := mkw 0x20089c20980e240c 0x240113841301c481 0xdc19f8203c1e641a 0x3b833f040783cc83

def z135 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0x23e001d803e00b04 0x847c003b007c0160

def z136 : W := mkw 0x0008077006d41e00 0x600100ee00da83c0 0x0e0007f80ffc1f06 0xc1c000ff01ff83e0

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x3006000600000001 0xe600c000c0000000

def z138 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4c19be01cc1e749a 0x098337c03983ce93

def z139 : W := mkw 0x0085008500000000 0x0010a010a0000000 0x438187c1c0000000 0x087030f838000000

def z140 : W := mkw 0xa3ffffbffc0e348c 0x747ffff7ff81c691 0xfffffffffc1e749b 0xffffffffff83ce93

def z141 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8060ffff8e7 0xffbfff00c1ffff1c

def z142 : W := mkw 0xc1ffc7ff6ff7dff7 0x783ff8ffedfefbfe 0xffffc7ffffffffff 0xfffff8ffffffffff

def z143 : W := mkw 0x400000000020c131 0x0800000000041826 0x040000000063fffe 0x00800000000c7fff

def z144 : W := mkw 0x00008800080a2004 0x0000110001014400 0xdc19f8203c1e749b 0x7b833f040783ce93

def z145 : W := mkw 0x01f7600a20000000 0x003eec0144000000 0xf1fff83e30000001 0xfe3fff07c6000000

def z146 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf3fffffff0001ff9 0xfe7ffffffe0003ff

def z147 : W := mkw 0xa0008a404d8f3cce 0x7400114809b1e799 0x0c0000000f9ffcfe 0x0180000001f3ff9f

def z148 : W := mkw 0x02a7708fb0000000 0x0054ee11f6000000 0x0007f807f0000001 0x2000ff00fe000000

def z149 : W := mkw 0x03f7619f20000000 0x007eec33e4000000 0x23e601de00000000 0x847cc03bc0000000

def z150 : W := mkw 0xa0081e20d40c3488 0x740103c41a818691 0x84187e21f01c7499 0x50830fc43e038e93

def z151 : W := mkw 0x05ffef700ffffe07 0xe0bffdee01ffffc0 0xfffffff80fffff06 0xffffffff01ffffe0

def z152 : W := mkw 0x0158077004841e00 0x602b00ee009083c0 0xf3f807f800001f00 0xde7f00ff000003e0

def z153 : W := mkw 0x800002c5448018c0 0x50000058a8900318 0x020007c7c00018e1 0xc04000f8f800031c

def z154 : W := mkw 0x0158057002d00a00 0x002b00ae005a0140 0xf3f807f803e00b04 0xde7f00ff007c0160

def z155 : W := mkw 0x057268000278e001 0x80ae4d00004f1c00 0x84787800007c6000 0x108f0f00000f8c00

def z156 : W := mkw 0x83fff7fffd8318c6 0x507ffeffffb06318 0xfbffffffff800001 0xff7ffffffff00000

def z157 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x6b8787c7cf818864 0x8d70f0f8f9f0310c

def z158 : W := mkw 0x00858800090b2006 0x0010b10001216400 0xfd9ff8000f9fe006 0x3fb3ff0001f3fc00

def z159 : W := mkw 0x80a7c2cf6d8318c6 0x5014f859edb06318 0xfbe7c7ffff8398e7 0xff7cf8fffff0731c

def z160 : W := mkw 0x022a55bfb0000000 0x00454ab7f6000000 0xb26647fff0000001 0xf64cc8fffe000000

def z161 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xa466403e3061ef7c 0x948cc807c60c3def

def z162 : W := mkw 0x800082004c021084 0x5000104009804210 0x58018601cc021083 0x6b0030c039804210

def z163 : W := mkw 0x21581f7096dc3e08 0x642b03ee12db87c1 0xfff87ff83ffc7f1e 0xdfff0fff07ff8fe3

def z164 : W := mkw 0x01dd87700fd71e06 0x603bb0ee01fae3c0 0xffff87f80fff9f06 0xfffff0ff01fff3e0

def z165 : W := mkw 0x0008077004841e00 0x600100ee009083c0 0xde1807f80c1c1f02 0xdbc300ff018383e0

def z166 : W := mkw 0x80858085490300c6 0x1010b010a9206018 0x00078007c00380e1 0x2000f000f800701c

def z167 : W := mkw 0xa0089e60dd8f3cce 0x740113cc1bb1e799 0xdc19fe21ff9ffcff 0x7b833fc43ff3ff9f

def z168 : W := mkw 0x07f7e99f2b7be007 0x80fefd33e56f7c00 0xfffff9de0fffe006 0xbfffff3bc1fffc00

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000021083 0x6200000000004210

def z170 : W := mkw 0x008d14a590000000 0x0011a294b2000000 0xf39fffe7f0000001 0xfe73fffcfe000000

def z171 : W := mkw 0x02a7708fb0000000 0x0054ee11f6000000 0xb067f83ff0000001 0xf60cff07fe000000

def z172 : W := mkw 0x00089c20980a2004 0x0001138413014400 0xdc19fe21fc1e6003 0x7b833fc43f83cc00

def z173 : W := mkw 0x048588000b7be007 0x8090b100016f7c00 0x7d8780000fffe006 0x2fb0f00001fffc00

def z174 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xdd99f8000f9e6002 0x3bb33f0001f3cc00

def z175 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x0c000621fc1e749b 0x418000c43f83ce93

def z176 : W := mkw 0x05f7e8850b7be007 0x80befd10a16f7c00 0xffffffc7cfffe007 0xfffffff8f9fffc00

def z177 : W := mkw 0x0085800009030006 0x0010b00001206000 0x498180000f800000 0x0930300001f00000

def z178 : W := mkw 0x400000000020c131 0x0800000000041826 0x0400000000606718 0x00800000000c0ce3

def z179 : W := mkw 0xe0089e2afc0e35bc 0x7c0113c55f81c6b7 0xdc19fe3ffc1e7ffb 0xfb833fc7ff83cfff

def z180 : W := mkw 0xe02ade2afc2ef5bd 0x7c055bc55f85deb7 0xfc7ffe3ffc7fffff 0xff8fffc7ff8fffff

def z181 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x5b8187c1cf821083 0x6b7030f839f04210

def z182 : W := mkw 0x0158177096d41e00 0x602b02ee12da83c0 0xfff9fff9fffc1f07 0xffff3fff3fff83e0

def z183 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0xfff801d80ffc0b06 0x9fff003b01ff8160

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000003800001f00 0xc0000007000003e0

def z185 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x439fffc7f0000001 0x2873fff8fe000000

def z186 : W := mkw 0x83fff7fffd8318c6 0x507ffeffffb06318 0xfbffffffff8398e7 0xff7ffffffff0731c

def z187 : W := mkw 0x602a5c2ab02ce539 0x2c054b8556059ca7 0xb47e783e307fffff 0xf68fcf07c60fffff

def z188 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb46640063063e0ff 0x368cc800c60c7c1f

def z189 : W := mkw 0x0158053000000000 0x002b00a600000000 0xf3f807f800000000 0xde7f00ff00000000

def z190 : W := mkw 0x03f7708fb0000000 0x007eee11f6000000 0xf1fff807f0000001 0x3e3fff00fe000000

def z191 : W := mkw 0x402a462a2424d531 0x680548c544849aa6 0xfc7e463e3c7fffff 0xff8fc8c7c78fffff

def z192 : W := mkw 0x0008077004841e00 0x600100ee009083c0 0xb66007f800601f06 0xd6cc00ff000c03e0

def z193 : W := mkw 0xa3ddbfb5dc0e348c 0x747bb7f6bb81c691 0x4b99bfc1cc1c0000 0x097337f839838000

def z194 : W := mkw 0x07fffdbfbb5b2006 0x80ffffb7f76b6400 0xfbffffffff9c0001 0xff7ffffffff38000

def z195 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4819fe01fc1e6099 0x29033fc03f83cc13

def z196 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0xf9fff8000f9c0000 0x3f3fff0001f38000

def z197 : W := mkw 0x0085008500000000 0x0010a010a0000000 0x738787c7c0000001 0xee70f0f8f8000000

def z198 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x2de600000fffe006 0x05bcc00001fffc00

def z199 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x738787c7c3818865 0xee70f0f8f870310c

def z200 : W := mkw 0x42a7708fb020c131 0x0854ee11f6041826 0x0007f807f003e0f9 0x2000ff00fe007c1f

def z201 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x846040383063fffe 0x108c0807060c7fff

def z202 : W := mkw 0x05ffed300b7be007 0x80bffda6016f7c00 0xfffffff80fffe006 0xffffffff01fffc00

def z203 : W := mkw 0xa0008a404ede3e8c 0x7400114809dbc7d1 0x0c0000000ffe7f9e 0x0180000001ffcff3

def z204 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000000002749a 0x0080000000004e93

def z205 : W := mkw 0xc5f7eacf6ffbf9f7 0xd8befd59edff7f3e 0xffffffffffffffff 0xffffffffffffffff

def z206 : W := mkw 0xc08582cf6d8319f6 0x5810b059edb0633e 0x7b8787ffff839fff 0xef70f0fffff073ff

def z207 : W := mkw 0x800082c54c8218c4 0x50001058a9904318 0x5a0187c7cc0218e3 0xeb4030f8f980431c

def z208 : W := mkw 0x800002c5448018c0 0x50000058a8900318 0x020007c1c0000000 0x004000f838000000

def z209 : W := mkw 0x85d5aac54fdb38c6 0xd0bab558a9fb6718 0x7b9fbfc7cf9f98e7 0xef73f7f8f9f3f31c

def z210 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c1cf838006 0x2f70f0f839f07000

def z211 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xcff807f80ffc0700 0x19ff00ff01ff80e0

def z212 : W := mkw 0xe0afdeeffdaffdff 0x7c15fbddffb5ffbf 0xffffffffffffffff 0xffffffffffffffff

def z213 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb066403e3003e0f9 0xf60cc807c6007c1f

def z214 : W := mkw 0x0150000002500000 0x002a0000004a0000 0xfdf800380ffc1f06 0xdfbf000701ff83e0

def z215 : W := mkw 0x03ff75bfb2540600 0x207feeb7f64a80c0 0xf7fffffff07c0701 0xfefffffffe0f80e0

def z216 : W := mkw 0x01f7e00009030006 0x003efc0001206000 0xf9fff8000f838006 0x3f3fff0001f07000

def z217 : W := mkw 0x017240000270c001 0x002e4800004e1800 0xfdfe40000fffe006 0x3fbfc80001fffc00

def z218 : W := mkw 0xa4008a004f7ff48f 0xf480114009effe91 0x0c0000000ffff49e 0x0180000001fffe93

def z219 : W := mkw 0x0085008500000000 0x0010a010a0000000 0x00078007c0000001 0x2000f000f8000000

def z220 : W := mkw 0x43f7619f2020c131 0x087eec33e4041826 0x23e601de00618b64 0x847cc03bc00c316c

def z221 : W := mkw 0x84008a404ffbf8c7 0xd080114809ff7f18 0x0c0000000ffff8e6 0x0180000001ffff1c

def z222 : W := mkw 0x0158053000000000 0x002b00a600000000 0x439807c000000000 0x087300f800000000

def z223 : W := mkw 0xa1589f70dede3e8c 0x742b13ee1bdbc7d1 0xdf99ffe1ff9e749b 0x7bf33ffc3ff3ce93

def z224 : W := mkw 0x03ff77ffb4801800 0x407feefff6900300 0xfbffffffff801807 0xff7ffffffff00300

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000002030001499 0x4000000406000293

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0xb460000000600006 0x168c0000000c0000

def z227 : W := mkw 0xa3ddbfb5dc0e348c 0x747bb7f6bb81c691 0xdf99ffe1fc1e749b 0x7bf33ffc3f83ce93

def z228 : W := mkw 0x800082004c021084 0x5000104009804210 0x48018601cc000000 0x090030c039800000

def z229 : W := mkw 0x05f760000371c003 0x80beec00006e3800 0xfdfe00000ffd8006 0x1fbfc00001ffb000

def z230 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff00398e7 0xfe7ffffffe00731c

def z231 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8203ffff49f 0x7fbfff0407fffe93

def z232 : W := mkw 0x03dd37f596d41e00 0x607ba6feb2da83c0 0xfff9bff9cffc1f06 0xdfff37ff39ff83e0

def z233 : W := mkw 0x00a7408f20000000 0x0014e811e4000000 0xf3e7c7fff0000001 0xfe7cf8fffe000000

def z234 : W := mkw 0x01d501d503d10a42 0x003aa03aa07a2148 0x23e601de03e18b64 0x847cc03bc07c316c

def z235 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff83e3fffe007 0xffbfff07c7fffc00

def z236 : W := mkw 0xa0081620d4041488 0x740102c41a808291 0x94004621f002749b 0x728008c43e004e93

def z237 : W := mkw 0x01f7608500000000 0x003eec10a0000000 0xf3ffffc7c0000001 0xfe7ffff8f8000000

def z238 : W := mkw 0x0008077004841e00 0x600100ee009083c0 0x7b8007f80f801f06 0xcf7000ff01f003e0

def z239 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff0606719 0xfefffffffe0c0ce3

def z240 : W := mkw 0x017a477a26d41e00 0x602f48ef44da83c0 0xfffe47fe3ffc1f07 0xffffc8ffc7ff83e0

def z241 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x040640063063ffff 0x2080c800c60c7fff

def z242 : W := mkw 0xa3fffffffede3e8c 0x747fffffffdbc7d1 0xfffffffffffe7f9f 0xffffffffffffcff3

def z243 : W := mkw 0x84a7eac54dabf8c7 0xd094fd58a9b57f18 0x7b87ffc7cf83f8e7 0xef70fff8f9f07f1c

def z244 : W := mkw 0x0422c8000b7be007 0x80845900016f7c00 0xbc6640000fffe006 0x378cc80001fffc00

def z245 : W := mkw 0x820817fff48018c0 0x504102fffe900318 0x020007fff00018e1 0xc04000fffe00031c

def z246 : W := mkw 0x808582854c021084 0x5010b050a9804210 0x7b8787c7cc021083 0xef70f0f8f9804210

def z247 : W := mkw 0x0158062006541400 0x602b00c400ca8280 0xfdf806200ffc1406 0x5fbf00c401ff8280

def z248 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x5819be01cc1e1083 0x6b0337c03983c210

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0xb40640263003fcff 0xf680c804c6007f9f

def z250 : W := mkw 0x0008062004041400 0x600100c400808280 0xdc1806200c1c1402 0x5b8300c401838280

def z251 : W := mkw 0x417a453a2020c131 0x082f48a744041826 0xf7fe47fe3063ffff 0xfeffc8ffc60c7fff

def z252 : W := mkw 0x05f7615003f1ca03 0x80beec2a007e3940 0x23e601d803e18b04 0x847cc03b007c3160

def z253 : W := mkw 0x008502c505811842 0x4010a058a0b02308 0x7b8607c60f819866 0xcf70c0f8c1f0330c

def z254 : W := mkw 0x01d5200000000000 0x003aa40000000000 0x4199b80000000000 0x0833370000000000

def z255 : W := mkw 0x0158153090000000 0x002b02a612000000 0xf3f9fff9f0000001 0xfe7f3fff3e000000

def z256 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8000ffffffe 0x3fbfff0001ffffff

def z257 : W := mkw 0x0022400a20000000 0x0004480144000000 0x8060403830000000 0x100c080706000000

def z258 : W := mkw 0x85f7e2c54ff3d8c7 0xd0befc58a9fe7b18 0x7be787c7cfe398e7 0xef7cf0f8f9fc731c

def z259 : W := mkw 0xa1589f30dc0e348c 0x742b13e61b81c691 0xfff9fff9fc1e749b 0xffff3fff3f83ce93

def z260 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x499ff8000f9fe000 0x2933ff0001f3fc00

def z261 : W := mkw 0x0150035006d41e00 0x602a006a00da83c0 0x2fe001d80ffc1f06 0x85fc003b01ff83e0

def z262 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z263 : W := mkw 0x43ff77ffb6f4df31 0x687feefff6de9be6 0xffffffffffffffff 0xffffffffffffffff

def z264 : W := mkw 0x020815b590000000 0x004102b6b2000000 0x020007c1c0000000 0x004000f838000000

def z265 : W := mkw 0x0008077004841e00 0x600100ee009083c0 0x020007c000000000 0x004000f800000000

def z266 : W := mkw 0x0022400a20000000 0x0004480144000000 0x0006400630000001 0x2000c800c6000000

def z267 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x8460403e30607ff9 0xd08c0807c60c0fff

def z268 : W := mkw 0x0085000001010002 0x0010a00000202000 0x2186000003818004 0x0430c00000703000

def z269 : W := mkw 0xa4089e20df7ff48f 0xf48113c41beffe91 0xdc19fe21fffff49f 0x7b833fc43ffffe93

def z270 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0x4d99b8000fffe006 0x09b3370001fffc00

def z271 : W := mkw 0x002240000020c001 0x0004480000041800 0x8460400000606000 0x108c0800000c0c00

def z272 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x0001fe21f0027499 0x60003fc43e004e93

def z273 : W := mkw 0xa3fffffffd8f3cce 0x747fffffffb1e799 0xffffffffff9ffcff 0xfffffffffff3ff9f

def z274 : W := mkw 0x00008800080a2004 0x0000110001014400 0x0c0000000c1e6002 0x018000000183cc00

def z275 : W := mkw 0x07f7f88fbb7be007 0x80feff11f76f7c00 0xfdfff807ffffe007 0x3fbfff00fffffc00

def z276 : W := mkw 0xa0859ac5dd8b38ce 0x5410b358bbb16719 0x7b87ffc7ff83f8ff 0xef70fff8fff07f1f

def z277 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x69ffb8000ffd8004 0x0d3ff70001ffb000

def z278 : W := mkw 0x602a5c2ab02ce539 0x2c054b8556059ca7 0x84787838307c6718 0x108f0f07060f8ce3

def z279 : W := mkw 0x0158053000000000 0x002b00a600000000 0x8078003800000000 0x100f000700000000

def z280 : W := mkw 0x02a7708fb0000000 0x0054ee11f6000000 0x7387ffc7f0000001 0xee70fff8fe000000

def z281 : W := mkw 0xa20817bff4041488 0x744102f7fe808291 0x020007fff0001499 0xc04000fffe000293

def z282 : W := mkw 0x85f7e8854b7be0c7 0x90befd10a96f7c18 0xfdfff807cfffe0e7 0x3fbfff00f9fffc1c

def z283 : W := mkw 0x81d583d54fd31ac6 0x503ab07aa9fa6358 0x7be787dfcfe39be7 0xef7cf0fbf9fc737c

def z284 : W := mkw 0x03ff67ff26d41e00 0x607fecffe4da83c0 0xfffe07fe0ffc1f06 0xdfffc0ffc1ff83e0

def z285 : W := mkw 0xa1589f70dede3e8c 0x742b13ee1bdbc7d1 0x4b99bfc1cf9c0000 0x097337f839f38000

def z286 : W := mkw 0x0008142090000000 0x0001028412000000 0xd419fe21f002749b 0x7a833fc43e004e93

def z287 : W := mkw 0xc022c20a6c22d1b5 0x580458414d845a36 0xfc67c63ffc63ffff 0xff8cf8c7ff8c7fff

def z288 : W := mkw 0x4000000000000130 0x0800000000000026 0x0000000000001ff8 0x00000000000003ff

def z289 : W := mkw 0x0008142090000000 0x0001028412000000 0x8018782030000000 0x10030f0406000000

def z290 : W := mkw 0x47fffdbfbb7be137 0x88ffffb7f76f7c26 0xffffffffffffffff 0xffffffffffffffff

def z291 : W := mkw 0x20081c20900c2408 0x2401038412018481 0x84187820301c6418 0x10830f0406038c83

def z292 : W := mkw 0x85ffeff54ffffec7 0xf0bffdfea9ffffd8 0xffffffffcfffffe7 0xfffffffff9fffffc

def z293 : W := mkw 0x80089620dc021084 0x500112c41b804210 0xd819fe21fc021083 0x7b033fc43f804210

def z294 : W := mkw 0x8000020044001080 0x5000004008800210 0x00000601c0001081 0x400000c038000210

def z295 : W := mkw 0x400000000020c131 0x0800000000041826 0xb46000380063fffe 0xd68c0007000c7fff

def z296 : W := mkw 0x808582004d031086 0x5010b04009a06210 0x79878601cf839087 0x6f30f0c039f07210

def z297 : W := mkw 0x05ddaf700fdf3e06 0xe0bbb5ee01fbe7c0 0x4b99bfc00f9c0000 0x097337f801f38000

def z298 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0601f07 0xfefffffffe0c03e0

def z299 : W := mkw 0x03fff5bfb9030006 0x007ffeb7f7206000 0xfbffffffff838007 0xff7ffffffff07000

def z300 : W := mkw 0x84a7e885492be0c7 0x9094fd10a9257c18 0x0007f807c003e0e1 0x2000ff00f8007c1c

def z301 : W := mkw 0x05f7e0000b73c007 0x80befc00016e7800 0x79e780000fe38006 0x2f3cf00001fc7000

def z302 : W := mkw 0x0000024004801800 0x4000004800900300 0x7b8607c60f8398e7 0xef70c0f8c1f0731c

def z303 : W := mkw 0x015088000a5a2004 0x002a1100014b4400 0xfdf9f8000ffe6006 0x3fbf3f0001ffcc00

def z304 : W := mkw 0x03f761df21810842 0x007eec3be4302108 0x23e601de03818864 0x847cc03bc070310c

def z305 : W := mkw 0x03f7619f20000000 0x007eec33e4000000 0x73e787dfc0000001 0xee7cf0fbf8000000

def z306 : W := mkw 0x402a542ab020c131 0x08054a8556041826 0xf47ffe3ff063ffff 0xfe8fffc7fe0c7fff

def z307 : W := mkw 0x4000000a20000130 0x0800000144000026 0x0000003830000718 0x00000007060000e3

def z308 : W := mkw 0x2008142090040408 0x2401028412008081 0x0000002030000418 0x0000000406000083

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0x9400002000001402 0x5280000400000280

def z310 : W := mkw 0x05fffc209b7be007 0x80bfff84136f7c00 0xfdfffe21ffffe007 0x7fbfffc43ffffc00

def z311 : W := mkw 0x00008800080a2004 0x0000110001014400 0x4819b8000c1c0000 0x0903370001838000

def z312 : W := mkw 0x0150024006d01800 0x402a004800da0300 0xfff807c00ffc1806 0xdfff00f801ff8300

def z313 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8383fffe71e 0x3fbfff0707fffce3

def z314 : W := mkw 0x002240000020c001 0x0004480000041800 0x000640000003e000 0x2000c80000007c00

def z315 : W := mkw 0x4022424a26f4df31 0x6804484944de9be6 0xbc66403e3fffffff 0xf78cc807c7ffffff

def z316 : W := mkw 0x82a7f2cffd8318c6 0x5054fe59ffb06318 0x7b87ffc7ff8398e7 0xef70fff8fff0731c

def z317 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xf3f9bff9c0000000 0xde7f37ff38000000

def z318 : W := mkw 0x808502c5458118c2 0x5010a058a8b02318 0x238607c7c38198e5 0xc470c0f8f870331c

def z319 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x739fbfc7c0000001 0xee73f7f8f8000000

def z320 : W := mkw 0x017a453a20000000 0x002f48a744000000 0xf3fe47fe30000001 0xfe7fc8ffc6000000

def z321 : W := mkw 0x2000180090082008 0x0400030012010401 0x0000780030006018 0x00000f0006000c03

def z322 : W := mkw 0x057268000278e001 0x80ae4d00004f1c00 0xfdf878000ffc6006 0x1fbf0f0001ff8c00

def z323 : W := mkw 0x0008053000000000 0x000100a600000000 0x020007f800000000 0xc04000ff00000000

def z324 : W := mkw 0x400000000020c131 0x0800000000041826 0x0000000000618b64 0x00000000000c316c

def z325 : W := mkw 0xa1589e20de5e348c 0x742b13c41bcbc691 0xfdf9fe21fffe749f 0x7fbf3fc43fffce93

def z326 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb466003e00619f66 0xd68cc007c00c33ec

def z327 : W := mkw 0xa5ddbe20df5f348e 0xf4bbb7c41bebe691 0xdd99fe21ff9e749b 0x7bb33fc43ff3ce93

def z328 : W := mkw 0x0008062004041400 0x600100c400808280 0xfc7806380c7c1f06 0xdf8f00c7018f83e0

def z329 : W := mkw 0x828d97fffd8318c6 0x5051b2ffffb06318 0x7b8787ffff8398e7 0xef70f0fffff0731c

def z330 : W := mkw 0x400000000020c131 0x0800000000041826 0x340600060063ffff 0xe680c000c00c7fff

def z331 : W := mkw 0x0158073006541600 0x602b00e600ca82c0 0xdc7806380c7c1702 0x5b8f00c7018f82e0

def z332 : W := mkw 0xa0009a00dc0e348c 0x740013401b81c691 0x0c01f801fc1e749b 0x21803f003f83ce93

def z333 : W := mkw 0x0150000002500000 0x002a0000004a0000 0x499800000f9c0000 0x0933000001f38000

def z334 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc79fe39fc7e7f9f 0xff8f3fc73f8fcff3

def z335 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x2066401e3063ebfd 0xa40cc803c60c7d7f

def z336 : W := mkw 0x0085808509030006 0x0010b010a1206000 0x7b8787c7cf838007 0xef70f0f8f9f07000

def z337 : W := mkw 0x0000000a20000000 0x0000000144000000 0x0000003e30000001 0xc0000007c6000000

def z338 : W := mkw 0x017a477006f4de01 0x602f48ee00de9bc0 0xfffe47f80fffff06 0xffffc8ff01ffffe0

def z339 : W := mkw 0x00a7600000000000 0x0014ec0000000000 0x0007f80000000000 0x2000ff0000000000

def z340 : W := mkw 0x04008a400ffffe07 0xe080114801ffffc0 0x0c0000000fffff06 0x0180000001ffffe0

def z341 : W := mkw 0x80000085400000c0 0x10000010a8000018 0x00000007c00000e1 0x00000000f800001c

def z342 : W := mkw 0x0158053000000000 0x002b00a600000000 0xf7f807f800601f06 0xdeff00ff000c03e0

def z343 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xd819fe21fc1c0001 0x7b033fc43f838000

def z344 : W := mkw 0x0150011000000000 0x002a002200000000 0x23e001d800000000 0x847c003b00000000

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x8460003800600700 0x108c0007000c00e0

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x2006000600018864 0x8400c000c000310c

def z347 : W := mkw 0x800807f544841ec0 0x700100fea89083d8 0x020007ffc0001fe1 0xc04000fff80003fc

def z348 : W := mkw 0x0085008500000000 0x0010a010a0000000 0x738787c7c00398e7 0xee70f0f8f800731c

def z349 : W := mkw 0x0008066006d41e00 0x600100cc00da83c0 0xdc1806200ffc1f06 0x5b8300c401ff83e0

def z350 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xc3f9fff9f0000000 0x187f3fff3e000000

def z351 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x7b9807c00f9c1806 0xcf7300f801f38300

def z352 : W := mkw 0x05f768000379e003 0x80beed00006f3c00 0xa5fe780003fde004 0x14bfcf00007fbc00

def z353 : W := mkw 0x808582c54fd71ec6 0x7010b058a9fae3d8 0x7f8787c7cfff9fe7 0xeff0f0f8f9fff3fc

def z354 : W := mkw 0x028d15bfb0000000 0x0051a2b7f6000000 0x738787fff0000001 0xee70f0fffe000000

def z355 : W := mkw 0x81f7e2c54d8318c6 0x503efc58a9b06318 0xfbffffc7cf8398e7 0xff7ffff8f9f0731c

def z356 : W := mkw 0x040008000278e001 0x80800100004f1c00 0x04000000007c6000 0x00800000000f8c00

def z357 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0x4399bffff0000001 0xc87337fffe000000

def z358 : W := mkw 0x4000000a20000130 0x0800000144000026 0x0000001e00000b60 0x80000003c000016c

def z359 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x0060001800600300 0x000c0003000c0060

def z360 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8187c1cf8398e6 0x097030f839f0731c

def z361 : W := mkw 0x05f760000371c003 0x80beec00006e3800 0xb5e6400003e3e006 0x36bcc800007c7c00

def z362 : W := mkw 0x0000004000800800 0x0000000800100100 0x238001c003800804 0x8470003800700100

def z363 : W := mkw 0x0000800009030006 0x0000100001206000 0x080000000f838006 0x0100000001f07000

def z364 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0x038001c003800000 0x0070003800700000

def z365 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb460403830607f1e 0xd68c0807060c0fe3

def z366 : W := mkw 0xc00082404da3d9f7 0x5800104809b47b3e 0x0c0000000fe3fffe 0x0180000001fc7fff

def z367 : W := mkw 0x040088000b5b2006 0x80801100016b6400 0x080000000f9c0000 0x0100000001f38000

def z368 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe01cc1e6002 0x3b833fc03983cc00

def z369 : W := mkw 0x0158057002d40e00 0x202b00ae005a81c0 0xa7f801f803fc0f04 0x94ff003f007f81e0

def z370 : W := mkw 0x81dd87f54d8318c6 0x503bb0fea9b06318 0xfbff87ffcf8398e7 0xff7ff0fff9f0731c

def z371 : W := mkw 0x422a55bfb020c131 0x08454ab7f6041826 0xb66647fff063ffff 0xf6ccc8fffe0c7fff

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000398e6 0x000000000000731c

def z373 : W := mkw 0xc0a7c2cf6da3d9f7 0x5814f859edb47b3e 0x7b87c7c7ff83f8ff 0xef70f8f8fff07f1f

def z374 : W := mkw 0x0085008500000000 0x0010a010a0000000 0x238601c600000000 0x8470c038c0000000

def z375 : W := mkw 0x815887704ed61e84 0x702b10ee09dac3d0 0xfff987f9cffe1f87 0xffff30ff39ffc3f0

def z376 : W := mkw 0x4172415a22f0cb31 0x082e482b445e1966 0xb7e641fe33e3ffff 0xf6fcc83fc67c7fff

def z377 : W := mkw 0x03ff65bf20000000 0x007fecb7e4000000 0xf3fe07fe00000000 0xde7fc0ffc0000000

def z378 : W := mkw 0x800082404d8318c6 0x5000104809b06318 0x380600060f8398e7 0xe700c000c1f0731c

def z379 : W := mkw 0x07ff7dbfb278e001 0x80ffefb7f64f1c00 0xf7fffffff07c6001 0xfefffffffe0f8c00

def z380 : W := mkw 0x0022c800082ae005 0x0004590001055c00 0xfc7ff8000c7fe006 0x3f8fff00018ffc00

def z381 : W := mkw 0x83fff7ffffd71ec6 0x707ffefffffae3d8 0xffffffffffff9fe7 0xfffffffffffff3fc

def z382 : W := mkw 0x0000024006d41e00 0x6000004800da83c0 0x080000000f9c0000 0x0100000001f38000

def z383 : W := mkw 0x0000000000000000 0x0000000000000000 0xd019f80000000000 0x3a033f0000000000

def z384 : W := mkw 0x0000008500000000 0x00000010a0000000 0x020007c7c0000001 0xc04000f8f8000000

def z385 : W := mkw 0x0008053000040600 0x200100a6000080c0 0x0000003800000700 0x00000007000000e0

def z386 : W := mkw 0x04a7e800092be007 0x8094fd0001257c00 0xb467f8000063e006 0x368cff00000c7c00

def z387 : W := mkw 0x0000004001810842 0x0000000800302108 0x0000000003818864 0x000000000070310c

def z388 : W := mkw 0x800082404fd71ec6 0x7000104809fae3d8 0x0c0000000fff9fe6 0x0180000001fff3fc

def z389 : W := mkw 0x20000800000c2408 0x2400010000018481 0x04000000001c6418 0x0080000000038c83

def z390 : W := mkw 0x82a7f08ff90300c6 0x1054fe11ff206018 0x0007f807f00380e1 0x2000ff00fe00701c

def z391 : W := mkw 0x0000024004801800 0x4000004800900300 0xffe007f80fe01f06 0xdffc00ff01fc03e0

def z392 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x6bf807d80ffc0b04 0x8d7f00fb01ff8160

def z393 : W := mkw 0x25fffc209b7fe40f 0xa4bfff84136ffc81 0xfdfff8203fffe41e 0x3fbfff0407fffc83

def z394 : W := mkw 0x020817ffb4841e00 0x604102fff69083c0 0x020007fff0001f01 0xc04000fffe0003e0

def z395 : W := mkw 0x0000100090000000 0x0000020012000000 0x0001f801f0000001 0x20003f003e000000

def z396 : W := mkw 0x020815bfb0000000 0x004102b7f6000000 0xd219fffff0000001 0xfa433ffffe000000

def z397 : W := mkw 0xa2affeaffc0e348c 0x7455ffd5ff81c691 0xdc1ffe27fc1e749b 0x7b83ffc4ff83ce93

def z398 : W := mkw 0x0085008501010042 0x0010a010a0202008 0x0006000600018060 0x0000c000c000300c

def z399 : W := mkw 0xa08d9ea5dd0f34ce 0x7411b3d4bba1e699 0xdc1ffe27fc1ff4fb 0x7b83ffc4ff83fe9f

def z400 : W := mkw 0x0022400a20000000 0x0004480144000000 0x2066001e00000000 0x840cc003c0000000

def z401 : W := mkw 0x0008142090000000 0x0001028412000000 0x4019be01c0000000 0x080337c038000000

def z402 : W := mkw 0x05d5200003510002 0x80baa400006a2000 0x0180000003800000 0x0030000000700000

def z403 : W := mkw 0x057a6f7006fcfe01 0xe0af4dee00df9fc0 0xfff87ff80ffc7f06 0xdfff0fff01ff8fe0

def z404 : W := mkw 0xe17adf7afefeffbd 0x7c2f5bef5fdfdff7 0xffffffffffffffff 0xffffffffffffffff

def z405 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x847ff800007fe000 0x308fff00000ffc00

def z406 : W := mkw 0x800082004c021084 0x5000104009804210 0x080000000c021082 0x0100000001804210

def z407 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x23e607fff0000001 0xc47cc0fffe000000

def z408 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf800001 0xef70f0f8f9f00000

def z409 : W := mkw 0x04a760000121c003 0x8094ec0000243800 0x0006000000018000 0x0000c00000003000

def z410 : W := mkw 0x4422c80a2b7be137 0x88845901456f7c26 0xbc66403e3fffffff 0xf78cc807c7ffffff

def z411 : W := mkw 0x4158077a26d41f30 0x682b00ef44da83e6 0xfff807fe3ffc1fff 0xdfff00ffc7ff83ff

def z412 : W := mkw 0x037a753ab0000000 0x006f4ea756000000 0xd079fe39f0000001 0x7a0f3fc73e000000

def z413 : W := mkw 0xa0089c20d80e248c 0x340113841b01c491 0x8419f821f01e6499 0x30833f043e03cc93

def z414 : W := mkw 0x440088000b7be137 0x88801100016f7c26 0x0c0000000ffffffe 0x0180000001ffffff

def z415 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x038001c003800000 0x0070003800700000

def z416 : W := mkw 0xa0081620d4041488 0x740102c41a808291 0xdc180621fc1c149b 0x5b8300c43f838293

def z417 : W := mkw 0x40a7408f2020c131 0x0814e811e4041826 0xf7e7c7fff063ffff 0xfefcf8fffe0c7fff

def z418 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x0006000600018060 0x0000c000c000300c

def z419 : W := mkw 0x01f7e800080a2004 0x003efd0001014400 0xfdfff8000c1e6002 0x3fbfff000183cc00

def z420 : W := mkw 0x85f7eac54ffbf8c7 0xd0befd58a9ff7f18 0xffffffc1cfffe006 0x3ffffff839fffc00

def z421 : W := mkw 0x03ff77ffb6d41e00 0x607feefff6da83c0 0xfbffffffff9c0001 0xff7ffffffff38000

def z422 : W := mkw 0x05ddaf700fdf3e06 0xe0bbb5ee01fbe7c0 0xfff9bff80ffc1f06 0xdfff37ff01ff83e0

def z423 : W := mkw 0xa0089f70dc8e3e8c 0x740113ee1b91c7d1 0xde19fff9fc1e7f9b 0xfbc33fff3f83cff3

def z424 : W := mkw 0x0000024006d41e00 0x6000004800da83c0 0x7f8007c00ffc1f06 0xcff000f801ff83e0

def z425 : W := mkw 0x0485a800090b2006 0x8090b50001216400 0x0001b80000000000 0x0000370000000000

def z426 : W := mkw 0x85d5aac54fdb38c6 0xd0bab558a9fb6718 0x4b99bfc1cf9c0000 0x097337f839f38000

def z427 : W := mkw 0x057268000278e001 0x80ae4d00004f1c00 0xb47e7800007fe006 0x368fcf00000ffc00

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000400030026099 0x2000080006004c13

def z429 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfbf807f80f9c0000 0xdf7f00ff01f38000

def z430 : W := mkw 0x03f761df22d00a00 0x007eec3be45a0140 0x23e601de03e00b04 0x847cc03bc07c0160

def z431 : W := mkw 0x0222700ab0000000 0x00444e0156000000 0x0000780030000000 0x00000f0006000000

def z432 : W := mkw 0xa1581770d6d41e88 0x742b02ee1ada83d1 0xfff807f9fffc1f9f 0xdfff00ff3fff83f3

def z433 : W := mkw 0xa0088e204c0e348c 0x740111c40981c691 0xdc1806200c1e749a 0x5b8300c40183ce93

def z434 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x21e7f80003e3e004 0x243cff00007c7c00

def z435 : W := mkw 0x01ff677006d41e00 0x603fecee00da83c0 0xfffffff80ffc1f06 0xffffffff01ff83e0

def z436 : W := mkw 0x0200019f20000000 0x00400033e4000000 0x020001de00000000 0x8040003bc0000000

def z437 : W := mkw 0x05f760c503f1c843 0x80beec18a07e3908 0x23e601c603e18864 0x847cc038c07c310c

def z438 : W := mkw 0x0572e8000b7be007 0x80ae5d00016f7c00 0x8c7878000fffe006 0x118f0f0001fffc00

def z439 : W := mkw 0x4022c80a282ae135 0x0804590145055c26 0xfc7ff83e3c7fffff 0xff8fff07c78fffff

def z440 : W := mkw 0x037a75bfb0000000 0x006f4eb7f6000000 0x82787ffff0000001 0xd04f0ffffe000000

def z441 : W := mkw 0x20081c20900c2408 0x2401038412018481 0x94187820301e749b 0x72830f040603ce93

def z442 : W := mkw 0x055088000b7be007 0x80aa1100016f7c00 0xfdf800000fffe006 0x1fbf000001fffc00

def z443 : W := mkw 0x808d86e54d871cc6 0x7011b0dca9b0e398 0xff9f87e7cf9f9ce7 0xfff3f0fcf9f3f39c

def z444 : W := mkw 0x0372611a20000000 0x006e4c2344000000 0x0060001800000000 0x000c000300000000

def z445 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x0000400030006018 0x0000080006000c03

def z446 : W := mkw 0x0085000000000000 0x0010a00000000000 0x7187800000000000 0x2e30f00000000000

def z447 : W := mkw 0xc08582c54da3d9f7 0x5810b058a9b47b3e 0x7f8787c7cfe3ffff 0xeff0f0f8f9fc7fff

def z448 : W := mkw 0xe022d80af82ae1bd 0x1c045b015f055c37 0x0007f807f003e0f9 0x2000ff00fe007c1f

def z449 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff81e0fffeb66 0xbfbfff03c1fffd6c

def z450 : W := mkw 0x05588f700ffffe07 0xe0ab11ee01ffffc0 0xfff807f80fffff06 0xdfff00ff01ffffe0

def z451 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x0006403e3003fff9 0xe000c807c6007fff

def z452 : W := mkw 0x06a7f88fb92be007 0x80d4ff11f7257c00 0x0007f807f003e001 0x2000ff00fe007c00

def z453 : W := mkw 0x40a740cf21a1c973 0x0814e819e434392e 0x23e601de03e18b64 0x847cc03bc07c316c

def z454 : W := mkw 0xa08d9ee5dd8f3cce 0x7411b3dcbbb1e799 0x7b9fbfc7cf9f98e7 0xef73f7f8f9f3f31c

def z455 : W := mkw 0xa5ffff70dffffe8f 0xf4bfffee1bffffd1 0xfffffff9ffffff9f 0xffffffff3ffffff3

def z456 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0x9401f821f002749b 0x72803f043e004e93

def z457 : W := mkw 0x85f7ea404ffbf8c7 0xd0befd4809ff7f18 0xfdfff8000ffff8e6 0x3fbfff0001ffff1c

def z458 : W := mkw 0x008580c509830846 0x0010b018a1306108 0x7b8781c60f838866 0xaf70f038c1f0710c

def z459 : W := mkw 0x81dd87f54fd71ec6 0x703bb0fea9fae3d8 0x7b9f87c7cf9f98e7 0xef73f0f8f9f3f31c

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060006000380e1 0x2000c000c000701c

def z461 : W := mkw 0x0022400a20000000 0x0004480144000000 0xb066403e300398e7 0xf60cc807c600731c

def z462 : W := mkw 0x21581d30925c2608 0x242b03a6124b84c1 0x84787838307c6718 0x108f0f07060f8ce3

def z463 : W := mkw 0x402240000020c131 0x0804480000041826 0xb46640000063fffe 0x368cc800000c7fff

def z464 : W := mkw 0x05f760000371c003 0x80beec00006e3800 0xf1fff80003e18004 0x3e3fff00007c3000

def z465 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc1ffe27fc1ffcff 0xff83ffc4ff83ff9f

def z466 : W := mkw 0x03ff75ffb1810842 0x007feebff6302108 0xf3fffffff3818865 0xfe7ffffffe70310c

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x3006000000038006 0x2600c00000007000

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000000601f06 0x00800000000c03e0

def z469 : W := mkw 0x0150000002500000 0x002a0000004a0000 0x84780000007c0000 0x108f0000000f8000

def z470 : W := mkw 0x800002c5448018c0 0x50000058a8900318 0x7b8007c7cf8018e7 0xcf7000f8f9f0031c

def z471 : W := mkw 0x84858ac54ffbf8c7 0xd090b158a9ff7f18 0x7f8787c7cffff8e7 0xeff0f0f8f9ffff1c

def z472 : W := mkw 0x4000000a20000130 0x0800000144000026 0x3006003e30039fff 0xe600c007c60073ff

def z473 : W := mkw 0xa57afe20de7ef48d 0xf4af5fc41bcfde91 0xdc79fe21fc7e749b 0x7b8f3fc43f8fce93

def z474 : W := mkw 0xa1589f30de5e368c 0x742b13e61bcbc6d1 0xdc79fe39fc7e779b 0x7b8f3fc73f8fcef3

def z475 : W := mkw 0xa02ade20dc2ef48d 0x74055bc41b85de91 0xfc7ffe21fc7ff49f 0x7f8fffc43f8ffe93

def z476 : W := mkw 0x4000000a20000130 0x0800000144000026 0xb460003e30601fff 0xd68c0007c60c03ff

def z477 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0x0001b801c0000000 0x0000370038000000

def z478 : W := mkw 0x237a7d3ab00c2408 0x246f4fa756018481 0x84787838301c6418 0x108f0f0706038c83

def z479 : W := mkw 0x0022400a20000000 0x0004480144000000 0xb466403e3002749b 0xf68cc807c6004e93

def z480 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x4b9807f80f9c1f00 0xc97300ff01f383e0

def z481 : W := mkw 0x002240000020c001 0x0004480000041800 0xb46640060063f8e7 0xf68cc800c00c7f1c

def z482 : W := mkw 0x05ff677007f5de03 0xe0bfecee00febbc0 0xfffe07f80ffd9f06 0xdfffc0ff01ffb3e0

def z483 : W := mkw 0x4572680a2278e131 0x88ae4d01444f1c26 0xb47e783e307fffff 0xf68fcf07c60fffff

def z484 : W := mkw 0x002a542ab0000000 0x00054a8556000000 0xf07ffe3ff0000001 0xfe0fffc7fe000000

def z485 : W := mkw 0x03ff75ffb2d00a00 0x007feebff65a0140 0xf3fffffff3e00b05 0xfe7ffffffe7c0160

def z486 : W := mkw 0x45ffef7a2fffff37 0xe8bffdef45ffffe6 0xfffffffe3fffffff 0xffffffffc7ffffff

def z487 : W := mkw 0xe008162af40415b8 0x7c0102c55e8082b7 0x0000063ff0001ff9 0xc00000c7fe0003ff

def z488 : W := mkw 0x0208153ab0000000 0x004102a756000000 0x0000003830000000 0x0000000706000000

def z489 : W := mkw 0x057260000270c001 0x80ae4c00004e1800 0x0060000000600000 0x000c0000000c0000

def z490 : W := mkw 0x000000c500800840 0x00000018a0100108 0x020001c600000860 0x80400038c000010c

def z491 : W := mkw 0x87fffffffffbf8c7 0xd0ffffffffff7f18 0xfffffffffffff8e7 0xffffffffffffff1c

def z492 : W := mkw 0xe3ffffbffc2ef5bd 0x7c7ffff7ff85deb7 0xfffffffffc7fffff 0xffffffffff8fffff

def z493 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8380fffff06 0xffbfff0701ffffe0

def z494 : W := mkw 0x83fff5bff90300c6 0x107ffeb7ff206018 0xf3fffffff00380e1 0xfe7ffffffe00701c

def z495 : W := mkw 0x800082404c821884 0x5000104809904310 0x7b8187c1cf821887 0xef7030f839f04310

def z496 : W := mkw 0x800082c54d8318c6 0x50001058a9b06318 0x0a0007c7cf8398e7 0xc14000f8f9f0731c

def z497 : W := mkw 0xa4a7f800d92be08f 0x9494ff001b257c11 0x0007f801f003e099 0x2000ff003e007c13

def z498 : W := mkw 0x057a6d30027ce601 0xa0af4da6004f9cc0 0x84787838007c6700 0x108f0f07000f8ce0

def z499 : W := mkw 0x0158053002540600 0x202b00a6004a80c0 0x00180000001c0000 0x0003000000038000

def z500 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff0618b65 0xfe7ffffffe0c316c

def z501 : W := mkw 0x417a453a2274c731 0x282f48a7444e98e6 0xb47e403e307fffff 0xf68fc807c60fffff

def z502 : W := mkw 0xa2089fbffc0e348c 0x744113f7ff81c691 0xde19fffffc1e749b 0xfbc33fffff83ce93

def z503 : W := mkw 0xa0081620d4041488 0x740102c41a808291 0xd019fe21f0001499 0x7a033fc43e000293

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x9400400000026002 0x3280080000004c00

def z505 : W := mkw 0xa0008a004c0e348c 0x740011400981c691 0x5c018601cc1e749b 0x6b8030c03983ce93

def z506 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807c00ffc0006 0x1fff00f801ff8000

def z507 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x3066001e00639be7 0xe60cc003c00c737c

def z508 : W := mkw 0x0008062004041400 0x600100c400808280 0x0000062000001400 0x400000c400000280

def z509 : W := mkw 0xa02ade2afc0e348c 0x74055bc55f81c691 0xfc7ffe3ffc1e749b 0xff8fffc7ff83ce93

def z510 : W := mkw 0xa1588f704ede3e8c 0x742b11ee09dbc7d1 0xfff807f80ffe7f9e 0xdfff00ff01ffcff3

def z511 : W := mkw 0x01ff653000000000 0x003feca600000000 0xf3fffff800000000 0xfe7fffff00000000

def z512 : W := mkw 0x0000020004001000 0x4000004000800200 0x580006000c001002 0x4b0000c001800200

def z513 : W := mkw 0x44a7e80a292be137 0x8894fd0145257c26 0xb467f83e3063ffff 0xf68cff07c60c7fff

def z514 : W := mkw 0x03ff77bfb4041400 0x607feef7f6808280 0xfffffffffc1c1403 0xffffffffff838280

def z515 : W := mkw 0x07f7619f2371c003 0x80feec33e46e3800 0x23e601de03e18004 0x847cc03bc07c3000

def z516 : W := mkw 0x800082004c021084 0x5000104009804210 0xdc01c621fc02749b 0x7b8038c43f804e93

def z517 : W := mkw 0xa0089c20d80a208c 0x140113841b014411 0xd019fe21f0026099 0x7a033fc43e004c13

def z518 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff003e0f9 0xfe7ffffffe007c1f

def z519 : W := mkw 0xa0008a004c0e348c 0x740011400981c691 0x9c0040203c1e749b 0x738008040783ce93

def z520 : W := mkw 0xe022ca0a6c2ef5bd 0x7c0459414d85deb7 0xbc66403e3c7fffff 0xf78cc807c78fffff

def z521 : W := mkw 0xa0089620dc06148c 0x740112c41b80c291 0x58018621fc02149b 0x6b0030c43f804293

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000402030000001 0x7200080406000000

def z523 : W := mkw 0x83ddb7f5dd8318c6 0x507bb6febbb06318 0x7b9fbfc7cf8398e7 0xef73f7f8f9f0731c

def z524 : W := mkw 0x417a477a26f4df31 0x682f48ef44de9be6 0xfff847f83ffc7f1e 0xdfff08ff07ff8fe3

def z525 : W := mkw 0x05f7e9500bfbea07 0x80befd2a017f7d40 0xfffff9d80fffeb06 0xbfffff3b01fffd60

def z526 : W := mkw 0x808582854d0310c6 0x5010b050a9a06218 0x58078607cc0390e3 0x6b00f0c0f980721c

def z527 : W := mkw 0xa0081620d4041488 0x740102c41a808291 0x00000601c0000000 0x000000c038000000

def z528 : W := mkw 0x0008042000000000 0x0001008400000000 0xd018062000000000 0x5a0300c400000000

def z529 : W := mkw 0x80858085490300c6 0x1010b010a9206018 0x79878007cf8380e7 0x2f30f000f9f0701c

def z530 : W := mkw 0xa5ddbe20df5f348e 0xf4bbb7c41bebe691 0x4999be01cf9c0000 0x093337c039f38000

def z531 : W := mkw 0x0000800008020004 0x0000100001004000 0x580180000c020002 0x2b00300001804000

def z532 : W := mkw 0xe02a562af424d5b9 0x7c054ac55e849ab7 0xb466463ff063ffff 0xf68cc8c7fe0c7fff

def z533 : W := mkw 0x0000000002500000 0x00000000004a0000 0x0c0000000ffc0006 0x0180000001ff8000

def z534 : W := mkw 0x04a7e800092be007 0x8094fd0001257c00 0xdc1ff8000c1fe002 0x3b83ff000183fc00

def z535 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb466403e30606719 0xf68cc807c60c0ce3

def z536 : W := mkw 0xc0a7c08f6923c1f7 0x1814f811ed24783e 0xb467c03ff063ffff 0xf68cf807fe0c7fff

def z537 : W := mkw 0x07ddbdb59b5b2006 0x80fbb7b6b36b6400 0x4b99bfc1cf9c0000 0x097337f839f38000

def z538 : W := mkw 0x0008142090000000 0x0001028412000000 0x00000621f0000001 0x400000c43e000000

def z539 : W := mkw 0x05f768000278e001 0x80beed00004f1c00 0xf5fff800007c6000 0x3ebfff00000f8c00

def z540 : W := mkw 0x0022400a20000000 0x0004480144000000 0xb466403e30601f07 0xf68cc807c60c03e0

def z541 : W := mkw 0x4000000a20000130 0x0800000144000026 0x00000006300000f9 0x00000000c600001f

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0xb466003e00639fe7 0xf68cc007c00c73fc

def z543 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8187c7cf8018e1 0xc97030f8f9f0031c

def z544 : W := mkw 0x4008077a24841f30 0x680100ef449083e6 0x020007fe30001ff9 0xc04000ffc60003ff

def z545 : W := mkw 0x0150024006d41e00 0x602a004800da83c0 0xfdf800000ffc1f06 0x1fbf000001ff83e0

def z546 : W := mkw 0x008582400d831806 0x4010b04801b06300 0x7b8787c00f839806 0xef70f0f801f07300

def z547 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x807ff83ff0000001 0x300fff07fe000000

def z548 : W := mkw 0x01f760000020c001 0x003eec0000041800 0xf5fff8000063e006 0x3ebfff00000c7c00

def z549 : W := mkw 0x437a753ab020c131 0x086f4ea756041826 0x8478783830606718 0x108f0f07060c0ce3

def z550 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xcdf9f8000ffc6000 0x19bf3f0001ff8c00

def z551 : W := mkw 0x800082404d8318c6 0x5000104809b06318 0x080000000f800000 0x0100000001f00000

def z552 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff002749b 0xfefffffffe004e93

def z553 : W := mkw 0x400000000020c131 0x0800000000041826 0x000000000003e0f8 0x0000000000007c1f

def z554 : W := mkw 0x402a477a24a4df31 0x680548ef44949be6 0xb66647fe3063ffff 0xf6ccc8ffc60c7fff

def z555 : W := mkw 0x8000800048020084 0x1000100009004010 0x00018001c0020081 0x2000300038004010

def z556 : W := mkw 0x0000000002540600 0x20000000004a80c0 0x04000000007c0700 0x00800000000f80e0

def z557 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x8466403e3063e7f9 0x308cc807c60c7cff

def z558 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x2b8601c60f8398e6 0x8570c038c1f0731c

def z559 : W := mkw 0x04a7e800092be007 0x8094fd0001257c00 0x7987f8000f83e006 0x2f30ff0001f07c00

def z560 : W := mkw 0xc00002cf648019f0 0x58000059ec90033e 0x020007fff0001ff9 0xc04000fffe0003ff

def z561 : W := mkw 0x05ffef700ffffe07 0xe0bffdee01ffffc0 0xffffffc00fffe006 0x3ffffff801fffc00

def z562 : W := mkw 0x037a777ab6d41e00 0x606f4eef56da83c0 0xfff87ff83ffc1f06 0xdfff0fff07ff83e0

def z563 : W := mkw 0x07fffdbfb92be007 0x80ffffb7f7257c00 0xf3fffffff003e001 0xfe7ffffffe007c00

def z564 : W := mkw 0x03fffdbfb80a2004 0x007fffb7f7014400 0xfffffffffc1e6003 0xffffffffff83cc00

def z565 : W := mkw 0x07fffd3abb7be007 0x80ffffa7576f7c00 0xfdfff8383fffe006 0x3fbfff0707fffc00

def z566 : W := mkw 0xa5fffee5dffffccf 0xf4bfffdcbbffff99 0xffffffe7fffffcff 0xfffffffcffffff9f

def z567 : W := mkw 0xa08d96e5dd871cce 0x7411b2dcbbb0e399 0x7b8787e7ff839cff 0xef70f0fcfff0739f

def z568 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x08078007cf8398e7 0x2100f000f9f0731c

def z569 : W := mkw 0x81d582c54fd318c6 0x503ab058a9fa6318 0xffff87c7cfff98e7 0xfffff0f8f9fff31c

def z570 : W := mkw 0x0022400000000000 0x0004480000000000 0xb066400000000000 0x360cc80000000000

def z571 : W := mkw 0x0172600000000000 0x002e4c0000000000 0x8078780000000000 0x100f0f0000000000

def z572 : W := mkw 0x0158053002500000 0x002b00a6004a0000 0xfff807f80ffc0006 0xdfff00ff01ff8000

def z573 : W := mkw 0x85f7ea004f7bf087 0xd0befd4009ef7e10 0xfdfffe01cffff087 0x7fbfffc039fffe10

def z574 : W := mkw 0x05f7e8c50bfbe847 0x80befd18a17f7d08 0xfffff9c60fffe866 0xbfffff38c1fffd0c

def z575 : W := mkw 0xa5fffe20df7ff48f 0xf4bfffc41beffe91 0xfdfffe01cfffe006 0x3fbfffc039fffc00

def z576 : W := mkw 0xa0008a004c0e348c 0x740011400981c691 0xdc19f8000c1e749a 0x3b833f000183ce93

def z577 : W := mkw 0xc3fff7fffda3d9f7 0x587ffeffffb47b3e 0xffffffffffe3ffff 0xfffffffffffc7fff

def z578 : W := mkw 0x05f7ea400ffffe07 0xe0befd4801ffffc0 0xfdfff8000fffff06 0x3fbfff0001ffffe0

def z579 : W := mkw 0xa0089e60dede3e8c 0x740113cc1bdbc7d1 0xdc19fe21fffe7f9f 0x7b833fc43fffcff3

def z580 : W := mkw 0x03dd37f596d41e00 0x607ba6feb2da83c0 0x4b99bfc1cf9c0000 0x097337f839f38000

def z581 : W := mkw 0x417a453a2274c731 0x282f48a7444e98e6 0x84784038307c6718 0x108f0807060f8ce3

def z582 : W := mkw 0x800886204c061484 0x700110c40980c290 0xdc198621cc1e1483 0x7b8330c43983c290

def z583 : W := mkw 0x03d5219500000000 0x007aa432a0000000 0x038001c000000000 0x0070003800000000

def z584 : W := mkw 0x0008066004841c00 0x600100cc00908380 0xff9807e00f9c1c06 0xdff300fc01f38380

def z585 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x300640063003f8ff 0xe600c800c6007f1f

def z586 : W := mkw 0xa3fffdbff80a208c 0x147fffb7ff014411 0xf3fffffff0026099 0xfe7ffffffe004c13

def z587 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x867807f8007c1f00 0xd0cf00ff000f83e0

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x738007c000000000 0xce7000f800000000

def z589 : W := mkw 0x0200108fb0000000 0x00400211f6000000 0x00000007f0000001 0x00000000fe000000

def z590 : W := mkw 0x002240000020c001 0x0004480000041800 0xb46640380063ff06 0xf68cc807000c7fe0

def z591 : W := mkw 0x01dd07f506d41e00 0x603ba0fea0da83c0 0xffff87ffcffc1f07 0xfffff0fff9ff83e0

def z592 : W := mkw 0x0158053002540600 0x202b00a6004a80c0 0xf7f807f8007c0700 0xdeff00ff000f80e0

def z593 : W := mkw 0x257a7c20927ce409 0xa4af4f84124f9c81 0x84787820307c6418 0x108f0f04060f8c83

def z594 : W := mkw 0x81dd87f54fd71ec6 0x703bb0fea9fae3d8 0xfff987f9cffc1f06 0xdfff30ff39ff83e0

def z595 : W := mkw 0x437a753ab020c131 0x086f4ea756041826 0xb47e783e3063ffff 0xf68fcf07c60c7fff

def z596 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x338601c6038398e7 0xe670c038c070731c

def z597 : W := mkw 0x80a7c2c54da3d8c7 0x5014f858a9b47b18 0xffe7c7c7cfe3f8e7 0xfffcf8f8f9fc7f1c

def z598 : W := mkw 0x037a753ab0000000 0x006f4ea756000000 0xb07e783e30000001 0xf60fcf07c6000000

def z599 : W := mkw 0x04008800092be007 0x8080110001257c00 0x000000000003e000 0x0000000000007c00

def z600 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x799fb8000f9f8006 0x2f33f70001f3f000

def z601 : W := mkw 0x00008800080a2004 0x0000110001014400 0x0001f80000026000 0x20003f0000004c00

def z602 : W := mkw 0x07fffdb59b7be007 0x80ffffb6b36f7c00 0xffffffc1cfffe006 0x3ffffff839fffc00

def z603 : W := mkw 0xc02242cf64a0d9f1 0x58044859ec941b3e 0xb66647fff063ffff 0xf6ccc8fffe0c7fff

def z604 : W := mkw 0xe02ade2afc2ef5bd 0x7c055bc55f85deb7 0xdc79fe39fc7e779b 0x7b8f3fc73f8fcef3

def z605 : W := mkw 0x0008162094041400 0x600102c412808280 0xdc19fe21fc1c1403 0x7b833fc43f838280

def z606 : W := mkw 0xc022c24a6da3d9f7 0x580458494db47b3e 0xbc66403e3fe3ffff 0xf78cc807c7fc7fff

def z607 : W := mkw 0x45f7600a2371c133 0x88beec01446e3826 0xb5e6403e33e3ffff 0xf6bcc807c67c7fff

def z608 : W := mkw 0xa08d9ee5dd8f3cce 0x7411b3dcbbb1e799 0x4b99bfc1cf9c0000 0x097337f839f38000

def z609 : W := mkw 0x0572e8000a7ae005 0x80ae5d00014f5c00 0xdc79f8000c7e6002 0x3b8f3f00018fcc00

def z610 : W := mkw 0x80858085490300c6 0x1010b010a9206018 0x30078007c00398e7 0xe600f000f800731c

def z611 : W := mkw 0xa0859885d90b20ce 0x1410b310bb216419 0x0007f807f003e0f9 0x2000ff00fe007c1f

def z612 : W := mkw 0xa7ffffbfff7ff48f 0xf4fffff7ffeffe91 0xfffffffffffff49f 0xfffffffffffffe93

def z613 : W := mkw 0x20081e20940c3408 0x640103c412818681 0xdc187e203c1c741a 0x5b830fc407838e83

def z614 : W := mkw 0xa3ff77bff4041488 0x747feef7fe808291 0xf3fffffff0001499 0xfe7ffffffe000293

def z615 : W := mkw 0x0000000000000000 0x0000000000000000 0x50018601c0000001 0x6a0030c038000000

def z616 : W := mkw 0x83f7e3df6d8318c6 0x507efc7bedb06318 0x7be787dfcf8398e7 0xef7cf0fbf9f0731c

def z617 : W := mkw 0xa1589f70dede3e8c 0x742b13ee1bdbc7d1 0xfff9bff9cffc1f06 0xdfff37ff39ff83e0

def z618 : W := mkw 0xa0089ee5dc8e3ccc 0x740113dcbb91c799 0xde19ffe7fc1e7cfb 0xfbc33ffcff83cf9f

def z619 : W := mkw 0x002240000020c001 0x0004480000041800 0xb46640203063f49f 0x768cc804060c7e93

def z620 : W := mkw 0xa3ffffbffc0e348c 0x747ffff7ff81c691 0xfbfffffffc1c0001 0xff7fffffff838000

def z621 : W := mkw 0x0000080000082000 0x0000010000010400 0x84187800001c6000 0x10830f0000038c00

def z622 : W := mkw 0x0000015000800a00 0x0000002a00100140 0x020001d800000b00 0x8040003b00000160

def z623 : W := mkw 0x41f7600a2020c131 0x083eec0144041826 0xf5fff83e3063ffff 0xfebfff07c60c7fff

def z624 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0xb7e001f803e01f06 0xd6fc003f007c03e0

def z625 : W := mkw 0x4022400a20000130 0x0804480144000026 0xb066403e30001ff9 0xf60cc807c60003ff

def z626 : W := mkw 0x0008062004041400 0x600100c400808280 0xdc1846203c1e749b 0x7b8308c40783ce93

def z627 : W := mkw 0x83ff77fff48018c0 0x507feefffe900318 0xf3fffffff00018e1 0xfe7ffffffe00031c

def z628 : W := mkw 0x05ffed300b7fe607 0xa0bffda6016ffcc0 0xfdfff8380fffe706 0x3fbfff0701fffce0

def z629 : W := mkw 0xa08d9e20dd0f348e 0x7411b3c41ba1e691 0xfd9ffe21ff9ff49f 0x7fb3ffc43ff3fe93

def z630 : W := mkw 0x81dd87f54fd71ec6 0x703bb0fea9fae3d8 0x4b9987c1cf9c0000 0x097330f839f38000

def z631 : W := mkw 0x0000024006d41e00 0x6000004800da83c0 0xbc6000380ffc1f06 0xd78c000701ff83e0

def z632 : W := mkw 0x80008a004c0a3084 0x5000114009814610 0xdc19fe01cc1e7083 0x7b833fc03983ce10

def z633 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb46640383063e71e 0x368cc807060c7ce3

def z634 : W := mkw 0x037a753ab0000000 0x006f4ea756000000 0xf3f87ff830000000 0xde7f0fff06000000

def z635 : W := mkw 0xa08d9ea5dc0e348c 0x7411b3d4bb81c691 0xff9fffe7fc1e749b 0xfff3fffcff83ce93

def z636 : W := mkw 0x000000000020c001 0x0000000000041800 0x040000000063e006 0x00800000000c7c00

def z637 : W := mkw 0x80858085490300c6 0x1010b010a9206018 0x738787c7c00380e1 0xee70f0f8f800701c

def z638 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x2066003e30619ffd 0xc40cc007c60c33ff

def z639 : W := mkw 0xa37aff3afc0e348c 0x746f5fe75f81c691 0xdc79fe39fc1e749b 0x7b8f3fc73f83ce93

def z640 : W := mkw 0x04a7e8000b7be007 0x8094fd00016f7c00 0x0c07f8000fffe006 0x2180ff0001fffc00

def z641 : W := mkw 0x03f7619f20000000 0x007eec33e4000000 0xb3e641fe30000001 0xf67cc83fc6000000

def z642 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb066403e30618b65 0xf60cc807c60c316c

def z643 : W := mkw 0x808502c5448018c0 0x5010a058a8900318 0x738787c7c00018e1 0xee70f0f8f800031c

def z644 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x2466001e0063fffe 0x848cc003c00c7fff

def z645 : W := mkw 0x01ff742090000000 0x003fee8412000000 0xf1fffe21f0000001 0x7e3fffc43e000000

def z646 : W := mkw 0x01dd05b500000000 0x003ba0b6a0000000 0xf3ff87ffc0000001 0xfe7ff0fff8000000

def z647 : W := mkw 0x83fff7bffc021084 0x507ffef7ff804210 0xfbfffffffc021083 0xff7fffffff804210

def z648 : W := mkw 0x0085800009030006 0x0010b00001206000 0x0007800000038000 0x2000f00000007000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0xb460403830627f9f 0xf68c0807060c4ff3

def z650 : W := mkw 0xc0a7c2cf6da3d9f7 0x5814f859edb47b3e 0x7be787dfcfe39be7 0xef7cf0fbf9fc737c

def z651 : W := mkw 0x43f7619f2020c131 0x087eec33e4041826 0xb7e641fe3063ffff 0xf6fcc83fc60c7fff

def z652 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xb466401e0063eb66 0xb68cc803c00c7d6c

def z653 : W := mkw 0x4172400a2270c131 0x082e4801444e1826 0xfdfe403e3fffffff 0xffbfc807c7ffffff

def z654 : W := mkw 0x0150000002500000 0x002a0000004a0000 0x21e0000003e00004 0x043c0000007c0000

def z655 : W := mkw 0x80858085490300c6 0x1010b010a9206018 0x00018001c0000000 0x0000300038000000

def z656 : W := mkw 0xc0a7c08f6923c1f7 0x1814f811ed24783e 0x0007c007f003e0f9 0x2000f800fe007c1f

def z657 : W := mkw 0x0000020004041400 0x6000004000808280 0x0c0000000c1c1402 0x0180000001838280

def z658 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x020787c7c00398e1 0xe040f0f8f800731c

def z659 : W := mkw 0x03f7619f20000000 0x007eec33e4000000 0xf3fff9de00000000 0xbe7fff3bc0000000

def z660 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff847f83ffe7f9f 0xffff08ff07ffcff3

def z661 : W := mkw 0x808580c5498308c6 0x1010b018a9306118 0x238781c7c38388e5 0xa470f038f870711c

def z662 : W := mkw 0x01f7600000000000 0x003eec0000000000 0x21e6000000000000 0x043cc00000000000

def z663 : W := mkw 0x0150000000000000 0x002a000000000000 0xf1f8000000000000 0x1e3f000000000000

def z664 : W := mkw 0xe02ade2afc2ef5bd 0x7c055bc55f85deb7 0xdc1ffe27fc1ff4fb 0x7b83ffc4ff83fe9f

def z665 : W := mkw 0x83ddb7f5dd8318c6 0x507bb6febbb06318 0x4b99bfc1cf800000 0x097337f839f00000

def z666 : W := mkw 0x815807f546d41ec0 0x702b00fea8da83d8 0xfff807ffcffc1fe7 0xdfff00fff9ff83fc

def z667 : W := mkw 0x400000000020c131 0x0800000000041826 0x940040203063ffff 0x72800804060c7fff

def z668 : W := mkw 0x20081c20900c2408 0x2401038412018481 0x00183800001c0000 0x0003070000038000

def z669 : W := mkw 0x0008042000040400 0x2001008400008080 0x84180020001c0400 0x1083000400038080

def z670 : W := mkw 0x815887704fd71ec6 0x702b10ee09fae3d8 0xfff807f80fff9fe6 0xdfff00ff01fff3fc

def z671 : W := mkw 0x40a740cf21a1c973 0x0814e819e434392e 0xb7e641fe33e3ffff 0xf6fcc83fc67c7fff

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc1800000c1c0002 0x1b83000001838000

def z673 : W := mkw 0xa08d9ee5dd8f3cce 0x7411b3dcbbb1e799 0xdf99ffe1ff9e749b 0x7bf33ffc3ff3ce93

def z674 : W := mkw 0x03f7719fb0000000 0x007eee33f6000000 0x23e7f9dff0000001 0xa47cff3bfe000000

def z675 : W := mkw 0x002240000020c001 0x0004480000041800 0x2066000000618004 0x040cc000000c3000

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x8400402030006418 0x1080080406000c83

def z677 : W := mkw 0x042268000028e001 0x80844d0000051c00 0x0000780000006000 0x00000f0000000c00

def z678 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x4f9807c00ffc1f06 0x09f300f801ff83e0

def z679 : W := mkw 0x01d580000b530006 0x003ab000016a6000 0xfdff80000fff8006 0x3fbff00001fff000

def z680 : W := mkw 0x035817ffb6d41e00 0x606b02fff6da83c0 0xfff807fffffc1f07 0xdfff00ffffff83e0

def z681 : W := mkw 0xa5f7ea004f7ff48f 0xf4befd4009effe91 0xfdfff8000ffff49e 0x3fbfff0001fffe93

def z682 : W := mkw 0x0022400a2020c001 0x0004480144041800 0xb466403e3063e007 0xf68cc807c60c7c00

def z683 : W := mkw 0x00a7c0000923c007 0x0014f80001247800 0xfde7c0000fe3e006 0x3fbcf80001fc7c00

def z684 : W := mkw 0x23ff7dbfb00c2408 0x247fefb7f6018481 0xf7fffffff01c6419 0xfefffffffe038c83

def z685 : W := mkw 0x037a753ab2540600 0x206f4ea7564a80c0 0x84787838307c0700 0x108f0f07060f80e0

def z686 : W := mkw 0x0008062004041400 0x600100c400808280 0x481806000c1c0000 0x090300c001838000

def z687 : W := mkw 0x40a7c00a2923c137 0x0814f80145247826 0xfde7c03e3fe3ffff 0xffbcf807c7fc7fff

def z688 : W := mkw 0x4000000a20000130 0x0800000144000026 0x9400403e30027ffb 0xf2800807c6004fff

def z689 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x946040383062779b 0x728c0807060c4ef3

def z690 : W := mkw 0xa1dd9ff5dfdf3ece 0x743bb3febbfbe7d9 0xffffffffffffffff 0xffffffffffffffff

def z691 : W := mkw 0x0158073004041400 0x602b00e600808280 0xfff807f80c1c1402 0xdfff00ff01838280

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000006000018e1 0xc0000000c000031c

def z693 : W := mkw 0x800082404d8318c6 0x5000104809b06318 0x7b8007c00f8398e6 0xcf7000f801f0731c

def z694 : W := mkw 0x808d96e5dd8318c6 0x5011b2dcbbb06318 0xfb9fffe7ff8398e7 0xff73fffcfff0731c

def z695 : W := mkw 0x42a7708fb020c131 0x0854ee11f6041826 0xb467f83ff063ffff 0xf68cff07fe0c7fff

def z696 : W := mkw 0x03ff77ffb4841e00 0x607feefff69083c0 0xf3fffffff0001f01 0xfe7ffffffe0003e0

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000000001806 0xc600000000000300

def z698 : W := mkw 0x4022424a24a0d931 0x4804484944941b26 0xffe647fe3fe3ffff 0xfffcc8ffc7fc7fff

def z699 : W := mkw 0x0000024004801800 0x4000004800900300 0x020007c000001800 0xc04000f800000300

def z700 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x8c1878203c1e749a 0x11830f040783ce93

def z701 : W := mkw 0x0158053002540600 0x202b00a6004a80c0 0xb4780038007c1f06 0xd68f0007000f83e0

def z702 : W := mkw 0x008502c504801800 0x4010a058a0900300 0x7b8787c7cf801807 0xef70f0f8f9f00300

def z703 : W := mkw 0x4158077006f4df31 0x682b00ee00de9be6 0xfff807f80ffffffe 0xdfff00ff01ffffff

def z704 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xdf9807e00f9c1402 0x5bf300fc01f38280

def z705 : W := mkw 0x800082404d8318c6 0x5000104809b06318 0x58018601cf8398e7 0x6b0030c039f0731c

def z706 : W := mkw 0x03ff753ab0000000 0x007feea756000000 0xf1fff83830000000 0x3e3fff0706000000

def z707 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8787c7cf8398e7 0x2970f0f8f9f0731c

def z708 : W := mkw 0xa0008a404c8e3e8c 0x740011480991c7d1 0x0c0000000c1e7f9a 0x018000000183cff3

def z709 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff063e0ff 0xfefffffffe0c7c1f

def z710 : W := mkw 0x06089dbfbb7be007 0x80c113b7f76f7c00 0x0e0007ffffffe007 0xc1c000fffffffc00

def z711 : W := mkw 0x837af77afd8318c6 0x506f5eef5fb06318 0x887878383f8398e6 0x110f0f0707f0731c

def z712 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x639fbfc7c0000000 0x8c73f7f8f8000000

def z713 : W := mkw 0xa0089e60dd8f3cce 0x740113cc1bb1e799 0xff99ffe1ff9ffcff 0xfff33ffc3ff3ff9f

def z714 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xfbffffffff800007 0xff7ffffffff00000

def z715 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x69f9b8000ffc0004 0x0d3f370001ff8000

def z716 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe21fc1e641a 0x3b833fc43f83cc83

def z717 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0x4399bff9f0000000 0x087337ff3e000000

def z718 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xddf9f8000ffe6002 0x3bbf3f0001ffcc00

def z719 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x8466403e3063ffff 0x308cc807c60c7fff

def z720 : W := mkw 0xa3f7eb9f6c0e348c 0x747efd73ed81c691 0x2fe601de0c1e749a 0x85fcc03bc183ce93

def z721 : W := mkw 0xa0081660d4841c88 0x740102cc1a908391 0x020007e1f0001c99 0xc04000fc3e000393

def z722 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xf47ff83e3063ffff 0xfe8fff07c60c7fff

def z723 : W := mkw 0x0158177096d41e00 0x602b02ee12da83c0 0xfff9fff9fffe7f9f 0xffff3fff3fffcff3

def z724 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8003fffe01e 0x3fbfff0007fffc03

def z725 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xcdf9f8383ffc6718 0x19bf3f0707ff8ce3

def z726 : W := mkw 0xa00816e5d4841cc8 0x740102dcba908399 0x020007e1f0001499 0x404000fc3e000293

def z727 : W := mkw 0x47f7e99f2b7be137 0x88fefd33e56f7c26 0xfffff9de0fffeb66 0xbfffff3bc1fffd6c

def z728 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe01fc1e609b 0x3b833fc03f83cc13

def z729 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0001807 0xfe7ffffffe000300

def z730 : W := mkw 0x417a477a26f4df31 0x682f48ef44de9be6 0x4b9e47c63f9fe0f9 0x2973c8f8c7f3fc1f

def z731 : W := mkw 0xa0009a00dc0a308c 0x540013401b814611 0xdc19fe01fc1e709b 0x7b833fc03f83ce13

def z732 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x739fbfc1c0000000 0x2e73f7f838000000

def z733 : W := mkw 0xa0089f70dc8e3e8c 0x740113ee1b91c7d1 0xff99fff9ff9e7f9f 0xfff33fff3ff3cff3

def z734 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xedfff8000ffde004 0x1dbfff0001ffbc00

def z735 : W := mkw 0x8158077046d41ec0 0x702b00ee08da83d8 0xfff807f80ffc1fe6 0xdfff00ff01ff83fc

def z736 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe21fc1ffcff 0x7b833fc43f83ff9f

def z737 : W := mkw 0x020817f594841e00 0x604102feb29083c0 0x020007f9c0001f00 0xc04000ff380003e0

def z738 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787e7ff839cff 0xef70f0fcfff0739f

def z739 : W := mkw 0x022a55bfb0000000 0x00454ab7f6000000 0xf27ffffff0000001 0xfe4ffffffe000000

def z740 : W := mkw 0xa5ff7620d775d48b 0xf4bfeec41aeeba91 0x21e60621f3e1949d 0x443cc0c43e7c3293

def z741 : W := mkw 0xa1dd9ff5dfdf3ece 0x743bb3febbfbe7d9 0x4b99bfc1cf9c0000 0x097337f839f38000

def z742 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf3fffffff0000719 0xfe7ffffffe0000e3

def z743 : W := mkw 0x85d5a8854b5b20c6 0x90bab510a96b6418 0x4999b801cf9c0000 0x0933370039f38000

def z744 : W := mkw 0xa0089c20d80e248c 0x340113841b01c491 0x8419f821f01c6418 0x10833f043e038c83

def z745 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xd999f8000f9c0000 0x3b333f0001f38000

def z746 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000ffff087 0x7fbfff0001fffe10

def z747 : W := mkw 0x45d5a80a2b5b2136 0x88bab501456b6426 0x4999b83e3f9c1ff9 0xc9333707c7f383ff

def z748 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0x63ffbfdfc0618b64 0x8c7ff7fbf80c316c

def z749 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0xfff801f80ffc1f06 0xdfff003f01ff83e0

def z750 : W := mkw 0x07ff75bfb371c003 0x80ffeeb7f66e3800 0xf7fffffff3e3e007 0xfefffffffe7c7c00

def z751 : W := mkw 0x00089c20980a2004 0x0001138413014400 0xdc19fe21fc1e749b 0x7b833fc43f83ce93

def z752 : W := mkw 0x05f7e8850b7be007 0x80befd10a16f7c00 0xffffffc7cffff8e7 0xfffffff8f9ffff1c

def z753 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xfde6403e3fe3ffff 0xffbcc807c7fc7fff

def z754 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff003f4fb 0xfefffffffe007e9f

def z755 : W := mkw 0x05f7e8850b7be007 0x80befd10a16f7c00 0xfdfff807cfffe007 0x3fbfff00f9fffc00

def z756 : W := mkw 0xe02ade2afc2ef5bd 0x7c055bc55f85deb7 0x687fbe1fcc7d8b64 0x8d0ff7c3f98fb16c

def z757 : W := mkw 0x808502c5458118c2 0x5010a058a8b02318 0x338607c7c38398e7 0xe670c0f8f870731c

def z758 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0x4999b8000ffd8004 0x0933370001ffb000

def z759 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0026099 0xfe7ffffffe004c13

def z760 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xfbe787ffcf8398e7 0xff7cf0fff9f0731c

def z761 : W := mkw 0x808502c5458118c2 0x5010a058a8b02318 0x238607c7c3818864 0x8470c0f8f870310c

def z762 : W := mkw 0xc422ca4a6ffbf9f7 0xd88459494dff7f3e 0xbc66403e3fffffff 0xf78cc807c7ffffff

def z763 : W := mkw 0x03dd35b592500000 0x007ba6b6b24a0000 0x4b99bfc1cf9c0000 0x097337f839f38000

def z764 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x739fffc7f0000001 0xee73fff8fe000000

def z765 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0xc9f9f8000f9c0000 0x193f3f0001f38000

def z766 : W := mkw 0x45f760cf23f1c973 0x88beec19e47e392e 0x23e601de03e18b64 0x847cc03bc07c316c

def z767 : W := mkw 0x0008142090000000 0x0001028412000000 0xf399ffe1f0000001 0xfe733ffc3e000000

def z768 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f80ffe7f9e 0xdfff00ff01ffcff3

def z769 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff81e0ffffbe7 0xffbfff03c1ffff7c

def z770 : W := mkw 0x0085008500000000 0x0010a010a0000000 0xf39fffc7c0000001 0xfe73fff8f8000000

def z771 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc19fe21fc1e7c9f 0xff833fc43f83cf93

def z772 : W := mkw 0x80858ac54d8b38c6 0x5010b158a9b16718 0xff9fffe7ff9ffcff 0xfff3fffcfff3ff9f

def z773 : W := mkw 0x84008a404fdb38c6 0xd080114809fb6718 0x080000000f9f98e6 0x0100000001f3f31c

def z774 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfd99fe21ff9e749f 0x7fb33fc43ff3ce93

def z775 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff83e0fffffe7 0xffbfff07c1fffffc

def z776 : W := mkw 0x40a7c80a292be137 0x0814f90145257c26 0xfdfff83e3fffffff 0xffbfff07c7ffffff

def z777 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8060fffe0e7 0x3fbfff00c1fffc1c

def z778 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x7bf807d80ffc1b06 0xcf7f00fb01ff8360

def z779 : W := mkw 0xa1509950dada2a8c 0x142a132a1b5b4551 0x23e1f9d9f3e26b9d 0xa47c3f3b3e7c4d73

def z780 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8063fffffff 0x3fbfff00c7ffffff

def z781 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xfdffb8000fff8006 0x3fbff70001fff000

def z782 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4819fe01fc1c6018 0x09033fc03f838c03

def z783 : W := mkw 0x0008177094841e00 0x600102ee129083c0 0x020007f9f0001f01 0xc04000ff3e0003e0

def z784 : W := mkw 0x40af54afb020c131 0x0815ea95f6041826 0xf7fffffff063ffff 0xfefffffffe0c7fff

def z785 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0x499ff8000f9c0000 0x2933ff0001f38000

def z786 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xa466403e3063fffe 0x948cc807c60c7fff

def z787 : W := mkw 0x01f7e800090b2006 0x003efd0001216400 0xfdfff8000f9fe006 0x3fbfff0001f3fc00

def z788 : W := mkw 0x04a7e8000b7be007 0x8094fd00016f7c00 0xdc1ff8000fffe006 0x3b83ff0001fffc00

def z789 : W := mkw 0x47f7619f2371c133 0x88feec33e46e3826 0x23e601de03e18b64 0x847cc03bc07c316c

def z790 : W := mkw 0x05f768000278e001 0x80beed00004f1c00 0xfdfff8000ffc6006 0x3fbfff0001ff8c00

def z791 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x2fe007f80ffc1f06 0xc5fc00ff01ff83e0

def z792 : W := mkw 0x42af75bfb020c131 0x0855eeb7f6041826 0xb667fffff063ffff 0xf6ccfffffe0c7fff

def z793 : W := mkw 0xa0008a404ede3e8c 0x7400114809dbc7d1 0x080000000f9c0000 0x0100000001f38000

def z794 : W := mkw 0x8485aac54d8b38c6 0xd090b558a9b16718 0x7b87bfc7cf8398e7 0xef70f7f8f9f0731c

def z795 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8060fffe007 0xffbfff00c1fffc00

def z796 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7f8787c7cfe39fe7 0xeff0f0f8f9fc73fc

def z797 : W := mkw 0x808502c5458118c2 0x5010a058a8b02318 0x738787c7c38198e5 0xee70f0f8f870331c

def z798 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xc3f9bff9c0000000 0x187f37ff38000000

def z799 : W := mkw 0x0150035006d41e00 0x602a006a00da83c0 0xbfe001f80ffc1f06 0xd7fc003f01ff83e0

def z800 : W := mkw 0x8158077046d41e80 0x702b00ee08da83d0 0xfff807f9cffc1f87 0xdfff00ff39ff83f0

def z801 : W := mkw 0x20081c20900c2408 0x2401038412018481 0x8419f821f01c6419 0x30833f043e038c83

def z802 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xffe787c7cfe398e7 0xfffcf0f8f9fc731c

def z803 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0x2fe001d80ffc0b06 0x85fc003b01ff8160

def z804 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfffe07fe0ffc1f07 0xffffc0ffc1ff83e0

def z805 : W := mkw 0xa0089f70dc8e3e8c 0x740113ee1b91c7d1 0xde19ffe1fc1e749b 0x7bc33ffc3f83ce93

def z806 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff00018e1 0xfe7ffffffe00031c

def z807 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x238787c7c38398e5 0xe470f0f8f870731c

def z808 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8383fffff1e 0xffbfff0707ffffe3

def z809 : W := mkw 0x07dd35b593510002 0x80fba6b6b26a2000 0x4399bfc1c3800000 0x087337f838700000

def z810 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4c19fe01fc1e749b 0x29833fc03f83ce93

def z811 : W := mkw 0x0158057002d40e00 0x202b00ae005a81c0 0xfff801f80ffc0f06 0x9fff003f01ff81e0

def z812 : W := mkw 0x0422c8000b7be007 0x80845900016f7c00 0xfc7ff8000fffe006 0x3f8fff0001fffc00

def z813 : W := mkw 0x015088000a5a2004 0x002a1100014b4400 0xfdf9b8000ffc0006 0x1fbf370001ff8000

def z814 : W := mkw 0x47f7e99f2b7be137 0x88fefd33e56f7c26 0xfffff9fe3fffffff 0xffffff3fc7ffffff

def z815 : W := mkw 0xa0089e60dc8e3c8c 0x740113cc1b91c791 0xfff9fff9fffe7f9f 0xffff3fff3fffcff3

def z816 : W := mkw 0x01f7600a22500000 0x003eec01444a0000 0xfdfff83e3ffc1f07 0xffbfff07c7ff83e0

def z817 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xcff807f80ffc1f00 0xd9ff00ff01ff83e0

def z818 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff0607ff9 0xfefffffffe0c0fff

def z819 : W := mkw 0x05f768000379e003 0x80beed00006f3c00 0xfdfe78000ffde006 0x1fbfcf0001ffbc00

def z820 : W := mkw 0x04afef700daffe07 0xe095fdee01b5ffc0 0x0207fff80003ff00 0xe040ffff00007fe0

def z821 : W := mkw 0x05f7e8850b7be007 0x80befd10a16f7c00 0xffffffc1cfffe006 0x3ffffff839fffc00

def z822 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7f8787c7cf83fcff 0xeff0f0f8f9f07f9f

def z823 : W := mkw 0xa0089e60dc8e3e8c 0x740113cc1b91c7d1 0xdc19fe21fc1e7f9b 0x7b833fc43f83cff3

def z824 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x499fb8000f9f8000 0x2933f70001f3f000

def z825 : W := mkw 0x47ff75bfb371c133 0x88ffeeb7f66e3826 0xf3fffffff3e18b65 0xfe7ffffffe7c316c

def z826 : W := mkw 0x040088000b5b2006 0x80801100016b6400 0xdc19f8000f9e6002 0x3b833f0001f3cc00

def z827 : W := mkw 0x020817ffb4841e00 0x604102fff69083c0 0x020007fff0000001 0xc04000fffe000000

def z828 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0627f9f 0xfefffffffe0c4ff3

def z829 : W := mkw 0xa0089e60dd8f3cce 0x740113cc1bb1e799 0xfc1ffe27ff9ffcff 0xff83ffc4fff3ff9f

def z830 : W := mkw 0xa0089e20dd0f34ce 0x740113c41ba1e699 0xdc19fe21fc1ff4fb 0x7b833fc43f83fe9f

def z831 : W := mkw 0xa0858ac54d8f3cce 0x7410b158a9b1e799 0xff87c7e7ff9ffcff 0xfff0f8fcfff3ff9f

def z832 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0xf3ffffe1f0000001 0x7e7ffffc3e000000

def z833 : W := mkw 0x02a7708fb0000000 0x0054ee11f6000000 0x0207ffc7f0000001 0xe040fff8fe000000

def z834 : W := mkw 0x01f7608500000000 0x003eec10a0000000 0xf3ffffc1c0000000 0x3e7ffff838000000

def z835 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0xdc19f821fc1e749b 0x7b833f043f83ce93

def z836 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xfdf9f8000ffe6006 0x3fbf3f0001ffcc00

def z837 : W := mkw 0xa00816e5d4841cc8 0x740102dcba908399 0x020007c7c00018e1 0xc04000f8f800031c

def z838 : W := mkw 0xe0008a404efeffbd 0x7c00114809dfdff7 0x0c0000000ffffffe 0x0180000001ffffff

def z839 : W := mkw 0x0000024006d41e00 0x6000004800da83c0 0xffe007f80ffc1f06 0xdffc00ff01ff83e0

def z840 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xf39fffe7f0000001 0xfe73fffcfe000000

def z841 : W := mkw 0x84008a404dabf8c7 0xd080114809b57f18 0x080000000f83f8e6 0x0100000001f07f1c

def z842 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xc3f9fffff0000001 0xd87f3ffffe000000

def z843 : W := mkw 0xa0858ac54d8b38ce 0x5410b158a9b16719 0x7b8787c7cf83f8ff 0xef70f0f8f9f07f1f

def z844 : W := mkw 0xa0089c20d80e248c 0x340113841b01c491 0xd419fe21f01e6499 0x7a833fc43e03cc93

def z845 : W := mkw 0x07ff75bfb371c003 0x80ffeeb7f66e3800 0xfffffffffffd8007 0xffffffffffffb000

def z846 : W := mkw 0x0150035006d41e00 0x602a006a00da83c0 0x2be001d80ffc0b04 0x857c003b01ff8160

def z847 : W := mkw 0x02a772cfb6d41e00 0x6054ee59f6da83c0 0x0c07f807fffc1f07 0x2180ff00ffff83e0

def z848 : W := mkw 0x01d5208500000000 0x003aa410a0000000 0x739fbfc7c0000001 0xee73f7f8f8000000

def z849 : W := mkw 0x85726ac546f8f8c1 0xd0ae4d58a8df1f18 0x86787fc7c07c78e1 0xd0cf0ff8f80f8f1c

def z850 : W := mkw 0xa0089f30dc0e368c 0x740113e61b81c6d1 0xdc19fe39fc1e779b 0x7b833fc73f83cef3

def z851 : W := mkw 0x23ff75bfb0040408 0x247feeb7f6008081 0xf3fffffff0000419 0xfe7ffffffe000083

def z852 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff83e3fffff07 0xffbfff07c7ffffe0

def z853 : W := mkw 0xa0089f70dc8e3e8c 0x740113ee1b91c7d1 0xfe79fff9fc7e7f9f 0xffcf3fff3f8fcff3

def z854 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff8063fffe007 0x3fbfff00c7fffc00

def z855 : W := mkw 0x008d14a590000000 0x0011a294b2000000 0xf79fffe7f003fcff 0xfef3fffcfe007f9f

def z856 : W := mkw 0x00858800090b2006 0x0010b10001216400 0xfd9ff8263f9ffcff 0xffb3ff04c7f3ff9f

def z857 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0xf3ffffc7c0000001 0xfe7ffff8f8000000

def z858 : W := mkw 0xc0a7c2cf6da3d9f7 0x5814f859edb47b3e 0xcfe1c7f9ffe06718 0x19fc38ff3ffc0ce3

def z859 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff061ef7d 0xfefffffffe0c3def

def z860 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xeff807f80ffc0f04 0x9dff00ff01ff81e0

def z861 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xd3f9fff9f0000001 0x7a7f3fff3e000000

def z862 : W := mkw 0x04a7e800092be007 0x8094fd0001257c00 0xfd9ff8000f9fe006 0x3fb3ff0001f3fc00

def z863 : W := mkw 0x2158177096d41e08 0x642b02ee12da83c1 0xfff807f83ffc1f1e 0xdfff00ff07ff83e3

def z864 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0xd399fffff0000001 0xfa733ffffe000000

def z865 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787ffcf839fe7 0xef70f0fff9f073fc

def z866 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8200ffff406 0x7fbfff0401fffe80

def z867 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8383ffffffe 0x3fbfff0707ffffff

def z868 : W := mkw 0xc4a7e88f692be1f7 0x9894fd11ed257c3e 0x0007f807f003e0f9 0x2000ff00fe007c1f

def z869 : W := mkw 0x00af54afb0000000 0x0015ea95f6000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z870 : W := mkw 0x03f7708fb0000000 0x007eee11f6000000 0xf3ffffc7f0000001 0xfe7ffff8fe000000

def z871 : W := mkw 0x80008a004c0a3084 0x5000114009814610 0xdc19fe21fc1e749b 0x7b833fc43f83ce93

def z872 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x738787c7c38398e7 0xee70f0f8f870731c

def z873 : W := mkw 0x020815bfb0000000 0x004102b7f6000000 0x4219bffff0000001 0xc84337fffe000000

def z874 : W := mkw 0x80858ac54d8b38c6 0x5010b158a9b16718 0x7b9fbfc7cf9f98e7 0xef73f7f8f9f3f31c

def z875 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff003fcff 0xfefffffffe007f9f

def z876 : W := mkw 0x022a57ffb4841e00 0x60454afff69083c0 0xb66647fff0601f07 0xf6ccc8fffe0c03e0

def z877 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x799ff8000f9fe006 0x2f33ff0001f3fc00

def z878 : W := mkw 0xa0089e20dd0f348e 0x740113c41ba1e691 0xdc19fe21ff9ff49f 0x7b833fc43ff3fe93

def z879 : W := mkw 0x422a57ffb4a4df31 0x68454afff6949be6 0xb66647fff063ffff 0xf6ccc8fffe0c7fff

def z880 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x4999f8000f9e6000 0x29333f0001f3cc00

def z881 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807fe0ffc1fe7 0xdfff00ffc1ff83fc

def z882 : W := mkw 0x440088000b7be137 0x88801100016f7c26 0xdc19f8203fffffff 0x7b833f0407ffffff

def z883 : W := mkw 0x015088000a5a2004 0x002a1100014b4400 0x4999b8000f9c0000 0x0933370001f38000

def z884 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xfb87c7e7ff8398e7 0xff70f8fcfff0731c

def z885 : W := mkw 0xa0089e60dc8e3c8c 0x740113cc1b91c791 0xff9fffe7ff9ffcff 0xfff3fffcfff3ff9f

def z886 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x4399bfc7c0000001 0xc87337f8f8000000

def z887 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xdff807f80ffc1702 0x5bff00ff01ff82e0

def z888 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0xdd99f8000fffe006 0x3bb33f0001fffc00

def z889 : W := mkw 0x8422ca404ffbf8c7 0xd084594809ff7f18 0xbc6640060ffff8e7 0xf78cc800c1ffff1c

def z890 : W := mkw 0x208d1ce5918d2c4a 0x2411a39cb231a589 0xa79e79e6339dec7c 0x94f3cf3cc673bd8f

def z891 : W := mkw 0xe008177af4841fb8 0x7c0102ef5e9083f7 0x020007fff0001ff9 0xc04000fffe0003ff

def z892 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x4d99b8000f9e6002 0x09b3370001f3cc00

def z893 : W := mkw 0xa0089c20d80a208c 0x140113841b014411 0xdc19fe21fc1e609b 0x7b833fc43f83cc13

def z894 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf8380e1 0xef70f0f8f9f0701c

def z895 : W := mkw 0x0008153090000000 0x000102a612000000 0xd219fff9f0000001 0xfa433fff3e000000

def z896 : W := mkw 0xa00817f5d4841ec8 0x740102feba9083d9 0x020007fff0001ff9 0xc04000fffe0003ff

def z897 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x63f9bfd9c0000000 0x8c7f37fb38000000

def z898 : W := mkw 0x43dd35b59020c131 0x087ba6b6b2041826 0x4799bfc1c063fffe 0x08f337f8380c7fff

def z899 : W := mkw 0xc4008a404ffbf9f7 0xd880114809ff7f3e 0x0c0000000ffffffe 0x0180000001ffffff

def z900 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xcc19fe21fc1e749a 0x19833fc43f83ce93

def z901 : W := mkw 0x07f7e99f2b5b2006 0x80fefd33e56b6400 0x6bffb9de0f9c0000 0x8d7ff73bc1f38000

def z902 : W := mkw 0x0008162094041400 0x600102c412808280 0xdc19fe21fc1e749b 0x7b833fc43f83ce93

def z903 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0001403 0xfefffffffe000280

def z904 : W := mkw 0x07f7e9950b7be007 0x80fefd32a16f7c00 0xfffff9c00fffe006 0x3fffff3801fffc00

def z905 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf3fffffff00000f9 0xfe7ffffffe00001f

def z906 : W := mkw 0xa0089e60dc8e3c8c 0x740113cc1b91c791 0xde19ffe1fc1e7c9b 0xfbc33ffc3f83cf93

def z907 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0xf3fffff9c0000000 0xfe7fffff38000000

def z908 : W := mkw 0xa0089e60dc8e3c8c 0x740113cc1b91c791 0xdf99ffe1ff9e749b 0x7bf33ffc3ff3ce93

def z909 : W := mkw 0x055088000b7be007 0x80aa1100016f7c00 0xfdf9f8000fffe006 0x3fbf3f0001fffc00

def z910 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0001f01 0xfe7ffffffe0003e0

def z911 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0x439fffc1c0000000 0x2873fff838000000

def z912 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xcdf9f8000fffe006 0x19bf3f0001fffc00

def z913 : W := mkw 0x01d5200002500000 0x003aa400004a0000 0xfdf9b8000ffc0006 0x1fbf370001ff8000

def z914 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xcc19fe21fc1e6499 0x39833fc43f83cc93

def z915 : W := mkw 0xc5f7e88f6b7be1f7 0x98befd11ed6f7c3e 0xfdfff807ffffe0ff 0x3fbfff00fffffc1f

def z916 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e0fffff66 0xffbfff07c1ffffec

def z917 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfffe07fe0ffd9f66 0xdfffc0ffc1ffb3ec

def z918 : W := mkw 0x03ff75bfb2500000 0x007feeb7f64a0000 0xf3fffffff3e00005 0xfe7ffffffe7c0000

def z919 : W := mkw 0xe02a577af4a4dfb9 0x7c054aef5e949bf7 0xb66647fff063ffff 0xf6ccc8fffe0c7fff

def z920 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff0600301 0xfe7ffffffe0c0060

def z921 : W := mkw 0x20089c20980e240c 0x240113841301c481 0xdc19fe21fc1e641b 0x7b833fc43f83cc83

def z922 : W := mkw 0x000088000a5a2004 0x00001100014b4400 0xdc19f8000ffe6006 0x3b833f0001ffcc00

def z923 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff81e0ffffffe 0xbfbfff03c1ffffff

def z924 : W := mkw 0x01dd15b590000000 0x003ba2b6b2000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z925 : W := mkw 0x00a7608500000000 0x0014ec10a0000000 0x7387ffc7c0000001 0xee70fff8f8000000

def z926 : W := mkw 0x01d588000b5b2006 0x003ab100016b6400 0xfdfff8000fffe006 0x3fbfff0001fffc00

def z927 : W := mkw 0x4422c80a2b7be137 0x88845901456f7c26 0xfc7ff83e3fffffff 0xff8fff07c7ffffff

def z928 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f80ffc0706 0x1fff00ff01ff80e0

def z929 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff00380e1 0xfe7ffffffe00701c

def z930 : W := mkw 0x20081c20900c2408 0x2401038412018481 0xc419fe21f01c6418 0x18833fc43e038c83

def z931 : W := mkw 0xe022ca4a6daffdff 0x7c0459494db5ffbf 0xbc66403e3fffffff 0xf78cc807c7ffffff

def z932 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x4d9ff8000fffe006 0x29b3ff0001fffc00

def z933 : W := mkw 0xa0081770d4841e88 0x740102ee1a9083d1 0x020007f9c0001f00 0xc04000ff380003e0

def z934 : W := mkw 0xa0089f30dc0e348c 0x740113e61b81c691 0xde19fff9fc1e749b 0xfbc33fff3f83ce93

def z935 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x2066403e3063fffd 0xe40cc807c60c7fff

def z936 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x4399bff9c0000000 0xc87337ff38000000

def z937 : W := mkw 0x015088000a5a2004 0x002a1100014b4400 0xfdf9f8383ffe7f9f 0xffbf3f0707ffcff3

def z938 : W := mkw 0x057268000278e001 0x80ae4d00004f1c00 0xfdfe78000fffe006 0x3fbfcf0001fffc00

def z939 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8060fffe066 0x3fbfff00c1fffc0c

def z940 : W := mkw 0xa0858ac54d8f3cce 0x7410b158a9b1e799 0x7b8787c7cf9f98e7 0xef70f0f8f9f3f31c

def z941 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xdd99f8203f9e749b 0x7bb33f0407f3ce93

def z942 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8180fffeb06 0xbfbfff0301fffd60

def z943 : W := mkw 0x0158177096d41e00 0x602b02ee12da83c0 0xfff9bff9cffc1f06 0xdfff37ff39ff83e0

def z944 : W := mkw 0xa0089c20d80e248c 0x340113841b01c491 0xdc19f821fc1e649b 0x3b833f043f83cc93

def z945 : W := mkw 0x03ff75bfb2540600 0x207feeb7f64a80c0 0xf3fffffff01c0001 0xfe7ffffffe038000

def z946 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc79fe39fc7e779b 0x7b8f3fc73f8fcef3

def z947 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x8419fe21f01e7499 0x70833fc43e03ce93

def z948 : W := mkw 0x0158057002d00a00 0x002b00ae005a0140 0xfff807f80ffc0b06 0xdfff00ff01ff8160

def z949 : W := mkw 0x01ff74a590000000 0x003fee94b2000000 0xf3ffffe7f0000001 0xfe7ffffcfe000000

def z950 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x8c7ff8000fffe006 0x318fff0001fffc00

def z951 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf7fffffff063f49f 0xfefffffffe0c7e93

def z952 : W := mkw 0x42a7708fb020c131 0x0854ee11f6041826 0xf7e7fffff063ffff 0xfefcfffffe0c7fff

def z953 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8787c7cf818060 0x0970f0f8f9f0300c

def z954 : W := mkw 0x43f761df22f0cb31 0x087eec3be45e1966 0x23e601de03e18b64 0x847cc03bc07c316c

def z955 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf7fffffff0027ffb 0xfefffffffe004fff

def z956 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0038007 0xfe7ffffffe007000

def z957 : W := mkw 0x0158153090000000 0x002b02a612000000 0xf3f9bff9c0000000 0xde7f37ff38000000

def z958 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0x4819f801fc1e6099 0x29033f003f83cc13

def z959 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xd799ffe1f002749b 0x7af33ffc3e004e93

def z960 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf8380e7 0x2f70f0f8f9f0701c

def z961 : W := mkw 0x040088000b7be007 0x80801100016f7c00 0x8c1878000fffe006 0x11830f0001fffc00

def z962 : W := mkw 0x0550a8000b5b2006 0x80aa1500016b6400 0x081838000f9c0000 0x0103070001f38000

def z963 : W := mkw 0xa20817fff4841e88 0x744102fffe9083d1 0x020007fff0001f99 0xc04000fffe0003f3

def z964 : W := mkw 0x028d35b590000000 0x0051a6b6b2000000 0x0201bfc1c0000000 0x004037f838000000

def z965 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x6b8787c7cf8388e5 0xad70f0f8f9f0711c

def z966 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x4399bfe1f0000001 0x487337fc3e000000

def z967 : W := mkw 0xa0089c20d80e248c 0x340113841b01c491 0x9419f821f01e749b 0x72833f043e03ce93

def z968 : W := mkw 0x01d5208500000000 0x003aa410a0000000 0x4399bfc1c0000000 0x087337f838000000

def z969 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xff87c7c7cf83f8e7 0xfff0f8f8f9f07f1c

def z970 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xc7f9fff9f0606718 0x18ff3fff3e0c0ce3

def z971 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xffffffc00fffe006 0xfffffff801fffc00

def z972 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x6ff807d80ffc1f06 0x8dff00fb01ff83e0

def z973 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xcc19fe21fc1c7499 0x59833fc43f838e93

def z974 : W := mkw 0x0150035006d41e00 0x602a006a00da83c0 0xfff801d80ffc1f06 0x9fff003b01ff83e0

def z975 : W := mkw 0x03dd35b592540600 0x207ba6b6b24a80c0 0xc7f9bff9c07c0700 0x18ff37ff380f80e0

def z976 : W := mkw 0x01f760000270c001 0x003eec00004e1800 0xfdfff8000fffe006 0x3fbfff0001fffc00

def z977 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0x4d99b8000ffc6000 0x09b3370001ff8c00

def z978 : W := mkw 0xa0089e60dc8e3c8c 0x740113cc1b91c791 0xdc19fe21ff9e7c9f 0x7b833fc43ff3cf93

def z979 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff003f8ff 0xfe7ffffffe007f1f

def z980 : W := mkw 0x008502c504801800 0x4010a058a0900300 0x7b8787c7cf8398e7 0xef70f0f8f9f0731c

def z981 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8063ffff8ff 0xffbfff00c7ffff1f

def z982 : W := mkw 0x0358377096d41e00 0x606b06ee12da83c0 0xfff83ff80ffc1f06 0xdfff07ff01ff83e0

def z983 : W := mkw 0x03ff75bfb2540600 0x207feeb7f64a80c0 0xfffffffffffc0707 0xffffffffffff80e0

def z984 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff0607f1f 0xfefffffffe0c0fe3

def z985 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xf3f9bfc1c0000000 0x1e7f37f838000000

def z986 : W := mkw 0x0158053002500000 0x002b00a6004a0000 0xfff807f80ffc1f06 0xdfff00ff01ff83e0

def z987 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e3fffe71f 0xffbfff07c7fffce3

def z988 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc1ffe27fc1ff4fb 0x7b83ffc4ff83fe9f

def z989 : W := mkw 0x03ff75bfb1010042 0x007feeb7f6202008 0xf3fffffff0018061 0xfe7ffffffe00300c

def z990 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x5819fe01fc1e709b 0x6b033fc03f83ce13

def z991 : W := mkw 0x03ff75bfb2540600 0x207feeb7f64a80c0 0xf7fffffff07c1f07 0xfefffffffe0f83e0

def z992 : W := mkw 0x437a753ab274c731 0x286f4ea7564e98e6 0x84787838307c6718 0x108f0f07060f8ce3

def z993 : W := mkw 0xa0081660d4841cc8 0x740102cc1a908399 0x00000621f0001cf9 0x400000c43e00039f

def z994 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x5399bfc1c0000001 0x6a7337f838000000

def z995 : W := mkw 0x47ff75bfb371c133 0x88ffeeb7f66e3826 0xf7fffffff3e3ffff 0xfefffffffe7c7fff

def z996 : W := mkw 0xa0081770d4841e88 0x740102ee1a9083d1 0x020007c1c0000000 0x004000f838000000

def z997 : W := mkw 0x05d5a8850b5b2006 0x80bab510a16b6400 0x7b9fbfc7cf9c0001 0xef73f7f8f9f38000

def z998 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e3fffeb67 0xffbfff07c7fffd6c

def z999 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xf9fff8000f9fe000 0x3f3fff0001f3fc00

def z1000 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc7ffe3ffc7fffff 0xff8fffc7ff8fffff

def z1001 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff81e3fffebff 0xbfbfff03c7fffd7f

def z1002 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8263ffff4ff 0x7fbfff04c7fffe9f

def z1003 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0006419 0xfefffffffe000c83

def z1004 : W := mkw 0x00858800090b2006 0x0010b10001216400 0x799fb8000f9f8006 0x2f33f70001f3f000

def z1005 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0026003 0xfefffffffe004c00

def z1006 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xf7f9bff9c0601f06 0xdeff37ff380c03e0

def z1007 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x6b8787c7cf8398e6 0x8d70f0f8f9f0731c

def z1008 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x638787c7c3818864 0x8c70f0f8f870310c

def z1009 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x8c19f821fc1e749b 0x31833f043f83ce93

def z1010 : W := mkw 0x028d15bfb0000000 0x0051a2b7f6000000 0xf39ffffff0000001 0xfe73fffffe000000

def z1011 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x7999b8000f9c0006 0x0f33370001f38000

def z1012 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xd399bfe1c0000000 0x5a7337fc38000000

def z1013 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff0619f67 0xfefffffffe0c33ec

def z1014 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8383fffff9f 0xffbfff0707fffff3

def z1015 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8003fffe09f 0x3fbfff0007fffc13

def z1016 : W := mkw 0x84008a404fdb38c6 0xd080114809fb6718 0x080000000f9c0000 0x0100000001f38000

def z1017 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf819866 0xcf70f0f8f9f0330c

def z1018 : W := mkw 0xa0089e60dc8e3ccc 0x740113cc1b91c799 0xdc19fe21fc1e7cfb 0x7b833fc43f83cf9f

def z1019 : W := mkw 0x05f7e8850b7be007 0x80befd10a16f7c00 0xfffff9c60fffe006 0xbfffff38c1fffc00

def z1020 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x79ffb8000fff8006 0x2f3ff70001fff000

def z1021 : W := mkw 0x84008a404ffffec7 0xf080114809ffffd8 0x0c0000000fffffe6 0x0180000001fffffc

def z1022 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f80ffc0700 0xdfff00ff01ff80e0

def z1023 : W := mkw 0xa0008a404ede3e8c 0x7400114809dbc7d1 0xbc6040383ffe7f9f 0xf78c080707ffcff3

def z1024 : W := mkw 0x02af74afb0000000 0x0055ee95f6000000 0xf39fffe7f0000001 0xfe73fffcfe000000

def z1025 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xadfe78000fffe006 0x15bfcf0001fffc00

def z1026 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xcd99f8000f9c6000 0x19b33f0001f38c00

def z1027 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e3fffe7ff 0x3fbfff07c7fffcff

def z1028 : W := mkw 0x0158153090000000 0x002b02a612000000 0x4399bfc1c0000000 0x087337f838000000

def z1029 : W := mkw 0x477a7d3ab278e131 0x88ef4fa7564f1c26 0x84787838307c6718 0x108f0f07060f8ce3

def z1030 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfffe47fe3fffffff 0xffffc8ffc7ffffff

def z1031 : W := mkw 0x420817ffb4841f30 0x684102fff69083e6 0x020007fff0001ff9 0xc04000fffe0003ff

def z1032 : W := mkw 0x01f7e8000a5a2004 0x003efd00014b4400 0xfdfff8000ffe6006 0x3fbfff0001ffcc00

def z1033 : W := mkw 0x42a7708fb020c131 0x0854ee11f6041826 0x7387ffc7f003f8ff 0xee70fff8fe007f1f

def z1034 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xff8787e7cf839ce7 0xfff0f0fcf9f0739c

def z1035 : W := mkw 0xe00816eff4841df8 0x7c0102ddfe9083bf 0x020007fff0001ff9 0xc04000fffe0003ff

def z1036 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0600007 0xfefffffffe0c0000

def z1037 : W := mkw 0x03f7719fb0000000 0x007eee33f6000000 0x73e7ffdff0000001 0xee7cfffbfe000000

def z1038 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x63ffbffff0000001 0xcc7ff7fffe000000

def z1039 : W := mkw 0x45f7e88f2b7be137 0x88befd11e56f7c26 0xffffffffffffffff 0xffffffffffffffff

def z1040 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff063e7f9 0xfefffffffe0c7cff

def z1041 : W := mkw 0xa0008a404d8b38ce 0x5400114809b16719 0x080000000f83f8fe 0x0100000001f07f1f

def z1042 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xf7e647fe3063ffff 0xfefcc8ffc60c7fff

def z1043 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xcdfff8000fffe000 0x39bfff0001fffc00

def z1044 : W := mkw 0x05f7e88f2b7be007 0x80befd11e56f7c00 0xffffffffffffe007 0xfffffffffffffc00

def z1045 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x2466003e3063ffff 0xc48cc007c60c7fff

def z1046 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff0619ffd 0xfe7ffffffe0c33ff

def z1047 : W := mkw 0x46a7f88fb92be137 0x88d4ff11f7257c26 0x0007f807f003e0f9 0x2000ff00fe007c1f

def z1048 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0600b05 0xfe7ffffffe0c0160

def z1049 : W := mkw 0xe0008a404daffdff 0x7c00114809b5ffbf 0x0c0000000ffffffe 0x0180000001ffffff

def z1050 : W := mkw 0xa20817fff4841cc8 0x744102fffe908399 0x020007fff0001cf9 0xc04000fffe00039f

def z1051 : W := mkw 0x808582c54d871cc6 0x7010b058a9b0e398 0x7f8787c7cf9f9ce7 0xeff0f0f8f9f3f39c

def z1052 : W := mkw 0xa0089c20d80e248c 0x340113841b01c491 0x0019f801f01e6099 0x20033f003e03cc13

def z1053 : W := mkw 0x4572680a2278e131 0x88ae4d01444f1c26 0xfdf878383ffc7f1e 0xdfbf0f0707ff8fe3

def z1054 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3f9fff9f0000000 0xde7f3fff3e000000

def z1055 : W := mkw 0xa0089e60dd8f3cce 0x740113cc1bb1e799 0xdc19fe21ff9e749b 0x7b833fc43ff3ce93

def z1056 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf818865 0xef70f0f8f9f0310c

def z1057 : W := mkw 0x0572e8000b7be007 0x80ae5d00016f7c00 0x8c7878000ffc6000 0x118f0f0001ff8c00

def z1058 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x4d99b8000ffc0006 0x09b3370001ff8000

def z1059 : W := mkw 0x01f7600002500000 0x003eec00004a0000 0xf9fff8000f9c0000 0x3f3fff0001f38000

def z1060 : W := mkw 0xa0008a404c8e3c8c 0x740011480991c791 0x0c0000000f9e7c9e 0x0180000001f3cf93

def z1061 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x4399ffc1f0000000 0x08733ff83e000000

def z1062 : W := mkw 0x0550280002582000 0x80aa0500004b0400 0xfdf838000ffc0006 0x1fbf070001ff8000

def z1063 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8000fffe71e 0x3fbfff0001fffce3

def z1064 : W := mkw 0x43ff75bfb270c131 0x087feeb7f64e1826 0xffffffffffffffff 0xffffffffffffffff

def z1065 : W := mkw 0xe02a56eff4a4ddf9 0x7c054addfe949bbf 0xb66647fff063ffff 0xf6ccc8fffe0c7fff

def z1066 : W := mkw 0xa0008a404d8f3cce 0x7400114809b1e799 0xbc0640263f9ffcff 0xf780c804c7f3ff9f

def z1067 : W := mkw 0x43dd35bfb0000130 0x087ba6b7f6000026 0x4399bffff0001ff9 0xc87337fffe0003ff

def z1068 : W := mkw 0x0550a8000b7be007 0x80aa1500016f7c00 0x0c1838000fffe006 0x0183070001fffc00

def z1069 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0639fe7 0xfefffffffe0c73fc

def z1070 : W := mkw 0x03ff75bfb2500000 0x007feeb7f64a0000 0xfbffffffff9c0001 0xff7ffffffff38000

def z1071 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x6bf807f80ffc1f04 0xcd7f00ff01ff83e0

def z1072 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xd819fe21fc1e6099 0x7b033fc43f83cc13

def z1073 : W := mkw 0x0150035006d01a00 0x402a006a00da0340 0xfff807d80ffc1b06 0xdfff00fb01ff8360

def z1074 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8000fffeb66 0x3fbfff0001fffd6c

def z1075 : W := mkw 0x0085808509030006 0x0010b010a1206000 0x7b8787c7cf8398e7 0xef70f0f8f9f0731c

def z1076 : W := mkw 0x00008800090b2006 0x0000110001216400 0xdc19f8000f9fe006 0x3b833f0001f3fc00

def z1077 : W := mkw 0x03f7619f20000000 0x007eec33e4000000 0xf3ffffdfc0000001 0xfe7ffffbf8000000

def z1078 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x73ffbfdfc0000001 0xee7ff7fbf8000000

def z1079 : W := mkw 0x008580c509830846 0x0010b018a1306108 0x7b8787c7cf838867 0xef70f0f8f9f0710c

def z1080 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf7fffffff063f8e7 0xfefffffffe0c7f1c

def z1081 : W := mkw 0x0572e8000b7be007 0x80ae5d00016f7c00 0xbc7e78000fffe006 0x378fcf0001fffc00

def z1082 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0018865 0xfe7ffffffe00310c

def z1083 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xfc7e403e3c7fffff 0xff8fc807c78fffff

def z1084 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe39fc1e7f9b 0xfb833fc73f83cff3

def z1085 : W := mkw 0x0285308590000000 0x0050a610b2000000 0x4381bfc1c0000000 0x087037f838000000

def z1086 : W := mkw 0x040088000b5b2006 0x80801100016b6400 0x4819b8000f9c0000 0x0903370001f38000

def z1087 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xf3f9fff9f0000001 0xfe7f3fff3e000000

def z1088 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdffb8000ffd8006 0x1fbff70001ffb000

def z1089 : W := mkw 0x43ff75bfb274c731 0x287feeb7f64e98e6 0xf7fffffff07fffff 0xfefffffffe0fffff

def z1090 : W := mkw 0x0158177096d41e00 0x602b02ee12da83c0 0xfff807f9fffc1f07 0xdfff00ff3fff83e0

def z1091 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0xf9fff8000f9f8006 0x3f3fff0001f3f000

def z1092 : W := mkw 0x41f7600a2270c131 0x083eec01444e1826 0xfdfff83e3fffffff 0xffbfff07c7ffffff

def z1093 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x7399bfc1c0000000 0xce7337f838000000

def z1094 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x4399ffc1f0000001 0x28733ff83e000000

def z1095 : W := mkw 0x05d5a8850b5b2006 0x80bab510a16b6400 0x4b99bfc1cf9c0000 0x097337f839f38000

def z1096 : W := mkw 0x80008a404d8b38c6 0x5000114809b16718 0x0c0000000f9ff8e6 0x0180000001f3ff1c

def z1097 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000ffff8e6 0x3fbfff0001ffff1c

def z1098 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xc3fffffff0000001 0x387ffffffe000000

def z1099 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3ffbfffc0000000 0xde7ff7fff8000000

def z1100 : W := mkw 0x07f7e88f2b7be007 0x80fefd11e56f7c00 0xfdfff8060fffe006 0x3fbfff00c1fffc00

def z1101 : W := mkw 0x85f7e8854b7be0c7 0x90befd10a96f7c18 0xfdfff801cfffe006 0x3fbfff0039fffc00

def z1102 : W := mkw 0xa0081770d4841e88 0x740102ee1a9083d1 0x020007e1f0001499 0x404000fc3e000293

def z1103 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc1ffe27fc1e749b 0xff83ffc4ff83ce93

def z1104 : W := mkw 0x07f7e99f2b7be007 0x80fefd33e56f7c00 0xfffff9fe3fffe007 0xffffff3fc7fffc00

def z1105 : W := mkw 0x07f7e99f2b7be007 0x80fefd33e56f7c00 0xffffffdfcfffe007 0xfffffffbf9fffc00

def z1106 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf3fffffff003e001 0xfe7ffffffe007c00

def z1107 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0x499ff8063f9fe0f9 0x2933ff00c7f3fc1f

def z1108 : W := mkw 0x417a553ab020c131 0x082f4aa756041826 0xf7fffffff063ffff 0xfefffffffe0c7fff

def z1109 : W := mkw 0x0150024006d01800 0x402a004800da0300 0xfff807f80ffc1f06 0xdfff00ff01ff83e0

def z1110 : W := mkw 0x05f760000371c003 0x80beec00006e3800 0xfdfff8000ffd8006 0x3fbfff0001ffb000

def z1111 : W := mkw 0xa0008a404d8f3cce 0x7400114809b1e799 0x0c0000000f9e749a 0x0180000001f3ce93

def z1112 : W := mkw 0x01f7e0000b530006 0x003efc00016a6000 0xfdfff8000fff8006 0x3fbfff0001fff000

def z1113 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x2b8607c7cf8398e7 0xc570c0f8f9f0731c

def z1114 : W := mkw 0x4572e80a2b7be137 0x88ae5d01456f7c26 0x8c7878383ffffffe 0x118f0f0707ffffff

def z1115 : W := mkw 0x015088000a5a2004 0x002a1100014b4400 0xdd99f8000f9e6002 0x3bb33f0001f3cc00

def z1116 : W := mkw 0x81dd85b54b5706c6 0x303bb0b6a96ae0d8 0x847f803fc07f87e1 0x308ff007f80ff0fc

def z1117 : W := mkw 0x20081c20900c2408 0x2401038412018481 0xd419fe21f01e749b 0x7a833fc43e03ce93

def z1118 : W := mkw 0xa1581770d6d41e88 0x742b02ee1ada83d1 0xfff807f9cffc1f06 0xdfff00ff39ff83e0

def z1119 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e3fffef7e 0xbfbfff07c7fffdef

def z1120 : W := mkw 0x020817f594841e00 0x604102feb29083c0 0x020007c1c0000000 0x004000f838000000

def z1121 : W := mkw 0x422a55bfb020c131 0x08454ab7f6041826 0xf67ffffff063ffff 0xfecffffffe0c7fff

def z1122 : W := mkw 0x020815bfb0000000 0x004102b7f6000000 0x0201fffff0000001 0xe0403ffffe000000

def z1123 : W := mkw 0x0150080002582000 0x002a0100004b0400 0xfdf878000ffc6006 0x1fbf0f0001ff8c00

def z1124 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdf9f8000ffc6006 0x1fbf3f0001ff8c00

def z1125 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0xc3f9ffc1c0000000 0x187f3ff838000000

def z1126 : W := mkw 0x00008800080a2004 0x0000110001014400 0xfd99f8000f9e6006 0x3fb33f0001f3cc00

def z1127 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xf3ffbfffc0000001 0xfe7ff7fff8000000

def z1128 : W := mkw 0x0085108590000000 0x0010a210b2000000 0x7387ffc7f0000001 0xee70fff8fe000000

def z1129 : W := mkw 0x0150000002500000 0x002a0000004a0000 0xfdf9f8000ffc0006 0x3fbf3f0001ff8000

def z1130 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xf9f9b8000f9c0000 0x1f3f370001f38000

def z1131 : W := mkw 0xa00816e5d4841cc8 0x740102dcba908399 0xb60647e7f003fcff 0xf6c0c8fcfe007f9f

def z1132 : W := mkw 0x20081e20940c3408 0x640103c412818681 0xdc19fe21fc1c741b 0x7b833fc43f838e83

def z1133 : W := mkw 0x800002c5448018c0 0x50000058a8900318 0x7b8607c7cf8398e7 0xef70c0f8f9f0731c

def z1134 : W := mkw 0x80858085490300c6 0x1010b010a9206018 0x7b8787c7cf8380e7 0xef70f0f8f9f0701c

def z1135 : W := mkw 0x01ff65b500000000 0x003fecb6a0000000 0xf3ffffffc0000001 0xfe7ffffff8000000

def z1136 : W := mkw 0x0158153090000000 0x002b02a612000000 0xd399ffe1f0000001 0x7a733ffc3e000000

def z1137 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8060fffe866 0xbfbfff00c1fffd0c

def z1138 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf3fffffff0618005 0xfe7ffffffe0c3000

def z1139 : W := mkw 0x0208177ab4841e00 0x604102ef569083c0 0x020007f830001f00 0xc04000ff060003e0

def z1140 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8380fffe006 0xffbfff0701fffc00

def z1141 : W := mkw 0xa1581770d6d41e88 0x742b02ee1ada83d1 0xfff847f9fffe7f9f 0xffff08ff3fffcff3

def z1142 : W := mkw 0x048588000b7be007 0x8090b100016f7c00 0xfd9ff8000fffe006 0x3fb3ff0001fffc00

def z1143 : W := mkw 0x02af75bfb0000000 0x0055eeb7f6000000 0xd21ffffff0000001 0xfa43fffffe000000

def z1144 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0x739fbffff0000001 0xee73f7fffe000000

def z1145 : W := mkw 0x820817fff4841ec0 0x704102fffe9083d8 0x020007fff0001fe1 0xc04000fffe0003fc

def z1146 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x799fb8000f9c0000 0x2f33f70001f38000

def z1147 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf3fffffff0039fff 0xfe7ffffffe0073ff

def z1148 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xd399ffc1c0000000 0x3a733ff838000000

def z1149 : W := mkw 0x01ff753090000000 0x003feea612000000 0xf3fffff9f0000001 0xfe7fffff3e000000

def z1150 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xffe7c7ffffe3ffff 0xfffcf8fffffc7fff

def z1151 : W := mkw 0x020815b590000000 0x004102b6b2000000 0x4219bfc1c0000000 0x084337f838000000

def z1152 : W := mkw 0x07d5a9950b5b2006 0x80fab532a16b6400 0x4b99b9c00f9c0000 0x0973373801f38000

def z1153 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff062779b 0xfefffffffe0c4ef3

def z1154 : W := mkw 0x035815bfb0000000 0x006b02b7f6000000 0xf3f9fffff0000001 0xfe7f3ffffe000000

def z1155 : W := mkw 0x01d5200002500000 0x003aa400004a0000 0x4999b8000f9c0000 0x0933370001f38000

def z1156 : W := mkw 0x008d14a590000000 0x0011a294b2000000 0x4399bfc1c0000000 0x087337f838000000

def z1157 : W := mkw 0x00858800090b2006 0x0010b10001216400 0x4999b8000f9c0000 0x0933370001f38000

def z1158 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf7fffffff063ff07 0xfefffffffe0c7fe0

def z1159 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xf9fff8000ffd8004 0x3f3fff0001ffb000

def z1160 : W := mkw 0x0150015002d00a00 0x002a002a005a0140 0x6bf801d80ffc0b04 0x8d7f003b01ff8160

def z1161 : W := mkw 0x85d5a8854b5b20c6 0x90bab510a96b6418 0x499fb807cf9f80e1 0x2933f700f9f3f01c

def z1162 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff987f9cffc1f07 0xffff30ff39ff83e0

def z1163 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0x69ffb8000f9c0000 0x0d3ff70001f38000

def z1164 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff0006019 0xfe7ffffffe000c03

def z1165 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xaff801f80ffc1f06 0x95ff003f01ff83e0

def z1166 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xcdf9b8000ffc0000 0x19bf370001ff8000

def z1167 : W := mkw 0x07ff75bfb3510002 0x80ffeeb7f66a2000 0xf3fffffff3800001 0xfe7ffffffe700000

def z1168 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807d80ffc0b06 0x9fff00fb01ff8160

def z1169 : W := mkw 0x85f7e8854b7be0c7 0x90befd10a96f7c18 0xffffffc7cfffe0e7 0xfffffff8f9fffc1c

def z1170 : W := mkw 0x0550280002582000 0x80aa0500004b0400 0x499838000f9c0000 0x0933070001f38000

def z1171 : W := mkw 0x05f7e9100b7be007 0x80befd22016f7c00 0xfffff9d80fffe006 0xbfffff3b01fffc00

def z1172 : W := mkw 0xa0081660d4841e88 0x740102cc1a9083d1 0x00000621f0001f99 0x400000c43e0003f3

def z1173 : W := mkw 0x80858ac54d8b38c6 0x5010b158a9b16718 0x7f8787c7cf9ff8e7 0xeff0f0f8f9f3ff1c

def z1174 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff063e71f 0xfefffffffe0c7ce3

def z1175 : W := mkw 0x057268000278e001 0x80ae4d00004f1c00 0x8c7878000ffc6006 0x118f0f0001ff8c00

def z1176 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x439fbfc7c0000000 0x0873f7f8f8000000

def z1177 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf7fffffff0600701 0xfefffffffe0c00e0

def z1178 : W := mkw 0x617a5d3ab27ce739 0x2c2f4ba7564f9ce7 0x84787838307c6718 0x108f0f07060f8ce3

def z1179 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff8383fffe006 0x3fbfff0707fffc00

def z1180 : W := mkw 0x03ff75b59020c001 0x007feeb6b2041800 0xf7ffffc1c063e006 0x3efffff8380c7c00

def z1181 : W := mkw 0x808502c5458118c2 0x5010a058a8b02318 0x7b8607c7cf8198e7 0xcf70c0f8f9f0331c

def z1182 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xfffffffffc1c0003 0xffffffffff838000

def z1183 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000ffff806 0xffbfff0001ffff00

def z1184 : W := mkw 0x4022400a2020c131 0x0804480144041826 0xf467c63ff063ffff 0xfe8cf8c7fe0c7fff

def z1185 : W := mkw 0x040088000b7be007 0x80801100016f7c00 0x4c19b8000fffe006 0x0983370001fffc00

def z1186 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0xc399ffe1f0000000 0x18733ffc3e000000

def z1187 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc79fe39fc1e749b 0xff8f3fc73f83ce93

def z1188 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff0018061 0xfe7ffffffe00300c

def z1189 : W := mkw 0x03dd35b592500000 0x007ba6b6b24a0000 0xfff9bfc1cffc0006 0x1fff37f839ff8000

def z1190 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf7fffffff063eb67 0xfefffffffe0c7d6c

def z1191 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff83e3fffe0ff 0xffbfff07c7fffc1f

def z1192 : W := mkw 0xa08582c54d871cce 0x7410b058a9b0e399 0x7b8787c7cf839cff 0xef70f0f8f9f0739f

def z1193 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8203fffe41e 0x3fbfff0407fffc83

def z1194 : W := mkw 0x03ff75bfb020c001 0x007feeb7f6041800 0xf7fffffff0606001 0xfefffffffe0c0c00

def z1195 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x499fb8000f9d8000 0x0933f70001f3b000

def z1196 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc1ffe21fc1ff49f 0x7f83ffc43f83fe93

def z1197 : W := mkw 0x4022400a2020c131 0x0804480144041826 0x8466403e3063fff9 0xf08cc807c60c7fff

def z1198 : W := mkw 0x03ff75bfb2500000 0x007feeb7f64a0000 0xfffffffffffc1f07 0xffffffffffff83e0

def z1199 : W := mkw 0xa0008a404fdf3ece 0x7400114809fbe7d9 0x0c0000000ffffffe 0x0180000001ffffff

def z1200 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff847f83ffc1f07 0xffff08ff07ff83e0

def z1201 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xff9f87c7cf9f98e7 0xfff3f0f8f9f3f31c

def z1202 : W := mkw 0x07ff75b59371c003 0x80ffeeb6b26e3800 0x63ffbfc1c3e18004 0x0c7ff7f8387c3000

def z1203 : W := mkw 0x05f7e9100b7be207 0x80befd22016f7c40 0xfdfff8180fffe306 0x3fbfff0301fffc60

def z1204 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x439fbfc7c0000001 0x2873f7f8f8000000

def z1205 : W := mkw 0xa5f7e8004b7be08f 0x94befd00096f7c11 0xfdfff8000fffe09e 0x3fbfff0001fffc13

def z1206 : W := mkw 0x017a553ab0000000 0x002f4aa756000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z1207 : W := mkw 0xa1581770d6d41e88 0x742b02ee1ada83d1 0xfff9fff9fffc1f9f 0xffff3fff3fff83f3

def z1208 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x799fb8060f9f98e7 0xef33f700c1f3f31c

def z1209 : W := mkw 0xa4008a404ffffe8f 0xf480114809ffffd1 0x0c0000000fffff9e 0x0180000001fffff3

def z1210 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0x4819fe21fc1e7499 0x69033fc43f83ce93

def z1211 : W := mkw 0x02af75bfb0000000 0x0055eeb7f6000000 0xb267fffff0000001 0xf64cfffffe000000

def z1212 : W := mkw 0x03dd35b590000000 0x007ba6b6b2000000 0x739fbfc7c00398e7 0xee73f7f8f800731c

def z1213 : W := mkw 0x01f7608f20000000 0x003eec11e4000000 0xf3fffffff0000001 0xfe7ffffffe000000

def z1214 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7be787dfcfe39be7 0xef7cf0fbf9fc737c

def z1215 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff063ebfd 0xfe7ffffffe0c7d7f

def z1216 : W := mkw 0x02af75bfb0000000 0x0055eeb7f6000000 0x0207ffc7f0000001 0x2040fff8fe000000

def z1217 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8180fffe306 0x3fbfff0301fffc60

def z1218 : W := mkw 0x4172c80a2a7ae135 0x082e5901454f5c26 0xfdfff83e3fffffff 0xffbfff07c7ffffff

def z1219 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0x69ffb81e0ffd8b64 0x8d3ff703c1ffb16c

def z1220 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3ffffdfc0000000 0xbe7ffffbf8000000

def z1221 : W := mkw 0x0572e8000b7be007 0x80ae5d00016f7c00 0xdc79f8000fffe006 0x3b8f3f0001fffc00

def z1222 : W := mkw 0xc5f7e88f6b7be1f7 0x98befd11ed6f7c3e 0xfdfff83fffffffff 0xffbfff07ffffffff

def z1223 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8203fffffff 0x7fbfff0407ffffff

def z1224 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x827ffffff0000001 0xf04ffffffe000000

def z1225 : W := mkw 0x05f7e8850b7be047 0x80befd10a16f7c08 0xfdfff8060fffe066 0x3fbfff00c1fffc0c

def z1226 : W := mkw 0x41f7608f2020c131 0x083eec11e4041826 0xf7fffffff063ffff 0xfefffffffe0c7fff

def z1227 : W := mkw 0x800082404c821884 0x5000104809904310 0x7b8787c7cf8398e7 0xef70f0f8f9f0731c

def z1228 : W := mkw 0x420815bfb0000130 0x084102b7f6000026 0xd619fffff0027ffb 0xfac33ffffe004fff

def z1229 : W := mkw 0xa0008a404c8e3ccc 0x740011480991c799 0x0c0000000c1e7cfa 0x018000000183cf9f

def z1230 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0xfdf9b8000fffe006 0x1fbf370001fffc00

def z1231 : W := mkw 0x07ff75bfb121c003 0x80ffeeb7f6243800 0xf3fffffff0018001 0xfe7ffffffe003000

def z1232 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x4999f8000f9c6000 0x09333f0001f38c00

def z1233 : W := mkw 0x008502c505811842 0x4010a058a0b02308 0x7b8787c7cf819867 0xef70f0f8f9f0330c

def z1234 : W := mkw 0x0158177096d41e00 0x602b02ee12da83c0 0xfff87ff83ffc1f06 0xdfff0fff07ff83e0

def z1235 : W := mkw 0xa0008a404d8f3cce 0x7400114809b1e799 0x080000000f9f98e6 0x0100000001f3f31c

def z1236 : W := mkw 0x07f7e91a2b7be007 0x80fefd23456f7c00 0xfdfff8180fffe006 0x3fbfff0301fffc00

def z1237 : W := mkw 0x000814a590000000 0x00010294b2000000 0xd219ffe7f0000001 0xfa433ffcfe000000

def z1238 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x63ffffdff0000001 0xac7ffffbfe000000

def z1239 : W := mkw 0xa0008a404ede3e8c 0x7400114809dbc7d1 0x0c0000000f9e749a 0x0180000001f3ce93

def z1240 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0x7d9fb8000fffe006 0x2fb3f70001fffc00

def z1241 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000ffc6000 0x3fbfff0001ff8c00

def z1242 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000ffff49e 0x3fbfff0001fffe93

def z1243 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3ffffc7f0000001 0x3e7ffff8fe000000

def z1244 : W := mkw 0xa0858ac54d8f3cce 0x7410b158a9b1e799 0xff9fffc7cf9ffcff 0xfff3fff8f9f3ff9f

def z1245 : W := mkw 0x03ff75bfb1010002 0x007feeb7f6202000 0xf3fffffff3818005 0xfe7ffffffe703000

def z1246 : W := mkw 0x0150035006d41e00 0x602a006a00da83c0 0x7fe007d80ffc1f06 0xcffc00fb01ff83e0

def z1247 : W := mkw 0xa0081e20d40c3488 0x740103c41a818691 0xd419fe21f01c7499 0x7a833fc43e038e93

def z1248 : W := mkw 0x4572e80a2b7be137 0x88ae5d01456f7c26 0xbc7e783e3fffffff 0xf78fcf07c7ffffff

def z1249 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff003fff9 0xfe7ffffffe007fff

def z1250 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0xfdfff8000f9e6002 0x3fbfff0001f3cc00

def z1251 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x69fff8000fffe004 0x2d3fff0001fffc00

def z1252 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff847f83ffc7f1e 0xdfff08ff07ff8fe3

def z1253 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe21fc7e7f9f 0x7b833fc43f8fcff3

def z1254 : W := mkw 0x02af75bfb0000000 0x0055eeb7f6000000 0x7387fffff0000001 0xee70fffffe000000

def z1255 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8000fffe0fe 0x3fbfff0001fffc1f

def z1256 : W := mkw 0x80858ac54d8b38c6 0x5010b158a9b16718 0x7b87ffc7cf83f8e7 0xef70fff8f9f07f1c

def z1257 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0xf3f9bffff0000001 0xde7f37fffe000000

def z1258 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x6dffb8000fffe006 0x0dbff70001fffc00

def z1259 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8060fffffff 0xffbfff00c1ffffff

def z1260 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xe3fffffff0000000 0x9c7ffffffe000000

def z1261 : W := mkw 0x42af75bfb020c131 0x0855eeb7f6041826 0x0207fffff003fff9 0xe040fffffe007fff

def z1262 : W := mkw 0x01f760850020c001 0x003eec10a0041800 0xf7ffffc7c063f8e7 0xfefffff8f80c7f1c

def z1263 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfbf807f80ffc0b04 0xdf7f00ff01ff8160

def z1264 : W := mkw 0x037a75bfb0000000 0x006f4eb7f6000000 0xd279fffff0000001 0xfa4f3ffffe000000

def z1265 : W := mkw 0x84008a404ffbf8c7 0xd080114809ff7f18 0x0c0000000fffe006 0x0180000001fffc00

def z1266 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x439ffffff0000001 0xe873fffffe000000

def z1267 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff81e0fffe006 0xbfbfff03c1fffc00

def z1268 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x5999b8000f9e0002 0x2b33370001f3c000

def z1269 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xd39fffe7f0000001 0x7a73fffcfe000000

def z1270 : W := mkw 0x057268000278e001 0x80ae4d00004f1c00 0xcdf878000ffc6000 0x19bf0f0001ff8c00

def z1271 : W := mkw 0xa0081770d4841e88 0x740102ee1a9083d1 0xb66047f9f0627f9f 0xf6cc08ff3e0c4ff3

def z1272 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff847f80ffe7f06 0xffff08ff01ffcfe0

def z1273 : W := mkw 0x85f7e8854b7be0c7 0x90befd10a96f7c18 0xfdfff807cffff8e7 0xffbfff00f9ffff1c

def z1274 : W := mkw 0xe022ca4a6efeffbd 0x7c0459494ddfdff7 0xbc66403e3fffffff 0xf78cc807c7ffffff

def z1275 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffff9f0000000 0x3e7fffff3e000000

def z1276 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff83e3ffff8e7 0xffbfff07c7ffff1c

def z1277 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xcff807f80ffc1f06 0x19ff00ff01ff83e0

def z1278 : W := mkw 0x0572e8000a7ae005 0x80ae5d00014f5c00 0xfdf9f8000ffe6006 0x3fbf3f0001ffcc00

def z1279 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0xfb9fffc7cf8398e7 0xff73fff8f9f0731c

def z1280 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xdd9ff8000f9fe002 0x3bb3ff0001f3fc00

def z1281 : W := mkw 0xa00816e5d4841cc8 0x740102dcba908399 0x020007c1c0000000 0x004000f838000000

def z1282 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f80ffe1f87 0xffff00ff01ffc3f0

def z1283 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x699fb8000f9d8004 0x0d33f70001f3b000

def z1284 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0x439fffc7f003e0f9 0x2873fff8fe007c1f

def z1285 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x6b8787c7cf8198e5 0xcd70f0f8f9f0331c

def z1286 : W := mkw 0x4572680a2278e131 0x88ae4d01444f1c26 0xfdfe783e3fffffff 0xffbfcf07c7ffffff

def z1287 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8263ffffcff 0xffbfff04c7ffff9f

def z1288 : W := mkw 0x03dd35b592540600 0x207ba6b6b24a80c0 0x4399bfc1c01c0000 0x087337f838038000

def z1289 : W := mkw 0xa0008a404ede3e8c 0x7400114809dbc7d1 0x0c0000000ffc1f06 0x0180000001ff83e0

def z1290 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8000fffff06 0x3fbfff0001ffffe0

def z1291 : W := mkw 0x05f7e80a2b5b2006 0x80befd01456b6400 0xf9fff83e3f9c0001 0xff3fff07c7f38000

def z1292 : W := mkw 0xa4008a404ffffccf 0xf480114809ffff99 0x0c0000000ffffcfe 0x0180000001ffff9f

def z1293 : W := mkw 0x0172c8000a7ae005 0x002e5900014f5c00 0xfdfff8000fffe006 0x3fbfff0001fffc00

def z1294 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe27fc1e7cfb 0xfb833fc4ff83cf9f

def z1295 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b8787c7cf838866 0xaf70f0f8f9f0710c

def z1296 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xfd9ff8000f9fe006 0x3fb3ff0001f3fc00

def z1297 : W := mkw 0x85f7e8004b7be0c7 0x90befd00096f7c18 0xfdfff8000fffe0e6 0x3fbfff0001fffc1c

def z1298 : W := mkw 0xa0008a404d8f3cce 0x7400114809b1e799 0x080000000f9c0000 0x0100000001f38000

def z1299 : W := mkw 0x03ff75bfb270c001 0x007feeb7f64e1800 0xffffffffffffe007 0xfffffffffffffc00

def z1300 : W := mkw 0x0572e8000b7be007 0x80ae5d00016f7c00 0xfdf878000fffe006 0x1fbf0f0001fffc00

def z1301 : W := mkw 0x03ff75bfb2500200 0x007feeb7f64a0040 0xf3fffffff0600301 0xfe7ffffffe0c0060

def z1302 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0x4bf807d80ffc0300 0x097f00fb01ff8060

def z1303 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff9fff80ffc1f06 0xffff3fff01ff83e0

def z1304 : W := mkw 0x03ff75bfb0040600 0x207feeb7f60080c0 0xf3fffffff0000701 0xfe7ffffffe0000e0

def z1305 : W := mkw 0x008d14a590000000 0x0011a294b2000000 0xd399ffe1f0000001 0x7a733ffc3e000000

def z1306 : W := mkw 0x028d35bfb0000000 0x0051a6b7f6000000 0x0201bffff0000001 0xc04037fffe000000

def z1307 : W := mkw 0x008500c501810842 0x0010a018a0302108 0x238607c7c3818865 0xc470c0f8f870310c

def z1308 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfffe07f80fff9f06 0xffffc0ff01fff3e0

def z1309 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x43f9bfd9c0000000 0x087f37fb38000000

def z1310 : W := mkw 0x008d14a590000000 0x0011a294b2000000 0x739fbfc7c0000001 0xee73f7f8f8000000

def z1311 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x5b8787c7cf8390e3 0x6b70f0f8f9f0721c

def z1312 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0x4399bfdfc0000000 0x887337fbf8000000

def z1313 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0001499 0xfe7ffffffe000293

def z1314 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0xf3fffffff0021083 0xfe7ffffffe004210

def z1315 : W := mkw 0x020815b590000000 0x004102b6b2000000 0xd219ffe1f0000001 0x7a433ffc3e000000

def z1316 : W := mkw 0x07ff75bfb270c001 0x80ffeeb7f64e1800 0xf3fffffff0600001 0xfe7ffffffe0c0000

def z1317 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x7b87c7c7ff83f8ff 0xef70f8f8fff07f1f

def z1318 : W := mkw 0xa158077046d41e88 0x742b00ee08da83d1 0xfff807f80ffc1f9e 0xdfff00ff01ff83f3

def z1319 : W := mkw 0x05f7e8000b5b2006 0x80befd00016b6400 0xfdfff8000ffc0006 0x3fbfff0001ff8000

def z1320 : W := mkw 0x808580c5498308c6 0x1010b018a9306118 0x738787c7c38388e5 0xee70f0f8f870711c

def z1321 : W := mkw 0x808582c54d8318c6 0x5010b058a9b06318 0x4b8787c7cf8398e1 0xe970f0f8f9f0731c

def z1322 : W := mkw 0x0158153090000000 0x002b02a612000000 0xf7f9fff9f0627f9f 0xfeff3fff3e0c4ff3

def z1323 : W := mkw 0x45f7e8000b7be137 0x88befd00016f7c26 0xfdfff8380ffffffe 0xffbfff0701ffffff

def z1324 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8380fffe706 0x3fbfff0701fffce0

def z1325 : W := mkw 0x45d5a8000b7be137 0x88bab500016f7c26 0x4d99b8000ffffffe 0x09b3370001ffffff

def z1326 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xdd99b8000f9c0002 0x1bb3370001f38000

def z1327 : W := mkw 0x02a7708fb0000000 0x0054ee11f6000000 0xf3e7fffff0000001 0xfe7cfffffe000000

def z1328 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf3fffffff0000b61 0xfe7ffffffe00016c

def z1329 : W := mkw 0x0172600002500000 0x002e4c00004a0000 0xfdf878000ffc0006 0x1fbf0f0001ff8000

def z1330 : W := mkw 0x03ff75bfb2500000 0x007feeb7f64a0000 0xf7fffffff07c0001 0xfefffffffe0f8000

def z1331 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0xfdf9b8380ffc1f06 0xdfbf370701ff83e0

def z1332 : W := mkw 0x02a7708fb0000000 0x0054ee11f6000000 0x4387ffc7f0000001 0x2870fff8fe000000

def z1333 : W := mkw 0x03ff75bfb0040400 0x207feeb7f6008080 0xf7fffffff01c0401 0xfefffffffe038080

def z1334 : W := mkw 0x05d5a8000b7be007 0x80bab500016f7c00 0x4999b8000f9fe000 0x0933370001f3fc00

def z1335 : W := mkw 0x05d5a8000b5b2006 0x80bab500016b6400 0x4999b8000f9f8006 0x0933370001f3f000

def z1336 : W := mkw 0x03dd35bfb0000000 0x007ba6b7f6000000 0x4399bfc7f0000001 0x087337f8fe000000

def z1337 : W := mkw 0x43ff75bfb274c731 0x287feeb7f64e98e6 0xf7fffffff07c6719 0xfefffffffe0f8ce3

def z1338 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe21fc1c741a 0x5b833fc43f838e83

def z1339 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f83ffc1f9f 0xdfff00ff07ff83f3

def z1340 : W := mkw 0xa0009a00dc0e348c 0x740013401b81c691 0xdc19f801fc1e749b 0x3b833f003f83ce93

def z1341 : W := mkw 0x03ff75bfb0000000 0x007feeb7f6000000 0x23e7fffff0000001 0xe47cfffffe000000

def z1342 : W := mkw 0xe0a7d88ff92be1ff 0x1c14fb11ff257c3f 0x0007f807f003e0f9 0x2000ff00fe007c1f

def z1343 : W := mkw 0x43ff75bfb0000130 0x087feeb7f6000026 0xf7fffffff0601fff 0xfefffffffe0c03ff

def z1344 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfff8203fffe007 0x7fbfff0407fffc00

def z1345 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0xfdfffe01cfffe007 0x7fbfffc039fffc00

def z1346 : W := mkw 0x0008066004841c00 0x600100cc00908380 0xfff807f80ffc1f06 0xdfff00ff01ff83e0

def z1347 : W := mkw 0x43ff75bfb020c131 0x087feeb7f6041826 0xf3fffffff0639be7 0xfe7ffffffe0c737c

def z1348 : W := mkw 0x05f7e80a2b7be007 0x80befd01456f7c00 0xfdfff83e3ffff49f 0xffbfff07c7fffe93

def z1349 : W := mkw 0x85f7e8004b7be087 0x90befd00096f7c10 0xfdfff801cfffe087 0x3fbfff0039fffc10

def z1350 : W := mkw 0x00a7c800092be007 0x0014f90001257c00 0xfdfff8000fffe006 0x3fbfff0001fffc00

def z1351 : W := mkw 0x808582c54d871ec6 0x7010b058a9b0e3d8 0x7b8787c7cf839fe7 0xef70f0f8f9f073fc

def z1352 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xdc19fe21fc1c6419 0x7b833fc43f838c83

def z1353 : W := mkw 0x037a753ab0000000 0x006f4ea756000000 0xf3f9fff9f0000001 0xfe7f3fff3e000000

def z1354 : W := mkw 0x2008177094841e08 0x640102ee129083c1 0x020007f830001f18 0xc04000ff060003e3

def z1355 : W := mkw 0x00858800090b2006 0x0010b10001216400 0xdd99f8000f9e6002 0x3bb33f0001f3cc00

def z1356 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xff99ffe1fc1e749b 0xfff33ffc3f83ce93

def z1357 : W := mkw 0x05f7e8000b7be007 0x80befd00016f7c00 0x49f9b8000ffc0000 0x093f370001ff8000

def z1358 : W := mkw 0x0285308590000000 0x0050a610b2000000 0x7387bfc7c0000001 0xee70f7f8f8000000

def z1359 : W := mkw 0xa0089e20dc0e348c 0x740113c41b81c691 0xfc79fe21fc7e749f 0x7f8f3fc43f8fce93

def z1360 : W := mkw 0xa0009800d80a208c 0x140013001b014411 0x8419f801f01e6099 0x30833f003e03cc13

def z1361 : W := mkw 0x45f7e80a2b7be137 0x88befd01456f7c26 0xfdfff8383ffff79f 0x7fbfff0707fffef3

def z1362 : W := mkw 0x0158077006d41e00 0x602b00ee00da83c0 0xfff807f80fff9fe6 0xdfff00ff01fff3fc

def z1363 : W := mkw 0x0000000000000000 0x0000000000000000 0xb466403e3063ffff 0xf68cc807c60c7fff

def z1364 : W := mkw 0x0158053002540600 0x202b00a6004a80c0 0xfff807f80ffc0706 0xdfff00ff01ff80e0

def z1365 : W := mkw 0x03ff75b590000000 0x007feeb6b2000000 0x63ffbfc1c0000000 0x0c7ff7f838000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z6,z8]),(1,[z1,z2,z7,z3,z9,z6]),(0,[z10,z11,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z12,z3,z4,z6]),(0,[z1,z13,z2,z7,z3,z4,z6])],[(0,[z1,z14,z2,z7,z3,z4,z6]),(0,[z15,z1,z16,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z17,z4,z6]),(0,[z1,z2,z7,z3,z4,z18,z6]),(0,[z1,z2,z7,z3,z4,z6,z19]),(0,[z1,z2,z7,z20,z3,z4,z6]),(0,[z1,z2,z21,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z23,z6]),(1,[z24,z1,z2,z3,z25,z6]),(0,[z1,z2,z7,z3,z4,z6,z26]),(1,[z1,z2,z7,z27,z4,z28])],[(0,[z1,z2,z7,z29,z3,z4,z6]),(0,[z1,z2,z30,z3,z31,z4,z6]),(0,[z1,z7,z3,z32,z33,z4,z6]),(0,[z1,z7,z3,z33,z4,z28,z6]),(0,[z1,z2,z3,z34,z31,z4,z6])],[(0,[z1,z2,z7,z3,z4,z35,z6]),(0,[z1,z2,z7,z36,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z37,z6]),(1,[z38,z1,z2,z7,z6,z39]),(1,[z1,z2,z7,z40,z41,z6]),(0,[z1,z2,z7,z3,z41,z6,z42]),(1,[z1,z43,z7,z3,z4,z6]),(0,[z44,z1,z43,z7,z3,z4,z6])],[(0,[z1,z22,z7,z3,z4,z6,z42]),(0,[z1,z2,z7,z3,z4,z5,z6])],[(0,[z1,z2,z45,z7,z3,z4,z6]),(0,[z46,z1,z2,z7,z3,z4,z6]),(0,[z15,z1,z47,z7,z3,z4,z6]),(0,[z48,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z3,z49,z31,z4,z6])],[(0,[z50,z2,z7,z3,z51,z4,z6]),(0,[z1,z52,z2,z3,z31,z4,z6]),(0,[z48,z1,z22,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z3,z4,z6]),(0,[z1,z2,z3,z53,z31,z4,z6]),(0,[z1,z2,z54,z7,z3,z4,z6]),(0,[z1,z55,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z56,z3,z4,z6]),(1,[z1,z2,z7,z3,z4,z57]),(0,[z1,z2,z7,z3,z4,z58,z6]),(0,[z1,z59,z2,z7,z3,z4,z6]),(0,[z1,z52,z22,z7,z3,z4,z6]),(0,[z60,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z61]),(1,[z1,z2,z3,z4,z62,z6])]],
   [[(0,[z63,z1,z2,z7,z3,z4,z6]),(0,[z64,z1,z2,z7,z3,z4,z6]),(1,[z65,z1,z2,z3,z4,z66]),(0,[z38,z67,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z68,z6]),(0,[z69,z1,z2,z7,z3,z4,z6]),(0,[z70,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z71]),(0,[z72,z1,z73,z2,z7,z3,z6]),(0,[z1,z2,z7,z74,z3,z75,z4])],[(0,[z76,z1,z2,z77,z3,z4,z6]),(0,[z78,z1,z2,z7,z3,z4,z6]),(0,[z1,z79,z2,z7,z3,z4,z6])],[(0,[z50,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z80,z30,z3,z4,z6]),(0,[z1,z2,z7,z81,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z82,z6]),(0,[z1,z2,z3,z31,z31,z4,z6]),(1,[z1,z2,z7,z3,z4,z83])],[(0,[z15,z1,z84,z2,z3,z4,z6]),(0,[z11,z1,z22,z7,z3,z4,z6]),(0,[z1,z85,z22,z7,z3,z4,z6]),(0,[z1,z86,z7,z87,z3,z4,z6])],[(0,[z1,z2,z30,z3,z88,z4,z6]),(0,[z1,z2,z7,z3,z89,z4,z6]),(0,[z65,z1,z2,z7,z3,z90,z6]),(0,[z1,z2,z7,z3,z91,z4,z6])],[(0,[z92,z1,z2,z7,z3,z4,z6]),(0,[z93,z1,z2,z7,z3,z4,z6])],[(0,[z1,z94,z2,z95,z3,z4,z6]),(0,[z15,z2,z7,z3,z4,z6,z96]),(0,[z0,z1,z2,z3,z4,z25,z6]),(0,[z1,z84,z2,z97,z3,z4,z6]),(0,[z1,z2,z77,z97,z3,z4,z6]),(0,[z1,z2,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z98])]],
   [[(0,[z1,z22,z99,z7,z3,z4,z6]),(0,[z1,z22,z2,z7,z33,z4,z6]),(0,[z1,z2,z100,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z101,z4,z6]),(0,[z1,z2,z95,z3,z31,z4,z6]),(0,[z0,z1,z2,z7,z3,z4,z102]),(0,[z1,z2,z7,z3,z103,z4,z6]),(0,[z1,z2,z7,z3,z41,z104,z6]),(0,[z1,z2,z7,z3,z4,z6,z105]),(0,[z106,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z107,z6])],[(0,[z108,z1,z7,z3,z4,z23,z6]),(0,[z109,z1,z52,z7,z3,z4,z6]),(1,[z1,z110,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z111,z6]),(0,[z1,z112,z7,z3,z33,z4,z6]),(1,[z1,z2,z113,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z25,z6]),(0,[z1,z114,z7,z115,z3,z4,z6])],[(0,[z116,z1,z2,z7,z3,z4,z6]),(0,[z1,z117,z2,z7,z3,z4,z6]),(0,[z1,z118,z2,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z119,z6]),(0,[z1,z2,z114,z7,z3,z4,z120]),(0,[z1,z2,z7,z3,z4,z6,z121]),(0,[z122,z1,z2,z7,z3,z4,z6]),(0,[z123,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z124,z4,z6])],[(0,[z1,z2,z7,z125,z3,z4,z6]),(0,[z1,z2,z7,z3,z75,z4,z6])],[(0,[z50,z1,z2,z7,z30,z4,z6]),(0,[z126,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z127,z6]),(0,[z44,z1,z2,z7,z3,z127,z6])],[(0,[z128,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z129,z6]),(0,[z0,z1,z2,z3,z31,z4,z6]),(0,[z11,z1,z2,z7,z30,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z130]),(0,[z1,z2,z7,z3,z131,z4,z6]),(0,[z132,z1,z2,z7,z3,z4,z6])]],
   [[(0,[z15,z1,z2,z7,z3,z4,z6]),(0,[z0,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z133,z4,z6]),(1,[z1,z2,z77,z3,z4,z6]),(0,[z44,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z134,z3,z4,z6])],[(0,[z135,z2,z7,z3,z51,z4,z6]),(0,[z1,z2,z7,z3,z4,z120,z28]),(0,[z136,z1,z2,z7,z3,z4,z6]),(0,[z137,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z138,z6]),(0,[z139,z1,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z6,z140]),(0,[z38,z1,z2,z141,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z6,z142]),(1,[z1,z52,z112,z3,z4,z6]),(0,[z106,z1,z7,z3,z33,z4,z6]),(0,[z1,z22,z2,z7,z143,z4,z6]),(0,[z109,z1,z2,z7,z3,z4,z140]),(0,[z109,z1,z2,z77,z3,z4,z6]),(0,[z144,z1,z2,z3,z31,z4,z6]),(0,[z1,z145,z2,z7,z3,z4,z6]),(1,[z1,z7,z3,z146,z4,z6]),(0,[z1,z7,z3,z4,z147,z6,z42])],[(0,[z108,z1,z95,z7,z3,z4,z6]),(0,[z1,z148,z2,z3,z31,z4,z6]),(0,[z1,z7,z87,z3,z33,z4,z6])],[(1,[z108,z148,z7,z3,z4,z6]),(0,[z1,z148,z22,z7,z3,z4,z6]),(0,[z65,z0,z1,z2,z3,z4,z6]),(0,[z1,z149,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z150,z6])],[(0,[z1,z2,z151,z3,z31,z4,z6]),(0,[z152,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z153,z4,z6]),(0,[z154,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z155,z3,z153,z4,z6]),(0,[z1,z2,z7,z3,z4,z156,z6]),(1,[z1,z2,z7,z3,z157,z6]),(0,[z44,z1,z2,z7,z3,z157,z6])],[(0,[z1,z22,z7,z3,z4,z6,z96]),(0,[z135,z1,z22,z7,z3,z4,z6]),(1,[z158,z1,z2,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z159,z6]),(0,[z65,z1,z22,z7,z3,z4,z6]),(0,[z1,z160,z2,z7,z3,z4,z6]),(0,[z38,z1,z2,z7,z4,z6,z39]),(0,[z1,z2,z7,z161,z3,z4,z6]),(1,[z1,z2,z7,z3,z162,z42]),(0,[z1,z2,z7,z163,z3,z4,z6])]],
   [[(0,[z1,z2,z77,z27,z3,z4,z6]),(0,[z1,z164,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z66]),(0,[z165,z1,z2,z7,z3,z4,z6])],[(0,[z15,z1,z7,z3,z33,z4,z6]),(0,[z2,z7,z3,z166,z4,z104,z6]),(0,[z1,z73,z2,z7,z3,z75,z6]),(0,[z1,z2,z7,z3,z75,z4,z167]),(0,[z1,z2,z7,z168,z3,z4,z6]),(0,[z169,z1,z2,z7,z3,z4,z6]),(0,[z170,z1,z7,z3,z4,z6,z42])],[(0,[z1,z171,z2,z7,z3,z4,z6]),(0,[z172,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z173,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z23,z6]),(0,[z1,z2,z174,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z175,z6]),(1,[z1,z2,z176,z3,z4,z6]),(0,[z177,z1,z2,z77,z3,z4,z6])],[(1,[z50,z2,z7,z51,z4,z6]),(0,[z1,z22,z7,z3,z4,z120,z6]),(0,[z1,z7,z3,z33,z4,z6,z42]),(0,[z1,z2,z77,z3,z153,z4,z6])],[(0,[z1,z2,z7,z178,z3,z4,z6]),(0,[z1,z7,z3,z75,z4,z23,z6]),(0,[z1,z2,z7,z3,z4,z6,z179]),(0,[z44,z1,z2,z7,z4,z6,z180]),(0,[z1,z2,z7,z3,z181,z4,z6])],[(0,[z1,z2,z7,z3,z88,z4,z6]),(0,[z1,z22,z7,z3,z4,z5,z6]),(0,[z1,z182,z2,z7,z3,z4,z6]),(0,[z183,z1,z2,z7,z3,z4,z6])],[(0,[z184,z1,z2,z7,z3,z4,z6]),(0,[z50,z1,z185,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z186,z6]),(0,[z1,z2,z7,z3,z187,z4,z6])]],
   [[(0,[z1,z2,z7,z188,z3,z4,z6]),(0,[z1,z22,z2,z7,z3,z4,z6]),(0,[z65,z24,z1,z2,z3,z4,z6])],[(0,[z189,z1,z95,z7,z3,z4,z6]),(1,[z15,z2,z151,z3,z4,z6]),(0,[z1,z190,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z191,z4,z6]),(0,[z192,z1,z2,z77,z3,z4,z6])],[(0,[z189,z2,z95,z7,z3,z4,z6]),(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z6,z193]),(0,[z1,z2,z7,z194,z3,z4,z6])],[(0,[z50,z1,z2,z7,z3,z4,z195]),(0,[z1,z52,z2,z97,z3,z4,z6]),(0,[z1,z14,z22,z7,z3,z4,z6]),(0,[z1,z2,z196,z7,z3,z4,z6]),(0,[z197,z1,z73,z7,z3,z4,z6]),(0,[z1,z7,z3,z75,z4,z186,z6]),(0,[z1,z2,z198,z7,z3,z4,z6]),(1,[z199,z1,z2,z7,z3,z6])],[(0,[z1,z148,z7,z97,z3,z4,z6]),(0,[z1,z7,z3,z200,z33,z4,z6]),(0,[z1,z2,z7,z201,z3,z4,z6])],[(0,[z1,z2,z7,z202,z3,z4,z6]),(1,[z1,z7,z3,z4,z203,z6]),(0,[z204,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z205]),(0,[z1,z2,z7,z3,z4,z6,z206]),(0,[z1,z2,z7,z3,z207,z4,z6]),(0,[z44,z1,z2,z7,z27,z4,z6]),(0,[z1,z2,z7,z27,z4,z28,z6])],[(0,[z1,z2,z7,z3,z208,z4,z6]),(0,[z1,z2,z114,z7,z3,z4,z5])],[(0,[z1,z2,z112,z77,z3,z4,z6]),(1,[z48,z1,z7,z33,z4,z6]),(0,[z1,z2,z7,z3,z200,z4,z6]),(0,[z1,z149,z7,z3,z4,z23,z6]),(0,[z1,z2,z3,z31,z4,z6,z39]),(0,[z1,z2,z7,z3,z4,z209,z6]),(0,[z1,z2,z77,z3,z4,z6,z66]),(0,[z1,z2,z7,z3,z210,z4,z6]),(1,[z211,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z212])]],
   [[(0,[z1,z2,z7,z213,z3,z4,z6]),(0,[z108,z2,z7,z3,z4,z6,z96]),(0,[z1,z2,z3,z33,z31,z4,z6]),(0,[z214,z1,z2,z3,z31,z4,z6]),(0,[z38,z1,z2,z3,z31,z4,z6])],[(0,[z1,z2,z99,z7,z3,z4,z6]),(0,[z10,z1,z215,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z33,z4,z6]),(0,[z1,z216,z2,z7,z3,z4,z6])],[(0,[z1,z217,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z104,z6]),(1,[z182,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z218])],[(0,[z219,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z220,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z221,z6])],[(0,[z222,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z223]),(0,[z1,z2,z224,z7,z3,z4,z6]),(0,[z24,z1,z7,z3,z33,z4,z6]),(0,[z109,z182,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z87,z3,z4,z6]),(0,[z225,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z155,z7,z3,z4,z6])],[(1,[z1,z94,z2,z3,z4,z6]),(0,[z226,z1,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z6,z227]),(0,[z1,z2,z7,z41,z4,z6,z39]),(0,[z1,z2,z7,z3,z228,z4,z6])],[(0,[z1,z2,z229,z7,z3,z4,z6]),(0,[z1,z73,z2,z7,z3,z4,z6]),(1,[z1,z230,z7,z3,z4,z6]),(0,[z1,z2,z7,z231,z3,z4,z6])],[(0,[z1,z232,z2,z7,z3,z4,z6]),(0,[z233,z1,z2,z7,z3,z4,z6])]],
   [[(0,[z2,z95,z7,z3,z4,z6,z96]),(0,[z1,z234,z2,z7,z3,z4,z6]),(0,[z48,z1,z2,z235,z3,z4,z6]),(0,[z197,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z236,z6]),(0,[z1,z2,z77,z40,z3,z4,z6]),(1,[z1,z237,z7,z3,z4,z6]),(0,[z238,z1,z2,z7,z3,z4,z6]),(0,[z38,z1,z2,z7,z3,z4,z83]),(1,[z1,z7,z3,z239,z4,z6])],[(0,[z108,z1,z2,z7,z3,z4,z6]),(0,[z15,z1,z2,z3,z4,z25,z6]),(0,[z1,z240,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z3,z153,z6])],[(0,[z1,z2,z7,z241,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z242]),(0,[z1,z2,z7,z3,z4,z243,z6]),(0,[z1,z84,z52,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z6,z180]),(0,[z1,z22,z244,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z245,z6]),(0,[z1,z2,z7,z3,z4,z6,z140]),(0,[z1,z2,z7,z3,z246,z4,z6]),(0,[z247,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z248,z6]),(0,[z1,z2,z7,z40,z3,z41,z6]),(0,[z249,z1,z2,z7,z3,z4,z6])],[(0,[z250,z1,z2,z3,z31,z4,z6]),(0,[z106,z1,z22,z7,z3,z4,z6]),(0,[z1,z110,z7,z27,z3,z4,z6])],[(0,[z1,z2,z7,z3,z251,z4,z6]),(0,[z1,z2,z252,z7,z3,z4,z6]),(0,[z253,z1,z2,z7,z3,z4,z6]),(0,[z1,z254,z2,z7,z3,z4,z6])],[(0,[z1,z2,z77,z151,z3,z4,z6]),(0,[z1,z2,z77,z3,z166,z4,z6]),(0,[z1,z255,z7,z3,z4,z6,z96]),(0,[z1,z22,z7,z3,z31,z4,z6]),(1,[z1,z2,z3,z256,z4,z6])],[(0,[z1,z7,z151,z3,z33,z4,z6]),(0,[z257,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z196,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z258,z6])],[(0,[z1,z2,z7,z3,z4,z6,z259]),(0,[z50,z1,z2,z260,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z96]),(0,[z1,z7,z3,z33,z41,z4,z6]),(0,[z1,z73,z7,z3,z33,z4,z6]),(1,[z261,z2,z7,z3,z4,z6]),(0,[z262,z1,z2,z77,z3,z4,z6]),(1,[z1,z2,z114,z3,z4,z5]),(0,[z1,z2,z7,z3,z4,z83,z6])]],
   [[(0,[z1,z2,z7,z3,z263,z4,z6]),(0,[z197,z1,z84,z7,z3,z4,z6])],[(1,[z1,z47,z7,z3,z4,z6]),(0,[z1,z264,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z6,z180])],[(0,[z108,z1,z7,z3,z33,z4,z6]),(0,[z15,z1,z22,z7,z3,z4,z6]),(0,[z265,z1,z2,z7,z3,z4,z6]),(0,[z1,z84,z2,z77,z3,z4,z6]),(0,[z1,z52,z112,z7,z3,z4,z6]),(1,[z1,z22,z77,z3,z4,z6]),(0,[z1,z2,z7,z74,z3,z4,z6])],[(0,[z266,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z30,z3,z4,z6]),(0,[z139,z1,z22,z7,z3,z4,z6]),(0,[z197,z1,z2,z176,z3,z4,z6]),(0,[z1,z149,z2,z7,z3,z4,z23])],[(0,[z250,z135,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z267,z3,z4,z6]),(0,[z268,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z9,z6]),(0,[z1,z2,z7,z3,z4,z120,z6]),(0,[z1,z2,z7,z3,z4,z6,z269]),(0,[z1,z2,z270,z7,z3,z4,z6]),(0,[z1,z73,z7,z3,z75,z4,z6]),(0,[z271,z1,z2,z7,z3,z4,z6]),(0,[z170,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z272,z6]),(0,[z1,z2,z7,z3,z4,z28,z96]),(0,[z1,z155,z7,z3,z33,z4,z6]),(0,[z1,z7,z3,z33,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z6,z273])],[(0,[z1,z255,z2,z7,z3,z4,z6]),(0,[z1,z2,z114,z7,z3,z4,z96]),(0,[z274,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z141,z3,z4,z6])]],
   [[(0,[z1,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z275,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z276]),(0,[z106,z1,z2,z7,z31,z4,z6]),(1,[z1,z2,z277,z3,z4,z6]),(0,[z44,z1,z2,z277,z3,z4,z6]),(0,[z1,z2,z7,z3,z278,z4,z6])],[(0,[z1,z2,z2,z7,z3,z4,z6]),(0,[z279,z1,z2,z7,z3,z4,z6]),(0,[z10,z1,z280,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z281])],[(0,[z15,z135,z2,z7,z3,z4,z6]),(0,[z50,z1,z2,z7,z3,z9,z6]),(0,[z1,z2,z7,z3,z4,z282,z6]),(0,[z1,z2,z7,z3,z4,z283,z6]),(0,[z1,z84,z7,z3,z75,z4,z6]),(0,[z1,z284,z2,z7,z3,z4,z6])],[(1,[z1,z215,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z285]),(0,[z286,z1,z2,z7,z3,z4,z6]),(0,[z24,z1,z2,z7,z3,z153,z6]),(0,[z1,z2,z7,z3,z4,z6,z287])],[(0,[z1,z280,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z288,z3,z4,z6]),(0,[z289,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z28,z6])],[(0,[z50,z1,z2,z3,z31,z4,z6]),(0,[z197,z1,z7,z3,z4,z23,z6]),(0,[z1,z2,z3,z31,z290,z4,z6]),(0,[z1,z2,z3,z31,z162,z4,z6]),(0,[z1,z2,z7,z291,z3,z4,z28])],[(0,[z189,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z292,z6]),(0,[z11,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z293,z4,z6]),(0,[z1,z2,z7,z3,z294,z4,z6]),(0,[z1,z2,z277,z7,z3,z4,z6])],[(0,[z1,z2,z7,z295,z3,z4,z6]),(0,[z1,z2,z3,z51,z31,z4,z6]),(1,[z11,z2,z7,z30,z4,z6]),(0,[z76,z1,z7,z3,z33,z4,z6]),(0,[z197,z72,z1,z2,z7,z3,z6]),(1,[z1,z2,z77,z31,z4,z6]),(0,[z1,z2,z7,z3,z296,z4,z6])]],
   [[(0,[z1,z94,z2,z7,z3,z4,z6]),(0,[z1,z2,z297,z7,z3,z4,z6]),(0,[z50,z1,z298,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z6,z66]),(0,[z1,z2,z299,z7,z3,z4,z6])],[(0,[z1,z7,z3,z33,z33,z4,z6]),(0,[z1,z22,z2,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z300,z6]),(0,[z1,z2,z301,z7,z3,z4,z6])],[(0,[z302,z1,z2,z7,z3,z4,z6]),(1,[z303,z1,z2,z3,z4,z6]),(0,[z1,z22,z22,z7,z3,z4,z6]),(0,[z1,z304,z2,z7,z3,z4,z6]),(0,[z38,z1,z2,z7,z3,z41,z6]),(0,[z1,z2,z7,z40,z3,z6,z39]),(0,[z1,z305,z2,z7,z3,z4,z6])],[(0,[z197,z1,z7,z3,z4,z186,z6]),(0,[z1,z2,z7,z3,z306,z4,z6]),(0,[z1,z2,z7,z307,z3,z4,z6]),(0,[z1,z2,z7,z308,z3,z4,z6]),(0,[z1,z7,z40,z3,z239,z4,z6])],[(0,[z309,z1,z2,z7,z3,z4,z6]),(0,[z286,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z310,z3,z4,z6]),(0,[z1,z2,z155,z7,z3,z153,z6])],[(0,[z15,z1,z2,z99,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z25,z6])],[(0,[z197,z1,z95,z7,z3,z4,z6]),(0,[z1,z22,z155,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z227]),(0,[z1,z149,z2,z7,z3,z4,z6]),(0,[z311,z1,z2,z77,z3,z4,z6]),(0,[z312,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z3,z313,z4,z6])],[(1,[z189,z95,z7,z3,z4,z6]),(0,[z314,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z166,z6,z39]),(0,[z1,z7,z3,z33,z75,z4,z6])]],
   [[(0,[z1,z2,z7,z3,z315,z4,z6]),(0,[z108,z1,z148,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z316,z6]),(0,[z1,z317,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z291,z3,z4,z6]),(0,[z65,z1,z2,z7,z3,z318,z6]),(0,[z1,z319,z7,z40,z3,z4,z6])],[],[(0,[z108,z189,z2,z7,z3,z4,z6]),(0,[z1,z2,z99,z3,z31,z4,z6]),(0,[z1,z320,z2,z7,z3,z4,z6]),(0,[z76,z1,z2,z7,z3,z104,z6]),(0,[z1,z2,z7,z321,z3,z4,z6]),(1,[z1,z2,z322,z3,z4,z6]),(0,[z1,z2,z7,z3,z34,z4,z6])],[(0,[z323,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z244,z7,z3,z4,z6]),(0,[z1,z2,z7,z324,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z127,z6])],[(0,[z1,z2,z7,z3,z4,z6,z325]),(0,[z1,z2,z7,z326,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z6,z327]),(0,[z328,z1,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z329,z6]),(0,[z48,z1,z2,z77,z3,z4,z6]),(1,[z1,z7,z3,z33,z4,z6]),(0,[z44,z1,z7,z3,z33,z4,z6]),(0,[z1,z22,z77,z7,z3,z4,z6]),(0,[z1,z2,z7,z330,z3,z4,z6]),(0,[z331,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z332,z6]),(0,[z333,z1,z2,z7,z3,z4,z6]),(0,[z50,z1,z2,z7,z3,z119,z6]),(0,[z1,z2,z3,z31,z166,z4,z6]),(0,[z1,z52,z2,z77,z3,z4,z6]),(0,[z222,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z75,z4,z6]),(1,[z1,z100,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z31,z4,z6])],[(1,[z1,z2,z7,z3,z4,z334]),(0,[z1,z2,z7,z335,z3,z4,z6]),(1,[z135,z2,z7,z3,z4,z120]),(0,[z336,z1,z2,z7,z3,z4,z6]),(0,[z337,z1,z2,z7,z3,z4,z6]),(0,[z197,z1,z2,z7,z3,z75,z6]),(0,[z1,z338,z2,z7,z3,z4,z6]),(0,[z177,z1,z2,z7,z3,z4,z6])]],
   [[(0,[z339,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z340,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z341,z4,z6]),(0,[z303,z1,z2,z7,z3,z4,z6]),(0,[z135,z1,z2,z3,z31,z4,z6]),(0,[z342,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z343,z6])],[(0,[z344,z1,z2,z7,z3,z4,z6]),(0,[z345,z1,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z6,z39]),(0,[z65,z1,z2,z3,z31,z4,z6]),(0,[z346,z1,z2,z7,z3,z4,z6])],[(0,[z1,z95,z7,z97,z3,z4,z6]),(0,[z1,z2,z7,z3,z347,z4,z6]),(0,[z1,z22,z7,z97,z3,z4,z6]),(0,[z348,z1,z2,z7,z3,z4,z6]),(0,[z261,z1,z2,z7,z3,z4,z6]),(0,[z349,z1,z2,z7,z3,z4,z6]),(0,[z65,z1,z2,z7,z3,z4,z5]),(1,[z1,z350,z7,z3,z4,z6]),(0,[z351,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z352,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z62,z6])],[(0,[z189,z1,z7,z3,z4,z23,z6]),(0,[z1,z2,z7,z3,z4,z353,z6]),(0,[z108,z1,z22,z7,z3,z4,z6]),(1,[z1,z280,z7,z3,z4,z6]),(0,[z1,z354,z2,z7,z3,z4,z6])],[(0,[z50,z11,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z355,z6]),(0,[z1,z2,z356,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z23,z6]),(0,[z1,z22,z149,z7,z3,z4,z6]),(0,[z106,z1,z357,z7,z3,z4,z6]),(0,[z1,z2,z7,z358,z3,z4,z6]),(0,[z1,z2,z7,z359,z3,z4,z6])],[(0,[z1,z22,z7,z30,z3,z4,z6]),(0,[z250,z1,z2,z7,z3,z4,z120]),(0,[z1,z2,z7,z3,z360,z4,z6]),(0,[z72,z1,z7,z3,z33,z4,z6]),(0,[z109,z1,z7,z3,z75,z4,z6]),(0,[z192,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z361,z7,z3,z4,z6])],[(0,[z1,z7,z30,z3,z33,z4,z6]),(0,[z362,z1,z2,z7,z3,z4,z6]),(0,[z363,z1,z2,z7,z3,z4,z6]),(0,[z1,z254,z22,z7,z3,z4,z6])],[(0,[z15,z1,z2,z155,z3,z4,z6]),(0,[z364,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z365,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z366]),(1,[z1,z2,z174,z3,z4,z6])]],
   [[(0,[z1,z2,z7,z3,z104,z6,z39]),(0,[z1,z2,z367,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z368,z6]),(0,[z1,z2,z7,z27,z3,z4,z28]),(0,[z369,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z370,z6]),(0,[z1,z2,z95,z77,z3,z4,z6]),(1,[z1,z2,z3,z4,z58,z6]),(0,[z1,z2,z7,z3,z371,z4,z6]),(0,[z372,z1,z2,z7,z3,z4,z6])],[(0,[z50,z1,z2,z7,z51,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z373]),(0,[z303,z1,z2,z3,z4,z6,z96]),(0,[z374,z1,z2,z7,z3,z4,z6]),(0,[z1,z264,z2,z3,z31,z4,z6]),(0,[z38,z1,z2,z7,z3,z6,z39]),(0,[z1,z2,z7,z3,z4,z375,z6])],[(0,[z11,z1,z2,z7,z51,z4,z6]),(0,[z2,z7,z3,z51,z4,z104,z6]),(0,[z1,z2,z7,z3,z376,z4,z6]),(0,[z1,z377,z2,z7,z3,z4,z6]),(0,[z348,z1,z7,z3,z33,z4,z6]),(0,[z1,z264,z22,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z378,z4,z6]),(0,[z1,z2,z77,z3,z4,z23,z6]),(0,[z265,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z155,z7,z3,z25,z6]),(0,[z1,z2,z7,z379,z3,z4,z6]),(0,[z44,z1,z2,z7,z3,z4,z28]),(0,[z380,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z381,z6]),(0,[z382,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z57]),(0,[z383,z1,z2,z7,z3,z4,z6]),(0,[z384,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z90,z6])],[(0,[z385,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z51,z4,z6]),(0,[z1,z2,z386,z7,z3,z4,z6]),(0,[z387,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z28,z6])],[(0,[z1,z2,z7,z3,z388,z4,z6]),(0,[z1,z2,z7,z3,z4,z120,z42]),(0,[z1,z2,z7,z389,z3,z4,z6]),(0,[z1,z2,z3,z3,z31,z4,z6]),(0,[z1,z2,z77,z3,z4,z6,z42]),(1,[z1,z86,z7,z3,z4,z6]),(0,[z24,z1,z2,z7,z3,z4,z6])],[(0,[z0,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z390,z6]),(0,[z391,z1,z2,z7,z3,z4,z6]),(0,[z392,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z393,z3,z4,z6])]],
   [[(1,[z1,z394,z2,z3,z4,z6]),(0,[z395,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z51,z33,z4,z6]),(0,[z1,z396,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z6,z397]),(0,[z398,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z270,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z186,z6]),(0,[z1,z2,z7,z3,z157,z4,z6])],[(0,[z1,z2,z322,z3,z166,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z399]),(1,[z250,z2,z7,z3,z4,z96]),(0,[z400,z1,z2,z7,z3,z4,z6]),(0,[z401,z1,z2,z7,z3,z4,z6]),(1,[z106,z1,z2,z31,z4,z6]),(0,[z1,z2,z402,z77,z3,z4,z6]),(0,[z1,z2,z403,z7,z3,z4,z6])],[(0,[z1,z148,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z404]),(0,[z1,z2,z405,z7,z3,z4,z6]),(0,[z1,z22,z7,z27,z3,z4,z6]),(0,[z1,z2,z7,z3,z406,z4,z6]),(0,[z1,z407,z2,z7,z3,z4,z6]),(0,[z65,z1,z2,z114,z3,z4,z6]),(0,[z1,z2,z7,z115,z3,z4,z6])],[(0,[z1,z2,z7,z3,z408,z4,z6]),(0,[z197,z1,z2,z7,z3,z4,z6])],[(0,[z2,z99,z7,z151,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z102,z6]),(0,[z1,z2,z409,z7,z3,z4,z6]),(0,[z1,z2,z298,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z410,z4,z6]),(0,[z382,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z113,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z411,z4,z6]),(0,[z1,z2,z7,z291,z3,z4,z180]),(0,[z1,z412,z2,z7,z3,z4,z6])],[(0,[z1,z99,z7,z3,z33,z4,z6]),(0,[z76,z1,z2,z7,z3,z4,z413]),(0,[z1,z2,z3,z414,z31,z4,z6]),(0,[z1,z2,z27,z3,z31,z4,z6]),(0,[z415,z1,z2,z7,z3,z4,z6]),(1,[z1,z7,z3,z4,z147,z6])],[(0,[z1,z2,z7,z3,z4,z416,z6]),(0,[z135,z11,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z417,z4,z6])]],
   [[(0,[z1,z2,z7,z3,z4,z195,z6]),(0,[z1,z2,z7,z418,z3,z4,z6]),(0,[z1,z419,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z420,z6])],[(0,[z1,z2,z421,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z220,z4,z6]),(0,[z1,z2,z422,z7,z3,z4,z6]),(0,[z1,z2,z7,z291,z3,z4,z6])],[(1,[z1,z2,z7,z3,z4,z423]),(0,[z135,z1,z2,z7,z3,z4,z96]),(0,[z424,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z425,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z426,z6]),(0,[z1,z2,z427,z7,z3,z4,z6])],[(0,[z262,z1,z2,z7,z3,z4,z6]),(1,[z1,z317,z7,z3,z4,z6]),(0,[z428,z1,z2,z7,z3,z4,z6]),(0,[z65,z1,z2,z7,z3,z4,z96]),(0,[z1,z2,z97,z3,z4,z5,z6]),(0,[z429,z1,z2,z7,z3,z4,z6])],[(0,[z1,z52,z95,z7,z3,z4,z6]),(0,[z1,z430,z2,z7,z3,z4,z6]),(0,[z1,z431,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z104,z6]),(0,[z1,z7,z3,z33,z4,z6,z140]),(0,[z1,z2,z7,z3,z4,z6,z432])],[(0,[z1,z2,z7,z3,z4,z433,z6]),(0,[z10,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z434,z7,z3,z4,z6]),(0,[z1,z435,z2,z7,z3,z4,z6]),(0,[z1,z436,z2,z7,z3,z4,z6]),(0,[z197,z1,z7,z3,z33,z4,z6]),(0,[z106,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z437,z7,z3,z4,z6])],[(0,[z1,z84,z2,z7,z3,z4,z6]),(1,[z1,z3,z33,z31,z4,z6]),(0,[z1,z2,z438,z7,z3,z4,z6]),(0,[z1,z2,z77,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z439,z4,z6]),(1,[z44,z1,z2,z7,z4,z180])],[(0,[z109,z189,z1,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z162,z4,z6]),(0,[z1,z73,z2,z7,z3,z6,z42]),(0,[z1,z149,z2,z3,z31,z4,z6]),(0,[z1,z149,z2,z7,z3,z4,z42]),(0,[z1,z2,z7,z4,z28,z6,z180]),(0,[z1,z2,z7,z291,z3,z6,z42])]],
   [[(1,[z1,z16,z7,z3,z4,z6]),(0,[z1,z149,z2,z7,z291,z3,z4]),(0,[z1,z440,z2,z7,z3,z4,z6]),(0,[z24,z1,z2,z3,z4,z5,z6])],[(0,[z15,z2,z7,z151,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z334]),(0,[z1,z7,z3,z33,z4,z6,z96]),(0,[z1,z2,z7,z3,z4,z96,z180]),(1,[z1,z7,z3,z4,z221,z6]),(0,[z1,z2,z7,z441,z3,z4,z6]),(0,[z1,z43,z2,z7,z3,z4,z6])],[(0,[z1,z2,z442,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z443,z6]),(0,[z1,z7,z3,z33,z263,z4,z6]),(0,[z1,z22,z7,z3,z4,z6,z66]),(0,[z1,z73,z2,z7,z3,z186,z6]),(0,[z1,z444,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z39])],[(0,[z1,z2,z7,z445,z3,z4,z6]),(0,[z446,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z97,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z447]),(0,[z1,z2,z77,z3,z4,z6,z140]),(0,[z1,z2,z7,z3,z4,z6,z448]),(1,[z1,z2,z3,z449,z4,z6])],[(0,[z15,z1,z2,z3,z31,z4,z6]),(1,[z1,z2,z7,z3,z4,z413]),(0,[z1,z2,z7,z3,z4,z120,z180]),(0,[z1,z2,z450,z7,z3,z4,z6]),(0,[z262,z1,z7,z3,z33,z4,z6]),(0,[z1,z22,z7,z143,z3,z4,z6]),(0,[z109,z261,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z451,z3,z4,z6]),(0,[z1,z2,z7,z452,z3,z4,z6]),(0,[z1,z149,z2,z168,z3,z4,z6]),(0,[z72,z1,z2,z3,z31,z4,z6]),(0,[z1,z237,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z453,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z454]),(0,[z72,z1,z2,z7,z3,z4,z42])],[(0,[z1,z2,z7,z3,z4,z6,z455]),(0,[z1,z2,z7,z3,z4,z456,z6]),(0,[z10,z1,z7,z3,z33,z4,z6]),(0,[z65,z1,z2,z97,z3,z4,z6]),(0,[z72,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z457,z6]),(0,[z109,z1,z2,z7,z3,z4,z23]),(0,[z106,z1,z2,z7,z87,z4,z6]),(0,[z1,z145,z2,z3,z31,z4,z6]),(0,[z458,z1,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z291,z3,z4])],[(0,[z1,z2,z7,z3,z4,z459,z6]),(0,[z460,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z120,z6]),(0,[z1,z84,z7,z3,z33,z4,z6]),(0,[z1,z112,z7,z97,z3,z4,z6]),(0,[z461,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z291,z3,z31,z4,z6])]],
   [[(1,[z0,z2,z99,z3,z4,z6]),(1,[z1,z2,z3,z88,z4,z6]),(0,[z1,z2,z7,z462,z3,z4,z6]),(0,[z1,z84,z2,z112,z3,z4,z6]),(0,[z1,z2,z7,z463,z3,z4,z6]),(0,[z1,z2,z464,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z153,z4,z6]),(0,[z38,z1,z2,z77,z3,z4,z6])],[(0,[z76,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z6,z105]),(0,[z1,z2,z77,z3,z41,z4,z6]),(1,[z1,z2,z7,z3,z4,z465]),(0,[z1,z2,z466,z7,z3,z4,z6])],[(0,[z189,z1,z2,z7,z3,z4,z6]),(0,[z11,z2,z7,z3,z4,z104,z6]),(0,[z135,z1,z2,z7,z3,z4,z120]),(0,[z1,z2,z97,z3,z4,z25,z6]),(0,[z109,z1,z7,z3,z4,z6,z140]),(0,[z467,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z318,z4,z6])],[(0,[z468,z1,z2,z7,z3,z4,z6]),(0,[z469,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z470,z4,z6]),(0,[z65,z1,z2,z7,z3,z4,z120]),(0,[z1,z2,z7,z3,z4,z471,z6]),(0,[z1,z2,z7,z472,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z473])],[(0,[z1,z2,z7,z3,z4,z6,z474]),(0,[z1,z2,z7,z3,z378,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z475]),(0,[z1,z67,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z476,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z477,z6]),(0,[z1,z22,z112,z7,z3,z4,z6]),(0,[z1,z2,z7,z478,z3,z4,z6]),(1,[z1,z2,z77,z87,z4,z6])],[(0,[z479,z1,z2,z7,z3,z4,z6]),(0,[z480,z1,z2,z7,z3,z4,z6]),(0,[z481,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z482,z3,z4,z6])],[(0,[z1,z22,z7,z3,z51,z4,z6]),(0,[z1,z7,z3,z3,z33,z4,z6]),(0,[z24,z1,z2,z3,z4,z25,z6]),(0,[z1,z2,z7,z3,z483,z4,z6])]],
   [[(0,[z1,z2,z77,z3,z4,z5,z6]),(0,[z484,z1,z2,z7,z3,z4,z6])],[(0,[z10,z1,z2,z7,z3,z104,z6]),(0,[z1,z2,z7,z235,z3,z4,z6]),(0,[z1,z2,z3,z153,z4,z5,z6])],[(0,[z1,z2,z485,z7,z3,z4,z6]),(0,[z1,z2,z97,z3,z31,z4,z6]),(0,[z1,z2,z3,z31,z4,z186,z6]),(0,[z1,z2,z3,z31,z486,z4,z6]),(0,[z1,z237,z7,z3,z4,z25,z6]),(0,[z1,z2,z7,z3,z4,z6,z487])],[(0,[z189,z1,z7,z3,z33,z4,z6]),(0,[z197,z1,z148,z7,z3,z4,z6]),(0,[z250,z1,z2,z77,z3,z4,z6]),(0,[z1,z488,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z3,z25,z6]),(0,[z1,z2,z489,z7,z3,z4,z6]),(0,[z490,z1,z2,z7,z3,z4,z6]),(0,[z44,z1,z2,z7,z3,z4,z180])],[(0,[z135,z2,z95,z7,z3,z4,z6]),(0,[z0,z2,z99,z7,z3,z4,z6]),(0,[z10,z1,z2,z7,z3,z166,z6]),(0,[z1,z2,z7,z3,z4,z491,z6]),(0,[z1,z149,z2,z7,z3,z4,z140]),(0,[z1,z2,z7,z27,z3,z4,z6])],[(0,[z1,z317,z7,z30,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z492]),(0,[z1,z7,z87,z3,z146,z4,z6])],[(1,[z1,z2,z493,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z494,z6]),(0,[z1,z2,z7,z3,z495,z4,z6]),(0,[z1,z2,z7,z3,z496,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z497])],[(1,[z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z498,z7,z3,z4,z6]),(0,[z499,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z27,z3,z33,z4,z6]),(0,[z24,z1,z2,z3,z31,z4,z6]),(0,[z44,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z500,z4,z6])]],
   [[(0,[z250,z1,z2,z7,z3,z4,z96]),(0,[z24,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z256,z4,z6]),(0,[z1,z2,z143,z3,z31,z4,z6]),(1,[z67,z2,z7,z3,z4,z6])],[(0,[z15,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z501,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z502]),(0,[z109,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z89,z4,z6]),(0,[z1,z2,z7,z3,z4,z42,z180])],[(0,[z135,z2,z99,z7,z3,z4,z6]),(1,[z1,z185,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z503,z6]),(0,[z342,z1,z2,z7,z3,z4,z6]),(1,[z109,z1,z7,z3,z4,z140]),(0,[z1,z2,z40,z3,z31,z4,z6])],[(0,[z1,z2,z77,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z32,z4,z6]),(0,[z1,z2,z196,z143,z3,z4,z6]),(0,[z504,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z6,z423]),(0,[z401,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z505,z6]),(0,[z506,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z507,z3,z4,z6])],[(0,[z508,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z104,z6]),(0,[z1,z2,z7,z3,z4,z6,z509]),(0,[z1,z2,z7,z3,z4,z6,z510])],[(0,[z1,z511,z2,z7,z3,z4,z6]),(0,[z512,z1,z2,z7,z3,z4,z6]),(0,[z197,z1,z22,z7,z3,z4,z6]),(1,[z183,z2,z7,z3,z4,z6]),(1,[z72,z1,z2,z7,z291,z3])],[(0,[z1,z2,z7,z3,z513,z4,z6]),(0,[z1,z2,z514,z7,z3,z4,z6]),(0,[z1,z2,z7,z515,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z28,z6]),(0,[z1,z85,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z25,z6]),(0,[z38,z211,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z516,z4,z6])]],
   [[(0,[z1,z2,z7,z3,z4,z517,z6]),(0,[z108,z148,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z518,z4,z6]),(0,[z76,z1,z2,z7,z3,z166,z6]),(0,[z1,z2,z7,z3,z290,z4,z6]),(0,[z1,z7,z3,z33,z31,z4,z6]),(0,[z1,z22,z114,z7,z3,z4,z6]),(0,[z1,z2,z155,z3,z31,z4,z6]),(0,[z1,z2,z3,z153,z4,z25,z6]),(0,[z1,z2,z7,z3,z162,z4,z6])],[(0,[z1,z22,z7,z3,z4,z519,z6]),(0,[z1,z2,z7,z3,z4,z6,z520]),(0,[z1,z2,z7,z3,z4,z521,z6])],[(0,[z10,z2,z7,z3,z51,z4,z6]),(0,[z522,z1,z2,z7,z3,z4,z6]),(0,[z48,z1,z7,z3,z33,z4,z6]),(0,[z109,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z523,z6]),(0,[z1,z73,z2,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z524,z4,z6])],[(0,[z1,z2,z7,z525,z3,z4,z6]),(0,[z1,z2,z7,z3,z526,z4,z6]),(0,[z1,z52,z7,z3,z33,z4,z6]),(0,[z1,z73,z22,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z4,z167]),(0,[z1,z2,z3,z31,z4,z527,z6]),(0,[z1,z2,z77,z422,z3,z4,z6]),(0,[z1,z2,z7,z3,z25,z6,z42]),(0,[z1,z2,z7,z3,z4,z6,z66])],[(0,[z528,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z529,z4,z6]),(0,[z1,z2,z367,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z530])],[(0,[z108,z1,z2,z3,z31,z4,z6]),(0,[z50,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z143,z3,z4,z6]),(0,[z262,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z6,z180]),(0,[z531,z1,z2,z7,z3,z4,z6]),(0,[z24,z1,z2,z7,z3,z25,z6]),(0,[z1,z2,z7,z3,z4,z6,z532])],[(0,[z533,z1,z2,z7,z3,z4,z6]),(0,[z11,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z534,z7,z3,z4,z6]),(0,[z65,z1,z2,z3,z4,z6,z66]),(0,[z38,z1,z230,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z162,z6,z42])],[(0,[z10,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z535,z3,z4,z6]),(0,[z1,z2,z77,z3,z31,z4,z6]),(0,[z72,z1,z2,z7,z3,z41,z6])]],
   [[(0,[z1,z2,z7,z3,z4,z6,z536]),(0,[z1,z84,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z537,z3,z4,z6]),(0,[z538,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z539,z7,z3,z4,z6]),(0,[z1,z2,z7,z87,z3,z4,z6])],[(0,[z189,z1,z148,z7,z3,z4,z6]),(0,[z1,z394,z2,z95,z3,z4,z6]),(0,[z540,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z541,z3,z4,z6]),(1,[z1,z22,z7,z33,z4,z6]),(0,[z1,z22,z2,z77,z3,z4,z6]),(0,[z199,z1,z2,z7,z3,z4,z6])],[(0,[z542,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z543,z4,z6]),(0,[z1,z2,z3,z31,z41,z4,z6]),(0,[z1,z2,z7,z3,z414,z4,z6]),(0,[z44,z392,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z291,z3,z6])],[(0,[z1,z2,z7,z544,z3,z4,z6]),(0,[z545,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z114,z7,z3,z4,z66]),(0,[z1,z2,z7,z3,z4,z6,z465])],[(0,[z546,z1,z2,z7,z3,z4,z6]),(0,[z1,z547,z2,z7,z3,z4,z6]),(1,[z1,z2,z3,z4,z282,z6]),(0,[z1,z548,z7,z3,z33,z4,z6]),(0,[z1,z7,z3,z549,z33,z4,z6]),(0,[z199,z1,z2,z7,z3,z23,z6]),(0,[z1,z2,z550,z7,z3,z4,z6])],[(0,[z0,z1,z2,z151,z3,z4,z6]),(0,[z1,z2,z7,z3,z551,z4,z6]),(0,[z1,z86,z2,z7,z3,z4,z6]),(0,[z1,z2,z552,z7,z3,z4,z6]),(0,[z1,z110,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z553,z3,z4,z6]),(0,[z108,z135,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z554,z4,z6]),(0,[z1,z2,z3,z166,z4,z282,z6]),(0,[z1,z2,z7,z3,z555,z4,z6]),(0,[z1,z2,z112,z7,z3,z4,z6]),(0,[z144,z1,z2,z7,z3,z4,z6]),(0,[z158,z1,z2,z3,z4,z6,z42])],[(0,[z1,z148,z2,z7,z3,z4,z6]),(0,[z556,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z557,z3,z4,z6]),(0,[z1,z2,z7,z3,z558,z4,z6])]],
   [[(0,[z1,z2,z559,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z49,z4,z6]),(0,[z1,z2,z77,z7,z87,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z560])],[(0,[z1,z2,z7,z151,z3,z4,z6]),(0,[z1,z2,z7,z3,z166,z4,z6]),(1,[z1,z84,z97,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z90,z6]),(0,[z1,z2,z7,z3,z313,z4,z6])],[(0,[z1,z2,z99,z77,z3,z4,z6]),(1,[z1,z2,z260,z3,z4,z6]),(0,[z1,z2,z7,z561,z3,z4,z6]),(0,[z76,z1,z2,z3,z31,z4,z6]),(0,[z1,z562,z2,z7,z3,z4,z6]),(0,[z1,z319,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z563,z3,z4,z6]),(0,[z76,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z322,z7,z3,z4,z6]),(1,[z1,z73,z7,z3,z75,z6]),(0,[z1,z2,z7,z3,z4,z527,z6]),(0,[z1,z2,z77,z3,z3,z4,z6]),(0,[z1,z2,z564,z7,z3,z4,z6]),(1,[z1,z319,z7,z3,z4,z6])],[(0,[z189,z1,z22,z7,z3,z4,z6]),(0,[z0,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z565,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z566]),(0,[z1,z2,z7,z3,z4,z6,z567]),(1,[z1,z2,z550,z3,z4,z6]),(0,[z1,z2,z7,z291,z3,z162,z4])],[(0,[z1,z2,z7,z3,z568,z4,z6]),(0,[z1,z2,z7,z3,z4,z569,z6]),(0,[z570,z1,z2,z7,z3,z4,z6]),(0,[z1,z571,z2,z7,z3,z4,z6]),(0,[z572,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z7,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z573,z6])],[(0,[z1,z2,z260,z7,z3,z4,z6]),(0,[z1,z52,z7,z3,z4,z23,z6]),(0,[z48,z1,z2,z270,z3,z4,z6]),(0,[z1,z2,z77,z194,z3,z4,z6]),(0,[z1,z2,z7,z574,z3,z4,z6])],[(0,[z1,z2,z87,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z575])]],
   [[(0,[z1,z148,z7,z3,z33,z4,z6]),(0,[z135,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z576,z6]),(0,[z1,z2,z7,z3,z4,z6,z577])],[(0,[z1,z2,z7,z578,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z579]),(0,[z1,z52,z148,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z6]),(0,[z1,z7,z143,z3,z33,z4,z6]),(0,[z65,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z77,z114,z3,z4,z6])],[(0,[z1,z580,z2,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z4,z102]),(0,[z2,z7,z3,z51,z4,z6,z96]),(0,[z1,z2,z7,z3,z581,z4,z6]),(1,[z1,z2,z80,z3,z4,z6]),(0,[z1,z2,z80,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z582,z4,z6]),(0,[z1,z2,z215,z7,z3,z4,z6]),(0,[z1,z2,z112,z155,z3,z4,z6]),(0,[z1,z22,z7,z3,z153,z4,z6]),(0,[z1,z583,z2,z7,z3,z4,z6]),(0,[z584,z1,z2,z7,z3,z4,z6])],[(0,[z108,z109,z1,z7,z3,z4,z6]),(0,[z1,z2,z7,z585,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z586]),(0,[z1,z7,z40,z3,z33,z4,z6]),(1,[z1,z2,z438,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z209,z6]),(0,[z587,z1,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z3,z162,z6])],[(0,[z588,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z6,z98])],[(0,[z1,z589,z2,z7,z3,z4,z6]),(0,[z590,z1,z2,z7,z3,z4,z6]),(0,[z197,z1,z2,z7,z3,z6,z42]),(0,[z1,z254,z2,z77,z3,z4,z6]),(0,[z24,z1,z2,z155,z3,z4,z6])],[(0,[z1,z148,z7,z3,z75,z4,z6]),(0,[z2,z7,z3,z4,z120,z6,z96]),(0,[z1,z591,z2,z7,z3,z4,z6]),(0,[z592,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z593,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z594,z6]),(0,[z158,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z595,z4,z6]),(0,[z1,z350,z2,z7,z3,z4,z6]),(0,[z72,z1,z2,z7,z3,z6,z39]),(0,[z596,z1,z2,z7,z3,z4,z6])]],
   [[(0,[z2,z99,z7,z3,z4,z6,z96]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z197,z1,z2,z7,z3,z186,z6]),(1,[z1,z149,z7,z3,z4,z23]),(0,[z1,z2,z7,z3,z4,z597,z6]),(1,[z1,z2,z3,z31,z4,z6]),(0,[z44,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z3,z31,z4,z25,z6]),(0,[z1,z598,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z28,z6])],[(0,[z1,z2,z599,z7,z3,z4,z6]),(0,[z0,z15,z2,z7,z3,z4,z6]),(1,[z1,z22,z7,z3,z4,z6]),(0,[z44,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z176,z3,z4,z6]),(0,[z1,z2,z114,z7,z3,z4,z6]),(1,[z1,z7,z115,z3,z4,z6]),(0,[z1,z2,z600,z40,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z519,z6]),(0,[z1,z2,z3,z31,z75,z4,z6]),(0,[z109,z1,z2,z3,z31,z4,z6]),(0,[z109,z1,z2,z7,z3,z4,z42]),(0,[z1,z2,z77,z291,z3,z4,z6])],[(0,[z601,z1,z2,z7,z3,z4,z6]),(1,[z1,z298,z7,z3,z4,z6]),(0,[z1,z22,z7,z602,z3,z4,z6]),(0,[z109,z1,z22,z7,z3,z4,z6]),(0,[z109,z1,z2,z7,z291,z3,z4]),(1,[z1,z2,z155,z3,z153,z6]),(0,[z1,z2,z7,z3,z4,z6,z603]),(0,[z1,z2,z7,z3,z4,z6,z604])],[(0,[z605,z1,z2,z7,z3,z4,z6]),(0,[z48,z1,z2,z7,z33,z4,z6]),(0,[z1,z7,z3,z33,z4,z6,z39]),(0,[z1,z22,z7,z3,z4,z523,z6]),(0,[z1,z22,z7,z3,z4,z186,z6]),(0,[z1,z2,z7,z3,z4,z6,z606]),(0,[z1,z357,z2,z7,z3,z4,z6]),(0,[z214,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z607,z4,z6]),(0,[z38,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z600,z7,z3,z4,z6]),(0,[z1,z2,z174,z27,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z608]),(0,[z1,z2,z609,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z610,z4,z6]),(0,[z1,z2,z155,z97,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z167]),(0,[z1,z2,z7,z40,z41,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z611])],[(0,[z250,z2,z7,z3,z4,z6,z96]),(0,[z1,z7,z97,z3,z4,z23,z6]),(0,[z1,z2,z7,z3,z4,z6,z612]),(1,[z1,z2,z168,z3,z4,z6]),(0,[z2,z7,z3,z4,z5,z6,z432])],[(0,[z1,z22,z95,z7,z3,z4,z6]),(0,[z1,z2,z7,z613,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z614])]],
   [[(0,[z1,z2,z7,z3,z119,z4,z6]),(0,[z615,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z616,z6]),(0,[z211,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z82,z6]),(0,[z1,z2,z7,z3,z4,z6,z617]),(0,[z1,z2,z7,z3,z162,z4,z42])],[(0,[z1,z22,z7,z87,z3,z4,z6]),(0,[z1,z2,z54,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z618]),(0,[z619,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z620])],[(0,[z1,z2,z77,z3,z4,z6,z96]),(0,[z1,z2,z77,z3,z4,z6,z39]),(0,[z621,z1,z2,z7,z3,z4,z6]),(1,[z2,z7,z3,z4,z6,z432])],[(0,[z622,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z291,z3,z4,z120]),(0,[z1,z2,z7,z3,z146,z4,z6])],[(0,[z76,z10,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z623,z4,z6]),(0,[z38,z1,z7,z3,z33,z4,z6]),(0,[z624,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z625,z3,z4,z6]),(0,[z48,z1,z2,z7,z143,z4,z6]),(0,[z1,z22,z7,z40,z3,z4,z6])],[(0,[z1,z16,z2,z7,z3,z4,z6]),(0,[z626,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z30,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z104,z6]),(0,[z250,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z112,z3,z4,z25,z6]),(0,[z1,z2,z3,z31,z4,z23,z6])]],
   [[(0,[z1,z7,z3,z4,z23,z6,z140]),(0,[z1,z2,z7,z3,z4,z6,z327]),(0,[z1,z7,z3,z4,z221,z25,z6]),(0,[z1,z2,z7,z3,z4,z627,z6])],[(0,[z0,z1,z2,z7,z3,z4,z423]),(0,[z1,z2,z7,z628,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z120,z6]),(0,[z1,z2,z7,z3,z4,z6,z629])],[(0,[z0,z1,z52,z2,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z630,z6]),(0,[z631,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z143,z3,z256,z4,z6]),(0,[z1,z149,z2,z113,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z6,z42]),(0,[z1,z2,z7,z3,z632,z4,z6]),(0,[z1,z2,z7,z633,z3,z4,z6]),(0,[z38,z1,z350,z7,z3,z4,z6])],[(0,[z1,z22,z7,z151,z3,z4,z6]),(0,[z1,z22,z7,z3,z166,z4,z6]),(0,[z1,z634,z2,z7,z3,z4,z6]),(0,[z109,z1,z7,z97,z3,z4,z6]),(0,[z1,z2,z114,z3,z4,z5,z6]),(0,[z1,z2,z7,z27,z3,z4,z180])],[(0,[z1,z2,z7,z3,z53,z4,z6])],[(0,[z1,z77,z7,z3,z33,z4,z6]),(0,[z109,z1,z149,z7,z3,z4,z6]),(0,[z106,z1,z2,z77,z3,z4,z6]),(0,[z311,z1,z2,z7,z3,z4,z6])],[(0,[z1,z185,z2,z7,z3,z4,z6]),(0,[z1,z112,z7,z3,z75,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z635])],[(0,[z15,z1,z2,z151,z3,z4,z6]),(0,[z636,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z112,z3,z31,z4,z6]),(0,[z1,z7,z3,z33,z4,z6,z492]),(0,[z1,z22,z7,z3,z4,z6,z180]),(0,[z1,z149,z2,z77,z3,z4,z6]),(1,[z1,z396,z7,z3,z4,z6])]],
   [[(0,[z1,z2,z7,z3,z637,z4,z6]),(0,[z250,z1,z7,z3,z33,z4,z6]),(0,[z106,z1,z100,z7,z3,z4,z6]),(0,[z1,z2,z7,z638,z3,z4,z6])],[(0,[z11,z2,z7,z3,z4,z6,z96]),(0,[z197,z1,z112,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z6,z639]),(0,[z1,z2,z3,z31,z4,z6,z205])],[(0,[z1,z2,z640,z7,z3,z4,z6]),(1,[z1,z255,z7,z3,z4,z6]),(0,[z197,z1,z2,z438,z3,z4,z6]),(0,[z1,z2,z3,z31,z208,z4,z6]),(0,[z1,z2,z7,z3,z153,z4,z6]),(1,[z1,z2,z231,z3,z4,z6]),(0,[z44,z1,z2,z231,z3,z4,z6]),(0,[z1,z641,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z4,z6]),(0,[z48,z1,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z41,z4,z6]),(0,[z1,z7,z27,z3,z500,z4,z6])],[(0,[z11,z2,z7,z30,z3,z4,z6]),(0,[z1,z52,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z642,z3,z4,z6]),(0,[z72,z1,z2,z77,z3,z4,z6])],[(0,[z2,z7,z30,z3,z51,z4,z6]),(0,[z1,z2,z7,z3,z643,z4,z6]),(0,[z1,z2,z7,z644,z3,z4,z6]),(0,[z65,z1,z2,z3,z153,z4,z6]),(0,[z1,z645,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z449,z4,z6])],[(0,[z1,z646,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z203,z6]),(0,[z333,z1,z2,z77,z3,z4,z6]),(0,[z65,z1,z2,z7,z3,z4,z66]),(0,[z1,z2,z7,z3,z4,z647,z6])]],
   [[(0,[z50,z1,z2,z493,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z42,z96]),(0,[z1,z2,z7,z3,z549,z4,z6]),(0,[z197,z1,z2,z3,z31,z4,z6])],[(0,[z648,z1,z2,z7,z3,z4,z6]),(0,[z50,z1,z2,z7,z3,z4,z6]),(1,[z1,z2,z7,z3,z4,z195]),(0,[z649,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z153,z6,z42]),(0,[z38,z1,z2,z550,z3,z4,z6])],[(0,[z0,z1,z84,z2,z3,z4,z6]),(0,[z11,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z290,z4,z6]),(0,[z1,z7,z3,z33,z162,z4,z6]),(0,[z183,z2,z7,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z6,z650]),(0,[z1,z2,z7,z3,z4,z6,z42])],[(0,[z1,z2,z7,z3,z651,z4,z6]),(0,[z1,z160,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z652,z3,z4,z6])],[(0,[z1,z583,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z602,z3,z4,z6])],[(0,[z1,z2,z7,z3,z486,z4,z6]),(0,[z1,z7,z3,z33,z4,z6,z66]),(0,[z1,z2,z7,z3,z4,z186,z6]),(0,[z38,z1,z2,z7,z40,z4,z6]),(1,[z1,z7,z3,z500,z4,z6]),(0,[z1,z2,z7,z3,z4,z147,z6])],[(0,[z1,z2,z7,z3,z653,z4,z6]),(0,[z654,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z655,z4,z6]),(0,[z10,z2,z7,z3,z166,z4,z6]),(0,[z1,z548,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z6,z42,z39])],[(0,[z1,z52,z2,z112,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z6,z140]),(0,[z262,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z656])]],
   [[(0,[z1,z2,z95,z7,z3,z4,z6]),(0,[z0,z1,z2,z99,z3,z4,z6]),(0,[z1,z7,z3,z4,z203,z6,z96]),(0,[z1,z396,z114,z7,z3,z4,z6]),(0,[z1,z2,z230,z7,z3,z4,z6])],[(0,[z657,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z658,z4,z6]),(0,[z10,z1,z2,z3,z31,z4,z6]),(0,[z1,z2,z3,z4,z58,z6,z96]),(1,[z1,z77,z3,z33,z4,z6]),(0,[z1,z2,z77,z3,z162,z4,z6]),(0,[z1,z659,z2,z7,z3,z4,z6]),(0,[z1,z660,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z28,z42])],[(0,[z1,z394,z2,z7,z3,z4,z6]),(0,[z50,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z661,z4,z6]),(0,[z1,z84,z2,z3,z31,z4,z6]),(1,[z1,z22,z3,z31,z4,z6]),(1,[z1,z357,z7,z3,z4,z6]),(0,[z1,z2,z114,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z239,z4,z6])],[(0,[z11,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z413,z6]),(0,[z1,z662,z2,z7,z3,z4,z6]),(0,[z1,z7,z291,z3,z33,z4,z6]),(0,[z123,z1,z2,z7,z3,z4,z6])],[(0,[z50,z1,z2,z7,z3,z4,z334]),(0,[z1,z2,z3,z31,z4,z6,z96]),(1,[z1,z2,z141,z3,z4,z6]),(0,[z1,z2,z3,z4,z62,z6,z42])],[(0,[z663,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z664]),(0,[z1,z2,z7,z3,z4,z665,z6]),(0,[z1,z2,z7,z3,z4,z666,z6]),(0,[z1,z2,z40,z3,z313,z4,z6]),(1,[z392,z2,z7,z3,z4,z6]),(1,[z170,z1,z7,z3,z4,z6])],[(0,[z1,z95,z7,z3,z33,z4,z6]),(0,[z0,z1,z2,z7,z3,z4,z6]),(1,[z1,z7,z3,z518,z4,z6]),(1,[z76,z2,z7,z3,z104,z6]),(0,[z76,z2,z7,z3,z4,z104,z6]),(0,[z1,z367,z7,z3,z33,z4,z6]),(0,[z1,z22,z232,z7,z3,z4,z6]),(0,[z38,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z77,z143,z3,z4,z6]),(1,[z1,z2,z7,z74,z3,z4]),(0,[z1,z2,z7,z667,z3,z4,z6]),(0,[z1,z2,z7,z668,z3,z4,z6])],[(0,[z669,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z551,z4,z6]),(0,[z1,z2,z7,z3,z4,z670,z6]),(0,[z1,z2,z7,z3,z4,z236,z6]),(0,[z24,z1,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z40,z3,z4,z6]),(0,[z1,z2,z7,z3,z671,z4,z6])]],
   [[(0,[z672,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z104,z6]),(0,[z1,z2,z7,z3,z4,z6,z673])],[(0,[z1,z2,z7,z493,z3,z4,z6]),(0,[z1,z674,z2,z7,z3,z4,z6]),(0,[z135,z2,z7,z3,z4,z120,z6]),(0,[z675,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z402,z7,z3,z4,z6]),(0,[z676,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z7,z3,z4,z6]),(0,[z1,z2,z677,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z120,z6]),(0,[z678,z1,z2,z7,z3,z4,z6]),(0,[z1,z114,z7,z3,z33,z4,z6]),(0,[z1,z22,z7,z3,z4,z25,z6])],[(0,[z148,z2,z95,z7,z3,z4,z6]),(0,[z1,z2,z47,z7,z3,z4,z6]),(0,[z1,z679,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z166,z4,z6]),(0,[z1,z680,z2,z7,z3,z4,z6]),(1,[z1,z2,z235,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z681])],[(0,[z1,z95,z7,z3,z75,z4,z6]),(0,[z135,z1,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z75,z4,z6]),(0,[z1,z2,z3,z31,z4,z5,z6])],[(0,[z682,z1,z2,z7,z3,z4,z6]),(0,[z65,z1,z2,z7,z3,z4,z6]),(0,[z683,z1,z2,z7,z3,z4,z6]),(1,[z660,z2,z7,z3,z4,z6]),(0,[z44,z660,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z684,z3,z4,z6])],[(0,[z189,z1,z2,z3,z31,z4,z6]),(0,[z1,z685,z2,z7,z3,z4,z6]),(0,[z686,z1,z2,z7,z3,z4,z6]),(0,[z1,z7,z97,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z687,z4,z6]),(0,[z1,z2,z27,z3,z449,z4,z6])],[(0,[z1,z7,z30,z3,z518,z4,z6]),(0,[z1,z2,z7,z688,z3,z4,z6]),(0,[z1,z2,z7,z689,z3,z4,z6])]],
   [[(0,[z65,z15,z1,z2,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z690]),(0,[z109,z197,z1,z7,z3,z4,z6]),(0,[z691,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z155,z77,z3,z4,z6]),(0,[z692,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z6,z180])],[(0,[z1,z2,z7,z3,z693,z4,z6]),(0,[z1,z2,z425,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z51,z4,z6]),(0,[z76,z1,z2,z7,z3,z4,z57]),(0,[z250,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z694,z6]),(0,[z1,z2,z7,z3,z23,z6,z105]),(0,[z38,z1,z2,z7,z3,z4,z465])],[(0,[z1,z2,z7,z3,z695,z4,z6]),(0,[z0,z1,z2,z155,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z6,z577]),(0,[z1,z73,z2,z77,z3,z4,z6]),(1,[z1,z2,z7,z3,z318,z6])],[(0,[z1,z2,z696,z7,z3,z4,z6]),(0,[z697,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z698,z4,z6]),(0,[z1,z84,z7,z97,z3,z4,z6]),(1,[z1,z2,z600,z3,z4,z6]),(1,[z1,z552,z7,z3,z4,z6]),(0,[z44,z1,z552,z7,z3,z4,z6])],[(0,[z15,z1,z52,z2,z3,z4,z6]),(0,[z699,z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z166,z41,z6]),(0,[z631,z1,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z700,z6])],[(0,[z108,z1,z2,z77,z3,z4,z6]),(0,[z135,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z41,z4,z6]),(0,[z701,z1,z2,z7,z3,z4,z6])],[(0,[z702,z1,z2,z7,z3,z4,z6]),(0,[z10,z1,z2,z77,z3,z4,z6]),(0,[z65,z1,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z703,z4,z6]),(0,[z704,z1,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z291,z3,z4,z96]),(0,[z65,z1,z2,z112,z3,z4,z6]),(1,[z197,z1,z7,z3,z186,z6]),(0,[z1,z2,z7,z3,z705,z4,z6]),(0,[z1,z2,z77,z77,z3,z4,z6]),(0,[z1,z706,z2,z7,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z7,z3,z707,z6]),(0,[z1,z580,z7,z33,z4,z6]),(0,[z1,z7,z3,z4,z708,z423]),(0,[z72,z1,z22,z7,z291,z3])],[(0,[z1,z7,z3,z33,z119,z6]),(0,[z1,z3,z31,z4,z203,z6]),(0,[z1,z7,z515,z3,z4,z23]),(0,[z286,z1,z7,z3,z4,z140]),(0,[z1,z2,z7,z3,z157,z6])],[(0,[z1,z7,z3,z709,z4,z6]),(0,[z1,z7,z710,z3,z4,z6]),(0,[z1,z7,z3,z4,z711,z6]),(0,[z1,z712,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z713]),(0,[z1,z714,z7,z3,z4,z6]),(0,[z1,z2,z715,z3,z4,z6]),(0,[z1,z7,z3,z33,z127,z6]),(0,[z1,z2,z7,z3,z4,z716]),(0,[z1,z717,z7,z3,z4,z6]),(0,[z1,z2,z718,z3,z4,z6])],[(0,[z1,z2,z7,z719,z4,z6]),(0,[z1,z2,z155,z3,z89,z6])],[(0,[z1,z298,z260,z3,z4,z6]),(0,[z250,z2,z3,z31,z4,z96]),(0,[z1,z7,z3,z4,z23,z720]),(0,[z1,z2,z141,z3,z4,z465])],[(0,[z1,z2,z698,z31,z4,z6])],[(0,[z1,z2,z77,z3,z4,z334]),(0,[z1,z2,z3,z4,z721,z6]),(0,[z135,z2,z77,z3,z4,z120]),(0,[z1,z2,z7,z722,z4,z6]),(0,[z723,z2,z7,z3,z4,z6]),(0,[z1,z3,z31,z4,z147,z6])],[(0,[z1,z2,z3,z724,z4,z6]),(0,[z1,z2,z3,z725,z4,z6]),(0,[z38,z67,z2,z7,z6,z39]),(0,[z1,z2,z3,z4,z726,z6])],[(0,[z11,z2,z7,z3,z4,z334]),(0,[z1,z2,z3,z727,z4,z6]),(0,[z1,z2,z7,z3,z705,z42]),(0,[z1,z110,z174,z3,z4,z6])],[(0,[z108,z7,z3,z200,z4,z6]),(0,[z1,z2,z7,z3,z4,z728]),(0,[z1,z729,z7,z3,z4,z6])],[(0,[z1,z22,z7,z3,z4,z102]),(0,[z1,z185,z7,z3,z4,z195]),(1,[z2,z7,z730,z4,z6]),(0,[z123,z1,z2,z3,z25,z6])],[(0,[z189,z394,z95,z3,z4,z6]),(0,[z65,z15,z2,z3,z4,z96]),(0,[z1,z7,z557,z33,z4,z6]),(0,[z1,z7,z3,z33,z162,z42]),(0,[z1,z22,z438,z3,z4,z6]),(0,[z1,z2,z550,z3,z4,z83])],[],[(0,[z1,z2,z7,z3,z4,z731]),(0,[z1,z22,z7,z3,z9,z6])],[(0,[z1,z659,z97,z3,z4,z6]),(0,[z1,z732,z7,z3,z4,z6])]],
   [[(0,[z165,z2,z7,z3,z4,z96]),(0,[z1,z77,z3,z33,z4,z6]),(0,[z1,z438,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z733]),(0,[z1,z2,z734,z3,z4,z6])],[(0,[z2,z7,z3,z4,z735,z6])],[(0,[z1,z2,z7,z3,z4,z736]),(0,[z1,z2,z77,z638,z4,z6])],[(0,[z15,z2,z403,z3,z4,z6]),(0,[z1,z298,z3,z31,z4,z6]),(0,[z1,z737,z2,z3,z4,z6])],[(0,[z1,z94,z3,z75,z4,z6]),(0,[z1,z22,z155,z3,z153,z6]),(0,[z1,z2,z77,z3,z90,z6]),(0,[z1,z2,z7,z3,z738,z6])],[(0,[z72,z1,z7,z291,z3,z33]),(0,[z401,z1,z7,z3,z4,z227]),(0,[z1,z22,z3,z4,z62,z6]),(0,[z1,z739,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z740])],[(0,[z302,z2,z7,z3,z104,z6]),(0,[z1,z2,z7,z4,z6,z741]),(0,[z1,z2,z710,z3,z4,z6]),(0,[z1,z149,z168,z3,z4,z23]),(0,[z1,z7,z3,z742,z4,z6])],[(0,[z1,z2,z3,z4,z743,z6]),(1,[z1,z2,z3,z4,z740])],[(0,[z1,z2,z7,z3,z4,z744]),(0,[z1,z264,z112,z3,z4,z6]),(0,[z1,z2,z745,z3,z4,z6]),(0,[z1,z2,z746,z3,z4,z6])],[(0,[z255,z95,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z90,z96]),(0,[z1,z22,z7,z3,z4,z83]),(0,[z1,z2,z3,z747,z4,z6])],[(0,[z250,z2,z77,z3,z4,z96]),(0,[z1,z2,z235,z3,z4,z6]),(0,[z1,z7,z3,z748,z4,z6]),(0,[z158,z1,z2,z3,z90,z6])],[(0,[z749,z2,z3,z31,z4,z6]),(0,[z1,z7,z750,z3,z4,z6])],[(0,[z660,z2,z7,z3,z4,z6]),(0,[z1,z237,z7,z3,z4,z6]),(0,[z751,z1,z7,z3,z33,z4]),(0,[z211,z7,z3,z33,z4,z6]),(0,[z1,z752,z3,z33,z4,z6])],[(0,[z1,z2,z7,z753,z4,z6]),(0,[z1,z7,z3,z4,z708,z6])],[(0,[z1,z7,z3,z754,z4,z6])],[(0,[z1,z2,z755,z3,z4,z6]),(0,[z182,z7,z3,z33,z4,z6])]],
   [[(0,[z109,z1,z7,z3,z4,z502]),(0,[z1,z2,z7,z4,z6,z756])],[(0,[z1,z2,z3,z256,z4,z6]),(0,[z1,z2,z77,z3,z757,z6]),(0,[z211,z350,z7,z3,z4,z6])],[(0,[z1,z2,z77,z3,z4,z423]),(0,[z1,z22,z7,z3,z119,z6]),(0,[z1,z2,z758,z3,z4,z6]),(0,[z67,z2,z7,z3,z6,z39])],[(0,[z1,z2,z260,z3,z4,z195]),(0,[z1,z759,z7,z3,z4,z6]),(0,[z342,z7,z3,z263,z4,z6]),(0,[z24,z1,z237,z3,z25,z6])],[(0,[z1,z52,z244,z3,z4,z6]),(0,[z1,z114,z115,z3,z4,z5]),(0,[z1,z2,z7,z27,z4,z756])],[(0,[z1,z2,z7,z3,z760,z6]),(0,[z106,z1,z33,z31,z4,z6]),(0,[z1,z3,z239,z31,z4,z6])],[(0,[z197,z1,z7,z3,z186,z6]),(0,[z197,z1,z7,z3,z147,z6]),(0,[z1,z2,z7,z3,z761,z6]),(0,[z1,z7,z3,z4,z6,z762])],[],[(0,[z1,z763,z7,z3,z4,z6]),(0,[z1,z16,z77,z3,z4,z6]),(0,[z65,z1,z2,z3,z4,z423]),(0,[z1,z764,z7,z3,z4,z6]),(0,[z1,z2,z765,z3,z4,z6]),(0,[z1,z2,z3,z766,z31,z4]),(0,[z24,z1,z2,z3,z25,z6])],[(0,[z767,z1,z7,z3,z4,z6]),(0,[z768,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z769,z4,z6])],[(0,[z391,z2,z7,z3,z104,z6]),(0,[z770,z1,z7,z3,z4,z6]),(0,[z38,z1,z2,z7,z6,z39])],[(0,[z1,z2,z7,z3,z4,z771]),(0,[z1,z255,z7,z3,z4,z42]),(0,[z1,z7,z625,z33,z4,z6]),(0,[z214,z2,z3,z486,z4,z6]),(0,[z44,z1,z2,z7,z157,z180])],[(0,[z1,z2,z77,z3,z4,z413]),(0,[z1,z255,z7,z291,z3,z4]),(0,[z1,z2,z7,z3,z4,z720]),(0,[z1,z2,z7,z3,z772,z6]),(0,[z1,z77,z3,z4,z773,z6])],[(0,[z1,z2,z7,z3,z4,z774]),(0,[z1,z2,z775,z3,z4,z6]),(0,[z1,z2,z3,z776,z4,z6])],[(0,[z1,z2,z777,z3,z4,z6]),(0,[z778,z2,z7,z3,z4,z6])],[(0,[z1,z215,z7,z3,z4,z6]),(0,[z250,z2,z7,z3,z4,z779]),(0,[z38,z1,z350,z7,z6,z39]),(0,[z1,z7,z40,z239,z41,z6])]],
   [[(0,[z2,z7,z3,z4,z416,z96]),(0,[z48,z1,z270,z33,z4,z6]),(0,[z211,z2,z550,z3,z4,z6])],[(0,[z1,z2,z3,z780,z4,z6]),(0,[z1,z2,z3,z31,z4,z195]),(0,[z1,z2,z781,z3,z4,z6]),(0,[z1,z2,z77,z3,z6,z105]),(0,[z183,z2,z3,z31,z4,z6]),(0,[z1,z2,z77,z3,z4,z465])],[(0,[z1,z2,z7,z3,z4,z782]),(0,[z222,z232,z7,z3,z4,z6]),(0,[z783,z1,z2,z3,z4,z6]),(0,[z1,z7,z3,z784,z4,z6])],[(0,[z1,z2,z785,z3,z4,z6]),(0,[z67,z2,z7,z3,z4,z83])],[(0,[z1,z298,z7,z3,z4,z195]),(0,[z1,z2,z7,z786,z4,z6]),(0,[z1,z787,z2,z3,z4,z6])],[(0,[z1,z2,z788,z3,z4,z6]),(0,[z649,z1,z2,z7,z4,z180]),(0,[z1,z2,z7,z3,z789,z4]),(0,[z1,z7,z638,z33,z4,z6]),(0,[z461,z1,z7,z33,z4,z6])],[(0,[z1,z2,z790,z3,z4,z6]),(0,[z1,z22,z7,z295,z4,z6]),(0,[z303,z1,z2,z3,z4,z6]),(0,[z2,z99,z3,z4,z58,z6]),(0,[z2,z434,z7,z3,z4,z96]),(0,[z791,z2,z7,z3,z4,z6])],[(0,[z1,z7,z3,z33,z4,z57]),(0,[z1,z230,z550,z3,z4,z6])],[(0,[z1,z7,z3,z792,z4,z6]),(0,[z1,z7,z3,z4,z793,z6]),(0,[z1,z2,z77,z3,z794,z6])],[(0,[z1,z84,z602,z3,z4,z6]),(0,[z1,z2,z795,z3,z4,z6]),(0,[z481,z1,z2,z31,z4,z6]),(0,[z1,z2,z7,z3,z127,z180])],[(0,[z1,z2,z7,z3,z796,z6]),(0,[z1,z2,z7,z3,z797,z6]),(0,[z1,z7,z642,z33,z4,z6]),(0,[z1,z357,z3,z31,z4,z6])],[(0,[z1,z798,z7,z3,z4,z6]),(0,[z799,z2,z7,z3,z4,z6]),(0,[z197,z182,z7,z3,z4,z6]),(0,[z1,z7,z3,z75,z711,z6]),(0,[z2,z77,z3,z4,z6,z432])],[(0,[z1,z84,z194,z3,z4,z6]),(0,[z2,z7,z3,z4,z800,z6])],[(0,[z1,z2,z7,z801,z3,z4]),(0,[z1,z2,z7,z3,z802,z6]),(0,[z50,z2,z7,z730,z4,z6]),(0,[z803,z2,z7,z3,z4,z6]),(0,[z804,z2,z7,z3,z4,z6])],[(0,[z1,z550,z3,z33,z4,z6]),(0,[z1,z7,z33,z4,z6,z606]),(0,[z1,z2,z3,z31,z4,z805]),(0,[z1,z806,z7,z3,z4,z6])],[(0,[z1,z2,z77,z3,z4,z6]),(0,[z1,z84,z47,z3,z4,z6]),(0,[z1,z2,z7,z3,z807,z6]),(0,[z76,z22,z7,z3,z104,z6])]],
   [[(0,[z590,z1,z2,z31,z4,z6]),(0,[z1,z2,z3,z808,z4,z6]),(0,[z1,z7,z809,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z810]),(0,[z811,z2,z7,z3,z4,z6]),(0,[z170,z1,z3,z4,z62,z6])],[(0,[z1,z185,z77,z3,z4,z6]),(0,[z1,z100,z7,z3,z4,z6]),(0,[z109,z1,z77,z3,z4,z140]),(0,[z770,z1,z7,z3,z90,z6])],[(0,[z1,z115,z3,z4,z5,z6])],[(0,[z47,z7,z3,z4,z6,z96]),(0,[z1,z2,z812,z3,z4,z6]),(0,[z24,z1,z2,z3,z209,z6])],[(0,[z660,z2,z3,z31,z4,z6]),(0,[z158,z1,z2,z3,z4,z6]),(0,[z813,z1,z2,z3,z4,z6])],[(0,[z1,z73,z3,z31,z75,z6]),(0,[z1,z2,z3,z814,z4,z6]),(0,[z1,z319,z3,z31,z4,z6]),(0,[z183,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z815]),(0,[z1,z319,z7,z40,z41,z6])],[(0,[z1,z280,z7,z3,z4,z6]),(0,[z1,z816,z2,z3,z4,z6]),(0,[z2,z99,z7,z3,z4,z423]),(0,[z11,z2,z7,z585,z4,z6]),(0,[z817,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z818,z4,z6])],[(0,[z1,z2,z819,z3,z4,z6]),(0,[z1,z149,z2,z7,z3,z105])],[(0,[z1,z394,z3,z33,z4,z6]),(1,[z2,z820,z3,z4,z6]),(0,[z1,z254,z602,z3,z4,z6]),(0,[z1,z2,z821,z3,z4,z6]),(0,[z1,z2,z7,z3,z822,z6]),(1,[z1,z7,z3,z711,z6])],[(0,[z108,z182,z7,z3,z4,z6]),(0,[z15,z2,z820,z3,z4,z6]),(0,[z1,z2,z3,z31,z318,z6])],[(0,[z1,z464,z97,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z167]),(0,[z1,z2,z174,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z823]),(0,[z542,z2,z7,z51,z4,z6]),(0,[z1,z2,z824,z3,z4,z6]),(0,[z135,z7,z3,z33,z4,z120]),(0,[z1,z22,z600,z3,z4,z6]),(0,[z1,z22,z196,z3,z4,z6]),(0,[z109,z1,z7,z3,z4,z167]),(0,[z1,z7,z3,z825,z4,z6])],[(0,[z1,z2,z40,z313,z41,z6])],[(0,[z11,z2,z30,z88,z4,z6]),(0,[z1,z826,z3,z33,z4,z6])],[(0,[z1,z827,z2,z3,z4,z6]),(0,[z1,z828,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z829]),(0,[z1,z357,z77,z3,z4,z6])]],
   [[(0,[z572,z95,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z830]),(0,[z1,z22,z7,z3,z6,z831]),(0,[z1,z832,z7,z3,z4,z6]),(0,[z1,z833,z7,z3,z4,z6]),(0,[z1,z2,z114,z3,z4,z740]),(0,[z392,z2,z7,z3,z127,z6]),(0,[z1,z2,z7,z507,z4,z28])],[(0,[z72,z1,z237,z7,z3,z6]),(0,[z1,z834,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z835]),(0,[z1,z2,z836,z3,z4,z6]),(0,[z65,z1,z2,z3,z4,z71]),(0,[z1,z86,z7,z3,z4,z6]),(0,[z1,z22,z7,z27,z4,z28]),(0,[z199,z1,z2,z7,z3,z6]),(0,[z1,z2,z3,z4,z837,z6])],[(0,[z1,z7,z3,z4,z6,z838]),(0,[z839,z22,z7,z3,z4,z6]),(0,[z1,z840,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z203,z6]),(0,[z1,z7,z3,z4,z23,z579]),(0,[z1,z7,z3,z4,z841,z6]),(0,[z1,z842,z7,z3,z4,z6])],[(0,[z1,z2,z3,z31,z772,z6]),(0,[z1,z3,z31,z4,z221,z6])],[(0,[z1,z2,z7,z3,z6,z843]),(0,[z1,z2,z7,z3,z4,z844]),(0,[z1,z600,z3,z33,z4,z6]),(0,[z106,z1,z2,z31,z4,z6])],[(0,[z1,z7,z845,z3,z4,z6]),(0,[z846,z7,z3,z33,z4,z6])],[(0,[z1,z22,z7,z3,z4,z57])],[(0,[z2,z3,z4,z58,z6,z432]),(0,[z48,z1,z33,z31,z4,z6]),(0,[z1,z7,z3,z33,z90,z6]),(0,[z1,z2,z3,z49,z153,z6])],[(0,[z189,z847,z7,z3,z4,z6]),(0,[z11,z317,z7,z30,z4,z6]),(0,[z1,z7,z3,z4,z147,z6]),(0,[z1,z848,z77,z3,z4,z6])],[(0,[z1,z73,z77,z3,z75,z6]),(0,[z1,z319,z77,z3,z4,z6]),(0,[z65,z1,z115,z3,z4,z6])],[(0,[z1,z94,z2,z3,z4,z6]),(0,[z286,z1,z7,z3,z4,z492]),(0,[z65,z1,z2,z3,z4,z327]),(0,[z1,z2,z3,z849,z25,z6])],[(0,[z1,z2,z7,z3,z4,z850]),(0,[z11,z22,z7,z30,z4,z6]),(0,[z65,z1,z2,z3,z4,z629]),(0,[z1,z7,z851,z3,z4,z6])],[(0,[z1,z2,z852,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z853]),(0,[z67,z230,z7,z3,z4,z6])],[(0,[z1,z2,z854,z3,z4,z6])]],
   [[(0,[z855,z1,z7,z3,z4,z6]),(0,[z856,z1,z2,z3,z4,z6]),(0,[z1,z857,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z6,z858]),(0,[z660,z2,z231,z3,z4,z6]),(0,[z1,z7,z3,z859,z4,z6])],[(0,[z1,z2,z7,z3,z495,z42]),(0,[z860,z2,z7,z3,z4,z6]),(0,[z1,z861,z7,z3,z4,z6])],[(0,[z1,z2,z862,z3,z4,z6]),(0,[z197,z1,z2,z7,z3,z167]),(0,[z2,z7,z863,z3,z4,z6]),(0,[z1,z2,z7,z4,z756,z180])],[(0,[z24,z1,z22,z3,z25,z6])],[(0,[z1,z2,z3,z529,z25,z6]),(0,[z1,z22,z3,z313,z4,z6]),(0,[z1,z22,z113,z3,z4,z6]),(0,[z1,z864,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z865,z6]),(0,[z1,z2,z866,z3,z4,z6]),(0,[z1,z2,z3,z867,z4,z6]),(0,[z1,z237,z7,z3,z6,z42]),(0,[z38,z1,z2,z7,z465,z39])],[(0,[z1,z7,z3,z4,z147,z167]),(0,[z2,z3,z31,z4,z6,z868]),(0,[z869,z1,z7,z3,z4,z6])],[(0,[z1,z870,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z423]),(0,[z1,z22,z7,z3,z127,z6]),(0,[z1,z2,z7,z3,z871,z4])],[(0,[z1,z47,z7,z3,z4,z6]),(0,[z1,z2,z537,z31,z4,z6]),(0,[z872,z1,z2,z7,z3,z6]),(0,[z1,z149,z7,z3,z4,z720]),(0,[z1,z873,z7,z3,z4,z6])],[(1,[z2,z7,z3,z4,z779])],[(0,[z1,z2,z7,z3,z874,z6]),(0,[z1,z875,z7,z3,z4,z6])],[(0,[z1,z876,z2,z3,z4,z6]),(0,[z1,z298,z77,z3,z4,z6]),(0,[z199,z1,z149,z7,z3,z23])],[(0,[z1,z2,z877,z3,z4,z6]),(0,[z328,z2,z7,z3,z4,z96]),(0,[z1,z2,z7,z3,z4,z878]),(0,[z1,z176,z3,z4,z23,z6])],[(0,[z1,z2,z3,z879,z4,z6]),(0,[z135,z22,z7,z3,z4,z120]),(0,[z1,z2,z880,z3,z4,z6]),(0,[z1,z73,z7,z74,z3,z75]),(0,[z1,z2,z3,z31,z157,z6]),(0,[z881,z2,z7,z3,z4,z6])],[(0,[z1,z2,z3,z882,z4,z6])],[(0,[z883,z1,z2,z3,z4,z6]),(0,[z1,z2,z7,z3,z884,z6]),(0,[z261,z7,z3,z33,z4,z6]),(0,[z1,z2,z7,z3,z711,z6]),(0,[z109,z1,z7,z684,z3,z4])]],
   [[(0,[z1,z2,z3,z4,z5,z423]),(0,[z1,z2,z7,z3,z4,z885]),(0,[z1,z22,z7,z3,z162,z42]),(0,[z1,z886,z7,z3,z4,z6]),(0,[z887,z2,z7,z3,z4,z6])],[(0,[z135,z2,z7,z3,z4,z517]),(0,[z1,z2,z888,z3,z4,z6]),(0,[z1,z7,z3,z4,z889,z6]),(0,[z1,z2,z77,z87,z4,z6]),(0,[z44,z660,z2,z7,z4,z180]),(0,[z1,z2,z7,z890,z3,z42])],[(0,[z1,z2,z3,z4,z6,z891]),(0,[z250,z7,z3,z4,z203,z96]),(0,[z1,z7,z74,z3,z33,z4]),(0,[z1,z2,z306,z31,z4,z6]),(0,[z1,z2,z892,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z893]),(0,[z1,z2,z7,z3,z894,z6]),(0,[z631,z148,z7,z3,z4,z6]),(0,[z895,z1,z7,z3,z4,z423])],[(0,[z1,z2,z3,z4,z896,z6]),(0,[z1,z112,z3,z4,z457,z6]),(0,[z1,z22,z176,z3,z4,z6])],[(0,[z50,z22,z7,z51,z4,z6]),(0,[z1,z897,z7,z3,z4,z6])],[(0,[z1,z3,z518,z88,z4,z6]),(0,[z1,z7,z3,z898,z4,z6]),(0,[z1,z7,z3,z33,z4,z465]),(0,[z1,z3,z31,z4,z6,z899]),(0,[z2,z7,z3,z4,z6,z868])],[(0,[z1,z2,z820,z3,z4,z6]),(0,[z0,z99,z3,z33,z4,z6])],[(0,[z108,z7,z3,z4,z6,z510]),(0,[z1,z2,z7,z3,z4,z900]),(0,[z1,z2,z901,z3,z4,z6]),(0,[z392,z552,z7,z3,z4,z6])],[(0,[z902,z1,z2,z7,z3,z4]),(0,[z11,z2,z7,z730,z4,z6]),(0,[z1,z548,z3,z290,z4,z6]),(0,[z44,z392,z2,z7,z4,z180])],[(0,[z545,z148,z7,z3,z4,z6]),(0,[z15,z22,z151,z3,z4,z6]),(0,[z1,z903,z7,z3,z4,z6])],[(0,[z682,z1,z7,z33,z4,z6]),(0,[z1,z112,z710,z3,z4,z6]),(0,[z1,z2,z904,z3,z4,z6]),(0,[z177,z1,z2,z3,z209,z6]),(0,[z1,z350,z7,z3,z4,z465])],[(0,[z1,z7,z3,z905,z4,z6]),(0,[z1,z2,z7,z3,z4,z906]),(0,[z44,z1,z7,z33,z4,z180]),(0,[z1,z7,z161,z33,z4,z6]),(0,[z158,z1,z2,z3,z25,z6])],[(0,[z1,z907,z7,z3,z4,z6])],[(0,[z189,z95,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z908])],[(0,[z1,z7,z3,z711,z186,z6])]],
   [[(0,[z1,z2,z909,z3,z4,z6]),(0,[z1,z910,z7,z3,z4,z6]),(0,[z1,z911,z7,z3,z4,z6]),(0,[z211,z22,z7,z3,z4,z6]),(0,[z158,z1,z22,z3,z4,z6]),(0,[z392,z43,z7,z3,z4,z6])],[(0,[z1,z2,z322,z3,z4,z6]),(0,[z1,z2,z912,z3,z4,z6]),(0,[z1,z913,z2,z3,z4,z6]),(0,[z1,z2,z7,z40,z6,z858])],[(0,[z1,z2,z7,z3,z4,z914]),(0,[z1,z7,z33,z4,z6,z287]),(0,[z182,z2,z7,z3,z4,z42]),(0,[z1,z2,z3,z4,z6,z915])],[(0,[z1,z2,z3,z916,z4,z6]),(0,[z182,z22,z7,z3,z4,z6]),(0,[z182,z2,z7,z291,z3,z4]),(0,[z917,z2,z7,z3,z4,z6])],[(0,[z1,z7,z3,z33,z4,z6]),(0,[z1,z918,z7,z3,z4,z6]),(0,[z199,z1,z2,z77,z3,z6])],[(0,[z76,z2,z7,z3,z104,z57]),(0,[z1,z2,z3,z4,z6,z919]),(0,[z1,z7,z3,z920,z4,z6])],[(0,[z11,z2,z30,z31,z4,z6]),(0,[z1,z2,z7,z921,z3,z4])],[(0,[z922,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z923,z4,z6]),(0,[z211,z2,z7,z3,z4,z83])],[(0,[z342,z95,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z423]),(0,[z1,z237,z3,z31,z4,z6]),(0,[z1,z2,z231,z3,z157,z6])],[(0,[z1,z47,z3,z4,z25,z6]),(0,[z1,z2,z77,z3,z4,z195]),(0,[z1,z924,z7,z3,z4,z6]),(0,[z1,z350,z7,z3,z4,z6]),(0,[z1,z22,z7,z667,z4,z6]),(0,[z1,z2,z609,z3,z153,z6])],[(0,[z925,z1,z7,z3,z4,z6]),(0,[z1,z926,z2,z3,z4,z6]),(0,[z1,z2,z3,z927,z4,z6]),(0,[z1,z77,z3,z146,z4,z6]),(0,[z928,z2,z7,z3,z4,z6])],[(0,[z1,z929,z7,z3,z4,z6]),(0,[z1,z2,z7,z930,z3,z4]),(0,[z1,z7,z3,z4,z6,z931])],[(0,[z1,z2,z932,z3,z4,z6]),(0,[z1,z2,z3,z4,z933,z6])],[(0,[z1,z2,z7,z3,z4,z934]),(0,[z1,z2,z7,z935,z4,z6]),(0,[z1,z936,z7,z3,z4,z6]),(0,[z937,z1,z2,z3,z4,z6]),(0,[z199,z1,z22,z7,z3,z6])],[(0,[z1,z685,z7,z3,z75,z6]),(0,[z1,z2,z938,z3,z4,z6]),(0,[z1,z2,z3,z939,z4,z6]),(0,[z1,z22,z7,z623,z4,z6]),(0,[z109,z1,z2,z7,z3,z105]),(0,[z1,z230,z7,z3,z4,z83]),(0,[z1,z2,z7,z3,z4,z756])],[(0,[z1,z7,z3,z33,z4,z334]),(0,[z1,z52,z710,z3,z4,z6]),(0,[z1,z7,z3,z33,z6,z940]),(0,[z1,z2,z941,z3,z4,z6]),(0,[z1,z254,z194,z3,z4,z6])]],
   [[(0,[z895,z1,z7,z3,z4,z6]),(0,[z1,z2,z942,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z167]),(0,[z943,z22,z7,z3,z4,z6]),(0,[z1,z22,z114,z3,z4,z5]),(0,[z261,z22,z7,z3,z4,z6])],[(0,[z1,z47,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z944]),(0,[z1,z3,z33,z4,z282,z6]),(0,[z1,z77,z87,z33,z4,z6]),(0,[z1,z737,z22,z3,z4,z6])],[(0,[z1,z945,z7,z3,z4,z6]),(0,[z197,z1,z3,z31,z186,z6]),(0,[z1,z2,z3,z31,z761,z6])],[(0,[z1,z2,z7,z3,z4,z946]),(0,[z1,z317,z3,z88,z4,z6]),(0,[z182,z7,z97,z3,z4,z6])],[(0,[z2,z7,z3,z4,z120,z779])],[(0,[z1,z2,z7,z3,z4,z947]),(0,[z1,z84,z97,z3,z4,z6]),(0,[z1,z2,z515,z3,z4,z5]),(0,[z948,z2,z7,z3,z4,z6]),(0,[z1,z160,z367,z3,z4,z6]),(0,[z1,z949,z7,z3,z4,z6])],[(0,[z1,z2,z77,z74,z3,z4]),(0,[z1,z739,z77,z3,z4,z6])],[(0,[z1,z2,z950,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z779])],[(0,[z158,z1,z2,z3,z4,z120]),(0,[z1,z2,z270,z3,z4,z6]),(0,[z1,z2,z550,z3,z4,z6]),(0,[z1,z951,z7,z3,z4,z6])],[(0,[z197,z1,z7,z3,z316,z6]),(0,[z1,z7,z3,z952,z4,z6]),(0,[z1,z2,z7,z3,z953,z6]),(0,[z1,z7,z3,z954,z33,z4]),(0,[z1,z22,z277,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z740]),(0,[z1,z7,z3,z955,z4,z6])],[(0,[z109,z1,z7,z3,z4,z227]),(0,[z1,z956,z7,z3,z4,z6])],[(0,[z1,z215,z3,z31,z4,z6]),(0,[z1,z957,z7,z3,z4,z6])],[(0,[z1,z7,z3,z4,z6,z720]),(0,[z1,z2,z7,z3,z4,z958]),(0,[z65,z1,z2,z3,z4,z740]),(0,[z170,z1,z7,z3,z162,z42])],[(0,[z1,z2,z112,z3,z90,z6]),(0,[z1,z959,z7,z3,z4,z6]),(0,[z660,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z6,z858,z39])],[(0,[z1,z2,z7,z3,z960,z6]),(0,[z1,z2,z752,z3,z4,z6]),(0,[z1,z2,z77,z688,z4,z6]),(0,[z1,z2,z961,z3,z4,z6])],[(0,[z2,z3,z31,z4,z6,z432]),(0,[z38,z1,z2,z77,z6,z39]),(0,[z1,z3,z4,z147,z62,z6])]],
   [[(0,[z148,z847,z7,z3,z4,z6]),(0,[z1,z22,z7,z20,z4,z6]),(0,[z1,z22,z77,z31,z4,z6]),(0,[z1,z2,z962,z3,z4,z6])],[(0,[z1,z77,z3,z518,z4,z6]),(0,[z1,z2,z3,z31,z789,z4]),(0,[z1,z552,z7,z3,z127,z6])],[(0,[z1,z317,z7,z3,z4,z6]),(0,[z250,z7,z3,z33,z4,z96]),(0,[z1,z2,z77,z3,z318,z6]),(0,[z660,z2,z7,z3,z157,z6])],[(0,[z1,z2,z3,z4,z6,z963]),(0,[z1,z964,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z965,z6]),(0,[z1,z7,z698,z33,z4,z6]),(0,[z1,z966,z7,z3,z4,z6]),(0,[z1,z110,z7,z27,z4,z28])],[(0,[z1,z22,z493,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z967]),(0,[z1,z22,z7,z651,z4,z6]),(0,[z1,z968,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z969,z6])],[(0,[z1,z22,z7,z3,z4,z6]),(0,[z1,z7,z3,z970,z4,z6])],[(0,[z1,z2,z971,z3,z4,z6]),(0,[z972,z2,z7,z3,z4,z6]),(0,[z1,z149,z113,z3,z4,z23]),(0,[z1,z2,z114,z3,z4,z236]),(0,[z1,z396,z114,z3,z4,z5])],[(0,[z189,z95,z3,z31,z4,z6]),(0,[z197,z1,z77,z3,z186,z6]),(0,[z1,z2,z7,z3,z505,z42]),(0,[z1,z2,z3,z34,z4,z527]),(0,[z1,z2,z77,z483,z4,z6])],[(0,[z1,z7,z3,z4,z221,z6]),(0,[z38,z1,z22,z7,z6,z39]),(0,[z1,z77,z3,z239,z4,z6])],[(0,[z1,z3,z33,z4,z62,z6]),(0,[z109,z197,z1,z7,z3,z42]),(0,[z1,z43,z7,z3,z127,z6])],[(0,[z1,z2,z168,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z973])],[(0,[z108,z255,z7,z3,z4,z6]),(0,[z584,z2,z7,z3,z4,z96]),(0,[z974,z2,z7,z3,z4,z6]),(0,[z615,z1,z2,z7,z3,z42]),(0,[z1,z2,z77,z40,z41,z6])],[(0,[z1,z975,z7,z3,z4,z6]),(0,[z1,z52,z3,z414,z4,z6]),(0,[z1,z7,z33,z410,z4,z6])],[(0,[z69,z2,z7,z3,z104,z6])],[(0,[z1,z3,z518,z31,z4,z6]),(0,[z1,z976,z3,z33,z4,z6]),(0,[z109,z1,z7,z3,z4,z720]),(0,[z1,z100,z3,z31,z4,z6])],[(0,[z2,z7,z3,z4,z6,z432]),(0,[z1,z2,z977,z3,z4,z6]),(0,[z106,z1,z100,z31,z4,z6])]],
   [[(0,[z1,z22,z7,z3,z4,z334]),(0,[z38,z1,z2,z7,z83,z39])],[(0,[z1,z22,z7,z3,z4,z167]),(0,[z67,z2,z7,z3,z4,z465])],[(0,[z1,z2,z7,z3,z4,z978]),(0,[z1,z7,z3,z979,z4,z6]),(0,[z1,z350,z3,z31,z4,z6])],[(0,[z1,z280,z3,z31,z4,z6])],[(0,[z980,z1,z2,z7,z3,z6]),(0,[z50,z2,z7,z51,z9,z6]),(0,[z1,z7,z3,z33,z4,z413]),(0,[z303,z1,z22,z3,z4,z6])],[(0,[z1,z2,z3,z981,z4,z6]),(0,[z1,z3,z4,z203,z58,z6]),(0,[z199,z1,z7,z3,z33,z6])],[(0,[z982,z2,z7,z3,z4,z6])],[(0,[z1,z47,z155,z3,z4,z6]),(0,[z1,z2,z77,z513,z4,z6]),(0,[z1,z983,z7,z3,z4,z6]),(0,[z2,z114,z7,z3,z4,z432])],[],[(0,[z1,z7,z3,z984,z4,z6]),(0,[z1,z97,z3,z623,z4,z6]),(0,[z1,z2,z77,z625,z4,z6]),(0,[z1,z7,z3,z33,z6,z105])],[(0,[z1,z985,z7,z3,z4,z6]),(0,[z0,z1,z2,z3,z90,z6]),(0,[z1,z22,z3,z4,z58,z6]),(0,[z1,z84,z537,z3,z4,z6]),(0,[z986,z2,z7,z3,z4,z6]),(0,[z1,z52,z3,z410,z4,z6])],[(0,[z38,z1,z2,z31,z6,z39]),(0,[z1,z2,z3,z153,z849,z6])],[(0,[z1,z2,z3,z987,z4,z6]),(0,[z1,z2,z3,z4,z849,z6])],[(0,[z1,z2,z7,z3,z4,z988]),(0,[z1,z989,z7,z3,z4,z6]),(0,[z1,z22,z7,z3,z90,z6])],[(0,[z1,z2,z7,z3,z4,z990]),(0,[z1,z2,z3,z31,z4,z835]),(0,[z1,z86,z3,z31,z4,z6]),(0,[z1,z991,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z992,z6]),(0,[z67,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z4,z993,z6])]],
   [[(0,[z1,z114,z3,z33,z4,z5]),(0,[z1,z994,z7,z3,z4,z6])],[],[(0,[z1,z367,z3,z32,z4,z6])],[(0,[z250,z22,z7,z3,z4,z96])],[(0,[z1,z7,z3,z995,z4,z6])],[(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z2,z997,z3,z4,z6]),(0,[z1,z2,z77,z3,z157,z6]),(0,[z1,z2,z7,z3,z516,z42]),(0,[z392,z2,z277,z3,z4,z6])],[(0,[z250,z303,z2,z3,z4,z96])],[(0,[z197,z1,z94,z3,z4,z6]),(0,[z1,z2,z3,z998,z4,z6])],[(0,[z1,z2,z999,z3,z4,z6]),(0,[z50,z2,z7,z51,z119,z6]),(0,[z1,z2,z7,z3,z4,z1000])],[(0,[z1,z7,z3,z4,z6,z899])],[(0,[z1,z2,z77,z267,z4,z6])],[(0,[z1,z317,z3,z31,z4,z6]),(0,[z1,z2,z3,z1001,z4,z6]),(0,[z158,z1,z2,z3,z4,z96]),(0,[z1,z2,z3,z1002,z4,z6]),(0,[z872,z1,z7,z3,z33,z6]),(0,[z1,z2,z3,z4,z993,z167]),(0,[z106,z1,z2,z747,z4,z6]),(0,[z1,z2,z31,z4,z6,z532]),(0,[z1,z1003,z7,z3,z4,z6]),(0,[z1004,z1,z2,z3,z4,z6])],[(0,[z1,z1005,z7,z3,z4,z6])],[(0,[z723,z7,z3,z33,z4,z6]),(0,[z1,z2,z550,z3,z4,z465]),(0,[z158,z1,z3,z4,z147,z6])],[(0,[z1,z7,z3,z33,z4,z195]),(0,[z1,z1006,z7,z3,z4,z6]),(0,[z183,z7,z3,z33,z4,z6]),(0,[z1,z168,z3,z4,z23,z6])],[(0,[z1,z2,z7,z3,z1007,z6]),(0,[z1008,z1,z2,z7,z3,z6])]],
   [[(0,[z1,z2,z7,z3,z4,z1009]),(0,[z94,z2,z3,z4,z6,z96]),(0,[z1,z22,z7,z33,z4,z6])],[(0,[z189,z94,z95,z3,z4,z6]),(0,[z392,z2,z7,z3,z4,z6]),(0,[z1,z22,z7,z306,z4,z6]),(0,[z170,z1,z7,z3,z4,z6]),(0,[z1,z1010,z7,z3,z4,z6])],[(0,[z0,z2,z99,z3,z4,z102]),(0,[z1,z2,z1011,z3,z4,z6]),(0,[z1,z1012,z7,z3,z4,z6]),(0,[z1,z7,z3,z1013,z4,z6]),(0,[z1,z2,z7,z3,z849,z6])],[(0,[z1,z2,z3,z4,z282,z6]),(0,[z1,z84,z176,z3,z4,z6]),(0,[z1,z2,z3,z31,z871,z4]),(0,[z1,z552,z277,z3,z4,z6])],[(0,[z1,z2,z1014,z3,z4,z6]),(0,[z106,z1,z22,z31,z4,z6]),(0,[z1,z22,z3,z449,z4,z6]),(1,[z1,z2,z3,z849,z6])],[(0,[z2,z7,z3,z730,z4,z6]),(0,[z1,z2,z1015,z3,z4,z6]),(0,[z1,z22,z7,z3,z4,z413])],[],[(0,[z1,z270,z3,z33,z4,z6]),(0,[z72,z1,z2,z176,z3,z6]),(0,[z38,z1,z2,z141,z6,z39])],[(0,[z15,z2,z3,z4,z6,z432]),(0,[z1,z7,z3,z4,z1016,z6]),(0,[z1,z231,z3,z33,z4,z6]),(0,[z348,z1,z7,z3,z6,z577]),(0,[z65,z2,z7,z3,z4,z432])],[(0,[z0,z22,z99,z3,z4,z6]),(0,[z1,z22,z3,z88,z4,z6]),(0,[z1,z2,z7,z3,z1017,z6]),(0,[z1,z2,z7,z3,z4,z1018]),(0,[z1,z2,z371,z31,z4,z6])],[(0,[z1,z94,z22,z3,z4,z6]),(0,[z24,z1,z3,z33,z25,z6]),(0,[z1,z22,z7,z3,z4,z465]),(0,[z1,z22,z7,z3,z6,z105]),(0,[z1,z2,z1019,z3,z4,z6]),(0,[z1,z2,z1020,z3,z4,z6])],[(0,[z1,z7,z3,z4,z1021,z6]),(0,[z1022,z2,z7,z3,z4,z6]),(0,[z1,z145,z3,z290,z4,z6]),(0,[z1,z43,z277,z3,z4,z6]),(0,[z1,z3,z500,z449,z4,z6])],[(0,[z1,z7,z3,z4,z1023,z6])],[(0,[z1,z1024,z7,z3,z4,z6]),(0,[z1,z2,z87,z747,z4,z6])],[(0,[z1,z350,z141,z3,z4,z6])],[(0,[z1,z2,z1025,z3,z4,z6]),(0,[z109,z182,z7,z3,z4,z140])]],
   [[(0,[z0,z1,z237,z3,z4,z6]),(0,[z2,z7,z730,z51,z4,z6]),(0,[z1,z277,z3,z33,z4,z6]),(0,[z1,z237,z77,z3,z4,z6]),(0,[z1,z2,z1026,z3,z4,z6])],[(0,[z1,z7,z315,z33,z4,z6]),(0,[z1,z2,z7,z3,z4,z102]),(0,[z1,z2,z3,z1027,z4,z6]),(0,[z1,z1028,z7,z3,z4,z6]),(0,[z1,z2,z97,z3,z90,z6]),(0,[z1,z2,z7,z3,z1029,z6]),(0,[z1030,z2,z7,z3,z4,z6])],[(0,[z1,z2,z3,z1031,z4,z6]),(0,[z1,z1032,z2,z3,z4,z6]),(0,[z108,z847,z7,z3,z4,z6]),(0,[z2,z820,z151,z3,z4,z6]),(0,[z1,z7,z3,z1033,z4,z6]),(0,[z2,z7,z3,z191,z4,z96]),(0,[z1,z2,z438,z3,z4,z6]),(0,[z660,z7,z3,z33,z4,z6]),(0,[z123,z1,z2,z3,z6,z205])],[(0,[z1,z2,z493,z3,z9,z6]),(0,[z1,z73,z7,z3,z711,z6]),(0,[z986,z2,z3,z31,z4,z6]),(0,[z1,z2,z31,z4,z426,z6]),(0,[z1,z7,z3,z4,z773,z6])],[(0,[z1,z2,z7,z3,z9,z6]),(0,[z1,z2,z7,z3,z1034,z6]),(0,[z1,z2,z3,z4,z6,z1035])],[(0,[z1,z1036,z7,z3,z4,z6]),(0,[z1,z1037,z7,z3,z4,z6]),(0,[z1,z1038,z7,z3,z4,z6])],[(0,[z1,z2,z3,z1039,z4,z6])],[(0,[z1,z7,z3,z1040,z4,z6]),(0,[z1,z7,z3,z4,z1041,z6]),(0,[z1,z22,z7,z371,z4,z6]),(0,[z1,z7,z3,z33,z318,z6]),(0,[z1,z149,z7,z3,z4,z23])],[(0,[z1,z2,z7,z1042,z4,z6]),(0,[z65,z1,z2,z3,z4,z325]),(0,[z1,z2,z1043,z3,z4,z6]),(0,[z1,z254,z97,z3,z4,z6]),(0,[z1,z52,z367,z3,z4,z6]),(0,[z67,z2,z3,z31,z4,z6]),(0,[z1,z2,z1044,z3,z4,z6])],[(0,[z1,z95,z176,z3,z4,z6]),(0,[z1,z47,z77,z3,z4,z6]),(0,[z1,z2,z7,z1045,z4,z6]),(0,[z1,z7,z3,z1046,z4,z6])],[(0,[z2,z3,z31,z1047,z4,z6]),(0,[z1,z2,z155,z3,z153,z6])],[(0,[z1,z1048,z7,z3,z4,z6]),(0,[z1,z2,z3,z4,z62,z6]),(0,[z1,z7,z3,z4,z6,z1049]),(0,[z1,z2,z27,z449,z4,z28]),(0,[z158,z170,z1,z3,z4,z6])],[],[(0,[z1,z2,z155,z3,z658,z6]),(0,[z132,z2,z7,z3,z4,z120]),(0,[z1,z2,z3,z4,z6,z1050])],[(0,[z1,z2,z7,z3,z1051,z6]),(0,[z15,z435,z2,z3,z4,z6]),(0,[z1,z160,z112,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z1052]),(0,[z1,z600,z3,z239,z4,z6]),(0,[z1,z2,z277,z3,z127,z6])],[(0,[z1,z2,z7,z3,z9,z334]),(0,[z1,z22,z7,z3,z4,z195]),(0,[z686,z2,z7,z3,z4,z96]),(0,[z1,z2,z3,z1053,z4,z6]),(0,[z183,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z83])]],
   [[(0,[z1,z1054,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z1055]),(0,[z1,z2,z7,z3,z1056,z6]),(0,[z619,z1,z2,z31,z4,z6])],[(0,[z7,z3,z33,z4,z6,z432]),(0,[z1,z1057,z3,z33,z4,z6])],[(0,[z1,z2,z1058,z3,z4,z6]),(0,[z1,z1059,z2,z3,z4,z6])],[(0,[z1,z7,z3,z4,z1060,z57]),(0,[z1,z1061,z7,z3,z4,z6]),(0,[z1,z215,z77,z3,z4,z6]),(0,[z1,z149,z7,z3,z4,z147])],[(0,[z1,z2,z1062,z3,z4,z6])],[(0,[z211,z230,z7,z3,z4,z6])],[(0,[z1,z7,z3,z75,z471,z6]),(0,[z1,z2,z3,z1063,z4,z6]),(0,[z72,z1,z2,z291,z3,z31])],[(0,[z1,z7,z3,z1064,z4,z6]),(0,[z214,z2,z151,z3,z4,z6]),(0,[z1,z2,z493,z3,z119,z6]),(0,[z158,z1,z3,z33,z4,z6]),(0,[z1,z2,z3,z4,z6,z1065])],[(0,[z1,z2,z7,z3,z119,z6]),(0,[z1,z3,z33,z313,z4,z6]),(0,[z1,z7,z3,z4,z1066,z6]),(0,[z38,z1,z2,z550,z6,z39])],[(0,[z135,z2,z7,z3,z4,z456]),(0,[z126,z2,z7,z3,z4,z120]),(0,[z1,z7,z3,z1067,z4,z6]),(0,[z1,z2,z1057,z3,z4,z6]),(0,[z1,z2,z1068,z3,z4,z6]),(0,[z1,z174,z3,z500,z4,z6])],[(0,[z1,z1069,z7,z3,z4,z6]),(0,[z2,z7,z3,z1047,z4,z6]),(0,[z1,z22,z141,z3,z4,z6]),(0,[z1,z2,z40,z31,z41,z6])],[(0,[z592,z95,z7,z3,z4,z6]),(0,[z303,z1,z3,z4,z203,z6]),(0,[z1,z79,z2,z7,z3,z42])],[(0,[z1,z22,z7,z74,z3,z4]),(0,[z72,z1,z2,z7,z441,z3])],[(0,[z1,z7,z3,z549,z75,z6])],[(0,[z1,z2,z77,z653,z4,z6]),(0,[z1,z1070,z7,z3,z4,z6]),(0,[z1,z396,z7,z3,z4,z6]),(0,[z1,z7,z3,z146,z4,z6]),(0,[z1071,z2,z7,z3,z4,z6])],[(0,[z189,z95,z77,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z1072]),(0,[z1,z913,z22,z3,z4,z6]),(0,[z1073,z2,z7,z3,z4,z6])]],
   [[],[(0,[z1,z2,z3,z1074,z4,z6]),(0,[z1075,z1,z2,z3,z31,z6])],[(0,[z1,z255,z7,z3,z4,z6]),(0,[z76,z2,z7,z3,z104,z413]),(0,[z1076,z1,z2,z3,z4,z6]),(0,[z1,z1077,z7,z3,z4,z6]),(0,[z1,z1078,z7,z3,z4,z6])],[(0,[z1,z22,z260,z3,z4,z6]),(0,[z1,z2,z7,z3,z119,z334])],[(0,[z1,z2,z77,z476,z4,z6]),(0,[z1,z7,z535,z33,z4,z6]),(0,[z65,z1,z2,z3,z90,z66])],[(0,[z1,z7,z537,z33,z4,z6]),(0,[z1079,z1,z2,z7,z3,z6]),(0,[z348,z1,z7,z3,z186,z6]),(0,[z24,z1,z2,z3,z849,z6]),(0,[z1,z1080,z7,z3,z4,z6]),(0,[z1,z2,z7,z890,z3,z6])],[(0,[z1,z22,z1081,z3,z4,z6]),(0,[z1,z100,z77,z3,z4,z6]),(0,[z1,z1082,z7,z3,z4,z6])],[(0,[z1,z2,z7,z1083,z4,z6]),(0,[z1,z2,z7,z3,z4,z1084]),(0,[z1,z1085,z7,z3,z4,z6])],[(0,[z1,z317,z80,z3,z4,z6]),(0,[z2,z7,z3,z4,z6,z779]),(0,[z1,z22,z7,z3,z318,z6]),(0,[z1,z2,z1086,z3,z4,z6])],[(0,[z2,z7,z3,z51,z9,z6]),(0,[z1,z1087,z7,z3,z4,z6])],[(0,[z1,z2,z3,z31,z4,z102]),(0,[z1,z2,z1088,z3,z4,z6]),(0,[z1,z7,z3,z33,z157,z6]),(0,[z1,z350,z77,z3,z4,z6]),(0,[z67,z2,z7,z3,z41,z6])],[(0,[z1,z22,z80,z3,z4,z6]),(0,[z1,z7,z3,z1089,z4,z6]),(0,[z1,z280,z77,z3,z4,z6]),(0,[z1090,z2,z7,z3,z4,z6]),(0,[z1,z2,z1091,z3,z4,z6]),(0,[z1,z77,z87,z146,z4,z6])],[(0,[z1,z2,z3,z1092,z4,z6]),(0,[z0,z680,z2,z3,z4,z6]),(0,[z1,z1093,z7,z3,z4,z6]),(0,[z1,z1094,z7,z3,z4,z6])],[(0,[z1,z2,z1095,z3,z4,z6]),(0,[z1,z2,z31,z4,z6,z530])],[(0,[z1,z94,z3,z33,z4,z6]),(0,[z1076,z1,z2,z3,z4,z167]),(0,[z1,z2,z77,z687,z4,z6])],[(0,[z50,z2,z51,z31,z4,z6]),(0,[z197,z1,z7,z3,z6,z105])]],
   [[(0,[z1,z149,z3,z31,z4,z23])],[(0,[z1,z22,z3,z31,z4,z6]),(0,[z1,z7,z3,z1096,z90,z6]),(0,[z1,z2,z7,z3,z127,z28])],[(0,[z1,z141,z3,z33,z4,z6]),(0,[z1,z2,z1097,z3,z4,z6])],[(0,[z211,z2,z7,z3,z4,z6]),(0,[z50,z2,z7,z51,z4,z334])],[(0,[z1,z1098,z7,z3,z4,z6]),(0,[z1,z1099,z7,z3,z4,z6]),(0,[z1,z2,z826,z3,z4,z6]),(0,[z67,z2,z141,z3,z4,z6])],[(0,[z1,z7,z3,z518,z4,z6]),(0,[z1,z2,z1100,z3,z4,z6]),(0,[z65,z1,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z1101,z6]),(0,[z76,z2,z7,z3,z104,z6]),(0,[z1,z2,z7,z4,z6,z858]),(0,[z392,z2,z231,z3,z4,z6])],[(0,[z15,z151,z3,z33,z4,z6]),(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1,z86,z77,z3,z4,z6])],[(0,[z1,z255,z3,z4,z58,z6]),(0,[z980,z1,z7,z3,z33,z6])],[(0,[z660,z2,z7,z3,z4,z180])],[(0,[z1,z2,z7,z3,z4,z1103]),(0,[z44,z1,z43,z7,z4,z180])],[(0,[z1,z2,z1104,z3,z4,z6]),(0,[z1,z2,z1105,z3,z4,z6])],[(0,[z1,z1106,z7,z3,z4,z6]),(0,[z109,z261,z7,z3,z4,z140]),(0,[z1,z2,z7,z3,z632,z42]),(0,[z596,z1,z2,z7,z291,z3])],[(0,[z1,z2,z3,z1107,z4,z6]),(0,[z1,z7,z3,z1108,z4,z6]),(0,[z1,z7,z3,z239,z4,z6]),(0,[z1109,z2,z7,z3,z4,z6])],[(0,[z1,z2,z1110,z3,z4,z6]),(0,[z1,z7,z3,z4,z1111,z6])],[(0,[z1,z1112,z2,z3,z4,z6]),(0,[z1,z7,z3,z220,z4,z23]),(0,[z1,z583,z7,z3,z4,z519])],[(0,[z1,z2,z335,z31,z4,z6]),(0,[z1,z2,z7,z3,z1113,z6]),(0,[z902,z1,z7,z3,z33,z4]),(0,[z1,z2,z3,z1114,z4,z6])]],
   [[(0,[z1115,z1,z2,z3,z4,z6]),(0,[z250,z255,z7,z3,z4,z96])],[(0,[z2,z7,z3,z1116,z104,z6]),(0,[z1,z2,z155,z3,z849,z6])],[(0,[z1,z2,z196,z3,z4,z6]),(0,[z1,z552,z7,z3,z4,z6]),(0,[z1,z2,z600,z3,z4,z6]),(0,[z158,z1,z2,z3,z153,z6])],[(0,[z2,z820,z7,z3,z4,z6]),(0,[z11,z7,z30,z33,z4,z6]),(0,[z1,z317,z77,z3,z4,z6]),(0,[z72,z1,z2,z7,z890,z3])],[(0,[z1,z7,z33,z4,z665,z6]),(0,[z1,z7,z1117,z3,z33,z4]),(0,[z2,z3,z31,z4,z6,z1118]),(0,[z44,z1,z2,z7,z127,z180]),(0,[z1,z2,z7,z890,z3,z4])],[(0,[z1,z3,z33,z449,z4,z6]),(0,[z1,z2,z7,z3,z4,z829]),(0,[z182,z7,z3,z75,z4,z6]),(0,[z1,z110,z3,z449,z4,z6]),(0,[z1,z2,z3,z1119,z4,z6])],[(0,[z1,z1120,z2,z3,z4,z6]),(0,[z1,z148,z176,z3,z4,z6]),(0,[z1,z52,z696,z3,z4,z6]),(0,[z1,z237,z112,z3,z4,z6]),(0,[z1,z2,z7,z3,z6,z831])],[(0,[z1,z2,z7,z747,z4,z6]),(0,[z1,z396,z3,z31,z4,z6]),(0,[z1,z7,z3,z1121,z4,z6]),(0,[z1,z2,z3,z4,z5,z740]),(0,[z1,z2,z7,z4,z28,z756])],[(0,[z1,z2,z27,z31,z4,z28]),(0,[z1,z2,z7,z27,z4,z28])],[(0,[z839,z2,z7,z3,z4,z6]),(1,[z1,z2,z747,z4,z6])],[(0,[z1,z185,z7,z3,z9,z6]),(0,[z1,z1122,z7,z3,z4,z6]),(0,[z1,z43,z7,z3,z4,z6]),(0,[z1123,z1,z2,z3,z4,z6])],[(0,[z1,z2,z1124,z3,z4,z6]),(0,[z303,z1,z3,z33,z4,z6]),(0,[z1,z255,z3,z31,z4,z6]),(0,[z1,z1125,z7,z3,z4,z6])],[(0,[z1,z94,z47,z3,z4,z6]),(0,[z1126,z1,z2,z3,z4,z57]),(0,[z76,z2,z7,z3,z1116,z6]),(0,[z253,z1,z2,z7,z291,z3]),(0,[z1,z22,z231,z3,z4,z6]),(0,[z109,z1,z168,z3,z4,z6])],[(0,[z1,z1127,z7,z3,z4,z6]),(0,[z1128,z1,z7,z3,z4,z6]),(0,[z1129,z182,z2,z3,z4,z6])],[(0,[z1,z2,z1130,z3,z4,z6]),(0,[z1,z2,z7,z3,z9,z195]),(0,[z1,z2,z7,z3,z4,z57]),(0,[z1,z2,z77,z3,z874,z6]),(0,[z1,z2,z3,z4,z1131,z6])],[(0,[z1,z2,z7,z1132,z3,z4]),(0,[z1,z52,z47,z3,z4,z6]),(0,[z1,z2,z7,z3,z1133,z6]),(0,[z336,z1,z2,z3,z25,z6]),(0,[z65,z1,z2,z3,z4,z66])]],
   [[(0,[z1,z2,z7,z3,z1134,z6]),(0,[z1,z1135,z7,z3,z4,z6])],[(0,[z15,z2,z7,z3,z4,z423]),(0,[z1,z77,z115,z3,z4,z6])],[(0,[z1,z1136,z7,z3,z4,z6]),(0,[z1,z2,z7,z326,z4,z28])],[(0,[z11,z2,z7,z30,z4,z6]),(0,[z1,z2,z1137,z3,z4,z6])],[(0,[z1,z52,z442,z3,z4,z6]),(0,[z2,z7,z30,z730,z4,z6]),(0,[z1,z1138,z7,z3,z4,z6]),(0,[z38,z211,z2,z7,z6,z39])],[(0,[z1,z7,z3,z549,z551,z6]),(0,[z1,z1139,z2,z3,z4,z6])],[(0,[z1,z2,z1140,z3,z4,z6]),(0,[z1,z2,z297,z31,z4,z6]),(0,[z2,z77,z3,z4,z6,z1141]),(0,[z1,z2,z7,z41,z6,z858])],[(0,[z1,z2,z1142,z3,z4,z6])],[(0,[z1,z1143,z7,z3,z4,z6]),(0,[z1,z1144,z7,z3,z4,z6])],[(0,[z1,z847,z7,z3,z4,z6]),(0,[z1,z2,z3,z4,z1145,z6]),(0,[z15,z16,z151,z3,z4,z6]),(0,[z1,z110,z7,z3,z4,z6]),(0,[z1,z2,z1146,z3,z4,z6]),(0,[z109,z1,z7,z3,z4,z147]),(0,[z1,z2,z3,z153,z90,z6])],[(0,[z15,z13,z2,z3,z4,z6]),(0,[z2,z7,z3,z4,z1116,z6]),(0,[z1,z2,z113,z3,z4,z6]),(0,[z1,z2,z3,z313,z4,z6])],[(0,[z1,z73,z7,z3,z147,z6]),(0,[z1,z7,z3,z1147,z4,z6]),(0,[z1,z1148,z7,z3,z4,z6])],[(0,[z1,z1149,z7,z3,z4,z6]),(0,[z7,z3,z33,z1047,z4,z6]),(0,[z1,z2,z3,z153,z6,z567]),(0,[z1,z7,z3,z1096,z4,z6])],[(0,[z11,z2,z7,z81,z4,z6]),(0,[z1,z2,z7,z3,z1150,z6]),(0,[z392,z2,z3,z31,z4,z6]),(0,[z170,z1,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z127,z6])],[(0,[z1,z185,z7,z3,z119,z6]),(0,[z76,z2,z3,z31,z104,z6]),(0,[z1,z2,z7,z365,z41,z6]),(0,[z1,z7,z3,z33,z789,z4]),(0,[z1,z264,z244,z3,z4,z6])],[(0,[z542,z1,z2,z7,z6,z39]),(0,[z1,z1151,z7,z3,z4,z6]),(0,[z1,z2,z1152,z3,z4,z6])]],
   [[(0,[z1,z2,z7,z3,z954,z4]),(0,[z60,z148,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z1060,z6]),(0,[z67,z2,z77,z3,z4,z6]),(0,[z1,z7,z3,z1153,z4,z6])],[(0,[z1,z1154,z7,z3,z4,z6]),(0,[z1,z52,z112,z3,z4,z6])],[(0,[z192,z2,z99,z3,z4,z6]),(0,[z1,z2,z260,z3,z9,z6]),(0,[z1,z2,z7,z3,z119,z195]),(0,[z2,z7,z3,z698,z104,z6])],[(0,[z108,z148,z7,z3,z4,z6]),(0,[z135,z2,z7,z3,z4,z120])],[(0,[z1,z22,z235,z3,z4,z6]),(0,[z38,z1,z7,z33,z6,z39]),(0,[z1,z2,z141,z3,z4,z83])],[(0,[z1,z1155,z2,z3,z4,z6]),(0,[z1,z322,z3,z33,z4,z6]),(0,[z1156,z1,z7,z3,z4,z6]),(0,[z1157,z1,z2,z3,z4,z6])],[(0,[z660,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z162,z42])],[(0,[z1,z1158,z7,z3,z4,z6]),(0,[z1,z7,z3,z162,z147,z42])],[(0,[z1,z260,z3,z33,z4,z6]),(0,[z1,z2,z463,z31,z4,z6]),(0,[z48,z1,z7,z898,z4,z6]),(0,[z1,z2,z1159,z3,z4,z6]),(0,[z1,z2,z747,z31,z4,z6]),(0,[z1160,z2,z7,z3,z4,z6]),(0,[z211,z2,z7,z3,z4,z465])],[(0,[z1,z2,z3,z4,z1161,z6]),(0,[z1,z2,z114,z3,z4,z58]),(0,[z1162,z2,z7,z3,z4,z6]),(0,[z1,z2,z1163,z3,z4,z6])],[(0,[z50,z2,z493,z51,z4,z6]),(0,[z1,z7,z3,z1164,z4,z6]),(0,[z1,z2,z176,z3,z4,z6]),(0,[z197,z1,z438,z3,z186,z6])],[(0,[z50,z2,z7,z51,z4,z6]),(0,[z1,z22,z3,z256,z4,z6]),(0,[z1,z552,z3,z31,z4,z6]),(1,[z1,z2,z7,z6,z858])],[(0,[z1,z80,z3,z33,z4,z6]),(0,[z1,z3,z146,z31,z4,z6])],[(0,[z1008,z1,z22,z7,z3,z6]),(0,[z1165,z2,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z1029,z6]),(0,[z1,z7,z27,z500,z4,z28])],[(1,[z847,z7,z3,z4,z6]),(0,[z50,z185,z7,z51,z4,z6]),(0,[z1,z2,z1166,z3,z4,z6]),(0,[z1,z3,z33,z4,z58,z6]),(0,[z1,z77,z1167,z3,z4,z6]),(0,[z1168,z2,z7,z3,z4,z6])],[(0,[z1,z230,z7,z3,z4,z465])]],
   [[(0,[z15,z2,z151,z3,z4,z6]),(0,[z1,z2,z3,z31,z9,z6]),(0,[z1,z2,z176,z3,z6,z42]),(0,[z783,z182,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1169,z6]),(0,[z1,z22,z77,z33,z4,z6]),(0,[z1,z22,z7,z330,z4,z6])],[(0,[z1,z2,z1170,z3,z4,z6]),(0,[z1,z2,z7,z689,z41,z6])],[(0,[z1,z2,z1171,z3,z4,z6]),(0,[z1,z298,z7,z3,z9,z6]),(0,[z1,z43,z3,z31,z4,z6])],[(0,[z1,z394,z2,z3,z4,z6]),(0,[z0,z2,z3,z53,z4,z6]),(0,[z1,z22,z7,z40,z41,z6])],[(0,[z1,z149,z7,z3,z23,z105]),(0,[z1,z77,z3,z500,z4,z6])],[(0,[z1,z2,z3,z4,z1172,z6]),(0,[z1,z2,z260,z3,z119,z6]),(0,[z48,z1,z7,z33,z4,z6])],[(0,[z1,z112,z3,z371,z4,z6]),(0,[z72,z1,z2,z7,z3,z700]),(0,[z392,z2,z7,z3,z157,z6])],[],[(0,[z182,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z1173,z6]),(0,[z139,z1,z7,z3,z523,z6]),(0,[z1,z7,z3,z1174,z4,z6])],[(0,[z1,z2,z1175,z3,z4,z6]),(0,[z1,z1176,z7,z3,z4,z6])],[(0,[z1,z1177,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z1178,z6]),(0,[z1,z2,z3,z31,z4,z83]),(0,[z1,z3,z500,z31,z4,z6])],[(0,[z1,z548,z97,z3,z4,z6]),(0,[z1,z2,z1179,z3,z4,z6]),(0,[z1,z1180,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z465,z39])],[(0,[z1,z2,z7,z3,z1181,z6]),(0,[z1,z230,z7,z3,z4,z6]),(0,[z109,z1,z7,z3,z4,z635])],[(0,[z1,z2,z7,z3,z4,z423])],[(0,[z1,z1182,z7,z3,z4,z6]),(0,[z1,z2,z3,z4,z740,z66])]],
   [[(0,[z2,z99,z820,z3,z4,z6]),(0,[z1,z2,z1183,z3,z4,z6]),(0,[z1,z149,z7,z3,z4,z519]),(0,[z1,z2,z77,z3,z4,z958])],[(0,[z1,z7,z33,z4,z6,z193]),(0,[z1,z2,z7,z1184,z4,z6]),(0,[z1,z2,z1185,z3,z4,z6]),(0,[z1,z1186,z7,z3,z4,z6])],[(0,[z189,z232,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z102]),(0,[z1,z110,z3,z31,z4,z6]),(0,[z72,z1,z2,z7,z134,z3]),(0,[z44,z1,z2,z7,z4,z180])],[(0,[z1,z2,z7,z3,z4,z1187]),(0,[z15,z2,z3,z4,z58,z6]),(0,[z1,z7,z3,z1188,z4,z6]),(0,[z1,z350,z550,z3,z4,z6])],[(0,[z1,z16,z7,z3,z4,z6]),(0,[z1,z1189,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z119,z6]),(0,[z1,z7,z3,z1190,z4,z6])],[(0,[z1,z2,z3,z1191,z4,z6]),(0,[z1,z2,z7,z3,z6,z1192]),(0,[z799,z22,z7,z3,z4,z6]),(0,[z1,z2,z1193,z3,z4,z6])],[(0,[z261,z2,z7,z3,z4,z6]),(0,[z1,z94,z52,z3,z4,z6]),(0,[z50,z2,z260,z51,z4,z6]),(0,[z943,z2,z7,z3,z4,z6]),(0,[z1,z1194,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z127,z6]),(0,[z1,z2,z114,z3,z4,z5]),(0,[z1,z552,z231,z3,z4,z6])],[(0,[z11,z2,z7,z3,z9,z6]),(0,[z1,z298,z7,z3,z119,z6]),(0,[z1,z2,z3,z449,z4,z6])],[(0,[z1,z2,z1195,z3,z4,z6]),(0,[z1,z149,z77,z3,z4,z23]),(0,[z1,z2,z7,z3,z4,z1196]),(0,[z1,z2,z54,z3,z89,z6]),(0,[z211,z2,z141,z3,z4,z6])],[(0,[z1,z2,z77,z451,z4,z6]),(0,[z1,z22,z77,z3,z4,z6]),(0,[z38,z1,z2,z7,z6,z858])],[(0,[z265,z2,z3,z53,z4,z6])],[],[(0,[z108,z148,z3,z31,z4,z6])],[(0,[z1,z2,z7,z1197,z4,z6]),(0,[z1,z3,z33,z88,z4,z6]),(0,[z1,z1198,z7,z3,z4,z6])],[(0,[z0,z2,z820,z3,z4,z6]),(0,[z1,z7,z3,z4,z1199,z6]),(0,[z1200,z2,z7,z3,z4,z6]),(0,[z1,z22,z812,z3,z4,z6]),(0,[z1,z22,z7,z3,z157,z6]),(0,[z1,z2,z74,z3,z31,z4]),(0,[z1,z43,z231,z3,z4,z6])],[(0,[z1,z2,z7,z3,z1201,z6]),(0,[z1,z2,z557,z31,z4,z6]),(0,[z1,z2,z277,z3,z4,z6]),(0,[z751,z1,z2,z3,z31,z4]),(0,[z1,z2,z3,z31,z162,z42])]],
   [[(0,[z1,z7,z1202,z3,z4,z6])],[(0,[z1,z493,z3,z33,z4,z6]),(0,[z1,z2,z1203,z3,z4,z6]),(0,[z383,z1,z97,z3,z4,z6])],[(0,[z1,z2,z155,z3,z643,z6])],[(0,[z15,z2,z422,z3,z4,z6]),(0,[z1,z2,z3,z4,z58,z423]),(0,[z1,z1204,z7,z3,z4,z6]),(0,[z106,z1,z357,z31,z4,z6])],[(0,[z1,z2,z3,z4,z6,z1205]),(0,[z1,z1206,z7,z3,z4,z6])],[(0,[z1,z22,z174,z3,z4,z6]),(0,[z249,z1,z2,z7,z4,z180])],[(0,[z2,z7,z3,z4,z6,z1207]),(0,[z1,z2,z77,z31,z4,z6]),(0,[z1,z2,z402,z3,z4,z236])],[(0,[z605,z2,z7,z3,z4,z96]),(0,[z50,z298,z7,z51,z4,z6]),(0,[z1,z73,z2,z7,z3,z167]),(0,[z1,z2,z1208,z3,z4,z6]),(0,[z2,z7,z3,z4,z6,z1118])],[(0,[z1,z22,z7,z695,z4,z6]),(0,[z1,z7,z3,z4,z6,z1209]),(0,[z1,z3,z239,z313,z4,z6]),(0,[z44,z1,z2,z277,z4,z180])],[(0,[z1,z2,z7,z3,z4,z1210]),(0,[z1,z1211,z7,z3,z4,z6]),(0,[z1,z1212,z7,z3,z4,z6]),(1,[z1,z2,z7,z4,z756]),(0,[z44,z1,z2,z7,z4,z756])],[(0,[z1,z47,z3,z4,z5,z6]),(0,[z1,z2,z493,z3,z4,z6]),(0,[z1,z1213,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z1214,z6]),(0,[z1,z7,z3,z1215,z4,z6])],[(0,[z1,z7,z3,z75,z6,z105]),(0,[z1,z1216,z7,z3,z4,z6]),(0,[z1,z2,z3,z1217,z4,z6])],[(0,[z1,z2,z3,z1218,z4,z6]),(0,[z1,z2,z3,z1219,z4,z6]),(0,[z1,z1220,z7,z3,z4,z6])],[(0,[z1,z2,z1221,z3,z4,z6]),(0,[z109,z1,z7,z3,z4,z140])],[(0,[z1,z2,z3,z4,z6,z1222]),(0,[z211,z2,z3,z31,z4,z6]),(0,[z1,z396,z77,z3,z4,z6])]],
   [[(0,[z986,z7,z3,z33,z4,z6]),(0,[z1,z22,z7,z595,z4,z6]),(0,[z660,z552,z7,z3,z4,z6])],[(0,[z1,z2,z3,z1223,z4,z6]),(0,[z1,z319,z600,z3,z4,z6]),(0,[z1,z2,z231,z3,z127,z6]),(0,[z1,z2,z7,z3,z124,z42])],[(0,[z1,z94,z97,z3,z4,z6]),(0,[z1,z52,z198,z3,z4,z6]),(0,[z182,z2,z3,z31,z4,z6]),(0,[z72,z1,z2,z7,z291,z3])],[(0,[z1,z255,z77,z3,z4,z6]),(0,[z1,z264,z3,z414,z4,z6])],[(0,[z1,z1224,z7,z3,z4,z6]),(0,[z1,z2,z1225,z3,z4,z6]),(0,[z1,z73,z7,z3,z378,z6]),(0,[z1,z7,z3,z1226,z4,z6])],[(0,[z1,z2,z493,z3,z4,z334]),(0,[z1,z2,z7,z3,z1227,z6]),(0,[z67,z7,z3,z33,z4,z6])],[(0,[z1,z2,z7,z3,z4,z334]),(0,[z1,z7,z3,z1228,z4,z6]),(0,[z1,z230,z3,z31,z4,z6]),(0,[z144,z1,z2,z3,z4,z66]),(0,[z1,z7,z3,z4,z1229,z6])],[(0,[z1,z2,z1230,z3,z4,z6]),(0,[z1,z7,z1231,z3,z4,z6]),(0,[z2,z7,z3,z4,z779,z96]),(0,[z1,z2,z7,z3,z4,z167])],[(0,[z1109,z2,z3,z31,z4,z6]),(0,[z660,z43,z7,z3,z4,z6])],[(0,[z1,z185,z7,z3,z4,z334]),(0,[z1,z2,z1232,z3,z4,z6]),(0,[z1,z112,z3,z32,z4,z6])],[(0,[z1,z3,z1031,z33,z4,z6]),(0,[z67,z350,z7,z3,z4,z6])],[(0,[z1233,z1,z2,z7,z3,z6]),(0,[z1234,z2,z7,z3,z4,z6]),(0,[z1,z86,z77,z87,z4,z6]),(0,[z1,z2,z7,z3,z42,z287])],[(0,[z1,z2,z191,z31,z4,z6]),(0,[z1,z7,z3,z4,z1235,z6])],[(0,[z1,z7,z213,z33,z4,z6]),(0,[z1,z2,z77,z410,z4,z6])],[(0,[z135,z94,z2,z3,z4,z6]),(0,[z1075,z1,z2,z7,z3,z6]),(0,[z65,z1,z2,z3,z4,z269]),(0,[z1,z2,z1236,z3,z4,z6]),(0,[z1237,z1,z7,z3,z4,z6]),(0,[z1,z2,z600,z40,z41,z6])],[(0,[z1,z22,z143,z31,z4,z6]),(0,[z261,z2,z3,z31,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z58,z6])],[(0,[z1,z1238,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z1239,z6]),(0,[z846,z2,z7,z3,z4,z6])],[(0,[z0,z2,z99,z3,z4,z423]),(0,[z1,z2,z1240,z3,z4,z6]),(0,[z1,z2,z1241,z3,z4,z6]),(0,[z1,z2,z1242,z3,z4,z6]),(0,[z1,z2,z633,z31,z4,z6]),(0,[z65,z1,z2,z3,z318,z66])],[(0,[z1,z1243,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z6,z1244]),(0,[z1,z2,z3,z34,z4,z5]),(0,[z1,z2,z7,z3,z766,z4]),(0,[z1,z1245,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z90,z6])],[(0,[z1246,z2,z7,z3,z4,z6])],[(0,[z50,z2,z7,z51,z4,z195]),(0,[z65,z1,z2,z3,z4,z58]),(0,[z392,z2,z77,z3,z4,z6]),(0,[z170,z1,z77,z3,z4,z6])],[(0,[z15,z1,z2,z3,z90,z6]),(0,[z76,z2,z77,z3,z104,z6]),(0,[z1,z2,z7,z3,z4,z1247]),(0,[z1,z2,z3,z1248,z4,z6]),(0,[z1,z1198,z3,z31,z4,z6]),(0,[z1,z2,z77,z439,z4,z6])],[(0,[z1,z7,z3,z1249,z4,z6]),(0,[z1,z7,z40,z33,z41,z6])],[(0,[z1,z2,z7,z898,z4,z6]),(0,[z1,z2,z1250,z3,z4,z6])],[(0,[z11,z2,z80,z30,z4,z6]),(0,[z250,z2,z7,z3,z4,z96]),(0,[z1,z319,z3,z313,z4,z6])],[(0,[z135,z47,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z57]),(0,[z631,z14,z7,z3,z4,z6])],[(0,[z1,z22,z77,z87,z4,z6]),(0,[z660,z2,z7,z3,z127,z6])],[(0,[z1,z176,z3,z33,z4,z6])],[(0,[z1,z2,z1251,z3,z4,z6]),(0,[z1,z115,z3,z31,z4,z6]),(0,[z1252,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z1253]),(0,[z1,z1254,z7,z3,z4,z6]),(0,[z1,z2,z644,z31,z4,z6]),(1,[z1,z2,z7,z890,z3])],[(0,[z1,z2,z3,z1255,z4,z6]),(0,[z1,z2,z7,z3,z1256,z6]),(0,[z1,z84,z710,z3,z4,z6]),(0,[z1,z7,z3,z4,z720,z140])]],
   [[(0,[z1,z1257,z7,z3,z4,z6]),(0,[z255,z182,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z757,z6])],[(0,[z1,z2,z260,z3,z4,z334]),(0,[z303,z1,z255,z3,z4,z6])],[(0,[z1,z2,z1258,z3,z4,z6])],[(0,[z847,z95,z7,z3,z4,z6]),(0,[z540,z1,z7,z33,z4,z6]),(0,[z1,z2,z3,z1259,z4,z6]),(0,[z1,z7,z3,z4,z23,z167]),(0,[z1,z1213,z3,z31,z4,z6]),(0,[z1,z2,z652,z31,z4,z6]),(0,[z1,z552,z77,z3,z4,z6]),(0,[z1,z2,z77,z472,z4,z6]),(0,[z1,z1260,z7,z3,z4,z6])],[],[(0,[z1,z7,z3,z1261,z4,z6]),(0,[z197,z1,z7,z3,z355,z6]),(0,[z1,z3,z33,z31,z4,z6]),(0,[z1,z22,z904,z3,z4,z6])],[(0,[z108,z59,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z1116,z6]),(0,[z1,z1262,z7,z3,z4,z6]),(0,[z1263,z2,z7,z3,z4,z6])],[(0,[z1,z2,z554,z31,z4,z6])],[(0,[z1,z2,z77,z3,z9,z6]),(0,[z192,z2,z425,z3,z4,z6]),(0,[z1,z2,z77,z747,z4,z6]),(0,[z1,z1264,z7,z3,z4,z6]),(0,[z1,z7,z3,z4,z1265,z6]),(0,[z1,z552,z7,z3,z157,z6])],[(0,[z1,z1266,z7,z3,z4,z6]),(0,[z649,z2,z7,z51,z4,z6]),(0,[z1,z2,z77,z27,z4,z28])],[(0,[z1,z2,z1267,z3,z4,z6]),(0,[z2,z7,z3,z4,z6,z1141]),(0,[z38,z1,z230,z7,z6,z39]),(0,[z1,z2,z1268,z3,z4,z6])],[(0,[z2,z7,z3,z51,z4,z334]),(0,[z1,z1269,z7,z3,z4,z6]),(0,[z1,z2,z1270,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z413]),(0,[z1,z22,z322,z3,z4,z6]),(0,[z311,z1,z2,z3,z4,z327]),(0,[z1,z43,z77,z3,z4,z6])],[(0,[z50,z7,z51,z33,z4,z6]),(0,[z1,z2,z3,z4,z1271,z6]),(0,[z44,z1,z552,z7,z4,z180])],[(0,[z1,z237,z97,z3,z4,z6]),(0,[z1,z235,z3,z33,z4,z6]),(0,[z1,z27,z33,z31,z4,z6]),(0,[z65,z1,z22,z3,z4,z66])],[(0,[z250,z2,z3,z4,z58,z96]),(0,[z1,z7,z3,z220,z4,z82])],[(0,[z0,z2,z99,z3,z4,z6]),(0,[z1,z2,z3,z88,z4,z6]),(0,[z1,z2,z3,z31,z4,z334]),(0,[z1,z2,z77,z3,z4,z57]),(0,[z135,z2,z3,z31,z4,z120]),(0,[z1,z112,z176,z3,z4,z6]),(0,[z1272,z2,z7,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z1273,z6]),(0,[z1,z7,z3,z4,z6,z1274]),(0,[z1,z2,z7,z3,z6,z105]),(0,[z1,z2,z77,z3,z1133,z6]),(0,[z1,z1275,z7,z3,z4,z6]),(0,[z183,z2,z114,z3,z4,z5]),(0,[z1,z2,z7,z3,z4,z465]),(0,[z1,z43,z7,z3,z157,z6])],[(0,[z1,z2,z1276,z3,z4,z6])],[(0,[z1,z298,z7,z3,z4,z334]),(0,[z1,z84,z3,z290,z4,z6]),(0,[z48,z1,z235,z33,z4,z6]),(0,[z197,z1,z176,z3,z186,z6]),(0,[z1,z230,z141,z3,z4,z6])],[(0,[z1277,z2,z7,z3,z4,z6]),(0,[z1,z2,z77,z3,z4,z83])],[(0,[z11,z7,z30,z518,z4,z6]),(0,[z11,z2,z77,z30,z4,z6]),(0,[z1,z2,z1278,z3,z4,z6]),(0,[z1,z174,z3,z33,z4,z6])],[(0,[z1,z2,z7,z3,z1279,z6]),(0,[z1,z354,z112,z3,z4,z6]),(0,[z1,z22,z7,z930,z3,z4])],[(0,[z1,z22,z821,z3,z4,z6]),(0,[z24,z1,z3,z221,z25,z6])],[(0,[z1,z2,z7,z3,z794,z6]),(0,[z1,z2,z1280,z3,z4,z6]),(0,[z1,z2,z3,z4,z1281,z6]),(0,[z1282,z2,z7,z3,z4,z6]),(0,[z1,z2,z1283,z3,z4,z6])],[(0,[z1,z2,z7,z890,z3,z162])],[(0,[z1,z976,z2,z3,z4,z6]),(0,[z1,z7,z3,z1284,z4,z6]),(0,[z751,z1,z2,z7,z3,z4]),(0,[z1,z2,z7,z3,z1285,z6])],[(0,[z1,z2,z3,z4,z721,z57]),(0,[z1,z2,z3,z1286,z4,z6]),(0,[z1,z110,z77,z3,z4,z6]),(0,[z1,z350,z7,z3,z4,z83]),(0,[z1,z2,z1287,z3,z4,z6])],[(0,[z1,z7,z3,z992,z33,z6])],[(0,[z15,z1,z237,z3,z4,z6]),(0,[z1,z2,z77,z3,z119,z6]),(0,[z1126,z1,z2,z3,z4,z6]),(0,[z1,z1288,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z90,z6]),(0,[z1,z7,z3,z4,z1289,z6])],[(0,[z382,z7,z3,z200,z4,z6]),(0,[z1,z196,z3,z33,z4,z6])],[(0,[z1,z145,z97,z3,z4,z6]),(0,[z1,z407,z112,z3,z4,z6]),(0,[z1,z2,z3,z49,z208,z6]),(0,[z1,z2,z77,z3,z127,z6])],[(0,[z1,z2,z1290,z3,z4,z6]),(0,[z1,z2,z231,z3,z4,z6])]],
   [[(0,[z1,z185,z493,z3,z4,z6])],[(0,[z1,z185,z7,z3,z4,z6]),(0,[z847,z2,z7,z3,z4,z6]),(0,[z1,z2,z1291,z3,z4,z6])],[(0,[z189,z182,z7,z3,z4,z6]),(0,[z1,z22,z270,z3,z4,z6]),(0,[z1,z22,z550,z3,z4,z6]),(0,[z1,z1070,z77,z3,z4,z6]),(0,[z1,z7,z1167,z3,z4,z6]),(0,[z1,z7,z3,z4,z6,z1292])],[(0,[z1,z1293,z2,z3,z4,z6]),(1,[z1,z7,z3,z4,z720]),(0,[z1,z2,z7,z3,z4,z1294]),(0,[z1,z2,z7,z3,z1295,z6]),(0,[z1,z2,z1296,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1297,z6]),(0,[z108,z148,z77,z3,z4,z6]),(0,[z1,z2,z493,z3,z4,z195]),(0,[z1,z7,z898,z33,z4,z6]),(0,[z1,z7,z3,z4,z1298,z6]),(0,[z1,z113,z3,z33,z4,z6])],[(0,[z183,z2,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z195]),(0,[z1,z1299,z7,z3,z4,z6]),(0,[z1,z7,z27,z33,z4,z28]),(0,[z199,z1,z2,z3,z31,z6])],[(0,[z109,z1,z7,z3,z4,z259]),(0,[z1,z2,z1300,z3,z4,z6]),(0,[z1,z1301,z7,z3,z4,z6]),(0,[z24,z1,z2,z3,z90,z6]),(0,[z1302,z2,z7,z3,z4,z6])],[(0,[z1,z3,z33,z727,z4,z6]),(0,[z1,z2,z77,z3,z162,z42])],[],[(0,[z135,z2,z7,z3,z4,z779]),(0,[z1303,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z500,z4,z6]),(0,[z1,z2,z7,z3,z6,z940]),(0,[z1160,z2,z77,z3,z4,z6]),(0,[z2,z114,z3,z4,z5,z432])],[(0,[z1,z1304,z7,z3,z4,z6]),(0,[z1,z2,z3,z31,z4,z423]),(0,[z1305,z1,z7,z3,z4,z6])],[],[(0,[z50,z2,z77,z51,z4,z6]),(0,[z1,z1306,z7,z3,z4,z6]),(0,[z1,z97,z3,z4,z175,z6]),(0,[z1307,z1,z2,z7,z3,z6]),(0,[z109,z1,z176,z3,z4,z6]),(0,[z1129,z1,z2,z3,z4,z6]),(0,[z1,z2,z7,z3,z228,z42])],[(0,[z1,z7,z3,z147,z6,z105]),(0,[z1308,z2,z7,z3,z4,z6]),(0,[z660,z2,z277,z3,z4,z6]),(0,[z158,z1,z2,z3,z162,z42]),(0,[z1,z1309,z7,z3,z4,z6])],[(0,[z1,z357,z7,z3,z4,z6]),(0,[z197,z1,z7,z3,z711,z6])],[(0,[z1310,z1,z7,z3,z4,z6])]],
   [[(0,[z1,z16,z3,z31,z4,z6]),(0,[z1,z2,z7,z3,z1311,z6]),(0,[z197,z1,z466,z7,z3,z6]),(0,[z1,z2,z141,z3,z4,z6]),(0,[z1,z1312,z7,z3,z4,z6])],[(0,[z0,z2,z3,z4,z300,z6]),(0,[z22,z7,z3,z4,z6,z432]),(0,[z1,z1313,z7,z3,z4,z6])],[(0,[z1,z394,z22,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z805]),(0,[z182,z52,z7,z3,z4,z6]),(0,[z1,z2,z7,z74,z3,z4]),(0,[z1,z1314,z7,z3,z4,z6])],[(0,[z1,z22,z33,z31,z4,z6]),(0,[z1,z1315,z7,z3,z4,z6]),(0,[z1,z7,z1316,z3,z4,z6])],[(0,[z1,z2,z7,z3,z1317,z6]),(0,[z1,z2,z3,z31,z4,z413]),(0,[z2,z7,z3,z4,z6,z1318]),(0,[z1,z22,z168,z3,z4,z6])],[(0,[z1,z2,z1319,z3,z4,z6]),(0,[z1,z2,z7,z3,z1320,z6]),(0,[z1,z2,z7,z3,z1321,z6])],[(0,[z1,z1322,z7,z3,z4,z6])],[(0,[z1,z2,z3,z1323,z4,z6]),(0,[z48,z1,z77,z33,z4,z6]),(0,[z211,z2,z77,z3,z4,z6]),(0,[z44,z1,z2,z77,z4,z180])],[(0,[z1,z2,z1324,z3,z4,z6]),(0,[z1,z7,z33,z4,z6,z520]),(0,[z1,z2,z3,z162,z62,z42])],[(0,[z1,z2,z260,z3,z4,z6]),(0,[z1,z2,z3,z1325,z4,z6]),(0,[z479,z1,z7,z33,z4,z6]),(0,[z1,z2,z3,z31,z6,z105]),(0,[z1,z2,z3,z31,z4,z465]),(0,[z1,z848,z7,z3,z4,z6]),(0,[z1,z2,z7,z291,z890,z3])],[(0,[z1,z2,z1326,z3,z4,z6]),(0,[z1,z319,z7,z3,z4,z6]),(0,[z392,z7,z3,z33,z4,z6]),(0,[z1,z73,z7,z3,z75,z6]),(0,[z182,z2,z77,z3,z4,z6])],[(0,[z76,z7,z3,z33,z104,z6])],[(0,[z1,z185,z260,z3,z4,z6]),(0,[z767,z1,z7,z3,z4,z57]),(0,[z1,z2,z1081,z3,z4,z6]),(0,[z1,z2,z77,z607,z4,z6]),(0,[z67,z2,z550,z3,z4,z6]),(0,[z249,z1,z2,z7,z6,z39])],[(0,[z135,z2,z7,z3,z4,z272]),(0,[z1,z1327,z7,z3,z4,z6]),(0,[z1,z80,z3,z518,z4,z6]),(0,[z1,z2,z7,z3,z4,z853])],[(0,[z1,z77,z33,z31,z4,z6]),(0,[z1,z230,z77,z3,z4,z6]),(0,[z1,z7,z3,z1328,z4,z6]),(0,[z1,z2,z7,z3,z318,z6])],[(0,[z1,z3,z33,z256,z4,z6]),(0,[z1,z1329,z2,z3,z4,z6])]],
   [[(0,[z1,z1330,z7,z3,z4,z6]),(0,[z1,z2,z1331,z3,z4,z6]),(0,[z1,z77,z3,z4,z203,z6]),(0,[z982,z22,z7,z3,z4,z6]),(0,[z44,z1,z22,z7,z4,z180]),(0,[z333,z2,z422,z3,z4,z6]),(0,[z1,z1332,z7,z3,z4,z6])],[(0,[z1,z2,z80,z3,z4,z6]),(0,[z65,z1,z3,z33,z4,z66]),(0,[z1,z2,z3,z4,z5,z618])],[(0,[z44,z1,z2,z231,z4,z180])],[(0,[z672,z2,z7,z3,z4,z96]),(0,[z1,z85,z7,z3,z378,z6]),(0,[z197,z1,z7,z3,z523,z6])],[(0,[z1,z1333,z7,z3,z4,z6])],[(0,[z1,z2,z1334,z3,z4,z6]),(0,[z1,z2,z77,z623,z4,z6]),(0,[z1,z2,z1335,z3,z4,z6])],[(0,[z1,z1336,z7,z3,z4,z6]),(0,[z1,z7,z3,z1337,z4,z6]),(0,[z1,z2,z7,z3,z90,z120]),(0,[z1,z155,z3,z33,z153,z6]),(0,[z1,z73,z7,z3,z75,z167]),(0,[z1,z77,z3,z4,z147,z6])],[(0,[z1,z2,z3,z31,z4,z6]),(0,[z261,z2,z77,z3,z4,z6]),(0,[z1,z2,z7,z40,z41,z6])],[(0,[z1,z2,z188,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z1338]),(0,[z1,z710,z97,z3,z4,z6]),(0,[z1,z7,z115,z3,z4,z6]),(0,[z1,z1216,z3,z31,z4,z6]),(0,[z1339,z2,z7,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z1340]),(0,[z1,z298,z493,z3,z4,z6]),(0,[z67,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z291,z3,z558]),(0,[z1,z2,z31,z4,z6,z603])],[(0,[z1,z298,z7,z3,z4,z6]),(0,[z1,z1341,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z102]),(0,[z1,z185,z3,z31,z4,z6]),(0,[z1,z7,z3,z33,z1029,z6]),(0,[z109,z1,z3,z31,z4,z140]),(0,[z2,z7,z3,z4,z6,z1342])],[(0,[z1,z7,z3,z1343,z4,z6]),(0,[z1,z2,z1344,z3,z4,z6]),(0,[z1,z237,z176,z3,z4,z6]),(0,[z1,z2,z1345,z3,z4,z6])],[],[(0,[z1,z7,z3,z33,z9,z6]),(0,[z624,z2,z7,z3,z4,z120]),(0,[z1346,z2,z7,z3,z4,z6]),(0,[z1,z7,z3,z1347,z4,z6])],[(0,[z1,z2,z1348,z3,z4,z6])],[(0,[z1,z2,z3,z4,z1349,z6]),(0,[z1350,z1,z2,z3,z4,z6])]],
   [[(1,[z1,z710,z3,z4,z6]),(0,[z660,z2,z7,z3,z4,z28])],[(0,[z1,z2,z7,z3,z1351,z6]),(0,[z1075,z1,z7,z3,z33,z6]),(0,[z1,z77,z3,z4,z221,z6])],[(0,[z682,z1,z2,z31,z4,z6]),(0,[z1,z2,z7,z3,z4,z1352]),(0,[z144,z1,z2,z3,z4,z98]),(0,[z749,z2,z7,z3,z4,z6])],[(0,[z1,z2,z3,z31,z4,z167]),(0,[z44,z1,z2,z31,z4,z180])],[(0,[z1,z1353,z7,z3,z4,z6])],[(0,[z1,z22,z7,z417,z4,z6]),(0,[z1,z2,z277,z3,z157,z6]),(0,[z1,z2,z1354,z3,z4,z6])],[(0,[z1,z2,z7,z730,z4,z6]),(0,[z1,z2,z7,z1117,z3,z4]),(0,[z1355,z1,z2,z3,z4,z6])],[(0,[z1,z2,z7,z3,z4,z1356]),(0,[z626,z2,z7,z3,z4,z96]),(0,[z1,z2,z77,z20,z4,z6]),(0,[z197,z1,z7,z3,z694,z6]),(0,[z72,z1,z2,z77,z291,z3]),(0,[z1,z2,z1357,z3,z4,z6])],[(0,[z1,z7,z3,z33,z4,z83]),(0,[z1,z2,z174,z27,z4,z28])],[(0,[z1,z1358,z7,z3,z4,z6]),(0,[z1,z7,z3,z33,z4,z1055]),(0,[z1,z3,z31,z825,z4,z6])],[(0,[z15,z47,z151,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z1359]),(0,[z1,z7,z439,z33,z4,z6]),(0,[z1,z1211,z77,z3,z4,z6])],[(0,[z392,z22,z7,z3,z4,z6]),(0,[z1,z2,z7,z3,z4,z1360]),(0,[z1,z2,z7,z3,z41,z465])],[(0,[z0,z2,z3,z4,z6,z432]),(0,[z1,z1315,z3,z31,z4,z6]),(0,[z1,z2,z3,z1361,z4,z6])],[(0,[z1,z22,z7,z251,z4,z6]),(0,[z1,z22,z3,z4,z282,z6]),(0,[z1362,z2,z7,z3,z4,z6])],[(0,[z1363,z1,z2,z7,z4,z6]),(0,[z1,z168,z3,z33,z4,z6])],[(0,[z15,z2,z525,z3,z4,z6]),(0,[z1364,z2,z7,z3,z4,z6]),(0,[z1,z33,z31,z4,z6,z180]),(0,[z1,z1365,z7,z3,z4,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 501) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 501).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1014).take 418) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1432)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [501, 513, 418] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 147).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 147).take 169).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 316).take 157).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 473).take 39).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [147, 169, 157, 39] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_37153

theorem PEqualNP.Outside.L_meta_37153 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4274572488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4274572488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37153.solve