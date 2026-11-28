import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45780

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
  Nat.testBit (4008241896 * 2 ^ 32 + 4007692416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0116130d8c386b60#64 ++ 0x1008b0986c61c35b#64 ++ 0xa33e3f1f9c78fffd#64 ++ 0xf519f1f8fce3c7ff#64 : BitVec 256),
   (0x0c4ac862a58b15a0#64 ++ 0x80625643152c58ad#64 ++ 0xdccfc8e3e78f1fff#64 ++ 0xfee67e471f3c78ff#64 : BitVec 256),
   (0xe0a170b47805b8c2#64 ++ 0x2f050b85a3c02dc6#64 ++ 0xe0f1f0fc780ff8ee#64 ++ 0xef078f87e3c07fc7#64 : BitVec 256),
   (0x7601fd007ad01e01#64 ++ 0x0bb00fe803d680f0#64 ++ 0x7f01ff007ff01f17#64 ++ 0xbbf80ff803ff80f8#64 : BitVec 256),
   (0x7bfe0000576ec004#64 ++ 0x63dff00002bb7600#64 ++ 0x7ffe00007fffe007#64 ++ 0x73fff00003ffff00#64 : BitVec 256),
   (0xfffdaedb00000008#64 ++ 0x47ffed76d8000000#64 ++ 0xffffffff80000007#64 ++ 0xcffffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [8, 5]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000400072c01401 0x08000200039600a0 0x0000000063800000 0x00000000031c0000

def z1 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z2 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z3 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z4 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x7ffe00007fffe007 0x73fff00003ffff00

def z5 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z6 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffff80000007 0xcffffffffc000000

def z7 : W := mkw 0xece9e8f271879482 0xaf674f47938c3ca4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z8 : W := mkw 0x73b400005264c004 0x639da00002932600 0x63f00000787fe006 0x631f800003c3ff00

def z9 : W := mkw 0xf601aedb00000008 0x07b00d76d8000000 0xff01ffff80000007 0x8ff80ffffc000000

def z10 : W := mkw 0xffffaedb04284008 0x47fffd76d8214200 0xffffffff9c78e007 0xfffffffffce3c700

def z11 : W := mkw 0xe0a160b070059082 0x2f050b0583802c84 0x40c1c0e060070002 0x0a060e0703003800

def z12 : W := mkw 0xf6a1fdb47ad5bec3 0x2fb50feda3d6adf6 0xfff1fffc7fffffff 0xffff8fffe3ffffff

def z13 : W := mkw 0x084a0062850b01a0 0x804250031428580d 0xdcce00e3e78f00ef 0x76e670071f3c7807

def z14 : W := mkw 0x0116120d8c286960 0x1008b0906c61434b 0xa03e301f9808f8ec 0xe501f180fcc047c7

def z15 : W := mkw 0x16008d0002d00601 0x00b0046800168030 0x1f000f0007f00711 0x10f80078003f8038

def z16 : W := mkw 0x811773bdac397be2 0x1c08bb9ded61cbdf 0xa33fffff9c78fffd 0xfd19fffffce3c7ff

def z17 : W := mkw 0x76008d0052d00601 0x03b0046802968030 0x7f000f007ff00717 0x33f8007803ff8038

def z18 : W := mkw 0x81b602bd842de1e2 0x340db015ec216f0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z19 : W := mkw 0x0000400020001000 0x0000020001000080 0x4001c00060001806 0xaa000e00030000c0

def z20 : W := mkw 0x084a0062850b01a0 0x804250031428580d 0x80ce00e3800f00e8 0x440670071c007807

def z21 : W := mkw 0x720135005a500a01 0x0b9009a802d28050 0x2300370018700000 0x011801b800c38000

def z22 : W := mkw 0x80a000b000058082 0x2405000580002c04 0x00c000e000070000 0x0006000700003800

def z23 : W := mkw 0xfffffffbffdb1fa9 0xcfffffffdffed8fd 0xffffffffffff1fff 0xfffffffffffff8ff

def z24 : W := mkw 0x0000402020011080 0x0000020101000884 0xc0c1c0e0600f18ee 0xee060e07030078c7

def z25 : W := mkw 0x0c4a8842858a0520 0x80625442142c5029 0x1c0e080387800711 0x10e070401c3c0038

def z26 : W := mkw 0xe0a130945804a842 0x2f050984a2c02542 0x2030301c1800e000 0x01018180e0c00700

def z27 : W := mkw 0xf6a1fd947ad4be43 0x2fb50feca3d6a5f2 0x7f31ff1c7ff0ff17 0xbbf98ff8e3ff87f8

def z28 : W := mkw 0xfffdffdb7ad01e09 0x4fffeffedbd680f0 0xfffffffffff01f17 0xffffffffffff80f8

def z29 : W := mkw 0x095c024b00000008 0x404ae01258000000 0x000e000380000000 0x000070001c000000

def z30 : W := mkw 0x600171007ad01e01 0x0b000b8803d680f0 0x6001f0007ff01f16 0xbb000f8003ff80f8

def z31 : W := mkw 0x7ae8000053468004 0x63d74000029a3400 0x5cc0000063870002 0x02e60000031c3800

def z32 : W := mkw 0x8515aedb00000008 0x0428ad76d8000000 0xa33fffff80000005 0xcd19fffffc000000

def z33 : W := mkw 0x7bfe10045f6ee844 0x63dff08022fb7742 0xfffe301c7ffff8ef 0xf7fff180e3ffffc7

def z34 : W := mkw 0x16009d000ad00e01 0x00b004e800568070 0x3f003f001ff01f15 0xb1f801f800ff80f8

def z35 : W := mkw 0x69fe0000552ec004 0x634ff00002a97600 0x60fe0000780fe006 0x6307f00003c07f00

def z36 : W := mkw 0x7601ac0000000000 0x03b00d6000000000 0x7f01ff0000000007 0x8bf80ff800000000

def z37 : W := mkw 0x7f5dae4b00000008 0x43faed7258000000 0x7f0fff0380000007 0x8bf87ff81c000000

def z38 : W := mkw 0x17168f0986f84721 0x10b8b4784c37c239 0x1f0e0f0387f00711 0x10f870781c3f8038

def z39 : W := mkw 0x0116030984384320 0x1008b0184c21c219 0x030e0f0384700711 0x101870781c238038

def z40 : W := mkw 0xfee9acd200000008 0x47f74d6690000000 0x5cc1c0e000000002 0x0ae60e0700000000

def z41 : W := mkw 0xffffbfdf8c386b68 0x57fffdfefc61c35b 0xffffffff9c78ffff 0xfffffffffce3c7ff

def z42 : W := mkw 0x000051007ad01e01 0x0800028803d680f0 0x000000007ff01f10 0x3000000003ff80f8

def z43 : W := mkw 0x89fc02db00000008 0x444fe016d8000000 0x80fe00ff80000000 0x4407f007fc000000

def z44 : W := mkw 0xfae970b47b47b8c6 0x6fd74b85a3da3dc6 0xfcf1f0fc7b8ff8ee 0xefe78f87e3dc7fc7

def z45 : W := mkw 0x7ffc884200000000 0x43ffe44210000000 0xffffc8e380000007 0xcffffe471c000000

def z46 : W := mkw 0xecebf8f6fd8fbde2 0xaf675fc7b7ec7def 0xfcfff8ffff8fffff 0xffe7ffc7fffc7fff

def z47 : W := mkw 0x00a0000000048000 0x2005000000002400 0x00f00000000fe000 0x4007800000007f00

def z48 : W := mkw 0x0000010000100200 0x0000000800008010 0x03000f0004700711 0x1018007800238038

def z49 : W := mkw 0xf6a1fd907ad01e01 0x0fb50fec83d680f0 0xfff1fffc7ff01f17 0xffff8fffe3ff80f8

def z50 : W := mkw 0x0002000004080000 0x0000100000204000 0x000e000004080005 0x7000700000204000

def z51 : W := mkw 0x0000130d88102b60 0x100000986c40815b 0x80003f1f80001ff8 0x840001f8fc0000ff

def z52 : W := mkw 0x7bff35005f7eca05 0x6bdff9a802fbf650 0x7ffe37007fffe007 0x73fff1b803ffff00

def z53 : W := mkw 0xfffdeefb20011088 0x47ffef77d9000884 0xffffffffe00f18ef 0xefffffffff0078c7

def z54 : W := mkw 0xfffffdb47ffffec7 0x6fffffeda3fffff6 0xfffffffc7fffffff 0xffffffffe3ffffff

def z55 : W := mkw 0x72020000576ec004 0x2390100002bb7600 0x7f0000007fffe007 0x33f8000003ffff00

def z56 : W := mkw 0xf601fdb47ad13ec3 0x0fb00feda3d689f6 0xff01fffc7ff01fff 0xbff80fffe3ff80ff

def z57 : W := mkw 0x0114020900000000 0x0008a01048000000 0x803e001f80000000 0x4401f000fc000000

def z58 : W := mkw 0x00025120ffdb1fa1 0x8800128907fed8fd 0x000000007fff1ff8 0x3000000003fff8ff

def z59 : W := mkw 0x60a0000050048000 0x2305000002802400 0x60f00000780fe006 0x6307800003c07f00

def z60 : W := mkw 0xfbff70b47f6ff8c6 0x6fdffb85a3fb7fc6 0xfffff0fc7ffff8ef 0xffffff87e3ffffc7

def z61 : W := mkw 0x7601fd62fad11fa1 0x8bb00feb17d688fd 0xff01ffe3fff01fff 0xbff80fff1fff80ff

def z62 : W := mkw 0xfee9ecf221831488 0xc7f74f67910c18a4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z63 : W := mkw 0x00005024280138c0 0x00000281214009c6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z64 : W := mkw 0x0000110408306a40 0x1000008820418352 0x000000001870e000 0x0000000000c38700

def z65 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0x5cc1c0e0678f1ffa 0x3ae60e07033c78ff

def z66 : W := mkw 0x7601bd0008100a00 0x03b00de800408050 0x7f01ff001c701f17 0xbbf80ff800e380f8

def z67 : W := mkw 0x80a000940004a042 0x24050004a0002502 0x0030001c0000e000 0x00018000e0000700

def z68 : W := mkw 0x095e0000052a4000 0x004af00000295200 0x7ffe00007fffe007 0x73fff00003ffff00

def z69 : W := mkw 0x0c48884200000000 0x0062444210000000 0x5cc1c0e000000002 0x0ae60e0700000000

def z70 : W := mkw 0x0116020d84286160 0x1008b0106c21430b 0x803e001f8008e0e8 0x4401f000fc004707

def z71 : W := mkw 0x7601ec0072c01401 0x0bb00f60039600a0 0x5c01c00063800002 0x0ae00e00031c0000

def z72 : W := mkw 0x09fe0000052ec004 0x604ff00000297600 0x00fe0000000fe000 0x4007f00000007f00

def z73 : W := mkw 0x7fffec0077eed405 0x6bffff6003bf76a0 0x7fffc0007fffe007 0x7bfffe0003ffff00

def z74 : W := mkw 0xe0a1209000000000 0x0705090480000000 0xe0f1f0fc00000006 0xcf078f87e0000000

def z75 : W := mkw 0x0000100408002840 0x0000008020400142 0xa030301c1808f8ec 0xe5018180e0c047c7

def z76 : W := mkw 0x0000000000000000 0x0000000000000000 0x800e080380000005 0xc40070401c000000

def z77 : W := mkw 0x7717ff09fef85f21 0x1bb8bff84ff7c2f9 0x7f0fff03fff01f17 0xbbf87ff81fff80f8

def z78 : W := mkw 0x7601ed0072d01601 0x0bb00f68039680b0 0x5f01cf0067f00713 0x1af80e78033f8038

def z79 : W := mkw 0x00024020a58b15a0 0x80001201052c58ad 0x00000000678f1ff8 0x30000000033c78ff

def z80 : W := mkw 0x0c4a8862850b01a0 0x806254431428580d 0xdccfc8e3800f00ef 0xcee67e471c007807

def z81 : W := mkw 0x0000110008100a00 0x0000008800408050 0x23003f001c701f15 0xb11801f800e380f8

def z82 : W := mkw 0x0400c80020801400 0x00200640010400a0 0x5c01c80067801f17 0xbae00e40033c00f8

def z83 : W := mkw 0xe0a171b47815bac2 0x2f050b8da3c0add6 0xe3f1fffc7c7fffff 0xff1f8fffe3e3ffff

def z84 : W := mkw 0x0114130d08306a40 0x1008a09868418352 0x23303f1c1c70ff15 0xb11981f8e0e387f8

def z85 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x803e3f1f8008fff8 0xc401f1f8fc0047ff

def z86 : W := mkw 0xf3b5269900000008 0x479da934c8000000 0x2330371c00000000 0x011981b8e0000000

def z87 : W := mkw 0x0c4ac800258a1400 0x00625640012c50a0 0x5ccfc800678f1f17 0xfae67e40033c78f8

def z88 : W := mkw 0x0d5c8a4b00000000 0x006ae45258000000 0xffffffff80000007 0xcffffffffc000000

def z89 : W := mkw 0x0d5eca6fa5ab75e0 0x906af6537d2d5baf 0xdcffc8ffe78fffff 0xfee7fe47ff3c7fff

def z90 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x5fce000067f70003 0x12fe7000033fb800

def z91 : W := mkw 0x7bfe000004284000 0x43dff00000214200 0x7ffe00001c78e007 0x73fff00000e3c700

def z92 : W := mkw 0xe0a171b47ad5bec3 0x2f050b8da3d6adf6 0xe0f1f0fc7ffffffe 0xff078f87e3ffffff

def z93 : W := mkw 0x0114020900000000 0x0008a01048000000 0x030e0f0380000001 0x001870781c000000

def z94 : W := mkw 0xe0a160b070059082 0x2f050b0583802c84 0xe0f1f0fc60070006 0xcf078f87e3003800

def z95 : W := mkw 0x7a4a0000574a0000 0x03d2500002ba5000 0x7fce00007fff0007 0x73fe700003fff800

def z96 : W := mkw 0xffffaedb052ec00c 0x67fffd76d8297600 0xffffffff800fe007 0xcffffffffc007f00

def z97 : W := mkw 0x0000500078001800 0x0800028003c000c0 0x0000000078001800 0x2000000003c000c0

def z98 : W := mkw 0x1b5e0000076a4004 0x40daf000003b5200 0x1f0e000007f00001 0x10f87000003f8000

def z99 : W := mkw 0x1f5c8e4b00000008 0x40fae47258000000 0x1f0e0f0380000001 0x00f870781c000000

def z100 : W := mkw 0x0002000084080120 0x0000100004204009 0x800e080384081ffd 0xf40070401c2040ff

def z101 : W := mkw 0x7bfe0000d76ec124 0x63dff00006bb7609 0xfffe0803ffffffff 0xf7fff0401fffffff

def z102 : W := mkw 0x0116020d84286160 0x1008b0106c21430b 0xa33e3f1f8008e0ed 0xc519f1f8fc004707

def z103 : W := mkw 0xe0a120b40005a0c2 0x27050905a0002d06 0xe0f1f0fc000fe0ee 0xcf078f87e0007f07

def z104 : W := mkw 0x00021104df7eeb64 0x3000108826fbf75b 0x000000007ffffff8 0x3000000003ffffff

def z105 : W := mkw 0x000211048c386b60 0x100010882461c35b 0x000000001c78fff8 0x3000000000e3c7ff

def z106 : W := mkw 0x7601fd207ad11e81 0x0bb00fe903d688f4 0xffc1ffe07fff1fff 0xfffe0fff03fff8ff

def z107 : W := mkw 0x7bfc000000000000 0x43dfe00000000000 0x7ffe000000000007 0x43fff00000000000

def z108 : W := mkw 0xffffaedb576ec00c 0x67fffd76dabb7600 0xffffffffffffe007 0xffffffffffffff00

def z109 : W := mkw 0x0116000004284000 0x0008b00000214200 0x233e00001c78e005 0x7119f00000e3c700

def z110 : W := mkw 0x00020020850b01a0 0x800010010428580d 0x00000000000f00e8 0x0000000000007807

def z111 : W := mkw 0x0400d9007ad01e01 0x082006c803d680f0 0x5c01c8007ff01f17 0xbae00e4003ff80f8

def z112 : W := mkw 0x0116530dfef87f61 0x1808b2986ff7c3fb 0xa33e3f1ffff8fffd 0xf519f1f8ffffc7ff

def z113 : W := mkw 0x89fe00b4052fe0c6 0x644ff005a0297f06 0x80fe00fc000fe0e8 0x4407f007e0007f07

def z114 : W := mkw 0x7717ff0dfef87f61 0x1bb8bff86ff7c3fb 0xff3fff1ffff8ffff 0xfff9fff8ffffc7ff

def z115 : W := mkw 0xfee9acd200000008 0x47f74d6690000000 0xfcf1f0fc00000006 0xcfe78f87e0000000

def z116 : W := mkw 0x88ea00f6850fa1e2 0xa4475007b4287d0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z117 : W := mkw 0x68ea0000550e8000 0x2347500002a87400 0x7cfe00007f8fe007 0x73e7f00003fc7f00

def z118 : W := mkw 0x000211048c386b60 0x100010882461c35b 0x800e08039c78fffd 0xf40070401ce3c7ff

def z119 : W := mkw 0x7ffc8e4b00000008 0x43ffe47258000000 0x7ffe0f0380000007 0x43fff0781c000000

def z120 : W := mkw 0xf601ffdb7ad01e09 0x0fb00ffedbd680f0 0xff01fffffff01f17 0xbff80fffffff80f8

def z121 : W := mkw 0x0c48c86220011080 0x0062464311000884 0xdccfc8e3e00f18ef 0xeee67e471f0078c7

def z122 : W := mkw 0x7200000052400000 0x0390000002920000 0x7f0000007ff00007 0x33f8000003ff8000

def z123 : W := mkw 0x0000010002d00601 0x0000000800168030 0x0000000007f00710 0x10000000003f8038

def z124 : W := mkw 0xe0a160b47005b0c2 0x2f050b05a3802d86 0xc0f1c0fc600fe0ea 0x4e078e07e3007f07

def z125 : W := mkw 0xe00170b4780138c2 0x0f000b85a3c009c6 0xe001f0fc780018ee 0xaf000f87e3c000c7

def z126 : W := mkw 0xfee9acd25346800c 0x67f74d66929a3400 0x5cc1c0e063870002 0x0ae60e07031c3800

def z127 : W := mkw 0x8401feff280138ca 0x0c200ff7f94009c6 0x8001ffff800018e8 0x8c000ffffc0000c7

def z128 : W := mkw 0x0114000000204000 0x0008a00000010200 0x233000001870e000 0x0119800000c38700

def z129 : W := mkw 0x1200050002500201 0x0090002800128010 0x0300070000700000 0x0018003800038000

def z130 : W := mkw 0x720135005a500a01 0x0b9009a802d28050 0x7f0037007ff00007 0x33f801b803ff8000

def z131 : W := mkw 0x000050247805b8c2 0x2800028123c02dc6 0x00000000780ff8e8 0x2000000003c07fc7

def z132 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0x7ff1f7fc00000002 0x0bff8fbfe0000000

def z133 : W := mkw 0x095e136f8d3b6be0 0x904af09b7c69db5f 0xa3fe3fff9c7ffffd 0xf51ff1fffce3ffff

def z134 : W := mkw 0x720135005a500a01 0x0b9009a802d28050 0x23003f001c701f15 0xb11801f800e380f8

def z135 : W := mkw 0x0c4ac862258b1480 0x80625643112c58a4 0x5ccfc0e0678f0007 0x7ae67e07033c7800

def z136 : W := mkw 0xf2a170b47a45b8c2 0x2f950b85a3d22dc6 0xfff1f0fc7ffff8ef 0xffff8f87e3ffffc7

def z137 : W := mkw 0x09fe130d8d3eeb64 0x704ff0986c69f75b 0xa3fe3f1f9c7ffffd 0xf51ff1f8fce3ffff

def z138 : W := mkw 0x00020000576ec004 0x2000100002bb7600 0x000000007fffe000 0x3000000003ffff00

def z139 : W := mkw 0x8401aedb00000008 0x04200d76d8000000 0x8001ffff80000000 0x8c000ffffc000000

def z140 : W := mkw 0x7bfe4020f7efd5a4 0xe3dff20107bf7ead 0x7ffe00007fffffff 0x73fff00003ffffff

def z141 : W := mkw 0xffffafdb84384328 0x57fffd7edc21c219 0xffffffff84700717 0xdffffffffc238038

def z142 : W := mkw 0x0516db6facb97fe0 0x9028b6db7d65cbff 0xa33fffff9c78fffd 0xfd19fffffce3c7ff

def z143 : W := mkw 0xfbff2699576ec00c 0x67dff934cabb7600 0x7ffe371c7fffe007 0x73fff1b8e3ffff00

def z144 : W := mkw 0x73b535005a74ca05 0x6b9da9a802d3a650 0x233037001870e000 0x011981b800c38700

def z145 : W := mkw 0xe0a130945804a842 0x2f050984a2c02542 0xa030301c1808f8ec 0xe5018180e0c047c7

def z146 : W := mkw 0x7bfe0209576ec004 0x63dff0104abb7600 0xfffe3f1fffffe007 0xf7fff1f8ffffff00

def z147 : W := mkw 0x7ffec862f7efd5a4 0xe3fff64317bf7ead 0xffffc8e3ffffffff 0xfffffe471fffffff

def z148 : W := mkw 0xf3b576bd7805b8ca 0x6f9dabb5ebc02dc6 0xe3f1f7fc780ff8ee 0xef1f8fbfe3c07fc7

def z149 : W := mkw 0x000251007ffede05 0x2800128803fff6f0 0x000000007fffff10 0x3000000003fffff8

def z150 : W := mkw 0x800170b4280138c2 0x0c000b85a14009c6 0x8001f0fc000018e8 0x8c000f87e00000c7

def z151 : W := mkw 0xe9fd72ff7805b8ca 0x6f4feb97fbc02dc6 0xe0fff0fff80ff8ee 0xef07ff87ffc07fc7

def z152 : W := mkw 0x89fc02db00000008 0x444fe016d8000000 0xa3fe3fff80000005 0xc51ff1fffc000000

def z153 : W := mkw 0x7ee8c86273c79484 0xe3f74643139e3ca4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z154 : W := mkw 0x73b400005264c004 0x639da00002932600 0x233000001870e000 0x0119800000c38700

def z155 : W := mkw 0x80a000b40005a0c2 0x24050005a0002d06 0x80f000fc000fe0e8 0x44078007e0007f07

def z156 : W := mkw 0xfee9ecd272c01409 0x4ff74f66939600a0 0x5cc1c0e063800002 0x0ae60e07031c0000

def z157 : W := mkw 0xfbfe02db576ec00c 0x67dff016dabb7600 0xfffe00ffffffe007 0x77fff007ffffff00

def z158 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xdcffc0ff80000002 0x4ee7fe07fc000000

def z159 : W := mkw 0x7601ec0072c01401 0x0bb00f60039600a0 0x7f01c0007ff00007 0x3bf80e0003ff8000

def z160 : W := mkw 0xfffdaedb5346800c 0x67ffed76da9a3400 0xffffffffe3870007 0xcfffffffff1c3800

def z161 : W := mkw 0x0401fd0028901e01 0x08200fe8014480f0 0x0001ff0000001f10 0x88000ff8000000f8

def z162 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0x9c0fc8e387801ff9 0x9ce07e471c3c00ff

def z163 : W := mkw 0xfbfd209000000000 0x47dfe90480000000 0xfffff0fc00000007 0xcfffff87e0000000

def z164 : W := mkw 0xfae960b073479086 0x6fd74b05839a3c84 0x5cc1c0e063870002 0x0ae60e07031c3800

def z165 : W := mkw 0xece9f8f67805b8c2 0x2f674fc7b3c02dc6 0xfcfff8fff80ff8ef 0xefe7ffc7ffc07fc7

def z166 : W := mkw 0xf6a1fcb47805b8c2 0x2fb50fe5a3c02dc6 0xfff1fffc780ff8ef 0xefff8fffe3c07fc7

def z167 : W := mkw 0x1f5e8e4b858a0528 0xc0faf4725c2c5029 0x1f0e0f0387800711 0x10f870781c3c0038

def z168 : W := mkw 0x7200000000000000 0x0390000000000000 0x7f00000000000007 0x03f8000000000000

def z169 : W := mkw 0xfbfd26db00000008 0x47dfe936d8000000 0xa3fe37ff80000000 0x451ff1bffc000000

def z170 : W := mkw 0x7201240000000000 0x0390092000000000 0x2300370000000000 0x011801b800000000

def z171 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0c1c0e000000006 0xce060e0700000000

def z172 : W := mkw 0x000250247f6ff8c6 0x2800128123fb7fc6 0x000000007ffff8e8 0x3000000003ffffc7

def z173 : W := mkw 0xfffdbedf5804a84a 0x6fffedf6fac02542 0xffffffff9800e007 0xcffffffffcc00700

def z174 : W := mkw 0x0000110008100a00 0x0000008800408050 0x000000001c701f10 0x3000000000e380f8

def z175 : W := mkw 0x0001350008100a01 0x080009a800408050 0x0000370000000000 0x000001b800000000

def z176 : W := mkw 0x1600cd0022d01601 0x00b00668011680b0 0x5f01cf0067f01f17 0xbaf80e78033f80f8

def z177 : W := mkw 0x0c4a8862858b05a0 0x80625443142c582d 0x9cce08e3878f07f9 0x54e670471c3c783f

def z178 : W := mkw 0xecebe8f2f58f95a2 0xaf675f4797ac7cad 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z179 : W := mkw 0xe0a371b4fc3dfbe2 0x3f051b8da7e1efdf 0xe0f1f0fc7c7ffffe 0xff078f87e3e3ffff

def z180 : W := mkw 0x0000402020011080 0x0000020101000884 0x8001c0e0000018e8 0x8c000e07000000c7

def z181 : W := mkw 0x0d5e9b4f8c386b60 0x106af4da7c61c35b 0xffffffff9c78ffff 0xfffffffffce3c7ff

def z182 : W := mkw 0x084a4062a50b11a0 0x804252031528588d 0xc0cfc0e3e00f18ee 0xee067e071f0078c7

def z183 : W := mkw 0x000211048c386b60 0x100010882461c35b 0xa030301c1c78fffc 0xf5018180e0e3c7ff

def z184 : W := mkw 0x0d5edb6fadbb7fe0 0x906af6db7d6ddbff 0xffffffffffffffff 0xffffffffffffffff

def z185 : W := mkw 0x0c48c862a18315a0 0x80624643150c18ad 0xdcc1c8e3e3871ffa 0x8ee60e471f1c38ff

def z186 : W := mkw 0x1f5c8e4b00000008 0x40fae47258000000 0xdfcfcfe380000007 0xcefe7e7f1c000000

def z187 : W := mkw 0x7601ec0020801400 0x03b00f60010400a0 0x7f01ff0067801f17 0xbbf80ff8033c00f8

def z188 : W := mkw 0x7bfc000052400000 0x43dfe00002920000 0x7ffe00007ff00007 0x73fff00003ff8000

def z189 : W := mkw 0xe4a1aedb00000008 0x07250d76d8000000 0xe0f1ffff80000006 0xcf078ffffc000000

def z190 : W := mkw 0x00025124adbb7fe0 0x90001289256ddbff 0x000000007ffffff8 0x3000000003ffffff

def z191 : W := mkw 0x0c4a8842858a0520 0x80625442142c5029 0x9c0e080387881ffd 0xf4e070401c3c40ff

def z192 : W := mkw 0x0400c862a08115a0 0x80200643150408ad 0x8001c8e380001ff8 0x8c000e471c0000ff

def z193 : W := mkw 0xfeebfdf6ffdfbfe3 0xaff75fefb7fefdff 0xffffffffffffffff 0xffffffffffffffff

def z194 : W := mkw 0x0000000000000000 0x0000000000000000 0x230000001c700005 0x3118000000e38000

def z195 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0x80cfc8e3800f1ff8 0xcc067e471c0078ff

def z196 : W := mkw 0x0114020900000000 0x0008a01048000000 0xa33e3f1f80000005 0xc519f1f8fc000000

def z197 : W := mkw 0x0517ff0dacb87f61 0x1828bff86d65c3fb 0xa33fff1f9c78fffd 0xfd19fff8fce3c7ff

def z198 : W := mkw 0x7601fd0028901e01 0x0bb00fe8014480f0 0x7f01ff0000001f17 0x8bf80ff8000000f8

def z199 : W := mkw 0xe0a370b4fc0db9e2 0x2f051b85a7e06dcf 0xe0fff8fffc0fffff 0xff07ffc7ffe07fff

def z200 : W := mkw 0x095e026f852b61e0 0x904af0137c295b0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z201 : W := mkw 0xffffacd2576ec00c 0x67fffd6692bb7600 0x7fffc0e07fffe007 0x7bfffe0703ffff00

def z202 : W := mkw 0x084a0000050a0000 0x0042500000285000 0x5cce0000678f0007 0x72e67000033c7800

def z203 : W := mkw 0x1b5e0000076a4004 0x40daf000003b5200 0x5fce000067ff0007 0x72fe7000033ff800

def z204 : W := mkw 0x7601fd247ad5bec3 0x2bb00fe923d6adf6 0x7f01ff007fffffff 0xbbf80ff803ffffff

def z205 : W := mkw 0x09fe020d852ee164 0x704ff0106c29770b 0x80fe001f800fe0e8 0x4407f000fc007f07

def z206 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x2330371c1c78fff8 0x311981b8e0e3c7ff

def z207 : W := mkw 0x76a1fd007ad49e01 0x2bb50fe803d6a4f0 0x7ff1ff007fffff17 0xfbff8ff803fffff8

def z208 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0x1c0e0803e78f1ff9 0x30e070401f3c78ff

def z209 : W := mkw 0x0114130d08306a40 0x1008a09868418352 0x2330371c1870e000 0x011981b8e0c38700

def z210 : W := mkw 0x0c4ad962ad9b1fa0 0x806256cb156cd8fd 0xffcfffe3ffff1fff 0xfffe7fff1ffff8ff

def z211 : W := mkw 0x7e4bec62f7cb15a1 0x8bf25f6317be58ad 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z212 : W := mkw 0x1f5c8e4b00000008 0x40fae47258000000 0xbf3e3f1f80000005 0xc5f9f1f8fc000000

def z213 : W := mkw 0x1f5e8f4b84384328 0x50faf47a5c21c219 0x1f0e0f0384700711 0x10f870781c238038

def z214 : W := mkw 0x0c48884200000000 0x0062444210000000 0x1c0e080380000001 0x00e070401c000000

def z215 : W := mkw 0x7bfe130ddf7eeb64 0x73dff0986efbf75b 0xfffe3f1fffffffff 0xf7fff1f8ffffffff

def z216 : W := mkw 0xffffffdb7ffede0d 0x6ffffffedbfff6f0 0xffffffffffffff17 0xfffffffffffffff8

def z217 : W := mkw 0x9ffc8edb00000008 0x44ffe476d8000000 0x9ffe0fff80000001 0x44fff07ffc000000

def z218 : W := mkw 0x7bfe0000076a4004 0x43dff000003b5200 0x7ffe000007f00007 0x53fff000003f8000

def z219 : W := mkw 0xedfffbfffdbfffe2 0xbf6fffdfffedffff 0xffffffffffffffff 0xffffffffffffffff

def z220 : W := mkw 0x7601ec0072c01401 0x0bb00f60039600a0 0x7f01ff0063800007 0x8bf80ff8031c0000

def z221 : W := mkw 0xfeebecf2a58b15a8 0xc7f75f67952c58ad 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z222 : W := mkw 0x7e49fd427ad01e01 0x0bf24fea13d680f0 0xffcfffe3fff01f17 0xfffe7fff1fff80f8

def z223 : W := mkw 0x0116020984080120 0x0008b0104c204009 0xa33e3f1f84081ffd 0xf519f1f8fc2040ff

def z224 : W := mkw 0x6001700078001800 0x0b000b8003c000c0 0x6001f00078001806 0xab000f8003c000c0

def z225 : W := mkw 0x1601fd002ad01e01 0x08b00fe8015680f0 0x1f01ff0007f01f11 0x98f80ff8003f80f8

def z226 : W := mkw 0x7f5ffd007ffa5e05 0x4bfaffe803ffd2f0 0x7f0fff007ff01f17 0xbbf87ff803ff80f8

def z227 : W := mkw 0x7ae8000000000000 0x43d7400000000000 0x5cc0000000000002 0x02e6000000000000

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c00000067800007 0x32e00000033c0000

def z229 : W := mkw 0x7e4bfd42ffda1f21 0x8bf25fea17fed0f9 0x7f0fff03fff01f17 0xbbf87ff81fff80f8

def z230 : W := mkw 0xfbfc02db00000008 0x47dfe016d8000000 0xfffe00ff80000007 0x47fff007fc000000

def z231 : W := mkw 0x8dfc8adb00000008 0x446fe456d8000000 0xdcffc8ff80000007 0xcee7fe47fc000000

def z232 : W := mkw 0x0114130d88306b60 0x1008a0986c41835b 0xa3303f1f9870fff8 0x851981f8fcc387ff

def z233 : W := mkw 0x084a4020250b1080 0x0042520101285884 0xdccfc0e0678f18ef 0xfee67e07033c78c7

def z234 : W := mkw 0x7bfe130d8c386b60 0x53dff0986c61c35b 0xfffe3f1f9c78ffff 0xf7fff1f8fce3c7ff

def z235 : W := mkw 0x7ffffd007ffede05 0x6bffffe803fff6f0 0x7fffff007fffff17 0xfbfffff803fffff8

def z236 : W := mkw 0xfffdbedf08002848 0x47ffedf6f8400142 0xffffffff9808f8ef 0xeffffffffcc047c7

def z237 : W := mkw 0x89fe02df84286168 0x544ff016fc21430b 0x80fe00ff8008e0e8 0x4407f007fc004707

def z238 : W := mkw 0x0000000052400000 0x0000000002920000 0x000000007ff00000 0x3000000003ff8000

def z239 : W := mkw 0x7601fc0078001800 0x0bb00fe003c000c0 0x7f01ff0078001807 0xabf80ff803c000c0

def z240 : W := mkw 0x88e800d200000008 0x4447400690000000 0x00c000e000000000 0x0006000700000000

def z241 : W := mkw 0x0c48c86221831480 0x80624643110c18a4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z242 : W := mkw 0x800002db00000008 0x04000016d8000000 0x800000ff80000000 0x04000007fc000000

def z243 : W := mkw 0x61b6130ddc3ceb60 0x330db0986ee1e75b 0xe3fe3f1ffc7fffff 0xf71ff1f8ffe3ffff

def z244 : W := mkw 0xe0a1209050048002 0x2f05090482802400 0x0000000000000000 0x0000000000000000

def z245 : W := mkw 0x7e4bfd62ffdb1fa1 0x8bf25feb17fed8fd 0xffcfffe3ffff1fff 0xfffe7fff1ffff8ff

def z246 : W := mkw 0x7bfe0062d76fc1a4 0xe3dff00316bb7e0d 0xfffe00e3ffffe0ef 0x77fff0071fffff07

def z247 : W := mkw 0xf3b570b47a65f8c6 0x6f9dab85a3d32fc6 0xe3f1f0fc787ff8ee 0xef1f8f87e3c3ffc7

def z248 : W := mkw 0xe9ff70b47d2ff8c6 0x6f4ffb85a3e97fc6 0xe0fff0fc780ff8ee 0xef07ff87e3c07fc7

def z249 : W := mkw 0x7ffe8d0057fec605 0x63fff46802bff630 0x7ffe0f007fffe717 0x73fff07803ffff38

def z250 : W := mkw 0xfffdfeff7805b8ca 0x6fffeff7fbc02dc6 0xfffffffff80ff8ef 0xefffffffffc07fc7

def z251 : W := mkw 0xe0a170b4280138c2 0x0f050b85a14009c6 0xe0f1f0fc000018ee 0xcf078f87e00000c7

def z252 : W := mkw 0x1b5e0309877a4324 0x50daf0184c3bd219 0x1f0e0f0387f00711 0x10f870781c3f8038

def z253 : W := mkw 0x095e0000052a4004 0x404af00000295200 0x000e000000000000 0x0000700000000000

def z254 : W := mkw 0xfffdaedb50048008 0x67ffed76da802400 0xfffffffff80fe007 0xefffffffffc07f00

def z255 : W := mkw 0x1b5e0000076a4004 0x40daf000003b5200 0x3f3e00001ff8e005 0x71f9f00000ffc700

def z256 : W := mkw 0x0848006201030080 0x8042400310081804 0x00c000e000070000 0x0006000700003800

def z257 : W := mkw 0x0c4bfd62ad9b1fa1 0x88625feb156cd8fd 0xdccfffe3e78f1fff 0xfee67fff1f3c78ff

def z258 : W := mkw 0x08e8000001068004 0x6047400000083400 0x00c0000000070000 0x0006000000003800

def z259 : W := mkw 0xe1b773bdfc3dfbe2 0x3f0dbb9defe1efdf 0xe3fffffffc7fffff 0xff1fffffffe3ffff

def z260 : W := mkw 0x0c48c86221831480 0x80624643110c18a4 0xdccfc8e3e3870007 0xcee67e471f1c3800

def z261 : W := mkw 0xf7b5ae9900000008 0x47bdad74c8000000 0x7f31ff1c00000007 0x8bf98ff8e0000000

def z262 : W := mkw 0x0dfec862a5afd5a4 0xe06ff643152d7ead 0xdcffc8e3e78fffff 0xfee7fe471f3c7fff

def z263 : W := mkw 0x0114120d08002840 0x0008a09068400142 0xa33e3f1f9808f8ed 0xe519f1f8fcc047c7

def z264 : W := mkw 0x7603fd04fef87f61 0x1bb01fe827f7c3fb 0x7f01ff007ff8ffff 0xbbf80ff803ffc7ff

def z265 : W := mkw 0x0400c82020811480 0x00200641010408a4 0xdcc1c8e0678f1fff 0xfee60e47033c78ff

def z266 : W := mkw 0x0400c86220811480 0x80200643110408a4 0x0001c0e000000000 0x08000e0700000000

def z267 : W := mkw 0x0116000004284000 0x0008b00000214200 0x030e000004700001 0x1018700000238000

def z268 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xc0c1f0fc600718ea 0x8e060f87e30038c7

def z269 : W := mkw 0xf6a1fdb07ad59e83 0x2fb50fed83d6acf4 0x7fc1ffe07ff71f17 0xbbfe0fff03ffb8f8

def z270 : W := mkw 0x0c48884200000000 0x0062444210000000 0xdccfc8e380000007 0xcee67e471c000000

def z271 : W := mkw 0xe1b772bdfc2df9e2 0x3f0dbb95efe16fcf 0xe0fff0fff80ff8ee 0xef07ff87ffc07fc7

def z272 : W := mkw 0xfffffffffc3dfbea 0x7fffffffffe1efdf 0xfffffffffc7fffff 0xffffffffffe3ffff

def z273 : W := mkw 0xffffaedb858a0528 0xc7fffd76dc2c5029 0xffffffff87800717 0xdffffffffc3c0038

def z274 : W := mkw 0x6001710078101a00 0x0b000b8803c080d0 0x6301ff007c701f17 0xbb180ff803e380f8

def z275 : W := mkw 0x7715ff0d7af07e41 0x1bb8aff86bd783f2 0x7f31ff1c7ff0ff17 0xbbf98ff8e3ff87f8

def z276 : W := mkw 0x73b6130dde7ceb64 0x739db0986ef3e75b 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z277 : W := mkw 0x8dfdaedb00000008 0x446fed76d8000000 0x80ffffff80000000 0xcc07fffffc000000

def z278 : W := mkw 0x7b5e0000576a4004 0x43daf00002bb5200 0x7f0e00007ff00007 0x33f8700003ff8000

def z279 : W := mkw 0x0d5e8b4b85ba4720 0x906af45a5c2dd239 0x1f0e0f0387f00711 0x10f870781c3f8038

def z280 : W := mkw 0x7316000056684000 0x0398b00002b34200 0x7f3e00007ff8e007 0x73f9f00003ffc700

def z281 : W := mkw 0x0000400020801400 0x00000200010400a0 0x0000000067801f10 0x30000000033c00f8

def z282 : W := mkw 0x09fe0000052ec004 0x604ff00000297600 0x5cfe0000678fe007 0x72e7f000033c7f00

def z283 : W := mkw 0x7601ad0002d00601 0x03b00d6800168030 0x7f01ff0007f00717 0x9bf80ff8003f8038

def z284 : W := mkw 0x7bfc00005366c004 0x63dfe000029b3600 0x7ff000007bf7e002 0x03ff800003dfbf00

def z285 : W := mkw 0x1bfe0000076ec004 0x60dff000003b7600 0x1ffe000007ffe001 0x50fff000003fff00

def z286 : W := mkw 0x7fffac00576ec004 0x63fffd6002bb7600 0x7fffff007fffe007 0xfbfffff803ffff00

def z287 : W := mkw 0xfffffeff7f6ff8ce 0x6ffffff7fbfb7fc6 0xfffffffffffff8ef 0xffffffffffffffc7

def z288 : W := mkw 0x8401fdb428913ec3 0x0c200feda14489f6 0x8001fffc00001ff8 0x8c000fffe00000ff

def z289 : W := mkw 0xe1b7339d8c386b60 0x170db99cec61c35b 0xe3ffffff9c78ffff 0xff1ffffffce3c7ff

def z290 : W := mkw 0x0000130d88102b60 0x100000986c40815b 0xa3003f1f9c701ffd 0xb51801f8fce380ff

def z291 : W := mkw 0x0116030d84386360 0x1008b0186c21c31b 0x833e0f1f8478e7f9 0x5419f078fc23c73f

def z292 : W := mkw 0xf3b5269900000008 0x479da934c8000000 0xa33e3f1f80000005 0xc519f1f8fc000000

def z293 : W := mkw 0x00025104fef87f61 0x1800128827f7c3fb 0x000000007ff8fff8 0x3000000003ffc7ff

def z294 : W := mkw 0x0116130ddf7eeb64 0x3008b0986efbf75b 0xa33e3f1ffffffffd 0xf519f1f8ffffffff

def z295 : W := mkw 0x00024020a58b15a0 0x80001201052c58ad 0xc0c1c0e0678f1ffe 0xfe060e07033c78ff

def z296 : W := mkw 0xfee9fcf67805b8ca 0x6ff74fe7b3c02dc6 0xfcf1f0fc780ff8ee 0xefe78f87e3c07fc7

def z297 : W := mkw 0x1f5ece6ba58b15a8 0xc0faf6735d2c58ad 0xdfcfcfe3e78f1fff 0xfefe7e7f1f3c78ff

def z298 : W := mkw 0x0000110408102a40 0x0000008820408152 0xa3303f1c1c78fffd 0xf51981f8e0e3c7ff

def z299 : W := mkw 0x7fffff0dfffeff65 0x7bfffff86ffff7fb 0xffffff1fffffffff 0xfffffff8ffffffff

def z300 : W := mkw 0x00020000076a4004 0x00001000003b5200 0x0000000007f00000 0x10000000003f8000

def z301 : W := mkw 0x7ee9fd007bd69e05 0x6bf74fe803deb4f0 0x7fc1ff007ff71f17 0xbbfe0ff803ffb8f8

def z302 : W := mkw 0x000010045804a842 0x2800008022c02542 0x000000001800e000 0x0000000000c00700

def z303 : W := mkw 0x6000000050000000 0x0300000002800000 0x6000000078000006 0x2300000003c00000

def z304 : W := mkw 0x7601ac0052400000 0x03b00d6002920000 0x7f01ff007ff00007 0xbbf80ff803ff8000

def z305 : W := mkw 0x0401ec0020801401 0x08200f60010400a0 0x0001c00000000000 0x08000e0000000000

def z306 : W := mkw 0x6117730dfc387b60 0x1b08bb986fe1c3db 0xe33fff1ffc78ffff 0xff19fff8ffe3c7ff

def z307 : W := mkw 0xf2a135945a54aa43 0x2f9509aca2d2a552 0x2330371c1870e000 0x011981b8e0c38700

def z308 : W := mkw 0x1f5e8e4b076a400c 0x40faf472583b5200 0x1f0e0f0387f00001 0x10f870781c3f8000

def z309 : W := mkw 0x7601bd005a500a01 0x0bb00de802d28050 0x7f01ff0018700007 0x8bf80ff800c38000

def z310 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x803e001f9c78fff8 0x7401f000fce3c7ff

def z311 : W := mkw 0x72a0000052448000 0x2395000002922400 0x7ff000007fffe007 0x73ff800003ffff00

def z312 : W := mkw 0x0c4ac862f7efd5a4 0xa062564317bf7ead 0xdccfc8e3ffffffff 0xfee67e471fffffff

def z313 : W := mkw 0xffffeefba58b15a8 0xc7ffff77dd2c58ad 0xffffffffe78f1fff 0xffffffffff3c78ff

def z314 : W := mkw 0xf7b5ff997ad01e09 0x4fbdaffccbd680f0 0x7f31ff1c7ff01f17 0xbbf98ff8e3ff80f8

def z315 : W := mkw 0x1600dd007ad01e01 0x08b006e803d680f0 0x1f000f007ff01f11 0x30f8007803ff80f8

def z316 : W := mkw 0xfffdbfdf88102b68 0x57ffedfefc40815b 0xffffffff80001fff 0xcffffffffc0000ff

def z317 : W := mkw 0xfffff8f6ffeffde6 0xefffffc7b7ff7fef 0xfffff8ffffffffff 0xffffffc7ffffffff

def z318 : W := mkw 0x0116020d84286160 0x1008b0106c21430b 0xa33e001f9c78e0ed 0x7519f000fce3c707

def z319 : W := mkw 0x1f5ec862a7eb55a4 0xc0faf643153f5aad 0xdfcfc8e3e7ff1fff 0xfefe7e471f3ff8ff

def z320 : W := mkw 0xecebe8f2a58b15a0 0x87675f47952c58ad 0xfcfff8ffe78f1fff 0xffe7ffc7ff3c78ff

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000080004001f15 0xb0000040002000f8

def z322 : W := mkw 0x7ae8000053468004 0x63d74000029a3400 0x7cf000007b8fe006 0x63e7800003dc7f00

def z323 : W := mkw 0xe9fd22db00000008 0x474fe916d8000000 0xe0fff0ff80000006 0xcf07ff87fc000000

def z324 : W := mkw 0x600170247805b8c2 0x2b000b8123c02dc6 0x6001f000780ff8ee 0xab000f8003c07fc7

def z325 : W := mkw 0x6401fd0078901e01 0x0b200fe803c480f0 0x6001ff0078001f16 0xab000ff803c000f8

def z326 : W := mkw 0x0116020904284000 0x0008b01048214200 0xa33e3f1f9c78e005 0xf519f1f8fce3c700

def z327 : W := mkw 0x0000100408002840 0x0000008020400142 0x2030301c1800e000 0x01018180e0c00700

def z328 : W := mkw 0x0002000484286160 0x100010002421430b 0x000000000008e0e8 0x0000000000004707

def z329 : W := mkw 0xfbff73bdff7ffbe6 0x7fdffb9deffbffdf 0xffffffffffffffff 0xffffffffffffffff

def z330 : W := mkw 0xe0a130945804a842 0x2f050984a2c02542 0x60f0301c780fe006 0x63078180e3c07f00

def z331 : W := mkw 0x0c48c862a08115a0 0x80624643150408ad 0xdccfc8e380001fff 0xcee67e471c0000ff

def z332 : W := mkw 0x0848000001020000 0x0042400000081000 0x5cc0000063870002 0x02e60000031c3800

def z333 : W := mkw 0x60a0000050048000 0x2305000002802400 0x40c0000060070002 0x0206000003003800

def z334 : W := mkw 0x8401f8f6a8813de2 0x8c200fc7b54409ef 0x8001f8ff80001ff8 0x8c000fc7fc0000ff

def z335 : W := mkw 0x0400d90028901e00 0x002006c8014480f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z336 : W := mkw 0xf3b537995a500a09 0x4f9da9bccad28050 0x2330371c18700000 0x011981b8e0c38000

def z337 : W := mkw 0x0116020984284120 0x1008b0104c214209 0x000e000380000000 0x000070001c000000

def z338 : W := mkw 0x0400c80020801400 0x00200640010400a0 0x5c01c00063800002 0x0ae00e00031c0000

def z339 : W := mkw 0x73b400005264c004 0x639da00002932600 0x7f3000007ff0e007 0x33f9800003ff8700

def z340 : W := mkw 0x000051247ad5bec3 0x2800028923d6adf6 0x000000007ffffff8 0x3000000003ffffff

def z341 : W := mkw 0x1b5e0000576ec004 0x60daf00002bb7600 0x1f0e00007fffe001 0x30f8700003ffff00

def z342 : W := mkw 0xe0a130b45805a8c2 0x2f050985a2c02d46 0xa0f030fc180fe0e8 0x45078187e0c07f07

def z343 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x830e3f1f84701ff9 0x941871f8fc2380ff

def z344 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x030e0f039c78fff9 0x301870781ce3c7ff

def z345 : W := mkw 0xe8eb70b47d0fb8c2 0x2f475b85a3e87dc6 0xfcfff0fc7f8ff8ef 0xffe7ff87e3fc7fc7

def z346 : W := mkw 0xf7b5aedb00000008 0x47bdad76d8000000 0xa331ffff80000000 0x8d198ffffc000000

def z347 : W := mkw 0x800170b4280138c2 0x0c000b85a14009c6 0xc0c1f0fc600f18ee 0xee060f87e30078c7

def z348 : W := mkw 0xfffdeefb21831488 0xc7ffef77d90c18a4 0xffffffffe3870007 0xcfffffffff1c3800

def z349 : W := mkw 0x0401fd0028901e01 0x08200fe8014480f0 0x5c01ff0067801f17 0xbae00ff8033c00f8

def z350 : W := mkw 0xe0a160b020011080 0x07050b0581000884 0xe0f1f0fc600f18ee 0xef078f87e30078c7

def z351 : W := mkw 0x00000062800101a0 0x800000031400080d 0x800000e3800000e8 0x040000071c000007

def z352 : W := mkw 0x084a0042850a0120 0x8042500214285009 0x000e000380000000 0x000070001c000000

def z353 : W := mkw 0x8401acd200000008 0x04200d6690000000 0x0001c0e000000000 0x08000e0700000000

def z354 : W := mkw 0xfffdeefba08115a8 0xc7ffef77dd0408ad 0xffffffff80001fff 0xcffffffffc0000ff

def z355 : W := mkw 0x77b5fd007af4de05 0x6bbdafe803d7a6f0 0x7f31ff007ff0ff17 0xbbf98ff803ff87f8

def z356 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0x2030301c780ff8e8 0x21018180e3c07fc7

def z357 : W := mkw 0x084a4062a58b15a0 0x80425203152c58ad 0x80ce00e3e78f1ff8 0x740670071f3c78ff

def z358 : W := mkw 0x72a0000052448004 0x6395000002922400 0x0000000000000000 0x0000000000000000

def z359 : W := mkw 0xe0a160b070059082 0x2f050b0583802c84 0x60f1c0e0780fe006 0x6b078e0703c07f00

def z360 : W := mkw 0x0848004200000000 0x0042400210000000 0x80ce00e380000000 0x440670071c000000

def z361 : W := mkw 0xfbff2090576ec004 0x67dff90482bb7600 0xfffff0fc7fffe007 0xffffff87e3ffff00

def z362 : W := mkw 0x720175007a501a01 0x0b900ba803d280d0 0x6301f70078701806 0xab180fb803c380c0

def z363 : W := mkw 0x7ffec862a58b15a0 0xc3fff643152c58ad 0xffffc8e3e78f1fff 0xfffffe471f3c78ff

def z364 : W := mkw 0xe0a170b078059882 0x2f050b8583c02cc4 0x60c1f0e078071806 0xab060f8703c038c0

def z365 : W := mkw 0xfffffefffd8fbdea 0xeffffff7ffec7def 0xffffffffff8fffff 0xfffffffffffc7fff

def z366 : W := mkw 0xffffaedb076a400c 0x47fffd76d83b5200 0xffffffff87f00007 0xdffffffffc3f8000

def z367 : W := mkw 0x60a0000050048000 0x2305000002802400 0x203000001800e000 0x0101800000c00700

def z368 : W := mkw 0xe0a130945804a842 0x2f050984a2c02542 0xe0f1f0fc1800e006 0xcf078f87e0c00700

def z369 : W := mkw 0x0116000084284120 0x0008b00004214209 0xa33e08039c78fffd 0xf519f0401ce3c7ff

def z370 : W := mkw 0x80a170b42805b8c2 0x2c050b85a1402dc6 0x80f1f0fc000ff8e8 0xcc078f87e0007fc7

def z371 : W := mkw 0xf6a1fcb47ac5bcc3 0x2fb50fe5a3d62de6 0xfcf1f0fc7b8ff8ee 0xefe78f87e3dc7fc7

def z372 : W := mkw 0x7aea0000576ec004 0x63d7500002bb7600 0x5cc000007fffe002 0x32e6000003ffff00

def z373 : W := mkw 0x7bfe1104df7eeb64 0x73dff08826fbf75b 0x7ffe00007fffffff 0x73fff00003ffffff

def z374 : W := mkw 0x01b400000024c004 0x600da00000012600 0x003000000000e000 0x0001800000000700

def z375 : W := mkw 0xe0a000b45005a0c2 0x27050005a2802d06 0xe0f000fc780fe0ee 0x67078007e3c07f07

def z376 : W := mkw 0xe4a1f8f6f885bde2 0xaf250fc7b7c42def 0xe0f1f8fff80ffffe 0xef078fc7ffc07fff

def z377 : W := mkw 0x73b4000000000000 0x439da00000000000 0x2330000000000000 0x0119800000000000

def z378 : W := mkw 0x0001700028001800 0x08000b80014000c0 0x0001f00000001800 0x88000f80000000c0

def z379 : W := mkw 0xe0a170947804b842 0x2f050b84a3c025c2 0x6031f01c7800f806 0xab018f80e3c007c0

def z380 : W := mkw 0x7317370dde786b61 0x1b98b9b86ef3c35b 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z381 : W := mkw 0x7ffdfd007ad01e01 0x4bffefe803d680f0 0x7fffff007ff01f17 0xfbfffff803ff80f8

def z382 : W := mkw 0x0000020d80002160 0x100000106c00010b 0x8000001f800000e8 0x04000000fc000007

def z383 : W := mkw 0x084a0000576ec004 0x2042500002bb7600 0x5cce00007fffe007 0x72e6700003ffff00

def z384 : W := mkw 0x1e4acd62a7db17a1 0x80f2566b153ed8bd 0xdfcfcfe3e7ff1fff 0xfefe7e7f1f3ff8ff

def z385 : W := mkw 0x0400db6fa8913fe0 0x902006db7d4489ff 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z386 : W := mkw 0xfffdbfdf08306a48 0x57ffedfef8418352 0xffffffff9870e007 0xcffffffffcc38700

def z387 : W := mkw 0x7715ae0900000000 0x03b8ad7048000000 0xff3fff1f80000007 0xcff9fff8fc000000

def z388 : W := mkw 0x0000020900000000 0x0000001048000000 0x80003f1f80000000 0x840001f8fc000000

def z389 : W := mkw 0x0116532dadbb7fe0 0x9008b2996d6ddbff 0xa33e3f1ffffffffd 0xf519f1f8ffffffff

def z390 : W := mkw 0x800000b4000120c2 0x04000005a0000906 0x800000fc000000e8 0x04000007e0000007

def z391 : W := mkw 0x011610040c286840 0x0008b08020614342 0xa33e301c1c78f8ed 0xf519f180e0e3c7c7

def z392 : W := mkw 0x7ffec86277efd484 0xe3fff64313bf7ea4 0x7fffc0e07fffe007 0x7bfffe0703ffff00

def z393 : W := mkw 0x6001600070001000 0x0b000b0003800080 0x4001c00060000002 0x0a000e0003000000

def z394 : W := mkw 0x0000000400002040 0x0000000020000102 0x8030001c0008e0e8 0x44018000e0004707

def z395 : W := mkw 0x000050247805b8c2 0x2800028123c02dc6 0xa030301c780ff8ec 0xe5018180e3c07fc7

def z396 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xa031f0fc1800f8e8 0x8d018f87e0c007c7

def z397 : W := mkw 0x1f5e884287ea4524 0xc0faf442143f5229 0x1f0e080387f00711 0x10f870401c3f8038

def z398 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x233e3f1f9c70e711 0x1119f1f8fce38738

def z399 : W := mkw 0x00025024fd8fbde2 0xa800128127ec7def 0x000000007f8ffff8 0x3000000003fc7fff

def z400 : W := mkw 0x0114020d00206040 0x1008a01068010302 0x0030001c0000e000 0x00018000e0000700

def z401 : W := mkw 0xe8eb70f6fd0fb9e2 0xaf475b87b7e87dcf 0xe0fff0fff80ff8ee 0xef07ff87ffc07fc7

def z402 : W := mkw 0x0401ac0000000000 0x00200d6000000000 0x0001ff0000000000 0x88000ff800000000

def z403 : W := mkw 0x0000110008100a00 0x0000008800408050 0x2300370018700000 0x011801b800c38000

def z404 : W := mkw 0x7e49ac4200000000 0x03f24d6210000000 0xffcfffe380000007 0xcffe7fff1c000000

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c00000600f0006 0x6206000003007800

def z406 : W := mkw 0x0c48c86221831480 0x80624643110c18a4 0xdcc1c0e0638f18ee 0xeee60e07031c78c7

def z407 : W := mkw 0x7601bd005ad00e01 0x0bb00de802d68070 0x3f003f001ff00711 0x11f801f800ff8038

def z408 : W := mkw 0x1314060900000008 0x4098a03048000000 0x0300070000000000 0x0018003800000000

def z409 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z410 : W := mkw 0x7601ac0000000000 0x03b00d6000000000 0x5c01c00000000002 0x0ae00e0000000000

def z411 : W := mkw 0x1200000002400000 0x0090000000120000 0x1f00000007f00001 0x10f80000003f8000

def z412 : W := mkw 0x0002000084080120 0x0000100004204009 0x0000000004081ff8 0x30000000002040ff

def z413 : W := mkw 0x7bfe11005f7eca04 0x63dff08802fbf650 0x7ffe3f007fffff17 0xf3fff1f803fffff8

def z414 : W := mkw 0x095e130d8d3a6b60 0x104af0986c69d35b 0xfffe3f1fffffffff 0xf7fff1f8ffffffff

def z415 : W := mkw 0x0000402020011080 0x0000020101000884 0x00000000600f18e8 0x20000000030078c7

def z416 : W := mkw 0x0002000084080120 0x0000100004204009 0x000e080384000711 0x100070401c200038

def z417 : W := mkw 0xe1b5229900000000 0x070da914c8000000 0xe3ffffff80000007 0xcf1ffffffc000000

def z418 : W := mkw 0x0c4ad966adbb7fe0 0x906256cb356ddbff 0xdccfc8e3ffffffff 0xfee67e471fffffff

def z419 : W := mkw 0x0516db0dacb87f60 0x1028b6d86d65c3fb 0xff3fff1ffff8ffff 0xfff9fff8ffffc7ff

def z420 : W := mkw 0xfee9acd200000008 0x47f74d6690000000 0x7fc1ffe000000007 0x8bfe0fff00000000

def z421 : W := mkw 0x7ffec80077eed404 0x63fff64003bf76a0 0x7fffc8007fffff17 0xfbfffe4003fffff8

def z422 : W := mkw 0x0401fd62a8911fa1 0x88200feb154488fd 0x8001ffe380001ff8 0x8c000fff1c0000ff

def z423 : W := mkw 0x7bfe51007ffede05 0x6bdff28803fff6f0 0x7ffe00007fffff17 0x73fff00003fffff8

def z424 : W := mkw 0xfffdbfdb08100a08 0x47ffedfed8408050 0xffffffff9c701f17 0xfffffffffce380f8

def z425 : W := mkw 0x0114000000000000 0x0008a00000000000 0x233e000000000005 0x4119f00000000000

def z426 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0x3f3e3f1f80000001 0x01f9f1f8fc000000

def z427 : W := mkw 0x0000000080000120 0x0000000004000009 0x8000080380001ff8 0x840000401c0000ff

def z428 : W := mkw 0xfffdafdb02d00609 0x47ffed7ed8168030 0xffffffff87f00717 0xdffffffffc3f8038

def z429 : W := mkw 0x6ceac862f58f95a0 0xa367564317ac7cad 0xfcffc8e3ff8fffff 0xffe7fe471ffc7fff

def z430 : W := mkw 0x89fe02fb850b01a8 0xc44ff017dc28580d 0x80fe00ff800f00e8 0x4407f007fc007807

def z431 : W := mkw 0x8c4bf8f6ad8b3de2 0x8c625fc7b56c59ef 0xdccff8ffe78f1fff 0xfee67fc7ff3c78ff

def z432 : W := mkw 0x0116532dfc3dfbe2 0x3808b2996fe1efdf 0xa33e3f1ffc7ffffd 0xf519f1f8ffe3ffff

def z433 : W := mkw 0x0d5ecb6ba5bb57a0 0x906af65b5d2ddabd 0xdfcfcfe3e7ff1fff 0xfefe7e7f1f3ff8ff

def z434 : W := mkw 0x0116020d84286160 0x1008b0106c21430b 0x803e081f8408fffd 0xf401f040fc2047ff

def z435 : W := mkw 0x1314000002604004 0x4098a00000130200 0x0300000000700000 0x0018000000038000

def z436 : W := mkw 0x17169f0d8ef86f61 0x10b8b4f86c77c37b 0xbf3e3f1f9ff8fffd 0xf5f9f1f8fcffc7ff

def z437 : W := mkw 0x80a040b42005b0c2 0x24050205a1002d86 0xc0f1c0fc600ff8ee 0xee078e07e3007fc7

def z438 : W := mkw 0x7ae8000053468004 0x63d74000029a3400 0x7fc000007ff70007 0x33fe000003ffb800

def z439 : W := mkw 0x7600c80072c01400 0x03b00640039600a0 0x7f01c8007ff01f17 0xbbf80e4003ff80f8

def z440 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x7f01f7007bf00002 0x0bf80fb803df8000

def z441 : W := mkw 0xfee9acd200000008 0x47f74d6690000000 0xdccfc8e380000007 0xcee67e471c000000

def z442 : W := mkw 0x0000100408002840 0x0000008020400142 0x8000301c000018e8 0x84000180e00000c7

def z443 : W := mkw 0x0000100408002840 0x0000008020400142 0x000000001808f8e8 0x2000000000c047c7

def z444 : W := mkw 0xf6a1ecb072c59483 0x2fb50f6583962ca4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z445 : W := mkw 0x7bfe0309d77ec324 0x73dff0184ebbf619 0x7ffe0f03ffffe717 0x73fff0781fffff38

def z446 : W := mkw 0x0000402070059082 0x2800020103802c84 0x0000000060070000 0x0000000003003800

def z447 : W := mkw 0x0c4a8842050a0000 0x0062544210285000 0xdccfc8e3e78f0007 0xfee67e471f3c7800

def z448 : W := mkw 0x084a4020a58b15a0 0x80425201052c58ad 0x5cce0000678f1fff 0x72e67000033c78ff

def z449 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x2301ff0018701f10 0x89180ff800c380f8

def z450 : W := mkw 0x0848000000000000 0x0042400000000000 0x5cce000000000007 0x42e6700000000000

def z451 : W := mkw 0xf6a1ac9000000000 0x07b50d6480000000 0xfff1fffc00000007 0xcfff8fffe0000000

def z452 : W := mkw 0x7bfc000050048000 0x63dfe00002802400 0x7ffe0000780fe007 0x63fff00003c07f00

def z453 : W := mkw 0xe0a173bdf815bbe2 0x3f050b9defc0addf 0xe0f1fffff80ffffe 0xef078fffffc07fff

def z454 : W := mkw 0xfffdaeff0005a0ca 0x67ffed77f8002d06 0xffffffff800fe0ef 0xcffffffffc007f07

def z455 : W := mkw 0x7603fd007ffede05 0x2bb01fe803fff6f0 0x7f01ff007fffff17 0xbbf80ff803fffff8

def z456 : W := mkw 0x7201240052400001 0x0b90092002920000 0x0000000000000000 0x0000000000000000

def z457 : W := mkw 0x1f5c8f4b02d00609 0x40fae47a58168030 0x1f0e0f0387f00711 0x10f870781c3f8038

def z458 : W := mkw 0xe0a1209050048000 0x2705090482802400 0xe0f1f0fc780fe006 0xef078f87e3c07f00

def z459 : W := mkw 0x16008c0002c00401 0x00b0046000160020 0x1c00000003800000 0x00e00000001c0000

def z460 : W := mkw 0x720011005a500a00 0x0390008802d28050 0x7f003f007ff01f17 0xb3f801f803ff80f8

def z461 : W := mkw 0x60a0402070059080 0x2305020103802c84 0xe0f1c0e0780ff8ee 0xef078e0703c07fc7

def z462 : W := mkw 0x800170b4280138c2 0x0c000b85a14009c6 0xa031f0fc1808f8ec 0xed018f87e0c047c7

def z463 : W := mkw 0x00025124fc3dfbe2 0x3800128927e1efdf 0x000000007c7ffff8 0x3000000003e3ffff

def z464 : W := mkw 0xe0a1709078001800 0x0f050b8483c000c0 0xe0f1f0fc78001806 0xef078f87e3c000c0

def z465 : W := mkw 0x720051007ad01e01 0x0b90028803d680f0 0x7f0000007ff01f17 0x33f8000003ff80f8

def z466 : W := mkw 0x7603fd00fed81f21 0x0bb01fe807f6c0f9 0xff0fff03fff81fff 0xfff87ff81fffc0ff

def z467 : W := mkw 0x7601ec0072c01401 0x0bb00f60039600a0 0x5c01c80067801f17 0xbae00e40033c00f8

def z468 : W := mkw 0x720175007ad01e01 0x0b900ba803d680f0 0x230037007ff01f10 0x311801b803ff80f8

def z469 : W := mkw 0x7bfe0000052ec004 0x63dff00000297600 0x7ffe0000000fe007 0x43fff00000007f00

def z470 : W := mkw 0x0114030900304200 0x1008a01848018210 0x0300070000700000 0x0018003800038000

def z471 : W := mkw 0xfffdaedb52400008 0x47ffed76da920000 0xfffffffffff00007 0xffffffffffff8000

def z472 : W := mkw 0x084a0062850b01a0 0x804250031428580d 0x80ce08e3840f1ffd 0xf40670471c2078ff

def z473 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0x40c1c0e0780ff8ea 0x2a060e0703c07fc7

def z474 : W := mkw 0x0400c862a08115a0 0x80200643150408ad 0xdc01c8e3e7801fff 0xbee00e471f3c00ff

def z475 : W := mkw 0x7e4bec62a58b15a0 0x83f25f63152c58ad 0xffcfffe3e78f1fff 0xfffe7fff1f3c78ff

def z476 : W := mkw 0x7715ff097ad01e01 0x0bb8aff84bd680f0 0xff3fff1ffff01f17 0xfff9fff8ffff80f8

def z477 : W := mkw 0xfee9fdd27ad01e09 0x4ff74fee93d680f0 0x7fc1ffe07ff01f17 0xbbfe0fff03ff80f8

def z478 : W := mkw 0x084a0000050a0000 0x0042500000285000 0x1c0e000007800001 0x10e07000003c0000

def z479 : W := mkw 0x04008e4b00000008 0x0020047258000000 0x00000f0380000000 0x000000781c000000

def z480 : W := mkw 0xe1b770b47c2df8c2 0x2f0dbb85a3e16fc6 0xe3fff0fc7c7ff8ef 0xff1fff87e3e3ffc7

def z481 : W := mkw 0x0402c862a48915a0 0x80201643152448ad 0x800fc8e384081ffd 0xfc007e471c2040ff

def z482 : W := mkw 0x800170b47805b8c2 0x2c000b85a3c02dc6 0x8001f0fc780ff8e8 0xac000f87e3c07fc7

def z483 : W := mkw 0x00020000050a0000 0x0000100000285000 0x00000000678f0000 0x30000000033c7800

def z484 : W := mkw 0x6001200000000000 0x0300090000000000 0x6001f00000000006 0x8b000f8000000000

def z485 : W := mkw 0x81b613bd8c3debe2 0x340db09dec61ef5f 0xa3fe3fff9c7ffffd 0xf51ff1fffce3ffff

def z486 : W := mkw 0x0c4ad962ffdb1fa1 0x886256cb17fed8fd 0xdccfc8e3ffff1fff 0xfee67e471ffff8ff

def z487 : W := mkw 0x8dfecafba58b15a8 0xc46ff657dd2c58ad 0xdcffc8ffe78f1fff 0xfee7fe47ff3c78ff

def z488 : W := mkw 0xe4a1f8b47885bcc2 0x2f250fc5a3c42de6 0xfcf1f8fc7f8fffff 0xffe78fc7e3fc7fff

def z489 : W := mkw 0xfffdffdb28901e09 0x4fffeffed94480f0 0xffffffff80001f17 0xcffffffffc0000f8

def z490 : W := mkw 0x7e49ec6273c31481 0x8bf24f63139e18a4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z491 : W := mkw 0x00020000858a0520 0x80001000042c5029 0x0000000007800710 0x10000000003c0038

def z492 : W := mkw 0x7ffe8842576ec004 0x63fff44212bb7600 0xffffc8e3ffffe007 0xfffffe471fffff00

def z493 : W := mkw 0x0114130d88102b60 0x1008a0986c40815b 0xa33e3f1f80001ffd 0xc519f1f8fc0000ff

def z494 : W := mkw 0xffffaefb850b01a8 0xc7fffd77dc28580d 0xffffffff800f00ef 0xcffffffffc007807

def z495 : W := mkw 0x0d5ec862a5ab55a0 0x806af643152d5aad 0xffffc8e3ffffffff 0xfffffe471fffffff

def z496 : W := mkw 0x0400c862a08115a0 0x80200643150408ad 0xc0c1c8e3e00f1ffe 0xee060e471f0078ff

def z497 : W := mkw 0xfbfd70b47805b8c2 0x6fdfeb85a3c02dc6 0xfffff0fc780ff8ef 0xefffff87e3c07fc7

def z498 : W := mkw 0x0002000004284000 0x0000100000214200 0x000000001c78e000 0x3000000000e3c700

def z499 : W := mkw 0x084a0000050a0000 0x0042500000285000 0x00ce0000000f0000 0x4006700000007800

def z500 : W := mkw 0x0116030984384320 0x1008b0184c21c219 0x830e0f0384781ffd 0xf41870781c23c0ff

def z501 : W := mkw 0x8401eefba08115a8 0x84200f77dd0408ad 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z502 : W := mkw 0x89fc02ff0005a0ca 0x644fe017f8002d06 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z503 : W := mkw 0xe1b5339d5834ea42 0x3f0da99ceac1a752 0x2330371c1870e000 0x011981b8e0c38700

def z504 : W := mkw 0x9f5daedb00000008 0x44faed76d8000000 0x9f0fffff80000001 0x8cf87ffffc000000

def z505 : W := mkw 0x60a050247805b8c2 0x2b05028123c02dc6 0x60f00000780ff8ee 0x6307800003c07fc7

def z506 : W := mkw 0x0000110008100a00 0x0000008800408050 0x00003f0000001f10 0x800001f8000000f8

def z507 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x5cfe0000638fe002 0x42e7f000031c7f00

def z508 : W := mkw 0x0c4a884284080120 0x0062544214204009 0xdccfc8e384081fff 0xfee67e471c2040ff

def z509 : W := mkw 0x0000002000010080 0x0000000100000804 0x80c000e0000f00e8 0x4406000700007807

def z510 : W := mkw 0x8001309408002842 0x0c000984a0400142 0x0000301c00000000 0x00000180e0000000

def z511 : W := mkw 0x0116532dac397be0 0x1008b2996d61cbdf 0xe3fffffffc7fffff 0xff1fffffffe3ffff

def z512 : W := mkw 0xfffdfedb78001808 0x4fffeff6dbc000c0 0xfffffffff8001807 0xefffffffffc000c0

def z513 : W := mkw 0xe0a1209000000000 0x0705090480000000 0x2030301c00000000 0x01018180e0000000

def z514 : W := mkw 0x1b5c000000000000 0x40dae00000000000 0x1f0e000000000001 0x00f8700000000000

def z515 : W := mkw 0x0c4adb6fad9b3fe0 0x906256db7d6cd9ff 0xdccfffffe78f1fff 0xfee67fffff3c78ff

def z516 : W := mkw 0xf3b5269900000008 0x479da934c8000000 0xe3f1f7fc00000006 0xcf1f8fbfe0000000

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x23003f0000000005 0x811801f800000000

def z518 : W := mkw 0xe0a370b4fd8fbde2 0xaf051b85a7ec7def 0xe0f1f0fc7f8ffffe 0xff078f87e3fc7fff

def z519 : W := mkw 0x09fe0062852fc1a4 0xe04ff00314297e0d 0x80fe00e3800fe0e8 0x4407f0071c007f07

def z520 : W := mkw 0xe4a1feff7805b8ca 0x2f250ff7fbc02dc6 0xe0f1fffff80ff8ee 0xef078fffffc07fc7

def z521 : W := mkw 0x8c49aedb00000008 0x04624d76d8000000 0xdccfffff80000007 0xcee67ffffc000000

def z522 : W := mkw 0xf3b5379d08306a48 0x579da9bce8418352 0x2330371c1870e000 0x011981b8e0c38700

def z523 : W := mkw 0x8401bfdf88102b68 0x14200dfefc40815b 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z524 : W := mkw 0x000210048c082960 0x000010802460414b 0xa03e381f9c08fffd 0xf501f1c0fce047ff

def z525 : W := mkw 0x80a050b47805b8c2 0x2c050285a3c02dc6 0x80f000fc780ff8e8 0x64078007e3c07fc7

def z526 : W := mkw 0xfffdeedb20801408 0x47ffef76d90400a0 0xffffffffe7801f17 0xffffffffff3c00f8

def z527 : W := mkw 0xece9a8d200000000 0x07674d4690000000 0xfcfff8ff80000007 0xcfe7ffc7fc000000

def z528 : W := mkw 0xfffdeedb72c01409 0x4fffef76db9600a0 0xffffffffe3800007 0xcfffffffff1c0000

def z529 : W := mkw 0x0402c862a58b15a0 0x80201643152c58ad 0x8001c8e3e78f1ff8 0xbc000e471f3c78ff

def z530 : W := mkw 0x800160b020011082 0x0c000b0581000884 0x0001c0e000000000 0x08000e0700000000

def z531 : W := mkw 0x7bfc000053468004 0x63dfe000029a3400 0x7ffe000063870007 0x43fff000031c3800

def z532 : W := mkw 0x0400884200000000 0x0020044210000000 0x8001c8e380000000 0x8c000e471c000000

def z533 : W := mkw 0x0000510028901e01 0x08000288014480f0 0x0000000000001f10 0x00000000000000f8

def z534 : W := mkw 0xffffffffadbb7fe8 0xd7fffffffd6ddbff 0xffffffffffffffff 0xffffffffffffffff

def z535 : W := mkw 0x60a1700078049800 0x2b050b8003c024c0 0x60f1f000780ff806 0xeb078f8003c07fc0

def z536 : W := mkw 0x7ffe8e4b576ec00c 0x63fff4725abb7600 0x7ffe0f03ffffe007 0x73fff0781fffff00

def z537 : W := mkw 0x0c48c86221831480 0x80624643110c18a4 0x5cc1c8e067871f17 0xbae60e47033c38f8

def z538 : W := mkw 0xfffdaedb5264c00c 0x67ffed76da932600 0xffffffff9870e007 0xcffffffffcc38700

def z539 : W := mkw 0x01160000576ec004 0x2008b00002bb7600 0x233e00007fffe005 0x7119f00003ffff00

def z540 : W := mkw 0x7e4bfd007fda1e01 0x0bf25fe803fed0f0 0x7fcfff007fff1f17 0xfbfe7ff803fff8f8

def z541 : W := mkw 0x7ffdac0000000000 0x43ffed6000000000 0x7fffff0000000007 0xcbfffff800000000

def z542 : W := mkw 0xfee9ecf27005908a 0x6ff74f6793802c84 0x5cc1c0e060070002 0x0ae60e0703003800

def z543 : W := mkw 0xf2a175b47a55bac3 0x2f950bada3d2add6 0xe3f1f7fc787ff8ee 0xef1f8fbfe3c3ffc7

def z544 : W := mkw 0x61b60000542cc000 0x230db00002a16600 0x63fe00007c7fe007 0x731ff00003e3ff00

def z545 : W := mkw 0x0116030984384320 0x1008b0184c21c219 0x233e0f039c78e715 0x7119f0781ce3c738

def z546 : W := mkw 0x0116030984384320 0x1008b0184c21c219 0xa33e3f1f84700715 0xd519f1f8fc238038

def z547 : W := mkw 0x7ffedb6fffffffe4 0xf3fff6db7fffffff 0xffffffffffffffff 0xffffffffffffffff

def z548 : W := mkw 0xe0a160b070059082 0x2f050b0583802c84 0xc0c1c0e0600f18ee 0xee060e07030078c7

def z549 : W := mkw 0xfee9aedb00000008 0x47f74d76d8000000 0xdcc1ffff80000002 0x8ee60ffffc000000

def z550 : W := mkw 0x7eeac862f7cf95a4 0xe3f7564317be7cad 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z551 : W := mkw 0xe0a1309408002840 0x07050984a0400142 0xe0f1f0fc1808f8ee 0xef078f87e0c047c7

def z552 : W := mkw 0x81b4029900000008 0x440da014c8000000 0x0030001c00000000 0x00018000e0000000

def z553 : W := mkw 0x1f5e9f4f8c386b68 0x50faf4fa7c61c35b 0xbf3e3f1f9c78fffd 0xf5f9f1f8fce3c7ff

def z554 : W := mkw 0x7ee9ec0073c69405 0x6bf74f60039e34a0 0x5cc1c00063870002 0x0ae60e00031c3800

def z555 : W := mkw 0x04008d0000900601 0x0020046800048030 0x00000f0000000710 0x0000007800000038

def z556 : W := mkw 0x000000240005a0c2 0x2000000120002d06 0x00000000000fe0e8 0x0000000000007f07

def z557 : W := mkw 0x0401fd007ad01e01 0x08200fe803d680f0 0x0001ff007ff01f10 0xb8000ff803ff80f8

def z558 : W := mkw 0x0116130d0c386a40 0x1008b0986861c352 0x233e371c1c78e005 0x7119f1b8e0e3c700

def z559 : W := mkw 0xfbff60b0776fd086 0x6fdffb0583bb7e84 0x7fffc0e07fffe007 0x7bfffe0703ffff00

def z560 : W := mkw 0x000050247805b8c2 0x2800028123c02dc6 0xc0c1c0e0780ff8ee 0xee060e0703c07fc7

def z561 : W := mkw 0x0002130d8c386b60 0x100010986c61c35b 0x80003f1f9c78fff8 0xb40001f8fce3c7ff

def z562 : W := mkw 0x8401ffdb28901e09 0x0c200ffed94480f0 0x8001ffff80001f10 0x8c000ffffc0000f8

def z563 : W := mkw 0x73b60000566cc004 0x639db00002b36600 0x233e00001c78e005 0x7119f00000e3c700

def z564 : W := mkw 0x7ffffd62ffffdfa5 0xebffffeb17fffefd 0xffffffe3ffffffff 0xffffffff1fffffff

def z565 : W := mkw 0xf7b7ffbdfefdffe3 0x3fbdbffdeff7efff 0xffffffffffffffff 0xffffffffffffffff

def z566 : W := mkw 0x0c4ad866ad8b3de0 0x806256c3356c59ef 0xfcfff8ffff8fffff 0xffe7ffc7fffc7fff

def z567 : W := mkw 0x7f5dff4b7ad01e09 0x4bfaeffa5bd680f0 0x7f0fff03fff01f17 0xbbf87ff81fff80f8

def z568 : W := mkw 0x0114130d08306a40 0x1008a09868418352 0xa330371c1878f8ec 0xe51981b8e0c3c7c7

def z569 : W := mkw 0x0114130d08306a40 0x1008a09868418352 0xa33e3f1f9870e005 0xc519f1f8fcc38700

def z570 : W := mkw 0x7aea0000574e8004 0x63d7500002ba7400 0x5cce0000678f0007 0x72e67000033c7800

def z571 : W := mkw 0x0401ff0da8903f61 0x18200ff86d4481fb 0x8001ff1f80001ff8 0x8c000ff8fc0000ff

def z572 : W := mkw 0x00004020a08115a0 0x80000201050408ad 0x0000000000001ff8 0x00000000000000ff

def z573 : W := mkw 0x0c4ad866fd8fbde2 0xa86256c337ec7def 0xdccfc8e3ff8fffff 0xfee67e471ffc7fff

def z574 : W := mkw 0x7200000052400000 0x0390000002920000 0x2300000018700000 0x0118000000c38000

def z575 : W := mkw 0xfffdbfdb5a500a09 0x4fffedfedad28050 0xffffffff98700007 0xcffffffffcc38000

def z576 : W := mkw 0x1b5e130d8f7a6b64 0x50daf0986c7bd35b 0xbf3e3f1f9ff8fffd 0xf5f9f1f8fcffc7ff

def z577 : W := mkw 0xfbfd269900000008 0x47dfe934c8000000 0x7ffe371c00000007 0x43fff1b8e0000000

def z578 : W := mkw 0x73b60000576ec004 0x639db00002bb7600 0x233000007fffe000 0x3119800003ffff00

def z579 : W := mkw 0x0d5eca6ba58b15a0 0x806af6535d2c58ad 0xffffffffe78f1fff 0xffffffffff3c78ff

def z580 : W := mkw 0x73b4130d5a74ea44 0x739da0986ad3a752 0x2330371c1870e000 0x011981b8e0c38700

def z581 : W := mkw 0x0401fd0028901e01 0x08200fe8014480f0 0x2301ff001c701f15 0xb9180ff800e380f8

def z582 : W := mkw 0x0000000053468004 0x20000000029a3400 0x0000000063870000 0x00000000031c3800

def z583 : W := mkw 0x000211008c180b20 0x000010880460c059 0xa30e3f039c781ffd 0xf51871f81ce3c0ff

def z584 : W := mkw 0x8c4beefba58b15a8 0x84625f77dd2c58ad 0xdccfffffe78f1fff 0xfee67fffff3c78ff

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000000818ec 0xe4000000000040c7

def z586 : W := mkw 0x1e4a8d4287da0721 0x80f2546a143ed039 0x1f0e0f0387f00711 0x10f870781c3f8038

def z587 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x23fe0000187fe000 0x411ff00000c3ff00

def z588 : W := mkw 0x7bfc00005264c004 0x63dfe00002932600 0x7ffe00001870e007 0x43fff00000c38700

def z589 : W := mkw 0x011613098c384b20 0x1008b0984c61c259 0x230e3f039c701f15 0xb11871f81ce380f8

def z590 : W := mkw 0xfbfe00b4576fe0c6 0x67dff005a2bb7f06 0xfffe00fc7fffe0ef 0x77fff007e3ffff07

def z591 : W := mkw 0x7601fd047ad03e41 0x0bb00fe823d681f2 0xff31ff1c7ff8ffff 0xfff98ff8e3ffc7ff

def z592 : W := mkw 0x7bfe4020776fd084 0x63dff20103bb7e84 0xffffc0e07ffff8ef 0xfffffe0703ffffc7

def z593 : W := mkw 0xfbff30945f6ee846 0x6fdff984a2fb7742 0x7ffe301c7fffe007 0x73fff180e3ffff00

def z594 : W := mkw 0x7316130dde786b60 0x1398b0986ef3c35b 0xff3e3f1ffff8ffff 0xf7f9f1f8ffffc7ff

def z595 : W := mkw 0x0c4a8842858a0520 0x80625442142c5029 0xdccfc8e387800717 0xdee67e471c3c0038

def z596 : W := mkw 0x7bfe020dd76ee164 0x73dff0106ebb770b 0xfffe001fffffe0ef 0x77fff000ffffff07

def z597 : W := mkw 0x0000030980100320 0x100000184c008019 0x00000f0380000710 0x000000781c000038

def z598 : W := mkw 0xe1b7339ddc3ceb62 0x3f0db99ceee1e75b 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z599 : W := mkw 0x011611048c386b60 0x1008b0882461c35b 0x233e00001c78fffd 0x7119f00000e3c7ff

def z600 : W := mkw 0x011611000c384a00 0x0008b0880061c250 0x233e3f001c78ff15 0xf119f1f800e3c7f8

def z601 : W := mkw 0xf3b5369d5804a84a 0x6f9da9b4eac02542 0x2330371c1800e000 0x011981b8e0c00700

def z602 : W := mkw 0x000000005264c004 0x2000000002932600 0x000000001870e000 0x0000000000c38700

def z603 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0x5ccfc8e3e7870713 0x1ae67e471f3c3838

def z604 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0x5fcfcfe380000003 0x0afe7e7f1c000000

def z605 : W := mkw 0x89fe13df8c386b68 0x544ff09efc61c35b 0xa3fe3fff9c78fffd 0xf51ff1fffce3c7ff

def z606 : W := mkw 0x0402c820a58b15a0 0x80201641052c58ad 0x5c01c800678f1fff 0xbae00e40033c78ff

def z607 : W := mkw 0x0400880000000000 0x0020044000000000 0x5c01c80000000007 0x8ae00e4000000000

def z608 : W := mkw 0x6001300058000800 0x0b00098002c00040 0x2000300018000000 0x0100018000c00000

def z609 : W := mkw 0x16008c0000000000 0x00b0046000000000 0x1f000f0000000001 0x00f8007800000000

def z610 : W := mkw 0x0400880000800400 0x0020044000040020 0x1c00080007800711 0x10e00040003c0038

def z611 : W := mkw 0x0000130d08102a40 0x1000009868408152 0x0000371c00000000 0x000001b8e0000000

def z612 : W := mkw 0x0c4ac842a58a1520 0x80625642152c50a9 0x5c0fc803e7801f17 0xbae07e401f3c00f8

def z613 : W := mkw 0xe0a1209000000000 0x0705090480000000 0x40c1c0e000000002 0x0a060e0700000000

def z614 : W := mkw 0x0000000050048000 0x2000000002802400 0x00000000780fe000 0x2000000003c07f00

def z615 : W := mkw 0x6401f80078801c00 0x0b200fc003c400e0 0x7c01f8007f801f17 0xbbe00fc003fc00f8

def z616 : W := mkw 0x0c48c84220801400 0x00624642110400a0 0xdccfc8e3e7801f17 0xfee67e471f3c00f8

def z617 : W := mkw 0xf3b7379d8c386b68 0x579db9bcec61c35b 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z618 : W := mkw 0x8001209000000000 0x0400090480000000 0x8001f0fc00000000 0x8c000f87e0000000

def z619 : W := mkw 0x0c48884201820400 0x80624442100c1020 0x1c00000003800000 0x00e00000001c0000

def z620 : W := mkw 0xffffaedf84286168 0x57fffd76fc21430b 0xffffffff8008e0ef 0xcffffffffc004707

def z621 : W := mkw 0x7717bf0d8c386b60 0x13b8bdf86c61c35b 0xff3fff1f9c78ffff 0xfff9fff8fce3c7ff

def z622 : W := mkw 0x1e488c4200000008 0x40f2446210000000 0x1c00000000000000 0x00e0000000000000

def z623 : W := mkw 0x0c4a8842858a0520 0x80625442142c5029 0x5cce0803e78f0717 0x72e670401f3c7838

def z624 : W := mkw 0x7bfe50247f6ff8c6 0x6bdff28123fb7fc6 0x7ffe00007ffff8ef 0x73fff00003ffffc7

def z625 : W := mkw 0x0000402020011080 0x0000020101000884 0x40c1c0e060070002 0x0a060e0703003800

def z626 : W := mkw 0x000051007ad01e01 0x0800028803d680f0 0x23003f007ff01f15 0xb11801f803ff80f8

def z627 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xdccfc0e3e38f00ea 0x4ee67e071f1c7807

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x203000001808e004 0x6101800000c04700

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0xa030301c00000004 0xc5018180e0000000

def z630 : W := mkw 0xece9f8f67987bcc2 0xaf674fc7b3cc3de6 0xfcf1f0fc7b8ff8ee 0xefe78f87e3dc7fc7

def z631 : W := mkw 0x0000402021831480 0x80000201010c18a4 0x0000000063870000 0x00000000031c3800

def z632 : W := mkw 0x0002130d8c182b60 0x100010986c60c15b 0x800e3f1f84081ffd 0xf40071f8fc2040ff

def z633 : W := mkw 0x60a0000000000000 0x0305000000000000 0x60f0000000000006 0x4307800000000000

def z634 : W := mkw 0x89fe02db052ec00c 0x644ff016d8297600 0x80fe00ff800fe000 0x4407f007fc007f00

def z635 : W := mkw 0x7603fd20ffdb1fa1 0x8bb01fe907fed8fd 0x7f01ff007fff1fff 0xbbf80ff803fff8ff

def z636 : W := mkw 0x60a010045804a840 0x2305008022c02542 0xe0f0301c780ff8ee 0xe7078180e3c07fc7

def z637 : W := mkw 0x09fe0000576ec004 0x604ff00002bb7600 0x00fe00007fffe000 0x7007f00003ffff00

def z638 : W := mkw 0x720170007a401800 0x0b900b8003d200c0 0x7f01f0007ff01807 0xbbf80f8003ff80c0

def z639 : W := mkw 0x000011005a500a01 0x0800008802d28050 0x0000000018700000 0x0000000000c38000

def z640 : W := mkw 0x0d5e9b4f8dba6f60 0x906af4da7c6dd37b 0xbf3e3f1f9ff8fffd 0xf5f9f1f8fcffc7ff

def z641 : W := mkw 0x0114130908100a00 0x0008a09848408050 0xa33e3f1f9c701f15 0xf519f1f8fce380f8

def z642 : W := mkw 0xf2a1249000000008 0x4795092480000000 0x0000000000000000 0x0000000000000000

def z643 : W := mkw 0x0114020900000000 0x0008a01048000000 0x2330371c00000000 0x011981b8e0000000

def z644 : W := mkw 0x0000110488102b60 0x100000882440815b 0x0000000000001ff8 0x00000000000000ff

def z645 : W := mkw 0x1a48000003420004 0x40d24000001a1000 0x1c00000003800000 0x00e00000001c0000

def z646 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x5c01c0007ff01f12 0x3ae00e0003ff80f8

def z647 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xa33e371f9878e0e8 0x4519f1b8fcc3c707

def z648 : W := mkw 0xffffaedb050a0008 0x47fffd76d8285000 0xffffffffe78f0007 0xffffffffff3c7800

def z649 : W := mkw 0x80a010b40805a8c2 0x24050085a0402d46 0xa0f030fc180ff8ec 0xe5078187e0c07fc7

def z650 : W := mkw 0x7601ff0dfad03f61 0x1bb00ff86fd681fb 0xff01ff1ffff01fff 0xbff80ff8ffff80ff

def z651 : W := mkw 0x8001269900000008 0x04000934c8000000 0x0000371c00000000 0x000001b8e0000000

def z652 : W := mkw 0x7e4ac862f7cb15a0 0x83f2564317be58ad 0xffcfc8e3ffff1fff 0xfffe7e471ffff8ff

def z653 : W := mkw 0xffffaedb84080128 0x47fffd76dc204009 0xffffffff84081fff 0xfffffffffc2040ff

def z654 : W := mkw 0x00024020a40911a0 0x000012010520488d 0xc0cfc8e3e40f1fff 0xfe067e471f2078ff

def z655 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x3f3e00001ff0e001 0x11f9f00000ff8700

def z656 : W := mkw 0xfffdffff7ad5becb 0x6fffeffffbd6adf6 0xffffffffffffffff 0xffffffffffffffff

def z657 : W := mkw 0x6c4bf862fd8b1da0 0x8b625fc317ec58ed 0xfccff8e3ff8f1fff 0xffe67fc71ffc78ff

def z658 : W := mkw 0x8ceac8f6a58fb5e2 0xa4675647b52c7daf 0xdcffc8ffe78fffff 0xfee7fe47ff3c7fff

def z659 : W := mkw 0x80a0009000000000 0x0405000480000000 0x80f000fc00000000 0x44078007e0000000

def z660 : W := mkw 0xf3b530945a64e846 0x6f9da984a2d32742 0x2330301c1870e000 0x01198180e0c38700

def z661 : W := mkw 0x0002000084080120 0x0000100004204009 0x800e0003800800e8 0x440070001c004007

def z662 : W := mkw 0xe4a1fdb47895bec3 0x2f250feda3c4adf6 0xe0f1fffc780ffffe 0xef078fffe3c07fff

def z663 : W := mkw 0x00020000052ec004 0x2000100000297600 0x00000000000fe000 0x0000000000007f00

def z664 : W := mkw 0x7200000052400000 0x0390000002920000 0x5c00000063800002 0x02e00000031c0000

def z665 : W := mkw 0x7bfc020900000000 0x43dfe01048000000 0xfffe3f1f80000007 0xc7fff1f8fc000000

def z666 : W := mkw 0xfffdacd200000008 0x47ffed6690000000 0x7fffc0e000000007 0x4bfffe0700000000

def z667 : W := mkw 0xf3b526995264c00c 0x679da934ca932600 0x2330371c1870e000 0x011981b8e0c38700

def z668 : W := mkw 0x00024020a58b15a0 0x80001201052c58ad 0x800e0803e78f1ffd 0xf40070401f3c78ff

def z669 : W := mkw 0x7f5fff6ffffb7fe1 0x9bfafffb7fffdbff 0xffffffffffffffff 0xffffffffffffffff

def z670 : W := mkw 0x7e49fd627bd31e81 0x8bf24feb13de98f4 0x7fc1ffe07ff71f17 0xbbfe0fff03ffb8f8

def z671 : W := mkw 0x09fe0000052ec004 0x604ff00000297600 0x23fe00001c7fe005 0x711ff00000e3ff00

def z672 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0x60f1f0fc7807e002 0x0b078f87e3c03f00

def z673 : W := mkw 0x7315370d5a706a41 0x1b98a9b86ad38352 0x2330371c1870e000 0x011981b8e0c38700

def z674 : W := mkw 0x7ffe8842d7eec524 0xe3fff44216bf7629 0x7ffe0803ffffe717 0x73fff0401fffff38

def z675 : W := mkw 0x7717fd007ef85e01 0x0bb8bfe803f7c2f0 0x7f3fff007ff8ff17 0xfbf9fff803ffc7f8

def z676 : W := mkw 0x0000100008000800 0x0000008000400040 0x2000300018001804 0xa100018000c000c0

def z677 : W := mkw 0x0116000004284000 0x0008b00000214200 0x003e00000008e000 0x4001f00000004700

def z678 : W := mkw 0xffffbfdfdf7eeb6c 0x77fffdfefefbf75b 0xffffffffffffffff 0xffffffffffffffff

def z679 : W := mkw 0x0400c80020801400 0x00200640010400a0 0x0001c80000001f10 0x88000e40000000f8

def z680 : W := mkw 0xfffdfeff280138ca 0x4fffeff7f94009c6 0xffffffff800018ef 0xcffffffffc0000c7

def z681 : W := mkw 0xe1b573bd7835fac2 0x3f0dab9debc1afd6 0xe3f1f7fc787ff8ee 0xef1f8fbfe3c3ffc7

def z682 : W := mkw 0x084a0000850a0120 0x0042500004285009 0xdcce0803e78f1fff 0xf6e670401f3c78ff

def z683 : W := mkw 0x800173bda8113be2 0x1c000b9ded4089df 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z684 : W := mkw 0x00024020f7efd5a4 0xa000120107bf7ead 0x000000007ffffff8 0x3000000003ffffff

def z685 : W := mkw 0x1f5e8d0007fa4605 0x40faf468003fd230 0x1f0e0f0007f00711 0x10f87078003f8038

def z686 : W := mkw 0x000211048c386b60 0x100010882461c35b 0x23003f001c78fffd 0xb11801f800e3c7ff

def z687 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x5c01ff0063801f12 0x8ae00ff8031c00f8

def z688 : W := mkw 0x7bfe0000050a0000 0x43dff00000285000 0x7ffe0000678f0007 0x73fff000033c7800

def z689 : W := mkw 0x0402c800a4881520 0x00201640052440a9 0xdc0fc803e7881fff 0xfee07e401f3c40ff

def z690 : W := mkw 0xfffdeefb7005908a 0x6fffef77db802c84 0xffffffffe0070007 0xcfffffffff003800

def z691 : W := mkw 0x60a20000576ec004 0x2305100002bb7600 0x60f000007fffe006 0x7307800003ffff00

def z692 : W := mkw 0x7601fc007ac01c01 0x0bb00fe003d600e0 0x7c01f0007b801806 0xabe00f8003dc00c0

def z693 : W := mkw 0xe1b572bd7805b8c2 0x2f0dab95ebc02dc6 0xe3fffffff80ff8ef 0xef1fffffffc07fc7

def z694 : W := mkw 0x6001702078011880 0x0b000b8103c008c4 0xe0c1f0e0780f18ee 0xef060f8703c078c7

def z695 : W := mkw 0x00005024280138c2 0x08000281214009c6 0x00000000000018e8 0x00000000000000c7

def z696 : W := mkw 0x6001700478003840 0x0b000b8023c001c2 0xe031f01c7808f8ee 0xef018f80e3c047c7

def z697 : W := mkw 0xffffffdffef87f69 0x5ffffffefff7c3fb 0xfffffffffff8ffff 0xffffffffffffc7ff

def z698 : W := mkw 0x8517bfdf8c386b68 0x1428bdfefc61c35b 0xa33fffff9c78fffd 0xfd19fffffce3c7ff

def z699 : W := mkw 0x0000130d88102b60 0x100000986c40815b 0xa0303f1f9808fffc 0xe50181f8fcc047ff

def z700 : W := mkw 0x09fc000000000000 0x404fe00000000000 0x00fe000000000000 0x4007f00000000000

def z701 : W := mkw 0x0002010084384320 0x100010080421c219 0x0000000004700710 0x1000000000238038

def z702 : W := mkw 0x7bff70007f6ed804 0x6bdffb8003fb76c0 0x7ffff0007ffff807 0xfbffff8003ffffc0

def z703 : W := mkw 0xe0a370b47f6ff8c6 0x2f051b85a3fb7fc6 0xe0f1f0fc7ffff8ee 0xff078f87e3ffffc7

def z704 : W := mkw 0x7bfe130d5f7eea44 0x73dff0986afbf752 0x7ffe371c7fffe007 0x73fff1b8e3ffff00

def z705 : W := mkw 0xffffeefbf7efd5ac 0xe7ffff77dfbf7ead 0xffffffffffffffff 0xffffffffffffffff

def z706 : W := mkw 0x0400884280800520 0x8020044214040029 0x0000080380000710 0x000000401c000038

def z707 : W := mkw 0x1600dd247ad5bec3 0x28b006e923d6adf6 0x1f000f007ffffff9 0x30f8007803ffffff

def z708 : W := mkw 0x7a4a0000576ec004 0x23d2500002bb7600 0x7fce00007fffe007 0x73fe700003ffff00

def z709 : W := mkw 0x1f5cde6f7805b8ca 0x68fae6f37bc02dc6 0x1f0e0f03f80ff8e9 0x20f870781fc07fc7

def z710 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xe0f1f0fc780fe0ea 0x4f078f87e3c07f07

def z711 : W := mkw 0x16009d005ad00e01 0x08b004e802d68070 0x1f000f001ff00711 0x10f8007800ff8038

def z712 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xdccfc8e3e38f1ffa 0xcee67e471f1c78ff

def z713 : W := mkw 0xe0a170b47ac5bcc3 0x2f050b85a3d62de6 0xe0f1f0fc7b8ff8ee 0xef078f87e3dc7fc7

def z714 : W := mkw 0x80a040b42005b0c2 0x24050205a1002d86 0x80f1c0fc000ff8e8 0xcc078e07e0007fc7

def z715 : W := mkw 0xf6a1fdb47ad5bec3 0x2fb50feda3d6adf6 0x7f31ff1c7fffffff 0xbbf98ff8e3ffffff

def z716 : W := mkw 0x0dfffd002dbede05 0x686fffe8016df6f0 0x00ffff00000fff10 0xc807fff800007ff8

def z717 : W := mkw 0x8401ffff28913ecb 0x0c200ffff94489f6 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z718 : W := mkw 0x000050247805b8c2 0x2800028123c02dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z719 : W := mkw 0x7ae8130ddb56ab64 0x73d740986edab55b 0xdcc03f1fe3871ffa 0x86e601f8ff1c38ff

def z720 : W := mkw 0xf6a1fd907ad01e09 0x4fb50fec83d680f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z721 : W := mkw 0x1f5e8e4b87ea452c 0xc0faf4725c3f5229 0x1f0e0f0387f00711 0x10f870781c3f8038

def z722 : W := mkw 0xece9aedb00000008 0x07674d76d8000000 0xfcffffff80000007 0xcfe7fffffc000000

def z723 : W := mkw 0x12020000576ec004 0x2090100002bb7600 0x1f0000007fffe001 0x30f8000003ffff00

def z724 : W := mkw 0x7601fd247ad13ec1 0x0bb00fe923d689f6 0xfff1fffc7fffffff 0xffff8fffe3ffffff

def z725 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xe3f1f0fc7c7ff8ef 0xff1f8f87e3e3ffc7

def z726 : W := mkw 0x720051007ad01e01 0x0b90028803d680f0 0x7f003f007ff01f17 0xb3f801f803ff80f8

def z727 : W := mkw 0xe0a040b47005b0c2 0x27050205a3802d86 0xe0f1c0fc780ff8ee 0xef078e07e3c07fc7

def z728 : W := mkw 0x1601bd000ad00e01 0x08b00de800568070 0x1f003f0007f00711 0x10f801f8003f8038

def z729 : W := mkw 0x8c49aedb00000008 0x04624d76d8000000 0x9c0fffff80000001 0x8ce07ffffc000000

def z730 : W := mkw 0xecebb8d6dd8ead62 0xaf675dc6b6ec756b 0x3c3e381f9f80e711 0x11e1f1c0fcfc0738

def z731 : W := mkw 0x7aea0000574e8000 0x23d7500002ba7400 0x7ffe00007fffe007 0x73fff00003ffff00

def z732 : W := mkw 0x084a0000576ec004 0x2042500002bb7600 0x5cc000007fffe002 0x32e6000003ffff00

def z733 : W := mkw 0x7600d9007ad01e00 0x03b006c803d680f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z734 : W := mkw 0x00020000576ec004 0x2000100002bb7600 0x5c0000007fffe007 0x32e0000003ffff00

def z735 : W := mkw 0xfffdaedb5264c00c 0x67ffed76da932600 0xfffffffff87fe007 0xefffffffffc3ff00

def z736 : W := mkw 0x80a000b40005a0c2 0x24050005a0002d06 0xc0f1c0fc000fe0ee 0xce078e07e0007f07

def z737 : W := mkw 0x77b4c862f2e5d5a4 0xe3bda64317972ead 0xa331c8e39870fff8 0x8d198e471cc387ff

def z738 : W := mkw 0x0402c820a48915a0 0x00201641052448ad 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z739 : W := mkw 0x8401fdf6a8913fe3 0x8c200fefb54489ff 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z740 : W := mkw 0xe0a120b45005a0c2 0x27050905a2802d06 0xe0f1f0fc780fe0ee 0xef078f87e3c07f07

def z741 : W := mkw 0xfffdaedb02400008 0x47ffed76d8120000 0xffffffff87f00007 0xdffffffffc3f8000

def z742 : W := mkw 0xfeebbdd68c386b68 0x57f75deeb461c35b 0x5cc1c0e01c78fffa 0x3ae60e0700e3c7ff

def z743 : W := mkw 0x9f5daedb00000008 0x44faed76d8000000 0xdfcfffff80000007 0xcefe7ffffc000000

def z744 : W := mkw 0xfee9ecf273c79483 0xaff74f67939e3ca4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z745 : W := mkw 0x7717ee0df6e87561 0x1bb8bf706fb743ab 0xdc3fc01fe388e0ea 0x4ee1fe00ff1c4707

def z746 : W := mkw 0xfbff2299576ec004 0x67dff914cabb7600 0xffffffffffffe007 0xffffffffffffff00

def z747 : W := mkw 0x7200010052500200 0x0390000802928010 0x7f000f007ff00717 0x33f8007803ff8038

def z748 : W := mkw 0x095e024b852a4120 0x904af0125c295209 0x000e000380000000 0x000070001c000000

def z749 : W := mkw 0x720175007ad01e01 0x0b900ba803d680f0 0x7f0037007ff01f17 0x33f801b803ff80f8

def z750 : W := mkw 0xfbff22db576ec00c 0x67dff916dabb7600 0xfffff0ffffffe007 0xffffff87ffffff00

def z751 : W := mkw 0xf6a1fd947ad03e41 0x0fb50feca3d681f2 0xfff1fffc7ff8ffff 0xffff8fffe3ffc7ff

def z752 : W := mkw 0xfbfe02db576ec00c 0x67dff016dabb7600 0xfffe3fffffffe007 0xf7fff1ffffffff00

def z753 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x5fce00007fffe003 0x32fe700003ffff00

def z754 : W := mkw 0x7600cd0072d01601 0x03b00668039680b0 0x7f01cf007ff01f17 0xbbf80e7803ff80f8

def z755 : W := mkw 0x89fc53db7ad01e09 0x4c4fe29edbd680f0 0x80fe00fffff01f10 0x7407f007ffff80f8

def z756 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0xff0fff03fff01f17 0xfff87ff81fff80f8

def z757 : W := mkw 0x60017024780138c0 0x0b000b8123c009c6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z758 : W := mkw 0x76a1fd007ad49e01 0x2bb50fe803d6a4f0 0x7fc1ff007ff71f17 0xbbfe0ff803ffb8f8

def z759 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0x233e3f1f9c78fff9 0x3119f1f8fce3c7ff

def z760 : W := mkw 0x7bff2400576ec005 0x6bdff92002bb7600 0x7ffe00007fffe007 0x73fff00003ffff00

def z761 : W := mkw 0x7a4b3562df5b0ba1 0x8bd259ab16fad85d 0xa3ce37e3987f00e8 0x451e71bf1cc3f807

def z762 : W := mkw 0xe1b763b9f43dd3a2 0x3f0dbb1dcfa1ee9d 0x43cfcfe3e4770713 0x1a1e7e7f1f23b838

def z763 : W := mkw 0xfee9ecf273c7948c 0xe7f74f67939e3ca4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z764 : W := mkw 0x7601ed0022d01601 0x03b00f68011680b0 0x7f01ff0067f01f17 0xbbf80ff8033f80f8

def z765 : W := mkw 0x8403aedb576ec00c 0x24201d76dabb7600 0x8001ffffffffe000 0xbc000fffffffff00

def z766 : W := mkw 0xf7b5aedb00000008 0x47bdad76d8000000 0xa33fffff80000005 0xcd19fffffc000000

def z767 : W := mkw 0x00025124fefdffe3 0x3800128927f7efff 0x000000007ffffff8 0x3000000003ffffff

def z768 : W := mkw 0xfffdaedb52448008 0x67ffed76da922400 0xffffffffffffe007 0xffffffffffffff00

def z769 : W := mkw 0xf6a1fdb47ad5bec3 0x2fb50feda3d6adf6 0xffc1fffc7ff71fff 0xbffe0fffe3ffb8ff

def z770 : W := mkw 0x00025124fffb7fe1 0x9800128927ffdbff 0x000000007ffffff8 0x3000000003ffffff

def z771 : W := mkw 0x00025124ac397be0 0x100012892561cbdf 0x000000007c7ffff8 0x3000000003e3ffff

def z772 : W := mkw 0xf2a171b47a55bac2 0x2f950b8da3d2add6 0xfff1fffc7fffffff 0xffff8fffe3ffffff

def z773 : W := mkw 0x09fe0000576ec004 0x604ff00002bb7600 0x5cfe00007fffe007 0x72e7f00003ffff00

def z774 : W := mkw 0xfffdaedb50048008 0x67ffed76da802400 0xffffffff9800e007 0xcffffffffcc00700

def z775 : W := mkw 0x00025124ffdfbfe3 0xa800128927fefdff 0x000000007ffffff8 0x3000000003ffffff

def z776 : W := mkw 0xe0a130b40805a8c2 0x27050985a0402d46 0xe0f1f0fc180ff8ee 0xef078f87e0c07fc7

def z777 : W := mkw 0x00025124ff7ffbe6 0x3800128927fbffdf 0x000000007ffffff8 0x3000000003ffffff

def z778 : W := mkw 0xf6a1fdb07ad59e83 0x2fb50fed83d6acf4 0xfff1fffc7ff71f17 0xffff8fffe3ffb8f8

def z779 : W := mkw 0x7601bd005ad00e01 0x0bb00de802d68070 0x7f01ff001ff00717 0x9bf80ff800ff8038

def z780 : W := mkw 0x8401ffbda8913fe3 0x1c200ffded4489ff 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z781 : W := mkw 0x7200000052448000 0x2390000002922400 0x7f0000007fffe007 0x33f8000003ffff00

def z782 : W := mkw 0x9b5f70b42f6b78c6 0x4cdafb85a17b5bc6 0x9f0ff0fc07f018e9 0x9cf87f87e03f80c7

def z783 : W := mkw 0x7601fd247ad13ec3 0x0bb00fe923d689f6 0x7f01ff007ff01fff 0xbbf80ff803ff80ff

def z784 : W := mkw 0x0c48c86220811480 0x00624643110408a4 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z785 : W := mkw 0x0401fd2428913ec3 0x08200fe9214489f6 0x0001ff0000001ff8 0x88000ff8000000ff

def z786 : W := mkw 0x800170b4280138c2 0x0c000b85a14009c6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z787 : W := mkw 0x1f5e8f4b85ba4728 0xd0faf47a5c2dd239 0x1f0e0f0387f00711 0x10f870781c3f8038

def z788 : W := mkw 0x0c48c862a18315a0 0x80624643150c18ad 0xdccfc8e3e3871fff 0xcee67e471f1c38ff

def z789 : W := mkw 0xe0a170b47a45b8c2 0x2f050b85a3d22dc6 0xe0f1f0fc7ffff8ee 0xff078f87e3ffffc7

def z790 : W := mkw 0x00025124ffffffe4 0xb000128927ffffff 0x000000007ffffff8 0x3000000003ffffff

def z791 : W := mkw 0x0114020900000000 0x0008a01048000000 0xe3ffffff80000007 0xcf1ffffffc000000

def z792 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x7f01ff007ff00713 0x1bf80ff803ff8038

def z793 : W := mkw 0x8dfc8adb00000008 0x446fe456d8000000 0xffffffff80000007 0xcffffffffc000000

def z794 : W := mkw 0xe0a171b47815bac2 0x2f050b8da3c0add6 0xe3f1f7fc787ff8ee 0xef1f8fbfe3c3ffc7

def z795 : W := mkw 0xe0a170b47885bcc2 0x2f050b85a3c42de6 0xe0f1f0fc7f8ffffe 0xff078f87e3fc7fff

def z796 : W := mkw 0xfee9ecf272c5948b 0x6ff74f6793962ca4 0x5cc1c0e063870002 0x0ae60e07031c3800

def z797 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xfffff7ff80000002 0x4fffffbffc000000

def z798 : W := mkw 0x7601fd207ad11e81 0x0bb00fe903d688f4 0x7fc1ffe07ff71f17 0xbbfe0fff03ffb8f8

def z799 : W := mkw 0x7f5dae4b00000000 0x03faed7258000000 0xffffffff80000007 0xcffffffffc000000

def z800 : W := mkw 0xf3b5379d5a74ea4c 0x779da9bcead3a752 0x2330371c1870e000 0x011981b8e0c38700

def z801 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0x5ccfc8e3e78f1ffb 0x3ae67e471f3c78ff

def z802 : W := mkw 0xedfdaedb00000008 0x476fed76d8000000 0xe0ffffff80000006 0xcf07fffffc000000

def z803 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xe0fff8fff80ff8ef 0xef07ffc7ffc07fc7

def z804 : W := mkw 0x095e0000576ec004 0x204af00002bb7600 0x7ffe00007fffe007 0x73fff00003ffff00

def z805 : W := mkw 0xf6a1fdb07ad59e83 0x2fb50fed83d6acf4 0xffc1ffe07fff1fff 0xfffe0fff03fff8ff

def z806 : W := mkw 0x73b60000566cc000 0x239db00002b36600 0x7ffe00007fffe007 0x73fff00003ffff00

def z807 : W := mkw 0x7bfe0042d76ec124 0xe3dff00216bb7609 0x7ffe0003ffffe007 0x73fff0001fffff00

def z808 : W := mkw 0xfffdaedb0260400c 0x47ffed76d8130200 0xffffffff80700007 0xcffffffffc038000

def z809 : W := mkw 0xf7b5ae9900000000 0x07bdad74c8000000 0xffffffff80000007 0xcffffffffc000000

def z810 : W := mkw 0x1f5e8f4b87fa4721 0x90faf47a5c3fd239 0x1f0e0f0387f00711 0x10f870781c3f8038

def z811 : W := mkw 0x76008d0052d00601 0x03b0046802968030 0x5f000f0067f00713 0x12f80078033f8038

def z812 : W := mkw 0xf6a1fd947ad4be43 0x2fb50feca3d6a5f2 0x7ff1ff1c7fffff17 0xfbff8ff8e3fffff8

def z813 : W := mkw 0x8dfdaedb00000008 0x446fed76d8000000 0xa3ffffff80000005 0xcd1ffffffc000000

def z814 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xe3ffffff9c78ffff 0xff1ffffffce3c7ff

def z815 : W := mkw 0x8d5daedb00000008 0x446aed76d8000000 0x800fffff80000000 0x8c007ffffc000000

def z816 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x7ff000007fffe002 0x33ff800003ffff00

def z817 : W := mkw 0x1f5c8e4b00000008 0x40fae47258000000 0xffffffff80000007 0xcffffffffc000000

def z818 : W := mkw 0x7601fd207ad59e83 0x2bb00fe903d6acf4 0x7f01ff007ff71f17 0xbbf80ff803ffb8f8

def z819 : W := mkw 0x89fe02ff852b61e8 0xd44ff017fc295b0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z820 : W := mkw 0x73160000576ec004 0x2398b00002bb7600 0x7f3e00007fffe007 0x73f9f00003ffff00

def z821 : W := mkw 0xf3b5379d5a54aa4b 0x6f9da9bcead2a552 0x2330371c1870e000 0x011981b8e0c38700

def z822 : W := mkw 0xfffdaedb5346800c 0x67ffed76da9a3400 0xfffffffffb8fe007 0xefffffffffdc7f00

def z823 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x7fc1ff007fff1f17 0xfbfe0ff803fff8f8

def z824 : W := mkw 0x120011000a500a00 0x0090008800528050 0x3f003f001ff01f15 0xb1f801f800ff80f8

def z825 : W := mkw 0x7aea0000576ec004 0x63d7500002bb7600 0x5cce00007fffe007 0x72e6700003ffff00

def z826 : W := mkw 0x720135005a500a01 0x0b9009a802d28050 0x7f003f007ff01f17 0xb3f801f803ff80f8

def z827 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xc0f1c0fc780ff8ea 0x6e078e07e3c07fc7

def z828 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffff9808e007 0xeffffffffcc04700

def z829 : W := mkw 0x76a08d0052d48601 0x23b504680296a430 0x7ff00f007fffe717 0x73ff807803ffff38

def z830 : W := mkw 0x0114130d08102a40 0x0008a09868408152 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z831 : W := mkw 0x16008d0052d00601 0x00b0046802968030 0x1f000f007ff00711 0x30f8007803ff8038

def z832 : W := mkw 0xf3b766b9a58b15a8 0xc79dbb35cd2c58ad 0x2330371c678f1ff8 0x311981b8e33c78ff

def z833 : W := mkw 0xfffdaedb50000008 0x47ffed76da800000 0xfffffffff8000007 0xefffffffffc00000

def z834 : W := mkw 0x7601bd005a500a00 0x03b00de802d28050 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z835 : W := mkw 0x16009d000ad00e01 0x00b004e800568070 0x1f000f001ff01f11 0x30f8007800ff80f8

def z836 : W := mkw 0x16008d0002d00601 0x00b0046800168030 0x5f000f0067f00717 0x32f80078033f8038

def z837 : W := mkw 0x7bfe0000d76ec124 0x63dff00006bb7609 0x7ffe00007fffffff 0x73fff00003ffffff

def z838 : W := mkw 0x084a130d8d1a2b60 0x104250986c68d15b 0xdcce3f1fe78f1fff 0xf6e671f8ff3c78ff

def z839 : W := mkw 0x0400d9007ad01e01 0x082006c803d680f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z840 : W := mkw 0xfffdaedb01020008 0x47ffed76d8081000 0xffffffffe3870007 0xcfffffffff1c3800

def z841 : W := mkw 0xf6a1bd945ad4ae43 0x2fb50deca2d6a572 0x3f303f1c1ff0e711 0x11f981f8e0ff8738

def z842 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0xfffe0803ffffe007 0xf7fff0401fffff00

def z843 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xa3ffffff80000000 0xcd1ffffffc000000

def z844 : W := mkw 0xf6a1fdb47ad5bec3 0x2fb50feda3d6adf6 0x7ff1fffc7ff7ff17 0xbbff8fffe3ffbff8

def z845 : W := mkw 0x0400890000900600 0x0020044800048030 0x1f000f0007f00711 0x10f80078003f8038

def z846 : W := mkw 0x7601ed0072d01601 0x0bb00f68039680b0 0x5f01cf0067f01f17 0xbaf80e78033f80f8

def z847 : W := mkw 0x1a4a0000576ec004 0x60d2500002bb7600 0x1c0000007fffe000 0x30e0000003ffff00

def z848 : W := mkw 0x96a08db402d5a6c3 0x24b5046da016ad36 0x9ff00ffc07ffe7f9 0x54ff807fe03fff3f

def z849 : W := mkw 0xf601fdd27ad01e09 0x0fb00fee93d680f0 0x7f01ffe07ff01f17 0xbbf80fff03ff80f8

def z850 : W := mkw 0x0116020984284120 0x0008b0104c214209 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z851 : W := mkw 0xfbfd26db00000008 0x47dfe936d8000000 0xe3fff7ff80000006 0xcf1fffbffc000000

def z852 : W := mkw 0x7bfe0209576ec004 0x63dff0104abb7600 0xfffe001fffffe007 0x77fff000ffffff00

def z853 : W := mkw 0x1600dd007ad01e01 0x08b006e803d680f0 0x3f003f007ff01f15 0xb1f801f803ff80f8

def z854 : W := mkw 0x76a1fd007ad01e01 0x0bb50fe803d680f0 0x7ff1ff007ff01f17 0xfbff8ff803ff80f8

def z855 : W := mkw 0x1600dd002ad01e01 0x00b006e8015680f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z856 : W := mkw 0x73b60000576ec004 0x639db00002bb7600 0x7f3000007fffe007 0x33f9800003ffff00

def z857 : W := mkw 0x7bfe024b576ec00c 0x63dff0125abb7600 0x7ffe0003ffffe007 0x73fff0001fffff00

def z858 : W := mkw 0x7bfc000052448000 0x63dfe00002922400 0x7ffe00007fffe007 0x73fff00003ffff00

def z859 : W := mkw 0x76a1fd007ad49e05 0x6bb50fe803d6a4f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z860 : W := mkw 0x1b5e0000076a4004 0x40daf000003b5200 0x7ffe00007fffe007 0x73fff00003ffff00

def z861 : W := mkw 0xf6a1fd947ad4be43 0x2fb50feca3d6a5f2 0xff31ff1c7ff8ffff 0xfff98ff8e3ffc7ff

def z862 : W := mkw 0x16008d0002d00601 0x00b0046800168030 0x3f003f0007f00715 0x91f801f8003f8038

def z863 : W := mkw 0xfffdaedb5004800a 0x6fffed76da802400 0xffffffff80000007 0xcffffffffc000000

def z864 : W := mkw 0x7601fd627ad11e81 0x8bb00feb13d688f4 0x7f01ffe07ff01f17 0xbbf80fff03ff80f8

def z865 : W := mkw 0xf6a1edb072d59683 0x2fb50f6d8396acb4 0x5fc1cfe067f70713 0x1afe0e7f033fb838

def z866 : W := mkw 0xfffdaedb00800408 0x47ffed76d8040020 0xffffffff87800717 0xdffffffffc3c0038

def z867 : W := mkw 0x0400c90020901600 0x00200648010480b0 0x5f01cf0067f01f17 0xbaf80e78033f80f8

def z868 : W := mkw 0x09fe0209852ec124 0x704ff0104c297609 0x00fe0003800fe000 0x4007f0001c007f00

def z869 : W := mkw 0xf6a1fd907ad49e01 0x2fb50fec83d6a4f0 0xfff1fffc7fffff17 0xffff8fffe3fffff8

def z870 : W := mkw 0xfffdaedb5366c00c 0x67ffed76da9b3600 0xfffffffffbf7e007 0xcfffffffffdfbf00

def z871 : W := mkw 0xe4a1f9b47895bec2 0x2f250fcda3c4adf6 0xfff1fffc7fffffff 0xffff8fffe3ffffff

def z872 : W := mkw 0x89fe02bd852fe1e6 0x744ff015ec297f0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z873 : W := mkw 0xf6a1fdb47ad5bec3 0x2fb50feda3d6adf6 0x7fc1ffe07fffffff 0xbbfe0fff03ffffff

def z874 : W := mkw 0x084a0000052a4000 0x0042500000295200 0x5cce00007fffe007 0x72e6700003ffff00

def z875 : W := mkw 0xf6a1fdb07ad59e83 0x2fb50fed83d6acf4 0x7ff1ffe07fffff17 0xfbff8fff03fffff8

def z876 : W := mkw 0xfbff2090576ec004 0x67dff90482bb7600 0x7fffc0e07fffe007 0x7bfffe0703ffff00

def z877 : W := mkw 0x7b5e0000576a4000 0x03daf00002bb5200 0x7ffe00007fffe007 0x73fff00003ffff00

def z878 : W := mkw 0xf2a174b47a45b8c3 0x2f950ba5a3d22dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z879 : W := mkw 0xf2a174b47805b8ca 0x6f950ba5a3c02dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z880 : W := mkw 0x0c4ac862a5ab55a0 0x80625643152d5aad 0xdccfc8e3ffffffff 0xfee67e471fffffff

def z881 : W := mkw 0x7601fd247ad5bec3 0x2bb00fe923d6adf6 0xffc1ffe07fffffff 0xfffe0fff03ffffff

def z882 : W := mkw 0xf6a1fdb47ad5bec3 0x2fb50feda3d6adf6 0xff31fffc7ff0ffff 0xbff98fffe3ff87ff

def z883 : W := mkw 0xfbfe00d2576ec00c 0x67dff00692bb7600 0x7ffe00e07fffe007 0x73fff00703ffff00

def z884 : W := mkw 0x16009d000ad00e01 0x00b004e800568070 0x1f003f0007f01f11 0x90f801f8003f80f8

def z885 : W := mkw 0x7aea0000576ec004 0x63d7500002bb7600 0x7cf000007fffe006 0x73e7800003ffff00

def z886 : W := mkw 0x095e026b852b41a0 0x904af0135c295a0d 0x80ce00e3800f00e8 0x440670071c007807

def z887 : W := mkw 0x0d5cdb6f29b37ec0 0x906ae6db794d9bf6 0x7ff1f7fc7bf7e002 0x0bff8fbfe3dfbf00

def z888 : W := mkw 0x80a040b42005b0c2 0x24050205a1002d86 0xc0f1c0fc600fe0ea 0x4e078e07e3007f07

def z889 : W := mkw 0x00025124acb97fe0 0x900012892565cbff 0x000000001c78fff8 0x3000000000e3c7ff

def z890 : W := mkw 0x095e024f852a6160 0x904af0127c29530b 0x803e001f8008e0e8 0x4401f000fc004707

def z891 : W := mkw 0x7601ad0052d00601 0x03b00d6802968030 0x7f01ff007ff00717 0xbbf80ff803ff8038

def z892 : W := mkw 0x00004024200130c0 0x0000020121000986 0xc0f1c0fc600ff8ee 0xee078e07e3007fc7

def z893 : W := mkw 0x7601bd005ad00e01 0x0bb00de802d68070 0x3f003f001ff01f15 0xb1f801f800ff80f8

def z894 : W := mkw 0x7bfe0209d76ec124 0x63dff0104ebb7609 0xfffe3f1fffffffff 0xf7fff1f8ffffffff

def z895 : W := mkw 0x7601bd000ad00e01 0x03b00de800568070 0x7f01ff001ff01f17 0xbbf80ff800ff80f8

def z896 : W := mkw 0x1601ed0022d01601 0x08b00f68011680b0 0x1f01cf0007f00711 0x18f80e78003f8038

def z897 : W := mkw 0xfffdaedb0342000c 0x47ffed76d81a1000 0xffffffff83800007 0xcffffffffc1c0000

def z898 : W := mkw 0x1bfe0000576ec004 0x60dff00002bb7600 0x1ffe00007fffe001 0x70fff00003ffff00

def z899 : W := mkw 0x1f5e8b4b87fa4724 0xd0faf45a5c3fd239 0x1f0e0f0387f00711 0x10f870781c3f8038

def z900 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x7ffe00007ff7e003 0x13fff00003ffbf00

def z901 : W := mkw 0x80a170b47805b8c2 0x2c050b85a3c02dc6 0x80f1f0fc780ff8e8 0xec078f87e3c07fc7

def z902 : W := mkw 0x7600dd007ad01e01 0x0bb006e803d680f0 0x7f000f007ff01f17 0x33f8007803ff80f8

def z903 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xc0f1f0fc600ff8ea 0xce078f87e3007fc7

def z904 : W := mkw 0x095e0209852a4124 0x504af0104c295209 0x000e000380000000 0x000070001c000000

def z905 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xa0f1f0fc180ff8e8 0xcd078f87e0c07fc7

def z906 : W := mkw 0x76008d0052d00601 0x03b0046802968030 0x3f000f001ff00711 0x11f8007800ff8038

def z907 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x3f003f007ff01f11 0x31f801f803ff80f8

def z908 : W := mkw 0x7601fd207ad11e81 0x0bb00fe903d688f4 0x7f01ff007fff1fff 0xbbf80ff803fff8ff

def z909 : W := mkw 0x7bff2400576ec004 0x63dff92002bb7600 0x7ffe37007fffe007 0x73fff1b803ffff00

def z910 : W := mkw 0x000211048c182b60 0x000010882460c15b 0xa33e3f1f9c78fffd 0xf519f1f8fce3c7ff

def z911 : W := mkw 0x7bfe0209d76ec124 0x73dff0104ebb7609 0x7ffe0003ffffe007 0x73fff0001fffff00

def z912 : W := mkw 0xfee9acd200000000 0x07f74d6690000000 0xffffffff80000007 0xcffffffffc000000

def z913 : W := mkw 0x76008d0002d00601 0x03b0046800168030 0x7f000f0007f00717 0x13f80078003f8038

def z914 : W := mkw 0xfbff2090576ec004 0x67dff90482bb7600 0x7ffe301c7fffe007 0x73fff180e3ffff00

def z915 : W := mkw 0xf6a1fdb07ad11e81 0x0fb50fed83d688f4 0xfff1fffc7fff1fff 0xffff8fffe3fff8ff

def z916 : W := mkw 0x7601ad0002d00601 0x03b00d6800168030 0x3f003f0007f00711 0x11f801f8003f8038

def z917 : W := mkw 0x09fe026f852fe1e4 0xf04ff0137c297f0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z918 : W := mkw 0x76a1fd047ad4be41 0x2bb50fe823d6a5f2 0xfff1ff1c7fffffff 0xffff8ff8e3ffffff

def z919 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xa33e3f1f9878fff8 0xc519f1f8fcc3c7ff

def z920 : W := mkw 0x7601fd047ad4be43 0x2bb00fe823d6a5f2 0x7f01ff007ff0ff17 0xbbf80ff803ff87f8

def z921 : W := mkw 0x7bfe0209576ec004 0x63dff0104abb7600 0x7ffe0f03ffffe007 0x73fff0781fffff00

def z922 : W := mkw 0x09fe0000052ec004 0x604ff00000297600 0x7ffe00007fffe007 0x73fff00003ffff00

def z923 : W := mkw 0xf601fdb47ad5bec3 0x2fb00feda3d6adf6 0xff01fffc7fffffff 0xbff80fffe3ffffff

def z924 : W := mkw 0x16008d0002d00601 0x00b0046800168030 0x3f000f001ff00715 0x31f8007800ff8038

def z925 : W := mkw 0x1600cd0022d01601 0x00b00668011680b0 0x1f01cf0007f01f11 0x98f80e78003f80f8

def z926 : W := mkw 0xf6a1fd907ad01e01 0x0fb50fec83d680f0 0x7fc1ffe07ff01f17 0xbbfe0fff03ff80f8

def z927 : W := mkw 0x0d5e8a4b85aa4520 0x906af4525c2d5229 0x1c0e080387800711 0x10e070401c3c0038

def z928 : W := mkw 0xf2a175b47ad5bec3 0x2f950bada3d6adf6 0xe3f1f7fc7ffffffe 0xff1f8fbfe3ffffff

def z929 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x5cfe00007fffe002 0x72e7f00003ffff00

def z930 : W := mkw 0xe5b5aedb00000008 0x072dad76d8000000 0xe3ffffff80000007 0xcf1ffffffc000000

def z931 : W := mkw 0xf601fd947ad03e43 0x0fb00feca3d681f2 0x7f01ff1c7ff01f17 0xbbf80ff8e3ff80f8

def z932 : W := mkw 0x00025124ad9b3fe0 0x90001289256cd9ff 0x00000000678f1ff8 0x30000000033c78ff

def z933 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0xffc1ffe07ff01f17 0xfffe0fff03ff80f8

def z934 : W := mkw 0x8401ffffa8913fe8 0x94200ffffd4489ff 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z935 : W := mkw 0x72a20000576ec004 0x2395100002bb7600 0x7ff000007fffe007 0x73ff800003ffff00

def z936 : W := mkw 0xe0a171b47ad5bec3 0x2f050b8da3d6adf6 0xe3f1fffc7fffffff 0xff1f8fffe3ffffff

def z937 : W := mkw 0xfbff26db576ec00c 0x67dff936dabb7600 0xfffe37ffffffe007 0x77fff1bfffffff00

def z938 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x7f01f7007ff01f12 0x3bf80fb803ff80f8

def z939 : W := mkw 0x095e526fad2b79e0 0x904af2937d695bcf 0xe0fff0fff80ff8ee 0xef07ff87ffc07fc7

def z940 : W := mkw 0x16009d040ad02e41 0x00b004e820568172 0xbf303f1c1ff8fffd 0xf5f981f8e0ffc7ff

def z941 : W := mkw 0xfffdaedb52400008 0x47ffed76da920000 0xffffffffe3800007 0xcfffffffff1c0000

def z942 : W := mkw 0x7bff2000576ec004 0x63dff90002bb7600 0x7ffff0007fffe007 0xfbffff8003ffff00

def z943 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xffcfffe3e78f1fff 0xfffe7fff1f3c78ff

def z944 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xfcffc8e3ff8fffff 0xffe7fe471ffc7fff

def z945 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xffcfc8e3ffff1fff 0xfffe7e471ffff8ff

def z946 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xdcffffff80000002 0xcee7fffffc000000

def z947 : W := mkw 0x73b400005264c004 0x639da00002932600 0x7ff000007fffe007 0x73ff800003ffff00

def z948 : W := mkw 0xf2a171b47ad5bec3 0x2f950b8da3d6adf6 0xfff1f0fc7fffffff 0xffff8f87e3ffffff

def z949 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xe0f1f8fc7c0fffff 0xff078fc7e3e07fff

def z950 : W := mkw 0xff5daedb00000008 0x47faed76d8000000 0xff0fffff80000007 0x8ff87ffffc000000

def z951 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffff84001f17 0xfffffffffc2000f8

def z952 : W := mkw 0x7bfc00005366c004 0x63dfe000029b3600 0x7ff000007bffe006 0x63ff800003dfff00

def z953 : W := mkw 0xe0a171b47a55bac3 0x2f050b8da3d2add6 0xe0f1f0fc787ff8ee 0xef078f87e3c3ffc7

def z954 : W := mkw 0xf2a175b47a55bac3 0x2f950bada3d2add6 0xfff1f7fc7ffff8ef 0xffff8fbfe3ffffc7

def z955 : W := mkw 0xfbff2699576ec00c 0x67dff934cabb7600 0xfffe3f1fffffe007 0xf7fff1f8ffffff00

def z956 : W := mkw 0x7601fd247ad5bec3 0x2bb00fe923d6adf6 0xff31ff1c7fffffff 0xfff98ff8e3ffffff

def z957 : W := mkw 0xe0a171b47895bec3 0x2f050b8da3c4adf6 0xe0f1f0fc780ffffe 0xef078f87e3c07fff

def z958 : W := mkw 0x80a170b42805b8c2 0x2c050b85a1402dc6 0xc0f1f0fc600ff8ee 0xee078f87e3007fc7

def z959 : W := mkw 0x0114130d88306b60 0x1008a0986c41835b 0xa33e3f1f9870fffd 0xc519f1f8fcc387ff

def z960 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xff3e3f1ffff8ffff 0xf7f9f1f8ffffc7ff

def z961 : W := mkw 0xfbff2090576ec006 0x6fdff90482bb7600 0x7ffe00007fffe007 0x73fff00003ffff00

def z962 : W := mkw 0x084a0000576ec004 0x2042500002bb7600 0x1c0e00007fffe001 0x30e0700003ffff00

def z963 : W := mkw 0xe0a175b47815bac3 0x2f050bada3c0add6 0xe0f1f7fc780ff8ee 0xef078fbfe3c07fc7

def z964 : W := mkw 0xfffdaedb00048008 0x67ffed76d8002400 0xffffffff800fe007 0xcffffffffc007f00

def z965 : W := mkw 0xf601fd907ad01e01 0x0fb00fec83d680f0 0xff01fffc7ff01f17 0xbff80fffe3ff80f8

def z966 : W := mkw 0x80a160b42005b0c2 0x2c050b05a1002d86 0x80f1c0fc000fe0e8 0x4c078e07e0007f07

def z967 : W := mkw 0xe9fd22db00000008 0x474fe916d8000000 0xe3ffffff80000007 0xcf1ffffffc000000

def z968 : W := mkw 0x8c49aedb00000008 0x04624d76d8000000 0x80cfffff80000000 0xcc067ffffc000000

def z969 : W := mkw 0x095e020d852a6164 0x504af0106c29530b 0x803e001f8008e0e8 0x4401f000fc004707

def z970 : W := mkw 0xe9ff72fffd2ff9e2 0xbf4ffb97ffe97fcf 0xe0fff0fff80ff8ee 0xef07ff87ffc07fc7

def z971 : W := mkw 0x7601fd047ad03e41 0x0bb00fe823d681f2 0x7f31ff1c7ff0ff17 0xbbf98ff8e3ff87f8

def z972 : W := mkw 0x00025124ac397be2 0x180012892561cbdf 0x000000001c78fff8 0x3000000000e3c7ff

def z973 : W := mkw 0x80a050b42805b8c2 0x24050285a1402dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z974 : W := mkw 0x8d5daedb00000008 0x046aed76d8000000 0xffffffff80000007 0xcffffffffc000000

def z975 : W := mkw 0x084a4020a50b11a0 0x004252010528588d 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z976 : W := mkw 0xf601fdb07ad11e83 0x0fb00fed83d688f4 0x7f01ffe07ff01f17 0xbbf80fff03ff80f8

def z977 : W := mkw 0xe0a130945804a840 0x27050984a2c02542 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z978 : W := mkw 0xf2a170b47a45b8c6 0x6f950b85a3d22dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z979 : W := mkw 0xfffdaedb02c00409 0x47ffed76d8160020 0xffffffff83800007 0xcffffffffc1c0000

def z980 : W := mkw 0x7601fd047ad03e41 0x0bb00fe823d681f2 0x7f01ff007ff8ffff 0xbbf80ff803ffc7ff

def z981 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffff800818ef 0xeffffffffc0040c7

def z982 : W := mkw 0xfffdaedb00204008 0x47ffed76d8010200 0xffffffff9870e007 0xcffffffffcc38700

def z983 : W := mkw 0x7601ec0072c01400 0x03b00f60039600a0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z984 : W := mkw 0x9ffdaedb00000008 0x44ffed76d8000000 0x9fffffff80000001 0xccfffffffc000000

def z985 : W := mkw 0x0401ff6fa8913fe1 0x98200ffb7d4489ff 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z986 : W := mkw 0xfffdaedb5346800c 0x67ffed76da9a3400 0xfffffffffff70007 0xffffffffffffb800

def z987 : W := mkw 0xf3b5269900000008 0x479da934c8000000 0xe3ffffff80000007 0xcf1ffffffc000000

def z988 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0xffffc0e07fffe007 0xfffffe0703ffff00

def z989 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffff9c700007 0xfffffffffce38000

def z990 : W := mkw 0x8401aedb00000008 0x04200d76d8000000 0x800fffff80000005 0xcc007ffffc000000

def z991 : W := mkw 0x7b5e0000576ec004 0x63daf00002bb7600 0x7f0e00007fffe007 0x33f8700003ffff00

def z992 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xdccfc8e3e7871ffb 0x9ee67e471f3c38ff

def z993 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0x60f1f0fc780ff8ea 0x2b078f87e3c07fc7

def z994 : W := mkw 0x7bfe0000052a4000 0x43dff00000295200 0x7ffe00007fffe007 0x73fff00003ffff00

def z995 : W := mkw 0xe0a170b4280138c0 0x07050b85a14009c6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z996 : W := mkw 0xfffdaedb0024c00c 0x67ffed76d8012600 0xffffffff8000e007 0xcffffffffc000700

def z997 : W := mkw 0x80a050b47805b8c2 0x2c050285a3c02dc6 0xc0f1c0fc780ff8ee 0xee078e07e3c07fc7

def z998 : W := mkw 0xf6a1fdb47ad13ec3 0x0fb50feda3d689f6 0xfff1fffc7ff01fff 0xffff8fffe3ff80ff

def z999 : W := mkw 0xf3b5379d5a74ea43 0x3f9da9bcead3a752 0x2330371c1870e000 0x011981b8e0c38700

def z1000 : W := mkw 0xe0a171b47815bac2 0x2f050b8da3c0add6 0xe0f1fffc780ffffe 0xef078fffe3c07fff

def z1001 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x5f01ff0067f01f13 0x9af80ff8033f80f8

def z1002 : W := mkw 0xfffdaedb52400008 0x47ffed76da920000 0xffffffff98700007 0xcffffffffcc38000

def z1003 : W := mkw 0x7601bd005ad00e01 0x0bb00de802d68070 0x7f003f007ff00717 0x33f801f803ff8038

def z1004 : W := mkw 0x8dfdaedb00000008 0x446fed76d8000000 0xdcffffff80000007 0xcee7fffffc000000

def z1005 : W := mkw 0x0400990008900e00 0x002004c800448070 0x3f003f001ff01f15 0xb1f801f800ff80f8

def z1006 : W := mkw 0x0400d92428913ec0 0x002006c9214489f6 0xfff1fffc7fffffff 0xffff8fffe3ffffff

def z1007 : W := mkw 0x9f5daedb00000008 0x44faed76d8000000 0xbf3fffff80000005 0xcdf9fffffc000000

def z1008 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0xff31ff1c7ff01f17 0xfff98ff8e3ff80f8

def z1009 : W := mkw 0x095e020d852a6160 0x104af0106c29530b 0x80fe001f800fe0e8 0x4407f000fc007f07

def z1010 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffffe00f0007 0xefffffffff007800

def z1011 : W := mkw 0x7601fd007ad49e01 0x2bb00fe803d6a4f0 0x7f01ff007fffff17 0xbbf80ff803fffff8

def z1012 : W := mkw 0xe0a171b47815bac2 0x2f050b8da3c0add6 0xe0f1f0fc7c7ffffe 0xff078f87e3e3ffff

def z1013 : W := mkw 0xe0a130b45805a8c2 0x2f050985a2c02d46 0xe0f1f0fc180fe0ee 0xcf078f87e0c07f07

def z1014 : W := mkw 0x1200010002500200 0x0090000800128010 0x1f000f0007f00711 0x10f80078003f8038

def z1015 : W := mkw 0x7601fd047ad03e41 0x0bb00fe823d681f2 0xff01ff1c7ff01fff 0xbff80ff8e3ff80ff

def z1016 : W := mkw 0x7ae8000053468004 0x63d74000029a3400 0x7ff000007fffe007 0x73ff800003ffff00

def z1017 : W := mkw 0x0c4a8842850a0120 0x0062544214285009 0xdccfc8e3e78f1fff 0xfee67e471f3c78ff

def z1018 : W := mkw 0x1600dd007ad01e01 0x08b006e803d680f0 0x5f01cf007ff01f17 0xbaf80e7803ff80f8

def z1019 : W := mkw 0xf6a1ad9002d00601 0x07b50d6c80168030 0xfff1fffc07f00717 0xdfff8fffe03f8038

def z1020 : W := mkw 0x7bfe0609576ec00c 0x63dff0304abb7600 0x7ffe07007fffe007 0x73fff03803ffff00

def z1021 : W := mkw 0x69fe120ddd2ee964 0x734ff0906ee9774b 0xe0fe301ff80ff8ee 0xe707f180ffc07fc7

def z1022 : W := mkw 0x1601fd007ad01e01 0x08b00fe803d680f0 0x1f01ff007ff01f11 0xb8f80ff803ff80f8

def z1023 : W := mkw 0x7bfc00005366c004 0x63dfe000029b3600 0x7ffe00007bf7e007 0x43fff00003dfbf00

def z1024 : W := mkw 0xfffdaedb0106800c 0x67ffed76d8083400 0xffffffff80070007 0xcffffffffc003800

def z1025 : W := mkw 0x6401f90078901e00 0x0b200fc803c480f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z1026 : W := mkw 0xfffdaedb01820408 0xc7ffed76d80c1020 0xffffffff83800007 0xcffffffffc1c0000

def z1027 : W := mkw 0x1601fd002ad01e01 0x08b00fe8015680f0 0x5f01ff0067f01f17 0xbaf80ff8033f80f8

def z1028 : W := mkw 0x16008d0002d00601 0x00b0046800168030 0x5f01cf0007f00717 0x9af80e78003f8038

def z1029 : W := mkw 0x8515aedb00000008 0x0428ad76d8000000 0x803fffff80000000 0xcc01fffffc000000

def z1030 : W := mkw 0xf2a174b47805b8c2 0x2f950ba5a3c02dc6 0xe3f1f7fc780ff8ee 0xef1f8fbfe3c07fc7

def z1031 : W := mkw 0x1601ad0002d00601 0x00b00d6800168030 0x1f01ff0007f00711 0x98f80ff8003f8038

def z1032 : W := mkw 0x0000110008100a00 0x0000008800408050 0x7f003f007ff01f17 0xb3f801f803ff80f8

def z1033 : W := mkw 0x7bfe0042576ec004 0x63dff00212bb7600 0xfffe00e3ffffe007 0x77fff0071fffff00

def z1034 : W := mkw 0x76009d005ad00e01 0x03b004e802d68070 0x7f003f007ff01f17 0xb3f801f803ff80f8

def z1035 : W := mkw 0xe9ff72bdfd2ff9e6 0x7f4ffb95efe97fcf 0xe0fff0fff80ff8ee 0xef07ff87ffc07fc7

def z1036 : W := mkw 0x72a011045a54aa40 0x2395008822d2a552 0xfff03f1c7fffffff 0xf7ff81f8e3ffffff

def z1037 : W := mkw 0x1600cd0072d01601 0x08b00668039680b0 0x1f000f0067f00711 0x10f80078033f8038

def z1038 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xffffffffe7800007 0xffffffffff3c0000

def z1039 : W := mkw 0x89fe02ff852fe1e2 0xb44ff017fc297f0f 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z1040 : W := mkw 0x1600cd0022d01601 0x00b00668011680b0 0x5f01cf0067f00713 0x1af80e78033f8038

def z1041 : W := mkw 0xf601fdb47ad13ec3 0x0fb00feda3d689f6 0xffc1fffc7fff1fff 0xfffe0fffe3fff8ff

def z1042 : W := mkw 0x7ffc8a4b00000000 0x43ffe45258000000 0xffffffff80000007 0xcffffffffc000000

def z1043 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xe3f1fffc780ff8ef 0xef1f8fffe3c07fc7

def z1044 : W := mkw 0xe0a160b47005b0c2 0x2f050b05a3802d86 0xe0f1f0fc600fe0ee 0xcf078f87e3007f07

def z1045 : W := mkw 0x60a050247805b8c0 0x2305028123c02dc6 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z1046 : W := mkw 0x7601fd0028901e00 0x03b00fe8014480f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z1047 : W := mkw 0x1600dd002ad01e01 0x08b006e8015680f0 0x1f000f0007f01f11 0x10f80078003f80f8

def z1048 : W := mkw 0x7601ed0072d01601 0x0bb00f68039680b0 0x7f01cf007ff00717 0x3bf80e7803ff8038

def z1049 : W := mkw 0xfe49aedb00000008 0x07f24d76d8000000 0xffcfffff80000007 0xcffe7ffffc000000

def z1050 : W := mkw 0x0116130d8d3a6b60 0x1008b0986c69d35b 0xa33e3f1ffffffffd 0xf519f1f8ffffffff

def z1051 : W := mkw 0xf2a170b47805b8c2 0x2f950b85a3c02dc6 0xfff1f0fc780ff8ef 0xefff8f87e3c07fc7

def z1052 : W := mkw 0x8115229900000000 0x0408a914c8000000 0xa33fffff80000005 0xcd19fffffc000000

def z1053 : W := mkw 0x0400d966a8913fe0 0x902006cb354489ff 0x8001c8e380001ff8 0x8c000e471c0000ff

def z1054 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xa33e3f1f9c70fff9 0x9519f1f8fce387ff

def z1055 : W := mkw 0x80a120b40005a0c2 0x24050905a0002d06 0x80f1f0fc000fe0e8 0xcc078f87e0007f07

def z1056 : W := mkw 0x1b5e0000576ec004 0x60daf00002bb7600 0x3f3e00007fffe005 0x71f9f00003ffff00

def z1057 : W := mkw 0x05148a4b00000000 0x0028a45258000000 0xa33fffff80000005 0xcd19fffffc000000

def z1058 : W := mkw 0x68ea0000576ec004 0x2347500002bb7600 0x7cfe00007fffe007 0x73e7f00003ffff00

def z1059 : W := mkw 0xfffdaedb52400009 0x4fffed76da920000 0xffffffff80000007 0xcffffffffc000000

def z1060 : W := mkw 0x720171007a501a00 0x0b900b8803d280d0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z1061 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xfcfff8ffe78f1fff 0xffe7ffc7ff3c78ff

def z1062 : W := mkw 0xf6a1fd947ad4be43 0x2fb50feca3d6a5f2 0xfff1fffc7ff0ff17 0xffff8fffe3ff87f8

def z1063 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x7ffe3f007fffe007 0xf3fff1f803ffff00

def z1064 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x7ffe08007fffff17 0xf3fff04003fffff8

def z1065 : W := mkw 0xfbff2490576ec00c 0x67dff92482bb7600 0x7ffe00007fffe007 0x73fff00003ffff00

def z1066 : W := mkw 0x8515aedb00000008 0x0428ad76d8000000 0x830fffff80000001 0x8c187ffffc000000

def z1067 : W := mkw 0xf2a175b47a55bac3 0x2f950bada3d2add6 0xe3f1fffc7c7fffff 0xff1f8fffe3e3ffff

def z1068 : W := mkw 0x80a170b42805b8c2 0x2c050b85a1402dc6 0xa0f1f0fc180ff8ec 0xed078f87e0c07fc7

def z1069 : W := mkw 0x0516c862a4a955a0 0x8028b64315254aad 0xa33fc8e39c78fffd 0xfd19fe471ce3c7ff

def z1070 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x5f01cf007ff01f13 0x3af80e7803ff80f8

def z1071 : W := mkw 0xe0a170b42805b8c2 0x2f050b85a1402dc6 0xe0f1f0fc000ff8ee 0xcf078f87e0007fc7

def z1072 : W := mkw 0xedfdaadb00000000 0x076fed56d8000000 0xffffffff80000007 0xcffffffffc000000

def z1073 : W := mkw 0x7bfe0209576ec004 0x63dff0104abb7600 0x7ffe371c7fffe007 0x73fff1b8e3ffff00

def z1074 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xdfcfffff80000003 0x8efe7ffffc000000

def z1075 : W := mkw 0x7601ad0052d00601 0x0bb00d6802968030 0x1f000f0007f00711 0x10f80078003f8038

def z1076 : W := mkw 0xfffdaedb50048008 0x67ffed76da802400 0xffffffffe0070007 0xcfffffffff003800

def z1077 : W := mkw 0xfffdaedb5264c00c 0x67ffed76da932600 0xfffffffffff0e007 0xffffffffffff8700

def z1078 : W := mkw 0x7601ad0002d00601 0x03b00d6800168030 0x5f01cf0007f00713 0x1af80e78003f8038

def z1079 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0x7fffffff80000003 0x0bfffffffc000000

def z1080 : W := mkw 0xe0a160b47005b0c2 0x2f050b05a3802d86 0xe0f1c0fc780fe0ee 0x6f078e07e3c07f07

def z1081 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0xfffe00007ffff8ef 0xf7fff00003ffffc7

def z1082 : W := mkw 0x16009d000ad00e01 0x00b004e800568070 0x3f003f001ff00711 0x11f801f800ff8038

def z1083 : W := mkw 0xfffdaedb00000008 0x47ffed76d8000000 0xbf3fffff80000001 0x8df9fffffc000000

def z1084 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x7f31ff007ff8ff17 0xfbf98ff803ffc7f8

def z1085 : W := mkw 0x7601ed0072d01601 0x0bb00f68039680b0 0x7f01ff0067f00717 0x9bf80ff8033f8038

def z1086 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0x3f01ff001ff01f11 0x99f80ff800ff80f8

def z1087 : W := mkw 0x7601fd427ad01e01 0x0bb00fea13d680f0 0xff01ffe3fff01f17 0xbff80fff1fff80f8

def z1088 : W := mkw 0x89fe02fb852fc1ac 0xe44ff017dc297e0d 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z1089 : W := mkw 0x7601fd002ad01e01 0x0bb00fe8015680f0 0x7f01ff0007f01f17 0x9bf80ff8003f80f8

def z1090 : W := mkw 0x76a1fd247ad5bec3 0x2bb50fe923d6adf6 0x7ff1ff007fffffff 0xfbff8ff803ffffff

def z1091 : W := mkw 0x1f5e8f4b877a432c 0x50faf47a5c3bd219 0x1f0e0f0387f00711 0x10f870781c3f8038

def z1092 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x3f3e00007fffe001 0x31f9f00003ffff00

def z1093 : W := mkw 0xf6a1fd907ad01e01 0x0fb50fec83d680f0 0x7f31ff1c7ff01f17 0xbbf98ff8e3ff80f8

def z1094 : W := mkw 0xe0a120b40005a0c2 0x27050905a0002d06 0xc0f1c0fc000fe0ea 0x4e078e07e0007f07

def z1095 : W := mkw 0xe0a160b070059080 0x27050b0583802c84 0xe0f1f0fc780ff8ee 0xef078f87e3c07fc7

def z1096 : W := mkw 0xfee9aedb00000008 0x47f74d76d8000000 0xdccfffff80000007 0xcee67ffffc000000

def z1097 : W := mkw 0x89fe02df852ee16c 0x744ff016fc29770b 0x80fe00ff800fe0e8 0x4407f007fc007f07

def z1098 : W := mkw 0xf2a170b47a45b8c2 0x2f950b85a3d22dc6 0xfcf1f0fc7b8ff8ee 0xefe78f87e3dc7fc7

def z1099 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0xfffe301c7fffe007 0xf7fff180e3ffff00

def z1100 : W := mkw 0x0401fd0028901e01 0x08200fe8014480f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z1101 : W := mkw 0x76a1fd207ad59e81 0x2bb50fe903d6acf4 0xfff1ffe07fffffff 0xffff8fff03ffffff

def z1102 : W := mkw 0x1601fd002ad01e01 0x08b00fe8015680f0 0x3f01ff001ff01f15 0xb9f80ff800ff80f8

def z1103 : W := mkw 0x7601fd207ad11e81 0x0bb00fe903d688f4 0xff01ffe07ff01fff 0xbff80fff03ff80ff

def z1104 : W := mkw 0x7bfe0000d76ec124 0x63dff00006bb7609 0x7ffe0803ffffe717 0x73fff0401fffff38

def z1105 : W := mkw 0xfbfe0090576ec004 0x67dff00482bb7600 0xfffe00fc7fffe007 0x77fff007e3ffff00

def z1106 : W := mkw 0x8401fbffa8913fe2 0x9c200fdffd4489ff 0x8001ffff80001ff8 0x8c000ffffc0000ff

def z1107 : W := mkw 0xf6a1fd907ad49e03 0x2fb50fec83d6a4f0 0x7f01ff007ff01f17 0xbbf80ff803ff80f8

def z1108 : W := mkw 0xe0a160b42005b0c2 0x27050b05a1002d86 0xe0f1f0fc600ff8ee 0xef078f87e3007fc7

def z1109 : W := mkw 0x7ae800005366c004 0x63d74000029b3600 0x5cc000007bf7e002 0x02e6000003dfbf00

def z1110 : W := mkw 0xf3b5339d5a74ea46 0x7f9da99cead3a752 0x2330371c1870e000 0x011981b8e0c38700

def z1111 : W := mkw 0x9601fdb42ad13ec3 0x0cb00feda15689f6 0x9f01fffc07f01ff9 0x9cf80fffe03f80ff

def z1112 : W := mkw 0x69fe0000552ec000 0x234ff00002a97600 0x7ffe00007fffe007 0x73fff00003ffff00

def z1113 : W := mkw 0x0c4ac862a58b15a0 0x80625643152c58ad 0xdccfc0e3e78f1ffa 0x7ee67e071f3c78ff

def z1114 : W := mkw 0x7bfe0000576ec004 0x63dff00002bb7600 0x7ffe00007bffe002 0x43fff00003dfff00

def z1115 : W := mkw 0x16008d0002d00601 0x00b0046800168030 0x1f000f0007f01f15 0xb0f80078003f80f8

def z1116 : W := mkw 0xf2a170b47a45b8c2 0x2f950b85a3d22dc6 0xe3f1f0fc787ff8ee 0xef1f8f87e3c3ffc7

def z1117 : W := mkw 0x0116130d8c386b60 0x1008b0986c61c35b 0xe3fe3f1ffc7fffff 0xf71ff1f8ffe3ffff

def z1118 : W := mkw 0x72020000576ec004 0x2390100002bb7600 0x5c0000007fffe002 0x32e0000003ffff00

def z1119 : W := mkw 0x7bfe0000d76ec124 0x63dff00006bb7609 0xfffe0003ffffe0ef 0x77fff0001fffff07

def z1120 : W := mkw 0x7601fd007ad01e01 0x0bb00fe803d680f0 0xff01ff007ff81fff 0xfff80ff803ffc0ff

def z1121 : W := mkw 0xfffdaedb5244800c 0x67ffed76da922400 0xffffffff80000007 0xcffffffffc000000

def z1122 : W := mkw 0x7bfc00005366c004 0x63dfe000029b3600 0x7ff000007ff7e007 0x33ff800003ffbf00

def z1123 : W := mkw 0xf715aedb00000008 0x07b8ad76d8000000 0xff3fffff80000007 0xcff9fffffc000000

def z1124 : W := mkw 0xe0a160b47005b0c2 0x2f050b05a3802d86 0xc0f1c0fc600ff8ee 0xee078e07e3007fc7

def z1125 : W := mkw 0x7aea0000576ec004 0x63d7500002bb7600 0x7fc000007fffe007 0x33fe000003ffff00

def z1126 : W := mkw 0xf601fdb47ad13ec3 0x0fb00feda3d689f6 0xff31fffc7ff8ffff 0xfff98fffe3ffc7ff

def z1127 : W := mkw 0x1600cd2022d11681 0x00b00669011688b4 0xdfc1cfe067ff1fff 0xfefe0e7f033ff8ff

def z1128 : W := mkw 0x1600cd0022d01601 0x00b00668011680b0 0x1f000f0067f01f11 0x30f80078033f80f8

def z1129 : W := mkw 0x0c488a4b00000000 0x0062445258000000 0xdccfffff80000007 0xcee67ffffc000000

def z1130 : W := mkw 0xfbfe0299576ec00c 0x67dff014cabb7600 0x7ffe001c7fffe007 0x73fff000e3ffff00

def z1131 : W := mkw 0xe0a170b47805b8c2 0x2f050b85a3c02dc6 0xfcf1f0fc7f8ff8ef 0xffe78f87e3fc7fc7

def z1132 : W := mkw 0xfbfd229900000000 0x47dfe914c8000000 0xffffffff80000007 0xcffffffffc000000

def z1133 : W := mkw 0xfbff2699576ec00c 0x67dff934cabb7600 0xfffff7fc7fffe007 0xffffffbfe3ffff00

def z1134 : W := mkw 0x00025124fdbfffe2 0xb800128927edffff 0x000000007ffffff8 0x3000000003ffffff

def z1135 : W := mkw 0x76a1fd007ad49e01 0x2bb50fe803d6a4f0 0x7f31ff007ff0ff17 0xbbf98ff803ff87f8

def z1136 : W := mkw 0x1b5e0000576ec004 0x60daf00002bb7600 0x5fce00007fffe007 0x72fe700003ffff00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z7,z6]),(0,[z1,z2,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z9,z6])],[(0,[z1,z2,z3,z4,z5,z6,z10]),(0,[z1,z2,z3,z4,z11,z12,z6]),(0,[z1,z13,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z16,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z18,z5,z6]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z21,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z22,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z23]),(0,[z24,z1,z25,z3,z4,z5,z6]),(0,[z1,z2,z4,z26,z5,z27,z6]),(0,[z1,z2,z4,z5,z12,z6,z28]),(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z1,z2,z30,z3,z4,z5,z6])],[(0,[z1,z2,z3,z31,z4,z32,z5]),(0,[z1,z2,z3,z4,z33,z5,z6]),(1,[z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z6]),(0,[z1,z2,z15,z36,z4,z5,z6]),(0,[z1,z2,z3,z4,z37,z5,z6])],[(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z39,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z4,z11,z5,z12,z6]),(0,[z2,z3,z4,z5,z40,z6,z41]),(0,[z42,z1,z2,z4,z43,z5,z6])],[(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z3,z4,z45,z5,z6]),(0,[z1,z2,z4,z5,z46,z12,z6]),(0,[z47,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z12,z6]),(0,[z48,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z6])],[(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z4,z5,z12,z6]),(0,[z1,z20,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z53]),(0,[z1,z2,z4,z5,z12,z6,z54]),(0,[z1,z2,z55,z3,z43,z5,z6]),(1,[z1,z2,z4,z5,z56,z6])]],
   [[(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z59,z3,z4,z60,z6])],[(0,[z1,z2,z3,z61,z4,z5,z6]),(0,[z1,z25,z3,z4,z26,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z6])],[(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z67,z5,z6])],[(0,[z1,z68,z2,z3,z4,z5,z6]),(0,[z1,z69,z2,z3,z4,z5,z6]),(0,[z70,z2,z71,z3,z4,z5,z6]),(0,[z70,z1,z72,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z73,z5,z6]),(0,[z1,z2,z4,z74,z5,z12,z6]),(1,[z1,z2,z55,z3,z5,z6])],[(0,[z75,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z36,z3,z4,z5,z6])],[(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z77,z4,z5,z6])],[(1,[z1,z2,z78,z4,z5,z6]),(0,[z24,z1,z2,z15,z4,z5,z6]),(0,[z79,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z15,z15,z4,z5,z6]),(0,[z1,z80,z2,z3,z4,z5,z6])],[(0,[z81,z1,z82,z2,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z83,z6]),(0,[z24,z39,z1,z2,z3,z4,z6]),(0,[z1,z82,z20,z3,z4,z5,z6]),(0,[z84,z1,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z54])],[(0,[z79,z1,z3,z4,z5,z86,z6]),(0,[z1,z87,z2,z3,z4,z5,z6])],[(1,[z1,z2,z88,z3,z4,z5]),(0,[z1,z2,z89,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6]),(1,[z1,z2,z3,z4,z92,z6])],[(0,[z1,z2,z71,z4,z5,z12,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z94,z5,z6]),(0,[z1,z2,z3,z95,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z96]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z98,z4,z5,z12,z6]),(0,[z1,z2,z99,z3,z4,z12,z6])],[(0,[z100,z1,z2,z3,z101,z5,z6]),(0,[z1,z82,z2,z3,z4,z5,z6]),(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z103,z6])],[(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z41]),(0,[z24,z1,z2,z106,z4,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z108])],[(0,[z109,z1,z2,z4,z5,z12,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z28,z108]),(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z6]),(0,[z1,z2,z99,z3,z4,z74,z5])],[(0,[z1,z2,z15,z114,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z117,z3,z4,z5,z6]),(0,[z118,z1,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z43,z5]),(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z1,z121,z2,z3,z4,z5,z6])]],
   [[(0,[z81,z1,z2,z122,z4,z5,z6]),(0,[z75,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z15,z4,z74,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z6])],[(0,[z81,z1,z2,z3,z4,z124,z6]),(0,[z1,z2,z3,z4,z125,z5,z6])],[(0,[z75,z24,z1,z2,z3,z4,z6]),(0,[z1,z2,z15,z4,z5,z46,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z1,z2,z3,z4,z127,z5,z6])],[(0,[z128,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z1,z2,z130,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z74,z6])],[(1,[z81,z2,z114,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z132,z6]),(0,[z1,z133,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z134,z3,z4,z5,z6]),(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(0,[z1,z137,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z139,z5])],[(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z2,z4,z5,z12,z12,z6]),(0,[z42,z1,z2,z4,z5,z12,z6])]],
   [[(0,[z75,z1,z2,z78,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z141]),(0,[z1,z142,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z143,z6]),(0,[z1,z2,z144,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z145,z5,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z1,z2,z4,z147,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z148,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z150,z5,z6]),(0,[z1,z2,z3,z4,z5,z151,z6])],[(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z152,z5,z6]),(0,[z1,z2,z78,z3,z4,z5,z6]),(1,[z1,z2,z4,z11,z12,z6]),(0,[z1,z2,z3,z4,z153,z5,z6]),(0,[z1,z2,z3,z4,z43,z5,z108])],[(0,[z1,z2,z154,z3,z31,z5,z6]),(0,[z1,z2,z3,z4,z155,z11,z6]),(0,[z1,z154,z3,z4,z147,z5,z6]),(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z2,z3,z43,z5,z157,z6])],[(0,[z1,z2,z3,z31,z5,z6,z108]),(0,[z75,z1,z25,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z74,z12,z6])],[(0,[z1,z2,z3,z4,z5,z158,z6]),(0,[z1,z2,z159,z3,z4,z5,z6]),(0,[z1,z2,z3,z31,z4,z5,z160]),(0,[z1,z161,z2,z15,z4,z5,z6]),(0,[z1,z162,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z163,z6])],[(0,[z1,z72,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z164,z6])],[(0,[z51,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z31,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z165,z6]),(0,[z1,z2,z3,z4,z5,z166,z6]),(1,[z1,z2,z4,z5,z49,z6])]],
   [[(0,[z1,z2,z167,z3,z4,z5,z6]),(0,[z1,z2,z168,z3,z4,z5,z6]),(0,[z1,z2,z99,z3,z4,z155,z6])],[(0,[z1,z2,z3,z4,z5,z169,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z171,z1,z2,z3,z4,z5,z6]),(0,[z172,z1,z2,z3,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z173]),(0,[z1,z2,z15,z3,z4,z5,z6])],[(0,[z174,z1,z2,z3,z4,z5,z6]),(0,[z175,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z176,z4,z5,z6]),(0,[z1,z177,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z92,z6]),(0,[z1,z2,z59,z3,z5,z60,z6]),(0,[z1,z2,z3,z150,z5,z60,z6])],[(0,[z1,z2,z3,z4,z5,z178,z6]),(0,[z1,z2,z3,z4,z5,z179,z6]),(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z12,z6]),(0,[z1,z2,z181,z3,z4,z5,z6]),(0,[z1,z182,z2,z15,z4,z5,z6]),(0,[z1,z2,z4,z74,z5,z49,z6]),(0,[z183,z1,z2,z3,z4,z5,z6])],[(0,[z100,z1,z184,z3,z4,z5,z6]),(0,[z1,z185,z2,z3,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z6]),(0,[z1,z2,z187,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z12,z6]),(0,[z1,z2,z36,z3,z4,z5,z28]),(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z189,z6]),(0,[z138,z1,z2,z3,z139,z5,z6])],[(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z40]),(0,[z1,z192,z2,z3,z147,z5,z6]),(0,[z1,z2,z4,z5,z12,z193,z6])],[(0,[z194,z1,z2,z3,z4,z5,z6]),(0,[z1,z195,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z107,z4,z5,z6]),(0,[z131,z1,z2,z99,z3,z4,z5])]],
   [[(1,[z196,z2,z3,z4,z5,z41]),(0,[z1,z197,z2,z3,z4,z5,z6]),(0,[z1,z2,z198,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z199,z6]),(0,[z1,z200,z2,z184,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z201]),(0,[z1,z202,z2,z4,z5,z12,z6]),(0,[z1,z2,z203,z3,z4,z5,z6]),(0,[z131,z1,z2,z204,z4,z5,z6])],[(1,[z1,z205,z2,z4,z5,z6]),(0,[z206,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z207,z4,z5,z6]),(0,[z1,z208,z2,z3,z4,z5,z6])],[(0,[z100,z209,z2,z3,z4,z5,z6]),(0,[z1,z2,z210,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z211,z5,z6]),(0,[z1,z2,z212,z3,z4,z5,z6]),(0,[z1,z2,z213,z3,z4,z5,z6]),(0,[z1,z214,z2,z3,z4,z5,z6])],[(1,[z70,z2,z71,z4,z5,z6]),(0,[z138,z1,z2,z3,z215,z5,z6]),(0,[z196,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z216]),(0,[z1,z2,z3,z4,z217,z5,z6]),(0,[z1,z2,z3,z218,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z219,z6]),(0,[z1,z2,z31,z4,z5,z12,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z6]),(0,[z1,z2,z3,z4,z222,z5,z6]),(0,[z223,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z224,z4,z5,z12,z6]),(0,[z1,z2,z107,z4,z5,z12,z6]),(1,[z1,z2,z225,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z226,z5,z6])],[(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z105,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z4,z5,z12,z40,z6]),(0,[z228,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z229,z5,z6]),(0,[z1,z2,z3,z4,z5,z230,z6]),(0,[z131,z1,z2,z15,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z202,z2,z3,z147,z5,z6]),(0,[z1,z2,z59,z3,z4,z150,z6]),(0,[z1,z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z234,z5,z6])],[(0,[z81,z2,z3,z114,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z108]),(0,[z1,z2,z15,z4,z235,z5,z6]),(0,[z1,z2,z4,z5,z12,z6,z108])],[(0,[z100,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z6,z236]),(0,[z1,z2,z3,z4,z237,z5,z6]),(0,[z238,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z59,z3,z4,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z6])],[(0,[z81,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z240,z5,z6]),(0,[z1,z82,z2,z15,z4,z5,z6]),(0,[z138,z1,z2,z98,z3,z5,z6])],[(0,[z241,z2,z184,z3,z4,z5,z6]),(0,[z1,z2,z15,z71,z4,z5,z6]),(0,[z1,z2,z3,z4,z242,z5,z6]),(1,[z42,z1,z2,z4,z43,z5]),(0,[z1,z2,z243,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z244,z5,z6]),(1,[z1,z82,z4,z245,z5,z6]),(0,[z1,z2,z3,z4,z246,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z3,z4,z5,z248,z6]),(0,[z1,z2,z15,z4,z249,z5,z6]),(0,[z1,z2,z15,z4,z5,z6,z250]),(0,[z1,z2,z3,z4,z251,z5,z6])],[(0,[z1,z2,z252,z3,z4,z5,z6]),(0,[z51,z2,z3,z31,z4,z5,z6]),(0,[z1,z161,z2,z3,z5,z6,z108]),(0,[z1,z253,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z254])],[(0,[z1,z2,z255,z3,z4,z5,z6]),(0,[z1,z2,z98,z59,z3,z5,z6])]],
   [[(0,[z1,z256,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z40,z6]),(0,[z24,z1,z3,z4,z5,z46,z6]),(0,[z1,z2,z257,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z74,z250])],[(0,[z1,z2,z3,z4,z124,z5,z6]),(0,[z1,z258,z2,z3,z4,z5,z6]),(0,[z75,z1,z2,z3,z4,z259,z6]),(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z261,z6]),(0,[z1,z25,z2,z3,z4,z155,z6]),(0,[z1,z161,z2,z3,z4,z5,z6]),(0,[z1,z2,z262,z3,z4,z5,z6]),(0,[z263,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z264,z4,z5,z6]),(0,[z1,z161,z72,z2,z3,z5,z6]),(0,[z1,z265,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z150,z155,z6])],[(0,[z1,z266,z2,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z268,z5,z6]),(0,[z1,z2,z3,z4,z5,z269,z6]),(0,[z105,z1,z270,z2,z3,z4,z5]),(1,[z1,z2,z59,z3,z60,z6])],[(0,[z81,z1,z2,z114,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z271,z6]),(0,[z1,z2,z3,z4,z5,z6,z272]),(0,[z105,z2,z3,z4,z5,z40,z6]),(0,[z1,z2,z3,z4,z5,z6,z273])],[(0,[z1,z2,z274,z3,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z86]),(0,[z138,z1,z161,z2,z3,z5,z6]),(1,[z1,z2,z4,z74,z12,z6]),(0,[z138,z1,z2,z3,z4,z5,z108])],[(0,[z1,z2,z3,z275,z4,z5,z6]),(0,[z1,z2,z276,z3,z4,z5,z6]),(0,[z1,z2,z122,z3,z4,z277,z5]),(0,[z1,z2,z3,z278,z4,z5,z6])],[(1,[z1,z2,z279,z3,z4,z6]),(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z131,z196,z1,z2,z3,z4,z5]),(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z282,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z215,z5,z6]),(0,[z51,z1,z2,z3,z31,z5,z6]),(0,[z1,z182,z2,z3,z4,z5,z6]),(0,[z1,z2,z283,z3,z4,z5,z6])],[(1,[z1,z2,z3,z284,z5,z6]),(0,[z1,z2,z34,z4,z11,z5,z6]),(0,[z1,z2,z4,z26,z5,z12,z6]),(0,[z1,z2,z285,z3,z4,z5,z6])],[(0,[z2,z3,z31,z4,z215,z5,z6]),(0,[z138,z1,z2,z122,z3,z5,z6]),(0,[z1,z2,z3,z4,z286,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z287])],[(0,[z1,z2,z4,z288,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z289,z6])],[(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z291,z1,z2,z3,z4,z5,z6])],[(0,[z100,z1,z241,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z293,z1,z2,z3,z4,z5,z6]),(0,[z1,z192,z202,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z136,z6]),(0,[z1,z72,z2,z15,z4,z5,z6]),(0,[z1,z294,z2,z3,z4,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6])],[(1,[z105,z2,z3,z4,z5,z40]),(1,[z1,z2,z4,z150,z12,z6])],[(0,[z1,z2,z3,z4,z5,z296,z6]),(0,[z1,z2,z297,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z2,z3,z4,z5,z6]),(1,[z75,z2,z3,z4,z259,z6]),(0,[z298,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z15,z4,z155,z6])],[(0,[z1,z2,z3,z4,z299,z5,z6]),(0,[z1,z270,z2,z3,z4,z5,z6]),(0,[z300,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z301,z5,z6]),(0,[z302,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z1,z2,z304,z3,z4,z5,z6])],[(0,[z1,z305,z2,z3,z4,z5,z6]),(0,[z196,z1,z2,z3,z146,z5,z6]),(0,[z1,z2,z176,z4,z26,z5,z6]),(1,[z1,z161,z72,z2,z5,z6]),(0,[z1,z2,z306,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z307,z12,z6]),(1,[z1,z2,z207,z4,z5,z6]),(0,[z1,z2,z308,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z99,z3,z4,z5,z6])],[(0,[z1,z2,z3,z204,z4,z5,z6])],[(0,[z1,z2,z309,z3,z4,z5,z6]),(0,[z310,z1,z2,z3,z4,z5,z6])],[(0,[z39,z2,z3,z4,z11,z5,z6]),(0,[z1,z2,z311,z3,z4,z5,z6]),(0,[z1,z2,z15,z98,z4,z5,z6]),(0,[z138,z1,z2,z3,z107,z5,z6]),(0,[z1,z2,z312,z3,z4,z5,z6])],[(0,[z81,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z4,z5,z12,z6]),(0,[z109,z1,z2,z3,z31,z5,z6]),(0,[z105,z196,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z6,z313])]],
   [[(0,[z209,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z259,z6]),(0,[z1,z2,z3,z4,z5,z314,z6]),(0,[z1,z2,z315,z3,z4,z5,z6]),(0,[z131,z1,z2,z283,z4,z5,z6])],[(1,[z1,z2,z3,z4,z124,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z3,z4,z5,z6,z317]),(0,[z1,z192,z2,z15,z4,z5,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z319,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z320,z6])],[(0,[z321,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z322,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z323,z6]),(0,[z1,z2,z324,z3,z4,z5,z6]),(0,[z1,z2,z325,z3,z4,z5,z6]),(0,[z326,z1,z2,z3,z4,z5,z6])],[(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z328,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z329,z6]),(0,[z196,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z330,z5,z6]),(0,[z1,z331,z2,z3,z4,z5,z6])],[(0,[z1,z332,z2,z3,z4,z5,z6]),(0,[z1,z2,z333,z3,z4,z5,z6]),(1,[z1,z20,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z334,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z1,z2,z225,z59,z4,z5,z6])],[(0,[z1,z335,z2,z184,z4,z5,z6]),(0,[z70,z1,z82,z2,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z26,z6]),(0,[z138,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z336,z6])],[(0,[z1,z2,z15,z4,z26,z5,z6]),(0,[z337,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z5,z60,z6,z108]),(0,[z1,z2,z98,z3,z5,z6,z108])],[(0,[z1,z338,z2,z3,z4,z5,z6]),(0,[z1,z2,z339,z3,z4,z5,z6]),(0,[z1,z2,z15,z154,z4,z5,z6]),(0,[z340,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z36,z4,z5,z6,z28]),(0,[z1,z2,z341,z3,z74,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z342,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z344,z1,z2,z3,z4,z5,z6])],[(0,[z109,z1,z192,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z345,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z106,z4,z5,z6]),(1,[z1,z25,z3,z4,z26,z6]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z2,z98,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z348]),(0,[z105,z1,z2,z3,z4,z5,z108]),(0,[z1,z349,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z350,z5,z6])],[(0,[z1,z2,z3,z114,z4,z5,z6]),(0,[z1,z2,z4,z11,z5,z269,z6])],[(0,[z1,z2,z184,z4,z5,z12,z6]),(1,[z1,z2,z4,z5,z269,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z352,z2,z3,z4,z5,z6]),(0,[z1,z161,z72,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z353,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z354]),(0,[z1,z2,z3,z355,z4,z5,z6]),(0,[z1,z2,z3,z4,z356,z5,z6]),(0,[z1,z357,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z250])],[(0,[z1,z2,z358,z3,z4,z5,z6]),(0,[z70,z1,z2,z122,z4,z5,z6]),(0,[z1,z2,z3,z4,z359,z5,z6]),(0,[z1,z2,z15,z4,z5,z6,z41]),(0,[z1,z360,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z74,z5,z361,z6])],[(0,[z1,z2,z362,z3,z4,z5,z6]),(0,[z1,z2,z122,z3,z4,z136,z6]),(0,[z1,z2,z3,z4,z363,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z364,z5,z6]),(0,[z75,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z365]),(0,[z1,z2,z4,z5,z86,z12,z6])],[(0,[z63,z1,z2,z184,z3,z4,z6]),(0,[z81,z1,z2,z71,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z366])],[(0,[z1,z241,z2,z4,z5,z12,z6]),(0,[z1,z2,z367,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z368,z5,z6])],[(0,[z369,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z46,z6]),(0,[z1,z3,z4,z26,z5,z46,z6]),(0,[z1,z2,z122,z3,z4,z370,z6]),(0,[z1,z2,z122,z3,z5,z6,z108])],[(0,[z1,z2,z3,z4,z5,z371,z6]),(1,[z109,z2,z3,z215,z5,z6]),(0,[z196,z1,z2,z3,z372,z5,z6]),(0,[z1,z2,z3,z4,z373,z5,z6]),(0,[z1,z374,z2,z3,z4,z5,z6]),(1,[z24,z1,z2,z4,z12,z6]),(0,[z1,z2,z3,z4,z375,z5,z6])],[(0,[z70,z1,z20,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z376,z6]),(0,[z1,z2,z377,z3,z4,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z5,z6])],[(0,[z109,z2,z3,z4,z215,z5,z6]),(0,[z1,z2,z122,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z379,z5,z6]),(0,[z1,z2,z380,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z147,z5,z6]),(1,[z1,z2,z3,z4,z277,z5]),(0,[z1,z2,z3,z4,z381,z5,z6])]],
   [[(0,[z382,z1,z2,z3,z4,z5,z6]),(1,[z1,z270,z3,z4,z5,z313]),(0,[z1,z383,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z12,z60,z6]),(0,[z1,z2,z15,z384,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z254])],[(0,[z1,z385,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z386]),(0,[z1,z2,z3,z387,z4,z5,z6]),(0,[z388,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z259,z6]),(0,[z1,z389,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z2,z3,z4,z12,z60,z6]),(0,[z391,z1,z2,z3,z4,z5,z6])],[(0,[z1,z68,z2,z184,z3,z5,z6]),(0,[z1,z2,z3,z4,z392,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z6]),(0,[z1,z192,z2,z3,z5,z6,z108]),(0,[z1,z2,z98,z3,z4,z60,z6])],[(0,[z1,z2,z393,z3,z4,z5,z6]),(0,[z1,z2,z154,z3,z4,z5,z6]),(0,[z1,z2,z36,z3,z4,z43,z5]),(1,[z131,z1,z2,z99,z3,z4])],[(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z32,z5]),(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z396,z5,z6]),(0,[z1,z2,z15,z4,z155,z5,z6])],[(0,[z1,z192,z2,z3,z4,z5,z6]),(0,[z1,z2,z397,z3,z4,z5,z6]),(1,[z1,z2,z204,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(1,[z39,z2,z3,z4,z11,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z399,z1,z2,z3,z4,z5,z6]),(1,[z1,z25,z2,z4,z12,z6]),(0,[z1,z2,z15,z4,z5,z86,z6]),(1,[z1,z2,z315,z4,z5,z6])],[(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z401,z6]),(0,[z1,z402,z2,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z5,z250])]],
   [[(0,[z403,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z1,z270,z2,z15,z4,z5,z6]),(0,[z1,z72,z2,z4,z235,z5,z6]),(0,[z1,z2,z3,z107,z5,z6,z108])],[(0,[z405,z1,z2,z3,z4,z5,z6])],[(0,[z1,z406,z2,z3,z4,z5,z6]),(0,[z39,z1,z2,z15,z4,z5,z6]),(0,[z24,z1,z2,z407,z4,z5,z6]),(0,[z1,z2,z408,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z250,z108])],[(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z410,z3,z4,z5,z6]),(1,[z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z12,z6]),(0,[z1,z2,z411,z15,z4,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z6])],[(0,[z412,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z413,z5,z6]),(0,[z51,z1,z2,z15,z4,z5,z6]),(0,[z1,z414,z2,z3,z4,z5,z6]),(0,[z415,z1,z2,z3,z4,z5,z6])],[(0,[z100,z1,z2,z3,z284,z5,z6]),(0,[z416,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z27,z6]),(0,[z79,z1,z270,z3,z4,z5,z6]),(0,[z1,z2,z122,z4,z235,z5,z6]),(0,[z1,z2,z15,z4,z5,z6,z28]),(0,[z1,z2,z3,z4,z103,z5,z6])],[(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z1,z2,z34,z3,z4,z5,z6]),(0,[z1,z2,z418,z3,z4,z5,z6])],[(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z43,z5,z6]),(1,[z1,z2,z3,z5,z361,z6])]],
   [[(1,[z190,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z420,z6]),(0,[z1,z2,z3,z4,z421,z5,z6]),(0,[z1,z422,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z423,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z424]),(0,[z425,z1,z2,z3,z4,z5,z6]),(0,[z196,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z407,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z426,z6]),(0,[z1,z161,z2,z3,z235,z5,z6]),(0,[z1,z2,z55,z3,z4,z5,z6])],[(0,[z427,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z106,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z6,z428]),(0,[z1,z2,z429,z3,z4,z5,z6])],[(0,[z1,z82,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z2,z3,z4,z431,z5,z6]),(0,[z1,z2,z99,z3,z4,z139,z5]),(0,[z1,z432,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z434,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z435,z3,z4,z5,z6]),(0,[z1,z2,z4,z150,z5,z12,z6]),(0,[z1,z2,z15,z436,z4,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z6])],[(0,[z1,z2,z3,z4,z437,z5,z6]),(0,[z1,z2,z3,z4,z235,z5,z6]),(0,[z1,z2,z4,z150,z5,z56,z6])],[(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z2,z439,z3,z4,z5,z6])],[(0,[z1,z2,z440,z3,z4,z5,z6]),(1,[z63,z1,z2,z3,z4,z6]),(0,[z1,z2,z224,z3,z4,z12,z6])]],
   [[(0,[z190,z1,z2,z184,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z441,z6]),(0,[z442,z1,z2,z3,z4,z5,z6]),(0,[z443,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z444,z12,z6]),(0,[z1,z2,z3,z4,z155,z74,z6]),(0,[z1,z2,z3,z4,z74,z5,z250])],[(0,[z1,z2,z3,z4,z445,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z288,z5,z6]),(0,[z1,z2,z3,z4,z249,z5,z6]),(0,[z1,z447,z2,z3,z4,z5,z6]),(0,[z1,z448,z2,z3,z4,z5,z6]),(0,[z1,z2,z315,z4,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z250])],[(0,[z1,z2,z449,z3,z4,z5,z6]),(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z36,z4,z5,z6])],[(0,[z109,z1,z2,z15,z4,z5,z6]),(0,[z105,z1,z2,z3,z4,z74,z5]),(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z1,z2,z4,z139,z5,z12,z6])],[(0,[z1,z2,z4,z5,z451,z12,z6]),(0,[z1,z2,z3,z4,z5,z444,z6]),(0,[z1,z2,z436,z3,z4,z5,z6]),(0,[z1,z2,z3,z452,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z453,z6]),(0,[z75,z1,z2,z15,z4,z5,z6])],[(0,[z1,z2,z3,z4,z101,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z454]),(0,[z1,z2,z3,z455,z4,z5,z6])],[(0,[z1,z2,z456,z3,z4,z5,z6]),(0,[z1,z2,z4,z215,z5,z12,z6]),(0,[z2,z3,z4,z11,z5,z259,z6]),(0,[z131,z105,z1,z2,z3,z4,z5]),(0,[z1,z270,z2,z3,z4,z5,z313]),(0,[z1,z2,z457,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z458,z5,z6])]],
   [[(0,[z1,z2,z459,z15,z4,z5,z6])],[(0,[z1,z2,z460,z4,z215,z5,z6]),(0,[z1,z2,z461,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z157,z6])],[(0,[z1,z2,z3,z4,z462,z5,z6]),(1,[z463,z1,z2,z3,z4,z5]),(0,[z105,z79,z1,z2,z3,z4,z5]),(0,[z1,z20,z2,z4,z5,z12,z6]),(1,[z1,z2,z4,z12,z60,z6]),(0,[z1,z2,z3,z4,z464,z5,z6]),(0,[z1,z2,z465,z3,z4,z5,z6])],[(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z79,z196,z1,z2,z3,z4,z5]),(0,[z1,z25,z2,z15,z4,z5,z6]),(0,[z1,z2,z468,z3,z4,z5,z6]),(0,[z1,z2,z3,z469,z4,z5,z6])],[(0,[z470,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z370,z6]),(0,[z1,z2,z3,z4,z5,z6,z471]),(0,[z42,z1,z2,z15,z4,z5,z6])],[(0,[z1,z472,z2,z3,z4,z5,z6]),(0,[z51,z1,z192,z2,z3,z5,z6]),(1,[z1,z2,z3,z4,z5,z160]),(0,[z1,z72,z2,z4,z5,z12,z6])],[(0,[z39,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z259,z12,z6]),(0,[z1,z2,z3,z4,z473,z5,z6]),(0,[z1,z2,z59,z122,z3,z5,z6]),(0,[z1,z474,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z475,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z259,z12,z6]),(0,[z1,z2,z3,z476,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z477,z6]),(0,[z1,z478,z2,z3,z4,z5,z6]),(0,[z1,z2,z411,z3,z4,z5,z6]),(0,[z1,z479,z2,z3,z4,z5,z6])]],
   [[(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z480,z6]),(0,[z1,z481,z2,z3,z4,z5,z6]),(0,[z1,z192,z154,z3,z4,z5,z6]),(1,[z1,z2,z122,z235,z5,z6]),(0,[z1,z2,z3,z4,z482,z5,z6])],[(0,[z1,z2,z3,z4,z5,z417,z259]),(0,[z483,z1,z2,z3,z4,z5,z6]),(0,[z24,z1,z2,z4,z5,z12,z6]),(1,[z1,z383,z2,z3,z5,z6]),(0,[z1,z2,z484,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z485,z5,z6]),(0,[z1,z2,z486,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z487,z5,z6]),(1,[z1,z2,z3,z107,z5,z108])],[(0,[z196,z1,z2,z3,z4,z5,z40]),(0,[z1,z2,z3,z4,z5,z488,z6]),(0,[z1,z20,z2,z4,z245,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z489]),(0,[z1,z2,z4,z43,z5,z6,z28])],[(1,[z1,z200,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z490,z5,z6]),(0,[z1,z2,z224,z3,z4,z155,z6]),(1,[z1,z2,z283,z4,z5,z6])],[(0,[z1,z2,z122,z3,z4,z5,z471])],[(0,[z138,z1,z2,z3,z31,z5,z6]),(0,[z491,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z492,z5,z6]),(0,[z493,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z494]),(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z225,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z2,z71,z3,z114,z4,z5,z6]),(0,[z1,z2,z495,z3,z4,z5,z6]),(0,[z1,z496,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z497,z6])],[(0,[z498,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z245,z5,z6]),(0,[z1,z499,z2,z3,z4,z5,z6]),(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z501,z5,z6]),(0,[z1,z2,z3,z288,z5,z12,z6]),(0,[z1,z2,z3,z4,z502,z5,z6])],[(0,[z1,z2,z3,z4,z5,z503,z6]),(0,[z409,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z59,z3,z4,z504,z5]),(0,[z1,z2,z98,z3,z4,z150,z6]),(0,[z1,z2,z505,z3,z4,z5,z6])],[(0,[z506,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z507,z4,z5,z6]),(0,[z109,z1,z202,z2,z3,z5,z6]),(0,[z1,z508,z2,z3,z4,z5,z6]),(0,[z509,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z510,z5,z6]),(0,[z1,z511,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z313]),(0,[z1,z2,z15,z224,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z512])],[(0,[z1,z2,z71,z3,z4,z5,z6]),(1,[z1,z2,z460,z4,z5,z6]),(0,[z1,z2,z3,z4,z513,z5,z6]),(0,[z1,z270,z3,z4,z5,z6,z313]),(0,[z1,z2,z514,z3,z4,z5,z6])],[(0,[z1,z2,z88,z3,z4,z5,z6]),(0,[z1,z2,z515,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z28])],[(1,[z1,z385,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z160]),(0,[z1,z202,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z516,z6]),(0,[z1,z2,z3,z4,z5,z323,z6])],[(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z196,z1,z2,z3,z4,z139,z5]),(1,[z24,z1,z3,z4,z46,z6]),(0,[z24,z1,z2,z3,z4,z12,z6]),(0,[z1,z2,z3,z4,z5,z518,z6]),(0,[z1,z2,z3,z5,z86,z143,z6]),(0,[z1,z2,z15,z3,z4,z12,z6]),(0,[z1,z2,z3,z4,z74,z5,z6])]],
   [[(0,[z1,z2,z3,z284,z4,z5,z6]),(0,[z1,z200,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z196,z2,z3,z4,z5,z6,z41]),(0,[z1,z519,z2,z3,z4,z5,z6]),(0,[z138,z1,z192,z2,z3,z5,z6]),(0,[z1,z2,z15,z122,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z520,z6])],[(0,[z75,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z21,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z1,z2,z59,z4,z5,z12,z6])],[(0,[z1,z2,z3,z4,z521,z5,z6]),(0,[z1,z2,z3,z4,z26,z5,z6])],[(0,[z209,z241,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z1,z2,z3,z4,z523,z5,z6]),(0,[z524,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z525,z5,z6]),(0,[z1,z2,z3,z107,z4,z139,z5])],[(0,[z1,z2,z459,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z526]),(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z1,z161,z2,z3,z150,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z528]),(0,[z1,z253,z2,z4,z5,z12,z6]),(0,[z340,z1,z2,z3,z4,z5,z6]),(0,[z1,z529,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z530,z5,z6]),(0,[z463,z1,z2,z3,z4,z5,z259]),(0,[z1,z2,z3,z531,z4,z5,z6]),(0,[z1,z532,z2,z3,z4,z5,z6]),(0,[z533,z1,z2,z3,z4,z5,z6])],[(0,[z100,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z534]),(0,[z196,z1,z270,z2,z3,z4,z5]),(0,[z1,z25,z2,z3,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6]),(0,[z1,z2,z15,z99,z4,z5,z6]),(0,[z1,z2,z3,z4,z536,z5,z6])]],
   [[(0,[z1,z537,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z21,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z538]),(0,[z1,z161,z2,z4,z5,z12,z6])],[(0,[z1,z2,z15,z4,z5,z40,z6]),(0,[z539,z1,z2,z3,z4,z5,z6]),(0,[z1,z82,z3,z4,z245,z5,z6])],[(0,[z1,z2,z3,z4,z540,z5,z6]),(0,[z1,z2,z3,z4,z541,z5,z6]),(1,[z1,z2,z341,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z542,z6])],[(0,[z1,z2,z3,z4,z5,z543,z6]),(0,[z1,z2,z15,z4,z5,z6,z108])],[(1,[z100,z184,z3,z4,z5,z6]),(1,[z1,z2,z311,z5,z12,z6])],[(0,[z1,z2,z4,z245,z5,z12,z6]),(0,[z1,z29,z2,z4,z5,z12,z6])],[(0,[z1,z2,z544,z3,z4,z5,z6]),(0,[z39,z1,z2,z3,z4,z11,z6]),(1,[z1,z2,z3,z146,z5,z6]),(0,[z1,z2,z4,z43,z5,z12,z6])],[(0,[z545,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z99,z3,z4,z6,z250]),(0,[z546,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z547,z5,z6]),(0,[z1,z2,z3,z4,z548,z5,z6]),(0,[z1,z2,z3,z4,z5,z549,z6]),(1,[z1,z2,z4,z259,z12,z6])],[(0,[z1,z2,z154,z3,z215,z5,z6]),(0,[z1,z2,z3,z4,z550,z5,z6]),(0,[z1,z2,z3,z4,z551,z5,z6]),(0,[z1,z2,z3,z4,z552,z5,z6])],[(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z2,z553,z3,z4,z5,z6])],[(0,[z1,z2,z3,z215,z147,z5,z6]),(0,[z1,z2,z3,z4,z147,z5,z6]),(0,[z1,z2,z3,z4,z554,z5,z6]),(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z1,z557,z2,z3,z4,z5,z6])],[(0,[z24,z1,z2,z3,z4,z155,z6]),(0,[z1,z2,z3,z4,z370,z5,z6]),(0,[z1,z2,z15,z3,z4,z155,z6])],[(0,[z81,z1,z72,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z259,z6]),(0,[z1,z2,z21,z3,z4,z543,z6]),(0,[z558,z1,z2,z3,z4,z5,z6])],[(0,[z1,z205,z2,z4,z215,z5,z6]),(0,[z1,z2,z3,z4,z5,z559,z6]),(0,[z1,z2,z3,z372,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z561,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z460,z3,z4,z5,z6]),(0,[z1,z202,z2,z3,z5,z6,z108]),(0,[z1,z161,z2,z122,z4,z5,z6]),(0,[z298,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z562,z5,z6])]],
   [[(0,[z1,z2,z563,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z564,z5,z6]),(0,[z1,z270,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z155,z5,z6])],[(0,[z1,z2,z3,z4,z5,z565,z6]),(0,[z1,z2,z566,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z538]),(0,[z1,z2,z3,z4,z567,z5,z6])],[(0,[z1,z202,z2,z3,z4,z5,z6]),(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z86,z6]),(1,[z1,z2,z288,z5,z12,z6]),(0,[z131,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z99,z4,z5,z12,z6])],[(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z12,z6,z250])],[(0,[z1,z2,z3,z570,z4,z5,z6]),(0,[z1,z571,z2,z3,z4,z5,z6]),(0,[z572,z1,z2,z3,z4,z5,z6]),(0,[z1,z270,z2,z3,z4,z139,z5]),(0,[z1,z2,z573,z3,z4,z5,z6])],[(0,[z1,z2,z574,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z575]),(0,[z1,z72,z2,z122,z3,z5,z6]),(0,[z1,z2,z311,z4,z5,z12,z6]),(0,[z1,z2,z576,z3,z4,z5,z6])],[(0,[z81,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z577,z6]),(0,[z1,z2,z578,z3,z4,z5,z6]),(0,[z79,z1,z2,z15,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z471])],[(0,[z1,z2,z579,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z86,z6,z313]),(0,[z1,z2,z224,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z580,z3,z4,z5,z6]),(0,[z1,z581,z2,z3,z4,z5,z6]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z583,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z155,z5,z12,z6]),(0,[z1,z2,z3,z4,z584,z5,z6]),(0,[z1,z2,z3,z4,z74,z6,z250])],[(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z586,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z28])],[(0,[z1,z2,z3,z587,z4,z5,z6])],[(0,[z100,z1,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z154,z3,z5,z6]),(1,[z1,z2,z3,z4,z521,z5]),(0,[z1,z2,z3,z588,z4,z5,z6]),(0,[z589,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z590,z6]),(0,[z1,z2,z3,z4,z43,z5,z6])],[(0,[z70,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z591,z4,z5,z6]),(0,[z1,z2,z3,z4,z592,z5,z6]),(0,[z1,z2,z3,z4,z5,z593,z6]),(0,[z1,z2,z98,z3,z150,z5,z6])],[(0,[z1,z2,z21,z3,z4,z437,z6]),(0,[z1,z2,z594,z3,z4,z5,z6]),(0,[z1,z595,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z596,z5,z6]),(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z39,z1,z25,z2,z3,z4,z6]),(0,[z196,z1,z2,z3,z4,z5,z108]),(0,[z1,z82,z2,z4,z245,z5,z6]),(0,[z1,z2,z3,z4,z5,z598,z6]),(0,[z1,z2,z4,z235,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z6,z428]),(0,[z599,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z372,z5,z6]),(0,[z1,z2,z154,z3,z4,z5,z538]),(0,[z79,z1,z2,z3,z4,z139,z5]),(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6])]],
   [[(0,[z81,z1,z2,z3,z4,z83,z6]),(0,[z602,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z277,z5,z6]),(1,[z1,z2,z224,z4,z12,z6]),(0,[z1,z2,z59,z3,z4,z5,z254])],[(0,[z1,z603,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z604,z6]),(0,[z1,z2,z3,z4,z155,z60,z6]),(0,[z42,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z605,z5,z6]),(0,[z1,z606,z2,z3,z4,z5,z6])],[(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z2,z608,z3,z4,z5,z6]),(0,[z1,z2,z609,z15,z4,z5,z6]),(0,[z138,z1,z2,z15,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z417]),(0,[z1,z352,z2,z4,z5,z12,z6]),(0,[z1,z265,z2,z3,z4,z5,z6]),(0,[z1,z610,z2,z15,z4,z5,z6])],[(0,[z1,z335,z2,z3,z4,z5,z6]),(0,[z611,z1,z2,z3,z4,z5,z6]),(0,[z1,z612,z2,z3,z4,z5,z6])],[(0,[z70,z1,z2,z114,z4,z5,z6]),(0,[z1,z2,z3,z4,z613,z5,z6]),(0,[z1,z202,z2,z154,z3,z5,z6]),(1,[z1,z2,z36,z4,z5,z28]),(0,[z614,z1,z2,z3,z4,z5,z6])],[(0,[z209,z1,z184,z3,z4,z5,z6]),(0,[z463,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z615,z3,z4,z5,z6]),(0,[z1,z616,z2,z3,z4,z5,z6])],[(0,[z51,z1,z202,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z617,z6]),(0,[z1,z2,z3,z4,z618,z5,z6])]],
   [[(0,[z1,z385,z2,z184,z3,z5,z6]),(0,[z24,z1,z2,z3,z4,z26,z6])],[(0,[z1,z2,z184,z15,z4,z5,z6]),(0,[z1,z619,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z620]),(0,[z1,z2,z122,z3,z150,z5,z6]),(0,[z1,z2,z15,z4,z5,z5,z6]),(0,[z1,z2,z3,z621,z4,z5,z6])],[(0,[z1,z2,z622,z3,z4,z5,z6]),(0,[z1,z623,z2,z3,z4,z5,z6])],[(1,[z51,z2,z3,z31,z5,z6]),(0,[z1,z2,z15,z31,z4,z5,z6]),(0,[z1,z21,z3,z4,z245,z5,z6]),(0,[z1,z2,z3,z4,z624,z5,z6])],[(0,[z625,z1,z2,z3,z4,z5,z6]),(0,[z81,z1,z20,z2,z4,z5,z6]),(0,[z626,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z176,z3,z4,z5,z6]),(0,[z1,z161,z2,z59,z3,z5,z6]),(1,[z1,z2,z99,z4,z12,z6]),(1,[z1,z2,z17,z4,z5,z6])],[(0,[z1,z82,z2,z21,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z313]),(0,[z1,z2,z4,z5,z12,z6,z313]),(0,[z1,z2,z122,z4,z5,z12,z6])],[(0,[z1,z627,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z215,z5,z6]),(0,[z1,z2,z3,z4,z504,z5,z6])],[(0,[z1,z241,z2,z15,z4,z5,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z629,z1,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z5,z60,z6])]],
   [[(1,[z1,z2,z3,z101,z5,z6]),(0,[z1,z2,z3,z4,z5,z630,z6]),(0,[z1,z2,z3,z31,z147,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6])],[(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z83,z6]),(0,[z1,z2,z21,z4,z5,z12,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z633,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z634,z5,z6])],[(0,[z81,z70,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z543,z6]),(0,[z1,z2,z154,z4,z5,z12,z6]),(0,[z1,z2,z3,z635,z4,z5,z6]),(0,[z1,z555,z2,z15,z4,z5,z6]),(1,[z1,z2,z98,z3,z150,z6])],[(1,[z1,z68,z2,z3,z5,z6]),(0,[z209,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z636,z3,z4,z5,z6]),(0,[z1,z637,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z92,z6]),(0,[z1,z2,z638,z3,z4,z5,z6])],[(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z1,z192,z2,z4,z5,z12,z6]),(0,[z1,z2,z640,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z5,z12,z6]),(0,[z641,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z642,z6]),(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z644,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z645,z3,z4,z5,z6]),(0,[z75,z2,z3,z4,z5,z259,z6]),(0,[z1,z2,z646,z3,z4,z5,z6]),(0,[z647,z1,z2,z3,z4,z5,z6]),(1,[z1,z202,z3,z147,z5,z6]),(0,[z1,z2,z3,z4,z5,z12,z6])],[(0,[z196,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z5,z6,z648]),(0,[z1,z2,z3,z4,z5,z56,z6])],[(0,[z1,z2,z3,z4,z649,z5,z6]),(0,[z1,z2,z3,z650,z4,z5,z6]),(1,[z1,z2,z407,z4,z5,z6]),(0,[z1,z2,z15,z59,z4,z5,z6])]],
   [[(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z651,z5,z6]),(0,[z1,z2,z3,z4,z652,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z653]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z655,z4,z5,z6]),(0,[z1,z2,z4,z5,z12,z6,z656])],[(0,[z1,z202,z3,z4,z147,z5,z6]),(0,[z138,z1,z202,z2,z3,z5,z6]),(0,[z1,z2,z154,z3,z4,z521,z5]),(0,[z1,z2,z657,z3,z4,z5,z6]),(0,[z409,z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z15,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z658,z5,z6]),(0,[z1,z2,z3,z4,z659,z5,z6]),(0,[z1,z2,z3,z4,z5,z361,z6])],[(0,[z39,z1,z2,z3,z4,z259,z6]),(0,[z1,z270,z2,z3,z4,z5,z108]),(0,[z1,z2,z3,z4,z139,z43,z5]),(0,[z1,z2,z3,z4,z5,z660,z6])],[(0,[z661,z1,z2,z3,z4,z5,z6]),(0,[z1,z205,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z12,z6,z41]),(0,[z1,z2,z3,z4,z5,z662,z6]),(0,[z663,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z664,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z215,z5,z6]),(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z666,z6]),(1,[z1,z2,z591,z4,z5,z6]),(0,[z1,z2,z3,z4,z245,z5,z6]),(0,[z1,z383,z2,z3,z5,z86,z6]),(0,[z1,z2,z3,z4,z5,z667,z6]),(0,[z1,z2,z99,z3,z4,z5,z108])],[(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z609,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z6])],[(1,[z1,z335,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z669,z5,z6]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z105,z1,z2,z15,z4,z5,z6]),(0,[z1,z610,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z451,z6])]],
   [[(0,[z1,z2,z3,z4,z670,z5,z6]),(0,[z1,z671,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z46,z6]),(0,[z1,z2,z384,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z672,z5,z6]),(0,[z1,z2,z673,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z674,z5,z6]),(0,[z1,z2,z122,z3,z235,z5,z6]),(0,[z131,z1,z2,z99,z3,z4,z6])],[(0,[z1,z2,z3,z675,z4,z5,z6]),(1,[z1,z2,z3,z4,z437,z6]),(1,[z1,z2,z311,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z656])],[(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z114,z4,z5,z12,z6]),(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z678]),(0,[z1,z679,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z680])],[(0,[z1,z2,z3,z4,z5,z681,z6]),(0,[z1,z682,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z683,z5,z6]),(0,[z1,z2,z3,z4,z5,z193,z6]),(0,[z684,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z685,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z288,z5,z6]),(0,[z686,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z184,z3,z4,z5,z6]),(0,[z1,z2,z687,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z11,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z41]),(0,[z1,z2,z3,z688,z4,z5,z6]),(0,[z1,z2,z15,z4,z139,z5,z6])],[(0,[z209,z1,z241,z3,z4,z5,z6]),(0,[z1,z2,z311,z3,z5,z12,z6]),(0,[z1,z2,z15,z35,z4,z5,z6]),(0,[z1,z2,z59,z207,z4,z5,z6])],[(0,[z1,z689,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z690]),(0,[z196,z1,z2,z3,z4,z74,z5]),(0,[z1,z270,z2,z3,z4,z5,z86]),(0,[z1,z2,z691,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z692,z3,z4,z5,z6]),(0,[z105,z1,z2,z3,z4,z139,z5]),(1,[z1,z2,z15,z4,z12,z6]),(0,[z1,z2,z17,z4,z150,z5,z6])],[(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z695,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z696,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z697]),(0,[z70,z1,z2,z71,z4,z5,z6])],[(0,[z1,z241,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z12,z565,z6]),(1,[z1,z2,z3,z4,z103,z6]),(0,[z1,z2,z3,z139,z5,z6,z108]),(0,[z1,z2,z3,z4,z698,z5,z6])],[(0,[z100,z2,z184,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z215,z5,z6]),(0,[z123,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z157,z6]),(0,[z699,z1,z2,z3,z4,z5,z6])],[(1,[z1,z192,z154,z3,z5,z6]),(0,[z1,z700,z2,z3,z4,z5,z6])],[(0,[z701,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z702,z5,z6]),(0,[z1,z2,z3,z4,z5,z703,z6])],[(0,[z1,z2,z279,z184,z3,z4,z6]),(0,[z1,z2,z88,z184,z3,z4,z5]),(0,[z1,z2,z3,z4,z704,z5,z6]),(0,[z1,z2,z3,z215,z5,z6,z108]),(0,[z75,z1,z2,z591,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z1,z706,z2,z3,z4,z5,z6]),(0,[z1,z2,z129,z15,z4,z5,z6]),(1,[z1,z2,z3,z4,z504,z5]),(0,[z1,z2,z3,z4,z5,z6,z108]),(1,[z138,z1,z2,z3,z139,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z335,z2,z279,z4,z6]),(0,[z81,z2,z114,z4,z5,z6]),(0,[z51,z2,z3,z31,z5,z160]),(0,[z75,z2,z4,z259,z12,z6]),(0,[z79,z1,z2,z3,z146,z5]),(0,[z1,z2,z17,z4,z370,z6]),(0,[z1,z2,z707,z4,z74,z6]),(0,[z1,z2,z59,z3,z60,z254])],[(0,[z1,z2,z3,z708,z5,z6]),(0,[z1,z450,z2,z3,z5,z108]),(0,[z1,z2,z315,z4,z103,z6]),(0,[z1,z2,z99,z709,z3,z4])],[(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z2,z711,z4,z5,z6]),(0,[z1,z2,z4,z251,z12,z6])],[(0,[z1,z712,z3,z4,z5,z6]),(0,[z1,z2,z17,z4,z5,z6])],[(0,[z1,z2,z3,z4,z713,z6]),(0,[z1,z2,z3,z5,z143,z6]),(0,[z1,z2,z3,z4,z714,z6]),(0,[z1,z2,z4,z12,z426,z6]),(0,[z1,z2,z4,z5,z715,z6]),(0,[z1,z72,z2,z716,z5,z6]),(0,[z1,z2,z553,z4,z12,z6]),(0,[z1,z2,z717,z5,z12,z6])],[(0,[z718,z1,z2,z3,z4,z6]),(0,[z81,z2,z114,z4,z124,z6]),(0,[z51,z2,z3,z719,z5,z6]),(0,[z1,z2,z288,z11,z12,z6])],[(0,[z63,z1,z2,z15,z4,z6]),(0,[z1,z2,z4,z5,z720,z6]),(0,[z1,z2,z71,z4,z83,z6]),(0,[z1,z2,z4,z124,z12,z6]),(0,[z1,z2,z4,z11,z12,z6]),(0,[z1,z2,z721,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z270,z4,z5,z12,z313]),(0,[z1,z2,z716,z122,z5,z6]),(0,[z1,z2,z306,z4,z12,z6]),(0,[z1,z2,z311,z5,z6,z54]),(0,[z1,z2,z723,z15,z5,z6]),(0,[z1,z2,z15,z4,z103,z6])],[(0,[z1,z2,z3,z101,z5,z6]),(0,[z63,z1,z2,z724,z4,z6]),(0,[z1,z2,z3,z4,z725,z6]),(0,[z1,z2,z726,z4,z5,z6]),(0,[z1,z2,z3,z4,z727,z6]),(0,[z1,z2,z728,z4,z5,z6]),(0,[z1,z2,z3,z4,z729,z5]),(0,[z1,z3,z4,z26,z730,z6])]],
   [[(0,[z1,z2,z4,z268,z12,z6]),(0,[z1,z2,z3,z731,z5,z6])],[(0,[z63,z100,z184,z3,z4,z6]),(0,[z1,z732,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z543,z6]),(0,[z1,z2,z98,z3,z150,z6])],[(0,[z1,z68,z2,z3,z5,z6]),(0,[z1,z2,z733,z4,z5,z6]),(0,[z1,z2,z696,z4,z12,z6]),(0,[z39,z2,z34,z4,z11,z6]),(0,[z1,z202,z312,z3,z5,z6]),(0,[z24,z1,z2,z4,z27,z6]),(0,[z1,z2,z55,z3,z277,z5]),(0,[z1,z2,z4,z323,z12,z6]),(0,[z1,z2,z15,z4,z504,z5])],[(0,[z100,z190,z184,z3,z4,z5]),(0,[z734,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z3,z4,z277,z136]),(0,[z1,z2,z4,z5,z49,z6])],[(0,[z1,z202,z3,z147,z5,z6]),(0,[z1,z2,z4,z277,z5,z12]),(0,[z1,z2,z709,z3,z4,z74])],[(0,[z1,z2,z3,z737,z5,z6]),(0,[z1,z738,z4,z5,z12,z6]),(0,[z1,z2,z739,z5,z12,z6]),(0,[z42,z1,z2,z43,z5,z157]),(0,[z1,z2,z98,z17,z150,z6])],[(0,[z1,z2,z407,z4,z5,z6]),(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z555,z2,z35,z5,z6])],[(0,[z1,z2,z176,z4,z5,z6]),(0,[z1,z2,z59,z3,z136,z6]),(0,[z1,z2,z15,z4,z5,z741])]],
   [[(0,[z75,z2,z3,z4,z417,z259]),(0,[z1,z2,z207,z4,z5,z254])],[(0,[z463,z1,z2,z15,z4,z5]),(0,[z2,z3,z4,z5,z742,z41]),(0,[z1,z2,z3,z4,z743,z5]),(0,[z2,z4,z5,z12,z744,z6]),(0,[z1,z2,z15,z288,z12,z6])],[(0,[z63,z1,z2,z4,z12,z6]),(0,[z81,z2,z745,z4,z5,z6]),(0,[z1,z2,z3,z5,z746,z6]),(0,[z1,z2,z747,z4,z5,z6])],[(0,[z1,z20,z89,z4,z5,z6]),(0,[z1,z2,z3,z5,z417,z746]),(0,[z1,z2,z15,z55,z5,z6]),(0,[z1,z2,z36,z4,z92,z6])],[(0,[z1,z748,z2,z279,z4,z6]),(0,[z1,z2,z4,z462,z12,z6]),(0,[z1,z270,z579,z3,z4,z5]),(0,[z1,z2,z749,z4,z5,z6]),(0,[z1,z25,z2,z4,z27,z6]),(0,[z1,z2,z3,z588,z5,z108]),(0,[z1,z2,z15,z5,z750,z6])],[(0,[z298,z2,z114,z4,z5,z6]),(0,[z1,z2,z4,z5,z751,z6]),(0,[z1,z2,z98,z150,z12,z6])],[(0,[z1,z335,z2,z4,z5,z6]),(0,[z1,z205,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z752,z6]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z1,z2,z754,z4,z5,z6]),(0,[z1,z2,z36,z4,z755,z5]),(0,[z1,z2,z98,z150,z56,z6]),(0,[z1,z2,z709,z3,z4,z250])],[(0,[z1,z2,z756,z4,z5,z6]),(0,[z1,z2,z757,z3,z4,z6]),(0,[z2,z3,z31,z719,z5,z6]),(0,[z1,z2,z758,z4,z5,z6]),(0,[z196,z1,z2,z4,z74,z12]),(0,[z1,z2,z4,z543,z12,z6]),(0,[z759,z2,z3,z4,z5,z6]),(0,[z1,z2,z311,z3,z150,z6])]],
   [[(0,[z1,z2,z3,z760,z5,z6]),(0,[z1,z21,z761,z4,z5,z6]),(0,[z131,z1,z2,z709,z3,z4])],[(0,[z1,z2,z88,z4,z5,z12]),(0,[z1,z2,z274,z4,z12,z6]),(0,[z1,z2,z3,z4,z437,z6]),(0,[z1,z2,z311,z3,z5,z6]),(0,[z1,z2,z4,z5,z12,z471]),(0,[z1,z2,z3,z458,z60,z6])],[(0,[z2,z3,z4,z5,z762,z6]),(0,[z2,z3,z4,z5,z763,z6]),(0,[z1,z2,z225,z4,z5,z6]),(0,[z1,z2,z4,z504,z5,z12]),(0,[z1,z2,z311,z74,z12,z6]),(0,[z1,z2,z315,z4,z12,z6])],[(0,[z1,z2,z15,z4,z83,z6]),(0,[z1,z2,z764,z4,z5,z6]),(0,[z1,z2,z3,z107,z765,z5])],[(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z2,z3,z32,z5,z108]),(0,[z767,z1,z2,z4,z5,z12]),(0,[z1,z2,z311,z3,z5,z768])],[(0,[z1,z2,z3,z215,z5,z538]),(0,[z138,z1,z2,z3,z5,z346]),(0,[z1,z2,z15,z4,z92,z6])],[(0,[z1,z2,z4,z5,z769,z6]),(0,[z24,z1,z407,z4,z46,z6]),(0,[z24,z1,z4,z46,z12,z6])],[(0,[z770,z1,z2,z3,z4,z5]),(0,[z109,z414,z2,z3,z5,z6]),(0,[z771,z1,z2,z3,z4,z5]),(0,[z1,z161,z2,z150,z12,z6]),(0,[z1,z2,z15,z4,z12,z6])]],
   [[(0,[z1,z82,z210,z4,z5,z6]),(1,[z1,z2,z4,z772,z6]),(0,[z1,z773,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z1,z2,z5,z12,z143,z6]),(0,[z1,z2,z122,z5,z56,z6]),(0,[z775,z1,z2,z4,z5,z12]),(0,[z42,z1,z2,z4,z43,z5])],[(0,[z1,z2,z3,z4,z776,z6]),(0,[z2,z3,z719,z4,z5,z6]),(0,[z1,z82,z4,z245,z5,z6]),(0,[z1,z3,z737,z147,z5,z6]),(0,[z1,z2,z225,z59,z60,z6]),(0,[z1,z2,z204,z4,z74,z6])],[(0,[z190,z1,z335,z2,z4,z5]),(0,[z1,z2,z3,z4,z103,z6]),(0,[z1,z529,z2,z3,z5,z108])],[(0,[z1,z335,z68,z2,z5,z6]),(0,[z777,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z778,z6]),(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z2,z311,z150,z12,z6])],[(0,[z100,z184,z3,z101,z5,z6]),(0,[z1,z2,z114,z4,z83,z6]),(0,[z1,z192,z154,z3,z5,z6]),(0,[z1,z2,z122,z150,z12,z6]),(0,[z1,z2,z780,z5,z12,z6]),(0,[z1,z2,z311,z12,z60,z6]),(0,[z1,z2,z3,z4,z74,z250]),(0,[z1,z2,z781,z204,z5,z6])],[(0,[z1,z385,z2,z15,z5,z6]),(0,[z75,z463,z2,z3,z4,z259]),(0,[z1,z2,z213,z4,z12,z6]),(0,[z1,z82,z761,z4,z5,z6]),(0,[z1,z2,z311,z207,z5,z6]),(0,[z42,z1,z2,z4,z43,z103]),(0,[z1,z2,z59,z3,z782,z6]),(0,[z1,z2,z783,z4,z5,z6])],[(0,[z1,z2,z4,z347,z12,z6]),(0,[z1,z2,z15,z4,z662,z6]),(0,[z1,z784,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z504,z5]),(0,[z138,z1,z2,z3,z139,z5]),(0,[z1,z785,z2,z204,z5,z6])],[(0,[z1,z2,z4,z350,z12,z6]),(0,[z1,z2,z59,z3,z60,z6]),(1,[z1,z2,z3,z782,z6])]],
   [[(0,[z1,z2,z3,z4,z786,z6]),(0,[z1,z2,z787,z3,z4,z6]),(0,[z1,z788,z3,z4,z5,z6]),(0,[z1,z761,z4,z245,z5,z6]),(0,[z79,z1,z2,z3,z5,z143]),(0,[z1,z2,z3,z4,z789,z6]),(0,[z1,z2,z288,z74,z12,z6]),(0,[z1,z2,z304,z4,z5,z28])],[(0,[z63,z1,z335,z2,z4,z6]),(0,[z790,z1,z2,z3,z4,z5]),(0,[z1,z2,z622,z4,z12,z6]),(0,[z791,z1,z2,z3,z4,z5]),(0,[z24,z1,z3,z4,z658,z6]),(0,[z1,z25,z15,z4,z26,z6])],[(0,[z1,z2,z792,z4,z5,z6]),(0,[z1,z748,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z793,z5]),(0,[z1,z623,z2,z4,z12,z6]),(0,[z1,z2,z4,z12,z361,z6])],[(0,[z1,z2,z279,z3,z4,z6]),(0,[z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z393,z4,z12,z6]),(0,[z1,z2,z4,z359,z12,z6]),(0,[z1,z2,z4,z5,z12,z160]),(0,[z1,z2,z15,z5,z143,z6])],[(0,[z1,z2,z3,z4,z794,z6]),(0,[z1,z2,z4,z271,z12,z6]),(0,[z1,z2,z3,z4,z795,z6]),(1,[z1,z761,z4,z5,z6]),(0,[z1,z2,z3,z136,z6,z108]),(0,[z2,z4,z5,z12,z796,z6])],[(0,[z1,z2,z4,z364,z12,z6])],[(0,[z1,z481,z154,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z742]),(0,[z1,z2,z122,z288,z5,z6]),(0,[z1,z2,z685,z4,z12,z6]),(0,[z1,z2,z4,z5,z56,z6])],[(0,[z1,z2,z3,z4,z5,z797]),(0,[z1,z2,z798,z4,z5,z6]),(0,[z1,z2,z4,z368,z12,z6]),(0,[z1,z2,z315,z4,z155,z6])]],
   [[(0,[z1,z2,z3,z4,z799,z5]),(0,[z1,z2,z4,z530,z12,z6]),(0,[z1,z3,z4,z5,z800,z6]),(0,[z1,z801,z3,z4,z5,z6]),(0,[z1,z154,z3,z737,z5,z6]),(0,[z1,z2,z3,z4,z5,z802]),(0,[z1,z2,z122,z455,z5,z6]),(0,[z1,z2,z4,z5,z12,z768]),(0,[z1,z2,z4,z289,z12,z6]),(0,[z1,z2,z3,z5,z750,z6]),(0,[z1,z2,z709,z3,z4,z5])],[(0,[z1,z2,z3,z4,z803,z6]),(0,[z1,z555,z2,z288,z12,z6])],[(0,[z1,z804,z2,z3,z5,z6]),(0,[z1,z2,z4,z5,z805,z6]),(0,[z1,z2,z806,z3,z5,z6]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z2,z4,z148,z12,z6]),(0,[z1,z2,z55,z3,z5,z6]),(0,[z1,z2,z4,z5,z12,z809]),(0,[z1,z2,z4,z150,z12,z6]),(0,[z1,z2,z288,z12,z60,z6])],[(0,[z1,z2,z810,z3,z4,z6]),(0,[z1,z2,z811,z4,z5,z6]),(0,[z1,z2,z3,z4,z762,z6])],[(0,[z1,z2,z591,z4,z11,z6]),(0,[z1,z2,z4,z379,z12,z6]),(0,[z1,z2,z4,z5,z812,z6]),(0,[z1,z2,z15,z4,z155,z6])],[(0,[z1,z2,z3,z4,z813,z5]),(0,[z1,z182,z21,z4,z5,z6]),(0,[z814,z2,z3,z4,z5,z6]),(0,[z1,z2,z311,z3,z815,z5]),(0,[z1,z2,z609,z4,z92,z6])],[(0,[z1,z2,z3,z816,z5,z6]),(0,[z1,z2,z817,z3,z4,z5]),(0,[z2,z3,z4,z11,z762,z6]),(0,[z1,z2,z818,z4,z5,z6]),(0,[z131,z1,z2,z99,z204,z4])],[(0,[z1,z2,z15,z4,z375,z6]),(0,[z42,z1,z2,z4,z755,z5])]],
   [[(0,[z1,z2,z4,z819,z5,z6]),(0,[z1,z2,z820,z3,z5,z6]),(0,[z1,z2,z578,z3,z139,z5]),(0,[z1,z4,z5,z821,z12,z6]),(0,[z1,z2,z15,z4,z5,z254]),(0,[z1,z2,z3,z5,z163,z108])],[(0,[z1,z2,z88,z3,z4,z5]),(0,[z1,z2,z4,z396,z12,z6]),(0,[z1,z2,z3,z4,z92,z6])],[(0,[z100,z200,z184,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z2,z823,z4,z5,z6]),(0,[z1,z270,z3,z4,z584,z5]),(0,[z1,z2,z824,z4,z5,z6])],[(0,[z1,z2,z3,z825,z5,z6]),(0,[z1,z202,z495,z3,z5,z6]),(0,[z196,z2,z15,z4,z5,z41])],[(0,[z1,z2,z826,z4,z5,z6]),(0,[z1,z2,z3,z4,z827,z6]),(0,[z767,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z828]),(0,[z1,z2,z829,z4,z12,z6]),(0,[z830,z2,z4,z5,z12,z6]),(0,[z1,z2,z3,z4,z755,z5]),(0,[z1,z2,z831,z4,z5,z6])],[(0,[z190,z1,z2,z279,z3,z4]),(0,[z1,z682,z3,z147,z5,z6]),(0,[z1,z192,z154,z3,z5,z538]),(0,[z24,z1,z2,z311,z12,z6]),(0,[z1,z270,z3,z4,z5,z832]),(0,[z1,z2,z3,z4,z5,z833])],[(0,[z1,z2,z4,z5,z451,z656])],[(0,[z1,z2,z834,z4,z5,z6]),(0,[z1,z2,z835,z4,z5,z6]),(0,[z1,z2,z836,z4,z5,z6]),(0,[z1,z555,z2,z4,z12,z6])]],
   [[(0,[z1,z2,z3,z837,z5,z6]),(0,[z1,z838,z2,z3,z5,z6]),(0,[z1,z20,z21,z4,z5,z6]),(0,[z1,z2,z4,z248,z12,z6]),(0,[z1,z2,z99,z3,z5,z361])],[(0,[z1,z839,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z840]),(0,[z1,z2,z4,z401,z12,z6]),(0,[z24,z1,z2,z4,z841,z6]),(0,[z48,z2,z436,z4,z5,z6])],[(0,[z1,z2,z3,z842,z5,z6]),(0,[z1,z2,z4,z693,z12,z6]),(0,[z1,z2,z3,z4,z5,z843]),(0,[z1,z2,z691,z3,z139,z5])],[(0,[z1,z2,z4,z5,z844,z6]),(0,[z1,z845,z2,z279,z4,z6]),(0,[z1,z2,z846,z4,z5,z6]),(0,[z109,z2,z3,z719,z5,z6]),(0,[z24,z1,z566,z3,z4,z6]),(0,[z1,z2,z847,z3,z5,z6]),(1,[z1,z3,z737,z5,z6]),(0,[z1,z2,z4,z848,z5,z6])],[(0,[z70,z1,z2,z311,z5,z6]),(0,[z138,z1,z2,z12,z60,z6])],[(0,[z100,z385,z184,z3,z5,z6]),(0,[z1,z2,z4,z5,z849,z6]),(0,[z1,z2,z4,z32,z5,z12]),(0,[z850,z2,z3,z4,z5,z6]),(0,[z1,z25,z3,z4,z26,z6]),(0,[z1,z2,z15,z4,z5,z851])],[(0,[z1,z2,z3,z852,z5,z6]),(0,[z1,z2,z4,z12,z44,z6]),(0,[z1,z2,z853,z4,z5,z6]),(0,[z1,z2,z4,z5,z12,z538]),(0,[z42,z1,z2,z4,z43,z92]),(0,[z1,z2,z854,z4,z5,z6]),(0,[z1,z2,z315,z4,z74,z250])],[(0,[z1,z2,z855,z4,z5,z6]),(0,[z1,z2,z856,z3,z5,z6]),(0,[z1,z265,z25,z4,z12,z6]),(0,[z1,z25,z2,z311,z12,z6]),(0,[z1,z2,z15,z5,z361,z6])]],
   [[(0,[z70,z2,z745,z4,z5,z6]),(0,[z1,z25,z4,z26,z12,z6]),(0,[z1,z2,z857,z5,z12,z6]),(0,[z1,z2,z207,z4,z60,z6])],[(0,[z298,z2,z4,z259,z12,z6]),(0,[z1,z2,z858,z5,z12,z6])],[(0,[z100,z184,z4,z5,z12,z6]),(0,[z1,z2,z859,z4,z5,z6]),(0,[z1,z2,z4,z437,z12,z6]),(0,[z1,z2,z3,z5,z230,z108]),(0,[z337,z2,z4,z5,z444,z6]),(0,[z1,z3,z4,z5,z821,z6])],[(0,[z1,z2,z860,z3,z5,z6]),(0,[z1,z2,z4,z5,z861,z6]),(0,[z1,z2,z862,z4,z5,z6]),(0,[z138,z1,z2,z139,z5,z12]),(0,[z1,z2,z15,z4,z74,z250])],[(0,[z1,z2,z3,z4,z5,z863]),(0,[z1,z2,z15,z311,z5,z6])],[(0,[z1,z2,z4,z199,z12,z6]),(0,[z1,z2,z864,z4,z5,z6]),(0,[z1,z2,z4,z5,z865,z6]),(0,[z1,z2,z4,z417,z259,z12]),(0,[z1,z2,z3,z372,z5,z108]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z2,z4,z518,z12,z6]),(0,[z1,z2,z4,z74,z12,z250])],[(0,[z1,z867,z2,z4,z5,z6]),(0,[z1,z868,z2,z4,z5,z6]),(0,[z1,z2,z4,z249,z12,z6]),(0,[z1,z2,z4,z5,z869,z6]),(0,[z1,z2,z781,z3,z5,z6])],[(0,[z1,z2,z3,z284,z5,z870])]],
   [[(0,[z1,z2,z4,z5,z871,z6]),(0,[z81,z2,z594,z4,z5,z6]),(1,[z1,z2,z3,z765,z5]),(0,[z1,z785,z2,z3,z5,z6])],[(0,[z81,z1,z2,z311,z5,z6]),(0,[z1,z2,z4,z872,z5,z6]),(0,[z1,z2,z807,z5,z12,z6]),(0,[z1,z2,z15,z288,z5,z6])],[(0,[z1,z2,z4,z5,z873,z6]),(0,[z1,z2,z3,z765,z5,z6])],[(0,[z1,z2,z4,z5,z772,z6]),(0,[z1,z265,z4,z245,z5,z6]),(0,[z1,z2,z3,z4,z277,z5]),(0,[z1,z2,z3,z4,z458,z250])],[(0,[z1,z2,z15,z284,z5,z6]),(0,[z493,z2,z3,z31,z5,z6]),(0,[z1,z202,z147,z5,z12,z6]),(0,[z1,z2,z4,z458,z12,z6]),(0,[z1,z2,z3,z4,z5,z254])],[(0,[z1,z874,z2,z3,z5,z6])],[],[(0,[z1,z2,z4,z5,z875,z6]),(0,[z1,z2,z3,z5,z876,z6]),(0,[z196,z2,z3,z4,z5,z41]),(0,[z1,z2,z4,z464,z12,z6]),(0,[z1,z2,z15,z4,z5,z802]),(0,[z131,z1,z2,z99,z3,z4])]],
   [[(0,[z1,z2,z3,z877,z5,z6]),(0,[z1,z2,z3,z4,z878,z6]),(0,[z1,z2,z4,z480,z12,z6]),(0,[z1,z2,z288,z259,z12,z6]),(0,[z196,z1,z2,z3,z5,z361]),(0,[z1,z2,z15,z4,z136,z6]),(0,[z1,z2,z4,z5,z451,z28])],[(0,[z1,z845,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z879,z6]),(0,[z1,z880,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z742]),(0,[z105,z2,z15,z4,z5,z40]),(0,[z1,z2,z881,z4,z5,z6]),(0,[z1,z2,z204,z4,z5,z6]),(0,[z1,z2,z15,z5,z157,z6])],[(0,[z1,z72,z2,z4,z83,z6]),(0,[z75,z511,z2,z3,z4,z6]),(0,[z1,z2,z4,z5,z882,z6]),(0,[z1,z161,z2,z716,z5,z6]),(0,[z1,z265,z4,z5,z193,z6]),(0,[z1,z2,z99,z4,z12,z108]),(0,[z1,z2,z4,z155,z848,z6]),(0,[z1,z2,z465,z4,z43,z5])],[(0,[z70,z2,z71,z4,z5,z6]),(0,[z1,z2,z3,z5,z883,z6]),(0,[z1,z2,z884,z4,z5,z6]),(0,[z75,z2,z15,z4,z259,z6]),(0,[z1,z2,z3,z885,z5,z6]),(0,[z1,z2,z4,z473,z12,z6]),(0,[z1,z383,z2,z15,z5,z6]),(0,[z131,z1,z2,z15,z99,z4])],[(0,[z1,z335,z385,z2,z5,z6]),(0,[z1,z886,z2,z4,z5,z6]),(0,[z1,z2,z146,z5,z12,z6]),(0,[z1,z2,z15,z4,z370,z6])],[(0,[z100,z887,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z888,z6]),(0,[z81,z1,z2,z4,z136,z6]),(0,[z889,z1,z2,z3,z4,z5]),(0,[z1,z890,z2,z4,z5,z6]),(0,[z1,z2,z4,z482,z12,z6]),(1,[z1,z2,z12,z361,z6]),(0,[z1,z2,z891,z4,z5,z6])],[(0,[z892,z1,z2,z3,z4,z6]),(0,[z1,z2,z224,z311,z12,z6])],[(0,[z1,z2,z893,z4,z5,z6]),(0,[z70,z2,z4,z5,z444,z6]),(0,[z105,z1,z2,z4,z74,z12]),(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z3,z894,z5,z6])]],
   [[(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z2,z4,z345,z12,z6]),(0,[z1,z192,z3,z737,z5,z6])],[(0,[z1,z2,z3,z4,z772,z6]),(0,[z1,z2,z896,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z2,z3,z4,z5,z851]),(0,[z1,z2,z898,z3,z5,z6]),(0,[z1,z2,z15,z4,z166,z6])],[(0,[z1,z68,z2,z15,z5,z6]),(0,[z1,z2,z899,z3,z4,z6]),(0,[z1,z2,z411,z249,z5,z6]),(0,[z1,z2,z55,z3,z139,z5])],[(0,[z1,z2,z3,z900,z5,z6]),(0,[z1,z2,z3,z5,z361,z6])],[(0,[z1,z2,z15,z4,z124,z6]),(0,[z1,z2,z3,z4,z901,z6]),(0,[z1,z161,z2,z207,z5,z6]),(0,[z1,z2,z902,z4,z5,z6])],[(0,[z1,z2,z3,z4,z903,z6]),(0,[z1,z2,z4,z12,z163,z6])],[(0,[z1,z904,z2,z4,z5,z6]),(0,[z39,z2,z4,z11,z269,z6]),(0,[z1,z2,z3,z4,z905,z6]),(0,[z1,z2,z106,z4,z5,z6]),(0,[z1,z2,z906,z4,z5,z6]),(0,[z1,z2,z907,z4,z5,z6]),(0,[z1,z2,z908,z4,z5,z6]),(0,[z298,z1,z2,z311,z5,z6]),(0,[z1,z2,z4,z12,z164,z6]),(0,[z1,z2,z15,z59,z60,z6])],[(0,[z2,z3,z719,z215,z5,z6]),(0,[z1,z2,z3,z909,z5,z6])]],
   [[(0,[z910,z2,z3,z4,z5,z6]),(0,[z1,z3,z737,z4,z5,z6]),(0,[z180,z1,z2,z4,z12,z6]),(0,[z1,z2,z716,z4,z5,z6]),(0,[z1,z2,z911,z5,z12,z6]),(0,[z1,z2,z4,z5,z12,z912])],[(0,[z1,z2,z591,z4,z259,z6]),(0,[z654,z1,z2,z4,z12,z6]),(0,[z1,z2,z407,z4,z437,z6]),(0,[z1,z2,z122,z207,z5,z6]),(0,[z1,z2,z913,z4,z5,z6])],[(0,[z326,z2,z3,z215,z5,z6]),(0,[z1,z2,z3,z5,z914,z6])],[(0,[z1,z2,z4,z5,z915,z6]),(0,[z1,z2,z916,z4,z5,z6]),(0,[z1,z2,z150,z12,z60,z6]),(0,[z1,z2,z723,z3,z5,z6])],[(0,[z1,z917,z2,z4,z5,z6]),(0,[z1,z2,z99,z4,z139,z12]),(0,[z1,z2,z4,z74,z12,z6]),(0,[z1,z2,z3,z4,z74,z454])],[(0,[z1,z2,z918,z4,z5,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z288,z5,z6]),(0,[z1,z2,z3,z278,z150,z6])],[(0,[z1,z2,z920,z4,z5,z6]),(0,[z340,z1,z29,z2,z4,z5]),(0,[z1,z2,z4,z74,z49,z250])],[(0,[z2,z3,z745,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z284,z5,z6]),(0,[z1,z2,z3,z921,z5,z6]),(0,[z1,z2,z535,z4,z12,z6]),(0,[z1,z2,z3,z5,z497,z108]),(0,[z1,z2,z3,z4,z765,z5])],[(0,[z2,z887,z3,z4,z5,z6]),(0,[z1,z922,z2,z3,z5,z6]),(0,[z1,z2,z4,z453,z12,z6]),(0,[z1,z2,z362,z4,z12,z6]),(0,[z1,z2,z4,z516,z12,z6]),(0,[z1,z2,z4,z5,z923,z6])],[(0,[z1,z2,z15,z4,z649,z6]),(0,[z1,z2,z924,z4,z5,z6]),(0,[z1,z2,z925,z4,z5,z6]),(0,[z337,z1,z2,z311,z5,z6])],[(0,[z70,z137,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z926,z6]),(0,[z105,z2,z3,z4,z5,z126]),(0,[z298,z2,z4,z5,z565,z6]),(0,[z1,z352,z4,z5,z307,z6])],[(0,[z1,z2,z3,z4,z136,z6]),(0,[z1,z2,z4,z536,z12,z6]),(0,[z1,z2,z638,z4,z12,z6]),(0,[z1,z2,z15,z4,z5,z866])],[(0,[z105,z2,z3,z4,z5,z40]),(0,[z1,z25,z4,z307,z12,z6]),(0,[z1,z2,z122,z235,z136,z6]),(0,[z1,z2,z3,z5,z157,z6])],[(0,[z1,z2,z927,z3,z4,z6]),(0,[z1,z2,z4,z215,z772,z6]),(0,[z463,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z683,z12,z6]),(0,[z196,z2,z3,z146,z5,z41]),(0,[z24,z1,z106,z4,z46,z6]),(0,[z1,z2,z4,z12,z60,z6]),(0,[z1,z2,z59,z207,z60,z6])],[(0,[z109,z2,z15,z215,z5,z6]),(0,[z75,z2,z3,z4,z259,z6]),(0,[z1,z2,z3,z4,z928,z6]),(0,[z340,z1,z2,z99,z3,z4])]],
   [[(0,[z1,z619,z2,z4,z12,z6]),(0,[z1,z2,z3,z929,z5,z6]),(0,[z1,z2,z3,z4,z5,z930]),(0,[z1,z2,z4,z5,z931,z6]),(0,[z1,z2,z3,z4,z370,z6]),(0,[z1,z555,z2,z4,z136,z6]),(0,[z1,z2,z207,z4,z150,z6])],[(0,[z1,z2,z308,z4,z12,z6])],[(0,[z196,z2,z3,z4,z5,z742]),(0,[z1,z2,z461,z4,z12,z6]),(0,[z1,z2,z167,z4,z12,z6]),(0,[z1,z161,z72,z2,z5,z6]),(0,[z1,z2,z15,z4,z277,z5]),(0,[z1,z2,z207,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z932,z1,z2,z3,z4,z5]),(0,[z1,z2,z933,z4,z5,z6]),(0,[z1,z3,z4,z730,z46,z6]),(0,[z1,z270,z15,z4,z5,z313]),(0,[z1,z2,z311,z235,z5,z6]),(0,[z1,z2,z707,z4,z5,z6])],[(0,[z1,z2,z3,z934,z5,z6]),(0,[z1,z2,z4,z681,z12,z6]),(0,[z24,z1,z3,z4,z730,z6]),(0,[z1,z2,z935,z5,z12,z6])],[(0,[z1,z2,z4,z548,z12,z6]),(0,[z298,z2,z3,z4,z259,z6]),(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z706,z2,z4,z12,z6]),(0,[z1,z2,z3,z107,z5,z108])],[(0,[z1,z2,z15,z146,z5,z6]),(0,[z1,z2,z4,z551,z12,z6]),(0,[z1,z82,z2,z4,z543,z6]),(0,[z1,z2,z3,z5,z937,z6]),(0,[z1,z2,z4,z247,z12,z6]),(0,[z1,z2,z731,z5,z12,z6])],[(0,[z1,z2,z938,z4,z5,z6]),(0,[z1,z939,z2,z4,z5,z6]),(0,[z1,z2,z15,z4,z32,z5]),(0,[z1,z2,z847,z3,z5,z417]),(0,[z1,z2,z5,z12,z361,z6])]],
   [[(0,[z190,z1,z200,z2,z4,z5]),(0,[z1,z2,z3,z4,z124,z6]),(0,[z105,z389,z2,z3,z4,z5]),(0,[z1,z2,z283,z4,z5,z6]),(0,[z1,z2,z17,z4,z12,z6])],[(0,[z1,z2,z940,z4,z5,z6]),(0,[z1,z2,z4,z417,z12,z6]),(0,[z39,z2,z15,z4,z11,z6]),(0,[z1,z2,z4,z370,z12,z6])],[(0,[z100,z68,z184,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z3,z4,z5,z730,z6]),(0,[z1,z383,z2,z5,z12,z6]),(0,[z1,z2,z3,z942,z5,z6]),(0,[z1,z2,z225,z4,z504,z5]),(0,[z1,z2,z341,z3,z74,z250])],[(0,[z1,z943,z3,z4,z5,z6]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z2,z4,z235,z136,z6]),(0,[z1,z161,z2,z35,z5,z6])],[(0,[z1,z945,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z946])],[(0,[z1,z2,z724,z4,z5,z6]),(0,[z2,z3,z4,z762,z259,z6]),(0,[z1,z2,z947,z3,z5,z6]),(0,[z24,z1,z2,z288,z12,z6]),(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z2,z315,z5,z361,z6])],[(0,[z1,z2,z3,z4,z949,z6]),(0,[z1,z25,z3,z4,z730,z6]),(0,[z1,z2,z3,z4,z5,z950])],[(0,[z1,z2,z3,z4,z5,z951]),(0,[z63,z1,z200,z2,z4,z6]),(0,[z190,z1,z2,z4,z5,z12]),(0,[z14,z2,z71,z4,z5,z6]),(0,[z1,z2,z3,z31,z5,z538]),(1,[z1,z2,z4,z417,z12]),(0,[z1,z2,z4,z179,z12,z6]),(0,[z1,z2,z3,z5,z361,z250])]],
   [[(0,[z1,z2,z3,z952,z5,z6]),(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z2,z3,z5,z60,z254])],[(0,[z1,z610,z2,z4,z543,z6]),(0,[z1,z2,z716,z3,z5,z6]),(0,[z1,z2,z224,z4,z848,z6])],[(0,[z1,z2,z3,z4,z954,z6]),(0,[z1,z2,z947,z5,z12,z6]),(0,[z1,z2,z3,z4,z782,z6])],[(0,[z1,z2,z3,z5,z955,z6]),(0,[z1,z2,z4,z5,z269,z6]),(0,[z1,z20,z21,z4,z543,z6]),(0,[z24,z1,z3,z4,z46,z6]),(0,[z1,z2,z407,z4,z12,z6]),(0,[z131,z1,z2,z99,z4,z12]),(0,[z138,z1,z2,z3,z5,z189])],[(0,[z1,z2,z3,z4,z155,z417]),(0,[z1,z2,z956,z4,z5,z6]),(0,[z1,z2,z3,z4,z957,z6]),(1,[z1,z2,z4,z848,z6])],[(0,[z100,z184,z3,z284,z5,z6]),(0,[z1,z2,z311,z259,z12,z6]),(0,[z1,z2,z3,z531,z5,z108]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z959,z2,z3,z4,z5,z6]),(0,[z1,z2,z15,z4,z525,z6]),(0,[z1,z2,z4,z755,z5,z6])],[(0,[z100,z335,z184,z4,z5,z6]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z1,z20,z2,z4,z543,z6]),(0,[z1,z2,z15,z4,z5,z471]),(0,[z1,z2,z4,z43,z92,z6])],[(0,[z1,z385,z2,z5,z12,z6]),(0,[z1,z2,z3,z5,z961,z6]),(0,[z196,z2,z3,z372,z5,z41]),(0,[z1,z962,z2,z3,z5,z6]),(0,[z1,z25,z2,z288,z12,z6]),(0,[z1,z2,z311,z136,z12,z6])]],
   [[(0,[z1,z2,z284,z5,z12,z6]),(0,[z1,z200,z2,z88,z4,z5]),(0,[z1,z25,z3,z4,z307,z6])],[(0,[z1,z2,z88,z15,z4,z5]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z192,z2,z3,z5,z538]),(0,[z1,z2,z4,z592,z12,z6]),(0,[z1,z2,z5,z12,z157,z6]),(0,[z1,z2,z4,z43,z755,z5]),(0,[z42,z1,z2,z55,z43,z5])],[(0,[z1,z2,z3,z4,z5,z964]),(0,[z1,z2,z324,z4,z12,z6]),(0,[z1,z2,z4,z5,z965,z6])],[(0,[z70,z1,z2,z4,z136,z6]),(0,[z109,z2,z3,z215,z5,z6]),(0,[z1,z2,z3,z4,z966,z6]),(0,[z196,z2,z3,z4,z5,z289]),(0,[z24,z1,z2,z4,z12,z6])],[],[(0,[z1,z385,z2,z88,z3,z5]),(0,[z1,z3,z4,z5,z832,z313]),(0,[z1,z2,z436,z4,z12,z6]),(0,[z1,z784,z4,z5,z12,z6]),(0,[z1,z2,z17,z4,z155,z6])],[(0,[z1,z2,z15,z4,z5,z967])],[(0,[z1,z2,z15,z372,z5,z6]),(0,[z1,z270,z3,z4,z5,z313]),(0,[z1,z2,z122,z235,z277,z5])]],
   [[(0,[z100,z184,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z968,z5])],[(0,[z463,z1,z2,z4,z5,z12]),(0,[z1,z969,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z970,z6]),(0,[z1,z2,z971,z4,z5,z6]),(0,[z1,z2,z3,z146,z5,z6]),(0,[z1,z2,z4,z613,z12,z6]),(0,[z1,z3,z4,z5,z832,z6]),(0,[z1,z2,z4,z703,z12,z6]),(0,[z972,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z973,z6]),(0,[z1,z2,z3,z4,z974,z5]),(0,[z1,z2,z3,z4,z32,z5]),(0,[z1,z2,z4,z12,z329,z6]),(0,[z1,z975,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z976,z6]),(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z20,z21,z4,z437,z6]),(0,[z1,z192,z154,z3,z521,z5]),(0,[z1,z2,z341,z5,z12,z6])],[(0,[z887,z184,z3,z4,z5,z6]),(0,[z1,z2,z3,z665,z5,z108]),(0,[z1,z2,z4,z259,z12,z6]),(0,[z1,z2,z4,z618,z12,z6]),(0,[z1,z2,z30,z4,z12,z6])],[(0,[z1,z2,z3,z4,z5,z870]),(0,[z1,z2,z3,z4,z978,z6]),(0,[z1,z2,z4,z83,z12,z6]),(0,[z39,z2,z3,z4,z11,z6]),(0,[z1,z511,z2,z4,z12,z6]),(0,[z1,z25,z2,z4,z12,z6]),(0,[z1,z2,z315,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z979])],[(0,[z1,z738,z3,z4,z5,z6]),(0,[z1,z2,z980,z4,z5,z6]),(0,[z1,z2,z4,z136,z12,z6]),(0,[z1,z479,z2,z4,z12,z6]),(0,[z1,z2,z3,z12,z361,z6])],[(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z25,z433,z3,z4,z6]),(0,[z1,z2,z694,z4,z12,z6]),(0,[z1,z2,z983,z4,z5,z6]),(0,[z1,z2,z3,z4,z984,z5])]],
   [[(0,[z1,z985,z2,z3,z5,z6]),(0,[z109,z2,z460,z215,z5,z6]),(0,[z1,z2,z15,z4,z5,z160]),(0,[z105,z1,z2,z3,z5,z361]),(0,[z1,z2,z407,z4,z155,z6]),(1,[z1,z2,z716,z5,z6]),(0,[z1,z2,z311,z815,z5,z12])],[(0,[z1,z2,z3,z4,z5,z986]),(1,[z2,z3,z4,z762,z6]),(0,[z1,z2,z940,z4,z11,z6]),(0,[z1,z2,z98,z3,z5,z254])],[(0,[z1,z2,z15,z4,z5,z6]),(0,[z100,z279,z184,z3,z4,z6]),(0,[z1,z887,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z202,z3,z737,z5,z6]),(0,[z1,z2,z3,z988,z5,z6])],[(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z3,z780,z5,z6]),(0,[z51,z2,z31,z5,z12,z6]),(0,[z1,z2,z3,z4,z74,z693]),(0,[z1,z2,z4,z521,z5,z12]),(0,[z1,z2,z3,z4,z136,z471])],[(0,[z1,z2,z3,z284,z990,z5]),(0,[z1,z2,z4,z5,z27,z6]),(0,[z1,z2,z15,z107,z5,z108]),(0,[z1,z2,z3,z991,z5,z6])],[(0,[z1,z992,z3,z4,z5,z6]),(0,[z1,z20,z4,z5,z307,z6]),(0,[z1,z2,z15,z98,z150,z6])],[(0,[z1,z2,z3,z4,z993,z6]),(0,[z1,z385,z200,z2,z5,z6]),(0,[z1,z2,z3,z994,z5,z6]),(0,[z1,z2,z3,z4,z995,z6]),(0,[z1,z2,z15,z4,z371,z6]),(0,[z1,z2,z372,z5,z12,z6]),(0,[z1,z2,z224,z288,z12,z6]),(0,[z1,z2,z74,z12,z361,z6])],[(0,[z190,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z996]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z1,z2,z3,z4,z370,z471]),(0,[z1,z2,z59,z12,z60,z6]),(0,[z1,z2,z4,z5,z998,z6])]],
   [[(0,[z1,z2,z34,z4,z12,z6]),(0,[z1,z2,z3,z452,z5,z108])],[(0,[z24,z1,z2,z591,z4,z6]),(0,[z1,z2,z5,z49,z361,z6])],[(0,[z1,z3,z4,z5,z999,z6]),(0,[z196,z2,z181,z3,z4,z5]),(0,[z2,z3,z4,z5,z40,z742]),(0,[z1,z2,z4,z841,z12,z6]),(0,[z1,z2,z3,z4,z5,z471])],[(0,[z1,z2,z3,z4,z1000,z6]),(0,[z1,z2,z1001,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z2,z1003,z4,z5,z6]),(0,[z1,z2,z122,z235,z5,z471]),(0,[z340,z1,z2,z99,z4,z12])],[(0,[z1,z200,z2,z279,z4,z6]),(0,[z1,z82,z2,z4,z83,z6]),(0,[z138,z1,z2,z3,z136,z6])],[(0,[z1,z72,z2,z596,z5,z6]),(0,[z1,z2,z3,z4,z1004,z5]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z1005,z2,z4,z5,z6]),(0,[z1,z2,z3,z150,z662,z6]),(0,[z1,z2,z99,z311,z12,z6])],[(0,[z1,z2,z101,z5,z12,z6]),(0,[z63,z1,z2,z3,z4,z6]),(0,[z190,z1,z68,z2,z3,z5]),(0,[z1,z1006,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z1007,z5]),(0,[z1,z2,z1008,z4,z5,z6]),(0,[z1,z2,z150,z288,z12,z6])],[(0,[z1,z1009,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z1011,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1012,z6]),(0,[z81,z2,z436,z4,z5,z6]),(0,[z1,z2,z3,z4,z1013,z6])],[(0,[z1,z385,z2,z279,z3,z6]),(0,[z1,z2,z3,z911,z5,z6]),(0,[z1,z2,z460,z4,z772,z6]),(0,[z1,z2,z1014,z4,z5,z6]),(0,[z1,z2,z1015,z4,z5,z6]),(0,[z2,z4,z11,z259,z12,z6]),(0,[z1,z270,z2,z3,z146,z5]),(0,[z1,z2,z640,z4,z12,z6]),(0,[z1,z2,z15,z4,z848,z6])],[(0,[z1,z2,z3,z1016,z5,z6]),(0,[z1,z2,z3,z4,z5,z967]),(0,[z1,z1017,z3,z4,z5,z6]),(0,[z24,z1,z15,z4,z46,z6]),(0,[z1,z2,z1018,z4,z5,z6]),(0,[z1,z2,z99,z288,z12,z6]),(0,[z1,z2,z4,z5,z1019,z6])],[(0,[z1,z2,z3,z372,z5,z6]),(0,[z1,z191,z2,z4,z12,z6]),(0,[z1,z2,z3,z1020,z5,z6])],[(0,[z1,z2,z3,z719,z5,z6]),(0,[z1,z2,z1021,z4,z5,z6]),(0,[z196,z2,z3,z4,z698,z5]),(0,[z1,z2,z224,z4,z12,z6]),(0,[z1,z2,z1022,z4,z5,z6])],[(0,[z1,z2,z3,z1023,z5,z6]),(0,[z63,z1,z68,z2,z3,z6]),(0,[z1,z2,z122,z4,z83,z6]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z1,z182,z2,z4,z12,z6])],[(0,[z1,z2,z4,z672,z12,z6]),(0,[z1,z2,z1025,z4,z5,z6]),(0,[z1,z2,z122,z413,z5,z6]),(0,[z1,z2,z459,z4,z83,z6]),(0,[z1,z2,z38,z4,z12,z6]),(0,[z1,z2,z4,z674,z12,z6]),(0,[z1,z2,z4,z217,z12,z6])],[(0,[z1,z2,z3,z4,z5,z1026]),(0,[z1,z2,z1027,z4,z5,z6]),(0,[z1,z2,z1028,z4,z5,z6])]],
   [[],[(0,[z1,z2,z3,z4,z1029,z5]),(0,[z1,z2,z3,z4,z5,z979]),(0,[z1,z2,z3,z4,z1030,z6]),(0,[z1,z192,z3,z5,z667,z6]),(0,[z1,z2,z484,z4,z12,z6]),(0,[z1,z2,z36,z4,z5,z28]),(0,[z1,z2,z1031,z4,z5,z6])],[(0,[z1,z2,z459,z4,z12,z6]),(0,[z1,z2,z4,z5,z417,z12]),(0,[z1032,z1,z2,z4,z5,z6]),(0,[z1,z2,z397,z4,z12,z6]),(0,[z1,z2,z935,z3,z5,z6])],[(0,[z51,z142,z2,z3,z5,z6]),(0,[z1,z610,z2,z4,z12,z6]),(0,[z1,z2,z3,z1033,z5,z6]),(0,[z1,z2,z15,z4,z5,z538])],[(0,[z1,z20,z2,z4,z83,z6]),(0,[z81,z2,z114,z4,z83,z6]),(0,[z81,z419,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z160]),(0,[z109,z2,z215,z5,z12,z6]),(0,[z1,z2,z1034,z4,z5,z6]),(0,[z1,z2,z122,z235,z370,z6]),(0,[z1,z2,z99,z4,z74,z12]),(0,[z1,z2,z4,z92,z12,z6]),(0,[z1,z2,z341,z5,z49,z6])],[(0,[z1,z2,z745,z4,z5,z6]),(0,[z1,z2,z4,z5,z1035,z6]),(0,[z1,z2,z1036,z4,z5,z6]),(0,[z1,z2,z34,z4,z155,z6]),(0,[z1,z2,z1037,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1038]),(0,[z1,z2,z829,z4,z150,z6])],[(0,[z1,z2,z4,z1039,z5,z6]),(0,[z1,z2,z1040,z4,z5,z6]),(0,[z1,z2,z4,z5,z1041,z6]),(0,[z1,z2,z99,z4,z451,z12]),(0,[z1,z2,z36,z4,z5,z428]),(0,[z1,z2,z3,z782,z60,z6])],[(0,[z100,z184,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z1042,z5]),(0,[z1,z2,z3,z4,z1043,z6]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z51,z2,z3,z31,z5,z6]),(0,[z1,z25,z4,z26,z27,z6]),(0,[z1,z2,z122,z235,z5,z6]),(0,[z1,z2,z829,z4,z5,z6])]],
   [[(0,[z1,z2,z1045,z3,z4,z6]),(0,[z1,z2,z1046,z4,z5,z6]),(0,[z1,z383,z2,z3,z5,z6]),(0,[z1,z2,z4,z848,z12,z6]),(0,[z1,z2,z99,z4,z12,z6]),(0,[z1,z2,z1047,z4,z5,z6])],[(0,[z2,z4,z259,z444,z12,z6]),(0,[z1,z2,z3,z4,z5,z768]),(0,[z138,z1,z2,z15,z139,z5])],[(0,[z1,z200,z2,z4,z5,z6]),(0,[z1,z2,z1048,z4,z5,z6]),(0,[z105,z2,z3,z4,z5,z742]),(0,[z123,z1,z2,z4,z5,z323])],[(0,[z1,z2,z3,z4,z5,z809]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z122,z249,z5,z6]),(0,[z1,z2,z4,z702,z12,z6]),(0,[z1,z2,z4,z5,z12,z254])],[(0,[z2,z3,z4,z5,z742,z6])],[(0,[z369,z2,z3,z215,z5,z6]),(0,[z39,z2,z4,z11,z12,z6]),(0,[z1050,z2,z3,z4,z5,z6])],[(0,[z1,z2,z279,z15,z4,z6]),(0,[z196,z2,z4,z5,z12,z41]),(0,[z1,z2,z4,z16,z12,z6]),(0,[z1,z2,z3,z74,z361,z250])],[(0,[z1,z2,z3,z4,z1051,z6]),(0,[z1,z2,z3,z4,z1052,z5])]],
   [[(0,[z1,z2,z460,z5,z6,z108]),(0,[z1,z2,z3,z4,z417,z12]),(0,[z1,z1053,z2,z3,z5,z6]),(0,[z1054,z2,z3,z4,z5,z6]),(0,[z1,z214,z2,z4,z12,z6]),(0,[z1,z2,z3,z4,z1055,z6])],[(0,[z39,z2,z640,z3,z4,z6]),(0,[z589,z2,z3,z4,z11,z6]),(0,[z1,z2,z15,z311,z12,z6]),(0,[z1,z182,z129,z4,z5,z6])],[(0,[z1,z2,z1056,z3,z5,z6]),(0,[z1,z1057,z2,z3,z4,z5]),(0,[z1,z2,z1058,z3,z5,z6]),(0,[z1,z2,z99,z505,z3,z4])],[(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1,z2,z460,z4,z5,z6]),(0,[z1,z2,z4,z151,z12,z6])],[(0,[z1,z68,z2,z5,z12,z6]),(0,[z295,z1,z2,z4,z12,z6]),(0,[z1,z2,z55,z3,z5,z108])],[(0,[z1,z385,z2,z3,z5,z6]),(0,[z63,z190,z1,z2,z3,z4]),(0,[z1,z2,z1060,z4,z5,z6]),(0,[z75,z2,z591,z4,z259,z6]),(0,[z1,z1061,z3,z4,z5,z6]),(0,[z171,z1,z2,z4,z12,z6]),(0,[z1,z2,z4,z5,z1062,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z830,z2,z3,z4,z5,z6]),(0,[z1,z2,z315,z341,z5,z6])],[(0,[z1,z192,z15,z154,z5,z6]),(0,[z138,z1,z2,z3,z277,z5])],[(0,[z1,z2,z88,z279,z3,z4]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z1,z2,z311,z3,z136,z6]),(0,[z1,z177,z2,z4,z12,z6])]],
   [[(0,[z1,z2,z3,z1064,z5,z6]),(0,[z1,z2,z3,z5,z1065,z6]),(0,[z1,z2,z3,z4,z1066,z5])],[(0,[z1,z2,z3,z4,z1067,z6]),(0,[z625,z1,z2,z4,z12,z6]),(0,[z1,z2,z591,z4,z5,z6]),(0,[z1,z2,z3,z4,z1068,z6]),(0,[z105,z432,z2,z3,z4,z5]),(0,[z1,z2,z1016,z5,z12,z6])],[(0,[z1,z68,z2,z88,z3,z5]),(0,[z1,z2,z279,z4,z12,z6]),(0,[z1,z1069,z2,z3,z5,z6]),(0,[z1,z2,z1070,z4,z5,z6]),(0,[z1,z2,z3,z4,z1071,z6]),(0,[z1,z2,z15,z341,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1072]),(0,[z1,z2,z3,z1073,z5,z6]),(0,[z1,z2,z3,z372,z32,z5]),(0,[z138,z1,z2,z3,z32,z5]),(0,[z1,z202,z2,z3,z5,z538]),(0,[z1,z161,z2,z634,z5,z6]),(0,[z1,z72,z2,z288,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1074]),(0,[z19,z1,z2,z4,z12,z6]),(0,[z1,z2,z15,z4,z488,z6])],[],[(0,[z1,z2,z1075,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z2,z3,z4,z5,z1077]),(0,[z1,z2,z15,z4,z521,z5])],[(0,[z1,z2,z1078,z4,z5,z6]),(0,[z2,z3,z4,z5,z744,z6]),(0,[z1,z2,z3,z4,z5,z538]),(0,[z910,z2,z4,z5,z12,z6]),(0,[z1,z2,z98,z3,z782,z6])]],
   [[(0,[z1,z2,z4,z94,z12,z6]),(0,[z1,z161,z2,z5,z56,z6])],[(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z2,z3,z4,z1080,z6]),(0,[z1,z2,z15,z4,z342,z6]),(0,[z1,z3,z761,z4,z5,z6]),(0,[z1,z2,z3,z5,z577,z108]),(0,[z1,z25,z176,z4,z26,z6]),(0,[z1,z270,z2,z3,z5,z143]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z2,z341,z3,z5,z6])],[(0,[z1,z2,z3,z1081,z5,z6]),(0,[z1,z2,z1082,z4,z5,z6]),(0,[z75,z2,z3,z4,z762,z6]),(0,[z1,z2,z341,z74,z12,z6]),(0,[z1,z2,z3,z4,z815,z5])],[(0,[z1,z2,z3,z4,z5,z1083]),(0,[z1,z2,z4,z5,z841,z6]),(0,[z1,z2,z311,z5,z12,z6])],[(0,[z63,z1,z2,z1075,z4,z6]),(0,[z2,z745,z114,z4,z5,z6]),(0,[z70,z133,z2,z4,z5,z6]),(0,[z1,z2,z4,z119,z12,z6]),(0,[z1,z2,z98,z3,z251,z6])],[(0,[z1,z4,z5,z999,z12,z6]),(0,[z1,z2,z3,z858,z5,z6])],[(0,[z1,z2,z1084,z4,z5,z6]),(0,[z1,z2,z1085,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z417]),(0,[z1,z2,z1086,z4,z5,z6]),(0,[z1,z2,z4,z125,z12,z6]),(0,[z1,z2,z311,z5,z12,z768])],[(1,[z2,z3,z719,z5,z6]),(0,[z51,z2,z3,z31,z32,z5]),(0,[z1,z2,z212,z4,z12,z6]),(0,[z1,z2,z3,z150,z136,z6])]],
   [[(0,[z2,z71,z745,z4,z5,z6]),(0,[z1,z2,z1087,z4,z5,z6]),(0,[z1,z2,z4,z12,z497,z6]),(0,[z1,z2,z609,z4,z5,z428])],[(0,[z1,z2,z3,z739,z5,z6]),(0,[z1,z2,z4,z1088,z5,z6]),(0,[z1,z161,z2,z311,z5,z6]),(0,[z340,z1,z2,z4,z43,z5]),(0,[z1,z2,z1089,z4,z5,z6]),(0,[z1,z2,z1090,z4,z5,z6])],[(0,[z1,z2,z1091,z3,z4,z6]),(0,[z632,z2,z3,z31,z5,z6]),(0,[z1,z2,z3,z1092,z5,z6]),(0,[z1,z2,z4,z5,z1093,z6]),(0,[z1,z2,z207,z4,z504,z5])],[(0,[z1,z68,z200,z2,z5,z6]),(0,[z1,z2,z460,z4,z966,z6]),(0,[z1,z2,z3,z372,z139,z5]),(0,[z1,z2,z3,z4,z1094,z6]),(0,[z1,z2,z3,z4,z1095,z6]),(1,[z1,z3,z4,z730,z6]),(0,[z1,z2,z3,z277,z5,z108])],[(0,[z1,z335,z2,z88,z4,z5]),(0,[z79,z1,z418,z3,z4,z5]),(0,[z105,z2,z4,z5,z12,z40])],[(0,[z100,z88,z184,z3,z4,z5]),(0,[z63,z1,z2,z88,z3,z4])],[(0,[z1,z2,z3,z4,z5,z1096]),(0,[z51,z2,z15,z31,z5,z6]),(0,[z131,z1,z2,z3,z4,z179]),(0,[z1,z2,z586,z4,z12,z6]),(0,[z1,z192,z154,z5,z12,z6]),(0,[z42,z1,z2,z4,z5,z323])],[(0,[z190,z1,z385,z2,z3,z5]),(0,[z1,z2,z4,z1097,z5,z6]),(0,[z1,z2,z311,z3,z60,z6]),(0,[z1,z2,z3,z857,z5,z6])]],
   [[(1,[z2,z745,z4,z5,z6]),(0,[z1,z2,z3,z4,z1098,z6]),(0,[z1,z2,z3,z1099,z5,z6]),(0,[z1,z2,z3,z4,z5,z741])],[(0,[z1,z1100,z2,z4,z5,z6]),(0,[z1,z2,z1101,z4,z5,z6]),(0,[z1,z2,z288,z5,z12,z6])],[(0,[z1,z2,z4,z5,z12,z6]),(0,[z1,z2,z1102,z4,z5,z6]),(0,[z1,z2,z1103,z4,z5,z6]),(0,[z1,z2,z12,z60,z6,z108]),(0,[z1,z2,z311,z288,z5,z6]),(0,[z1,z208,z2,z4,z12,z6]),(0,[z1,z2,z288,z5,z56,z6])],[(0,[z1,z2,z15,z101,z5,z6]),(0,[z1,z2,z3,z1104,z5,z6]),(0,[z109,z205,z2,z215,z5,z6]),(0,[z1,z2,z716,z235,z5,z6]),(0,[z1,z253,z2,z288,z5,z6]),(0,[z1,z2,z457,z4,z12,z6]),(0,[z1,z2,z3,z5,z1105,z6]),(0,[z138,z1,z2,z3,z765,z5])],[(0,[z1,z2,z3,z1106,z5,z6]),(0,[z1,z2,z4,z5,z1107,z6]),(0,[z1,z2,z514,z3,z5,z108]),(0,[z1,z2,z3,z765,z5,z108])],[(0,[z1,z2,z34,z4,z124,z6]),(0,[z138,z1,z2,z460,z5,z6]),(0,[z1,z2,z15,z4,z543,z6]),(0,[z1,z2,z3,z4,z1108,z6]),(0,[z1,z2,z3,z1109,z5,z6]),(0,[z1,z161,z2,z4,z136,z6]),(0,[z1,z2,z59,z3,z504,z60])],[(0,[z1,z68,z2,z279,z3,z6]),(0,[z63,z1,z385,z2,z3,z6]),(0,[z75,z2,z78,z4,z259,z6]),(0,[z463,z1,z2,z4,z259,z12]),(0,[z1,z161,z2,z3,z5,z254])],[(0,[z1,z3,z4,z5,z1110,z6]),(0,[z1,z2,z99,z204,z4,z6])]],
   [[(0,[z1,z82,z384,z4,z5,z6]),(0,[z1,z202,z15,z147,z5,z6]),(0,[z1,z2,z4,z1111,z5,z6]),(0,[z1,z2,z3,z782,z5,z6])],[(0,[z1,z2,z1112,z3,z5,z6]),(0,[z1,z2,z4,z755,z5,z28])],[(0,[z1,z2,z3,z4,z990,z5]),(0,[z1,z2,z78,z4,z5,z6]),(0,[z1,z1113,z3,z4,z5,z6]),(0,[z39,z2,z3,z4,z762,z6]),(0,[z1,z20,z761,z4,z5,z6]),(0,[z1,z2,z3,z4,z521,z5]),(0,[z378,z1,z2,z4,z12,z6]),(0,[z1,z2,z4,z815,z5,z12]),(0,[z2,z3,z4,z5,z796,z6]),(0,[z1,z2,z3,z139,z765,z5]),(0,[z1,z2,z709,z3,z4,z6])],[(0,[z1,z2,z3,z1114,z5,z6]),(0,[z1,z2,z1115,z4,z5,z6]),(0,[z1,z2,z3,z4,z1116,z6]),(0,[z1117,z2,z3,z4,z5,z6]),(0,[z1,z2,z122,z3,z5,z254]),(0,[z1,z233,z2,z4,z12,z6]),(0,[z1,z2,z225,z4,z5,z254])],[(0,[z1,z2,z3,z4,z83,z6]),(0,[z1,z2,z1118,z3,z5,z6]),(0,[z1,z2,z806,z5,z12,z6]),(0,[z1,z2,z609,z4,z12,z6]),(0,[z1,z2,z55,z5,z12,z6]),(0,[z14,z2,z459,z4,z5,z6])],[(0,[z1,z2,z3,z1119,z5,z6]),(0,[z1,z2,z1120,z4,z5,z6]),(0,[z560,z1,z2,z4,z12,z6]),(0,[z1,z2,z3,z150,z782,z6])],[(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z25,z2,z591,z4,z6]),(0,[z1,z2,z761,z4,z5,z6]),(0,[z1,z2,z3,z4,z370,z277])],[(0,[z1,z192,z515,z3,z5,z6]),(0,[z1,z2,z311,z11,z12,z6])]],
   [[(0,[z1,z2,z3,z1122,z5,z6]),(0,[z1,z2,z3,z4,z5,z1123]),(0,[z24,z1,z25,z4,z12,z6]),(0,[z1,z2,z707,z4,z12,z6]),(1,[z1,z2,z709,z3,z4])],[(0,[z1,z2,z3,z4,z1124,z6]),(0,[z1,z2,z3,z1125,z5,z6]),(0,[z1,z2,z3,z4,z5,z912])],[(0,[z1,z2,z4,z5,z1126,z6]),(0,[z1,z2,z3,z4,z5,z417]),(0,[z1,z2,z1127,z4,z5,z6]),(0,[z1,z2,z1128,z4,z5,z6])],[(0,[z1,z1129,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z1130,z6]),(0,[z1,z610,z384,z4,z5,z6]),(1,[z1,z2,z4,z755,z5])],[(0,[z1,z2,z3,z4,z1131,z6])],[(0,[z1,z2,z3,z4,z5,z1132]),(0,[z775,z1,z2,z3,z4,z5]),(0,[z1,z2,z15,z4,z437,z6]),(0,[z1,z2,z3,z5,z1133,z6]),(0,[z1,z2,z107,z5,z12,z108])],[(0,[z1134,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z12,z559,z6]),(0,[z1,z2,z940,z4,z12,z6]),(0,[z1,z2,z1135,z4,z5,z6]),(0,[z1,z2,z1136,z3,z5,z6]),(0,[z1,z2,z3,z155,z361,z6]),(0,[z131,z1,z2,z99,z283,z4])],[(0,[z190,z1,z2,z15,z4,z5]),(0,[z1,z2,z4,z103,z12,z6]),(0,[z1,z2,z3,z188,z5,z108])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 527).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1048).take 164) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1212)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [527, 521, 164] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 100).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 205).take 51).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [100, 105, 51] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_45780

theorem PEqualNP.Outside.L_meta_45780 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4007692416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4007692416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45780.solve