import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45710

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
  Nat.testBit (4008241832 * 2 ^ 32 + 4008231040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x20428566cc30de18#64 ++ 0x040850acd9861bc3#64 ++ 0xe8c78fffdc71fe3b#64 ++ 0x7d18f1fffb8e3fc7#64 : BitVec 256),
   (0x0319331145862ae8#64 ++ 0x2063266228b0c55d#64 ++ 0xf739f311e78e3fff#64 ++ 0xfee73e623cf1c7ff#64 : BitVec 256),
   (0x582c5c1a380b4570#64 ++ 0x8b058b83470168ae#64 ++ 0xf83e7c1e380fc7ff#64 ++ 0xbf07cf83c701f8ff#64 : BitVec 256),
   (0x1d806fa03ed00780#64 ++ 0x43b00df407da00f0#64 ++ 0x5fc07fe03ff007c5#64 ++ 0xebf80ffc07fe00f8#64 : BitVec 256),
   (0x9ef78000336db001#64 ++ 0x13def000066db600#64 ++ 0xbfff80003ffff801#64 ++ 0xf7fff00007ffff00#64 : BitVec 256),
   (0xdffffadd80000002#64 ++ 0x1bffff5bb0000000#64 ++ 0xdfffffffc0000001#64 ++ 0xdbfffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z1 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z2 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z3 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z4 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xbfff80003ffff801 0xf7fff00007ffff00

def z5 : W := mkw 0xc37fb25d80000002 0x186ff64bb0000000 0xd73ff31fc0000001 0xdae7fe63f8000000

def z6 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z7 : W := mkw 0x0319321100000000 0x0063264220000000 0x1738700000000000 0x82e70e0000000000

def z8 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x200000001c71fe3a 0x24000000038e3fc7

def z9 : W := mkw 0x20428046c020d818 0x04085008d8041b03 0xa007801fc001f83a 0x1400f003f8003f07

def z10 : W := mkw 0x61087fffcc104e1a 0x0c210ffff98209c3 0x40007fffc000063a 0x08000ffff80000c7

def z11 : W := mkw 0x0319321100020060 0x006326422000400c 0xf739f311e00e07ff 0xfee73e623c01c0ff

def z12 : W := mkw 0x84c2800002609001 0x10985000004c1200 0x00c0000000700000 0x00180000000e0000

def z13 : W := mkw 0x000005203ffdb781 0x400000a407ffb6f0 0x200000003fffffc4 0x2400000007fffff8

def z14 : W := mkw 0x582c5818300b0160 0x8b058b030601602c 0x10387000200e01c4 0x82070e000401c038

def z15 : W := mkw 0x87d3a2c580000002 0x10fa7458b0000000 0xcfc78fffc0000001 0x59f8f1fff8000000

def z16 : W := mkw 0x9eb50000336db001 0x13d6a000066db600 0x373800003ffff800 0xa6e7000007ffff00

def z17 : W := mkw 0x00000402380b4570 0x80000080470168ae 0xe8060c1e380fc7ff 0x3d00c183c701f8ff

def z18 : W := mkw 0x86d380000364b001 0x10da7000006c9600 0x07c1800007f03800 0x40f8300000fe0700

def z19 : W := mkw 0xdffffaddb36db003 0x1bffff5bb66db600 0xfffffffffffff801 0xffffffffffffff00

def z20 : W := mkw 0x9ff7efa03ed00780 0x53fefdf407da00f0 0xdfffffe03ff007c5 0xfbfffffc07fe00f8

def z21 : W := mkw 0x0311230145842a88 0x2062246028b08551 0x07018301c7803800 0x40e0306038f00700

def z22 : W := mkw 0x86d380000364b001 0x10da7000006c9600 0xb7f9800027fe3801 0xf6ff300004ffc700

def z23 : W := mkw 0x0211000001042000 0x0042200000208400 0xb7398000278e3801 0xf6e7300004f1c700

def z24 : W := mkw 0x1d806ba036d00380 0x43b00d7406da0070 0x17c073e027f001c4 0xc2f80e7c04fe0038

def z25 : W := mkw 0x41087add80000002 0x08210f5bb0000000 0x40007fffc0000000 0x08000ffff8000000

def z26 : W := mkw 0x9ef7800000000000 0x13def00000000000 0x9fff800000000001 0xd3fff00000000000

def z27 : W := mkw 0x1d806a8000000000 0x03b00d5000000000 0x1700700000000000 0x82e00e0000000000

def z28 : W := mkw 0x0480000002400000 0x0090000000480000 0x07c0000007f00000 0x40f8000000fe0000

def z29 : W := mkw 0xc27f905d80000002 0x184ff20bb0000000 0x803f801fc0000000 0x1007f003f8000000

def z30 : W := mkw 0x21083777cc924ef8 0x242106eef99249df 0x40007fffc00007fe 0x08000ffff80000ff

def z31 : W := mkw 0x200000024020d818 0x0400000048041b03 0x200000000001f83a 0x0400000000003f07

def z32 : W := mkw 0x1800480000000000 0x0300090000000000 0x58007c0000000001 0x8b000f8000000000

def z33 : W := mkw 0x0219101141062868 0x204322022820c50d 0xa0398011c00e383a 0x140730023801c707

def z34 : W := mkw 0x2353a365c5b4ba88 0x246a746cb8b69751 0x07c183e1c7f03800 0x40f8307c38fe0700

def z35 : W := mkw 0x0211000001042000 0x0042200000208400 0x0701800007803800 0x40e0300000f00700

def z36 : W := mkw 0x9fffb31177efbae9 0x33fff6622efdf75d 0xfffff311ffffffff 0xfffffe623fffffff

def z37 : W := mkw 0x7deefffefefbdff8 0xcfbddfffdfdf7bff 0xffffffffffffffff 0xffffffffffffffff

def z38 : W := mkw 0x1cc2800032609000 0x03985000064c1200 0xbfc780003ff1f801 0xf7f8f00007fe3f00

def z39 : W := mkw 0x0042804480000000 0x0008500890000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z40 : W := mkw 0xdffffedfb80b4572 0x9bffffdbf70168ae 0xfffffffff80fc7ff 0xffffffffff01f8ff

def z41 : W := mkw 0x9ef784023b6ff571 0x93def080476dfeae 0xbfff80003fffffff 0xf7fff00007ffffff

def z42 : W := mkw 0x3fdbfff7fff6fff8 0x67fb7ffefffedfff 0xffffffffffffffff 0xffffffffffffffff

def z43 : W := mkw 0x40085c1a08024570 0x88010b83410048ae 0xf0387c1e200e07ff 0xbe070f83c401c0ff

def z44 : W := mkw 0xdffffaddb2699003 0x1bffff5bb64d3200 0xdfffffffd871c001 0xdbfffffffb0e3800

def z45 : W := mkw 0x0580228000000000 0x00b0045000000000 0x07c003e000000000 0x40f8007c00000000

def z46 : W := mkw 0x582c581830090000 0x0b058b0306012000 0xf83e7c1e380fc001 0xbf07cf83c701f800

def z47 : W := mkw 0x9ce6800032699001 0x139cd000064d3200 0x08c600001871c000 0x0118c000030e3800

def z48 : W := mkw 0x0000010045862ae8 0x2000002008b0c55d 0x20000000278e3ffe 0x2400000004f1c7ff

def z49 : W := mkw 0xdce6c8cc80000002 0x1b9cd91990000000 0x08c60cee00000000 0x0118c19dc0000000

def z50 : W := mkw 0x9ff7a3a037fdb281 0x53fef47406ffb650 0xbfff83e03ffff801 0xf7fff07c07ffff00

def z51 : W := mkw 0x1c80488032400100 0x4390091006480020 0x0000000000000000 0x0000000000000000

def z52 : W := mkw 0x1d806fa07ed00f88 0x43b00df40fda01f1 0xffc1fff1fff03fff 0xfff83ffe3ffe07ff

def z53 : W := mkw 0x0108331144820ae8 0x202106622890415d 0x40007311c00007fe 0x08000e62380000ff

def z54 : W := mkw 0xdfbd7a9900000002 0x1bf7af5320000000 0x5ff87fe000000001 0xcbff0ffc00000000

def z55 : W := mkw 0x582c5818300b0160 0x8b058b030601602c 0xb83e7000380fc1c5 0xb707ce000701f838

def z56 : W := mkw 0x20000566cc104e18 0x040000acd98209c3 0x40000fffc000063a 0x080001fff80000c7

def z57 : W := mkw 0x9eb50000334d2001 0x13d6a0000669a400 0x17380000238e0000 0x82e700000471c000

def z58 : W := mkw 0x1824000030090000 0x0304800006012000 0xb83e0000380fc001 0xb707c0000701f800

def z59 : W := mkw 0x225b9057c126f878 0x244b720af824df0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z60 : W := mkw 0x235bb777cdb6fef8 0x246b76eef9b6dfdf 0xffffffffffffffff 0xffffffffffffffff

def z61 : W := mkw 0x40085c1a08024570 0x88010b83410048ae 0x40007c1e000007fe 0x08000f83c00000ff

def z62 : W := mkw 0x402c101a000b4070 0x880582034001680e 0xa03e001e000fc03a 0x1407c003c001f807

def z63 : W := mkw 0x0000000000000000 0x0000000000000000 0xc8060c1e00000001 0x1900c183c0000000

def z64 : W := mkw 0xdeffd818336fb161 0x9bdffb03066df62c 0xbffff0003ffff9c5 0xf7fffe0007ffff38

def z65 : W := mkw 0x586edc1a382bd570 0x8b0ddb8347057aae 0xf8fffc1e3c7fffff 0xff1fff83c78fffff

def z66 : W := mkw 0x5d887fba3ed247f0 0xcbb10ff747da48fe 0x5fc07ffe3ff007ff 0xebf80fffc7fe00ff

def z67 : W := mkw 0x1d80230036c00280 0x03b0046006d80050 0x5fc073003ff007c5 0xebf80e6007fe00f8

def z68 : W := mkw 0x004285648c100600 0x000850ac918200c0 0xc8c78fffdc700601 0x7918f1fffb8e00c0

def z69 : W := mkw 0x200005227c3bdf78 0x840000a44f877bef 0x200000003c7ffffe 0x24000000078fffff

def z70 : W := mkw 0x0000040208004410 0x0000008041000882 0x200000001801c63a 0x24000000030038c7

def z71 : W := mkw 0xffffffffcdb6fefa 0x3ffffffff9b6dfdf 0xffffffffffffffff 0xffffffffffffffff

def z72 : W := mkw 0x18004c0038000500 0x03000980070000a0 0x58007c00380007c5 0xab000f80070000f8

def z73 : W := mkw 0x01006fa00c900780 0x40200df4019200f0 0x40007fe0000007c4 0x08000ffc000000f8

def z74 : W := mkw 0x9ff7ea80336db001 0x13fefd50066db600 0xffffffe03ffff801 0xfffffffc07ffff00

def z75 : W := mkw 0xbef78566ff7dfe19 0x17def0acdfefbfc3 0xffff8ffffffffe3b 0xfffff1ffffffffc7

def z76 : W := mkw 0x1d8023a036d00280 0x43b0047406da0050 0x1fc003e03ff00001 0xe3f8007c07fe0000

def z77 : W := mkw 0x4024000a00094010 0x8804800140012802 0x0006000e0001c000 0x0000c001c0003800

def z78 : W := mkw 0x1f997fb17fd62fe8 0x63f32ff62ffac5fd 0xfff9fff1fffe3fff 0xffff3ffe3fffc7ff

def z79 : W := mkw 0xdffffbddc5862aea 0x3bffff7bb8b0c55d 0xffffffffe78e3fff 0xfffffffffcf1c7ff

def z80 : W := mkw 0x606e905ec02bd878 0x8c0dd20bd8057b0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z81 : W := mkw 0x20000164c4100a08 0x0400002c98820141 0x000003e1c0000000 0x0000007c38000000

def z82 : W := mkw 0x0042800000209000 0x0008500000041200 0xa8c780001c71f801 0x7518f000038e3f00

def z83 : W := mkw 0xdfbd7add80000002 0x1bf7af5bb0000000 0x57387fffc0000000 0x8ae70ffff8000000

def z84 : W := mkw 0xffffffffcc30de1a 0x1ffffffff9861bc3 0xffffffffdc71fe3b 0xfffffffffb8e3fc7

def z85 : W := mkw 0x03193211018620e0 0x206326422030c41c 0xd739f311e38e01c5 0xdae73e623c71c038

def z86 : W := mkw 0x9ef78000334d2001 0x13def0000669a400 0x9fff8000238e0001 0xd3fff0000471c000

def z87 : W := mkw 0x86d3800000000000 0x10da700000000000 0x07c1800000000000 0x40f8300000000000

def z88 : W := mkw 0x2042806480309000 0x0408500c90061200 0x00c000e000700000 0x0018001c000e0000

def z89 : W := mkw 0x58244c0a38094510 0x8b048981470128a2 0x08060c0e1801c000 0x0100c181c3003800

def z90 : W := mkw 0x0319321100000000 0x0063264220000000 0xd739f311c0000001 0xdae73e6238000000

def z91 : W := mkw 0x1c80000032400000 0x0390000006480000 0x1fc000003ff00001 0xe3f8000007fe0000

def z92 : W := mkw 0x82778000012db001 0x104ef0000025b600 0xa03f8000000ff800 0x1407f0000001ff00

def z93 : W := mkw 0xc7dbfadd80000002 0x18fb7f5bb0000000 0x47c1ffffc0000000 0x48f83ffff8000000

def z94 : W := mkw 0x000005200c100600 0x000000a4018200c0 0x48c00fe01c700601 0x691801fc038e00c0

def z95 : W := mkw 0x0100230004800280 0x0020046000900050 0x57007300278007c5 0xeae00e6004f000f8

def z96 : W := mkw 0x1f997a9133c621e0 0x63f32f522678c43c 0x17387000238e01c4 0x82e70e000471c038

def z97 : W := mkw 0x02110000336db001 0x00422000066db600 0xb73980003ffff801 0xf6e7300007ffff00

def z98 : W := mkw 0x9ef78044b36db001 0x13def008966db600 0xffff8ffffffff801 0xfffff1ffffffff00

def z99 : W := mkw 0x5da46faa3ed94790 0xcbb48df547db28f2 0x5fc67fee3ff1c7c5 0xebf8cffdc7fe38f8

def z100 : W := mkw 0x1d806a8032c00180 0x43b00d5006580030 0x17007000238001c4 0x82e00e0004700038

def z101 : W := mkw 0xbef78046f36df819 0x17def008de6dbf03 0xbfff801ffffff83b 0xf7fff003ffffff07

def z102 : W := mkw 0x20428164c4309a08 0x0408502c98861341 0x00c183e1c4703800 0x4018307c388e0700

def z103 : W := mkw 0x786edd7efc3bdf78 0x8f0ddbafdf877bef 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0018311c0000001 0x5800306238000000

def z105 : W := mkw 0x0008101000020060 0x000102020000400c 0xf0387010200e07ff 0xbe070e020401c0ff

def z106 : W := mkw 0x5dac7fba3edb47f0 0xcbb58ff747db68fe 0xfffe7ffe3fffc7ff 0xffffcfffc7fff8ff

def z107 : W := mkw 0x058023a006d00280 0x40b0047400da0050 0x07c003e007f00000 0x40f8007c00fe0000

def z108 : W := mkw 0xdce6ccceb8094512 0x9b9cd999d70128a2 0x08c60cee1801c000 0x0118c19dc3003800

def z109 : W := mkw 0xdeffdc1a3b6ff571 0x9bdffb83476dfeae 0xfffffc1e3fffffff 0xffffff83c7ffffff

def z110 : W := mkw 0x9ff7efa03ffdb781 0x53fefdf407ffb6f0 0xffffffe03fffffc5 0xfffffffc07fffff8

def z111 : W := mkw 0xc37fb35dc5862aea 0x386ff66bb8b0c55d 0xf73ff31fe78e3fff 0xfee7fe63fcf1c7ff

def z112 : W := mkw 0x2142a766ccb0de98 0x042854ecd9961bd3 0xffc7fffffff1ffff 0xfff8fffffffe3fff

def z113 : W := mkw 0x204284668830d410 0x0408508cd1061a82 0xc8c78fffd871c001 0x5918f1fffb0e3800

def z114 : W := mkw 0x00000402380b4570 0x80000080470168ae 0x20000000380fc7fe 0x240000000701f8ff

def z115 : W := mkw 0x5cac5c1a3a4b4570 0x8b958b83474968ae 0xfffe7c1e3fffc7ff 0xffffcf83c7fff8ff

def z116 : W := mkw 0x4008105d80000002 0x0801020bb0000000 0x0000001fc0000000 0x00000003f8000000

def z117 : W := mkw 0x18004d203c100700 0x030009a4078200e0 0x58c07fe03c7007c5 0xeb180ffc078e00f8

def z118 : W := mkw 0x586ed85c80000000 0x0b0ddb0b90000000 0xd8ffffffc0000001 0xdb1ffffff8000000

def z119 : W := mkw 0x0108331144820ae8 0x202106622890415d 0xe001f311c4003fff 0x7c003e62388007ff

def z120 : W := mkw 0x9ef780000364b001 0x13def000006c9600 0x9fff800007f03801 0xd3fff00000fe0700

def z121 : W := mkw 0x87dbb3d5c5862aea 0x30fb767ab8b0c55d 0xf7f9f3f1e78e3fff 0xfeff3e7e3cf1c7ff

def z122 : W := mkw 0x9eb50000334d2001 0x13d6a0000669a400 0x1ff800003ffe0001 0xe3ff000007ffc000

def z123 : W := mkw 0x402c5c1a080b4570 0x88058b83410168ae 0xe03e7c1e000fc7fe 0x1c07cf83c001f8ff

def z124 : W := mkw 0x0219111145862ae8 0x2043222228b0c55d 0xa0398011e78e3ffe 0x340730023cf1c7ff

def z125 : W := mkw 0x0000004480000000 0x0000000890000000 0x40000fffc0000000 0x080001fff8000000

def z126 : W := mkw 0x43197f1b4d866ff8 0xa8632fe369b0cdff 0xf739ff1fe78e3fff 0xfee73fe3fcf1c7ff

def z127 : W := mkw 0x0319321101042000 0x0063264220208400 0xf739f311e78e3801 0xfee73e623cf1c700

def z128 : W := mkw 0xdce6c8cc80000002 0x1b9cd91990000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z129 : W := mkw 0x592c7add80000002 0x0b258f5bb0000000 0xd83e7fffc0000001 0x9b07cffff8000000

def z130 : W := mkw 0x582c581800000000 0x0b058b0300000000 0xd83e7c1e00000001 0x9b07cf83c0000000

def z131 : W := mkw 0x87d3a2c580000002 0x10fa7458b0000000 0x07c183e1c0000000 0x40f8307c38000000

def z132 : W := mkw 0xdffffefdba500502 0x5bffffdfb74a00a0 0xdfffffffd8700001 0xdbfffffffb0e0000

def z133 : W := mkw 0xdffffadd81042002 0x1bffff5bb0208400 0xffffffffe78e3801 0xfffffffffcf1c700

def z134 : W := mkw 0x200005227ef0df98 0x440000a44fde1bf3 0x200000003ff1fffe 0x2400000007fe3fff

def z135 : W := mkw 0x3dc2efe6fef0df98 0x47b85dfcdfde1bf3 0xffc7fffffff1ffff 0xfff8fffffffe3fff

def z136 : W := mkw 0x03197fb14d962fe8 0x60632ff629b2c5fd 0xf739fff1e78e3fff 0xfee73ffe3cf1c7ff

def z137 : W := mkw 0x1d806a8000000000 0x03b00d5000000000 0x5fc07fe000000001 0xcbf80ffc00000000

def z138 : W := mkw 0x18240000336db001 0x03048000066db600 0xb83e00003ffff801 0xb707c00007ffff00

def z139 : W := mkw 0x9ef785203f7db601 0x13def0a407efb6c0 0xffff8fe03ffffe01 0xfffff1fc07ffffc0

def z140 : W := mkw 0xdffffadd812db003 0x1bffff5bb025b600 0xffffffffc00ff801 0xdffffffff801ff00

def z141 : W := mkw 0xdebd5c1a3b4f6571 0x9bd7ab834769ecae 0xff3e7c1e3b8fc7ff 0xbfe7cf83c771f8ff

def z142 : W := mkw 0xc27f905d812db003 0x184ff20bb025b600 0xa03f801fc00ff800 0x1407f003f801ff00

def z143 : W := mkw 0x0000012004100200 0x0000002400820040 0x00c003e004700000 0x4018007c008e0000

def z144 : W := mkw 0xdffffffd8c900782 0x5bffffffb19200f0 0xdfffffffc00007c5 0xdbfffffff80000f8

def z145 : W := mkw 0xdfbd7a9932c00182 0x5bf7af5326580030 0x17387000238001c4 0x82e70e0004700038

def z146 : W := mkw 0x0000010044000a08 0x0000002008800141 0x40000311c000063a 0x08000062380000c7

def z147 : W := mkw 0xdeff905d80000002 0x1bdff20bb0000000 0x9fff801fc0000001 0xd3fff003f8000000

def z148 : W := mkw 0x0000040208004410 0x0000008041000882 0xe8060c1e1801c63b 0x3d00c183c30038c7

def z149 : W := mkw 0x9fbd331177cf2ae9 0x33f7a6622ef9e55d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z150 : W := mkw 0x00000000336db001 0x00000000066db600 0x200000003ffff800 0x2400000007ffff00

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z152 : W := mkw 0x9fffb21100000000 0x13fff64220000000 0xdffff311c0000001 0xdbfffe6238000000

def z153 : W := mkw 0x5d887ffdbed00782 0x4bb10fffb7da00f0 0x5fc07ffffff007c5 0xebf80ffffffe00f8

def z154 : W := mkw 0x0042804480000000 0x0008500890000000 0x8007801fc0000000 0x1000f003f8000000

def z155 : W := mkw 0xa2778046c12df819 0x144ef008d825bf03 0xa03f801fc00ff83a 0x1407f003f801ff07

def z156 : W := mkw 0x0000010044000a08 0x0000002008800141 0xe0018311c4003e3b 0x7c003062388007c7

def z157 : W := mkw 0x0042804480000000 0x0008500890000000 0x08c60cee00000000 0x0118c19dc0000000

def z158 : W := mkw 0x25c2a3e4c6f09a88 0x44b8547c98de1351 0x07c183e1c7f03800 0x40f8307c38fe0700

def z159 : W := mkw 0x03193211018620e0 0x206326422030c41c 0xf7387010238e07ff 0xbee70e020471c0ff

def z160 : W := mkw 0x4008101a00024070 0x880102034000480e 0x0000001e0000003a 0x00000003c0000007

def z161 : W := mkw 0xda7fdc5fb80b4572 0x9b4ffb8bf70168ae 0xf83ffc1ff80fc7ff 0xbf07ff83ff01f8ff

def z162 : W := mkw 0x03193211418628e8 0x206326422830c51d 0xb739f011e38e39fe 0x96e73e023c71c73f

def z163 : W := mkw 0x5dac7e9a3acb45f0 0xcbb58fd3475968be 0xff3e7c1e3b8fc7ff 0xbfe7cf83c771f8ff

def z164 : W := mkw 0x5cac5cba3a5b4570 0xcb958b97474b68ae 0xf8fe7cfe387fc7ff 0xbf1fcf9fc70ff8ff

def z165 : W := mkw 0x5b3d7f1b7d8f6ff8 0xab67afe36fb1edff 0xff3fff1fff8fffff 0xffe7ffe3fff1ffff

def z166 : W := mkw 0x20428164c4309a08 0x0408502c98861341 0xe0c183f1c4703e3b 0x7c18307e388e07c7

def z167 : W := mkw 0x592c7f1b7c8b4ff8 0xab258fe36f9169ff 0xf83e7f1ff80fc7ff 0xbf07cfe3ff01f8ff

def z168 : W := mkw 0xdffffaddb2c00182 0x5bffff5bb6580030 0xdfffffffe38001c5 0xdbfffffffc700038

def z169 : W := mkw 0x20428164c4309a08 0x0408502c98861341 0xc8c78fffc4703801 0x5918f1fff88e0700

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00000100000063b 0x3c000002000000c7

def z171 : W := mkw 0xdebd5818334f2161 0x9bd7ab030669e42c 0x17387000238e01c4 0x82e70e000471c038

def z172 : W := mkw 0x5dac7fb83ed00780 0x4bb58ff707da00f0 0xdffe7ffe3ff007c5 0xfbffcfffc7fe00f8

def z173 : W := mkw 0x582c5818300b0160 0x8b058b030601602c 0xf0387010200e07ff 0xbe070e020401c0ff

def z174 : W := mkw 0x400048cc80000002 0x0800091990000000 0x00000cee00000000 0x0000019dc0000000

def z175 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xa007801fdc71fe3a 0x3400f003fb8e3fc7

def z176 : W := mkw 0x010022c580000002 0x00200458b0000000 0x000003e1c0000000 0x0000007c38000000

def z177 : W := mkw 0x0000000040000808 0x0000000008000101 0xa0018011c000383a 0x1400300238000707

def z178 : W := mkw 0x1d806ea03ad00580 0x43b00dd4075a00b0 0x1fc07ce03bf001c4 0x83f80f9c077e0038

def z179 : W := mkw 0xbfffb777fffffef9 0x37fff6eeffffffdf 0xffffffffffffffff 0xffffffffffffffff

def z180 : W := mkw 0x200005224c104e18 0x040000a4498209c3 0x000000000000063a 0x00000000000000c7

def z181 : W := mkw 0x0311230145862ae8 0x2062246028b0c55d 0x27018301e78e3ffe 0x64e030603cf1c7ff

def z182 : W := mkw 0x58244c0a38094510 0x8b048981470128a2 0x58067c0e3801c7c5 0xab00cf81c70038f8

def z183 : W := mkw 0x0000000041062868 0x200000000820c50d 0x20000000000e383a 0x040000000001c707

def z184 : W := mkw 0x01006fa00c900780 0x40200df4019200f0 0x48c07fe01c7007c5 0x69180ffc038e00f8

def z185 : W := mkw 0x82778000336db001 0x104ef000066db600 0xa03f80003ffff800 0x3407f00007ffff00

def z186 : W := mkw 0xfce6ccee8830d412 0x1f9cd99dd1061a82 0x08c60cee1871c000 0x0118c19dc30e3800

def z187 : W := mkw 0xdeffd818336db001 0x1bdffb03066db600 0xfffffc1e3ffff801 0xffffff83c7ffff00

def z188 : W := mkw 0x0000042008100400 0x0000008401020080 0x08c00ce018700000 0x0118019c030e0000

def z189 : W := mkw 0x87d3a30147e4ba89 0x30fa746028fc9751 0x07c18301c7f03800 0x40f8306038fe0700

def z190 : W := mkw 0x200004220830d410 0x0400008441061a82 0x000000001871c000 0x00000000030e3800

def z191 : W := mkw 0xdfbd7e9b380b4572 0x9bf7afd3670168ae 0xff3e7c1e380fc7ff 0xbfe7cf83c701f8ff

def z192 : W := mkw 0xdff7eacd80000002 0x1bfefd59b0000000 0x0fc78fefc0000000 0x41f8f1fdf8000000

def z193 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xa7398311c78e383a 0x54e7306238f1c707

def z194 : W := mkw 0xdce6ccecba500502 0x5b9cd99d974a00a0 0x08c60cee18700000 0x0118c19dc30e0000

def z195 : W := mkw 0x000000000364b001 0x00000000006c9600 0x0000000007f03800 0x0000000000fe0700

def z196 : W := mkw 0x01006a8000000000 0x00200d5000000000 0x40007fe000000000 0x08000ffc00000000

def z197 : W := mkw 0x0000010004800280 0x0000002000900050 0x00000000278007c4 0x2000000004f000f8

def z198 : W := mkw 0x402c101a000b4070 0x880582034001680e 0xf03e701e200fc7ff 0xbe07ce03c401f8ff

def z199 : W := mkw 0x000004203a500500 0x40000084074a00a0 0x0000000018700000 0x00000000030e0000

def z200 : W := mkw 0x01006fa00c900780 0x40200df4019200f0 0x57007fe0278007c5 0xeae00ffc04f000f8

def z201 : W := mkw 0x0042800000209000 0x0008500000041200 0xa00780000001f800 0x1400f00000003f00

def z202 : W := mkw 0x231937334db6fef8 0x246326e669b6dfdf 0xf739f311ffffffff 0xfee73e623fffffff

def z203 : W := mkw 0x1d806a8032c00180 0x43b00d5006580030 0x5fc07fe0238001c5 0xcbf80ffc04700038

def z204 : W := mkw 0x1c804ca03a500500 0x43900994074a00a0 0x08c00ce018700000 0x0118019c030e0000

def z205 : W := mkw 0xdef7c8ccb36db003 0x1bdef919966db600 0xbfff8cee3ffff801 0xf7fff19dc7ffff00

def z206 : W := mkw 0x86d380000364b001 0x10da7000006c9600 0xafc780001ff1f801 0x75f8f00003fe3f00

def z207 : W := mkw 0x20428466c830dc18 0x0408508cd9061b83 0xa8c78cffd871f83a 0x1518f19ffb0e3f07

def z208 : W := mkw 0x1f916fa03fd42780 0x43f22df407fa84f0 0xfff9ffe03ffe3fc5 0xffff3ffc07ffc7f8

def z209 : W := mkw 0xddeefadd80000002 0x1bbddf5bb0000000 0x48c67fffc0000000 0x0918cffff8000000

def z210 : W := mkw 0x0000000032699001 0x00000000064d3200 0x000000001871c000 0x00000000030e3800

def z211 : W := mkw 0xdffffffdbed00782 0x5bffffffb7da00f0 0xdffffffffff007c5 0xfbfffffffffe00f8

def z212 : W := mkw 0xc27f905d80000002 0x184ff20bb0000000 0xc8ff8fffc0000001 0x591ff1fff8000000

def z213 : W := mkw 0x03193211018620e0 0x206326422030c41c 0x17387000238e01c4 0x82e70e000471c038

def z214 : W := mkw 0x9ce6800032699001 0x139cd000064d3200 0xa8c780001c71f801 0x7518f000038e3f00

def z215 : W := mkw 0x0042810044209a08 0x0008502008841341 0xe8c78311dc71fe3b 0x7d18f0623b8e3fc7

def z216 : W := mkw 0xc23d101900000002 0x1847a20320000000 0x0038000000000000 0x0007000000000000

def z217 : W := mkw 0x1b197f117d862fe8 0x23632fe22fb0c5fd 0xff39ff11ff8e3fff 0xffe73fe23ff1c7ff

def z218 : W := mkw 0xdffffbddc4820aea 0x3bffff7bb890415d 0xdfffffffc00007ff 0xdbfffffff80000ff

def z219 : W := mkw 0x0000040208004410 0x0000008041000882 0x40000c1e0000063a 0x08000183c00000c7

def z220 : W := mkw 0x5d887add80000002 0x0bb10f5bb0000000 0x5fc07fffc0000001 0xcbf80ffff8000000

def z221 : W := mkw 0x20000566cc104e18 0x040000acd98209c3 0x48c00fffdc70063b 0x691801fffb8e00c7

def z222 : W := mkw 0x0000040208024570 0x80000080410048ae 0x00000000000007fe 0x00000000000000ff

def z223 : W := mkw 0x01087fb14c920fe8 0x60210ff6299241fd 0x40007ff1c00007fe 0x08000ffe380000ff

def z224 : W := mkw 0x058023a006d00280 0x40b0047400da0050 0x57c073e027f007c5 0xeaf80e7c04fe00f8

def z225 : W := mkw 0x0108321100000000 0x0021064220000000 0x40007311c0000000 0x08000e6238000000

def z226 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0x4701f311c7803ffe 0x48e03e6238f007ff

def z227 : W := mkw 0xc7ffb2dd80000002 0x18fff65bb0000000 0x87ff83ffc0000000 0x50fff07ff8000000

def z228 : W := mkw 0xfeffdd7eff7fff79 0x9fdffbafdfefffef 0xffffffffffffffff 0xffffffffffffffff

def z229 : W := mkw 0x0000000000209000 0x0000000000041200 0x200000001c71f800 0x24000000038e3f00

def z230 : W := mkw 0xbef785227f7dfe19 0x17def0a44fefbfc3 0xbfff80003ffffe3b 0xf7fff00007ffffc7

def z231 : W := mkw 0x0319331177efbae9 0x206326622efdf75d 0xf739f311ffffffff 0xfee73e623fffffff

def z232 : W := mkw 0x9ef7800032400000 0x13def00006480000 0x9fff80003ff00001 0xf3fff00007fe0000

def z233 : W := mkw 0x9eb50000334d2001 0x13d6a0000669a400 0xbf3e00003b8fc001 0xb7e7c0000771f800

def z234 : W := mkw 0x0211000001042000 0x0042200000208400 0xa0398000000e3800 0x140730000001c700

def z235 : W := mkw 0x5824480830090100 0x8b04890106012020 0x0000000000000000 0x0000000000000000

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0xa80600001801c001 0x3500c00003003800

def z237 : W := mkw 0xdfbd7a9900000002 0x1bf7af5320000000 0x1738700000000000 0x82e70e0000000000

def z238 : W := mkw 0x0211000141042808 0x2042200028208501 0x00018001c0003800 0x0000300038000700

def z239 : W := mkw 0x582c5d1a7d8f6ff8 0xab058ba34fb1edff 0xf83e7c1e3f8fffff 0xbf07cf83c7f1ffff

def z240 : W := mkw 0x235bb375c5b6bae8 0x246b766eb8b6d75d 0xf7f9f3f1e7fe3fff 0xfeff3e7e3cffc7ff

def z241 : W := mkw 0x1d806ba006d00280 0x43b00d7400da0050 0x5fc07fe007f00001 0xcbf80ffc00fe0000

def z242 : W := mkw 0x5a3d5c1b790f6d78 0xab47ab836f21edaf 0xf83ffc1ff80fffff 0xbf07ff83ff01ffff

def z243 : W := mkw 0xdffffa9900000002 0x1bffff5320000000 0x9ffff00000000001 0xd3fffe0000000000

def z244 : W := mkw 0x5b3d7b1945862ae8 0x2b67af6328b0c55d 0xff3fff1fe78e3fff 0xffe7ffe3fcf1c7ff

def z245 : W := mkw 0x9ef7800032699001 0x13def000064d3200 0x9fff80001871c001 0xd3fff000030e3800

def z246 : W := mkw 0x402c141a080b4470 0x880582834101688e 0xe83e0c1e180fc63b 0x3d07c183c301f8c7

def z247 : W := mkw 0x58085c1a38024570 0x8b010b83470048ae 0x58007c1e380007ff 0xab000f83c70000ff

def z248 : W := mkw 0xdffffaddb00b0162 0x9bffff5bb601602c 0xdfffffffe00e01c5 0xdbfffffffc01c038

def z249 : W := mkw 0x786edc7eb83bd570 0x8f0ddb8fd7077aae 0xf8fe7cfe387fc7ff 0xbf1fcf9fc70ff8ff

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x48c00fe000000001 0x491801fc00000000

def z251 : W := mkw 0x1dc2efa03ef09780 0x43b85df407de12f0 0xffc7ffe03ff1ffc5 0xfff8fffc07fe3ff8

def z252 : W := mkw 0x5b3d7e1b398f65f0 0xab67afc36731ecbe 0xff3e7c1e3b8fc7ff 0xbfe7cf83c771f8ff

def z253 : W := mkw 0xbce68566fe79de19 0x179cd0acdfcf3bc3 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z254 : W := mkw 0x20428566ff7dfe19 0x040850acdfefbfc3 0xe8c78ffffffffe3b 0x7d18f1ffffffffc7

def z255 : W := mkw 0x204285224c30de18 0x040850a449861bc3 0xa8c780001c71fe3b 0x7518f000038e3fc7

def z256 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xa8ff8000187ff800 0x151ff000030fff00

def z257 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0x28c60cee1c71fe3a 0x2518c19dc38e3fc7

def z258 : W := mkw 0x200005227f7dfe19 0x040000a44fefbfc3 0x200000003ffffe3a 0x2400000007ffffc7

def z259 : W := mkw 0x0100230004800280 0x0020046000900050 0x0700030007800000 0x40e0006000f00000

def z260 : W := mkw 0xdffffeddb8000502 0x1bffffdbb70000a0 0xdffffffff80007c5 0xfbffffffff0000f8

def z261 : W := mkw 0xdffffadf800b4072 0x9bffff5bf001680e 0xffffffffc00fc03b 0xdffffffff801f807

def z262 : W := mkw 0x87d3a3e586d00282 0x50fa747cb0da0050 0x07c183e1c7f00000 0x40f8307c38fe0000

def z263 : W := mkw 0x18004c0038000500 0x03000980070000a0 0x08000c0018000000 0x0100018003000000

def z264 : W := mkw 0x204284668830d410 0x0408508cd1061a82 0x08c60cee1871c000 0x0118c19dc30e3800

def z265 : W := mkw 0x00000000300b0160 0x800000000601602c 0x00000000200e01c4 0x000000000401c038

def z266 : W := mkw 0x3cc28566fe70de18 0x079850acdfce1bc3 0xffc78ffffff1fe3b 0xfff8f1fffffe3fc7

def z267 : W := mkw 0xdfbd7b9945862aea 0x3bf7af7328b0c55d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z268 : W := mkw 0x9ef78000336db001 0x13def000066db600 0x0fc780001ff1f800 0x41f8f00003fe3f00

def z269 : W := mkw 0xdef7cc0a3b6df511 0x9bdef981476dbea2 0xbfff8c0e3ffff801 0xf7fff181c7ffff00

def z270 : W := mkw 0x0000000032400000 0x0000000006480000 0x000000003ff00000 0x2000000007fe0000

def z271 : W := mkw 0x000005203ed00780 0x400000a407da00f0 0x000000003ff007c4 0x2000000007fe00f8

def z272 : W := mkw 0x0000040208004410 0x0000008041000882 0x08060c0e1801c000 0x0100c181c3003800

def z273 : W := mkw 0x20428446c820dc18 0x04085088d9041b83 0xe8078c1fd801fe3b 0x3d00f183fb003fc7

def z274 : W := mkw 0x9ed380003364b001 0x13da7000066c9600 0x1fc180003ff03801 0xe3f8300007fe0700

def z275 : W := mkw 0x8277800000000000 0x104ef00000000000 0x803f800000000000 0x1007f00000000000

def z276 : W := mkw 0xdffffedf88004412 0x1bffffdbf1000882 0xffffffffd801c63b 0xfffffffffb0038c7

def z277 : W := mkw 0x582c5c1a08004410 0x0b058b8341000882 0xf83e7c1e1801c63b 0xbf07cf83c30038c7

def z278 : W := mkw 0x004284020820d410 0x0008508041041a82 0xe8c78c1e1c71fe3b 0x7d18f183c38e3fc7

def z279 : W := mkw 0xbef78164f77dba09 0x17def02c9eefb741 0xbfff83e1fffff801 0xf7fff07c3fffff00

def z280 : W := mkw 0xc27f901a012ff071 0x984ff2034025fe0e 0xa03f801e000ff83a 0x1407f003c001ff07

def z281 : W := mkw 0x9ff7a2c5b36db003 0x13fef458b66db600 0xbfff83e1fffff801 0xf7fff07c3fffff00

def z282 : W := mkw 0x2000012044309a08 0x0400002408861341 0x0000000004703800 0x00000000008e0700

def z283 : W := mkw 0x0000040238094510 0x80000080470128a2 0x000000001801c000 0x0000000003003800

def z284 : W := mkw 0x0100230044800a88 0x0020046008900151 0xf701f311e7803fff 0xfee03e623cf007ff

def z285 : W := mkw 0x433d331b458f6af8 0xa867a66368b1ed5f 0xf73ff31fe78fffff 0xfee7fe63fcf1ffff

def z286 : W := mkw 0x1d806ea03a500500 0x43b00dd4074a00a0 0x5fc07fe018700001 0xcbf80ffc030e0000

def z287 : W := mkw 0x20428566cdb6fef8 0x240850acd9b6dfdf 0xe8c78fffffffffff 0x7d18f1ffffffffff

def z288 : W := mkw 0xdffffffdbffdb783 0x5bffffffb7ffb6f0 0xffffffffffffffc5 0xfffffffffffffff8

def z289 : W := mkw 0xdde6eacc80000002 0x1bbcdd5990000000 0x5fc67fee00000001 0xcbf8cffdc0000000

def z290 : W := mkw 0x9ef78100776dba09 0x13def0200eedb741 0xffff8311fffffe3b 0xfffff0623fffffc7

def z291 : W := mkw 0x41087fba0c9247f0 0xc8210ff7419248fe 0x40007ffe000007fe 0x08000fffc00000ff

def z292 : W := mkw 0x00000002000b4070 0x800000004001680e 0x20000000000fc03a 0x040000000001f807

def z293 : W := mkw 0x0319331144820ae8 0x206326622890415d 0xd739f311c00007ff 0xdae73e62380000ff

def z294 : W := mkw 0x010027200c900680 0x002004e4019200d0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z295 : W := mkw 0x20000566cc30de18 0x040000acd9861bc3 0x60000fffdc71fe3a 0x2c0001fffb8e3fc7

def z296 : W := mkw 0x5fbd7fbb7fdf6ff8 0xebf7aff76ffbedff 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0xe0018311dc71fe3b 0x7c0030623b8e3fc7

def z298 : W := mkw 0x1e91000033442000 0x03d2200006688400 0xbff980003ffe3801 0xf7ff300007ffc700

def z299 : W := mkw 0x9ce6800032699001 0x139cd000064d3200 0x1fc600003ff1c001 0xe3f8c00007fe3800

def z300 : W := mkw 0x582c5d1a7c0b4f78 0x8b058ba34f8169ef 0xf83fff1ffc0fffff 0xff07ffe3ff81ffff

def z301 : W := mkw 0x1d806b8036c00380 0x43b00d7006d80070 0x57007300278007c5 0xeae00e6004f000f8

def z302 : W := mkw 0x010027203ed00780 0x402004e407da00f0 0x570073003ff007c5 0xeae00e6007fe00f8

def z303 : W := mkw 0x0042804480000000 0x0008500890000000 0x00c183e1c0000000 0x4018307c38000000

def z304 : W := mkw 0xdffffadd8364b003 0x1bffff5bb06c9600 0xdfffffffc7f03801 0xdbfffffff8fe0700

def z305 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xa83e0c1e180fc03a 0x1507c183c301f807

def z306 : W := mkw 0x0000000000000000 0x0000000000000000 0x1700000027800001 0xe2e0000004f00000

def z307 : W := mkw 0x0000040038000500 0x00000080070000a0 0x00000000380007c4 0x20000000070000f8

def z308 : W := mkw 0xdfffffba3ffff7f1 0xdbfffff747fffefe 0xfffffffe3fffffff 0xffffffffc7ffffff

def z309 : W := mkw 0x0311230145842a88 0x2062246028b08551 0xb7398301e78e3801 0xf6e730603cf1c700

def z310 : W := mkw 0x827f9011412fb869 0x304ff2022825f70d 0xa03f8011c00ff83a 0x1407f0023801ff07

def z311 : W := mkw 0x0000000000020060 0x000000000000400c 0x20000000200e07fe 0x240000000401c0ff

def z312 : W := mkw 0x1d806fa00c900780 0x43b00df4019200f0 0x5fc07fe0000007c5 0xcbf80ffc000000f8

def z313 : W := mkw 0xfffffadfc020d81a 0x1fffff5bf8041b03 0xffffffffc001f83b 0xdffffffff8003f07

def z314 : W := mkw 0x5dac7a9832cb01e0 0xcbb58f530659603c 0x17387000238e01c4 0x82e70e000471c038

def z315 : W := mkw 0x0319331144000a08 0x0063266228800141 0xf739f311c4003e3b 0xfee73e62388007c7

def z316 : W := mkw 0xffffffffcc104e1a 0x1ffffffff98209c3 0xdfffffffc000063b 0xdbfffffff80000c7

def z317 : W := mkw 0x40085c1a08024570 0x88010b83410048ae 0xe8067c1e1801c7ff 0x3d00cf83c30038ff

def z318 : W := mkw 0x1d806fa23edb47f0 0xc3b00df447db68fe 0x7fc07fe03fffc7ff 0xeff80ffc07fff8ff

def z319 : W := mkw 0x9fd3efe5bed00782 0x53fa7dfcb7da00f0 0x5fc1ffe1fff007c5 0xebf83ffc3ffe00f8

def z320 : W := mkw 0xdfffff1b7feffff9 0xbbffffe36ffdffff 0xffffff1fffffffff 0xffffffe3ffffffff

def z321 : W := mkw 0x582c5c18380b0560 0x8b058b83070160ac 0x58387c00380e07c5 0xab070f800701c0f8

def z322 : W := mkw 0x0008101140020868 0x200102022800410d 0x00000011c000003a 0x0000000238000007

def z323 : W := mkw 0x43197add80000002 0x08632f5bb0000000 0xd739ffffc0000001 0xdae73ffff8000000

def z324 : W := mkw 0xdeffd8dd80000002 0x1bdffb1bb0000000 0x88ff8cffc0000000 0x111ff19ff8000000

def z325 : W := mkw 0x0311230005842280 0x0062246000b08450 0xf739f300278e3fc5 0xfee73e6004f1c7f8

def z326 : W := mkw 0xe27f905fc020d81a 0x1c4ff20bf8041b03 0xa03f801fc001f83a 0x1407f003f8003f07

def z327 : W := mkw 0x0311230145842a88 0x2062246028b08551 0x5701f301e7803fc5 0xeae03e603cf007f8

def z328 : W := mkw 0xdce6c8ccb2699003 0x1b9cd919964d3200 0x08c60cee1871c000 0x0118c19dc30e3800

def z329 : W := mkw 0x9ef7804480000000 0x13def00890000000 0xdfff8fffc0000001 0xdbfff1fff8000000

def z330 : W := mkw 0x84c280c480000002 0x1098501890000000 0x00c000e000000000 0x0018001c00000000

def z331 : W := mkw 0x031937317fd62fe8 0x606326e62ffac5fd 0xf739f311fffe3fff 0xfee73e623fffc7ff

def z332 : W := mkw 0x0042804480209000 0x0008500890041200 0xe8c78fffdc71f801 0x7d18f1fffb8e3f00

def z333 : W := mkw 0x82778000012db001 0x104ef0000025b600 0xb73f8000278ff801 0xf6e7f00004f1ff00

def z334 : W := mkw 0x0008111044020a68 0x000102220880414d 0xf039f311e40e3fff 0xfe073e623c81c7ff

def z335 : W := mkw 0x00000000018620e0 0x200000000030c41c 0x00000000238e01c4 0x000000000471c038

def z336 : W := mkw 0x0580228002c00080 0x40b0045000580010 0x0700000003800000 0x00e0000000700000

def z337 : W := mkw 0x9fffffb17fffbfe9 0x73fffff62ffff7fd 0xfffffff1ffffffff 0xfffffffe3fffffff

def z338 : W := mkw 0x0319331145842a88 0x2063266228b08551 0xd739f311c7803801 0xdae73e6238f00700

def z339 : W := mkw 0xdffffbddf7efbaeb 0x3bffff7bbefdf75d 0xffffffffffffffff 0xffffffffffffffff

def z340 : W := mkw 0x43197bddc5862aea 0x28632f7bb8b0c55d 0xf739ffffe78e3fff 0xfee73ffffcf1c7ff

def z341 : W := mkw 0xdffffaddb34d2003 0x1bffff5bb669a400 0xdfffffffe38e0001 0xdbfffffffc71c000

def z342 : W := mkw 0x582c5c1a08024570 0x8b058b83410048ae 0xd83e7c1e000007ff 0x9b07cf83c00000ff

def z343 : W := mkw 0x7b7fff7ffdbffff8 0xaf6fffefffb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z344 : W := mkw 0xdffffadd818620e2 0x3bffff5bb030c41c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z345 : W := mkw 0x0008101000020060 0x000102020000400c 0x40007010000007fe 0x08000e02000000ff

def z346 : W := mkw 0x606e957ecc3bde78 0x8c0dd2afd9877bcf 0xe8ff8fffdc7ffe3b 0x7d1ff1fffb8fffc7

def z347 : W := mkw 0xdeff905db36db003 0x1bdff20bb66db600 0xbfff801ffffff801 0xf7fff003ffffff00

def z348 : W := mkw 0x000004023b6ff571 0x80000080476dfeae 0x200000003ffffffe 0x2400000007ffffff

def z349 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xe039f311c00e3ffe 0x1c073e623801c7ff

def z350 : W := mkw 0x414afadd80000002 0x08295f5bb0000000 0xc8c7ffffc0000001 0x5918fffff8000000

def z351 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0x37387000278e3ffe 0xa6e70e0004f1c7ff

def z352 : W := mkw 0x82350000010d2001 0x1046a0000021a400 0x00380000000e0000 0x000700000001c000

def z353 : W := mkw 0x204285668c30d610 0x040850acd1861ac2 0x48c60fee1c71c601 0x6918c1fdc38e38c0

def z354 : W := mkw 0x582c5818300b0160 0x8b058b030601602c 0xd83e7c1e200e01c5 0x9b07cf83c401c038

def z355 : W := mkw 0x9eb50000334d2001 0x13d6a0000669a400 0xb7398000278e3801 0xf6e7300004f1c700

def z356 : W := mkw 0x1c8005203e500600 0x039000a407ca00c0 0x5fc00fe03ff00601 0xebf801fc07fe00c0

def z357 : W := mkw 0x1da46fa03ed90780 0x43b48df407db20f0 0xfffe7fe03fffc7c5 0xffffcffc07fff8f8

def z358 : W := mkw 0x20428164c4309a08 0x0408502c98861341 0xa8c783e1dc71f801 0x7518f07c3b8e3f00

def z359 : W := mkw 0x18085c1038020560 0x03010b82070040ac 0xf8387c10380e07ff 0xbf070f820701c0ff

def z360 : W := mkw 0xc27f905dc106286a 0x384ff20bb820c50d 0xa03f801fc00e383a 0x1407f003f801c707

def z361 : W := mkw 0xda7fd85d80000002 0x1b4ffb0bb0000000 0xd83ffc1fc0000001 0x9b07ff83f8000000

def z362 : W := mkw 0x0219101100000000 0x0043220220000000 0x80398011c0000000 0x1007300238000000

def z363 : W := mkw 0xbef78566cc30de18 0x17def0acd9861bc3 0xffff8fffdc71fe3b 0xfffff1fffb8e3fc7

def z364 : W := mkw 0x5a3d5c1a390f6570 0x8b47ab834721ecae 0xff3ffc1e3f8fffff 0xffe7ff83c7f1ffff

def z365 : W := mkw 0x0219101101062060 0x204322022020c40c 0x00380000000e0000 0x000700000001c000

def z366 : W := mkw 0x7866cc6eb839d510 0x8f0cd98dd7073aa2 0x08c60cee1871c000 0x0118c19dc30e3800

def z367 : W := mkw 0x9fb56fa03fdd2781 0x53f6adf407fba4f0 0x5ff87fe03ffe07c5 0xebff0ffc07ffc0f8

def z368 : W := mkw 0x0000000030090000 0x0000000006012000 0x20000000380fc000 0x240000000701f800

def z369 : W := mkw 0x423d101b410f6878 0xa847a2036821ed0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z370 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x170070003ff007c4 0xa2e00e0007fe00f8

def z371 : W := mkw 0x1b3d3311758f2ae8 0x2367a6622eb1e55d 0xff3ff311ff8fffff 0xffe7fe623ff1ffff

def z372 : W := mkw 0x18004d203ed00780 0x430009a407da00f0 0x58007c003ff007c5 0xab000f8007fe00f8

def z373 : W := mkw 0x3cc2cde6fe70df18 0x479859bcdfce1be3 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z374 : W := mkw 0x200005224db6fef8 0x240000a449b6dfdf 0x200000003ffffffe 0x2400000007ffffff

def z375 : W := mkw 0x000005200c100600 0x000000a4018200c0 0x40000fe000000600 0x080001fc000000c0

def z376 : W := mkw 0x000005200c100600 0x000000a4018200c0 0x000000001c700600 0x20000000038e00c0

def z377 : W := mkw 0xa6d38566cf74fe19 0x14da70acd9ee9fc3 0xefc78fffdff1fe3b 0x7df8f1fffbfe3fc7

def z378 : W := mkw 0x058027a03ed00780 0x40b004f407da00f0 0x07c003e03ff007c4 0x60f8007c07fe00f8

def z379 : W := mkw 0x0100230144800a88 0x2020046028900151 0x00000301c0000000 0x0000006038000000

def z380 : W := mkw 0x9ef7800001042000 0x13def00000208400 0xbfff8000278e3801 0xf7fff00004f1c700

def z381 : W := mkw 0x1d806a8032c00180 0x43b00d5006580030 0x1fc070003ff001c5 0xe3f80e0007fe0038

def z382 : W := mkw 0x19006fa03c900780 0x43200df4079200f0 0x58007fe0380007c5 0xab000ffc070000f8

def z383 : W := mkw 0x5b3d7a19318f21e0 0xab67af432631e43c 0x17387000238e01c4 0x82e70e000471c038

def z384 : W := mkw 0xdfbd7a9900000002 0x1bf7af5320000000 0xdf3e7c1e00000001 0x9be7cf83c0000000

def z385 : W := mkw 0xc066804c80000002 0x180cd00990000000 0x0006000e00000000 0x0000c001c0000000

def z386 : W := mkw 0xdfbd7a9900000002 0x1bf7af5320000000 0xd739f311c0000001 0xdae73e6238000000

def z387 : W := mkw 0x22538566cd34fe18 0x044a70acd9a69fc3 0xffff8ffffffffe3b 0xfffff1ffffffffc7

def z388 : W := mkw 0x23193777cd966ef8 0x246326eef9b2cddf 0xf739ffffe78e3fff 0xfee73ffffcf1c7ff

def z389 : W := mkw 0x1c804ca03a500500 0x43900994074a00a0 0x58c07ce0387007c5 0xab180f9c070e00f8

def z390 : W := mkw 0x00428144c4000a08 0x0008502898800141 0xe8c78fffc4003e3b 0x7d18f1fff88007c7

def z391 : W := mkw 0x9ef7810077efbae9 0x33def0200efdf75d 0xbfff80003fffffff 0xf7fff00007ffffff

def z392 : W := mkw 0xdffffadd80209002 0x1bffff5bb0041200 0xffffffffdc71f801 0xfffffffffb8e3f00

def z393 : W := mkw 0x586edc5eb80b4570 0x8b0ddb8bd70168ae 0xf8fffffff80fc7ff 0xff1fffffff01f8ff

def z394 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x0fc00fe01ff00000 0x41f801fc03fe0000

def z395 : W := mkw 0xdfbd7a99300b0162 0x9bf7af532601602c 0x17387000200e01c4 0x82e70e000401c038

def z396 : W := mkw 0x1c80488000000000 0x0390091000000000 0x08c00ce000000000 0x0118019c00000000

def z397 : W := mkw 0x20428166c430da18 0x0408502cd8861b43 0xa0c783ffc471f83a 0x5418f07ff88e3f07

def z398 : W := mkw 0x9ef78000012db001 0x13def0000025b600 0xbfff8000000ff801 0xd7fff0000001ff00

def z399 : W := mkw 0x786edd7ecc30de18 0x0f0ddbafd9861bc3 0xf8ffffffdc71fe3b 0xff1ffffffb8e3fc7

def z400 : W := mkw 0xbff7efe6fffdff99 0x57fefdfcdfffbff3 0xffffffffffffffff 0xffffffffffffffff

def z401 : W := mkw 0x0219101141062868 0x204322022820c50d 0xf039f011e00e3fff 0xbe073e023c01c7ff

def z402 : W := mkw 0x3d806fa27ef0df98 0x47b00df44fde1bf3 0x7fc07fe03ff1ffff 0xeff80ffc07fe3fff

def z403 : W := mkw 0x05806fa00ed00780 0x40b00df401da00f0 0x47c07fe007f007c4 0x48f80ffc00fe00f8

def z404 : W := mkw 0x0100230004800280 0x0020046000900050 0x40007300000007c4 0x08000e60000000f8

def z405 : W := mkw 0x0311220100000000 0x0062244020000000 0x07018301c0000000 0x40e0306038000000

def z406 : W := mkw 0xdeff901a336ff071 0x9bdff203466dfe0e 0xbfff801e3ffff83b 0xf7fff003c7ffff07

def z407 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x57007fe0238007c4 0x8ae00ffc047000f8

def z408 : W := mkw 0xdef7c8cc80000002 0x1bdef91990000000 0x9fff8cee00000001 0xd3fff19dc0000000

def z409 : W := mkw 0xa6d38164c774ba09 0x14da702c98ee9741 0x07c183e1c7f03800 0x40f8307c38fe0700

def z410 : W := mkw 0xdffffedfbb6ff573 0x9bffffdbf76dfeae 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0x48067c1e1801c7fe 0x0900cf83c30038ff

def z412 : W := mkw 0x0000000200004010 0x0000000040000802 0xa006001e0001c03a 0x1400c003c0003807

def z413 : W := mkw 0x9ff7ea8000000000 0x13fefd5000000000 0xdfffffe000000001 0xdbfffffc00000000

def z414 : W := mkw 0x235bb357c5a6faf8 0x246b766af8b4df5f 0xf73ff31fe78fffff 0xfee7fe63fcf1ffff

def z415 : W := mkw 0x000005204c100e08 0x000000a4098201c1 0xe8c18ff1dc703e3b 0x7d1831fe3b8e07c7

def z416 : W := mkw 0x0219101141062868 0x204322022820c50d 0xb7398011e78e383b 0xf6e730023cf1c707

def z417 : W := mkw 0x0008111045862ae8 0x2001022208b0c55d 0xf0387010278e3fff 0xbe070e0204f1c7ff

def z418 : W := mkw 0x1824000030090000 0x0304800006012000 0x080600001801c000 0x0100c00003003800

def z419 : W := mkw 0x402c1018000b0060 0x880582030001600c 0x00380000000e0000 0x000700000001c000

def z420 : W := mkw 0x1d806fa23ed04790 0x43b00df447da08f2 0xffc67ffe3ff1c7ff 0xfff8cfffc7fe38ff

def z421 : W := mkw 0xdffffaddc106286a 0x3bffff5bb820c50d 0xffffffffc00e383b 0xdffffffff801c707

def z422 : W := mkw 0xdffffadd80020062 0x1bffff5bb000400c 0xffffffffe00e07ff 0xfffffffffc01c0ff

def z423 : W := mkw 0xa7d3a7e7cc30de1a 0x14fa74fcf9861bc3 0xefc78fffdc71fe3b 0x7df8f1fffb8e3fc7

def z424 : W := mkw 0x0211010045862ae8 0x2042202008b0c55d 0xb7398000278e3fff 0xf6e7300004f1c7ff

def z425 : W := mkw 0xdffffaddb2400002 0x1bffff5bb6480000 0xdffffffffff00001 0xfbfffffffffe0000

def z426 : W := mkw 0x2142efe6ccb0df98 0x44285dfcd9961bf3 0xe8c7ffffdc71ffff 0x7d18fffffb8e3fff

def z427 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0380000200e0001 0xb60700000401c000

def z428 : W := mkw 0xc37ffadd80000002 0x186fff5bb0000000 0xc03fffffc0000000 0x1807fffff8000000

def z429 : W := mkw 0x782c5d7efc1b4f78 0x8f058bafdf8369ef 0xf83e7ffff80fc7ff 0xbf07cfffff01f8ff

def z430 : W := mkw 0x004285200c309600 0x000850a4018612c0 0xe8c78fe01c71fe01 0x7d18f1fc038e3fc0

def z431 : W := mkw 0x1f997b9145862ae8 0x23f32f7228b0c55d 0xfff9fff1e78e3fff 0xffff3ffe3cf1c7ff

def z432 : W := mkw 0x0042800000209000 0x0008500000041200 0x00c1800004703800 0x40183000008e0700

def z433 : W := mkw 0xdfbd7a99334d2003 0x1bf7af532669a400 0x17387000238e0000 0x82e70e000471c000

def z434 : W := mkw 0x214ab777ccb2def8 0x242956eef9965bdf 0xe8c7ffffdc71ffff 0x7d18fffffb8e3fff

def z435 : W := mkw 0x87d3a3c5c5842a8a 0x30fa7478b8b08551 0x07c183e1c7803800 0x40f8307c38f00700

def z436 : W := mkw 0x20428564cc309e08 0x040850ac998613c1 0x48c18fe1dc703e01 0x691831fc3b8e07c0

def z437 : W := mkw 0x0042800000000000 0x0008500000000000 0x88c7800000000001 0x5118f00000000000

def z438 : W := mkw 0x0024000000090000 0x0004800000012000 0xa03e0000000fc000 0x1407c0000001f800

def z439 : W := mkw 0x582c101a300b4070 0x8b0582034601680e 0xb83e001e380fc03b 0xb707c003c701f807

def z440 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0x30387000380fc7fe 0xa6070e000701f8ff

def z441 : W := mkw 0x0219101001062060 0x004322020020c40c 0xf739f010278e3fff 0xfee73e0204f1c7ff

def z442 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0x183e7c0e380fc1c4 0x8307cf81c701f838

def z443 : W := mkw 0x20000566cc104e18 0x040000acd98209c3 0xe0018fffc4003e3b 0x7c0031fff88007c7

def z444 : W := mkw 0xffffffffff7dfe1b 0x1fffffffffefbfc3 0xfffffffffffffe3b 0xffffffffffffffc7

def z445 : W := mkw 0x19006f003c800780 0x03200de0079000f0 0x5f007f003f8007c5 0xebe00fe007f000f8

def z446 : W := mkw 0x1ca4000032490000 0x0394800006492000 0xbffe00003fffc001 0xf7ffc00007fff800

def z447 : W := mkw 0xdfbd7fb93ed00782 0x5bf7aff727da00f0 0x5ff87fe03ff007c5 0xebff0ffc07fe00f8

def z448 : W := mkw 0x582c581800000000 0x0b058b0300000000 0x1038700000000000 0x82070e0000000000

def z449 : W := mkw 0x0000010044820ae8 0x200000200890415d 0x00000000000007fe 0x00000000000000ff

def z450 : W := mkw 0x1d806fa00c100600 0x03b00df4018200c0 0x5fc07fe01c700601 0xebf80ffc038e00c0

def z451 : W := mkw 0x3d806fe6fed04f98 0x47b00dfcdfda09f3 0x5fc07ffffff007ff 0xebf80ffffffe00ff

def z452 : W := mkw 0xa7d3a3e5c4309a0a 0x14fa747cb8861341 0x07c183e1c4703800 0x40f8307c388e0700

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x50007000200007c5 0xaa000e00040000f8

def z454 : W := mkw 0x9fffb21133efb0e1 0x33fff642267df61c 0xbffff0003ffff9c5 0xf7fffe0007ffff38

def z455 : W := mkw 0x9ce6800032699001 0x139cd000064d3200 0xb8fe0000387fc001 0xb71fc000070ff800

def z456 : W := mkw 0x1c804ca03a500500 0x43900994074a00a0 0x1fc00ce03ff00001 0xe3f8019c07fe0000

def z457 : W := mkw 0x0000000032c00180 0x4000000006580030 0x00000000238001c4 0x0000000004700038

def z458 : W := mkw 0xa2778566cd3dfe19 0x144ef0acd9a7bfc3 0xe8ff8fffdc7ffe3b 0x7d1ff1fffb8fffc7

def z459 : W := mkw 0x1824040238094410 0x0304808047012882 0xf83e0c1e380fc63b 0xbf07c183c701f8c7

def z460 : W := mkw 0x38668566fc39de18 0x070cd0acdf873bc3 0xf8ff8ffffc7ffe3b 0xff1ff1ffff8fffc7

def z461 : W := mkw 0x20428146c420da18 0x04085028d8841b43 0xe007831fc401fe3b 0x7c00f063f8803fc7

def z462 : W := mkw 0x00004c0008000500 0x00000980010000a0 0x40007c00000007c4 0x08000f80000000f8

def z463 : W := mkw 0x0100230045862ae8 0x2020046008b0c55d 0x77007300278e3fff 0xeee00e6004f1c7ff

def z464 : W := mkw 0x41087a9900000002 0x08210f5320000000 0x0000700000000000 0x00000e0000000000

def z465 : W := mkw 0x18240402380b4570 0x83048080470168ae 0xb83e0000380fc7ff 0xb707c0000701f8ff

def z466 : W := mkw 0x1c804da03e500700 0x439009b407ca00e0 0x48c00fe01c700601 0x691801fc038e00c0

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x08c000001c700001 0x61180000038e0000

def z468 : W := mkw 0x0319331104800280 0x0063266220900050 0xd739f311e78007c5 0xfae73e623cf000f8

def z469 : W := mkw 0x1d887fb17ed20fe8 0x63b10ff62fda41fd 0x5fc07ff1fff007ff 0xebf80ffe3ffe00ff

def z470 : W := mkw 0xdeffdc1a380b4570 0x9bdffb83470168ae 0xfffffc1e380fc7ff 0xffffff83c701f8ff

def z471 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x1ffe7cee00000000 0x83ffcf9dc0000000

def z472 : W := mkw 0x0008101000000000 0x0001020200000000 0xd038701000000001 0x9a070e0200000000

def z473 : W := mkw 0x03193311058622e0 0x2063266220b0c45c 0x57387300278e07c5 0xeae70e6004f1c0f8

def z474 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x17f9f3e1c0000000 0xc2ff3e7c38000000

def z475 : W := mkw 0x079933b147d62ae8 0x60f3267628fac55d 0xf7f9f3f1e7fe3fff 0xfeff3e7e3cffc7ff

def z476 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0x1739f301e78e39c4 0xc2e73e603cf1c738

def z477 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0x40c18fffc4703e3a 0x481831fff88e07c7

def z478 : W := mkw 0x582c581a300b4170 0x8b058b034601682e 0xb03e701e200fc1fe 0x9607ce03c401f83f

def z479 : W := mkw 0x825380000124b001 0x104a700000249600 0x0001800000003800 0x0000300000000700

def z480 : W := mkw 0x00000000012db001 0x000000000025b600 0x20000000000ff800 0x040000000001ff00

def z481 : W := mkw 0x592c7f1a3c8b47f0 0x8b258fe3479168fe 0xff3e7f1e3f8fc7ff 0xffe7cfe3c7f1f8ff

def z482 : W := mkw 0x1a350000310d2000 0x0346a0000621a400 0xbf3f80003f8ff801 0xf7e7f00007f1ff00

def z483 : W := mkw 0x9ce68000336db001 0x139cd000066db600 0x28c600003ffff800 0x2518c00007ffff00

def z484 : W := mkw 0x5b3d7e1b380b4570 0x8b67afc3670168ae 0xff3fff1ff80fc7ff 0xffe7ffe3ff01f8ff

def z485 : W := mkw 0x9ce6cca03a799501 0x539cd994074f32a0 0x08c60ce01871c000 0x0118c19c030e3800

def z486 : W := mkw 0x837fb31145afbae9 0x306ff66228b5f75d 0xf73ff311e78fffff 0xfee7fe623cf1ffff

def z487 : W := mkw 0x9ef7800030090000 0x13def00006012000 0xbfff8000380fc001 0xf7fff0000701f800

def z488 : W := mkw 0x87d3a2c58364b003 0x10fa7458b06c9600 0x07c183e1c7f03800 0x40f8307c38fe0700

def z489 : W := mkw 0x0311220101842080 0x2062244020308410 0x0700000003800000 0x00e0000000700000

def z490 : W := mkw 0x0000010044000a08 0x0000002008800141 0x2000000004003e3a 0x24000000008007c7

def z491 : W := mkw 0x4008581800000000 0x08010b0300000000 0x40007c1e00000000 0x08000f83c0000000

def z492 : W := mkw 0x000005024c004e18 0x000000a0498009c3 0xe8078f1fdc01fe3b 0x7d00f1e3fb803fc7

def z493 : W := mkw 0x87dbb2d580000002 0x10fb765ab0000000 0xd7f9f3f1c0000001 0xdaff3e7e38000000

def z494 : W := mkw 0x5ca44caa3a594510 0xcb948995474b28a2 0x08c60cee1871c000 0x0118c19dc30e3800

def z495 : W := mkw 0xdffffbfd86d00282 0x5bffff7fb0da0050 0xdfffffffc7f00001 0xdbfffffff8fe0000

def z496 : W := mkw 0x1c8005203ed00780 0x439000a407da00f0 0x1fc000003ff007c5 0xe3f8000007fe00f8

def z497 : W := mkw 0x0008101000020060 0x000102020000400c 0xa0380010000e003a 0x140700020001c007

def z498 : W := mkw 0x582c5d3a3c1b4770 0x8b058ba7478368ee 0xf8fe7ffe3c7fc7ff 0xff1fcfffc78ff8ff

def z499 : W := mkw 0x4008581800020160 0x88010b030000402c 0x00007000000001c4 0x00000e0000000038

def z500 : W := mkw 0x1d806a8032400000 0x03b00d5006480000 0x5fc07fe03ff00001 0xebf80ffc07fe0000

def z501 : W := mkw 0x614affffcc30de1a 0x0c295ffff9861bc3 0xe8c7ffffdc71fe3b 0x7d18fffffb8e3fc7

def z502 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x48c07fe0187007c4 0x09180ffc030e00f8

def z503 : W := mkw 0x1dc2eac480000000 0x03b85d5890000000 0xdfc7ffffc0000001 0xdbf8fffff8000000

def z504 : W := mkw 0x9ef7800000209000 0x13def00000041200 0xbfff80001c71f801 0xf7fff000038e3f00

def z505 : W := mkw 0x1824000000000000 0x0304800000000000 0x983e000000000001 0x9307c00000000000

def z506 : W := mkw 0x20428566fc3bdf78 0x840850acdf877bef 0xe8c78ffffc7fffff 0x7d18f1ffff8fffff

def z507 : W := mkw 0x8066800000299001 0x100cd00000053200 0x000600000001c000 0x0000c00000003800

def z508 : W := mkw 0x3dc2efe6bef0d790 0x47b85dfcd7de1af2 0x5fc67fee3ff1c7c5 0xebf8cffdc7fe38f8

def z509 : W := mkw 0x58244c0a380b4570 0x8b048981470168ae 0x28060c0e380fc7fe 0x2500c181c701f8ff

def z510 : W := mkw 0x1824000030090000 0x0304800006012000 0x10380000200e0000 0x820700000401c000

def z511 : W := mkw 0x9ef78000336db001 0x13def000066db600 0x1ffe00003bffc000 0x83ffc000077ff800

def z512 : W := mkw 0x0211000001042000 0x0042200000208400 0x17380000238e0000 0x82e700000471c000

def z513 : W := mkw 0x582c5c1a3b6ff571 0x8b058b83476dfeae 0xf83e7c1e3fffffff 0xbf07cf83c7ffffff

def z514 : W := mkw 0x225b9577cd36fe78 0x244b72aef9a6dfcf 0xe8ff8fffdc7ffe3b 0x7d1ff1fffb8fffc7

def z515 : W := mkw 0x5824480800000000 0x0b04890100000000 0x08060c0e00000000 0x0100c181c0000000

def z516 : W := mkw 0x592c7fba3c9b47f0 0xcb258ff7479368fe 0xf83e7ffe380fc7ff 0xbf07cfffc701f8ff

def z517 : W := mkw 0x00000000334d2001 0x000000000669a400 0x00000000238e0000 0x000000000471c000

def z518 : W := mkw 0xdca4488800000002 0x1b94891100000000 0x0000000000000000 0x0000000000000000

def z519 : W := mkw 0x8691000003442001 0x10d2200000688400 0x0700000003800000 0x00e0000000700000

def z520 : W := mkw 0x9fbd321133cf20e1 0x33f7a6422679e41c 0x17387000238e01c4 0x82e70e000471c038

def z521 : W := mkw 0x9fffb211336db001 0x13fff642266db600 0xfffff311fffff801 0xfffffe623fffff00

def z522 : W := mkw 0x058027a00ed00680 0x40b004f401da00d0 0x4fc00fe01ff00601 0x69f801fc03fe00c0

def z523 : W := mkw 0xdffffaddb0090002 0x1bffff5bb6012000 0xfffffffff80fc001 0xffffffffff01f800

def z524 : W := mkw 0x1f99331177c62ae8 0x23f326622ef8c55d 0xfff9f311fffe3fff 0xffff3e623fffc7ff

def z525 : W := mkw 0x9ca4000032490001 0x1394800006492000 0x0000000000000000 0x0000000000000000

def z526 : W := mkw 0x182c1010300b0060 0x030582020601600c 0xf83e7010380fc7ff 0xbf07ce020701f8ff

def z527 : W := mkw 0x025380000124b000 0x004a700000249600 0xbfff80003ffff801 0xf7fff00007ffff00

def z528 : W := mkw 0x87d3a3a007f4b281 0x50fa747400fe9650 0x07c183e007f03800 0x40f8307c00fe0700

def z529 : W := mkw 0x0000000001042000 0x0000000000208400 0x20000000278e3800 0x2400000004f1c700

def z530 : W := mkw 0x010023a004900280 0x4020047400920050 0x000003e000000000 0x0000007c00000000

def z531 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x68c00fe01c71fe3b 0x6d1801fc038e3fc7

def z532 : W := mkw 0x1d806fa03ffdb781 0x43b00df407ffb6f0 0x7fc07fe03fffffc5 0xeff80ffc07fffff8

def z533 : W := mkw 0x079123a147d42a88 0x60f2247428fa8551 0x07c183e1c7f03800 0x40f8307c38fe0700

def z534 : W := mkw 0x035bb25580000000 0x006b764ab0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z535 : W := mkw 0x235bb777cc30de18 0x046b76eef9861bc3 0xffffffffdc71fe3b 0xfffffffffb8e3fc7

def z536 : W := mkw 0x9ef7cc003b6db501 0x13def980076db6a0 0xfffffc003fffffc5 0xffffff8007fffff8

def z537 : W := mkw 0x782c5d3a7c3bdf78 0x8f058ba74f877bef 0xf83e7c1e3c7fffff 0xbf07cf83c78fffff

def z538 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0xe8060c1e1c71fe3b 0x3d00c183c38e3fc7

def z539 : W := mkw 0xe27f957fcc30de1a 0x1c4ff2aff9861bc3 0xe8ff8fffdc71fe3b 0x7d1ff1fffb8e3fc7

def z540 : W := mkw 0x9ce6800000000000 0x139cd00000000000 0x08c6000000000000 0x0118c00000000000

def z541 : W := mkw 0x20000566cc104e18 0x040000acd98209c3 0xe8060fffd801c63b 0x3d00c1fffb0038c7

def z542 : W := mkw 0x204284668830d410 0x0408508cd1061a82 0xe8c60cfe1871c63b 0x3d18c19fc30e38c7

def z543 : W := mkw 0x000005223edb47f0 0xc00000a447db68fe 0x200000003fffc7fe 0x2400000007fff8ff

def z544 : W := mkw 0x000005200c900780 0x400000a4019200f0 0x00000000000007c4 0x00000000000000f8

def z545 : W := mkw 0x1f997fb13fd627e0 0x63f32ff627fac4fc 0x5ff87fe03ffe07c5 0xebff0ffc07ffc0f8

def z546 : W := mkw 0x2000046688104410 0x0400008cd1020882 0x00000cee00000000 0x0000019dc0000000

def z547 : W := mkw 0x41087f1b4c824ff8 0xa8210fe3699049ff 0x40007f1fc00007fe 0x08000fe3f80000ff

def z548 : W := mkw 0x0008141208024470 0x000102824100488e 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z549 : W := mkw 0x18004c0238004510 0x03000980470008a2 0xf8067c1e3801c7ff 0xbf00cf83c70038ff

def z550 : W := mkw 0x1c80000000000000 0x0390000000000000 0x1fc0000000000001 0xc3f8000000000000

def z551 : W := mkw 0x0000010045862ae8 0x2000002008b0c55d 0xe0018311e78e3fff 0x7c0030623cf1c7ff

def z552 : W := mkw 0xdffffffd8c100602 0x1bffffffb18200c0 0xdfffffffdc700601 0xfbfffffffb8e00c0

def z553 : W := mkw 0x9fb56a8033cd2181 0x53f6ad500679a430 0x17387000238e01c4 0x82e70e000471c038

def z554 : W := mkw 0x00428000336db001 0x00085000066db600 0xa8c780003ffff801 0x7518f00007ffff00

def z555 : W := mkw 0xfffffffffef0df9a 0x5fffffffffde1bf3 0xfffffffffff1ffff 0xfffffffffffe3fff

def z556 : W := mkw 0x9ff7a2c580000002 0x13fef458b0000000 0x9fff83e1c0000001 0xd3fff07c38000000

def z557 : W := mkw 0x01083211008200e0 0x202106422010401c 0x00007000000001c4 0x00000e0000000038

def z558 : W := mkw 0x204280468020d010 0x04085008d0041a02 0x0006000e0001c000 0x0000c001c0003800

def z559 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x973ff01fc0000000 0x92e7fe03f8000000

def z560 : W := mkw 0x86f78000036db001 0x10def000006db600 0xa7ff800007fff800 0x54fff00000ffff00

def z561 : W := mkw 0x604add7ecc32df78 0x8c095bafd9865bef 0xe8c7ffffdc71ffff 0x7d18fffffb8e3fff

def z562 : W := mkw 0x0000012006d00280 0x4000002400da0050 0x0000000007f00000 0x0000000000fe0000

def z563 : W := mkw 0xda7fdc1a392ff571 0x9b4ffb834725feae 0xf83ffc1e380fffff 0xbf07ff83c701ffff

def z564 : W := mkw 0x1c80000032400000 0x0390000006480000 0x08c0000018700000 0x01180000030e0000

def z565 : W := mkw 0x1d806b8004800280 0x03b00d7000900050 0x5fc07fe0278007c5 0xebf80ffc04f000f8

def z566 : W := mkw 0x1d806fa07fd62fe8 0x63b00df40ffac5fd 0x7fc07fe03ffe3fff 0xeff80ffc07ffc7ff

def z567 : W := mkw 0x00004ca008100500 0x40000994010200a0 0x00000ce000000000 0x0000019c00000000

def z568 : W := mkw 0x5b3d7a1900000000 0x0b67af4320000000 0xdf3fff1fc0000001 0xdbe7ffe3f8000000

def z569 : W := mkw 0x2353a767cdb4fe98 0x246a74ecf9b69fd3 0xefc78fffdff1fe3b 0x7df8f1fffbfe3fc7

def z570 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0x48c60fffd871c63a 0x0918c1fffb0e38c7

def z571 : W := mkw 0x402c141a380b4570 0x88058283470168ae 0xa03e001e380fc7fe 0x3407c003c701f8ff

def z572 : W := mkw 0x1dc2efe4bed00780 0x43b85dfc97da00f0 0xdfc7fffffff007c5 0xfbf8fffffffe00f8

def z573 : W := mkw 0x41087edf88024572 0x88210fdbf10048ae 0x40007fffc00007fe 0x08000ffff80000ff

def z574 : W := mkw 0x41087bddc4820aea 0x28210f7bb890415d 0x40007fffc00007fe 0x08000ffff80000ff

def z575 : W := mkw 0x01083310048202e0 0x002106620090405c 0xf7387310278e07ff 0xfee70e6204f1c0ff

def z576 : W := mkw 0xdffffbdd84800282 0x1bffff7bb0900050 0xdfffffffe78007c5 0xfbfffffffcf000f8

def z577 : W := mkw 0xdffffbddc5842a8a 0x3bffff7bb8b08551 0xdfffffffc7803801 0xdbfffffff8f00700

def z578 : W := mkw 0x0219111145062a68 0x2043222228a0c54d 0xe0398311c40e3e3b 0x7c0730623881c7c7

def z579 : W := mkw 0x402c101800000000 0x0805820300000000 0x803e001e00000000 0x1007c003c0000000

def z580 : W := mkw 0x0108331144820ae8 0x202106622890415d 0x57007311e78007ff 0xeae00e623cf000ff

def z581 : W := mkw 0x592c7edfb80b4572 0x8b258fdbf70168ae 0xf83e7ffff80fc7ff 0xbf07cfffff01f8ff

def z582 : W := mkw 0x0008101000020060 0x000102020000400c 0x10387000200e01c4 0x82070e000401c038

def z583 : W := mkw 0x3cc2cce6ba70d510 0x4798599cd74e1aa2 0x08c60cee1871c000 0x0118c19dc30e3800

def z584 : W := mkw 0xdffffa99336db003 0x1bffff53266db600 0xbffff0003ffff801 0xf7fffe0007ffff00

def z585 : W := mkw 0x1866800030299000 0x030cd00006053200 0xb8ff80003c7ff801 0xf71ff000078fff00

def z586 : W := mkw 0x1f916fa17fd42f88 0x63f22df42ffa85f1 0x5fc1ffe1fff03fc5 0xebf83ffc3ffe07f8

def z587 : W := mkw 0x20428566fef0df98 0x440850acdfde1bf3 0xe8c78ffffff1ffff 0x7d18f1fffffe3fff

def z588 : W := mkw 0x031937137d8f6ff8 0xa06326e26fb1edff 0xf739f311ff8fffff 0xfee73e623ff1ffff

def z589 : W := mkw 0x01006a8000800180 0x40200d5000100030 0x00007000000001c4 0x00000e0000000038

def z590 : W := mkw 0x20000046c0004818 0x04000008d8000903 0x0000001fc000003a 0x00000003f8000007

def z591 : W := mkw 0xfffffbfdc4309a0a 0x1fffff7fb8861341 0xdfffffffc4703801 0xdbfffffff88e0700

def z592 : W := mkw 0xbce68466ba79d411 0x179cd08cd74f3a82 0x08c60cee1871c000 0x0118c19dc30e3800

def z593 : W := mkw 0x1800480030000100 0x0300090006000020 0x10007000200001c4 0x82000e0004000038

def z594 : W := mkw 0x582c581a000b4070 0x8b058b034001680e 0xf83e7c1e000fc03b 0x9f07cf83c001f807

def z595 : W := mkw 0x035bb355c5862ae8 0x206b766ab8b0c55d 0xffffffffe78e3fff 0xfffffffffcf1c7ff

def z596 : W := mkw 0xdfffffdffd8f6ffa 0xbbfffffbffb1edff 0xffffffffff8fffff 0xfffffffffff1ffff

def z597 : W := mkw 0xdceedc1a3a6bd571 0x9b9ddb83474d7aae 0xf8fe7c1e387fc7ff 0xbf1fcf83c70ff8ff

def z598 : W := mkw 0x00081412380b4570 0x80010282470168ae 0xf0387010380fc7ff 0xbe070e020701f8ff

def z599 : W := mkw 0x5dac7e9a380b4570 0x8bb58fd3470168ae 0xfffe7ffe380fc7ff 0xffffcfffc701f8ff

def z600 : W := mkw 0xdde6efecbed00782 0x5bbcddfd97da00f0 0x5fc67fee3ff007c5 0xebf8cffdc7fe00f8

def z601 : W := mkw 0x031937314d962ee8 0x206326e629b2c5dd 0xfff9fff1fffe3fff 0xffff3ffe3fffc7ff

def z602 : W := mkw 0xdfbd7a99018620e2 0x3bf7af532030c41c 0x17387000238e01c4 0x82e70e000471c038

def z603 : W := mkw 0x0319321141062868 0x206326422820c50d 0xf739f311c00e383b 0xdee73e623801c707

def z604 : W := mkw 0x1c804c003a400500 0x03900980074800a0 0x5fc07c003ff007c5 0xebf80f8007fe00f8

def z605 : W := mkw 0x21006fe6cc904f98 0x44200dfcd99209f3 0x40007fffc00007fe 0x08000ffff80000ff

def z606 : W := mkw 0x204284668830d410 0x0408508cd1061a82 0xa8c78cee1c71f801 0x7518f19dc38e3f00

def z607 : W := mkw 0x000005207fd62fe8 0x600000a40ffac5fd 0x200000003ffe3ffe 0x2400000007ffc7ff

def z608 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0x57387311e38e07fe 0x8ae70e623c71c0ff

def z609 : W := mkw 0x1d806e8038000500 0x03b00dd0070000a0 0x5fc07fe0380007c5 0xebf80ffc070000f8

def z610 : W := mkw 0x1f997a9100000000 0x03f32f5220000000 0xdff9fff1c0000001 0xdbff3ffe38000000

def z611 : W := mkw 0x9ef7cca03b7db501 0x53def994076fb6a0 0xbfff8ce03ffff801 0xf7fff19c07ffff00

def z612 : W := mkw 0xfffffffffc3bdf7a 0x9fffffffff877bef 0xfffffffffc7fffff 0xffffffffff8fffff

def z613 : W := mkw 0xdffffbddc4000a0a 0x1bffff7bb8800141 0xffffffffc4003e3b 0xfffffffff88007c7

def z614 : W := mkw 0x40004c0a08004510 0x88000981410008a2 0x00000c0e00000000 0x00000181c0000000

def z615 : W := mkw 0x0000010077efbae9 0x200000200efdf75d 0x200000003ffffffe 0x2400000007ffffff

def z616 : W := mkw 0x582c581800020060 0x0b058b030000400c 0xf83e7c1e200e07ff 0xbf07cf83c401c0ff

def z617 : W := mkw 0x1800000030000000 0x0300000006000000 0x1800000038000001 0xa300000007000000

def z618 : W := mkw 0x9fd3eac580000002 0x13fa7d58b0000000 0x5fc1ffe1c0000001 0xcbf83ffc38000000

def z619 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xe0078fffc001fe3a 0x1c00f1fff8003fc7

def z620 : W := mkw 0x582c5c1a38094510 0x8b058b83470128a2 0xd83e7c1e1801c001 0x9b07cf83c3003800

def z621 : W := mkw 0x9ef78000336db001 0x13def000066db600 0x17f9800027fe3800 0xc2ff300004ffc700

def z622 : W := mkw 0x0042800000209000 0x0008500000041200 0x08c600001871c000 0x0118c000030e3800

def z623 : W := mkw 0x25c2a7e6cef0de98 0x44b854fcd9de1bd3 0xefc78fffdff1fe3b 0x7df8f1fffbfe3fc7

def z624 : W := mkw 0x031937134d866ef8 0x206326e269b0cddf 0xff3fff1fff8fffff 0xffe7ffe3fff1ffff

def z625 : W := mkw 0xdffffedf88024572 0x9bffffdbf10048ae 0xdfffffffc00007ff 0xdbfffffff80000ff

def z626 : W := mkw 0x000005220c104610 0x000000a4418208c2 0xe8c60ffe1c71c63b 0x7d18c1ffc38e38c7

def z627 : W := mkw 0x01006fa03ed00780 0x40200df407da00f0 0x40007fe03ff007c4 0x28000ffc07fe00f8

def z628 : W := mkw 0xbef78466bb7df411 0x17def08cd76fbe82 0xbfff8cee3ffff801 0xf7fff19dc7ffff00

def z629 : W := mkw 0x0000010004000200 0x0000002000800040 0x4000030004000601 0x68000060008000c0

def z630 : W := mkw 0x9eb5000000000000 0x13d6a00000000000 0x1738000000000000 0x82e7000000000000

def z631 : W := mkw 0x0211000000000000 0x0042200000000000 0x9739800000000001 0xd2e7300000000000

def z632 : W := mkw 0x20428046c020d818 0x04085008d8041b03 0xe8c78fffc001f83b 0x5d18f1fff8003f07

def z633 : W := mkw 0x0000010044000a08 0x0000002008800141 0x00018301c4003800 0x4000306038800700

def z634 : W := mkw 0x0108331145862ae8 0x2021066228b0c55d 0x60007311e78e3ffe 0x2c000e623cf1c7ff

def z635 : W := mkw 0x40085c1a380b4570 0x88010b83470168ae 0x60007c1e380fc7fe 0x2c000f83c701f8ff

def z636 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0x08c78fefdc71f800 0x4118f1fdfb8e3f00

def z637 : W := mkw 0x20428044c0209808 0x0408500898041301 0x00018001c0003800 0x0000300038000700

def z638 : W := mkw 0xdeffd81800000000 0x1bdffb0300000000 0xdffffc1e00000001 0xdbffff83c0000000

def z639 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0x20c183e1dc71fe3a 0x6418307c3b8e3fc7

def z640 : W := mkw 0x9de6efa03ef99781 0x53bcddf407df32f0 0x5fc67fe03ff1c7c5 0xebf8cffc07fe38f8

def z641 : W := mkw 0x1c80000032400000 0x0390000006480000 0x1700000023800000 0x82e0000004700000

def z642 : W := mkw 0x1f997b9177c62be8 0x63f32f722ef8c57d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z643 : W := mkw 0x582c5c1838000500 0x0b058b83070000a0 0xd83e7c1e380007c5 0xbb07cf83c70000f8

def z644 : W := mkw 0x7866cd6efc39df18 0x8f0cd9addf873be3 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z645 : W := mkw 0x9ef784023b6df411 0x13def080476dbe82 0xffff8c1e3ffffe3b 0xfffff183c7ffffc7

def z646 : W := mkw 0x03193211018620e0 0x206326422030c41c 0xb739f000278e39c5 0xf6e73e0004f1c738

def z647 : W := mkw 0x9a778000312db001 0x134ef0000625b600 0xb83f8000380ff801 0xb707f0000701ff00

def z648 : W := mkw 0x9ff7a30037edb281 0x13fef46006fdb650 0xfffff3003fffffc5 0xfffffe6007fffff8

def z649 : W := mkw 0x9ff7ea8033edb181 0x53fefd50067db630 0xbffff0003ffff9c5 0xf7fffe0007ffff38

def z650 : W := mkw 0x1c804da03ed00780 0x439009b407da00f0 0x08c00ce03ff007c4 0x2118019c07fe00f8

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001800004003801 0x7400300000800700

def z652 : W := mkw 0x035bb31145a6bae8 0x206b766228b4d75d 0xfffff311ffffffff 0xfffffe623fffffff

def z653 : W := mkw 0x0042844688004410 0x00085088d1000882 0xe8c78fffd801c63b 0x7d18f1fffb0038c7

def z654 : W := mkw 0x0100220000000000 0x0020044000000000 0x5700730000000001 0xcae00e6000000000

def z655 : W := mkw 0xdffffffdffd62fea 0x7bffffffbffac5fd 0xfffffffffffe3fff 0xffffffffffffc7ff

def z656 : W := mkw 0x20428046c020d818 0x04085008d8041b03 0xa8c7801fdc71f83b 0x7518f003fb8e3f07

def z657 : W := mkw 0x8791228100000002 0x10f2245020000000 0x0700000000000000 0x00e0000000000000

def z658 : W := mkw 0x5b3d7b19758f2be8 0xab67af632eb1e57d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z659 : W := mkw 0xdfffffffbedb47f2 0xdbfffffff7db68fe 0xffffffffffffc7ff 0xfffffffffffff8ff

def z660 : W := mkw 0x8253804580000002 0x104a7008b0000000 0x00018001c0000000 0x0000300038000000

def z661 : W := mkw 0x9eff9010336fb061 0x13dff202066df60c 0xfffff0103fffffff 0xfffffe0207ffffff

def z662 : W := mkw 0xfce6cdeecc30de1a 0x1f9cd9bdd9861bc3 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z663 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0x50387c1e200e07fe 0x8a070f83c401c0ff

def z664 : W := mkw 0x0000040008000400 0x0000008001000080 0x48000c0018000601 0x29000180030000c0

def z665 : W := mkw 0x000005203ed00780 0x400000a407da00f0 0x48c00fe03ff007c5 0x691801fc07fe00f8

def z666 : W := mkw 0x9fffb31145862ae8 0x33fff66228b0c55d 0xfffff311e78e3fff 0xfffffe623cf1c7ff

def z667 : W := mkw 0x048000a002500000 0x40900014004a0000 0x00c000e000700000 0x0018001c000e0000

def z668 : W := mkw 0x82778000012db001 0x104ef0000025b600 0xa8ff80001c7ff801 0x751ff000038fff00

def z669 : W := mkw 0x1c800000336db001 0x03900000066db600 0x3fc000003ffff801 0xe7f8000007ffff00

def z670 : W := mkw 0xdceedcdeb80b4572 0x9b9ddb9bd70168ae 0xf8fe7cfe380fc7ff 0xbf1fcf9fc701f8ff

def z671 : W := mkw 0xc27f905f800b4072 0x984ff20bf001680e 0xa03f801fc00fc03a 0x1407f003f801f807

def z672 : W := mkw 0x1d806e803ac00580 0x43b00dd0075800b0 0x5f007c003b8007c5 0xabe00f80077000f8

def z673 : W := mkw 0x786edc5ef82bdd78 0x8f0ddb8bdf057baf 0xf83ffc1ff80fffff 0xbf07ff83ff01ffff

def z674 : W := mkw 0x3842cd66fc30df18 0x070859acdf861be3 0xf8c7fffffc71ffff 0xff18ffffff8e3fff

def z675 : W := mkw 0x86d38000336db001 0x10da7000066db600 0x27c180003ffff800 0x64f8300007ffff00

def z676 : W := mkw 0x58244c0a38094510 0x8b048981470128a2 0xe8060c1e1801c63b 0x3d00c183c30038c7

def z677 : W := mkw 0x9ef785203ffdb781 0x53def0a407ffb6f0 0xbfff80003fffffc5 0xf7fff00007fffff8

def z678 : W := mkw 0x582c5d3a3edb47f0 0xcb058ba747db68fe 0xf83e7c1e3fffc7ff 0xbf07cf83c7fff8ff

def z679 : W := mkw 0x0311230145842a88 0x2062246028b08551 0xe7018311c7803e3b 0x7ce0306238f007c7

def z680 : W := mkw 0x9ff7a30177edba89 0x33fef4602efdb751 0xbfff8301fffff801 0xf7fff0603fffff00

def z681 : W := mkw 0x18244c0038090500 0x03048980070120a0 0xf83e7c00380fc7c5 0xbf07cf800701f8f8

def z682 : W := mkw 0x5dac7fb83edb07e0 0xcbb58ff707db60fc 0x5ff87fe03ffe07c5 0xebff0ffc07ffc0f8

def z683 : W := mkw 0xdce6cc0a3a69d511 0x9b9cd981474d3aa2 0x08c60c0e1871c000 0x0118c181c30e3800

def z684 : W := mkw 0x0100220000800080 0x0020044000100010 0x17007000238001c4 0x82e00e0004700038

def z685 : W := mkw 0x000005027d8f6ff8 0xa00000a04fb1edff 0x200000003f8ffffe 0x2400000007f1ffff

def z686 : W := mkw 0xdceed8dc80000002 0x1b9ddb1b90000000 0xd8fe7cfe00000001 0x9b1fcf9fc0000000

def z687 : W := mkw 0x18004c02380b4570 0x83000980470168ae 0x78007c00380fc7ff 0xaf000f800701f8ff

def z688 : W := mkw 0x1d887fb03ed207e0 0x43b10ff607da40fc 0xfff87ff03ffe07ff 0xffff0ffe07ffc0ff

def z689 : W := mkw 0x204a9576cc32de78 0x040952aed9865bcf 0xf8fffffffc7fffff 0xff1fffffff8fffff

def z690 : W := mkw 0x5dac7a9800000000 0x0bb58f5300000000 0xdffe7ffe00000001 0xdbffcfffc0000000

def z691 : W := mkw 0x60085d7ecc124f78 0x8c010bafd98249ef 0x40007fffc00007fe 0x08000ffff80000ff

def z692 : W := mkw 0x3dc2efe4fef09f88 0x47b85dfc9fde13f1 0x5fc1ffe1fff03fc5 0xebf83ffc3ffe07f8

def z693 : W := mkw 0x0108331144820ae8 0x202106622890415d 0xf0387311e00e07ff 0xbe070e623c01c0ff

def z694 : W := mkw 0xfffffeff8830d412 0x1fffffdff1061a82 0xdfffffffd871c001 0xdbfffffffb0e3800

def z695 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xb73f8000238ff800 0x96e7f0000471ff00

def z696 : W := mkw 0x87dbb31147e6bae9 0x30fb766228fcd75d 0xf7f9f311e7fe3fff 0xfeff3e623cffc7ff

def z697 : W := mkw 0x9fd3efa03ff4b781 0x53fa7df407fe96f0 0x5fc1ffe03ff03fc5 0xebf83ffc07fe07f8

def z698 : W := mkw 0x9eff9011736fb869 0x33dff2022e6df70d 0xbfff8011fffff83b 0xf7fff0023fffff07

def z699 : W := mkw 0x0000010045842a88 0x2000002008b08551 0x0000000007803800 0x0000000000f00700

def z700 : W := mkw 0x58244c0a38094510 0x8b048981470128a2 0xb83e0c0e380fc001 0xb707c181c701f800

def z701 : W := mkw 0x0211010045042a08 0x0042202008a08541 0xf7398311e78e3e3b 0xfee730623cf1c7c7

def z702 : W := mkw 0x3dc2efe6cc30de18 0x07b85dfcd9861bc3 0xffc7ffffdc71fe3b 0xfff8fffffb8e3fc7

def z703 : W := mkw 0x20428566cc104e18 0x040850acd98209c3 0xc8c78fffc000063b 0x5918f1fff80000c7

def z704 : W := mkw 0xdffffedfb8094512 0x9bffffdbf70128a2 0xdfffffffd801c001 0xdbfffffffb003800

def z705 : W := mkw 0x41087ffd8c900782 0x48210fffb19200f0 0x40007fffc00007c4 0x08000ffff80000f8

def z706 : W := mkw 0x1f997fb13ed00780 0x43f32ff627da00f0 0xdff9fff1fff007c5 0xfbff3ffe3ffe00f8

def z707 : W := mkw 0x031933b145962ae8 0x6063267628b2c55d 0xf739f3f1e78e3fff 0xfee73e7e3cf1c7ff

def z708 : W := mkw 0x0108331144820ae8 0x202106622890415d 0x00007000000007fe 0x00000e00000000ff

def z709 : W := mkw 0x43197add80000002 0x08632f5bb0000000 0xc039ffffc0000000 0x18073ffff8000000

def z710 : W := mkw 0x3dc2eac6f2e0d998 0x47b85d58de5c1b33 0xb707f01fe381f9fe 0x96e0fe03fc703f3f

def z711 : W := mkw 0x210837334c924ef8 0x242106e6699249df 0x40007311c00007fe 0x08000e62380000ff

def z712 : W := mkw 0xdffffaddb2490003 0x1bffff5bb6492000 0xdfffffffc0000001 0xdbfffffff8000000

def z713 : W := mkw 0x200005224d3dfe19 0x040000a449a7bfc3 0x200000001c7ffe3a 0x24000000038fffc7

def z714 : W := mkw 0x0000004480000000 0x0000000890000000 0xc8060fffc0000001 0x1900c1fff8000000

def z715 : W := mkw 0x2142a346c4a0da98 0x04285468d8941b53 0xf707f31fe781ffff 0xfee0fe63fcf03fff

def z716 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x000000001871c63a 0x00000000030e38c7

def z717 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0xa00180001c71fe3b 0x74003000038e3fc7

def z718 : W := mkw 0x8377efa00dbdb781 0x506efdf401b7b6f0 0xe03fffe0000fffc4 0x1c07fffc0001fff8

def z719 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x5ffe7fffc0000000 0x8bffcffff8000000

def z720 : W := mkw 0xa7d3a3e5c5b4ba8a 0x34fa747cb8b69751 0x07c183e1c7f03800 0x40f8307c38fe0700

def z721 : W := mkw 0xdffffaddb36db003 0x1bffff5bb66db600 0xdfffffffe7fe3801 0xdbfffffffcffc700

def z722 : W := mkw 0xdeffdc5ebb6ff571 0x9bdffb8bd76dfeae 0xffffffffffffffff 0xffffffffffffffff

def z723 : W := mkw 0xdef7804cb36db003 0x1bdef009966db600 0xbfff800e3ffff801 0xf7fff001c7ffff00

def z724 : W := mkw 0xbef785227ffffef9 0x37def0a44fffffdf 0xbfff80003fffffff 0xf7fff00007ffffff

def z725 : W := mkw 0x45ac33ba06db42f0 0xc8b5867740db685e 0xa7fe03fe07ffc03a 0x54ffc07fc0fff807

def z726 : W := mkw 0xdffffadd83442003 0x1bffff5bb0688400 0xdfffffffc3800001 0xdbfffffff8700000

def z727 : W := mkw 0xc6dbdc1a0b66f571 0x98db7b83416cdeae 0x47c1fc1e07f03ffe 0x48f83f83c0fe07ff

def z728 : W := mkw 0x1d806a8032c00180 0x43b00d5006580030 0x5fc07fe03ff001c5 0xebf80ffc07fe0038

def z729 : W := mkw 0x9ef7c800336db001 0x13def900066db600 0xfffffc003ffff801 0xffffff8007ffff00

def z730 : W := mkw 0x9eb50000336db001 0x13d6a000066db600 0xbf3e00003ffff801 0xb7e7c00007ffff00

def z731 : W := mkw 0x3d806fa27ed04f98 0x47b00df44fda09f3 0x5fc07fe03ff007ff 0xebf80ffc07fe00ff

def z732 : W := mkw 0x582c101a300b4070 0x8b0582034601680e 0xf83e701e380fc7ff 0xbf07ce03c701f8ff

def z733 : W := mkw 0x204285224c30de18 0x040850a449861bc3 0x20c180001c71fe3a 0x64183000038e3fc7

def z734 : W := mkw 0x9eb50000336db001 0x13d6a000066db600 0xb73980003ffff801 0xf6e7300007ffff00

def z735 : W := mkw 0x84c280c480000002 0x1098501890000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z736 : W := mkw 0x0008101200024070 0x000102024000480e 0xf03e701e200fc7ff 0xbe07ce03c401f8ff

def z737 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0x5739f311e78e3ffe 0xcae73e623cf1c7ff

def z738 : W := mkw 0x5da46fa83ed90780 0xcbb48df507db20f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z739 : W := mkw 0x5b356f0b7d8d6f98 0xab66ade16fb1adf3 0x0f078f0fdf81f800 0x41e0f1e1fbf03f00

def z740 : W := mkw 0xdfdbfadd80000002 0x1bfb7f5bb0000000 0x5fc1ffffc0000001 0xcbf83ffff8000000

def z741 : W := mkw 0xdffffaddb36fb063 0x1bffff5bb66df60c 0xffffffffffffffff 0xffffffffffffffff

def z742 : W := mkw 0x412c7add80000002 0x08258f5bb0000000 0xc03e7fffc0000000 0x1807cffff8000000

def z743 : W := mkw 0x0042804480000000 0x0008500890000000 0xc0078fffc0000000 0x1800f1fff8000000

def z744 : W := mkw 0x582c581a300b4170 0x8b058b034601682e 0xf03e701e200fc7ff 0xbe07ce03c401f8ff

def z745 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x57c07fe027f007c4 0xcaf80ffc04fe00f8

def z746 : W := mkw 0x87d3a6c7b80b4572 0x90fa74d8f70168ae 0x27c183e1f80fc7fe 0x64f8307c3f01f8ff

def z747 : W := mkw 0x5b7ffa5d80000000 0x0b6fff4bb0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z748 : W := mkw 0xdffffadd81842082 0x3bffff5bb0308410 0xdfffffffc3800001 0xdbfffffff8700000

def z749 : W := mkw 0xdffffaddb18f21e2 0xbbffff5bb631e43c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z750 : W := mkw 0xdffffadd8124b003 0x1bffff5bb0249600 0xdfffffffc0003801 0xdbfffffff8000700

def z751 : W := mkw 0x9ef78044b36db001 0x13def008966db600 0xbfff801ffffff801 0xf7fff003ffffff00

def z752 : W := mkw 0x1e995cb17b562d68 0x63d32b962f6ac5ad 0xa8f98cf1d87e383a 0x151f319e3b0fc707

def z753 : W := mkw 0x406e905c80000000 0x080dd20b90000000 0xc8ff8fffc0000001 0x591ff1fff8000000

def z754 : W := mkw 0x182c1412380b4470 0x030582824701688e 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z755 : W := mkw 0x200005224ef0de98 0x440000a449de1bd3 0x200000001ff1fe3a 0x2400000003fe3fc7

def z756 : W := mkw 0x9ef78044b36db001 0x13def008966db600 0xbfff83e1fffff801 0xf7fff07c3fffff00

def z757 : W := mkw 0x9deeb31176eb9ae9 0x33bdd6622edd735d 0x48c67311d871c7fe 0x0918ce623b0e38ff

def z758 : W := mkw 0x4042c8cc80000002 0x0808591990000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z759 : W := mkw 0x0042804480209000 0x0008500890041200 0xc8c78fffd871c001 0x5918f1fffb0e3800

def z760 : W := mkw 0x786ed97cf43b9b68 0x8f0ddb2f9e87736d 0x10f9f3e1e47e39c4 0xc21f3e7c3c8fc738

def z761 : W := mkw 0x235bb67789b6f4f0 0x246b76cef136de9e 0x1ffe7cee3bffc1c4 0x83ffcf9dc77ff838

def z762 : W := mkw 0xdffffadd818620e2 0x3bffff5bb030c41c 0xffffffffe38e07ff 0xfffffffffc71c0ff

def z763 : W := mkw 0x05806fa00ed00780 0x40b00df401da00f0 0x4fc07fe01ff007c5 0x69f80ffc03fe00f8

def z764 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xff3fff1fe78e3fff 0xffe7ffe3fcf1c7ff

def z765 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0x583e7c1e380fc7fe 0x8b07cf83c701f8ff

def z766 : W := mkw 0xdffffadd81042002 0x1bffff5bb0208400 0xdfffffffe38e0001 0xdbfffffffc71c000

def z767 : W := mkw 0x1d806fa23ed04790 0x43b00df447da08f2 0x5fc67fee3ff1c7c5 0xebf8cffdc7fe38f8

def z768 : W := mkw 0x1ce6800032699000 0x039cd000064d3200 0xbfff80003ffff801 0xf7fff00007ffff00

def z769 : W := mkw 0x5dac7add80000002 0x0bb58f5bb0000000 0xdffe7fffc0000001 0xdbffcffff8000000

def z770 : W := mkw 0x021915314d162e68 0x204322a629a2c5cd 0xe8f98ff1dc7e3e3b 0x7d1f31fe3b8fc7c7

def z771 : W := mkw 0x41087fbb4c924ff8 0xe8210ff7699249ff 0x40007fffc00007fe 0x08000ffff80000ff

def z772 : W := mkw 0x1d806ea03ad00580 0x43b00dd4075a00b0 0x5fc07ce03bf007c5 0xabf80f9c077e00f8

def z773 : W := mkw 0x61087f7fcc924ff8 0xac210feff99249ff 0x40007fffc00007fe 0x08000ffff80000ff

def z774 : W := mkw 0x02110000336db001 0x00422000066db600 0x373800003ffff800 0xa6e7000007ffff00

def z775 : W := mkw 0xffbd7fbb4c30de1a 0x1ff7aff769861bc3 0x373870001c71fe3a 0xa6e70e00038e3fc7

def z776 : W := mkw 0x41087addb36db003 0x08210f5bb66db600 0x60007ffffffff800 0x2c000fffffffff00

def z777 : W := mkw 0x20428046c020d818 0x04085008d8041b03 0xe8c78fffdc71f83b 0x7d18f1fffb8e3f07

def z778 : W := mkw 0x0000004480000000 0x0000000890000000 0x48c00fffc0000001 0x491801fff8000000

def z779 : W := mkw 0x1d806ba036d00380 0x43b00d7406da0070 0x5fc07fe027f001c5 0xcbf80ffc04fe0038

def z780 : W := mkw 0xbef785227f7fff79 0x97def0a44fefffef 0xbfff80003fffffff 0xf7fff00007ffffff

def z781 : W := mkw 0x9fffb25580000000 0x13fff64ab0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z782 : W := mkw 0x200005227c39df18 0x840000a44f873be3 0x200000001c71fe3a 0x24000000038e3fc7

def z783 : W := mkw 0xdffffaddb34d2003 0x1bffff5bb669a400 0xdffffffffffe0001 0xfbffffffffffc000

def z784 : W := mkw 0x0219111045062a68 0x0043222208a0c54d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z785 : W := mkw 0x00428044b36db001 0x00085008966db600 0xe8c78ffffffff801 0x7d18f1ffffffff00

def z786 : W := mkw 0xdeffd8dd80000002 0x1bdffb1bb0000000 0xc8ff8fffc0000001 0x591ff1fff8000000

def z787 : W := mkw 0x5fbd7a9900000000 0x0bf7af5320000000 0xdfffffffc0000001 0xdbfffffff8000000

def z788 : W := mkw 0x9ef780c4b36db003 0x13def018966db600 0xbfff80e03ffff801 0xf7fff01c07ffff00

def z789 : W := mkw 0x5cac5c1a380b4570 0x8b958b83470168ae 0xfffe7c1e380fc7ff 0xffffcf83c701f8ff

def z790 : W := mkw 0x586ed85cb0299000 0x0b0ddb0b96053200 0xf8fffffffc7ff801 0xff1fffffff8fff00

def z791 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xf83fff1ff80fc7ff 0xff07ffe3ff01f8ff

def z792 : W := mkw 0xc27f905dc12fb86b 0x384ff20bb825f70d 0xa03f801fc00ff83a 0x1407f003f801ff07

def z793 : W := mkw 0xdce6c8cc80000002 0x1b9cd91990000000 0x48c60fffc0000000 0x0918c1fff8000000

def z794 : W := mkw 0x86d3804480000000 0x10da700890000000 0xcfc78fffc0000001 0x59f8f1fff8000000

def z795 : W := mkw 0xdffffaddb3c621e2 0x7bffff5bb678c43c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z796 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0x3739f301e78e3ffe 0xe6e73e603cf1c7ff

def z797 : W := mkw 0x9ef780000124b000 0x13def00000249600 0xbfff80003ffff801 0xf7fff00007ffff00

def z798 : W := mkw 0x1a350000336db001 0x0346a000066db600 0xbf3f80003ffff801 0xf7e7f00007ffff00

def z799 : W := mkw 0xbce685227e79de19 0x179cd0a44fcf3bc3 0x28c600001c71fe3a 0x2518c000038e3fc7

def z800 : W := mkw 0x0042804480209000 0x0008500890041200 0xe8c78fffc001f801 0x5d18f1fff8003f00

def z801 : W := mkw 0x9da46fa03ed90781 0x53b48df407db20f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z802 : W := mkw 0x058023a006d00280 0x40b0047400da0050 0x17c073e027f001c4 0xc2f80e7c04fe0038

def z803 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xffffffffc000063b 0xfffffffff80000c7

def z804 : W := mkw 0xdffffaddb00b0162 0x9bffff5bb601602c 0xffffffffe00e07ff 0xfffffffffc01c0ff

def z805 : W := mkw 0x402c101a000b4070 0x880582034001680e 0xe03e701e000fc7fe 0x1c07ce03c001f8ff

def z806 : W := mkw 0x200005227efbdff8 0xc40000a44fdf7bff 0x200000003ffffffe 0x2400000007ffffff

def z807 : W := mkw 0x9ff7a2c580000002 0x13fef458b0000000 0xdfff8fffc0000001 0xdbfff1fff8000000

def z808 : W := mkw 0xdfbd7addb34d2003 0x1bf7af5bb669a400 0x57387fffe38e0000 0x8ae70ffffc71c000

def z809 : W := mkw 0x0353a24580000000 0x006a7448b0000000 0xcfc78fffc0000001 0x59f8f1fff8000000

def z810 : W := mkw 0xddeefadd80000002 0x1bbddf5bb0000000 0x5fc67fffc0000001 0xcbf8cffff8000000

def z811 : W := mkw 0x01006fa00c900780 0x40200df4019200f0 0x00007000000007c4 0x00000e00000000f8

def z812 : W := mkw 0x1c80000032400000 0x0390000006480000 0x5fc00fe03ff00001 0xebf801fc07fe0000

def z813 : W := mkw 0x0142a2c580000002 0x00285458b0000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z814 : W := mkw 0x5cac5c9a380b4570 0x8b958b93470168ae 0xf8fe7cfe380fc7ff 0xbf1fcf9fc701f8ff

def z815 : W := mkw 0x0108331044820ae8 0x002106620890415d 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z816 : W := mkw 0xc27f957dbed00782 0x584ff2afb7da00f0 0x803f801ffff007c4 0x3007f003fffe00f8

def z817 : W := mkw 0x0100232004900280 0x0020046400920050 0x57c073e027f007c5 0xeaf80e7c04fe00f8

def z818 : W := mkw 0x86d380448364b001 0x10da7008906c9600 0x07c183e1c7f03800 0x40f8307c38fe0700

def z819 : W := mkw 0xdfbd7add80000002 0x1bf7af5bb0000000 0xd739ffffc0000001 0xdae73ffff8000000

def z820 : W := mkw 0x200005224d34fe18 0x040000a449a69fc3 0x200000003ffffe3a 0x2400000007ffffc7

def z821 : W := mkw 0x582c5c1a080b4570 0x8b058b83410168ae 0xf83e7c1e000fc7ff 0x9f07cf83c001f8ff

def z822 : W := mkw 0x1d806fa00ed00780 0x43b00df401da00f0 0x5fc07fe007f007c5 0xcbf80ffc00fe00f8

def z823 : W := mkw 0x00428144c4209a08 0x0008502898841341 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z824 : W := mkw 0x1d806b8036c00280 0x03b00d7006d80050 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z825 : W := mkw 0xdce6ccceba69d513 0x9b9cd999d74d3aa2 0x08c60cee1871c000 0x0118c19dc30e3800

def z826 : W := mkw 0x200005224c3bde78 0x840000a449877bcf 0x200000001c7ffe3a 0x24000000038fffc7

def z827 : W := mkw 0x200005227ff6fff8 0x640000a44ffedfff 0x200000003ffffffe 0x2400000007ffffff

def z828 : W := mkw 0x025b905580000000 0x004b720ab0000000 0xc8ff8fffc0000001 0x591ff1fff8000000

def z829 : W := mkw 0xdfbd7a99334f2163 0x9bf7af532669e42c 0x17387000238e01c4 0x82e70e000471c038

def z830 : W := mkw 0xdce6c9ccc5862aea 0x3b9cd93998b0c55d 0x28c60cee278e3ffe 0x2518c19dc4f1c7ff

def z831 : W := mkw 0x021100000124b000 0x0042200000249600 0xb73980003ffff801 0xf6e7300007ffff00

def z832 : W := mkw 0xc37ffadd812db003 0x186fff5bb025b600 0xe03fffffc00ff800 0x1c07fffff801ff00

def z833 : W := mkw 0x9ff7efe4bffdb781 0x53fefdfc97ffb6f0 0xffffffffffffffc5 0xfffffffffffffff8

def z834 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0xdfc67ffe3ff007c5 0xfbf8cfffc7fe00f8

def z835 : W := mkw 0x86d380000364b001 0x10da7000006c9600 0xbfff80003ffff801 0xf7fff00007ffff00

def z836 : W := mkw 0x0319325580000000 0x0063264ab0000000 0xd739ffffc0000001 0xdae73ffff8000000

def z837 : W := mkw 0x200005224f74fe19 0x040000a449ee9fc3 0x200000001ff1fe3a 0x2400000003fe3fc7

def z838 : W := mkw 0xdff7eacdb36db003 0x1bfefd59b66db600 0xbfff8feffffff801 0xf7fff1fdffffff00

def z839 : W := mkw 0x87d3a3c5c7e4ba8b 0x30fa7478b8fc9751 0x07c183e1c7f03800 0x40f8307c38fe0700

def z840 : W := mkw 0xbeb505227f7dfe19 0x17d6a0a44fefbfc3 0x373800003ffffe3a 0xa6e7000007ffffc7

def z841 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x5fc07fe03bf007c4 0x8bf80ffc077e00f8

def z842 : W := mkw 0x3d806fa27ef0df98 0x47b00df44fde1bf3 0x370070003ff1fffe 0xa6e00e0007fe3fff

def z843 : W := mkw 0xbeb50566ff5d6e19 0x17d6a0acdfebadc3 0x57380fffe38e063a 0x8ae701fffc71c0c7

def z844 : W := mkw 0x1d806fa07ed00f88 0x43b00df40fda01f1 0x7fc07fe03ff03fff 0xeff80ffc07fe07ff

def z845 : W := mkw 0x1d806fa07ed00f88 0x43b00df40fda01f1 0x5fc1ffe1fff03fc5 0xebf83ffc3ffe07f8

def z846 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xf8fe7ffe380fc7ff 0xff1fcfffc701f8ff

def z847 : W := mkw 0x582c585c80000000 0x0b058b0b90000000 0xd83e7fffc0000001 0x9b07cffff8000000

def z848 : W := mkw 0x200005224d36fe78 0x240000a449a6dfcf 0x200000001c7ffe3a 0x24000000038fffc7

def z849 : W := mkw 0x02538000336db001 0x004a7000066db600 0xbfff80003ffff801 0xf7fff00007ffff00

def z850 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xf8ff8ffffc7ffe3b 0xff1ff1ffff8fffc7

def z851 : W := mkw 0x058027a00ed00680 0x40b004f401da00d0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z852 : W := mkw 0xdff7eacdb36db003 0x1bfefd59b66db600 0x0fc78fefdff1f800 0x41f8f1fdfbfe3f00

def z853 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xf8fe7c1e3c7fc7ff 0xff1fcf83c78ff8ff

def z854 : W := mkw 0x5cac5c1a3a4b4570 0x8b958b83474968ae 0xff3e7c1e3b8fc7ff 0xbfe7cf83c771f8ff

def z855 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x17c073e03ff007c4 0xe2f80e7c07fe00f8

def z856 : W := mkw 0xdffffaddb3cf20e3 0x3bffff5bb679e41c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z857 : W := mkw 0x5deefadc80000000 0x0bbddf5b90000000 0xdfffffffc0000001 0xdbfffffff8000000

def z858 : W := mkw 0x402c5c1a080b4570 0x88058b83410168ae 0xe83e7c1e180fc7ff 0x3d07cf83c301f8ff

def z859 : W := mkw 0xdffffadd80209002 0x1bffff5bb0041200 0xffffffffc001f801 0xdffffffff8003f00

def z860 : W := mkw 0x21087ff7cc924ff8 0x64210ffef99249ff 0x40007fffc00007fe 0x08000ffff80000ff

def z861 : W := mkw 0x010027203ed00780 0x402004e407da00f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z862 : W := mkw 0xdeff905d80000002 0x1bdff20bb0000000 0xdfff8fffc0000001 0xdbfff1fff8000000

def z863 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xffff8fe03ffff801 0xfffff1fc07ffff00

def z864 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0xa80600001c71fe3b 0x3500c000038e3fc7

def z865 : W := mkw 0x9ce6804480000000 0x139cd00890000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z866 : W := mkw 0x03193211418628e8 0x206326422830c51d 0xf739f011e38e3fff 0xbee73e023c71c7ff

def z867 : W := mkw 0xdffffaddb2699003 0x1bffff5bb64d3200 0xffffffffdc71f801 0xfffffffffb8e3f00

def z868 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x1fc07ce03ff007c4 0xa3f80f9c07fe00f8

def z869 : W := mkw 0x40085c1a08024570 0x88010b83410048ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z870 : W := mkw 0x40085c1a08024570 0x88010b83410048ae 0x00007000000007fe 0x00000e00000000ff

def z871 : W := mkw 0x004a905480000000 0x0009520a90000000 0xd8ffffffc0000001 0xdb1ffffff8000000

def z872 : W := mkw 0x200005227f7fff79 0x840000a44fefffef 0x200000003ffffffe 0x2400000007ffffff

def z873 : W := mkw 0x200005224cb0de98 0x040000a449961bd3 0x200000003ff1fffe 0x2400000007fe3fff

def z874 : W := mkw 0x1d806fa17ed00f88 0x63b00df42fda01f1 0x5fc07fe1fff007c5 0xebf80ffc3ffe00f8

def z875 : W := mkw 0x1d806ba036d00380 0x43b00d7406da0070 0x1fc073e03ff001c5 0xe3f80e7c07fe0038

def z876 : W := mkw 0x41087add80000002 0x08210f5bb0000000 0xc8067fffc0000001 0x1900cffff8000000

def z877 : W := mkw 0xdff7eacd80000002 0x1bfefd59b0000000 0x5fc7ffefc0000001 0xcbf8fffdf8000000

def z878 : W := mkw 0xdffffaddb2490002 0x1bffff5bb6492000 0xffffffffffffc001 0xfffffffffffff800

def z879 : W := mkw 0xdffffadd81062062 0x1bffff5bb020c40c 0xffffffffe78e3fff 0xfffffffffcf1c7ff

def z880 : W := mkw 0xc066804c80000002 0x180cd00990000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z881 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xe83e7c1e180fc7fe 0x1d07cf83c301f8ff

def z882 : W := mkw 0x1d8027203ed00680 0x03b004e407da00d0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z883 : W := mkw 0x9ce68044b2699001 0x139cd008964d3200 0xc8c78fffd871c001 0x5918f1fffb0e3800

def z884 : W := mkw 0x86f78000336db001 0x10def000066db600 0xa7ff80003ffff800 0x74fff00007ffff00

def z885 : W := mkw 0xbef785224c30de18 0x17def0a449861bc3 0xbfff80001c71fe3b 0xf7fff000038e3fc7

def z886 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0xffc1ffe03ff03fc5 0xfff83ffc07fe07f8

def z887 : W := mkw 0x058023a006d00280 0x40b0047400da0050 0x47c073e007f007c4 0x48f80e7c00fe00f8

def z888 : W := mkw 0x9ef78045b36db003 0x13def008b66db600 0xbfff8001fffff801 0xf7fff0003fffff00

def z889 : W := mkw 0xdef7c8ccb36db003 0x1bdef919966db600 0xffff8ffffffff801 0xfffff1ffffffff00

def z890 : W := mkw 0x0253804480000000 0x004a700890000000 0xdfff8fffc0000001 0xdbfff1fff8000000

def z891 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xf03e7c1e200fc7fe 0x9e07cf83c401f8ff

def z892 : W := mkw 0x010022c580000002 0x00200458b0000000 0x40000fffc0000000 0x080001fff8000000

def z893 : W := mkw 0x20428566ccb0df98 0x440850acd9961bf3 0xe8c78fffdc71ffff 0x7d18f1fffb8e3fff

def z894 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0xe00000101c71fe3b 0x3c000002038e3fc7

def z895 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0xdfc1fff1fff007c5 0xfbf83ffe3ffe00f8

def z896 : W := mkw 0x004284468820d410 0x00085088d1041a82 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z897 : W := mkw 0x5d806faa3ed04790 0xcbb00df547da08f2 0x5fc07fee3ff007c5 0xebf80ffdc7fe00f8

def z898 : W := mkw 0x1cc28044b2400000 0x0398500896480000 0xdfc78ffffff00001 0xfbf8f1fffffe0000

def z899 : W := mkw 0xdffffaddb34f2163 0x9bffff5bb669e42c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z900 : W := mkw 0xdffffaddb0299002 0x1bffff5bb6053200 0xfffffffffc7ff801 0xffffffffff8fff00

def z901 : W := mkw 0x200005224c104e18 0x040000a4498209c3 0x2000000004003e3a 0x24000000008007c7

def z902 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xffffffffd801c001 0xfffffffffb003800

def z903 : W := mkw 0xdff7eacd80000002 0x1bfefd59b0000000 0xcfc78fffc0000001 0x59f8f1fff8000000

def z904 : W := mkw 0x200005224cb0df98 0x440000a449961bf3 0x200000001c71fffe 0x24000000038e3fff

def z905 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0xffc67fe03ff1c7c5 0xfff8cffc07fe38f8

def z906 : W := mkw 0xc7dbfadd8364b003 0x18fb7f5bb06c9600 0x47c1ffffc7f03800 0x48f83ffff8fe0700

def z907 : W := mkw 0xdffffadd8124b002 0x1bffff5bb0249600 0xfffffffffffff801 0xffffffffffffff00

def z908 : W := mkw 0x05806fa00ed00780 0x40b00df401da00f0 0x57c07fe027f007c5 0xeaf80ffc04fe00f8

def z909 : W := mkw 0x9ef7c880336db101 0x53def910066db620 0xbfff80003ffff801 0xf7fff00007ffff00

def z910 : W := mkw 0x592c7add80000002 0x0b258f5bb0000000 0x48067fffc0000000 0x0900cffff8000000

def z911 : W := mkw 0x18244c0238094510 0x03048980470128a2 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z912 : W := mkw 0x9ff7eac4b36db001 0x13fefd58966db600 0xfffffffffffff801 0xffffffffffffff00

def z913 : W := mkw 0x592c7add80000002 0x0b258f5bb0000000 0x50387fffc0000000 0x8a070ffff8000000

def z914 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x4fc7ffffc0000000 0x49f8fffff8000000

def z915 : W := mkw 0x200005224cb2def8 0x240000a449965bdf 0x200000001c71fffe 0x24000000038e3fff

def z916 : W := mkw 0xdffffadd80800182 0x5bffff5bb0100030 0xdfffffffc00001c5 0xdbfffffff8000038

def z917 : W := mkw 0xc37ffadd80000002 0x186fff5bb0000000 0xc8ffffffc0000001 0x591ffffff8000000

def z918 : W := mkw 0xdce6c8ccb2699003 0x1b9cd919964d3200 0xe8c78fffdc71f801 0x7d18f1fffb8e3f00

def z919 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xf8c7fffffc71ffff 0xff18ffffff8e3fff

def z920 : W := mkw 0x582c5c1a08024470 0x0b058b834100488e 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z921 : W := mkw 0xdffffaddb2699003 0x1bffff5bb64d3200 0xfffffffff87fc001 0xffffffffff0ff800

def z922 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xfffff0003fffffc5 0xfffffe0007fffff8

def z923 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xffff8311fffff801 0xfffff0623fffff00

def z924 : W := mkw 0x582c5c3a3a5b4570 0xcb058b87474b68ae 0xf83e7c1e387fc7ff 0xbf07cf83c70ff8ff

def z925 : W := mkw 0x582c5c1a3a4b4570 0x8b058b83474968ae 0xf83e7c1e3fffc7ff 0xbf07cf83c7fff8ff

def z926 : W := mkw 0x204285224c30de18 0x040850a449861bc3 0xa00780001c71fe3a 0x3400f000038e3fc7

def z927 : W := mkw 0x87d3a2c580000002 0x10fa7458b0000000 0x47c18fffc0000000 0x48f831fff8000000

def z928 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xf83ffc1e3c0fffff 0xff07ff83c781ffff

def z929 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xffc78ffffff1fe3b 0xfff8f1fffffe3fc7

def z930 : W := mkw 0xdffffaddb0000002 0x1bffff5bb6000000 0xdffffffff8000001 0xfbffffffff000000

def z931 : W := mkw 0x5f997add80000002 0x0bf32f5bb0000000 0xdff9ffffc0000001 0xdbff3ffff8000000

def z932 : W := mkw 0x1e910000336db001 0x03d22000066db600 0xbff980003ffff801 0xf7ff300007ffff00

def z933 : W := mkw 0x0108325580000000 0x0021064ab0000000 0x40007fffc0000000 0x08000ffff8000000

def z934 : W := mkw 0x200005224c924ef8 0x240000a4499249df 0x00000000000007fe 0x00000000000000ff

def z935 : W := mkw 0x0042804480000000 0x0008500890000000 0xe8c78fffc000063b 0x7d18f1fff80000c7

def z936 : W := mkw 0x5b3d7add80000002 0x0b67af5bb0000000 0xdf3fffffc0000001 0xdbe7fffff8000000

def z937 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xfff9fff1e78e3fff 0xffff3ffe3cf1c7ff

def z938 : W := mkw 0xc7ffb2dd80000002 0x18fff65bb0000000 0xcfff8fffc0000001 0x59fff1fff8000000

def z939 : W := mkw 0x382405227c39de18 0x070480a44f873bc3 0xb83e00003c7ffe3b 0xb707c000078fffc7

def z940 : W := mkw 0x1d806fa03ed90780 0x43b00df407db20f0 0x7fc07fe03fffc7c5 0xeff80ffc07fff8f8

def z941 : W := mkw 0xdffffadd80020062 0x1bffff5bb000400c 0xffffffffc00e003b 0xdffffffff801c007

def z942 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0x48c78fffdc71fe3a 0x4918f1fffb8e3fc7

def z943 : W := mkw 0x82778000012db001 0x104ef0000025b600 0xbfff80003ffff801 0xf7fff00007ffff00

def z944 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xb73f80003ffff800 0xb6e7f00007ffff00

def z945 : W := mkw 0x1d806fa00c900680 0x03b00df4019200d0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z946 : W := mkw 0x0042804480000000 0x0008500890000000 0x40c18fffc0000000 0x481831fff8000000

def z947 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xf739f311e38e3ffe 0x9ee73e623c71c7ff

def z948 : W := mkw 0xa7d3a3e4c7f4ba89 0x54fa747c98fe9751 0x07c183e1c7f03800 0x40f8307c38fe0700

def z949 : W := mkw 0x9eb50000336db001 0x13d6a000066db600 0x3ff800003ffff801 0xe7ff000007ffff00

def z950 : W := mkw 0x1da46fa03ed00780 0x43b48df407da00f0 0xdffe7fe03ff007c5 0xfbffcffc07fe00f8

def z951 : W := mkw 0x404ad85c80000000 0x08095b0b90000000 0xc8c7ffffc0000001 0x5918fffff8000000

def z952 : W := mkw 0x87d3a2c580000002 0x10fa7458b0000000 0x0fc78fefc0000000 0x41f8f1fdf8000000

def z953 : W := mkw 0xdffffadd80020062 0x1bffff5bb000400c 0xdfffffffc00007ff 0xdbfffffff80000ff

def z954 : W := mkw 0xdffffaddb10d2002 0x1bffff5bb621a400 0xffffffffff8ff801 0xfffffffffff1ff00

def z955 : W := mkw 0x9ef7c800336db101 0x13def900066db620 0xbffff0003ffff9c5 0xf7fffe0007ffff38

def z956 : W := mkw 0x0211000001042000 0x0042200000208400 0xf7398311e78e3801 0xfee730623cf1c700

def z957 : W := mkw 0x43197add818620e2 0x28632f5bb030c41c 0x57387fffe38e01c4 0x8ae70ffffc71c038

def z958 : W := mkw 0x200815324c32de78 0x040102a649865bcf 0xf03870103c7fffff 0xbe070e02078fffff

def z959 : W := mkw 0x0042804480209000 0x0008500890041200 0xc8c78fffc4703801 0x5918f1fff88e0700

def z960 : W := mkw 0xdffffaddb3442002 0x1bffff5bb6688400 0xfffffffffffe3801 0xffffffffffffc700

def z961 : W := mkw 0xdffffaddb2699003 0x1bffff5bb64d3200 0xdffffffffff1c001 0xfbfffffffffe3800

def z962 : W := mkw 0x414afadd80000002 0x08295f5bb0000000 0x48c67fffc0000000 0x0918cffff8000000

def z963 : W := mkw 0xc7d3eacd80000002 0x18fa7d59b0000000 0x07c18fefc0000000 0x40f831fdf8000000

def z964 : W := mkw 0x592c7addb0090002 0x0b258f5bb6012000 0xf83e7ffff80fc001 0xbf07cfffff01f800

def z965 : W := mkw 0xc37ffadd80000002 0x186fff5bb0000000 0xd73fffffc0000001 0xdae7fffff8000000

def z966 : W := mkw 0x0042804480000000 0x0008500890000000 0xc8c78fffdc700001 0x7918f1fffb8e0000

def z967 : W := mkw 0x0000004480000000 0x0000000890000000 0xc0018fffc0000001 0x580031fff8000000

def z968 : W := mkw 0xdef7c808336db001 0x1bdef901066db600 0xbfff8c0e3ffff801 0xf7fff181c7ffff00

def z969 : W := mkw 0x41087add80000002 0x08210f5bb0000000 0x48c07fffc0000001 0x49180ffff8000000

def z970 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0x383e7c0e380fc7fe 0xa707cf81c701f8ff

def z971 : W := mkw 0x1d806ea03ad00580 0x43b00dd4075a00b0 0x5fc07fe03bf001c5 0xcbf80ffc077e0038

def z972 : W := mkw 0x41087add80000002 0x08210f5bb0000000 0x57007fffc0000001 0xcae00ffff8000000

def z973 : W := mkw 0xe27f905fc126f87a 0x3c4ff20bf824df0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z974 : W := mkw 0xc37fb25d80000002 0x186ff64bb0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z975 : W := mkw 0xdffffadd80209002 0x1bffff5bb0041200 0xdfffffffd871c001 0xdbfffffffb0e3800

def z976 : W := mkw 0x1ca40000336db001 0x03948000066db600 0xbffe00003ffff801 0xf7ffc00007ffff00

def z977 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xffffffffc4003801 0xfffffffff8800700

def z978 : W := mkw 0xdceed8dc80000002 0x1b9ddb1b90000000 0xd8ffffffc0000001 0xdb1ffffff8000000

def z979 : W := mkw 0xdffffaddb3efb0e3 0x3bffff5bb67df61c 0xfffffffffffff9c5 0xffffffffffffff38

def z980 : W := mkw 0x1c804ca03a500500 0x43900994074a00a0 0x5fc07ce03ff007c5 0xebf80f9c07fe00f8

def z981 : W := mkw 0x9ef78000336db001 0x13def000066db600 0x3ffe00003ffff800 0xa7ffc00007ffff00

def z982 : W := mkw 0xdfbd7a9933cf20e3 0x3bf7af532679e41c 0x17387000238e01c4 0x82e70e000471c038

def z983 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xe8c78fffd871fe3a 0x1d18f1fffb0e3fc7

def z984 : W := mkw 0x1d806fa23ed04790 0x43b00df447da08f2 0x7fc07fe03ff1c7ff 0xeff80ffc07fe38ff

def z985 : W := mkw 0x000005227fdf6ff8 0xe00000a44ffbedff 0x200000003ffffffe 0x2400000007ffffff

def z986 : W := mkw 0xddac7add80000002 0x1bb58f5bb0000000 0x40007fffc0000000 0x08000ffff8000000

def z987 : W := mkw 0x00081412380b4570 0x80010282470168ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z988 : W := mkw 0x9fd3eac580000002 0x13fa7d58b0000000 0xdfc7ffffc0000001 0xdbf8fffff8000000

def z989 : W := mkw 0xdffffaddb3cd2183 0x5bffff5bb679a430 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z990 : W := mkw 0x82778044812db001 0x104ef0089025b600 0xa03f801fc00ff800 0x1407f003f801ff00

def z991 : W := mkw 0x627f905fc12ff878 0xac4ff20bf825ff0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z992 : W := mkw 0xdcac5c9a380b4572 0x9b958b93470168ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z993 : W := mkw 0x1da46fa03ed90780 0x43b48df407db20f0 0x5ff87fe03ffe07c5 0xebff0ffc07ffc0f8

def z994 : W := mkw 0x402c141a080b4470 0x880582834101688e 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z995 : W := mkw 0x0042804480000000 0x0008500890000000 0xe8c78fffc4003801 0x7d18f1fff8800700

def z996 : W := mkw 0xc7997add80000002 0x18f32f5bb0000000 0x47007fffc0000000 0x08e00ffff8000000

def z997 : W := mkw 0x435bfadd80000002 0x086b7f5bb0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z998 : W := mkw 0xdffffaddb12db003 0x1bffff5bb625b600 0xfffffffff80ff801 0xffffffffff01ff00

def z999 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xffff8c1e3ffff801 0xfffff183c7ffff00

def z1000 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x000000001c71f800 0x00000000038e3f00

def z1001 : W := mkw 0xa27f9057c12ff879 0x344ff20af825ff0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z1002 : W := mkw 0x4008585c80000000 0x08010b0b90000000 0x40007fffc0000000 0x08000ffff8000000

def z1003 : W := mkw 0x200005227c39de18 0x040000a44f873bc3 0x200000003c7ffe3a 0x24000000078fffc7

def z1004 : W := mkw 0x402c5c1a080b4570 0x88058b83410168ae 0xf03e7c1e200fc7ff 0xbe07cf83c401f8ff

def z1005 : W := mkw 0x200005224db4fe98 0x240000a449b69fd3 0x200000001ff1fe3a 0x2400000003fe3fc7

def z1006 : W := mkw 0x5cac5cba3a5b4570 0xcb958b97474b68ae 0xfffe7cfe3fffc7ff 0xffffcf9fc7fff8ff

def z1007 : W := mkw 0x1d806fa27ed04f98 0x43b00df44fda09f3 0xffc7fffffff1ffff 0xfff8fffffffe3fff

def z1008 : W := mkw 0xc7fffadd80000002 0x18ffff5bb0000000 0xc7ffffffc0000000 0x58fffffff8000000

def z1009 : W := mkw 0x1ed380003364b000 0x03da7000066c9600 0xbfff80003ffff801 0xf7fff00007ffff00

def z1010 : W := mkw 0x43197add80000002 0x08632f5bb0000000 0x4701ffffc0000000 0x48e03ffff8000000

def z1011 : W := mkw 0x9ef7c880336db001 0x13def910066db600 0xbfff8ce03ffff801 0xf7fff19c07ffff00

def z1012 : W := mkw 0x414afadd80209002 0x08295f5bb0041200 0xe8c7ffffdc71f801 0x7d18fffffb8e3f00

def z1013 : W := mkw 0x5da46faa3ed94790 0xcbb48df547db28f2 0xffc67ffe3ff1c7ff 0xfff8cfffc7fe38ff

def z1014 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xfff9f311fffe3fff 0xffff3e623fffc7ff

def z1015 : W := mkw 0xdffffaddb36fb163 0x9bffff5bb66df62c 0xfffffffffffff9c5 0xffffffffffffff38

def z1016 : W := mkw 0xdffffadd8364b003 0x1bffff5bb06c9600 0xffffffffdff1f801 0xfffffffffbfe3f00

def z1017 : W := mkw 0x200005227e79de19 0x040000a44fcf3bc3 0x200000001c71fe3a 0x24000000038e3fc7

def z1018 : W := mkw 0x41087add80800182 0x48210f5bb0100030 0x40007fffc00001c4 0x08000ffff8000038

def z1019 : W := mkw 0x782c5d3a7c3bdf78 0x8f058ba74f877bef 0x303870003c7ffffe 0xa6070e00078fffff

def z1020 : W := mkw 0xdffffaddb2400002 0x1bffff5bb6480000 0xdfffffffe3800001 0xdbfffffffc700000

def z1021 : W := mkw 0x1fdbfad580000000 0x03fb7f5ab0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z1022 : W := mkw 0x582c5818300b0060 0x0b058b030601600c 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z1023 : W := mkw 0x41087add80020062 0x08210f5bb000400c 0xf0387fffe00e07ff 0xbe070ffffc01c0ff

def z1024 : W := mkw 0xbef785227ffdff99 0x57def0a44fffbff3 0xbfff80003fffffff 0xf7fff00007ffffff

def z1025 : W := mkw 0x5d887add80000002 0x0bb10f5bb0000000 0x57007fffc0000000 0x8ae00ffff8000000

def z1026 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xff3ff311ff8fffff 0xffe7fe623ff1ffff

def z1027 : W := mkw 0x5da46fa83ed00780 0x4bb48df507da00f0 0x5fc67fee3ff007c5 0xebf8cffdc7fe00f8

def z1028 : W := mkw 0x82778000336db001 0x104ef000066db600 0xb73f80003ffff801 0xf6e7f00007ffff00

def z1029 : W := mkw 0xc5cafadd80000002 0x18b95f5bb0000000 0x40c07fffc0000000 0x08180ffff8000000

def z1030 : W := mkw 0x86d38000336db001 0x10da7000066db600 0xb7f980003ffff801 0xf6ff300007ffff00

def z1031 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xffffffffe00e0001 0xfffffffffc01c000

def z1032 : W := mkw 0xdff7eacd80000002 0x1bfefd59b0000000 0x9fff8fefc0000001 0xd3fff1fdf8000000

def z1033 : W := mkw 0xdffffaddb0090002 0x1bffff5bb6012000 0xdfffffffd801c001 0xdbfffffffb003800

def z1034 : W := mkw 0x200005227dbffff8 0xa40000a44fb7ffff 0x200000003ffffffe 0x2400000007ffffff

def z1035 : W := mkw 0xa7d3a365c7f4ba89 0x34fa746cb8fe9751 0x07c183e1c7f03800 0x40f8307c38fe0700

def z1036 : W := mkw 0x1d8023a036d00280 0x43b0047406da0050 0x5fc073e03ff007c5 0xebf80e7c07fe00f8

def z1037 : W := mkw 0xddeefaddb2699003 0x1bbddf5bb64d3200 0x48c67fffd871c000 0x0918cffffb0e3800

def z1038 : W := mkw 0xdffffaddb00b0162 0x9bffff5bb601602c 0xfffffffff80fc1c5 0xffffffffff01f838

def z1039 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x1fffffefc0000000 0xc3fffffdf8000000

def z1040 : W := mkw 0xdffffaddb2400002 0x1bffff5bb6480000 0xdfffffffd8700001 0xdbfffffffb0e0000

def z1041 : W := mkw 0x1d806fa07ed00f88 0x43b00df40fda01f1 0x5fc07ff1fff007ff 0xebf80ffe3ffe00ff

def z1042 : W := mkw 0x035bb2558124b000 0x006b764ab0249600 0xfffffffffffff801 0xffffffffffffff00

def z1043 : W := mkw 0x1d806e803a400500 0x03b00dd0074800a0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z1044 : W := mkw 0x5d887add80000002 0x0bb10f5bb0000000 0x48c07fffc0000000 0x09180ffff8000000

def z1045 : W := mkw 0xdffffadd810d2003 0x1bffff5bb021a400 0xdfffffffc00e0001 0xdbfffffff801c000

def z1046 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xdfffffffe00007c5 0xfbfffffffc0000f8

def z1047 : W := mkw 0xdda46fa83ed00782 0x5bb48df507da00f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z1048 : W := mkw 0x43197add80000002 0x08632f5bb0000000 0x57387fffc0000000 0x8ae70ffff8000000

def z1049 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x57f9ffffc0000000 0xcaff3ffff8000000

def z1050 : W := mkw 0x582c5c3a381b4570 0x8b058b87470368ae 0xf8fe7cfe387fc7ff 0xbf1fcf9fc70ff8ff

def z1051 : W := mkw 0x01006fa00c900780 0x40200df4019200f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z1052 : W := mkw 0xbce6cce6ba79d511 0x579cd99cd74f3aa2 0x08c60cee1871c000 0x0118c19dc30e3800

def z1053 : W := mkw 0xdffffaddb364b003 0x1bffff5bb66c9600 0xdffffffffff03801 0xfbfffffffffe0700

def z1054 : W := mkw 0x200005224c32df78 0x840000a449865bef 0x200000001c71fffe 0x24000000038e3fff

def z1055 : W := mkw 0x20428566cc30de18 0x040850acd9861bc3 0xa8c78fffdc71f83a 0x5518f1fffb8e3f07

def z1056 : W := mkw 0x20428566ccb0de98 0x040850acd9961bd3 0xe8c78ffffff1ffff 0x7d18f1fffffe3fff

def z1057 : W := mkw 0xc27f905f812ff073 0x984ff20bf025fe0e 0xa03f801fc00ff83a 0x1407f003f801ff07

def z1058 : W := mkw 0x402c5c1a380b4570 0x88058b83470168ae 0xe03e7c1e380fc7fe 0x3c07cf83c701f8ff

def z1059 : W := mkw 0x414afadd80000002 0x08295f5bb0000000 0xc007ffffc0000000 0x1800fffff8000000

def z1060 : W := mkw 0xdffffadd80209002 0x1bffff5bb0041200 0xdfffffffc4703801 0xdbfffffff88e0700

def z1061 : W := mkw 0xdfbd7add80000002 0x1bf7af5bb0000000 0xdf3e7fffc0000001 0x9be7cffff8000000

def z1062 : W := mkw 0x1866804480000000 0x030cd00890000000 0xd8ff8fffc0000001 0xdb1ff1fff8000000

def z1063 : W := mkw 0x8253804580000002 0x104a7008b0000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z1064 : W := mkw 0x41087add80000002 0x08210f5bb0000000 0xc001ffffc0000001 0x58003ffff8000000

def z1065 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x200000000001fe3a 0x0400000000003fc7

def z1066 : W := mkw 0x27d3a3e5c7f4ba88 0x64fa747cb8fe9751 0x07c183e1c7f03800 0x40f8307c38fe0700

def z1067 : W := mkw 0x9ce68044b2699001 0x139cd008964d3200 0x08c60cee1871c000 0x0118c19dc30e3800

def z1068 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xdfffffffe7800001 0xfbfffffffcf00000

def z1069 : W := mkw 0xfce6cc6eba79d511 0x9f9cd98dd74f3aa2 0x08c60cee1871c000 0x0118c19dc30e3800

def z1070 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0xffc07ff03ff007ff 0xfff80ffe07fe00ff

def z1071 : W := mkw 0x1d806ba036d00380 0x43b00d7406da0070 0x57c073e027f007c5 0xeaf80e7c04fe00f8

def z1072 : W := mkw 0x01006ac480000000 0x00200d5890000000 0x40007fffc0000000 0x08000ffff8000000

def z1073 : W := mkw 0xc35bfadd80000002 0x186b7f5bb0000000 0x4001ffffc0000000 0x08003ffff8000000

def z1074 : W := mkw 0x586ed85cb00b0160 0x8b0ddb0b9601602c 0xd8ffffffe00e01c5 0xdb1ffffffc01c038

def z1075 : W := mkw 0xdce6c8cc80000002 0x1b9cd91990000000 0x08c78fefc0000000 0x4118f1fdf8000000

def z1076 : W := mkw 0x402c141a380b4570 0x88058283470168ae 0xf03e701e380fc7ff 0xbe07ce03c701f8ff

def z1077 : W := mkw 0xdffffaddb36db003 0x1bffff5bb66db600 0xffffffffe38ff801 0xdffffffffc71ff00

def z1078 : W := mkw 0xdde6eacc80000002 0x1bbcdd5990000000 0xdfc7ffffc0000001 0xdbf8fffff8000000

def z1079 : W := mkw 0x0319321101062060 0x006326422020c40c 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z1080 : W := mkw 0xddeefadd80000002 0x1bbddf5bb0000000 0xd8fe7fffc0000001 0x9b1fcffff8000000

def z1081 : W := mkw 0x9ff7eac480000000 0x13fefd5890000000 0xdfffffffc0000001 0xdbfffffff8000000

def z1082 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x28c000001c71fe3b 0x65180000038e3fc7

def z1083 : W := mkw 0xdffffadd818620e2 0x3bffff5bb030c41c 0xffffffffe78e39c5 0xfffffffffcf1c738

def z1084 : W := mkw 0x5da46faa3ed94790 0xcbb48df547db28f2 0xfffe7fee3fffc7c5 0xffffcffdc7fff8f8

def z1085 : W := mkw 0xc27f905d812db003 0x184ff20bb025b600 0xe8ff8fffdc7ff801 0x7d1ff1fffb8fff00

def z1086 : W := mkw 0x200005227e70de18 0x040000a44fce1bc3 0x200000003ff1fe3a 0x2400000007fe3fc7

def z1087 : W := mkw 0xdeffd85cb36db001 0x1bdffb0b966db600 0xfffffffffffff801 0xffffffffffffff00

def z1088 : W := mkw 0x05c2a2c480000000 0x00b8545890000000 0xcfc78fffc0000001 0x59f8f1fff8000000

def z1089 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xff3e7c1e3f8fc7ff 0xffe7cf83c7f1f8ff

def z1090 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xdfffffffdc700001 0xfbfffffffb8e0000

def z1091 : W := mkw 0x1d806fa23ed04790 0x43b00df447da08f2 0x5fc07ffe3ff007ff 0xebf80fffc7fe00ff

def z1092 : W := mkw 0x0319331145862ae8 0x2063266228b0c55d 0xb739f011e78e3ffe 0xb6e73e023cf1c7ff

def z1093 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xafff80001ffff800 0x55fff00003ffff00

def z1094 : W := mkw 0x82778044812db001 0x104ef0089025b600 0xe8ff8fffc00ff801 0x5d1ff1fff801ff00

def z1095 : W := mkw 0xdffffaddb36db003 0x1bffff5bb66db600 0xffffffffd87ff801 0xdffffffffb0fff00

def z1096 : W := mkw 0x41087add80000002 0x08210f5bb0000000 0xd0387fffc0000001 0x9a070ffff8000000

def z1097 : W := mkw 0x225385224db6fef8 0x244a70a449b6dfdf 0xbfff80003fffffff 0xf7fff00007ffffff

def z1098 : W := mkw 0x0042804480000000 0x0008500890000000 0x48c60fffc0000000 0x0918c1fff8000000

def z1099 : W := mkw 0x9fffb355f7efbae9 0x33fff66abefdf75d 0xffffffffffffffff 0xffffffffffffffff

def z1100 : W := mkw 0x1d806fa23ed94790 0xc3b00df447db28f2 0x5fc07fe03ff1c7c5 0xebf80ffc07fe38f8

def z1101 : W := mkw 0x200005227e70df18 0x440000a44fce1be3 0x200000001c71fe3a 0x24000000038e3fc7

def z1102 : W := mkw 0xdffffaddb34d2003 0x1bffff5bb669a400 0xfffffffffb8fc001 0xffffffffff71f800

def z1103 : W := mkw 0x1d806ac480000000 0x03b00d5890000000 0x5fc07fffc0000001 0xcbf80ffff8000000

def z1104 : W := mkw 0xdef7c888336db003 0x1bdef911066db600 0xbfff80003ffff801 0xf7fff00007ffff00

def z1105 : W := mkw 0x000005224c104e18 0x000000a4498209c3 0xe8c78fffdc71fe3b 0x7d18f1fffb8e3fc7

def z1106 : W := mkw 0x41006acd80000002 0x08200d59b0000000 0x00000fefc0000000 0x000001fdf8000000

def z1107 : W := mkw 0x221105224d34fe18 0x044220a449a69fc3 0xb73980003ffffe3b 0xf6e7300007ffffc7

def z1108 : W := mkw 0x582c5cba381b4570 0xcb058b97470368ae 0xf83e7cfe380fc7ff 0xbf07cf9fc701f8ff

def z1109 : W := mkw 0xdffffadd80090002 0x1bffff5bb0012000 0xffffffffc00fc001 0xdffffffff801f800

def z1110 : W := mkw 0x9ef78000336db001 0x13def000066db600 0x37f980003ffff800 0xe6ff300007ffff00

def z1111 : W := mkw 0xdcac5c1a3a4b4571 0x9b958b83474968ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z1112 : W := mkw 0x014ab25580000000 0x0029564ab0000000 0xc8c7ffffc0000001 0x5918fffff8000000

def z1113 : W := mkw 0x1dc2eac4b2c00180 0x43b85d5896580030 0xdfc7ffffe38001c5 0xdbf8fffffc700038

def z1114 : W := mkw 0xdffffaddb2609002 0x1bffff5bb64c1200 0xfffffffffff1f801 0xfffffffffffe3f00

def z1115 : W := mkw 0xdffffadd812db003 0x1bffff5bb025b600 0xffffffffe78ff801 0xfffffffffcf1ff00

def z1116 : W := mkw 0x9ef78000336db001 0x13def000066db600 0xffff80103ffffe3b 0xfffff00207ffffc7

def z1117 : W := mkw 0x1dc2eac4b2609000 0x03b85d58964c1200 0xffc7fffffff1f801 0xfff8fffffffe3f00

def z1118 : W := mkw 0x1cc2c8c480000000 0x0398591890000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z1119 : W := mkw 0xdeffd85c80000000 0x1bdffb0b90000000 0xdfffffffc0000001 0xdbfffffff8000000

def z1120 : W := mkw 0x200005224d966ef8 0x240000a449b2cddf 0x20000000278e3ffe 0x2400000004f1c7ff

def z1121 : W := mkw 0x0042804480000000 0x0008500890000000 0x08c78fefc0000000 0x4118f1fdf8000000

def z1122 : W := mkw 0xdffffadd8364b003 0x1bffff5bb06c9600 0xffffffffe7fe3801 0xfffffffffcffc700

def z1123 : W := mkw 0xdb7ffadd80000002 0x1b6fff5bb0000000 0xd83fffffc0000001 0x9b07fffff8000000

def z1124 : W := mkw 0x87d3a2c58364b003 0x10fa7458b06c9600 0xefc78fffdff1f801 0x7df8f1fffbfe3f00

def z1125 : W := mkw 0x200005224c104e18 0x040000a4498209c3 0x200000001801c63a 0x24000000030038c7

def z1126 : W := mkw 0x5cac5c1a3a4b4570 0x8b958b83474968ae 0xf8fe7c1e387fc7ff 0xbf1fcf83c70ff8ff

def z1127 : W := mkw 0xdffffaddb36db003 0x1bffff5bb66db600 0xdfffffffdff1f801 0xdbfffffffbfe3f00

def z1128 : W := mkw 0x0142eac480000000 0x00285d5890000000 0xc8c7ffffc0000001 0x5918fffff8000000

def z1129 : W := mkw 0x9ff7a2c5b36db003 0x13fef458b66db600 0xffff8ffffffff801 0xfffff1ffffffff00

def z1130 : W := mkw 0x1da46fa23ed94790 0x43b48df447db28f2 0xfffe7ffe3fffc7ff 0xffffcfffc7fff8ff

def z1131 : W := mkw 0x035bb255818620e0 0x206b764ab030c41c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z1132 : W := mkw 0x0253804481042000 0x004a700890208400 0xffff8fffe78e3801 0xfffff1fffcf1c700

def z1133 : W := mkw 0x414afadd80000002 0x08295f5bb0000000 0x40c1ffffc0000000 0x48183ffff8000000

def z1134 : W := mkw 0x86d380448364b001 0x10da7008906c9600 0xcfc78fffc7f03801 0x59f8f1fff8fe0700

def z1135 : W := mkw 0xdffffadd812db003 0x1bffff5bb025b600 0xffffffffdc7ff801 0xfffffffffb8fff00

def z1136 : W := mkw 0x5fbd7a9933cf21e0 0xebf7af532679e43c 0x17387000238e01c4 0x82e70e000471c038

def z1137 : W := mkw 0xdef7c8cc80000002 0x1bdef91990000000 0xdfff8fffc0000001 0xdbfff1fff8000000

def z1138 : W := mkw 0x3cc285227ef0df98 0x479850a44fde1bf3 0xbfc780003ff1ffff 0xf7f8f00007fe3fff

def z1139 : W := mkw 0x404a905d80000002 0x0809520bb0000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z1140 : W := mkw 0x19006f203c900780 0x03200de4079200f0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z1141 : W := mkw 0x2353a345c5a4ba88 0x246a7468b8b49751 0x07018301c7803800 0x40e0306038f00700

def z1142 : W := mkw 0xdffffaddb0090002 0x1bffff5bb6012000 0xdfffffffe00e0001 0xdbfffffffc01c000

def z1143 : W := mkw 0xdffffadd808200e2 0x3bffff5bb010401c 0xdfffffffc00001c5 0xdbfffffff8000038

def z1144 : W := mkw 0x3c8005227e70de18 0x079000a44fce1bc3 0x3fc000003ff1fe3b 0xe7f8000007fe3fc7

def z1145 : W := mkw 0x200005224c30de18 0x040000a449861bc3 0x0000000004703e3a 0x00000000008e07c7

def z1146 : W := mkw 0x18668044b0090000 0x030cd00896012000 0xf8ff8ffff80fc001 0xff1ff1ffff01f800

def z1147 : W := mkw 0x1d806ea03ad00580 0x43b00dd4075a00b0 0x1fc07ce03ff001c5 0xe3f80f9c07fe0038

def z1148 : W := mkw 0x9ef78044b36db001 0x13def008966db600 0xbfff8cee3ffff801 0xf7fff19dc7ffff00

def z1149 : W := mkw 0xdffffadd800b0062 0x9bffff5bb001600c 0xdfffffffc00e0001 0xdbfffffff801c000

def z1150 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x4fc07fe01ff007c4 0x49f80ffc03fe00f8

def z1151 : W := mkw 0x7ce6cceeba79d510 0xcf9cd99dd74f3aa2 0x08c60cee1871c000 0x0118c19dc30e3800

def z1152 : W := mkw 0xc33d7add80000002 0x1867af5bb0000000 0x40387fffc0000000 0x08070ffff8000000

def z1153 : W := mkw 0xc27f905d80000002 0x184ff20bb0000000 0xc03f8fffc0000000 0x1807f1fff8000000

def z1154 : W := mkw 0x231937334db6fef8 0x246326e669b6dfdf 0x373870003ffffffe 0xa6e70e0007ffffff

def z1155 : W := mkw 0xdffffadd80020062 0x1bffff5bb000400c 0xdfffffffe00e01c5 0xdbfffffffc01c038

def z1156 : W := mkw 0x45887add80000002 0x08b10f5bb0000000 0x47c07fffc0000000 0x48f80ffff8000000

def z1157 : W := mkw 0x200005227c1b4f78 0x840000a44f8369ef 0x20000000380fc7fe 0x240000000701f8ff

def z1158 : W := mkw 0x1eb50000334d2000 0x03d6a0000669a400 0xbfff80003ffff801 0xf7fff00007ffff00

def z1159 : W := mkw 0xdffffaddb00b0062 0x1bffff5bb601600c 0xfffffffff80fc7ff 0xffffffffff01f8ff

def z1160 : W := mkw 0x5d887addb2c00182 0x4bb10f5bb6580030 0x57007fffe38001c4 0x8ae00ffffc700038

def z1161 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xc8ffffffc0000000 0x191ffffff8000000

def z1162 : W := mkw 0xdffffadd82400002 0x1bffff5bb0480000 0xdfffffffc7f00001 0xdbfffffff8fe0000

def z1163 : W := mkw 0xdffffaddb2c00182 0x5bffff5bb6580030 0xdffffffffff001c5 0xfbfffffffffe0038

def z1164 : W := mkw 0x59087add80000002 0x0b210f5bb0000000 0x58007fffc0000001 0x8b000ffff8000000

def z1165 : W := mkw 0x5d887addb2400002 0x0bb10f5bb6480000 0x5fc07ffffff00001 0xebf80ffffffe0000

def z1166 : W := mkw 0x9ef78044b34d2001 0x13def0089669a400 0xdfff8fffe38e0001 0xdbfff1fffc71c000

def z1167 : W := mkw 0xdffffaddb0090102 0x9bffff5bb6012020 0xdfffffffc0000001 0xdbfffffff8000000

def z1168 : W := mkw 0x0142a24480000000 0x0028544890000000 0xdfc7ffffc0000001 0xdbf8fffff8000000

def z1169 : W := mkw 0xdde6eacd80000002 0x1bbcdd59b0000000 0x08c60fefc0000000 0x0118c1fdf8000000

def z1170 : W := mkw 0xdffffaddb0000102 0x1bffff5bb6000020 0xdfffffffe00001c5 0xdbfffffffc000038

def z1171 : W := mkw 0x0311230045842a88 0x0062246008b08551 0xf739f311e78e3fff 0xfee73e623cf1c7ff

def z1172 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0x8fff8fffc0000000 0x51fff1fff8000000

def z1173 : W := mkw 0x1c804d203e500700 0x039009a407ca00e0 0x5fc07fe03ff007c5 0xebf80ffc07fe00f8

def z1174 : W := mkw 0xdffffaddb36db003 0x1bffff5bb66db600 0xdffffffffbffc001 0xdbffffffff7ff800

def z1175 : W := mkw 0x200005224c904f98 0x440000a4499209f3 0x00000000000007fe 0x00000000000000ff

def z1176 : W := mkw 0xdffffaddb34d2003 0x1bffff5bb669a400 0xffffffffe78e3801 0xfffffffffcf1c700

def z1177 : W := mkw 0x1da46fa03ed90780 0x43b48df407db20f0 0x5fc67fe03ff1c7c5 0xebf8cffc07fe38f8

def z1178 : W := mkw 0xe27f905ec12ff879 0x9c4ff20bd825ff0f 0xa03f801fc00ff83a 0x1407f003f801ff07

def z1179 : W := mkw 0xdffffadd80020162 0x9bffff5bb000402c 0xdfffffffc00001c5 0xdbfffffff8000038

def z1180 : W := mkw 0x41087add80020162 0x88210f5bb000402c 0x40007fffc00001c4 0x08000ffff8000038

def z1181 : W := mkw 0xdeff905db36db003 0x1bdff20bb66db600 0xffff8ffffffff801 0xfffff1ffffffff00

def z1182 : W := mkw 0x0042804480000000 0x0008500890000000 0xe8c78fffd801c001 0x7d18f1fffb003800

def z1183 : W := mkw 0x20428466c830dc18 0x0408508cd9061b83 0xe8c78fffd871f83b 0x5d18f1fffb0e3f07

def z1184 : W := mkw 0xdef7c808336db101 0x9bdef901066db620 0xbfff80003ffff801 0xf7fff00007ffff00

def z1185 : W := mkw 0x41087add80020062 0x08210f5bb000400c 0x40007fffc00007fe 0x08000ffff80000ff

def z1186 : W := mkw 0x582c5c1a380b4570 0x8b058b83470168ae 0xb03e701e380fc7fe 0xb607ce03c701f8ff

def z1187 : W := mkw 0x8277804480000000 0x104ef00890000000 0xc8ff8fffc0000001 0x591ff1fff8000000

def z1188 : W := mkw 0x200005224c124f78 0x840000a4498249ef 0x00000000000007fe 0x00000000000000ff

def z1189 : W := mkw 0x582c581a000b4070 0x8b058b034001680e 0xf83e7c1e200fc7ff 0xbf07cf83c401f8ff

def z1190 : W := mkw 0x058027a03ed00780 0x40b004f407da00f0 0x57c073e03ff007c5 0xeaf80e7c07fe00f8

def z1191 : W := mkw 0x4008105d80000002 0x0801020bb0000000 0x40000fffc0000000 0x080001fff8000000

def z1192 : W := mkw 0xdffffadd80299003 0x1bffff5bb0053200 0xdfffffffc001c001 0xdbfffffff8003800

def z1193 : W := mkw 0xdffffadd81042002 0x1bffff5bb0208400 0xffffffffc00e3801 0xdffffffff801c700

def z1194 : W := mkw 0xdffffaddb2400102 0x5bffff5bb6480020 0xdfffffffc0000001 0xdbfffffff8000000

def z1195 : W := mkw 0x400048cc80000002 0x0800091990000000 0x40000fffc0000000 0x080001fff8000000

def z1196 : W := mkw 0x386685227c3bdf78 0x870cd0a44f877bef 0xb8ff80003c7fffff 0xf71ff000078fffff

def z1197 : W := mkw 0x200005227c30df18 0x040000a44f861be3 0x200000003c71fffe 0x24000000078e3fff

def z1198 : W := mkw 0x9ef78000336db001 0x13def000066db600 0x1fff80003ffff800 0xc3fff00007ffff00

def z1199 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0xfff87fe03ffe07c5 0xffff0ffc07ffc0f8

def z1200 : W := mkw 0xdffffadd82609003 0x1bffff5bb04c1200 0xdfffffffc0700001 0xdbfffffff80e0000

def z1201 : W := mkw 0x5866c84c80000000 0x0b0cd90990000000 0xc8c78fffc0000001 0x5918f1fff8000000

def z1202 : W := mkw 0xda7fd85d80000002 0x1b4ffb0bb0000000 0xd8ffffffc0000001 0xdb1ffffff8000000

def z1203 : W := mkw 0x225b9055c126b868 0x244b720ab824d70d 0xa0398011c00e383a 0x140730023801c707

def z1204 : W := mkw 0x200005227ed04f98 0x440000a44fda09f3 0x000000003ff007fe 0x2000000007fe00ff

def z1205 : W := mkw 0x5cac5c9a3a4b4570 0xcb958b93474968ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z1206 : W := mkw 0x0319333145962ae8 0x2063266628b2c55d 0xf7f9f3f1e7fe3fff 0xfeff3e7e3cffc7ff

def z1207 : W := mkw 0x86f78000036db001 0x10def000006db600 0xafff80001ffff801 0x75fff00003ffff00

def z1208 : W := mkw 0x1842c84480000000 0x0308590890000000 0xd8c7ffffc0000001 0xdb18fffff8000000

def z1209 : W := mkw 0x61087ffecc924ff8 0xcc210fffd99249ff 0x40007fffc00007fe 0x08000ffff80000ff

def z1210 : W := mkw 0x61087fffcc924efa 0x2c210ffff99249df 0x40007fffc00007fe 0x08000ffff80000ff

def z1211 : W := mkw 0x004a905480020060 0x0009520a9000400c 0xf8ffffffe00e07ff 0xff1ffffffc01c0ff

def z1212 : W := mkw 0x87dbb2d580000002 0x10fb765ab0000000 0xdfffffffc0000001 0xdbfffffff8000000

def z1213 : W := mkw 0x1d806fa03ed00780 0x43b00df407da00f0 0x1fc07fe03ff001c4 0xc3f80ffc07fe0038

def z1214 : W := mkw 0xdffffadd80800082 0x1bffff5bb0100010 0xdfffffffe38001c5 0xdbfffffffc700038

def z1215 : W := mkw 0x43197add81042002 0x08632f5bb0208400 0xf739ffffe78e3801 0xfee73ffffcf1c700

def z1216 : W := mkw 0x41087add808200e2 0x28210f5bb010401c 0x40007fffc00001c4 0x08000ffff8000038

def z1217 : W := mkw 0xdffffadd81062062 0x3bffff5bb020c40c 0xdfffffffc00e0001 0xdbfffffff801c000

def z1218 : W := mkw 0x1a778000312db000 0x034ef0000625b600 0xbfff80003ffff801 0xf7fff00007ffff00

def z1219 : W := mkw 0xddeefadd80000002 0x1bbddf5bb0000000 0xc8c7ffffc0000001 0x5918fffff8000000

def z1220 : W := mkw 0xdffffadd80000002 0x1bffff5bb0000000 0xd73fffffc0000000 0x9ae7fffff8000000

def z1221 : W := mkw 0x1824000030090000 0x0304800006012000 0xf83e0c1e380fc001 0xbf07c183c701f800

def z1222 : W := mkw 0x5dcafadd80000002 0x0bb95f5bb0000000 0xdfc7ffffc0000001 0xdbf8fffff8000000

def z1223 : W := mkw 0xdffffaddb3edb183 0x5bffff5bb67db630 0xfffffffffffff9c5 0xffffffffffffff38

def z1224 : W := mkw 0xdffffadd836db003 0x1bffff5bb06db600 0xffffffffc7fff801 0xdffffffff8ffff00

def z1225 : W := mkw 0x0219101141062868 0x204322022820c50d 0xf739f011e78e3fff 0xfee73e023cf1c7ff

def z1226 : W := mkw 0x200005224c104e18 0x040000a4498209c3 0x000000001c70063a 0x20000000038e00c7

def z1227 : W := mkw 0x18085c1238024570 0x03010b82470048ae 0xf83e7c1e380fc7ff 0xbf07cf83c701f8ff

def z1228 : W := mkw 0xa27785224d3dfe19 0x144ef0a449a7bfc3 0xa03f80001c7ffe3a 0x3407f000038fffc7

def z1229 : W := mkw 0xa6d385224f74fe19 0x14da70a449ee9fc3 0x27c180001ff1fe3a 0x64f8300003fe3fc7

def z1230 : W := mkw 0x05806fa03ed00780 0x40b00df407da00f0 0x47c07fe03ff007c4 0x68f80ffc07fe00f8

def z1231 : W := mkw 0xdfbd7add80000002 0x1bf7af5bb0000000 0x5ff87fffc0000001 0xcbff0ffff8000000

def z1232 : W := mkw 0x1d806ba006d00280 0x43b00d7400da0050 0x5fc07fe027f007c5 0xebf80ffc04fe00f8

def z1233 : W := mkw 0x200005227ffdff99 0x440000a44fffbff3 0x200000003ffffffe 0x2400000007ffffff

def z1234 : W := mkw 0xc7dbfadd80000002 0x18fb7f5bb0000000 0xcfc7ffffc0000001 0x59f8fffff8000000

def z1235 : W := mkw 0x592c7addb00b0162 0x8b258f5bb601602c 0x50387fffe00e01c4 0x8a070ffffc01c038

def z1236 : W := mkw 0x05806ba006d00380 0x40b00d7400da0070 0x07c073e007f001c4 0x40f80e7c00fe0038

def z1237 : W := mkw 0xc7dbfadd80000002 0x18fb7f5bb0000000 0xd7f9ffffc0000001 0xdaff3ffff8000000

def z1238 : W := mkw 0x200005224c32de78 0x040000a449865bcf 0x200000003c7ffffe 0x24000000078fffff

def z1239 : W := mkw 0xdffffadd82c00082 0x5bffff5bb0580010 0xdfffffffc3800001 0xdbfffffff8700000

def z1240 : W := mkw 0xdffffaddb2cb01e2 0xdbffff5bb659603c 0xdfffffffe38e01c5 0xdbfffffffc71c038

def z1241 : W := mkw 0x200005227ffffef9 0x240000a44fffffdf 0x200000003ffffffe 0x2400000007ffffff

def z1242 : W := mkw 0x1d806aa032d00180 0x43b00d54065a0030 0x17c070e023f001c4 0x82f80e1c047e0038

def z1243 : W := mkw 0xdffffadd81042002 0x1bffff5bb0208400 0xdfffffffc7803801 0xdbfffffff8f00700

def z1244 : W := mkw 0x204285224c30de18 0x040850a449861bc3 0x28c600001c71fe3a 0x2518c000038e3fc7

def z1245 : W := mkw 0xc16efadd80000002 0x182ddf5bb0000000 0x40067fffc0000000 0x0800cffff8000000

def z1246 : W := mkw 0x596efadd80000002 0x0b2ddf5bb0000000 0xd8ffffffc0000001 0xdb1ffffff8000000

def z1247 : W := mkw 0x9fffb255b36db001 0x13fff64ab66db600 0xfffffffffffff801 0xffffffffffffff00

def z1248 : W := mkw 0x1cc2804480000000 0x0398500890000000 0xdfc78fffc0000001 0xdbf8f1fff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z9,z2,z3,z4]),(0,[z0,z1,z2,z3,z10,z4,z6]),(0,[z11,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z12,z4,z6]),(0,[z13,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z15,z4]),(0,[z0,z1,z2,z3,z16,z4,z6]),(0,[z17,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z18,z4,z19]),(0,[z0,z1,z2,z3,z4,z20,z6])],[(0,[z21,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z22,z4,z6]),(0,[z23,z0,z1,z8,z2,z3,z4]),(0,[z0,z24,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z26,z4])],[(0,[z0,z27,z1,z2,z3,z4,z6]),(0,[z0,z28,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z29])],[(1,[z0,z1,z2,z30,z3,z6]),(0,[z0,z1,z31,z2,z3,z4,z6]),(0,[z0,z32,z1,z2,z3,z4,z6])],[(0,[z33,z0,z1,z2,z3,z4,z19]),(1,[z0,z1,z2,z34,z4,z6]),(0,[z35,z0,z1,z2,z3,z4,z6]),(1,[z23,z1,z2,z3,z36,z6]),(0,[z0,z1,z2,z3,z37,z4,z6]),(0,[z0,z38,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z40]),(0,[z0,z1,z2,z3,z4,z41,z6])],[(0,[z0,z1,z2,z42,z3,z4,z6]),(0,[z23,z1,z2,z3,z4,z36,z6]),(0,[z0,z1,z2,z43,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z44]),(0,[z0,z45,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z40]),(0,[z0,z1,z2,z46,z3,z4,z6])],[(0,[z1,z2,z3,z47,z4,z36,z6]),(0,[z48,z1,z2,z3,z4,z49,z6]),(0,[z0,z1,z2,z3,z4,z50,z6])]],
   [[(0,[z0,z51,z1,z2,z3,z4,z6]),(0,[z0,z1,z52,z2,z3,z4,z6]),(0,[z53,z1,z2,z3,z47,z4,z6]),(0,[z0,z1,z2,z3,z4,z54,z6]),(0,[z0,z1,z2,z55,z3,z4,z6]),(0,[z0,z1,z56,z3,z57,z4,z6]),(0,[z0,z58,z1,z2,z3,z4,z19])],[(0,[z0,z2,z59,z60,z3,z4,z6]),(0,[z0,z1,z2,z34,z3,z4,z6]),(0,[z0,z1,z2,z61,z62,z4,z6]),(0,[z0,z1,z2,z3,z4,z29,z19]),(0,[z63,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z64,z6]),(0,[z0,z1,z2,z3,z65,z4,z6]),(0,[z0,z1,z2,z3,z66,z4,z6])],[(0,[z0,z67,z1,z2,z3,z4,z6]),(0,[z68,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z69,z2,z3,z4]),(0,[z70,z0,z1,z8,z2,z3,z4]),(1,[z0,z1,z2,z25,z3,z4])],[(0,[z33,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z71]),(0,[z0,z72,z1,z2,z3,z4,z19]),(0,[z73,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z74,z6]),(0,[z0,z1,z2,z3,z75,z6,z19]),(0,[z0,z76,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z77,z3,z4,z6]),(0,[z39,z0,z1,z78,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z79]),(0,[z48,z0,z1,z2,z3,z4,z49]),(0,[z0,z1,z2,z3,z80,z4,z6]),(0,[z0,z1,z81,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z83]),(0,[z39,z0,z1,z2,z3,z18,z4]),(0,[z0,z1,z2,z25,z3,z4,z84]),(0,[z85,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z86,z4,z6]),(0,[z0,z1,z2,z3,z87,z4,z6])],[(0,[z0,z1,z88,z2,z3,z4,z6]),(0,[z0,z1,z2,z89,z3,z4,z19]),(0,[z90,z0,z1,z2,z3,z4,z49]),(0,[z0,z91,z1,z2,z3,z92,z6]),(0,[z0,z1,z56,z2,z3,z75,z6]),(0,[z0,z1,z8,z2,z3,z18,z4]),(0,[z0,z1,z2,z3,z4,z93,z6])],[(0,[z94,z95,z0,z2,z3,z4,z6]),(0,[z0,z1,z96,z2,z3,z4,z6]),(0,[z97,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z57,z19]),(1,[z0,z1,z2,z3,z98,z6]),(0,[z0,z58,z1,z8,z2,z3,z4])],[(1,[z0,z2,z3,z99,z4,z6]),(0,[z0,z100,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z101,z6]),(0,[z0,z1,z102,z2,z103,z4,z6])]],
   [[(0,[z104,z0,z1,z2,z3,z4,z6]),(0,[z105,z0,z1,z2,z106,z4,z6]),(0,[z0,z107,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z106,z4,z19]),(0,[z0,z1,z2,z3,z4,z108,z6])],[(0,[z0,z72,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z106,z4,z109,z6]),(0,[z0,z1,z2,z3,z4,z110,z6]),(0,[z0,z1,z2,z3,z4,z111,z6])],[(0,[z23,z0,z1,z2,z25,z3,z4])],[(0,[z0,z1,z2,z112,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z79,z40]),(0,[z0,z1,z113,z2,z3,z4,z6]),(0,[z114,z0,z1,z2,z3,z4,z19])],[(1,[z0,z1,z2,z115,z4,z6]),(0,[z0,z1,z2,z116,z3,z4,z6]),(0,[z0,z117,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z118,z4]),(0,[z119,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z120,z4,z6]),(0,[z0,z1,z2,z3,z121,z4,z6])],[(1,[z23,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z122,z4,z6]),(0,[z0,z91,z1,z2,z123,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(0,[z125,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z126,z3,z4,z6]),(0,[z127,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z128,z6]),(0,[z0,z1,z2,z3,z129,z4,z6]),(0,[z0,z1,z2,z130,z3,z131,z4])],[(0,[z0,z1,z2,z3,z4,z6,z132]),(0,[z0,z1,z2,z3,z4,z6,z133]),(0,[z48,z90,z1,z2,z3,z4,z6]),(1,[z90,z1,z2,z3,z4,z79]),(0,[z0,z1,z134,z2,z135,z3,z4]),(0,[z0,z136,z1,z2,z3,z4,z6]),(0,[z0,z137,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z25,z3,z4,z109]),(0,[z0,z138,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z139,z6]),(0,[z0,z2,z3,z92,z4,z110,z6]),(0,[z0,z1,z2,z3,z92,z4,z140]),(0,[z0,z1,z2,z3,z4,z141,z6]),(0,[z0,z1,z2,z25,z3,z4,z19])],[(1,[z0,z1,z2,z3,z4,z44]),(0,[z114,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z142,z19])],[(0,[z143,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z115,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z144]),(0,[z0,z1,z2,z3,z4,z145,z6]),(0,[z0,z1,z2,z3,z57,z6,z19])],[(0,[z33,z0,z1,z2,z25,z3,z4]),(0,[z146,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z147,z6]),(0,[z148,z0,z24,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z149,z6]),(0,[z39,z0,z1,z8,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z26,z6]),(0,[z151,z0,z1,z2,z3,z4,z19])],[(0,[z0,z1,z2,z3,z4,z152,z6]),(1,[z0,z100,z9,z3,z4,z6]),(0,[z0,z1,z56,z2,z3,z4,z19]),(0,[z0,z1,z2,z25,z3,z153,z4])],[(0,[z0,z137,z1,z8,z2,z3,z4]),(0,[z154,z39,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z155,z6]),(0,[z0,z58,z1,z2,z25,z3,z4])],[(0,[z156,z0,z1,z60,z3,z4,z6]),(0,[z157,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z62,z4,z6]),(0,[z48,z0,z1,z2,z3,z4,z6]),(1,[z97,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z158,z3,z4,z6]),(0,[z159,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z19,z84])]],
   [[(0,[z0,z1,z2,z160,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z161,z6]),(0,[z39,z0,z1,z2,z61,z3,z4])],[(0,[z162,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z163,z4,z6]),(0,[z0,z72,z1,z2,z25,z3,z4])],[(1,[z0,z1,z2,z164,z4,z6]),(0,[z0,z1,z2,z3,z165,z4,z19]),(0,[z0,z1,z166,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z167,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z168]),(0,[z0,z1,z2,z62,z3,z4,z19]),(0,[z0,z1,z169,z2,z3,z4,z6])],[(0,[z170,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z89,z3,z4]),(0,[z0,z1,z2,z3,z57,z4,z6]),(0,[z0,z1,z2,z3,z4,z171,z6]),(0,[z0,z1,z2,z3,z172,z4,z6])],[(0,[z0,z1,z2,z34,z60,z4,z6]),(0,[z0,z1,z2,z173,z3,z4,z6]),(0,[z0,z1,z2,z174,z3,z4,z6]),(0,[z0,z107,z2,z135,z3,z4,z6]),(0,[z0,z1,z175,z2,z3,z4,z6]),(0,[z176,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z78,z2,z3,z4,z6]),(0,[z177,z0,z1,z2,z3,z4,z6]),(0,[z156,z0,z178,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z179,z6]),(0,[z0,z1,z2,z89,z3,z4,z6]),(0,[z105,z39,z0,z1,z2,z3,z4]),(0,[z0,z91,z1,z2,z3,z110,z6]),(0,[z0,z1,z2,z3,z4,z75,z19]),(0,[z0,z1,z180,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z16,z4]),(0,[z181,z0,z1,z2,z3,z4,z6])],[(0,[z0,z107,z1,z2,z106,z4,z6]),(0,[z73,z0,z2,z3,z92,z4,z6]),(0,[z0,z1,z2,z3,z129,z18,z4])],[(0,[z0,z1,z2,z182,z3,z4,z6]),(0,[z183,z0,z1,z2,z3,z4,z6]),(0,[z94,z33,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z60,z3,z4,z6]),(0,[z94,z0,z100,z2,z3,z4,z6]),(0,[z184,z0,z1,z2,z3,z4,z6]),(0,[z39,z39,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z164,z4,z6]),(0,[z0,z1,z2,z25,z3,z165,z4]),(0,[z0,z1,z2,z3,z185,z4,z6]),(0,[z0,z1,z8,z2,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z186]),(0,[z0,z1,z2,z3,z4,z187,z6])],[(0,[z95,z0,z2,z3,z106,z4,z6]),(0,[z39,z95,z0,z1,z2,z3,z4]),(0,[z188,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z189,z4,z6]),(0,[z0,z1,z8,z2,z135,z3,z4]),(0,[z0,z1,z190,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z191,z6]),(0,[z114,z0,z1,z2,z25,z3,z4])],[(0,[z105,z0,z1,z2,z3,z4,z192]),(0,[z21,z0,z1,z2,z165,z4,z6]),(1,[z0,z1,z2,z3,z4,z133]),(0,[z39,z0,z1,z2,z3,z4,z36]),(0,[z82,z53,z0,z1,z2,z3,z6]),(0,[z193,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z194,z6]),(0,[z195,z0,z1,z2,z3,z4,z6]),(0,[z196,z0,z1,z2,z25,z3,z4])],[(0,[z197,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z198,z4,z6]),(0,[z199,z0,z1,z2,z3,z4,z6]),(0,[z156,z1,z2,z60,z3,z4,z6]),(0,[z105,z0,z1,z2,z89,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z36]),(1,[z53,z1,z2,z3,z47,z6]),(0,[z200,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z2,z3,z4,z6]),(0,[z201,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z102,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z202,z3,z4]),(0,[z0,z203,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z109,z19]),(0,[z0,z1,z2,z3,z4,z19,z19])],[(0,[z33,z204,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z205,z6]),(0,[z0,z1,z2,z3,z206,z4,z6]),(1,[z0,z1,z2,z3,z4,z98]),(0,[z114,z0,z1,z2,z3,z131,z4])],[(0,[z0,z1,z207,z2,z3,z4,z6]),(0,[z0,z1,z208,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z209,z6]),(0,[z210,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z49]),(0,[z0,z107,z1,z2,z62,z4,z6]),(0,[z0,z137,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z19,z211])],[(0,[z0,z204,z1,z2,z198,z4,z6]),(0,[z0,z1,z134,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z212]),(0,[z0,z1,z2,z25,z25,z3,z4])],[(0,[z213,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z214,z4,z6]),(0,[z215,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z61,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z93])]],
   [[(0,[z0,z1,z2,z3,z4,z216,z6]),(0,[z0,z217,z1,z2,z3,z4,z6]),(1,[z114,z0,z1,z2,z131,z4])],[(0,[z0,z1,z2,z3,z4,z6,z218]),(0,[z219,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z131,z4]),(0,[z0,z1,z2,z3,z4,z142,z6]),(0,[z151,z0,z1,z2,z25,z3,z4])],[(0,[z23,z0,z1,z2,z3,z4,z133]),(0,[z73,z0,z1,z2,z3,z110,z6]),(1,[z0,z1,z2,z3,z220,z4]),(0,[z0,z1,z2,z25,z3,z103,z4]),(0,[z0,z1,z56,z2,z25,z3,z4])],[(0,[z151,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z221,z2,z3,z4,z6]),(0,[z222,z0,z1,z2,z3,z4,z6])],[(1,[z95,z78,z2,z3,z4,z6]),(0,[z223,z0,z1,z2,z3,z4,z6]),(0,[z0,z224,z1,z2,z3,z4,z6]),(0,[z225,z0,z1,z2,z3,z4,z6]),(0,[z226,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z36,z6]),(1,[z0,z1,z2,z3,z4,z168]),(0,[z0,z1,z2,z3,z4,z227,z6]),(0,[z148,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z228]),(0,[z229,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z230]),(0,[z0,z1,z2,z202,z3,z4,z6]),(0,[z0,z231,z1,z2,z3,z4,z6])],[(0,[z0,z72,z2,z3,z106,z4,z6]),(0,[z39,z0,z72,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z232,z4,z6]),(0,[z0,z1,z2,z3,z233,z4,z6]),(0,[z0,z1,z2,z61,z18,z4,z6])],[(0,[z234,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z235,z3,z4,z6]),(0,[z236,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z237])]],
   [[(0,[z238,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z239,z4,z6]),(0,[z0,z1,z2,z62,z25,z3,z4])],[(0,[z0,z1,z2,z3,z103,z4,z6]),(0,[z0,z1,z2,z240,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z75]),(0,[z0,z241,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z242,z4,z6]),(0,[z0,z100,z1,z2,z3,z4,z168]),(0,[z0,z1,z2,z62,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z243,z6]),(0,[z0,z1,z2,z3,z244,z4,z6])],[(0,[z0,z1,z2,z3,z245,z4,z6]),(0,[z0,z1,z2,z246,z3,z4,z6]),(0,[z0,z1,z2,z247,z3,z4,z6])],[(0,[z0,z1,z2,z198,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z1,z2,z3,z4,z49,z6,z79]),(0,[z0,z1,z2,z3,z4,z6,z248])],[(0,[z33,z0,z204,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z249,z4,z6]),(0,[z250,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z251,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z252,z4,z6]),(0,[z0,z1,z2,z3,z4,z253,z6]),(0,[z0,z1,z2,z25,z3,z47,z4]),(0,[z0,z1,z2,z254,z3,z4,z6]),(0,[z0,z1,z255,z2,z25,z3,z4])],[(0,[z0,z1,z2,z3,z256,z4,z6]),(0,[z0,z1,z257,z2,z3,z4,z6]),(0,[z0,z1,z258,z2,z3,z4,z6]),(1,[z39,z0,z1,z2,z3,z16])]],
   [[(0,[z259,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z260])],[(0,[z95,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z6,z261]),(0,[z0,z1,z2,z3,z262,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z19])],[(0,[z39,z33,z0,z1,z2,z3,z4]),(0,[z0,z263,z1,z2,z3,z4,z6]),(0,[z213,z0,z1,z264,z3,z4,z6]),(0,[z39,z0,z100,z1,z2,z3,z4]),(0,[z265,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z180,z56,z2,z3,z4])],[(0,[z213,z0,z1,z2,z3,z4,z128]),(0,[z0,z1,z2,z25,z3,z4,z79]),(0,[z0,z107,z2,z3,z4,z110,z6]),(0,[z0,z1,z2,z266,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z267,z6]),(0,[z0,z58,z1,z2,z3,z4,z93]),(0,[z0,z1,z2,z3,z4,z109,z6])],[(0,[z0,z1,z2,z3,z268,z4,z6]),(0,[z0,z1,z2,z3,z4,z269,z6]),(0,[z270,z0,z1,z2,z3,z4,z6]),(0,[z271,z0,z1,z2,z3,z4,z211])],[(0,[z272,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z61,z106,z4,z6]),(0,[z0,z1,z273,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z274,z4,z6]),(0,[z0,z1,z2,z3,z275,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z276]),(0,[z82,z0,z1,z2,z25,z3,z4]),(0,[z39,z0,z1,z2,z2,z3,z4]),(0,[z0,z1,z2,z277,z3,z4,z6]),(0,[z278,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z40])],[(0,[z0,z1,z2,z3,z4,z279,z6])],[(0,[z95,z0,z1,z8,z2,z3,z4]),(0,[z82,z0,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z2,z25,z3,z6])]],
   [[(0,[z0,z2,z89,z3,z99,z4,z6]),(0,[z150,z53,z0,z1,z2,z3,z6]),(0,[z94,z0,z1,z9,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z26,z4]),(0,[z0,z1,z2,z3,z4,z280,z6]),(0,[z0,z1,z2,z130,z4,z6,z40]),(0,[z0,z1,z2,z3,z4,z281,z6])],[(0,[z23,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z123,z3,z4,z6])],[(0,[z53,z0,z1,z2,z3,z4,z19]),(0,[z48,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z282,z2,z3,z4,z6]),(0,[z157,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z131,z4,z19])],[(0,[z33,z0,z107,z2,z3,z4,z6]),(0,[z283,z0,z1,z2,z3,z4,z6]),(0,[z284,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z285,z3,z4,z6])],[(0,[z0,z286,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z287,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z106,z4]),(0,[z39,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z4,z19,z288]),(0,[z0,z1,z2,z25,z3,z4,z4])],[(0,[z0,z1,z2,z3,z4,z289,z6]),(0,[z0,z1,z2,z3,z4,z290,z6]),(0,[z148,z105,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z291,z3,z4,z6]),(0,[z292,z0,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z4,z19])],[(0,[z23,z0,z1,z2,z3,z6,z19]),(0,[z271,z39,z0,z1,z2,z3,z4]),(0,[z293,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z294,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z248]),(0,[z0,z1,z295,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z296,z4,z6]),(0,[z0,z204,z1,z2,z25,z3,z4]),(0,[z53,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z297,z2,z3,z4,z6])],[(0,[z0,z1,z298,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z299,z4,z6]),(0,[z0,z1,z2,z3,z300,z4,z6]),(0,[z0,z301,z1,z2,z3,z4,z6]),(0,[z302,z0,z1,z2,z3,z4,z6]),(0,[z303,z39,z0,z1,z2,z3,z4]),(0,[z0,z58,z1,z2,z4,z109,z6]),(0,[z0,z1,z2,z3,z18,z4,z304])],[(0,[z0,z204,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z84])],[(0,[z95,z33,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z305,z3,z4,z6]),(0,[z306,z0,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z8,z2,z3,z4]),(0,[z114,z0,z1,z2,z130,z4,z6])],[(0,[z0,z78,z2,z135,z3,z4,z6]),(0,[z0,z100,z1,z2,z3,z4,z6]),(0,[z307,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z308]),(0,[z309,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z3,z310,z4,z6])],[(0,[z311,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z49,z19]),(0,[z0,z312,z1,z2,z3,z4,z6])],[(0,[z95,z0,z1,z2,z25,z3,z4]),(0,[z23,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z313]),(0,[z0,z1,z2,z3,z314,z4,z6]),(1,[z0,z107,z2,z62,z4,z6]),(1,[z0,z91,z2,z3,z110,z6]),(0,[z315,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z39,z0,z1,z264,z2,z3,z4]),(0,[z23,z0,z1,z56,z2,z3,z6]),(0,[z0,z1,z2,z3,z15,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z316]),(0,[z0,z1,z2,z317,z3,z4,z6]),(0,[z0,z1,z2,z130,z3,z4,z6]),(0,[z0,z1,z318,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z319,z6])],[(0,[z0,z1,z2,z3,z4,z6,z320]),(0,[z0,z1,z2,z321,z3,z4,z6]),(0,[z0,z107,z72,z2,z3,z4,z6])],[(0,[z21,z0,z1,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z140]),(0,[z0,z1,z2,z25,z3,z92,z4])],[(0,[z322,z0,z1,z2,z3,z4,z6]),(0,[z105,z0,z1,z2,z3,z4,z19]),(1,[z0,z1,z2,z323,z3,z4]),(0,[z148,z0,z1,z2,z103,z4,z6]),(0,[z0,z1,z2,z3,z18,z4,z6])],[(0,[z0,z1,z2,z3,z4,z324,z6]),(0,[z325,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z109]),(0,[z0,z1,z2,z3,z4,z6,z326]),(0,[z0,z1,z8,z2,z3,z86,z4])],[(0,[z327,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z328,z19])],[(0,[z70,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z329,z6])]],
   [[(0,[z33,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z330,z4,z6]),(0,[z53,z0,z1,z2,z25,z3,z4]),(0,[z39,z0,z1,z2,z3,z4,z211]),(0,[z0,z331,z1,z2,z3,z4,z6]),(0,[z332,z0,z1,z2,z3,z4,z19])],[(0,[z0,z1,z2,z3,z333,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z211]),(0,[z334,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z102,z2,z14,z4,z6]),(0,[z82,z0,z1,z2,z3,z57,z6]),(0,[z0,z1,z2,z130,z3,z4,z40])],[(0,[z335,z0,z1,z2,z3,z4,z6]),(0,[z105,z0,z1,z8,z2,z3,z4]),(0,[z39,z21,z0,z1,z2,z3,z4]),(0,[z0,z336,z1,z2,z3,z4,z6]),(0,[z125,z0,z1,z2,z25,z3,z4])],[(0,[z0,z1,z2,z3,z4,z337,z6]),(1,[z0,z1,z2,z3,z4,z128]),(0,[z90,z1,z2,z3,z4,z6,z79]),(1,[z82,z0,z1,z3,z75,z6]),(0,[z0,z58,z1,z2,z3,z4,z6]),(0,[z338,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z19,z339]),(0,[z150,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z340,z3,z4,z6])],[(0,[z1,z264,z2,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z29,z6]),(0,[z0,z1,z2,z3,z4,z6,z341]),(0,[z39,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z8,z2,z61,z3,z4]),(0,[z0,z1,z2,z342,z3,z4,z6])],[(0,[z0,z1,z2,z3,z343,z4,z6]),(0,[z213,z0,z1,z2,z3,z4,z344]),(0,[z0,z1,z264,z2,z3,z4,z19]),(0,[z345,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z346,z4,z6]),(0,[z0,z1,z2,z3,z4,z347,z6]),(0,[z348,z0,z1,z2,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z4,z6])],[(0,[z0,z107,z100,z2,z3,z4,z6]),(0,[z0,z72,z1,z2,z3,z4,z6]),(0,[z349,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z123,z4,z6]),(0,[z271,z0,z2,z3,z4,z29,z6]),(0,[z0,z1,z2,z350,z3,z57,z4]),(0,[z0,z1,z2,z25,z3,z57,z4]),(0,[z39,z351,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z61,z3,z18,z6])],[(0,[z0,z1,z2,z3,z352,z4,z6]),(0,[z0,z1,z69,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z353,z2,z3,z4,z6]),(0,[z0,z204,z1,z2,z164,z4,z6]),(0,[z82,z23,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z354,z3,z4,z6])],[(0,[z213,z1,z264,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z355,z4,z6]),(0,[z0,z356,z1,z2,z3,z4,z6]),(1,[z0,z357,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z26,z4,z19])],[(0,[z0,z1,z14,z3,z103,z4,z6]),(0,[z0,z1,z358,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z6,z19])],[(0,[z204,z1,z78,z2,z3,z4,z6]),(0,[z0,z359,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z360,z6]),(0,[z0,z1,z2,z3,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z361,z6]),(0,[z0,z1,z2,z62,z4,z109,z6]),(0,[z148,z0,z1,z2,z14,z4,z6])],[(0,[z362,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z363,z6])],[(0,[z0,z1,z2,z3,z364,z4,z6])],[(0,[z365,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z165,z4]),(0,[z0,z1,z2,z3,z4,z49,z6]),(1,[z0,z1,z2,z3,z4,z140]),(0,[z0,z1,z2,z3,z366,z4,z6]),(0,[z0,z1,z2,z3,z4,z367,z6]),(2,[z0,z1,z2,z3,z98]),(0,[z368,z0,z1,z2,z3,z4,z6]),(0,[z114,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z369,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z165,z4]),(0,[z196,z0,z1,z2,z3,z4,z6]),(0,[z0,z370,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z371,z1,z2,z3,z4,z6]),(0,[z0,z372,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z373,z3,z4,z6]),(1,[z0,z1,z374,z2,z3,z4]),(0,[z0,z100,z1,z135,z3,z4,z6])],[(0,[z156,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z6,z344]),(0,[z105,z0,z1,z2,z25,z3,z4]),(0,[z375,z0,z1,z2,z3,z4,z6]),(0,[z0,z137,z1,z2,z3,z4,z6]),(1,[z271,z0,z2,z3,z4,z29]),(0,[z376,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z237,z19]),(0,[z0,z1,z2,z3,z4,z377,z6]),(0,[z0,z378,z1,z2,z3,z4,z6])],[(0,[z379,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z380,z4,z6]),(0,[z0,z381,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z350,z3,z4,z6]),(0,[z0,z382,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z6])],[(0,[z0,z1,z2,z3,z383,z4,z6]),(0,[z0,z91,z2,z3,z4,z110,z6]),(0,[z0,z1,z2,z3,z4,z384,z6]),(0,[z39,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z304])],[(0,[z0,z1,z2,z3,z4,z385,z6]),(0,[z0,z1,z2,z3,z4,z386,z6]),(0,[z0,z1,z2,z387,z3,z4,z6]),(0,[z39,z53,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z131,z4,z79]),(0,[z0,z1,z2,z388,z3,z4,z6])],[(0,[z0,z389,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z89,z4,z6]),(0,[z390,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z391,z6]),(0,[z94,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z6,z392]),(0,[z39,z0,z1,z2,z3,z393,z4])],[(0,[z0,z394,z1,z2,z3,z4,z6]),(0,[z0,z137,z2,z3,z4,z6,z211]),(0,[z0,z1,z56,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z341]),(0,[z63,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z395,z6]),(0,[z114,z0,z1,z2,z3,z4,z40])]],
   [[(0,[z0,z396,z1,z2,z3,z4,z6]),(0,[z156,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z397,z2,z3,z4,z6]),(0,[z0,z137,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z398,z4,z6]),(0,[z39,z0,z1,z2,z3,z103,z4]),(0,[z0,z1,z2,z3,z399,z4,z6])],[(0,[z95,z0,z204,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z400,z6]),(0,[z401,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z29])],[],[(0,[z0,z1,z264,z2,z25,z3,z4]),(0,[z0,z1,z258,z2,z3,z4,z75]),(0,[z0,z1,z8,z2,z402,z3,z4]),(0,[z0,z1,z8,z2,z3,z4,z237]),(0,[z0,z403,z58,z2,z3,z4,z6])],[(0,[z404,z0,z1,z2,z3,z4,z6]),(0,[z405,z0,z1,z2,z3,z4,z6]),(0,[z94,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z406,z6]),(0,[z148,z0,z1,z102,z3,z4,z6]),(0,[z0,z407,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z40])],[(0,[z0,z1,z2,z3,z165,z4,z6]),(0,[z0,z1,z2,z3,z4,z408,z6]),(0,[z39,z73,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z409,z6]),(0,[z0,z58,z357,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z410])],[(0,[z0,z1,z190,z2,z3,z4,z6]),(0,[z0,z1,z2,z411,z3,z4,z6]),(0,[z412,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z413,z6]),(0,[z104,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z230,z6])],[(1,[z0,z1,z2,z3,z4,z192]),(1,[z0,z224,z2,z3,z4,z6]),(0,[z0,z1,z2,z414,z3,z4,z6]),(0,[z150,z0,z1,z2,z3,z57,z6])]],
   [[(0,[z415,z0,z1,z2,z3,z4,z6]),(0,[z416,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z75,z6]),(0,[z0,z203,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z130,z4,z40]),(0,[z417,z0,z1,z2,z3,z4,z6])],[(0,[z213,z0,z1,z60,z3,z4,z6]),(1,[z213,z1,z264,z3,z4,z6]),(0,[z125,z0,z1,z56,z2,z3,z4])],[(0,[z0,z418,z1,z2,z3,z4,z6]),(0,[z90,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z419,z3,z4,z6]),(0,[z0,z1,z2,z3,z220,z92,z4]),(0,[z148,z0,z420,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z421]),(0,[z0,z1,z2,z3,z4,z6,z422]),(0,[z39,z90,z0,z1,z2,z3,z4]),(0,[z0,z72,z1,z2,z62,z4,z6]),(0,[z0,z1,z2,z3,z4,z423,z6]),(0,[z424,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z255,z2,z3,z4,z6])],[(0,[z39,z0,z1,z2,z3,z47,z4]),(0,[z0,z91,z1,z2,z3,z4,z425]),(0,[z0,z1,z2,z426,z3,z4,z6]),(0,[z39,z0,z58,z1,z2,z3,z4])],[(1,[z0,z1,z2,z3,z4,z344]),(0,[z427,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z428,z6]),(0,[z271,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z429,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z204,z1,z2,z3,z4]),(0,[z39,z0,z1,z2,z60,z3,z4]),(0,[z150,z23,z0,z1,z2,z3,z6]),(0,[z430,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z431,z2,z3,z4,z6]),(0,[z432,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z433,z19]),(1,[z150,z0,z1,z2,z25,z3])],[(0,[z95,z0,z107,z2,z3,z4,z6]),(0,[z0,z1,z2,z434,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z329]),(1,[z0,z1,z2,z3,z4,z230]),(1,[z0,z1,z2,z3,z4,z304])]],
   [[(0,[z156,z0,z1,z2,z25,z3,z4]),(0,[z90,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z435,z4,z6]),(0,[z0,z1,z436,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z110]),(0,[z437,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z61,z3,z109,z6])],[(0,[z438,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z110]),(0,[z0,z1,z2,z439,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z392]),(0,[z0,z1,z2,z440,z3,z4,z6]),(0,[z0,z1,z8,z2,z2,z3,z4]),(0,[z441,z0,z1,z2,z3,z4,z6])],[(0,[z156,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z442,z3,z4,z6]),(0,[z0,z1,z443,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z75,z19]),(0,[z0,z1,z2,z3,z4,z19,z444])],[(0,[z0,z445,z1,z2,z3,z4,z6]),(0,[z0,z446,z1,z2,z3,z4,z6]),(0,[z271,z0,z1,z8,z2,z3,z4]),(1,[z0,z1,z180,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z447,z6])],[(0,[z94,z0,z1,z2,z25,z3,z4]),(0,[z39,z0,z1,z102,z2,z3,z4]),(0,[z0,z1,z2,z448,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z83,z6]),(0,[z0,z1,z8,z2,z3,z26,z4]),(0,[z449,z0,z1,z2,z3,z4,z19])],[(0,[z0,z450,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z47,z4,z19]),(0,[z0,z1,z2,z451,z3,z4,z6]),(0,[z0,z1,z2,z3,z57,z4,z341]),(0,[z0,z1,z2,z3,z4,z452,z6])],[(0,[z453,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z454,z6]),(0,[z0,z1,z2,z3,z455,z4,z6]),(0,[z0,z456,z1,z2,z3,z4,z6]),(0,[z457,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z458,z6]),(0,[z0,z459,z1,z2,z3,z4,z6]),(1,[z39,z0,z1,z8,z3,z4]),(0,[z0,z1,z2,z460,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z4,z19])]],
   [[(0,[z0,z1,z461,z2,z3,z4,z6]),(0,[z462,z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z29,z6,z211]),(0,[z463,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z130,z3,z4]),(0,[z0,z1,z2,z464,z25,z3,z4])],[(0,[z0,z1,z56,z2,z3,z57,z6]),(0,[z0,z465,z1,z2,z25,z3,z4])],[(0,[z0,z466,z1,z2,z3,z4,z6]),(0,[z467,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z106,z4]),(0,[z468,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z464,z3,z4,z6])],[(0,[z0,z1,z469,z2,z3,z4,z6]),(0,[z39,z0,z1,z56,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z470,z6]),(0,[z0,z465,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z471,z6]),(0,[z472,z0,z1,z2,z3,z4,z6]),(1,[z53,z0,z1,z2,z3,z19]),(0,[z473,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z107,z1,z2,z3,z4])],[(0,[z105,z0,z1,z102,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z474,z6])],[(1,[z0,z1,z2,z3,z4,z422]),(0,[z0,z475,z1,z2,z3,z4,z6]),(0,[z476,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z84]),(0,[z0,z1,z477,z2,z3,z4,z6]),(0,[z0,z1,z2,z18,z4,z109,z6])],[(0,[z53,z0,z1,z2,z3,z47,z6]),(0,[z0,z1,z2,z478,z3,z4,z6]),(0,[z0,z1,z2,z135,z3,z4,z19]),(0,[z0,z1,z2,z3,z479,z4,z6]),(0,[z480,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z481,z4,z6]),(0,[z0,z482,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z483,z4,z6]),(0,[z90,z0,z1,z2,z25,z3,z4]),(0,[z73,z0,z2,z3,z106,z4,z6]),(0,[z0,z1,z8,z2,z354,z3,z4])],[(0,[z0,z1,z2,z25,z89,z3,z4]),(0,[z0,z1,z2,z3,z4,z19,z79]),(1,[z48,z1,z2,z3,z4,z49]),(0,[z114,z39,z0,z1,z2,z3,z4])],[(1,[z21,z1,z2,z89,z4,z6]),(0,[z0,z1,z2,z3,z484,z4,z6]),(0,[z0,z1,z2,z3,z485,z4,z6]),(0,[z0,z1,z2,z3,z486,z4,z6]),(0,[z0,z1,z2,z3,z220,z4,z6]),(0,[z0,z58,z1,z2,z3,z18,z6]),(0,[z0,z1,z2,z3,z487,z4,z6]),(0,[z0,z1,z2,z3,z488,z4,z19])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z0,z100,z78,z2,z3,z4,z6]),(0,[z489,z0,z1,z2,z3,z4,z6]),(0,[z271,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z329,z75]),(1,[z125,z0,z1,z2,z3,z4]),(0,[z490,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z491,z25,z3,z4])],[(0,[z95,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z264,z2,z3,z4]),(0,[z492,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z493,z4,z6]),(1,[z0,z1,z2,z3,z4,z209]),(0,[z53,z0,z1,z2,z3,z6,z19]),(0,[z0,z1,z2,z3,z494,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z495]),(1,[z0,z420,z2,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z6]),(0,[z0,z1,z2,z14,z3,z4,z248])],[(0,[z0,z496,z1,z2,z25,z3,z4])],[(0,[z497,z0,z1,z2,z3,z4,z6]),(0,[z0,z178,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z99,z4,z6]),(0,[z0,z1,z2,z3,z92,z4,z19]),(0,[z0,z1,z2,z25,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z433,z6])],[(0,[z0,z1,z2,z3,z498,z4,z6]),(0,[z0,z1,z2,z3,z4,z212,z6]),(0,[z0,z1,z2,z499,z3,z4,z6]),(1,[z0,z1,z2,z3,z16,z6]),(0,[z0,z500,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z25,z3,z501,z4])]],
   [[(0,[z0,z2,z62,z3,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z211]),(0,[z0,z403,z1,z2,z3,z4,z6])],[(0,[z21,z1,z2,z89,z3,z4,z6]),(0,[z0,z502,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z36]),(0,[z0,z100,z9,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z92,z4]),(0,[z151,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z8,z2,z3,z4,z109])],[(0,[z23,z0,z1,z2,z3,z36,z6]),(1,[z0,z1,z503,z2,z3,z4]),(0,[z0,z1,z2,z3,z504,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z19]),(0,[z0,z505,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z506,z3,z4,z6])],[(0,[z0,z1,z2,z3,z507,z4,z6]),(0,[z0,z1,z2,z508,z3,z4,z6]),(0,[z0,z1,z2,z509,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z49]),(0,[z0,z91,z1,z2,z3,z4,z19]),(0,[z148,z39,z0,z1,z2,z3,z4]),(0,[z0,z510,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z511,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z209]),(0,[z449,z0,z1,z2,z3,z4,z6])],[(0,[z512,z0,z1,z2,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z131,z4,z6]),(0,[z0,z1,z2,z3,z513,z4,z6])],[(0,[z0,z1,z2,z514,z3,z4,z6]),(0,[z0,z1,z2,z515,z3,z4,z6]),(0,[z53,z0,z1,z56,z2,z3,z6]),(0,[z0,z1,z2,z3,z516,z4,z6]),(1,[z0,z1,z258,z2,z3,z4]),(0,[z517,z0,z1,z2,z3,z4,z6])],[(0,[z33,z0,z78,z2,z3,z4,z6]),(1,[z0,z178,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z518,z6]),(0,[z21,z0,z1,z2,z3,z4,z19]),(0,[z125,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z204,z100,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z0,z1,z8,z8,z2,z3,z4])],[(0,[z0,z204,z2,z135,z3,z4,z6]),(0,[z156,z213,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z520,z6]),(0,[z0,z1,z2,z3,z4,z521,z6]),(0,[z0,z91,z1,z8,z2,z3,z4]),(0,[z0,z522,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z98,z6]),(0,[z0,z1,z2,z3,z4,z6,z523])],[(0,[z39,z213,z0,z1,z2,z3,z4]),(0,[z0,z1,z524,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z129,z4]),(1,[z0,z1,z2,z3,z26,z19])],[(0,[z0,z1,z2,z3,z525,z4,z6]),(0,[z0,z526,z1,z2,z3,z4,z6]),(0,[z250,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z46,z3,z4,z19])],[(0,[z39,z0,z1,z2,z3,z57,z4])],[(0,[z33,z0,z9,z2,z3,z4,z6]),(0,[z527,z0,z1,z2,z60,z3,z6]),(0,[z21,z0,z1,z8,z2,z3,z4]),(0,[z90,z0,z1,z2,z3,z4,z79]),(0,[z0,z1,z2,z135,z25,z3,z4]),(0,[z0,z1,z2,z3,z528,z4,z6])],[(0,[z105,z1,z2,z3,z165,z4,z6]),(0,[z529,z0,z1,z2,z3,z4,z6]),(0,[z530,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z531,z2,z3,z4,z6])],[(0,[z154,z0,z1,z2,z3,z4,z6]),(1,[z0,z72,z2,z106,z4,z6]),(0,[z0,z107,z2,z62,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z75]),(0,[z0,z1,z31,z8,z2,z3,z4]),(0,[z0,z1,z532,z2,z3,z4,z6])]],
   [[(0,[z0,z533,z1,z2,z3,z4,z6]),(0,[z0,z534,z1,z2,z60,z3,z4]),(0,[z0,z1,z2,z535,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z4,z19])],[(0,[z0,z1,z2,z3,z4,z536,z6]),(0,[z0,z1,z8,z2,z3,z537,z4]),(0,[z0,z1,z538,z2,z3,z4,z6])],[(1,[z0,z534,z1,z2,z3,z4]),(1,[z105,z1,z2,z165,z4,z6]),(0,[z0,z1,z3,z4,z237,z6,z84])],[(0,[z39,z23,z0,z1,z2,z3,z4]),(0,[z437,z39,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z539]),(1,[z0,z1,z2,z3,z15,z4])],[(0,[z0,z1,z2,z3,z540,z4,z6]),(0,[z0,z107,z1,z2,z3,z4,z19]),(0,[z82,z39,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z192,z6]),(0,[z0,z1,z2,z3,z4,z110,z19]),(0,[z73,z0,z1,z8,z2,z3,z4]),(0,[z271,z0,z137,z2,z3,z4,z6]),(0,[z0,z1,z541,z2,z3,z4,z6])],[(0,[z105,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z542,z2,z3,z4,z6]),(0,[z543,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z118,z103,z4]),(1,[z0,z1,z56,z3,z57,z6]),(0,[z85,z0,z1,z8,z2,z3,z4]),(0,[z544,z0,z1,z2,z3,z4,z19]),(0,[z0,z500,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z545,z2,z3,z4,z6]),(0,[z0,z1,z546,z2,z3,z4,z6]),(0,[z0,z1,z2,z547,z3,z4,z6]),(0,[z0,z1,z8,z2,z25,z3,z4])],[(1,[z548,z0,z1,z2,z4,z6]),(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z374,z2,z60,z3,z4]),(0,[z0,z1,z2,z323,z3,z47,z4]),(0,[z0,z549,z1,z2,z3,z4,z6]),(0,[z0,z550,z1,z2,z3,z4,z6]),(0,[z0,z91,z1,z2,z25,z3,z4]),(0,[z39,z0,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z3,z4,z6,z84]),(0,[z551,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z328,z6])],[(0,[z0,z1,z2,z3,z4,z49,z40]),(0,[z0,z1,z2,z3,z4,z6,z552]),(0,[z0,z1,z2,z3,z4,z553,z6]),(1,[z148,z0,z1,z103,z4,z6]),(0,[z39,z0,z1,z2,z3,z131,z4]),(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z127,z0,z1,z2,z3,z4,z19])],[(0,[z0,z1,z2,z3,z4,z6,z555]),(0,[z0,z107,z1,z8,z2,z3,z4]),(0,[z39,z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z8,z2,z3,z131,z4]),(0,[z0,z1,z2,z3,z4,z556,z6]),(0,[z332,z0,z1,z2,z3,z4,z6])],[(1,[z0,z52,z2,z3,z4,z6]),(0,[z39,z0,z1,z9,z2,z3,z4]),(0,[z0,z1,z8,z2,z3,z103,z4]),(1,[z0,z1,z2,z3,z4,z523])],[(0,[z557,z0,z1,z2,z3,z4,z6]),(0,[z21,z0,z1,z2,z25,z3,z4]),(1,[z39,z0,z1,z2,z3,z4])],[(0,[z0,z1,z558,z2,z3,z4,z6]),(0,[z0,z224,z2,z89,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z559,z6]),(0,[z0,z1,z2,z3,z560,z4,z6]),(0,[z0,z1,z2,z3,z537,z4,z6]),(0,[z0,z1,z2,z3,z561,z4,z6]),(0,[z0,z1,z2,z131,z4,z6,z40]),(0,[z114,z0,z1,z2,z131,z4,z6])],[(0,[z0,z72,z1,z2,z106,z4,z6]),(0,[z562,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z288]),(0,[z0,z1,z2,z3,z4,z563,z6]),(0,[z39,z0,z1,z2,z3,z4,z29])]],
   [[(0,[z0,z1,z264,z2,z3,z4,z6])],[(0,[z0,z564,z1,z2,z3,z4,z6]),(0,[z0,z565,z1,z2,z3,z4,z6]),(0,[z0,z1,z566,z2,z3,z4,z6]),(1,[z39,z0,z1,z2,z3,z98]),(1,[z0,z58,z1,z2,z109,z6]),(1,[z332,z0,z1,z2,z3,z4])],[(0,[z567,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z568,z4,z6]),(0,[z0,z1,z2,z569,z3,z4,z6]),(0,[z0,z1,z570,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z425]),(0,[z0,z1,z2,z571,z3,z4,z6]),(0,[z39,z0,z137,z1,z2,z3,z4]),(0,[z0,z1,z572,z2,z3,z4,z6]),(0,[z0,z1,z2,z573,z3,z4,z6])],[(0,[z0,z1,z2,z574,z3,z4,z6]),(0,[z0,z91,z1,z2,z115,z4,z6]),(1,[z0,z403,z2,z3,z4,z6])],[(0,[z48,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z503,z2,z135,z3,z4]),(0,[z575,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z4,z392]),(0,[z0,z1,z2,z3,z26,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z576]),(0,[z0,z1,z2,z3,z4,z6,z577]),(0,[z578,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z579,z3,z4,z6]),(0,[z580,z0,z1,z2,z3,z4,z6])],[(0,[z73,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z25,z3,z18,z4]),(0,[z0,z1,z2,z25,z3,z581,z4]),(0,[z0,z1,z2,z3,z153,z4,z6])],[(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z205,z6]),(0,[z376,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z583,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z584,z6]),(0,[z0,z1,z2,z3,z4,z19,z410]),(0,[z0,z1,z2,z3,z501,z4,z6])]],
   [[(0,[z0,z1,z8,z2,z3,z47,z4]),(0,[z0,z1,z2,z3,z49,z205,z6]),(0,[z0,z1,z2,z3,z57,z4,z19]),(0,[z424,z0,z1,z2,z3,z4,z6])],[(0,[z548,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z30,z60,z3,z6]),(0,[z0,z585,z1,z2,z3,z4,z6])],[(0,[z0,z1,z78,z2,z3,z4,z19]),(0,[z0,z1,z8,z2,z60,z3,z4]),(0,[z0,z1,z586,z2,z3,z4,z6]),(0,[z48,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z587,z3,z4,z6]),(1,[z39,z0,z1,z3,z4,z84]),(0,[z0,z1,z180,z2,z3,z4,z19])],[(0,[z0,z100,z1,z9,z3,z4,z6]),(0,[z0,z107,z1,z2,z25,z3,z4]),(0,[z39,z0,z1,z2,z62,z3,z4]),(0,[z0,z588,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z60,z3,z4,z19]),(0,[z39,z0,z1,z2,z3,z4,z79]),(0,[z589,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z590,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z62,z3,z4]),(1,[z0,z137,z2,z3,z4,z211]),(0,[z0,z1,z2,z3,z4,z6,z591]),(1,[z0,z1,z102,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z592,z6])],[(0,[z53,z23,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z79]),(0,[z0,z593,z1,z2,z3,z4,z6]),(0,[z39,z0,z91,z1,z2,z3,z4]),(0,[z0,z1,z2,z594,z3,z4,z6]),(0,[z39,z0,z595,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z237,z6])],[(0,[z0,z1,z2,z3,z4,z6,z596])],[(1,[z527,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z597,z6]),(0,[z598,z0,z1,z2,z3,z4,z6]),(0,[z544,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z599,z4,z6]),(0,[z0,z1,z2,z116,z25,z3,z4])]],
   [[(0,[z0,z1,z78,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z600,z6]),(0,[z0,z601,z1,z2,z3,z4,z6]),(0,[z0,z1,z9,z2,z3,z4,z19]),(0,[z0,z1,z8,z102,z2,z3,z4]),(0,[z0,z1,z102,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z393,z4,z6]),(0,[z0,z1,z180,z8,z2,z3,z4]),(0,[z0,z58,z1,z2,z3,z4,z523])],[(1,[z0,z2,z59,z3,z4,z6]),(0,[z105,z21,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z602,z6]),(0,[z94,z0,z1,z2,z3,z4,z6]),(0,[z603,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z4,z83]),(0,[z0,z604,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z605,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z19,z40])],[(0,[z0,z1,z606,z2,z3,z4,z6]),(0,[z150,z39,z0,z1,z2,z3,z4])],[(0,[z607,z0,z1,z2,z3,z4,z6]),(0,[z213,z0,z1,z2,z3,z4,z19]),(0,[z105,z0,z1,z2,z62,z4,z6]),(0,[z608,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z61,z3,z4,z19]),(0,[z0,z609,z1,z2,z3,z4,z6])],[(0,[z0,z1,z610,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z611,z6]),(0,[z0,z1,z2,z2,z3,z4,z6]),(0,[z0,z1,z2,z30,z3,z4,z6]),(0,[z0,z1,z2,z3,z131,z4,z49]),(0,[z97,z0,z1,z2,z3,z49,z6]),(1,[z0,z1,z2,z3,z4,z425]),(0,[z0,z1,z2,z3,z4,z6,z612]),(0,[z0,z1,z2,z3,z4,z6,z84]),(0,[z0,z58,z1,z2,z61,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z613]),(1,[z294,z0,z2,z3,z4,z6]),(0,[z1,z2,z89,z3,z165,z4,z6]),(0,[z0,z1,z2,z614,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z339]),(0,[z615,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z616,z3,z4,z6]),(0,[z0,z617,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z106,z4]),(0,[z0,z1,z2,z3,z4,z618,z6]),(0,[z0,z1,z619,z2,z3,z4,z6]),(0,[z0,z137,z1,z2,z3,z4,z211]),(0,[z39,z0,z1,z2,z130,z3,z4]),(1,[z0,z1,z2,z25,z3,z19])],[(1,[z156,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z620,z3,z4,z6]),(0,[z0,z9,z2,z135,z3,z4,z6]),(0,[z73,z0,z1,z2,z3,z92,z6]),(0,[z0,z1,z2,z25,z3,z4,z211]),(0,[z0,z1,z2,z3,z621,z4,z6]),(0,[z0,z1,z8,z56,z2,z3,z4]),(0,[z0,z1,z8,z2,z130,z3,z4])]],
   [[(0,[z622,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z623,z3,z4,z6]),(0,[z0,z624,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z56,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z625]),(0,[z222,z0,z1,z2,z3,z4,z19])],[(0,[z626,z0,z1,z2,z3,z4,z6]),(0,[z0,z91,z1,z2,z3,z4,z428]),(0,[z39,z0,z1,z2,z3,z4,z98]),(0,[z627,z0,z1,z2,z3,z4,z6])],[(0,[z213,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z628,z6]),(0,[z0,z1,z2,z3,z4,z36,z19]),(0,[z48,z0,z1,z2,z25,z3,z4]),(0,[z148,z0,z1,z2,z3,z4,z19])],[(0,[z629,z0,z1,z2,z3,z4,z6]),(0,[z294,z0,z2,z60,z3,z4,z6]),(0,[z0,z1,z503,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z630,z4,z6])],[(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z632,z2,z3,z4,z6]),(0,[z148,z0,z1,z3,z103,z4,z6])],[(0,[z633,z0,z1,z2,z3,z4,z6]),(0,[z90,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z2,z3,z75,z6]),(0,[z634,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z635,z3,z4,z6])],[(0,[z0,z1,z636,z2,z3,z4,z6]),(0,[z0,z1,z637,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z103,z4,z19]),(0,[z151,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z638,z6]),(0,[z0,z1,z639,z2,z3,z4,z6])],[(0,[z105,z0,z1,z2,z165,z4,z6]),(0,[z39,z0,z1,z2,z89,z3,z4]),(0,[z0,z1,z2,z3,z640,z4,z6]),(0,[z0,z641,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z57,z4,z75,z6]),(0,[z0,z1,z2,z174,z25,z3,z4]),(0,[z176,z0,z1,z2,z25,z3,z4])]],
   [[(0,[z0,z1,z78,z2,z25,z3,z4]),(0,[z156,z0,z1,z264,z3,z4,z6]),(0,[z21,z0,z1,z102,z2,z4,z6]),(0,[z0,z1,z642,z2,z3,z4,z6]),(0,[z271,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z643,z3,z4,z6]),(0,[z148,z0,z1,z8,z2,z3,z4]),(0,[z229,z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z491,z3,z4,z6])],[(0,[z0,z1,z2,z3,z644,z4,z6]),(0,[z0,z100,z2,z3,z106,z4,z6]),(0,[z0,z1,z2,z3,z4,z645,z6]),(0,[z646,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z19])],[(0,[z0,z1,z2,z60,z25,z3,z4]),(0,[z0,z1,z2,z3,z647,z4,z6]),(0,[z0,z496,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z648,z6]),(0,[z95,z0,z78,z2,z3,z4,z6]),(1,[z33,z204,z2,z3,z4,z6]),(0,[z0,z534,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z649,z6]),(0,[z0,z1,z69,z2,z3,z103,z4]),(0,[z303,z0,z1,z2,z3,z4,z6])],[(0,[z548,z0,z1,z2,z60,z4,z6]),(0,[z0,z650,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z14,z3,z4])],[(0,[z651,z0,z1,z2,z3,z4,z6]),(0,[z94,z0,z2,z135,z3,z4,z6]),(0,[z39,z0,z1,z2,z135,z3,z4]),(0,[z0,z1,z8,z2,z3,z92,z4]),(0,[z0,z652,z1,z2,z3,z4,z6]),(0,[z653,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z9,z2,z25,z3,z4]),(0,[z0,z2,z3,z106,z4,z110,z6]),(0,[z271,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z102,z2,z25,z3,z4]),(0,[z39,z0,z1,z572,z2,z3,z4])],[(0,[z654,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z655]),(1,[z0,z1,z2,z3,z4,z428]),(0,[z0,z1,z656,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z657,z4,z6]),(0,[z0,z1,z2,z3,z658,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z659]),(0,[z0,z1,z2,z3,z660,z4,z6]),(0,[z0,z1,z420,z2,z3,z4,z6])],[(0,[z95,z0,z9,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z661,z6]),(0,[z148,z21,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z47,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z662]),(0,[z39,z0,z1,z2,z3,z4,z49]),(0,[z0,z1,z2,z663,z3,z4,z6])],[(0,[z213,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z664,z0,z1,z2,z3,z4,z6]),(1,[z94,z0,z135,z3,z4,z6]),(0,[z665,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z61,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z666,z6])],[(0,[z0,z667,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z668,z4,z6]),(0,[z0,z669,z1,z2,z3,z4,z6]),(0,[z0,z595,z1,z2,z3,z4,z6])],[(0,[z0,z1,z374,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z670,z6]),(0,[z73,z0,z91,z2,z3,z4,z6]),(0,[z351,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z8,z3,z4,z237]),(0,[z0,z1,z2,z3,z4,z671,z6])],[(0,[z33,z0,z2,z3,z106,z4,z6]),(0,[z0,z672,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z323,z3,z4,z6]),(0,[z94,z0,z1,z135,z3,z4,z6]),(0,[z0,z1,z2,z3,z581,z4,z6])],[(0,[z48,z0,z1,z2,z3,z4,z79]),(1,[z0,z1,z134,z2,z3,z4]),(0,[z0,z1,z2,z3,z673,z4,z6]),(0,[z0,z1,z2,z674,z3,z4,z6]),(1,[z73,z0,z2,z3,z92,z6]),(0,[z0,z1,z2,z3,z675,z4,z6]),(0,[z225,z0,z1,z2,z25,z3,z4])]],
   [[(0,[z490,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z676,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z36,z6]),(0,[z0,z100,z1,z2,z3,z4,z212]),(0,[z0,z1,z2,z3,z4,z677,z6]),(0,[z148,z0,z1,z2,z25,z3,z4]),(0,[z0,z1,z8,z2,z3,z57,z4])],[(0,[z0,z1,z2,z3,z678,z4,z6]),(0,[z0,z1,z2,z25,z3,z4,z237])],[(0,[z0,z1,z2,z135,z3,z4,z6]),(1,[z0,z24,z2,z3,z4,z6]),(0,[z0,z1,z102,z14,z3,z4,z6]),(0,[z679,z0,z1,z2,z3,z4,z6]),(0,[z82,z0,z1,z3,z4,z75,z6]),(0,[z82,z0,z1,z8,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z680,z6]),(0,[z0,z681,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z682,z4,z6]),(1,[z0,z1,z2,z350,z3,z4]),(0,[z0,z1,z2,z3,z4,z683,z6])],[(0,[z684,z0,z1,z2,z3,z4,z6]),(0,[z685,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z686,z6]),(1,[z0,z1,z2,z3,z4,z19])],[(0,[z0,z687,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z3,z4,z75]),(0,[z0,z1,z282,z8,z2,z3,z4]),(0,[z0,z1,z8,z3,z4,z237,z6]),(0,[z0,z1,z2,z3,z488,z4,z6])],[(0,[z0,z1,z688,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z47,z4,z44]),(0,[z73,z0,z107,z2,z3,z4,z6])],[(0,[z0,z204,z1,z2,z3,z4,z19]),(0,[z156,z0,z52,z2,z3,z4,z6]),(0,[z0,z1,z2,z689,z3,z4,z6]),(0,[z0,z1,z2,z3,z690,z4,z6]),(0,[z0,z1,z2,z3,z691,z4,z6]),(0,[z0,z1,z2,z692,z3,z4,z6]),(0,[z693,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z95,z1,z78,z2,z3,z4,z6]),(0,[z156,z39,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z694]),(0,[z0,z1,z2,z3,z695,z4,z6]),(0,[z0,z1,z2,z3,z118,z4,z6]),(0,[z39,z0,z370,z1,z2,z3,z4]),(0,[z0,z1,z2,z402,z3,z4,z6]),(0,[z0,z1,z357,z2,z3,z4,z6]),(1,[z0,z1,z2,z61,z18,z6]),(0,[z0,z1,z2,z3,z696,z4,z6]),(0,[z0,z1,z2,z3,z4,z697,z6]),(0,[z0,z1,z2,z25,z340,z3,z4])],[(0,[z0,z1,z2,z3,z4,z698,z6]),(0,[z0,z100,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z92,z4,z6])],[(1,[z0,z1,z8,z2,z3,z4]),(1,[z0,z1,z255,z2,z3,z4])],[(0,[z0,z2,z135,z3,z106,z4,z6]),(0,[z150,z0,z1,z2,z3,z75,z6]),(0,[z39,z0,z1,z2,z440,z3,z4])],[(0,[z699,z0,z1,z2,z3,z4,z6]),(0,[z23,z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z700,z3,z4,z6]),(0,[z94,z39,z0,z1,z2,z3,z4]),(0,[z701,z0,z1,z2,z3,z4,z6])],[(0,[z0,z204,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z702,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z444]),(0,[z0,z1,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z130,z3,z4,z19]),(0,[z0,z1,z703,z2,z3,z4,z6])],[(0,[z105,z0,z1,z2,z3,z4,z422]),(0,[z0,z1,z2,z3,z4,z6,z704]),(0,[z0,z91,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z705,z3,z4,z6]),(0,[z0,z1,z2,z3,z26,z6,z19])],[(0,[z0,z1,z706,z2,z3,z4,z6]),(0,[z0,z100,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z25,z3,z4,z110]),(0,[z0,z58,z1,z2,z3,z109,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z150,z0,z1,z2,z3,z209]),(0,[z707,z1,z2,z3,z4,z6]),(0,[z125,z0,z1,z56,z3,z57]),(0,[z708,z0,z1,z2,z3,z98])],[(0,[z0,z1,z2,z709,z3,z4]),(0,[z90,z0,z1,z2,z3,z98]),(0,[z0,z710,z135,z3,z4,z6]),(0,[z0,z2,z710,z3,z4,z6]),(0,[z0,z100,z273,z3,z4,z6]),(0,[z39,z73,z0,z2,z3,z92]),(0,[z125,z0,z1,z2,z3,z16]),(0,[z0,z1,z8,z2,z711,z3]),(0,[z0,z403,z58,z2,z109,z6])],[(0,[z0,z1,z2,z3,z4,z712]),(0,[z39,z0,z1,z297,z3,z4]),(0,[z0,z1,z713,z2,z3,z4]),(0,[z714,z0,z1,z2,z3,z4]),(0,[z0,z357,z2,z61,z4,z6])],[(0,[z0,z2,z715,z3,z4,z6]),(0,[z39,z0,z178,z2,z3,z4]),(0,[z294,z0,z534,z2,z3,z4]),(0,[z0,z1,z2,z387,z3,z19]),(0,[z0,z1,z716,z2,z3,z4]),(0,[z0,z1,z717,z2,z3,z4]),(0,[z97,z0,z1,z2,z3,z6]),(0,[z0,z2,z3,z718,z110,z6]),(0,[z376,z0,z2,z402,z3,z4]),(0,[z0,z138,z1,z2,z25,z3])],[(0,[z0,z204,z1,z2,z3,z98]),(0,[z0,z1,z2,z3,z4,z719]),(0,[z0,z1,z2,z4,z720,z6]),(0,[z0,z91,z2,z3,z110,z425]),(0,[z0,z1,z2,z3,z4,z721]),(0,[z0,z1,z2,z3,z98,z722])],[(0,[z0,z1,z2,z3,z723,z6]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z2,z3,z98,z79]),(0,[z0,z2,z62,z725,z4,z6]),(0,[z0,z1,z8,z632,z3,z4]),(0,[z0,z1,z2,z3,z4,z726])],[(0,[z0,z1,z2,z3,z611,z19]),(0,[z0,z1,z56,z3,z57,z341]),(0,[z0,z1,z2,z3,z727,z6]),(0,[z0,z728,z2,z3,z4,z19])],[(0,[z0,z1,z8,z2,z164,z4]),(0,[z578,z204,z2,z3,z4,z6]),(0,[z527,z0,z2,z59,z3,z6]),(0,[z193,z0,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z729,z6]),(0,[z0,z1,z2,z3,z730,z6]),(0,[z39,z0,z1,z2,z3,z730]),(0,[z0,z1,z2,z3,z504,z19]),(0,[z449,z1,z2,z3,z4,z328]),(0,[z0,z2,z731,z3,z4,z19])]],
   [[(0,[z0,z1,z2,z732,z4,z6]),(0,[z0,z446,z1,z2,z109,z6]),(0,[z332,z0,z1,z2,z3,z75]),(0,[z0,z1,z733,z2,z3,z4])],[(0,[z0,z1,z2,z3,z734,z6]),(0,[z105,z1,z2,z165,z4,z192]),(0,[z0,z1,z2,z3,z735,z4]),(0,[z736,z0,z1,z2,z4,z6]),(0,[z737,z1,z2,z3,z4,z6])],[(0,[z0,z2,z3,z738,z4,z6]),(0,[z105,z1,z2,z739,z4,z6]),(0,[z0,z1,z710,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z740]),(0,[z0,z1,z102,z2,z3,z98])],[(0,[z0,z1,z2,z3,z628,z19]),(0,[z0,z394,z2,z62,z4,z6]),(0,[z0,z1,z2,z3,z4,z741]),(0,[z0,z1,z2,z742,z3,z4]),(0,[z743,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z232,z19]),(0,[z0,z1,z56,z255,z3,z4]),(0,[z0,z1,z255,z464,z3,z4])],[(0,[z0,z1,z2,z744,z4,z6]),(0,[z0,z1,z2,z3,z511,z19]),(0,[z0,z745,z2,z3,z4,z6]),(0,[z82,z0,z1,z3,z75,z83]),(0,[z0,z728,z8,z2,z3,z4]),(0,[z114,z0,z1,z2,z746,z4])],[(0,[z0,z1,z2,z3,z747,z4]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z2,z3,z4,z749]),(0,[z39,z0,z1,z2,z3,z205]),(0,[z0,z1,z2,z3,z4,z750]),(0,[z39,z0,z1,z2,z3,z751]),(0,[z0,z1,z2,z18,z727,z6])],[(0,[z33,z752,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z133]),(0,[z0,z1,z2,z753,z3,z4]),(0,[z0,z1,z2,z3,z4,z428]),(0,[z0,z1,z3,z75,z433,z19])],[(0,[z0,z1,z2,z198,z4,z6]),(0,[z156,z1,z374,z60,z3,z4]),(0,[z0,z754,z1,z2,z4,z6]),(0,[z53,z1,z2,z3,z47,z6]),(0,[z0,z1,z755,z2,z3,z4]),(0,[z39,z0,z1,z2,z3,z756])]],
   [[(1,[z1,z2,z3,z757,z6]),(0,[z0,z1,z2,z758,z3,z4]),(0,[z759,z0,z1,z2,z3,z4]),(0,[z424,z1,z2,z3,z4,z49]),(0,[z462,z0,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z106,z98]),(0,[z0,z1,z3,z760,z4,z6])],[(0,[z156,z1,z761,z3,z4,z6]),(0,[z94,z0,z135,z3,z4,z6]),(0,[z271,z0,z2,z402,z3,z4]),(0,[z0,z1,z2,z3,z4,z762]),(0,[z0,z763,z2,z3,z4,z6]),(0,[z0,z180,z2,z731,z3,z4]),(0,[z39,z764,z1,z2,z3,z4]),(0,[z0,z1,z2,z130,z746,z4])],[(0,[z0,z1,z2,z765,z4,z6]),(0,[z0,z1,z2,z3,z4,z766]),(0,[z0,z767,z2,z3,z4,z6]),(0,[z39,z0,z1,z257,z3,z4]),(0,[z0,z1,z2,z3,z4,z212]),(0,[z0,z768,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z769,z4]),(0,[z0,z1,z2,z3,z645,z19]),(0,[z82,z0,z1,z25,z3,z75]),(0,[z0,z1,z2,z3,z98,z98])],[(0,[z770,z0,z2,z3,z4,z6]),(0,[z0,z1,z8,z3,z4,z237]),(0,[z0,z1,z8,z3,z4,z395]),(0,[z0,z1,z255,z3,z4,z237]),(0,[z0,z1,z2,z3,z4,z93]),(0,[z0,z58,z1,z2,z93,z109])],[(0,[z0,z1,z2,z771,z3,z6]),(0,[z0,z772,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z773,z6]),(0,[z774,z0,z1,z2,z3,z6]),(0,[z0,z1,z3,z4,z775,z84]),(0,[z0,z1,z2,z61,z18,z304]),(0,[z114,z0,z1,z2,z131,z4]),(0,[z0,z1,z2,z776,z3,z4])],[(0,[z39,z0,z1,z2,z198,z4]),(0,[z0,z1,z374,z2,z30,z3]),(0,[z1,z264,z761,z3,z4,z6]),(0,[z0,z1,z777,z3,z4,z6]),(0,[z778,z0,z1,z2,z3,z4]),(0,[z0,z779,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z780])],[(0,[z95,z78,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z781]),(0,[z0,z1,z782,z2,z3,z4]),(0,[z1,z2,z3,z47,z757,z6]),(0,[z0,z1,z134,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z2,z115,z4,z110,z6]),(0,[z0,z91,z2,z3,z110,z428]),(0,[z784,z1,z2,z3,z4,z6]),(0,[z785,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z786]),(0,[z0,z1,z2,z3,z787,z4]),(0,[z0,z1,z2,z25,z164,z4]),(0,[z0,z1,z2,z3,z788,z6]),(0,[z0,z1,z2,z789,z4,z6]),(0,[z0,z1,z2,z3,z790,z4]),(0,[z39,z0,z1,z2,z791,z4]),(0,[z0,z2,z3,z4,z792,z19])]],
   [[(0,[z95,z78,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z793]),(0,[z0,z1,z2,z130,z393,z4]),(0,[z0,z500,z2,z3,z4,z288])],[(0,[z294,z527,z0,z2,z3,z6]),(0,[z225,z0,z1,z2,z3,z205]),(0,[z0,z24,z2,z3,z4,z6]),(0,[z764,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z794,z4])],[(0,[z0,z1,z2,z3,z4,z795]),(0,[z1,z2,z3,z757,z36,z6]),(0,[z0,z1,z2,z350,z3,z4]),(0,[z150,z0,z1,z2,z350,z3]),(0,[z39,z796,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z19]),(0,[z0,z1,z2,z3,z797,z6])],[(0,[z0,z798,z1,z2,z3,z6]),(0,[z21,z1,z8,z2,z89,z4]),(0,[z53,z1,z2,z3,z47,z44]),(0,[z0,z1,z2,z3,z4,z799]),(0,[z800,z0,z1,z2,z3,z4]),(0,[z148,z0,z1,z118,z103,z4]),(0,[z39,z0,z1,z3,z4,z423])],[(0,[z0,z2,z3,z801,z4,z6]),(0,[z0,z802,z2,z3,z4,z6]),(0,[z0,z1,z2,z25,z3,z187]),(0,[z332,z0,z1,z3,z4,z444])],[(0,[z0,z1,z2,z3,z4,z803]),(0,[z39,z0,z1,z2,z30,z3]),(0,[z0,z1,z2,z3,z4,z804]),(0,[z23,z0,z1,z2,z3,z44])],[(0,[z294,z0,z374,z2,z3,z4]),(0,[z53,z23,z1,z2,z3,z19]),(0,[z0,z1,z2,z805,z4,z6]),(0,[z0,z1,z806,z2,z3,z4]),(0,[z0,z1,z2,z3,z92,z98]),(0,[z148,z39,z0,z1,z103,z4]),(0,[z0,z1,z2,z61,z18,z6]),(0,[z0,z58,z1,z2,z727,z6]),(0,[z125,z0,z1,z3,z501,z4])]],
   [[(0,[z21,z2,z89,z99,z4,z6]),(0,[z0,z1,z2,z3,z4,z807]),(0,[z0,z1,z2,z3,z4,z808])],[(0,[z0,z809,z1,z2,z3,z4]),(0,[z626,z0,z135,z3,z4,z6]),(0,[z39,z0,z1,z175,z3,z4]),(0,[z0,z1,z2,z3,z677,z19]),(0,[z0,z1,z255,z2,z3,z4]),(0,[z332,z0,z1,z56,z3,z4])],[(0,[z0,z1,z2,z3,z4,z810]),(0,[z156,z332,z0,z1,z3,z4]),(0,[z23,z0,z1,z180,z2,z3]),(0,[z0,z1,z2,z3,z98,z49]),(0,[z0,z100,z9,z3,z4,z212]),(0,[z39,z0,z1,z56,z3,z57]),(0,[z811,z0,z1,z2,z3,z98])],[(0,[z21,z1,z2,z89,z4,z19]),(0,[z21,z0,z1,z2,z3,z98]),(0,[z0,z549,z2,z106,z4,z6]),(0,[z0,z91,z2,z3,z110,z19]),(0,[z39,z0,z1,z2,z3,z16]),(0,[z303,z0,z1,z2,z3,z98]),(1,[z0,z1,z2,z746,z4])],[(0,[z0,z1,z374,z2,z34,z4]),(0,[z0,z107,z2,z439,z4,z6]),(0,[z0,z812,z1,z2,z3,z98]),(0,[z85,z1,z190,z2,z3,z4]),(0,[z813,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z814,z4,z6]),(0,[z156,z59,z60,z3,z4,z6]),(0,[z39,z21,z1,z2,z89,z4]),(0,[z815,z1,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z115,z4]),(0,[z0,z1,z8,z2,z3,z98]),(0,[z0,z1,z2,z354,z4,z40])],[(0,[z0,z2,z3,z4,z816,z211]),(0,[z817,z0,z2,z3,z4,z6]),(0,[z39,z0,z1,z538,z3,z4]),(0,[z0,z1,z2,z3,z818,z98]),(0,[z0,z1,z8,z254,z3,z4])],[(0,[z0,z1,z2,z3,z4,z819])]],
   [[(0,[z774,z0,z1,z2,z3,z128]),(0,[z213,z0,z1,z2,z3,z98]),(0,[z0,z1,z820,z2,z3,z4]),(0,[z0,z1,z2,z821,z4,z6]),(0,[z0,z1,z2,z25,z3,z347]),(0,[z0,z822,z2,z3,z4,z6]),(0,[z823,z0,z1,z3,z4,z19])],[(0,[z157,z351,z1,z2,z3,z4]),(0,[z39,z0,z1,z3,z4,z363]),(0,[z0,z824,z2,z3,z4,z19]),(0,[z1,z2,z3,z4,z825,z19])],[(0,[z1,z2,z761,z3,z4,z6]),(0,[z0,z1,z826,z2,z3,z4]),(0,[z0,z1,z2,z3,z57,z98]),(0,[z39,z0,z1,z3,z399,z4])],[(0,[z0,z1,z827,z2,z3,z4]),(0,[z828,z0,z1,z2,z3,z4]),(0,[z105,z39,z1,z2,z165,z4]),(0,[z0,z420,z8,z2,z3,z4]),(0,[z0,z1,z3,z4,z829,z19]),(0,[z0,z1,z2,z3,z501,z19])],[(0,[z0,z1,z2,z34,z4,z6]),(1,[z1,z2,z739,z4,z6]),(0,[z21,z1,z2,z25,z89,z4]),(0,[z1,z2,z3,z4,z830,z6]),(0,[z831,z0,z1,z8,z2,z3])],[(0,[z0,z446,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z832]),(0,[z148,z332,z0,z1,z3,z4]),(0,[z0,z1,z2,z3,z98,z833])],[(0,[z0,z834,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z835,z6]),(0,[z53,z1,z2,z3,z328,z6]),(0,[z82,z0,z1,z3,z75,z19]),(0,[z836,z0,z1,z2,z3,z4]),(0,[z0,z1,z837,z2,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z1,z2,z839,z4,z6]),(0,[z0,z1,z2,z3,z4,z840]),(1,[z0,z1,z3,z4,z775]),(0,[z544,z0,z2,z3,z4,z142])],[(0,[z0,z1,z2,z25,z3,z4]),(0,[z0,z841,z2,z3,z4,z6]),(0,[z0,z1,z2,z842,z3,z4]),(0,[z0,z1,z8,z587,z3,z4]),(0,[z0,z1,z56,z3,z843,z6]),(0,[z0,z1,z3,z57,z843,z6]),(0,[z39,z0,z1,z639,z3,z4]),(0,[z0,z844,z8,z2,z3,z4])],[(0,[z94,z0,z112,z3,z4,z6]),(0,[z0,z845,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z846,z4])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z830]),(1,[z0,z1,z760,z4,z6])],[(0,[z548,z294,z0,z2,z4,z6]),(0,[z39,z0,z1,z2,z123,z4]),(0,[z0,z1,z2,z847,z3,z4]),(0,[z176,z0,z465,z1,z2,z4])],[(0,[z21,z0,z2,z99,z4,z6]),(0,[z0,z1,z2,z3,z122,z19]),(0,[z0,z1,z2,z3,z98,z6]),(0,[z0,z1,z2,z25,z3,z98]),(0,[z0,z1,z180,z2,z3,z86]),(0,[z0,z357,z2,z3,z4,z19])],[(0,[z0,z2,z3,z99,z4,z6]),(0,[z0,z1,z848,z2,z3,z4]),(0,[z849,z0,z1,z2,z3,z6]),(0,[z0,z1,z850,z3,z4,z6]),(0,[z225,z0,z1,z2,z3,z19]),(0,[z0,z137,z572,z2,z3,z4]),(0,[z39,z0,z1,z3,z4,z171]),(0,[z0,z1,z2,z3,z41,z19])],[(0,[z0,z851,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z2,z853,z4,z6]),(0,[z0,z1,z2,z854,z4,z6]),(0,[z0,z855,z2,z3,z4,z6])]],
   [[(1,[z1,z761,z3,z4,z6]),(0,[z39,z215,z0,z1,z3,z4]),(0,[z0,z1,z2,z3,z4,z856]),(0,[z0,z1,z2,z3,z857,z4]),(0,[z0,z1,z2,z858,z4,z6]),(0,[z0,z1,z2,z3,z4,z859]),(0,[z0,z1,z2,z3,z131,z98])],[(0,[z0,z1,z2,z860,z3,z6]),(0,[z861,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z862]),(0,[z0,z604,z2,z106,z4,z6]),(0,[z39,z0,z1,z2,z3,z863]),(0,[z0,z1,z2,z131,z746,z4])],[(0,[z0,z8,z2,z3,z99,z4]),(0,[z125,z0,z1,z255,z3,z4]),(0,[z0,z1,z864,z2,z3,z4]),(0,[z0,z1,z2,z46,z4,z40])],[(0,[z0,z1,z2,z3,z865,z4]),(0,[z866,z1,z2,z3,z4,z6]),(0,[z0,z107,z2,z62,z4,z6]),(0,[z0,z1,z2,z115,z4,z6]),(0,[z0,z1,z2,z3,z98,z29]),(0,[z0,z1,z2,z3,z118,z4]),(0,[z0,z357,z8,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z867]),(0,[z0,z1,z2,z616,z4,z40]),(0,[z0,z1,z8,z3,z4,z145])],[(0,[z0,z868,z2,z3,z4,z6]),(0,[z0,z1,z2,z869,z4,z6]),(0,[z0,z1,z102,z569,z4,z6]),(0,[z0,z1,z8,z113,z3,z4]),(0,[z0,z1,z2,z870,z3,z98])],[(0,[z548,z39,z0,z1,z2,z4]),(0,[z90,z1,z2,z3,z4,z79]),(0,[z351,z1,z2,z3,z4,z49]),(0,[z0,z1,z2,z3,z98,z40]),(0,[z0,z1,z2,z3,z120,z19]),(0,[z634,z0,z1,z2,z3,z19])],[(0,[z156,z0,z1,z2,z3,z98]),(0,[z871,z0,z1,z2,z3,z4]),(0,[z148,z0,z1,z25,z103,z4]),(0,[z0,z1,z872,z2,z3,z4]),(0,[z119,z0,z1,z2,z3,z19])]],
   [[(0,[z0,z1,z873,z2,z3,z4]),(0,[z0,z874,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z44]),(0,[z0,z1,z2,z323,z3,z4]),(0,[z0,z1,z2,z3,z101,z19]),(0,[z0,z137,z1,z2,z3,z98]),(0,[z0,z875,z2,z3,z4,z6]),(0,[z0,z1,z2,z876,z3,z4]),(0,[z104,z0,z1,z2,z3,z98]),(1,[z0,z1,z2,z727,z6])],[(0,[z0,z1,z2,z3,z4,z877]),(0,[z0,z1,z2,z3,z4,z878]),(0,[z39,z0,z1,z3,z16,z84]),(0,[z39,z0,z1,z3,z501,z4]),(0,[z0,z1,z2,z3,z4,z879])],[(0,[z0,z1,z2,z3,z4,z880])],[(0,[z0,z1,z2,z881,z4,z6]),(0,[z0,z882,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z883,z4]),(0,[z0,z100,z9,z3,z4,z6]),(0,[z0,z1,z2,z3,z884,z6]),(0,[z0,z91,z2,z115,z110,z6]),(0,[z148,z0,z1,z103,z4,z19]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z203,z31,z2,z3,z4]),(0,[z0,z1,z8,z703,z3,z4]),(0,[z0,z58,z1,z2,z25,z109])],[(0,[z0,z886,z2,z3,z4,z6]),(0,[z105,z0,z1,z2,z3,z98]),(0,[z0,z887,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z888,z6]),(0,[z332,z0,z1,z14,z3,z4])],[(0,[z0,z52,z2,z3,z4,z19]),(0,[z213,z0,z1,z2,z3,z889]),(0,[z890,z0,z1,z2,z3,z4]),(0,[z39,z53,z1,z2,z3,z47]),(0,[z0,z1,z2,z3,z47,z98]),(0,[z0,z1,z2,z891,z4,z6]),(0,[z332,z0,z1,z135,z3,z4]),(0,[z892,z0,z1,z2,z3,z4]),(0,[z0,z58,z1,z2,z3,z98]),(0,[z0,z1,z2,z3,z10,z19]),(0,[z0,z1,z893,z3,z4,z19])],[(0,[z0,z1,z894,z2,z3,z4]),(0,[z105,z0,z420,z2,z4,z6]),(0,[z39,z97,z0,z1,z2,z3]),(0,[z0,z1,z2,z3,z75,z392]),(0,[z39,z0,z895,z2,z3,z4]),(0,[z896,z0,z1,z3,z4,z6]),(0,[z222,z0,z1,z2,z488,z4])],[(0,[z0,z1,z2,z3,z4,z128]),(0,[z0,z1,z2,z60,z3,z98]),(0,[z0,z2,z3,z897,z4,z6]),(0,[z85,z1,z2,z3,z4,z79]),(0,[z0,z898,z1,z2,z3,z4])]],
   [[(0,[z95,z475,z2,z3,z4,z6]),(0,[z94,z39,z0,z135,z3,z4]),(0,[z0,z1,z2,z3,z4,z899])],[(0,[z0,z1,z2,z164,z4,z6]),(0,[z0,z1,z8,z3,z4,z602]),(0,[z0,z1,z2,z3,z139,z19]),(1,[z0,z710,z3,z4,z6]),(0,[z0,z1,z2,z62,z3,z98]),(0,[z0,z1,z2,z3,z4,z900])],[(0,[z0,z1,z901,z2,z3,z4]),(0,[z0,z1,z2,z123,z4,z6]),(0,[z0,z91,z2,z3,z718,z6]),(0,[z0,z1,z2,z3,z4,z902]),(0,[z148,z0,z1,z2,z3,z98])],[(0,[z0,z52,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z903]),(0,[z0,z224,z2,z3,z4,z19]),(0,[z0,z91,z1,z2,z3,z98]),(0,[z0,z1,z904,z2,z3,z4]),(0,[z0,z905,z2,z3,z4,z6]),(0,[z0,z595,z1,z2,z3,z98]),(0,[z39,z0,z1,z2,z61,z18]),(0,[z0,z357,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z906])],[(0,[z223,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z907]),(0,[z1,z2,z739,z165,z4,z6]),(0,[z0,z908,z2,z3,z4,z6]),(0,[z332,z0,z1,z9,z3,z4])],[(0,[z0,z1,z2,z3,z909,z6]),(0,[z213,z1,z264,z3,z4,z19]),(0,[z0,z1,z2,z3,z910,z4]),(0,[z0,z911,z1,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z912]),(0,[z0,z1,z2,z3,z913,z4]),(0,[z0,z1,z2,z3,z329,z19]),(0,[z114,z0,z1,z2,z537,z4])],[(0,[z0,z1,z2,z3,z4,z914]),(0,[z0,z1,z915,z2,z3,z4]),(0,[z39,z0,z1,z535,z3,z4]),(0,[z0,z1,z2,z25,z3,z521]),(0,[z0,z1,z2,z3,z4,z916])],[(0,[z548,z0,z1,z2,z25,z4]),(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z72,z8,z2,z106,z4]),(0,[z114,z0,z1,z2,z3,z98])]],
   [[(0,[z156,z534,z1,z60,z3,z4]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z53,z0,z1,z2,z3,z392])],[(0,[z0,z1,z2,z3,z333,z19]),(0,[z0,z224,z8,z2,z3,z4]),(0,[z0,z107,z2,z725,z4,z6])],[(0,[z0,z1,z8,z2,z198,z4]),(0,[z156,z527,z1,z60,z3,z6]),(0,[z39,z0,z107,z2,z62,z4])],[(0,[z0,z1,z2,z3,z205,z6]),(0,[z0,z1,z2,z3,z4,z98])],[(0,[z0,z1,z919,z3,z4,z6]),(0,[z0,z1,z2,z920,z4,z6]),(0,[z0,z1,z2,z3,z4,z921]),(0,[z0,z1,z2,z434,z3,z19]),(0,[z0,z1,z56,z2,z3,z98]),(0,[z0,z1,z2,z130,z3,z98])],[(0,[z0,z1,z2,z3,z922,z6]),(0,[z0,z107,z1,z2,z3,z98]),(0,[z0,z1,z102,z14,z4,z19]),(0,[z332,z0,z1,z3,z4,z75]),(0,[z0,z58,z1,z2,z109,z523])],[(0,[z156,z178,z60,z3,z4,z6]),(0,[z0,z534,z1,z2,z30,z3]),(0,[z39,z0,z2,z3,z99,z4]),(0,[z701,z0,z1,z2,z3,z19]),(0,[z39,z0,z1,z2,z3,z923])],[(0,[z0,z752,z2,z3,z4,z6]),(0,[z0,z1,z2,z924,z4,z6]),(0,[z1,z761,z60,z3,z4,z6]),(0,[z0,z9,z710,z3,z4,z6]),(0,[z0,z1,z2,z925,z4,z6]),(0,[z0,z1,z926,z2,z3,z4]),(0,[z0,z1,z14,z760,z4,z6]),(0,[z0,z1,z2,z3,z927,z4]),(0,[z39,z0,z868,z2,z3,z4]),(0,[z0,z403,z2,z3,z4,z523])]],
   [[(0,[z0,z1,z2,z928,z4,z6]),(0,[z156,z294,z60,z3,z4,z6]),(0,[z0,z1,z102,z14,z15,z4])],[(0,[z0,z1,z2,z3,z220,z4]),(0,[z0,z1,z2,z25,z776,z3])],[(0,[z0,z1,z929,z3,z4,z6]),(0,[z39,z23,z1,z2,z3,z36])],[(0,[z0,z52,z2,z25,z3,z4]),(0,[z1,z2,z3,z739,z4,z6]),(0,[z0,z1,z2,z3,z4,z930]),(0,[z0,z1,z2,z3,z398,z19])],[(0,[z0,z1,z2,z3,z931,z4]),(0,[z0,z1,z932,z2,z3,z6]),(0,[z933,z0,z1,z2,z30,z3]),(0,[z0,z1,z934,z2,z30,z3]),(0,[z39,z213,z1,z264,z3,z4]),(0,[z935,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z936,z4]),(0,[z0,z1,z2,z3,z205,z40]),(0,[z0,z1,z2,z3,z4,z168]),(0,[z39,z937,z1,z2,z3,z4]),(0,[z39,z0,z1,z255,z3,z4])],[(0,[z0,z2,z135,z164,z4,z6])],[(0,[z557,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z209,z19]),(0,[z1,z2,z3,z4,z49,z830]),(0,[z0,z1,z2,z3,z4,z938]),(0,[z151,z0,z1,z2,z3,z98]),(0,[z0,z1,z2,z939,z3,z4]),(0,[z0,z940,z2,z3,z4,z6])],[(0,[z0,z107,z2,z305,z4,z6]),(0,[z0,z1,z2,z3,z4,z941]),(0,[z39,z33,z204,z2,z3,z4]),(0,[z527,z0,z1,z8,z2,z3]),(0,[z0,z1,z942,z3,z4,z6]),(0,[z0,z72,z2,z25,z106,z4])]],
   [[(0,[z0,z1,z2,z3,z943,z6]),(0,[z0,z1,z2,z846,z4,z6]),(0,[z0,z1,z2,z3,z944,z6]),(0,[z0,z100,z710,z3,z4,z6]),(0,[z0,z1,z2,z3,z621,z19]),(0,[z148,z0,z1,z69,z103,z4]),(0,[z39,z0,z1,z2,z3,z944]),(0,[z225,z1,z2,z340,z3,z4])],[(0,[z0,z945,z2,z3,z4,z6]),(0,[z0,z224,z2,z25,z3,z4]),(0,[z82,z0,z1,z3,z843,z6]),(0,[z0,z728,z2,z3,z4,z6]),(0,[z946,z0,z1,z2,z3,z4])],[(0,[z0,z1,z8,z102,z14,z4]),(0,[z0,z1,z2,z14,z3,z98]),(0,[z0,z2,z731,z3,z4,z6]),(0,[z0,z496,z2,z116,z3,z4])],[(0,[z0,z224,z2,z3,z4,z6]),(0,[z213,z1,z264,z25,z3,z4]),(0,[z0,z1,z2,z3,z98,z36]),(0,[z947,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z135,z3,z98]),(0,[z0,z1,z2,z4,z948,z6])],[(0,[z0,z1,z572,z2,z3,z98]),(0,[z39,z0,z1,z2,z3,z949]),(0,[z0,z1,z2,z130,z4,z40])],[(0,[z213,z1,z264,z3,z4,z6]),(1,[z0,z2,z3,z718,z6]),(0,[z0,z950,z2,z3,z4,z6]),(0,[z0,z1,z2,z951,z3,z4])],[(0,[z204,z752,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z952,z4]),(0,[z0,z1,z2,z3,z4,z953]),(0,[z48,z0,z1,z2,z3,z98]),(0,[z0,z1,z2,z725,z4,z6]),(0,[z0,z2,z3,z4,z29,z816]),(1,[z0,z1,z2,z3,z98])],[(0,[z0,z1,z2,z3,z4,z954]),(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z1,z760,z103,z4,z6]),(0,[z956,z0,z1,z2,z3,z98])]],
   [[(0,[z0,z1,z2,z957,z3,z4]),(0,[z0,z1,z958,z2,z3,z4]),(0,[z0,z420,z2,z3,z4,z19]),(0,[z959,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z344]),(0,[z90,z0,z1,z2,z3,z205]),(0,[z0,z1,z2,z3,z718,z6])],[(0,[z0,z1,z2,z3,z4,z960]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z39,z0,z91,z2,z3,z110]),(0,[z150,z0,z1,z2,z25,z3])],[(0,[z156,z52,z60,z3,z4,z6]),(0,[z0,z1,z2,z962,z3,z4]),(0,[z0,z1,z2,z3,z4,z963]),(0,[z0,z1,z2,z3,z560,z19]),(0,[z0,z1,z2,z3,z4,z230]),(0,[z0,z1,z2,z3,z16,z19]),(0,[z0,z1,z2,z3,z4,z304]),(0,[z0,z1,z2,z3,z964,z4]),(0,[z0,z1,z2,z3,z487,z19])],[(0,[z33,z204,z2,z3,z4,z19]),(0,[z97,z0,z1,z8,z2,z3]),(0,[z0,z100,z9,z3,z4,z168]),(0,[z0,z1,z56,z2,z3,z230])],[(0,[z0,z1,z2,z3,z4,z965]),(0,[z966,z0,z1,z2,z3,z4])],[(0,[z1,z2,z89,z739,z4,z6]),(0,[z967,z0,z1,z2,z3,z4]),(0,[z90,z1,z2,z3,z4,z830])],[(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z1,z2,z969,z3,z4]),(0,[z0,z1,z180,z2,z3,z4]),(0,[z39,z0,z1,z2,z970,z4]),(0,[z39,z0,z1,z3,z4,z775]),(0,[z0,z971,z8,z2,z3,z4]),(0,[z0,z1,z2,z776,z3,z26])]],
   [[(0,[z0,z1,z2,z972,z3,z4]),(0,[z156,z548,z1,z60,z4,z6]),(0,[z39,z0,z1,z2,z34,z4]),(0,[z0,z2,z3,z4,z6,z973]),(0,[z0,z1,z2,z3,z4,z889]),(0,[z0,z357,z2,z3,z4,z93])],[(0,[z0,z1,z2,z3,z4,z974]),(0,[z0,z1,z2,z3,z4,z975]),(0,[z0,z976,z1,z2,z3,z6]),(0,[z0,z1,z8,z2,z123,z4]),(0,[z0,z1,z2,z3,z98,z75])],[(0,[z33,z204,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z1,z2,z3,z4,z978]),(0,[z0,z1,z2,z3,z4,z979]),(0,[z105,z1,z2,z285,z4,z6]),(0,[z0,z980,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z792,z6]),(0,[z390,z0,z1,z8,z3,z4]),(0,[z82,z0,z1,z8,z3,z75]),(0,[z39,z0,z1,z2,z3,z981]),(0,[z0,z1,z3,z4,z982,z19]),(0,[z0,z1,z2,z46,z4,z410])],[(0,[z0,z1,z983,z3,z4,z6]),(0,[z0,z178,z2,z3,z4,z19]),(0,[z39,z0,z1,z8,z3,z4]),(0,[z39,z0,z834,z2,z3,z4]),(0,[z0,z1,z180,z2,z3,z98]),(0,[z0,z984,z8,z2,z3,z4]),(0,[z0,z1,z2,z61,z129,z18])],[(0,[z985,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z986]),(0,[z23,z0,z1,z2,z3,z98])],[(0,[z512,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z269,z19]),(0,[z0,z1,z2,z464,z3,z19])],[(0,[z987,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z547,z3,z19]),(0,[z631,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z988]),(0,[z0,z1,z2,z3,z4,z989]),(0,[z0,z1,z2,z3,z4,z248]),(0,[z0,z1,z2,z3,z990,z98])],[(0,[z0,z2,z3,z991,z4,z6]),(0,[z0,z1,z2,z3,z279,z19]),(0,[z39,z0,z1,z8,z3,z98]),(0,[z332,z0,z1,z8,z3,z4])]],
   [[(0,[z0,z1,z2,z4,z992,z6]),(0,[z73,z0,z2,z3,z92,z19]),(0,[z0,z993,z2,z3,z4,z6]),(0,[z303,z0,z1,z2,z440,z4]),(0,[z0,z1,z2,z61,z727,z6])],[(0,[z0,z1,z2,z994,z4,z6]),(0,[z0,z178,z8,z2,z3,z4]),(0,[z213,z1,z264,z3,z4,z128]),(0,[z995,z0,z1,z2,z3,z4]),(0,[z23,z1,z2,z3,z36,z209]),(0,[z332,z53,z0,z1,z2,z3]),(0,[z48,z97,z1,z2,z3,z49]),(0,[z0,z1,z2,z3,z4,z996]),(0,[z154,z0,z1,z2,z3,z98])],[(0,[z39,z95,z78,z2,z3,z4]),(0,[z0,z1,z2,z997,z3,z4]),(0,[z0,z1,z2,z3,z4,z422]),(0,[z0,z1,z2,z3,z4,z998]),(0,[z39,z0,z1,z2,z3,z999]),(0,[z229,z0,z1,z2,z3,z230])],[(0,[z0,z1,z1000,z2,z3,z4]),(0,[z39,z0,z1,z3,z4,z520]),(0,[z0,z72,z2,z106,z4,z19])],[(0,[z0,z2,z3,z4,z1001,z6]),(0,[z0,z1,z2,z1002,z3,z4]),(0,[z0,z1,z1003,z2,z3,z4])],[(0,[z0,z1,z2,z1004,z4,z6]),(0,[z0,z1,z1005,z2,z3,z4]),(0,[z53,z1,z8,z2,z3,z47]),(0,[z0,z1,z9,z2,z3,z98])],[(0,[z0,z1,z2,z198,z25,z4]),(0,[z0,z1,z2,z3,z290,z19]),(0,[z21,z1,z2,z89,z4,z6]),(0,[z105,z1,z2,z165,z4,z19]),(0,[z0,z1,z2,z1006,z4,z6]),(0,[z0,z1,z2,z25,z3,z483]),(0,[z0,z91,z2,z3,z110,z6]),(0,[z0,z420,z2,z25,z3,z4]),(0,[z0,z1,z8,z3,z4,z433]),(0,[z0,z357,z2,z4,z109,z6]),(0,[z424,z0,z1,z2,z3,z19])],[(0,[z0,z1007,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1008]),(0,[z0,z2,z3,z4,z816,z6]),(0,[z125,z0,z1,z2,z3,z4])]],
   [[(0,[z0,z1,z1009,z2,z3,z6]),(0,[z0,z1,z2,z1010,z3,z4]),(0,[z0,z420,z2,z3,z4,z6]),(0,[z437,z0,z1,z2,z3,z98])],[(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z1,z2,z1012,z3,z19]),(0,[z0,z1,z2,z440,z131,z4])],[(0,[z33,z204,z2,z25,z3,z4]),(0,[z527,z0,z1,z2,z34,z6]),(0,[z0,z2,z3,z1013,z4,z6]),(0,[z90,z595,z1,z2,z3,z4]),(0,[z1014,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1015]),(0,[z0,z1,z2,z3,z4,z1016])],[(1,[z0,z1,z2,z3,z889]),(0,[z823,z0,z1,z3,z4,z6]),(0,[z0,z1,z1017,z2,z3,z4]),(0,[z0,z1,z2,z1018,z3,z4]),(0,[z73,z0,z2,z3,z647,z6]),(0,[z0,z1,z2,z3,z1019,z4]),(0,[z0,z1,z102,z25,z14,z4]),(0,[z125,z0,z1,z2,z3,z98]),(0,[z0,z1,z56,z3,z57,z19]),(0,[z70,z0,z1,z2,z537,z4])],[(0,[z0,z1,z2,z791,z4,z6]),(0,[z0,z824,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z76,z2,z62,z4,z6]),(0,[z0,z1,z3,z843,z75,z6]),(0,[z82,z0,z1,z2,z3,z98]),(0,[z1,z2,z3,z4,z825,z6])],[(0,[z0,z1,z1021,z2,z3,z4]),(0,[z548,z0,z1,z2,z4,z19]),(0,[z39,z0,z1,z426,z3,z4]),(0,[z0,z1,z3,z4,z237,z775]),(0,[z0,z1,z2,z1022,z4,z19])],[(0,[z95,z0,z2,z164,z4,z6]),(0,[z0,z844,z2,z3,z4,z6]),(0,[z0,z1,z2,z1023,z3,z4]),(0,[z0,z1,z2,z3,z4,z1024]),(0,[z0,z1,z2,z3,z1025,z4]),(0,[z1026,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z843,z6]),(0,[z0,z1,z3,z4,z829,z6])],[(0,[z0,z2,z3,z1027,z4,z6]),(0,[z271,z0,z1,z2,z3,z98]),(0,[z0,z1,z2,z3,z57,z392]),(0,[z0,z1,z2,z61,z25,z18])]],
   [[(0,[z0,z1,z2,z3,z1028,z6]),(0,[z0,z1,z2,z3,z4,z1029]),(0,[z39,z0,z224,z2,z3,z4]),(0,[z0,z1,z2,z3,z1030,z6]),(0,[z94,z0,z710,z3,z4,z6]),(0,[z0,z370,z2,z3,z4,z29]),(0,[z0,z1,z8,z2,z61,z18])],[(0,[z0,z178,z2,z25,z3,z4]),(0,[z196,z0,z2,z3,z153,z4])],[(0,[z0,z1,z78,z2,z3,z98]),(0,[z213,z1,z8,z264,z3,z4]),(0,[z0,z1,z2,z3,z4,z1031]),(0,[z48,z1,z2,z3,z4,z328]),(0,[z0,z1,z2,z3,z751,z6]),(0,[z82,z0,z1,z3,z75,z6]),(0,[z0,z1,z258,z2,z3,z4]),(0,[z250,z0,z1,z2,z3,z98]),(0,[z0,z1,z2,z3,z18,z98])],[(0,[z33,z2,z414,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1032]),(0,[z127,z1,z2,z3,z4,z339])],[(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z1,z2,z61,z274,z6]),(0,[z554,z0,z1,z2,z25,z3])],[(0,[z0,z1,z1034,z2,z3,z4]),(0,[z0,z1,z2,z4,z1035,z6]),(0,[z0,z1036,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1037]),(0,[z53,z1,z2,z25,z3,z47]),(0,[z0,z1,z8,z2,z3,z205]),(0,[z0,z107,z2,z246,z4,z6]),(0,[z39,z0,z1,z3,z4,z539]),(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z2,z3,z4,z775]),(0,[z0,z58,z1,z2,z109,z19])],[(0,[z0,z1,z2,z3,z4,z1039]),(0,[z68,z0,z1,z8,z3,z4]),(0,[z154,z0,z370,z2,z3,z4]),(0,[z0,z1,z2,z3,z26,z19])],[(0,[z0,z1,z2,z3,z4,z1040]),(0,[z0,z1041,z2,z3,z4,z6]),(0,[z0,z1042,z1,z2,z3,z4]),(0,[z0,z403,z2,z3,z4,z19]),(0,[z0,z1043,z2,z3,z4,z19])]],
   [[(0,[z0,z1,z2,z3,z1044,z4]),(0,[z0,z895,z2,z3,z4,z6]),(0,[z548,z0,z534,z1,z2,z4]),(1,[z1,z2,z3,z4,z830]),(0,[z48,z1,z2,z3,z4,z830]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z0,z357,z2,z3,z4,z6]),(0,[z0,z1,z2,z760,z4,z6]),(0,[z150,z0,z1,z2,z3,z98])],[(0,[z0,z1,z2,z3,z4,z1046]),(0,[z0,z2,z3,z4,z1047,z6]),(0,[z0,z1,z2,z1048,z3,z4]),(0,[z598,z0,z1,z2,z131,z4]),(0,[z39,z0,z58,z1,z2,z109])],[(0,[z0,z1,z2,z3,z4,z1049])],[(0,[z0,z1,z2,z1050,z4,z6]),(0,[z1051,z0,z2,z3,z4,z6]),(0,[z97,z0,z1,z2,z3,z209]),(0,[z1,z2,z3,z4,z1052,z6]),(0,[z0,z1,z2,z3,z4,z1053]),(0,[z0,z1,z1054,z2,z3,z4])],[(0,[z0,z9,z514,z3,z4,z6]),(0,[z21,z1,z2,z494,z4,z6])],[(0,[z0,z1,z1055,z3,z4,z6]),(0,[z0,z1,z1056,z3,z4,z6]),(0,[z0,z2,z30,z59,z3,z6]),(0,[z548,z0,z1,z374,z2,z4]),(0,[z0,z1,z2,z3,z695,z19]),(0,[z0,z107,z8,z2,z62,z4]),(0,[z0,z91,z2,z123,z110,z6]),(0,[z0,z1,z2,z3,z4,z140]),(0,[z39,z0,z1,z2,z3,z734]),(0,[z39,z0,z403,z2,z3,z4]),(0,[z0,z403,z8,z2,z3,z4])],[(0,[z105,z1,z2,z165,z4,z6]),(0,[z0,z2,z3,z4,z1057,z19])],[(0,[z796,z1,z2,z3,z4,z6]),(0,[z332,z0,z1,z3,z75,z19])]],
   [[(0,[z0,z1,z2,z3,z923,z6]),(0,[z156,z1,z8,z60,z3,z4]),(0,[z0,z1,z374,z2,z3,z4]),(0,[z0,z446,z2,z3,z110,z6]),(0,[z0,z1,z2,z1058,z4,z6])],[(0,[z105,z0,z2,z99,z4,z6]),(0,[z0,z1,z2,z1059,z3,z4]),(0,[z0,z1,z2,z3,z949,z6]),(0,[z271,z0,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z98,z211]),(0,[z148,z0,z420,z103,z4,z6]),(0,[z0,z1,z2,z3,z999,z6]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z1,z2,z3,z4,z1061]),(0,[z0,z1062,z1,z2,z3,z4])],[(0,[z33,z204,z2,z164,z4,z6])],[(0,[z0,z1,z2,z34,z25,z4]),(0,[z527,z0,z1,z2,z3,z19]),(0,[z213,z1,z264,z3,z4,z344]),(0,[z0,z1,z2,z3,z1063,z4]),(0,[z0,z1,z56,z3,z57,z6]),(0,[z0,z1,z703,z3,z57,z6]),(0,[z0,z1,z2,z4,z727,z6])],[(0,[z0,z1,z934,z2,z3,z4]),(0,[z0,z1,z2,z3,z128,z889]),(0,[z53,z1,z2,z323,z3,z47]),(0,[z48,z1,z2,z3,z49,z205]),(0,[z39,z0,z420,z2,z3,z4]),(0,[z82,z0,z1,z2,z3,z230]),(0,[z0,z1,z2,z350,z3,z16])],[(0,[z0,z1,z2,z1064,z3,z4]),(0,[z0,z2,z59,z3,z4,z19]),(0,[z53,z1,z2,z3,z757,z6]),(0,[z0,z1,z2,z25,z3,z205]),(0,[z0,z1,z1065,z2,z3,z4]),(0,[z0,z728,z180,z2,z3,z4]),(0,[z0,z1,z2,z3,z363,z19])],[(0,[z0,z1,z8,z2,z30,z3]),(0,[z23,z1,z8,z2,z3,z36]),(0,[z148,z0,z1,z103,z4,z6]),(0,[z0,z1,z2,z3,z4,z341]),(0,[z0,z1,z2,z61,z3,z98]),(0,[z0,z1,z2,z746,z4,z6])],[(0,[z0,z1,z2,z1066,z4,z6]),(0,[z33,z0,z2,z164,z4,z6]),(0,[z0,z100,z2,z164,z4,z6]),(0,[z23,z652,z1,z2,z3,z6]),(0,[z148,z0,z1,z8,z103,z4]),(0,[z0,z1,z2,z3,z1067,z98]),(0,[z0,z1,z8,z506,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z1068]),(0,[z0,z52,z2,z3,z4,z6]),(0,[z156,z1,z30,z60,z3,z6]),(0,[z0,z1,z2,z89,z3,z98]),(0,[z0,z1,z2,z3,z131,z205]),(0,[z0,z2,z725,z3,z4,z6]),(0,[z0,z1,z893,z3,z4,z6]),(0,[z1,z2,z3,z4,z6,z1069])],[(0,[z39,z0,z1,z2,z3,z4]),(0,[z0,z1070,z2,z3,z4,z6]),(0,[z53,z0,z1,z180,z2,z3])],[(0,[z294,z0,z2,z3,z4,z19]),(0,[z0,z1071,z2,z3,z4,z6]),(0,[z1072,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1073]),(0,[z0,z1,z2,z3,z1074,z4]),(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z1,z8,z56,z3,z57]),(0,[z0,z1,z2,z3,z86,z19]),(0,[z0,z1,z2,z727,z109,z6])],[(0,[z33,z204,z2,z198,z4,z6]),(0,[z0,z1,z2,z1076,z4,z6]),(0,[z156,z1,z60,z3,z4,z19]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z0,z1,z2,z350,z3,z19]),(0,[z0,z1,z8,z2,z3,z16]),(0,[z0,z1,z2,z3,z16,z98])],[(0,[z453,z0,z2,z106,z4,z6]),(0,[z94,z0,z503,z135,z3,z4]),(0,[z63,z0,z1,z2,z393,z4])],[(0,[z94,z0,z1,z2,z3,z98]),(1,[z0,z2,z725,z4,z6]),(0,[z0,z1,z8,z2,z115,z4]),(0,[z332,z0,z1,z2,z3,z4]),(0,[z82,z0,z1,z3,z329,z75]),(0,[z39,z0,z1,z2,z3,z98]),(0,[z0,z403,z2,z25,z3,z4]),(0,[z0,z58,z1,z2,z109,z6])],[(0,[z0,z1,z2,z3,z4,z1078]),(0,[z548,z527,z0,z1,z2,z6]),(0,[z0,z1,z2,z3,z4,z192]),(0,[z21,z1,z2,z739,z4,z6]),(0,[z0,z8,z2,z731,z3,z4])],[(0,[z95,z0,z1,z2,z3,z98]),(0,[z0,z1,z2,z3,z391,z19]),(0,[z39,z0,z855,z2,z3,z4]),(0,[z0,z1,z2,z746,z4,z40]),(0,[z1079,z1,z2,z3,z4,z19])]],
   [[(0,[z33,z2,z3,z494,z4,z6]),(0,[z294,z0,z8,z2,z3,z4]),(0,[z0,z534,z1,z2,z34,z4]),(0,[z0,z1,z2,z3,z4,z1080]),(0,[z97,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z1081]),(0,[z0,z1,z1082,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1083])],[(0,[z148,z0,z1,z689,z4,z6]),(0,[z0,z1,z2,z3,z1037,z19]),(0,[z0,z2,z3,z1084,z4,z6]),(0,[z0,z1,z2,z3,z4,z1085]),(0,[z0,z1,z1086,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1087]),(0,[z332,z0,z1,z2,z3,z98])],[(0,[z0,z1088,z1,z2,z3,z4]),(0,[z0,z107,z2,z62,z25,z4])],[(0,[z0,z1,z2,z1089,z4,z6]),(0,[z0,z1,z2,z3,z4,z1090]),(0,[z0,z1091,z2,z3,z4,z6]),(0,[z39,z1092,z1,z2,z3,z4])],[(1,[z332,z0,z1,z3,z75]),(0,[z0,z1,z8,z3,z4,z775])],[(0,[z0,z1,z2,z3,z1093,z6]),(0,[z0,z1,z8,z2,z34,z4]),(0,[z527,z0,z1,z2,z25,z3]),(0,[z0,z1,z2,z3,z1094,z4]),(0,[z0,z1,z2,z3,z233,z19])],[(0,[z0,z1,z2,z3,z4,z1095]),(0,[z0,z2,z59,z34,z4,z6]),(0,[z0,z1,z2,z1096,z3,z4]),(0,[z0,z389,z2,z106,z4,z6]),(0,[z21,z224,z2,z89,z4,z6]),(0,[z23,z1,z2,z25,z3,z36]),(0,[z23,z0,z1,z2,z3,z1037]),(0,[z0,z1,z2,z3,z408,z19]),(0,[z0,z1,z2,z3,z4,z329]),(0,[z0,z1,z2,z130,z581,z4])],[(0,[z1,z752,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z230,z19])]],
   [[(0,[z0,z2,z25,z3,z99,z4]),(0,[z0,z137,z2,z3,z4,z211]),(0,[z0,z1,z102,z14,z4,z6]),(0,[z0,z1,z2,z3,z4,z392]),(0,[z0,z1,z56,z350,z3,z57]),(0,[z39,z0,z1,z3,z98,z84])],[(0,[z0,z1,z2,z1097,z3,z4]),(0,[z0,z1,z2,z3,z75,z19]),(0,[z424,z1,z2,z174,z3,z4])],[(0,[z415,z0,z135,z3,z4,z6]),(0,[z0,z1,z2,z970,z4,z6]),(0,[z294,z0,z2,z30,z3,z6]),(0,[z1098,z0,z1,z2,z3,z4]),(0,[z0,z137,z2,z3,z153,z4]),(0,[z0,z1,z2,z3,z98,z1099])],[(0,[z294,z0,z2,z34,z4,z6]),(0,[z0,z2,z59,z25,z3,z4]),(0,[z0,z1100,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z757,z6]),(0,[z1092,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z98,z237]),(0,[z0,z1,z2,z25,z3,z16]),(0,[z0,z1,z2,z491,z581,z4])],[(1,[z752,z2,z3,z4,z6]),(0,[z0,z1,z1101,z2,z3,z4]),(0,[z53,z1,z2,z3,z47,z19]),(0,[z0,z72,z1,z2,z3,z98])],[(0,[z95,z601,z2,z3,z4,z6]),(0,[z0,z1,z8,z287,z3,z4]),(0,[z0,z1,z2,z25,z115,z4]),(0,[z0,z91,z8,z2,z3,z110]),(0,[z0,z1,z2,z3,z4,z1102]),(0,[z0,z1,z2,z1012,z3,z4]),(0,[z0,z1103,z1,z2,z3,z4]),(0,[z490,z1,z2,z202,z3,z4])],[(0,[z0,z1,z2,z3,z1104,z6]),(0,[z94,z0,z135,z3,z4,z19]),(0,[z0,z2,z725,z106,z4,z6]),(0,[z0,z137,z2,z3,z4,z816]),(0,[z0,z1,z2,z25,z3,z584])],[(0,[z1105,z0,z1,z3,z4,z6]),(0,[z0,z1,z2,z30,z34,z6]),(0,[z332,z213,z0,z1,z3,z4]),(0,[z0,z1,z2,z1106,z3,z4]),(0,[z0,z1,z2,z291,z3,z19]),(0,[z0,z1,z2,z705,z3,z19]),(0,[z0,z1,z180,z2,z3,z57])]],
   [[(0,[z156,z1,z34,z60,z4,z6]),(0,[z294,z0,z2,z25,z3,z4]),(0,[z0,z1,z2,z3,z889,z6]),(0,[z0,z1,z2,z1107,z3,z4]),(0,[z271,z0,z2,z3,z4,z142]),(0,[z39,z0,z1,z295,z3,z4])],[(0,[z0,z1,z2,z1108,z4,z6]),(0,[z156,z1,z60,z25,z3,z4]),(0,[z0,z1,z2,z3,z4,z425]),(0,[z0,z1,z2,z123,z25,z4]),(0,[z0,z370,z1,z2,z3,z98])],[(0,[z82,z0,z1,z258,z3,z75]),(0,[z0,z1,z2,z25,z3,z19]),(0,[z0,z1,z777,z3,z4,z19])],[(0,[z53,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z1109]),(0,[z39,z0,z357,z2,z3,z4])],[(0,[z0,z1,z2,z440,z3,z98])],[(0,[z95,z78,z2,z3,z4,z19]),(0,[z39,z0,z1,z2,z3,z1110])],[(0,[z0,z1,z298,z2,z3,z19]),(0,[z548,z0,z1,z8,z2,z4]),(0,[z0,z1,z2,z4,z1111,z6]),(0,[z0,z1,z2,z3,z355,z19]),(0,[z1112,z0,z1,z2,z3,z4]),(0,[z48,z1,z2,z202,z3,z4]),(0,[z0,z1,z1113,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1114]),(0,[z0,z24,z2,z3,z4,z19])],[(0,[z0,z1,z2,z3,z4,z1115]),(0,[z0,z1,z2,z3,z1116,z6]),(0,[z39,z0,z100,z9,z3,z4]),(0,[z0,z58,z357,z2,z109,z6]),(0,[z1079,z1,z2,z3,z4,z6])]],
   [[(0,[z33,z0,z1,z2,z3,z98]),(0,[z48,z1,z2,z3,z4,z49]),(0,[z0,z1,z1117,z2,z3,z4]),(0,[z0,z100,z1,z2,z3,z98]),(0,[z0,z779,z8,z2,z3,z4])],[(0,[z0,z1118,z1,z2,z3,z4]),(0,[z127,z1,z2,z3,z4,z79]),(0,[z0,z1,z2,z115,z4,z425]),(0,[z0,z1,z2,z3,z98,z110]),(0,[z0,z1,z2,z3,z4,z1119]),(0,[z0,z1,z1120,z2,z3,z4]),(0,[z104,z595,z1,z2,z3,z4])],[(0,[z1121,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1122]),(0,[z39,z0,z1,z3,z4,z662]),(0,[z0,z1,z2,z3,z4,z1123]),(0,[z0,z1,z2,z3,z1124,z4]),(0,[z0,z1,z1125,z2,z3,z4])],[(0,[z95,z78,z8,z2,z3,z4]),(0,[z0,z1,z2,z1126,z4,z6]),(0,[z0,z1,z2,z3,z4,z209]),(0,[z0,z1,z2,z25,z3,z74]),(0,[z157,z0,z1,z2,z3,z98]),(0,[z250,z0,z572,z2,z3,z4]),(0,[z0,z1,z2,z2,z3,z98]),(0,[z831,z0,z1,z2,z3,z6])],[(0,[z0,z971,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1127]),(0,[z23,z1,z2,z3,z36,z133]),(0,[z1128,z0,z1,z2,z3,z4]),(0,[z73,z0,z8,z2,z3,z92]),(0,[z0,z24,z8,z2,z3,z4]),(0,[z82,z0,z1,z3,z75,z392]),(0,[z0,z1,z2,z61,z18,z19]),(0,[z114,z0,z1,z2,z488,z4])],[(0,[z0,z91,z2,z25,z3,z110]),(0,[z0,z1,z2,z3,z4,z1129]),(0,[z0,z1130,z2,z3,z4,z6])],[(0,[z0,z482,z1,z2,z3,z19]),(0,[z0,z1,z2,z574,z3,z19]),(0,[z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z26,z98]),(0,[z0,z1,z2,z711,z3,z6])],[(0,[z33,z204,z2,z3,z4,z6]),(0,[z0,z2,z3,z92,z718,z6]),(0,[z0,z1,z56,z25,z3,z57]),(0,[z0,z1,z8,z169,z3,z4])]],
   [[(0,[z0,z374,z2,z59,z3,z4]),(0,[z0,z1131,z1,z2,z3,z4]),(0,[z1132,z0,z1,z2,z3,z4]),(0,[z53,z127,z1,z2,z3,z19]),(0,[z0,z984,z2,z3,z4,z6]),(0,[z0,z1,z2,z1133,z3,z4]),(0,[z0,z1,z2,z3,z329,z98])],[(0,[z0,z1,z503,z2,z3,z4]),(0,[z0,z1,z2,z25,z3,z185]),(0,[z0,z1,z2,z3,z1134,z4])],[(0,[z39,z0,z1,z2,z164,z4]),(0,[z0,z1,z2,z3,z4,z1135]),(0,[z0,z403,z2,z3,z4,z93])],[(0,[z0,z1,z3,z1136,z4,z6]),(0,[z0,z1,z2,z3,z4,z1137]),(0,[z0,z1,z2,z1138,z3,z4]),(0,[z0,z1,z2,z1139,z3,z4])],[(0,[z0,z1140,z2,z3,z4,z6]),(0,[z527,z0,z1,z2,z3,z907]),(0,[z94,z0,z135,z25,z3,z4]),(0,[z0,z1,z2,z1141,z4,z6]),(0,[z73,z0,z2,z115,z4,z6]),(0,[z0,z1,z2,z3,z4,z1142]),(0,[z0,z1,z180,z3,z4,z433])],[(0,[z0,z1,z2,z3,z4,z1143]),(0,[z0,z1,z3,z4,z982,z6]),(1,[z0,z1,z2,z776,z3])],[(0,[z0,z178,z2,z3,z4,z6]),(0,[z48,z0,z1,z2,z3,z205]),(0,[z0,z1,z2,z1144,z3,z4]),(0,[z0,z1,z180,z2,z3,z230]),(0,[z0,z1,z2,z3,z98,z84]),(0,[z0,z1,z1145,z2,z3,z4]),(0,[z0,z1,z2,z25,z3,z675]),(0,[z0,z1,z2,z25,z3,z281])],[(0,[z39,z0,z1,z207,z3,z4]),(0,[z0,z1,z2,z739,z4,z6]),(0,[z1,z2,z3,z757,z4,z6]),(0,[z0,z1,z2,z3,z756,z6]),(0,[z0,z1146,z1,z2,z3,z4])]],
   [[(0,[z0,z1147,z2,z3,z4,z6]),(0,[z0,z1,z2,z30,z3,z19]),(0,[z0,z1,z2,z3,z1148,z6]),(0,[z0,z1,z2,z3,z380,z19]),(0,[z0,z1,z2,z3,z4,z1149]),(0,[z0,z1,z2,z123,z4,z425])],[(0,[z39,z0,z1,z112,z3,z4]),(0,[z0,z1,z2,z34,z4,z19]),(0,[z0,z1150,z2,z3,z4,z6]),(0,[z23,z1,z2,z3,z36,z19]),(0,[z23,z0,z1,z2,z3,z392]),(0,[z1,z2,z3,z1151,z4,z6]),(0,[z0,z1,z2,z3,z4,z1152]),(0,[z0,z1,z255,z3,z4,z75]),(0,[z0,z1,z2,z3,z4,z1153]),(0,[z0,z1,z2,z3,z129,z4])],[(0,[z0,z1,z2,z1154,z3,z4]),(0,[z548,z0,z1,z2,z30,z6]),(0,[z0,z1,z2,z3,z4,z1155]),(0,[z21,z1,z2,z240,z4,z6]),(0,[z0,z1,z2,z1156,z3,z4]),(0,[z0,z1,z180,z2,z3,z75]),(0,[z0,z1,z1157,z2,z3,z4])],[(0,[z0,z1,z1158,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z1159]),(0,[z53,z1,z2,z388,z3,z6]),(0,[z0,z1,z2,z3,z1160,z4]),(0,[z73,z0,z2,z3,z92,z6]),(0,[z0,z1,z2,z115,z4,z428])],[(0,[z0,z1,z2,z3,z4,z1161]),(0,[z53,z1,z2,z3,z328,z19]),(0,[z0,z2,z106,z4,z536,z6]),(0,[z0,z1,z2,z3,z4,z1162]),(0,[z73,z0,z2,z25,z3,z92]),(0,[z0,z24,z2,z25,z3,z4]),(0,[z148,z0,z1,z760,z4,z6]),(0,[z0,z1,z2,z3,z4,z1163])],[(0,[z0,z2,z182,z106,z4,z6]),(0,[z0,z1,z2,z3,z1164,z4]),(0,[z0,z1,z2,z839,z4,z19])],[(0,[z0,z1,z264,z2,z3,z98]),(0,[z0,z72,z2,z106,z4,z6]),(0,[z0,z1,z2,z3,z1165,z4]),(0,[z0,z1,z2,z3,z4,z1166])],[(0,[z0,z1,z2,z3,z4,z1167]),(0,[z0,z1,z102,z760,z4,z6])]],
   [[(0,[z1168,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1169])],[(0,[z0,z534,z1,z2,z3,z4]),(0,[z0,z8,z2,z59,z3,z4]),(0,[z105,z1,z8,z2,z165,z4]),(0,[z0,z1,z2,z3,z245,z19]),(0,[z0,z1,z2,z3,z4,z1170]),(0,[z0,z1,z2,z3,z98,z109])],[(0,[z1171,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z98,z19])],[(0,[z0,z1,z2,z3,z4,z1172]),(0,[z0,z1,z761,z3,z4,z6]),(0,[z0,z2,z3,z99,z4,z19]),(0,[z23,z1,z2,z3,z757,z6]),(0,[z0,z100,z8,z9,z3,z4]),(0,[z0,z1,z2,z3,z15,z4]),(0,[z0,z1173,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z1174]),(0,[z82,z0,z1,z387,z3,z6]),(0,[z0,z1,z1175,z2,z3,z4]),(0,[z0,z2,z3,z718,z4,z6]),(1,[z0,z2,z3,z4,z816]),(0,[z332,z0,z1,z180,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1176]),(0,[z105,z1,z2,z165,z4,z422]),(0,[z0,z1177,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1178]),(0,[z0,z1,z2,z3,z4,z1179]),(0,[z0,z1,z2,z1180,z3,z4]),(0,[z653,z0,z1,z8,z3,z4])],[(0,[z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z863,z6]),(0,[z0,z1,z2,z3,z4,z1181]),(0,[z0,z1,z2,z3,z630,z19]),(0,[z1182,z0,z1,z2,z3,z4])],[(0,[z0,z1,z1183,z3,z4,z6]),(0,[z0,z1,z2,z3,z1184,z6]),(0,[z933,z0,z1,z2,z3,z4]),(0,[z937,z1,z2,z3,z4,z6])]],
   [[(0,[z548,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z1185,z3,z4]),(0,[z0,z1,z2,z1022,z4,z6]),(0,[z53,z0,z1,z2,z3,z44]),(0,[z0,z1,z2,z1186,z4,z6]),(0,[z0,z107,z2,z62,z4,z19]),(0,[z0,z1,z2,z115,z4,z19]),(0,[z0,z1,z2,z3,z1187,z4]),(0,[z0,z1,z2,z3,z4,z816]),(0,[z148,z0,z24,z103,z4,z6]),(0,[z63,z0,z1,z2,z3,z98]),(0,[z0,z1,z2,z776,z3,z19])],[(0,[z0,z100,z461,z3,z4,z6]),(0,[z0,z203,z2,z3,z4,z211]),(0,[z0,z1,z1188,z2,z3,z4])],[(0,[z0,z1,z2,z1189,z4,z6]),(0,[z0,z1,z2,z30,z25,z3]),(0,[z21,z0,z420,z2,z4,z6]),(0,[z0,z1190,z2,z3,z4,z6]),(0,[z0,z1,z2,z1191,z3,z4]),(0,[z0,z1,z2,z3,z536,z19]),(0,[z0,z1,z2,z123,z4,z428]),(0,[z39,z0,z1,z102,z14,z4])],[(0,[z39,z0,z24,z2,z3,z4]),(0,[z0,z1,z2,z3,z843,z6]),(0,[z0,z1,z2,z3,z4,z523])],[(0,[z0,z1,z2,z3,z4,z1192]),(0,[z0,z1,z2,z3,z4,z1193]),(0,[z0,z1,z2,z3,z4,z1194]),(0,[z0,z1,z2,z1195,z3,z4]),(0,[z0,z1,z2,z1196,z3,z4]),(0,[z351,z0,z1,z2,z3,z98]),(0,[z39,z278,z0,z1,z3,z4])],[(0,[z0,z1,z1197,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1198,z6]),(0,[z0,z1199,z2,z3,z4,z6]),(0,[z0,z1,z282,z2,z354,z4])],[(0,[z0,z1,z2,z3,z4,z1200]),(0,[z0,z1,z2,z3,z1201,z4]),(0,[z0,z1,z2,z3,z4,z1202]),(0,[z0,z2,z1203,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z30,z3,z6]),(0,[z0,z100,z9,z3,z4,z19]),(0,[z0,z1,z1204,z2,z3,z4])],[(0,[z0,z1,z2,z1205,z4,z6]),(0,[z105,z1,z2,z25,z165,z4]),(0,[z23,z1,z2,z3,z36,z6]),(0,[z1206,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1207,z6]),(0,[z0,z1208,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z746,z4])],[(0,[z156,z39,z1,z60,z3,z4]),(0,[z0,z534,z2,z59,z3,z4]),(0,[z11,z1,z2,z3,z4,z79]),(0,[z0,z1,z2,z3,z1209,z6]),(0,[z0,z403,z2,z3,z4,z6]),(0,[z0,z1043,z2,z3,z4,z6])],[(0,[z752,z78,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z1210,z6]),(0,[z1211,z0,z1,z2,z3,z4]),(0,[z150,z0,z1,z2,z3,z329]),(0,[z150,z0,z1,z2,z3,z230]),(0,[z896,z0,z1,z3,z4,z19])],[(0,[z0,z1,z2,z3,z1212,z4]),(0,[z0,z1,z2,z3,z165,z98]),(0,[z0,z1,z2,z3,z22,z19])],[(0,[z0,z1213,z2,z3,z4,z6]),(0,[z332,z0,z1,z2,z3,z57])],[(0,[z0,z1,z2,z3,z4,z1214]),(0,[z0,z1,z2,z164,z4,z19]),(0,[z527,z0,z534,z1,z2,z3]),(0,[z332,z23,z0,z1,z2,z3]),(0,[z39,z0,z1,z702,z3,z4]),(0,[z0,z1,z69,z2,z3,z4])],[(0,[z0,z1,z2,z1215,z3,z4]),(0,[z0,z1,z2,z123,z4,z19])]],
   [[(0,[z39,z0,z52,z2,z3,z4]),(0,[z0,z1,z2,z3,z981,z6]),(0,[z0,z1,z2,z1216,z3,z4]),(0,[z0,z681,z2,z106,z4,z6]),(0,[z0,z1,z180,z56,z3,z57]),(0,[z39,z0,z1,z2,z3,z1148]),(0,[z0,z1,z2,z464,z3,z98])],[(0,[z0,z1,z2,z3,z4,z1217]),(0,[z548,z0,z2,z59,z4,z6]),(0,[z0,z1218,z1,z2,z3,z6]),(0,[z94,z0,z134,z135,z3,z4]),(0,[z39,z0,z1,z3,z4,z84]),(0,[z0,z2,z3,z4,z1057,z6]),(0,[z0,z465,z1,z2,z131,z4])],[(0,[z39,z527,z0,z1,z2,z3]),(0,[z0,z1,z2,z3,z4,z1219]),(0,[z0,z1,z2,z3,z4,z1220]),(0,[z73,z0,z2,z3,z92,z140]),(0,[z0,z1,z2,z3,z1110,z6]),(0,[z0,z1,z2,z3,z57,z19]),(0,[z82,z39,z0,z1,z3,z75]),(0,[z332,z0,z1,z3,z75,z6]),(0,[z0,z1221,z1,z2,z3,z98])],[(0,[z527,z0,z1,z374,z2,z3]),(0,[z23,z231,z1,z2,z3,z6]),(0,[z53,z0,z1,z2,z3,z98]),(0,[z90,z1,z2,z340,z3,z4]),(0,[z0,z1,z2,z3,z1222,z4]),(0,[z0,z1,z2,z3,z4,z1223]),(0,[z0,z1,z2,z3,z4,z1224]),(0,[z0,z72,z2,z725,z4,z6]),(0,[z1225,z1,z2,z3,z4,z6]),(0,[z0,z1,z1226,z2,z3,z4]),(0,[z39,z0,z1,z531,z3,z4]),(0,[z0,z1,z102,z14,z4,z248])],[(0,[z527,z0,z1,z2,z3,z986]),(0,[z0,z1,z2,z3,z393,z98]),(0,[z0,z1,z3,z4,z6,z775])],[(0,[z95,z752,z2,z3,z4,z6]),(0,[z0,z1227,z1,z2,z4,z6]),(0,[z39,z294,z0,z2,z3,z4]),(0,[z39,z0,z2,z59,z3,z4]),(0,[z0,z1,z2,z3,z4,z1228]),(0,[z39,z0,z1,z8,z3,z16]),(0,[z332,z0,z1,z3,z4,z84]),(0,[z0,z58,z1,z8,z2,z109]),(0,[z0,z1,z2,z3,z4,z1229]),(0,[z0,z1230,z2,z3,z4,z6])],[(0,[z527,z0,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z1231]),(0,[z0,z669,z1,z2,z25,z3]),(0,[z0,z1,z2,z3,z103,z98])],[(0,[z0,z1,z2,z198,z4,z19]),(0,[z0,z1232,z2,z3,z4,z6]),(0,[z0,z1,z1233,z2,z3,z4]),(0,[z39,z0,z1,z656,z3,z4]),(0,[z0,z1,z2,z3,z4,z1234]),(0,[z0,z1,z2,z3,z1235,z4]),(0,[z0,z1236,z2,z3,z4,z6]),(0,[z39,z0,z1,z2,z1186,z4]),(0,[z150,z0,z1,z2,z776,z3])]],
   [[(0,[z0,z2,z59,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1237]),(0,[z0,z1,z2,z3,z205,z19]),(0,[z0,z1,z2,z3,z4,z83]),(0,[z0,z1,z3,z4,z843,z6]),(0,[z0,z1,z2,z776,z3,z6])],[(0,[z0,z1,z1238,z2,z3,z4]),(0,[z23,z0,z1,z2,z3,z19]),(0,[z0,z1,z2,z3,z4,z1239]),(0,[z0,z1,z2,z3,z4,z1240]),(0,[z0,z500,z2,z3,z4,z211])],[(0,[z0,z1,z1241,z2,z3,z4]),(0,[z213,z1,z761,z3,z4,z6]),(0,[z0,z1242,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1243]),(0,[z417,z1,z2,z3,z4,z49]),(0,[z39,z0,z72,z2,z106,z4]),(0,[z73,z0,z2,z3,z718,z6])],[(0,[z73,z0,z1,z2,z3,z98]),(0,[z0,z496,z2,z3,z4,z29])],[(0,[z284,z78,z2,z3,z4,z6]),(0,[z0,z1,z1244,z2,z3,z4]),(0,[z1,z2,z3,z4,z830,z79]),(0,[z94,z0,z8,z135,z3,z4]),(0,[z73,z0,z2,z3,z220,z92])],[(0,[z294,z0,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1245]),(0,[z0,z1,z56,z434,z3,z6]),(0,[z97,z0,z1,z2,z25,z3]),(0,[z271,z0,z2,z3,z4,z816]),(0,[z0,z1,z2,z3,z1246,z4]),(0,[z0,z1,z2,z1012,z3,z57]),(0,[z0,z357,z2,z3,z4,z523])],[(0,[z156,z1,z60,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1247]),(0,[z105,z624,z1,z2,z4,z6]),(0,[z0,z100,z9,z25,z3,z4]),(0,[z0,z1248,z1,z2,z3,z4])],[(0,[z0,z1,z3,z57,z75,z19]),(0,[z0,z1,z2,z573,z3,z19])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 516) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 516).take 507) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1023).take 310) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1333)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [516, 507, 310] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 69).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 69).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 143).take 83).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 226).take 30).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [69, 74, 83, 30] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_45710

theorem PEqualNP.Outside.L_meta_45710 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 4008231040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 4008231040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45710.solve