import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37793

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
  Nat.testBit (4277071598 * 2 ^ 32 + 4276677344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x010004044045858d#64 ++ 0x002000808808b0b1#64 ++ 0xfe814d2cc0cf9f9f#64 ++ 0xbfd029a59819f3f3#64 : BitVec 256),
   (0x2a0010450312aca6#64 ++ 0x05400208a0625594#64 ++ 0xfde2b2d70733ece7#64 ++ 0x7fbc565ae0e67d9c#64 : BitVec 256),
   (0x840cc31818285050#64 ++ 0x5081986303050a0a#64 ++ 0xabdcc318383c70fe#64 ++ 0xf57b986307078e1f#64 : BitVec 256),
   (0x481703e02d807a00#64 ++ 0x8902e07c05b00f40#64 ++ 0x67ff03e03fc07f05#64 ++ 0xecffe07c07f80fe0#64 : BitVec 256),
   (0x703bfc0036ff0000#64 ++ 0xee077f8006dfe000#64 ++ 0x1fbffc003fff8003#64 ++ 0xe3f7ff8007fff000#64 : BitVec 256),
   (0x801febba80000000#64 ++ 0xf003fd7750000000#64 ++ 0xff9fffffc0000000#64 ++ 0x1ff3fffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe814d2cc0cf9f9f 0xbfd029a59819f3f3

def z1 : W := mkw 0x2200100102120022 0x0440020020424004 0x0000b01300300060 0x000016026006000c

def z2 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b2d70733ece7 0x7fbc565ae0e67d9c

def z3 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff03e03fc07f05 0xecffe07c07f80fe0

def z4 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffc003fff8003 0xe3f7ff8007fff000

def z5 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0000000 0x1ff3fffff8000000

def z6 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabdcc318383c70fe 0xf57b986307078e1f

def z7 : W := mkw 0x713bfc0476ff858d 0xee277f808edff0b1 0x1fbffc003fff9f9f 0xe3f7ff8007fff3f3

def z8 : W := mkw 0x503bec0034ed0000 0xea077d80069da000 0x07bf4c003fcc0001 0xe0f7e98007f98000

def z9 : W := mkw 0x481328e2a5802a00 0xa902651c54b00540 0x54233ce7c7c00f01 0x0a84679cf8f801e0

def z10 : W := mkw 0x0004030008005000 0x0000806001000a00 0x23dc030038007004 0xe47b806007000e00

def z11 : W := mkw 0x001328a280000000 0xa002651450000000 0x54033ce7c0000000 0x0a80679cf8000000

def z12 : W := mkw 0x841febba90280050 0xf083fd775205000a 0xff9fffffc03c00fa 0x1ff3fffff807801f

def z13 : W := mkw 0x2a08d045133aaca6 0x45411a08a2675594 0xfffef2d73f3fece7 0xffffde5ae7e7fd9c

def z14 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x14233c0007c38001 0x0284678000f87000

def z15 : W := mkw 0x481703e42d80fe84 0x8902e07c85b01fd0 0xffff03e43fc3ff87 0xffffe07c87f87ff0

def z16 : W := mkw 0x0800004001002800 0x0100000800200500 0x65e202c007006c05 0x6cbc405800e00d80

def z17 : W := mkw 0x22001005021284a6 0x04400200a0425094 0x9800b017003380e2 0x13001602e006701c

def z18 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x625d03e038c07f04 0x8c4ba07c07180fe0

def z19 : W := mkw 0xcc0cc3583da87a50 0x5981986b07b50f4a 0xabfcc3183ffc7fff 0xf57f986307ff8fff

def z20 : W := mkw 0x4013040024c50000 0x880260800498a000 0x1fbf4c003fcf8003 0xe3f7e98007f9f000

def z21 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xefff43e83fcc7f9f 0xfdffe87d07f98ff3

def z22 : W := mkw 0xf03bfc1ab6ff0000 0xfe077f8356dfe000 0x9fbffc1fffff8003 0xf3f7ff83fffff000

def z23 : W := mkw 0x48172be2ad807a00 0xa902e57c55b00f40 0x77ff3fe7ffc07f05 0xeeffe7fcfff80fe0

def z24 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x442300e007c00f01 0x0884601c00f801e0

def z25 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x017e02c03f006000 0x402fc05807e00c00

def z26 : W := mkw 0x0000000010280000 0x0000000002050000 0x00000000383c0002 0xe000000007078000

def z27 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xffe3ffffc7ffffff 0xfffc7ffff8ffffff

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x54010c24c0000000 0x0a80218498000000

def z29 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x021d012038c01300 0x8043a02407180260

def z30 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0xfd82fedfc0000000 0x1fb05fdbf8000000

def z31 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x006000000733ece7 0x600c000000e67d9c

def z32 : W := mkw 0xc81febfaad807a00 0xf903fd7f55b00f40 0xffffffffffc07f05 0xfffffffffff80fe0

def z33 : W := mkw 0x001300a000000000 0x8002601400000000 0x440300e000000000 0x0880601c00000000

def z34 : W := mkw 0x8008c01800000000 0x5001180300000000 0x8800c01800000000 0x1100180300000000

def z35 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0x015eb2d338306060 0x402bd65a67060c0c

def z36 : W := mkw 0xae08d05d133aacf6 0x55c11a0ba267559e 0xfde2f2df073fecff 0x7fbc5e5be0e7fd9f

def z37 : W := mkw 0x3028fc00127f0000 0x66051f80024fe000 0x1e81fc0000ff8003 0xa3d03f80001ff000

def z38 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x027d01203fc07f05 0xe04fa02407f80fe0

def z39 : W := mkw 0x800cc31800000000 0x5001986300000000 0xabdcc318003060e6 0x757b986300060c1c

def z40 : W := mkw 0x4013000024800000 0x8802600004900000 0x0423000007c00001 0x0084600000f80000

def z41 : W := mkw 0xf03fffbab6ff0000 0xfe07fff756dfe000 0xffbfffffffff8003 0xfff7fffffffff000

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x98004c0cc0000000 0x1300098198000000

def z43 : W := mkw 0x7a3bf84137ba2822 0xef477f0826f74504 0x017eb2d33f306060 0x402fd65a67e60c0c

def z44 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd82b2d700000000 0x1fb0565ae0000000

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0x6681012000000000 0x0cd0202400000000

def z46 : W := mkw 0x713bfc0476ff858d 0xee277f808edff0b1 0x9fbffc0cffff809b 0xf3f7ff819ffff013

def z47 : W := mkw 0x6a1713e52f92fea6 0x8d42e27ca5f25fd4 0xffffb3f73ff3ffe7 0xfffff67ee7fe7ffc

def z48 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff83c70fe 0xfffbffffff078e1f

def z49 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0x9800fc1fc0000000 0x13001f83f8000000

def z50 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xffdffffff8007004 0xfffbffffff000e00

def z51 : W := mkw 0x840403ba88005050 0x1080807751000a0a 0xe04003ffc00070fc 0x1c08007ff8000e1f

def z52 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a804000000c0002 0xa150080000018000

def z53 : W := mkw 0x8108ec1ec045858d 0x70211d83d808b0b1 0xfe81fd3fc0cf9f9f 0xbfd03fa7f819f3f3

def z54 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x1de2b0000733ece7 0x63bc560000e67d9c

def z55 : W := mkw 0xcc1fc3f83da87a50 0xd983f87f07b50f4a 0xefffc3f83ffc7fff 0xfdfff87f07ff8fff

def z56 : W := mkw 0x8a1febff8100aca6 0xf143fd7ff0201594 0xffdfffffc0006ce4 0x1ffbfffff8000d9c

def z57 : W := mkw 0x0000000000000000 0x0000000000000000 0xa9c08210003060e6 0x7538104200060c1c

def z58 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x021c4108380c1018 0x8043882107018203

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x6681012000c01f05 0xacd02024001803e0

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa80410800000000 0x1550082100000000

def z61 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0xe04002d700006ce4 0x1c08005ae0000d9c

def z62 : W := mkw 0x503bec0034ed0000 0xea077d80069da000 0x021d4c0038cc0000 0x8043a98007198000

def z63 : W := mkw 0x5020040034ed0000 0x0a040080069da000 0x0000000038cc0000 0x8000000007198000

def z64 : W := mkw 0x001328a280000000 0xa002651450000000 0xfd83bef7c0000000 0x1fb077def8000000

def z65 : W := mkw 0x7020140036ff0000 0x0e04028006dfe000 0x002000003fff8003 0xe004000007fff000

def z66 : W := mkw 0x7033140036ff0000 0x8e06628006dfe000 0x07bf00003fff8003 0xe0f7e00007fff000

def z67 : W := mkw 0x8404031808005050 0x1080806301000a0a 0xa0400318000070fc 0x1408006300000e1f

def z68 : W := mkw 0x0400000018285050 0x0080000003050a0a 0x00400000383c70fe 0xe008000007078e1f

def z69 : W := mkw 0x503bec0034ed0000 0xea077d80069da000 0x1e9d4c0038cf8003 0xa3d3a9800719f000

def z70 : W := mkw 0xae0cd35d1b3afcf6 0x55c19a6ba3675f9e 0xfffef3df3f3ffcff 0xffffde7be7e7ff9f

def z71 : W := mkw 0xf42cd7183eff5050 0x5e859ae307dfea0a 0xabfcc3183ffff0ff 0xf57f986307fffe1f

def z72 : W := mkw 0xf43fff183eff5050 0xfe87ffe307dfea0a 0x1fbffd083fff901b 0xe3f7ffa107fff203

def z73 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xba804d0cc00f909e 0xb75009a19801f213

def z74 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x07bfb0003ff00001 0xe0f7f60007fe0000

def z75 : W := mkw 0x811fefbec045858d 0xf023fdf7d808b0b1 0xff9fffffc00f809a 0x1ff3fffff801f013

def z76 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xfde2b3ffc733ffff 0x7fbc567ff8e67fff

def z77 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc00c109e 0xbff3fffff8018213

def z78 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x021d4d28c0000000 0x0043a9a518000000

def z79 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x542230c707038c01 0x0a844618e0e07180

def z80 : W := mkw 0x2000100402128484 0x0400020080425090 0xfda2b00407338c87 0x7fb4560080e67190

def z81 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x0000000000cf9f9f 0xa00000000019f3f3

def z82 : W := mkw 0x080403e009007a00 0x0100807c01200f40 0x604003e000007f04 0x0c08007c00000fe0

def z83 : W := mkw 0x4013000024800000 0x8802600004900000 0x07bf00003fc00001 0xe0f7e00007f80000

def z84 : W := mkw 0xc81febfaad807a00 0xf903fd7f55b00f40 0x017eb2d33f006000 0x402fd65a67e00c00

def z85 : W := mkw 0x480000402d807a00 0x0900000805b00f40 0x006000003fc07f05 0xe00c000007f80fe0

def z86 : W := mkw 0x0100040040450109 0x002000800808a021 0x02014d28c0cc1318 0x804029a518198263

def z87 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x1dbeb0003f338003 0x63b7d60007e67000

def z88 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3b3f707f3ffe7 0xfffc767ee0fe7ffc

def z89 : W := mkw 0x880403fa89007a00 0x1100807f51200f40 0xe04003ffc0007f04 0x1c08007ff8000fe0

def z90 : W := mkw 0x411707a06cc55309 0x8822e0f40d98aa61 0x021d4d28f8cc1318 0x8043a9a51f198263

def z91 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x457f02e03fc06f01 0x48afe05c07f80de0

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000003060e6 0x6008000000060c1c

def z93 : W := mkw 0x0000000000000000 0x0000000000000000 0x039c000038000000 0xe073800007000000

def z94 : W := mkw 0x3028fc00127f0000 0x66051f80024fe000 0x1800fc00003f8002 0x03001f800007f000

def z95 : W := mkw 0xc81febfaa5802a00 0xf903fd7f54b00540 0xffbfffffc7c00f01 0x1ff7fffff8f801e0

def z96 : W := mkw 0x0000040000450000 0x000000800008a000 0xbe814d0800cf909f 0xb7d029a10019f213

def z97 : W := mkw 0xaa0cd35d0312aca6 0x55419a6ba0625594 0xfffef3df0733ece7 0x7fffde7be0e67d9c

def z98 : W := mkw 0xa01ffbba82120000 0xf403ff7750424000 0xffbfffffc7338003 0x7ff7fffff8e67000

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814d2cc0c01f05 0xbfd029a5981803e0

def z100 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x015c821038306060 0x402b904207060c0c

def z101 : W := mkw 0x6013100026920000 0x8c02620004d24000 0x1fbfb0003ff38003 0xe3f7f60007fe7000

def z102 : W := mkw 0x0a0403e50900fea6 0x0140807ca1201fd4 0xe04003f700007fe4 0x1c08007ee0000ffc

def z103 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x035cc318383c7078 0xc06b986307078e0f

def z104 : W := mkw 0xf43fff183eff5050 0xfe87ffe307dfea0a 0xbfffff183ffff0ff 0xf7ffffe307fffe1f

def z105 : W := mkw 0xae04135d0b12fcf6 0x15c0826ba1625f9e 0xfde2b3df0733fcff 0x7fbc567be0e67f9f

def z106 : W := mkw 0x0b0000454100adaf 0x01600008a82015b5 0xe04003ffc0007ffc 0x1c08007ff8000fff

def z107 : W := mkw 0x2a00104103122822 0x0540020820624504 0x0162b2d307306060 0x402c565a60e60c0c

def z108 : W := mkw 0xaa1ffbff8312aca6 0xf543ff7ff0625594 0xffffffffc733ece7 0x7ffffffff8e67d9c

def z109 : W := mkw 0x0008c00010280000 0x4001180002050000 0x0b9cc000383c0002 0xe173980007078000

def z110 : W := mkw 0x80172bba80000000 0xb002e57750000000 0xf4033fffc0000000 0x1e8067fff8000000

def z111 : W := mkw 0x0100000040000109 0x0020000008000021 0x00000128c0001318 0x0000002518000263

def z112 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x991efedfc0000000 0x1323dfdbf8000000

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0x88004008000c009a 0x1100080100018013

def z114 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xab9ef3db00000000 0x1573de7b60000000

def z115 : W := mkw 0x8408c01810280050 0x508118030205000a 0x8800c018003c00fa 0x110018030007801f

def z116 : W := mkw 0x001328a280000000 0xa002651450000000 0xfe837defc0000000 0x1fd06fbdf8000000

def z117 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x56014d2cc0cf9f19 0x8ac029a59819f3e3

def z118 : W := mkw 0x800403ba80000000 0x1000807750000000 0xe00003ffc0000000 0x1c00007ff8000000

def z119 : W := mkw 0x491707e46dc5ff8d 0x8922e0fc8db8bff1 0xffff4fecffcfff9f 0xffffe9fd9ff9fff3

def z120 : W := mkw 0x000000a280000000 0x0000001450000000 0x400000e7c0000000 0x0800001cf8000000

def z121 : W := mkw 0x0000000400008484 0x0000000080001090 0xfc80000400038c87 0x3f90000080007190

def z122 : W := mkw 0x0008c00010280000 0x4001180002050000 0xab9cc108383c109e 0xf573982107078213

def z123 : W := mkw 0x2000100002120000 0x0400020000424000 0x0020000007338003 0x6004000000e67000

def z124 : W := mkw 0x8e04035d0900fcf6 0x11c0806ba1201f9e 0xe04003df00007cfc 0x1c08007be0000f9f

def z125 : W := mkw 0x0013280000000000 0xa002650000000000 0x14033c0000000000 0x0280678000000000

def z126 : W := mkw 0x7028d40036ff0000 0x4e051a8006dfe000 0x0bbcc0003fff8003 0xe177980007fff000

def z127 : W := mkw 0x3128fc04527f858d 0x66251f808a4ff0b1 0x9800fc0cc03f809a 0x13001f819807f013

def z128 : W := mkw 0x713bfc0476ff858d 0xee277f808edff0b1 0xffbffd2cffff9f9f 0xfff7ffa59ffff3f3

def z129 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x463f01e03fc01f01 0x88c7e03c07f803e0

def z130 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x1e814c0000cf9f9f 0xa3d029800019f3f3

def z131 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0x1fbffd28ffff931b 0xe3f7ffa51ffff263

def z132 : W := mkw 0x001703a000000000 0x8002e07400000000 0x679f03e000000000 0x0cf3e07c00000000

def z133 : W := mkw 0x0000000000000000 0x0000000000000000 0xabc0c318003c70fe 0xf578186300078e1f

def z134 : W := mkw 0x811fefbec045858d 0xf023fdf7d808b0b1 0xff9fffffc0cf9f9f 0xbff3fffff819f3f3

def z135 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbffed73fff8003 0xfff7ffdae7fff000

def z136 : W := mkw 0x8a0403ff8100aca6 0x1140807ff0201594 0xe04003ffc0006ce4 0x1c08007ff8000d9c

def z137 : W := mkw 0x210014044257858d 0x04200280884af0b1 0xffa3fd2cc7ff9f9f 0xfff47fa598fff3f3

def z138 : W := mkw 0x2000100002120000 0x0400020000424000 0x1da2b00007338003 0x63b4560000e67000

def z139 : W := mkw 0xc81febfaad807a00 0xf903fd7f55b00f40 0x67ff4fe8ffc07f05 0xecffe9fd1ff80fe0

def z140 : W := mkw 0x783fffe03fff7a00 0xef07fffc07ffef40 0x7fffffe03fffff07 0xeffffffc07ffffe0

def z141 : W := mkw 0x010000044000858d 0x00200000880010b1 0xea80412cc00c1f9e 0xbd500825980183f3

def z142 : W := mkw 0xf03fffbaa6d70000 0xfe07fff754dae000 0xffbfffffc7c38001 0x1ff7fffff8f87000

def z143 : W := mkw 0x810cc71c4045858d 0x502198e38808b0b1 0xff9dcf3cc0cf9f9f 0xbff3b9e79819f3f3

def z144 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x9a1dfd3fc0000000 0x1343bfa7f8000000

def z145 : W := mkw 0x481300402d807a00 0x8902600805b00f40 0x07ff00003fc07f05 0xe0ffe00007f80fe0

def z146 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x07ff02c03fc06001 0xe0ffe05807f80c00

def z147 : W := mkw 0x0400000010280050 0x008000000205000a 0x00000000003c00fa 0x000000000007801f

def z148 : W := mkw 0x841feb1818285050 0xf083fd6303050a0a 0xbfdfff18383c70fe 0xf7fbffe307078e1f

def z149 : W := mkw 0x481300e02d807a00 0x8902601c05b00f40 0x446300e03fc07f05 0xe88c601c07f80fe0

def z150 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x037f03e03fc07300 0xc06fe07c07f80e60

def z151 : W := mkw 0x0000000000000000 0x0000000000000000 0xaa804108000c109e 0xb550082100018213

def z152 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x54010c24c0c38f01 0x0a802184981871e0

def z153 : W := mkw 0x090407e44945ff8d 0x012080fc8928bff1 0xfec14fecc0cfff9f 0xbfd829fd9819fff3

def z154 : W := mkw 0x3228fc05127f84a6 0x66451f80a24ff094 0x9800fc17003f80e2 0x13001f82e007f01c

def z155 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xffffb3f73fc07f05 0xfffff67ee7f80fe0

def z156 : W := mkw 0x30201400127f0000 0x06040280024fe000 0x00000000003f8002 0x000000000007f000

def z157 : W := mkw 0xd43fef183ced5050 0xfa87fde3079daa0a 0x021d4d0838cc1018 0x8043a9a107198203

def z158 : W := mkw 0x800cc31800000000 0x5001986300000000 0xab9cc31800000000 0x1573986300000000

def z159 : W := mkw 0x22001005021284a6 0x04400200a0425094 0xfc80b01700338ce7 0x3f901602e006719c

def z160 : W := mkw 0x513bec0074ed0109 0xea277d800e9da021 0x021d4d28f8cc1318 0x8043a9a51f198263

def z161 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe2f3df073ffcff 0xfffc5e7be0e7ff9f

def z162 : W := mkw 0xee1fd3fd3fbafef6 0xddc3fa7fa7f75fde 0xfffff3ff3fffffff 0xfffffe7fe7ffffff

def z163 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x47bf00e03fc00f01 0xe8f7e01c07f801e0

def z164 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x011eb2d300000000 0x0023d65a60000000

def z165 : W := mkw 0x850cc71c586dd5dd 0x50a198e38b0dbabb 0xffddcf3cf8ffffff 0xfffbb9e79f1fffff

def z166 : W := mkw 0x503bec0034ed0000 0xea077d80069da000 0x1f9ffc0038cc0000 0x83f3ff8007198000

def z167 : W := mkw 0x742014003eff5050 0x0e84028007dfea0a 0x006000003ffff0ff 0xe00c000007fffe1f

def z168 : W := mkw 0x1028ec00106d0000 0x62051d80020da000 0x00004c00000c0000 0x0000098000018000

def z169 : W := mkw 0x0008c00010280000 0x4001180002050000 0x021c4000380c0000 0x8043880007018000

def z170 : W := mkw 0x4c0000403da87a50 0x0980000807b50f4a 0x006000003ffc7fff 0xe00c000007ff8fff

def z171 : W := mkw 0x2a1bf8450312aca6 0xe5437f08a0625594 0xfffffed70733ece7 0x7fffffdae0e67d9c

def z172 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xaa80410800cf9f9f 0xb55008210019f3f3

def z173 : W := mkw 0x2a00104103122822 0x0540020820624504 0x1de2b2d30733e063 0x63bc565a60e67c0c

def z174 : W := mkw 0x0800004001002800 0x0100000800200500 0x604002c000006c04 0x0c08005800000d80

def z175 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfc810c24c0c38f87 0x3f902184981871f0

def z176 : W := mkw 0x000cc30018285000 0x4001986003050a00 0x2bdcc300383c7006 0xe57b986007078e00

def z177 : W := mkw 0xc81703faad807a00 0x9902e07f55b00f40 0xe7ff03ffffc07f05 0xfcffe07ffff80fe0

def z178 : W := mkw 0x2000140002570000 0x04000280004ae000 0x1fa3fc0007ff8003 0xe3f47f8000fff000

def z179 : W := mkw 0x090403e44900ff8d 0x0120807c89201ff1 0xe04003ecc0007f9c 0x1c08007d98000ff3

def z180 : W := mkw 0x490004446dc5ff8d 0x092000888db8bff1 0x006000003fcfff9f 0xe00c000007f9fff3

def z181 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x98004c0cc00f809a 0x130009819801f013

def z182 : W := mkw 0x503fefa03ced5200 0xea07fdf4079daa40 0x021d4d2038cc1300 0x8043a9a407198260

def z183 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x013eb0003f300000 0x4027d60007e60000

def z184 : W := mkw 0x8408c01810280050 0x508118030205000a 0x00004008000c0018 0x0000080100018003

def z185 : W := mkw 0x0000000000000000 0x0000000000000000 0x658202c000000000 0x0cb0405800000000

def z186 : W := mkw 0x001be80000000000 0xe0037d0000000000 0x1f9ffc0000000000 0x03f3ff8000000000

def z187 : W := mkw 0x70333ca2a6d70000 0xae06679454dae000 0x54233ce7c7c38001 0x0a84679cf8f87000

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x02014d28c0000000 0x004029a518000000

def z189 : W := mkw 0xfa3fffffb7ffaca6 0xff47fffff6fff594 0xffffffffffffece7 0xfffffffffffffd9c

def z190 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xff9ffffff80c1018 0x9ff3ffffff018203

def z191 : W := mkw 0x801fc3b800000000 0xd003f87700000000 0xef9fc3f800000000 0x1df3f87f00000000

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0xfdc2b2d7003060e6 0x7fb8565ae0060c1c

def z193 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0x54233ce7c7c38f01 0x0a84679cf8f871e0

def z194 : W := mkw 0x0004030008005000 0x0000806001000a00 0x015c020038006000 0x402b804007000c00

def z195 : W := mkw 0x0000040000450000 0x000000800008a000 0x1e814c0000cf8003 0xa3d029800019f000

def z196 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xffff4fecffc07f05 0xffffe9fd9ff80fe0

def z197 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xffddcf3cf83c70fe 0xfffbb9e79f078e1f

def z198 : W := mkw 0x001703a000000000 0x8002e07400000000 0xff9fb3f700000000 0x1ff3f67ee0000000

def z199 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xbffffe103fffe0e7 0xf7ffffc207fffc1c

def z200 : W := mkw 0x001feba000000000 0xe003fd7400000000 0x7f9fffe000000000 0x0ff3fffc00000000

def z201 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0c01f05 0xbff3fffff81803e0

def z202 : W := mkw 0x811fefbec045858d 0xf023fdf7d808b0b1 0xff9fffffc0c38f01 0x1ff3fffff81871e0

def z203 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d82b00000000000 0x03b0560000000000

def z204 : W := mkw 0x480000402d807a00 0x0900000805b00f40 0x65e202c03fc07f05 0xecbc405807f80fe0

def z205 : W := mkw 0x801feb1800000000 0xf003fd6300000000 0xbf9fff1800000000 0x17f3ffe300000000

def z206 : W := mkw 0x7a333c4527d7aca6 0xaf466788a4faf594 0xfde3bed707f3ece7 0x7fbc77dae0fe7d9c

def z207 : W := mkw 0x001328a280000000 0xa002651450000000 0x000230c300000000 0x0000461860000000

def z208 : W := mkw 0x583fefe03ded7a00 0xeb07fdfc07bdaf40 0x67ff4fe03fcc7f05 0xecffe9fc07f98fe0

def z209 : W := mkw 0x0000280280000000 0x2000050050000000 0x10003c07c0000000 0x02000780f8000000

def z210 : W := mkw 0x080000440100ac84 0x0100000880201590 0xfde202c40703ec87 0x7fbc405880e07d90

def z211 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xbfbffd083fff909f 0xf7f7ffa107fff213

def z212 : W := mkw 0x010000044000858d 0x00200000880010b1 0xe000012cc0001f9c 0x1c000025980003f3

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814d2cc0000000 0x1fd029a598000000

def z214 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3ffffc733ece7 0x7ffc7ffff8e67d9c

def z215 : W := mkw 0x23001405425785af 0x04600280a84af0b5 0xfe81fd3fc0ff9fff 0xbfd03fa7f81ff3ff

def z216 : W := mkw 0x7a3bfc4537ffaca6 0xef477f88a6fff594 0xfffffed73fffece7 0xffffffdae7fffd9c

def z217 : W := mkw 0x783bfc403fff7a00 0xef077f8807ffef40 0x1ffffc003fffff07 0xe3ffff8007ffffe0

def z218 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x5da2b0c707338c03 0x6bb45618e0e67180

def z219 : W := mkw 0xae1ffbff9b3afcf6 0xf5c3ff7ff3675f9e 0xffffffffff3ffcff 0xffffffffffe7ff9f

def z220 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c80000000038003 0x2390000000007000

def z221 : W := mkw 0x8504031c4800d5dd 0x10a0806389001abb 0xe040033cc0007ffc 0x1c08006798000fff

def z222 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x1ea37c0007cf8003 0xa3d46f8000f9f000

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0400210000060e4 0x1408004200000c1c

def z224 : W := mkw 0x080403e009007a00 0x0100807c01200f40 0x65e203e007007f05 0x6cbc407c00e00fe0

def z225 : W := mkw 0x001703a000000000 0x8002e07400000000 0x011e02c000000000 0x0023c05800000000

def z226 : W := mkw 0x2a0014450357aca6 0x05400288a06af594 0xffe3fed707ffece7 0xfffc7fdae0fffd9c

def z227 : W := mkw 0x0804034009007800 0x0100806801200f00 0x67fe03c03f007c05 0xecffc07807e00f80

def z228 : W := mkw 0x841fc3b818285050 0xd083f87703050a0a 0xefdfc3f8383c70fe 0xfdfbf87f07078e1f

def z229 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe814d2cc00f809a 0x1fd029a59801f013

def z230 : W := mkw 0xf03ffbbab6ba0000 0xfe07ff7756d74000 0x013eb2d33f300000 0x4027d65a67e60000

def z231 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x895cc218383c60fa 0x512b984307078c1f

def z232 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x163f7c003fcf8001 0x82c7ef8007f9f000

def z233 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xffdfffffc03060e6 0x7ffbfffff8060c1c

def z234 : W := mkw 0x0004030008005000 0x0000806001000a00 0x67dd032038c07f05 0xecfba06407180fe0

def z235 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x025c4108383c70fe 0xe04b882107078e1f

def z236 : W := mkw 0x8408c01818285050 0x5081180303050a0a 0x8840c018383c70fe 0xf108180307078e1f

def z237 : W := mkw 0x800cc31810280000 0x5001986302050000 0xab9cc318383c0002 0xf573986307078000

def z238 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xa9e082100733ece7 0x753c104200e67d9c

def z239 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x65fe02c03f006c05 0x6cbfc05807e00d80

def z240 : W := mkw 0x800cc31800000000 0x5001986300000000 0x011c821000000000 0x0023904200000000

def z241 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xefddc33838fc7fff 0xfdfbb867071f8fff

def z242 : W := mkw 0x0400000018285050 0x0080000003050a0a 0x0040000038306060 0x4008000007060c0c

def z243 : W := mkw 0x881febfa89007a00 0xf103fd7f51200f40 0xffdfffffc0007f04 0x1ffbfffff8000fe0

def z244 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x617e03e03f007f04 0x4c2fc07c07e00fe0

def z245 : W := mkw 0x0100040040450109 0x002000800808a021 0x1e814d28c0cf931b 0xa3d029a51819f263

def z246 : W := mkw 0xd43fef183ced5050 0xfa87fde3079daa0a 0xabddcf1838fc70fe 0xf57bb9e3071f8e1f

def z247 : W := mkw 0x010000044000858d 0x00200000880010b1 0x8000000cc0000098 0x1000000198000013

def z248 : W := mkw 0xa60cd31d1a3ad4f6 0x54c19a63a3475a9e 0xbbdcf31f383ff0fe 0xf77b9e63e707fe1f

def z249 : W := mkw 0x8404031808005050 0x1080806301000a0a 0x0000010800001018 0x0000002100000203

def z250 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xff83ffffc0cf9f9f 0xbff07ffff819f3f3

def z251 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x546230c70733ece7 0x6a8c4618e0e67d9c

def z252 : W := mkw 0x703bfca2b6ff0000 0xee077f9456dfe000 0x5fbffce7ffff8003 0xebf7ff9cfffff000

def z253 : W := mkw 0x491707e46dc5ff8d 0x8922e0fc8db8bff1 0x67ff03e03fcfff9f 0xecffe07c07f9fff3

def z254 : W := mkw 0x090004444145ad8d 0x012000888828b5b1 0xffe34fecc7cfff9f 0xfffc69fd98f9fff3

def z255 : W := mkw 0x6a0010452f92fea6 0x0d400208a5f25fd4 0x006000003ff3ffe7 0xe00c000007fe7ffc

def z256 : W := mkw 0x8404031808005050 0x1080806301000a0a 0x0040021000006060 0x0008004200000c0c

def z257 : W := mkw 0x2a0413450b12fca6 0x05408268a1625f94 0xfffeb3d73f33fce7 0xffffd67ae7e67f9c

def z258 : W := mkw 0x2000100002120000 0x0400020000424000 0xbde2b2100733e0e7 0x77bc564200e67c1c

def z259 : W := mkw 0x0000040000450000 0x000000800008a000 0x0000000000cf8003 0xa00000000019f000

def z260 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfce000040733ece7 0x7f9c000080e67d9c

def z261 : W := mkw 0xc81febfaad807a00 0xf903fd7f55b00f40 0x67ffb3f33fc07f05 0xecfff67e67f80fe0

def z262 : W := mkw 0x3028fc00127f0000 0x66051f80024fe000 0x1da2fc00073f8003 0x63b45f8000e7f000

def z263 : W := mkw 0xaa1ffbfb83122822 0xf543ff7f70624504 0x017eb2d307306060 0x402fd65a60e60c0c

def z264 : W := mkw 0xf43bfc1836ff0050 0xfe877f8306dfe00a 0x9fbffc183fff80fb 0xf3f7ff8307fff01f

def z265 : W := mkw 0xb028fc1a927f0000 0x76051f83524fe000 0x9800fc1fc03f8002 0x13001f83f807f000

def z266 : W := mkw 0x001703a000000000 0x8002e07400000000 0x679f03e000c01f05 0xacf3e07c001803e0

def z267 : W := mkw 0x4800004025802a00 0x0900000804b00540 0x0020000007c00f01 0x0004000000f801e0

def z268 : W := mkw 0x001703a008005000 0x8002e07401000a00 0x67df03e038007004 0xecfbe07c07000e00

def z269 : W := mkw 0x001328a280000000 0xa002651450000000 0x00010c20c0000000 0x0000218418000000

def z270 : W := mkw 0x783fffe03fff7a00 0xef07fffc07ffef40 0x1ffffec03fffe003 0xe3ffffd807fffc00

def z271 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0xfcc002d70003ece7 0x3f98005ae0007d9c

def z272 : W := mkw 0xa608d01d123a84f6 0x54c11a03a247509e 0x9800f01f003f80fa 0x13001e03e007f01f

def z273 : W := mkw 0x0000000400008484 0x0000000080001090 0x9800000400038082 0x1300000080007010

def z274 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x0162b2d30733ece7 0x602c565a60e67d9c

def z275 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x013eb0003fff8003 0xe027d60007fff000

def z276 : W := mkw 0x7a333c4527d7aca6 0xaf466788a4faf594 0x54233cc707c38c01 0x0a846798e0f87180

def z277 : W := mkw 0x7a3bfc4537ffaca6 0xef477f88a6fff594 0x1ffffc003fffece7 0xe3ffff8007fffd9c

def z278 : W := mkw 0x0000000000000000 0x0000000000000000 0xff83ffffc0000000 0x1ff07ffff8000000

def z279 : W := mkw 0x080403e009007a00 0x0100807c01200f40 0x63dc03e038007f04 0xec7b807c07000fe0

def z280 : W := mkw 0x703fffa03eff5200 0xee07fff407dfea40 0x1fbffd203fff9303 0xe3f7ffa407fff260

def z281 : W := mkw 0x0408c00018285050 0x4081180003050a0a 0x0bdcc000383c70fe 0xe17b980007078e1f

def z282 : W := mkw 0x841febba88005050 0xf083fd7751000a0a 0xffdfffffc00070fc 0x1ffbfffff8000e1f

def z283 : W := mkw 0x001be80010280000 0xe0037d0002050000 0x1f9ffc00383c0002 0xe3f3ff8007078000

def z284 : W := mkw 0x7020140026d70000 0x0e04028004dae000 0x0020000007c38001 0x0004000000f87000

def z285 : W := mkw 0x71333c0466d7858d 0xae2667808cdaf0b1 0xfea37d2cc7cf9f9f 0xbfd46fa598f9f3f3

def z286 : W := mkw 0xc81fc3f82d807a00 0xd903f87f05b00f40 0xefffc3f83fc07f05 0xfdfff87f07f80fe0

def z287 : W := mkw 0x811febbec000858d 0xf023fd77d80010b1 0xff9fffffc0001f9c 0x1ff3fffff80003f3

def z288 : W := mkw 0x010000044000858d 0x00200000880010b1 0xfc80012cc0039f9f 0x3f900025980073f3

def z289 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xf840b2d70033ece6 0x1f08165ae0067d9c

def z290 : W := mkw 0x6a1310e52792aea6 0x8d42621ca4f255d4 0xfde3b2f707f3efe7 0x7fbc765ee0fe7dfc

def z291 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0x0000b01300000000 0x0000160260000000

def z292 : W := mkw 0x8000001a80000000 0x1000000350000000 0x8000001fc0000000 0x10000003f8000000

def z293 : W := mkw 0x8408c01810280050 0x508118030205000a 0x0000801000300060 0x000010020006000c

def z294 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x0000000000c38f01 0x00000000001871e0

def z295 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x9a014d2cc0cf939a 0x934029a59819f273

def z296 : W := mkw 0x800cebba80000000 0x70019d7750000000 0xf800ffffc0000000 0x1f001ffff8000000

def z297 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x015c8210383c70fe 0xe02b904207078e1f

def z298 : W := mkw 0x8c0cc35819287850 0x5181986b03250f0a 0xeffec3d83f3c7cff 0xfdffd87b07e78f9f

def z299 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x65e202c00733ece7 0x6cbc405800e67d9c

def z300 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x1f9ffd28c0000000 0x03f3ffa518000000

def z301 : W := mkw 0xf13fffbef6ff858d 0xfe27fff7dedff0b1 0xffbfffffffff9f9f 0xfff7fffffffff3f3

def z302 : W := mkw 0x001703a000000000 0x8002e07400000000 0x021d012000000000 0x0043a02400000000

def z303 : W := mkw 0x8c0403f809007a50 0x1180807f01200f4a 0xe04003f800007ffc 0x1c08007f00000fff

def z304 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfd9eb2d700000000 0x1fb3d65ae0000000

def z305 : W := mkw 0x22001005021284a6 0x04400200a0425094 0x00000000003380e2 0x000000000006701c

def z306 : W := mkw 0x491304e465c5af8d 0x8922609c8cb8b5f1 0xfea34decc7cf9f9f 0xbfd469bd98f9f3f3

def z307 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x75e232c70703ec05 0x6ebc4658e0e07d80

def z308 : W := mkw 0x001be8a280000000 0xe0037d1450000000 0x5f9ffce7c0000000 0x0bf3ff9cf8000000

def z309 : W := mkw 0x0000000000000000 0x0000000000000000 0xa880000000000086 0x3510000000000010

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000012000001f04 0x0c000024000003e0

def z311 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x23dc4308380c701c 0xe47b886107018e03

def z312 : W := mkw 0x0b0004454145adaf 0x01600088a828b5b5 0xfec14fffc0cfffff 0xbfd829fff819ffff

def z313 : W := mkw 0x8408c01810280050 0x508118030205000a 0xa9c0c218003c60fe 0x7538184300078c1f

def z314 : W := mkw 0x0004030008005000 0x0000806001000a00 0xabdc4308380c709e 0xf57b886107018e13

def z315 : W := mkw 0x800403ba80000000 0x1000807750000000 0x000002d300000000 0x0000005a60000000

def z316 : W := mkw 0x6a1713e52f92fea6 0x8d42e27ca5f25fd4 0x67ff03e03ff3ffe7 0xecffe07c07fe7ffc

def z317 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x1da3bc0007f38003 0x63b4778000fe7000

def z318 : W := mkw 0x0100040040450109 0x002000800808a021 0x0000000000cc1318 0x8000000000198263

def z319 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x5562b2d70733ec61 0x4aac565ae0e67d8c

def z320 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff8306060 0x5ffbffffff060c0c

def z321 : W := mkw 0x50332c0024c50000 0xaa0665800498a000 0x00010c0000c00000 0x0000218000180000

def z322 : W := mkw 0x0013000000000000 0x8002600000000000 0x079f000000000000 0x00f3e00000000000

def z323 : W := mkw 0x4013000024800000 0x8802600004900000 0x67bf01203fc01f05 0xecf7e02407f803e0

def z324 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xe000012cc0cf9f9f 0xbc0000259819f3f3

def z325 : W := mkw 0xcc1703f82d807a50 0x9982e07f05b00f4a 0xe7ff03f83fc07ffd 0xfcffe07f07f80fff

def z326 : W := mkw 0x01132ca6c045858d 0xa0226594d808b0b1 0xfe837defc0cf9f9f 0xbfd06fbdf819f3f3

def z327 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x153fbc003ff38001 0x42a7f78007fe7000

def z328 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xe21d4fffc0000000 0x1c43a9fff8000000

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z330 : W := mkw 0x481707e02dc57a00 0x8902e0fc05b8af40 0x7fff4fe03fcfff07 0xefffe9fc07f9ffe0

def z331 : W := mkw 0x0100040040450109 0x002000800808a021 0xaa814d28c0cc139e 0xb55029a518198273

def z332 : W := mkw 0x8408e81a90280050 0x70811d035205000a 0x9800fc1fc03c00fa 0x13001f83f807801f

def z333 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfc804c0cc00f8c9f 0x3f9009819801f193

def z334 : W := mkw 0xab1fffffc357adaf 0xf563fffff86af5b5 0xffffffffc7ffffff 0xfffffffff8ffffff

def z335 : W := mkw 0x0000000000000000 0x0000000000000000 0x0201012000c01300 0x8040202400180260

def z336 : W := mkw 0x851fefbed86dd5dd 0xf0a3fdf7db0dbabb 0xffdffffff8ffffff 0xfffbffffff1fffff

def z337 : W := mkw 0xc01febbaac805200 0xf803fd7755900a40 0xff9ffffff8c01300 0x9ff3ffffff180260

def z338 : W := mkw 0x800cc31800000000 0x5001986300000000 0x021c410800000000 0x0043882100000000

def z339 : W := mkw 0x011707a44045858d 0x8022e0f48808b0b1 0xff9f4fecc0cf9f9f 0xbff3e9fd9819f3f3

def z340 : W := mkw 0x6a0010452f92fea6 0x0d400208a5f25fd4 0xfde2b2d73ff3ffe7 0xffbc565ae7fe7ffc

def z341 : W := mkw 0x840cc31c1828d4d4 0x5081986383051a9a 0xffdcc31c383ffcff 0xfffb98638707ff9f

def z342 : W := mkw 0x0000000400008484 0x0000000080001090 0x5400000400038c01 0x0a80000080007180

def z343 : W := mkw 0x4013000024800000 0x8802600004900000 0x021d000038c00000 0x8043a00007180000

def z344 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x0b9cc108383c101a 0xe173982107078203

def z345 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa840c318003c70fe 0x1508186300078e1f

def z346 : W := mkw 0xc01febbaac805200 0xf803fd7755900a40 0x021d4d28f8c01300 0x8043a9a51f180260

def z347 : W := mkw 0x480403402d807a00 0x0900806805b00f40 0x23fc03003fc07f05 0xe47f806007f80fe0

def z348 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x023d4c003fff8003 0xe047a98007fff000

def z349 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xffc1cf3cc0ffffff 0xfff839e7981fffff

def z350 : W := mkw 0xf83ffffabfff7a00 0xff07ffff57ffef40 0xffffffffffffff07 0xffffffffffffffe0

def z351 : W := mkw 0x840cc31808005050 0x5081986301000a0a 0xabdcc318000070fc 0x157b986300000e1f

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e814c0000000000 0x03d0298000000000

def z353 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xfde3bef7c7f3efe7 0x7fbc77def8fe7dfc

def z354 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1a1dfc0038ff8002 0x8343bf80071ff000

def z355 : W := mkw 0xcc1febfabda87a50 0xf983fd7f57b50f4a 0xfffffffffffc7fff 0xffffffffffff8fff

def z356 : W := mkw 0x7a20144537ffaca6 0x0f440288a6fff594 0xfde2b2d73fffece7 0xffbc565ae7fffd9c

def z357 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x0bdcc210383c6062 0xe17b984207078c0c

def z358 : W := mkw 0x0000000400008484 0x0000000080001090 0xfe814d2cc0038c87 0x3fd029a598007190

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0xee81412800cc1f9f 0xbdd02825001983f3

def z360 : W := mkw 0x491304e465c5af8d 0x8922609c8cb8b5f1 0x54230ce4c7c38f01 0x0a84619c98f871e0

def z361 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0x00004c08c0000000 0x0000098118000000

def z362 : W := mkw 0xc41fc3183ca85050 0xd883f86307950a0a 0xafffc3183ffc70ff 0xf5fff86307ff8e1f

def z363 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x001c000038000000 0x0003800007000000

def z364 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x017e02c03fc07f05 0xe02fc05807f80fe0

def z365 : W := mkw 0x850cc718586d5159 0x50a198e30b0daa2b 0x021d4d28f8cc1318 0x8043a9a51f198263

def z366 : W := mkw 0x0008c00010280000 0x4001180002050000 0xabdcc210383c60e6 0xf57b984207078c1c

def z367 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x9e814c0cc0cf809b 0xb3d029819819f013

def z368 : W := mkw 0x703fff003eff5000 0xee07ffe007dfea00 0x3fffff003ffff007 0xe7ffffe007fffe00

def z369 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x0020000007038c01 0x0004000000e07180

def z370 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xdc22b0d707338ce3 0x1b84561ae0e6719c

def z371 : W := mkw 0x703bfc0026d70000 0xee077f8004dae000 0x1fbffc0007c38001 0x03f7ff8000f87000

def z372 : W := mkw 0x0100040040450109 0x002000800808a021 0x00004c08c00c0018 0x0000098118018003

def z373 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x193efc003f3f8002 0x4327df8007e7f000

def z374 : W := mkw 0x503bec0034ed0000 0xea077d80069da000 0x0b9dcc0038fc0002 0xe173b980071f8000

def z375 : W := mkw 0x0400000018285050 0x0080000003050a0a 0xaac04108383c70fe 0xf558082107078e1f

def z376 : W := mkw 0xc91feffeedc5ff8d 0xf923fdffddb8bff1 0xffffffffffcfff9f 0xfffffffffff9fff3

def z377 : W := mkw 0x8404031808005050 0x1080806301000a0a 0xa9c08318003070fe 0x7538106300060e1f

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x05a2000007000001 0x60b4400000e00000

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00002d700000000 0x1c00005ae0000000

def z380 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x7fbffd203fff9f07 0xeff7ffa407fff3e0

def z381 : W := mkw 0x681713e02f927a00 0x8d02e27c05f24f40 0x7fffb3e03ff3ff07 0xeffff67c07fe7fe0

def z382 : W := mkw 0x800403ba80000000 0x1000807750000000 0xfd82b3ffc0000000 0x1fb0567ff8000000

def z383 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xfea37defc7cf9f9f 0xbfd46fbdf8f9f3f3

def z384 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0xdc03fcffc0000000 0x1b807f9ff8000000

def z385 : W := mkw 0xf43ffb183eba5050 0xfe87ff6307d74a0a 0x017eb2103f306060 0x402fd64207e60c0c

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x6480000000000c05 0x2c90000000000180

def z387 : W := mkw 0xcc1fc3f83da87a50 0xd983f87f07b50f4a 0x017e82d03f306060 0x402fd05a07e60c0c

def z388 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814d2cc00c109e 0xbfd029a598018213

def z389 : W := mkw 0x491707e46dc5ff8d 0x8922e0fc8db8bff1 0x77ff0fe4ffc3ff05 0xeeffe1fc9ff87fe0

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x9800b01700000000 0x13001602e0000000

def z391 : W := mkw 0x0008e80000000000 0x60011d0000000000 0x1800fc0000000000 0x03001f8000000000

def z392 : W := mkw 0x810403bec000858d 0x10208077d80010b1 0xe00003ffc0001f9c 0x1c00007ff80003f3

def z393 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xab9cc318380c1018 0x9573986307018203

def z394 : W := mkw 0x7028fc0036ff0000 0x6e051f8006dfe000 0x1820fc003fff8003 0xe3041f8007fff000

def z395 : W := mkw 0x2000100002120000 0x0400020000424000 0xfda2b2d707338003 0x7fb4565ae0e67000

def z396 : W := mkw 0xf43fffbabeff5050 0xfe87fff757dfea0a 0xfffffffffffff0ff 0xfffffffffffffe1f

def z397 : W := mkw 0x2800104003122800 0x0500020800624500 0x7de2b2c00733ec07 0x6fbc565800e67d80

def z398 : W := mkw 0x811fefbac0450109 0xf023fdf75808a021 0xff9fffffc0cc1318 0x9ff3fffff8198263

def z399 : W := mkw 0x0000040000450000 0x000000800008a000 0x18004c00000f8002 0x030009800001f000

def z400 : W := mkw 0xf03ffbbab6ba0000 0xfe07ff7756d74000 0xffbfffffff300000 0x5ff7ffffffe60000

def z401 : W := mkw 0x011bec044045858d 0xe0237d808808b0b1 0xff9ffd2cc0cf9f9f 0xbff3ffa59819f3f3

def z402 : W := mkw 0x7b3bfc4577ffadaf 0xef677f88aefff5b5 0xffffffffffffffff 0xffffffffffffffff

def z403 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0xe5e202d707006ce5 0x7cbc405ae0e00d9c

def z404 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0x021d4d28f80c1018 0x8043a9a51f018203

def z405 : W := mkw 0x840cc718186d5050 0x508198e3030daa0a 0xbfddcf1838fff0ff 0xf7fbb9e3071ffe1f

def z406 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbffd2cffff8003 0xfff7ffa59ffff000

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0x21c0020000006004 0x6438004000000c00

def z408 : W := mkw 0x0100040040450109 0x002000800808a021 0x66814d28c0cc1f1d 0xacd029a5181983e3

def z409 : W := mkw 0xf03fffbab6ff0000 0xfe07fff756dfe000 0x1fbffd28ffff8003 0xe3f7ffa51ffff000

def z410 : W := mkw 0x810407bec045858d 0x102080f7d808b0b1 0xfe814fffc0cf9f9f 0xbfd029fff819f3f3

def z411 : W := mkw 0x0000000000000000 0x0000000000000000 0x0681000000c00001 0xa0d0200000180000

def z412 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabdcc31838306060 0x557b986307060c0c

def z413 : W := mkw 0x02000005000084a6 0x00400000a0001094 0x80000017000000e0 0x10000002e000001c

def z414 : W := mkw 0x2e0010451b3afcf6 0x05c00208a3675f9e 0x006000003f3ffcff 0xe00c000007e7ff9f

def z415 : W := mkw 0x6b1717e56fd7ffaf 0x8d62e2fcadfafff5 0xffffffffffffffff 0xffffffffffffffff

def z416 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x679fb3f300000000 0x0cf3f67e60000000

def z417 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xe162b2d707306ce4 0x5c2c565ae0e60d9c

def z418 : W := mkw 0x801703ba80000000 0x9002e07750000000 0xe79f03ffc0000000 0x1cf3e07ff8000000

def z419 : W := mkw 0x010000044000858d 0x00200000880010b1 0xfe814d2cc0001f9c 0x1fd029a5980003f3

def z420 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x23dc831038307064 0xe47b906207060e0c

def z421 : W := mkw 0x010407044845d58d 0x002080e08908bab1 0xffdd4f2cf8cfff9f 0xfffba9e59f19fff3

def z422 : W := mkw 0x2e0010451b3afcf6 0x05c00208a3675f9e 0xfde2b2d73f3ffcff 0xffbc565ae7e7ff9f

def z423 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x17bf3c003fc38001 0xe2f7e78007f87000

def z424 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfda2b2d707038c01 0x1fb4565ae0e07180

def z425 : W := mkw 0x800cc31800000000 0x5001986300000000 0xff9dcf3cc0000000 0x1ff3b9e798000000

def z426 : W := mkw 0x881febfa81002800 0xf103fd7f50200500 0xffffffffc7006c05 0x7ffffffff8e00d80

def z427 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa25c4318380c70fc 0x944b886307018e1f

def z428 : W := mkw 0x0004030000000000 0x0000806000000000 0x239c030000000000 0x0473806000000000

def z429 : W := mkw 0x801febbe80008484 0xf003fd77d0001090 0xff9fffffc0038c87 0x3ff3fffff8007190

def z430 : W := mkw 0x0800004001002800 0x0100000800200500 0x0060000007006c05 0x600c000000e00d80

def z431 : W := mkw 0x6a1713e12f927a22 0x8d42e27c25f24f44 0x017eb2d33f306060 0x402fd65a67e60c0c

def z432 : W := mkw 0x0000040000450000 0x000000800008a000 0x7e814d2000cf9f07 0xafd029a40019f3e0

def z433 : W := mkw 0x840ceb1a98285050 0x70819d6353050a0a 0xbbdcff1ff83c70fe 0xf77b9fe3ff078e1f

def z434 : W := mkw 0x783ffbe03fba7a00 0xef07ff7c07f74f40 0x017eb2c03f306000 0x402fd65807e60c00

def z435 : W := mkw 0x23001405425785af 0x04600280a84af0b5 0x9800fc1fc03f80fa 0x13001f83f807f01f

def z436 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0x0060000007ffffff 0xe00c000000ffffff

def z437 : W := mkw 0xcc1fc3f83da87a50 0xd983f87f07b50f4a 0x67ff43e83fcc7f1d 0xecffe87d07f98fe3

def z438 : W := mkw 0x850cc718586d5159 0x50a198e30b0daa2b 0xabddcf38f8fc73fe 0xf57bb9e71f1f8e7f

def z439 : W := mkw 0x401be80024800000 0xe8037d0004900000 0x1fbffc003fc00001 0xe3f7ff8007f80000

def z440 : W := mkw 0x480403e02d807a00 0x0900807c05b00f40 0x606003e03fc07f05 0xec0c007c07f80fe0

def z441 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa15c8318383070fc 0x542b906307060e1f

def z442 : W := mkw 0x783ffbe03fba7a00 0xef07ff7c07f74f40 0x67ffb3e03ff07f05 0xecfff67c07fe0fe0

def z443 : W := mkw 0x811fefbac0450109 0xf023fdf75808a021 0x021d4d28c0cc1318 0x8043a9a518198263

def z444 : W := mkw 0xaa1ffbff8312aca6 0xf543ff7ff0625594 0xfdfeb2d70733ece7 0x7fbfd65ae0e67d9c

def z445 : W := mkw 0x0800004001002800 0x0100000800200500 0x442200c007000c01 0x0884401800e00180

def z446 : W := mkw 0x0000000008005000 0x0000000001000a00 0x0040000038007004 0xe008000007000e00

def z447 : W := mkw 0x400000002c805200 0x0800000005900a40 0x0000000038c01300 0x8000000007180260

def z448 : W := mkw 0x8404031818285050 0x1080806303050a0a 0xa0400318383c70fe 0xf408006307078e1f

def z449 : W := mkw 0xb428fc18127f0050 0x76851f83024fe00a 0x9800fc18003f80fa 0x13001f830007f01f

def z450 : W := mkw 0xf53fff1c7effd5dd 0xfea7ffe38fdffabb 0xffffff3cffffffff 0xffffffe79fffffff

def z451 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xabdef3db383c70fe 0xf57bde7b67078e1f

def z452 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x8a1cc118383c10fa 0x914398230707821f

def z453 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xf8004d2cc00f9f9e 0x1f0009a59801f3f3

def z454 : W := mkw 0xcd1fc7fc7dedffdd 0xd9a3f8ff8fbdbffb 0xffffcffcffffffff 0xfffff9ff9fffffff

def z455 : W := mkw 0xc81febfaad807a00 0xf903fd7f55b00f40 0xffffffffff006000 0x5fffffffffe00c00

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x0980800000300002 0x6130100000060000

def z457 : W := mkw 0xae0cd35d1b3afcf6 0x55c19a6ba3675f9e 0xabfcc3183f3ffcff 0xf57f986307e7ff9f

def z458 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xefff83f03ff07fe7 0xfdfff07e07fe0ffc

def z459 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x551fbef7c0000000 0x0aa3f7def8000000

def z460 : W := mkw 0x8c0cc3f819287a50 0x5181987f03250f4a 0xebdcc3f8383c7ffe 0xfd7b987f07078fff

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x88008010003000e2 0x110010020006001c

def z462 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x031ffffbc0000000 0x0063ffff78000000

def z463 : W := mkw 0x001bec0000450000 0xe0037d800008a000 0x1f9ffc0000cf8003 0xa3f3ff800019f000

def z464 : W := mkw 0x0004030008005000 0x0000806001000a00 0x021c010038001000 0x8043802007000200

def z465 : W := mkw 0x010000044000858d 0x00200000880010b1 0xe681012cc0c01f9d 0xbcd02025981803f3

def z466 : W := mkw 0x8004031800000000 0x1000806300000000 0xa000031800000000 0x1400006300000000

def z467 : W := mkw 0x7020100036ba0000 0x0e04020006d74000 0x002000003f300000 0x4004000007e60000

def z468 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x679f4fe8c0000000 0x0cf3e9fd18000000

def z469 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfc80000400cf9f9f 0xbf9000008019f3f3

def z470 : W := mkw 0x0800004001002800 0x0100000800200500 0xede282d007306ce7 0x7dbc505a00e60d9c

def z471 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x001c000038000000 0x0003800007000000

def z472 : W := mkw 0x782014403fff7a00 0x0f04028807ffef40 0x006000003fffff07 0xe00c000007ffffe0

def z473 : W := mkw 0x0800004001002800 0x0100000800200500 0xfde2b2d707006c05 0x7fbc565ae0e00d80

def z474 : W := mkw 0x0404030018285050 0x0080806003050a0a 0x23dc0300383c70fe 0xe47b806007078e1f

def z475 : W := mkw 0x2a1338e78312aca6 0xa542671cf0625594 0xfde3bef7c733ece7 0x7fbc77def8e67d9c

def z476 : W := mkw 0x713bfc0476ff858d 0xee277f808edff0b1 0x5fbffc24ffff8f03 0xebf7ff849ffff1e0

def z477 : W := mkw 0x801febba90280000 0xf003fd7752050000 0xff9ffffff83c0002 0xfff3ffffff078000

def z478 : W := mkw 0x0000000400008484 0x0000000080001090 0xfe81012400c39f87 0xbfd02024801873f0

def z479 : W := mkw 0x840cc3ba98285050 0x5081987753050a0a 0xebdcc3fff83c70fe 0xfd7b987fff078e1f

def z480 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x033ffc003ffc0000 0xc067ff8007ff8000

def z481 : W := mkw 0xa21ffbbf821284a6 0xf443ff77f0425094 0xff9fffffc03380e2 0x1ff3fffff806701c

def z482 : W := mkw 0x080000e001002a00 0x0100001c00200540 0x400000e000000f00 0x0800001c000001e0

def z483 : W := mkw 0x481703e025802a00 0x8902e07c04b00540 0x67bf03e007c00f01 0x0cf7e07c00f801e0

def z484 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x001c000000000000 0x0003800000000000

def z485 : W := mkw 0x080403e009007a00 0x0100807c01200f40 0x66c103e000c07f05 0xacd8207c00180fe0

def z486 : W := mkw 0x22001005021284a6 0x04400200a0425094 0x1000300700038000 0x02000600e0007000

def z487 : W := mkw 0x513bec0474ed858d 0xea277d808e9db0b1 0xfe9d4d2cf8cf9f9f 0xbfd3a9a59f19f3f3

def z488 : W := mkw 0x001be80000000000 0xe0037d0000000000 0x021d4c0000000000 0x0043a98000000000

def z489 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x679f03e038c01300 0x8cf3e07c07180260

def z490 : W := mkw 0x0800004009007a00 0x0100000801200f40 0x0040000000007f04 0x0008000000000fe0

def z491 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x10000c04c0038000 0x0200018098007000

def z492 : W := mkw 0x800cc31800000000 0x5001986300000000 0xab9cc318000c109e 0xb573986300018213

def z493 : W := mkw 0xaa08f85f8312aca6 0x75411f0bf0625594 0xfde2fedfc733ece7 0x7fbc5fdbf8e67d9c

def z494 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x646303e007c07f05 0x0c8c607c00f80fe0

def z495 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x65e302e007c06f05 0x6cbc605c00f80de0

def z496 : W := mkw 0x7120140476ff858d 0x0e2402808edff0b1 0x002000003fff9f9f 0xe004000007fff3f3

def z497 : W := mkw 0x8400001800000050 0x108000030000000a 0x80000018000000f8 0x100000030000001f

def z498 : W := mkw 0x490004446dc5ff8d 0x092000888db8bff1 0xfee14d2cffcfff9f 0xffdc29a59ff9fff3

def z499 : W := mkw 0x783bfce037ff2a00 0xef077f9c06ffe540 0x5fbffce03fff8f03 0xebf7ff9c07fff1e0

def z500 : W := mkw 0x0000040000450000 0x000000800008a000 0x14010c0000c38001 0x0280218000187000

def z501 : W := mkw 0x2a1338e78312aca6 0xa542671cf0625594 0x54233ce7c7038c01 0x0a84679cf8e07180

def z502 : W := mkw 0xc01febbaa4800000 0xf803fd7754900000 0xffbfffffffc00001 0xfff7fffffff80000

def z503 : W := mkw 0x2000100002120000 0x0400020000424000 0x0122b00007300000 0x4024560000e60000

def z504 : W := mkw 0x4013000024800000 0x8802600004900000 0x013e00003f000000 0x4027c00007e00000

def z505 : W := mkw 0x0000000400008484 0x0000000080001090 0xfdc082140033ece7 0x7fb8104280067d9c

def z506 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x23fe03c03f007004 0xe47fc07807e00e00

def z507 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x561f7defc0000000 0x0ac3efbdf8000000

def z508 : W := mkw 0x3028fc00127f0000 0x66051f80024fe000 0x1b9cfc00383f8002 0xe3739f800707f000

def z509 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x002200c007000000 0x0004401800e00000

def z510 : W := mkw 0x7a3fffe53ffffea6 0xef47fffca7ffffd4 0xfffffff73fffffe7 0xfffffffee7fffffc

def z511 : W := mkw 0x8e0cc35d1928fcf6 0x51c1986ba3251f9e 0xebdcc3df383c7cfe 0xfd7b987be7078f9f

def z512 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x9860b0170733ece7 0x730c1602e0e67d9c

def z513 : W := mkw 0x801fefba80450000 0xf003fdf75008a000 0xff9fffffc0cf8003 0xbff3fffff819f000

def z514 : W := mkw 0xcc1fc3f83da87a50 0xd983f87f07b50f4a 0x67ff83f03ff07f65 0xecfff07e07fe0fec

def z515 : W := mkw 0x2008d000123a0000 0x44011a0002474000 0x1fbef0003f3f8003 0xe3f7de0007e7f000

def z516 : W := mkw 0x22001005021284a6 0x04400200a0425094 0xb9c0b2170033e0e6 0x77381642e0067c1c

def z517 : W := mkw 0x3028f800123a0000 0x66051f0002474000 0x0000b00000300000 0x0000160000060000

def z518 : W := mkw 0x850cc71c586dd5dd 0x50a198e38b0dbabb 0xbbdccf1cf83ff0fe 0xf77b99e39f07fe1f

def z519 : W := mkw 0x080403e009007a00 0x0100807c01200f40 0x004002c000006000 0x0008005800000c00

def z520 : W := mkw 0xae0cd3591b3a7872 0x55c19a6b23674f0e 0x017eb2d33f306060 0x402fd65a67e60c0c

def z521 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff03e03f006000 0x4cffe07c07e00c00

def z522 : W := mkw 0xfc3ffff83fff7a50 0xff87ffff07ffef4a 0xfffffff83fffffff 0xffffffff07ffffff

def z523 : W := mkw 0x800cc3ba80000000 0x5001987750000000 0xeb9cc3ffc0000000 0x1d73987ff8000000

def z524 : W := mkw 0x001be80000000000 0xe0037d0000000000 0x011eb00000000000 0x0023d60000000000

def z525 : W := mkw 0x8404031808005050 0x1080806301000a0a 0xaac04318000c70fe 0xb558086300018e1f

def z526 : W := mkw 0x850cc71c586dd5dd 0x50a198e38b0dbabb 0xfe9d4d2cf8cf9f9f 0xbfd3a9a59f19f3f3

def z527 : W := mkw 0x0000040400458484 0x000000808008b090 0xfe814c0400cf8c87 0xbfd029808019f190

def z528 : W := mkw 0x7a20144537ffaca6 0x0f440288a6fff594 0x006000003fffece7 0xe00c000007fffd9c

def z529 : W := mkw 0x800ceb1a80000000 0x70019d6350000000 0xbb9cff1fc0000000 0x17739fe3f8000000

def z530 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x76810d24c0c39f05 0xaed021a4981873e0

def z531 : W := mkw 0x0008c00010280000 0x4001180002050000 0x011c800038300000 0x4023900007060000

def z532 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x669d012038c01f05 0xacd3a024071803e0

def z533 : W := mkw 0x22001005021284a6 0x04400200a0425094 0xfd82b2d7003380e2 0x1fb0565ae006701c

def z534 : W := mkw 0x0000000000000000 0x0000000000000000 0x0140821000306060 0x4028104200060c0c

def z535 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x00000000000f809a 0x000000000001f013

def z536 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x1fbffc003f300000 0x43f7ff8007e60000

def z537 : W := mkw 0x793fffe47fffff8d 0xef27fffc8ffffff1 0xffffffecffffff9f 0xfffffffd9ffffff3

def z538 : W := mkw 0x8508c41c506d85dd 0x50a118838a0db0bb 0x9800cc1cc03f80fa 0x130019839807f01f

def z539 : W := mkw 0x4a1703e52d80fea6 0x8942e07ca5b01fd4 0xe7ff03f73fc07fe5 0xfcffe07ee7f80ffc

def z540 : W := mkw 0x811fefbec045858d 0xf023fdf7d808b0b1 0xfe9d4d2cc0cf9f9f 0xbfd3a9a59819f3f3

def z541 : W := mkw 0x850cc31c5828d5dd 0x50a198638b051abb 0xebdcc33cf83c7ffe 0xfd7b98679f078fff

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0xa980821000000000 0x1530104200000000

def z543 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xfee14d2cc7ffffff 0xffdc29a598ffffff

def z544 : W := mkw 0x0008c00000000000 0x4001180000000000 0x0b9cc00000000000 0x0173980000000000

def z545 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xabddcf38f83c70fe 0xf57bb9e71f078e1f

def z546 : W := mkw 0x491703e46d80ff8d 0x8922e07c8db01ff1 0xe7ff03ecffc07f9d 0xfcffe07d9ff80ff3

def z547 : W := mkw 0x2a1713e50312aca6 0x8542e27ca0625594 0xffffb3f70733ece7 0x7ffff67ee0e67d9c

def z548 : W := mkw 0xf43ffb183eba5050 0xfe87ff6307d74a0a 0xabfef3183f3c70fe 0xf57fde6307e78e1f

def z549 : W := mkw 0x800403ba80000000 0x1000807750000000 0x00000128c0000000 0x0000002518000000

def z550 : W := mkw 0x0000040000450000 0x000000800008a000 0x02014c0000cc0000 0x8040298000198000

def z551 : W := mkw 0x2a00104103122822 0x0540020820624504 0x002230c307000000 0x0004461860e00000

def z552 : W := mkw 0x2a00104103122822 0x0540020820624504 0x65e2b2d307306c65 0x6cbc565a60e60d8c

def z553 : W := mkw 0x850cc71c586dd5dd 0x50a198e38b0dbabb 0xabdcc31838ffffff 0xf57b9863071fffff

def z554 : W := mkw 0x7020140036ff0000 0x0e04028006dfe000 0x1ea14c003fff8003 0xe3d4298007fff000

def z555 : W := mkw 0x8408c01810280050 0x508118030205000a 0xaa80c118003c10fe 0xb55018230007821f

def z556 : W := mkw 0x401bc00034a80000 0xc803780006950000 0x0fbfc0003ffc0003 0xe1f7f80007ff8000

def z557 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x54010c24c0cf9f9f 0xaa8021849819f3f3

def z558 : W := mkw 0x05000404586dd5dd 0x00a000808b0dbabb 0xfec14d2cf8ffffff 0xffd829a59f1fffff

def z559 : W := mkw 0x8108ec1ec045858d 0x70211d83d808b0b1 0x9800fc1fc00f809a 0x13001f83f801f013

def z560 : W := mkw 0x2000100002120000 0x0400020000424000 0x1800b00000338002 0x0300160000067000

def z561 : W := mkw 0x723bfc0536ff84a6 0xee477f80a6dff094 0x9fbffc173fff80e3 0xf3f7ff82e7fff01c

def z562 : W := mkw 0x001be80000000000 0xe0037d0000000000 0xff9ffed700000000 0x1ff3ffdae0000000

def z563 : W := mkw 0xf03fffbab6ff0000 0xfe07fff756dfe000 0x1fbffed33fff8003 0xe3f7ffda67fff000

def z564 : W := mkw 0x401703a024800000 0x8802e07404900000 0x67bf03e03fc00001 0xecf7e07c07f80000

def z565 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xf4010d2cc0c39f9d 0x1e8021a5981873f3

def z566 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x98004c0cc0cf9f9f 0xb30009819819f3f3

def z567 : W := mkw 0x0800004001002800 0x0100000800200500 0x67e303e007c07f05 0xecfc607c00f80fe0

def z568 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x6681012000cf9f9f 0xacd020240019f3f3

def z569 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x66a301e007c01f05 0xacd4603c00f803e0

def z570 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0x0040000000006ce4 0x0008000000000d9c

def z571 : W := mkw 0x081703e001002800 0x8102e07c00200500 0x67ff03e007006c05 0x6cffe07c00e00d80

def z572 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xab9dcf38c0000000 0x1573b9e718000000

def z573 : W := mkw 0x303bfc00127f0000 0xe6077f80024fe000 0x1f9ffc00003f8002 0x03f3ff800007f000

def z574 : W := mkw 0x00172ba280000000 0xa002e57450000000 0x779f3fe7c0000000 0x0ef3e7fcf8000000

def z575 : W := mkw 0x783bfc4037ff2800 0xef077f8806ffe500 0x7ffffec03fffec07 0xefffffd807fffd80

def z576 : W := mkw 0xea1ffbffaf92fea6 0xfd43ff7ff5f25fd4 0xfffffffffff3ffe7 0xfffffffffffe7ffc

def z577 : W := mkw 0x401703002c805000 0x8802e06005900a00 0x27ff03003fc07005 0xe4ffe06007f80e00

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x0102b2d300000000 0x0020565a60000000

def z579 : W := mkw 0x2a00104103122822 0x0540020820624504 0xa9e2b2d3073060e6 0x753c565a60e60c1c

def z580 : W := mkw 0xfe3fff5d3ffffcf6 0xffc7ffeba7ffff9e 0xffffffdf3ffffcff 0xfffffffbe7ffff9f

def z581 : W := mkw 0x783717e03fff7a00 0x8f06e2fc07ffef40 0x67ff03e03fffff07 0xecffe07c07ffffe0

def z582 : W := mkw 0xaa1ffbfb83122822 0xf543ff7f70624504 0xffffffffc7306060 0x5ffffffff8e60c0c

def z583 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x9962b2d70733e0e2 0x532c565ae0e67c1c

def z584 : W := mkw 0x001703a000000000 0x8002e07400000000 0xff9f4fecc0000000 0x1ff3e9fd98000000

def z585 : W := mkw 0x22001005021284a6 0x04400200a0425094 0x9da2b017073380e3 0x73b45602e0e6701c

def z586 : W := mkw 0xaa0413ff8312aca6 0x1540827ff0625594 0xfde2b3ffc733ece7 0x7fbc567ff8e67d9c

def z587 : W := mkw 0x0000000000000000 0x0000000000000000 0x540230c700000000 0x0a804618e0000000

def z588 : W := mkw 0xaf0cd75d5b7ffdff 0x55e19aebab6fffbf 0xffffffffffffffff 0xffffffffffffffff

def z589 : W := mkw 0x411707a46cc5d78d 0x8822e0f48d98baf1 0xfe9d4d2cf8cf9f9f 0xbfd3a9a59f19f3f3

def z590 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xffdef3df383c70fe 0xfffbde7be7078e1f

def z591 : W := mkw 0x8408c01810280050 0x508118030205000a 0x8b9cc018383c00fa 0xf17398030707801f

def z592 : W := mkw 0x0000000400008484 0x0000000080001090 0xe000000400000c84 0x1c00000080000190

def z593 : W := mkw 0x01132ca6c045858d 0xa0226594d808b0b1 0x54033ce7c0c38f01 0x0a80679cf81871e0

def z594 : W := mkw 0x7020140036ff0000 0x0e04028006dfe000 0x1da2b0003fff8003 0xe3b4560007fff000

def z595 : W := mkw 0xb42cff181a7f5050 0x76859fe3034fea0a 0xbbdcff18383ff0fe 0xf77b9fe30707fe1f

def z596 : W := mkw 0x78373fe02fd77a00 0xaf06e7fc05faef40 0x77ff3fe03fc3ff05 0xeeffe7fc07f87fe0

def z597 : W := mkw 0x743bfc003eff5050 0xee877f8007dfea0a 0x1ffffc003ffff0ff 0xe3ffff8007fffe1f

def z598 : W := mkw 0x4813004025802800 0x8902600804b00500 0x67ff02c03fc06c05 0xecffe05807f80d80

def z599 : W := mkw 0x0800004001002800 0x0100000800200500 0x016202c007006000 0x402c405800e00c00

def z600 : W := mkw 0xc41fc3b83ca85250 0xd883f87707950a4a 0x021d412838cc1318 0x8043a82507198263

def z601 : W := mkw 0x3a28fc45137faca6 0x67451f88a26ff594 0xfde2fed7073fece7 0x7fbc5fdae0e7fd9c

def z602 : W := mkw 0x7a3bfc4137ff2822 0xef477f8826ffe504 0x1ffffed33fffe063 0xe3ffffda67fffc0c

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000c01f05 0xa0000000001803e0

def z604 : W := mkw 0x201bf80002120000 0xe4037f0000424000 0x1fbffc0007338003 0x63f7ff8000e67000

def z605 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xe2014d2cc0cc1f9c 0x9c4029a5981983f3

def z606 : W := mkw 0x8404031808005050 0x1080806301000a0a 0xa3dc0318380070fc 0xf47b806307000e1f

def z607 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xf46232d70703ece5 0x1e8c465ae0e07d9c

def z608 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xaa9c4108380c109e 0xb553882107018213

def z609 : W := mkw 0x7033380026920000 0xae06670004d24000 0x0022300007000000 0x0004460000e00000

def z610 : W := mkw 0x0000040000450000 0x000000800008a000 0xfe814d2cc0cf8003 0xbfd029a59819f000

def z611 : W := mkw 0xd03fefbab4ed0000 0xfa07fdf7569da000 0xff9ffffff8cc0000 0x9ff3ffffff198000

def z612 : W := mkw 0x0000000400008484 0x0000000080001090 0xfe80410c000f9c9f 0xbfd008218001f393

def z613 : W := mkw 0x800cc31808005000 0x5001986301000a00 0xabdcc31838007004 0xf57b986307000e00

def z614 : W := mkw 0x7a3bf84537baaca6 0xef477f08a6f75594 0xfdfeb2d73f33ece7 0x7fbfd65ae7e67d9c

def z615 : W := mkw 0x491707e06dc57b09 0x8922e0fc0db8af61 0x67ff4fe8ffcc7f1d 0xecffe9fd1ff98fe3

def z616 : W := mkw 0x0004030008005000 0x0000806001000a00 0xabdc8310383070e6 0xf57b906207060e1c

def z617 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x07bf01203fc01301 0xe0f7e02407f80260

def z618 : W := mkw 0x4113040464c5858d 0x882260808c98b0b1 0xffbf4d2cffcf9f9f 0xfff7e9a59ff9f3f3

def z619 : W := mkw 0xd03fefbab4ed0000 0xfa07fdf7569da000 0x021d4d28f8cc0000 0x8043a9a51f198000

def z620 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0xfdc2b2d700006ce4 0x1fb8565ae0000d9c

def z621 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1c23fc0007ff8003 0x03847f8000fff000

def z622 : W := mkw 0x0008c400106d0000 0x40011880020da000 0x1f9dcc0038ff8003 0xe3f3b980071ff000

def z623 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0xfe81fd3fc0000000 0x1fd03fa7f8000000

def z624 : W := mkw 0x3128fc04527f858d 0x66251f808a4ff0b1 0xfe81fd2cc0ff9f9f 0xbfd03fa5981ff3f3

def z625 : W := mkw 0x703fffa036ff0000 0xee07fff406dfe000 0x7fbfffe03fff8003 0xeff7fffc07fff000

def z626 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa9dc8210383060e6 0x753b904207060c1c

def z627 : W := mkw 0x800cc31800000000 0x5001986300000000 0xff9ef3df00000000 0x1ff3de7be0000000

def z628 : W := mkw 0x081703e009007a00 0x8102e07c01200f40 0x67df03e000007f04 0x0cfbe07c00000fe0

def z629 : W := mkw 0x0000000000000000 0x0000000000000000 0x2280010000001004 0xa450002000000200

def z630 : W := mkw 0x480000402d807a00 0x0900000805b00f40 0x006000003f006000 0x400c000007e00c00

def z631 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x5e814c24c0cf8f03 0xabd029849819f1e0

def z632 : W := mkw 0x2a0413e50b12fea6 0x0540827ca1625fd4 0xfde2b3f70733ffe7 0x7fbc567ee0e67ffc

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0x02004108000c1018 0x8040082100018203

def z634 : W := mkw 0x2a00104103122822 0x0540020820624504 0x0060000007306060 0x400c000000e60c0c

def z635 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe814d2cc0c38f01 0x1fd029a5981871e0

def z636 : W := mkw 0x0000000400008484 0x0000000080001090 0x0000000000038c87 0x2000000000007190

def z637 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc80000400000000 0x1f90000080000000

def z638 : W := mkw 0x481febe02d807a00 0xe903fd7c05b00f40 0x7fffffe03fc07f05 0xeffffffc07f80fe0

def z639 : W := mkw 0x6a1713e12f927a22 0x8d42e27c25f24f44 0x67ffb3f33ff07f65 0xecfff67e67fe0fec

def z640 : W := mkw 0x0a00004101002822 0x0140000820200504 0x004002d300006060 0x0008005a60000c0c

def z641 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfca230c707038c87 0x3f944618e0e07190

def z642 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfe9d4d2cc0000000 0x1fd3a9a598000000

def z643 : W := mkw 0x05000404586dd5dd 0x00a000808b0dbabb 0x0040000038ffffff 0xe0080000071fffff

def z644 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x0bbef0003f3c0002 0xe177de0007e78000

def z645 : W := mkw 0x800403ba80000000 0x1000807750000000 0xfe814fffc0000000 0x1fd029fff8000000

def z646 : W := mkw 0x0400000018285050 0x0080000003050a0a 0x00000000380c1018 0x8000000007018203

def z647 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xfde2fedfc73fecff 0x7fbc5fdbf8e7fd9f

def z648 : W := mkw 0xaa1ffbff8312aca6 0xf543ff7ff0625594 0xffbfffffc7038c01 0x1ff7fffff8e07180

def z649 : W := mkw 0xa208f81f821284a6 0x74411f03f0425094 0x9800fc1fc03380e2 0x13001f83f806701c

def z650 : W := mkw 0x000403a008005200 0x0000807401000a40 0x0000012000001300 0x0000002400000260

def z651 : W := mkw 0xc41fc3b83ca85250 0xd883f87707950a4a 0xabddc33838fc73fe 0xf57bb867071f8e7f

def z652 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x02014d28c0cf9f9f 0xa04029a51819f3f3

def z653 : W := mkw 0x000403a000000000 0x0000807400000000 0x600003e000000000 0x0c00007c00000000

def z654 : W := mkw 0x7120140476ff858d 0x0e2402808edff0b1 0xfea14d2cffff9f9f 0xffd429a59ffff3f3

def z655 : W := mkw 0x0100040040450109 0x002000800808a021 0xfe814d2cc0cc1318 0x9fd029a598198263

def z656 : W := mkw 0x0008c00010280000 0x4001180002050000 0x0800c000003c0002 0x0100180000078000

def z657 : W := mkw 0x503be80034a80000 0xea077d0006950000 0x001c000038000000 0x0003800007000000

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000c109e 0xa000000000018213

def z659 : W := mkw 0x6a1310e52792aea6 0x8d42621ca4f255d4 0x542330e707c38f01 0x0a84661ce0f871e0

def z660 : W := mkw 0x8508c41c506d85dd 0x50a118838a0db0bb 0xfe81cd3cc0ff9fff 0xbfd039a7981ff3ff

def z661 : W := mkw 0x0400000008005050 0x0080000001000a0a 0x00400000000070fc 0x0008000000000e1f

def z662 : W := mkw 0x70333c0036ff0000 0xae06678006dfe000 0x14233c003fff8003 0xe284678007fff000

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00001080000109c 0x1400002100000213

def z664 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xdc014c2cc0cf8f9b 0x1b8029859819f1f3

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000012cc0000000 0x1c00002598000000

def z666 : W := mkw 0xae0cd35d1b3afcf6 0x55c19a6ba3675f9e 0xfdfeb2d73f33ece7 0x7fbfd65ae7e67d9c

def z667 : W := mkw 0x6a1310452792aca6 0x8d426208a4f25594 0xffffb2d73ff3ece7 0xfffff65ae7fe7d9c

def z668 : W := mkw 0x4000000024800000 0x0800000004900000 0x002000003fc00001 0xe004000007f80000

def z669 : W := mkw 0x0108c404506d858d 0x402118808a0db0b1 0xff9dcd2cf8ff9f9f 0xfff3b9a59f1ff3f3

def z670 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0x400000c700000c00 0x08000018e0000180

def z671 : W := mkw 0x0400000018285050 0x0080000003050a0a 0xa9c08210383c70fe 0xf538104207078e1f

def z672 : W := mkw 0x840cc31810280050 0x508198630205000a 0xab9cc318003c00fa 0x157398630007801f

def z673 : W := mkw 0x71333c0466d7858d 0xae2667808cdaf0b1 0x54233c24c7c38f01 0x0a84678498f871e0

def z674 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xe11eb3ffc0000000 0x1c23d67ff8000000

def z675 : W := mkw 0xa40cd3181a3a5050 0x54819a6303474a0a 0xbffef3183f3ff0ff 0xf7ffde6307e7fe1f

def z676 : W := mkw 0xae0cd3591b3a7872 0x55c19a6b23674f0e 0xabfef3db3f3c70fe 0xf57fde7b67e78e1f

def z677 : W := mkw 0x481fc3e03da87a00 0xc903f87c07b50f40 0x6fffc3e03ffc7f07 0xedfff87c07ff8fe0

def z678 : W := mkw 0x801be81a80000000 0xf0037d0350000000 0x9f9ffc1fc0000000 0x13f3ff83f8000000

def z679 : W := mkw 0x703bfc0436ff8484 0xee077f8086dff090 0xffbffc043fff8c87 0xfff7ff8087fff190

def z680 : W := mkw 0x2a00104103122822 0x0540020820624504 0xfde2b2d707306060 0x5fbc565ae0e60c0c

def z681 : W := mkw 0xf43fff183eff5050 0xfe87ffe307dfea0a 0x1ffffe103fffe063 0xe3ffffc207fffc0c

def z682 : W := mkw 0x30203c0002570000 0x26040780004ae000 0x10003c0000038000 0x0200078000007000

def z683 : W := mkw 0x0100040040450109 0x002000800808a021 0x00010c20c0c00300 0x0000218418180060

def z684 : W := mkw 0x001be80000000000 0xe0037d0000000000 0xff9ffd2cc0000000 0x1ff3ffa598000000

def z685 : W := mkw 0x480000402d807a00 0x0900000805b00f40 0x66e101203fc07f05 0xecdc202407f80fe0

def z686 : W := mkw 0x6a1713e52f92fea6 0x8d42e27ca5f25fd4 0x77ff33e73fc3ff05 0xeeffe67ce7f87fe0

def z687 : W := mkw 0x010000044000858d 0x00200000880010b1 0x0000000000001f9c 0x00000000000003f3

def z688 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xe06002d70733ece7 0x7c0c005ae0e67d9c

def z689 : W := mkw 0x010000044000858d 0x00200000880010b1 0x40000024c0000f00 0x08000004980001e0

def z690 : W := mkw 0xf03fff1836ff0000 0xfe07ffe306dfe000 0xbfbfff183fff8003 0xf7f7ffe307fff000

def z691 : W := mkw 0x7a3bfc4537ffaca6 0xef477f88a6fff594 0x5fbffcc73fff8c03 0xebf7ff98e7fff180

def z692 : W := mkw 0x2000100002120000 0x0400020000424000 0x1422300007038001 0x0284460000e07000

def z693 : W := mkw 0x0a0000450100aca6 0x01400008a0201594 0xe9c082d700306ce6 0x7d38105ae0060d9c

def z694 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xfde2b2d707ffffff 0xffbc565ae0ffffff

def z695 : W := mkw 0x78333ce027d72a00 0xaf06679c04fae540 0x54233ce007c38f01 0x0a84679c00f871e0

def z696 : W := mkw 0x0004030008005000 0x0000806001000a00 0x2040030000007004 0x0408006000000e00

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x4401002000c00f01 0x08802004001801e0

def z698 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x23dd032038c07304 0xe47ba06407180e60

def z699 : W := mkw 0x6a1713e52f92fea6 0x8d42e27ca5f25fd4 0xfdfeb2d73f33ece7 0x7fbfd65ae7e67d9c

def z700 : W := mkw 0xcc1fc3f83da87a50 0xd983f87f07b50f4a 0xabfec3d83f3c70fe 0xf57fd87b07e78e1f

def z701 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x1f9ffed300000000 0x03f3ffda60000000

def z702 : W := mkw 0x0000000400008484 0x0000000080001090 0xfd82b2d700038c87 0x3fb0565ae0007190

def z703 : W := mkw 0x401300a024800200 0x8802601404900040 0x0001002000c00300 0x0000200400180060

def z704 : W := mkw 0x8504071c4845d5dd 0x10a080e38908babb 0xfec14f3cc0cfffff 0xbfd829e79819ffff

def z705 : W := mkw 0xb03fffba927f0000 0xf607fff7524fe000 0xff9fffffc03f8002 0x1ff3fffff807f000

def z706 : W := mkw 0x4c1703e03da87a50 0x8982e07c07b50f4a 0x67ff03e03ffc7fff 0xecffe07c07ff8fff

def z707 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff83c60fa 0x5ffbffffff078c1f

def z708 : W := mkw 0x000028a280000000 0x2000051450000000 0x50003ce7c0000000 0x0a00079cf8000000

def z709 : W := mkw 0x4013000024800000 0x8802600004900000 0x07bf00003fc01f05 0xe0f7e00007f803e0

def z710 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x9b1fffffc0000000 0x1363fffff8000000

def z711 : W := mkw 0xaf0cd75d5b7ffdff 0x55e19aebab6fffbf 0xabfcc3183fffffff 0xf57f986307ffffff

def z712 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1ffffe103fffe063 0xe3ffffc207fffc0c

def z713 : W := mkw 0xc81703faad807a00 0x9902e07f55b00f40 0xffff4fffffc07f05 0xffffe9fffff80fe0

def z714 : W := mkw 0x811fefbec045858d 0xf023fdf7d808b0b1 0x011eb2d300cf9f9f 0xa023d65a6019f3f3

def z715 : W := mkw 0x850cc71c586dd5dd 0x50a198e38b0dbabb 0x555d8e34f8f3ef61 0x4aabb1c69f1e7dec

def z716 : W := mkw 0x491707e46dc5ff8d 0x8922e0fc8db8bff1 0x997e4eccff0fe09a 0x532fc9d99fe1fc13

def z717 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x5de2b2d70733ec63 0x6bbc565ae0e67d8c

def z718 : W := mkw 0xc01febbaa4800000 0xf803fd7754900000 0xff9ffffff8c00000 0x9ff3ffffff180000

def z719 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0xbfbffd28ffff939f 0xf7f7ffa51ffff273

def z720 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0cc1f9f 0xbff3fffff81983f3

def z721 : W := mkw 0xa708d41d527f85ff 0x54e11a83aa4ff0bf 0x9800fc1fc03f80fa 0x13001f83f807f01f

def z722 : W := mkw 0x840cc3ba98285050 0x5081987753050a0a 0xffddcffff83c70fe 0xfffbb9ffff078e1f

def z723 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe81fd3fc0cf9f9f 0xbfd03fa7f819f3f3

def z724 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x9fbffc103fff80e3 0xf3f7ff8207fff01c

def z725 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff8fc7fff 0xfffbffffff1f8fff

def z726 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x5e814d2cc0cf9f1b 0xabd029a59819f3e3

def z727 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x463f00e03fc00f01 0x88c7e01c07f801e0

def z728 : W := mkw 0xae0cd35d1b3afcf6 0x55c19a6ba3675f9e 0x563e71cf3f0f9c19 0x8ac7ce39e7e1f383

def z729 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x023d4c003fcf8001 0x8047a98007f9f000

def z730 : W := mkw 0x800ceb1a80000000 0x70019d6350000000 0xff9effdfc0000000 0x1ff3dffbf8000000

def z731 : W := mkw 0x0a0403450900fca6 0x01408068a1201f94 0xe04003d700007ce4 0x1c08007ae0000f9c

def z732 : W := mkw 0x7020140036ff0000 0x0e04028006dfe000 0x03bc00003fff8003 0xe077800007fff000

def z733 : W := mkw 0x743bfc0036ff0050 0xee877f8006dfe00a 0x1fbffc003fff80fb 0xe3f7ff8007fff01f

def z734 : W := mkw 0xf02417bab6ff0000 0x1e0482f756dfe000 0xe02003ffffff8003 0xfc04007ffffff000

def z735 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x035cc318383c70fe 0xe06b986307078e1f

def z736 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x9fbffc173fff8003 0xf3f7ff82e7fff000

def z737 : W := mkw 0x8e0403ff8900fcf6 0x11c0807ff1201f9e 0xe04003ffc0007cfc 0x1c08007ff8000f9f

def z738 : W := mkw 0x2b0014414357292b 0x05600288286ae525 0x0363fffbc7fc7378 0xc06c7fff78ff8e6f

def z739 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b3f70733ffe7 0x7fbc567ee0e67ffc

def z740 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67bf03e03fc01f01 0x8cf7e07c07f803e0

def z741 : W := mkw 0x2a00104103122822 0x0540020820624504 0x0162b2d30733e063 0x602c565a60e67c0c

def z742 : W := mkw 0x841febba80000050 0xf083fd775000000a 0xff9fffffc00000f8 0x1ff3fffff800001f

def z743 : W := mkw 0xc808e85aad807a00 0x79011d0b55b00f40 0x9860fc1fffc07f05 0xf30c1f83fff80fe0

def z744 : W := mkw 0x48172be2ad807a00 0xa902e57c55b00f40 0x67ff33e33fc07f05 0xecffe67c67f80fe0

def z745 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xe31fffffc0000000 0x1c63fffff8000000

def z746 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xbfbffd083fff8003 0xf7f7ffa107fff000

def z747 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x037f03e03fc07f05 0xe06fe07c07f80fe0

def z748 : W := mkw 0xc01febbaac805200 0xf803fd7755900a40 0xff9ffffff8c01f05 0xbff3ffffff1803e0

def z749 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x193efc003fff8003 0xe327df8007fff000

def z750 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1e3ffc003fff8003 0x83c7ff8007fff000

def z751 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xffe3b3ffc7f3ffff 0xfffc767ff8fe7fff

def z752 : W := mkw 0x001be8a280000000 0xe0037d1450000000 0x551fbce7c0000000 0x0aa3f79cf8000000

def z753 : W := mkw 0x840cebba98285050 0x70819d7753050a0a 0xfbdcfffff83c70fe 0xff7b9fffff078e1f

def z754 : W := mkw 0x2000100002120000 0x0400020000424000 0x1fbeb0003f338003 0xe3f7d60007e67000

def z755 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xa9e2b2d30733ece7 0x753c565a60e67d9c

def z756 : W := mkw 0x2008d000123a0000 0x44011a0002474000 0x0bbcc0003f3f8003 0xe177980007e7f000

def z757 : W := mkw 0x4a1703e12d807a22 0x8942e07c25b00f44 0x67ff03f33fc07f65 0xecffe07e67f80fec

def z758 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xf562b2d70733ece5 0x5eac565ae0e67d9c

def z759 : W := mkw 0x401703002c805000 0x8802e06005900a00 0x67ff03203fc07f05 0xecffe06407f80fe0

def z760 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xe2014d2cc0cf9f9f 0xbc4029a59819f3f3

def z761 : W := mkw 0x80042bba80000000 0x3000857750000000 0xf0003fffc0000000 0x1e0007fff8000000

def z762 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xbfffff183ffff0ff 0xf7ffffe307fffe1f

def z763 : W := mkw 0x800cc31800000000 0x5001986300000000 0xff9fffffc0000000 0x1ff3fffff8000000

def z764 : W := mkw 0x001328a280000000 0xa002651450000000 0xdc037cefc0000000 0x1b806f9df8000000

def z765 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa35cc318383c70fc 0xd46b986307078e1f

def z766 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xaa814d28c0cf9f9f 0xb55029a51819f3f3

def z767 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xefddc338383c70fe 0xfdfbb86707078e1f

def z768 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x0162b2d30733ec61 0x402c565a60e67d8c

def z769 : W := mkw 0x4013040024c50000 0x880260800498a000 0x07bf00003fcf8003 0xe0f7e00007f9f000

def z770 : W := mkw 0x382cffe01b7f7a00 0x67059ffc036fef40 0x7840ffe0003fff06 0x0f081ffc0007ffe0

def z771 : W := mkw 0xf4373f182ed75050 0xbe86e7e305daea0a 0xb4633f1807c3f0fd 0x168c67e300f87e1f

def z772 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfc62b2d70733ece7 0x1f8c565ae0e67d9c

def z773 : W := mkw 0x8408c01818285050 0x5081180303050a0a 0x8bdcc018383c70fe 0xf17b980307078e1f

def z774 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0c01300 0x9ff3fffff8180260

def z775 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde3b2f707f3efe7 0x7fbc765ee0fe7dfc

def z776 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x07ff01203fc07f05 0xe0ffe02407f80fe0

def z777 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x5fbffcc73fff8003 0xebf7ff98e7fff000

def z778 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x9962b2d70733ece7 0x732c565ae0e67d9c

def z779 : W := mkw 0x0404030018285050 0x0080806003050a0a 0xabdc4308383c70fe 0xf57b886107078e1f

def z780 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x9f9ffedfc0000000 0x13f3ffdbf8000000

def z781 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x66bf01e03fc01f05 0xacd7e03c07f803e0

def z782 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x153fbc003fff8003 0xe2a7f78007fff000

def z783 : W := mkw 0x7028d40036ff0000 0x4e051a8006dfe000 0x1fbef0003fff8003 0xe3f7de0007fff000

def z784 : W := mkw 0x7b20144577ffadaf 0x0f640288aefff5b5 0x006000003fffffff 0xe00c000007ffffff

def z785 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffed33fff8003 0xe3f7ffda67fff000

def z786 : W := mkw 0x4013040024c50000 0x880260800498a000 0x17bf0c003fc38001 0xe2f7e18007f87000

def z787 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x013eb0003f338003 0x6027d60007e67000

def z788 : W := mkw 0x0a0403e50900fea6 0x0140807ca1201fd4 0x604003e700007f04 0x0c08007ce0000fe0

def z789 : W := mkw 0x840ceb1a98285050 0x70819d6353050a0a 0xabdcf31b383c70fe 0xf57b9e6367078e1f

def z790 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x143f3c003fc38001 0x0287e78007f87000

def z791 : W := mkw 0x401703a024800000 0x8802e07404900000 0x67bf03e03fc01f05 0xecf7e07c07f803e0

def z792 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xffc14f2cc0cfff9f 0xfff829e59819fff3

def z793 : W := mkw 0x8a0403ff8900fea6 0x1140807ff1201fd4 0xe04003ffc0007fe4 0x1c08007ff8000ffc

def z794 : W := mkw 0x8d0403fc4900ffdd 0x11a0807f89201ffb 0xe04003fcc0007ffc 0x1c08007f98000fff

def z795 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x17bf7c003fcf8001 0xe2f7ef8007f9f000

def z796 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xfde2b2dfc733ecff 0x7fbc565bf8e67d9f

def z797 : W := mkw 0x840ceb1a98285050 0x70819d6353050a0a 0xffdeffdff83c70fe 0xfffbdffbff078e1f

def z798 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1d3ffc003fff8003 0x43a7ff8007fff000

def z799 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xffff03e43fc07f05 0xffffe07c87f80fe0

def z800 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1ffffc003fffe0e7 0xe3ffff8007fffc1c

def z801 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa95cc318383c70fe 0x552b986307078e1f

def z802 : W := mkw 0x041328a298285050 0xa082651453050a0a 0x54433ce7f83c70fe 0xea88679cff078e1f

def z803 : W := mkw 0x713bf80476ba858d 0xee277f008ed750b1 0xe13eb12cff301f9c 0x5c27d6259fe603f3

def z804 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0x1fbffc003fff931b 0xe3f7ff8007fff263

def z805 : W := mkw 0xf43bfc1836ff0050 0xfe877f8306dfe00a 0x1fbffc103fff8063 0xe3f7ff8207fff00c

def z806 : W := mkw 0x001328a280000000 0xa002651450000000 0x5e837ce7c0000000 0x0bd06f9cf8000000

def z807 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xbbdccf1cf83c70fe 0xf77b99e39f078e1f

def z808 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xffc3ffffc0ffffff 0xfff87ffff81fffff

def z809 : W := mkw 0xd43fefbabced5050 0xfa87fdf7579daa0a 0x021d4d28f8cc1018 0x8043a9a51f198203

def z810 : W := mkw 0x0404030018285050 0x0080806003050a0a 0x015c0200383c70fe 0xe02b804007078e1f

def z811 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x153f3c003fc38001 0x42a7e78007f87000

def z812 : W := mkw 0xf03bfc1ab6ff0000 0xfe077f8356dfe000 0xffbffedfffff8003 0xfff7ffdbfffff000

def z813 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffd28ffff8003 0xe3f7ffa51ffff000

def z814 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0x9902fedfc0000000 0x13205fdbf8000000

def z815 : W := mkw 0x481300402d807a00 0x8902600805b00f40 0x017e00003fc07f05 0xe02fc00007f80fe0

def z816 : W := mkw 0x480403402d807a00 0x0900806805b00f40 0x67fe03c03fc07f05 0xecffc07807f80fe0

def z817 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfa1dffffc0000000 0x1f43bffff8000000

def z818 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe814fffc0cf9f9f 0xbfd029fff819f3f3

def z819 : W := mkw 0x4813004025802a00 0x8902600804b00540 0x07bf00003fc00f01 0xe0f7e00007f801e0

def z820 : W := mkw 0x481300402d807a00 0x8902600805b00f40 0x67ff01203fc07f05 0xecffe02407f80fe0

def z821 : W := mkw 0x4013000024800000 0x8802600004900000 0x47bf00203fc00f01 0xe8f7e00407f801e0

def z822 : W := mkw 0x0404030018285050 0x0080806003050a0a 0x025c0100383c70fe 0xe04b802007078e1f

def z823 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfec14f3cc0cfffff 0xbfd829e79819ffff

def z824 : W := mkw 0xaa1ffbff8312aca6 0xf543ff7ff0625594 0x027d4d28c733ece7 0x604fa9a518e67d9c

def z825 : W := mkw 0x4013000024800000 0x8802600004900000 0x1fbf00003fc38003 0xe3f7e00007f87000

def z826 : W := mkw 0x480403402d807a00 0x0900806805b00f40 0x017c02003fc07f05 0xe02f804007f80fe0

def z827 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b2d70733e0e2 0x5fbc565ae0e67c1c

def z828 : W := mkw 0xc01febbaa4800200 0xf803fd7754900040 0xff9fffffc0c00300 0x1ff3fffff8180060

def z829 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1ebd4c003fff8003 0xe3d7a98007fff000

def z830 : W := mkw 0xc01febbaac805200 0xf803fd7755900a40 0xff9ffffff8000000 0x1ff3ffffff000000

def z831 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffc003fcf8001 0x83f7ff8007f9f000

def z832 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0xdf9ffcffc0000000 0x1bf3ff9ff8000000

def z833 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x23fd03203fc07f05 0xe47fa06407f80fe0

def z834 : W := mkw 0x411300046480858d 0x882260008c9010b1 0xe7bf012cffc01f9d 0xfcf7e0259ff803f3

def z835 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b3ffc733ece7 0x7fbc567ff8e67d9c

def z836 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xffffffffffc07f05 0xfffffffffff80fe0

def z837 : W := mkw 0xcc1bc0f835a82a50 0xd983781f06b5054a 0xcc23c0f807fc0ffb 0x1984781f00ff81ff

def z838 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xffdffffff83c70fe 0xfffbffffff078e1f

def z839 : W := mkw 0x2a00104103122822 0x0540020820624504 0x7de2b2d30733ec67 0x6fbc565a60e67d8c

def z840 : W := mkw 0xb528fc1c527f85dd 0x76a51f838a4ff0bb 0x9800fc1cc03f80fa 0x13001f839807f01f

def z841 : W := mkw 0x800cebba80000000 0x70019d7750000000 0x9800fedfc0000000 0x13001fdbf8000000

def z842 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x0bbdcc003fff8003 0xe177b98007fff000

def z843 : W := mkw 0x801be81a80000000 0xf0037d0350000000 0xff9ffedfc0000000 0x1ff3ffdbf8000000

def z844 : W := mkw 0x481300402d807a00 0x8902600805b00f40 0x027d00003fc07f05 0xe04fa00007f80fe0

def z845 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xffdfffffc0007004 0x1ffbfffff8000e00

def z846 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x67bf01e03fc01f05 0xecf7e03c07f803e0

def z847 : W := mkw 0xcc1703f82d807a50 0x9982e07f05b00f4a 0x67ff03e83fc07f1d 0xecffe07d07f80fe3

def z848 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x111ebed7c0000000 0x0223d7daf8000000

def z849 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x8b5cc318383c70fa 0xd16b986307078e1f

def z850 : W := mkw 0x7028d40036ff0000 0x4e051a8006dfe000 0x013c80003fff8003 0xe027900007fff000

def z851 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0xff83ffffc0000000 0x1ff07ffff8000000

def z852 : W := mkw 0x0000000000000000 0x0000000000000000 0x54033ce7c0000000 0x0a80679cf8000000

def z853 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xefff43e83fc07f05 0xfdffe87d07f80fe0

def z854 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1dbefc003f3f8003 0x63b7df8007e7f000

def z855 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff83070fc 0x5ffbffffff060e1f

def z856 : W := mkw 0x00172ba288005000 0xa002e57451000a00 0x77df3fe7f8007004 0xeefbe7fcff000e00

def z857 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffd203fff9303 0xe3f7ffa407fff260

def z858 : W := mkw 0xc01febbab4a80000 0xf803fd7756950000 0xffbffffffffc0003 0xfff7ffffffff8000

def z859 : W := mkw 0x800403ba80000000 0x1000807750000000 0xff83ffffc0000000 0x1ff07ffff8000000

def z860 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd83bef7c0000000 0x1fb077def8000000

def z861 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xffdffffff80c709e 0xfffbffffff018e13

def z862 : W := mkw 0xc41febbabca85250 0xf883fd7757950a4a 0xffdffffff8fc73fe 0xfffbffffff1f8e7f

def z863 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xffdfffffc0306060 0x5ffbfffff8060c0c

def z864 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc03000e2 0x1ff3fffff806001c

def z865 : W := mkw 0x001328a280000000 0xa002651450000000 0xfdc3bef7c03060e6 0x7fb877def8060c1c

def z866 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x8a5cc118383c70fe 0xf14b982307078e1f

def z867 : W := mkw 0x2f0014455b7ffdff 0x05e00288ab6fffbf 0x006000003fffffff 0xe00c000007ffffff

def z868 : W := mkw 0x841febba90280050 0xf083fd775205000a 0xff9fffffc03c10fe 0xbff3fffff807821f

def z869 : W := mkw 0x6b0014456fd7ffaf 0x0d600288adfafff5 0x006000003fffffff 0xe00c000007ffffff

def z870 : W := mkw 0x001328a280000000 0xa002651450000000 0x54033ce7c0c00f01 0x0a80679cf81801e0

def z871 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x113ebc003f338000 0x4227d78007e67000

def z872 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b2d7073ffcff 0xffbc565ae0e7ff9f

def z873 : W := mkw 0x2a00104103122822 0x0540020820624504 0xbde2b2d30733e0e7 0x77bc565a60e67c1c

def z874 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfa014d2cc0cf9f9e 0x9f4029a59819f3f3

def z875 : W := mkw 0xc01febbaac805000 0xf803fd7755900a00 0xffffffffffc07005 0xfffffffffff80e00

def z876 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x5fbffc24ffff8003 0xebf7ff849ffff000

def z877 : W := mkw 0x480000402d807a00 0x0900000805b00f40 0x03fc00003fc07f05 0xe07f800007f80fe0

def z878 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x77ff33e73fc07f05 0xeeffe67ce7f80fe0

def z879 : W := mkw 0x841febba88005050 0xf083fd7751000a0a 0xffdfffffc03070fe 0x7ffbfffff8060e1f

def z880 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x1fbfb0003ff38003 0xe3f7f60007fe7000

def z881 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x6fff43e03fcc7f07 0xedffe87c07f98fe0

def z882 : W := mkw 0x080407e009457a00 0x010080fc0128af40 0x7ec14fe000cfff07 0xafd829fc0019ffe0

def z883 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe814d2cc0cf9f19 0x9fd029a59819f3e3

def z884 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x9fbffc083fff809b 0xf3f7ff8107fff013

def z885 : W := mkw 0x800cebba80000000 0x70019d7750000000 0xfe81ffffc0000000 0x1fd03ffff8000000

def z886 : W := mkw 0x0400000018285050 0x0080000003050a0a 0x03dc0000383c70fe 0xe07b800007078e1f

def z887 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3ffffc73ffcff 0xfffc7ffff8e7ff9f

def z888 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff43e83fcc7f1d 0xecffe87d07f98fe3

def z889 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1a3dfc003fff8003 0xe347bf8007fff000

def z890 : W := mkw 0x0004030008005000 0x0000806001000a00 0xabdcc318383c70fe 0xf57b986307078e1f

def z891 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x779fbff7c0000000 0x0ef3f7fef8000000

def z892 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff80c701c 0xfffbffffff018e03

def z893 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x457f02e03fc07f05 0xe8afe05c07f80fe0

def z894 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xffffb3f73ff07fe7 0xfffff67ee7fe0ffc

def z895 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x1fbf7c003fcf8003 0xe3f7ef8007f9f000

def z896 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x443f00e03fc00f01 0x0887e01c07f801e0

def z897 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfec14d2cc0ffffff 0xffd829a5981fffff

def z898 : W := mkw 0x2000100002120000 0x0400020000424000 0xfde2b2d70733e0e7 0x7fbc565ae0e67c1c

def z899 : W := mkw 0x7b333c4567d7adaf 0xaf666788acfaf5b5 0x54233ce7c7c38f01 0x0a84679cf8f871e0

def z900 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x657f03e03fc07f05 0x4cafe07c07f80fe0

def z901 : W := mkw 0xc01febbaa4800000 0xf803fd7754900000 0xffbfffffffc01f05 0xfff7fffffff803e0

def z902 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe837defc0cf9f9f 0xbfd06fbdf819f3f3

def z903 : W := mkw 0x001328a280000000 0xa002651450000000 0x10023cc7c0000000 0x02004798f8000000

def z904 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x7fff4fe03fc07f05 0xefffe9fc07f80fe0

def z905 : W := mkw 0xc81703f82d807a00 0x9902e07f05b00f40 0xe7ff03f83fc07f05 0xfcffe07f07f80fe0

def z906 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbffd2cffff9f07 0xfff7ffa59ffff3e0

def z907 : W := mkw 0x001be8a280000000 0xe0037d1450000000 0x561f7ce7c0000000 0x0ac3ef9cf8000000

def z908 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xffff4fecffcc7f9f 0xffffe9fd9ff98ff3

def z909 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3b3f70733ece7 0x7ffc767ee0e67d9c

def z910 : W := mkw 0x8008e8ba80000000 0x70011d1750000000 0xd800fcffc0000000 0x1b001f9ff8000000

def z911 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x5f9ffdefc0000000 0x0bf3ffbdf8000000

def z912 : W := mkw 0x0408c00018285050 0x4081180003050a0a 0xabdcc108383c70fe 0xf57b982107078e1f

def z913 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0x7fbffd28ffff9f1f 0xeff7ffa51ffff3e3

def z914 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabddcf38f83c70fe 0xf57bb9e71f078e1f

def z915 : W := mkw 0x703bfca2b6ff0000 0xee077f9456dfe000 0xffbffdefffff8003 0xfff7ffbdfffff000

def z916 : W := mkw 0x401328a2a4800000 0xa802651454900000 0x54233ce7c7c00001 0x0a84679cf8f80000

def z917 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa9dcc218383c60fe 0x753b984307078c1f

def z918 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0x995efedff83c60fa 0x532bdfdbff078c1f

def z919 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0xf800fedfc0000000 0x1f001fdbf8000000

def z920 : W := mkw 0x4813004025802800 0x8902600804b00500 0x67ff03e03fc07f05 0xecffe07c07f80fe0

def z921 : W := mkw 0x703bfca036ff0000 0xee077f9406dfe000 0x5fbffce03fff8003 0xebf7ff9c07fff000

def z922 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x67ff02e03fc06f05 0xecffe05c07f80de0

def z923 : W := mkw 0x001be8a280000000 0xe0037d1450000000 0xff9ffdefc0000000 0x1ff3ffbdf8000000

def z924 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xff9ffffff83c10fa 0x9ff3ffffff07821f

def z925 : W := mkw 0xc01febbaac805200 0xf803fd7755900a40 0xffbfffffffc01301 0xfff7fffffff80260

def z926 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x0bdcc108383c70fe 0xe17b982107078e1f

def z927 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x541f3ce7c0000000 0x0a83e79cf8000000

def z928 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff83c6062 0xfffbffffff078c0c

def z929 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde3bef7c733ece7 0x7fbc77def8e67d9c

def z930 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x56014d2cc0cf9f9f 0xaac029a59819f3f3

def z931 : W := mkw 0x703bfc02b6ff0000 0xee077f8056dfe000 0x1fbffc07ffff8003 0xe3f7ff80fffff000

def z932 : W := mkw 0x481703402d807a00 0x8902e06805b00f40 0x27ff03003fc07f05 0xe4ffe06007f80fe0

def z933 : W := mkw 0x3128fc04527f858d 0x66251f808a4ff0b1 0x1800fc04c03f8002 0x03001f809807f000

def z934 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xff81cf3cc0cf9f9f 0xbff039e79819f3f3

def z935 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfffeb2d73f33ece7 0xffffd65ae7e67d9c

def z936 : W := mkw 0x001be8a290280000 0xe0037d1452050000 0x5f9ffce7f83c0002 0xebf3ff9cff078000

def z937 : W := mkw 0x70333c0036ff0000 0xae06678006dfe000 0x17bf3c003fff8003 0xe2f7e78007fff000

def z938 : W := mkw 0xf43bfc1836ff0050 0xfe877f8306dfe00a 0x1fbffc083fff801b 0xe3f7ff8107fff003

def z939 : W := mkw 0x7033140036ff0000 0x8e06628006dfe000 0x1fbf4c003fff8003 0xe3f7e98007fff000

def z940 : W := mkw 0x481300e02d807a00 0x8902601c05b00f40 0x47ff00e03fc07f05 0xe8ffe01c07f80fe0

def z941 : W := mkw 0x601bf80026920000 0xec037f0004d24000 0x1fbffc003ff38003 0xe3f7ff8007fe7000

def z942 : W := mkw 0x801febba90280000 0xf003fd7752050000 0xff9fffffc03c0002 0x1ff3fffff8078000

def z943 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xe7ff03f03fc07fe5 0xfcffe07e07f80ffc

def z944 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xe7ff03ecffc07f05 0xfcffe07d9ff80fe0

def z945 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x007c00003fc07f05 0xe00f800007f80fe0

def z946 : W := mkw 0x0408c00018285050 0x4081180003050a0a 0x015c8000383c70fe 0xe02b900007078e1f

def z947 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffd083fff901b 0xe3f7ffa107fff203

def z948 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b3df0733fcff 0x7fbc567be0e67f9f

def z949 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xffa34d2cc7cf9f9f 0xfff469a598f9f3f3

def z950 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0x54037cefc0000000 0x0a806f9df8000000

def z951 : W := mkw 0x6b1314e567d7afaf 0x8d62629cacfaf5f5 0x54233ce7c7c38f01 0x0a84679cf8f871e0

def z952 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0c00f01 0x1ff3fffff81801e0

def z953 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x66fd01203fc07f05 0xecdfa02407f80fe0

def z954 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe2f2d7073fece7 0xfffc5e5ae0e7fd9c

def z955 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xefff83f03fc07f05 0xfdfff07e07f80fe0

def z956 : W := mkw 0x0000000000000000 0x0000000000000000 0xfd82fedfc0000000 0x1fb05fdbf8000000

def z957 : W := mkw 0xf43bfc1836ff0050 0xfe877f8306dfe00a 0xbfbffd183fff90ff 0xf7f7ffa307fff21f

def z958 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x571fffffc0000000 0x0ae3fffff8000000

def z959 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xbfbffe103fff8003 0xf7f7ffc207fff000

def z960 : W := mkw 0x8e04035d0900fcf6 0x11c0806ba1201f9e 0xa040031800007cfc 0x1408006300000f9f

def z961 : W := mkw 0x841febba90280050 0xf083fd775205000a 0xff9ffffff83c00fa 0xfff3ffffff07801f

def z962 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xf962b2d70733ece6 0x5f2c565ae0e67d9c

def z963 : W := mkw 0x80172bba80000000 0xb002e57750000000 0x54033ef7c0000000 0x0a8067def8000000

def z964 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1ebf7c003fcf8003 0xa3d7ef8007f9f000

def z965 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xffdfffffc00060e4 0x1ffbfffff8000c1c

def z966 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x477f03e03fc07f01 0xc8efe07c07f80fe0

def z967 : W := mkw 0x2008d000123a0000 0x44011a0002474000 0x1dbeb0003f338003 0x63b7d60007e67000

def z968 : W := mkw 0x481300e025802a00 0x8902601c04b00540 0x453f00e03fc00f01 0x48a7e01c07f801e0

def z969 : W := mkw 0xf03bfcbab6ff0000 0xfe077f9756dfe000 0xdfbffcffffff8003 0xfbf7ff9ffffff000

def z970 : W := mkw 0x001328a280000000 0xa002651450000000 0x5503bef7c0000000 0x0aa077def8000000

def z971 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa15c8318383c70fe 0xf42b906307078e1f

def z972 : W := mkw 0x6013100026920000 0x8c02620004d24000 0x17bf30003fc38001 0xe2f7e60007f87000

def z973 : W := mkw 0x841febba90280050 0xf083fd775205000a 0xff9fffffc0300060 0x1ff3fffff806000c

def z974 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x153eb0003f338001 0x42a7d60007e67000

def z975 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x5562b2d70733ece7 0x6aac565ae0e67d9c

def z976 : W := mkw 0x401bc40034ed0000 0xc8037880069da000 0x1fbfcc003fff8003 0xe3f7f98007fff000

def z977 : W := mkw 0x2a00104103122822 0x0540020820624504 0xfde2b2d70733e063 0x7fbc565ae0e67c0c

def z978 : W := mkw 0x03000405404585af 0x00600080a808b0b5 0xfe814d3fc0cf9fff 0xbfd029a7f819f3ff

def z979 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x013eb0003ff38001 0x4027d60007fe7000

def z980 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xffbfffffc7000001 0x7ff7fffff8e00000

def z981 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbffd2cffff909f 0xfff7ffa59ffff213

def z982 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1b3ffc003fff8002 0xc367ff8007fff000

def z983 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x617e03e03fc07f05 0xec2fc07c07f80fe0

def z984 : W := mkw 0x00172ba280000000 0xa002e57450000000 0x74033fe7c0000000 0x0e8067fcf8000000

def z985 : W := mkw 0x001be8a280000000 0xe0037d1450000000 0x5c03fce7c0000000 0x0b807f9cf8000000

def z986 : W := mkw 0x3328fc05527f85af 0x66651f80aa4ff0b5 0x9800fc1fc03f80fa 0x13001f83f807f01f

def z987 : W := mkw 0x00172ba280000000 0xa002e57450000000 0x551f3ee7c0000000 0x0aa3e7dcf8000000

def z988 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x033ffc003fff8003 0xe067ff8007fff000

def z989 : W := mkw 0xf03bfc1ab6ff0000 0xfe077f8356dfe000 0xffbffd3fffff8003 0xfff7ffa7fffff000

def z990 : W := mkw 0x001328a280000000 0xa002651450000000 0xdc03bcf7c0000000 0x1b80779ef8000000

def z991 : W := mkw 0xf03bfc1836ff0000 0xfe077f8306dfe000 0x9fbffc183fff8003 0xf3f7ff8307fff000

def z992 : W := mkw 0x090403e44900ff8d 0x0120807c89201ff1 0x604003e4c0007f04 0x0c08007c98000fe0

def z993 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x77ff0fe4ffc07f05 0xeeffe1fc9ff80fe0

def z994 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x66814d28c0cf9f9f 0xacd029a51819f3f3

def z995 : W := mkw 0x801febba88005200 0xf003fd7751000a40 0xff9fffffc0001300 0x1ff3fffff8000260

def z996 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x1e814d28c0cf9f9f 0xa3d029a51819f3f3

def z997 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdfffffc03c70fe 0x1ffbfffff8078e1f

def z998 : W := mkw 0x48172be2ad807a00 0xa902e57c55b00f40 0xffff7fefffc07f05 0xffffeffdfff80fe0

def z999 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xff81cd2cc0ff9f9f 0xfff039a5981ff3f3

def z1000 : W := mkw 0x401328a2a4800000 0xa802651454900000 0x57bf3ce7ffc00001 0xeaf7e79cfff80000

def z1001 : W := mkw 0x2a00104103122822 0x0540020820624504 0x1562b2d30733e061 0x42ac565a60e67c0c

def z1002 : W := mkw 0x723bfc0136ff0022 0xee477f8026dfe004 0x1fbffc133fff8063 0xe3f7ff8267fff00c

def z1003 : W := mkw 0x001be8a280000000 0xe0037d1450000000 0xff9ffef7c0000000 0x1ff3ffdef8000000

def z1004 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x023d01203fc01f01 0x8047a02407f803e0

def z1005 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x003c00003fff8003 0xe007800007fff000

def z1006 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfc03ffffc0000000 0x1f807ffff8000000

def z1007 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x467f01e03fc07f05 0xe8cfe03c07f80fe0

def z1008 : W := mkw 0x840ceb1a98285050 0x70819d6353050a0a 0xffddff3ff83c70fe 0xfffbbfe7ff078e1f

def z1009 : W := mkw 0x7033140036ff0000 0x8e06628006dfe000 0x013e00003fff8003 0xe027c00007fff000

def z1010 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0300002 0x7ff3fffff8060000

def z1011 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x627d03e03fc07f05 0xec4fa07c07f80fe0

def z1012 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa9dc8210383c70fe 0xf53b904207078e1f

def z1013 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x65e2b2d30733ece7 0x6cbc565a60e67d9c

def z1014 : W := mkw 0x840cc3ba98285050 0x5081987753050a0a 0xffdef3fff83c70fe 0xfffbde7fff078e1f

def z1015 : W := mkw 0x48172be02d807a00 0xa902e57c05b00f40 0x77ff3fe03fc07f05 0xeeffe7fc07f80fe0

def z1016 : W := mkw 0x703bfc0026d70000 0xee077f8004dae000 0x1fbffc003fc38001 0xe3f7ff8007f87000

def z1017 : W := mkw 0x841febba90280050 0xf083fd775205000a 0xffdfffffc03c60fe 0x7ffbfffff8078c1f

def z1018 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x005c0000383c70fe 0xe00b800007078e1f

def z1019 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x07bf4c003fff8003 0xe0f7e98007fff000

def z1020 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1dbeb0003fff8003 0xe3b7d60007fff000

def z1021 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe2f3df0733ece7 0x7ffc5e7be0e67d9c

def z1022 : W := mkw 0x001328a280000000 0xa002651450000000 0x75833ee7c0000000 0x0eb067dcf8000000

def z1023 : W := mkw 0x8408c01810280050 0x508118030205000a 0xabdcc218383c60fe 0xf57b984307078c1f

def z1024 : W := mkw 0x3028fc00127f0000 0x66051f80024fe000 0x1fbefc003f3f8003 0xe3f7df8007e7f000

def z1025 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ffb3f33fc07f05 0xecfff67e67f80fe0

def z1026 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe837defc0000000 0x1fd06fbdf8000000

def z1027 : W := mkw 0x6013100026920000 0x8c02620004d24000 0x1dbeb0003f338003 0x63b7d60007e67000

def z1028 : W := mkw 0x80172bba80000000 0xb002e57750000000 0xfd83bfffc0000000 0x1fb077fff8000000

def z1029 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbffc043fff8003 0xfff7ff8087fff000

def z1030 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xbfddcf18383c70fe 0xf7fbb9e307078e1f

def z1031 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfe81cd3cc0ff9fff 0xbfd039a7981ff3ff

def z1032 : W := mkw 0x8e04035d0900fcf6 0x11c0806ba1201f9e 0xe04002d700006ce4 0x1c08005ae0000d9c

def z1033 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xbfbffc003fff8087 0xf7f7ff8007fff010

def z1034 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1bbefc003f3f8002 0xe377df8007e7f000

def z1035 : W := mkw 0x601bd00036ba0000 0xcc037a0006d74000 0x1fbff0003fff8003 0xe3f7fe0007fff000

def z1036 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xff9ffffff8001000 0x9ff3ffffff000200

def z1037 : W := mkw 0xc81703faad807a00 0x9902e07f55b00f40 0xffffb3ffffc07f05 0xfffff67ffff80fe0

def z1038 : W := mkw 0x7028fc0036ff0000 0x6e051f8006dfe000 0x1bbcfc003fff8003 0xe3779f8007fff000

def z1039 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff4fe8ffc07f05 0xecffe9fd1ff80fe0

def z1040 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xf51fbfffc0000000 0x1ea3f7fff8000000

def z1041 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x07ff02c03fc07f05 0xe0ffe05807f80fe0

def z1042 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0c00001 0xbff3fffff8180000

def z1043 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2fedfc733ece7 0x7fbc5fdbf8e67d9c

def z1044 : W := mkw 0x001328a280000000 0xa002651450000000 0xfc833ce7c0000000 0x1f90679cf8000000

def z1045 : W := mkw 0x001328a280000000 0xa002651450000000 0x56037defc0000000 0x0ac06fbdf8000000

def z1046 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc00c0002 0xbff3fffff8018000

def z1047 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x779f7fefc0000000 0x0ef3effdf8000000

def z1048 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0001f04 0x1ff3fffff80003e0

def z1049 : W := mkw 0x801febba90280000 0xf003fd7752050000 0xff9ffffff83c109e 0xfff3ffffff078213

def z1050 : W := mkw 0x0000000000000000 0x0000000000000000 0xffc3ffffc03c70fe 0xfff87ffff8078e1f

def z1051 : W := mkw 0x001328a280000000 0xa002651450000000 0xff83ffffc0000000 0x1ff07ffff8000000

def z1052 : W := mkw 0x090403e44900ff8d 0x0120807c89201ff1 0x604003e000007f9c 0x0c08007c00000ff3

def z1053 : W := mkw 0x201bf800123a0000 0xe4037f0002474000 0x1fbffc003f3f8003 0xe3f7ff8007e7f000

def z1054 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x8bdcc218383c60fa 0xf17b984307078c1f

def z1055 : W := mkw 0x840ceb1a98285050 0x70819d6353050a0a 0xabdccf18f83c70fe 0xf57b99e31f078e1f

def z1056 : W := mkw 0x84172bba88005050 0xb082e57751000a0a 0xf4433fffc00070fc 0x1e8867fff8000e1f

def z1057 : W := mkw 0x841febba88005050 0xf083fd7751000a0a 0xffdffffff80070fc 0xfffbffffff000e1f

def z1058 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x015c8210383c60fa 0x402b904207078c1f

def z1059 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x17bfbc003ff38001 0xe2f7f78007fe7000

def z1060 : W := mkw 0x7028d40036ff0000 0x4e051a8006dfe000 0x1fbdcc003fff8003 0xe3f7b98007fff000

def z1061 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x75e2b2d70733ec65 0x6ebc565ae0e67d8c

def z1062 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xffdffffff83070e6 0xfffbffffff060e1c

def z1063 : W := mkw 0x481703e025802a00 0x8902e07c04b00540 0x67bf03e03fc00f01 0xecf7e07c07f801e0

def z1064 : W := mkw 0x00172ba280000000 0xa002e57450000000 0xff9f7fefc0000000 0x1ff3effdf8000000

def z1065 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff83f03ff07f65 0xecfff07e07fe0fec

def z1066 : W := mkw 0x48172be2ad807a00 0xa902e57c55b00f40 0xffffbff7ffc07f05 0xfffff7fefff80fe0

def z1067 : W := mkw 0x001703a000000000 0x8002e07400000000 0xff9fffffc0000000 0x1ff3fffff8000000

def z1068 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b2d707f3ffe7 0xffbc565ae0fe7ffc

def z1069 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x017e02c03fc06f01 0x402fc05807f80de0

def z1070 : W := mkw 0x0008c00010280000 0x4001180002050000 0xabdcc318383c70fe 0xf57b986307078e1f

def z1071 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x5fbffc203fff8f03 0xebf7ff8407fff1e0

def z1072 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffc003ff38001 0x43f7ff8007fe7000

def z1073 : W := mkw 0xc81703faad807a00 0x9902e07f55b00f40 0x67ff03e8ffc07f05 0xecffe07d1ff80fe0

def z1074 : W := mkw 0xc41febbabca85250 0xf883fd7757950a4a 0xff9ffffff8cc1318 0x9ff3ffffff198263

def z1075 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffc003fff9f07 0xe3f7ff8007fff3e0

def z1076 : W := mkw 0xc01febbaa4800000 0xf803fd7754900000 0xffbfffffff000000 0x5ff7ffffffe00000

def z1077 : W := mkw 0x0804034009007800 0x0100806801200f00 0x67ff03e03fc07f05 0xecffe07c07f80fe0

def z1078 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xdd62b2d70733ece3 0x5bac565ae0e67d9c

def z1079 : W := mkw 0xcc1703faad807a50 0x9982e07f55b00f4a 0xe7ff03ffffc07ffd 0xfcffe07ffff80fff

def z1080 : W := mkw 0x840ceb1818285050 0x70819d6303050a0a 0xbbdcff18383c70fe 0xf77b9fe307078e1f

def z1081 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x7fbffec03fff8003 0xeff7ffd807fff000

def z1082 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x47bf01e03fc01f01 0xe8f7e03c07f803e0

def z1083 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffc003f3f8002 0x43f7ff8007e7f000

def z1084 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xbbdeffdff83c70fe 0xf77bdffbff078e1f

def z1085 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xf6014d2cc0cf9f9d 0x9ec029a59819f3f3

def z1086 : W := mkw 0x5a3bec4535edaca6 0xeb477d88a6bdb594 0xe25d4ed738cc6ce4 0x9c4ba9dae7198d9c

def z1087 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3ffffc7f3ffe7 0xfffc7ffff8fe7ffc

def z1088 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xffdffffff8006000 0x5ffbffffff000c00

def z1089 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2b2d70733ec61 0x5fbc565ae0e67d8c

def z1090 : W := mkw 0x481300402d807a00 0x8902600805b00f40 0x67ff02c03fc07f05 0xecffe05807f80fe0

def z1091 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xfffffed73fffe0e7 0xffffffdae7fffc1c

def z1092 : W := mkw 0x800cebba80000000 0x70019d7750000000 0xfb9cffffc0000000 0x1f739ffff8000000

def z1093 : W := mkw 0x480403402d807a00 0x0900806805b00f40 0x67fd03203fc07f05 0xecffa06407f80fe0

def z1094 : W := mkw 0x703bfca2b6ff0000 0xee077f9456dfe000 0x1fbffcc33fff8003 0xe3f7ff9867fff000

def z1095 : W := mkw 0x841be8ba90280050 0xf0837d175205000a 0xdc03fcffc03c00fa 0x1b807f9ff807801f

def z1096 : W := mkw 0x621713a52e92d6a6 0x8c42e274a5d25ad4 0x9a1db13738f393e2 0x9343b626e71e727c

def z1097 : W := mkw 0x841febba88005050 0xf083fd7751000a0a 0xff9fffffc0001018 0x1ff3fffff8000203

def z1098 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x02014d28c0cf9f19 0x804029a51819f3e3

def z1099 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0000086 0x3ff3fffff8000010

def z1100 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xebdcc3df383c70fe 0xfd7b987be7078e1f

def z1101 : W := mkw 0x7033140026d70000 0x8e06628004dae000 0x07bf00003fc38001 0xe0f7e00007f87000

def z1102 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3fed70733ece7 0x7ffc7fdae0e67d9c

def z1103 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0x9802fcdfc0000000 0x13005f9bf8000000

def z1104 : W := mkw 0x840cc3b818285050 0x5081987703050a0a 0xebdcc3f8383c70fe 0xfd7b987f07078e1f

def z1105 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0x00600000073fecff 0x600c000000e7fd9f

def z1106 : W := mkw 0x0a0403e50900fea6 0x0140807ca1201fd4 0xe04002d700006ce4 0x1c08005ae0000d9c

def z1107 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbffd283fff9f9f 0xfff7ffa507fff3f3

def z1108 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x3ffffe003fffe007 0xe7ffffc007fffc00

def z1109 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xebdcc33cf83c70fe 0xfd7b98679f078e1f

def z1110 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xaffec3183f3c70ff 0xf5ffd86307e78e1f

def z1111 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xffe2f3ffc73fffff 0xfffc5e7ff8e7ffff

def z1112 : W := mkw 0x703bfca2b6ff0000 0xee077f9456dfe000 0xffbffef7ffff8003 0xfff7ffdefffff000

def z1113 : W := mkw 0x8f04035d4900fdff 0x11e0806ba9201fbf 0xe04003ffc0007ffc 0x1c08007ff8000fff

def z1114 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x23fe03c03fc07f05 0xe47fc07807f80fe0

def z1115 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0x0060000007f3efe7 0x600c000000fe7dfc

def z1116 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff83060e6 0x7ffbffffff060c1c

def z1117 : W := mkw 0xf43bfc1836ff0050 0xfe877f8306dfe00a 0xbffffe183fffe0ff 0xf7ffffc307fffc1f

def z1118 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x1fbef0003f3f8003 0xe3f7de0007e7f000

def z1119 : W := mkw 0xc81703faad807a00 0x9902e07f55b00f40 0x67ff03f33fc07f05 0xecffe07e67f80fe0

def z1120 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0x561f7deff80c1018 0x8ac3efbdff018203

def z1121 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x23dc8310383c70fe 0xe47b906207078e1f

def z1122 : W := mkw 0x481703e2ad807a00 0x8902e07c55b00f40 0x67ff03e7ffc07f05 0xecffe07cfff80fe0

def z1123 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0001004 0xbff3fffff8000200

def z1124 : W := mkw 0x7033140036ff0000 0x8e06628006dfe000 0x023d00003fff8003 0xe047a00007fff000

def z1125 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0xfe83fdffc0000000 0x1fd07fbff8000000

def z1126 : W := mkw 0x001328a280000000 0xa002651450000000 0xfe837defc00c109e 0xbfd06fbdf8018213

def z1127 : W := mkw 0x0a0403e50900fea6 0x0140807ca1201fd4 0x604003e000007fe4 0x0c08007c00000ffc

def z1128 : W := mkw 0xc01febbaac805200 0xf803fd7755900a40 0xffdffffff8c07304 0xfffbffffff180e60

def z1129 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x013eb0003f3f8002 0x4027d60007e7f000

def z1130 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xefffc3f83ffc7fff 0xfdfff87f07ff8fff

def z1131 : W := mkw 0x001328a280000000 0xa002651450000000 0x76833de7c0000000 0x0ed067bcf8000000

def z1132 : W := mkw 0xf03bfc1ab6ff0000 0xfe077f8356dfe000 0x1fbffc08ffff8003 0xe3f7ff811ffff000

def z1133 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xff9ffffff80c109e 0xbff3ffffff018213

def z1134 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x1fbfbc003ff38003 0xe3f7f78007fe7000

def z1135 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabdcc31838fc7fff 0xf57b9863071f8fff

def z1136 : W := mkw 0x0000280280000000 0x2000050050000000 0x54023cc7c0000000 0x0a804798f8000000

def z1137 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff80c70fc 0x9ffbffffff018e1f

def z1138 : W := mkw 0x7028d40036ff0000 0x4e051a8006dfe000 0x023c40003fff8003 0xe047880007fff000

def z1139 : W := mkw 0x0000280280000000 0x2000050050000000 0xfd82bed7c0000000 0x1fb057daf8000000

def z1140 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xaa5cc318383c70fe 0x954b986307078e1f

def z1141 : W := mkw 0x840cc3ba98285050 0x5081987753050a0a 0xabdcc3db383c70fe 0xf57b987b67078e1f

def z1142 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xe162b2d70733ece7 0x7c2c565ae0e67d9c

def z1143 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xde014d2cc0cf9f9b 0x9bc029a59819f3f3

def z1144 : W := mkw 0x801328ba80000000 0xb002651750000000 0xd4033cffc0000000 0x1a80679ff8000000

def z1145 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x65ff02e03fc06f05 0x6cbfe05c07f80de0

def z1146 : W := mkw 0x840cebba98285050 0x70819d7753050a0a 0xf840ffffc03c70fe 0x1f081ffff8078e1f

def z1147 : W := mkw 0x503bec0034ed0000 0xea077d80069da000 0x1fbf4c003fcf8003 0xe3f7e98007f9f000

def z1148 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x7fbffd203fff8003 0xeff7ffa407fff000

def z1149 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xa25c4318383c70fe 0xf44b886307078e1f

def z1150 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfd9efedfc0000000 0x1fb3dfdbf8000000

def z1151 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabddc33838fc73fe 0xf57bb867071f8e7f

def z1152 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x65fe02c03fc07f05 0xecbfc05807f80fe0

def z1153 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x895cc218383c70fe 0xf12b984307078e1f

def z1154 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x3fbffd003fff9007 0xe7f7ffa007fff200

def z1155 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xfc014d2cc0cf9f9f 0x1f8029a59819f3f3

def z1156 : W := mkw 0x800cebba80000000 0x70019d7750000000 0xfd82ffffc0000000 0x1fb05ffff8000000

def z1157 : W := mkw 0x840cc3ba98285050 0x5081987753050a0a 0xabdcc338f83c70fe 0xf57b98671f078e1f

def z1158 : W := mkw 0x040cc30018285050 0x4081986003050a0a 0x2bdcc300383c70fe 0xe57b986007078e1f

def z1159 : W := mkw 0x2a00104103122822 0x0540020820624504 0x1962b2d30733e062 0x432c565a60e67c0c

def z1160 : W := mkw 0x4c1703e02d807a50 0x8982e07c05b00f4a 0x67ff03e03fc07ffd 0xecffe07c07f80fff

def z1161 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0x0020000007c38f01 0x0004000000f871e0

def z1162 : W := mkw 0x841febba88005050 0xf083fd7751000a0a 0xffdfffffc00c70fe 0xbffbfffff8018e1f

def z1163 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xffdfffffc0006004 0x7ffbfffff8000c00

def z1164 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x7fff03e03fc3ff07 0xefffe07c07f87fe0

def z1165 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0038003 0x3ff3fffff8007000

def z1166 : W := mkw 0x001be80000000000 0xe0037d0000000000 0xff9fffffc0000000 0x1ff3fffff8000000

def z1167 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabdef3db383c70fe 0xf57bde7b67078e1f

def z1168 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xde1ffdffc0000000 0x1bc3ffbff8000000

def z1169 : W := mkw 0x40172ba2ac805200 0xa802e57455900a40 0x561f3de7f8c01300 0x8ac3e7bcff180260

def z1170 : W := mkw 0x840cc3b818285250 0x5081987703050a4a 0xabdcc338383c73fe 0xf57b986707078e7f

def z1171 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xff9d4d2cf8cf9f9f 0xfff3a9a59f19f3f3

def z1172 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xb9e2b2d70733e0e6 0x773c565ae0e67c1c

def z1173 : W := mkw 0x801febba80000000 0xf003fd7750000000 0x5f9ffef7c0000000 0x0bf3ffdef8000000

def z1174 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe2b3d70733fce7 0xfffc567ae0e67f9c

def z1175 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0x0020000007cf9f9f 0xa004000000f9f3f3

def z1176 : W := mkw 0xd03febbab4a80000 0xfa07fd7756950000 0xff9ffffff8000000 0x1ff3ffffff000000

def z1177 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xbbdcf31f383c70fe 0xf77b9e63e7078e1f

def z1178 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xf91effffc0000000 0x1f23dffff8000000

def z1179 : W := mkw 0x890403fec900ff8d 0x1120807fd9201ff1 0xe04003ffc0007f9c 0x1c08007ff8000ff3

def z1180 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xe7ff03f73fc07f05 0xfcffe07ee7f80fe0

def z1181 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xafddc31838fc70ff 0xf5fbb863071f8e1f

def z1182 : W := mkw 0x0408c00018285050 0x4081180003050a0a 0xabdcc210383c70fe 0xf57b984207078e1f

def z1183 : W := mkw 0x3128fc04527f858d 0x66251f808a4ff0b1 0x1800fc00003f809a 0x03001f800007f013

def z1184 : W := mkw 0xf03bfc1ab6ff0000 0xfe077f8356dfe000 0x1fbffc133fff8003 0xe3f7ff8267fff000

def z1185 : W := mkw 0xc01febbaa4800000 0xf803fd7754900000 0xffbfffffc7c00001 0x1ff7fffff8f80000

def z1186 : W := mkw 0xc8172bfaad807a00 0xb902e57f55b00f40 0xf7ff3fffffc07f05 0xfeffe7fffff80fe0

def z1187 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xefff03e03fc07f87 0xfdffe07c07f80ff0

def z1188 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xefdec3d8383c70fe 0xfdfbd87b07078e1f

def z1189 : W := mkw 0x801febba98285000 0xf003fd7753050a00 0xffdffffff83c7006 0xfffbffffff078e00

def z1190 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0xe7ff03e83fc07f9d 0xfcffe07d07f80ff3

def z1191 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc00c009a 0x1ff3fffff8018013

def z1192 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1fbffc003fff909f 0xe3f7ff8007fff213

def z1193 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x47ff02e03fc06f01 0xe8ffe05c07f80de0

def z1194 : W := mkw 0x801febba88005000 0xf003fd7751000a00 0xffdffffff8c07f05 0xfffbffffff180fe0

def z1195 : W := mkw 0x841febba90280050 0xf083fd775205000a 0xff9fffffc00c0018 0x1ff3fffff8018003

def z1196 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xffdcc31c383c70fe 0xfffb986387078e1f

def z1197 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3b2d707f3ece7 0xfffc765ae0fe7d9c

def z1198 : W := mkw 0x0404030018285050 0x0080806003050a0a 0xabdc8310383c70fe 0xf57b906207078e1f

def z1199 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x23dc4308383c70fe 0xe47b886107078e1f

def z1200 : W := mkw 0xcc1703f82d807a50 0x9982e07f05b00f4a 0xefff83f83ff07fff 0xfdfff07f07fe0fff

def z1201 : W := mkw 0x001328a280000000 0xa002651450000000 0x579f3ce7c0000000 0x0af3e79cf8000000

def z1202 : W := mkw 0x80172bba80000000 0xb002e57750000000 0x54033defc0000000 0x0a8067bdf8000000

def z1203 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff03e03fc06f01 0x4cffe07c07f80de0

def z1204 : W := mkw 0xf43bfc1ab6ff0050 0xfe877f8356dfe00a 0x9fbffc1fffff80fb 0xf3f7ff83fffff01f

def z1205 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x173ffc003fff8001 0xc2e7ff8007fff000

def z1206 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xfde2b2f7c733efe7 0x7fbc565ef8e67dfc

def z1207 : W := mkw 0x8404031818285050 0x1080806303050a0a 0xa3dc0318383c70fe 0xf47b806307078e1f

def z1208 : W := mkw 0x703bd40036ff0000 0xce077a8006dfe000 0x0fbfc0003fff8003 0xe1f7f80007fff000

def z1209 : W := mkw 0x7033140036ff0000 0x8e06628006dfe000 0x1fbfb0003fff8003 0xe3f7f60007fff000

def z1210 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff03e03ff07fe7 0xecffe07c07fe0ffc

def z1211 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x67ff03e03fcc7f9f 0xecffe07c07f98ff3

def z1212 : W := mkw 0x080403e40900fe84 0x0100807c81201fd0 0xe04003e400007f84 0x1c08007c80000ff0

def z1213 : W := mkw 0xb128fc1ed27f858d 0x76251f83da4ff0b1 0x9800fc1fc03f809a 0x13001f83f807f013

def z1214 : W := mkw 0x840cc31a98285050 0x5081986353050a0a 0xabdcc31ff83c70fe 0xf57b9863ff078e1f

def z1215 : W := mkw 0x401bec0024c50000 0xe8037d800498a000 0x1fbffc003fcf8003 0xe3f7ff8007f9f000

def z1216 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x1dbfbc003ff38003 0x63b7f78007fe7000

def z1217 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xfde2f2df073fecff 0x7fbc5e5be0e7fd9f

def z1218 : W := mkw 0x703bfca2b6ff0000 0xee077f9456dfe000 0x1fbffc20ffff8003 0xe3f7ff841ffff000

def z1219 : W := mkw 0x480403e02d807a00 0x0900807c05b00f40 0x63fc03e03fc07f05 0xec7f807c07f80fe0

def z1220 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc00c1018 0x9ff3fffff8018203

def z1221 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0xffbfffffffff8003 0xfff7fffffffff000

def z1222 : W := mkw 0x2008d400127f0000 0x44011a80024fe000 0x1fbffc003fff8003 0xe3f7ff8007fff000

def z1223 : W := mkw 0x00172ba280000000 0xa002e57450000000 0x561f3de7c0000000 0x0ac3e7bcf8000000

def z1224 : W := mkw 0x6013100026920000 0x8c02620004d24000 0x07bf00003ff38003 0xe0f7e00007fe7000

def z1225 : W := mkw 0x001feba280000000 0xe003fd7450000000 0x7f9fffe7c0000000 0x0ff3fffcf8000000

def z1226 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x1de2b2d30733ece7 0x63bc565a60e67d9c

def z1227 : W := mkw 0x001328a280000000 0xa002651450000000 0xf4033defc0000000 0x1e8067bdf8000000

def z1228 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x7fffb3e03fc07f05 0xeffff67c07f80fe0

def z1229 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfe9f7defc0000000 0x1fd3efbdf8000000

def z1230 : W := mkw 0x00172ba280000000 0xa002e57450000000 0xff9fbff7c0000000 0x1ff3f7fef8000000

def z1231 : W := mkw 0x8408e81a90280050 0x70811d035205000a 0xfdc2fedfc03c60fe 0x7fb85fdbf8078c1f

def z1232 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xfd9fbef7c0000000 0x1fb3f7def8000000

def z1233 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xff83fd2cc0cf9f9f 0xbff07fa59819f3f3

def z1234 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xebdcc338383c7ffe 0xfd7b986707078fff

def z1235 : W := mkw 0x0b0403e54900ffaf 0x0160807ca9201ff5 0xe04003ffc0007ffc 0x1c08007ff8000fff

def z1236 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x1fbffc003f338003 0x63f7ff8007e67000

def z1237 : W := mkw 0x841febba88005050 0xf083fd7751000a0a 0xffdfffffc0006060 0x1ffbfffff8000c0c

def z1238 : W := mkw 0x8008e81a80000000 0x70011d0350000000 0xdc02fcdfc0000000 0x1b805f9bf8000000

def z1239 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0xffbffd2cffff931b 0xfff7ffa59ffff263

def z1240 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xbb9effdfc0000000 0x1773dffbf8000000

def z1241 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xffdfffffc03c70fe 0xfffbfffff8078e1f

def z1242 : W := mkw 0xcc1703f82d807a50 0x9982e07f05b00f4a 0x67ff03f03fc07f65 0xecffe07e07f80fec

def z1243 : W := mkw 0x010004044045858d 0x002000808808b0b1 0xff834fecc0cf9f9f 0xbff069fd9819f3f3

def z1244 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x76814d2cc0cf9f1d 0xaed029a59819f3e3

def z1245 : W := mkw 0x0a08c0451128aca6 0x41411808a2251594 0xebdcc2d7383c6ce6 0xfd7b985ae7078d9c

def z1246 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0xfd83feffc0000000 0x1fb07fdff8000000

def z1247 : W := mkw 0x801febba90280000 0xf003fd7752050000 0xff9ffffff80c0000 0x9ff3ffffff018000

def z1248 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xff9ffffff83c101a 0xfff3ffffff078203

def z1249 : W := mkw 0xcc1703f82d807a50 0x9982e07f05b00f4a 0xefff43f83fcc7fff 0xfdffe87f07f98fff

def z1250 : W := mkw 0x6013140026d70000 0x8c02628004dae000 0x1fbffc003fff8003 0xe3f7ff8007fff000

def z1251 : W := mkw 0xa40413180a125050 0x1480826301424a0a 0xbde2b3180733f0ff 0x77bc566300e67e1f

def z1252 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0xffe3f3ff07ffffff 0xfffc7e7fe0ffffff

def z1253 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x7fbffc003fff8c07 0xeff7ff8007fff180

def z1254 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc0000c05 0x3ff3fffff8000180

def z1255 : W := mkw 0x001328a280000000 0xa002651450000000 0x76833de7c0c01f05 0xaed067bcf81803e0

def z1256 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x0bbef0003fff8003 0xe177de0007fff000

def z1257 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff83c7078 0xdffbffffff078e0f

def z1258 : W := mkw 0x80172bba80000000 0xb002e57750000000 0xfe837fffc0000000 0x1fd06ffff8000000

def z1259 : W := mkw 0x001328a280000000 0xa002651450000000 0x5d83bce7c0000000 0x0bb0779cf8000000

def z1260 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xbfdcc318383ff0ff 0xf7fb98630707fe1f

def z1261 : W := mkw 0x8e0403fd0900fef6 0x11c0807fa1201fde 0xe04003ff00007ffc 0x1c08007fe0000fff

def z1262 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x1162b2d70733e060 0x422c565ae0e67c0c

def z1263 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xefdcc318383c7cff 0xfdfb986307078f9f

def z1264 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x9de2b2d70733e0e3 0x73bc565ae0e67c1c

def z1265 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x667f03e03fc07f05 0x8ccfe07c07f80fe0

def z1266 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0x555fbef7f8306060 0x4aabf7deff060c0c

def z1267 : W := mkw 0x703bfca036ff0200 0xee077f9406dfe040 0x1fbffc203fff8303 0xe3f7ff8407fff060

def z1268 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xbfdef318383c70fe 0xf7fbde6307078e1f

def z1269 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xf61f7fffc0000000 0x1ec3effff8000000

def z1270 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9fffffc000109c 0x1ff3fffff8000213

def z1271 : W := mkw 0xc41febbabca85050 0xf883fd7757950a0a 0xfffffffffffc70ff 0xffffffffffff8e1f

def z1272 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x9fbffc0cffff8003 0xf3f7ff819ffff000

def z1273 : W := mkw 0x801febba90280000 0xf003fd7752050000 0xffdffffff83c60e6 0xfffbffffff078c1c

def z1274 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xabdcc318383c60fa 0x557b986307078c1f

def z1275 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0x1fbffc20ffff8303 0xe3f7ff841ffff060

def z1276 : W := mkw 0x010004044045858d 0x002000808808b0b1 0x9a014d2cc0cf9f9f 0xb34029a59819f3f3

def z1277 : W := mkw 0x713bfc0076ff0109 0xee277f800edfe021 0x1fbffc08ffff801b 0xe3f7ff811ffff003

def z1278 : W := mkw 0x70333c0026d70000 0xae06678004dae000 0x163f3c003fc38001 0x82c7e78007f87000

def z1279 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x07bfb0003fff8003 0xe0f7f60007fff000

def z1280 : W := mkw 0x0408c00018285050 0x4081180003050a0a 0x025c4000383c70fe 0xe04b880007078e1f

def z1281 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xff9ffffff8000000 0x1ff3ffffff000000

def z1282 : W := mkw 0x48172be2ad807a00 0xa902e57c55b00f40 0x67ff0fe0ffc07f05 0xecffe1fc1ff80fe0

def z1283 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xdd1ffeffc0000000 0x1ba3ffdff8000000

def z1284 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xfde2b2d70733ffff 0x7fbc565ae0e67fff

def z1285 : W := mkw 0x2a0010450312aca6 0x05400208a0625594 0x0162b2d30733e0e2 0x402c565a60e67c1c

def z1286 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x6fff83e03ff07f07 0xedfff07c07fe0fe0

def z1287 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0x0bdcc210383c70fe 0xe17b984207078e1f

def z1288 : W := mkw 0x703bf80036ba0000 0xee077f0006d74000 0x193eb0003f338002 0x4327d60007e67000

def z1289 : W := mkw 0x001328a280000000 0xa002651450000000 0xf4033ef7c0000000 0x1e8067def8000000

def z1290 : W := mkw 0x480403402d807a00 0x0900806805b00f40 0x027c01003fc07f05 0xe04f802007f80fe0

def z1291 : W := mkw 0x401703a02c805200 0x8802e07405900a40 0x67bf01203fc01f05 0xecf7e02407f803e0

def z1292 : W := mkw 0x801febba90280000 0xf003fd7752050000 0xff9ffffff8300000 0x5ff3ffffff060000

def z1293 : W := mkw 0x80172bba80000000 0xb002e57750000000 0xf79f3fffc0000000 0x1ef3e7fff8000000

def z1294 : W := mkw 0x801be8ba80000000 0xf0037d1750000000 0x5403bcf7c0000000 0x0a80779ef8000000

def z1295 : W := mkw 0x2b0014454357adaf 0x05600288a86af5b5 0xabe0c31807ffffff 0xf57c186300ffffff

def z1296 : W := mkw 0x841febba98285050 0xf083fd7753050a0a 0xffdffffff8307064 0xfffbffffff060e0c

def z1297 : W := mkw 0x0100040040450109 0x002000800808a021 0x7e814d28c0cf9f1f 0xafd029a51819f3e3

def z1298 : W := mkw 0x703bfc0036ff0000 0xee077f8006dfe000 0x163f7c003fff8003 0xe2c7ef8007fff000

def z1299 : W := mkw 0x2b0010454312adaf 0x05600208a86255b5 0xffe3ffffc733ffff 0x7ffc7ffff8e67fff

def z1300 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xaadc4108383c70fe 0xf55b882107078e1f

def z1301 : W := mkw 0x481703e02d807a00 0x8902e07c05b00f40 0x637f03e03fc07f04 0xcc6fe07c07f80fe0

def z1302 : W := mkw 0x401328a2a4800200 0xa802651454900040 0x54033ce7c0c00300 0x0a80679cf8180060

def z1303 : W := mkw 0x840cc31818285050 0x5081986303050a0a 0xffddcf3cf8fc7fff 0xfffbb9e79f1f8fff

def z1304 : W := mkw 0x801febba80000000 0xf003fd7750000000 0xff9ffffff8000000 0xfff3ffffff000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z7,z5,z6]),(0,[z0,z2,z3,z8,z4,z5,z6]),(0,[z0,z2,z9,z3,z4,z5,z6]),(0,[z10,z11,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z12]),(0,[z0,z2,z13,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z14,z4,z6])],[(0,[z0,z2,z3,z15,z4,z5,z6]),(0,[z0,z16,z17,z3,z4,z5,z6]),(0,[z0,z2,z18,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z19])],[],[(0,[z0,z2,z20,z3,z4,z5,z6]),(1,[z0,z2,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z22]),(0,[z11,z0,z2,z23,z4,z5,z6])],[(0,[z0,z2,z24,z25,z4,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z27,z3,z4,z5,z6]),(0,[z0,z2,z25,z3,z4,z5,z6]),(0,[z28,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z29,z3,z4,z30,z6]),(0,[z0,z31,z2,z3,z4,z6,z32]),(0,[z33,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z34,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z35])],[(0,[z0,z2,z3,z4,z5,z6,z32]),(0,[z0,z2,z3,z4,z5,z6,z36])],[(0,[z0,z2,z37,z3,z4,z5,z6]),(1,[z0,z2,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z39,z5,z6]),(0,[z0,z2,z40,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z41])]],
   [[(0,[z0,z17,z27,z3,z4,z5,z6]),(0,[z42,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z43,z5,z6]),(0,[z44,z0,z2,z38,z4,z5,z6])],[(0,[z45,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z46,z5,z6]),(0,[z0,z2,z24,z47,z4,z5,z6]),(0,[z0,z17,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z49,z6,z48]),(0,[z10,z0,z2,z3,z4,z50,z6]),(0,[z0,z2,z3,z4,z51,z6,z48])],[(0,[z52,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z30,z6]),(0,[z0,z2,z3,z4,z5,z53,z6]),(0,[z0,z54,z2,z3,z4,z5,z6])],[(0,[z0,z2,z29,z4,z5,z6,z55]),(0,[z0,z2,z3,z4,z5,z6,z56]),(0,[z57,z0,z2,z3,z4,z5,z58]),(0,[z0,z2,z3,z4,z6,z48,z41])],[(0,[z59,z11,z0,z2,z3,z4,z6]),(0,[z60,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z3,z62,z4,z5,z6]),(0,[z0,z2,z3,z63,z4,z5,z6]),(0,[z64,z0,z2,z3,z4,z58,z6]),(0,[z11,z0,z2,z3,z65,z4,z6])],[(0,[z0,z16,z2,z47,z4,z5,z6]),(1,[z0,z2,z3,z4,z58,z48]),(0,[z0,z2,z3,z66,z49,z5,z6]),(0,[z10,z0,z2,z3,z4,z5,z55]),(0,[z0,z2,z3,z14,z4,z5,z67]),(1,[z11,z0,z68,z2,z3,z4])],[(0,[z0,z2,z3,z69,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z70]),(0,[z0,z2,z3,z4,z5,z6,z71])],[(1,[z0,z61,z3,z62,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z72]),(0,[z73,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z74,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z75,z6]),(0,[z0,z2,z76,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z77,z6]),(1,[z0,z31,z3,z4,z78,z6]),(0,[z0,z79,z3,z4,z5,z58,z6])],[(0,[z0,z80,z2,z3,z4,z5,z6]),(0,[z44,z81,z0,z2,z3,z4,z6]),(0,[z0,z82,z2,z83,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z84]),(0,[z10,z0,z2,z85,z4,z5,z6])],[(0,[z86,z0,z2,z3,z87,z5,z6]),(0,[z59,z0,z88,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z48,z70]),(0,[z10,z0,z2,z4,z5,z6,z32])],[(0,[z0,z2,z3,z4,z5,z6,z89]),(0,[z11,z0,z2,z3,z4,z6,z48])],[(0,[z86,z81,z2,z3,z4,z5,z6]),(0,[z0,z2,z90,z3,z4,z5,z6]),(1,[z0,z2,z91,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z6]),(0,[z93,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z94,z85,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z95]),(0,[z96,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z97])],[(0,[z0,z2,z3,z4,z5,z6,z98]),(0,[z44,z0,z2,z3,z4,z78,z6]),(0,[z99,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z100,z48]),(0,[z0,z2,z3,z101,z47,z5,z6]),(0,[z0,z102,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z103,z6]),(0,[z81,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z83,z3,z5,z6,z104]),(0,[z0,z2,z3,z4,z5,z6,z105])]],
   [[(0,[z0,z106,z2,z3,z4,z5,z6]),(0,[z0,z107,z3,z4,z5,z6,z108]),(0,[z109,z0,z2,z3,z4,z110,z6])],[(0,[z111,z0,z2,z3,z4,z5,z6]),(0,[z59,z0,z2,z3,z4,z112,z6]),(0,[z113,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z114,z5,z6]),(0,[z0,z2,z3,z4,z5,z115,z100]),(1,[z116,z0,z2,z3,z4,z6]),(0,[z11,z0,z61,z2,z3,z4,z6]),(1,[z117,z2,z3,z4,z5,z6]),(0,[z0,z2,z94,z83,z3,z5,z6])],[(0,[z0,z2,z3,z4,z118,z5,z6])],[],[(0,[z0,z2,z119,z4,z5,z6,z32]),(0,[z120,z0,z2,z3,z4,z5,z6])],[(0,[z121,z0,z2,z3,z4,z5,z6]),(0,[z0,z17,z107,z3,z4,z5,z6]),(0,[z122,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z47,z4,z5,z6,z55]),(0,[z0,z123,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z6,z108]),(1,[z0,z2,z3,z5,z6,z124]),(0,[z125,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z67,z6,z104]),(1,[z11,z0,z2,z23,z4,z6]),(0,[z0,z2,z3,z126,z4,z5,z6])],[(0,[z0,z27,z3,z4,z5,z6,z70]),(0,[z0,z2,z127,z4,z128,z5,z6]),(0,[z0,z61,z2,z3,z62,z5,z6]),(0,[z0,z2,z129,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z48,z70]),(0,[z130,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z14,z4,z5,z104])],[(0,[z0,z2,z3,z4,z131,z5,z6]),(0,[z132,z0,z2,z3,z4,z6,z48]),(0,[z10,z0,z2,z24,z4,z5,z6]),(1,[z109,z0,z2,z3,z5,z104])]],
   [[(0,[z0,z107,z2,z3,z4,z5,z6]),(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z134,z6,z48]),(0,[z11,z0,z2,z3,z4,z134,z6]),(1,[z0,z2,z3,z135,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z136]),(0,[z0,z79,z2,z3,z4,z5,z58])],[(0,[z0,z137,z2,z3,z4,z5,z6]),(0,[z11,z0,z138,z2,z3,z4,z6]),(0,[z44,z0,z2,z3,z135,z5,z6]),(0,[z0,z31,z2,z3,z4,z49,z6]),(0,[z0,z2,z3,z4,z5,z6,z139]),(0,[z0,z2,z83,z4,z140,z5,z6]),(0,[z11,z0,z2,z94,z3,z4,z6]),(0,[z141,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z142]),(0,[z0,z2,z3,z4,z5,z143,z6])],[(0,[z0,z2,z3,z4,z144,z5,z6]),(0,[z0,z2,z145,z4,z118,z5,z6])],[(0,[z0,z2,z146,z3,z4,z5,z6]),(0,[z0,z147,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z30,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z148]),(0,[z0,z2,z149,z3,z4,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z150,z3,z4,z5,z6]),(0,[z151,z152,z2,z3,z4,z5,z6]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z2,z145,z3,z4,z5,z6])],[(1,[z0,z2,z3,z87,z5,z6]),(0,[z0,z2,z154,z3,z4,z5,z6]),(1,[z0,z2,z155,z4,z5,z6]),(0,[z0,z2,z83,z3,z65,z5,z6]),(0,[z0,z2,z156,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z157]),(0,[z0,z2,z3,z4,z158,z5,z6])],[(0,[z0,z159,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z160,z4,z5,z6]),(0,[z0,z2,z161,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z162]),(0,[z44,z0,z2,z155,z4,z5,z6]),(0,[z57,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z110,z5,z6]),(0,[z0,z2,z163,z4,z5,z67,z6])]],
   [[(1,[z0,z2,z129,z4,z5,z6])],[(1,[z121,z27,z3,z4,z5,z6]),(1,[z81,z2,z3,z4,z164,z6]),(0,[z151,z0,z2,z3,z4,z5,z165]),(0,[z0,z2,z3,z166,z4,z5,z6]),(0,[z10,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z14,z5,z6]),(0,[z0,z2,z3,z4,z167,z5,z6])],[(0,[z151,z11,z0,z2,z3,z4,z6]),(0,[z0,z168,z2,z3,z4,z5,z6]),(0,[z169,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z170,z4,z5,z6]),(0,[z0,z2,z171,z3,z4,z5,z6]),(0,[z11,z172,z0,z2,z3,z4,z6])],[(0,[z86,z107,z2,z3,z4,z5,z6]),(0,[z0,z173,z2,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z5,z70]),(0,[z0,z2,z3,z4,z6,z35,z48])],[(0,[z0,z174,z2,z3,z4,z5,z6]),(0,[z175,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z94,z3,z4,z5,z6]),(0,[z176,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z6,z177])],[(0,[z0,z138,z27,z3,z4,z5,z6]),(0,[z0,z178,z2,z3,z4,z5,z6]),(0,[z0,z107,z79,z3,z4,z5,z6]),(0,[z0,z179,z2,z3,z119,z5,z6]),(0,[z0,z2,z3,z180,z4,z5,z6]),(0,[z0,z61,z2,z83,z3,z5,z6])],[(0,[z181,z0,z2,z119,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z5,z100]),(0,[z0,z138,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z182,z4,z5,z6])],[(0,[z0,z107,z3,z62,z4,z5,z6]),(0,[z0,z138,z2,z3,z183,z5,z6]),(0,[z0,z2,z3,z65,z183,z5,z6]),(0,[z0,z2,z3,z4,z5,z184,z6]),(0,[z11,z0,z82,z2,z3,z4,z6])]],
   [[(0,[z2,z3,z4,z164,z5,z134,z6]),(0,[z185,z0,z2,z3,z4,z5,z6]),(0,[z186,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z187,z4,z5,z6])],[(0,[z188,z0,z2,z3,z4,z5,z6]),(0,[z0,z102,z2,z3,z47,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z189]),(0,[z0,z2,z3,z4,z58,z6,z190]),(0,[z10,z0,z2,z3,z4,z5,z115]),(0,[z0,z2,z3,z4,z191,z5,z6]),(0,[z192,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z193,z3,z4,z5,z6]),(0,[z194,z0,z2,z3,z4,z5,z6]),(1,[z195,z2,z3,z128,z5,z6]),(1,[z0,z2,z196,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z197]),(0,[z198,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z199,z5,z6]),(0,[z200,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z3,z4,z164,z5,z6]),(0,[z0,z2,z3,z4,z5,z202,z6]),(0,[z152,z0,z2,z3,z4,z6,z48]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z204,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z205,z5,z6]),(0,[z0,z2,z3,z4,z206,z5,z6])],[(0,[z207,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z208,z4,z5,z6]),(1,[z0,z2,z83,z140,z5,z6]),(0,[z209,z0,z2,z3,z4,z5,z6])],[(0,[z0,z210,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z119,z4,z6,z48]),(0,[z0,z2,z3,z4,z211,z5,z6]),(0,[z0,z2,z3,z4,z5,z115,z165]),(0,[z0,z17,z2,z47,z4,z5,z6]),(0,[z0,z2,z29,z3,z4,z6,z48])],[(0,[z212,z0,z2,z3,z183,z5,z6]),(0,[z0,z68,z2,z3,z4,z158,z5]),(0,[z120,z11,z0,z2,z3,z4,z6])],[(0,[z213,z0,z214,z3,z4,z5,z6]),(0,[z0,z215,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z128,z5,z6,z104]),(0,[z0,z3,z62,z4,z216,z5,z6]),(0,[z0,z2,z3,z4,z217,z5,z6]),(0,[z0,z218,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z128,z6,z48]),(0,[z0,z2,z3,z4,z5,z6,z219]),(0,[z0,z2,z3,z4,z6,z48,z48])],[(0,[z220,z0,z2,z3,z4,z5,z6]),(0,[z86,z0,z107,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z221]),(0,[z0,z2,z3,z222,z4,z5,z6]),(0,[z223,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z48])],[(0,[z213,z0,z2,z3,z4,z134,z6]),(0,[z0,z224,z2,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z94,z4,z5,z6,z55])],[(0,[z225,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z226,z3,z4,z5,z6]),(0,[z11,z212,z0,z2,z3,z4,z6]),(0,[z0,z227,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z58,z6]),(0,[z0,z2,z3,z4,z5,z6,z228]),(0,[z229,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z230])],[(1,[z0,z2,z3,z4,z5,z231]),(0,[z0,z2,z3,z232,z4,z5,z6]),(0,[z57,z0,z2,z3,z4,z233,z6]),(0,[z11,z0,z2,z3,z4,z115,z6]),(0,[z0,z2,z3,z4,z6,z48,z219])],[(1,[z44,z0,z3,z4,z6,z108]),(0,[z0,z31,z2,z3,z4,z6,z108])],[(0,[z0,z2,z3,z183,z5,z6,z104]),(0,[z234,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z6,z165]),(1,[z0,z2,z3,z4,z5,z235]),(0,[z0,z2,z3,z4,z5,z6,z108]),(0,[z0,z2,z3,z4,z5,z236,z6]),(0,[z0,z2,z3,z4,z237,z5,z6]),(1,[z11,z0,z2,z3,z4,z48]),(0,[z11,z0,z238,z2,z3,z4,z6])]],
   [[(0,[z0,z2,z239,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z240,z5,z6]),(0,[z0,z61,z2,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z5,z235])],[(0,[z59,z181,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z241]),(0,[z0,z242,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z47,z4,z6,z48]),(0,[z0,z2,z3,z4,z5,z6,z243]),(0,[z11,z132,z0,z2,z3,z4,z6])],[(0,[z0,z138,z107,z3,z4,z5,z6]),(0,[z0,z2,z244,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z134,z6]),(0,[z245,z0,z2,z3,z4,z5,z6]),(0,[z109,z0,z61,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z246])],[(0,[z247,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z248]),(0,[z0,z2,z3,z4,z5,z249,z6]),(1,[z250,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z49,z6]),(0,[z0,z2,z3,z65,z4,z6,z41])],[(0,[z44,z250,z2,z3,z4,z5,z6]),(0,[z0,z251,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z252,z5,z6])],[(0,[z0,z2,z3,z253,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z100,z6]),(0,[z0,z254,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z255,z4,z5,z6]),(0,[z0,z82,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z3,z4,z5,z55]),(0,[z0,z2,z3,z14,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z256,z6]),(0,[z213,z11,z0,z2,z3,z4,z6])],[(0,[z59,z0,z2,z94,z4,z5,z6]),(0,[z195,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z257,z3,z4,z5,z6]),(0,[z0,z258,z2,z3,z4,z5,z6])]],
   [[(0,[z195,z0,z2,z3,z183,z5,z6]),(0,[z259,z0,z2,z3,z4,z5,z6]),(0,[z0,z260,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z261]),(1,[z151,z2,z3,z4,z5,z165]),(0,[z0,z2,z262,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z263]),(0,[z0,z2,z3,z4,z5,z6,z264]),(1,[z0,z2,z3,z4,z6,z12]),(0,[z0,z2,z3,z4,z5,z6,z265])],[(0,[z44,z213,z0,z2,z3,z4,z6]),(0,[z266,z0,z2,z3,z4,z5,z6]),(0,[z132,z0,z2,z4,z5,z6,z32]),(0,[z0,z2,z267,z3,z4,z6,z48]),(0,[z268,z0,z2,z3,z4,z5,z6])],[(1,[z152,z2,z3,z4,z5,z100]),(0,[z109,z0,z138,z2,z3,z5,z6]),(0,[z269,z0,z2,z3,z4,z5,z6])],[(0,[z59,z0,z2,z119,z4,z5,z6]),(0,[z0,z2,z3,z4,z270,z5,z6]),(0,[z0,z271,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z100,z55]),(0,[z0,z29,z3,z47,z4,z5,z6]),(0,[z0,z138,z2,z3,z5,z67,z6]),(0,[z0,z2,z3,z62,z5,z6,z41]),(0,[z0,z2,z3,z4,z5,z6,z272]),(0,[z0,z2,z3,z65,z5,z67,z6])],[(0,[z273,z0,z2,z3,z4,z5,z6])],[(0,[z86,z2,z3,z4,z5,z134,z6]),(1,[z0,z274,z3,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z5,z6]),(0,[z0,z2,z3,z4,z276,z5,z6]),(0,[z0,z2,z3,z4,z277,z5,z6]),(0,[z11,z0,z2,z3,z4,z140,z6]),(0,[z0,z2,z85,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z48,z32]),(0,[z11,z0,z2,z3,z4,z6,z55])],[(0,[z278,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z20,z3,z119,z5,z6]),(0,[z0,z279,z2,z3,z4,z5,z6]),(0,[z207,z11,z0,z2,z3,z4,z6]),(0,[z209,z11,z0,z2,z3,z4,z6])],[(0,[z195,z0,z82,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z280,z5,z6]),(0,[z0,z138,z2,z3,z216,z5,z6]),(0,[z0,z2,z3,z65,z216,z5,z6]),(0,[z44,z0,z2,z3,z4,z6,z32]),(0,[z132,z0,z2,z3,z4,z49,z6]),(0,[z0,z281,z2,z3,z4,z118,z5]),(0,[z0,z2,z3,z4,z5,z6,z282]),(0,[z283,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z284,z4,z5,z6]),(0,[z109,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z285,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z286])],[(0,[z181,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z5,z287,z6]),(0,[z288,z0,z2,z3,z4,z5,z6]),(0,[z0,z289,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z290,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z291,z5,z6]),(0,[z151,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z292,z5,z6])],[(0,[z0,z2,z3,z4,z5,z293,z6]),(0,[z294,z0,z2,z3,z4,z5,z6]),(0,[z295,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z296,z5,z6]),(0,[z186,z0,z2,z3,z4,z118,z6]),(0,[z11,z0,z2,z3,z23,z4,z6])],[(0,[z121,z0,z27,z3,z4,z5,z6]),(0,[z213,z0,z2,z3,z4,z5,z297])],[(0,[z0,z2,z3,z4,z5,z6,z298]),(0,[z0,z2,z3,z62,z4,z5,z6]),(0,[z0,z299,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z50,z6])],[(0,[z0,z2,z25,z4,z5,z6,z55]),(0,[z0,z2,z3,z4,z300,z5,z6]),(0,[z0,z82,z2,z94,z4,z5,z6]),(0,[z0,z82,z2,z3,z14,z5,z6])]],
   [[(0,[z11,z86,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z6,z301]),(0,[z302,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z303])],[(0,[z0,z2,z3,z4,z304,z5,z6]),(0,[z0,z2,z3,z4,z49,z134,z6]),(0,[z0,z305,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z306,z4,z5,z6]),(0,[z0,z307,z2,z3,z4,z5,z6]),(0,[z308,z0,z2,z3,z4,z67,z6])],[(0,[z309,z0,z2,z3,z4,z5,z6])],[(0,[z0,z107,z3,z47,z4,z5,z6]),(0,[z310,z0,z2,z3,z4,z5,z6]),(1,[z0,z161,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z0,z312,z2,z3,z4,z5,z6]),(1,[z186,z0,z2,z3,z6,z41])],[(0,[z0,z2,z3,z4,z5,z313,z6]),(0,[z0,z2,z3,z65,z4,z118,z6])],[(0,[z314,z0,z2,z3,z4,z5,z6]),(0,[z0,z138,z2,z3,z128,z5,z6]),(0,[z0,z2,z3,z4,z315,z5,z6]),(0,[z0,z2,z3,z316,z4,z5,z6]),(0,[z0,z2,z3,z317,z4,z5,z6]),(1,[z0,z2,z3,z4,z158,z48])],[(0,[z318,z0,z2,z3,z4,z5,z6]),(1,[z0,z319,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z100,z6,z320]),(0,[z0,z2,z3,z321,z4,z5,z6]),(0,[z0,z3,z4,z78,z5,z6,z108]),(0,[z0,z2,z3,z4,z5,z58,z6]),(0,[z322,z0,z2,z3,z4,z5,z6])],[(0,[z0,z107,z31,z3,z4,z5,z6]),(0,[z0,z2,z323,z4,z128,z5,z6]),(0,[z0,z16,z2,z29,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z115,z6]),(0,[z324,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z67,z6,z325]),(0,[z11,z0,z326,z2,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z327,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z165]),(0,[z0,z2,z3,z4,z328,z5,z6]),(0,[z0,z2,z24,z3,z4,z5,z6]),(0,[z329,z0,z2,z3,z4,z6,z48])],[(0,[z0,z2,z3,z330,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z77,z6]),(0,[z0,z68,z2,z3,z4,z5,z100]),(0,[z331,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z332,z6])],[(0,[z333,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z334]),(0,[z335,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z336]),(0,[z0,z2,z29,z3,z4,z6,z337]),(0,[z0,z2,z3,z4,z5,z6,z337]),(0,[z0,z2,z3,z4,z338,z5,z6]),(0,[z0,z339,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z340,z4,z5,z6]),(0,[z269,z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z6,z341]),(0,[z342,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z197]),(0,[z0,z16,z2,z3,z4,z5,z6])],[(0,[z0,z2,z94,z3,z183,z5,z6]),(0,[z0,z2,z343,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z344,z6]),(0,[z0,z2,z3,z4,z5,z345,z6]),(0,[z0,z2,z3,z4,z5,z6,z346]),(0,[z11,z0,z2,z347,z4,z5,z6])],[(0,[z59,z0,z2,z3,z4,z201,z6]),(0,[z81,z0,z2,z3,z4,z134,z6]),(0,[z0,z2,z3,z4,z5,z100,z6]),(0,[z0,z250,z2,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z348,z5,z6]),(1,[z349,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z3,z4,z5,z70]),(0,[z64,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z350]),(0,[z0,z2,z3,z4,z5,z351,z6]),(0,[z0,z68,z2,z3,z14,z4,z5]),(0,[z308,z0,z2,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z6,z48])]],
   [[(0,[z86,z0,z27,z3,z4,z5,z6]),(0,[z352,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z353,z3,z4,z5,z6]),(0,[z0,z2,z3,z354,z4,z5,z6]),(0,[z57,z0,z3,z4,z5,z6,z70]),(0,[z0,z2,z3,z4,z5,z6,z355]),(0,[z0,z2,z3,z4,z356,z5,z6]),(0,[z0,z2,z3,z4,z5,z67,z6]),(0,[z0,z2,z3,z4,z6,z48,z336])],[(0,[z86,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z5,z357,z6]),(0,[z0,z2,z3,z183,z4,z6,z48]),(0,[z358,z0,z2,z3,z4,z5,z6]),(0,[z359,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z3,z4,z5,z115]),(0,[z109,z0,z2,z3,z5,z6,z104]),(0,[z11,z0,z2,z3,z4,z6,z6])],[(0,[z121,z0,z107,z3,z4,z5,z6]),(0,[z0,z2,z3,z360,z4,z5,z6]),(1,[z0,z2,z127,z4,z5,z6]),(0,[z0,z2,z3,z4,z361,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z362])],[(0,[z0,z2,z3,z4,z5,z363,z6]),(0,[z213,z0,z2,z364,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z365]),(0,[z44,z0,z2,z3,z4,z49,z6]),(0,[z0,z2,z83,z4,z5,z6,z32])],[(0,[z86,z2,z3,z4,z5,z6,z165]),(0,[z0,z2,z3,z4,z5,z48,z165]),(0,[z116,z0,z2,z3,z4,z100,z6]),(0,[z0,z2,z3,z4,z216,z5,z6]),(0,[z366,z0,z2,z3,z4,z5,z6]),(0,[z367,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z368,z5,z6]),(0,[z0,z68,z2,z24,z3,z4,z5]),(0,[z0,z2,z4,z118,z5,z6,z177])],[(0,[z0,z2,z3,z4,z112,z5,z6]),(0,[z0,z369,z2,z3,z4,z5,z6]),(0,[z117,z0,z2,z3,z4,z5,z6]),(0,[z0,z370,z2,z3,z4,z5,z6]),(1,[z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z371,z4,z5,z6])],[(0,[z372,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z373,z5,z6]),(0,[z59,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z374,z4,z5,z6]),(0,[z0,z2,z3,z4,z115,z6,z12]),(0,[z11,z11,z0,z2,z3,z4,z6])],[(0,[z11,z0,z2,z25,z3,z4,z6]),(0,[z213,z0,z2,z3,z4,z5,z6]),(0,[z0,z375,z2,z3,z4,z5,z6]),(0,[z0,z2,z83,z3,z140,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z55])]],
   [[(0,[z2,z25,z3,z119,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z376]),(0,[z11,z0,z2,z3,z4,z128,z6]),(0,[z213,z0,z2,z3,z4,z164,z6]),(0,[z0,z82,z61,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z377,z6]),(0,[z11,z0,z79,z2,z3,z4,z6])],[(0,[z59,z0,z2,z3,z4,z5,z231]),(1,[z0,z2,z3,z4,z48,z165]),(0,[z378,z0,z2,z3,z4,z5,z6]),(0,[z379,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z124]),(0,[z0,z2,z3,z65,z4,z6,z48]),(1,[z0,z2,z4,z5,z6,z325]),(0,[z0,z2,z3,z4,z6,z6,z48])],[(1,[z0,z2,z3,z380,z5,z6]),(0,[z0,z2,z3,z4,z5,z231,z6]),(0,[z0,z2,z3,z381,z4,z5,z6]),(0,[z0,z2,z3,z4,z382,z5,z6]),(0,[z0,z2,z383,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z115,z6,z32]),(1,[z0,z2,z3,z4,z384,z6]),(0,[z0,z2,z3,z4,z5,z6,z385])],[(0,[z386,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z387]),(0,[z109,z0,z68,z2,z3,z4,z5]),(0,[z388,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z241]),(0,[z0,z2,z3,z389,z4,z5,z6]),(0,[z390,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z135,z5,z6]),(0,[z0,z2,z3,z4,z5,z235,z6]),(0,[z44,z0,z3,z4,z5,z6,z108]),(0,[z391,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z392,z6]),(0,[z0,z31,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z393,z6]),(0,[z0,z2,z3,z394,z4,z5,z6]),(0,[z0,z395,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z396])],[(0,[z195,z0,z2,z3,z128,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z3,z4,z5,z297,z6]),(0,[z151,z0,z2,z3,z211,z5,z6]),(0,[z0,z397,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z398,z6]),(0,[z399,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z400]),(0,[z0,z2,z83,z3,z5,z6,z41]),(0,[z0,z401,z2,z3,z4,z5,z6])]],
   [[(0,[z181,z0,z2,z25,z4,z5,z6]),(0,[z212,z0,z2,z3,z4,z6,z48]),(0,[z0,z82,z138,z2,z3,z5,z6]),(0,[z0,z2,z83,z24,z4,z5,z6]),(0,[z0,z82,z2,z94,z3,z5,z6]),(0,[z109,z0,z2,z3,z65,z5,z6]),(0,[z0,z238,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z402,z5,z6]),(0,[z0,z403,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z404,z48])],[(0,[z2,z27,z3,z4,z5,z134,z6]),(0,[z0,z2,z3,z4,z5,z6,z405]),(0,[z0,z61,z2,z3,z183,z5,z6]),(0,[z213,z0,z31,z2,z3,z4,z6]),(0,[z0,z2,z38,z3,z4,z5,z6])],[(0,[z81,z2,z27,z3,z4,z5,z6]),(1,[z0,z2,z3,z406,z5,z6]),(0,[z407,z0,z2,z3,z4,z5,z6]),(0,[z408,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z409]),(0,[z0,z2,z3,z4,z78,z6,z48]),(0,[z0,z2,z3,z4,z140,z6,z48]),(0,[z10,z0,z2,z4,z5,z6,z55]),(0,[z0,z2,z3,z4,z5,z410,z6])],[(0,[z411,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z412,z6]),(0,[z0,z413,z2,z3,z4,z5,z6]),(0,[z0,z2,z414,z3,z4,z5,z6])],[(0,[z0,z2,z3,z415,z4,z5,z6]),(0,[z0,z2,z3,z5,z67,z6,z41])],[(0,[z186,z0,z2,z3,z4,z6,z41]),(0,[z109,z0,z2,z3,z4,z5,z48])],[(0,[z0,z2,z3,z4,z416,z5,z6]),(0,[z0,z417,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z14,z183,z5,z6]),(1,[z0,z102,z2,z3,z5,z6]),(0,[z0,z79,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z418,z5,z6]),(0,[z419,z0,z2,z3,z4,z5,z6]),(1,[z308,z0,z2,z3,z4,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z420,z6]),(0,[z212,z0,z82,z2,z3,z5,z6]),(1,[z0,z2,z3,z327,z5,z6]),(0,[z0,z421,z2,z3,z4,z5,z6]),(0,[z0,z2,z422,z3,z4,z5,z6])],[(0,[z0,z2,z27,z3,z4,z6,z48]),(0,[z0,z2,z25,z3,z4,z6,z48]),(0,[z0,z2,z3,z423,z4,z5,z6])],[(0,[z212,z0,z76,z3,z4,z5,z6]),(0,[z0,z2,z3,z348,z4,z5,z6]),(0,[z57,z117,z2,z3,z4,z5,z6]),(0,[z0,z2,z83,z3,z4,z5,z6]),(0,[z0,z424,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z425,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z320]),(0,[z0,z2,z3,z4,z5,z6,z426]),(0,[z0,z2,z3,z4,z5,z427,z6]),(0,[z428,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z429,z6]),(0,[z0,z430,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z431,z4,z5,z6]),(0,[z432,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z66,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z433])],[(0,[z0,z2,z119,z4,z5,z6,z55]),(1,[z0,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z434,z5,z6]),(0,[z11,z0,z2,z3,z4,z6,z104])],[(0,[z0,z435,z2,z3,z4,z5,z6]),(0,[z0,z2,z436,z27,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z48,z108]),(0,[z0,z2,z3,z4,z199,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z437]),(0,[z0,z2,z3,z4,z49,z5,z433]),(1,[z0,z2,z3,z65,z118,z6]),(1,[z0,z2,z145,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z438]),(1,[z0,z76,z3,z4,z5,z6]),(0,[z0,z17,z2,z29,z4,z5,z6])]],
   [[(0,[z195,z212,z2,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z6,z108]),(0,[z0,z31,z2,z3,z4,z78,z6]),(0,[z0,z2,z439,z3,z4,z5,z6]),(0,[z0,z2,z440,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z441,z6]),(0,[z0,z2,z3,z4,z442,z5,z6]),(0,[z11,z0,z2,z3,z62,z4,z6]),(0,[z11,z0,z2,z3,z4,z67,z6]),(0,[z0,z2,z347,z3,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z443,z6]),(0,[z0,z2,z3,z4,z5,z6,z444]),(0,[z11,z0,z2,z3,z126,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z445,z2,z3,z4,z5,z6]),(0,[z0,z349,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z58,z6,z48]),(0,[z132,z0,z2,z85,z4,z5,z6]),(0,[z446,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z177])],[(0,[z213,z2,z3,z4,z5,z134,z6]),(0,[z0,z2,z447,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z233,z6]),(0,[z0,z2,z3,z4,z5,z448,z6]),(0,[z11,z0,z2,z3,z4,z158,z6])],[(0,[z152,z0,z2,z3,z4,z5,z165]),(0,[z0,z17,z2,z3,z4,z5,z6]),(0,[z57,z349,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z49,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z449]),(0,[z0,z2,z3,z4,z158,z5,z48])],[(0,[z0,z2,z3,z4,z5,z6,z450]),(0,[z0,z2,z3,z4,z49,z164,z6]),(0,[z0,z2,z3,z4,z5,z6,z451]),(0,[z0,z2,z3,z4,z5,z452,z6]),(0,[z453,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z454]),(0,[z0,z2,z3,z4,z5,z6,z455]),(0,[z151,z2,z3,z4,z5,z6,z165]),(0,[z456,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z457]),(1,[z0,z2,z458,z4,z5,z6]),(1,[z0,z2,z3,z232,z5,z6]),(0,[z0,z2,z85,z4,z5,z115,z6])]],
   [[(0,[z0,z2,z3,z128,z140,z5,z6]),(0,[z0,z2,z3,z4,z459,z5,z6]),(0,[z0,z138,z2,z3,z62,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z460]),(0,[z10,z0,z2,z3,z4,z5,z48]),(1,[z0,z281,z2,z3,z4,z5])],[(1,[z59,z2,z119,z4,z5,z6]),(0,[z461,z0,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z129,z4,z5,z6]),(0,[z186,z0,z2,z3,z65,z5,z6])],[(0,[z0,z27,z3,z4,z5,z6,z108]),(0,[z0,z2,z3,z66,z4,z5,z6])],[(0,[z0,z2,z3,z4,z462,z5,z6]),(0,[z463,z0,z2,z3,z4,z5,z6]),(0,[z464,z0,z2,z3,z4,z5,z6]),(1,[z0,z138,z3,z216,z5,z6]),(0,[z465,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z24,z3,z4,z48])],[(0,[z0,z2,z94,z3,z128,z5,z6]),(0,[z11,z152,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z466,z5,z6])],[(0,[z59,z0,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z467,z4,z5,z6]),(0,[z0,z2,z214,z3,z4,z5,z6]),(1,[z0,z2,z85,z4,z49,z6])],[(0,[z213,z81,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z468,z5,z6]),(0,[z0,z61,z2,z3,z5,z67,z6]),(0,[z44,z11,z0,z2,z3,z4,z6]),(0,[z469,z0,z2,z3,z4,z5,z6]),(0,[z0,z470,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z118,z6,z48]),(0,[z0,z2,z3,z4,z5,z51,z6])],[(0,[z152,z2,z27,z3,z4,z5,z6]),(0,[z0,z2,z3,z183,z140,z5,z6]),(0,[z0,z82,z2,z3,z5,z6,z104]),(1,[z0,z2,z3,z4,z6,z282]),(0,[z11,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z128,z5,z6,z41]),(0,[z11,z0,z2,z3,z4,z164,z6]),(0,[z151,z0,z2,z21,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z190]),(0,[z11,z0,z2,z83,z3,z4,z6]),(0,[z0,z2,z3,z4,z384,z5,z6]),(0,[z0,z2,z3,z4,z252,z5,z6])],[(0,[z121,z0,z2,z3,z4,z6,z48]),(0,[z2,z27,z3,z4,z5,z6,z165]),(0,[z0,z2,z471,z3,z4,z5,z6]),(0,[z0,z2,z3,z216,z5,z6,z104]),(0,[z0,z2,z3,z4,z472,z5,z6]),(0,[z0,z473,z2,z3,z4,z5,z6]),(1,[z0,z474,z2,z3,z4,z5]),(0,[z0,z2,z475,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z476,z5,z6]),(0,[z0,z61,z2,z3,z216,z5,z6]),(0,[z0,z2,z3,z4,z5,z477,z6]),(0,[z0,z2,z3,z4,z5,z6,z404])],[(0,[z278,z0,z2,z27,z3,z4,z6]),(1,[z0,z2,z436,z3,z4,z6]),(0,[z81,z0,z2,z3,z4,z5,z6]),(0,[z57,z0,z2,z3,z199,z5,z6]),(0,[z0,z2,z3,z5,z115,z6,z264]),(0,[z0,z2,z3,z14,z5,z67,z6]),(0,[z11,z0,z2,z347,z3,z4,z6])],[(0,[z0,z107,z2,z3,z4,z6,z48]),(0,[z81,z0,z2,z3,z4,z164,z6]),(0,[z478,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z479]),(0,[z109,z0,z2,z3,z4,z5,z67])],[(0,[z0,z2,z3,z480,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z481]),(0,[z0,z482,z2,z3,z4,z5,z6]),(0,[z0,z2,z483,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z50,z6]),(0,[z11,z0,z2,z3,z126,z4,z6])],[(0,[z0,z2,z3,z4,z484,z5,z6]),(0,[z0,z485,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z183,z5,z6,z41]),(0,[z0,z486,z2,z3,z4,z5,z6]),(0,[z0,z138,z2,z83,z3,z5,z6]),(0,[z0,z2,z3,z14,z216,z5,z6]),(0,[z0,z2,z3,z487,z4,z5,z6]),(0,[z488,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z489,z3,z4,z5,z6]),(0,[z0,z490,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z65,z128,z5,z6]),(0,[z0,z16,z3,z47,z4,z5,z6])],[(0,[z491,z0,z2,z3,z4,z5,z6]),(0,[z181,z0,z2,z83,z4,z5,z6]),(0,[z0,z2,z3,z4,z492,z5,z6]),(0,[z0,z2,z29,z85,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z493])],[(0,[z59,z0,z2,z3,z373,z5,z6]),(0,[z2,z3,z4,z5,z100,z6,z165]),(0,[z0,z2,z29,z4,z5,z6,z32]),(0,[z11,z0,z31,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z32,z41]),(0,[z0,z2,z494,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z158,z6,z48])],[(0,[z57,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z495,z3,z4,z5,z6]),(0,[z132,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z115,z6]),(0,[z0,z2,z3,z4,z115,z6,z48])],[(0,[z0,z107,z3,z4,z5,z6,z70]),(0,[z0,z2,z3,z4,z496,z5,z6]),(0,[z0,z2,z3,z4,z5,z497,z6])],[(0,[z0,z2,z3,z87,z4,z5,z6]),(0,[z0,z2,z3,z21,z4,z5,z6]),(0,[z0,z2,z3,z498,z4,z5,z6]),(0,[z10,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z499,z5,z6])],[(0,[z59,z0,z2,z3,z380,z5,z6]),(0,[z500,z0,z2,z3,z4,z5,z6]),(0,[z195,z2,z3,z4,z128,z5,z6]),(0,[z213,z0,z2,z3,z275,z5,z6]),(0,[z81,z0,z31,z2,z3,z4,z6]),(0,[z11,z81,z0,z2,z3,z4,z6]),(0,[z0,z2,z501,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z502]),(0,[z0,z82,z2,z3,z65,z5,z6])],[(0,[z0,z503,z2,z3,z4,z5,z6]),(0,[z0,z2,z504,z3,z4,z5,z6]),(0,[z212,z0,z2,z3,z128,z5,z6]),(0,[z505,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z506,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z507,z6]),(0,[z0,z2,z508,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z104])]],
   [[(0,[z59,z0,z2,z3,z4,z5,z241]),(0,[z0,z2,z509,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z48,z165]),(0,[z0,z2,z94,z3,z4,z6,z48])],[(0,[z0,z27,z3,z62,z4,z5,z6]),(0,[z81,z2,z3,z4,z164,z5,z6]),(0,[z151,z0,z2,z91,z4,z5,z6]),(1,[z0,z2,z3,z4,z459,z6]),(0,[z0,z2,z3,z4,z510,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z511]),(1,[z0,z2,z3,z348,z5,z6]),(0,[z0,z512,z2,z3,z4,z5,z6])],[(0,[z0,z2,z88,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z513,z6]),(0,[z0,z2,z3,z4,z5,z6,z514]),(0,[z11,z0,z2,z3,z4,z78,z6]),(1,[z0,z515,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z118,z6,z32]),(0,[z0,z516,z2,z3,z4,z5,z6])],[(0,[z0,z2,z517,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z518]),(0,[z0,z519,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z62,z14,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z520]),(1,[z0,z82,z2,z94,z5,z6]),(0,[z0,z2,z3,z4,z6,z48,z104])],[(0,[z0,z2,z521,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z337]),(0,[z0,z2,z3,z4,z5,z6,z522]),(0,[z186,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z523,z5,z6]),(0,[z0,z2,z3,z14,z4,z5,z48])],[(1,[z0,z2,z20,z3,z5,z6]),(0,[z524,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z525,z6]),(0,[z0,z2,z3,z4,z5,z6,z526]),(0,[z0,z2,z83,z85,z4,z5,z6]),(0,[z192,z0,z2,z3,z4,z6,z48])],[(0,[z527,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z528,z5,z6]),(0,[z0,z2,z3,z4,z529,z5,z6]),(0,[z530,z0,z2,z3,z4,z5,z6])],[(0,[z531,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z164,z6,z48]),(0,[z0,z2,z29,z24,z4,z5,z6]),(1,[z0,z79,z3,z4,z5,z58]),(1,[z0,z2,z3,z5,z6,z22]),(0,[z0,z2,z3,z4,z6,z48,z355])]],
   [[(1,[z181,z2,z25,z4,z5,z6]),(0,[z212,z0,z173,z3,z4,z5,z6]),(0,[z151,z0,z319,z3,z4,z5,z6])],[(0,[z0,z2,z532,z3,z4,z5,z6]),(0,[z0,z533,z2,z3,z4,z5,z6])],[(0,[z534,z0,z2,z3,z4,z5,z6]),(0,[z535,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z536,z4,z5,z6]),(0,[z0,z138,z2,z3,z4,z5,z6]),(0,[z0,z2,z83,z3,z4,z6,z502])],[(0,[z121,z86,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z537,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z538]),(0,[z0,z2,z3,z539,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z540,z6])],[(0,[z0,z2,z47,z4,z5,z6,z32]),(0,[z0,z2,z3,z4,z507,z5,z6]),(0,[z11,z0,z2,z85,z3,z4,z6])],[(1,[z0,z173,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z541]),(1,[z212,z2,z3,z183,z5,z6]),(0,[z11,z0,z2,z3,z4,z216,z6]),(0,[z542,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z543,z3,z4,z5,z6]),(0,[z57,z0,z2,z458,z4,z5,z6]),(0,[z57,z0,z2,z3,z232,z5,z6]),(0,[z544,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z545]),(0,[z0,z2,z3,z4,z6,z48,z55])],[(0,[z0,z79,z27,z3,z4,z5,z6]),(0,[z86,z0,z2,z3,z131,z5,z6]),(0,[z0,z2,z3,z546,z4,z5,z6]),(0,[z0,z274,z2,z3,z4,z5,z6]),(0,[z152,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z547,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z433])]],
   [[(0,[z195,z0,z2,z83,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z548]),(1,[z0,z16,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z549,z5,z6])],[(0,[z550,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z119,z4,z5,z6]),(0,[z0,z2,z364,z3,z4,z5,z6]),(0,[z0,z2,z29,z3,z4,z5,z6])],[(0,[z0,z551,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z119,z4,z5,z6]),(0,[z0,z552,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z553]),(0,[z0,z2,z3,z554,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z555,z6]),(0,[z213,z0,z274,z3,z4,z5,z6]),(0,[z0,z61,z138,z3,z4,z5,z6]),(0,[z0,z2,z556,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z118,z6]),(0,[z557,z0,z2,z3,z4,z5,z6]),(0,[z0,z558,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z559,z6]),(0,[z0,z560,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z561,z5,z6]),(0,[z562,z0,z2,z3,z4,z5,z6]),(0,[z0,z61,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z6,z48,z396]),(0,[z329,z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z128,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z563]),(0,[z0,z2,z85,z4,z49,z5,z6]),(0,[z0,z2,z564,z3,z4,z5,z6]),(0,[z565,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z59,z0,z2,z83,z4,z5,z6]),(0,[z0,z2,z91,z3,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z5,z6]),(0,[z566,z0,z2,z3,z4,z5,z6])],[(0,[z0,z567,z2,z3,z4,z5,z6]),(0,[z86,z152,z2,z3,z4,z5,z6]),(0,[z0,z2,z323,z3,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z5,z6]),(0,[z0,z79,z2,z3,z4,z5,z70]),(0,[z568,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z110,z6])]],
   [[(0,[z0,z2,z569,z3,z4,z5,z6]),(0,[z0,z570,z2,z3,z4,z5,z6]),(0,[z0,z571,z2,z3,z4,z5,z6])],[(0,[z0,z2,z127,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z5,z165]),(0,[z0,z2,z3,z4,z572,z5,z6]),(0,[z0,z82,z2,z3,z4,z6,z48]),(0,[z0,z2,z573,z3,z4,z5,z6]),(1,[z574,z0,z2,z3,z4,z6]),(1,[z109,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z14,z4,z6,z48])],[(0,[z0,z2,z3,z4,z575,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z576]),(0,[z11,z0,z2,z24,z3,z4,z6]),(0,[z172,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z164,z6,z32]),(1,[z132,z0,z2,z4,z6,z32]),(0,[z0,z2,z577,z3,z4,z5,z6]),(1,[z11,z0,z2,z3,z252,z6])],[(0,[z578,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z323,z4,z5,z6]),(0,[z212,z2,z3,z183,z4,z5,z6])],[(0,[z0,z579,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z580]),(0,[z0,z2,z3,z4,z5,z58,z48]),(0,[z0,z2,z3,z4,z581,z5,z6]),(0,[z268,z0,z2,z3,z4,z6,z48])],[(0,[z0,z2,z3,z4,z5,z6,z582]),(1,[z0,z583,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z380,z5,z6]),(0,[z584,z0,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z47,z4,z6]),(0,[z11,z0,z2,z29,z3,z4,z6]),(0,[z0,z585,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z118,z49,z6]),(0,[z0,z2,z3,z4,z5,z6,z586]),(0,[z0,z2,z3,z4,z67,z6,z48]),(0,[z587,z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z6,z588]),(0,[z0,z2,z589,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z590]),(0,[z0,z2,z3,z4,z5,z591,z6])]],
   [[(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z593,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z77,z6]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z0,z2,z3,z594,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z595]),(0,[z10,z0,z68,z2,z3,z4,z5]),(0,[z0,z2,z24,z3,z4,z5,z48]),(0,[z0,z2,z3,z4,z596,z5,z6]),(0,[z0,z2,z3,z4,z597,z5,z6])],[(0,[z59,z2,z3,z119,z4,z5,z6]),(1,[z0,z214,z3,z4,z5,z6]),(0,[z0,z2,z85,z3,z4,z6,z48]),(0,[z109,z0,z2,z3,z5,z6,z41])],[(0,[z151,z0,z2,z3,z4,z5,z100]),(0,[z0,z2,z598,z3,z4,z5,z6]),(1,[z10,z0,z2,z3,z4,z48]),(1,[z0,z2,z3,z423,z5,z6])],[(1,[z0,z2,z3,z131,z5,z6]),(0,[z0,z599,z2,z3,z4,z5,z6]),(0,[z195,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z6,z320]),(0,[z0,z2,z94,z4,z140,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z600]),(0,[z283,z0,z2,z3,z4,z6,z48])],[(0,[z0,z2,z3,z284,z4,z6,z48]),(0,[z0,z2,z3,z23,z4,z5,z6])],[(1,[z278,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z100,z6,z48]),(0,[z57,z0,z2,z3,z4,z507,z6]),(0,[z0,z2,z601,z3,z4,z5,z6]),(0,[z0,z2,z267,z3,z4,z5,z6]),(1,[z11,z0,z2,z347,z4,z6])],[(0,[z0,z2,z3,z4,z602,z5,z6]),(0,[z603,z0,z2,z3,z4,z5,z6]),(0,[z11,z181,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z100,z48]),(0,[z0,z2,z3,z423,z5,z115,z6])],[(0,[z0,z2,z3,z4,z406,z5,z6]),(0,[z151,z0,z2,z3,z4,z6,z48]),(0,[z0,z604,z2,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z5,z58]),(1,[z10,z0,z2,z4,z5,z55]),(0,[z0,z2,z3,z118,z5,z6,z41]),(1,[z0,z2,z3,z4,z5,z479])]],
   [[(0,[z605,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z606,z6]),(0,[z0,z2,z3,z49,z5,z6,z22]),(0,[z0,z2,z3,z4,z5,z6,z325]),(0,[z294,z0,z2,z3,z4,z6,z48]),(1,[z0,z2,z347,z4,z5,z6])],[(0,[z0,z607,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z14,z4,z48])],[(0,[z0,z2,z3,z4,z5,z608,z6]),(0,[z0,z2,z3,z609,z4,z5,z6]),(0,[z151,z0,z2,z3,z327,z5,z6]),(0,[z0,z2,z3,z62,z4,z6,z48]),(0,[z0,z2,z94,z4,z5,z6,z32]),(0,[z610,z0,z2,z3,z4,z5,z6])],[(0,[z213,z0,z2,z3,z4,z5,z197]),(0,[z0,z2,z3,z4,z5,z165,z55]),(0,[z0,z2,z3,z4,z5,z6,z611]),(0,[z612,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z613,z5,z6])],[(0,[z0,z2,z3,z4,z614,z5,z6]),(0,[z0,z2,z3,z196,z4,z5,z6]),(1,[z0,z2,z3,z4,z233,z6]),(0,[z0,z2,z83,z4,z5,z6,z55]),(0,[z0,z474,z2,z3,z4,z5,z6]),(0,[z109,z0,z2,z3,z4,z5,z6])],[(0,[z0,z27,z3,z47,z4,z5,z6]),(0,[z0,z2,z3,z615,z4,z5,z6]),(0,[z181,z0,z2,z3,z4,z5,z6]),(0,[z616,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z617,z3,z4,z5,z6]),(0,[z0,z2,z618,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z619]),(0,[z0,z620,z2,z3,z4,z5,z6]),(0,[z0,z281,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z48,z70]),(0,[z0,z474,z2,z3,z4,z49,z5]),(0,[z0,z2,z3,z621,z4,z5,z6])],[(1,[z0,z179,z2,z3,z5,z6]),(0,[z0,z138,z3,z4,z216,z5,z6]),(0,[z0,z2,z83,z3,z14,z5,z6])]],
   [[(0,[z622,z0,z2,z3,z4,z5,z6]),(1,[z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z623,z5,z6]),(0,[z0,z2,z624,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z625,z5,z6]),(0,[z11,z0,z2,z3,z4,z252,z6])],[(0,[z11,z0,z2,z3,z252,z5,z6])],[(0,[z0,z2,z3,z4,z5,z626,z6]),(0,[z0,z2,z3,z4,z627,z5,z6]),(1,[z64,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z49,z6,z41]),(0,[z0,z2,z4,z5,z115,z6,z55]),(0,[z574,z0,z2,z3,z4,z115,z6]),(0,[z0,z628,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z14,z5,z67])],[(0,[z629,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z630,z3,z4,z5,z6]),(0,[z631,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z163,z3,z4,z5,z6]),(0,[z28,z11,z0,z2,z3,z4,z6]),(0,[z33,z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z632,z3,z4,z5,z6]),(0,[z0,z2,z85,z3,z4,z6,z32]),(0,[z10,z0,z2,z3,z4,z384,z6]),(0,[z0,z2,z24,z3,z4,z6,z48])],[(0,[z633,z0,z2,z3,z4,z5,z6]),(0,[z0,z634,z2,z3,z4,z5,z6]),(1,[z0,z88,z3,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6])],[(0,[z636,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z94,z24,z4,z5,z6])]],
   [[(0,[z637,z0,z2,z3,z4,z5,z6]),(0,[z0,z515,z2,z3,z5,z6,z70]),(1,[z0,z2,z3,z4,z6,z190]),(0,[z0,z2,z3,z638,z4,z5,z6]),(0,[z0,z2,z3,z4,z67,z6,z282]),(0,[z11,z0,z68,z2,z3,z4,z6])],[(0,[z0,z2,z3,z639,z4,z5,z6]),(0,[z0,z640,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z211,z5,z6]),(0,[z0,z641,z2,z3,z4,z5,z6]),(0,[z0,z16,z2,z3,z4,z6,z48])],[(0,[z0,z2,z3,z4,z642,z5,z6]),(0,[z0,z179,z2,z3,z4,z5,z6]),(0,[z2,z3,z183,z4,z128,z5,z6]),(0,[z0,z643,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z644,z4,z5,z6]),(0,[z186,z0,z2,z3,z5,z6,z41]),(1,[z0,z2,z3,z4,z477,z6])],[(0,[z0,z2,z3,z4,z645,z5,z6]),(0,[z213,z0,z2,z196,z4,z5,z6]),(0,[z0,z646,z2,z3,z4,z5,z6])],[(0,[z11,z0,z2,z27,z3,z4,z6]),(0,[z0,z515,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z6,z32])],[(0,[z329,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z112,z6]),(0,[z0,z2,z647,z3,z4,z5,z6]),(0,[z195,z11,z0,z2,z3,z4,z6]),(0,[z11,z0,z2,z3,z183,z4,z6]),(0,[z0,z319,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z58,z6,z70]),(0,[z0,z2,z3,z4,z5,z6,z648]),(0,[z11,z0,z2,z3,z4,z6,z41])],[(0,[z0,z2,z3,z4,z5,z6,z649])],[(0,[z181,z0,z2,z94,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z297]),(0,[z650,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z651]),(0,[z652,z0,z2,z3,z4,z5,z6]),(0,[z653,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z654,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z216,z6,z48]),(0,[z655,z0,z2,z3,z4,z5,z6]),(0,[z656,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z118,z5,z479]),(0,[z0,z2,z3,z4,z332,z6,z48])],[(0,[z0,z2,z3,z657,z4,z5,z6]),(0,[z0,z2,z85,z119,z4,z5,z6]),(0,[z212,z0,z2,z83,z3,z5,z6]),(0,[z213,z0,z2,z3,z406,z5,z6]),(1,[z213,z2,z3,z4,z134,z6]),(0,[z658,z0,z2,z3,z4,z5,z6]),(0,[z0,z369,z2,z3,z4,z6,z48])],[(0,[z0,z2,z3,z659,z4,z5,z6]),(0,[z0,z31,z3,z4,z78,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z660]),(0,[z0,z661,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z662,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z201,z6]),(0,[z0,z61,z2,z3,z128,z5,z6]),(0,[z663,z0,z2,z3,z4,z5,z6]),(0,[z213,z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z62,z5,z6,z104]),(1,[z652,z2,z3,z4,z5,z6]),(0,[z664,z0,z2,z3,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z5,z6])],[(0,[z665,z0,z2,z3,z4,z5,z6]),(0,[z44,z652,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z6,z70]),(0,[z0,z2,z4,z49,z5,z6,z32])],[(0,[z86,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z183,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z666]),(0,[z0,z2,z3,z667,z4,z5,z6]),(0,[z0,z2,z668,z3,z4,z5,z6]),(0,[z0,z669,z2,z3,z4,z5,z6])],[(0,[z0,z2,z25,z4,z5,z6,z32]),(0,[z0,z670,z2,z3,z4,z5,z6]),(0,[z0,z671,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z458,z4,z5,z6]),(1,[z57,z0,z3,z4,z5,z70]),(1,[z0,z2,z3,z4,z6,z502]),(0,[z0,z2,z3,z4,z5,z672,z6]),(0,[z109,z11,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z373,z4,z5,z6]),(0,[z0,z2,z3,z4,z673,z5,z6]),(0,[z587,z0,z2,z3,z4,z5,z6]),(0,[z0,z82,z2,z3,z140,z5,z6]),(0,[z388,z0,z2,z3,z4,z6,z48])]],
   [[(0,[z0,z31,z27,z3,z4,z5,z6]),(0,[z0,z583,z2,z3,z4,z5,z6]),(0,[z0,z2,z85,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z674,z5,z6]),(0,[z0,z2,z3,z14,z128,z5,z6]),(0,[z151,z0,z161,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z675]),(0,[z132,z0,z2,z3,z4,z6,z32]),(0,[z109,z0,z2,z3,z4,z5,z104]),(1,[z0,z2,z163,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z676]),(0,[z0,z2,z3,z4,z134,z6,z32]),(0,[z0,z31,z2,z3,z4,z6,z48]),(0,[z57,z0,z79,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z124,z70]),(0,[z0,z2,z3,z677,z4,z5,z6])],[(0,[z59,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z296,z6]),(0,[z0,z2,z3,z4,z678,z5,z6]),(0,[z574,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z48])],[(0,[z0,z2,z3,z4,z679,z5,z6]),(0,[z11,z0,z107,z2,z3,z4,z6]),(0,[z0,z680,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z681]),(0,[z0,z2,z682,z3,z4,z5,z6]),(0,[z11,z0,z68,z2,z3,z4,z5])],[(0,[z121,z11,z0,z2,z3,z4,z6]),(0,[z683,z0,z2,z3,z4,z5,z6]),(0,[z684,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z685,z3,z4,z5,z6]),(0,[z0,z2,z3,z686,z4,z5,z6]),(1,[z0,z2,z3,z5,z6,z264]),(0,[z125,z11,z0,z2,z3,z4,z6]),(1,[z0,z2,z3,z126,z5,z6])],[(0,[z107,z2,z27,z3,z4,z5,z6]),(0,[z687,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z275,z5,z6]),(0,[z0,z2,z85,z47,z4,z5,z6]),(0,[z0,z688,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z4,z5,z6])],[(0,[z0,z2,z436,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z119,z4,z6]),(0,[z689,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z690]),(0,[z0,z326,z2,z3,z4,z5,z6])],[(0,[z0,z82,z2,z3,z5,z6,z41])]],
   [[(0,[z181,z2,z25,z3,z4,z5,z6]),(0,[z11,z0,z16,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z691,z5,z6]),(0,[z109,z0,z2,z3,z4,z477,z6])],[(0,[z152,z2,z3,z4,z5,z100,z6]),(0,[z0,z692,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z216,z5,z6,z41]),(0,[z0,z2,z83,z3,z4,z296,z6]),(0,[z0,z2,z85,z3,z4,z49,z6]),(0,[z0,z693,z2,z3,z4,z5,z6])],[(0,[z59,z0,z583,z3,z4,z5,z6]),(0,[z0,z2,z694,z3,z4,z5,z6]),(0,[z0,z2,z3,z62,z65,z5,z6]),(1,[z0,z2,z3,z4,z5,z590]),(0,[z0,z2,z3,z4,z695,z5,z6]),(0,[z696,z0,z2,z3,z4,z5,z6]),(0,[z11,z186,z0,z2,z3,z4,z6])],[(0,[z697,z0,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z459,z6]),(0,[z0,z2,z3,z101,z4,z5,z6]),(0,[z44,z0,z2,z3,z4,z5,z590]),(0,[z0,z2,z698,z3,z4,z5,z6]),(0,[z0,z79,z2,z3,z4,z6,z48]),(1,[z11,z0,z2,z3,z126,z6])],[(0,[z0,z2,z3,z699,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z700]),(0,[z212,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z701,z5,z6]),(0,[z702,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z703,z3,z4,z5,z6])],[(0,[z121,z2,z27,z3,z4,z5,z6]),(1,[z0,z2,z364,z4,z5,z6]),(0,[z0,z2,z3,z65,z118,z5,z6]),(0,[z11,z0,z2,z475,z3,z4,z6])],[(0,[z44,z0,z31,z3,z4,z5,z6]),(0,[z57,z11,z0,z2,z3,z4,z6]),(0,[z0,z2,z83,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z5,z6,z704]),(0,[z11,z0,z2,z3,z4,z5,z48])],[(0,[z0,z17,z29,z3,z4,z5,z6]),(0,[z11,z0,z17,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z78,z5,z6]),(0,[z0,z2,z3,z4,z140,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z705]),(0,[z0,z2,z3,z706,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z4,z231,z707]),(0,[z0,z61,z3,z160,z5,z6]),(0,[z0,z2,z21,z4,z5,z165]),(0,[z708,z0,z2,z3,z4,z6])],[(0,[z278,z250,z2,z3,z4,z6]),(0,[z0,z161,z3,z327,z5,z6]),(0,[z11,z0,z2,z3,z423,z6])],[(0,[z0,z2,z709,z4,z5,z6]),(0,[z562,z0,z2,z3,z6,z41]),(0,[z0,z2,z3,z14,z216,z48]),(0,[z44,z0,z475,z3,z4,z6]),(0,[z0,z2,z3,z4,z48,z70]),(0,[z0,z2,z3,z4,z118,z433]),(0,[z109,z0,z2,z3,z4,z282])],[(0,[z0,z2,z3,z4,z710,z6]),(0,[z0,z2,z3,z4,z6,z711]),(0,[z0,z2,z3,z712,z5,z6]),(0,[z0,z2,z4,z5,z6,z713]),(0,[z2,z3,z4,z164,z714,z6]),(1,[z2,z3,z4,z5,z715])],[(0,[z2,z25,z716,z4,z5,z6])],[(0,[z0,z2,z83,z330,z5,z6]),(0,[z0,z717,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z718]),(0,[z0,z31,z3,z4,z6,z404]),(0,[z0,z2,z3,z719,z5,z6]),(0,[z0,z2,z3,z4,z720,z6])],[(0,[z0,z2,z4,z5,z6,z721]),(0,[z0,z2,z3,z4,z5,z722]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z724,z5,z6])],[(0,[z2,z3,z4,z100,z48,z165]),(0,[z0,z2,z703,z3,z4,z48])],[(0,[z0,z2,z3,z373,z5,z241]),(0,[z0,z2,z3,z4,z241,z725]),(0,[z622,z0,z2,z3,z4,z48]),(0,[z726,z2,z3,z4,z5,z6]),(0,[z0,z2,z727,z4,z5,z6]),(0,[z0,z2,z83,z5,z6,z522])],[(0,[z0,z2,z3,z348,z6,z48]),(0,[z0,z2,z3,z4,z5,z728]),(0,[z0,z2,z3,z4,z477,z6]),(0,[z109,z11,z0,z2,z3,z104]),(0,[z0,z2,z3,z729,z5,z6])],[(0,[z0,z2,z3,z87,z5,z6]),(0,[z0,z2,z364,z4,z5,z297]),(0,[z0,z2,z3,z4,z730,z6]),(0,[z0,z515,z2,z3,z6,z48])],[(0,[z44,z0,z3,z4,z235,z108]),(0,[z0,z731,z2,z3,z5,z6])],[(0,[z11,z250,z2,z3,z4,z6]),(0,[z0,z2,z3,z732,z384,z6])],[(0,[z121,z27,z3,z4,z5,z6]),(0,[z81,z2,z3,z4,z164,z6]),(0,[z57,z0,z3,z5,z124,z70]),(0,[z33,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z733,z5,z6]),(0,[z0,z2,z3,z118,z6,z734]),(0,[z308,z0,z2,z3,z65,z6])],[(0,[z0,z2,z3,z4,z5,z297]),(0,[z11,z0,z16,z47,z4,z6])],[(0,[z0,z2,z3,z4,z5,z735]),(0,[z0,z515,z27,z3,z5,z6])]],
   [[],[(0,[z0,z2,z3,z736,z5,z6]),(0,[z0,z2,z3,z6,z48,z737])],[(0,[z652,z2,z3,z4,z5,z6]),(0,[z2,z738,z3,z4,z5,z6]),(0,[z0,z739,z3,z4,z5,z6]),(0,[z0,z2,z3,z66,z118,z6])],[],[(0,[z605,z2,z3,z183,z5,z6]),(0,[z0,z2,z740,z4,z5,z6]),(0,[z0,z741,z3,z4,z5,z6])],[(0,[z0,z2,z21,z4,z459,z6])],[(0,[z0,z2,z3,z4,z341,z48]),(0,[z0,z2,z3,z4,z6,z742]),(0,[z0,z2,z145,z4,z49,z6])],[(0,[z81,z214,z3,z4,z5,z6]),(0,[z0,z593,z2,z3,z4,z48]),(0,[z0,z2,z3,z211,z77,z6]),(0,[z0,z2,z4,z5,z6,z743])],[(0,[z11,z0,z2,z744,z4,z6])],[(0,[z0,z2,z3,z4,z745,z6]),(0,[z11,z0,z281,z2,z3,z4])],[(0,[z0,z61,z2,z323,z5,z6]),(0,[z0,z2,z3,z746,z5,z6]),(0,[z10,z11,z0,z2,z4,z55])],[(0,[z0,z2,z747,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z748]),(0,[z0,z2,z3,z749,z5,z6]),(0,[z0,z2,z3,z750,z5,z6]),(0,[z0,z2,z3,z62,z14,z48]),(0,[z0,z751,z3,z4,z5,z6])],[(0,[z195,z2,z323,z128,z5,z6]),(0,[z752,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z296,z753])],[(0,[z0,z82,z2,z546,z5,z6]),(0,[z0,z754,z2,z3,z5,z6])],[(0,[z198,z0,z2,z4,z6,z32])],[(0,[z0,z583,z3,z4,z201,z6]),(0,[z11,z0,z755,z3,z4,z6])]],
   [[(0,[z574,z0,z2,z3,z6,z264])],[(0,[z0,z2,z24,z4,z5,z555]),(0,[z96,z2,z3,z128,z5,z6]),(0,[z0,z2,z3,z4,z5,z590]),(0,[z0,z756,z2,z3,z5,z6]),(0,[z11,z0,z515,z2,z3,z6]),(0,[z0,z2,z3,z4,z613,z48])],[(0,[z0,z2,z757,z4,z5,z6]),(0,[z0,z2,z83,z380,z5,z6]),(0,[z0,z758,z3,z4,z5,z6]),(0,[z0,z138,z2,z323,z5,z6]),(0,[z0,z102,z2,z3,z6,z48]),(0,[z0,z2,z3,z4,z276,z48]),(0,[z0,z2,z129,z4,z233,z6]),(0,[z11,z0,z2,z3,z126,z6])],[(0,[z11,z0,z2,z3,z4,z48])],[(0,[z0,z2,z759,z4,z5,z6]),(0,[z0,z2,z83,z596,z5,z6]),(0,[z192,z0,z3,z4,z6,z219])],[(0,[z0,z2,z196,z4,z134,z6]),(0,[z760,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z38,z4,z6]),(0,[z0,z2,z3,z4,z761,z6])],[(0,[z0,z2,z3,z762,z5,z6]),(0,[z0,z2,z3,z4,z763,z6]),(0,[z764,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z765]),(0,[z11,z0,z2,z3,z4,z448]),(0,[z11,z766,z2,z3,z4,z6])],[(0,[z81,z2,z3,z4,z304,z6]),(0,[z11,z0,z583,z3,z4,z6])],[(0,[z59,z2,z119,z380,z5,z6]),(0,[z0,z2,z3,z4,z5,z767]),(0,[z0,z2,z163,z14,z5,z6]),(0,[z0,z768,z3,z4,z6,z48])],[(0,[z0,z31,z2,z196,z4,z6]),(0,[z0,z2,z769,z3,z5,z6]),(0,[z0,z2,z3,z4,z338,z48]),(0,[z0,z2,z3,z423,z6,z48])],[(0,[z0,z2,z3,z4,z425,z48]),(0,[z0,z2,z770,z4,z5,z6]),(1,[z0,z2,z3,z5,z771]),(0,[z109,z0,z2,z3,z284,z48])],[(0,[z0,z2,z3,z4,z240,z48]),(0,[z151,z2,z3,z4,z5,z165]),(0,[z0,z772,z3,z4,z5,z6]),(0,[z0,z281,z2,z4,z5,z177]),(0,[z125,z0,z2,z3,z4,z479]),(0,[z11,z0,z68,z2,z347,z4])],[(0,[z0,z319,z3,z4,z459,z6])],[(0,[z86,z2,z3,z4,z48,z165]),(0,[z0,z2,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z773]),(0,[z0,z2,z24,z4,z332,z48]),(0,[z33,z0,z2,z23,z4,z6])],[(0,[z0,z2,z3,z4,z774,z6]),(0,[z0,z775,z3,z4,z5,z6]),(0,[z0,z2,z3,z48,z124,z70])]],
   [[(0,[z0,z2,z776,z4,z5,z6]),(0,[z0,z2,z3,z777,z5,z6]),(0,[z0,z424,z3,z4,z5,z58])],[(0,[z0,z274,z3,z4,z5,z6]),(0,[z0,z778,z3,z4,z5,z6]),(0,[z0,z779,z2,z3,z4,z5]),(0,[z245,z2,z3,z128,z5,z6]),(0,[z0,z693,z3,z62,z5,z6])],[],[(0,[z0,z2,z3,z4,z780,z6]),(0,[z44,z0,z2,z23,z4,z6]),(0,[z132,z0,z2,z4,z6,z743])],[(0,[z0,z2,z781,z4,z5,z6]),(0,[z2,z716,z119,z4,z5,z6]),(0,[z0,z2,z3,z782,z5,z6]),(0,[z11,z0,z2,z3,z783,z6])],[(0,[z278,z81,z2,z3,z4,z6]),(0,[z11,z0,z2,z21,z4,z6])],[(0,[z0,z2,z3,z4,z784,z6]),(0,[z0,z2,z3,z373,z112,z6]),(0,[z0,z2,z3,z222,z4,z48]),(0,[z0,z2,z3,z4,z433,z41])],[(0,[z0,z2,z3,z785,z5,z6]),(0,[z0,z2,z786,z3,z5,z6]),(0,[z0,z31,z3,z4,z78,z6]),(0,[z0,z2,z3,z787,z5,z6]),(0,[z0,z788,z2,z3,z5,z6]),(0,[z64,z0,z68,z2,z3,z4])],[(0,[z0,z2,z3,z4,z5,z789])],[(0,[z213,z2,z3,z4,z134,z297]),(0,[z0,z2,z21,z4,z77,z6]),(0,[z11,z0,z79,z3,z4,z58]),(0,[z0,z2,z4,z5,z606,z55])],[(0,[z0,z2,z3,z790,z5,z6]),(0,[z0,z2,z791,z4,z5,z6]),(0,[z0,z2,z347,z252,z5,z6])],[(0,[z11,z0,z2,z3,z4,z231]),(0,[z792,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z793]),(0,[z0,z68,z2,z3,z4,z384]),(0,[z0,z2,z3,z187,z4,z48])],[(0,[z0,z2,z3,z5,z6,z794]),(0,[z57,z0,z129,z4,z5,z70])],[(0,[z0,z2,z323,z5,z6,z104]),(0,[z0,z2,z3,z795,z5,z6])],[(0,[z0,z796,z3,z4,z5,z6]),(0,[z684,z0,z2,z3,z6,z41]),(1,[z0,z2,z3,z4,z797]),(0,[z0,z138,z3,z667,z5,z6])],[(0,[z0,z2,z3,z798,z5,z6]),(0,[z44,z0,z214,z3,z4,z6]),(0,[z0,z2,z3,z6,z12,z264]),(0,[z0,z2,z3,z126,z5,z48])]],
   [[(0,[z117,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z799,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z797]),(0,[z0,z2,z3,z800,z5,z6]),(0,[z0,z2,z3,z783,z5,z6])],[(0,[z0,z2,z3,z4,z5,z801]),(0,[z0,z68,z802,z2,z3,z4])],[(0,[z212,z2,z3,z803,z5,z6]),(0,[z0,z2,z458,z232,z5,z6]),(0,[z0,z2,z3,z4,z529,z48]),(0,[z11,z0,z2,z23,z4,z6])],[(0,[z278,z0,z214,z3,z4,z6]),(0,[z0,z2,z3,z804,z5,z6]),(0,[z0,z2,z3,z275,z5,z297]),(0,[z10,z0,z2,z4,z5,z19]),(0,[z0,z2,z3,z4,z48,z71])],[(0,[z0,z2,z3,z5,z6,z805]),(0,[z806,z0,z2,z3,z4,z6]),(0,[z109,z0,z2,z3,z5,z104])],[(0,[z152,z2,z3,z4,z5,z715]),(0,[z0,z2,z3,z135,z5,z6]),(0,[z0,z2,z3,z65,z110,z6])],[(0,[z0,z2,z3,z4,z112,z231]),(0,[z0,z2,z3,z4,z5,z807]),(0,[z0,z2,z3,z4,z6,z734]),(0,[z808,z2,z3,z4,z6,z48])],[(0,[z11,z0,z2,z3,z135,z6])],[(0,[z0,z2,z91,z4,z77,z6]),(0,[z0,z3,z4,z5,z6,z809])],[(0,[z349,z2,z3,z4,z5,z6]),(0,[z0,z810,z2,z3,z4,z5]),(0,[z0,z2,z3,z811,z5,z6]),(0,[z11,z652,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z393,z48]),(0,[z308,z0,z2,z3,z14,z67])],[(0,[z0,z2,z323,z65,z5,z6]),(0,[z234,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z30,z6,z812]),(0,[z0,z515,z2,z3,z4,z48]),(0,[z0,z2,z770,z3,z5,z6]),(0,[z308,z0,z2,z163,z4,z6])],[(0,[z0,z2,z155,z4,z5,z6]),(0,[z109,z0,z2,z3,z597,z5]),(0,[z0,z2,z3,z284,z51,z6])],[(0,[z0,z82,z2,z94,z6,z48]),(0,[z0,z3,z4,z6,z48,z809])],[(0,[z0,z2,z3,z813,z5,z6]),(0,[z0,z2,z3,z4,z814,z6]),(0,[z0,z107,z3,z4,z48,z70]),(0,[z0,z2,z815,z4,z5,z6]),(0,[z213,z326,z2,z3,z4,z6]),(0,[z151,z2,z3,z211,z5,z165]),(0,[z0,z2,z129,z4,z5,z6]),(0,[z11,z349,z2,z3,z4,z6]),(0,[z11,z0,z2,z816,z4,z6])]],
   [[(0,[z11,z0,z214,z3,z4,z6]),(0,[z0,z755,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z817,z6]),(0,[z652,z2,z3,z4,z5,z235])],[(0,[z234,z0,z2,z4,z5,z55]),(0,[z11,z0,z2,z3,z252,z48])],[(0,[z0,z31,z3,z4,z642,z6]),(0,[z0,z2,z3,z373,z5,z6]),(0,[z818,z2,z3,z4,z5,z6]),(0,[z0,z2,z819,z4,z6,z48])],[(0,[z0,z2,z820,z4,z5,z6]),(0,[z0,z2,z13,z3,z4,z48])],[(0,[z766,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z126,z6,z48]),(1,[z0,z2,z23,z252,z6])],[],[(0,[z358,z27,z3,z4,z5,z6]),(0,[z0,z2,z821,z4,z5,z6]),(0,[z0,z138,z3,z43,z5,z6]),(0,[z117,z2,z3,z4,z233,z6]),(0,[z0,z2,z83,z695,z5,z6]),(0,[z0,z2,z3,z4,z384,z6])],[(0,[z0,z107,z3,z87,z5,z6]),(0,[z0,z2,z3,z4,z6,z797])],[(1,[z2,z3,z803,z5,z6]),(0,[z212,z2,z3,z183,z6,z48]),(0,[z81,z2,z3,z4,z6,z35])],[(0,[z0,z2,z196,z4,z5,z6]),(0,[z0,z2,z3,z199,z5,z6]),(0,[z0,z2,z3,z5,z67,z511]),(0,[z11,z0,z2,z4,z6,z177])],[(0,[z121,z738,z3,z4,z5,z6]),(0,[z11,z212,z2,z3,z183,z6]),(0,[z0,z2,z196,z4,z164,z6]),(0,[z0,z822,z2,z3,z4,z30]),(0,[z823,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z6,z824]),(0,[z0,z2,z3,z4,z591,z48]),(0,[z120,z0,z2,z3,z126,z6])],[(0,[z0,z16,z47,z4,z6,z48]),(0,[z0,z2,z83,z140,z5,z6])],[(0,[z0,z2,z323,z380,z5,z6]),(0,[z213,z274,z3,z4,z134,z6]),(0,[z0,z2,z458,z4,z507,z6]),(0,[z0,z2,z3,z232,z507,z6])],[(0,[z0,z2,z825,z3,z5,z6]),(0,[z0,z2,z364,z4,z6,z48]),(0,[z116,z0,z2,z826,z4,z6]),(0,[z0,z61,z3,z5,z6,z105])],[(0,[z0,z583,z3,z380,z5,z6]),(0,[z0,z827,z3,z4,z5,z6])],[(0,[z59,z179,z2,z119,z5,z6]),(0,[z0,z2,z3,z4,z441,z48]),(0,[z0,z2,z3,z406,z5,z6]),(0,[z0,z2,z3,z4,z6,z828]),(0,[z0,z2,z145,z5,z6,z41])]],
   [[(0,[z0,z2,z3,z829,z5,z6]),(0,[z0,z2,z3,z4,z479,z32])],[(0,[z0,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z6,z830]),(0,[z81,z2,z543,z3,z4,z6]),(0,[z0,z2,z3,z831,z5,z6]),(0,[z349,z2,z3,z4,z233,z6]),(0,[z0,z79,z3,z4,z58,z190]),(0,[z0,z2,z3,z4,z832,z6]),(0,[z0,z2,z3,z66,z5,z433]),(0,[z11,z0,z2,z833,z4,z6])],[],[(0,[z0,z2,z834,z3,z5,z6]),(0,[z0,z835,z3,z4,z5,z6]),(0,[z0,z102,z2,z3,z5,z6]),(0,[z250,z2,z3,z4,z5,z590]),(0,[z0,z2,z423,z5,z6,z55])],[(0,[z0,z2,z836,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z231]),(0,[z0,z2,z3,z360,z4,z48]),(0,[z0,z2,z3,z327,z5,z6]),(0,[z0,z214,z196,z4,z5,z6]),(0,[z0,z2,z569,z3,z4,z48]),(0,[z0,z2,z3,z4,z452,z48]),(0,[z0,z2,z4,z5,z837,z55])],[(0,[z0,z2,z27,z3,z4,z838]),(0,[z57,z349,z3,z4,z5,z70])],[(0,[z0,z839,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z6,z840])],[(0,[z0,z2,z3,z4,z841,z6]),(0,[z44,z0,z3,z4,z6,z824]),(0,[z10,z0,z2,z4,z384,z55]),(0,[z11,z0,z2,z3,z842,z6])],[(0,[z0,z2,z3,z4,z843,z6]),(0,[z0,z2,z844,z4,z5,z6]),(0,[z0,z2,z3,z4,z845,z6])],[(0,[z0,z2,z846,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z297]),(0,[z0,z2,z4,z5,z6,z847]),(0,[z64,z0,z2,z3,z4,z48]),(0,[z0,z2,z4,z296,z6,z32]),(0,[z0,z2,z3,z4,z848,z6])],[(0,[z0,z2,z3,z4,z5,z849]),(0,[z0,z214,z3,z406,z5,z6]),(0,[z0,z2,z3,z850,z5,z6]),(0,[z0,z2,z145,z4,z5,z6])],[(0,[z0,z2,z3,z4,z851,z6]),(0,[z86,z579,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z4,z479])],[(0,[z852,z0,z2,z3,z4,z6]),(0,[z0,z214,z3,z4,z6,z48]),(0,[z0,z2,z853,z4,z5,z6]),(0,[z0,z2,z38,z4,z5,z235])],[(0,[z0,z2,z3,z854,z5,z6]),(0,[z11,z0,z2,z3,z131,z6]),(0,[z0,z2,z3,z4,z6,z855]),(0,[z0,z474,z2,z4,z5,z32]),(0,[z856,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z857,z5,z6]),(0,[z0,z2,z3,z4,z626,z48]),(0,[z0,z2,z3,z4,z6,z858])],[(0,[z0,z2,z3,z4,z859,z6]),(0,[z860,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z199,z233,z6])]],
   [[(0,[z0,z2,z3,z4,z861,z6]),(0,[z0,z274,z364,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z862]),(0,[z250,z2,z38,z4,z5,z6])],[(0,[z0,z2,z3,z4,z863,z6]),(0,[z151,z2,z21,z4,z5,z165]),(0,[z0,z2,z3,z4,z864,z6]),(0,[z865,z0,z2,z3,z4,z48])],[(0,[z0,z88,z3,z373,z5,z6]),(0,[z11,z0,z2,z3,z4,z241]),(0,[z0,z3,z4,z6,z824,z108]),(0,[z432,z0,z2,z83,z5,z6]),(0,[z11,z0,z2,z23,z252,z6])],[(0,[z81,z0,z2,z3,z4,z590]),(0,[z0,z2,z3,z4,z5,z866])],[(0,[z0,z2,z867,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z868])],[(0,[z116,z0,z68,z2,z3,z4]),(0,[z0,z2,z3,z296,z6,z41])],[(0,[z0,z2,z3,z869,z4,z6]),(0,[z186,z0,z2,z3,z252,z6])],[(0,[z870,z0,z2,z3,z4,z6]),(0,[z0,z474,z2,z3,z4,z384]),(0,[z0,z2,z3,z871,z5,z6])],[(0,[z27,z3,z4,z5,z6,z341]),(0,[z0,z88,z3,z4,z5,z241]),(0,[z0,z872,z3,z4,z5,z6])],[(0,[z0,z873,z3,z4,z5,z6]),(0,[z874,z2,z3,z4,z5,z6]),(0,[z0,z2,z85,z4,z49,z6])],[(0,[z0,z179,z2,z3,z6,z48]),(0,[z0,z2,z3,z14,z128,z48]),(0,[z116,z0,z2,z3,z850,z6]),(0,[z0,z2,z3,z4,z48,z248]),(0,[z0,z2,z38,z4,z30,z6]),(0,[z0,z2,z3,z4,z6,z875]),(0,[z11,z0,z2,z3,z876,z6])],[(0,[z59,z2,z618,z4,z5,z6]),(0,[z0,z2,z877,z4,z110,z6])],[(0,[z0,z2,z878,z4,z5,z6]),(0,[z120,z0,z2,z23,z4,z6])],[(0,[z59,z583,z119,z4,z5,z6]),(0,[z0,z2,z685,z4,z49,z6]),(0,[z0,z474,z2,z3,z4,z5])],[],[(0,[z0,z2,z3,z4,z112,z241]),(0,[z0,z2,z3,z65,z645,z6]),(0,[z64,z0,z79,z3,z4,z58])]],
   [[(0,[z212,z0,z2,z323,z5,z6]),(0,[z0,z82,z2,z5,z6,z449])],[(0,[z0,z88,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z6,z879]),(0,[z0,z2,z85,z4,z384,z6])],[(0,[z0,z161,z3,z4,z5,z6]),(0,[z0,z2,z3,z880,z5,z6]),(0,[z0,z2,z881,z4,z5,z6]),(0,[z0,z882,z2,z3,z5,z6]),(0,[z151,z2,z91,z4,z5,z165]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z186,z0,z2,z3,z6,z41])],[(0,[z0,z2,z3,z884,z5,z6]),(0,[z0,z2,z3,z4,z885,z6]),(0,[z11,z0,z2,z323,z4,z6]),(0,[z0,z886,z2,z3,z4,z5]),(0,[z109,z0,z2,z3,z48,z41]),(0,[z0,z887,z3,z4,z5,z6])],[(0,[z0,z138,z3,z402,z5,z6]),(0,[z0,z2,z888,z4,z5,z6]),(0,[z0,z88,z3,z4,z5,z231]),(0,[z213,z2,z196,z4,z134,z6]),(0,[z0,z2,z3,z211,z6,z48]),(0,[z530,z2,z3,z4,z5,z100]),(0,[z0,z2,z3,z889,z5,z6])],[(0,[z890,z0,z2,z3,z4,z5]),(0,[z11,z0,z88,z3,z4,z6]),(0,[z0,z2,z3,z4,z891,z6]),(0,[z0,z2,z3,z4,z6,z892]),(0,[z0,z2,z3,z135,z5,z235]),(0,[z11,z0,z2,z458,z4,z6])],[(0,[z121,z11,z27,z3,z4,z6]),(0,[z314,z0,z2,z3,z4,z48]),(0,[z0,z173,z83,z3,z5,z6]),(0,[z0,z2,z893,z4,z5,z6]),(0,[z0,z281,z2,z3,z5,z41]),(0,[z0,z2,z3,z4,z5,z771]),(0,[z0,z2,z894,z4,z6,z48])],[(0,[z81,z250,z2,z3,z4,z6])],[(0,[z132,z0,z2,z3,z4,z433]),(0,[z0,z2,z494,z3,z4,z48]),(0,[z308,z0,z2,z4,z6,z325])],[(0,[z0,z2,z3,z895,z5,z6]),(0,[z250,z2,z3,z135,z5,z6]),(0,[z57,z0,z3,z199,z5,z70]),(0,[z10,z0,z2,z4,z48,z355])],[(0,[z0,z2,z896,z4,z5,z6]),(0,[z213,z2,z3,z406,z134,z6]),(0,[z897,z2,z3,z4,z5,z6])],[(0,[z314,z0,z2,z4,z5,z55]),(0,[z109,z0,z61,z2,z3,z48]),(0,[z0,z2,z155,z4,z5,z235]),(0,[z0,z2,z83,z140,z6,z502]),(0,[z0,z474,z2,z3,z5,z22]),(0,[z0,z898,z3,z4,z6,z48])],[(0,[z0,z2,z3,z4,z899,z5]),(0,[z195,z0,z2,z323,z5,z6])],[(0,[z0,z2,z900,z4,z5,z6]),(0,[z0,z2,z3,z348,z5,z6]),(0,[z283,z0,z2,z3,z14,z48])],[(0,[z121,z436,z27,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z901]),(0,[z0,z2,z3,z4,z30,z797]),(0,[z0,z515,z2,z3,z5,z6]),(0,[z11,z902,z2,z3,z4,z6])],[(0,[z903,z0,z2,z3,z4,z241]),(0,[z0,z2,z904,z4,z5,z6]),(0,[z250,z2,z155,z4,z5,z6]),(0,[z0,z2,z83,z140,z296,z6]),(0,[z0,z2,z4,z5,z6,z905]),(0,[z0,z2,z3,z4,z479,z48])]],
   [[(0,[z0,z2,z196,z275,z5,z6]),(0,[z176,z0,z2,z3,z4,z48])],[(0,[z181,z0,z2,z20,z5,z6]),(0,[z229,z2,z25,z4,z5,z6]),(0,[z172,z2,z3,z4,z164,z6]),(0,[z0,z2,z3,z906,z5,z6])],[(0,[z702,z27,z3,z4,z5,z6]),(0,[z278,z0,z31,z3,z4,z6]),(0,[z2,z3,z183,z803,z5,z6])],[(0,[z195,z2,z3,z803,z5,z6]),(0,[z0,z2,z3,z4,z492,z48]),(0,[z907,z0,z2,z3,z4,z6]),(0,[z0,z79,z3,z4,z5,z58]),(0,[z0,z2,z163,z4,z6,z48]),(0,[z0,z2,z908,z4,z6,z48])],[(0,[z0,z2,z3,z14,z5,z525]),(0,[z0,z319,z3,z4,z77,z6]),(0,[z0,z2,z83,z217,z5,z6]),(0,[z0,z474,z2,z85,z4,z5])],[(0,[z0,z909,z3,z4,z5,z6]),(0,[z0,z2,z85,z4,z623,z6]),(0,[z0,z2,z323,z140,z5,z6]),(0,[z0,z2,z3,z4,z910,z6])],[(0,[z612,z27,z3,z4,z5,z6]),(0,[z152,z2,z3,z4,z5,z626]),(0,[z0,z2,z3,z4,z201,z231]),(0,[z0,z2,z3,z4,z911,z6]),(0,[z0,z2,z85,z423,z5,z6]),(0,[z0,z2,z3,z5,z433,z22]),(0,[z0,z2,z3,z126,z4,z48])],[(0,[z0,z912,z2,z3,z4,z5]),(0,[z0,z31,z2,z3,z4,z197]),(0,[z0,z2,z3,z913,z5,z6]),(0,[z0,z2,z65,z118,z6,z177])],[(0,[z81,z31,z27,z3,z4,z6]),(0,[z0,z2,z3,z275,z6,z48]),(0,[z0,z2,z3,z4,z48,z165]),(0,[z366,z0,z2,z3,z5,z104]),(0,[z0,z2,z4,z5,z6,z325]),(0,[z0,z669,z2,z3,z4,z48])],[(0,[z0,z2,z3,z4,z5,z914])],[(0,[z116,z0,z2,z3,z915,z6]),(0,[z0,z2,z916,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z241]),(0,[z0,z2,z3,z732,z5,z6])],[(0,[z0,z2,z3,z4,z5,z917]),(0,[z0,z2,z3,z4,z6,z918]),(0,[z0,z2,z3,z4,z919,z6]),(0,[z0,z3,z4,z5,z6,z824]),(0,[z0,z2,z4,z6,z48,z325])],[(0,[z0,z2,z920,z4,z5,z6]),(0,[z0,z2,z3,z4,z673,z48]),(1,[z0,z2,z770,z5,z6]),(0,[z0,z2,z3,z921,z5,z6])],[(0,[z0,z2,z364,z406,z5,z6]),(0,[z0,z2,z922,z4,z5,z6]),(0,[z0,z2,z145,z4,z296,z6])],[(0,[z151,z11,z2,z3,z4,z165])]],
   [[(0,[z11,z181,z2,z25,z4,z6]),(0,[z923,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z915,z5,z6]),(0,[z0,z2,z3,z4,z6,z924]),(0,[z0,z2,z3,z4,z6,z925])],[(0,[z0,z2,z21,z4,z5,z100]),(0,[z0,z2,z3,z4,z5,z926]),(0,[z0,z2,z3,z4,z48,z526]),(0,[z209,z0,z2,z347,z4,z6])],[(0,[z0,z2,z3,z4,z48,z365])],[(0,[z0,z2,z3,z4,z927,z6]),(0,[z195,z11,z2,z3,z128,z6]),(0,[z0,z2,z3,z4,z6,z928]),(0,[z0,z929,z3,z4,z5,z6]),(0,[z250,z2,z3,z4,z6,z48]),(0,[z930,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z931,z6])],[(0,[z0,z2,z24,z423,z5,z6]),(0,[z0,z2,z932,z4,z5,z6])],[(0,[z0,z161,z3,z211,z5,z6])],[(0,[z0,z2,z21,z4,z6,z48]),(0,[z0,z2,z933,z4,z5,z6]),(0,[z934,z2,z3,z4,z5,z6]),(0,[z0,z2,z816,z4,z5,z6])],[(0,[z0,z2,z20,z5,z6,z32]),(0,[z116,z0,z2,z3,z4,z48]),(0,[z0,z935,z3,z4,z5,z6]),(0,[z936,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z937,z5,z6]),(0,[z0,z2,z3,z4,z237,z48])],[(0,[z0,z2,z21,z327,z5,z6]),(0,[z0,z2,z3,z5,z6,z938]),(0,[z0,z2,z3,z65,z6,z734])],[(0,[z0,z2,z3,z939,z5,z6]),(0,[z2,z3,z4,z714,z134,z6]),(0,[z161,z3,z4,z5,z6,z165])],[(0,[z0,z274,z3,z275,z5,z6]),(0,[z0,z2,z940,z4,z5,z6])],[(0,[z0,z2,z3,z941,z5,z6]),(0,[z0,z2,z3,z4,z942,z6])],[(0,[z0,z738,z3,z4,z5,z6]),(0,[z0,z2,z94,z4,z5,z241]),(0,[z0,z2,z943,z4,z5,z6]),(0,[z0,z2,z3,z14,z67,z282]),(0,[z0,z768,z3,z4,z5,z6])],[(0,[z44,z0,z38,z4,z6,z108]),(0,[z0,z2,z3,z423,z5,z6]),(0,[z10,z0,z2,z3,z4,z48])],[(0,[z0,z2,z944,z4,z5,z6]),(0,[z0,z2,z3,z14,z183,z48]),(0,[z0,z2,z3,z4,z6,z320]),(0,[z0,z369,z3,z4,z6,z404])]],
   [[(0,[z0,z474,z2,z3,z66,z5])],[(0,[z278,z0,z2,z3,z4,z6]),(0,[z0,z2,z945,z4,z5,z6]),(0,[z0,z946,z2,z3,z4,z5]),(0,[z44,z652,z3,z4,z6,z108])],[(0,[z0,z2,z3,z947,z5,z6]),(0,[z0,z948,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z714,z6]),(0,[z949,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z950,z6]),(0,[z0,z61,z3,z62,z6,z48]),(0,[z0,z2,z475,z3,z4,z48])],[(0,[z0,z2,z3,z951,z4,z5]),(0,[z0,z2,z3,z4,z952,z6]),(1,[z0,z3,z4,z5,z728]),(0,[z10,z0,z2,z4,z5,z55])],[(0,[z11,z0,z2,z83,z140,z6]),(0,[z109,z0,z2,z3,z167,z5])],[(0,[z0,z2,z953,z4,z5,z6]),(0,[z0,z954,z3,z4,z5,z6]),(0,[z44,z250,z3,z4,z6,z108]),(0,[z44,z0,z3,z4,z590,z108])],[(0,[z0,z2,z955,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z236])],[(0,[z278,z121,z27,z3,z4,z6]),(0,[z956,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z5,z6,z957]),(0,[z2,z3,z4,z803,z5,z6]),(0,[z0,z2,z91,z4,z6,z48]),(0,[z0,z2,z101,z5,z6,z32]),(0,[z250,z2,z3,z4,z6,z32]),(0,[z0,z802,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z2,z3,z252,z6,z32])],[(0,[z59,z11,z2,z119,z4,z6]),(0,[z0,z2,z3,z959,z5,z6]),(0,[z0,z2,z3,z5,z6,z960]),(0,[z0,z2,z3,z4,z6,z961]),(0,[z0,z2,z85,z4,z332,z6])],[(0,[z0,z2,z25,z4,z201,z6]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z963,z6]),(0,[z0,z2,z91,z327,z5,z6]),(0,[z11,z0,z2,z3,z327,z6]),(0,[z0,z2,z24,z3,z4,z48])],[(0,[z0,z2,z3,z964,z5,z6]),(0,[z0,z2,z3,z4,z965,z6])],[(0,[z11,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z48,z595])],[(0,[z0,z2,z966,z4,z5,z6])],[(0,[z0,z319,z3,z4,z6,z48]),(0,[z0,z967,z2,z3,z5,z6]),(0,[z0,z2,z3,z65,z118,z479])],[(0,[z0,z2,z968,z4,z5,z6]),(0,[z0,z2,z3,z384,z6,z969]),(0,[z0,z2,z3,z14,z5,z67])]],
   [[(0,[z970,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z4,z5,z971]),(0,[z0,z319,z3,z327,z5,z6]),(0,[z192,z0,z3,z4,z48,z70]),(0,[z0,z2,z3,z972,z5,z6]),(0,[z11,z0,z2,z932,z4,z6])],[(0,[z0,z2,z3,z4,z6,z973]),(0,[z0,z2,z3,z321,z4,z48]),(0,[z0,z2,z3,z974,z5,z6])],[(0,[z0,z2,z83,z5,z6,z350])],[(0,[z388,z2,z3,z4,z5,z165]),(0,[z0,z2,z3,z4,z6,z190])],[(0,[z531,z0,z2,z3,z4,z48]),(0,[z10,z0,z2,z85,z4,z48]),(0,[z125,z0,z2,z3,z4,z48]),(0,[z109,z0,z2,z3,z14,z48])],[(0,[z0,z975,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z48,z457])],[(0,[z0,z2,z3,z373,z201,z6]),(0,[z568,z2,z3,z4,z164,z6]),(0,[z0,z161,z21,z4,z5,z6]),(0,[z44,z0,z3,z135,z6,z108]),(0,[z865,z0,z2,z3,z4,z6])],[(0,[z0,z2,z976,z3,z5,z6]),(0,[z0,z977,z3,z4,z5,z6]),(0,[z978,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z979,z6,z48])],[(0,[z0,z2,z3,z4,z112,z6]),(0,[z0,z2,z3,z4,z980,z6]),(0,[z0,z2,z163,z5,z6,z41]),(0,[z0,z2,z3,z981,z6,z48])],[(0,[z0,z2,z3,z982,z5,z6]),(0,[z0,z2,z983,z4,z5,z6]),(0,[z0,z2,z127,z4,z6,z48]),(0,[z0,z2,z3,z4,z77,z165]),(0,[z0,z2,z3,z65,z382,z6]),(0,[z0,z2,z3,z290,z4,z48])],[(0,[z0,z2,z3,z348,z5,z235]),(0,[z984,z0,z2,z3,z4,z6]),(0,[z109,z0,z2,z3,z5,z771])],[(0,[z151,z319,z3,z4,z5,z165]),(0,[z985,z0,z2,z3,z4,z6]),(0,[z808,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z201,z241]),(0,[z44,z0,z155,z4,z6,z108]),(0,[z0,z2,z85,z23,z4,z6])],[(0,[z0,z2,z986,z4,z5,z6]),(0,[z987,z0,z2,z3,z4,z6]),(0,[z117,z2,z3,z232,z5,z6])],[(0,[z0,z2,z3,z988,z5,z6]),(0,[z0,z2,z3,z5,z6,z989]),(0,[z990,z0,z2,z3,z4,z6]),(0,[z250,z2,z3,z348,z5,z6]),(0,[z0,z2,z3,z5,z6,z991]),(0,[z0,z2,z257,z3,z4,z48])]],
   [[(0,[z0,z886,z2,z3,z4,z296]),(0,[z0,z2,z3,z23,z252,z6])],[(0,[z0,z992,z2,z3,z5,z6]),(0,[z0,z31,z3,z4,z6,z346]),(0,[z0,z3,z4,z5,z728,z70]),(0,[z0,z474,z2,z3,z4,z48]),(0,[z268,z0,z2,z4,z6,z355])],[(0,[z0,z2,z993,z4,z5,z6]),(0,[z994,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z995,z6]),(0,[z996,z2,z3,z4,z5,z6]),(0,[z57,z0,z3,z4,z5,z70]),(0,[z0,z82,z2,z94,z5,z6])],[(0,[z0,z2,z3,z4,z6,z725]),(0,[z0,z173,z3,z183,z5,z6]),(0,[z250,z2,z3,z4,z49,z6]),(0,[z57,z0,z515,z3,z5,z70])],[(0,[z212,z153,z2,z3,z5,z6]),(0,[z11,z0,z138,z3,z216,z6]),(0,[z0,z2,z3,z4,z627,z48]),(0,[z0,z2,z3,z4,z6,z997]),(0,[z0,z421,z2,z3,z4,z48])],[(0,[z195,z2,z3,z128,z6,z48])],[(0,[z116,z0,z2,z998,z4,z6]),(0,[z999,z2,z3,z4,z5,z6]),(0,[z0,z2,z1000,z3,z4,z6]),(0,[z0,z1001,z3,z4,z5,z6]),(0,[z0,z2,z819,z4,z5,z6])],[],[(0,[z11,z0,z274,z3,z4,z6]),(0,[z0,z274,z3,z4,z5,z197]),(0,[z0,z161,z91,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z264]),(0,[z11,z0,z474,z2,z3,z4]),(0,[z0,z2,z3,z126,z5,z6])],[(0,[z0,z2,z3,z1002,z5,z6]),(0,[z1003,z0,z2,z3,z4,z6]),(0,[z0,z421,z2,z4,z5,z55]),(0,[z0,z2,z1004,z4,z6,z48])],[(0,[z0,z2,z3,z1005,z5,z6]),(0,[z0,z2,z3,z4,z1006,z6])],[],[(0,[z212,z2,z3,z183,z5,z6])],[(0,[z0,z2,z1007,z4,z5,z6]),(0,[z0,z2,z129,z232,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z1008]),(0,[z0,z138,z3,z614,z5,z6]),(0,[z0,z16,z47,z4,z5,z6]),(0,[z0,z2,z83,z381,z5,z6])]],
   [[(0,[z10,z0,z2,z24,z4,z48])],[(0,[z0,z2,z364,z4,z5,z6]),(0,[z0,z2,z716,z4,z5,z6]),(0,[z0,z2,z3,z1009,z5,z6]),(0,[z266,z0,z2,z4,z6,z32]),(0,[z0,z2,z3,z4,z48,z666])],[(0,[z0,z2,z3,z4,z48,z518]),(0,[z0,z2,z3,z4,z1010,z6]),(0,[z0,z2,z3,z4,z48,z520])],[(0,[z0,z2,z1011,z4,z5,z6])],[(0,[z0,z27,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z5,z1012])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z288,z27,z3,z4,z5,z6]),(0,[z0,z1013,z3,z4,z5,z6]),(0,[z44,z0,z2,z196,z4,z6]),(0,[z0,z2,z3,z101,z6,z48])],[(0,[z117,z2,z3,z4,z507,z6])],[(0,[z0,z76,z3,z4,z6,z48]),(0,[z11,z0,z2,z3,z4,z545]),(0,[z0,z2,z3,z252,z6,z48])],[(0,[z0,z61,z632,z3,z5,z6]),(0,[z57,z0,z3,z4,z233,z70]),(0,[z109,z0,z2,z3,z4,z48]),(0,[z11,z0,z2,z993,z4,z6])],[(0,[z0,z88,z3,z4,z112,z6]),(0,[z0,z31,z2,z3,z4,z433])],[(0,[z73,z2,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1014]),(0,[z132,z0,z2,z4,z6,z32]),(0,[z574,z0,z2,z3,z423,z6]),(0,[z0,z2,z1015,z4,z5,z6]),(0,[z11,z0,z2,z3,z252,z6])],[(0,[z0,z2,z3,z1016,z5,z6])],[(0,[z0,z214,z364,z4,z5,z6])],[(0,[z0,z2,z3,z4,z6,z1017])],[(0,[z278,z0,z2,z3,z4,z1018]),(0,[z0,z2,z3,z1019,z5,z6]),(0,[z0,z2,z3,z4,z311,z48])],[(0,[z0,z2,z3,z1020,z5,z6]),(0,[z0,z1021,z3,z4,z5,z6]),(0,[z1022,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1023]),(0,[z0,z2,z1024,z3,z5,z6]),(0,[z0,z2,z458,z4,z6,z48]),(0,[z0,z2,z3,z232,z6,z48]),(0,[z11,z0,z2,z3,z66,z6])]],
   [[(0,[z0,z214,z3,z4,z5,z6]),(0,[z278,z0,z2,z945,z4,z6]),(0,[z0,z2,z1025,z4,z5,z6]),(0,[z1026,z0,z2,z3,z4,z6]),(0,[z0,z281,z2,z3,z65,z118])],[(0,[z59,z2,z119,z4,z6,z48]),(0,[z0,z2,z3,z1027,z5,z6]),(0,[z0,z2,z3,z4,z1028,z6]),(0,[z0,z2,z3,z4,z58,z48]),(0,[z0,z2,z163,z14,z5,z67]),(0,[z283,z0,z2,z3,z6,z396])],[],[],[(0,[z0,z2,z119,z4,z5,z241]),(0,[z59,z2,z119,z4,z5,z231]),(0,[z11,z0,z68,z2,z23,z4])],[(0,[z0,z2,z3,z1029,z5,z6]),(0,[z0,z2,z3,z4,z5,z1030]),(0,[z1031,z2,z3,z4,z5,z6]),(0,[z0,z2,z129,z4,z507,z6]),(0,[z0,z2,z3,z4,z48,z19]),(0,[z11,z0,z2,z145,z4,z6])],[(0,[z11,z0,z2,z196,z4,z6])],[(0,[z0,z2,z3,z5,z6,z1032])],[(0,[z0,z2,z3,z1033,z5,z6]),(0,[z0,z2,z3,z1034,z5,z6]),(0,[z0,z2,z3,z1035,z5,z6]),(0,[z0,z2,z3,z4,z1036,z6])],[(0,[z0,z61,z2,z163,z5,z6])],[(0,[z181,z2,z624,z4,z5,z6]),(0,[z2,z3,z4,z35,z48,z165]),(0,[z0,z2,z4,z5,z6,z1037]),(0,[z11,z0,z2,z3,z4,z235])],[(0,[z0,z2,z3,z4,z233,z6]),(0,[z11,z0,z2,z3,z1038,z6])],[(0,[z0,z2,z1039,z4,z5,z6]),(0,[z0,z2,z3,z4,z1040,z6]),(0,[z11,z0,z173,z3,z4,z6]),(0,[z0,z2,z1041,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1042,z6]),(0,[z0,z1043,z3,z4,z5,z6]),(0,[z0,z2,z323,z14,z5,z6]),(0,[z0,z473,z47,z4,z5,z6])],[(0,[z1044,z0,z2,z3,z4,z6]),(0,[z1045,z0,z2,z3,z4,z6]),(0,[z0,z179,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z1046,z6]),(0,[z0,z2,z3,z4,z1047,z6])],[(0,[z0,z567,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z1048,z6]),(0,[z0,z2,z3,z4,z1049,z6]),(0,[z141,z2,z3,z183,z5,z6]),(0,[z0,z2,z3,z199,z507,z6]),(1,[z0,z2,z4,z6,z743])]],
   [[(0,[z1050,z0,z2,z3,z4,z6]),(0,[z0,z2,z196,z4,z5,z197]),(0,[z574,z0,z2,z4,z6,z32])],[(0,[z1051,z0,z2,z3,z4,z6]),(0,[z0,z138,z2,z163,z5,z6]),(0,[z0,z2,z3,z5,z6,z124]),(0,[z0,z2,z85,z4,z296,z6]),(0,[z0,z2,z83,z499,z5,z6])],[(0,[z0,z1052,z2,z3,z5,z6]),(0,[z64,z0,z2,z3,z4,z6]),(0,[z11,z0,z68,z2,z3,z252])],[(0,[z11,z0,z2,z3,z921,z6])],[(0,[z0,z82,z2,z3,z14,z48]),(0,[z0,z2,z3,z4,z285,z48])],[(0,[z0,z88,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z231,z48]),(0,[z11,z0,z2,z20,z3,z6]),(0,[z0,z16,z102,z47,z5,z6]),(0,[z11,z0,z61,z3,z62,z6]),(0,[z0,z2,z3,z110,z6,z41]),(0,[z0,z1053,z2,z3,z6,z48])],[(0,[z0,z2,z3,z4,z5,z1054]),(0,[z0,z2,z3,z406,z5,z197]),(0,[z0,z2,z3,z4,z5,z1055]),(0,[z93,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z4,z1056,z48])],[(0,[z99,z2,z3,z4,z134,z6]),(0,[z0,z2,z3,z4,z235,z48])],[(0,[z0,z2,z3,z211,z5,z6]),(0,[z0,z2,z3,z4,z197,z48]),(0,[z0,z2,z3,z4,z100,z12]),(0,[z0,z2,z3,z4,z6,z1057]),(0,[z0,z2,z94,z24,z4,z48]),(0,[z0,z2,z3,z306,z4,z48])],[(0,[z584,z0,z2,z4,z6,z32]),(0,[z0,z2,z3,z4,z5,z1058])],[(0,[z0,z2,z3,z1059,z5,z6]),(0,[z0,z3,z4,z5,z6,z728]),(0,[z0,z2,z894,z4,z5,z6])],[(0,[z0,z2,z66,z5,z6,z32]),(0,[z0,z802,z2,z3,z4,z48]),(0,[z11,z0,z2,z3,z1060,z6])],[(0,[z0,z2,z3,z380,z5,z241]),(0,[z213,z2,z364,z4,z134,z6])],[(0,[z44,z0,z3,z348,z6,z108])],[(0,[z11,z0,z2,z3,z87,z6]),(0,[z0,z1061,z3,z4,z5,z6]),(0,[z122,z0,z2,z3,z5,z104]),(0,[z207,z0,z2,z3,z4,z197]),(0,[z0,z2,z3,z4,z1062,z6]),(0,[z0,z2,z1063,z4,z5,z6]),(0,[z0,z2,z145,z65,z5,z6])],[(0,[z1064,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z412,z48]),(0,[z0,z898,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z1065,z4,z5,z6]),(0,[z0,z2,z20,z5,z6,z55]),(0,[z181,z2,z25,z4,z6,z48]),(0,[z213,z2,z3,z4,z134,z6]),(0,[z0,z138,z13,z3,z5,z6]),(0,[z64,z0,z2,z1066,z4,z6]),(0,[z0,z2,z23,z4,z6,z48])],[(0,[z213,z2,z3,z4,z714,z6]),(0,[z117,z2,z458,z4,z5,z6]),(0,[z0,z2,z3,z662,z4,z48])],[(0,[z1067,z0,z2,z3,z4,z6]),(0,[z0,z1068,z3,z4,z5,z6]),(0,[z0,z2,z508,z3,z4,z48]),(0,[z0,z2,z3,z14,z4,z282]),(0,[z0,z2,z1069,z4,z6,z48])],[(0,[z0,z2,z3,z4,z420,z48]),(0,[z0,z82,z2,z539,z5,z6]),(0,[z0,z2,z3,z678,z6,z41])],[(0,[z1070,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z1071,z5,z6]),(0,[z109,z0,z2,z3,z5,z396])],[(0,[z0,z2,z3,z380,z6,z48]),(0,[z610,z2,z3,z128,z5,z6]),(0,[z0,z173,z3,z4,z6,z48]),(0,[z0,z2,z3,z1072,z5,z6]),(0,[z0,z2,z4,z5,z6,z1073]),(0,[z0,z2,z3,z4,z6,z502]),(0,[z0,z2,z4,z6,z743,z32]),(0,[z0,z238,z2,z23,z4,z6])],[(0,[z0,z515,z107,z3,z5,z6]),(0,[z0,z79,z3,z4,z5,z728]),(0,[z0,z2,z3,z4,z6,z1074]),(0,[z186,z0,z2,z3,z4,z479]),(0,[z11,z0,z2,z878,z4,z6])],[(0,[z0,z2,z3,z4,z201,z6]),(0,[z0,z2,z3,z1075,z5,z6]),(0,[z0,z2,z3,z4,z6,z1076]),(0,[z151,z2,z3,z4,z459,z165]),(0,[z0,z2,z163,z4,z5,z6]),(0,[z0,z2,z3,z252,z49,z6]),(0,[z0,z2,z908,z4,z5,z6]),(0,[z11,z0,z2,z347,z126,z6])],[(0,[z0,z1077,z2,z4,z5,z6]),(0,[z0,z2,z3,z380,z5,z231]),(0,[z59,z2,z716,z4,z5,z6]),(0,[z0,z2,z364,z275,z5,z6]),(0,[z0,z2,z770,z140,z5,z6])],[(0,[z0,z1078,z3,z4,z5,z6]),(0,[z0,z2,z85,z4,z30,z6]),(0,[z11,z117,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z296,z6]),(0,[z0,z2,z4,z5,z6,z1079])],[(0,[z0,z2,z3,z4,z5,z1080]),(0,[z0,z2,z3,z126,z252,z6])],[(0,[z213,z214,z3,z4,z134,z6]),(0,[z0,z2,z998,z4,z5,z6]),(0,[z0,z2,z3,z1081,z5,z6]),(0,[z0,z2,z1082,z4,z5,z6]),(0,[z0,z2,z3,z4,z695,z48]),(0,[z0,z2,z347,z4,z5,z48])],[(0,[z0,z138,z3,z602,z5,z6]),(0,[z0,z2,z3,z1083,z5,z6]),(0,[z903,z0,z2,z3,z4,z6]),(0,[z2,z3,z716,z4,z5,z6]),(0,[z0,z2,z3,z275,z5,z6]),(0,[z11,z0,z2,z127,z4,z6]),(0,[z349,z2,z458,z4,z5,z6]),(0,[z349,z2,z3,z232,z5,z6])],[(0,[z0,z2,z3,z4,z6,z1084]),(0,[z0,z2,z23,z4,z134,z6]),(0,[z1085,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1086,z5,z6]),(0,[z0,z1087,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1088,z6]),(0,[z0,z1089,z3,z4,z5,z6])],[(0,[z0,z2,z1090,z4,z5,z6]),(0,[z0,z2,z3,z6,z48,z264])]],
   [[(0,[z0,z2,z101,z5,z6,z55]),(0,[z0,z2,z3,z1091,z6,z48])],[(0,[z11,z0,z2,z3,z211,z6]),(0,[z0,z2,z83,z581,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1018]),(0,[z0,z2,z94,z323,z5,z6]),(0,[z0,z281,z2,z3,z4,z110])],[(0,[z0,z2,z3,z4,z5,z235]),(0,[z109,z0,z2,z3,z48,z104])],[(0,[z0,z2,z83,z4,z5,z241]),(0,[z11,z0,z2,z3,z199,z6]),(0,[z0,z2,z3,z4,z1092,z6])],[(0,[z59,z2,z119,z373,z5,z6]),(0,[z0,z3,z4,z78,z6,z824]),(0,[z11,z0,z2,z1093,z4,z6])],[(0,[z0,z2,z3,z1094,z5,z6]),(0,[z0,z2,z9,z3,z4,z48]),(0,[z0,z2,z3,z4,z6,z1095]),(0,[z0,z2,z3,z126,z6,z41])],[(0,[z250,z2,z3,z4,z5,z6]),(0,[z605,z107,z3,z4,z5,z6]),(0,[z0,z214,z3,z275,z5,z6]),(0,[z0,z1096,z47,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1097]),(0,[z0,z2,z3,z317,z4,z48]),(0,[z10,z0,z2,z4,z48,z32]),(0,[z0,z2,z3,z66,z6,z48]),(0,[z109,z0,z2,z3,z477,z104])],[(0,[z0,z2,z3,z4,z48,z676])],[(0,[z269,z0,z2,z3,z4,z590]),(0,[z0,z2,z3,z4,z6,z1056])],[(0,[z0,z2,z21,z4,z5,z6]),(0,[z0,z2,z3,z876,z5,z6]),(0,[z0,z2,z458,z199,z5,z6])],[(0,[z0,z2,z3,z131,z6,z48]),(0,[z59,z2,z119,z4,z5,z241]),(0,[z0,z2,z24,z4,z115,z48]),(0,[z1098,z2,z3,z4,z6,z48])],[(0,[z0,z2,z3,z4,z1099,z6]),(0,[z0,z2,z83,z3,z4,z753]),(0,[z11,z0,z2,z3,z1094,z6])],[(0,[z0,z2,z3,z4,z5,z1100]),(0,[z574,z0,z2,z23,z4,z6]),(0,[z0,z2,z3,z1101,z6,z48])],[(0,[z195,z2,z618,z3,z5,z6])],[(0,[z0,z1102,z3,z4,z5,z6]),(0,[z169,z0,z2,z3,z4,z48])]],
   [[(0,[z0,z16,z101,z47,z5,z6]),(0,[z0,z2,z347,z4,z6,z48])],[(0,[z0,z2,z3,z4,z30,z6]),(0,[z0,z620,z3,z62,z5,z6])],[(0,[z247,z0,z2,z83,z5,z6]),(0,[z0,z2,z3,z4,z5,z715]),(0,[z0,z2,z3,z4,z1103,z6]),(0,[z0,z2,z3,z4,z5,z1104]),(0,[z0,z2,z145,z65,z118,z6])],[(0,[z0,z2,z1105,z3,z4,z6])],[(0,[z349,z2,z3,z4,z507,z6])],[(0,[z59,z2,z20,z119,z5,z6]),(0,[z0,z326,z2,z23,z4,z6])],[(0,[z0,z1106,z2,z3,z5,z6]),(0,[z465,z2,z3,z183,z5,z6]),(0,[z11,z152,z2,z3,z4,z100]),(0,[z0,z61,z3,z62,z5,z6]),(0,[z0,z138,z3,z216,z6,z48])],[(0,[z0,z88,z3,z4,z201,z6]),(0,[z11,z0,z102,z2,z3,z6]),(0,[z0,z2,z3,z1107,z5,z6]),(0,[z11,z0,z2,z3,z6,z264])],[(0,[z0,z2,z3,z1108,z5,z6]),(0,[z0,z2,z83,z472,z5,z6]),(0,[z0,z2,z3,z423,z6,z12])],[(0,[z0,z2,z3,z4,z5,z1109]),(0,[z0,z2,z3,z4,z5,z1110]),(0,[z0,z2,z4,z30,z6,z32])],[(0,[z636,z27,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z373,z6]),(0,[z366,z0,z2,z3,z4,z48])],[(0,[z0,z2,z91,z4,z5,z6]),(0,[z0,z2,z3,z4,z233,z70]),(0,[z0,z1111,z3,z4,z5,z6])],[(0,[z64,z0,z2,z3,z1112,z6])],[(0,[z0,z2,z3,z5,z6,z1113]),(0,[z0,z2,z94,z5,z6,z303]),(0,[z0,z2,z3,z4,z351,z48]),(1,[z0,z2,z347,z4,z48])],[],[(0,[z0,z2,z3,z1112,z5,z6]),(0,[z0,z2,z85,z66,z49,z6]),(0,[z0,z2,z3,z126,z118,z6])]],
   [[(0,[z0,z2,z1114,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z6]),(1,[z2,z3,z4,z714,z6]),(0,[z0,z2,z1115,z3,z4,z6]),(0,[z64,z0,z2,z3,z4,z235])],[(0,[z0,z2,z3,z4,z363,z48]),(0,[z0,z2,z3,z4,z6,z1116]),(0,[z0,z2,z3,z5,z6,z1117])],[(0,[z0,z319,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1118,z5,z6]),(0,[z0,z2,z3,z14,z5,z377])],[(0,[z0,z173,z3,z128,z5,z6]),(0,[z0,z2,z1096,z4,z5,z6]),(0,[z0,z2,z347,z4,z6,z32])],[(0,[z0,z2,z4,z5,z6,z1119]),(0,[z0,z2,z3,z4,z6,z1120]),(0,[z0,z2,z3,z187,z5,z67])],[(0,[z2,z3,z4,z5,z714,z6])],[(0,[z0,z2,z3,z4,z5,z1121]),(0,[z213,z2,z3,z275,z134,z6]),(0,[z109,z0,z2,z3,z110,z104]),(0,[z11,z0,z2,z1122,z4,z6])],[(0,[z0,z2,z3,z6,z48,z124]),(0,[z11,z0,z2,z1114,z4,z6])],[(0,[z0,z2,z3,z4,z1123,z6])],[(0,[z0,z2,z569,z4,z5,z115]),(0,[z0,z2,z3,z1124,z5,z6])],[(0,[z278,z0,z2,z3,z1005,z6]),(0,[z214,z3,z4,z5,z134,z6]),(0,[z0,z2,z501,z3,z4,z48]),(0,[z0,z2,z3,z4,z48,z97])],[(0,[z0,z2,z3,z4,z297,z48]),(0,[z151,z2,z3,z4,z48,z165]),(0,[z109,z0,z2,z3,z5,z675]),(0,[z0,z2,z3,z979,z5,z6])],[(0,[z359,z2,z119,z4,z5,z6]),(0,[z0,z2,z21,z211,z5,z6]),(0,[z0,z2,z3,z4,z110,z48]),(0,[z0,z2,z3,z981,z5,z6])],[(0,[z0,z2,z127,z4,z5,z6]),(0,[z0,z2,z3,z4,z1125,z6]),(0,[z652,z2,z3,z4,z5,z590])],[(0,[z0,z2,z3,z327,z459,z6]),(0,[z109,z0,z2,z3,z65,z48])]],
   [[(0,[z0,z2,z20,z3,z6,z48]),(0,[z0,z2,z495,z3,z4,z48]),(0,[z10,z0,z2,z170,z4,z5]),(0,[z0,z802,z2,z3,z4,z158])],[(0,[z1126,z0,z2,z3,z4,z48]),(0,[z0,z1127,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z6,z1128])],[(0,[z278,z2,z3,z4,z134,z6]),(0,[z44,z0,z2,z3,z4,z197])],[(0,[z0,z2,z4,z5,z6,z177]),(0,[z0,z2,z3,z1129,z5,z6])],[(0,[z0,z214,z3,z4,z5,z197]),(0,[z152,z161,z3,z4,z5,z6]),(0,[z269,z0,z2,z3,z4,z48]),(0,[z0,z2,z40,z3,z4,z48]),(0,[z186,z0,z2,z3,z6,z734])],[(0,[z0,z2,z1130,z4,z5,z6]),(0,[z1131,z0,z2,z3,z4,z231]),(0,[z0,z2,z826,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z1132]),(0,[z109,z0,z138,z2,z3,z48]),(0,[z11,z0,z2,z3,z4,z148])],[(0,[z0,z2,z3,z4,z6,z1133]),(0,[z0,z2,z3,z1134,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1135]),(0,[z0,z2,z4,z6,z48,z177]),(0,[z0,z326,z2,z3,z4,z48])],[(0,[z0,z2,z3,z4,z134,z197]),(0,[z349,z79,z3,z4,z5,z6])],[(0,[z195,z2,z3,z128,z5,z6]),(0,[z0,z2,z1093,z4,z5,z6]),(0,[z0,z2,z3,z4,z427,z48])],[(0,[z0,z583,z3,z373,z5,z6]),(0,[z0,z274,z3,z4,z5,z297]),(0,[z1136,z0,z2,z3,z4,z6]),(0,[z132,z0,z2,z23,z4,z6])],[(0,[z133,z0,z3,z4,z5,z70]),(0,[z0,z2,z3,z4,z6,z1137]),(0,[z652,z2,z38,z4,z5,z6]),(0,[z11,z0,z2,z347,z4,z48])],[(0,[z0,z2,z3,z4,z6,z707]),(0,[z11,z0,z2,z3,z101,z6])],[(0,[z152,z2,z3,z4,z100,z320]),(0,[z64,z0,z2,z3,z1138,z6]),(0,[z1139,z0,z2,z3,z4,z6]),(0,[z0,z2,z1004,z4,z5,z6])],[(0,[z0,z2,z91,z211,z5,z6]),(0,[z0,z2,z3,z4,z5,z1140]),(0,[z0,z2,z3,z14,z5,z345])],[(0,[z0,z2,z3,z4,z5,z1141]),(0,[z0,z2,z24,z101,z5,z6]),(0,[z0,z2,z3,z4,z49,z479])]],
   [[(0,[z0,z583,z3,z4,z5,z241]),(0,[z0,z1142,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z6,z124]),(0,[z0,z2,z347,z4,z49,z6]),(0,[z0,z2,z4,z6,z48,z1079])],[(0,[z2,z3,z4,z5,z715,z165]),(0,[z1126,z0,z2,z3,z4,z100]),(0,[z1143,z2,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z14,z67])],[(0,[z212,z76,z3,z183,z5,z6]),(0,[z0,z2,z3,z4,z1144,z6]),(0,[z11,z0,z2,z163,z4,z6])],[(0,[z0,z2,z1145,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z197])],[(0,[z0,z2,z3,z4,z6,z1146]),(0,[z0,z2,z3,z4,z433,z48]),(0,[z269,z0,z238,z3,z4,z6])],[(0,[z0,z2,z3,z1147,z5,z6]),(0,[z0,z2,z3,z4,z608,z48]),(0,[z0,z2,z3,z4,z405,z48]),(0,[z0,z319,z3,z211,z5,z6]),(0,[z44,z0,z3,z4,z6,z108]),(0,[z0,z3,z4,z404,z48,z70]),(0,[z0,z2,z1066,z4,z5,z6]),(0,[z0,z2,z14,z5,z67,z325])],[(0,[z250,z31,z3,z4,z5,z6]),(0,[z902,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z65,z51,z6])],[(0,[z478,z27,z3,z4,z5,z6]),(0,[z0,z2,z3,z1148,z5,z6]),(0,[z0,z2,z323,z4,z6,z48]),(0,[z0,z2,z3,z4,z134,z433]),(0,[z0,z2,z3,z4,z5,z1149]),(0,[z11,z0,z2,z23,z126,z6])],[(0,[z342,z27,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1150,z6]),(0,[z0,z2,z3,z4,z5,z1151]),(0,[z0,z2,z1152,z4,z5,z6]),(0,[z0,z2,z347,z4,z384,z6])],[(0,[z0,z583,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z5,z1153]),(0,[z0,z2,z3,z101,z5,z6]),(0,[z0,z2,z163,z5,z6,z104])],[(0,[z0,z2,z3,z1154,z5,z6]),(0,[z0,z2,z38,z4,z5,z590]),(0,[z0,z227,z2,z3,z4,z48]),(1,[z0,z515,z2,z3,z48]),(0,[z1155,z2,z3,z4,z5,z6])],[(0,[z0,z76,z3,z4,z5,z6]),(0,[z278,z0,z3,z4,z6,z108]),(0,[z0,z2,z3,z4,z1156,z6]),(0,[z0,z2,z3,z4,z5,z1157]),(0,[z0,z2,z3,z252,z5,z6]),(1,[z0,z2,z3,z126,z48])],[(0,[z0,z583,z3,z4,z5,z231]),(0,[z0,z2,z94,z4,z201,z6])],[(0,[z331,z107,z3,z4,z5,z6]),(0,[z0,z2,z323,z4,z841,z6]),(0,[z0,z161,z3,z4,z459,z6]),(0,[z192,z0,z3,z4,z6,z108]),(0,[z0,z2,z83,z3,z14,z48]),(0,[z11,z0,z2,z3,z4,z228])],[(0,[z0,z1158,z2,z3,z4,z5]),(0,[z0,z2,z94,z770,z5,z6]),(0,[z0,z1159,z3,z4,z5,z6]),(0,[z0,z2,z1160,z4,z5,z6])],[(0,[z0,z2,z1161,z3,z4,z6]),(1,[z2,z716,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z1162]),(0,[z0,z2,z3,z4,z1163,z6]),(0,[z0,z258,z3,z216,z5,z6]),(0,[z0,z2,z3,z4,z6,z12])]],
   [[(0,[z0,z2,z1164,z4,z5,z6]),(0,[z0,z2,z119,z4,z201,z6]),(0,[z0,z2,z3,z609,z4,z48]),(0,[z0,z2,z3,z931,z5,z6])],[(0,[z0,z2,z3,z4,z1165,z6]),(0,[z1166,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z1167]),(0,[z152,z2,z3,z4,z5,z100]),(0,[z0,z2,z24,z47,z4,z48]),(0,[z0,z2,z29,z3,z4,z797])],[(0,[z0,z2,z3,z4,z1168,z6]),(0,[z0,z2,z1169,z3,z4,z6]),(0,[z57,z117,z3,z4,z5,z70]),(0,[z0,z2,z85,z4,z49,z433])],[(0,[z0,z2,z24,z25,z4,z48]),(0,[z0,z2,z458,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1170]),(0,[z0,z2,z3,z232,z5,z6]),(0,[z1171,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z591,z104])],[(0,[z2,z3,z4,z5,z100,z715]),(0,[z652,z2,z3,z135,z5,z6]),(0,[z57,z11,z0,z3,z4,z70]),(0,[z0,z281,z2,z3,z4,z5])],[(0,[z59,z2,z119,z4,z5,z6])],[(0,[z0,z1172,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1173,z6])],[(0,[z0,z2,z3,z4,z78,z590])],[(0,[z2,z27,z3,z4,z48,z165]),(0,[z0,z1174,z3,z4,z5,z6]),(0,[z0,z31,z2,z23,z4,z6]),(0,[z0,z2,z1175,z3,z4,z6]),(0,[z0,z2,z163,z65,z5,z6]),(0,[z0,z2,z4,z6,z282,z325])],[(0,[z0,z2,z3,z4,z6,z1176]),(0,[z59,z0,z2,z20,z5,z6]),(0,[z0,z2,z564,z4,z6,z32]),(0,[z0,z68,z2,z347,z4,z5])],[(0,[z0,z2,z3,z4,z5,z1177]),(0,[z652,z2,z155,z4,z5,z6]),(0,[z0,z2,z3,z65,z296,z6]),(0,[z0,z2,z877,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1178,z6]),(0,[z0,z2,z3,z5,z6,z1179]),(0,[z0,z2,z3,z842,z5,z6]),(0,[z0,z2,z3,z4,z6,z282]),(0,[z0,z2,z145,z4,z5,z479])],[(0,[z86,z680,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z4,z451]),(0,[z0,z2,z1180,z4,z5,z6]),(0,[z0,z82,z2,z770,z5,z6]),(0,[z10,z0,z2,z706,z4,z5])],[(0,[z0,z27,z3,z4,z48,z70]),(0,[z0,z2,z3,z380,z112,z6])],[(0,[z151,z2,z3,z4,z77,z165]),(0,[z0,z82,z2,z5,z6,z265])],[(0,[z0,z2,z83,z24,z4,z48])]],
   [[(0,[z0,z395,z3,z216,z5,z6])],[(0,[z0,z2,z3,z4,z672,z48]),(0,[z0,z2,z4,z5,z479,z177])],[(0,[z0,z2,z3,z4,z5,z1181]),(0,[z0,z2,z196,z4,z5,z297]),(0,[z0,z2,z3,z4,z50,z6])],[(0,[z0,z1182,z2,z3,z4,z5]),(0,[z0,z2,z3,z135,z5,z590]),(0,[z283,z0,z2,z3,z6,z41])],[(0,[z0,z31,z214,z3,z4,z6]),(0,[z0,z2,z1183,z4,z5,z6]),(0,[z0,z2,z3,z4,z158,z48])],[(0,[z0,z27,z3,z87,z5,z6]),(0,[z0,z2,z3,z5,z6,z1184]),(0,[z0,z2,z24,z3,z4,z12]),(0,[z0,z2,z3,z729,z6,z48])],[(0,[z0,z2,z3,z87,z6,z48])],[(0,[z0,z319,z21,z4,z5,z6]),(0,[z0,z2,z23,z126,z5,z6])],[(0,[z11,z0,z2,z3,z380,z6]),(0,[z0,z2,z364,z4,z5,z197]),(0,[z0,z2,z3,z406,z5,z297]),(0,[z0,z2,z3,z4,z6,z1185]),(0,[z0,z2,z4,z5,z6,z1186])],[(0,[z121,z27,z3,z4,z6,z48]),(0,[z0,z2,z155,z4,z5,z590]),(0,[z0,z1053,z2,z3,z5,z6]),(0,[z0,z2,z458,z4,z233,z6]),(0,[z0,z2,z3,z232,z233,z6]),(0,[z11,z0,z2,z3,z126,z48])],[],[(0,[z0,z2,z1187,z4,z5,z6]),(0,[z0,z2,z3,z4,z507,z6])],[(0,[z0,z2,z3,z4,z5,z197]),(0,[z0,z2,z3,z4,z5,z1188]),(0,[z0,z2,z3,z4,z1189,z6]),(0,[z125,z0,z2,z3,z252,z6])],[(0,[z11,z0,z76,z3,z4,z6]),(0,[z0,z2,z1190,z4,z5,z6]),(0,[z0,z2,z3,z4,z164,z197]),(0,[z0,z2,z3,z4,z459,z6]),(0,[z0,z2,z3,z4,z48,z298])],[(0,[z652,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z5,z837])],[(0,[z0,z2,z1122,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1191,z6]),(0,[z212,z173,z3,z183,z5,z6]),(0,[z0,z2,z3,z1192,z5,z6]),(0,[z0,z2,z3,z4,z6,z337]),(0,[z0,z61,z3,z1086,z5,z6]),(0,[z0,z2,z38,z135,z5,z6]),(0,[z10,z0,z2,z4,z48,z55])],[(0,[z0,z161,z3,z4,z77,z6])],[(0,[z0,z2,z85,z49,z6,z22]),(0,[z0,z2,z3,z4,z206,z48])],[(0,[z0,z2,z1193,z4,z5,z6]),(0,[z0,z2,z3,z4,z1194,z6]),(0,[z0,z2,z3,z4,z6,z1195]),(0,[z0,z2,z3,z5,z6,z22]),(0,[z0,z2,z85,z66,z5,z6]),(0,[z10,z0,z2,z4,z50,z55]),(0,[z0,z2,z3,z14,z67,z48]),(0,[z0,z2,z347,z3,z4,z48])],[(0,[z181,z2,z25,z4,z5,z6]),(0,[z99,z2,z119,z4,z5,z6]),(0,[z0,z2,z323,z4,z6,z901]),(0,[z0,z2,z85,z101,z5,z6]),(0,[z0,z2,z3,z135,z6,z32]),(0,[z0,z2,z4,z418,z6,z32]),(0,[z0,z339,z2,z4,z6,z32]),(0,[z0,z2,z23,z4,z5,z6]),(0,[z0,z2,z3,z6,z734,z41])],[(0,[z0,z2,z3,z4,z5,z1196]),(0,[z59,z88,z119,z4,z5,z6]),(0,[z0,z1197,z3,z4,z5,z6]),(0,[z0,z2,z23,z4,z164,z6]),(0,[z0,z1198,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1199]),(0,[z0,z2,z4,z5,z6,z1200])],[(0,[z0,z2,z3,z4,z241,z48]),(0,[z0,z16,z1096,z4,z5,z6]),(0,[z0,z2,z3,z1124,z30,z6]),(0,[z1201,z0,z2,z3,z4,z6]),(0,[z0,z2,z267,z4,z332,z6]),(0,[z0,z2,z1069,z4,z5,z6])],[(0,[z27,z3,z4,z5,z429,z6]),(0,[z0,z2,z3,z4,z1202,z6]),(0,[z209,z0,z2,z3,z252,z6])],[(0,[z0,z319,z91,z4,z5,z6]),(0,[z0,z138,z3,z1086,z5,z6])],[(0,[z0,z173,z3,z4,z5,z6]),(0,[z0,z2,z3,z380,z5,z6]),(0,[z388,z2,z3,z4,z6,z336])],[(0,[z0,z2,z1203,z4,z5,z6]),(0,[z0,z2,z3,z4,z39,z48])],[(0,[z655,z107,z3,z4,z5,z6]),(0,[z194,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z4,z5,z433]),(0,[z11,z0,z68,z2,z3,z126])],[(0,[z59,z2,z119,z4,z112,z6]),(0,[z0,z2,z3,z5,z6,z1204])],[(0,[z0,z2,z3,z1205,z5,z6]),(0,[z0,z2,z323,z5,z6,z41])],[(0,[z0,z1206,z3,z4,z5,z6]),(0,[z11,z0,z2,z4,z6,z325])],[(0,[z11,z0,z2,z3,z348,z6]),(0,[z11,z0,z2,z129,z4,z6]),(0,[z0,z2,z3,z4,z5,z1207]),(0,[z33,z0,z2,z3,z4,z433])]],
   [[(0,[z194,z0,z2,z4,z5,z55]),(0,[z0,z2,z439,z3,z6,z41]),(0,[z0,z2,z3,z6,z48,z1204]),(0,[z11,z0,z2,z3,z1208,z6])],[(0,[z388,z2,z3,z4,z48,z165])],[(0,[z0,z2,z3,z1209,z5,z6]),(0,[z0,z2,z1210,z4,z5,z6]),(0,[z0,z2,z770,z83,z5,z6]),(0,[z0,z279,z2,z3,z4,z48])],[(0,[z0,z2,z1211,z4,z5,z6]),(0,[z0,z3,z1086,z4,z5,z6]),(0,[z57,z0,z458,z4,z5,z70]),(0,[z57,z0,z3,z232,z5,z70])],[(0,[z44,z0,z2,z3,z4,z433]),(0,[z0,z802,z2,z3,z4,z6]),(0,[z0,z2,z3,z1091,z5,z6])],[(0,[z0,z1212,z2,z3,z5,z6]),(0,[z0,z2,z4,z5,z6,z1213]),(0,[z574,z0,z2,z3,z4,z6])],[(0,[z11,z0,z2,z3,z406,z6]),(0,[z0,z68,z515,z2,z3,z5]),(0,[z0,z2,z3,z4,z606,z48]),(0,[z0,z2,z85,z4,z6,z743]),(0,[z308,z0,z2,z3,z4,z6])],[(0,[z0,z2,z744,z4,z5,z6]),(0,[z0,z2,z347,z126,z5,z6]),(0,[z0,z68,z2,z3,z126,z5])],[(0,[z0,z2,z20,z85,z5,z6]),(0,[z250,z2,z3,z4,z5,z235])],[(0,[z0,z82,z173,z3,z5,z6]),(0,[z0,z2,z3,z4,z48,z541]),(0,[z0,z2,z3,z4,z5,z1214])],[(0,[z0,z2,z1215,z3,z5,z6]),(0,[z0,z2,z38,z4,z6,z48]),(0,[z117,z2,z129,z4,z5,z6])],[(0,[z0,z2,z94,z380,z5,z6]),(0,[z213,z0,z2,z3,z4,z590]),(0,[z0,z515,z2,z3,z48,z70]),(0,[z865,z0,z2,z3,z4,z58]),(0,[z0,z2,z3,z66,z5,z6]),(0,[z11,z0,z2,z23,z4,z48])],[(0,[z0,z2,z3,z1216,z5,z6]),(0,[z0,z1217,z3,z4,z5,z6]),(0,[z0,z31,z3,z4,z6,z824]),(0,[z10,z0,z2,z4,z5,z355]),(0,[z0,z2,z3,z5,z6,z734]),(0,[z11,z0,z2,z3,z1218,z6]),(0,[z11,z0,z2,z1219,z4,z6])],[(0,[z0,z2,z3,z4,z1220,z6]),(0,[z0,z485,z2,z94,z5,z6]),(0,[z0,z274,z3,z4,z6,z48]),(0,[z0,z2,z29,z24,z4,z48]),(0,[z0,z2,z4,z384,z6,z32]),(0,[z0,z2,z3,z65,z118,z6]),(0,[z109,z0,z2,z3,z5,z71]),(0,[z0,z2,z163,z4,z6,z282])],[(0,[z738,z27,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z77,z100])],[(0,[z0,z2,z3,z131,z5,z6]),(0,[z0,z2,z155,z135,z5,z6]),(0,[z1098,z2,z3,z4,z5,z6])]],
   [[(0,[z432,z2,z3,z128,z5,z6]),(0,[z0,z2,z3,z211,z459,z6]),(0,[z0,z2,z3,z4,z6,z824]),(0,[z109,z0,z2,z3,z4,z1056])],[(0,[z0,z2,z3,z1221,z5,z6]),(0,[z11,z0,z2,z347,z4,z6]),(0,[z0,z2,z3,z1101,z5,z6]),(0,[z11,z0,z929,z3,z4,z6])],[(0,[z635,z2,z3,z4,z5,z100]),(0,[z268,z0,z2,z4,z6,z32]),(0,[z0,z2,z3,z4,z523,z48])],[(0,[z0,z1222,z2,z3,z5,z6]),(0,[z11,z0,z2,z364,z4,z6]),(0,[z0,z2,z3,z4,z5,z479]),(1,[z0,z802,z2,z3,z4])],[(0,[z117,z2,z3,z199,z5,z6]),(0,[z11,z0,z2,z3,z232,z6]),(0,[z0,z2,z347,z4,z5,z6]),(0,[z0,z2,z347,z23,z4,z6])],[(0,[z1223,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z1224,z5,z6]),(0,[z349,z2,z129,z4,z5,z6]),(0,[z1225,z0,z2,z3,z4,z6]),(0,[z11,z0,z2,z3,z4,z433]),(0,[z0,z2,z3,z14,z4,z48])],[(0,[z505,z27,z3,z4,z5,z6]),(0,[z0,z107,z3,z101,z5,z6]),(0,[z0,z1226,z3,z4,z5,z6]),(0,[z1227,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z327,z77,z6]),(0,[z0,z2,z1228,z4,z5,z6]),(0,[z57,z0,z3,z4,z5,z728]),(0,[z10,z0,z2,z3,z4,z1095])],[(0,[z213,z2,z3,z4,z134,z197])],[(0,[z0,z2,z3,z4,z1229,z6]),(0,[z0,z2,z3,z4,z12,z165]),(0,[z1230,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z1231,z6]),(0,[z0,z2,z23,z4,z118,z6])],[(0,[z0,z88,z3,z380,z5,z6]),(0,[z11,z0,z2,z1015,z4,z6])],[(0,[z0,z2,z3,z4,z1232,z6]),(0,[z388,z2,z3,z4,z134,z6]),(0,[z116,z152,z2,z3,z4,z100]),(0,[z0,z138,z3,z216,z5,z6]),(0,[z1233,z2,z3,z4,z5,z6]),(0,[z652,z2,z3,z348,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1234]),(0,[z57,z0,z3,z4,z507,z70]),(0,[z11,z0,z82,z2,z94,z6]),(0,[z10,z0,z2,z4,z5,z837])],[(0,[z0,z106,z3,z62,z5,z6]),(0,[z0,z1235,z2,z3,z5,z6]),(0,[z117,z2,z3,z4,z6,z48]),(0,[z574,z0,z2,z85,z4,z6]),(0,[z10,z0,z2,z3,z4,z12]),(0,[z587,z0,z475,z3,z4,z6])],[(0,[z0,z2,z3,z1236,z5,z6]),(0,[z0,z2,z3,z4,z6,z1237]),(0,[z0,z2,z3,z4,z384,z48])],[(0,[z0,z2,z3,z4,z48,z438]),(0,[z0,z2,z38,z4,z6,z32]),(0,[z0,z2,z3,z4,z1238,z6]),(0,[z0,z2,z3,z4,z6,z743])],[(0,[z213,z250,z2,z3,z4,z6]),(0,[z0,z2,z3,z1239,z5,z6]),(0,[z349,z2,z3,z199,z5,z6])]],
   [[],[(0,[z0,z2,z3,z4,z1240,z6]),(0,[z0,z2,z3,z14,z51,z48])],[(0,[z0,z2,z436,z3,z4,z6]),(0,[z195,z2,z127,z128,z5,z6])],[(0,[z0,z2,z3,z4,z1241,z6]),(0,[z0,z2,z20,z24,z5,z6]),(0,[z0,z2,z4,z5,z6,z1242]),(0,[z0,z2,z3,z275,z5,z197]),(0,[z1243,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z135,z6,z48]),(0,[z0,z2,z129,z199,z5,z6])],[(0,[z0,z2,z509,z3,z4,z48]),(0,[z1244,z2,z3,z4,z5,z6]),(0,[z0,z1245,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z590,z32])],[],[(0,[z278,z0,z2,z836,z4,z6]),(1,[z0,z3,z1086,z5,z6]),(0,[z44,z0,z3,z4,z6,z493]),(0,[z349,z2,z3,z4,z6,z48]),(0,[z0,z2,z3,z4,z48,z460])],[(0,[z0,z281,z2,z3,z4,z48])],[(0,[z151,z161,z3,z4,z5,z165]),(0,[z0,z2,z3,z4,z1246,z6]),(0,[z0,z2,z3,z4,z1247,z6]),(0,[z0,z2,z155,z4,z6,z48]),(0,[z0,z2,z3,z348,z5,z590])],[(0,[z0,z2,z3,z803,z5,z6]),(0,[z359,z2,z3,z4,z5,z165]),(0,[z0,z2,z3,z4,z6,z1248]),(0,[z0,z2,z3,z5,z6,z737]),(0,[z11,z0,z671,z2,z3,z4]),(0,[z0,z3,z4,z58,z48,z70])],[(0,[z0,z2,z3,z380,z201,z6]),(0,[z0,z2,z4,z5,z6,z1249]),(0,[z0,z2,z129,z4,z6,z48]),(0,[z0,z2,z3,z65,z252,z6]),(0,[z28,z326,z2,z3,z4,z6])],[(0,[z0,z2,z3,z1250,z5,z6]),(0,[z0,z2,z3,z5,z6,z1251]),(0,[z0,z1252,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1253,z5,z6]),(0,[z0,z2,z3,z4,z1254,z6]),(0,[z1255,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z1256,z5,z6]),(0,[z0,z2,z3,z4,z49,z590]),(0,[z11,z0,z2,z3,z4,z479])],[(0,[z0,z2,z3,z373,z6,z48]),(0,[z207,z0,z2,z3,z4,z48])],[(0,[z0,z2,z3,z4,z6,z1257]),(0,[z0,z2,z3,z4,z1258,z6]),(0,[z1259,z0,z2,z3,z4,z6]),(0,[z349,z3,z4,z5,z6,z70])]],
   [[(0,[z0,z2,z3,z14,z5,z51])],[(0,[z0,z2,z3,z4,z5,z1260]),(1,[z0,z2,z3,z4,z838]),(0,[z0,z583,z3,z4,z112,z6]),(0,[z0,z2,z3,z373,z5,z231]),(0,[z207,z172,z2,z3,z4,z6]),(0,[z11,z0,z802,z2,z3,z4])],[(0,[z0,z2,z3,z5,z6,z1261])],[(0,[z0,z2,z196,z406,z5,z6]),(0,[z0,z470,z47,z4,z5,z6]),(0,[z0,z2,z24,z4,z5,z313]),(0,[z0,z1262,z3,z4,z5,z6]),(0,[z11,z0,z2,z3,z1256,z6])],[(0,[z0,z2,z20,z3,z5,z6]),(0,[z11,z0,z2,z91,z4,z6]),(0,[z464,z0,z2,z3,z4,z48]),(0,[z0,z238,z3,z4,z78,z6]),(0,[z308,z0,z2,z3,z252,z6])],[(0,[z0,z2,z3,z4,z5,z1263]),(0,[z133,z2,z3,z4,z5,z165]),(0,[z0,z2,z3,z4,z5,z838]),(0,[z0,z1264,z3,z4,z5,z6]),(0,[z0,z2,z196,z4,z6,z48]),(0,[z0,z2,z3,z199,z6,z48]),(0,[z0,z2,z3,z1038,z5,z6]),(0,[z10,z0,z2,z267,z4,z48])],[(0,[z1131,z0,z2,z3,z4,z6]),(0,[z0,z214,z3,z4,z5,z297]),(0,[z0,z2,z1265,z4,z5,z6]),(0,[z0,z2,z38,z348,z5,z6]),(0,[z0,z2,z23,z4,z252,z6])],[(0,[z11,z0,z375,z2,z3,z4]),(0,[z0,z3,z1096,z4,z5,z6]),(0,[z0,z2,z83,z140,z6,z48]),(0,[z0,z2,z23,z252,z5,z6])],[(0,[z0,z2,z3,z4,z6,z1266]),(0,[z0,z2,z3,z1267,z5,z6])],[(0,[z278,z0,z2,z3,z1221,z6]),(0,[z81,z2,z3,z4,z714,z6]),(0,[z0,z2,z3,z4,z5,z1268]),(0,[z0,z2,z3,z126,z110,z6])],[(0,[z0,z2,z3,z4,z1269,z6]),(0,[z0,z2,z38,z4,z49,z6]),(0,[z0,z2,z3,z6,z48,z22])],[(0,[z0,z2,z3,z4,z1270,z6]),(0,[z0,z2,z3,z406,z6,z48]),(0,[z2,z3,z4,z5,z6,z715]),(0,[z0,z281,z2,z3,z65,z5]),(0,[z0,z2,z3,z14,z5,z771])],[(0,[z250,z3,z4,z5,z6,z108]),(0,[z0,z2,z3,z4,z6,z1271]),(0,[z0,z2,z3,z5,z67,z771])],[(0,[z0,z2,z3,z1272,z5,z6]),(0,[z0,z31,z694,z3,z4,z6]),(0,[z11,z0,z161,z3,z4,z6]),(0,[z0,z2,z3,z1218,z5,z6]),(0,[z0,z3,z4,z5,z58,z728]),(0,[z0,z474,z2,z85,z4,z49]),(0,[z0,z2,z149,z3,z4,z48])],[],[(0,[z0,z2,z3,z4,z164,z433]),(0,[z616,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z4,z1273,z6]),(0,[z11,z0,z2,z155,z4,z6]),(0,[z0,z2,z3,z4,z233,z58]),(0,[z0,z2,z3,z66,z296,z6]),(0,[z11,z0,z2,z347,z252,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1274]),(0,[z0,z2,z3,z327,z6,z48]),(0,[z0,z2,z3,z4,z48,z511]),(0,[z0,z2,z3,z5,z6,z969]),(0,[z308,z0,z2,z3,z6,z41])],[(0,[z0,z2,z3,z5,z6,z812])],[(0,[z0,z2,z3,z1275,z5,z6]),(0,[z1276,z2,z3,z4,z5,z6]),(0,[z0,z2,z23,z4,z6,z41])],[(0,[z0,z2,z3,z1277,z5,z6]),(0,[z0,z2,z83,z4,z201,z6]),(0,[z0,z2,z91,z4,z459,z6]),(0,[z0,z2,z489,z4,z6,z32])],[(0,[z278,z0,z2,z3,z4,z838]),(0,[z0,z2,z24,z119,z4,z48]),(0,[z616,z0,z2,z4,z5,z55]),(0,[z0,z2,z3,z659,z4,z48]),(0,[z0,z2,z3,z1278,z5,z6]),(0,[z0,z2,z3,z4,z48,z675]),(0,[z192,z0,z3,z4,z5,z70]),(1,[z0,z2,z3,z4,z753])],[(0,[z11,z0,z2,z3,z4,z297])],[(0,[z0,z2,z3,z1279,z5,z6]),(0,[z151,z2,z3,z4,z5,z715]),(0,[z0,z1280,z2,z3,z4,z5]),(0,[z428,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z4,z110,z6]),(0,[z0,z2,z145,z4,z6,z48])],[(0,[z0,z2,z3,z4,z6,z1281]),(0,[z544,z0,z2,z3,z4,z48])],[(0,[z0,z274,z196,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z753]),(0,[z0,z2,z3,z1208,z5,z6])],[(0,[z2,z3,z803,z128,z5,z6]),(0,[z0,z3,z62,z1086,z5,z6])],[(0,[z0,z2,z3,z4,z6,z838]),(0,[z59,z2,z119,z4,z201,z6]),(0,[z11,z0,z2,z3,z275,z6]),(0,[z1126,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z1138,z5,z6]),(0,[z11,z0,z2,z1282,z4,z6])],[(0,[z0,z2,z323,z4,z5,z6]),(0,[z0,z2,z4,z49,z6,z743])],[(0,[z0,z2,z3,z621,z4,z48])],[(0,[z0,z583,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z103,z48]),(0,[z0,z2,z3,z4,z1283,z6]),(0,[z181,z2,z716,z4,z5,z6]),(0,[z225,z0,z2,z4,z6,z32]),(0,[z0,z1284,z3,z4,z5,z6]),(0,[z0,z1285,z3,z4,z5,z6]),(1,[z0,z2,z3,z6,z734]),(0,[z587,z0,z2,z23,z4,z6])],[(0,[z0,z2,z94,z46,z5,z6]),(0,[z0,z274,z3,z406,z5,z6]),(0,[z11,z0,z319,z3,z4,z6]),(0,[z151,z2,z3,z327,z5,z165]),(0,[z0,z2,z1286,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1287]),(0,[z0,z2,z3,z1288,z5,z6]),(0,[z1289,z0,z2,z3,z4,z6]),(0,[z0,z2,z1290,z4,z5,z6]),(0,[z0,z68,z2,z3,z4,z110]),(0,[z207,z0,z2,z23,z4,z6])]],
   [[(0,[z0,z2,z1291,z4,z5,z6]),(0,[z0,z2,z3,z4,z1292,z6]),(0,[z0,z2,z3,z1060,z5,z6]),(0,[z268,z0,z2,z24,z4,z48]),(0,[z0,z281,z2,z145,z4,z5])],[(0,[z0,z2,z3,z4,z48,z553]),(0,[z0,z2,z3,z4,z1293,z6]),(0,[z109,z0,z2,z3,z48,z396]),(0,[z11,z0,z68,z2,z3,z4]),(0,[z294,z2,z3,z4,z6,z35])],[(0,[z57,z0,z3,z4,z48,z70]),(0,[z11,z0,z2,z3,z6,z22])],[(0,[z122,z0,z2,z3,z4,z48]),(0,[z0,z2,z3,z135,z49,z6]),(0,[z0,z2,z833,z4,z5,z6])],[(0,[z0,z2,z3,z4,z77,z6]),(0,[z0,z2,z3,z4,z590,z48])],[(0,[z0,z2,z155,z348,z5,z6]),(0,[z0,z515,z2,z3,z5,z48]),(0,[z0,z2,z1219,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1294,z6]),(0,[z0,z2,z4,z110,z6,z1186])],[(0,[z0,z2,z1295,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1296]),(0,[z1297,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1298,z5,z6]),(0,[z0,z2,z3,z4,z143,z48])],[(0,[z11,z0,z179,z2,z3,z6]),(0,[z0,z822,z2,z3,z4,z5]),(0,[z11,z0,z2,z3,z4,z590]),(0,[z0,z2,z94,z5,z6,z89]),(0,[z0,z1299,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1300]),(0,[z419,z2,z3,z183,z5,z6]),(0,[z0,z2,z3,z4,z344,z48]),(0,[z0,z2,z3,z66,z6,z41]),(0,[z0,z2,z3,z5,z771,z104])],[(0,[z0,z2,z3,z4,z100,z48]),(0,[z0,z2,z423,z5,z6,z32]),(0,[z0,z2,z145,z4,z6,z32]),(0,[z11,z0,z2,z3,z777,z6])],[(0,[z0,z2,z1301,z4,z5,z6]),(0,[z0,z79,z3,z4,z5,z608]),(0,[z0,z2,z25,z4,z5,z241]),(0,[z0,z2,z85,z3,z4,z433])],[(0,[z0,z2,z3,z4,z357,z48]),(0,[z0,z2,z4,z5,z6,z837])],[(0,[z0,z3,z1086,z216,z5,z6]),(0,[z0,z2,z1282,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z753]),(0,[z0,z2,z3,z4,z1095,z48])],[(0,[z0,z2,z3,z4,z48,z588]),(0,[z0,z161,z3,z4,z6,z48]),(0,[z0,z2,z1302,z3,z4,z6]),(0,[z0,z2,z3,z4,z590,z108]),(0,[z0,z79,z3,z4,z58,z48]),(0,[z64,z0,z2,z1290,z4,z6]),(0,[z0,z2,z83,z6,z32,z41]),(0,[z0,z2,z3,z4,z5,z1303])],[(0,[z0,z2,z3,z4,z1304,z6]),(0,[z0,z2,z24,z4,z5,z345]),(0,[z0,z2,z3,z5,z6,z771]),(0,[z0,z887,z3,z4,z6,z48])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 502).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1008).take 325) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1333)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [502, 506, 325] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 142).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 290).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 434).take 78).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [142, 148, 144, 78] = true :=
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

end PEqualNP.Outside.L_meta_37793

theorem PEqualNP.Outside.L_meta_37793 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071598 * 2 ^ 32 + 4276677344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071598 * 2 ^ 32 + 4276677344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37793.solve