import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37091

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4243114184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xa00412113881b189#64 ++ 0x3400824227103631#64 ++ 0xdc0cf633f883f39b#64 ++ 0xfb819ec67f107e73#64 : BitVec 256),
   (0x401140c480344632#64 ++ 0x08022818900688c6#64 ++ 0xb63349cc80fc7fff#64 ++ 0xf6c66939901f8fff#64 : BitVec 256),
   (0x80c28e0b0b0a98c4#64 ++ 0x501851c161615318#64 ++ 0x7dc38e0f1f0f9ce7#64 ++ 0x6fb871c1e3e1f39c#64 : BitVec 256),
   (0x036c0f701dd01f00#64 ++ 0x606d81ee03ba03e0#64 ++ 0xfbfc0ff01ff01f06#64 ++ 0xdf7f81fe03fe03e0#64 : BitVec 256),
   (0x05bff00016ef6007#64 ++ 0x80b7fe0002ddec00#64 ++ 0xfdfff0001fffe006#64 ++ 0x3fbffe0003fffc00#64 : BitVec 256),
   (0x01fbedaec0000000#64 ++ 0x003f7db5d8000000#64 ++ 0xf3ffffffe0000001#64 ++ 0xfe7ffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0093e08ec0000000 0x00127c11d8000000 0x0003f00fe0000001 0x20007e01fc000000

def z1 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0000001 0xfe7ffffffc000000

def z2 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ff01ff01f06 0xdf7f81fe03fe03e0

def z3 : W := mkw 0x052c100016ef6007 0x80a5820002ddec00 0xfdfc00001fffe006 0x1fbf800003fffc00

def z4 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb63349cc80fc7fff 0xf6c66939901f8fff

def z5 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc38e0f1f0f9ce7 0x6fb871c1e3e1f39c

def z6 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0cf633f883f39b 0xfb819ec67f107e73

def z7 : W := mkw 0x02400f7009101f00 0x604801ee012203e0 0x02000ff000001f00 0xc04001fe000003e0

def z8 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x23f009c007700c04 0x047e013800ee0180

def z9 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0001fffe006 0x3fbffe0003fffc00

def z10 : W := mkw 0x0493f000022f6007 0x80927e000045ec00 0xb433f00000ffe006 0x36867e00001ffc00

def z11 : W := mkw 0x012c100014c12001 0x0025820002982400 0xfdfcf0001ff3e006 0x3fbf9e0003fe7c00

def z12 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffcfff3fff3ff9f 0xffff9ffe7ffe7ff3

def z13 : W := mkw 0x07fffd6017ff6e07 0xc0ffffac02ffedc0 0xfffff9c01fffec06 0x3fffff3803fffd80

def z14 : W := mkw 0x808282010a0a9084 0x1010504021415210 0x7dc386031f0f9087 0x6fb870c063e1f210

def z15 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xa3ff79fce0000000 0x947fef3f9c000000

def z16 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x21c3080c070c0c64 0x0438610180e1818c

def z17 : W := mkw 0x01680d2000000000 0x002d01a400000000 0xf3fc0ff000000000 0xde7f81fe00000000

def z18 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0x4dccb0001fffe006 0x09b9960003fffc00

def z19 : W := mkw 0x00c28c0a00000000 0x0018518140000000 0x71c38e0f00000001 0x6e3871c1e0000000

def z20 : W := mkw 0x01680f2009001800 0x402d01e401200300 0xfbfc0ff01f001c06 0xdf7f81fe03e00380

def z21 : W := mkw 0x012c004014d00600 0x00258008029a00c0 0xfbfc09c01ff01f06 0xdf7f813803fe03e0

def z22 : W := mkw 0x253d701034e5610b 0xa4a7ae02069cac21 0x803c7030e0f06318 0x90078e061c1e0c63

def z23 : W := mkw 0x03ee8f7a1dd01f00 0x607dd1ef43ba03e0 0xfbff8fff1ff01f07 0xff7ff1ffe3fe03e0

def z24 : W := mkw 0xa00412113881b189 0x3400824227103631 0x0c0000001883f39a 0x0180000003107e73

def z25 : W := mkw 0x012c000014c00000 0x0025800002980000 0xf9fc00001ff00006 0x1f3f800003fe0000

def z26 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x49c08e0f1f039ce1 0x493811c1e3e0739c

def z27 : W := mkw 0x01796daec0000000 0x002f2db5d8000000 0x823c7fffe0000001 0xd0478ffffc000000

def z28 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0009ffff39f 0xffbffe0013fffe73

def z29 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0x7df380001f7f8006 0x2fbe700003eff000

def z30 : W := mkw 0x02400f3009001900 0x604801e601200320 0x0000063000000000 0x000000c600000000

def z31 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x41cff63fe0000001 0x2839fec7fc000000

def z32 : W := mkw 0x0200004005500e00 0x4040000800aa01c0 0x0000000007700c04 0x0000000000ee0180

def z33 : W := mkw 0x0000000000000000 0x0000000000000000 0x3403080c000c1ce7 0x668061018001839c

def z34 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xc3fcf7f3e0000000 0x987f9efe7c000000

def z35 : W := mkw 0x437d4ff49df45f32 0x686fa9fe93be8be6 0xfbff0ffc1ffc1f66 0xdf7fe1ff83ff83ec

def z36 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0x41ccb63360000000 0x083996c66c000000

def z37 : W := mkw 0x060412501fff7f07 0xe0c0824a03ffefe0 0x0c0000001fffff06 0x0180000003ffffe0

def z38 : W := mkw 0x01fbedeec0100600 0x003f7dbdd80200c0 0xf3ffffffe0f01f07 0xfe7ffffffc1e03e0

def z39 : W := mkw 0x0000004000100600 0x00000008000200c0 0xb23009c000f01f06 0xd6460138001e03e0

def z40 : W := mkw 0x00400e0009001800 0x400801c001200300 0x79c00e001f001c06 0x4f3801c003e00380

def z41 : W := mkw 0x4011408480244032 0x0802281090048806 0x0403400c800c60f9 0x2080680190018c1f

def z42 : W := mkw 0x00828000020a0004 0x0010500000414000 0x7dc380001f0f8006 0x2fb8700003e1f000

def z43 : W := mkw 0x80400e0b090098c0 0x500801c161201318 0x00000e0f00001ce1 0x400001c1e000039c

def z44 : W := mkw 0x053d700014e56003 0x80a7ae00029cac00 0x803c700000f06000 0x10078e00001e0c00

def z45 : W := mkw 0x401140c480344632 0x08022818900688c6 0x823041c080f06318 0x90460838101e0c63

def z46 : W := mkw 0x00400daec0000000 0x000801b5d8000000 0x02000fffe0000001 0xc04001fffc000000

def z47 : W := mkw 0x0404100016ef6007 0x8080820002ddec00 0x0c0000001fffe006 0x0180000003fffc00

def z48 : W := mkw 0x41fbedeec0344632 0x083f7dbdd80688c6 0xf7ffffffe0fc7fff 0xfefffffffc1f8fff

def z49 : W := mkw 0x81fbefafcb0a98c4 0x503f7df5f9615318 0xffffffffff0f9ce7 0xffffffffffe1f39c

def z50 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff633ffffe007 0xffbffec67ffffc00

def z51 : W := mkw 0x00c28c0a00000000 0x0018518140000000 0xf1cffe3fe0000001 0xfe39ffc7fc000000

def z52 : W := mkw 0x03ee8f7a1fda1f44 0x607dd1ef43fb43e8 0xfbff0ffc1ffc1f66 0xdf7fe1ff83ff83ec

def z53 : W := mkw 0x40d3ccce833e4e76 0x481a7999d067c9ce 0xb7f349cc87fc7fff 0xf6fe693990ff8fff

def z54 : W := mkw 0x2004101030812109 0x2400820206102421 0x800c7030e0806318 0x90018e061c100c63

def z55 : W := mkw 0x25bff01036ef610f 0xa4b7fe0206ddec21 0xfdfff030ffffe31e 0xbfbffe061ffffc63

def z56 : W := mkw 0x020402501dd01f00 0x6040804a03ba03e0 0x080000001ff01f06 0x0100000003fe03e0

def z57 : W := mkw 0x00c28c0a00000000 0x0018518140000000 0x75c38e0f000c1ce7 0x6eb871c1e001839c

def z58 : W := mkw 0x037d6ff4ddd01f00 0x606fadfe9bba03e0 0xfbfc7ff0fff01f06 0xdf7f8ffe1ffe03e0

def z59 : W := mkw 0x00c28e000b0a1804 0x401851c001614300 0x7dc38e001f0f9c06 0x6fb871c003e1f380

def z60 : W := mkw 0x036c0f301dc01900 0x606d81e603b80320 0x49cc06301f000000 0x093980c603e00000

def z61 : W := mkw 0x401140c480344632 0x08022818900688c6 0x863341cc80fc63f9 0xb0c66839901f8c7f

def z62 : W := mkw 0x82400f7b09109fc0 0x704801ef612213f8 0x02000fff00001fe1 0xc04001ffe00003fc

def z63 : W := mkw 0x00400daec0000000 0x000801b5d8000000 0xd20cffffe0000001 0xfa419ffffc000000

def z64 : W := mkw 0x81eaaf2b4b0a98c4 0x503d55e569615318 0x7dcfbe3f7f0f9ce7 0x6fb9f7c7efe1f39c

def z65 : W := mkw 0x400000c480100630 0x08000018900200c6 0xb23009cc80f01fff 0xd6460139901e03ff

def z66 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x79c08e031f039c06 0x4f3811c063e07380

def z67 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x49c086031f038000 0x093810c063e07000

def z68 : W := mkw 0xa000021128009188 0x3400004225001231 0x0000000000001398 0x0000000000000273

def z69 : W := mkw 0x01fbec0a00000000 0x003f7d8140000000 0xf1fffe0f00000001 0x7e3fffc1e0000000

def z70 : W := mkw 0x81fbefafc8009080 0x103f7df5f9001210 0xfffffffff8039083 0xffffffffff007210

def z71 : W := mkw 0x800002010b0a98c4 0x5000004021615318 0x0c0000001f0f9ce6 0x0180000003e1f39c

def z72 : W := mkw 0xa0c69e1b3b8bb9cd 0x7418d3c367717739 0xfdcffe3fff8fffff 0xffb9ffc7fff1ffff

def z73 : W := mkw 0x0011400000244002 0x0002280000048800 0xb433400000fc6006 0x36866800001f8c00

def z74 : W := mkw 0x4093e08ec0244032 0x08127c11d8048806 0x0403f00fe00c60f9 0x20807e01fc018c1f

def z75 : W := mkw 0x437d4ff49df45f32 0x686fa9fe93be8be6 0xffff4ffc9ffc7fff 0xffffe9ff93ff8fff

def z76 : W := mkw 0x032c017014d00700 0x2065802e029a00e0 0x823c01f000f00300 0x9047803e001e0060

def z77 : W := mkw 0x8082800b020a80c4 0x1010500160415018 0x0403800f000f80e1 0x20807001e001f01c

def z78 : W := mkw 0x80d3ce0b0b2ed8c6 0x501a79c16165db18 0xfdf3ce0f1ffffce7 0x7fbe79c1e3ffff9c

def z79 : W := mkw 0x45bff0c496ff6637 0x88b7fe1892dfecc6 0xfffff9cc9fffffff 0xffffff3993ffffff

def z80 : W := mkw 0x0493f000022f6007 0x80927e000045ec00 0x0403f000000fe000 0x20807e000001fc00

def z81 : W := mkw 0x01fffdaed0812001 0x003fffb5da102400 0xfffffffff883e003 0xffffffffff107c00

def z82 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x6bfc0ff01f700c04 0x0d7f81fe03ee0180

def z83 : W := mkw 0x016c0d2014c00000 0x002d81a402980000 0xfbfc0ff01ff00006 0xdf7f81fe03fe0000

def z84 : W := mkw 0x01ae800016ca0004 0x0035d00002d94000 0xfdff80001fff8006 0x3fbff00003fff000

def z85 : W := mkw 0xa00412113b8bb9cd 0x7400824227717739 0xdc0cf633ff8fffff 0xfb819ec67ff1ffff

def z86 : W := mkw 0x07eebf301fcb3905 0xe0fdd7e603f96720 0x49ccb6301f038000 0x093996c603e07000

def z87 : W := mkw 0xa36c1f313dc1b989 0x746d83e627b83731 0x49ccb6337f038000 0x093996c66fe07000

def z88 : W := mkw 0x0093e08ec0000000 0x00127c11d8000000 0xd00ff63fe0000001 0xfa01fec7fc000000

def z89 : W := mkw 0x400000c480100630 0x08000018900200c6 0x020009cc80001ff9 0xc0400139900003ff

def z90 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x823c0ff000f01f00 0xd04781fe001e03e0

def z91 : W := mkw 0x016c0e001dc01800 0x402d81c003b80300 0xf9fc0e001ff01c06 0x5f3f81c003fe0380

def z92 : W := mkw 0x053d700014e56003 0x80a7ae00029cac00 0xb43f700000fc6006 0x3687ee00001f8c00

def z93 : W := mkw 0x03fbedeec5500e00 0x407f7dbdd8aa01c0 0x23f309cc07700c04 0x047e613980ee0180

def z94 : W := mkw 0x00116084c0000000 0x00022c1098000000 0x00007000e0000000 0x00000e001c000000

def z95 : W := mkw 0x4000004000344632 0x08000008000688c6 0x3403080c00fc7fff 0x66806101801f8fff

def z96 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00cf633e0000001 0xfa019ec67c000000

def z97 : W := mkw 0x00828000020a0004 0x0010500000414000 0x7dc3880c1f0f9ce7 0x6fb8710183e1f39c

def z98 : W := mkw 0xa1fbefbfe8009188 0x343f7df7fd001231 0xf3ffffffe0001399 0xfe7ffffffc000273

def z99 : W := mkw 0xa00412113881b189 0x3400824227103631 0xc80cf633f883e318 0x99019ec67f107c63

def z100 : W := mkw 0x01bbe00000000000 0x00377c0000000000 0xf1fff00000000000 0x3e3ffe0000000000

def z101 : W := mkw 0x0404100016cb2005 0x8080820002d96400 0x080000001f038000 0x0100000003e07000

def z102 : W := mkw 0x053d700016ef6007 0x80a7ae0002ddec00 0x8c3c70001fffe006 0x11878e0003fffc00

def z103 : W := mkw 0x0493e000022e4006 0x80927c000045c800 0x00030000000c0000 0x0000600000018000

def z104 : W := mkw 0xa00412113881b189 0x3400824227103631 0x480cb63378038000 0x090196c66f007000

def z105 : W := mkw 0x05fffdaed6ef6007 0x80bfffb5daddec00 0xffffffffffffe007 0xfffffffffffffc00

def z106 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0x21f30000077c0004 0x043e600000ef8000

def z107 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb23309cc00fc1f66 0xd6466139801f83ec

def z108 : W := mkw 0x032c017014d00700 0x2065802e029a00e0 0xfbfc01f01ff00306 0x9f7f803e03fe0060

def z109 : W := mkw 0x02440f7019901f00 0x604881ee033203e0 0xda0c0ff018801f02 0xdb4181fe031003e0

def z110 : W := mkw 0x83ee8f7b1fda9fc4 0x707dd1ef63fb53f8 0xffff8fff1fff9fe7 0xfffff1ffe3fff3fc

def z111 : W := mkw 0x4011408480244032 0x0802281090048806 0x3403480c800c7cff 0x6680690190018f9f

def z112 : W := mkw 0xa015521138a5f18b 0x3402aa422714be31 0xfc3ff633f8fff39f 0xff87fec67f1ffe73

def z113 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0xa3fc09f007f00f04 0x947f813e00fe01e0

def z114 : W := mkw 0x4493f0c4823f6637 0x88927e189047ecc6 0xb633f9cc80ffffff 0xf6c67f39901fffff

def z115 : W := mkw 0x85fbee0b0f6ed8c6 0xd0bf7dc161eddb18 0x7df38e0f1f7f9ce7 0x6fbe71c1e3eff39c

def z116 : W := mkw 0x04000000066e4006 0x8080000000cdc800 0x00000000077c0004 0x0000000000ef8000

def z117 : W := mkw 0x4000004000344632 0x08000008000688c6 0x0400000000fc7ffe 0x00800000001f8fff

def z118 : W := mkw 0x401140c480344632 0x08022818900688c6 0x223309cc007c0c64 0x04466139800f818c

def z119 : W := mkw 0x83ee8f3b1fca99c4 0x707dd1e763f95338 0x7dcf8e3f1f0f9ce7 0x6fb9f1c7e3e1f39c

def z120 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb63349cc00fc6c66 0x36c66939801f8d8c

def z121 : W := mkw 0x8082820b0b0a98c4 0x5010504161615318 0x0c03800f1f0f9ce7 0x21807001e3e1f39c

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000400080000001 0xf200080010000000

def z123 : W := mkw 0xa5bff2113eeff18f 0xb4b7fe4227ddfe31 0xfdfff633fffff39f 0xffbffec67ffffe73

def z124 : W := mkw 0x032c013014c00100 0x2065802602980020 0x000c003000000000 0x0001800600000000

def z125 : W := mkw 0xc093c0cf823ec6f6 0x18127819f047d8de 0xb633c9cf80ffffff 0xf6c67939f01fffff

def z126 : W := mkw 0xa00412113881b189 0x3400824227103631 0x5c0cb63378039083 0x6b8196c66f007210

def z127 : W := mkw 0xa3fffffffdd1bf89 0x747fffffffba37f1 0xfffffffffff3ff9f 0xfffffffffffe7ff3

def z128 : W := mkw 0x433d41f494f44732 0x2867a83e929e88e6 0xb63f49fc80fc7fff 0xf6c7e93f901f8fff

def z129 : W := mkw 0xa08692113a8bb18d 0x3410d24227517631 0xfdcff633ff8ff39f 0xffb9fec67ff1fe73

def z130 : W := mkw 0x05eebd2a56cb2005 0x80bdd7a54ad96400 0x49ccb6337f038000 0x093996c66fe07000

def z131 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xfffff9cc9fffe007 0xffffff3993fffc00

def z132 : W := mkw 0x0011408480000000 0x0002281090000000 0xb23349cc80000001 0xf646693990000000

def z133 : W := mkw 0x8093e08fc20a80c4 0x10127c11f8415018 0x0403f00fe00f80e1 0x20807e01fc01f01c

def z134 : W := mkw 0x47fffff49fff7f37 0xe8fffffe93ffefe6 0xfffffffc9fffffff 0xffffffff93ffffff

def z135 : W := mkw 0x0004021018801100 0x2000804203100220 0xd80c063018801302 0xdb0180c603100260

def z136 : W := mkw 0xc5fffecf9ffffef7 0xd8bfffd9f3ffffde 0xffffffcf9fffffff 0xfffffff9f3ffffff

def z137 : W := mkw 0x03ffef701dd01f00 0x607ffdee03ba03e0 0xfbfffff01ff01f06 0xff7ffffe03fe03e0

def z138 : W := mkw 0x820402511fda9fc4 0x7040804a23fb53f8 0x0c0000001fff9fe6 0x0180000003fff3fc

def z139 : W := mkw 0xa000000120008088 0x1400000024001011 0x00000003e0000099 0x000000007c000013

def z140 : W := mkw 0x03ffefbeddc01900 0x607ffdf7dbb80320 0xfbffffffff000001 0xff7fffffffe00000

def z141 : W := mkw 0x601550d4b0b5673b 0x2c02aa1a9616ace7 0xb63f79fce0fc7fff 0xf6c7ef3f9c1f8fff

def z142 : W := mkw 0x01680daec0000000 0x002d01b5d8000000 0xf3fc0fffe0000001 0xde7f81fffc000000

def z143 : W := mkw 0x0082800a00000000 0x0010500140000000 0x0003800f00000001 0x20007001e0000000

def z144 : W := mkw 0x81ee8e0b1fca98c4 0x503dd1c163f95318 0xfdff8e0f1fff9ce7 0x7fbff1c1e3fff39c

def z145 : W := mkw 0x0000000000000000 0x0000000000000000 0x940040008080739b 0xf280080010100e73

def z146 : W := mkw 0xe01552d5b8b5f7bb 0x3c02aa5ab716bef7 0xfe3ffffff8ffffff 0xffc7ffffff1fffff

def z147 : W := mkw 0x0011408480000000 0x0002281090000000 0xf23fffffe0000001 0xfe47fffffc000000

def z148 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0x823c71f0e0000000 0x90478e3e1c000000

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x800c7030e0000000 0x90018e061c000000

def z150 : W := mkw 0x413d40c494f44632 0x0827a818929e88c6 0xffff49cc9ffc7fff 0xffffe93993ff8fff

def z151 : W := mkw 0xa000021128009188 0x3400004225001231 0x00000633e0001399 0xc00000c67c000273

def z152 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000000000c1ce6 0x008000000001839c

def z153 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x23f309cc00000000 0x047e613980000000

def z154 : W := mkw 0x0482b000020b2005 0x8090560000416400 0x0000b00000038000 0x0000160000007000

def z155 : W := mkw 0x43794de485744e32 0x486f29bc90ae89c6 0x23f309cc077c0c64 0x047e613980ef818c

def z156 : W := mkw 0x01eaadaec0000000 0x003d55b5d8000000 0x43ccbfffe0000001 0xc87997fffc000000

def z157 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xb3f009c007f01f06 0xd67e013800fe03e0

def z158 : W := mkw 0x0539600004644002 0x80a72c00008c8800 0x0030000000700000 0x00060000000e0000

def z159 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000000000801302 0xd200000000100260

def z160 : W := mkw 0x41fbedeec0344632 0x083f7dbdd80688c6 0xf3ffffffe0f06319 0xfe7ffffffc1e0c63

def z161 : W := mkw 0x41794de480344632 0x082f29bc900688c6 0xf7ff4ffc80fc7fff 0xfeffe9ff901f8fff

def z162 : W := mkw 0xa097f29ff881b189 0x3412fe53ff103631 0xdc0ff63ff883f39b 0xfb81fec7ff107e73

def z163 : W := mkw 0x8004021118809180 0x3000804223101230 0xdc0c863318839383 0xfb8190c663107270

def z164 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffc0ff01ff3ff9e 0xdfff81fe03fe7ff3

def z165 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfbfcbff37ff39f06 0xdf7f97fe6ffe73e0

def z166 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0xf3fcbff360000000 0xde7f97fe6c000000

def z167 : W := mkw 0x4011408480244032 0x0802281090048806 0x0003000c000c0060 0x000060018001800c

def z168 : W := mkw 0x036c0d6015d00e00 0x406d81ac02ba01c0 0xfbfc09c01ff00c06 0x1f7f813803fe0180

def z169 : W := mkw 0x0000004000100600 0x00000008000200c0 0x223009c000700c04 0x04460138000e0180

def z170 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x2bf009c01ff01f06 0x057e013803fe03e0

def z171 : W := mkw 0x0328016004500600 0x0065002c008a00c0 0x023001c000700000 0x00460038000e0000

def z172 : W := mkw 0x05fbedaec66e4006 0x80bf7db5d8cdc800 0xf3ffffffe77c0005 0xfe7ffffffcef8000

def z173 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff80c1ffffce7 0x7fbfff0183ffff9c

def z174 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xfffc8ff31ff39f87 0xffff91fe63fe73f0

def z175 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfc0ffe3ff88fffff 0xff81ffc7ff11ffff

def z176 : W := mkw 0xc0400ecf89109ef0 0x580801d9f12213de 0x02000fcf80001ff9 0xc04001f9f00003ff

def z177 : W := mkw 0x036c0f301dc01900 0x606d81e603b80320 0xfbfc0ff01f000000 0xdf7f81fe03e00000

def z178 : W := mkw 0x01794da480000000 0x002f29b490000000 0xf3ff4ffc80000001 0xfe7fe9ff90000000

def z179 : W := mkw 0x00514daec0000000 0x000a29b5d8000000 0xb2334fffe0000001 0xf64669fffc000000

def z180 : W := mkw 0x85bff2011eeff087 0x90b7fe4023ddfe10 0xfdfff6031ffff087 0x7fbffec063fffe10

def z181 : W := mkw 0xc0d3cecf8b3edef6 0x581a79d9f167dbde 0xfff3cfcf9fffffff 0xfffe79f9f3ffffff

def z182 : W := mkw 0x037d4ff49dd01f00 0x606fa9fe93ba03e0 0xfbff4ffc9ff01f07 0xff7fe9ff93fe03e0

def z183 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x49cc06301ff01f06 0x093980c603fe03e0

def z184 : W := mkw 0x07ffff701fff7f07 0xe0ffffee03ffefe0 0xfffffff01fffff06 0xfffffffe03ffffe0

def z185 : W := mkw 0x01680d2000000000 0x002d01a400000000 0xf3fcfff3e0000001 0xfe7f9ffe7c000000

def z186 : W := mkw 0xa40412113eeff18f 0xb480824227ddfe31 0x0c0000001ffff39e 0x0180000003fffe73

def z187 : W := mkw 0x001140c480100600 0x00022818900200c0 0xb23349cc80f01f07 0xf6466939901e03e0

def z188 : W := mkw 0xa1ffffbff881b189 0x343ffff7ff103631 0xfffffffff883f39b 0xffffffffff107e73

def z189 : W := mkw 0x0011404000344602 0x00022808000688c0 0xb63349c000fc7f06 0xf6c66938001f8fe0

def z190 : W := mkw 0x0128000004400000 0x0025000000880000 0x21f0000007700004 0x043e000000ee0000

def z191 : W := mkw 0x45bbe0c4867e4636 0x88b77c1890cfc8c6 0x23f309cc077c0c64 0x047e613980ef818c

def z192 : W := mkw 0x03ffeffeddd01f00 0x607ffdffdbba03e0 0xfbfffffffff01f07 0xff7ffffffffe03e0

def z193 : W := mkw 0x4000004000100630 0x08000008000200c6 0x0000000000001ff8 0x00000000000003ff

def z194 : W := mkw 0x401140c480344632 0x08022818900688c6 0x060349cc800c7ff9 0xe0c0693990018fff

def z195 : W := mkw 0x42400ff489101f30 0x684801fe912203e6 0x02000ffc80001ff9 0xc04001ff900003ff

def z196 : W := mkw 0x052c300014c12001 0x80a5860002982400 0x000c300000000000 0x0001860000000000

def z197 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0x49ccb0001f038000 0x0939960003e07000

def z198 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc386031f0f8006 0x2fb870c063e1f000

def z199 : W := mkw 0x0004121018813101 0x2000824203102620 0xdc0cf6301883f302 0xfb819ec603107e60

def z200 : W := mkw 0xc3ffcfff9ffedff6 0x787ff9fff3ffdbfe 0xffffcfff9fffffff 0xfffff9fff3ffffff

def z201 : W := mkw 0x0000004000100600 0x00000008000200c0 0xb63049c080f07f9f 0xf6c60938101e0ff3

def z202 : W := mkw 0x01680d2000000000 0x002d01a400000000 0x23f009c000000000 0x047e013800000000

def z203 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0xd23cf7f3e0000001 0xfa479efe7c000000

def z204 : W := mkw 0xa00412513891b789 0x3400824a271236f1 0xfe3cfff3f8f3ff9f 0xffc79ffe7f1e7ff3

def z205 : W := mkw 0x00400c0001000800 0x4008018000200100 0x21c0080007000c04 0x0438010000e00180

def z206 : W := mkw 0x05bff00014e56003 0x80b7fe00029cac00 0xf1fff00000f06000 0x3e3ffe00001e0c00

def z207 : W := mkw 0x05fffe001fef7807 0xc0bfffc003fdef00 0xfdfffe001ffffc06 0x7fbfffc003ffff80

def z208 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x69c38e0f1f0f8c64 0x0d3871c1e3e1f18c

def z209 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x2dc3080c1f0f9ce6 0x05b8610183e1f39c

def z210 : W := mkw 0xa00010012001a089 0x1400020024003411 0x0000b00360038000 0x000016006c007000

def z211 : W := mkw 0x800412011881b081 0x1000824023103610 0xdc0cf6031883f083 0x7b819ec063107e10

def z212 : W := mkw 0x01bbe1a4c0000000 0x00377c3498000000 0xf3fff1f0e0000000 0xbe7ffe3e1c000000

def z213 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb63341c080fc631e 0xb6c66838101f8c63

def z214 : W := mkw 0xa00412113881b189 0x3400824227103631 0x0c00f003f883f39b 0x21801e007f107e73

def z215 : W := mkw 0xa093f08fe001a089 0x14127e11fc003411 0x0403f00fe003e099 0x20807e01fc007c13

def z216 : W := mkw 0x05bff04016ff6607 0x80b7fe0802dfecc0 0xfffff9c01fffff06 0xffffff3803ffffe0

def z217 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xc9fcf0001ff3e000 0x193f9e0003fe7c00

def z218 : W := mkw 0x401140c480344632 0x08022818900688c6 0xa23349cc80fc6f7c 0x94466939901f8def

def z219 : W := mkw 0x800002010b0a98c4 0x5000004021615318 0x3c03080c1f0f9ce7 0x6780610183e1f39c

def z220 : W := mkw 0x01bbe08ec0000000 0x00377c11d8000000 0xf1fff00fe0000001 0x3e3ffe01fc000000

def z221 : W := mkw 0x4011408480244032 0x0802281090048806 0xb433400c80fc60ff 0x36866801901f8c1f

def z222 : W := mkw 0x013d400014e44002 0x0027a800029c8800 0xfdff40001ffc6006 0x3fbfe80003ff8c00

def z223 : W := mkw 0xe004125138b5f7bb 0x3c00824a2716bef7 0xdc0cf633f8ffffff 0xfb819ec67f1fffff

def z224 : W := mkw 0x21fffdbef0812109 0x243fffb7de102421 0xf3ffffffe0806319 0xfe7ffffffc100c63

def z225 : W := mkw 0xa00412113881b189 0x3400824227103631 0x9c0040009883f39b 0xf380080013107e73

def z226 : W := mkw 0x0493f08ec22f6007 0x80927e11d845ec00 0x0403f00fe00fe001 0x20807e01fc01fc00

def z227 : W := mkw 0x45bff08496ef6037 0x88b7fe1092ddec06 0xfdfff00c9fffe0ff 0x3fbffe0193fffc1f

def z228 : W := mkw 0x0000000000000000 0x0000000000000000 0x34030000000c0006 0x2680600000018000

def z229 : W := mkw 0x401140c480344632 0x08022818900688c6 0x863041c080fc7ffe 0x90c60838101f8fff

def z230 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfcfff3fff01f07 0xff7f9ffe7ffe03e0

def z231 : W := mkw 0x03ea8d6a075a0e44 0x407d51ad40eb41c8 0x23f309cc077c0c64 0x047e613980ef818c

def z232 : W := mkw 0x05bff2101eef7107 0xa0b7fe4203ddee20 0xfdfff6301ffff306 0xffbffec603fffe60

def z233 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdc3ce0f9f8fffff 0xffb879c1f3f1ffff

def z234 : W := mkw 0xa0400e1b290099c8 0x740801c365201339 0x00000e3fe0001ff9 0xc00001c7fc0003ff

def z235 : W := mkw 0x01fbedaec30a0844 0x403f7db5d8614108 0xf3ffffffe70c0c65 0xfe7ffffffce1818c

def z236 : W := mkw 0x05bff08ed6ef6007 0x80b7fe11daddec00 0xfdfff00fffffe007 0x3fbffe01fffffc00

def z237 : W := mkw 0x41bbe0c480344632 0x08377c18900688c6 0xf7fff9cc80fc7fff 0xfeffff39901f8fff

def z238 : W := mkw 0xa20412513dd1bf89 0x7440824a27ba37f1 0x0c0000001ff3ff9e 0x0180000003fe7ff3

def z239 : W := mkw 0x05bfe00016ee4006 0x80b7fc0002ddc800 0xf9ff00001ffc0006 0x1f3fe00003ff8000

def z240 : W := mkw 0x4493f084822f6037 0x88927e109045ec06 0x0403f00c800fe0f9 0x20807e019001fc1f

def z241 : W := mkw 0x01fbedaec20a0004 0x003f7db5d8414000 0xffffffffff0f8007 0xffffffffffe1f000

def z242 : W := mkw 0x41fbedeec0344632 0x083f7dbdd80688c6 0x23f309cc007c0c64 0x047e6139800f818c

def z243 : W := mkw 0x0000004000100600 0x00000008000200c0 0xb63309cc00fc1fe7 0xf6c66139801f83fc

def z244 : W := mkw 0x00c28c0a020a0004 0x0018518140414000 0x7dc38e0f1f0f8007 0x6fb871c1e3e1f000

def z245 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x01c0000007000000 0x0038000000e00000

def z246 : W := mkw 0x401140c480344632 0x08022818900688c6 0x363309cc007c1ce7 0x66c66139800f839c

def z247 : W := mkw 0x4093c0c4823e4636 0x081278189047c8c6 0xfff3c9cc9fffffff 0xfffe793993ffffff

def z248 : W := mkw 0x036c1f701dd13f01 0x606d83ee03ba27e0 0xfffcfff01ff3ff06 0xffff9ffe03fe7fe0

def z249 : W := mkw 0xa0c69e1b3b8bb9cd 0x7418d3c367717739 0xddccf633ff83f39b 0xfbb99ec67ff07e73

def z250 : W := mkw 0x2004101030812109 0x2400820206102421 0xd00cf633e0806319 0xfa019ec67c100c63

def z251 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xf3fc0ff007700c04 0xde7f81fe00ee0180

def z252 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ff0ffc00000000 0xde7fe1ff80000000

def z253 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xb3f349cc80000001 0xf67e693990000000

def z254 : W := mkw 0x0004100010812001 0x0000820002102400 0x0c0000001883e002 0x0180000003107c00

def z255 : W := mkw 0x2004101030812109 0x2400820206102421 0x940c7030e080739b 0xf2818e061c100e73

def z256 : W := mkw 0x05fffdaed4e56003 0x80bfffb5da9cac00 0xf3ffffffe0f06001 0xfe7ffffffc1e0c00

def z257 : W := mkw 0x03eeaf3a5dc01900 0x607dd5e74bb80320 0x49ccb6337f000000 0x093996c66fe00000

def z258 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0xf9fcb0001ff38006 0x1f3f960003fe7000

def z259 : W := mkw 0x053d700014e56003 0x80a7ae00029cac00 0xf9fc70001ff06006 0x1f3f8e0003fe0c00

def z260 : W := mkw 0x80c28c0b020a80c4 0x1018518160415018 0x75c38e0f000f80e1 0x6eb871c1e001f01c

def z261 : W := mkw 0x0000021008001100 0x2000004201000220 0x0000063000001300 0xc00000c600000260

def z262 : W := mkw 0x0000100000012001 0x0000020000002400 0x0400f0000003e000 0x20801e0000007c00

def z263 : W := mkw 0x400000c480100630 0x08000018900200c6 0x020009cc00000c60 0x004001398000018c

def z264 : W := mkw 0x413961e4c0344632 0x08272c3c980688c6 0x823c71f0e0f06318 0x90478e3e1c1e0c63

def z265 : W := mkw 0x41fbedeec0100630 0x083f7dbdd80200c6 0xf3ffffffe0001ff9 0xfe7ffffffc0003ff

def z266 : W := mkw 0x02400f7009101f00 0x604801ee012203e0 0x7bc00ff01f001f06 0xcf7801fe03e003e0

def z267 : W := mkw 0x00400c0000000000 0x0008018000000000 0x71c00e0000000000 0x4e3801c000000000

def z268 : W := mkw 0xa2441f713991bf89 0x744883ee273237f1 0xde0cfff3f883ff9b 0xfbc19ffe7f107ff3

def z269 : W := mkw 0x01bbe1aec0000000 0x00377c35d8000000 0x823ff1ffe0000001 0xb047fe3ffc000000

def z270 : W := mkw 0x0011400000000000 0x0002280000000000 0xb033400000000000 0x3606680000000000

def z271 : W := mkw 0x8493f00b022fe0c7 0x90927e016045fc18 0x0403f00f000fe0e1 0x20807e01e001fc1c

def z272 : W := mkw 0x80400e0b090098c0 0x500801c161201318 0x5c008e0f18039ce3 0x6b8011c1e300739c

def z273 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000400080806318 0x9000080010100c63

def z274 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0xb5f3400007fc6006 0x36be680000ff8c00

def z275 : W := mkw 0x032c03701cd01700 0x2065806e039a02e0 0xda3c07f018f01302 0xdb4780fe031e0260

def z276 : W := mkw 0x400000c480344632 0x08000018900688c6 0x060009cc80fc7fff 0xc0c00139901f8fff

def z277 : W := mkw 0xc093c08f822ec0f6 0x18127811f045d81e 0x0403c00f800fe0f9 0x20807801f001fc1f

def z278 : W := mkw 0xa0c69e1b3b8bb9cd 0x7418d3c367717739 0x7dcfbe3f7f0f9ce7 0x6fb9f7c7efe1f39c

def z279 : W := mkw 0x01bbe00000244002 0x00377c0000048800 0xf5fff00000fc6006 0x3ebffe00001f8c00

def z280 : W := mkw 0x03fbedeec5500e00 0x407f7dbdd8aa01c0 0xf3ffffffe7700c05 0xfe7ffffffcee0180

def z281 : W := mkw 0x032c017014d00700 0x2065802e029a00e0 0xb23c09f000f01f06 0xd647813e001e03e0

def z282 : W := mkw 0xa00010012001a089 0x1400020024003411 0xd40cf633e003e099 0xfa819ec67c007c13

def z283 : W := mkw 0x40514deec0344632 0x080a29bdd80688c6 0xb6334fffe0fc7fff 0xf6c669fffc1f8fff

def z284 : W := mkw 0x05fffdaed6ef6007 0x80bfffb5daddec00 0xfffff9cc1fffe006 0x3fffff3983fffc00

def z285 : W := mkw 0x0004100010812001 0x0000820002102400 0xdc0cf0001883e002 0x3b819e0003107c00

def z286 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x7dc3880c1f0f8c66 0x2fb8710183e1f18c

def z287 : W := mkw 0x01fbed2000000000 0x003f7da400000000 0xf3fffff000000000 0xfe7ffffe00000000

def z288 : W := mkw 0xe37d5ff5bdf5ffbb 0x7c6fabfeb7bebff7 0xffffffffffffffff 0xffffffffffffffff

def z289 : W := mkw 0xe01142d5a834d7ba 0x3c02285ab5069af7 0xb6334fffe0fc7fff 0xf6c669fffc1f8fff

def z290 : W := mkw 0x401140c480344632 0x08022818900688c6 0xf63fffffe0fc7fff 0xfec7fffffc1f8fff

def z291 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3fff9cc00000000 0x3e7fff3980000000

def z292 : W := mkw 0x0004021018801100 0x2000804203100220 0x0800000018801302 0x0100000003100260

def z293 : W := mkw 0xa0441fbff881b189 0x340883f7ff103631 0xde0cfffff883f39b 0xfbc19fffff107e73

def z294 : W := mkw 0x00d3edaec0000000 0x001a7db5d8000000 0x0203ffffe0000001 0xe0407ffffc000000

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0xb030000000f00006 0x16060000001e0000

def z296 : W := mkw 0x84d3fe0b0b2ff8c7 0xd09a7fc16165ff18 0x7dc3fe0f1f0ffce7 0x6fb87fc1e3e1ff9c

def z297 : W := mkw 0x43794de485744e32 0x486f29bc90ae89c6 0xb7f349cc87fc7fff 0xf6fe693990ff8fff

def z298 : W := mkw 0x01680d2000000000 0x002d01a400000000 0x41cc063000000000 0x083980c600000000

def z299 : W := mkw 0x00c28e0a09001800 0x401851c141200300 0x79c38e0f1f001c07 0x6f3871c1e3e00380

def z300 : W := mkw 0x00400d2a40000000 0x000801a548000000 0x0000063360000000 0x000000c66c000000

def z301 : W := mkw 0x2004121038813109 0x2400824207102621 0xd80c7630f880731a 0xdb018ec61f100e63

def z302 : W := mkw 0x8000020108009080 0x1000004021001210 0x4800860318038000 0x090010c063007000

def z303 : W := mkw 0xa0155295b881b189 0x3402aa52b7103631 0xfe3ffffff883f39b 0xffc7ffffff107e73

def z304 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdcffe3fff0f9ce7 0xffb9ffc7ffe1f39c

def z305 : W := mkw 0x00000000020a0004 0x0000000000414000 0x0c0000001f0f8006 0x0180000003e1f000

def z306 : W := mkw 0x213d71b4f0812109 0x2427ae369e102421 0x823c71f0e0806318 0x90478e3e1c100c63

def z307 : W := mkw 0xa0c69e1b3b8bb9cd 0x7418d3c367717739 0x7dc38e0f1f8fffff 0x6fb871c1e3f1ffff

def z308 : W := mkw 0x00400e0009001800 0x400801c001200300 0x7dc30e0c1f0c1ce7 0x6fb861c183e1839c

def z309 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x35c3080c070c1ce7 0x66b8610180e1839c

def z310 : W := mkw 0x0000004000100600 0x00000008000200c0 0x0000000000f01f06 0x00000000001e03e0

def z311 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb23349cc80f06319 0xf6466939901e0c63

def z312 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x4dcff0001f0fe000 0x29b9fe0003e1fc00

def z313 : W := mkw 0x0000000000000000 0x0000000000000000 0x9400400000806002 0x3280080000100c00

def z314 : W := mkw 0xa00010012001a089 0x1400020024003411 0x040000000003e098 0x0080000000007c13

def z315 : W := mkw 0x05bff1a4d6ef6007 0x80b7fe349addec00 0xfffff1f0ffffe006 0xbffffe3e1ffffc00

def z316 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x2df300001fffe006 0x05be600003fffc00

def z317 : W := mkw 0x0493f000022f6007 0x80927e000045ec00 0x7dc3f0001f0fe006 0x2fb87e0003e1fc00

def z318 : W := mkw 0x0004100010812001 0x0000820002102400 0x480cb00018038000 0x0901960003007000

def z319 : W := mkw 0x01bfe00014c00000 0x0037fc0002980000 0xf9fff0001ff00006 0x3f3ffe0003fe0000

def z320 : W := mkw 0xe0155295b8a5f1bb 0x3c02aa52b714be37 0xdc0ff63ff88ff3fb 0xfb81fec7ff11fe7f

def z321 : W := mkw 0xa53d72113ce5f18b 0xb4a7ae42279cbe31 0xdc3cf633f8f3f39b 0xfb879ec67f1e7e73

def z322 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe080739b 0xfefffffffc100e73

def z323 : W := mkw 0x401140c480344632 0x08022818900688c6 0x223309cc807c1ffd 0xc4466139900f83ff

def z324 : W := mkw 0x401140c480344632 0x08022818900688c6 0x963041c080f0739b 0xf2c60838101e0e73

def z325 : W := mkw 0xa20412513dd1bf89 0x7440824a27ba37f1 0xdc0cf633fff3ff9f 0xfb819ec67ffe7ff3

def z326 : W := mkw 0xa00412113881b189 0x3400824227103631 0x0c000633f883f39b 0xc18000c67f107e73

def z327 : W := mkw 0xa00010012001a089 0x1400020024003411 0x0400f003e003e099 0x20801e007c007c13

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000080c00001ce1 0x400001018000039c

def z329 : W := mkw 0x401140c480344632 0x08022818900688c6 0x823049cc80f07ff9 0xd0460939901e0fff

def z330 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00c063000000000 0xda0180c600000000

def z331 : W := mkw 0x02440e501dd01f00 0x604881ca03ba03e0 0x79c00e001ff01f06 0x4f3801c003fe03e0

def z332 : W := mkw 0xe004125138b5f7bb 0x3c00824a2716bef7 0x0c00000018fffffe 0x01800000031fffff

def z333 : W := mkw 0x401140c480344632 0x08022818900688c6 0x263349cc807c6cfd 0x24c66939900f8d9f

def z334 : W := mkw 0xa5aeb2113ecbb18d 0xb4b5d64227d97631 0xddccf633ff83f39b 0xfbb99ec67ff07e73

def z335 : W := mkw 0x2000001020000108 0x2400000204000021 0x00000030e0000318 0x800000061c000063

def z336 : W := mkw 0xa1eebf3b7881b189 0x343dd7e76f103631 0xddccf633f883f39b 0xfbb99ec67f107e73

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0xb403480c808c7fff 0xf680690190118fff

def z338 : W := mkw 0x41fbedaec0244032 0x083f7db5d8048806 0xf7ffffffe00c60f9 0xfefffffffc018c1f

def z339 : W := mkw 0x400000c480100630 0x08000018900200c6 0x020001c080000318 0x8040003810000063

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z341 : W := mkw 0x80400e0b090098c0 0x500801c161201318 0x0000060300000000 0x000000c060000000

def z342 : W := mkw 0x8000020108009080 0x1000004021001210 0x5c00860318039083 0x6b8010c063007210

def z343 : W := mkw 0x4093e0cec0344632 0x08127c19d80688c6 0xb633f9cfe0fc7fff 0xf6c67f39fc1f8fff

def z344 : W := mkw 0x4000004000344632 0x08000008000688c6 0x00000000007c0c64 0x00000000000f818c

def z345 : W := mkw 0x4000008480000030 0x0800001090000006 0x0000000c800000f9 0x000000019000001f

def z346 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe00c1ce7 0xfefffffffc01839c

def z347 : W := mkw 0xa2400f7129109f88 0x744801ee252213f1 0x02000ff3e0001f99 0xc04001fe7c0003f3

def z348 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x4bcc0ff01f001f00 0xc97981fe03e003e0

def z349 : W := mkw 0x85eebe0b1fcbb8c5 0xd0bdd7c163f97718 0x7dcfbe0f1f0f9ce7 0x6fb9f7c1e3e1f39c

def z350 : W := mkw 0x0082800a020a0044 0x0010500140414008 0x0003000c000c0060 0x000060018001800c

def z351 : W := mkw 0x03680f7009101f00 0x606d01ee012203e0 0xf3fc0ff000001f00 0xde7f81fe000003e0

def z352 : W := mkw 0x80000001020a80c4 0x1000000020415018 0x04000000000f80e0 0x008000000001f01c

def z353 : W := mkw 0xa3ee9f7b3fdbbfcd 0x747dd3ef67fb77f9 0xffffffffffffffff 0xffffffffffffffff

def z354 : W := mkw 0x8082820b0a0a90c4 0x1010504161415218 0x5c03860f180f90e3 0x6b8070c1e301f21c

def z355 : W := mkw 0x05aaa000064a0004 0x80b5540000c94000 0x01c0000007000000 0x0038000000e00000

def z356 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x23f30fffe0000001 0xc47e61fffc000000

def z357 : W := mkw 0x81fbefafcb0a98c4 0x503f7df5f9615318 0xfbffffffff038001 0xff7fffffffe07000

def z358 : W := mkw 0x43ffeffeddf45f32 0x687ffdffdbbe8be6 0xfffffffffffc7fff 0xffffffffffff8fff

def z359 : W := mkw 0x0139600000000000 0x00272c0000000000 0x803c700000000000 0x10078e0000000000

def z360 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0x01c0000000000000 0x0038000000000000

def z361 : W := mkw 0xa00412113881b189 0x3400824227103631 0xd80cf633f8038001 0xfb019ec67f007000

def z362 : W := mkw 0xe0115085a025e0bb 0x1c022a10b404bc17 0x0403f00fe00fe0f9 0x20807e01fc01fc1f

def z363 : W := mkw 0x0004000010800000 0x0000800002100000 0xd80c000018800002 0x1b01800003100000

def z364 : W := mkw 0x85fffe0b1feff8c7 0xd0bfffc163fdff18 0xfdfffe0f1ffffce7 0x7fbfffc1e3ffff9c

def z365 : W := mkw 0x02400d6001100e00 0x404801ac002201c0 0x020009c000000c00 0x0040013800000180

def z366 : W := mkw 0x01fbedaec0244002 0x003f7db5d8048800 0xf7ffffffe0fc6007 0xfefffffffc1f8c00

def z367 : W := mkw 0x0000020009001800 0x4000004001200300 0x080000001f001c06 0x0100000003e00380

def z368 : W := mkw 0x0000004000100600 0x00000008000200c0 0x823001c000f00300 0x90460038001e0060

def z369 : W := mkw 0x00c28daec0000000 0x001851b5d8000000 0x73c38fffe0000001 0xee7871fffc000000

def z370 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x21c30e0f070c1ce5 0x443861c1e0e1839c

def z371 : W := mkw 0x8000000b000080c0 0x1000000160001018 0x0000000f000000e1 0x00000001e000001c

def z372 : W := mkw 0x07bff2501fff7f07 0xe0f7fe4a03ffefe0 0xfdfff0001fffff06 0x3fbffe0003ffffe0

def z373 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00cf00000000000 0x3a019e0000000000

def z374 : W := mkw 0x00400e0009001800 0x400801c001200300 0x00000e0000001c00 0x400001c000000380

def z375 : W := mkw 0x80c68e1b1b8a99c4 0x7018d1c363715338 0xfdcf8e3f1f8f9fe7 0xffb9f1c7e3f1f3fc

def z376 : W := mkw 0xa0c29e0b2b0bb8cd 0x541853c165617719 0x7dc3fe0fff0ffcff 0x6fb87fc1ffe1ff9f

def z377 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xcbfc07f01ff00300 0x997f80fe03fe0060

def z378 : W := mkw 0x0404100014e56003 0x80808200029cac00 0x0000000000f06000 0x00000000001e0c00

def z379 : W := mkw 0x83ea8f6b0f5a9ec4 0x507d51ed61eb53d8 0x7ff38fcf1f7f9ce7 0x6ffe71f9e3eff39c

def z380 : W := mkw 0x453d70c494f56633 0x88a7ae18929eacc6 0x823c71c080f06318 0x90478e38101e0c63

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400000000001083 0x6280000000000210

def z382 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x4dc3860f1f0f80e1 0x29b870c1e3e1f01c

def z383 : W := mkw 0xa5fffe1b3feff9cf 0xf4bfffc367fdff39 0xfdfffe3fffffffff 0xffbfffc7ffffffff

def z384 : W := mkw 0x45bff0c496ff6637 0x88b7fe1892dfecc6 0xfffff9cc1fffec66 0x3fffff3983fffd8c

def z385 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x5dc086031f039083 0x6bb810c063e07210

def z386 : W := mkw 0xa086921b3a8bb1cd 0x3410d24367517639 0xdc0ff63ff88ff3fb 0xfb81fec7ff11fe7f

def z387 : W := mkw 0xa0c28e1b2b0a99cc 0x741851c365615339 0x7dc38e3fff0f9fff 0xefb871c7ffe1f3ff

def z388 : W := mkw 0xa00412113b8bb9cd 0x7400824227717739 0x0c0000001f8ffffe 0x0180000003f1ffff

def z389 : W := mkw 0x236c1f703dd13f09 0x646d83ee07ba27e1 0xfbfc7ff0fff07f1e 0xdf7f8ffe1ffe0fe3

def z390 : W := mkw 0x0011408480244002 0x0002281090048800 0xb63349cc80fc6007 0xf6c66939901f8c00

def z391 : W := mkw 0x80400fafc90098c0 0x500801f5f9201318 0x02000fffe0001ce1 0xc04001fffc00039c

def z392 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x71c38e0f070c0c65 0x6e3871c1e0e1818c

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0x3003080c00000001 0x6600610180000000

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000080000001c06 0x4600010000000380

def z395 : W := mkw 0x2000100020012009 0x0400020004002401 0x00007000e0006018 0x00000e001c000c03

def z396 : W := mkw 0x4011408480244032 0x0802281090048806 0xb63349cc800c60f9 0xf6c6693990018c1f

def z397 : W := mkw 0xa00412113881b189 0x3400824227103631 0x0800000018038000 0x0100000003007000

def z398 : W := mkw 0x0011408480000000 0x0002281090000000 0xb63349cc8080739b 0xf6c6693990100e73

def z399 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x23f3f9cfe0000001 0x247e7f39fc000000

def z400 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x63ffbfff60000000 0x0c7ff7ffec000000

def z401 : W := mkw 0x45fffdeed6ff6637 0x88bfffbddadfecc6 0xffffffffffffffff 0xffffffffffffffff

def z402 : W := mkw 0x00828000020a0004 0x0010500000414000 0x21c30000070c0004 0x0438600000e18000

def z403 : W := mkw 0xc0514ecf8934def2 0x580a29d9f1269bde 0xb6334fcf80fc7fff 0xf6c669f9f01f8fff

def z404 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffc4ff09ff07f9f 0xffff89fe13fe0ff3

def z405 : W := mkw 0x82c68e5b1fda9fc4 0x7058d1cb63fb53f8 0x7dc38e0f1fff9fe7 0x6fb871c1e3fff3fc

def z406 : W := mkw 0xa00412113881b189 0x3400824227103631 0x8c0c7030f883f39a 0x91818e061f107e73

def z407 : W := mkw 0x036c0d7014d00700 0x206d81ae029a00e0 0xf3fc0ff000f00300 0xde7f81fe001e0060

def z408 : W := mkw 0x0004001010800100 0x2000800202100020 0x800c003000800300 0x9001800600100060

def z409 : W := mkw 0x05fbec0a076e4846 0xc0bf7d8140edc908 0x21f3080c077c0c64 0x043e610180ef818c

def z410 : W := mkw 0x84c69e0b1feff8c7 0xd098d3c163fdff18 0x7dc38e0f1ffffce7 0x6fb871c1e3ffff9c

def z411 : W := mkw 0x01ea8d2a00000000 0x003d51a540000000 0xf3ff8fff00000001 0xfe7ff1ffe0000000

def z412 : W := mkw 0xe01150c5a035e6bb 0x1c022a18b406bcd7 0xb633f9cfe0ffffff 0xf6c67f39fc1fffff

def z413 : W := mkw 0xc01142c58834d6b2 0x18022858b1069ad6 0xfe33cfcf98ffffff 0xffc679f9f31fffff

def z414 : W := mkw 0x0004021018801100 0x2000804203100220 0xd80cf633f8801303 0xfb019ec67f100260

def z415 : W := mkw 0x8082800b020a80c4 0x1010500160415018 0x7dc3800f1f0f80e7 0x2fb87001e3e1f01c

def z416 : W := mkw 0x45bbe0c4867e4636 0x88b77c1890cfc8c6 0xb7f349cc87fc7fff 0xf6fe693990ff8fff

def z417 : W := mkw 0x0093e08ec0000000 0x00127c11d8000000 0xb233f9cfe0000001 0xf6467f39fc000000

def z418 : W := mkw 0x01bbe08480000000 0x00377c1090000000 0xf3fff9cc80000001 0xfe7fff3990000000

def z419 : W := mkw 0xa36c0f713dd09f88 0x746d81ee27ba13f1 0xfbfc0ff3fff01f9f 0xdf7f81fe7ffe03f3

def z420 : W := mkw 0x45bff0c496ff6637 0x88b7fe1892dfecc6 0xfffff1c09fffe31e 0xbffffe3813fffc63

def z421 : W := mkw 0xa082900b220ba0cd 0x1410520164417419 0x0403f00fe00fe0f9 0x20807e01fc01fc1f

def z422 : W := mkw 0x0128000000000000 0x0025000000000000 0xf1fc000000000000 0x1e3f800000000000

def z423 : W := mkw 0x0497f00012af6007 0x8092fe000255ec00 0xdc0ff000188fe002 0x3b81fe000311fc00

def z424 : W := mkw 0x81ea8f2b0b0a98c4 0x503d51e561615318 0xffff8fff1f0f9ce7 0xfffff1ffe3e1f39c

def z425 : W := mkw 0x000001a4c0000000 0x0000003498000000 0x020001f0e0000000 0x8040003e1c000000

def z426 : W := mkw 0x81eaaf2b4b0a98c4 0x503d55e569615318 0x49ccb6337f038000 0x093996c66fe07000

def z427 : W := mkw 0x8000020108009080 0x1000004021001210 0xdc0cf633f8039083 0xfb819ec67f007210

def z428 : W := mkw 0xa000021128009188 0x3400004225001231 0x5c008633f803939b 0xeb8010c67f007273

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000633e0000001 0xc00000c67c000000

def z430 : W := mkw 0x00400e0009001800 0x400801c001200300 0x49c006001f000000 0x093800c003e00000

def z431 : W := mkw 0x0000008ec0000000 0x00000011d8000000 0x0000000fe0000001 0x00000001fc000000

def z432 : W := mkw 0x032c03701dd01f00 0x6065806e03ba03e0 0x8a3c01f01ff01f06 0x9147803e03fe03e0

def z433 : W := mkw 0x8000000100008080 0x1000000020001010 0x0400800300038081 0x2080100060007010

def z434 : W := mkw 0x03680f600d501e00 0x406d01ec01aa03c0 0x7bf00fc01f701c06 0x4f7e01f803ee0380

def z435 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb23049c080f07f1e 0xd6460938101e0fe3

def z436 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xffff0ffc1ffc1fe7 0xffffe1ff83ff83fc

def z437 : W := mkw 0x2004101030812109 0x2400820206102421 0x0000000000806318 0x0000000000100c63

def z438 : W := mkw 0x87ffff7b1fffffc7 0xf0ffffef63fffff8 0xffffffff1fffffe7 0xffffffffe3fffffc

def z439 : W := mkw 0xa7ffff713fffff8f 0xf4ffffee27fffff1 0xfffffff3ffffff9f 0xfffffffe7ffffff3

def z440 : W := mkw 0x03680f700d501f00 0x606d01ee01aa03e0 0x23f00ff007701f04 0xc47e01fe00ee03e0

def z441 : W := mkw 0x05bbf000022f6007 0x80b77e000045ec00 0xf5fff000000fe000 0x3ebffe000001fc00

def z442 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x79c38e0f1f038001 0x6f3871c1e3e07000

def z443 : W := mkw 0x0486900016ef6007 0x8090d20002ddec00 0x7dc380001fffe006 0x2fb8700003fffc00

def z444 : W := mkw 0x836c0f711fda9fc4 0x706d81ee23fb53f8 0xfffc0ff01fff9fe6 0xdfff81fe03fff3fc

def z445 : W := mkw 0x00000000030a0844 0x4000000000614108 0x00000000070c0c64 0x0000000000e1818c

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x79c000001f000006 0x0f38000003e00000

def z447 : W := mkw 0x836c0f7b1dd09fc0 0x706d81ef63ba13f8 0xfbfc0fff1ff01fe7 0xdf7f81ffe3fe03fc

def z448 : W := mkw 0x40400deec0100630 0x080801bdd80200c6 0x02000fffe0001ff9 0xc04001fffc0003ff

def z449 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000860300000001 0x6a0010c060000000

def z450 : W := mkw 0xa00412113881b189 0x3400824227103631 0x4c0cf633f803e099 0x29819ec67f007c13

def z451 : W := mkw 0x0004021018801100 0x2000804203100220 0x480c063018000000 0x090180c603000000

def z452 : W := mkw 0xa00012112801b189 0x3400024225003631 0x0400f633e003f399 0xe0801ec67c007e73

def z453 : W := mkw 0x0000004000100600 0x00000008000200c0 0x020009c000001f00 0xc0400138000003e0

def z454 : W := mkw 0xa5bff00136efe08f 0x94b7fe0026ddfc11 0xfdfff003ffffe09f 0x3fbffe007ffffc13

def z455 : W := mkw 0xc00002410b3edef6 0x580000482167dbde 0x0c0000001ffffffe 0x0180000003ffffff

def z456 : W := mkw 0x41fbedeec0344632 0x083f7dbdd80688c6 0xb7f349cc80fc7fff 0xf6fe6939901f8fff

def z457 : W := mkw 0x0093c000022e4006 0x001278000045c800 0xfdf3c0001fffe006 0x3fbe780003fffc00

def z458 : W := mkw 0xa16c1f313881b189 0x342d83e627103631 0xfffcfff3f883f39b 0xffff9ffe7f107e73

def z459 : W := mkw 0x401140c480344632 0x08022818900688c6 0x263309cc00fc7ffe 0x04c66139801f8fff

def z460 : W := mkw 0x83ee8f3b1fca99c4 0x707dd1e763f95338 0x49cc86331f038000 0x093990c663e07000

def z461 : W := mkw 0x03ffedfed4d00700 0x207ffdbfda9a00e0 0xf3ffffffe0f00301 0xfe7ffffffc1e0060

def z462 : W := mkw 0x0011408480000000 0x0002281090000000 0x0003400c80000001 0x2000680190000000

def z463 : W := mkw 0x81fbefafcb0a98c4 0x503f7df5f9615318 0x7ff38fcf1f0f9ce7 0x6ffe71f9e3e1f39c

def z464 : W := mkw 0x0011400000244002 0x0002280000048800 0x04034000000c6000 0x2080680000018c00

def z465 : W := mkw 0x433d41f494f44732 0x2867a83e929e88e6 0x823c41f080f06318 0x9047883e101e0c63

def z466 : W := mkw 0x0004100010812001 0x0000820002102400 0xdc0cf0009883f39b 0xfb819e0013107e73

def z467 : W := mkw 0x413961e4c0344632 0x08272c3c980688c6 0xb63f79fce0fc7fff 0xf6c7ef3f9c1f8fff

def z468 : W := mkw 0xa497f2113aaff18f 0xb492fe422755fe31 0xdc0ff633f88ff39b 0xfb81fec67f11fe73

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000f003e0000001 0x20001e007c000000

def z470 : W := mkw 0xa5ffffbffeeff18f 0xb4bffff7ffddfe31 0xfffffffffffff39f 0xfffffffffffffe73

def z471 : W := mkw 0x0000000000000000 0x0000000000000000 0x400cb63360000000 0x080196c66c000000

def z472 : W := mkw 0xa004021138809188 0x3400804227101231 0xd80c0633f880139b 0xdb0180c67f100273

def z473 : W := mkw 0x0128012000000000 0x0025002400000000 0x823c01f000000000 0x9047803e00000000

def z474 : W := mkw 0x4000004000344632 0x08000008000688c6 0x0000000000f06318 0x00000000001e0c63

def z475 : W := mkw 0xa32c13713cd1b789 0x3465826e279a36f1 0xde3cf7f3f8f3f39b 0xfbc79efe7f1e7e73

def z476 : W := mkw 0x83ffefffdfda9fc4 0x707ffdfffbfb53f8 0xffffffffffff9fe7 0xfffffffffffff3fc

def z477 : W := mkw 0x03fbeffec9101f00 0x607f7dffd92203e0 0xf3ffffffe0001f01 0xfe7ffffffc0003e0

def z478 : W := mkw 0x4011408480244032 0x0802281090048806 0x0000400080006018 0x0000080010000c03

def z479 : W := mkw 0xa00412113881b189 0x3400824227103631 0x480cb633f8039399 0xc90196c67f007273

def z480 : W := mkw 0x00828000020a0004 0x0010500000414000 0x04038000000f8000 0x208070000001f000

def z481 : W := mkw 0x0000000000244002 0x0000000000048800 0x0400000000fc6006 0x00800000001f8c00

def z482 : W := mkw 0x85ffffafdfeff8c7 0xd0bffff5fbfdff18 0xfffffffffffffce7 0xffffffffffffff9c

def z483 : W := mkw 0xa0441e113981b989 0x740883c227303731 0xfdccfe33ff83ff9f 0xffb99fc67ff07ff3

def z484 : W := mkw 0xa00412113881b189 0x3400824227103631 0x800c7633e0807399 0xd0018ec67c100e73

def z485 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xa1ff700007fc6004 0x143fee0000ff8c00

def z486 : W := mkw 0x00400d2000000000 0x000801a400000000 0x02000ff000000000 0xc04001fe00000000

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000000080739a 0x0080000000100e73

def z488 : W := mkw 0x80c28e4b0b1a9ec4 0x501851c9616353d8 0xfff38fcf1fff9fe7 0xfffe71f9e3fff3fc

def z489 : W := mkw 0xa0c69e1b3b8bb9cd 0x7418d3c367717739 0x49ccb6337f038000 0x093996c66fe07000

def z490 : W := mkw 0x00400daec0000000 0x000801b5d8000000 0x020009cc00000000 0x0040013980000000

def z491 : W := mkw 0x05fffdaed6cb2005 0x80bfffb5dad96400 0xfbffffffff038001 0xff7fffffffe07000

def z492 : W := mkw 0x4000004000344632 0x08000008000688c6 0xb63009c000fc7ffe 0xd6c60138001f8fff

def z493 : W := mkw 0x00400c0a00000000 0x0008018140000000 0x00000e0f00000001 0x400001c1e0000000

def z494 : W := mkw 0x012c000014c00000 0x0025800002980000 0x803c000000f00000 0x10078000001e0000

def z495 : W := mkw 0x400000c480100630 0x08000018900200c6 0x360309cc800c1fff 0xe6c06139900183ff

def z496 : W := mkw 0x80c69e0b1b8bb8c5 0x5018d3c163717718 0xfdcffe0f1f8ffce7 0x7fb9ffc1e3f1ff9c

def z497 : W := mkw 0x83ee8f7b1fda9fc4 0x707dd1ef63fb53f8 0xfbfc8ff31ff39f06 0xdf7f91fe63fe73e0

def z498 : W := mkw 0xa0400fbfe8009188 0x340801f7fd001231 0x02000fffe0001399 0xc04001fffc000273

def z499 : W := mkw 0xa493f001222fe08f 0x94927e002445fc11 0x0403f003e00fe099 0x20807e007c01fc13

def z500 : W := mkw 0x07ffef701ffe5f06 0xe0fffdee03ffcbe0 0xfbff0ff01ffc1f06 0xdf7fe1fe03ff83e0

def z501 : W := mkw 0x8000020108009080 0x1000004021001210 0xdc00c6039883f39b 0xfb8018c073107e73

def z502 : W := mkw 0x0404100016ef6007 0x8080820002ddec00 0xdc0cf0001fffe006 0x3b819e0003fffc00

def z503 : W := mkw 0xa5bff2113eeff18f 0xb4b7fe4227ddfe31 0xfdfff0001ffff39e 0x3fbffe0003fffe73

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000080001399 0xc000000010000273

def z505 : W := mkw 0x0093e08ec0000000 0x00127c11d8000000 0x0003000c00000000 0x0000600180000000

def z506 : W := mkw 0xa1bff2113881b189 0x3437fe4227103631 0xfdfff633f883f39b 0xffbffec67f107e73

def z507 : W := mkw 0x03680d2005400800 0x406d01a400a80100 0x01c0000007000000 0x0038000000e00000

def z508 : W := mkw 0x80d3ee8fcb0a98c4 0x501a7dd1f9615318 0x7dc3fe0fff0f9ce7 0x6fb87fc1ffe1f39c

def z509 : W := mkw 0x401542d498b45732 0x2802a85a93168ae6 0xfe3f4ffc98fc7fff 0xffc7e9ff931f8fff

def z510 : W := mkw 0x2004101030812109 0x2400820206102421 0x000c303060000000 0x000186060c000000

def z511 : W := mkw 0x00869000128b2005 0x0010d20002516400 0xfdcff0001f8fe006 0x3fb9fe0003f1fc00

def z512 : W := mkw 0x0082a00a40000000 0x0010540148000000 0x0000b00360000000 0x000016006c000000

def z513 : W := mkw 0x0004000014c00000 0x0000800002980000 0x080000001ff00006 0x0100000003fe0000

def z514 : W := mkw 0x01aaa00000000000 0x0035540000000000 0x41ccb00000000000 0x0839960000000000

def z515 : W := mkw 0xa00412113881b189 0x3400824227103631 0xd80cb63378839302 0xdb0196c66f107260

def z516 : W := mkw 0x4011408480244032 0x0802281090048806 0x9403400c808c73fb 0xf280680190118e7f

def z517 : W := mkw 0x8082800b020a80c4 0x1010500160415018 0x0000800300038000 0x0000100060007000

def z518 : W := mkw 0x073d717014f56703 0xa0e7ae2e029eace0 0x823c71f000f06300 0x90478e3e001e0c60

def z519 : W := mkw 0x800002010b0a98c4 0x5000004021615318 0x080000001f038000 0x0100000003e07000

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c00800018038002 0x2b80100003007000

def z521 : W := mkw 0x036c0f301dc01900 0x606d81e603b80320 0x79cc0e301f001c06 0x4f3981c603e00380

def z522 : W := mkw 0x016c0f3018801100 0x202d81e603100220 0xfbfc0ff018801302 0xdf7f81fe03100260

def z523 : W := mkw 0x80400e0b090098c0 0x500801c161201318 0x34030e0f000c1ce7 0x668061c1e001839c

def z524 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0x7dcfb0001f0f8006 0x2fb9f60003e1f000

def z525 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x69ffb0001f7f8004 0x0d3ff60003eff000

def z526 : W := mkw 0x053d700014e56003 0x80a7ae00029cac00 0xdc3cf00018f3e002 0x3b879e00031e7c00

def z527 : W := mkw 0x85bff2011feff8c7 0xd0b7fe4023fdff18 0xfdfff0001ffffce6 0x3fbffe0003ffff9c

def z528 : W := mkw 0x05fffd2016ef6007 0x80bfffa402ddec00 0xfffffff01fffe006 0xfffffffe03fffc00

def z529 : W := mkw 0x401140c480344632 0x08022818900688c6 0x0403400c80fc7fff 0x20806801901f8fff

def z530 : W := mkw 0x401140c480100630 0x08022818900200c6 0xb23349cc80001ff9 0xf6466939900003ff

def z531 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x4dc086031f0f9ce6 0x09b810c063e1f39c

def z532 : W := mkw 0x436c0f701df45f32 0x686d81ee03be8be6 0xfffc0ff01ffc7ffe 0xdfff81fe03ff8fff

def z533 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x73f38fcf00000001 0x6e7e71f9e0000000

def z534 : W := mkw 0x033d61f4d4d00700 0x2067ac3e9a9a00e0 0x823c71f0e0f00300 0x90478e3e1c1e0060

def z535 : W := mkw 0x0004100010812001 0x0000820002102400 0xdc0cf633f883e003 0xfb819ec67f107c00

def z536 : W := mkw 0x01796da4c0000000 0x002f2db498000000 0xf3fc7ff0e0000000 0xde7f8ffe1c000000

def z537 : W := mkw 0x0093e00000000000 0x00127c0000000000 0x0003f00000000000 0x20007e0000000000

def z538 : W := mkw 0x020402501dd01f00 0x6040804a03ba03e0 0xba3009c01ff01f06 0xd746013803fe03e0

def z539 : W := mkw 0xc0c28e4b0b3edef6 0x581851c96167dbde 0x7dc38e0f1fffffff 0x6fb871c1e3ffffff

def z540 : W := mkw 0x800002010b0a98c4 0x5000004021615318 0x5c0086031f0f9ce7 0x6b8010c063e1f39c

def z541 : W := mkw 0x00400e4009101e00 0x400801c8012203c0 0xfbf00fc01ff01f06 0xdf7e01f803fe03e0

def z542 : W := mkw 0xa00012012801b089 0x1400024025003611 0x5c00f603f803f09b 0x6b801ec07f007e13

def z543 : W := mkw 0x40d3ccce80344632 0x081a7999d00688c6 0xf7f3cfcf80fc7fff 0xfefe79f9f01f8fff

def z544 : W := mkw 0x05fffc0a16ef6007 0x80bfff8142ddec00 0xfdfffe0f1fffe007 0x7fbfffc1e3fffc00

def z545 : W := mkw 0x020402501dd01f00 0x6040804a03ba03e0 0xd80c06301ff01f06 0xdb0180c603fe03e0

def z546 : W := mkw 0xa36c1f313dc1b989 0x746d83e627b83731 0xddccf633ff83f39b 0xfbb99ec67ff07e73

def z547 : W := mkw 0xe00412d5b891b7b9 0x3c00825ab71236f7 0xde0cfffff883fffb 0xfbc19fffff107fff

def z548 : W := mkw 0x0200017000100700 0x2040002e000200e0 0x020001f000000300 0x8040003e00000060

def z549 : W := mkw 0x0011408480000000 0x0002281090000000 0xb63349cc800c1ce7 0xf6c669399001839c

def z550 : W := mkw 0xa5aeb2113ecbb18d 0xb4b5d64227d97631 0x49ccb6337f038000 0x093996c66fe07000

def z551 : W := mkw 0x441550c496ff6637 0x8882aa1892dfecc6 0xbe3349cc9fffffff 0xf7c6693993ffffff

def z552 : W := mkw 0x4000004000344632 0x08000008000688c6 0x9400400080fc7fff 0xf2800800101f8fff

def z553 : W := mkw 0xa13d73b5f881b189 0x3427ae76bf103631 0xde3cf7f3f883f39b 0xfbc79efe7f107e73

def z554 : W := mkw 0xc01142c58b3edef6 0x58022858b167dbde 0xbe3349cc9fffffff 0xf7c6693993ffffff

def z555 : W := mkw 0x037d4f701df45f02 0x606fa9ee03be8be0 0xffff4ff01ffc7f06 0xffffe9fe03ff8fe0

def z556 : W := mkw 0x401550c490b56633 0x0802aa189216acc6 0xfe3ff9cc98ffffff 0xffc7ff39931fffff

def z557 : W := mkw 0x40d3ccce833e4e76 0x481a7999d067c9ce 0x23f309cc077c0c64 0x047e613980ef818c

def z558 : W := mkw 0x41fbedeec0344632 0x083f7dbdd80688c6 0xf3ffffffe07c0c65 0xfe7ffffffc0f818c

def z559 : W := mkw 0x85bff00b16efe0c7 0x90b7fe0162ddfc18 0xfdfff00f1fffe0e7 0x3fbffe01e3fffc1c

def z560 : W := mkw 0x0011400000244002 0x0002280000048800 0xb433480c00fc7ce7 0x76866901801f8f9c

def z561 : W := mkw 0x401140c480344632 0x08022818900688c6 0x023001c000700000 0x00460038000e0000

def z562 : W := mkw 0x077d7f701df57f03 0xe0efafee03beafe0 0xfbfc7ff01ff07f06 0xdf7f8ffe03fe0fe0

def z563 : W := mkw 0x07fbed60077e4e06 0xc0ff7dac00efc9c0 0x23f309c0077c0c04 0x047e613800ef8180

def z564 : W := mkw 0x0004021018801100 0x2000804203100220 0xdc0c46309880739b 0xfb8188c613100e73

def z565 : W := mkw 0xa000021128009188 0x3400004225001231 0x0000063360000000 0x000000c66c000000

def z566 : W := mkw 0x85fffe0b1feff8c7 0xd0bfffc163fdff18 0xfdfff6031fffe006 0x3fbffec063fffc00

def z567 : W := mkw 0x04001000022f6007 0x808002000045ec00 0x04000000000fe000 0x008000000001fc00

def z568 : W := mkw 0xe01552d5b8b5f7bb 0x3c02aa5ab716bef7 0xde3cf7f3f8f3f39b 0xfbc79efe7f1e7e73

def z569 : W := mkw 0x81fbedafc20a80c4 0x103f7db5f8415018 0xf7ffffffe00f80e1 0xfefffffffc01f01c

def z570 : W := mkw 0x01fbed2a40000000 0x003f7da548000000 0xf1fff63360000000 0x3e3ffec66c000000

def z571 : W := mkw 0x2004101030812109 0x2400820206102421 0xdc0cf030f883e31a 0xbb819e061f107c63

def z572 : W := mkw 0x036c0f301dc01900 0x606d81e603b80320 0xd9cc06301f801302 0xdb3980c603f00260

def z573 : W := mkw 0x020402101dc01900 0x6040804203b80320 0x080000001f000000 0x0100000003e00000

def z574 : W := mkw 0x01bbe000020a0004 0x00377c0000414000 0xfdfff0001f0f8006 0x3fbffe0003e1f000

def z575 : W := mkw 0x01bbe00000000000 0x00377c0000000000 0x21f3000000000000 0x043e600000000000

def z576 : W := mkw 0xa00412113881b189 0x3400824227103631 0x4c0cb6337883f39a 0x098196c66f107e73

def z577 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0x023001c000000000 0x0046003800000000

def z578 : W := mkw 0xe01552d5b8b5f7bb 0x3c02aa5ab716bef7 0xbe3349cc98ffffff 0xf7c66939931fffff

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0xd40cf633e080739b 0xfa819ec67c100e73

def z580 : W := mkw 0xa000021128009188 0x3400004225001231 0x94004633e080739b 0xf28008c67c100e73

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0xb23009c000000000 0xd646013800000000

def z582 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0c06301883f39a 0xdb8180c603107e73

def z583 : W := mkw 0x0082800000000000 0x0010500000000000 0x71c3800000000000 0x2e38700000000000

def z584 : W := mkw 0x076c1f701fff7f07 0xe0ed83ee03ffefe0 0xfffc0ff01fffff06 0xdfff81fe03ffffe0

def z585 : W := mkw 0xa00412113881b189 0x3400824227103631 0x5c0086031883f39b 0x6b8010c063107e73

def z586 : W := mkw 0x80400e010b0a98c4 0x500801c021615318 0x7dc00e001f0f9ce6 0x4fb801c003e1f39c

def z587 : W := mkw 0x0000008480000000 0x0000001090000000 0x020009cc80000001 0xc040013990000000

def z588 : W := mkw 0xa00410113081a189 0x3400820226103431 0x840cf033e083e399 0xb0819e067c107c73

def z589 : W := mkw 0x0011400000244002 0x0002280000048800 0x20330000007c0004 0x04066000000f8000

def z590 : W := mkw 0x0204005014d00700 0x2040800a029a00e0 0x0000000000f00300 0x00000000001e0060

def z591 : W := mkw 0x80c28e0b090098c0 0x501851c161201318 0x71c38e0f00001ce1 0x6e3871c1e000039c

def z592 : W := mkw 0x00d3cc8e80000000 0x001a7991d0000000 0xf3f3cfcf80000001 0xfe7e79f9f0000000

def z593 : W := mkw 0x01fbedaec30a0844 0x403f7db5d8614108 0x23f309cc070c0c64 0x047e613980e1818c

def z594 : W := mkw 0xa40412113eeff18f 0xb480824227ddfe31 0xdc0cf633fffff39f 0xfb819ec67ffffe73

def z595 : W := mkw 0x01ffedaed4c00000 0x003ffdb5da980000 0xfbfffffffff00007 0xff7ffffffffe0000

def z596 : W := mkw 0x80400e0b090098c0 0x500801c161201318 0x79c00e0f1f001ce7 0x4f3801c1e3e0039c

def z597 : W := mkw 0xa1fbfdafe001a089 0x143f7fb5fc003411 0xf7ffffffe003e099 0xfefffffffc007c13

def z598 : W := mkw 0xa1ffffbffb8bb9cd 0x743ffff7ff717739 0xffffffffff8fffff 0xfffffffffff1ffff

def z599 : W := mkw 0x0497f00016ef6007 0x8092fe0002ddec00 0x0c03f0001fffe006 0x21807e0003fffc00

def z600 : W := mkw 0x012c000014c00000 0x0025800002980000 0x49cc00001f000000 0x0939800003e00000

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400400080006099 0x2080080010000c13

def z602 : W := mkw 0x601550d4b0b5673b 0x2c02aa1a9616ace7 0x823c71f0e0f06318 0x90478e3e1c1e0c63

def z603 : W := mkw 0x80d3ce8f8b0a98c4 0x501a79d1f1615318 0xfff3cfcf9f0f9ce7 0xfffe79f9f3e1f39c

def z604 : W := mkw 0x82c28f7b0b1a9fc4 0x705851ef616353f8 0x7fc38fff1f0f9fe7 0xeff871ffe3e1f3fc

def z605 : W := mkw 0x85eebe0b1fcbb8c5 0xd0bdd7c163f97718 0x49ccb6031f038000 0x093996c063e07000

def z606 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0xd1ccf633e0000001 0xfa399ec67c000000

def z607 : W := mkw 0xe0d7dedfbbbfffff 0x7c1afbdbf777ffff 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0x00c28e0a0b0a1844 0x401851c141614308 0x79c30e0c1f0c1c66 0x4f3861c183e1838c

def z609 : W := mkw 0x05bff00016cb2005 0x80b7fe0002d96400 0xf9fff0001f038000 0x3f3ffe0003e07000

def z610 : W := mkw 0x0411700000256003 0x80822e000004ac00 0x0000700000006000 0x00000e0000000c00

def z611 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0cf6337883e002 0x3b819ec66f107c00

def z612 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0xb23f79fce0000001 0xf647ef3f9c000000

def z613 : W := mkw 0x232c117034d12709 0x2465822e069a24e1 0x823c71f0e0f06318 0x90478e3e1c1e0c63

def z614 : W := mkw 0x00c28c0a00000000 0x0018518140000000 0x21c3080c00000000 0x0438610180000000

def z615 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0xf1fff000077c0004 0x3e3ffe0000ef8000

def z616 : W := mkw 0x840412011feff8c7 0xd080824023fdff18 0x0c0000001ffffce6 0x0180000003ffff9c

def z617 : W := mkw 0x05fffc0a17ef6847 0xc0bfff8142fded08 0xfdfff80c1fffec66 0x3fbfff0183fffd8c

def z618 : W := mkw 0x80c28e0b08009080 0x101851c161001210 0x7dc38e0f18039083 0x6fb871c1e3007210

def z619 : W := mkw 0x0000000000000000 0x0000000000000000 0x0403000c000c00e1 0x208060018001801c

def z620 : W := mkw 0x8000020108009080 0x1000004021001210 0x7c038e0f180f9ce7 0x6f8071c1e301f39c

def z621 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb23349cc807c0c65 0xf6466939900f818c

def z622 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x04038e0f000f9ce1 0x608071c1e001f39c

def z623 : W := mkw 0x400000c480100630 0x08000018900200c6 0x960049cc80807ffb 0xf2c0093990100fff

def z624 : W := mkw 0x80400e0b0b0a98c4 0x500801c161615318 0x0c000e0f1f0f9ce7 0x418001c1e3e1f39c

def z625 : W := mkw 0x03ffeffeddd01f00 0x607ffdffdbba03e0 0xfbff0ffc1ff01f06 0xdf7fe1ff83fe03e0

def z626 : W := mkw 0xa12c12113cc1b189 0x3425824227983631 0xfdfcf633fff3f39f 0xffbf9ec67ffe7e73

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x2003080c000c0c64 0x040061018001818c

def z628 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0cf0001883f39a 0x3b819e0003107e73

def z629 : W := mkw 0x0011408480000000 0x0002281090000000 0x823041c080000000 0x9046083810000000

def z630 : W := mkw 0x03eeaf7a5dd01f00 0x607dd5ef4bba03e0 0xfbfcbff37ff01f06 0xdf7f97fe6ffe03e0

def z631 : W := mkw 0x420402501df45f32 0x6840804a03be8be6 0x0c0000001ffc7ffe 0x0180000003ff8fff

def z632 : W := mkw 0x00828000020a0004 0x0010500000414000 0x49c080001f038000 0x0938100003e07000

def z633 : W := mkw 0x0004025018901700 0x2000804a031202e0 0xfa3c0ff018f01f06 0xdf4781fe031e03e0

def z634 : W := mkw 0x07ffff301fef7907 0xe0ffffe603fdef20 0xfdfff6301fffe006 0x3fbffec603fffc00

def z635 : W := mkw 0x05fbedaec66e4006 0x80bf7db5d8cdc800 0x23f309cc077c0004 0x047e613980ef8000

def z636 : W := mkw 0xc0c28ecf8b1a9ef4 0x581851d9f16353de 0x7fc38fcf9f0f9fff 0xeff871f9f3e1f3ff

def z637 : W := mkw 0x07bff17016ff6707 0xa0f7fe2e02dfece0 0xfffff1f01fffe306 0xbffffe3e03fffc60

def z638 : W := mkw 0x80400e0109009880 0x500801c021201310 0x7dc08e031f039c87 0x6fb811c063e07390

def z639 : W := mkw 0x02400ffec9101f00 0x604801ffd92203e0 0x02000fffe0001f01 0xc04001fffc0003e0

def z640 : W := mkw 0x80c28fafcb0a98c4 0x501851f5f9615318 0x7fc38fffff0f9ce7 0xeff871ffffe1f39c

def z641 : W := mkw 0x0011400000244002 0x0002280000048800 0x8030400000f06000 0x10060800001e0c00

def z642 : W := mkw 0x053d71a4d4e56003 0x80a7ae349a9cac00 0x823c71f0e0f06000 0x90478e3e1c1e0c00

def z643 : W := mkw 0x032c02501dd01f00 0x6065804a03ba03e0 0xf9fc00001ff01f06 0x1f3f800003fe03e0

def z644 : W := mkw 0x012c02101cc01100 0x2025804203980220 0xf9fc06301ff01306 0xdf3f80c603fe0260

def z645 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0x71cfbe3f60000001 0x6e39f7c7ec000000

def z646 : W := mkw 0xc1fbefefcb3edef6 0x583f7dfdf967dbde 0xffffffffffffffff 0xffffffffffffffff

def z647 : W := mkw 0x436c0ff49dd01f30 0x686d81fe93ba03e6 0xfbfc0ffc9ff01fff 0xdf7f81ff93fe03ff

def z648 : W := mkw 0xa0441e1b3981b9c9 0x740883c367303739 0xdc0cfe3ff883fffb 0xfb819fc7ff107fff

def z649 : W := mkw 0xa1ffffbff881b189 0x343ffff7ff103631 0xfbfffffff8038001 0xff7fffffff007000

def z650 : W := mkw 0x00440e1019801900 0x600881c203300320 0xf9cc0e301f801f06 0xdf3981c603f003e0

def z651 : W := mkw 0x421542d49df45f32 0x6842a85a93be8be6 0xbe3349cc9ffc7fff 0xf7c6693993ff8fff

def z652 : W := mkw 0x80000201090098c0 0x5000004021201318 0x0000000000001ce0 0x000000000000039c

def z653 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0xddccf0001f83e002 0x3bb99e0003f07c00

def z654 : W := mkw 0x05fffd2a56ef6007 0x80bfffa54addec00 0xfdfff6337fffe006 0x3fbffec66ffffc00

def z655 : W := mkw 0x8082800b020a80c4 0x1010500160415018 0x3403880f000f9ce7 0x66807101e001f39c

def z656 : W := mkw 0x0000020008001000 0x0000004001000200 0x5800060018001002 0x4b0000c003000200

def z657 : W := mkw 0x00400c0a01000840 0x4008018140200108 0x0000080c00000c60 0x000001018000018c

def z658 : W := mkw 0x01bbe00000000000 0x00377c0000000000 0xf1fff633e0000001 0xfe3ffec67c000000

def z659 : W := mkw 0x4000000000244032 0x0800000000048806 0x04000000000c60f8 0x0080000000018c1f

def z660 : W := mkw 0x01680d6000100600 0x002d01ac000200c0 0xf3fc0ff000f01f06 0xde7f81fe001e03e0

def z661 : W := mkw 0x05fbfdaec22f6007 0x80bf7fb5d845ec00 0xf7ffffffe00fe001 0xfefffffffc01fc00

def z662 : W := mkw 0x02440f701dd01f00 0x604881ee03ba03e0 0x0a000ff01ff01f06 0xc14001fe03fe03e0

def z663 : W := mkw 0x42514ff489345f32 0x684a29fe91268be6 0xb6334ffc80fc7fff 0xf6c669ff901f8fff

def z664 : W := mkw 0xc0d3ce8f8b2ed8f6 0x581a79d1f165db1e 0x7dc3ce0f9f0ffcff 0x6fb879c1f3e1ff9f

def z665 : W := mkw 0x8000020108009080 0x1000004021001210 0x0000060300001081 0x400000c060000210

def z666 : W := mkw 0x45bff04016ff6637 0x88b7fe0802dfecc6 0xfdfff0001ffffffe 0x3fbffe0003ffffff

def z667 : W := mkw 0x01bff00010812001 0x0037fe0002102400 0xfdfff0001883e002 0x3fbffe0003107c00

def z668 : W := mkw 0x01ffefbed8801100 0x203ffdf7db100220 0xfbfffffff8801303 0xff7fffffff100260

def z669 : W := mkw 0x4404104016ff6637 0x8880820802dfecc6 0x0c0000001ffffffe 0x0180000003ffffff

def z670 : W := mkw 0x437d4ff49df45f32 0x686fa9fe93be8be6 0xfbfc4ff09ff07f1e 0xdf7f89fe13fe0fe3

def z671 : W := mkw 0x036c0ffeddd01f00 0x606d81ffdbba03e0 0xfbfc0ffffff01f07 0xdf7f81fffffe03e0

def z672 : W := mkw 0x00c28c0a00000000 0x0018518140000000 0x41c0860300000000 0x083810c060000000

def z673 : W := mkw 0xa0c69e1b3881b189 0x3418d3c367103631 0xfdcffe3ff883f39b 0xffb9ffc7ff107e73

def z674 : W := mkw 0xe5bff2d5befff7bf 0xbcb7fe5ab7dffef7 0xffffffffffffffff 0xffffffffffffffff

def z675 : W := mkw 0x02400f7009101f00 0x604801ee012203e0 0xb2300ff000f01f06 0xd64601fe001e03e0

def z676 : W := mkw 0xe1fffffff8b5f7bb 0x3c3fffffff16bef7 0xfffffffff8ffffff 0xffffffffff1fffff

def z677 : W := mkw 0xa00410013081a089 0x1400820026103411 0xdc0cf003f883e09b 0x3b819e007f107c13

def z678 : W := mkw 0x036c0f301dc01900 0x606d81e603b80320 0xf9fc06301ff00006 0x1f3f80c603fe0000

def z679 : W := mkw 0x81fbefafc90098c0 0x503f7df5f9201318 0xf3ffffffe0001ce1 0xfe7ffffffc00039c

def z680 : W := mkw 0x81fbee0b0b0a98c4 0x503f7dc161615318 0xfdfffe0f1f0f9ce7 0x7fbfffc1e3e1f39c

def z681 : W := mkw 0x0415500016ef6007 0x8082aa0002ddec00 0xbc3340001fffe006 0x3786680003fffc00

def z682 : W := mkw 0xa00010012001a089 0x1400020024003411 0x9400f003e083f39b 0xf2801e007c107e73

def z683 : W := mkw 0x80c28c0b030a88c4 0x5018518160615118 0x25c3880f070f8ce5 0x24b87101e0e1f19c

def z684 : W := mkw 0x40514ec489345e32 0x480a29d891268bc6 0xfff34fcc9ffc7fff 0xfffe69f993ff8fff

def z685 : W := mkw 0x453d70c494f56633 0x88a7ae18929eacc6 0xb63f79cc80fc7fff 0xf6c7ef39901f8fff

def z686 : W := mkw 0x0011408480000000 0x0002281090000000 0x223309cc00000000 0x0446613980000000

def z687 : W := mkw 0x00d3ec8ec0000000 0x001a7d91d8000000 0x71c3fe0fe0000001 0x6e387fc1fc000000

def z688 : W := mkw 0x0015500010a56003 0x0002aa000214ac00 0xfc3ff00018ffe006 0x3f87fe00031ffc00

def z689 : W := mkw 0xc0d3cecf8b3edef6 0x581a79d9f167dbde 0x7ff38fcf1f7f9ce7 0x6ffe71f9e3eff39c

def z690 : W := mkw 0x0200025009101f00 0x6040004a012203e0 0x0000000000001f00 0x00000000000003e0

def z691 : W := mkw 0xa1eebf3b7881b189 0x343dd7e76f103631 0x49ccb63378038000 0x093996c66f007000

def z692 : W := mkw 0x07fffffedfff7f07 0xe0ffffffdbffefe0 0xffffffffffffff07 0xffffffffffffffe0

def z693 : W := mkw 0x01fbefaec9001800 0x403f7df5d9200300 0xfbffffffff001c07 0xff7fffffffe00380

def z694 : W := mkw 0x05bbf000066f6007 0x80b77e0000cdec00 0x25f3f000077fe004 0x24be7e0000effc00

def z695 : W := mkw 0x8000020108009080 0x1000004021001210 0x0c00000018039082 0x0180000003007210

def z696 : W := mkw 0x07eebf701fdb3f05 0xe0fdd7ee03fb67e0 0xfbfcbff01ff39f06 0xdf7f97fe03fe73e0

def z697 : W := mkw 0x808282010b0a98c4 0x5010504021615318 0x7dc380001f0f9ce6 0x2fb8700003e1f39c

def z698 : W := mkw 0xa000021128009188 0x3400004225001231 0xd00cf633e0001399 0xfa019ec67c000273

def z699 : W := mkw 0x0128212040000000 0x0025042408000000 0x000c303060000000 0x000186060c000000

def z700 : W := mkw 0x4011404000344632 0x08022808000688c6 0xb433400000fc7ffe 0x36866800001f8fff

def z701 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x843ff00000ffe000 0x3087fe00001ffc00

def z702 : W := mkw 0xe00002d5a81097b8 0x3c00005ab50212f7 0x02000fffe0001ff9 0xc04001fffc0003ff

def z703 : W := mkw 0x03ee8f701fda1f04 0x607dd1ee03fb43e0 0xffff8ff01fff9f06 0xfffff1fe03fff3e0

def z704 : W := mkw 0x0004100010812001 0x0000820002102400 0x800c700000806000 0x10018e0000100c00

def z705 : W := mkw 0x0011400000244002 0x0002280000048800 0xb433400080fc739f 0xf6866800101f8e73

def z706 : W := mkw 0xa5bff2113eeff18f 0xb4b7fe4227ddfe31 0xfdfff6337fffe006 0x3fbffec66ffffc00

def z707 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x79c38e0f1f0f8c65 0x6f3871c1e3e1f18c

def z708 : W := mkw 0x45bff08496ef6037 0x88b7fe1092ddec06 0xfdfff00c1fffe066 0x3fbffe0183fffc0c

def z709 : W := mkw 0x41fbedaec0244032 0x083f7db5d8048806 0xf7ffffffe00c7cff 0xfefffffffc018f9f

def z710 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x33f009c007701c06 0x467e013800ee0380

def z711 : W := mkw 0x05bbf000066f6007 0x80b77e0000cdec00 0x7df3f0001f7fe006 0x2fbe7e0003effc00

def z712 : W := mkw 0x232c117034d12709 0x2465822e069a24e1 0xfffcf1f0fff3e31e 0xbfff9e3e1ffe7c63

def z713 : W := mkw 0x01fbed2000000000 0x003f7da400000000 0xf3fffff3e0000001 0xfe7ffffe7c000000

def z714 : W := mkw 0xa3681d612551ae89 0x546d03ac24aa35d1 0x27f0f9c3e773ec9d 0x24fe1f387cee7d93

def z715 : W := mkw 0xe01552d5b8b5f7bb 0x3c02aa5ab716bef7 0x6a3fbfff787f8c64 0x0d47f7ffef0ff18c

def z716 : W := mkw 0x45bff08496ef6037 0x88b7fe1092ddec06 0xfffff9cc9fffe0ff 0xffffff3993fffc1f

def z717 : W := mkw 0x4497f08492af6037 0x8892fe109255ec06 0xdc0ff00c988ff3fb 0xfb81fe019311fe7f

def z718 : W := mkw 0x4493f084822f6037 0x88927e109045ec06 0x0403f00c000fe060 0x20807e018001fc0c

def z719 : W := mkw 0x00400e4009101e00 0x400801c8012203c0 0x7bf00fc01f701c06 0x4f7e01f803ee0380

def z720 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdcffe3fff8fffff 0xffb9ffc7fff1ffff

def z721 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0x6bfcbff37f738c04 0x0d7f97fe6fee7180

def z722 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xe9fff0001fffe004 0x1d3ffe0003fffc00

def z723 : W := mkw 0x036c1f701dd13f01 0x606d83ee03ba27e0 0xfffc0ff01ff3ff06 0xdfff81fe03fe7fe0

def z724 : W := mkw 0x01680f6009101e00 0x402d01ec012203c0 0xfbfc0ff01ff01f06 0xdf7f81fe03fe03e0

def z725 : W := mkw 0x857d7e0b1de5f8c3 0xd0afafc163bcbf18 0x803c7e0f00f07ce1 0x50078fc1e01e0f9c

def z726 : W := mkw 0xe097d29fbaaff1ff 0x3c12fa53f755fe3f 0xdc0ff63ff88ff3fb 0xfb81fec7ff11fe7f

def z727 : W := mkw 0x20c69c1a338b294d 0x6418d38346716529 0xa1cf783ce78c6f7c 0x9439ef079cf18def

def z728 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0xf3fc0ff007f00f04 0xde7f81fe00fe01e0

def z729 : W := mkw 0x01fbedaec1000800 0x403f7db5d8200100 0xf3ffffffe7000c05 0xfe7ffffffce00180

def z730 : W := mkw 0x012c000014c00000 0x0025800002980000 0xfbfc09c01ff00006 0xdf7f813803fe0000

def z731 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xb3f009c007700c04 0xd67e013800ee0180

def z732 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffc8ff31ff3ff9f 0xffff91fe63fe7ff3

def z733 : W := mkw 0xe2400ff5a9109fb8 0x7c4801feb52213f7 0x02000fffe0001ff9 0xc04001fffc0003ff

def z734 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0x49ccb0001ff38006 0x0939960003fe7000

def z735 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff00c1fffe0e7 0x3fbffe0183fffc1c

def z736 : W := mkw 0x401140c480344632 0x08022818900688c6 0x863349cc80fc7ff9 0xf0c66939901f8fff

def z737 : W := mkw 0x05fbedaec64a0004 0x80bf7db5d8c94000 0xf3ffffffe7000001 0xfe7ffffffce00000

def z738 : W := mkw 0x8493f08fc22fe0c7 0x90927e11f845fc18 0x0403f00fe00fe0e1 0x20807e01fc01fc1c

def z739 : W := mkw 0xa00412113981b9c9 0x7400824227303739 0xdc0cf633f883fffb 0xfb819ec67f107fff

def z740 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0cf633f88fffff 0xfb819ec67f11ffff

def z741 : W := mkw 0x01680daec0000000 0x002d01b5d8000000 0xf3fcffffe0000001 0xfe7f9ffffc000000

def z742 : W := mkw 0x80400e4109109e80 0x500801c8212213d0 0xfff0cfc39ff3ff9f 0xfffe19f873fe7ff3

def z743 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x69c38e0f1f0f9ce5 0x4d3871c1e3e1f39c

def z744 : W := mkw 0x408280c4821a0634 0x08105018904340c6 0x7fc389cc9f0f9fff 0xeff8713993e1f3ff

def z745 : W := mkw 0xc0d3cecf8b3edef6 0x581a79d9f167dbde 0xcbf0c7c39ff3e318 0x997e18f873fe7c63

def z746 : W := mkw 0x4000004000344632 0x08000008000688c6 0xd40cf633e0fc7fff 0xfa819ec67c1f8fff

def z747 : W := mkw 0x0486900016ef6007 0x8090d20002ddec00 0xfdcff0001fffe006 0x3fb9fe0003fffc00

def z748 : W := mkw 0x05fbedaec66e4006 0x80bf7db5d8cdc800 0xffffffffff7f8007 0xffffffffffeff000

def z749 : W := mkw 0xa1ffffbff881b189 0x343ffff7ff103631 0x2ff309cc1883f39a 0x05fe613983107e73

def z750 : W := mkw 0x437d4fb49de45932 0x686fa9f693bc8b26 0x4dcf463c9f0c60f9 0x29b9e8c793e18c1f

def z751 : W := mkw 0x45bff08496ef6037 0x88b7fe1092ddec06 0xfdfff0009fffe01e 0x3fbffe0013fffc03

def z752 : W := mkw 0x808282010a0a9084 0x1010504021415210 0x7dc38e0f1f0f9ce7 0x6fb871c1e3e1f39c

def z753 : W := mkw 0x836c1f711dd1bf81 0x706d83ee23ba37f0 0xfffcfff31ff3ff87 0xffff9ffe63fe7ff0

def z754 : W := mkw 0xa20412113dc1b989 0x7440824227b83731 0xdc0cf633ff83f39b 0xfb819ec67ff07e73

def z755 : W := mkw 0xa0155295b881b189 0x3402aa52b7103631 0xbe3349cc9883f39b 0xf7c6693993107e73

def z756 : W := mkw 0x036c2f705dd01f00 0x606d85ee0bba03e0 0xfbfc3ff07ff01f06 0xdf7f87fe0ffe03e0

def z757 : W := mkw 0x05bff08ed6ef6007 0x80b7fe11daddec00 0xfdfff63fffffe007 0xffbffec7fffffc00

def z758 : W := mkw 0x00440e5019901f00 0x600881ca033203e0 0xfbfc0ff01ff01f06 0xdf7f81fe03fe03e0

def z759 : W := mkw 0x436c0f701dd01f30 0x686d81ee03ba03e6 0xfbfc0ff01ff01ffe 0xdf7f81fe03fe03ff

def z760 : W := mkw 0x01682daec0000000 0x002d05b5d8000000 0x020c3fffe0000001 0xc04187fffc000000

def z761 : W := mkw 0x0486900016ef6007 0x8090d20002ddec00 0x4dc080001fffe006 0x09b8100003fffc00

def z762 : W := mkw 0x80400e4b09109ec0 0x500801c9612213d8 0x02000fcf00001fe1 0xc04001f9e00003fc

def z763 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0009fffe09f 0x3fbffe0013fffc13

def z764 : W := mkw 0xa3ee9f3b3fcbb9cd 0x747dd3e767f97739 0x49ccb6337f038000 0x093996c66fe07000

def z765 : W := mkw 0x036c0f7a1dd01f00 0x606d81ef43ba03e0 0xfbfc0fff1ff01f07 0xdf7f81ffe3fe03e0

def z766 : W := mkw 0x45bff08496ef6037 0x88b7fe1092ddec06 0xfdfff00c9ffff3ff 0xffbffe0193fffe7f

def z767 : W := mkw 0x836c0f7b1dd09fc0 0x706d81ef63ba13f8 0xffff0fff1ffc1fe7 0xffffe1ffe3ff83fc

def z768 : W := mkw 0xe093d08fa22fe0ff 0x1c127a11f445fc1f 0x0403f00fe00fe0f9 0x20807e01fc01fc1f

def z769 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0x7dcfb0001fffe006 0x2fb9f60003fffc00

def z770 : W := mkw 0x401140c480344632 0x08022818900688c6 0xa63349cc80fc7ffe 0x94c66939901f8fff

def z771 : W := mkw 0x07bff13016ef6107 0xa0f7fe2602ddec20 0xfdfff0301fffe006 0x3fbffe0603fffc00

def z772 : W := mkw 0x036c1d6015d12e01 0x406d83ac02ba25c0 0xfffcf9c01ff3ec06 0x3fff9f3803fe7d80

def z773 : W := mkw 0xa00412113881b189 0x3400824227103631 0xcc0cf633f883f39a 0x99819ec67f107e73

def z774 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdc38e0f1f8f9fe7 0xffb871c1e3f1f3fc

def z775 : W := mkw 0x052c100016ef6007 0x80a5820002ddec00 0x4dcc00001fffe006 0x09b9800003fffc00

def z776 : W := mkw 0x83ae817b16da87c4 0x3075d02f62db50f8 0x863f81ff00ff83e1 0xb0c7f03fe01ff07c

def z777 : W := mkw 0x633d51f4b4f5673b 0x2c67aa3e969eace7 0x823c71f0e0f06318 0x90478e3e1c1e0c63

def z778 : W := mkw 0x036c0d6015d00e00 0x406d81ac02ba01c0 0xa3fc09c007f00c04 0x147f813800fe0180

def z779 : W := mkw 0x05bff08ed6ef6007 0x80b7fe11daddec00 0xfdfff00c1fffe006 0x3fbffe0183fffc00

def z780 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfc0ffe3ff883f39b 0xff81ffc7ff107e73

def z781 : W := mkw 0xa00412113881b189 0x3400824227103631 0xc80cf633f883f399 0xd9019ec67f107e73

def z782 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe0806003 0xfefffffffc100c00

def z783 : W := mkw 0x00c28e000b0a1804 0x401851c001614300 0x7dc38e0c1f0f9ce7 0x6fb871c183e1f39c

def z784 : W := mkw 0x06d3ff700b3f7f07 0xe0da7fee0167efe0 0x0603fff0000fff00 0xe0c07ffe0001ffe0

def z785 : W := mkw 0xa60412513fffff8f 0xf4c0824a27fffff1 0x0c0000001fffff9e 0x0180000003fffff3

def z786 : W := mkw 0x836c0f7b1dd09fc0 0x706d81ef63ba13f8 0xfffc8fff1ff39fe7 0xffff91ffe3fe73fc

def z787 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe00c00e1 0xfefffffffc01801c

def z788 : W := mkw 0x05bff00a16ef6047 0x80b7fe0142ddec08 0xfdfff00c1fffe066 0x3fbffe0183fffc0c

def z789 : W := mkw 0x01fbedaec30a0844 0x403f7db5d8614108 0xf3ffffffe7000001 0xfe7ffffffce00000

def z790 : W := mkw 0xa00010012001a089 0x1400020024003411 0xd40cf633e083f39b 0xfa819ec67c107e73

def z791 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffc0ff3fff3ff9f 0xdfff81fe7ffe7ff3

def z792 : W := mkw 0x01680d2004400000 0x002d01a400880000 0x23f009c007700004 0x047e013800ee0000

def z793 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0x23f009c007f00f04 0x047e013800fe01e0

def z794 : W := mkw 0x0297e2deddd01f00 0x6052fc5bdbba03e0 0x0803f00ffff01f07 0x21007e01fffe03e0

def z795 : W := mkw 0x05ae900016ef6007 0x80b5d20002ddec00 0xfdff80001fffe006 0x3fbff00003fffc00

def z796 : W := mkw 0x012c100014c12001 0x0025820002982400 0xfdfc00001ff3e006 0x1fbf800003fe7c00

def z797 : W := mkw 0x0093e08ec0000000 0x00127c11d8000000 0xf23fffffe0000001 0xfe47fffffc000000

def z798 : W := mkw 0x0093c000022e4006 0x001278000045c800 0x7df380001f7f8006 0x2fbe700003eff000

def z799 : W := mkw 0x0000000000000000 0x0000000000000000 0xf23cfff3e0000001 0xfe479ffe7c000000

def z800 : W := mkw 0x05fbedaec4644002 0x80bf7db5d88c8800 0xf3ffffffe0700001 0xfe7ffffffc0e0000

def z801 : W := mkw 0xa36c0f713dd09f88 0x746d81ee27ba13f1 0xfbfcfff3fff01f9f 0xff7f9ffe7ffe03f3

def z802 : W := mkw 0x473d71f494f56733 0xa8e7ae3e929eace6 0x823c71f080f06318 0x90478e3e101e0c63

def z803 : W := mkw 0x00400c4001100e00 0x40080188002201c0 0xb3f009c007f01f06 0xd67e013800fe03e0

def z804 : W := mkw 0x052c100016ef6007 0x80a5820002ddec00 0xfdfcf0001fffe006 0x3fbf9e0003fffc00

def z805 : W := mkw 0x05bff01016ef6107 0xa0b7fe0202ddec20 0xfdfff0301fffe306 0xbfbffe0603fffc60

def z806 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xa3fc0ff007f01f04 0xd47f81fe00fe03e0

def z807 : W := mkw 0x4493e084822e4036 0x88927c109045c806 0x0003000c000c0060 0x000060018001800c

def z808 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xf3fc0ff007f01f06 0xde7f81fe00fe03e0

def z809 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfff38fcf1f0f9ce7 0xfffe71f9e3e1f39c

def z810 : W := mkw 0x45aeb0c496db2635 0x88b5d61892db64c6 0x4bccb9cc9f039ff9 0xc979973993e073ff

def z811 : W := mkw 0x01fbedaec0244002 0x003f7db5d8048800 0xf7ffffffe0fc7ce7 0xfefffffffc1f8f9c

def z812 : W := mkw 0x016c0e401dd01e00 0x402d81c803ba03c0 0xfbfc0fc01ff01f06 0xdf7f81f803fe03e0

def z813 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe00c0c65 0xfe7ffffffc01818c

def z814 : W := mkw 0x036c0f301dc01900 0x606d81e603b80320 0xfbfc0ff01ff00006 0xdf7f81fe03fe0000

def z815 : W := mkw 0xa00412113881b189 0x3400824227103631 0x4c0cf633f883f39b 0x29819ec67f107e73

def z816 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xf9fff0001ff3e000 0x3f3ffe0003fe7c00

def z817 : W := mkw 0x03680f700d501f00 0x606d01ee01aa03e0 0x23f00ff007700c04 0x047e01fe00ee0180

def z818 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffcfff3fff07f9f 0xffff9ffe7ffe0ff3

def z819 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xcbfc0ff01ff01f00 0xd97f81fe03fe03e0

def z820 : W := mkw 0x0328016004500600 0x0065002c008a00c0 0x23f001c007700004 0x047e003800ee0000

def z821 : W := mkw 0x0493f084c22f6007 0x80927e109845ec00 0x0403f000e00fe000 0x20807e001c01fc00

def z822 : W := mkw 0xa36c0f713dd09f88 0x746d81ee27ba13f1 0xfffc8ff3fff39f9f 0xffff91fe7ffe73f3

def z823 : W := mkw 0x401140c480344632 0x08022818900688c6 0xfff349cc9ffc7fff 0xfffe693993ff8fff

def z824 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffbfff60000000 0xde7ff7ffec000000

def z825 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x79c38e0f1f0f9c66 0x4f3871c1e3e1f38c

def z826 : W := mkw 0x01796da4c0000000 0x002f2db498000000 0xf3fcfff3e0000001 0xfe7f9ffe7c000000

def z827 : W := mkw 0x813963a5cb0a98c4 0x50272c74b9615318 0x8e3c71f0ff0f9ce6 0x91c78e3e1fe1f39c

def z828 : W := mkw 0x80400e0109009880 0x500801c021201310 0x7dc38e0f1f0f9ce7 0x6fb871c1e3e1f39c

def z829 : W := mkw 0x01680d2000000000 0x002d01a400000000 0xf3fcbff360000000 0xde7f97fe6c000000

def z830 : W := mkw 0xc0400e4b09109ef0 0x580801c9612213de 0x00000e0f00001ff9 0x400001c1e00003ff

def z831 : W := mkw 0x036c0d6015d00e00 0x406d81ac02ba01c0 0xfbfc0ff01ff00c06 0xdf7f81fe03fe0180

def z832 : W := mkw 0x80c28f2b4b0a98c4 0x501851e569615318 0x7dc38e3f7f0f9ce7 0x6fb871c7efe1f39c

def z833 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfdccf633ff83f39f 0xffb99ec67ff07e73

def z834 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x29f300001f7f8004 0x053e600003eff000

def z835 : W := mkw 0x076c3f701dd13f01 0xe0ed87ee03ba27e0 0xfbfc3ff01ff01f06 0xdf7f87fe03fe03e0

def z836 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xffffffffffffe007 0xfffffffffffffc00

def z837 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbff0ffc1ff01f07 0xff7fe1ff83fe03e0

def z838 : W := mkw 0xc493f08f822fe0f7 0x98927e11f045fc1e 0x0403f00f800fe0f9 0x20807e01f001fc1f

def z839 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0xfbfc09f01ff00f06 0x9f7f813e03fe01e0

def z840 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xcbfc07f01ff01f06 0x997f80fe03fe03e0

def z841 : W := mkw 0xe20412513df5ffbb 0x7c40824a27bebff7 0x0c0000001ffffffe 0x0180000003ffffff

def z842 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x2dc3880f1f0f9ce7 0x25b87101e3e1f39c

def z843 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xffff0ff01ffc1f06 0xffffe1fe03ff83e0

def z844 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff633fffff39f 0xffbffec67ffffe73

def z845 : W := mkw 0xa0c28e1b2b0a99cc 0x741851c365615339 0xfdcffe3fff0f9fff 0xffb9ffc7ffe1f3ff

def z846 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc4ff09ff01f07 0xff7f89fe13fe03e0

def z847 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0xf3fcfff3e0000001 0xfe7f9ffe7c000000

def z848 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffcfff01ff3ff9e 0xffff9ffe03fe7ff3

def z849 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x23f009c007f01f06 0x047e013800fe03e0

def z850 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0xfdffb0001fff8006 0x3fbff60003fff000

def z851 : W := mkw 0x01fbedaec20a0044 0x003f7db5d8414008 0xf3ffffffe00c0061 0xfe7ffffffc01800c

def z852 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x7dc3880c1f0f9ce7 0x6fb8710183e1f39c

def z853 : W := mkw 0x236c1f703dd13f09 0x646d83ee07ba27e1 0xfbfc3ff07ff01f06 0xdf7f87fe0ffe03e0

def z854 : W := mkw 0x032c03701dd01f00 0x6065806e03ba03e0 0xfbfc01f01ff01f06 0x9f7f803e03fe03e0

def z855 : W := mkw 0xa12c12513cd1b789 0x3425824a279a36f1 0xfffcfff3fff3ff9f 0xffff9ffe7ffe7ff3

def z856 : W := mkw 0x016c0f301cc01100 0x202d81e603980220 0xfbfc0ff01ff01306 0xdf7f81fe03fe0260

def z857 : W := mkw 0xa00412113881b189 0x3400824227103631 0x4c0cf633f803f399 0xe9819ec67f007e73

def z858 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x03f001c007700000 0x007e003800ee0000

def z859 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfbfcbff3fff39f9f 0xdf7f97fe7ffe73f3

def z860 : W := mkw 0x036c0f601dd01e00 0x406d81ec03ba03c0 0xfbfc0fc01ff01c06 0x5f7f81f803fe0380

def z861 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x823fffffe0000001 0xf047fffffc000000

def z862 : W := mkw 0x01bfc00016ee4006 0x0037f80002ddc800 0xfdffc0001fffe006 0x3fbff80003fffc00

def z863 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xcbfcf7f3fff3e318 0x997f9efe7ffe7c63

def z864 : W := mkw 0x401140c480344632 0x08022818900688c6 0xfe33c9cc98ffffff 0xffc67939931fffff

def z865 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc09c01ff01f06 0x1f7f813803fe03e0

def z866 : W := mkw 0x8082800b020a80c4 0x1010500160415018 0x7dc3880f1f0f9ce7 0x6fb87101e3e1f39c

def z867 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff6031fffe007 0x7fbffec063fffc00

def z868 : W := mkw 0xa20412513dd1bf89 0x7440824a27ba37f1 0x080000001ff39f06 0x0100000003fe73e0

def z869 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xfdfff00c9fffe007 0x3fbffe0193fffc00

def z870 : W := mkw 0x41eaad6a40344632 0x083d55ad480688c6 0x45ccb63360fc7ffe 0x08b996c66c1f8fff

def z871 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x7bf00fc01ff01f06 0x4f7e01f803fe03e0

def z872 : W := mkw 0x01fbedaec4400000 0x003f7db5d8880000 0xf3ffffffe7700005 0xfe7ffffffcee0000

def z873 : W := mkw 0x808282010b0a98c4 0x5010504021615318 0x7dc3880c1f0f9ce7 0x6fb8710183e1f39c

def z874 : W := mkw 0x0097d00012af6007 0x0012fa000255ec00 0xfdfff0001fffe006 0x3fbffe0003fffc00

def z875 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xa3f009c007f00f04 0x947e013800fe01e0

def z876 : W := mkw 0xa36c0f7b3dd09fc8 0x746d81ef67ba13f9 0xfbfc0ffffff01fff 0xdf7f81fffffe03ff

def z877 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0x63fcbff360000000 0x0c7f97fe6c000000

def z878 : W := mkw 0x03680d6a05500e40 0x406d01ad40aa01c8 0x23f009cc07700c64 0x047e013980ee018c

def z879 : W := mkw 0xa00412113981b989 0x7400824227303731 0xdc0cf633ff83ff9f 0xfb819ec67ff07ff3

def z880 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x6dffb0001fffe006 0x0dbff60003fffc00

def z881 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfbfcfff3fff39f07 0xff7f9ffe7ffe73e0

def z882 : W := mkw 0x01794da480000000 0x002f29b490000000 0xf3ffffffe0000001 0xfe7ffffffc000000

def z883 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0x69fcb0001f738004 0x0d3f960003ee7000

def z884 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb63349cc00fc7ffe 0x36c66939801f8fff

def z885 : W := mkw 0x05bfe00016ee4006 0x80b7fc0002ddc800 0xfdff80001fff8006 0x3fbff00003fff000

def z886 : W := mkw 0x05bff12016ef6007 0x80b7fe2402ddec00 0xfffff1f01fffe006 0xbffffe3e03fffc00

def z887 : W := mkw 0xa36c0f713dd09f88 0x746d81ee27ba13f1 0xfffc4ff3fff07f9f 0xffff89fe7ffe0ff3

def z888 : W := mkw 0x05fbedaec66e4006 0x80bf7db5d8cdc800 0xf7ffffffe7fc6007 0xfefffffffcff8c00

def z889 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0x23fc09f007700c04 0x047f813e00ee0180

def z890 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdff00001fffe006 0x1fbfe00003fffc00

def z891 : W := mkw 0x04441daed6ef6007 0x808883b5daddec00 0x0e000fffffffe007 0xc1c001fffffffc00

def z892 : W := mkw 0x036c0d6015d00e00 0x406d81ac02ba01c0 0x2bf009c01ff00c06 0x057e013803fe0180

def z893 : W := mkw 0x8082804b021a86c4 0x10105009604350d8 0xb63389cf00ff9fe7 0xf6c67139e01ff3fc

def z894 : W := mkw 0x0497f08ed2af6007 0x8092fe11da55ec00 0xdc0ff63ff88fe003 0xfb81fec7ff11fc00

def z895 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffc0ff01ffc1fe6 0xdfff81fe03ff83fc

def z896 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xfffc0ff01ff39f86 0xdfff81fe03fe73f0

def z897 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe08c7fff 0xfefffffffc118fff

def z898 : W := mkw 0xa20412513991bf89 0x7440824a273237f1 0x0c0000001883ff9a 0x0180000003107ff3

def z899 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xb3f009c007f00c06 0x167e013800fe0180

def z900 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc3880c1f0f9ce6 0x2fb8710183e1f39c

def z901 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dcfbe3f7f0f9ce7 0x6fb9f7c7efe1f39c

def z902 : W := mkw 0x01fbedaec30a0844 0x403f7db5d8614108 0xf7ffffffe70c1ce7 0xfefffffffce1839c

def z903 : W := mkw 0x05bff00a16ef6007 0x80b7fe0142ddec00 0xfdfff00f1fffe007 0x3fbffe01e3fffc00

def z904 : W := mkw 0xa0c28e0b2b0a98cc 0x541851c165615319 0x7dc38e0fff0f9cff 0x6fb871c1ffe1f39f

def z905 : W := mkw 0x01bbe1aec0000000 0x00377c35d8000000 0xd23ff7ffe0000001 0xfa47fefffc000000

def z906 : W := mkw 0x4493e084822e4036 0x88927c109045c806 0x0403400c800c60f9 0x2080680190018c1f

def z907 : W := mkw 0x053d700016ef6007 0x80a7ae0002ddec00 0xfdfc70001fffe006 0x1fbf8e0003fffc00

def z908 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdcffe0f1f0f9ce7 0x7fb9ffc1e3e1f39c

def z909 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffc7ff0fff3ff9e 0xdfff8ffe1ffe7ff3

def z910 : W := mkw 0x012c004014d00600 0x00258008029a00c0 0xfbfc01c01ff00306 0x9f7f803803fe0060

def z911 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0x0dc000001fffe006 0x01b8000003fffc00

def z912 : W := mkw 0x236c1f703dd13f09 0x646d83ee07ba27e1 0xfffc7ff0fff07f9f 0xffff8ffe1ffe0ff3

def z913 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xabfc09f01ff01f06 0x957f813e03fe03e0

def z914 : W := mkw 0x41fbedaec0000030 0x083f7db5d8000006 0xf3ffffffe00000f9 0xfe7ffffffc00001f

def z915 : W := mkw 0x032c02501dd01f00 0x6065804a03ba03e0 0xfbfc09c01ff01f06 0xdf7f813803fe03e0

def z916 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc8ff31ff01f07 0xff7f91fe63fe03e0

def z917 : W := mkw 0x00c28e0a0b0a1844 0x401851c141614308 0x7dc38e0c1f0f9c66 0x6fb871c183e1f38c

def z918 : W := mkw 0x0493e08ec22e4006 0x80927c11d845c800 0x0003f00fe00c0001 0x20007e01fc018000

def z919 : W := mkw 0xe0400edfa9109ff8 0x7c0801dbf52213ff 0x02000fffe0001ff9 0xc04001fffc0003ff

def z920 : W := mkw 0x00828000022e4006 0x001050000045c800 0x7dc380001fffe006 0x2fb8700003fffc00

def z921 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x69c3880c1f0f8c64 0x0d38710183e1f18c

def z922 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfbfc7ff3fff07f9f 0xdf7f8ffe7ffe0ff3

def z923 : W := mkw 0x01796daec0000000 0x002f2db5d8000000 0xf3fc7fffe0000001 0xde7f8ffffc000000

def z924 : W := mkw 0x03680f700d501f00 0x606d01ee01aa03e0 0xb3f00ff007f01f06 0xd67e01fe00fe03e0

def z925 : W := mkw 0x05bff084d6ef6007 0x80b7fe109addec00 0xfdfff000ffffe006 0x3fbffe001ffffc00

def z926 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x63ffffffe0000001 0x2c7ffffffc000000

def z927 : W := mkw 0x05bff1a4d6ef6007 0x80b7fe349addec00 0xfffff7f3ffffe007 0xfffffefe7ffffc00

def z928 : W := mkw 0x401140c480344632 0x08022818900688c6 0x263349cc80fc7fff 0x24c66939901f8fff

def z929 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xfffcfff3fff39f87 0xffff9ffe7ffe73f0

def z930 : W := mkw 0x80c28c0b030a88c4 0x5018518160615118 0x7dc3880f1f0f8ce7 0x2fb87101e3e1f19c

def z931 : W := mkw 0x036c0d6015d00e00 0x406d81ac02ba01c0 0x6bfc09c01f700c04 0x0d7f813803ee0180

def z932 : W := mkw 0xa00412113881b189 0x3400824227103631 0xd80cf633f883f31a 0xdb019ec67f107e63

def z933 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xf3fc09c007700c04 0x1e7f813800ee0180

def z934 : W := mkw 0x01ae800016ca0004 0x0035d00002d94000 0xf9fc80001ff38006 0x1f3f900003fe7000

def z935 : W := mkw 0xa497f29ffaaff18f 0xb492fe53ff55fe31 0xdc0ff63ff88ff39b 0xfb81fec7ff11fe73

def z936 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x73f00fc007700c04 0x4e7e01f800ee0180

def z937 : W := mkw 0x0011408480000000 0x0002281090000000 0xd23cf7f3e0000001 0xfa479efe7c000000

def z938 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0x2df300001f7f8006 0x05be600003eff000

def z939 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe0006099 0xfefffffffc000c13

def z940 : W := mkw 0x83680f610d509e80 0x506d01ec21aa13d0 0x7ff08fc31f739c87 0x6ffe11f863ee7390

def z941 : W := mkw 0xa0c28e1b2b0a99cc 0x741851c365615339 0xfdc3ce3fff8fffff 0xffb879c7fff1ffff

def z942 : W := mkw 0x82400fffc9109fc0 0x704801fff92213f8 0x02000fffe0001fe1 0xc04001fffc0003fc

def z943 : W := mkw 0xa5bbe2112e6ed18e 0xb4b77c4225cdda31 0x21f30633e77c139d 0xc43e60c67cef8273

def z944 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x49fcb0001f738000 0x093f960003ee7000

def z945 : W := mkw 0x80400e010b0a98c4 0x500801c021615318 0x7dc30e0c1f0f9ce7 0x6fb861c183e1f39c

def z946 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xfffffffff8038003 0xffffffffff007000

def z947 : W := mkw 0x05bff00a56ef6007 0x80b7fe014addec00 0xfdfff0037fffe006 0x3fbffe006ffffc00

def z948 : W := mkw 0x25bff00036ef600f 0x84b7fe0006ddec01 0xfdfff000ffffe01e 0x3fbffe001ffffc03

def z949 : W := mkw 0xa2400fffe9109f88 0x744801fffd2213f1 0x02000fffe0001f99 0xc04001fffc0003f3

def z950 : W := mkw 0x052c100016ef6007 0x80a5820002ddec00 0x2df000001fffe006 0x05be000003fffc00

def z951 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfffff9c01fffe006 0xffffff3803fffc00

def z952 : W := mkw 0x01fbedaec20a0004 0x003f7db5d8414000 0xf3ffffffe70c0005 0xfe7ffffffce18000

def z953 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0xfdf3c0001fffe006 0x3fbe780003fffc00

def z954 : W := mkw 0xa00412113881b189 0x3400824227103631 0xd80cf633f883e319 0xfb019ec67f107c63

def z955 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc3ce0f9f0ffcff 0x6fb879c1f3e1ff9f

def z956 : W := mkw 0x053d700014e56003 0x80a7ae00029cac00 0xfdfcf0001ff3e006 0x3fbf9e0003fe7c00

def z957 : W := mkw 0x03680f700d501f00 0x606d01ee01aa03e0 0xf3fc0ff007701f04 0xde7f81fe00ee03e0

def z958 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0x823c77f3e0000001 0xd0478efe7c000000

def z959 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff8001ffffc06 0x7fbfff0003ffff80

def z960 : W := mkw 0xa00412113881b189 0x3400824227103631 0xcc0cf633f883e399 0xb9819ec67f107c73

def z961 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x3dc3080c1f0f9ce7 0x67b8610183e1f39c

def z962 : W := mkw 0x41fbedaec0244032 0x083f7db5d8048806 0xf7ffffffe0fc60ff 0xfefffffffc1f8c1f

def z963 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xf9fcf0001ff3e006 0x1f3f9e0003fe7c00

def z964 : W := mkw 0x032c017014d00700 0x2065802e029a00e0 0xfbfc09f01ff01f06 0xdf7f813e03fe03e0

def z965 : W := mkw 0x01fbedaec22e4006 0x003f7db5d845c800 0xffffffffffffe007 0xfffffffffffffc00

def z966 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xf9fff0001f7f8004 0x3f3ffe0003eff000

def z967 : W := mkw 0x05bff1aed6ef6007 0x80b7fe35daddec00 0xfffff1ffffffe007 0xbffffe3ffffffc00

def z968 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x7bfc0ff01f701c06 0x4f7f81fe03ee0380

def z969 : W := mkw 0xa493f08fe22fe08f 0x94927e11fc45fc11 0x0403f00fe00fe099 0x20807e01fc01fc13

def z970 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff6337fffe006 0x3fbffec66ffffc00

def z971 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xa3fc09f007700c04 0x947f813e00ee0180

def z972 : W := mkw 0xc2400fff89109ff0 0x784801fff12213fe 0x02000fff80001ff9 0xc04001fff00003ff

def z973 : W := mkw 0x012c02501cd01700 0x2025804a039a02e0 0xfbfc0ff01ff01f06 0xdf7f81fe03fe03e0

def z974 : W := mkw 0xc0400ecf89109ef0 0x580801d9f12213de 0x02000fcf00001ce1 0x404001f9e000039c

def z975 : W := mkw 0x01bbe000022e4006 0x00377c000045c800 0xfdfff0001fffe006 0x3fbffe0003fffc00

def z976 : W := mkw 0x012c000016ca0004 0x0025800002d94000 0xfdfc00001fff8006 0x1fbf800003fff000

def z977 : W := mkw 0xc093e08fc22ec0f6 0x18127c11f845d81e 0x0403f00fe00fe0f9 0x20807e01fc01fc1f

def z978 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0xb3fc09f007f01f06 0xd67f813e00fe03e0

def z979 : W := mkw 0x036c0f7a5dd01f00 0x606d81ef4bba03e0 0xfbfc0ff37ff01f06 0xdf7f81fe6ffe03e0

def z980 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x6dc38e0f1f0f9ce6 0x0db871c1e3e1f39c

def z981 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ff01f700c04 0xdf7f81fe03ee0180

def z982 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xffffffffffffffff 0xffffffffffffffff

def z983 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffc4ff09ff3ff9f 0xffff89fe13fe7ff3

def z984 : W := mkw 0x41fbedaec0244032 0x083f7db5d8048806 0xf3ffffffe00c0061 0xfe7ffffffc01800c

def z985 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff80c1fffe007 0x7fbfff0183fffc00

def z986 : W := mkw 0x4093c084822e4036 0x081278109045c806 0x0403c00c800fe0f9 0x208078019001fc1f

def z987 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xd3fcf7f3e0000001 0xfa7f9efe7c000000

def z988 : W := mkw 0x0493f084822f6007 0x80927e109045ec00 0x0403f00c800fe001 0x20807e019001fc00

def z989 : W := mkw 0x82400f7109109fc0 0x704801ee212213f8 0x02000ff000001fe0 0xc04001fe000003fc

def z990 : W := mkw 0x83680f6b0d509ec0 0x506d01ed61aa13d8 0x23f00fcf07701ce5 0x447e01f9e0ee039c

def z991 : W := mkw 0x82400e5b09109fc0 0x704801cb612213f8 0x00000e0f00001fe1 0x400001c1e00003fc

def z992 : W := mkw 0x0493f000022f6007 0x80927e000045ec00 0xfdf3f0001fffe006 0x3fbe7e0003fffc00

def z993 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfc3cf633f8f3f39f 0xff879ec67f1e7e73

def z994 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0001ffff306 0xffbffe0003fffe60

def z995 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb63309cc00fc7ffe 0xd6c66139801f8fff

def z996 : W := mkw 0xa20412513fdbbfcd 0x7440824a27fb77f9 0x0c0000001ffffffe 0x0180000003ffffff

def z997 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfcfff01ff01f06 0xff7f9ffe03fe03e0

def z998 : W := mkw 0x8000020108009080 0x1000004021001210 0xdc0cf633f883f39b 0xfb819ec67f107e73

def z999 : W := mkw 0x000001a4c0000000 0x0000003498000000 0xd20cf7f3e0000001 0xfa419efe7c000000

def z1000 : W := mkw 0xa00412113cc1b189 0x3400824227983631 0xdc0cf633fff3f39f 0xfb819ec67ffe7e73

def z1001 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x2dc3080c1f0f8c66 0x05b8610183e1f18c

def z1002 : W := mkw 0x236c0f703dd01f08 0x646d81ee07ba03e1 0xfbfc0ff0fff01f1e 0xdf7f81fe1ffe03e3

def z1003 : W := mkw 0x0128004004500600 0x00250008008a00c0 0xb3f009c007f01f06 0xd67e013800fe03e0

def z1004 : W := mkw 0x82c28f3b0b0a99c4 0x705851e761615338 0x7dc38e3f1f0f9ce7 0x6fb871c7e3e1f39c

def z1005 : W := mkw 0x80c28e1b0b0a99c4 0x701851c361615338 0x7dc38e3f1f0f9fe7 0xefb871c7e3e1f3fc

def z1006 : W := mkw 0x25bff01036ef610f 0xa4b7fe0206ddec21 0xfdfff0001fffe31e 0x3fbffe0003fffc63

def z1007 : W := mkw 0x05fbedaec22e4006 0x80bf7db5d845c800 0xf3ffffffe00c0001 0xfe7ffffffc018000

def z1008 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff6301fffe006 0xffbffec603fffc00

def z1009 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ff01ff00300 0xdf7f81fe03fe0060

def z1010 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0cfe3ff883fffb 0xfb819fc7ff107fff

def z1011 : W := mkw 0x012c000014c00000 0x0025800002980000 0xfdfc80001ff38006 0x3fbf900003fe7000

def z1012 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffc0ff01ff07f9e 0xdfff81fe03fe0ff3

def z1013 : W := mkw 0x03680f600d501e00 0x406d01ec01aa03c0 0x6bf00fc01f700c04 0x0d7e01f803ee0180

def z1014 : W := mkw 0x453d70c494f56633 0x88a7ae18929eacc6 0x823c71c000f06000 0x10478e38001e0c00

def z1015 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc38e3fff0f9ce7 0xefb871c7ffe1f39c

def z1016 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0x43ccbff360000000 0xc87997fe6c000000

def z1017 : W := mkw 0xa20412513cd1b789 0x3440824a279a36f1 0x0c00000018f3f39a 0x01800000031e7e73

def z1018 : W := mkw 0x036c0d6015d00e00 0x406d81ac02ba01c0 0xfbfc09c01ff01f06 0xdf7f813803fe03e0

def z1019 : W := mkw 0x00c28c0a030a0844 0x4018518140614108 0x7dc38e0f1f0f8c67 0x6fb871c1e3e1f18c

def z1020 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdc3ce0f9f0f9ce7 0xffb879c1f3e1f39c

def z1021 : W := mkw 0x653d70d4b4f5673b 0xaca7ae1a969eace7 0x823c71f0e0f06318 0x90478e3e1c1e0c63

def z1022 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ff09ff01f9f 0xdf7f81fe13fe03f3

def z1023 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0801303 0xfe7ffffffc100260

def z1024 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdf38e0f1fff9ce7 0x7fbe71c1e3fff39c

def z1025 : W := mkw 0x4093c08e822e4076 0x08127811d045c80e 0x0003000c000c0060 0x000060018001800c

def z1026 : W := mkw 0x01bff00014c12001 0x0037fe0002982400 0xfdfff0001ff3e006 0x3fbffe0003fe7c00

def z1027 : W := mkw 0x0000008480000000 0x0000001090000000 0xd20cffffe0000001 0xfa419ffffc000000

def z1028 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff003ffffe007 0x3fbffe007ffffc00

def z1029 : W := mkw 0xa16c1f313cc1b189 0x342d83e627983631 0xfffcfff3fff3f39f 0xffff9ffe7ffe7e73

def z1030 : W := mkw 0x41fbedeec33e4e76 0x483f7dbdd867c9ce 0x23f309cc077c0c64 0x047e613980ef818c

def z1031 : W := mkw 0x05bff08ed6ef6007 0x80b7fe11daddec00 0xfffff9cfffffe007 0xffffff39fffffc00

def z1032 : W := mkw 0x41fbedaec0244032 0x083f7db5d8048806 0xf7ffffffe08c73fb 0xfefffffffc118e7f

def z1033 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffcbff37ff39f87 0xffff97fe6ffe73f0

def z1034 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff80c9fffffff 0xffbfff0193ffffff

def z1035 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfbfc0ff01ff39f06 0xdf7f81fe03fe73e0

def z1036 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x6dc38e0f1f0f8ce5 0x2db871c1e3e1f19c

def z1037 : W := mkw 0x036c1f701dd13f01 0x606d83ee03ba27e0 0xfffcfff09ff3ff9f 0xffff9ffe13fe7ff3

def z1038 : W := mkw 0xe00412513bbfffff 0x7c00824a2777ffff 0x0c0000001ffffffe 0x0180000003ffffff

def z1039 : W := mkw 0x0086800016ca0004 0x0010d00002d94000 0x7dc380001fff8006 0x2fb8700003fff000

def z1040 : W := mkw 0x41fbedaec0244032 0x083f7db5d8048806 0xf3ffffffe0006019 0xfe7ffffffc000c03

def z1041 : W := mkw 0x01fbedaec20a0004 0x003f7db5d8414000 0xfbffffffff038001 0xff7fffffffe07000

def z1042 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xfbfc0ff31ff01f87 0xdf7f81fe63fe03f0

def z1043 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xcdfff0001fffe000 0x39bffe0003fffc00

def z1044 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0xfdfcf0001ff3e006 0x3fbf9e0003fe7c00

def z1045 : W := mkw 0x013d500014e56003 0x0027aa00029cac00 0xfdfff0001fffe006 0x3fbffe0003fffc00

def z1046 : W := mkw 0x82400f7109109f80 0x704801ee212213f0 0x02000ff300001f81 0xc04001fe600003f0

def z1047 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x2dc30e0f1f0f9ce7 0x45b861c1e3e1f39c

def z1048 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0x49ccb0001ff3e000 0x0939960003fe7c00

def z1049 : W := mkw 0x03680f600d501e00 0x406d01ec01aa03c0 0xfbfc0ff01f701c06 0xdf7f81fe03ee0380

def z1050 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xadff70001fffe006 0x15bfee0003fffc00

def z1051 : W := mkw 0x036c1f701dd13f01 0x606d83ee03ba27e0 0xfbfcbff01ff39f06 0xdf7f97fe03fe73e0

def z1052 : W := mkw 0x0128012000000000 0x0025002400000000 0xd23cf7f3e0000001 0xfa479efe7c000000

def z1053 : W := mkw 0x0128004004500600 0x00250008008a00c0 0x23f009c007700c04 0x047e013800ee0180

def z1054 : W := mkw 0xe004125138b5f7bb 0x3c00824a2716bef7 0x0c00000018f3f39a 0x01800000031e7e73

def z1055 : W := mkw 0x0493e08ec22e4006 0x80927c11d845c800 0x0003000c000c0000 0x0000600180018000

def z1056 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0009fffe31e 0xbfbffe0013fffc63

def z1057 : W := mkw 0x0486900016ef6007 0x8090d20002ddec00 0x2dc300001fffe006 0x05b8600003fffc00

def z1058 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb633f9cfe0fc7fff 0xf6c67f39fc1f8fff

def z1059 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0xfdfff0001f7f8006 0x3fbffe0003eff000

def z1060 : W := mkw 0x03fbedaec5400800 0x407f7db5d8a80100 0xf3ffffffe7000001 0xfe7ffffffce00000

def z1061 : W := mkw 0x80514e0b0924d8c2 0x500a29c161249b18 0xb4334e0f00fc7ce7 0x768669c1e01f8f9c

def z1062 : W := mkw 0x05bff1a4d6ef6007 0x80b7fe349addec00 0xfffff9fcffffe007 0xffffff3f9ffffc00

def z1063 : W := mkw 0x4493f08ec22f6037 0x88927e11d845ec06 0x0403f00fe00fe0f9 0x20807e01fc01fc1f

def z1064 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x43cfffffe0000001 0xe879fffffc000000

def z1065 : W := mkw 0x01aa8000064a0004 0x0035500000c94000 0x7df380001f7f8006 0x2fbe700003eff000

def z1066 : W := mkw 0x2004101030812109 0x2400820206102421 0xdc0cf633f883e31b 0xfb819ec67f107c63

def z1067 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x2bf00ff01ff01f06 0xc57e01fe03fe03e0

def z1068 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xfffff9cc9ffff39f 0xffffff3993fffe73

def z1069 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3fcfff3e0000000 0xde7f9ffe7c000000

def z1070 : W := mkw 0x01680d2004400000 0x002d01a400880000 0xf3fc0ff007700004 0xde7f81fe00ee0000

def z1071 : W := mkw 0x40514e8489245832 0x480a29d091248b06 0x7dc34e0c9f0c7cff 0x6fb869c193e18f9f

def z1072 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdc3ce0f1f8ffce7 0x7fb879c1e3f1ff9c

def z1073 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xfbfc8ff31ff39f06 0xdf7f91fe63fe73e0

def z1074 : W := mkw 0x00c28c0a020a0004 0x0018518140414000 0x7dc38e0f1f0f9ce7 0x6fb871c1e3e1f39c

def z1075 : W := mkw 0x0493f08ec22f6007 0x80927e11d845ec00 0x0403f00c000fe000 0x20807e018001fc00

def z1076 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb6334fffe0fc7fff 0xf6c669fffc1f8fff

def z1077 : W := mkw 0x01fbed2a40000000 0x003f7da548000000 0xf3fffff360000000 0xfe7ffffe6c000000

def z1078 : W := mkw 0x032c017014d00700 0x2065802e029a00e0 0xa3fc01f007f00304 0x947f803e00fe0060

def z1079 : W := mkw 0x45fbedeec67e4636 0x88bf7dbdd8cfc8c6 0x23f309cc077c0c64 0x047e613980ef818c

def z1080 : W := mkw 0x01ea8d2a00000000 0x003d51a540000000 0xf3ffffffe0000001 0xfe7ffffffc000000

def z1081 : W := mkw 0x0000004000100600 0x00000008000200c0 0xfbf009c01ff01f06 0xdf7e013803fe03e0

def z1082 : W := mkw 0x25bff1b4f6ef610f 0xa4b7fe369eddec21 0xfffff1f0ffffe31e 0xbffffe3e1ffffc63

def z1083 : W := mkw 0x0404100016ef6007 0x8080820002ddec00 0x7dc000001fffe006 0x0fb8000003fffc00

def z1084 : W := mkw 0x01eaadaec0000000 0x003d55b5d8000000 0x43ccb7f3e0000000 0x887996fe7c000000

def z1085 : W := mkw 0xa00410113081a189 0x3400820226103431 0xd40cf633e083e399 0xfa819ec67c107c73

def z1086 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0xddccf0001fffe006 0x3bb99e0003fffc00

def z1087 : W := mkw 0x05fbedaec76e4846 0xc0bf7db5d8edc908 0xf3ffffffe77c0c65 0xfe7ffffffcef818c

def z1088 : W := mkw 0x401160c4c0344632 0x08022c18980688c6 0xb63379cce0fc7fff 0xf6c66f399c1f8fff

def z1089 : W := mkw 0xa00012112801b189 0x3400024225003631 0xd40cf633e003f399 0xfa819ec67c007e73

def z1090 : W := mkw 0x236c1f703dd13f09 0x646d83ee07ba27e1 0xfbfcfff3fff07f1f 0xff7f9ffe7ffe0fe3

def z1091 : W := mkw 0x01eaadaec0000000 0x003d55b5d8000000 0xd3ccffffe0000001 0xfa799ffffc000000

def z1092 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfbfcfff3fff3ff1e 0xdf7f9ffe7ffe7fe3

def z1093 : W := mkw 0xa36c0f713dd09f88 0x746d81ee27ba13f1 0xfbfc0ff37ff01f06 0xdf7f81fe6ffe03e0

def z1094 : W := mkw 0x016c0d2014c00000 0x002d81a402980000 0xfbfc09c01ff00006 0x1f7f813803fe0000

def z1095 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0ff63ff88ff3fb 0xfb81fec7ff11fe7f

def z1096 : W := mkw 0x032c017014d00700 0x2065802e029a00e0 0xcbfc01f01ff00300 0x997f803e03fe0060

def z1097 : W := mkw 0xa0c28e1b2b0a99cc 0x741851c365615339 0x7dc38e0f1f0f9fff 0x6fb871c1e3e1f3ff

def z1098 : W := mkw 0x01bbe1a4c0000000 0x00377c3498000000 0xf3fff7f3e0000001 0xfe7ffefe7c000000

def z1099 : W := mkw 0x236c1f703dd13f09 0x646d83ee07ba27e1 0xfbfc0ff01ff07f1e 0xdf7f81fe03fe0fe3

def z1100 : W := mkw 0x01ae900016cb2005 0x0035d20002d96400 0xfdfff0001fffe006 0x3fbffe0003fffc00

def z1101 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x29c3080c1f0f8c64 0x0538610183e1f18c

def z1102 : W := mkw 0x00828000020a0004 0x0010500000414000 0xfdf380001fff8006 0x3fbe700003fff000

def z1103 : W := mkw 0x45bff08496ef6037 0x88b7fe1092ddec06 0xfdfff80c9ffffcff 0x7fbfff0193ffff9f

def z1104 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x6bfc0ff01f701f04 0xcd7f81fe03ee03e0

def z1105 : W := mkw 0xa00412113881b189 0x3400824227103631 0xdc0cf633f883e31a 0xbb819ec67f107c63

def z1106 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xffff4ffc9ffc7fff 0xffffe9ff93ff8fff

def z1107 : W := mkw 0x401140c480344632 0x08022818900688c6 0xf633cfcf80fc7fff 0xfec679f9f01f8fff

def z1108 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc38e0f1f0f8c66 0x2fb871c1e3e1f18c

def z1109 : W := mkw 0x00d3cc8e80000000 0x001a7991d0000000 0xf3ffffffe0000001 0xfe7ffffffc000000

def z1110 : W := mkw 0x03680f600d501e00 0x406d01ec01aa03c0 0xfbf00fc01ff01f06 0xdf7e01f803fe03e0

def z1111 : W := mkw 0x036c0d7015d00f00 0x606d81ae02ba01e0 0x83fc01f007f00300 0x907f803e00fe0060

def z1112 : W := mkw 0xa36c0f713dd09f88 0x746d81ee27ba13f1 0xfbfc0ff01ff01f9e 0xdf7f81fe03fe03f3

def z1113 : W := mkw 0x00400daec0000000 0x000801b5d8000000 0x820c7fffe0000001 0xd0418ffffc000000

def z1114 : W := mkw 0x836c0f711dd09fc0 0x706d81ee23ba13f8 0xfbfc0ff01ff01fe6 0xdf7f81fe03fe03fc

def z1115 : W := mkw 0x4093c08e822e4076 0x08127811d045c80e 0x0403400c800c60f9 0x2080680190018c1f

def z1116 : W := mkw 0x05bff00016cb2005 0x80b7fe0002d96400 0xf9fff0001ff38006 0x3f3ffe0003fe7000

def z1117 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0xc3fcb7f360000000 0x987f96fe6c000000

def z1118 : W := mkw 0x0497f00016ef6007 0x8092fe0002ddec00 0x7dc3f0001fffe006 0x2fb87e0003fffc00

def z1119 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x6dfff0001f7fe004 0x2dbffe0003effc00

def z1120 : W := mkw 0x01bbe08480000000 0x00377c1090000000 0xf3ffffffe0000001 0xfe7ffffffc000000

def z1121 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbff0ffc1ffc1f66 0xdf7fe1ff83ff83ec

def z1122 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xfbffffffff000007 0xff7fffffffe00000

def z1123 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfc0ff633f88ff39f 0xff81fec67f11fe73

def z1124 : W := mkw 0xa2400f7129109f88 0x744801ee252213f1 0x02000ff360001f00 0xc04001fe6c0003e0

def z1125 : W := mkw 0x05bff12056ef6007 0x80b7fe240addec00 0xfdfff0307fffe006 0x3fbffe060ffffc00

def z1126 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ff01ff00c06 0x1f7f81fe03fe0180

def z1127 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ff3fff01f07 0xdf7f81fe7ffe03e0

def z1128 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x23f00ff007700c04 0xc47e01fe00ee0180

def z1129 : W := mkw 0x05aeb00016cb2005 0x80b5d60002d96400 0xc9fcb0001ff38000 0x193f960003fe7000

def z1130 : W := mkw 0x25bff01036ef610f 0xa4b7fe0206ddec21 0xfdfff0307fffe006 0x3fbffe060ffffc00

def z1131 : W := mkw 0xa00412513891b789 0x3400824a271236f1 0x0c00000018f3ff9e 0x01800000031e7ff3

def z1132 : W := mkw 0x032c016014d00600 0x0065802c029a00c0 0xfbfc01c01ff00006 0x1f7f803803fe0000

def z1133 : W := mkw 0x0497d00016ef6007 0x8092fa0002ddec00 0xfdf3c0001fffe006 0x3fbe780003fffc00

def z1134 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0001ffff39e 0x3fbffe0003fffe73

def z1135 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3fff7f3e0000000 0xbe7ffefe7c000000

def z1136 : W := mkw 0x03680d7005500f00 0x606d01ae00aa01e0 0x23f009f007700f04 0x847e013e00ee01e0

def z1137 : W := mkw 0x80c2ae0b4b0a98c4 0x501855c169615318 0x7dc3be0f7f0f9ce7 0x6fb877c1efe1f39c

def z1138 : W := mkw 0x036c0d7014d00700 0x206d81ae029a00e0 0xfbfc0ff01ff00306 0xdf7f81fe03fe0060

def z1139 : W := mkw 0x236c1f703dd13f09 0x646d83ee07ba27e1 0xfffcfff0fff3ff1e 0xffff9ffe1ffe7fe3

def z1140 : W := mkw 0x016c0d6014d00600 0x002d81ac029a00c0 0xfbfc0ff01ff01f06 0xdf7f81fe03fe03e0

def z1141 : W := mkw 0x036c1f701dd13f01 0x606d83ee03ba27e0 0xfffcfff3fff3ff07 0xffff9ffe7ffe7fe0

def z1142 : W := mkw 0xa3680f712d509f88 0x746d01ee25aa13f1 0x23f00ff3e7701f9d 0xc47e01fe7cee03f3

def z1143 : W := mkw 0x053d500016ef6007 0x80a7aa0002ddec00 0xfdff40001fffe006 0x3fbfe80003fffc00

def z1144 : W := mkw 0x01fbedaec0244002 0x003f7db5d8048800 0xf7ffffffe00c6001 0xfefffffffc018c00

def z1145 : W := mkw 0x01fbedaec0244002 0x003f7db5d8048800 0xf3ffffffe0f06001 0xfe7ffffffc1e0c00

def z1146 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc38e0f1f8fffff 0x6fb871c1e3f1ffff

def z1147 : W := mkw 0x00514daec0000000 0x000a29b5d8000000 0xf23fffffe0000001 0xfe47fffffc000000

def z1148 : W := mkw 0x036c1f701dd13f01 0x606d83ee03ba27e0 0xfbfc7ff01ff07f06 0xdf7f8ffe03fe0fe0

def z1149 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x7df380001fffe006 0x2fbe700003fffc00

def z1150 : W := mkw 0xe40412513efff7bf 0xbc80824a27dffef7 0x0c0000001ffffffe 0x0180000003ffffff

def z1151 : W := mkw 0xa0c28e1b2b0a99cc 0x741851c365615339 0x7dc38e3f7f0f9ce7 0x6fb871c7efe1f39c

def z1152 : W := mkw 0x03680f600d501e00 0x406d01ec01aa03c0 0x23f00fc007701c04 0x447e01f800ee0380

def z1153 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff80c1fffec66 0x3fbfff0183fffd8c

def z1154 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x4dc38e0f1f0f9ce1 0x69b871c1e3e1f39c

def z1155 : W := mkw 0xa00412113881b189 0x3400824227103631 0x840cf633e083f399 0xf0819ec67c107e73

def z1156 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0001ffff087 0x7fbffe0003fffe10

def z1157 : W := mkw 0x03680f700d501f00 0x606d01ee01aa03e0 0x23f009c007701f04 0x047e013800ee03e0

def z1158 : W := mkw 0x032c03701cd01700 0x2065806e039a02e0 0xfbfc07f01ff01306 0xdf7f80fe03fe0260

def z1159 : W := mkw 0x012c100014c12001 0x0025820002982400 0xf9fcb0001ff38006 0x1f3f960003fe7000

def z1160 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0xf23fffffe0000001 0xfe47fffffc000000

def z1161 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xc3fff7ffe0000001 0xb87ffefffc000000

def z1162 : W := mkw 0x01fbedaec20a0004 0x003f7db5d8414000 0xffffffffff0f9ce7 0xffffffffffe1f39c

def z1163 : W := mkw 0x00828000020a0004 0x0010500000414000 0x7dc3880c1f0f8c66 0x2fb8710183e1f18c

def z1164 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xa3ff7fffe0000001 0xd47feffffc000000

def z1165 : W := mkw 0xc093c08f822ec0f6 0x18127811f045d81e 0x0403800f000f80e1 0x20807001e001f01c

def z1166 : W := mkw 0x25bff01036ef610f 0xa4b7fe0206ddec21 0xfdfff030fffff39f 0xffbffe061ffffe73

def z1167 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x43fcb7f360000000 0x087f96fe6c000000

def z1168 : W := mkw 0x836c0f7b1dd09fc0 0x706d81ef63ba13f8 0xfbfc0ff31ff01f06 0xdf7f81fe63fe03e0

def z1169 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff030ffffe006 0xbfbffe061ffffc00

def z1170 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x37f309cc077c1ce7 0x66fe613980ef839c

def z1171 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0001399 0xfe7ffffffc000273

def z1172 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe0001083 0xfefffffffc000210

def z1173 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0x2ff009c01ff3ff9e 0x05fe013803fe7ff3

def z1174 : W := mkw 0x01eaadaec0000000 0x003d55b5d8000000 0x73cfbfffe0000001 0xee79f7fffc000000

def z1175 : W := mkw 0x01796daec0000000 0x002f2db5d8000000 0x823c77f3e0000000 0x90478efe7c000000

def z1176 : W := mkw 0x00c28daec0000000 0x001851b5d8000000 0xf3cfffffe0000001 0xfe79fffffc000000

def z1177 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xcdfcf0001fffe006 0x19bf9e0003fffc00

def z1178 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xfffff9cc1fffe006 0x3fffff3983fffc00

def z1179 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x2bf009c01f700c04 0x057e013803ee0180

def z1180 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x63ffbfffe0000001 0xcc7ff7fffc000000

def z1181 : W := mkw 0xe497f295baaff1bf 0xbc92fe52b755fe37 0xdc0ff63ff88ff3fb 0xfb81fec7ff11fe7f

def z1182 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xfffccff39ff3ff9f 0xffff99fe73fe7ff3

def z1183 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffc8ff01ff39f06 0xffff91fe03fe73e0

def z1184 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x7bf009c01f700c06 0x0f7e013803ee0180

def z1185 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xdbfc07f01ff01302 0xdb7f80fe03fe0260

def z1186 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc07f01ff00306 0x9f7f80fe03fe0060

def z1187 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0x49ccb0001f7f8004 0x0939960003eff000

def z1188 : W := mkw 0x401140c480344632 0x08022818900688c6 0x263309cc80fc7fff 0xc4c66139901f8fff

def z1189 : W := mkw 0x0004100010812001 0x0000820002102400 0xdc0cf633f883f39b 0xfb819ec67f107e73

def z1190 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfc0cfe33f883ff9f 0xff819fc67f107ff3

def z1191 : W := mkw 0x012c004014d00600 0x00258008029a00c0 0xfbfc09c01ff00c06 0x1f7f813803fe0180

def z1192 : W := mkw 0x01fbedaec20a0004 0x003f7db5d8414000 0xf7ffffffe00f8001 0xfefffffffc01f000

def z1193 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0001c07 0xfe7ffffffc000380

def z1194 : W := mkw 0x036c0f7a1dd01f40 0x606d81ef43ba03e8 0xfbfc0ffc1ff01f66 0xdf7f81ff83fe03ec

def z1195 : W := mkw 0x82400f7b09109fc0 0x704801ef612213f8 0x02000ff300001f00 0xc04001fe600003e0

def z1196 : W := mkw 0xc093c28f8a2ed0f6 0x18127851f145da1e 0xdc03c60f988ff3fb 0xfb8078c1f311fe7f

def z1197 : W := mkw 0x4493f084822f6037 0x88927e109045ec06 0x0403f000800fe018 0x20807e001001fc03

def z1198 : W := mkw 0x01eaadaec0000000 0x003d55b5d8000000 0xf3fcbfffe0000001 0xde7f97fffc000000

def z1199 : W := mkw 0x012c104014d12601 0x00258208029a24c0 0xfffcf9c09ff3ff9f 0xffff9f3813fe7ff3

def z1200 : W := mkw 0x236c1d7035d12f09 0x646d83ae06ba25e1 0xa3fc79f0e7f06f1c 0x947f8f3e1cfe0de3

def z1201 : W := mkw 0x82400f6b09109ec0 0x504801ed612213d8 0x02000fcf00001ce1 0x404001f9e000039c

def z1202 : W := mkw 0x01796daec0000000 0x002f2db5d8000000 0xd23cffffe0000001 0xfa479ffffc000000

def z1203 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffc0ff01ff01f87 0xffff81fe03fe03f0

def z1204 : W := mkw 0x45bff08ed6ef6037 0x88b7fe11daddec06 0xfdfff00fffffe0ff 0x3fbffe01fffffc1f

def z1205 : W := mkw 0xa36c1f7b3dd1bfc9 0x746d83ef67ba37f9 0xfffcfffffff3ffff 0xffff9ffffffe7fff

def z1206 : W := mkw 0x01fbedaec0244002 0x003f7db5d8048800 0xf3ffffffe07c0005 0xfe7ffffffc0f8000

def z1207 : W := mkw 0x013961a4c0000000 0x00272c3498000000 0xc23cf7f3e0000000 0x98479efe7c000000

def z1208 : W := mkw 0x012c012014c00000 0x0025802402980000 0xfbfc01f01ff00006 0x9f7f803e03fe0000

def z1209 : W := mkw 0x00d3edaec0000000 0x001a7db5d8000000 0xd20fffffe0000001 0xfa41fffffc000000

def z1210 : W := mkw 0x03680f700d501f00 0x606d01ee01aa03e0 0x7bf00ff01f701f06 0xcf7e01fe03ee03e0

def z1211 : W := mkw 0x8082820b0b0a98c4 0x5010504161615318 0x7dc3800f1f0f9ce7 0x2fb87001e3e1f39c

def z1212 : W := mkw 0x00400d2000000000 0x000801a400000000 0xd20cfff3e0000001 0xfa419ffe7c000000

def z1213 : W := mkw 0x01eaad2a40000000 0x003d55a548000000 0xf3ffbfff60000001 0xfe7ff7ffec000000

def z1214 : W := mkw 0x05bbe000066e4006 0x80b77c0000cdc800 0x69f380001f7f8004 0x0d3e700003eff000

def z1215 : W := mkw 0x05bff1a4d6ef6007 0x80b7fe349addec00 0xfffff1c01fffe006 0x3ffffe3803fffc00

def z1216 : W := mkw 0xe493f085a22fe0bf 0x9c927e10b445fc17 0x0403f00fe00fe0f9 0x20807e01fc01fc1f

def z1217 : W := mkw 0x80c28f2b0b0a98c4 0x501851e561615318 0x7fc38fff1f0f9ce7 0xeff871ffe3e1f39c

def z1218 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0806319 0xfe7ffffffc100c63

def z1219 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc7ff0fff01f06 0xdf7f8ffe1ffe03e0

def z1220 : W := mkw 0x453d71e4d4f56633 0x88a7ae3c9a9eacc6 0x823c71f0e0f06318 0x90478e3e1c1e0c63

def z1221 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0xfdcf8e3f1f0f9ce7 0xffb9f1c7e3e1f39c

def z1222 : W := mkw 0x4000004000344632 0x08000008000688c6 0xb63309cc00fc7fff 0xf6c66139801f8fff

def z1223 : W := mkw 0xa2400f7b29109fc8 0x744801ef652213f9 0x02000fffe0001ff9 0xc04001fffc0003ff

def z1224 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x23f309cc077c0c64 0x047e613980ef818c

def z1225 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0009fffe007 0xffbffe0013fffc00

def z1226 : W := mkw 0x052c100016cb2005 0x80a5820002d96400 0xf9fc00001ff38006 0x1f3f800003fe7000

def z1227 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xe3ffffffe0000000 0x9c7ffffffc000000

def z1228 : W := mkw 0xa0441e513991bf89 0x740883ca273237f1 0xfffcfff3fff3ff9f 0xffff9ffe7ffe7ff3

def z1229 : W := mkw 0x04828000066e4006 0x8090500000cdc800 0x7dc380001f7f8006 0x2fb8700003eff000

def z1230 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xfffff9cc9ffffce7 0xffffff3993ffff9c

def z1231 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x6bfc0ff01ff01f06 0x0d7f81fe03fe03e0

def z1232 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xc3fcffffe0000001 0xd87f9ffffc000000

def z1233 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc30e0c1f0f9ce6 0x4fb861c183e1f39c

def z1234 : W := mkw 0x01fbedaec1000840 0x403f7db5d8200108 0xf3ffffffe0000c61 0xfe7ffffffc00018c

def z1235 : W := mkw 0x00400daec0000000 0x000801b5d8000000 0x420cbfffe0000001 0xc84197fffc000000

def z1236 : W := mkw 0x016c1d2014c12001 0x002d83a402982400 0xfffcfff3fff3e007 0xffff9ffe7ffe7c00

def z1237 : W := mkw 0x03680f600d501e00 0x406d01ec01aa03c0 0x2bf009c01f701c06 0x057e013803ee0380

def z1238 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xf3fcfff3e7700c05 0xfe7f9ffe7cee0180

def z1239 : W := mkw 0x01fbedaec30a0844 0x403f7db5d8614108 0xffffffffff0f8c67 0xffffffffffe1f18c

def z1240 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0x4bfc07f01f700000 0x097f80fe03ee0000

def z1241 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc4ff09ff07f1e 0xdf7f89fe13fe0fe3

def z1242 : W := mkw 0x01bfe00016ca0004 0x0037fc0002d94000 0xfdfff0001fff8006 0x3fbffe0003fff000

def z1243 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffcbff37ff3ff9e 0xdfff97fe6ffe7ff3

def z1244 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc38e0f9f0f9fff 0xefb871c1f3e1f3ff

def z1245 : W := mkw 0x401140c480344632 0x08022818900688c6 0xa23349cc80fc7ffd 0xd4466939901f8fff

def z1246 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x4dcff0001fffe006 0x29b9fe0003fffc00

def z1247 : W := mkw 0x0000004000100600 0x00000008000200c0 0xb63349cc80fc7fff 0xf6c66939901f8fff

def z1248 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x7dffb0001f7f8006 0x2fbff60003eff000

def z1249 : W := mkw 0xa00412113881b189 0x3400824227103631 0xfe3cfff3f883f39b 0xffc79ffe7f107e73

def z1250 : W := mkw 0x01eaadaec0000000 0x003d55b5d8000000 0x43ccbfff60000000 0x087997ffec000000

def z1251 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xebfc0ff01ff00f04 0x9d7f81fe03fe01e0

def z1252 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xddfcf0001ff3e002 0x3bbf9e0003fe7c00

def z1253 : W := mkw 0x02400f7009101f00 0x604801ee012203e0 0xfbf00ff01ff01f06 0xdf7e01fe03fe03e0

def z1254 : W := mkw 0x45bff00016ef6037 0x88b7fe0002ddec06 0xfdfff0001fffe0fe 0x3fbffe0003fffc1f

def z1255 : W := mkw 0x05bff08496ef6007 0x80b7fe1092ddec00 0xfffff1c09fffe006 0xbffffe3813fffc00

def z1256 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0x73ffbfff60000001 0x6e7ff7ffec000000

def z1257 : W := mkw 0x836c0f711dd09f80 0x706d81ee23ba13f0 0xffff8fff1fff9fe7 0xfffff1ffe3fff3fc

def z1258 : W := mkw 0x401140c480344632 0x08022818900688c6 0xb63f79fce0fc7fff 0xf6c7ef3f9c1f8fff

def z1259 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xfffcfff37ff3ff06 0xffff9ffe6ffe7fe0

def z1260 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfcbff37ff01f06 0xdf7f97fe6ffe03e0

def z1261 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xbbf009c01ff01f06 0xd77e013803fe03e0

def z1262 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x7dc3fe0fff0f9ce7 0x6fb87fc1ffe1f39c

def z1263 : W := mkw 0x01796daec0000000 0x002f2db5d8000000 0xb23f7fffe0000001 0xf647effffc000000

def z1264 : W := mkw 0x016c0f201dc01800 0x402d81e403b80300 0xfbfc0ff01ff01c06 0xdf7f81fe03fe0380

def z1265 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0xb7f049c087f07f9f 0xf6fe093810fe0ff3

def z1266 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfffc4ff01ff07f06 0xffff89fe03fe0fe0

def z1267 : W := mkw 0x01fbedaec0244002 0x003f7db5d8048800 0xf7ffffffe0fc739f 0xfefffffffc1f8e73

def z1268 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0f00007 0xfe7ffffffc1e0000

def z1269 : W := mkw 0x00400c4001100e00 0x40080188002201c0 0x23f009c007700c04 0x047e013800ee0180

def z1270 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf7ffffffe00c0007 0xfefffffffc018000

def z1271 : W := mkw 0x02440e501dd01f00 0x604881ca03ba03e0 0xfbf00fc01ff01f06 0xdf7e01f803fe03e0

def z1272 : W := mkw 0x05aeb00016ef6007 0x80b5d60002ddec00 0xfdfcb0001fffe006 0x1fbf960003fffc00

def z1273 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffffe0001ce1 0xfe7ffffffc00039c

def z1274 : W := mkw 0xc0400fefc9109ef0 0x580801fdf92213de 0x02000fffe0001ff9 0xc04001fffc0003ff

def z1275 : W := mkw 0x401140c480344632 0x08022818900688c6 0x363309cc00fc7fff 0x66c66139801f8fff

def z1276 : W := mkw 0x80c28e0b0b0a98c4 0x501851c161615318 0x4dc3860f1f0f9ce7 0x29b870c1e3e1f39c

def z1277 : W := mkw 0x401140c480344632 0x08022818900688c6 0xf63ff9cc80fc7fff 0xfec7ff39901f8fff

def z1278 : W := mkw 0xa36c1f713dd1bf89 0x746d83ee27ba37f1 0xdffcf7f3fff3f39b 0xfbff9efe7ffe7e73

def z1279 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x23f009c007701f04 0xc47e013800ee03e0

def z1280 : W := mkw 0x03680d6005500e00 0x406d01ac00aa01c0 0x63fc0ff007700c04 0x0c7f81fe00ee0180

def z1281 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xfdfff0001ffffce6 0x3fbffe0003ffff9c

def z1282 : W := mkw 0xa2400f7129109f88 0x744801ee252213f1 0x02000ff000001f98 0xc04001fe000003f3

def z1283 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0x2df3f0001fffe006 0x25be7e0003fffc00

def z1284 : W := mkw 0x401140c480344632 0x08022818900688c6 0xf63f4ffc80fc7fff 0xfec7e9ff901f8fff

def z1285 : W := mkw 0x01fbedaec0000000 0x003f7db5d8000000 0xf3ffffff60000000 0x3e7fffffec000000

def z1286 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xf9ffb0001fff8006 0x1f3ff60003fff000

def z1287 : W := mkw 0xa32c13713cd1b789 0x3465826e279a36f1 0xfffcf7f3fff3f39f 0xffff9efe7ffe7e73

def z1288 : W := mkw 0xe00412513891b7b9 0x3c00824a271236f7 0x0c0000001883fffa 0x0180000003107fff

def z1289 : W := mkw 0x05bff00016ef6007 0x80b7fe0002ddec00 0xbdf340001fffe006 0x37be680003fffc00

def z1290 : W := mkw 0x25bff01036ef610f 0xa4b7fe0206ddec21 0xfdfff633ffffe31f 0xffbffec67ffffc63

def z1291 : W := mkw 0x036c0f701dd01f00 0x606d81ee03ba03e0 0xfbfc0ffc1ff01fe7 0xdf7f81ff83fe03fc

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z8,z9,z4,z5,z6]),(0,[z1,z2,z10,z9,z4,z5,z6]),(1,[z11,z1,z4,z5,z6,z12]),(0,[z1,z8,z9,z13,z4,z5,z6]),(0,[z1,z2,z9,z4,z14,z5,z6]),(0,[z15,z1,z2,z9,z4,z5,z6]),(0,[z16,z1,z2,z9,z4,z5,z6])],[(0,[z17,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z18,z9,z4,z5,z6]),(0,[z19,z1,z2,z9,z4,z5,z6]),(0,[z20,z1,z2,z9,z4,z5,z6]),(1,[z21,z1,z9,z4,z5,z6]),(0,[z1,z2,z9,z22,z4,z5,z6])],[(0,[z1,z2,z23,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z24,z6]),(0,[z25,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z26,z5,z6]),(0,[z27,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z28,z4,z5,z6]),(1,[z1,z2,z29,z4,z5,z6])],[(0,[z1,z30,z2,z9,z4,z5,z6]),(0,[z31,z1,z2,z9,z4,z5,z6]),(0,[z1,z32,z8,z9,z4,z5,z6]),(0,[z33,z34,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z35,z5,z6])],[(0,[z36,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z37,z4,z5,z6]),(0,[z1,z38,z2,z9,z4,z5,z6]),(0,[z39,z1,z9,z4,z5,z6,z12]),(0,[z40,z1,z9,z41,z4,z5,z6]),(0,[z42,z1,z9,z4,z5,z6,z12]),(0,[z1,z9,z4,z43,z5,z6,z12]),(0,[z1,z2,z44,z9,z45,z4,z6])],[(0,[z46,z2,z47,z9,z4,z5,z6]),(0,[z1,z9,z4,z48,z5,z6,z12]),(0,[z2,z9,z4,z5,z49,z24,z6]),(0,[z1,z2,z9,z50,z4,z5,z6]),(0,[z51,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z52,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z53,z5,z6]),(0,[z1,z2,z54,z55,z4,z5,z6])],[(0,[z56,z2,z9,z4,z48,z5,z6]),(0,[z57,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z58,z9,z4,z5,z6]),(0,[z59,z1,z2,z9,z4,z5,z6]),(0,[z1,z60,z9,z41,z4,z5,z6]),(0,[z1,z2,z9,z61,z4,z5,z6]),(1,[z1,z2,z4,z5,z62,z6]),(0,[z63,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z64,z6]),(0,[z1,z2,z9,z65,z4,z5,z6]),(0,[z1,z2,z9,z4,z66,z5,z6]),(0,[z1,z9,z4,z67,z5,z6,z12]),(1,[z16,z1,z2,z9,z54,z4])]],
   [[(0,[z1,z2,z9,z4,z5,z68,z6]),(0,[z69,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z70,z6])],[(0,[z1,z2,z9,z4,z71,z6,z72]),(0,[z73,z1,z9,z4,z5,z6,z12]),(0,[z1,z9,z45,z4,z5,z6,z12]),(1,[z34,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z74,z5,z6]),(0,[z1,z8,z9,z4,z75,z5,z6]),(0,[z1,z76,z9,z4,z77,z5,z6]),(0,[z1,z2,z9,z4,z5,z78,z6]),(0,[z1,z2,z9,z4,z79,z5,z6])],[(0,[z17,z1,z80,z9,z4,z5,z6]),(0,[z25,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z6,z12]),(0,[z1,z81,z2,z9,z4,z5,z6]),(1,[z1,z82,z9,z4,z5,z6])],[(1,[z83,z1,z9,z4,z5,z6]),(0,[z1,z9,z41,z4,z75,z5,z6]),(1,[z84,z1,z2,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z6,z72])],[(0,[z1,z2,z9,z4,z5,z6,z85]),(0,[z1,z2,z9,z86,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z62,z6]),(0,[z1,z2,z9,z4,z5,z6,z87]),(0,[z88,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z89,z4,z5,z6]),(0,[z1,z90,z2,z9,z4,z5,z6]),(0,[z91,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z92,z9,z4,z5,z6])],[(0,[z1,z2,z93,z9,z4,z5,z6]),(0,[z94,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z95,z4,z5,z6]),(0,[z96,z1,z2,z50,z4,z5,z6]),(0,[z39,z1,z80,z9,z4,z5,z6]),(0,[z97,z1,z2,z9,z4,z79,z6]),(0,[z1,z2,z9,z4,z5,z6,z98]),(0,[z1,z2,z9,z4,z5,z99,z6])],[(0,[z46,z100,z2,z9,z4,z5,z6]),(0,[z1,z2,z101,z9,z4,z5,z6]),(0,[z1,z2,z102,z9,z4,z5,z6]),(0,[z1,z2,z103,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z104,z6,z12])]],
   [[(0,[z2,z47,z9,z105,z4,z5,z6]),(0,[z1,z2,z47,z106,z4,z5,z6]),(0,[z1,z2,z9,z107,z4,z5,z6]),(1,[z73,z1,z2,z79,z5,z6]),(0,[z1,z108,z9,z4,z43,z5,z6]),(0,[z1,z109,z2,z9,z4,z5,z6])],[(0,[z1,z9,z4,z77,z5,z110,z6]),(0,[z1,z2,z9,z111,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z112]),(1,[z1,z113,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z114,z5,z6]),(1,[z11,z1,z2,z4,z5,z6]),(0,[z1,z8,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z115,z6])],[(0,[z1,z2,z116,z9,z4,z5,z6]),(0,[z1,z2,z9,z117,z118,z5,z6]),(0,[z1,z2,z9,z4,z5,z119,z6]),(0,[z1,z2,z9,z120,z4,z5,z6])],[(0,[z1,z2,z9,z4,z121,z5,z6]),(0,[z0,z1,z56,z9,z4,z5,z6]),(0,[z122,z1,z2,z9,z4,z5,z6]),(0,[z39,z40,z1,z9,z4,z5,z6])],[(0,[z1,z2,z105,z4,z5,z6,z123]),(0,[z1,z2,z9,z4,z5,z6,z6]),(0,[z1,z2,z80,z9,z4,z5,z6]),(0,[z1,z124,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z125]),(0,[z1,z2,z9,z4,z5,z126,z6])],[(0,[z1,z2,z9,z4,z5,z6,z127]),(0,[z2,z9,z117,z4,z5,z24,z6]),(0,[z39,z1,z60,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z128,z5,z6]),(0,[z73,z42,z1,z2,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z129]),(0,[z16,z1,z2,z9,z4,z5,z72])],[(0,[z100,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z130,z4,z5,z6]),(1,[z1,z2,z131,z4,z5,z6]),(0,[z132,z1,z2,z131,z4,z5,z6]),(0,[z1,z2,z9,z4,z133,z5,z6]),(0,[z1,z2,z9,z4,z134,z5,z6]),(0,[z1,z8,z9,z41,z4,z5,z6]),(1,[z135,z1,z9,z4,z5,z12]),(0,[z1,z2,z9,z4,z5,z6,z136]),(0,[z1,z2,z9,z45,z4,z67,z6])]],
   [[(0,[z1,z2,z137,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z138,z6])],[(0,[z1,z2,z9,z4,z5,z139,z6]),(0,[z1,z2,z140,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z141,z5,z6])],[(0,[z0,z1,z9,z4,z5,z6,z12]),(0,[z142,z1,z2,z9,z4,z5,z6]),(0,[z1,z80,z9,z4,z5,z6,z12])],[(0,[z143,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z144,z6]),(0,[z145,z1,z2,z9,z5,z6,z146]),(1,[z147,z2,z9,z4,z5,z6])],[(0,[z148,z36,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z49,z6]),(0,[z149,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z150,z5,z6]),(0,[z1,z44,z9,z4,z5,z6,z12]),(1,[z1,z2,z106,z4,z5,z151])],[(0,[z152,z1,z2,z9,z4,z5,z6]),(0,[z96,z153,z2,z9,z4,z5,z6]),(0,[z1,z2,z154,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z155,z5,z6]),(0,[z1,z9,z4,z5,z151,z6,z12]),(1,[z156,z2,z9,z4,z5,z6]),(0,[z1,z157,z9,z4,z5,z104,z6])],[(0,[z2,z9,z4,z48,z5,z49,z6]),(0,[z16,z1,z2,z9,z4,z49,z6]),(0,[z1,z8,z9,z4,z5,z151,z6]),(0,[z1,z2,z158,z9,z4,z5,z6])],[(1,[z132,z2,z9,z48,z5,z6]),(0,[z19,z1,z2,z9,z4,z49,z6]),(0,[z159,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z13,z4,z5,z6]),(0,[z1,z2,z9,z4,z160,z5,z6]),(0,[z1,z2,z9,z118,z4,z5,z146])]],
   [[(0,[z1,z2,z9,z4,z161,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z162]),(0,[z1,z2,z9,z4,z163,z5,z6])],[(0,[z1,z2,z9,z4,z5,z24,z6]),(0,[z1,z9,z4,z5,z24,z6,z164]),(0,[z1,z76,z2,z9,z4,z110,z6]),(0,[z1,z2,z9,z4,z5,z6,z165])],[(1,[z166,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z167,z4,z5,z6]),(0,[z1,z168,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z54,z4,z5,z146])],[(0,[z169,z1,z8,z9,z4,z5,z6])],[(0,[z0,z1,z80,z9,z4,z5,z6]),(0,[z1,z170,z2,z9,z4,z5,z6]),(0,[z1,z171,z2,z9,z4,z5,z6]),(0,[z2,z106,z9,z172,z4,z5,z6]),(0,[z33,z1,z2,z173,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z104,z72]),(0,[z1,z2,z9,z4,z5,z174,z6])],[(0,[z1,z2,z3,z9,z4,z5,z6]),(1,[z1,z2,z9,z4,z5,z175]),(0,[z1,z2,z9,z4,z5,z6,z176])],[(0,[z1,z2,z47,z4,z43,z5,z6]),(0,[z1,z177,z2,z9,z4,z5,z6]),(0,[z178,z1,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z72,z12]),(0,[z179,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z180,z6])],[(0,[z17,z1,z8,z9,z4,z5,z6]),(1,[z33,z1,z2,z9,z6,z181])]],
   [[(0,[z1,z2,z182,z9,z4,z5,z6]),(0,[z1,z183,z2,z9,z4,z5,z6]),(0,[z1,z7,z2,z184,z4,z5,z6]),(0,[z1,z76,z2,z9,z4,z77,z6]),(0,[z185,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z186])],[(0,[z187,z1,z2,z9,z4,z5,z6]),(0,[z148,z1,z2,z9,z4,z71,z6]),(1,[z96,z2,z9,z4,z5,z188]),(0,[z189,z1,z2,z9,z4,z5,z6]),(0,[z190,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z191,z5,z6])],[(0,[z1,z8,z192,z9,z4,z5,z6]),(0,[z1,z2,z9,z193,z4,z5,z6]),(0,[z46,z1,z8,z9,z4,z5,z6]),(0,[z132,z1,z2,z9,z117,z5,z6]),(0,[z1,z2,z9,z194,z4,z5,z6]),(0,[z1,z2,z9,z4,z195,z5,z6]),(0,[z42,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z196,z9,z4,z5,z6]),(0,[z1,z2,z197,z89,z4,z5,z6]),(0,[z1,z2,z9,z4,z198,z5,z6]),(1,[z1,z168,z9,z4,z5,z6]),(1,[z1,z2,z173,z4,z5,z6]),(0,[z145,z1,z2,z9,z4,z5,z146])],[(0,[z199,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z200]),(0,[z201,z1,z2,z9,z4,z5,z6]),(0,[z202,z1,z8,z9,z4,z5,z6]),(0,[z73,z1,z2,z4,z43,z5,z6]),(0,[z21,z1,z2,z9,z4,z5,z6]),(1,[z203,z2,z9,z4,z5,z6])],[(0,[z153,z2,z9,z4,z48,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z204]),(0,[z205,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z5,z104,z6,z146])],[(0,[z1,z2,z9,z117,z5,z6,z146]),(0,[z1,z2,z206,z9,z4,z5,z6]),(0,[z1,z2,z9,z207,z4,z5,z6]),(0,[z1,z2,z44,z197,z4,z5,z6]),(1,[z1,z2,z9,z4,z208,z6])],[(0,[z100,z2,z9,z105,z4,z5,z6]),(0,[z1,z2,z9,z4,z209,z5,z6]),(0,[z25,z1,z2,z197,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z210,z6]),(0,[z1,z9,z4,z77,z5,z6,z12]),(0,[z1,z2,z9,z4,z211,z5,z6]),(0,[z212,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z213,z4,z5,z6]),(0,[z33,z1,z2,z9,z4,z5,z6]),(0,[z33,z1,z2,z9,z4,z5,z99])],[(0,[z1,z2,z9,z4,z5,z214,z6]),(0,[z1,z2,z9,z4,z5,z6,z215]),(0,[z1,z2,z9,z216,z4,z5,z6]),(1,[z1,z2,z44,z4,z43,z6]),(0,[z1,z2,z217,z9,z4,z5,z6]),(0,[z1,z2,z9,z218,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z4,z219,z5,z6]),(0,[z220,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z221,z4,z5,z6]),(0,[z222,z1,z2,z9,z4,z5,z6])],[(0,[z96,z56,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z223]),(0,[z25,z1,z9,z4,z5,z110,z6]),(0,[z25,z1,z8,z9,z4,z5,z6]),(0,[z1,z76,z2,z9,z4,z5,z6]),(0,[z185,z1,z9,z4,z5,z6,z12]),(0,[z1,z8,z9,z89,z4,z5,z6]),(0,[z1,z2,z9,z173,z4,z5,z6]),(0,[z1,z2,z9,z224,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z225,z6]),(0,[z1,z9,z4,z5,z6,z12,z127]),(0,[z11,z1,z9,z4,z5,z6,z12]),(0,[z1,z8,z9,z4,z5,z104,z6])],[(1,[z17,z192,z9,z4,z5,z6]),(0,[z1,z226,z9,z105,z4,z5,z6]),(1,[z1,z2,z4,z227,z5,z6]),(0,[z228,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z106,z9,z4,z5,z123])],[(1,[z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z229,z4,z5,z6]),(0,[z96,z148,z2,z9,z4,z5,z6]),(0,[z96,z1,z230,z9,z4,z5,z6]),(0,[z1,z2,z231,z9,z4,z5,z6]),(0,[z1,z2,z9,z232,z4,z5,z6]),(1,[z1,z2,z9,z4,z233,z6]),(0,[z1,z2,z9,z4,z5,z6,z234]),(0,[z1,z235,z2,z9,z4,z5,z6])],[(0,[z0,z1,z2,z236,z4,z5,z6]),(0,[z1,z2,z9,z4,z237,z5,z6]),(1,[z9,z4,z5,z6,z238,z12]),(1,[z185,z2,z9,z4,z5,z6]),(0,[z1,z2,z239,z9,z4,z5,z6]),(1,[z1,z9,z4,z240,z5,z6]),(0,[z1,z2,z4,z79,z5,z6,z123]),(1,[z241,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z41,z4,z5,z6]),(0,[z1,z9,z4,z5,z110,z6,z12])],[(0,[z25,z17,z1,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z242,z5,z6]),(1,[z39,z1,z9,z75,z5,z6]),(0,[z243,z1,z2,z9,z4,z5,z6]),(0,[z42,z1,z2,z9,z4,z43,z6])]],
   [[(0,[z36,z2,z9,z105,z4,z5,z6]),(0,[z244,z1,z2,z9,z4,z5,z6]),(0,[z148,z2,z9,z4,z5,z24,z6]),(0,[z84,z1,z2,z9,z4,z5,z6])],[(0,[z25,z1,z76,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z6,z72,z181]),(0,[z245,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z246,z4,z5,z6])],[(0,[z1,z2,z9,z4,z247,z5,z6]),(1,[z1,z248,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z249])],[(0,[z1,z2,z9,z250,z4,z5,z6]),(0,[z1,z251,z2,z9,z4,z5,z6]),(0,[z252,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z176,z181]),(0,[z253,z1,z2,z9,z4,z5,z6])],[(0,[z254,z1,z2,z9,z4,z5,z6]),(0,[z88,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z255,z4,z5,z6])],[(0,[z100,z1,z8,z9,z4,z5,z6]),(0,[z83,z1,z2,z9,z4,z5,z6]),(0,[z132,z1,z9,z4,z5,z6,z12]),(0,[z166,z1,z2,z9,z4,z5,z6]),(0,[z135,z1,z2,z9,z4,z5,z12]),(0,[z1,z2,z9,z256,z4,z5,z6]),(0,[z1,z2,z44,z9,z4,z43,z6])],[(0,[z1,z2,z257,z9,z4,z5,z6]),(0,[z96,z46,z2,z9,z4,z5,z6]),(0,[z1,z2,z258,z41,z4,z5,z6]),(0,[z1,z2,z259,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z260,z5,z6]),(0,[z153,z1,z2,z9,z4,z5,z6]),(0,[z261,z1,z2,z9,z4,z5,z6]),(0,[z1,z7,z2,z4,z43,z5,z6]),(0,[z262,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z263,z4,z5,z6])]],
   [[(0,[z0,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z264,z5,z6]),(0,[z1,z2,z9,z4,z265,z5,z6]),(0,[z1,z266,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z45,z4,z6,z181])],[(0,[z267,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z268]),(0,[z1,z2,z106,z9,z4,z5,z151])],[(0,[z1,z8,z9,z117,z4,z5,z6]),(0,[z269,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z55,z4,z5,z6])],[(0,[z0,z17,z2,z9,z4,z5,z6]),(0,[z270,z1,z2,z9,z4,z5,z6]),(0,[z36,z2,z9,z4,z5,z49,z6]),(0,[z1,z2,z9,z4,z5,z271,z6]),(0,[z1,z2,z9,z4,z272,z5,z6]),(0,[z273,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z274,z9,z4,z5,z6]),(0,[z1,z275,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z276,z4,z5,z6]),(0,[z1,z2,z106,z105,z4,z5,z6]),(0,[z1,z2,z47,z4,z79,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z277]),(0,[z145,z1,z2,z9,z118,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z278])],[(0,[z279,z1,z2,z9,z4,z5,z6]),(0,[z1,z80,z9,z41,z4,z5,z6]),(0,[z1,z8,z280,z9,z4,z5,z6]),(0,[z1,z281,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z282,z6]),(0,[z1,z2,z226,z9,z4,z5,z6]),(0,[z1,z106,z9,z4,z5,z6,z12])],[(0,[z1,z2,z9,z4,z283,z5,z6]),(0,[z46,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z49,z6,z72]),(0,[z96,z1,z2,z9,z4,z5,z188]),(0,[z1,z2,z9,z284,z4,z5,z6]),(0,[z135,z1,z2,z9,z4,z5,z6]),(0,[z285,z1,z2,z9,z4,z5,z6])]],
   [[(0,[z286,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z192,z9,z4,z5,z6]),(0,[z287,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z288]),(0,[z73,z1,z2,z4,z79,z5,z6]),(1,[z27,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z289])],[(1,[z1,z2,z9,z290,z5,z6]),(0,[z291,z1,z2,z9,z4,z5,z6])],[(0,[z292,z1,z2,z9,z4,z5,z6]),(0,[z42,z1,z2,z105,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z293]),(0,[z36,z1,z2,z9,z48,z5,z6]),(0,[z294,z1,z2,z9,z4,z5,z6]),(0,[z295,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z296,z6]),(0,[z16,z1,z9,z4,z5,z6,z12]),(0,[z1,z8,z9,z4,z297,z5,z6]),(0,[z63,z2,z106,z9,z4,z5,z6]),(0,[z1,z2,z9,z28,z4,z5,z6])],[(0,[z298,z1,z2,z9,z4,z5,z6]),(0,[z299,z1,z2,z9,z4,z5,z6]),(0,[z300,z1,z2,z9,z4,z5,z6]),(0,[z19,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z301,z4,z5,z6]),(0,[z285,z1,z248,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z302,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z303]),(0,[z1,z2,z9,z4,z5,z304,z6])],[(0,[z17,z36,z2,z9,z4,z5,z6]),(0,[z305,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z306,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z164]),(1,[z1,z251,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z307]),(0,[z308,z1,z2,z9,z4,z5,z6]),(0,[z145,z1,z2,z9,z4,z233,z6]),(0,[z309,z1,z2,z9,z4,z5,z6])]],
   [[(0,[z310,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z311,z4,z5,z6]),(0,[z1,z2,z312,z9,z4,z5,z6]),(0,[z135,z1,z9,z4,z5,z6,z12]),(0,[z313,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z4,z43,z5,z6,z123]),(1,[z63,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z104,z6])],[(0,[z1,z2,z9,z4,z5,z314,z6]),(0,[z25,z1,z2,z105,z4,z5,z6]),(0,[z46,z36,z2,z9,z4,z5,z6]),(1,[z1,z2,z315,z4,z5,z6]),(0,[z96,z1,z2,z316,z4,z5,z6]),(0,[z1,z2,z317,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z67,z5,z6]),(0,[z318,z1,z2,z9,z4,z5,z6])],[(0,[z319,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z320]),(0,[z1,z171,z8,z9,z4,z5,z6]),(0,[z42,z1,z2,z106,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z321])],[(0,[z132,z1,z2,z18,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z123]),(1,[z322,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z323,z4,z5,z6]),(0,[z1,z2,z9,z324,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z325]),(0,[z1,z2,z9,z4,z5,z326,z6]),(0,[z42,z1,z2,z47,z4,z5,z6]),(0,[z1,z2,z316,z9,z4,z5,z6]),(0,[z42,z25,z1,z2,z4,z5,z6]),(0,[z135,z1,z2,z9,z4,z5,z327]),(0,[z328,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z329,z4,z5,z6])],[(0,[z330,z1,z2,z9,z4,z5,z6]),(0,[z1,z331,z2,z9,z4,z5,z6]),(1,[z2,z9,z4,z5,z6,z332])]],
   [[(0,[z1,z56,z2,z9,z4,z5,z6]),(1,[z1,z2,z236,z4,z5,z6]),(0,[z1,z2,z9,z4,z48,z5,z6]),(0,[z1,z76,z9,z4,z75,z5,z6]),(0,[z1,z2,z9,z333,z4,z5,z6]),(0,[z1,z2,z197,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z334]),(0,[z1,z2,z9,z335,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z336]),(0,[z25,z1,z2,z184,z4,z5,z6]),(0,[z337,z1,z2,z9,z4,z5,z6])],[(1,[z2,z9,z4,z338,z5,z6]),(1,[z1,z2,z258,z4,z5,z6]),(0,[z1,z2,z9,z339,z4,z5,z6]),(0,[z34,z1,z2,z9,z4,z5,z6])],[(0,[z340,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z341,z5,z6]),(0,[z1,z2,z9,z4,z342,z5,z72])],[(0,[z1,z2,z9,z4,z343,z5,z6]),(0,[z1,z2,z9,z344,z4,z5,z6]),(0,[z1,z2,z9,z345,z4,z5,z6]),(0,[z1,z7,z2,z80,z4,z5,z6]),(0,[z33,z346,z2,z9,z4,z5,z6])],[(0,[z1,z7,z2,z4,z79,z5,z6]),(1,[z1,z4,z5,z6,z347,z12]),(0,[z1,z9,z4,z5,z6,z6,z12]),(0,[z33,z1,z8,z9,z4,z5,z6]),(0,[z1,z348,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z349,z6]),(0,[z1,z168,z9,z4,z5,z151,z6])],[(0,[z100,z1,z2,z105,z4,z5,z6]),(0,[z350,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z9,z45,z67,z6])],[(0,[z1,z351,z2,z9,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z4,z352,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z353]),(0,[z1,z76,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z327,z6]),(0,[z1,z2,z9,z4,z354,z5,z6]),(0,[z1,z2,z355,z9,z4,z5,z6]),(0,[z356,z1,z2,z9,z4,z5,z6]),(0,[z285,z1,z2,z4,z5,z6,z123]),(0,[z1,z2,z9,z4,z5,z357,z6]),(0,[z145,z1,z2,z28,z4,z5,z6])],[(0,[z1,z2,z9,z4,z358,z5,z6]),(0,[z1,z56,z9,z4,z5,z6,z12]),(0,[z2,z9,z105,z4,z48,z5,z6]),(0,[z1,z2,z9,z131,z4,z5,z6]),(0,[z1,z2,z9,z117,z4,z5,z6])],[(0,[z359,z1,z2,z9,z4,z5,z6]),(0,[z360,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z361,z6]),(1,[z1,z76,z9,z4,z77,z6]),(0,[z1,z2,z106,z4,z43,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z362])],[(0,[z132,z1,z8,z9,z4,z5,z6]),(0,[z1,z9,z4,z71,z5,z6,z12]),(0,[z363,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z41,z4,z227,z5,z6]),(0,[z1,z9,z4,z5,z364,z6,z12]),(0,[z1,z365,z8,z9,z4,z5,z6]),(1,[z366,z2,z9,z4,z5,z6]),(0,[z147,z2,z9,z4,z5,z6,z146])],[(0,[z367,z1,z2,z9,z4,z5,z6]),(0,[z1,z7,z2,z105,z4,z5,z6]),(0,[z368,z1,z2,z9,z4,z5,z6]),(0,[z340,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z280,z9,z4,z5,z6]),(0,[z33,z42,z1,z2,z9,z4,z6]),(0,[z369,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z370,z5,z6]),(0,[z147,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z371,z5,z6]),(0,[z1,z9,z4,z5,z6,z12,z288])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z9,z372,z4,z5,z6]),(0,[z373,z1,z2,z9,z4,z5,z6]),(0,[z374,z1,z2,z9,z4,z5,z6]),(0,[z39,z1,z2,z9,z41,z5,z6]),(0,[z1,z2,z9,z4,z5,z375,z6]),(0,[z1,z2,z9,z4,z5,z6,z376]),(0,[z42,z1,z2,z9,z4,z364,z6]),(0,[z33,z1,z377,z9,z4,z5,z6])],[(0,[z1,z2,z378,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z379,z6]),(0,[z1,z2,z9,z4,z380,z5,z6]),(1,[z2,z9,z172,z4,z5,z6]),(0,[z381,z1,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z277,z181])]],
   [[(0,[z132,z1,z2,z9,z48,z5,z6]),(0,[z1,z2,z9,z4,z382,z5,z6]),(0,[z1,z8,z9,z118,z4,z5,z6]),(0,[z1,z9,z4,z5,z104,z6,z165])],[(0,[z100,z1,z2,z47,z4,z5,z6]),(0,[z46,z2,z9,z4,z5,z49,z6]),(0,[z1,z8,z9,z4,z342,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z383]),(0,[z145,z1,z82,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z384,z5,z6]),(0,[z1,z2,z9,z4,z385,z5,z6])],[(0,[z1,z2,z105,z4,z43,z5,z6]),(1,[z153,z2,z9,z4,z5,z24]),(0,[z1,z2,z9,z4,z5,z6,z386]),(1,[z1,z2,z9,z4,z6,z387]),(0,[z1,z2,z9,z4,z5,z6,z388]),(1,[z1,z9,z389,z4,z5,z6])],[(0,[z1,z1,z2,z9,z4,z5,z6]),(0,[z17,z2,z9,z4,z5,z24,z6]),(0,[z390,z1,z2,z9,z4,z5,z6]),(0,[z36,z153,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z391,z5,z6]),(0,[z392,z1,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z54,z4,z5,z6]),(0,[z1,z2,z9,z4,z297,z5,z6])],[(0,[z393,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z230,z9,z4,z5,z6]),(0,[z394,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z395,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z238,z12]),(1,[z1,z377,z9,z4,z5,z6])],[(0,[z1,z2,z9,z396,z4,z5,z6])],[(0,[z46,z2,z9,z4,z5,z24,z6]),(0,[z1,z2,z9,z4,z5,z397,z6]),(0,[z153,z1,z8,z9,z4,z5,z6]),(0,[z1,z9,z4,z75,z5,z6,z12]),(0,[z1,z9,z118,z4,z5,z6,z12])],[(0,[z1,z7,z2,z47,z4,z5,z6]),(0,[z398,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z4,z5,z62,z110,z6]),(0,[z399,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z44,z4,z43,z5,z6]),(0,[z400,z1,z2,z9,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z4,z401,z5,z6]),(1,[z19,z2,z9,z4,z49,z6]),(0,[z25,z1,z2,z4,z43,z5,z6]),(0,[z1,z9,z4,z5,z6,z12,z123]),(0,[z402,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z403]),(0,[z1,z2,z106,z4,z5,z151,z6]),(1,[z1,z404,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z405,z6]),(0,[z1,z2,z9,z4,z5,z406,z6]),(0,[z1,z2,z197,z4,z5,z6,z123]),(0,[z1,z2,z9,z4,z67,z5,z6])],[(0,[z16,z1,z8,z9,z4,z5,z6])],[(0,[z19,z1,z8,z9,z4,z5,z6]),(0,[z1,z407,z2,z9,z4,z5,z6]),(0,[z11,z1,z2,z4,z5,z6,z12])],[(0,[z408,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z409,z4,z5,z6])],[(0,[z1,z2,z47,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z410,z6]),(0,[z411,z1,z2,z9,z4,z5,z6])],[(0,[z135,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z412]),(0,[z21,z1,z9,z4,z79,z5,z6]),(0,[z1,z2,z9,z4,z5,z72,z146]),(0,[z1,z113,z9,z4,z342,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z413]),(0,[z16,z1,z2,z9,z54,z4,z5])],[(0,[z414,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z415,z5,z6]),(0,[z201,z1,z9,z4,z5,z6,z12]),(0,[z42,z1,z2,z44,z4,z5,z6]),(0,[z1,z2,z9,z4,z416,z5,z6]),(1,[z1,z2,z9,z4,z5,z99])]],
   [[(0,[z1,z8,z9,z4,z5,z6,z123])],[(0,[z25,z1,z9,z41,z4,z5,z6]),(0,[z417,z1,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z77,z5,z6]),(0,[z418,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z419]),(0,[z1,z2,z9,z4,z420,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z421])],[(0,[z422,z1,z2,z9,z4,z5,z6]),(0,[z33,z1,z9,z4,z5,z6,z12]),(0,[z1,z8,z423,z9,z4,z5,z6]),(0,[z16,z1,z2,z9,z4,z342,z6])],[(0,[z1,z2,z9,z4,z5,z424,z6]),(0,[z425,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z426,z6]),(0,[z1,z2,z9,z4,z427,z5,z6]),(0,[z1,z9,z41,z4,z77,z5,z6]),(0,[z1,z2,z9,z4,z5,z428,z6])],[(0,[z429,z1,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z48,z5,z6]),(0,[z2,z9,z4,z71,z5,z49,z6]),(0,[z430,z1,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z12,z353]),(1,[z2,z9,z4,z5,z6,z238]),(0,[z1,z8,z197,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z6,z181]),(0,[z2,z9,z4,z5,z6,z332,z146])],[(0,[z431,z1,z2,z9,z4,z5,z6]),(0,[z96,z2,z9,z117,z4,z5,z6]),(0,[z1,z432,z2,z9,z4,z5,z6]),(0,[z285,z1,z7,z2,z4,z5,z6]),(0,[z1,z2,z9,z4,z227,z5,z6]),(0,[z1,z76,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z433,z5,z6]),(0,[z1,z434,z9,z54,z4,z5,z6])],[(0,[z1,z2,z9,z9,z4,z5,z6]),(0,[z25,z1,z2,z4,z5,z151,z6]),(0,[z1,z2,z9,z435,z4,z5,z6]),(1,[z42,z1,z2,z4,z364,z6]),(0,[z1,z2,z436,z9,z4,z5,z6]),(0,[z16,z1,z2,z9,z54,z4,z6])],[(0,[z36,z56,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z437,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z438,z6])]],
   [[(0,[z1,z2,z9,z4,z5,z6,z439]),(0,[z1,z60,z2,z9,z41,z5,z6]),(1,[z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z106,z4,z79,z5,z6]),(0,[z1,z440,z2,z9,z4,z5,z6]),(1,[z400,z2,z9,z4,z5,z6])],[(1,[z185,z9,z4,z5,z6,z12]),(0,[z1,z2,z197,z9,z79,z5,z6]),(1,[z1,z2,z9,z4,z342,z72])],[(0,[z17,z1,z192,z9,z4,z5,z6]),(0,[z1,z2,z441,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z442,z5,z6]),(0,[z148,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z443,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z444,z6]),(0,[z445,z1,z2,z9,z4,z5,z6]),(0,[z446,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z447,z6])],[(0,[z1,z2,z9,z4,z448,z5,z6]),(0,[z449,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z450,z6]),(0,[z451,z1,z2,z9,z4,z5,z6]),(0,[z156,z1,z2,z9,z4,z5,z6])],[(1,[z1,z2,z9,z4,z304,z6]),(0,[z1,z2,z9,z4,z5,z452,z6]),(0,[z453,z1,z2,z9,z4,z5,z6]),(0,[z40,z1,z2,z9,z4,z77,z6]),(0,[z1,z8,z9,z4,z354,z5,z6]),(0,[z1,z8,z9,z45,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z327,z6]),(0,[z1,z2,z9,z4,z5,z6,z454]),(0,[z1,z2,z9,z4,z5,z6,z455])],[(0,[z1,z2,z9,z4,z456,z5,z6]),(0,[z185,z2,z9,z4,z5,z6,z12]),(0,[z457,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z9,z118,z5,z104])],[(0,[z1,z9,z105,z4,z5,z6,z12]),(0,[z1,z2,z258,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z12,z146]),(0,[z1,z2,z9,z4,z5,z379,z6])],[(0,[z1,z2,z9,z4,z5,z6,z458]),(0,[z1,z56,z8,z9,z4,z5,z6]),(0,[z96,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z9,z459,z5,z6]),(0,[z1,z76,z80,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z460,z6]),(1,[z1,z2,z4,z5,z6,z347]),(0,[z33,z1,z2,z44,z9,z4,z6]),(0,[z286,z1,z2,z9,z4,z151,z6]),(0,[z1,z2,z9,z118,z4,z5,z6])]],
   [[(0,[z36,z2,z9,z117,z4,z5,z6]),(1,[z148,z2,z9,z4,z71,z6]),(0,[z1,z2,z461,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z342,z5,z6])],[(0,[z462,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z463,z6]),(0,[z464,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z465,z5,z6]),(0,[z466,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z467,z5,z6]),(1,[z25,z1,z184,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z468]),(0,[z340,z1,z8,z9,z4,z5,z6]),(0,[z42,z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z9,z54,z4,z5,z6])],[(0,[z469,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z470]),(0,[z132,z36,z2,z9,z4,z5,z6]),(0,[z471,z1,z2,z9,z4,z5,z6]),(1,[z1,z170,z9,z4,z5,z6]),(0,[z153,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z472,z6]),(0,[z145,z1,z2,z9,z4,z208,z6]),(0,[z1,z157,z2,z9,z4,z5,z6])],[(0,[z473,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z459,z4,z5,z6]),(1,[z1,z157,z9,z4,z5,z6])],[(0,[z1,z2,z9,z474,z4,z5,z6]),(0,[z25,z1,z2,z80,z4,z5,z6]),(0,[z40,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z475]),(0,[z1,z8,z9,z4,z5,z364,z6]),(0,[z1,z2,z4,z79,z5,z364,z6]),(0,[z1,z2,z44,z4,z79,z5,z6])],[(0,[z46,z1,z2,z105,z4,z5,z6]),(0,[z1,z2,z47,z4,z5,z6,z123]),(0,[z25,z1,z2,z4,z79,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z347]),(0,[z1,z8,z9,z4,z5,z6,z146])],[(0,[z1,z2,z9,z4,z5,z476,z6]),(0,[z83,z1,z9,z105,z4,z5,z6]),(0,[z1,z60,z2,z9,z4,z5,z6]),(0,[z1,z76,z60,z9,z4,z5,z6])]],
   [[(0,[z2,z9,z117,z4,z48,z5,z6]),(1,[z1,z2,z9,z4,z209,z6]),(0,[z1,z2,z477,z9,z4,z5,z6]),(0,[z1,z7,z2,z4,z5,z151,z6]),(0,[z1,z2,z9,z478,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z479,z6])],[(0,[z480,z1,z2,z9,z4,z5,z6]),(0,[z39,z1,z9,z4,z77,z5,z6]),(0,[z1,z2,z9,z4,z338,z5,z6])],[(0,[z481,z1,z2,z9,z4,z5,z6]),(0,[z145,z1,z2,z9,z4,z5,z6])],[(0,[z17,z2,z192,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z482,z6]),(0,[z1,z2,z9,z4,z5,z6,z483]),(0,[z285,z1,z9,z4,z5,z6,z12])],[(0,[z1,z9,z4,z75,z5,z110,z6]),(0,[z1,z2,z197,z9,z89,z5,z6]),(0,[z1,z2,z9,z4,z5,z484,z6]),(0,[z285,z1,z2,z9,z4,z5,z151]),(0,[z1,z2,z485,z9,z4,z5,z6])],[],[(0,[z486,z1,z2,z9,z4,z5,z6]),(0,[z1,z192,z9,z4,z5,z6,z12]),(0,[z487,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z488,z6]),(0,[z1,z8,z2,z9,z4,z5,z12]),(1,[z1,z9,z4,z5,z6,z165]),(0,[z1,z2,z9,z4,z5,z6,z489])],[(0,[z490,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z18,z4,z5,z6]),(0,[z1,z103,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z491,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z492,z4,z5,z6]),(0,[z493,z1,z2,z9,z4,z5,z6]),(0,[z494,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z77,z5,z6]),(0,[z1,z2,z9,z495,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z496,z6]),(0,[z1,z2,z9,z4,z5,z497,z6])],[(0,[z46,z1,z2,z47,z4,z5,z6]),(0,[z1,z8,z47,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z498]),(0,[z25,z1,z7,z9,z4,z5,z6]),(1,[z1,z7,z80,z4,z5,z6]),(0,[z1,z9,z4,z342,z5,z6,z12]),(0,[z1,z2,z423,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z499]),(1,[z1,z9,z4,z5,z174,z6])],[(0,[z1,z9,z4,z5,z24,z6,z12]),(0,[z1,z366,z2,z9,z4,z5,z6])],[(0,[z0,z1,z192,z9,z4,z5,z6]),(0,[z1,z2,z9,z500,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z181]),(0,[z1,z2,z9,z4,z501,z5,z6]),(0,[z145,z400,z2,z9,z4,z5,z6]),(0,[z1,z2,z29,z9,z4,z5,z6])],[(0,[z1,z2,z9,z315,z4,z5,z6]),(0,[z153,z1,z2,z9,z4,z5,z24]),(0,[z1,z9,z4,z5,z6,z12,z439]),(1,[z1,z8,z9,z4,z5,z12]),(1,[z1,z2,z197,z89,z5,z6]),(0,[z16,z1,z2,z44,z9,z4,z6])],[(0,[z96,z1,z2,z9,z290,z5,z6]),(0,[z1,z2,z502,z9,z4,z5,z6]),(0,[z1,z251,z9,z4,z5,z24,z6]),(0,[z1,z2,z9,z4,z5,z6,z503]),(0,[z504,z1,z2,z9,z4,z5,z6]),(1,[z145,z1,z2,z9,z5,z146])],[(0,[z505,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z506]),(0,[z1,z507,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z172,z4,z5,z6]),(0,[z1,z2,z9,z4,z67,z6,z72])],[(0,[z1,z2,z9,z4,z5,z508,z6]),(0,[z1,z2,z9,z4,z509,z5,z6]),(0,[z1,z2,z9,z510,z4,z5,z6]),(0,[z511,z1,z2,z9,z4,z5,z6])]],
   [[(0,[z512,z1,z2,z9,z4,z5,z6]),(0,[z513,z1,z2,z9,z4,z5,z6]),(0,[z514,z1,z2,z9,z4,z5,z6]),(0,[z25,z1,z2,z47,z4,z5,z6]),(0,[z148,z1,z2,z9,z4,z49,z6]),(0,[z148,z1,z2,z315,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z515,z6]),(0,[z1,z8,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z516,z4,z5,z6])],[(0,[z1,z2,z9,z4,z517,z5,z6]),(0,[z1,z9,z4,z5,z6,z87,z12]),(0,[z33,z1,z2,z9,z45,z5,z6])],[(0,[z1,z2,z9,z236,z4,z5,z6]),(0,[z1,z2,z9,z518,z4,z5,z6]),(0,[z33,z1,z2,z9,z4,z67,z6]),(0,[z457,z1,z2,z4,z5,z6,z181])],[(0,[z1,z2,z9,z4,z519,z5,z6]),(0,[z520,z1,z2,z9,z4,z5,z6]),(0,[z33,z1,z2,z217,z4,z5,z6]),(0,[z1,z2,z9,z45,z4,z5,z6]),(0,[z1,z521,z2,z9,z4,z5,z6])],[(0,[z1,z9,z4,z5,z49,z6,z12])],[(0,[z522,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z523,z5,z6]),(1,[z346,z2,z9,z4,z5,z6])],[(1,[z1,z8,z9,z4,z5,z6]),(0,[z73,z156,z2,z9,z4,z5,z6])],[(0,[z132,z2,z9,z4,z5,z24,z6]),(0,[z16,z1,z2,z9,z4,z71,z6]),(0,[z1,z2,z524,z9,z4,z5,z6]),(0,[z1,z2,z29,z54,z4,z5,z6])]],
   [[(0,[z46,z148,z2,z9,z4,z5,z6]),(0,[z19,z1,z2,z9,z4,z71,z6]),(0,[z84,z1,z2,z4,z5,z110,z6]),(0,[z1,z2,z4,z43,z5,z364,z6]),(1,[z1,z108,z9,z4,z5,z6]),(1,[z1,z2,z525,z4,z5,z6]),(0,[z1,z2,z526,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z527,z6]),(1,[z1,z2,z217,z4,z5,z6])],[(0,[z1,z2,z9,z528,z4,z5,z6]),(0,[z1,z2,z9,z529,z4,z5,z6]),(0,[z1,z2,z9,z530,z4,z5,z6]),(0,[z1,z2,z9,z4,z531,z5,z6]),(0,[z1,z2,z9,z4,z532,z5,z6]),(0,[z350,z1,z9,z4,z5,z6,z12]),(0,[z533,z1,z2,z9,z4,z5,z6])],[(0,[z1,z534,z2,z9,z4,z5,z6]),(0,[z535,z1,z2,z9,z4,z5,z6]),(0,[z536,z1,z2,z9,z4,z5,z6]),(0,[z1,z377,z2,z9,z4,z5,z6])],[(0,[z537,z1,z2,z9,z4,z5,z6]),(0,[z1,z538,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z539]),(0,[z1,z2,z9,z4,z540,z5,z6]),(0,[z1,z2,z9,z4,z5,z364,z6]),(0,[z1,z2,z4,z5,z151,z6,z123]),(1,[z541,z1,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z542,z6]),(0,[z1,z9,z89,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z6,z146]),(0,[z1,z113,z2,z9,z4,z5,z6])],[(0,[z96,z2,z9,z4,z5,z6,z188])],[(0,[z1,z2,z9,z4,z543,z5,z6]),(0,[z2,z9,z4,z5,z24,z6,z188]),(0,[z1,z8,z2,z9,z4,z5,z327]),(0,[z1,z241,z2,z9,z4,z5,z6]),(0,[z1,z2,z44,z9,z4,z364,z6])]],
   [[(0,[z1,z2,z9,z544,z4,z5,z6]),(0,[z1,z545,z2,z9,z4,z5,z6]),(1,[z1,z440,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z546]),(1,[z97,z1,z2,z9,z4,z6]),(0,[z1,z2,z9,z4,z5,z6,z547]),(0,[z1,z2,z106,z9,z4,z5,z6])],[(0,[z148,z2,z9,z4,z48,z5,z6]),(0,[z19,z2,z9,z4,z5,z49,z6]),(0,[z153,z2,z9,z4,z5,z24,z6]),(0,[z1,z548,z2,z9,z4,z5,z6]),(0,[z1,z9,z167,z4,z5,z6,z12]),(0,[z145,z322,z2,z9,z4,z5,z6]),(0,[z1,z434,z2,z9,z4,z5,z6])],[(0,[z549,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z238]),(0,[z97,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z550]),(0,[z1,z2,z9,z118,z5,z104,z6])],[(0,[z17,z1,z2,z9,z4,z5,z6]),(0,[z1,z9,z117,z4,z5,z6,z12]),(1,[z1,z8,z9,z4,z5,z327]),(0,[z541,z1,z9,z4,z5,z6,z181]),(0,[z1,z2,z9,z4,z342,z6,z72]),(0,[z1,z9,z54,z389,z4,z5,z6])],[(0,[z1,z2,z9,z4,z551,z5,z6]),(0,[z96,z1,z8,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z6,z188]),(0,[z1,z2,z9,z552,z4,z5,z6]),(0,[z1,z8,z9,z184,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z553]),(0,[z1,z2,z9,z4,z5,z6,z554]),(0,[z190,z1,z2,z9,z4,z5,z6]),(0,[z39,z25,z1,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z12,z181]),(0,[z2,z9,z4,z5,z6,z238,z12]),(0,[z1,z2,z555,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z556,z5,z6]),(0,[z1,z2,z9,z4,z557,z5,z6]),(0,[z16,z1,z2,z9,z4,z67,z6]),(0,[z1,z2,z9,z4,z558,z5,z6]),(0,[z1,z2,z9,z54,z4,z6,z72])]],
   [[(0,[z39,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z559,z6]),(0,[z42,z1,z2,z9,z4,z5,z6]),(0,[z560,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z561,z4,z5,z6])],[(0,[z202,z1,z2,z9,z4,z5,z6]),(0,[z285,z1,z8,z9,z4,z5,z6]),(0,[z42,z241,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z562,z4,z5,z6]),(1,[z1,z9,z4,z5,z6,z277]),(0,[z1,z2,z9,z54,z4,z342,z5])],[(0,[z1,z2,z9,z563,z4,z5,z6]),(0,[z564,z1,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z327,z6,z12])],[(0,[z0,z56,z2,z9,z4,z5,z6]),(1,[z1,z226,z9,z4,z5,z6]),(1,[z1,z2,z50,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z565,z6]),(0,[z1,z2,z9,z4,z5,z566,z6]),(0,[z1,z2,z9,z4,z5,z233,z6])],[(0,[z1,z2,z567,z9,z4,z5,z6]),(0,[z40,z1,z9,z4,z5,z110,z6]),(0,[z1,z2,z9,z4,z5,z6,z568])],[(0,[z1,z8,z9,z4,z71,z5,z6]),(0,[z39,z1,z2,z9,z75,z5,z6]),(0,[z1,z2,z9,z4,z5,z569,z6]),(0,[z73,z1,z2,z9,z4,z5,z6]),(0,[z570,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z571,z4,z5,z6]),(0,[z1,z572,z2,z9,z4,z5,z6])],[(0,[z1,z60,z9,z4,z5,z110,z6]),(0,[z1,z2,z44,z9,z4,z5,z6]),(0,[z1,z9,z4,z43,z5,z447,z6])],[(0,[z1,z2,z2,z9,z4,z5,z6]),(0,[z1,z573,z2,z9,z4,z5,z6]),(0,[z1,z47,z9,z4,z5,z6,z12]),(0,[z574,z1,z2,z9,z4,z5,z6]),(0,[z2,z9,z41,z4,z338,z5,z6]),(0,[z1,z2,z9,z516,z4,z5,z6])]],
   [[(0,[z575,z1,z2,z9,z4,z5,z6]),(0,[z40,z1,z2,z9,z4,z110,z6]),(0,[z1,z2,z9,z4,z240,z5,z6])],[(0,[z1,z2,z9,z4,z5,z576,z6]),(0,[z577,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z578]),(0,[z145,z1,z8,z9,z4,z5,z6]),(1,[z457,z1,z2,z4,z5,z6])],[(0,[z579,z1,z2,z9,z4,z5,z6]),(0,[z1,z197,z9,z4,z5,z6,z12]),(0,[z1,z9,z4,z240,z79,z5,z6]),(0,[z1,z2,z9,z4,z380,z79,z6]),(0,[z1,z2,z9,z4,z5,z580,z6])],[(0,[z581,z1,z2,z9,z4,z5,z6]),(1,[z40,z1,z9,z4,z110,z6]),(0,[z285,z1,z440,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z175]),(0,[z145,z1,z2,z525,z4,z5,z6]),(0,[z1,z2,z9,z4,z208,z5,z6])],[(0,[z1,z2,z9,z4,z5,z582,z6]),(0,[z583,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z584,z4,z5,z6]),(1,[z1,z9,z4,z5,z6,z164]),(0,[z40,z1,z76,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z585,z6]),(0,[z166,z2,z9,z41,z4,z5,z6]),(0,[z1,z2,z248,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z586,z5,z6]),(0,[z587,z1,z2,z9,z4,z5,z6])],[]],
   [[(0,[z1,z2,z9,z4,z5,z588,z6]),(0,[z589,z1,z2,z9,z4,z5,z6])],[(0,[z1,z590,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z591,z5,z6]),(0,[z1,z2,z197,z4,z5,z364,z6]),(0,[z285,z1,z2,z9,z4,z5,z123]),(0,[z1,z2,z9,z4,z151,z6,z387]),(0,[z592,z1,z2,z9,z4,z5,z6]),(0,[z16,z235,z2,z9,z4,z5,z6]),(1,[z1,z434,z9,z4,z5,z6])],[(0,[z1,z593,z2,z9,z4,z5,z6])],[(0,[z100,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z105,z4,z79,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z594]),(0,[z36,z1,z2,z9,z117,z5,z6]),(0,[z1,z595,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z596,z5,z6]),(0,[z1,z9,z54,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z6,z597]),(0,[z33,z1,z2,z9,z4,z6,z181])],[(1,[z46,z2,z47,z4,z5,z6])],[(0,[z0,z25,z1,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z598]),(0,[z1,z507,z8,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z43,z5,z6]),(0,[z42,z27,z2,z9,z4,z5,z6])],[(0,[z0,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z599,z9,z4,z5,z6]),(0,[z1,z2,z9,z105,z4,z5,z6]),(0,[z148,z1,z9,z4,z5,z6,z12]),(0,[z600,z1,z2,z9,z4,z5,z6]),(0,[z601,z1,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z151,z6,z419]),(0,[z1,z322,z2,z9,z4,z5,z6]),(0,[z145,z1,z404,z9,z4,z5,z6])],[(0,[z56,z2,z9,z4,z5,z24,z6]),(0,[z1,z8,z9,z4,z5,z110,z6]),(0,[z1,z2,z9,z67,z5,z6,z181]),(0,[z1,z2,z9,z4,z602,z5,z6])]],
   [[(1,[z0,z56,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z603,z6]),(0,[z148,z1,z2,z443,z4,z5,z6])],[(0,[z1,z7,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z604,z6]),(0,[z42,z1,z2,z4,z5,z6,z123]),(0,[z1,z2,z9,z4,z5,z605,z6]),(0,[z1,z2,z9,z4,z5,z6,z332]),(0,[z606,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6,z607])],[(0,[z96,z1,z9,z4,z5,z6,z12]),(0,[z608,z1,z2,z9,z4,z5,z6])],[(0,[z1,z32,z2,z9,z4,z5,z6]),(0,[z1,z2,z89,z4,z43,z5,z6]),(0,[z42,z16,z1,z2,z9,z4,z6]),(0,[z1,z82,z2,z9,z4,z5,z6])],[(0,[z36,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z609,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z188]),(0,[z25,z1,z9,z184,z4,z5,z6]),(0,[z1,z2,z9,z184,z4,z5,z6]),(0,[z1,z2,z610,z9,z4,z5,z6]),(0,[z1,z8,z106,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z611,z6]),(0,[z612,z1,z2,z9,z4,z5,z6])],[(0,[z2,z9,z4,z48,z5,z6,z188]),(0,[z96,z1,z2,z9,z4,z304,z6]),(0,[z1,z60,z2,z9,z75,z5,z6])]],
   [[(0,[z1,z9,z613,z4,z5,z6,z12])],[(0,[z614,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z615,z9,z4,z5,z6]),(0,[z40,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z616,z6]),(0,[z541,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z617,z4,z5,z6])],[(0,[z96,z1,z2,z9,z459,z5,z6]),(0,[z1,z2,z9,z4,z618,z5,z6]),(0,[z1,z7,z9,z4,z5,z6,z12]),(0,[z619,z1,z2,z9,z4,z5,z6]),(1,[z1,z2,z9,z4,z380,z6]),(0,[z1,z2,z9,z4,z620,z5,z6])],[(1,[z100,z2,z105,z4,z5,z6]),(0,[z1,z60,z9,z4,z5,z6,z12]),(1,[z1,z2,z4,z5,z6,z176])],[(0,[z1,z2,z9,z4,z71,z5,z6]),(0,[z1,z2,z9,z621,z4,z5,z6]),(0,[z1,z2,z9,z4,z622,z5,z6]),(0,[z1,z2,z9,z623,z4,z5,z6]),(0,[z1,z346,z2,z9,z4,z5,z6]),(0,[z33,z1,z2,z9,z4,z5,z175])],[],[(0,[z1,z2,z9,z4,z624,z5,z6]),(0,[z132,z2,z9,z4,z48,z5,z6]),(0,[z36,z1,z9,z4,z5,z6,z12]),(0,[z96,z1,z170,z9,z4,z5,z6]),(0,[z145,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z613,z4,z5,z6])],[(0,[z1,z2,z9,z48,z5,z6,z146]),(0,[z1,z2,z625,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z626]),(0,[z39,z1,z9,z4,z75,z5,z6]),(0,[z627,z1,z2,z9,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z4,z5,z628,z6]),(0,[z629,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z630,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z188,z12]),(0,[z1,z9,z184,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z631,z5,z6]),(0,[z632,z1,z2,z9,z4,z5,z6]),(0,[z16,z1,z2,z9,z4,z6,z181]),(0,[z633,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z4,z5,z6]),(1,[z1,z230,z9,z4,z5,z6]),(0,[z1,z2,z9,z634,z4,z5,z6])],[(0,[z2,z9,z105,z4,z5,z49,z6]),(0,[z1,z2,z9,z635,z4,z5,z6]),(0,[z1,z8,z44,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z636]),(0,[z285,z1,z2,z106,z4,z5,z6])],[(0,[z96,z1,z2,z9,z4,z209,z6]),(0,[z1,z2,z9,z637,z4,z5,z6]),(0,[z1,z2,z9,z4,z638,z5,z6]),(0,[z1,z108,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z118,z4,z5,z104])],[(0,[z1,z639,z2,z9,z4,z5,z6]),(0,[z1,z2,z47,z197,z4,z5,z6]),(0,[z1,z2,z443,z9,z4,z5,z6]),(0,[z96,z1,z2,z9,z4,z5,z24]),(0,[z1,z80,z9,z184,z4,z5,z6]),(0,[z1,z7,z80,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z12,z12])],[(0,[z17,z2,z9,z4,z48,z5,z6]),(0,[z148,z2,z9,z105,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z640,z6]),(0,[z285,z25,z1,z2,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z347,z12]),(0,[z641,z1,z2,z9,z4,z5,z6]),(0,[z42,z1,z2,z9,z4,z6,z72]),(1,[z285,z1,z2,z4,z5,z123])],[(0,[z1,z2,z642,z9,z4,z5,z6]),(0,[z1,z643,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z75,z5,z6]),(0,[z11,z1,z2,z9,z4,z5,z6]),(0,[z73,z1,z2,z9,z79,z5,z6]),(0,[z42,z1,z2,z4,z5,z364,z6]),(0,[z644,z1,z2,z9,z4,z5,z6]),(0,[z645,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z54,z4,z5,z104])],[(0,[z2,z9,z105,z4,z5,z24,z6]),(0,[z1,z2,z9,z4,z5,z6,z646]),(0,[z39,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z647,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z648])]],
   [[(0,[z46,z2,z9,z4,z48,z5,z6]),(0,[z1,z2,z4,z5,z6,z347,z12]),(0,[z33,z1,z2,z9,z5,z6,z181]),(0,[z1,z2,z9,z4,z5,z6,z649]),(0,[z1,z2,z9,z4,z5,z6,z72])],[(0,[z1,z9,z4,z79,z5,z6,z12]),(0,[z73,z1,z2,z197,z4,z5,z6]),(0,[z650,z1,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z651,z5,z6]),(0,[z96,z2,z9,z105,z4,z5,z6]),(0,[z1,z2,z9,z4,z652,z5,z6]),(0,[z505,z1,z9,z4,z5,z6,z12]),(0,[z1,z2,z653,z9,z4,z5,z6])],[(0,[z1,z2,z197,z105,z4,z5,z6]),(0,[z1,z2,z9,z654,z4,z5,z6]),(0,[z1,z2,z9,z4,z655,z5,z6]),(0,[z656,z1,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z79,z5,z6]),(0,[z1,z2,z44,z9,z4,z6,z72]),(0,[z657,z1,z2,z9,z4,z5,z6])],[(0,[z1,z8,z9,z4,z5,z6,z12]),(0,[z73,z1,z8,z9,z4,z5,z6]),(0,[z73,z366,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z43,z5,z6]),(0,[z658,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z525,z9,z4,z5,z6])],[(0,[z1,z2,z9,z659,z4,z5,z6]),(0,[z660,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z661,z4,z5,z6]),(0,[z1,z9,z4,z638,z5,z6,z12]),(0,[z33,z1,z436,z9,z4,z5,z6]),(0,[z203,z1,z2,z9,z4,z5,z6])],[(0,[z1,z662,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z663,z5,z6]),(0,[z42,z1,z7,z2,z4,z5,z6]),(0,[z1,z9,z41,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z6,z664]),(0,[z1,z2,z9,z4,z5,z110,z6]),(0,[z1,z2,z9,z4,z665,z5,z6]),(1,[z1,z9,z4,z5,z6,z419]),(0,[z145,z1,z2,z9,z4,z5,z104])],[(0,[z1,z2,z9,z4,z666,z5,z6]),(0,[z667,z1,z2,z9,z4,z5,z6]),(0,[z1,z668,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z669,z5,z6]),(0,[z1,z2,z9,z4,z670,z5,z6])]],
   [[(0,[z1,z2,z671,z9,z4,z5,z6]),(0,[z672,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z673]),(0,[z1,z2,z9,z4,z5,z6,z674]),(0,[z1,z675,z2,z9,z4,z5,z6]),(1,[z286,z1,z2,z9,z4,z6]),(0,[z1,z2,z9,z45,z67,z5,z6])],[(0,[z132,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z676]),(0,[z19,z148,z2,z9,z4,z5,z6]),(0,[z1,z365,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z677,z6]),(0,[z1,z678,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z679,z6]),(0,[z1,z2,z9,z4,z5,z6,z387])],[(0,[z1,z2,z9,z4,z5,z680,z6]),(0,[z1,z8,z9,z105,z4,z5,z6]),(0,[z1,z2,z681,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z682,z6]),(0,[z1,z2,z89,z4,z79,z5,z6])],[(0,[z148,z2,z9,z4,z71,z5,z6]),(0,[z1,z2,z9,z4,z683,z5,z6]),(0,[z1,z2,z197,z106,z4,z5,z6]),(1,[z1,z436,z9,z4,z5,z6])],[(0,[z148,z1,z8,z9,z4,z5,z6]),(0,[z169,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z684,z5,z6]),(0,[z1,z2,z9,z4,z685,z5,z6])],[(0,[z686,z1,z2,z9,z4,z5,z6]),(0,[z96,z2,z9,z4,z5,z49,z6]),(0,[z1,z9,z4,z342,z5,z174,z6]),(0,[z1,z2,z9,z389,z4,z5,z6])],[(0,[z1,z8,z80,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z6,z6])],[(0,[z56,z2,z192,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z290,z5,z6]),(0,[z687,z1,z2,z9,z4,z5,z6]),(1,[z1,z9,z4,z5,z447,z6]),(0,[z688,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z689]),(0,[z16,z203,z2,z9,z4,z5,z6])]],
   [[(0,[z1,z690,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z691]),(1,[z1,z2,z55,z4,z5,z6])],[(0,[z1,z2,z9,z692,z4,z5,z6]),(0,[z73,z1,z2,z9,z89,z5,z6])],[(0,[z1,z693,z2,z9,z4,z5,z6]),(0,[z1,z2,z694,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z151,z6])],[(0,[z17,z1,z56,z9,z4,z5,z6]),(0,[z46,z1,z2,z9,z4,z5,z6]),(0,[z96,z132,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z695,z5,z6]),(0,[z1,z2,z9,z696,z4,z5,z6]),(0,[z1,z2,z404,z9,z4,z5,z6])],[(0,[z96,z17,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z697,z5,z6]),(0,[z1,z2,z9,z4,z5,z698,z6]),(0,[z36,z2,z9,z4,z5,z6,z188])],[(0,[z699,z1,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z49,z6]),(0,[z1,z7,z2,z197,z4,z5,z6]),(0,[z1,z80,z9,z4,z5,z110,z6]),(0,[z205,z1,z2,z9,z4,z5,z6]),(1,[z235,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z700,z4,z5,z6]),(0,[z1,z2,z9,z118,z48,z5,z6]),(0,[z1,z2,z9,z4,z5,z5,z6]),(0,[z1,z8,z60,z9,z4,z5,z6]),(0,[z1,z2,z701,z9,z4,z5,z6]),(0,[z42,z1,z2,z9,z45,z4,z6]),(0,[z1,z2,z9,z4,z5,z6,z702])],[(1,[z1,z2,z316,z4,z5,z6]),(0,[z153,z1,z2,z9,z4,z5,z188]),(0,[z40,z1,z8,z9,z4,z5,z6]),(0,[z1,z2,z703,z9,z4,z5,z6]),(0,[z704,z1,z2,z9,z4,z5,z6]),(0,[z705,z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z9,z4,z707,z6]),(0,[z1,z2,z4,z708,z5,z6]),(0,[z2,z9,z4,z709,z5,z6]),(0,[z1,z710,z9,z4,z5,z99]),(0,[z1,z710,z9,z4,z5,z6]),(0,[z1,z82,z28,z4,z5,z6])],[(0,[z1,z2,z711,z4,z5,z6]),(0,[z1,z9,z712,z4,z5,z6]),(0,[z713,z9,z4,z5,z6,z12]),(0,[z1,z9,z4,z5,z327,z714]),(0,[z1,z2,z9,z4,z380,z6]),(0,[z1,z2,z9,z118,z5,z715])],[(0,[z96,z2,z9,z4,z5,z458]),(0,[z1,z2,z4,z716,z5,z6]),(0,[z1,z8,z9,z4,z5,z475]),(0,[z1,z106,z4,z5,z151,z12]),(0,[z1,z9,z4,z717,z5,z6]),(0,[z1,z2,z4,z5,z6,z176]),(0,[z1,z9,z4,z718,z5,z6]),(0,[z719,z1,z9,z4,z5,z6])],[(0,[z27,z2,z105,z4,z5,z6]),(0,[z1,z2,z9,z4,z720,z6]),(0,[z1,z9,z4,z5,z6,z721]),(0,[z1,z9,z118,z5,z104,z12]),(0,[z42,z1,z2,z4,z78,z6]),(0,[z285,z1,z248,z4,z5,z123]),(0,[z1,z2,z722,z4,z5,z6])],[(0,[z1,z723,z9,z4,z5,z6]),(0,[z724,z1,z9,z4,z5,z6]),(0,[z11,z4,z5,z6,z238,z12]),(0,[z1,z2,z44,z4,z725,z6]),(0,[z33,z1,z2,z9,z99,z181]),(0,[z1,z9,z4,z5,z6,z726]),(0,[z322,z2,z9,z5,z6,z146]),(0,[z1,z2,z9,z727,z4,z5])],[(0,[z148,z2,z9,z4,z697,z6]),(0,[z1,z131,z4,z5,z6,z12]),(0,[z153,z2,z9,z4,z5,z225]),(0,[z1,z728,z9,z4,z5,z6])],[(0,[z1,z226,z236,z4,z5,z6]),(0,[z729,z2,z9,z4,z5,z6])],[(0,[z730,z1,z131,z4,z5,z6]),(0,[z1,z731,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z732]),(0,[z153,z2,z9,z290,z5,z6]),(0,[z11,z185,z4,z5,z6,z12])]],
   [[(0,[z1,z2,z4,z5,z6,z733]),(0,[z1,z8,z9,z4,z5,z483]),(0,[z1,z8,z9,z4,z5,z542]),(0,[z1,z377,z217,z4,z5,z6])],[(0,[z1,z2,z734,z4,z5,z6]),(0,[z25,z1,z226,z4,z5,z6]),(0,[z1,z9,z563,z4,z5,z12]),(0,[z39,z11,z1,z4,z5,z6]),(0,[z1,z2,z735,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z175])],[(0,[z132,z9,z48,z5,z6,z12]),(0,[z1,z2,z9,z459,z209,z6]),(0,[z1,z2,z9,z736,z5,z6]),(0,[z11,z1,z4,z5,z110,z6]),(0,[z2,z9,z737,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z12]),(0,[z1,z9,z4,z5,z738,z6]),(0,[z1,z2,z9,z4,z5,z739]),(0,[z1,z2,z9,z4,z5,z740]),(0,[z25,z1,z216,z4,z5,z6]),(0,[z11,z1,z8,z4,z5,z12]),(0,[z741,z9,z4,z5,z6,z12]),(0,[z1,z9,z4,z742,z5,z6]),(0,[z33,z1,z2,z9,z6,z181])],[(0,[z286,z1,z7,z2,z4,z6]),(0,[z1,z2,z9,z4,z743,z6]),(0,[z1,z2,z4,z744,z5,z6]),(1,[z1,z2,z9,z6,z745]),(0,[z1,z2,z9,z727,z4,z6])],[(0,[z2,z9,z746,z4,z5,z6]),(0,[z1,z443,z4,z5,z6,z12]),(0,[z1,z2,z747,z4,z5,z6]),(0,[z96,z2,z9,z4,z5,z188]),(0,[z2,z29,z748,z4,z5,z6])],[(0,[z2,z9,z105,z4,z304,z6]),(0,[z27,z2,z47,z4,z5,z6]),(0,[z153,z2,z9,z4,z5,z749]),(0,[z1,z168,z9,z4,z5,z6]),(0,[z1,z2,z9,z750,z5,z6]),(0,[z1,z2,z4,z751,z5,z6]),(0,[z1,z2,z173,z4,z5,z6]),(0,[z1,z2,z9,z4,z752,z6]),(0,[z1,z9,z4,z5,z753,z6])],[(0,[z2,z9,z4,z5,z24,z325]),(0,[z1,z2,z9,z4,z5,z754]),(0,[z2,z9,z4,z5,z6,z755]),(0,[z1,z756,z9,z4,z5,z6]),(0,[z203,z2,z9,z4,z5,z6]),(0,[z1,z9,z459,z5,z6,z12]),(0,[z1,z8,z757,z4,z5,z6]),(0,[z457,z1,z4,z5,z6,z277]),(0,[z758,z1,z9,z4,z5,z6])]],
   [[(0,[z1,z9,z4,z759,z5,z6]),(0,[z97,z1,z7,z2,z4,z6]),(0,[z1,z9,z4,z380,z6,z12]),(0,[z1,z436,z173,z4,z5,z6]),(0,[z457,z760,z2,z4,z5,z6]),(0,[z1,z2,z761,z4,z5,z6])],[(0,[z1,z8,z50,z4,z5,z6]),(0,[z2,z9,z4,z5,z749,z188]),(0,[z1,z2,z4,z762,z5,z6]),(0,[z1,z2,z763,z4,z5,z6]),(0,[z1,z2,z106,z4,z151,z387]),(1,[z1,z2,z9,z5,z715])],[(0,[z73,z1,z79,z5,z6,z12]),(0,[z1,z9,z5,z6,z12,z764])],[(0,[z1,z765,z9,z4,z5,z6]),(0,[z1,z8,z4,z766,z5,z6]),(0,[z73,z1,z8,z79,z5,z6]),(0,[z1,z9,z4,z5,z767,z6]),(0,[z1,z9,z4,z5,z6,z768]),(0,[z1,z2,z29,z4,z6,z72])],[(0,[z1,z2,z769,z4,z5,z6]),(0,[z1,z2,z9,z770,z5,z6]),(0,[z1,z2,z771,z4,z5,z6]),(0,[z1,z772,z9,z4,z5,z6])],[(0,[z83,z36,z9,z4,z5,z6]),(0,[z220,z2,z105,z4,z5,z6]),(0,[z63,z2,z47,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z773]),(0,[z1,z230,z9,z4,z304,z6]),(0,[z147,z2,z9,z290,z5,z6]),(0,[z1,z9,z4,z5,z6,z419]),(0,[z1,z2,z9,z4,z774,z6]),(0,[z1,z2,z775,z4,z5,z6]),(0,[z1,z9,z4,z776,z110,z6]),(0,[z11,z1,z8,z4,z5,z6]),(0,[z1,z525,z4,z5,z6,z12]),(0,[z1,z9,z4,z777,z6,z12]),(0,[z1,z778,z9,z4,z5,z6])],[(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z780]),(0,[z25,z1,z4,z227,z5,z6]),(0,[z366,z2,z4,z79,z5,z6]),(0,[z1,z2,z9,z4,z5,z781]),(0,[z782,z2,z9,z4,z5,z6]),(0,[z286,z1,z9,z4,z6,z419])],[(0,[z17,z192,z9,z4,z5,z6]),(0,[z593,z2,z9,z4,z5,z24]),(0,[z783,z1,z2,z9,z4,z6]),(0,[z1,z7,z784,z4,z5,z6]),(0,[z9,z4,z5,z6,z12,z785]),(0,[z286,z1,z2,z9,z4,z6]),(0,[z1,z9,z4,z5,z786,z6]),(0,[z145,z1,z2,z525,z5,z146]),(0,[z145,z147,z2,z9,z5,z146])]],
   [[(0,[z1,z230,z9,z459,z5,z6]),(0,[z787,z2,z9,z4,z5,z6]),(0,[z1,z44,z4,z43,z6,z12]),(0,[z1,z788,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z233,z6]),(0,[z789,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z790]),(0,[z1,z9,z4,z5,z6,z791]),(0,[z2,z615,z105,z4,z5,z6]),(0,[z792,z1,z9,z4,z5,z6]),(0,[z1,z793,z9,z4,z5,z6]),(0,[z1,z9,z4,z240,z5,z6]),(0,[z9,z4,z5,z6,z238,z12]),(0,[z505,z9,z4,z5,z6,z238]),(0,[z11,z185,z2,z4,z5,z6]),(0,[z1,z9,z4,z6,z387,z419])],[(0,[z794,z192,z9,z4,z5,z6]),(0,[z1,z2,z795,z4,z5,z6]),(0,[z796,z1,z2,z4,z5,z6]),(0,[z1,z436,z9,z4,z5,z6]),(0,[z42,z366,z2,z4,z5,z6]),(0,[z1,z2,z22,z4,z43,z6]),(0,[z1,z2,z9,z5,z715,z146])],[(0,[z0,z56,z236,z4,z5,z6]),(0,[z56,z2,z9,z290,z5,z6]),(0,[z39,z1,z9,z75,z5,z6]),(0,[z797,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z588]),(0,[z798,z1,z2,z4,z5,z6])],[(0,[z83,z1,z197,z4,z5,z6]),(0,[z96,z9,z4,z5,z188,z12]),(0,[z799,z2,z9,z4,z5,z6]),(0,[z2,z9,z800,z4,z5,z6]),(0,[z63,z2,z106,z4,z5,z151])],[(0,[z17,z9,z4,z5,z6,z164]),(0,[z1,z9,z4,z5,z6,z801]),(0,[z392,z2,z9,z4,z49,z6]),(0,[z1,z2,z9,z4,z802,z6]),(0,[z1,z9,z4,z5,z472,z12]),(0,[z1,z2,z9,z4,z5,z714])],[(0,[z148,z2,z9,z290,z5,z6]),(0,[z1,z9,z4,z5,z447,z6]),(0,[z135,z185,z9,z4,z5,z12]),(0,[z803,z1,z9,z4,z5,z6])],[(0,[z1,z2,z804,z4,z5,z6]),(0,[z1,z2,z805,z4,z5,z6]),(0,[z1,z806,z9,z4,z5,z6]),(0,[z42,z1,z2,z4,z6,z383]),(0,[z1,z2,z55,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z118,z5,z361]),(0,[z145,z1,z2,z9,z5,z715])],[(0,[z1,z230,z9,z4,z209,z6]),(0,[z84,z1,z4,z5,z6,z12]),(0,[z1,z9,z4,z807,z5,z6]),(0,[z16,z1,z2,z54,z55,z4])],[(0,[z0,z9,z661,z4,z5,z6]),(0,[z46,z8,z47,z4,z5,z6]),(0,[z1,z808,z9,z4,z5,z6]),(0,[z11,z1,z76,z4,z5,z6]),(0,[z42,z1,z2,z173,z4,z6]),(0,[z1,z2,z28,z4,z208,z6])],[(0,[z1,z2,z9,z4,z809,z6]),(0,[z96,z2,z9,z290,z5,z188]),(0,[z1,z2,z4,z810,z5,z6]),(0,[z811,z2,z9,z4,z5,z6])],[(0,[z2,z443,z105,z4,z5,z6]),(0,[z730,z1,z9,z4,z5,z6]),(0,[z2,z9,z117,z290,z5,z6]),(0,[z1,z9,z4,z77,z6,z664]),(0,[z73,z1,z2,z247,z5,z6]),(0,[z812,z1,z9,z4,z5,z6]),(0,[z286,z1,z2,z106,z4,z151]),(0,[z813,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z5,z6,z745])],[(0,[z1,z814,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z815]),(0,[z1,z2,z316,z4,z5,z6]),(0,[z1,z2,z816,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z546]),(0,[z1,z9,z4,z5,z484,z12]),(0,[z1,z817,z9,z4,z5,z6]),(0,[z34,z2,z173,z4,z5,z6])],[(0,[z1,z818,z9,z4,z5,z6]),(0,[z564,z1,z9,z4,z5,z12]),(0,[z11,z1,z4,z5,z6,z12]),(0,[z1,z819,z9,z4,z5,z6]),(0,[z33,z1,z2,z9,z247,z6])]],
   [[(0,[z46,z2,z9,z290,z5,z6]),(0,[z294,z2,z47,z4,z5,z6]),(0,[z1,z820,z9,z4,z5,z6])],[(0,[z132,z2,z131,z48,z5,z6]),(0,[z39,z1,z9,z684,z5,z6]),(0,[z1,z2,z28,z4,z5,z6])],[(0,[z1,z821,z9,z4,z5,z6]),(0,[z33,z1,z8,z9,z6,z181])],[(0,[z42,z1,z2,z4,z410,z6]),(0,[z1,z9,z4,z5,z6,z822]),(0,[z1,z82,z9,z4,z208,z6])],[(0,[z1,z2,z197,z530,z5,z6]),(0,[z1,z2,z9,z823,z5,z6]),(0,[z166,z2,z258,z4,z5,z6]),(0,[z824,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z825,z6]),(0,[z16,z1,z9,z54,z4,z12]),(0,[z826,z9,z4,z5,z6,z12])],[(0,[z2,z315,z4,z48,z5,z6]),(0,[z2,z9,z4,z5,z24,z223]),(0,[z2,z9,z4,z5,z827,z6]),(0,[z203,z2,z9,z4,z49,z6]),(1,[z11,z185,z4,z5,z6]),(0,[z1,z9,z4,z828,z6,z12]),(0,[z235,z9,z4,z5,z6,z12]),(0,[z1,z2,z197,z623,z5,z6]),(0,[z322,z2,z9,z118,z5,z6]),(0,[z829,z2,z9,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z830]),(0,[z1,z9,z4,z5,z386,z12]),(0,[z73,z1,z240,z79,z5,z6])],[(0,[z1,z831,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z832,z6]),(0,[z1,z2,z9,z4,z5,z833]),(0,[z308,z1,z9,z4,z110,z6])]],
   [[(0,[z34,z2,z9,z4,z5,z6]),(0,[z1,z2,z834,z4,z5,z6]),(0,[z2,z9,z290,z5,z49,z6]),(0,[z1,z9,z4,z750,z5,z6]),(0,[z1,z8,z9,z4,z380,z6]),(0,[z73,z1,z2,z810,z5,z6]),(0,[z1,z9,z835,z4,z5,z6]),(0,[z33,z1,z377,z9,z6,z181]),(0,[z147,z2,z836,z4,z5,z6])],[(0,[z100,z8,z105,z4,z5,z6]),(0,[z1,z837,z9,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z176]),(0,[z1,z9,z4,z5,z6,z838]),(0,[z1,z839,z9,z4,z5,z6])],[(0,[z17,z280,z9,z4,z5,z6]),(0,[z1,z840,z9,z4,z5,z6]),(0,[z96,z2,z9,z4,z5,z553]),(0,[z148,z9,z4,z71,z6,z12]),(0,[z1,z2,z50,z4,z304,z6]),(0,[z1,z82,z9,z4,z5,z6]),(0,[z2,z9,z4,z5,z6,z841]),(0,[z1,z9,z4,z5,z515,z12]),(0,[z241,z2,z4,z5,z6,z123]),(0,[z400,z2,z28,z4,z5,z6])],[(0,[z1,z2,z9,z4,z842,z6]),(0,[z1,z251,z9,z4,z5,z6]),(0,[z84,z1,z2,z4,z5,z6]),(0,[z1,z843,z9,z4,z5,z6])],[(0,[z63,z2,z9,z4,z5,z6]),(0,[z1,z2,z844,z4,z5,z6]),(0,[z1,z7,z4,z240,z5,z6])],[(0,[z1,z2,z9,z4,z6,z845]),(0,[z1,z846,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z85,z12]),(0,[z1,z2,z50,z459,z5,z6]),(0,[z847,z2,z9,z4,z5,z6]),(0,[z201,z11,z1,z4,z5,z6]),(0,[z729,z8,z9,z4,z5,z6]),(1,[z1,z2,z810,z5,z6]),(0,[z337,z1,z2,z9,z5,z146])],[(0,[z1,z9,z4,z5,z6,z848]),(0,[z1,z849,z9,z4,z5,z6]),(0,[z1,z2,z850,z4,z5,z6]),(0,[z851,z2,z9,z4,z5,z6]),(1,[z1,z9,z4,z5,z714]),(0,[z852,z1,z2,z9,z4,z6]),(0,[z1,z9,z853,z4,z5,z6])],[(0,[z1,z854,z9,z4,z5,z6]),(0,[z1,z28,z4,z5,z6,z12]),(0,[z1,z9,z4,z5,z6,z855])]],
   [[(0,[z856,z1,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z303,z12]),(0,[z147,z2,z9,z117,z5,z6]),(0,[z1,z2,z9,z4,z5,z857]),(0,[z1,z858,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z859]),(0,[z1,z860,z9,z4,z5,z6]),(0,[z322,z2,z9,z4,z233,z6])],[(0,[z100,z105,z4,z5,z6,z12]),(0,[z861,z2,z9,z4,z5,z6]),(0,[z11,z1,z2,z4,z5,z6]),(0,[z862,z1,z2,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z863]),(0,[z1,z2,z9,z864,z5,z6])],[(0,[z17,z230,z9,z4,z5,z6]),(0,[z1,z865,z9,z4,z5,z6]),(0,[z1,z170,z316,z4,z5,z6]),(0,[z1,z76,z9,z4,z622,z6]),(0,[z25,z185,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z866,z6]),(0,[z337,z1,z2,z9,z6,z181])],[(0,[z25,z1,z236,z4,z5,z6]),(0,[z1,z2,z867,z4,z5,z6]),(0,[z560,z1,z2,z79,z5,z6]),(0,[z400,z82,z9,z4,z5,z6]),(0,[z145,z2,z9,z5,z332,z146]),(0,[z2,z9,z4,z5,z6,z868])],[(0,[z1,z2,z869,z4,z5,z6]),(0,[z132,z2,z9,z870,z5,z6]),(0,[z1,z871,z9,z4,z5,z6]),(0,[z1,z2,z316,z290,z5,z6]),(0,[z872,z2,z9,z4,z5,z6]),(0,[z25,z1,z784,z4,z5,z6])],[(0,[z1,z2,z9,z4,z873,z6]),(0,[z1,z2,z784,z4,z5,z6]),(0,[z874,z1,z2,z4,z5,z6]),(0,[z1,z875,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z876])],[(0,[z2,z9,z4,z338,z5,z6]),(0,[z1,z2,z131,z4,z5,z6]),(0,[z2,z9,z4,z870,z5,z6]),(0,[z1,z2,z50,z4,z209,z6]),(0,[z1,z2,z258,z4,z5,z6]),(0,[z9,z4,z338,z5,z6,z12]),(0,[z1,z9,z4,z5,z776,z6]),(0,[z135,z1,z9,z4,z5,z12]),(0,[z11,z1,z167,z4,z5,z6]),(0,[z877,z2,z9,z4,z5,z6]),(0,[z1,z878,z9,z4,z5,z6]),(0,[z33,z1,z2,z6,z176,z181])],[(0,[z1,z8,z9,z4,z5,z458]),(0,[z1,z2,z9,z4,z5,z879]),(0,[z1,z2,z880,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z881]),(0,[z882,z2,z9,z4,z5,z6]),(0,[z40,z1,z9,z4,z379,z6]),(0,[z1,z8,z883,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z884,z5,z6]),(0,[z1,z80,z4,z5,z62,z6]),(0,[z1,z2,z885,z4,z5,z6]),(0,[z4,z5,z6,z238,z347,z12]),(0,[z1,z2,z9,z5,z6,z715])],[(0,[z1,z2,z886,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z887]),(0,[z1,z2,z44,z4,z420,z6]),(0,[z1,z377,z9,z4,z5,z175]),(0,[z2,z9,z888,z4,z5,z6])],[(0,[z147,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z776,z6]),(0,[z11,z185,z1,z4,z5,z6]),(0,[z1,z2,z9,z45,z67,z6]),(0,[z1,z889,z9,z4,z5,z6]),(0,[z1,z113,z9,z4,z342,z72])],[(0,[z1,z2,z890,z4,z5,z6]),(0,[z46,z2,z891,z4,z5,z6]),(0,[z1,z892,z9,z4,z5,z6]),(0,[z1,z9,z4,z893,z5,z6]),(0,[z1,z2,z106,z4,z5,z151])],[(0,[z156,z2,z9,z4,z5,z6]),(0,[z1,z894,z9,z4,z5,z6]),(0,[z1,z895,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z896,z6]),(0,[z1,z55,z4,z5,z6,z12]),(0,[z1,z168,z9,z4,z6,z387]),(0,[z897,z2,z9,z4,z5,z6])],[(0,[z2,z9,z4,z5,z6,z898]),(0,[z1,z899,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z725,z6]),(0,[z16,z1,z2,z29,z54,z4])],[(0,[z100,z226,z105,z4,z5,z6]),(0,[z1,z2,z9,z4,z900,z6]),(0,[z132,z2,z9,z48,z5,z6]),(0,[z1,z2,z9,z4,z901,z6]),(0,[z1,z2,z4,z5,z151,z268]),(0,[z1,z76,z9,z4,z77,z6]),(0,[z902,z2,z9,z4,z5,z6])],[(0,[z1,z2,z903,z4,z5,z6]),(0,[z1,z2,z9,z4,z6,z904]),(0,[z201,z1,z9,z75,z5,z6]),(0,[z905,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z906,z5,z6])]],
   [[(0,[z1,z2,z907,z4,z5,z6]),(0,[z1,z2,z9,z4,z908,z6]),(0,[z1,z9,z4,z5,z6,z909]),(0,[z1,z821,z315,z4,z5,z6]),(0,[z166,z2,z4,z227,z5,z6]),(0,[z346,z436,z9,z4,z5,z6]),(0,[z910,z1,z9,z4,z5,z6])],[(0,[z166,z2,z9,z4,z5,z6]),(0,[z2,z9,z4,z827,z49,z6]),(0,[z1,z315,z4,z5,z6,z12]),(0,[z153,z9,z4,z5,z24,z12]),(0,[z322,z2,z28,z4,z5,z6]),(0,[z147,z2,z911,z4,z5,z6]),(0,[z1,z2,z836,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z797,z8,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z6,z745]),(0,[z1,z9,z912,z4,z5,z6])],[(0,[z2,z9,z172,z4,z5,z6]),(0,[z1,z9,z4,z5,z698,z12]),(0,[z1,z913,z9,z4,z5,z6]),(1,[z2,z9,z4,z5,z749]),(0,[z2,z9,z4,z914,z5,z6]),(0,[z147,z9,z4,z5,z6,z12])],[(0,[z1,z915,z9,z4,z5,z6]),(0,[z1,z916,z9,z4,z5,z6]),(0,[z1,z230,z50,z4,z5,z6]),(0,[z796,z1,z4,z5,z6,z164]),(0,[z917,z1,z2,z9,z4,z6]),(0,[z918,z9,z172,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z919])],[(0,[z46,z2,z681,z4,z5,z6]),(0,[z97,z25,z1,z2,z4,z6]),(0,[z135,z1,z9,z4,z5,z714]),(0,[z9,z4,z5,z6,z868,z165])],[(0,[z920,z1,z2,z4,z5,z6]),(0,[z2,z9,z4,z71,z827,z6]),(0,[z153,z2,z9,z4,z5,z24]),(0,[z9,z4,z5,z6,z12,z841]),(0,[z1,z8,z55,z4,z5,z6]),(0,[z921,z1,z2,z9,z4,z6]),(0,[z1,z9,z4,z5,z6,z922]),(0,[z1,z2,z9,z4,z6,z387])],[(0,[z83,z9,z4,z5,z24,z6]),(0,[z42,z83,z1,z4,z5,z6]),(0,[z686,z2,z9,z48,z5,z6]),(0,[z923,z2,z9,z4,z5,z6]),(0,[z1,z924,z9,z4,z5,z6]),(0,[z1,z2,z106,z4,z5,z580]),(0,[z1,z2,z89,z810,z5,z6]),(0,[z42,z1,z2,z409,z4,z6]),(0,[z33,z34,z2,z9,z6,z181]),(0,[z1,z2,z9,z4,z5,z715])]],
   [[(0,[z1,z2,z925,z4,z5,z6]),(0,[z56,z9,z4,z74,z5,z6]),(0,[z926,z2,z9,z4,z5,z6]),(0,[z185,z9,z4,z5,z6,z238]),(0,[z1,z2,z44,z4,z6,z234]),(0,[z203,z2,z927,z4,z5,z6])],[(0,[z418,z2,z105,z4,z5,z6]),(0,[z39,z1,z9,z150,z5,z6]),(0,[z2,z106,z172,z4,z5,z151]),(0,[z1,z2,z173,z4,z5,z99])],[(0,[z1,z2,z9,z928,z5,z6]),(0,[z1,z9,z4,z5,z929,z6]),(0,[z166,z9,z4,z5,z6,z12]),(0,[z11,z1,z41,z4,z5,z6]),(0,[z84,z1,z8,z4,z5,z6]),(0,[z1,z2,z4,z725,z364,z6]),(0,[z33,z1,z2,z217,z6,z181]),(0,[z322,z82,z9,z4,z5,z6])],[(0,[z1,z9,z4,z5,z576,z12]),(0,[z1,z2,z9,z4,z930,z6]),(0,[z1,z8,z9,z4,z5,z682]),(0,[z235,z8,z9,z4,z5,z6]),(0,[z1,z931,z9,z4,z5,z6])],[(0,[z19,z2,z9,z4,z49,z6]),(0,[z1,z8,z9,z4,z5,z626]),(0,[z285,z1,z2,z4,z5,z626]),(0,[z1,z404,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z932]),(0,[z1,z2,z9,z4,z208,z6]),(0,[z1,z404,z9,z4,z233,z6])],[(0,[z1,z933,z9,z4,z5,z6]),(0,[z1,z8,z316,z4,z5,z6]),(0,[z25,z1,z4,z5,z6,z419]),(0,[z934,z1,z2,z4,z5,z6])],[(0,[z1,z9,z4,z5,z582,z12]),(1,[z1,z784,z4,z5,z6]),(0,[z1,z2,z44,z4,z43,z6])],[(0,[z1,z9,z4,z5,z6,z935]),(0,[z1,z936,z9,z4,z5,z6]),(0,[z1,z9,z4,z596,z110,z6]),(0,[z9,z4,z5,z6,z12,z332]),(0,[z937,z2,z9,z4,z5,z6])]],
   [[(0,[z1,z2,z938,z4,z5,z6]),(0,[z939,z2,z9,z4,z5,z6]),(0,[z1,z217,z4,z5,z6,z12]),(0,[z1,z9,z4,z5,z940,z6]),(0,[z1,z8,z28,z4,z5,z6]),(0,[z1,z8,z29,z4,z5,z6]),(0,[z1,z2,z9,z4,z6,z941])],[(0,[z1,z2,z4,z5,z942,z6]),(0,[z97,z1,z2,z105,z4,z6]),(0,[z25,z1,z4,z240,z5,z6]),(0,[z285,z1,z2,z4,z5,z943]),(0,[z1,z2,z944,z4,z5,z6]),(0,[z1,z2,z927,z4,z5,z6])],[(0,[z1,z2,z9,z4,z945,z6]),(0,[z1,z2,z4,z227,z5,z6]),(0,[z946,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z6]),(0,[z1,z2,z947,z4,z5,z6]),(1,[z1,z9,z4,z776,z6]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z1,z4,z5,z6,z949,z12]),(0,[z203,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z5,z99])],[(0,[z185,z2,z9,z4,z5,z6]),(0,[z241,z2,z9,z4,z5,z6]),(0,[z166,z80,z9,z4,z5,z6]),(0,[z1,z8,z4,z5,z62,z6]),(0,[z1,z8,z950,z4,z5,z6]),(0,[z1,z9,z118,z5,z104,z165])],[(0,[z1,z2,z951,z4,z5,z6]),(0,[z17,z794,z9,z4,z5,z6]),(0,[z96,z2,z9,z4,z304,z188]),(0,[z135,z9,z4,z5,z238,z12]),(0,[z135,z1,z4,z5,z347,z12]),(0,[z952,z2,z9,z4,z5,z6]),(0,[z1,z436,z9,z4,z5,z99]),(0,[z33,z1,z2,z9,z6,z745]),(0,[z1,z2,z953,z4,z5,z6]),(0,[z400,z2,z9,z4,z208,z6])],[(0,[z1,z2,z9,z4,z5,z954]),(0,[z25,z1,z4,z5,z447,z6]),(0,[z1,z2,z9,z4,z955,z6]),(0,[z1,z2,z956,z4,z5,z6])],[(0,[z185,z56,z9,z4,z5,z6]),(1,[z2,z891,z4,z5,z6]),(0,[z1,z957,z9,z4,z5,z6]),(0,[z34,z8,z9,z4,z5,z6]),(0,[z8,z9,z4,z5,z6,z332]),(0,[z286,z958,z2,z9,z4,z6])]],
   [[(0,[z2,z9,z4,z5,z6,z238]),(0,[z46,z2,z443,z4,z5,z6]),(0,[z1,z2,z959,z4,z5,z6]),(0,[z1,z9,z4,z342,z174,z72])],[(0,[z1,z248,z9,z4,z5,z6]),(0,[z286,z1,z168,z9,z4,z6]),(0,[z1,z2,z9,z246,z5,z104])],[(0,[z1,z108,z105,z4,z5,z6]),(0,[z46,z2,z9,z4,z304,z6]),(0,[z1,z2,z9,z4,z5,z960]),(0,[z8,z9,z4,z338,z5,z6]),(0,[z42,z1,z2,z4,z364,z6]),(0,[z1,z2,z911,z4,z5,z6])],[(0,[z1,z9,z4,z5,z162,z12]),(0,[z1,z2,z9,z4,z961,z6]),(0,[z2,z9,z4,z962,z5,z6]),(0,[z1,z2,z963,z4,z5,z6]),(0,[z1,z964,z9,z4,z5,z6]),(0,[z1,z82,z525,z4,z5,z6])],[(0,[z1,z9,z4,z5,z6,z12]),(0,[z400,z2,z9,z4,z5,z6]),(0,[z148,z2,z9,z4,z209,z6]),(0,[z96,z170,z9,z4,z5,z188]),(0,[z457,z965,z2,z4,z5,z6]),(0,[z400,z2,z9,z4,z233,z6])],[(0,[z1,z2,z966,z4,z5,z6]),(0,[z1,z2,z967,z4,z5,z6]),(0,[z241,z9,z4,z5,z6,z12]),(0,[z1,z2,z9,z4,z501,z72]),(0,[z1,z968,z9,z4,z5,z6]),(0,[z1,z404,z28,z4,z5,z6]),(0,[z145,z1,z2,z28,z5,z146])],[(0,[z1,z2,z443,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z969]),(0,[z398,z2,z9,z48,z5,z6]),(0,[z1,z2,z970,z4,z5,z6]),(0,[z1,z971,z9,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z972]),(0,[z973,z1,z9,z4,z5,z6])]],
   [[(0,[z1,z804,z4,z5,z6,z12]),(0,[z2,z197,z172,z4,z5,z6]),(0,[z34,z377,z9,z4,z5,z6]),(0,[z541,z457,z1,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z974])],[(0,[z975,z1,z2,z4,z5,z6]),(0,[z153,z251,z9,z4,z5,z24]),(0,[z1,z8,z9,z4,z5,z452]),(0,[z185,z103,z9,z4,z5,z6]),(0,[z97,z1,z9,z4,z6,z12]),(0,[z97,z1,z2,z173,z4,z6]),(0,[z1,z2,z9,z118,z5,z104])],[(0,[z976,z1,z2,z4,z5,z6]),(0,[z25,z1,z4,z5,z6,z347])],[(0,[z1,z9,z4,z5,z6,z977]),(0,[z96,z2,z315,z4,z5,z6]),(0,[z203,z2,z9,z4,z209,z6]),(0,[z1,z2,z4,z5,z6,z347]),(0,[z40,z1,z4,z62,z110,z6]),(0,[z1,z978,z9,z4,z5,z6])],[(0,[z1,z979,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z980,z6]),(0,[z1,z981,z9,z4,z5,z6]),(0,[z1,z9,z4,z208,z6,z12]),(0,[z185,z2,z4,z5,z6,z347]),(0,[z1,z2,z810,z79,z5,z6]),(0,[z1,z9,z4,z5,z175,z982])],[(0,[z1,z108,z47,z4,z5,z6]),(0,[z1,z8,z131,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z983]),(0,[z1,z80,z4,z227,z5,z6]),(0,[z9,z4,z984,z5,z6,z12]),(0,[z145,z400,z2,z9,z5,z146])],[(0,[z25,z1,z184,z4,z5,z6])],[(0,[z1,z170,z9,z4,z5,z6]),(0,[z56,z230,z9,z4,z5,z6]),(0,[z2,z131,z4,z5,z24,z6]),(0,[z1,z2,z985,z4,z5,z6]),(0,[z1,z9,z4,z638,z110,z6]),(0,[z8,z9,z172,z4,z5,z6])]],
   [[(0,[z27,z2,z9,z4,z5,z6]),(0,[z2,z9,z48,z5,z6,z303]),(0,[z579,z2,z9,z4,z5,z188]),(0,[z2,z4,z338,z227,z5,z6]),(0,[z205,z1,z9,z4,z379,z6]),(0,[z42,z241,z2,z4,z364,z6]),(0,[z1,z9,z4,z986,z5,z6]),(0,[z1,z106,z4,z5,z151,z419]),(0,[z987,z2,z9,z4,z5,z6])],[(0,[z1,z988,z131,z4,z5,z6]),(0,[z1,z2,z9,z290,z5,z6]),(0,[z1,z2,z4,z5,z989,z6]),(0,[z1,z9,z613,z4,z77,z6]),(0,[z1,z9,z4,z5,z990,z6]),(0,[z147,z8,z9,z4,z5,z6])],[(0,[z1,z2,z4,z5,z991,z6]),(0,[z1,z9,z750,z75,z5,z6]),(0,[z1,z2,z992,z4,z5,z6]),(0,[z1,z8,z106,z4,z5,z151])],[(0,[z96,z2,z131,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z993]),(0,[z1,z2,z994,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z714]),(0,[z11,z1,z248,z4,z5,z6]),(0,[z156,z8,z9,z4,z5,z6]),(0,[z34,z2,z9,z4,z5,z99])],[(0,[z1,z2,z9,z995,z5,z6]),(0,[z1,z2,z642,z4,z43,z6]),(0,[z549,z2,z9,z48,z5,z6]),(0,[z2,z9,z4,z5,z6,z996]),(0,[z322,z2,z9,z4,z208,z6]),(0,[z1,z2,z9,z4,z233,z104])],[(0,[z1,z997,z9,z4,z5,z6]),(0,[z390,z2,z9,z48,z5,z6]),(0,[z132,z8,z9,z48,z5,z6]),(0,[z1,z2,z9,z4,z998,z5]),(0,[z42,z2,z172,z4,z5,z6]),(0,[z999,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z1000]),(0,[z2,z891,z105,z4,z5,z6]),(0,[z1001,z1,z2,z9,z4,z6]),(0,[z1,z2,z316,z4,z304,z6]),(0,[z1,z9,z4,z5,z12,z320]),(0,[z1,z9,z1002,z4,z5,z6]),(0,[z1003,z1,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z1004,z6]),(0,[z1,z2,z9,z4,z1005,z6]),(0,[z73,z97,z1,z2,z79,z6]),(0,[z1,z389,z55,z4,z5,z6])]],
   [[(0,[z21,z1,z105,z4,z5,z6]),(0,[z1,z2,z1006,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z749]),(0,[z2,z9,z1007,z4,z5,z6]),(0,[z166,z8,z9,z4,z5,z6])],[(0,[z1,z2,z1008,z4,z5,z6]),(0,[z1,z2,z315,z4,z5,z6]),(0,[z1,z1009,z9,z4,z5,z6]),(0,[z1,z2,z316,z459,z5,z6]),(0,[z1,z76,z9,z4,z776,z6]),(0,[z1,z9,z4,z5,z714,z12]),(0,[z27,z9,z4,z5,z6,z12]),(0,[z190,z1,z13,z4,z5,z6]),(0,[z1,z2,z89,z5,z6,z403]),(0,[z1,z2,z9,z4,z5,z1010]),(0,[z1011,z1,z2,z4,z5,z6])],[(0,[z1,z1012,z9,z4,z5,z6]),(0,[z11,z185,z9,z4,z5,z6]),(0,[z346,z2,z9,z4,z5,z175]),(0,[z541,z1,z4,z5,z6,z176]),(0,[z457,z16,z1,z2,z4,z6]),(0,[z1,z1013,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z1014,z6])],[(0,[z1,z2,z9,z4,z1015,z6]),(0,[z322,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z175]),(0,[z1,z434,z29,z4,z5,z6])],[(0,[z1016,z2,z9,z4,z5,z6]),(0,[z2,z9,z4,z5,z6,z1017]),(0,[z11,z1,z4,z5,z6,z353]),(0,[z34,z9,z4,z5,z6,z12]),(0,[z1,z1018,z9,z4,z5,z6]),(0,[z1,z2,z197,z495,z5,z6]),(0,[z1,z2,z9,z5,z104,z715])],[(0,[z1019,z1,z2,z9,z4,z6]),(0,[z1,z2,z9,z4,z1020,z6]),(0,[z1,z7,z80,z4,z5,z6]),(0,[z1,z2,z9,z810,z5,z6]),(0,[z1,z2,z9,z4,z1021,z6]),(0,[z1,z1022,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z175,z181]),(0,[z1,z2,z9,z324,z67,z6])],[(0,[z2,z9,z4,z5,z6,z332]),(0,[z199,z1,z9,z4,z5,z12]),(0,[z1023,z2,z9,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z943]),(0,[z1,z2,z217,z4,z5,z175]),(0,[z16,z1,z9,z54,z389,z4])],[(0,[z1,z2,z236,z4,z5,z6]),(0,[z148,z2,z9,z4,z219,z6]),(0,[z1,z316,z4,z5,z6,z12]),(0,[z96,z8,z9,z4,z5,z188]),(0,[z1,z2,z9,z4,z1024,z6]),(0,[z1,z9,z4,z1025,z5,z6]),(0,[z346,z2,z173,z4,z5,z6])]],
   [[(0,[z1,z8,z9,z4,z5,z282]),(0,[z1,z8,z9,z4,z5,z12]),(0,[z1026,z1,z4,z5,z6,z12]),(0,[z63,z9,z4,z5,z6,z12]),(0,[z1,z8,z173,z4,z5,z6]),(0,[z1,z2,z197,z89,z5,z6]),(0,[z1027,z2,z9,z4,z5,z6]),(0,[z1,z4,z5,z6,z176,z277])],[(0,[z17,z9,z4,z5,z6,z238]),(0,[z1,z2,z1028,z4,z5,z6]),(0,[z0,z794,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1029]),(0,[z1,z2,z9,z4,z1030,z5]),(0,[z1,z2,z1031,z4,z5,z6]),(0,[z185,z8,z9,z4,z5,z12]),(0,[z847,z9,z4,z5,z6,z12]),(0,[z8,z9,z4,z1032,z5,z6]),(0,[z42,z1,z8,z4,z364,z6]),(0,[z203,z8,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1033]),(0,[z145,z1,z2,z9,z5,z146]),(0,[z145,z1,z2,z9,z233,z146])],[(0,[z1,z2,z316,z4,z209,z6]),(0,[z851,z9,z4,z5,z6,z12]),(0,[z42,z1,z2,z9,z4,z175]),(0,[z1,z2,z106,z4,z5,z943]),(0,[z1,z2,z1034,z4,z5,z6])],[(0,[z21,z1,z47,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1035]),(0,[z1,z2,z9,z4,z1036,z6]),(0,[z1,z8,z9,z4,z208,z6]),(0,[z1,z1037,z9,z4,z5,z6]),(0,[z2,z9,z4,z5,z6,z1038])],[(0,[z1039,z1,z2,z4,z5,z6]),(0,[z96,z2,z9,z4,z5,z293]),(0,[z2,z9,z4,z1040,z5,z6]),(0,[z8,z9,z4,z5,z6,z238]),(0,[z1,z4,z5,z6,z347,z12]),(0,[z1041,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z1042,z6])],[(0,[z1,z170,z9,z290,z5,z6]),(0,[z1,z2,z1043,z4,z5,z6]),(0,[z185,z4,z5,z6,z347,z12]),(0,[z1,z8,z44,z4,z43,z6]),(0,[z16,z241,z2,z9,z4,z6])],[(0,[z25,z1,z528,z4,z5,z6]),(0,[z83,z9,z4,z48,z5,z6]),(0,[z390,z1,z2,z79,z5,z6]),(0,[z212,z2,z105,z4,z5,z6]),(0,[z1,z9,z4,z242,z5,z12]),(0,[z1,z1044,z4,z5,z6,z12])],[]],
   [[(0,[z1,z779,z4,z5,z6,z12]),(0,[z1045,z1,z4,z5,z6,z12]),(0,[z1,z2,z44,z173,z4,z6]),(0,[z1,z4,z5,z1046,z174,z6])],[(0,[z1,z2,z9,z4,z1047,z6]),(0,[z346,z2,z9,z4,z5,z6]),(0,[z1,z2,z1048,z4,z5,z6]),(0,[z1,z1049,z9,z4,z5,z6]),(0,[z2,z258,z4,z338,z5,z6]),(0,[z1,z8,z4,z227,z5,z6]),(0,[z241,z2,z9,z4,z6,z72]),(0,[z1,z377,z173,z4,z5,z6])],[(0,[z1,z8,z9,z4,z5,z6]),(0,[z366,z2,z9,z4,z5,z6]),(0,[z1,z2,z1050,z4,z5,z6]),(0,[z1,z9,z250,z4,z5,z12]),(0,[z1,z8,z9,z4,z233,z6]),(0,[z1,z1051,z9,z4,z5,z6])],[(0,[z1052,z2,z9,z4,z5,z6]),(0,[z185,z8,z9,z4,z5,z6]),(0,[z285,z1,z4,z5,z12,z123]),(0,[z882,z9,z4,z5,z6,z12]),(0,[z1053,z1,z9,z4,z5,z6]),(0,[z241,z8,z9,z4,z5,z6]),(0,[z21,z1,z9,z4,z380,z6]),(0,[z33,z1,z9,z6,z277,z181]),(0,[z2,z9,z4,z5,z6,z1054])],[(0,[z17,z595,z9,z4,z5,z6]),(0,[z1,z2,z891,z4,z5,z6]),(0,[z1,z1055,z9,z4,z5,z6]),(0,[z286,z25,z1,z2,z4,z6]),(0,[z1,z2,z525,z4,z5,z6]),(0,[z1,z2,z1056,z4,z5,z6]),(0,[z1,z2,z525,z4,z233,z6]),(0,[z203,z2,z1057,z4,z5,z6])],[(0,[z1,z2,z9,z1058,z5,z6]),(0,[z1,z2,z1059,z4,z5,z6]),(0,[z153,z9,z4,z5,z24,z164]),(0,[z2,z1060,z9,z4,z5,z6]),(0,[z1,z2,z4,z1061,z5,z6]),(0,[z466,z1,z2,z4,z5,z123]),(0,[z1,z2,z1062,z4,z5,z6]),(0,[z16,z235,z2,z9,z54,z4])],[(0,[z1,z9,z4,z1063,z5,z6]),(0,[z1,z988,z9,z4,z5,z6]),(0,[z1064,z2,z9,z4,z5,z6]),(0,[z9,z1007,z4,z5,z6,z12]),(0,[z1065,z1,z2,z4,z5,z6])],[(0,[z1,z2,z9,z1066,z4,z5]),(0,[z148,z2,z50,z4,z5,z6]),(0,[z16,z1,z2,z9,z250,z4]),(0,[z1,z8,z9,z4,z5,z714]),(0,[z42,z1,z2,z617,z4,z6]),(0,[z1,z44,z4,z43,z447,z6]),(0,[z1,z436,z217,z4,z5,z6]),(0,[z145,z322,z2,z9,z5,z146])]],
   [[(0,[z794,z2,z9,z4,z5,z6]),(0,[z1,z1067,z9,z4,z5,z6]),(0,[z1,z230,z316,z4,z5,z6]),(0,[z1,z2,z1068,z4,z5,z6]),(0,[z1069,z2,z9,z4,z5,z6]),(0,[z156,z9,z4,z5,z6,z12]),(0,[z286,z1,z2,z4,z6,z123]),(0,[z1070,z9,z172,z4,z5,z6]),(0,[z33,z1,z2,z9,z175,z181]),(0,[z1,z404,z9,z4,z208,z6])],[(0,[z2,z9,z396,z48,z5,z6]),(0,[z1,z9,z4,z1071,z5,z6]),(0,[z1,z4,z240,z227,z5,z6]),(0,[z1,z9,z389,z4,z5,z6]),(0,[z1,z2,z9,z4,z1072,z6]),(0,[z1,z9,z4,z5,z1073,z6])],[(0,[z1026,z1,z2,z4,z5,z6]),(0,[z1,z80,z236,z4,z5,z6]),(0,[z88,z56,z9,z4,z5,z6]),(0,[z1074,z1,z2,z9,z4,z6]),(0,[z1,z1075,z9,z4,z5,z6]),(0,[z241,z7,z2,z4,z5,z6]),(0,[z40,z1,z9,z4,z488,z6])],[(0,[z1,z2,z9,z1076,z5,z6]),(0,[z1077,z2,z9,z4,z5,z6]),(0,[z1,z80,z784,z4,z5,z6]),(0,[z1,z377,z9,z4,z5,z6]),(0,[z1,z76,z9,z4,z354,z6]),(0,[z366,z9,z4,z5,z6,z12]),(0,[z145,z1,z9,z5,z12,z146]),(0,[z1,z1078,z9,z4,z5,z6]),(0,[z33,z541,z1,z9,z6,z181]),(0,[z1,z2,z4,z5,z1046,z6])],[(0,[z1,z2,z9,z4,z1079,z5]),(0,[z1,z440,z9,z4,z5,z6]),(0,[z25,z1,z696,z4,z5,z6]),(0,[z1,z4,z227,z5,z6,z12]),(0,[z1080,z2,z9,z4,z5,z6]),(0,[z97,z1,z2,z4,z6,z123]),(0,[z1081,z1,z9,z4,z5,z6])],[(0,[z56,z9,z4,z5,z6,z164]),(0,[z36,z2,z131,z4,z5,z6]),(0,[z145,z1,z404,z9,z5,z146])],[(0,[z2,z316,z105,z4,z5,z6]),(0,[z2,z47,z891,z4,z5,z6]),(0,[z1,z2,z1082,z4,z5,z6]),(0,[z1,z2,z1083,z4,z5,z6]),(0,[z1084,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z5,z1085]),(0,[z1,z2,z1086,z4,z5,z6]),(0,[z202,z280,z9,z4,z5,z6]),(0,[z2,z9,z1087,z4,z5,z6]),(0,[z1,z2,z9,z67,z6,z745])]],
   [[(0,[z1,z2,z9,z1088,z5,z6]),(0,[z1,z2,z9,z4,z5,z1089]),(0,[z244,z2,z9,z4,z49,z6]),(0,[z46,z47,z4,z5,z6,z12]),(0,[z97,z1,z2,z106,z4,z6])],[(0,[z1,z9,z1090,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z327]),(0,[z1,z9,z45,z67,z6,z12]),(0,[z1091,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z99,z1092])],[(0,[z1,z9,z4,z304,z6,z12]),(0,[z1045,z1,z2,z4,z5,z6]),(0,[z97,z21,z1,z9,z4,z6]),(0,[z1,z9,z4,z5,z6,z1093])],[(0,[z1094,z1,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z1095]),(0,[z1,z4,z708,z5,z6,z12]),(0,[z1,z1096,z9,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z949]),(0,[z1,z2,z9,z4,z6,z1097]),(0,[z1,z2,z4,z43,z604,z6]),(0,[z1,z2,z1044,z4,z5,z6]),(0,[z1,z2,z9,z5,z6,z764]),(0,[z1,z9,z301,z4,z5,z12]),(0,[z11,z1,z4,z5,z6,z439]),(0,[z1098,z2,z9,z4,z5,z6]),(0,[z33,z1,z2,z173,z6,z181]),(0,[z1,z2,z9,z4,z72,z413])],[(0,[z1,z9,z4,z5,z6,z277]),(0,[z1,z4,z5,z6,z12,z176]),(0,[z1,z2,z757,z4,z5,z6]),(0,[z73,z366,z2,z79,z5,z6])],[(0,[z1,z9,z1099,z4,z5,z6]),(0,[z40,z1,z9,z4,z776,z6]),(0,[z1100,z1,z4,z5,z6,z12]),(0,[z1,z365,z423,z4,z5,z6]),(0,[z285,z1,z440,z4,z5,z123])],[(0,[z1,z2,z9,z4,z1101,z6]),(0,[z1102,z1,z2,z4,z5,z6]),(0,[z1,z4,z5,z62,z447,z6]),(0,[z1,z2,z4,z1103,z5,z6]),(0,[z1,z8,z4,z5,z347,z12]),(0,[z2,z4,z5,z6,z238,z347]),(0,[z27,z8,z9,z4,z5,z6]),(1,[z1,z2,z4,z5,z943])]],
   [[(0,[z1,z93,z9,z4,z5,z12]),(0,[z100,z2,z891,z4,z5,z6]),(0,[z25,z1,z584,z4,z5,z6]),(0,[z1,z8,z9,z290,z5,z6]),(0,[z9,z4,z5,z6,z238,z164]),(0,[z39,z1,z9,z297,z5,z6]),(0,[z1,z9,z4,z5,z99,z12]),(0,[z145,z1,z8,z9,z5,z146]),(0,[z2,z9,z4,z1032,z5,z6]),(0,[z1,z1104,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z5,z1105]),(0,[z1,z9,z4,z5,z6,z1092]),(0,[z400,z404,z9,z4,z5,z6]),(0,[z1,z1106,z9,z4,z5,z6])],[(0,[z83,z1,z4,z43,z5,z6]),(0,[z1,z2,z9,z1107,z5,z6]),(0,[z1,z2,z4,z766,z5,z6]),(0,[z33,z457,z1,z2,z4,z6]),(0,[z1,z2,z9,z4,z302,z72])],[(0,[z132,z2,z9,z290,z5,z6])],[(0,[z1,z8,z9,z4,z5,z214]),(0,[z17,z2,z9,z290,z5,z6]),(0,[z2,z105,z4,z237,z5,z6]),(0,[z96,z2,z9,z459,z5,z188]),(0,[z243,z1,z9,z75,z5,z6]),(0,[z1,z4,z5,z6,z12,z733]),(0,[z1,z2,z9,z4,z1108,z6]),(0,[z1109,z2,z9,z4,z5,z6]),(0,[z1,z1110,z9,z4,z5,z6]),(0,[z1,z1111,z9,z4,z5,z6])],[(0,[z1,z9,z4,z5,z6,z1112]),(0,[z1113,z2,z29,z4,z5,z6])],[(0,[z0,z9,z4,z5,z6,z238]),(0,[z1,z9,z4,z5,z1114,z6]),(0,[z457,z1,z2,z4,z5,z6]),(0,[z1,z2,z44,z9,z4,z175]),(0,[z34,z2,z217,z4,z5,z6]),(0,[z1,z9,z4,z1115,z5,z6])],[(0,[z1,z2,z1116,z4,z5,z6]),(0,[z2,z131,z4,z48,z5,z6]),(0,[z1117,z2,z9,z4,z5,z6]),(0,[z63,z8,z9,z4,z5,z6]),(0,[z1,z2,z4,z5,z151,z943])],[(0,[z1,z2,z1118,z4,z5,z6]),(0,[z0,z11,z1,z4,z5,z6]),(0,[z1,z2,z1119,z4,z5,z6]),(0,[z40,z1,z9,z4,z110,z6]),(0,[z1120,z2,z9,z4,z5,z6]),(0,[z1,z1121,z9,z4,z5,z6])]],
   [[(0,[z1,z8,z315,z4,z5,z6]),(0,[z1122,z2,z9,z4,z5,z6]),(0,[z1,z7,z423,z4,z5,z6]),(0,[z185,z9,z4,z5,z6,z12]),(0,[z8,z9,z4,z5,z238,z12]),(0,[z286,z1,z9,z4,z6,z12]),(0,[z1,z2,z9,z4,z5,z1123]),(0,[z1,z2,z9,z4,z342,z72])],[(0,[z132,z2,z18,z48,z5,z6]),(0,[z579,z1,z9,z4,z5,z12]),(0,[z97,z1,z2,z4,z364,z6]),(0,[z1,z2,z197,z810,z5,z6]),(0,[z1,z4,z5,z6,z1124,z165])],[(0,[z1,z2,z1125,z4,z5,z6]),(0,[z11,z1,z4,z5,z6,z347]),(0,[z201,z1,z9,z5,z6,z288]),(0,[z322,z8,z9,z4,z5,z6]),(0,[z1,z1126,z9,z4,z5,z6])],[(0,[z1,z1127,z9,z4,z5,z6]),(0,[z1,z1128,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z304,z6]),(0,[z1,z2,z1129,z4,z5,z6]),(0,[z1,z9,z4,z6,z387,z12]),(0,[z1,z2,z9,z4,z428,z72]),(0,[z1,z2,z1130,z4,z5,z6])],[(0,[z96,z2,z9,z4,z209,z188]),(0,[z2,z9,z4,z5,z6,z1131]),(0,[z73,z1,z2,z380,z79,z6]),(0,[z1,z1132,z9,z4,z5,z6])],[(0,[z1,z2,z1133,z4,z5,z6]),(0,[z1,z2,z1134,z4,z5,z6]),(0,[z96,z2,z9,z4,z5,z749]),(0,[z1,z9,z4,z5,z12,z468]),(0,[z1,z434,z9,z4,z5,z6]),(0,[z1,z197,z89,z5,z6,z12]),(0,[z88,z32,z9,z4,z5,z6]),(0,[z1065,z1,z8,z4,z5,z6]),(0,[z1135,z2,z9,z4,z5,z6]),(0,[z1,z1136,z9,z4,z5,z6])],[(0,[z17,z630,z9,z4,z5,z6]),(0,[z1,z8,z236,z4,z5,z6]),(0,[z1,z2,z9,z459,z5,z6]),(0,[z25,z166,z9,z4,z5,z6]),(0,[z872,z8,z9,z4,z5,z6]),(0,[z33,z457,z1,z2,z6,z181]),(0,[z1,z29,z389,z4,z5,z6])],[(0,[z1,z2,z9,z4,z1137,z6]),(0,[z148,z2,z9,z4,z71,z6]),(0,[z1,z9,z4,z155,z5,z12]),(0,[z1,z258,z4,z5,z6,z12])]],
   [[(0,[z46,z2,z47,z4,z5,z6]),(0,[z1,z1138,z9,z4,z5,z6]),(0,[z1,z8,z258,z4,z5,z6]),(0,[z1100,z1,z2,z4,z5,z6]),(0,[z400,z9,z4,z5,z6,z12]),(0,[z9,z4,z5,z6,z996,z12]),(0,[z877,z8,z9,z4,z5,z6]),(0,[z1,z9,z1139,z4,z5,z6]),(0,[z1,z2,z4,z5,z943,z123]),(0,[z1,z2,z9,z4,z233,z146])],[(0,[z1140,z1,z9,z4,z5,z6]),(0,[z1,z1141,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1142]),(0,[z8,z1060,z9,z4,z5,z6]),(0,[z958,z2,z9,z4,z5,z6]),(0,[z33,z1,z436,z9,z6,z181])],[(0,[z1,z2,z1143,z4,z5,z6]),(0,[z185,z80,z9,z4,z5,z6]),(0,[z1144,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z163,z5,z12]),(0,[z1145,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z1146,z6]),(0,[z2,z315,z4,z5,z24,z6]),(0,[z1,z157,z9,z4,z5,z6]),(0,[z185,z9,z4,z5,z6,z127]),(0,[z1147,z2,z9,z4,z5,z6]),(0,[z1,z1148,z9,z4,z5,z6]),(0,[z965,z2,z9,z4,z5,z6])],[(0,[z1,z2,z1149,z4,z5,z6]),(0,[z1,z8,z9,z45,z67,z6]),(0,[z2,z9,z4,z5,z6,z1150]),(0,[z1,z2,z9,z4,z6,z1151]),(0,[z1,z1152,z9,z4,z5,z6]),(0,[z1070,z1,z9,z4,z5,z6]),(0,[z1,z2,z1153,z4,z5,z6]),(0,[z16,z1,z2,z9,z727,z4]),(0,[z1,z434,z55,z4,z5,z6])],[(0,[z1,z2,z9,z4,z1154,z6]),(0,[z1,z2,z9,z4,z5,z1155]),(0,[z713,z2,z9,z4,z5,z6]),(0,[z169,z1,z9,z297,z5,z6]),(0,[z2,z172,z4,z43,z5,z6]),(0,[z1,z2,z1156,z4,z5,z6])],[(0,[z1,z1157,z9,z4,z5,z6]),(0,[z203,z2,z9,z4,z71,z6]),(0,[z1,z8,z9,z4,z5,z268]),(0,[z366,z2,z197,z4,z5,z6]),(0,[z1,z1158,z9,z4,z5,z6]),(0,[z1159,z1,z2,z4,z5,z6])],[(0,[z1,z2,z9,z4,z209,z6]),(0,[z51,z2,z9,z4,z49,z6]),(0,[z1,z9,z4,z342,z72,z12]),(0,[z1160,z2,z9,z4,z5,z6]),(0,[z322,z404,z9,z4,z5,z6])]],
   [[(0,[z25,z1,z13,z4,z5,z6]),(0,[z1161,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z828,z6]),(0,[z97,z1,z9,z4,z240,z6]),(0,[z705,z1,z2,z79,z5,z6])],[(0,[z147,z2,z9,z48,z5,z6]),(0,[z905,z8,z9,z4,z5,z6]),(0,[z366,z8,z9,z4,z5,z6]),(0,[z97,z1162,z2,z9,z4,z6]),(0,[z1163,z1,z2,z9,z4,z6])],[(0,[z96,z230,z9,z4,z5,z188]),(0,[z1,z8,z9,z4,z5,z677]),(0,[z1,z60,z9,z111,z5,z6]),(0,[z1,z9,z4,z233,z6,z12]),(0,[z73,z156,z2,z79,z5,z6]),(0,[z1164,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1165]),(0,[z1159,z1,z4,z5,z6,z165])],[(0,[z1,z103,z4,z5,z6,z347]),(0,[z16,z1,z2,z9,z4,z484]),(0,[z560,z42,z1,z2,z4,z6])],[(0,[z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z9,z6,z745,z181]),(0,[z1,z2,z1166,z4,z5,z6]),(0,[z1167,z2,z9,z4,z5,z6])],[(0,[z1,z9,z4,z5,z6,z165]),(0,[z1,z9,z4,z5,z1168,z6]),(0,[z1,z2,z9,z45,z685,z6]),(0,[z1,z2,z9,z45,z6,z745]),(0,[z145,z1,z2,z9,z208,z146])],[(0,[z1,z2,z18,z4,z5,z6]),(0,[z27,z2,z443,z4,z5,z6])],[(0,[z100,z2,z105,z4,z5,z6]),(0,[z83,z1,z4,z79,z5,z6]),(0,[z1,z2,z1169,z4,z5,z6]),(0,[z1,z170,z9,z4,z304,z6]),(0,[z25,z1,z637,z4,z5,z6]),(0,[z741,z2,z9,z4,z5,z6]),(0,[z1,z76,z9,z4,z655,z6]),(0,[z1,z1170,z9,z4,z5,z6]),(0,[z1,z9,z4,z240,z380,z6])]],
   [[(0,[z574,z2,z105,z4,z5,z6]),(0,[z153,z8,z9,z4,z5,z24]),(0,[z1,z9,z4,z5,z174,z6]),(0,[z42,z1,z4,z364,z6,z12]),(0,[z1,z8,z9,z4,z6,z387]),(0,[z1171,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z67,z175]),(0,[z1172,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z290,z304,z6]),(0,[z1,z9,z4,z5,z6,z1173]),(0,[z1,z80,z4,z5,z6,z347]),(0,[z1174,z2,z9,z4,z5,z6]),(0,[z97,z1175,z2,z9,z4,z6]),(0,[z1176,z2,z9,z4,z5,z6]),(0,[z346,z377,z9,z4,z5,z6]),(0,[z1,z157,z9,z118,z5,z104])],[(0,[z83,z100,z105,z4,z5,z6]),(0,[z96,z83,z9,z4,z5,z6]),(0,[z1,z2,z1177,z4,z5,z6]),(0,[z1,z2,z1178,z4,z5,z6]),(0,[z1,z170,z9,z459,z5,z6]),(0,[z1,z2,z197,z194,z5,z6]),(0,[z1175,z2,z9,z4,z5,z6])],[(0,[z1,z1179,z9,z4,z5,z6]),(0,[z1180,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1181]),(0,[z1,z9,z4,z5,z1182,z6]),(0,[z1011,z1,z4,z5,z174,z6])],[(0,[z658,z2,z105,z4,z5,z6]),(0,[z25,z241,z2,z4,z5,z6]),(0,[z11,z1,z7,z4,z5,z6]),(0,[z1,z29,z4,z5,z6,z12]),(0,[z457,z1,z8,z4,z5,z6])],[(0,[z1,z230,z9,z4,z5,z6]),(0,[z57,z2,z9,z4,z49,z6]),(0,[z1,z2,z4,z5,z725,z6])],[(0,[z19,z8,z9,z4,z49,z6]),(0,[z185,z230,z9,z4,z5,z6]),(0,[z1,z231,z9,z4,z5,z12]),(0,[z97,z1,z2,z44,z4,z6]),(0,[z1,z1183,z9,z4,z5,z6]),(0,[z1,z1184,z9,z4,z5,z6]),(0,[z1,z1185,z9,z4,z5,z6])],[(0,[z63,z2,z105,z4,z5,z6]),(0,[z179,z2,z47,z4,z5,z6]),(0,[z322,z9,z4,z5,z6,z12]),(0,[z97,z1,z2,z89,z4,z6]),(0,[z1,z1186,z9,z4,z5,z6])]],
   [[(0,[z1,z2,z9,z870,z5,z6]),(0,[z1,z2,z1187,z4,z5,z6]),(0,[z42,z1,z2,z4,z115,z6]),(0,[z1,z436,z9,z4,z5,z175]),(0,[z1,z404,z525,z4,z5,z6]),(0,[z1,z2,z525,z4,z208,z6])],[(0,[z1,z2,z9,z1188,z5,z6]),(0,[z1189,z1,z2,z9,z4,z5]),(0,[z96,z2,z9,z4,z5,z303]),(0,[z1,z2,z9,z4,z5,z1190]),(0,[z39,z1,z9,z750,z5,z6]),(0,[z1,z9,z4,z5,z112,z12]),(0,[z285,z1,z2,z4,z5,z123])],[(0,[z414,z1,z9,z4,z5,z12]),(0,[z1,z108,z44,z4,z43,z6]),(0,[z1191,z1,z9,z4,z5,z6])],[(0,[z1,z8,z9,z4,z5,z325]),(0,[z1,z170,z9,z4,z209,z6]),(0,[z1,z9,z290,z5,z6,z12]),(0,[z1,z7,z248,z4,z5,z6])],[(0,[z1192,z2,z9,z4,z5,z6]),(0,[z1193,z2,z9,z4,z5,z6]),(0,[z11,z2,z4,z5,z6,z238]),(0,[z1,z1194,z9,z4,z5,z6]),(0,[z346,z2,z9,z4,z5,z99]),(0,[z1,z2,z4,z5,z1195,z6])],[(0,[z148,z2,z315,z4,z71,z6]),(0,[z148,z2,z9,z4,z827,z6]),(0,[z1,z2,z9,z290,z209,z6]),(0,[z1,z8,z9,z4,z5,z99]),(0,[z1,z9,z4,z5,z6,z1196]),(0,[z1,z2,z883,z4,z5,z6]),(0,[z1,z9,z4,z1197,z5,z6]),(0,[z16,z1,z434,z9,z54,z4])],[(0,[z535,z1,z2,z4,z5,z123]),(0,[z1198,z2,z9,z4,z5,z6]),(0,[z1199,z1,z9,z4,z5,z6]),(0,[z1,z9,z1200,z4,z5,z6]),(0,[z1,z2,z4,z5,z1201,z6]),(0,[z1202,z2,z9,z4,z5,z6]),(0,[z1,z1203,z9,z4,z5,z6])],[(0,[z1,z2,z4,z1204,z5,z6]),(0,[z1,z108,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1205]),(0,[z1206,z2,z9,z4,z5,z6]),(0,[z1207,z2,z9,z4,z5,z6])]],
   [[(0,[z36,z2,z315,z4,z5,z6]),(0,[z1208,z1,z9,z4,z5,z6]),(0,[z1209,z2,z9,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z450]),(0,[z350,z1,z9,z613,z4,z6]),(0,[z1,z2,z217,z4,z5,z6]),(0,[z1,z1210,z9,z4,z5,z6]),(0,[z1,z2,z217,z4,z5,z99])],[(0,[z1,z2,z9,z4,z1211,z6]),(0,[z42,z1,z2,z4,z144,z6]),(0,[z1212,z2,z9,z4,z5,z6]),(0,[z1213,z2,z9,z4,z5,z6]),(0,[z9,z172,z4,z5,z6,z12]),(0,[z1,z2,z1214,z4,z5,z6]),(0,[z16,z1,z2,z29,z4,z6])],[(0,[z1,z2,z1215,z4,z5,z6]),(0,[z25,z1,z703,z4,z5,z6]),(0,[z1,z956,z4,z5,z6,z12]),(0,[z1,z9,z4,z5,z6,z1216]),(0,[z457,z1,z2,z4,z6,z72]),(0,[z829,z9,z4,z5,z6,z165])],[(0,[z1,z2,z9,z4,z1217,z6]),(0,[z541,z1,z9,z4,z5,z6]),(0,[z2,z172,z4,z79,z5,z6]),(0,[z1218,z2,z9,z4,z5,z6]),(0,[z309,z1,z2,z9,z54,z4]),(0,[z1,z2,z9,z54,z727,z4])],[(0,[z2,z9,z105,z290,z5,z6]),(0,[z1,z1219,z9,z4,z5,z6]),(0,[z40,z84,z1,z4,z110,z6])],[(0,[z56,z794,z9,z4,z5,z6]),(0,[z1,z2,z9,z4,z1220,z6]),(0,[z1,z50,z4,z5,z6,z12]),(0,[z346,z9,z4,z5,z6,z12])],[(0,[z1,z2,z9,z4,z1221,z6]),(0,[z1,z2,z9,z1222,z5,z6]),(0,[z1,z2,z4,z5,z6,z1223]),(0,[z457,z1,z4,z5,z6,z12]),(0,[z400,z8,z9,z4,z5,z6]),(0,[z33,z346,z2,z9,z6,z181]),(0,[z1,z1224,z9,z4,z5,z6]),(0,[z1,z377,z9,z4,z5,z99]),(0,[z760,z2,z9,z4,z5,z6]),(0,[z1113,z2,z9,z4,z5,z6])],[(0,[z1,z2,z1225,z4,z5,z6]),(0,[z96,z2,z50,z4,z5,z188]),(0,[z1,z9,z4,z209,z6,z12]),(0,[z1,z8,z9,z4,z342,z72]),(0,[z286,z1,z2,z106,z4,z6])]],
   [[(0,[z11,z17,z1,z4,z5,z6]),(0,[z1,z236,z4,z5,z6,z12]),(0,[z97,z1,z2,z47,z4,z6]),(0,[z1,z2,z1226,z4,z5,z6]),(0,[z1,z8,z443,z4,z5,z6]),(0,[z96,z2,z316,z4,z5,z188]),(0,[z1,z9,z4,z77,z776,z6]),(0,[z505,z11,z1,z4,z5,z6]),(0,[z97,z1,z2,z9,z4,z6]),(0,[z1227,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1228]),(0,[z400,z2,z525,z4,z5,z6]),(0,[z1,z2,z1057,z4,z5,z6])],[(0,[z1,z2,z571,z4,z5,z123])],[(0,[z1,z8,z9,z4,z304,z6])],[(0,[z1,z230,z9,z290,z5,z6]),(0,[z1,z2,z1229,z4,z5,z6]),(0,[z33,z1,z9,z6,z12,z181]),(0,[z1,z4,z5,z6,z1223,z12]),(0,[z1,z8,z9,z118,z5,z104])],[],[(0,[z46,z2,z316,z4,z5,z6]),(0,[z1,z2,z9,z4,z827,z6]),(0,[z1,z2,z1230,z4,z5,z6]),(0,[z1,z8,z9,z459,z5,z6]),(0,[z1,z8,z4,z5,z6,z347])],[(0,[z1,z1231,z9,z4,z5,z6]),(0,[z148,z8,z9,z4,z71,z6]),(0,[z1232,z2,z9,z4,z5,z6]),(0,[z34,z2,z9,z4,z5,z175])],[(0,[z1,z2,z9,z4,z1233,z6]),(0,[z2,z9,z4,z5,z6,z749]),(0,[z1,z9,z4,z5,z479,z12]),(0,[z1,z173,z4,z5,z6,z12]),(0,[z1234,z2,z9,z4,z5,z6]),(0,[z1235,z2,z9,z4,z5,z6]),(0,[z1,z2,z9,z727,z4,z72])]],
   [[(0,[z1236,z1,z9,z4,z5,z6]),(0,[z1,z1237,z9,z4,z5,z6]),(0,[z1,z1238,z9,z4,z5,z6]),(0,[z1,z784,z184,z4,z5,z6]),(0,[z826,z2,z9,z4,z5,z6]),(0,[z1080,z9,z4,z5,z6,z12]),(0,[z1239,z2,z9,z4,z5,z6]),(0,[z1,z1240,z9,z4,z5,z6])],[(0,[z19,z9,z4,z49,z6,z12]),(0,[z235,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z638,z6,z353]),(0,[z42,z1,z2,z4,z725,z6]),(0,[z1,z1241,z9,z4,z5,z6])],[(0,[z1,z226,z9,z4,z5,z6]),(0,[z1242,z1,z2,z4,z5,z6]),(0,[z1,z2,z50,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z1243]),(0,[z1,z2,z9,z4,z1244,z6]),(0,[z1,z2,z9,z1245,z5,z6])],[(0,[z1,z2,z1246,z4,z5,z6]),(0,[z2,z891,z9,z4,z5,z6]),(0,[z1247,z1,z9,z5,z6,z12])],[(0,[z1,z7,z226,z4,z5,z6]),(0,[z1,z8,z9,z4,z5,z204]),(0,[z1,z2,z1248,z4,z5,z6]),(0,[z16,z203,z2,z9,z54,z4])],[(0,[z1,z2,z9,z4,z5,z1249]),(0,[z21,z1,z9,z4,z5,z6]),(0,[z1,z4,z5,z62,z6,z12]),(0,[z1,z171,z9,z4,z354,z6]),(0,[z1250,z2,z9,z4,z5,z6]),(0,[z1,z1251,z9,z4,z5,z6]),(0,[z1,z2,z1252,z4,z5,z6])],[(0,[z185,z192,z9,z4,z5,z6]),(0,[z0,z56,z3,z4,z5,z6]),(0,[z1,z8,z9,z4,z209,z6]),(0,[z1,z1253,z9,z4,z5,z6]),(0,[z1,z2,z29,z4,z5,z6]),(0,[z1,z858,z9,z4,z5,z175]),(0,[z1,z2,z28,z4,z233,z6])],[(0,[z1,z2,z4,z1254,z5,z6]),(0,[z1,z18,z4,z5,z6,z12]),(0,[z1,z2,z1255,z4,z5,z6]),(0,[z1,z9,z4,z5,z6,z982]),(0,[z1,z2,z9,z4,z5,z943]),(0,[z1256,z2,z9,z4,z5,z6]),(0,[z1,z9,z4,z5,z1257,z6])]],
   [[(0,[z1,z794,z9,z4,z5,z6]),(0,[z1,z2,z9,z1258,z5,z6]),(0,[z1247,z1,z2,z9,z5,z6]),(0,[z285,z1,z8,z4,z5,z123])],[(0,[z2,z9,z290,z5,z6,z188]),(0,[z25,z1,z4,z5,z62,z6]),(0,[z1,z2,z9,z4,z777,z6]),(0,[z1,z9,z4,z5,z175,z12]),(0,[z1,z9,z4,z5,z6,z1259])],[(0,[z1,z2,z4,z5,z62,z6]),(0,[z1,z9,z4,z5,z129,z12]),(0,[z1,z2,z950,z4,z5,z6]),(0,[z1,z2,z9,z4,z620,z72]),(1,[z1,z2,z9,z727,z4])],[(0,[z1,z9,z4,z5,z6,z164]),(0,[z514,z2,z105,z4,z5,z6]),(0,[z1,z1260,z9,z4,z5,z6]),(0,[z2,z9,z4,z5,z24,z749]),(0,[z457,z1,z2,z45,z4,z6]),(0,[z16,z1,z2,z9,z54,z4])],[(0,[z2,z9,z635,z4,z5,z24]),(0,[z1,z2,z106,z4,z5,z698]),(0,[z1,z1261,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z1262,z6]),(0,[z1,z8,z18,z4,z5,z6]),(0,[z1,z7,z4,z5,z6,z419]),(0,[z1263,z2,z9,z4,z5,z6])],[(0,[z279,z2,z105,z4,z5,z6]),(0,[z1,z9,z4,z5,z12,z594]),(0,[z2,z9,z117,z5,z6,z578]),(0,[z1208,z1,z315,z4,z5,z6]),(0,[z135,z11,z1,z4,z5,z12]),(0,[z1,z2,z9,z727,z4,z342])],[(0,[z1264,z1,z9,z4,z5,z6]),(0,[z1,z1265,z9,z4,z5,z6]),(0,[z1,z1266,z9,z4,z5,z6]),(0,[z73,z97,z1,z2,z4,z6]),(0,[z42,z1,z2,z339,z4,z6]),(0,[z1267,z2,z9,z4,z5,z6]),(0,[z34,z436,z9,z4,z5,z6]),(0,[z322,z2,z525,z4,z5,z6]),(0,[z1,z82,z9,z4,z233,z6])]],
   [[(0,[z83,z1,z9,z4,z5,z6]),(0,[z1268,z2,z9,z4,z5,z6]),(0,[z25,z1,z248,z4,z5,z6]),(0,[z1269,z1,z9,z4,z5,z6]),(0,[z1270,z2,z9,z4,z5,z6]),(0,[z1,z2,z4,z43,z6,z636]),(0,[z1,z2,z4,z5,z6,z1124]),(0,[z2,z9,z748,z4,z5,z6])],[(0,[z11,z1,z184,z4,z5,z6]),(0,[z1,z2,z44,z4,z523,z6])],[(0,[z1,z1271,z9,z4,z5,z6]),(0,[z1,z4,z5,z6,z347,z419]),(0,[z1,z8,z197,z89,z5,z6]),(0,[z286,z1239,z2,z9,z4,z6]),(0,[z16,z1,z2,z9,z255,z4])],[(0,[z1,z2,z1272,z4,z5,z6]),(1,[z2,z9,z4,z827,z6]),(0,[z1,z2,z221,z79,z5,z6]),(0,[z286,z1,z8,z9,z4,z6]),(0,[z42,z27,z2,z4,z364,z6])],[(0,[z579,z1,z2,z9,z5,z146]),(0,[z73,z1,z2,z79,z5,z6]),(0,[z1273,z2,z9,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1274]),(0,[z1,z2,z9,z1275,z5,z6]),(0,[z1,z113,z9,z4,z5,z6]),(0,[z1162,z2,z9,z4,z5,z6])],[(0,[z1,z2,z9,z4,z1276,z6]),(0,[z1,z2,z9,z1277,z5,z6]),(0,[z1,z170,z50,z4,z5,z6]),(0,[z1,z7,z4,z5,z447,z6]),(0,[z1,z2,z4,z43,z725,z6]),(0,[z1,z918,z9,z4,z5,z6]),(0,[z1,z168,z106,z4,z5,z151]),(0,[z1,z9,z4,z5,z6,z1278])],[(0,[z0,z56,z9,z4,z5,z6]),(0,[z2,z50,z4,z5,z49,z6]),(0,[z97,z1,z8,z9,z4,z6]),(0,[z241,z2,z106,z4,z5,z6]),(0,[z1,z2,z106,z4,z5,z484])]],
   [[(0,[z1,z2,z9,z4,z427,z72]),(0,[z1,z2,z50,z290,z5,z6]),(0,[z366,z2,z4,z43,z5,z6]),(0,[z1,z1279,z9,z4,z5,z6]),(0,[z145,z1,z82,z9,z5,z146])],[(0,[z1,z1280,z9,z4,z5,z6]),(0,[z2,z9,z4,z209,z49,z6]),(0,[z1,z2,z788,z4,z5,z6]),(0,[z73,z21,z1,z79,z5,z6])],[(0,[z2,z9,z870,z48,z5,z6]),(0,[z1,z2,z1281,z4,z5,z6]),(0,[z1,z4,z5,z6,z1282,z164]),(0,[z1,z2,z4,z5,z6,z1282]),(0,[z11,z1,z613,z4,z5,z6])],[(0,[z1,z2,z1283,z4,z5,z6]),(0,[z19,z2,z9,z4,z827,z6]),(0,[z2,z9,z4,z5,z6,z785]),(0,[z346,z8,z9,z4,z5,z6])],[(0,[z1,z2,z9,z1284,z5,z6]),(0,[z1,z9,z784,z4,z5,z6]),(0,[z1285,z2,z9,z4,z5,z6])],[(0,[z148,z2,z443,z4,z71,z6]),(0,[z1,z2,z1286,z4,z5,z6]),(0,[z1,z8,z4,z5,z1201,z6]),(1,[z1,z2,z4,z725,z6]),(0,[z1,z9,z4,z5,z6,z1287])],[(1,[z794,z9,z4,z5,z6]),(0,[z1,z2,z9,z459,z304,z6]),(0,[z1,z8,z525,z4,z5,z6]),(0,[z2,z9,z4,z5,z6,z1288]),(0,[z346,z2,z217,z4,z5,z6])],[(0,[z1,z2,z1289,z4,z5,z6]),(0,[z1,z2,z1290,z4,z5,z6]),(0,[z63,z2,z316,z4,z5,z6]),(0,[z2,z9,z4,z984,z5,z6]),(0,[z1209,z8,z9,z4,z5,z6]),(0,[z1,z8,z217,z4,z5,z6]),(0,[z1,z1291,z9,z4,z5,z6]),(0,[z1,z2,z173,z4,z5,z175])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 520).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1035).take 259) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1294)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [520, 515, 259] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 95).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 186).take 70).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [95, 91, 70] = true :=
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

end PEqualNP.Outside.L_meta_37091

theorem PEqualNP.Outside.L_meta_37091 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243114184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243114184) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37091.solve