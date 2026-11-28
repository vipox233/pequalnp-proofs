import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40217

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4272482952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x5000040120134254#64 ++ 0x940001004804d095#64 ++ 0xee023ce3e03fc7ff#64 ++ 0xfb808f38f80ff1ff#64 : BitVec 256),
   (0x200cd14c90c8992b#64 ++ 0x080334532432264a#64 ++ 0xde1dd35c91c8f93d#64 ++ 0xf78774d724723e4f#64 : BitVec 256),
   (0x41616297160d2e32#64 ++ 0x505858a5c5834b8c#64 ++ 0xbde1e39f1e0f3e33#64 ++ 0xef7878e7c783cf8c#64 : BitVec 256),
   (0x80b603e00b603580#64 ++ 0x602d80f802d80d60#64 ++ 0x7ffe03e01ff03fc3#64 ++ 0x5fff80f807fc0ff0#64 : BitVec 256),
   (0x02dbfc001dbec003#64 ++ 0x80b6ff00076fb000#64 ++ 0xfbfffc001fffc003#64 ++ 0x3effff0007fff000#64 : BitVec 256),
   (0x00ffbbfac0000000#64 ++ 0x003feefeb0000000#64 ++ 0xf8ffffffe0000000#64 ++ 0xfe3ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x20022ca360000000 0x08008b28d8000000

def z1 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z2 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc001fffc003 0x3effff0007fff000

def z3 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1dd35c91c8f93d 0xf78774d724723e4f

def z4 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1e39f1e0f3e33 0xef7878e7c783cf8c

def z5 : W := mkw 0x5000040120134254 0x940001004804d095 0xee023ce3e03fc7ff 0xfb808f38f80ff1ff

def z6 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe03e01ff03fc3 0x5fff80f807fc0ff0

def z7 : W := mkw 0x41f763f7160d2e32 0x507dd8fdc5834b8c 0xfdffe3ff1e0f3e33 0xff7ff8ffc783cf8c

def z8 : W := mkw 0x00dbb80000000000 0x0036ee0000000000 0xf8fffce3e0000000 0xfe3fff38f8000000

def z9 : W := mkw 0x4120029702012e30 0x504800a5c0804b8c 0xac00239f000f3e33 0xeb0008e7c003cf8c

def z10 : W := mkw 0x0092000009200000 0x0024800002480000 0x7bfe00001ff00003 0x1eff800007fc0000

def z11 : W := mkw 0x82ffffe01ffef583 0xe0bffff807ffbd60 0xffffffe01fffffc3 0x7ffffff807fffff0

def z12 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0x11e1c31c1e003800 0x047870c707800e00

def z13 : W := mkw 0x41fffbffd60d2e32 0x507ffefff5834b8c 0xfdfffffffe0f3e33 0xff7fffffff83cf8c

def z14 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0x8001fc1fe0000000 0xa0007f07f8000000

def z15 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfffffffffff03fc3 0xfffffffffffc0ff0

def z16 : W := mkw 0x029a9c0009b2c001 0x80a6a700026cb000 0x421e1c0001f0c000 0x10878700007c3000

def z17 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x8401d35c8008f93c 0xe10074d720023e4f

def z18 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x101dc31c11c03800 0x040770c704700e00

def z19 : W := mkw 0x5000040120134254 0x940001004804d095 0x20022ca3603706c2 0x08008b28d80dc1b0

def z20 : W := mkw 0x4000000100010210 0x1000000040004084 0xee0220e3003f07f3 0xfb808838c00fc1fc

def z21 : W := mkw 0x4161229702012e30 0x505848a5c0804b8c 0xbce1e39f00003e30 0xef3878e7c0000f8c

def z22 : W := mkw 0x020044001dbec003 0x80801100076fb000 0x030000001fffc003 0x00c0000007fff000

def z23 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0x11fdc0001fc00000 0x047f700007f00000

def z24 : W := mkw 0x800000000b603580 0x6000000002d80d60 0x070000001ff03fc3 0x01c0000007fc0ff0

def z25 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x11fc03001fc03800 0x047f00c007f00e00

def z26 : W := mkw 0x4120029702012e30 0x504800a5c0804b8c 0x0400039f00003e30 0xc10000e7c0000f8c

def z27 : W := mkw 0x0000000000000000 0x0000000000000000 0xce0010408008c13d 0xf38004102002304f

def z28 : W := mkw 0xa0bed3ec9be8bdab 0x682fb4fb26fa2f6a 0xdffdd35c9fc8f93d 0xf7ff74d727f23e4f

def z29 : W := mkw 0x80b603facb603580 0x602d80feb2d80d60 0x7ffe03fffff03fc3 0xdfff80fffffc0ff0

def z30 : W := mkw 0x200040041088882b 0x080010010422220a 0x000000000008c03c 0x000000000002300f

def z31 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x7efe03e0003007c3 0x5fbf80f8000c01f0

def z32 : W := mkw 0x4161229306052610 0x505848a4c1814984 0x21e020830e070602 0x08780820c381c180

def z33 : W := mkw 0x500c9549a0134254 0x940325526804d095 0xfe1fffffe03fc7ff 0xff87fffff80ff1ff

def z34 : W := mkw 0x80b202a00b202480 0x602c80a802c80920 0x21e200a00e3006c2 0x08788028038c01b0

def z35 : W := mkw 0x80ffbbfacb202480 0x603feefeb2c80920 0xf9ffffffee3006c2 0xfe7ffffffb8c01b0

def z36 : W := mkw 0x502407fbe0134254 0x940901fef804d095 0xee023fffe03fc7ff 0xfb808ffff80ff1ff

def z37 : W := mkw 0x0008d00010888003 0x0002340004222000 0xda1dd00011c8c001 0x3687740004723000

def z38 : W := mkw 0x22dffd4c9dfed92b 0x88b7ff53277fb64a 0xffffff5c9ffff93f 0xffffffd727fffe4f

def z39 : W := mkw 0x200c914880c09109 0x0803245220302442 0x421c104081c0c10c 0x1087041020703043

def z40 : W := mkw 0x20ffbbfac0c09109 0x083feefeb0302442 0xfaffffffe1c0c10c 0xfebffffff8703043

def z41 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0xb8e3efbf60000000 0xee38fbefd8000000

def z42 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x31ffec001ff70002 0x0c7ffb0007fdc000

def z43 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0xb9fde0001fcf0003 0x2e7f780007f3c000

def z44 : W := mkw 0x1000040020124044 0x8400010008049011 0x42021c60e030c1cc 0x10808718380c3073

def z45 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0x7bffc0001ff00003 0x1efff00007fc0000

def z46 : W := mkw 0x00616292140c0002 0x001858a485030000 0xb9e1e39f1e0f0003 0xee7878e7c783c000

def z47 : W := mkw 0x0020028002002400 0x400800a000800900 0x3de003801e003e03 0x4f7800e007800f80

def z48 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x31fe03a01ff03ec2 0x0c7f80e807fc0fb0

def z49 : W := mkw 0x004db95ac0000000 0x00136e56b0000000 0xd81dff5fe0000000 0xf6077fd7f8000000

def z50 : W := mkw 0x002403fac0000000 0x000900feb0000000 0x000003ffe0000000 0xc00000fff8000000

def z51 : W := mkw 0xa0b643e41be8bdab 0x682d90f906fa2f6a 0x7ffe03e01ff8ffff 0x5fff80f807fe3fff

def z52 : W := mkw 0x52dbfc013dbfc257 0x94b6ff004f6ff095 0xfffffce3ffffc7ff 0xffffff38fffff1ff

def z53 : W := mkw 0x2000000c80000828 0x080000032000020a 0x0000001c8000003c 0x800000072000000f

def z54 : W := mkw 0x612403df82413f38 0x584900f7e0904fce 0x040003df80003f3c 0xc10000f7e0000fcf

def z55 : W := mkw 0x616df3df96cdbf3b 0x585b7cf7e5b36fce 0xfffdf3df9fcfff3f 0xffff7cf7e7f3ffcf

def z56 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x521dd35c91c0f90c 0x148774d724703e43

def z57 : W := mkw 0x50b607e120134254 0x942d81f84804d095 0xfefe3fe3e03fc7ff 0xffbf8ff8f80ff1ff

def z58 : W := mkw 0x204df95ed0c8992b 0x08137e57b432264a 0xde1dff5ff1c8f93d 0xf7877fd7fc723e4f

def z59 : W := mkw 0x8096016009601180 0x2025805802580460 0x6e1e00e001f007c3 0x5b878038007c01f0

def z60 : W := mkw 0x220cd54c9dfed92b 0x88833553277fb64a 0xdf1dd35c9ffff93f 0xf7c774d727fffe4f

def z61 : W := mkw 0x0000000002002400 0x4000000000800900 0x050000001e003e03 0x0140000007800f80

def z62 : W := mkw 0x00416000140c0002 0x0010580005030000 0xb9e1e0001e0f0003 0x2e7878000783c000

def z63 : W := mkw 0x43fbfe971fbfee33 0xd0feffa5c7effb8c 0xffffff9f1ffffe33 0xffffffe7c7ffff8c

def z64 : W := mkw 0x53fbfe973fbfee77 0xd4feffa5cfeffb9d 0xffffffffffffffff 0xffffffffffffffff

def z65 : W := mkw 0x6149f01f948d8a3b 0x18527c07e523628e 0x8001f01f800fc03c 0xa0007c07e003f00f

def z66 : W := mkw 0x200c914c80c09929 0x080324532030264a 0x461c135c81c0f93c 0xd18704d720703e4f

def z67 : W := mkw 0x02dbbc000db6c001 0x80b6ef00036db000 0x63fe3c000ff7c002 0x18ff8f0003fdf000

def z68 : W := mkw 0xa0bed3ec9be8bdab 0x682fb4fb26fa2f6a 0xffffd3fc9ff8ffff 0xfffff4ff27fe3fff

def z69 : W := mkw 0x82dffd601dfed183 0xa0b7ff58077fb460 0xfbfffc601fffc1c3 0x3effff1807fff070

def z70 : W := mkw 0xa0fffbfedbe8bdab 0x683ffeffb6fa2f6a 0xfffffffffff8ffff 0xfffffffffffe3fff

def z71 : W := mkw 0xd0b607e12b7377d4 0xf42d81f84adcddf5 0xfffe3fe3ffffffff 0xffff8ff8ffffffff

def z72 : W := mkw 0x2008d00c9088882b 0x080234032422220a 0x8001d01c8008c03c 0xa00074072002300f

def z73 : W := mkw 0x80ffbbfac2403580 0x603feefeb0900d60 0xfcffffffe0003fc0 0xff3ffffff8000ff0

def z74 : W := mkw 0x009e9968c0000000 0x0027a65a30000000 0xd81fdf7ce0000000 0xf607f7df38000000

def z75 : W := mkw 0x1000040020124044 0x8400010008049011 0x6e021ce0e030c7cf 0x5b808738380c31f3

def z76 : W := mkw 0x90960560297251c4 0xa42581580a5c9471 0x421e1c60e1f0c1cc 0x10878718387c3073

def z77 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0x20e22ca360000000 0x08388b28d8000000

def z78 : W := mkw 0x20fffbfed0c8992b 0x083ffeffb432264a 0xfefffffff1c8f93d 0xffbffffffc723e4f

def z79 : W := mkw 0x029244001dbec003 0x80a49100076fb000 0x7bfe00001fffc003 0x1eff800007fff000

def z80 : W := mkw 0x02fffbfaddac8003 0x00bffefeb76b2000 0x11fdc31c1fc00000 0x047f70c707f00000

def z81 : W := mkw 0x0000040000124000 0x8000010000049000 0xea023c00003fc003 0x3a808f00000ff000

def z82 : W := mkw 0x229e9d4889f2d109 0x88a7a752227cb442 0x421e1c4081f0c10c 0x10878710207c3043

def z83 : W := mkw 0x00be9bfac0000000 0x002fa6feb0000000 0x401e1fffe0000000 0xd00787fff8000000

def z84 : W := mkw 0x616df3df96cdbf3b 0x585b7cf7e5b36fce 0xbdfde39f1fcf3e33 0xef7f78e7c7f3cf8c

def z85 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x10fdc31c00000000 0x043f70c700000000

def z86 : W := mkw 0x50ffbffbe0134254 0x943feffef804d095 0xfeffffffe03fc7ff 0xffbffffff80ff1ff

def z87 : W := mkw 0x00f72bfac0000000 0x003dcafeb0000000 0x20e22fffe0000000 0xc8388bfff8000000

def z88 : W := mkw 0x5000000120010254 0x1400000048004095 0x040000e3e00007fc 0xc1000038f80001ff

def z89 : W := mkw 0x0004014000401100 0x0001005000100440 0x0400034000003900 0x410000d000000e40

def z90 : W := mkw 0x009e9968c0000000 0x0027a65a30000000 0x401e1c60e0000000 0x1007871838000000

def z91 : W := mkw 0x8096016009601180 0x2025805802580460 0x421e006001f001c0 0x10878018007c0070

def z92 : W := mkw 0x1000000020000044 0x0400000008000011 0x00000060e00001cc 0x0000001838000073

def z93 : W := mkw 0x4000000100010210 0x1000000040004084 0xac002083000f0633 0xeb000820c003c18c

def z94 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z95 : W := mkw 0x02d36c001dbec003 0x80b4db00076fb000 0x23e22c001fffc003 0x08f88b0007fff000

def z96 : W := mkw 0x5000000120010254 0x1400000048004095 0xec023ce3e00007fc 0xfb008f38f80001ff

def z97 : W := mkw 0x52dbfc013dbfc257 0x94b6ff004f6ff095 0xfffffc001fffc7ff 0x3fffff0007fff1ff

def z98 : W := mkw 0x0000400410080822 0x0000100104020208 0x9c01c31c10083831 0xe70070c704020e0c

def z99 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe1f3df9e0fff3f 0xfff87cf7e783ffcf

def z100 : W := mkw 0x00ffbbfac0401100 0x003feefeb0100440 0xfefffffff1c03901 0xffbffffffc700e40

def z101 : W := mkw 0x01fffbfed60c2c22 0x407ffeffb5830b08 0xf9fffffffe003800 0xfe7fffffff800e00

def z102 : W := mkw 0x800401400b603580 0x6001005002d80d60 0x5f1c03401ff03fc3 0x57c700d007fc0ff0

def z103 : W := mkw 0x5000040120134254 0x940001004804d095 0xe8023ce3e00fc03c 0xfa008f38f803f00f

def z104 : W := mkw 0x5008d401309bc257 0x940235004c26f095 0xfe1ffce3f1ffc7ff 0xff87ff38fc7ff1ff

def z105 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x53fe03601ff039c0 0x14ff80d807fc0e70

def z106 : W := mkw 0x0000000000000000 0x0000000000000000 0x6e0200e0003007c3 0x5b808038000c01f0

def z107 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0x3de1c39c1e003e03 0x4f7870e707800f80

def z108 : W := mkw 0x41416005160d2e32 0x5050580145834b8c 0xbde1e0001e0f3e33 0x2f7878000783cf8c

def z109 : W := mkw 0x0249fc00149ec003 0x80927f000527b000 0x8001fc00000fc000 0x20007f000003f000

def z110 : W := mkw 0x4169f297168dae33 0x505a7ca5c5a36b8c 0xfffdf39f1fcffe33 0xffff7ce7c7f3ff8c

def z111 : W := mkw 0x82be9fe00bf2f581 0xe0afa7f802fcbd60 0x7ffe1fe01ff0ffc3 0x5fff87f807fc3ff0

def z112 : W := mkw 0x5000040120134254 0x940001004804d095 0xce001040803fc7ff 0xf3800410200ff1ff

def z113 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800208300000000 0xea000820c0000000

def z114 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8023ce3e0000000 0xfa008f38f8000000

def z115 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe3fe3fff03fc3 0xffff8ff8fffc0ff0

def z116 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xb8fde39f00000000 0xee3f78e7c0000000

def z117 : W := mkw 0x200c914880c09109 0x0803245220302442 0x5e1c134091c0f90d 0x578704d024703e43

def z118 : W := mkw 0x02d32c000d364000 0x80b4cb00034d9000 0x21e22c000e370002 0x08788b00038dc000

def z119 : W := mkw 0x82f72fe00f767580 0xe0bdcbf803dd9d60 0x7ffe2fe01ff73fc3 0x5fff8bf807fdcff0

def z120 : W := mkw 0x5000000120010254 0x1400000048004095 0xac0020e3e00f07ff 0xeb000838f803c1ff

def z121 : W := mkw 0xa0be93e88be0b589 0x682fa4fa22f82d62 0x7ffe13e09ff0ffcf 0x5fff84f827fc3ff3

def z122 : W := mkw 0x51416417341f4a76 0x94505905cd07d29d 0x8001fc1fe00fc03c 0xa0007f07f803f00f

def z123 : W := mkw 0x0069ba9ac0000000 0x001a6ea6b0000000 0xb8e1ff9fe0000000 0xee387fe7f8000000

def z124 : W := mkw 0x00dbf80010888003 0x0036fe0004222000 0xfafffc0011c8c001 0x3ebfff0004723000

def z125 : W := mkw 0xc1b643e51f6d3fb2 0x706d90f947db4fec 0x7ffe03e01fff3ff3 0x5fff80f807ffcffc

def z126 : W := mkw 0x802403fac2403580 0x600900feb0900d60 0x040003ffe0003fc0 0xc10000fff8000ff0

def z127 : W := mkw 0x00416004140c0822 0x0010580105030208 0xbde1e31c1e0f3833 0xef7878c70783ce0c

def z128 : W := mkw 0x41416017140d0a32 0x10505805c503428c 0x8001e01f000f0030 0xa0007807c003c00c

def z129 : W := mkw 0x22fffffeddfed92b 0x88bfffffb77fb64a 0xfffffffffffff93f 0xfffffffffffffe4f

def z130 : W := mkw 0x002002b240000000 0x000800ac90000000 0x000000a360000000 0x00000028d8000000

def z131 : W := mkw 0xa2ffffec9ffefdab 0xe8bffffb27ffbf6a 0xfffffffc9fffffff 0xffffffff27ffffff

def z132 : W := mkw 0x300cd54cb0dad96f 0x8c0335532c36b65b 0xde1fdf7cf1f8f9fd 0xf787f7df3c7e3e7f

def z133 : W := mkw 0x41004005160d2e32 0x5040100145834b8c 0x050000001e0f3e33 0x014000000783cf8c

def z134 : W := mkw 0x02412c0004164000 0x80904b0001059000 0x00002c0000070000 0x00000b000001c000

def z135 : W := mkw 0x02089c000092c001 0x808227000024b000 0x00001c000000c000 0x0000070000003000

def z136 : W := mkw 0x5000040120134254 0x940001004804d095 0xea023c03e03fc03f 0xba808f00f80ff00f

def z137 : W := mkw 0x00d360001d2c0002 0x0034d800074b0000 0xfbffe0001fff0003 0x3efff80007ffc000

def z138 : W := mkw 0xc1f763f71f6d3fb2 0x707dd8fdc7db4fec 0xffffe3ff1fff3ff3 0xfffff8ffc7ffcffc

def z139 : W := mkw 0x0004014880000000 0x0001005220000000 0x0000035c80000000 0xc00000d720000000

def z140 : W := mkw 0x00089808c0000000 0x0002260230000000 0x00001c00e0000000 0x0000070038000000

def z141 : W := mkw 0x0008d00010888003 0x0002340004222000 0x101dc00011c00000 0x0407700004700000

def z142 : W := mkw 0x009e9968c0000000 0x0027a65a30000000 0x001c000000000000 0x0007000000000000

def z143 : W := mkw 0x02dbbc0009b2c001 0x80b6ef00026cb000 0xfafffc0001f0c000 0x3ebfff00007c3000

def z144 : W := mkw 0xc1fffbffdf6d3fb2 0x707ffefff7db4fec 0xffffffffffff3ff3 0xffffffffffffcffc

def z145 : W := mkw 0x5000040120134254 0x940001004804d095 0x80003c03e00fc03c 0xa0000f00f803f00f

def z146 : W := mkw 0x229edd4c99fad92b 0x88a7b753267eb64a 0xde1fdf5c91f8f93d 0xf787f7d7247e3e4f

def z147 : W := mkw 0x43fbfa971fadae33 0x50fefea5c7eb6b8c 0xbdfde39f1fcf3e33 0xef7f78e7c7f3cf8c

def z148 : W := mkw 0x2000400410c8992b 0x080010010432264a 0x0600000011c8f93d 0x0180000004723e4f

def z149 : W := mkw 0x5000040120134254 0x940001004804d095 0x06000000003fc7ff 0x01800000000ff1ff

def z150 : W := mkw 0x40416001140d0212 0x1010580045034084 0xbde1e0831e0f0633 0xef787820c783c18c

def z151 : W := mkw 0x8092002009200080 0x2024800802480020 0x00020020003000c0 0x00008008000c0030

def z152 : W := mkw 0x80b603e002403580 0x602d80f800900d60 0x7cfe03e000003fc0 0x5f3f80f800000ff0

def z153 : W := mkw 0x0208d4001dbec003 0x80823500076fb000 0xdb1dd0001fffc003 0x36c7740007fff000

def z154 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x90fdff1fe0000000 0xa43f7fc7f8000000

def z155 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1fd3fc91f8ffff 0xff87f4ff247e3fff

def z156 : W := mkw 0x43dbfc051fbfee33 0xd0f6ff0147effb8c 0xfffffc001ffffe33 0x3fffff0007ffff8c

def z157 : W := mkw 0x000c914880401100 0x0003245220100440 0xde1dd35c91c03901 0xf78774d724700e40

def z158 : W := mkw 0x00fffbfad0888003 0x003ffefeb4222000 0xfafffffff1c8c001 0xfebffffffc723000

def z159 : W := mkw 0x0000400410080822 0x0000100104020208 0x1001c31c10003800 0x040070c704000e00

def z160 : W := mkw 0x80b643e41b683da2 0x602d90f906da0f68 0xffffc3fc1ff83ff3 0xfffff0ff07fe0ffc

def z161 : W := mkw 0x202403fec0401928 0x080900ffb010064a 0x040003ffe000393c 0xc10000fff8000e4f

def z162 : W := mkw 0x22dffd4c9dfed92b 0x88b7ff53277fb64a 0xfbffff1c1ffff803 0x3effffc707fffe00

def z163 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0xe8e23ce3e0000000 0xfa388f38f8000000

def z164 : W := mkw 0x6169f29f968dae3b 0x585a7ca7e5a36b8e 0xbde1f39f9e0ffe3f 0xef787ce7e783ff8f

def z165 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffce3ffffc003 0xfeffff38fffff000

def z166 : W := mkw 0x02dffd489dbec003 0x80b7ff52276fb000 0xfbffff5c9fffc003 0xfeffffd727fff000

def z167 : W := mkw 0x000c914880000000 0x0003245220000000 0xd81dd35c80000000 0xf60774d720000000

def z168 : W := mkw 0x5000000120010254 0x1400000048004095 0x00000003e000003c 0x80000000f800000f

def z169 : W := mkw 0xc3fffff71fffffb3 0xf0fffffdc7ffffec 0xffffffff1ffffff3 0xffffffffc7fffffc

def z170 : W := mkw 0x50ffbbfbe0010254 0x143feefef8004095 0xfcffffffe00007fc 0xff3ffffff80001ff

def z171 : W := mkw 0xc1f723f30f653790 0x707dc8fcc3d94de4 0x7ffe23e31ff73fc3 0x5fff88f8c7fdcff0

def z172 : W := mkw 0x4161229306052610 0x505848a4c1814984 0x3de023831e073e03 0x4f7808e0c781cf80

def z173 : W := mkw 0x00ffbbfac2002400 0x403feefeb0800900 0xfdfffffffe003e03 0xff7fffffff800f80

def z174 : W := mkw 0x0249fc00149ec003 0x80927f000527b000 0xb9e1fc001e0fc003 0x2e787f000783f000

def z175 : W := mkw 0x5000040120134254 0x940001004804d095 0xac003c83e00fc63f 0xeb000f20f803f18f

def z176 : W := mkw 0x5049bc1be0134254 0x94126f06f804d095 0x8001fc1fe00fc03c 0xa0007f07f803f00f

def z177 : W := mkw 0x000c914880000000 0x0003245220000000 0xf81fffffe0000000 0xfe07fffff8000000

def z178 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xfde3fffffe0f3e33 0xff78ffffff83cf8c

def z179 : W := mkw 0xe1fff3ff9fedbfbb 0x787ffcffe7fb6fee 0xfffff3ff9fffffff 0xfffffcffe7ffffff

def z180 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x91fdfc001fcfc000 0x247f7f0007f3f000

def z181 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x461c104091c8f93d 0x1187041024723e4f

def z182 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x17fc03001ff03fc3 0x05ff00c007fc0ff0

def z183 : W := mkw 0x41204285160d2e32 0x504810a145834b8c 0x3de003801e0f3e33 0x4f7800e00783cf8c

def z184 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x91e1e31f1e0f3830 0xa47878c7c783ce0c

def z185 : W := mkw 0x00b603e009200000 0x002d80f802480000 0x7bfe03e01ff00003 0x5eff80f807fc0000

def z186 : W := mkw 0x22dff94c9dec992b 0x08b7fe53277b264a 0xdffdd35c9fc8f93d 0xf7ff74d727f23e4f

def z187 : W := mkw 0x0004014000401100 0x0001005000100440 0x5e1c034011c03901 0x578700d004700e40

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x42020060003001c0 0x10808018000c0070

def z189 : W := mkw 0x41f36ab7560d2e32 0x507cdaadd5834b8c 0xbde3efbf7e0f3e33 0xef78fbefdf83cf8c

def z190 : W := mkw 0x41004005160d2e32 0x5040100145834b8c 0x9d01c31c1e0f3e33 0xe74070c70783cf8c

def z191 : W := mkw 0x614df15f94cd9b3b 0x18537c57e53366ce 0xde1df35f91cff93d 0xf7877cd7e473fe4f

def z192 : W := mkw 0x00dbb80000000000 0x0036ee0000000000 0xf8fffc0000000000 0x3e3fff0000000000

def z193 : W := mkw 0x02fffffaddbec003 0x80bffffeb76fb000 0xfbffffffffffc003 0xfefffffffffff000

def z194 : W := mkw 0x8096016009601180 0x2025805802580460 0x7bfe00601ff001c3 0x1eff801807fc0070

def z195 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x141dc35c91c0393c 0xc50770d724700e4f

def z196 : W := mkw 0x41ffbbfbc6052610 0x507feefef1814984 0xf9ffffffee070602 0xfe7ffffffb81c180

def z197 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffc409fffc13f 0xffffff1027fff04f

def z198 : W := mkw 0x80f723f20b603580 0x603dc8fc82d80d60 0xffffe3ff1ff03fc3 0xfffff8ffc7fc0ff0

def z199 : W := mkw 0x02dffd68ddbec003 0x80b7ff5a376fb000 0xfbfffc60ffffc003 0x3effff183ffff000

def z200 : W := mkw 0x006dbbfac0000000 0x001b6efeb0000000 0x8001ffffe0000000 0xe0007ffff8000000

def z201 : W := mkw 0x80ffbbe00b603580 0x603feef802d80d60 0xffffffe01ff03fc3 0x7ffffff807fc0ff0

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0xc800104080000000 0xf200041020000000

def z203 : W := mkw 0x22dbfc041dfed92b 0x88b6ff01077fb64a 0xfffffc001ffff93f 0x3fffff0007fffe4f

def z204 : W := mkw 0x00dbbc0000124000 0x8036ef0000049000 0xfafffc00003fc003 0x3ebfff00000ff000

def z205 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x78fe03e000000000 0x5e3f80f800000000

def z206 : W := mkw 0x0061229202002400 0x401848a480800900 0xbde1e39f1e003e03 0xef7878e7c7800f80

def z207 : W := mkw 0x802403e002403580 0x600900f800900d60 0x040003e000003fc0 0x410000f800000ff0

def z208 : W := mkw 0x20fffbfed0c8992b 0x083ffeffb432264a 0xf8fffffff1c03800 0xfe3ffffffc700e00

def z209 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xd8fdd35c80000000 0xf63f74d720000000

def z210 : W := mkw 0x00f72bf240000000 0x003dcafc90000000 0x78fe2fe360000000 0x5e3f8bf8d8000000

def z211 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xf9ffffffffc03800 0xfe7ffffffff00e00

def z212 : W := mkw 0x02dbfc1addbec003 0x80b6ff06b76fb000 0xfbfffc1fffffc003 0xbeffff07fffff000

def z213 : W := mkw 0x0000040000124000 0x8000010000049000 0xee023c40803fc13f 0xfb808f10200ff04f

def z214 : W := mkw 0x41416017140d0a32 0x10505805c503428c 0x9c01e31f100f3831 0xe70078c7c403ce0c

def z215 : W := mkw 0x80be93e88b603580 0x602fa4fa22d80d60 0xffffd3fc9ff03fc3 0xfffff4ff27fc0ff0

def z216 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x15e1c31c1e0f3e33 0x057870c70783cf8c

def z217 : W := mkw 0x4000000100010210 0x1000000040004084 0x2000208300070602 0x08000820c001c180

def z218 : W := mkw 0x51616697361f6e76 0xd45859a5cd87db9d 0xbde1ff9ffe0ffe3f 0xef787fe7ff83ff8f

def z219 : W := mkw 0x2004414c90c8992b 0x080110532432264a 0x0600035c91c8f93d 0xc18000d724723e4f

def z220 : W := mkw 0x22dbfc0c9dbec82b 0x88b6ff03276fb20a 0xfbfffc1c9fffc03f 0xbeffff0727fff00f

def z221 : W := mkw 0x700c9549a0d3d35d 0x9c0325526834f4d7 0xee1e3ce3e1ffc7ff 0xfb878f38f87ff1ff

def z222 : W := mkw 0xc16162971f6d3fb2 0x705858a5c7db4fec 0xbfe1e39f1fff3ff3 0xeff878e7c7ffcffc

def z223 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x30ffefbf60000000 0x0c3ffbefd8000000

def z224 : W := mkw 0x40ffbbfbc0010210 0x103feefef0004084 0xfcffffffe00f0633 0xff3ffffff803c18c

def z225 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z226 : W := mkw 0x00ffbbfac9200000 0x003feefeb2480000 0xfbfffffffff00003 0xfefffffffffc0000

def z227 : W := mkw 0x00fbbabac0000000 0x003eeeaeb0000000 0xa0e3fcbfe0000000 0xa838ff2ff8000000

def z228 : W := mkw 0x416563d7164d3f32 0x505958f5c5934fcc 0xfffde3df1fcf3f33 0xffff78f7c7f3cfcc

def z229 : W := mkw 0x0000400010080002 0x0000100004020000 0x9801c00010080001 0x2600700004020000

def z230 : W := mkw 0x00b603fac0000000 0x002d80feb0000000 0x78fe03ffe0000000 0xde3f80fff8000000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x420010408000c10c 0x1080041020003043

def z232 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x161dc31c11c8f93d 0x058770c704723e4f

def z233 : W := mkw 0x02dbfc00149ec003 0x80b6ff000527b000 0xf8fffc00000fc000 0x3e3fff000003f000

def z234 : W := mkw 0x80b202a00b202480 0x602c80a802c80920 0x3de203a01e303ec3 0x4f7880e8078c0fb0

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0xee023ce3e008c13d 0xfb808f38f802304f

def z236 : W := mkw 0x209ed96cd0c8992b 0x0827b65b3432264a 0xde1fdf7cf1c8f93d 0xf787f7df3c723e4f

def z237 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x13fdc0001fffc003 0x04ff700007fff000

def z238 : W := mkw 0x0004014000401100 0x0001005000100440 0x101c030011c03800 0x040700c004700e00

def z239 : W := mkw 0x4000040100134210 0x900001004004d084 0xee023c83003fc633 0xfb808f20c00ff18c

def z240 : W := mkw 0x0092040009324000 0x80248100024c9000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z241 : W := mkw 0x0004014000000000 0x0001005000000000 0x581c034000000000 0x560700d000000000

def z242 : W := mkw 0x820044001ffef583 0xe080110007ffbd60 0x070000001fffffc3 0x01c0000007fffff0

def z243 : W := mkw 0x224dfd4c94ded92b 0x88937f532537b64a 0xde1dff5c91cff93d 0xf7877fd72473fe4f

def z244 : W := mkw 0x51616697361f6e76 0xd45859a5cd87db9d 0xffe3fffffe3fffff 0xfff8ffffff8fffff

def z245 : W := mkw 0x700cd54db0dbdb7f 0x9c0335536c36f6df 0xfe1ffffff1ffffff 0xff87fffffc7fffff

def z246 : W := mkw 0x0041201200000000 0x0010480480000000 0x8001e01f00000000 0xa0007807c0000000

def z247 : W := mkw 0x509e9d69e0134254 0x9427a75a7804d095 0xee1e3ce3e03fc7ff 0xfb878f38f80ff1ff

def z248 : W := mkw 0x02d32c000d364000 0x80b4cb00034d9000 0xebe23c000e3fc003 0x3af88f00038ff000

def z249 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xc21dd05c81c8c13c 0xb08774172072304f

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0xee023ce3e03007c3 0xfb808f38f80c01f0

def z251 : W := mkw 0x5000040120134254 0x940001004804d095 0x84003ce3e00fc7fc 0xe1000f38f803f1ff

def z252 : W := mkw 0x8096016009601180 0x2025805802580460 0x5e1e036011f039c1 0x578780d8047c0e70

def z253 : W := mkw 0xc12403f702413fb0 0x704900fdc0904fec 0x040003ff00003ff0 0xc10000ffc0000ffc

def z254 : W := mkw 0x00416000140c0002 0x0010580005030000 0x8001e000000f0000 0x200078000003c000

def z255 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1ffffff1c8f93d 0xff87fffffc723e4f

def z256 : W := mkw 0x00dfb968c0000000 0x0037ee5a30000000 0xf8fffc60e0000000 0x3e3fff1838000000

def z257 : W := mkw 0x0249f800148c8003 0x00927e0005232000 0x0001c00000000000 0x0000700000000000

def z258 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfeffffffe008c13d 0xffbffffff802304f

def z259 : W := mkw 0x4000000100010210 0x1000000040004084 0xec023ce3e00f0633 0xfb008f38f803c18c

def z260 : W := mkw 0x0020028002002400 0x400800a000800900 0x11e003001e003800 0x047800c007800e00

def z261 : W := mkw 0x2008d00c90c8992b 0x080234032432264a 0x8601d01c91c8f93d 0xa180740724723e4f

def z262 : W := mkw 0x02fffffad49ec003 0x80bffffeb527b000 0xf8ffffffe00fc000 0xfe3ffffff803f000

def z263 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x60fe3ce3e0000000 0x183f8f38f8000000

def z264 : W := mkw 0x0000000000000000 0x0000000000000000 0x200200a0003006c2 0x08008028000c01b0

def z265 : W := mkw 0x00dfb97ac0000000 0x0037ee5eb0000000 0xc01ffc7fe0000000 0xb007ff1ff8000000

def z266 : W := mkw 0x0061629610080822 0x001858a584020208 0xbce1e39f10083831 0xef3878e7c4020e0c

def z267 : W := mkw 0x000c914880000000 0x0003245220000000 0xde1dd35c8008c13d 0xf78774d72002304f

def z268 : W := mkw 0x2008900880808009 0x0802240220202002 0x000010008000c00c 0x0000040020003003

def z269 : W := mkw 0x41004005160d2e32 0x5040100145834b8c 0xad0020831e0f3e33 0xeb400820c783cf8c

def z270 : W := mkw 0x5000040120134254 0x940001004804d095 0x86003c03e03fc7ff 0xa1800f00f80ff1ff

def z271 : W := mkw 0x2004414410c8992b 0x080110510432264a 0x5e1c034011c8f93d 0x578700d004723e4f

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x680200e000000000 0x5a00803800000000

def z273 : W := mkw 0x502403fbe0010254 0x140900fef8004095 0x040003ffe00007fc 0xc10000fff80001ff

def z274 : W := mkw 0x0092000009200000 0x0024800002480000 0x21e200000e300002 0x08788000038c0000

def z275 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xbde1e3fffe0f3fff 0xef7878ffff83cfff

def z276 : W := mkw 0x42dbfc011dbfc213 0x90b6ff00476ff084 0xfffffc831fffc633 0xffffff20c7fff18c

def z277 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x78ffc3fc00000000 0x5e3ff0ff00000000

def z278 : W := mkw 0x52d32c012d374254 0x94b4cb004b4dd095 0xefe23ce3ee3fc7ff 0xfbf88f38fb8ff1ff

def z279 : W := mkw 0x5000040120134254 0x940001004804d095 0x00002c0360070000 0x00000b00d801c000

def z280 : W := mkw 0x00b603e000401100 0x002d80f800100440 0x7efe03e011c03901 0x5fbf80f804700e40

def z281 : W := mkw 0x00ffbbe000000000 0x003feef800000000 0xf8ffffe000000000 0x7e3ffff800000000

def z282 : W := mkw 0xd0960561297353d4 0xb42581584a5cd4f5 0xee1e3ce3e1ffc7ff 0xfb878f38f87ff1ff

def z283 : W := mkw 0x02920c0009324000 0x80a48300024c9000 0x00020c0000300000 0x00008300000c0000

def z284 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0xb9e1e31c1e0f3803 0x2e7878c70783ce00

def z285 : W := mkw 0x006db3da80000000 0x001b6cf6a0000000 0xf8fdf3df80000000 0xfe3f7cf7e0000000

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e3e0000000 0xc0000038f8000000

def z287 : W := mkw 0x109e9d68e0124044 0x8427a75a38049011 0x421e1c60e030c1cc 0x10878718380c3073

def z288 : W := mkw 0x0000040000124000 0x8000010000049000 0x42021c000030c000 0x10808700000c3000

def z289 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x10fdc3ffe0000000 0xc43f70fff8000000

def z290 : W := mkw 0x002403fac0000000 0x000900feb0000000 0xe8023fffe0000000 0xfa008ffff8000000

def z291 : W := mkw 0x90b607e02b7275c4 0xe42d81f80adc9d71 0x7ffe1fe0fff0ffcf 0x5fff87f83ffc3ff3

def z292 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x25e020831e0f3e33 0x09780820c783cf8c

def z293 : W := mkw 0x52d32c012d374254 0x94b4cb004b4dd095 0x21e22ca36e3706c2 0x08788b28db8dc1b0

def z294 : W := mkw 0x0049f000148c8003 0x00127c0005232000 0xfbfdf0001fcfc003 0x3eff7c0007f3f000

def z295 : W := mkw 0x82fffffadffef583 0xe0bffffeb7ffbd60 0xffffffffffffffc3 0xfffffffffffffff0

def z296 : W := mkw 0x02dbbc000d364000 0x80b6ef00034d9000 0xf9fffc000e370002 0x3e7fff00038dc000

def z297 : W := mkw 0x0020028000000000 0x000800a000000000 0x38e0038000000000 0x4e3800e000000000

def z298 : W := mkw 0x0061229200000000 0x001848a480000000 0xb8e1e39f00000000 0xee3878e7c0000000

def z299 : W := mkw 0x2004014c80401928 0x080100532010064a 0x0400035c8000393c 0xc10000d720000e4f

def z300 : W := mkw 0x0008900000808001 0x0002240000202000 0x421c100001c0c000 0x1087040000703000

def z301 : W := mkw 0x200c914880c09109 0x0803245220302442 0xce1c104081c8c13d 0xf38704102072304f

def z302 : W := mkw 0x43f32e930f376610 0xd0fccba4c3cdd984 0x21e22c830e370602 0x08788b20c38dc180

def z303 : W := mkw 0x202cd3fed0c8992b 0x080b34ffb432264a 0xde1dd3fff1c8f93d 0xf78774fffc723e4f

def z304 : W := mkw 0x4161229306052610 0x505848a4c1814984 0xb9e1e39f0e070602 0xee7878e7c381c180

def z305 : W := mkw 0x4149f81fd40d0a32 0x10527e07f503428c 0x8001fc1fe00f0030 0xa0007f07f803c00c

def z306 : W := mkw 0x02004400149ec003 0x808011000527b000 0x00000000000fc000 0x000000000003f000

def z307 : W := mkw 0x00dbb80009200000 0x0036ee0002480000 0xfbfffc001ff00003 0x3effff0007fc0000

def z308 : W := mkw 0x5000040120134254 0x940001004804d095 0x62023ce3e037c7ce 0x18808f38f80df1f3

def z309 : W := mkw 0x000c914880000000 0x0003245220000000 0x401c104080000000 0x1007041020000000

def z310 : W := mkw 0xa00cd14c9be8bdab 0x6803345326fa2f6a 0xdf1dd35c9ff8ffff 0xf7c774d727fe3fff

def z311 : W := mkw 0x00fffbfad40c0002 0x003ffefeb5030000 0xf9fffffffe0f0003 0xfe7fffffff83c000

def z312 : W := mkw 0xd0b603e12b6137d4 0x742d80f84ad84df5 0x7ffe03e3fff03fff 0xdfff80f8fffc0fff

def z313 : W := mkw 0x00be93e880000000 0x002fa4fa20000000 0xf8ffd3fc80000000 0xfe3ff4ff20000000

def z314 : W := mkw 0x00004000140c0002 0x0000100005030000 0x010000001e0f0003 0x004000000783c000

def z315 : W := mkw 0x02d328000d240000 0x00b4ca0003490000 0x01e000000e000000 0x0078000003800000

def z316 : W := mkw 0x0000000000000000 0x0000000000000000 0x800010008008c03c 0xa00004002002300f

def z317 : W := mkw 0x80b603e009601180 0x202d80f802580460 0x7afe03e001f001c0 0x5ebf80f8007c0070

def z318 : W := mkw 0x00dbb81ac0000000 0x0036ee06b0000000 0xf8fffc1fe0000000 0xbe3fff07f8000000

def z319 : W := mkw 0x82ffffe01ffef583 0xe0bffff807ffbd60 0xfbffff001ffff803 0x3effffc007fffe00

def z320 : W := mkw 0xc16563f7164d3fb2 0x705958fdc5934fec 0xbde1e3ff1e0f3ff3 0xef7878ffc783cffc

def z321 : W := mkw 0x02d36c001d3e4002 0x80b4db00074f9000 0xb9e3ec001e3f0003 0x2e78fb00078fc000

def z322 : W := mkw 0x809200000b603580 0x6024800002d80d60 0x7ffe00001ff03fc3 0x1fff800007fc0ff0

def z323 : W := mkw 0x5000000120010254 0x1400000048004095 0xce0010e3e008c7fd 0xf3800438f80231ff

def z324 : W := mkw 0x02dffd401dfed103 0x80b7ff50077fb440 0xffffff401ffff903 0x7fffffd007fffe40

def z325 : W := mkw 0x2004014880401108 0x0801005220100442 0x000000408000010c 0x0000001020000043

def z326 : W := mkw 0x8096016009601180 0x2025805802580460 0x001c000001c00000 0x0007000000700000

def z327 : W := mkw 0x0041281240000000 0x00104a0490000000 0x00002c0360000000 0x00000b00d8000000

def z328 : W := mkw 0x00b603e002002400 0x402d80f800800900 0x7dfe03e01e003e03 0x5f7f80f807800f80

def z329 : W := mkw 0x5000040120134254 0x940001004804d095 0x6e0200e0003fc7ff 0x5b808038000ff1ff

def z330 : W := mkw 0xa02403ec82403da8 0x680900fb20900f6a 0x040003fc80003ffc 0xc10000ff20000fff

def z331 : W := mkw 0xd1f767f73f7f7ff6 0xf47dd9fdcfdfdffd 0xffffffffffffffff 0xffffffffffffffff

def z332 : W := mkw 0x4120029302012610 0x504800a4c0804984 0x0000008300000600 0x00000020c0000180

def z333 : W := mkw 0x50004405301b4a76 0x940011014c06d29d 0xfe03fffff03fffff 0xff80fffffc0fffff

def z334 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffce01fffc7c3 0x7fffff3807fff1f0

def z335 : W := mkw 0x00416000140c0002 0x0010580005030000 0x11e1c0001e000000 0x0478700007800000

def z336 : W := mkw 0x5000040120134254 0x940001004804d095 0xee023c00003fc7ff 0x3b808f00000ff1ff

def z337 : W := mkw 0x5000040120134254 0x940001004804d095 0xe8023ce3e03706c2 0xfa008f38f80dc1b0

def z338 : W := mkw 0x800000000b603580 0x6000000002d80d60 0x6f0200e01ff03fc3 0x5bc0803807fc0ff0

def z339 : W := mkw 0x0000001ac0000000 0x00000006b0000000 0x0000001fe0000000 0x80000007f8000000

def z340 : W := mkw 0xd00004012b7377d4 0xf40001004adcddf5 0xef023ce3ffffffff 0xfbc08f38ffffffff

def z341 : W := mkw 0x4349fc17149fca33 0x90d27f05c527f28c 0x8001fc1f000fc030 0xa0007f07c003f00c

def z342 : W := mkw 0x5020068122136654 0xd40801a04884d995 0xffe23fe3fe3fffff 0xfff88ff8ff8fffff

def z343 : W := mkw 0x41204297160d2e32 0x504810a5c5834b8c 0x0500039f1e0f3e33 0xc14000e7c783cf8c

def z344 : W := mkw 0x220044041dfed92b 0x88801101077fb64a 0x070000001ffff93f 0x01c0000007fffe4f

def z345 : W := mkw 0x02dbfc041dbec823 0x80b6ff01076fb208 0xffffff1c1ffff833 0xffffffc707fffe0c

def z346 : W := mkw 0x802403e00b603580 0x600900f802d80d60 0x070003e01ff03fc3 0x41c000f807fc0ff0

def z347 : W := mkw 0x0000000000000000 0x0000000000000000 0x80003c03e0000000 0xa0000f00f8000000

def z348 : W := mkw 0x00fbba9200000000 0x003eeea480000000 0xf8ffff9f00000000 0xfe3fffe7c0000000

def z349 : W := mkw 0xd0b206a12b3366d4 0xf42c81a84accd9b5 0xefe23ce3ee3fc7ff 0xfbf88f38fb8ff1ff

def z350 : W := mkw 0x5061269320134254 0x941849a4c804d095 0xfee3ffffe03fc7ff 0xffb8fffff80ff1ff

def z351 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x15e1c39f1e003e30 0xc57870e7c7800f8c

def z352 : W := mkw 0x0004014000401100 0x0001005000100440 0x7e1e03e011f03fc3 0x5f8780f8047c0ff0

def z353 : W := mkw 0x80f32ab24b202480 0x603ccaac92c80920 0x21e22ca36e3006c2 0x08788b28db8c01b0

def z354 : W := mkw 0x029a980009a08001 0x00a6a60002682000 0x001c000001c00000 0x0007000000700000

def z355 : W := mkw 0x5000000120010254 0x1400000048004095 0x6e0200e3e03007ff 0xdb808038f80c01ff

def z356 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe13e09ff8ffff 0xffff84f827fe3fff

def z357 : W := mkw 0x5000040120134254 0x940001004804d095 0xae002083003fc7ff 0xeb800820c00ff1ff

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0xca0010000008c001 0x3280040000023000

def z359 : W := mkw 0x009a980000000000 0x0026a60000000000 0x401e1c0000000000 0x1007870000000000

def z360 : W := mkw 0x20fffbfed0c8992b 0x083ffeffb432264a 0x10fdc31c11c03800 0x043f70c704700e00

def z361 : W := mkw 0x0120029602002c20 0x404800a580800b08 0x0000031c00003800 0x000000c700000e00

def z362 : W := mkw 0x00d3280000000000 0x0034ca0000000000 0x20e22c0000000000 0x08388b0000000000

def z363 : W := mkw 0x5000000120010254 0x1400000048004095 0x04000000000007fc 0x01000000000001ff

def z364 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe3e3ff1e3f3ff3 0xfff8f8ffc78fcffc

def z365 : W := mkw 0x020040001dac8003 0x00801000076b2000 0x010000001fc00000 0x0040000007f00000

def z366 : W := mkw 0x5000040120134254 0x940001004804d095 0x00000000000fc03c 0x000000000003f00f

def z367 : W := mkw 0x0020028002002400 0x400800a000800900 0x0400038000003e00 0x410000e000000f80

def z368 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x901dd31c91c8f83c 0xa40774c724723e0f

def z369 : W := mkw 0x1000040020124044 0x8400010008049011 0xea023ce3e030c1cc 0xfa808f38f80c3073

def z370 : W := mkw 0xd02407e1225377d4 0xf40901f84894ddf5 0xee023fe3e03fffff 0xfb808ff8f80fffff

def z371 : W := mkw 0x41fffbffd60d2e32 0x507ffefff5834b8c 0xbdfde39f1e0f3e33 0xef7f78e7c783cf8c

def z372 : W := mkw 0x41416017140d0a32 0x10505805c503428c 0xb9e1e01f1e0f0033 0xae787807c783c00c

def z373 : W := mkw 0x7000440530dbdb7f 0x9c0011014c36f6df 0x0600000011ffffff 0x01800000047fffff

def z374 : W := mkw 0x0020028002002400 0x400800a000800900 0x7fe203e01e303fc3 0x5ff880f8078c0ff0

def z375 : W := mkw 0x41416017140d0a32 0x10505805c503428c 0xac01e09f000f0633 0xeb007827c003c18c

def z376 : W := mkw 0x4169fa9fd60d2e32 0x505a7ea7f5834b8c 0xbde1ff9ffe0f3e33 0xef787fe7ff83cf8c

def z377 : W := mkw 0x4000400510090a32 0x100010014402428c 0xbc01e39f100f3e33 0xef0078e7c403cf8c

def z378 : W := mkw 0x0061229200000000 0x001848a480000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z379 : W := mkw 0x200c914880c09109 0x0803245220302442 0xda1dd35c81c0c10c 0xf68774d720703043

def z380 : W := mkw 0x0008d00410888823 0x0002340104222208 0xde1dd31c11c8f831 0xf78774c704723e0c

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000e0000007c0 0x41000038000001f0

def z382 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x79fe03e01fc03800 0x5e7f80f807f00e00

def z383 : W := mkw 0x00fffbfed0080822 0x003ffeffb4020208 0xfcfffffff0083831 0xff3ffffffc020e0c

def z384 : W := mkw 0x43fbfe931fbfe613 0xd0feffa4c7eff984 0xfbfffc831fffc603 0x3effff20c7fff180

def z385 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x3dfc03801fc03e03 0x4f7f00e007f00f80

def z386 : W := mkw 0x0061229200000000 0x001848a480000000 0x10e1c31c00000000 0x043870c700000000

def z387 : W := mkw 0x200cd54c90dad92b 0x880335532436b64a 0xfe1fff5c91fff93f 0xff87ffd7247ffe4f

def z388 : W := mkw 0xd00004012b7377d4 0xf40001004adcddf5 0x070000001fffffff 0x01c0000007ffffff

def z389 : W := mkw 0x0004014000401100 0x0001005000100440 0xde1c134091c8f93d 0xf78704d024723e4f

def z390 : W := mkw 0x0249fc00149ec003 0x80927f000527b000 0xea03fc00003fc003 0x3a80ff00000ff000

def z391 : W := mkw 0x0004014000401100 0x0001005000100440 0x421c004001c00100 0x1087001000700040

def z392 : W := mkw 0xc1f362b71f2d2eb2 0x707cd8adc7cb4bac 0xbde3e3bf1e3f3ef3 0xef78f8efc78fcfbc

def z393 : W := mkw 0x80b603e00b202480 0x602d80f802c80920 0x79fe03e00e3006c2 0x5e7f80f8038c01b0

def z394 : W := mkw 0x8004016000401180 0x2001005800100460 0x00000060000001c0 0x0000001800000070

def z395 : W := mkw 0x0000400410080822 0x0000100104020208 0x8001c01c00080030 0xa00070070002000c

def z396 : W := mkw 0x82b647e01ffef583 0xe0ad91f807ffbd60 0x7ffe03e01fffffc3 0x5fff80f807fffff0

def z397 : W := mkw 0x2000000000c09109 0x0800000000302442 0x0200000001c0c10c 0x0080000000703043

def z398 : W := mkw 0x02ffbffacd364000 0x80bfeffeb34d9000 0xf9ffffffee370002 0xfe7ffffffb8dc000

def z399 : W := mkw 0x7004014da0411b7c 0x1c010053681046df 0x040003ffe0003ffc 0xc10000fff8000fff

def z400 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0x9de1c31c1e083831 0xe77870c707820e0c

def z401 : W := mkw 0x029adc0019bac003 0x80a6b700066eb000 0xda1fdc0011f8c001 0x3687f700047e3000

def z402 : W := mkw 0x0000040000124000 0x8000010000049000 0x02000000003fc003 0x00800000000ff000

def z403 : W := mkw 0x7004054da0535b7c 0x9c0101536814d6df 0xee023fffe03fffff 0xfb808ffff80fffff

def z404 : W := mkw 0x81f763f61f6c3da2 0x607dd8fd87db0f68 0x7fffc3fc1ff03fc3 0x5ffff0ff07fc0ff0

def z405 : W := mkw 0x4000000100010210 0x1000000040004084 0x04000000000f0633 0x010000000003c18c

def z406 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x8401e39f000f3e30 0xe10078e7c003cf8c

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0xee0210e08038c7ff 0xfb808438200e31ff

def z408 : W := mkw 0x009e9968c0000000 0x0027a65a30000000 0xe81e3ce3e0000000 0xfa078f38f8000000

def z409 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfbfffc60ffffc1cf 0x3effff183ffff073

def z410 : W := mkw 0x0092000009200000 0x0024800002480000 0x421e000001f00000 0x10878000007c0000

def z411 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfeffffffe03007c3 0xffbffffff80c01f0

def z412 : W := mkw 0x0200040009b2c001 0x80800100026cb000 0x0200000001f0c000 0x00800000007c3000

def z413 : W := mkw 0x204df14c94cc992b 0x08137c532533264a 0xfffdf35c9fcff93f 0xffff7cd727f3fe4f

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c00030010003801 0x470000c004000e00

def z415 : W := mkw 0xd0b206a12b3366d4 0xf42c81a84accd9b5 0x21e22ca36e3706c2 0x08788b28db8dc1b0

def z416 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0xdbfdd0001fc8c001 0x36ff740007f23000

def z417 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xa1e3fc000e3fc002 0x2878ff00038ff000

def z418 : W := mkw 0x520044013dbfc257 0x948011004f6ff095 0xef023ce3ffffc7ff 0xfbc08f38fffff1ff

def z419 : W := mkw 0x716df7dfb6dfff7f 0xdc5b7df7edb7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z420 : W := mkw 0x80b202a00b202480 0x602c80a802c80920 0x7bfe00a01ff006c3 0x1eff802807fc01b0

def z421 : W := mkw 0xd0ffbffbeb7377d4 0xf43feffefadcddf5 0xffffffffffffffff 0xffffffffffffffff

def z422 : W := mkw 0x81f763f61f6c3da2 0x607dd8fd87db0f68 0x11fdc31c1fc03800 0x047f70c707f00e00

def z423 : W := mkw 0x51004405361f6e76 0xd44011014d87db9d 0xef023ce3fe3fffff 0xfbc08f38ff8fffff

def z424 : W := mkw 0x002c93fac0000000 0x000b24feb0000000 0xd81dd3ffe0000000 0xf60774fff8000000

def z425 : W := mkw 0x200c914880c09109 0x0803245220302442 0x001c000001c00000 0x0007000000700000

def z426 : W := mkw 0x52dbfc013dbfc257 0x94b6ff004f6ff095 0xfbfffca37fffc6c3 0x3effff28dffff1b0

def z427 : W := mkw 0x80ffbbfac9601180 0x203feefeb2580460 0xfaffffffe1f001c0 0xfebffffff87c0070

def z428 : W := mkw 0x006523fac0000000 0x001948feb0000000 0xb8e1e3ffe0000000 0xee3878fff8000000

def z429 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x31e1e39f1e073e02 0x0c7878e7c781cf80

def z430 : W := mkw 0x5000040120134254 0x940001004804d095 0x6e022ce3603707c3 0x5b808b38d80dc1f0

def z431 : W := mkw 0x600cd14d90c99b3b 0x18033453643266ce 0xfe1df3df91cfff3f 0xff877cf7e473ffcf

def z432 : W := mkw 0x5000040120134254 0x940001004804d095 0x46021c60e03fc7ff 0x11808718380ff1ff

def z433 : W := mkw 0x02ffffe01dbec003 0x80bffff8076fb000 0xfbffffe01fffc003 0x7efffff807fff000

def z434 : W := mkw 0x20bed3ec90c8992b 0x082fb4fb2432264a 0xfeffd3fc91c8f93d 0xffbff4ff24723e4f

def z435 : W := mkw 0x2249fc0c949ec82b 0x88927f032527b20a 0x8001fc1c800fc03c 0xa0007f072003f00f

def z436 : W := mkw 0x802002a002002480 0x600800a800800920 0x000000a0000006c0 0x00000028000001b0

def z437 : W := mkw 0x5120029722012e74 0x544800a5c8804b9d 0x040003ffe0003ffc 0xc10000fff8000fff

def z438 : W := mkw 0x7000440530dbdb7f 0x9c0011014c36f6df 0xee023ce3f1ffffff 0xfb808f38fc7fffff

def z439 : W := mkw 0x024164001dbec003 0x80905900076fb000 0xbbe1e0001fffc003 0x2ef8780007fff000

def z440 : W := mkw 0x41004005140d0a32 0x104010014503428c 0x00000000000f0030 0x000000000003c00c

def z441 : W := mkw 0x5049bc1be0134254 0x94126f06f804d095 0xee03fcffe03fc7ff 0xfb80ff3ff80ff1ff

def z442 : W := mkw 0x5120069722136e74 0xd44801a5c884db9d 0xee023fffe03fffff 0xfb808ffff80fffff

def z443 : W := mkw 0x80b202a00b202480 0x602c80a802c80920 0x6fe200e00e3007c3 0x5bf88038038c01f0

def z444 : W := mkw 0x5000040120134254 0x940001004804d095 0x46021ce3e030c7fc 0xd1808738f80c31ff

def z445 : W := mkw 0x200cd14890c8910b 0x0803345224322442 0xda1dd04091c8c10d 0x3687741024723043

def z446 : W := mkw 0x0000400410080822 0x0000100104020208 0x0400000010083831 0x0100000004020e0c

def z447 : W := mkw 0x80bed3e01be8b583 0x602fb4f806fa2d60 0xffffd3e01ff8ffc3 0x7ffff4f807fe3ff0

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x6a02000000300003 0x1a808000000c0000

def z449 : W := mkw 0x0249fc00149ec003 0x80927f000527b000 0xda1dfc0011cfc001 0x36877f000473f000

def z450 : W := mkw 0x0092000000000000 0x0024800000000000 0x78fe000000000000 0x1e3f800000000000

def z451 : W := mkw 0x802403e002403580 0x600900f800900d60 0x3de003e01e003fc3 0x4f7800f807800ff0

def z452 : W := mkw 0x0000040000124000 0x8000010000049000 0x80003c00000fc000 0x20000f000003f000

def z453 : W := mkw 0x5000040120134254 0x940001004804d095 0x060000e3e03fc7ff 0xc1800038f80ff1ff

def z454 : W := mkw 0x412403ffc2012e30 0x504900fff0804b8c 0x040003ffe0003e30 0xc10000fff8000f8c

def z455 : W := mkw 0x80f763e01f6c3582 0x603dd8f807db0d60 0xffffe3e01fff3fc3 0x7ffff8f807ffcff0

def z456 : W := mkw 0x51004405361f6e76 0xd44011014d87db9d 0x070000001e3fffff 0x01c00000078fffff

def z457 : W := mkw 0x01fffbfed60c2c22 0x407ffeffb5830b08 0x11fdc31c1e003800 0x047f70c707800e00

def z458 : W := mkw 0x5000040120134254 0x940001004804d095 0x24022ce3e03707fe 0xc9008b38f80dc1ff

def z459 : W := mkw 0x20dff94c90c8992b 0x0837fe532432264a 0xfeffff5c91c8f93d 0xffbfffd724723e4f

def z460 : W := mkw 0x002403e000000000 0x000900f800000000 0x000003e000000000 0x400000f800000000

def z461 : W := mkw 0x0161229206042400 0x405848a481810900 0x01e000000e000000 0x0078000003800000

def z462 : W := mkw 0x2008d00c9088882b 0x080234032422220a 0xce01d05c8008c13d 0xf38074172002304f

def z463 : W := mkw 0x61fffbffd6cdbf3b 0x587ffefff5b36fce 0xffffffffffcfff3f 0xfffffffffff3ffcf

def z464 : W := mkw 0x22dff94c9dec992b 0x08b7fe53277b264a 0x11fdc31c1fc03800 0x047f70c707f00e00

def z465 : W := mkw 0x029a9c0009b2c001 0x80a6a700026cb000 0xea1e3c0001ffc003 0x3a878f00007ff000

def z466 : W := mkw 0x0020028002002400 0x400800a000800900 0x21e000800e000602 0x0878002003800180

def z467 : W := mkw 0x02fffbfaddac8003 0x00bffefeb76b2000 0xf9ffffffffc00000 0xfe7ffffffff00000

def z468 : W := mkw 0x22dffd489dfed10b 0x88b7ff52277fb442 0xfbfffc409fffc10f 0x3effff1027fff043

def z469 : W := mkw 0x02fbfe801fbee403 0xc0beffa007efb900 0xffffff801ffffe03 0x7fffffe007ffff80

def z470 : W := mkw 0x4120429712092e32 0x504810a5c4824b8c 0x9c01c39f10083e31 0xe70070e7c4020f8c

def z471 : W := mkw 0x0008d00010888003 0x0002340004222000 0xde1dd04091c8c13d 0xf78774102472304f

def z472 : W := mkw 0x0000000009200000 0x0000000002480000 0x030000001ff00003 0x00c0000007fc0000

def z473 : W := mkw 0x2004014c80401928 0x080100532010064a 0x5e1c035c91c0393d 0xd78700d724700e4f

def z474 : W := mkw 0xd02403e1224137d4 0x740900f848904df5 0x040003e3e0003ffc 0xc10000f8f8000fff

def z475 : W := mkw 0x020044001dbec003 0x80801100076fb000 0xeb023c001fffc003 0x3ac08f0007fff000

def z476 : W := mkw 0x0092000009200000 0x0024800002480000 0x11fc00001fc00000 0x047f000007f00000

def z477 : W := mkw 0x612cd3df92c9bf3b 0x584b34f7e4b26fce 0xde1dd3df91c8ff3d 0xf78774f7e4723fcf

def z478 : W := mkw 0x0000400410080822 0x0000100104020208 0xde01d35c9008f93d 0xf78074d724023e4f

def z479 : W := mkw 0x5249fc01349fc257 0x94927f004d27f095 0xee03fce3e03fc7ff 0xfb80ff38f80ff1ff

def z480 : W := mkw 0x1000040020124044 0x8400010008049011 0xce021c60e038c1fd 0xf3808718380e307f

def z481 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x5e1dc35c11c03901 0x578770d704700e40

def z482 : W := mkw 0x8000000002403580 0x6000000000900d60 0x0400000000003fc0 0x0100000000000ff0

def z483 : W := mkw 0x50416401341f4256 0x941059004d07d095 0xffe3fce3fe3fc7ff 0xfff8ff38ff8ff1ff

def z484 : W := mkw 0x41616697161f6e32 0xd05859a5c587db8c 0xffe3ff9f1e3ffe33 0xfff8ffe7c78fff8c

def z485 : W := mkw 0x6161629716cdbf3b 0x585858a5c5b36fce 0xbfe1e39f1fcfff3f 0xeff878e7c7f3ffcf

def z486 : W := mkw 0x43dbfc171dbfca33 0x90f6ff05c76ff28c 0xfbfffc1f1fffc033 0xbeffff07c7fff00c

def z487 : W := mkw 0xa09ed16c99e899ab 0x2827b45b267a266a 0xde1fd37c91f8f9fd 0xf787f4df247e3e7f

def z488 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0x7fffc3fc1ff03fc3 0x5ffff0ff07fc0ff0

def z489 : W := mkw 0x51616697361f6e76 0xd45859a5cd87db9d 0xbde3efbf7e3f3ef3 0xef78fbefdf8fcfbc

def z490 : W := mkw 0x52dbfc013dbfc257 0x94b6ff004f6ff095 0xfbfffc03ffffc03f 0xbeffff00fffff00f

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8023c0000000000 0x3a008f0000000000

def z492 : W := mkw 0x00dbb80000000000 0x0036ee0000000000 0x10fdc00000000000 0x043f700000000000

def z493 : W := mkw 0x80b202a00b603580 0x602c80a802d80d60 0x27e200a01ff03fc3 0x09f8802807fc0ff0

def z494 : W := mkw 0x0008d00010888003 0x0002340004222000 0x8001d0000008c000 0x2000740000023000

def z495 : W := mkw 0x63ffffdf9fffff3b 0xd8fffff7e7ffffce 0xffffffdf9fffff3f 0xfffffff7e7ffffcf

def z496 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffff1c00000000 0x3e3fffc700000000

def z497 : W := mkw 0xa02cd3ec92c8bdab 0x680b34fb24b22f6a 0xde1dd3fc91c8fffd 0xf78774ff24723fff

def z498 : W := mkw 0x202cd3cc92c8bd2b 0x480b34f324b22f4a 0xfffdd3dc9fc8ff3f 0xffff74f727f23fcf

def z499 : W := mkw 0x0092082040000000 0x0024820810000000 0x00020c2060000000 0x0000830818000000

def z500 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000408000013c 0xc10000102000004f

def z501 : W := mkw 0x209ed14c99e8992b 0x0827b453267a264a 0xffffd35c9ff8f93f 0xfffff4d727fe3e4f

def z502 : W := mkw 0x4100000502012e30 0x5040000140804b8c 0x0400000000003e30 0x0100000000000f8c

def z503 : W := mkw 0x5000040120134254 0x940001004804d095 0xea023ca3603fc6c3 0x3a808f28d80ff1b0

def z504 : W := mkw 0x610cd14d96cdbf3b 0x5843345365b36fce 0xdf1dd35c9fcfff3f 0xf7c774d727f3ffcf

def z505 : W := mkw 0x0000400010888003 0x0000100004222000 0x0200000011c8c001 0x0080000004723000

def z506 : W := mkw 0x43f36e971f3f6e32 0xd0fcdba5c7cfdb8c 0xbde3ef9f1e3f3e33 0xef78fbe7c78fcf8c

def z507 : W := mkw 0x00416400141e4002 0x8010590005079000 0xfbe3fc001e3fc003 0x3ef8ff00078ff000

def z508 : W := mkw 0x00ffbffac0124000 0x803feffeb0049000 0xfaffffffe03fc003 0xfebffffff80ff000

def z509 : W := mkw 0x50ffbffbe0134254 0x943feffef804d095 0xf8ffffffe00fc03c 0xfe3ffffff803f00f

def z510 : W := mkw 0x802403e002403580 0x600900f800900d60 0x5e1c03e011c03fc1 0x578700f804700ff0

def z511 : W := mkw 0x802403e002403580 0x600900f800900d60 0x6e0203e000303fc3 0x5b8080f8000c0ff0

def z512 : W := mkw 0x216df3de96ccbd2b 0x485b7cf7a5b32f4a 0xdffdd35c9fc8f93d 0xf7ff74d727f23e4f

def z513 : W := mkw 0x0000000000000000 0x0000000000000000 0x9801c31c00000000 0xe60070c700000000

def z514 : W := mkw 0x029adc001dbec003 0x80a6b700076fb000 0x431e1c001fffc003 0x10c7870007fff000

def z515 : W := mkw 0x0096014009601100 0x0025805002580440 0x7ffe03401ff03903 0x5fff80d007fc0e40

def z516 : W := mkw 0x0008d400109ac003 0x800235000426b000 0xfa1ffc0011ffc003 0x3e87ff00047ff000

def z517 : W := mkw 0x02fbfe921dbec003 0x80beffa4876fb000 0xfbffff9f1fffc003 0xfeffffe7c7fff000

def z518 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0x11fdc31c1fc03800 0x047f70c707f00e00

def z519 : W := mkw 0x0020029200000000 0x000800a480000000 0x0000039f00000000 0xc00000e7c0000000

def z520 : W := mkw 0x200c914c80401928 0x080324532010064a 0xdc1dd35c8000393c 0xf70774d720000e4f

def z521 : W := mkw 0xd0b607e12b7377d4 0xf42d81f84adcddf5 0x7ffe03e01fffffff 0x5fff80f807ffffff

def z522 : W := mkw 0xa0b603ec8b603da8 0x682d80fb22d80f6a 0x7ffe03fc9ff03fff 0xdfff80ff27fc0fff

def z523 : W := mkw 0x4000000100010210 0x1000000040004084 0x0400008300000630 0xc1000020c000018c

def z524 : W := mkw 0x5000040120134254 0x940001004804d095 0xce003c43e00fc13d 0xf3800f10f803f04f

def z525 : W := mkw 0x10ffbffae0124044 0x843feffeb8049011 0xfaffffffe030c1cc 0xfebffffff80c3073

def z526 : W := mkw 0x5000000120010254 0x1400000048004095 0x000000a3600006c0 0x00000028d80001b0

def z527 : W := mkw 0x5000040120134254 0x940001004804d095 0xa0023ca3e03fc6fe 0xa8008f28f80ff1bf

def z528 : W := mkw 0xc1f322b30f252690 0x707cc8acc3c949a4 0x21e220a30e3706c2 0x08788828c38dc1b0

def z529 : W := mkw 0x41fffbffd40d0a32 0x107ffefff503428c 0xf8ffffffe00f0030 0xfe3ffffff803c00c

def z530 : W := mkw 0x7008d40db09bca7f 0x9c0235036c26f29f 0xee03fcffe03fc7ff 0xfb80ff3ff80ff1ff

def z531 : W := mkw 0x00be9be8c0000000 0x002fa6fa30000000 0x78fe1fe0e0000000 0x5e3f87f838000000

def z532 : W := mkw 0x2004014c80401928 0x080100532010064a 0xce00135c8008f93d 0xf38004d720023e4f

def z533 : W := mkw 0x5000040120134254 0x940001004804d095 0x00000000003706c2 0x00000000000dc1b0

def z534 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0x0001c01c00000000 0x0000700700000000

def z535 : W := mkw 0x4020028102012610 0x500800a040804984 0xbde023831e0f3e33 0xef7808e0c783cf8c

def z536 : W := mkw 0x02fbfeb25dbec003 0x80beffac976fb000 0xfbfffca37fffc003 0x3effff28dffff000

def z537 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xd81dd35c91c03800 0xf60774d724700e00

def z538 : W := mkw 0xd0b607e12b7377d4 0xf42d81f84adcddf5 0x7ffe2fe37ff73fc3 0x5fff8bf8dffdcff0

def z539 : W := mkw 0x000cd14c90080822 0x0003345324020208 0xdc1dd35c90083831 0xf70774d724020e0c

def z540 : W := mkw 0x0049b80000000000 0x00126e0000000000 0x8001fc0000000000 0x20007f0000000000

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000000003007c3 0x01800000000c01f0

def z542 : W := mkw 0x0000040000124000 0x8000010000049000 0x20022c0000370002 0x08008b00000dc000

def z543 : W := mkw 0x002403c002403500 0x400900f000900d40 0x7ffc03c01fc03f03 0x5fff00f007f00fc0

def z544 : W := mkw 0xf0bed7edbbfbffff 0xfc2fb5fb6efeffff 0xffffffffffffffff 0xffffffffffffffff

def z545 : W := mkw 0x02d32c000d364000 0x80b4cb00034d9000 0x7bfe2c001ff70003 0x1eff8b0007fdc000

def z546 : W := mkw 0x0000000000401100 0x0000000000100440 0x0600000011c03901 0x0180000004700e40

def z547 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xa1e1e09f0e0f0632 0xa8787827c383c18c

def z548 : W := mkw 0x430044051fbfee33 0xd0c0110147effb8c 0x070000001ffffe33 0x01c0000007ffff8c

def z549 : W := mkw 0xc1b603f70b613fb0 0x706d80fdc2d84fec 0x7ffe03ff1ff03ff3 0xdfff80ffc7fc0ffc

def z550 : W := mkw 0x0000040000124000 0x8000010000049000 0xee023ce0003fc7c3 0x7b808f38000ff1f0

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00004000000101 0x5380001000000040

def z552 : W := mkw 0x200cd14c9088882b 0x080334532422220a 0xd81dd35c8008c03c 0xf60774d72002300f

def z553 : W := mkw 0x0008900880000000 0x0002240220000000 0x8001d01c80000000 0xa000740720000000

def z554 : W := mkw 0x6100400516cdbf3b 0x5840100145b36fce 0x070000001fcfff3f 0x01c0000007f3ffcf

def z555 : W := mkw 0x0000000400000820 0x0000000100000208 0x0400031c00003830 0xc10000c700000e0c

def z556 : W := mkw 0x529a9c0129b3c255 0x94a6a7004a6cf095 0xee1e3ce3e1ffc7ff 0xfb878f38f87ff1ff

def z557 : W := mkw 0xd2ffffe13ffff7d7 0xf4bffff84ffffdf5 0xffffffe3ffffffff 0xfffffff8ffffffff

def z558 : W := mkw 0xc1f763f71f6d3fb2 0x707dd8fdc7db4fec 0xbdfde39f1fcf3e33 0xef7f78e7c7f3cf8c

def z559 : W := mkw 0x00b202800b202400 0x402c80a002c80900 0x7ffe03801ff03e03 0x5fff80e007fc0f80

def z560 : W := mkw 0x03fbfe961fbeec23 0xc0feffa587efbb08 0xfbffff1c1ffff803 0x3effffc707fffe00

def z561 : W := mkw 0x2008d00c9088882b 0x080234032422220a 0x9c01d31c9008f83d 0xe70074c724023e0f

def z562 : W := mkw 0x5092040129334254 0x942481004a4cd095 0xfffe3ce3ffffc7ff 0xffff8f38fffff1ff

def z563 : W := mkw 0x02f32eb24d364000 0x80bccbac934d9000 0x21e22ca36e370002 0x08788b28db8dc000

def z564 : W := mkw 0x000cd14010c89103 0x0003345004322440 0xde1dd34011c8f901 0x778774d004723e40

def z565 : W := mkw 0x00dbf800140c0002 0x0036fe0005030000 0xf9fffc001e0f0003 0x3e7fff000783c000

def z566 : W := mkw 0x0092000009200000 0x0024800002480000 0x7ffe00e01ff007c3 0x5fff803807fc01f0

def z567 : W := mkw 0x4000000100010210 0x1000000040004084 0x80002003000f0030 0xa0000800c003c00c

def z568 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0x00e0000000000000 0x0038000000000000

def z569 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0xf9fffc001fc00000 0x3e7fff0007f00000

def z570 : W := mkw 0x00616280160c2402 0x401858a005830900 0xbde1e3801e0f3e03 0x6f7878e00783cf80

def z571 : W := mkw 0x2000400410c8992b 0x080010010432264a 0xce00104091c8f93d 0xf380041024723e4f

def z572 : W := mkw 0x029e9d68c9b2c001 0x80a7a75a326cb000 0x421e1c60e1f0c000 0x10878718387c3000

def z573 : W := mkw 0x809e9968c9601180 0x2027a65a32580460 0x421e1c60e1f001c0 0x10878718387c0070

def z574 : W := mkw 0x4000000100010210 0x1000000040004084 0xee0030c3800fc73f 0xfb800c30e003f1cf

def z575 : W := mkw 0x01416016140c0822 0x0050580585030208 0x0001c01c00000000 0x0000700700000000

def z576 : W := mkw 0x52fffffbfdbfc257 0x94bffffeff6ff095 0xffffffffffffc7ff 0xfffffffffffff1ff

def z577 : W := mkw 0x000c914880000000 0x0003245220000000 0x101dc31c00000000 0x040770c700000000

def z578 : W := mkw 0x80b607e00b727580 0xe02d81f802dc9d60 0xfffe3fe01fffffc3 0x7fff8ff807fffff0

def z579 : W := mkw 0x50ffbffbe0134254 0x943feffef804d095 0xf8ffffffe03706c2 0xfe3ffffff80dc1b0

def z580 : W := mkw 0x51416417341f4a76 0x94505905cd07d29d 0xee03fcffe03fc7ff 0xfb80ff3ff80ff1ff

def z581 : W := mkw 0x809601600b603580 0x6025805802d80d60 0x471e00601ff03fc3 0x11c7801807fc0ff0

def z582 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0xb9e1e39f1e003800 0xee7878e7c7800e00

def z583 : W := mkw 0x2008d00c9088882b 0x080234032422220a 0x0001c01c00000000 0x0000700700000000

def z584 : W := mkw 0x4161229706052e30 0x505848a5c1814b8c 0x25e0239f0e073e32 0xc97808e7c381cf8c

def z585 : W := mkw 0x000cd14890888003 0x0003345224222000 0xda1dd35c91c8c001 0xf68774d724723000

def z586 : W := mkw 0x51fffffff61f6e76 0xd47ffffffd87db9d 0xfffffffffe3fffff 0xffffffffff8fffff

def z587 : W := mkw 0x41616293160d2612 0x505858a4c5834984 0xb9e1e0831e0f0603 0x2e787820c783c180

def z588 : W := mkw 0xa00040041be8bdab 0x6800100106fa2f6a 0x070000001ff8ffff 0x01c0000007fe3fff

def z589 : W := mkw 0x00040168c0000000 0x0001005a30000000 0x00000060e0000000 0x0000001838000000

def z590 : W := mkw 0x5161269326176654 0xd45849a4c985d995 0xefe23ce3ee3fc7ff 0xfbf88f38fb8ff1ff

def z591 : W := mkw 0xc0b603e10b613790 0x702d80f842d84de4 0xfffe23e31fff3ff3 0xffff88f8c7ffcffc

def z592 : W := mkw 0x00f723f200000000 0x003dc8fc80000000 0xf8ffe3ff00000000 0xfe3ff8ffc0000000

def z593 : W := mkw 0x41fbfa97160d2e32 0x507efea5c5834b8c 0xfdffff9f1e0f3e33 0xff7fffe7c783cf8c

def z594 : W := mkw 0x216df3de96ccbd2b 0x485b7cf7a5b32f4a 0x11fdc31c1fc03800 0x047f70c707f00e00

def z595 : W := mkw 0x00fbbab240000000 0x003eeeac90000000 0xf8fffca360000000 0x3e3fff28d8000000

def z596 : W := mkw 0x41f362971f2d2e32 0x507cd8a5c7cb4b8c 0xffffe39f1fff3e33 0xfffff8e7c7ffcf8c

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8002000000f0003 0x2a0008000003c000

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x2c00008000000603 0x4b00002000000180

def z599 : W := mkw 0x70fffffff0dbdb7f 0x9c3ffffffc36f6df 0xfefffffff1ffffff 0xffbffffffc7fffff

def z600 : W := mkw 0x41f32ab346052610 0x507ccaacd1814984 0x21e22ca36e070602 0x08788b28db81c180

def z601 : W := mkw 0x00dfb94880000000 0x0037ee5220000000 0xf8ffff5c80000000 0xfe3fffd720000000

def z602 : W := mkw 0x2004414c9048192a 0x080110532412064a 0x9c01c35c9008393d 0xe70070d724020e4f

def z603 : W := mkw 0x5161269326176654 0xd45849a4c985d995 0x21e22ca36e3706c2 0x08788b28db8dc1b0

def z604 : W := mkw 0x8000000009601180 0x2000000002580460 0x0200000001f001c0 0x00800000007c0070

def z605 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c00000000080031 0xe30000000002000c

def z606 : W := mkw 0x43ffffffdfbfee33 0xd0fffffff7effb8c 0xfffffffffffffe33 0xffffffffffffff8c

def z607 : W := mkw 0x416df3df960d2e32 0x505b7cf7e5834b8c 0xfdfdf3df9e0f3e33 0xff7f7cf7e783cf8c

def z608 : W := mkw 0x0096016000000000 0x0025805800000000 0x401e006000000000 0x1007801800000000

def z609 : W := mkw 0x1000040020124044 0x8400010008049011 0x00020c20603000c0 0x00008308180c0030

def z610 : W := mkw 0xa0bed3ec9be8bdab 0x682fb4fb26fa2f6a 0x7fffc3fc1ff03fc3 0x5ffff0ff07fc0ff0

def z611 : W := mkw 0x0249fc1ad49ec003 0x80927f06b527b000 0x8001fc1fe00fc000 0xa0007f07f803f000

def z612 : W := mkw 0x0000000000000000 0x0000000000000000 0x40021c60e0000000 0x1000871838000000

def z613 : W := mkw 0x01004004160c2c22 0x4040100105830b08 0x010000001e003800 0x0040000007800e00

def z614 : W := mkw 0x0249fc001dbec003 0x80927f00076fb000 0x8301fc001fffc003 0x20c07f0007fff000

def z615 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x50ffdf7ce0000000 0x143ff7df38000000

def z616 : W := mkw 0x5000040120134254 0x940001004804d095 0x26022ca3603fc7ff 0x09808b28d80ff1ff

def z617 : W := mkw 0x03fbfa961facac23 0x40fefea587eb2b08 0x11fdc31c1fc03800 0x047f70c707f00e00

def z618 : W := mkw 0x0000040000124000 0x8000010000049000 0xea023ce3e03fc003 0xfa808f38f80ff000

def z619 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x25e203e00e303fc2 0x497880f8038c0ff0

def z620 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x15fc03e01fc03fc0 0x457f00f807f00ff0

def z621 : W := mkw 0x80b202a00b202480 0x602c80a802c80920 0x01e000000e000000 0x0078000003800000

def z622 : W := mkw 0x0004414410481922 0x0001105104120648 0xde1dc35c11c83931 0xf78770d704720e4c

def z623 : W := mkw 0x4061229300010210 0x101848a4c0004084 0xbce1e39f000f0633 0xef3878e7c003c18c

def z624 : W := mkw 0x51616697361f6e76 0xd45859a5cd87db9d 0xbfe1e39f1e3fffff 0xeff878e7c78fffff

def z625 : W := mkw 0x41ffbbffc2012e30 0x507feefff0804b8c 0xfcffffffe0003e30 0xff3ffffff8000f8c

def z626 : W := mkw 0x829e9d6009f2d181 0xa0a7a758027cb460 0x421e1c6001f0c1c0 0x10878718007c3070

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000000008c13d 0x018000000002304f

def z628 : W := mkw 0x00b603e000000000 0x002d80f800000000 0x10fc030000000000 0x043f00c000000000

def z629 : W := mkw 0x1000040020124044 0x8400010008049011 0x00001c00e000c00c 0x0000070038003003

def z630 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xda1dd31c11c8f801 0x368774c704723e00

def z631 : W := mkw 0xa09e916889e09189 0x2827a45a22782462 0x421e106081f0c1cc 0x10878418207c3073

def z632 : W := mkw 0x0008900000000000 0x0002240000000000 0xd81dd00000000000 0x3607740000000000

def z633 : W := mkw 0x50dbbc0120134254 0x9436ef004804d095 0xfefffce3e03fc7ff 0xffbfff38f80ff1ff

def z634 : W := mkw 0x80f72bf24b603580 0x603dcafc92d80d60 0x7ffe2fe37ff03fc3 0x5fff8bf8dffc0ff0

def z635 : W := mkw 0x82fffbe01fecb583 0x60bffef807fb2d60 0x7fffc3e01ff03fc3 0x5ffff0f807fc0ff0

def z636 : W := mkw 0x20fffbfed088882b 0x083ffeffb422220a 0xf8ffffffe008c03c 0xfe3ffffff802300f

def z637 : W := mkw 0x700cd54db0dbdb7f 0x9c0335536c36f6df 0xde1dff5ff1cff93d 0xf7877fd7fc73fe4f

def z638 : W := mkw 0x0041200000000000 0x0010480000000000 0xb8e1e00000000000 0x2e38780000000000

def z639 : W := mkw 0x50f32eb360134254 0x943ccbacd804d095 0xeee23ce3e03fc7ff 0xfbb88f38f80ff1ff

def z640 : W := mkw 0xa0bed3ec9be8bdab 0x682fb4fb26fa2f6a 0x11fdc31c1fc03800 0x047f70c707f00e00

def z641 : W := mkw 0x616563df964d3f3a 0x585958f7e5934fce 0xbde1e3df9e0f3f3f 0xef7878f7e783cfcf

def z642 : W := mkw 0x300c9548a0d2d14d 0x8c0325522834b453 0x421e1c60e1f0c1cc 0x10878718387c3073

def z643 : W := mkw 0x5004054120535354 0x940101504814d4d5 0xfe1e3fe3f1ffffff 0xff878ff8fc7fffff

def z644 : W := mkw 0xc10040051f6d3fb2 0x7040100147db4fec 0x070000001fff3ff3 0x01c0000007ffcffc

def z645 : W := mkw 0x0061229200000000 0x001848a480000000 0x20e0208300000000 0x08380820c0000000

def z646 : W := mkw 0x80be9be8cb603580 0x602fa6fa32d80d60 0x7ffe1fe0fff03fc3 0x5fff87f83ffc0ff0

def z647 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x63fe00e00ff007c2 0x18ff803803fc01f0

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x5a1c000011c00001 0x1687000004700000

def z649 : W := mkw 0x029a9c0009b2c001 0x80a6a700026cb000 0x7bfe1c001ff0c003 0x1eff870007fc3000

def z650 : W := mkw 0x50f32eb360134254 0x943ccbacd804d095 0x20e22ca3603706c2 0x08388b28d80dc1b0

def z651 : W := mkw 0x02ffbffac9b2c001 0x80bfeffeb26cb000 0xfaffffffe1f0c000 0xfebffffff87c3000

def z652 : W := mkw 0x1000040020124044 0x8400010008049011 0x020000000030c1cc 0x00800000000c3073

def z653 : W := mkw 0x700cd54db0dbdb7f 0x9c0335536c36f6df 0xde1dd35c91ffffff 0xf78774d7247fffff

def z654 : W := mkw 0x82f32ea00f366480 0xe0bccba803cd9920 0x21e22ca00e3706c2 0x08788b28038dc1b0

def z655 : W := mkw 0x00b202a000000000 0x002c80a800000000 0x20e200a000000000 0x0838802800000000

def z656 : W := mkw 0x82fffbe01fecb583 0x60bffef807fb2d60 0x11fdc3001fc03800 0x047f70c007f00e00

def z657 : W := mkw 0x5000040120134254 0x940001004804d095 0xac022ca3603f06f3 0xeb008b28d80fc1bc

def z658 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xc21ffc0001ffc000 0x3087ff00007ff000

def z659 : W := mkw 0x2049f81ed088882b 0x08127e07b422220a 0x8001fc1fe008c03c 0xa0007f07f802300f

def z660 : W := mkw 0x2008d00410c8992b 0x080234010432264a 0xde1dd00011c8f93d 0x3787740004723e4f

def z661 : W := mkw 0x41616297140d0a32 0x105858a5c503428c 0xb8e1e39f000f0030 0xee3878e7c003c00c

def z662 : W := mkw 0x4120029702012e30 0x504800a5c0804b8c 0x3de0039f1e003e33 0xcf7800e7c7800f8c

def z663 : W := mkw 0x2004014c80401928 0x080100532010064a 0x0000031c00003800 0x000000c700000e00

def z664 : W := mkw 0x82fbfea01fbee483 0xe0beffa807efb920 0xfbfffca01fffc6c3 0x3effff2807fff1b0

def z665 : W := mkw 0x206df3de90c8992b 0x081b7cf7a432264a 0xfefdf3df91c8f93d 0xffbf7cf7e4723e4f

def z666 : W := mkw 0x5249fc01349fc257 0x94927f004d27f095 0x8001fc03e00fc03c 0xa0007f00f803f00f

def z667 : W := mkw 0x002403fac0000000 0x000900feb0000000 0x0000031c00000000 0x000000c700000000

def z668 : W := mkw 0x802002800b603580 0x600800a002d80d60 0x3fe003801ff03fc3 0x4ff800e007fc0ff0

def z669 : W := mkw 0x4369fe97169fee33 0xd0da7fa5c5a7fb8c 0xbde1ff9f1e0ffe33 0xef787fe7c783ff8c

def z670 : W := mkw 0x416563ffd60d2e32 0x505958fff5834b8c 0xbde1e3fffe0f3e33 0xef7878ffff83cf8c

def z671 : W := mkw 0x436166971fbfee33 0xd0d859a5c7effb8c 0xbfe1e39f1ffffe33 0xeff878e7c7ffff8c

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x39e000001e000003 0x0e78000007800000

def z673 : W := mkw 0x4100000106052610 0x5040000041814984 0x010000000e070602 0x004000000381c180

def z674 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x53ffdc001ff0c000 0x14fff70007fc3000

def z675 : W := mkw 0x020004000d364000 0x80800100034d9000 0x010000000e370002 0x00400000038dc000

def z676 : W := mkw 0x800000000b603580 0x6000000002d80d60 0x010000001fc03800 0x0040000007f00e00

def z677 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7bfe03001ff03803 0x1eff80c007fc0e00

def z678 : W := mkw 0x2000400410c8992b 0x080010010432264a 0x9e01c31c11c8f93d 0xe78070c704723e4f

def z679 : W := mkw 0x20ffbbfec0401928 0x083feeffb010064a 0xfcffffffe000393c 0xff3ffffff8000e4f

def z680 : W := mkw 0x520044013dbfc257 0x948011004f6ff095 0x070000001fffc7ff 0x01c0000007fff1ff

def z681 : W := mkw 0x5000040120134254 0x940001004804d095 0xc2023c63e03fc1fc 0xb0808f18f80ff07f

def z682 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x461e03e001f03fc0 0x518780f8007c0ff0

def z683 : W := mkw 0x700cd14db0c99b7f 0x1c0334536c3266df 0xde1dd3fff1c8fffd 0xf78774fffc723fff

def z684 : W := mkw 0x800000000b202480 0x6000000002c80920 0x010000000e3006c2 0x00400000038c01b0

def z685 : W := mkw 0x4141201304050210 0x10504804c1014084 0x0000200300070000 0x00000800c001c000

def z686 : W := mkw 0x4161229306052610 0x505848a4c1814984 0xade020830e0f0633 0xeb780820c383c18c

def z687 : W := mkw 0x00b603e000000000 0x002d80f800000000 0xf8fe3fe3e0000000 0xfe3f8ff8f8000000

def z688 : W := mkw 0x2000000400401928 0x080000010010064a 0x040000000000393c 0x0100000000000e4f

def z689 : W := mkw 0x802403e002403580 0x600900f800900d60 0x0000030000003800 0x000000c000000e00

def z690 : W := mkw 0x02fffffaddbec003 0x80bffffeb76fb000 0xfbffff1c1fffc003 0x3effffc707fff000

def z691 : W := mkw 0x0041200004040000 0x0010480001010000 0x21e020000e070002 0x087808000381c000

def z692 : W := mkw 0x009ad00019a88003 0x0026b400066a2000 0xfbffd0001ff8c003 0x3efff40007fe3000

def z693 : W := mkw 0x72dffd4dbdffdb7f 0x9cb7ff536f7ff6df 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x4100001700010a30 0x10400005c000428c 0x0000001f00000030 0x80000007c000000c

def z695 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x5ffc03401fc03901 0x57ff00d007f00e40

def z696 : W := mkw 0x1000040020124044 0x8400010008049011 0xea023c60e03fc1cf 0x3a808f18380ff073

def z697 : W := mkw 0x2008d00c9088882b 0x080234032422220a 0xda1dd01c91c8c03d 0xb68774072472300f

def z698 : W := mkw 0x0020428412082c22 0x400810a104820b08 0xbde1c39c1e083e33 0xef7870e707820f8c

def z699 : W := mkw 0x209e9968c0c09109 0x0827a65a30302442 0x421e1c60e1c0c10c 0x1087871838703043

def z700 : W := mkw 0x20fffbfed0c8992b 0x083ffeffb432264a 0xdefdd35c91c8f93d 0xf7bf74d724723e4f

def z701 : W := mkw 0x129a9c0029b2c045 0x84a6a7000a6cb011 0x421e1c60e1f0c1cc 0x10878718387c3073

def z702 : W := mkw 0x2000400410c8992b 0x080010010432264a 0x0000000011c03800 0x0000000004700e00

def z703 : W := mkw 0x41416017160d2e32 0x50505805c5834b8c 0x8501e01f1e0f3e33 0xa1407807c783cf8c

def z704 : W := mkw 0x7008d40db09bca7f 0x9c0235036c26f29f 0x8001fc1fe00fc03c 0xa0007f07f803f00f

def z705 : W := mkw 0x82dbfc001ffef583 0xe0b6ff0007ffbd60 0xfffffc001fffffc3 0x3fffff0007fffff0

def z706 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x9c1dc31c11c83831 0xe70770c704720e0c

def z707 : W := mkw 0x806dbbfac2403580 0x601b6efeb0900d60 0x8401ffffe0003fc0 0xe1007ffff8000ff0

def z708 : W := mkw 0x22d72d4c8d765928 0x88b5cb53235d964a 0x25e22f5c8e37393e 0xc9788bd7238dce4f

def z709 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0x9801ff1fe0000000 0xe6007fc7f8000000

def z710 : W := mkw 0x80b603f20b603580 0x602d80fc82d80d60 0x7ffe03ff1ff03fc3 0xdfff80ffc7fc0ff0

def z711 : W := mkw 0x419ed96dd60d2e32 0x5067b65b75834b8c 0x451e1c60fe0f3e33 0x114787183f83cf8c

def z712 : W := mkw 0x00fbbab240000000 0x003eeeac90000000 0xf8ffffbf60000000 0xfe3fffefd8000000

def z713 : W := mkw 0x50004405301b4a76 0x940011014c06d29d 0x06000000103fffff 0x01800000040fffff

def z714 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc60ffffc003 0x3effff183ffff000

def z715 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1dd35c91f8ffff 0xf78774d7247e3fff

def z716 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x90fdffffe0000000 0xe43f7ffff8000000

def z717 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xb1fffc001fffc002 0x2c7fff0007fff000

def z718 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x11e1e31f1e073800 0x047878c7c781ce00

def z719 : W := mkw 0xc12403f702413fb0 0x704900fdc0904fec 0x0400039f00003e30 0xc10000e7c0000f8c

def z720 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0x31ffefbf7ff03ec2 0x0c7ffbefdffc0fb0

def z721 : W := mkw 0x80b202a00b202480 0x602c80a802c80920 0x7ffe03a01ff03ec3 0x5fff80e807fc0fb0

def z722 : W := mkw 0xc1d761771d6d1bb2 0x3075d85dc75b46ec 0xc21fe07f01ff01f0 0xb087f81fc07fc07c

def z723 : W := mkw 0x00fbbabac0000000 0x003eeeaeb0000000 0xf8fffcbfe0000000 0xbe3fff2ff8000000

def z724 : W := mkw 0x4161229306052610 0x505848a4c1814984 0xbde1e39f1e073e03 0xef7878e7c781cf80

def z725 : W := mkw 0x2004414410c8992b 0x080110510432264a 0xde1dc35c11c8f93d 0xf78770d704723e4f

def z726 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xa5e1e39f0e0f3e32 0xe97878e7c383cf8c

def z727 : W := mkw 0x22dbfc0c9dbec82b 0x88b6ff03276fb20a 0xffffff1c9ffff83f 0xffffffc727fffe0f

def z728 : W := mkw 0x02dbfc1addbec003 0x80b6ff06b76fb000 0xfbfffcffffffc003 0xfeffff3ffffff000

def z729 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1fd3fc91c8f93d 0xff87f4ff24723e4f

def z730 : W := mkw 0x70004405309bca7f 0x9c0011014c26f29f 0x06000000003fc7ff 0x01800000000ff1ff

def z731 : W := mkw 0x8049b81acb603580 0x60126e06b2d80d60 0x8701fc1ffff03fc3 0xa1c07f07fffc0ff0

def z732 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfbfffc207fffc0c3 0x3effff081ffff030

def z733 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0x8001fc1fe008c03c 0xa0007f07f802300f

def z734 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfaffffffe03001c0 0xfebffffff80c0070

def z735 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbfe1e39f1e3f3ff3 0xeff878e7c78fcffc

def z736 : W := mkw 0x02dbbc000d364000 0x80b6ef00034d9000 0xfbfffc001ff70003 0x3effff0007fdc000

def z737 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x101dc31c11c8f83c 0x040770c704723e0f

def z738 : W := mkw 0x02dbfc041dbec823 0x80b6ff01076fb208 0xfbfffc1c1fffc033 0xbeffff0707fff00c

def z739 : W := mkw 0x22dbfc089dbec00b 0x88b6ff02276fb002 0xfbfffc009fffc00f 0x3effff0027fff003

def z740 : W := mkw 0xc12403ffc2413fb0 0x704900fff0904fec 0x040003ffe0003ff0 0xc10000fff8000ffc

def z741 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7bfe03a01ff03ec3 0x1eff80e807fc0fb0

def z742 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfbfffce3ffffc1cf 0xfeffff38fffff073

def z743 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x11e1c31c1e0f3830 0x047870c70783ce0c

def z744 : W := mkw 0x826dffe016def583 0xe09b7ff805b7bd60 0x8401ffe0000fffc0 0x61007ff80003fff0

def z745 : W := mkw 0x4020428512092e32 0x500810a144824b8c 0xbde1e39f1e0f3e33 0xef7878e7c783cf8c

def z746 : W := mkw 0xd0b607e12b7377d4 0xf42d81f84adcddf5 0x91fc3f03ffcff83c 0xa47f0fc0fff3fe0f

def z747 : W := mkw 0x0249f4001dbec003 0x80927d00076fb000 0xfbfdf0001fffc003 0x3eff7c0007fff000

def z748 : W := mkw 0xc02403e102413790 0x700900f840904de4 0x040003e300003ff0 0xc10000f8c0000ffc

def z749 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffffffe00f0003 0xfe3ffffff803c000

def z750 : W := mkw 0x616db3db86c5b719 0x585b6cf6e1b16dc6 0x63fc30c38fc7c70e 0x18ff0c30e3f1f1c3

def z751 : W := mkw 0xb09e9568a9f2d1cd 0xac27a55a2a7cb473 0x421e1c60e1f0c1cc 0x10878718387c3073

def z752 : W := mkw 0x000c914880000000 0x0003245220000000 0xd81dff5fe0000000 0xf6077fd7f8000000

def z753 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x161dc35c91c8f93d 0xc58770d724723e4f

def z754 : W := mkw 0x022447faddbec003 0x808911feb76fb000 0x030003ffffffc003 0xc0c000fffffff000

def z755 : W := mkw 0x02dbfc1addbec003 0x80b6ff06b76fb000 0xfbfffc1c1fffc003 0x3effff0707fff000

def z756 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe13e09ff0ffcf 0x5fff84f827fc3ff3

def z757 : W := mkw 0x20f36ab650c8992b 0x083cdaad9432264a 0x26e22ca371c8f93d 0x09b88b28dc723e4f

def z758 : W := mkw 0x0249fc00149ec003 0x80927f000527b000 0xfbfdfc001fcfc003 0x3eff7f0007f3f000

def z759 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfaffffffe008c001 0xfebffffff8023000

def z760 : W := mkw 0x00ffbbfac4040000 0x003feefeb1010000 0xf9ffffffee070002 0xfe7ffffffb81c000

def z761 : W := mkw 0x80ffbbfac9200080 0x203feefeb2480020 0xf8ffffffe03000c0 0xfe3ffffff80c0030

def z762 : W := mkw 0x0092040009324000 0x80248100024c9000 0x7bfe2c001ff70003 0x1eff8b0007fdc000

def z763 : W := mkw 0x41616a97560d2e32 0x50585aa5d5834b8c 0xbde1ef9f7e0f3e33 0xef787be7df83cf8c

def z764 : W := mkw 0x80ffbbfac2403580 0x603feefeb0900d60 0xfefffffff1c03fc1 0xffbffffffc700ff0

def z765 : W := mkw 0x004db97ac0000000 0x00136e5eb0000000 0x8001fc7fe0000000 0xa0007f1ff8000000

def z766 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x10fdef1f60000000 0x043f7bc7d8000000

def z767 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1ffffff1f8ffff 0xff87fffffc7e3fff

def z768 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xc801fc5fe0000000 0xf2007f17f8000000

def z769 : W := mkw 0x4161229706052e30 0x505848a5c1814b8c 0xbde1e39f0e073e32 0xef7878e7c381cf8c

def z770 : W := mkw 0xd0f32eb36b3366d4 0xf43ccbacdaccd9b5 0x21e22ca36e3706c2 0x08788b28db8dc1b0

def z771 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfdffffffffc03fc0 0xff7ffffffff00ff0

def z772 : W := mkw 0x22dbfc0c9dbec82b 0x88b6ff03276fb20a 0xfbfffc1c1fffc003 0x3effff0707fff000

def z773 : W := mkw 0x00f723f200000000 0x003dc8fc80000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z774 : W := mkw 0x00616292160c2402 0x401858a485830900 0xbde1e39f1e0f3e03 0xef7878e7c783cf80

def z775 : W := mkw 0x0008900880000000 0x0002240220000000 0x8001fc1fe0000000 0xa0007f07f8000000

def z776 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0xbde1e39c1e0f3e03 0x6f7878e70783cf80

def z777 : W := mkw 0x412403d702413f30 0x504900f5c0904fcc 0x040003df00003f30 0xc10000f7c0000fcc

def z778 : W := mkw 0x700cd54db0dbdb7f 0x9c0335536c36f6df 0x301fefbf71f73ec2 0x0c07fbefdc7dcfb0

def z779 : W := mkw 0x00be93e880000000 0x002fa4fa20000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z780 : W := mkw 0x80ffbbfacb202480 0x603feefeb2c80920 0xffffffffee3007c3 0xfffffffffb8c01f0

def z781 : W := mkw 0xa0bad2ac9ba8acab 0x682eb4ab26ea2b2a 0xa1e3d0bc8e38c6fe 0xa878f42f238e31bf

def z782 : W := mkw 0x20ffbbfac0c09109 0x083feefeb0302442 0xfeffffffe1c8c13d 0xffbffffff872304f

def z783 : W := mkw 0x00ffbbfac0401100 0x003feefeb0100440 0xfcffffffe0003900 0xff3ffffff8000e40

def z784 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfcffffffe0080031 0xff3ffffff802000c

def z785 : W := mkw 0x229e9d4889f2d109 0x88a7a752227cb442 0x421e1c0001f0c000 0x10878700007c3000

def z786 : W := mkw 0x02dbfc121dbec003 0x80b6ff04876fb000 0xfbfffc1f1fffc003 0xbeffff07c7fff000

def z787 : W := mkw 0x006dbbfac0000000 0x001b6efeb0000000 0xb8e1ffffe0000000 0xee387ffff8000000

def z788 : W := mkw 0x00ffbbfac0401100 0x003feefeb0100440 0xf8fffffff1c03800 0xfe3ffffffc700e00

def z789 : W := mkw 0x00d360001d2c0002 0x0034d800074b0000 0xb9fde0001fcf0003 0x2e7f780007f3c000

def z790 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x561dd35c91c0f93c 0xd58774d724703e4f

def z791 : W := mkw 0xf0b647e53bfbffff 0xfc2d91f94efeffff 0x7ffe03e01fffffff 0x5fff80f807ffffff

def z792 : W := mkw 0x0069ba9ac0000000 0x001a6ea6b0000000 0x90e1ff1fe0000000 0xa4387fc7f8000000

def z793 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x37fe03a01ff03fc3 0x0dff80e807fc0ff0

def z794 : W := mkw 0x00dbf0001dac8003 0x0036fc00076b2000 0xfbfff0001fffc003 0x3efffc0007fff000

def z795 : W := mkw 0x4061229302012610 0x501848a4c0804984 0xbde1e39f1e0f3e33 0xef7878e7c783cf8c

def z796 : W := mkw 0x5000040120134254 0x940001004804d095 0xffe23ce3fe3fc7ff 0xfff88f38ff8ff1ff

def z797 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1e3ff1e0f3ff3 0xef7878ffc783cffc

def z798 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xa801fc9fe0000000 0xea007f27f8000000

def z799 : W := mkw 0x80b603e88b603580 0x602d80fa22d80d60 0x7ffe03fc9ff03fc3 0xdfff80ff27fc0ff0

def z800 : W := mkw 0x80b603facb603580 0x602d80feb2d80d60 0x7ffe03fc1ff03fc3 0x5fff80ff07fc0ff0

def z801 : W := mkw 0x00612a9240000000 0x00184aa490000000 0xb8e1ef9f60000000 0xee387be7d8000000

def z802 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x11e1c31c1e073e02 0x047870c70781cf80

def z803 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xf9fffc001fcfc000 0x3e7fff0007f3f000

def z804 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffffbf60000000 0x3e3fffefd8000000

def z805 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe3e39f1e3f3e33 0xfff8f8e7c78fcf8c

def z806 : W := mkw 0xd1f326b32f3766d4 0xf47cc9accbcdd9b5 0x21e22ca36e3706c2 0x08788b28db8dc1b0

def z807 : W := mkw 0x52dbf8013dad8257 0x14b6fe004f6b6095 0x15fdc0e3ffc007fc 0xc57f7038fff001ff

def z808 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x11fc03001ff03ec2 0x047f00c007fc0fb0

def z809 : W := mkw 0x80ffbbfac9601180 0x203feefeb2580460 0xfbfffffffff001c3 0xfefffffffffc0070

def z810 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x73fe03e01ff03fc2 0x1cff80f807fc0ff0

def z811 : W := mkw 0x029244001dbec003 0x80a49100076fb000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z812 : W := mkw 0xd02403fbe24137d4 0x740900fef8904df5 0x040003ffe0003ffc 0xc10000fff8000fff

def z813 : W := mkw 0x00dbb81ac0000000 0x0036ee06b0000000 0x90fdfc1fe0000000 0xa43f7f07f8000000

def z814 : W := mkw 0x43ba9e970bb3ee31 0xd0eea7a5c2ecfb8c 0x461e1f9f01f0fe30 0xd18787e7c07c3f8c

def z815 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xc003fc7fe0000000 0xb000ff1ff8000000

def z816 : W := mkw 0x5000040120134254 0x940001004804d095 0xfe03ffffe03fc7ff 0xff80fffff80ff1ff

def z817 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfbfffc001fffc1cf 0x3effff0007fff073

def z818 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xb9e1e39f1e0f3830 0xee7878e7c783ce0c

def z819 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0x91e1e31c1e0f3800 0x247878c70783ce00

def z820 : W := mkw 0x00ffbbfac2002400 0x403feefeb0800900 0xfcffffffe0003e00 0xff3ffffff8000f80

def z821 : W := mkw 0x00dfb95ac0000000 0x0037ee56b0000000 0xf8ffff5fe0000000 0xfe3fffd7f8000000

def z822 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffce3ffffc7c3 0xffffff38fffff1f0

def z823 : W := mkw 0x329e9d48a9f2d14d 0x8ca7a7522a7cb453 0x421e1c60e1f0c1cc 0x10878718387c3073

def z824 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfffdd35c9fc8f93f 0xffff74d727f23e4f

def z825 : W := mkw 0x20ffbbfac0c09109 0x083feefeb0302442 0xf8ffffffe1c00000 0xfe3ffffff8700000

def z826 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xd21dd35c91c8f93c 0xb48774d724723e4f

def z827 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xc01fffffe0000000 0xf007fffff8000000

def z828 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfcfffffff0003801 0xff3ffffffc000e00

def z829 : W := mkw 0x0069ba9ac0000000 0x001a6ea6b0000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z830 : W := mkw 0x029adc001dbec003 0x80a6b700076fb000 0x7bfe1c001fffc003 0x1eff870007fff000

def z831 : W := mkw 0x004db95ac0000000 0x00136e56b0000000 0xc01dfc5fe0000000 0xb0077f17f8000000

def z832 : W := mkw 0x00dfb97ac0000000 0x0037ee5eb0000000 0xd81fff7fe0000000 0xf607ffdff8000000

def z833 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfffffffffff8ffff 0xfffffffffffe3fff

def z834 : W := mkw 0x029ad4001dbec003 0x80a6b500076fb000 0xfbffd0001fffc003 0x3efff40007fff000

def z835 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0x91fdff1fffc03800 0xa47f7fc7fff00e00

def z836 : W := mkw 0x00d364001d3e4002 0x8034d900074f9000 0xfbfffc001fffc003 0x3effff0007fff000

def z837 : W := mkw 0x02dbbc000db6c001 0x80b6ef00036db000 0xebfe3c000fffc003 0x3aff8f0003fff000

def z838 : W := mkw 0x80ffbbfac9601180 0x203feefeb2580460 0xfeffffffe1f007c3 0xffbffffff87c01f0

def z839 : W := mkw 0x51004405341f4a76 0x944011014d07d29d 0x06000000003fc7ff 0x01800000000ff1ff

def z840 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1e3fffe0f3e33 0xef7878ffff83cf8c

def z841 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0x11e1c31c1e0f3803 0x047870c70783ce00

def z842 : W := mkw 0x02dbfc125dbec003 0x80b6ff04976fb000 0xfbfffc037fffc003 0x3effff00dffff000

def z843 : W := mkw 0x00dbb81ac0000000 0x0036ee06b0000000 0xa0e3fc1fe0000000 0xa838ff07f8000000

def z844 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0x7fffefff7ff03fc3 0x5ffffbffdffc0ff0

def z845 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1fff5c91c8f93d 0xff87ffd724723e4f

def z846 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x57fe03601ff03fc3 0x15ff80d807fc0ff0

def z847 : W := mkw 0x02d36c001d3e4002 0x80b4db00074f9000 0xfbffec001fff0003 0x3efffb0007ffc000

def z848 : W := mkw 0x006dbbdac0000000 0x001b6ef6b0000000 0xf8fdffdfe0000000 0xfe3f7ff7f8000000

def z849 : W := mkw 0x11616696361e6c66 0xc45859a58d879b19 0x53e3df7cfe30f9cc 0x14f8f7df3f8c3e73

def z850 : W := mkw 0x4128d2971289ae33 0x504a34a5c4a26b8c 0xde1dd39f11c8fe31 0xf78774e7c4723f8c

def z851 : W := mkw 0x00ffbbfac9200000 0x003feefeb2480000 0xf9ffffffee300002 0xfe7ffffffb8c0000

def z852 : W := mkw 0x00ffbbfac9200000 0x003feefeb2480000 0xfaffffffe1f00000 0xfebffffff87c0000

def z853 : W := mkw 0x802407e002527580 0xe00901f800949d60 0xee023fe0003fffc3 0x7b808ff8000ffff0

def z854 : W := mkw 0x006dbbfac0000000 0x001b6efeb0000000 0x8001ff1fe0000000 0xa0007fc7f8000000

def z855 : W := mkw 0x00dbb81ac0000000 0x0036ee06b0000000 0xf8fffcffe0000000 0xfe3fff3ff8000000

def z856 : W := mkw 0x80ffbbfac9601180 0x203feefeb2580460 0xf8ffffffe1c00000 0xfe3ffffff8700000

def z857 : W := mkw 0x02d32c000d364000 0x80b4cb00034d9000 0x63fe2c000ff70002 0x18ff8b0003fdc000

def z858 : W := mkw 0x00dbb81ac9200000 0x0036ee06b2480000 0xfbfffc1ffff00003 0xbeffff07fffc0000

def z859 : W := mkw 0x00ffbbfacb202400 0x403feefeb2c80900 0xfffffffffff03e03 0xfffffffffffc0f80

def z860 : W := mkw 0x00dbb83ac0000000 0x0036ee0eb0000000 0x8003fc3fe0000000 0xa000ff0ff8000000

def z861 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xfde3e3ff1e0f3e33 0xff78f8ffc783cf8c

def z862 : W := mkw 0x909e9d68e97251c4 0xa427a75a3a5c9471 0x421e1c60e1f0c1cc 0x10878718387c3073

def z863 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xee03fcffe03007c3 0xfb80ff3ff80c01f0

def z864 : W := mkw 0x006dbbfac0000000 0x001b6efeb0000000 0xd81dffffe0000000 0xf6077ffff8000000

def z865 : W := mkw 0x80ffbbfac2403580 0x603feefeb0900d60 0xfeffffffe0303fc3 0xffbffffff80c0ff0

def z866 : W := mkw 0x80b202a00b603580 0x602c80a802d80d60 0x7ffe00a01ff03fc3 0x1fff802807fc0ff0

def z867 : W := mkw 0x200cd16cd0c8992b 0x0803345b3432264a 0xde1dd37cf1c8f93d 0xf78774df3c723e4f

def z868 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xbbfde0001fffc003 0x2eff780007fff000

def z869 : W := mkw 0x50ffbffbe0134254 0x943feffef804d095 0x16fdc31c003fc7ff 0x05bf70c7000ff1ff

def z870 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfbffffffeff007c2 0xfefffffffbfc01f0

def z871 : W := mkw 0x000c914880401100 0x0003245220100440 0xfe1ffffff1f03fc3 0xff87fffffc7c0ff0

def z872 : W := mkw 0xc12403f302413790 0x704900fcc0904de4 0x040003e300003fc0 0x410000f8c0000ff0

def z873 : W := mkw 0x00be9bfac0000000 0x002fa6feb0000000 0xd81fdfffe0000000 0xf607f7fff8000000

def z874 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x11fdc0001ff70002 0x047f700007fdc000

def z875 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffc001fffc13f 0x3fffff0007fff04f

def z876 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfdffffffee303fc2 0xff7ffffffb8c0ff0

def z877 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xda1dd31c91c8f83d 0xb68774c724723e0f

def z878 : W := mkw 0x80ffbbfac2403580 0x603feefeb0900d60 0xf8ffffffe0003800 0xfe3ffffff8000e00

def z879 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfbfffffffff03803 0xfefffffffffc0e00

def z880 : W := mkw 0xd12403f722413ff4 0x744900fdc8904ffd 0x040003ffe0003ffc 0xc10000fff8000fff

def z881 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xb9e1e39f1e073e02 0xee7878e7c781cf80

def z882 : W := mkw 0x61616297168dae3b 0x585858a5c5a36b8e 0xbde1e39f1e0ffe3f 0xef7878e7c783ff8f

def z883 : W := mkw 0xa0ffbbfacbe0b589 0x683feefeb2f82d62 0xfffffffffff0ffcf 0xfffffffffffc3ff3

def z884 : W := mkw 0xc16162b7160d2eb2 0x705858adc5834bac 0xbde1e3bf1e0f3ef3 0xef7878efc783cfbc

def z885 : W := mkw 0x00fbbabac0000000 0x003eeeaeb0000000 0xb8e3ffbfe0000000 0xee38ffeff8000000

def z886 : W := mkw 0x0069ba9ac0000000 0x001a6ea6b0000000 0xa0e1fc9fe0000000 0xa8387f27f8000000

def z887 : W := mkw 0x7249fc0db49fca7f 0x9c927f036d27f29f 0x8001fc1fe00fc03c 0xa0007f07f803f00f

def z888 : W := mkw 0x00ffbbfac2002400 0x403feefeb0800900 0xfffffffffe303fc3 0xffffffffff8c0ff0

def z889 : W := mkw 0x00dfb97ac0000000 0x0037ee5eb0000000 0x801dfc1fe0000000 0xa0077f07f8000000

def z890 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xfffde39f1fcf3e33 0xffff78e7c7f3cf8c

def z891 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xb8e1fc1fe0000000 0xae387f07f8000000

def z892 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffffffe008c03c 0xfe3ffffff802300f

def z893 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe3fffffe3f3ff3 0xfff8ffffff8fcffc

def z894 : W := mkw 0x20ffbbfac0808009 0x083feefeb0202002 0xf8ffffffe000c00c 0xfe3ffffff8003003

def z895 : W := mkw 0x5000040120134254 0x940001004804d095 0x66023ce3e03fc7ff 0x19808f38f80ff1ff

def z896 : W := mkw 0x029204000d364000 0x80a48100034d9000 0x7bfe00001ff70003 0x1eff800007fdc000

def z897 : W := mkw 0x0069babac0000000 0x001a6eaeb0000000 0x8001fcbfe0000000 0xa0007f2ff8000000

def z898 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xdbfdfc001fcfc001 0x36ff7f0007f3f000

def z899 : W := mkw 0x2008d00410c8992b 0x080234010432264a 0xde1dd31c11c8f93d 0xf78774c704723e4f

def z900 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xb9e1e31f1e0f3833 0xae7878c7c783ce0c

def z901 : W := mkw 0x5000040120134254 0x940001004804d095 0xfe023fe3f03fffff 0xff808ff8fc0fffff

def z902 : W := mkw 0x029244001dbec003 0x80a49100076fb000 0x13fc00001fffc003 0x04ff000007fff000

def z903 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbffff1c1fffc003 0xfeffffc707fff000

def z904 : W := mkw 0x00616284160c2c22 0x401858a105830b08 0xbde1e39c1e0f3e33 0xef7878e70783cf8c

def z905 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc009fffc03f 0xbeffff0027fff00f

def z906 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xb8fdff9fe0000000 0xee3f7fe7f8000000

def z907 : W := mkw 0x809601400b603580 0x6025805002d80d60 0x7ffe03401ff03fc3 0x5fff80d007fc0ff0

def z908 : W := mkw 0x02dbbc000db6c001 0x80b6ef00036db000 0xfbfffc000ff7c002 0x3effff0003fdf000

def z909 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x11fdc0001fcfc000 0x047f700007f3f000

def z910 : W := mkw 0x51204685361f6e76 0xd44811a14d87db9d 0x7fe203e01e3fffff 0x5ff880f8078fffff

def z911 : W := mkw 0x006dbbfac0000000 0x001b6efeb0000000 0xe803ffffe0000000 0xfa00fffff8000000

def z912 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xb8ffefbf60000000 0xee3ffbefd8000000

def z913 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x9e1dc31c11c8f93d 0xe78770c704723e4f

def z914 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffc001fffc7c3 0x3fffff0007fff1f0

def z915 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z916 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfcffffffe0000603 0xff3ffffff8000180

def z917 : W := mkw 0x5000040120134254 0x940001004804d095 0xc6023ce3e03fc7fc 0xf1808f38f80ff1ff

def z918 : W := mkw 0x02dbbc000db6c001 0x80b6ef00036db000 0x7bfe3c001ff7c003 0x1eff8f0007fdf000

def z919 : W := mkw 0x009e9968c0000000 0x0027a65a30000000 0xf81fffffe0000000 0xfe07fffff8000000

def z920 : W := mkw 0x00416004140c0822 0x0010580105030208 0xb9e1e31c1e0f3803 0x2e7878c70783ce00

def z921 : W := mkw 0x51004405361f6e76 0xd44011014d87db9d 0x050000001e0ffe3f 0x014000000783ff8f

def z922 : W := mkw 0x200cd14c94cc992b 0x080334532533264a 0xdf1dd35c9fcff93f 0xf7c774d727f3fe4f

def z923 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde3efbf7e0f3e33 0xef78fbefdf83cf8c

def z924 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1dd3fc91c8fffd 0xf78774ff24723fff

def z925 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe03e01ff83ff3 0xffff80f807fe0ffc

def z926 : W := mkw 0x02dbfc205dbec003 0x80b6ff08176fb000 0xfbfffc207fffc003 0x3effff081ffff000

def z927 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1df3df91c8f93d 0xff877cf7e4723e4f

def z928 : W := mkw 0x7004454530dbdb7f 0x9c0111514c36f6df 0x7e1e03e011ffffff 0x5f8780f8047fffff

def z929 : W := mkw 0x41204285160d2e32 0x504810a145834b8c 0xbde1c39c1e0f3e33 0xef7870e70783cf8c

def z930 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xb9ffec001fff0003 0x2e7ffb0007ffc000

def z931 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffc401fffc103 0x7fffff1007fff040

def z932 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x9de1e31f1e0f3831 0xe77878c7c783ce0c

def z933 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xd0ffff7fe0000000 0xb43fffdff8000000

def z934 : W := mkw 0x02d36c001dbec003 0x80b4db00076fb000 0x7bfe2c001fffc003 0x1eff8b0007fff000

def z935 : W := mkw 0x02dbbc000db6c001 0x80b6ef00036db000 0x21fe2c000ff70002 0x087f8b0003fdc000

def z936 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfffffce0ffffc7cf 0x7fffff383ffff1f3

def z937 : W := mkw 0x0041281240000000 0x00104a0490000000 0x8001ec1f60000000 0xa0007b07d8000000

def z938 : W := mkw 0x5092000129210254 0x142480004a484095 0x7ffe00e3fff007ff 0xdfff8038fffc01ff

def z939 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1dd3fff1c8f93d 0xf78774fffc723e4f

def z940 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x3dfe03a01ff03ec3 0x4f7f80e807fc0fb0

def z941 : W := mkw 0x00dfb97ac0000000 0x0037ee5eb0000000 0xe81ffcffe0000000 0xfa07ff3ff8000000

def z942 : W := mkw 0x00dbb81ac0000000 0x0036ee06b0000000 0xc01ffc1fe0000000 0xb007ff07f8000000

def z943 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe3fffffe0fff3f 0xfff8ffffff83ffcf

def z944 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc831fffc003 0xfeffff20c7fff000

def z945 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x5ffc03401ff03fc3 0x57ff00d007fc0ff0

def z946 : W := mkw 0x80ffbbfacb202480 0x603feefeb2c80920 0xf9ffffffee000000 0xfe7ffffffb800000

def z947 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc409fffc10f 0x3effff1027fff043

def z948 : W := mkw 0xd10044053f7f7ff6 0xf44011014fdfdffd 0x070000001fffffff 0x01c0000007ffffff

def z949 : W := mkw 0x5000040120134254 0x940001004804d095 0xfe1e3ce3f1ffc7ff 0xff878f38fc7ff1ff

def z950 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc409fffc003 0xfeffff1027fff000

def z951 : W := mkw 0x612403ffc2413f38 0x584900fff0904fce 0x040003ffe0003f3c 0xc10000fff8000fcf

def z952 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe3fe3fff8ffff 0xffff8ff8fffe3fff

def z953 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x79fe03e01ff03ec2 0x5e7f80f807fc0fb0

def z954 : W := mkw 0xa29e9d6889f2d189 0xa8a7a75a227cb462 0x421e1c6081f0c1cc 0x10878718207c3073

def z955 : W := mkw 0x80ffbbfac2002480 0x603feefeb0800920 0xf8ffffffe00006c0 0xfe3ffffff80001b0

def z956 : W := mkw 0x530044053fbfee77 0xd4c011014feffb9d 0x070000001fffffff 0x01c0000007ffffff

def z957 : W := mkw 0x5349fc17349fca77 0x94d27f05cd27f29d 0x8001fc1fe00fc03c 0xa0007f07f803f00f

def z958 : W := mkw 0x00fbba9ac0000000 0x003eeea6b0000000 0xf8ffff9fe0000000 0xfe3fffe7f8000000

def z959 : W := mkw 0x02dbfc08ddbec003 0x80b6ff02376fb000 0xfbfffc00ffffc003 0x3effff003ffff000

def z960 : W := mkw 0x02d32c000d364000 0x80b4cb00034d9000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z961 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xb1e1e39f1e0f3e32 0xac7878e7c783cf8c

def z962 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0xa0e3ecbf60000000 0xa838fb2fd8000000

def z963 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xbde1e39ffe0f3e3f 0xef7878e7ff83cf8f

def z964 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xe3fffc000fffc002 0x38ffff0003fff000

def z965 : W := mkw 0x002403c002403500 0x400900f000900d40 0x7ffe03e01ff03fc3 0x5fff80f807fc0ff0

def z966 : W := mkw 0x7100440536dfff7f 0xdc4011014db7ffdf 0x070000001fffffff 0x01c0000007ffffff

def z967 : W := mkw 0x00ffbbfac2002400 0x403feefeb0800900 0xf9fffffffe003800 0xfe7fffffff800e00

def z968 : W := mkw 0x00ffbbfac9601100 0x003feefeb2580440 0xfffffffffff03903 0xfffffffffffc0e40

def z969 : W := mkw 0x02ffbbfac9a08001 0x00bfeefeb2682000 0xf8ffffffe1c00000 0xfe3ffffff8700000

def z970 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfcffffffe00007c0 0xff3ffffff80001f0

def z971 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x11fdec001fc70000 0x047f7b0007f1c000

def z972 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x63fe3c001fffc003 0x18ff8f0007fff000

def z973 : W := mkw 0x00dbf8001d2c0002 0x0036fe00074b0000 0xfbfffc001fff0003 0x3effff0007ffc000

def z974 : W := mkw 0x00dbbc0009324000 0x8036ef00024c9000 0xfbfffc001fffc003 0x3effff0007fff000

def z975 : W := mkw 0xd02403e1224137d4 0x740900f848904df5 0x040003e000003ffc 0x410000f800000fff

def z976 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc03ffffc003 0xbeffff00fffff000

def z977 : W := mkw 0x002c93fac0000000 0x000b24feb0000000 0xf81fffffe0000000 0xfe07fffff8000000

def z978 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0xfbffe0001fff0003 0x3efff80007ffc000

def z979 : W := mkw 0x2000400410c8992b 0x080010010432264a 0xee023ce3f1c8f93d 0xfb808f38fc723e4f

def z980 : W := mkw 0x0008d00410888823 0x0002340104222208 0xde1dd35c91c8f93d 0xf78774d724723e4f

def z981 : W := mkw 0xe12403ff82413fb8 0x784900ffe0904fee 0x040003ff80003ffc 0xc10000ffe0000fff

def z982 : W := mkw 0x200cd94cd0c8992b 0x080336533432264a 0xde1ddf5cf1c8f93d 0xf78777d73c723e4f

def z983 : W := mkw 0xa00cd16c90c899ab 0x2803345b2432266a 0xde1dd37c91c8f9fd 0xf78774df24723e7f

def z984 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x941dd35c91c8f93c 0xe50774d724723e4f

def z985 : W := mkw 0x000c914880401100 0x0003245220100440 0xde1dd35c91c8f93d 0xf78774d724723e4f

def z986 : W := mkw 0x009ad40019bac003 0x8026b500066eb000 0xfbfffc001fffc003 0x3effff0007fff000

def z987 : W := mkw 0x004db95ac0000000 0x00136e56b0000000 0x8001ff5fe0000000 0xe0007fd7f8000000

def z988 : W := mkw 0x00ffbbfac0401100 0x003feefeb0100440 0xfefffffff1c8f93d 0xffbffffffc723e4f

def z989 : W := mkw 0x80ffbbfac9601180 0x203feefeb2580460 0xfefffffff1f039c1 0xffbffffffc7c0e70

def z990 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1fd37c91f8f9fd 0xf787f4df247e3e7f

def z991 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x561dd35c91c8f93d 0x158774d724723e4f

def z992 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x3de1c39c1e0f3e33 0x4f7870e70783cf8c

def z993 : W := mkw 0x7149f41fb49fca7f 0x9c527d07ed27f29f 0x8001fc1fe00fc03c 0xa0007f07f803f00f

def z994 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x35fe03e01ff03fc2 0x4d7f80f807fc0ff0

def z995 : W := mkw 0x80ffbbfac2403580 0x603feefeb0900d60 0xfdfffffffe003fc3 0xff7fffffff800ff0

def z996 : W := mkw 0x5000040120134254 0x940001004804d095 0xa4023ce3e03fc7fe 0xe9008f38f80ff1ff

def z997 : W := mkw 0x41416017140d0a32 0x10505805c503428c 0xbde1e31f1e0f3833 0xef7878c7c783ce0c

def z998 : W := mkw 0x20ffbbfac0401108 0x083feefeb0100442 0xf8ffffffe000010c 0xfe3ffffff8000043

def z999 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe03e09ff03fff 0xdfff80f827fc0fff

def z1000 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xe803fc1fe0000000 0xba00ff07f8000000

def z1001 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1dd3dc91c8ff3f 0xff8774f724723fcf

def z1002 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x9de1c31c1e0f3e33 0xe77870c70783cf8c

def z1003 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1ff9ffe0f3e33 0xef787fe7ff83cf8c

def z1004 : W := mkw 0x82dbfc201dbec083 0xa0b6ff08076fb020 0xfbfffc201fffc0c3 0x3effff0807fff030

def z1005 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xd8fdff5fe0000000 0xf63f7fd7f8000000

def z1006 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xb9fdfc001fcfc003 0x2e7f7f0007f3f000

def z1007 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1fdf7cf1c8f93d 0xf787f7df3c723e4f

def z1008 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xe0fffcffe0000000 0xb83fff3ff8000000

def z1009 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffffffe03006c2 0xfe3ffffff80c01b0

def z1010 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffc601fffc1c3 0x3effff1807fff070

def z1011 : W := mkw 0x00dfb97ac0000000 0x0037ee5eb0000000 0xf8fffc7fe0000000 0xbe3fff1ff8000000

def z1012 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfbfffffffff039c0 0xfefffffffffc0e70

def z1013 : W := mkw 0x0092040009324000 0x80248100024c9000 0x7bfe00001fffc003 0x1eff800007fff000

def z1014 : W := mkw 0x22dbfc0c9dbec82b 0x88b6ff03276fb20a 0xfffffc5c9fffc13f 0xffffff1727fff04f

def z1015 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x3ffc03801ff03fc3 0x4fff00e007fc0ff0

def z1016 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xb9e1e39f1e0f3e03 0x2e7878e7c783cf80

def z1017 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x73fffc001ff7c002 0x1cffff0007fdf000

def z1018 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffc001fffc033 0xffffff0007fff00c

def z1019 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x67fe00e01ff03fc3 0x19ff803807fc0ff0

def z1020 : W := mkw 0x00fbbabac0000000 0x003eeeaeb0000000 0x80e1fc1fe0000000 0xa0387f07f8000000

def z1021 : W := mkw 0x02d32c000d364000 0x80b4cb00034d9000 0x31fe2c001ff70002 0x0c7f8b0007fdc000

def z1022 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0x0001ec1f60000000 0x00007b07d8000000

def z1023 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x9c1dd31c91c8f83d 0xe70774c724723e0f

def z1024 : W := mkw 0x02dbfc089dbec003 0x80b6ff02276fb000 0xfbfffc1c9fffc003 0xbeffff0727fff000

def z1025 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x57fe03e01ff03fc0 0x55ff80f807fc0ff0

def z1026 : W := mkw 0x00ffbbfac2002400 0x403feefeb0800900 0xf9ffffffee000602 0xfe7ffffffb800180

def z1027 : W := mkw 0x200c914c80c09929 0x080324532030264a 0xde1dd35c81c0f93c 0xf78774d720703e4f

def z1028 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xf9fffffffff03ec2 0xfe7ffffffffc0fb0

def z1029 : W := mkw 0x80f32ab24b202480 0x603ccaac92c80920 0xbde3efbf7e303ec3 0xef78fbefdf8c0fb0

def z1030 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfafffffff1c00001 0xfebffffffc700000

def z1031 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xbde1e3bf7e0f3ef3 0xef7878efdf83cfbc

def z1032 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf9fffffffe000003 0xfe7fffffff800000

def z1033 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xbde1e39f1e0f3fff 0xef7878e7c783cfff

def z1034 : W := mkw 0x416162b7560d2e32 0x505858add5834b8c 0xbde1e3bf7e0f3e33 0xef7878efdf83cf8c

def z1035 : W := mkw 0x0049f400149ec003 0x80127d000527b000 0xfbfffc001fffc003 0x3effff0007fff000

def z1036 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1dff5ff1c8f93d 0xf7877fd7fc723e4f

def z1037 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x95e1e31f1e0f3e33 0xa57878c7c783cf8c

def z1038 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x35e1e39f1e073e32 0xcd7878e7c781cf8c

def z1039 : W := mkw 0x00dfb94880000000 0x0037ee5220000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1040 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfeffffffe1f03fc0 0xffbffffff87c0ff0

def z1041 : W := mkw 0x51004405361f6e76 0xd44011014d87db9d 0x050000001e3f3ef3 0x01400000078fcfbc

def z1042 : W := mkw 0x2049b81ac0808009 0x08126e06b0202002 0x8001fc1fe000c00c 0xa0007f07f8003003

def z1043 : W := mkw 0xa0b603e88b603588 0x682d80fa22d80d62 0x7ffe03e09ff03fcf 0x5fff80f827fc0ff3

def z1044 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0xfbfdf0001fcfc003 0x3eff7c0007f3f000

def z1045 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde3e3bf1e3f3ef3 0xef78f8efc78fcfbc

def z1046 : W := mkw 0x02d364001dbec003 0x80b4d900076fb000 0xfbffe0001fffc003 0x3efff80007fff000

def z1047 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xc61dd35c81c8f93c 0xf18774d720723e4f

def z1048 : W := mkw 0x00416000140c0002 0x0010580005030000 0xfbfde0001fcf0003 0x3eff780007f3c000

def z1049 : W := mkw 0x80b60be04b603580 0x602d82f812d80d60 0x7ffe0fe07ff03fc3 0x5fff83f81ffc0ff0

def z1050 : W := mkw 0x00ffbbfac0808001 0x003feefeb0202000 0xfaffffffe1c0c000 0xfebffffff8703000

def z1051 : W := mkw 0x00fbbabac0000000 0x003eeeaeb0000000 0xe8e3fcffe0000000 0xfa38ff3ff8000000

def z1052 : W := mkw 0x00f72bf240000000 0x003dcafc90000000 0xf8ffefff60000000 0xfe3ffbffd8000000

def z1053 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe1fe0fff03fc3 0x5fff87f83ffc0ff0

def z1054 : W := mkw 0x720044053dffdb7f 0x9c8011014f7ff6df 0x070000001fffffff 0x01c0000007ffffff

def z1055 : W := mkw 0x40416005140d0a32 0x101058014503428c 0xbde1e39f1e0f3e33 0xef7878e7c783cf8c

def z1056 : W := mkw 0x006523fac0000000 0x001948feb0000000 0xf8e3ffffe0000000 0xfe38fffff8000000

def z1057 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe3f3ff9e3fffff 0xfff8fcffe78fffff

def z1058 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1fd35c91f8f93f 0xff87f4d7247e3e4f

def z1059 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe23e01fff3fc3 0x7fff88f807ffcff0

def z1060 : W := mkw 0x00fbba9200000000 0x003eeea480000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1061 : W := mkw 0x80f72bf24b603580 0x603dcafc92d80d60 0xffffefff7ff03fc3 0xfffffbffdffc0ff0

def z1062 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe1e3df1e0f3f33 0xfff878f7c783cfcc

def z1063 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1e31c1e0f3e33 0x2f7878c70783cf8c

def z1064 : W := mkw 0x80ffbbfacb202480 0x603feefeb2c80920 0xfbfffffffff006c3 0xfefffffffffc01b0

def z1065 : W := mkw 0x80f723f20b603580 0x603dc8fc82d80d60 0xfffffffffff03fc3 0xfffffffffffc0ff0

def z1066 : W := mkw 0x80dfb97ac9601180 0x2037ee5eb2580460 0xc21ffc7fe1f001c0 0xb087ff1ff87c0070

def z1067 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x7bffc0001fffc003 0x1efff00007fff000

def z1068 : W := mkw 0x712403dfa2413f7c 0x5c4900f7e8904fdf 0x040003ffe0003ffc 0xc10000fff8000fff

def z1069 : W := mkw 0xa0ffbbfac9e09189 0x283feefeb2782462 0xfaffffffe1f0c1cc 0xfebffffff87c3073

def z1070 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xfde1f3df9e0f3e33 0xff787cf7e783cf8c

def z1071 : W := mkw 0x00f72bfac0000000 0x003dcafeb0000000 0xb8e3efffe0000000 0xee38fbfff8000000

def z1072 : W := mkw 0x80ffbbfacb202480 0x603feefeb2c80920 0xfdfffffffe303ec3 0xff7fffffff8c0fb0

def z1073 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x15e1c39f1e0f3e33 0xc57870e7c783cf8c

def z1074 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xce01fc5fe008c13d 0xf3807f17f802304f

def z1075 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xf8ffff1fe0000000 0xbe3fffc7f8000000

def z1076 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe3fe01ff03fc3 0x7fff8ff807fc0ff0

def z1077 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xd81dfc1fe0000000 0xb6077f07f8000000

def z1078 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x5e1dc35c11c8f93d 0x578770d704723e4f

def z1079 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0xf9fffc001fcf0003 0x3e7fff0007f3c000

def z1080 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x50ffdfffe0000000 0xd43ff7fff8000000

def z1081 : W := mkw 0x02dbfc041dbec823 0x80b6ff01076fb208 0xfbffff1c1ffff803 0x3effffc707fffe00

def z1082 : W := mkw 0x204db95ac0c09109 0x08136e56b0302442 0xc21dfc5fe1c0c10c 0xb0877f17f8703043

def z1083 : W := mkw 0x5000040120134254 0x940001004804d095 0xe2023ce3e03fc7fe 0xb8808f38f80ff1ff

def z1084 : W := mkw 0x006db3da80000000 0x001b6cf6a0000000 0xf8ffffffe0000000 0xfe3ffffff8000000

def z1085 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffc801fffc603 0x7fffff2007fff180

def z1086 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x17fc03e01ff03fc3 0x45ff00f807fc0ff0

def z1087 : W := mkw 0x80fbbabacb202480 0x603eeeaeb2c80920 0xa1e3fcbfee3006c2 0xa878ff2ffb8c01b0

def z1088 : W := mkw 0x829e9d68c9f2d181 0xa0a7a75a327cb460 0x421e1c60e1f0c1c0 0x10878718387c3070

def z1089 : W := mkw 0x00ffbbfac0401100 0x003feefeb0100440 0xfefffffff1f03fc3 0xffbffffffc7c0ff0

def z1090 : W := mkw 0x70004405309bca7f 0x9c0011014c26f29f 0x00000000000fc03c 0x000000000003f00f

def z1091 : W := mkw 0x2008d00c9088882b 0x080234032422220a 0xde1dd31c91c8f83d 0xf78774c724723e0f

def z1092 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x3de1e39f1e073e03 0x4f7878e7c781cf80

def z1093 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe03e01ff8ffff 0x5fff80f807fe3fff

def z1094 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xffe3e3fffe3f3fff 0xfff8f8ffff8fcfff

def z1095 : W := mkw 0x00d320000d240000 0x0034c80003490000 0x7bfe20001ff70003 0x1eff880007fdc000

def z1096 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0xa003fcbfe0000000 0xa800ff2ff8000000

def z1097 : W := mkw 0x029a9c0009b2c001 0x80a6a700026cb000 0xfbfe3c001fffc003 0x3eff8f0007fff000

def z1098 : W := mkw 0x00b202800b202400 0x402c80a002c80900 0x7ffe03e01ff03fc3 0x5fff80f807fc0ff0

def z1099 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x95e1e39f1e0f3e30 0xe57878e7c783cf8c

def z1100 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0x91fde0001fcf0000 0x247f780007f3c000

def z1101 : W := mkw 0x0049f000148c8003 0x00127c0005232000 0xb9fde0001fcf0003 0x2e7f780007f3c000

def z1102 : W := mkw 0x7000440530dbdb7f 0x9c0011014c36f6df 0x0600000011cff93d 0x018000000473fe4f

def z1103 : W := mkw 0x802403c00b603580 0x600900f002d80d60 0x7ffc03c01ff03fc3 0x5fff00f007fc0ff0

def z1104 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0x31fde0001fc70002 0x0c7f780007f1c000

def z1105 : W := mkw 0x80b603f24b603580 0x602d80fc92d80d60 0x7ffe03e37ff03fc3 0x5fff80f8dffc0ff0

def z1106 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe03e3fff03fc3 0xdfff80f8fffc0ff0

def z1107 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe2fe37ff03fc3 0x5fff8bf8dffc0ff0

def z1108 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x70ffffffe0000000 0x1c3ffffff8000000

def z1109 : W := mkw 0x00ffbbfac0401100 0x003feefeb0100440 0xfaffffffe1c00100 0xfebffffff8700040

def z1110 : W := mkw 0x53f32e932f376654 0xd4fccba4cbcdd995 0x21e22ca36e3706c2 0x08788b28db8dc1b0

def z1111 : W := mkw 0x00ffbbfac2403500 0x403feefeb0900d40 0xffffffffffc03f03 0xfffffffffff00fc0

def z1112 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfaffffffe000c10c 0xfebffffff8003043

def z1113 : W := mkw 0x01ffbbfac6042400 0x407feefeb1810900 0xf9ffffffee000000 0xfe7ffffffb800000

def z1114 : W := mkw 0x00ffbbfac9200000 0x003feefeb2480000 0xfffffffffff007c3 0xfffffffffffc01f0

def z1115 : W := mkw 0x229e9d68c9f2d109 0x88a7a75a327cb442 0x421e1c60e1f0c10c 0x10878718387c3043

def z1116 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xde1dd31c11c8f93d 0x378774c704723e4f

def z1117 : W := mkw 0x02dbf8001dac8003 0x00b6fe00076b2000 0x11fdc0001fcf0003 0x047f700007f3c000

def z1118 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0xb9e1e39f1e0f3803 0xee7878e7c783ce00

def z1119 : W := mkw 0x0069ba9ac2002400 0x401a6ea6b0800900 0xbde1ff9ffe003e03 0xef787fe7ff800f80

def z1120 : W := mkw 0x2045614c944c192a 0x081158532513064a 0xbde1e35c9e0f393f 0xef7878d72783ce4f

def z1121 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xfe1df35c91cff93f 0xff877cd72473fe4f

def z1122 : W := mkw 0x809200000b603580 0x6024800002d80d60 0x7ffe00e01ff03fc3 0x5fff803807fc0ff0

def z1123 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xd3fffc001fffc000 0x34ffff0007fff000

def z1124 : W := mkw 0x22dbfc041dbec82b 0x88b6ff01076fb20a 0xfbfffc001fffc03f 0x3effff0007fff00f

def z1125 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfcffffffe000013c 0xff3ffffff800004f

def z1126 : W := mkw 0x009240001d2c0002 0x00249000074b0000 0x7bfe00001fff0003 0x1eff800007ffc000

def z1127 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffce09fffc7ff 0xffffff3827fff1ff

def z1128 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xfde3ff9f1e0f3e33 0xff78ffe7c783cf8c

def z1129 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xa0e3ffffe0000000 0xe838fffff8000000

def z1130 : W := mkw 0x80be93e88b603580 0x602fa4fa22d80d60 0xfffffffffff03fc3 0xfffffffffffc0ff0

def z1131 : W := mkw 0x20ffbbfac0c09109 0x083feefeb0302442 0xfefffffff1c0f90d 0xffbffffffc703e43

def z1132 : W := mkw 0x809200000b603580 0x6024800002d80d60 0x17fc00001ff03fc3 0x05ff000007fc0ff0

def z1133 : W := mkw 0x0049b81ac0000000 0x00126e06b0000000 0x8001fcffe0000000 0xe0007f3ff8000000

def z1134 : W := mkw 0x0004414410481922 0x0001105104120648 0xde1dd35c91c8f93d 0xf78774d724723e4f

def z1135 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0x7ffe03001ff03fc3 0x1fff80c007fc0ff0

def z1136 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe23e31ff03fc3 0xffff88f8c7fc0ff0

def z1137 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xffffffffffc03901 0xfffffffffff00e40

def z1138 : W := mkw 0x0096014009601100 0x0025805002580440 0x7ffe03e01ff03fc3 0x5fff80f807fc0ff0

def z1139 : W := mkw 0x80b603facb603580 0x602d80feb2d80d60 0xfffe3ffffff03fc3 0xffff8ffffffc0ff0

def z1140 : W := mkw 0x0092000009200000 0x0024800002480000 0xfbfe20001fff0003 0x3eff880007ffc000

def z1141 : W := mkw 0x0061229202002400 0x401848a480800900 0xffe3fffffe303fc3 0xfff8ffffff8c0ff0

def z1142 : W := mkw 0x0041201200000000 0x0010480480000000 0x8001fc1fe0000000 0xa0007f07f8000000

def z1143 : W := mkw 0x00dbf800148c8003 0x0036fe0005232000 0xfbfffc001fcfc003 0x3effff0007f3f000

def z1144 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1e3df9e0f3f3f 0xef7878f7e783cfcf

def z1145 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x53ffdc001fffc003 0x14fff70007fff000

def z1146 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfeffffffe0000101 0xffbffffff8000040

def z1147 : W := mkw 0x41616297168dae33 0x505858a5c5a36b8c 0xbfe1e39f1fcffe33 0xeff878e7c7f3ff8c

def z1148 : W := mkw 0x41416005160d2e32 0x5050580145834b8c 0xbde1e31c1e0f3e33 0xef7878c70783cf8c

def z1149 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbfe1e39f1e0fff3f 0xeff878e7c783ffcf

def z1150 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0x35e1e39f1e0f3e33 0x0d7878e7c783cf8c

def z1151 : W := mkw 0x80ffbbfacb603580 0x603feefeb2d80d60 0xfdffffffffc03e03 0xff7ffffffff00f80

def z1152 : W := mkw 0x00616296140c0822 0x001858a585030208 0xbde1e39f1e0f3833 0xef7878e7c783ce0c

def z1153 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0x961dd31c91c8f93d 0xa58774c724723e4f

def z1154 : W := mkw 0x004db95ac0000000 0x00136e56b0000000 0x901dff1fe0000000 0xa4077fc7f8000000

def z1155 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xbde1f39f9e0ffe3f 0xef787ce7e783ff8f

def z1156 : W := mkw 0x03dbfc161dbec823 0x80f6ff05876fb208 0xfbfffc1c1fffc003 0x3effff0707fff000

def z1157 : W := mkw 0x0061229200000000 0x001848a480000000 0xb8e1ff9fe0000000 0xee387fe7f8000000

def z1158 : W := mkw 0x0061229200000000 0x001848a480000000 0xb8e3efbf60000000 0xee38fbefd8000000

def z1159 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfffffce3ffffc13f 0xffffff38fffff04f

def z1160 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xdbfdd0001fffc003 0x36ff740007fff000

def z1161 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffca01fffc6c3 0x3effff2807fff1b0

def z1162 : W := mkw 0x0000000000000000 0x0000000000000000 0xf803ffffe0000000 0xfe00fffff8000000

def z1163 : W := mkw 0x02dbfc041dbec823 0x80b6ff01076fb208 0xffffff5c9ffff93f 0xffffffd727fffe4f

def z1164 : W := mkw 0x500c9549a0134254 0x940325526804d095 0xde1dd35c803fc7ff 0xf78774d7200ff1ff

def z1165 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x93fdfc001fffc003 0x24ff7f0007fff000

def z1166 : W := mkw 0xd1b647e53f7f7ff6 0xf46d91f94fdfdffd 0x7ffe03e01fffffff 0x5fff80f807ffffff

def z1167 : W := mkw 0x200cd14c90c8992b 0x080334532432264a 0xd81dd35c91c8f83c 0xf60774d724723e0f

def z1168 : W := mkw 0x004db95ac0401100 0x00136e56b0100440 0xde1dff5ff1c03901 0xf7877fd7fc700e40

def z1169 : W := mkw 0xf00044053bfbffff 0xfc0011014efeffff 0x070000001fffffff 0x01c0000007ffffff

def z1170 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfeffffffe038c7ff 0xffbffffff80e31ff

def z1171 : W := mkw 0x22dbfc1eddbec82b 0x88b6ff07b76fb20a 0xfbfffc1fffffc03f 0xbeffff07fffff00f

def z1172 : W := mkw 0x80ffbbfac0401180 0x203feefeb0100460 0xf8ffffffe00001c0 0xfe3ffffff8000070

def z1173 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfbfffc00ffffc00f 0x3effff003ffff003

def z1174 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffce01fffc003 0x7effff3807fff000

def z1175 : W := mkw 0x02ffbbfacd240000 0x00bfeefeb3490000 0xf9ffffffee000000 0xfe7ffffffb800000

def z1176 : W := mkw 0xf02403eda2413ffc 0x7c0900fb68904fff 0x040003ffe0003ffc 0xc10000fff8000fff

def z1177 : W := mkw 0xc12403e502413fb0 0x704900f940904fec 0x040003e000003ff0 0x410000f800000ffc

def z1178 : W := mkw 0x00ffbbfac9200000 0x003feefeb2480000 0xf9ffffffffc00000 0xfe7ffffffff00000

def z1179 : W := mkw 0x809601600b603580 0x6025805802d80d60 0x7ffe00601ff03fc3 0x1fff801807fc0ff0

def z1180 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x78ffefff60000000 0x5e3ffbffd8000000

def z1181 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x7bffec001ff70003 0x1efffb0007fdc000

def z1182 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xb0ffffbfe0000000 0xac3fffeff8000000

def z1183 : W := mkw 0x00f32ab240000000 0x003ccaac90000000 0x30e3efbf60000000 0x0c38fbefd8000000

def z1184 : W := mkw 0x0041201200000000 0x0010480480000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z1185 : W := mkw 0x80b603e8cb603580 0x602d80fa32d80d60 0x7ffe03e0fff03fc3 0x5fff80f83ffc0ff0

def z1186 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe13e01ff8ffc3 0x7fff84f807fe3ff0

def z1187 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xffe1f3fffe0fffff 0xfff87cffff83ffff

def z1188 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0xfaffffffe0300003 0xfebffffff80c0000

def z1189 : W := mkw 0x0008900880000000 0x0002240220000000 0xe803fcffe0000000 0xfa00ff3ff8000000

def z1190 : W := mkw 0x51004405341f4a76 0x944011014d07d29d 0x00000000000fc03c 0x000000000003f00f

def z1191 : W := mkw 0x02dbfc041dbec823 0x80b6ff01076fb208 0xfffffc001ffff833 0x3fffff0007fffe0c

def z1192 : W := mkw 0x00ffbbfac0000000 0x003feefeb0000000 0x30ffefffe0000000 0xcc3ffbfff8000000

def z1193 : W := mkw 0x612403df82413f38 0x584900f7e0904fce 0x0400039f00003e30 0xc10000e7c0000f8c

def z1194 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xf9fffc001ff70002 0x3e7fff0007fdc000

def z1195 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0x31e1e31c1e073802 0x0c7878c70781ce00

def z1196 : W := mkw 0x12dbfc003dbec047 0x84b6ff000f6fb011 0xfffffc60ffffc1ff 0xffffff183ffff07f

def z1197 : W := mkw 0x004db95ac0000000 0x00136e56b0000000 0xf81fffffe0000000 0xfe07fffff8000000

def z1198 : W := mkw 0x80b202800b603580 0x602c80a002d80d60 0x7ffe03801ff03fc3 0x5fff80e007fc0ff0

def z1199 : W := mkw 0x01616296160c2c22 0x405858a585830b08 0xbde1e31c1e0f3833 0xef7878c70783ce0c

def z1200 : W := mkw 0x00fbbabac0000000 0x003eeeaeb0000000 0x20e3ecbf60000000 0x0838fb2fd8000000

def z1201 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xffffc3fc1ff03fc3 0xfffff0ff07fc0ff0

def z1202 : W := mkw 0x80b603e00b603580 0x602d80f802d80d60 0xfffe13e09ff03fc3 0xffff84f827fc0ff0

def z1203 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xfbfffca37fffc003 0x3effff28dffff000

def z1204 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0x33ffec001fffc003 0x0cfffb0007fff000

def z1205 : W := mkw 0x41616297160d2e32 0x505858a5c5834b8c 0xffe1f39f1e0ffe33 0xfff87ce7c783ff8c

def z1206 : W := mkw 0x02dbfc001dbec003 0x80b6ff00076fb000 0xffffff001ffff803 0x7fffffc007fffe00

def z1207 : W := mkw 0x51616297360d2e76 0x545858a5cd834b9d 0xfde3fffffe0f3fff 0xff78ffffff83cfff

def z1208 : W := mkw 0x0069ba9ac0000000 0x001a6ea6b0000000 0x8001ff9fe0000000 0xe0007fe7f8000000

def z1209 : W := mkw 0xd02403e1224137d4 0x740900f848904df5 0x040003e360003fc0 0x410000f8d8000ff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z10,z1,z3,z4,z5,z6,z11])],[(0,[z1,z12,z2,z3,z13,z5,z6]),(0,[z14,z2,z3,z4,z5,z6,z15])],[(0,[z1,z12,z16,z2,z3,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z19,z6]),(0,[z1,z2,z3,z20,z4,z5,z6])],[(0,[z1,z2,z3,z21,z4,z5,z6]),(0,[z1,z22,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z25]),(0,[z1,z16,z2,z3,z26,z5,z6]),(0,[z27,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z6,z28])],[(1,[z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z30,z3,z4,z5,z6]),(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z32,z5,z6])],[(0,[z1,z2,z3,z4,z5,z33,z6]),(0,[z2,z3,z4,z5,z34,z6,z35])],[(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z37,z1,z3,z38,z4,z5,z6]),(0,[z2,z39,z3,z40,z4,z5,z6]),(0,[z41,z2,z39,z3,z4,z5,z6]),(1,[z1,z42,z3,z4,z5,z6]),(0,[z1,z43,z44,z3,z4,z5,z6]),(0,[z1,z45,z2,z3,z4,z5,z6])],[(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z47,z14,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z48]),(0,[z49,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z50,z22,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z51]),(0,[z2,z3,z4,z5,z52,z6,z15]),(0,[z14,z2,z3,z26,z4,z5,z6]),(0,[z1,z2,z53,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z54,z55,z6]),(0,[z1,z2,z56,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z57,z6]),(0,[z14,z2,z3,z58,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z59,z6])],[(0,[z1,z2,z3,z60,z4,z5,z6]),(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z62,z1,z2,z3,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z64,z6]),(0,[z1,z2,z3,z4,z5,z65,z6])],[(0,[z1,z2,z66,z3,z4,z5,z6]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z34,z6,z68]),(0,[z1,z2,z3,z4,z5,z6,z69]),(0,[z1,z2,z3,z4,z5,z25,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z70]),(0,[z14,z2,z3,z4,z5,z6,z71]),(0,[z1,z2,z72,z4,z5,z34,z6])],[(1,[z2,z3,z4,z5,z6,z73]),(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z25,z68]),(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z76])],[(0,[z77,z1,z2,z78,z4,z5,z6]),(0,[z2,z3,z38,z4,z5,z6,z15]),(0,[z14,z79,z2,z3,z4,z5,z6]),(1,[z1,z2,z18,z4,z19,z6])],[(0,[z1,z2,z80,z3,z4,z5,z6]),(0,[z81,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z82,z38,z5,z6]),(0,[z83,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z84,z6])]],
   [[(0,[z85,z1,z2,z3,z4,z86,z6]),(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z3,z4,z88,z5,z6])],[(0,[z2,z3,z32,z4,z5,z6,z15]),(0,[z89,z1,z2,z3,z4,z5,z6])],[(0,[z1,z22,z3,z4,z5,z52,z6]),(0,[z90,z1,z2,z3,z13,z5,z6]),(0,[z2,z3,z4,z63,z5,z6,z15]),(0,[z14,z2,z3,z4,z5,z91,z6]),(1,[z1,z2,z3,z82,z5,z6]),(0,[z1,z2,z92,z3,z4,z5,z6]),(0,[z1,z2,z3,z93,z4,z5,z6]),(0,[z94,z1,z2,z3,z4,z5,z6])],[(0,[z1,z95,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z96,z5,z6]),(0,[z1,z2,z3,z4,z5,z97,z6]),(0,[z98,z1,z16,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z99,z5,z6]),(1,[z100,z2,z3,z4,z5,z6]),(0,[z1,z101,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z102,z6]),(0,[z1,z2,z3,z4,z103,z5,z6]),(0,[z1,z2,z3,z4,z5,z104,z6]),(0,[z1,z2,z3,z4,z5,z105,z6]),(0,[z106,z1,z2,z3,z4,z5,z71]),(0,[z1,z107,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z108,z4,z5,z6]),(1,[z109,z2,z3,z4,z5,z15]),(0,[z2,z18,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z110,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z111]),(0,[z98,z1,z2,z3,z32,z5,z6])],[(0,[z1,z2,z3,z4,z112,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z115]),(0,[z14,z2,z3,z4,z5,z55,z6]),(0,[z1,z23,z2,z3,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z117,z3,z4,z5,z6])]],
   [[(0,[z1,z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z119]),(0,[z1,z2,z3,z4,z120,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z121]),(0,[z1,z2,z3,z4,z5,z122,z6]),(0,[z123,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z78,z4,z5,z6]),(0,[z124,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z125]),(0,[z2,z3,z4,z5,z126,z6,z15]),(0,[z14,z10,z2,z3,z4,z5,z6]),(0,[z127,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z128,z5,z91])],[(0,[z1,z2,z3,z129,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z131]),(0,[z1,z12,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z132,z4,z5,z6])],[(0,[z14,z2,z3,z133,z4,z5,z6]),(0,[z1,z134,z2,z3,z4,z5,z6]),(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z136,z5,z6]),(0,[z137,z1,z3,z4,z5,z6,z138])],[(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z140,z14,z2,z3,z4,z5,z6]),(0,[z141,z1,z2,z3,z4,z5,z6])],[(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z143,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z144]),(0,[z14,z2,z3,z4,z145,z5,z6]),(0,[z1,z2,z3,z146,z4,z5,z6]),(0,[z1,z2,z3,z4,z147,z5,z6])],[(0,[z2,z148,z3,z4,z149,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z2,z44,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z24,z71]),(1,[z127,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z150,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z151,z6])],[(0,[z22,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z152,z6]),(0,[z1,z153,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z52,z6]),(0,[z1,z2,z3,z4,z5,z54,z6]),(0,[z106,z154,z2,z3,z4,z5,z6]),(1,[z1,z2,z155,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z156,z5,z6]),(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z1,z158,z2,z3,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6])],[(0,[z62,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z160])],[(0,[z1,z2,z3,z161,z4,z5,z6]),(0,[z1,z42,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z162,z4,z5,z6])],[(0,[z10,z1,z22,z3,z4,z5,z6]),(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z1,z16,z2,z3,z63,z5,z6]),(0,[z163,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z164,z6])],[(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z82,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z166,z3,z4,z5,z6]),(0,[z167,z2,z3,z78,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z168,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z169]),(0,[z1,z2,z3,z4,z5,z170,z6]),(0,[z1,z2,z3,z4,z5,z6,z171]),(0,[z1,z2,z3,z172,z4,z5,z6]),(0,[z1,z173,z2,z3,z4,z5,z6]),(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z175,z5,z6])],[(0,[z1,z2,z3,z4,z5,z176,z6]),(0,[z1,z23,z3,z26,z4,z5,z6]),(0,[z177,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z178,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z179]),(1,[z1,z180,z3,z4,z5,z6])],[(0,[z77,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z181,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z182]),(0,[z14,z2,z3,z183,z4,z5,z6]),(0,[z81,z1,z23,z3,z4,z5,z6]),(1,[z1,z2,z3,z184,z5,z6])],[(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z50,z14,z2,z3,z4,z5,z6]),(0,[z2,z3,z133,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z25,z6,z15]),(0,[z1,z2,z3,z186,z4,z5,z6]),(0,[z187,z1,z2,z3,z4,z5,z6]),(0,[z188,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z189,z5,z6]),(0,[z1,z2,z3,z190,z4,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z4,z5,z191,z6])],[(0,[z192,z2,z193,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z24,z6,z15]),(0,[z1,z3,z38,z4,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z194,z6]),(0,[z1,z2,z195,z3,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z187,z1,z2,z3,z4,z5,z68])],[(0,[z14,z2,z3,z4,z5,z6,z68]),(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z27,z1,z197,z3,z4,z5,z6]),(1,[z177,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z25,z6,z71])],[(0,[z1,z2,z3,z4,z5,z6,z198]),(0,[z1,z2,z199,z3,z4,z5,z6]),(1,[z114,z2,z3,z4,z86,z6]),(1,[z200,z2,z3,z4,z5,z6]),(0,[z98,z1,z67,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z201]),(0,[z202,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z203,z4,z5,z6]),(0,[z204,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z15]),(0,[z206,z2,z3,z4,z5,z6,z15]),(0,[z1,z109,z2,z3,z4,z5,z207]),(0,[z1,z2,z3,z208,z4,z5,z6]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z25,z6,z211])]],
   [[(1,[z1,z212,z3,z4,z5,z6]),(0,[z14,z1,z79,z3,z4,z5,z6]),(0,[z213,z1,z2,z3,z4,z5,z6]),(0,[z1,z118,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z214,z4,z5,z6])],[(0,[z167,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z215]),(0,[z1,z2,z3,z216,z4,z5,z6]),(0,[z1,z16,z2,z39,z3,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z6])],[(0,[z1,z2,z219,z3,z4,z5,z6]),(1,[z1,z3,z220,z4,z5,z6])],[(0,[z50,z1,z22,z3,z4,z5,z6]),(0,[z14,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z221,z6])],[(0,[z2,z3,z4,z149,z5,z86,z6]),(0,[z1,z2,z3,z4,z5,z6,z222]),(1,[z223,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z224,z4,z5,z6])],[(0,[z50,z22,z2,z3,z4,z5,z6]),(0,[z85,z2,z3,z4,z5,z6,z15]),(0,[z225,z2,z3,z4,z5,z6,z15]),(0,[z10,z1,z2,z3,z4,z5,z15]),(0,[z1,z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z39,z3,z32,z5,z6]),(0,[z187,z227,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z228,z5,z6])],[(0,[z16,z2,z3,z4,z5,z6,z15]),(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z231,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z6])],[(0,[z2,z3,z78,z4,z5,z6,z15]),(1,[z1,z2,z232,z4,z5,z6]),(0,[z1,z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z234,z6]),(0,[z106,z1,z2,z3,z184,z5,z6])]],
   [[(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z236,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z149,z6]),(0,[z10,z1,z109,z3,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z68])],[(1,[z1,z237,z3,z4,z5,z6]),(0,[z238,z1,z2,z3,z4,z5,z6])],[(0,[z167,z77,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z239,z4,z5,z6]),(0,[z240,z1,z3,z4,z5,z6,z71]),(1,[z1,z2,z3,z4,z145,z25])],[(0,[z241,z1,z2,z3,z4,z5,z6]),(1,[z14,z79,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z6,z138]),(0,[z62,z1,z23,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z242]),(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z3,z5,z244,z55,z6]),(1,[z27,z1,z2,z4,z245,z6]),(0,[z1,z2,z3,z4,z5,z244,z6])],[(0,[z246,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z109,z2,z3,z4,z5,z6,z15]),(1,[z1,z79,z3,z4,z5,z6]),(0,[z1,z248,z2,z3,z4,z5,z6]),(0,[z1,z2,z249,z3,z4,z5,z6])],[(0,[z2,z30,z3,z4,z5,z6,z15]),(0,[z250,z2,z3,z4,z5,z6,z15])],[(1,[z10,z2,z3,z4,z5,z15]),(0,[z2,z3,z93,z4,z5,z6,z15]),(0,[z1,z3,z38,z4,z5,z207,z6]),(0,[z1,z118,z3,z4,z5,z52,z6]),(0,[z1,z2,z3,z4,z251,z5,z6]),(0,[z1,z2,z3,z4,z5,z252,z6]),(0,[z1,z3,z4,z5,z6,z253,z138])]],
   [[(0,[z254,z1,z2,z3,z4,z5,z6]),(1,[z81,z1,z3,z4,z52,z6])],[(0,[z192,z1,z22,z3,z4,z5,z6]),(0,[z167,z1,z2,z78,z4,z5,z6]),(0,[z114,z1,z2,z255,z4,z5,z6]),(0,[z256,z1,z2,z3,z4,z5,z6]),(0,[z1,z257,z2,z3,z4,z5,z6]),(1,[z258,z2,z3,z4,z5,z6]),(1,[z47,z1,z2,z3,z5,z138])],[(0,[z14,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z259,z4,z5,z6]),(0,[z1,z2,z3,z4,z149,z5,z6]),(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z260,z1,z2,z3,z4,z5,z6])],[(0,[z77,z2,z3,z133,z4,z5,z6]),(0,[z1,z2,z261,z3,z4,z5,z6]),(0,[z14,z2,z3,z38,z4,z5,z6]),(0,[z1,z2,z262,z3,z4,z5,z6]),(0,[z263,z1,z2,z3,z4,z5,z6]),(0,[z264,z1,z2,z3,z4,z5,z6]),(0,[z47,z265,z2,z3,z4,z5,z6])],[(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z268,z3,z4,z5,z6])],[(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z1,z2,z3,z4,z270,z5,z6]),(0,[z14,z2,z212,z3,z4,z5,z6]),(0,[z14,z2,z271,z3,z4,z5,z6]),(0,[z1,z2,z3,z155,z4,z5,z6])],[(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6]),(0,[z274,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z275,z6]),(0,[z1,z2,z3,z4,z19,z5,z6]),(0,[z1,z2,z3,z4,z276,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z109,z2,z3,z4,z5,z24]),(0,[z127,z1,z2,z3,z38,z5,z6]),(0,[z1,z2,z3,z4,z5,z278,z6]),(0,[z1,z2,z3,z4,z279,z5,z6])]],
   [[(0,[z280,z1,z2,z3,z4,z5,z6]),(0,[z23,z2,z3,z4,z5,z6,z15]),(1,[z37,z1,z38,z4,z5,z6]),(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z282])],[(0,[z1,z283,z2,z3,z4,z5,z6]),(1,[z1,z284,z2,z3,z5,z6]),(0,[z285,z1,z2,z3,z4,z5,z6])],[(0,[z286,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z287,z3,z4,z5,z6]),(0,[z1,z16,z118,z3,z4,z5,z6]),(0,[z62,z1,z3,z4,z5,z52,z6]),(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z3,z99,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z291])],[(0,[z1,z2,z3,z292,z4,z5,z6]),(0,[z157,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z293,z6]),(1,[z294,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z295]),(0,[z1,z296,z2,z3,z4,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z298,z2,z3,z4,z13,z5,z6]),(0,[z37,z1,z2,z299,z4,z5,z6]),(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z128,z5,z244,z6]),(0,[z1,z2,z301,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z245,z6,z15]),(0,[z14,z2,z3,z4,z5,z34,z6]),(0,[z1,z2,z3,z4,z302,z5,z6]),(0,[z47,z173,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z167,z2,z3,z4,z149,z5,z6]),(0,[z1,z2,z3,z304,z4,z5,z6]),(0,[z1,z2,z3,z305,z4,z5,z6]),(0,[z306,z2,z3,z4,z5,z6,z15]),(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z308,z5,z6])],[(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z310]),(0,[z1,z311,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z312]),(0,[z1,z2,z3,z4,z5,z6,z73]),(0,[z313,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z15]),(0,[z1,z315,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z5,z244,z6])],[(0,[z1,z193,z3,z4,z5,z52,z6]),(0,[z2,z3,z78,z133,z4,z5,z6]),(0,[z1,z2,z18,z78,z4,z5,z6]),(0,[z1,z2,z3,z4,z178,z5,z6]),(1,[z2,z3,z4,z5,z6,z15]),(0,[z14,z2,z3,z4,z5,z245,z6]),(0,[z81,z1,z2,z3,z4,z88,z6]),(0,[z316,z1,z2,z3,z4,z5,z6])],[(0,[z14,z85,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z317,z6]),(1,[z318,z2,z3,z4,z5,z6]),(1,[z240,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z319])],[(0,[z1,z2,z148,z3,z4,z5,z6]),(0,[z77,z1,z2,z148,z4,z5,z6]),(0,[z114,z2,z148,z3,z4,z5,z6]),(0,[z1,z2,z232,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z81,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z320]),(0,[z1,z321,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z93,z5,z6])],[(0,[z187,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z39,z32,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z322,z6]),(0,[z1,z2,z3,z4,z323,z5,z6]),(0,[z1,z100,z2,z3,z4,z5,z6]),(0,[z1,z2,z324,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z211])],[(0,[z1,z2,z325,z3,z4,z5,z6]),(0,[z1,z2,z3,z26,z4,z5,z6]),(0,[z1,z23,z2,z3,z4,z88,z6]),(0,[z1,z2,z3,z4,z5,z326,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z182,z6]),(0,[z1,z109,z2,z3,z4,z5,z15]),(0,[z327,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z58,z4,z5,z6]),(0,[z14,z1,z2,z3,z4,z5,z24]),(0,[z1,z180,z2,z3,z4,z5,z6])],[(0,[z328,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z11]),(0,[z14,z2,z3,z4,z329,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z330])],[(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z331])],[(0,[z1,z2,z3,z332,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z333,z6]),(0,[z1,z2,z3,z40,z4,z5,z6]),(0,[z187,z100,z2,z3,z4,z5,z6]),(1,[z1,z334,z3,z4,z5,z6])],[(0,[z167,z2,z3,z4,z5,z6,z15]),(0,[z2,z3,z4,z145,z5,z6,z15]),(0,[z335,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z40,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z138])],[],[(0,[z1,z2,z3,z4,z336,z5,z6]),(0,[z1,z2,z3,z4,z337,z5,z6]),(0,[z1,z3,z4,z5,z52,z6,z11]),(0,[z1,z284,z2,z3,z88,z5,z6]),(0,[z200,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z106,z2,z3,z4,z5,z6,z15]),(0,[z339,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z340]),(0,[z1,z2,z3,z4,z341,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z244,z6,z138]),(0,[z1,z2,z3,z4,z5,z342,z6])]],
   [[(0,[z1,z2,z3,z343,z4,z5,z6]),(0,[z22,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z344,z4,z5,z6]),(1,[z1,z2,z3,z5,z275,z6]),(1,[z1,z345,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z14,z2,z3,z4,z13,z5,z6]),(0,[z2,z3,z4,z5,z244,z6,z15]),(0,[z347,z14,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z63,z5,z6]),(0,[z348,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z349])],[(0,[z1,z2,z3,z4,z5,z350,z6])],[(1,[z14,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z351,z4,z5,z6]),(0,[z352,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z353]),(0,[z1,z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z355,z5,z6])],[(0,[z298,z1,z2,z3,z13,z5,z6]),(0,[z27,z1,z42,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z356]),(0,[z1,z2,z3,z4,z5,z6,z253])],[(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z358,z1,z2,z3,z4,z5,z6])],[(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z1,z22,z3,z4,z5,z207,z6]),(0,[z1,z2,z3,z360,z4,z5,z6]),(0,[z1,z361,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z4,z244,z6])]],
   [[(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z363,z5,z6]),(1,[z1,z2,z3,z364,z5,z6])],[(0,[z1,z365,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z366,z5,z6]),(0,[z2,z3,z4,z5,z6,z6,z15]),(0,[z14,z1,z2,z3,z4,z5,z15]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z27,z1,z2,z18,z4,z5,z6]),(0,[z106,z1,z334,z3,z4,z5,z6]),(0,[z1,z2,z368,z3,z4,z5,z6])],[(0,[z1,z2,z3,z133,z4,z5,z6]),(0,[z1,z2,z369,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z178,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z370]),(1,[z1,z2,z3,z93,z244,z6])],[(0,[z1,z2,z3,z4,z371,z5,z6]),(0,[z1,z2,z3,z372,z4,z5,z6]),(0,[z2,z3,z4,z5,z373,z245,z6])],[(0,[z1,z2,z3,z4,z5,z6,z115]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z145,z5,z6]),(0,[z1,z2,z3,z375,z4,z5,z6])],[(0,[z27,z2,z3,z4,z5,z6,z15]),(0,[z14,z2,z3,z4,z376,z5,z6]),(0,[z10,z1,z118,z3,z4,z5,z6]),(0,[z1,z2,z3,z377,z4,z5,z6]),(1,[z378,z2,z3,z4,z5,z6])],[(0,[z1,z2,z379,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z86,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z52,z6]),(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z68,z71])],[(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z2,z148,z3,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z34,z6,z15]),(0,[z10,z1,z3,z26,z4,z5,z6]),(0,[z10,z226,z2,z3,z4,z5,z6]),(0,[z1,z43,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z382,z6]),(0,[z1,z383,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z384,z5,z6]),(0,[z1,z2,z3,z4,z5,z385,z6]),(0,[z106,z1,z2,z155,z4,z5,z6])],[(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z387,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z388]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z390,z2,z3,z4,z5,z6])],[(0,[z1,z284,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z128,z5,z91,z6])],[(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z392])],[(0,[z1,z2,z3,z4,z5,z393,z6]),(1,[z14,z2,z3,z4,z5,z15]),(0,[z14,z2,z3,z4,z5,z207,z6]),(0,[z62,z1,z16,z3,z4,z5,z6])],[(0,[z2,z193,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z394,z6]),(1,[z1,z16,z3,z26,z5,z6]),(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z197,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z145,z5,z25])],[(0,[z1,z2,z3,z4,z5,z6,z396]),(0,[z1,z2,z397,z3,z4,z5,z6]),(0,[z37,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z398,z3,z4,z5,z6]),(0,[z1,z3,z26,z4,z5,z52,z6]),(0,[z1,z2,z3,z4,z5,z399,z6]),(0,[z187,z1,z2,z72,z4,z5,z6])],[(0,[z2,z3,z128,z4,z5,z6,z15]),(0,[z1,z400,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z401,z2,z3,z4,z5,z6])],[(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z232,z4,z5,z6]),(0,[z2,z3,z4,z366,z5,z6,z15]),(0,[z14,z2,z3,z4,z5,z25,z6]),(0,[z1,z2,z3,z4,z5,z403,z6]),(0,[z1,z2,z3,z4,z5,z6,z404]),(1,[z137,z1,z3,z4,z5,z6]),(0,[z106,z1,z180,z3,z4,z5,z6])],[(0,[z77,z85,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z405,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z295]),(0,[z1,z2,z3,z184,z4,z5,z6])],[(0,[z1,z2,z148,z18,z4,z5,z6]),(0,[z114,z1,z237,z3,z4,z5,z6]),(0,[z98,z62,z1,z2,z3,z5,z6]),(0,[z81,z1,z3,z4,z5,z52,z6]),(0,[z1,z2,z3,z406,z4,z5,z6]),(0,[z407,z1,z2,z3,z4,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z44,z409,z3,z4,z5,z6])],[(1,[z1,z2,z3,z216,z5,z6]),(0,[z410,z1,z2,z3,z4,z5,z6]),(1,[z411,z2,z3,z4,z5,z6])],[(0,[z192,z1,z2,z3,z4,z5,z6]),(1,[z1,z165,z3,z4,z5,z6])],[(0,[z1,z412,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z413,z4,z5,z6]),(0,[z1,z3,z4,z5,z207,z6,z11]),(0,[z414,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z4,z19,z5,z6]),(0,[z49,z2,z3,z4,z5,z34,z6]),(0,[z1,z2,z3,z4,z5,z6,z415])],[(0,[z81,z2,z3,z4,z5,z6,z15]),(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z1,z417,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z418,z6]),(1,[z10,z1,z3,z4,z5,z11]),(0,[z1,z2,z3,z4,z5,z419,z6])],[(1,[z298,z2,z3,z13,z5,z6]),(0,[z14,z2,z3,z32,z4,z5,z6]),(0,[z1,z118,z3,z4,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z420,z6])],[(0,[z1,z2,z3,z4,z5,z6,z421]),(1,[z1,z118,z299,z4,z5,z6]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z19,z5,z245,z6]),(0,[z1,z2,z3,z4,z5,z6,z422]),(0,[z106,z1,z2,z3,z4,z145,z6])],[(0,[z81,z10,z1,z3,z4,z5,z6]),(0,[z1,z258,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z423,z6]),(0,[z205,z2,z3,z4,z5,z6,z15]),(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z88,z5,z275,z6]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z426,z6]),(0,[z1,z2,z3,z93,z5,z244,z6]),(0,[z2,z3,z4,z5,z91,z6,z427])],[(1,[z77,z2,z148,z4,z5,z6]),(0,[z14,z2,z299,z3,z4,z5,z6]),(0,[z428,z1,z2,z3,z4,z5,z6])],[(0,[z50,z1,z2,z3,z4,z5,z322]),(0,[z37,z1,z118,z3,z4,z5,z6]),(1,[z1,z2,z3,z429,z5,z6]),(0,[z1,z2,z3,z4,z430,z5,z6]),(0,[z1,z2,z3,z4,z5,z431,z6])],[(0,[z167,z1,z2,z148,z4,z5,z6]),(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z1,z2,z433,z3,z4,z5,z6]),(0,[z1,z2,z3,z434,z4,z5,z6]),(0,[z37,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z436,z6]),(0,[z1,z2,z3,z4,z5,z437,z6])]],
   [[(0,[z298,z90,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z1,z439,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z440,z4,z5,z6]),(0,[z1,z2,z3,z4,z145,z25,z6])],[(0,[z2,z3,z133,z4,z13,z5,z6]),(0,[z10,z2,z3,z4,z5,z6,z15]),(0,[z14,z2,z3,z4,z5,z441,z6]),(0,[z1,z2,z3,z4,z5,z442,z6]),(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z1,z2,z3,z4,z5,z6,z138])],[(0,[z14,z2,z3,z128,z4,z5,z6]),(0,[z1,z2,z3,z4,z444,z5,z6]),(1,[z1,z2,z3,z4,z5,z356]),(1,[z1,z409,z3,z4,z5,z6])],[(0,[z50,z192,z2,z3,z4,z5,z6]),(0,[z298,z1,z2,z3,z133,z5,z6]),(0,[z1,z2,z445,z3,z4,z5,z6])],[(1,[z192,z193,z3,z4,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z14,z298,z2,z3,z4,z5,z6]),(0,[z12,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z6,z447]),(0,[z448,z1,z2,z3,z4,z5,z6]),(0,[z1,z449,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z128,z5,z6])],[(0,[z450,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z451,z6]),(0,[z452,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z39,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z453,z5,z6]),(0,[z1,z2,z3,z454,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z353,z15]),(0,[z14,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z455]),(0,[z1,z16,z3,z26,z4,z5,z6]),(0,[z2,z3,z4,z5,z456,z244,z6])]],
   [[(0,[z50,z1,z2,z3,z4,z5,z29]),(0,[z1,z457,z2,z3,z4,z5,z6]),(0,[z2,z3,z440,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z458,z5,z6]),(0,[z1,z2,z3,z4,z145,z5,z71])],[(0,[z1,z2,z3,z459,z4,z5,z6]),(0,[z62,z2,z3,z4,z5,z6,z15]),(0,[z14,z14,z2,z3,z4,z5,z6]),(1,[z1,z2,z39,z32,z5,z6]),(0,[z1,z2,z3,z4,z364,z5,z6])],[(0,[z460,z1,z2,z3,z4,z5,z6]),(0,[z1,z461,z2,z3,z4,z5,z6])],[(0,[z114,z2,z3,z4,z5,z6,z15]),(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z27,z223,z2,z3,z4,z5,z6]),(1,[z49,z2,z3,z4,z5,z6]),(0,[z1,z2,z462,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z463,z6]),(0,[z1,z2,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z464,z4,z5,z6]),(0,[z1,z118,z3,z4,z5,z207,z6]),(0,[z1,z465,z2,z3,z4,z5,z6])],[(0,[z62,z10,z1,z3,z4,z5,z6]),(0,[z62,z1,z2,z3,z5,z244,z6]),(0,[z466,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z13,z5,z244,z6]),(0,[z114,z1,z2,z3,z4,z149,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z6]),(0,[z1,z2,z3,z220,z4,z5,z6]),(0,[z1,z2,z469,z3,z4,z5,z6])],[(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z4,z5,z55,z6]),(0,[z123,z2,z3,z4,z5,z91,z6])]],
   [[(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z78,z4,z5,z86,z6]),(0,[z1,z2,z473,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z5,z6,z138]),(1,[z1,z3,z4,z5,z6,z474]),(0,[z1,z2,z3,z4,z5,z6,z211])],[(0,[z90,z2,z3,z4,z5,z6,z15]),(0,[z1,z237,z2,z3,z4,z5,z6]),(0,[z1,z475,z2,z3,z4,z5,z6]),(0,[z14,z205,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z6,z11]),(0,[z476,z1,z2,z3,z4,z5,z6])],[(0,[z114,z167,z2,z3,z4,z5,z6]),(0,[z2,z3,z26,z4,z5,z6,z15]),(0,[z98,z2,z3,z4,z5,z6,z15]),(0,[z1,z109,z23,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z477,z6]),(0,[z478,z1,z2,z3,z4,z5,z6])],[(0,[z14,z22,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z1,z2,z480,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z6])],[(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z14,z90,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z128,z4,z5,z91])],[(1,[z14,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z44,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z71]),(0,[z1,z2,z481,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z482,z6]),(1,[z2,z3,z4,z5,z25,z15]),(0,[z1,z2,z3,z4,z5,z483,z6]),(0,[z1,z2,z3,z4,z484,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z485,z6]),(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z27,z258,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z72,z18,z4,z5,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z486,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z487])],[(0,[z114,z85,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z488]),(0,[z1,z2,z3,z4,z5,z489,z6]),(0,[z1,z2,z3,z4,z5,z490,z6])],[(0,[z491,z1,z2,z3,z4,z5,z6]),(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z494,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z495,z6]),(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z497]),(0,[z27,z1,z2,z3,z429,z5,z6]),(0,[z177,z2,z3,z4,z5,z245,z6]),(0,[z1,z2,z3,z93,z4,z244,z6]),(0,[z1,z2,z3,z498,z4,z5,z6])],[(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z500,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z501,z4,z5,z6])],[(0,[z1,z23,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z502,z4,z5,z6]),(0,[z339,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z503,z5,z6]),(1,[z187,z1,z2,z4,z5,z68]),(1,[z2,z3,z4,z5,z6,z35]),(0,[z1,z2,z3,z4,z5,z91,z6])],[(0,[z1,z2,z3,z4,z5,z504,z6]),(0,[z14,z2,z3,z4,z5,z86,z6]),(0,[z1,z23,z3,z38,z4,z5,z6]),(0,[z1,z118,z299,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z25])],[(0,[z1,z193,z3,z4,z5,z207,z6]),(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z347,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z506,z5,z6]),(0,[z1,z3,z4,z88,z5,z52,z6]),(0,[z1,z2,z4,z5,z245,z6,z68]),(0,[z507,z1,z2,z3,z4,z5,z6]),(1,[z1,z12,z2,z44,z3,z6]),(0,[z154,z1,z2,z3,z4,z5,z6])],[(0,[z1,z508,z2,z3,z4,z5,z6]),(1,[z123,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z509,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z510,z6]),(0,[z1,z2,z3,z4,z5,z511,z6]),(0,[z294,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z48]),(0,[z1,z2,z3,z512,z4,z5,z6])],[(0,[z10,z1,z193,z3,z4,z5,z6]),(0,[z513,z1,z2,z3,z4,z5,z6]),(0,[z1,z514,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z88,z5,z6]),(0,[z515,z1,z2,z3,z4,z5,z6]),(0,[z1,z109,z3,z4,z5,z52,z6]),(0,[z98,z1,z345,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z516,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z517,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z518]),(0,[z10,z1,z3,z38,z4,z5,z6])],[(0,[z519,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z520,z3,z4,z5,z6]),(1,[z167,z2,z78,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z24,z6])],[(0,[z1,z2,z3,z4,z5,z6,z521]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z1,z2,z3,z523,z4,z5,z6]),(0,[z1,z2,z3,z4,z524,z5,z6]),(0,[z1,z2,z525,z3,z4,z5,z6])],[(0,[z114,z2,z3,z133,z4,z5,z6])],[(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z1,z16,z2,z3,z5,z244,z6]),(0,[z1,z2,z3,z4,z527,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z528])],[(0,[z14,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z529,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z13,z5,z6]),(0,[z14,z2,z3,z4,z149,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z421]),(0,[z62,z1,z12,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z530,z6]),(0,[z531,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z227,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z534,z14,z2,z3,z4,z5,z6]),(0,[z187,z1,z2,z3,z4,z5,z34]),(0,[z1,z2,z3,z535,z4,z5,z6])],[(0,[z1,z2,z536,z3,z4,z5,z6]),(0,[z90,z2,z3,z133,z4,z5,z6]),(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z538]),(1,[z2,z3,z4,z5,z456,z6]),(1,[z94,z2,z3,z4,z5,z6])],[(0,[z1,z2,z78,z4,z5,z245,z6]),(0,[z539,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z15,z71]),(0,[z540,z14,z2,z3,z4,z5,z6])],[(0,[z298,z2,z3,z78,z4,z5,z6]),(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z544]),(1,[z1,z545,z3,z4,z5,z6])],[(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z547,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z427])],[(1,[z1,z2,z3,z4,z5,z322]),(0,[z1,z12,z2,z3,z5,z55,z6])]],
   [[(1,[z90,z2,z3,z133,z5,z6]),(0,[z1,z2,z3,z4,z548,z5,z6]),(0,[z1,z3,z26,z4,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z549]),(0,[z550,z1,z2,z3,z4,z5,z6]),(0,[z551,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z373,z6])],[(0,[z1,z2,z552,z3,z4,z5,z6]),(0,[z1,z299,z3,z26,z4,z5,z6]),(0,[z106,z1,z2,z3,z364,z5,z6])],[(0,[z2,z3,z4,z5,z55,z6,z15]),(0,[z47,z2,z3,z4,z5,z6,z15])],[(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z85,z2,z3,z78,z4,z5,z6]),(0,[z553,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z183,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z54,z6])],[(0,[z307,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z376,z5,z6]),(0,[z1,z2,z3,z4,z5,z554,z6])],[(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z555,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z556,z6]),(0,[z1,z2,z3,z4,z5,z6,z557]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z558])],[(0,[z114,z1,z2,z3,z216,z5,z6]),(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z1,z72,z3,z220,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z34]),(0,[z1,z2,z560,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z253]),(0,[z1,z411,z2,z3,z4,z5,z6])],[(0,[z114,z1,z165,z3,z4,z5,z6]),(1,[z205,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z6,z68]),(0,[z47,z1,z2,z3,z128,z5,z6]),(0,[z1,z2,z561,z3,z4,z5,z6]),(0,[z1,z2,z334,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z562,z6]),(0,[z1,z2,z3,z4,z5,z34,z71])],[(0,[z1,z2,z563,z3,z4,z5,z6]),(0,[z298,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z15]),(0,[z206,z1,z2,z3,z4,z5,z6])],[(0,[z14,z2,z148,z3,z4,z5,z6]),(0,[z2,z3,z4,z19,z5,z6,z15]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z44,z3,z5,z6])],[(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z93,z4,z5,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z207,z6]),(0,[z1,z2,z3,z567,z4,z5,z6])],[(0,[z1,z2,z345,z3,z4,z5,z6])],[(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z569,z2,z3,z4,z5,z6]),(0,[z225,z14,z2,z3,z4,z5,z6]),(0,[z570,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z571,z3,z4,z5,z6])],[(0,[z225,z1,z2,z3,z4,z5,z6]),(0,[z192,z1,z193,z3,z4,z5,z6]),(0,[z1,z572,z2,z3,z4,z5,z6]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z573,z6]),(0,[z294,z1,z3,z4,z5,z55,z6]),(0,[z1,z2,z3,z574,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z86,z6,z15]),(0,[z14,z23,z2,z3,z4,z5,z6]),(0,[z1,z23,z3,z4,z88,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z576,z6]),(0,[z577,z1,z2,z3,z4,z5,z6]),(0,[z14,z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z578]),(0,[z10,z1,z2,z3,z4,z5,z207]),(0,[z98,z1,z2,z3,z5,z55,z6]),(1,[z41,z2,z3,z4,z5,z6])],[(0,[z14,z2,z3,z78,z4,z5,z6]),(0,[z298,z77,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z88,z5,z6,z15]),(0,[z1,z16,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z579,z6]),(0,[z47,z1,z2,z3,z5,z6,z138]),(0,[z1,z2,z3,z4,z5,z580,z6])],[(0,[z1,z2,z3,z4,z5,z581,z6]),(0,[z1,z582,z2,z3,z4,z5,z6]),(0,[z14,z12,z2,z3,z4,z5,z6]),(0,[z37,z1,z3,z26,z4,z5,z6]),(0,[z1,z3,z26,z4,z5,z207,z6]),(0,[z1,z2,z583,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z15,z71]),(0,[z1,z2,z3,z584,z4,z5,z6]),(0,[z98,z1,z2,z4,z5,z55,z6]),(0,[z47,z1,z2,z3,z4,z5,z91])],[(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z77,z2,z3,z4,z5,z86,z6]),(0,[z1,z2,z3,z4,z5,z586,z6]),(0,[z1,z2,z3,z587,z4,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z11]),(0,[z1,z2,z72,z4,z5,z245,z6]),(0,[z1,z2,z3,z4,z5,z6,z588]),(0,[z106,z411,z2,z3,z4,z5,z6])],[(0,[z589,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z590,z6]),(1,[z1,z197,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z591]),(0,[z592,z1,z2,z3,z4,z5,z6]),(1,[z154,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z593,z5,z6]),(0,[z2,z3,z4,z5,z573,z6,z15]),(0,[z62,z1,z3,z4,z63,z5,z6]),(0,[z1,z2,z3,z594,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z48,z6]),(0,[z1,z545,z72,z3,z4,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z85,z2,z3,z4,z149,z6]),(0,[z250,z1,z2,z3,z4,z5,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z81,z1,z3,z4,z5,z207,z6]),(0,[z1,z2,z3,z4,z596,z5,z6]),(0,[z1,z2,z3,z32,z4,z5,z6])],[(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z598,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z599,z6]),(0,[z1,z2,z3,z4,z600,z5,z6]),(0,[z601,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z602,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z603,z6])],[(0,[z1,z2,z3,z4,z5,z604,z6]),(0,[z2,z3,z4,z149,z5,z6,z15]),(0,[z605,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z606,z5,z6]),(0,[z1,z2,z3,z4,z607,z5,z6]),(0,[z608,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z299,z3,z4,z5,z6]),(0,[z81,z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z609,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z610]),(1,[z1,z43,z3,z4,z5,z6])],[(0,[z1,z611,z2,z3,z4,z5,z6]),(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z613,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z115]),(0,[z1,z614,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z38,z4,z5,z6]),(0,[z62,z1,z2,z39,z3,z5,z6]),(0,[z615,z1,z2,z3,z4,z5,z6]),(1,[z106,z1,z2,z3,z4,z71])],[(0,[z1,z2,z3,z4,z616,z5,z6]),(0,[z1,z2,z617,z3,z4,z5,z6])],[(0,[z618,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z271,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z619,z6]),(0,[z1,z2,z3,z4,z5,z620,z6]),(0,[z1,z2,z3,z4,z5,z621,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6])],[(0,[z2,z3,z133,z4,z149,z5,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z624,z6]),(0,[z1,z2,z3,z4,z5,z441,z6]),(0,[z1,z2,z3,z4,z625,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z626]),(0,[z27,z1,z2,z4,z5,z245,z6])],[(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z1,z23,z2,z3,z4,z52,z6]),(0,[z1,z2,z629,z3,z4,z5,z6]),(1,[z265,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z128,z4,z5,z6]),(0,[z1,z2,z3,z5,z91,z6,z138])],[(0,[z1,z306,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z630,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z631])],[(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z633,z6]),(0,[z1,z2,z3,z4,z5,z6,z634]),(0,[z114,z298,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z133,z5,z244,z6]),(0,[z2,z3,z4,z5,z91,z6,z15]),(0,[z1,z2,z3,z4,z5,z6,z635]),(0,[z1,z2,z3,z636,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z637,z6])],[(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z50,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z639,z6]),(0,[z1,z2,z3,z4,z5,z6,z640])],[(0,[z1,z2,z3,z4,z5,z6,z29]),(0,[z1,z2,z3,z4,z5,z6,z70]),(0,[z298,z2,z3,z4,z149,z5,z6]),(0,[z1,z2,z3,z4,z5,z641,z6]),(0,[z1,z2,z3,z642,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z643,z6]),(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z644])],[(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z14,z77,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z646]),(0,[z1,z2,z3,z4,z5,z647,z6])]],
   [[(0,[z114,z14,z2,z3,z4,z5,z6]),(0,[z14,z1,z212,z3,z4,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z187,z1,z2,z4,z5,z6,z68]),(0,[z1,z545,z2,z3,z4,z5,z6]),(0,[z1,z649,z2,z3,z4,z5,z6]),(1,[z1,z2,z368,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z650,z6]),(0,[z118,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z25,z15]),(0,[z1,z2,z651,z3,z4,z5,z6])],[(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z62,z1,z3,z4,z5,z207,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z652,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z653,z6]),(0,[z1,z2,z3,z4,z5,z6,z654]),(0,[z240,z1,z2,z3,z4,z5,z6])],[(0,[z85,z2,z3,z4,z149,z5,z6]),(0,[z1,z118,z2,z38,z4,z5,z6]),(0,[z200,z10,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z207,z6,z73]),(1,[z173,z2,z3,z4,z5,z6]),(0,[z106,z1,z2,z3,z4,z6,z71])],[(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z133,z5,z6]),(0,[z2,z3,z4,z5,z207,z6,z15]),(0,[z2,z3,z4,z5,z6,z518,z15]),(0,[z187,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z656]),(1,[z1,z67,z3,z4,z5,z6]),(0,[z378,z2,z3,z4,z5,z244,z6])],[(0,[z37,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z657,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z35]),(0,[z1,z658,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z659,z4,z5,z6]),(0,[z2,z3,z4,z13,z5,z6,z15]),(1,[z1,z2,z3,z4,z5,z182]),(0,[z98,z14,z2,z3,z4,z5,z6]),(0,[z14,z2,z72,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z660,z3,z4,z5,z6]),(0,[z1,z2,z3,z661,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z11]),(0,[z1,z2,z3,z662,z4,z5,z6]),(0,[z1,z2,z39,z3,z5,z55,z6]),(0,[z1,z2,z3,z429,z4,z5,z6])],[(0,[z1,z2,z663,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z664])],[(0,[z77,z2,z148,z3,z4,z5,z6]),(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z1,z3,z38,z4,z5,z52,z6]),(0,[z62,z1,z2,z3,z26,z5,z6]),(0,[z1,z2,z3,z4,z5,z666,z6]),(0,[z27,z1,z2,z3,z4,z5,z356]),(0,[z1,z2,z3,z128,z4,z5,z138])],[(0,[z1,z22,z2,z3,z4,z5,z6]),(0,[z192,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z148,z4,z5,z245,z6]),(1,[z14,z212,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z329,z5,z6]),(1,[z1,z2,z3,z99,z5,z6])],[(0,[z667,z1,z2,z3,z4,z5,z6]),(0,[z167,z14,z2,z3,z4,z5,z6]),(0,[z298,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z668,z6]),(0,[z14,z2,z3,z4,z5,z244,z6]),(0,[z1,z118,z2,z299,z4,z5,z6]),(0,[z1,z2,z3,z4,z669,z5,z6])],[(0,[z1,z2,z3,z4,z670,z5,z6]),(0,[z1,z2,z3,z4,z671,z5,z6]),(0,[z2,z3,z4,z5,z6,z15,z68]),(0,[z14,z16,z2,z3,z4,z5,z6]),(0,[z37,z62,z1,z3,z4,z5,z6]),(0,[z672,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(1,[z227,z2,z3,z4,z5,z6]),(0,[z106,z1,z2,z368,z4,z5,z6])],[(0,[z1,z2,z3,z673,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z144]),(0,[z106,z14,z2,z3,z4,z5,z6]),(0,[z1,z674,z2,z3,z4,z5,z6]),(0,[z1,z2,z409,z3,z4,z5,z6])]],
   [[(0,[z1,z675,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z676,z6]),(0,[z1,z2,z3,z4,z5,z677,z6]),(0,[z1,z109,z2,z3,z4,z5,z11]),(0,[z98,z1,z2,z39,z4,z5,z6])],[(0,[z1,z2,z678,z3,z4,z5,z6]),(0,[z1,z2,z3,z679,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z680,z6]),(0,[z1,z2,z3,z4,z681,z5,z6]),(0,[z106,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z682,z6]),(0,[z1,z2,z3,z4,z5,z683,z6])],[(0,[z14,z192,z2,z3,z4,z5,z6]),(0,[z62,z1,z299,z3,z4,z5,z6]),(1,[z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z245,z6])],[(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z114,z2,z3,z4,z5,z86,z6]),(0,[z1,z2,z3,z4,z5,z86,z6]),(0,[z2,z299,z3,z4,z5,z6,z15]),(0,[z1,z299,z3,z38,z4,z5,z6]),(0,[z1,z2,z3,z685,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z245,z6]),(0,[z1,z2,z3,z686,z4,z5,z6]),(0,[z1,z2,z44,z3,z93,z4,z6])],[(0,[z2,z148,z3,z78,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z456,z6]),(0,[z687,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z688,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z133,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z71]),(0,[z1,z2,z3,z4,z5,z689,z6])],[(0,[z1,z2,z690,z3,z4,z5,z6]),(0,[z534,z1,z2,z3,z4,z5,z6]),(0,[z246,z14,z2,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z19,z5,z6]),(0,[z691,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z4,z5,z6,z68]),(0,[z692,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z474,z71])]],
   [[(0,[z1,z2,z3,z4,z88,z5,z6]),(1,[z1,z23,z3,z4,z88,z6]),(0,[z318,z2,z3,z4,z5,z207,z6]),(0,[z1,z2,z3,z4,z5,z6,z427]),(0,[z94,z2,z3,z4,z5,z25,z6])],[(0,[z1,z2,z3,z4,z5,z693,z6]),(0,[z1,z2,z3,z694,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z695,z6])],[(0,[z1,z2,z696,z3,z4,z5,z6]),(0,[z1,z2,z697,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z373,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z72,z4,z5,z34]),(0,[z106,z1,z2,z3,z4,z5,z25])],[(0,[z2,z39,z3,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z6,z15,z138]),(0,[z1,z23,z3,z4,z5,z6,z11]),(0,[z1,z3,z4,z88,z5,z207,z6])],[(0,[z50,z1,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z699,z4,z5,z6]),(0,[z14,z2,z39,z3,z4,z5,z6]),(1,[z62,z1,z3,z63,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z474])],[(0,[z1,z2,z3,z700,z4,z5,z6]),(0,[z2,z72,z3,z4,z5,z6,z15]),(0,[z27,z14,z2,z3,z4,z5,z6]),(0,[z1,z2,z701,z3,z4,z5,z6])],[(0,[z1,z2,z702,z3,z4,z5,z6]),(0,[z1,z2,z3,z703,z4,z5,z6]),(0,[z1,z109,z3,z4,z5,z207,z6]),(1,[z98,z1,z2,z5,z55,z6]),(0,[z1,z2,z18,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6])],[(1,[z1,z2,z255,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z1,z2,z3,z32,z5,z244,z6]),(0,[z1,z2,z706,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z3,z4,z5,z707,z6]),(0,[z137,z3,z4,z5,z6,z15]),(0,[z37,z1,z708,z4,z5,z6]),(0,[z709,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z710]),(0,[z265,z2,z3,z4,z5,z6]),(0,[z2,z3,z133,z711,z5,z6]),(0,[z14,z2,z155,z4,z5,z6]),(0,[z712,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z713,z6])],[(0,[z1,z714,z3,z4,z5,z6]),(0,[z1,z2,z715,z4,z5,z6]),(0,[z127,z1,z2,z3,z5,z6]),(0,[z47,z173,z2,z3,z5,z138])],[(0,[z50,z22,z3,z4,z5,z322]),(1,[z79,z3,z4,z5,z15]),(0,[z223,z2,z3,z4,z5,z356])],[(0,[z114,z2,z3,z4,z86,z115]),(0,[z62,z1,z560,z3,z5,z6]),(0,[z716,z2,z3,z4,z5,z6]),(0,[z98,z294,z1,z5,z55,z6])],[(0,[z534,z2,z3,z4,z5,z115]),(0,[z1,z717,z3,z4,z5,z6]),(0,[z187,z227,z2,z4,z5,z68]),(0,[z1,z2,z3,z718,z5,z6])],[(0,[z298,z2,z3,z178,z5,z6]),(0,[z106,z1,z2,z3,z364,z71]),(0,[z1,z3,z4,z5,z6,z719])],[(0,[z1,z2,z18,z4,z337,z6]),(0,[z2,z255,z4,z5,z6,z15]),(0,[z109,z3,z4,z5,z126,z15]),(0,[z1,z334,z3,z364,z5,z6])]],
   [[(0,[z50,z79,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z720]),(0,[z1,z2,z3,z4,z5,z721]),(0,[z1,z2,z3,z5,z6,z722])],[(0,[z2,z3,z305,z4,z5,z15]),(0,[z12,z2,z44,z3,z6,z15]),(0,[z723,z2,z3,z4,z5,z6])],[(0,[z2,z3,z133,z5,z573,z6]),(0,[z14,z2,z3,z178,z5,z6]),(0,[z2,z3,z724,z5,z6,z15]),(0,[z2,z3,z4,z366,z6,z518]),(0,[z14,z2,z725,z4,z5,z6]),(0,[z62,z14,z3,z63,z5,z6]),(0,[z14,z180,z3,z4,z5,z6]),(0,[z1,z2,z3,z726,z5,z6]),(0,[z27,z1,z2,z4,z245,z356]),(0,[z1,z3,z727,z4,z5,z6]),(0,[z1,z2,z368,z184,z5,z6]),(0,[z94,z728,z3,z4,z5,z6])],[(0,[z1,z2,z3,z724,z5,z6]),(0,[z173,z2,z3,z4,z5,z6]),(0,[z165,z3,z4,z5,z6,z15]),(0,[z1,z2,z729,z4,z5,z6]),(0,[z1,z708,z38,z4,z5,z6]),(0,[z10,z1,z3,z4,z5,z455]),(0,[z294,z1,z12,z3,z5,z6])],[(0,[z98,z14,z2,z5,z55,z6]),(0,[z213,z1,z3,z4,z52,z6]),(0,[z2,z3,z4,z5,z730,z6]),(0,[z1,z2,z3,z4,z524,z25]),(0,[z1,z2,z155,z4,z5,z25])],[(0,[z1,z2,z232,z4,z5,z115]),(0,[z2,z3,z4,z5,z731,z15]),(0,[z240,z1,z3,z4,z5,z15]),(0,[z200,z10,z3,z4,z5,z11]),(0,[z1,z732,z3,z4,z5,z6]),(0,[z733,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z184,z5,z6]),(0,[z734,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z128,z5,z722])],[(0,[z1,z2,z3,z735,z5,z6]),(0,[z736,z3,z4,z5,z6,z15]),(0,[z2,z737,z4,z5,z6,z15]),(0,[z1,z738,z3,z4,z5,z6]),(0,[z1,z3,z739,z4,z5,z6]),(0,[z1,z72,z220,z4,z5,z34])],[(0,[z1,z3,z4,z5,z6,z740]),(0,[z1,z237,z3,z4,z5,z115]),(0,[z1,z2,z3,z4,z5,z741])]],
   [[(0,[z1,z2,z3,z178,z5,z182]),(0,[z42,z3,z4,z5,z6,z15]),(0,[z258,z2,z3,z4,z5,z356])],[(0,[z2,z3,z4,z5,z322,z15]),(0,[z1,z23,z3,z4,z96,z6]),(0,[z1,z742,z3,z4,z5,z6]),(0,[z2,z3,z429,z5,z6,z15]),(0,[z1,z2,z3,z743,z5,z6]),(0,[z10,z1,z3,z4,z5,z744]),(0,[z1,z2,z3,z745,z5,z6]),(0,[z1,z2,z3,z4,z25,z746])],[(0,[z1,z747,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z102]),(0,[z2,z148,z255,z4,z5,z6]),(0,[z109,z23,z3,z4,z5,z15]),(0,[z687,z2,z3,z4,z5,z15]),(0,[z1,z3,z4,z5,z6,z748])],[(0,[z450,z2,z3,z4,z5,z15]),(0,[z2,z148,z4,z5,z653,z6]),(0,[z749,z2,z3,z4,z5,z6]),(0,[z1,z2,z39,z146,z5,z6]),(0,[z98,z1,z2,z5,z750,z6])],[(0,[z1,z212,z3,z4,z5,z6]),(0,[z118,z299,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z479,z15]),(0,[z471,z1,z38,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z751])],[(0,[z1,z3,z4,z5,z6,z744])],[(0,[z114,z2,z3,z4,z86,z182]),(0,[z1,z3,z220,z4,z5,z6]),(0,[z1,z2,z39,z5,z750,z6]),(0,[z1,z2,z3,z20,z244,z6]),(0,[z752,z2,z3,z4,z5,z6])],[(0,[z1,z2,z753,z4,z5,z6])]],
   [[(0,[z1,z754,z3,z4,z5,z6]),(0,[z223,z2,z3,z4,z5,z6]),(0,[z163,z2,z148,z4,z5,z6]),(0,[z79,z2,z3,z4,z5,z15]),(0,[z14,z755,z3,z4,z5,z6]),(0,[z37,z1,z413,z4,z5,z6]),(0,[z380,z1,z38,z4,z5,z6]),(0,[z1,z3,z4,z5,z207,z312])],[(0,[z200,z22,z3,z4,z5,z6]),(0,[z85,z2,z3,z4,z329,z6]),(0,[z1,z2,z3,z4,z5,z756]),(0,[z2,z3,z4,z5,z25,z35])],[(0,[z226,z2,z3,z4,z5,z6]),(0,[z2,z757,z78,z4,z5,z6]),(0,[z1,z758,z3,z4,z5,z6]),(0,[z2,z72,z4,z5,z34,z35])],[(0,[z1,z2,z232,z4,z5,z6]),(0,[z759,z2,z3,z4,z5,z6]),(0,[z760,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z761]),(0,[z762,z1,z3,z4,z5,z6]),(0,[z378,z2,z3,z93,z244,z6]),(0,[z374,z1,z2,z3,z5,z138]),(0,[z411,z334,z3,z4,z5,z6])],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z2,z3,z133,z5,z624,z6]),(0,[z378,z2,z3,z133,z5,z6]),(0,[z14,z2,z3,z4,z145,z25]),(1,[z1,z708,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z764]),(0,[z98,z1,z2,z413,z5,z6]),(0,[z765,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z4,z5,z356]),(0,[z407,z1,z2,z3,z4,z71])],[(0,[z1,z237,z3,z4,z5,z6]),(0,[z22,z212,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z731]),(0,[z766,z2,z3,z4,z5,z6])],[(0,[z1,z2,z767,z4,z5,z6]),(0,[z768,z2,z3,z4,z5,z48]),(0,[z1,z2,z3,z4,z145,z25])],[(0,[z1,z2,z3,z769,z5,z6]),(0,[z1,z2,z232,z4,z5,z182]),(0,[z14,z79,z3,z4,z5,z6]),(0,[z1,z23,z3,z4,z88,z6]),(0,[z27,z1,z2,z4,z245,z6])]],
   [[(1,[z240,z3,z4,z5,z15]),(0,[z2,z4,z5,z6,z15,z770]),(0,[z2,z3,z4,z5,z6,z771]),(0,[z223,z2,z3,z99,z5,z6]),(0,[z27,z177,z2,z4,z245,z6]),(0,[z1,z3,z772,z4,z5,z6]),(0,[z773,z2,z3,z4,z5,z6])],[(0,[z774,z1,z2,z3,z5,z6]),(0,[z2,z255,z133,z4,z5,z6]),(0,[z1,z237,z3,z4,z5,z182]),(0,[z345,z3,z4,z5,z6,z15]),(0,[z775,z2,z3,z4,z5,z6]),(0,[z98,z1,z345,z5,z55,z6])],[(0,[z62,z3,z63,z5,z6,z15]),(0,[z127,z10,z1,z3,z5,z6]),(0,[z1,z776,z2,z3,z5,z6]),(0,[z10,z2,z3,z4,z5,z73]),(0,[z1,z3,z777,z4,z5,z6])],[(0,[z114,z2,z3,z4,z33,z6]),(0,[z10,z2,z3,z4,z5,z15]),(0,[z62,z1,z3,z63,z5,z6]),(0,[z27,z1,z2,z4,z778,z6]),(0,[z407,z1,z2,z4,z245,z6]),(0,[z779,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z780]),(0,[z1,z2,z72,z4,z5,z781]),(0,[z2,z3,z782,z4,z5,z6])],[(0,[z783,z2,z3,z4,z5,z6]),(0,[z81,z1,z3,z4,z52,z6]),(0,[z784,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z785,z5,z6])],[(0,[z258,z2,z3,z4,z5,z6]),(0,[z1,z786,z3,z4,z5,z6]),(0,[z98,z2,z5,z55,z6,z15]),(0,[z2,z3,z364,z5,z6,z15]),(0,[z347,z2,z3,z4,z441,z6]),(0,[z14,z2,z3,z429,z5,z6]),(0,[z37,z127,z1,z38,z5,z6]),(0,[z787,z2,z3,z4,z5,z6]),(0,[z98,z1,z2,z5,z55,z6]),(0,[z788,z2,z3,z4,z5,z6]),(0,[z789,z1,z3,z4,z5,z6])],[(0,[z1,z2,z790,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z791]),(0,[z792,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z793]),(0,[z2,z3,z4,z25,z15,z71]),(0,[z794,z1,z3,z4,z5,z6]),(0,[z27,z1,z2,z99,z245,z6]),(0,[z1,z2,z3,z128,z5,z59]),(0,[z1,z2,z155,z4,z5,z71])]],
   [[(0,[z1,z193,z3,z4,z5,z322]),(0,[z1,z2,z255,z178,z5,z6]),(0,[z250,z1,z2,z3,z4,z71]),(0,[z411,z2,z3,z364,z5,z6])],[(0,[z200,z2,z3,z4,z5,z322]),(0,[z2,z3,z440,z5,z573,z6]),(0,[z2,z3,z795,z5,z6,z15]),(0,[z1,z79,z3,z4,z5,z24]),(0,[z1,z299,z4,z5,z477,z6]),(0,[z1,z2,z3,z4,z796,z6]),(0,[z1,z2,z3,z797,z5,z6])],[(0,[z14,z409,z3,z4,z5,z6]),(0,[z1,z12,z2,z480,z3,z6]),(0,[z798,z2,z3,z4,z5,z6]),(0,[z1,z43,z3,z5,z244,z6]),(0,[z154,z334,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z29]),(0,[z1,z2,z3,z4,z5,z799]),(0,[z1,z2,z3,z4,z5,z800]),(1,[z2,z3,z4,z5,z731]),(0,[z2,z3,z4,z5,z385,z15]),(0,[z200,z2,z3,z4,z5,z15]),(0,[z14,z284,z2,z3,z5,z6]),(0,[z801,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z802,z5,z6]),(0,[z14,z2,z3,z4,z5,z668]),(0,[z534,z2,z3,z4,z5,z15]),(0,[z1,z803,z3,z4,z5,z6]),(0,[z390,z2,z3,z4,z5,z15]),(0,[z127,z14,z2,z3,z5,z6]),(0,[z804,z2,z3,z4,z5,z6]),(0,[z1,z12,z43,z3,z5,z6]),(0,[z106,z411,z2,z3,z4,z71])],[(0,[z177,z2,z255,z4,z5,z6]),(0,[z2,z3,z128,z5,z91,z15]),(0,[z1,z42,z3,z4,z5,z6]),(0,[z1,z2,z3,z805,z5,z6]),(0,[z258,z2,z3,z99,z5,z6]),(0,[z1,z2,z4,z5,z6,z806])],[(0,[z167,z2,z3,z4,z5,z115]),(0,[z114,z2,z255,z4,z86,z6]),(0,[z1,z3,z4,z5,z807,z6])],[(0,[z50,z22,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z393,z15]),(0,[z294,z1,z3,z4,z5,z6]),(0,[z1,z16,z3,z470,z5,z6]),(0,[z1,z2,z3,z429,z5,z48])]],
   [[(0,[z1,z2,z3,z4,z5,z808]),(0,[z14,z2,z39,z32,z5,z6]),(0,[z2,z3,z4,z5,z6,z809]),(0,[z1,z2,z3,z4,z5,z810])],[(0,[z1,z811,z3,z4,z5,z6]),(0,[z10,z118,z3,z4,z5,z15]),(0,[z3,z4,z5,z6,z15,z812]),(0,[z1,z23,z3,z4,z323,z6]),(0,[z813,z2,z3,z4,z5,z6]),(0,[z154,z2,z155,z4,z5,z6])],[(0,[z1,z2,z3,z814,z5,z6]),(0,[z815,z2,z3,z4,z5,z6])],[(0,[z10,z3,z26,z4,z5,z15])],[(0,[z1,z2,z3,z4,z816,z6]),(0,[z1,z817,z3,z4,z5,z6]),(0,[z476,z2,z3,z4,z5,z15]),(0,[z2,z3,z5,z275,z6,z15])],[(0,[z2,z3,z4,z5,z6,z15]),(0,[z192,z754,z3,z4,z5,z6]),(0,[z85,z2,z3,z4,z5,z115]),(0,[z1,z2,z3,z818,z5,z6]),(0,[z339,z79,z3,z4,z5,z6]),(0,[z1,z42,z3,z99,z5,z6]),(0,[z1,z2,z18,z4,z19,z6]),(1,[z1,z2,z4,z5,z781])],[(0,[z14,z2,z3,z4,z5,z198]),(0,[z3,z4,z5,z6,z15,z253]),(0,[z1,z819,z2,z3,z5,z6]),(1,[z1,z2,z5,z750,z6])],[(0,[z14,z2,z3,z4,z5,z201]),(0,[z318,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z731,z6]),(0,[z14,z3,z4,z5,z6,z474]),(0,[z820,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z88,z6,z370])]],
   [[(0,[z378,z2,z3,z13,z5,z6]),(0,[z2,z3,z4,z5,z562,z15]),(0,[z821,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z88,z807,z6])],[(0,[z14,z2,z3,z4,z5,z215]),(0,[z1,z237,z255,z4,z5,z6]),(0,[z1,z822,z3,z4,z5,z6]),(0,[z1,z2,z3,z82,z5,z6]),(0,[z1,z2,z3,z823,z5,z6]),(0,[z1,z2,z824,z4,z5,z6]),(0,[z2,z3,z825,z4,z5,z6]),(0,[z1,z2,z826,z4,z5,z6]),(0,[z137,z1,z12,z3,z5,z6])],[(0,[z2,z3,z4,z5,z6,z211]),(0,[z1,z79,z3,z4,z5,z15]),(0,[z14,z10,z3,z4,z5,z11]),(0,[z827,z2,z3,z4,z5,z6]),(0,[z154,z180,z3,z4,z5,z6]),(0,[z1,z728,z3,z4,z5,z6])],[(0,[z828,z2,z3,z4,z5,z6]),(0,[z829,z2,z3,z4,z5,z6])],[(0,[z307,z3,z4,z5,z6,z295]),(0,[z14,z830,z3,z4,z5,z6]),(0,[z14,z240,z3,z4,z5,z6]),(1,[z1,z3,z4,z807,z6]),(0,[z831,z2,z3,z4,z5,z6]),(0,[z832,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z356,z833]),(0,[z1,z334,z368,z4,z5,z6])],[(0,[z1,z165,z3,z216,z5,z6]),(0,[z109,z2,z3,z4,z5,z15]),(0,[z240,z3,z4,z5,z15,z71]),(0,[z14,z834,z3,z4,z5,z6]),(0,[z1,z696,z3,z4,z52,z6])],[(0,[z1,z830,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z835])],[(0,[z1,z334,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z40,z4,z5,z6]),(0,[z1,z16,z3,z814,z5,z6]),(0,[z836,z1,z3,z4,z5,z6])],[(0,[z2,z3,z133,z4,z5,z115]),(0,[z127,z1,z345,z3,z5,z6]),(0,[z1,z837,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z838])],[(0,[z2,z3,z435,z4,z5,z15]),(0,[z14,z345,z3,z4,z5,z6]),(0,[z1,z3,z26,z814,z5,z6]),(0,[z2,z3,z4,z5,z839,z6]),(0,[z1,z2,z3,z4,z145,z746])],[(0,[z1,z2,z3,z840,z5,z6]),(0,[z1,z841,z2,z3,z5,z6]),(0,[z1,z842,z3,z4,z5,z6]),(0,[z843,z2,z3,z4,z5,z6]),(0,[z62,z1,z3,z596,z5,z6]),(0,[z2,z3,z4,z5,z6,z844])],[(0,[z1,z2,z845,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z846]),(0,[z2,z30,z4,z5,z6,z353]),(0,[z2,z3,z93,z244,z6,z15]),(0,[z2,z3,z4,z145,z25,z15]),(0,[z1,z345,z3,z4,z5,z6]),(0,[z1,z3,z814,z63,z5,z6]),(0,[z1,z2,z3,z5,z275,z6]),(0,[z1,z701,z3,z26,z5,z6]),(0,[z1,z847,z3,z4,z5,z6]),(0,[z1,z12,z2,z75,z3,z6])],[(0,[z2,z3,z4,z5,z15,z51]),(0,[z212,z3,z4,z5,z6,z15]),(0,[z14,z12,z2,z44,z3,z6]),(0,[z10,z1,z3,z4,z5,z578]),(0,[z848,z2,z3,z4,z5,z6]),(0,[z1,z2,z849,z3,z4,z6])],[(0,[z180,z3,z4,z5,z6,z15]),(0,[z1,z3,z850,z4,z5,z6]),(0,[z1,z697,z38,z4,z5,z6]),(0,[z851,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z3,z444,z6]),(0,[z852,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z853,z6]),(0,[z854,z2,z3,z4,z5,z6]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z223,z197,z3,z4,z5,z6]),(0,[z1,z2,z155,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z856]),(0,[z1,z857,z3,z4,z5,z6])],[(0,[z8,z193,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z24]),(0,[z858,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z48,z15]),(0,[z14,z2,z3,z4,z5,z48]),(0,[z859,z2,z3,z4,z5,z6]),(0,[z860,z2,z3,z4,z5,z6])]],
   [[(0,[z192,z2,z3,z4,z5,z29]),(0,[z540,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z861,z5,z6]),(0,[z1,z2,z4,z5,z6,z781])],[(0,[z1,z2,z3,z5,z6,z862]),(0,[z863,z2,z3,z4,z5,z15]),(0,[z27,z14,z2,z4,z245,z6]),(0,[z864,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z865]),(0,[z1,z2,z4,z5,z245,z356]),(0,[z1,z2,z155,z184,z5,z6]),(0,[z2,z3,z4,z145,z25,z211])],[(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z2,z867,z4,z5,z6]),(0,[z1,z868,z3,z4,z5,z6]),(1,[z2,z3,z4,z869,z6]),(0,[z2,z3,z4,z5,z869,z6]),(0,[z409,z3,z4,z5,z6,z15]),(0,[z14,z2,z3,z364,z5,z6]),(0,[z2,z3,z4,z5,z6,z870])],[(0,[z871,z2,z3,z4,z5,z6]),(0,[z79,z3,z4,z5,z6,z15]),(0,[z1,z3,z4,z5,z6,z872])],[(0,[z14,z2,z3,z93,z244,z6]),(0,[z873,z2,z3,z4,z5,z6]),(0,[z1,z180,z368,z4,z5,z6])],[(0,[z611,z2,z3,z4,z5,z15]),(0,[z1,z874,z3,z4,z5,z6]),(0,[z1,z875,z3,z4,z5,z6]),(0,[z408,z2,z3,z133,z5,z6]),(0,[z614,z2,z3,z4,z5,z15]),(0,[z2,z3,z82,z5,z6,z15]),(0,[z2,z3,z4,z5,z6,z876]),(0,[z62,z1,z3,z147,z5,z6]),(0,[z1,z284,z3,z5,z207,z6]),(0,[z1,z2,z877,z4,z5,z6])],[(0,[z2,z3,z711,z13,z5,z6]),(0,[z81,z14,z3,z4,z52,z6]),(0,[z2,z3,z4,z5,z6,z878])],[(0,[z1,z2,z3,z178,z5,z6]),(0,[z1,z2,z725,z4,z5,z6]),(0,[z1,z180,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z879]),(0,[z1,z3,z4,z5,z6,z880])]],
   [[(0,[z50,z22,z3,z4,z5,z29]),(0,[z1,z2,z3,z881,z5,z6]),(0,[z1,z2,z3,z5,z882,z6]),(0,[z2,z3,z4,z5,z620,z15]),(0,[z2,z3,z4,z5,z6,z883]),(0,[z1,z2,z3,z5,z6,z884]),(0,[z885,z2,z3,z4,z5,z6]),(0,[z886,z2,z3,z4,z5,z6]),(0,[z1,z12,z2,z849,z3,z6])],[(0,[z378,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z441,z15]),(0,[z1,z2,z3,z4,z5,z887]),(0,[z888,z2,z3,z4,z5,z6]),(0,[z889,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z216,z5,z115]),(0,[z23,z3,z4,z88,z6,z15]),(0,[z1,z2,z3,z890,z5,z6]),(0,[z891,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z750,z6]),(0,[z892,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z578,z15]),(0,[z1,z2,z3,z893,z5,z6]),(0,[z2,z3,z894,z4,z5,z6]),(0,[z258,z197,z3,z4,z5,z6]),(0,[z187,z1,z2,z4,z5,z781])],[(0,[z1,z2,z3,z4,z895,z6]),(0,[z177,z2,z3,z4,z5,z6]),(0,[z2,z3,z757,z4,z5,z6]),(0,[z1,z896,z3,z4,z5,z6]),(0,[z14,z545,z3,z4,z5,z6]),(0,[z897,z2,z3,z4,z5,z6]),(0,[z380,z62,z1,z3,z5,z6]),(0,[z1,z898,z3,z4,z5,z6]),(0,[z106,z1,z2,z3,z184,z71]),(0,[z106,z1,z3,z4,z474,z71])],[(0,[z200,z2,z3,z4,z5,z6]),(0,[z1,z2,z899,z4,z5,z6]),(0,[z114,z2,z3,z4,z86,z6]),(0,[z62,z1,z345,z3,z5,z6]),(0,[z98,z294,z1,z3,z5,z6]),(0,[z1,z2,z3,z429,z5,z356])],[(0,[z2,z3,z4,z5,z15,z125]),(0,[z37,z14,z38,z4,z5,z6]),(0,[z1,z2,z3,z900,z5,z6])],[(0,[z14,z16,z3,z26,z5,z6]),(0,[z1,z2,z3,z4,z901,z6]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z94,z902,z3,z4,z5,z6])]],
   [[(0,[z1,z903,z3,z4,z5,z6]),(0,[z77,z2,z571,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z15]),(0,[z904,z1,z2,z3,z5,z6])],[(0,[z768,z2,z3,z4,z5,z6])],[(0,[z14,z3,z4,z5,z54,z6]),(0,[z1,z905,z3,z4,z5,z6]),(0,[z906,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z907]),(0,[z1,z908,z3,z4,z5,z6]),(0,[z909,z3,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z910,z6]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z912,z2,z3,z4,z5,z6])],[(0,[z1,z2,z913,z4,z5,z6]),(0,[z1,z914,z3,z4,z5,z6]),(0,[z94,z2,z3,z4,z5,z24]),(0,[z915,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z5,z750,z6]),(0,[z1,z2,z72,z4,z5,z443])],[(0,[z1,z755,z3,z4,z5,z6]),(0,[z43,z3,z4,z5,z6,z15]),(0,[z2,z3,z743,z5,z6,z15]),(0,[z916,z2,z3,z4,z5,z6])],[(0,[z14,z2,z3,z216,z5,z6]),(0,[z1,z2,z3,z4,z917,z6]),(0,[z98,z1,z5,z54,z55,z6])],[(0,[z2,z3,z659,z4,z5,z15]),(0,[z14,z165,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z115,z15]),(0,[z1,z918,z3,z4,z5,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z920,z1,z2,z3,z5,z6]),(1,[z1,z2,z3,z4,z746]),(0,[z1,z2,z3,z4,z746,z71]),(0,[z2,z3,z4,z5,z921,z6])]],
   [[(0,[z1,z2,z922,z4,z5,z6]),(0,[z1,z2,z3,z923,z5,z6]),(0,[z2,z3,z4,z711,z5,z6]),(0,[z1,z2,z232,z178,z5,z6]),(0,[z3,z4,z5,z6,z15,z740]),(0,[z1,z118,z17,z4,z5,z6]),(0,[z1,z2,z924,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z925])],[(0,[z1,z926,z3,z4,z5,z6]),(0,[z1,z2,z927,z4,z5,z6]),(0,[z2,z3,z4,z5,z928,z6]),(1,[z1,z2,z4,z778,z6])],[(0,[z1,z237,z3,z178,z5,z6]),(0,[z1,z2,z3,z4,z5,z731]),(0,[z2,z3,z4,z5,z666,z15]),(0,[z14,z2,z3,z929,z5,z6]),(0,[z1,z3,z26,z5,z6,z320]),(0,[z1,z930,z3,z4,z5,z6]),(0,[z1,z931,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z778,z6]),(0,[z1,z2,z3,z932,z5,z6]),(0,[z933,z2,z3,z4,z5,z6]),(0,[z1,z12,z43,z44,z3,z6])],[(0,[z2,z379,z78,z4,z5,z6]),(0,[z1,z2,z3,z120,z244,z6])],[(0,[z1,z79,z3,z4,z5,z6]),(0,[z177,z2,z78,z4,z5,z6]),(0,[z1,z2,z3,z216,z5,z182]),(0,[z109,z3,z4,z5,z52,z15]),(0,[z240,z2,z3,z4,z5,z15]),(0,[z14,z934,z3,z4,z5,z6]),(0,[z14,z118,z299,z4,z5,z6]),(0,[z81,z1,z3,z4,z807,z6]),(0,[z1,z935,z3,z4,z5,z6]),(0,[z1,z936,z3,z4,z5,z6])],[(0,[z2,z3,z178,z5,z6,z15]),(0,[z2,z3,z5,z6,z15,z862]),(0,[z937,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z938,z6])],[(0,[z1,z2,z939,z4,z5,z6]),(0,[z114,z2,z232,z4,z86,z6]),(0,[z566,z1,z3,z4,z5,z11]),(0,[z1,z23,z3,z88,z275,z6]),(0,[z1,z2,z3,z4,z5,z940]),(0,[z941,z2,z3,z4,z5,z6])],[(0,[z1,z2,z708,z4,z5,z6]),(0,[z942,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z943,z5,z6]),(0,[z114,z237,z3,z4,z86,z6]),(0,[z205,z2,z3,z4,z5,z731]),(0,[z2,z3,z4,z5,z677,z15]),(0,[z47,z1,z2,z3,z5,z138])],[(0,[z77,z2,z148,z4,z5,z6]),(0,[z1,z944,z3,z4,z5,z6]),(0,[z1,z2,z849,z3,z5,z6])],[(0,[z1,z2,z3,z429,z5,z6]),(0,[z1,z2,z4,z5,z34,z781])],[(0,[z1,z2,z3,z4,z5,z945]),(0,[z2,z3,z4,z5,z6,z946])],[(0,[z1,z947,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z948])],[(0,[z94,z2,z3,z4,z5,z15]),(0,[z14,z2,z3,z4,z5,z356]),(0,[z1,z2,z3,z4,z949,z6])],[],[(0,[z1,z950,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z951,z6]),(0,[z1,z2,z3,z4,z5,z952]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z37,z1,z38,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z954]),(0,[z2,z3,z4,z5,z6,z955]),(0,[z1,z409,z3,z4,z5,z6])]],
   [[(0,[z754,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z15,z396]),(0,[z1,z2,z757,z4,z5,z6]),(0,[z62,z10,z3,z4,z5,z15]),(0,[z1,z284,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z956,z6]),(0,[z1,z2,z3,z4,z5,z957]),(0,[z958,z2,z3,z4,z5,z6])],[(0,[z192,z193,z3,z4,z5,z6]),(0,[z298,z2,z3,z376,z5,z6]),(0,[z1,z237,z232,z4,z5,z6]),(0,[z81,z3,z4,z52,z6,z15]),(0,[z2,z3,z4,z5,z695,z15]),(0,[z14,z959,z3,z4,z5,z6]),(0,[z1,z960,z3,z4,z5,z6])],[(0,[z1,z2,z3,z961,z5,z6]),(0,[z2,z3,z93,z456,z244,z6]),(0,[z962,z2,z3,z4,z5,z6])],[(0,[z14,z2,z3,z4,z5,z346]),(0,[z298,z2,z3,z711,z5,z6]),(0,[z863,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z963,z6])],[(0,[z192,z212,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z115]),(0,[z127,z1,z23,z3,z5,z6]),(0,[z1,z964,z3,z4,z5,z6]),(0,[z965,z1,z2,z3,z4,z5])],[(0,[z1,z118,z708,z4,z5,z6]),(0,[z1,z2,z39,z32,z5,z6]),(0,[z2,z3,z4,z5,z966,z6]),(0,[z27,z258,z2,z4,z245,z6]),(0,[z967,z2,z3,z4,z5,z6])],[(0,[z62,z1,z617,z3,z5,z6]),(0,[z81,z1,z3,z4,z562,z6])],[(0,[z968,z2,z3,z4,z5,z6]),(0,[z2,z969,z3,z4,z5,z6]),(0,[z970,z2,z3,z4,z5,z6]),(0,[z1,z971,z3,z4,z5,z6])]],
   [[(0,[z1,z972,z3,z4,z5,z6]),(0,[z3,z4,z5,z15,z474,z71])],[(0,[z50,z754,z3,z4,z5,z6]),(0,[z1,z2,z3,z711,z5,z6]),(0,[z973,z1,z3,z4,z5,z6]),(0,[z974,z1,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z24,z731]),(0,[z240,z1,z3,z4,z5,z6]),(0,[z154,z2,z3,z364,z5,z6])],[(0,[z10,z1,z3,z4,z5,z705]),(0,[z10,z1,z284,z3,z5,z6]),(0,[z1,z334,z155,z4,z5,z6])],[(1,[z2,z757,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z975]),(0,[z863,z2,z3,z4,z5,z25]),(0,[z250,z2,z3,z4,z6,z421]),(0,[z14,z976,z3,z4,z5,z6]),(0,[z977,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z474]),(0,[z1,z978,z3,z4,z5,z6])],[(0,[z2,z979,z3,z4,z5,z6]),(0,[z62,z1,z3,z5,z64,z6]),(0,[z980,z1,z2,z4,z5,z6]),(0,[z1,z3,z4,z5,z744,z11]),(0,[z1,z3,z4,z5,z6,z981]),(0,[z1,z2,z3,z4,z778,z6])],[(0,[z2,z39,z32,z5,z6,z15]),(0,[z14,z2,z982,z4,z5,z6]),(0,[z223,z42,z3,z4,z5,z6])],[(0,[z31,z2,z3,z4,z5,z15]),(0,[z2,z3,z893,z5,z6,z15]),(0,[z14,z2,z368,z4,z5,z6]),(0,[z1,z2,z5,z750,z55,z6])]],
   [[(0,[z1,z2,z4,z5,z6,z983])],[(0,[z307,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z869,z6]),(0,[z1,z2,z3,z795,z5,z6]),(0,[z2,z3,z4,z5,z57,z15]),(0,[z515,z2,z3,z4,z5,z15]),(0,[z106,z2,z3,z4,z15,z71]),(0,[z1,z2,z984,z4,z5,z6])],[(0,[z1,z834,z3,z4,z5,z6]),(0,[z985,z2,z4,z5,z6,z15]),(0,[z1,z909,z3,z4,z5,z6]),(0,[z986,z1,z3,z4,z5,z6])],[(0,[z90,z2,z3,z711,z5,z6]),(0,[z114,z2,z3,z4,z869,z6]),(0,[z2,z3,z4,z5,z25,z15]),(0,[z1,z2,z3,z4,z103,z25]),(0,[z987,z2,z3,z4,z5,z6]),(0,[z988,z2,z3,z4,z5,z6])],[(0,[z2,z72,z4,z5,z34,z15]),(0,[z318,z212,z3,z4,z5,z6]),(0,[z411,z2,z3,z4,z5,z71])],[(1,[z2,z3,z711,z5,z6]),(0,[z157,z2,z4,z5,z6,z70]),(0,[z2,z3,z4,z5,z6,z989]),(0,[z1,z2,z990,z4,z5,z6]),(0,[z1,z334,z3,z184,z5,z6])],[(0,[z1,z2,z991,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z182]),(0,[z14,z2,z3,z4,z5,z338]),(0,[z2,z3,z4,z5,z356,z15]),(0,[z14,z2,z3,z992,z5,z6]),(0,[z1,z2,z3,z4,z5,z993])],[(0,[z237,z3,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z15,z291]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z2,z3,z4,z5,z6,z995]),(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z902,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z6,z35]),(0,[z2,z3,z4,z5,z86,z115]),(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z2,z3,z997,z5,z6]),(0,[z2,z3,z998,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z999]),(0,[z1000,z2,z3,z4,z5,z6]),(0,[z1,z2,z1001,z4,z5,z6])],[(0,[z1,z2,z3,z1002,z5,z6]),(0,[z10,z3,z4,z5,z15,z11]),(0,[z14,z2,z3,z1003,z5,z6]),(0,[z62,z1,z3,z110,z5,z6]),(0,[z1,z3,z4,z5,z6,z1004]),(0,[z1005,z2,z3,z4,z5,z6]),(0,[z1,z1006,z3,z4,z5,z6])],[(0,[z306,z3,z4,z5,z126,z6]),(0,[z14,z2,z3,z99,z5,z6]),(0,[z127,z1,z3,z5,z52,z6]),(0,[z1,z12,z2,z44,z3,z6])],[(0,[z123,z2,z3,z4,z5,z6]),(0,[z258,z42,z3,z4,z5,z6]),(0,[z1,z180,z155,z4,z5,z6])],[(0,[z1,z2,z1007,z4,z5,z6]),(0,[z2,z3,z4,z5,z15,z312]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z48]),(0,[z1,z2,z368,z364,z5,z6]),(0,[z106,z240,z1,z3,z4,z71])],[(0,[z2,z3,z4,z5,z105,z15]),(0,[z1,z42,z3,z429,z5,z6]),(0,[z1009,z2,z3,z4,z5,z6]),(0,[z1,z1010,z3,z4,z5,z6]),(0,[z106,z1,z180,z3,z4,z71])],[(0,[z628,z2,z3,z4,z5,z15]),(0,[z1011,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1012])],[(0,[z167,z2,z78,z4,z5,z6]),(0,[z1013,z1,z3,z4,z5,z6]),(0,[z294,z3,z4,z5,z6,z15]),(0,[z79,z212,z3,z4,z5,z6]),(0,[z258,z2,z18,z4,z5,z6]),(0,[z1,z2,z3,z364,z5,z6])]],
   [[(0,[z327,z2,z271,z4,z5,z6]),(0,[z127,z1,z16,z3,z5,z6]),(0,[z1,z3,z1014,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z93,z244,z6])],[(0,[z47,z14,z2,z3,z5,z138]),(0,[z1,z2,z3,z1016,z5,z6]),(0,[z1,z1017,z3,z4,z5,z6]),(0,[z478,z1,z2,z5,z55,z6]),(0,[z2,z3,z4,z5,z35,z71]),(0,[z2,z3,z128,z5,z91,z427])],[(0,[z540,z2,z3,z4,z5,z29]),(0,[z1,z16,z3,z5,z437,z6]),(0,[z1,z1018,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1019]),(0,[z2,z148,z4,z5,z6,z353]),(0,[z2,z3,z133,z178,z5,z6]),(0,[z3,z4,z5,z54,z6,z15]),(0,[z14,z212,z3,z4,z5,z24]),(0,[z10,z1,z3,z4,z5,z119]),(0,[z1,z2,z3,z99,z5,z48]),(0,[z1020,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z1021,z3,z4,z5,z6])],[(0,[z77,z2,z181,z4,z5,z6]),(0,[z1022,z2,z3,z4,z5,z356]),(1,[z1,z2,z849,z3,z6]),(0,[z1,z2,z1023,z4,z5,z6]),(0,[z1,z180,z3,z184,z5,z6])],[(0,[z1,z165,z3,z4,z5,z115]),(0,[z378,z2,z3,z178,z5,z6]),(0,[z14,z1024,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1025])],[(0,[z2,z3,z4,z5,z152,z15]),(0,[z94,z2,z3,z4,z5,z6]),(0,[z240,z3,z4,z5,z6,z15]),(0,[z1026,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z15,z71]),(0,[z1,z2,z4,z5,z750,z6]),(0,[z1,z197,z3,z429,z5,z6])],[(0,[z14,z2,z3,z4,z5,z322]),(0,[z10,z306,z3,z4,z5,z15]),(0,[z1,z545,z3,z4,z5,z6]),(0,[z1,z2,z3,z574,z244,z6]),(0,[z1,z2,z301,z32,z5,z6])],[(0,[z22,z3,z4,z5,z126,z6]),(0,[z1,z2,z1027,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z427]),(0,[z114,z2,z3,z178,z86,z6]),(0,[z2,z3,z4,z5,z647,z15]),(0,[z2,z3,z4,z5,z6,z1028])],[(0,[z167,z2,z255,z4,z5,z6]),(0,[z94,z2,z3,z4,z5,z182]),(0,[z284,z2,z3,z5,z6,z15]),(0,[z2,z3,z4,z5,z6,z1029]),(0,[z1030,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1031,z6]),(0,[z1032,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z5,z1033,z6]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z2,z3,z4,z5,z373,z6]),(0,[z90,z2,z3,z133,z5,z6]),(0,[z2,z3,z5,z882,z6,z15]),(0,[z1,z16,z3,z26,z5,z6]),(0,[z1,z284,z23,z3,z88,z6]),(0,[z1035,z1,z3,z4,z5,z6])],[(0,[z77,z2,z271,z4,z5,z6]),(0,[z2,z3,z216,z5,z6,z15]),(0,[z2,z3,z4,z869,z86,z6]),(0,[z1,z3,z4,z5,z6,z812]),(0,[z14,z2,z1036,z4,z5,z6])],[(0,[z14,z2,z255,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z770]),(0,[z2,z3,z4,z149,z869,z6]),(0,[z41,z2,z39,z32,z5,z6])],[(0,[z200,z193,z3,z4,z5,z6]),(0,[z2,z148,z757,z4,z5,z6]),(0,[z1,z2,z3,z1037,z5,z6]),(0,[z1,z2,z3,z1038,z5,z6]),(0,[z1,z3,z4,z5,z54,z6]),(0,[z1039,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1040]),(0,[z1,z23,z3,z4,z807,z6]),(0,[z1,z284,z23,z3,z5,z6]),(0,[z2,z3,z4,z5,z1041,z6])]],
   [[(0,[z2,z3,z4,z149,z6,z518]),(0,[z14,z3,z4,z5,z6,z253]),(0,[z137,z1,z3,z4,z5,z6]),(0,[z411,z2,z368,z4,z5,z6])],[(0,[z294,z1,z3,z5,z244,z6]),(0,[z2,z3,z1042,z4,z5,z6])],[(0,[z1,z22,z3,z4,z5,z322]),(0,[z85,z2,z255,z4,z5,z6]),(0,[z3,z220,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z1043])],[(0,[z1,z2,z3,z216,z5,z6]),(0,[z411,z2,z3,z4,z5,z6]),(0,[z205,z2,z3,z4,z5,z15]),(0,[z1,z1044,z3,z4,z5,z6])],[(0,[z1,z165,z3,z4,z5,z6]),(0,[z328,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z1045,z5,z6])],[(0,[z206,z2,z3,z5,z6,z144]),(0,[z14,z212,z3,z4,z5,z15])],[(0,[z1,z118,z602,z4,z5,z6])],[(0,[z1,z2,z3,z929,z5,z6]),(0,[z127,z1,z299,z3,z5,z6]),(0,[z62,z1,z3,z814,z5,z6]),(0,[z10,z1,z3,z4,z5,z11])]],
   [[(0,[z298,z2,z3,z13,z5,z6]),(0,[z1,z165,z3,z4,z5,z182]),(0,[z14,z1046,z3,z4,z5,z6]),(0,[z1,z2,z1047,z4,z5,z6]),(0,[z1,z3,z4,z807,z52,z6]),(0,[z1048,z1,z3,z4,z5,z6])],[(0,[z1,z934,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z206,z2,z3,z13,z5,z6]),(0,[z14,z2,z3,z4,z5,z488]),(0,[z140,z2,z3,z183,z5,z6]),(0,[z1,z118,z299,z4,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z1051,z2,z3,z4,z5,z6])],[(0,[z177,z2,z148,z4,z5,z6]),(0,[z10,z3,z4,z5,z15,z295]),(0,[z1052,z2,z3,z4,z5,z6]),(0,[z47,z265,z2,z3,z5,z138])],[(0,[z1,z2,z3,z4,z5,z1053]),(0,[z2,z255,z4,z5,z86,z6]),(0,[z47,z2,z3,z5,z15,z138]),(0,[z246,z2,z3,z376,z5,z6]),(0,[z2,z3,z4,z5,z1054,z6]),(0,[z1,z2,z3,z1055,z5,z6]),(0,[z1056,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z778,z245,z6])],[(0,[z2,z3,z699,z133,z5,z6]),(0,[z2,z3,z4,z5,z160,z15]),(0,[z2,z3,z4,z5,z48,z1028]),(0,[z1,z2,z3,z1057,z5,z6]),(0,[z411,z2,z3,z4,z5,z25])],[(0,[z1,z2,z1058,z4,z5,z6]),(0,[z27,z223,z2,z4,z245,z6])],[(0,[z1,z2,z44,z849,z3,z6])],[(0,[z200,z79,z3,z4,z5,z6]),(0,[z2,z39,z40,z32,z5,z6])]],
   [[(0,[z10,z193,z3,z4,z5,z15]),(0,[z14,z197,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1060,z2,z3,z4,z5,z6]),(0,[z1,z545,z72,z4,z5,z34])],[(0,[z10,z3,z38,z4,z5,z15])],[(0,[z187,z14,z2,z4,z5,z68]),(0,[z2,z3,z4,z5,z6,z1061]),(0,[z1,z2,z3,z4,z5,z356]),(0,[z1,z2,z3,z1062,z5,z6]),(0,[z1,z2,z4,z5,z781,z68])],[(0,[z185,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z1063,z5,z6]),(0,[z235,z2,z3,z4,z86,z6]),(0,[z298,z2,z3,z4,z5,z115]),(0,[z2,z3,z4,z5,z6,z1064])],[(0,[z85,z2,z3,z4,z149,z6]),(0,[z1,z2,z232,z216,z5,z6]),(0,[z2,z3,z4,z5,z6,z1065]),(0,[z47,z137,z1,z3,z5,z138])],[(0,[z2,z3,z4,z5,z6,z1066]),(0,[z14,z1067,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1068,z6]),(0,[z2,z3,z4,z5,z6,z1069]),(0,[z1,z2,z849,z3,z93,z6])],[(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1,z959,z3,z4,z5,z6]),(0,[z1,z237,z3,z216,z5,z6]),(0,[z14,z43,z3,z4,z5,z6]),(0,[z1071,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1072]),(0,[z1,z2,z849,z3,z244,z6])],[(0,[z1,z2,z3,z1073,z5,z6]),(0,[z14,z2,z3,z4,z5,z493]),(0,[z1,z736,z3,z4,z5,z6]),(0,[z1074,z2,z3,z4,z5,z6]),(0,[z10,z1,z3,z4,z5,z242])]],
   [[(0,[z16,z3,z26,z5,z6,z15]),(0,[z14,z2,z3,z128,z5,z91]),(0,[z1075,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z2,z3,z4,z5,z115]),(0,[z109,z3,z4,z5,z207,z15]),(0,[z1077,z2,z3,z4,z5,z6])],[(0,[z49,z2,z3,z4,z5,z6]),(0,[z14,z2,z1078,z4,z5,z6]),(0,[z1,z197,z3,z4,z5,z48]),(0,[z1,z2,z3,z99,z5,z356])],[(0,[z2,z78,z4,z5,z33,z6]),(0,[z1,z1079,z3,z4,z5,z6]),(0,[z822,z3,z4,z5,z6,z15]),(0,[z1080,z2,z3,z4,z5,z6]),(0,[z1,z1081,z3,z4,z5,z6]),(0,[z223,z2,z3,z429,z5,z6])],[(0,[z77,z2,z757,z4,z5,z6]),(0,[z2,z3,z1082,z4,z5,z6]),(0,[z1,z2,z3,z4,z1083,z6]),(0,[z1084,z2,z3,z4,z5,z6]),(0,[z1,z1085,z3,z4,z5,z6]),(0,[z106,z1,z2,z368,z4,z71])],[(0,[z1,z2,z3,z4,z5,z1086]),(0,[z2,z3,z4,z149,z423,z6]),(0,[z2,z3,z4,z5,z6,z1087])],[(0,[z1,z2,z3,z5,z6,z1088]),(0,[z1089,z2,z3,z4,z5,z6])],[(0,[z1,z2,z255,z216,z5,z6]),(0,[z2,z3,z4,z5,z1090,z6]),(0,[z540,z212,z3,z4,z5,z6]),(0,[z62,z1,z325,z3,z5,z6]),(0,[z1,z2,z1091,z4,z5,z6]),(0,[z1,z2,z3,z1092,z5,z6])]],
   [[(0,[z157,z2,z78,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z165,z255,z4,z5,z6]),(0,[z2,z3,z4,z518,z15,z71]),(0,[z1,z2,z3,z5,z1094,z6]),(0,[z1095,z1,z3,z4,z5,z6]),(0,[z1096,z2,z3,z4,z5,z6]),(0,[z1,z1097,z3,z4,z5,z6])],[(0,[z1,z976,z3,z4,z5,z6]),(0,[z1098,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z1099,z5,z6]),(0,[z1,z23,z3,z4,z355,z6]),(0,[z1,z1100,z3,z4,z5,z6]),(0,[z123,z2,z3,z128,z5,z91])],[(0,[z2,z3,z4,z149,z438,z6]),(0,[z27,z1,z2,z429,z245,z6]),(0,[z106,z1,z2,z3,z4,z746])],[(0,[z114,z2,z3,z4,z350,z6]),(0,[z1,z2,z982,z4,z5,z6]),(0,[z2,z232,z4,z5,z6,z15]),(0,[z127,z2,z3,z5,z6,z15]),(0,[z1,z16,z3,z468,z5,z6]),(0,[z1,z2,z3,z4,z6,z746])],[(0,[z318,z193,z3,z4,z5,z6]),(0,[z1,z2,z368,z4,z5,z6]),(0,[z1101,z1,z3,z4,z5,z6])],[(0,[z14,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z65,z15]),(0,[z2,z767,z4,z5,z6,z15]),(0,[z2,z3,z4,z5,z1102,z6])],[(0,[z2,z3,z4,z5,z29,z15]),(0,[z1,z2,z3,z4,z5,z1103]),(0,[z1,z1104,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z14,z67,z3,z4,z5,z6]),(0,[z1108,z2,z3,z4,z5,z6]),(0,[z1109,z2,z3,z4,z5,z6])]],
   [[(0,[z10,z1,z3,z4,z5,z295]),(0,[z2,z3,z4,z5,z15,z591]),(0,[z2,z155,z4,z5,z6,z15]),(0,[z14,z2,z3,z184,z5,z6]),(0,[z1,z2,z4,z5,z1110,z6]),(0,[z1111,z2,z3,z4,z5,z6]),(0,[z1112,z2,z3,z4,z5,z6]),(0,[z1113,z2,z3,z4,z5,z6]),(0,[z258,z2,z3,z429,z5,z6])],[(0,[z85,z2,z3,z4,z112,z6]),(0,[z1,z67,z3,z4,z5,z6])],[(0,[z1114,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1115,z5,z6]),(0,[z1,z2,z1116,z4,z5,z6]),(0,[z2,z3,z4,z5,z317,z15]),(0,[z1,z2,z3,z4,z5,z182]),(0,[z1,z2,z3,z992,z5,z6]),(0,[z187,z1,z2,z4,z5,z68]),(0,[z1,z2,z155,z364,z5,z6])],[(0,[z559,z2,z3,z4,z5,z15]),(0,[z127,z1,z3,z63,z5,z6]),(0,[z106,z1,z334,z3,z4,z71])],[(0,[z3,z4,z5,z6,z15,z474])],[(0,[z167,z2,z58,z4,z5,z6]),(0,[z1,z1117,z3,z4,z5,z6]),(0,[z1,z2,z3,z1003,z5,z6]),(0,[z545,z3,z4,z5,z6,z15]),(0,[z14,z294,z3,z4,z5,z6])],[(0,[z79,z193,z3,z4,z5,z6]),(0,[z1,z1118,z2,z3,z5,z6]),(0,[z14,z212,z3,z4,z5,z6]),(0,[z1119,z2,z3,z4,z5,z6]),(0,[z1,z3,z1120,z4,z5,z6]),(0,[z1,z118,z532,z4,z5,z6]),(0,[z1,z2,z1121,z4,z5,z6]),(0,[z1,z2,z3,z99,z5,z6]),(0,[z352,z1,z2,z4,z5,z68]),(0,[z137,z1,z3,z5,z244,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1122]),(0,[z2,z3,z4,z5,z182,z15]),(0,[z985,z1,z2,z4,z5,z6]),(0,[z10,z2,z3,z4,z5,z707]),(0,[z1,z1123,z3,z4,z5,z6])],[(0,[z27,z2,z4,z245,z6,z15]),(0,[z3,z1124,z4,z5,z6,z15]),(0,[z14,z3,z220,z4,z5,z6]),(0,[z1125,z2,z3,z4,z5,z6]),(0,[z1,z23,z3,z4,z444,z6]),(0,[z49,z2,z72,z4,z5,z34])],[(0,[z227,z2,z3,z4,z5,z6]),(0,[z1126,z1,z3,z4,z5,z6]),(0,[z27,z1,z197,z4,z245,z6]),(0,[z1,z1127,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1128,z5,z6]),(0,[z1129,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1130]),(0,[z2,z3,z1131,z4,z5,z6])],[(0,[z280,z2,z3,z4,z5,z15]),(0,[z10,z3,z4,z88,z5,z15]),(0,[z1,z2,z3,z4,z5,z1132]),(0,[z1133,z2,z3,z4,z5,z6]),(0,[z1134,z1,z2,z4,z5,z6]),(0,[z1,z180,z3,z364,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z3,z4,z5,z1136]),(0,[z1,z2,z255,z4,z5,z115]),(0,[z1,z42,z3,z4,z5,z356]),(0,[z2,z3,z4,z5,z6,z1137])],[(0,[z1,z2,z3,z259,z244,z6]),(0,[z14,z2,z232,z4,z5,z6]),(0,[z2,z3,z4,z5,z707,z15]),(0,[z1138,z1,z2,z3,z4,z5])],[(0,[z2,z3,z4,z341,z5,z15]),(0,[z14,z2,z3,z763,z5,z6]),(0,[z200,z2,z3,z4,z5,z24])]],
   [[(0,[z14,z237,z3,z4,z5,z6]),(0,[z81,z10,z3,z4,z5,z15]),(0,[z2,z368,z4,z5,z6,z15]),(0,[z187,z100,z2,z4,z5,z68])],[(0,[z973,z3,z4,z5,z6,z15]),(0,[z974,z3,z4,z5,z6,z15]),(0,[z553,z2,z58,z4,z5,z6])],[(0,[z2,z3,z4,z5,z456,z6]),(0,[z2,z3,z5,z6,z15,z1088]),(0,[z197,z3,z4,z5,z6,z15]),(0,[z14,z23,z3,z4,z88,z6]),(0,[z1,z2,z3,z4,z5,z1139]),(0,[z1140,z1,z3,z4,z5,z6]),(0,[z47,z1,z3,z5,z253,z138])],[(0,[z1,z1024,z3,z4,z5,z6]),(0,[z1141,z2,z3,z4,z5,z6]),(0,[z1142,z2,z3,z4,z5,z6])],[(0,[z1143,z1,z3,z4,z5,z6]),(0,[z14,z2,z72,z4,z5,z34]),(0,[z1,z2,z3,z1144,z5,z6])],[(0,[z290,z22,z3,z4,z5,z6]),(0,[z1,z1145,z3,z4,z5,z6]),(0,[z298,z2,z255,z4,z5,z6]),(0,[z223,z2,z3,z4,z5,z48]),(0,[z1146,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z322]),(0,[z22,z754,z3,z4,z5,z6]),(0,[z1,z2,z3,z1147,z5,z6]),(0,[z238,z1,z2,z4,z5,z68]),(0,[z1,z2,z72,z4,z5,z34])],[(0,[z1,z2,z3,z1148,z5,z6]),(0,[z543,z2,z3,z4,z5,z15]),(0,[z127,z1,z3,z5,z207,z6]),(0,[z411,z2,z155,z4,z5,z6])]],
   [[(0,[z577,z2,z78,z4,z5,z6]),(0,[z298,z2,z3,z189,z5,z6]),(0,[z1,z2,z3,z1149,z5,z6]),(0,[z14,z2,z3,z4,z5,z581]),(0,[z14,z786,z3,z4,z5,z6]),(0,[z1,z197,z3,z4,z5,z356]),(0,[z1,z2,z18,z4,z430,z6])],[(1,[z754,z3,z4,z5,z6]),(0,[z1,z2,z3,z1150,z5,z6]),(0,[z294,z1,z39,z3,z5,z6]),(0,[z1,z2,z4,z5,z643,z68]),(0,[z1,z2,z462,z4,z5,z34]),(0,[z2,z3,z4,z5,z6,z1151])],[(0,[z1,z2,z1036,z4,z5,z6]),(0,[z2,z3,z4,z5,z176,z15]),(0,[z566,z2,z3,z4,z5,z15]),(0,[z774,z2,z3,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z744])],[(0,[z1152,z1,z2,z3,z5,z6]),(0,[z1,z2,z255,z4,z5,z6]),(0,[z1,z2,z1153,z4,z5,z6]),(0,[z106,z14,z2,z3,z4,z71]),(0,[z550,z1,z3,z4,z52,z6]),(0,[z1154,z2,z3,z4,z5,z6])],[(0,[z14,z2,z3,z4,z5,z634]),(0,[z14,z79,z3,z4,z5,z24]),(0,[z1,z2,z3,z1155,z5,z6]),(0,[z27,z1,z2,z4,z245,z48]),(0,[z1,z1156,z3,z4,z5,z6]),(0,[z1157,z2,z3,z4,z5,z6])],[(0,[z167,z2,z757,z4,z5,z6]),(0,[z90,z2,z3,z183,z5,z6]),(0,[z37,z127,z1,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z253]),(0,[z98,z1,z67,z5,z55,z6]),(0,[z1158,z2,z3,z4,z5,z6]),(0,[z1,z12,z44,z409,z3,z6])],[(0,[z14,z2,z3,z4,z5,z29]),(0,[z307,z109,z3,z4,z5,z15]),(0,[z2,z3,z184,z5,z6,z15]),(0,[z1,z3,z708,z4,z5,z6]),(1,[z1,z2,z3,z5,z722])],[(0,[z10,z22,z3,z4,z5,z15]),(0,[z1,z1159,z3,z4,z5,z6]),(0,[z1,z1160,z3,z4,z5,z6]),(0,[z14,z2,z3,z4,z5,z646]),(0,[z1,z2,z255,z4,z5,z182]),(0,[z2,z3,z4,z5,z194,z15]),(1,[z1,z3,z814,z5,z6]),(0,[z1,z2,z18,z4,z778,z6]),(0,[z1,z1161,z3,z4,z5,z6])]],
   [[(0,[z2,z148,z3,z4,z5,z115]),(0,[z2,z3,z4,z5,z382,z15]),(0,[z14,z42,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z5,z722]),(0,[z411,z180,z3,z4,z5,z6])],[(0,[z1,z165,z3,z178,z5,z6]),(0,[z2,z3,z4,z5,z15,z521]),(0,[z2,z3,z4,z5,z15,z522]),(0,[z534,z2,z3,z4,z329,z6]),(0,[z1162,z2,z3,z4,z5,z6]),(0,[z1,z1163,z3,z4,z5,z6]),(0,[z411,z2,z3,z184,z5,z6])],[(0,[z2,z3,z4,z5,z1164,z6]),(0,[z1,z1165,z3,z4,z5,z6]),(0,[z2,z3,z99,z5,z6,z15]),(0,[z258,z2,z3,z4,z5,z48]),(0,[z2,z3,z4,z5,z6,z1166])],[(0,[z1,z2,z1167,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z833]),(0,[z1168,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1169]),(0,[z389,z1,z2,z4,z5,z68]),(0,[z1170,z2,z3,z4,z5,z6])],[(0,[z1,z3,z1171,z4,z5,z6]),(0,[z14,z811,z3,z4,z5,z6]),(0,[z37,z1,z82,z38,z5,z6]),(0,[z1,z3,z26,z5,z641,z6]),(0,[z2,z3,z4,z5,z6,z1172]),(0,[z1,z1173,z3,z4,z5,z6])],[(0,[z267,z2,z78,z4,z5,z6]),(0,[z1,z1046,z3,z4,z5,z6]),(0,[z1,z1174,z3,z4,z5,z6]),(0,[z1022,z2,z3,z4,z5,z6]),(0,[z2,z1175,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1176])],[(0,[z1,z3,z4,z5,z6,z1177]),(0,[z114,z2,z3,z216,z86,z6]),(0,[z250,z2,z3,z4,z86,z6]),(0,[z37,z38,z4,z5,z6,z15]),(0,[z1,z16,z345,z3,z5,z6]),(0,[z1178,z2,z3,z4,z5,z6]),(0,[z94,z2,z3,z4,z145,z25])],[(0,[z1,z2,z3,z4,z5,z1179]),(0,[z1,z3,z1124,z4,z5,z6]),(0,[z114,z165,z3,z4,z86,z6]),(0,[z1180,z2,z3,z4,z5,z6]),(0,[z1,z1181,z3,z4,z5,z6]),(0,[z27,z2,z4,z373,z245,z6]),(0,[z1,z2,z3,z5,z91,z722])]],
   [[(0,[z41,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z15,z538]),(0,[z250,z2,z3,z4,z15,z71]),(0,[z1182,z2,z3,z4,z5,z6]),(0,[z1183,z2,z3,z4,z5,z6]),(0,[z1184,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z5,z1185]),(0,[z22,z2,z3,z4,z5,z29]),(0,[z1,z12,z2,z369,z3,z6]),(0,[z1,z2,z3,z4,z5,z1186])],[(0,[z10,z1,z3,z4,z5,z396]),(0,[z1,z2,z3,z5,z1187,z6]),(0,[z1,z42,z3,z4,z5,z48]),(0,[z154,z2,z368,z4,z5,z6])],[(0,[z1188,z2,z3,z4,z5,z6]),(0,[z1189,z2,z3,z4,z5,z6])],[(0,[z235,z1,z2,z4,z245,z6]),(0,[z334,z3,z4,z5,z6,z15]),(0,[z14,z2,z3,z82,z5,z6]),(0,[z1,z299,z708,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z746])],[(0,[z154,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z15,z549]),(0,[z2,z3,z4,z5,z1190,z6]),(0,[z14,z79,z3,z4,z5,z15]),(0,[z1,z197,z3,z4,z5,z6]),(0,[z10,z226,z3,z4,z5,z11])],[(0,[z1,z1191,z3,z4,z5,z6]),(0,[z230,z2,z3,z4,z5,z15]),(0,[z1192,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1193,z6])],[(0,[z1,z1194,z3,z4,z5,z6]),(0,[z114,z2,z3,z4,z441,z6]),(0,[z1,z3,z4,z814,z5,z6])]],
   [[(0,[z100,z2,z3,z4,z5,z6]),(0,[z1,z165,z232,z4,z5,z6]),(0,[z14,z137,z3,z4,z5,z6]),(0,[z1,z1195,z2,z3,z5,z6]),(0,[z1,z284,z3,z5,z52,z6]),(0,[z1,z1196,z3,z4,z5,z6]),(0,[z1197,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z722,z138]),(0,[z154,z2,z3,z184,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1198]),(0,[z2,z3,z4,z5,z420,z15]),(0,[z67,z3,z4,z5,z6,z15]),(0,[z1,z1199,z2,z3,z5,z6]),(0,[z109,z2,z3,z4,z5,z73]),(0,[z27,z1,z42,z4,z245,z6]),(0,[z106,z154,z2,z3,z4,z71])],[(0,[z618,z1,z3,z4,z52,z6]),(0,[z1,z1067,z3,z4,z5,z6]),(0,[z14,z334,z3,z4,z5,z6]),(0,[z1200,z2,z3,z4,z5,z6])],[(0,[z318,z22,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1201]),(0,[z1,z43,z3,z4,z5,z6]),(0,[z106,z1,z2,z155,z4,z71])],[(0,[z1,z2,z3,z4,z5,z1202]),(0,[z1,z1203,z3,z4,z5,z6]),(0,[z257,z2,z3,z4,z5,z15]),(0,[z10,z109,z3,z4,z5,z15]),(0,[z1,z2,z737,z4,z5,z6]),(0,[z240,z1,z3,z4,z5,z24]),(0,[z106,z1,z2,z3,z4,z71])],[(0,[z754,z193,z3,z4,z5,z6]),(0,[z1,z1204,z3,z4,z5,z6]),(0,[z85,z2,z3,z4,z869,z6]),(0,[z1,z2,z3,z1205,z5,z6]),(0,[z1,z1206,z3,z4,z5,z6]),(0,[z1,z197,z3,z99,z5,z6]),(0,[z1,z2,z4,z19,z778,z6]),(0,[z1,z2,z3,z128,z5,z91])],[(0,[z1,z2,z3,z5,z1207,z6]),(0,[z1,z2,z3,z178,z5,z115]),(0,[z14,z842,z3,z4,z5,z6]),(0,[z1208,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1209])],[(0,[z1,z2,z1078,z4,z5,z6]),(0,[z187,z2,z4,z5,z15,z68]),(0,[z14,z2,z3,z5,z275,z6]),(0,[z258,z2,z4,z5,z245,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1045).take 196) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1241)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 524, 196] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 98).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 215).take 41).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [98, 117, 41] = true :=
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

end PEqualNP.Outside.L_meta_40217

theorem PEqualNP.Outside.L_meta_40217 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272482952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272482952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40217.solve