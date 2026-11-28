import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47012

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
  Nat.testBit (4008241288 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000c1a1aa06686a8#64 ++ 0x00018343540cd0d5#64 ++ 0xfa1c3e3fe3ff8fff#64 ++ 0xdf4387c7fc7ff1ff#64 : BitVec 256),
   (0x28e1c4c54d113150#64 ++ 0x051c3898a9a2262a#64 ++ 0xfde3c7c7fd11f1fb#64 ++ 0xffbc78f8ffa23e3f#64 : BitVec 256),
   (0x4602e969961a5a60#64 ++ 0x48c05d2d32c34b4c#64 ++ 0x7e03f9f99e1e7e65#64 ++ 0x6fc07f3f33c3cfcc#64 : BitVec 256),
   (0x977401b61ba06d82#64 ++ 0x12ee8036c3740db0#64 ++ 0xbffc01fe1fe07f86#64 ++ 0x77ff803fc3fc0ff0#64 : BitVec 256),
   (0x17bb76001fdd8001#64 ++ 0x22f76ec003fbb000#64 ++ 0xd7fffe001fff8000#64 ++ 0x7affffc003fff000#64 : BitVec 256),
   (0xe7dfbfffe0000000#64 ++ 0xbcfbf7fffc000000#64 ++ 0xe7ffffffe0000000#64 ++ 0x7cfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 4]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [7, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x021c383802ee0e04 0x00438707005dc1c0

def z1 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z2 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xd7fffe001fff8000 0x7affffc003fff000

def z3 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x05e3c1c01c007000 0x20bc783803800e00

def z4 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z5 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z6 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z7 : W := mkw 0x11b9160009c58001 0x223722c00138b000 0xd3fc3e0003ff8000 0x5a7f87c0007ff000

def z8 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z9 : W := mkw 0x57bbff699fdfda61 0x6af77fed33fbfb4c 0xfffffff99ffffe65 0x7fffffff33ffffcc

def z10 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x05e3c1c000000000 0x20bc783800000000

def z11 : W := mkw 0xd71e3b3ab2cc8001 0xbae3c76756599000 0x021c383802ee0000 0x00438707005dc000

def z12 : W := mkw 0x2889de49e4579278 0x05113bc93c8af24f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z13 : W := mkw 0x00081a08a0000000 0x0001034114000000 0x40003e01e0000000 0x080007c03c000000

def z14 : W := mkw 0x079b360000000000 0x20f366c000000000 0xc7fffe0000000000 0x78ffffc000000000

def z15 : W := mkw 0x171a320012cc8001 0x22e3464002599000 0x021c380002ee0000 0x00438700005dc000

def z16 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x180000001d11f1fb 0x8300000003a23e3f

def z17 : W := mkw 0xe7dfbfffe0648488 0xbcfbf7fffc0c9091 0xe7ffffffe1e1819a 0xfcfffffffc3c3033

def z18 : W := mkw 0x0004001200000000 0x0000800240000000 0xa21c003e00000000 0x54438007c0000000

def z19 : W := mkw 0x97ff77b61ffded83 0x32ffeef6c3ffbdb0 0xfffffffe1fffff86 0x7fffffffc3fffff0

def z20 : W := mkw 0x5732e9699f9a5a60 0x4ae65d2d33f34b4c 0xfffff9f99ffe7e65 0x7fffff3f33ffcfcc

def z21 : W := mkw 0x0004001200200480 0x0000800240040090 0x021c003802e00e04 0x00438007005c01c0

def z22 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z23 : W := mkw 0xf7ffffffffff86a9 0xbefffffffffff0d5 0xffffffffffff8fff 0xfffffffffffff1ff

def z24 : W := mkw 0x0602600016180000 0x00c04c0002c30000 0x5603f8001e1e0000 0x6ac07f0003c3c000

def z25 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z26 : W := mkw 0x977001a41b806902 0x12ee003483700d20 0xbde001c61d007182 0x77bc0038c3a00e30

def z27 : W := mkw 0x102000001ba06d82 0x0204000003740db0 0x180000001fe07f86 0x0300000003fc0ff0

def z28 : W := mkw 0x00a1c4410d111040 0x0014388821a22208 0xfde3c7c19d11f061 0x7fbc78f833a23e0c

def z29 : W := mkw 0xc71e3b3aa0000000 0xb8e3c76754000000 0x021c383800000000 0x0043870700000000

def z30 : W := mkw 0xefffffffed113150 0xbdfffffffda2262a 0xfffffffffd11f1fb 0xffffffffffa23e3f

def z31 : W := mkw 0xc71e3b3aa06686a8 0xb8e3c767540cd0d5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z32 : W := mkw 0x0820c0410d113150 0x0104180821a2262a 0x7c03c1c19d11f1fb 0xef80783833a23e3f

def z33 : W := mkw 0x20cd9edfe0000000 0x0419b3dbfc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z34 : W := mkw 0x977001a41b806902 0x12ee003483700d20 0x05e001c01c007000 0x20bc003803800e00

def z35 : W := mkw 0x173a72001fdd8001 0x22e74e4003fbb000 0x121c38001fff8000 0x0243870003fff000

def z36 : W := mkw 0x4602a969920a4a20 0x48c0552d32414944 0x6603f9f9820e0e04 0x6cc07f3f3041c1c0

def z37 : W := mkw 0xf7dfbffff2cc8001 0xbefbf7fffe599000 0xe7ffffffe2ee0000 0x7cfffffffc5dc000

def z38 : W := mkw 0x6ee3e5e55f197950 0x4ddc7cbcabe32f2a 0x05e3c1c01c007000 0x20bc783803800e00

def z39 : W := mkw 0x977001a41ba06d82 0x12ee003483740db0 0x1de001c01fe07f86 0x23bc003803fc0ff0

def z40 : W := mkw 0xc71efb7bb61a5a60 0xf8e3df6f76c34b4c 0x7e1ff9f99e1e7e65 0x6fc3ff3f33c3cfcc

def z41 : W := mkw 0x97ff7fbebfffefab 0x32ffeff7d7fffdf5 0xffffffffffffffff 0xffffffffffffffff

def z42 : W := mkw 0xc71ebb7ba0000000 0xb8e3d76f74000000 0x661ff9f980000000 0x6cc3ff3f30000000

def z43 : W := mkw 0x179b360012cc8001 0x22f366c002599000 0xc7fffe0002ee0000 0x78ffffc0005dc000

def z44 : W := mkw 0x00004000161a5a60 0x4000080002c34b4c 0x180000001e1e7e65 0x0300000003c3cfcc

def z45 : W := mkw 0xe7dffffff61a5a60 0xfcfbfffffec34b4c 0xfffffffffe1e7e65 0x7fffffffffc3cfcc

def z46 : W := mkw 0x0793240000000000 0x20f2648000000000 0x05e3c00000000000 0x20bc780000000000

def z47 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z48 : W := mkw 0x0000080880020220 0x0000010110004044 0x7a003839821e0e65 0x4f4007073043c1cc

def z49 : W := mkw 0x000c121220648488 0x00018242440c9091 0x801c060661e1819a 0x900380c0cc3c3033

def z50 : W := mkw 0x0600012012004800 0x00c0002402400900 0x3e0001f81e007e04 0x67c0003f03c00fc0

def z51 : W := mkw 0x173000001b800000 0x02e6000003700000 0x97fc00001fe00000 0x72ff800003fc0000

def z52 : W := mkw 0x28c184c540003150 0x05183098a800062a 0xede3c7c7e00071fb 0xfdbc78f8fc000e3f

def z53 : W := mkw 0x17bf7e1abfff86a9 0x22f7efc357fff0d5 0xfffffe3fffff8fff 0xffffffc7fffff1ff

def z54 : W := mkw 0xf7ffbffffba06d82 0xbefff7ffff740db0 0xffffffffffe07f86 0x7ffffffffffc0ff0

def z55 : W := mkw 0x17bb76001f990001 0x22f76ec003f32000 0xc7fffe001c000000 0x78ffffc003800000

def z56 : W := mkw 0xf7ffffffffdd8001 0xbefffffffffbb000 0xf7ffffffffff8000 0x7efffffffffff000

def z57 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x100000001fff8000 0x0200000003fff000

def z58 : W := mkw 0x0004001200200480 0x0000800240040090 0xfa1c063fe3f18fff 0xdf4380c7fc7e31ff

def z59 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0xc1fffe07e0000000 0x183fffc0fc000000

def z60 : W := mkw 0xe7d3adedc0000000 0xbcfa75bdb8000000 0x67e3f9f980000000 0x6cfc7f3f30000000

def z61 : W := mkw 0x00a144000d110000 0x0014288001a22000 0xd5e3c6001d118000 0x7abc78c003a23000

def z62 : W := mkw 0x10ab76001fdd8001 0x22156ec003fbb000 0x5003fe001fff8000 0x0a007fc003fff000

def z63 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xfffffffffe007e04 0x7fffffffffc00fc0

def z64 : W := mkw 0x00000000120a4a20 0x4000000002414944 0x00000000020e0e04 0x000000000041c1c0

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0xf8000607e11181fb 0xdf0000c0fc22303f

def z66 : W := mkw 0x28eddedfed77b7f8 0x051dbbdbfdaef6ff 0xffffffffffffffff 0xffffffffffffffff

def z67 : W := mkw 0xe7dfbfffe0206d82 0xbcfbf7fffc040db0 0xefffffffe0007f86 0x7dfffffffc000ff0

def z68 : W := mkw 0x460efb7bb67edee8 0x48c1df6f76cfdbdd 0xfe1fffffffffffff 0xffc3ffffffffffff

def z69 : W := mkw 0x3ffbf6c55fddb151 0x27ff7ed8abfbb62a 0xffffffc7fffff1fb 0xfffffff8fffffe3f

def z70 : W := mkw 0x4000896980025a60 0x4800112d30004b4c 0x280001f980007e65 0x0500003f30000fcc

def z71 : W := mkw 0x0000000000206d82 0x0000000000040db0 0x0800000000007f86 0x0100000000000ff0

def z72 : W := mkw 0x182040001fb17dd2 0x0304080003f62fba 0x180000001ff1ffff 0x8300000003fe3fff

def z73 : W := mkw 0x46022928920a4a20 0x48c0452512414944 0x02003838020e0e04 0x004007070041c1c0

def z74 : W := mkw 0x17bb36001b800000 0x22f766c003700000 0xd7fffe001fe00000 0x7affffc003fc0000

def z75 : W := mkw 0x977c1bbebbe6efaa 0x12ef8377d77cddf5 0xfffc3fffffffffff 0xffff87ffffffffff

def z76 : W := mkw 0x28e1048449012110 0x051c209089202422 0x81e006066101819a 0x903c00c0cc203033

def z77 : W := mkw 0x002040000d110000 0x0004080001a22000 0x100000001d118000 0x0200000003a23000

def z78 : W := mkw 0x9174009609a02582 0x122e8012c13404b0 0x81fc000601e00182 0x103f8000c03c0030

def z79 : W := mkw 0x17bbf6411fdd9041 0x22f77ec823fbb208 0xffffffc19ffff061 0x7ffffff833fffe0c

def z80 : W := mkw 0x00000000006686a8 0x00000000000cd0d5 0xf8000607e3ff8fff 0xdf0000c0fc7ff1ff

def z81 : W := mkw 0x102852001fdd8001 0x02050a4003fbb000 0xd21c3e001fff8000 0x5a4387c003fff000

def z82 : W := mkw 0x977001a41b806902 0x12ee003483700d20 0x97fc01c01fe07000 0x72ff803803fc0e00

def z83 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xfffffe07ffff81fb 0xffffffc0fffff03f

def z84 : W := mkw 0x408bfe49845f9261 0x68117fc9308bf24c 0x4003fe01801f8061 0x08007fc03003f00c

def z85 : W := mkw 0x4602a96980000000 0x08c0552d30000000 0x6603f9f980000000 0x6cc07f3f30000000

def z86 : W := mkw 0x284080c540003150 0x05081018a800062a 0xf80007c7e111f1fb 0xdf0000f8fc223e3f

def z87 : W := mkw 0x4602212012084800 0x48c0442402410900 0x0000000000000000 0x0000000000000000

def z88 : W := mkw 0x008b7e08a45f8229 0x20116fc1148bf045 0x4003fe01e01f8079 0x88007fc03c03f00f

def z89 : W := mkw 0x0004081aa02206a8 0x00008103540440d5 0x2800003fe0000fff 0x85000007fc0001ff

def z90 : W := mkw 0xe04489ffe0000000 0x9c08913ffc000000 0x200001ffe0000000 0x0400003ffc000000

def z91 : W := mkw 0x4602e16116185840 0x48c05c2c22c30b08 0x0403c1c01c007000 0x2080783803800e00

def z92 : W := mkw 0xc712212000000000 0xb8e2442400000000 0x0000000000000000 0x0000000000000000

def z93 : W := mkw 0x0602200000000000 0x00c0440000000000 0x4603f80000000000 0x68c07f0000000000

def z94 : W := mkw 0x17b364001fdd8001 0x22f66c8003fbb000 0x15e3c0001fff8000 0x22bc780003fff000

def z95 : W := mkw 0x6083a44140000000 0xac10748828000000 0x0003c00000000000 0x0000780000000000

def z96 : W := mkw 0x00000000006686a8 0x00000000000cd0d5 0x1800000003ff8fff 0x83000000007ff1ff

def z97 : W := mkw 0x284080c540003150 0x05081018a800062a 0x280001c7e00071fb 0x85000038fc000e3f

def z98 : W := mkw 0x0040008400002100 0x0008001080000420 0x280001c600007182 0x05000038c0000e30

def z99 : W := mkw 0x9774c1f71fb07dc2 0x12ee983ee3f60fb8 0xffffc1ff9ff07fe7 0x7ffff83ff3fe0ffc

def z100 : W := mkw 0x0800400004111050 0x010008000082220a 0x0000000000118079 0x800000000002300f

def z101 : W := mkw 0xa1dd169660000000 0xb43ba2d2cc000000 0x81fc060660000000 0x103f80c0cc000000

def z102 : W := mkw 0x804401b600206d82 0x10088036c0040db0 0x280001fe00007f86 0x0500003fc0000ff0

def z103 : W := mkw 0x6ee3ededdf1b7b70 0x4ddc7dbdbbe36f6e 0xffe3ffffff1fffff 0xfffc7fffffe3ffff

def z104 : W := mkw 0x0060008409002100 0x000c001081200420 0xbde001c61d007182 0x77bc0038c3a00e30

def z105 : W := mkw 0xbff5c5f75fb17dd2 0x17feb8beebf62fba 0xffffc7fffff1ffff 0xfffff8fffffe3fff

def z106 : W := mkw 0x57bfff7bbfffdee9 0x6af7ffef77fffbdd 0xffffffffffffffff 0xffffffffffffffff

def z107 : W := mkw 0xe7d7a5f740000000 0xbcfaf4bee8000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z108 : W := mkw 0x079b360000448000 0x20f366c000089000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z109 : W := mkw 0x102040001fdfda61 0x4204080003fbfb4c 0x180000001ffffe65 0x0300000003ffffcc

def z110 : W := mkw 0x37fbf6c55fdd8001 0x26ff7ed8abfbb000 0xf7ffffc7ffff8000 0x7efffff8fffff000

def z111 : W := mkw 0x106000841ba06d82 0x020c001083740db0 0xbde001c61fe07f86 0x77bc0038c3fc0ff0

def z112 : W := mkw 0x0008120000448000 0x0001024000089000 0xd21c3e0003ff8000 0x5a4387c0007ff000

def z113 : W := mkw 0x00081a08a0468228 0x000103411408d045 0x40003e01e01f8079 0x880007c03c03f00f

def z114 : W := mkw 0x4602a16100000000 0x08c0542c20000000 0x0403c1c000000000 0x2080783800000000

def z115 : W := mkw 0x060e7a1ab67e86a8 0x00c1cf4356cfd0d5 0xfe1ffe3fffff8fff 0xffc3ffc7fffff1ff

def z116 : W := mkw 0x0008120000448000 0x0001024000089000 0x021c380002ee0000 0x00438700005dc000

def z117 : W := mkw 0x000c1a1aa0000000 0x0001834354000000 0xe21c3e3fe0000000 0x5c4387c7fc000000

def z118 : W := mkw 0x8044009600202582 0x10088012c00404b0 0x0000000600000182 0x00000000c0000030

def z119 : W := mkw 0x4002e849841a1260 0x48005d093083424c 0x4003f801801e0061 0x08007f003003c00c

def z120 : W := mkw 0x0008120020448008 0x0001024004089001 0x0000060060018018 0x800000c00c003003

def z121 : W := mkw 0xa1dd1e9ee06686a8 0xb43ba3d3dc0cd0d5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z122 : W := mkw 0x977c13b61be4ed82 0x12ef8276c37c9db0 0xfffc3ffe1fffff86 0x7fff87ffc3fffff0

def z123 : W := mkw 0x17b364001f990001 0x22f66c8003f32000 0x05e3c0001c000000 0x20bc780003800000

def z124 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xd21c3e3803ff8e04 0x5a4387c7007ff1c0

def z125 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xc1e3c607e11181fb 0x983c78c0fc22303f

def z126 : W := mkw 0xc04489ff80227fe2 0x5808913ff0044ffc 0x280001ff80007fe7 0x0500003ff0000ffc

def z127 : W := mkw 0xd776e9ff9fba7fe2 0x5aeedd3ff3f74ffc 0xfffff9ff9ffe7fe7 0x7fffff3ff3ffcffc

def z128 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x000000001c007000 0x0000000003800e00

def z129 : W := mkw 0xa7d585f740000000 0x14fab0bee8000000 0xe7ffc7ffe0000000 0x7cfff8fffc000000

def z130 : W := mkw 0xd776a9ff9ba06d82 0x1aeed53ff3740db0 0xfffff9ff9fe07f86 0x7fffff3ff3fc0ff0

def z131 : W := mkw 0x608bbe49e0000000 0xac1177c93c000000 0x4003fe01e0000000 0x08007fc03c000000

def z132 : W := mkw 0x4002e849961a5a60 0x48005d0932c34b4c 0x5803f8019e1e7e65 0x0b007f0033c3cfcc

def z133 : W := mkw 0xeff3e5e54d113150 0xbdfe7cbca9a2262a 0x05e3c1c01c007000 0x20bc783803800e00

def z134 : W := mkw 0xd776e1f71fb87dc2 0x5aeedc3ee3f70fb8 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z135 : W := mkw 0x008b7600045d8001 0x20116ec0008bb000 0x4003fe00001f8000 0x08007fc00003f000

def z136 : W := mkw 0x0008120000448000 0x0001024000089000 0xfa1c3e07e3ff81fb 0xdf4387c0fc7ff03f

def z137 : W := mkw 0x875401b600000000 0x10ea8036c0000000 0xa7fc01fe00000000 0x74ff803fc0000000

def z138 : W := mkw 0x082c5a1aad77b7f8 0x01058b4355aef6ff 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z139 : W := mkw 0xf7ffbffffbe6efaa 0xbefff7ffff7cddf5 0xffffffffffffffff 0xffffffffffffffff

def z140 : W := mkw 0x171e3a1ab2ee86a9 0x22e3c743565dd0d5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z141 : W := mkw 0x173260001f980000 0x02e64c0003f30000 0xd7fff8001ffe0000 0x7affff0003ffc000

def z142 : W := mkw 0x0000080880020220 0x0000010110004044 0x2800003980000e65 0x05000007300001cc

def z143 : W := mkw 0xe7dfbfffe0200480 0xbcfbf7fffc040090 0xffffffffe3e00f86 0x7ffffffffc7c01f0

def z144 : W := mkw 0x875001a400000000 0x10ea003480000000 0x05e001c000000000 0x20bc003800000000

def z145 : W := mkw 0x082040000d113150 0x0104080001a2262a 0xf8000607fd11f1fb 0xdf0000c0ffa23e3f

def z146 : W := mkw 0x082040001f1b7b70 0x4104080003e36f6e 0x180000001f1fffff 0x8300000003e3ffff

def z147 : W := mkw 0x173812001bc48000 0x02e7024003789000 0xd7fc3e001fff8000 0x7aff87c003fff000

def z148 : W := mkw 0x8004013200204c82 0x1000802640040990 0x0000003800000e04 0x00000007000001c0

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0xd000060001118000 0x5a0000c000223000

def z150 : W := mkw 0x0000804100001040 0x0000100820000208 0x280001c180007061 0x0500003830000e0c

def z151 : W := mkw 0x0004081aa02206a8 0x00008103540440d5 0xba1c003fe3e00fff 0xd7438007fc7c01ff

def z152 : W := mkw 0x66c3adedc0000000 0x0cd875bdb8000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z153 : W := mkw 0x17b916001bc58001 0x22f722c00378b000 0x97fc06001fe18000 0x72ff80c003fc3000

def z154 : W := mkw 0x28e1c4c55f1b7b70 0x451c3898abe36f6e 0xfde3c7c7ff1fffff 0xffbc78f8ffe3ffff

def z155 : W := mkw 0x906401b61ba06d82 0x120c8036c3740db0 0x380001fe1fe07f86 0x0700003fc3fc0ff0

def z156 : W := mkw 0x28edd6d76d75b5d8 0x051dbadaedaeb6bb 0xfdffc7c7fdf1f1fb 0xffbff8f8ffbe3e3f

def z157 : W := mkw 0x0000c04104101040 0x0000180820820208 0x7c03c1c19c107061 0x6f80783833820e0c

def z158 : W := mkw 0x11bd1e1aa9e786a9 0x2237a3c3553cf0d5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z159 : W := mkw 0x917400961ba06d82 0x122e8012c3740db0 0x99fc00061fe07f86 0x133f8000c3fc0ff0

def z160 : W := mkw 0x11b9160009c58001 0x223722c00138b000 0x81fc060001e18000 0x103f80c0003c3000

def z161 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x68003e3fe01f8fff 0x8d0007c7fc03f1ff

def z162 : W := mkw 0xf7dfbffff2a04c82 0xbefbf7fffe540990 0xe7ffffffe2e00e04 0x7cfffffffc5c01c0

def z163 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a00003802000e04 0x47400007004001c0

def z164 : W := mkw 0x875401b600200480 0x10ea8036c0040090 0xbffc01fe03e00f86 0x77ff803fc07c01f0

def z165 : W := mkw 0x0000400004101040 0x0000080000820208 0x180000001c107061 0x0300000003820e0c

def z166 : W := mkw 0x0800000000003150 0x010000000000062a 0x08000000000071fb 0x8100000000000e3f

def z167 : W := mkw 0x0008120000000000 0x0001024000000000 0xc21c3e0000000000 0x584387c000000000

def z168 : W := mkw 0x28ed16966965a598 0x051da2d2cd2cb4b3 0x81fc060661e1819a 0x903f80c0cc3c3033

def z169 : W := mkw 0x57bbf7611fddd841 0x6af77eec23fbbb08 0xd7ffffc01ffff000 0x7afffff803fffe00

def z170 : W := mkw 0xe7dfffffe4101040 0xbcfbfffffc820208 0xfffffffffc107061 0x7fffffffff820e0c

def z171 : W := mkw 0x977c1bbebbe6efaa 0x12ef8377d77cddf5 0xbffc39fe1fee7f86 0x77ff873fc3fdcff0

def z172 : W := mkw 0x2ee3e4c55f193150 0x05dc7c98abe3262a 0xffe3ffc7ff1ff1fb 0xfffc7ff8ffe3fe3f

def z173 : W := mkw 0xe1dd9fffe0000000 0xbc3bb3fffc000000 0xa1fc07ffe0000000 0x143f80fffc000000

def z174 : W := mkw 0x1000000012a04c82 0x0200000002540990 0x0000000002e00e04 0x00000000005c01c0

def z175 : W := mkw 0x288bf641445d9051 0x25117ec8288bb20a 0x4003fe01e01f8079 0x88007fc03c03f00f

def z176 : W := mkw 0x4000896980000000 0x0800112d30000000 0x200001f980000000 0x0400003f30000000

def z177 : W := mkw 0x977001a41b806902 0x12ee003483700d20 0x3fe001f81e007e04 0x67fc003f03c00fc0

def z178 : W := mkw 0x102040001fff86a9 0x0204080003fff0d5 0x180000001fff8fff 0x8300000003fff1ff

def z179 : W := mkw 0x4000896980025a60 0x4800112d30004b4c 0x7a0039f9821e7e65 0x4f40073f3043cfcc

def z180 : W := mkw 0xbffddffffff7fffa 0x17ffbbfffffeffff 0xffffffffffffffff 0xffffffffffffffff

def z181 : W := mkw 0xb7f585f75ba06d82 0x16feb0beeb740db0 0xffffc7ffffe07f86 0x7ffff8fffffc0ff0

def z182 : W := mkw 0x11bb76000ddd8001 0x22376ec001bbb000 0xc1fffe0001ff8000 0x183fffc0003ff000

def z183 : W := mkw 0x284488dfe02237f8 0x0508911bfc0446ff 0x280001ffe0007fff 0x8500003ffc000fff

def z184 : W := mkw 0xd7ffffff9fffffe3 0x7afffffff3fffffc 0xffffffff9fffffe7 0x7ffffffff3fffffc

def z185 : W := mkw 0xe75489ffe0000000 0x9cea913ffc000000 0xa7fc01ffe0000000 0x74ff803ffc000000

def z186 : W := mkw 0x28e1048449012110 0x051c209089202422 0xf9e00607e11181fb 0xdf3c00c0fc22303f

def z187 : W := mkw 0x977409be9ba26fa2 0x12ee8137d3744df4 0xfffc39ff9ffe7fe7 0x7fff873ff3ffcffc

def z188 : W := mkw 0x0004081aa02206a8 0x00008103540440d5 0x7a00383fe21e0fff 0xcf400707fc43c1ff

def z189 : W := mkw 0x46026928961a5a60 0x48c04d2512c34b4c 0x1a0038381e1e7e65 0x0340070703c3cfcc

def z190 : W := mkw 0x2840008440002110 0x0508001088000422 0x000000066000019a 0x80000000cc000033

def z191 : W := mkw 0x2ffbf6c54d113150 0x25ff7ed8a9a2262a 0xffffffc7fd11f1fb 0xfffffff8ffa23e3f

def z192 : W := mkw 0x20c1048440000000 0x0418209088000000 0x81e0060660000000 0x103c00c0cc000000

def z193 : W := mkw 0x68e3eccdcd1b3370 0x4d1c7d99b9a3666e 0xfde3ffc7fd1ff1fb 0xffbc7ff8ffa3fe3f

def z194 : W := mkw 0x977441b61fba7fe2 0x52ee8836c3f74ffc 0xbffc01fe1ffe7fe7 0x77ff803fc3ffcffc

def z195 : W := mkw 0xa7df369660000000 0xb4fbe6d2cc000000 0xc7fffe0660000000 0x78ffffc0cc000000

def z196 : W := mkw 0xe7dfb7f760000000 0xbcfbf6feec000000 0x85ffc7c660000000 0x30bff8f8cc000000

def z197 : W := mkw 0xc79f3f3aa0000000 0xb8f3e7e754000000 0xc7fffe3800000000 0x78ffffc700000000

def z198 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x07fff9f800000000 0x20ffff3f00000000

def z199 : W := mkw 0x0000c84984121260 0x000019093082424c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z200 : W := mkw 0x00000000006686a8 0x00000000000cd0d5 0x0000000002ee0e04 0x00000000005dc1c0

def z201 : W := mkw 0x977c13b63be4ed8a 0x12ef8276c77c9db1 0xbffc07fe7fe1ff9e 0xf7ff80ffcffc3ff3

def z202 : W := mkw 0x460ebb7ba06686a8 0x08c1d76f740cd0d5 0xfe1fffffe3ff8fff 0xffc3fffffc7ff1ff

def z203 : W := mkw 0xb7ff76967fdd8001 0xb6ffeed2cffbb000 0xd7fffe067fff8000 0x7affffc0cffff000

def z204 : W := mkw 0x000c1a1aa0200480 0x0001834354040090 0xfa1c3e3fe3e00f86 0x5f4387c7fc7c01f0

def z205 : W := mkw 0x0000c04104101040 0x0000180820820208 0xfc03c7c7fd11f1fb 0xff8078f8ffa23e3f

def z206 : W := mkw 0x00004000045d8001 0x00000800008bb000 0x00000000001f8000 0x000000000003f000

def z207 : W := mkw 0x0000000012004800 0x0000000002400900 0x180000001e007e04 0x0300000003c00fc0

def z208 : W := mkw 0xd77629be9baa6fa2 0x5aeec537d3754df4 0xbffc39fe1fee7f86 0x77ff873fc3fdcff0

def z209 : W := mkw 0xd716293a92aa4ea2 0x5ae2c527525549d4 0x021c383802ee0e04 0x00438707005dc1c0

def z210 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xfffc07fffff1ffff 0xffff80fffffe3fff

def z211 : W := mkw 0x182040001fddb151 0x0304080003fbb62a 0x180000001ffff1fb 0x8300000003fffe3f

def z212 : W := mkw 0x4602a96980025a60 0x48c0552d30004b4c 0x6e03f9f980007e65 0x6dc07f3f30000fcc

def z213 : W := mkw 0x97f765b61fb96d83 0x32feecb6c3f72db0 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z214 : W := mkw 0x77bbfe49ffdd8001 0xaef77fc93ffbb000 0xd7fffe01ffff8000 0x7affffc03ffff000

def z215 : W := mkw 0xf7f3e5e55f990001 0xbefe7cbcabf32000 0x05e3c1c01c000000 0x20bc783803800000

def z216 : W := mkw 0xe04c9bffe06686a8 0x9c09937ffc0cd0d5 0xfa1c3fffe3ff8fff 0xdf4387fffc7ff1ff

def z217 : W := mkw 0xefdfbfffe0003150 0xbdfbf7fffc00062a 0xefffffffe00071fb 0xfdfffffffc000e3f

def z218 : W := mkw 0x4602e96996180000 0x08c05d2d32c30000 0x7603f9f99e1e0000 0x6ec07f3f33c3c000

def z219 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x07fc01f81ee07e04 0x20ff803f03dc0fc0

def z220 : W := mkw 0x0000000000448000 0x0000000000089000 0x1000000003ff8000 0x02000000007ff000

def z221 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x07fff8001eee0000 0x20ffff0003ddc000

def z222 : W := mkw 0xe7ffffffed110000 0xbcfffffffda22000 0xf7fffffffd118000 0x7effffffffa23000

def z223 : W := mkw 0x479bff69961a5a60 0x68f37fed32c34b4c 0xfffffff99e1e7e65 0x7fffffff33c3cfcc

def z224 : W := mkw 0x284080c540003150 0x05081018a800062a 0x000001c000007000 0x0000003800000e00

def z225 : W := mkw 0x00004808961a5a60 0x4000090112c34b4c 0x7a0038399e1e7e65 0x4f40070733c3cfcc

def z226 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe11181fb 0xfffffffffc22303f

def z227 : W := mkw 0x479bbf6980000000 0x28f377ed30000000 0xe7fffff980000000 0x7cffffff30000000

def z228 : W := mkw 0x1000000012cc8001 0x0200000002599000 0x0000000002ee0000 0x00000000005dc000

def z229 : W := mkw 0x57bbfe499fdf9261 0x6af77fc933fbf24c 0xd7fffe019fff8061 0x7affffc033fff00c

def z230 : W := mkw 0x8154009600000000 0x102a8012c0000000 0x81fc000600000000 0x103f8000c0000000

def z231 : W := mkw 0x877401b609002100 0x10ee8036c1200420 0xbffc01fe1d007182 0x77ff803fc3a00e30

def z232 : W := mkw 0x917c1a9ea9e6a7aa 0x122f8353d53cd4f5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z233 : W := mkw 0x0004001200200480 0x0000800240040090 0xba1c003e03e00f86 0x57438007c07c01f0

def z234 : W := mkw 0xe7dbbfede0000000 0xbcfb77fdbc000000 0x45e3ffc1e0000000 0x28bc7ff83c000000

def z235 : W := mkw 0x4002e969841a5a60 0x48005d2d30834b4c 0x6803f9f9801e7e65 0x0d007f3f3003cfcc

def z236 : W := mkw 0x668bff69f61a5a60 0xecd17fed3ec34b4c 0x7e03fff9fe1e7e65 0x6fc07fff3fc3cfcc

def z237 : W := mkw 0x0600092892024a20 0x00c0012512404944 0x7e0039f99e1e7e65 0x6fc0073f33c3cfcc

def z238 : W := mkw 0xe7d3ededd61a5a60 0xfcfa7dbdbac34b4c 0x7fe3f9f99e1e7e65 0x6ffc7f3f33c3cfcc

def z239 : W := mkw 0x1020000009c58001 0x020400000138b000 0x0000000001e18000 0x00000000003c3000

def z240 : W := mkw 0x9174009609a02582 0x122e8012c13404b0 0xbdfc01c61de07182 0x77bf8038c3bc0e30

def z241 : W := mkw 0x082040000d77b7f8 0x0104080001aef6ff 0x180000001fffffff 0x8300000003ffffff

def z242 : W := mkw 0x4000c969961a5a60 0x4800192d32c34b4c 0x380001f99e1e7e65 0x0700003f33c3cfcc

def z243 : W := mkw 0x4002e849841a1260 0x48005d093083424c 0x7c03f9c19c1e7061 0x6f807f383383ce0c

def z244 : W := mkw 0x066001a41b006900 0x00cc003483600d20 0xbfe001fe1f007f86 0x77fc003fc3e00ff0

def z245 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xa81c063fe1e18fff 0x950380c7fc3c31ff

def z246 : W := mkw 0x977409bebba26faa 0x12ee8137d7744df5 0xbffc01ffffe07fff 0xf7ff803ffffc0fff

def z247 : W := mkw 0x28c1c4c544113150 0x05183898a882262a 0x6803c7c7e011f1fb 0x8d0078f8fc023e3f

def z248 : W := mkw 0x4e22e9699f1b7b70 0x49c45d2d33e36f6e 0x7e03f9f99f1fffff 0xefc07f3f33e3ffff

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000607e0000000 0x5c0000c0fc000000

def z250 : W := mkw 0x00ad5e1aad7786a8 0x0015abc355aef0d5 0xfffffe3fffff8fff 0xffffffc7fffff1ff

def z251 : W := mkw 0x68e1cdedcd137b70 0x4d1c39bdb9a26f6e 0xfde3c7fffd11ffff 0xffbc78ffffa23fff

def z252 : W := mkw 0xe84489ffe0003150 0x9d08913ffc00062a 0x280001ffe00071fb 0x8500003ffc000e3f

def z253 : W := mkw 0x973401321ba06d82 0x12e6802643740db0 0x1a1c00381fe07f86 0x0343800703fc0ff0

def z254 : W := mkw 0x162260001fdd8001 0x02c44c0003fbb000 0x5603f8001fff8000 0x6ac07f0003fff000

def z255 : W := mkw 0x40022808800a0220 0x4800450110014044 0x00003800000e0000 0x000007000001c000

def z256 : W := mkw 0x00000808806686a8 0x00000101100cd0d5 0x7a00383983ff8fff 0xcf400707307ff1ff

def z257 : W := mkw 0xe04081e540000000 0x9c08103ca8000000 0x000001c000000000 0x0000003800000000

def z258 : W := mkw 0x000c1a1aa0448000 0x0001834354089000 0xf21c3e3fe3ff8000 0x5e4387c7fc7ff000

def z259 : W := mkw 0xc756a9ff80000000 0x18ead53ff0000000 0xe7fff9ff80000000 0x7cffff3ff0000000

def z260 : W := mkw 0x3ff3e4c55f993151 0x27fe7c98abf3262a 0x05e3c1c01c007000 0x20bc783803800e00

def z261 : W := mkw 0x68ebfecded113150 0xad1d7fd9bda2262a 0xfde3ffc7fd11f1fb 0xffbc7ff8ffa23e3f

def z262 : W := mkw 0x460e3b3ab26ecea8 0x48c1c767564dd9d5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z264 : W := mkw 0x000c121220648488 0x00018242440c9091 0xba1c063e63e18f9e 0xd74380c7cc7c31f3

def z265 : W := mkw 0x079b7600045d8001 0x20f36ec0008bb000 0xc7fffe00001f8000 0x78ffffc00003f000

def z266 : W := mkw 0x1fbb76001fddb151 0x23f76ec003fbb62a 0xdffffe001ffff1fb 0xfbffffc003fffe3f

def z267 : W := mkw 0x97fb77a41fdde903 0x32ff6ef483fbbd20 0xd7ffffc01ffff000 0x7afffff803fffe00

def z268 : W := mkw 0x28e144844d112110 0x051c289089a22422 0xd5e3c6067d11819a 0xfabc78c0cfa23033

def z269 : W := mkw 0xb7fd17b67ba06d82 0xb6ffa2f6cf740db0 0xbffc07fe7fe07f86 0x77ff80ffcffc0ff0

def z270 : W := mkw 0xe7dfbfffe02206a8 0xbcfbf7fffc0440d5 0xefffffffe0000fff 0xfdfffffffc0001ff

def z271 : W := mkw 0x177000841b802100 0x02ee001083700420 0xbffc01c61fe07182 0x77ff8038c3fc0e30

def z272 : W := mkw 0xe7df3fbee0000000 0xbcfbe7f7dc000000 0x83fc3e3e60000000 0x107f87c7cc000000

def z273 : W := mkw 0x102c5a1abfff86a9 0x02058b4357fff0d5 0xfa1c3e3fffff8fff 0xdf4387c7fffff1ff

def z274 : W := mkw 0x9714013212a04c82 0x12e2802642540990 0x021c003802e00e04 0x00438007005c01c0

def z275 : W := mkw 0xc71e3b3ab20a4a20 0xf8e3c76756414944 0x021c3838020e0e04 0x004387070041c1c0

def z276 : W := mkw 0x0064009609202580 0x000c8012c12404b0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z277 : W := mkw 0x9710012012804802 0x12e2002402500900 0x0000000000000000 0x0000000000000000

def z278 : W := mkw 0xffffffffffb17dd2 0xbffffffffff62fba 0xfffffffffff1ffff 0xfffffffffffe3fff

def z279 : W := mkw 0xc004093aa0000000 0x9800812754000000 0x0000003800000000 0x0000000700000000

def z280 : W := mkw 0x0060008409002100 0x000c001081200420 0x81e0000601000182 0x103c0000c0200030

def z281 : W := mkw 0x2881c44144111050 0x051038882882220a 0xf803c607e11181fb 0xdf0078c0fc22303f

def z282 : W := mkw 0x0000c041161a5a60 0x4000180822c34b4c 0x7c03c1c19e1e7e65 0x6f80783833c3cfcc

def z283 : W := mkw 0x0004001220200488 0x0000800244040091 0x000000066000019a 0x80000000cc000033

def z284 : W := mkw 0x6ee3ededdf1b7b70 0x4ddc7dbdbbe36f6e 0x7fe3f9f99e1e7e65 0x6ffc7f3f33c3cfcc

def z285 : W := mkw 0xf7f7a5f75ba06d82 0xbefef4beeb740db0 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z286 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x4403f9c19c1e7061 0x28807f383383ce0c

def z287 : W := mkw 0xb9f5c4d74db135d2 0x173eb89ae9b626ba 0xfdffc7c7fdf1f1fb 0xffbff8f8ffbe3e3f

def z288 : W := mkw 0x0081040000000000 0x0010208000000000 0xc5e3c60000000000 0x78bc78c000000000

def z289 : W := mkw 0x1118120000c48001 0x2223024000189000 0x001c000000e00000 0x00038000001c0000

def z290 : W := mkw 0xe7ffbfffe9002100 0xbcfff7fffd200420 0xfffffffffd007182 0x7fffffffffa00e30

def z291 : W := mkw 0x60008849e0000000 0x8c0011093c000000 0x00000001e0000000 0x000000003c000000

def z292 : W := mkw 0x9714013212a04c82 0x12e2802642540990 0xba1c003e03e00f86 0x57438007c07c01f0

def z293 : W := mkw 0x975401b612a06d82 0x12ea8036c2540db0 0x2a1c01fe02e07f86 0x0543803fc05c0ff0

def z294 : W := mkw 0x0600012012004800 0x00c0002402400900 0x0200003802000e04 0x00400007004001c0

def z295 : W := mkw 0xbff1c5e55f917952 0x17fe38bcabf22f2a 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z296 : W := mkw 0x97ff76961ffda583 0x32ffeed2c3ffb4b0 0xd7fffe061fff8182 0x7affffc0c3fff030

def z297 : W := mkw 0x57bbff699fdd8001 0x2af77fed33fbb000 0xf7fffff99fff8000 0x7effffff33fff000

def z298 : W := mkw 0x46022928920a4a20 0x48c0452512414944 0x3e0039f81e0e7e04 0x67c0073f03c1cfc0

def z299 : W := mkw 0x284c9adfe066b7f8 0x0509935bfc0cd6ff 0xfa1c3fffe3ffffff 0xdf4387fffc7fffff

def z300 : W := mkw 0x0000c04104101040 0x0000180820820208 0x0403c1c01c007000 0x2080783803800e00

def z301 : W := mkw 0x28e1048449012110 0x051c209089202422 0x01e0000000000000 0x003c000000000000

def z302 : W := mkw 0x46022928920a4a20 0x48c0452512414944 0x7a003839821e0e65 0x4f4007073043c1cc

def z303 : W := mkw 0x0600000012000000 0x00c0000002400000 0x160000001e000000 0x62c0000003c00000

def z304 : W := mkw 0x171a720016dc8001 0x22e34e4002db9000 0x561ff8001efe0000 0x6ac3ff0003dfc000

def z305 : W := mkw 0xf7ffbffffb806902 0xbefff7ffff700d20 0xe7fffffffc007000 0x7cffffffff800e00

def z306 : W := mkw 0xe7dfbfffe0448000 0xbcfbf7fffc089000 0xf7ffffffe3ff8000 0x7efffffffc7ff000

def z307 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xd5e3c7c01d11f000 0x7abc78f803a23e00

def z308 : W := mkw 0xbff5c5f75fb17dd2 0x17feb8beebf62fba 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z309 : W := mkw 0x28e1c4c54d77b7f8 0x051c3898a9aef6ff 0xfde3c7c7ffffffff 0xffbc78f8ffffffff

def z310 : W := mkw 0x60cbbecde0000000 0xac1977d9bc000000 0xe5e3ffc7e0000000 0x7cbc7ff8fc000000

def z311 : W := mkw 0x102040001f990001 0x0204080003f32000 0x000000001c000000 0x0000000003800000

def z312 : W := mkw 0x1710000012800000 0x02e2000002500000 0x021c000002e00000 0x00438000005c0000

def z313 : W := mkw 0x6ee3e5e55f197950 0x4ddc7cbcabe32f2a 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z314 : W := mkw 0x9f7441b61fb17dd2 0x13ee8836c3f62fba 0xbffc01fe1ff1ffff 0xf7ff803fc3fe3fff

def z315 : W := mkw 0x4602e161161a5a60 0x48c05c2c22c34b4c 0x1c03c1c01e1e7e65 0x2380783803c3cfcc

def z316 : W := mkw 0x00ab76000d5d8001 0x20156ec001abb000 0xd5e3fe001d1f8000 0x7abc7fc003a3f000

def z317 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x85fc01c61de07182 0x30bf8038c3bc0e30

def z318 : W := mkw 0x28e9decded57b378 0x051d3bd9bdaaf66f 0xfde3ffc7fd1ff1fb 0xffbc7ff8ffa3fe3f

def z319 : W := mkw 0x8714013200000000 0x10e2802640000000 0x021c003800000000 0x0043800700000000

def z320 : W := mkw 0x000c1212206686a8 0x00018242440cd0d5 0x981c060663ff8fff 0x930380c0cc7ff1ff

def z321 : W := mkw 0x2881c44144111050 0x051038882882220a 0x4003c601e0118079 0x880078c03c02300f

def z322 : W := mkw 0x28eddedfed113150 0x051dbbdbfda2262a 0xfffffffffd11f1fb 0xffffffffffa23e3f

def z323 : W := mkw 0x08a144000d113150 0x0114288001a2262a 0xdde3c6001d11f1fb 0xfbbc78c003a23e3f

def z324 : W := mkw 0x0000c04104101040 0x0000180820820208 0x4003c00180100061 0x080078003002000c

def z325 : W := mkw 0x9114001200a00482 0x1222800240140090 0x001c000000e00000 0x00038000001c0000

def z326 : W := mkw 0xe7dffffff67edee8 0xfcfbfffffecfdbdd 0xffffffffffffffff 0xffffffffffffffff

def z327 : W := mkw 0x57bb7f289fdfca21 0x6af76fe513fbf944 0xd7fffe381fff8e04 0x7affffc703fff1c0

def z328 : W := mkw 0x17fb76841fdda101 0x22ff6ed083fbb420 0xffffffc61ffff182 0x7ffffff8c3fffe30

def z329 : W := mkw 0x0602e04116181040 0x00c05c0822c30208 0x7e03f9c19e1e7061 0x6fc07f3833c3ce0c

def z330 : W := mkw 0x2ee1c5e55f117950 0x05dc38bcabe22f2a 0xffe3c7ffff11ffff 0xfffc78ffffe23fff

def z331 : W := mkw 0x0000000000020220 0x0000000000004044 0x18000000021e0e65 0x030000000043c1cc

def z332 : W := mkw 0x00a1040009010000 0x0014208001202000 0x81e0060001018000 0x103c00c000203000

def z333 : W := mkw 0x57b3e5611f995841 0x6af67cac23f32b08 0x05e3c1c01c007000 0x20bc783803800e00

def z334 : W := mkw 0x0602612016184800 0x00c04c2402c30900 0x7e03f9f81e1e7e04 0x6fc07f3f03c3cfc0

def z335 : W := mkw 0x0820000009012110 0x0104000001202422 0x000000000101819a 0x8000000000203033

def z336 : W := mkw 0x400a3a08a0000000 0xa801474114000000 0x0000380000000000 0x0000070000000000

def z337 : W := mkw 0x28c1c4c544111050 0x05183898a882220a 0xe5e3c7c7e0118079 0xfcbc78f8fc02300f

def z338 : W := mkw 0x17b364001f990001 0x22f66c8003f32000 0xd5e3c6001d118000 0x7abc78c003a23000

def z339 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xe21c3e3fe2ee0e04 0x5c4387c7fc5dc1c0

def z340 : W := mkw 0x102400121ba06d82 0x0204800243740db0 0xba1c003e1fe07f86 0x57438007c3fc0ff0

def z341 : W := mkw 0x97ff37b61ba06d82 0x32ffe6f6c3740db0 0xfffffffe1fe07f86 0x7fffffffc3fc0ff0

def z342 : W := mkw 0xb1fd169669a02582 0xb63fa2d2cd3404b0 0x81fc060661e00182 0x103f80c0cc3c0030

def z343 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z344 : W := mkw 0x0000400016180000 0x0000080002c30000 0x100000001e1e0000 0x0200000003c3c000

def z345 : W := mkw 0xd77489ff9ba27fe2 0x5aee913ff3744ffc 0xbffc01ff9fe07fe7 0x77ff803ff3fc0ffc

def z346 : W := mkw 0x00a956000d558000 0x00152ac001aab000 0xd7fffe001fff8000 0x7affffc003fff000

def z347 : W := mkw 0xa9fdd6d76d113150 0xb53fbadaeda2262a 0xfdffc7c7fd11f1fb 0xffbff8f8ffa23e3f

def z348 : W := mkw 0x06a364001f190000 0x00d46c8003e32000 0xd7e3fe001f1f8000 0x7afc7fc003e3f000

def z349 : W := mkw 0x0000000000648488 0x00000000000c9091 0x0000000001e1819a 0x80000000003c3033

def z350 : W := mkw 0x000a3200004c8001 0x2001464000099000 0x00003800000e0000 0x000007000001c000

def z351 : W := mkw 0xb1fd169669c58001 0xb63fa2d2cd38b000 0x81fc060661e18000 0x103f80c0cc3c3000

def z352 : W := mkw 0x975401b612a04c82 0x12ea8036c2540990 0xa7fc01fe02e00e04 0x74ff803fc05c01c0

def z353 : W := mkw 0x173c1a1abbe686a8 0x02e78343577cd0d5 0xfffc3e3fffff8fff 0xffff87c7fffff1ff

def z354 : W := mkw 0xe04489ffe02206a8 0x9c08913ffc0440d5 0x280001ffe0000fff 0x8500003ffc0001ff

def z355 : W := mkw 0x2860c0c54d113150 0x050c1818a9a2262a 0x380001c7fd11f1fb 0x87000038ffa23e3f

def z356 : W := mkw 0x20cd9edfe06686a8 0x0419b3dbfc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z357 : W := mkw 0x87df37b600000000 0x30fbe6f6c0000000 0xe7fffffe00000000 0x7cffffffc0000000

def z358 : W := mkw 0xc756e9ff961a5a60 0x58eadd3ff2c34b4c 0xfffff9ff9e1e7e65 0x7fffff3ff3c3cfcc

def z359 : W := mkw 0x3ffffedfffffb7f9 0x27ffffdbfffff6ff 0xffffffffffffffff 0xffffffffffffffff

def z360 : W := mkw 0x97fd17b61be5ed83 0x32ffa2f6c37cbdb0 0xbffc07fe1fe1ff86 0x77ff80ffc3fc3ff0

def z361 : W := mkw 0x3fbbf6415fdd9051 0x27f77ec82bfbb20a 0xd7fffe01ffff8079 0xfaffffc03ffff00f

def z362 : W := mkw 0x102040001fba7fe2 0x4204080003f74ffc 0x180000001ffe7fe7 0x0300000003ffcffc

def z363 : W := mkw 0x000c1a1aa0020220 0x0001834354004044 0xfa1c3e3fe21e0e65 0x5f4387c7fc43c1cc

def z364 : W := mkw 0x102000001b800000 0x0204000003700000 0x100000001fe00000 0x0200000003fc0000

def z365 : W := mkw 0x079f3e1aa06686a8 0x20f3e7c3540cd0d5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z366 : W := mkw 0xe7dffffff6185840 0xfcfbfffffec30b08 0xe7fffffffc007000 0x7cffffffff800e00

def z367 : W := mkw 0x173001201b804800 0x02e6002403700900 0xbffc01f81fe07e04 0x77ff803f03fc0fc0

def z368 : W := mkw 0xf7ffbffffb800000 0xbefff7ffff700000 0xf7ffffffffe00000 0x7efffffffffc0000

def z369 : W := mkw 0x20c184c540000000 0x04183098a8000000 0x05e3c1c000000000 0x20bc783800000000

def z370 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0xfe03ffffff1fffff 0xffc07fffffe3ffff

def z371 : W := mkw 0x0199160000000000 0x203322c000000000 0x81fc060000000000 0x103f80c000000000

def z372 : W := mkw 0xe0cfbfffe0000000 0xbc19f7fffc000000 0x6003ffffe0000000 0x0c007ffffc000000

def z373 : W := mkw 0xd772e1e51f987942 0x5aee5c3ca3f30f28 0x05e3c1c01c007000 0x20bc783803800e00

def z374 : W := mkw 0xa7dd17b660000000 0xb4fba2f6cc000000 0xa7fc07fe60000000 0x74ff80ffcc000000

def z375 : W := mkw 0x6883ec49c41b1270 0x4d107d893883624e 0x4003fe01e01f8079 0x88007fc03c03f00f

def z376 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x2de001fe1c007f86 0x25bc003fc3800ff0

def z377 : W := mkw 0x4002a84980000000 0x0800550930000000 0x4003f80180000000 0x08007f0030000000

def z378 : W := mkw 0x06004120161a5a60 0x40c0082402c34b4c 0x3e0001f81e1e7e65 0x67c0003f03c3cfcc

def z379 : W := mkw 0xe646a9ffe0000000 0x9cc8d53ffc000000 0x6603f9ffe0000000 0x6cc07f3ffc000000

def z380 : W := mkw 0x17bf7e1abfff86a9 0x22f7efc357fff0d5 0xd7fffe381fff8e04 0x7affffc703fff1c0

def z381 : W := mkw 0xc71e3b3aa06686a8 0xb8e3c767540cd0d5 0x021c383802ee0e04 0x00438707005dc1c0

def z382 : W := mkw 0x0020000009002100 0x0004000001200420 0x180000001d007182 0x0300000003a00e30

def z383 : W := mkw 0x079b760016180000 0x20f36ec002c30000 0xd7fffe001e1e0000 0x7affffc003c3c000

def z384 : W := mkw 0x0000080880000000 0x0000010110000000 0x6200383980000000 0x4c40070730000000

def z385 : W := mkw 0xbff505b65ba16d92 0x17fea0b6cb742db2 0xbffc07fe7fe1ff9e 0xf7ff80ffcffc3ff3

def z386 : W := mkw 0x4002e04104181040 0x48005c0820830208 0x0003c00000000000 0x0000780000000000

def z387 : W := mkw 0x977c1bbebba06d82 0x12ef8377d7740db0 0xfffc3fffffe07f86 0x7fff87fffffc0ff0

def z388 : W := mkw 0x977400961ba02582 0x12ee8012c37404b0 0x97fc00061fe00182 0x72ff8000c3fc0030

def z389 : W := mkw 0x060c1b3ab266cea8 0x00c18367564cd9d5 0xfe1c3fffffffffff 0xffc387ffffffffff

def z390 : W := mkw 0x4602e96996185840 0x48c05d2d32c30b08 0x6603f9f99c007000 0x6cc07f3f33800e00

def z391 : W := mkw 0x4000c96984125a60 0x4800192d30824b4c 0x7c03c1f99c107e65 0x6f80783f33820fcc

def z392 : W := mkw 0x0004001200200480 0x0000800240040090 0x2800003e00000f86 0x05000007c00001f0

def z393 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x45e3fe001c1f8000 0x28bc7fc00383f000

def z394 : W := mkw 0x2840c0c544103150 0x05081818a882062a 0x7c03c1c7fc1071fb 0xef807838ff820e3f

def z395 : W := mkw 0xa84481f740207dd2 0x1508903ee8040fba 0x280001ffe0007fff 0x8500003ffc000fff

def z396 : W := mkw 0x20c1c4c544101040 0x04183898a8820208 0xfde3c7c7fc107061 0x7fbc78f8ff820e0c

def z397 : W := mkw 0x11b956001fdd8001 0x22372ac003fbb000 0x91fc06001fff8000 0x123f80c003fff000

def z398 : W := mkw 0x4004897ba0225ee8 0x4800912f74044bdd 0x280001ffe0007fff 0x8500003ffc000fff

def z399 : W := mkw 0x102c1a1abbe6efaa 0x02058343577cddf5 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z400 : W := mkw 0x977401b61b806902 0x12ee8036c3700d20 0xa7fc01fe1c007000 0x74ff803fc3800e00

def z401 : W := mkw 0xf7fffffffffded83 0xbeffffffffffbdb0 0xffffffffffffff86 0x7ffffffffffffff0

def z402 : W := mkw 0x679bbe49e0000000 0xacf377c93c000000 0xc7fffe01e0000000 0x78ffffc03c000000

def z403 : W := mkw 0x668bbf69e0000000 0xacd177ed3c000000 0x6603fff9e0000000 0x6cc07fff3c000000

def z404 : W := mkw 0x00081a08a0468228 0x000103411408d045 0xd21c3e01e3ff8079 0xda4387c03c7ff00f

def z405 : W := mkw 0x4602e96984101040 0x08c05d2d30820208 0x7e03f9f99c107061 0x6fc07f3f33820e0c

def z406 : W := mkw 0x28e5c4d74d3135d0 0x051cb89ae9a626ba 0xffffc7fffff1ffff 0xfffff8fffffe3fff

def z407 : W := mkw 0xe7dffffff6180000 0xbcfbfffffec30000 0xf7fffffffe1e0000 0x7effffffffc3c000

def z408 : W := mkw 0xe7dfbfffe0468228 0xbcfbf7fffc08d045 0xe7ffffffe01f8079 0xfcfffffffc03f00f

def z409 : W := mkw 0x973401321ba04c82 0x12e6802643740990 0x97fc00381fe00e04 0x72ff800703fc01c0

def z410 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x0603f9f81e0e7e04 0x20c07f3f03c1cfc0

def z411 : W := mkw 0x102040001ffded83 0x0204080003ffbdb0 0x180000001fffff86 0x0300000003fffff0

def z412 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x85ffc6001de18000 0x30bff8c003bc3000

def z413 : W := mkw 0x38e1c4c55fddb151 0x071c3898abfbb62a 0xfde3c7c7fffff1fb 0xffbc78f8fffffe3f

def z414 : W := mkw 0x4602a96992004800 0x08c0552d32400900 0x7e03f9f99e007e04 0x6fc07f3f33c00fc0

def z415 : W := mkw 0x38e1c4c55fb17dd2 0x071c3898abf62fba 0xfde3c7c7fff1ffff 0xffbc78f8fffe3fff

def z416 : W := mkw 0xefffffffed77b7f8 0xbdfffffffdaef6ff 0xffffffffffffffff 0xffffffffffffffff

def z417 : W := mkw 0x4602292880000000 0x08c0452510000000 0x0200383800000000 0x0040070700000000

def z418 : W := mkw 0xe7dfbfffe0025a60 0xfcfbf7fffc004b4c 0xefffffffe0007e65 0x7dfffffffc000fcc

def z419 : W := mkw 0x66c3ededd61a5a60 0x4cd87dbdbac34b4c 0xffe3fffffe1e7e65 0x7ffc7fffffc3cfcc

def z420 : W := mkw 0x4602e16116185840 0x48c05c2c22c30b08 0x3e03c1f81e007e04 0x67c0783f03c00fc0

def z421 : W := mkw 0x17bf76121ffd8481 0x22f7eec243ffb090 0xfffffe3e1fff8f86 0x7fffffc7c3fff1f0

def z422 : W := mkw 0x9170008409802102 0x122e001081300420 0x01e0000000000000 0x003c000000000000

def z423 : W := mkw 0x97bf77321ffdcc83 0x32f7eee643ffb990 0xd7fffe381fff8e04 0x7affffc703fff1c0

def z424 : W := mkw 0x17bb7e089fdf8221 0x22f76fc113fbf044 0xfffffe399fff8e65 0x7fffffc733fff1cc

def z425 : W := mkw 0x17bb36001bcd8001 0x22f766c00379b000 0x83fc3e0003ef8000 0x107f87c0007df000

def z426 : W := mkw 0x0060008409002100 0x000c001081200420 0x05e001c01c007000 0x20bc003803800e00

def z427 : W := mkw 0x17bb76001ffded83 0x22f76ec003ffbdb0 0xdffffe001fffff86 0x7bffffc003fffff0

def z428 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xbde3c1c61d007182 0x77bc7838c3a00e30

def z429 : W := mkw 0x688bfe49e4111050 0xad117fc93c82220a 0x4003fe01e0118079 0x88007fc03c02300f

def z430 : W := mkw 0xe04489ffe0206d82 0x9c08913ffc040db0 0x280001ffe0007f86 0x0500003ffc000ff0

def z431 : W := mkw 0x9174009609a02582 0x122e8012c13404b0 0xbbfc003e03e00f86 0x577f8007c07c01f0

def z432 : W := mkw 0x4602a969920a5a60 0x48c0552d32414b4c 0x2a0039f9820e7e65 0x0540073f3041cfcc

def z433 : W := mkw 0x00000000002206a8 0x00000000000440d5 0x0800000000000fff 0x81000000000001ff

def z434 : W := mkw 0x804c1bbea066efaa 0x10098377d40cddf5 0xfa1c3fffe3ffffff 0xdf4387fffc7fffff

def z435 : W := mkw 0x288dde5be47796f8 0x0511bbcb7c8ef2df 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z436 : W := mkw 0x000c121220000000 0x0001824244000000 0x801c060660000000 0x100380c0cc000000

def z437 : W := mkw 0x28ed1e9ee967a7b8 0x051da3d3dd2cf4f7 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z438 : W := mkw 0xf7ffbfffe9a02582 0xbefff7fffd3404b0 0xe7ffffffe1e00182 0x7cfffffffc3c0030

def z439 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x1a1c383803ff8fff 0x83438707007ff1ff

def z440 : W := mkw 0x17bb77201fddc801 0x22f76ee403fbb900 0xfffffff81ffffe04 0x7fffffff03ffffc0

def z441 : W := mkw 0x5622e9699fdfda61 0x4ac45d2d33fbfb4c 0x7e03f9f99ffffe65 0x6fc07f3f33ffffcc

def z442 : W := mkw 0x28e1cccdcd133370 0x051c3999b9a2666e 0xffe3ffffff1fffff 0xfffc7fffffe3ffff

def z443 : W := mkw 0xb9f5049649a12592 0x173ea092c93424b2 0x81fc060661e1819a 0x903f80c0cc3c3033

def z444 : W := mkw 0x28e184c549013150 0x051c3098a920262a 0xa9e007c7e101f1fb 0x953c00f8fc203e3f

def z445 : W := mkw 0x0002600004180000 0x00004c0000830000 0x4003f800001e0000 0x08007f000003c000

def z446 : W := mkw 0x400afa49a45e9268 0x48015f49348bd24d 0x4003fe01e01f8079 0x88007fc03c03f00f

def z447 : W := mkw 0x971e333212eccc83 0x32e3c666425d9990 0x021c383802ee0e04 0x00438707005dc1c0

def z448 : W := mkw 0x086040840d113150 0x010c081081a2262a 0xbde001c61d11f1fb 0xf7bc0038c3a23e3f

def z449 : W := mkw 0x0083640004190001 0x20106c8000832000 0x0003c00000000000 0x0000780000000000

def z450 : W := mkw 0x204080c540000000 0x04081018a8000000 0x200001c7e0000000 0x04000038fc000000

def z451 : W := mkw 0xfff7edffdfbb7ff2 0x5ffefdbffbf76ffe 0xffffffffffffffff 0xffffffffffffffff

def z452 : W := mkw 0x07bb76000d110000 0x20f76ec001a22000 0xd7fffe001d118000 0x7affffc003a23000

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000011181fb 0x830000000022303f

def z454 : W := mkw 0x917401b609a06d82 0x122e8036c1340db0 0xa9fc01fe01e07f86 0x153f803fc03c0ff0

def z455 : W := mkw 0x91fd169609e5a583 0x323fa2d2c13cb4b0 0x81fc060601e18182 0x103f80c0c03c3030

def z456 : W := mkw 0x000c1a1aa0648488 0x00018343540c9091 0xe21c3e3fe1e1819a 0xdc4387c7fc3c3033

def z457 : W := mkw 0xe646e9fff61a5a60 0xdcc8dd3ffec34b4c 0x7e03f9fffe1e7e65 0x6fc07f3fffc3cfcc

def z458 : W := mkw 0xd77e3bbebba06d82 0xbaefc777d7740db0 0xbffc39fe1fe07f86 0x77ff873fc3fc0ff0

def z459 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xe5e3c7c7fc007000 0x7cbc78f8ff800e00

def z460 : W := mkw 0xd71e3b3ab2a04c82 0xbae3c76756540990 0x021c383802e00e04 0x00438707005c01c0

def z461 : W := mkw 0x608fbe5be0000000 0xac11f7cb7c000000 0xe21ffe3fe0000000 0x5c43ffc7fc000000

def z462 : W := mkw 0xa1d1048440000000 0xb43a209088000000 0x01e0000000000000 0x003c000000000000

def z463 : W := mkw 0x97f545b61fb16d82 0x12fea8b6c3f62db0 0xffffc7fe1ff1ff86 0x7ffff8ffc3fe3ff0

def z464 : W := mkw 0x0600012000000000 0x00c0002400000000 0x260001f800000000 0x64c0003f00000000

def z465 : W := mkw 0x2881c44144111050 0x051038882882220a 0x0003c00000000000 0x0000780000000000

def z466 : W := mkw 0xe7dfbfffe0020220 0xbcfbf7fffc004044 0xffffffffe21e0e65 0x7ffffffffc43c1cc

def z467 : W := mkw 0x102000001be6efaa 0x02040000037cddf5 0x180000001fffffff 0x8300000003ffffff

def z468 : W := mkw 0xeff3e5e54d113150 0xbdfe7cbca9a2262a 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z469 : W := mkw 0xe7d7adffe0000000 0xbcfaf5bffc000000 0x25e3c1ffe0000000 0x24bc783ffc000000

def z470 : W := mkw 0x400efa5ba47e96e8 0x4801df4b748fd2dd 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z471 : W := mkw 0x000cda5ba47696e8 0x00019b4b748ed2dd 0xfe1fffffffffffff 0xffc3ffffffffffff

def z472 : W := mkw 0x27dbb6c540000000 0x24fb76d8a8000000 0xe7ffffc7e0000000 0x7cfffff8fc000000

def z473 : W := mkw 0x17bf7e1abfdd8001 0x22f7efc357fbb000 0xf7fffe3fffff8000 0x7effffc7fffff000

def z474 : W := mkw 0x000c1a1aa0000000 0x0001834354000000 0xfa1c3e3fe11181fb 0xdf4387c7fc22303f

def z475 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x7de3c1c19c107061 0x6fbc783833820e0c

def z476 : W := mkw 0xa1dd169660648488 0xb43ba2d2cc0c9091 0x81fc060661e1819a 0x903f80c0cc3c3033

def z477 : W := mkw 0x4000092880024a20 0x4800012510004944 0x0000003800000e04 0x00000007000001c0

def z478 : W := mkw 0xe7dbb7e540000000 0xbcfb76fca8000000 0xc7ffffc000000000 0x78fffff800000000

def z479 : W := mkw 0x468bff69965fda61 0x68d17fed32cbfb4c 0x7e03fff99e1ffe65 0x6fc07fff33c3ffcc

def z480 : W := mkw 0x875c1bbea0000000 0x10eb8377d4000000 0xe7fc3fffe0000000 0x7cff87fffc000000

def z481 : W := mkw 0xa9fd169669012110 0xb53fa2d2cd202422 0x81fc06066101819a 0x903f80c0cc203033

def z482 : W := mkw 0x57b3ed699f9b5a61 0x6af67dad33f36b4c 0x7fe3f9f99e1e7e65 0x6ffc7f3f33c3cfcc

def z483 : W := mkw 0xf7ffbfffe9c58001 0xbefff7fffd38b000 0xe7ffffffe1e18000 0x7cfffffffc3c3000

def z484 : W := mkw 0x0710000000000000 0x00e2000000000000 0x87fc000000000000 0x70ff800000000000

def z485 : W := mkw 0x4606e97bb63a5ee8 0x48c0dd2f76c74bdd 0x7e03f9fffe1e7fff 0xefc07f3fffc3cfff

def z486 : W := mkw 0x2881040040010010 0x0510208008002002 0x0000060060018018 0x800000c00c003003

def z487 : W := mkw 0xbff1c5e55f917952 0x17fe38bcabf22f2a 0x05e3c1c01c007000 0x20bc783803800e00

def z488 : W := mkw 0x00081a0880468220 0x000103411008d044 0xfa1c3e3983ff8e65 0x5f4387c7307ff1cc

def z489 : W := mkw 0x6ee3ededcd113150 0x0ddc7dbdb9a2262a 0xffe3fffffd11f1fb 0xfffc7fffffa23e3f

def z490 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xfde3c7c7e11181fb 0xffbc78f8fc22303f

def z491 : W := mkw 0xefdfffffe4111050 0xbdfbfffffc82220a 0xe7ffffffe0118079 0xfcfffffffc02300f

def z492 : W := mkw 0x971c1b3ab2e6ceaa 0x12e38367565cd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z493 : W := mkw 0x39f9d6c54dd5b151 0x273f3ad8a9bab62a 0xfdffc7c7fdf1f1fb 0xffbff8f8ffbe3e3f

def z494 : W := mkw 0xa1dd96d760000000 0xb43bb2daec000000 0xe5ffc7c7e0000000 0x7cbff8f8fc000000

def z495 : W := mkw 0xd7bf7f3abfdd8001 0xbaf7efe757fbb000 0xd7fffe381fff8000 0x7affffc703fff000

def z496 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xc01c3e07e1ff81fb 0x980387c0fc3ff03f

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x921c000003e00000 0x52438000007c0000

def z498 : W := mkw 0xefffbfffe9012110 0xbdfff7fffd202422 0xe7ffffffe101819a 0xfcfffffffc203033

def z499 : W := mkw 0x97f365a41f996903 0x32fe6cb483f32d20 0x05e3c1c01c007000 0x20bc783803800e00

def z500 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x85e3c7c67d01f19a 0xb0bc78f8cfa03e33

def z501 : W := mkw 0xa1dd1e9ee0000000 0xb43ba3d3dc000000 0xe3fc3e3fe0000000 0x5c7f87c7fc000000

def z502 : W := mkw 0x39f9168449c5a111 0x273f22d08938b422 0x81fc060661e1819a 0x903f80c0cc3c3033

def z503 : W := mkw 0x20e1c4c54d110000 0x041c3898a9a22000 0xf5e3c7c7fd118000 0x7ebc78f8ffa23000

def z504 : W := mkw 0xe0c58dffe0000000 0x9c18b1bffc000000 0xe5e3c7ffe0000000 0x7cbc78fffc000000

def z505 : W := mkw 0x0008120000448000 0x0001024000089000 0x40003e00001f8000 0x080007c00003f000

def z506 : W := mkw 0x0000080880020220 0x0000010110004044 0x40003801801e0061 0x080007003003c00c

def z507 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x2a1c383fe2ee0fff 0x85438707fc5dc1ff

def z508 : W := mkw 0x3ff1c4c55f913150 0x07fe3898abf2262a 0xffffc7c7fff1f1fb 0xfffff8f8fffe3e3f

def z509 : W := mkw 0x0602600016180000 0x00c04c0002c30000 0x0403c0001c000000 0x2080780003800000

def z510 : W := mkw 0x46026928961a4a20 0x48c04d2512c34944 0x5603f8381e1e0e04 0x6ac07f0703c3c1c0

def z511 : W := mkw 0x000c121220648488 0x00018242440c9091 0xd21c3e0663ff819a 0xda4387c0cc7ff033

def z512 : W := mkw 0x608bbe49e0468228 0xac1177c93c08d045 0x4003fe01e01f8079 0x88007fc03c03f00f

def z513 : W := mkw 0x7ffbffeddfdffb71 0x6fff7ffdbbfbff6e 0xffffffffffffffff 0xffffffffffffffff

def z514 : W := mkw 0xe79fbf7be0000000 0xbcf3f7ef7c000000 0x421ffe39e0000000 0x0843ffc73c000000

def z515 : W := mkw 0xaff5c5f74d113150 0x15feb8bee9a2262a 0xffffc7fffd11f1fb 0xfffff8ffffa23e3f

def z516 : W := mkw 0xefffffffed113150 0xbdfffffffda2262a 0xe7fffffffc007000 0x7cffffffff800e00

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x52003800021e0000 0x4a4007000043c000

def z518 : W := mkw 0x0000000000000000 0x0000000000000000 0x28000007e00001fb 0x85000000fc00003f

def z519 : W := mkw 0xe7dfffffe45d8001 0xbcfbfffffc8bb000 0xe7ffffffe01f8000 0x7cfffffffc03f000

def z520 : W := mkw 0xc646e9ff963a7fe2 0x58c8dd3ff2c74ffc 0x7e03f9ff9e1e7fe7 0x6fc07f3ff3c3cffc

def z521 : W := mkw 0x1712200012880001 0x22e2440002510000 0x0000000000000000 0x0000000000000000

def z522 : W := mkw 0x3ff3e4c55f993151 0x27fe7c98abf3262a 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z523 : W := mkw 0x0004081aa02206a8 0x00008103540440d5 0xf800063fe1118fff 0xdf0000c7fc2231ff

def z524 : W := mkw 0x4000884980021260 0x480011093000424c 0x0000000180000061 0x000000003000000c

def z525 : W := mkw 0x4606e97b963a5ee0 0x48c0dd2f72c74bdc 0xfe1ff9ff9ffe7fe7 0x7fc3ff3ff3ffcffc

def z526 : W := mkw 0x2089160060000000 0xa41122c00c000000 0x0000060060000000 0x000000c00c000000

def z527 : W := mkw 0x00e144840d112100 0x001c289081a22420 0xfde3c7c61d11f182 0x7fbc78f8c3a23e30

def z528 : W := mkw 0x000c1a1aa02206a8 0x00018343540440d5 0xea1c3e3fe0000fff 0xdd4387c7fc0001ff

def z529 : W := mkw 0x804401b600000000 0x10088036c0000000 0x200001fe00000000 0x0400003fc0000000

def z530 : W := mkw 0x3ffb76845fdda111 0x27ff6ed08bfbb422 0xd7fffe067fff819a 0xfaffffc0cffff033

def z531 : W := mkw 0x28e1048449012110 0x051c209089202422 0xbde007c67d01f19a 0xf7bc00f8cfa03e33

def z532 : W := mkw 0x0000400016185840 0x4000080002c30b08 0x000000001c007000 0x0000000003800e00

def z533 : W := mkw 0x4602e969967edee8 0x48c05d2d32cfdbdd 0x7e03f9f99fffffff 0xefc07f3f33ffffff

def z534 : W := mkw 0xc75e3bbea0000000 0xb8ebc777d4000000 0xa7fc39fe00000000 0x74ff873fc0000000

def z535 : W := mkw 0x000c1a1aa0000000 0x0001834354000000 0x021c383800000000 0x0043870700000000

def z536 : W := mkw 0xc71e3b3aa0000000 0xb8e3c76754000000 0xe21c3e3fe0000000 0x5c4387c7fc000000

def z537 : W := mkw 0x17b364001f990001 0x22f66c8003f32000 0x57e3f8001e1e0000 0x6afc7f0003c3c000

def z538 : W := mkw 0x608bfe49e41a1260 0xec117fc93c83424c 0x4003fe01e01e0061 0x08007fc03c03c00c

def z539 : W := mkw 0x1130000009800000 0x0226000001300000 0x81fc000001e00000 0x103f8000003c0000

def z540 : W := mkw 0x00004000167edee8 0x4000080002cfdbdd 0x180000001fffffff 0x8300000003ffffff

def z541 : W := mkw 0x977401b609a02582 0x12ee8036c13404b0 0xa7fc01fe01e00182 0x74ff803fc03c0030

def z542 : W := mkw 0x571a3b2892ceca21 0x6ae347651259d944 0x021c383802ee0e04 0x00438707005dc1c0

def z543 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x45e3c7c1fc11f079 0xa8bc78f83f823e0f

def z544 : W := mkw 0x804409bea0226faa 0x10088137d4044df5 0x280001ffe0007fff 0x8500003ffc000fff

def z545 : W := mkw 0x0000000000468228 0x000000000008d045 0x00000000001f8079 0x800000000003f00f

def z546 : W := mkw 0x4600896992025a60 0x48c0112d32404b4c 0x3e0001f99e007e65 0x67c0003f33c00fcc

def z547 : W := mkw 0x10a144001fdd8001 0x0214288003fbb000 0xd5e3c6001fff8000 0x7abc78c003fff000

def z548 : W := mkw 0x17bb76001fdfda61 0x62f76ec003fbfb4c 0xdffffe001ffffe65 0x7bffffc003ffffcc

def z549 : W := mkw 0x17b364001f990001 0x22f66c8003f32000 0x97ffc0001fe00000 0x72fff80003fc0000

def z550 : W := mkw 0x4602e849961a1260 0x48c05d0932c3424c 0x5603f8019e1e0061 0x6ac07f0033c3c00c

def z551 : W := mkw 0x286080c549003150 0x050c1018a920062a 0xbde001c7fd0071fb 0xf7bc0038ffa00e3f

def z552 : W := mkw 0x0081440004110000 0x0010288000822000 0x4003c60000118000 0x080078c000023000

def z553 : W := mkw 0x0008120000448000 0x0001024000089000 0x801c060001e18000 0x100380c0003c3000

def z554 : W := mkw 0x00081a08a0468228 0x000103411408d045 0xf8003e07e11f81fb 0xdf0007c0fc23f03f

def z555 : W := mkw 0xe04489ffe0025a60 0xdc08913ffc004b4c 0x280001ffe0007e65 0x0500003ffc000fcc

def z556 : W := mkw 0x875401b600206d82 0x10ea8036c0040db0 0xaffc01fe00007f86 0x75ff803fc0000ff0

def z557 : W := mkw 0x684089edc0027b70 0x4d08113db8004f6e 0x280001ffe0007fff 0x8500003ffc000fff

def z558 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x83fc003e03e00f86 0x107f8007c07c01f0

def z559 : W := mkw 0xf7ffffffff990001 0xbefffffffff32000 0xe7fffffffc000000 0x7cffffffff800000

def z560 : W := mkw 0x46a3ed699f1b5a60 0x48d47dad33e36b4c 0xffe3fff99f1ffe65 0x7ffc7fff33e3ffcc

def z561 : W := mkw 0x0004081aa06686a8 0x00008103540cd0d5 0x3800003fe3ff8fff 0x87000007fc7ff1ff

def z562 : W := mkw 0x000c1a1aa0468228 0x000183435408d045 0xe21c3e3fe01f8079 0xdc4387c7fc03f00f

def z563 : W := mkw 0xf7ffffffffdfda61 0xfefffffffffbfb4c 0xfffffffffffffe65 0x7fffffffffffffcc

def z564 : W := mkw 0x17bb76001fff86a9 0x22f76ec003fff0d5 0xdffffe001fff8fff 0xfbffffc003fff1ff

def z565 : W := mkw 0x0060008409002100 0x000c001081200420 0xfde007c7fd11f1fb 0xffbc00f8ffa23e3f

def z566 : W := mkw 0x008b7600045d8001 0x20116ec0008bb000 0xd21ffe0003ff8000 0x5a43ffc0007ff000

def z567 : W := mkw 0x804001a400006902 0x1008003480000d20 0x000001c000007000 0x0000003800000e00

def z568 : W := mkw 0x28a1c4414d113150 0x0514388829a2262a 0x5803c601fd11f1fb 0x8b0078c03fa23e3f

def z569 : W := mkw 0xd772e9ed9f9a7b62 0x5aee5d3db3f34f6c 0x7fe3f9f99e1e7e65 0x6ffc7f3f33c3cfcc

def z570 : W := mkw 0x28e184c549012110 0x051c3098a9202422 0xe5e3c7c7e101819a 0xfcbc78f8fc203033

def z571 : W := mkw 0x173040001fdd8001 0x02e6080003fbb000 0x97fc00001fff8000 0x72ff800003fff000

def z572 : W := mkw 0x0004081aa02206a8 0x00008103540440d5 0x0000003800000e04 0x00000007000001c0

def z573 : W := mkw 0x977e33b61beced83 0x32efc676c37d9db0 0xbffc39fe1fee7f86 0x77ff873fc3fdcff0

def z574 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c0001c01c007000 0x6780003803800e00

def z575 : W := mkw 0xe7dfbffff20a4a20 0xfcfbf7fffe414944 0xe7ffffffe20e0e04 0x7cfffffffc41c1c0

def z576 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x2c03c1f99c007e65 0x2580783f33800fcc

def z577 : W := mkw 0xbffff7f75ffdfdd3 0x37fffefeebffbfba 0xffffffffffffffff 0xffffffffffffffff

def z578 : W := mkw 0x2800804140001050 0x050010082800020a 0x00000001e0000079 0x800000003c00000f

def z579 : W := mkw 0x00a144000d110000 0x0014288001a22000 0x05e3c0001c000000 0x20bc780003800000

def z580 : W := mkw 0x804401b600206d82 0x10088036c0040db0 0xba1c01fe03e07f86 0x5743803fc07c0ff0

def z581 : W := mkw 0x4002e849841a1260 0x48005d093083424c 0x7a03f839821e0e65 0x4f407f073043c1cc

def z582 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x1de3c1c01d11f1fb 0xa3bc783803a23e3f

def z583 : W := mkw 0x864401b612206d82 0x10c88036c2440db0 0x3e0001fe1e007f86 0x67c0003fc3c00ff0

def z584 : W := mkw 0x000c121200648480 0x00018242400c9090 0xfa1c3e3e03ff8f86 0x5f4387c7c07ff1f0

def z585 : W := mkw 0x0004081a802206a0 0x00008103500440d4 0xfa1c383f83fe0fe7 0x5f438707f07fc1fc

def z586 : W := mkw 0xf7f3a5e55b806902 0xbefe74bcab700d20 0x05e3c1c01c007000 0x20bc783803800e00

def z587 : W := mkw 0xf7fbf7e55fdd8001 0xbeff7efcabfbb000 0xd7ffffc01fff8000 0x7afffff803fff000

def z588 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x7a1c383982fe0e65 0x4f438707305fc1cc

def z589 : W := mkw 0x102000001b806902 0x0204000003700d20 0x000000001c007000 0x0000000003800e00

def z590 : W := mkw 0x6eefffffff7ffff8 0x4dddffffffefffff 0xffffffffffffffff 0xffffffffffffffff

def z591 : W := mkw 0x0602200012080000 0x00c0440002410000 0x02003800020e0000 0x004007000041c000

def z592 : W := mkw 0x000c121220648488 0x00018242440c9091 0xf81c0607e1f181fb 0xdf0380c0fc3e303f

def z593 : W := mkw 0xf7ffffffffba7fe2 0xfefffffffff74ffc 0xfffffffffffe7fe7 0x7fffffffffffcffc

def z594 : W := mkw 0x4662e9ed9f1a7b60 0x48cc5d3db3e34f6c 0xffe3f9ff9f1e7fe7 0x7ffc7f3ff3e3cffc

def z595 : W := mkw 0x4602a96980020220 0x08c0552d30004044 0x7e03f9f9821e0e65 0x6fc07f3f3043c1cc

def z596 : W := mkw 0x0020000009000000 0x0004000001200000 0x95e000001d000000 0x72bc000003a00000

def z597 : W := mkw 0x11b1040009810001 0x2236208001302000 0x01e0000000000000 0x003c000000000000

def z598 : W := mkw 0x162001201ba06d82 0x02c4002403740db0 0x3e0001f81fe07f86 0x67c0003f03fc0ff0

def z599 : W := mkw 0x0000012000004800 0x0000002400000900 0x280001f800007e04 0x0500003f00000fc0

def z600 : W := mkw 0xf77489fffba06d82 0x9eee913fff740db0 0xbffc01ffffe07f86 0x77ff803ffffc0ff0

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x7800000180100061 0x4f0000003002000c

def z602 : W := mkw 0x460efb7bb61a5a60 0x48c1df6f76c34b4c 0xfe1ffffffe1e7e65 0x7fc3ffffffc3cfcc

def z603 : W := mkw 0x28e5ccdfed3337f8 0x051cb99bfda666ff 0xfde3c7fffd11ffff 0xffbc78ffffa23fff

def z604 : W := mkw 0x079f3e1aa0000000 0x20f3e7c354000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z605 : W := mkw 0x173400121ba00480 0x02e6800243740090 0xbffc003e1fe00f86 0x77ff8007c3fc01f0

def z606 : W := mkw 0x4602e969841a1260 0x48c05d2d3083424c 0x6603f9f9801e0061 0x6cc07f3f3003c00c

def z607 : W := mkw 0x17bf76123ffd8489 0x22f7eec247ffb091 0xd7fffe067fff819a 0xfaffffc0cffff033

def z608 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x4203f839821e0e65 0x08407f073043c1cc

def z609 : W := mkw 0x00081a08a0468228 0x000103411408d045 0x00003800000e0000 0x000007000001c000

def z610 : W := mkw 0x000c5a1ab67edee8 0x40018b4356cfdbdd 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z611 : W := mkw 0x17bb7e08bfdf8229 0x22f76fc117fbf045 0xd7fffe01ffff8079 0xfaffffc03ffff00f

def z612 : W := mkw 0x608fbe5be06686a8 0xac11f7cb7c0cd0d5 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z613 : W := mkw 0x460e3b3ab26ecea8 0x48c1c767564dd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z614 : W := mkw 0x20e184c549002100 0x041c3098a9200420 0xfde3c7c7fd007182 0x7fbc78f8ffa00e30

def z615 : W := mkw 0x173000001ba06d82 0x02e6000003740db0 0x9ffc00001fe07f86 0x73ff800003fc0ff0

def z616 : W := mkw 0x0040008400000000 0x0008001080000000 0xa5e001c600000000 0x74bc0038c0000000

def z617 : W := mkw 0x0000000000025a60 0x4000000000004b4c 0x0800000000007e65 0x0100000000000fcc

def z618 : W := mkw 0x0600c16116105840 0x00c0182c22c20b08 0x7e03c1f99e107e65 0x6fc0783f33c20fcc

def z619 : W := mkw 0xe04c9bffe0000000 0x9c09937ffc000000 0xe21c3fffe0000000 0x5c4387fffc000000

def z620 : W := mkw 0xa044009660000000 0x94088012cc000000 0x0000000660000000 0x00000000cc000000

def z621 : W := mkw 0x0000080880020220 0x0000010110004044 0xfa003e3fe31f8fff 0xdf4007c7fc63f1ff

def z622 : W := mkw 0x060a7200165c8000 0x00c14e4002cb9000 0xd61ffe001fff8000 0x7ac3ffc003fff000

def z623 : W := mkw 0x00081a08a06686a8 0x00010341140cd0d5 0x58003e01e3ff8fff 0x8b0007c03c7ff1ff

def z624 : W := mkw 0x179b760016dd8001 0x22f36ec002dbb000 0x421ffe0002ff8000 0x0843ffc0005ff000

def z625 : W := mkw 0x00040012006686a8 0x00008002400cd0d5 0xba1c003e03ff8fff 0xd7438007c07ff1ff

def z626 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xba1c383e03ee0f86 0x57438707c07dc1f0

def z627 : W := mkw 0x171e3a1ab2ee86a9 0x22e3c743565dd0d5 0x021c383802ee0e04 0x00438707005dc1c0

def z628 : W := mkw 0x977441b61ffded83 0x12ee8836c3ffbdb0 0xbffc01fe1fffff86 0x77ff803fc3fffff0

def z629 : W := mkw 0x11b956000dd58001 0x22372ac001bab000 0xd5ffc6001df18000 0x7abff8c003be3000

def z630 : W := mkw 0x97ff77b61fdd8001 0x32ffeef6c3fbb000 0xf7fffffe1fff8000 0x7effffffc3fff000

def z631 : W := mkw 0x28a1c4414d111050 0x0514388829a2220a 0xd5e3c601fd118079 0xfabc78c03fa2300f

def z632 : W := mkw 0x977401b61b800000 0x12ee8036c3700000 0xb7fc01fe1fe00000 0x76ff803fc3fc0000

def z633 : W := mkw 0x0604013212204c80 0x00c0802642440990 0xbe1c01fe1fe07f86 0x77c3803fc3fc0ff0

def z634 : W := mkw 0x571afb6996deda61 0x6ae35f6d32dbdb4c 0x7e1ff9f99efe7e65 0x6fc3ff3f33dfcfcc

def z635 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x421c3e39e2ff8e7d 0x884387c73c5ff1cf

def z636 : W := mkw 0x875c1bbea06686a8 0x10eb8377d40cd0d5 0xfffc3fffe3ff8fff 0xffff87fffc7ff1ff

def z637 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x2de3c1c7fc0071fb 0xa5bc7838ff800e3f

def z638 : W := mkw 0x608bfe49e45d8001 0xac117fc93c8bb000 0x4003fe01e01f8000 0x08007fc03c03f000

def z639 : W := mkw 0x3ffbf6c55fddb151 0x27ff7ed8abfbb62a 0xd7ffffc01ffff000 0x7afffff803fffe00

def z640 : W := mkw 0x171a320012cc8001 0x22e3464002599000 0xd21c3e0003ff8000 0x5a4387c0007ff000

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0xb800000601000182 0x57000000c0200030

def z642 : W := mkw 0xe7d3e5e556185840 0xfcfa7cbcaac30b08 0x05e3c1c01c007000 0x20bc783803800e00

def z643 : W := mkw 0x00004000041a1260 0x400008000083424c 0x00000000001e0061 0x000000000003c00c

def z644 : W := mkw 0x008b360000000000 0x201166c000000000 0x4003fe0000000000 0x08007fc000000000

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000601e0118079 0x880000c03c02300f

def z646 : W := mkw 0x460ebb7ba0000000 0x08c1d76f74000000 0xe61fffffe0000000 0x7cc3fffffc000000

def z647 : W := mkw 0xefffffffff1b7b70 0xfdffffffffe36f6e 0xffffffffff1fffff 0xffffffffffe3ffff

def z648 : W := mkw 0x17b144001f910000 0x02f6288003f22000 0xd7ffc6001ff18000 0x7afff8c003fe3000

def z649 : W := mkw 0x0004001200200480 0x0000800240040090 0x801c000601e00182 0x10038000c03c0030

def z650 : W := mkw 0x173000001b800000 0x02e6000003700000 0x05e000001c000000 0x20bc000003800000

def z651 : W := mkw 0x000c121220648488 0x00018242440c9091 0x001c000000e00000 0x00038000001c0000

def z652 : W := mkw 0x2081844140000000 0x0410308828000000 0x4003c601e0000000 0x080078c03c000000

def z653 : W := mkw 0x875401b612004800 0x10ea8036c2400900 0xbffc01fe1e007e04 0x77ff803fc3c00fc0

def z654 : W := mkw 0x06026808961a0220 0x00c04d0112c34044 0x7e03f8399e1e0e65 0x6fc07f0733c3c1cc

def z655 : W := mkw 0x00a144000d110000 0x0014288001a22000 0xfde3c607fd1181fb 0xffbc78c0ffa2303f

def z656 : W := mkw 0xe8e5cdffed113150 0x9d1cb9bffda2262a 0xfde3c7fffd11f1fb 0xffbc78ffffa23e3f

def z657 : W := mkw 0x0004081aa0000000 0x0000810354000000 0x2000003fe0000000 0x04000007fc000000

def z658 : W := mkw 0x5622e9699fba7fe2 0x4ac45d2d33f74ffc 0x7e03f9f99ffe7fe7 0x6fc07f3f33ffcffc

def z659 : W := mkw 0x17bb360009c58001 0x22f766c00138b000 0xc7fffe0001e18000 0x78ffffc0003c3000

def z660 : W := mkw 0x977401b61be6efaa 0x12ee8036c37cddf5 0xbffc01fe1fffffff 0xf7ff803fc3ffffff

def z661 : W := mkw 0xffffffffffddb151 0xbffffffffffbb62a 0xfffffffffffff1fb 0xfffffffffffffe3f

def z662 : W := mkw 0x977661b61fb86d82 0x12eecc36c3f70db0 0xfffff9fe1ffe7f86 0x7fffff3fc3ffcff0

def z663 : W := mkw 0x400c9b7ba066dee8 0x4801936f740cdbdd 0xfa1c3fffe3ffffff 0xdf4387fffc7fffff

def z664 : W := mkw 0x4000816100005840 0x4800102c20000b08 0x000001c000007000 0x0000003800000e00

def z665 : W := mkw 0x4602e16116185840 0x48c05c2c22c30b08 0x7c03c1c19c107061 0x6f80783833820e0c

def z666 : W := mkw 0x173a32001bcc8001 0x22e7464003799000 0x97fc38001fee0000 0x72ff870003fdc000

def z667 : W := mkw 0xe75ebbffe0000000 0xbcebd77ffc000000 0x221c39ffe0000000 0x0443873ffc000000

def z668 : W := mkw 0x06026000161a5a60 0x40c04c0002c34b4c 0x5e03f8001e1e7e65 0x6bc07f0003c3cfcc

def z669 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0x821c3e3e63ef8f9e 0x904387c7cc7df1f3

def z670 : W := mkw 0x071a320000000000 0x20e3464000000000 0x021c380000000000 0x0043870000000000

def z671 : W := mkw 0x0089160000458001 0x201122c00008b000 0x0000060000018000 0x000000c000003000

def z672 : W := mkw 0x0600012012004800 0x00c0002402400900 0x040001c01c007000 0x2080003803800e00

def z673 : W := mkw 0x6e83ed69d61b5a70 0x4dd07dad3ac36b4e 0x7e03fff9fe1ffe7d 0xefc07fff3fc3ffcf

def z674 : W := mkw 0x0000804100000000 0x0000100820000000 0x6403c1c180000000 0x6c80783830000000

def z675 : W := mkw 0x460afb69b65eda68 0x48c15f6d36cbdb4d 0x7e03fff9fe1ffe7d 0xefc07fff3fc3ffcf

def z676 : W := mkw 0xd77efbffbffeffea 0x5aefdf7ff7ffdffd 0xffffffffffffffff 0xffffffffffffffff

def z677 : W := mkw 0x006c1a9ea966a7a8 0x000d8353d52cd4f5 0xfffc3fffffffffff 0xffff87ffffffffff

def z678 : W := mkw 0x0000080880020220 0x0000010110004044 0x02003838020e0e04 0x004007070041c1c0

def z679 : W := mkw 0xbf7481f75ba07dd2 0x17ee903eeb740fba 0xbffc01ffffe07fff 0xf7ff803ffffc0fff

def z680 : W := mkw 0x0060c0c50d103140 0x000c1818a1a20628 0xfde3c1c79d1071e3 0x7fbc7838f3a20e3c

def z681 : W := mkw 0xd716e97b96ba5ee2 0x5ae2dd2f72d74bdc 0x7e1ff9f99efe7e65 0x6fc3ff3f33dfcfcc

def z682 : W := mkw 0x068b7600165d8001 0x20d16ec002cbb000 0x5603fe001e1f8000 0x6ac07fc003c3f000

def z683 : W := mkw 0x1020000009a02582 0x02040000013404b0 0x0000000001e00182 0x00000000003c0030

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x800006066101819a 0x900000c0cc203033

def z685 : W := mkw 0x00000808a0020228 0x0000010114004045 0x00000001e0000079 0x800000003c00000f

def z686 : W := mkw 0x28e9d6c54d55b150 0x051d3ad8a9aab62a 0xffffffc7fffff1fb 0xfffffff8fffffe3f

def z687 : W := mkw 0x0000400004100000 0x0000080000820000 0x5403c0001c100000 0x6a80780003820000

def z688 : W := mkw 0x00081200006686a8 0x00010240000cd0d5 0xda1c3e0003ff8fff 0xdb4387c0007ff1ff

def z689 : W := mkw 0x917c129629e4a58a 0x122f8252c53c94b1 0x81fc060661e1819a 0x903f80c0cc3c3033

def z690 : W := mkw 0x811c121220000000 0xb023824244000000 0x001c000000000000 0x0003800000000000

def z691 : W := mkw 0x00081a08a0468228 0x000103411408d045 0x7a003e39e21f8e7d 0xcf4007c73c43f1cf

def z692 : W := mkw 0xe7dfffffe41a1260 0xfcfbfffffc83424c 0xe7ffffffe01e0061 0x7cfffffffc03c00c

def z693 : W := mkw 0x4602e16116185840 0x48c05c2c22c30b08 0x5603f9c01e1e7000 0x6ac07f3803c3ce00

def z694 : W := mkw 0x11bd161229e58489 0x2237a2c2453cb091 0x81fc060661e1819a 0x903f80c0cc3c3033

def z695 : W := mkw 0x008f7e1aa47f86a9 0x2011efc3548ff0d5 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z696 : W := mkw 0x2881c44144111050 0x051038882882220a 0x7c03c7c1fc11f079 0xef8078f83f823e0f

def z697 : W := mkw 0x28ebf6c54d5db151 0x251d7ed8a9abb62a 0xfde3ffc7fd1ff1fb 0xffbc7ff8ffa3fe3f

def z698 : W := mkw 0x6e42e9edd61a7b70 0x4dc85d3dbac34f6e 0x7e03f9fffe1e7fff 0xefc07f3fffc3cfff

def z699 : W := mkw 0x460afb69965eda60 0x48c15f6d32cbdb4c 0xfe1ffff99ffffe65 0x7fc3ffff33ffffcc

def z700 : W := mkw 0x0000000000200480 0x0000000000040090 0x1800000003e00f86 0x03000000007c01f0

def z701 : W := mkw 0x9714013212a04c82 0x12e2802642540990 0x3e1c01f81ee07e04 0x67c3803f03dc0fc0

def z702 : W := mkw 0xa8e5c5f74d317dd2 0x151cb8bee9a62fba 0xfde3c7fffd11ffff 0xffbc78ffffa23fff

def z703 : W := mkw 0x971c1b3ab2e6ceaa 0x12e38367565cd9d5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z704 : W := mkw 0x460efb7bb67edee8 0x48c1df6f76cfdbdd 0x7e1ff9f99efe7e65 0x6fc3ff3f33dfcfcc

def z705 : W := mkw 0x806401b609206d82 0x100c8036c1240db0 0xbde001fe1d007f86 0x77bc003fc3a00ff0

def z706 : W := mkw 0x28e144844d113150 0x051c289089a2262a 0x99e006067d11f1fb 0x933c00c0cfa23e3f

def z707 : W := mkw 0x51b99f6989c7da61 0x6a3733ed3138fb4c 0xa9fc07f981e1fe65 0x153f80ff303c3fcc

def z708 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xfffffffffc007000 0x7fffffffff800e00

def z709 : W := mkw 0x0710000000000000 0x00e2000000000000 0x97fc000003e00000 0x72ff8000007c0000

def z710 : W := mkw 0x079b3600004c8001 0x20f366c000099000 0xc7fffe00000e0000 0x78ffffc00001c000

def z711 : W := mkw 0x182c5a1abff7fffa 0x03058b4357feffff 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z712 : W := mkw 0x479bb76100000000 0x28f376ec20000000 0xc7ffffc000000000 0x78fffff800000000

def z713 : W := mkw 0x182040001fdffb71 0x4304080003fbff6e 0x180000001fffffff 0x8300000003ffffff

def z714 : W := mkw 0xefdfbfffe0002110 0xbdfbf7fffc000422 0xe7ffffffe000019a 0xfcfffffffc000033

def z715 : W := mkw 0x879f373200000000 0x30f3e6e640000000 0xc7fffe3800000000 0x78ffffc700000000

def z716 : W := mkw 0x20c184c540001040 0x04183098a8000208 0xede3c7c7e0007061 0x7dbc78f8fc000e0c

def z717 : W := mkw 0xa7d585f740200480 0x14fab0bee8040090 0xffffc7ffe3f18fff 0xfffff8fffc7e31ff

def z718 : W := mkw 0x70abbe49fba06d82 0xae1577c93f740db0 0x5803fe01ffe07f86 0x0b007fc03ffc0ff0

def z719 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x2e03f9f99e0e7e65 0x25c07f3f33c1cfcc

def z720 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xbffc07fe7fe1ff9e 0xf7ff80ffcffc3ff3

def z721 : W := mkw 0xe7dfbfffe0448000 0xbcfbf7fffc089000 0xe7ffffffe01f8000 0x7cfffffffc03f000

def z722 : W := mkw 0x082c5a1aad77b7f8 0x01058b4355aef6ff 0x1a1c38381fffffff 0x8343870703ffffff

def z723 : W := mkw 0x6ee32dacdb0b6b30 0x4ddc65b59b616d66 0x83e03e3e630f8f9e 0x907c07c7cc61f1f3

def z724 : W := mkw 0x9f3441321fb17dd2 0x13e6882643f62fba 0x1a1c00381ff1ffff 0x8343800703fe3fff

def z725 : W := mkw 0xc79f3f3aa0000000 0xb8f3e7e754000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z726 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x000000001d01f19a 0x8000000003a03e33

def z727 : W := mkw 0x1024481a9fba7fe2 0x4204890353f74ffc 0xfa1c383f9ffe7fe7 0x5f438707f3ffcffc

def z728 : W := mkw 0x179b760016dc8001 0x22f36ec002db9000 0xd7fffe001efe0000 0x7affffc003dfc000

def z729 : W := mkw 0xe0c185e540000000 0x9c1830bca8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z730 : W := mkw 0xe7dfbfffe02206a0 0xbcfbf7fffc0440d4 0xffffffffe3fe0fe7 0x7ffffffffc7fc1fc

def z731 : W := mkw 0xd77621b61ba06d82 0xbaeec436c3740db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z732 : W := mkw 0x479fbf7ba0000000 0x28f3f7ef74000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z733 : W := mkw 0x079b360000448000 0x20f366c000089000 0xc7fffe0002ee0000 0x78ffffc0005dc000

def z734 : W := mkw 0x1793240012880001 0x22f2648002510000 0x05e3c00000000000 0x20bc780000000000

def z735 : W := mkw 0xc75ebbffa0000000 0x18ebd77ff4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z736 : W := mkw 0x2ffbf6c54d55b150 0x25ff7ed8a9aab62a 0xffffffc7fffff1fb 0xfffffff8fffffe3f

def z737 : W := mkw 0xe7d7a5f760000000 0xbcfaf4beec000000 0x05e3c1c660000000 0x20bc7838cc000000

def z738 : W := mkw 0x479bbe4980000000 0x28f377c930000000 0xc7fffe0180000000 0x78ffffc030000000

def z739 : W := mkw 0xa7d585f740000000 0x14fab0bee8000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z740 : W := mkw 0x875621b600000000 0x10eac436c0000000 0xe7fff9fe00000000 0x7cffff3fc0000000

def z741 : W := mkw 0x977621b61ba06d82 0x12eec436c3740db0 0xfffff9fe1fe07f86 0x7fffff3fc3fc0ff0

def z742 : W := mkw 0x079f3e1aa02206a8 0x20f3e7c3540440d5 0xeffffe3fe0000fff 0xfdffffc7fc0001ff

def z743 : W := mkw 0x5712e969969a5a61 0x6ae25d2d32d34b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z744 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xfffffe019fff8061 0x7fffffc033fff00c

def z745 : W := mkw 0x10a956001fdd8001 0x02152ac003fbb000 0xd7fffe001fff8000 0x7affffc003fff000

def z746 : W := mkw 0x0824481aad3337f8 0x0104890355a666ff 0x3800003ffd11ffff 0x87000007ffa23fff

def z747 : W := mkw 0x082c5a1aad113150 0x01058b4355a2262a 0xfa1c3e3ffd11f1fb 0xdf4387c7ffa23e3f

def z748 : W := mkw 0x102040001f995841 0x4204080003f32b08 0x000000001c007000 0x0000000003800e00

def z749 : W := mkw 0x2860c0c54d113150 0x050c1818a9a2262a 0x280001c7fc0071fb 0x85000038ff800e3f

def z750 : W := mkw 0x102040001fdda101 0x0204080003fbb420 0x180000001ffff182 0x0300000003fffe30

def z751 : W := mkw 0x87d725b600000000 0x30fae4b6c0000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z752 : W := mkw 0x102040001f990001 0x0204080003f32000 0x100000001fe00000 0x0200000003fc0000

def z753 : W := mkw 0x479b3e08a0000000 0xa8f367c114000000 0xc7fffe0000000000 0x78ffffc000000000

def z754 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x17fff8001fff8000 0x22ffff0003fff000

def z755 : W := mkw 0x173a72001fdc8001 0x22e74e4003fb9000 0xd7fff8001ffe0000 0x7affff0003ffc000

def z756 : W := mkw 0xe7d3adede0000000 0xbcfa75bdbc000000 0x05e3c1c1e0000000 0x20bc78383c000000

def z757 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x7e03f9fffe1e7fff 0xefc07f3fffc3cfff

def z758 : W := mkw 0x20c58cdfe0000000 0x0418b19bfc000000 0xe5e3c7ffe0000000 0x7cbc78fffc000000

def z759 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x000000001eee0000 0x0000000003ddc000

def z760 : W := mkw 0x079f361220648488 0x20f3e6c2440c9091 0xc7fffe0661e1819a 0xf8ffffc0cc3c3033

def z761 : W := mkw 0x20c184c540000000 0x04183098a8000000 0x45e3c7c1e0000000 0x28bc78f83c000000

def z762 : W := mkw 0x479bff69965eda60 0x68f37fed32cbdb4c 0xfffffff99ffffe65 0x7fffffff33ffffcc

def z763 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xfffc39fe1ffe7f86 0x7fff873fc3ffcff0

def z764 : W := mkw 0x102040001ffeffea 0x4204080003ffdffd 0x180000001fffffff 0x8300000003ffffff

def z765 : W := mkw 0xe7dfbffff26ecea8 0xfcfbf7fffe4dd9d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z766 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0xc5e3c7c000000000 0x78bc78f800000000

def z767 : W := mkw 0x079b360000448000 0x20f366c000089000 0xc7fffe00001f8000 0x78ffffc00003f000

def z768 : W := mkw 0x173e7a1abfff86a9 0x22e7cf4357fff0d5 0xfa1c3e3fffff8fff 0xdf4387c7fffff1ff

def z769 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe7ffffffe0118079 0xfcfffffffc02300f

def z770 : W := mkw 0x20cd9edfe06686a8 0x0419b3dbfc0cd0d5 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z771 : W := mkw 0x182040000db135d2 0x0304080001b626ba 0x180000001df1f1fb 0x8300000003be3e3f

def z772 : W := mkw 0x479b3f2880000000 0x28f367e510000000 0xc7fffe3800000000 0x78ffffc700000000

def z773 : W := mkw 0xcf3e7b3aad113150 0xb9e7cf6755a2262a 0x1a1c38381d11f1fb 0x8343870703a23e3f

def z774 : W := mkw 0x619bbe49e0000000 0xac3377c93c000000 0xc1fffe01e0000000 0x183fffc03c000000

def z775 : W := mkw 0xe7dfbfffe0648488 0xbcfbf7fffc0c9091 0xf7ffffffe3ff819a 0xfefffffffc7ff033

def z776 : W := mkw 0xa0c584d760000000 0x9418b09aec000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z777 : W := mkw 0xefdfbfffe0003150 0xbdfbf7fffc00062a 0xffffffffe111f1fb 0xfffffffffc223e3f

def z778 : W := mkw 0xd73e7b3abfdd8001 0xbae7cf6757fbb000 0x121c38381fff8000 0x0243870703fff000

def z779 : W := mkw 0x4602e969b61a5a68 0x48c05d2d36c34b4d 0x7e03f9f9fe1e7e7d 0xefc07f3f3fc3cfcf

def z780 : W := mkw 0x1fbb76001fddb151 0x23f76ec003fbb62a 0xd7fffe001ffff000 0x7affffc003fffe00

def z781 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x87fffffe60000000 0x30ffffffcc000000

def z782 : W := mkw 0x97ff37b61beced83 0x32ffe6f6c37d9db0 0xfffffffe1fee7f86 0x7fffffffc3fdcff0

def z783 : W := mkw 0x06026120161a5a60 0x40c04c2402c34b4c 0x7e03f9f81e1e7e65 0x6fc07f3f03c3cfcc

def z784 : W := mkw 0xe7dfbfffe066efaa 0xbcfbf7fffc0cddf5 0xffffffffe3ffffff 0xfffffffffc7fffff

def z785 : W := mkw 0xe04489ffe0225ee8 0xdc08913ffc044bdd 0x280001ffe0007fff 0x8500003ffc000fff

def z786 : W := mkw 0x6e02e969d61a5a70 0x4dc05d2d3ac34b4e 0x7e03f9f9fe1e7e7d 0xefc07f3f3fc3cfcf

def z787 : W := mkw 0x917401b609a06d82 0x122e8036c1340db0 0xbdfc01fe1de07f86 0x77bf803fc3bc0ff0

def z788 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0xf8000607ffff81fb 0xdf0000c0fffff03f

def z789 : W := mkw 0xe7dfb7f760000000 0xbcfbf6feec000000 0xa7ffc7fe60000000 0x74fff8ffcc000000

def z790 : W := mkw 0x20c584d740200480 0x0418b09ae8040090 0xffffc7ffe3e00f86 0x7ffff8fffc7c01f0

def z791 : W := mkw 0xe7d3a5e5406686a8 0xbcfa74bca80cd0d5 0x1de3c1c003ff8fff 0xa3bc7838007ff1ff

def z792 : W := mkw 0x102048089fdf8221 0x0204090113fbf044 0x7a0038399fff8e65 0x4f40070733fff1cc

def z793 : W := mkw 0x102852001fdd8001 0x02050a4003fbb000 0x901c06001fff8000 0x120380c003fff000

def z794 : W := mkw 0x562269289fdfca21 0x4ac44d2513fbf944 0x120038381fff8e04 0x0240070703fff1c0

def z795 : W := mkw 0x46026928961a4a20 0x48c04d2512c34944 0x7e03f9f81e1e7e04 0x6fc07f3f03c3cfc0

def z796 : W := mkw 0xafd585f740207dd2 0x15fab0bee8040fba 0xefffc7ffe0007fff 0xfdfff8fffc000fff

def z797 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x100000001d11f000 0x0200000003a23e00

def z798 : W := mkw 0x0600c96996125a60 0x00c0192d32c24b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z799 : W := mkw 0x079b360000000000 0x20f366c000000000 0x07fff80000000000 0x20ffff0000000000

def z800 : W := mkw 0x97781bacbbc6eb2a 0x12ef03759778dd65 0x45e03fc1fc1ff079 0xa8bc07f83f83fe0f

def z801 : W := mkw 0x97ff37b61be4ed82 0x32ffe6f6c37c9db0 0xfffffffe1fffff86 0x7fffffffc3fffff0

def z802 : W := mkw 0x008d1e1aa0000000 0x0011a3c354000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z803 : W := mkw 0x1199160000c48001 0x223322c000189000 0x81fc060000e00000 0x103f80c0001c0000

def z804 : W := mkw 0x60cbbecde0000000 0xac1977d9bc000000 0x45e3ffc1e0000000 0x28bc7ff83c000000

def z805 : W := mkw 0x906441b61ffded83 0x120c8836c3ffbdb0 0x380001fe1fffff86 0x0700003fc3fffff0

def z806 : W := mkw 0x07bb76000d558000 0x20f76ec001aab000 0xd7fffe001fff8000 0x7affffc003fff000

def z807 : W := mkw 0x102040001f910000 0x0204080003f22000 0x100000001ff18000 0x0200000003fe3000

def z808 : W := mkw 0x17b76c1abfbb06a9 0x22f6ed8357f760d5 0x2de3c03ffc000fff 0xa5bc7807ff8001ff

def z809 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xfffffe061fff8182 0x7fffffc0c3fff030

def z810 : W := mkw 0x3f5ab2c552ccb151 0x27eb5658aa59962a 0x2a1c39c7e2ee71fb 0x85438738fc5dce3f

def z811 : W := mkw 0xefdfbfffe0001050 0xbdfbf7fffc00020a 0xe7ffffffe0000079 0xfcfffffffc00000f

def z812 : W := mkw 0xe7dbb7e540000000 0xbcfb76fca8000000 0xe7ffffc7e0000000 0x7cfffff8fc000000

def z813 : W := mkw 0xf7dfbffff2aa4ea2 0xfefbf7fffe5549d4 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z814 : W := mkw 0x173260001f990001 0x22e64c0003f32000 0x000000001c000000 0x0000000003800000

def z815 : W := mkw 0x17bb36001bc48000 0x22f766c003789000 0xd7fffe001fff8000 0x7affffc003fff000

def z816 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xdffffe001fff81fb 0xfbffffc003fff03f

def z817 : W := mkw 0xe7dfbffff266cea8 0xbcfbf7fffe4cd9d5 0xffffffffffffffff 0xffffffffffffffff

def z818 : W := mkw 0x973e73321ffded83 0x32e7ce6643ffbdb0 0x1a1c38381fffff86 0x0343870703fffff0

def z819 : W := mkw 0x80cf77b6047ded83 0x3019eef6c08fbdb0 0x6803fffe001fff86 0x0d007fffc003fff0

def z820 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe1000182 0x7ffffffffc200030

def z821 : W := mkw 0xc756a9ff80227fe2 0x58ead53ff0044ffc 0xeffff9ff80007fe7 0x7dffff3ff0000ffc

def z822 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xc21c3e3fe3ff8fff 0x984387c7fc7ff1ff

def z823 : W := mkw 0x975401b612a04c82 0x12ea8036c2540990 0xbffc01fe1ee07e04 0x77ff803fc3dc0fc0

def z824 : W := mkw 0xefdfbfffe02237f8 0xbdfbf7fffc0446ff 0xefffffffe0007fff 0xfdfffffffc000fff

def z825 : W := mkw 0x173a72001fdd8001 0x22e74e4003fbb000 0xd21c3e001fff8000 0x5a4387c003fff000

def z826 : W := mkw 0xe7dbb7e540000000 0xbcfb76fca8000000 0x85ffc7c000000000 0x30bff8f800000000

def z827 : W := mkw 0xe1dbbecde0000000 0xbc3b77d9bc000000 0x41e3fe01e0000000 0x083c7fc03c000000

def z828 : W := mkw 0x102c5a1abfffdee9 0x42058b4357fffbdd 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z829 : W := mkw 0xa1dd5696761a5a60 0xf43baad2cec34b4c 0x99fc06067e1e7e65 0x133f80c0cfc3cfcc

def z830 : W := mkw 0x39fd169669e5a599 0x273fa2d2cd3cb4b3 0x81fc060661e1819a 0x903f80c0cc3c3033

def z831 : W := mkw 0xe7dfb7f740000000 0xbcfbf6fee8000000 0xe7fffffe00000000 0x7cffffffc0000000

def z832 : W := mkw 0xe7dfbfffe0468220 0xbcfbf7fffc08d044 0xffffffffe3ff8e65 0x7ffffffffc7ff1cc

def z833 : W := mkw 0xd71e3b3ab2e6ceaa 0xbae3c767565cd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z834 : W := mkw 0xe7dbbfede0000000 0xbcfb77fdbc000000 0xe5e3ffc7e0000000 0x7cbc7ff8fc000000

def z835 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xc5fffe001dff8000 0x38bfffc003bff000

def z836 : W := mkw 0x27dbb6c540448000 0x24fb76d8a8089000 0xffffffc7e3ff81fb 0xfffffff8fc7ff03f

def z837 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0xfe1ff9f99ffe7e65 0x7fc3ff3f33ffcfcc

def z838 : W := mkw 0x977401b63ba06d8a 0x12ee8036c7740db1 0xbffc01fe7fe07f9e 0xf7ff803fcffc0ff3

def z839 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x87fffe001fef8000 0x30ffffc003fdf000

def z840 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xc7fffe001eee0000 0x78ffffc003ddc000

def z841 : W := mkw 0x0060c0c50d103140 0x000c1818a1a20628 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z842 : W := mkw 0xe04489ffe0226faa 0x9c08913ffc044df5 0x280001ffe0007fff 0x8500003ffc000fff

def z843 : W := mkw 0xa7dd9fffe06686a8 0x14fbb3fffc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z844 : W := mkw 0x082040001f7ffff8 0x4104080003efffff 0x180000001fffffff 0x8300000003ffffff

def z845 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x87ffc1c000000000 0x70fff83800000000

def z846 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x1e03f9f81e1e7e65 0x23c07f3f03c3cfcc

def z847 : W := mkw 0xf7dfbffff2804802 0xbefbf7fffe500900 0xe7ffffffe0000000 0x7cfffffffc000000

def z848 : W := mkw 0xc7df3fbea0000000 0xb8fbe7f7d4000000 0xe7fffffe00000000 0x7cffffffc0000000

def z849 : W := mkw 0x4820c9698d137b70 0x4904192d31a26f6e 0x380001f99d11ffff 0x8700003f33a23fff

def z850 : W := mkw 0xe7dfbfffe0006902 0xbcfbf7fffc000d20 0xe7ffffffe0007000 0x7cfffffffc000e00

def z851 : W := mkw 0x28c184c540003150 0x05183098a800062a 0x05e3c1c000007000 0x20bc783800000e00

def z852 : W := mkw 0x4602a96992024a20 0x08c0552d32404944 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z853 : W := mkw 0x11bb76000ddd8001 0x22376ec001bbb000 0xd5fffe001dff8000 0x7abfffc003bff000

def z854 : W := mkw 0xe7dbbfedc0000000 0xbcfb77fdb8000000 0xe7fffff980000000 0x7cffffff30000000

def z855 : W := mkw 0x17b364001f990001 0x22f66c8003f32000 0xd7fff8001ffe0000 0x7affff0003ffc000

def z856 : W := mkw 0xb1fd169669e4a58a 0xb63fa2d2cd3c94b1 0x81fc060661e1819a 0x903f80c0cc3c3033

def z857 : W := mkw 0x66c3a5e540000000 0x0cd874bca8000000 0x05e3c1c000000000 0x20bc783800000000

def z858 : W := mkw 0x37dbb6c552cc8001 0x26fb76d8aa599000 0xe7ffffc7e2ee0000 0x7cfffff8fc5dc000

def z859 : W := mkw 0x20c18ccdc0020220 0x04183199b8004044 0xffe3ffffe21e0e65 0x7ffc7ffffc43c1cc

def z860 : W := mkw 0x0008120000448000 0x0001024000089000 0xc21c3e0002ee0000 0x584387c0005dc000

def z861 : W := mkw 0xc712e969961a5a60 0xf8e25d2d32c34b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z862 : W := mkw 0x57bb77201fddc801 0x6af76ee403fbb900 0xd7fffe001fff8000 0x7affffc003fff000

def z863 : W := mkw 0x875401b612204c80 0x10ea8036c2440990 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z864 : W := mkw 0xf064c9ffffdd8001 0x9e0c993ffffbb000 0x300001ffffff8000 0x0600003ffffff000

def z865 : W := mkw 0x102040001f990001 0x0204080003f32000 0x100000001d118000 0x0200000003a23000

def z866 : W := mkw 0xf7d3a5e552880001 0xbefa74bcaa510000 0x05e3c1c000000000 0x20bc783800000000

def z867 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xfde3c7c7e0100061 0x7fbc78f8fc02000c

def z868 : W := mkw 0xfff3e5e55f997952 0x5ffe7cbcabf32f2a 0x05e3c1c01c007000 0x20bc783803800e00

def z869 : W := mkw 0xe0c58dffe0000000 0x9c18b1bffc000000 0x25e3c1ffe0000000 0x24bc783ffc000000

def z870 : W := mkw 0xe7dfbfffe0021260 0xfcfbf7fffc00424c 0xe7ffffffe0000061 0x7cfffffffc00000c

def z871 : W := mkw 0x182040001fdda111 0x0304080003fbb422 0x100000001fff819a 0x8200000003fff033

def z872 : W := mkw 0xe7dfbfffe0648488 0xbcfbf7fffc0c9091 0xffffffffe1f181fb 0xfffffffffc3e303f

def z873 : W := mkw 0x082040000d3337f8 0x0104080001a666ff 0x180000001d11ffff 0x8300000003a23fff

def z874 : W := mkw 0x000cd253247494c8 0x00019a4a648e9299 0xfc1fc7c7fdf1f1fb 0xff83f8f8ffbe3e3f

def z875 : W := mkw 0x082048089f1b7b70 0x4104090113e36f6e 0xfa003e3fff1fffff 0xdf4007c7ffe3ffff

def z876 : W := mkw 0xa7dfb6d760000000 0xb4fbf6daec000000 0xe7ffffc7e0000000 0x7cfffff8fc000000

def z877 : W := mkw 0x079b372012004800 0x20f366e402400900 0xfffffff81e007e04 0x7fffffff03c00fc0

def z878 : W := mkw 0x082040000d113150 0x0104080001a2262a 0xd80006001d11f1fb 0xdb0000c003a23e3f

def z879 : W := mkw 0x4602e96996184800 0x08c05d2d32c30900 0x7e03f9f99e1e7e04 0x6fc07f3f33c3cfc0

def z880 : W := mkw 0x28a144004d113150 0x0514288009a2262a 0x180006007d11f1fb 0x830000c00fa23e3f

def z881 : W := mkw 0x284892c54044b150 0x05091258a808962a 0xfa1c3fc7e3fff1fb 0xdf4387f8fc7ffe3f

def z882 : W := mkw 0xd7bb77201fdd8001 0xbaf76ee403fbb000 0xd7fffe001fff8000 0x7affffc003fff000

def z883 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xe7fffffffc007000 0x7cffffffff800e00

def z884 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x65e3ffffe0000000 0x2cbc7ffffc000000

def z885 : W := mkw 0x917401b61ba06d82 0x122e8036c3740db0 0xb9fc01fe1fe07f86 0x173f803fc3fc0ff0

def z886 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0xe5ffffc7e0000000 0x7cbffff8fc000000

def z887 : W := mkw 0x1fbb76001fddb151 0x23f76ec003fbb62a 0xfffffe07fffff1fb 0xffffffc0fffffe3f

def z888 : W := mkw 0x182040001f913150 0x0304080003f2262a 0x180000001ff1f1fb 0x8300000003fe3e3f

def z889 : W := mkw 0x20c184c5406686a8 0x04183098a80cd0d5 0xfde3c7c7e3ff8fff 0xffbc78f8fc7ff1ff

def z890 : W := mkw 0xe7d7a5f740000000 0xbcfaf4bee8000000 0x07ffc1f800000000 0x20fff83f00000000

def z891 : W := mkw 0x4002e849841a1260 0x48005d093083424c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z892 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x000000001de18000 0x0000000003bc3000

def z893 : W := mkw 0x082040000d57b378 0x0104080001aaf66f 0x180000001d1ff1fb 0x8300000003a3fe3f

def z894 : W := mkw 0x87df369600000000 0x30fbe6d2c0000000 0xc7fffe0600000000 0x78ffffc0c0000000

def z895 : W := mkw 0x06026928961a4a20 0x00c04d2512c34944 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z896 : W := mkw 0xe1dfbedfe06686a8 0xbc3bf7dbfc0cd0d5 0xc1fffe07e1ff81fb 0x983fffc0fc3ff03f

def z897 : W := mkw 0x5020c9699fdfda61 0x4a04192d33fbfb4c 0x380001f99ffffe65 0x0700003f33ffffcc

def z898 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0xfe03fff99f1ffe65 0x7fc07fff33e3ffcc

def z899 : W := mkw 0x162260001fdd8001 0x02c44c0003fbb000 0x120038001fff8000 0x0240070003fff000

def z900 : W := mkw 0xe7d7adffe0000000 0xbcfaf5bffc000000 0x67e3f9ffe0000000 0x6cfc7f3ffc000000

def z901 : W := mkw 0xa1d184c540000000 0xb43a3098a8000000 0x05e3c1c000000000 0x20bc783800000000

def z902 : W := mkw 0x086040840d113150 0x010c081081a2262a 0x380001c61d11f1fb 0x87000038c3a23e3f

def z903 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe7ffffffe101819a 0xfcfffffffc203033

def z904 : W := mkw 0x17bb76001fdde903 0x22f76ec003fbbd20 0xd7fffe001ffff000 0x7affffc003fffe00

def z905 : W := mkw 0xe7d7a5f740206d82 0xbcfaf4bee8040db0 0x2de3c1fe00007f86 0x25bc783fc0000ff0

def z906 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xede3c7c7e00001fb 0xfdbc78f8fc00003f

def z907 : W := mkw 0x082040000d133370 0x0104080001a2666e 0x180000001f1fffff 0x8300000003e3ffff

def z908 : W := mkw 0xe7d7adffe0000000 0xbcfaf5bffc000000 0x05e3c1f800000000 0x20bc783f00000000

def z909 : W := mkw 0xefd3a5e540003150 0xbdfa74bca800062a 0x05e3c1c000007000 0x20bc783800000e00

def z910 : W := mkw 0x182440121fb17dd2 0x0304880243f62fba 0xfa1c063ffff1ffff 0xdf4380c7fffe3fff

def z911 : W := mkw 0x079b360000000000 0x20f366c000000000 0xe7fffe07e0000000 0x7cffffc0fc000000

def z912 : W := mkw 0x17bb360009c58001 0x22f766c00138b000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z913 : W := mkw 0x102040001f990001 0x0204080003f32000 0x100000001e1e0000 0x0200000003c3c000

def z914 : W := mkw 0x082040000d317dd2 0x0104080001a62fba 0x180000001d11ffff 0x8300000003a23fff

def z915 : W := mkw 0x87df3fbea06686a8 0x30fbe7f7d40cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z916 : W := mkw 0x4002e969841a5a60 0x48005d2d30834b4c 0x7c03f9f99c1e7e65 0x6f807f3f3383cfcc

def z917 : W := mkw 0x66c3adedd20a4a20 0x4cd875bdba414944 0xe7e3ffffe20e0e04 0x7cfc7ffffc41c1c0

def z918 : W := mkw 0x079b3e08a0468228 0x20f367c11408d045 0xc7fffe01e01f8079 0xf8ffffc03c03f00f

def z919 : W := mkw 0xa7d3248440000000 0xb4fa649088000000 0x05e3c00000000000 0x20bc780000000000

def z920 : W := mkw 0x113852001fdd8001 0x22270a4003fbb000 0x101c00001fff8000 0x0203800003fff000

def z921 : W := mkw 0x66cfbfffe0000000 0x0cd9f7fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z922 : W := mkw 0xf7dfbfffe0a00482 0xbefbf7fffc140090 0xe7ffffffe0e00000 0x7cfffffffc1c0000

def z923 : W := mkw 0x102040001f9b5a61 0x4204080003f36b4c 0x180000001e1e7e65 0x0300000003c3cfcc

def z924 : W := mkw 0xe864c9ffed113150 0x9d0c993ffda2262a 0x380001fffd11f1fb 0x8700003fffa23e3f

def z925 : W := mkw 0xe7d3adedc0000000 0xbcfa75bdb8000000 0x45e3f9c180000000 0x28bc7f3830000000

def z926 : W := mkw 0x2860c0c54d113150 0x050c1818a9a2262a 0xf80007c7fd11f1fb 0xdf0000f8ffa23e3f

def z927 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xa7fff9fe00000000 0x74ffff3fc0000000

def z928 : W := mkw 0x102040001f987942 0x4204080003f30f28 0x000000001c007000 0x0000000003800e00

def z929 : W := mkw 0xe7dfbffff2025a60 0xfcfbf7fffe404b4c 0xfffffffffe007e65 0x7fffffffffc00fcc

def z930 : W := mkw 0x0089160000000000 0x001122c000000000 0xc7fffe0000000000 0x78ffffc000000000

def z931 : W := mkw 0xe756a9ffe0000000 0x9cead53ffc000000 0xe7fff9ffe0000000 0x7cffff3ffc000000

def z932 : W := mkw 0x20cd96d760000000 0x0419b2daec000000 0xe5ffc7c7e0000000 0x7cbff8f8fc000000

def z933 : W := mkw 0x66c3adedc0020220 0x0cd875bdb8004044 0xffe3ffffe31f8fff 0xfffc7ffffc63f1ff

def z934 : W := mkw 0xf7dfbffff2cc8001 0xbefbf7fffe599000 0xf7ffffffe3ff8000 0x7efffffffc7ff000

def z935 : W := mkw 0x4002e969961a5a60 0x48005d2d32c34b4c 0x7803f9f99e1e7e65 0x0f007f3f33c3cfcc

def z936 : W := mkw 0x20c1c4c544101040 0x04183898a8820208 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z937 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x65e3c1c180000000 0x6cbc783830000000

def z938 : W := mkw 0x27db368440000000 0x24fb66d088000000 0xc7fffe0660000000 0x78ffffc0cc000000

def z939 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xa7fc01fe1ee07e04 0x74ff803fc3dc0fc0

def z940 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xf7ffffffe3e00000 0x7efffffffc7c0000

def z941 : W := mkw 0x684489ffe0227ff8 0x4d08913ffc044fff 0x280001ffe0007fff 0x8500003ffc000fff

def z942 : W := mkw 0x179b360012cc8001 0x22f366c002599000 0x07fff80002ee0000 0x20ffff00005dc000

def z943 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x97fc01f81fe07e04 0x72ff803f03fc0fc0

def z944 : W := mkw 0x102c52123ffd8489 0x02058a4247ffb091 0x901c06067fff819a 0x920380c0cffff033

def z945 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x921c00001fff8000 0x5243800003fff000

def z946 : W := mkw 0x60c18dedc0025a60 0x4c1831bdb8004b4c 0xede3c7ffe0007e65 0x7dbc78fffc000fcc

def z947 : W := mkw 0x17bb36001bcc8001 0x22f766c003799000 0xd7fffe001fee0000 0x7affffc003fdc000

def z948 : W := mkw 0xe7dfbfffe0020228 0xbcfbf7fffc004045 0xe7ffffffe0000079 0xfcfffffffc00000f

def z949 : W := mkw 0xe7dfbffff2084800 0xfcfbf7fffe410900 0xe7ffffffe0000000 0x7cfffffffc000000

def z950 : W := mkw 0x102c5a1abfff86a9 0x02058b4357fff0d5 0x121c38381fff8e04 0x0243870703fff1c0

def z951 : W := mkw 0x008b360000448000 0x201166c000089000 0x4003fe00001f8000 0x08007fc00003f000

def z952 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x000000001c11f079 0x8000000003823e0f

def z953 : W := mkw 0xc75ebbffa0000000 0xb8ebd77ff4000000 0xe7fff9ff80000000 0x7cffff3ff0000000

def z954 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0x6de3c7c7fc11f1fb 0xadbc78f8ff823e3f

def z955 : W := mkw 0xb1fd169669e5a583 0xb63fa2d2cd3cb4b0 0x81fc060661e18182 0x103f80c0cc3c3030

def z956 : W := mkw 0x082c5a1abf7ffff8 0x41058b4357efffff 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z957 : W := mkw 0x688bfe49e45f9278 0x4d117fc93c8bf24f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z958 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x27fff9ffe0000000 0x24ffff3ffc000000

def z959 : W := mkw 0x0820c0410d113150 0x0104180821a2262a 0x380001c19d11f1fb 0x8700003833a23e3f

def z960 : W := mkw 0xe7d7adffc0000000 0x1cfaf5bff8000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z961 : W := mkw 0xe7dfbfffe0225ee8 0xfcfbf7fffc044bdd 0xefffffffe0007fff 0xfdfffffffc000fff

def z962 : W := mkw 0x971e3b3ab2eeceab 0x32e3c767565dd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z963 : W := mkw 0x002040000d558000 0x0004080001aab000 0x100000001fff8000 0x0200000003fff000

def z964 : W := mkw 0x082040000d75b5d8 0x0104080001aeb6bb 0x180000001df1f1fb 0x8300000003be3e3f

def z965 : W := mkw 0x002040000d110000 0x0004080001a22000 0xd00006001d118000 0x5a0000c003a23000

def z966 : W := mkw 0x17bb77201fddc801 0x22f76ee403fbb900 0xd7fffe381fff8e04 0x7affffc703fff1c0

def z967 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xfffc01ff9ff07fe7 0x7fff803ff3fe0ffc

def z968 : W := mkw 0x204488dfe02206a8 0x0408911bfc0440d5 0x280001ffe0000fff 0x8500003ffc0001ff

def z969 : W := mkw 0xd176e8df8dba37e2 0x5a2edd1bf1b746fc 0xc1fff80781fe01e3 0x183fff00f03fc03c

def z970 : W := mkw 0xe7dfb7f760000000 0xbcfbf6feec000000 0xc7ffffc660000000 0x78fffff8cc000000

def z971 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0xfde3c7c7e11181fb 0xffbc78f8fc22303f

def z972 : W := mkw 0x28cd9edfe066b7f8 0x0519b3dbfc0cd6ff 0xffffffffe3ffffff 0xfffffffffc7fffff

def z973 : W := mkw 0xa7dd97f760000000 0xb4fbb2feec000000 0xe7ffc7ffe0000000 0x7cfff8fffc000000

def z974 : W := mkw 0x079b360012080000 0x20f366c002410000 0xc7fffe00020e0000 0x78ffffc00041c000

def z975 : W := mkw 0x679bbf69e0000000 0xacf377ed3c000000 0xe7fffff9e0000000 0x7cffffff3c000000

def z976 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xffffffc01ffff000 0x7ffffff803fffe00

def z977 : W := mkw 0xf7dfbffff2ee86a9 0xbefbf7fffe5dd0d5 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z978 : W := mkw 0x66c3a5e540000000 0x0cd874bca8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z979 : W := mkw 0x082040000d3135d0 0x0104080001a626ba 0x180000001ff1ffff 0x8300000003fe3fff

def z980 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xa5e3c1c600000000 0x74bc7838c0000000

def z981 : W := mkw 0xe7dfbfffe0004800 0xbcfbf7fffc000900 0xefffffffe0007e04 0x7dfffffffc000fc0

def z982 : W := mkw 0x17bb77201fdd8001 0x22f76ee403fbb000 0xf7fffff81fff8000 0x7effffff03fff000

def z983 : W := mkw 0x3860c0c55fddb151 0x070c1818abfbb62a 0x380001c7fffff1fb 0x87000038fffffe3f

def z984 : W := mkw 0xf7dfbffff2a04c82 0xbefbf7fffe540990 0xfffffffffee07e04 0x7fffffffffdc0fc0

def z985 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xffe3ffc7ff1ff1fb 0xfffc7ff8ffe3fe3f

def z986 : W := mkw 0xe1dd9fffe0000000 0xbc3bb3fffc000000 0xe5ffc7ffe0000000 0x7cbff8fffc000000

def z987 : W := mkw 0x20c996c560000000 0xa41932d8ac000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z988 : W := mkw 0x977001a41b806902 0x12ee003483700d20 0xbffc01f81fe07e04 0x77ff803f03fc0fc0

def z989 : W := mkw 0x28eddedfed77b7f8 0x051dbbdbfdaef6ff 0x07fff9f81eee7e04 0x20ffff3f03ddcfc0

def z990 : W := mkw 0xc04489ffa0227fea 0x5808913ff4044ffd 0x280001ffe0007fff 0x8500003ffc000fff

def z991 : W := mkw 0x102852001fdd8001 0x02050a4003fbb000 0x50003e001fff8000 0x0a0007c003fff000

def z992 : W := mkw 0xe7dfbfffe0468228 0xbcfbf7fffc08d045 0xffffffffe21f8e7d 0xfffffffffc43f1cf

def z993 : W := mkw 0x082040001f197950 0x4104080003e32f2a 0x180000001d11f1fb 0x8300000003a23e3f

def z994 : W := mkw 0x27d3a4c540000000 0x24fa7498a8000000 0x05e3c1c000000000 0x20bc783800000000

def z995 : W := mkw 0xe7dfbfffe04c8001 0xbcfbf7fffc099000 0xe7ffffffe00e0000 0x7cfffffffc01c000

def z996 : W := mkw 0xe7dbbfede0000000 0xbcfb77fdbc000000 0xc7ffffc1e0000000 0x78fffff83c000000

def z997 : W := mkw 0x20cbb6c540000000 0x241976d8a8000000 0xe5e3ffc7e0000000 0x7cbc7ff8fc000000

def z998 : W := mkw 0x408bfe49a45f9269 0x68117fc9348bf24d 0x4003fe01e01f8079 0x88007fc03c03f00f

def z999 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x3ffc01f81ee07e04 0x67ff803f03dc0fc0

def z1000 : W := mkw 0x4712e969961a5a60 0x48e25d2d32c34b4c 0xfffff9f99e1e7e65 0x7fffff3f33c3cfcc

def z1001 : W := mkw 0x460ef373367cdcc8 0x48c1de6e66cf9b99 0x841fc7c67de1f19a 0xb083f8f8cfbc3e33

def z1002 : W := mkw 0x27d184c540000000 0x04fa3098a8000000 0xe7ffc7c7e0000000 0x7cfff8f8fc000000

def z1003 : W := mkw 0xd77621b61ba86d82 0x5aeec436c3750db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1004 : W := mkw 0x17bb76003fdd8009 0x22f76ec007fbb001 0xd7fffe007fff8018 0xfaffffc00ffff003

def z1005 : W := mkw 0x0602200000000000 0x00c0440000000000 0x5603f800021e0000 0x6ac07f000043c000

def z1006 : W := mkw 0x28c184c540001050 0x05183098a800020a 0xe5e3c7c7e0000079 0xfcbc78f8fc00000f

def z1007 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x6603f9f99e0e7e04 0x6cc07f3f33c1cfc0

def z1008 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xf7ffffffe1118000 0x7efffffffc223000

def z1009 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x520038001fff8000 0x4a40070003fff000

def z1010 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xfde3c7c7e1000182 0x7fbc78f8fc200030

def z1011 : W := mkw 0x002040000d112100 0x0004080001a22420 0x180000001d11f182 0x0300000003a23e30

def z1012 : W := mkw 0x082040001f197950 0x4104080003e32f2a 0x000000001c007000 0x0000000003800e00

def z1013 : W := mkw 0x60c3a4c540000000 0xac187498a8000000 0x05e3c1c000000000 0x20bc783800000000

def z1014 : W := mkw 0x102c5a1abffeffea 0x42058b4357ffdffd 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z1015 : W := mkw 0x17b956001fd58000 0x02f72ac003fab000 0xd7fffe001fff8000 0x7affffc003fff000

def z1016 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x3c0001c01d11f1fb 0xe780003803a23e3f

def z1017 : W := mkw 0x10a956001fdd8001 0x22152ac003fbb000 0x100006001fff8000 0x020000c003fff000

def z1018 : W := mkw 0xe04489ffe02206a8 0x9c08913ffc0440d5 0x200001ffe0000e04 0x0400003ffc0001c0

def z1019 : W := mkw 0x079b3600006686a8 0x20f366c0000cd0d5 0xdffffe0003ff8fff 0xfbffffc0007ff1ff

def z1020 : W := mkw 0x177001a41b806900 0x02ee003483700d20 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1021 : W := mkw 0xe84489ffc0227ff2 0x5d08913ff8044ffe 0x280001ffe0007fff 0x8500003ffc000fff

def z1022 : W := mkw 0xe7dfbfffe0448000 0xbcfbf7fffc089000 0xffffffffe3ff81fb 0xfffffffffc7ff03f

def z1023 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x38000007fd11f1fb 0x87000000ffa23e3f

def z1024 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x1ffc01f81fe07f86 0x23ff803f03fc0ff0

def z1025 : W := mkw 0x20cd96d760648488 0x0419b2daec0c9091 0xe5ffc7c7e1e1819a 0xfcbff8f8fc3c3033

def z1026 : W := mkw 0xe7dfbfffe02206a8 0xbcfbf7fffc0440d5 0xffffffffe21e0fff 0xfffffffffc43c1ff

def z1027 : W := mkw 0xe7d7a5f740000000 0xbcfaf4bee8000000 0x85ffc1c600000000 0x30bff838c0000000

def z1028 : W := mkw 0x579bbf6992ceca21 0x6af377ed3259d944 0xe7fffff982ee0e04 0x7cffffff305dc1c0

def z1029 : W := mkw 0x162041201fddc801 0x02c4082403fbb900 0x3e0001f81ffffe04 0x67c0003f03ffffc0

def z1030 : W := mkw 0xe1dfbedfe06686a8 0xbc3bf7dbfc0cd0d5 0xfbfffe3fe3ff8fff 0xdf7fffc7fc7ff1ff

def z1031 : W := mkw 0xa7dd9fffe0000000 0x14fbb3fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1032 : W := mkw 0x173e7a1abfff86a9 0x22e7cf4357fff0d5 0x1a1c38381fff8fff 0x8343870703fff1ff

def z1033 : W := mkw 0x60c18dedc0000000 0x0c1831bdb8000000 0xe5e3c7ffe0000000 0x7cbc78fffc000000

def z1034 : W := mkw 0xefdfbfffe0010010 0xbdfbf7fffc002002 0xe7ffffffe0018018 0xfcfffffffc003003

def z1035 : W := mkw 0xe7dfbfffe0468228 0xbcfbf7fffc08d045 0xe7ffffffe00e0000 0x7cfffffffc01c000

def z1036 : W := mkw 0x973401321ba04c82 0x12e6802643740990 0xbffc01f81fe07e04 0x77ff803f03fc0fc0

def z1037 : W := mkw 0x079b372000000000 0x20f366e400000000 0xe7fffff800000000 0x7cffffff00000000

def z1038 : W := mkw 0xe7d3a5e540005840 0xfcfa74bca8000b08 0x05e3c1c000007000 0x20bc783800000e00

def z1039 : W := mkw 0xe7dfbfffe0200480 0xbcfbf7fffc040090 0xffffffffe3f18fff 0xfffffffffc7e31ff

def z1040 : W := mkw 0xe7dfbfffe0227fe2 0xfcfbf7fffc044ffc 0xefffffffe0007fe7 0x7dfffffffc000ffc

def z1041 : W := mkw 0x179f3e1ab2ee86a9 0x22f3e7c3565dd0d5 0xe7fffe3fe2ee0e04 0x7cffffc7fc5dc1c0

def z1042 : W := mkw 0x17bb76001f980000 0x22f76ec003f30000 0xd7fffe001ffe0000 0x7affffc003ffc000

def z1043 : W := mkw 0xe7d7a5f740000000 0xbcfaf4bee8000000 0xe7ffc7ffe0000000 0x7cfff8fffc000000

def z1044 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x000000001c1f8000 0x000000000383f000

def z1045 : W := mkw 0x173001201ba06d82 0x02e6002403740db0 0xbffc01f81fe07f86 0x77ff803f03fc0ff0

def z1046 : W := mkw 0x4642a9ed80000000 0x08c8553db0000000 0xe7e3f9ff80000000 0x7cfc7f3ff0000000

def z1047 : W := mkw 0x079b360012000000 0x20f366c002400000 0xd7fffe001e000000 0x7affffc003c00000

def z1048 : W := mkw 0xc79b372000000000 0xb8f366e400000000 0xc7fffe0000000000 0x78ffffc000000000

def z1049 : W := mkw 0xe7dfbfffe0448000 0xbcfbf7fffc089000 0xe7ffffffe1e18000 0x7cfffffffc3c3000

def z1050 : W := mkw 0xa1d184c540000000 0xb43a3098a8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z1051 : W := mkw 0xe0cd9fffe06686a8 0x9c19b3fffc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1052 : W := mkw 0xe7dfbfffe02206a8 0xbcfbf7fffc0440d5 0xe7ffffffe0000e04 0x7cfffffffc0001c0

def z1053 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0x180000001fff81fb 0x8300000003fff03f

def z1054 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x2ffc01fe1ee07f86 0x25ff803fc3dc0ff0

def z1055 : W := mkw 0xe1dfb6d760000000 0xbc3bf6daec000000 0x81ffc60660000000 0x103ff8c0cc000000

def z1056 : W := mkw 0xe7d7adffe0000000 0xbcfaf5bffc000000 0xe5e3c7ffe0000000 0x7cbc78fffc000000

def z1057 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xffe3c7ffff11ffff 0xfffc78ffffe23fff

def z1058 : W := mkw 0x102040001fdf8221 0x0204080003fbf044 0x180000001fff8e65 0x0300000003fff1cc

def z1059 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xefffffffe2ee0fff 0xfdfffffffc5dc1ff

def z1060 : W := mkw 0x20c584d740000000 0x0418b09ae8000000 0xe7ffc7ffe0000000 0x7cfff8fffc000000

def z1061 : W := mkw 0x17bb76001fdd9041 0x22f76ec003fbb208 0xdffffe001ffff061 0x7bffffc003fffe0c

def z1062 : W := mkw 0x20c184c540000000 0x04183098a8000000 0x25e3c1c7e0000000 0x24bc7838fc000000

def z1063 : W := mkw 0x571e3b3ab2eecea9 0x6ae3c767565dd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z1064 : W := mkw 0xbf7401b65ba06d92 0x17ee8036cb740db2 0xbffc01fe7fe07f9e 0xf7ff803fcffc0ff3

def z1065 : W := mkw 0x286040844d113150 0x050c081089a2262a 0x180000067d11f1fb 0x83000000cfa23e3f

def z1066 : W := mkw 0x102040001fb86d82 0x0204080003f70db0 0x180000001ffe7f86 0x0300000003ffcff0

def z1067 : W := mkw 0x20c99ecde0468228 0x041933d9bc08d045 0xe5e3ffc7e01f8079 0xfcbc7ff8fc03f00f

def z1068 : W := mkw 0x00a54c1aad3306a8 0x0014a98355a660d5 0xfde3c63ffd118fff 0xffbc78c7ffa231ff

def z1069 : W := mkw 0x4793ad6980000000 0x28f275ad30000000 0x67e3f9f980000000 0x6cfc7f3f30000000

def z1070 : W := mkw 0xe7dfbfffe0200480 0xbcfbf7fffc040090 0xe7ffffffe1e00182 0x7cfffffffc3c0030

def z1071 : W := mkw 0x679fbe5be06686a8 0xacf3f7cb7c0cd0d5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1072 : W := mkw 0x60cfbedfe0000000 0xac19f7dbfc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1073 : W := mkw 0xbf95c57356b15cd2 0x17f2b8ae6ad62b9a 0x421fc639e2f18e7d 0x8843f8c73c5e31cf

def z1074 : W := mkw 0xa7df369660648488 0xb4fbe6d2cc0c9091 0xd7fffe0663ff819a 0xfaffffc0cc7ff033

def z1075 : W := mkw 0x102040001fb87dc2 0x4204080003f70fb8 0x180000001fe07f86 0x0300000003fc0ff0

def z1076 : W := mkw 0x0089160000448000 0x001122c000089000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z1077 : W := mkw 0x17bb36001bcd8001 0x22f766c00379b000 0xc7fffe0003ef8000 0x78ffffc0007df000

def z1078 : W := mkw 0xb7d585f752a04c82 0x16fab0beea540990 0xe7ffc7ffe2e00e04 0x7cfff8fffc5c01c0

def z1079 : W := mkw 0x1fbb76001fdda111 0x23f76ec003fbb422 0xd7fffe001fff819a 0xfaffffc003fff033

def z1080 : W := mkw 0x20c99ecde0000000 0x041933d9bc000000 0xe5e3ffc7e0000000 0x7cbc7ff8fc000000

def z1081 : W := mkw 0x17bb76001fddc801 0x22f76ec003fbb900 0xdffffe001ffffe04 0x7bffffc003ffffc0

def z1082 : W := mkw 0x079f361220000000 0x20f3e6c244000000 0xc7fffe0660000000 0x78ffffc0cc000000

def z1083 : W := mkw 0xe84489ffe02237f8 0x9d08913ffc0446ff 0x280001ffe0007fff 0x8500003ffc000fff

def z1084 : W := mkw 0x977621b61ba86d83 0x32eec436c3750db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1085 : W := mkw 0xe0cd9fffe0000000 0x9c19b3fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1086 : W := mkw 0x102040001f9a7b62 0x4204080003f34f6c 0x180000001e1e7e65 0x0300000003c3cfcc

def z1087 : W := mkw 0x60cbbecde0468228 0xac1977d9bc08d045 0xfde3ffc7e11f81fb 0xffbc7ff8fc23f03f

def z1088 : W := mkw 0x977621b61ba86d82 0x12eec436c3750db0 0xbffc39fe1fee7f86 0x77ff873fc3fdcff0

def z1089 : W := mkw 0x008b360000000000 0x201166c000000000 0xc5e3fe0000000000 0x78bc7fc000000000

def z1090 : W := mkw 0xe7d7a5f740200480 0xbcfaf4bee8040090 0xbfffc1fe03e00f86 0x77fff83fc07c01f0

def z1091 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0xfe03fffffe1e7e65 0x7fc07fffffc3cfcc

def z1092 : W := mkw 0xf7dfbffff2a04c82 0xbefbf7fffe540990 0xffffffffe3e00f86 0x7ffffffffc7c01f0

def z1093 : W := mkw 0x000c121200648480 0x00018242400c9090 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z1094 : W := mkw 0xe7dfbfffe0206d82 0xbcfbf7fffc040db0 0xffffffffe3e07f86 0x7ffffffffc7c0ff0

def z1095 : W := mkw 0x106400961ba06d82 0x020c8012c3740db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1096 : W := mkw 0x182040000dd5b151 0x0304080001bab62a 0x180000001df1f1fb 0x8300000003be3e3f

def z1097 : W := mkw 0x0602200012080000 0x00c0440002410000 0x4603f800020e0000 0x68c07f000041c000

def z1098 : W := mkw 0x573a7b289fdfda61 0x6ae74f6513fbfb4c 0x1a1c38381ffffe65 0x0343870703ffffcc

def z1099 : W := mkw 0xc7dfbfff80000000 0x38fbf7fff0000000 0xe7ffffff80000000 0x7cfffffff0000000

def z1100 : W := mkw 0x20e184c549002100 0x041c3098a9200420 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z1101 : W := mkw 0xe7dfbfffe0648480 0xbcfbf7fffc0c9090 0xffffffffe3ff8f86 0x7ffffffffc7ff1f0

def z1102 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x47fffe001eff8000 0x28ffffc003dff000

def z1103 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x4603f9f99e1e7e65 0x28c07f3f33c3cfcc

def z1104 : W := mkw 0x079f361200000000 0x20f3e6c240000000 0xe7fffe3e00000000 0x7cffffc7c0000000

def z1105 : W := mkw 0xefdfbfffe0207dd2 0xbdfbf7fffc040fba 0xefffffffe0007fff 0xfdfffffffc000fff

def z1106 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xa5ffc7ffe0000000 0x34bff8fffc000000

def z1107 : W := mkw 0x4000c96984125a60 0x4800192d30824b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z1108 : W := mkw 0x27dfbedfe06686a8 0x24fbf7dbfc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1109 : W := mkw 0x877401b609202580 0x10ee8036c12404b0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1110 : W := mkw 0x179b360000c48001 0x22f366c000189000 0xc7fffe0000e00000 0x78ffffc0001c0000

def z1111 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xefffffffe01f8fff 0xfdfffffffc03f1ff

def z1112 : W := mkw 0x082040000d55b150 0x0104080001aab62a 0x180000001ffff1fb 0x8300000003fffe3f

def z1113 : W := mkw 0x06ab76001f5d8000 0x00d56ec003ebb000 0xd7fffe001fff8000 0x7affffc003fff000

def z1114 : W := mkw 0x0e2041201f117950 0x01c4082403e22f2a 0x3e0001f81f11ffff 0xe7c0003f03e23fff

def z1115 : W := mkw 0x00681a8ca946a328 0x000d03519528d465 0xfde03fc7fd1ff1fb 0xffbc07f8ffa3fe3f

def z1116 : W := mkw 0xe7d7adffe0000000 0xbcfaf5bffc000000 0xa7ffc1ffe0000000 0x74fff83ffc000000

def z1117 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0x87fc01fe1fe07f86 0x30ff803fc3fc0ff0

def z1118 : W := mkw 0xe7dfb7f760648488 0xbcfbf6feec0c9091 0x85ffc7c661e1819a 0xb0bff8f8cc3c3033

def z1119 : W := mkw 0x4000c96984125a60 0x4800192d30824b4c 0x380001f99c107e65 0x0700003f33820fcc

def z1120 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xc7fffff800000000 0x78ffffff00000000

def z1121 : W := mkw 0x60c18ccde0000000 0x8c183199bc000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z1122 : W := mkw 0x002040000d5d8001 0x0004080001abb000 0x100000001d1f8000 0x0200000003a3f000

def z1123 : W := mkw 0x177400961ba02580 0x02ee8012c37404b0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1124 : W := mkw 0xe7dfbffff2204c80 0xbcfbf7fffe440990 0xffffffffffe07f86 0x7ffffffffffc0ff0

def z1125 : W := mkw 0x10285a08bfdf8229 0x02050b4117fbf045 0x50003e01ffff8079 0x8a0007c03ffff00f

def z1126 : W := mkw 0x0791040000000000 0x00f2208000000000 0xc7ffc60000000000 0x78fff8c000000000

def z1127 : W := mkw 0x279bb64140000000 0x24f376c828000000 0xc7fffe01e0000000 0x78ffffc03c000000

def z1128 : W := mkw 0xe79fbf7be0000000 0xbcf3f7ef7c000000 0xc7fffe39e0000000 0x78ffffc73c000000

def z1129 : W := mkw 0x0602e16116185840 0x00c05c2c22c30b08 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z1130 : W := mkw 0x886441b60d317dd2 0x110c8836c1a62fba 0x380001fe1d11ffff 0x8700003fc3a23fff

def z1131 : W := mkw 0x179f3e1ab2ee86a9 0x22f3e7c3565dd0d5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1132 : W := mkw 0x11bb76001fdd8001 0x22376ec003fbb000 0xd1fffe001fff8000 0x1a3fffc003fff000

def z1133 : W := mkw 0xa7db368440000000 0xb4fb66d088000000 0xc7fffe0000000000 0x78ffffc000000000

def z1134 : W := mkw 0x002040000d7786a8 0x0004080001aef0d5 0x180000001fff8fff 0x8300000003fff1ff

def z1135 : W := mkw 0x864661b616386d82 0x10c8cc36c2c70db0 0x7e03f9fe1e1e7f86 0x6fc07f3fc3c3cff0

def z1136 : W := mkw 0x688bfe49c45f9271 0x6d117fc9388bf24e 0x4003fe01e01f8079 0x88007fc03c03f00f

def z1137 : W := mkw 0x4e02e969961b5a70 0x49c05d2d32c36b4e 0x7e03f9f99e1ffe7d 0xefc07f3f33c3ffcf

def z1138 : W := mkw 0xe1dfbfffe0000000 0xbc3bf7fffc000000 0xe1ffffffe0000000 0x1c3ffffffc000000

def z1139 : W := mkw 0x688bfe49e4579278 0xad117fc93c8af24f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z1140 : W := mkw 0xf7d7a5f752a04c82 0xbefaf4beea540990 0x07ffc1f802e00e04 0x20fff83f005c01c0

def z1141 : W := mkw 0x102040001fb07dc2 0x0204080003f60fb8 0x180000001ff07fe7 0x0300000003fe0ffc

def z1142 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x47fffff9e0000000 0x28ffffff3c000000

def z1143 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xffffffffe2fe0e65 0x7ffffffffc5fc1cc

def z1144 : W := mkw 0xe7d7adffc0000000 0xbcfaf5bff8000000 0xe7fff9ff80000000 0x7cffff3ff0000000

def z1145 : W := mkw 0xe6c7adffe0000000 0x9cd8f5bffc000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z1146 : W := mkw 0x082040000d5db151 0x0104080001abb62a 0x180000001d1ff1fb 0x8300000003a3fe3f

def z1147 : W := mkw 0x102040001fdde903 0x0204080003fbbd20 0x100000001ffff000 0x0200000003fffe00

def z1148 : W := mkw 0x082040001f1b7b70 0x4104080003e36f6e 0x180000001e1e7e65 0x0300000003c3cfcc

def z1149 : W := mkw 0x173a72001fdd8001 0x22e74e4003fbb000 0x021c38001eee0000 0x0043870003ddc000

def z1150 : W := mkw 0x002040000d110000 0x0004080001a22000 0xf8000607fd1181fb 0xdf0000c0ffa2303f

def z1151 : W := mkw 0x20c58cdfe02206a8 0x0418b19bfc0440d5 0xede3c7ffe0000fff 0xfdbc78fffc0001ff

def z1152 : W := mkw 0xe7d3adedd20a4a20 0xfcfa75bdba414944 0x07e3f9f8020e0e04 0x20fc7f3f0041c1c0

def z1153 : W := mkw 0x1f3a72001fddb151 0x23e74e4003fbb62a 0x1a1c38001ffff1fb 0x8343870003fffe3f

def z1154 : W := mkw 0xf7dfbffff2800000 0xbefbf7fffe500000 0xe7ffffffe2e00000 0x7cfffffffc5c0000

def z1155 : W := mkw 0x102040001ffda583 0x0204080003ffb4b0 0x100000001fff8182 0x0200000003fff030

def z1156 : W := mkw 0x679bbe49e0000000 0xacf377c93c000000 0x45e3fe01e0000000 0x28bc7fc03c000000

def z1157 : W := mkw 0x00c1048400000000 0x0018209080000000 0xe5e3c7c600000000 0x7cbc78f8c0000000

def z1158 : W := mkw 0x3fbb76005fdd8011 0x27f76ec00bfbb002 0xd7fffe007fff8018 0xfaffffc00ffff003

def z1159 : W := mkw 0x102040001fddc801 0x0204080003fbb900 0x180000001ffffe04 0x0300000003ffffc0

def z1160 : W := mkw 0x162040001fdd8001 0x02c4080003fbb000 0x160000001fff8000 0x62c0000003fff000

def z1161 : W := mkw 0x87d505b600000000 0x10faa0b6c0000000 0xe7ffc7fe00000000 0x7cfff8ffc0000000

def z1162 : W := mkw 0xe7dfbfffe0020220 0xbcfbf7fffc004044 0xe7ffffffe20e0e04 0x7cfffffffc41c1c0

def z1163 : W := mkw 0x102040001ffd8481 0x0204080003ffb090 0x180000001fff8f86 0x0300000003fff1f0

def z1164 : W := mkw 0x28c184c540003150 0x05183098a800062a 0x2de3c1c7e00071fb 0xa5bc7838fc000e3f

def z1165 : W := mkw 0x182040001ffdfdd3 0x0304080003ffbfba 0x180000001fffffff 0x8300000003ffffff

def z1166 : W := mkw 0xc793252000000000 0xb8f264a400000000 0x05e3c00000000000 0x20bc780000000000

def z1167 : W := mkw 0x102c52121ffded83 0x02058a4243ffbdb0 0xfa1c3e3e1fffff86 0x5f4387c7c3fffff0

def z1168 : W := mkw 0x102040001fffffe3 0x4204080003fffffc 0x180000001fffffe7 0x0300000003fffffc

def z1169 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0xe3fffe3fe0000000 0x5c7fffc7fc000000

def z1170 : W := mkw 0x179b360012cc8001 0x22f366c002599000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z1171 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x180000001d007182 0x0300000003a00e30

def z1172 : W := mkw 0xe7dfbfffe0002100 0xbcfbf7fffc000420 0xefffffffe0007182 0x7dfffffffc000e30

def z1173 : W := mkw 0x5622a9699ba06d82 0x0ac4552d33740db0 0x7e03f9f99fe07f86 0x6fc07f3f33fc0ff0

def z1174 : W := mkw 0xe7dfbffff20a5a60 0xfcfbf7fffe414b4c 0xefffffffe20e7e65 0x7dfffffffc41cfcc

def z1175 : W := mkw 0xa7df37b660000000 0xb4fbe6f6cc000000 0xe7fffffe60000000 0x7cffffffcc000000

def z1176 : W := mkw 0x00a1c4410d111040 0x0014388821a22208 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z1177 : W := mkw 0xc79f3f3aa06686a8 0xb8f3e7e7540cd0d5 0xd7fffe3803ff8e04 0x7affffc7007ff1c0

def z1178 : W := mkw 0x97df37b612eccc83 0x32fbe6f6c25d9990 0xe7fffffe02ee0e04 0x7cffffffc05dc1c0

def z1179 : W := mkw 0xe7dfbfffe0025a60 0xfcfbf7fffc004b4c 0xffffffffe21e7e65 0x7ffffffffc43cfcc

def z1180 : W := mkw 0x0000c849961a5a60 0x4000190932c34b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z1181 : W := mkw 0xe7d3adedc0025a60 0xfcfa75bdb8004b4c 0x2de3c1f980007e65 0x25bc783f30000fcc

def z1182 : W := mkw 0x102852001fdd8001 0x02050a4003fbb000 0x121c38001fff8000 0x0243870003fff000

def z1183 : W := mkw 0x0081040000000000 0x0010208000000000 0xd5e3c60001118000 0x7abc78c000223000

def z1184 : W := mkw 0xc752a1e500000000 0x18ea543ca0000000 0x05e3c1c000000000 0x20bc783800000000

def z1185 : W := mkw 0x0602e849961a1260 0x00c05d0932c3424c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z1186 : W := mkw 0x479fbf7ba06686a8 0x28f3f7ef740cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1187 : W := mkw 0x6602e969f61a5a60 0xccc05d2d3ec34b4c 0x7e03f9f9fe1e7e65 0x6fc07f3f3fc3cfcc

def z1188 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x080000001c0071fb 0x8100000003800e3f

def z1189 : W := mkw 0xa9fd16966965a598 0xb53fa2d2cd2cb4b3 0x81fc060661e1819a 0x903f80c0cc3c3033

def z1190 : W := mkw 0x973441321ffdcc83 0x12e6882643ffb990 0x121c00381fff8e04 0x0243800703fff1c0

def z1191 : W := mkw 0x26c185e540000000 0x04d830bca8000000 0xe7e3c7ffe0000000 0x7cfc78fffc000000

def z1192 : W := mkw 0x20c18ccdc0000000 0x04183199b8000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z1193 : W := mkw 0x4e2269289f1b7b70 0x49c44d2513e36f6e 0x1a0038381f1fffff 0x8340070703e3ffff

def z1194 : W := mkw 0xe7dfbfffe0200488 0xbcfbf7fffc040091 0xe7ffffffe000019a 0xfcfffffffc000033

def z1195 : W := mkw 0xa1dd96d760000000 0xb43bb2daec000000 0xc1ffc607e0000000 0x183ff8c0fc000000

def z1196 : W := mkw 0x182040001fffb7f9 0x0304080003fff6ff 0x180000001fffffff 0x8300000003ffffff

def z1197 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x7e03fff9fe1ffe7d 0xefc07fff3fc3ffcf

def z1198 : W := mkw 0xefd3a5e540003150 0xbdfa74bca800062a 0x2de3c1c7e00071fb 0xa5bc7838fc000e3f

def z1199 : W := mkw 0x082040000d111050 0x0104080001a2220a 0x100000001d118079 0x8200000003a2300f

def z1200 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xe7ffffffe2ff8e7d 0xfcfffffffc5ff1cf

def z1201 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xf5e3c7c7e1118000 0x7ebc78f8fc223000

def z1202 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x58000601fd11f1fb 0x8b0000c03fa23e3f

def z1203 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xfffc07ffffe07f86 0x7fff80fffffc0ff0

def z1204 : W := mkw 0x102040001fffefab 0x0204080003fffdf5 0x180000001fffffff 0x8300000003ffffff

def z1205 : W := mkw 0x20c184c540000000 0x04183098a8000000 0x65e3c1c180000000 0x6cbc783830000000

def z1206 : W := mkw 0x079b3e08a0000000 0x20f367c114000000 0xc7fffe01e0000000 0x78ffffc03c000000

def z1207 : W := mkw 0xa84489ffe0227ffa 0x1508913ffc044fff 0x280001ffe0007fff 0x8500003ffc000fff

def z1208 : W := mkw 0xefdfbfffe066b7f8 0xbdfbf7fffc0cd6ff 0xffffffffe3ffffff 0xfffffffffc7fffff

def z1209 : W := mkw 0x17bb76001fddd841 0x62f76ec003fbbb08 0xd7fffe001ffff000 0x7affffc003fffe00

def z1210 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xbffc01ffffe07fff 0xf7ff803ffffc0fff

def z1211 : W := mkw 0xe7dfbfffe0226faa 0xbcfbf7fffc044df5 0xefffffffe0007fff 0xfdfffffffc000fff

def z1212 : W := mkw 0xe7dbb7e540448000 0xbcfb76fca8089000 0xd7ffffc003ff8000 0x7afffff8007ff000

def z1213 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x3e03f9f81e0e7e04 0x67c07f3f03c1cfc0

def z1214 : W := mkw 0x0081844100000000 0x0010308820000000 0xe5e3c7c180000000 0x7cbc78f830000000

def z1215 : W := mkw 0x1710000012800000 0x02e2000002500000 0x87fc000002e00000 0x70ff8000005c0000

def z1216 : W := mkw 0x17bb76000ddd8001 0x22f76ec001bbb000 0xc7fffe0001ff8000 0x78ffffc0003ff000

def z1217 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x980006067d11f1fb 0x930000c0cfa23e3f

def z1218 : W := mkw 0xd736693a9fba7fe2 0x5ae6cd2753f74ffc 0x1a1c38381ffe7fe7 0x0343870703ffcffc

def z1219 : W := mkw 0x079b3e0880000000 0x20f367c110000000 0xe7fffe3980000000 0x7cffffc730000000

def z1220 : W := mkw 0x079b360000458001 0x20f366c00008b000 0xc7fffe0000018000 0x78ffffc000003000

def z1221 : W := mkw 0xa7df3e9ee06686a8 0xb4fbe7d3dc0cd0d5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1222 : W := mkw 0x66c3adedc0000000 0x0cd875bdb8000000 0x67e3f9f980000000 0x6cfc7f3f30000000

def z1223 : W := mkw 0x079b7600045d8001 0x20f36ec0008bb000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z1224 : W := mkw 0x102040001f980000 0x0204080003f30000 0x100000001ffe0000 0x0200000003ffc000

def z1225 : W := mkw 0x60c3a4c540000000 0xac187498a8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z1226 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xe5e3c7c7e0118079 0xfcbc78f8fc02300f

def z1227 : W := mkw 0x002c5a1aad7786a8 0x00058b4355aef0d5 0xfa1c3e3fffff8fff 0xdf4387c7fffff1ff

def z1228 : W := mkw 0xf7dfbffff2eccc83 0xbefbf7fffe5d9990 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z1229 : W := mkw 0xe7d3adedc0020220 0xbcfa75bdb8004044 0x7fe3f9f9821e0e65 0x6ffc7f3f3043c1cc

def z1230 : W := mkw 0x00081a0880468220 0x000103411008d044 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z1231 : W := mkw 0x079f361200200480 0x20f3e6c240040090 0xfffffe3e03e00f86 0x7fffffc7c07c01f0

def z1232 : W := mkw 0x2820c0414d113150 0x0504180829a2262a 0x18000001fd11f1fb 0x830000003fa23e3f

def z1233 : W := mkw 0x67dbbecde0000000 0xacfb77d9bc000000 0xe7ffffc7e0000000 0x7cfffff8fc000000

def z1234 : W := mkw 0x102040001f9a5a60 0x4204080003f34b4c 0x180000001ffe7e65 0x0300000003ffcfcc

def z1235 : W := mkw 0xe7dfb7f760000000 0xbcfbf6feec000000 0x05ffc1c000000000 0x20bff83800000000

def z1236 : W := mkw 0xe7d3adedc0000000 0xbcfa75bdb8000000 0x07e3f9f800000000 0x20fc7f3f00000000

def z1237 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xc1e3c607e0000000 0x183c78c0fc000000

def z1238 : W := mkw 0xe7dfbfffe0020220 0xbcfbf7fffc004044 0xefffffffe0000e65 0x7dfffffffc0001cc

def z1239 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x85e3c7c660000000 0x30bc78f8cc000000

def z1240 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xc5e3c7c7fd11f1fb 0xb8bc78f8ffa23e3f

def z1241 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xbffc01fe1ff1ffff 0xf7ff803fc3fe3fff

def z1242 : W := mkw 0xe7d7adffe02206a8 0xbcfaf5bffc0440d5 0x2de3c1ffe0000fff 0xa5bc783ffc0001ff

def z1243 : W := mkw 0xa1dd169660000000 0xb43ba2d2cc000000 0xc5ffc60660000000 0x78bff8c0cc000000

def z1244 : W := mkw 0x20c1048440000000 0x0418209088000000 0xc5e3c60660000000 0x78bc78c0cc000000

def z1245 : W := mkw 0x102040001fdd9041 0x0204080003fbb208 0x180000001ffff061 0x0300000003fffe0c

def z1246 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xffffffffe3ee0f86 0x7ffffffffc7dc1f0

def z1247 : W := mkw 0x1024481abfff86a9 0x0204890357fff0d5 0x3800003fffff8fff 0x87000007fffff1ff

def z1248 : W := mkw 0xa7df369660000000 0xb4fbe6d2cc000000 0x85ffc60660000000 0x30bff8c0cc000000

def z1249 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x27e3c1f800000000 0x64fc783f00000000

def z1250 : W := mkw 0x182040001ff7fffa 0x0304080003feffff 0x180000001fffffff 0x8300000003ffffff

def z1251 : W := mkw 0x102040001fdfca21 0x4204080003fbf944 0x100000001fff8e04 0x0200000003fff1c0

def z1252 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xc5ffffc7e0000000 0x38bffff8fc000000

def z1253 : W := mkw 0x279b360060000000 0xa4f366c00c000000 0xc7fffe0060000000 0x78ffffc00c000000

def z1254 : W := mkw 0x002040000d110000 0x0004080001a22000 0x180000001d1181fb 0x8300000003a2303f

def z1255 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x180000001c107061 0x0300000003820e0c

def z1256 : W := mkw 0x67dbbfedc0000000 0x2cfb77fdb8000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1257 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x67fff9f980000000 0x6cffff3f30000000

def z1258 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x7e03f9f99f1fffff 0xefc07f3f33e3ffff

def z1259 : W := mkw 0xe7dfb7f760000000 0xbcfbf6feec000000 0xe5ffc7c7e0000000 0x7cbff8f8fc000000

def z1260 : W := mkw 0xf7dfbffff2e6ceaa 0xbefbf7fffe5cd9d5 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z1261 : W := mkw 0x082040001f193150 0x0104080003e3262a 0x180000001f1ff1fb 0x8300000003e3fe3f

def z1262 : W := mkw 0x0793240000000000 0x20f2648000000000 0xc5e3c60000000000 0x78bc78c000000000

def z1263 : W := mkw 0x875481f700000000 0x10ea903ee0000000 0xe7ffc1ff80000000 0x7cfff83ff0000000

def z1264 : W := mkw 0xe0c58dffe02206a8 0x9c18b1bffc0440d5 0xfde3c7ffe1118fff 0xffbc78fffc2231ff

def z1265 : W := mkw 0x079b7600165c8000 0x20f36ec002cb9000 0xd7fffe001fff8000 0x7affffc003fff000

def z1266 : W := mkw 0xe7dfbfffe0001040 0xbcfbf7fffc000208 0xefffffffe0007061 0x7dfffffffc000e0c

def z1267 : W := mkw 0xc79fbf7ba0000000 0xb8f3f7ef74000000 0xe7fffff980000000 0x7cffffff30000000

def z1268 : W := mkw 0xefdfbfffe0027b70 0xfdfbf7fffc004f6e 0xefffffffe0007fff 0xfdfffffffc000fff

def z1269 : W := mkw 0x002040000d110000 0x0004080001a22000 0x000000001c000000 0x0000000003800000

def z1270 : W := mkw 0xf7d3a5e552804802 0xbefa74bcaa500900 0x05e3c1c000000000 0x20bc783800000000

def z1271 : W := mkw 0x27dbb6c540000000 0x24fb76d8a8000000 0xc7ffffc000000000 0x78fffff800000000

def z1272 : W := mkw 0xe7d3a5e540006902 0xbcfa74bca8000d20 0x05e3c1c000007000 0x20bc783800000e00

def z1273 : W := mkw 0x002852000d558000 0x00050a4001aab000 0xd21c3e001fff8000 0x5a4387c003fff000

def z1274 : W := mkw 0x2864c8dfed77b7f8 0x050c991bfdaef6ff 0x380001ffffffffff 0x8700003fffffffff

def z1275 : W := mkw 0xe7dfbffff2000000 0xbcfbf7fffe400000 0xf7fffffffe000000 0x7effffffffc00000

def z1276 : W := mkw 0x000c1a1aa06686a8 0x00018343540cd0d5 0xfe1c3fffffffffff 0xffc387ffffffffff

def z1277 : W := mkw 0x26c185e552004800 0x04d830bcaa400900 0xffe3c7fffe007e04 0x7ffc78ffffc00fc0

def z1278 : W := mkw 0xe7dfbfffe0448008 0xbcfbf7fffc089001 0xe7ffffffe0018018 0xfcfffffffc003003

def z1279 : W := mkw 0xf7dfbffff2ee86a9 0xbefbf7fffe5dd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1280 : W := mkw 0x019b360000000000 0x203366c000000000 0xc1fffe0000000000 0x183fffc000000000

def z1281 : W := mkw 0x173260001fdd8001 0x02e64c0003fbb000 0xd7fff8001fff8000 0x7affff0003fff000

def z1282 : W := mkw 0x082c52122d75b5d8 0x01058a4245aeb6bb 0x981c06067df1f1fb 0x930380c0cfbe3e3f

def z1283 : W := mkw 0xe7dfbfffe0204c82 0xbcfbf7fffc040990 0xe7ffffffe0000e04 0x7cfffffffc0001c0

def z1284 : W := mkw 0xe7dfbfffe02206a8 0xbcfbf7fffc0440d5 0xffffffffe3e00fff 0xfffffffffc7c01ff

def z1285 : W := mkw 0xe7dfbedfe0000000 0xbcfbf7dbfc000000 0xc7fffe07e0000000 0x78ffffc0fc000000

def z1286 : W := mkw 0x579bff6996deda61 0x6af37fed32dbdb4c 0xfffffff99efe7e65 0x7fffffff33dfcfcc

def z1287 : W := mkw 0x7ff3e5e55f997951 0x6ffe7cbcabf32f2a 0x05e3c1c01c007000 0x20bc783803800e00

def z1288 : W := mkw 0xa7dfb7f740000000 0x34fbf6fee8000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1289 : W := mkw 0x20c184c540002100 0x04183098a8000420 0xede3c7c7e0007182 0x7dbc78f8fc000e30

def z1290 : W := mkw 0x102c5a1abfffefab 0x02058b4357fffdf5 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z1291 : W := mkw 0xe7d3a5e552004800 0xbcfa74bcaa400900 0x05e3c1c01c007000 0x20bc783803800e00

def z1292 : W := mkw 0x87d325a400000000 0x30fa64b480000000 0x05e3c1c000000000 0x20bc783800000000

def z1293 : W := mkw 0x179b760016dd8001 0x22f36ec002dbb000 0xc7fffe0002ff8000 0x78ffffc0005ff000

def z1294 : W := mkw 0x60cbbecde0000000 0xac1977d9bc000000 0xc1e3fe07e0000000 0x183c7fc0fc000000

def z1295 : W := mkw 0x082852000d55b150 0x01050a4001aab62a 0xda1c3e001ffff1fb 0xdb4387c003fffe3f

def z1296 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xe7ffffffe3ef8f9e 0xfcfffffffc7df1f3

def z1297 : W := mkw 0x26c3a4c540000000 0x04d87498a8000000 0xe7e3ffc7e0000000 0x7cfc7ff8fc000000

def z1298 : W := mkw 0xa1dd9edfe06686a8 0xb43bb3dbfc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1299 : W := mkw 0x182040001fdd9051 0x0304080003fbb20a 0x100000001fff8079 0x8200000003fff00f

def z1300 : W := mkw 0x875441b6161a5a60 0x50ea8836c2c34b4c 0xbffc01fe1e1e7e65 0x77ff803fc3c3cfcc

def z1301 : W := mkw 0xc752a9ed80000000 0x18ea553db0000000 0x67e3f9f980000000 0x6cfc7f3f30000000

def z1302 : W := mkw 0x479bbf6980468220 0x28f377ed3008d044 0xfffffff983ff8e65 0x7fffffff307ff1cc

def z1303 : W := mkw 0x182852001fddb151 0x03050a4003fbb62a 0xfa1c3e07fffff1fb 0xdf4387c0fffffe3f

def z1304 : W := mkw 0xa7d185e540000000 0x14fa30bca8000000 0x05e3c1c000000000 0x20bc783800000000

def z1305 : W := mkw 0x979f373212a04c82 0x32f3e6e642540990 0xc7fffe3802e00e04 0x78ffffc7005c01c0

def z1306 : W := mkw 0x4602a969920a4a20 0x48c0552d32414944 0x7e03f9f99e0e7e04 0x6fc07f3f33c1cfc0

def z1307 : W := mkw 0x28c184c540003150 0x05183098a800062a 0xfde3c7c7e111f1fb 0xffbc78f8fc223e3f

def z1308 : W := mkw 0xe7dfbfffe066dee8 0xfcfbf7fffc0cdbdd 0xffffffffe3ffffff 0xfffffffffc7fffff

def z1309 : W := mkw 0x182040001fbb7ff2 0x4304080003f76ffe 0x180000001fffffff 0x8300000003ffffff

def z1310 : W := mkw 0xe7dfbfffe0468228 0xbcfbf7fffc08d045 0xffffffffe11f81fb 0xfffffffffc23f03f

def z1311 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xffffc7c7fff1f1fb 0xfffff8f8fffe3e3f

def z1312 : W := mkw 0xa0c585f740000000 0x1418b0bee8000000 0xe5e3c7ffe0000000 0x7cbc78fffc000000

def z1313 : W := mkw 0x0712200000000000 0x00e2440000000000 0xc7fff80000000000 0x78ffff0000000000

def z1314 : W := mkw 0x102a72001fdd8001 0x22054e4003fbb000 0x100038001fff8000 0x0200070003fff000

def z1315 : W := mkw 0xd712e969969a5a62 0x5ae25d2d32d34b4c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z1316 : W := mkw 0xbff3e5e55f997953 0x37fe7cbcabf32f2a 0x05e3c1c01c007000 0x20bc783803800e00

def z1317 : W := mkw 0x179b360012800000 0x22f366c002500000 0xc7fffe0002e00000 0x78ffffc0005c0000

def z1318 : W := mkw 0x608bfe49e45e9268 0xec117fc93c8bd24d 0x4003fe01e01f8079 0x88007fc03c03f00f

def z1319 : W := mkw 0x20c996c540000000 0x041932d8a8000000 0xe7ffffc7e0000000 0x7cfffff8fc000000

def z1320 : W := mkw 0x102040001fdf9261 0x4204080003fbf24c 0x100000001fff8061 0x0200000003fff00c

def z1321 : W := mkw 0x079f3e1aa06686a8 0x20f3e7c3540cd0d5 0xc7fffe3802ee0e04 0x78ffffc7005dc1c0

def z1322 : W := mkw 0xa1dd96d760000000 0xb43bb2daec000000 0x85ffc7c660000000 0x30bff8f8cc000000

def z1323 : W := mkw 0x002040001f190000 0x0004080003e32000 0x100000001f1f8000 0x0200000003e3f000

def z1324 : W := mkw 0x102040001f996903 0x0204080003f32d20 0x000000001c007000 0x0000000003800e00

def z1325 : W := mkw 0xe7dfbfffe02206a8 0xbcfbf7fffc0440d5 0xffffffffe1118fff 0xfffffffffc2231ff

def z1326 : W := mkw 0xb77401b67ba06d82 0x96ee8036cf740db0 0xbffc01fe7fe07f86 0x77ff803fcffc0ff0

def z1327 : W := mkw 0x37bb76007fdd8001 0xa6f76ec00ffbb000 0xd7fffe007fff8000 0x7affffc00ffff000

def z1328 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xe5e3c7c7e101819a 0xfcbc78f8fc203033

def z1329 : W := mkw 0x87db37a400000000 0x30fb66f480000000 0xc7ffffc000000000 0x78fffff800000000

def z1330 : W := mkw 0x573089699b825a60 0x4ae6112d33704b4c 0xbffc01f99fe07e65 0x77ff803f33fc0fcc

def z1331 : W := mkw 0x27dfbedfe0000000 0x24fbf7dbfc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1332 : W := mkw 0x66cfbfffe06686a8 0x0cd9f7fffc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1333 : W := mkw 0xe7dfbffff26ecea8 0xfcfbf7fffe4dd9d5 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z1334 : W := mkw 0xb9fd169669e5a59a 0x173fa2d2cd3cb4b3 0x81fc060661e1819a 0x903f80c0cc3c3033

def z1335 : W := mkw 0x071a320000448000 0x20e3464000089000 0x021c380002ee0000 0x00438700005dc000

def z1336 : W := mkw 0x002040001f1b5a60 0x4004080003e36b4c 0x180000001f1ffe65 0x0300000003e3ffcc

def z1337 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0xfe03f9ff9f1e7fe7 0x7fc07f3ff3e3cffc

def z1338 : W := mkw 0xe7d3a5e552084800 0xfcfa74bcaa410900 0x05e3c1c000000000 0x20bc783800000000

def z1339 : W := mkw 0x002040001f1a7b60 0x4004080003e34f6c 0x180000001f1e7fe7 0x0300000003e3cffc

def z1340 : W := mkw 0x87df37b600648480 0x30fbe6f6c00c9090 0xfffffffe03ff8f86 0x7fffffffc07ff1f0

def z1341 : W := mkw 0xb864c1f75fb17dd2 0x170c983eebf62fba 0x380001fffff1ffff 0x8700003ffffe3fff

def z1342 : W := mkw 0x173040001fdd8001 0x02e6080003fbb000 0x121c00001fff8000 0x0243800003fff000

def z1343 : W := mkw 0x60c3accdc0000000 0x0c187599b8000000 0xe5e3ffc7e0000000 0x7cbc7ff8fc000000

def z1344 : W := mkw 0x87df3fbea0000000 0x30fbe7f7d4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1345 : W := mkw 0x0081040000000000 0x0010208000000000 0xfde3c607e11181fb 0xffbc78c0fc22303f

def z1346 : W := mkw 0xefdfbfffe0003150 0xbdfbf7fffc00062a 0xe7ffffffe0007000 0x7cfffffffc000e00

def z1347 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe2000e04 0x7ffffffffc4001c0

def z1348 : W := mkw 0x17bb77201fddc801 0x22f76ee403fbb900 0xd7ffffc01ffff000 0x7afffff803fffe00

def z1349 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0x07fff9f802ee0e04 0x20ffff3f005dc1c0

def z1350 : W := mkw 0x07db368400000000 0x20fb66d080000000 0xe7ffffc600000000 0x7cfffff8c0000000

def z1351 : W := mkw 0x082040001f117950 0x0104080003e22f2a 0x180000001f11ffff 0x8300000003e23fff

def z1352 : W := mkw 0x179b360012880001 0x22f366c002510000 0xc7fffe0000000000 0x78ffffc000000000

def z1353 : W := mkw 0x079b3e0880020220 0x20f367c110004044 0xfffffe39821e0e65 0x7fffffc73043c1cc

def z1354 : W := mkw 0x102040001fdf8229 0x0204080003fbf045 0x100000001fff8079 0x8200000003fff00f

def z1355 : W := mkw 0xe7dbbfede0468228 0xbcfb77fdbc08d045 0x45e3ffc1e01f8079 0xa8bc7ff83c03f00f

def z1356 : W := mkw 0xc71e3b3ab26ecea8 0xf8e3c767564dd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z1357 : W := mkw 0xe7dfbfffe0202582 0xbcfbf7fffc0404b0 0xe7ffffffe0000182 0x7cfffffffc000030

def z1358 : W := mkw 0xe7d3adedc0000000 0xbcfa75bdb8000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z1359 : W := mkw 0x0081040000000000 0x0010208000000000 0xe5e3c607e0000000 0x7cbc78c0fc000000

def z1360 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xfffc07fe1ff1ff86 0x7fff80ffc3fe3ff0

def z1361 : W := mkw 0xa7df3e9ee0000000 0xb4fbe7d3dc000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z1362 : W := mkw 0x182040001f993151 0x0304080003f3262a 0x180000001d11f1fb 0x8300000003a23e3f

def z1363 : W := mkw 0x182040001fb17dd2 0x0304080003f62fba 0x180000001fe07f86 0x0300000003fc0ff0

def z1364 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xefffffffe1e18fff 0xfdfffffffc3c31ff

def z1365 : W := mkw 0x28c184c540003150 0x05183098a800062a 0xe5e3c7c7e0007000 0x7cbc78f8fc000e00

def z1366 : W := mkw 0x91fd169629e5a58b 0x323fa2d2c53cb4b1 0x81fc060661e1819a 0x903f80c0cc3c3033

def z1367 : W := mkw 0x2860c0c54d113150 0x050c1818a9a2262a 0x180001c01d11f1fb 0x8300003803a23e3f

def z1368 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x25e3c1c7e0000000 0x24bc7838fc000000

def z1369 : W := mkw 0x079b360000000000 0x20f366c000000000 0xd7fffe0001118000 0x7affffc000223000

def z1370 : W := mkw 0xc756a1f700000000 0x18ead43ee0000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z1371 : W := mkw 0x102c5a1abfdd8001 0x02058b4357fbb000 0xf21c3e3fffff8000 0x5e4387c7fffff000

def z1372 : W := mkw 0x28c184c540010010 0x05183098a8002002 0xe5e3c7c7e0018018 0xfcbc78f8fc003003

def z1373 : W := mkw 0xf7dfbffff2ceca21 0xfefbf7fffe59d944 0xe7ffffffe2ee0e04 0x7cfffffffc5dc1c0

def z1374 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xf7ffffffe3ff8e04 0x7efffffffc7ff1c0

def z1375 : W := mkw 0x4712a96980000000 0x08e2552d30000000 0xe7fff9f980000000 0x7cffff3f30000000

def z1376 : W := mkw 0xa1df369660000000 0xb43be6d2cc000000 0xc1fffe0660000000 0x183fffc0cc000000

def z1377 : W := mkw 0x1fbb76001fdd9051 0x23f76ec003fbb20a 0xd7fffe001fff8079 0xfaffffc003fff00f

def z1378 : W := mkw 0x977401b61ba06d82 0x12ee8036c3740db0 0xadfc01fe1de07f86 0x35bf803fc3bc0ff0

def z1379 : W := mkw 0x9174009609a02582 0x122e8012c13404b0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1380 : W := mkw 0xe7dfbfffe0020220 0xbcfbf7fffc004044 0xe7ffffffe01e0061 0x7cfffffffc03c00c

def z1381 : W := mkw 0xa1dd96d760648488 0xb43bb2daec0c9091 0xfdffc7c7e1f181fb 0xffbff8f8fc3e303f

def z1382 : W := mkw 0x0004081aa02206a8 0x00008103540440d5 0x3800003fe1118fff 0x87000007fc2231ff

def z1383 : W := mkw 0x173401321ba04c80 0x02e6802643740990 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1384 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x97fff8001fee0000 0x72ffff0003fdc000

def z1385 : W := mkw 0x4000c969961a5a60 0x4800192d32c34b4c 0x280001f99c007e65 0x0500003f33800fcc

def z1386 : W := mkw 0x102040000ddd8001 0x0204080001bbb000 0x0000000001ff8000 0x00000000003ff000

def z1387 : W := mkw 0x079b360000000000 0x20f366c000000000 0xd7fffe0003e00000 0x7affffc0007c0000

def z1388 : W := mkw 0xd756a9ff92aa4ea2 0x5aead53ff25549d4 0xe7fff9ff82ee0e04 0x7cffff3ff05dc1c0

def z1389 : W := mkw 0x906401b61ba06d82 0x120c8036c3740db0 0x280001fe1c007f86 0x0500003fc3800ff0

def z1390 : W := mkw 0xe7d3a5e552004800 0xbcfa74bcaa400900 0x3fe3c1f81e007e04 0x67fc783f03c00fc0

def z1391 : W := mkw 0xf7dfbffff2a06d82 0xbefbf7fffe540db0 0xefffffffe2e07f86 0x7dfffffffc5c0ff0

def z1392 : W := mkw 0x102040001fb16d82 0x0204080003f62db0 0x180000001ff1ff86 0x0300000003fe3ff0

def z1393 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x6c03f9f99c1e7e65 0x2d807f3f3383cfcc

def z1394 : W := mkw 0x608bfe49e45f9261 0xec117fc93c8bf24c 0x4003fe01e01f8061 0x08007fc03c03f00c

def z1395 : W := mkw 0xe7dfbfffe0468228 0xbcfbf7fffc08d045 0xf7ffffffe3ff8079 0xfefffffffc7ff00f

def z1396 : W := mkw 0x079bb64100000000 0x20f376c820000000 0xe7ffffc180000000 0x7cfffff830000000

def z1397 : W := mkw 0x479b3f28920a4a20 0x68f367e512414944 0xc7fffe38020e0e04 0x78ffffc70041c1c0

def z1398 : W := mkw 0x20c184c540000000 0x04183098a8000000 0x85e3c7c660000000 0x30bc78f8cc000000

def z1399 : W := mkw 0x2081844140000000 0x0410308828000000 0xc5e3c601e0000000 0x78bc78c03c000000

def z1400 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xf7fffe07ffff8000 0x7effffc0fffff000

def z1401 : W := mkw 0x0199160000000000 0x203322c000000000 0xc5ffc60000000000 0x78bff8c000000000

def z1402 : W := mkw 0x182040001f917952 0x0304080003f22f2a 0x180000001d11f1fb 0x8300000003a23e3f

def z1403 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xd7fffe01ffff8079 0xfaffffc03ffff00f

def z1404 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xfde3c7c7fc007000 0x7fbc78f8ff800e00

def z1405 : W := mkw 0xe7dfbfffe0648488 0xbcfbf7fffc0c9091 0xe7ffffffe0e00000 0x7cfffffffc1c0000

def z1406 : W := mkw 0x2885c453443114d0 0x0510b88a6886229a 0xfa1fc63fe3f18fff 0xdf43f8c7fc7e31ff

def z1407 : W := mkw 0x4602e16116185840 0x48c05c2c22c30b08 0x7e03f9f81e1e7e04 0x6fc07f3f03c3cfc0

def z1408 : W := mkw 0xf7dfbffff2880001 0xbefbf7fffe510000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1409 : W := mkw 0x4602e969961a5a60 0x48c05d2d32c34b4c 0x5603f9f81e1e7e04 0x6ac07f3f03c3cfc0

def z1410 : W := mkw 0x082440120d3135d0 0x0104880241a626ba 0xba1c003e1ff1ffff 0xd7438007c3fe3fff

def z1411 : W := mkw 0x6793a44140000000 0xacf2748828000000 0x05e3c00000000000 0x20bc780000000000

def z1412 : W := mkw 0x4602e96984121260 0x08c05d2d3082424c 0x7e03f9f99e1e7e65 0x6fc07f3f33c3cfcc

def z1413 : W := mkw 0x182c5a1abfffb7f9 0x03058b4357fff6ff 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z1414 : W := mkw 0x079b360000000000 0x20f366c000000000 0x85ffc60000000000 0x30bff8c000000000

def z1415 : W := mkw 0x173a72001fdc8000 0x02e74e4003fb9000 0xd7fffe001fff8000 0x7affffc003fff000

def z1416 : W := mkw 0xa7d185e540000000 0x14fa30bca8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z1417 : W := mkw 0x182040001f993151 0x0304080003f3262a 0x000000001c007000 0x0000000003800e00

def z1418 : W := mkw 0xe7dfbfffe0458001 0xbcfbf7fffc08b000 0xe7ffffffe0018000 0x7cfffffffc003000

def z1419 : W := mkw 0xc756a9ff802206a0 0x18ead53ff00440d4 0xfffff9ff83fe0fe7 0x7fffff3ff07fc1fc

def z1420 : W := mkw 0x608bbe49e0000000 0xac1177c93c000000 0xc5e3fe01e0000000 0x78bc7fc03c000000

def z1421 : W := mkw 0x17bb76001fdda101 0x22f76ec003fbb420 0xdffffe001ffff182 0x7bffffc003fffe30

def z1422 : W := mkw 0x2860c0c54d113150 0x050c1818a9a2262a 0x000001c01c007000 0x0000003803800e00

def z1423 : W := mkw 0xe7dfbfffe0024a20 0xfcfbf7fffc004944 0xe7ffffffe0000e04 0x7cfffffffc0001c0

def z1424 : W := mkw 0x0793240000000000 0x20f2648000000000 0x87ffc00000000000 0x70fff80000000000

def z1425 : W := mkw 0x00e144840d112100 0x001c289081a22420 0xfde3c7c7fd11f1fb 0xffbc78f8ffa23e3f

def z1426 : W := mkw 0x9f7401b61ba16d92 0x13ee8036c3742db2 0xbffc01fe1fe1ff9e 0xf7ff803fc3fc3ff3

def z1427 : W := mkw 0xe7dfbfffe00a0220 0xfcfbf7fffc014044 0xe7ffffffe00e0000 0x7cfffffffc01c000

def z1428 : W := mkw 0x97bb77201fddc803 0x32f76ee403fbb900 0xd7fffe001fff8000 0x7affffc003fff000

def z1429 : W := mkw 0x806401b609206d82 0x100c8036c1240db0 0x380001fe1d007f86 0x0700003fc3a00ff0

def z1430 : W := mkw 0xa1dd9edfe0000000 0xb43bb3dbfc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1431 : W := mkw 0xe1d3a4c540000000 0xbc3a7498a8000000 0x01e3c00000000000 0x003c780000000000

def z1432 : W := mkw 0x102040000dd58001 0x0204080001bab000 0x100000001df18000 0x0200000003be3000

def z1433 : W := mkw 0xe04489ffe0227fe2 0xdc08913ffc044ffc 0x280001ffe0007fe7 0x0500003ffc000ffc

def z1434 : W := mkw 0xe7dfbfffe0020220 0xbcfbf7fffc004044 0xffffffffe31f8fff 0xfffffffffc63f1ff

def z1435 : W := mkw 0x10285a089fdfda61 0x42050b4113fbfb4c 0xfa1c3e399ffffe65 0x5f4387c733ffffcc

def z1436 : W := mkw 0xa0c585f740206d82 0x1418b0bee8040db0 0xede3c7ffe0007f86 0x7dbc78fffc000ff0

def z1437 : W := mkw 0xe7dbb7e560000000 0xbcfb76fcac000000 0x05e3c7c060000000 0x20bc78f80c000000

def z1438 : W := mkw 0x66cbbfede0000000 0xacd977fdbc000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z1439 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0xa5e3c1c600000000 0x74bc7838c0000000

def z1440 : W := mkw 0xc75ebbffa06686a8 0x18ebd77ff40cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1441 : W := mkw 0xe7dfbfffe0005840 0xfcfbf7fffc000b08 0xe7ffffffe0007000 0x7cfffffffc000e00

def z1442 : W := mkw 0x102040001fb96d83 0x0204080003f72db0 0x180000001fe07f86 0x0300000003fc0ff0

def z1443 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xc3fffe0003ff8000 0x187fffc0007ff000

def z1444 : W := mkw 0x0081040000000000 0x0010208000000000 0x05e3c00000000000 0x20bc780000000000

def z1445 : W := mkw 0xf7dfbfffe0c48001 0xbefbf7fffc189000 0xe7ffffffe0e00000 0x7cfffffffc1c0000

def z1446 : W := mkw 0x60cfbedfe06686a8 0xac19f7dbfc0cd0d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1447 : W := mkw 0x082040000d112110 0x0104080001a22422 0x100000001d11819a 0x8200000003a23033

def z1448 : W := mkw 0xa1d584d740000000 0x143ab09ae8000000 0xe5ffc7c7e0000000 0x7cbff8f8fc000000

def z1449 : W := mkw 0xe7dfbfffe0200480 0xbcfbf7fffc040090 0xefffffffe0000f86 0x7dfffffffc0001f0

def z1450 : W := mkw 0x679bb64140000000 0xacf376c828000000 0xc7fffe0000000000 0x78ffffc000000000

def z1451 : W := mkw 0xe0cfbfffe0000000 0xbc19f7fffc000000 0xe5e3ffffe0000000 0x7cbc7ffffc000000

def z1452 : W := mkw 0x11bb76000ddd8001 0x22376ec001bbb000 0xd3fffe0003ff8000 0x5a7fffc0007ff000

def z1453 : W := mkw 0x102040001ffd8489 0x0204080003ffb091 0x100000001fff819a 0x8200000003fff033

def z1454 : W := mkw 0x288bfe49e45f9279 0x25117fc93c8bf24f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z1455 : W := mkw 0xe7dbbfede0000000 0xbcfb77fdbc000000 0x67e3fff9e0000000 0x6cfc7fff3c000000

def z1456 : W := mkw 0xe0c185e540000000 0x9c1830bca8000000 0x05e3c1c000000000 0x20bc783800000000

def z1457 : W := mkw 0xd064c9ff9fba7fe2 0x5a0c993ff3f74ffc 0x380001ff9ffe7fe7 0x0700003ff3ffcffc

def z1458 : W := mkw 0x079b360000000000 0x20f366c000000000 0x45e3fe0000000000 0x28bc7fc000000000

def z1459 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xd7fffe067fff819a 0xfaffffc0cffff033

def z1460 : W := mkw 0x066401b61b206d80 0x00cc8036c3640db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1461 : W := mkw 0x102040001fff86a9 0x0204080003fff0d5 0x100000001fff8e04 0x0200000003fff1c0

def z1462 : W := mkw 0x182040001f917952 0x0304080003f22f2a 0x000000001c007000 0x0000000003800e00

def z1463 : W := mkw 0x082040000d137b70 0x4104080001a26f6e 0x180000001d11ffff 0x8300000003a23fff

def z1464 : W := mkw 0x6860c9eddf1b7b70 0x4d0c193dbbe36f6e 0x380001ffff1fffff 0x8700003fffe3ffff

def z1465 : W := mkw 0x102040001fdd8001 0x0204080003fbb000 0xd00006001fff8000 0x5a0000c003fff000

def z1466 : W := mkw 0xe7d58dffe0000000 0x9cfab1bffc000000 0xe7ffc7ffe0000000 0x7cfff8fffc000000

def z1467 : W := mkw 0x102040001fffdee9 0x4204080003fffbdd 0x180000001fffffff 0x8300000003ffffff

def z1468 : W := mkw 0xe7dbb7e540000000 0xbcfb76fca8000000 0x45e3ffc000000000 0x28bc7ff800000000

def z1469 : W := mkw 0x082040000d1b3370 0x4104080001a3666e 0x180000001d1ff1fb 0x8300000003a3fe3f

def z1470 : W := mkw 0x679fbe5be0000000 0xacf3f7cb7c000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z1471 : W := mkw 0x08285a08ad57b378 0x01050b4115aaf66f 0x58003e01fd1ff1fb 0x8b0007c03fa3fe3f

def z1472 : W := mkw 0x4683ad6980000000 0x08d075ad30000000 0xe7e3fff980000000 0x7cfc7fff30000000

def z1473 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x00000000011181fb 0x800000000022303f

def z1474 : W := mkw 0xe7dfbfffe0648488 0xbcfbf7fffc0c9091 0xffffffffe3e18f9e 0xfffffffffc7c31f3

def z1475 : W := mkw 0x27d3a4c540000000 0x24fa7498a8000000 0xe5e3c7c7e0000000 0x7cbc78f8fc000000

def z1476 : W := mkw 0x0793240000000000 0x20f2648000000000 0x47e3f80000000000 0x68fc7f0000000000

def z1477 : W := mkw 0x173260001fdd8001 0x22e64c0003fbb000 0x100000001fff8000 0x0200000003fff000

def z1478 : W := mkw 0xf7dbb7e552cc8001 0xbefb76fcaa599000 0x07fff9c002ee0000 0x20ffff38005dc000

def z1479 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xefffffffe00001fb 0xfdfffffffc00003f

def z1480 : W := mkw 0xe7d7a5f740000000 0xbcfaf4bee8000000 0x25e3c1fe00000000 0x24bc783fc0000000

def z1481 : W := mkw 0x00ab76000d5d8001 0x20156ec001abb000 0xd7fffe001fff8000 0x7affffc003fff000

def z1482 : W := mkw 0xe7dfbffff20a4a20 0xfcfbf7fffe414944 0xffffffffe21e0e65 0x7ffffffffc43c1cc

def z1483 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x47e3f9c000000000 0x68fc7f3800000000

def z1484 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xe7ffffffe2000e04 0x7cfffffffc4001c0

def z1485 : W := mkw 0x977401b61b804800 0x12ee8036c3700900 0xbffc01fe1fe07e04 0x77ff803fc3fc0fc0

def z1486 : W := mkw 0x0683240000000000 0x00d0648000000000 0xc7e3fe0000000000 0x78fc7fc000000000

def z1487 : W := mkw 0xe7dfbffff20a4a20 0xfcfbf7fffe414944 0xfffffffffe0e7e04 0x7fffffffffc1cfc0

def z1488 : W := mkw 0x806401b609206d82 0x100c8036c1240db0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1489 : W := mkw 0x102440121ffd8481 0x0204880243ffb090 0xba1c003e1fff8f86 0x57438007c3fff1f0

def z1490 : W := mkw 0xe7dfbffff2080000 0xbcfbf7fffe410000 0xe7ffffffe20e0000 0x7cfffffffc41c000

def z1491 : W := mkw 0x11b956000dd58001 0x22372ac001bab000 0xd7fffe001fff8000 0x7affffc003fff000

def z1492 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xf7ffffffe21e0000 0x7efffffffc43c000

def z1493 : W := mkw 0x079b360000448000 0x20f366c000089000 0xc7fffe0001e18000 0x78ffffc0003c3000

def z1494 : W := mkw 0xb9fd169649e5a593 0x373fa2d2c93cb4b2 0x81fc060661e1819a 0x903f80c0cc3c3033

def z1495 : W := mkw 0xe7d3adedc0000000 0xbcfa75bdb8000000 0x25e3c1f980000000 0x24bc783f30000000

def z1496 : W := mkw 0x17b364001f990000 0x02f66c8003f32000 0xd7fffe001fff8000 0x7affffc003fff000

def z1497 : W := mkw 0x479bbf6980025a60 0x68f377ed30004b4c 0xeffffff980007e65 0x7dffffff30000fcc

def z1498 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xc3fffe3fe0000000 0x187fffc7fc000000

def z1499 : W := mkw 0x102040001ffdcc83 0x0204080003ffb990 0x100000001fff8e04 0x0200000003fff1c0

def z1500 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0x57fff8001efe0000 0x6affff0003dfc000

def z1501 : W := mkw 0x21d996c540000000 0x243b32d8a8000000 0xe5ffc7c7e0000000 0x7cbff8f8fc000000

def z1502 : W := mkw 0xd71e3b3ab2eeceaa 0x5ae3c767565dd9d5 0x021c383802ee0e04 0x00438707005dc1c0

def z1503 : W := mkw 0xe7dfbffff2206d82 0xbcfbf7fffe440db0 0xfffffffffe007f86 0x7fffffffffc00ff0

def z1504 : W := mkw 0x28c184c540002110 0x05183098a8000422 0xe5e3c7c7e000019a 0xfcbc78f8fc000033

def z1505 : W := mkw 0x082040000d113150 0x0104080001a2262a 0x780000019d11f1fb 0xcf00000033a23e3f

def z1506 : W := mkw 0xe7dfbfffe06686a8 0xbcfbf7fffc0cd0d5 0xe7ffffffe1ff81fb 0xfcfffffffc3ff03f

def z1507 : W := mkw 0x079b360000000000 0x20f366c000000000 0xd7fffe00021e0000 0x7affffc00043c000

def z1508 : W := mkw 0x082048088d133370 0x0104090111a2666e 0x7a0038399f1fffff 0xcf40070733e3ffff

def z1509 : W := mkw 0x17bb76001fdd8001 0x22f76ec003fbb000 0xfffffe381fff8e04 0x7fffffc703fff1c0

def z1510 : W := mkw 0x008d1e1aa06686a8 0x0011a3c3540cd0d5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1511 : W := mkw 0x5712e969969a5a60 0x4ae25d2d32d34b4c 0x7e1ff9f99efe7e65 0x6fc3ff3f33dfcfcc

def z1512 : W := mkw 0x082040000d113150 0x0104080001a2262a 0xb80000061d11f1fb 0xd7000000c3a23e3f

def z1513 : W := mkw 0x102040001fddd841 0x4204080003fbbb08 0x100000001ffff000 0x0200000003fffe00

def z1514 : W := mkw 0x679bbe49e0468228 0xacf377c93c08d045 0xd7fffe01e3ff8079 0xfaffffc03c7ff00f

def z1515 : W := mkw 0x28e10c8cc9032330 0x051c219199206466 0xfbe03e3fe31f8fff 0xdf7c07c7fc63f1ff

def z1516 : W := mkw 0x286cdadfed77b7f8 0x050d9b5bfdaef6ff 0xfa1c3fffffffffff 0xdf4387ffffffffff

def z1517 : W := mkw 0x008b3600004c8001 0x201166c000099000 0x4003fe00000e0000 0x08007fc00001c000

def z1518 : W := mkw 0xe7dfbfffe0448000 0xbcfbf7fffc089000 0xe7ffffffe2ee0000 0x7cfffffffc5dc000

def z1519 : W := mkw 0x0199160000448000 0x203322c000089000 0x81fc060001e18000 0x103f80c0003c3000

def z1520 : W := mkw 0xf7dfbffff2e6ceaa 0xbefbf7fffe5cd9d5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1521 : W := mkw 0xe7dfbffff2024a20 0xbcfbf7fffe404944 0xfffffffffe1e7e65 0x7fffffffffc3cfcc

def z1522 : W := mkw 0x4793a56100000000 0x28f274ac20000000 0x05e3c1c000000000 0x20bc783800000000

def z1523 : W := mkw 0xe7d3a5e540000000 0xbcfa74bca8000000 0x45e3c7c1e0000000 0x28bc78f83c000000

def z1524 : W := mkw 0xe7dbb7e540000000 0xbcfb76fca8000000 0x07fff9c000000000 0x20ffff3800000000

def z1525 : W := mkw 0x079b360000000000 0x20f366c000000000 0xfffffe07e11181fb 0xffffffc0fc22303f

def z1526 : W := mkw 0x87df37b600206d82 0x30fbe6f6c0040db0 0xeffffffe00007f86 0x7dffffffc0000ff0

def z1527 : W := mkw 0x002040000d111040 0x0004080001a22208 0x180000001d11f061 0x0300000003a23e0c

def z1528 : W := mkw 0x079f3e1aa0000000 0x20f3e7c354000000 0xc7fffe3800000000 0x78ffffc700000000

def z1529 : W := mkw 0xc79f3f3aa06686a8 0xb8f3e7e7540cd0d5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1530 : W := mkw 0x6ec3adedc0027b70 0x4dd875bdb8004f6e 0xefe3ffffe0007fff 0xfdfc7ffffc000fff

def z1531 : W := mkw 0x20c184c540000000 0x04183098a8000000 0xc5e3c7c000000000 0x78bc78f800000000

def z1532 : W := mkw 0x002040000d103140 0x0004080001a20628 0x180000001d1071e3 0x0300000003a20e3c

def z1533 : W := mkw 0xe7dfbfffe0200480 0xbcfbf7fffc040090 0xe7ffffffe2e00e04 0x7cfffffffc5c01c0

def z1534 : W := mkw 0xe7df3fbee0000000 0xbcfbe7f7dc000000 0xc7fffe3e60000000 0x78ffffc7cc000000

def z1535 : W := mkw 0x28cd9edfe02237f8 0x0519b3dbfc0446ff 0xefffffffe0007fff 0xfdfffffffc000fff

def z1536 : W := mkw 0xe7dbbfede0000000 0xbcfb77fdbc000000 0x05e3f9c000000000 0x20bc7f3800000000

def z1537 : W := mkw 0x182040001fddb151 0x0304080003fbb62a 0x100000001ffff000 0x0200000003fffe00

def z1538 : W := mkw 0x004080c500000000 0x00081018a0000000 0xe5e3c1c780000000 0x7cbc7838f0000000

def z1539 : W := mkw 0x20c996c540448000 0x041932d8a8089000 0xf7ffffc7e3ff8000 0x7efffff8fc7ff000

def z1540 : W := mkw 0x2fdbb6c540003150 0x25fb76d8a800062a 0xefffffc7e00071fb 0xfdfffff8fc000e3f

def z1541 : W := mkw 0x879f361220000000 0xb0f3e6c244000000 0xc7fffe0000000000 0x78ffffc000000000

def z1542 : W := mkw 0x0004081a802206a0 0x00008103500440d4 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z1543 : W := mkw 0x28e1c4c54d113150 0x051c3898a9a2262a 0xade3c7c7fd01f1fb 0xb5bc78f8ffa03e3f

def z1544 : W := mkw 0xc79f3f3aa0000000 0xb8f3e7e754000000 0x07fff83800000000 0x20ffff0700000000

def z1545 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe0100061 0x7ffffffffc02000c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z9,z5,z10]),(0,[z1,z2,z8,z4,z5,z11,z6])],[(1,[z1,z2,z12,z8,z4,z6]),(0,[z13,z1,z2,z8,z4,z5,z6]),(1,[z1,z14,z15,z8,z4,z5]),(0,[z1,z16,z2,z8,z8,z4,z5])],[(1,[z1,z2,z8,z4,z5,z17]),(0,[z18,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z19,z10]),(0,[z1,z2,z8,z4,z20,z5,z6])],[(0,[z21,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z23]),(0,[z1,z24,z2,z25,z8,z4,z5])],[(0,[z1,z2,z8,z4,z26,z5,z6]),(0,[z1,z27,z2,z8,z4,z5,z22]),(0,[z1,z24,z14,z2,z8,z4,z5]),(0,[z1,z28,z2,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z29,z6,z30]),(0,[z1,z2,z8,z4,z5,z31,z6]),(0,[z1,z32,z2,z8,z4,z5,z6])],[(0,[z1,z2,z33,z8,z4,z5,z6]),(0,[z1,z16,z2,z8,z4,z34,z5]),(0,[z1,z35,z2,z25,z8,z4,z5]),(0,[z1,z16,z2,z8,z36,z4,z5])],[(0,[z1,z15,z2,z8,z4,z5,z37])],[(0,[z1,z2,z8,z4,z38,z5,z6])],[(0,[z1,z14,z2,z8,z4,z34,z5]),(0,[z1,z2,z8,z4,z39,z5,z6]),(0,[z1,z2,z8,z4,z5,z40,z6])],[(0,[z1,z2,z8,z4,z5,z41,z6])],[],[(1,[z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z42,z6]),(1,[z1,z16,z43,z8,z4,z5]),(0,[z44,z1,z2,z8,z4,z5,z45]),(0,[z1,z2,z8,z4,z5,z6,z45])],[(0,[z1,z46,z2,z8,z4,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z47]),(0,[z48,z49,z2,z8,z4,z5,z6]),(0,[z1,z50,z51,z2,z8,z4,z6]),(1,[z1,z2,z52,z8,z4,z5]),(1,[z1,z43,z8,z4,z5,z6]),(0,[z1,z16,z2,z8,z4,z5,z29])],[(0,[z1,z15,z53,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z54]),(0,[z1,z55,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z56]),(0,[z1,z57,z2,z25,z8,z4,z5]),(0,[z58,z1,z2,z8,z4,z5,z6]),(0,[z1,z50,z2,z8,z4,z5,z59])],[(0,[z49,z1,z2,z8,z4,z5,z60])]],
   [[(0,[z1,z2,z8,z4,z4,z5,z6]),(0,[z1,z61,z16,z2,z8,z4,z5]),(0,[z1,z14,z2,z8,z4,z5,z29]),(0,[z1,z57,z2,z52,z8,z4,z5]),(0,[z1,z62,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z17]),(1,[z1,z2,z8,z4,z5,z63])],[],[(0,[z64,z1,z2,z8,z4,z5,z6])],[(0,[z65,z1,z2,z66,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z67])],[(0,[z1,z16,z2,z8,z4,z68,z5]),(0,[z1,z2,z25,z8,z4,z34,z5]),(0,[z1,z14,z8,z69,z4,z5,z6]),(0,[z1,z57,z2,z8,z70,z4,z5])],[(0,[z71,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z72,z8,z4,z5,z6])],[(0,[z1,z2,z8,z73,z4,z5,z6]),(0,[z1,z74,z2,z8,z4,z5,z6])],[(0,[z1,z14,z2,z8,z4,z68,z5]),(0,[z1,z2,z8,z4,z5,z75,z10])],[(0,[z1,z2,z8,z66,z4,z5,z22]),(0,[z1,z2,z76,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z10,z56]),(0,[z1,z77,z57,z2,z8,z4,z5]),(0,[z1,z57,z2,z8,z4,z78,z5]),(0,[z1,z2,z79,z8,z4,z5,z6]),(0,[z80,z1,z2,z8,z4,z5,z6])],[(0,[z1,z81,z2,z8,z4,z5,z10]),(1,[z1,z14,z8,z69,z4,z5]),(0,[z1,z2,z8,z4,z78,z5,z6])],[(0,[z1,z2,z8,z4,z82,z5,z6]),(1,[z1,z83,z8,z4,z5,z6]),(1,[z1,z2,z8,z84,z4,z6]),(0,[z1,z16,z2,z8,z85,z4,z5])],[(0,[z1,z2,z86,z8,z4,z5,z6]),(0,[z1,z2,z8,z87,z4,z5,z6]),(0,[z1,z24,z57,z2,z8,z4,z5]),(0,[z1,z2,z76,z8,z73,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z29])],[(0,[z1,z88,z2,z8,z4,z5,z6]),(0,[z89,z1,z8,z4,z5,z90,z6]),(0,[z48,z1,z2,z8,z91,z5,z6]),(0,[z1,z2,z8,z4,z5,z92,z10]),(0,[z1,z93,z2,z8,z4,z5,z6])],[(0,[z1,z14,z2,z8,z85,z4,z5])],[(0,[z2,z3,z8,z66,z4,z5,z6]),(0,[z1,z94,z2,z8,z4,z5,z6]),(0,[z44,z1,z27,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z4,z95,z5,z6]),(0,[z96,z1,z2,z8,z4,z5,z22]),(0,[z1,z15,z2,z97,z4,z5,z6]),(0,[z1,z98,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z99,z6]),(0,[z1,z100,z16,z2,z8,z4,z5]),(0,[z1,z2,z8,z5,z101,z6,z45])],[(0,[z1,z16,z2,z8,z4,z102,z5]),(0,[z1,z16,z2,z8,z4,z103,z5]),(1,[z1,z104,z2,z4,z105,z6])],[(0,[z1,z2,z8,z4,z106,z5,z6]),(0,[z1,z2,z8,z4,z5,z107,z6]),(1,[z1,z57,z2,z8,z4,z5])],[(0,[z1,z2,z25,z8,z4,z68,z5]),(0,[z1,z108,z2,z8,z4,z5,z22]),(0,[z1,z15,z8,z4,z5,z90,z6]),(0,[z1,z109,z2,z8,z4,z5,z6])],[(0,[z1,z14,z2,z8,z4,z102,z5]),(0,[z1,z14,z2,z8,z4,z103,z5]),(0,[z1,z2,z8,z110,z4,z5,z6]),(0,[z1,z111,z2,z8,z4,z5,z6])],[(1,[z112,z1,z14,z8,z4,z5]),(0,[z113,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z114,z4,z5,z10]),(0,[z1,z115,z2,z8,z4,z5,z6])],[(0,[z116,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z53,z8,z4,z5,z10]),(1,[z117,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z69,z4,z5,z6]),(0,[z1,z2,z8,z4,z118,z5,z6]),(0,[z1,z46,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z119,z4,z78,z6])],[(0,[z89,z1,z61,z8,z4,z5,z6]),(0,[z120,z1,z2,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z5,z30])],[(0,[z112,z2,z53,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z121,z6])],[(0,[z1,z2,z8,z4,z5,z10,z45]),(0,[z1,z2,z25,z8,z85,z4,z5])],[(0,[z1,z2,z8,z4,z5,z122,z6]),(0,[z89,z123,z2,z8,z4,z5,z6]),(0,[z1,z15,z2,z8,z4,z5,z6]),(0,[z124,z1,z2,z8,z4,z5,z6]),(1,[z1,z109,z2,z8,z4,z5]),(0,[z1,z2,z125,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z126,z127,z6])],[(0,[z1,z128,z2,z8,z4,z5,z22]),(0,[z1,z14,z8,z4,z5,z6,z56]),(0,[z1,z2,z8,z4,z5,z129,z6])],[],[(0,[z1,z2,z8,z4,z5,z130,z6]),(0,[z1,z2,z8,z4,z131,z5,z45]),(0,[z1,z2,z8,z132,z4,z5,z6])],[(0,[z1,z16,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z6,z133])]],
   [[(0,[z1,z2,z8,z4,z5,z134,z6]),(0,[z1,z61,z2,z69,z4,z5,z6]),(0,[z1,z135,z51,z8,z4,z5,z6]),(0,[z1,z50,z2,z8,z119,z5,z6])],[(0,[z136,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z102,z5]),(0,[z1,z57,z8,z4,z5,z90,z6]),(0,[z1,z57,z2,z8,z4,z137,z5]),(0,[z1,z2,z25,z8,z4,z103,z5]),(0,[z1,z16,z138,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z6,z139]),(0,[z1,z14,z2,z8,z4,z5,z10]),(0,[z1,z140,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z59]),(1,[z1,z141,z8,z4,z5,z6]),(0,[z1,z2,z8,z85,z4,z5,z101])],[(0,[z142,z1,z2,z8,z4,z5,z6])],[(0,[z1,z57,z2,z53,z8,z4,z5]),(0,[z1,z2,z8,z66,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z143]),(0,[z113,z1,z2,z8,z4,z75,z6]),(0,[z1,z2,z8,z4,z144,z5,z6]),(1,[z1,z145,z2,z8,z4,z5]),(0,[z1,z14,z57,z8,z4,z5,z6]),(1,[z1,z146,z2,z8,z4,z5])],[(0,[z1,z147,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z148,z5,z6])],[(0,[z149,z1,z2,z8,z4,z5,z6]),(0,[z150,z1,z2,z8,z4,z5,z6]),(0,[z151,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z152,z103,z5]),(0,[z1,z153,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z154,z4,z5,z6])],[(0,[z1,z14,z2,z8,z4,z155,z5])],[(0,[z1,z2,z8,z156,z4,z5,z6]),(0,[z157,z1,z2,z8,z4,z5,z10]),(0,[z1,z16,z2,z97,z8,z4,z5])],[(0,[z1,z2,z3,z8,z4,z5,z10]),(0,[z1,z158,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z159,z5,z6])],[(0,[z1,z104,z57,z2,z8,z4,z5])],[(0,[z48,z1,z2,z8,z4,z5,z22]),(0,[z1,z160,z2,z8,z4,z5,z10]),(0,[z1,z14,z2,z97,z8,z4,z5]),(0,[z1,z2,z25,z4,z5,z6,z30])],[(0,[z161,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z162])],[(0,[z163,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z164,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z6,z56]),(0,[z165,z1,z2,z8,z4,z5,z6]),(0,[z1,z166,z16,z2,z8,z4,z5])],[(0,[z167,z1,z2,z8,z4,z5,z6]),(0,[z65,z2,z8,z66,z4,z5,z6]),(0,[z65,z1,z2,z8,z4,z5,z22]),(0,[z1,z51,z2,z8,z4,z5,z6]),(0,[z1,z104,z2,z4,z5,z105,z6]),(0,[z44,z1,z16,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z168,z4,z5,z6]),(0,[z1,z2,z8,z4,z169,z5,z6]),(0,[z2,z8,z4,z5,z10,z6,z22]),(0,[z1,z2,z8,z4,z5,z6,z170])],[(0,[z1,z2,z8,z4,z5,z171,z6]),(0,[z1,z2,z8,z172,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z173,z6]),(0,[z1,z174,z2,z8,z4,z5,z6])],[(0,[z1,z2,z175,z8,z4,z5,z6]),(0,[z1,z135,z160,z8,z4,z5,z6]),(0,[z1,z2,z8,z176,z4,z5,z6])],[(0,[z1,z2,z8,z4,z177,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z143]),(0,[z1,z16,z16,z2,z8,z4,z5])],[(1,[z1,z178,z2,z8,z4,z5]),(0,[z1,z2,z8,z179,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z180,z6]),(0,[z1,z15,z2,z25,z8,z4,z5]),(0,[z1,z2,z25,z8,z4,z5,z181]),(1,[z1,z182,z8,z4,z5,z6])],[(0,[z1,z2,z8,z119,z78,z5,z6])],[(0,[z1,z2,z183,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z184,z6]),(0,[z1,z2,z8,z4,z5,z185,z6]),(0,[z1,z14,z16,z2,z8,z4,z5])],[(0,[z1,z2,z186,z8,z4,z5,z6]),(0,[z1,z16,z15,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z187,z6]),(0,[z1,z2,z8,z4,z103,z5,z10]),(0,[z1,z2,z25,z97,z8,z4,z5]),(0,[z188,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z67])],[(0,[z1,z2,z8,z85,z4,z5,z22]),(0,[z1,z2,z8,z189,z4,z5,z6])],[(0,[z1,z14,z15,z2,z8,z4,z5]),(0,[z1,z2,z190,z8,z4,z5,z6]),(0,[z1,z2,z8,z191,z4,z5,z6]),(0,[z1,z2,z192,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z193,z5,z6]),(0,[z1,z2,z8,z4,z5,z194,z6])],[(1,[z48,z2,z8,z68,z5,z6]),(1,[z1,z2,z8,z4,z5,z195]),(0,[z1,z16,z2,z76,z8,z4,z5])],[(0,[z48,z1,z2,z8,z4,z5,z196]),(0,[z1,z57,z2,z8,z73,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z162])],[(0,[z1,z2,z97,z8,z4,z5,z197]),(0,[z1,z2,z8,z70,z4,z5,z195]),(0,[z157,z1,z16,z2,z8,z4,z5])],[(0,[z65,z1,z2,z8,z4,z5,z198]),(0,[z1,z2,z8,z91,z4,z5,z10]),(0,[z1,z108,z8,z4,z5,z6,z22]),(0,[z1,z14,z2,z76,z8,z4,z5]),(1,[z1,z57,z8,z4,z5,z90]),(0,[z1,z16,z2,z8,z4,z131,z5])],[]],
   [[],[(0,[z199,z1,z2,z8,z4,z5,z6]),(0,[z49,z1,z2,z8,z91,z5,z6]),(0,[z1,z14,z2,z8,z4,z131,z5])],[(0,[z200,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z201,z6]),(0,[z1,z2,z8,z4,z202,z5,z6]),(0,[z1,z2,z8,z4,z5,z203,z6]),(0,[z204,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z25,z8,z8,z4,z5])],[(0,[z205,z1,z2,z8,z4,z5,z6])],[(0,[z89,z1,z57,z2,z8,z4,z5])],[(0,[z206,z1,z2,z8,z4,z5,z6]),(0,[z207,z1,z2,z8,z4,z5,z6])],[(0,[z1,z135,z2,z8,z119,z4,z6]),(0,[z1,z2,z8,z4,z5,z208,z6])],[(1,[z2,z8,z4,z5,z10,z22]),(0,[z1,z51,z2,z25,z8,z4,z5]),(0,[z1,z57,z2,z8,z4,z5,z105]),(0,[z1,z16,z2,z8,z4,z5,z127]),(0,[z1,z2,z8,z4,z5,z209,z6])],[(0,[z1,z2,z8,z4,z5,z210,z6]),(0,[z1,z2,z8,z4,z5,z22,z22]),(0,[z1,z2,z211,z8,z4,z5,z6]),(0,[z167,z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z212,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z213,z6]),(0,[z65,z0,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z76,z8,z4,z5]),(0,[z1,z2,z8,z4,z214,z5,z6])],[(0,[z1,z14,z2,z8,z4,z5,z127])],[(1,[z1,z108,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z215]),(0,[z1,z2,z8,z4,z5,z101,z6])],[(0,[z1,z2,z8,z4,z5,z216,z6]),(0,[z1,z2,z25,z8,z4,z131,z5])],[(0,[z1,z178,z2,z53,z8,z4,z5]),(0,[z1,z2,z8,z4,z34,z5,z10]),(0,[z1,z2,z97,z8,z4,z5,z217]),(0,[z1,z2,z8,z218,z4,z5,z6])],[(0,[z1,z146,z2,z8,z4,z5,z6])]],
   [[(0,[z65,z1,z2,z8,z4,z219,z6])],[(0,[z220,z1,z2,z8,z4,z5,z6])],[(1,[z1,z221,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z222]),(0,[z1,z14,z2,z8,z4,z223,z5])],[(0,[z1,z2,z224,z8,z4,z5,z6]),(0,[z225,z1,z2,z8,z4,z5,z10]),(0,[z1,z14,z2,z8,z4,z5,z90]),(0,[z1,z2,z192,z25,z8,z4,z5]),(0,[z1,z182,z2,z8,z4,z5,z6]),(0,[z1,z27,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z5,z226]),(0,[z1,z2,z8,z4,z227,z5,z6]),(0,[z1,z228,z57,z2,z8,z4,z5])],[(0,[z112,z1,z14,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z229,z5,z6]),(0,[z1,z2,z8,z4,z230,z5,z6])],[(0,[z1,z2,z8,z4,z231,z5,z6]),(0,[z1,z2,z8,z4,z232,z5,z6])],[(0,[z233,z1,z2,z8,z4,z5,z234]),(0,[z233,z1,z104,z2,z8,z4,z6])],[(0,[z1,z2,z8,z235,z4,z5,z6]),(0,[z1,z2,z8,z4,z236,z5,z6])],[(0,[z1,z237,z2,z8,z4,z5,z6]),(0,[z1,z57,z57,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z238,z6]),(0,[z1,z239,z2,z8,z4,z5,z6]),(1,[z1,z160,z8,z70,z5,z6]),(0,[z1,z2,z8,z4,z240,z5,z6])],[(1,[z1,z241,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z105,z10]),(0,[z1,z8,z69,z4,z5,z90,z6])],[(0,[z1,z57,z51,z2,z8,z4,z5]),(0,[z1,z14,z2,z8,z242,z4,z5]),(0,[z1,z2,z8,z243,z4,z5,z6])],[(0,[z0,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z60,z6]),(0,[z1,z244,z2,z8,z4,z5,z6])],[(0,[z44,z1,z2,z8,z4,z5,z10]),(0,[z245,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z246,z6]),(0,[z1,z2,z247,z8,z4,z5,z6])]],
   [[(0,[z1,z16,z2,z8,z4,z248,z5])],[(0,[z249,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z97,z8,z4,z5,z22]),(0,[z1,z250,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z251,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z252])],[(0,[z1,z2,z8,z4,z253,z5,z6]),(0,[z1,z254,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z226]),(0,[z1,z135,z8,z4,z102,z5,z6]),(0,[z1,z2,z8,z255,z4,z5,z6]),(0,[z256,z1,z2,z8,z4,z5,z6])],[],[(0,[z1,z16,z123,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z257,z10]),(0,[z258,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z259,z6])],[(0,[z1,z2,z8,z260,z4,z5,z6]),(0,[z1,z2,z8,z4,z261,z5,z6])],[(1,[z65,z2,z66,z4,z5,z6]),(0,[z1,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z76,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z262,z5,z6])],[(0,[z1,z14,z123,z2,z8,z4,z5]),(0,[z263,z1,z2,z8,z4,z5,z22])],[(0,[z1,z14,z2,z8,z191,z4,z5]),(0,[z1,z2,z72,z8,z4,z5,z105]),(0,[z264,z1,z2,z8,z4,z5,z6]),(0,[z1,z265,z2,z8,z4,z5,z6])],[(0,[z112,z1,z2,z8,z4,z5,z10]),(0,[z1,z93,z14,z2,z8,z4,z5]),(0,[z1,z16,z2,z266,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z267,z6]),(0,[z1,z2,z268,z8,z4,z5,z6]),(0,[z1,z16,z2,z8,z4,z5,z19]),(0,[z1,z14,z2,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z269,z6])],[(1,[z1,z2,z8,z4,z5,z270]),(0,[z1,z271,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z272,z6]),(0,[z1,z27,z2,z25,z8,z4,z5])],[(1,[z1,z273,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z274,z5,z162])],[(0,[z1,z123,z2,z8,z4,z5,z22]),(0,[z96,z1,z2,z8,z4,z5,z6]),(0,[z1,z50,z2,z8,z4,z5,z10]),(0,[z1,z57,z160,z2,z8,z4,z5]),(0,[z1,z14,z2,z8,z4,z5,z19]),(0,[z1,z50,z2,z8,z5,z127,z6]),(0,[z1,z2,z8,z4,z5,z275,z6])],[(0,[z1,z276,z2,z8,z66,z4,z6]),(0,[z1,z2,z8,z4,z277,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z278])]],
   [[(0,[z1,z2,z8,z4,z5,z90,z10]),(0,[z1,z2,z8,z4,z5,z279,z6])],[(0,[z1,z2,z8,z4,z274,z34,z6])],[(0,[z1,z108,z2,z8,z4,z5,z6]),(0,[z1,z280,z2,z8,z4,z5,z6])],[(0,[z1,z2,z281,z8,z4,z5,z6]),(0,[z282,z1,z2,z8,z4,z5,z6])],[(0,[z283,z1,z2,z8,z4,z5,z6]),(0,[z1,z128,z2,z3,z8,z4,z5]),(0,[z113,z1,z2,z8,z4,z5,z6]),(1,[z233,z2,z8,z4,z75,z6]),(0,[z1,z2,z8,z4,z248,z5,z6])],[(0,[z1,z2,z8,z4,z284,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z285]),(1,[z1,z2,z211,z8,z4,z5]),(1,[z1,z2,z72,z8,z4,z5])],[(0,[z1,z2,z8,z286,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z5,z45]),(0,[z1,z2,z8,z4,z5,z287,z6])],[(0,[z1,z288,z61,z2,z8,z4,z5]),(0,[z1,z289,z2,z8,z4,z5,z6]),(0,[z206,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z290])],[(0,[z1,z2,z8,z4,z291,z5,z6])],[(0,[z1,z2,z8,z4,z292,z5,z6]),(0,[z1,z2,z8,z4,z293,z5,z6]),(0,[z1,z14,z2,z8,z69,z4,z5]),(0,[z1,z160,z2,z8,z9,z5,z6]),(0,[z1,z294,z2,z8,z4,z5,z6])],[(0,[z1,z128,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z295,z6]),(0,[z1,z2,z25,z8,z4,z5,z19]),(0,[z249,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z296,z6]),(0,[z1,z2,z8,z4,z297,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z270]),(0,[z157,z1,z2,z8,z103,z5,z6]),(0,[z1,z2,z8,z298,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z10,z10]),(0,[z1,z2,z299,z8,z4,z5,z6])],[(0,[z300,z1,z2,z8,z4,z5,z6])],[(0,[z112,z1,z16,z2,z8,z4,z5]),(0,[z1,z2,z301,z8,z4,z5,z6]),(0,[z1,z2,z8,z302,z4,z5,z6]),(0,[z1,z303,z2,z8,z4,z5,z6])],[(0,[z1,z304,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z129,z105])]],
   [[(0,[z1,z2,z8,z4,z5,z6,z305]),(0,[z1,z2,z8,z4,z131,z5,z10]),(0,[z1,z16,z2,z25,z4,z5,z6])],[],[(0,[z1,z1,z2,z8,z4,z5,z6]),(1,[z199,z1,z2,z8,z5,z6]),(0,[z220,z1,z57,z2,z8,z4,z5]),(0,[z1,z50,z16,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z6,z306]),(0,[z1,z2,z8,z4,z137,z5,z10]),(0,[z1,z16,z2,z8,z119,z4,z5])],[(0,[z1,z2,z307,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z308,z6]),(0,[z1,z2,z8,z309,z4,z5,z6])],[],[(0,[z1,z14,z2,z8,z119,z4,z5]),(0,[z1,z14,z2,z8,z4,z5,z54]),(0,[z1,z2,z8,z4,z310,z274,z5])],[(1,[z1,z311,z2,z8,z4,z5]),(0,[z1,z135,z2,z8,z4,z5,z22]),(0,[z1,z311,z2,z8,z4,z5,z22]),(0,[z96,z1,z2,z25,z8,z4,z5])],[(0,[z96,z1,z14,z2,z8,z4,z5]),(0,[z1,z312,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z313,z5,z6])],[(0,[z48,z1,z2,z8,z4,z5,z6]),(1,[z1,z81,z2,z8,z4,z5])],[(0,[z1,z24,z2,z8,z4,z5,z10]),(0,[z1,z16,z2,z8,z4,z5,z314])],[(0,[z1,z2,z8,z315,z4,z5,z6]),(0,[z1,z316,z2,z8,z4,z5,z6])],[(0,[z65,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z317,z5,z6]),(0,[z1,z2,z8,z318,z4,z5,z6]),(0,[z113,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z319,z5,z6]),(1,[z1,z16,z2,z25,z4,z5]),(0,[z320,z1,z2,z8,z4,z5,z6])],[(0,[z113,z1,z14,z2,z8,z4,z5])],[(0,[z112,z1,z2,z8,z4,z5,z306]),(0,[z1,z2,z8,z4,z274,z5,z10]),(0,[z1,z51,z8,z70,z4,z5,z6]),(0,[z1,z57,z2,z321,z8,z4,z5]),(1,[z1,z35,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z91,z103,z5,z6]),(0,[z1,z2,z8,z322,z4,z5,z6]),(0,[z1,z323,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z310,z5,z6])],[(0,[z324,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z325,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z326]),(1,[z1,z2,z8,z4,z5,z10]),(0,[z1,z2,z25,z8,z119,z4,z5])],[(0,[z1,z2,z8,z4,z5,z10,z285]),(0,[z1,z16,z2,z8,z4,z5,z90]),(0,[z1,z2,z8,z4,z327,z5,z6]),(0,[z1,z2,z328,z8,z4,z5,z6]),(0,[z1,z2,z8,z85,z5,z6,z45])],[(0,[z1,z53,z8,z69,z4,z5,z6]),(0,[z1,z2,z8,z70,z4,z5,z10]),(0,[z1,z329,z2,z8,z4,z5,z6]),(1,[z1,z138,z2,z8,z4,z5]),(0,[z1,z2,z8,z330,z4,z5,z6])],[(0,[z331,z1,z2,z8,z4,z5,z6]),(1,[z49,z2,z8,z91,z5,z6]),(0,[z1,z2,z8,z4,z5,z127,z22]),(0,[z1,z332,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z333,z5,z6]),(0,[z1,z334,z2,z8,z4,z5,z6]),(0,[z1,z335,z2,z8,z4,z5,z6])],[],[(0,[z1,z2,z8,z85,z4,z5,z6])],[(0,[z1,z2,z8,z336,z4,z5,z6]),(0,[z1,z2,z337,z8,z4,z5,z6])],[(0,[z1,z338,z2,z8,z4,z5,z6]),(0,[z339,z1,z2,z8,z4,z5,z6])],[(0,[z1,z340,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z341,z6]),(0,[z1,z2,z25,z8,z4,z5,z127]),(0,[z1,z27,z2,z8,z4,z137,z6]),(0,[z1,z2,z8,z4,z5,z342,z6])],[(1,[z1,z276,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z6,z343]),(0,[z1,z61,z2,z8,z4,z5,z22]),(0,[z344,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z345,z6])],[(1,[z1,z346,z8,z4,z5,z6]),(0,[z1,z77,z16,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z347,z6])],[(0,[z1,z348,z2,z8,z4,z5,z6])],[(0,[z89,z1,z2,z8,z4,z5,z270])],[(0,[z349,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z29,z22]),(0,[z350,z1,z2,z8,z4,z5,z6]),(0,[z1,z24,z16,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z351,z6]),(0,[z1,z2,z8,z4,z352,z5,z6])]],
   [[(1,[z113,z2,z8,z4,z34,z6]),(1,[z1,z2,z8,z85,z5,z45])],[(0,[z1,z2,z8,z4,z5,z197,z6]),(0,[z1,z135,z8,z4,z9,z5,z6])],[(0,[z1,z311,z2,z8,z4,z5,z6]),(0,[z1,z353,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z90])],[(0,[z48,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z68,z5,z22]),(0,[z49,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z354,z22])],[(0,[z48,z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z102,z5,z22]),(0,[z1,z2,z355,z8,z4,z5,z6]),(0,[z1,z2,z25,z356,z8,z4,z5])],[(0,[z113,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z357,z5,z6]),(0,[z1,z2,z8,z4,z5,z358,z6])],[(0,[z65,z1,z2,z25,z8,z4,z5]),(1,[z1,z16,z2,z8,z4,z5])],[],[(0,[z1,z2,z8,z359,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z360,z6]),(0,[z1,z57,z2,z8,z4,z5,z56]),(0,[z1,z2,z8,z361,z4,z5,z6]),(1,[z1,z16,z266,z8,z4,z5])],[(0,[z1,z362,z2,z8,z4,z5,z127]),(0,[z363,z1,z2,z8,z4,z5,z6])],[(0,[z1,z104,z2,z8,z4,z5,z10])],[(0,[z1,z364,z2,z8,z4,z5,z6])],[(0,[z1,z14,z2,z8,z4,z5,z341]),(0,[z1,z365,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z366]),(0,[z1,z46,z2,z8,z4,z5,z10]),(0,[z1,z367,z2,z8,z4,z9,z6])],[(1,[z1,z128,z2,z8,z4,z5])],[(0,[z89,z1,z14,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z34,z5]),(0,[z1,z2,z321,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z6,z368])]],
   [[(0,[z1,z2,z369,z8,z4,z5,z10])],[],[(1,[z1,z2,z8,z370,z5,z6]),(0,[z1,z276,z2,z8,z4,z5,z6]),(0,[z1,z371,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z372,z6]),(1,[z1,z16,z2,z4,z5,z29]),(0,[z1,z2,z8,z4,z5,z373,z6]),(0,[z1,z2,z8,z4,z5,z374,z6])],[(0,[z1,z57,z273,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z375,z5,z6])],[(0,[z1,z2,z8,z4,z376,z5,z6]),(2,[z1,z43,z8,z4,z5]),(0,[z1,z2,z8,z377,z4,z5,z6]),(0,[z1,z378,z2,z8,z4,z5,z6])],[(0,[z1,z57,z2,z8,z4,z5,z29]),(1,[z1,z2,z8,z119,z78,z6])],[(1,[z1,z2,z8,z4,z5,z306]),(0,[z1,z2,z8,z4,z5,z379,z6]),(0,[z1,z16,z2,z8,z4,z5,z101])],[(0,[z1,z2,z380,z8,z4,z5,z6]),(1,[z1,z51,z8,z4,z19,z6]),(0,[z1,z14,z365,z2,z8,z4,z5]),(0,[z1,z141,z8,z4,z5,z127,z6])],[(0,[z233,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z381,z22]),(0,[z1,z16,z2,z8,z69,z4,z5]),(0,[z1,z382,z16,z2,z8,z4,z5])],[(0,[z1,z14,z2,z8,z4,z5,z101]),(0,[z1,z2,z8,z4,z5,z29,z6]),(0,[z1,z383,z2,z8,z4,z5,z6])],[(0,[z0,z1,z2,z8,z4,z5,z6]),(0,[z384,z1,z2,z8,z4,z5,z6]),(1,[z44,z1,z2,z8,z5,z101])],[(0,[z1,z2,z8,z4,z5,z385,z6])],[(0,[z1,z2,z8,z386,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z387,z6]),(0,[z1,z145,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z388,z5,z6])],[(0,[z49,z1,z2,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z68,z5]),(0,[z1,z104,z16,z2,z8,z4,z5]),(0,[z1,z389,z2,z8,z4,z5,z6])],[(0,[z117,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z390,z4,z5,z6]),(0,[z1,z2,z97,z8,z4,z5,z6]),(0,[z1,z2,z8,z391,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z95,z5,z10])],[],[(0,[z392,z1,z2,z8,z4,z5,z6]),(0,[z1,z393,z2,z8,z4,z5,z6])],[(0,[z1,z2,z394,z8,z4,z5,z6]),(0,[z1,z135,z2,z8,z4,z19,z6]),(0,[z1,z2,z8,z4,z5,z395,z6]),(0,[z1,z2,z396,z8,z4,z5,z6])],[(0,[z89,z1,z2,z8,z4,z5,z10]),(0,[z1,z57,z2,z8,z85,z4,z5]),(0,[z1,z397,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z398,z4,z5,z6]),(1,[z1,z2,z8,z4,z227,z5]),(0,[z1,z2,z25,z8,z110,z4,z5]),(0,[z1,z399,z2,z8,z4,z5,z6])],[(0,[z263,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z53,z8,z4,z5,z22]),(1,[z1,z2,z8,z4,z210,z6]),(1,[z1,z2,z369,z8,z4,z5]),(0,[z48,z2,z8,z4,z68,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z101]),(0,[z1,z16,z43,z2,z8,z4,z5]),(0,[z1,z16,z2,z8,z4,z5,z54])],[(0,[z1,z346,z8,z66,z4,z5,z6]),(0,[z233,z1,z2,z8,z4,z75,z6]),(0,[z1,z2,z8,z4,z400,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z401]),(0,[z1,z2,z8,z4,z402,z102,z5]),(0,[z1,z27,z57,z2,z8,z4,z5])],[(0,[z1,z61,z15,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z69,z4,z5]),(0,[z1,z2,z8,z4,z403,z5,z6])],[(0,[z404,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z405,z4,z5,z6])],[(0,[z1,z2,z8,z406,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z407])],[(0,[z1,z2,z8,z4,z219,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z408]),(0,[z1,z15,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z409,z5,z6]),(0,[z1,z57,z2,z8,z4,z102,z5]),(0,[z1,z57,z2,z8,z4,z103,z5])],[(0,[z1,z123,z2,z8,z4,z5,z6]),(0,[z65,z1,z2,z8,z410,z5,z6]),(0,[z1,z411,z2,z8,z4,z5,z19]),(0,[z1,z371,z14,z2,z8,z4,z5])],[(0,[z1,z412,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z413,z4,z5,z6]),(0,[z1,z2,z8,z414,z4,z5,z6]),(0,[z1,z2,z8,z415,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z416]),(0,[z1,z16,z2,z8,z4,z5,z75]),(0,[z1,z16,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z155,z5,z6]),(0,[z1,z239,z57,z2,z8,z4,z5])],[(1,[z1,z2,z8,z4,z5,z343])]],
   [[(0,[z1,z2,z8,z4,z370,z5,z6]),(0,[z1,z2,z8,z417,z4,z5,z6])],[(0,[z1,z14,z2,z8,z4,z5,z75]),(0,[z1,z14,z2,z8,z4,z5,z22]),(1,[z1,z2,z8,z4,z5,z418]),(0,[z1,z2,z8,z4,z419,z5,z6])],[(0,[z1,z2,z8,z68,z103,z5,z6])],[(0,[z1,z2,z8,z85,z4,z137,z5])],[(0,[z0,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z381,z6])],[(0,[z0,z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z420,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z54])],[(1,[z1,z77,z2,z8,z4,z5]),(0,[z1,z14,z2,z355,z8,z4,z5])],[(1,[z1,z183,z8,z4,z5,z6]),(0,[z49,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z421,z8,z4,z5,z6])],[(0,[z89,z1,z16,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z422,z5,z6]),(0,[z157,z1,z2,z8,z4,z5,z22]),(0,[z1,z57,z2,z8,z4,z5,z10]),(0,[z1,z24,z2,z8,z9,z5,z6]),(0,[z1,z2,z8,z4,z5,z423,z6])],[(0,[z1,z2,z424,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z196,z6]),(0,[z117,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z30])],[(0,[z1,z2,z8,z119,z4,z5,z10]),(0,[z157,z1,z2,z8,z73,z5,z6])],[(0,[z1,z2,z8,z4,z75,z105,z6])],[(0,[z1,z2,z25,z8,z4,z5,z75]),(1,[z1,z334,z2,z8,z5,z6]),(0,[z1,z425,z2,z8,z4,z5,z6])],[(0,[z1,z16,z2,z8,z66,z4,z5]),(0,[z1,z426,z2,z8,z4,z5,z6]),(0,[z1,z2,z427,z8,z4,z5,z6])],[(0,[z263,z1,z2,z25,z8,z4,z5])]],
   [[(1,[z1,z2,z8,z4,z5,z60]),(0,[z1,z2,z428,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z10,z54]),(0,[z1,z2,z8,z4,z5,z6,z418]),(0,[z263,z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z429,z5,z6]),(0,[z1,z2,z8,z4,z5,z430,z6])],[(0,[z1,z14,z2,z8,z66,z4,z5]),(1,[z1,z2,z8,z4,z5,z47]),(0,[z1,z2,z8,z4,z5,z234,z6])],[(0,[z1,z2,z8,z4,z431,z5,z6]),(0,[z1,z2,z8,z4,z9,z5,z22]),(0,[z96,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z432,z4,z5,z6]),(0,[z1,z57,z2,z97,z8,z4,z5])],[(0,[z433,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z434,z5,z6]),(0,[z1,z2,z435,z8,z4,z5,z6]),(1,[z1,z27,z2,z8,z4,z131])],[],[(0,[z1,z123,z2,z25,z8,z4,z5]),(0,[z436,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z19,z22]),(0,[z1,z24,z160,z8,z4,z5,z6]),(0,[z1,z16,z2,z8,z4,z9,z5]),(0,[z1,z135,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z437,z4,z5,z6]),(0,[z1,z2,z8,z85,z4,z5,z45])],[(0,[z1,z2,z8,z4,z5,z6,z438])],[(0,[z48,z1,z2,z76,z8,z5,z6]),(0,[z1,z2,z8,z4,z103,z5,z22]),(0,[z439,z1,z2,z8,z4,z5,z6])],[(0,[z1,z14,z2,z8,z4,z9,z5])],[(0,[z1,z367,z2,z8,z4,z5,z6]),(0,[z1,z2,z440,z8,z4,z5,z6])],[(0,[z65,z1,z14,z2,z8,z4,z5]),(0,[z1,z160,z2,z8,z70,z5,z6]),(0,[z1,z57,z2,z8,z4,z441,z5])],[(0,[z1,z2,z8,z442,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z443,z6])],[(0,[z1,z2,z444,z8,z4,z5,z6]),(0,[z445,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z25,z8,z66,z4,z5]),(0,[z1,z2,z8,z446,z4,z5,z6]),(0,[z1,z2,z8,z91,z4,z5,z22]),(0,[z1,z2,z8,z4,z447,z5,z6])],[(0,[z1,z448,z2,z8,z4,z5,z6])],[(0,[z1,z449,z2,z8,z4,z5,z6]),(0,[z1,z2,z450,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z253,z5])]],
   [[(0,[z1,z2,z8,z8,z4,z5,z6]),(0,[z1,z57,z15,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z6,z451]),(0,[z1,z452,z2,z8,z4,z5,z6])],[(0,[z453,z1,z2,z8,z4,z5,z6]),(0,[z165,z1,z16,z2,z8,z4,z5])],[(0,[z1,z46,z123,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z127,z6])],[(0,[z1,z2,z25,z8,z4,z9,z5]),(0,[z1,z57,z2,z76,z8,z4,z5])],[(0,[z112,z1,z97,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z45]),(0,[z1,z2,z8,z4,z454,z5,z6])],[(1,[z1,z2,z8,z455,z5,z6]),(0,[z1,z16,z2,z4,z5,z29,z6]),(0,[z456,z1,z2,z8,z4,z5,z6]),(0,[z44,z1,z2,z8,z4,z5,z101])],[(0,[z1,z57,z2,z8,z4,z131,z5]),(0,[z1,z2,z8,z4,z5,z457,z6]),(0,[z1,z2,z8,z4,z5,z458,z6])],[(0,[z1,z2,z459,z8,z4,z5,z6]),(0,[z1,z160,z8,z4,z5,z19,z6]),(0,[z1,z2,z8,z4,z5,z314,z6]),(0,[z1,z2,z8,z4,z5,z460,z6])],[(0,[z65,z1,z83,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z461,z5,z6]),(0,[z1,z61,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z75,z22]),(0,[z1,z2,z8,z73,z4,z5,z10])],[(0,[z1,z2,z8,z4,z5,z6,z23]),(0,[z1,z2,z8,z4,z5,z462,z6]),(0,[z1,z2,z8,z4,z5,z463,z6]),(0,[z1,z464,z2,z8,z4,z5,z6])],[(0,[z1,z16,z266,z8,z4,z5,z6])],[(0,[z1,z2,z465,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z466]),(0,[z1,z467,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z78,z5,z10]),(0,[z1,z2,z8,z4,z9,z5,z6]),(0,[z1,z57,z2,z8,z413,z4,z5])],[(0,[z48,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z10,z468]),(0,[z1,z14,z15,z8,z4,z5,z6]),(0,[z1,z135,z2,z25,z8,z4,z5])],[(0,[z112,z1,z2,z8,z4,z5,z469]),(1,[z1,z2,z8,z4,z5,z408]),(0,[z1,z135,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z470,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z19,z6]),(0,[z439,z1,z2,z25,z8,z4,z5])],[(0,[z65,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z68,z5,z6]),(1,[z1,z8,z4,z5,z354,z22]),(0,[z1,z2,z8,z4,z5,z354,z6]),(0,[z1,z57,z2,z8,z4,z5,z127]),(0,[z1,z471,z2,z8,z4,z5,z6])],[(1,[z1,z2,z472,z8,z4,z5]),(0,[z1,z2,z8,z4,z102,z5,z6])],[(0,[z1,z2,z473,z8,z4,z5,z6])],[],[(0,[z1,z2,z8,z4,z5,z59,z6]),(0,[z1,z2,z8,z4,z5,z6,z54])],[(0,[z113,z1,z2,z8,z4,z34,z6]),(0,[z474,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z475,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z476,z22])],[(0,[z1,z2,z8,z73,z68,z5,z6]),(1,[z1,z2,z356,z8,z4,z5]),(0,[z1,z2,z450,z25,z8,z4,z5])],[(0,[z1,z2,z8,z477,z4,z5,z6]),(0,[z1,z50,z2,z8,z4,z127,z6])],[(1,[z1,z2,z8,z4,z5,z478]),(0,[z113,z2,z8,z4,z34,z5,z6]),(0,[z1,z2,z8,z4,z5,z105,z22]),(0,[z1,z2,z8,z69,z4,z5,z10]),(0,[z1,z2,z8,z4,z479,z5,z6]),(0,[z1,z100,z2,z8,z4,z5,z6])],[],[(0,[z1,z14,z2,z8,z70,z4,z5])],[(0,[z1,z2,z8,z4,z480,z5,z6]),(0,[z44,z1,z2,z8,z4,z5,z22]),(1,[z96,z2,z8,z4,z5,z10]),(1,[z1,z61,z69,z4,z5,z6]),(0,[z1,z2,z321,z8,z4,z5,z6])],[(0,[z1,z2,z73,z4,z103,z5,z6]),(0,[z1,z2,z321,z8,z4,z274,z6])],[(0,[z1,z2,z8,z455,z5,z19,z6]),(0,[z344,z1,z57,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z321,z8,z4,z105,z6])],[(0,[z49,z1,z2,z8,z4,z5,z17]),(0,[z1,z50,z24,z2,z8,z5,z6]),(0,[z1,z2,z8,z4,z5,z481,z6])],[(0,[z1,z2,z8,z4,z482,z5,z6]),(0,[z1,z61,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z483])],[(0,[z1,z61,z14,z2,z8,z4,z5])],[(0,[z1,z484,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z75,z6])],[(0,[z1,z2,z8,z4,z485,z5,z6]),(0,[z1,z24,z51,z8,z4,z5,z6]),(0,[z1,z2,z8,z70,z4,z5,z418]),(0,[z1,z311,z57,z2,z8,z4,z5]),(0,[z1,z2,z486,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z487,z6])],[(0,[z1,z2,z8,z66,z4,z5,z10]),(0,[z233,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z144,z5,z10]),(0,[z1,z81,z2,z8,z4,z5,z6]),(0,[z488,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z489,z5,z6])],[(0,[z1,z2,z490,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z10,z238]),(0,[z1,z77,z61,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z491]),(0,[z1,z2,z8,z4,z131,z5,z101])],[(0,[z1,z2,z8,z4,z492,z5,z6]),(0,[z1,z2,z8,z493,z4,z5,z6]),(0,[z1,z2,z8,z4,z441,z5,z6])],[(0,[z1,z2,z8,z4,z5,z92,z6]),(1,[z1,z2,z8,z4,z5,z494]),(0,[z1,z2,z8,z4,z5,z495,z6]),(0,[z496,z1,z2,z8,z4,z5,z6])],[(0,[z497,z1,z2,z8,z4,z5,z6]),(0,[z49,z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z22,z139])],[(0,[z1,z2,z3,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z6,z498])],[(0,[z1,z50,z2,z8,z4,z5,z22]),(1,[z1,z2,z8,z4,z5,z197])],[(0,[z1,z57,z123,z2,z8,z4,z5]),(0,[z1,z16,z2,z8,z91,z4,z5]),(0,[z1,z160,z2,z8,z4,z5,z22])],[(0,[z1,z2,z8,z4,z5,z90,z22]),(0,[z1,z2,z8,z4,z5,z499,z6]),(0,[z1,z364,z57,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z500,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z501,z6]),(0,[z1,z2,z25,z8,z4,z5,z22]),(0,[z1,z2,z8,z502,z4,z5,z6]),(0,[z1,z51,z2,z8,z4,z102,z6]),(0,[z1,z2,z503,z8,z4,z5,z6])],[(0,[z1,z14,z2,z8,z91,z4,z5]),(0,[z1,z2,z8,z4,z5,z504,z6]),(0,[z1,z57,z2,z2,z8,z4,z5])],[(0,[z505,z1,z2,z8,z4,z5,z6]),(0,[z506,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z234]),(0,[z1,z51,z2,z8,z4,z5,z10]),(0,[z507,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z508,z4,z5,z6]),(0,[z1,z16,z2,z8,z4,z274,z5]),(0,[z1,z2,z8,z78,z5,z127,z6])],[(0,[z1,z2,z8,z114,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z468]),(0,[z1,z50,z440,z8,z4,z5,z6]),(1,[z1,z50,z2,z8,z127,z6])],[(0,[z1,z2,z53,z8,z4,z5,z6]),(0,[z1,z509,z2,z8,z4,z5,z6]),(0,[z113,z1,z2,z8,z4,z5,z10]),(0,[z1,z57,z2,z8,z4,z5,z19])],[(0,[z1,z2,z8,z510,z4,z5,z6]),(0,[z511,z1,z2,z8,z4,z5,z6]),(0,[z1,z14,z2,z8,z4,z274,z5])],[(0,[z1,z16,z2,z3,z8,z4,z5]),(0,[z1,z2,z8,z4,z512,z5,z22]),(1,[z1,z2,z25,z4,z5,z30])],[(1,[z1,z2,z8,z4,z5,z469]),(1,[z89,z123,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z56]),(0,[z1,z166,z2,z8,z4,z5,z6])],[],[(0,[z1,z2,z8,z4,z5,z198,z6]),(0,[z1,z14,z2,z3,z8,z4,z5]),(0,[z113,z1,z2,z321,z8,z4,z6]),(0,[z1,z2,z8,z4,z513,z5,z6])],[(0,[z1,z2,z8,z4,z5,z514,z6]),(0,[z1,z2,z8,z4,z5,z515,z6]),(0,[z1,z2,z8,z4,z137,z5,z54])],[(0,[z1,z2,z8,z4,z5,z10,z22])],[(0,[z1,z2,z8,z4,z5,z6,z516]),(0,[z1,z16,z2,z8,z4,z5,z6])],[(0,[z517,z1,z2,z8,z4,z5,z6]),(0,[z518,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z91,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z519]),(0,[z1,z2,z8,z4,z131,z6,z54])],[(1,[z1,z2,z8,z4,z5,z217])],[(0,[z0,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z131,z5,z22]),(0,[z1,z2,z8,z4,z5,z520,z6]),(0,[z1,z14,z2,z8,z4,z5,z6])]],
   [[(0,[z1,z521,z2,z8,z4,z5,z6]),(0,[z233,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z137,z6,z54])],[(0,[z1,z2,z8,z522,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z466]),(0,[z233,z1,z14,z2,z8,z4,z5]),(0,[z1,z61,z2,z97,z4,z5,z6]),(0,[z523,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z524,z4,z5,z6])],[(0,[z49,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z525,z5,z6]),(0,[z1,z2,z8,z4,z137,z5,z22]),(0,[z96,z2,z8,z4,z5,z10,z6]),(0,[z1,z27,z2,z8,z85,z4,z5])],[],[(0,[z1,z2,z526,z8,z4,z5,z6])],[(0,[z1,z2,z25,z3,z8,z4,z5]),(0,[z1,z8,z4,z5,z354,z6,z22]),(0,[z1,z146,z2,z8,z4,z103,z5]),(1,[z1,z2,z8,z4,z310,z5]),(1,[z1,z2,z8,z4,z5,z259])],[(0,[z117,z1,z2,z25,z8,z4,z5]),(0,[z1,z527,z2,z8,z4,z5,z6]),(0,[z157,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z117,z1,z14,z2,z8,z4,z5]),(0,[z1,z288,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z189,z4,z5])],[(0,[z113,z1,z16,z2,z8,z4,z5])],[(0,[z1,z160,z2,z8,z4,z5,z6]),(1,[z1,z43,z2,z8,z4,z5])],[(0,[z263,z1,z57,z2,z8,z4,z5]),(0,[z528,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z12,z8,z66,z4,z6]),(0,[z1,z2,z25,z8,z4,z5,z6])],[(0,[z89,z1,z2,z8,z4,z5,z478]),(0,[z1,z2,z8,z4,z529,z5,z6]),(0,[z1,z57,z2,z8,z119,z4,z5]),(0,[z1,z2,z8,z530,z4,z5,z6]),(0,[z1,z2,z531,z8,z4,z5,z6])],[(0,[z1,z2,z53,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z6,z217]),(0,[z157,z1,z2,z76,z4,z5,z6])],[(0,[z532,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z533,z5,z6]),(0,[z1,z2,z8,z4,z5,z534,z6]),(0,[z1,z128,z16,z2,z8,z4,z5])],[(0,[z535,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z536,z6]),(0,[z1,z2,z8,z4,z5,z101,z10]),(0,[z1,z2,z8,z73,z4,z5,z494])]],
   [[(0,[z65,z1,z221,z8,z4,z5,z6]),(0,[z1,z537,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z34,z5,z22]),(1,[z1,z14,z8,z4,z5,z56]),(0,[z1,z2,z8,z4,z538,z5,z6])],[(0,[z1,z2,z2,z8,z4,z5,z6]),(0,[z199,z1,z2,z8,z66,z5,z6]),(0,[z1,z539,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z152,z5,z6]),(1,[z1,z2,z8,z4,z5,z129])],[(0,[z65,z1,z2,z8,z4,z5,z226]),(0,[z1,z15,z2,z69,z4,z5,z6])],[(0,[z233,z113,z2,z8,z4,z5,z6]),(0,[z1,z14,z2,z8,z73,z4,z5])],[(0,[z540,z1,z2,z8,z4,z5,z6]),(0,[z96,z117,z2,z8,z4,z5,z6]),(0,[z1,z2,z472,z8,z69,z4,z5])],[(0,[z1,z2,z8,z4,z103,z5,z6]),(0,[z1,z16,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z45,z54]),(0,[z1,z2,z8,z4,z541,z5,z6])],[(0,[z1,z2,z8,z410,z4,z5,z6]),(0,[z1,z27,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z542,z5,z6]),(1,[z1,z2,z355,z8,z4,z5])],[(0,[z1,z2,z543,z8,z4,z5,z6]),(0,[z1,z2,z8,z85,z4,z5,z10]),(0,[z1,z57,z2,z8,z212,z4,z5]),(1,[z1,z440,z8,z4,z5,z6])],[(1,[z112,z53,z8,z4,z5,z6]),(0,[z233,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z544,z5,z6]),(0,[z1,z2,z8,z4,z5,z22,z326]),(0,[z1,z14,z2,z25,z8,z4,z5])],[(0,[z545,z1,z2,z8,z4,z5,z6]),(0,[z1,z24,z2,z8,z70,z5,z6]),(0,[z1,z2,z8,z84,z4,z9,z6]),(0,[z1,z2,z8,z546,z4,z5,z6]),(0,[z1,z14,z14,z2,z8,z4,z5]),(0,[z1,z547,z2,z8,z4,z5,z6]),(0,[z1,z141,z2,z8,z4,z5,z6]),(0,[z1,z2,z548,z8,z4,z5,z6])],[(0,[z1,z8,z4,z9,z5,z19,z6]),(0,[z1,z362,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z91,z4,z5,z6]),(0,[z1,z549,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z494,z6])],[(0,[z1,z16,z2,z8,z70,z4,z5]),(0,[z1,z57,z2,z8,z4,z5,z90])],[(0,[z1,z2,z8,z550,z4,z5,z6])],[(0,[z117,z1,z57,z2,z8,z4,z5]),(0,[z1,z51,z2,z8,z119,z4,z6]),(0,[z1,z2,z52,z8,z4,z5,z6])],[(0,[z89,z1,z97,z8,z4,z5,z6]),(0,[z157,z1,z2,z25,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z4,z5,z6,z22]),(0,[z1,z2,z551,z8,z4,z5,z6]),(0,[z157,z1,z14,z2,z8,z4,z5]),(0,[z1,z288,z2,z25,z8,z4,z5]),(0,[z1,z16,z2,z8,z4,z78,z5])],[(1,[z1,z14,z57,z8,z4,z5]),(0,[z1,z288,z14,z2,z8,z4,z5])],[(1,[z1,z2,z8,z4,z5,z107]),(0,[z1,z552,z2,z8,z4,z5,z6]),(0,[z1,z160,z2,z25,z8,z4,z5]),(0,[z1,z50,z160,z2,z8,z5,z6])],[(0,[z553,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z357,z5]),(0,[z1,z14,z2,z8,z4,z78,z5])],[(0,[z89,z112,z2,z8,z4,z5,z6]),(0,[z554,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z25,z8,z4,z5]),(0,[z1,z2,z266,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z555,z6])],[(0,[z1,z135,z50,z2,z8,z4,z6])],[(0,[z1,z241,z2,z8,z66,z4,z5]),(0,[z1,z2,z8,z4,z556,z5,z6])],[(0,[z1,z2,z8,z4,z455,z5,z6]),(0,[z1,z2,z8,z4,z557,z5,z6])],[(0,[z1,z2,z8,z4,z102,z5,z67]),(0,[z1,z2,z8,z4,z558,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z559]),(0,[z1,z104,z2,z8,z4,z5,z22]),(0,[z1,z24,z8,z4,z102,z5,z6]),(0,[z1,z135,z57,z2,z8,z4,z5])],[(0,[z112,z1,z53,z8,z4,z5,z6]),(0,[z1,z2,z76,z8,z4,z5,z10])],[(0,[z1,z2,z8,z4,z34,z5,z6]),(0,[z1,z2,z25,z8,z70,z4,z5])],[(0,[z112,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z560,z5,z6]),(0,[z561,z1,z2,z8,z4,z5,z6])],[(0,[z339,z1,z16,z2,z8,z4,z5]),(0,[z562,z1,z2,z8,z4,z5,z6])],[(0,[z49,z1,z2,z76,z8,z5,z6]),(0,[z1,z2,z8,z4,z34,z105,z6])],[(1,[z1,z8,z4,z5,z354,z6]),(0,[z1,z2,z25,z8,z4,z78,z5]),(0,[z1,z16,z2,z8,z4,z5,z30])]],
   [[(0,[z225,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z563])],[(0,[z96,z1,z2,z8,z4,z5,z10])],[(1,[z1,z2,z8,z4,z219,z6]),(0,[z1,z2,z564,z8,z4,z5,z6]),(0,[z1,z14,z2,z8,z4,z5,z30])],[],[(0,[z1,z565,z2,z8,z4,z5,z6]),(0,[z1,z566,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z567,z5,z6]),(0,[z1,z2,z8,z4,z5,z5,z6]),(0,[z1,z2,z8,z4,z5,z476,z6]),(0,[z1,z2,z568,z8,z4,z5,z6]),(0,[z1,z27,z2,z8,z4,z131,z5])],[(0,[z1,z2,z8,z4,z5,z569,z6])],[],[(0,[z1,z2,z8,z4,z5,z105,z6]),(0,[z1,z16,z2,z8,z4,z137,z5]),(0,[z1,z2,z570,z8,z4,z5,z6])],[(0,[z1,z571,z2,z8,z4,z5,z6])],[(0,[z572,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z573,z6])],[(0,[z1,z16,z2,z53,z8,z4,z5]),(1,[z1,z135,z8,z4,z102,z6]),(1,[z1,z365,z2,z8,z4,z5]),(0,[z1,z14,z2,z8,z4,z137,z5]),(0,[z574,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z575]),(0,[z44,z1,z2,z8,z4,z5,z6])],[(0,[z1,z138,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z576,z4,z5,z6]),(0,[z1,z61,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z577,z6]),(0,[z1,z2,z578,z8,z4,z5,z6])],[(0,[z1,z14,z2,z53,z8,z4,z5]),(2,[z1,z108,z8,z4,z5])],[(0,[z1,z579,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z580,z5,z6])]],
   [[(0,[z0,z2,z3,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z5,z101]),(0,[z1,z27,z2,z8,z4,z131,z6])],[(0,[z1,z484,z14,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z257,z6]),(0,[z157,z49,z1,z2,z8,z5,z6]),(0,[z1,z2,z8,z581,z4,z5,z6]),(0,[z1,z2,z582,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z69,z4,z5]),(0,[z1,z2,z8,z4,z583,z5,z6])],[(0,[z89,z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z168,z66,z5,z6]),(0,[z584,z1,z2,z8,z4,z5,z6]),(0,[z585,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z586])],[(0,[z112,z1,z123,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z10,z587]),(0,[z588,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z274,z5])],[(0,[z1,z589,z2,z8,z4,z5,z22]),(0,[z96,z1,z16,z2,z8,z4,z5]),(0,[z1,z1,z2,z8,z4,z5,z10])],[(0,[z1,z2,z8,z4,z590,z5,z6]),(0,[z1,z2,z490,z8,z4,z5,z6]),(0,[z561,z1,z14,z2,z8,z4,z5]),(0,[z1,z2,z8,z119,z4,z127,z6])],[(0,[z112,z1,z2,z8,z4,z5,z6]),(0,[z1,z591,z2,z8,z4,z5,z6]),(0,[z592,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z593])],[],[(0,[z1,z2,z8,z4,z594,z5,z6])],[(0,[z1,z2,z8,z595,z4,z5,z22]),(0,[z1,z596,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z575])],[(0,[z1,z597,z2,z8,z4,z5,z6]),(0,[z1,z50,z2,z8,z4,z5,z6]),(0,[z1,z598,z2,z8,z4,z5,z6])],[(0,[z123,z2,z53,z8,z4,z5,z6]),(0,[z599,z1,z2,z8,z4,z5,z6])],[(0,[z48,z1,z2,z8,z4,z5,z10]),(0,[z1,z24,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z90,z6]),(0,[z1,z2,z8,z4,z5,z6,z600])],[(0,[z1,z2,z12,z8,z4,z5,z6]),(0,[z48,z157,z1,z2,z8,z5,z6]),(0,[z1,z8,z70,z4,z9,z5,z6]),(0,[z1,z2,z76,z73,z4,z5,z6])],[(0,[z601,z1,z2,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z5,z54]),(0,[z1,z43,z2,z8,z4,z5,z6])]],
   [[(0,[z65,z1,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z602,z5,z6]),(1,[z1,z288,z2,z8,z4,z5]),(1,[z1,z2,z8,z4,z137,z54])],[(0,[z1,z2,z8,z603,z4,z5,z6]),(0,[z1,z2,z8,z4,z274,z5,z22])],[(0,[z1,z604,z2,z8,z4,z5,z6])],[(0,[z1,z8,z70,z4,z102,z5,z6]),(0,[z1,z16,z2,z8,z73,z4,z5])],[(0,[z1,z605,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z512,z5,z6]),(0,[z1,z57,z2,z8,z4,z556,z5]),(0,[z44,z1,z2,z25,z8,z4,z5])],[(1,[z1,z46,z2,z8,z4,z5]),(0,[z1,z2,z8,z84,z4,z5,z6]),(0,[z44,z1,z14,z2,z8,z4,z5]),(1,[z1,z2,z321,z4,z274,z6])],[(0,[z1,z2,z8,z70,z4,z5,z22]),(0,[z1,z160,z2,z8,z78,z5,z6])],[(0,[z49,z2,z8,z91,z4,z5,z6]),(0,[z1,z57,z2,z8,z4,z5,z75]),(0,[z1,z57,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z606,z4,z5,z6])],[(1,[z1,z108,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z10,z6])],[(0,[z1,z2,z8,z73,z91,z5,z6]),(0,[z1,z2,z8,z119,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z6,z37]),(0,[z1,z109,z2,z8,z4,z9,z5]),(0,[z1,z16,z43,z8,z4,z5,z6])],[(0,[z48,z1,z2,z8,z68,z5,z6]),(0,[z157,z1,z2,z4,z103,z5,z6])],[(0,[z1,z2,z607,z8,z4,z5,z6]),(0,[z1,z2,z8,z608,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z126,z6])],[(0,[z609,z1,z2,z8,z4,z5,z6]),(0,[z1,z411,z2,z8,z4,z5,z6]),(0,[z1,z610,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z131,z5,z6])],[(0,[z1,z2,z611,z8,z4,z5,z6]),(1,[z1,z2,z76,z73,z5,z6]),(0,[z1,z2,z8,z4,z612,z5,z6])],[(0,[z1,z2,z8,z4,z274,z75,z6]),(0,[z1,z16,z2,z8,z4,z5,z105])]],
   [[(0,[z112,z1,z2,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z137,z5,z6])],[(0,[z48,z1,z16,z2,z8,z4,z5]),(0,[z113,z1,z2,z8,z4,z5,z408]),(1,[z1,z2,z490,z8,z4,z5])],[(0,[z1,z14,z2,z8,z4,z5,z105]),(0,[z1,z2,z25,z8,z73,z4,z5])],[(1,[z1,z2,z8,z4,z5,z198]),(0,[z1,z2,z8,z4,z613,z5,z6]),(0,[z1,z2,z614,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z469,z6]),(0,[z65,z1,z16,z2,z8,z4,z5]),(1,[z1,z2,z8,z4,z5,z196]),(0,[z1,z273,z2,z8,z4,z5,z6]),(0,[z1,z615,z2,z8,z4,z5,z6]),(0,[z1,z50,z2,z25,z8,z4,z5])],[(0,[z1,z77,z2,z8,z4,z5,z6]),(0,[z1,z50,z14,z2,z8,z4,z5]),(0,[z1,z616,z2,z8,z4,z5,z6])],[(0,[z617,z1,z2,z8,z4,z5,z6]),(0,[z1,z618,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z619,z6]),(0,[z1,z57,z2,z8,z66,z4,z5]),(0,[z1,z24,z8,z4,z9,z5,z6])],[(0,[z1,z24,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z620,z6]),(0,[z621,z1,z2,z8,z4,z5,z6]),(0,[z44,z1,z2,z8,z85,z5,z6])],[(0,[z1,z622,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z587]),(0,[z1,z15,z97,z8,z4,z5,z6]),(0,[z623,z1,z2,z8,z4,z5,z6])],[(0,[z1,z624,z2,z8,z4,z5,z6]),(0,[z1,z50,z2,z8,z4,z5,z63]),(0,[z625,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z33,z8,z4,z5]),(0,[z1,z2,z8,z242,z4,z5,z6]),(0,[z626,z1,z2,z8,z4,z5,z6])],[(0,[z1,z627,z2,z8,z4,z5,z6]),(0,[z532,z1,z2,z8,z4,z5,z6]),(0,[z233,z1,z2,z8,z4,z5,z143]),(0,[z1,z57,z2,z8,z4,z5,z628]),(0,[z1,z104,z2,z321,z4,z5,z6]),(0,[z1,z335,z16,z2,z8,z4,z5])],[(0,[z1,z629,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z630,z6])],[(0,[z1,z57,z2,z8,z4,z9,z5]),(0,[z1,z2,z631,z8,z4,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z105])],[(1,[z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z632,z5,z6]),(0,[z1,z2,z25,z8,z4,z419,z5])]],
   [[(0,[z65,z1,z2,z8,z370,z5,z6]),(0,[z1,z633,z2,z8,z4,z5,z6]),(0,[z1,z16,z57,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z634,z5,z6]),(0,[z1,z2,z8,z4,z357,z5,z19])],[(0,[z1,z123,z8,z69,z4,z5,z6]),(0,[z635,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z636,z5,z6])],[(0,[z1,z2,z637,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z478,z6]),(0,[z1,z16,z51,z2,z8,z4,z5]),(0,[z1,z14,z57,z2,z8,z4,z5]),(0,[z1,z2,z4,z274,z5,z105,z6]),(0,[z1,z2,z356,z8,z4,z5,z6])],[(0,[z1,z183,z8,z66,z4,z5,z6]),(0,[z1,z241,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z638,z5,z6])],[(0,[z1,z2,z8,z639,z4,z5,z6]),(0,[z1,z640,z2,z8,z4,z5,z6])],[(0,[z641,z1,z2,z8,z4,z5,z6]),(1,[z1,z15,z97,z4,z5,z6]),(0,[z1,z14,z51,z2,z8,z4,z5]),(0,[z1,z16,z2,z8,z4,z352,z5]),(0,[z1,z2,z8,z4,z5,z642,z6])],[(0,[z1,z340,z2,z8,z4,z5,z6]),(0,[z44,z1,z2,z8,z4,z137,z5])],[(0,[z1,z2,z33,z8,z66,z4,z5]),(0,[z117,z2,z8,z4,z5,z6,z22]),(1,[z1,z24,z8,z9,z5,z6]),(0,[z643,z1,z2,z8,z4,z5,z6])],[(0,[z233,z1,z2,z8,z4,z34,z6]),(0,[z1,z2,z8,z73,z4,z5,z22])],[(0,[z233,z2,z8,z4,z5,z75,z6]),(0,[z157,z1,z57,z2,z8,z4,z5]),(0,[z1,z50,z2,z8,z4,z78,z6]),(0,[z1,z27,z2,z8,z4,z5,z54])],[(0,[z1,z644,z2,z8,z4,z5,z6])],[(0,[z1,z2,z76,z8,z103,z5,z6])],[(0,[z1,z2,z83,z8,z4,z5,z6]),(0,[z645,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z646,z5,z6]),(0,[z1,z2,z8,z4,z5,z29,z10]),(1,[z1,z2,z8,z4,z402,z5]),(0,[z1,z2,z8,z4,z5,z6,z647])],[(0,[z0,z1,z2,z8,z4,z5,z10]),(0,[z2,z8,z91,z4,z68,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z6]),(0,[z528,z1,z57,z2,z8,z4,z5]),(0,[z1,z648,z2,z8,z4,z5,z6]),(0,[z1,z616,z2,z25,z8,z4,z5])],[(0,[z649,z1,z2,z8,z4,z5,z6]),(0,[z1,z14,z2,z8,z4,z5,z56])]],
   [[(0,[z1,z650,z2,z8,z4,z5,z6]),(0,[z651,z1,z2,z8,z4,z5,z6]),(0,[z1,z145,z2,z8,z4,z5,z10]),(1,[z1,z411,z2,z8,z4,z5]),(0,[z1,z2,z652,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z653,z5,z6])],[(0,[z1,z654,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z68,z5,z10]),(0,[z49,z1,z2,z8,z4,z5,z10]),(0,[z1,z2,z25,z8,z4,z5,z30])],[(0,[z1,z655,z2,z8,z4,z5,z6]),(0,[z1,z2,z97,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z102,z5,z10]),(0,[z1,z2,z8,z4,z5,z6,z656]),(0,[z1,z382,z2,z8,z4,z5,z6]),(1,[z1,z266,z8,z4,z5,z6])],[(0,[z112,z1,z8,z4,z5,z90,z6]),(1,[z1,z2,z8,z4,z5,z504])],[(0,[z89,z1,z53,z8,z4,z5,z6]),(0,[z657,z1,z2,z8,z4,z5,z6]),(0,[z65,z1,z2,z8,z4,z210,z6]),(0,[z113,z1,z104,z2,z8,z4,z6])],[(0,[z1,z16,z160,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z658,z5,z6])],[(0,[z453,z1,z16,z2,z8,z4,z5]),(0,[z1,z659,z2,z8,z4,z5,z6])],[(0,[z1,z221,z2,z8,z4,z5,z6]),(0,[z1,z2,z369,z3,z8,z4,z5]),(0,[z1,z2,z472,z8,z4,z5,z6]),(0,[z1,z104,z2,z8,z4,z5,z6]),(0,[z44,z1,z2,z8,z5,z101,z6])],[(0,[z1,z14,z160,z2,z8,z4,z5]),(0,[z1,z104,z2,z8,z4,z274,z6]),(1,[z1,z2,z25,z8,z4,z5])],[(0,[z1,z2,z8,z69,z4,z5,z22]),(0,[z263,z1,z2,z8,z4,z5,z10]),(0,[z1,z2,z321,z4,z274,z5,z6])],[(0,[z1,z104,z2,z8,z4,z105,z6]),(0,[z1,z2,z25,z8,z4,z137,z5])],[],[(0,[z1,z2,z8,z4,z5,z10,z30])],[(0,[z1,z2,z369,z8,z4,z5,z6]),(0,[z1,z15,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z660,z6]),(0,[z1,z2,z321,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z6,z661]),(0,[z1,z2,z8,z4,z5,z662,z6]),(0,[z1,z16,z2,z8,z4,z5,z45])],[(0,[z112,z1,z61,z8,z4,z5,z6]),(1,[z1,z604,z2,z8,z4,z5]),(1,[z1,z2,z8,z4,z5,z37])],[(0,[z1,z123,z2,z8,z4,z5,z10]),(0,[z49,z1,z2,z8,z68,z5,z6])]],
   [[(0,[z1,z14,z2,z8,z4,z5,z45])],[(0,[z1,z604,z2,z53,z8,z4,z5]),(0,[z1,z2,z8,z663,z4,z5,z6])],[(0,[z1,z2,z8,z664,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z665,z4,z5,z6]),(0,[z0,z1,z16,z2,z8,z4,z5]),(0,[z1,z666,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z152,z5])],[(0,[z1,z2,z8,z4,z5,z259,z127])],[(0,[z49,z1,z16,z2,z8,z4,z5]),(0,[z1,z644,z14,z2,z8,z4,z5]),(1,[z157,z1,z2,z103,z5,z6])],[],[(0,[z233,z1,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z22,z416]),(0,[z1,z2,z8,z4,z5,z667,z6]),(0,[z1,z668,z2,z8,z4,z5,z6])],[(0,[z1,z8,z4,z5,z90,z6,z56])],[(1,[z1,z367,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z195,z6]),(0,[z669,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z652,z25,z8,z4,z5]),(0,[z1,z2,z8,z4,z131,z137,z5])],[(0,[z2,z8,z4,z34,z5,z75,z6]),(0,[z1,z2,z8,z4,z227,z9,z5]),(0,[z1,z51,z2,z8,z4,z19,z6])],[(1,[z1,z2,z8,z168,z5,z6]),(0,[z1,z2,z8,z4,z5,z47,z6]),(0,[z1,z670,z2,z8,z4,z5,z6]),(0,[z1,z671,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z628,z6])],[(0,[z1,z178,z2,z8,z4,z5,z6]),(0,[z1,z672,z2,z8,z4,z5,z6]),(0,[z233,z1,z2,z321,z8,z4,z6]),(0,[z1,z2,z8,z4,z673,z5,z6]),(0,[z1,z2,z25,z8,z4,z5,z45])],[(0,[z117,z1,z2,z8,z4,z5,z10]),(0,[z263,z1,z16,z2,z8,z4,z5]),(0,[z1,z50,z182,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z63])],[(0,[z89,z1,z123,z8,z4,z5,z6]),(0,[z674,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z36,z4,z5,z6])],[(0,[z1,z2,z8,z4,z675,z5,z6]),(0,[z1,z61,z8,z69,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z676,z6]),(0,[z1,z2,z8,z4,z164,z5,z22]),(0,[z1,z677,z2,z8,z4,z5,z6]),(0,[z1,z104,z2,z25,z8,z4,z5]),(0,[z1,z16,z27,z2,z8,z4,z5])],[(0,[z89,z1,z2,z8,z4,z5,z6]),(0,[z678,z1,z2,z8,z4,z5,z6]),(0,[z1,z51,z2,z8,z4,z5,z22]),(0,[z1,z104,z14,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z679,z6]),(0,[z1,z680,z2,z8,z4,z5,z6])],[(0,[z1,z589,z2,z8,z4,z5,z6]),(0,[z1,z97,z8,z69,z4,z5,z6]),(0,[z1,z14,z27,z2,z8,z4,z5]),(0,[z1,z2,z8,z73,z4,z5,z575]),(0,[z1,z2,z8,z4,z5,z681,z6]),(0,[z1,z682,z2,z8,z4,z5,z6]),(0,[z1,z683,z2,z8,z4,z5,z6])],[(0,[z112,z1,z14,z2,z8,z4,z5]),(0,[z684,z1,z2,z8,z4,z5,z6])],[(0,[z685,z1,z2,z8,z4,z5,z6]),(0,[z1,z15,z123,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z181,z6])],[(0,[z1,z2,z8,z686,z4,z5,z6]),(0,[z687,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z211,z8,z69,z4,z5]),(0,[z1,z135,z2,z8,z4,z102,z6]),(0,[z1,z16,z2,z321,z8,z4,z5]),(0,[z1,z2,z369,z25,z8,z4,z5])],[(0,[z1,z57,z2,z8,z91,z4,z5]),(0,[z688,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z595,z4,z5,z6]),(0,[z1,z135,z2,z8,z4,z5,z10]),(0,[z1,z334,z2,z8,z5,z19,z6])],[(0,[z48,z1,z2,z8,z4,z5,z466]),(0,[z1,z2,z8,z4,z689,z5,z6]),(0,[z1,z14,z2,z321,z8,z4,z5])],[],[(1,[z89,z1,z14,z8,z4,z5]),(0,[z1,z311,z123,z2,z8,z4,z5]),(0,[z233,z1,z16,z2,z8,z4,z5]),(0,[z1,z57,z2,z8,z4,z274,z5])],[(0,[z1,z160,z8,z70,z4,z5,z6]),(0,[z1,z2,z8,z4,z690,z5,z6]),(0,[z691,z1,z2,z8,z4,z5,z6])],[(0,[z1,z35,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z692])],[(0,[z1,z2,z8,z693,z4,z5,z6]),(1,[z1,z2,z8,z410,z5,z6]),(1,[z1,z362,z2,z8,z4,z5])],[(0,[z1,z57,z2,z3,z8,z4,z5]),(0,[z44,z1,z57,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z274,z5,z6])]],
   [[(0,[z1,z694,z2,z8,z4,z5,z6]),(0,[z1,z228,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z102,z5,z19,z6])],[(0,[z117,z1,z16,z2,z8,z4,z5]),(0,[z1,z695,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z402,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z30])],[(0,[z1,z2,z696,z8,z4,z5,z6])],[],[(0,[z1,z346,z2,z8,z4,z5,z6]),(0,[z113,z1,z2,z8,z4,z5,z107]),(0,[z1,z2,z8,z70,z4,z5,z6]),(0,[z1,z2,z8,z4,z223,z5,z6])],[(0,[z1,z24,z2,z8,z78,z5,z6]),(0,[z1,z2,z8,z697,z4,z5,z6]),(0,[z1,z670,z14,z2,z8,z4,z5]),(0,[z1,z57,z2,z8,z4,z5,z6]),(0,[z1,z2,z25,z321,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z127,z10]),(0,[z1,z2,z8,z4,z5,z101,z54])],[(0,[z674,z1,z2,z25,z8,z4,z5])],[(0,[z1,z2,z8,z119,z4,z5,z6])],[(0,[z1,z2,z8,z4,z698,z5,z6])],[(0,[z89,z1,z2,z25,z8,z4,z5]),(1,[z1,z8,z4,z5,z126,z6])],[(0,[z1,z2,z8,z4,z699,z5,z6]),(0,[z112,z1,z57,z2,z8,z4,z5]),(0,[z89,z1,z14,z2,z8,z4,z5]),(0,[z0,z1,z2,z8,z4,z5,z343]),(0,[z700,z1,z2,z8,z4,z5,z6])],[(0,[z1,z61,z2,z8,z4,z5,z10]),(0,[z1,z15,z2,z8,z4,z5,z504]),(0,[z1,z135,z16,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z701,z5,z6])],[(0,[z1,z2,z8,z4,z5,z702,z6]),(0,[z1,z2,z8,z4,z703,z5,z6])],[(0,[z1,z2,z8,z4,z704,z5,z6]),(1,[z1,z108,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z101,z22]),(0,[z1,z2,z8,z4,z5,z462,z10]),(0,[z1,z2,z8,z4,z705,z5,z6]),(0,[z1,z51,z8,z4,z5,z19,z6])],[(0,[z0,z1,z2,z66,z4,z5,z6]),(0,[z1,z2,z8,z4,z78,z5,z22]),(0,[z1,z16,z2,z8,z4,z5,z56]),(0,[z1,z50,z57,z2,z8,z4,z5]),(0,[z1,z2,z706,z8,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z14,z8,z686,z4,z5]),(0,[z89,z123,z8,z4,z5,z22]),(0,[z474,z2,z8,z4,z5,z22]),(0,[z1,z8,z4,z707,z5,z6]),(0,[z1,z104,z57,z2,z4,z105]),(0,[z1,z2,z8,z4,z5,z708]),(0,[z1,z43,z76,z8,z4,z5])],[(0,[z96,z2,z8,z4,z5,z10]),(0,[z1,z109,z367,z2,z8,z4]),(0,[z1,z160,z8,z546,z5,z6]),(0,[z1,z104,z2,z72,z4,z105])],[(0,[z1,z565,z2,z25,z4,z5]),(0,[z1,z709,z108,z8,z4,z5]),(0,[z1,z710,z2,z8,z4,z5])],[(0,[z1,z2,z25,z4,z613,z5]),(0,[z1,z108,z8,z4,z5,z56]),(0,[z96,z138,z2,z8,z4,z5]),(0,[z1,z14,z304,z8,z4,z5]),(0,[z1,z2,z711,z8,z4,z5]),(0,[z1,z25,z8,z4,z5,z126]),(0,[z1,z43,z8,z4,z131,z5])],[(0,[z89,z1,z355,z8,z4,z5]),(0,[z1,z128,z2,z490,z4,z5]),(0,[z1,z2,z8,z4,z712,z5]),(0,[z1,z2,z713,z8,z4,z5])],[(0,[z1,z145,z2,z66,z4,z5]),(0,[z1,z2,z8,z4,z5,z714]),(0,[z1,z2,z8,z4,z715,z5])],[(0,[z1,z14,z8,z4,z5,z661]),(0,[z1,z2,z716,z8,z4,z5]),(0,[z1,z334,z8,z102,z5,z6])],[(0,[z1,z2,z8,z4,z5,z717]),(0,[z1,z2,z8,z4,z718,z137])],[(0,[z1,z2,z8,z719,z5,z6]),(0,[z1,z2,z8,z4,z5,z418])],[(0,[z1,z2,z8,z4,z720,z6]),(0,[z49,z57,z2,z8,z91,z5]),(0,[z1,z141,z8,z4,z5,z10])],[(0,[z1,z2,z8,z4,z5,z721]),(0,[z89,z311,z123,z8,z4,z5]),(0,[z65,z83,z66,z4,z5,z6]),(0,[z1,z722,z2,z8,z4,z5]),(0,[z1,z108,z8,z4,z34,z5]),(0,[z1,z2,z76,z723,z5,z6]),(0,[z1,z2,z8,z4,z5,z724]),(0,[z1,z2,z8,z4,z137,z130])],[(0,[z1,z2,z8,z4,z5,z725]),(0,[z1,z726,z2,z8,z4,z5]),(0,[z1,z727,z2,z8,z4,z5]),(0,[z1,z16,z728,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z729])],[(0,[z1,z43,z8,z4,z68,z5]),(0,[z1,z2,z8,z4,z5,z730])],[(0,[z1,z2,z8,z4,z731,z10]),(0,[z1,z2,z8,z4,z5,z494])],[(0,[z1,z2,z8,z4,z732,z5]),(0,[z199,z1,z57,z2,z8,z5])]],
   [[(0,[z65,z276,z2,z66,z4,z6]),(0,[z1,z323,z2,z25,z4,z5])],[(1,[z1,z733,z8,z4,z5]),(0,[z1,z108,z8,z4,z5,z29]),(0,[z1,z135,z14,z8,z4,z102]),(0,[z1,z734,z43,z8,z4,z5])],[(0,[z1,z83,z8,z370,z5,z6]),(0,[z1,z2,z8,z4,z5,z735]),(0,[z1,z108,z8,z736,z4,z5]),(0,[z1,z2,z8,z4,z5,z737]),(0,[z1,z2,z8,z4,z738,z5])],[(0,[z1,z2,z8,z4,z5,z739]),(0,[z1,z2,z8,z4,z740,z5])],[(0,[z1,z108,z57,z8,z4,z5]),(0,[z1,z323,z69,z4,z5,z6]),(0,[z1,z14,z2,z8,z4,z741])],[(0,[z89,z1,z742,z8,z4,z5]),(0,[z1,z2,z8,z743,z5,z6]),(0,[z1,z744,z8,z4,z5,z6]),(0,[z1,z745,z8,z4,z5,z6]),(0,[z1,z334,z411,z2,z8,z5])],[(0,[z1,z746,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z234]),(0,[z1,z747,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z137,z181])],[(0,[z1,z276,z16,z2,z8,z4]),(0,[z1,z748,z2,z8,z4,z5]),(0,[z1,z2,z490,z73,z4,z5]),(0,[z1,z2,z8,z212,z5,z45])],[(0,[z1,z2,z8,z4,z5,z47]),(0,[z1,z2,z749,z8,z4,z5]),(0,[z1,z15,z97,z4,z5,z197]),(0,[z1,z160,z367,z2,z8,z6]),(0,[z157,z1,z14,z2,z103,z5]),(0,[z1,z750,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z751,z5]),(0,[z1,z108,z8,z4,z68,z5]),(0,[z1,z752,z2,z8,z4,z5]),(0,[z113,z2,z25,z8,z4,z34]),(0,[z1,z2,z8,z4,z753,z5])],[(0,[z1,z754,z8,z4,z5,z6]),(0,[z113,z14,z2,z8,z4,z34]),(0,[z1,z104,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z556,z54]),(0,[z1,z755,z8,z4,z5,z6]),(0,[z1,z27,z2,z8,z4,z131])],[(0,[z65,z16,z2,z66,z4,z5]),(0,[z1,z25,z183,z8,z4,z5]),(0,[z1,z182,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z756])],[(0,[z1,z622,z14,z8,z4,z5])],[(0,[z1,z2,z8,z757,z5,z6]),(0,[z1,z2,z758,z8,z4,z5]),(0,[z1,z759,z221,z8,z4,z5]),(0,[z1,z183,z12,z8,z4,z6]),(0,[z1,z760,z2,z8,z4,z5]),(0,[z1,z2,z761,z8,z4,z5]),(0,[z1,z1,z108,z8,z4,z5]),(0,[z1,z108,z8,z4,z762,z5]),(0,[z1,z108,z8,z4,z164,z5]),(0,[z1,z77,z2,z413,z4,z5])],[(0,[z1,z2,z8,z4,z763,z6]),(0,[z1,z764,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z765]),(0,[z1,z2,z8,z4,z5,z766])],[(0,[z49,z2,z8,z91,z5,z17]),(0,[z1,z108,z8,z85,z4,z5])]],
   [[(0,[z1,z440,z8,z4,z5,z22])],[(0,[z1,z767,z2,z8,z4,z5]),(0,[z1,z57,z564,z8,z4,z5])],[(0,[z48,z2,z8,z68,z5,z10]),(0,[z1,z768,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z769]),(0,[z1,z2,z770,z8,z4,z5]),(0,[z1,z15,z8,z4,z5,z197]),(0,[z1,z2,z771,z8,z4,z5])],[(0,[z1,z108,z8,z4,z5,z326]),(0,[z1,z2,z8,z4,z772,z5]),(0,[z1,z2,z4,z5,z773,z30])],[(0,[z112,z365,z2,z8,z4,z5]),(0,[z1,z346,z12,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z466]),(0,[z1,z61,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z774,z5]),(0,[z1,z2,z8,z4,z5,z775]),(0,[z1,z104,z16,z2,z4,z105]),(0,[z1,z43,z8,z4,z248,z5])],[(0,[z1,z83,z8,z4,z210,z6]),(0,[z1,z108,z8,z4,z102,z5]),(0,[z1,z108,z8,z4,z103,z5]),(0,[z1,z2,z8,z4,z5,z776])],[(0,[z1,z2,z8,z4,z5,z777]),(0,[z1,z2,z8,z4,z137,z285]),(0,[z1,z2,z8,z4,z5,z778])],[(0,[z1,z2,z8,z779,z5,z6]),(0,[z1,z16,z780,z8,z4,z5])],[(0,[z89,z16,z123,z8,z4,z5]),(0,[z233,z16,z2,z8,z4,z75]),(0,[z1,z15,z97,z4,z5,z217]),(0,[z1,z2,z8,z4,z310,z5]),(0,[z439,z2,z369,z8,z4,z5]),(0,[z1,z2,z192,z8,z189,z5]),(0,[z1,z2,z8,z4,z5,z259])],[(0,[z1,z2,z8,z4,z5,z781]),(0,[z1,z452,z57,z8,z4,z5]),(0,[z1,z43,z8,z4,z5,z782])],[(0,[z1,z783,z2,z8,z5,z6])],[(0,[z44,z1,z43,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z784]),(0,[z1,z8,z4,z5,z785,z22]),(0,[z1,z2,z8,z786,z5,z6]),(0,[z1,z2,z8,z455,z5,z6]),(0,[z1,z160,z8,z70,z5,z195]),(0,[z1,z16,z2,z8,z119,z78])],[(0,[z1,z2,z8,z4,z787,z6]),(0,[z1,z2,z25,z4,z5,z656])],[(0,[z1,z788,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z789]),(0,[z1,z2,z790,z8,z4,z5]),(0,[z2,z8,z4,z5,z10,z791])]],
   [[(0,[z1,z128,z780,z8,z4,z5]),(0,[z1,z792,z2,z8,z4,z5]),(0,[z1,z793,z2,z8,z4,z5]),(0,[z1,z367,z2,z8,z4,z227]),(0,[z1,z43,z8,z4,z5,z19]),(0,[z1,z135,z57,z8,z4,z102]),(0,[z1,z2,z8,z4,z794,z5])],[(0,[z113,z57,z2,z8,z4,z34]),(0,[z1,z2,z8,z795,z5,z6]),(0,[z1,z24,z43,z8,z4,z5])],[(0,[z1,z2,z8,z4,z164,z139]),(0,[z1,z2,z8,z4,z5,z796]),(0,[z1,z2,z25,z321,z4,z274])],[(1,[z1,z108,z8,z4,z5]),(0,[z1,z797,z2,z8,z4,z5]),(0,[z1,z798,z2,z8,z5,z6]),(0,[z1,z108,z8,z4,z5,z10]),(0,[z1,z61,z57,z69,z4,z5]),(0,[z1,z14,z2,z321,z4,z274]),(0,[z1,z754,z25,z8,z4,z5])],[(0,[z1,z799,z2,z8,z4,z5]),(0,[z199,z1,z16,z2,z8,z5]),(0,[z2,z8,z4,z34,z800,z6]),(0,[z1,z108,z8,z4,z5,z801]),(0,[z1,z802,z2,z8,z4,z5]),(0,[z1,z803,z43,z8,z4,z5]),(0,[z1,z16,z2,z4,z5,z460])],[(0,[z1,z16,z2,z12,z8,z4]),(0,[z1,z2,z8,z4,z804,z5]),(0,[z2,z8,z4,z5,z791,z22]),(0,[z1,z2,z8,z84,z4,z10]),(0,[z1,z61,z211,z69,z4,z5]),(0,[z1,z57,z15,z97,z4,z5]),(0,[z1,z2,z8,z4,z805,z5]),(0,[z1,z2,z8,z4,z5,z129]),(0,[z165,z1,z2,z8,z248,z5]),(0,[z1,z16,z182,z8,z4,z5])],[(0,[z1,z806,z8,z4,z5,z22]),(0,[z1,z2,z490,z4,z5,z30])],[(0,[z157,z1,z57,z2,z103,z5])],[(0,[z1,z8,z4,z5,z354,z22]),(0,[z439,z2,z8,z4,z5,z10]),(0,[z1,z807,z2,z8,z4,z5]),(0,[z1,z16,z2,z570,z4,z5])],[(0,[z112,z808,z8,z4,z5,z6]),(0,[z365,z123,z2,z8,z4,z5]),(0,[z1,z809,z8,z4,z5,z6]),(0,[z1,z108,z16,z8,z4,z5]),(0,[z1,z61,z810,z4,z5,z6]),(0,[z1,z2,z472,z8,z4,z5]),(0,[z1,z2,z25,z706,z4,z5])],[(0,[z117,z1,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z811]),(0,[z1,z334,z51,z8,z4,z6])],[(0,[z1,z2,z8,z4,z5,z812]),(0,[z1,z2,z8,z4,z219,z22]),(0,[z1,z14,z8,z4,z214,z5]),(0,[z1,z50,z141,z2,z8,z6]),(0,[z1,z2,z8,z4,z5,z813])],[(0,[z112,z53,z8,z4,z5,z6]),(0,[z1,z814,z2,z8,z4,z5]),(0,[z1,z815,z8,z4,z5,z22]),(0,[z1,z104,z2,z4,z105,z10])],[(0,[z1,z816,z8,z4,z5,z6]),(0,[z233,z2,z8,z4,z800,z6]),(0,[z1,z108,z97,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z817]),(0,[z1,z2,z8,z4,z818,z5]),(0,[z1,z135,z8,z4,z819,z6])],[(0,[z1,z221,z8,z4,z5,z226]),(0,[z1,z2,z8,z4,z5,z820]),(0,[z1,z2,z8,z4,z5,z821]),(0,[z822,z2,z8,z4,z5,z6]),(0,[z1,z16,z2,z8,z4,z823])],[(0,[z1,z2,z8,z4,z5,z824]),(0,[z1,z825,z2,z8,z4,z5]),(0,[z1,z16,z2,z490,z4,z5]),(0,[z1,z2,z8,z4,z5,z826])]],
   [[(0,[z1,z2,z8,z4,z5,z827]),(0,[z1,z828,z2,z8,z4,z5]),(0,[z1,z57,z51,z8,z4,z19]),(0,[z1,z16,z141,z8,z4,z5]),(0,[z44,z1,z2,z8,z5,z829])],[(0,[z1,z2,z8,z4,z5,z478]),(0,[z1,z2,z8,z830,z5,z6]),(0,[z1,z2,z8,z4,z5,z831]),(0,[z89,z808,z8,z4,z5,z6]),(0,[z117,z2,z8,z4,z5,z791]),(0,[z1,z2,z8,z4,z5,z832])],[(0,[z1,z2,z4,z5,z833,z22]),(0,[z1,z57,z2,z8,z455,z5])],[(0,[z1,z2,z8,z4,z5,z834]),(0,[z1,z835,z8,z4,z5,z6]),(0,[z1,z2,z836,z8,z4,z5]),(0,[z1,z61,z2,z52,z4,z5]),(0,[z1,z135,z43,z8,z4,z5])],[(0,[z1,z2,z8,z837,z5,z6]),(0,[z1,z135,z8,z4,z102,z22]),(0,[z1,z61,z69,z4,z5,z6]),(0,[z1,z334,z8,z9,z5,z6]),(0,[z528,z1,z14,z8,z4,z5]),(0,[z1,z14,z624,z8,z4,z5])],[(0,[z1,z2,z8,z4,z838,z6]),(0,[z1,z839,z8,z4,z5,z6]),(0,[z1,z840,z8,z4,z5,z6]),(0,[z1,z841,z2,z4,z5,z6]),(0,[z1,z8,z4,z5,z842,z6]),(0,[z44,z1,z2,z8,z5,z476]),(0,[z1,z2,z8,z4,z5,z843])],[(0,[z1,z844,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z107]),(0,[z233,z1,z43,z8,z4,z5]),(0,[z1,z14,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z845]),(0,[z1,z2,z355,z4,z5,z29]),(0,[z1,z2,z25,z8,z846,z5])],[(0,[z1,z2,z8,z4,z5,z847]),(0,[z1,z14,z94,z8,z4,z5]),(1,[z1,z810,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z848]),(0,[z1,z2,z8,z4,z849,z5]),(0,[z1,z16,z2,z614,z4,z5])],[(0,[z1,z2,z8,z4,z5,z850]),(0,[z1,z16,z2,z8,z4,z219]),(0,[z1,z2,z851,z8,z4,z5]),(0,[z1,z8,z4,z5,z785,z6]),(0,[z157,z1,z108,z8,z4,z5]),(0,[z1,z2,z8,z852,z5,z22]),(0,[z1,z853,z8,z4,z5,z6]),(0,[z1,z43,z8,z119,z4,z5])],[(0,[z113,z1,z108,z8,z4,z5]),(0,[z1,z50,z57,z2,z8,z127])],[(0,[z1,z2,z8,z4,z5,z854]),(0,[z1,z2,z8,z4,z219,z198]),(0,[z1,z855,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z856,z22]),(0,[z1,z2,z8,z4,z857,z5]),(0,[z1,z2,z8,z858,z4,z5])],[(0,[z1,z334,z14,z2,z8,z5])],[(0,[z1,z2,z859,z8,z4,z5]),(0,[z1,z15,z355,z8,z4,z5]),(0,[z1,z24,z367,z8,z9,z6]),(0,[z860,z1,z43,z8,z4,z5])],[(0,[z1,z2,z8,z5,z861,z10]),(0,[z1,z24,z8,z707,z5,z6]),(0,[z1,z16,z440,z8,z4,z5])],[(0,[z1,z8,z4,z862,z5,z6]),(0,[z1,z2,z8,z4,z863,z22]),(0,[z1,z8,z4,z5,z864,z56]),(0,[z1,z2,z76,z73,z5,z575])],[(0,[z1,z16,z83,z8,z4,z5]),(0,[z1,z865,z2,z8,z4,z5]),(0,[z1,z108,z76,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z866])]],
   [[(0,[z1,z43,z8,z4,z5,z127])],[(0,[z65,z221,z66,z4,z5,z6]),(0,[z1,z806,z8,z4,z5,z6]),(0,[z1,z2,z867,z8,z4,z5]),(0,[z2,z8,z4,z5,z6,z868])],[(0,[z1,z276,z2,z25,z8,z4]),(0,[z1,z2,z8,z4,z5,z869]),(0,[z1,z108,z8,z4,z131,z5]),(0,[z1,z2,z8,z4,z5,z870]),(0,[z1,z2,z871,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z872])],[(0,[z65,z2,z66,z4,z5,z226])],[(0,[z1,z873,z2,z8,z4,z5]),(0,[z561,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z197])],[(0,[z112,z53,z25,z8,z4,z5]),(0,[z1,z874,z2,z8,z5,z6]),(0,[z96,z1,z108,z8,z4,z5]),(0,[z1,z875,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z876]),(0,[z1,z135,z16,z8,z4,z102]),(0,[z1,z877,z2,z8,z4,z5])],[(0,[z1,z878,z2,z8,z4,z5]),(0,[z1,z160,z25,z8,z70,z5]),(0,[z1,z2,z8,z879,z5,z6]),(0,[z1,z2,z880,z8,z4,z5])],[(0,[z1,z881,z8,z4,z5,z6]),(0,[z1,z128,z8,z4,z5,z354]),(0,[z1,z61,z81,z8,z4,z5]),(0,[z1,z61,z14,z69,z4,z5])],[(0,[z1,z108,z8,z4,z5,z306]),(0,[z1,z8,z4,z5,z882,z6]),(0,[z1,z2,z8,z4,z5,z883]),(0,[z1,z43,z8,z4,z5,z90])],[(0,[z1,z2,z8,z4,z5,z884]),(0,[z572,z1,z14,z8,z4,z5]),(0,[z1,z221,z8,z370,z5,z6])],[(0,[z1,z2,z8,z4,z885,z6]),(0,[z1,z14,z8,z4,z5,z630]),(0,[z1,z2,z8,z4,z5,z886]),(0,[z1,z50,z2,z8,z127,z6])],[(0,[z1,z2,z8,z370,z5,z226]),(0,[z233,z2,z8,z4,z75,z10]),(0,[z1,z145,z887,z8,z4,z5]),(0,[z1,z887,z8,z4,z5,z10]),(0,[z1,z2,z888,z8,z4,z5])],[(0,[z1,z108,z8,z4,z5,z127]),(0,[z1,z2,z889,z8,z4,z5]),(0,[z157,z1,z16,z2,z103,z5]),(0,[z1,z2,z8,z4,z5,z890])],[(0,[z1,z2,z8,z891,z5,z6]),(0,[z1,z892,z2,z8,z4,z5]),(0,[z1,z2,z4,z5,z833,z6]),(0,[z1,z893,z2,z8,z4,z5]),(0,[z1,z57,z43,z8,z4,z5]),(0,[z1,z2,z25,z4,z5,z30]),(0,[z1,z2,z8,z4,z894,z5])],[(0,[z1,z2,z8,z4,z5,z469]),(0,[z89,z123,z8,z4,z5,z6]),(0,[z1,z895,z2,z8,z5,z6]),(0,[z1,z2,z25,z8,z4,z210]),(0,[z205,z1,z2,z103,z5,z6]),(0,[z1,z2,z321,z4,z274,z22]),(0,[z1,z2,z8,z4,z5,z896]),(0,[z1,z2,z8,z4,z897,z5]),(0,[z1,z14,z571,z8,z4,z5]),(1,[z1,z2,z8,z4,z718])],[(0,[z1,z2,z8,z898,z5,z6]),(0,[z1,z365,z2,z8,z4,z5]),(0,[z1,z135,z8,z4,z102,z6]),(0,[z1,z2,z52,z4,z5,z30]),(0,[z1,z899,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z4,z5,z900]),(0,[z1,z346,z241,z8,z4,z5]),(0,[z1,z108,z160,z8,z4,z5]),(0,[z1,z108,z128,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z901]),(0,[z1,z104,z2,z4,z129,z105]),(0,[z1,z104,z2,z25,z4,z105])],[(0,[z112,z1,z46,z8,z4,z5]),(0,[z1,z902,z2,z8,z4,z5]),(0,[z1,z14,z8,z4,z5,z11])],[(0,[z1,z2,z8,z4,z5,z903]),(0,[z1,z904,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z905])],[(0,[z112,z16,z53,z8,z4,z5]),(0,[z1,z2,z906,z8,z4,z5]),(1,[z1,z2,z4,z5,z773])],[(0,[z1,z2,z25,z8,z370,z5]),(0,[z1,z346,z57,z8,z4,z5]),(0,[z1,z907,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z908]),(0,[z1,z14,z8,z361,z4,z5]),(0,[z1,z57,z8,z4,z5,z555])],[(0,[z1,z14,z2,z8,z370,z5]),(0,[z1,z2,z8,z5,z856,z6]),(0,[z1,z2,z8,z4,z5,z217]),(0,[z1,z2,z8,z4,z5,z909]),(0,[z1,z8,z70,z5,z520,z6])],[(0,[z1,z2,z910,z8,z4,z5]),(0,[z1,z145,z2,z4,z5,z92]),(0,[z1,z2,z8,z78,z360,z6])],[(0,[z1,z911,z83,z8,z4,z5]),(0,[z1,z2,z76,z73,z5,z22]),(0,[z1,z912,z8,z4,z5,z22])],[(0,[z1,z913,z2,z8,z4,z5])],[(0,[z89,z1,z46,z8,z4,z5]),(0,[z199,z1,z2,z8,z5,z10]),(0,[z1,z51,z8,z4,z662,z6]),(0,[z1,z914,z2,z8,z4,z5]),(0,[z1,z2,z8,z85,z223,z5])],[(0,[z1,z2,z369,z4,z5,z468]),(0,[z1,z334,z57,z2,z8,z5]),(0,[z1,z2,z8,z4,z915,z5])],[(0,[z1,z108,z51,z8,z4,z5]),(0,[z1,z2,z8,z916,z5,z6]),(0,[z1,z2,z8,z4,z917,z5])],[],[(0,[z1,z655,z69,z4,z5,z6]),(0,[z1,z221,z8,z4,z210,z6]),(0,[z108,z8,z4,z5,z10,z22]),(0,[z1,z104,z2,z490,z4,z5]),(0,[z1,z50,z14,z2,z8,z127])],[(0,[z1,z46,z15,z8,z4,z5]),(0,[z65,z2,z66,z370,z5,z6]),(0,[z1,z918,z2,z8,z4,z5]),(0,[z220,z1,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z919]),(0,[z1,z920,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z210,z226]),(0,[z199,z1,z2,z25,z8,z5]),(0,[z1,z2,z8,z4,z921,z5]),(0,[z1,z644,z2,z8,z4,z155]),(0,[z1,z2,z8,z4,z5,z922])]],
   [[(0,[z1,z923,z2,z8,z4,z5]),(0,[z1,z43,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z924]),(0,[z1,z2,z8,z4,z5,z925])],[(0,[z1,z2,z926,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z927]),(0,[z1,z928,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z929])],[(0,[z561,z112,z14,z8,z4,z5]),(0,[z1,z930,z2,z8,z4,z5]),(0,[z1,z2,z8,z84,z4,z227]),(0,[z1,z2,z8,z4,z5,z931]),(0,[z1,z43,z266,z8,z4,z5]),(0,[z263,z1,z43,z8,z4,z5])],[(0,[z1,z2,z932,z8,z4,z5]),(0,[z1,z311,z8,z4,z5,z354]),(0,[z1,z2,z8,z4,z933,z5])],[(0,[z1,z2,z8,z4,z5,z934]),(0,[z1,z288,z2,z8,z4,z5]),(0,[z1,z14,z2,z8,z935,z5]),(0,[z1,z8,z4,z5,z126,z259])],[(0,[z1,z2,z936,z4,z5,z22]),(0,[z623,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z937]),(0,[z1,z2,z938,z8,z4,z5]),(0,[z1,z16,z2,z8,z4,z939])],[],[(0,[z1,z2,z8,z4,z5,z940]),(0,[z89,z123,z25,z8,z4,z5]),(0,[z1,z14,z8,z4,z5,z56])],[(0,[z1,z2,z8,z4,z5,z22]),(0,[z1,z8,z4,z941,z5,z6]),(0,[z1,z942,z8,z4,z5,z6]),(0,[z1,z141,z8,z119,z4,z6])],[(0,[z1,z46,z2,z8,z4,z5]),(0,[z1,z100,z2,z8,z4,z352]),(0,[z1,z50,z2,z8,z127,z63])],[(0,[z1,z2,z8,z4,z943,z6]),(0,[z1,z145,z942,z8,z4,z5])],[(0,[z1,z944,z2,z8,z4,z5]),(0,[z1,z945,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z946,z5]),(0,[z528,z311,z2,z8,z4,z5]),(0,[z1,z947,z8,z4,z5,z6])],[(0,[z1,z108,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z948]),(0,[z433,z1,z14,z8,z4,z5]),(0,[z1,z221,z8,z4,z5,z10]),(0,[z1,z57,z2,z8,z370,z5]),(0,[z1,z2,z8,z4,z5,z949]),(0,[z1,z950,z2,z8,z4,z5])],[(0,[z1,z904,z8,z4,z5,z6]),(0,[z1,z951,z108,z8,z4,z5]),(0,[z2,z8,z4,z5,z22,z586]),(0,[z1,z2,z355,z8,z4,z5])],[(0,[z1,z952,z2,z8,z4,z5]),(0,[z1,z43,z8,z69,z4,z5]),(0,[z1,z440,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z953])],[(0,[z1,z2,z954,z4,z5,z6]),(0,[z1,z15,z97,z4,z5,z22]),(0,[z1,z108,z8,z4,z5,z19]),(0,[z1,z2,z8,z5,z955,z6]),(0,[z1,z956,z2,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z4,z957,z6])],[(0,[z1,z2,z8,z4,z5,z958]),(0,[z1,z14,z8,z4,z5,z270]),(0,[z1,z14,z8,z639,z4,z5]),(0,[z1,z24,z8,z9,z5,z22]),(0,[z1,z959,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z960])],[(0,[z1,z81,z123,z8,z4,z5]),(0,[z65,z2,z66,z4,z210,z6]),(0,[z1,z2,z8,z4,z5,z961]),(0,[z1,z2,z76,z73,z5,z6])],[(0,[z65,z199,z2,z66,z5,z6]),(0,[z0,z16,z2,z3,z4,z5])],[(0,[z1,z2,z4,z962,z5,z6]),(0,[z1,z963,z346,z8,z4,z5]),(0,[z1,z160,z8,z70,z5,z10]),(0,[z1,z334,z440,z8,z5,z6])],[(0,[z1,z964,z2,z8,z4,z5]),(0,[z1,z108,z589,z8,z4,z5])],[(0,[z157,z1,z2,z442,z5,z6]),(0,[z1,z965,z2,z8,z4,z5]),(0,[z1,z966,z8,z4,z5,z6])],[(0,[z1,z46,z8,z69,z4,z5]),(0,[z1,z35,z123,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z198]),(0,[z1,z2,z8,z4,z967,z6]),(0,[z1,z145,z2,z3,z4,z5])],[(0,[z1,z346,z14,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z196]),(0,[z1,z46,z108,z8,z4,z5]),(0,[z1,z24,z367,z8,z5,z6]),(0,[z1,z14,z57,z8,z4,z5]),(0,[z1,z968,z356,z8,z4,z5])],[(0,[z1,z14,z8,z4,z5,z306]),(0,[z1,z50,z2,z8,z969,z6])],[(0,[z1,z2,z8,z4,z5,z970]),(0,[z1,z2,z8,z4,z5,z971]),(0,[z199,z1,z2,z12,z8,z6]),(0,[z1,z14,z211,z8,z4,z5]),(0,[z1,z2,z8,z4,z357,z5]),(0,[z1,z2,z972,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z973]),(0,[z1,z974,z2,z8,z4,z5])],[(0,[z1,z108,z108,z8,z4,z5]),(0,[z1,z266,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z975,z5]),(0,[z1,z14,z397,z8,z4,z5]),(0,[z1,z976,z8,z4,z5,z6]),(0,[z1,z2,z25,z4,z261,z5]),(0,[z1,z43,z8,z4,z5,z54])],[(0,[z1,z2,z8,z4,z5,z977]),(0,[z1,z2,z8,z4,z978,z5]),(0,[z1,z979,z2,z8,z4,z5]),(0,[z1,z2,z980,z8,z4,z5]),(0,[z1,z16,z367,z2,z8,z4]),(0,[z1,z2,z8,z4,z5,z981]),(1,[z1,z2,z723,z5,z6])],[(0,[z1,z2,z8,z4,z939,z6]),(0,[z1,z57,z2,z321,z4,z274]),(0,[z1,z982,z8,z4,z5,z6])],[(0,[z1,z8,z983,z69,z4,z5]),(0,[z1,z160,z8,z707,z5,z6]),(0,[z1,z2,z8,z4,z5,z984])],[(0,[z1,z2,z985,z4,z5,z6]),(0,[z1,z2,z33,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z986]),(0,[z1,z334,z16,z2,z8,z5]),(0,[z1,z2,z987,z8,z4,z5])]],
   [[(0,[z1,z2,z8,z4,z988,z6]),(0,[z65,z2,z989,z4,z5,z6]),(0,[z1,z8,z4,z5,z990,z6]),(0,[z1,z2,z936,z4,z5,z6]),(0,[z1,z991,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z992])],[(0,[z65,z2,z66,z4,z5,z10]),(0,[z1,z993,z2,z8,z4,z5]),(0,[z258,z2,z8,z4,z5,z22]),(0,[z1,z93,z2,z8,z223,z5]),(0,[z1,z50,z43,z8,z4,z5])],[(0,[z1,z16,z8,z4,z5,z354]),(0,[z1,z2,z994,z8,z4,z5]),(0,[z2,z8,z4,z612,z5,z10]),(0,[z1,z2,z8,z4,z5,z995])],[(0,[z1,z2,z8,z4,z5,z996]),(0,[z65,z183,z66,z4,z5,z6]),(0,[z2,z8,z4,z5,z791,z6]),(0,[z1,z2,z997,z8,z4,z5]),(0,[z1,z43,z8,z4,z5,z314]),(0,[z1,z2,z8,z4,z969,z6])],[(0,[z1,z2,z8,z998,z4,z6]),(0,[z1,z2,z8,z4,z999,z6]),(0,[z1,z2,z8,z1000,z5,z6]),(0,[z1,z14,z8,z530,z4,z5]),(0,[z1,z2,z8,z4,z131,z155])],[(0,[z2,z8,z4,z1001,z5,z6]),(0,[z1,z2,z1002,z8,z4,z5])],[(0,[z1,z8,z4,z5,z354,z6]),(0,[z1,z2,z8,z4,z1003,z6]),(0,[z1,z1004,z8,z4,z5,z6]),(0,[z1,z2,z25,z582,z4,z5]),(0,[z1,z1005,z108,z8,z4,z5])],[(0,[z1,z14,z221,z8,z4,z5]),(0,[z1,z108,z8,z119,z4,z5]),(0,[z1,z365,z15,z8,z4,z5]),(0,[z1,z2,z1006,z8,z4,z5]),(0,[z1,z440,z25,z8,z4,z5]),(0,[z1,z16,z2,z8,z1007,z5])],[(0,[z1,z2,z8,z4,z5,z1008]),(0,[z1,z1009,z2,z8,z4,z5]),(0,[z1,z2,z1010,z8,z4,z5]),(0,[z1,z1011,z2,z8,z4,z5]),(0,[z1,z43,z355,z8,z4,z5]),(0,[z1,z728,z8,z4,z5,z6]),(0,[z1,z100,z43,z8,z4,z5])],[(0,[z1,z2,z8,z4,z219,z6]),(0,[z1,z2,z8,z370,z5,z10]),(0,[z1,z1012,z2,z8,z4,z5])],[(0,[z1,z815,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1013,z5]),(0,[z1,z15,z97,z4,z5,z6]),(0,[z1,z2,z8,z4,z137,z341]),(0,[z1,z1014,z2,z8,z4,z5])],[(0,[z65,z346,z66,z4,z5,z6]),(0,[z1,z1015,z8,z4,z5,z6]),(0,[z1,z128,z2,z4,z5,z381]),(0,[z1,z61,z16,z69,z4,z5]),(0,[z249,z2,z356,z8,z4,z5]),(0,[z1,z1016,z2,z8,z4,z5]),(0,[z1,z1017,z2,z8,z4,z5])],[(0,[z1,z2,z33,z8,z168,z5]),(0,[z1,z8,z4,z5,z1018,z343]),(0,[z49,z16,z2,z8,z91,z5]),(0,[z523,z1,z14,z8,z4,z5]),(0,[z1,z24,z8,z9,z5,z6])],[(0,[z1,z1019,z2,z8,z4,z5]),(0,[z1,z2,z8,z119,z78,z10]),(0,[z1,z1020,z2,z8,z4,z6]),(0,[z1,z160,z8,z5,z296,z6]),(0,[z1,z51,z8,z4,z819,z6]),(0,[z1,z8,z4,z5,z6,z1021]),(0,[z1,z440,z8,z4,z5,z63]),(1,[z1,z50,z141,z8,z6]),(0,[z1,z2,z8,z78,z969,z6])],[(0,[z157,z1,z2,z103,z5,z22]),(0,[z1,z340,z2,z8,z4,z95]),(0,[z1,z2,z8,z4,z5,z1022])],[(0,[z1,z1023,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z1024,z6]),(0,[z1,z2,z1025,z8,z4,z5]),(0,[z1,z51,z8,z4,z19,z10]),(0,[z1,z2,z8,z4,z5,z1026]),(0,[z1,z50,z8,z126,z127,z6]),(0,[z1,z2,z8,z4,z5,z1027])]],
   [[(0,[z1,z2,z8,z4,z1028,z5]),(0,[z1,z1029,z2,z8,z4,z5]),(0,[z1,z2,z8,z969,z127,z6])],[(0,[z1,z2,z8,z4,z402,z5]),(0,[z157,z1,z2,z723,z5,z6])],[(0,[z1,z14,z2,z8,z4,z210]),(0,[z1,z367,z2,z8,z4,z22]),(0,[z44,z1,z108,z8,z4,z5]),(0,[z1,z14,z328,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z575]),(0,[z1,z2,z8,z4,z5,z1030])],[(0,[z112,z1,z365,z8,z4,z5]),(0,[z1,z43,z8,z66,z4,z5]),(0,[z1,z2,z8,z4,z5,z1031]),(0,[z1,z108,z8,z4,z5,z416]),(0,[z1,z51,z43,z8,z4,z5])],[(0,[z1,z1032,z2,z8,z4,z5]),(0,[z1,z2,z8,z168,z5,z22]),(0,[z1,z2,z8,z4,z1033,z5]),(0,[z1,z411,z2,z8,z4,z5])],[(0,[z1,z2,z25,z8,z84,z4]),(0,[z1,z2,z8,z4,z5,z1034])],[(0,[z112,z365,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1035]),(0,[z1,z2,z8,z852,z5,z6]),(0,[z2,z8,z4,z636,z5,z10]),(0,[z1,z266,z8,z4,z5,z6]),(0,[z1,z14,z2,z8,z84,z4])],[(0,[z1,z14,z8,z398,z4,z5]),(0,[z1,z108,z8,z4,z5,z90]),(0,[z1,z2,z8,z4,z5,z504]),(0,[z1,z2,z8,z4,z1036,z6]),(0,[z1,z1037,z2,z8,z4,z5])],[(0,[z1,z2,z8,z595,z5,z45]),(0,[z1,z2,z8,z4,z5,z1038]),(0,[z1,z2,z8,z4,z5,z1039]),(0,[z1,z2,z8,z4,z5,z1040])],[(0,[z1,z1041,z2,z8,z4,z5])],[(0,[z65,z2,z168,z66,z5,z6]),(0,[z1,z108,z8,z4,z512,z5]),(0,[z1,z43,z8,z4,z9,z5]),(0,[z1,z1042,z8,z4,z5,z6])],[(0,[z89,z1,z365,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1043])],[(0,[z1,z2,z8,z4,z863,z6]),(0,[z1,z1044,z2,z8,z4,z5]),(0,[z1,z288,z15,z8,z4,z5]),(0,[z1,z1045,z2,z8,z4,z6]),(0,[z1,z135,z8,z4,z229,z6]),(0,[z1,z141,z8,z4,z5,z259])],[(0,[z1,z2,z8,z4,z210,z10]),(0,[z592,z2,z8,z91,z5,z6]),(0,[z1,z2,z8,z4,z1046,z5]),(0,[z1,z1047,z2,z8,z4,z5])],[(0,[z1,z183,z8,z4,z5,z1048]),(0,[z1,z15,z97,z4,z5,z504])],[(0,[z1,z2,z8,z4,z5,z1049]),(0,[z1,z733,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1050]),(0,[z1,z2,z8,z4,z5,z1051])]],
   [[(0,[z1,z2,z8,z4,z5,z1052]),(0,[z554,z2,z8,z4,z34,z6]),(0,[z117,z1,z108,z8,z4,z5]),(0,[z1,z365,z8,z69,z4,z5])],[(0,[z1,z1053,z2,z8,z4,z5]),(0,[z1,z50,z16,z2,z8,z127])],[(0,[z1,z2,z8,z4,z1054,z6]),(0,[z1,z604,z2,z8,z4,z5]),(0,[z48,z2,z8,z1001,z5,z6]),(0,[z1,z2,z8,z4,z5,z1055]),(0,[z1,z2,z8,z4,z5,z37]),(0,[z1,z57,z427,z8,z4,z5]),(0,[z339,z1,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z352,z54]),(0,[z1,z50,z182,z8,z127,z6])],[(0,[z1,z2,z8,z4,z5,z1056])],[(0,[z1,z2,z1057,z4,z5,z6]),(0,[z1,z108,z15,z8,z4,z5]),(0,[z1,z57,z55,z8,z4,z5])],[(0,[z1,z160,z43,z8,z4,z5])],[(0,[z1,z808,z8,z4,z5,z6]),(0,[z1,z1058,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1059])],[(0,[z1,z2,z8,z410,z5,z22]),(0,[z1,z2,z1060,z8,z4,z5]),(0,[z1,z1061,z8,z4,z5,z6]),(0,[z1,z616,z2,z8,z4,z181]),(0,[z1,z2,z8,z4,z137,z54])],[(0,[z1,z2,z1062,z8,z4,z5]),(0,[z1,z2,z4,z1063,z5,z6]),(0,[z1,z2,z8,z4,z1064,z6])],[(0,[z1,z759,z2,z8,z4,z5]),(0,[z1,z57,z2,z8,z4,z210]),(0,[z1,z135,z108,z8,z4,z5]),(0,[z1,z15,z97,z4,z5,z37]),(0,[z1,z2,z1065,z8,z4,z5])],[(0,[z1,z46,z81,z8,z4,z5])],[(0,[z1,z734,z2,z8,z4,z5]),(0,[z399,z2,z8,z4,z5,z22]),(0,[z1,z1066,z2,z8,z4,z5]),(0,[z1,z228,z43,z8,z4,z5])],[(0,[z233,z1,z108,z8,z4,z5]),(0,[z1,z2,z1067,z8,z4,z5]),(0,[z1,z2,z321,z4,z274,z6])],[(0,[z1,z1068,z8,z4,z5,z6]),(0,[z123,z808,z8,z4,z5,z6]),(0,[z1,z57,z2,z8,z84,z4]),(0,[z1,z2,z8,z4,z5,z864]),(0,[z1,z50,z141,z8,z127,z6])],[(0,[z1,z2,z8,z4,z1069,z5]),(0,[z1,z183,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z1070]),(0,[z1,z2,z8,z4,z1071,z5])],[(0,[z1,z2,z8,z168,z5,z6]),(0,[z1,z2,z8,z4,z1072,z5]),(0,[z49,z2,z8,z91,z5,z10]),(0,[z1,z24,z25,z8,z9,z5]),(0,[z1,z2,z321,z4,z1073,z6]),(0,[z1,z266,z25,z8,z4,z5]),(0,[z1,z43,z8,z4,z5,z101])]],
   [[],[(0,[z48,z2,z8,z68,z5,z466]),(0,[z1,z2,z8,z4,z5,z1074]),(0,[z1,z25,z8,z4,z5,z354]),(0,[z1,z57,z8,z4,z5,z252])],[(0,[z1,z1075,z2,z8,z4,z5]),(0,[z1,z288,z8,z110,z4,z5]),(0,[z1,z1076,z8,z4,z5,z6]),(0,[z1,z16,z1077,z8,z4,z5])],[(0,[z1,z8,z4,z5,z126,z22]),(0,[z1,z160,z8,z70,z5,z418]),(0,[z1,z2,z8,z4,z5,z1078])],[(0,[z1,z81,z53,z8,z4,z5]),(0,[z113,z16,z2,z8,z4,z34]),(0,[z1,z334,z2,z8,z5,z10])],[(0,[z89,z46,z123,z8,z4,z5]),(0,[z1,z276,z2,z8,z4,z10]),(0,[z1,z963,z2,z8,z4,z5]),(0,[z1,z912,z8,z4,z5,z6]),(0,[z1,z108,z749,z8,z4,z5]),(0,[z1,z288,z8,z69,z4,z5]),(0,[z1,z109,z2,z8,z84,z4]),(0,[z1,z1079,z8,z4,z5,z6]),(0,[z1,z32,z2,z25,z4,z5])],[(0,[z1,z2,z8,z410,z5,z198]),(0,[z1,z346,z8,z4,z5,z10])],[(0,[z1,z2,z1080,z8,z4,z5]),(0,[z1,z1081,z8,z4,z5,z6])],[(0,[z1,z2,z490,z8,z4,z5]),(0,[z1,z16,z15,z97,z4,z5]),(0,[z1,z16,z1079,z8,z4,z5])],[(0,[z1,z35,z53,z8,z4,z5]),(0,[z1,z1082,z2,z8,z4,z5]),(0,[z1,z8,z4,z5,z22,z1083]),(0,[z1,z362,z8,z4,z5,z126])],[(0,[z1,z2,z8,z4,z1084,z6]),(0,[z1,z2,z8,z4,z5,z1085]),(0,[z1,z2,z12,z8,z4,z22]),(0,[z49,z2,z8,z91,z5,z60]),(0,[z113,z2,z8,z4,z34,z10]),(0,[z1,z1086,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z1087,z5]),(0,[z1,z2,z8,z4,z1088,z6]),(0,[z1,z1089,z2,z8,z4,z5]),(0,[z1,z50,z440,z8,z127,z6])],[(0,[z1,z2,z8,z4,z5,z1090]),(0,[z1,z108,z8,z4,z5,z101]),(0,[z1,z2,z25,z8,z1091,z5])],[(1,[z808,z8,z4,z5,z6]),(0,[z1,z346,z16,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1092]),(0,[z1093,z2,z8,z4,z5,z6]),(0,[z1,z51,z8,z4,z357,z19]),(0,[z1,z334,z51,z2,z8,z6]),(0,[z1,z14,z8,z413,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1094]),(0,[z1,z2,z8,z370,z210,z6]),(0,[z65,z2,z33,z66,z4,z5]),(0,[z49,z2,z8,z1001,z5,z6]),(0,[z1,z108,z8,z69,z4,z5]),(0,[z1,z1095,z2,z8,z4,z10]),(0,[z1,z2,z1096,z8,z4,z5]),(0,[z1,z1097,z43,z8,z4,z5])],[(0,[z225,z1,z2,z8,z5,z462])],[]],
   [[(0,[z1,z108,z8,z4,z5,z23]),(0,[z1,z2,z8,z4,z1098,z5]),(0,[z1,z2,z8,z4,z5,z1099]),(0,[z1,z2,z4,z723,z5,z6]),(0,[z1,z27,z43,z8,z4,z5])],[],[(0,[z1,z2,z8,z846,z5,z6]),(0,[z117,z2,z356,z8,z4,z5]),(0,[z1,z2,z1100,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z1101]),(0,[z1,z362,z2,z8,z4,z5])],[(0,[z1,z742,z2,z8,z4,z5]),(0,[z1,z1102,z8,z4,z5,z6]),(0,[z1,z2,z8,z1103,z5,z6]),(0,[z1,z1104,z2,z8,z4,z5]),(0,[z2,z8,z4,z800,z75,z6]),(0,[z1,z16,z51,z8,z4,z19]),(0,[z1,z2,z8,z4,z5,z1105])],[(0,[z1,z2,z8,z4,z5,z1106]),(0,[z1,z2,z8,z1107,z5,z6]),(0,[z621,z2,z8,z68,z5,z6]),(0,[z1,z2,z1108,z8,z4,z5])],[(0,[z1,z2,z8,z4,z1109,z22]),(0,[z1,z2,z8,z85,z5,z238]),(0,[z1,z16,z2,z8,z455,z5])],[(0,[z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z1007,z5,z6]),(0,[z1,z43,z8,z4,z5,z75]),(0,[z1,z43,z8,z4,z5,z22]),(0,[z1,z16,z2,z4,z5,z381]),(0,[z1,z1110,z2,z8,z4,z5])],[(0,[z49,z1,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1111]),(0,[z1,z2,z73,z723,z5,z6]),(0,[z1,z2,z321,z4,z310,z274])],[(0,[z1,z1112,z2,z8,z4,z5]),(0,[z1,z2,z8,z410,z219,z6]),(0,[z1,z1113,z8,z4,z5,z6])],[(0,[z1,z1114,z2,z8,z4,z5])],[(0,[z1,z1115,z2,z8,z4,z6]),(0,[z1,z108,z8,z4,z5,z54]),(0,[z157,z1,z2,z25,z103,z5]),(0,[z1,z2,z8,z4,z1073,z6])],[(0,[z1,z2,z8,z4,z5,z1116]),(0,[z1,z2,z8,z4,z1117,z6]),(0,[z1,z2,z8,z4,z5,z1118]),(0,[z1,z1076,z25,z8,z4,z5]),(0,[z1,z43,z8,z1119,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1120]),(0,[z1,z24,z440,z8,z5,z6]),(0,[z1,z2,z8,z4,z1121,z5]),(0,[z1,z1122,z2,z8,z4,z5])],[(0,[z1,z1123,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z1124]),(0,[z1,z1125,z2,z8,z4,z5]),(0,[z1,z1126,z2,z8,z4,z5]),(0,[z1,z50,z2,z8,z127,z59])],[(0,[z273,z123,z2,z8,z4,z5]),(0,[z0,z1,z43,z8,z4,z5]),(0,[z157,z1,z2,z490,z4,z5]),(0,[z1,z8,z4,z5,z126,z6]),(0,[z1,z138,z43,z8,z4,z5])],[]],
   [[(0,[z1,z8,z4,z102,z819,z6])],[(0,[z1,z780,z8,z4,z5,z22]),(0,[z1,z2,z1127,z8,z4,z5])],[(0,[z1,z108,z8,z4,z5,z75]),(0,[z1,z108,z8,z4,z5,z22]),(0,[z1,z2,z8,z357,z455,z5]),(0,[z167,z365,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1128])],[(0,[z1,z83,z8,z4,z5,z22]),(0,[z1,z2,z8,z84,z4,z22]),(0,[z1,z1129,z2,z8,z5,z6]),(0,[z1,z135,z334,z2,z8,z6]),(0,[z1,z2,z8,z4,z1130,z5]),(0,[z1,z1131,z2,z8,z4,z5]),(0,[z1,z27,z2,z8,z4,z314])],[(0,[z1,z97,z603,z4,z5,z6]),(0,[z1,z1132,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z1133]),(0,[z1,z589,z2,z8,z4,z512]),(0,[z1,z1134,z2,z8,z4,z5]),(0,[z1,z8,z4,z1135,z5,z6])],[(0,[z112,z1,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z1136,z6]),(0,[z1,z14,z8,z4,z5,z126]),(0,[z1,z8,z4,z5,z6,z864]),(0,[z1,z16,z2,z8,z1137,z5])],[(0,[z89,z123,z8,z4,z5,z270])],[(0,[z1,z145,z2,z369,z4,z5]),(0,[z1,z2,z8,z4,z5,z1138]),(0,[z1,z288,z2,z191,z4,z5])],[(0,[z1,z604,z15,z8,z4,z5]),(0,[z1,z24,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z1139,z22]),(0,[z1,z2,z8,z4,z5,z1140]),(0,[z2,z356,z8,z4,z5,z10])],[(0,[z233,z2,z8,z4,z75,z234]),(0,[z1,z104,z2,z4,z105,z22]),(0,[z1,z1141,z2,z8,z4,z5]),(0,[z1,z43,z1131,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1142]),(0,[z1,z2,z25,z4,z492,z5]),(0,[z1,z2,z8,z4,z5,z1143]),(0,[z1,z50,z2,z25,z8,z127]),(0,[z1,z16,z2,z415,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1144]),(0,[z1,z2,z1100,z4,z5,z6]),(0,[z1,z15,z2,z355,z4,z5]),(0,[z1,z14,z254,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1145]),(0,[z1,z8,z4,z5,z90,z37])],[(0,[z1,z2,z25,z8,z4,z5]),(0,[z89,z1,z43,z8,z4,z5]),(0,[z1,z1146,z2,z8,z4,z5])]],
   [[(0,[z1,z14,z2,z8,z4,z5]),(0,[z1,z16,z43,z8,z4,z5]),(0,[z339,z128,z2,z8,z4,z5])],[(0,[z1,z57,z221,z8,z4,z5]),(0,[z1,z1147,z2,z8,z4,z5]),(0,[z1,z2,z52,z8,z4,z5]),(0,[z1,z43,z8,z4,z5,z6])],[(0,[z1,z108,z8,z66,z4,z5]),(0,[z1,z2,z12,z8,z168,z6]),(0,[z1,z1148,z2,z8,z4,z5]),(0,[z49,z2,z8,z437,z5,z6]),(0,[z1,z1149,z2,z8,z4,z5]),(0,[z1,z14,z266,z8,z4,z5]),(0,[z1,z1150,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z829])],[(0,[z1,z15,z86,z4,z5,z6]),(0,[z1,z83,z8,z4,z5,z198]),(0,[z1,z8,z4,z5,z126,z1040])],[(0,[z1,z2,z1151,z8,z4,z5]),(0,[z48,z2,z25,z8,z68,z5]),(0,[z113,z2,z8,z4,z34,z408]),(0,[z1,z2,z281,z4,z274,z6]),(0,[z1,z61,z69,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z1152]),(0,[z1,z16,z1061,z8,z4,z5])],[(0,[z136,z53,z8,z4,z5,z6]),(0,[z48,z14,z2,z8,z68,z5]),(0,[z1,z2,z8,z4,z5,z63])],[(0,[z1,z2,z1153,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1154]),(0,[z1,z1155,z2,z8,z4,z5])],[],[(0,[z1,z2,z8,z4,z1156,z5]),(0,[z65,z1,z43,z8,z4,z5]),(0,[z1,z61,z35,z8,z4,z5]),(0,[z1,z1157,z2,z8,z4,z5]),(0,[z1,z135,z8,z4,z102,z67]),(0,[z1,z8,z1158,z4,z5,z6]),(0,[z1,z128,z43,z8,z4,z5]),(0,[z1,z1159,z2,z8,z4,z5]),(0,[z1,z1160,z2,z8,z4,z5])],[(0,[z1,z108,z8,z4,z9,z5]),(0,[z1,z8,z4,z5,z90,z864])],[(0,[z1,z2,z8,z4,z1161,z5]),(0,[z1,z2,z8,z983,z4,z5]),(0,[z344,z1,z2,z8,z441,z5]),(0,[z1,z2,z8,z4,z152,z5])],[(0,[z1,z141,z8,z4,z5,z22]),(0,[z1,z2,z8,z595,z5,z326])],[(0,[z1,z2,z25,z8,z168,z5]),(0,[z1,z2,z8,z4,z5,z1162]),(0,[z1,z490,z8,z4,z5,z354]),(0,[z1,z57,z548,z8,z4,z5]),(0,[z157,z1,z2,z103,z5,z6]),(0,[z1,z16,z43,z4,z5,z29])],[(0,[z1,z14,z2,z8,z168,z5]),(0,[z1,z1163,z2,z8,z4,z5]),(0,[z1,z2,z1164,z8,z4,z5]),(0,[z1,z2,z1165,z8,z4,z5])],[(0,[z1,z14,z147,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1166]),(0,[z1,z1167,z2,z8,z4,z5]),(0,[z1,z1168,z2,z8,z4,z5]),(0,[z1,z57,z8,z4,z5,z126])],[(0,[z1,z14,z108,z8,z4,z5]),(0,[z48,z1,z43,z8,z4,z5])]],
   [[(0,[z1,z2,z25,z8,z410,z5]),(0,[z1,z2,z8,z4,z5,z1169]),(0,[z1,z367,z2,z8,z4,z6])],[(0,[z1,z1170,z2,z8,z4,z5]),(0,[z1,z1171,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1172]),(0,[z1,z440,z8,z4,z5,z59]),(0,[z1,z2,z8,z4,z1173,z5])],[(0,[z1,z2,z8,z4,z5,z1174]),(0,[z1,z211,z8,z4,z5,z90]),(0,[z1,z2,z8,z4,z5,z1175])],[(0,[z1,z604,z8,z69,z4,z5]),(0,[z1,z1176,z2,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1177]),(0,[z1,z51,z8,z455,z19,z6]),(0,[z1,z2,z8,z4,z5,z1178]),(0,[z1,z14,z2,z8,z4,z885]),(0,[z1,z2,z8,z4,z718,z54])],[(0,[z1,z2,z8,z4,z5,z1179]),(0,[z1180,z1,z2,z8,z5,z6]),(0,[z1,z2,z8,z4,z5,z1181])],[(0,[z1,z83,z8,z4,z219,z6]),(0,[z1,z2,z8,z4,z1139,z6]),(0,[z1,z1182,z2,z8,z4,z5]),(0,[z1,z1183,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1184]),(0,[z1,z61,z472,z69,z4,z5]),(0,[z1,z2,z25,z8,z4,z1024])],[],[(0,[z1,z1185,z2,z8,z5,z6])],[(0,[z1,z2,z321,z318,z4,z6]),(0,[z1,z745,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z1186,z5]),(0,[z1,z2,z8,z1187,z5,z6])],[(0,[z1,z1188,z2,z8,z4,z5]),(0,[z1,z2,z8,z5,z1189,z22]),(0,[z1,z2,z25,z76,z73,z5]),(0,[z165,z1,z43,z8,z4,z5])],[(0,[z112,z1,z14,z8,z4,z5]),(0,[z233,z2,z8,z4,z75,z22]),(0,[z1,z50,z2,z8,z127,z10]),(0,[z1,z50,z2,z8,z20,z6]),(0,[z1,z14,z2,z76,z73,z5]),(0,[z1,z2,z8,z4,z1190,z5]),(0,[z1,z2,z1191,z8,z4,z5])],[(0,[z1,z2,z1192,z8,z4,z5]),(0,[z1,z2,z8,z4,z1193,z5])],[(0,[z48,z57,z2,z8,z68,z5])],[(0,[z1,z2,z8,z4,z5,z1194]),(0,[z1,z182,z8,z4,z5,z22]),(0,[z1,z334,z2,z25,z8,z5]),(0,[z1,z2,z8,z4,z5,z1195])],[(0,[z89,z123,z8,z4,z5,z10]),(0,[z117,z8,z4,z5,z354,z22])],[(0,[z1,z2,z1196,z8,z4,z5]),(0,[z1,z16,z2,z8,z370,z5]),(0,[z1,z2,z8,z1197,z5,z6]),(0,[z1,z2,z8,z4,z5,z1198]),(0,[z1,z1199,z2,z8,z4,z5])]],
   [[(0,[z1,z43,z8,z4,z5,z37]),(0,[z1,z2,z8,z4,z5,z1200])],[(0,[z1,z2,z1201,z8,z4,z5]),(0,[z1,z1202,z2,z8,z4,z5]),(0,[z1,z43,z8,z70,z4,z5]),(0,[z1,z2,z25,z8,z4,z1203])],[(0,[z89,z1,z14,z8,z4,z5]),(0,[z1,z1204,z2,z8,z4,z5]),(0,[z1,z2,z1205,z8,z4,z5]),(0,[z1,z1206,z2,z8,z4,z5]),(0,[z1,z24,z8,z84,z9,z6]),(1,[z1,z8,z4,z5,z864])],[(0,[z1,z8,z4,z5,z1207,z6]),(0,[z1,z14,z8,z4,z5,z203])],[(0,[z1,z57,z2,z8,z168,z5]),(0,[z48,z2,z8,z68,z5,z22]),(0,[z1,z2,z8,z4,z5,z1208]),(0,[z1,z1183,z108,z8,z4,z5]),(0,[z1,z1209,z8,z4,z5,z22]),(0,[z1,z81,z8,z4,z5,z257]),(0,[z1,z135,z367,z8,z4,z6])],[(0,[z1,z2,z8,z4,z1210,z6]),(0,[z1,z2,z8,z410,z5,z6]),(0,[z1,z2,z8,z4,z5,z1211]),(0,[z58,z2,z8,z4,z75,z6]),(0,[z1,z2,z8,z4,z164,z54]),(0,[z1,z43,z8,z4,z78,z5])],[(0,[z1,z2,z8,z4,z5,z1212])],[(0,[z1,z2,z8,z1001,z5,z6]),(0,[z1,z16,z2,z337,z4,z5]),(0,[z1,z1037,z440,z8,z4,z5])],[(0,[z1,z2,z8,z1213,z5,z6]),(0,[z199,z1,z2,z8,z5,z22]),(0,[z1,z1214,z2,z8,z4,z5])],[(0,[z1,z33,z183,z8,z4,z5]),(0,[z1,z1215,z43,z8,z4,z5]),(0,[z1,z1216,z8,z4,z5,z6])],[(0,[z1,z1217,z2,z8,z4,z5]),(0,[z1,z14,z62,z8,z4,z5]),(0,[z1,z16,z43,z25,z4,z5])],[(0,[z1,z2,z8,z4,z731,z6]),(0,[z1,z2,z8,z4,z823,z6]),(0,[z1,z2,z8,z4,z5,z1218])],[(0,[z65,z138,z2,z8,z4,z5]),(0,[z1,z1219,z2,z8,z4,z5]),(0,[z1,z14,z473,z8,z4,z5]),(0,[z1,z211,z266,z8,z4,z5]),(0,[z1,z1220,z2,z8,z4,z5])],[(0,[z2,z8,z4,z5,z121,z10]),(0,[z1,z2,z8,z4,z5,z1221])],[(0,[z1,z2,z8,z4,z1222,z5]),(0,[z1,z108,z8,z4,z5,z476]),(0,[z1,z1223,z8,z4,z5,z22]),(0,[z1,z1224,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z1225,z5]),(0,[z1,z2,z1226,z8,z4,z5]),(0,[z138,z2,z8,z4,z5,z22]),(0,[z1,z1227,z2,z8,z4,z5]),(0,[z1,z2,z8,z242,z5,z101]),(0,[z1,z2,z8,z85,z5,z829])]],
   [[(0,[z1,z8,z4,z5,z354,z270]),(0,[z1,z2,z8,z455,z5,z10]),(0,[z1,z77,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1228]),(0,[z1,z484,z2,z8,z4,z341]),(0,[z1,z16,z2,z321,z4,z274])],[(0,[z8,z4,z5,z354,z10,z22])],[(0,[z1,z61,z2,z355,z4,z5])],[(0,[z1,z1053,z83,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1229]),(0,[z1,z2,z490,z4,z5,z416]),(0,[z1230,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1203,z6]),(0,[z48,z2,z8,z68,z5,z196]),(0,[z1,z1231,z2,z8,z4,z5]),(0,[z1,z145,z2,z4,z5,z29]),(0,[z1,z50,z2,z8,z662,z6]),(0,[z453,z1,z43,z8,z4,z5]),(0,[z44,z1,z2,z8,z658,z5])],[(0,[z1,z276,z2,z33,z8,z4]),(0,[z1,z2,z1232,z8,z4,z5])],[(0,[z1,z43,z8,z91,z4,z5]),(0,[z1,z2,z8,z4,z1233,z5]),(0,[z1,z1234,z2,z8,z4,z5])],[(0,[z112,z273,z2,z8,z4,z5]),(0,[z1,z135,z8,z4,z402,z102])],[(0,[z1,z178,z2,z8,z4,z5]),(0,[z1,z2,z12,z8,z4,z6]),(0,[z1,z46,z8,z4,z5,z587]),(0,[z1,z942,z8,z4,z5,z10]),(0,[z1,z14,z15,z8,z4,z5]),(0,[z1,z77,z61,z69,z4,z5]),(0,[z1,z182,z8,z4,z5,z6]),(0,[z1,z671,z50,z2,z8,z6]),(0,[z1,z2,z8,z4,z5,z1235]),(0,[z1,z2,z8,z4,z5,z1236]),(0,[z1,z2,z1237,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1238]),(0,[z1,z2,z8,z4,z5,z17]),(0,[z2,z8,z4,z5,z22,z133]),(0,[z44,z1,z2,z8,z441,z5]),(0,[z1,z2,z8,z4,z5,z1239])],[(0,[z1,z2,z33,z12,z8,z4]),(0,[z1,z2,z1240,z4,z5,z6]),(0,[z1,z8,z69,z4,z5,z197]),(0,[z1,z43,z8,z4,z274,z5]),(0,[z1,z16,z2,z8,z4,z1241]),(0,[z1,z2,z8,z85,z5,z358])],[(0,[z1,z2,z8,z4,z5,z1242]),(0,[z1,z221,z8,z4,z5,z22]),(0,[z1,z2,z8,z1091,z5,z6]),(0,[z263,z1,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1243]),(0,[z1,z2,z1244,z8,z4,z5]),(0,[z1,z1245,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1246]),(0,[z1,z50,z2,z8,z259,z127])],[(0,[z1,z24,z109,z8,z9,z5]),(0,[z1,z2,z8,z4,z5,z67])],[(0,[z1,z1247,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1248]),(0,[z65,z2,z25,z66,z4,z5]),(0,[z1,z14,z2,z8,z1000,z5]),(0,[z1,z2,z8,z4,z5,z1249])],[(0,[z65,z14,z2,z66,z4,z5]),(0,[z1,z2,z1250,z8,z4,z5]),(0,[z1,z43,z3,z8,z4,z5]),(0,[z1,z440,z8,z4,z5,z10]),(0,[z1,z340,z2,z8,z4,z131]),(0,[z1,z1251,z2,z8,z4,z5]),(0,[z1,z2,z25,z4,z5,z773])],[(0,[z89,z112,z14,z8,z4,z5]),(0,[z112,z53,z8,z4,z5,z10]),(0,[z2,z989,z66,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1252]),(0,[z1,z50,z141,z8,z5,z6])]],
   [[(0,[z1,z1253,z8,z4,z5,z126])],[(0,[z1,z1254,z2,z8,z4,z5]),(0,[z1,z43,z123,z8,z4,z5]),(0,[z1,z1255,z2,z8,z4,z5]),(0,[z1,z14,z81,z8,z4,z5]),(0,[z1,z2,z8,z4,z1256,z5]),(0,[z1,z14,z160,z8,z70,z5])],[(0,[z1,z108,z8,z91,z4,z5]),(0,[z1,z108,z490,z8,z4,z5]),(1,[z1,z334,z51,z8,z6]),(0,[z1,z57,z8,z4,z5,z90])],[(0,[z1,z2,z8,z4,z5,z1257]),(0,[z1,z2,z8,z4,z1109,z6]),(0,[z1,z160,z8,z70,z5,z22]),(0,[z1,z108,z8,z595,z4,z5]),(0,[z688,z2,z8,z4,z5,z10]),(0,[z1,z16,z2,z8,z1258,z5])],[(0,[z1,z183,z8,z4,z5,z824]),(0,[z1,z2,z8,z4,z5,z1259]),(0,[z1,z2,z8,z4,z5,z1260]),(0,[z1,z810,z69,z4,z5,z6]),(0,[z1,z1261,z2,z8,z4,z5])],[(0,[z199,z1,z346,z8,z5,z6]),(0,[z1,z1262,z2,z8,z4,z5]),(0,[z117,z365,z2,z8,z4,z5]),(0,[z528,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z1263,z5]),(0,[z1,z362,z141,z8,z4,z5])],[(0,[z112,z1,z604,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1264]),(0,[z1,z1265,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z1266])],[(0,[z2,z369,z356,z8,z4,z5]),(0,[z1,z27,z2,z8,z4,z512]),(0,[z1,z15,z43,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1267]),(0,[z1,z2,z8,z4,z5,z1268])],[(0,[z1,z2,z8,z119,z969,z6])],[(0,[z112,z250,z8,z4,z5,z6]),(0,[z1,z1269,z2,z8,z4,z5])],[(0,[z1,z221,z8,z4,z5,z198]),(0,[z1,z108,z3,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1270])],[(0,[z1,z2,z1271,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1272])],[(0,[z89,z14,z123,z8,z4,z5]),(0,[z1,z2,z186,z73,z5,z6]),(0,[z2,z8,z4,z5,z31,z10]),(0,[z1,z27,z2,z8,z4,z628]),(0,[z1,z2,z652,z8,z4,z253]),(0,[z1,z1273,z2,z8,z4,z5])],[(0,[z808,z53,z8,z4,z5,z6])],[(0,[z89,z1,z604,z8,z4,z5]),(0,[z1,z83,z8,z410,z5,z6]),(0,[z1,z14,z8,z110,z4,z5]),(0,[z1,z2,z8,z5,z101,z829])],[(0,[z1,z2,z989,z4,z5,z6]),(0,[z1,z2,z1274,z8,z4,z5]),(0,[z1,z780,z8,z4,z5,z6]),(0,[z1,z81,z97,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1275]),(0,[z1,z2,z25,z8,z119,z78])]],
   [[(0,[z1,z108,z8,z4,z5,z6]),(0,[z65,z2,z66,z4,z5,z22]),(0,[z610,z2,z8,z4,z5,z22]),(0,[z1276,z2,z8,z4,z5,z6]),(0,[z1,z2,z1277,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1278]),(0,[z1,z2,z8,z4,z5,z1279]),(0,[z1,z108,z8,z4,z5,z381]),(0,[z1,z14,z8,z69,z4,z5]),(0,[z1,z182,z25,z8,z4,z5])],[(0,[z1,z83,z8,z4,z5,z6]),(0,[z1,z14,z183,z8,z4,z5]),(0,[z199,z1,z2,z33,z8,z5]),(0,[z1,z145,z2,z25,z4,z5]),(0,[z1,z2,z8,z84,z4,z6]),(0,[z1,z1280,z2,z8,z4,z5]),(0,[z1,z35,z450,z8,z4,z5]),(0,[z1,z1281,z8,z4,z5,z6])],[(0,[z1,z104,z2,z406,z4,z6])],[(0,[z1,z14,z2,z8,z410,z5]),(0,[z1,z1282,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1283]),(0,[z1,z15,z355,z4,z5,z6]),(0,[z1,z35,z97,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1284])],[(0,[z199,z1,z276,z2,z8,z6]),(0,[z1,z24,z367,z8,z4,z6])],[(0,[z1,z8,z4,z5,z354,z10]),(0,[z2,z8,z4,z202,z5,z10]),(0,[z1,z2,z8,z4,z5,z1285])],[(0,[z1,z2,z25,z12,z8,z4]),(0,[z113,z2,z8,z4,z34,z107]),(0,[z561,z46,z2,z8,z4,z5]),(0,[z1,z43,z8,z4,z1286,z5])],[(0,[z2,z8,z4,z1287,z5,z6]),(0,[z1,z2,z8,z4,z5,z1288]),(0,[z1,z57,z160,z8,z70,z5]),(0,[z1,z43,z8,z73,z4,z5])],[(0,[z1,z8,z707,z9,z5,z6]),(0,[z1,z2,z1289,z8,z4,z5]),(0,[z1,z104,z2,z4,z105,z6])],[(0,[z1,z57,z2,z8,z4,z5]),(0,[z1,z50,z108,z8,z4,z5]),(0,[z1,z104,z2,z4,z1073,z6]),(0,[z1,z2,z321,z4,z274,z162])],[(0,[z1,z8,z4,z5,z882,z10]),(0,[z1,z1290,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1291])],[(0,[z1,z221,z8,z4,z219,z6]),(0,[z1,z16,z2,z8,z4,z210]),(0,[z1,z2,z8,z4,z1292,z5]),(0,[z1,z57,z266,z8,z4,z5]),(0,[z1,z1293,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1294,z5]),(0,[z1,z43,z25,z8,z4,z5])],[(0,[z1,z2,z8,z4,z219,z226]),(0,[z117,z2,z8,z4,z5,z22]),(0,[z1,z166,z43,z8,z4,z5])],[(0,[z1,z1295,z2,z8,z4,z5]),(0,[z65,z2,z66,z4,z5,z198]),(0,[z1,z241,z2,z8,z4,z5]),(0,[z1,z228,z2,z52,z4,z5]),(0,[z1,z2,z8,z4,z5,z1296]),(0,[z1,z2,z4,z5,z1073,z6]),(0,[z1,z2,z8,z1137,z5,z6]),(0,[z1,z448,z2,z25,z4,z5])]],
   [[(0,[z1,z14,z8,z4,z169,z5]),(0,[z1,z16,z2,z8,z84,z4]),(0,[z1,z57,z659,z8,z4,z5])],[(0,[z1,z2,z8,z1258,z5,z6]),(0,[z1,z1265,z8,z4,z5,z6]),(0,[z1,z2,z1297,z8,z4,z5]),(0,[z1,z51,z8,z524,z4,z6]),(0,[z1,z16,z816,z8,z4,z5])],[(0,[z1,z135,z8,z4,z102,z10]),(0,[z1,z109,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1298]),(0,[z1,z2,z1299,z8,z4,z5]),(0,[z1,z2,z8,z4,z1300,z5])],[(1,[z112,z365,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1301]),(0,[z1,z2,z8,z4,z1302,z5]),(0,[z532,z1,z2,z8,z5,z476]),(0,[z1,z2,z1303,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1304]),(0,[z1,z14,z141,z8,z4,z5])],[(0,[z112,z53,z8,z4,z5,z306]),(0,[z1,z367,z8,z4,z19,z6]),(0,[z1,z2,z8,z4,z5,z1305]),(0,[z1,z43,z8,z4,z5,z105]),(0,[z1,z16,z2,z8,z1306,z5])],[(0,[z625,z2,z8,z4,z5,z10]),(0,[z206,z1,z2,z8,z4,z556]),(0,[z1,z16,z1170,z8,z4,z5])],[(0,[z1,z2,z1307,z8,z4,z5]),(0,[z2,z8,z4,z5,z22,z215]),(0,[z1,z288,z35,z8,z4,z5])],[(0,[z1,z2,z8,z370,z5,z198]),(0,[z1,z2,z8,z4,z5,z1308])],[(0,[z44,z1,z2,z8,z248,z5])],[(0,[z89,z299,z8,z4,z5,z6]),(0,[z1,z57,z183,z8,z4,z5]),(0,[z1,z565,z2,z4,z105,z6]),(0,[z1,z108,z25,z8,z4,z5]),(0,[z1,z141,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z59])],[(0,[z808,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z861,z6]),(0,[z1,z2,z8,z4,z144,z285]),(0,[z1,z14,z15,z191,z4,z5]),(0,[z1,z2,z1309,z8,z4,z5])],[(0,[z1,z83,z25,z8,z4,z5]),(0,[z1,z57,z2,z8,z410,z5]),(0,[z1,z145,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z143]),(0,[z1,z2,z8,z4,z800,z6]),(0,[z1,z24,z14,z8,z9,z5]),(0,[z1,z334,z51,z8,z19,z6]),(0,[z1,z146,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1310])],[(0,[z1,z2,z1311,z4,z5,z6]),(0,[z1,z2,z8,z4,z210,z22]),(0,[z1,z241,z2,z8,z168,z5]),(0,[z1,z2,z8,z4,z5,z1312]),(0,[z1,z1313,z2,z8,z4,z5]),(0,[z1,z2,z25,z4,z489,z5])],[(0,[z1,z128,z1170,z8,z4,z5]),(0,[z1,z1314,z2,z8,z4,z5])],[(0,[z1,z241,z183,z8,z4,z5]),(0,[z1,z2,z8,z5,z1315,z6]),(0,[z2,z8,z4,z5,z1316,z6]),(0,[z1,z8,z4,z819,z19,z6]),(0,[z1,z1317,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z718,z5])],[(0,[z1,z2,z8,z4,z1318,z22])]],
   [[(0,[z1,z108,z8,z70,z4,z5]),(0,[z1,z160,z440,z8,z5,z6]),(0,[z1,z14,z440,z8,z4,z5])],[(0,[z1,z2,z1319,z8,z4,z5]),(0,[z65,z2,z66,z4,z219,z6]),(0,[z1,z104,z43,z8,z4,z5]),(0,[z1,z16,z1293,z8,z4,z5]),(0,[z1,z1320,z2,z8,z4,z5])],[(0,[z1,z14,z83,z8,z4,z5]),(0,[z1,z1321,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1322]),(0,[z1,z16,z2,z459,z4,z5]),(0,[z1,z2,z8,z4,z819,z6]),(0,[z1,z968,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z829,z6])],[(1,[z1,z2,z4,z1073,z6]),(0,[z1,z141,z8,z78,z5,z6])],[(0,[z1,z2,z76,z156,z5,z6]),(0,[z1,z108,z8,z4,z78,z5]),(0,[z1,z2,z25,z191,z4,z5]),(0,[z1,z1323,z2,z8,z4,z5]),(0,[z1,z57,z2,z76,z73,z5]),(0,[z1,z2,z8,z4,z5,z162])],[(0,[z1,z1324,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1325]),(0,[z1,z2,z8,z4,z1326,z6]),(0,[z1,z8,z1327,z4,z5,z6])],[(0,[z65,z2,z12,z66,z4,z6]),(0,[z1,z2,z1328,z8,z4,z5]),(0,[z113,z2,z435,z8,z4,z6]),(0,[z1,z2,z8,z4,z1329,z5]),(0,[z1,z8,z4,z1330,z5,z6])],[(0,[z1,z2,z1331,z8,z4,z5]),(0,[z1,z2,z8,z5,z1189,z6]),(0,[z1,z14,z7,z8,z4,z5]),(0,[z1,z1170,z8,z4,z5,z22]),(0,[z1,z2,z8,z85,z419,z5]),(0,[z1,z43,z8,z4,z5,z30])],[(0,[z233,z2,z8,z4,z75,z6]),(1,[z1,z15,z355,z4,z5]),(0,[z1,z135,z440,z8,z4,z6]),(0,[z1,z2,z8,z4,z1332,z5])],[(0,[z1,z2,z8,z370,z219,z6]),(0,[z1,z2,z8,z4,z5,z1333]),(0,[z1,z24,z8,z227,z9,z5]),(0,[z1,z16,z2,z396,z4,z5]),(0,[z1,z2,z8,z4,z718,z6])],[(0,[z2,z8,z989,z4,z5,z6]),(1,[z1,z24,z367,z8,z6])],[(0,[z1,z2,z8,z4,z210,z198]),(0,[z1,z2,z8,z5,z1334,z6]),(0,[z1,z2,z8,z4,z5,z791]),(0,[z1,z1335,z108,z8,z4,z5]),(0,[z1,z43,z8,z4,z352,z5])],[(0,[z1,z14,z742,z8,z4,z5]),(0,[z1,z2,z8,z4,z1241,z6]),(0,[z1,z2,z8,z114,z5,z238]),(0,[z1,z1336,z2,z8,z4,z5]),(0,[z1,z16,z947,z8,z4,z5])],[(0,[z89,z8,z4,z5,z216,z6]),(0,[z1,z2,z8,z1337,z5,z6]),(0,[z1,z183,z8,z4,z5,z22]),(0,[z1,z670,z2,z355,z4,z5])],[(0,[z65,z1,z108,z8,z4,z5]),(0,[z49,z2,z8,z91,z5,z22])],[(0,[z1,z2,z8,z4,z5,z1338]),(0,[z1,z1339,z2,z8,z4,z5])]],
   [[(1,[z2,z8,z1001,z5,z6]),(0,[z1,z2,z8,z4,z1340,z5]),(0,[z1,z97,z810,z4,z5,z6]),(0,[z1,z367,z440,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z1341]),(0,[z1,z1342,z2,z8,z4,z5]),(0,[z1,z43,z8,z4,z137,z5]),(0,[z1,z2,z8,z4,z1343,z5])],[(0,[z1,z2,z8,z4,z1344,z5]),(0,[z1,z1345,z2,z8,z4,z5]),(0,[z1,z27,z2,z8,z4,z718])],[(0,[z1,z2,z8,z4,z5,z1346]),(0,[z1,z2,z490,z66,z4,z5]),(0,[z48,z2,z8,z68,z5,z6]),(0,[z1,z1209,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z195]),(0,[z1,z1077,z8,z4,z5,z6]),(0,[z1,z141,z25,z8,z4,z5]),(0,[z1,z16,z2,z4,z5,z275]),(1,[z1,z2,z8,z969,z6])],[(0,[z1,z43,z53,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1347]),(0,[z1,z1348,z8,z4,z5,z6]),(0,[z1,z108,z8,z4,z5,z30])],[(0,[z1,z2,z8,z4,z5,z1349]),(0,[z1,z276,z2,z8,z4,z22]),(0,[z1,z108,z8,z4,z5,z354]),(0,[z1,z51,z25,z8,z4,z19]),(0,[z1,z1350,z2,z8,z4,z5]),(0,[z1,z1351,z2,z8,z4,z5])],[(0,[z1,z346,z8,z4,z5,z22]),(0,[z1,z1352,z2,z8,z4,z5]),(0,[z0,z1,z733,z8,z4,z5]),(0,[z1,z1353,z2,z8,z4,z5]),(0,[z1,z1354,z2,z8,z4,z5]),(0,[z1,z2,z76,z73,z5,z10]),(0,[z1,z135,z25,z8,z4,z102])],[(0,[z112,z14,z53,z8,z4,z5]),(0,[z199,z1,z2,z8,z5,z6]),(0,[z1,z2,z8,z4,z5,z1048]),(0,[z1,z2,z8,z4,z5,z1355]),(0,[z1,z2,z4,z5,z1356,z22]),(0,[z1,z2,z8,z4,z5,z1357])],[(0,[z1,z2,z8,z4,z5,z1358]),(0,[z138,z2,z3,z8,z4,z5])],[(0,[z233,z677,z2,z8,z4,z6]),(0,[z1,z16,z840,z8,z4,z5])],[(0,[z1,z1359,z2,z8,z4,z5]),(0,[z113,z2,z8,z4,z34,z22]),(0,[z1,z108,z8,z4,z274,z5])],[(0,[z1,z2,z8,z4,z1318,z6]),(1,[z1,z43,z8,z4,z5]),(0,[z1,z24,z57,z8,z9,z5])],[(0,[z1,z311,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z1360,z6]),(0,[z112,z604,z53,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1361]),(0,[z1,z2,z1362,z8,z4,z5]),(0,[z1,z2,z8,z119,z479,z6]),(0,[z1,z968,z25,z8,z4,z5])],[(0,[z1,z2,z1363,z8,z4,z5]),(0,[z1,z1223,z8,z4,z5,z6]),(0,[z1,z108,z8,z4,z137,z5]),(0,[z1,z2,z8,z4,z5,z1364])],[(0,[z1,z2,z1365,z8,z4,z5])],[(0,[z1,z108,z311,z8,z4,z5]),(0,[z233,z2,z25,z8,z4,z75])],[(0,[z1,z108,z53,z8,z4,z5]),(0,[z1,z2,z8,z1366,z5,z6]),(0,[z1,z2,z1367,z8,z4,z5]),(0,[z233,z14,z2,z8,z4,z75]),(0,[z1,z2,z25,z322,z4,z5]),(0,[z2,z8,z4,z5,z10,z22]),(0,[z1,z598,z2,z8,z4,z131])]],
   [[(0,[z116,z1,z14,z8,z4,z5]),(0,[z1,z108,z123,z8,z4,z5]),(0,[z128,z138,z2,z8,z4,z5]),(0,[z1,z288,z2,z355,z4,z5]),(0,[z1,z2,z8,z4,z5,z1368]),(0,[z1,z367,z2,z25,z8,z4]),(0,[z1,z8,z4,z819,z5,z6])],[(0,[z1,z1369,z2,z8,z4,z5]),(0,[z1,z14,z640,z8,z4,z5]),(1,[z2,z8,z4,z5,z791]),(0,[z1,z1224,z141,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1370]),(0,[z1,z16,z2,z4,z5,z11]),(0,[z1,z43,z8,z4,z5,z45])],[(0,[z1,z1371,z2,z8,z4,z5]),(0,[z1,z355,z8,z69,z4,z5]),(0,[z1,z14,z2,z8,z119,z78]),(0,[z1,z43,z43,z8,z4,z5]),(0,[z1,z2,z1372,z8,z4,z5])],[(0,[z1,z16,z221,z8,z4,z5]),(0,[z1,z2,z8,z707,z5,z6]),(0,[z1,z2,z8,z4,z5,z1373])],[(0,[z112,z14,z365,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1374]),(0,[z1,z2,z8,z4,z1375,z5]),(0,[z1,z334,z2,z8,z357,z5]),(0,[z1,z2,z8,z4,z5,z1376]),(0,[z1,z16,z1377,z8,z4,z5])],[(1,[z1,z942,z8,z4,z5]),(0,[z1,z383,z57,z8,z4,z5])],[(0,[z1,z2,z8,z4,z1378,z6]),(0,[z1,z2,z8,z410,z5,z226]),(0,[z1,z2,z8,z4,z1379,z6]),(0,[z113,z2,z8,z4,z800,z6])],[(0,[z65,z57,z2,z66,z4,z5]),(0,[z1,z138,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1380])],[(0,[z1,z221,z8,z4,z5,z6])],[(0,[z273,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z1381]),(0,[z1,z8,z4,z102,z345,z6]),(0,[z1382,z1,z43,z8,z4,z5]),(0,[z1,z182,z8,z4,z5,z63])],[(0,[z1,z1383,z2,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z226]),(0,[z1,z2,z8,z370,z5,z22]),(0,[z1,z14,z2,z12,z8,z4]),(0,[z1,z14,z182,z8,z4,z5]),(0,[z453,z138,z2,z8,z4,z5])],[(0,[z1,z1384,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z219,z10]),(0,[z1,z346,z33,z8,z4,z5]),(0,[z1,z108,z8,z1385,z4,z5])],[(0,[z65,z241,z2,z66,z4,z5]),(0,[z1,z15,z97,z4,z5,z10]),(0,[z225,z1,z2,z8,z5,z101]),(0,[z1,z1386,z2,z8,z4,z5])],[(0,[z1,z1387,z2,z8,z4,z5]),(0,[z1,z108,z365,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1388])],[(0,[z1,z108,z8,z4,z1389,z5]),(0,[z1,z2,z8,z119,z78,z22]),(0,[z1,z24,z8,z9,z5,z10]),(0,[z1,z2,z8,z4,z5,z1390]),(0,[z1,z2,z8,z4,z5,z1391])]],
   [[(0,[z65,z2,z356,z8,z4,z5]),(0,[z49,z1,z108,z8,z4,z5]),(0,[z113,z1,z43,z8,z4,z5]),(0,[z1,z14,z8,z4,z5,z37])],[(0,[z1,z276,z346,z8,z4,z6]),(0,[z1,z51,z8,z4,z19,z22]),(0,[z1,z160,z8,z70,z5,z6]),(0,[z1,z16,z8,z4,z5,z126])],[(0,[z80,z2,z8,z4,z5,z10]),(0,[z1,z1392,z2,z8,z4,z5]),(0,[z1,z24,z8,z20,z5,z6])],[(0,[z157,z1,z146,z2,z103,z5])],[(0,[z1,z2,z8,z1393,z5,z6]),(0,[z1,z14,z8,z4,z544,z5]),(0,[z2,z8,z4,z5,z216,z10]),(0,[z1,z2,z8,z4,z741,z6]),(0,[z1,z24,z367,z2,z8,z6]),(0,[z1,z2,z8,z4,z1394,z6]),(0,[z1,z2,z8,z4,z5,z1395]),(0,[z1,z1396,z2,z8,z4,z5]),(0,[z1,z2,z8,z85,z5,z45])],[(0,[z1,z2,z8,z4,z1397,z5]),(0,[z1,z2,z25,z4,z5,z347])],[(0,[z89,z57,z123,z8,z4,z5]),(0,[z233,z57,z2,z8,z4,z75]),(1,[z1,z8,z707,z5,z6]),(0,[z1,z50,z24,z51,z8,z6]),(0,[z1,z14,z8,z4,z297,z5])],[(0,[z46,z365,z2,z8,z4,z5]),(0,[z0,z1,z108,z8,z4,z5]),(0,[z1,z2,z1398,z8,z4,z5]),(0,[z1,z108,z8,z73,z4,z5]),(0,[z1,z2,z1399,z8,z4,z5]),(0,[z674,z1,z2,z8,z419,z5])],[(0,[z1,z1400,z8,z4,z5,z6]),(0,[z1,z1401,z2,z8,z4,z5])],[(0,[z1,z266,z8,z4,z5,z10])],[(0,[z1,z2,z1402,z8,z4,z5]),(0,[z1,z411,z51,z8,z4,z19]),(0,[z1,z57,z2,z8,z119,z78]),(0,[z1,z1280,z182,z8,z4,z5])],[(0,[z1,z14,z228,z8,z4,z5]),(0,[z1,z14,z8,z4,z5,z864]),(0,[z157,z1,z2,z152,z103,z5])],[(0,[z1,z8,z4,z5,z90,z270]),(0,[z1,z1403,z8,z4,z5,z6]),(0,[z1,z733,z8,z4,z5,z343]),(0,[z2,z8,z4,z5,z642,z22]),(0,[z96,z1,z43,z8,z4,z5]),(0,[z1,z2,z1404,z8,z4,z5])],[(0,[z1,z2,z25,z8,z4,z219]),(0,[z1,z2,z8,z4,z5,z1405]),(0,[z1,z2,z1406,z8,z4,z6])],[(0,[z65,z2,z66,z4,z5,z6]),(0,[z1,z14,z2,z8,z4,z219]),(1,[z1,z1076,z8,z4,z5])],[(0,[z1,z2,z8,z1407,z5,z6]),(0,[z1,z2,z8,z4,z5,z1408]),(0,[z48,z16,z2,z8,z68,z5]),(0,[z1,z2,z25,z4,z5,z468]),(0,[z1,z24,z16,z8,z9,z5]),(0,[z1,z364,z2,z8,z4,z628]),(0,[z1,z2,z4,z1073,z105,z6])]],
   [[(0,[z112,z1,z108,z8,z4,z5]),(0,[z1,z2,z8,z1409,z5,z6]),(0,[z1,z1410,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z1411,z5]),(0,[z258,z1,z14,z8,z4,z5])],[(0,[z1,z2,z8,z1412,z5,z22]),(0,[z1,z8,z810,z4,z5,z6]),(0,[z1,z2,z1413,z8,z4,z5]),(0,[z1,z367,z8,z70,z4,z6])],[(0,[z1,z221,z25,z8,z4,z5]),(0,[z1,z128,z2,z8,z4,z5]),(0,[z1,z57,z2,z12,z8,z4]),(0,[z1,z1414,z2,z8,z4,z5]),(0,[z1,z1415,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1416]),(0,[z1,z2,z1417,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1418]),(0,[z1,z57,z182,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z270]),(0,[z1,z108,z8,z4,z5,z105]),(0,[z1,z2,z8,z4,z5,z1419]),(0,[z96,z2,z8,z4,z5,z791])],[(0,[z1,z273,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z1420,z5]),(0,[z1,z1421,z8,z4,z5,z6]),(0,[z1,z128,z266,z8,z4,z5])],[(0,[z1,z14,z8,z4,z5,z354])],[(0,[z1,z2,z8,z370,z5,z6]),(0,[z1,z2,z1422,z8,z4,z5]),(0,[z1,z14,z547,z8,z4,z5]),(0,[z1,z16,z2,z4,z5,z29])],[(0,[z1,z16,z2,z8,z168,z5]),(0,[z1,z241,z2,z12,z8,z4])],[(0,[z89,z1,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1423]),(0,[z1,z16,z266,z4,z5,z29]),(0,[z1,z50,z362,z2,z8,z127])],[(0,[z1,z81,z8,z4,z5,z90]),(0,[z1,z50,z141,z8,z4,z6]),(0,[z1,z27,z2,z8,z4,z194])],[(0,[z1,z1424,z2,z8,z4,z5]),(0,[z1,z2,z8,z119,z78,z6])],[(0,[z1,z2,z8,z4,z5,z306]),(0,[z1,z276,z241,z2,z8,z4]),(0,[z1,z887,z8,z4,z5,z6]),(0,[z1,z2,z8,z189,z5,z101]),(0,[z1,z335,z43,z8,z4,z5]),(0,[z1,z1159,z440,z8,z4,z5]),(0,[z1,z182,z8,z4,z5,z59])],[(0,[z1,z1425,z2,z4,z5,z6]),(0,[z157,z1,z2,z103,z5,z10]),(0,[z1,z2,z211,z8,z4,z5]),(0,[z1,z51,z8,z4,z19,z6]),(0,[z1,z2,z72,z8,z4,z5]),(0,[z1,z16,z2,z8,z4,z1426])],[(0,[z1,z14,z15,z69,z4,z5]),(0,[z1,z57,z141,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1427])],[(0,[z1,z8,z4,z5,z1428,z6]),(0,[z49,z2,z25,z8,z91,z5]),(0,[z1,z35,z8,z4,z5,z90])],[(0,[z1,z276,z57,z2,z8,z4]),(0,[z1,z8,z4,z5,z1018,z6]),(0,[z49,z14,z2,z8,z91,z5]),(0,[z1,z2,z321,z4,z274,z10]),(0,[z1,z61,z43,z8,z4,z5]),(0,[z1,z43,z8,z4,z1429,z5]),(0,[z1,z378,z2,z8,z5,z101])]],
   [[(0,[z1,z2,z8,z4,z5,z1430]),(0,[z1,z367,z2,z8,z4,z10]),(0,[z1,z2,z8,z4,z5,z1431]),(0,[z1,z1432,z2,z8,z4,z5]),(0,[z1,z8,z4,z5,z1433,z6])],[(0,[z1,z2,z8,z4,z5,z1434]),(0,[z1,z1400,z25,z8,z4,z5])],[(0,[z1,z2,z8,z168,z5,z10]),(0,[z1,z1435,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1436]),(0,[z1,z14,z8,z4,z5,z495]),(0,[z1,z265,z57,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1437])],[(0,[z1,z2,z8,z4,z1438,z5]),(0,[z1,z2,z8,z4,z5,z1439])],[(0,[z1,z83,z8,z4,z5,z226]),(1,[z2,z8,z4,z800,z6]),(0,[z1,z16,z2,z309,z4,z5]),(0,[z1,z942,z2,z8,z4,z5]),(0,[z1,z77,z2,z52,z4,z5]),(0,[z1,z15,z25,z97,z4,z5]),(0,[z1,z43,z8,z4,z5,z56]),(0,[z1,z2,z8,z4,z5,z1440]),(0,[z1,z2,z8,z414,z5,z45])],[(0,[z1,z2,z8,z4,z5,z1441]),(0,[z1,z57,z2,z8,z4,z219]),(0,[z1,z334,z160,z8,z5,z6])],[(0,[z1,z1442,z2,z8,z4,z5]),(0,[z1,z334,z2,z8,z5,z22]),(0,[z1,z24,z8,z118,z5,z6]),(0,[z1,z1443,z8,z4,z5,z6])],[(1,[z1,z8,z4,z819,z6])],[(0,[z1,z1444,z2,z8,z4,z5]),(0,[z48,z1,z108,z8,z4,z5]),(0,[z117,z108,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z1445]),(0,[z1,z2,z8,z4,z1446,z5])],[(0,[z1,z1447,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1448])],[(0,[z1,z2,z8,z4,z5,z1449]),(0,[z1,z2,z8,z4,z210,z6]),(0,[z1,z2,z369,z8,z4,z5]),(0,[z1,z2,z8,z4,z1450,z5]),(0,[z1,z2,z8,z4,z5,z1451]),(0,[z1,z57,z440,z8,z4,z5])],[(0,[z1,z1452,z8,z4,z5,z6]),(0,[z1,z43,z8,z4,z34,z5]),(0,[z1,z61,z25,z69,z4,z5])],[(0,[z1,z57,z83,z8,z4,z5]),(0,[z1,z346,z8,z168,z5,z6]),(0,[z1,z1453,z2,z8,z4,z5]),(0,[z1,z2,z25,z4,z5,z515])],[(0,[z1,z2,z1454,z8,z4,z6]),(0,[z1,z2,z8,z4,z5,z1455]),(0,[z1,z2,z8,z4,z5,z1456]),(0,[z1,z2,z8,z4,z5,z1457]),(0,[z1,z2,z8,z4,z131,z253])],[(0,[z1,z371,z2,z8,z242,z5])],[(0,[z1,z1170,z3,z8,z4,z5]),(0,[z1,z1458,z2,z8,z4,z5]),(0,[z1,z1313,z141,z8,z4,z5])]],
   [[(0,[z1,z61,z686,z4,z5,z6]),(0,[z112,z1,z288,z8,z4,z5]),(0,[z1,z1459,z8,z4,z5,z6]),(0,[z1,z1460,z2,z8,z4,z6]),(0,[z1,z334,z51,z8,z5,z6]),(0,[z1,z2,z8,z723,z5,z6])],[(0,[z1,z81,z2,z8,z4,z5]),(0,[z1,z1461,z2,z8,z4,z5]),(0,[z1,z2,z1462,z8,z4,z5]),(0,[z1,z15,z810,z4,z5,z6]),(0,[z1,z1463,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z1464,z5]),(0,[z1,z43,z8,z4,z5,z29]),(0,[z1,z2,z8,z36,z5,z45])],[(0,[z1,z2,z8,z4,z5,z343]),(0,[z1,z1465,z2,z8,z4,z5]),(0,[z136,z1,z14,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1466])],[(0,[z112,z53,z8,z4,z5,z469]),(0,[z1,z1467,z2,z8,z4,z5]),(0,[z311,z273,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1468]),(0,[z1,z16,z2,z25,z4,z5]),(0,[z1,z1469,z2,z8,z4,z5])],[(0,[z1,z2,z8,z4,z1470,z5]),(0,[z1,z2,z8,z410,z5,z10]),(0,[z1,z1170,z8,z4,z5,z6]),(0,[z205,z1,z2,z25,z4,z5]),(0,[z1,z1471,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z1472,z5])],[(0,[z339,z2,z8,z4,z5,z22]),(0,[z1,z35,z2,z8,z4,z5]),(0,[z1,z16,z266,z25,z4,z5]),(0,[z1,z1473,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1474])],[(0,[z1,z2,z1475,z8,z4,z5]),(0,[z1,z1476,z2,z8,z4,z5]),(0,[z1,z16,z2,z52,z4,z5])],[(0,[z89,z1,z288,z8,z4,z5]),(0,[z1,z221,z8,z410,z5,z6]),(0,[z199,z1,z183,z8,z5,z6]),(0,[z199,z1,z241,z2,z8,z5]),(0,[z1,z1477,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1478]),(0,[z1,z51,z440,z8,z4,z6]),(0,[z1,z16,z2,z154,z4,z5])],[(0,[z1,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z1479]),(0,[z89,z123,z8,z4,z5,z478]),(0,[z456,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z4,z5,z1480]),(0,[z1,z2,z4,z274,z1073,z6]),(0,[z1,z335,z2,z8,z36,z5])],[(0,[z1,z77,z2,z8,z4,z5]),(0,[z1,z288,z43,z8,z4,z5])],[(0,[z1,z183,z8,z4,z5,z6]),(0,[z1,z1481,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1482]),(0,[z1,z15,z2,z52,z4,z5]),(0,[z1,z2,z8,z4,z5,z1483]),(0,[z1,z14,z79,z8,z4,z5]),(0,[z1,z57,z74,z8,z4,z5]),(0,[z1,z57,z8,z4,z5,z430]),(0,[z1,z2,z8,z4,z5,z1484])],[(0,[z49,z2,z8,z91,z5,z6]),(0,[z1,z14,z8,z4,z5,z267]),(0,[z1,z2,z8,z4,z1485,z6]),(0,[z1,z1486,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1487]),(0,[z1,z77,z266,z8,z4,z5])],[(0,[z1,z2,z8,z4,z1488,z6]),(0,[z1,z138,z266,z8,z4,z5])],[(0,[z1,z1489,z2,z8,z4,z5]),(0,[z204,z2,z8,z4,z5,z22])],[(0,[z1,z2,z8,z455,z5,z22])]],
   [[(0,[z112,z57,z53,z8,z4,z5]),(0,[z1,z8,z4,z5,z6,z1083]),(0,[z1,z2,z8,z4,z5,z1490]),(0,[z1,z43,z8,z85,z4,z5])],[(0,[z1,z1491,z8,z4,z5,z6]),(0,[z1,z108,z8,z4,z5,z45]),(0,[z1,z8,z4,z5,z126,z10]),(0,[z1,z334,z2,z8,z5,z6]),(1,[z1,z2,z8,z5,z829])],[(0,[z1,z2,z8,z4,z5,z1492]),(0,[z1,z276,z2,z8,z4,z6]),(0,[z1,z1493,z2,z8,z4,z5]),(0,[z1,z288,z61,z69,z4,z5]),(0,[z1,z2,z8,z5,z1494,z6]),(0,[z1,z2,z8,z4,z5,z1495]),(0,[z1,z14,z35,z8,z4,z5]),(0,[z1,z14,z425,z8,z4,z5]),(0,[z157,z1,z43,z8,z4,z5]),(0,[z1,z1496,z8,z4,z5,z6])],[(0,[z1,z346,z8,z4,z5,z6]),(0,[z112,z1,z8,z4,z5,z197]),(0,[z1,z276,z14,z2,z8,z4]),(0,[z1,z2,z8,z4,z1497,z5])],[(0,[z1,z2,z8,z4,z5,z60]),(0,[z1,z2,z4,z5,z1356,z6]),(0,[z1,z14,z666,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1498])],[(0,[z1,z1499,z2,z8,z4,z5]),(0,[z1,z382,z43,z8,z4,z5])],[(0,[z1,z1500,z8,z4,z5,z6]),(0,[z113,z2,z8,z4,z34,z6]),(0,[z1,z2,z1501,z8,z4,z5]),(0,[z1,z43,z8,z4,z102,z5]),(0,[z1,z43,z8,z4,z103,z5])],[(0,[z220,z1,z14,z8,z4,z5]),(0,[z1,z2,z12,z8,z4,z10]),(0,[z1,z2,z4,z5,z1502,z6]),(0,[z1,z14,z8,z983,z4,z5]),(0,[z1,z2,z8,z4,z5,z1503]),(0,[z1,z1377,z8,z4,z5,z6])],[(0,[z1,z16,z2,z4,z5,z773])],[(0,[z1,z1095,z2,z8,z4,z6]),(0,[z1,z2,z1504,z8,z4,z5]),(0,[z1,z16,z2,z503,z4,z5]),(0,[z1,z2,z8,z4,z5,z773])],[(0,[z89,z1,z8,z4,z5,z197]),(0,[z1,z799,z221,z8,z4,z5]),(0,[z1,z1505,z2,z8,z4,z5]),(0,[z1,z14,z15,z97,z4,z5]),(0,[z1,z16,z160,z8,z70,z5]),(0,[z1,z2,z8,z4,z5,z1506])],[(0,[z96,z273,z2,z8,z4,z5])],[(0,[z1,z16,z2,z8,z4,z5]),(0,[z65,z2,z66,z410,z5,z6]),(0,[z1,z1507,z2,z8,z4,z5])],[(0,[z112,z53,z8,z4,z5,z22]),(0,[z1,z1508,z2,z8,z4,z5]),(0,[z1,z135,z50,z160,z8,z6]),(0,[z1,z43,z321,z8,z4,z5])],[(0,[z1,z14,z8,z603,z4,z5]),(0,[z1,z276,z2,z8,z168,z6]),(1,[z1,z1170,z8,z4,z5]),(0,[z256,z2,z8,z4,z5,z10]),(0,[z1,z411,z2,z8,z455,z5]),(0,[z1,z16,z266,z8,z4,z5]),(0,[z1,z2,z8,z4,z653,z54]),(0,[z1,z2,z8,z4,z131,z718])]],
   [[(0,[z2,z8,z91,z1001,z5,z6]),(0,[z1,z2,z8,z4,z1426,z6])],[(0,[z1,z276,z183,z8,z4,z6]),(0,[z1,z1509,z8,z4,z5,z6]),(0,[z1,z1510,z2,z8,z4,z5]),(0,[z1,z104,z14,z2,z4,z105])],[(0,[z1,z14,z8,z4,z5,z587]),(0,[z1,z2,z8,z1511,z5,z6]),(0,[z1,z14,z367,z2,z8,z4])],[(0,[z1,z239,z2,z8,z212,z5])],[(0,[z1,z1512,z2,z8,z4,z5]),(0,[z1,z43,z8,z4,z5,z10]),(0,[z1,z8,z70,z707,z5,z6])],[(0,[z1,z1386,z182,z8,z4,z5])],[(0,[z1,z1513,z2,z8,z4,z5]),(0,[z1,z61,z69,z4,z5,z22]),(0,[z1,z2,z8,z4,z1514,z5]),(0,[z1,z14,z51,z8,z4,z19])],[(0,[z1,z8,z4,z5,z90,z306]),(0,[z1,z8,z4,z5,z842,z22]),(0,[z1,z2,z25,z8,z455,z5]),(0,[z1,z2,z4,z5,z29,z773])],[(0,[z523,z123,z8,z4,z5,z6]),(0,[z1,z2,z1515,z8,z5,z6]),(0,[z1,z14,z2,z8,z455,z5]),(0,[z1,z2,z1516,z8,z4,z5]),(0,[z1,z1076,z356,z8,z4,z5]),(0,[z1,z1517,z43,z8,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1518]),(0,[z1,z1519,z108,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1520])],[(0,[z2,z8,z1001,z68,z5,z6]),(0,[z1,z2,z8,z4,z5,z1521]),(0,[z1,z108,z321,z8,z4,z5]),(0,[z1,z2,z8,z4,z1522,z5]),(0,[z1,z382,z2,z8,z4,z314])],[(0,[z1,z733,z2,z8,z4,z5]),(0,[z320,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z1523])],[(0,[z1,z346,z25,z8,z4,z5]),(0,[z1,z16,z183,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1524]),(0,[z1,z2,z25,z568,z4,z5])],[(0,[z1,z1525,z2,z8,z4,z5]),(0,[z233,z2,z8,z4,z75,z143]),(0,[z1,z135,z8,z4,z583,z6]),(0,[z1,z2,z8,z4,z1526,z5]),(0,[z1,z16,z2,z413,z4,z5])],[(0,[z1,z16,z2,z8,z410,z5]),(0,[z1,z930,z346,z8,z4,z5]),(0,[z1,z43,z97,z8,z4,z5]),(0,[z1,z1527,z2,z8,z4,z5])],[]],
   [[(0,[z199,z1,z14,z2,z8,z5]),(0,[z1,z1528,z2,z8,z4,z5]),(0,[z1,z2,z8,z4,z5,z1529]),(0,[z1,z2,z8,z4,z1530,z5])],[(0,[z112,z178,z53,z8,z4,z5]),(0,[z1,z2,z1531,z8,z4,z5]),(0,[z2,z356,z3,z8,z4,z5]),(0,[z1,z14,z15,z355,z4,z5]),(0,[z1,z2,z4,z5,z773,z6]),(0,[z1,z1532,z2,z8,z4,z5])],[(0,[z1,z83,z8,z4,z5,z10]),(0,[z1,z566,z14,z8,z4,z5]),(0,[z1,z2,z810,z4,z5,z6]),(0,[z44,z1,z2,z8,z5,z101])],[(0,[z1,z2,z8,z4,z5,z1533]),(0,[z48,z471,z2,z8,z5,z6]),(0,[z1,z2,z8,z4,z5,z408]),(0,[z532,z1,z108,z8,z4,z5]),(0,[z365,z2,z8,z4,z5,z10]),(0,[z1,z2,z8,z4,z5,z1534]),(0,[z1,z2,z8,z5,z829,z45])],[(0,[z1,z2,z1535,z8,z4,z5]),(0,[z1,z2,z490,z3,z4,z5]),(0,[z1,z2,z723,z103,z5,z6]),(0,[z1,z2,z8,z4,z5,z1536]),(0,[z1,z16,z1421,z8,z4,z5]),(0,[z1,z2,z1253,z8,z4,z5])],[(0,[z1,z911,z2,z8,z4,z5]),(0,[z1,z2,z1537,z8,z4,z5]),(0,[z220,z273,z2,z8,z4,z5]),(0,[z1,z57,z8,z4,z5,z864])],[(0,[z1,z1538,z2,z8,z4,z5])],[(0,[z1,z2,z1539,z8,z4,z5]),(0,[z1,z183,z8,z168,z5,z6]),(0,[z1,z108,z8,z4,z5,z139]),(0,[z1180,z1,z2,z8,z5,z10]),(0,[z1,z16,z2,z76,z73,z5])],[(0,[z562,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z5,z969,z6])],[(0,[z1,z2,z8,z410,z210,z6]),(0,[z1,z2,z490,z4,z274,z5]),(0,[z1,z57,z367,z2,z8,z4]),(0,[z1,z43,z8,z8,z4,z5])],[(0,[z1,z2,z8,z1540,z4,z5]),(0,[z1,z2,z8,z4,z1541,z5]),(0,[z1542,z2,z8,z4,z5,z6])],[(0,[z2,z8,z4,z5,z800,z6]),(0,[z1,z2,z25,z355,z4,z5])],[(0,[z1,z2,z1543,z4,z5,z6]),(0,[z112,z1,z355,z8,z4,z5]),(0,[z1,z2,z356,z8,z4,z5]),(0,[z1,z50,z2,z8,z127,z22]),(0,[z1,z2,z8,z4,z227,z5]),(0,[z1,z2,z8,z1306,z5,z6])],[(0,[z1,z108,z27,z8,z4,z5]),(0,[z363,z2,z8,z4,z5,z22]),(0,[z1,z2,z8,z935,z5,z6]),(0,[z1,z2,z76,z73,z5,z494])],[(0,[z1,z1076,z2,z8,z4,z5]),(0,[z1,z43,z8,z36,z4,z5])],[(0,[z1,z2,z8,z4,z5,z1544]),(0,[z1,z2,z8,z4,z5,z1545]),(0,[z1,z2,z8,z1412,z5,z6]),(0,[z1,z57,z8,z4,z5,z354])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 486) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 486).take 486) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 972).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1457).take 80) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1537)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [486, 486, 485, 80] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 87).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 87).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 175).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 276).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 366).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 458).take 54).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [87, 88, 101, 90, 92, 54] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_47012

theorem PEqualNP.Outside.L_meta_47012 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241288 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241288 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47012.solve