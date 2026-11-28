import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47018

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
  Nat.testBit (4008241312 * 2 ^ 32 + 3936938144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000c1616a06585a8#64 ++ 0x000182c2d40cb0b5#64 ++ 0xfa1c3e3fe3ff8fff#64 ++ 0xdf4387c7fc7ff1ff#64 : BitVec 256),
   (0x28e1cacb8d12b2e0#64 ++ 0x051c395971a2565c#64 ++ 0xfde3cfcf9d13f3e3#64 ++ 0x7fbc79f9f3a27e7c#64 : BitVec 256),
   (0x4602e16156185850#64 ++ 0x48c05c2c2ac30b0a#64 ++ 0x7e03f1f1fe1c7c7d#64 ++ 0xefc07e3e3fc38f8f#64 : BitVec 256),
   (0x977401bc1ba06f02#64 ++ 0x12ee803783740de0#64 ++ 0xbffc01fe1fe07f86#64 ++ 0x77ff803fc3fc0ff0#64 : BitVec 256),
   (0x17bb7c001fdf0001#64 ++ 0x22f76f8003fbe000#64 ++ 0xd7fffe001fff8000#64 ++ 0x7affffc003fff000#64 : BitVec 256),
   (0xe7dfbfffe0000000#64 ++ 0xbcfbf7fffc000000#64 ++ 0xe7ffffffe0000000#64 ++ 0x7cfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z1 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xd7fffe001fff8000 0x7affffc003fff000

def z2 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z3 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z4 : W := mkw 0x608bbe43e0000000 0xac1177c87c000000 0x4003fe01e0000000 0x08007fc03c000000

def z5 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z6 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x05e3c1c000000000 0x20bc783800000000

def z7 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x100000001fff8000 0x0200000003fff000

def z8 : W := mkw 0x3ffbfecb9fdfb2e1 0x27ff7fd973fbf65c 0xffffffcf9ffff3e3 0x7ffffff9f3fffe7c

def z9 : W := mkw 0x1fbb7c001fdfb2e1 0x23f76f8003fbf65c 0xdffffe001ffff3e3 0x7bffffc003fffe7c

def z10 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z11 : W := mkw 0x1020000009a02702 0x02040000013404e0 0x0000000001e00382 0x00000000003c0070

def z12 : W := mkw 0x008b7c00045f0001 0x20116f80008be000 0x4003fe00001f8000 0x08007fc00003f000

def z13 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z14 : W := mkw 0x008f7e16a47f85a9 0x2011efc2d48ff0b5 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z15 : W := mkw 0x17bb7c001fdf5851 0x62f76f8003fbeb0a 0xdffffe001ffffc7d 0xfbffffc003ffff8f

def z16 : W := mkw 0x28a1ca438d1290e0 0x0514394871a2521c 0xd5e3ce019d138061 0x7abc79c033a2700c

def z17 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe21c0c7d 0xfffffffffc43818f

def z18 : W := mkw 0xe7dffffff67dddf8 0xfcfbfffffecfbbbf 0xffffffffffffffff 0xffffffffffffffff

def z19 : W := mkw 0x00000202800080a0 0x0000004050001014 0x2800000f800003e3 0x05000001f000007c

def z20 : W := mkw 0x000c141420650508 0x00018282840ca0a1 0x021c303062ec0c1c 0x804386060c5d8183

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x7a003031e21c0c7d 0xcf4006063c43818f

def z22 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x85ffce001de38000 0x30bff9c003bc7000

def z23 : W := mkw 0x00081602a04580a8 0x000102c05408b015 0x40003e01e01f8079 0x880007c03c03f00f

def z24 : W := mkw 0x0060008809002200 0x000c001101200440 0xbde001ce1d007382 0x77bc0039c3a00e70

def z25 : W := mkw 0x9174009c09a02702 0x122e8013813404e0 0x81fc000e01e00382 0x103f8001c03c0070

def z26 : W := mkw 0xc71e3736e06585a8 0xb8e3c6e6dc0cb0b5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z27 : W := mkw 0x000c1616a0000000 0x000182c2d4000000 0xe21c3e3fe0000000 0x5c4387c7fc000000

def z28 : W := mkw 0x875401bc00200500 0x10ea8037800400a0 0xbffc01fe03e00f86 0x77ff803fc07c01f0

def z29 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0xc7fffe0000000000 0x78ffffc000000000

def z30 : W := mkw 0x4602212052084810 0x48c044240a410902 0x02003030620c0c1c 0x804006060c418183

def z31 : W := mkw 0x6ee3ebebdf1afaf0 0x4ddc7d7d7be35f5e 0xffe3ffffff1fffff 0xfffc7fffffe3ffff

def z32 : W := mkw 0xb9f5cadf8db2b7e2 0x173eb95bf1b656fc 0xfdffcfcf9df3f3e3 0x7fbff9f9f3be7e7c

def z33 : W := mkw 0x0008140000450000 0x000102800008a000 0xd21c3e0003ff8000 0x5a4387c0007ff000

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000021c0c7d 0x830000000043818f

def z35 : W := mkw 0x182040001fdfb2e1 0x0304080003fbf65c 0x180000001ffff3e3 0x0300000003fffe7c

def z36 : W := mkw 0x0602600016180000 0x00c04c0002c30000 0x5603f0001e1c0000 0x6ac07e0003c38000

def z37 : W := mkw 0x4000816140005850 0x4800102c28000b0a 0x280001f1e0007c7d 0x8500003e3c000f8f

def z38 : W := mkw 0xe7dfbfffe0005850 0xfcfbf7fffc000b0a 0xefffffffe0007c7d 0xfdfffffffc000f8f

def z39 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x180000001d13f3e3 0x0300000003a27e7c

def z40 : W := mkw 0xa1dd9edfa0000000 0xb43bb3dbf4000000 0xe5ffcfcf80000000 0x7cbff9f9f0000000

def z41 : W := mkw 0x9710012012804802 0x12e2002402500900 0x0000000000000000 0x0000000000000000

def z42 : W := mkw 0xefdfbfffe000b2e0 0xbdfbf7fffc00165c 0xefffffffe00073e3 0x7dfffffffc000e7c

def z43 : W := mkw 0x20818a4380000000 0x0410314870000000 0x4003ce0180000000 0x080079c030000000

def z44 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z45 : W := mkw 0x4602e363d618d8f0 0x48c05c6c7ac31b1e 0xfe03ffffff1fffff 0xffc07fffffe3ffff

def z46 : W := mkw 0x060a7400165d0000 0x00c14e8002cba000 0xd61ffe001fff8000 0x7ac3ffc003fff000

def z47 : W := mkw 0x57bbfc415fdf1051 0x6af77f882bfbe20a 0xd7fffe01ffff8079 0xfaffffc03ffff00f

def z48 : W := mkw 0x460eb777e06585a8 0x08c1d6eefc0cb0b5 0xfe1fffffe3ff8fff 0xffc3fffffc7ff1ff

def z49 : W := mkw 0x57bbfd615fdf5851 0x6af77fac2bfbeb0a 0xfffffff1fffffc7d 0xfffffffe3fffff8f

def z50 : W := mkw 0x0602600016180000 0x00c04c0002c30000 0x0403c0001c000000 0x2080780003800000

def z51 : W := mkw 0x804401bc00206f02 0x1008803780040de0 0x280001fe00007f86 0x0500003fc0000ff0

def z52 : W := mkw 0x804c17bea065efaa 0x100982f7d40cbdf5 0xfa1c3fffe3ffffff 0xdf4387fffc7fffff

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x3c0001c01c007000 0x6780003803800e00

def z54 : W := mkw 0x102040001fb87f52 0x4204080003f70fea 0x180000001ffc7fff 0x8300000003ff8fff

def z55 : W := mkw 0xa7df3e9ea0000000 0xb4fbe7d3d4000000 0xc7fffe0e00000000 0x78ffffc1c0000000

def z56 : W := mkw 0x179b3c0012cd0001 0x22f367800259a000 0xc7fffe0002ec0000 0x78ffffc0005d8000

def z57 : W := mkw 0x0600012012004800 0x00c0002402400900 0x3e0001f01e007c04 0x67c0003e03c00f80

def z58 : W := mkw 0x11bb7c000ddf0001 0x22376f8001bbe000 0xc1fffe0001ff8000 0x183fffc0003ff000

def z59 : W := mkw 0x97ff7dbc1fdf0001 0x32ffefb783fbe000 0xf7fffffe1fff8000 0x7effffffc3fff000

def z60 : W := mkw 0x0000020280000000 0x0000004050000000 0xe0000e0f80000000 0x5c0001c1f0000000

def z61 : W := mkw 0xe7dffffff6185850 0xfcfbfffffec30b0a 0xfffffffffe1c7c7d 0xffffffffffc38f8f

def z62 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0x801c0e0e01e38382 0x100381c1c03c7070

def z63 : W := mkw 0x102040001fdf5851 0x4204080003fbeb0a 0x180000001ffffc7d 0x8300000003ffff8f

def z64 : W := mkw 0xc71eb57560000000 0xb8e3d6aeac000000 0x661ff1f1e0000000 0x6cc3fe3e3c000000

def z65 : W := mkw 0x060c1736b265cda8 0x00c182e6d64cb9b5 0xfe1c3fffffffffff 0xffc387ffffffffff

def z66 : W := mkw 0x0000400016185850 0x4000080002c30b0a 0x180000001e1c7c7d 0x8300000003c38f8f

def z67 : W := mkw 0xa1dd1e9ea0000000 0xb43ba3d3d4000000 0x81fc0e0e00000000 0x103f81c1c0000000

def z68 : W := mkw 0x07bb7c000d120000 0x20f76f8001a24000 0xd7fffe001d138000 0x7affffc003a27000

def z69 : W := mkw 0x17b368001f9a0001 0x22f66d0003f34000 0x05e3c0001c000000 0x20bc780003800000

def z70 : W := mkw 0x875401bc00000000 0x10ea803780000000 0xa7fc01fe00000000 0x74ff803fc0000000

def z71 : W := mkw 0x171a340012cd0001 0x22e346800259a000 0xd21c3e0003ff8000 0x5a4387c0007ff000

def z72 : W := mkw 0x2881ca43841290e0 0x051039487082521c 0x4003ce0180138061 0x080079c03002700c

def z73 : W := mkw 0x97ff7dbc1fff6f03 0x32ffefb783ffede0 0xfffffffe1fffff86 0x7fffffffc3fffff0

def z74 : W := mkw 0x608fbe57e06585a8 0xac11f7cafc0cb0b5 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z75 : W := mkw 0x1712200012880001 0x22e2440002510000 0x0000000000000000 0x0000000000000000

def z76 : W := mkw 0x00000202800080a0 0x0000004050001014 0xf8000e0f811383e3 0x5f0001c1f022707c

def z77 : W := mkw 0x460ef777f67dddf8 0x48c1deeefecfbbbf 0xfe1fffffffffffff 0xffc3ffffffffffff

def z78 : W := mkw 0x977c17bebbe5efaa 0x12ef82f7d77cbdf5 0xfffc3fffffffffff 0xffff87ffffffffff

def z79 : W := mkw 0xd776e1fd5fb87f52 0x5aeedc3fabf70fea 0xfffff1fffffc7fff 0xfffffe3fffff8fff

def z80 : W := mkw 0x9714013412a04d02 0x12e28026825409a0 0x021c003002e00c04 0x00438006005c0180

def z81 : W := mkw 0x877401bc09002200 0x10ee803781200440 0xbffc01fe1d007382 0x77ff803fc3a00e70

def z82 : W := mkw 0xe7dfbfffe0650508 0xbcfbf7fffc0ca0a1 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z83 : W := mkw 0x2860c2cb8d12b2e0 0x050c185971a2565c 0x380001cf9d13f3e3 0x07000039f3a27e7c

def z84 : W := mkw 0x17bb3c001bcf0001 0x22f767800379e000 0x83fc3e0003ef8000 0x107f87c0007df000

def z85 : W := mkw 0x684083ebc000faf0 0x4d08107d78001f5e 0x280001ffe0007fff 0x8500003ffc000fff

def z86 : W := mkw 0xe7d7abffe0000000 0xbcfaf57ffc000000 0x25e3c1ffe0000000 0x24bc783ffc000000

def z87 : W := mkw 0x4602212052084810 0x48c044240a410902 0x0000000000000000 0x0000000000000000

def z88 : W := mkw 0x0602612016184800 0x00c04c2402c30900 0x7e03f1f01e1c7c04 0x6fc07e3e03c38f80

def z89 : W := mkw 0x284482dfa020b7e8 0x0508905bf40416fd 0x280001ffe0007fff 0x8500003ffc000fff

def z90 : W := mkw 0x0004001400200500 0x00008002800400a0 0xba1c003e03e00f86 0x57438007c07c01f0

def z91 : W := mkw 0xa1dd1e9ea06585a8 0xb43ba3d3d40cb0b5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z92 : W := mkw 0x977441bc1fff6f03 0x12ee883783ffede0 0xbffc01fe1fffff86 0x77ff803fc3fffff0

def z93 : W := mkw 0x977001a81b806a02 0x12ee003503700d40 0x05e001c01c007000 0x20bc003803800e00

def z94 : W := mkw 0x28e10a8a8902a2a0 0x051c215151205454 0x81e00e0e01038382 0x103c01c1c0207070

def z95 : W := mkw 0x284082cb8000b2e0 0x050810597000165c 0x280001cf800073e3 0x05000039f0000e7c

def z96 : W := mkw 0x0000c04104101040 0x0000180820820208 0x7c03c1c19c107061 0x6f80783833820e0c

def z97 : W := mkw 0xf7dfbffff2a04d02 0xbefbf7fffe5409a0 0xe7ffffffe2e00c04 0x7cfffffffc5c0180

def z98 : W := mkw 0x479bbd6140000000 0x28f377ac28000000 0xe7fffff1e0000000 0x7cfffffe3c000000

def z99 : W := mkw 0x17b148001f920000 0x02f6290003f24000 0xd7ffce001ff38000 0x7afff9c003fe7000

def z100 : W := mkw 0x4e22e1615f1afaf0 0x49c45c2c2be35f5e 0x7e03f1f1ff1fffff 0xefc07e3e3fe3ffff

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x7800000180100061 0x4f0000003002000c

def z102 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xfffc31fffffc7fff 0xffff863fffff8fff

def z103 : W := mkw 0x17bb3c001b800000 0x22f7678003700000 0xd7fffe001fe00000 0x7affffc003fc0000

def z104 : W := mkw 0x00040216a02085a8 0x00008042d40410b5 0x2800003fe0000fff 0x85000007fc0001ff

def z105 : W := mkw 0x00a1c8410d121040 0x0014390821a24208 0xfde3cfc19d13f061 0x7fbc79f833a27e0c

def z106 : W := mkw 0x0793280000000000 0x20f2650000000000 0x05e3c00000000000 0x20bc780000000000

def z107 : W := mkw 0x000a3400004d0001 0x200146800009a000 0x00003000000c0000 0x0000060000018000

def z108 : W := mkw 0xc79f3d3460000000 0xb8f3e7a68c000000 0xc7fffe3060000000 0x78ffffc60c000000

def z109 : W := mkw 0x0000400016180000 0x0000080002c30000 0x100000001e1c0000 0x0200000003c38000

def z110 : W := mkw 0xe8e5cbffed12b2e0 0x9d1cb97ffda2565c 0xfde3cffffd13f3e3 0x7fbc79ffffa27e7c

def z111 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z112 : W := mkw 0xf7ffffffffdf0001 0xbefffffffffbe000 0xf7ffffffffff8000 0x7efffffffffff000

def z113 : W := mkw 0x9714013412a04d02 0x12e28026825409a0 0x3e1c01f01ee07c04 0x67c3803e03dc0f80

def z114 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0x421c3e31e2ff8c7d 0x884387c63c5ff18f

def z115 : W := mkw 0x66c3ebebd6185850 0x4cd87d7d7ac30b0a 0xffe3fffffe1c7c7d 0xfffc7fffffc38f8f

def z116 : W := mkw 0x28e9decb8d57b2e0 0x051d3bd971aaf65c 0xffffffcf9ffff3e3 0x7ffffff9f3fffe7c

def z117 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x0403c1c01c007000 0x2080783803800e00

def z118 : W := mkw 0xefffffffed12b2e0 0xbdfffffffda2565c 0xfffffffffd13f3e3 0x7fffffffffa27e7c

def z119 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x85fc01ce1de07382 0x30bf8039c3bc0e70

def z120 : W := mkw 0xf7dfbffff2cd0001 0xbefbf7fffe59a000 0xe7ffffffe2ec0000 0x7cfffffffc5d8000

def z121 : W := mkw 0x0060c0c90d103240 0x000c181921a20648 0xfde3c1cf9d1073e3 0x7fbc7839f3a20e7c

def z122 : W := mkw 0xe04483ffe02085a8 0x9c08907ffc0410b5 0x280001ffe0000fff 0x8500003ffc0001ff

def z123 : W := mkw 0x00a148000d120000 0x0014290001a24000 0xd5e3ce001d138000 0x7abc79c003a27000

def z124 : W := mkw 0x1130000009800000 0x0226000001300000 0x81fc000001e00000 0x103f8000003c0000

def z125 : W := mkw 0xb7fd1fbebba06f02 0xb6ffa3f7d7740de0 0xbffc0ffe1fe07f86 0x77ff81ffc3fc0ff0

def z126 : W := mkw 0xe7dfbfffe00080a0 0xbcfbf7fffc001014 0xffffffffe11383e3 0x7ffffffffc22707c

def z127 : W := mkw 0x6ee3ebebcd12b2e0 0x0ddc7d7d79a2565c 0xffe3fffffd13f3e3 0x7ffc7fffffa27e7c

def z128 : W := mkw 0xd77621bc5ba86f12 0x5aeec4378b750de2 0xbffc31fe7fec7f9e 0xf7ff863fcffd8ff3

def z129 : W := mkw 0xe7dfbdfd60000000 0xbcfbf7bfac000000 0x07fff1f060000000 0x20fffe3e0c000000

def z130 : W := mkw 0x4002e04144181050 0x48005c082883020a 0x7a03f031e21c0c7d 0xcf407e063c43818f

def z131 : W := mkw 0x173a74001fdf0001 0x22e74e8003fbe000 0x121c30001fff8000 0x0243860003fff000

def z132 : W := mkw 0xbff5cbff9fb2ffe2 0x17feb97ff3f65ffc 0xffffcfff9ff3ffe7 0x7ffff9fff3fe7ffc

def z133 : W := mkw 0x4602a16140000000 0x08c0542c28000000 0x0403c1c000000000 0x2080783800000000

def z134 : W := mkw 0x11b91c0009c70001 0x223723800138e000 0x81fc0e0001e38000 0x103f81c0003c7000

def z135 : W := mkw 0xa84483ff8020ffe2 0x1508907ff0041ffc 0x280001ff80007fe7 0x0500003ff0000ffc

def z136 : W := mkw 0x000c1616a0450000 0x000182c2d408a000 0xf21c3e3fe3ff8000 0x5e4387c7fc7ff000

def z137 : W := mkw 0x082040001f1afaf0 0x4104080003e35f5e 0x180000001f1fffff 0x8300000003e3ffff

def z138 : W := mkw 0x102c5616bfff85a9 0x02058ac2d7fff0b5 0xfa1c3e3fffff8fff 0xdf4387c7fffff1ff

def z139 : W := mkw 0x082000000902a2a0 0x0104000001205454 0x0000000001038382 0x0000000000207070

def z140 : W := mkw 0x87df3dbc00000000 0x30fbe7b780000000 0xe7fffffe00000000 0x7cffffffc0000000

def z141 : W := mkw 0xb1fd1e9ea9c70001 0xb63fa3d3d538e000 0x81fc0e0e01e38000 0x103f81c1c03c7000

def z142 : W := mkw 0x171a740016dd0001 0x22e34e8002dba000 0x561ff0001efc0000 0x6ac3fe0003df8000

def z143 : W := mkw 0x00000000006585a8 0x00000000000cb0b5 0x1800000003ff8fff 0x83000000007ff1ff

def z144 : W := mkw 0x28ebfecb8d5fb2e1 0x251d7fd971abf65c 0xfde3ffcf9d1ff3e3 0x7fbc7ff9f3a3fe7c

def z145 : W := mkw 0x079f3e16a06585a8 0x20f3e7c2d40cb0b5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z146 : W := mkw 0x288dde57a47795e8 0x0511bbcaf48ef2bd 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z147 : W := mkw 0x68ebfecbed12b2e0 0xad1d7fd97da2565c 0xfde3ffcffd13f3e3 0x7fbc7ff9ffa27e7c

def z148 : W := mkw 0x17bf7e16bfff85a9 0x22f7efc2d7fff0b5 0xfffffe3fffff8fff 0xffffffc7fffff1ff

def z149 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x3e03c1f01e007c04 0x67c0783e03c00f80

def z150 : W := mkw 0xb9f50a9e89a2a7a2 0x173ea153d13454f4 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z151 : W := mkw 0x17bb7d201fdf4801 0x22f76fa403fbe900 0xfffffff01ffffc04 0x7ffffffe03ffff80

def z152 : W := mkw 0x102000001ba06f02 0x0204000003740de0 0x180000001fe07f86 0x0300000003fc0ff0

def z153 : W := mkw 0xc71e353460650508 0xb8e3c6a68c0ca0a1 0x021c303062ec0c1c 0x804386060c5d8183

def z154 : W := mkw 0xe7d7a9fd40000000 0xbcfaf53fa8000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z155 : W := mkw 0x0000400016185850 0x4000080002c30b0a 0x7a003031fe1c7c7d 0xcf4006063fc38f8f

def z156 : W := mkw 0x00004000045f0001 0x00000800008be000 0x00000000001f8000 0x000000000003f000

def z157 : W := mkw 0xc712212040000000 0xb8e2442408000000 0x0000000000000000 0x0000000000000000

def z158 : W := mkw 0x608bfe43e45f0001 0xac117fc87c8be000 0x4003fe01e01f8000 0x08007fc03c03f000

def z159 : W := mkw 0xe04483ffe0000000 0x9c08907ffc000000 0x200001ffe0000000 0x0400003ffc000000

def z160 : W := mkw 0xf7ffbffffbe5efaa 0xbefff7ffff7cbdf5 0xffffffffffffffff 0xffffffffffffffff

def z161 : W := mkw 0xa1dd1e9ea0000000 0xb43ba3d3d4000000 0xe3fc3e3fe0000000 0x5c7f87c7fc000000

def z162 : W := mkw 0xc004013460000000 0x980080268c000000 0x0000003060000000 0x000000060c000000

def z163 : W := mkw 0x977001a81b806a02 0x12ee003503700d40 0x97fc01c01fe07000 0x72ff803803fc0e00

def z164 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x0603f1f07e0c7c1c 0xa0c07e3e0fc18f83

def z165 : W := mkw 0x00081602a0000000 0x000102c054000000 0x40003e01e0000000 0x080007c03c000000

def z166 : W := mkw 0xf7ffbffffba06f02 0xbefff7ffff740de0 0xffffffffffe07f86 0x7ffffffffffc0ff0

def z167 : W := mkw 0xa1d1088800000000 0xb43a211100000000 0x01e0000000000000 0x003c000000000000

def z168 : W := mkw 0x00000202800080a0 0x0000004050001014 0xfa003e3fe31f8fff 0xdf4007c7fc63f1ff

def z169 : W := mkw 0x97ff7c9c1fff2703 0x32ffef9383ffe4e0 0xd7fffe0e1fff8382 0x7affffc1c3fff070

def z170 : W := mkw 0x28eddedfad77b7e8 0x051dbbdbf5aef6fd 0xffffffffffffffff 0xffffffffffffffff

def z171 : W := mkw 0x284c96dfa065b7e8 0x050992dbf40cb6fd 0xfa1c3fffe3ffffff 0xdf4387fffc7fffff

def z172 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x4203f031e21c0c7d 0x88407e063c43818f

def z173 : W := mkw 0x2881ca43841290e0 0x051039487082521c 0x7c03cfc19c13f061 0x6f8079f833827e0c

def z174 : W := mkw 0x9174009c09a02702 0x122e8013813404e0 0xbbfc003e03e00f86 0x577f8007c07c01f0

def z175 : W := mkw 0x4602212040000000 0x08c0442408000000 0x0200303060000000 0x004006060c000000

def z176 : W := mkw 0x173000001b800000 0x02e6000003700000 0x97fc00001fe00000 0x72ff800003fc0000

def z177 : W := mkw 0x460e3736f26dcdb8 0x48c1c6e6de4db9b7 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z178 : W := mkw 0x60cbbecbe0000000 0xac1977d97c000000 0xe5e3ffcfe0000000 0x7cbc7ff9fc000000

def z179 : W := mkw 0x082040000d77b7e8 0x0104080001aef6fd 0x180000001fffffff 0x8300000003ffffff

def z180 : W := mkw 0xefffbfffe902a2a0 0xbdfff7fffd205454 0xe7ffffffe1038382 0x7cfffffffc207070

def z181 : W := mkw 0x11bd1e16a9e785a9 0x2237a3c2d53cf0b5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z182 : W := mkw 0xf7ffffffffff6f03 0xbeffffffffffede0 0xffffffffffffff86 0x7ffffffffffffff0

def z183 : W := mkw 0x11b95c001fdf0001 0x22372b8003fbe000 0x91fc0e001fff8000 0x123f81c003fff000

def z184 : W := mkw 0x082040000d123240 0x0104080001a24648 0x000000001c007000 0x0000000003800e00

def z185 : W := mkw 0x28e1c8c90d123240 0x051c391921a24648 0x05e3c1c01c007000 0x20bc783803800e00

def z186 : W := mkw 0x6083a84140000000 0xac10750828000000 0x0003c00000000000 0x0000780000000000

def z187 : W := mkw 0x0602600016180000 0x00c04c0002c30000 0x7e03f031fe1c0c7d 0xefc07e063fc3818f

def z188 : W := mkw 0x8044009c00202702 0x10088013800404e0 0x0000000e00000382 0x00000001c0000070

def z189 : W := mkw 0x9174009c09a02702 0x122e8013813404e0 0xbdfc01ce1de07382 0x77bf8039c3bc0e70

def z190 : W := mkw 0x28ed1e9ea967a7a8 0x051da3d3d52cf4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z191 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x85ffcfce00000000 0x30bff9f9c0000000

def z192 : W := mkw 0x00081602a04580a8 0x000102c05408b015 0xd21c3e01e3ff8079 0xda4387c03c7ff00f

def z193 : W := mkw 0x002040000d120000 0x0004080001a24000 0x100000001d138000 0x0200000003a27000

def z194 : W := mkw 0x17b368001fdf0001 0x22f66d0003fbe000 0x15e3c0001fff8000 0x22bc780003fff000

def z195 : W := mkw 0x06a368001f1a0000 0x00d46d0003e34000 0xd7e3fe001f1f8000 0x7afc7fc003e3f000

def z196 : W := mkw 0x20c188c900000000 0x0418311920000000 0x05e3c1c000000000 0x20bc783800000000

def z197 : W := mkw 0x479bfd6156185850 0x68f37fac2ac30b0a 0xfffffff1fe1c7c7d 0xfffffffe3fc38f8f

def z198 : W := mkw 0x000cd657a47595e8 0x00019acaf48eb2bd 0xfe1fffffffffffff 0xffc3ffffffffffff

def z199 : W := mkw 0x28a1ca438d12b2e0 0x0514394871a2565c 0x5803ce019d13f3e3 0x0b0079c033a27e7c

def z200 : W := mkw 0x9f7441bc1fb2ffe2 0x13ee883783f65ffc 0xbffc01fe1ff3ffe7 0x77ff803fc3fe7ffc

def z201 : W := mkw 0x4602e161567dddf8 0x48c05c2c2acfbbbf 0x7e03f1f1ffffffff 0xefc07e3e3fffffff

def z202 : W := mkw 0xf7f7a9fd5ba06f02 0xbefef53fab740de0 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z203 : W := mkw 0x68e1cbebcd12faf0 0x4d1c397d79a25f5e 0xfde3cffffd13ffff 0xffbc79ffffa27fff

def z204 : W := mkw 0xe7ffbfffe9002200 0xbcfff7fffd200440 0xfffffffffd007382 0x7fffffffffa00e70

def z205 : W := mkw 0x977c17bebba06f02 0x12ef82f7d7740de0 0xfffc3fffffe07f86 0x7fff87fffffc0ff0

def z206 : W := mkw 0x917401bc09a06f02 0x122e803781340de0 0xa9fc01fe01e07f86 0x153f803fc03c0ff0

def z207 : W := mkw 0x2840c2cb8410b2e0 0x050818597082165c 0x7c03c1cf9c1073e3 0x6f807839f3820e7c

def z208 : W := mkw 0xe7dbbde940000000 0xbcfb77bd28000000 0xc7ffffc000000000 0x78fffff800000000

def z209 : W := mkw 0x20cd9edfa0000000 0x0419b3dbf4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z210 : W := mkw 0x28e1c8c90d12b2e0 0x051c391921a2565c 0x1de3c1c01d13f3e3 0x23bc783803a27e7c

def z211 : W := mkw 0x0081080000000000 0x0010210000000000 0xc5e3ce0000000000 0x78bc79c000000000

def z212 : W := mkw 0x804401bc00000000 0x1008803780000000 0x200001fe00000000 0x0400003fc0000000

def z213 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x2de001fe1c007f86 0x25bc003fc3800ff0

def z214 : W := mkw 0x00000202800080a0 0x0000004050001014 0x80000e0e01038382 0x100001c1c0207070

def z215 : W := mkw 0x000c1616a0000000 0x000182c2d4000000 0x801c0e0e00000000 0x100381c1c0000000

def z216 : W := mkw 0xa044029ea0000000 0x94088053d4000000 0x0000000e00000000 0x00000001c0000000

def z217 : W := mkw 0x28e1088809022200 0x051c211101204440 0x01e0000000000000 0x003c000000000000

def z218 : W := mkw 0x102854001fdf0001 0x02050a8003fbe000 0xd21c3e001fff8000 0x5a4387c003fff000

def z219 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xd21c3e0e03ff8382 0x5a4387c1c07ff070

def z220 : W := mkw 0x079b7c0016180000 0x20f36f8002c30000 0xd7fffe001e1c0000 0x7affffc003c38000

def z221 : W := mkw 0x000c1616a0200500 0x000182c2d40400a0 0xfa1c3e3fe3e00f86 0x5f4387c7fc7c01f0

def z222 : W := mkw 0x38e1cacb9fb2ffe2 0x071c395973f65ffc 0xfde3cfcf9ff3ffe7 0x7fbc79f9f3fe7ffc

def z223 : W := mkw 0x0020000009000000 0x0004000001200000 0x95e000001d000000 0x72bc000003a00000

def z224 : W := mkw 0x608bfe43e4181050 0xec117fc87c83020a 0x4003fe01e01c0079 0x88007fc03c03800f

def z225 : W := mkw 0x102040001f9a0001 0x0204080003f34000 0x000000001c000000 0x0000000003800000

def z226 : W := mkw 0x102040001fff6f03 0x0204080003ffede0 0x180000001fffff86 0x0300000003fffff0

def z227 : W := mkw 0x071a340000000000 0x20e3468000000000 0x021c300000000000 0x0043860000000000

def z228 : W := mkw 0x97ff3dbc1ba06f02 0x32ffe7b783740de0 0xfffffffe1fe07f86 0x7fffffffc3fc0ff0

def z229 : W := mkw 0x0008140000000000 0x0001028000000000 0xc21c3e0000000000 0x584387c000000000

def z230 : W := mkw 0x57bfff77ffffddf9 0x6af7ffeefffffbbf 0xffffffffffffffff 0xffffffffffffffff

def z231 : W := mkw 0x0040008800002200 0x0008001100000440 0x280001ce00007382 0x05000039c0000e70

def z232 : W := mkw 0x0008140000450000 0x000102800008a000 0xfa1c3e31e3ff8c7d 0xdf4387c63c7ff18f

def z233 : W := mkw 0x162260001fdf0001 0x02c44c0003fbe000 0x5603f0001fff8000 0x6ac07e0003fff000

def z234 : W := mkw 0x079b3c0000450000 0x20f367800008a000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z235 : W := mkw 0xa9fd1e9ea902a2a0 0xb53fa3d3d5205454 0x81fc0e0e01038382 0x103f81c1c0207070

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x62003031e0000000 0x4c4006063c000000

def z237 : W := mkw 0x08a148000d12b2e0 0x0114290001a2565c 0xdde3ce001d13f3e3 0x7bbc79c003a27e7c

def z238 : W := mkw 0x182040001fb2ffe2 0x0304080003f65ffc 0x180000001ff3ffe7 0x0300000003fe7ffc

def z239 : W := mkw 0xefffffffed77b7e8 0xbdfffffffdaef6fd 0xffffffffffffffff 0xffffffffffffffff

def z240 : W := mkw 0x171a340012cd0001 0x22e346800259a000 0x021c300002ec0000 0x00438600005d8000

def z241 : W := mkw 0x00000000000080a0 0x0000000000001014 0x18000000011383e3 0x030000000022707c

def z242 : W := mkw 0x977403be9ba0efa2 0x12ee8077d3741df4 0xfffc0fff9ff3ffe7 0x7fff81fff3fe7ffc

def z243 : W := mkw 0x0000804100000000 0x0000100820000000 0x6403c1c180000000 0x6c80783830000000

def z244 : W := mkw 0xe84483ffe000b2e0 0x9d08907ffc00165c 0x280001ffe00073e3 0x0500003ffc000e7c

def z245 : W := mkw 0x4602a16140000000 0x08c0542c28000000 0x6603f1f1e0000000 0x6cc07e3e3c000000

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x40003001e01c0079 0x880006003c03800f

def z247 : W := mkw 0x28e1c8c90d123240 0x051c391921a24648 0xbde3c1ce1d007382 0x77bc7839c3a00e70

def z248 : W := mkw 0x875401bc00206f02 0x10ea803780040de0 0xaffc01fe00007f86 0x75ff803fc0000ff0

def z249 : W := mkw 0x468bfd61565f5851 0x68d17fac2acbeb0a 0x7e03fff1fe1ffc7d 0xefc07ffe3fc3ff8f

def z250 : W := mkw 0x00081602a06585a8 0x000102c0540cb0b5 0x58003e01e3ff8fff 0x8b0007c03c7ff1ff

def z251 : W := mkw 0x39f9decb8dd7b2e1 0x273f3bd971baf65c 0xfdffcfcf9df3f3e3 0x7fbff9f9f3be7e7c

def z252 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xfffffffffe007c04 0x7fffffffffc00f80

def z253 : W := mkw 0x977c15bc1be56f02 0x12ef82b7837cade0 0xfffc3ffe1fffff86 0x7fff87ffc3fffff0

def z254 : W := mkw 0xe7dfbfffe04580a8 0xbcfbf7fffc08b015 0xe7ffffffe01f8079 0xfcfffffffc03f00f

def z255 : W := mkw 0x0000400004100000 0x0000080000820000 0x5403c0001c100000 0x6a80780003820000

def z256 : W := mkw 0x00e148880d122200 0x001c291101a24440 0xfde3cfce1d13f382 0x7fbc79f9c3a27e70

def z257 : W := mkw 0x906401bc1ba06f02 0x120c803783740de0 0x380001fe1fe07f86 0x0700003fc3fc0ff0

def z258 : W := mkw 0x971c1736b2e5cdaa 0x12e382e6d65cb9b5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z259 : W := mkw 0x0600012012004800 0x00c0002402400900 0x0200003002000c04 0x0040000600400180

def z260 : W := mkw 0x0020000009002200 0x0004000001200440 0x180000001d007382 0x0300000003a00e70

def z261 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0000e0001138000 0x5a0001c000227000

def z262 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xe7ffffffe1e38382 0x7cfffffffc3c7070

def z263 : W := mkw 0x4000c16156185850 0x4800182c2ac30b0a 0x380001f1fe1c7c7d 0x8700003e3fc38f8f

def z264 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x07fff0001eec0000 0x20fffe0003dd8000

def z265 : W := mkw 0x080000000000b2e0 0x010000000000165c 0x08000000000073e3 0x0100000000000e7c

def z266 : W := mkw 0x39f91e8a89c7a2a1 0x273f23d15138f454 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z267 : W := mkw 0xe646e3fff6185850 0xdcc8dc7ffec30b0a 0x7e03f1fffe1c7c7d 0xefc07e3fffc38f8f

def z268 : W := mkw 0x97f549bc1fb26f02 0x12fea93783f64de0 0xffffcffe1ff3ff86 0x7ffff9ffc3fe7ff0

def z269 : W := mkw 0x57b3e9615f9a5851 0x6af67d2c2bf34b0a 0x7fe3f1f1fe1c7c7d 0xeffc7e3e3fc38f8f

def z270 : W := mkw 0x4002e04156185850 0x48005c082ac30b0a 0x5803f001fe1c7c7d 0x8b007e003fc38f8f

def z271 : W := mkw 0x0008140000450000 0x000102800008a000 0x801c0e0001e38000 0x100381c0003c7000

def z272 : W := mkw 0x00000202a00080a8 0x0000004054001015 0x00000001e0000079 0x800000003c00000f

def z273 : W := mkw 0x00ad5e16ad7785a8 0x0015abc2d5aef0b5 0xfffffe3fffff8fff 0xffffffc7fffff1ff

def z274 : W := mkw 0x288bfe43845f90e1 0x25117fc8708bf21c 0x4003fe01801f8061 0x08007fc03003f00c

def z275 : W := mkw 0xf7ffffffffff85a9 0xbefffffffffff0b5 0xffffffffffff8fff 0xfffffffffffff1ff

def z276 : W := mkw 0xbff50bbe9ba2efa2 0x17fea177d3745df4 0xbffc0ffe1fe3ff86 0x77ff81ffc3fc7ff0

def z277 : W := mkw 0x11b95c000dd70001 0x22372b8001bae000 0xd5ffce001df38000 0x7abff9c003be7000

def z278 : W := mkw 0x00000202806585a8 0x00000040500cb0b5 0xf8000e0f83ff8fff 0xdf0001c1f07ff1ff

def z279 : W := mkw 0xd71e353472cd0001 0xbae3c6a68e59a000 0x021c303062ec0000 0x004386060c5d8000

def z280 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0x2de3c1cf9c0073e3 0x25bc7839f3800e7c

def z281 : W := mkw 0x2881ca43841290e0 0x051039487082521c 0xf803ce0f811383e3 0x5f0079c1f022707c

def z282 : W := mkw 0x000c1616a0000000 0x000182c2d4000000 0xfa1c3e3fe21c0c7d 0xdf4387c7fc43818f

def z283 : W := mkw 0x4602a16152084810 0x48c0542c2a410902 0x6603f1f1e20c0c1c 0xecc07e3e3c418183

def z284 : W := mkw 0x08004000041290e0 0x010008000082521c 0x0000000000138061 0x000000000002700c

def z285 : W := mkw 0x0000400004101040 0x0000080000820208 0x180000001c107061 0x0300000003820e0c

def z286 : W := mkw 0xd716e17556b85d52 0x5ae2dc2eaad70baa 0x7e1ff1f1fefc7c7d 0xefc3fe3e3fdf8f8f

def z287 : W := mkw 0x11bd1e16a9e785a9 0x2237a3c2d53cf0b5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z288 : W := mkw 0x0060008809002200 0x000c001101200440 0x05e001c01c007000 0x20bc003803800e00

def z289 : W := mkw 0x0004001400200500 0x00008002800400a0 0xfa1c303fe3fc0fff 0xdf438607fc7f81ff

def z290 : W := mkw 0x0000000000650508 0x00000000000ca0a1 0x0000000002ec0c1c 0x80000000005d8183

def z291 : W := mkw 0x0000000012004800 0x0000000002400900 0x180000001e007c04 0x0300000003c00f80

def z292 : W := mkw 0x4002e04144181050 0x48005c082883020a 0x4003f001e01c0079 0x88007e003c03800f

def z293 : W := mkw 0x00081602a04580a8 0x000102c05408b015 0x7a003e31e21f8c7d 0xcf4007c63c43f18f

def z294 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0x85e3cfce1d03f382 0x30bc79f9c3a07e70

def z295 : W := mkw 0xe7d3e9e956185850 0xfcfa7d3d2ac30b0a 0x05e3c1c01c007000 0x20bc783803800e00

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x02003030620c0c1c 0x804006060c418183

def z297 : W := mkw 0x173814001bc50000 0x02e702800378a000 0xd7fc3e001fff8000 0x7aff87c003fff000

def z298 : W := mkw 0x00081400006585a8 0x00010280000cb0b5 0xda1c3e0003ff8fff 0xdb4387c0007ff1ff

def z299 : W := mkw 0x284082cb8000b2e0 0x050810597000165c 0xf8000fcf8113f3e3 0x5f0001f9f0227e7c

def z300 : W := mkw 0x173000001b800000 0x02e6000003700000 0x05e000001c000000 0x20bc000003800000

def z301 : W := mkw 0x17bb7e02bfdf80a9 0x22f76fc057fbf015 0xd7fffe01ffff8079 0xfaffffc03ffff00f

def z302 : W := mkw 0xd776a1fd5ba06f02 0x1aeed43fab740de0 0xfffff1ffffe07f86 0x7ffffe3ffffc0ff0

def z303 : W := mkw 0xe7d3abebc0000000 0xbcfa757d78000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z304 : W := mkw 0xf7ffbfffe9c70001 0xbefff7fffd38e000 0xe7ffffffe1e38000 0x7cfffffffc3c7000

def z305 : W := mkw 0x0008140000450000 0x000102800008a000 0x40003e00001f8000 0x080007c00003f000

def z306 : W := mkw 0xc71e3736e0000000 0xb8e3c6e6dc000000 0xe21c3e3fe0000000 0x5c4387c7fc000000

def z307 : W := mkw 0xe7dfffffe45f0001 0xbcfbfffffc8be000 0xe7ffffffe01f8000 0x7cfffffffc03f000

def z308 : W := mkw 0x4602e16156180000 0x08c05c2c2ac30000 0x7603f1f1fe1c0000 0x6ec07e3e3fc38000

def z309 : W := mkw 0x3fbbfe439fdf90e1 0x27f77fc873fbf21c 0xd7fffe019fff8061 0x7affffc033fff00c

def z310 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x5603f1c01e1c7000 0x6ac07e3803c38e00

def z311 : W := mkw 0x00040216a02085a8 0x00008042d40410b5 0xba1c003fe3e00fff 0xd7438007fc7c01ff

def z312 : W := mkw 0x6ee3e9e95f1a7a50 0x4ddc7d3d2be34f4a 0x05e3c1c01c007000 0x20bc783803800e00

def z313 : W := mkw 0x460af561565d5850 0x48c15eac2acbab0a 0xfe1ffff1fffffc7d 0xffc3fffe3fffff8f

def z314 : W := mkw 0x008b7c00045f0001 0x20116f80008be000 0xd21ffe0003ff8000 0x5a43ffc0007ff000

def z315 : W := mkw 0x8004013400204d02 0x10008026800409a0 0x0000003000000c04 0x0000000600000180

def z316 : W := mkw 0x17bf7e16bfdf0001 0x22f7efc2d7fbe000 0xf7fffe3fffff8000 0x7effffc7fffff000

def z317 : W := mkw 0x00836800041a0001 0x20106d0000834000 0x0003c00000000000 0x0000780000000000

def z318 : W := mkw 0xf7ffffffff9a0001 0xbefffffffff34000 0xe7fffffffc000000 0x7cffffffff800000

def z319 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xfffffe31ffff8c7d 0xffffffc63ffff18f

def z320 : W := mkw 0x1118140000c50001 0x222302800018a000 0x001c000000e00000 0x00038000001c0000

def z321 : W := mkw 0xc75e35bc60000000 0xb8ebc6b78c000000 0xa7fc31fe60000000 0x74ff863fcc000000

def z322 : W := mkw 0xe7dfbfffe0200500 0xbcfbf7fffc0400a0 0xffffffffe3e00f86 0x7ffffffffc7c01f0

def z323 : W := mkw 0x00040216a0000000 0x00008042d4000000 0x2000003fe0000000 0x04000007fc000000

def z324 : W := mkw 0x875c17bea0000000 0x10eb82f7d4000000 0xe7fc3fffe0000000 0x7cff87fffc000000

def z325 : W := mkw 0x3ffffedfbfffb7e9 0x27ffffdbf7fff6fd 0xffffffffffffffff 0xffffffffffffffff

def z326 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xf81c0e0f81f383e3 0x5f0381c1f03e707c

def z327 : W := mkw 0x0004001400200500 0x00008002800400a0 0x801c000e01e00382 0x10038001c03c0070

def z328 : W := mkw 0x000c1616a00080a0 0x000182c2d4001014 0xfa1c3e3fe11383e3 0x5f4387c7fc22707c

def z329 : W := mkw 0x3ffbfcc91fdf3241 0x27ff7f9923fbe648 0xd7ffffc01ffff000 0x7afffff803fffe00

def z330 : W := mkw 0x00081602a04580a8 0x000102c05408b015 0x00000e0000038000 0x000001c000007000

def z331 : W := mkw 0x5732e1615f985850 0x4ae65c2c2bf30b0a 0xfffff1f1fffc7c7d 0xfffffe3e3fff8f8f

def z332 : W := mkw 0x2889de43a45790e8 0x05113bc8748af21d 0x4003fe01e01f8079 0x88007fc03c03f00f

def z333 : W := mkw 0x9774009c1ba02702 0x12ee8013837404e0 0x97fc000e1fe00382 0x72ff8001c3fc0070

def z334 : W := mkw 0x4602e04156181050 0x48c05c082ac3020a 0x5603f001fe1c0079 0xeac07e003fc3800f

def z335 : W := mkw 0x0600012012004800 0x00c0002402400900 0x040001c01c007000 0x2080003803800e00

def z336 : W := mkw 0x00000000006585a8 0x00000000000cb0b5 0x0000000001e38382 0x00000000003c7070

def z337 : W := mkw 0x079f3e16a0000000 0x20f3e7c2d4000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z338 : W := mkw 0x000c141420000000 0x0001828284000000 0x021c303060000000 0x004386060c000000

def z339 : W := mkw 0x4606e377f638ddf8 0x48c0dc6efec71bbf 0x7e03f1fffe1c7fff 0xefc07e3fffc38fff

def z340 : W := mkw 0xd71e353472a04d02 0xbae3c6a68e5409a0 0x021c303062e00c04 0x004386060c5c0180

def z341 : W := mkw 0x2ee3eacb9f1ab2e0 0x05dc7d5973e3565c 0xffe3ffcf9f1ff3e3 0x7ffc7ff9f3e3fe7c

def z342 : W := mkw 0x977001a81b806a02 0x12ee003503700d40 0xbde001ce1d007382 0x77bc0039c3a00e70

def z343 : W := mkw 0x00040216a02085a8 0x00008042d40410b5 0x7a00303fe21c0fff 0xcf400607fc4381ff

def z344 : W := mkw 0x000c141400650500 0x00018282800ca0a0 0xfa1c3e3e03ff8f86 0x5f4387c7c07ff1f0

def z345 : W := mkw 0xe7dffffff6185850 0xfcfbfffffec30b0a 0xe7fffffffc007000 0x7cffffffff800e00

def z346 : W := mkw 0xc71e353460000000 0xb8e3c6a68c000000 0x021c303060000000 0x004386060c000000

def z347 : W := mkw 0xc71ef57576185850 0xf8e3deaeaec30b0a 0x7e1ff1f1fe1c7c7d 0xefc3fe3e3fc38f8f

def z348 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x83fc003e03e00f86 0x107f8007c07c01f0

def z349 : W := mkw 0x17b368001f9a0001 0x22f66d0003f34000 0x57e3f0001e1c0000 0x6afc7e0003c38000

def z350 : W := mkw 0x20e18acb89002200 0x041c315971200440 0xfde3cfcf9d007382 0x7fbc79f9f3a00e70

def z351 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0x2a1c303fe2ec0fff 0x85438607fc5d81ff

def z352 : W := mkw 0x177000881b802200 0x02ee001103700440 0xbffc01ce1fe07382 0x77ff8039c3fc0e70

def z353 : W := mkw 0x28e18acb8902b2e0 0x051c31597120565c 0xa9e00fcf8103f3e3 0x153c01f9f0207e7c

def z354 : W := mkw 0xf7ffffffffb87f52 0xfefffffffff70fea 0xfffffffffffc7fff 0xffffffffffff8fff

def z355 : W := mkw 0x17bf7c143fff0509 0x22f7ef8287ffe0a1 0xd7fffe307fff8c1c 0xfaffffc60ffff183

def z356 : W := mkw 0x102400141ba06f02 0x0204800283740de0 0xba1c003e1fe07f86 0x57438007c3fc0ff0

def z357 : W := mkw 0x008b3c0000000000 0x2011678000000000 0x4003fe0000000000 0x08007fc000000000

def z358 : W := mkw 0x977001a81ba06f02 0x12ee003503740de0 0x1de001c01fe07f86 0x23bc003803fc0ff0

def z359 : W := mkw 0x00a95c000d570000 0x00152b8001aae000 0xd7fffe001fff8000 0x7affffc003fff000

def z360 : W := mkw 0x17b368001f9a0001 0x22f66d0003f34000 0xd5e3ce001d138000 0x7abc79c003a27000

def z361 : W := mkw 0x4000c16144105850 0x4800182c28820b0a 0x7c03c1f1fc107c7d 0xef80783e3f820f8f

def z362 : W := mkw 0x0000804100001040 0x0000100820000208 0x280001c180007061 0x0500003830000e0c

def z363 : W := mkw 0x0004001400000000 0x0000800280000000 0xa21c003e00000000 0x54438007c0000000

def z364 : W := mkw 0x008b7e02a45f80a9 0x20116fc0548bf015 0x4003fe01e01f8079 0x88007fc03c03f00f

def z365 : W := mkw 0x57bbfd615fdf5851 0x6af77fac2bfbeb0a 0xd7ffffc01ffff000 0x7afffff803fffe00

def z366 : W := mkw 0xe04c97ffe06585a8 0x9c0992fffc0cb0b5 0xfa1c3fffe3ff8fff 0xdf4387fffc7ff1ff

def z367 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0xc1fffe0fe0000000 0x183fffc1fc000000

def z368 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xba1c0e3e03e38f86 0x574381c7c07c71f0

def z369 : W := mkw 0x977c15bc3be56f0a 0x12ef82b7877cade1 0xbffc31fe7fec7f9e 0xf7ff863fcffd8ff3

def z370 : W := mkw 0x4002e04144181050 0x48005c082883020a 0x0003c00000000000 0x0000780000000000

def z371 : W := mkw 0x5622e1615fdf5851 0x4ac45c2c2bfbeb0a 0x7e03f1f1fffffc7d 0xefc07e3e3fffff8f

def z372 : W := mkw 0x0000c243841090e0 0x000018487082121c 0xfc03cfcf9d13f3e3 0x7f8079f9f3a27e7c

def z373 : W := mkw 0x4000012040004810 0x4800002408000902 0x0000003060000c1c 0x800000060c000183

def z374 : W := mkw 0x000c1616a0650508 0x000182c2d40ca0a1 0xe21c3e3fe2ec0c1c 0xdc4387c7fc5d8183

def z375 : W := mkw 0x20cd9edfa06585a8 0x0419b3dbf40cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z376 : W := mkw 0x28e10a8a8902a2a0 0x051c215151205454 0xbde00fce1d03f382 0x77bc01f9c3a07e70

def z377 : W := mkw 0x102040001fff85a9 0x0204080003fff0b5 0x180000001fff8fff 0x8300000003fff1ff

def z378 : W := mkw 0x01991c0000000000 0x2033238000000000 0x81fc0e0000000000 0x103f81c000000000

def z379 : W := mkw 0x4602612056185850 0x48c04c240ac30b0a 0x1a0030307e1c7c7d 0x834006060fc38f8f

def z380 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0x981c0e0e03ff8fff 0x930381c1c07ff1ff

def z381 : W := mkw 0x400c9777e065ddf8 0x480192eefc0cbbbf 0xfa1c3fffe3ffffff 0xdf4387fffc7fffff

def z382 : W := mkw 0xb7f58bff9ba06f02 0x16feb17ff3740de0 0xffffcfff9fe07f86 0x7ffff9fff3fc0ff0

def z383 : W := mkw 0x00040216a02085a8 0x00008042d40410b5 0x0000000e00000382 0x00000001c0000070

def z384 : W := mkw 0x804401bc00206f02 0x1008803780040de0 0xba1c01fe03e07f86 0x5743803fc07c0ff0

def z385 : W := mkw 0xd772e1e95f987a52 0x5aee5c3d2bf30f4a 0x7fe3f1f1fe1c7c7d 0xeffc7e3e3fc38f8f

def z386 : W := mkw 0x204082cb80000000 0x0408105970000000 0x200001cf80000000 0x04000039f0000000

def z387 : W := mkw 0x00040216a06585a8 0x00008042d40cb0b5 0x3800003fe3ff8fff 0x87000007fc7ff1ff

def z388 : W := mkw 0x179b7c0016df0001 0x22f36f8002dbe000 0x421ffe0002ff8000 0x0843ffc0005ff000

def z389 : W := mkw 0x864401bc12206f02 0x10c8803782440de0 0x3e0001fe1e007f86 0x67c0003fc3c00ff0

def z390 : W := mkw 0x1020000009c70001 0x020400000138e000 0x0000000001e38000 0x00000000003c7000

def z391 : W := mkw 0x66c3abebc0000000 0x0cd8757d78000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z392 : W := mkw 0xe79fbf77e0000000 0xbcf3f7eefc000000 0x421ffe31e0000000 0x0843ffc63c000000

def z393 : W := mkw 0x00000000004580a8 0x000000000008b015 0x00000000001f8079 0x800000000003f00f

def z394 : W := mkw 0x0000000000000000 0x0000000000000000 0x28000031e0000c7d 0x850000063c00018f

def z395 : W := mkw 0x20c10a8a80000000 0x0418215150000000 0x81e00e0e00000000 0x103c01c1c0000000

def z396 : W := mkw 0x0060028a8900a2a0 0x000c005151201454 0xfde00fcf9d13f3e3 0x7fbc01f9f3a27e7c

def z397 : W := mkw 0x000c141420650508 0x00018282840ca0a1 0x7a1c3031e2fc0c7d 0xcf4386063c5f818f

def z398 : W := mkw 0x00000000006585a8 0x00000000000cb0b5 0x7a003031e3ff8fff 0xcf4006063c7ff1ff

def z399 : W := mkw 0x608bbe43e04580a8 0xac1177c87c08b015 0x4003fe01e01f8079 0x88007fc03c03f00f

def z400 : W := mkw 0xc756a1fd40000000 0x18ead43fa8000000 0xe7fff1ffe0000000 0x7cfffe3ffc000000

def z401 : W := mkw 0xa7dd1fbea0000000 0xb4fba3f7d4000000 0xa7fc0ffe00000000 0x74ff81ffc0000000

def z402 : W := mkw 0x77bbfe43ffdf0001 0xaef77fc87ffbe000 0xd7fffe01ffff8000 0x7affffc03ffff000

def z403 : W := mkw 0x1000000012cd0001 0x020000000259a000 0x0000000002ec0000 0x00000000005d8000

def z404 : W := mkw 0xe0c58bffe0000000 0x9c18b17ffc000000 0xe5e3cfffe0000000 0x7cbc79fffc000000

def z405 : W := mkw 0x28ed1e9ea967a7a8 0x051da3d3d52cf4f5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z406 : W := mkw 0x0064009c09202700 0x000c8013812404e0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z407 : W := mkw 0x286082cb8900b2e0 0x050c10597120165c 0xbde001cf9d0073e3 0x77bc0039f3a00e7c

def z408 : W := mkw 0x28e1c8c90d123240 0x051c391921a24648 0x7de3c1c19c107061 0x6fbc783833820e0c

def z409 : W := mkw 0x082042028d12b2e0 0x0104084051a2565c 0xf8000e0f9d13f3e3 0x5f0001c1f3a27e7c

def z410 : W := mkw 0xe7dbbfebe0000000 0xbcfb77fd7c000000 0x45e3ffc1e0000000 0x28bc7ff83c000000

def z411 : W := mkw 0x668bff63f6185850 0xecd17fec7ec30b0a 0x7e03fff1fe1c7c7d 0xefc07ffe3fc38f8f

def z412 : W := mkw 0x0004001400200500 0x00008002800400a0 0x2800003e00000f86 0x05000007c00001f0

def z413 : W := mkw 0xe7dfbfffe0206f02 0xbcfbf7fffc040de0 0xefffffffe0007f86 0x7dfffffffc000ff0

def z414 : W := mkw 0x0602200000000000 0x00c0440000000000 0x4603f00000000000 0x68c07e0000000000

def z415 : W := mkw 0x875001a800000000 0x10ea003500000000 0x05e001c000000000 0x20bc003800000000

def z416 : W := mkw 0xc71e353472084810 0xf8e3c6a68e410902 0x021c3030620c0c1c 0x804386060c418183

def z417 : W := mkw 0x17bb7c001f9a0001 0x22f76f8003f34000 0xc7fffe001c000000 0x78ffffc003800000

def z418 : W := mkw 0x977661bc1fb86f02 0x12eecc3783f70de0 0xfffff1fe1ffc7f86 0x7ffffe3fc3ff8ff0

def z419 : W := mkw 0x460e3534726d4d18 0x48c1c6a68e4da9a3 0x021c303062ec0c1c 0x804386060c5d8183

def z420 : W := mkw 0x0600012012004800 0x00c0002402400900 0x7e0031f1fe1c7c7d 0xefc0063e3fc38f8f

def z421 : W := mkw 0x917c169ea9e5a7aa 0x122f82d3d53cb4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z422 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x6603f1f1fc007000 0x6cc07e3e3f800e00

def z423 : W := mkw 0xffffffffffdfb2e1 0xbffffffffffbf65c 0xfffffffffffff3e3 0x7ffffffffffffe7c

def z424 : W := mkw 0x000c141420650508 0x00018282840ca0a1 0x001c000000e00000 0x00038000001c0000

def z425 : W := mkw 0x3ff1cacb9f92b2e0 0x07fe395973f2565c 0xffffcfcf9ff3f3e3 0x7ffff9f9f3fe7e7c

def z426 : W := mkw 0x00040014006585a8 0x00008002800cb0b5 0xba1c003e03ff8fff 0xd7438007c07ff1ff

def z427 : W := mkw 0xf7ffbffffb806a02 0xbefff7ffff700d40 0xe7fffffffc007000 0x7cffffffff800e00

def z428 : W := mkw 0x20891e02a0000000 0xa41123c054000000 0x00000e0000000000 0x000001c000000000

def z429 : W := mkw 0x97ff7fbebfffefab 0x32ffeff7d7fffdf5 0xffffffffffffffff 0xffffffffffffffff

def z430 : W := mkw 0x0602600016185850 0x40c04c0002c30b0a 0x5e03f0001e1c7c7d 0xebc07e0003c38f8f

def z431 : W := mkw 0x0710000000000000 0x00e2000000000000 0x87fc000000000000 0x70ff800000000000

def z432 : W := mkw 0xd77481fd5ba07f52 0x5aee903fab740fea 0xbffc01ffffe07fff 0xf7ff803ffffc0fff

def z433 : W := mkw 0x17b368001f9a0001 0x22f66d0003f34000 0x97ffc0001fe00000 0x72fff80003fc0000

def z434 : W := mkw 0x38e1cacb9fdfb2e1 0x071c395973fbf65c 0xfde3cfcf9ffff3e3 0x7fbc79f9f3fffe7c

def z435 : W := mkw 0x4602a16140005850 0x48c0542c28000b0a 0x6e03f1f1e0007c7d 0xedc07e3e3c000f8f

def z436 : W := mkw 0xe04081e940000000 0x9c08103d28000000 0x000001c000000000 0x0000003800000000

def z437 : W := mkw 0xd716213452a84d12 0x5ae2c4268a5509a2 0x021c303062ec0c1c 0x804386060c5d8183

def z438 : W := mkw 0x460ef777f6185850 0x48c1deeefec30b0a 0xfe1ffffffe1c7c7d 0xffc3ffffffc38f8f

def z439 : W := mkw 0x162001201ba06f02 0x02c4002403740de0 0x3e0001f01fe07f86 0x67c0003e03fc0ff0

def z440 : W := mkw 0x0602e04116181040 0x00c05c0822c30208 0x7e03f1c19e1c7061 0x6fc07e3833c38e0c

def z441 : W := mkw 0x977401bc1b800000 0x12ee803783700000 0xb7fc01fe1fe00000 0x76ff803fc3fc0000

def z442 : W := mkw 0x0000c04104101040 0x0000180820820208 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z443 : W := mkw 0x973401341ba04d02 0x12e68026837409a0 0x97fc00301fe00c04 0x72ff800603fc0180

def z444 : W := mkw 0x0600012000000000 0x00c0002400000000 0x260001f000000000 0x64c0003e00000000

def z445 : W := mkw 0x00a1080009020000 0x0014210001204000 0x81e00e0001038000 0x103c01c000207000

def z446 : W := mkw 0x28e5cadfad32b7e8 0x051cb95bf5a656fd 0xfde3cffffd13ffff 0xffbc79ffffa27fff

def z447 : W := mkw 0x977403bebba0efaa 0x12ee8077d7741df5 0xbffc01ffffe07fff 0xf7ff803ffffc0fff

def z448 : W := mkw 0x3ff3eacb9f9ab2e1 0x27fe7d5973f3565c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z449 : W := mkw 0x00000000002085a8 0x00000000000410b5 0x0800000000000fff 0x81000000000001ff

def z450 : W := mkw 0x0060008809002200 0x000c001101200440 0x81e0000e01000382 0x103c0001c0200070

def z451 : W := mkw 0xe04483ffe0005850 0xdc08907ffc000b0a 0x280001ffe0007c7d 0x8500003ffc000f8f

def z452 : W := mkw 0x102000001be5efaa 0x02040000037cbdf5 0x180000001fffffff 0x8300000003ffffff

def z453 : W := mkw 0x106000881ba06f02 0x020c001103740de0 0xbde001ce1fe07f86 0x77bc0039c3fc0ff0

def z454 : W := mkw 0x6eefffffff7ffff8 0x4dddffffffefffff 0xffffffffffffffff 0xffffffffffffffff

def z455 : W := mkw 0x0040008800000000 0x0008001100000000 0xa5e001ce00000000 0x74bc0039c0000000

def z456 : W := mkw 0x9170008809802202 0x122e001101300440 0x01e0000000000000 0x003c000000000000

def z457 : W := mkw 0xfff7ebffdfbafff2 0x5ffefd7ffbf75ffe 0xffffffffffffffff 0xffffffffffffffff

def z458 : W := mkw 0x068b7c00165f0001 0x20d16f8002cbe000 0x5603fe001e1f8000 0x6ac07fc003c3f000

def z459 : W := mkw 0xbff1cbeb9f92fae2 0x17fe397d73f25f5c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z460 : W := mkw 0x977441bc1fb87f52 0x52ee883783f70fea 0xbffc01fe1ffc7fff 0xf7ff803fc3ff8fff

def z461 : W := mkw 0x0600412016185850 0x40c0082402c30b0a 0x3e0001f01e1c7c7d 0xe7c0003e03c38f8f

def z462 : W := mkw 0x971e353412ed4d03 0x32e3c6a6825da9a0 0x021c303002ec0c04 0x00438606005d8180

def z463 : W := mkw 0x8154009c00000000 0x102a801380000000 0x81fc000e00000000 0x103f8001c0000000

def z464 : W := mkw 0xffffffffffb2ffe2 0xbffffffffff65ffc 0xfffffffffff3ffe7 0x7ffffffffffe7ffc

def z465 : W := mkw 0xe7dfffffe4181050 0xfcfbfffffc83020a 0xe7ffffffe01c0079 0xfcfffffffc03800f

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0xb800000e01000382 0x57000001c0200070

def z467 : W := mkw 0x082c5616ad77b7e8 0x01058ac2d5aef6fd 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z468 : W := mkw 0x000c1616a04580a8 0x000182c2d408b015 0xe21c3e3fe01f8079 0xdc4387c7fc03f00f

def z469 : W := mkw 0x2ffbfecb8d12b2e0 0x25ff7fd971a2565c 0xffffffcf9d13f3e3 0x7ffffff9f3a27e7c

def z470 : W := mkw 0x2881c84104121040 0x0510390820824208 0x0003c00000000000 0x0000780000000000

def z471 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0x821c3e3e63ef8f9e 0x904387c7cc7df1f3

def z472 : W := mkw 0xc646e1fd56387f52 0x58c8dc3faac70fea 0x7e03f1fffe1c7fff 0xefc07e3fffc38fff

def z473 : W := mkw 0x086040880d12b2e0 0x010c081101a2565c 0xbde001ce1d13f3e3 0x77bc0039c3a27e7c

def z474 : W := mkw 0x0000c04104101040 0x0000180820820208 0x0403c1c01c007000 0x2080783803800e00

def z475 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x1c03c1c01e1c7c7d 0xa380783803c38f8f

def z476 : W := mkw 0x97fd1dbc1be76f03 0x32ffa3b7837cede0 0xbffc0ffe1fe3ff86 0x77ff81ffc3fc7ff0

def z477 : W := mkw 0xe7dfbffff2084810 0xfcfbf7fffe410902 0xe7ffffffe20c0c1c 0xfcfffffffc418183

def z478 : W := mkw 0x20c18acb800080a0 0x0418315970001014 0xfde3cfcf811383e3 0x7fbc79f9f022707c

def z479 : W := mkw 0x973401341ba06f02 0x12e6802683740de0 0x1a1c00301fe07f86 0x0343800603fc0ff0

def z480 : W := mkw 0x977401bc1be5efaa 0x12ee8037837cbdf5 0xbffc01fe1fffffff 0xf7ff803fc3ffffff

def z481 : W := mkw 0x00a148000d120000 0x0014290001a24000 0x05e3c0001c000000 0x20bc780003800000

def z482 : W := mkw 0x171e341432ed0509 0x22e3c682865da0a1 0x021c303062ec0c1c 0x804386060c5d8183

def z483 : W := mkw 0xe7dfbfffe02085a8 0xbcfbf7fffc0410b5 0xefffffffe0000fff 0xfdfffffffc0001ff

def z484 : W := mkw 0xefffffffed123240 0xbdfffffffda24648 0xe7fffffffc007000 0x7cffffffff800e00

def z485 : W := mkw 0xeff3ebebcd12b2e0 0xbdfe7d7d79a2565c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z486 : W := mkw 0x0000400004181050 0x400008000083020a 0x00000000001c0079 0x800000000003800f

def z487 : W := mkw 0x6ee3e9e95f1a7a50 0x4ddc7d3d2be34f4a 0x7fe3f1f1fe1c7c7d 0xeffc7e3e3fc38f8f

def z488 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xffe3ffffff1fffff 0xfffc7fffffe3ffff

def z489 : W := mkw 0x173001201b804800 0x02e6002403700900 0xbffc01f01fe07c04 0x77ff803e03fc0f80

def z490 : W := mkw 0x0000000012084810 0x4000000002410902 0x00000000020c0c1c 0x8000000000418183

def z491 : W := mkw 0x284080c900003240 0x0508101920000648 0x000001c000007000 0x0000003800000e00

def z492 : W := mkw 0x0000000000206f02 0x0000000000040de0 0x0800000000007f86 0x0100000000000ff0

def z493 : W := mkw 0x000c1414206585a8 0x00018282840cb0b5 0x1a1c303063ff8fff 0x834386060c7ff1ff

def z494 : W := mkw 0x11b91c0009c70001 0x223723800138e000 0xd3fc3e0003ff8000 0x5a7f87c0007ff000

def z495 : W := mkw 0x1710000012800000 0x02e2000002500000 0x021c000002e00000 0x00438000005c0000

def z496 : W := mkw 0x9174009c1ba06f02 0x122e801383740de0 0x99fc000e1fe07f86 0x133f8001c3fc0ff0

def z497 : W := mkw 0x102c1616bbe5efaa 0x020582c2d77cbdf5 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z498 : W := mkw 0xbffddfffbff7ffea 0x17ffbbfff7fefffd 0xffffffffffffffff 0xffffffffffffffff

def z499 : W := mkw 0x811c141420000000 0xb023828284000000 0x001c000000000000 0x0003800000000000

def z500 : W := mkw 0x11b1080009820001 0x2236210001304000 0x01e0000000000000 0x003c000000000000

def z501 : W := mkw 0x4000816140005850 0x4800102c28000b0a 0x7a0031f1e21c7c7d 0xcf40063e3c438f8f

def z502 : W := mkw 0x0000c04104101040 0x0000180820820208 0x4003c00180100061 0x080078003002000c

def z503 : W := mkw 0xd7fffdfd5fff7f53 0x7affffbfabffefea 0xffffffffffffffff 0xffffffffffffffff

def z504 : W := mkw 0x4602212052084810 0x48c044240a410902 0x3e0031f07e0c7c1c 0xe7c0063e0fc18f83

def z505 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xe21c3e3fe1e38382 0x5c4387c7fc3c7070

def z506 : W := mkw 0x000c141420650508 0x00018282840ca0a1 0xd21c3e3063ff8c1c 0xda4387c60c7ff183

def z507 : W := mkw 0xe7dfbfffe0450000 0xbcfbf7fffc08a000 0xf7ffffffe3ff8000 0x7efffffffc7ff000

def z508 : W := mkw 0xa7d58bff80000000 0x14fab17ff0000000 0xe7ffcfff80000000 0x7cfff9fff0000000

def z509 : W := mkw 0x668bbf63e0000000 0xacd177ec7c000000 0x6603fff1e0000000 0x6cc07ffe3c000000

def z510 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xc01c3e0fe1ff83fb 0x980387c1fc3ff07f

def z511 : W := mkw 0x10ab7c001fdf0001 0x22156f8003fbe000 0x5003fe001fff8000 0x0a007fc003fff000

def z512 : W := mkw 0x28e18acb8902a2a0 0x051c315971205454 0xe5e3cfcf81038382 0x7cbc79f9f0207070

def z513 : W := mkw 0x9714013412a04d02 0x12e28026825409a0 0xba1c003e03e00f86 0x57438007c07c01f0

def z514 : W := mkw 0x28e9decbad57b2e8 0x051d3bd975aaf65d 0xfde3ffcffd1ff3fb 0xffbc7ff9ffa3fe7f

def z515 : W := mkw 0x28e1cacb9f1afaf0 0x451c395973e35f5e 0xfde3cfcf9f1fffff 0xffbc79f9f3e3ffff

def z516 : W := mkw 0x4602a16152004800 0x08c0542c2a400900 0x7e03f1f1fe007c04 0x6fc07e3e3fc00f80

def z517 : W := mkw 0x17fb7c881fdf2201 0x22ff6f9103fbe440 0xffffffce1ffff382 0x7ffffff9c3fffe70

def z518 : W := mkw 0x20e1cacb8d120000 0x041c395971a24000 0xf5e3cfcf9d138000 0x7ebc79f9f3a27000

def z519 : W := mkw 0x17bbfc411fdf1041 0x22f77f8823fbe208 0xffffffc19ffff061 0x7ffffff833fffe0c

def z520 : W := mkw 0xbff5c9fd1fb27f42 0x17feb93fa3f64fe8 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z521 : W := mkw 0x000c1616a02085a8 0x000182c2d40410b5 0xea1c3e3fe0000fff 0xdd4387c7fc0001ff

def z522 : W := mkw 0x6883ea43c41a90f0 0x4d107d487883521e 0x4003fe01e01f8079 0x88007fc03c03f00f

def z523 : W := mkw 0xf7f3e9e95f9a0001 0xbefe7d3d2bf34000 0x05e3c1c01c000000 0x20bc783803800000

def z524 : W := mkw 0x46a3e9615f1a5850 0x48d47d2c2be34b0a 0xffe3fff1ff1ffc7d 0xfffc7ffe3fe3ff8f

def z525 : W := mkw 0x0000012000004800 0x0000002400000900 0x280001f000007c04 0x0500003e00000f80

def z526 : W := mkw 0x408bfc41445f1051 0x68117f88288be20a 0x4003fe01e01f8079 0x88007fc03c03f00f

def z527 : W := mkw 0x400a340060000000 0xa80146800c000000 0x0000300060000000 0x000006000c000000

def z528 : W := mkw 0x460ef575767d5d58 0x48c1deaeaecfabab 0x7e1ff1f1fefc7c7d 0xefc3fe3e3fdf8f8f

def z529 : W := mkw 0x7ffbffebdfdffaf1 0x6fff7ffd7bfbff5e 0xffffffffffffffff 0xffffffffffffffff

def z530 : W := mkw 0x4600816152005850 0x48c0102c2a400b0a 0x3e0001f1fe007c7d 0xe7c0003e3fc00f8f

def z531 : W := mkw 0x460eb777e0000000 0x08c1d6eefc000000 0xe61fffffe0000000 0x7cc3fffffc000000

def z532 : W := mkw 0x57bbfd615fdf0001 0x2af77fac2bfbe000 0xf7fffff1ffff8000 0x7efffffe3ffff000

def z533 : W := mkw 0xe7d3e9e956185850 0xfcfa7d3d2ac30b0a 0x7fe3f1f1fe1c7c7d 0xeffc7e3e3fc38f8f

def z534 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x67e3f1f1e0000000 0x6cfc7e3e3c000000

def z535 : W := mkw 0x806401bc09206f02 0x100c803781240de0 0xbde001fe1d007f86 0x77bc003fc3a00ff0

def z536 : W := mkw 0x000c5616b67dddf8 0x40018ac2d6cfbbbf 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z537 : W := mkw 0x4002e16144185850 0x48005c2c28830b0a 0x6803f1f1e01c7c7d 0x8d007e3e3c038f8f

def z538 : W := mkw 0x97f769bc1fba6f03 0x32feed3783f74de0 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z539 : W := mkw 0x28e1c8c90d123240 0x051c391921a24648 0xd5e3cfc01d13f000 0x7abc79f803a27e00

def z540 : W := mkw 0x37fbfecb9fdf0001 0x26ff7fd973fbe000 0xf7ffffcf9fff8000 0x7efffff9f3fff000

def z541 : W := mkw 0xf7fbfde95fdf0001 0xbeff7fbd2bfbe000 0xd7ffffc01fff8000 0x7afffff803fff000

def z542 : W := mkw 0x977c17bebbe5efaa 0x12ef82f7d77cbdf5 0xbffc0ffe1fe3ff86 0x77ff81ffc3fc7ff0

def z543 : W := mkw 0x875c17bea06585a8 0x10eb82f7d40cb0b5 0xfffc3fffe3ff8fff 0xffff87fffc7ff1ff

def z544 : W := mkw 0x28eddedfad12b2e0 0x051dbbdbf5a2565c 0xfffffffffd13f3e3 0x7fffffffffa27e7c

def z545 : W := mkw 0x28c18acb8000b2e0 0x051831597000165c 0xede3cfcf800073e3 0x7dbc79f9f0000e7c

def z546 : W := mkw 0x608fbe57e0000000 0xac11f7cafc000000 0xe21ffe3fe0000000 0x5c43ffc7fc000000

def z547 : W := mkw 0x4662e1e95f187a50 0x48cc5c3d2be30f4a 0xffe3f1ffff1c7fff 0xfffc7e3fffe38fff

def z548 : W := mkw 0xe04c97ffe0000000 0x9c0992fffc000000 0xe21c3fffe0000000 0x5c4387fffc000000

def z549 : W := mkw 0x97bf7d341fff4d03 0x32f7efa683ffe9a0 0xd7fffe301fff8c04 0x7affffc603fff180

def z550 : W := mkw 0xf7ffbfffe9a02702 0xbefff7fffd3404e0 0xe7ffffffe1e00382 0x7cfffffffc3c0070

def z551 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xa81c0e3fe1e38fff 0x950381c7fc3c71ff

def z552 : W := mkw 0x8714013400000000 0x10e2802680000000 0x021c003000000000 0x0043800600000000

def z553 : W := mkw 0x20c1cacb84101040 0x0418395970820208 0xfde3cfcf9c107061 0x7fbc79f9f3820e0c

def z554 : W := mkw 0x17bb3c0009c70001 0x22f767800138e000 0xc7fffe0001e38000 0x78ffffc0003c7000

def z555 : W := mkw 0x0600000012000000 0x00c0000002400000 0x160000001e000000 0x62c0000003c00000

def z556 : W := mkw 0xefdfffffe41290e0 0xbdfbfffffc82521c 0xe7ffffffe0138061 0x7cfffffffc02700c

def z557 : W := mkw 0x00000202800080a0 0x0000004050001014 0x40000e0180138061 0x080001c03002700c

def z558 : W := mkw 0x971c153432e54d0a 0x12e382a6865ca9a1 0x021c303062ec0c1c 0x804386060c5d8183

def z559 : W := mkw 0xbff1c9e91f927a42 0x17fe393d23f24f48 0x05e3c1c01c007000 0x20bc783803800e00

def z560 : W := mkw 0xa1dd1e9ea06585a8 0xb43ba3d3d40cb0b5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z561 : W := mkw 0x060e7616b67d85a8 0x00c1cec2d6cfb0b5 0xfe1ffe3fffff8fff 0xffc3ffc7fffff1ff

def z562 : W := mkw 0x60008243e0000000 0x8c0010487c000000 0x00000001e0000000 0x000000003c000000

def z563 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0x45e3cfc19c13f061 0x28bc79f833827e0c

def z564 : W := mkw 0xa8e5cbff8d32ffe2 0x151cb97ff1a65ffc 0xfde3cfff9d13ffe7 0x7fbc79fff3a27ffc

def z565 : W := mkw 0xd77ef7fffffdfffa 0x5aefdeffffffbfff 0xffffffffffffffff 0xffffffffffffffff

def z566 : W := mkw 0x00a14a028d1280a0 0x0014294051a25014 0xfde3ce0f9d1383e3 0x7fbc79c1f3a2707c

def z567 : W := mkw 0x97fb7da81fdf6a03 0x32ff6fb503fbed40 0xd7ffffc01ffff000 0x7afffff803fffe00

def z568 : W := mkw 0xe7dfffffe4101040 0xbcfbfffffc820208 0xfffffffffc107061 0x7fffffffff820e0c

def z569 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x2c03c1f1fc007c7d 0xa580783e3f800f8f

def z570 : W := mkw 0x171e3616b2ed85a9 0x22e3c6c2d65db0b5 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z571 : W := mkw 0x173040001fdf0001 0x02e6080003fbe000 0x97fc00001fff8000 0x72ff800003fff000

def z572 : W := mkw 0x97f369a81f9a6a03 0x32fe6d3503f34d40 0x05e3c1c01c007000 0x20bc783803800e00

def z573 : W := mkw 0x173a34001bcd0001 0x22e746800379a000 0x97fc30001fec0000 0x72ff860003fd8000

def z574 : W := mkw 0x679bbe43e0000000 0xacf377c87c000000 0xc7fffe01e0000000 0x78ffffc03c000000

def z575 : W := mkw 0x9774c1fd1fb07f42 0x12ee983fa3f60fe8 0xffffc1ff9ff07fe7 0x7ffff83ff3fe0ffc

def z576 : W := mkw 0x4602212052084810 0x48c044240a410902 0x7a003031e21c0c7d 0xcf4006063c43818f

def z577 : W := mkw 0x27dbbecb80000000 0x24fb77d970000000 0xe7ffffcf80000000 0x7cfffff9f0000000

def z578 : W := mkw 0x571a352052cd4811 0x6ae346a40a59a902 0x021c303062ec0c1c 0x804386060c5d8183

def z579 : W := mkw 0x57bb7d205fdf4811 0x6af76fa40bfbe902 0xd7fffe307fff8c1c 0xfaffffc60ffff183

def z580 : W := mkw 0x804403bea020efaa 0x10088077d4041df5 0x280001ffe0007fff 0x8500003ffc000fff

def z581 : W := mkw 0xbf7483ff9ba0ffe2 0x17ee907ff3741ffc 0xbffc01ff9fe07fe7 0x77ff803ff3fc0ffc

def z582 : W := mkw 0x28eddedfad77b7e8 0x051dbbdbf5aef6fd 0xfdffcfcf9df3f3e3 0x7fbff9f9f3be7e7c

def z583 : W := mkw 0x0081480004120000 0x0010290000824000 0x4003ce0000138000 0x080079c000027000

def z584 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0x68003e3fe01f8fff 0x8d0007c7fc03f1ff

def z585 : W := mkw 0x00891c0000470001 0x201123800008e000 0x00000e0000038000 0x000001c000007000

def z586 : W := mkw 0x28e1cacb8d123240 0x051c395971a24648 0xe5e3cfcf9c007000 0x7cbc79f9f3800e00

def z587 : W := mkw 0x28e14a8a8d12b2e0 0x051c295151a2565c 0x99e00e0e1d13f3e3 0x133c01c1c3a27e7c

def z588 : W := mkw 0x688bfe43e41290e0 0xad117fc87c82521c 0x4003fe01e0138061 0x08007fc03c02700c

def z589 : W := mkw 0x00040216802085a0 0x00008042d00410b4 0xfa1c0e3f83f38fe7 0x5f4381c7f07e71fc

def z590 : W := mkw 0xd7bf7d347fdf0001 0xbaf7efa68ffbe000 0xd7fffe307fff8000 0x7affffc60ffff000

def z591 : W := mkw 0xaff5cbff8d12b2e0 0x15feb97ff1a2565c 0xffffcfff9d13f3e3 0x7ffff9fff3a27e7c

def z592 : W := mkw 0x4602e16144181050 0x48c05c2c2883020a 0x6603f1f1e01c0079 0xecc07e3e3c03800f

def z593 : W := mkw 0x17bf7e16bfff85a9 0x22f7efc2d7fff0b5 0xd7fffe0e1fff8382 0x7affffc1c3fff070

def z594 : W := mkw 0xd776e1fd5fb87f52 0x5aeedc3fabf70fea 0xbfffc1fe1fe07f86 0x77fff83fc3fc0ff0

def z595 : W := mkw 0x4000816140000000 0x0800102c28000000 0x200001f1e0000000 0x0400003e3c000000

def z596 : W := mkw 0x173400141ba00500 0x02e68002837400a0 0xbffc003e1fe00f86 0x77ff8007c3fc01f0

def z597 : W := mkw 0x3ffb7e8a9fdfa2a1 0x27ff6fd153fbf454 0xd7fffe0e1fff8382 0x7affffc1c3fff070

def z598 : W := mkw 0x0000400016185850 0x4000080002c30b0a 0x000000001c007000 0x0000000003800e00

def z599 : W := mkw 0x00081602804580a0 0x000102c05008b014 0xfa1c3e0f83ff83e3 0x5f4387c1f07ff07c

def z600 : W := mkw 0x4602a16140000000 0x08c0542c28000000 0x7e03f1f1e21c0c7d 0xefc07e3e3c43818f

def z601 : W := mkw 0x0004001400200500 0x00008002800400a0 0x021c003002e00c04 0x00438006005c0180

def z602 : W := mkw 0x28008243800090e0 0x050010487000121c 0x0000000180000061 0x000000003000000c

def z603 : W := mkw 0x4002a04140000000 0x0800540828000000 0x4003f001e0000000 0x08007e003c000000

def z604 : W := mkw 0x0820c0410d12b2e0 0x0104180821a2565c 0x7c03c1c19d13f3e3 0x6f80783833a27e7c

def z605 : W := mkw 0x977e35bc1bed6f03 0x32efc6b7837dade0 0xbffc31fe1fec7f86 0x77ff863fc3fd8ff0

def z606 : W := mkw 0x0000000000005850 0x4000000000000b0a 0x0800000000007c7d 0x8100000000000f8f

def z607 : W := mkw 0x102000001b800000 0x0204000003700000 0x100000001fe00000 0x0200000003fc0000

def z608 : W := mkw 0x10a148001fdf0001 0x0214290003fbe000 0xd5e3ce001fff8000 0x7abc79c003fff000

def z609 : W := mkw 0x0600c16116105840 0x00c0182c22c20b08 0x7e03c1f19e107c65 0x6fc0783e33c20f8c

def z610 : W := mkw 0x0002600004180000 0x00004c0000830000 0x4003f000001c0000 0x08007e0000038000

def z611 : W := mkw 0x977401bc1b806a02 0x12ee803783700d40 0xa7fc01fe1c007000 0x74ff803fc3800e00

def z612 : W := mkw 0x9114001400a00502 0x12228002801400a0 0x001c000000e00000 0x00038000001c0000

def z613 : W := mkw 0x0000c04116185850 0x4000180822c30b0a 0x7c03c1c19e1c7c7d 0xef80783833c38f8f

def z614 : W := mkw 0x0008140000450000 0x000102800008a000 0x021c300002ec0000 0x00438600005d8000

def z615 : W := mkw 0x4602a16152085850 0x48c0542c2a410b0a 0x2a0031f1e20c7c7d 0x8540063e3c418f8f

def z616 : W := mkw 0x804001a800006a02 0x1008003500000d40 0x000001c000007000 0x0000003800000e00

def z617 : W := mkw 0xe75eb7ffe0000000 0xbcebd6fffc000000 0x221c31ffe0000000 0x0443863ffc000000

def z618 : W := mkw 0xf7f3a9e95b806a02 0xbefe753d2b700d40 0x05e3c1c01c007000 0x20bc783803800e00

def z619 : W := mkw 0x00040216a02085a8 0x00008042d40410b5 0xf8000e3fe1138fff 0xdf0001c7fc2271ff

def z620 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x07fc01f01ee07c04 0x20ff803e03dc0f80

def z621 : W := mkw 0x0602200012080000 0x00c0440002410000 0x02003000020c0000 0x0040060000418000

def z622 : W := mkw 0xb7ff7e9ebfdf0001 0xb6ffefd3d7fbe000 0xd7fffe0e1fff8000 0x7affffc1c3fff000

def z623 : W := mkw 0x3ff3e8c91f9a3241 0x27fe7d1923f34648 0x05e3c1c01c007000 0x20bc783803800e00

def z624 : W := mkw 0x5622e1615fb87f52 0x4ac45c2c2bf70fea 0x7e03f1f1fffc7fff 0xefc07e3e3fff8fff

def z625 : W := mkw 0x079b7c00045f0001 0x20f36f80008be000 0xc7fffe00001f8000 0x78ffffc00003f000

def z626 : W := mkw 0x975401bc12a04d02 0x12ea8037825409a0 0xa7fc01fe02e00c04 0x74ff803fc05c0180

def z627 : W := mkw 0x4606e17556385d50 0x48c0dc2eaac70baa 0xfe1ff1fffffc7fff 0xffc3fe3fffff8fff

def z628 : W := mkw 0x17bb7e029fdf80a1 0x22f76fc053fbf014 0xfffffe0f9fff83e3 0x7fffffc1f3fff07c

def z629 : W := mkw 0x00081602a04580a8 0x000102c05408b015 0xf8003e0fe11f83fb 0xdf0007c1fc23f07f

def z630 : W := mkw 0x28e5cadf8d32b7e0 0x051cb95bf1a656fc 0xffffcfff9ff3ffe7 0x7ffff9fff3fe7ffc

def z631 : W := mkw 0xd772e1e95f987a52 0x5aee5c3d2bf30f4a 0x05e3c1c01c007000 0x20bc783803800e00

def z632 : W := mkw 0xe1dd9fffe0000000 0xbc3bb3fffc000000 0xa1fc0fffe0000000 0x143f81fffc000000

def z633 : W := mkw 0x0004001420200508 0x00008002840400a1 0x0000003060000c1c 0x800000060c000183

def z634 : W := mkw 0x102000001b806a02 0x0204000003700d40 0x000000001c007000 0x0000000003800e00

def z635 : W := mkw 0x6ee3ebebdf1afaf0 0x4ddc7d7d7be35f5e 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z636 : W := mkw 0xf7ffbffffb800000 0xbefff7ffff700000 0xf7ffffffffe00000 0x7efffffffffc0000

def z637 : W := mkw 0xe7df3fbee0000000 0xbcfbe7f7dc000000 0x83fc3e3e60000000 0x107f87c7cc000000

def z638 : W := mkw 0x460af763f65dd8f8 0x48c15eec7ecbbb1f 0x7e03fff1fe1ffc7d 0xefc07ffe3fc3ff8f

def z639 : W := mkw 0xe0cfbfffe0000000 0xbc19f7fffc000000 0x6003ffffe0000000 0x0c007ffffc000000

def z640 : W := mkw 0xbfffffff9fffffe3 0x37fffffff3fffffc 0xffffffff9fffffe7 0x7ffffffff3fffffc

def z641 : W := mkw 0xe7ffffffed120000 0xbcfffffffda24000 0xf7fffffffd138000 0x7effffffffa27000

def z642 : W := mkw 0x0008140020450008 0x000102800408a001 0x00003000600c0018 0x800006000c018003

def z643 : W := mkw 0x91fd1c9c09e72703 0x323fa393813ce4e0 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z644 : W := mkw 0x173260001f980000 0x02e64c0003f30000 0xd7fff0001ffc0000 0x7afffe0003ff8000

def z645 : W := mkw 0x1000000012a04d02 0x02000000025409a0 0x0000000002e00c04 0x00000000005c0180

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x921c000003e00000 0x52438000007c0000

def z647 : W := mkw 0x28810a02800280a0 0x0510214050005014 0x00000e0000038000 0x000001c000007000

def z648 : W := mkw 0x2ee1cbeb9f12fae0 0x05dc397d73e25f5c 0xffe3cfff9f13ffe7 0x7ffc79fff3e27ffc

def z649 : W := mkw 0xe04483ffe0206f02 0x9c08907ffc040de0 0x280001ffe0007f86 0x0500003ffc000ff0

def z650 : W := mkw 0x4002e04144181050 0x48005c082883020a 0x7c03f1c1fc1c7079 0xef807e383f838e0f

def z651 : W := mkw 0x917c169ea9e5a7aa 0x122f82d3d53cb4f5 0xfbfc3e3fe3ff8fff 0xdf7f87c7fc7ff1ff

def z652 : W := mkw 0x400af643e45d90f8 0x48015ec87c8bb21f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z653 : W := mkw 0xe75483ffe0000000 0x9cea907ffc000000 0xa7fc01ffe0000000 0x74ff803ffc000000

def z654 : W := mkw 0x4002200040080010 0x4800440008010002 0x00003000600c0018 0x800006000c018003

def z655 : W := mkw 0x00ab7c000d5f0001 0x20156f8001abe000 0xd5e3fe001d1f8000 0x7abc7fc003a3f000

def z656 : W := mkw 0x17bb7c001fff85a9 0x22f76f8003fff0b5 0xdffffe001fff8fff 0xfbffffc003fff1ff

def z657 : W := mkw 0x066001a81b006a00 0x00cc003503600d40 0xbfe001fe1f007f86 0x77fc003fc3e00ff0

def z658 : W := mkw 0xeff3e9e94d123240 0xbdfe7d3d29a24648 0x05e3c1c01c007000 0x20bc783803800e00

def z659 : W := mkw 0x28e10a8a8902a2a0 0x051c215151205454 0xf9e00e0f811383e3 0x5f3c01c1f022707c

def z660 : W := mkw 0x40048377e020ddf8 0x4800906efc041bbf 0x280001ffe0007fff 0x8500003ffc000fff

def z661 : W := mkw 0x28e1cacb8d77b7e8 0x051c395971aef6fd 0xfde3cfcf9fffffff 0xffbc79f9f3ffffff

def z662 : W := mkw 0x400ef657e47d95f8 0x4801decafc8fb2bf 0xfa1ffe3fe3ff8fff 0xdf43ffc7fc7ff1ff

def z663 : W := mkw 0xe646a3ffe0000000 0x9cc8d47ffc000000 0x6603f1ffe0000000 0x6cc07e3ffc000000

def z664 : W := mkw 0x4000816140005850 0x4800102c28000b0a 0x000001c000007000 0x0000003800000e00

def z665 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x7c03c1c19c107061 0x6f80783833820e0c

def z666 : W := mkw 0x2840028a8000a2a0 0x0508005150001454 0x0000000e00000382 0x00000001c0000070

def z667 : W := mkw 0x6e83eb63d61ad8f0 0x4dd07d6c7ac35b1e 0x7e03fff1fe1ffc7d 0xefc07ffe3fc3ff8f

def z668 : W := mkw 0x17bf7c141fff0501 0x22f7ef8283ffe0a0 0xfffffe3e1fff8f86 0x7fffffc7c3fff1f0

def z669 : W := mkw 0xf77483fffba06f02 0x9eee907fff740de0 0xbffc01ffffe07f86 0x77ff803ffffc0ff0

def z670 : W := mkw 0x000c141420650508 0x00018282840ca0a1 0xba1c303e63ec0f9e 0xd7438607cc7d81f3

def z671 : W := mkw 0x571af56156dd5851 0x6ae35eac2adbab0a 0x7e1ff1f1fefc7c7d 0xefc3fe3e3fdf8f8f

def z672 : W := mkw 0x0000000000000000 0x0000000000000000 0x52003000021c0000 0x4a40060000438000

def z673 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x4403f1c1fc1c7079 0xa8807e383f838e0f

def z674 : W := mkw 0x977001a81b806a02 0x12ee003503700d40 0x3fe001f01e007c04 0x67fc003e03c00f80

def z675 : W := mkw 0x17b91c001bc70001 0x22f723800378e000 0x97fc0e001fe38000 0x72ff81c003fc7000

def z676 : W := mkw 0xb1fd1e9ea9a02702 0xb63fa3d3d53404e0 0x81fc0e0e01e00382 0x103f81c1c03c0070

def z677 : W := mkw 0x17bb7c001fff6f03 0x22f76f8003ffede0 0xdffffe001fffff86 0x7bffffc003fffff0

def z678 : W := mkw 0x975401bc12a06f02 0x12ea803782540de0 0x2a1c01fe02e07f86 0x0543803fc05c0ff0

def z679 : W := mkw 0x4602612056184810 0x48c04c240ac30902 0x5603f0307e1c0c1c 0xeac07e060fc38183

def z680 : W := mkw 0x977401bc09a02702 0x12ee8037813404e0 0xa7fc01fe01e00382 0x74ff803fc03c0070

def z681 : W := mkw 0x875401bc12004800 0x10ea803782400900 0xbffc01fe1e007c04 0x77ff803fc3c00f80

def z682 : W := mkw 0x00004000167dddf8 0x4000080002cfbbbf 0x180000001fffffff 0x8300000003ffffff

def z683 : W := mkw 0x0000000000200500 0x00000000000400a0 0x1800000003e00f86 0x03000000007c01f0

def z684 : W := mkw 0x28c1cacb841290e0 0x051839597082521c 0xe5e3cfcf80138061 0x7cbc79f9f002700c

def z685 : W := mkw 0x4000804140001050 0x480010082800020a 0x00000001e0000079 0x800000003c00000f

def z686 : W := mkw 0x6e42e3ebd618faf0 0x4dc85c7d7ac31f5e 0x7e03f1fffe1c7fff 0xefc07e3fffc38fff

def z687 : W := mkw 0x006c169ea965a7a8 0x000d82d3d52cb4f5 0xfffc3fffffffffff 0xffff87ffffffffff

def z688 : W := mkw 0x0604013412204d00 0x00c08026824409a0 0xbe1c01fe1fe07f86 0x77c3803fc3fc0ff0

def z689 : W := mkw 0xd77e35bc7ba06f02 0xbaefc6b78f740de0 0xbffc31fe7fe07f86 0x77ff863fcffc0ff0

def z690 : W := mkw 0xefffffffff1afaf0 0xfdffffffffe35f5e 0xffffffffff1fffff 0xffffffffffe3ffff

def z691 : W := mkw 0xc04481fd40207f52 0x5808903fa8040fea 0x280001ffe0007fff 0x8500003ffc000fff

def z692 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xc1e3ce0f811383e3 0x183c79c1f022707c

def z693 : W := mkw 0x28c1cacb8412b2e0 0x051839597082565c 0x6803cfcf8013f3e3 0x0d0079f9f0027e7c

def z694 : W := mkw 0x0000000000450000 0x000000000008a000 0x1000000003ff8000 0x02000000007ff000

def z695 : W := mkw 0xa9fddedfad12b2e0 0xb53fbbdbf5a2565c 0xfdffcfcf9d13f3e3 0x7fbff9f9f3a27e7c

def z696 : W := mkw 0xe7dffffff6180000 0xbcfbfffffec30000 0xf7fffffffe1c0000 0x7effffffffc38000

def z697 : W := mkw 0x173c1616bbe585a8 0x02e782c2d77cb0b5 0xfffc3e3fffff8fff 0xffff87c7fffff1ff

def z698 : W := mkw 0x57b3e9615f9a5851 0x6af67d2c2bf34b0a 0x05e3c1c01c007000 0x20bc783803800e00

def z699 : W := mkw 0x173000001ba06f02 0x02e6000003740de0 0x9ffc00001fe07f86 0x73ff800003fc0ff0

def z700 : W := mkw 0x68e3eacbcd1ab2f0 0x4d1c7d5979a3565e 0xfde3ffcffd1ff3fb 0xffbc7ff9ffa3fe7f

def z701 : W := mkw 0xf7ffffffffdf5851 0xfefffffffffbeb0a 0xfffffffffffffc7d 0xffffffffffffff8f

def z702 : W := mkw 0xc756e1fd56185850 0x58eadc3faac30b0a 0xfffff1fffe1c7c7d 0xfffffe3fffc38f8f

def z703 : W := mkw 0x4602e16144101040 0x08c05c2c28820208 0x7e03f1f1fc107061 0x6fc07e3e3f820e0c

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x3a00003002000c04 0x4740000600400180

def z705 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x45e3fe001c1f8000 0x28bc7fc00383f000

def z706 : W := mkw 0x28e14a8a8d12a2a0 0x051c295151a25454 0xd5e3ce0e1d138382 0x7abc79c1c3a27070

def z707 : W := mkw 0x9174009c09a02702 0x122e8013813404e0 0x85fc01ce1de07382 0x30bf8039c3bc0e70

def z708 : W := mkw 0x977817aabbc5eaaa 0x12ef02f55778bd55 0x45e03fc1fc1ff079 0xa8bc07f83f83fe0f

def z709 : W := mkw 0xe0c189e940000000 0x9c18313d28000000 0x05e3c1c000000000 0x20bc783800000000

def z710 : W := mkw 0x102440141fb87f52 0x4204880283f70fea 0xfa1c303ffffc7fff 0xdf438607ffff8fff

def z711 : W := mkw 0x679fbe57e0000000 0xacf3f7cafc000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z712 : W := mkw 0x102854001fdf5851 0x42050a8003fbeb0a 0xfa1c3e31fffffc7d 0xdf4387c63fffff8f

def z713 : W := mkw 0x173401341ba04d00 0x02e68026837409a0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z714 : W := mkw 0x5020c1615fdf5851 0x4a04182c2bfbeb0a 0x380001f1fffffc7d 0x8700003e3fffff8f

def z715 : W := mkw 0x688bfe43e45f90f8 0x4d117fc87c8bf21f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z716 : W := mkw 0x1170008809802200 0x022e001101300440 0xbdfc01ce1de07382 0x77bf8039c3bc0e70

def z717 : W := mkw 0x11b91c0009c70001 0x223723800138e000 0xc5ffce0001e38000 0x78bff9c0003c7000

def z718 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xe5e3cfcf9d03f382 0x7cbc79f9f3a07e70

def z719 : W := mkw 0xfff3e9e95f9a7a52 0x5ffe7d3d2bf34f4a 0x05e3c1c01c007000 0x20bc783803800e00

def z720 : W := mkw 0x460ef777f67dddf8 0x48c1deeefecfbbbf 0x841fcfce1de3f382 0x3083f9f9c3bc7e70

def z721 : W := mkw 0x002040000d120000 0x0004080001a24000 0xd0000e001d138000 0x5a0001c003a27000

def z722 : W := mkw 0x082040000d1ab2f0 0x4104080001a3565e 0x180000001d1ff3fb 0x8300000003a3fe7f

def z723 : W := mkw 0xf7dfbffff2ed4d03 0xbefbf7fffe5da9a0 0xe7ffffffe2ec0c04 0x7cfffffffc5d8180

def z724 : W := mkw 0x179b3c0012cd0001 0x22f367800259a000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z725 : W := mkw 0xc75eb7ffe06585a8 0x18ebd6fffc0cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z726 : W := mkw 0x87d509bc00000000 0x10faa13780000000 0xe7ffcffe00000000 0x7cfff9ffc0000000

def z727 : W := mkw 0x11bb7c000ddf0001 0x22376f8001bbe000 0xd3fffe0003ff8000 0x5a7fffc0007ff000

def z728 : W := mkw 0x079f3c1400000000 0x20f3e78280000000 0xe7fffe3e00000000 0x7cffffc7c0000000

def z729 : W := mkw 0xf064c3ffffdf0001 0x9e0c987ffffbe000 0x300001ffffff8000 0x0600003ffffff000

def z730 : W := mkw 0x2889de43845790e0 0x05113bc8708af21c 0x4003fe01801f8061 0x08007fc03003f00c

def z731 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xffe3ffffe21c0c7d 0xfffc7ffffc43818f

def z732 : W := mkw 0x079b7c00045f0001 0x20f36f80008be000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z733 : W := mkw 0x0712200000000000 0x00e2440000000000 0xc7fff00000000000 0x78fffe0000000000

def z734 : W := mkw 0xcf3e75346d12b2e0 0xb9e7cea68da2565c 0x1a1c30307d13f3e3 0x034386060fa27e7c

def z735 : W := mkw 0x102040000ddf0001 0x0204080001bbe000 0x0000000001ff8000 0x00000000003ff000

def z736 : W := mkw 0xe7dbbfebe0000000 0xbcfb77fd7c000000 0x67e3fff1e0000000 0x6cfc7ffe3c000000

def z737 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0x9de3cfce1d13f3e3 0x33bc79f9c3a27e7c

def z738 : W := mkw 0xf7dfbffff2ed85a9 0xbefbf7fffe5db0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z739 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0xe5ffffcfe0000000 0x7cbffff9fc000000

def z740 : W := mkw 0xa1dd5e9eb6185850 0xf43babd3d6c30b0a 0x99fc0e0e1e1c7c7d 0x933f81c1c3c38f8f

def z741 : W := mkw 0xe7d7a9fd40000000 0xbcfaf53fa8000000 0x07ffc1f000000000 0x20fff83e00000000

def z742 : W := mkw 0xe7d7abffc0000000 0x1cfaf57ff8000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z743 : W := mkw 0xb1fd1e9ea9e5a7aa 0xb63fa3d3d53cb4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z744 : W := mkw 0x1064009c1ba06f02 0x020c801383740de0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z745 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xbffc01fe1ffc7fff 0xf7ff803fc3ff8fff

def z746 : W := mkw 0x20cd9edfa0000000 0x0419b3dbf4000000 0xe5ffcfcf80000000 0x7cbff9f9f0000000

def z747 : W := mkw 0x01991c0000450000 0x203323800008a000 0x81fc0e0001e38000 0x103f81c0003c7000

def z748 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x47fffff1e0000000 0x28fffffe3c000000

def z749 : W := mkw 0xf7d7a9fd52a04d02 0xbefaf53faa5409a0 0x07ffc1f002e00c04 0x20fff83e005c0180

def z750 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xadfc01fe1de07f86 0x35bf803fc3bc0ff0

def z751 : W := mkw 0x9174009c09a02702 0x122e8013813404e0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z752 : W := mkw 0x079f3c1400200500 0x20f3e782800400a0 0xfffffe3e03e00f86 0x7fffffc7c07c01f0

def z753 : W := mkw 0x102c5616bfdf0001 0x02058ac2d7fbe000 0xf21c3e3fffff8000 0x5e4387c7fffff000

def z754 : W := mkw 0x80cf7dbc047f6f03 0x3019efb7808fede0 0x6803fffe001fff86 0x0d007fffc003fff0

def z755 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x520030001fff8000 0x4a40060003fff000

def z756 : W := mkw 0x17bb7c001fdf5851 0x62f76f8003fbeb0a 0xfffffe31fffffc7d 0xffffffc63fffff8f

def z757 : W := mkw 0x28c18acb8000b2e0 0x051831597000165c 0xfde3cfcf8113f3e3 0x7fbc79f9f0227e7c

def z758 : W := mkw 0x619bbe43e0000000 0xac3377c87c000000 0xc1fffe01e0000000 0x183fffc03c000000

def z759 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x07e3f1f060000000 0x20fc7e3e0c000000

def z760 : W := mkw 0x182442169fb2ffe2 0x03048842d3f65ffc 0xfa1c0e3f9ff3ffe7 0x5f4381c7f3fe7ffc

def z761 : W := mkw 0xefdfbfffe000a2a0 0xbdfbf7fffc001454 0xe7ffffffe0000382 0x7cfffffffc000070

def z762 : W := mkw 0x079b3d2012004800 0x20f367a402400900 0xfffffff01e007c04 0x7ffffffe03c00f80

def z763 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xe7ffffffe3ef8f9e 0xfcfffffffc7df1f3

def z764 : W := mkw 0xa1dd9edfa06585a8 0xb43bb3dbf40cb0b5 0xfdffcfcf81f383e3 0x7fbff9f9f03e707c

def z765 : W := mkw 0x60c18acbe0000000 0x8c1831597c000000 0xe5e3cfcfe0000000 0x7cbc79f9fc000000

def z766 : W := mkw 0xc756a1fd40200500 0x18ead43fa80400a0 0xfffff1ffe3fc0fff 0xfffffe3ffc7f81ff

def z767 : W := mkw 0x20c1cacb841090e0 0x041839597082121c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z768 : W := mkw 0xe04483ffe020efaa 0x9c08907ffc041df5 0x280001ffe0007fff 0x8500003ffc000fff

def z769 : W := mkw 0xe7d3a9e9406585a8 0xbcfa753d280cb0b5 0x1de3c1c003ff8fff 0xa3bc7838007ff1ff

def z770 : W := mkw 0x28e14a8a8d12a2a0 0x051c295151a25454 0xfde3cfce1d13f382 0x7fbc79f9c3a27e70

def z771 : W := mkw 0xe7dfbfffe0650500 0xbcfbf7fffc0ca0a0 0xffffffffe3ff8f86 0x7ffffffffc7ff1f0

def z772 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x6c03f1f1fc1c7c7d 0xad807e3e3f838f8f

def z773 : W := mkw 0xf7dfbffff2ed0509 0xbefbf7fffe5da0a1 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z774 : W := mkw 0xe7d7abffc0000000 0xbcfaf57ff8000000 0xe7ffcfff80000000 0x7cfff9fff0000000

def z775 : W := mkw 0x17bb7d201fdf4801 0x22f76fa403fbe900 0xfffffff1fffffc7d 0xfffffffe3fffff8f

def z776 : W := mkw 0xa7d18beb80000000 0x14fa317d70000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z777 : W := mkw 0x102040000dd70001 0x0204080001bae000 0x100000001df38000 0x0200000003be7000

def z778 : W := mkw 0x079b3c0012000000 0x20f3678002400000 0xd7fffe001e000000 0x7affffc003c00000

def z779 : W := mkw 0x0600c16116105840 0x00c0182c22c20b08 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z780 : W := mkw 0x204482dfa02085a8 0x0408905bf40410b5 0x280001ffe0000fff 0x8500003ffc0001ff

def z781 : W := mkw 0x1793280012880001 0x22f2650002510000 0x05e3c00000000000 0x20bc780000000000

def z782 : W := mkw 0xe7d7abffe0000000 0xbcfaf57ffc000000 0xa7ffc1ffe0000000 0x74fff83ffc000000

def z783 : W := mkw 0x37dbbecb92cd0001 0x26fb77d97259a000 0xe7ffffcf82ec0000 0x7cfffff9f05d8000

def z784 : W := mkw 0x51b99d6149c75851 0x6a3733ac2938eb0a 0xa9fc0ff1e1e3fc7d 0x953f81fe3c3c7f8f

def z785 : W := mkw 0x479fbf77e0000000 0x28f3f7eefc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z786 : W := mkw 0x57bb7d205fdf5851 0x6af76fa40bfbeb0a 0xdffffe307ffffc7d 0xfbffffc60fffff8f

def z787 : W := mkw 0x20c99ecb80000000 0x041933d970000000 0xe7ffffcf80000000 0x7cfffff9f0000000

def z788 : W := mkw 0x082040000d32ffe2 0x0104080001a65ffc 0x180000001d13ffe7 0x0300000003a27ffc

def z789 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xd7fffe01ffff8079 0xfaffffc03ffff00f

def z790 : W := mkw 0x079b3e02800080a0 0x20f367c050001014 0xfffffe0f811383e3 0x7fffffc1f022707c

def z791 : W := mkw 0x1f3a74001fdfb2e1 0x23e74e8003fbf65c 0x1a1c30001ffff3e3 0x0343860003fffe7c

def z792 : W := mkw 0xe864c3ffed12b2e0 0x9d0c987ffda2565c 0x380001fffd13f3e3 0x0700003fffa27e7c

def z793 : W := mkw 0xe7d3abebc0000000 0xbcfa757d78000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z794 : W := mkw 0xe7dfbfffe0002200 0xbcfbf7fffc000440 0xefffffffe0007382 0x7dfffffffc000e70

def z795 : W := mkw 0xd77621bc5ba06f02 0xbaeec4378b740de0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z796 : W := mkw 0x5712e16156985850 0x4ae25c2c2ad30b0a 0x7e1ff1f1fefc7c7d 0xefc3fe3e3fdf8f8f

def z797 : W := mkw 0x17bb3c001bc70001 0x22f767800378e000 0xd7fffe001fe38000 0x7affffc003fc7000

def z798 : W := mkw 0x20c58adfa0000000 0x0418b15bf4000000 0xe5e3cfffe0000000 0x7cbc79fffc000000

def z799 : W := mkw 0xe7dfbfffe065efaa 0xbcfbf7fffc0cbdf5 0xffffffffe3ffffff 0xfffffffffc7fffff

def z800 : W := mkw 0xe7d7a9fd60000000 0xbcfaf53fac000000 0x05e3c1f060000000 0x20bc783e0c000000

def z801 : W := mkw 0x4602e16144101040 0x08c05c2c28820208 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z802 : W := mkw 0x173a74001fdf0001 0x22e74e8003fbe000 0x021c30001eec0000 0x0043860003dd8000

def z803 : W := mkw 0x173260001fdf0001 0x22e64c0003fbe000 0x100000001fff8000 0x0200000003fff000

def z804 : W := mkw 0xf7dfbffff2a06f02 0xbefbf7fffe540de0 0xefffffffe2e07f86 0x7dfffffffc5c0ff0

def z805 : W := mkw 0x004080c900000000 0x0008101920000000 0xe5e3c1cf80000000 0x7cbc7839f0000000

def z806 : W := mkw 0x2889de43a45790e8 0x05113bc8748af21d 0x4003ce0180138061 0x080079c03002700c

def z807 : W := mkw 0x3f5ab6cb92cdb2e1 0x27eb56d97259b65c 0x2a1c31cf82ec73e3 0x05438639f05d8e7c

def z808 : W := mkw 0x679bbc4140000000 0xacf3778828000000 0xc7fffe0000000000 0x78ffffc000000000

def z809 : W := mkw 0x182856029fdfb2e1 0x03050ac053fbf65c 0xfa1c3e0f9ffff3e3 0x5f4387c1f3fffe7c

def z810 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xfffffe0e1fff8382 0x7fffffc1c3fff070

def z811 : W := mkw 0x66cbbfebe0000000 0xacd977fd7c000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z812 : W := mkw 0x102c5616bffdfffa 0x42058ac2d7ffbfff 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z813 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0x85ffce0000000000 0x30bff9c000000000

def z814 : W := mkw 0x917401bc1ba06f02 0x122e803783740de0 0xb9fc01fe1fe07f86 0x173f803fc3fc0ff0

def z815 : W := mkw 0x20c188c900000000 0x0418311920000000 0x65e3c1c180000000 0x6cbc783830000000

def z816 : W := mkw 0xe7d3a9e952084810 0xfcfa753d2a410902 0x05e3c1c000000000 0x20bc783800000000

def z817 : W := mkw 0x87df3fbea0000000 0x30fbe7f7d4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z818 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xc1e3ce0f80000000 0x183c79c1f0000000

def z819 : W := mkw 0xe7dbbde940000000 0xbcfb77bd28000000 0xe7fffff1e0000000 0x7cfffffe3c000000

def z820 : W := mkw 0x977401bc1b802200 0x12ee803783700440 0xbffc01fe1fe07382 0x77ff803fc3fc0e70

def z821 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x000000001c13f061 0x0000000003827e0c

def z822 : W := mkw 0x008d1e16a06585a8 0x0011a3c2d40cb0b5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z823 : W := mkw 0xbf95cb7796b2dde2 0x17f2b96ef2d65bbc 0x421fce3182f38c65 0x0843f9c6305e718c

def z824 : W := mkw 0x1fbb7c001fdf3241 0x23f76f8003fbe648 0xd7fffe001ffff000 0x7affffc003fffe00

def z825 : W := mkw 0x20c10a8a80000000 0x0418215150000000 0xc5e3ce0e00000000 0x78bc79c1c0000000

def z826 : W := mkw 0xe7df3fbee0000000 0xbcfbe7f7dc000000 0xc7fffe3e60000000 0x78ffffc7cc000000

def z827 : W := mkw 0x102042029fdf80a1 0x0204084053fbf014 0xf8000e0f9fff83e3 0x5f0001c1f3fff07c

def z828 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x7a003031ff1fffff 0xcf4006063fe3ffff

def z829 : W := mkw 0x079b3c0000450000 0x20f367800008a000 0xc7fffe0001e38000 0x78ffffc0003c7000

def z830 : W := mkw 0x082c5616bf7ffff8 0x41058ac2d7efffff 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z831 : W := mkw 0xe7d7abffe0000000 0xbcfaf57ffc000000 0xe5e3cfffe0000000 0x7cbc79fffc000000

def z832 : W := mkw 0x082040000d12a2a0 0x0104080001a25454 0x100000001d138382 0x0200000003a27070

def z833 : W := mkw 0xc7dfbdfd40000000 0x38fbf7bfa8000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z834 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x87ffc1c000000000 0x70fff83800000000

def z835 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xc3fffe0003ff8000 0x187fffc0007ff000

def z836 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z837 : W := mkw 0xe7dfbffff2080000 0xbcfbf7fffe410000 0xe7ffffffe20c0000 0x7cfffffffc418000

def z838 : W := mkw 0x102040001fb07f42 0x0204080003f60fe8 0x180000001ff07fe7 0x0300000003fe0ffc

def z839 : W := mkw 0x11b95c000dd70001 0x22372b8001bae000 0xc1ffce0001f38000 0x183ff9c0003e7000

def z840 : W := mkw 0x102040001fba6f03 0x0204080003f74de0 0x180000001fe07f86 0x0300000003fc0ff0

def z841 : W := mkw 0xc79b3d2040000000 0xb8f367a408000000 0xc7fffe0000000000 0x78ffffc000000000

def z842 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xd7fffe307fff8c1c 0xfaffffc60ffff183

def z843 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xf7ffffffe21c0000 0x7efffffffc438000

def z844 : W := mkw 0x579bbd6152cd4811 0x6af377ac2a59a902 0xe7fffff1e2ec0c1c 0xfcfffffe3c5d8183

def z845 : W := mkw 0xe7dbbfebe0000000 0xbcfb77fd7c000000 0xc7ffffc1e0000000 0x78fffff83c000000

def z846 : W := mkw 0xe0cfbfffe0000000 0xbc19f7fffc000000 0xe5e3ffffe0000000 0x7cbc7ffffc000000

def z847 : W := mkw 0xe7dfbffff2204d00 0xbcfbf7fffe4409a0 0xffffffffffe07f86 0x7ffffffffffc0ff0

def z848 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x27e3c1f000000000 0x64fc783e00000000

def z849 : W := mkw 0x39fd1e9ea9e7a7a9 0x273fa3d3d53cf4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z850 : W := mkw 0x57bb7c005fdf0011 0x6af76f800bfbe002 0xd7fffe007fff8018 0xfaffffc00ffff003

def z851 : W := mkw 0xc79f3f36e06585a8 0xb8f3e7e6dc0cb0b5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z852 : W := mkw 0xd71e353472ed4d03 0xbae3c6a68e5da9a0 0x021c303062ec0c04 0x004386060c5d8180

def z853 : W := mkw 0x082042028d12b2e0 0x0104084051a2565c 0x98000e0e1d13f3e3 0x130001c1c3a27e7c

def z854 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0x81ffce0e00000000 0x103ff9c1c0000000

def z855 : W := mkw 0x00081602804580a0 0x000102c05008b014 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z856 : W := mkw 0x906441bc1fff6f03 0x120c883783ffede0 0x380001fe1fffff86 0x0700003fc3fffff0

def z857 : W := mkw 0x70abbe43fba06f02 0xae1577c87f740de0 0x5803fe01ffe07f86 0x0b007fc03ffc0ff0

def z858 : W := mkw 0x182040001fb27f42 0x0304080003f64fe8 0x180000001fe07f86 0x0300000003fc0ff0

def z859 : W := mkw 0x4683a96140000000 0x08d0752c28000000 0xe7e3fff1e0000000 0x7cfc7ffe3c000000

def z860 : W := mkw 0xe7dfbfffe0006a02 0xbcfbf7fffc000d40 0xe7ffffffe0007000 0x7cfffffffc000e00

def z861 : W := mkw 0xefdfbfffe020ffe2 0xbdfbf7fffc041ffc 0xefffffffe0007fe7 0x7dfffffffc000ffc

def z862 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x00000000011383e3 0x000000000022707c

def z863 : W := mkw 0x28eddcdd2d773748 0x051dbb9ba5aee6e9 0x07fff1f07eec7c1c 0xa0fffe3e0fdd8f83

def z864 : W := mkw 0x20c99ecba04580a8 0x041933d97408b015 0xe5e3ffcfe01f8079 0xfcbc7ff9fc03f00f

def z865 : W := mkw 0x0000c04116185850 0x4000180822c30b0a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z866 : W := mkw 0xa7d189e900000000 0x14fa313d20000000 0x05e3c1c000000000 0x20bc783800000000

def z867 : W := mkw 0x688bfe43e45f90e1 0xad117fc87c8bf21c 0x4003fe01e01f8061 0x08007fc03c03f00c

def z868 : W := mkw 0xefdfbfffe000b2e0 0xbdfbf7fffc00165c 0xffffffffe113f3e3 0x7ffffffffc227e7c

def z869 : W := mkw 0x102040001fff0509 0x0204080003ffe0a1 0x100000001fff8c1c 0x8200000003fff183

def z870 : W := mkw 0x182040001f92fae2 0x0304080003f25f5c 0x180000001d13f3e3 0x0300000003a27e7c

def z871 : W := mkw 0x079f3e16a02085a8 0x20f3e7c2d40410b5 0xeffffe3fe0000fff 0xfdffffc7fc0001ff

def z872 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xbde3cfce1d03f382 0x77bc79f9c3a07e70

def z873 : W := mkw 0x102c5616bfff85a9 0x02058ac2d7fff0b5 0x901c0e0e1fff8382 0x120381c1c3fff070

def z874 : W := mkw 0xc79f3d3460000000 0xb8f3e7a68c000000 0x07fff03060000000 0x20fffe060c000000

def z875 : W := mkw 0xe79fbf77e0000000 0xbcf3f7eefc000000 0xc7fffe31e0000000 0x78ffffc63c000000

def z876 : W := mkw 0x00ab7c000d5f0001 0x20156f8001abe000 0xd7fffe001fff8000 0x7affffc003fff000

def z877 : W := mkw 0xe7dfbdfd40000000 0xbcfbf7bfa8000000 0xe7fffffe00000000 0x7cffffffc0000000

def z878 : W := mkw 0x562261205fdf4811 0x4ac44c240bfbe902 0x120030307fff8c1c 0x824006060ffff183

def z879 : W := mkw 0x9174009c1ba06f02 0x122e801383740de0 0xbdfc01ce1fe07f86 0x77bf8039c3fc0ff0

def z880 : W := mkw 0x279bbe4380000000 0x24f377c870000000 0xc7fffe0180000000 0x78ffffc030000000

def z881 : W := mkw 0x806401bc09206f02 0x100c803781240de0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z882 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x7fe3f1f1e21c0c7d 0xeffc7e3e3c43818f

def z883 : W := mkw 0x182040001fbafff2 0x4304080003f75ffe 0x180000001fffffff 0x8300000003ffffff

def z884 : W := mkw 0x479bbd6140000000 0x28f377ac28000000 0xc7ffffc000000000 0x78fffff800000000

def z885 : W := mkw 0x66cfbfffe06585a8 0x0cd9f7fffc0cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z886 : W := mkw 0x284482dfa020b7e8 0x0508905bf40416fd 0x280001cf800073e3 0x05000039f0000e7c

def z887 : W := mkw 0x11b95c000dd70001 0x22372b8001bae000 0xd7fffe001fff8000 0x7affffc003fff000

def z888 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0xc5e3cfc000000000 0x78bc79f800000000

def z889 : W := mkw 0xe7dfbffff2085850 0xfcfbf7fffe410b0a 0xefffffffe20c7c7d 0xfdfffffffc418f8f

def z890 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xefffffffe1e38fff 0xfdfffffffc3c71ff

def z891 : W := mkw 0xd71e353452ed4d13 0x7ae3c6a68a5da9a2 0x021c303062ec0c1c 0x804386060c5d8183

def z892 : W := mkw 0xe7dfbfffe0005850 0xfcfbf7fffc000b0a 0xffffffffe21c7c7d 0xfffffffffc438f8f

def z893 : W := mkw 0x66c3abebc0000000 0x0cd8757d78000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z894 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xc3fffe3fe0000000 0x187fffc7fc000000

def z895 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x780000019d13f3e3 0x4f00000033a27e7c

def z896 : W := mkw 0x102040001fffefab 0x0204080003fffdf5 0x180000001fffffff 0x8300000003ffffff

def z897 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xc7ffffce00000000 0x78fffff9c0000000

def z898 : W := mkw 0x688bfe43c45f90f1 0x6d117fc8788bf21e 0x4003fe01e01f8079 0x88007fc03c03f00f

def z899 : W := mkw 0x102040001f980000 0x0204080003f30000 0x100000001ffc0000 0x0200000003ff8000

def z900 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xd5ffce001df38000 0x7abff9c003be7000

def z901 : W := mkw 0x67dbbecbe0000000 0xacfb77d97c000000 0xe7ffffcfe0000000 0x7cfffff9fc000000

def z902 : W := mkw 0xefdfbfffe0003240 0xbdfbf7fffc000648 0xe7ffffffe0007000 0x7cfffffffc000e00

def z903 : W := mkw 0x102040001f9a5851 0x4204080003f34b0a 0x180000001e1c7c7d 0x8300000003c38f8f

def z904 : W := mkw 0x082040001f1afaf0 0x4104080003e35f5e 0x180000001d13f3e3 0x0300000003a27e7c

def z905 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xfde3cfcf81000382 0x7fbc79f9f0200070

def z906 : W := mkw 0xf7dfbfffe0c50001 0xbefbf7fffc18a000 0xe7ffffffe0e00000 0x7cfffffffc1c0000

def z907 : W := mkw 0x00e1c8c90d123240 0x001c391921a24648 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z908 : W := mkw 0xc79f3f36e0000000 0xb8f3e7e6dc000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z909 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x97ffce001fe38000 0x72fff9c003fc7000

def z910 : W := mkw 0x87db3da800000000 0x30fb67b500000000 0xc7ffffc000000000 0x78fffff800000000

def z911 : W := mkw 0x17bb3c0009c70001 0x22f767800138e000 0x85ffce0001e38000 0x30bff9c0003c7000

def z912 : W := mkw 0xe7dfbfffe04580a0 0xbcfbf7fffc08b014 0xffffffffe3ff83e3 0x7ffffffffc7ff07c

def z913 : W := mkw 0x082040000d123240 0x0104080001a24648 0x180000001c107061 0x0300000003820e0c

def z914 : W := mkw 0x082042029f1afaf0 0x4104084053e35f5e 0xfa003e3fff1fffff 0xdf4007c7ffe3ffff

def z915 : W := mkw 0x87df3c9c00000000 0x30fbe79380000000 0xc7fffe0e00000000 0x78ffffc1c0000000

def z916 : W := mkw 0x173a74001fdf0001 0x22e74e8003fbe000 0xd21c3e001fff8000 0x5a4387c003fff000

def z917 : W := mkw 0x102040001fb26f02 0x0204080003f64de0 0x180000001ff3ff86 0x0300000003fe7ff0

def z918 : W := mkw 0xb7d58bff92a04d02 0x16fab17ff25409a0 0xe7ffcfff82e00c04 0x7cfff9fff05c0180

def z919 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x65e3c1c180000000 0x6cbc783830000000

def z920 : W := mkw 0xe7dfbfffe0080010 0xfcfbf7fffc010002 0xe7ffffffe00c0018 0xfcfffffffc018003

def z921 : W := mkw 0x2864c2dfad77b7e8 0x050c985bf5aef6fd 0x380001ffffffffff 0x8700003fffffffff

def z922 : W := mkw 0x60cbbecbe0000000 0xac1977d97c000000 0x45e3ffc1e0000000 0x28bc7ff83c000000

def z923 : W := mkw 0x182c5616bfffb7e9 0x03058ac2d7fff6fd 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z924 : W := mkw 0xd7f3e9e95f9a7a53 0x7afe7d3d2bf34f4a 0x05e3c1c01c007000 0x20bc783803800e00

def z925 : W := mkw 0x479b3c0060000000 0xa8f367800c000000 0xc7fffe0060000000 0x78ffffc00c000000

def z926 : W := mkw 0x019b3c0000000000 0x2033678000000000 0xc1fffe0000000000 0x183fffc000000000

def z927 : W := mkw 0x00891c0000450000 0x001123800008a000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z928 : W := mkw 0x26c18beb80000000 0x04d8317d70000000 0xe7e3cfff80000000 0x7cfc79fff0000000

def z929 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x87fffffe60000000 0x30ffffffcc000000

def z930 : W := mkw 0xf7dfbffff2a84d12 0xfefbf7fffe5509a2 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z931 : W := mkw 0xefdfbfffe000faf0 0xfdfbf7fffc001f5e 0xefffffffe0007fff 0xfdfffffffc000fff

def z932 : W := mkw 0x27dbbecb804580a0 0x24fb77d97008b014 0xffffffcf83ff83e3 0x7ffffff9f07ff07c

def z933 : W := mkw 0x002040000d7785a8 0x0004080001aef0b5 0x180000001fff8fff 0x8300000003fff1ff

def z934 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xfffc31fe1ffc7f86 0x7fff863fc3ff8ff0

def z935 : W := mkw 0xd71e353472e54d0a 0xbae3c6a68e5ca9a1 0x021c303062ec0c1c 0x804386060c5d8183

def z936 : W := mkw 0xe7dfbffff2206f02 0xbcfbf7fffe440de0 0xfffffffffe007f86 0x7fffffffffc00ff0

def z937 : W := mkw 0xe7dbbde940450000 0xbcfb77bd2808a000 0xd7ffffc003ff8000 0x7afffff8007ff000

def z938 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x7a003031ffff8c7d 0xcf4006063ffff18f

def z939 : W := mkw 0x17bb7c001fdf2201 0x22f76f8003fbe440 0xdffffe001ffff382 0x7bffffc003fffe70

def z940 : W := mkw 0xa7dfbfff80000000 0x34fbf7fff0000000 0xe7ffffff80000000 0x7cfffffff0000000

def z941 : W := mkw 0x182040001fffffe3 0x0304080003fffffc 0x180000001fffffe7 0x0300000003fffffc

def z942 : W := mkw 0xe6c7abffe0000000 0x9cd8f57ffc000000 0xe7e3ffffe0000000 0x7cfc7ffffc000000

def z943 : W := mkw 0x27dbbcc900000000 0x24fb779920000000 0xc7ffffc000000000 0x78fffff800000000

def z944 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xfffffffffe1c7c7d 0xffffffffffc38f8f

def z945 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xfffc0ffe1ff3ff86 0x7fff81ffc3fe7ff0

def z946 : W := mkw 0x288bfe43a45f90e9 0x25117fc8748bf21d 0x4003fe01e01f8079 0x88007fc03c03f00f

def z947 : W := mkw 0xc79f3d3460650508 0xb8f3e7a68c0ca0a1 0xd7fffe3063ff8c1c 0xfaffffc60c7ff183

def z948 : W := mkw 0xe7dfbfffe00080a0 0xbcfbf7fffc001014 0xe7ffffffe0138061 0x7cfffffffc02700c

def z949 : W := mkw 0xd77621bc5ba86f12 0x5aeec4378b750de2 0xfffc31fffffc7fff 0xffff863fffff8fff

def z950 : W := mkw 0xe7d7a9fd40200500 0xbcfaf53fa80400a0 0xbfffc1fe03e00f86 0x77fff83fc07c01f0

def z951 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xc7fffe001de38000 0x78ffffc003bc7000

def z952 : W := mkw 0x00a148000d120000 0x0014290001a24000 0xd7ffce001ff38000 0x7afff9c003fe7000

def z953 : W := mkw 0x688bfe43e45790e8 0xad117fc87c8af21d 0x4003fe01e01f8079 0x88007fc03c03f00f

def z954 : W := mkw 0x2fdbbecb8000b2e0 0x25fb77d97000165c 0xefffffcf800073e3 0x7dfffff9f0000e7c

def z955 : W := mkw 0x002040000d121040 0x0004080001a24208 0x180000001d13f061 0x0300000003a27e0c

def z956 : W := mkw 0xe7dfbfffe0650508 0xbcfbf7fffc0ca0a1 0xffffffffe2fc0c7d 0xfffffffffc5f818f

def z957 : W := mkw 0xe7dfbfffe0450000 0xbcfbf7fffc08a000 0xe7ffffffe2ec0000 0x7cfffffffc5d8000

def z958 : W := mkw 0xa7df3e9ea0000000 0xb4fbe7d3d4000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z959 : W := mkw 0x6ee32baadb0aeab0 0x4ddc65755b615d56 0x83e03e3e630f8f9e 0x907c07c7cc61f1f3

def z960 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x45e3f1c1e0000000 0x28bc7e383c000000

def z961 : W := mkw 0xe7dfbfffe00080a8 0xbcfbf7fffc001015 0xe7ffffffe0000079 0xfcfffffffc00000f

def z962 : W := mkw 0xc752a1e940000000 0x18ea543d28000000 0x05e3c1c000000000 0x20bc783800000000

def z963 : W := mkw 0x079b7c00165d0000 0x20f36f8002cba000 0xd7fffe001fff8000 0x7affffc003fff000

def z964 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0xfe03f1ffff1c7fff 0xffc07e3fffe38fff

def z965 : W := mkw 0x479bfd61565d5850 0x68f37fac2acbab0a 0xfffffff1fffffc7d 0xfffffffe3fffff8f

def z966 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xc21c3e3fe3ff8fff 0x984387c7fc7ff1ff

def z967 : W := mkw 0xe7d3abebc0000000 0xbcfa757d78000000 0x45e3cfc180000000 0x28bc79f830000000

def z968 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xade3cfcf9d03f3e3 0x35bc79f9f3a07e7c

def z969 : W := mkw 0xe7dbbfebe04580a8 0xbcfb77fd7c08b015 0x45e3ffc1e01f8079 0xa8bc7ff83c03f00f

def z970 : W := mkw 0x17bb7c001fdf4801 0x22f76f8003fbe900 0xdffffe001ffffc04 0x7bffffc003ffff80

def z971 : W := mkw 0x0793280000000000 0x20f2650000000000 0x47e3f00000000000 0x68fc7e0000000000

def z972 : W := mkw 0x4002e16156185850 0x48005c2c2ac30b0a 0x7803f1f1fe1c7c7d 0x8f007e3e3fc38f8f

def z973 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe0100061 0x7ffffffffc02000c

def z974 : W := mkw 0xefdfbfffe065b7e8 0xbdfbf7fffc0cb6fd 0xffffffffe3ffffff 0xfffffffffc7fffff

def z975 : W := mkw 0x00810a02800080a0 0x0010214050001014 0xfde3ce0f811383e3 0x7fbc79c1f022707c

def z976 : W := mkw 0xe7d7abffe02085a8 0xbcfaf57ffc0410b5 0x2de3c1ffe0000fff 0xa5bc783ffc0001ff

def z977 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xfffffffffc007000 0x7fffffffff800e00

def z978 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0xfe1ff1f1fffc7c7d 0xffc3fe3e3fff8f8f

def z979 : W := mkw 0x102854001fdf0001 0x02050a8003fbe000 0x121c30001fff8000 0x0243860003fff000

def z980 : W := mkw 0xc04483ffe020fffa 0x5808907ffc041fff 0x280001ffe0007fff 0x8500003ffc000fff

def z981 : W := mkw 0x082040000d32b7e0 0x0104080001a656fc 0x180000001ff3ffe7 0x0300000003fe7ffc

def z982 : W := mkw 0xf7d3a9e952880001 0xbefa753d2a510000 0x05e3c1c000000000 0x20bc783800000000

def z983 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xf7ffffffe3ff8382 0x7efffffffc7ff070

def z984 : W := mkw 0x179b3c0012800000 0x22f3678002500000 0xc7fffe0002e00000 0x78ffffc0005c0000

def z985 : W := mkw 0xa84482df8020b7e2 0x1508905bf00416fc 0x280001cf800073e3 0x05000039f0000e7c

def z986 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x000000001eec0000 0x0000000003dd8000

def z987 : W := mkw 0x608bfe43e45d90f8 0xec117fc87c8bb21f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z988 : W := mkw 0x60cbbecbe0000000 0xac1977d97c000000 0xc1e3fe0fe0000000 0x183c7fc1fc000000

def z989 : W := mkw 0x0602612016184800 0x00c04c2402c30900 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z990 : W := mkw 0xf7dfbffff2804802 0xbefbf7fffe500900 0xe7ffffffe0000000 0x7cfffffffc000000

def z991 : W := mkw 0x102c54143fff0509 0x02058a8287ffe0a1 0x121c30307fff8c1c 0x824386060ffff183

def z992 : W := mkw 0xf7dfbffff2a04d02 0xbefbf7fffe5409a0 0xfffffffffee07c04 0x7fffffffffdc0f80

def z993 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x000000001d03f382 0x0000000003a07e70

def z994 : W := mkw 0x66c3a9e940000000 0x0cd8753d28000000 0x05e3c1c000000000 0x20bc783800000000

def z995 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x2e03f1f1fe0c7c7d 0xa5c07e3e3fc18f8f

def z996 : W := mkw 0x27d3aacb80000000 0x24fa755970000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z997 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xffe3cfff9f13ffe7 0x7ffc79fff3e27ffc

def z998 : W := mkw 0xa1dd9edfa06585a8 0xb43bb3dbf40cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z999 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe2000c04 0x7ffffffffc400180

def z1000 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x97fc01ce1fe07382 0x72ff8039c3fc0e70

def z1001 : W := mkw 0x97bb7d201fdf4803 0x32f76fa403fbe900 0xd7fffe001fff8000 0x7affffc003fff000

def z1002 : W := mkw 0x102040001fdf4801 0x0204080003fbe900 0x180000001ffffc04 0x0300000003ffff80

def z1003 : W := mkw 0x91fd1e9ea9e7a7ab 0x323fa3d3d53cf4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z1004 : W := mkw 0x6ec3abebc000faf0 0x4dd8757d78001f5e 0xefe3ffffe0007fff 0xfdfc7ffffc000fff

def z1005 : W := mkw 0x17b76a16bfba85a9 0x22f6ed42d7f750b5 0x2de3c03ffc000fff 0xa5bc7807ff8001ff

def z1006 : W := mkw 0x113854001fdf0001 0x22270a8003fbe000 0x101c00001fff8000 0x0203800003fff000

def z1007 : W := mkw 0x97df3dbc12ed4d03 0x32fbe7b7825da9a0 0xe7fffffe02ec0c04 0x7cffffffc05d8180

def z1008 : W := mkw 0xd176e0dd4db83752 0x5a2edc1ba9b706ea 0xc1fff00fe1fc03fb 0x983ffe01fc3f807f

def z1009 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x921c00001fff8000 0x5243800003fff000

def z1010 : W := mkw 0x9774009c1ba02702 0x12ee8013837404e0 0xbffc01ce1fe07382 0x77ff8039c3fc0e70

def z1011 : W := mkw 0x4712a16140000000 0x08e2542c28000000 0xe7fff1f1e0000000 0x7cfffe3e3c000000

def z1012 : W := mkw 0xe7dfbdfd60000000 0xbcfbf7bfac000000 0xa7fff1fe60000000 0x74fffe3fcc000000

def z1013 : W := mkw 0xa7db3c8800000000 0xb4fb679100000000 0xc7fffe0000000000 0x78ffffc000000000

def z1014 : W := mkw 0x4000c16156185850 0x4800182c2ac30b0a 0x280001f1fc007c7d 0x8500003e3f800f8f

def z1015 : W := mkw 0x4712e16156185850 0x48e25c2c2ac30b0a 0xfffff1f1fe1c7c7d 0xfffffe3e3fc38f8f

def z1016 : W := mkw 0xe7dfbfffe0200500 0xbcfbf7fffc0400a0 0xffffffffe3fc0fff 0xfffffffffc7f81ff

def z1017 : W := mkw 0x5712e16156985851 0x6ae25c2c2ad30b0a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1018 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xfffffe019fff8061 0x7fffffc033fff00c

def z1019 : W := mkw 0x10a95c001fdf0001 0x02152b8003fbe000 0xd7fffe001fff8000 0x7affffc003fff000

def z1020 : W := mkw 0x20e18acb8900a2a0 0x041c315971201454 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z1021 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x65e3ffffe0000000 0x2cbc7ffffc000000

def z1022 : W := mkw 0x20c18acb80000000 0x0418315970000000 0x85e3cfce00000000 0x30bc79f9c0000000

def z1023 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xa7ffcffe00000000 0x74fff9ffc0000000

def z1024 : W := mkw 0x079b3e02a0000000 0x20f367c054000000 0xc7fffe01e0000000 0x78ffffc03c000000

def z1025 : W := mkw 0xa7df3e9ea06585a8 0xb4fbe7d3d40cb0b5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1026 : W := mkw 0x179b3c0012880001 0x22f3678002510000 0xc7fffe0000000000 0x78ffffc000000000

def z1027 : W := mkw 0x57bb7c007fdf0001 0xaaf76f800ffbe000 0xd7fffe007fff8000 0x7affffc00ffff000

def z1028 : W := mkw 0x57bb7d205fdf4811 0x6af76fa40bfbe902 0xfffffff07ffffc1c 0xfffffffe0fffff83

def z1029 : W := mkw 0x102040001fffddf9 0x4204080003fffbbf 0x180000001fffffff 0x8300000003ffffff

def z1030 : W := mkw 0x002040000d570000 0x0004080001aae000 0x100000001fff8000 0x0200000003fff000

def z1031 : W := mkw 0x87d729bc00000000 0x30fae53780000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z1032 : W := mkw 0x082040000d77b7e8 0x0104080001aef6fd 0x180000001df3f3e3 0x0300000003be7e7c

def z1033 : W := mkw 0x20c99ecb80450000 0x041933d97008a000 0xf7ffffcf83ff8000 0x7efffff9f07ff000

def z1034 : W := mkw 0xe7d7abffe0000000 0xbcfaf57ffc000000 0x05e3c1ce00000000 0x20bc7839c0000000

def z1035 : W := mkw 0xa7dfbedfa0000000 0xb4fbf7dbf4000000 0xe7ffffcf80000000 0x7cfffff9f0000000

def z1036 : W := mkw 0x079b3c0000450000 0x20f367800008a000 0xc7fffe0002ec0000 0x78ffffc0005d8000

def z1037 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0x85ffcfce01e38382 0x30bff9f9c03c7070

def z1038 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xfde3cfcf9c007000 0x7fbc79f9f3800e00

def z1039 : W := mkw 0x082040000d57b2e0 0x0104080001aaf65c 0x180000001ffff3e3 0x0300000003fffe7c

def z1040 : W := mkw 0xe7dfbfffe04580a8 0xbcfbf7fffc08b015 0xffffffffe11f83fb 0xfffffffffc23f07f

def z1041 : W := mkw 0x60c3aacbc0000000 0xac18755978000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z1042 : W := mkw 0x11b95c001fdf0001 0x22372b8003fbe000 0xd5ffce001fff8000 0x7abff9c003fff000

def z1043 : W := mkw 0xd77401bc7ba06f02 0x9aee80378f740de0 0xbffc01fe7fe07f86 0x77ff803fcffc0ff0

def z1044 : W := mkw 0xf7dfbffff2e5cdaa 0xbefbf7fffe5cb9b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1045 : W := mkw 0x28c18acb8000b2e0 0x051831597000165c 0x2de3c1cf800073e3 0x25bc7839f0000e7c

def z1046 : W := mkw 0x28c188c900003240 0x0518311920000648 0x05e3c1c000007000 0x20bc783800000e00

def z1047 : W := mkw 0x4002e16144185850 0x48005c2c28830b0a 0x7c03f1f1fc1c7c7d 0xef807e3e3f838f8f

def z1048 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xe7ffffffe2ff8c7d 0xfcfffffffc5ff18f

def z1049 : W := mkw 0xe7dfbfffe0470001 0xbcfbf7fffc08e000 0xe7ffffffe0038000 0x7cfffffffc007000

def z1050 : W := mkw 0xa1dd9edfa0000000 0xb43bb3dbf4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1051 : W := mkw 0x27dfbedfa06585a8 0x24fbf7dbf40cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1052 : W := mkw 0x2860c0c90d12b2e0 0x050c181921a2565c 0x180001c01d13f3e3 0x0300003803a27e7c

def z1053 : W := mkw 0x879f3c1420000000 0xb0f3e78284000000 0xc7fffe0000000000 0x78ffffc000000000

def z1054 : W := mkw 0x17b368001f9a0000 0x02f66d0003f34000 0xd7fffe001fff8000 0x7affffc003fff000

def z1055 : W := mkw 0x08285602ad57b2e8 0x01050ac055aaf65d 0x58003e01fd1ff3fb 0x8b0007c03fa3fe7f

def z1056 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x95ffce001fff8000 0x32bff9c003fff000

def z1057 : W := mkw 0x917401bc09a06f02 0x122e803781340de0 0xbdfc01fe1de07f86 0x77bf803fc3bc0ff0

def z1058 : W := mkw 0xe7dfbfffe0450000 0xbcfbf7fffc08a000 0xe7ffffffe01f8000 0x7cfffffffc03f000

def z1059 : W := mkw 0x11bb7c000ddf0001 0x22376f8001bbe000 0x81ffce0001e38000 0x103ff9c0003c7000

def z1060 : W := mkw 0x07bb7c000d570000 0x20f76f8001aae000 0xd7fffe001fff8000 0x7affffc003fff000

def z1061 : W := mkw 0xd064c1fd5fb87f52 0x5a0c983fabf70fea 0x380001fffffc7fff 0x8700003fffff8fff

def z1062 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xfffffe301fff8c04 0x7fffffc603fff180

def z1063 : W := mkw 0x977401bc09a02702 0x12ee8037813404e0 0xbffc01fe1de07382 0x77ff803fc3bc0e70

def z1064 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0x07fff00000000000 0x20fffe0000000000

def z1065 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0xd7fffe0003e00000 0x7affffc0007c0000

def z1066 : W := mkw 0x102854001fdf0001 0x02050a8003fbe000 0x50003e001fff8000 0x0a0007c003fff000

def z1067 : W := mkw 0x002040001f187a50 0x4004080003e30f4a 0x180000001f1c7fff 0x8300000003e38fff

def z1068 : W := mkw 0xe7dbbde940000000 0xbcfb77bd28000000 0x45e3ffc000000000 0x28bc7ff800000000

def z1069 : W := mkw 0x17bb7c001f920000 0x22f76f8003f24000 0xd7fffe001ff38000 0x7affffc003fe7000

def z1070 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xf7ffffffe3e00000 0x7efffffffc7c0000

def z1071 : W := mkw 0x11bb3c0009c70001 0x223767800138e000 0xc1fffe0001e38000 0x183fffc0003c7000

def z1072 : W := mkw 0xa84483ffa020ffea 0x1508907ff4041ffd 0x280001ffe0007fff 0x8500003ffc000fff

def z1073 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x9dfc01ce1fe07f86 0x33bf8039c3fc0ff0

def z1074 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x25e3c1f1e0000000 0x24bc783e3c000000

def z1075 : W := mkw 0xefdfbfffe00280a0 0xbdfbf7fffc005014 0xe7ffffffe0038000 0x7cfffffffc007000

def z1076 : W := mkw 0x17bb7c001fdf4811 0x62f76f8003fbe902 0xd7fffe001fff8c1c 0xfaffffc003fff183

def z1077 : W := mkw 0x21d99ecb80000000 0x243b33d970000000 0xe5ffcfcf80000000 0x7cbff9f9f0000000

def z1078 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xbffc31fe7fec7f9e 0xf7ff863fcffd8ff3

def z1079 : W := mkw 0xe7dfbfffe0450008 0xbcfbf7fffc08a001 0xe7ffffffe00c0018 0xfcfffffffc018003

def z1080 : W := mkw 0xe7dfbffff265cda8 0xbcfbf7fffe4cb9b5 0xffffffffffffffff 0xffffffffffffffff

def z1081 : W := mkw 0x079b3c00004d0001 0x20f367800009a000 0xc7fffe00000c0000 0x78ffffc000018000

def z1082 : W := mkw 0x173260001f9a0001 0x22e64c0003f34000 0x000000001c000000 0x0000000003800000

def z1083 : W := mkw 0xe04483ffe02085a8 0x9c08907ffc0410b5 0x200001ffe0000382 0x0400003ffc000070

def z1084 : W := mkw 0x082040000d5fb2e1 0x0104080001abf65c 0x180000001d1ff3e3 0x0300000003a3fe7c

def z1085 : W := mkw 0x079bbc4100000000 0x20f3778820000000 0xe7ffffc180000000 0x7cfffff830000000

def z1086 : W := mkw 0x0820c0410d12b2e0 0x0104180821a2565c 0x380001c19d13f3e3 0x0700003833a27e7c

def z1087 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0xe7fffe31e0000000 0x7cffffc63c000000

def z1088 : W := mkw 0x082040000d1290e0 0x0104080001a2521c 0x100000001d138061 0x0200000003a2700c

def z1089 : W := mkw 0x102040001fdf2201 0x0204080003fbe440 0x180000001ffff382 0x0300000003fffe70

def z1090 : W := mkw 0xf7dfbffff2e54d0a 0xbefbf7fffe5ca9a1 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z1091 : W := mkw 0x082c5616ad12b2e0 0x01058ac2d5a2565c 0xfa1c3e3ffd13f3e3 0x5f4387c7ffa27e7c

def z1092 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0x27fff1ffe0000000 0x24fffe3ffc000000

def z1093 : W := mkw 0x87df3dbc00206f02 0x30fbe7b780040de0 0xeffffffe00007f86 0x7dffffffc0000ff0

def z1094 : W := mkw 0x4793a96140000000 0x28f2752c28000000 0x67e3f1f1e0000000 0x6cfc7e3e3c000000

def z1095 : W := mkw 0xc793292040000000 0xb8f2652408000000 0x05e3c00000000000 0x20bc780000000000

def z1096 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x000000001de38000 0x0000000003bc7000

def z1097 : W := mkw 0xf7dbbde952cd0001 0xbefb77bd2a59a000 0x07fff1c002ec0000 0x20fffe38005d8000

def z1098 : W := mkw 0xe7d3abebe0000000 0xbcfa757d7c000000 0x05e3c1c1e0000000 0x20bc78383c000000

def z1099 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0xd0000e001fff8000 0x5a0001c003fff000

def z1100 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xc5fffe001dff8000 0x38bfffc003bff000

def z1101 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x000000001c1f8000 0x000000000383f000

def z1102 : W := mkw 0x60cbbecbe04580a8 0xac1977d97c08b015 0xfde3ffcfe11f83fb 0xffbc7ff9fc23f07f

def z1103 : W := mkw 0x571e353472ed4d19 0x6ae3c6a68e5da9a3 0x021c303062ec0c1c 0x804386060c5d8183

def z1104 : W := mkw 0x177001a81b806a00 0x02ee003503700d40 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1105 : W := mkw 0x875481fd00000000 0x10ea903fa0000000 0xe7ffc1ff80000000 0x7cfff83ff0000000

def z1106 : W := mkw 0x977401bc3ba06f0a 0x12ee803787740de1 0xbffc01fe7fe07f9e 0xf7ff803fcffc0ff3

def z1107 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x87fffe001fef8000 0x30ffffc003fdf000

def z1108 : W := mkw 0x182040001f92b2e0 0x0304080003f2565c 0x180000001ff3f3e3 0x0300000003fe7e7c

def z1109 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xffffffffe1f383e3 0x7ffffffffc3e707c

def z1110 : W := mkw 0x182c5616bff7ffea 0x03058ac2d7fefffd 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z1111 : W := mkw 0x4602a16152004800 0x08c0542c2a400900 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1112 : W := mkw 0x11bb7c000ddf0001 0x22376f8001bbe000 0xd5fffe001dff8000 0x7abfffc003bff000

def z1113 : W := mkw 0x4642a1e940000000 0x08c8543d28000000 0xe7e3f1ffe0000000 0x7cfc7e3ffc000000

def z1114 : W := mkw 0x886441bc0d32ffe2 0x110c883781a65ffc 0x380001fe1d13ffe7 0x0700003fc3a27ffc

def z1115 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xfde3ffcffd1ff3fb 0xffbc7ff9ffa3fe7f

def z1116 : W := mkw 0x079b3c00006585a8 0x20f36780000cb0b5 0xdffffe0003ff8fff 0xfbffffc0007ff1ff

def z1117 : W := mkw 0x177000881ba06f02 0x02ee001103740de0 0xbffc01ce1fe07f86 0x77ff8039c3fc0ff0

def z1118 : W := mkw 0x2820c2438d12b2e0 0x0504184871a2565c 0x180000019d13f3e3 0x0300000033a27e7c

def z1119 : W := mkw 0x10285602bfdf80a9 0x02050ac057fbf015 0x50003e01ffff8079 0x8a0007c03ffff00f

def z1120 : W := mkw 0xe7d7a9fd40000000 0xbcfaf53fa8000000 0x85ffc1ce00000000 0x30bff839c0000000

def z1121 : W := mkw 0xefd3abebc000b2e0 0xbdfa757d7800165c 0x2de3c1cf800073e3 0x25bc7839f0000e7c

def z1122 : W := mkw 0x002c5616ad7785a8 0x00058ac2d5aef0b5 0xfa1c3e3fffff8fff 0xdf4387c7fffff1ff

def z1123 : W := mkw 0x66c3abebd2084810 0x4cd8757d7a410902 0xe7e3ffffe20c0c1c 0xfcfc7ffffc418183

def z1124 : W := mkw 0x977401bc1ba86f12 0x52ee803783750de2 0xbffc01fe1fec7f9e 0xf7ff803fc3fd8ff3

def z1125 : W := mkw 0x10244216bfff85a9 0x02048842d7fff0b5 0x3800003fffff8fff 0x87000007fffff1ff

def z1126 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xc5ffffcfe0000000 0x38bffff9fc000000

def z1127 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x3c0001c01d13f3e3 0x6780003803a27e7c

def z1128 : W := mkw 0x102040001fff85a9 0x0204080003fff0b5 0x100000001fff8382 0x0200000003fff070

def z1129 : W := mkw 0x60c18bebc0000000 0x0c18317d78000000 0xe5e3cfffe0000000 0x7cbc79fffc000000

def z1130 : W := mkw 0xe7d7a9fd40000000 0xbcfaf53fa8000000 0x25e3c1fe00000000 0x24bc783fc0000000

def z1131 : W := mkw 0xe7dfbfffe0200500 0xbcfbf7fffc0400a0 0xefffffffe0000f86 0x7dfffffffc0001f0

def z1132 : W := mkw 0x977621bc1ba86f02 0x12eec43783750de0 0xbffc31fe1fec7f86 0x77ff863fc3fd8ff0

def z1133 : W := mkw 0x68e1cacbcd12b2f0 0x4d1c395979a2565e 0xfde3cfcffd13f3fb 0xffbc79f9ffa27e7f

def z1134 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xe7fffffffc007000 0x7cffffffff800e00

def z1135 : W := mkw 0x102040001f9a0001 0x0204080003f34000 0x100000001fe00000 0x0200000003fc0000

def z1136 : W := mkw 0x102a74001fdf0001 0x22054e8003fbe000 0x100030001fff8000 0x0200060003fff000

def z1137 : W := mkw 0x082042028d12b2e0 0x0104084051a2565c 0x3800000f9d13f3e3 0x07000001f3a27e7c

def z1138 : W := mkw 0x102040001f9a0001 0x0204080003f34000 0x100000001e1c0000 0x0200000003c38000

def z1139 : W := mkw 0xa7d58bff802085a0 0x14fab17ff00410b4 0xffffcfff83f38fe7 0x7ffff9fff07e71fc

def z1140 : W := mkw 0xe7dbbde940000000 0xbcfb77bd28000000 0x07fff1c000000000 0x20fffe3800000000

def z1141 : W := mkw 0x3860c2cb9fdfb2e1 0x070c185973fbf65c 0x380001cf9ffff3e3 0x07000039f3fffe7c

def z1142 : W := mkw 0x679bbe43e0000000 0xacf377c87c000000 0x45e3fe01e0000000 0x28bc7fc03c000000

def z1143 : W := mkw 0x4002e04144181050 0x48005c082883020a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1144 : W := mkw 0xe7dfbfffe0650508 0xbcfbf7fffc0ca0a1 0xe7ffffffe0e00000 0x7cfffffffc1c0000

def z1145 : W := mkw 0xe7dfbfffe065ddf8 0xfcfbf7fffc0cbbbf 0xffffffffe3ffffff 0xfffffffffc7fffff

def z1146 : W := mkw 0x4820c1614d12faf0 0x4904182c29a25f5e 0x380001f1fd13ffff 0x8700003e3fa27fff

def z1147 : W := mkw 0xe7dfbfffe0001050 0xfcfbf7fffc00020a 0xe7ffffffe0000079 0xfcfffffffc00000f

def z1148 : W := mkw 0x0791080000000000 0x00f2210000000000 0xc7ffce0000000000 0x78fff9c000000000

def z1149 : W := mkw 0x082854000d57b2e0 0x01050a8001aaf65c 0xda1c3e001ffff3e3 0x5b4387c003fffe7c

def z1150 : W := mkw 0xc712e16156185850 0xf8e25c2c2ac30b0a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1151 : W := mkw 0x079b3c0000450000 0x20f367800008a000 0xc7fffe00001f8000 0x78ffffc00003f000

def z1152 : W := mkw 0x17bb7c001fdf6a03 0x22f76f8003fbed40 0xd7fffe001ffff000 0x7affffc003fffe00

def z1153 : W := mkw 0x60cfbedfe06585a8 0xac19f7dbfc0cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1154 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0x45e3fe0000000000 0x28bc7fc000000000

def z1155 : W := mkw 0xd712e16156985852 0x5ae25c2c2ad30b0a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1156 : W := mkw 0x102c54141fff6f03 0x02058a8283ffede0 0xfa1c3e3e1fffff86 0x5f4387c7c3fffff0

def z1157 : W := mkw 0xe7dfbffff2004800 0xbcfbf7fffe400900 0xe7ffffffe2000c04 0x7cfffffffc400180

def z1158 : W := mkw 0x079f3c1420650508 0x20f3e782840ca0a1 0xc7fffe3062ec0c1c 0xf8ffffc60c5d8183

def z1159 : W := mkw 0xe7d3a9e940006a02 0xbcfa753d28000d40 0x05e3c1c000007000 0x20bc783800000e00

def z1160 : W := mkw 0x079b3d2000000000 0x20f367a400000000 0xe7fffff000000000 0x7cfffffe00000000

def z1161 : W := mkw 0xa7df3e9ea06585a8 0xb4fbe7d3d40cb0b5 0xd7fffe0e03ff8382 0x7affffc1c07ff070

def z1162 : W := mkw 0xe0c58bffe02085a8 0x9c18b17ffc0410b5 0xfde3cfffe1138fff 0xffbc79fffc2271ff

def z1163 : W := mkw 0xe7d3a9e952084810 0xfcfa753d2a410902 0x07e3f1f0620c0c1c 0xa0fc7e3e0c418183

def z1164 : W := mkw 0x286cd6dfad77b7e8 0x050d9adbf5aef6fd 0xfa1c3fffffffffff 0xdf4387ffffffffff

def z1165 : W := mkw 0xe84483ffe020ffe2 0x9d08907ffc041ffc 0x280001ffe0007fe7 0x0500003ffc000ffc

def z1166 : W := mkw 0xe7dfbedfe0000000 0xbcfbf7dbfc000000 0xc7fffe0fe0000000 0x78ffffc1fc000000

def z1167 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xdffffe001fff8c7d 0xfbffffc003fff18f

def z1168 : W := mkw 0x182040001fffb7e9 0x0304080003fff6fd 0x180000001fffffff 0x8300000003ffffff

def z1169 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xf7ffffffe1138000 0x7efffffffc227000

def z1170 : W := mkw 0xe7dbbfebc0000000 0xbcfb77fd78000000 0xe7ffffcf80000000 0x7cfffff9f0000000

def z1171 : W := mkw 0xe7dfbdfd60000000 0xbcfbf7bfac000000 0x05ffc1c000000000 0x20bff83800000000

def z1172 : W := mkw 0x11b148000d920000 0x0236290001b24000 0xd5ffce001df38000 0x7abff9c003be7000

def z1173 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0xd7fffe0001138000 0x7affffc000227000

def z1174 : W := mkw 0x0060c2cb8d10b2e0 0x000c185971a2165c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z1175 : W := mkw 0x00040216802085a0 0x00008042d00410b4 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z1176 : W := mkw 0xd73661345fb87f52 0x5ae6cc268bf70fea 0x1a1c30307ffc7fff 0x834386060fff8fff

def z1177 : W := mkw 0x28e1cacbad12b2e8 0x051c395975a2565d 0xfde3cfcffd13f3fb 0xffbc79f9ffa27e7f

def z1178 : W := mkw 0x479b3d2052084810 0x68f367a40a410902 0xc7fffe30620c0c1c 0xf8ffffc60c418183

def z1179 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0xd7fffe00021c0000 0x7affffc000438000

def z1180 : W := mkw 0x102040001fdf80a9 0x0204080003fbf015 0x100000001fff8079 0x8200000003fff00f

def z1181 : W := mkw 0xe7dfbfffe0204d02 0xbcfbf7fffc0409a0 0xe7ffffffe0000c04 0x7cfffffffc000180

def z1182 : W := mkw 0x002040000d1280a0 0x0004080001a25014 0x180000001d1383e3 0x0300000003a2707c

def z1183 : W := mkw 0xf7dfbffff2cd4811 0xfefbf7fffe59a902 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z1184 : W := mkw 0xe7dbbde960000000 0xbcfb77bd2c000000 0x05e3f1c060000000 0x20bc7e380c000000

def z1185 : W := mkw 0x17bb3c001bcf0001 0x22f767800379e000 0xc7fffe0003ef8000 0x78ffffc0007df000

def z1186 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xf5e3cfcf81138000 0x7ebc79f9f0227000

def z1187 : W := mkw 0x082040000d32b7e8 0x0104080001a656fd 0x180000001d13ffff 0x8300000003a27fff

def z1188 : W := mkw 0x082040000d123240 0x0104080001a24648 0x180000001d007382 0x0300000003a00e70

def z1189 : W := mkw 0x079b3e02a04580a8 0x20f367c05408b015 0xc7fffe01e01f8079 0xf8ffffc03c03f00f

def z1190 : W := mkw 0xd77401bc5ba06f12 0x5aee80378b740de2 0xbffc01fe7fe07f9e 0xf7ff803fcffc0ff3

def z1191 : W := mkw 0x102c5616bfffddf9 0x42058ac2d7fffbbf 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z1192 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0x6de3cfcf9c13f3e3 0x2dbc79f9f3827e7c

def z1193 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x180000001f1fffff 0x8300000003e3ffff

def z1194 : W := mkw 0xe84483ffe020b7e8 0x9d08907ffc0416fd 0x280001ffe0007fff 0x8500003ffc000fff

def z1195 : W := mkw 0x102c5616bfffefab 0x02058ac2d7fffdf5 0xfa1c3e3fffffffff 0xdf4387c7ffffffff

def z1196 : W := mkw 0xe7dbbfebe0000000 0xbcfb77fd7c000000 0x05e3cfc000000000 0x20bc79f800000000

def z1197 : W := mkw 0xe7dfbfffe0005850 0xfcfbf7fffc000b0a 0xe7ffffffe0007000 0x7cfffffffc000e00

def z1198 : W := mkw 0x17bb7c001fdf5851 0x62f76f8003fbeb0a 0xd7fffe001ffff000 0x7affffc003fffe00

def z1199 : W := mkw 0x102040001f920000 0x0204080003f24000 0x100000001ff38000 0x0200000003fe7000

def z1200 : W := mkw 0x17bb3c0009c70001 0x22f767800138e000 0xd7fffe0003ff8000 0x7affffc0007ff000

def z1201 : W := mkw 0xefd3a9e940003240 0xbdfa753d28000648 0x05e3c1c000007000 0x20bc783800000e00

def z1202 : W := mkw 0xd77621bc5ba06f02 0x1aeec4378b740de0 0xbffc31fe7fe07f86 0x77ff863fcffc0ff0

def z1203 : W := mkw 0x479bbd6140450000 0x28f377ac2808a000 0xfffffff1e3ff8c7d 0xfffffffe3c7ff18f

def z1204 : W := mkw 0x102040001fdf4811 0x4204080003fbe902 0x100000001fff8c1c 0x8200000003fff183

def z1205 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe5ffcfcf80000000 0x7cbff9f9f0000000

def z1206 : W := mkw 0xe7dfbfffe0450000 0xbcfbf7fffc08a000 0xffffffffe3ff8c7d 0xfffffffffc7ff18f

def z1207 : W := mkw 0xa1d58adf80000000 0x143ab15bf0000000 0xe5ffcfcf80000000 0x7cbff9f9f0000000

def z1208 : W := mkw 0x28c18acb800280a0 0x0518315970005014 0xe5e3cfcf80038000 0x7cbc79f9f0007000

def z1209 : W := mkw 0x0793280000000000 0x20f2650000000000 0x87ffc00000000000 0x70fff80000000000

def z1210 : W := mkw 0xc756a1fd40207f52 0x58ead43fa8040fea 0xeffff1ffe0007fff 0xfdfffe3ffc000fff

def z1211 : W := mkw 0x1774009c1ba02700 0x02ee8013837404e0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1212 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xfffc01ff9ff07fe7 0x7fff803ff3fe0ffc

def z1213 : W := mkw 0x20c58adf80000000 0x0418b15bf0000000 0xe7ffcfff80000000 0x7cfff9fff0000000

def z1214 : W := mkw 0x11b95c000dd70001 0x22372b8001bae000 0x85ffce001de38000 0x30bff9c003bc7000

def z1215 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0xa5e3c1ce00000000 0x74bc7839c0000000

def z1216 : W := mkw 0x20c18acb80001040 0x0418315970000208 0xede3cfcf80007061 0x7dbc79f9f0000e0c

def z1217 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xffffffc01ffff000 0x7ffffff803fffe00

def z1218 : W := mkw 0x102040001fdf6a03 0x0204080003fbed40 0x100000001ffff000 0x0200000003fffe00

def z1219 : W := mkw 0x102040001f987a52 0x4204080003f30f4a 0x000000001c007000 0x0000000003800e00

def z1220 : W := mkw 0xe7dbbfebe0000000 0xbcfb77fd7c000000 0xe5e3ffcfe0000000 0x7cbc7ff9fc000000

def z1221 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0x47fffe001eff8000 0x28ffffc003dff000

def z1222 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0x4603f1f1fe1c7c7d 0xa8c07e3e3fc38f8f

def z1223 : W := mkw 0xe1dd9fffe0000000 0xbc3bb3fffc000000 0xe5ffcfffe0000000 0x7cbff9fffc000000

def z1224 : W := mkw 0xe7dfbfffe0004810 0xfcfbf7fffc000902 0xe7ffffffe0000c1c 0xfcfffffffc000183

def z1225 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xa5ffcfffe0000000 0x34bff9fffc000000

def z1226 : W := mkw 0x00891c0000000000 0x0011238000000000 0xc7fffe0000000000 0x78ffffc000000000

def z1227 : W := mkw 0x102040001fdf0001 0x0204080003fbe000 0x180000001fff8c7d 0x8300000003fff18f

def z1228 : W := mkw 0x20c18acb80000000 0x0418315970000000 0xfde3cfcf80100061 0x7fbc79f9f002000c

def z1229 : W := mkw 0x60c18bebc0005850 0x4c18317d78000b0a 0xede3cfffe0007c7d 0xfdbc79fffc000f8f

def z1230 : W := mkw 0xe7d3a9e940005850 0xfcfa753d28000b0a 0x2de3c1f1e0007c7d 0xa5bc783e3c000f8f

def z1231 : W := mkw 0x0081080000000000 0x0010210000000000 0x05e3c00000000000 0x20bc780000000000

def z1232 : W := mkw 0x20c18acb800080a0 0x0418315970001014 0xe5e3cfcf81038382 0x7cbc79f9f0207070

def z1233 : W := mkw 0x06ab7c001f5f0000 0x00d56f8003ebe000 0xd7fffe001fff8000 0x7affffc003fff000

def z1234 : W := mkw 0x17bb7c003fdf0009 0x22f76f8007fbe001 0xd7fffe007fff8018 0xfaffffc00ffff003

def z1235 : W := mkw 0x102040001fff0501 0x0204080003ffe0a0 0x180000001fff8f86 0x0300000003fff1f0

def z1236 : W := mkw 0x20c18acb80002200 0x0418315970000440 0xede3cfcf80007382 0x7dbc79f9f0000e70

def z1237 : W := mkw 0x679fbe57e06585a8 0xacf3f7cafc0cb0b5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1238 : W := mkw 0xd7bb7d205fdf0001 0xbaf76fa40bfbe000 0xd7fffe001fff8000 0x7affffc003fff000

def z1239 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xffffffffe3e38f86 0x7ffffffffc7c71f0

def z1240 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x87fc01fe1fe07f86 0x30ff803fc3fc0ff0

def z1241 : W := mkw 0x102040001f9a0001 0x0204080003f34000 0x100000001d138000 0x0200000003a27000

def z1242 : W := mkw 0x079b3c0000000000 0x20f3678000000000 0xfffffe31e21c0c7d 0xffffffc63c43818f

def z1243 : W := mkw 0xe04483ffe020ddf8 0xdc08907ffc041bbf 0x280001ffe0007fff 0x8500003ffc000fff

def z1244 : W := mkw 0xf7dfbffff2cd0001 0xbefbf7fffe59a000 0xf7ffffffe3ff8000 0x7efffffffc7ff000

def z1245 : W := mkw 0x173a74001fdd0000 0x02e74e8003fba000 0xd7fffe001fff8000 0x7affffc003fff000

def z1246 : W := mkw 0x0064009c09202700 0x000c8013812404e0 0xbdfc01ce1de07382 0x77bf8039c3bc0e70

def z1247 : W := mkw 0x2860c2cb8d12b2e0 0x050c185971a2565c 0x280001cf9c0073e3 0x05000039f3800e7c

def z1248 : W := mkw 0x082040001f1a7a50 0x4104080003e34f4a 0x000000001c007000 0x0000000003800e00

def z1249 : W := mkw 0x60c3a8c940000000 0xac18751928000000 0x05e3c1c000000000 0x20bc783800000000

def z1250 : W := mkw 0x479b3d2040000000 0x28f367a408000000 0xc7fffe3060000000 0x78ffffc60c000000

def z1251 : W := mkw 0x0081884100000000 0x0010310820000000 0xe5e3cfc180000000 0x7cbc79f830000000

def z1252 : W := mkw 0x17b95c001fd70000 0x02f72b8003fae000 0xd7fffe001fff8000 0x7affffc003fff000

def z1253 : W := mkw 0xe7dfbffff2084810 0xfcfbf7fffe410902 0xffffffffe21c0c7d 0xfffffffffc43818f

def z1254 : W := mkw 0x082040000d57b2e8 0x0104080001aaf65d 0x180000001d1ff3fb 0x8300000003a3fe7f

def z1255 : W := mkw 0xa7d3288800000000 0xb4fa651100000000 0x05e3c00000000000 0x20bc780000000000

def z1256 : W := mkw 0x079b3e0280000000 0x20f367c050000000 0xe7fffe0f80000000 0x7cffffc1f0000000

def z1257 : W := mkw 0xd77621bc5ba86f12 0x5aeec4378b750de2 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1258 : W := mkw 0x102040001fb87f52 0x4204080003f70fea 0x180000001fe07f86 0x0300000003fc0ff0

def z1259 : W := mkw 0x7ff3e9e95f9a7a51 0x6ffe7d3d2bf34f4a 0x05e3c1c01c007000 0x20bc783803800e00

def z1260 : W := mkw 0xe7dfbfffe04d0001 0xbcfbf7fffc09a000 0xe7ffffffe00c0000 0x7cfffffffc018000

def z1261 : W := mkw 0x102040001fff7f53 0x4204080003ffefea 0x180000001fffffff 0x8300000003ffffff

def z1262 : W := mkw 0xe7dfbfffe02085a8 0xbcfbf7fffc0410b5 0xffffffffe21c0fff 0xfffffffffc4381ff

def z1263 : W := mkw 0x27dfbedfa0000000 0x24fbf7dbf4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1264 : W := mkw 0x08244216ad32b7e8 0x01048842d5a656fd 0x3800003ffd13ffff 0x87000007ffa27fff

def z1265 : W := mkw 0xe7d3abebc0000000 0xbcfa757d78000000 0x85e3cfce00000000 0x30bc79f9c0000000

def z1266 : W := mkw 0xa1d18acb80000000 0xb43a315970000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z1267 : W := mkw 0xd73e75347fdf0001 0xbae7cea68ffbe000 0x121c30307fff8000 0x024386060ffff000

def z1268 : W := mkw 0x082040001f12fae0 0x0104080003e25f5c 0x180000001f13ffe7 0x0300000003e27ffc

def z1269 : W := mkw 0xe7dfbfffe020efaa 0xbcfbf7fffc041df5 0xefffffffe0007fff 0xfdfffffffc000fff

def z1270 : W := mkw 0xe7dfbfffe0650508 0xbcfbf7fffc0ca0a1 0xf7ffffffe3ff8c1c 0xfefffffffc7ff183

def z1271 : W := mkw 0xe1dfbfffe0000000 0xbc3bf7fffc000000 0xe1ffffffe0000000 0x1c3ffffffc000000

def z1272 : W := mkw 0x875621bc00000000 0x10eac43780000000 0xe7fff1fe00000000 0x7cfffe3fc0000000

def z1273 : W := mkw 0x00c1088800000000 0x0018211100000000 0xe5e3cfce00000000 0x7cbc79f9c0000000

def z1274 : W := mkw 0x0683280000000000 0x00d0650000000000 0xc7e3fe0000000000 0x78fc7fc000000000

def z1275 : W := mkw 0x66cfbfffe0000000 0x0cd9f7fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1276 : W := mkw 0xe0cd9fffe06585a8 0x9c19b3fffc0cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1277 : W := mkw 0xf7d3a9e952804802 0xbefa753d2a500900 0x05e3c1c000000000 0x20bc783800000000

def z1278 : W := mkw 0x20c18acb800080a0 0x0418315970001014 0xede3cfcf800003e3 0x7dbc79f9f000007c

def z1279 : W := mkw 0x20c188c900000000 0x0418311920000000 0xc5e3cfc000000000 0x78bc79f800000000

def z1280 : W := mkw 0xa9fd1e9ea967a7a8 0xb53fa3d3d52cf4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z1281 : W := mkw 0x17bb7c001fdf1041 0x22f76f8003fbe208 0xdffffe001ffff061 0x7bffffc003fffe0c

def z1282 : W := mkw 0x0602e04116181040 0x00c05c0822c30208 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1283 : W := mkw 0x4e2261205f1afaf0 0x49c44c240be35f5e 0x1a0030307f1fffff 0x834006060fe3ffff

def z1284 : W := mkw 0x479bbd6140005850 0x68f377ac28000b0a 0xeffffff1e0007c7d 0xfdfffffe3c000f8f

def z1285 : W := mkw 0xe7dbbde940000000 0xbcfb77bd28000000 0x85ffcfc000000000 0x30bff9f800000000

def z1286 : W := mkw 0x27db3e8a80000000 0x24fb67d150000000 0xc7fffe0e00000000 0x78ffffc1c0000000

def z1287 : W := mkw 0xb9fd1e9ea9e7a7aa 0x173fa3d3d53cf4f5 0x81fc0e0e01e38382 0x103f81c1c03c7070

def z1288 : W := mkw 0x179f3e16b2ed85a9 0x22f3e7c2d65db0b5 0xfffffe3fe3ff8fff 0xffffffc7fc7ff1ff

def z1289 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0x2ffc01fe1ee07f86 0x25ff803fc3dc0ff0

def z1290 : W := mkw 0x68e1cacbed12b2e0 0x8d1c39597da2565c 0xfde3cfcffd13f3e3 0x7fbc79f9ffa27e7c

def z1291 : W := mkw 0x20c99ecba0000000 0x041933d974000000 0xe5e3ffcfe0000000 0x7cbc7ff9fc000000

def z1292 : W := mkw 0x002040000d122200 0x0004080001a24440 0x180000001d13f382 0x0300000003a27e70

def z1293 : W := mkw 0xe7d3a9e952004800 0xbcfa753d2a400900 0x3fe3c1f01e007c04 0x67fc783e03c00f80

def z1294 : W := mkw 0x002040000d5f0001 0x0004080001abe000 0x100000001d1f8000 0x0200000003a3f000

def z1295 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0x080000001c0073e3 0x0100000003800e7c

def z1296 : W := mkw 0xe7dfbdfd60650508 0xbcfbf7bfac0ca0a1 0x07fff1f062ec0c1c 0xa0fffe3e0c5d8183

def z1297 : W := mkw 0x0793280000000000 0x20f2650000000000 0xc5e3ce0000000000 0x78bc79c000000000

def z1298 : W := mkw 0x977621bc1ba06f02 0x12eec43783740de0 0xfffff1fe1fe07f86 0x7ffffe3fc3fc0ff0

def z1299 : W := mkw 0x00a1ca438d1290e0 0x0014394871a2521c 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z1300 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xbdfc01ce1de07382 0x77bf8039c3bc0e70

def z1301 : W := mkw 0x973e75341fff6f03 0x32e7cea683ffede0 0x1a1c30301fffff86 0x0343860603fffff0

def z1302 : W := mkw 0xb864c3ff9fb2ffe2 0x170c987ff3f65ffc 0x380001ff9ff3ffe7 0x0700003ff3fe7ffc

def z1303 : W := mkw 0x00810a0280000000 0x0010214050000000 0xe5e3ce0f80000000 0x7cbc79c1f0000000

def z1304 : W := mkw 0x102854001fdf0001 0x02050a8003fbe000 0x901c0e001fff8000 0x120381c003fff000

def z1305 : W := mkw 0xe1dfbedfe0000000 0xbc3bf7dbfc000000 0xe3fffe3fe0000000 0x5c7fffc7fc000000

def z1306 : W := mkw 0xe7dfbfffe0200500 0xbcfbf7fffc0400a0 0xe7ffffffe1e00382 0x7cfffffffc3c0070

def z1307 : W := mkw 0xa0c58bff80000000 0x1418b17ff0000000 0xe5e3cfff80000000 0x7cbc79fff0000000

def z1308 : W := mkw 0xefdfbfffe020b7e8 0xbdfbf7fffc0416fd 0xefffffffe0007fff 0xfdfffffffc000fff

def z1309 : W := mkw 0x97ff3dbc1be56f02 0x32ffe7b7837cade0 0xfffffffe1fffff86 0x7fffffffc3fffff0

def z1310 : W := mkw 0x102040001fdf1041 0x0204080003fbe208 0x180000001ffff061 0x0300000003fffe0c

def z1311 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0xb800000e1d13f3e3 0x57000001c3a27e7c

def z1312 : W := mkw 0xe7d58bffe0000000 0x9cfab17ffc000000 0xe7ffcfffe0000000 0x7cfff9fffc000000

def z1313 : W := mkw 0x2860c2cb8d12b2e0 0x050c185971a2565c 0xf8000fcf9d13f3e3 0x5f0001f9f3a27e7c

def z1314 : W := mkw 0x977621bc1ba86f03 0x32eec43783750de0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1315 : W := mkw 0xe0cd9fffe0000000 0x9c19b3fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1316 : W := mkw 0x20c188c900000000 0x0418311920000000 0xa5e3c1ce00000000 0x74bc7839c0000000

def z1317 : W := mkw 0x162041201fdf4801 0x02c4082403fbe900 0x3e0001f01ffffc04 0x67c0003e03ffff80

def z1318 : W := mkw 0x28e1cacb8d1ab2f0 0x451c395971a3565e 0xfde3cfcf9d1ff3fb 0xffbc79f9f3a3fe7f

def z1319 : W := mkw 0xe7dfbfffe04580a8 0xbcfbf7fffc08b015 0xffffffffe21f8c7d 0xfffffffffc43f18f

def z1320 : W := mkw 0x20818a4380000000 0x0410314870000000 0xc5e3ce0180000000 0x78bc79c030000000

def z1321 : W := mkw 0x20cbbecb80000000 0x241977d970000000 0xe5e3ffcf80000000 0x7cbc7ff9f0000000

def z1322 : W := mkw 0x875441bc16185850 0x50ea883782c30b0a 0xbffc01fe1e1c7c7d 0xf7ff803fc3c38f8f

def z1323 : W := mkw 0x102040001fdf5851 0x4204080003fbeb0a 0x100000001ffff000 0x0200000003fffe00

def z1324 : W := mkw 0x6793a84140000000 0xacf2750828000000 0x05e3c00000000000 0x20bc780000000000

def z1325 : W := mkw 0x182040001ff7ffea 0x0304080003fefffd 0x180000001fffffff 0x8300000003ffffff

def z1326 : W := mkw 0x082040001f1a7a50 0x4104080003e34f4a 0x180000001e1c7c7d 0x8300000003c38f8f

def z1327 : W := mkw 0x20cd9edfa0650508 0x0419b3dbf40ca0a1 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z1328 : W := mkw 0x082042028d12b2e0 0x0104084051a2565c 0x58000e019d13f3e3 0x0b0001c033a27e7c

def z1329 : W := mkw 0xa1d188c900000000 0xb43a311920000000 0x05e3c1c000000000 0x20bc783800000000

def z1330 : W := mkw 0x408bfe43e45f90f9 0x68117fc87c8bf21f 0x4003fe01e01f8079 0x88007fc03c03f00f

def z1331 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xbffc01ffffe07fff 0xf7ff803ffffc0fff

def z1332 : W := mkw 0x0602200000000000 0x00c0440000000000 0x5603f000021c0000 0x6ac07e0000438000

def z1333 : W := mkw 0x162040001fdf0001 0x02c4080003fbe000 0x160000001fff8000 0x62c0000003fff000

def z1334 : W := mkw 0x082440140d32b7e0 0x0104880281a656fc 0xba1c003e1ff3ffe7 0x57438007c3fe7ffc

def z1335 : W := mkw 0x4000c16144105850 0x4800182c28820b0a 0x7e03f1f1fe1c7c7d 0xefc07e3e3fc38f8f

def z1336 : W := mkw 0x0081080000000000 0x0010210000000000 0xd5e3ce0001138000 0x7abc79c000227000

def z1337 : W := mkw 0x27d18acb80000000 0x04fa315970000000 0xe7ffcfcf80000000 0x7cfff9f9f0000000

def z1338 : W := mkw 0x17bb7c000ddf0001 0x22f76f8001bbe000 0xc7fffe0001ff8000 0x78ffffc0003ff000

def z1339 : W := mkw 0x87df3dbc00650500 0x30fbe7b7800ca0a0 0xfffffffe03ff8f86 0x7fffffffc07ff1f0

def z1340 : W := mkw 0x57bb7d205fdf0001 0x2af76fa40bfbe000 0xd7fffe307fff8000 0x7affffc60ffff000

def z1341 : W := mkw 0xa1dd9edfa0000000 0xb43bb3dbf4000000 0xc1ffce0f80000000 0x183ff9c1f0000000

def z1342 : W := mkw 0x00a95c000d570000 0x00152b8001aae000 0xd5ffce001df38000 0x7abff9c003be7000

def z1343 : W := mkw 0x28c18acb800090e0 0x051831597000121c 0xe5e3cfcf80000061 0x7cbc79f9f000000c

def z1344 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xefffffffe2ec0fff 0xfdfffffffc5d81ff

def z1345 : W := mkw 0x5622a1615ba06f02 0x0ac4542c2b740de0 0x7e03f1f1ffe07f86 0x6fc07e3e3ffc0ff0

def z1346 : W := mkw 0x002854000d570000 0x00050a8001aae000 0xd21c3e001fff8000 0x5a4387c003fff000

def z1347 : W := mkw 0x079b3c0000470001 0x20f367800008e000 0xc7fffe0000038000 0x78ffffc000007000

def z1348 : W := mkw 0xe7dfbffff2084810 0xfcfbf7fffe410902 0xfffffffffe0c7c1c 0xffffffffffc18f83

def z1349 : W := mkw 0xe1dfbedfe06585a8 0xbc3bf7dbfc0cb0b5 0xfbfffe3fe3ff8fff 0xdf7fffc7fc7ff1ff

def z1350 : W := mkw 0x279b3e02a0000000 0xa4f367c054000000 0xc7fffe0000000000 0x78ffffc000000000

def z1351 : W := mkw 0x4602e16156185850 0x48c05c2c2ac30b0a 0xfe03fff1ff1ffc7d 0xffc07ffe3fe3ff8f

def z1352 : W := mkw 0xe7dfbfffe0206f02 0xbcfbf7fffc040de0 0xffffffffe3e07f86 0x7ffffffffc7c0ff0

def z1353 : W := mkw 0x67dbbfebc0000000 0x2cfb77fd78000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1354 : W := mkw 0x182040001f9a3241 0x0304080003f34648 0x000000001c007000 0x0000000003800e00

def z1355 : W := mkw 0x082040001f1ab2e0 0x0104080003e3565c 0x180000001f1ff3e3 0x0300000003e3fe7c

def z1356 : W := mkw 0xe7d3a9e940005850 0xfcfa753d28000b0a 0x05e3c1c000007000 0x20bc783800000e00

def z1357 : W := mkw 0x002042028d1280a0 0x0004084051a25014 0xf8000e0f9d1383e3 0x5f0001c1f3a2707c

def z1358 : W := mkw 0xe7dfbfffe00080a0 0xbcfbf7fffc001014 0xefffffffe00003e3 0x7dfffffffc00007c

def z1359 : W := mkw 0x2889de43845790e1 0x25113bc8708af21c 0x4003ce0180138061 0x080079c03002700c

def z1360 : W := mkw 0x11bb7c001fdf0001 0x22376f8003fbe000 0xd1fffe001fff8000 0x1a3fffc003fff000

def z1361 : W := mkw 0x182040000dd7b2e1 0x0304080001baf65c 0x180000001df3f3e3 0x0300000003be7e7c

def z1362 : W := mkw 0x102040001fff4d03 0x0204080003ffe9a0 0x100000001fff8c04 0x0200000003fff180

def z1363 : W := mkw 0x17bb7d201fdf5851 0x62f76fa403fbeb0a 0xfffffff01ffffc7d 0xfffffffe03ffff8f

def z1364 : W := mkw 0x28cd9edfa020b7e8 0x0519b3dbf40416fd 0xefffffffe0007fff 0xfdfffffffc000fff

def z1365 : W := mkw 0x20c58adfa02085a8 0x0418b15bf40410b5 0xede3cfffe0000fff 0xfdbc79fffc0001ff

def z1366 : W := mkw 0xe7dfbfffe00080a0 0xbcfbf7fffc001014 0xffffffffe31f8fff 0xfffffffffc63f1ff

def z1367 : W := mkw 0x2860428a8d12b2e0 0x050c085151a2565c 0x1800000e1d13f3e3 0x03000001c3a27e7c

def z1368 : W := mkw 0xe7dfbfffe0450000 0xbcfbf7fffc08a000 0xe7ffffffe1e38000 0x7cfffffffc3c7000

def z1369 : W := mkw 0x20c99ecba0000000 0xa41933d974000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z1370 : W := mkw 0x877401bc09202700 0x10ee8037812404e0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1371 : W := mkw 0x17bb7c001fdf1051 0x62f76f8003fbe20a 0xd7fffe001fff8079 0xfaffffc003fff00f

def z1372 : W := mkw 0xa0c58adfa0000000 0x9418b15bf4000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z1373 : W := mkw 0xe7dfbfffe0202702 0xbcfbf7fffc0404e0 0xe7ffffffe0000382 0x7cfffffffc000070

def z1374 : W := mkw 0x284482df8020b7e0 0x0508905bf00416fc 0x280001ff80007fe7 0x0500003ff0000ffc

def z1375 : W := mkw 0xe84483ffc020fff2 0x5d08907ff8041ffe 0x280001ffe0007fff 0x8500003ffc000fff

def z1376 : W := mkw 0xe7dfbfffe04580a8 0xbcfbf7fffc08b015 0xf7ffffffe3ff8079 0xfefffffffc7ff00f

def z1377 : W := mkw 0x079f3c1420000000 0x20f3e78284000000 0xc7fffe3060000000 0x78ffffc60c000000

def z1378 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe7ffffffe01c0079 0xfcfffffffc03800f

def z1379 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xd5e3cfce1d13f382 0x7abc79f9c3a27e70

def z1380 : W := mkw 0x17b368001f9a0001 0x22f66d0003f34000 0xd7ffce001ff38000 0x7afff9c003fe7000

def z1381 : W := mkw 0xa1dd1e9ea0000000 0xb43ba3d3d4000000 0xc5ffce0e00000000 0x78bff9c1c0000000

def z1382 : W := mkw 0xf7dfbffff2800000 0xbefbf7fffe500000 0xe7ffffffe2e00000 0x7cfffffffc5c0000

def z1383 : W := mkw 0xe7d3abebc0000000 0xbcfa757d78000000 0x25e3c1cf80000000 0x24bc7839f0000000

def z1384 : W := mkw 0x082040000d12b2e0 0x0104080001a2565c 0xd8000e001d13f3e3 0x5b0001c003a27e7c

def z1385 : W := mkw 0xc752a1e940000000 0x18ea543d28000000 0x67e3f1f1e0000000 0x6cfc7e3e3c000000

def z1386 : W := mkw 0xa7df3e9ea0000000 0xb4fbe7d3d4000000 0x85ffce0e00000000 0x30bff9c1c0000000

def z1387 : W := mkw 0x906401bc1ba06f02 0x120c803783740de0 0x280001fe1c007f86 0x0500003fc3800ff0

def z1388 : W := mkw 0x60cfbedfe0000000 0xac19f7dbfc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1389 : W := mkw 0x20c18acb80000000 0x0418315970000000 0x45e3cfc180000000 0x28bc79f830000000

def z1390 : W := mkw 0x971e353432ed4d0b 0x32e3c6a6865da9a1 0x021c303062ec0c1c 0x804386060c5d8183

def z1391 : W := mkw 0xa7dd9fffa06585a8 0x14fbb3fff40cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1392 : W := mkw 0xe7d3a9e952004800 0xbcfa753d2a400900 0x05e3c1c01c007000 0x20bc783803800e00

def z1393 : W := mkw 0x20c18acb806585a8 0x04183159700cb0b5 0xfde3cfcf83ff8fff 0xffbc79f9f07ff1ff

def z1394 : W := mkw 0x102040001ffdfffa 0x4204080003ffbfff 0x180000001fffffff 0x8300000003ffffff

def z1395 : W := mkw 0x07db3c8800000000 0x20fb679100000000 0xe7ffffce00000000 0x7cfffff9c0000000

def z1396 : W := mkw 0x179b3c0012cd0001 0x22f367800259a000 0x07fff00002ec0000 0x20fffe00005d8000

def z1397 : W := mkw 0x086040880d12b2e0 0x010c081101a2565c 0x380001ce1d13f3e3 0x07000039c3a27e7c

def z1398 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xe7ffffffe20c0c1c 0xfcfffffffc418183

def z1399 : W := mkw 0xe7d7a9fd40206f02 0xbcfaf53fa8040de0 0x2de3c1fe00007f86 0x25bc783fc0000ff0

def z1400 : W := mkw 0x479fbf77e06585a8 0x28f3f7eefc0cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1401 : W := mkw 0x57bb7d205fdf4811 0x6af76fa40bfbe902 0xfffffe31ffff8c7d 0xffffffc63ffff18f

def z1402 : W := mkw 0x20c58adf80200500 0x0418b15bf00400a0 0xffffcfff83e00f86 0x7ffff9fff07c01f0

def z1403 : W := mkw 0x102040001f987a52 0x4204080003f30f4a 0x180000001e1c7c7d 0x8300000003c38f8f

def z1404 : W := mkw 0x28c18acb80003240 0x0518315970000648 0xe5e3cfcf80007000 0x7cbc79f9f0000e00

def z1405 : W := mkw 0xe7dfbfffe02085a8 0xbcfbf7fffc0410b5 0xe7ffffffe0000382 0x7cfffffffc000070

def z1406 : W := mkw 0x608bbe43e0000000 0xac1177c87c000000 0xc5e3fe01e0000000 0x78bc7fc03c000000

def z1407 : W := mkw 0x000c141400650500 0x00018282800ca0a0 0xfa1c3e3fe3ff8fff 0xdf4387c7fc7ff1ff

def z1408 : W := mkw 0xf7dfbfffe0a00502 0xbefbf7fffc1400a0 0xe7ffffffe0e00000 0x7cfffffffc1c0000

def z1409 : W := mkw 0x082040001f7ffff8 0x4104080003efffff 0x180000001fffffff 0x8300000003ffffff

def z1410 : W := mkw 0xa1df3e9ea0000000 0xb43be7d3d4000000 0xc1fffe0e00000000 0x183fffc1c0000000

def z1411 : W := mkw 0xe7dfbfffe0207f52 0xfcfbf7fffc040fea 0xefffffffe0007fff 0xfdfffffffc000fff

def z1412 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xfde3cffffd13ffff 0xffbc79ffffa27fff

def z1413 : W := mkw 0x87df3fbea06585a8 0x30fbe7f7d40cb0b5 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1414 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xefffffffe01f8fff 0xfdfffffffc03f1ff

def z1415 : W := mkw 0x179b3c0000c50001 0x22f367800018a000 0xc7fffe0000e00000 0x78ffffc0001c0000

def z1416 : W := mkw 0x28a14a028d12b2e0 0x0514294051a2565c 0x18000e001d13f3e3 0x030001c003a27e7c

def z1417 : W := mkw 0x20c18acb80000000 0x0418315970000000 0x25e3c1cf80000000 0x24bc7839f0000000

def z1418 : W := mkw 0xe7dfbdfd60000000 0xbcfbf7bfac000000 0xc7fffff060000000 0x78fffffe0c000000

def z1419 : W := mkw 0x26c18beb92004800 0x04d8317d72400900 0xffe3cfff9e007c04 0x7ffc79fff3c00f80

def z1420 : W := mkw 0xa7d589fd00000000 0x14fab13fa0000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z1421 : W := mkw 0xe7dfbfffe02085a8 0xbcfbf7fffc0410b5 0xffffffffe3e00fff 0xfffffffffc7c01ff

def z1422 : W := mkw 0x17bb7d201fdf4801 0x22f76fa403fbe900 0xd7fffe301fff8c04 0x7affffc603fff180

def z1423 : W := mkw 0x179b7c0016df0001 0x22f36f8002dbe000 0xc7fffe0002ff8000 0x78ffffc0005ff000

def z1424 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xffe3fffffd13f3e3 0x7ffc7fffffa27e7c

def z1425 : W := mkw 0x6860c3ebdf1afaf0 0x4d0c187d7be35f5e 0x380001ffff1fffff 0x8700003fffe3ffff

def z1426 : W := mkw 0xafd58bff8020ffe2 0x15fab17ff0041ffc 0xefffcfff80007fe7 0x7dfff9fff0000ffc

def z1427 : W := mkw 0x102040001fff2703 0x0204080003ffe4e0 0x100000001fff8382 0x0200000003fff070

def z1428 : W := mkw 0xe7d7abffe0000000 0xbcfaf57ffc000000 0x67e3f1ffe0000000 0x6cfc7e3ffc000000

def z1429 : W := mkw 0x973441341fff4d03 0x12e6882683ffe9a0 0x121c00301fff8c04 0x0243800603fff180

def z1430 : W := mkw 0xa7dd9fffa0000000 0x14fbb3fff4000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1431 : W := mkw 0x9f3441341fb2ffe2 0x13e6882683f65ffc 0x1a1c00301ff3ffe7 0x0343800603fe7ffc

def z1432 : W := mkw 0xd756a1fd52a84d12 0x5aead43faa5509a2 0xe7fff1ffe2ec0c1c 0xfcfffe3ffc5d8183

def z1433 : W := mkw 0x17bb3c001bc50000 0x22f767800378a000 0xd7fffe001fff8000 0x7affffc003fff000

def z1434 : W := mkw 0x182040001fdf3241 0x0304080003fbe648 0x100000001ffff000 0x0200000003fffe00

def z1435 : W := mkw 0xefdfbfffe00090e0 0xbdfbf7fffc00121c 0xe7ffffffe0000061 0x7cfffffffc00000c

def z1436 : W := mkw 0x079b3c0012080000 0x20f3678002410000 0xc7fffe00020c0000 0x78ffffc000418000

def z1437 : W := mkw 0x0e2041201f12fae0 0x01c4082403e25f5c 0x3e0001f01f13ffe7 0x67c0003e03e27ffc

def z1438 : W := mkw 0x00e14a8a8d12a2a0 0x001c295151a25454 0xfde3cfcf9d13f3e3 0x7fbc79f9f3a27e7c

def z1439 : W := mkw 0x008b3c0000450000 0x201167800008a000 0x4003fe00001f8000 0x08007fc00003f000

def z1440 : W := mkw 0xe7dfbfffe0004800 0xbcfbf7fffc000900 0xefffffffe0007c04 0x7dfffffffc000f80

def z1441 : W := mkw 0x01991c0000000000 0x2033238000000000 0xc5ffce0000000000 0x78bff9c000000000

def z1442 : W := mkw 0xe7dfbffff26dcdb8 0xfcfbf7fffe4db9b7 0xffffffffe3ff8fff 0xfffffffffc7ff1ff

def z1443 : W := mkw 0xe1dfbedfe06585a8 0xbc3bf7dbfc0cb0b5 0xc1fffe0fe1ff83fb 0x983fffc1fc3ff07f

def z1444 : W := mkw 0x002040001f1a5850 0x4004080003e34b0a 0x180000001f1ffc7d 0x8300000003e3ff8f

def z1445 : W := mkw 0x27d3a8c900000000 0x24fa751920000000 0x05e3c1c000000000 0x20bc783800000000

def z1446 : W := mkw 0x28c18acb8000a2a0 0x0518315970001454 0xe5e3cfcf80000382 0x7cbc79f9f0000070

def z1447 : W := mkw 0x573a75205fdf5851 0x6ae74ea40bfbeb0a 0x1a1c30307ffffc7d 0x834386060fffff8f

def z1448 : W := mkw 0x977001a81b806a02 0x12ee003503700d40 0xbffc01ce1fe07382 0x77ff8039c3fc0e70

def z1449 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xc5e3cfcf9d13f3e3 0x38bc79f9f3a27e7c

def z1450 : W := mkw 0x28cd9edfa065b7e8 0x0519b3dbf40cb6fd 0xffffffffe3ffffff 0xfffffffffc7fffff

def z1451 : W := mkw 0x173e74143fff85a9 0x22e7ce8287fff0b5 0x1a1c30307fff8fff 0x834386060ffff1ff

def z1452 : W := mkw 0x684483ffe020fff8 0x4d08907ffc041fff 0x280001ffe0007fff 0x8500003ffc000fff

def z1453 : W := mkw 0xc7df3dbc60000000 0xb8fbe7b78c000000 0xe7fffffe60000000 0x7cffffffcc000000

def z1454 : W := mkw 0xa1dd9edfa0000000 0xb43bb3dbf4000000 0x85ffcfce00000000 0x30bff9f9c0000000

def z1455 : W := mkw 0x679bbf63e0000000 0xacf377ec7c000000 0xe7fffff1e0000000 0x7cfffffe3c000000

def z1456 : W := mkw 0x20e1cacb8d122200 0x041c395971a24440 0xfde3cfcf9d13f382 0x7fbc79f9f3a27e70

def z1457 : W := mkw 0x079f3e16a0000000 0x20f3e7c2d4000000 0xc7fffe0e00000000 0x78ffffc1c0000000

def z1458 : W := mkw 0x66c3abebc00080a0 0x0cd8757d78001014 0xffe3ffffe31f8fff 0xfffc7ffffc63f1ff

def z1459 : W := mkw 0xe756a3ffe0000000 0x9cead47ffc000000 0xe7fff1ffe0000000 0x7cfffe3ffc000000

def z1460 : W := mkw 0x082040000d123240 0x0104080001a24648 0x100000001d13f000 0x0200000003a27e00

def z1461 : W := mkw 0x17bb7d201fdf4801 0x22f76fa403fbe900 0xd7ffffc01ffff000 0x7afffff803fffe00

def z1462 : W := mkw 0x0710000000000000 0x00e2000000000000 0x97fc000003e00000 0x72ff8000007c0000

def z1463 : W := mkw 0xa7dd9fffa0000000 0xb4fbb3fff4000000 0xe7ffcfff80000000 0x7cfff9fff0000000

def z1464 : W := mkw 0x879f3d3400000000 0x30f3e7a680000000 0xc7fffe3000000000 0x78ffffc600000000

def z1465 : W := mkw 0xe7dfbfffe04580a8 0xbcfbf7fffc08b015 0xe7ffffffe0038000 0x7cfffffffc007000

def z1466 : W := mkw 0x002040000d120000 0x0004080001a24000 0x000000001c000000 0x0000000003800000

def z1467 : W := mkw 0x08e148880d12b2e0 0x011c291101a2565c 0xfde3cfce1d13f3e3 0x7fbc79f9c3a27e7c

def z1468 : W := mkw 0xe7d3abebc00080a0 0xbcfa757d78001014 0xfde3cfcf811383e3 0x7fbc79f9f022707c

def z1469 : W := mkw 0xe7dfbfffe0001040 0xbcfbf7fffc000208 0xefffffffe0007061 0x7dfffffffc000e0c

def z1470 : W := mkw 0x082040000d12faf0 0x4104080001a25f5e 0x180000001d13ffff 0x8300000003a27fff

def z1471 : W := mkw 0x182040001fdf90e1 0x0304080003fbf21c 0x100000001fff8061 0x0200000003fff00c

def z1472 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xfde3cfcf9f1fffff 0xffbc79f9f3e3ffff

def z1473 : W := mkw 0x0060008809002200 0x000c001101200440 0xbffc01ce1fe07382 0x77ff8039c3fc0e70

def z1474 : W := mkw 0xe7d3a9e940000000 0xbcfa753d28000000 0x47e3f1c000000000 0x68fc7e3800000000

def z1475 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xfffc31ffffe07f86 0x7fff863ffffc0ff0

def z1476 : W := mkw 0x4793a96140000000 0x28f2752c28000000 0x05e3c1c000000000 0x20bc783800000000

def z1477 : W := mkw 0x102040001fb86f02 0x0204080003f70de0 0x180000001ffc7f86 0x0300000003ff8ff0

def z1478 : W := mkw 0x008d1e16a0000000 0x0011a3c2d4000000 0xe7fffe3fe0000000 0x7cffffc7fc000000

def z1479 : W := mkw 0xe7dfbffff26d4d18 0xfcfbf7fffe4da9a3 0xe7ffffffe2ec0c1c 0xfcfffffffc5d8183

def z1480 : W := mkw 0xe7dfbfffe06585a8 0xbcfbf7fffc0cb0b5 0xe7ffffffe1ff83fb 0xfcfffffffc3ff07f

def z1481 : W := mkw 0x10a95c001fdf0001 0x22152b8003fbe000 0x10000e001fff8000 0x020001c003fff000

def z1482 : W := mkw 0x979f3d3412a04d02 0x32f3e7a6825409a0 0xc7fffe3002e00c04 0x78ffffc6005c0180

def z1483 : W := mkw 0x102040001fdf1051 0x4204080003fbe20a 0x100000001fff8079 0x8200000003fff00f

def z1484 : W := mkw 0xe7dfbffff2000000 0xbcfbf7fffe400000 0xf7fffffffe000000 0x7effffffffc00000

def z1485 : W := mkw 0xe0c18bebc0000000 0x9c18317d78000000 0xe5e3cfcf80000000 0x7cbc79f9f0000000

def z1486 : W := mkw 0x000c1616a06585a8 0x000182c2d40cb0b5 0xfe1c3fffffffffff 0xffc387ffffffffff

def z1487 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xffe3ffcf9f1ff3e3 0x7ffc7ff9f3e3fe7c

def z1488 : W := mkw 0x182040001fdfa2a1 0x0304080003fbf454 0x100000001fff8382 0x0200000003fff070

def z1489 : W := mkw 0x002040000d103240 0x0004080001a20648 0x180000001d1073e3 0x0300000003a20e7c

def z1490 : W := mkw 0x082c54142d77b7e8 0x01058a8285aef6fd 0x1a1c30307fffffff 0x834386060fffffff

def z1491 : W := mkw 0x182040001f927a42 0x0304080003f24f48 0x000000001c007000 0x0000000003800e00

def z1492 : W := mkw 0xc79fbd7560000000 0xb8f3f7aeac000000 0xe7fffff1e0000000 0x7cfffffe3c000000

def z1493 : W := mkw 0x17bb7c000dd70001 0x22f76f8001bae000 0xd7fffe001df38000 0x7affffc003be7000

def z1494 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xefffffffe0000c7d 0xfdfffffffc00018f

def z1495 : W := mkw 0x102040001fdf80a1 0x0204080003fbf014 0x180000001fff83e3 0x0300000003fff07c

def z1496 : W := mkw 0xe7dfbffff2084810 0xfcfbf7fffe410902 0xe7ffffffe0000000 0x7cfffffffc000000

def z1497 : W := mkw 0xc71e3534726d4d18 0xf8e3c6a68e4da9a3 0x021c303062ec0c1c 0x804386060c5d8183

def z1498 : W := mkw 0x875401bc12204d00 0x10ea8037824409a0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1499 : W := mkw 0x20c18acb800080a0 0x0418315970001014 0xe5e3cfcf80138061 0x7cbc79f9f002700c

def z1500 : W := mkw 0x173040001fdf0001 0x02e6080003fbe000 0x121c00001fff8000 0x0243800003fff000

def z1501 : W := mkw 0x479bbc4140000000 0x28f3778828000000 0xc7fffe01e0000000 0x78ffffc03c000000

def z1502 : W := mkw 0x20cd9edfa06585a8 0x0419b3dbf40cb0b5 0xe5ffcfcf81e38382 0x7cbff9f9f03c7070

def z1503 : W := mkw 0x679bbe43e04580a8 0xacf377c87c08b015 0xd7fffe01e3ff8079 0xfaffffc03c7ff00f

def z1504 : W := mkw 0x87d329a800000000 0x30fa653500000000 0x05e3c1c000000000 0x20bc783800000000

def z1505 : W := mkw 0xe7d7a9fd40000000 0xbcfaf53fa8000000 0xe7fff1ffe0000000 0x7cfffe3ffc000000

def z1506 : W := mkw 0x071a340000450000 0x20e346800008a000 0x021c300002ec0000 0x00438600005d8000

def z1507 : W := mkw 0x66c3a9e940000000 0x0cd8753d28000000 0x67e3f1f1e0000000 0x6cfc7e3e3c000000

def z1508 : W := mkw 0x082c5616ad77b7e8 0x01058ac2d5aef6fd 0x981c0e0e1df3f3e3 0x130381c1c3be7e7c

def z1509 : W := mkw 0xc756a1fd40000000 0x18ead43fa8000000 0xa7ffc1fe00000000 0x74fff83fc0000000

def z1510 : W := mkw 0x162260001fdf0001 0x02c44c0003fbe000 0x120030001fff8000 0x0240060003fff000

def z1511 : W := mkw 0x28e18acb8902a2a0 0x051c315971205454 0xfde3cfcf9d03f382 0x7fbc79f9f3a07e70

def z1512 : W := mkw 0xe0c58bffe0000000 0x9c18b17ffc000000 0x25e3c1ffe0000000 0x24bc783ffc000000

def z1513 : W := mkw 0x173e7616bfff85a9 0x22e7cec2d7fff0b5 0xfa1c3e3fffff8fff 0xdf4387c7fffff1ff

def z1514 : W := mkw 0xe7dfbfffe02085a8 0xbcfbf7fffc0410b5 0xffffffffe1138fff 0xfffffffffc2271ff

def z1515 : W := mkw 0xe7dfbfffe00080a0 0xbcfbf7fffc001014 0xe7ffffffe1038382 0x7cfffffffc207070

def z1516 : W := mkw 0xc75eb7ffe0000000 0x18ebd6fffc000000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1517 : W := mkw 0xe7dfbfffe02085a0 0xbcfbf7fffc0410b4 0xffffffffe3f38fe7 0x7ffffffffc7e71fc

def z1518 : W := mkw 0x182040000db2b7e2 0x0304080001b656fc 0x180000001df3f3e3 0x0300000003be7e7c

def z1519 : W := mkw 0xe7dfbfffe0650508 0xbcfbf7fffc0ca0a1 0xffffffffe3ec0f9e 0xfffffffffc7d81f3

def z1520 : W := mkw 0xe7dfbffff2005850 0xfcfbf7fffe400b0a 0xfffffffffe007c7d 0xffffffffffc00f8f

def z1521 : W := mkw 0x28e1cacb8d12b2e0 0x051c395971a2565c 0xffffcfcf9ff3f3e3 0x7ffff9f9f3fe7e7c

def z1522 : W := mkw 0xf7dfbffff2880001 0xbefbf7fffe510000 0xe7ffffffe0000000 0x7cfffffffc000000

def z1523 : W := mkw 0x102040001f985850 0x4204080003f30b0a 0x180000001ffc7c7d 0x8300000003ff8f8f

def z1524 : W := mkw 0x2ffbfecb8d57b2e0 0x25ff7fd971aaf65c 0xffffffcf9ffff3e3 0x7ffffff9f3fffe7c

def z1525 : W := mkw 0x17b148001fdf0001 0x02f6290003fbe000 0xd7ffce001fff8000 0x7afff9c003fff000

def z1526 : W := mkw 0x977401bc1ba06f02 0x12ee803783740de0 0xa7fc01fe1de07382 0x74ff803fc3bc0e70

def z1527 : W := mkw 0x182040001fdffaf1 0x4304080003fbff5e 0x180000001fffffff 0x8300000003ffffff

def z1528 : W := mkw 0x002040001f1a0000 0x0004080003e34000 0x100000001f1f8000 0x0200000003e3f000

def z1529 : W := mkw 0x17bb7c001fdf0001 0x22f76f8003fbe000 0xf7fffe31ffff8000 0x7effffc63ffff000

def z1530 : W := mkw 0xe7dfbfffe0000000 0xbcfbf7fffc000000 0xffffffffe1000382 0x7ffffffffc200070

def z1531 : W := mkw 0xe1d3a8c940000000 0xbc3a751928000000 0x01e3c00000000000 0x003c780000000000

def z1532 : W := mkw 0xc75eb5fd60000000 0xb8ebd6bfac000000 0xe7fff1ffe0000000 0x7cfffe3ffc000000

def z1533 : W := mkw 0x28e1c8c90d123240 0x051c391921a24648 0xfde3cfce1d13f382 0x7fbc79f9c3a27e70

def z1534 : W := mkw 0x102040001f9a5851 0x4204080003f34b0a 0x000000001c007000 0x0000000003800e00

def z1535 : W := mkw 0x182040001f9ab2e1 0x0304080003f3565c 0x180000001d13f3e3 0x0300000003a27e7c

def z1536 : W := mkw 0xe7dfbfffe020ddf8 0xfcfbf7fffc041bbf 0xefffffffe0007fff 0xfdfffffffc000fff

def z1537 : W := mkw 0x102040001f9a6a03 0x0204080003f34d40 0x000000001c007000 0x0000000003800e00

def z1538 : W := mkw 0xa7df3fbea0000000 0xb4fbe7f7d4000000 0xe7fffffe00000000 0x7cffffffc0000000

def z1539 : W := mkw 0x17b95c001fd70001 0x22f72b8003fae000 0xd7ffce001ff38000 0x7afff9c003fe7000

def z1540 : W := mkw 0x17bb7d201fdf0001 0x22f76fa403fbe000 0xf7fffff01fff8000 0x7efffffe03fff000

def z1541 : W := mkw 0x2860c0c90d123240 0x050c181921a24648 0x000001c01c007000 0x0000003803800e00

def z1542 : W := mkw 0x57bb7d205fdf4811 0x6af76fa40bfbe902 0xd7fffe001fff8000 0x7affffc003fff000

def z1543 : W := mkw 0xf7dfbffff2a04d02 0xbefbf7fffe5409a0 0xffffffffe3e00f86 0x7ffffffffc7c01f0

def z1544 : W := mkw 0xe1dbbecbe0000000 0xbc3b77d97c000000 0x41e3fe01e0000000 0x083c7fc03c000000

def z1545 : W := mkw 0x102440141fff0501 0x0204880283ffe0a0 0xba1c003e1fff8f86 0x57438007c3fff1f0

def z1546 : W := mkw 0xe7dfbfffe0200508 0xbcfbf7fffc0400a1 0xe7ffffffe0000c1c 0xfcfffffffc000183

def z1547 : W := mkw 0x60c3aacbc0000000 0x0c18755978000000 0xe5e3ffcfe0000000 0x7cbc7ff9fc000000

def z1548 : W := mkw 0x066401bc1b206f00 0x00cc803783640de0 0xbffc01fe1fe07f86 0x77ff803fc3fc0ff0

def z1549 : W := mkw 0xe7dfbfffe0200500 0xbcfbf7fffc0400a0 0xe7ffffffe2e00c04 0x7cfffffffc5c0180

def z1550 : W := mkw 0x079f3e16a06585a8 0x20f3e7c2d40cb0b5 0xc7fffe0e01e38382 0x78ffffc1c03c7070

def z1551 : W := mkw 0xd71e353472ed4d1a 0x5ae3c6a68e5da9a3 0x021c303062ec0c1c 0x804386060c5d8183

def z1552 : W := mkw 0x179f3e16b2ed0509 0x22f3e7c2d65da0a1 0xe7fffe3fe2ec0c1c 0xfcffffc7fc5d8183

def z1553 : W := mkw 0x26c3aacb80000000 0x04d8755970000000 0xe7e3ffcf80000000 0x7cfc7ff9f0000000

def z1554 : W := mkw 0xa0c58bff80206f02 0x1418b17ff0040de0 0xede3cfff80007f86 0x7dbc79fff0000ff0

def z1555 : W := mkw 0xe7dfbdfd60000000 0xbcfbf7bfac000000 0x67fff1f1e0000000 0x6cfffe3e3c000000

def z1556 : W := mkw 0x008b3c0000000000 0x2011678000000000 0xc5e3fe0000000000 0x78bc7fc000000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z1,z2,z8,z3,z5]),(0,[z0,z1,z9,z2,z3,z5,z10]),(0,[z0,z11,z1,z2,z3,z5,z10])],[(0,[z0,z12,z1,z2,z3,z5,z13]),(0,[z0,z14,z1,z2,z3,z5,z10]),(0,[z0,z1,z15,z2,z3,z5,z10])],[(0,[z0,z1,z16,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z17]),(0,[z0,z1,z2,z3,z5,z13,z18])],[(0,[z19,z0,z1,z2,z3,z5,z10]),(0,[z20,z0,z1,z2,z3,z5,z13])],[(0,[z21,z0,z22,z2,z3,z5,z10]),(0,[z23,z0,z7,z1,z2,z3,z5]),(0,[z0,z24,z1,z2,z3,z25,z10]),(0,[z0,z1,z2,z3,z5,z26,z10])],[(0,[z27,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z28,z5,z13]),(0,[z0,z29,z29,z1,z2,z3,z5]),(0,[z0,z1,z30,z3,z31,z5,z10]),(0,[z0,z1,z2,z3,z5,z32,z10])],[(1,[z33,z0,z29,z2,z3,z5]),(0,[z34,z0,z1,z2,z3,z5,z10]),(1,[z0,z1,z35,z2,z3,z5]),(0,[z0,z36,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z37,z3,z5,z38]),(0,[z0,z29,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z30,z3,z5,z40])],[(0,[z0,z1,z2,z3,z41,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z42]),(0,[z0,z1,z43,z44,z2,z3,z5])],[(0,[z0,z1,z2,z3,z45,z5,z10]),(0,[z0,z46,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z47,z5,z10]),(0,[z0,z1,z2,z3,z48,z5,z10])],[(0,[z0,z12,z2,z3,z49,z5,z10])],[],[(0,[z0,z50,z1,z2,z3,z5,z10]),(0,[z21,z0,z39,z1,z2,z3,z5]),(0,[z0,z12,z2,z3,z51,z5,z10]),(0,[z0,z1,z2,z3,z52,z5,z10]),(0,[z53,z0,z1,z2,z3,z5,z10])],[(0,[z0,z24,z1,z2,z3,z5,z10])],[(0,[z0,z54,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z37,z3,z5,z55]),(1,[z0,z56,z1,z2,z3,z5]),(0,[z0,z57,z58,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z59,z10])]],
   [[(0,[z60,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z61])],[(0,[z62,z0,z1,z2,z3,z5,z13]),(1,[z0,z63,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z64,z10]),(0,[z0,z65,z1,z2,z3,z5,z10]),(1,[z66,z0,z1,z2,z5,z67])],[(0,[z0,z68,z1,z2,z3,z5,z10])],[(0,[z0,z7,z1,z2,z3,z5,z13])],[(0,[z0,z39,z69,z1,z2,z3,z5]),(0,[z0,z39,z1,z2,z3,z70,z5])],[(0,[z0,z71,z1,z2,z3,z5,z10])],[(0,[z0,z1,z72,z2,z3,z5,z6]),(0,[z0,z39,z1,z2,z3,z5,z73]),(0,[z66,z0,z15,z2,z3,z5,z10])],[(0,[z0,z57,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z74,z5,z10])],[(0,[z0,z75,z1,z2,z3,z5,z10]),(0,[z76,z0,z29,z1,z2,z3,z5]),(0,[z21,z1,z2,z3,z77,z5,z10]),(0,[z0,z1,z2,z3,z78,z79,z10]),(0,[z0,z1,z2,z3,z80,z5,z10]),(0,[z0,z1,z2,z3,z81,z5,z10])],[(0,[z76,z0,z39,z1,z2,z3,z5]),(0,[z0,z39,z1,z2,z30,z3,z5])],[(0,[z20,z0,z1,z2,z3,z5,z82]),(1,[z0,z1,z83,z2,z3,z5]),(0,[z0,z84,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z85,z5,z10])],[(0,[z0,z1,z2,z3,z5,z86,z10]),(0,[z0,z1,z2,z87,z3,z5,z10]),(0,[z0,z88,z1,z2,z3,z5,z10])],[(1,[z0,z89,z2,z3,z5,z10]),(0,[z90,z0,z24,z1,z2,z3,z10]),(0,[z0,z1,z2,z3,z5,z91,z13]),(0,[z0,z1,z2,z3,z5,z92,z10])],[(0,[z0,z1,z2,z3,z25,z93,z10]),(0,[z0,z1,z94,z2,z3,z5,z13]),(0,[z0,z95,z2,z8,z3,z5,z10]),(0,[z0,z95,z2,z3,z51,z5,z10]),(1,[z96,z0,z1,z31,z5,z10]),(0,[z0,z1,z2,z3,z80,z5,z97])],[(1,[z0,z1,z2,z3,z98,z5])],[(0,[z90,z1,z2,z3,z5,z78,z10]),(1,[z0,z1,z2,z3,z5,z13]),(0,[z0,z57,z1,z2,z3,z5,z6]),(0,[z0,z99,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z100,z5,z10]),(0,[z0,z39,z1,z2,z3,z5,z67])]],
   [[(0,[z101,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z102,z10]),(0,[z0,z1,z2,z3,z25,z5,z13]),(0,[z0,z103,z1,z2,z3,z5,z10])],[(0,[z0,z39,z1,z2,z3,z5,z78])],[(0,[z0,z12,z1,z2,z3,z5,z10]),(0,[z0,z29,z1,z94,z2,z3,z5])],[(0,[z104,z0,z95,z2,z3,z5,z10]),(0,[z0,z105,z1,z2,z3,z5,z10]),(0,[z0,z24,z1,z2,z3,z79,z10])],[(0,[z0,z106,z69,z1,z2,z3,z5]),(0,[z107,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z108,z10]),(0,[z109,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z110])],[(0,[z20,z0,z1,z2,z3,z5,z10]),(0,[z111,z0,z29,z1,z2,z3,z5]),(0,[z0,z29,z2,z3,z5,z10,z112]),(0,[z0,z1,z2,z3,z113,z5,z10]),(0,[z114,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z44,z2,z3,z115,z5]),(0,[z111,z0,z39,z1,z2,z3,z5])],[(0,[z0,z1,z2,z116,z3,z5,z10]),(0,[z0,z29,z1,z2,z117,z3,z5]),(0,[z0,z1,z2,z3,z28,z5,z10]),(1,[z0,z1,z44,z3,z5,z118])],[(1,[z0,z1,z2,z3,z119,z10]),(1,[z0,z1,z2,z3,z5,z120]),(0,[z0,z121,z1,z2,z3,z5,z10])],[(0,[z0,z36,z1,z2,z3,z5,z13]),(1,[z0,z2,z3,z5,z122,z13]),(0,[z0,z123,z39,z1,z2,z3,z5]),(0,[z0,z124,z1,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z80,z5]),(0,[z0,z1,z2,z3,z5,z125,z10])],[(1,[z0,z1,z2,z3,z5,z126]),(0,[z0,z39,z1,z2,z3,z5,z61]),(0,[z0,z1,z2,z3,z127,z5,z10])],[(0,[z0,z1,z2,z30,z3,z128,z10])],[(1,[z0,z1,z2,z3,z5,z129]),(0,[z0,z1,z2,z130,z3,z5,z10]),(1,[z0,z131,z1,z2,z3,z5])],[],[(0,[z0,z1,z2,z3,z5,z6,z13]),(0,[z0,z24,z1,z2,z3,z132,z10])],[(0,[z109,z0,z7,z1,z2,z3,z5])]],
   [[(0,[z20,z0,z7,z1,z2,z3,z5]),(0,[z0,z1,z2,z133,z3,z5,z10]),(1,[z0,z29,z134,z2,z3,z5]),(1,[z0,z2,z3,z5,z135,z10])],[(0,[z136,z0,z1,z2,z3,z5,z10]),(0,[z96,z0,z1,z44,z2,z3,z5]),(1,[z0,z137,z1,z2,z3,z5])],[(0,[z0,z7,z138,z1,z2,z3,z5]),(0,[z0,z139,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z140,z5,z73]),(0,[z0,z1,z2,z3,z5,z141,z10]),(0,[z0,z142,z1,z2,z3,z5,z10]),(0,[z0,z2,z3,z5,z135,z132,z10])],[],[(1,[z0,z1,z2,z3,z5,z82]),(0,[z143,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z128,z10])],[(0,[z0,z1,z95,z2,z3,z5,z13]),(0,[z0,z1,z2,z144,z3,z5,z10]),(0,[z0,z145,z1,z2,z3,z5,z10]),(0,[z0,z1,z146,z2,z3,z5,z10])],[(0,[z0,z29,z1,z2,z3,z5,z112]),(0,[z0,z1,z2,z3,z147,z5,z10])],[(0,[z0,z29,z1,z148,z2,z3,z5]),(0,[z0,z1,z2,z149,z3,z5,z10]),(0,[z0,z1,z2,z3,z93,z5,z6]),(0,[z0,z1,z94,z30,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z150,z10]),(1,[z0,z39,z1,z44,z3,z5]),(1,[z0,z151,z2,z3,z5,z10])],[(0,[z96,z0,z1,z2,z3,z5,z6]),(0,[z0,z29,z134,z1,z2,z3,z5]),(0,[z0,z39,z152,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z80,z5,z13]),(0,[z0,z1,z2,z3,z5,z153,z13])],[(1,[z0,z1,z2,z3,z5,z154]),(0,[z155,z0,z1,z2,z3,z5,z6]),(0,[z156,z0,z7,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z40,z10])],[(0,[z0,z1,z2,z3,z5,z157,z10]),(0,[z62,z0,z7,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z91,z10]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z158,z5,z10])],[(1,[z0,z138,z1,z2,z3,z5]),(0,[z0,z1,z94,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z31,z5])],[(0,[z0,z7,z7,z1,z2,z3,z5])]],
   [[(1,[z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z55,z10]),(0,[z0,z7,z2,z3,z5,z159,z10]),(0,[z0,z137,z1,z2,z3,z5,z10])],[(0,[z27,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z13,z160]),(0,[z0,z1,z2,z3,z25,z5,z10])],[(0,[z0,z1,z2,z3,z5,z161,z10]),(0,[z0,z1,z2,z3,z5,z162,z10])],[(0,[z0,z1,z2,z3,z163,z5,z10]),(0,[z0,z1,z2,z164,z3,z5,z10]),(0,[z90,z0,z29,z1,z2,z3,z5]),(0,[z165,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z70,z10,z166])],[(0,[z90,z0,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z167,z6]),(0,[z0,z1,z44,z2,z3,z5,z159]),(0,[z168,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z49,z5,z13]),(1,[z0,z1,z2,z3,z5,z97]),(0,[z0,z1,z2,z3,z5,z169,z10])],[(0,[z0,z1,z2,z170,z3,z5,z13]),(0,[z0,z1,z171,z2,z3,z5,z10]),(0,[z0,z1,z2,z172,z3,z5,z10]),(0,[z0,z1,z173,z2,z3,z5,z10])],[(0,[z0,z1,z2,z8,z3,z5,z13]),(0,[z0,z1,z2,z3,z51,z5,z13]),(0,[z0,z36,z134,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z174,z5,z10]),(0,[z0,z1,z2,z175,z3,z5,z10])],[(0,[z0,z39,z1,z2,z3,z49,z5]),(0,[z0,z39,z176,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z177,z5,z10]),(1,[z0,z1,z2,z3,z178,z5])],[(0,[z104,z0,z1,z2,z3,z5,z10]),(0,[z0,z179,z1,z2,z170,z3,z5]),(1,[z0,z2,z3,z5,z122,z10]),(0,[z0,z1,z2,z3,z5,z10,z180])],[(0,[z0,z181,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z182]),(0,[z0,z183,z1,z2,z3,z5,z10])],[(0,[z0,z184,z1,z185,z2,z3,z5])],[(0,[z90,z23,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z186,z5,z6])],[(0,[z0,z187,z1,z2,z3,z5,z10]),(0,[z21,z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z2,z37,z3,z5,z6]),(0,[z0,z1,z2,z3,z188,z5,z10]),(0,[z0,z39,z1,z2,z3,z51,z5]),(0,[z0,z1,z2,z3,z189,z5,z10])],[(0,[z0,z1,z2,z190,z170,z5,z10]),(0,[z21,z0,z1,z2,z3,z5,z191]),(0,[z0,z1,z2,z3,z5,z6,z10]),(0,[z192,z0,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z29,z69,z1,z2,z3,z5]),(0,[z0,z193,z123,z1,z2,z3,z5]),(0,[z0,z39,z1,z44,z3,z5,z10]),(0,[z66,z0,z1,z2,z3,z5,z10])],[(1,[z33,z148,z2,z3,z5,z10])],[(0,[z0,z1,z44,z2,z170,z3,z5]),(0,[z0,z194,z1,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z73]),(0,[z0,z195,z1,z2,z3,z5,z10])],[(1,[z0,z1,z72,z3,z80,z10]),(0,[z0,z1,z196,z44,z2,z3,z5])],[(0,[z1,z2,z117,z3,z77,z5,z10]),(0,[z23,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z197,z5,z10]),(0,[z0,z198,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z4,z5])],[(0,[z0,z36,z7,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z30,z3,z5]),(0,[z0,z1,z199,z2,z3,z5,z10])],[],[(0,[z104,z0,z29,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z31,z5,z13]),(0,[z0,z1,z95,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z5,z200]),(0,[z0,z39,z1,z2,z3,z5,z79])],[(0,[z0,z1,z2,z3,z201,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z202]),(0,[z0,z1,z2,z3,z203,z5,z10]),(0,[z0,z7,z1,z2,z3,z5,z159]),(0,[z0,z1,z2,z3,z5,z10,z204])],[(0,[z0,z12,z1,z2,z3,z73,z10]),(0,[z0,z152,z1,z2,z3,z4,z10])],[(0,[z0,z1,z2,z3,z5,z205,z10])],[(0,[z0,z1,z2,z3,z5,z153,z10]),(0,[z0,z1,z196,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z206,z5,z10]),(0,[z0,z1,z207,z2,z3,z5,z10]),(0,[z0,z24,z7,z1,z2,z3,z5])],[(0,[z23,z0,z1,z2,z3,z5,z6]),(0,[z143,z27,z1,z2,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z208]),(0,[z0,z1,z209,z2,z3,z5,z10]),(0,[z0,z1,z210,z2,z3,z5,z10]),(0,[z27,z1,z2,z3,z5,z10,z13]),(0,[z0,z211,z1,z2,z3,z5,z10]),(0,[z0,z134,z2,z37,z3,z5,z10]),(0,[z0,z1,z2,z3,z212,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z166])],[(0,[z0,z1,z2,z3,z213,z5,z10]),(0,[z214,z0,z1,z2,z3,z5,z10]),(0,[z215,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z216,z10])],[(0,[z0,z29,z7,z2,z3,z5,z10])]],
   [[(0,[z0,z134,z148,z2,z3,z5,z10]),(0,[z0,z1,z217,z2,z3,z5,z10]),(0,[z0,z218,z1,z2,z3,z5,z10]),(0,[z219,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z98,z5,z10]),(0,[z0,z220,z1,z2,z3,z5,z10]),(0,[z221,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z222,z3,z5,z10])],[(0,[z0,z223,z1,z2,z3,z5,z10]),(0,[z0,z12,z134,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z224,z5,z10])],[(0,[z33,z0,z148,z2,z3,z5,z10]),(0,[z0,z225,z1,z2,z3,z5,z10]),(0,[z27,z0,z39,z1,z2,z3,z5])],[(0,[z0,z226,z1,z2,z3,z5,z73]),(0,[z0,z227,z29,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z3,z5,z228])],[(0,[z229,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z230,z5,z10]),(0,[z0,z29,z1,z2,z3,z80,z5])],[(0,[z0,z7,z1,z2,z170,z3,z5]),(0,[z0,z231,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z49,z5,z10]),(0,[z0,z63,z1,z2,z3,z49,z5]),(0,[z0,z2,z3,z5,z159,z10,z112])],[(0,[z104,z0,z1,z2,z3,z5,z208]),(0,[z0,z1,z2,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z122,z13]),(0,[z232,z0,z1,z2,z3,z5,z10]),(0,[z0,z233,z1,z2,z3,z5,z10]),(0,[z0,z152,z1,z2,z3,z5,z166])],[(1,[z0,z234,z1,z2,z3,z5]),(0,[z0,z1,z2,z8,z3,z5,z10]),(0,[z0,z1,z2,z3,z51,z5,z10]),(1,[z0,z99,z2,z3,z5,z10]),(0,[z0,z1,z44,z3,z5,z10,z118])],[(0,[z0,z69,z2,z3,z49,z5,z10]),(0,[z0,z1,z2,z3,z5,z235,z10]),(1,[z0,z57,z1,z2,z79,z10])],[(0,[z236,z0,z1,z2,z3,z5,z10])],[(0,[z0,z123,z29,z1,z2,z3,z5]),(0,[z0,z237,z1,z2,z3,z5,z10]),(0,[z0,z1,z238,z2,z3,z5,z132])],[(0,[z104,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z13,z239]),(0,[z0,z240,z1,z44,z2,z3,z5])],[],[(0,[z241,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z135,z10])],[(0,[z0,z1,z2,z3,z5,z242,z10]),(0,[z243,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z244])]],
   [[(0,[z0,z12,z7,z1,z2,z3,z5])],[(1,[z0,z179,z1,z2,z3,z5]),(0,[z0,z1,z2,z245,z3,z5,z6]),(0,[z0,z152,z1,z2,z245,z3,z5])],[(0,[z246,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z247,z2,z3,z5,z10]),(0,[z66,z0,z1,z2,z3,z5,z13]),(0,[z0,z7,z1,z2,z3,z248,z5])],[(0,[z0,z1,z2,z3,z249,z5,z10])],[(0,[z0,z240,z1,z2,z3,z5,z6]),(0,[z250,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z251,z3,z5,z10]),(0,[z0,z29,z152,z1,z2,z3,z5]),(0,[z0,z24,z1,z3,z5,z132,z10]),(0,[z0,z57,z1,z2,z3,z5,z252])],[(0,[z0,z1,z2,z3,z5,z253,z10]),(0,[z23,z0,z1,z2,z3,z5,z254]),(0,[z0,z1,z151,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z13,z118]),(0,[z255,z0,z1,z2,z3,z5,z10]),(1,[z0,z256,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z257,z5,z10]),(0,[z0,z39,z1,z2,z3,z5,z132]),(0,[z0,z1,z2,z3,z258,z5,z10]),(0,[z0,z39,z1,z2,z3,z5,z166])],[(0,[z0,z184,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z31,z5,z10]),(0,[z0,z259,z1,z2,z3,z5,z10]),(0,[z0,z260,z39,z1,z2,z3,z5])],[],[(0,[z261,z0,z1,z2,z3,z5,z10]),(0,[z62,z0,z1,z2,z3,z5,z262]),(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z263,z3,z5,z10]),(0,[z0,z1,z44,z44,z2,z3,z5])],[(0,[z0,z264,z1,z2,z3,z5,z10]),(0,[z0,z57,z29,z1,z2,z3,z5]),(0,[z0,z265,z39,z1,z2,z3,z5])],[(0,[z0,z39,z1,z185,z2,z3,z5]),(0,[z0,z1,z2,z266,z3,z5,z10]),(0,[z0,z36,z1,z2,z37,z5,z10]),(0,[z0,z1,z2,z3,z5,z267,z10]),(0,[z0,z57,z39,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z268,z10]),(0,[z0,z1,z44,z72,z2,z3,z5])],[(0,[z0,z1,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z269,z5,z10])]],
   [[(0,[z0,z1,z44,z2,z3,z5,z118]),(0,[z0,z1,z2,z270,z3,z5,z10])],[(0,[z0,z69,z1,z2,z3,z5,z10]),(0,[z271,z0,z1,z2,z3,z5,z10]),(0,[z272,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z119,z5,z10]),(0,[z0,z273,z1,z2,z3,z5,z10]),(0,[z0,z1,z274,z2,z8,z3,z10]),(0,[z0,z39,z1,z2,z245,z3,z5])],[(0,[z0,z1,z44,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z10,z275]),(0,[z0,z22,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z276,z10])],[(1,[z0,z277,z2,z3,z5,z10]),(0,[z278,z0,z1,z2,z3,z5,z10])],[(0,[z0,z225,z1,z2,z3,z5,z13]),(0,[z0,z29,z1,z2,z3,z49,z5]),(0,[z0,z29,z176,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z279,z10])],[(0,[z33,z0,z123,z2,z3,z5,z10]),(0,[z1,z2,z3,z5,z6,z10,z13])],[(0,[z0,z1,z280,z2,z3,z5,z10]),(0,[z20,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z281,z2,z3,z5,z10]),(0,[z0,z193,z39,z1,z2,z3,z5]),(0,[z282,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z122,z10]),(0,[z0,z1,z2,z283,z3,z5,z10])],[],[(0,[z0,z284,z39,z1,z2,z3,z5])],[],[(0,[z0,z1,z148,z44,z2,z3,z5]),(0,[z62,z0,z1,z44,z2,z3,z5]),(0,[z285,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z286,z10]),(0,[z0,z39,z1,z2,z283,z3,z5])],[(0,[z0,z287,z1,z2,z3,z5,z10]),(0,[z0,z99,z2,z3,z5,z132,z10]),(0,[z0,z1,z2,z3,z178,z80,z5])],[(0,[z0,z288,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z13]),(1,[z0,z7,z1,z2,z3,z5]),(0,[z0,z7,z1,z44,z2,z3,z5])],[(0,[z0,z1,z209,z2,z170,z3,z5])]],
   [[(0,[z0,z1,z44,z2,z3,z93,z5]),(0,[z0,z1,z44,z95,z2,z3,z5]),(0,[z289,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z25,z5,z79,z10])],[(0,[z290,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z78,z13]),(0,[z23,z0,z24,z1,z2,z3,z10]),(0,[z0,z7,z1,z72,z2,z3,z5])],[(1,[z0,z58,z2,z3,z5,z10]),(0,[z291,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z292,z25,z5,z10]),(0,[z293,z0,z1,z2,z3,z5,z10])],[(0,[z21,z0,z1,z294,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z79]),(0,[z0,z29,z1,z2,z3,z70,z5]),(0,[z0,z1,z2,z3,z5,z295,z10])],[(0,[z0,z1,z148,z2,z3,z5,z6]),(0,[z296,z0,z1,z2,z3,z5,z10]),(0,[z62,z0,z1,z2,z3,z5,z6]),(0,[z0,z7,z1,z2,z3,z5,z118])],[(0,[z0,z297,z1,z2,z3,z5,z10])],[(0,[z0,z7,z1,z2,z3,z5,z6]),(0,[z298,z0,z1,z2,z3,z5,z10]),(0,[z96,z0,z39,z1,z2,z3,z5])],[(0,[z0,z1,z299,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z120])],[(0,[z104,z0,z7,z1,z2,z3,z5]),(0,[z0,z300,z1,z2,z3,z5,z10]),(0,[z0,z152,z1,z2,z3,z5,z13]),(0,[z0,z39,z56,z1,z2,z3,z5])],[(0,[z104,z0,z2,z3,z5,z159,z10]),(0,[z0,z1,z2,z3,z5,z10,z126]),(0,[z0,z184,z1,z2,z3,z5,z10]),(0,[z0,z1,z301,z2,z3,z5,z10]),(1,[z1,z2,z3,z5,z6,z13]),(0,[z143,z0,z29,z1,z2,z3,z5])],[(1,[z104,z69,z2,z3,z5,z10]),(0,[z143,z0,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z302,z10])],[(0,[z20,z0,z1,z2,z3,z5,z303]),(0,[z0,z1,z2,z3,z5,z10,z18]),(0,[z0,z134,z1,z2,z49,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z304])],[],[(0,[z305,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z89,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z306,z10]),(0,[z0,z1,z2,z3,z5,z10,z307]),(0,[z0,z1,z2,z308,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z38]),(0,[z0,z29,z145,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z3,z5,z67]),(0,[z66,z0,z7,z1,z2,z3,z5]),(0,[z0,z1,z2,z309,z3,z5,z10])],[(0,[z0,z1,z2,z310,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z157,z6]),(0,[z311,z0,z1,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z77,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z78]),(0,[z0,z1,z94,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z312,z5,z10]),(0,[z66,z0,z1,z2,z245,z5,z10])],[(0,[z0,z1,z2,z3,z313,z5,z10]),(0,[z104,z0,z69,z2,z3,z5,z10]),(0,[z21,z0,z1,z2,z3,z5,z17]),(0,[z0,z314,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z315,z5,z10])],[(0,[z21,z0,z1,z2,z3,z102,z10]),(0,[z0,z1,z2,z3,z70,z5,z166])],[(0,[z0,z69,z1,z2,z3,z5,z13]),(0,[z0,z1,z316,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z25,z5,z6])],[(0,[z0,z317,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z318]),(0,[z0,z1,z2,z3,z5,z10,z82]),(1,[z0,z319,z2,z3,z5,z10]),(0,[z0,z7,z1,z2,z3,z93,z5]),(0,[z0,z320,z1,z2,z3,z5,z10]),(0,[z0,z7,z1,z95,z2,z3,z5]),(0,[z0,z36,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z321,z10])],[(0,[z90,z0,z1,z2,z3,z5,z322]),(0,[z27,z0,z29,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z70,z166])],[(0,[z323,z0,z1,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z37,z3,z5]),(1,[z0,z1,z2,z3,z5,z55])],[(0,[z0,z1,z2,z3,z324,z5,z10])],[(0,[z0,z1,z2,z325,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z5,z13]),(0,[z326,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z67,z166])],[(0,[z0,z29,z1,z2,z3,z5,z61])],[(0,[z327,z0,z1,z2,z3,z5,z10]),(0,[z0,z24,z1,z44,z2,z3,z5])],[(0,[z0,z7,z1,z2,z3,z4,z5]),(0,[z328,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z329,z3,z5,z10]),(0,[z330,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z159,z13]),(0,[z0,z36,z1,z2,z3,z5,z6]),(0,[z0,z1,z44,z2,z3,z25,z5])],[(0,[z0,z176,z95,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z331,z5,z10]),(0,[z60,z0,z1,z44,z2,z3,z5])],[(0,[z0,z12,z176,z2,z3,z5,z10])],[(0,[z0,z1,z332,z2,z170,z3,z10]),(0,[z0,z1,z2,z3,z5,z10,z10]),(0,[z0,z1,z2,z3,z5,z6,z118])]],
   [[],[(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z3,z333,z5,z10]),(0,[z0,z225,z7,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z78,z10]),(0,[z0,z24,z1,z2,z3,z5,z6]),(1,[z0,z134,z2,z37,z5,z10])],[(0,[z0,z1,z2,z334,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z132]),(0,[z0,z29,z1,z2,z3,z5,z166])],[(0,[z0,z335,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z140,z5]),(0,[z0,z1,z2,z3,z5,z10,z97])],[(0,[z336,z0,z1,z2,z3,z5,z10]),(0,[z0,z234,z1,z2,z3,z5,z13])],[(1,[z0,z1,z2,z3,z5,z303]),(0,[z0,z24,z176,z1,z2,z3,z10])],[(0,[z0,z337,z1,z2,z3,z5,z10]),(0,[z76,z0,z1,z170,z3,z5,z10]),(0,[z0,z211,z1,z44,z2,z3,z5])],[(0,[z338,z0,z1,z2,z3,z5,z10]),(0,[z0,z29,z1,z185,z2,z3,z5]),(0,[z23,z0,z29,z1,z2,z3,z5]),(0,[z0,z7,z240,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z339,z5,z10]),(0,[z23,z0,z39,z1,z2,z3,z5]),(0,[z0,z152,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z340,z10])],[(0,[z0,z1,z2,z3,z3,z5,z10]),(0,[z0,z1,z2,z341,z3,z5,z10])],[(0,[z0,z1,z2,z3,z342,z5,z10]),(0,[z0,z123,z1,z3,z80,z5,z10]),(0,[z343,z0,z1,z2,z3,z5,z10]),(0,[z344,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z292,z3,z5])],[(0,[z0,z1,z2,z3,z5,z10,z345]),(0,[z0,z1,z2,z3,z248,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z346])],[(0,[z0,z1,z2,z3,z80,z5,z6]),(0,[z0,z29,z1,z2,z3,z31,z5]),(0,[z0,z29,z1,z2,z245,z3,z5]),(0,[z0,z1,z2,z3,z5,z347,z10])],[(0,[z0,z1,z2,z3,z348,z5,z10])],[(1,[z0,z106,z1,z2,z3,z5]),(0,[z21,z0,z1,z94,z2,z5,z10]),(0,[z0,z349,z1,z2,z3,z5,z10]),(0,[z0,z12,z1,z44,z2,z3,z5])]],
   [[(1,[z0,z176,z2,z3,z73,z10]),(0,[z0,z7,z1,z2,z3,z25,z5])],[(0,[z0,z2,z3,z49,z5,z159,z10]),(0,[z0,z1,z2,z30,z3,z5,z10]),(0,[z0,z1,z350,z2,z3,z5,z10])],[(0,[z20,z0,z1,z185,z3,z5,z10]),(0,[z20,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z77,z5,z13]),(0,[z351,z0,z1,z2,z3,z5,z10]),(0,[z0,z352,z1,z2,z3,z5,z10]),(0,[z0,z1,z72,z3,z80,z5,z10])],[(0,[z0,z1,z353,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z354])],[(0,[z0,z1,z355,z2,z3,z5,z10]),(0,[z21,z0,z1,z2,z117,z5,z10]),(1,[z143,z1,z2,z3,z5,z6]),(0,[z0,z123,z1,z95,z3,z5,z10]),(0,[z0,z152,z7,z1,z2,z3,z5])],[(1,[z0,z1,z332,z2,z3,z10]),(0,[z0,z356,z1,z2,z3,z5,z10]),(0,[z0,z357,z29,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z358,z5,z10]),(0,[z0,z1,z2,z3,z5,z61,z166])],[(0,[z76,z20,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z2,z3,z5,z10]),(0,[z0,z359,z2,z170,z3,z5,z10]),(0,[z0,z360,z1,z2,z3,z5,z10]),(0,[z0,z12,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z361,z3,z5,z10]),(0,[z362,z0,z1,z2,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z86]),(0,[z363,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z49,z5,z6]),(0,[z0,z134,z95,z2,z3,z5,z10])],[(0,[z33,z1,z148,z2,z3,z5,z10]),(0,[z0,z364,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z170,z3,z5,z6]),(0,[z0,z1,z2,z3,z365,z5,z10]),(0,[z0,z1,z2,z3,z5,z366,z10]),(0,[z0,z39,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z367,z10])],[(0,[z0,z1,z2,z3,z5,z10,z38]),(0,[z368,z0,z1,z2,z3,z5,z10])],[(0,[z33,z0,z95,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z369,z10]),(1,[z0,z1,z2,z3,z5,z262]),(0,[z0,z1,z2,z3,z5,z5,z10])],[(0,[z0,z1,z2,z370,z3,z5,z10]),(0,[z0,z1,z2,z3,z371,z5,z10]),(0,[z0,z39,z1,z9,z2,z3,z5])],[(1,[z0,z218,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z3,z51,z5]),(0,[z0,z1,z2,z3,z5,z159,z10])],[(0,[z372,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z373,z3,z5,z10]),(0,[z374,z0,z1,z2,z3,z5,z10])],[(0,[z0,z39,z1,z2,z3,z77,z5]),(0,[z0,z7,z1,z2,z292,z3,z5])]],
   [[(1,[z0,z36,z2,z49,z5,z10]),(0,[z0,z7,z1,z2,z3,z5,z346]),(0,[z0,z1,z375,z2,z3,z5,z10]),(0,[z0,z1,z376,z2,z3,z5,z10])],[(0,[z33,z0,z1,z2,z3,z5,z13])],[(0,[z0,z377,z1,z148,z2,z3,z5]),(0,[z0,z378,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z379,z3,z5]),(0,[z380,z0,z1,z2,z3,z5,z10])],[(1,[z76,z1,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z70,z5,z13]),(0,[z66,z0,z1,z2,z5,z67,z10])],[(0,[z0,z1,z2,z381,z3,z5,z10]),(0,[z0,z39,z7,z1,z2,z3,z5]),(0,[z0,z1,z44,z2,z3,z5,z382])],[(0,[z383,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z384,z5,z10]),(0,[z0,z1,z2,z3,z5,z385,z10]),(0,[z0,z1,z2,z133,z3,z5,z6]),(0,[z0,z1,z386,z2,z3,z5,z10]),(0,[z0,z7,z1,z2,z3,z371,z5])],[(0,[z0,z234,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z382,z10])],[(0,[z21,z96,z0,z1,z2,z5,z10]),(0,[z387,z0,z1,z2,z3,z5,z10]),(0,[z0,z388,z1,z2,z3,z5,z10])],[(0,[z0,z39,z1,z2,z8,z3,z5]),(0,[z0,z1,z2,z3,z389,z5,z10]),(0,[z0,z390,z1,z2,z3,z5,z10]),(0,[z96,z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z391,z31,z5])],[(0,[z0,z106,z1,z2,z3,z5,z10]),(0,[z0,z24,z1,z2,z3,z80,z10])],[(0,[z0,z1,z2,z3,z5,z392,z10])],[(0,[z0,z1,z94,z185,z3,z5,z10]),(0,[z393,z0,z1,z2,z3,z5,z10])],[(0,[z394,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z395,z2,z3,z5,z10]),(0,[z0,z131,z1,z2,z3,z5,z10])],[(1,[z0,z1,z44,z2,z3,z5])],[(0,[z0,z396,z1,z2,z3,z5,z10]),(0,[z397,z0,z1,z2,z3,z5,z10]),(0,[z398,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z399,z5,z10]),(0,[z0,z1,z2,z3,z5,z400,z79])]],
   [[(0,[z0,z176,z1,z72,z2,z3,z10]),(0,[z0,z29,z1,z2,z3,z257,z5]),(0,[z0,z1,z44,z375,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z401,z10])],[(0,[z0,z1,z2,z3,z5,z73,z13]),(0,[z0,z1,z2,z3,z5,z79,z10])],[(0,[z0,z1,z319,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z37,z3,z5])],[(0,[z0,z1,z2,z3,z5,z208,z10]),(1,[z27,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z30,z3,z5,z13]),(0,[z0,z390,z7,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z402,z5,z10])],[(0,[z20,z0,z39,z1,z2,z3,z5]),(0,[z0,z403,z1,z2,z3,z5,z10]),(0,[z0,z240,z1,z2,z3,z5,z404])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z211,z123,z1,z2,z3,z5]),(0,[z0,z1,z2,z405,z3,z5,z10])],[(1,[z0,z406,z1,z2,z3,z10]),(0,[z0,z234,z2,z3,z5,z10,z13]),(0,[z0,z63,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z140,z5,z10])],[(0,[z104,z0,z1,z44,z2,z3,z5])],[(0,[z0,z1,z407,z2,z3,z5,z10])],[(0,[z0,z1,z408,z2,z3,z5,z10]),(0,[z0,z409,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z4,z70,z5])],[(0,[z104,z33,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z410])],[],[(0,[z0,z1,z2,z3,z411,z5,z10])],[(0,[z412,z0,z1,z2,z3,z5,z10]),(0,[z0,z29,z2,z3,z49,z5,z10]),(1,[z0,z1,z2,z3,z5,z413]),(0,[z66,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z3,z5,z346,z10,z118]),(0,[z0,z1,z2,z3,z4,z10,z166])],[(0,[z0,z414,z1,z2,z3,z5,z10])],[(0,[z104,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z415,z5,z10]),(0,[z0,z134,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z416,z10])]],
   [[(0,[z62,z0,z29,z1,z2,z3,z5]),(0,[z0,z417,z1,z2,z3,z5,z10]),(0,[z0,z57,z1,z2,z292,z5,z10])],[(0,[z62,z0,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z346,z13]),(0,[z0,z1,z2,z3,z5,z418,z10])],[(0,[z33,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z44,z2,z2,z3,z5]),(0,[z0,z1,z2,z379,z3,z5,z10])],[(0,[z0,z1,z2,z3,z4,z5,z67]),(0,[z0,z1,z2,z3,z70,z5,z10])],[(0,[z66,z0,z1,z2,z3,z5,z6])],[(0,[z104,z69,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z419,z5,z10]),(0,[z0,z420,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z421,z5,z10]),(0,[z0,z176,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z422,z3,z5,z10]),(0,[z0,z2,z3,z49,z5,z73,z10])],[(0,[z0,z1,z294,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z423])],[(0,[z424,z0,z1,z2,z3,z5,z10]),(1,[z0,z22,z2,z3,z5,z10])],[(0,[z0,z1,z2,z425,z3,z5,z10]),(0,[z0,z7,z1,z2,z3,z5,z92]),(0,[z426,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z427]),(0,[z0,z123,z240,z2,z3,z5,z10]),(0,[z0,z1,z44,z94,z2,z3,z5]),(0,[z0,z1,z428,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z67,z10])],[(0,[z0,z1,z2,z3,z5,z429,z10]),(0,[z0,z39,z1,z2,z170,z3,z5])],[(0,[z0,z1,z95,z2,z3,z5,z6]),(0,[z0,z430,z1,z2,z3,z5,z10]),(1,[z0,z24,z1,z3,z132,z10])],[(0,[z33,z0,z7,z1,z2,z3,z5]),(0,[z0,z431,z29,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z432,z10])],[(0,[z33,z0,z29,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z117,z3,z5]),(1,[z0,z1,z2,z3,z5,z254]),(0,[z0,z1,z2,z3,z4,z5,z61])]],
   [[(0,[z0,z433,z1,z2,z3,z5,z10]),(0,[z0,z7,z1,z2,z434,z3,z5]),(0,[z0,z7,z1,z2,z435,z3,z5]),(0,[z0,z1,z238,z2,z3,z5,z10]),(1,[z0,z1,z375,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z436,z10]),(0,[z76,z0,z1,z2,z3,z5,z126]),(0,[z0,z1,z2,z3,z399,z5,z13]),(0,[z0,z1,z2,z3,z5,z437,z10]),(1,[z0,z54,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z438,z5,z10]),(0,[z0,z1,z2,z3,z5,z73,z10]),(0,[z0,z439,z1,z2,z3,z5,z10])],[(0,[z76,z0,z1,z2,z3,z5,z129]),(0,[z0,z1,z2,z3,z5,z79,z13]),(0,[z0,z440,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z441,z5,z10])],[(0,[z442,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z239]),(0,[z0,z1,z2,z3,z443,z5,z10]),(0,[z0,z444,z1,z2,z3,z5,z10])],[(0,[z0,z218,z1,z2,z3,z5,z6]),(0,[z0,z24,z12,z1,z2,z3,z10]),(1,[z0,z29,z7,z2,z3,z5]),(0,[z0,z29,z1,z2,z3,z5,z10])],[(0,[z69,z1,z148,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z13,z112]),(0,[z0,z445,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z446,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z447,z10])],[(0,[z0,z1,z2,z448,z3,z5,z10]),(0,[z0,z36,z29,z1,z2,z3,z5])],[(0,[z0,z36,z39,z1,z2,z3,z5])],[],[(0,[z449,z0,z1,z2,z3,z5,z10]),(0,[z21,z62,z1,z2,z3,z5,z10]),(1,[z21,z1,z2,z77,z5,z10]),(0,[z0,z29,z1,z2,z3,z77,z5]),(0,[z0,z123,z1,z8,z3,z5,z10]),(0,[z0,z176,z1,z2,z3,z73,z10]),(0,[z0,z450,z1,z2,z3,z5,z10]),(1,[z0,z39,z1,z3,z5,z346]),(0,[z0,z1,z2,z3,z5,z451,z10])],[(0,[z0,z452,z1,z2,z3,z5,z10]),(0,[z243,z0,z1,z44,z2,z3,z5])],[(0,[z0,z1,z185,z3,z31,z5,z10]),(0,[z0,z1,z2,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z51,z5,z6]),(0,[z0,z453,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z132,z13]),(0,[z0,z24,z29,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z454,z5,z10]),(0,[z0,z123,z2,z3,z49,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z112]),(0,[z0,z455,z1,z2,z3,z5,z10]),(0,[z0,z24,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z118])]],
   [[(0,[z0,z1,z2,z3,z456,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z457]),(0,[z0,z458,z1,z2,z3,z5,z10])],[(0,[z0,z1,z332,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z459,z10]),(0,[z0,z134,z1,z2,z3,z5,z13]),(0,[z0,z123,z2,z3,z51,z5,z10])],[(0,[z0,z1,z2,z3,z5,z346,z10]),(0,[z0,z1,z2,z3,z5,z460,z10]),(0,[z0,z461,z1,z2,z3,z5,z10])],[(0,[z0,z7,z1,z2,z117,z3,z5]),(1,[z0,z1,z3,z462,z5,z10]),(0,[z0,z12,z1,z2,z3,z51,z10]),(0,[z0,z1,z2,z3,z115,z5,z10]),(0,[z0,z1,z2,z3,z463,z5,z10])],[(0,[z0,z1,z2,z3,z5,z78,z6]),(0,[z0,z29,z1,z2,z8,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z464]),(0,[z0,z39,z1,z3,z5,z346,z10])],[(0,[z0,z256,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z51,z5,z413]),(0,[z0,z1,z2,z3,z5,z10,z465])],[],[(0,[z76,z0,z1,z2,z3,z5,z10]),(0,[z466,z0,z1,z2,z3,z5,z10]),(0,[z0,z176,z1,z2,z3,z5,z10]),(0,[z0,z226,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z189,z10])],[(1,[z0,z467,z1,z2,z3,z5]),(0,[z468,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z185,z2,z3,z5,z10])],[],[(0,[z0,z211,z29,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z469,z3,z5])],[(0,[z0,z1,z470,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z160]),(0,[z0,z1,z2,z3,z5,z67,z13]),(0,[z471,z0,z1,z2,z3,z5,z10])],[(0,[z1,z185,z2,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z31,z5,z6]),(0,[z0,z1,z2,z3,z5,z472,z10]),(0,[z0,z473,z1,z2,z3,z5,z10])],[(0,[z0,z69,z1,z44,z2,z3,z5]),(0,[z474,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z475,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z476,z10]),(1,[z0,z1,z2,z3,z5,z477])]],
   [[(0,[z0,z1,z2,z3,z5,z154,z10]),(0,[z0,z1,z2,z3,z391,z5,z10])],[(0,[z0,z359,z1,z2,z3,z5,z10]),(0,[z0,z406,z1,z2,z170,z3,z10]),(0,[z0,z1,z478,z2,z3,z5,z10]),(0,[z0,z2,z37,z3,z49,z5,z10])],[(0,[z1,z2,z3,z93,z5,z78,z10]),(0,[z0,z29,z1,z83,z2,z3,z5]),(0,[z0,z1,z44,z2,z3,z479,z5])],[(0,[z0,z1,z2,z3,z5,z480,z10]),(0,[z0,z12,z29,z1,z2,z3,z5]),(0,[z0,z7,z1,z2,z3,z5,z112])],[(0,[z0,z7,z1,z148,z2,z3,z5]),(0,[z0,z481,z1,z2,z3,z5,z10]),(1,[z0,z225,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z129,z10]),(0,[z0,z12,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z200,z10])],[(0,[z0,z482,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z483]),(0,[z0,z1,z2,z3,z5,z10,z484]),(0,[z0,z1,z2,z3,z5,z6,z485]),(0,[z0,z7,z134,z1,z2,z3,z5]),(0,[z486,z0,z1,z2,z3,z5,z10])],[(0,[z0,z69,z1,z2,z3,z5,z6]),(0,[z20,z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z35,z2,z8,z3,z5]),(1,[z0,z152,z1,z2,z3,z4])],[(1,[z23,z1,z2,z3,z93,z10]),(0,[z0,z29,z1,z2,z3,z5,z13])],[(0,[z0,z7,z1,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z487,z5,z10]),(1,[z0,z1,z488,z3,z5,z10]),(0,[z90,z0,z1,z2,z3,z78,z10]),(0,[z0,z39,z1,z2,z3,z5,z118])],[(0,[z0,z1,z44,z2,z3,z5,z73])],[(1,[z442,z0,z1,z2,z5,z10]),(0,[z0,z489,z1,z2,z3,z5,z10]),(0,[z490,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z491,z2,z3,z5,z10]),(0,[z21,z0,z1,z2,z3,z5,z13]),(0,[z492,z0,z1,z2,z3,z5,z10]),(0,[z493,z0,z1,z2,z3,z5,z10])],[(0,[z0,z494,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z292,z3,z5,z13]),(0,[z0,z495,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z178,z5,z10]),(0,[z241,z0,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z496,z5,z10]),(0,[z0,z497,z1,z2,z3,z5,z10])],[],[(0,[z104,z0,z1,z2,z3,z5,z483]),(0,[z0,z89,z2,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z498,z10]),(0,[z0,z1,z2,z3,z499,z5,z10]),(0,[z0,z1,z2,z3,z5,z132,z10])]],
   [[(0,[z0,z500,z1,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z5,z159]),(0,[z0,z152,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z501,z3,z5,z10])],[(0,[z0,z403,z7,z1,z2,z3,z5]),(0,[z502,z0,z1,z2,z3,z5,z10])],[(0,[z21,z0,z1,z2,z77,z5,z10])],[(0,[z0,z139,z39,z1,z2,z3,z5])],[(0,[z21,z0,z1,z2,z3,z119,z10]),(0,[z0,z1,z2,z3,z5,z503,z10]),(0,[z0,z1,z2,z504,z3,z5,z10]),(0,[z505,z0,z1,z2,z3,z5,z10])],[],[],[(0,[z506,z0,z1,z2,z3,z5,z10])],[(0,[z76,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z117,z3,z5,z13]),(0,[z0,z39,z1,z95,z2,z3,z5])],[(1,[z0,z1,z2,z3,z5,z507]),(0,[z0,z1,z2,z3,z5,z10,z262])],[(0,[z0,z1,z185,z2,z3,z5,z13]),(0,[z0,z106,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z508,z132]),(1,[z0,z1,z2,z3,z5,z252])],[(0,[z0,z7,z69,z1,z2,z3,z5]),(1,[z0,z29,z2,z3,z5,z112]),(0,[z0,z1,z2,z3,z479,z5,z10]),(0,[z0,z1,z2,z3,z509,z5,z10])],[(1,[z0,z359,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z80,z5]),(0,[z510,z0,z1,z2,z3,z5,z10]),(0,[z0,z511,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z6,z112]),(0,[z0,z134,z2,z3,z5,z159,z10]),(0,[z0,z7,z1,z2,z3,z5,z73])],[(0,[z0,z1,z512,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z513,z5,z10]),(0,[z0,z1,z2,z514,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z515,z3,z5,z10])],[(0,[z33,z0,z2,z3,z5,z159,z10]),(1,[z0,z29,z1,z2,z3,z5]),(0,[z0,z7,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z516,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z191]),(0,[z90,z0,z1,z2,z3,z5,z10]),(1,[z0,z39,z1,z2,z3,z5])],[(0,[z0,z1,z478,z2,z3,z5,z13]),(0,[z0,z1,z517,z2,z3,z5,z10]),(1,[z0,z1,z238,z2,z3,z5])],[],[(0,[z0,z1,z2,z3,z77,z5,z6]),(0,[z0,z29,z134,z2,z3,z5,z10]),(0,[z0,z1,z518,z2,z3,z5,z10])],[(0,[z0,z134,z69,z2,z3,z5,z10]),(0,[z111,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z519,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z508]),(0,[z0,z1,z2,z292,z3,z25,z10])],[],[(0,[z0,z1,z2,z3,z5,z520,z10]),(0,[z521,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z522,z5,z10])],[(0,[z33,z0,z69,z2,z3,z5,z10]),(0,[z0,z123,z1,z2,z3,z5,z13]),(0,[z0,z1,z274,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z523])],[(0,[z0,z1,z2,z3,z524,z5,z10])],[(0,[z104,z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z477])],[(0,[z104,z0,z39,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z3,z197,z5])],[(0,[z21,z0,z1,z2,z3,z5,z10]),(0,[z0,z39,z240,z1,z2,z3,z5]),(0,[z525,z0,z1,z2,z3,z5,z10])],[(0,[z90,z0,z1,z72,z2,z3,z10]),(0,[z0,z1,z2,z526,z3,z5,z10]),(0,[z0,z1,z2,z292,z3,z5,z10])],[]],
   [[(0,[z0,z1,z72,z2,z3,z5,z13]),(0,[z0,z256,z1,z3,z5,z73,z10]),(0,[z0,z1,z2,z527,z3,z5,z10])],[(0,[z0,z1,z2,z3,z528,z5,z10]),(0,[z0,z1,z2,z3,z415,z5,z6]),(0,[z0,z1,z2,z3,z529,z5,z10]),(0,[z0,z1,z2,z530,z3,z5,z10]),(0,[z66,z0,z29,z1,z2,z3,z5]),(0,[z0,z7,z1,z94,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z400,z10])],[(0,[z0,z1,z2,z3,z531,z5,z10]),(0,[z96,z0,z1,z2,z31,z5,z10]),(0,[z66,z0,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z532,z5,z10])],[(0,[z0,z1,z2,z3,z5,z6,z533]),(0,[z0,z29,z7,z1,z2,z3,z5]),(0,[z0,z277,z1,z2,z3,z5,z10])],[(0,[z33,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z534,z10]),(0,[z0,z123,z2,z8,z3,z5,z10]),(0,[z0,z1,z2,z3,z535,z5,z10]),(0,[z0,z536,z1,z2,z3,z5,z10])],[(1,[z0,z1,z2,z3,z5,z404]),(0,[z0,z1,z2,z537,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z25,z5])],[(0,[z0,z1,z2,z3,z70,z5,z6]),(0,[z0,z152,z1,z44,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z538,z10])],[(0,[z21,z0,z7,z1,z2,z3,z5]),(0,[z0,z176,z2,z3,z5,z73,z10])],[(0,[z0,z1,z539,z2,z3,z5,z10]),(0,[z0,z1,z2,z540,z3,z5,z10])],[(0,[z0,z1,z2,z117,z3,z5,z10]),(0,[z0,z1,z35,z2,z3,z5,z10]),(0,[z0,z1,z2,z245,z3,z70,z5])],[(0,[z0,z1,z2,z3,z5,z6,z541])],[(0,[z0,z1,z2,z3,z5,z10,z413])],[(0,[z0,z1,z2,z3,z5,z542,z10]),(0,[z0,z1,z44,z2,z3,z49,z5])],[(0,[z0,z152,z1,z2,z3,z5,z6]),(0,[z0,z39,z467,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z543,z5,z10])],[(0,[z96,z62,z0,z1,z2,z5,z10]),(0,[z0,z1,z2,z544,z3,z5,z10]),(0,[z0,z1,z545,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z546,z5,z10]),(1,[z0,z1,z478,z2,z3,z5]),(0,[z0,z1,z2,z3,z547,z5,z10])],[(0,[z0,z1,z2,z3,z5,z548,z10]),(0,[z90,z0,z1,z2,z3,z93,z10])],[(0,[z0,z1,z2,z3,z5,z549,z10]),(0,[z0,z1,z2,z3,z5,z10,z550])],[(0,[z0,z227,z1,z2,z3,z5,z10]),(0,[z0,z240,z1,z3,z80,z5,z10])],[(0,[z90,z0,z1,z2,z3,z5,z13]),(0,[z551,z0,z1,z2,z3,z5,z10]),(0,[z0,z134,z1,z2,z37,z5,z10]),(0,[z0,z57,z1,z2,z3,z5,z367]),(0,[z0,z1,z2,z292,z3,z79,z10])],[(0,[z76,z0,z7,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z552,z5,z10]),(0,[z0,z1,z2,z245,z3,z5,z67]),(0,[z0,z1,z2,z245,z5,z10,z61]),(0,[z0,z1,z553,z2,z3,z5,z10]),(0,[z0,z554,z1,z2,z3,z5,z10])],[(1,[z0,z337,z1,z2,z3,z5]),(0,[z62,z0,z1,z2,z117,z5,z10]),(0,[z0,z1,z2,z30,z3,z5,z6]),(0,[z0,z555,z1,z2,z3,z5,z10]),(0,[z229,z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z556]),(0,[z0,z39,z1,z44,z2,z3,z5])],[(0,[z111,z0,z1,z2,z3,z5,z10]),(0,[z557,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z558,z5,z10]),(0,[z0,z123,z134,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z559,z10]),(0,[z0,z1,z2,z3,z5,z560,z10])],[(0,[z0,z1,z2,z434,z3,z5,z10])],[(0,[z20,z1,z185,z2,z3,z5,z10]),(0,[z0,z1,z196,z185,z2,z3,z5]),(1,[z0,z409,z1,z2,z3,z5]),(0,[z0,z561,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z562,z5,z10]),(0,[z0,z39,z1,z72,z2,z3,z5]),(0,[z0,z1,z72,z2,z3,z25,z10])],[(1,[z104,z0,z29,z2,z3,z5]),(0,[z0,z356,z1,z2,z3,z5,z6]),(0,[z0,z123,z1,z2,z3,z5,z10])],[(0,[z0,z1,z43,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z79]),(0,[z0,z1,z44,z2,z3,z70,z5]),(1,[z0,z1,z2,z292,z25,z10])],[(0,[z0,z240,z1,z95,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z159])],[(0,[z0,z1,z2,z488,z3,z5,z10]),(1,[z0,z240,z95,z3,z5,z10])],[(0,[z0,z1,z563,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z254]),(0,[z0,z39,z1,z2,z3,z5,z6])],[]],
   [[(0,[z0,z1,z3,z462,z5,z73,z10]),(0,[z0,z1,z2,z245,z3,z5,z61]),(0,[z0,z152,z1,z2,z3,z70,z10])],[(0,[z0,z7,z1,z2,z3,z49,z5]),(0,[z0,z7,z176,z1,z2,z3,z5]),(0,[z0,z176,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z564,z10]),(0,[z0,z1,z72,z2,z3,z5,z10]),(0,[z0,z56,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z159,z6]),(0,[z111,z0,z7,z1,z2,z3,z5]),(0,[z0,z1,z386,z44,z2,z3,z5]),(0,[z0,z57,z151,z2,z3,z5,z10]),(0,[z0,z57,z1,z2,z3,z25,z10])],[(0,[z0,z1,z2,z3,z5,z565,z10]),(0,[z0,z134,z2,z3,z5,z73,z10])],[(0,[z0,z566,z1,z2,z3,z5,z10]),(0,[z62,z1,z2,z117,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z567,z10]),(1,[z0,z234,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z346,z6]),(0,[z0,z1,z2,z3,z5,z10,z568])],[(0,[z0,z1,z2,z569,z3,z5,z10]),(1,[z0,z1,z209,z2,z3,z5]),(1,[z62,z1,z2,z117,z5,z10]),(0,[z23,z1,z2,z3,z93,z5,z10]),(1,[z0,z123,z8,z3,z5,z10]),(0,[z0,z123,z7,z1,z2,z3,z5]),(0,[z0,z570,z1,z2,z3,z5,z10]),(0,[z0,z571,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z572,z10]),(0,[z0,z573,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z67])],[(0,[z0,z1,z2,z3,z574,z51,z5]),(0,[z0,z1,z2,z3,z5,z575,z10])],[(0,[z0,z1,z44,z2,z3,z5,z78]),(0,[z0,z1,z2,z3,z5,z13,z61])],[(0,[z0,z176,z1,z2,z3,z5,z6]),(0,[z0,z131,z1,z44,z2,z3,z5]),(0,[z0,z1,z395,z44,z2,z3,z5])],[(0,[z33,z0,z1,z2,z3,z5,z86]),(0,[z0,z29,z1,z2,z170,z3,z5]),(0,[z0,z57,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z576,z3,z5,z10]),(0,[z0,z1,z577,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z578,z5,z10]),(1,[z0,z2,z3,z579,z5,z10])],[(0,[z0,z1,z2,z3,z580,z5,z10]),(0,[z0,z39,z1,z2,z3,z93,z5]),(0,[z0,z1,z83,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z4,z5]),(0,[z96,z0,z1,z2,z30,z5,z10])],[(0,[z0,z1,z2,z3,z4,z5,z13]),(0,[z0,z1,z2,z3,z5,z581,z10])],[(0,[z0,z1,z2,z582,z3,z5,z10])],[(0,[z0,z24,z123,z1,z3,z5,z10]),(0,[z0,z7,z1,z2,z3,z5,z79]),(0,[z0,z7,z1,z2,z3,z70,z5])]],
   [[(0,[z0,z583,z1,z2,z3,z5,z10]),(0,[z584,z0,z1,z2,z3,z5,z10])],[(0,[z0,z585,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z61])],[(0,[z0,z1,z2,z3,z5,z13,z166])],[(0,[z0,z406,z1,z2,z3,z5,z10]),(0,[z27,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z586,z2,z3,z5,z10]),(0,[z0,z1,z587,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z588,z5,z10])],[(0,[z0,z1,z2,z190,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z485]),(0,[z589,z0,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z79,z6]),(1,[z0,z1,z2,z3,z5,z40])],[(0,[z0,z1,z72,z2,z3,z79,z10])],[(0,[z96,z0,z1,z3,z31,z5,z10]),(0,[z0,z39,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z590,z10]),(0,[z0,z1,z2,z3,z5,z591,z10]),(0,[z0,z1,z2,z592,z3,z5,z10])],[],[(0,[z0,z1,z577,z2,z8,z3,z5]),(0,[z0,z7,z1,z2,z3,z5,z67])],[(0,[z0,z1,z593,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z132]),(0,[z0,z1,z44,z2,z3,z5,z166])],[(0,[z0,z1,z2,z3,z5,z594,z10]),(0,[z0,z7,z1,z2,z3,z5,z78]),(0,[z0,z134,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z595,z3,z5,z10])],[(0,[z0,z596,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z597,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z508,z10])],[(0,[z0,z409,z1,z2,z3,z5,z6]),(0,[z285,z0,z39,z1,z2,z3,z5])],[(0,[z33,z0,z1,z44,z2,z3,z5]),(0,[z598,z0,z1,z2,z3,z5,z13]),(0,[z599,z0,z1,z2,z3,z5,z10]),(1,[z0,z554,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z44,z185,z2,z3,z5]),(0,[z90,z0,z7,z1,z2,z3,z5]),(0,[z0,z1,z2,z600,z3,z5,z10]),(0,[z0,z58,z1,z2,z3,z5,z10]),(0,[z0,z57,z1,z2,z3,z79,z10])],[(0,[z0,z1,z2,z3,z5,z132,z6])],[(0,[z601,z0,z1,z2,z3,z5,z10]),(0,[z62,z0,z1,z2,z3,z5,z534]),(0,[z0,z1,z602,z2,z3,z5,z10]),(0,[z0,z1,z72,z2,z3,z132,z10]),(0,[z0,z1,z2,z603,z3,z5,z10]),(0,[z0,z604,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z93,z5,z10]),(0,[z0,z1,z2,z3,z5,z605,z10]),(0,[z606,z0,z1,z2,z3,z5,z10]),(0,[z0,z607,z1,z2,z3,z5,z10]),(0,[z0,z608,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z483]),(0,[z0,z134,z1,z2,z3,z5,z6]),(0,[z0,z7,z1,z2,z3,z80,z5])],[(1,[z0,z1,z2,z3,z102,z10]),(0,[z0,z7,z1,z2,z3,z5,z61]),(0,[z0,z1,z44,z2,z3,z31,z5]),(0,[z0,z609,z1,z2,z3,z5,z10])],[(1,[z0,z234,z2,z3,z5,z13]),(0,[z155,z0,z1,z2,z3,z5,z10]),(0,[z521,z0,z7,z1,z2,z3,z5])],[(1,[z0,z377,z1,z2,z3,z5]),(0,[z610,z0,z1,z2,z3,z5,z10]),(0,[z0,z24,z1,z72,z3,z5,z10])],[(0,[z143,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z611,z5,z10]),(0,[z0,z1,z2,z30,z3,z189,z10])],[(1,[z0,z1,z2,z3,z5,z42])],[(0,[z0,z1,z2,z3,z462,z5,z10])],[(0,[z0,z1,z2,z3,z5,z410,z10]),(0,[z0,z1,z2,z3,z612,z5,z10]),(0,[z0,z184,z39,z1,z2,z3,z5]),(0,[z613,z0,z1,z2,z3,z5,z10])],[(0,[z614,z0,z1,z2,z3,z5,z10]),(0,[z0,z57,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z615,z3,z5,z10]),(0,[z0,z54,z1,z2,z3,z5,z79])],[(0,[z0,z1,z2,z3,z616,z5,z10]),(0,[z0,z1,z2,z3,z5,z617,z10]),(0,[z0,z7,z1,z545,z2,z3,z5])],[(0,[z23,z0,z1,z2,z3,z78,z10]),(0,[z0,z1,z2,z3,z5,z10,z112]),(0,[z0,z1,z2,z3,z4,z5,z10])],[(0,[z0,z1,z2,z3,z5,z167,z10]),(0,[z0,z1,z2,z3,z5,z67,z6]),(0,[z0,z7,z1,z2,z3,z5,z132]),(0,[z0,z7,z1,z2,z3,z5,z166]),(0,[z66,z0,z554,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z618])]],
   [[(0,[z619,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z30,z3,z5,z477]),(0,[z0,z39,z1,z2,z3,z100,z5])],[(0,[z0,z57,z1,z2,z5,z79,z10])],[(0,[z0,z29,z1,z44,z2,z3,z5])],[(0,[z0,z1,z2,z3,z620,z5,z10]),(1,[z0,z1,z2,z3,z5,z322]),(1,[z0,z211,z1,z2,z3,z5]),(0,[z0,z621,z1,z2,z3,z5,z10])],[(0,[z0,z7,z1,z185,z2,z3,z5]),(0,[z62,z0,z1,z94,z2,z5,z10]),(0,[z27,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z622,z10])],[(0,[z0,z1,z2,z623,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z51,z5]),(0,[z0,z29,z1,z72,z2,z3,z5]),(0,[z0,z1,z2,z3,z624,z5,z10])],[(0,[z0,z1,z2,z3,z5,z436,z6]),(0,[z0,z625,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z73,z6]),(0,[z0,z39,z1,z2,z292,z3,z5]),(0,[z0,z1,z2,z3,z626,z5,z10])],[(0,[z0,z39,z1,z2,z117,z3,z5]),(0,[z0,z1,z2,z3,z627,z5,z10]),(0,[z0,z1,z2,z3,z186,z5,z10]),(0,[z0,z240,z95,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z5,z118]),(0,[z0,z39,z1,z2,z3,z5,z346])],[(0,[z0,z1,z2,z3,z5,z10,z507]),(0,[z0,z1,z628,z2,z3,z5,z10]),(0,[z76,z1,z2,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z93,z79,z10]),(0,[z0,z1,z2,z37,z3,z5,z10]),(0,[z0,z7,z1,z2,z3,z31,z5])],[(0,[z0,z1,z2,z3,z5,z191,z10]),(0,[z0,z29,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z128,z10]),(0,[z629,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z252])],[(0,[z0,z1,z2,z630,z3,z5,z10]),(0,[z0,z2,z30,z3,z579,z5,z10]),(0,[z0,z1,z2,z3,z5,z631,z10])],[(0,[z0,z2,z3,z5,z122,z10,z13]),(0,[z0,z1,z2,z3,z5,z632,z10]),(0,[z0,z455,z1,z44,z2,z3,z5])],[(0,[z633,z0,z1,z2,z3,z5,z10])],[(0,[z0,z225,z69,z1,z2,z3,z5]),(1,[z0,z352,z1,z2,z3,z10])],[(0,[z21,z0,z1,z2,z3,z5,z6]),(0,[z27,z0,z7,z1,z2,z3,z5]),(0,[z0,z634,z1,z2,z3,z5,z13])]],
   [[(0,[z0,z1,z2,z3,z635,z5,z10]),(0,[z598,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z6,z61]),(0,[z0,z1,z95,z2,z3,z5,z42]),(0,[z0,z1,z2,z3,z5,z10,z636]),(0,[z0,z1,z2,z3,z5,z637,z10])],[(0,[z33,z0,z39,z1,z2,z3,z5]),(0,[z21,z0,z319,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z228,z10])],[(0,[z0,z1,z2,z3,z638,z5,z10]),(0,[z0,z1,z2,z600,z3,z5,z13])],[(0,[z0,z123,z176,z2,z3,z5,z10]),(0,[z0,z240,z1,z8,z3,z5,z10]),(0,[z0,z36,z1,z2,z49,z5,z10]),(0,[z0,z1,z2,z3,z5,z639,z10]),(1,[z0,z1,z2,z3,z574,z5])],[(0,[z76,z0,z1,z185,z3,z5,z10]),(0,[z76,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z640,z10])],[(0,[z0,z1,z2,z3,z93,z5,z13]),(0,[z0,z137,z1,z2,z3,z31,z5])],[(0,[z0,z1,z196,z2,z3,z5,z10]),(0,[z96,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z10,z641])],[(0,[z642,z0,z1,z2,z3,z5,z10]),(0,[z23,z0,z1,z2,z3,z5,z10]),(0,[z0,z240,z1,z2,z3,z5,z120]),(0,[z0,z1,z2,z3,z643,z5,z10])],[(0,[z0,z29,z1,z2,z3,z93,z5]),(0,[z0,z29,z1,z95,z2,z3,z5]),(0,[z0,z39,z1,z2,z3,z5,z112]),(0,[z0,z644,z1,z2,z3,z5,z10])],[(0,[z0,z39,z1,z148,z2,z3,z5]),(0,[z0,z7,z1,z2,z3,z51,z5]),(0,[z0,z1,z94,z2,z31,z5,z10]),(0,[z0,z1,z2,z3,z579,z5,z10]),(0,[z0,z260,z1,z2,z3,z5,z10])],[(0,[z143,z0,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z6,z166]),(0,[z0,z1,z44,z2,z37,z3,z5]),(0,[z0,z2,z3,z51,z5,z73,z10]),(1,[z0,z1,z2,z3,z5,z400])],[(0,[z104,z0,z148,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z541]),(1,[z0,z1,z274,z2,z3,z10]),(0,[z0,z645,z1,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z626,z5])],[(0,[z646,z0,z1,z2,z3,z5,z10]),(0,[z76,z0,z1,z2,z3,z5,z6]),(0,[z0,z265,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z533,z10]),(0,[z0,z1,z647,z2,z3,z5,z10])],[(0,[z0,z1,z185,z2,z3,z5,z6]),(0,[z0,z24,z240,z1,z3,z5,z10]),(1,[z0,z7,z2,z3,z5,z159])],[(1,[z90,z1,z2,z3,z78,z10]),(0,[z0,z1,z2,z648,z3,z5,z10])]],
   [[(1,[z0,z193,z1,z2,z3,z5]),(0,[z0,z138,z1,z2,z3,z5,z10]),(0,[z66,z0,z152,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z649,z10])],[(0,[z0,z29,z1,z2,z263,z3,z5]),(0,[z111,z0,z1,z44,z2,z3,z5])],[(0,[z0,z1,z2,z650,z3,z5,z10]),(0,[z0,z1,z2,z3,z651,z5,z10])],[(0,[z23,z0,z1,z72,z2,z3,z10]),(1,[z0,z15,z2,z3,z5,z10])],[(0,[z0,z1,z2,z652,z3,z5,z10]),(2,[z0,z234,z2,z3,z5]),(0,[z0,z123,z1,z44,z2,z3,z5]),(0,[z0,z357,z1,z2,z3,z5,z10])],[(0,[z20,z0,z1,z170,z3,z5,z10]),(0,[z0,z176,z1,z2,z3,z51,z10])],[(0,[z0,z148,z2,z3,z49,z5,z10])],[(0,[z0,z1,z2,z469,z3,z5,z10])],[(0,[z0,z193,z1,z2,z3,z5,z10]),(0,[z0,z57,z7,z1,z2,z3,z5])],[(1,[z0,z1,z294,z3,z5,z10]),(0,[z111,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z653,z10]),(1,[z0,z12,z2,z3,z51,z10]),(0,[z0,z1,z2,z654,z3,z5,z10]),(0,[z0,z655,z1,z2,z3,z5,z10]),(0,[z493,z0,z1,z44,z2,z3,z5])],[(0,[z0,z1,z656,z2,z3,z5,z10]),(0,[z0,z657,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z658])],[(0,[z0,z1,z659,z2,z3,z5,z10]),(0,[z0,z1,z2,z37,z3,z5,z13]),(0,[z0,z284,z1,z2,z3,z5,z10])],[(0,[z0,z123,z1,z2,z3,z5,z6]),(0,[z0,z29,z240,z1,z2,z3,z5]),(0,[z0,z1,z2,z245,z3,z5,z10])],[(0,[z0,z1,z2,z660,z3,z5,z10]),(1,[z0,z1,z2,z3,z5,z108]),(1,[z0,z29,z2,z3,z49,z5])],[(0,[z0,z1,z148,z2,z3,z5,z13]),(0,[z442,z0,z1,z2,z170,z5,z10]),(0,[z0,z7,z1,z2,z37,z3,z5])],[(0,[z0,z1,z2,z3,z5,z10,z322]),(0,[z0,z1,z2,z661,z3,z5,z10]),(0,[z143,z1,z2,z3,z5,z6,z10]),(0,[z0,z240,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z662,z3,z5,z10])]],
   [[(0,[z0,z634,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z663,z10]),(0,[z374,z0,z39,z1,z2,z3,z5])],[(0,[z0,z1,z2,z664,z3,z5,z10]),(0,[z0,z1,z2,z665,z3,z5,z10])],[(0,[z0,z1,z666,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z667,z5,z10])],[(0,[z0,z378,z29,z1,z2,z3,z5]),(0,[z0,z193,z7,z1,z2,z3,z5])],[(0,[z0,z1,z668,z2,z3,z5,z10]),(0,[z0,z29,z1,z2,z3,z25,z5])],[(0,[z0,z0,z1,z2,z3,z5,z10]),(0,[z0,z179,z1,z2,z3,z5,z10]),(0,[z62,z0,z1,z2,z77,z5,z10]),(0,[z0,z1,z2,z3,z5,z10,z669]),(0,[z670,z0,z1,z2,z3,z5,z10])],[(0,[z23,z0,z1,z2,z3,z93,z10]),(0,[z0,z1,z2,z3,z671,z5,z10])],[(1,[z0,z1,z2,z3,z5,z17]),(0,[z96,z0,z1,z2,z3,z5,z10])],[(0,[z672,z0,z1,z2,z3,z5,z10]),(0,[z0,z95,z2,z3,z49,z5,z10]),(0,[z387,z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z44,z2,z245,z3,z5])],[(0,[z23,z0,z1,z2,z3,z5,z13]),(1,[z0,z145,z1,z2,z3,z5]),(0,[z0,z277,z2,z30,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z303,z10]),(0,[z0,z106,z29,z1,z2,z3,z5]),(0,[z0,z1,z44,z2,z540,z3,z5])],[],[(0,[z0,z1,z2,z673,z3,z5,z10])],[(0,[z0,z1,z2,z3,z674,z5,z10]),(1,[z0,z1,z577,z2,z3,z5]),(1,[z0,z1,z2,z3,z391,z5]),(0,[z0,z1,z44,z2,z3,z5,z10]),(0,[z0,z675,z1,z2,z3,z5,z10])],[(0,[z104,z0,z123,z2,z3,z5,z10]),(0,[z0,z1,z94,z170,z3,z5,z10]),(0,[z96,z0,z1,z94,z3,z5,z10]),(0,[z66,z0,z1,z2,z3,z70,z5]),(0,[z0,z1,z2,z3,z5,z676,z10]),(0,[z0,z1,z677,z2,z3,z5,z10])],[(0,[z90,z0,z1,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z678,z5,z10]),(0,[z0,z1,z2,z3,z5,z404,z10]),(0,[z0,z1,z2,z679,z3,z5,z10]),(0,[z0,z39,z1,z2,z2,z3,z5]),(0,[z0,z1,z2,z3,z680,z5,z10])]],
   [[(0,[z0,z1,z2,z3,z681,z5,z10])],[(0,[z682,z0,z1,z2,z3,z5,z10]),(0,[z683,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z98,z49,z5]),(0,[z0,z607,z7,z1,z2,z3,z5])],[(0,[z0,z377,z1,z2,z3,z5,z10]),(0,[z96,z0,z7,z1,z2,z3,z5])],[(0,[z0,z1,z44,z2,z3,z77,z5]),(1,[z0,z1,z2,z3,z5,z534]),(0,[z0,z29,z1,z2,z292,z3,z5]),(0,[z0,z1,z94,z2,z30,z5,z10]),(0,[z0,z1,z684,z2,z3,z5,z10])],[(0,[z0,z1,z170,z3,z31,z5,z10]),(0,[z0,z1,z95,z2,z3,z5,z108]),(0,[z0,z29,z1,z2,z3,z5,z346])],[(0,[z0,z1,z2,z3,z25,z78,z10]),(0,[z0,z1,z2,z685,z3,z5,z10])],[(0,[z143,z0,z7,z1,z2,z3,z5]),(0,[z0,z39,z1,z94,z2,z3,z5])],[(1,[z0,z1,z2,z190,z5,z10]),(0,[z90,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z367])],[(0,[z0,z1,z2,z3,z686,z5,z10]),(0,[z0,z1,z2,z5,z67,z10,z61])],[(0,[z0,z1,z2,z435,z3,z5,z10]),(0,[z66,z0,z1,z2,z3,z5,z67])],[(0,[z0,z337,z1,z148,z2,z3,z5]),(0,[z21,z0,z1,z44,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z13,z275]),(0,[z0,z12,z1,z72,z2,z3,z10]),(0,[z0,z687,z1,z2,z3,z5,z10]),(0,[z0,z1,z3,z80,z5,z132,z10])],[(0,[z33,z0,z1,z2,z3,z5,z507]),(0,[z0,z688,z1,z2,z3,z5,z10]),(0,[z90,z0,z1,z2,z3,z5,z410]),(0,[z0,z24,z1,z2,z3,z5,z13]),(0,[z0,z1,z44,z2,z8,z3,z5]),(1,[z0,z1,z545,z2,z3,z5]),(0,[z0,z7,z1,z2,z245,z3,z5]),(1,[z0,z1,z94,z30,z5,z10])],[(0,[z156,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z689,z10])],[(0,[z0,z1,z2,z245,z3,z5,z13]),(1,[z0,z226,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z10,z690])],[(0,[z0,z1,z148,z2,z3,z5,z10]),(0,[z62,z0,z1,z2,z3,z5,z10]),(0,[z0,z36,z2,z3,z49,z5,z10]),(0,[z0,z414,z29,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z691,z10])]],
   [[],[(0,[z0,z240,z1,z2,z3,z5,z13]),(0,[z0,z7,z1,z2,z3,z5,z10]),(1,[z0,z1,z2,z245,z5,z61])],[(0,[z0,z1,z2,z3,z574,z5,z10]),(0,[z0,z1,z692,z2,z3,z5,z10])],[(0,[z33,z0,z29,z1,z2,z3,z5]),(0,[z21,z0,z1,z488,z3,z5,z10]),(0,[z0,z1,z2,z292,z3,z5,z6]),(0,[z0,z1,z693,z2,z3,z5,z10])],[(0,[z694,z0,z1,z2,z3,z5,z10]),(0,[z66,z0,z1,z2,z3,z5,z61]),(0,[z0,z1,z2,z3,z5,z695,z10])],[(0,[z23,z0,z1,z2,z3,z5,z154]),(0,[z0,z1,z2,z3,z5,z10,z696]),(0,[z0,z697,z1,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z13,z13]),(0,[z0,z1,z2,z3,z698,z5,z10]),(0,[z0,z467,z1,z2,z3,z5,z10])],[(0,[z0,z7,z1,z2,z3,z77,z5]),(0,[z0,z0,z1,z2,z3,z5,z13])],[(0,[z0,z1,z2,z3,z5,z6,z202])],[(0,[z0,z29,z1,z1,z2,z3,z5])],[(0,[z0,z352,z1,z2,z8,z3,z10]),(0,[z0,z699,z1,z2,z3,z5,z10]),(0,[z0,z1,z72,z2,z3,z80,z10])],[(0,[z0,z1,z2,z3,z700,z5,z10])],[(0,[z0,z1,z2,z3,z5,z10,z701]),(0,[z0,z431,z1,z2,z3,z5,z10])],[(1,[z0,z1,z196,z2,z3,z5]),(0,[z0,z39,z134,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z702,z10])],[(1,[z0,z184,z1,z2,z3,z5]),(0,[z0,z1,z2,z703,z3,z5,z10])],[(0,[z704,z0,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z117,z3,z5,z6]),(0,[z0,z705,z1,z2,z3,z5,z10]),(0,[z0,z1,z44,z2,z3,z5,z13]),(0,[z0,z1,z706,z2,z3,z5,z10]),(0,[z694,z0,z7,z1,z2,z3,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z10]),(0,[z0,z1,z44,z294,z3,z5]),(0,[z1,z2,z3,z708,z78,z10]),(0,[z0,z1,z2,z3,z5,z709]),(0,[z0,z256,z1,z3,z5,z6]),(0,[z0,z710,z1,z2,z3,z5])],[(0,[z0,z7,z1,z2,z190,z5]),(0,[z0,z554,z2,z3,z70,z5])],[(0,[z0,z1,z2,z3,z711,z5]),(0,[z0,z1,z294,z3,z102,z10]),(0,[z0,z24,z1,z3,z132,z13]),(0,[z0,z712,z1,z2,z3,z5]),(0,[z0,z29,z571,z2,z3,z5])],[(0,[z0,z713,z1,z2,z3,z10]),(0,[z0,z2,z3,z714,z49,z5]),(0,[z0,z7,z99,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z477])],[(0,[z0,z1,z2,z3,z715,z10]),(0,[z0,z716,z1,z2,z3,z10]),(0,[z0,z256,z39,z1,z3,z5]),(0,[z0,z717,z2,z3,z5,z10]),(0,[z0,z1,z2,z516,z5,z61])],[(0,[z33,z138,z1,z2,z3,z5]),(0,[z0,z1,z718,z3,z5,z10]),(0,[z1,z2,z3,z5,z10,z719]),(0,[z0,z277,z44,z2,z3,z5])],[(0,[z1,z2,z117,z720,z5,z10]),(0,[z90,z1,z2,z3,z78,z322]),(0,[z0,z234,z2,z3,z5,z132]),(0,[z0,z721,z1,z2,z3,z5]),(0,[z0,z722,z1,z2,z3,z5]),(0,[z0,z152,z554,z2,z3,z5])],[(0,[z0,z22,z2,z3,z119,z10]),(0,[z0,z1,z3,z462,z5,z723]),(0,[z0,z1,z2,z379,z5,z67]),(0,[z0,z39,z724,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z725])],[(0,[z0,z1,z44,z2,z3,z119]),(0,[z0,z1,z2,z3,z726,z5]),(0,[z0,z29,z2,z3,z402,z5]),(0,[z0,z7,z56,z2,z3,z5])],[(0,[z0,z727,z2,z3,z5,z10]),(0,[z0,z728,z1,z2,z3,z5]),(0,[z0,z1,z478,z3,z5,z239]),(0,[z0,z2,z3,z5,z729,z112])],[(0,[z0,z1,z730,z2,z3,z10]),(0,[z0,z152,z1,z2,z3,z4])],[(0,[z0,z359,z2,z190,z5,z10]),(0,[z23,z1,z2,z3,z93,z10]),(0,[z1,z2,z3,z74,z5,z6]),(0,[z278,z1,z2,z3,z5,z6])],[(0,[z0,z1,z731,z2,z3,z5])],[(0,[z104,z0,z106,z2,z3,z5]),(0,[z0,z406,z1,z2,z3,z10]),(0,[z0,z1,z488,z3,z5,z10]),(0,[z0,z732,z2,z3,z5,z10]),(0,[z0,z277,z2,z3,z5,z6]),(0,[z0,z733,z1,z2,z3,z5]),(0,[z0,z7,z58,z2,z3,z5]),(0,[z0,z24,z99,z3,z5,z10]),(0,[z0,z1,z72,z3,z178,z80]),(0,[z0,z1,z3,z5,z734,z118]),(0,[z0,z735,z58,z2,z3,z5])],[(0,[z33,z7,z148,z2,z3,z5]),(0,[z442,z0,z89,z2,z5,z10]),(0,[z0,z1,z2,z3,z5,z736]),(0,[z0,z24,z1,z630,z3,z10]),(0,[z0,z352,z95,z2,z3,z10])],[(0,[z0,z1,z737,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z738]),(0,[z0,z1,z2,z3,z5,z739])]],
   [[(0,[z0,z1,z2,z3,z102,z17]),(0,[z0,z234,z2,z3,z31,z5]),(0,[z0,z1,z2,z5,z740,z10])],[(0,[z21,z1,z2,z77,z5,z13]),(0,[z90,z7,z1,z2,z3,z78]),(0,[z0,z29,z134,z2,z263,z5]),(0,[z0,z1,z2,z3,z5,z741]),(0,[z0,z455,z1,z2,z3,z382])],[(0,[z0,z1,z44,z544,z3,z5]),(0,[z0,z1,z2,z3,z5,z742])],[(0,[z0,z2,z3,z5,z122,z483]),(0,[z76,z1,z44,z170,z3,z5]),(0,[z23,z1,z44,z2,z3,z93])],[(0,[z0,z1,z2,z5,z743,z13]),(0,[z0,z1,z2,z3,z5,z413]),(0,[z0,z39,z1,z518,z3,z5])],[(0,[z0,z406,z39,z1,z2,z3]),(0,[z0,z744,z1,z2,z3,z10]),(0,[z0,z1,z2,z3,z745,z10]),(0,[z0,z1,z746,z2,z3,z5]),(0,[z0,z747,z234,z2,z3,z5]),(0,[z0,z29,z2,z3,z371,z5]),(0,[z0,z7,z1,z72,z3,z80])],[(0,[z0,z29,z2,z3,z5,z483]),(0,[z0,z1,z2,z3,z5,z748]),(0,[z0,z1,z2,z3,z5,z749]),(0,[z0,z409,z1,z3,z5,z346]),(0,[z0,z7,z1,z2,z292,z25]),(0,[z0,z1,z94,z30,z5,z40])],[(0,[z298,z1,z2,z3,z5,z6]),(0,[z0,z554,z2,z3,z5,z61])],[(0,[z0,z1,z2,z3,z750,z10]),(0,[z0,z187,z2,z49,z5,z10]),(0,[z0,z1,z2,z3,z751,z10])],[(0,[z0,z752,z1,z2,z3,z5]),(0,[z0,z753,z1,z2,z3,z5]),(0,[z0,z1,z3,z462,z5,z13]),(0,[z0,z2,z3,z754,z73,z10])],[(0,[z21,z1,z2,z77,z119,z10]),(0,[z0,z755,z1,z2,z3,z5]),(0,[z0,z756,z2,z3,z5,z6])],[(0,[z0,z1,z757,z2,z3,z5]),(0,[z0,z234,z2,z3,z49,z5]),(0,[z0,z106,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z758,z5]),(0,[z0,z1,z2,z3,z5,z759])],[(0,[z0,z1,z760,z2,z3,z5])],[(0,[z0,z1,z2,z3,z189,z13]),(0,[z0,z1,z2,z3,z5,z761]),(0,[z0,z762,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z763])],[(0,[z0,z1,z2,z3,z5,z764]),(0,[z143,z467,z1,z2,z3,z5]),(0,[z0,z1,z3,z765,z462,z5]),(0,[z0,z1,z2,z3,z5,z740])],[(0,[z33,z0,z83,z2,z3,z5]),(0,[z289,z1,z2,z3,z78,z10]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z1,z72,z3,z80,z6]),(0,[z0,z39,z1,z434,z3,z5])]],
   [[(0,[z0,z396,z1,z44,z3,z5]),(0,[z0,z234,z2,z3,z51,z5]),(0,[z0,z1,z767,z3,z5,z13]),(0,[z0,z2,z3,z5,z768,z13]),(1,[z0,z123,z352,z3,z10]),(0,[z0,z94,z30,z579,z5,z10])],[],[(0,[z1,z2,z3,z5,z6,z769]),(0,[z0,z7,z1,z274,z2,z3]),(0,[z0,z1,z770,z3,z5,z10]),(0,[z0,z226,z176,z2,z3,z73])],[(0,[z104,z69,z2,z3,z5,z6]),(1,[z0,z256,z176,z3,z10]),(0,[z0,z1,z2,z3,z5,z771])],[(0,[z0,z29,z89,z2,z3,z5]),(0,[z0,z123,z234,z2,z3,z5])],[(0,[z0,z29,z1,z2,z3,z5]),(0,[z0,z1,z2,z772,z5,z10]),(0,[z0,z1,z2,z3,z5,z773]),(0,[z0,z1,z2,z3,z5,z774]),(1,[z0,z724,z2,z3,z5]),(0,[z0,z319,z44,z2,z3,z5]),(0,[z0,z775,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z776]),(0,[z0,z777,z1,z2,z3,z5]),(0,[z0,z7,z1,z2,z3,z128]),(0,[z0,z778,z1,z2,z3,z5])],[(0,[z0,z39,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z191]),(0,[z0,z234,z176,z2,z3,z5])],[(0,[z0,z1,z375,z2,z3,z5]),(0,[z0,z779,z1,z2,z5,z10]),(0,[z0,z625,z7,z2,z3,z5]),(0,[z0,z1,z238,z2,z3,z5]),(0,[z0,z780,z2,z3,z5,z10])],[(0,[z0,z781,z1,z2,z3,z5]),(0,[z0,z54,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z782]),(0,[z0,z234,z2,z3,z5,z79]),(0,[z0,z1,z2,z783,z3,z5]),(0,[z0,z36,z2,z784,z5,z10]),(0,[z0,z256,z176,z3,z73,z10]),(0,[z0,z7,z677,z2,z3,z5])],[(0,[z442,z0,z1,z44,z2,z5])],[(0,[z0,z1,z2,z3,z785,z5]),(0,[z0,z44,z2,z3,z786,z5])],[(0,[z0,z1,z787,z2,z3,z5]),(0,[z0,z788,z1,z2,z3,z5]),(0,[z0,z29,z7,z2,z3,z5]),(0,[z0,z29,z151,z2,z3,z5]),(0,[z0,z1,z2,z435,z5,z61]),(0,[z0,z1,z43,z2,z3,z479])],[(0,[z0,z319,z2,z3,z5,z6]),(0,[z0,z7,z22,z2,z3,z5]),(0,[z0,z789,z2,z3,z5,z10]),(0,[z23,z1,z2,z3,z93,z13]),(0,[z0,z29,z2,z3,z579,z5]),(0,[z0,z39,z151,z2,z3,z5])],[(0,[z0,z106,z218,z2,z3,z5]),(0,[z0,z790,z1,z2,z3,z5]),(0,[z0,z1,z791,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z792]),(0,[z0,z39,z2,z3,z579,z5]),(0,[z66,z0,z1,z2,z624,z5])],[(0,[z0,z106,z2,z3,z49,z5]),(0,[z0,z1,z2,z3,z5,z793]),(0,[z0,z1,z488,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z794])]],
   [[(0,[z0,z1,z2,z3,z795,z6]),(0,[z0,z1,z2,z796,z5,z10]),(0,[z0,z797,z2,z3,z5,z10])],[(0,[z0,z1,z798,z2,z3,z5]),(0,[z442,z0,z1,z2,z5,z13]),(0,[z0,z1,z2,z3,z5,z799]),(0,[z0,z1,z2,z600,z5,z61]),(0,[z0,z1,z2,z3,z5,z800]),(0,[z0,z2,z679,z49,z5,z10])],[(0,[z33,z273,z2,z3,z5,z10]),(0,[z0,z1,z2,z801,z5,z10]),(0,[z21,z1,z2,z77,z5,z10]),(0,[z1,z2,z720,z77,z5,z10]),(0,[z0,z802,z1,z2,z3,z5]),(0,[z0,z29,z277,z2,z3,z5]),(0,[z0,z29,z517,z2,z3,z5]),(0,[z0,z777,z277,z2,z3,z5]),(0,[z0,z1,z44,z199,z3,z5])],[(0,[z0,z803,z1,z2,z3,z5]),(0,[z0,z39,z277,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z804]),(0,[z0,z352,z1,z35,z2,z3]),(0,[z0,z805,z1,z2,z3,z5])],[(0,[z0,z1,z806,z2,z3,z10]),(0,[z0,z57,z1,z2,z79,z6]),(0,[z0,z240,z807,z3,z5,z10])],[(0,[z0,z1,z2,z3,z808,z5]),(0,[z0,z1,z809,z2,z3,z5]),(0,[z0,z2,z3,z51,z754,z10])],[(0,[z0,z810,z2,z3,z5,z10]),(0,[z0,z123,z218,z2,z3,z5]),(0,[z0,z1,z2,z3,z811,z5]),(0,[z0,z812,z1,z2,z3,z5])],[(0,[z0,z1,z332,z2,z190,z10]),(0,[z0,z813,z22,z2,z3,z5]),(0,[z0,z1,z488,z3,z119,z10]),(0,[z0,z29,z1,z2,z3,z814])],[(0,[z0,z1,z815,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z404])],[(0,[z0,z7,z1,z488,z3,z5]),(0,[z0,z1,z3,z462,z5,z10]),(0,[z0,z1,z2,z3,z5,z816])],[(0,[z0,z134,z2,z37,z5,z6]),(0,[z0,z95,z807,z3,z5,z10]),(0,[z0,z12,z2,z3,z389,z10])],[(0,[z0,z1,z2,z3,z817,z5]),(0,[z0,z1,z72,z514,z3,z10])],[(0,[z0,z1,z818,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z819]),(0,[z0,z1,z44,z332,z2,z3]),(0,[z1,z2,z3,z5,z13,z658]),(0,[z0,z1,z2,z3,z820,z10]),(0,[z0,z7,z2,z3,z5,z244])],[(0,[z0,z821,z1,z2,z3,z5]),(0,[z0,z822,z1,z2,z3,z5]),(0,[z0,z134,z2,z37,z5,z55]),(0,[z0,z277,z2,z3,z189,z10]),(0,[z0,z1,z3,z823,z132,z10])]],
   [[(0,[z0,z824,z2,z3,z5,z10]),(0,[z0,z29,z319,z2,z3,z5]),(0,[z0,z352,z1,z44,z2,z3]),(0,[z0,z1,z825,z2,z3,z5]),(0,[z0,z39,z1,z94,z30,z5]),(0,[z0,z39,z1,z350,z3,z5])],[(0,[z0,z39,z319,z2,z3,z5]),(0,[z0,z1,z767,z3,z5,z10]),(0,[z0,z2,z3,z5,z768,z10]),(0,[z0,z1,z2,z3,z5,z826])],[(0,[z0,z827,z1,z2,z3,z5]),(0,[z0,z123,z56,z2,z3,z5]),(0,[z0,z29,z15,z2,z3,z5])],[(0,[z0,z359,z2,z3,z5,z13]),(0,[z0,z828,z1,z2,z3,z5]),(0,[z0,z829,z2,z3,z5,z262]),(0,[z0,z1,z44,z3,z127,z5]),(0,[z0,z39,z15,z2,z3,z5])],[(0,[z0,z1,z294,z3,z5,z17]),(0,[z0,z830,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z831]),(0,[z0,z832,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z833]),(0,[z0,z1,z2,z3,z5,z834])],[(0,[z442,z0,z29,z1,z2,z5]),(0,[z0,z835,z2,z3,z5,z10]),(0,[z0,z277,z2,z3,z5,z477])],[(0,[z0,z1,z836,z2,z3,z5]),(0,[z0,z234,z634,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z837]),(0,[z0,z838,z1,z2,z3,z5]),(0,[z0,z839,z2,z3,z5,z10])],[(0,[z0,z840,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z841]),(0,[z0,z842,z2,z3,z5,z10]),(0,[z23,z1,z2,z3,z93,z154]),(0,[z0,z234,z2,z3,z5,z166]),(0,[z0,z29,z63,z2,z3,z5]),(0,[z0,z134,z2,z530,z5,z10])],[(0,[z0,z1,z2,z3,z5,z843]),(0,[z0,z337,z1,z2,z3,z5]),(0,[z383,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z844,z5]),(0,[z0,z256,z134,z3,z5,z10])],[(0,[z0,z225,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z845]),(0,[z155,z0,z1,z2,z5,z167]),(0,[z0,z1,z2,z3,z5,z846])],[(0,[z0,z1,z2,z3,z5,z483]),(0,[z0,z1,z2,z3,z5,z847]),(0,[z0,z1,z2,z3,z754,z10]),(0,[z0,z57,z1,z44,z2,z79]),(0,[z0,z1,z2,z3,z5,z848])],[(0,[z0,z1,z2,z849,z5,z10]),(0,[z0,z256,z226,z1,z3,z5]),(0,[z0,z2,z3,z850,z5,z10])],[(0,[z0,z1,z332,z2,z3,z6]),(0,[z0,z234,z185,z2,z3,z5]),(0,[z0,z7,z1,z2,z3,z102]),(0,[z0,z1,z44,z3,z558,z5]),(0,[z0,z123,z44,z8,z3,z5]),(0,[z0,z1,z2,z3,z5,z851]),(0,[z0,z1,z3,z5,z852,z10])],[(0,[z0,z359,z179,z2,z3,z5]),(0,[z0,z853,z1,z2,z3,z5]),(0,[z0,z29,z511,z2,z3,z5]),(0,[z0,z99,z238,z2,z3,z5]),(0,[z0,z39,z1,z3,z5,z734]),(0,[z0,z1,z2,z245,z5,z702])]],
   [[(0,[z0,z1,z44,z2,z190,z5]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z855,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z856,z5]),(0,[z0,z1,z2,z3,z857,z10])],[(0,[z0,z1,z858,z2,z3,z5]),(0,[z0,z1,z2,z3,z119,z191]),(0,[z0,z240,z95,z3,z5,z10]),(0,[z0,z1,z2,z3,z859,z5]),(0,[z0,z1,z44,z3,z5,z695])],[(0,[z0,z1,z2,z3,z5,z860]),(0,[z442,z0,z1,z2,z5,z10]),(0,[z0,z554,z2,z3,z5,z13]),(0,[z0,z2,z3,z5,z135,z861]),(0,[z0,z862,z1,z2,z3,z5])],[(0,[z1,z2,z863,z3,z5,z10]),(0,[z21,z319,z2,z77,z5,z10]),(0,[z0,z1,z864,z2,z3,z5]),(0,[z0,z234,z2,z245,z3,z5]),(0,[z0,z390,z1,z2,z435,z5])],[(0,[z865,z0,z1,z2,z5,z10]),(0,[z0,z1,z2,z801,z5,z13]),(0,[z0,z1,z2,z3,z5,z866]),(0,[z0,z1,z2,z3,z823,z10]),(0,[z0,z1,z44,z3,z5,z591])],[(0,[z0,z1,z2,z3,z867,z10]),(0,[z0,z139,z1,z2,z283,z5])],[(0,[z1,z2,z3,z5,z13,z618]),(0,[z0,z378,z1,z2,z263,z5]),(0,[z0,z58,z44,z2,z3,z5])],[],[(0,[z0,z2,z3,z5,z159,z483]),(0,[z0,z1,z2,z3,z5,z868]),(0,[z0,z869,z1,z2,z3,z5]),(0,[z0,z1,z870,z2,z3,z5]),(0,[z0,z1,z3,z5,z823,z10])],[(0,[z0,z29,z871,z2,z3,z5]),(0,[z442,z0,z7,z1,z2,z5]),(0,[z0,z406,z1,z2,z190,z10]),(0,[z0,z1,z872,z3,z5,z10]),(0,[z0,z873,z1,z2,z3,z5]),(0,[z0,z36,z2,z49,z5,z6]),(0,[z380,z1,z2,z3,z5,z6])],[(0,[z138,z69,z1,z2,z3,z5]),(0,[z0,z1,z44,z210,z3,z5]),(0,[z0,z151,z2,z3,z5,z252])],[(0,[z0,z123,z116,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z874]),(0,[z497,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z875])],[(0,[z0,z876,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z877]),(0,[z468,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z878,z5]),(0,[z0,z1,z545,z3,z5,z118]),(0,[z0,z1,z2,z3,z879,z10]),(0,[z0,z1,z880,z2,z3,z5])],[(0,[z104,z69,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z881,z10]),(0,[z0,z1,z2,z3,z5,z882]),(0,[z0,z58,z2,z3,z5,z6]),(0,[z0,z1,z883,z2,z3,z5]),(1,[z0,z1,z3,z823,z10])],[(0,[z76,z406,z1,z170,z3,z10]),(0,[z0,z1,z2,z3,z884,z5]),(0,[z0,z2,z3,z579,z5,z10]),(0,[z0,z1,z2,z3,z885,z5])]],
   [[(0,[z90,z1,z44,z2,z3,z78]),(0,[z0,z225,z2,z3,z5,z122]),(0,[z0,z604,z1,z44,z3,z5])],[(0,[z0,z1,z2,z3,z5,z507]),(0,[z0,z886,z2,z3,z5,z10])],[(0,[z442,z0,z1,z31,z5,z10]),(0,[z0,z887,z2,z3,z5,z10]),(0,[z0,z824,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z888]),(0,[z0,z1,z807,z3,z5,z10]),(0,[z0,z240,z1,z83,z3,z5]),(0,[z0,z1,z2,z3,z5,z861]),(0,[z0,z1,z2,z3,z5,z252])],[(0,[z0,z1,z2,z3,z5,z889]),(0,[z0,z1,z2,z3,z5,z890]),(0,[z0,z29,z2,z3,z5,z112]),(0,[z0,z1,z44,z3,z5,z110]),(0,[z0,z238,z2,z3,z5,z135]),(0,[z0,z1,z2,z3,z5,z734])],[(0,[z0,z359,z2,z3,z5,z10]),(0,[z0,z29,z1,z294,z3,z5]),(0,[z0,z1,z3,z5,z891,z10]),(0,[z0,z1,z44,z72,z3,z80]),(0,[z0,z461,z1,z2,z5,z67])],[(0,[z0,z1,z2,z3,z5,z892]),(0,[z0,z39,z1,z294,z3,z5]),(0,[z0,z1,z2,z3,z893,z5]),(0,[z0,z1,z44,z2,z292,z25])],[(0,[z0,z123,z1,z83,z3,z5]),(0,[z0,z1,z2,z3,z5,z894])],[(0,[z33,z0,z106,z2,z3,z5]),(0,[z0,z895,z1,z2,z3,z5]),(0,[z0,z234,z2,z8,z3,z5]),(0,[z0,z237,z1,z44,z3,z5]),(0,[z66,z0,z554,z2,z5,z67])],[(0,[z0,z89,z2,z3,z5,z841]),(0,[z0,z63,z2,z3,z5,z159])],[(0,[z33,z145,z2,z3,z5,z10]),(0,[z0,z896,z1,z2,z3,z5]),(0,[z0,z57,z29,z1,z2,z79])],[(0,[z0,z1,z2,z3,z5,z897]),(0,[z0,z1,z2,z3,z5,z40])],[(0,[z0,z1,z2,z3,z898,z10]),(0,[z0,z899,z1,z2,z3,z5])],[(0,[z27,z1,z2,z3,z5,z769]),(0,[z0,z29,z233,z2,z3,z5])],[(0,[z0,z900,z2,z3,z5,z10]),(0,[z0,z39,z1,z2,z3,z119]),(0,[z0,z1,z2,z3,z901,z5]),(0,[z0,z1,z2,z3,z5,z508])],[(0,[z0,z29,z2,z3,z5,z507]),(0,[z0,z1,z2,z3,z5,z902]),(0,[z0,z903,z1,z2,z3,z5]),(0,[z0,z904,z1,z2,z3,z5]),(0,[z0,z1,z905,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z906]),(0,[z0,z907,z1,z3,z5,z10]),(0,[z0,z1,z2,z245,z5,z740])],[(0,[z0,z1,z2,z3,z5,z908]),(0,[z0,z909,z2,z3,z5,z10]),(1,[z1,z2,z720,z5,z10]),(0,[z0,z234,z2,z3,z5,z275]),(0,[z0,z7,z103,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z910,z5]),(0,[z0,z911,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z912]),(0,[z0,z2,z37,z784,z5,z10])],[(0,[z0,z319,z488,z3,z5,z10]),(0,[z0,z913,z1,z2,z3,z5]),(0,[z0,z1,z2,z292,z25,z13]),(0,[z0,z914,z1,z2,z3,z5]),(0,[z0,z1,z44,z274,z2,z3]),(0,[z0,z24,z99,z3,z132,z10]),(0,[z0,z1,z2,z3,z915,z5])],[(0,[z33,z148,z2,z3,z5,z507]),(0,[z0,z916,z1,z2,z3,z5]),(0,[z0,z917,z1,z2,z3,z5]),(0,[z0,z123,z352,z8,z3,z10]),(0,[z0,z1,z2,z3,z5,z918])],[(0,[z0,z240,z95,z3,z5,z13]),(0,[z0,z554,z2,z3,z5,z10]),(0,[z0,z29,z2,z3,z5,z141]),(0,[z0,z29,z2,z3,z532,z5])],[(0,[z0,z256,z176,z2,z3,z10]),(0,[z0,z1,z44,z2,z3,z128]),(0,[z0,z39,z1,z515,z3,z5])],[(0,[z0,z134,z2,z263,z5,z10]),(0,[z0,z1,z2,z3,z5,z919]),(0,[z0,z1,z2,z3,z5,z920])],[(0,[z0,z1,z921,z2,z3,z5]),(0,[z0,z1,z2,z3,z922,z5]),(0,[z0,z634,z1,z2,z3,z399]),(0,[z0,z1,z923,z2,z3,z5]),(0,[z1,z2,z3,z5,z924,z10]),(0,[z0,z2,z3,z925,z5,z135])],[(0,[z76,z29,z1,z170,z3,z5]),(0,[z23,z29,z1,z2,z3,z93]),(0,[z0,z926,z1,z2,z3,z5]),(0,[z0,z927,z44,z2,z3,z5]),(0,[z0,z1,z928,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z929]),(0,[z76,z39,z1,z170,z3,z5]),(0,[z23,z39,z1,z2,z3,z93]),(0,[z0,z234,z2,z37,z3,z5]),(0,[z0,z1,z2,z245,z5,z533]),(1,[z0,z2,z3,z754,z10])],[(1,[z0,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z102,z10]),(0,[z0,z22,z44,z2,z3,z5]),(0,[z0,z1,z2,z600,z5,z18])],[(0,[z0,z234,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z930])],[(0,[z442,z0,z1,z209,z2,z5]),(0,[z0,z123,z8,z3,z5,z13]),(0,[z0,z1,z44,z83,z3,z5]),(0,[z0,z57,z7,z1,z2,z79]),(0,[z0,z1,z2,z3,z5,z931])],[(0,[z23,z1,z146,z2,z3,z10]),(0,[z0,z1,z932,z2,z3,z5]),(0,[z0,z234,z2,z3,z5,z91]),(0,[z0,z933,z1,z2,z3,z5]),(0,[z0,z240,z95,z3,z5,z120])],[(0,[z0,z1,z2,z3,z934,z10]),(0,[z0,z1,z3,z5,z935,z13]),(0,[z0,z29,z2,z3,z5,z122]),(0,[z0,z39,z1,z586,z3,z5]),(0,[z0,z1,z2,z3,z5,z936]),(0,[z0,z1,z94,z30,z128,z10]),(0,[z0,z2,z3,z786,z5,z10])],[(0,[z0,z1,z2,z3,z5,z937]),(0,[z20,z0,z234,z2,z3,z5]),(0,[z0,z938,z1,z2,z3,z5]),(0,[z0,z234,z134,z2,z3,z5]),(0,[z0,z39,z2,z3,z5,z122]),(0,[z0,z939,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z940]),(0,[z0,z1,z941,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z942])]],
   [[(0,[z0,z1,z943,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z944]),(0,[z0,z29,z2,z3,z5,z541])],[(0,[z0,z1,z2,z3,z945,z10]),(0,[z0,z1,z946,z2,z3,z10]),(0,[z0,z22,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z947]),(0,[z0,z2,z3,z579,z5,z13]),(0,[z0,z7,z9,z2,z3,z5]),(0,[z0,z39,z1,z512,z3,z5])],[(0,[z0,z1,z2,z3,z5,z948]),(0,[z0,z1,z2,z3,z949,z10]),(0,[z62,z1,z2,z720,z5,z10]),(0,[z0,z1,z2,z3,z5,z950]),(0,[z0,z29,z1,z94,z30,z5])],[(0,[z66,z0,z1,z2,z371,z5]),(0,[z0,z131,z2,z3,z5,z159])],[(0,[z0,z951,z2,z3,z5,z10]),(0,[z0,z952,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z953,z13]),(0,[z0,z7,z1,z3,z462,z5])],[(0,[z0,z24,z1,z3,z132,z6]),(0,[z0,z1,z2,z954,z3,z5]),(0,[z0,z955,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z956])],[(0,[z0,z1,z2,z3,z5,z957])],[(0,[z0,z1,z2,z3,z5,z958]),(0,[z0,z1,z478,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z322]),(0,[z0,z234,z2,z3,z5,z18]),(0,[z0,z211,z1,z2,z3,z5]),(0,[z0,z1,z2,z959,z5,z10]),(0,[z0,z1,z2,z3,z5,z960])],[(0,[z0,z234,z69,z2,z3,z5])],[(0,[z0,z1,z44,z488,z3,z5])],[(0,[z0,z1,z2,z3,z5,z961]),(0,[z0,z319,z2,z3,z5,z191]),(0,[z0,z1,z2,z3,z5,z962]),(0,[z0,z12,z44,z2,z3,z51]),(0,[z0,z1,z2,z3,z4,z257]),(0,[z0,z439,z1,z2,z3,z4])],[(0,[z76,z442,z1,z170,z5,z10]),(0,[z0,z963,z2,z3,z5,z13]),(0,[z0,z57,z1,z2,z79,z252])],[(0,[z0,z1,z2,z964,z5,z10]),(0,[z21,z198,z1,z2,z5,z10]),(0,[z62,z0,z234,z2,z3,z5]),(0,[z0,z234,z2,z3,z965,z5]),(0,[z0,z176,z2,z3,z73,z6]),(0,[z0,z131,z95,z2,z3,z5]),(0,[z343,z0,z29,z2,z3,z5]),(0,[z0,z7,z1,z2,z3,z189]),(0,[z966,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z967])],[(0,[z0,z1,z968,z3,z5,z10]),(0,[z104,z0,z871,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z969]),(0,[z0,z970,z2,z3,z5,z10])],[(0,[z0,z971,z1,z2,z3,z5]),(1,[z0,z807,z3,z5,z10]),(0,[z0,z7,z240,z95,z3,z5]),(0,[z0,z1,z2,z972,z5,z10])],[(0,[z0,z24,z99,z2,z3,z10])]],
   [[(0,[z0,z1,z2,z3,z5,z973]),(0,[z0,z409,z1,z2,z3,z5]),(0,[z0,z724,z185,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z974]),(0,[z0,z975,z1,z2,z3,z5])],[(0,[z104,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z976]),(0,[z0,z1,z2,z3,z5,z977])],[(0,[z0,z1,z2,z978,z5,z10]),(0,[z0,z979,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z980,z10]),(0,[z0,z981,z1,z2,z3,z5]),(0,[z0,z352,z1,z2,z3,z10]),(0,[z0,z1,z2,z3,z5,z982]),(0,[z0,z1,z2,z3,z5,z983]),(0,[z0,z1,z2,z292,z25,z10])],[(0,[z0,z984,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z985,z10])],[(0,[z0,z986,z1,z2,z3,z5]),(0,[z21,z1,z2,z77,z5,z6]),(0,[z0,z1,z2,z3,z987,z13]),(0,[z0,z1,z2,z3,z988,z5])],[(0,[z0,z989,z1,z2,z5,z10]),(0,[z0,z1,z2,z3,z5,z990]),(0,[z0,z991,z1,z2,z3,z5]),(0,[z0,z1,z294,z3,z119,z10]),(0,[z0,z99,z2,z3,z5,z508])],[(0,[z0,z1,z2,z3,z5,z992])],[(0,[z76,z1,z863,z3,z5,z10]),(0,[z0,z993,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z994,z5]),(0,[z107,z0,z24,z1,z3,z10]),(0,[z0,z1,z2,z3,z574,z5])],[],[(0,[z0,z1,z2,z995,z5,z10]),(0,[z0,z1,z996,z2,z3,z5]),(0,[z0,z1,z997,z3,z5,z10]),(0,[z0,z1,z2,z130,z25,z10]),(0,[z282,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z28,z166]),(0,[z0,z2,z3,z49,z5,z108]),(0,[z66,z0,z1,z2,z5,z740])],[(0,[z0,z123,z29,z8,z3,z5]),(0,[z0,z176,z2,z3,z140,z73]),(0,[z0,z927,z375,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z479])],[(0,[z0,z234,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z102,z13]),(0,[z2,z3,z5,z122,z6,z13]),(0,[z0,z1,z2,z3,z5,z998])],[(0,[z0,z1,z209,z2,z3,z5]),(0,[z62,z1,z2,z117,z5,z10]),(0,[z0,z29,z494,z2,z3,z5]),(0,[z0,z123,z8,z3,z5,z10])],[(0,[z0,z29,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z999]),(0,[z0,z1,z44,z2,z3,z102]),(0,[z136,z0,z29,z2,z3,z5]),(0,[z0,z193,z1,z434,z3,z5])],[(0,[z0,z1,z2,z3,z1000,z10]),(0,[z0,z1,z3,z5,z935,z10]),(0,[z0,z1,z2,z3,z5,z400])],[(0,[z76,z1,z170,z3,z5,z6]),(0,[z0,z2,z3,z5,z1001,z10]),(0,[z0,z1,z274,z2,z3,z10]),(0,[z0,z1002,z151,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z1003,z5,z10]),(0,[z0,z184,z1,z3,z5,z153]),(0,[z0,z1,z2,z3,z189,z6]),(0,[z0,z1,z2,z3,z1004,z5])],[(0,[z1005,z148,z2,z3,z5,z10]),(0,[z0,z234,z2,z3,z77,z5]),(0,[z0,z7,z554,z2,z3,z5]),(0,[z0,z1006,z1,z2,z3,z5]),(0,[z0,z717,z44,z2,z3,z5]),(0,[z0,z1,z2,z5,z67,z740])],[(0,[z0,z29,z1,z332,z2,z3]),(0,[z0,z1,z2,z3,z5,z1007]),(0,[z0,z24,z1,z44,z3,z132]),(0,[z0,z1,z2,z1008,z79,z10])],[(0,[z0,z39,z1,z332,z2,z3]),(0,[z0,z1,z2,z3,z119,z17]),(0,[z0,z1009,z1,z2,z3,z5]),(0,[z0,z123,z517,z3,z5,z10]),(0,[z0,z1,z2,z3,z1010,z10]),(0,[z0,z1,z2,z3,z1011,z5]),(0,[z243,z0,z1,z2,z115,z5])],[(0,[z0,z1,z2,z3,z5,z1012]),(0,[z0,z1,z2,z3,z5,z1013]),(0,[z0,z234,z2,z1014,z3,z5]),(0,[z0,z193,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z953,z10]),(0,[z1,z2,z3,z93,z708,z10]),(0,[z0,z12,z7,z2,z3,z51]),(0,[z0,z29,z1,z2,z1015,z5]),(0,[z0,z1,z2,z3,z5,z1016])],[(0,[z104,z69,z2,z3,z5,z483]),(0,[z0,z1,z2,z1017,z5,z10]),(0,[z0,z1018,z2,z3,z5,z10]),(0,[z0,z359,z332,z2,z3,z10]),(0,[z0,z1019,z2,z3,z5,z10]),(0,[z0,z1,z1020,z3,z5,z10]),(0,[z0,z57,z39,z1,z2,z79])],[(0,[z0,z1,z2,z3,z5,z1021]),(0,[z0,z24,z123,z176,z3,z10])],[(0,[z0,z1,z1022,z294,z3,z5]),(0,[z27,z1,z375,z2,z3,z5]),(0,[z155,z0,z1,z2,z5,z67]),(0,[z0,z1,z2,z3,z814,z10]),(0,[z0,z1,z2,z292,z1008,z10])],[(0,[z0,z1,z2,z3,z5,z1023]),(0,[z90,z0,z234,z2,z3,z5]),(0,[z0,z1024,z1,z2,z3,z5]),(0,[z0,z123,z251,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1025])],[(0,[z0,z1026,z1,z2,z3,z5]),(0,[z0,z2,z3,z1027,z5,z10]),(0,[z0,z2,z3,z1028,z5,z10])],[(0,[z0,z1029,z1,z2,z3,z5]),(0,[z76,z1,z209,z170,z3,z5]),(0,[z0,z2,z807,z3,z5,z10]),(0,[z0,z2,z3,z5,z10,z729])],[(0,[z0,z1030,z359,z2,z3,z5]),(0,[z0,z1,z1022,z2,z3,z5]),(0,[z0,z963,z2,z3,z5,z10]),(0,[z0,z123,z7,z8,z3,z5]),(0,[z0,z24,z1,z3,z823,z10])],[(0,[z0,z1,z2,z3,z1031,z5]),(0,[z0,z1,z294,z3,z5,z10])],[(0,[z387,z33,z29,z2,z3,z5]),(0,[z0,z1032,z1,z2,z3,z5]),(0,[z0,z277,z2,z3,z5,z40])],[(0,[z0,z1,z1033,z2,z3,z5]),(0,[z0,z29,z1,z2,z3,z119]),(0,[z0,z1,z2,z3,z5,z1034])]],
   [[(0,[z0,z2,z3,z5,z159,z507]),(0,[z23,z1,z2,z3,z93,z6]),(0,[z0,z1,z2,z3,z128,z13]),(0,[z221,z1,z2,z3,z5,z13]),(0,[z0,z29,z218,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1035]),(1,[z0,z1,z3,z5,z734])],[(0,[z104,z7,z69,z2,z3,z5]),(0,[z0,z1036,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1037]),(0,[z0,z1,z2,z3,z5,z108]),(0,[z0,z29,z2,z3,z49,z5]),(0,[z0,z1,z1038,z2,z3,z5])],[(0,[z0,z1039,z1,z2,z3,z5]),(0,[z0,z406,z1,z2,z3,z6]),(0,[z0,z1,z488,z3,z5,z6]),(0,[z21,z7,z1,z2,z77,z5]),(0,[z0,z56,z95,z2,z3,z5]),(0,[z0,z1,z72,z144,z3,z10]),(0,[z0,z1,z2,z3,z5,z1040]),(0,[z374,z184,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z415,z202]),(0,[z0,z123,z131,z2,z3,z5])],[(0,[z442,z0,z1,z2,z5,z6]),(0,[z0,z29,z1,z2,z190,z5]),(0,[z0,z352,z1,z2,z3,z13]),(0,[z0,z58,z2,z3,z5,z252])],[(0,[z0,z39,z1,z2,z190,z5]),(0,[z0,z1,z2,z3,z987,z10]),(0,[z0,z1,z2,z3,z1041,z5]),(0,[z96,z0,z137,z1,z31,z5]),(0,[z0,z1042,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z1043,z10]),(0,[z0,z29,z99,z2,z3,z5])],[(0,[z0,z314,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1044]),(0,[z505,z1,z2,z3,z5,z13]),(0,[z0,z1,z1045,z2,z3,z5]),(0,[z0,z24,z1,z3,z32,z10]),(0,[z0,z39,z99,z2,z3,z5])],[(0,[z0,z29,z2,z3,z313,z5]),(0,[z0,z1,z1046,z2,z3,z5])],[(0,[z0,z184,z824,z2,z3,z5]),(0,[z0,z1,z2,z1047,z5,z10]),(0,[z66,z0,z1,z2,z100,z5]),(0,[z0,z1,z2,z25,z1008,z10])],[(0,[z0,z744,z1,z2,z3,z6]),(0,[z0,z176,z3,z462,z73,z10]),(0,[z0,z1,z2,z3,z5,z1048])],[(0,[z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z1049])],[(0,[z0,z1,z2,z3,z5,z1050]),(0,[z0,z724,z2,z3,z5,z13]),(0,[z0,z1,z1051,z2,z3,z5]),(0,[z0,z29,z675,z2,z3,z5])],[(0,[z0,z1,z1052,z2,z3,z5]),(0,[z0,z7,z656,z2,z3,z5]),(0,[z1,z2,z3,z5,z366,z6]),(0,[z0,z36,z44,z2,z49,z5]),(0,[z521,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z729]),(0,[z521,z225,z1,z2,z3,z5]),(0,[z0,z1,z3,z959,z5,z10]),(0,[z0,z1,z2,z3,z1053,z5]),(0,[z0,z1054,z2,z3,z5,z10])],[(0,[z0,z377,z1,z2,z3,z5]),(0,[z0,z359,z44,z2,z3,z5]),(0,[z0,z1055,z1,z2,z3,z5])],[(0,[z694,z0,z29,z2,z3,z5]),(0,[z0,z1056,z2,z3,z5,z10]),(0,[z0,z234,z2,z3,z5,z159]),(0,[z0,z1,z2,z3,z1057,z10]),(0,[z0,z24,z29,z1,z3,z132]),(0,[z0,z1,z2,z3,z248,z166]),(0,[z0,z1,z2,z3,z4,z857])]],
   [[(0,[z0,z1,z2,z3,z5,z1058]),(0,[z184,z467,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z42]),(0,[z0,z29,z58,z2,z3,z5])],[(0,[z0,z1059,z2,z3,z5,z10]),(0,[z0,z1,z274,z2,z3,z13]),(0,[z0,z1,z478,z30,z3,z5]),(0,[z0,z1060,z2,z3,z5,z13]),(0,[z0,z29,z2,z3,z5,z701]),(0,[z0,z1,z2,z3,z5,z1061]),(0,[z0,z1,z44,z469,z3,z5]),(0,[z0,z1,z2,z3,z391,z5]),(0,[z0,z39,z1,z553,z3,z5]),(0,[z0,z39,z58,z2,z3,z5])],[(0,[z0,z1062,z2,z3,z5,z10]),(0,[z90,z1,z2,z3,z708,z10]),(0,[z0,z7,z176,z2,z3,z73]),(0,[z0,z1,z2,z3,z1063,z10])],[(0,[z0,z1064,z1,z2,z3,z5]),(0,[z0,z184,z724,z2,z3,z5]),(0,[z0,z1065,z1,z2,z3,z5]),(0,[z0,z1066,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z769,z10]),(0,[z0,z176,z44,z2,z3,z73]),(0,[z0,z1067,z1,z2,z3,z5])],[(0,[z0,z1,z2,z720,z5,z10]),(0,[z90,z29,z1,z2,z3,z78]),(0,[z1,z375,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1068]),(0,[z0,z1,z30,z959,z5,z10]),(0,[z0,z1069,z2,z3,z5,z10]),(0,[z0,z780,z44,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1070]),(0,[z0,z134,z2,z501,z5,z10]),(0,[z0,z22,z488,z3,z5,z10]),(0,[z90,z39,z1,z2,z3,z78]),(0,[z90,z1,z2,z3,z78,z13]),(0,[z0,z234,z2,z3,z5,z160]),(0,[z536,z1,z2,z3,z5,z13]),(0,[z0,z39,z1,z478,z3,z5]),(0,[z0,z152,z1,z2,z3,z92]),(0,[z0,z1071,z2,z3,z5,z10])],[(0,[z0,z359,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1072,z10]),(0,[z20,z39,z1,z185,z3,z5]),(0,[z0,z1,z2,z3,z1073,z10]),(0,[z0,z1,z2,z3,z5,z1074]),(0,[z0,z1,z2,z3,z5,z1075]),(0,[z0,z1076,z2,z3,z5,z10])],[(0,[z442,z0,z39,z1,z2,z5]),(0,[z0,z1,z2,z3,z5,z534]),(0,[z0,z1,z1077,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1078,z10]),(0,[z0,z1,z2,z3,z5,z1079]),(0,[z0,z1,z2,z3,z5,z1080]),(0,[z0,z1,z1020,z3,z5,z13]),(0,[z0,z29,z1,z72,z3,z80]),(0,[z0,z1081,z1,z2,z3,z5])],[(0,[z0,z1082,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z1083,z10]),(0,[z0,z15,z2,z3,z5,z13]),(0,[z0,z152,z1,z2,z3,z399]),(0,[z0,z1084,z1,z2,z3,z5]),(0,[z0,z29,z2,z3,z5,z622]),(0,[z0,z1085,z1,z2,z3,z5]),(0,[z0,z39,z1,z72,z3,z80])],[(0,[z23,z1,z2,z3,z93,z254]),(0,[z0,z1086,z1,z2,z3,z5]),(0,[z0,z29,z2,z3,z5,z729]),(0,[z0,z39,z1,z2,z292,z25])],[(0,[z0,z1087,z319,z2,z3,z5])],[(0,[z0,z1088,z1,z2,z3,z5]),(0,[z0,z1089,z1,z2,z3,z5])],[(0,[z0,z234,z2,z170,z3,z5]),(0,[z0,z1,z2,z3,z5,z1090]),(0,[z0,z1091,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1092]),(0,[z0,z0,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z1093,z5]),(0,[z0,z927,z1,z2,z3,z5]),(0,[z0,z39,z1,z3,z5,z416])],[(0,[z0,z1,z294,z3,z5,z13]),(0,[z0,z12,z2,z3,z51,z13]),(0,[z0,z409,z1,z3,z5,z157]),(0,[z241,z467,z1,z2,z3,z5]),(0,[z0,z926,z58,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z1094,z5]),(0,[z145,z69,z1,z2,z3,z5]),(0,[z0,z1,z545,z2,z3,z5])],[(0,[z104,z0,z234,z2,z3,z5]),(0,[z96,z0,z234,z2,z3,z5]),(0,[z0,z1,z478,z3,z80,z5]),(0,[z0,z1,z2,z3,z5,z1095]),(0,[z0,z24,z7,z1,z3,z132]),(0,[z0,z1,z2,z3,z128,z10]),(0,[z0,z1,z94,z959,z5,z10])],[(0,[z0,z1096,z1,z2,z3,z5]),(0,[z0,z226,z1,z2,z3,z5]),(0,[z0,z277,z2,z3,z128,z10]),(0,[z0,z1,z2,z3,z70,z382])],[(0,[z0,z1,z2,z3,z5,z1097]),(0,[z0,z134,z44,z2,z37,z5]),(0,[z0,z1,z2,z3,z5,z1098]),(0,[z0,z1,z44,z3,z462,z5])],[(0,[z0,z1099,z1,z2,z3,z5]),(0,[z0,z1,z94,z576,z5,z10]),(0,[z0,z1100,z2,z3,z5,z10]),(0,[z0,z1101,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1102,z5]),(1,[z0,z1,z959,z5,z10])],[(0,[z0,z1,z3,z1103,z5,z10]),(0,[z0,z106,z134,z2,z3,z5]),(1,[z1,z2,z3,z708,z10]),(0,[z0,z123,z3,z315,z5,z10]),(0,[z0,z29,z1,z274,z2,z3]),(0,[z0,z1104,z1,z2,z3,z10]),(0,[z0,z1,z2,z3,z1105,z5])],[(0,[z0,z337,z2,z3,z49,z5]),(0,[z0,z1,z2,z3,z1106,z10]),(0,[z0,z1107,z2,z3,z5,z10]),(0,[z0,z1,z209,z332,z2,z3]),(0,[z0,z993,z1,z294,z3,z5]),(0,[z0,z240,z352,z1,z3,z10]),(0,[z0,z39,z1,z274,z2,z3]),(0,[z0,z1,z1108,z2,z3,z5]),(0,[z0,z12,z29,z2,z3,z51])],[(0,[z0,z123,z39,z8,z3,z5])],[(0,[z21,z1,z488,z77,z5,z10]),(0,[z0,z176,z2,z3,z754,z10]),(0,[z0,z29,z1,z2,z3,z128]),(0,[z0,z1,z2,z3,z5,z1109]),(0,[z0,z1,z1110,z2,z3,z5])],[(0,[z0,z1,z2,z1111,z5,z10]),(0,[z0,z39,z1,z2,z3,z128]),(0,[z0,z1112,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z1113,z5])],[(1,[z1005,z2,z3,z5,z10]),(0,[z0,z123,z352,z1,z3,z10]),(0,[z0,z1,z2,z3,z1114,z5]),(0,[z0,z1,z2,z3,z189,z477])],[(0,[z0,z1,z1115,z3,z5,z10]),(0,[z0,z1116,z1,z2,z3,z5]),(0,[z0,z1117,z1,z2,z3,z10]),(0,[z0,z1,z44,z2,z3,z189]),(0,[z0,z1002,z1,z2,z3,z5])],[(0,[z0,z356,z1,z2,z3,z4]),(0,[z156,z0,z1,z2,z3,z248])],[(0,[z0,z724,z2,z3,z5,z10]),(0,[z0,z319,z2,z3,z102,z10]),(0,[z0,z1,z1118,z2,z3,z5]),(0,[z0,z220,z7,z2,z3,z5])],[(0,[z0,z22,z2,z3,z5,z191]),(0,[z0,z1119,z1,z2,z3,z5])],[(0,[z449,z0,z29,z2,z3,z5]),(0,[z0,z1,z3,z462,z5,z6]),(0,[z0,z1,z2,z3,z5,z1120])]],
   [[(0,[z0,z29,z22,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1121]),(0,[z0,z1122,z1,z2,z3,z5]),(0,[z0,z99,z3,z80,z5,z10])],[(0,[z0,z39,z22,z2,z3,z5]),(0,[z0,z1,z2,z3,z1123,z5])],[(0,[z104,z106,z69,z2,z3,z5]),(0,[z0,z184,z1,z2,z3,z5]),(0,[z0,z1060,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z1124,z10])],[(0,[z0,z1125,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1126]),(0,[z62,z1,z2,z117,z5,z262]),(0,[z0,z1,z72,z3,z437,z10]),(0,[z0,z1127,z1,z2,z3,z5])],[(0,[z0,z1128,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z769,z13]),(0,[z0,z1,z2,z3,z1129,z5]),(0,[z0,z1,z2,z3,z5,z1130]),(0,[z0,z7,z2,z3,z5,z159])],[(0,[z0,z1,z2,z3,z5,z1131]),(0,[z90,z1,z2,z3,z78,z10]),(0,[z0,z29,z297,z2,z3,z5]),(0,[z0,z1,z2,z3,z1132,z10]),(0,[z0,z1,z3,z1133,z5,z10])],[(0,[z0,z1,z2,z3,z708,z10]),(0,[z0,z780,z375,z2,z3,z5])],[(0,[z0,z1,z209,z2,z190,z5])],[(1,[z0,z829,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1134]),(0,[z0,z1135,z1,z2,z3,z5]),(0,[z0,z234,z240,z2,z3,z5]),(1,[z0,z2,z3,z5,z729]),(0,[z96,z0,z1,z959,z5,z10])],[(0,[z0,z89,z2,z190,z5,z10]),(0,[z21,z22,z2,z77,z5,z10]),(0,[z0,z15,z2,z3,z5,z10]),(0,[z0,z1136,z1,z2,z3,z5]),(0,[z60,z1,z375,z2,z3,z5]),(1,[z0,z1,z2,z1008,z10])],[(0,[z33,z0,z29,z2,z3,z5]),(0,[z0,z1137,z1,z2,z3,z5]),(0,[z0,z1138,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1139]),(0,[z0,z1,z2,z3,z5,z1140])],[(0,[z0,z1005,z2,z3,z5,z10])],[(0,[z0,z218,z69,z2,z3,z5]),(0,[z0,z1,z2,z190,z5,z13]),(0,[z0,z29,z1,z488,z3,z5]),(0,[z0,z1,z2,z1141,z3,z5])],[(0,[z0,z1,z2,z3,z1142,z5]),(0,[z0,z1,z2,z1143,z5,z10]),(0,[z0,z1,z2,z3,z5,z1144]),(0,[z0,z39,z1,z488,z3,z5]),(0,[z0,z134,z56,z2,z3,z5])],[(0,[z104,z171,z2,z3,z5,z10]),(0,[z76,z467,z1,z2,z3,z5]),(0,[z0,z829,z1,z2,z3,z5])]],
   [[(0,[z271,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1145]),(0,[z0,z234,z2,z3,z5,z239]),(0,[z598,z0,z234,z2,z3,z5]),(0,[z143,z0,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z1146,z5]),(0,[z0,z1,z2,z3,z5,z1147]),(0,[z0,z12,z2,z3,z51,z10]),(0,[z0,z1148,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z508,z135])],[(0,[z0,z1149,z1,z2,z3,z5]),(0,[z0,z1,z2,z5,z1150,z10]),(0,[z0,z1151,z1,z2,z3,z5]),(0,[z598,z0,z1,z2,z5,z91]),(0,[z0,z1152,z2,z3,z5,z13]),(0,[z0,z134,z2,z3,z5,z108]),(0,[z0,z1,z3,z5,z346,z734])],[(0,[z0,z29,z2,z3,z580,z5]),(0,[z0,z1,z94,z30,z5,z13]),(0,[z0,z1,z2,z3,z1153,z5]),(0,[z0,z1,z44,z3,z147,z5])],[(0,[z0,z1087,z1,z2,z3,z5]),(0,[z0,z56,z1,z2,z3,z5]),(0,[z0,z240,z1,z545,z3,z5])],[(0,[z0,z1154,z1,z2,z3,z5]),(0,[z0,z1,z2,z292,z25,z6])],[(0,[z0,z1,z2,z5,z1155,z10]),(0,[z0,z234,z44,z2,z3,z5]),(0,[z0,z1156,z1,z2,z3,z5]),(0,[z0,z63,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1157])],[(0,[z0,z234,z2,z3,z28,z5]),(0,[z0,z240,z95,z3,z5,z6])],[(0,[z76,z359,z170,z3,z5,z10]),(0,[z0,z1158,z1,z2,z3,z5]),(0,[z0,z123,z1,z545,z3,z5]),(0,[z0,z1,z2,z3,z5,z1159]),(0,[z0,z1160,z1,z2,z3,z5])],[(0,[z467,z1,z185,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1161]),(0,[z0,z234,z72,z2,z3,z5])],[(0,[z442,z0,z1,z332,z2,z10]),(0,[z0,z1,z2,z3,z5,z1162]),(0,[z865,z0,z1,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1163]),(0,[z0,z1,z1164,z2,z3,z5]),(0,[z0,z2,z3,z5,z10,z1165])],[(0,[z0,z234,z184,z2,z3,z5]),(0,[z0,z1,z2,z1111,z5,z13]),(0,[z0,z234,z2,z3,z5,z118]),(0,[z0,z1,z2,z3,z5,z1166]),(0,[z0,z1,z395,z2,z379,z5])],[(0,[z62,z0,z829,z2,z3,z5])],[(0,[z0,z1167,z2,z3,z5,z10]),(0,[z0,z234,z2,z3,z5,z6])],[(0,[z0,z1,z1168,z2,z3,z5]),(0,[z62,z1,z2,z117,z5,z6]),(0,[z0,z1160,z151,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1169]),(0,[z0,z1,z2,z3,z5,z1170]),(0,[z694,z0,z234,z2,z3,z5])]],
   [[(0,[z0,z145,z1,z2,z3,z5]),(0,[z0,z29,z519,z2,z3,z5]),(0,[z0,z7,z2,z3,z5,z451])],[(0,[z0,z29,z1,z2,z3,z102]),(0,[z372,z0,z1,z44,z3,z5]),(0,[z0,z1,z2,z3,z5,z1171]),(0,[z0,z1172,z2,z3,z5,z10])],[(0,[z0,z39,z1,z2,z3,z102]),(0,[z0,z1,z2,z3,z98,z5]),(0,[z0,z39,z1,z684,z3,z5])],[(0,[z0,z1173,z1,z2,z3,z5]),(0,[z0,z1174,z1,z3,z5,z10]),(0,[z1175,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z70,z302])],[(0,[z33,z29,z148,z2,z3,z5]),(0,[z0,z2,z3,z579,z5,z6]),(0,[z0,z1,z577,z2,z3,z5]),(0,[z493,z1,z196,z2,z3,z5])],[(0,[z33,z39,z148,z2,z3,z5]),(0,[z0,z1,z2,z3,z714,z5]),(0,[z0,z1,z2,z3,z5,z1176])],[(0,[z0,z1,z1177,z3,z5,z10]),(0,[z0,z151,z2,z3,z5,z367])],[(0,[z0,z234,z152,z2,z3,z5]),(0,[z0,z1,z2,z3,z1178,z5])],[(0,[z0,z29,z2,z329,z3,z5]),(0,[z0,z1179,z1,z2,z3,z5]),(0,[z0,z1,z2,z133,z5,z533])],[(0,[z0,z1180,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1181]),(0,[z0,z36,z29,z2,z49,z5])],[(0,[z0,z1182,z1,z2,z3,z5]),(0,[z0,z359,z29,z2,z3,z5]),(0,[z0,z24,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1183]),(0,[z0,z1,z83,z3,z5,z346])],[(0,[z0,z234,z95,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1184]),(0,[z0,z1,z44,z587,z3,z5]),(0,[z0,z39,z1185,z2,z3,z5])],[(0,[z0,z1,z1186,z2,z3,z5]),(0,[z0,z1187,z1,z2,z3,z5]),(0,[z0,z1188,z1,z2,z3,z5]),(0,[z0,z1189,z1,z2,z3,z5]),(0,[z0,z29,z1,z2,z292,z25]),(0,[z0,z2,z3,z5,z159,z729])],[(0,[z0,z29,z2,z660,z3,z5])],[(0,[z0,z1,z2,z190,z5,z10]),(0,[z0,z1,z2,z3,z5,z367])],[(0,[z0,z1,z488,z3,z5,z191]),(0,[z0,z1,z2,z3,z1190,z10]),(0,[z0,z1191,z1,z2,z3,z5]),(0,[z0,z1,z2,z172,z25,z10])]],
   [[(0,[z0,z1,z1192,z3,z5,z10]),(0,[z104,z0,z145,z2,z3,z5]),(0,[z0,z1,z836,z488,z3,z5]),(0,[z0,z1193,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z13,z1194]),(0,[z0,z131,z1,z2,z3,z5]),(0,[z0,z1195,z1,z2,z3,z5]),(0,[z0,z554,z44,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1196])],[(0,[z0,z1,z2,z3,z5,z1197]),(0,[z0,z319,z294,z3,z5,z10]),(0,[z0,z1198,z2,z3,z5,z10])],[(0,[z0,z1152,z2,z3,z5,z10]),(0,[z0,z234,z2,z3,z4,z5]),(0,[z0,z29,z2,z3,z714,z5]),(0,[z0,z63,z15,z2,z3,z5]),(0,[z0,z1199,z1,z2,z3,z5])],[(0,[z0,z234,z225,z2,z3,z5]),(0,[z0,z1200,z2,z3,z5,z10]),(0,[z0,z478,z2,z3,z5,z122]),(0,[z0,z211,z2,z3,z49,z5]),(0,[z0,z240,z44,z95,z3,z5]),(0,[z0,z1,z2,z3,z5,z1201]),(0,[z0,z12,z39,z2,z3,z51]),(0,[z0,z1,z94,z30,z5,z10]),(0,[z0,z1,z2,z3,z1202,z10])],[(0,[z442,z0,z406,z1,z2,z10]),(0,[z293,z1,z2,z3,z93,z10]),(0,[z0,z1,z2,z3,z1203,z5]),(0,[z0,z2,z3,z5,z135,z10]),(0,[z0,z1204,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1205]),(0,[z0,z7,z352,z1,z2,z3]),(0,[z0,z1,z2,z3,z5,z1206]),(0,[z0,z137,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1207])],[(0,[z374,z1,z2,z3,z5,z13]),(0,[z0,z1,z1208,z2,z3,z5])],[(0,[z0,z1209,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1210])],[(0,[z0,z1211,z1,z2,z3,z10]),(0,[z0,z1,z2,z3,z1212,z10]),(0,[z0,z554,z2,z3,z5,z6]),(0,[z0,z1,z2,z245,z5,z61])],[(0,[z0,z1,z1213,z2,z3,z5]),(0,[z0,z29,z316,z2,z3,z5])],[(0,[z76,z1,z375,z2,z3,z5]),(0,[z442,z0,z1,z488,z5,z10]),(0,[z0,z1214,z2,z3,z5,z10]),(0,[z0,z356,z1,z2,z3,z186]),(0,[z0,z1,z2,z3,z5,z1215]),(0,[z0,z260,z1,z2,z3,z200])],[(0,[z0,z36,z7,z2,z49,z5]),(0,[z0,z1,z1216,z2,z3,z5])],[(0,[z0,z359,z7,z2,z3,z5]),(0,[z0,z256,z3,z49,z5,z10]),(0,[z0,z1217,z2,z3,z5,z10]),(0,[z0,z1204,z2,z3,z579,z5]),(0,[z0,z39,z1,z44,z3,z5]),(0,[z0,z39,z1,z222,z3,z5])],[(0,[z0,z406,z179,z1,z2,z3]),(0,[z0,z1218,z1,z2,z3,z5]),(0,[z0,z1219,z1,z2,z3,z5]),(0,[z0,z29,z2,z3,z5,z304]),(0,[z0,z12,z2,z3,z574,z51])],[(0,[z0,z1,z2,z3,z102,z6]),(0,[z0,z256,z3,z51,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1220]),(0,[z0,z319,z2,z3,z5,z17])]],
   [[(0,[z104,z33,z29,z2,z3,z5])],[(0,[z0,z1221,z2,z3,z5,z10]),(0,[z0,z1,z2,z1222,z5,z10]),(0,[z0,z1,z2,z3,z5,z1223])],[(0,[z0,z89,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z1224])],[(0,[z0,z1,z2,z3,z5,z1225]),(0,[z0,z1226,z359,z2,z3,z5]),(0,[z0,z1227,z319,z2,z3,z5]),(0,[z0,z1,z1228,z2,z3,z5]),(0,[z96,z0,z1,z31,z5,z13]),(0,[z0,z1,z2,z3,z1229,z5]),(0,[z0,z1,z2,z283,z5,z61])],[(0,[z0,z1,z196,z2,z3,z5]),(0,[z467,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z1230])],[(0,[z0,z1231,z1,z2,z3,z5]),(0,[z0,z1,z1232,z2,z3,z5]),(0,[z0,z1,z2,z1015,z5,z10]),(0,[z0,z29,z608,z2,z3,z5])],[(0,[z0,z1233,z2,z3,z5,z10]),(0,[z0,z29,z71,z2,z3,z5])],[(0,[z0,z1234,z2,z3,z5,z10]),(0,[z0,z1235,z1,z2,z3,z5]),(0,[z0,z234,z2,z3,z25,z5]),(0,[z0,z234,z2,z3,z399,z5]),(0,[z0,z1,z196,z3,z5,z485]),(0,[z0,z12,z2,z3,z754,z10]),(0,[z0,z1,z1236,z2,z3,z5]),(0,[z0,z1,z2,z3,z1237,z5]),(0,[z0,z1,z2,z3,z857,z5])],[(0,[z0,z2,z3,z5,z1238,z10]),(0,[z0,z12,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1239])],[(0,[z33,z337,z148,z2,z3,z5]),(0,[z0,z1,z2,z3,z1240,z10]),(0,[z0,z1241,z1,z2,z3,z5]),(0,[z0,z1242,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z1243,z13])],[(0,[z0,z1,z2,z3,z5,z1244]),(0,[z0,z1245,z2,z3,z5,z10]),(0,[z0,z1246,z1,z2,z3,z10]),(0,[z0,z234,z1247,z2,z3,z5]),(0,[z0,z1248,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1249,z5]),(0,[z0,z414,z1,z2,z197,z5]),(0,[z0,z1,z2,z3,z1250,z5])],[(0,[z0,z1251,z1,z2,z3,z5])],[(0,[z0,z1252,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1253]),(0,[z0,z1254,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1255]),(0,[z0,z123,z274,z8,z3,z10]),(0,[z0,z29,z134,z2,z49,z5]),(0,[z0,z29,z131,z2,z3,z5])],[(0,[z0,z1256,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1257,z10]),(0,[z0,z1258,z1,z2,z3,z5]),(0,[z0,z123,z425,z3,z5,z10])],[(0,[z0,z2,z3,z5,z122,z10]),(0,[z0,z7,z89,z2,z3,z5]),(0,[z0,z1,z2,z3,z119,z13]),(0,[z0,z24,z1,z3,z268,z10]),(0,[z0,z1,z35,z2,z3,z5]),(0,[z1,z2,z3,z1259,z5,z10]),(1,[z0,z2,z784,z5,z10]),(0,[z0,z29,z2,z540,z3,z5]),(0,[z0,z39,z1,z545,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1260]),(0,[z0,z1261,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1262]),(0,[z0,z1,z2,z504,z79,z10])]],
   [[(0,[z0,z1030,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z626,z166])],[(0,[z0,z1,z1263,z2,z3,z5]),(0,[z0,z1264,z1,z2,z3,z5]),(0,[z0,z22,z2,z3,z102,z10]),(0,[z138,z1,z2,z3,z5,z13]),(0,[z0,z2,z784,z49,z5,z10]),(0,[z0,z56,z2,z3,z5,z112]),(0,[z0,z1,z2,z3,z5,z1265])],[(0,[z104,z1005,z2,z3,z5,z10]),(0,[z104,z0,z56,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1266]),(0,[z0,z7,z417,z2,z3,z5]),(0,[z232,z0,z29,z2,z3,z5]),(0,[z0,z1,z2,z3,z1008,z10])],[(0,[z0,z1198,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z128,z6]),(0,[z0,z7,z134,z2,z37,z5])],[(0,[z0,z1,z478,z185,z3,z5]),(0,[z21,z1,z2,z77,z5,z191]),(0,[z0,z39,z1,z661,z3,z5]),(0,[z0,z1,z2,z3,z5,z723])],[(0,[z33,z148,z2,z3,z5,z10]),(0,[z104,z0,z2,z3,z5,z108]),(0,[z0,z1200,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z5,z1267]),(0,[z0,z1268,z1,z2,z3,z5])],[(0,[z0,z2,z3,z5,z135,z13]),(0,[z0,z2,z3,z579,z189,z10])],[(0,[z0,z1,z2,z3,z5,z1269]),(0,[z0,z234,z2,z3,z5,z346]),(0,[z0,z352,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z1270]),(0,[z0,z1,z2,z3,z5,z1271]),(0,[z0,z29,z1,z3,z462,z5]),(0,[z0,z57,z1,z2,z79,z367])],[(0,[z0,z36,z63,z2,z49,z5]),(0,[z0,z39,z1,z3,z462,z5]),(0,[z66,z0,z1,z2,z5,z67])],[(0,[z33,z29,z145,z2,z3,z5]),(0,[z0,z1,z2,z3,z1272,z5]),(0,[z0,z1273,z256,z1,z3,z5]),(0,[z0,z1274,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1275,z5]),(0,[z0,z184,z2,z3,z5,z122]),(0,[z0,z193,z56,z2,z3,z5]),(0,[z0,z123,z352,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1276]),(0,[z0,z1,z2,z3,z70,z228]),(0,[z0,z1,z2,z3,z5,z1277]),(0,[z0,z1,z44,z3,z700,z5])],[(0,[z96,z0,z1,z478,z3,z5]),(0,[z0,z7,z2,z3,z5,z135])],[(0,[z0,z1,z1278,z2,z3,z5])],[(0,[z0,z95,z446,z3,z5,z10]),(0,[z0,z1,z1279,z2,z3,z5]),(0,[z0,z1,z2,z5,z1280,z10]),(0,[z0,z409,z1,z185,z3,z5]),(0,[z0,z1,z3,z80,z605,z10]),(0,[z0,z39,z1281,z2,z3,z5]),(0,[z0,z152,z1,z2,z3,z460])],[(0,[z0,z1282,z1,z2,z5,z10]),(0,[z27,z234,z2,z3,z5,z13]),(0,[z0,z151,z2,z3,z5,z13]),(0,[z0,z2,z3,z784,z5,z10]),(0,[z0,z2,z3,z579,z5,z477])],[(0,[z0,z29,z1,z2,z3,z189]),(0,[z0,z1,z2,z3,z1283,z5]),(0,[z0,z24,z39,z1,z3,z132])]],
   [[(0,[z0,z352,z1,z577,z2,z3]),(0,[z0,z1,z2,z3,z1284,z5]),(0,[z0,z1,z2,z3,z5,z1285]),(0,[z0,z1,z1286,z2,z3,z5]),(0,[z0,z39,z1,z2,z3,z189]),(0,[z0,z44,z2,z3,z5,z135])],[(0,[z0,z1,z2,z3,z5,z208]),(0,[z0,z1,z2,z5,z1287,z10]),(0,[z0,z123,z8,z3,z5,z6]),(0,[z0,z218,z2,z3,z5,z436]),(0,[z0,z211,z1,z83,z3,z5]),(0,[z0,z1,z83,z2,z3,z5]),(0,[z0,z1,z2,z3,z189,z40])],[(0,[z104,z0,z337,z2,z3,z5]),(0,[z0,z39,z240,z95,z3,z5]),(0,[z0,z134,z2,z784,z5,z10]),(0,[z0,z1288,z1,z2,z3,z5]),(0,[z285,z0,z1,z2,z100,z5])],[(0,[z0,z1,z2,z3,z1289,z10]),(0,[z0,z89,z2,z3,z5,z10]),(0,[z0,z1,z3,z1290,z5,z10]),(0,[z0,z1,z2,z5,z1008,z10])],[(0,[z21,z1,z2,z77,z102,z10]),(0,[z21,z1,z44,z2,z77,z5]),(0,[z0,z1,z1291,z2,z3,z5]),(0,[z143,z138,z1,z2,z3,z5]),(0,[z0,z1,z274,z2,z3,z6]),(0,[z96,z0,z1,z31,z5,z10])],[(0,[z0,z1,z2,z784,z5,z10]),(0,[z0,z1292,z256,z1,z3,z5])],[(0,[z0,z1,z2,z3,z5,z13]),(0,[z0,z36,z39,z2,z49,z5])],[(1,[z33,z145,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1293]),(0,[z0,z1294,z1,z2,z3,z5])],[(0,[z0,z1295,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1296]),(0,[z0,z1297,z1,z2,z3,z5]),(0,[z90,z1,z2,z3,z78,z6]),(0,[z0,z29,z1,z2,z3,z1298]),(0,[z0,z1281,z2,z3,z5,z10])],[(0,[z0,z145,z2,z3,z49,z5])],[(0,[z0,z1299,z1,z3,z5,z10]),(0,[z0,z1,z2,z3,z1300,z10]),(0,[z0,z1096,z22,z2,z3,z5]),(0,[z0,z2,z3,z5,z1243,z10]),(0,[z0,z1,z2,z3,z1301,z5]),(0,[z0,z29,z84,z2,z3,z5])],[(0,[z0,z1227,z1,z2,z3,z5]),(0,[z0,z1019,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1302])],[(0,[z0,z1303,z1,z2,z3,z5]),(0,[z0,z1304,z1,z2,z3,z5]),(0,[z0,z15,z2,z3,z5,z6]),(0,[z0,z56,z2,z3,z5,z73])],[(0,[z90,z1,z2,z3,z78,z410]),(0,[z0,z807,z8,z3,z5,z10])],[(0,[z104,z0,z211,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1305]),(0,[z0,z420,z1,z2,z79,z10]),(0,[z0,z234,z2,z3,z93,z5]),(0,[z0,z1,z44,z3,z5,z118])],[(0,[z0,z1,z2,z3,z119,z10]),(0,[z27,z0,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z120])]],
   [[(0,[z0,z2,z3,z5,z122,z13])],[(0,[z0,z1,z2,z3,z5,z126]),(0,[z0,z1,z2,z3,z5,z1306]),(0,[z0,z1,z2,z3,z5,z1307]),(0,[z0,z68,z7,z2,z3,z5])],[(0,[z0,z1,z294,z3,z5,z6]),(0,[z1,z2,z3,z543,z5,z6])],[(0,[z0,z1,z2,z3,z5,z129]),(0,[z0,z1,z2,z3,z5,z1308]),(0,[z0,z234,z2,z3,z5,z1309]),(0,[z0,z234,z7,z2,z3,z5]),(0,[z0,z1,z2,z5,z1150,z6]),(0,[z0,z1310,z1,z2,z3,z5])],[(0,[z0,z179,z89,z2,z3,z5]),(0,[z0,z2,z3,z5,z1083,z262])],[(0,[z0,z179,z1,z2,z3,z5]),(0,[z62,z1,z2,z405,z5,z10]),(0,[z0,z1311,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1312]),(0,[z0,z403,z1,z545,z3,z5]),(0,[z0,z39,z554,z2,z3,z5]),(0,[z66,z0,z15,z2,z5,z67])],[],[(0,[z33,z148,z2,z3,z5,z13]),(0,[z0,z29,z134,z2,z3,z5]),(0,[z0,z277,z94,z30,z5,z10])],[(0,[z0,z1,z2,z3,z28,z160]),(0,[z0,z99,z72,z2,z3,z10])],[(0,[z0,z1,z72,z3,z80,z13])],[(0,[z33,z377,z148,z2,z3,z5]),(0,[z0,z1,z1313,z2,z3,z5]),(0,[z0,z57,z234,z2,z3,z5])],[(0,[z0,z29,z2,z3,z339,z5]),(0,[z0,z1,z2,z3,z1314,z10]),(0,[z0,z1,z2,z3,z5,z1315]),(0,[z168,z1,z170,z3,z5,z10]),(0,[z0,z1,z1316,z2,z3,z5]),(0,[z1,z2,z3,z5,z560,z6]),(0,[z398,z1,z2,z3,z5,z6]),(0,[z0,z256,z1,z3,z5,z10]),(0,[z0,z29,z390,z2,z3,z5]),(0,[z0,z1317,z1,z2,z3,z5]),(0,[z0,z1,z1318,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z82]),(0,[z96,z0,z1,z44,z31,z5]),(0,[z0,z1,z2,z3,z5,z1319])],[(0,[z33,z145,z1,z2,z3,z5]),(0,[z0,z1,z1320,z2,z3,z5])],[(0,[z0,z1,z1321,z2,z3,z5]),(0,[z0,z1,z2,z3,z1322,z5])],[(0,[z0,z1323,z1,z2,z3,z5]),(0,[z0,z1,z2,z5,z1280,z13]),(0,[z0,z1,z2,z3,z1324,z5]),(0,[z0,z151,z2,z3,z5,z10])]],
   [[(0,[z0,z1,z1325,z2,z3,z5]),(0,[z0,z1326,z1,z2,z3,z5]),(0,[z0,z1199,z99,z2,z3,z5]),(0,[z0,z58,z2,z3,z5,z367])],[(0,[z0,z1,z1327,z2,z3,z5]),(0,[z0,z1328,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1329]),(0,[z96,z0,z1,z391,z31,z5])],[(0,[z0,z1,z488,z3,z102,z10]),(0,[z0,z1,z2,z3,z5,z154]),(0,[z0,z176,z2,z3,z268,z10])],[(0,[z0,z1,z2,z1330,z3,z10]),(0,[z0,z1,z2,z3,z1331,z10]),(0,[z0,z1332,z234,z2,z3,z5]),(0,[z0,z1333,z1,z2,z3,z5])],[(0,[z104,z29,z69,z2,z3,z5]),(0,[z0,z1334,z1,z2,z3,z5])],[(0,[z0,z138,z1,z2,z3,z5]),(0,[z104,z39,z69,z2,z3,z5]),(0,[z0,z1,z2,z1335,z5,z10]),(0,[z0,z22,z294,z3,z5,z10]),(0,[z0,z1336,z1,z2,z3,z5]),(0,[z0,z607,z1,z2,z3,z92])],[(0,[z21,z1,z2,z720,z5,z10]),(0,[z21,z39,z1,z2,z77,z5]),(0,[z1,z2,z3,z720,z5,z10]),(0,[z0,z240,z95,z3,z5,z404])],[(0,[z0,z1,z2,z3,z5,z10]),(0,[z0,z218,z2,z3,z5,z159]),(0,[z0,z1,z1337,z2,z3,z5]),(0,[z0,z256,z1,z44,z3,z5]),(0,[z0,z1338,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z1339,z5]),(0,[z0,z277,z2,z3,z5,z10]),(1,[z0,z1,z2,z3,z857])],[(0,[z0,z2,z3,z1340,z5,z10]),(0,[z0,z1,z2,z3,z5,z1341])],[(0,[z33,z0,z145,z2,z3,z5]),(0,[z0,z1342,z2,z3,z5,z10]),(0,[z0,z1,z1343,z2,z3,z5]),(0,[z0,z1,z3,z5,z734,z10])],[(0,[z0,z1,z44,z3,z419,z5]),(0,[z0,z1,z2,z3,z5,z1344]),(0,[z0,z1,z3,z140,z462,z5])],[(0,[z0,z234,z2,z600,z3,z5]),(0,[z0,z1,z2,z3,z5,z97]),(0,[z0,z1,z2,z3,z1345,z5])],[(0,[z0,z1,z2,z3,z128,z477])],[(0,[z33,z0,z234,z2,z3,z5]),(0,[z0,z99,z2,z3,z5,z13])],[(0,[z0,z234,z2,z3,z5,z153]),(0,[z0,z57,z1,z2,z79,z13]),(0,[z0,z1346,z1,z2,z3,z5]),(0,[z0,z1347,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z190,z5,z6]),(0,[z0,z1,z94,z582,z5,z10]),(0,[z0,z218,z95,z2,z3,z5]),(0,[z0,z1,z2,z3,z178,z5]),(0,[z0,z1,z2,z3,z5,z1348]),(0,[z0,z1,z2,z3,z5,z1349]),(0,[z0,z1,z1350,z2,z3,z5])],[(0,[z0,z1,z2,z1351,z5,z10]),(0,[z111,z0,z234,z2,z3,z5]),(0,[z0,z1,z577,z274,z2,z3])],[(0,[z0,z7,z1,z2,z3,z5]),(0,[z104,z2,z3,z5,z366,z10]),(0,[z0,z1,z2,z3,z5,z1352]),(0,[z0,z89,z2,z3,z5,z1308]),(0,[z0,z1,z2,z3,z1353,z5]),(0,[z0,z36,z2,z98,z49,z5]),(0,[z0,z2,z3,z49,z5,z55])],[(0,[z1005,z1,z2,z3,z5,z10]),(0,[z0,z22,z2,z3,z5,z17]),(0,[z0,z1,z1354,z2,z3,z5]),(0,[z0,z1355,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1356])],[(0,[z0,z36,z234,z2,z3,z5]),(0,[z0,z24,z1,z478,z3,z5]),(0,[z0,z1357,z1,z2,z3,z5]),(0,[z0,z2,z3,z1250,z579,z5])],[(0,[z0,z756,z2,z3,z5,z10]),(0,[z0,z24,z1,z425,z3,z10]),(0,[z0,z29,z176,z2,z3,z73])],[(0,[z0,z1,z2,z3,z5,z1358]),(0,[z0,z44,z89,z2,z3,z5]),(0,[z0,z1,z1359,z2,z3,z10]),(0,[z0,z39,z176,z2,z3,z73]),(0,[z0,z1360,z2,z3,z5,z10])],[(0,[z387,z106,z1,z2,z3,z5]),(0,[z0,z431,z1,z2,z3,z228])],[(0,[z0,z406,z1,z44,z2,z3]),(0,[z21,z1,z294,z77,z5,z10]),(0,[z0,z1,z1361,z2,z3,z5]),(0,[z0,z1362,z1,z2,z3,z5])],[(0,[z0,z234,z2,z292,z3,z5]),(0,[z0,z123,z352,z2,z3,z10]),(0,[z0,z29,z388,z2,z3,z5]),(0,[z0,z7,z151,z2,z3,z5]),(0,[z0,z1,z2,z3,z857,z70]),(0,[z0,z1363,z2,z3,z5,z10])],[(0,[z0,z234,z2,z117,z3,z5]),(0,[z0,z430,z2,z49,z5,z10]),(0,[z0,z7,z2,z3,z579,z5]),(0,[z0,z1,z72,z3,z80,z10])],[(0,[z0,z1,z1364,z2,z3,z5]),(0,[z0,z1,z2,z3,z102,z191])],[(0,[z232,z148,z2,z3,z5,z10]),(0,[z0,z337,z134,z2,z3,z5]),(0,[z0,z1,z1365,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1366])],[(0,[z1,z2,z3,z5,z6,z13]),(0,[z0,z256,z1,z3,z5,z13]),(0,[z0,z1,z1367,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1368])],[(0,[z66,z0,z234,z2,z3,z5]),(0,[z0,z56,z2,z3,z49,z5]),(0,[z0,z7,z277,z2,z3,z5]),(0,[z0,z1,z72,z3,z80,z97]),(0,[z0,z1,z1369,z2,z3,z5])]],
   [[(0,[z0,z2,z3,z49,z140,z5])],[(0,[z0,z1,z2,z3,z1370,z10]),(0,[z0,z184,z1,z478,z3,z5]),(0,[z27,z145,z1,z2,z3,z5]),(0,[z0,z134,z83,z2,z3,z5]),(0,[z0,z1148,z99,z2,z3,z5]),(0,[z0,z1371,z2,z3,z5,z10])],[(0,[z104,z0,z83,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z38]),(0,[z0,z1,z2,z3,z5,z1372]),(0,[z0,z1,z2,z3,z5,z1373])],[(0,[z0,z1374,z2,z3,z5,z10]),(0,[z0,z2,z3,z5,z10,z1375])],[(0,[z0,z29,z240,z95,z3,z5]),(0,[z0,z256,z29,z1,z3,z5]),(0,[z0,z1,z2,z3,z5,z1376])],[(0,[z0,z1377,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1378])],[(0,[z21,z1,z2,z77,z5,z17]),(0,[z0,z409,z1,z44,z3,z5])],[(0,[z0,z1,z1379,z3,z5,z10]),(0,[z0,z1380,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1381]),(0,[z0,z1,z2,z3,z5,z1382]),(0,[z0,z1,z2,z3,z5,z1383]),(0,[z0,z211,z1,z469,z3,z5]),(0,[z0,z15,z44,z2,z3,z5])],[(0,[z0,z1384,z1,z2,z3,z5]),(0,[z0,z319,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1385]),(0,[z0,z57,z1,z2,z1008,z10])],[(0,[z0,z1,z2,z3,z5,z1386]),(0,[z0,z406,z359,z2,z3,z10]),(0,[z0,z234,z2,z3,z1387,z5]),(0,[z0,z12,z56,z2,z3,z5]),(0,[z0,z1,z2,z3,z70,z166])],[(0,[z104,z225,z69,z2,z3,z5]),(0,[z0,z359,z39,z2,z3,z5]),(0,[z0,z1,z2,z3,z1388,z5]),(0,[z0,z1,z1389,z2,z3,z5]),(0,[z0,z277,z2,z3,z5,z13]),(0,[z0,z234,z2,z3,z5,z112]),(0,[z0,z2,z3,z5,z1238,z6]),(0,[z0,z1,z2,z3,z5,z55])],[(0,[z0,z234,z148,z2,z3,z5]),(0,[z0,z1,z2,z3,z795,z10]),(0,[z96,z0,z7,z1,z31,z5])],[(0,[z33,z1005,z2,z3,z5,z10]),(0,[z0,z1,z3,z1390,z5,z10]),(0,[z0,z7,z1,z94,z30,z5]),(0,[z0,z39,z939,z2,z3,z5])],[(0,[z0,z7,z319,z2,z3,z5])],[(0,[z0,z211,z131,z2,z3,z5]),(0,[z109,z0,z1,z2,z371,z5]),(0,[z0,z1,z2,z3,z5,z1391]),(0,[z0,z473,z1,z44,z3,z5]),(0,[z0,z152,z1,z2,z3,z200]),(0,[z0,z1,z2,z3,z5,z1392]),(0,[z0,z57,z1,z2,z400,z79])],[(0,[z0,z234,z1,z2,z3,z5]),(0,[z33,z0,z2,z3,z5,z108]),(0,[z0,z1,z1393,z2,z3,z5]),(0,[z0,z99,z2,z3,z5,z10]),(0,[z0,z7,z15,z2,z3,z5]),(0,[z0,z1,z959,z31,z5,z10])]],
   [[(0,[z0,z1394,z1,z2,z3,z5]),(0,[z0,z1395,z1,z2,z3,z5]),(0,[z0,z211,z2,z540,z3,z5]),(0,[z0,z57,z1,z2,z79,z10])],[(0,[z0,z1396,z1,z2,z3,z5]),(0,[z0,z123,z577,z8,z3,z5]),(0,[z0,z1397,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1398]),(0,[z234,z2,z3,z5,z6,z13]),(0,[z0,z1,z2,z3,z5,z1399]),(0,[z0,z240,z3,z5,z549,z10]),(0,[z0,z256,z176,z1,z3,z10]),(0,[z0,z7,z2,z3,z5,z649])],[(0,[z20,z1,z185,z3,z5,z13]),(0,[z0,z1,z2,z3,z1400,z5]),(0,[z0,z24,z1,z238,z3,z132])],[(0,[z0,z227,z1,z83,z3,z5])],[(0,[z0,z234,z2,z3,z5,z507]),(0,[z0,z2,z3,z1401,z5,z10]),(0,[z0,z46,z29,z2,z3,z5]),(0,[z0,z1,z1402,z2,z3,z5]),(0,[z0,z12,z2,z3,z51,z6])],[(0,[z0,z871,z1,z2,z3,z5]),(0,[z23,z0,z234,z2,z3,z5]),(0,[z0,z1403,z1,z2,z3,z5]),(1,[z1,z2,z3,z5,z769]),(0,[z0,z256,z7,z1,z3,z5]),(0,[z694,z138,z1,z2,z3,z5])],[(0,[z0,z29,z554,z2,z3,z5]),(0,[z0,z265,z56,z2,z3,z5]),(0,[z0,z57,z151,z2,z79,z10])],[(0,[z0,z1,z1404,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1405]),(0,[z69,z1005,z2,z3,z5,z10]),(0,[z0,z58,z2,z3,z5,z13]),(0,[z136,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z140,z5])],[(0,[z0,z359,z209,z2,z3,z5])],[(0,[z0,z1336,z234,z2,z3,z5]),(0,[z0,z1,z2,z3,z1406,z5])],[(0,[z0,z1,z35,z274,z2,z3]),(0,[z1407,z1,z2,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1408]),(0,[z0,z1,z72,z3,z823,z10])],[],[(0,[z0,z1409,z1,z2,z3,z5]),(0,[z387,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1410]),(0,[z0,z12,z2,z3,z51,z413]),(0,[z0,z1,z2,z3,z5,z1411])],[],[]],
   [[(0,[z104,z69,z2,z3,z5,z13])],[(0,[z0,z1,z94,z488,z5,z10]),(0,[z0,z29,z194,z2,z3,z5])],[(0,[z0,z1,z1412,z3,z5,z10]),(0,[z0,z83,z2,z3,z49,z5])],[(0,[z0,z1,z478,z170,z3,z5]),(0,[z0,z1,z2,z3,z1370,z13])],[(0,[z0,z1,z863,z3,z5,z10]),(0,[z0,z1,z488,z3,z5,z17]),(0,[z0,z234,z2,z3,z5,z122]),(0,[z0,z1,z2,z3,z1413,z5]),(0,[z0,z357,z1,z2,z3,z257])],[(0,[z0,z1,z2,z3,z5,z1414]),(0,[z0,z2,z3,z579,z5,z40]),(0,[z0,z1,z3,z80,z823,z10])],[(0,[z96,z0,z1,z31,z5,z6]),(0,[z0,z12,z256,z1,z3,z10]),(0,[z0,z1415,z1,z2,z3,z5]),(0,[z0,z1,z1416,z2,z3,z5])],[(0,[z76,z179,z1,z170,z3,z5]),(0,[z0,z1226,z1,z2,z3,z5]),(0,[z0,z406,z7,z1,z2,z3])],[(0,[z0,z1,z1417,z2,z3,z5]),(0,[z21,z29,z1,z2,z77,z5]),(0,[z0,z234,z2,z30,z3,z5]),(0,[z0,z57,z54,z1,z2,z79])],[(0,[z0,z1,z2,z3,z5,z1418]),(0,[z0,z1,z332,z2,z3,z10]),(0,[z493,z1,z2,z3,z5,z6]),(0,[z0,z29,z1,z2,z972,z5]),(0,[z0,z1,z1419,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1420]),(0,[z0,z319,z2,z3,z5,z13]),(0,[z0,z240,z95,z3,z5,z42]),(0,[z0,z1,z2,z3,z5,z1421]),(0,[z0,z1422,z2,z3,z5,z10]),(0,[z0,z39,z1423,z2,z3,z5])],[(0,[z0,z1,z1424,z3,z5,z10]),(0,[z0,z1,z2,z3,z1425,z5]),(0,[z0,z1,z2,z3,z5,z1426])],[(0,[z0,z1,z2,z3,z5,z86]),(0,[z0,z409,z1,z170,z3,z5]),(0,[z0,z193,z1,z545,z3,z5]),(0,[z0,z1427,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1428]),(0,[z0,z1,z2,z3,z1429,z5]),(0,[z0,z24,z99,z1,z3,z10])],[],[(0,[z0,z1,z2,z3,z5,z1430]),(0,[z0,z1,z2,z3,z5,z262]),(0,[z0,z1,z294,z3,z5,z191])]],
   [[],[(0,[z0,z7,z1,z294,z3,z5]),(0,[z0,z95,z3,z578,z5,z10]),(0,[z0,z1,z2,z3,z5,z1431]),(0,[z0,z1,z2,z3,z5,z1432])],[(0,[z0,z1433,z2,z3,z5,z10])],[(0,[z0,z209,z89,z2,z3,z5]),(0,[z0,z1,z1434,z2,z3,z5]),(0,[z0,z319,z2,z3,z119,z10]),(0,[z21,z0,z234,z2,z3,z5]),(0,[z0,z12,z2,z309,z3,z10]),(0,[z0,z193,z9,z2,z3,z5])],[(0,[z0,z1,z2,z5,z740,z61])],[(0,[z0,z1,z2,z3,z5,z1435]),(0,[z0,z735,z1,z2,z3,z5]),(0,[z0,z1436,z1,z2,z3,z5]),(0,[z0,z1437,z1,z2,z3,z5])],[(0,[z0,z1438,z1,z3,z5,z10]),(0,[z0,z1439,z234,z2,z3,z5]),(0,[z1,z2,z3,z5,z26,z6]),(0,[z0,z134,z2,z615,z5,z10]),(0,[z0,z1,z2,z3,z5,z1440]),(0,[z0,z1441,z1,z2,z3,z5]),(0,[z0,z1,z44,z376,z3,z5])],[(0,[z1,z863,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1442]),(0,[z0,z1,z2,z3,z5,z1443]),(0,[z0,z1444,z1,z2,z3,z5]),(0,[z0,z24,z3,z135,z132,z10])],[(0,[z0,z134,z2,z37,z5,z13]),(0,[z0,z234,z94,z2,z3,z5]),(0,[z521,z1,z2,z3,z5,z13]),(0,[z0,z1,z94,z30,z5,z6]),(0,[z0,z152,z1,z2,z3,z857])],[(0,[z96,z0,z1,z488,z5,z10]),(0,[z0,z7,z1,z2,z3,z119]),(0,[z0,z1,z1445,z2,z3,z5]),(0,[z0,z2,z3,z5,z135,z6]),(0,[z0,z211,z134,z2,z3,z5]),(0,[z0,z58,z2,z3,z5,z10]),(0,[z0,z1,z1446,z2,z3,z5]),(0,[z0,z151,z44,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1447,z5])],[(0,[z0,z1,z2,z3,z1448,z10]),(0,[z0,z1,z1449,z3,z5,z10]),(0,[z0,z234,z478,z2,z3,z5]),(0,[z0,z123,z35,z8,z3,z5]),(0,[z0,z1,z2,z245,z197,z5]),(0,[z0,z1,z1450,z2,z3,z5])],[(0,[z0,z1451,z1,z2,z3,z5]),(0,[z343,z69,z2,z3,z5,z10]),(0,[z96,z0,z29,z1,z31,z5])],[(0,[z33,z148,z2,z3,z5,z86]),(0,[z0,z2,z3,z1452,z5,z10]),(0,[z1,z2,z3,z5,z13,z523]),(0,[z250,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1453]),(0,[z0,z1,z2,z245,z115,z5])],[(0,[z0,z1,z2,z3,z5,z1454]),(0,[z0,z1,z2,z3,z1455,z5]),(0,[z0,z1,z1456,z3,z5,z10]),(1,[z0,z24,z99,z3,z10])],[(0,[z0,z1457,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1458,z5]),(0,[z0,z1,z2,z3,z5,z1459])]],
   [[(0,[z0,z1460,z1,z2,z3,z5]),(0,[z0,z813,z1,z2,z3,z5]),(0,[z0,z234,z145,z2,z3,z5]),(0,[z0,z2,z3,z51,z581,z10]),(0,[z0,z1185,z2,z3,z5,z10]),(0,[z0,z131,z386,z2,z3,z5])],[(0,[z0,z1,z44,z2,z3,z5]),(0,[z104,z69,z2,z3,z5,z10]),(0,[z106,z145,z1,z2,z3,z5]),(0,[z76,z0,z234,z2,z3,z5]),(0,[z0,z1461,z2,z3,z5,z10]),(0,[z1,z2,z3,z5,z295,z13]),(0,[z0,z234,z39,z2,z3,z5]),(0,[z0,z151,z2,z3,z5,z6])],[(0,[z0,z1462,z234,z2,z3,z5]),(0,[z0,z176,z602,z2,z3,z10]),(0,[z0,z44,z2,z3,z579,z5]),(0,[z0,z1,z2,z3,z5,z1463]),(0,[z0,z1,z2,z3,z1464,z5])],[(0,[z66,z0,z1,z2,z5,z91]),(0,[z0,z1441,z277,z2,z3,z5])],[(0,[z76,z7,z1,z170,z3,z5]),(0,[z23,z7,z1,z2,z3,z93]),(0,[z0,z234,z234,z2,z3,z5]),(0,[z0,z1,z44,z3,z5,z485])],[(0,[z1,z196,z375,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1465])],[(0,[z0,z1466,z1,z2,z3,z5]),(0,[z0,z176,z2,z3,z73,z13]),(0,[z0,z1467,z1,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1468]),(0,[z27,z1,z2,z3,z5,z13]),(0,[z0,z1,z2,z3,z70,z202]),(0,[z0,z1,z2,z3,z5,z1469])],[(0,[z0,z89,z332,z2,z3,z10]),(0,[z0,z29,z352,z1,z2,z3]),(0,[z0,z1470,z1,z2,z3,z5]),(0,[z0,z1,z1471,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z406,z89,z2,z3,z10]),(0,[z0,z406,z1,z209,z2,z3]),(0,[z0,z1,z1472,z3,z5,z10]),(0,[z0,z39,z352,z1,z2,z3]),(0,[z0,z2,z3,z579,z128,z10]),(0,[z0,z554,z2,z3,z5,z67])],[(0,[z0,z1473,z1,z2,z3,z10]),(0,[z0,z7,z2,z3,z5,z122]),(0,[z143,z1,z2,z3,z5,z769]),(0,[z0,z1,z2,z3,z5,z1474]),(0,[z0,z134,z2,z3,z5,z55])],[(0,[z0,z1,z332,z2,z3,z13]),(0,[z0,z1,z2,z3,z1475,z10]),(0,[z0,z1,z2,z3,z1476,z5]),(0,[z0,z911,z2,z3,z5,z10]),(0,[z0,z1477,z1,z2,z3,z5])],[(0,[z0,z1478,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1479]),(0,[z0,z1,z2,z3,z5,z1480]),(0,[z0,z1481,z1,z2,z3,z5])],[(0,[z442,z0,z359,z2,z5,z10]),(0,[z0,z1,z2,z3,z5,z410]),(0,[z0,z1,z2,z3,z5,z1482]),(0,[z0,z1,z2,z263,z5,z67])],[(0,[z33,z0,z56,z2,z3,z5]),(0,[z442,z0,z179,z1,z2,z5]),(0,[z0,z44,z2,z3,z5,z122]),(0,[z0,z256,z1,z3,z140,z5]),(0,[z229,z145,z1,z2,z3,z5]),(0,[z0,z1483,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z1484])],[(0,[z0,z1,z2,z3,z5,z1485]),(0,[z0,z724,z1,z2,z3,z5]),(0,[z27,z2,z3,z5,z122,z13]),(0,[z0,z1,z478,z3,z5,z118]),(0,[z0,z29,z2,z3,z5,z59]),(0,[z1486,z1,z2,z3,z5,z10])],[(0,[z0,z1,z1487,z3,z5,z10]),(0,[z33,z148,z44,z2,z3,z5]),(0,[z0,z179,z1,z332,z2,z3]),(0,[z1,z375,z185,z2,z3,z5])],[(0,[z0,z2,z3,z5,z122,z6])],[(0,[z0,z1433,z2,z3,z5,z13]),(0,[z0,z7,z2,z3,z5,z729]),(0,[z0,z1,z1488,z2,z3,z5]),(0,[z0,z1489,z1,z2,z3,z5])],[(0,[z0,z1490,z1,z2,z3,z5]),(0,[z0,z1,z1491,z2,z3,z5])],[(0,[z76,z89,z170,z3,z5,z10]),(0,[z0,z36,z2,z49,z5,z13]),(1,[z0,z1,z2,z5,z740])],[(0,[z0,z1,z2,z3,z5,z1492]),(0,[z0,z39,z1,z3,z5,z279]),(0,[z0,z1493,z2,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1494]),(0,[z0,z1495,z1,z2,z3,z5]),(0,[z0,z406,z29,z1,z2,z3]),(0,[z0,z1,z2,z3,z5,z1496]),(0,[z0,z1193,z1,z488,z3,z5]),(0,[z0,z1,z3,z5,z1497,z13]),(0,[z0,z134,z2,z3,z140,z5])],[(0,[z76,z1,z170,z3,z5,z13]),(0,[z0,z1,z2,z3,z1498,z10]),(0,[z0,z134,z2,z37,z5,z10])],[(0,[z33,z148,z2,z3,z5,z6]),(0,[z0,z1,z1499,z2,z3,z5]),(0,[z0,z176,z517,z2,z3,z10]),(0,[z0,z927,z2,z3,z5,z10])],[(0,[z0,z1,z44,z94,z30,z5]),(0,[z0,z1500,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1501,z5])],[(0,[z0,z22,z2,z3,z5,z10]),(0,[z0,z409,z1,z196,z3,z5]),(0,[z0,z1,z1502,z2,z3,z5]),(0,[z0,z1,z2,z3,z1503,z5]),(0,[z0,z1,z2,z3,z1504,z5]),(0,[z0,z1,z2,z3,z40,z128]),(0,[z0,z284,z1,z2,z3,z626])],[(0,[z0,z1,z2,z3,z5,z303]),(0,[z0,z1,z2,z3,z5,z1505]),(0,[z1,z2,z3,z5,z708,z10]),(0,[z90,z687,z1,z2,z3,z10]),(0,[z0,z1423,z2,z3,z5,z10])],[(0,[z104,z69,z2,z3,z5,z208]),(0,[z0,z1506,z234,z2,z3,z5]),(0,[z0,z240,z95,z3,z5,z108])],[(0,[z33,z0,z337,z2,z3,z5]),(0,[z0,z1,z2,z3,z1507,z5]),(0,[z0,z1508,z1,z2,z3,z5]),(0,[z0,z211,z123,z8,z3,z5]),(0,[z0,z489,z2,z3,z73,z10])]],
   [[(0,[z0,z1,z2,z3,z5,z1509]),(0,[z0,z1,z2,z3,z765,z5]),(0,[z0,z24,z1,z3,z132,z10])],[(0,[z0,z1510,z1,z2,z3,z5])],[(0,[z76,z1,z190,z170,z5,z10]),(0,[z0,z39,z89,z2,z3,z5]),(0,[z0,z2,z3,z754,z5,z10]),(0,[z0,z1,z2,z3,z925,z5]),(0,[z0,z1,z1511,z3,z5,z10])],[(0,[z0,z1,z2,z3,z5,z1512]),(0,[z0,z1,z2,z3,z5,z254]),(0,[z0,z29,z2,z3,z5,z567]),(0,[z0,z1513,z1,z2,z3,z5])],[(0,[z76,z1,z170,z3,z5,z126]),(0,[z0,z179,z1,z2,z190,z5]),(0,[z0,z39,z1,z3,z5,z153]),(0,[z0,z1,z2,z3,z5,z1514]),(0,[z0,z226,z1,z3,z462,z5]),(1,[z0,z927,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1515]),(0,[z0,z1,z2,z3,z5,z1516]),(0,[z0,z29,z183,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1517]),(0,[z0,z1,z1518,z2,z3,z5])],[(0,[z0,z106,z1,z2,z3,z5]),(0,[z76,z1,z170,z3,z5,z129]),(0,[z0,z234,z2,z3,z70,z5]),(0,[z0,z29,z134,z2,z37,z5])],[(0,[z145,z1,z2,z3,z5,z6]),(0,[z0,z39,z134,z2,z37,z5]),(0,[z0,z176,z2,z3,z73,z10])],[(0,[z0,z89,z2,z3,z5,z6]),(0,[z0,z234,z2,z3,z5,z73]),(0,[z0,z1,z2,z3,z5,z1519]),(0,[z0,z57,z58,z2,z79,z10])],[(0,[z0,z99,z44,z2,z3,z5])],[(0,[z0,z95,z3,z5,z564,z10]),(0,[z0,z1,z94,z30,z189,z10]),(0,[z0,z1,z44,z3,z5,z734])],[(0,[z33,z0,z211,z2,z3,z5]),(0,[z0,z2,z3,z5,z10,z1194]),(0,[z143,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z2,z3,z5,z1520])],[(0,[z0,z406,z1,z2,z3,z13]),(0,[z0,z29,z2,z3,z365,z5]),(0,[z0,z732,z2,z3,z5,z13]),(0,[z0,z24,z1,z3,z508,z132])],[(0,[z0,z1,z1521,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1522])],[(0,[z0,z1,z2,z3,z1298,z10]),(0,[z0,z1523,z1,z2,z3,z5]),(0,[z0,z29,z2,z3,z5,z135]),(0,[z0,z1,z2,z3,z681,z166])],[(0,[z0,z7,z1,z332,z2,z3]),(0,[z0,z234,z2,z1524,z3,z5]),(0,[z0,z88,z2,z49,z5,z10]),(0,[z0,z145,z134,z2,z3,z5]),(0,[z0,z39,z2,z3,z5,z135]),(0,[z0,z1525,z2,z3,z5,z10]),(0,[z0,z39,z1,z3,z5,z346])]],
   [[(0,[z0,z218,z148,z2,z3,z5]),(0,[z0,z1,z2,z3,z1526,z10]),(0,[z0,z29,z2,z3,z5,z590]),(0,[z0,z390,z554,z2,z3,z5])],[(0,[z0,z234,z2,z3,z5,z67]),(0,[z0,z99,z2,z3,z5,z6]),(0,[z0,z1,z1527,z2,z3,z5]),(0,[z0,z1528,z1,z2,z3,z5])],[(0,[z0,z1529,z2,z3,z5,z10]),(0,[z0,z1,z2,z5,z743,z10]),(0,[z23,z1,z2,z3,z708,z10]),(0,[z0,z256,z176,z3,z5,z10]),(0,[z0,z1273,z1,z2,z3,z5]),(0,[z0,z1,z94,z30,z5,z477])],[(0,[z225,z138,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1530]),(0,[z0,z234,z2,z3,z5,z78]),(0,[z0,z1,z2,z3,z5,z1531]),(0,[z0,z29,z134,z2,z197,z5]),(0,[z0,z1,z2,z3,z5,z1532])],[(0,[z0,z218,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z119,z6]),(0,[z0,z134,z2,z37,z5,z38]),(0,[z0,z29,z2,z3,z47,z5]),(0,[z0,z39,z1,z3,z5,z340])],[(0,[z0,z1,z1533,z3,z5,z10]),(0,[z0,z1534,z1,z2,z3,z5])],[(0,[z0,z1,z1535,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1536]),(0,[z0,z1537,z1,z2,z3,z5]),(0,[z0,z1,z1247,z2,z3,z5]),(0,[z0,z123,z807,z3,z5,z10]),(0,[z0,z1,z2,z3,z5,z1538]),(0,[z0,z1539,z2,z3,z5,z10]),(0,[z0,z1540,z2,z3,z5,z10])],[(0,[z442,z0,z1,z94,z5,z10]),(0,[z0,z1,z1541,z2,z3,z5]),(0,[z328,z1,z2,z3,z5,z13]),(0,[z426,z1,z2,z3,z5,z6]),(0,[z0,z36,z2,z49,z5,z10])],[(0,[z0,z2,z3,z1542,z5,z10]),(0,[z0,z1,z2,z3,z5,z1543]),(0,[z0,z1,z2,z3,z5,z1544])],[(0,[z0,z1,z3,z5,z1497,z10]),(0,[z0,z1545,z1,z2,z3,z5]),(0,[z96,z0,z39,z1,z31,z5])],[(0,[z0,z1,z2,z3,z5,z1546]),(0,[z76,z1,z170,z3,z5,z10]),(0,[z0,z1,z2,z3,z1547,z5])],[(0,[z76,z1,z332,z170,z3,z10]),(0,[z0,z1548,z1,z2,z3,z10]),(0,[z0,z1,z2,z3,z5,z1549]),(0,[z0,z829,z2,z3,z5,z10]),(0,[z0,z234,z2,z3,z80,z5]),(0,[z0,z1,z2,z3,z1498,z13]),(0,[z0,z1,z2,z3,z189,z10])],[(0,[z0,z467,z1,z2,z3,z5]),(0,[z62,z1,z2,z117,z5,z534]),(0,[z0,z1550,z1,z2,z3,z5]),(0,[z0,z234,z2,z3,z5,z61]),(0,[z0,z193,z123,z8,z3,z5])],[(0,[z0,z1,z3,z5,z1551,z10]),(0,[z1,z2,z3,z48,z5,z6]),(0,[z0,z39,z824,z2,z3,z5])],[(0,[z0,z1552,z1,z2,z3,z5]),(0,[z0,z22,z2,z3,z5,z13]),(0,[z0,z106,z2,z3,z5,z541]),(0,[z0,z1,z1553,z2,z3,z5]),(0,[z0,z1292,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1554]),(0,[z0,z1,z2,z3,z857,z166])],[(0,[z0,z1,z2,z3,z5,z1555]),(0,[z0,z1556,z1,z2,z3,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 482).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 976).take 491) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1467).take 83) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1550)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [482, 494, 491, 83] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 211).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 323).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 440).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 97, 112, 117, 72] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_47018

theorem PEqualNP.Outside.L_meta_47018 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241312 * 2 ^ 32 + 3936938144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3936938144) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47018.solve