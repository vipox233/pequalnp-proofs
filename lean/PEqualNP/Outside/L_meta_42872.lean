import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42872

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
  Nat.testBit (4276676840 * 2 ^ 32 + 4003520672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x001858b0b186b0a8#64 ++ 0x00030b161630d615#64 ++ 0xa038f9f1f38ff1fd#64 ++ 0xf4071f3e3e71fe3f#64 : BitVec 256),
   (0x20c32a5655b19660#64 ++ 0x2418654acab632cc#64 ++ 0xa1c73e7e7df19e66#64 ++ 0xf438e7cfcfbe33cc#64 : BitVec 256),
   (0x0e05850b0e014b50#64 ++ 0x41c0b0a161c0296a#64 ++ 0xfe07c78f8e01ffff#64 ++ 0x7fc0f8f1f1c03fff#64 : BitVec 256),
   (0x576807f00ada1d80#64 ++ 0x8aed00fe015b43b0#64 ++ 0x5ff807f00ffe1f87#64 ++ 0xebff00fe01ffc3f0#64 : BitVec 256),
   (0x9bb7f8000f6de001#64 ++ 0x1376ff0001edbc00#64 ++ 0xdffff8000fffe007#64 ++ 0xbbffff0001fffc00#64 : BitVec 256),
   (0xfdfef7ede0000002#64 ++ 0x1fbfdefdbc000000#64 ++ 0xfffffffff0000007#64 ++ 0xdffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa038f9f1f38ff1fd 0xf4071f3e3e71fe3f

def z1 : W := mkw 0x0805800b04014250 0x4100b0016080284a 0xa007c00f8001e078 0x1400f801f0003c0f

def z2 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73e7e7df19e66 0xf438e7cfcfbe33cc

def z3 : W := mkw 0x516802f000da1480 0x8a2d005e001b4290 0x01f8007001fe0000 0x803f000e003fc000

def z4 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff8000fffe007 0xbbffff0001fffc00

def z5 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff0000007 0xdffffffffe000000

def z6 : W := mkw 0x0c04850900000000 0x018090a120000000 0xfe07c78f80000007 0x5fc0f8f1f0000000

def z7 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07c78f8e01ffff 0x7fc0f8f1f1c03fff

def z8 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z9 : W := mkw 0xf1fa72e4e0000002 0x1e3f4e5c9c000000 0x01f8387070000000 0x803f070e0e000000

def z10 : W := mkw 0x0401050b04010b50 0x408020a16080216a 0xa007078f8c019ffe 0x7400e0f1f18033ff

def z11 : W := mkw 0xfdf6f74de0000002 0x1fbedee9bc000000 0xffc7fe0ff0000002 0x1ff8ffc1fe000000

def z12 : W := mkw 0x5f6d87fb0edb5fd0 0xcbedb0ff61db6bfa 0xffffc7ff8fffffff 0xfffff8fff1ffffff

def z13 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x000007f000001f80 0x400000fe000003f0

def z14 : W := mkw 0x020108121ffb9fe0 0xa040210243ff73fc 0x000000000fff9fe0 0x2000000001fff3fc

def z15 : W := mkw 0x64ca27ede0000002 0x0c9944fdbc000000 0xa1c73ffff0000006 0xd438e7fffe000000

def z16 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa038f9f1f18e0005 0xd4071f3e3e31c000

def z17 : W := mkw 0x0083280005218000 0x0010650000a43000 0x8007380000018000 0x1000e70000003000

def z18 : W := mkw 0x91b27800016ca001 0x12364f00002d9400 0x01f8380001fe0000 0x803f0700003fc000

def z19 : W := mkw 0x9b34d0000a4c6001 0x13669a0001498c00 0x5e38c000020e6001 0x0bc718000041cc00

def z20 : W := mkw 0x020100020e014b50 0x4040200041c0296a 0x000000000e01fff8 0x2000000001c03fff

def z21 : W := mkw 0xdd7cd7e9a0000002 0x1baf9afd34000000 0x5ff8c7f180000007 0xcbff18fe30000000

def z22 : W := mkw 0x001858b0b1809020 0x00030b1616301204 0xa038f9f1f1819065 0xf4071f3e3e30320c

def z23 : W := mkw 0x132000000a480000 0x0264000001490000 0x5ff800000ffe0007 0xabff000001ffc000

def z24 : W := mkw 0x2083280655218260 0x24106500caa4304c 0xa007380e70018060 0x1400e701ce00300c

def z25 : W := mkw 0x9b34d0000a4c6001 0x13669a0001498c00 0x5ff8c0000ffe6007 0xabff180001ffcc00

def z26 : W := mkw 0x91ba78b0b1eeb0a9 0x12374f16163dd615 0x01f8387071fe0000 0x803f070e0e3fc000

def z27 : W := mkw 0x444807fb00921fd0 0xc88900ff601243fa 0x200007ff80001ff8 0x440000fff00003ff

def z28 : W := mkw 0x9f34d5090a4c6911 0x53e69aa121498d22 0x5e38c181820e6199 0x0bc718303041cc33

def z29 : W := mkw 0x001858a0b106a0a8 0x00030b141620d415 0xa038f981f20fe1f9 0x14071f303e41fc3f

def z30 : W := mkw 0x9bb7f8121ffdf661 0x3376ff0243ffbecc 0xdffff8000ffffe67 0xbbffff0001ffffcc

def z31 : W := mkw 0xdf7cd7f9aada1d82 0x9bef9aff355b43b0 0x5ff8c7f18ffe1f87 0xebff18fe31ffc3f0

def z32 : W := mkw 0x001858a0a106a088 0x00030b141420d411 0x8038f981838fe19d 0xb0071f303071fc33

def z33 : W := mkw 0x00c32a5005b19400 0x0018654a00b63280 0x81c73e700df19e06 0xf038e7ce01be33c0

def z34 : W := mkw 0x2ec7af5f5fb1df70 0x65d8f5ebebf63bee 0xffc73e7e7df19e66 0xfff8e7cfcfbe33cc

def z35 : W := mkw 0x0c04850900000000 0x018090a120000000 0x5e07060e00000002 0x0bc0e0c1c0000000

def z36 : W := mkw 0x77eb2ff65ffb9fe0 0xaefd65fecbff73fc 0xffff3ffe7fff9fe7 0xffffe7ffcffff3fc

def z37 : W := mkw 0x9bb6f0000a4c6001 0x1376de0001498c00 0xdffff800020e6007 0x9bffff000041cc00

def z38 : W := mkw 0x99b6f00000000000 0x1336de0000000000 0xdffff80000000007 0x9bffff0000000000

def z39 : W := mkw 0x00105810b186b0a8 0x00020b021630d615 0xa000f801f38ff1f8 0x34001f003e71fe3f

def z40 : W := mkw 0x20c22a5451b09420 0x2418454a8a361284 0xa1c73e7e71f00006 0xd438e7cfce3e0000

def z41 : W := mkw 0x2e87ad0f5f21cb70 0x65d0f5a1ebe4396e 0xfe07ff8ffe01ffff 0x7fc0fff1ffc03fff

def z42 : W := mkw 0xbbb7f8065f6de261 0x3776ff00cbedbc4c 0xfffff80e7fffe067 0xbfffff01cffffc0c

def z43 : W := mkw 0x132000000a480000 0x0264000001490000 0x5fc000000c700002 0x0bf80000018e0000

def z44 : W := mkw 0x133058000b4ca000 0x02660b0001699400 0xdff8f8000fffe007 0xbbff1f0001fffc00

def z45 : W := mkw 0xf5fa77e4e0000002 0x1ebf4efc9c000000 0x5ff83ff070000007 0xcbff07fe0e000000

def z46 : W := mkw 0x2083281655b19660 0x24106502cab632cc 0xa007380e7df19e60 0x3400e701cfbe33cc

def z47 : W := mkw 0x644807ede0000002 0x0c8900fdbc000000 0x200007fff0000000 0x440000fffe000000

def z48 : W := mkw 0xf1fa7af4f186b0aa 0x1e3f4f5e9e30d615 0xa1f8f9f1f38ff1fd 0xf43f1f3e3e71fe3f

def z49 : W := mkw 0x0001081215b19660 0x2000210242b632cc 0x000000000df19e60 0x2000000001be33cc

def z50 : W := mkw 0xdd3cd5a9a0000002 0x1ba79ab534000000 0x5e38c18180000001 0x0bc7183030000000

def z51 : W := mkw 0x0c05850b04014b50 0x4180b0a16080296a 0xa007c78f8001fff8 0x5400f8f1f0003fff

def z52 : W := mkw 0x577857f0aade3d88 0x8aef0afe155bc7b1 0x5ff8c7f18ffe7f9f 0xebff18fe31ffcff3

def z53 : W := mkw 0x000800b0b08210a8 0x0001001616104215 0x200001f1f00011f8 0x4400003e3e00023f

def z54 : W := mkw 0x9ba7a0000e694001 0x1374f40001cd2800 0x5fc700000c700002 0x0bf8e000018e0000

def z55 : W := mkw 0x57680ff01bdebda8 0x8aed01fe037bd7b5 0x5ff807f00fffffff 0xebff00fe01ffffff

def z56 : W := mkw 0x020000000a000000 0x0040000001400000 0x5e0000000e000007 0x2bc0000001c00000

def z57 : W := mkw 0x8897f80b0525e251 0x5112ff0160a4bc4a 0xa007f80f8001e078 0x1400ff01f0003c0f

def z58 : W := mkw 0x9fb7fd0b0f6deb51 0x53f6ffa161edbd6a 0xffffff8f8fffffff 0xfffffff1f1ffffff

def z59 : W := mkw 0x20c2224440000000 0x0418444888000000 0xa1c73e7e70000006 0xd438e7cfce000000

def z60 : W := mkw 0x556807f000901400 0x0aad00fe00120280 0x5ff807f00df01e07 0xebff00fe01be03c0

def z61 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa0073e7e70019e60 0x5400e7cfce0033cc

def z62 : W := mkw 0xfffef7fdeada1d82 0x9fffdeffbd5b43b0 0xfffffffffffe1f87 0xffffffffffffc3f0

def z63 : W := mkw 0x0e058d1b1f81db70 0x41c0b1a363f03b6e 0xfe07ffffff81ffff 0xffc0fffffff03fff

def z64 : W := mkw 0x0000081011809020 0x0000010202301204 0xa000387071819064 0xf400070e0e30320c

def z65 : W := mkw 0x00105000a0000000 0x00020a0014000000 0xa000f801f0000000 0x14001f003e000000

def z66 : W := mkw 0x0805800b04014250 0x4100b0016080284a 0xa007c18f8201f1fd 0x7400f831f0403e3f

def z67 : W := mkw 0x9fb7fd090f6de001 0x13f6ffa121edbc00 0xffffff8f8fffe007 0xfffffff1f1fffc00

def z68 : W := mkw 0x0001081215b19660 0x2000210242b632cc 0xa007060e0df19e66 0x7400e0c1c1be33cc

def z69 : W := mkw 0xdf3cd5a9aa4a0982 0x9be79ab535494130 0x5e38c181820e0181 0x0bc718303041c030

def z70 : W := mkw 0x9bbff8b0bfeff0a9 0x1377ff1617fdfe15 0xdffff8707fffe007 0xbbffff0e0ffffc00

def z71 : W := mkw 0x20c3224644310640 0x24186448c88620c8 0x01c7060e0c700e02 0x0038e0c1c18e01c0

def z72 : W := mkw 0xa896f80df104a02a 0x1512df01be209405 0xa007f80ff001e078 0x1400ff01fe003c0f

def z73 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5e3807f0020e1f81 0x4bc700fe0041c3f0

def z74 : W := mkw 0x9bb6f0000a480000 0x1376de0001490000 0xdffff8000ffe0007 0xbbffff0001ffc000

def z75 : W := mkw 0xffffffedef6de003 0x1ffffffdbdedbc00 0xffffffffffffe007 0xfffffffffffffc00

def z76 : W := mkw 0x20db7af6f5b7b6e8 0x241b6f5edeb6f6dd 0xa1ffffffffffffff 0xf43fffffffffffff

def z77 : W := mkw 0xa896f00de0000002 0x1512de01bc000000 0xa007f80ff0000000 0x1400ff01fe000000

def z78 : W := mkw 0xbbb7f80def6de003 0x1776ff01bdedbc00 0xfffff80fffffe007 0xbfffff01fffffc00

def z79 : W := mkw 0x020108000f6de001 0x0040210001edbc00 0x000000000fffe000 0x2000000001fffc00

def z80 : W := mkw 0x576007400a580d00 0x8aec00e8014b01a0 0x5fc006000c700e02 0x0bf800c0018e01c0

def z81 : W := mkw 0x57785ff0bbdebda8 0x8aef0bfe177bd7b5 0xfff8fff1ffffffff 0xffff1ffe3fffffff

def z82 : W := mkw 0x060005000a000900 0x00c000a001400120 0x5e0007800e001f87 0x6bc000f001c003f0

def z83 : W := mkw 0x020000000a4c6001 0x0040000001498c00 0x00000000020e6000 0x000000000041cc00

def z84 : W := mkw 0x77eb27f64efb1fc0 0xaefd64fec9df63f8 0x5fff07fe0ffe1f87 0xebffe0ffc1ffc3f0

def z85 : W := mkw 0x576007400a580d00 0x8aec00e8014b01a0 0x5ff806000ffe0e07 0xabff00c001ffc1c0

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0x00380000038e0005 0xa00700000071c000

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000c1818201f1fd 0x7400183030403e3f

def z88 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff201f1ff 0xfffffffffe403e3f

def z89 : W := mkw 0x000800a0a0020088 0x0001001414004011 0x0000018180000198 0x0000003030000033

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x000006000c001e06 0x600000c0018003c0

def z91 : W := mkw 0x0400050000000900 0x008000a000000120 0x0000078000001f80 0x400000f0000003f0

def z92 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07c60f8c01ee7a 0x1fc0f8c1f1803dcf

def z93 : W := mkw 0x20c3225654b11660 0x2418644aca9622cc 0x21c7067e7c701e62 0x4438e0cfcf8e03cc

def z94 : W := mkw 0xfdfefffdf186b0aa 0x1fbfdfffbe30d615 0xfffffffff38ff1ff 0xfffffffffe71fe3f

def z95 : W := mkw 0x556807e000000000 0x0aad00fc00000000 0x5ff807f000000007 0xcbff00fe00000000

def z96 : W := mkw 0xdffffff00ffffd81 0x9bfffffe01ffffb0 0xdffffff00fffff87 0xfbfffffe01fffff0

def z97 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xfffff9818ffff1ff 0xffffff3031fffe3f

def z98 : W := mkw 0x0e058d1b1fb1df70 0x61c0b1a363f63bee 0xfe07c78f8ff1ffff 0x7fc0f8f1f1fe3fff

def z99 : W := mkw 0x2000000de0000002 0x04000001bc000000 0x2000000ff0000000 0x04000001fe000000

def z100 : W := mkw 0xfdfef7fde0921d82 0x9fbfdeffbc1243b0 0xfffffffff0001f87 0xdffffffffe0003f0

def z101 : W := mkw 0xdd24850900000002 0x1ba490a120000000 0x5e00000000000000 0x0bc0000000000000

def z102 : W := mkw 0x0e1dd5abae014b50 0x41c3bab575c0296a 0xfe3ffffffe01ffff 0xffc7ffffffc03fff

def z103 : W := mkw 0x404802f000921480 0x8809005e00124290 0x0000007000000000 0x0000000e00000000

def z104 : W := mkw 0x4440074000100d00 0x888800e8000201a0 0x0000060000000e00 0x000000c0000001c0

def z105 : W := mkw 0x64cb2ffff5b19662 0x2c9965fffeb632cc 0xa1c73ffffdf19e66 0xf438e7ffffbe33cc

def z106 : W := mkw 0x8897f8000525e001 0x1112ff0000a4bc00 0x8007f8000001e000 0x1000ff0000003c00

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0xa007060e00000006 0x5400e0c1c0000000

def z108 : W := mkw 0x5f6c87f90ada5d90 0xcbed90ff215b4bb2 0x5ff8c7f18ffe7f9f 0xebff18fe31ffcff3

def z109 : W := mkw 0x644807f650921fe0 0xac8900feca1243fc 0x200007fe70001fe0 0x440000ffce0003fc

def z110 : W := mkw 0x20c3225644b11640 0x2418644ac89622c8 0x01c7067e0df01e06 0xe038e0cfc1be03c0

def z111 : W := mkw 0x0e15dd0b0f05eb50 0x41c2bba161e0bd6a 0xfe3fff8f8f8fffff 0xffc7fff1f1f1ffff

def z112 : W := mkw 0xecdef7ede0000002 0x1d9bdefdbc000000 0xa007fffff0000000 0x5400fffffe000000

def z113 : W := mkw 0x440805a000020980 0x888100b400004130 0x0000018000000180 0x0000003000000030

def z114 : W := mkw 0x20c2225440901400 0x0418444a88120280 0xa1c73e7e7df01e06 0xf438e7cfcfbe03c0

def z115 : W := mkw 0x001850b0b08210a8 0x00030a1616104215 0xa038f9f1f00011fd 0xd4071f3e3e00023f

def z116 : W := mkw 0x9bb7f8020f6deb51 0x5376ff0041edbd6a 0xdffff8000fffffff 0xbbffff0001ffffff

def z117 : W := mkw 0xfdffffede525e003 0x1fbffffdbca4bc00 0xfffffffff001e007 0xdffffffffe003c00

def z118 : W := mkw 0x9bbff8b0bfeff0a9 0x1377ff1617fdfe15 0xfffff9f1fffff1ff 0xffffff3e3ffffe3f

def z119 : W := mkw 0x001850a0a0000000 0x00030a1414000000 0xa038f9f1f0000005 0xd4071f3e3e000000

def z120 : W := mkw 0xfffef7edea000902 0x1fffdefdbd400120 0xfffffffffe001f87 0xffffffffffc003f0

def z121 : W := mkw 0xfdfef7fde0da1482 0x9fbfdeffbc1b4290 0xfffffffff1fe0007 0xdffffffffe3fc000

def z122 : W := mkw 0xd7fa7ff00bfebd81 0x9aff4ffe017fd7b0 0x5ff83ff00ffe1f87 0xebff07fe01ffc3f0

def z123 : W := mkw 0x0000001000921d80 0x80000002001243b0 0x0000000000001f80 0x00000000000003f0

def z124 : W := mkw 0xfffff7efee014b52 0x5ffffefdfdc0296a 0xfffffffffe01ffff 0xffffffffffc03fff

def z125 : W := mkw 0x0082280001208000 0x0010450000241000 0x01c0380001f00000 0x80380700003e0000

def z126 : W := mkw 0x99b7f80005218000 0x1336ff0000a43000 0xdffff8000df18007 0xbbffff0001be3000

def z127 : W := mkw 0xfffef7edea480002 0x1fffdefdbd490000 0xfffffffffffe0007 0xffffffffffffc000

def z128 : W := mkw 0x001058000104a000 0x00020b0000209400 0x00383800018e0000 0x800707000031c000

def z129 : W := mkw 0xbbfffaf6fffff6e9 0x377fff5edffffedd 0xffffffffffffffff 0xffffffffffffffff

def z130 : W := mkw 0x9fa7a50b0e694b51 0x53f4f4a161cd296a 0xffc7c78f8e71ffff 0x7ff8f8f1f1ce3fff

def z131 : W := mkw 0x2040025650901660 0x2408004aca1202cc 0x2000067e70001e60 0x440000cfce0003cc

def z132 : W := mkw 0xb9f7fa5655b19660 0x373eff4acab632cc 0xfffffe7e7df19e67 0xffffffcfcfbe33cc

def z133 : W := mkw 0x000800b000821080 0x0001001600104210 0x003801f0038e1185 0xe007003e0071c230

def z134 : W := mkw 0x572805a00a4a0980 0x8ae500b401494130 0x5e380180020e0181 0x0bc700300041c030

def z135 : W := mkw 0x75ea27e440000000 0x0ebd44fc88000000 0xffff3ffe70000007 0xdfffe7ffce000000

def z136 : W := mkw 0x576007500ad81d00 0x8aec00ea015b03a0 0x5fc006700df01e06 0xebf800ce01be03c0

def z137 : W := mkw 0xfde6a74d40000002 0x1fbcd4e9a8000000 0x5fc7060e00000002 0x0bf8e0c1c0000000

def z138 : W := mkw 0x2cc6a74d40000000 0x0598d4e9a8000000 0xffc7fffff0000007 0xdff8fffffe000000

def z139 : W := mkw 0x0e1cddb9bb86f9b8 0x41c39bb73770df37 0xfe38f9f1f38ff1fd 0xffc71f3e3e71fe3f

def z140 : W := mkw 0x172005000a480900 0x02e400a001490120 0x5ff807800ffe1f87 0xebff00f001ffc3f0

def z141 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0xfff8c7f18fffffff 0xffff18fe31ffffff

def z142 : W := mkw 0x99b6f800016ca001 0x1336df00002d9400 0xdffff80001fe0007 0x9bffff00003fc000

def z143 : W := mkw 0x0083280005218000 0x0010650000a43000 0x81c738000df18006 0xb038e70001be3000

def z144 : W := mkw 0x020108121ffdf661 0x2040210243ffbecc 0x000000000ffffe60 0x2000000001ffffcc

def z145 : W := mkw 0x0001081215819260 0x0000210242b0324c 0xa0073e7e7d819e66 0xf400e7cfcfb033cc

def z146 : W := mkw 0x001850a0a0062088 0x00030a141400c411 0xa038c181820ff1fd 0x740718303041fe3f

def z147 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa000f9f1f001f1f8 0x54001f3e3e003e3f

def z148 : W := mkw 0x33e32a565ff99660 0x267c654acbff32cc 0xffff3e7e7fff9e67 0xffffe7cfcffff3cc

def z149 : W := mkw 0x64585ffdf186b0aa 0x0c8b0bffbe30d615 0xa038fffff38ff1fd 0xf4071ffffe71fe3f

def z150 : W := mkw 0xfdfffffff5b7b6ea 0x3fbffffffeb6f6dd 0xffffffffffffffff 0xffffffffffffffff

def z151 : W := mkw 0xf9fef2e4e0000002 0x1f3fde5c9c000000 0xdffff87070000007 0x9bffff0e0e000000

def z152 : W := mkw 0x440805a9a0000002 0x088100b534000000 0x0000018180000000 0x0000003030000000

def z153 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0x5fff38000dfe0002 0x8bffe70001bfc000

def z154 : W := mkw 0xfdfefffdf1809022 0x1fbfdfffbe301204 0xfffffffff1819067 0xfffffffffe30320c

def z155 : W := mkw 0x0a0580000e014000 0x0140b00001c02800 0xde07c0000e01e007 0x3bc0f80001c03c00

def z156 : W := mkw 0x000808b0b18290a8 0x0001011616305215 0xa00039f1f18191fc 0xf400073e3e30323f

def z157 : W := mkw 0x2ec7a74f4e314f50 0x65d8f4e9e9c629ea 0xffc7c78f8e71ffff 0x7ff8f8f1f1ce3fff

def z158 : W := mkw 0x0000001000821080 0x0000000200104210 0x00000000038e1180 0x200000000071c230

def z159 : W := mkw 0x00105800b104a028 0x00020b0016209405 0xa000f801f001e078 0x14001f003e003c0f

def z160 : W := mkw 0x0400050b00000b50 0x408000a16000016a 0x2000078f80001ff8 0x440000f1f00003ff

def z161 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07c18f8201e1f9 0x1fc0f831f0403c3f

def z162 : W := mkw 0x001858a0b104a028 0x00030b1416209405 0xa038f9f1f001e07d 0xd4071f3e3e003c0f

def z163 : W := mkw 0x0c04850b00000b50 0x418090a16000016a 0xfe07c78f80001fff 0x5fc0f8f1f00003ff

def z164 : W := mkw 0x0010500000042000 0x00020a0000008400 0x0038c000020e6001 0x000718000041cc00

def z165 : W := mkw 0x001850a0a0062088 0x00030a141400c411 0x0038c181820e6199 0x000718303041cc33

def z166 : W := mkw 0x9b34d8000b4ce001 0x13669b0001699c00 0xde38f800038fe005 0xbbc71f000071fc00

def z167 : W := mkw 0x22c32a565fb1df70 0x6458654acbf63bee 0xa1c73e7e7ff1fffe 0xf438e7cfcffe3fff

def z168 : W := mkw 0x020108121f87fbf8 0x4040210243f0ff7f 0x000000000f8ffff8 0x2000000001f1ffff

def z169 : W := mkw 0x0000081011809020 0x0000010202301204 0x0000387071800000 0x8000070e0e300000

def z170 : W := mkw 0xfffff7efee014b52 0x5ffffefdfdc0296a 0xfffffffffc000e07 0xdfffffffff8001c0

def z171 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x00383870718e0000 0x8007070e0e31c000

def z172 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x5e07060e0c000e02 0x0bc0e0c1c18001c0

def z173 : W := mkw 0x081dd8bbb587f2f8 0x4103bb1776b0fe5f 0xa03ff9fff38ff1fd 0xf407ff3ffe71fe3f

def z174 : W := mkw 0x0c05850b04010240 0x0180b0a160802048 0xfe07c78f8c019e67 0x7fc0f8f1f18033cc

def z175 : W := mkw 0x000800b0b08210a8 0x0001001616104215 0xa000c1f1f201f1fd 0x7400183e3e403e3f

def z176 : W := mkw 0xf1fa7ae4e16ca003 0x1e3f4f5c9c2d9400 0x01f8387071fe0000 0x803f070e0e3fc000

def z177 : W := mkw 0x0e0485090a004910 0x41c090a121400922 0x5e00000000000000 0x0bc0000000000000

def z178 : W := mkw 0x20c2224440000000 0x0418444888000000 0x01c7060e00000002 0x0038e0c1c0000000

def z179 : W := mkw 0x2e45875f5e915f70 0x65c8b0ebebd22bee 0xfe07c7fffe01ffff 0x7fc0f8ffffc03fff

def z180 : W := mkw 0xdffffffb0fffffd1 0xdbffffff61fffffa 0xffffffff8fffffff 0xfffffffff1ffffff

def z181 : W := mkw 0x0e87ad0b0f21cb50 0x41d0f5a161e4396a 0xffc7ff8f8ff1ffff 0xfff8fff1f1fe3fff

def z182 : W := mkw 0x0e1dddbbbf87fbf8 0x41c3bbb777f0ff7f 0xfe3fffffff8fffff 0xffc7fffffff1ffff

def z183 : W := mkw 0x5f6d87fb0edb5fd0 0xcbedb0ff61db6bfa 0x5fff07fe0ffe1f87 0xebffe0ffc1ffc3f0

def z184 : W := mkw 0x000008000104a000 0x0000010000209400 0x00000000038fe000 0x200000000071fc00

def z185 : W := mkw 0xf1fa7af4f186b0aa 0x1e3f4f5e9e30d615 0x01f83870718e0000 0x803f070e0e31c000

def z186 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xde3ff800020fe001 0x1bc7ff000041fc00

def z187 : W := mkw 0xfdfffffff5b19662 0x3fbffffffeb632cc 0xfffffffffdf19e67 0xffffffffffbe33cc

def z188 : W := mkw 0x020100020e014b50 0x4040200041c0296a 0x000000000c000e00 0x00000000018001c0

def z189 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdfc7f8000c71e002 0x1bf8ff00018e3c00

def z190 : W := mkw 0x1120000000480000 0x0224000000090000 0x01f8000001fe0000 0x803f0000003fc000

def z191 : W := mkw 0xdfbffda00f6fe981 0x9bf7ffb401edfd30 0xdffff9800fffe187 0xbbffff3001fffc30

def z192 : W := mkw 0x55785ff0b186b0a8 0x0aaf0bfe1630d615 0xfff8fff1f38ff1ff 0xffff1ffe3e71fe3f

def z193 : W := mkw 0x9bf7fa500ffdf401 0x137eff4a01ffbe80 0xdffffe700ffffe07 0xfbffffce01ffffc0

def z194 : W := mkw 0xdf3cd5a9aa4c6003 0x1be79ab535498c00 0x5e38c181820e6001 0x0bc718303041cc00

def z195 : W := mkw 0xfde6a74d40000002 0x1fbcd4e9a8000000 0xffc73e7e70000006 0xdff8e7cfce000000

def z196 : W := mkw 0x576007500ada1d80 0x8aec00ea015b43b0 0x5fc006000ffe1f82 0x2bf800c001ffc3f0

def z197 : W := mkw 0x0001000204010240 0x0000200040802048 0xa007060e0c019e66 0x7400e0c1c18033cc

def z198 : W := mkw 0x0e0485090a004910 0x41c090a121400922 0x5e00c18182006199 0x0bc0183030400c33

def z199 : W := mkw 0x0040025000901400 0x0008004a00120280 0x01c006700df01e06 0xe03800ce01be03c0

def z200 : W := mkw 0x001058101184b020 0x00020b0202309604 0xa038f870738ff065 0xf4071f0e0e71fe0c

def z201 : W := mkw 0x9ba7a0000e694001 0x1374f40001cd2800 0x5fff00000ffe0007 0xabffe00001ffc000

def z202 : W := mkw 0x91b37800056da001 0x12366f0000adb400 0x81ff38000dff8006 0xb03fe70001bff000

def z203 : W := mkw 0x20c2225650901660 0x2418444aca1202cc 0xa1c73e7e70001e66 0xd438e7cfce0003cc

def z204 : W := mkw 0x0c1cd5a9a0000000 0x01839ab534000000 0xfe3ffffff0000007 0xdfc7fffffe000000

def z205 : W := mkw 0x576907f20edb1fc0 0x8aed20fe41db63f8 0xffff07fe0fff9fe7 0xffffe0ffc1fff3fc

def z206 : W := mkw 0xfdfff7efe4010242 0x1fbffefdfc802048 0xfffffffffc019e67 0xffffffffff8033cc

def z207 : W := mkw 0xfdfef7fff0901662 0x3fbfdefffe1202cc 0xfffffffff0001e67 0xdffffffffe0003cc

def z208 : W := mkw 0xdd3cddb9b186b0aa 0x1ba79bb73630d615 0xfe38f9f1f38ff1fd 0xffc71f3e3e71fe3f

def z209 : W := mkw 0x0001000004010000 0x0000200000802000 0x800700000c018006 0x3000e00001803000

def z210 : W := mkw 0x13a328000f698000 0x0274650001ed3000 0xdfff38000fff8007 0xbbffe70001fff000

def z211 : W := mkw 0xfffef7edea4a0982 0x9fffdefdbd494130 0xfffffffff20e0187 0xdffffffffe41c030

def z212 : W := mkw 0x009378000525a000 0x00126f0000a4b400 0x81fff8000fffe007 0xb03fff0001fffc00

def z213 : W := mkw 0x576807fb0ada1fd0 0xcaed00ff615b43fa 0x7ff807ff8ffe1fff 0xefff00fff1ffc3ff

def z214 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0x5fff3e7e70000002 0x8bffe7cfce000000

def z215 : W := mkw 0x2440075f50901f70 0x648800ebea1203ee 0x200007fff0001ff8 0x440000fffe0003ff

def z216 : W := mkw 0x0a05800b0e014b50 0x4140b00161c0296a 0xa007c00f8e01fff8 0x3400f801f1c03fff

def z217 : W := mkw 0x000808b01186b0a8 0x000101160230d615 0x003801f0038ff1fd 0xe007003e0071fe3f

def z218 : W := mkw 0x9bb7f0000e6d6001 0x1376fe0001cdac00 0x5fffc0000e7e6003 0x0bfff80001cfcc00

def z219 : W := mkw 0x0001081215b7b6e8 0x2000210242b6f6dd 0x000000000ffffff8 0x2000000001ffffff

def z220 : W := mkw 0x2082280451208020 0x241045008a241004 0x0000380070000000 0x000007000e000000

def z221 : W := mkw 0x136002500ad81400 0x026c004a015b0280 0x5ff806700ffe1e07 0xebff00ce01ffc3c0

def z222 : W := mkw 0x20cb2af655b396e0 0x2419655ecab672dc 0xa1ff3ffe7fff9fe7 0xf43fe7ffcffff3fc

def z223 : W := mkw 0x576807e00a000900 0x0aed00fc01400120 0x5ff807f00e001f87 0xebff00fe01c003f0

def z224 : W := mkw 0x000108000525e001 0x0000210000a4bc00 0x000000000001e000 0x0000000000003c00

def z225 : W := mkw 0x060005000a000900 0x00c000a001400120 0xfe00c7818e01ffff 0x7fc018f031c03fff

def z226 : W := mkw 0x0e15dd0bbf05eb78 0x41c2bba177e0bd6f 0xfe07ff8ffe01ffff 0x7fc0fff1ffc03fff

def z227 : W := mkw 0x020108121fb1df70 0x6040210243f63bee 0x000000000ff1fff8 0x2000000001fe3fff

def z228 : W := mkw 0xffffffefef6deb53 0x5ffffffdfdedbd6a 0xffffffffffffffff 0xffffffffffffffff

def z229 : W := mkw 0x021158000f6de001 0x00422b0001edbc00 0x8038f8000fffe005 0xb0071f0001fffc00

def z230 : W := mkw 0x2ec7af5f5fb1df70 0x65d8f5ebebf63bee 0xffc7fffffff1ffff 0xfff8fffffffe3fff

def z231 : W := mkw 0x536802f00ada1480 0x8a6d005e015b4290 0x5ff800700ffe0007 0xabff000e01ffc000

def z232 : W := mkw 0x004802f000921480 0x0009005e00124290 0x01f807f00ffe1f87 0xe03f00fe01ffc3f0

def z233 : W := mkw 0x20c3224644310640 0x24186448c88620c8 0xa1c73e7e7c700e06 0xd438e7cfcf8e01c0

def z234 : W := mkw 0xffe7a74f4e014b52 0x5ffcf4e9e9c0296a 0x5fc7060e0c000e02 0x0bf8e0c1c18001c0

def z235 : W := mkw 0x000800a000000000 0x0001001400000000 0x003801f000000005 0xc007003e00000000

def z236 : W := mkw 0x0400050b00000b50 0x408000a16000016a 0xa000c78f8201fffd 0x740018f1f0403fff

def z237 : W := mkw 0x576807e00a580d00 0x8aed00fc014b01a0 0x5ff807f00c700e07 0xcbff00fe018e01c0

def z238 : W := mkw 0x20c22a5451b09420 0x2418454a8a361284 0x01c0387071f00000 0x8038070e0e3e0000

def z239 : W := mkw 0x0000001010801020 0x0000000202100204 0x2000007070001060 0x4400000e0e00020c

def z240 : W := mkw 0x0001000204310640 0x20002000408620c8 0x000000000c700e00 0x00000000018e01c0

def z241 : W := mkw 0x9fa7a50b0e694b51 0x53f4f4a161cd296a 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z242 : W := mkw 0x209b78b6f5a7b2e8 0x24136f16deb4f65d 0xa03ff9fff38ff1fd 0xf407ff3ffe71fe3f

def z243 : W := mkw 0x20585af6f196b6e8 0x240b0b5ede32d6dd 0xa038fffff38ffffd 0xf4071ffffe71ffff

def z244 : W := mkw 0x0000001000801000 0x0000000200100200 0x0000007001801004 0xe000000e00300200

def z245 : W := mkw 0x9bbff8a0af6de001 0x1377ff1415edbc00 0xfffff9f1ffffe007 0xffffff3e3ffffc00

def z246 : W := mkw 0x71ea2af451fa94a0 0xae3d455e8a3f5294 0x01f8387071fe0000 0x803f070e0e3fc000

def z247 : W := mkw 0x0a15d8000f05e000 0x0142bb0001e0bc00 0xde3ff8000f8fe007 0xbbc7ff0001f1fc00

def z248 : W := mkw 0x0e0d85bb0e835bd0 0x41c1b0b761d06b7a 0xfe3fc7ff8f8fffff 0xffc7f8fff1f1ffff

def z249 : W := mkw 0x9bb7f8101fedf021 0x1376ff0203fdbe04 0xfffff8707ffff067 0xffffff0e0ffffe0c

def z250 : W := mkw 0x0000000000062088 0x000000000000c411 0x00000000020e6198 0x000000000041cc33

def z251 : W := mkw 0x99b6f8000104a000 0x1336df0000209400 0xdffff800038fe007 0xbbffff000071fc00

def z252 : W := mkw 0x0400050000000000 0x008000a000000000 0x5e00078000000007 0x4bc000f000000000

def z253 : W := mkw 0x0804800000000000 0x0100900000000000 0xde07c00000000007 0x1bc0f80000000000

def z254 : W := mkw 0x0000000200000b50 0x400000004000016a 0x0000000000001ff8 0x00000000000003ff

def z255 : W := mkw 0x0082200000000000 0x0010440000000000 0x81c7380000000006 0x9038e70000000000

def z256 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000201f1f8 0x2000000000403e3f

def z257 : W := mkw 0x020000100ada1d80 0x80400002015b43b0 0x000000000ffe1f80 0x2000000001ffc3f0

def z258 : W := mkw 0x0e1cd5a9aa066998 0x41c39ab53540cd33 0x5e38c181820e6199 0x0bc718303041cc33

def z259 : W := mkw 0x9ba7a8000f6de001 0x1374f50001edbc00 0x5fc700000fffe002 0x2bf8e00001fffc00

def z260 : W := mkw 0x20c22a5451809020 0x0418454a8a301204 0xa1c73e7e71819066 0xf438e7cfce30320c

def z261 : W := mkw 0xfffffffffffb9fe2 0xbfffffffffff73fc 0xffffffffffff9fe7 0xfffffffffffff3fc

def z262 : W := mkw 0x0e0585000e014900 0x01c0b0a001c02920 0xde07c7800e01ff87 0x7bc0f8f001c03ff0

def z263 : W := mkw 0x00400a5011909420 0x0008014a02321284 0xa1c03e707df19e66 0xf43807ce0fbe33cc

def z264 : W := mkw 0x64cb2ff655b39fe0 0xac9965fecab673fc 0xa1c73ffe7df19fe6 0xf438e7ffcfbe33fc

def z265 : W := mkw 0xb9b6f00de0000002 0x1736de01bc000000 0xfffff80ff0000007 0x9fffff01fe000000

def z266 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x003807f0038e1f85 0xe00700fe0071c3f0

def z267 : W := mkw 0x9bb7f0000e014000 0x1376fe0001c02800 0xdffff8000e01e007 0xbbffff0001c03c00

def z268 : W := mkw 0xdd3cd5a9a0000002 0x1ba79ab534000000 0xfe3fc78f80000007 0x5fc7f8f1f0000000

def z269 : W := mkw 0x0e0485090a004910 0x41c090a121400922 0x5e00c7818e007f9f 0x6bc018f031c00ff3

def z270 : W := mkw 0xf1fa72f4e0da1482 0x9e3f4e5e9c1b4290 0x01f8387071fe0000 0x803f070e0e3fc000

def z271 : W := mkw 0x060105020e014b50 0x40c020a041c0296a 0x5e0007800e01ffff 0x6bc000f001c03fff

def z272 : W := mkw 0x57690ff00ffffd81 0x8aed21fe01ffffb0 0x5ff807f00fffff87 0xebff00fe01fffff0

def z273 : W := mkw 0x0a0580020e014b50 0x4140b00041c0296a 0xde07c0000e01ffff 0x3bc0f80001c03fff

def z274 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x8038f870738fe005 0xb0071f0e0e71fc00

def z275 : W := mkw 0xfd7cd7ede0000002 0x1faf9afdbc000000 0x7e38c7fff0000001 0x4fc718fffe000000

def z276 : W := mkw 0x20937806f525a268 0x24126f00dea4b44d 0xa007f80ff001e078 0x1400ff01fe003c0f

def z277 : W := mkw 0x001058000104a000 0x00020b0000209400 0x8038f800038fe005 0xb0071f000071fc00

def z278 : W := mkw 0x0000001210901660 0x20000002421202cc 0x0000000000001e60 0x00000000000003cc

def z279 : W := mkw 0x0a0580000e014000 0x0140b00001c02800 0xfe07c1818e01f1ff 0x7fc0f83031c03e3f

def z280 : W := mkw 0x001850a0a0062088 0x00030a141400c411 0x00380000000e0000 0x000700000001c000

def z281 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x0038f9f1f38e6199 0x80071f3e3e71cc33

def z282 : W := mkw 0x99b7f800056de001 0x1336ff0000adbc00 0x81fff80001ffe000 0x903fff00003ffc00

def z283 : W := mkw 0x5f2c85a90a4a4990 0xcbe590b521494932 0x5e38c181820e6199 0x0bc718303041cc33

def z284 : W := mkw 0x536802f00ada1d80 0x8a6d005e015b43b0 0x01f800700ffe1f80 0xa03f000e01ffc3f0

def z285 : W := mkw 0x576007400a580d00 0x8aec00e8014b01a0 0x5fc007800e701f87 0x6bf800f001ce03f0

def z286 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07060e0c019e66 0x7fc0e0c1c18033cc

def z287 : W := mkw 0x0a87a8000f21c000 0x0150f50001e43800 0xdfc7f8000ff1e007 0xbbf8ff0001fe3c00

def z288 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c000000df00006 0xa038000001be0000

def z289 : W := mkw 0xa8d7fa5ff5b19662 0x351aff4bfeb632cc 0xa1c7fe7ffdf19e66 0xf438ffcfffbe33cc

def z290 : W := mkw 0x132108000f6de001 0x0264210001edbc00 0x5ff800000fffe007 0xabff000001fffc00

def z291 : W := mkw 0x20410a5655b19660 0x2408214acab632cc 0x2000067e7df19e60 0x640000cfcfbe33cc

def z292 : W := mkw 0x9ba7a0000e694001 0x1374f40001cd2800 0xdfc7c0000e71e007 0x3bf8f80001ce3c00

def z293 : W := mkw 0x57eb2ff00ffb9d80 0x8afd65fe01ff73b0 0xdfff3ff00fff9f87 0xfbffe7fe01fff3f0

def z294 : W := mkw 0x9bb7f800bf6de029 0x1376ff0017edbc05 0xfffff801ffffe07f 0xbfffff003ffffc0f

def z295 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff801f003fe0181 0x8bff003e007fc030

def z296 : W := mkw 0xddbef5a9a0000002 0x1bb7deb534000000 0xdffff98180000007 0x9bffff3030000000

def z297 : W := mkw 0x000008101186b0a8 0x000001020230d615 0xa0003870738ff1fc 0xf400070e0e71fe3f

def z298 : W := mkw 0x0e05851b0edb5fd0 0xc1c0b0a361db6bfa 0xfe07c78f8fffffff 0x7fc0f8f1f1ffffff

def z299 : W := mkw 0x576807e00a5a0d80 0x8aed00fc014b41b0 0x5ff807800e7e0f83 0x0bff00f001cfc1f0

def z300 : W := mkw 0x645857ede0000002 0x0c8b0afdbc000000 0xa038fffff0000005 0xd4071ffffe000000

def z301 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0x5ff8f9f1f0000001 0x8bff1f3e3e000000

def z302 : W := mkw 0xbbf7fa545ffdf421 0x377eff4a8bffbe84 0xdffff8707fffe007 0xbbffff0e0ffffc00

def z303 : W := mkw 0x604802e4e0000002 0x0c09005c9c000000 0x0000007070000000 0x0000000e0e000000

def z304 : W := mkw 0x020000000a480000 0x0040000001490000 0x000000000ffe0000 0x2000000001ffc000

def z305 : W := mkw 0x20da72e4e0000000 0x041b4e5c9c000000 0xa1fffffff0000007 0xd43ffffffe000000

def z306 : W := mkw 0x0000081011b09420 0x2000010202361284 0x0000000001f00000 0x00000000003e0000

def z307 : W := mkw 0x000800b0b08210a8 0x0001001616104215 0x0000007070000000 0x0000000e0e000000

def z308 : W := mkw 0x020008101bdebda8 0x80400102037bd7b5 0x000000000ffffff8 0x2000000001ffffff

def z309 : W := mkw 0x0040025000901400 0x0008004a00120280 0x01c0007001f00000 0x8038000e003e0000

def z310 : W := mkw 0x00105000a0042008 0x00020a0014008401 0x0000c00180006018 0x0000180030000c03

def z311 : W := mkw 0x2083200644210240 0x24106400c8842048 0x0007000e00000000 0x0000e001c0000000

def z312 : W := mkw 0x2040024640100640 0x24080048c80200c8 0x0000060e00000e00 0x000000c1c00001c0

def z313 : W := mkw 0x06185db0bb86b9a8 0x00c30bb61770d735 0xfe38fff1ff8fffff 0xffc71ffe3ff1ffff

def z314 : W := mkw 0x5f6d87f00edb5d80 0x8bedb0fe01db6bb0 0xdfffc7f00fffff87 0xfbfff8fe01fffff0

def z315 : W := mkw 0xf1fb7af6f5b19662 0x3e3f6f5edeb632cc 0xa1ff3e7e7df19e66 0xf43fe7cfcfbe33cc

def z316 : W := mkw 0xa897f8065525e261 0x3512ff00caa4bc4c 0xa007f80e7001e060 0x1400ff01ce003c0c

def z317 : W := mkw 0x9b35d8000f6de001 0x1366bb0001edbc00 0x5e38c0000fffe001 0x2bc7180001fffc00

def z318 : W := mkw 0xd1fa7af001feb481 0x9a3f4f5e003fd690 0x01f8387001fe0000 0x803f070e003fc000

def z319 : W := mkw 0x889ff8b0b5a7f0a9 0x1113ff1616b4fe15 0xa03ff9f1f38ff1fd 0xf407ff3e3e71fe3f

def z320 : W := mkw 0xffffffffff87fbfa 0x5ffffffffff0ff7f 0xffffffffff8fffff 0xfffffffffff1ffff

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000387070000004 0xd400070e0e000000

def z322 : W := mkw 0x5f65874b0e594f50 0xcbecb0e961cb29ea 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z323 : W := mkw 0x04185dbbb186bbf8 0x40830bb77630d77f 0xa038fffff38ffffd 0xf4071ffffe71ffff

def z324 : W := mkw 0x060005100ada1d80 0x80c000a2015b43b0 0x5e0007800ffe1f87 0x6bc000f001ffc3f0

def z325 : W := mkw 0xfffffff65fffffe1 0xbffffffecbfffffc 0xfffffffe7fffffe7 0xffffffffcffffffc

def z326 : W := mkw 0xfffef7edea4c6003 0x1fffdefdbd498c00 0xfffffffff20e6007 0xdffffffffe41cc00

def z327 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa0383870718f9064 0xf407070e0e31f20c

def z328 : W := mkw 0x009b78b0b5a7b0a8 0x00136f1616b4f615 0xa1fff9f1fffff1ff 0xf43fff3e3ffffe3f

def z329 : W := mkw 0x0e04850b0a004b50 0x41c090a16140096a 0x7e00c78f82007ff9 0x4fc018f1f0400fff

def z330 : W := mkw 0x556807f000921d80 0x8aad00fe001243b0 0x5ff807f000001f87 0xcbff00fe000003f0

def z331 : W := mkw 0x91ba78b0b1eeb0a9 0x12374f16163dd615 0xa1f8f9f1f3fff1fd 0xf43f1f3e3e7ffe3f

def z332 : W := mkw 0xbbf7fa565ffdf661 0x377eff4acbffbecc 0xfffffe7e7ffffe67 0xffffffcfcfffffcc

def z333 : W := mkw 0x00105800b104a028 0x00020b0016209405 0xa038f801f38fe07d 0xb4071f003e71fc0f

def z334 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x7e07078f8c001ffa 0x4fc0e0f1f18003ff

def z335 : W := mkw 0x000008101186b0a8 0x000001020230d615 0x00000000038ff1f8 0x200000000071fe3f

def z336 : W := mkw 0x93b278000b6ca001 0x12764f00016d9400 0x5ff838000ffe0007 0xabff070001ffc000

def z337 : W := mkw 0xfdfeffede16ca003 0x1fbfdffdbc2d9400 0xfffffffff1fe0007 0xdffffffffe3fc000

def z338 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x01c038707df19e60 0xa038070e0fbe33cc

def z339 : W := mkw 0x5f6d87eb0e014b50 0x4bedb0fd61c0296a 0xffffc7ff8e01ffff 0xfffff8fff1c03fff

def z340 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c7fffffff1ffff 0xf438fffffffe3fff

def z341 : W := mkw 0x20c32a4655318660 0x24186548caa630cc 0xa1c73e0e7c718e62 0x1438e7c1cf8e31cc

def z342 : W := mkw 0x644807fdf08210aa 0x0c8900ffbe104215 0x200007fff00011f8 0x440000fffe00023f

def z343 : W := mkw 0x51785af0b1deb4a8 0x8a2f0b5e163bd695 0xa1f8f9f1f3fff1fd 0xf43f1f3e3e7ffe3f

def z344 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x203839f1f18e11f8 0xc407073e3e31c23f

def z345 : W := mkw 0x8814d00000046001 0x11029a0000008c00 0x0000c00000006000 0x0000180000000c00

def z346 : W := mkw 0x91b2700000000000 0x12364e0000000000 0x01f8380000000000 0x803f070000000000

def z347 : W := mkw 0x001850b0a0821080 0x00030a1614104210 0xa038f9f1f38e1185 0xf4071f3e3e71c230

def z348 : W := mkw 0x9fbffdbbbfeffbf9 0x53f7ffb777fdff7f 0xffffffffffffffff 0xffffffffffffffff

def z349 : W := mkw 0x51785af0b1deb4a8 0x8a2f0b5e163bd695 0x01f8387071fe0000 0x803f070e0e3fc000

def z350 : W := mkw 0x464807f00ada1d80 0x88c900fe015b43b0 0x000007f00ffe1f80 0x600000fe01ffc3f0

def z351 : W := mkw 0x1f25850b0e494b50 0x43e4b0a161c9296a 0xffffc78f8fffffff 0xfffff8f1f1ffffff

def z352 : W := mkw 0x021958b0bfeff0a9 0x00432b1617fdfe15 0xa038f9f1fffff1fd 0xf4071f3e3ffffe3f

def z353 : W := mkw 0xa89ef0ade0000002 0x1513de15bc000000 0xa03ff9fff0000005 0xd407ff3ffe000000

def z354 : W := mkw 0xfffef7edea004912 0x5fffdefdbd400922 0xfffffffff200619f 0xdffffffffe400c33

def z355 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xde07c60e0e01ee07 0x3bc0f8c1c1c03dc0

def z356 : W := mkw 0x20c32a4645318640 0x24186548c8a630c8 0x81c73e0e0df18e06 0xb038e7c1c1be31c0

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z358 : W := mkw 0x8887a00004214001 0x1110f40000842800 0x0007000000000000 0x0000e00000000000

def z359 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x00383870738ff1f8 0xa007070e0e71fe3f

def z360 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff806700dfe0e02 0x8bff00ce01bfc1c0

def z361 : W := mkw 0x2083280655218260 0x24106500caa4304c 0xa0073e0e7c019e66 0x7400e7c1cf8033cc

def z362 : W := mkw 0x0e0d85bbbe835bf8 0x41c1b0b777d06b7f 0xfe07c7fffe01ffff 0x7fc0f8ffffc03fff

def z363 : W := mkw 0x2ec7a74f4e314f50 0x65d8f4e9e9c629ea 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z364 : W := mkw 0x0a1dd8b0bf87f0a8 0x0143bb1617f0fe15 0xfe3ff9f1ff8ff1ff 0xffc7ff3e3ff1fe3f

def z365 : W := mkw 0x00105810b184b028 0x00020b0216309605 0xa000f871f181f07c 0xf4001f0e3e303e0f

def z366 : W := mkw 0x001850b0b08630a8 0x00030a161610c615 0x2038c1f1f20e71f9 0x4407183e3e41ce3f

def z367 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000018002001185 0x6000003000400230

def z368 : W := mkw 0x9bb7f80b0f6de251 0x5376ff0161edbc4a 0xfffff80f8fffe07f 0xbfffff01f1fffc0f

def z369 : W := mkw 0x644807efe0000b52 0x4c8900fdfc00016a 0x200007fff0001ff8 0x440000fffe0003ff

def z370 : W := mkw 0x001850b0a0863088 0x00030a161410c611 0x0038c1f1838e719d 0xe007183e3071ce33

def z371 : W := mkw 0x2040025650901660 0x2408004aca1202cc 0x21c0067e7df01e66 0xe43800cfcfbe03cc

def z372 : W := mkw 0x8896f00000000000 0x1112de0000000000 0x8007f80000000000 0x1000ff0000000000

def z373 : W := mkw 0x91a2200000680001 0x12344400000d0000 0x01c0000000700000 0x00380000000e0000

def z374 : W := mkw 0x9b3cd0a0aa4e6089 0x13679a141549cc11 0x5e38c181820e6199 0x0bc718303041cc33

def z375 : W := mkw 0x9fb7fd090f6de911 0x53f6ffa121edbd22 0xdffff9818fffe19f 0xbbffff3031fffc33

def z376 : W := mkw 0xdf7cd7f00ade7d81 0x9bef9afe015bcfb0 0x5ff8c7f00ffe7f87 0xebff18fe01ffcff0

def z377 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c7387e71f18060 0x9438e70fce3e300c

def z378 : W := mkw 0x0a05800b0e014250 0x4140b00161c0284a 0xfe07c00f8e01e07f 0x3fc0f801f1c03c0f

def z379 : W := mkw 0x001858a0a104a000 0x00030b1414209400 0xa038f9f1f38fe005 0xf4071f3e3e71fc00

def z380 : W := mkw 0x001850a0a0000000 0x00030a1414000000 0x0038387070000000 0x8007070e0e000000

def z381 : W := mkw 0xfdfef7fde0821082 0x1fbfdeffbc104210 0xfffffffff38e1187 0xfffffffffe71c230

def z382 : W := mkw 0xdf3cd5a9aa004912 0x5be79ab535400922 0x5e38c18182006199 0x0bc7183030400c33

def z383 : W := mkw 0x8814d009a0000002 0x11029a0134000000 0x0000c00180000000 0x0000180030000000

def z384 : W := mkw 0x0001000204014250 0x400020004080284a 0x000000000001e078 0x0000000000003c0f

def z385 : W := mkw 0x71eb2af655fb96e0 0xae3d655ecabf72dc 0xa1ff3e7e7dff9e66 0xf43fe7cfcfbff3cc

def z386 : W := mkw 0x020108020f6deb51 0x4040210041edbd6a 0x000000000ffffff8 0x2000000001ffffff

def z387 : W := mkw 0x756807ede0000002 0x0ead00fdbc000000 0x7ff807fff0000007 0xcfff00fffe000000

def z388 : W := mkw 0x00410a5215b19660 0x2008214a42b632cc 0x01c006700df19e66 0xe03800ce01be33cc

def z389 : W := mkw 0x000808b0b186b0a8 0x000101161630d615 0x200001f1f38ff1f8 0x6400003e3e71fe3f

def z390 : W := mkw 0x0e1dd5abae076bd8 0x41c3bab575c0ed7b 0xfe3fc78f8e0fffff 0x7fc7f8f1f1c1ffff

def z391 : W := mkw 0xfdfef7ede006208a 0x1fbfdefdbc00c411 0xfffffffff20e619f 0xdffffffffe41cc33

def z392 : W := mkw 0x2083281655a19260 0x24106502cab4324c 0xa007387e71819064 0xf400e70fce30320c

def z393 : W := mkw 0x20400a5651909660 0x2408014aca3212cc 0xa0003e7e71819e64 0xf40007cfce3033cc

def z394 : W := mkw 0x4e4d87fb0e935fd0 0xc9c9b0ff61d26bfa 0xfe07c7ff8e01ffff 0x7fc0f8fff1c03fff

def z395 : W := mkw 0x0400050b00000b50 0x408000a16000016a 0x0000060e00000e00 0x000000c1c00001c0

def z396 : W := mkw 0x77fb7ff6ffffbfe8 0xaeff6ffedffff7fd 0xffffffffffffffff 0xffffffffffffffff

def z397 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x5e07c78f8e006f9b 0x0bc0f8f1f1c00df3

def z398 : W := mkw 0xfdfeffede104a002 0x1fbfdffdbc209400 0xfffffffff38fe007 0xfffffffffe71fc00

def z399 : W := mkw 0xdd3cd5a9a006208a 0x1ba79ab53400c411 0x5e38c181820e6199 0x0bc718303041cc33

def z400 : W := mkw 0x1120000000000000 0x0224000000000000 0x5ff8000000000007 0x8bff000000000000

def z401 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5fc007f00c701f82 0x4bf800fe018e03f0

def z402 : W := mkw 0x020108101feff0a9 0x0040210203fdfe15 0x000000000ffff1f8 0x2000000001fffe3f

def z403 : W := mkw 0x0804800900000000 0x0100900120000000 0xa007c00f80000000 0x1400f801f0000000

def z404 : W := mkw 0x0400050900000000 0x008000a120000000 0x2000078f80000000 0x440000f1f0000000

def z405 : W := mkw 0x0040025000901400 0x0008004a00120280 0x0000067000001e00 0x400000ce000003c0

def z406 : W := mkw 0xdfefa7f00efb5d81 0x9bfdf4fe01df6bb0 0x5fff07f00ffe1f87 0xebffe0fe01ffc3f0

def z407 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000c0018001e078 0x1400180030003c0f

def z408 : W := mkw 0x576807f0bada1da8 0x8aed00fe175b43b5 0x7ff807f1fffe1fff 0xefff00fe3fffc3ff

def z409 : W := mkw 0x000800a0a0000000 0x0001001414000000 0x200001f1f0000000 0x4400003e3e000000

def z410 : W := mkw 0xbbe7aa565ff9d661 0x377cf54acbff3acc 0xffc73e7e7df19e66 0xfff8e7cfcfbe33cc

def z411 : W := mkw 0x776807f65ada1fe0 0xaeed00fecb5b43fc 0x7ff807fe7ffe1fe7 0xefff00ffcfffc3fc

def z412 : W := mkw 0x20c32a5655b7b6e8 0x2418654acab6f6dd 0xa1c73e7e7ffffffe 0xf438e7cfcfffffff

def z413 : W := mkw 0x132000000a480000 0x0264000001490000 0x5e380000020e0001 0x0bc700000041c000

def z414 : W := mkw 0xfdfef7fdf08210aa 0x1fbfdeffbe104215 0xfffffffff00011ff 0xdffffffffe00023f

def z415 : W := mkw 0x0601050b0e014b50 0x40c020a161c0296a 0x2000078f8e01fff8 0x640000f1f1c03fff

def z416 : W := mkw 0xfdfefffdf186b0aa 0x1fbfdfffbe30d615 0xfffffffff18e0007 0xdffffffffe31c000

def z417 : W := mkw 0x572805b00ada1d80 0x8ae500b6015b43b0 0x5e3801800ffe1f81 0x2bc7003001ffc3f0

def z418 : W := mkw 0x0000000b00000250 0x400000016000004a 0x2000000f80000078 0x04000001f000000f

def z419 : W := mkw 0x0a0580000e014000 0x0140b00001c02800 0x5e0700000c000002 0x0bc0e00001800000

def z420 : W := mkw 0x7fefafff5ffbdff0 0xeffdf5ffebff7bfe 0xffffffffffffffff 0xffffffffffffffff

def z421 : W := mkw 0xfdfff7efe4014252 0x5fbffefdfc80284a 0xfffffffff001e07f 0xdffffffffe003c0f

def z422 : W := mkw 0xa89ef8bdf186b0aa 0x1513df17be30d615 0xa03ff9fff38ff1fd 0xf407ff3ffe71fe3f

def z423 : W := mkw 0x77e327464e790f40 0xaefc64e8c9cf21e8 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z424 : W := mkw 0x9bb7f8100ffffd81 0x9376ff0201ffffb0 0xdffff8000fffff87 0xbbffff0001fffff0

def z425 : W := mkw 0x20d37a5655b5b660 0x241a6f4acab6b6cc 0xa1fffe7e7ffffe67 0xf43fffcfcfffffcc

def z426 : W := mkw 0x0083280205218240 0x0010650040a43048 0xa1c73e0e0df19e66 0xf438e7c1c1be33cc

def z427 : W := mkw 0xf1fa7af4f1b09422 0x3e3f4f5e9e361284 0x01f8387071f00000 0x803f070e0e3e0000

def z428 : W := mkw 0x001850a0a0062088 0x00030a141400c411 0xa038f9f1f20e619d 0xd4071f3e3e41cc33

def z429 : W := mkw 0x001850a0a0000000 0x00030a1414000000 0xa038f9f1f201f1fd 0xf4071f3e3e403e3f

def z430 : W := mkw 0x572805a00a4a0980 0x8ae500b401494130 0x5ff801800ffe0187 0xabff003001ffc030

def z431 : W := mkw 0xae97f50fee014b52 0x55d2fea1fdc0296a 0xfe07ff8ffe01ffff 0x7fc0fff1ffc03fff

def z432 : W := mkw 0x0805800b04014250 0x4100b0016080284a 0x0007000e00000000 0x0000e001c0000000

def z433 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0x5fffc78f80000003 0x0bfff8f1f0000000

def z434 : W := mkw 0xfdfeffedf104a02a 0x1fbfdffdbe209405 0xfffffffff001e07f 0xdffffffffe003c0f

def z435 : W := mkw 0x9bb6f8000b6ce001 0x1376df00016d9c00 0x5ff8f80003fe6001 0x8bff1f00007fcc00

def z436 : W := mkw 0x8a97f8000f25e001 0x1152ff0001e4bc00 0xde07f8000e01e007 0x3bc0ff0001c03c00

def z437 : W := mkw 0x9db6f50900000000 0x13b6dea120000000 0xffffff8f80000007 0xdffffff1f0000000

def z438 : W := mkw 0x2cc7af5f55b19660 0x2598f5ebeab632cc 0xffc7fffffdf19e67 0xfff8ffffffbe33cc

def z439 : W := mkw 0x0000001000901400 0x0000000200120280 0x000000000df01e00 0x2000000001be03c0

def z440 : W := mkw 0x8897f800b525e029 0x1112ff0016a4bc05 0xa007f801f001e078 0x1400ff003e003c0f

def z441 : W := mkw 0x512800a0004a0080 0x8a25001400094010 0x00380000000e0000 0x000700000001c000

def z442 : W := mkw 0xdf3dd5abae014b52 0x5be7bab575c0296a 0xfe3fc78f8e01ffff 0x7fc7f8f1f1c03fff

def z443 : W := mkw 0x021858b0bbdebda8 0x80430b16177bd7b5 0xa038f9f1fffffffd 0xf4071f3e3fffffff

def z444 : W := mkw 0x5d6c87e900000000 0x0bad90fd20000000 0xffffc7ff80000007 0xdffff8fff0000000

def z445 : W := mkw 0x020108100ffffd81 0x8040210201ffffb0 0x000000000fffff80 0x2000000001fffff0

def z446 : W := mkw 0x444807f0b0921da8 0x888900fe161243b5 0x200007f1f0001ff8 0x440000fe3e0003ff

def z447 : W := mkw 0x001058000104a000 0x00020b0000209400 0x8000f8000001e000 0x10001f0000003c00

def z448 : W := mkw 0x9bb7f8020f6de241 0x1376ff0041edbc48 0xfffffe0e0ffffe67 0xffffffc1c1ffffcc

def z449 : W := mkw 0xac96f50de0000002 0x1592dea1bc000000 0xfe07ff8ff0000007 0x5fc0fff1fe000000

def z450 : W := mkw 0x0e45875b0e915f50 0x41c8b0eb61d22bea 0xffc7c7ff8ff1ffff 0xfff8f8fff1fe3fff

def z451 : W := mkw 0x000800b000821080 0x0001001600104210 0xa038c1f1838ff1fd 0xf407183e3071fe3f

def z452 : W := mkw 0x1b2580000e494000 0x0364b00001c92800 0xdfffc0000fffe007 0xbbfff80001fffc00

def z453 : W := mkw 0x9fb7fd000f6de901 0x13f6ffa001edbd20 0xdfffff800fffff87 0xfbfffff001fffff0

def z454 : W := mkw 0x20c22a5451b09420 0x2418454a8a361284 0xa1c0387071f19064 0xf438070e0e3e320c

def z455 : W := mkw 0x57785ff00bdebd80 0x8aef0bfe017bd7b0 0xdff8fff00fffff87 0xfbff1ffe01fffff0

def z456 : W := mkw 0x0c04850900000000 0x018090a120000000 0xfe07c78f8201f1ff 0x7fc0f8f1f0403e3f

def z457 : W := mkw 0x0000000200000240 0x0000000040000048 0x2000060e00001e60 0x440000c1c00003cc

def z458 : W := mkw 0x00105800b104a028 0x00020b0016209405 0xa000f981f201f1fd 0x74001f303e403e3f

def z459 : W := mkw 0x00000800016ca001 0x00000100002d9400 0x0000000001fe0000 0x00000000003fc000

def z460 : W := mkw 0x57385db0bbceb9a8 0x8ae70bb61779d735 0xfe38f9f1f38ff1fd 0xffc71f3e3e71fe3f

def z461 : W := mkw 0x5f7ddffbbfdffff8 0xcbefbbff77fbffff 0xffffffffffffffff 0xffffffffffffffff

def z462 : W := mkw 0xfffffffdeffffd83 0x9fffffffbdffffb0 0xffffffffffffff87 0xfffffffffffffff0

def z463 : W := mkw 0x22c32a565ffb9fe0 0xa458654acbff73fc 0xa1c73e7e7fff9fe6 0xf438e7cfcffff3fc

def z464 : W := mkw 0x2887a80f5521c270 0x6510f501eaa4384e 0xa007f80ff001e078 0x1400ff01fe003c0f

def z465 : W := mkw 0x6e4d87efee014b52 0x4dc9b0fdfdc0296a 0xfe07c7fffe01ffff 0x7fc0f8ffffc03fff

def z466 : W := mkw 0x0001081215b19660 0x2000210242b632cc 0xa00038707df19e64 0xf400070e0fbe33cc

def z467 : W := mkw 0x133858b0bbceb0a8 0x02670b161779d615 0xfff8f9f1fffff1ff 0xffff1f3e3ffffe3f

def z468 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x01c73e7e7df00e02 0x8038e7cfcfbe01c0

def z469 : W := mkw 0xfdffffede5218002 0x1fbffffdbca43000 0xfffffffffdf18007 0xffffffffffbe3000

def z470 : W := mkw 0xb9f6f24440000000 0x173ede4888000000 0xfffffe7e70000007 0xdfffffcfce000000

def z471 : W := mkw 0x2ec7a74f4e014b50 0x45d8f4e9e9c0296a 0xffc7fffffe01ffff 0xfff8ffffffc03fff

def z472 : W := mkw 0x2040025450901420 0x2408004a8a120284 0x0000007070000000 0x0000000e0e000000

def z473 : W := mkw 0x020000000a004910 0x4040000001400922 0x0000000002006198 0x0000000000400c33

def z474 : W := mkw 0x5160024000580400 0x8a2c0048000b0080 0x01c0000000700000 0x00380000000e0000

def z475 : W := mkw 0x444807e000000000 0x088900fc00000000 0x000007f000000000 0x400000fe00000000

def z476 : W := mkw 0x8e97fd0b0f25eb51 0x51d2ffa161e4bd6a 0xfe07ff8f8e01ffff 0x7fc0fff1f1c03fff

def z477 : W := mkw 0x040805bbb0821bf8 0x408100b77610437f 0x200007fff0001ff8 0x440000fffe0003ff

def z478 : W := mkw 0x001858b00186b080 0x00030b160030d610 0x8038f9f0038ff185 0xf0071f3e0071fe30

def z479 : W := mkw 0x9b3cd8b0bbcef0a9 0x13679b161779de15 0xfe38f9f1f38ff1fd 0xffc71f3e3e71fe3f

def z480 : W := mkw 0x556807f000821080 0x0aad00fe00104210 0x5ff807f0038e1187 0xebff00fe0071c230

def z481 : W := mkw 0x2082200440000000 0x0410440088000000 0xa007380e70000000 0x1400e701ce000000

def z482 : W := mkw 0x557857e0a0000000 0x0aaf0afc14000000 0xfff8fff1f0000007 0xdfff1ffe3e000000

def z483 : W := mkw 0xfdbef5ade0000002 0x1fb7deb5bc000000 0xfe3ff98ff0000001 0x1fc7ff31fe000000

def z484 : W := mkw 0x809278000124a001 0x10124f0000249400 0x0000380000000000 0x0000070000000000

def z485 : W := mkw 0x020100000e014000 0x0040200001c02800 0x000000000e01e000 0x2000000001c03c00

def z486 : W := mkw 0x020000000a4a0980 0x8040000001494130 0x00000000020e0180 0x000000000041c030

def z487 : W := mkw 0xddfef7e000000000 0x1bbfdefc00000000 0xdffffff000000007 0xdbfffffe00000000

def z488 : W := mkw 0x020000000a580d00 0x80400000014b01a0 0x000000000c700e00 0x00000000018e01c0

def z489 : W := mkw 0x0a0588000f6de001 0x0140b10001edbc00 0xde07c0000fffe007 0x3bc0f80001fffc00

def z490 : W := mkw 0x028328000f6de001 0x0050650001edbc00 0x81c738000fffe006 0xb038e70001fffc00

def z491 : W := mkw 0xdffef7f00ada1d80 0x9bffdefe015b43b0 0xdffffff00ffe1f87 0xfbfffffe01ffc3f0

def z492 : W := mkw 0x576907f20edb5fd0 0xcaed20fe41db6bfa 0x5ff807f00fffffff 0xebff00fe01ffffff

def z493 : W := mkw 0x024002500ada1d80 0x8048004a015b43b0 0x01c006700ffe1f86 0xe03800ce01ffc3f0

def z494 : W := mkw 0xa886a00d40000002 0x1510d401a8000000 0x0007000e00000000 0x0000e001c0000000

def z495 : W := mkw 0xffeea7fd4ada1d82 0x9ffdd4ffa95b43b0 0x5fff07fe0ffe1f87 0xebffe0ffc1ffc3f0

def z496 : W := mkw 0x8897f8000525e001 0x1112ff0000a4bc00 0x81c7f8000df1e006 0xb038ff0001be3c00

def z497 : W := mkw 0x20c32a5455b19420 0x2418654a8ab63284 0x81c738707df18006 0xb038e70e0fbe3000

def z498 : W := mkw 0xdff7ff400f7ded01 0x9bfeffe801efbda0 0xdffffe000fffee07 0xbbffffc001fffdc0

def z499 : W := mkw 0x001958b2b5b7b6e8 0x20032b1656b6f6dd 0xa038f9f1fffffffd 0xf4071f3e3fffffff

def z500 : W := mkw 0x0e0485090a004910 0x41c090a121400922 0xfe07c78f8200619f 0x5fc0f8f1f0400c33

def z501 : W := mkw 0x000800b000821080 0x0001001600104210 0x000001f000001180 0x4000003e00000230

def z502 : W := mkw 0x9b2480000a484001 0x1364900001490800 0x5e00000000000000 0x0bc0000000000000

def z503 : W := mkw 0xffe7a74f4e014b52 0x5ffcf4e9e9c0296a 0xffc7c78f8e01ffff 0x7ff8f8f1f1c03fff

def z504 : W := mkw 0x132800b00aca1080 0x0265001601594210 0x5ff801f00ffe1187 0xebff003e01ffc230

def z505 : W := mkw 0xbff7ff5f5ffdff71 0x77feffebebffbfee 0xffffffffffffffff 0xffffffffffffffff

def z506 : W := mkw 0x2ac7aa565fb1d660 0x2558f54acbf63acc 0xffc7fe7e7ff1fe67 0xfff8ffcfcffe3fcc

def z507 : W := mkw 0xfbfffae4ef6de003 0x1f7fff5c9dedbc00 0xdffff8707fffe007 0xbbffff0e0ffffc00

def z508 : W := mkw 0xf1fa72e4e0000002 0x1e3f4e5c9c000000 0xa1f8f9f1f0000005 0xd43f1f3e3e000000

def z509 : W := mkw 0x132000100ada1d80 0x82640002015b43b0 0x5ff800000ffe1f87 0xabff000001ffc3f0

def z510 : W := mkw 0x0c1cddb9b186b0a8 0x01839bb73630d615 0xfe3ffffff38ff1ff 0xffc7fffffe71fe3f

def z511 : W := mkw 0x0e0585090e014000 0x01c0b0a121c02800 0xfe07c78f8e01e007 0x7fc0f8f1f1c03c00

def z512 : W := mkw 0x5560074000000000 0x0aac00e800000000 0x5fc0060000000002 0x0bf800c000000000

def z513 : W := mkw 0xb1f37a5655fdb661 0x363e6f4acabfb6cc 0xa1ff3e7e7dff9e66 0xf43fe7cfcfbff3cc

def z514 : W := mkw 0x00000000b0000028 0x0000000016000005 0x20000001f0000078 0x040000003e00000f

def z515 : W := mkw 0x0e058d1b1f87fbf8 0x41c0b1a363f0ff7f 0xfe07c78f8f8fffff 0x7fc0f8f1f1f1ffff

def z516 : W := mkw 0x020100120edb5fd0 0xc040200241db6bfa 0x000000000ffffff8 0x2000000001ffffff

def z517 : W := mkw 0xfffffffffffdf663 0x3fffffffffffbecc 0xfffffffffffffe67 0xffffffffffffffcc

def z518 : W := mkw 0x20c32a4445218000 0x0418654888a43000 0xa1c73e7e7df18006 0xf438e7cfcfbe3000

def z519 : W := mkw 0x20c2224440000000 0x0418444888000000 0x01c0387070000000 0x8038070e0e000000

def z520 : W := mkw 0x77e32f565ff99f60 0xaefc65eacbff33ec 0xffc73e7e7df19e66 0xfff8e7cfcfbe33cc

def z521 : W := mkw 0xa0927004e0000002 0x14124e009c000000 0x0000380070000000 0x000007000e000000

def z522 : W := mkw 0x001958b2b587b2e8 0x00032b1656b0f65d 0xa03fffffff8fffff 0xf407fffffff1ffff

def z523 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x01c007f00df01f86 0xe03800fe01be03f0

def z524 : W := mkw 0x060005000a000900 0x00c000a001400120 0x5e0006000c000e02 0x0bc000c0018001c0

def z525 : W := mkw 0xd13850a0a0000002 0x1a270a1414000000 0x0038000000000000 0x0007000000000000

def z526 : W := mkw 0x552805a000000000 0x0aa500b400000000 0x5e38018000000001 0x0bc7003000000000

def z527 : W := mkw 0x20cb2af6f5b396e8 0x2419655edeb672dd 0xa1c73ffffdf19ffe 0xf438e7ffffbe33ff

def z528 : W := mkw 0x20c2224440300400 0x2418444888060080 0x01c0000000700000 0x00380000000e0000

def z529 : W := mkw 0xffffffffffb1df72 0x7ffffffffff63bee 0xfffffffffff1ffff 0xfffffffffffe3fff

def z530 : W := mkw 0x2083280655218260 0x24106500caa4304c 0xa1c7380e7df18066 0xb438e701cfbe300c

def z531 : W := mkw 0xa8d7fa5655b5f661 0x351aff4acab6becc 0xa1c7fe7e7df1fe66 0xf438ffcfcfbe3fcc

def z532 : W := mkw 0x000800b000821080 0x0001001600104210 0x00380070018e0000 0x8007000e0031c000

def z533 : W := mkw 0xfdeea7ed40000002 0x1fbdd4fda8000000 0x5fff07fe00000007 0xcbffe0ffc0000000

def z534 : W := mkw 0x0083200004210000 0x0010640000842000 0x01c700000c700002 0x0038e000018e0000

def z535 : W := mkw 0x57680ff01bda9da0 0x8aed01fe037b53b4 0xfff83ff07fff9fe7 0xffff07fe0ffff3fc

def z536 : W := mkw 0x020100020e014b50 0x4040200041c0296a 0xa000c1818e01fffd 0x7400183031c03fff

def z537 : W := mkw 0xfde7af5f55b19662 0x3fbcf5ebeab632cc 0xffc73e7e7df19e66 0xfff8e7cfcfbe33cc

def z538 : W := mkw 0x0001080005218000 0x0000210000a43000 0x000000000df18000 0x2000000001be3000

def z539 : W := mkw 0x99bef8b0b186b0a8 0x1337df161630d615 0xfffff9f1f38ff1ff 0xffffff3e3e71fe3f

def z540 : W := mkw 0x6c4c87ede0000002 0x0d8990fdbc000000 0xfe07c7fff0000007 0x5fc0f8fffe000000

def z541 : W := mkw 0x020100020e014b50 0x4040200041c0296a 0xa007060e0e01fffe 0x7400e0c1c1c03fff

def z542 : W := mkw 0x00105800b104a028 0x00020b0016209405 0x0000380070000000 0x000007000e000000

def z543 : W := mkw 0x20db7af6f5b19660 0x241b6f5edeb632cc 0xa1fffffffdf19e67 0xf43fffffffbe33cc

def z544 : W := mkw 0x24c32f5f55b19f70 0x649865ebeab633ee 0xa1c73ffffdf19ffe 0xf438e7ffffbe33ff

def z545 : W := mkw 0x9bbff8b00feff081 0x1377ff1601fdfe10 0xdffff9f00ffff187 0xfbffff3e01fffe30

def z546 : W := mkw 0x020100000e694001 0x0040200001cd2800 0x000000000c700000 0x00000000018e0000

def z547 : W := mkw 0x0041025204911640 0x0008204a409222c8 0xa1c7067e0df19e66 0xf438e0cfc1be33cc

def z548 : W := mkw 0x5f2d85ab0e4b4bd0 0xcbe5b0b561c9697a 0xfe3fc78f8e0fffff 0x7fc7f8f1f1c1ffff

def z549 : W := mkw 0x000800b0b08210a8 0x0001001616104215 0x203801f1f38e11fd 0xe407003e3e71c23f

def z550 : W := mkw 0x776807fdeada1d82 0x8eed00ffbd5b43b0 0x7ff807fffffe1f87 0xefff00ffffffc3f0

def z551 : W := mkw 0xfffff7edee694003 0x1ffffefdbdcd2800 0xfffffffffc700007 0xdfffffffff8e0000

def z552 : W := mkw 0x26c32f565fb19f60 0x24d865eacbf633ec 0xffc73ffe7ff19fe7 0xfff8e7ffcffe33fc

def z553 : W := mkw 0x204802f6f09216e8 0x2409005ede1242dd 0x200007fff0001ff8 0x440000fffe0003ff

def z554 : W := mkw 0xfde6a74d40000002 0x1fbcd4e9a8000000 0xffc7c78f80000007 0x5ff8f8f1f0000000

def z555 : W := mkw 0x0083281015a19020 0x0010650202b43204 0xa1c738707df19066 0xf438e70e0fbe320c

def z556 : W := mkw 0x0a0480000a004000 0x0140900001400800 0x5e00c00002006001 0x0bc0180000400c00

def z557 : W := mkw 0x576807e00a480000 0x0aed00fc01490000 0x5ff807f00ffe0007 0xebff00fe01ffc000

def z558 : W := mkw 0x0c04850900000000 0x018090a120000000 0x5e00c18180000001 0x0bc0183030000000

def z559 : W := mkw 0xf5fa77ede0000002 0x1ebf4efdbc000000 0x21f83ffff0000000 0xc43f07fffe000000

def z560 : W := mkw 0xa897f00fe4014252 0x5512fe01fc80284a 0xa007f80ff001e078 0x1400ff01fe003c0f

def z561 : W := mkw 0x9fb7f50b0e014b50 0x53f6fea161c0296a 0xffffff8f8e01ffff 0xfffffff1f1c03fff

def z562 : W := mkw 0x000008101186b0a8 0x000001020230d615 0x00000000018e0000 0x000000000031c000

def z563 : W := mkw 0x060005000a000900 0x00c000a001400120 0x5e00018002000181 0x0bc0003000400030

def z564 : W := mkw 0x20c22a5651b09660 0x2418454aca3612cc 0x21c03e7e71f01e60 0xc43807cfce3e03cc

def z565 : W := mkw 0x2041025654911660 0x2408204aca9222cc 0xa007067e7c019e66 0x7400e0cfcf8033cc

def z566 : W := mkw 0x0001080215218260 0x2000210042a4304c 0x0000000000018060 0x000000000000300c

def z567 : W := mkw 0xdfe7a7400e794d01 0x9bfcf4e801cf29a0 0x5fc706000c700e02 0x0bf8e0c0018e01c0

def z568 : W := mkw 0x0000081011809020 0x0000010202301204 0x0000000001819060 0x200000000030320c

def z569 : W := mkw 0xfdfef7efe0000b52 0x5fbfdefdfc00016a 0xfffffffff0001fff 0xdffffffffe0003ff

def z570 : W := mkw 0x75eb2ff655b19660 0x2ebd65fecab632cc 0xffff3ffe7df19e67 0xffffe7ffcfbe33cc

def z571 : W := mkw 0x572005000a480900 0x8ae400a001490120 0x5e00000000000000 0x0bc0000000000000

def z572 : W := mkw 0xfffef7edea580d02 0x9fffdefdbd4b01a0 0xfffffffffc700e07 0xdfffffffff8e01c0

def z573 : W := mkw 0x99a6a00000000000 0x1334d40000000000 0x5fc7000000000002 0x0bf8e00000000000

def z574 : W := mkw 0x064007500a901d00 0x00c800ea015203a0 0x5fc007f00ff01f87 0xebf800fe01fe03f0

def z575 : W := mkw 0x516802e000000000 0x0a2d005c00000000 0x01f8007000000000 0x803f000e00000000

def z576 : W := mkw 0xf7fa77f4eada1d82 0x9eff4efe9d5b43b0 0x5ff83ff07ffe1f87 0xebff07fe0fffc3f0

def z577 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x5e00c1818e01fff9 0x2bc0183031c03fff

def z578 : W := mkw 0x644807fde0921d82 0x8c8900ffbc1243b0 0x200007fff0001f80 0x440000fffe0003f0

def z579 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x5e07060e0e01fffa 0x2bc0e0c1c1c03fff

def z580 : W := mkw 0xa8d6f24de0000002 0x151ade49bc000000 0xa1c7fe7ff0000006 0xd438ffcffe000000

def z581 : W := mkw 0x516802f000da1480 0x8a2d005e001b4290 0x01f801f003fe1185 0xe03f003e007fc230

def z582 : W := mkw 0xdf3cd5a00a4e6981 0x9be79ab40149cd30 0x5e38c180020e6181 0x0bc718300041cc30

def z583 : W := mkw 0x22c32a565ffdf661 0x2458654acbffbecc 0xa1c73e7e7ffffe66 0xf438e7cfcfffffcc

def z584 : W := mkw 0xfdeea7ede0000002 0x1fbdd4fdbc000000 0x7fc707fff0000002 0x4ff8e0fffe000000

def z585 : W := mkw 0x20c32a4655218260 0x24186548caa4304c 0xa1c73e7e70018066 0xd438e7cfce00300c

def z586 : W := mkw 0x464807f00a921d80 0x88c900fe015243b0 0x5e0007f00e001f87 0x6bc000fe01c003f0

def z587 : W := mkw 0x0040024000000000 0x0008004800000000 0x01c0067000000006 0xc03800ce00000000

def z588 : W := mkw 0x0e0585090e014910 0x41c0b0a121c02922 0xde07c1818e01e19f 0x3bc0f83031c03c33

def z589 : W := mkw 0x0001000204010240 0x0000200040802048 0x0007060e0c000e02 0x0000e0c1c18001c0

def z590 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x003839f0738e1185 0xe007073e0e71c230

def z591 : W := mkw 0x001058101186b0a8 0x00020b020230d615 0x8038f800038ff1fd 0xb0071f000071fe3f

def z592 : W := mkw 0xfdffffeff5218262 0x3fbffffdfea4304c 0xfffffffff0018067 0xdffffffffe00300c

def z593 : W := mkw 0x44585ff0b196bda8 0x888b0bfe1632d7b5 0xa038fff1f38ffffd 0xf4071ffe3e71ffff

def z594 : W := mkw 0x20da7af4f1b6b4a8 0x241b4f5e9e36d695 0xa1f8f9f1f3fff1fd 0xf43f1f3e3e7ffe3f

def z595 : W := mkw 0x576807e00a4a0980 0x8aed00fc01494130 0x5ff807f0020e0187 0xcbff00fe0041c030

def z596 : W := mkw 0xf1fa72e4e0000002 0x1e3f4e5c9c000000 0xa1ff3e7e70000006 0xd43fe7cfce000000

def z597 : W := mkw 0x20da7af4f1b6b4a8 0x241b4f5e9e36d695 0x01f8387071fe0000 0x803f070e0e3fc000

def z598 : W := mkw 0x0010500000000000 0x00020a0000000000 0x8038f80000000005 0x90071f0000000000

def z599 : W := mkw 0x644807fff0901662 0x2c8900fffe1202cc 0x200007fff0001e60 0x440000fffe0003cc

def z600 : W := mkw 0xfffff7edee014002 0x1ffffefdbdc02800 0xfffffffffe01e007 0xffffffffffc03c00

def z601 : W := mkw 0x77ea27f44ada1d80 0x8efd44fe895b43b0 0xffff3ffe7ffe1f87 0xffffe7ffcfffc3f0

def z602 : W := mkw 0x0805800004014000 0x0100b00000802800 0x8007c0000001e000 0x1000f80000003c00

def z603 : W := mkw 0x021958b2bf87fbf8 0x40432b1657f0ff7f 0xa038f9f1ff8ffffd 0xf4071f3e3ff1ffff

def z604 : W := mkw 0xb1f27a5451fcb421 0x363e4f4a8a3f9684 0x01f8387071fe0000 0x803f070e0e3fc000

def z605 : W := mkw 0x20db7af6f5b7b6e8 0x241b6f5edeb6f6dd 0xa1ff3e7e7dff9e66 0xf43fe7cfcfbff3cc

def z606 : W := mkw 0xdd3cd5a9a0000002 0x1ba79ab534000000 0xfe38f9f1f0000005 0xdfc71f3e3e000000

def z607 : W := mkw 0x77ea2ff45bfa9da0 0xaefd45fe8b7f53b4 0x5ff83ff07ffe1f87 0xebff07fe0fffc3f0

def z608 : W := mkw 0xfdfefffdf1b09422 0x3fbfdfffbe361284 0xfffffffff1f00007 0xdffffffffe3e0000

def z609 : W := mkw 0xdbfffaf00ffff481 0x9b7fff5e01fffe90 0xdffff8700fffe007 0xbbffff0e01fffc00

def z610 : W := mkw 0xffe7a74d4e694003 0x1ffcf4e9a9cd2800 0x5fc7060e0c700002 0x0bf8e0c1c18e0000

def z611 : W := mkw 0x0804800900004010 0x4100900120000802 0x0000c00180006018 0x0000180030000c03

def z612 : W := mkw 0x020000000a000900 0x0040000001400120 0x000000000e001f80 0x2000000001c003f0

def z613 : W := mkw 0x000008101186b0a8 0x000001020230d615 0xa000c181838ff1fd 0x740018303071fe3f

def z614 : W := mkw 0x9934d00000000000 0x13269a0000000000 0x5e38c00000000001 0x0bc7180000000000

def z615 : W := mkw 0x00000010108210a8 0x0000000202104215 0x00000000000011f8 0x000000000000023f

def z616 : W := mkw 0x9b35d0000e4d6001 0x1366ba0001c9ac00 0xde3fc0000e0fe007 0x3bc7f80001c1fc00

def z617 : W := mkw 0x0000001000da1480 0x80000002001b4290 0x0000000001fe0000 0x00000000003fc000

def z618 : W := mkw 0x9f35d50b0e4d6b51 0x53e6baa161c9ad6a 0xfe3fc78f8e0fffff 0x7fc7f8f1f1c1ffff

def z619 : W := mkw 0xbbf7fa444f6de001 0x177eff4889edbc00 0xfffffe7e7fffe007 0xffffffcfcffffc00

def z620 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x01c7060e0df19e62 0x2038e0c1c1be33cc

def z621 : W := mkw 0x0400050900000910 0x408000a120000122 0x0000018180000198 0x0000003030000033

def z622 : W := mkw 0xf9fef2ede0000002 0x1f3fde5dbc000000 0xa1fff87ff0000000 0x943fff0ffe000000

def z623 : W := mkw 0x20c3224644010240 0x04186448c8802048 0xa1c73e7e7c019e66 0xf438e7cfcf8033cc

def z624 : W := mkw 0xdfbffda9af6de003 0x1bf7ffb535edbc00 0xdffff9818fffe007 0xbbffff3031fffc00

def z625 : W := mkw 0x0000080011008020 0x0000010002201004 0xa000380070018060 0x140007000e00300c

def z626 : W := mkw 0xbbf7fa464f7de641 0x377eff48c9efbcc8 0xdffffe0e0fffee07 0xbbffffc1c1fffdc0

def z627 : W := mkw 0x9bb7f0000e694001 0x1376fe0001cd2800 0xdffff8000c700007 0x9bffff00018e0000

def z628 : W := mkw 0x516802f000da1480 0x8a2d005e001b4290 0x01f806700dfe1e06 0xe03f00ce01bfc3c0

def z629 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa038f871f18fe078 0x94071f0e3e31fc0f

def z630 : W := mkw 0x0000080001008000 0x0000010000201000 0x8000380001818004 0xb000070000303000

def z631 : W := mkw 0x000800a000020080 0x0001001400004010 0x00380180020e0181 0x000700300041c030

def z632 : W := mkw 0x9bbff8a0af6fe089 0x1377ff1415edfc11 0xdffff9818fffe19f 0xbbffff3031fffc33

def z633 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000c18180000005 0x5400183030000000

def z634 : W := mkw 0x9fb7fd0b0f6deb51 0x53f6ffa161edbd6a 0xdffffe0e0fffee07 0xbbffffc1c1fffdc0

def z635 : W := mkw 0x9bb7f8101feff0a9 0x1376ff0203fdfe15 0xdffff8000ffff1ff 0xbbffff0001fffe3f

def z636 : W := mkw 0x93b378000f6de001 0x12766f0001edbc00 0x01f838000fffe000 0xa03f070001fffc00

def z637 : W := mkw 0xffe6a74d4a580d02 0x9ffcd4e9a94b01a0 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z638 : W := mkw 0x020800b00ada1d80 0x80410016015b43b0 0x003801f00ffe1f85 0xe007003e01ffc3f0

def z639 : W := mkw 0xdfffffe00f6de001 0x1bfffffc01edbc00 0xdffffff00fffe007 0xfbfffffe01fffc00

def z640 : W := mkw 0x20c3224644310640 0x24186448c88620c8 0xa1c7060e0c719e66 0x7438e0c1c18e33cc

def z641 : W := mkw 0x0001000204010240 0x0000200040802048 0xa007c78f8e01ffff 0x7400f8f1f1c03fff

def z642 : W := mkw 0x8897f8000525e001 0x1112ff0000a4bc00 0x803ff800038fe005 0xb007ff000071fc00

def z643 : W := mkw 0x556807f000da1480 0x8aad00fe001b4290 0x5ff807f001fe0007 0xcbff00fe003fc000

def z644 : W := mkw 0x00585af0b196b4a8 0x000b0b5e1632d695 0xa1f8fff1ffffffff 0xf43f1ffe3fffffff

def z645 : W := mkw 0xdffffff0bffffda9 0x9bfffffe17ffffb5 0xfffffff1ffffffff 0xfffffffe3fffffff

def z646 : W := mkw 0x2040024440000000 0x0408004888000000 0x2000067e70000000 0x440000cfce000000

def z647 : W := mkw 0x0815d80bb505e278 0x4102bb0176a0bc4f 0xa007f80ff001e078 0x1400ff01fe003c0f

def z648 : W := mkw 0x000008001104a028 0x0000010002209405 0x000000000001e078 0x0000000000003c0f

def z649 : W := mkw 0x0a0580020e014240 0x0140b00041c02848 0xfe07c60e0e01fe67 0x7fc0f8c1c1c03fcc

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000c0000201e005 0x3000180000403c00

def z651 : W := mkw 0x060105020e010b40 0x00c020a041c02168 0xfe07078e0e019fe7 0x7fc0e0f1c1c033fc

def z652 : W := mkw 0x0e0485090a000900 0x01c090a121400120 0xfe07c78f8e001f87 0x7fc0f8f1f1c003f0

def z653 : W := mkw 0x0c05850b04014250 0x4180b0a16080284a 0xfe07c78f8001e07f 0x5fc0f8f1f0003c0f

def z654 : W := mkw 0x0e058d0b0f6deb51 0x41c0b1a161edbd6a 0xfe07c78f8fffffff 0x7fc0f8f1f1ffffff

def z655 : W := mkw 0xf1e2224440000002 0x1e3c444888000000 0x01c0000000000000 0x0038000000000000

def z656 : W := mkw 0x91b27800016ca001 0x12364f00002d9400 0x81f8f80003ffe005 0xb03f1f00007ffc00

def z657 : W := mkw 0x8a97f8000f6de001 0x1152ff0001edbc00 0x8007f8000fffe000 0x3000ff0001fffc00

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c18182006199 0x0000183030400c33

def z659 : W := mkw 0x57785ff0bbdebda8 0x8aef0bfe177bd7b5 0x5ff83ff07ffe1f87 0xebff07fe0fffc3f0

def z660 : W := mkw 0x9ba7a8000f69c001 0x1374f50001ed3800 0xdfc738000df18006 0xbbf8e70001be3000

def z661 : W := mkw 0x99b7f8000525e001 0x1336ff0000a4bc00 0xdffff8000001e007 0x9bffff0000003c00

def z662 : W := mkw 0x6440074d40000002 0x0c8800e9a8000000 0x0000060e00000000 0x000000c1c0000000

def z663 : W := mkw 0x28c7aa5f55b1d670 0x6518f54beab63ace 0xa1c7fe7ffdf1fe7e 0xf438ffcfffbe3fcf

def z664 : W := mkw 0x0600050b0a000b50 0x40c000a16140016a 0x7e00078f8e001fff 0x6fc000f1f1c003ff

def z665 : W := mkw 0x0083281215b19660 0x2010650242b632cc 0x81c738000df19e66 0xb038e70001be33cc

def z666 : W := mkw 0x20da7af4f186b0a8 0x041b4f5e9e30d615 0xa1fffffff38ff1ff 0xf43ffffffe71fe3f

def z667 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x0038c181838ff1f9 0x200718303071fe3f

def z668 : W := mkw 0xfdfff7efe4310642 0x3fbffefdfc8620c8 0xfffffffffc700e07 0xdfffffffff8e01c0

def z669 : W := mkw 0xfdf6f74d40000002 0x1fbedee9a8000000 0xdffffe0e00000007 0x9bffffc1c0000000

def z670 : W := mkw 0x2000000650000260 0x24000000ca00004c 0x2000000e70000060 0x04000001ce00000c

def z671 : W := mkw 0x2edfffffffb7fff8 0x65dbfffffff6ffff 0xffffffffffffffff 0xffffffffffffffff

def z672 : W := mkw 0x000808b0118290a0 0x0001011602305214 0xa03839f0738f91e5 0xf407073e0e71f23c

def z673 : W := mkw 0x99bef0a0a0000000 0x1337de1414000000 0xfffff9f1f0000007 0xdfffff3e3e000000

def z674 : W := mkw 0x001058000104a000 0x00020b0000209400 0xa038f981838ff1fd 0xf4071f303071fe3f

def z675 : W := mkw 0x5f6c87f90ada1d80 0x8bed90ff215b43b0 0xffffc7ff8ffe1f87 0xfffff8fff1ffc3f0

def z676 : W := mkw 0x573855a0aa4e2988 0x8ae70ab41549c531 0x5e38c181820e6199 0x0bc718303041cc33

def z677 : W := mkw 0xa897f80ff5218262 0x3512ff01fea4304c 0xa007f80ff0018060 0x1400ff01fe00300c

def z678 : W := mkw 0x001850a0a0000000 0x00030a1414000000 0x0038c18180000001 0x0007183030000000

def z679 : W := mkw 0x0001000204010240 0x0000200040802048 0x000000000c019e60 0x20000000018033cc

def z680 : W := mkw 0x91305000004c2001 0x12260a0000098400 0x00380000000e0000 0x000700000001c000

def z681 : W := mkw 0x556807f000da1d80 0x8aad00fe001b43b0 0x01f807f001fe1f80 0xc03f00fe003fc3f0

def z682 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x5e07078e0e001f87 0x6bc0e0f1c1c003f0

def z683 : W := mkw 0xfffffffdffeff0ab 0x1fffffffbffdfe15 0xfffffffffffff1ff 0xfffffffffffffe3f

def z684 : W := mkw 0x57690ff21ffb9fe0 0xaaed21fe43ff73fc 0x5ff807f00fff9fe7 0xebff00fe01fff3fc

def z685 : W := mkw 0x060805b00a821980 0x00c100b601504330 0x5e3807f00f8e1f87 0xebc700fe01f1c3f0

def z686 : W := mkw 0x0e0485090a004910 0x41c090a121400922 0xfe00c1818201f1fd 0x7fc0183030403e3f

def z687 : W := mkw 0x0001000204010240 0x0000200040802048 0xa007000e00018060 0x1400e001c000300c

def z688 : W := mkw 0x5f65874b0e594f50 0xcbecb0e961cb29ea 0xffc7c78f8e71ffff 0x7ff8f8f1f1ce3fff

def z689 : W := mkw 0xfffff7ffeedb5fd2 0xdffffefffddb6bfa 0xffffffffffffffff 0xffffffffffffffff

def z690 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000019064 0x740000000000320c

def z691 : W := mkw 0x572805b00aca1980 0x8ae500b601594330 0x5e3801f0038e1185 0xebc7003e0071c230

def z692 : W := mkw 0x0000081011809020 0x0000010202301204 0xa000f9f1f381f1fd 0xf4001f3e3e703e3f

def z693 : W := mkw 0xfde7a74f44310642 0x3fbcf4e9e88620c8 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z694 : W := mkw 0x572805a00a4a0980 0x8ae500b401494130 0x5e3807800e0e1f87 0x6bc700f001c1c3f0

def z695 : W := mkw 0x20c22a5451b09420 0x2418454a8a361284 0x01c03e707df01e06 0xe03807ce0fbe03c0

def z696 : W := mkw 0xa897f80de525e003 0x1512ff01bca4bc00 0xa007f80ff001e000 0x1400ff01fe003c00

def z697 : W := mkw 0x0040024000100400 0x0008004800020080 0x01c006000c700e02 0x003800c0018e01c0

def z698 : W := mkw 0xbbe7a2464e794641 0x377cf448c9cf28c8 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000181800011f8 0x440000303000023f

def z700 : W := mkw 0xfffefffdfbdebdaa 0x9fffdfffbf7bd7b5 0xffffffffffffffff 0xffffffffffffffff

def z701 : W := mkw 0x20d37a56f5b5b668 0x241a6f4adeb6b6cd 0xa1c7fe7ffdf1fe7e 0xf438ffcfffbe3fcf

def z702 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07c78f8c000e07 0x5fc0f8f1f18001c0

def z703 : W := mkw 0x577857f0aada1d80 0x8aef0afe155b43b0 0xfff8fff1fffe1f87 0xffff1ffe3fffc3f0

def z704 : W := mkw 0xfff7ff4d4f6de003 0x1ffeffe9a9edbc00 0xdffffe0e0fffe007 0xbbffffc1c1fffc00

def z705 : W := mkw 0xfdfef7fde0901402 0x1fbfdeffbc120280 0xfffffffffdf01e07 0xffffffffffbe03c0

def z706 : W := mkw 0x0805800b04014250 0x4100b0016080284a 0xa007c60f8c01fe7e 0x7400f8c1f1803fcf

def z707 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff8000dffe002 0x9bffff0001bffc00

def z708 : W := mkw 0x020108121ffff6e9 0x2040210243fffedd 0x000000000ffffff8 0x2000000001ffffff

def z709 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff38e0007 0xfffffffffe71c000

def z710 : W := mkw 0x020108121ffdff71 0x6040210243ffbfee 0x000000000ffffff8 0x2000000001ffffff

def z711 : W := mkw 0x444807fb00921fd0 0xc88900ff601243fa 0x000007fe00001f80 0x400000ffc00003f0

def z712 : W := mkw 0xfde6af5d5186b0aa 0x1fbcd5ebaa30d615 0x5fc7060e038ff1fa 0x2bf8e0c1c071fe3f

def z713 : W := mkw 0x644807f4e0921d82 0x8c8900fe9c1243b0 0x000007f070001f80 0x400000fe0e0003f0

def z714 : W := mkw 0x20c3225654b11660 0x2418644aca9622cc 0xa1c73e7e7c701e66 0xd438e7cfcf8e03cc

def z715 : W := mkw 0x99b7f800056da001 0x1336ff0000adb400 0xdffff8000dff8007 0xbbffff0001bff000

def z716 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff001e07f 0xdffffffffe003c0f

def z717 : W := mkw 0x8897f8020525e251 0x5112ff0040a4bc4a 0x8007f8000001e078 0x1000ff0000003c0f

def z718 : W := mkw 0x444807fbb0921ff8 0xc88900ff761243ff 0x200007fff0001ff8 0x440000fffe0003ff

def z719 : W := mkw 0x020108121ff9d661 0x2040210243ff3acc 0x000000000df19e60 0x2000000001be33cc

def z720 : W := mkw 0x99b7f800056de001 0x1336ff0000adbc00 0xdffff80001ffe007 0x9bffff00003ffc00

def z721 : W := mkw 0x9bb6f0000a4c6001 0x1376de0001498c00 0xdffff8000ffe6007 0xbbffff0001ffcc00

def z722 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1ff3e7e7fff9e67 0xf43fe7cfcffff3cc

def z723 : W := mkw 0x9bb7f0000e694001 0x1376fe0001cd2800 0xdffff8000ffe0007 0xbbffff0001ffc000

def z724 : W := mkw 0x93b278000b6ca001 0x12764f00016d9400 0x5ff838000dfe0002 0x8bff070001bfc000

def z725 : W := mkw 0x9bafa0b0beeb50a9 0x1375f41617dd6a15 0x7fc701f1fc7011fa 0x4ff8e03e3f8e023f

def z726 : W := mkw 0xfdfef7ede04a0082 0x9fbfdefdbc094010 0xfffffffff00e0007 0xdffffffffe01c000

def z727 : W := mkw 0x9bb7f8000f6de901 0x1376ff0001edbd20 0xdffff8000fffff87 0xbbffff0001fffff0

def z728 : W := mkw 0x77ab2da65f6b8be0 0xaef565b4cbed717c 0xfe3f398e720f81e1 0x1fc7e731ce41f03c

def z729 : W := mkw 0xdd3cd5a9a0000002 0x1ba79ab534000000 0xfe3ffffff0000007 0xdfc7fffffe000000

def z730 : W := mkw 0xbbb7f806ff6de269 0x3776ff00dfedbc4d 0xfffff80fffffe07f 0xbfffff01fffffc0f

def z731 : W := mkw 0x556807f000921480 0x0aad00fe00124290 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z732 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x01c73e7e7df19e62 0xa038e7cfcfbe33cc

def z733 : W := mkw 0x644807fdf0921daa 0x8c8900ffbe1243b5 0x200007fff0001ff8 0x440000fffe0003ff

def z734 : W := mkw 0x001058101184b020 0x00020b0202309604 0xa038f9f1f38ff1fd 0xf4071f3e3e71fe3f

def z735 : W := mkw 0x064807f00a921d80 0x00c900fe015243b0 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z736 : W := mkw 0xfdfef7ede0680003 0x1fbfdefdbc0d0000 0xfffffffff0700007 0xdffffffffe0e0000

def z737 : W := mkw 0x576007500ad81d00 0x8aec00ea015b03a0 0x5ff806700ffe1e07 0xebff00ce01ffc3c0

def z738 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73e7e7c719e62 0x5438e7cfcf8e33cc

def z739 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07c78f8c01fffa 0x5fc0f8f1f1803fff

def z740 : W := mkw 0x133058000b4ca000 0x02660b0001699400 0x5ff838000ffe0007 0xabff070001ffc000

def z741 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfe3ffffff0000001 0x5fc7fffffe000000

def z742 : W := mkw 0x91b27800016ca001 0x12364f00002d9400 0x5ff8380001fe0007 0x8bff0700003fc000

def z743 : W := mkw 0xf5fa77e4e0000002 0x1ebf4efc9c000000 0xffff3ffe70000007 0xdfffe7ffce000000

def z744 : W := mkw 0x132000000a480900 0x0264000001490120 0x5ff800000ffe1f87 0xabff000001ffc3f0

def z745 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff806700dfe1e06 0xebff00ce01bfc3c0

def z746 : W := mkw 0x132000000a480000 0x0264000001490000 0x5ff8000003fe0001 0x8bff0000007fc000

def z747 : W := mkw 0x4c4d87fb04935fd0 0xc989b0ff60926bfa 0xa007c7ff8001fff8 0x5400f8fff0003fff

def z748 : W := mkw 0x020108121fffbfe8 0xa040210243fff7fd 0x000000000ffffff8 0x2000000001ffffff

def z749 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff9800ffff187 0xfbffff3001fffe30

def z750 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0xa000c7f18201fffd 0x740018fe30403fff

def z751 : W := mkw 0x133050000a480000 0x02660a0001490000 0xdff8f8000ffe0007 0xbbff1f0001ffc000

def z752 : W := mkw 0x20db72e6e43726c8 0x241b6e5cdc86e4d9 0x01ffc78f8e7e6f9b 0x003ff8f1f1cfcdf3

def z753 : W := mkw 0x20c32a5655b396e0 0x2418654acab672dc 0xa1c73e7e7fff9fe6 0xf438e7cfcffff3fc

def z754 : W := mkw 0x9bb7f809af6de003 0x1376ff0135edbc00 0xdffff8018fffe007 0xbbffff0031fffc00

def z755 : W := mkw 0x9bb7f8020f6de241 0x1376ff0041edbc48 0xffffff8f8fffffff 0xfffffff1f1ffffff

def z756 : W := mkw 0x75fa77e4e0000000 0x0ebf4efc9c000000 0xfffffffff0000007 0xdffffffffe000000

def z757 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff807f00dfe0e07 0xcbff00fe01bfc1c0

def z758 : W := mkw 0xf3fb72e6ee014b52 0x5e7f6e5cddc0296a 0x01f838707e01fff8 0xa03f070e0fc03fff

def z759 : W := mkw 0x020108121ff99f60 0xa040210243ff33ec 0x000000000df19e60 0x2000000001be33cc

def z760 : W := mkw 0x33a328065f698260 0x26746500cbed304c 0xffff380e7fff8067 0xbfffe701cffff00c

def z761 : W := mkw 0xb9f6f24de0000002 0x173ede49bc000000 0xfffffe7ff0000007 0xdfffffcffe000000

def z762 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa1f8f9f1fffff1ff 0xf43f1f3e3ffffe3f

def z763 : W := mkw 0xfdbef5ade0000002 0x1fb7deb5bc000000 0xfe3ff9fff0000005 0xdfc7ff3ffe000000

def z764 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa03ffffff38ff1ff 0xf407fffffe71fe3f

def z765 : W := mkw 0x1b25800b0e494250 0x4364b00161c9284a 0xffffc00f8fffe07f 0xbffff801f1fffc0f

def z766 : W := mkw 0x99b7f8000525a000 0x1336ff0000a4b400 0xdffff8000fffe007 0xbbffff0001fffc00

def z767 : W := mkw 0x20c32a5655b5b660 0x2418654acab6b6cc 0xa1c73e7e7ffffe66 0xf438e7cfcfffffcc

def z768 : W := mkw 0x2ec6af5d5bb0dd30 0x65d8d5ebab761ba6 0x5fc0f9f1f3f06199 0x8bf81f3e3e7e0c33

def z769 : W := mkw 0xbdf6f74d40000000 0x17bedee9a8000000 0xfffffffff0000007 0xdffffffffe000000

def z770 : W := mkw 0x644807ffe0921fd2 0xcc8900fffc1243fa 0x200007fff0001ff8 0x440000fffe0003ff

def z771 : W := mkw 0x20c22a5451909420 0x0418454a8a321284 0xa1c73e7e7df19e66 0xf438e7cfcfbe33cc

def z772 : W := mkw 0x20c2224440100400 0x0418444888020080 0xa1c73e7e7c700e06 0xd438e7cfcf8e01c0

def z773 : W := mkw 0x132008000b4ca000 0x0264010001699400 0x5ff800000fffe007 0xabff000001fffc00

def z774 : W := mkw 0x95b27d0b016cab51 0x52b64fa1602d956a 0x21f83f8f81fe1ff8 0xc43f07f1f03fc3ff

def z775 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xffc7fffff0000002 0x5ff8fffffe000000

def z776 : W := mkw 0x93b378000f6da001 0x12766f0001edb400 0xdfff38000fff8007 0xbbffe70001fff000

def z777 : W := mkw 0xbbb7f8065f6de261 0x3776ff00cbedbc4c 0xfffffe0e7ffffe67 0xffffffc1cfffffcc

def z778 : W := mkw 0x444807f200921fd0 0xc88900fe401243fa 0x000007f000001ff8 0x400000fe000003ff

def z779 : W := mkw 0xbb74d2565adc7661 0x376e9a4acb5b8ecc 0x7e38c67e720e7e61 0x4fc718cfce41cfcc

def z780 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff201e007 0xfffffffffe403c00

def z781 : W := mkw 0x9bb7f80b0f6deb51 0x5376ff0161edbd6a 0xfffff80f8fffffff 0xbfffff01f1ffffff

def z782 : W := mkw 0x132000000a480000 0x0264000001490000 0xdff8c0000fffe007 0xbbff180001fffc00

def z783 : W := mkw 0x5f3cd5a9aa4e6998 0xcbe79ab53549cd33 0x5e38c181820e6199 0x0bc718303041cc33

def z784 : W := mkw 0x020108121ffbdff0 0xe040210243ff7bfe 0x000000000ffffff8 0x2000000001ffffff

def z785 : W := mkw 0x176007500ad81d00 0x02ec00ea015b03a0 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z786 : W := mkw 0xdd3dddbbb5b19662 0x3ba7bbb776b632cc 0x5e38c1818df19e61 0x2bc7183031be33cc

def z787 : W := mkw 0xccdffff005b7fd81 0x999bfffe00b6ffb0 0x8007fff00001ff80 0x5000fffe00003ff0

def z788 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x000007f002001f85 0x600000fe004003f0

def z789 : W := mkw 0x576807f0aada1d88 0x8aed00fe155b43b1 0x5ff807f18ffe1f9f 0xebff00fe31ffc3f3

def z790 : W := mkw 0x444807f0a0921d88 0x888900fe141243b1 0x000007f180001f98 0x400000fe300003f3

def z791 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xdffffe7e70000007 0x9bffffcfce000000

def z792 : W := mkw 0x2cdef7ede0000000 0x059bdefdbc000000 0xfffffffff0000007 0xdffffffffe000000

def z793 : W := mkw 0x0c05850b04014b50 0x4180b0a16080296a 0xfe07c78f8001ffff 0x5fc0f8f1f0003fff

def z794 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa038fff1ff8fffff 0xf4071ffe3ff1ffff

def z795 : W := mkw 0x66490fedef6de003 0x0cc921fdbdedbc00 0x200007ffffffe000 0x640000fffffffc00

def z796 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0xdff8c7f00fffff87 0xfbff18fe01fffff0

def z797 : W := mkw 0x13a320000e690000 0x0274640001cd2000 0x5fff00000ffe0007 0xabffe00001ffc000

def z798 : W := mkw 0xfdeea7ed40000002 0x1fbdd4fda8000000 0xffff3ffe70000007 0xdfffe7ffce000000

def z799 : W := mkw 0x9bb7f80b0f6de251 0x5376ff0161edbc4a 0xfffff98f8ffff1ff 0xffffff31f1fffe3f

def z800 : W := mkw 0x132000000a480000 0x0264000001490000 0xfff8c1818ffff1ff 0xffff183031fffe3f

def z801 : W := mkw 0x9bb6f8000b6ce001 0x1376df00016d9c00 0x5ff8380001fe0000 0x8bff0700003fc000

def z802 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffffc001e07 0xffffffffff8003c0

def z803 : W := mkw 0x020108121fb7fff8 0x6040210243f6ffff 0x000000000ffffff8 0x2000000001ffffff

def z804 : W := mkw 0x0083281215a19260 0x0010650242b4324c 0xa1c73e7e7df19e66 0xf438e7cfcfbe33cc

def z805 : W := mkw 0x2cc6a74d40000000 0x0598d4e9a8000000 0xffc73e7e70000006 0xdff8e7cfce000000

def z806 : W := mkw 0x132000000a480000 0x0264000001490000 0x5ff806000ffe1e07 0xebff00c001ffc3c0

def z807 : W := mkw 0x9bb7f8020f6deb51 0x5376ff0041edbd6a 0xfffff9818fffffff 0xffffff3031ffffff

def z808 : W := mkw 0xfdfef7ede0020982 0x9fbfdefdbc004130 0xfffffffff0000187 0xdffffffffe000030

def z809 : W := mkw 0x132008000b488000 0x0264010001691000 0xdff838000fff8007 0xbbff070001fff000

def z810 : W := mkw 0x020108121fb1df70 0x6040210243f63bee 0x000000000df19e60 0x2000000001be33cc

def z811 : W := mkw 0x576807f00ada5d90 0xcaed00fe015b4bb2 0x5ff807f00ffe7f9f 0xebff00fe01ffcff3

def z812 : W := mkw 0x572805a00a4a0980 0x8ae500b401494130 0x5ff807800ffe1f87 0xebff00f001ffc3f0

def z813 : W := mkw 0x596d82fb04db56d0 0xcb2db05f609b6ada 0xa1ffc07f81ffe078 0x943ff80ff03ffc0f

def z814 : W := mkw 0xbbb6f00dea480002 0x1776de01bd490000 0xfffff80ffffe0007 0xbfffff01ffffc000

def z815 : W := mkw 0x9b2480000a484001 0x1364900001490800 0x5ff800000ffe0007 0xabff000001ffc000

def z816 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe3fc78f8f8fffff 0xffc7f8f1f1f1ffff

def z817 : W := mkw 0x644807f440921d80 0x8c8900fe881243b0 0x200007fe70001f80 0x440000ffce0003f0

def z818 : W := mkw 0x9bb7f8001f6de021 0x1376ff0003edbc04 0xfffff8007fffe067 0xbfffff000ffffc0c

def z819 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x000001f000000180 0x0000003e00000030

def z820 : W := mkw 0xaa96f01deada1d82 0x9552de03bd5b43b0 0xa007f80ffffe1f80 0x3400ff01ffffc3f0

def z821 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0x5e07c78f8e01fffb 0x2bc0f8f1f1c03fff

def z822 : W := mkw 0x644807fff09216ea 0x2c8900fffe1242dd 0x200007fff0001ff8 0x440000fffe0003ff

def z823 : W := mkw 0xbbb7f8064f6de241 0x3776ff00c9edbc48 0xdffff80e0fffe007 0xbbffff01c1fffc00

def z824 : W := mkw 0x44585ff0b196bda8 0x888b0bfe1632d7b5 0xa000fff1f001fff8 0x54001ffe3e003fff

def z825 : W := mkw 0x132000100ad81400 0x02640002015b0280 0x5ff800000ffe1e07 0xabff000001ffc3c0

def z826 : W := mkw 0x576007400a580d00 0x8aec00e8014b01a0 0x5ff806000dfe0e02 0x8bff00c001bfc1c0

def z827 : W := mkw 0x132000000a480000 0x0264000001490000 0x5ff801800ffe1187 0xebff003001ffc230

def z828 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff8000ffff1ff 0xbbffff0001fffe3f

def z829 : W := mkw 0x576807e00a580d00 0x8aed00fc014b01a0 0x5ff807f00ffe0e07 0xebff00fe01ffc1c0

def z830 : W := mkw 0xfdeea7ede0000002 0x1fbdd4fdbc000000 0xffc73ffff0000006 0xdff8e7fffe000000

def z831 : W := mkw 0x444807f0a0921d80 0x888900fe141243b0 0x200007f1f0001f80 0x440000fe3e0003f0

def z832 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa038f9f1f20ff1f9 0x54071f3e3e41fe3f

def z833 : W := mkw 0xbbb7f8044f6de001 0x1776ff0089edbc00 0xfffff80e7fffe007 0xbfffff01cffffc00

def z834 : W := mkw 0xfdfef7ede0020082 0x1fbfdefdbc004010 0xfffffffff20e0187 0xdffffffffe41c030

def z835 : W := mkw 0x644807f6f0921fe8 0xac8900fede1243fd 0x200007fff0001ff8 0x440000fffe0003ff

def z836 : W := mkw 0x132100000e494000 0x0264200001c92800 0x5ff800000fffe007 0xabff000001fffc00

def z837 : W := mkw 0x444807f0b0921da8 0x888900fe161243b5 0x000007f070001f80 0x400000fe0e0003f0

def z838 : W := mkw 0x13a328000f6de001 0x0274650001edbc00 0xdfff38000fffe007 0xbbffe70001fffc00

def z839 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0x5fffc0000fffe003 0x2bfff80001fffc00

def z840 : W := mkw 0xa897f80f5525e271 0x7512ff01eaa4bc4e 0xa007f80ff001e078 0x1400ff01fe003c0f

def z841 : W := mkw 0x0c04850900000000 0x018090a120000000 0xfe07fffff0000007 0xdfc0fffffe000000

def z842 : W := mkw 0x20c32a5655b396e8 0x2418654acab672dd 0xa1c73e7e7df19ffe 0xf438e7cfcfbe33ff

def z843 : W := mkw 0x20c3224644310640 0x24186448c88620c8 0xa1c73e7e7c719e66 0xf438e7cfcf8e33cc

def z844 : W := mkw 0xf9fef2e4e0000002 0x1f3fde5c9c000000 0xfffffe7e70000007 0xdfffffcfce000000

def z845 : W := mkw 0xfdfef7ede0480002 0x1fbfdefdbc090000 0xfffffffff1fe0007 0xdffffffffe3fc000

def z846 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xffc7c78f8ff1ffff 0xfff8f8f1f1fe3fff

def z847 : W := mkw 0x20c32a5655b5f661 0x2418654acab6becc 0xa1c73e7e7df1fe66 0xf438e7cfcfbe3fcc

def z848 : W := mkw 0xfdfef7ede006208a 0x1fbfdefdbc00c411 0xfffffffff00e0007 0xdffffffffe01c000

def z849 : W := mkw 0xfdfef7ede002008a 0x1fbfdefdbc004011 0xfffffffff000019f 0xdffffffffe000033

def z850 : W := mkw 0x1b2588000f6de001 0x0364b10001edbc00 0xdfffc0000fffe007 0xbbfff80001fffc00

def z851 : W := mkw 0xfdfef7e440000000 0x1fbfdefc88000000 0xfffffffe70000007 0xdfffffffce000000

def z852 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff806700ffe1f82 0xabff00ce01ffc3f0

def z853 : W := mkw 0x1ba7a8000f69c000 0x0374f50001ed3800 0xdffff8000fffe007 0xbbffff0001fffc00

def z854 : W := mkw 0x20c32a5655b1d670 0x6418654acab63ace 0xa1c73e7e7df1fe7e 0xf438e7cfcfbe3fcf

def z855 : W := mkw 0x576807f00ad81400 0x0aed00fe015b0280 0x5ff807f00ffe1e07 0xebff00fe01ffc3c0

def z856 : W := mkw 0x0a97f8000f25e000 0x0152ff0001e4bc00 0xdffff8000fffe007 0xbbffff0001fffc00

def z857 : W := mkw 0xfdfef7ede0580402 0x9fbfdefdbc0b0080 0xfffffffff0700007 0xdffffffffe0e0000

def z858 : W := mkw 0x9bb7f8020f6de241 0x1376ff0041edbc48 0xdffffe0e0fffee07 0xbbffffc1c1fffdc0

def z859 : W := mkw 0x8897f80b0525e251 0x5112ff0160a4bc4a 0x8007f80e0001e000 0x1000ff01c0003c00

def z860 : W := mkw 0x20c32a5655b5b668 0x2418654acab6b6cd 0xa1c73e7e7df1fe7e 0xf438e7cfcfbe3fcf

def z861 : W := mkw 0x28c6a24440000000 0x0518d44888000000 0xffc7fe7e70000007 0xdff8ffcfce000000

def z862 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff807f00ffe0f83 0x8bff00fe01ffc1f0

def z863 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xfffffe0e0fffe007 0xffffffc1c1fffc00

def z864 : W := mkw 0x576807e00a480900 0x0aed00fc01490120 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z865 : W := mkw 0x9bb6f8000b4ca000 0x1376df0001699400 0xdffff8000fffe007 0xbbffff0001fffc00

def z866 : W := mkw 0x9bb7f800af6de001 0x1376ff0015edbc00 0xfffff801ffffe007 0xbfffff003ffffc00

def z867 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0xfff8c7f18ffe1f87 0xffff18fe31ffc3f0

def z868 : W := mkw 0x7deea7ed40000000 0x0fbdd4fda8000000 0xfffffffff0000007 0xdffffffffe000000

def z869 : W := mkw 0x556807f000da1480 0x8aad00fe001b4290 0x5ff807f00dfe1e07 0xebff00fe01bfc3c0

def z870 : W := mkw 0x8897f80bb525e279 0x5112ff0176a4bc4f 0xa007f80ff001e078 0x1400ff01fe003c0f

def z871 : W := mkw 0xecdef7ede0000002 0x1d9bdefdbc000000 0xfe07fffff0000007 0x5fc0fffffe000000

def z872 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffffdf00007 0xffffffffffbe0000

def z873 : W := mkw 0x132100020e490240 0x0264200041c92048 0xffff060e0fff9e67 0xffffe0c1c1fff3cc

def z874 : W := mkw 0x57705f40bb5cad28 0x8aee0be8176b95a5 0xffc0fe01fc71ee7a 0x1ff81fc03f8e3dcf

def z875 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xfffff8707fffe007 0xffffff0e0ffffc00

def z876 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xffff3e7e70000006 0xdfffe7cfce000000

def z877 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x200007f180001ff8 0x440000fe300003ff

def z878 : W := mkw 0x172805b00aca1980 0x02e500b601594330 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z879 : W := mkw 0x13b378000f6da000 0x02766f0001edb400 0xdffff8000fffe007 0xbbffff0001fffc00

def z880 : W := mkw 0x6c5cd7ede0000002 0x0d8b9afdbc000000 0xfe3ffffff0000007 0xdfc7fffffe000000

def z881 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x000007f00c001f86 0x600000fe018003f0

def z882 : W := mkw 0x132000000a480000 0x0264000001490000 0x5ff800000dfe0002 0x8bff000001bfc000

def z883 : W := mkw 0x9bb7f8090f6de011 0x5376ff0121edbc02 0xdffff8018fffe01f 0xbbffff0031fffc03

def z884 : W := mkw 0xecdef7fde0921d82 0x9d9bdeffbc1243b0 0xa007fffff0001f80 0x5400fffffe0003f0

def z885 : W := mkw 0x00410a5215919660 0x0008214a42b232cc 0xa1c73e7e7df19e66 0xf438e7cfcfbe33cc

def z886 : W := mkw 0x93b278000b6ca001 0x12764f00016d9400 0xdff8f8000fffe007 0xbbff1f0001fffc00

def z887 : W := mkw 0x9bb7f800bf6de029 0x1376ff0017edbc05 0xdffff8007fffe007 0xbbffff000ffffc00

def z888 : W := mkw 0x576007500ada1d80 0x8aec00ea015b43b0 0x5ff806000ffe1f87 0xabff00c001ffc3f0

def z889 : W := mkw 0x444907f204931fc0 0x888920fe409263f8 0xa00707fe0c019fe6 0x7400e0ffc18033fc

def z890 : W := mkw 0x9b35d8000f6de001 0x1366bb0001edbc00 0x5ff8c0000fffe007 0xabff180001fffc00

def z891 : W := mkw 0x9bb6f8000b6ca001 0x1376df00016d9400 0xdffff8000ffe0007 0xbbffff0001ffc000

def z892 : W := mkw 0x7fe7a74f4e794f50 0xeffcf4e9e9cf29ea 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z893 : W := mkw 0x572805b00ada1d80 0x8ae500b6015b43b0 0x5ff801800ffe1f87 0xabff003001ffc3f0

def z894 : W := mkw 0x13a220000a480000 0x0274440001490000 0xdfff38000ffe0007 0xbbffe70001ffc000

def z895 : W := mkw 0x99b6f800016ca001 0x1336df00002d9400 0x5ff8f80001fe0001 0x8bff1f00003fc000

def z896 : W := mkw 0x9bb7f80b0f6de251 0x5376ff0161edbc4a 0xdffff80e0fffe007 0xbbffff01c1fffc00

def z897 : W := mkw 0x001850b0a0821080 0x00030a1614104210 0xa038f9f1f38ff1fd 0xf4071f3e3e71fe3f

def z898 : W := mkw 0x20c22a5451b09420 0x2418454a8a361284 0xa1c73e7e7df01e06 0xf438e7cfcfbe03c0

def z899 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff807f00fffffff 0xebff00fe01ffffff

def z900 : W := mkw 0x75e2274440000000 0x0ebc44e888000000 0xffc73e7e70000006 0xdff8e7cfce000000

def z901 : W := mkw 0xffe7a74f4e694b53 0x5ffcf4e9e9cd296a 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z902 : W := mkw 0xa897f80fe525e253 0x5512ff01fca4bc4a 0xa007f80ff001e078 0x1400ff01fe003c0f

def z903 : W := mkw 0x464807f00a921d80 0x88c900fe015243b0 0x000007f00e001f80 0x600000fe01c003f0

def z904 : W := mkw 0xbfe7a74f4e794f51 0x77fcf4e9e9cf29ea 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z905 : W := mkw 0x9bb7f8020f6deb51 0x5376ff0041edbd6a 0xdffff8000fffee07 0xbbffff0001fffdc0

def z906 : W := mkw 0x20c2225650901660 0x2418444aca1202cc 0xa1c73e7e7df01e66 0xf438e7cfcfbe03cc

def z907 : W := mkw 0x9ba7a8000f6de001 0x1374f50001edbc00 0x5fff00000fffe007 0xabffe00001fffc00

def z908 : W := mkw 0x9b35d0000e4d6001 0x1366ba0001c9ac00 0xdfffc0000fffe007 0xbbfff80001fffc00

def z909 : W := mkw 0x1b2480000a480000 0x0364900001490000 0xdfffc0000ffe0007 0xbbfff80001ffc000

def z910 : W := mkw 0x644807f640921fc0 0xac8900fec81243f8 0x000007fe00001f80 0x400000ffc00003f0

def z911 : W := mkw 0x93b378000f6de001 0x12766f0001edbc00 0x5ff838000fffe007 0xabff070001fffc00

def z912 : W := mkw 0x9bb7f8021f6de261 0x3376ff0043edbc4c 0xdffff8000fffe067 0xbbffff0001fffc0c

def z913 : W := mkw 0x576807f0bada1da8 0x8aed00fe175b43b5 0xfff8c7f1ffffffff 0xffff18fe3fffffff

def z914 : W := mkw 0x576807f90ada1d80 0x8aed00ff215b43b0 0x7ff807ff8ffe1f87 0xefff00fff1ffc3f0

def z915 : W := mkw 0x444807f000921d80 0x888900fe001243b0 0x0000067000000e00 0x000000ce000001c0

def z916 : W := mkw 0x444807f900921d80 0x888900ff201243b0 0x200007ff80001f80 0x440000fff00003f0

def z917 : W := mkw 0x71fa7af4f1feb4a8 0xae3f4f5e9e3fd695 0x01f8387071fe0000 0x803f070e0e3fc000

def z918 : W := mkw 0x933050000a4c2001 0x12660a0001498400 0x5ff800000ffe0007 0xabff000001ffc000

def z919 : W := mkw 0xfdfef7ede0004012 0x5fbfdefdbc000802 0xfffffffff000601f 0xdffffffffe000c03

def z920 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff80003ffe001 0x9bffff00007ffc00

def z921 : W := mkw 0x9bb7f80bbf6de279 0x5376ff0177edbc4f 0xfffff80fffffe07f 0xbfffff01fffffc0f

def z922 : W := mkw 0xfde6a74d40000002 0x1fbcd4e9a8000000 0xffc7fffff0000007 0xdff8fffffe000000

def z923 : W := mkw 0xa897f8064525e241 0x3512ff00c8a4bc48 0x8007f80e0001e000 0x1000ff01c0003c00

def z924 : W := mkw 0x20c32a4645218240 0x04186548c8a43048 0xa1c73e7e7df19e66 0xf438e7cfcfbe33cc

def z925 : W := mkw 0x1120000000480000 0x0224000000090000 0x5ff8000001fe0007 0x8bff0000003fc000

def z926 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff807800ffe1f83 0x2bff00f001ffc3f0

def z927 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffffe000ffffe07 0xfbffffc001ffffc0

def z928 : W := mkw 0x776807f45ada1da0 0xaeed00fe8b5b43b4 0x5ff807f07ffe1f87 0xebff00fe0fffc3f0

def z929 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73e7e7df18e62 0x9438e7cfcfbe31cc

def z930 : W := mkw 0x576807f0aada1d80 0x8aed00fe155b43b0 0x7ff807f1fffe1f87 0xefff00fe3fffc3f0

def z931 : W := mkw 0x93b278000b6ca001 0x12764f00016d9400 0x5ff8380003fe0001 0x8bff0700007fc000

def z932 : W := mkw 0x576807f0bada1da8 0x8aed00fe175b43b5 0x5ff807f07ffe1f87 0xebff00fe0fffc3f0

def z933 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07fffffe01ffff 0xffc0ffffffc03fff

def z934 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0xa038f9f1f38fe1f9 0x94071f3e3e71fc3f

def z935 : W := mkw 0x644807fde0921482 0x8c8900ffbc124290 0x200007fff0000000 0x440000fffe000000

def z936 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73e7e7df00e06 0xd438e7cfcfbe01c0

def z937 : W := mkw 0x0e1dddbbbf87fbf8 0x41c3bbb777f0ff7f 0x5e3f3e7e7d8e0e02 0x8bc7e7cfcfb1c1c0

def z938 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff00011ff 0xdffffffffe00023f

def z939 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c7fffffdf19e67 0xf438ffffffbe33cc

def z940 : W := mkw 0x9dbef5a9a0000000 0x13b7deb534000000 0xfffffffff0000007 0xdffffffffe000000

def z941 : W := mkw 0x9bb6f8000b6ce001 0x1376df00016d9c00 0xdff8f80003ffe005 0xbbff1f00007ffc00

def z942 : W := mkw 0x021950a2ae014b50 0x40432a1455c0296a 0xa038f9f1fe01fffd 0xf4071f3e3fc03fff

def z943 : W := mkw 0x2897f80ff525e278 0x6512ff01fea4bc4f 0xa007f80ff001e078 0x1400ff01fe003c0f

def z944 : W := mkw 0x9bb7f8090f6de001 0x1376ff0121edbc00 0xfffff80f8fffe007 0xbfffff01f1fffc00

def z945 : W := mkw 0x001850a0a0062088 0x00030a141400c411 0xa038f9f1f20ff1fd 0xf4071f3e3e41fe3f

def z946 : W := mkw 0x776807f44ada1d80 0x8eed00fe895b43b0 0x7ff807fe7ffe1f87 0xefff00ffcfffc3f0

def z947 : W := mkw 0x0c04850b00000b50 0x418090a16000016a 0xfe07c78f8201ffff 0x7fc0f8f1f0403fff

def z948 : W := mkw 0x536802f00ada1480 0x8a6d005e015b4290 0x5ff806700ffe1e07 0xebff00ce01ffc3c0

def z949 : W := mkw 0x9b34d8000b4ce001 0x13669b0001699c00 0xdff8f8000fffe007 0xbbff1f0001fffc00

def z950 : W := mkw 0x444807f210921fe0 0xa88900fe421243fc 0x000007f000001fe0 0x400000fe000003fc

def z951 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73ffe7ff19fe7 0xf438e7ffcffe33fc

def z952 : W := mkw 0x020108121fffffe1 0xa040210243fffffc 0x000000000fffffe0 0x2000000001fffffc

def z953 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0x5fff3ffe70000007 0xcbffe7ffce000000

def z954 : W := mkw 0x1b2580000e494000 0x0364b00001c92800 0x5fff00000ffe0007 0xabffe00001ffc000

def z955 : W := mkw 0x9bb7f8001f6de029 0x1376ff0003edbc05 0xdffff8000fffe07f 0xbbffff0001fffc0f

def z956 : W := mkw 0xa897f806f525e269 0x3512ff00dea4bc4d 0xa007f80ff001e078 0x1400ff01fe003c0f

def z957 : W := mkw 0xf1fa7af4f1deb4aa 0x9e3f4f5e9e3bd695 0x01f8387071fe0000 0x803f070e0e3fc000

def z958 : W := mkw 0x0e05850b0e494b50 0x41c0b0a161c9296a 0xfe07c78f8fffffff 0x7fc0f8f1f1ffffff

def z959 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x7ff807f18ffe1fff 0xefff00fe31ffc3ff

def z960 : W := mkw 0xac9ef5ade0000002 0x1593deb5bc000000 0xfe3ffffff0000007 0xdfc7fffffe000000

def z961 : W := mkw 0x0c05850b04010240 0x0180b0a160802048 0xfe07c78f8e01ffff 0x7fc0f8f1f1c03fff

def z962 : W := mkw 0x99b6f800016ca001 0x1336df00002d9400 0x5fff380001fe0002 0x8bffe700003fc000

def z963 : W := mkw 0x99b6f00000480000 0x1336de0000090000 0xdffff80001fe0007 0x9bffff00003fc000

def z964 : W := mkw 0x0e05850b0e014b50 0x41c0b0a161c0296a 0xfe07c78f8201fff9 0x5fc0f8f1f0403fff

def z965 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c7fe7e7ff1fe67 0xf438ffcfcffe3fcc

def z966 : W := mkw 0x13305800bb4ca028 0x02660b0017699405 0xfff8f801ffffe07f 0xbfff1f003ffffc0f

def z967 : W := mkw 0x576807f01ada1da8 0x8aed00fe035b43b5 0x5ff807f00ffe1fff 0xebff00fe01ffc3ff

def z968 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff801f00ffe1f81 0xabff003e01ffc3f0

def z969 : W := mkw 0xacd6f74de0000002 0x159adee9bc000000 0xffc7fffff0000007 0xdff8fffffe000000

def z970 : W := mkw 0x001858a0b106a0a8 0x00030b141620d415 0xa038f9f1f20fe1fd 0xd4071f3e3e41fc3f

def z971 : W := mkw 0x576807e00a5a0d80 0x8aed00fc014b41b0 0x5ff807800ffe0f87 0xabff00f001ffc1f0

def z972 : W := mkw 0x444807f010921da8 0x888900fe021243b5 0x000007f000001ff8 0x400000fe000003ff

def z973 : W := mkw 0x464907f20e935fd0 0xc8c920fe41d26bfa 0x000007f00e01fff8 0x600000fe01c03fff

def z974 : W := mkw 0x444807f200921fc0 0x888900fe401243f8 0x200007fe00001fe0 0x440000ffc00003fc

def z975 : W := mkw 0x132008000b6ca001 0x02640100016d9400 0x5ff800000ffe0007 0xabff000001ffc000

def z976 : W := mkw 0x9bb7f8000f698000 0x1376ff0001ed3000 0xdffff8000fff8007 0xbbffff0001fff000

def z977 : W := mkw 0xfdf6f74d40000002 0x1fbedee9a8000000 0xfffffe7e70000007 0xdfffffcfce000000

def z978 : W := mkw 0xfdfef7ede04c2003 0x1fbfdefdbc098400 0xfffffffff00e0007 0xdffffffffe01c000

def z979 : W := mkw 0x001858a0a104a000 0x00030b1414209400 0xa038f9f1f38ff1fd 0xf4071f3e3e71fe3f

def z980 : W := mkw 0x9bb7f0000e6d6001 0x1376fe0001cdac00 0x5fffc0000ffe6007 0xabfff80001ffcc00

def z981 : W := mkw 0xf1fa7af4f1b6b4aa 0x3e3f4f5e9e36d695 0x01f8387071fe0000 0x803f070e0e3fc000

def z982 : W := mkw 0x13a228000b688000 0x02744500016d1000 0x5ff838000ffe0007 0xabff070001ffc000

def z983 : W := mkw 0x9bb7f80b0f6de251 0x5376ff0161edbc4a 0xfffffe0f8ffffe7f 0xffffffc1f1ffffcf

def z984 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xfffff9818fffe007 0xffffff3031fffc00

def z985 : W := mkw 0x24c2274440000000 0x049844e888000000 0xffc73ffe70000007 0xdff8e7ffce000000

def z986 : W := mkw 0x20c32a5445b19400 0x0418654a88b63280 0xa1c73e7e7df19e06 0xf438e7cfcfbe33c0

def z987 : W := mkw 0x0a0580020e014240 0x0140b00041c02848 0xfe07c78f8e01ffff 0x7fc0f8f1f1c03fff

def z988 : W := mkw 0x0e0485090a000900 0x01c090a121400120 0xfe07c78f8e01ffff 0x7fc0f8f1f1c03fff

def z989 : W := mkw 0x9f3cd5a9aa4e6999 0x53e79ab53549cd33 0x5e38c181820e6199 0x0bc718303041cc33

def z990 : W := mkw 0x136002400a580400 0x026c0048014b0080 0x5ff806000ffe0e07 0xabff00c001ffc1c0

def z991 : W := mkw 0xfdfef7ede0000912 0x5fbfdefdbc000122 0xfffffffff000019f 0xdffffffffe000033

def z992 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x21c73e7e7df01e62 0xc438e7cfcfbe03cc

def z993 : W := mkw 0x20c32a5655b7b6e8 0x2418654acab6f6dd 0xa1c73e7e7dff9e66 0xf438e7cfcfbff3cc

def z994 : W := mkw 0x9bb7f8020f6de251 0x5376ff0041edbc4a 0xdffff8000fffe07f 0xbbffff0001fffc0f

def z995 : W := mkw 0xdf3cd5a9aa4e298a 0x9be79ab53549c531 0x5e38c181820e6199 0x0bc718303041cc33

def z996 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff2001187 0xfffffffffe400230

def z997 : W := mkw 0x20c3225644911640 0x0418644ac89222c8 0xa1c73e7e7df19e66 0xf438e7cfcfbe33cc

def z998 : W := mkw 0xfdfef7ede0300402 0x3fbfdefdbc060080 0xfffffffff0700007 0xdffffffffe0e0000

def z999 : W := mkw 0x132000000a580d00 0x82640000014b01a0 0x5ff800000ffe0e07 0xabff000001ffc1c0

def z1000 : W := mkw 0xf9fef2ede0000002 0x1f3fde5dbc000000 0xfffff87ff0000007 0x9fffff0ffe000000

def z1001 : W := mkw 0xfde6a74d40000002 0x1fbcd4e9a8000000 0x5fc73e7e70000002 0x8bf8e7cfce000000

def z1002 : W := mkw 0x9ba7a0000e694001 0x1374f40001cd2800 0x5fff00000dfe0002 0x8bffe00001bfc000

def z1003 : W := mkw 0x644807fff0921fe2 0xac8900fffe1243fc 0x200007fff0001fe0 0x440000fffe0003fc

def z1004 : W := mkw 0x99b6f800016ca001 0x1336df00002d9400 0xdffff80003ffe007 0xbbffff00007ffc00

def z1005 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x81c73e7e7df18e06 0xb038e7cfcfbe31c0

def z1006 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff807f00dfe1f82 0xcbff00fe01bfc3f0

def z1007 : W := mkw 0x9bb6f8000b6ce001 0x1376df00016d9c00 0xdffff80003fe6007 0x9bffff00007fcc00

def z1008 : W := mkw 0xfdf6f74de0000002 0x1fbedee9bc000000 0xffc7fe7ff0000006 0xdff8ffcffe000000

def z1009 : W := mkw 0x9bb7f800af6de009 0x1376ff0015edbc01 0xdffff8018fffe01f 0xbbffff0031fffc03

def z1010 : W := mkw 0xfdfef7ede0100d02 0x9fbfdefdbc0201a0 0xfffffffff0000e07 0xdffffffffe0001c0

def z1011 : W := mkw 0x020108121fb19f60 0x2040210243f633ec 0x000000000ff19fe0 0x2000000001fe33fc

def z1012 : W := mkw 0x75ea27ede0000002 0x0ebd44fdbc000000 0xffff3ffff0000007 0xdfffe7fffe000000

def z1013 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffe7ff0000002 0x9fffffcffe000000

def z1014 : W := mkw 0xffe7a74f4e594f52 0xdffcf4e9e9cb29ea 0x5fc7060e0c700e02 0x0bf8e0c1c18e01c0

def z1015 : W := mkw 0x444807f010921da0 0x888900fe021243b4 0x200007f070001fe0 0x440000fe0e0003fc

def z1016 : W := mkw 0x9bb7f8000f6de911 0x5376ff0001edbd22 0xdffff8000fffe19f 0xbbffff0001fffc33

def z1017 : W := mkw 0x244807fff0921ff8 0x648900fffe1243ff 0x200007fff0001ff8 0x440000fffe0003ff

def z1018 : W := mkw 0xbbb7f80fff6de263 0x3776ff01ffedbc4c 0xfffff80fffffe067 0xbfffff01fffffc0c

def z1019 : W := mkw 0xfdfef7ede0000902 0x1fbfdefdbc000120 0xfffffffff0001f87 0xdffffffffe0003f0

def z1020 : W := mkw 0x6ccea7ede0000002 0x0d99d4fdbc000000 0xffc7fffff0000007 0xdff8fffffe000000

def z1021 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73ffffdf19ffe 0xf438e7ffffbe33ff

def z1022 : W := mkw 0x000808b0118290a0 0x0001011602305214 0xa038f9f1f38ff1fd 0xf4071f3e3e71fe3f

def z1023 : W := mkw 0xdf3cd5a9aa4e6983 0x9be79ab53549cd30 0x5e38c181820e6181 0x0bc718303041cc30

def z1024 : W := mkw 0x31e2224440000000 0x063c444888000000 0xffff3e7e70000007 0xdfffe7cfce000000

def z1025 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff200619f 0xdffffffffe400c33

def z1026 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0x5fff38000ffe0007 0xabffe70001ffc000

def z1027 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff806700ffe0e07 0xabff00ce01ffc1c0

def z1028 : W := mkw 0xfdfef7ede0042002 0x1fbfdefdbc008400 0xfffffffff20e6007 0xdffffffffe41cc00

def z1029 : W := mkw 0x9bb6f8000b6ce001 0x1376df00016d9c00 0x5ff8f8000ffe6007 0xabff1f0001ffcc00

def z1030 : W := mkw 0x020108121fb1d660 0x2040210243f63acc 0x000000000ff1fe60 0x2000000001fe3fcc

def z1031 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c7fe7ffdf1fe7e 0xf438ffcfffbe3fcf

def z1032 : W := mkw 0xbbb7f80d4f6de003 0x1776ff01a9edbc00 0xdffff80e0fffe007 0xbbffff01c1fffc00

def z1033 : W := mkw 0x132100000e694001 0x0264200001cd2800 0x5ff800000ffe0007 0xabff000001ffc000

def z1034 : W := mkw 0x444807f000921480 0x888900fe00124290 0x000007f000000000 0x400000fe00000000

def z1035 : W := mkw 0x020108121feffbf9 0x4040210243fdff7f 0x000000000ffffff8 0x2000000001ffffff

def z1036 : W := mkw 0x9ba7a0000e694001 0x1374f40001cd2800 0xdfffc0000fffe007 0xbbfff80001fffc00

def z1037 : W := mkw 0x776807f4eada1d82 0x8eed00fe9d5b43b0 0x5ff807f07ffe1f87 0xebff00fe0fffc3f0

def z1038 : W := mkw 0x1b35d8000f4de000 0x0366bb0001e9bc00 0xdffff8000fffe007 0xbbffff0001fffc00

def z1039 : W := mkw 0x536802f00ada1d80 0x8a6d005e015b43b0 0x5ff800700ffe1f87 0xabff000e01ffc3f0

def z1040 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0xa1c73e7e7ff1fffe 0xf438e7cfcffe3fff

def z1041 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff8000dfe0007 0x9bffff0001bfc000

def z1042 : W := mkw 0xfdfef7ede004200a 0x1fbfdefdbc008401 0xfffffffff000601f 0xdffffffffe000c03

def z1043 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xfffff8018fffe07f 0xbfffff0031fffc0f

def z1044 : W := mkw 0x132100000e490000 0x0264200001c92000 0xdfff00000fff8007 0xbbffe00001fff000

def z1045 : W := mkw 0x172005100ada1d80 0x82e400a2015b43b0 0x5ff807800ffe1f87 0xebff00f001ffc3f0

def z1046 : W := mkw 0x020108121fdffff8 0xc040210243fbffff 0x000000000ffffff8 0x2000000001ffffff

def z1047 : W := mkw 0x001858b0b196b4a8 0x00030b161632d695 0xa038f9f1fffffffd 0xf4071f3e3fffffff

def z1048 : W := mkw 0x93a220000a680001 0x12744400014d0000 0x5ff800000ffe0007 0xabff000001ffc000

def z1049 : W := mkw 0x20c3224644310640 0x24186448c88620c8 0x01c73e7e7c700e02 0x8038e7cfcf8e01c0

def z1050 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0x5ff8f8000fffe001 0xabff1f0001fffc00

def z1051 : W := mkw 0xbbb7f804ef6de003 0x1776ff009dedbc00 0xdffff8007fffe007 0xbbffff000ffffc00

def z1052 : W := mkw 0x136002500ada1d80 0x826c004a015b43b0 0x5ff806700ffe1f87 0xebff00ce01ffc3f0

def z1053 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdfff38000dff8006 0xbbffe70001bff000

def z1054 : W := mkw 0x20c32a5655b19660 0x2418654acab632cc 0x01c73e7e7df01e06 0xe038e7cfcfbe03c0

def z1055 : W := mkw 0x9bb7f8020f6de241 0x1376ff0041edbc48 0xfffff80e0fffe067 0xbfffff01c1fffc0c

def z1056 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0xffff07fe0ffe1f87 0xffffe0ffc1ffc3f0

def z1057 : W := mkw 0x001858b0b1b6b4a8 0x20030b161636d695 0xa038f9f1f3fff1fd 0xf4071f3e3e7ffe3f

def z1058 : W := mkw 0x20c32a4645318640 0x24186548c8a630c8 0xa1c73e7e7df18e06 0xf438e7cfcfbe31c0

def z1059 : W := mkw 0xb9fef2e4e0000000 0x173fde5c9c000000 0xfffffffff0000007 0xdffffffffe000000

def z1060 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0xfff807f00fff9fe7 0xffff00fe01fff3fc

def z1061 : W := mkw 0xfdfef7ede0100402 0x1fbfdefdbc020080 0xfffffffffc700e07 0xdfffffffff8e01c0

def z1062 : W := mkw 0xbbb7f80dff6de02b 0x1776ff01bfedbc05 0xfffff80fffffe07f 0xbfffff01fffffc0f

def z1063 : W := mkw 0x020108121f81db70 0x4040210243f03b6e 0x000000000f81fff8 0x2000000001f03fff

def z1064 : W := mkw 0xb1fa7af4f1feb4a9 0x363f4f5e9e3fd695 0x01f8387071fe0000 0x803f070e0e3fc000

def z1065 : W := mkw 0x9b34d0000a4c6001 0x13669a0001498c00 0x5ff8c00003fe6001 0x8bff1800007fcc00

def z1066 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0x7fff3ffff0000002 0xcfffe7fffe000000

def z1067 : W := mkw 0x020108121ff99660 0x2040210243ff32cc 0x000000000fff9e60 0x2000000001fff3cc

def z1068 : W := mkw 0x136802f00ada1480 0x026d005e015b4290 0x5ff807f00ffe1f87 0xebff00fe01ffc3f0

def z1069 : W := mkw 0xb9e6a24440000000 0x173cd44888000000 0xffc73e7e70000006 0xdff8e7cfce000000

def z1070 : W := mkw 0x001858b0b186b0a8 0x00030b161630d615 0x0038f9f1f38ff1f9 0xa0071f3e3e71fe3f

def z1071 : W := mkw 0xdf3cd5a9aa4a4992 0xdbe79ab535494932 0x5e38c181820e6199 0x0bc718303041cc33

def z1072 : W := mkw 0x0e05850b0e694b51 0x41c0b0a161cd296a 0xfe07c78f8e71ffff 0x7fc0f8f1f1ce3fff

def z1073 : W := mkw 0x20c32a5655b7b6e8 0x2418654acab6f6dd 0xa1c7ffffffffffff 0xf438ffffffffffff

def z1074 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xdffff9818fffe19f 0xbbffff3031fffc33

def z1075 : W := mkw 0xfdfef7ede0046003 0x1fbfdefdbc008c00 0xfffffffff0006007 0xdffffffffe000c00

def z1076 : W := mkw 0x132800b00ada1d80 0x82650016015b43b0 0x5ff801f00ffe1f87 0xebff003e01ffc3f0

def z1077 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffff9fff0000001 0x9fffff3ffe000000

def z1078 : W := mkw 0x8897f8020525e241 0x1112ff0040a4bc48 0xa007f80e0001e060 0x1400ff01c0003c0c

def z1079 : W := mkw 0x644807f450921da0 0xac8900fe8a1243b4 0x000007f070001f80 0x400000fe0e0003f0

def z1080 : W := mkw 0x8897f8021525e261 0x3112ff0042a4bc4c 0x8007f8000001e060 0x1000ff0000003c0c

def z1081 : W := mkw 0x9ba7a8000f69c001 0x1374f50001ed3800 0xdfff38000fff8007 0xbbffe70001fff000

def z1082 : W := mkw 0x20c32a4655318660 0x24186548caa630cc 0xa1c73e7e7c718e66 0xd438e7cfcf8e31cc

def z1083 : W := mkw 0xfdfef7ede006208a 0x1fbfdefdbc00c411 0xfffffffff20ff1ff 0xfffffffffe41fe3f

def z1084 : W := mkw 0x132000000a4c6001 0x0264000001498c00 0x5ff800000ffe6007 0xabff000001ffcc00

def z1085 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0x5ffffffff0000003 0x8bfffffffe000000

def z1086 : W := mkw 0xbbb7f80fef6de253 0x5776ff01fdedbc4a 0xfffff80fffffe07f 0xbfffff01fffffc0f

def z1087 : W := mkw 0x9bb7f800bf6de029 0x1376ff0017edbc05 0xfffff981fffff1ff 0xffffff303ffffe3f

def z1088 : W := mkw 0x172005000a480900 0x02e400a001490120 0x5ff806000ffe0e07 0xabff00c001ffc1c0

def z1089 : W := mkw 0xa897f80ff525a26a 0x3512ff01fea4b44d 0xa007f80ff001e078 0x1400ff01fe003c0f

def z1090 : W := mkw 0xbbb7f8045f6de021 0x3776ff008bedbc04 0xdffff8007fffe007 0xbbffff000ffffc00

def z1091 : W := mkw 0x64cb2ff655b39fe0 0xac9965fecab673fc 0xa0073ffe70019fe0 0x5400e7ffce0033fc

def z1092 : W := mkw 0x576007400a580d00 0x8aec00e8014b01a0 0x5ff807800ffe1f87 0xebff00f001ffc3f0

def z1093 : W := mkw 0x9bb7f8020f6deb51 0x5376ff0041edbd6a 0xfffffe0e0fffffff 0xffffffc1c1ffffff

def z1094 : W := mkw 0x1b2480000a484000 0x0364900001490800 0x5ff8c0000ffe6007 0xabff180001ffcc00

def z1095 : W := mkw 0x576807f9aada1d82 0x8aed00ff355b43b0 0x5ff807f18ffe1f87 0xebff00fe31ffc3f0

def z1096 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0x5ffff8000ffe6003 0x8bffff0001ffcc00

def z1097 : W := mkw 0xdf3cd5a9aa480902 0x9be79ab535490120 0x5e38c18180000001 0x0bc7183030000000

def z1098 : W := mkw 0x444807f9a0921d82 0x888900ff341243b0 0x000007f180001f80 0x400000fe300003f0

def z1099 : W := mkw 0x133158000f6de001 0x02662b0001edbc00 0xdff8f8000fffe007 0xbbff1f0001fffc00

def z1100 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0x5ff8c7f18ffe7f9f 0xebff18fe31ffcff3

def z1101 : W := mkw 0x20c3225644b11640 0x2418644ac89622c8 0xa1c73e7e7df01e06 0xf438e7cfcfbe03c0

def z1102 : W := mkw 0x9b34d0000a480000 0x13669a0001490000 0x5ff8c0000ffe0007 0xabff180001ffc000

def z1103 : W := mkw 0xfdfef7ede0000002 0x1fbfdefdbc000000 0xfffffffff0019067 0xfffffffffe00320c

def z1104 : W := mkw 0x0c048d191186b0a8 0x018091a32230d615 0xfe07c78f838ff1ff 0x7fc0f8f1f071fe3f

def z1105 : W := mkw 0x576807f01ada1da0 0x8aed00fe035b43b4 0x7ff807f07ffe1fe7 0xefff00fe0fffc3fc

def z1106 : W := mkw 0x576807f00ada1d80 0x8aed00fe015b43b0 0xfff83ff07ffe1f87 0xffff07fe0fffc3f0

def z1107 : W := mkw 0x132100020e494b50 0x4264200041c9296a 0x5ff800000fffffff 0xabff000001ffffff

def z1108 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0x5fff38000fffe002 0xabffe70001fffc00

def z1109 : W := mkw 0x776807fd4ada1d82 0x8eed00ffa95b43b0 0x5ff807fe0ffe1f87 0xebff00ffc1ffc3f0

def z1110 : W := mkw 0x644807fd40921d82 0x8c8900ffa81243b0 0x000007fe00001f80 0x400000ffc00003f0

def z1111 : W := mkw 0x644807ff50921ff0 0xec8900ffea1243fe 0x200007fff0001ff8 0x440000fffe0003ff

def z1112 : W := mkw 0x9bb7f0000e494000 0x1376fe0001c92800 0xdffff8000fffe007 0xbbffff0001fffc00

def z1113 : W := mkw 0x5d7cd7e9a0000000 0x0baf9afd34000000 0xfffffffff0000007 0xdffffffffe000000

def z1114 : W := mkw 0x060105020e010b40 0x00c020a041c02168 0xfe07c78f8e01ffff 0x7fc0f8f1f1c03fff

def z1115 : W := mkw 0xa897f80ff525e263 0x3512ff01fea4bc4c 0xa007f80ff001e060 0x1400ff01fe003c0c

def z1116 : W := mkw 0x132108000f698000 0x0264210001ed3000 0x5ff800000fff8007 0xabff000001fff000

def z1117 : W := mkw 0x9bb7f8020f6de241 0x1376ff0041edbc48 0xdffff8000ffffe67 0xbbffff0001ffffcc

def z1118 : W := mkw 0x9bb7f8000f6de001 0x1376ff0001edbc00 0xfffff8000ffff067 0xffffff0001fffe0c

def z1119 : W := mkw 0x776807fdfada1daa 0x8eed00ffbf5b43b5 0x7ff807fffffe1fff 0xefff00ffffffc3ff

def z1120 : W := mkw 0x133050000a4c2000 0x02660a0001498400 0x5ff8c0000ffe6007 0xabff180001ffcc00

def z1121 : W := mkw 0x9ba6a0000a480000 0x1374d40001490000 0x5fff00000ffe0007 0xabffe00001ffc000

def z1122 : W := mkw 0x576807f90ada1d90 0xcaed00ff215b43b2 0x5ff807f18ffe1f9f 0xebff00fe31ffc3f3

def z1123 : W := mkw 0x93b270000a480000 0x12764e0001490000 0x5ff838000ffe0007 0xabff070001ffc000

def z1124 : W := mkw 0x444807f900921d90 0xc88900ff201243b2 0x000007f180001f98 0x400000fe300003f3

def z1125 : W := mkw 0xdf3cd5a9aa4c6913 0x5be79ab535498d22 0x5e38c181820e6199 0x0bc718303041cc33

def z1126 : W := mkw 0xb9bef0ade0000002 0x1737de15bc000000 0xfffff9fff0000007 0xdfffff3ffe000000

def z1127 : W := mkw 0xbbb7f80f5f6de271 0x7776ff01ebedbc4e 0xfffff80fffffe07f 0xbfffff01fffffc0f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z7,z2,z8,z4,z9]),(0,[z0,z10,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z11,z5]),(0,[z0,z1,z7,z2,z12,z4,z5]),(0,[z0,z7,z2,z13,z8,z9,z5]),(0,[z0,z14,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z15,z4,z5])],[(0,[z16,z0,z7,z2,z8,z4,z5]),(0,[z0,z17,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z18,z19,z5]),(0,[z0,z20,z6,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z21,z5]),(0,[z22,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z8,z5])],[(0,[z0,z7,z24,z2,z8,z25,z5])],[(0,[z0,z7,z2,z8,z26,z4,z5]),(1,[z0,z7,z2,z27,z8,z5]),(0,[z0,z7,z2,z8,z4,z28,z5]),(0,[z29,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z30,z5]),(0,[z0,z7,z2,z8,z4,z31,z5])],[(0,[z0,z1,z7,z2,z3,z4,z5]),(0,[z0,z7,z2,z8,z4,z9,z5]),(0,[z32,z0,z7,z2,z8,z4,z5]),(0,[z0,z33,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z34,z8,z4,z5]),(0,[z0,z35,z7,z2,z8,z4,z5]),(0,[z0,z6,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z36,z5]),(0,[z0,z7,z2,z8,z37,z4,z5]),(0,[z0,z7,z2,z13,z8,z38,z5]),(0,[z39,z0,z7,z2,z8,z4,z5])]],
   [[(0,[z0,z7,z40,z2,z8,z4,z5]),(0,[z0,z7,z2,z41,z8,z4,z5]),(0,[z0,z7,z24,z2,z8,z42,z5]),(0,[z0,z7,z43,z23,z2,z8,z5])],[(1,[z0,z7,z44,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z45,z5]),(0,[z0,z14,z7,z2,z8,z36,z4]),(0,[z0,z7,z46,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z47,z4,z5])],[(0,[z0,z7,z2,z8,z4,z48,z5]),(0,[z49,z0,z7,z2,z8,z4,z50]),(0,[z0,z51,z7,z23,z2,z8,z5])],[],[(0,[z0,z7,z2,z8,z52,z4,z5]),(0,[z53,z0,z7,z2,z8,z54,z5]),(0,[z0,z7,z2,z8,z55,z4,z5]),(0,[z0,z56,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z57,z4,z58,z5]),(0,[z0,z7,z23,z59,z2,z8,z5]),(0,[z0,z7,z2,z60,z8,z4,z5])],[(0,[z0,z7,z23,z61,z2,z8,z5]),(1,[z0,z7,z23,z2,z5,z62])],[(0,[z0,z7,z63,z2,z8,z4,z5]),(0,[z64,z0,z7,z23,z2,z8,z5]),(0,[z65,z0,z7,z2,z8,z4,z5]),(0,[z0,z66,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z67,z5]),(0,[z68,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z8,z4,z69,z5,z62])],[(0,[z0,z7,z2,z8,z4,z70,z5]),(0,[z0,z7,z71,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z4,z72,z5]),(0,[z0,z7,z2,z73,z8,z4,z5]),(0,[z0,z7,z2,z8,z19,z4,z5]),(1,[z0,z7,z2,z8,z74,z5]),(0,[z0,z7,z2,z8,z47,z5,z75])]],
   [[(0,[z0,z7,z2,z76,z8,z4,z5]),(0,[z0,z7,z2,z8,z77,z78,z5]),(0,[z0,z79,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z76,z13,z8,z5]),(0,[z7,z2,z80,z8,z81,z4,z5]),(0,[z0,z82,z7,z2,z12,z4,z5]),(0,[z0,z83,z7,z2,z8,z4,z5]),(0,[z0,z79,z7,z2,z13,z8,z5])],[(0,[z0,z7,z2,z8,z84,z4,z5]),(1,[z0,z7,z2,z85,z4,z5]),(0,[z86,z0,z7,z23,z2,z8,z5])],[(0,[z87,z0,z7,z2,z8,z4,z88]),(0,[z89,z0,z7,z2,z8,z4,z5]),(0,[z90,z0,z7,z2,z8,z4,z5]),(0,[z0,z91,z7,z2,z8,z4,z5])],[(0,[z0,z92,z7,z2,z8,z4,z5]),(0,[z0,z7,z93,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z94]),(0,[z0,z7,z59,z2,z95,z8,z4]),(0,[z0,z7,z2,z8,z4,z96,z5]),(0,[z0,z91,z7,z2,z13,z8,z5])],[(0,[z0,z7,z2,z8,z4,z97,z5]),(0,[z0,z7,z23,z2,z8,z12,z5]),(0,[z0,z7,z98,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z4,z5,z62]),(0,[z0,z7,z99,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z5,z100])],[(0,[z0,z7,z2,z8,z4,z101,z5]),(0,[z0,z7,z102,z2,z8,z4,z5]),(0,[z0,z7,z2,z103,z8,z4,z5])],[(0,[z0,z7,z2,z104,z8,z4,z5]),(0,[z0,z7,z2,z103,z13,z8,z5]),(0,[z0,z7,z2,z8,z105,z4,z5])]],
   [[(0,[z0,z7,z2,z81,z106,z4,z5]),(0,[z107,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z108,z4,z5]),(1,[z0,z7,z2,z8,z109,z5])],[(1,[z0,z7,z2,z8,z4,z88]),(0,[z0,z7,z110,z2,z8,z4,z5]),(0,[z0,z7,z111,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z112,z5]),(0,[z0,z7,z2,z113,z13,z8,z5]),(0,[z0,z7,z114,z2,z8,z4,z5]),(0,[z115,z0,z7,z2,z8,z4,z5])],[(1,[z0,z7,z2,z8,z116,z5]),(0,[z0,z7,z2,z8,z4,z5,z100]),(0,[z0,z7,z2,z8,z4,z5,z117])],[(0,[z0,z7,z2,z8,z118,z58,z5]),(0,[z119,z7,z2,z8,z4,z5,z94]),(0,[z0,z7,z2,z8,z4,z5,z120]),(0,[z0,z7,z2,z8,z4,z5,z121]),(0,[z0,z7,z2,z8,z4,z122,z5]),(0,[z123,z0,z7,z2,z13,z8,z5])],[(0,[z0,z7,z2,z8,z4,z94,z124]),(0,[z0,z125,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z24,z2,z8,z5]),(0,[z0,z7,z2,z8,z126,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z127]),(0,[z0,z7,z2,z13,z8,z8,z5])],[(0,[z128,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z129,z5]),(0,[z0,z7,z2,z8,z4,z130,z5]),(0,[z0,z7,z2,z8,z12,z4,z5]),(0,[z0,z7,z131,z2,z13,z8,z5]),(0,[z0,z79,z7,z59,z2,z8,z4]),(1,[z0,z7,z2,z13,z106,z5]),(0,[z0,z7,z2,z8,z4,z132,z5])],[(0,[z133,z0,z7,z2,z81,z4,z5]),(0,[z0,z7,z2,z134,z8,z4,z5]),(1,[z0,z7,z2,z8,z135,z4]),(0,[z0,z7,z61,z2,z8,z4,z5])],[(0,[z0,z7,z2,z136,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z9,z137]),(0,[z0,z7,z2,z138,z8,z4,z5]),(0,[z0,z7,z139,z2,z8,z4,z5]),(0,[z0,z7,z140,z2,z8,z4,z5])]],
   [[(0,[z0,z7,z2,z8,z141,z4,z5]),(0,[z0,z1,z7,z23,z2,z4,z5]),(1,[z0,z7,z2,z8,z142,z5]),(0,[z0,z7,z2,z13,z8,z36,z5]),(0,[z0,z143,z7,z2,z8,z19,z5]),(1,[z0,z144,z7,z2,z8,z4])],[(0,[z145,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z3,z81,z4,z5]),(1,[z53,z7,z2,z8,z54,z5]),(0,[z146,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z27,z8,z12,z5]),(0,[z147,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z23,z2,z148,z8,z5]),(0,[z0,z7,z23,z2,z13,z4,z5]),(0,[z0,z7,z2,z8,z149,z4,z5])],[(0,[z0,z7,z2,z8,z4,z5,z150]),(0,[z0,z7,z2,z8,z4,z151,z5]),(0,[z0,z7,z2,z152,z8,z4,z5])],[(0,[z87,z0,z7,z2,z8,z153,z5]),(0,[z0,z7,z2,z8,z4,z5,z154]),(1,[z0,z155,z2,z8,z58,z5]),(0,[z156,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z95,z8,z4,z62])],[(0,[z0,z7,z2,z157,z8,z4,z5]),(0,[z158,z0,z7,z2,z8,z4,z5]),(0,[z159,z0,z7,z23,z2,z8,z5]),(0,[z0,z160,z155,z2,z8,z4,z5]),(0,[z0,z161,z7,z2,z8,z4,z5]),(0,[z162,z0,z7,z2,z8,z4,z5]),(0,[z0,z163,z7,z2,z8,z4,z5])],[(0,[z164,z0,z7,z2,z8,z4,z5]),(0,[z165,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z166,z4,z5]),(0,[z0,z7,z2,z167,z8,z4,z5]),(0,[z0,z7,z59,z2,z8,z38,z4])],[(1,[z0,z168,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z38,z58,z5]),(0,[z0,z7,z59,z2,z8,z4,z50])],[(0,[z169,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z170]),(0,[z0,z82,z7,z2,z13,z8,z5])]],
   [[(0,[z87,z0,z7,z2,z141,z4,z5]),(0,[z0,z7,z2,z8,z54,z58,z5])],[(1,[z0,z7,z2,z8,z153,z5]),(0,[z0,z7,z2,z2,z8,z4,z5])],[(0,[z171,z172,z7,z2,z8,z4,z5]),(0,[z0,z173,z7,z2,z8,z4,z5]),(0,[z0,z174,z7,z2,z8,z4,z5])],[(0,[z175,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z176,z5])],[(0,[z0,z177,z7,z2,z8,z4,z5]),(0,[z0,z7,z178,z2,z8,z4,z5]),(0,[z0,z160,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z179,z8,z4,z5])],[(0,[z53,z0,z7,z2,z8,z118,z5]),(0,[z0,z7,z2,z8,z4,z180,z5])],[(0,[z0,z7,z2,z3,z80,z4,z5]),(0,[z0,z7,z2,z13,z8,z12,z5]),(0,[z0,z7,z181,z2,z8,z4,z5])],[(0,[z0,z168,z7,z182,z2,z8,z4]),(0,[z0,z7,z2,z8,z183,z4,z5]),(0,[z184,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z185,z5])]],
   [[(0,[z0,z7,z23,z2,z80,z8,z5]),(0,[z0,z82,z7,z23,z2,z4,z5]),(0,[z0,z7,z2,z8,z186,z4,z5])],[(0,[z0,z7,z2,z8,z4,z5,z187]),(0,[z0,z7,z2,z95,z8,z4,z77])],[(0,[z0,z188,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z189,z4,z5]),(0,[z0,z7,z190,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z191,z5]),(0,[z0,z7,z2,z192,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z193,z5]),(0,[z0,z7,z23,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z194,z5])],[(0,[z0,z7,z2,z8,z4,z195,z5]),(0,[z0,z7,z2,z196,z8,z4,z5]),(0,[z197,z0,z198,z2,z8,z4,z5]),(0,[z0,z199,z7,z2,z134,z4,z5])],[(0,[z0,z7,z44,z2,z8,z4,z5]),(0,[z200,z0,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z201,z4,z5]),(0,[z0,z7,z2,z8,z202,z4,z5]),(0,[z0,z160,z2,z8,z18,z4,z5]),(0,[z0,z7,z203,z2,z8,z4,z5])],[(0,[z0,z204,z7,z182,z2,z8,z4]),(0,[z0,z7,z23,z2,z76,z8,z5]),(0,[z0,z7,z2,z8,z205,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z206]),(0,[z0,z7,z2,z8,z4,z5,z207]),(0,[z49,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z208,z5])]],
   [[(0,[z209,z0,z7,z2,z8,z4,z5]),(1,[z0,z7,z210,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z5,z211]),(0,[z49,z0,z7,z8,z4,z50,z5])],[(0,[z0,z212,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z213,z4,z5]),(1,[z0,z14,z7,z2,z8,z4]),(0,[z49,z0,z7,z59,z8,z4,z5]),(0,[z0,z7,z2,z8,z74,z4,z5])],[(0,[z0,z7,z2,z8,z4,z214,z5]),(0,[z53,z0,z7,z2,z85,z4,z5]),(0,[z0,z7,z2,z215,z8,z4,z5]),(0,[z0,z7,z23,z2,z134,z8,z5]),(0,[z0,z216,z7,z2,z8,z4,z5]),(0,[z217,z0,z7,z2,z8,z4,z5])],[(0,[z87,z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z218,z4,z5]),(0,[z219,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z9,z94]),(0,[z0,z7,z220,z2,z8,z4,z5]),(0,[z0,z20,z2,z8,z4,z9,z5]),(1,[z0,z7,z221,z2,z4,z5]),(0,[z49,z0,z7,z2,z95,z8,z4])],[(0,[z0,z7,z2,z222,z8,z4,z5]),(0,[z119,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z223,z8,z4,z5]),(0,[z224,z0,z7,z2,z8,z4,z5])],[(0,[z0,z225,z7,z2,z8,z4,z5]),(1,[z0,z7,z140,z2,z4,z5]),(1,[z0,z199,z7,z36,z4,z5])],[(0,[z0,z7,z226,z2,z8,z4,z5]),(0,[z0,z227,z7,z2,z8,z4,z5]),(0,[z0,z155,z7,z2,z8,z58,z5]),(0,[z0,z7,z2,z8,z4,z5,z228])],[(0,[z0,z229,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z230,z8,z4,z5]),(0,[z0,z7,z2,z27,z8,z4,z5]),(0,[z0,z7,z2,z231,z8,z4,z5]),(0,[z0,z7,z2,z8,z74,z5,z62])]],
   [[(0,[z0,z232,z7,z2,z8,z4,z5]),(1,[z0,z7,z233,z8,z4,z5]),(0,[z0,z7,z2,z230,z13,z8,z5]),(0,[z0,z7,z2,z8,z4,z5,z234]),(1,[z0,z7,z23,z2,z13,z5])],[(0,[z165,z7,z71,z2,z8,z4,z5]),(0,[z235,z0,z7,z2,z8,z4,z5]),(0,[z0,z236,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z237,z8,z4,z5]),(0,[z0,z238,z2,z230,z8,z4,z5]),(0,[z0,z7,z23,z2,z230,z8,z5]),(1,[z0,z7,z2,z13,z8,z5])],[(0,[z239,z0,z7,z2,z8,z4,z5]),(0,[z240,z0,z7,z2,z8,z4,z5]),(1,[z133,z7,z2,z81,z4,z5]),(0,[z53,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z241,z5]),(0,[z0,z7,z242,z2,z8,z4,z5]),(0,[z0,z7,z243,z2,z8,z4,z5])],[(0,[z244,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z80,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z245,z5]),(0,[z0,z7,z2,z8,z246,z4,z5])],[(0,[z0,z247,z7,z2,z8,z4,z5]),(0,[z0,z7,z248,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z58,z5])],[(0,[z0,z7,z2,z8,z4,z249,z5]),(0,[z250,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z251,z4,z5]),(0,[z0,z252,z7,z2,z8,z4,z5]),(0,[z0,z253,z7,z2,z8,z4,z5]),(0,[z254,z0,z7,z2,z8,z4,z5]),(0,[z0,z255,z7,z2,z8,z4,z5]),(0,[z0,z143,z7,z2,z13,z8,z5]),(0,[z0,z7,z131,z8,z19,z4,z5])],[(0,[z256,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z57,z4,z5]),(0,[z49,z0,z257,z7,z2,z8,z4]),(0,[z0,z257,z7,z2,z8,z4,z62])],[(1,[z0,z7,z2,z8,z97,z5]),(0,[z0,z7,z258,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z259,z4,z5]),(0,[z0,z7,z260,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z261]),(0,[z0,z262,z7,z2,z8,z4,z5]),(0,[z0,z7,z114,z8,z4,z5,z62])]],
   [[(0,[z0,z263,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z264,z5]),(0,[z0,z7,z2,z13,z8,z265,z5])],[(1,[z0,z7,z2,z8,z4,z195]),(0,[z0,z7,z2,z13,z80,z8,z5]),(0,[z0,z7,z2,z266,z8,z4,z5]),(0,[z0,z7,z2,z8,z267,z4,z5])],[(0,[z0,z7,z2,z8,z4,z268,z5]),(1,[z0,z1,z7,z23,z2,z5]),(0,[z0,z269,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z270,z5]),(0,[z0,z271,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z38,z4,z75]),(0,[z0,z7,z2,z8,z272,z4,z5]),(0,[z0,z273,z7,z2,z8,z4,z5])],[(0,[z274,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z275,z5])],[(0,[z0,z7,z276,z2,z8,z4,z5]),(0,[z277,z7,z2,z8,z4,z118,z5]),(0,[z7,z2,z8,z4,z137,z5,z94]),(0,[z0,z7,z23,z24,z2,z4,z5]),(0,[z278,z0,z7,z2,z8,z4,z5]),(0,[z49,z0,z7,z2,z8,z38,z4]),(0,[z0,z7,z2,z13,z8,z4,z5])],[(0,[z0,z279,z7,z2,z8,z4,z5]),(0,[z0,z199,z7,z2,z106,z4,z5]),(0,[z0,z7,z2,z13,z13,z8,z5]),(0,[z0,z7,z2,z8,z4,z265,z5])],[(0,[z280,z0,z7,z2,z8,z4,z5]),(0,[z281,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z282,z4,z5]),(0,[z0,z1,z2,z3,z8,z4,z5])],[(0,[z0,z7,z2,z8,z283,z4,z5]),(0,[z0,z7,z140,z2,z4,z58,z5]),(0,[z0,z7,z2,z284,z8,z4,z5])]],
   [[(0,[z0,z7,z182,z23,z2,z8,z5]),(0,[z0,z7,z2,z285,z8,z4,z5]),(0,[z0,z7,z76,z230,z8,z4,z5]),(0,[z0,z286,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z80,z106,z4,z5]),(0,[z0,z287,z7,z2,z8,z4,z5]),(0,[z288,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z289,z5])],[(0,[z0,z7,z71,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z4,z5]),(0,[z0,z7,z23,z2,z8,z54,z5]),(1,[z0,z198,z238,z8,z4,z5]),(0,[z0,z7,z290,z2,z8,z4,z5])],[(0,[z133,z0,z7,z23,z2,z8,z5]),(0,[z0,z20,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z13,z8,z5,z62]),(0,[z0,z7,z2,z13,z8,z5,z75]),(0,[z0,z7,z291,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z292,z4,z5]),(0,[z0,z7,z23,z2,z81,z4,z5]),(0,[z0,z7,z2,z13,z134,z8,z5]),(0,[z0,z7,z2,z8,z293,z4,z5])],[(1,[z0,z7,z2,z8,z294,z5]),(1,[z0,z7,z2,z57,z4,z5]),(0,[z0,z257,z7,z2,z8,z4,z77])],[(0,[z87,z7,z182,z2,z8,z4,z5]),(0,[z0,z7,z2,z295,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z296,z5]),(1,[z0,z7,z131,z8,z19,z5]),(0,[z297,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z298,z2,z8,z4,z5])],[(0,[z0,z7,z2,z299,z8,z4,z5]),(0,[z0,z7,z2,z8,z300,z4,z5]),(0,[z0,z7,z2,z8,z4,z301,z5]),(0,[z0,z7,z2,z8,z4,z302,z5]),(0,[z0,z7,z2,z8,z303,z4,z5]),(0,[z0,z304,z7,z2,z8,z4,z5])],[(1,[z87,z182,z2,z8,z4,z5]),(0,[z0,z7,z2,z305,z8,z4,z5]),(0,[z306,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z62]),(0,[z0,z7,z2,z8,z4,z5,z75])]],
   [[(0,[z307,z0,z7,z2,z8,z4,z5]),(0,[z0,z308,z7,z2,z8,z4,z5]),(0,[z0,z309,z7,z2,z8,z4,z5]),(0,[z0,z20,z7,z2,z8,z142,z5])],[(0,[z310,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z311,z2,z8,z4,z5]),(0,[z0,z7,z312,z2,z8,z4,z5]),(0,[z0,z313,z7,z2,z8,z4,z5]),(0,[z0,z1,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z314,z4,z5]),(0,[z0,z160,z7,z2,z8,z18,z5]),(0,[z0,z7,z2,z8,z4,z315,z5]),(0,[z0,z7,z2,z8,z4,z316,z5]),(0,[z0,z7,z2,z8,z317,z4,z5]),(0,[z0,z7,z2,z13,z106,z4,z5])],[(0,[z277,z0,z7,z2,z8,z4,z5]),(0,[z0,z1,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z4,z318,z5]),(0,[z0,z7,z2,z8,z319,z4,z5])],[(0,[z277,z0,z7,z2,z13,z8,z5]),(0,[z0,z6,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z113,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z5,z320]),(0,[z321,z0,z7,z2,z8,z4,z5]),(0,[z197,z0,z7,z238,z8,z4,z5]),(0,[z0,z7,z2,z8,z322,z4,z5])],[(0,[z0,z7,z2,z8,z47,z58,z5]),(0,[z0,z323,z7,z2,z8,z4,z5]),(0,[z0,z324,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z325]),(0,[z0,z7,z2,z8,z4,z5,z326]),(0,[z123,z0,z7,z2,z8,z4,z5])],[(0,[z0,z7,z238,z71,z8,z4,z5]),(0,[z327,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z24,z134,z8,z4,z5]),(0,[z0,z328,z7,z2,z8,z4,z5]),(0,[z0,z329,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z330,z8,z4,z5])],[(0,[z0,z7,z2,z8,z331,z4,z5]),(0,[z0,z7,z131,z2,z8,z4,z5]),(1,[z0,z143,z7,z8,z332,z5]),(0,[z333,z0,z7,z2,z13,z8,z5])]],
   [[(0,[z0,z7,z23,z2,z80,z4,z5]),(0,[z0,z334,z7,z2,z8,z4,z5]),(0,[z335,z0,z7,z2,z8,z4,z5]),(0,[z335,z0,z7,z233,z8,z4,z5]),(0,[z335,z0,z20,z7,z2,z8,z4]),(0,[z0,z1,z7,z2,z8,z336,z5]),(0,[z0,z7,z2,z8,z4,z5,z337]),(0,[z0,z7,z338,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z50,z5]),(0,[z0,z7,z2,z8,z339,z4,z5])],[(0,[z0,z7,z2,z340,z8,z4,z5]),(0,[z0,z7,z341,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z342,z4,z5]),(0,[z335,z0,z7,z2,z13,z8,z5]),(0,[z197,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z138,z230,z8,z4]),(0,[z0,z7,z2,z343,z8,z4,z5]),(0,[z344,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z345,z4,z5])],[(0,[z171,z0,z7,z23,z2,z8,z5]),(0,[z197,z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z346,z4,z5]),(0,[z0,z7,z2,z4,z316,z332,z5]),(0,[z347,z0,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z348,z5]),(0,[z0,z7,z2,z349,z8,z4,z5]),(0,[z0,z198,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z19,z58,z5]),(1,[z0,z7,z24,z134,z4,z5]),(1,[z0,z257,z7,z23,z2,z5]),(0,[z0,z7,z2,z350,z8,z4,z5])],[(0,[z0,z7,z23,z351,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z69,z5]),(0,[z0,z352,z7,z2,z8,z4,z5])],[(0,[z172,z7,z182,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z294,z5]),(0,[z0,z7,z2,z8,z4,z353,z5]),(1,[z0,z7,z23,z2,z80,z5]),(0,[z335,z0,z6,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z4,z5,z354]),(0,[z0,z7,z2,z8,z18,z332,z5]),(0,[z0,z257,z7,z23,z2,z8,z5]),(0,[z0,z257,z7,z2,z95,z4,z5])],[(0,[z0,z355,z7,z2,z8,z4,z5]),(0,[z0,z7,z356,z2,z8,z4,z5]),(0,[z0,z1,z7,z2,z106,z4,z5]),(0,[z0,z199,z7,z2,z36,z4,z5])],[(0,[z357,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z71,z230,z8,z4,z5]),(0,[z0,z7,z2,z8,z358,z4,z5]),(0,[z359,z0,z7,z2,z8,z4,z5]),(1,[z0,z7,z2,z4,z316,z5])]],
   [[(0,[z0,z7,z2,z360,z8,z4,z5]),(0,[z0,z7,z361,z2,z8,z4,z5]),(1,[z49,z0,z7,z8,z4,z50]),(0,[z357,z0,z7,z2,z13,z8,z5])],[(0,[z0,z7,z362,z2,z8,z4,z5]),(0,[z0,z7,z2,z363,z8,z4,z5]),(0,[z0,z82,z7,z2,z8,z4,z5]),(0,[z0,z364,z7,z2,z8,z4,z5]),(0,[z365,z0,z7,z2,z8,z4,z5]),(0,[z366,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z77,z5])],[(0,[z367,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z54,z5]),(0,[z0,z7,z2,z8,z4,z368,z5]),(0,[z0,z7,z2,z8,z18,z4,z5]),(0,[z0,z7,z2,z8,z369,z4,z5]),(0,[z370,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z24,z2,z13,z8,z5]),(0,[z0,z7,z371,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z372,z4,z5])],[(0,[z0,z155,z7,z2,z8,z18,z5])],[(0,[z0,z7,z2,z8,z373,z4,z5]),(1,[z159,z7,z2,z80,z4,z5]),(0,[z0,z7,z2,z8,z374,z4,z5]),(0,[z0,z7,z2,z8,z4,z375,z5]),(0,[z0,z7,z2,z8,z4,z376,z5])],[(0,[z87,z0,z182,z2,z8,z4,z5]),(1,[z335,z7,z2,z8,z4,z137]),(0,[z0,z7,z377,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z336,z4,z5]),(0,[z0,z7,z23,z2,z3,z8,z5]),(0,[z0,z378,z7,z2,z13,z8,z5]),(0,[z379,z0,z7,z2,z8,z4,z5])],[(0,[z380,z0,z7,z2,z8,z4,z5]),(0,[z64,z165,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z381]),(0,[z0,z7,z23,z238,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z382,z5]),(0,[z0,z7,z2,z8,z383,z4,z5]),(0,[z0,z7,z59,z134,z8,z4,z5]),(1,[z0,z7,z59,z8,z4,z187])],[(0,[z0,z7,z23,z2,z8,z81,z5]),(0,[z384,z0,z7,z2,z8,z4,z5]),(0,[z0,z199,z7,z8,z36,z4,z5])]],
   [[(0,[z7,z2,z8,z54,z4,z118,z5]),(0,[z0,z7,z2,z8,z385,z4,z5]),(0,[z0,z386,z7,z2,z8,z4,z5])],[(1,[z0,z7,z2,z141,z4,z5]),(0,[z0,z7,z44,z2,z8,z81,z5]),(0,[z0,z7,z23,z2,z8,z332,z5]),(0,[z0,z7,z2,z8,z387,z4,z5])],[(0,[z0,z7,z23,z2,z8,z118,z5]),(0,[z0,z1,z7,z2,z8,z368,z5]),(0,[z0,z7,z2,z4,z77,z5,z62])],[(0,[z0,z7,z2,z8,z25,z4,z5]),(0,[z0,z388,z7,z2,z8,z4,z5]),(0,[z389,z0,z7,z2,z8,z4,z5]),(1,[z0,z7,z2,z8,z38,z75])],[(0,[z0,z7,z390,z2,z8,z4,z5]),(1,[z0,z7,z2,z8,z4,z391]),(0,[z0,z7,z392,z2,z8,z4,z5]),(0,[z0,z7,z393,z2,z8,z4,z5]),(0,[z0,z144,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z394,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z5,z88]),(0,[z0,z395,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z396,z4,z5]),(0,[z0,z7,z2,z8,z8,z4,z5]),(0,[z0,z7,z2,z8,z135,z36,z4])],[(0,[z0,z397,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z398]),(0,[z0,z7,z2,z8,z4,z399,z5]),(0,[z0,z82,z7,z2,z106,z4,z5]),(0,[z0,z7,z400,z2,z8,z4,z5])],[(0,[z133,z159,z7,z2,z8,z4,z5]),(0,[z197,z0,z7,z230,z8,z4,z5])]],
   [[(0,[z64,z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z401,z8,z4,z5]),(0,[z0,z402,z7,z2,z8,z4,z5]),(0,[z0,z403,z7,z2,z8,z4,z5]),(0,[z0,z404,z7,z2,z8,z4,z5]),(0,[z0,z405,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z406,z5]),(0,[z335,z0,z7,z2,z8,z4,z137]),(0,[z0,z405,z7,z2,z13,z8,z5])],[(0,[z407,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z408,z4,z5]),(0,[z409,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z410,z5]),(0,[z0,z7,z2,z8,z411,z4,z5]),(0,[z0,z7,z59,z2,z13,z8,z5])],[(0,[z86,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z412,z8,z4,z5]),(0,[z0,z2,z8,z4,z9,z5,z124])],[(0,[z0,z82,z1,z2,z8,z4,z5]),(0,[z0,z7,z413,z23,z2,z8,z5]),(0,[z0,z7,z23,z2,z8,z47,z5])],[(0,[z87,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z414]),(1,[z0,z7,z114,z8,z4,z5]),(0,[z0,z415,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z5,z416])],[(0,[z165,z0,z7,z2,z8,z4,z391]),(0,[z0,z7,z2,z8,z109,z36,z5]),(0,[z0,z7,z2,z417,z8,z4,z5])]],
   [[(0,[z0,z227,z7,z2,z230,z8,z4]),(0,[z418,z0,z7,z2,z8,z4,z5])],[(0,[z0,z419,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z420,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z421]),(0,[z0,z155,z7,z23,z2,z8,z5]),(0,[z0,z7,z59,z8,z4,z5,z187]),(0,[z0,z7,z2,z8,z4,z422,z5])],[(1,[z0,z199,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z423,z4,z5]),(0,[z0,z7,z2,z8,z106,z4,z5]),(0,[z0,z7,z2,z13,z8,z77,z5]),(0,[z0,z7,z2,z8,z4,z424,z5])],[(1,[z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z425,z8,z4,z5]),(0,[z0,z426,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z427,z5]),(0,[z428,z0,z7,z2,z8,z4,z5])],[(0,[z87,z0,z172,z2,z8,z4,z5]),(0,[z429,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z430,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z431,z5])],[(0,[z0,z432,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z433,z5]),(0,[z0,z7,z2,z8,z4,z5,z434]),(0,[z0,z7,z2,z8,z435,z4,z5]),(0,[z0,z7,z2,z8,z436,z4,z5])],[(1,[z0,z7,z23,z2,z81,z5]),(0,[z53,z277,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z3,z8,z5]),(0,[z0,z7,z2,z8,z4,z437,z5]),(0,[z0,z7,z2,z438,z8,z4,z5]),(0,[z439,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z190,z23,z2,z8,z5])],[(0,[z0,z7,z2,z8,z440,z4,z5]),(0,[z0,z7,z2,z441,z8,z4,z5]),(0,[z0,z143,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z442,z5]),(0,[z0,z7,z23,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z77,z5]),(0,[z0,z443,z7,z2,z8,z4,z5]),(0,[z0,z7,z290,z2,z8,z77,z5])]],
   [[(0,[z0,z7,z2,z13,z8,z81,z5]),(1,[z0,z7,z2,z408,z4,z5]),(0,[z0,z7,z2,z8,z18,z54,z5]),(0,[z0,z7,z2,z8,z444,z4,z5]),(0,[z0,z7,z2,z106,z4,z96,z5]),(0,[z0,z445,z7,z2,z8,z4,z5]),(0,[z0,z79,z7,z2,z8,z4,z75])],[(1,[z0,z7,z2,z446,z8,z5]),(0,[z447,z0,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z448,z5]),(1,[z0,z7,z2,z8,z336,z5]),(0,[z0,z7,z2,z8,z4,z449,z5]),(0,[z0,z7,z2,z8,z47,z18,z5]),(0,[z0,z7,z450,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z332,z5])],[(0,[z0,z7,z2,z13,z8,z118,z5]),(0,[z451,z0,z7,z2,z8,z4,z5]),(1,[z0,z7,z452,z2,z8,z5])],[(1,[z197,z0,z230,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z453,z5])],[(0,[z159,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z95,z4,z5,z62]),(0,[z0,z79,z7,z2,z8,z47,z4])],[(0,[z165,z0,z7,z2,z8,z4,z5]),(0,[z159,z0,z7,z2,z13,z8,z5])],[(0,[z0,z7,z454,z2,z8,z4,z5]),(0,[z0,z7,z76,z8,z4,z50,z5]),(0,[z165,z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z4,z332,z5])]],
   [[(0,[z0,z7,z2,z8,z455,z4,z5]),(0,[z0,z7,z2,z8,z4,z118,z5]),(0,[z0,z456,z7,z2,z8,z4,z5]),(0,[z457,z0,z7,z2,z8,z4,z5]),(0,[z458,z0,z7,z2,z8,z4,z5]),(0,[z459,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z460,z8,z4,z5])],[],[(0,[z0,z7,z2,z8,z461,z4,z5]),(1,[z0,z204,z7,z2,z8,z4]),(0,[z0,z7,z23,z71,z2,z8,z5]),(0,[z0,z7,z59,z2,z8,z4,z137]),(0,[z0,z7,z2,z8,z4,z5,z462]),(1,[z0,z7,z2,z95,z4,z62]),(0,[z0,z7,z2,z463,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z78,z5])],[],[(0,[z0,z172,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z464,z8,z4,z5]),(0,[z0,z199,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z465,z4,z5])],[(0,[z0,z7,z2,z8,z81,z4,z5]),(0,[z335,z0,z7,z2,z8,z4,z94]),(0,[z466,z0,z7,z2,z8,z4,z5]),(0,[z0,z20,z7,z2,z8,z116,z5]),(0,[z0,z199,z7,z8,z4,z50,z5]),(0,[z0,z7,z23,z467,z2,z8,z5]),(0,[z0,z257,z7,z23,z2,z4,z5]),(0,[z0,z7,z2,z13,z8,z47,z5])],[(0,[z0,z7,z468,z2,z8,z4,z5]),(0,[z0,z160,z7,z2,z13,z8,z5]),(0,[z0,z199,z7,z59,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z469]),(0,[z0,z7,z2,z8,z4,z470,z5]),(0,[z0,z7,z2,z471,z8,z4,z5])],[(0,[z165,z0,z7,z2,z8,z4,z195]),(0,[z0,z7,z472,z2,z8,z4,z5])]],
   [[(0,[z0,z473,z7,z2,z8,z4,z5]),(0,[z0,z257,z7,z59,z2,z8,z4])],[(0,[z0,z7,z2,z474,z8,z4,z5]),(1,[z165,z7,z71,z8,z4,z5]),(0,[z0,z7,z2,z475,z8,z4,z5]),(0,[z0,z7,z2,z8,z476,z4,z5])],[(0,[z0,z477,z7,z2,z8,z4,z5]),(0,[z197,z0,z7,z2,z8,z448,z5]),(0,[z0,z7,z23,z2,z95,z8,z5]),(0,[z478,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z475,z13,z8,z5])],[(0,[z0,z7,z2,z8,z36,z4,z5]),(0,[z0,z7,z2,z8,z479,z4,z5])],[(0,[z0,z7,z2,z480,z8,z4,z5]),(0,[z335,z7,z2,z8,z4,z137,z5]),(1,[z0,z7,z2,z8,z368,z5]),(0,[z0,z7,z481,z2,z8,z4,z5]),(1,[z0,z7,z23,z24,z2,z5]),(0,[z0,z7,z23,z2,z8,z106,z5]),(0,[z0,z79,z7,z2,z8,z47,z5])],[(0,[z0,z7,z2,z482,z8,z4,z5]),(1,[z277,z7,z2,z8,z118,z5]),(0,[z0,z7,z2,z8,z4,z483,z5]),(0,[z0,z7,z131,z2,z8,z332,z5]),(0,[z0,z7,z467,z2,z8,z4,z5])],[(0,[z0,z7,z233,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z484,z4,z5]),(0,[z0,z485,z7,z2,z8,z4,z5]),(0,[z0,z486,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z487,z5])],[(0,[z0,z488,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z5,z124]),(0,[z0,z489,z7,z2,z8,z4,z5]),(0,[z0,z490,z7,z2,z8,z4,z5])]],
   [[(0,[z0,z198,z7,z238,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z58,z5]),(0,[z49,z0,z20,z7,z2,z8,z4]),(0,[z49,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z491,z5])],[(0,[z64,z0,z7,z76,z8,z4,z5]),(0,[z159,z0,z7,z2,z8,z294,z5]),(0,[z0,z7,z2,z8,z492,z4,z5]),(0,[z49,z0,z7,z2,z13,z8,z5]),(0,[z333,z0,z7,z2,z8,z4,z5])],[(0,[z0,z493,z7,z2,z8,z4,z5])],[(0,[z0,z7,z59,z76,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z494,z5]),(0,[z0,z7,z2,z8,z4,z5,z495]),(1,[z0,z82,z2,z12,z4,z5]),(0,[z0,z7,z2,z8,z58,z332,z5]),(0,[z0,z7,z2,z8,z496,z4,z5]),(0,[z0,z56,z7,z23,z2,z8,z5])],[(0,[z0,z7,z497,z2,z8,z4,z5])],[(0,[z119,z0,z20,z7,z2,z8,z4]),(0,[z0,z198,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z58,z5]),(0,[z49,z0,z6,z7,z2,z8,z4]),(0,[z0,z7,z221,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z498,z5]),(0,[z119,z0,z7,z2,z13,z8,z5]),(0,[z0,z199,z7,z24,z8,z4,z5]),(0,[z0,z499,z7,z2,z8,z4,z5]),(0,[z0,z500,z7,z2,z8,z4,z5])],[(0,[z501,z0,z7,z2,z8,z4,z5]),(0,[z335,z119,z7,z2,z8,z4,z5]),(0,[z0,z7,z351,z2,z8,z4,z5]),(0,[z0,z79,z7,z23,z2,z8,z5])]],
   [[(0,[z0,z7,z2,z8,z502,z4,z5]),(0,[z0,z7,z134,z8,z36,z4,z5]),(0,[z501,z0,z7,z2,z13,z8,z5])],[(0,[z0,z7,z2,z8,z18,z118,z5]),(0,[z0,z7,z2,z8,z4,z5,z503]),(1,[z0,z6,z2,z8,z4,z124])],[(0,[z87,z0,z7,z2,z8,z4,z214]),(0,[z0,z7,z504,z2,z8,z4,z5]),(0,[z119,z0,z6,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z4,z505,z5]),(0,[z0,z7,z2,z506,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z507,z5])],[(0,[z0,z7,z2,z8,z4,z508,z5]),(0,[z0,z7,z2,z8,z109,z4,z5]),(0,[z0,z7,z23,z2,z8,z38,z5]),(0,[z0,z7,z2,z95,z8,z4,z5]),(0,[z0,z7,z509,z2,z47,z4,z5])],[(0,[z7,z71,z2,z76,z8,z4,z5]),(0,[z53,z0,z7,z2,z13,z8,z5]),(0,[z0,z510,z7,z2,z8,z4,z5]),(0,[z0,z7,z24,z2,z8,z4,z5]),(0,[z0,z7,z23,z131,z2,z8,z5]),(0,[z0,z511,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z512,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z513,z5])],[(0,[z514,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z59,z2,z8,z4,z94])],[(0,[z0,z7,z515,z2,z8,z4,z5]),(0,[z0,z516,z7,z2,z8,z4,z5]),(0,[z0,z7,z210,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z517]),(0,[z0,z378,z7,z2,z8,z4,z5]),(0,[z0,z7,z518,z2,z8,z4,z5])]],
   [[(1,[z0,z7,z2,z8,z4,z214]),(0,[z0,z7,z2,z446,z8,z4,z5]),(0,[z0,z7,z519,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z135,z4,z5])],[(0,[z87,z171,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z520,z4,z5]),(0,[z0,z7,z2,z8,z4,z521,z5])],[(0,[z133,z7,z2,z8,z81,z4,z5]),(0,[z0,z522,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z523,z8,z4,z5])],[(0,[z0,z7,z2,z81,z12,z4,z5]),(0,[z0,z7,z23,z2,z8,z5,z94]),(0,[z0,z7,z23,z2,z8,z96,z5]),(0,[z0,z7,z2,z13,z95,z8,z5]),(1,[z0,z7,z290,z2,z8,z5])],[(0,[z0,z524,z7,z2,z8,z4,z5]),(0,[z0,z7,z43,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z525,z5]),(0,[z0,z7,z23,z2,z8,z18,z5]),(0,[z0,z20,z7,z2,z8,z4,z9])],[(0,[z87,z0,z7,z340,z8,z4,z5]),(0,[z197,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z526,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z106,z5]),(0,[z0,z7,z2,z8,z47,z38,z4])],[(0,[z0,z7,z2,z527,z8,z4,z5]),(0,[z0,z51,z7,z2,z8,z4,z5])],[(0,[z87,z0,z7,z468,z8,z4,z5]),(0,[z0,z7,z528,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z529]),(0,[z0,z7,z530,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z531,z5])]],
   [[(0,[z532,z0,z7,z2,z8,z4,z5]),(0,[z165,z0,z7,z76,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z533,z5]),(0,[z0,z7,z2,z13,z8,z5,z124]),(0,[z0,z7,z530,z2,z13,z8,z5])],[(0,[z0,z7,z182,z2,z8,z4,z5]),(0,[z0,z534,z7,z2,z8,z4,z5]),(0,[z49,z0,z7,z2,z8,z4,z137]),(0,[z288,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z24,z2,z106,z4,z5]),(0,[z0,z7,z2,z8,z4,z470,z332])],[(0,[z0,z7,z182,z2,z13,z8,z5]),(0,[z64,z0,z7,z2,z8,z4,z5]),(0,[z159,z0,z7,z2,z80,z4,z5]),(1,[z0,z7,z509,z2,z4,z5])],[(1,[z0,z7,z340,z8,z4,z5]),(0,[z171,z0,z182,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z535,z4,z5]),(0,[z133,z0,z7,z2,z8,z4,z5]),(0,[z277,z0,z7,z2,z8,z54,z5]),(0,[z0,z536,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z537,z5]),(0,[z0,z198,z7,z230,z8,z4,z5]),(0,[z0,z20,z7,z2,z8,z4,z5]),(0,[z538,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z5,z127]),(0,[z0,z7,z2,z8,z539,z4,z5])],[(0,[z133,z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z23,z2,z8,z137,z5]),(1,[z0,z7,z2,z8,z448,z5]),(0,[z0,z7,z2,z8,z540,z4,z5]),(0,[z0,z20,z7,z2,z13,z8,z5]),(0,[z0,z7,z59,z2,z8,z4,z5]),(0,[z0,z541,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z50,z5])],[(1,[z0,z7,z468,z8,z4,z5]),(0,[z542,z0,z7,z2,z8,z4,z5]),(0,[z0,z82,z2,z8,z12,z4,z5]),(0,[z0,z82,z7,z23,z2,z8,z5]),(0,[z0,z2,z8,z18,z4,z58,z5]),(0,[z0,z7,z2,z8,z4,z5,z124])],[(0,[z0,z7,z2,z543,z8,z4,z5]),(0,[z119,z0,z7,z2,z8,z4,z137]),(0,[z0,z7,z2,z3,z8,z4,z5]),(0,[z0,z7,z2,z544,z8,z4,z5]),(1,[z0,z7,z8,z4,z69,z5])],[(0,[z0,z7,z2,z8,z4,z545,z5]),(0,[z0,z546,z7,z2,z8,z4,z5]),(0,[z0,z547,z7,z2,z8,z4,z5]),(1,[z0,z20,z2,z8,z4,z9]),(0,[z0,z7,z2,z8,z548,z4,z5]),(0,[z0,z7,z221,z2,z4,z332,z5]),(0,[z549,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z47,z550,z4,z5])]],
   [[(0,[z0,z7,z2,z8,z4,z5,z551]),(0,[z0,z7,z2,z552,z8,z4,z5]),(0,[z0,z143,z7,z131,z8,z4,z5])],[(0,[z0,z7,z553,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z50,z5])],[(0,[z0,z7,z2,z8,z4,z554,z5]),(0,[z0,z555,z7,z2,z8,z4,z5]),(0,[z0,z556,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z557,z8,z4,z5])],[(0,[z0,z558,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z559,z5]),(0,[z0,z7,z2,z8,z4,z560,z5]),(0,[z49,z0,z79,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z4,z561,z5])],[(0,[z562,z0,z7,z2,z8,z4,z5]),(0,[z197,z0,z7,z2,z8,z435,z5]),(0,[z0,z563,z7,z2,z8,z4,z5]),(0,[z0,z7,z564,z2,z8,z4,z5]),(0,[z0,z7,z565,z2,z8,z4,z5]),(0,[z0,z199,z7,z23,z2,z4,z5]),(0,[z566,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z567,z5]),(1,[z0,z7,z2,z8,z78,z5])],[(0,[z568,z0,z7,z2,z8,z4,z5]),(0,[z0,z6,z7,z2,z13,z8,z5]),(0,[z0,z143,z7,z2,z8,z332,z5])],[(0,[z0,z155,z2,z8,z4,z58,z5]),(0,[z0,z7,z2,z8,z4,z5,z569]),(0,[z0,z7,z210,z2,z8,z36,z5]),(0,[z0,z7,z2,z8,z570,z4,z5])],[]],
   [[(0,[z0,z7,z2,z571,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z572]),(0,[z0,z7,z2,z8,z573,z4,z5]),(0,[z0,z574,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z575,z8,z4,z5]),(0,[z0,z20,z7,z59,z2,z8,z4]),(0,[z0,z7,z2,z8,z4,z576,z5]),(0,[z0,z577,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z578,z4,z5])],[(0,[z0,z7,z7,z2,z8,z4,z5]),(0,[z0,z579,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z580,z5])],[(0,[z0,z7,z400,z23,z2,z8,z5]),(1,[z0,z7,z23,z2,z96,z5]),(1,[z0,z79,z7,z2,z8,z47])],[(0,[z171,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z581,z8,z4,z5]),(0,[z0,z7,z59,z2,z8,z4,z187]),(0,[z0,z7,z2,z8,z4,z582,z5]),(0,[z0,z7,z2,z106,z4,z5,z62]),(0,[z0,z79,z7,z2,z8,z38,z5]),(0,[z0,z7,z2,z583,z8,z4,z5])],[(0,[z171,z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z4,z584,z5]),(0,[z0,z7,z2,z13,z8,z5,z94]),(0,[z0,z7,z23,z2,z8,z19,z5]),(0,[z0,z7,z2,z13,z8,z96,z5]),(0,[z0,z7,z585,z2,z8,z4,z5])],[(0,[z0,z7,z2,z586,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z18,z5]),(0,[z0,z587,z7,z2,z8,z4,z5]),(0,[z0,z588,z7,z2,z8,z4,z5]),(0,[z147,z0,z7,z2,z8,z4,z5])],[(0,[z87,z0,z7,z2,z360,z4,z5]),(0,[z589,z0,z7,z2,z8,z4,z5]),(1,[z64,z7,z76,z8,z4,z5]),(0,[z590,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z134,z8,z4,z50,z5]),(0,[z0,z257,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z578,z5,z62]),(0,[z591,z0,z7,z2,z8,z4,z5])],[(1,[z0,z7,z2,z138,z8,z4]),(1,[z0,z227,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z4,z5,z592]),(0,[z0,z7,z2,z13,z593,z8,z5]),(0,[z0,z257,z7,z2,z13,z8,z5])]],
   [[(0,[z0,z7,z2,z8,z4,z5,z391]),(0,[z0,z7,z8,z4,z50,z5,z187]),(0,[z0,z7,z23,z2,z8,z5,z187])],[(0,[z87,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z594,z8,z4,z5]),(0,[z0,z6,z7,z59,z2,z8,z4]),(0,[z0,z7,z2,z595,z8,z4,z5])],[(0,[z0,z7,z2,z8,z153,z4,z5]),(0,[z171,z0,z172,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z596,z5]),(0,[z0,z7,z24,z2,z36,z4,z5]),(0,[z0,z7,z23,z2,z4,z96,z5]),(0,[z0,z7,z2,z8,z38,z4,z5])],[(0,[z0,z7,z2,z597,z8,z4,z5]),(0,[z0,z82,z7,z2,z3,z4,z5])],[(1,[z0,z7,z2,z360,z4,z5]),(0,[z0,z7,z2,z8,z54,z4,z5]),(0,[z0,z7,z509,z2,z8,z4,z5])],[(0,[z598,z0,z7,z2,z8,z4,z5]),(0,[z49,z0,z7,z2,z8,z4,z94]),(1,[z0,z7,z412,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z137,z5]),(0,[z0,z7,z452,z2,z8,z12,z5]),(0,[z0,z7,z2,z8,z599,z4,z5]),(0,[z0,z7,z2,z104,z13,z8,z5])],[(0,[z0,z7,z2,z8,z4,z5,z600]),(1,[z0,z7,z2,z8,z4,z470]),(0,[z0,z7,z2,z8,z601,z4,z5])],[(0,[z197,z0,z2,z230,z8,z4,z5]),(0,[z0,z602,z7,z2,z8,z4,z5]),(0,[z0,z603,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z604,z5]),(1,[z0,z7,z23,z2,z8,z5])]],
   [[(0,[z0,z7,z2,z605,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z606,z5]),(0,[z0,z198,z238,z2,z8,z4,z5]),(0,[z0,z160,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z38,z5,z75])],[(0,[z64,z0,z7,z71,z8,z4,z5]),(0,[z0,z7,z2,z8,z607,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z608]),(0,[z0,z7,z2,z8,z4,z609,z5]),(0,[z0,z7,z2,z8,z4,z5,z610])],[(0,[z0,z7,z2,z8,z4,z137,z5]),(0,[z119,z0,z7,z2,z8,z4,z94]),(0,[z0,z611,z7,z2,z8,z4,z5]),(0,[z0,z612,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z142,z4,z5]),(0,[z613,z0,z7,z2,z8,z4,z5]),(0,[z0,z144,z7,z2,z8,z4,z332]),(0,[z0,z7,z2,z8,z614,z4,z5]),(0,[z0,z7,z2,z8,z550,z4,z5])],[(0,[z0,z7,z59,z71,z8,z4,z5]),(0,[z615,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z616,z4,z5]),(0,[z617,z0,z7,z2,z8,z4,z5]),(1,[z0,z7,z2,z8,z25,z5]),(0,[z0,z143,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z618,z5]),(0,[z0,z7,z2,z8,z4,z619,z5]),(0,[z0,z257,z7,z2,z106,z4,z5])],[(0,[z277,z0,z7,z2,z8,z118,z5]),(0,[z0,z7,z620,z2,z8,z4,z5]),(0,[z0,z621,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z622,z5]),(0,[z0,z20,z7,z2,z8,z4,z124])],[(0,[z0,z7,z623,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z624,z5])],[(0,[z625,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z626,z5]),(0,[z0,z7,z2,z8,z627,z4,z5]),(0,[z0,z7,z2,z628,z8,z4,z5]),(0,[z629,z0,z7,z2,z8,z4,z5])],[(0,[z630,z0,z7,z2,z8,z4,z5]),(0,[z631,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z632,z5]),(0,[z0,z7,z2,z8,z4,z5,z5]),(1,[z0,z7,z2,z8,z42,z5]),(0,[z0,z7,z2,z593,z8,z4,z5])]],
   [[(0,[z0,z2,z3,z8,z12,z4,z5]),(0,[z0,z257,z7,z2,z4,z77,z5])],[(0,[z0,z0,z7,z2,z8,z4,z5]),(0,[z633,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z634,z5]),(0,[z53,z7,z2,z8,z54,z4,z5]),(0,[z0,z7,z2,z8,z4,z635,z5]),(0,[z0,z7,z2,z8,z636,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z637])],[(0,[z0,z7,z2,z8,z18,z38,z5])],[(0,[z0,z7,z238,z76,z8,z4,z5]),(0,[z0,z638,z7,z2,z8,z4,z5]),(0,[z0,z7,z24,z2,z134,z4,z5]),(0,[z0,z7,z2,z8,z4,z639,z5])],[(0,[z0,z7,z640,z2,z8,z4,z5]),(0,[z641,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z642,z4,z5]),(0,[z0,z7,z2,z643,z8,z4,z5]),(0,[z0,z644,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z645,z5]),(0,[z0,z6,z7,z2,z8,z4,z124]),(0,[z0,z7,z413,z2,z8,z4,z5]),(0,[z0,z7,z646,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z19,z5])],[(0,[z0,z647,z7,z2,z8,z4,z5]),(0,[z648,z0,z7,z2,z8,z4,z5]),(1,[z0,z7,z2,z8,z435,z5]),(0,[z0,z649,z7,z2,z8,z4,z5])],[(0,[z650,z0,z7,z2,z8,z4,z5])]],
   [[(0,[z133,z0,z7,z2,z80,z4,z5]),(1,[z0,z7,z2,z8,z201,z5]),(0,[z119,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z116,z5]),(0,[z0,z7,z23,z2,z8,z9,z5]),(0,[z0,z651,z7,z2,z8,z4,z5]),(0,[z0,z652,z7,z2,z8,z4,z5]),(0,[z0,z653,z7,z2,z8,z4,z5]),(0,[z0,z7,z654,z2,z8,z4,z5]),(1,[z0,z7,z2,z550,z4,z5])],[(0,[z0,z7,z2,z8,z4,z655,z5]),(0,[z0,z7,z2,z8,z656,z4,z5]),(0,[z64,z7,z2,z76,z8,z4,z5]),(0,[z0,z7,z71,z8,z4,z50,z5]),(0,[z0,z160,z7,z2,z8,z58,z5]),(0,[z0,z7,z2,z13,z8,z5,z187]),(0,[z0,z7,z2,z8,z657,z4,z5])],[(0,[z658,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z659,z4,z5]),(0,[z0,z7,z2,z8,z660,z4,z5]),(0,[z0,z155,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z661,z4,z5])],[(0,[z0,z168,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z80,z12,z4,z5]),(0,[z0,z7,z2,z8,z662,z4,z5]),(0,[z0,z7,z2,z663,z8,z4,z5]),(0,[z0,z155,z7,z2,z13,z8,z5]),(0,[z0,z664,z7,z2,z8,z4,z5]),(0,[z0,z665,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z446,z8,z81,z5]),(0,[z0,z7,z2,z666,z8,z4,z5]),(0,[z667,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z148,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z5,z668]),(0,[z0,z7,z2,z8,z4,z669,z5]),(0,[z0,z7,z670,z2,z8,z4,z5]),(0,[z0,z143,z7,z8,z4,z332,z5]),(0,[z0,z304,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z264,z4,z5])],[(0,[z0,z7,z2,z671,z8,z4,z5]),(0,[z53,z0,z7,z2,z8,z4,z5]),(1,[z0,z257,z7,z2,z4,z77])],[(0,[z159,z7,z2,z80,z8,z4,z5]),(0,[z672,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z8,z19,z4,z332,z5])]],
   [[(0,[z165,z0,z7,z71,z8,z4,z5]),(0,[z159,z0,z7,z2,z81,z4,z5]),(0,[z0,z7,z2,z8,z673,z4,z5]),(0,[z0,z1,z7,z23,z2,z8,z5]),(0,[z674,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z42,z5])],[(0,[z277,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z675,z4,z5]),(0,[z0,z7,z23,z2,z13,z8,z5])],[(0,[z0,z7,z2,z676,z8,z4,z5]),(0,[z159,z0,z7,z2,z8,z201,z5]),(1,[z0,z82,z7,z23,z2,z5]),(0,[z49,z0,z7,z2,z8,z4,z187]),(0,[z0,z7,z2,z8,z4,z677,z5])],[(0,[z0,z204,z7,z2,z8,z4,z5]),(0,[z678,z0,z7,z2,z8,z4,z5]),(0,[z53,z0,z7,z2,z408,z4,z5]),(0,[z679,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z452,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z680,z4,z5]),(0,[z0,z7,z2,z681,z8,z4,z5])],[(0,[z0,z682,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z683]),(0,[z335,z0,z7,z412,z8,z4,z5])],[(0,[z0,z7,z23,z2,z8,z5,z62]),(0,[z0,z7,z23,z2,z8,z5,z75])],[(0,[z335,z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z684,z4,z5])]],
   [[(0,[z0,z685,z7,z2,z8,z4,z5]),(0,[z0,z686,z7,z2,z8,z4,z5]),(0,[z687,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z131,z2,z8,z19,z5]),(0,[z0,z7,z2,z13,z394,z8,z5])],[(0,[z0,z7,z2,z8,z688,z4,z5]),(0,[z0,z198,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z5,z689])],[(0,[z690,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z691,z8,z4,z5]),(0,[z692,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z693,z5])],[(0,[z0,z7,z2,z8,z4,z137,z124]),(0,[z0,z7,z2,z694,z8,z4,z5]),(0,[z0,z7,z695,z2,z8,z4,z5]),(0,[z0,z6,z2,z8,z4,z5,z124]),(0,[z0,z7,z23,z2,z8,z112,z5]),(0,[z0,z7,z2,z8,z4,z696,z5])],[(0,[z0,z697,z7,z2,z8,z4,z5]),(0,[z0,z7,z238,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z698,z5])],[(0,[z0,z172,z7,z2,z8,z4,z5]),(0,[z699,z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z700]),(0,[z0,z7,z2,z701,z8,z4,z5]),(0,[z0,z7,z2,z85,z8,z4,z5]),(0,[z0,z702,z7,z2,z8,z4,z5]),(0,[z0,z7,z238,z2,z13,z8,z5]),(0,[z0,z199,z7,z2,z8,z4,z5]),(1,[z0,z7,z2,z8,z578,z5])],[(0,[z87,z0,z7,z2,z8,z97,z5]),(0,[z0,z172,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z8,z703,z4,z5]),(0,[z0,z7,z2,z8,z4,z5,z704]),(0,[z0,z7,z2,z8,z4,z5,z705]),(0,[z0,z199,z7,z2,z13,z8,z5]),(0,[z0,z706,z7,z2,z8,z4,z5]),(0,[z357,z0,z7,z23,z2,z8,z5])],[(1,[z119,z7,z2,z8,z4,z94])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z7,z2,z8,z707,z5]),(0,[z0,z708,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z4,z709]),(0,[z0,z710,z7,z2,z8,z4]),(0,[z0,z199,z7,z13,z36,z5])],[(0,[z0,z7,z2,z711,z8,z5]),(0,[z0,z144,z7,z23,z2,z8]),(0,[z0,z7,z2,z13,z106,z5])],[(0,[z7,z2,z8,z4,z712,z5]),(0,[z0,z7,z2,z8,z713,z5]),(0,[z0,z7,z2,z8,z135,z4]),(0,[z0,z257,z7,z23,z2,z62])],[(0,[z0,z7,z714,z8,z4,z5]),(0,[z0,z7,z2,z8,z715,z5]),(0,[z0,z273,z2,z8,z58,z5]),(0,[z0,z405,z7,z221,z2,z5])],[(0,[z0,z7,z2,z8,z4,z716]),(0,[z0,z7,z2,z8,z142,z5]),(0,[z0,z155,z140,z2,z58,z5])],[(0,[z159,z7,z23,z2,z80,z5]),(0,[z53,z7,z2,z8,z54,z5]),(0,[z0,z7,z2,z717,z116,z5])],[(0,[z0,z7,z2,z718,z8,z5]),(0,[z0,z7,z2,z446,z106,z5]),(0,[z0,z719,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z720,z5]),(0,[z0,z7,z2,z8,z42,z5]),(0,[z0,z7,z2,z8,z721,z5])],[(0,[z0,z168,z7,z23,z2,z8]),(0,[z0,z7,z722,z8,z4,z5]),(0,[z0,z7,z2,z8,z723,z5]),(0,[z0,z7,z2,z8,z724,z5]),(0,[z0,z7,z2,z8,z725,z5]),(0,[z0,z7,z2,z8,z4,z726]),(0,[z0,z7,z2,z8,z727,z5]),(0,[z0,z7,z2,z728,z4,z5])]],
   [[(0,[z0,z7,z2,z8,z4,z729]),(0,[z0,z7,z2,z8,z730,z5]),(0,[z0,z7,z2,z731,z4,z5]),(0,[z0,z199,z7,z23,z24,z5]),(0,[z333,z7,z2,z104,z8,z5])],[(0,[z0,z7,z732,z8,z4,z5]),(0,[z133,z7,z23,z2,z81,z5]),(0,[z0,z7,z2,z8,z733,z5]),(0,[z734,z7,z2,z8,z4,z5])],[(0,[z0,z7,z23,z2,z141,z5]),(0,[z0,z735,z7,z2,z4,z5]),(0,[z0,z7,z2,z8,z4,z736]),(0,[z0,z7,z2,z737,z4,z5]),(0,[z0,z7,z738,z8,z4,z5]),(0,[z53,z7,z2,z408,z54,z5]),(0,[z0,z739,z23,z2,z8,z5])],[(0,[z0,z426,z7,z8,z332,z5]),(0,[z0,z257,z7,z2,z13,z77])],[],[(0,[z0,z7,z740,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z741]),(0,[z0,z7,z2,z8,z742,z5])],[(0,[z0,z7,z59,z8,z4,z668]),(0,[z0,z7,z2,z8,z4,z743]),(0,[z0,z7,z744,z2,z8,z5]),(0,[z0,z7,z2,z578,z550,z5])],[(0,[z0,z7,z2,z8,z201,z5])]],
   [[(0,[z0,z7,z2,z745,z4,z5]),(0,[z0,z7,z746,z2,z8,z5]),(0,[z0,z7,z2,z747,z8,z5]),(0,[z0,z20,z98,z2,z8,z4]),(0,[z0,z7,z8,z728,z4,z5]),(0,[z0,z257,z7,z23,z2,z77]),(0,[z0,z7,z290,z2,z5,z62])],[(0,[z0,z7,z468,z8,z4,z214]),(0,[z0,z748,z7,z2,z8,z4])],[(0,[z0,z7,z2,z8,z749,z5]),(0,[z0,z7,z2,z750,z8,z5]),(0,[z0,z7,z23,z2,z408,z5]),(0,[z0,z7,z751,z2,z8,z5]),(0,[z0,z144,z7,z2,z4,z316])],[(1,[z7,z752,z8,z4,z5]),(0,[z0,z7,z753,z8,z4,z5]),(0,[z7,z2,z8,z725,z4,z5]),(0,[z0,z7,z2,z8,z754,z5]),(0,[z0,z7,z2,z106,z42,z5])],[(0,[z87,z182,z2,z8,z4,z88]),(0,[z64,z7,z752,z8,z4,z5]),(0,[z0,z7,z2,z8,z755,z5]),(0,[z0,z7,z2,z8,z756,z4])],[(0,[z0,z7,z2,z757,z4,z5]),(0,[z0,z7,z71,z138,z8,z4]),(0,[z0,z7,z2,z13,z440,z5]),(0,[z667,z7,z2,z8,z4,z137]),(1,[z0,z2,z8,z4,z758]),(0,[z0,z257,z7,z2,z4,z77])],[(0,[z0,z6,z2,z471,z8,z4])],[(0,[z0,z759,z7,z2,z8,z4]),(0,[z0,z7,z24,z2,z760,z5])]],
   [[(1,[z7,z2,z8,z4,z712]),(0,[z0,z7,z59,z8,z4,z537]),(0,[z0,z7,z744,z2,z116,z5]),(0,[z0,z7,z2,z8,z4,z761]),(0,[z762,z7,z23,z2,z8,z5])],[(0,[z0,z7,z2,z141,z97,z5]),(0,[z0,z7,z2,z8,z4,z763]),(0,[z764,z7,z2,z8,z4,z5]),(0,[z0,z1,z7,z765,z2,z5]),(0,[z0,z199,z7,z148,z4,z5]),(0,[z0,z7,z2,z13,z8,z761])],[(0,[z0,z7,z2,z8,z766,z5]),(0,[z0,z7,z2,z13,z57,z5]),(0,[z0,z7,z23,z2,z593,z5]),(0,[z0,z7,z509,z2,z13,z5])],[(0,[z0,z7,z767,z8,z4,z5]),(0,[z0,z2,z768,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z769]),(0,[z0,z7,z2,z8,z770,z5]),(0,[z0,z155,z2,z57,z58,z5])],[(0,[z0,z7,z771,z8,z4,z5]),(0,[z0,z7,z772,z8,z4,z5]),(0,[z0,z7,z773,z2,z8,z5]),(0,[z0,z2,z8,z774,z4,z5])],[(0,[z0,z7,z23,z2,z8,z775]),(0,[z0,z79,z7,z2,z8,z112])],[(0,[z0,z7,z452,z2,z81,z5]),(0,[z0,z7,z2,z8,z776,z5]),(0,[z0,z7,z2,z387,z4,z62]),(0,[z0,z7,z114,z8,z578,z5])],[(0,[z0,z7,z2,z8,z777,z5]),(0,[z0,z7,z2,z778,z8,z5]),(0,[z0,z7,z221,z2,z4,z5]),(0,[z0,z143,z7,z8,z779,z5])]],
   [[(0,[z0,z7,z2,z8,z4,z780]),(0,[z7,z71,z752,z8,z4,z5]),(0,[z0,z7,z23,z2,z196,z5]),(0,[z0,z7,z2,z8,z781,z5])],[(0,[z0,z7,z782,z2,z8,z5]),(0,[z0,z199,z7,z36,z4,z5]),(0,[z123,z0,z7,z509,z2,z5])],[(0,[z0,z7,z8,z783,z4,z5]),(0,[z0,z784,z7,z2,z8,z4]),(0,[z0,z199,z7,z23,z59,z5])],[(0,[z0,z7,z785,z2,z4,z5]),(0,[z0,z7,z2,z8,z4,z786]),(1,[z0,z7,z2,z787,z5])],[(0,[z0,z7,z2,z788,z8,z5]),(0,[z87,z182,z2,z8,z153,z5]),(0,[z87,z204,z182,z2,z8,z4]),(0,[z0,z7,z2,z789,z4,z5]),(0,[z0,z6,z23,z2,z8,z124]),(0,[z0,z7,z8,z19,z779,z5]),(0,[z0,z7,z400,z2,z8,z127])],[(0,[z0,z7,z2,z790,z8,z5]),(0,[z0,z7,z233,z13,z8,z5]),(0,[z0,z91,z7,z140,z2,z5]),(0,[z0,z33,z7,z23,z2,z5])],[(0,[z64,z7,z23,z76,z8,z5]),(0,[z0,z7,z23,z2,z523,z5])],[(0,[z0,z7,z23,z2,z237,z5]),(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z155,z351,z2,z8,z5]),(1,[z0,z7,z728,z4,z5]),(0,[z0,z7,z59,z8,z4,z693])]],
   [[(0,[z0,z7,z2,z360,z4,z214]),(0,[z0,z7,z2,z8,z4,z791]),(0,[z0,z7,z2,z792,z8,z4]),(0,[z0,z793,z23,z2,z8,z5])],[(0,[z87,z182,z2,z141,z4,z5]),(0,[z794,z7,z2,z8,z4,z5]),(0,[z0,z7,z23,z738,z8,z5]),(0,[z0,z7,z2,z8,z795,z4])],[(0,[z0,z7,z2,z796,z4,z5]),(0,[z0,z7,z797,z2,z8,z5])],[(0,[z0,z7,z2,z8,z97,z5]),(0,[z0,z7,z23,z2,z8,z214]),(0,[z692,z7,z76,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z798]),(0,[z0,z7,z2,z8,z799,z5]),(0,[z49,z0,z7,z463,z8,z4])],[(0,[z0,z7,z800,z2,z8,z5]),(0,[z0,z7,z2,z27,z8,z5]),(0,[z0,z378,z2,z103,z8,z5])],[(0,[z0,z7,z782,z2,z141,z5]),(0,[z0,z7,z2,z8,z801,z5]),(0,[z0,z7,z2,z8,z4,z802]),(0,[z0,z7,z23,z2,z464,z5]),(0,[z0,z7,z2,z13,z231,z5]),(0,[z0,z7,z23,z242,z2,z5]),(0,[z0,z7,z23,z2,z330,z5])],[(0,[z0,z803,z7,z2,z8,z4]),(0,[z0,z804,z7,z8,z4,z5]),(0,[z0,z7,z2,z13,z8,z195]),(0,[z0,z1,z2,z3,z336,z5]),(0,[z0,z7,z2,z8,z47,z100])],[(0,[z0,z7,z23,z2,z360,z5]),(0,[z0,z7,z2,z81,z201,z5])]],
   [[(0,[z0,z7,z2,z805,z8,z4]),(0,[z0,z7,z44,z2,z8,z5]),(0,[z0,z7,z806,z2,z8,z5]),(0,[z0,z7,z23,z69,z5,z62]),(0,[z0,z7,z114,z8,z74,z5])],[(0,[z0,z7,z2,z8,z807,z5]),(0,[z0,z7,z2,z13,z8,z808])],[(0,[z0,z7,z23,z2,z607,z5])],[(0,[z0,z7,z340,z360,z4,z5]),(0,[z0,z7,z809,z2,z8,z5]),(0,[z0,z7,z2,z95,z578,z62])],[(0,[z0,z810,z7,z2,z8,z4]),(0,[z0,z7,z2,z811,z4,z5]),(0,[z0,z7,z2,z812,z4,z5]),(0,[z0,z82,z2,z813,z4,z5]),(0,[z0,z7,z23,z2,z5,z62]),(0,[z0,z7,z2,z8,z814,z5]),(0,[z501,z7,z2,z593,z8,z5])],[(0,[z0,z7,z468,z360,z4,z5]),(0,[z0,z7,z2,z8,z815,z5]),(0,[z0,z816,z2,z8,z4,z5]),(0,[z0,z198,z238,z8,z4,z5]),(0,[z0,z7,z509,z2,z58,z5]),(0,[z0,z7,z2,z8,z817,z5])],[(0,[z0,z7,z2,z8,z818,z5]),(0,[z0,z308,z7,z23,z2,z5]),(0,[z0,z7,z2,z819,z8,z5]),(0,[z0,z198,z238,z13,z8,z5]),(0,[z0,z143,z7,z148,z8,z5]),(0,[z0,z7,z2,z4,z820,z62])],[(0,[z0,z821,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z822,z5]),(0,[z0,z7,z2,z8,z823,z5]),(0,[z0,z7,z2,z824,z81,z5]),(0,[z7,z2,z8,z4,z712,z94]),(0,[z0,z7,z210,z2,z8,z135]),(0,[z0,z7,z825,z2,z4,z5]),(0,[z0,z7,z2,z13,z557,z5])]],
   [[(0,[z0,z7,z23,z2,z446,z5]),(0,[z0,z7,z8,z779,z332,z5]),(0,[z0,z7,z23,z2,z350,z5]),(0,[z0,z7,z2,z8,z795,z5])],[(0,[z0,z7,z131,z8,z19,z5]),(0,[z0,z7,z23,z114,z8,z5]),(0,[z123,z0,z7,z2,z8,z265])],[(0,[z0,z7,z2,z826,z4,z5]),(0,[z0,z20,z23,z2,z8,z9]),(0,[z0,z7,z23,z59,z8,z187]),(0,[z0,z7,z23,z2,z491,z5])],[(0,[z0,z7,z827,z2,z8,z5]),(0,[z0,z7,z2,z8,z828,z5]),(0,[z7,z2,z752,z8,z4,z5]),(0,[z133,z7,z44,z2,z81,z5]),(0,[z0,z768,z230,z8,z4,z5]),(0,[z0,z14,z7,z210,z2,z8])],[(0,[z87,z182,z2,z13,z8,z5]),(0,[z0,z7,z2,z80,z201,z5]),(0,[z0,z82,z452,z2,z12,z5]),(0,[z0,z7,z2,z8,z774,z5])],[(0,[z451,z7,z2,z81,z4,z5]),(0,[z0,z7,z2,z829,z4,z5]),(0,[z7,z2,z8,z54,z725,z5]),(0,[z0,z7,z233,z8,z4,z137]),(0,[z0,z7,z23,z2,z5,z495])],[(0,[z0,z7,z23,z2,z284,z5]),(0,[z0,z7,z744,z2,z4,z5]),(0,[z0,z199,z7,z135,z36,z4]),(0,[z0,z7,z2,z8,z779,z5])],[(0,[z0,z7,z2,z8,z4,z830]),(0,[z0,z7,z2,z831,z8,z5]),(0,[z832,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z109,z5]),(0,[z0,z7,z2,z8,z833,z5]),(0,[z0,z7,z23,z2,z73,z5]),(0,[z0,z144,z7,z2,z13,z8]),(0,[z0,z7,z23,z2,z550,z5]),(0,[z0,z7,z2,z95,z4,z820]),(0,[z0,z257,z7,z2,z77,z78])]],
   [[(0,[z0,z7,z2,z8,z4,z88]),(0,[z0,z7,z2,z8,z4,z834]),(0,[z0,z7,z23,z2,z108,z5]),(0,[z0,z1,z2,z3,z368,z5]),(0,[z0,z7,z728,z36,z4,z5]),(0,[z0,z199,z7,z210,z36,z5]),(0,[z0,z7,z2,z13,z8,z135])],[(0,[z0,z7,z2,z8,z835,z5]),(0,[z0,z7,z2,z8,z116,z5]),(0,[z0,z7,z836,z2,z8,z5])],[(0,[z0,z7,z2,z837,z8,z5]),(0,[z0,z7,z838,z2,z8,z5]),(0,[z0,z7,z2,z13,z696,z5])],[(0,[z0,z7,z59,z8,z4,z150]),(0,[z165,z7,z71,z8,z4,z195]),(0,[z0,z7,z23,z2,z628,z5]),(1,[z0,z7,z8,z4,z786])],[(0,[z0,z7,z2,z8,z839,z5]),(0,[z53,z7,z2,z8,z725,z5]),(0,[z0,z7,z2,z4,z840,z5]),(0,[z0,z313,z7,z23,z2,z5])],[(0,[z0,z168,z7,z2,z13,z8]),(0,[z0,z7,z2,z95,z74,z62])],[(0,[z0,z841,z7,z2,z8,z4])],[(0,[z0,z7,z23,z2,z368,z5]),(0,[z0,z7,z24,z134,z4,z5]),(0,[z0,z144,z7,z2,z8,z4])]],
   [[(0,[z0,z225,z2,z12,z4,z5]),(0,[z458,z7,z2,z80,z4,z5]),(0,[z0,z7,z842,z8,z4,z5]),(0,[z0,z199,z7,z109,z36,z5]),(0,[z0,z7,z23,z722,z8,z5])],[(0,[z0,z7,z843,z8,z4,z5]),(0,[z0,z7,z23,z2,z80,z5]),(0,[z0,z7,z2,z8,z4,z844]),(0,[z0,z7,z23,z2,z376,z5]),(0,[z0,z7,z23,z2,z8,z845]),(0,[z0,z653,z7,z23,z2,z5])],[(0,[z0,z155,z2,z8,z58,z5]),(0,[z0,z846,z2,z8,z4,z5]),(0,[z0,z7,z847,z8,z4,z5]),(0,[z0,z257,z7,z2,z4,z820])],[(0,[z0,z7,z2,z8,z4,z848]),(0,[z0,z7,z2,z8,z4,z849]),(0,[z0,z7,z850,z2,z8,z5]),(0,[z0,z20,z7,z744,z2,z5]),(0,[z0,z7,z2,z4,z316,z5])],[(0,[z0,z7,z2,z8,z4,z851])],[(0,[z0,z7,z2,z852,z4,z5]),(0,[z0,z168,z7,z2,z8,z4]),(0,[z0,z7,z853,z2,z8,z5]),(0,[z0,z7,z854,z8,z4,z5]),(0,[z49,z0,z7,z13,z8,z50])],[],[(1,[z0,z768,z8,z4,z5]),(0,[z0,z7,z2,z855,z4,z5])]],
   [[(0,[z0,z7,z2,z8,z153,z5]),(0,[z0,z856,z7,z2,z8,z5]),(0,[z0,z7,z2,z8,z4,z857]),(0,[z0,z7,z2,z8,z858,z5]),(0,[z0,z7,z2,z859,z4,z5]),(0,[z159,z7,z2,z80,z4,z5]),(0,[z0,z7,z860,z8,z4,z5]),(0,[z0,z1,z23,z2,z3,z5])],[(0,[z335,z7,z233,z8,z4,z137]),(0,[z0,z7,z2,z861,z8,z4]),(0,[z0,z7,z2,z8,z58,z470]),(0,[z0,z7,z23,z2,z8,z470])],[(0,[z0,z7,z2,z862,z4,z5]),(0,[z7,z2,z8,z725,z118,z5]),(0,[z335,z7,z2,z13,z8,z137]),(0,[z0,z7,z2,z8,z863,z5]),(0,[z0,z7,z2,z864,z4,z5]),(0,[z0,z7,z59,z8,z4,z187])],[(0,[z0,z7,z2,z8,z865,z5]),(0,[z0,z7,z2,z8,z866,z5]),(0,[z0,z7,z59,z13,z8,z187])],[(0,[z0,z7,z2,z867,z4,z5]),(0,[z0,z225,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z868,z4]),(0,[z0,z7,z2,z869,z4,z5])],[(0,[z0,z7,z2,z141,z4,z5]),(0,[z0,z7,z2,z870,z4,z5]),(0,[z0,z82,z51,z23,z2,z5]),(0,[z0,z1,z7,z452,z2,z5]),(0,[z0,z7,z2,z8,z4,z871])],[(0,[z0,z7,z23,z2,z455,z5]),(0,[z0,z7,z23,z2,z406,z5])],[(0,[z0,z7,z76,z8,z4,z195]),(0,[z0,z7,z2,z85,z54,z5]),(0,[z0,z7,z2,z8,z4,z872])]],
   [[(0,[z0,z7,z2,z8,z97,z214]),(0,[z0,z7,z2,z8,z4,z391]),(0,[z0,z7,z873,z2,z8,z5]),(0,[z0,z199,z7,z728,z4,z5]),(0,[z0,z14,z7,z2,z13,z8]),(0,[z0,z7,z8,z4,z50,z211]),(0,[z0,z7,z221,z2,z13,z5])],[(0,[z0,z7,z2,z13,z8,z391]),(0,[z0,z7,z233,z8,z4,z94])],[(0,[z0,z7,z23,z276,z2,z5]),(1,[z7,z2,z874,z4,z5]),(0,[z0,z7,z23,z2,z787,z5])],[(0,[z0,z7,z23,z2,z285,z5]),(0,[z0,z7,z2,z8,z875,z5]),(0,[z0,z405,z7,z23,z2,z5]),(0,[z0,z7,z2,z316,z42,z5]),(0,[z0,z143,z7,z221,z2,z5]),(0,[z0,z7,z23,z2,z60,z5])],[(0,[z0,z7,z2,z8,z4,z876]),(0,[z0,z7,z2,z877,z141,z5]),(0,[z0,z7,z878,z2,z4,z5]),(0,[z0,z7,z879,z2,z8,z5]),(0,[z549,z7,z2,z81,z4,z5]),(0,[z0,z7,z8,z578,z69,z5])],[(0,[z439,z0,z7,z23,z2,z5]),(0,[z0,z14,z7,z23,z2,z8]),(0,[z0,z7,z2,z13,z316,z5])],[(0,[z0,z7,z2,z8,z880,z4]),(0,[z0,z7,z23,z2,z659,z5]),(0,[z667,z7,z71,z8,z4,z5]),(0,[z0,z7,z2,z881,z8,z5]),(0,[z0,z7,z23,z2,z5,z421]),(1,[z0,z7,z8,z779,z5])],[(0,[z0,z7,z882,z2,z360,z5]),(0,[z0,z66,z2,z3,z4,z5]),(0,[z49,z0,z7,z2,z8,z142]),(0,[z0,z7,z210,z2,z8,z5]),(0,[z0,z7,z2,z8,z38,z127]),(0,[z0,z7,z23,z2,z424,z5])]],
   [[(0,[z0,z7,z806,z2,z4,z5]),(0,[z0,z7,z2,z8,z883,z5]),(0,[z0,z14,z7,z2,z8,z4]),(0,[z566,z0,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z884,z5])],[(0,[z0,z885,z7,z8,z4,z5]),(0,[z0,z7,z2,z8,z886,z5])],[(0,[z0,z7,z2,z8,z887,z5]),(0,[z0,z82,z1,z23,z2,z5]),(0,[z0,z7,z509,z2,z18,z5]),(0,[z0,z324,z7,z23,z2,z5]),(0,[z0,z7,z59,z8,z4,z705]),(0,[z0,z199,z7,z23,z36,z5]),(0,[z123,z0,z7,z23,z2,z5]),(0,[z0,z7,z114,z13,z8,z5])],[(0,[z0,z7,z340,z8,z97,z5]),(0,[z0,z7,z2,z888,z4,z5]),(0,[z0,z7,z2,z889,z8,z5]),(0,[z0,z7,z23,z2,z694,z5]),(0,[z0,z7,z2,z8,z890,z5])],[(0,[z165,z7,z752,z8,z4,z5]),(0,[z159,z7,z2,z80,z294,z5]),(0,[z0,z7,z140,z2,z4,z5])],[(0,[z0,z7,z468,z8,z97,z5]),(0,[z7,z23,z2,z80,z81,z5]),(0,[z0,z7,z2,z8,z891,z5]),(0,[z0,z7,z59,z8,z570,z4]),(0,[z0,z7,z2,z8,z4,z820])],[(0,[z7,z2,z8,z892,z4,z5]),(0,[z0,z7,z8,z4,z779,z5]),(0,[z0,z7,z2,z893,z4,z5]),(0,[z0,z7,z894,z2,z8,z5]),(0,[z0,z7,z2,z8,z895,z5]),(0,[z0,z7,z2,z578,z106,z5])],[(0,[z0,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z896,z5]),(0,[z0,z7,z233,z8,z4,z5]),(0,[z219,z0,z7,z8,z4,z50]),(1,[z0,z7,z806,z2,z5]),(0,[z897,z7,z2,z8,z4,z5]),(0,[z0,z7,z898,z8,z4,z5]),(0,[z0,z56,z351,z2,z8,z5]),(0,[z0,z7,z23,z2,z13,z5])]],
   [[(0,[z0,z7,z2,z13,z8,z5]),(0,[z0,z7,z2,z899,z4,z5]),(0,[z87,z182,z2,z8,z4,z214]),(0,[z0,z20,z7,z233,z8,z4]),(0,[z0,z2,z8,z813,z4,z5])],[(0,[z133,z7,z2,z81,z4,z5]),(0,[z0,z7,z2,z8,z900,z4]),(0,[z0,z7,z23,z392,z2,z5]),(0,[z0,z7,z23,z2,z453,z5]),(0,[z7,z2,z8,z4,z5,z901]),(0,[z0,z7,z23,z114,z4,z5]),(0,[z0,z79,z7,z2,z8,z795])],[(0,[z0,z7,z23,z2,z81,z5]),(1,[z7,z2,z8,z725,z5]),(0,[z53,z7,z2,z593,z8,z5]),(0,[z0,z7,z2,z4,z902,z5]),(0,[z0,z7,z2,z903,z8,z5])],[(0,[z197,z0,z768,z8,z4,z5])],[(0,[z0,z7,z2,z408,z4,z5]),(0,[z7,z2,z8,z4,z904,z5])],[(0,[z0,z7,z2,z8,z905,z5]),(0,[z0,z7,z23,z2,z136,z5]),(0,[z0,z7,z2,z446,z8,z5]),(0,[z0,z6,z7,z233,z8,z4])],[(0,[z165,z7,z71,z8,z4,z391]),(0,[z175,z7,z2,z8,z54,z5]),(0,[z0,z7,z2,z8,z336,z5]),(0,[z0,z7,z2,z717,z4,z5]),(0,[z0,z7,z906,z8,z4,z5])],[(0,[z0,z7,z2,z8,z907,z5]),(0,[z159,z7,z2,z13,z80,z5]),(0,[z0,z456,z2,z8,z4,z124]),(0,[z0,z7,z2,z8,z908,z5]),(0,[z0,z7,z909,z2,z8,z5]),(0,[z0,z7,z23,z114,z5,z62]),(0,[z0,z7,z23,z2,z5,z462]),(0,[z0,z7,z2,z4,z787,z5])]],
   [[(0,[z0,z7,z2,z8,z4,z195]),(0,[z0,z7,z2,z8,z910,z5]),(0,[z197,z0,z230,z8,z4,z5]),(0,[z0,z7,z2,z8,z911,z5]),(0,[z0,z2,z8,z774,z58,z5])],[(0,[z0,z7,z882,z2,z8,z5]),(0,[z197,z0,z230,z13,z8,z5]),(0,[z0,z1,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z912,z5])],[(0,[z0,z7,z2,z913,z4,z5]),(0,[z0,z378,z7,z23,z2,z5]),(0,[z0,z7,z23,z2,z272,z5])],[(0,[z0,z204,z7,z23,z2,z8]),(0,[z133,z7,z2,z13,z81,z5]),(0,[z147,z7,z2,z8,z54,z5]),(0,[z0,z7,z221,z2,z58,z5]),(0,[z0,z7,z2,z8,z4,z808])],[(0,[z0,z7,z2,z13,z141,z5]),(0,[z0,z7,z2,z914,z4,z5]),(0,[z0,z7,z23,z2,z95,z62])],[(0,[z0,z7,z2,z915,z8,z5]),(0,[z0,z7,z2,z916,z8,z5])],[(0,[z0,z204,z7,z2,z8,z4]),(0,[z0,z2,z8,z917,z4,z5]),(0,[z0,z7,z2,z8,z918,z5])],[(0,[z0,z7,z2,z8,z4,z919]),(0,[z0,z7,z131,z8,z779,z5]),(0,[z0,z7,z413,z61,z8,z5]),(0,[z0,z7,z2,z884,z5,z62])]],
   [[(0,[z0,z7,z340,z8,z4,z88]),(0,[z133,z7,z2,z446,z81,z5]),(0,[z0,z7,z2,z85,z118,z5]),(0,[z0,z7,z23,z2,z681,z5]),(0,[z0,z257,z7,z2,z684,z4])],[(0,[z0,z7,z23,z140,z2,z5]),(0,[z0,z257,z7,z23,z59,z2]),(0,[z86,z7,z467,z2,z8,z5])],[(0,[z0,z7,z468,z8,z4,z88]),(0,[z119,z7,z23,z2,z8,z94]),(0,[z0,z7,z2,z8,z920,z5])],[(0,[z0,z7,z2,z8,z921,z5]),(0,[z0,z7,z2,z8,z4,z922]),(0,[z0,z7,z2,z8,z294,z5]),(0,[z0,z7,z2,z57,z4,z5])],[(0,[z0,z7,z2,z360,z97,z5]),(0,[z0,z7,z2,z4,z923,z5]),(0,[z0,z7,z2,z13,z408,z5]),(0,[z0,z20,z515,z2,z8,z4])],[(0,[z0,z7,z2,z8,z153,z214]),(0,[z165,z7,z71,z8,z4,z5]),(0,[z0,z7,z924,z8,z4,z5]),(0,[z0,z7,z925,z2,z8,z5]),(0,[z0,z20,z2,z8,z116,z9]),(0,[z0,z7,z59,z2,z8,z142])],[(0,[z87,z182,z2,z8,z4,z5]),(0,[z165,z7,z71,z13,z8,z5]),(0,[z0,z7,z2,z8,z18,z470]),(0,[z0,z143,z7,z221,z332,z5])],[(0,[z0,z7,z2,z926,z4,z5])]],
   [[(0,[z49,z0,z7,z8,z4,z399]),(0,[z0,z7,z2,z8,z927,z5]),(0,[z0,z7,z2,z928,z4,z5]),(0,[z0,z7,z2,z8,z368,z5]),(0,[z0,z7,z23,z24,z2,z5]),(0,[z0,z7,z2,z8,z47,z795])],[(0,[z0,z7,z929,z8,z4,z5]),(0,[z0,z7,z2,z446,z408,z5]),(0,[z0,z7,z2,z930,z4,z5]),(0,[z0,z7,z2,z13,z213,z5]),(0,[z0,z7,z2,z8,z4,z758]),(0,[z0,z199,z7,z23,z148,z5]),(0,[z0,z7,z2,z8,z931,z5])],[(0,[z0,z7,z2,z141,z4,z214]),(0,[z147,z7,z2,z80,z4,z5]),(0,[z0,z7,z140,z2,z54,z5]),(0,[z335,z603,z7,z2,z8,z4]),(0,[z0,z7,z23,z2,z760,z5])],[(0,[z0,z7,z23,z468,z8,z5]),(0,[z165,z7,z23,z71,z8,z5]),(0,[z0,z7,z23,z2,z498,z5]),(0,[z197,z0,z7,z806,z2,z5]),(0,[z0,z82,z351,z2,z4,z5]),(0,[z0,z20,z2,z8,z142,z9])],[(0,[z0,z7,z2,z932,z4,z5]),(0,[z0,z933,z2,z8,z4,z5]),(0,[z934,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z935,z5]),(0,[z0,z7,z23,z114,z2,z5])],[(0,[z0,z7,z936,z8,z4,z5]),(0,[z87,z937,z2,z8,z4,z5]),(0,[z119,z510,z7,z2,z8,z4])],[(0,[z0,z7,z23,z2,z55,z5]),(0,[z0,z143,z7,z8,z332,z5]),(0,[z0,z7,z8,z4,z786,z5])],[(0,[z0,z7,z2,z8,z4,z938]),(0,[z0,z7,z939,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z940]),(0,[z0,z7,z2,z8,z941,z5]),(0,[z0,z7,z23,z695,z2,z5]),(0,[z0,z644,z7,z23,z2,z5]),(0,[z0,z199,z7,z210,z2,z5])]],
   [[(0,[z0,z7,z340,z8,z153,z5]),(0,[z0,z942,z7,z2,z8,z4]),(0,[z0,z82,z23,z2,z12,z5])],[(0,[z7,z937,z2,z8,z4,z5]),(0,[z0,z7,z2,z943,z4,z5]),(0,[z0,z7,z2,z104,z85,z5]),(0,[z0,z7,z2,z8,z944,z5]),(0,[z0,z816,z23,z2,z8,z5])],[(0,[z0,z7,z468,z8,z153,z5]),(0,[z945,z7,z2,z8,z4,z5]),(0,[z0,z14,z7,z2,z8,z109]),(0,[z0,z7,z23,z2,z42,z5]),(0,[z0,z7,z2,z946,z4,z5]),(0,[z0,z257,z7,z23,z2,z5])],[(0,[z7,z2,z8,z874,z4,z5]),(0,[z0,z947,z2,z8,z4,z5]),(0,[z49,z0,z7,z583,z8,z4]),(0,[z0,z257,z7,z114,z8,z4])],[(0,[z0,z7,z2,z948,z4,z5]),(0,[z0,z7,z23,z2,z677,z5])],[(0,[z0,z7,z340,z141,z4,z5]),(0,[z0,z7,z2,z8,z949,z5]),(0,[z0,z7,z2,z950,z8,z5])],[(0,[z0,z7,z951,z8,z4,z5]),(0,[z0,z198,z768,z8,z4,z5]),(0,[z0,z6,z2,z13,z8,z124]),(0,[z0,z952,z7,z2,z8,z4])],[(0,[z0,z7,z468,z141,z4,z5]),(0,[z0,z7,z2,z8,z4,z953]),(0,[z0,z7,z954,z2,z8,z5]),(0,[z0,z7,z71,z8,z4,z195]),(0,[z0,z7,z2,z8,z955,z5]),(0,[z90,z0,z7,z23,z2,z5]),(0,[z49,z0,z7,z8,z4,z50])]],
   [[(0,[z0,z7,z2,z4,z956,z5]),(0,[z0,z7,z23,z2,z85,z5])],[(0,[z0,z7,z2,z360,z4,z88]),(0,[z0,z2,z8,z4,z957,z5]),(0,[z0,z958,z2,z8,z4,z5])],[(0,[z0,z7,z2,z959,z4,z5]),(0,[z0,z7,z2,z8,z4,z960]),(0,[z0,z961,z2,z8,z4,z5]),(0,[z0,z7,z2,z8,z962,z5]),(0,[z197,z0,z138,z230,z8,z4]),(0,[z0,z7,z23,z2,z138,z8]),(0,[z0,z7,z2,z8,z963,z5])],[(0,[z0,z7,z2,z877,z8,z5]),(1,[z0,z2,z813,z4,z5]),(0,[z0,z964,z23,z2,z8,z5]),(0,[z0,z7,z2,z8,z787,z5]),(0,[z0,z7,z95,z4,z69,z62])],[(0,[z0,z7,z2,z8,z4,z214]),(0,[z0,z7,z965,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z88]),(0,[z0,z685,z7,z23,z2,z5]),(0,[z0,z232,z7,z23,z2,z5]),(0,[z0,z7,z966,z2,z8,z5]),(0,[z53,z7,z2,z85,z54,z5]),(0,[z335,z7,z2,z8,z4,z137]),(0,[z613,z7,z2,z8,z4,z137]),(0,[z0,z7,z2,z57,z368,z5])],[(0,[z0,z7,z2,z13,z8,z214]),(0,[z0,z7,z2,z967,z4,z5]),(0,[z0,z7,z2,z968,z4,z5]),(0,[z0,z7,z2,z8,z4,z969]),(0,[z970,z7,z2,z8,z4,z5]),(0,[z0,z7,z24,z4,z531,z5])],[(0,[z0,z7,z2,z971,z4,z5]),(0,[z133,z7,z2,z874,z4,z5]),(0,[z0,z7,z2,z972,z8,z5]),(0,[z0,z7,z2,z973,z8,z5]),(0,[z0,z199,z7,z8,z135,z4]),(0,[z0,z262,z7,z23,z2,z5])],[(0,[z0,z7,z23,z2,z5,z700]),(0,[z0,z7,z2,z974,z8,z5]),(0,[z0,z574,z7,z23,z2,z5]),(0,[z0,z7,z975,z2,z8,z5]),(0,[z0,z7,z2,z8,z976,z5]),(0,[z0,z7,z23,z2,z8,z709]),(1,[z0,z7,z2,z8,z795])]],
   [[(0,[z0,z7,z2,z8,z4,z977]),(0,[z0,z7,z2,z8,z4,z978]),(0,[z979,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z13,z360,z5]),(0,[z0,z7,z2,z8,z980,z5]),(0,[z0,z2,z8,z4,z981,z5]),(0,[z0,z7,z806,z2,z448,z5]),(0,[z0,z7,z982,z2,z8,z5]),(0,[z0,z7,z2,z8,z983,z5])],[(0,[z0,z7,z2,z8,z984,z5]),(0,[z0,z7,z2,z985,z8,z4]),(0,[z0,z486,z7,z59,z8,z4]),(0,[z0,z7,z61,z8,z19,z5]),(0,[z0,z443,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z38,z75])],[(0,[z0,z7,z23,z2,z535,z5])],[(0,[z7,z2,z80,z874,z4,z5]),(0,[z0,z7,z504,z2,z13,z5])],[(0,[z0,z7,z140,z2,z13,z5]),(0,[z0,z7,z986,z8,z4,z5]),(0,[z0,z7,z13,z8,z69,z5])],[(0,[z0,z524,z7,z23,z2,z5]),(0,[z0,z987,z2,z8,z4,z5]),(0,[z0,z697,z7,z23,z2,z5]),(0,[z0,z988,z2,z8,z4,z5]),(0,[z49,z0,z7,z8,z4,z786])],[(0,[z0,z199,z7,z601,z4,z5]),(0,[z0,z7,z24,z134,z25,z5])]],
   [[(0,[z0,z7,z340,z13,z8,z5]),(0,[z0,z7,z8,z4,z989,z5]),(0,[z0,z7,z990,z2,z4,z5]),(0,[z0,z7,z2,z8,z448,z5]),(0,[z0,z7,z2,z8,z4,z991]),(0,[z0,z7,z221,z2,z18,z5]),(0,[z0,z7,z23,z2,z560,z5]),(0,[z0,z7,z2,z106,z787,z5])],[(0,[z0,z7,z2,z360,z153,z5]),(0,[z0,z7,z992,z8,z4,z5]),(0,[z0,z937,z2,z8,z4,z5]),(0,[z0,z7,z993,z8,z4,z5]),(0,[z0,z7,z2,z8,z994,z5]),(0,[z0,z7,z23,z2,z567,z5]),(0,[z0,z79,z7,z2,z47,z550])],[(0,[z0,z7,z468,z13,z8,z5]),(0,[z0,z7,z8,z4,z995,z5]),(0,[z0,z7,z140,z2,z332,z5]),(0,[z0,z161,z7,z23,z2,z5]),(0,[z0,z7,z23,z670,z2,z5]),(0,[z0,z257,z7,z290,z2,z5])],[(0,[z0,z7,z2,z8,z4,z996]),(0,[z0,z7,z140,z2,z118,z5]),(0,[z0,z7,z2,z8,z38,z337])],[(0,[z277,z7,z467,z2,z8,z5]),(0,[z0,z198,z23,z238,z8,z5]),(0,[z0,z7,z997,z8,z4,z5]),(0,[z0,z20,z2,z13,z8,z9]),(0,[z0,z7,z114,z8,z4,z5]),(0,[z0,z7,z23,z2,z8,z741])],[(0,[z0,z7,z23,z2,z5,z572]),(0,[z0,z7,z765,z2,z8,z5]),(0,[z0,z7,z59,z438,z8,z4]),(0,[z0,z7,z23,z2,z576,z5]),(0,[z0,z143,z144,z7,z8,z332])],[(0,[z0,z7,z2,z915,z360,z5]),(0,[z0,z7,z2,z8,z4,z998]),(0,[z0,z7,z23,z2,z293,z5])],[(0,[z0,z7,z999,z2,z4,z5]),(0,[z0,z638,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z4,z1000])]],
   [[(0,[z0,z7,z2,z8,z4,z1001]),(0,[z0,z7,z2,z8,z1002,z5]),(0,[z0,z7,z2,z8,z1003,z5]),(0,[z0,z445,z7,z23,z2,z5]),(0,[z0,z7,z23,z2,z578,z5]),(0,[z0,z7,z2,z8,z78,z5]),(0,[z0,z7,z2,z13,z8,z1000])],[(0,[z0,z7,z2,z8,z1004,z5]),(0,[z0,z66,z7,z23,z2,z5]),(0,[z7,z23,z467,z2,z80,z5]),(0,[z197,z0,z230,z8,z448,z5]),(0,[z0,z199,z7,z23,z2,z5]),(0,[z0,z7,z23,z2,z8,z871]),(0,[z0,z7,z2,z13,z550,z5])],[(0,[z0,z7,z1005,z8,z4,z5]),(0,[z0,z386,z7,z2,z8,z47]),(0,[z0,z493,z7,z23,z2,z5])],[(0,[z0,z7,z2,z1006,z4,z5]),(0,[z0,z7,z2,z8,z1007,z5])],[(0,[z0,z7,z2,z8,z4,z1008]),(0,[z0,z7,z2,z8,z1009,z5]),(0,[z0,z7,z2,z8,z4,z1010]),(0,[z687,z0,z7,z23,z2,z5]),(0,[z0,z7,z23,z2,z5,z592]),(0,[z147,z7,z43,z2,z8,z5])],[(0,[z0,z7,z140,z2,z47,z5]),(0,[z0,z7,z2,z13,z8,z1010])],[(0,[z0,z7,z23,z2,z266,z5]),(0,[z0,z1011,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z1012,z4])],[(0,[z0,z7,z2,z8,z4,z1013]),(0,[z429,z7,z2,z8,z4,z94]),(0,[z7,z2,z8,z4,z5,z1014]),(0,[z418,z0,z7,z23,z2,z5]),(0,[z49,z0,z7,z23,z8,z50])]],
   [[(0,[z0,z7,z2,z1015,z8,z5]),(0,[z0,z7,z752,z8,z4,z5]),(0,[z0,z227,z7,z23,z2,z8]),(0,[z0,z7,z2,z8,z1016,z5]),(0,[z0,z7,z23,z2,z57,z5]),(0,[z0,z7,z24,z728,z4,z5]),(0,[z0,z143,z7,z8,z470,z332]),(0,[z0,z7,z2,z8,z795,z75])],[(0,[z0,z7,z2,z1017,z8,z5]),(0,[z0,z204,z7,z2,z13,z8]),(0,[z0,z488,z7,z23,z2,z5]),(0,[z0,z2,z3,z813,z4,z5]),(0,[z0,z7,z114,z106,z4,z5]),(0,[z0,z7,z2,z8,z795,z38])],[(0,[z0,z7,z452,z2,z8,z5]),(0,[z0,z7,z2,z8,z1018,z5]),(0,[z0,z7,z2,z13,z8,z1019])],[(0,[z64,z7,z76,z13,z8,z5]),(0,[z159,z7,z2,z874,z4,z5]),(0,[z0,z227,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z1020,z4]),(0,[z0,z7,z24,z13,z134,z5]),(0,[z0,z7,z114,z95,z4,z62])],[(0,[z0,z7,z530,z8,z332,z5])],[(0,[z0,z7,z1021,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z712]),(0,[z1022,z7,z2,z8,z4,z5]),(0,[z0,z7,z221,z2,z4,z470]),(0,[z0,z7,z8,z4,z1023,z5])],[(0,[z87,z182,z340,z8,z4,z5]),(0,[z0,z739,z2,z8,z4,z5]),(0,[z0,z82,z2,z27,z12,z5]),(0,[z0,z7,z2,z1024,z8,z4])],[(0,[z0,z7,z2,z8,z4,z1025]),(0,[z0,z7,z2,z8,z1026,z5]),(0,[z0,z7,z2,z1027,z4,z5]),(0,[z0,z7,z2,z8,z4,z1028]),(0,[z0,z7,z23,z2,z401,z5]),(0,[z333,z7,z2,z8,z118,z5]),(0,[z0,z7,z2,z8,z1029,z5]),(0,[z0,z1030,z7,z2,z8,z4])]],
   [[(0,[z87,z182,z468,z8,z4,z5]),(0,[z87,z168,z182,z2,z8,z4])],[(0,[z0,z263,z7,z23,z2,z5]),(0,[z0,z7,z134,z728,z4,z5]),(0,[z0,z7,z2,z95,z4,z62])],[(0,[z0,z7,z412,z13,z8,z5]),(0,[z0,z82,z7,z452,z2,z5]),(0,[z0,z1,z2,z13,z3,z5]),(0,[z0,z7,z2,z4,z77,z820])],[(0,[z0,z7,z1031,z8,z4,z5]),(0,[z0,z7,z768,z8,z4,z5]),(0,[z0,z199,z7,z23,z50,z5]),(0,[z0,z7,z2,z13,z8,z470]),(0,[z0,z7,z8,z4,z50,z786]),(0,[z0,z7,z23,z2,z1024,z8]),(0,[z0,z652,z7,z23,z2,z5])],[(0,[z0,z7,z2,z8,z1032,z5]),(0,[z0,z7,z1033,z2,z8,z5]),(0,[z0,z7,z2,z813,z4,z5]),(0,[z0,z7,z23,z2,z417,z5]),(0,[z0,z7,z59,z8,z4,z786]),(0,[z0,z304,z7,z2,z8,z112])],[],[(0,[z0,z7,z2,z1034,z8,z5]),(0,[z0,z2,z8,z4,z9,z758]),(0,[z0,z7,z23,z2,z5,z637]),(0,[z0,z7,z2,z4,z820,z5])],[(0,[z0,z1035,z7,z2,z8,z4]),(0,[z0,z7,z2,z8,z1036,z5]),(0,[z197,z0,z23,z230,z8,z5]),(0,[z0,z7,z2,z1037,z4,z5]),(0,[z0,z2,z8,z4,z758,z124]),(0,[z0,z7,z2,z8,z25,z5])]],
   [[],[(0,[z0,z7,z2,z8,z97,z88]),(0,[z0,z7,z1038,z2,z8,z5]),(0,[z0,z7,z2,z1039,z4,z5])],[(0,[z0,z7,z1040,z8,z4,z5]),(0,[z0,z7,z2,z8,z1041,z5]),(0,[z0,z7,z2,z8,z4,z1042]),(0,[z7,z2,z874,z81,z4,z5]),(0,[z0,z7,z23,z2,z645,z5])],[(0,[z0,z7,z2,z8,z1043,z5])],[(0,[z0,z7,z23,z2,z8,z195]),(0,[z277,z7,z2,z8,z118,z5]),(0,[z0,z7,z1044,z2,z8,z5]),(0,[z0,z7,z1045,z2,z4,z5]),(0,[z0,z20,z2,z8,z4,z758]),(0,[z762,z7,z2,z8,z4,z5]),(0,[z0,z7,z2,z13,z411,z5]),(0,[z0,z7,z2,z13,z787,z5])],[(0,[z0,z1046,z7,z2,z8,z4]),(0,[z1047,z7,z2,z8,z4,z5])],[(0,[z0,z7,z2,z8,z1048,z5]),(0,[z0,z7,z1049,z8,z4,z5]),(0,[z0,z79,z7,z509,z2,z5])],[(0,[z0,z257,z7,z23,z2,z127])]],
   [[(0,[z0,z686,z238,z8,z4,z5])],[(0,[z0,z7,z2,z8,z4,z775]),(0,[z335,z7,z2,z8,z4,z712]),(0,[z0,z7,z2,z8,z1050,z5]),(0,[z0,z7,z2,z8,z1051,z5]),(0,[z0,z6,z2,z8,z4,z758]),(0,[z0,z7,z1052,z2,z4,z5]),(0,[z0,z7,z2,z13,z430,z5])],[(0,[z0,z7,z2,z8,z1053,z5]),(0,[z0,z7,z1054,z8,z4,z5]),(0,[z0,z7,z23,z412,z8,z5]),(0,[z0,z7,z2,z8,z435,z5]),(0,[z0,z7,z2,z8,z1055,z5]),(0,[z0,z7,z2,z1056,z4,z5]),(0,[z1057,z7,z2,z8,z4,z5]),(0,[z0,z82,z2,z12,z4,z5]),(1,[z0,z7,z23,z114,z5])],[(0,[z0,z7,z2,z824,z8,z5]),(0,[z0,z7,z1058,z8,z4,z5]),(0,[z384,z0,z7,z23,z2,z5]),(0,[z0,z155,z2,z8,z774,z5]),(0,[z0,z257,z7,z23,z2,z112])],[(0,[z0,z7,z340,z8,z4,z214]),(0,[z0,z7,z2,z8,z4,z1059]),(0,[z0,z7,z2,z550,z4,z5])],[(0,[z0,z7,z2,z1060,z4,z5]),(0,[z297,z7,z76,z8,z4,z5]),(0,[z0,z7,z23,z2,z52,z5]),(0,[z0,z7,z23,z2,z193,z5]),(0,[z0,z7,z8,z74,z69,z5])],[],[(0,[z87,z182,z2,z360,z4,z5]),(0,[z7,z752,z76,z8,z4,z5]),(0,[z0,z279,z2,z8,z58,z5]),(0,[z0,z1,z2,z813,z4,z5]),(0,[z0,z649,z2,z8,z58,z5]),(0,[z0,z378,z2,z8,z58,z5]),(0,[z0,z7,z530,z113,z8,z5])]],
   [[(0,[z146,z7,z71,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z1061]),(0,[z0,z7,z2,z8,z1062,z5]),(0,[z0,z7,z2,z106,z368,z5]),(0,[z0,z6,z2,z8,z4,z124]),(0,[z0,z257,z7,z2,z4,z112])],[(0,[z0,z7,z23,z765,z2,z5]),(0,[z0,z7,z23,z221,z2,z5]),(0,[z0,z7,z23,z8,z69,z5])],[(0,[z937,z182,z2,z8,z4,z5]),(0,[z87,z182,z23,z2,z8,z5]),(0,[z0,z1063,z7,z2,z8,z4]),(0,[z0,z2,z8,z4,z1064,z5]),(0,[z0,z7,z2,z8,z1065,z5])],[(0,[z0,z7,z2,z8,z4,z1066]),(0,[z0,z7,z23,z2,z824,z5]),(0,[z197,z0,z230,z8,z435,z5]),(0,[z49,z0,z257,z7,z23,z2]),(0,[z0,z1067,z7,z23,z2,z8])],[(0,[z0,z7,z23,z2,z675,z5]),(0,[z0,z7,z2,z8,z109,z135]),(0,[z0,z793,z2,z8,z4,z5])],[(0,[z0,z7,z1068,z2,z4,z5]),(0,[z0,z7,z2,z8,z4,z1069]),(0,[z1070,z7,z2,z8,z4,z5]),(0,[z0,z91,z7,z23,z2,z5]),(0,[z0,z7,z8,z4,z1071,z5])],[(0,[z0,z82,z7,z23,z2,z5]),(0,[z0,z7,z23,z2,z8,z135]),(0,[z832,z7,z23,z2,z8,z5]),(0,[z0,z1067,z7,z2,z8,z4])],[(0,[z0,z7,z23,z24,z134,z5]),(0,[z0,z144,z7,z221,z2,z4])]],
   [[(0,[z0,z7,z8,z4,z786,z187])],[(0,[z0,z1072,z2,z8,z4,z5]),(0,[z0,z7,z1073,z8,z4,z5])],[(0,[z0,z7,z23,z2,z299,z5]),(0,[z0,z7,z23,z2,z601,z5]),(0,[z0,z7,z290,z2,z8,z5])],[(0,[z0,z7,z2,z8,z1074,z5]),(0,[z0,z7,z23,z2,z5,z705]),(0,[z0,z7,z2,z8,z4,z1075]),(0,[z0,z143,z7,z316,z332,z5]),(0,[z0,z7,z2,z8,z265,z75]),(0,[z0,z79,z7,z509,z2,z47])],[(0,[z0,z7,z1076,z2,z4,z5]),(0,[z0,z7,z2,z8,z4,z1077]),(0,[z0,z7,z2,z1078,z448,z5]),(0,[z0,z7,z2,z8,z1079,z5]),(0,[z0,z82,z23,z351,z2,z5]),(0,[z0,z173,z7,z23,z2,z5]),(0,[z0,z7,z140,z2,z38,z5]),(0,[z0,z7,z2,z1080,z4,z5])],[(0,[z0,z7,z23,z340,z8,z5]),(0,[z0,z7,z76,z138,z8,z4]),(0,[z0,z7,z2,z8,z1081,z5])],[(0,[z0,z6,z102,z2,z8,z4]),(0,[z0,z7,z23,z377,z2,z5]),(0,[z0,z7,z2,z95,z601,z4]),(0,[z0,z7,z2,z13,z95,z62])],[(0,[z0,z7,z1082,z8,z4,z5]),(1,[z0,z7,z744,z2,z5]),(0,[z0,z7,z131,z8,z264,z5])]],
   [[],[(0,[z0,z7,z2,z8,z4,z1083]),(0,[z0,z1,z2,z476,z4,z5]),(0,[z0,z2,z8,z4,z758,z5]),(0,[z0,z7,z210,z24,z2,z5]),(0,[z0,z7,z2,z4,z316,z470]),(0,[z0,z7,z1084,z2,z8,z5]),(0,[z0,z846,z23,z2,z8,z5]),(0,[z0,z7,z509,z2,z4,z5]),(0,[z0,z7,z2,z8,z578,z5])],[(0,[z0,z7,z340,z8,z4,z5]),(0,[z0,z7,z2,z8,z4,z1085]),(0,[z277,z7,z2,z8,z725,z5]),(0,[z0,z7,z23,z2,z703,z5]),(0,[z0,z7,z2,z8,z1086,z5]),(0,[z0,z79,z7,z2,z8,z30]),(0,[z0,z7,z23,z2,z31,z5])],[(0,[z119,z7,z2,z8,z4,z94]),(0,[z0,z7,z2,z8,z1087,z5])],[(0,[z0,z7,z468,z8,z4,z5]),(0,[z0,z7,z1088,z2,z4,z5]),(0,[z0,z7,z2,z4,z1089,z5]),(0,[z674,z7,z2,z8,z118,z5]),(0,[z119,z7,z2,z13,z8,z94]),(0,[z0,z7,z23,z530,z2,z5]),(0,[z0,z7,z23,z2,z884,z5]),(0,[z0,z7,z2,z475,z8,z100])],[(0,[z0,z7,z8,z4,z69,z5]),(0,[z0,z958,z23,z2,z8,z5]),(0,[z0,z257,z7,z290,z2,z77])],[(0,[z0,z7,z2,z8,z153,z88]),(0,[z0,z647,z7,z23,z2,z5]),(0,[z335,z7,z412,z8,z4,z137]),(0,[z0,z7,z2,z1078,z4,z5]),(0,[z0,z7,z2,z8,z1090,z5]),(0,[z0,z20,z2,z8,z4,z9]),(0,[z0,z7,z24,z134,z42,z5])],[(0,[z0,z7,z2,z8,z1091,z5]),(0,[z0,z7,z2,z787,z96,z5]),(0,[z0,z7,z509,z2,z5,z75])]],
   [[(0,[z335,z7,z23,z2,z8,z137]),(0,[z0,z7,z59,z8,z4,z132]),(0,[z0,z7,z23,z509,z2,z5])],[(0,[z0,z7,z2,z1092,z4,z5]),(0,[z641,z0,z230,z8,z4,z5]),(0,[z0,z7,z2,z8,z1093,z5])],[(0,[z197,z0,z227,z230,z8,z4]),(0,[z0,z199,z7,z23,z61,z5])],[(0,[z0,z7,z2,z141,z4,z88])],[(0,[z0,z7,z1094,z2,z8,z5]),(0,[z0,z7,z134,z4,z31,z5]),(0,[z0,z7,z2,z1095,z4,z5]),(0,[z0,z7,z59,z60,z8,z4]),(0,[z0,z405,z7,z8,z264,z5])],[(0,[z0,z7,z2,z8,z1096,z5]),(0,[z0,z7,z8,z4,z1097,z5]),(0,[z0,z160,z7,z140,z2,z5]),(0,[z0,z7,z565,z8,z19,z5]),(0,[z0,z7,z23,z2,z586,z5]),(0,[z0,z269,z7,z23,z2,z5]),(0,[z0,z7,z2,z8,z38,z619]),(0,[z0,z7,z2,z1098,z8,z5])],[(0,[z0,z7,z1099,z2,z8,z5]),(0,[z0,z7,z2,z138,z13,z8]),(0,[z0,z227,z7,z2,z13,z8]),(0,[z0,z238,z768,z8,z4,z5]),(0,[z0,z2,z813,z12,z4,z5]),(0,[z0,z7,z23,z2,z8,z872])],[(0,[z0,z7,z2,z1100,z4,z5]),(0,[z0,z7,z23,z2,z8,z391]),(0,[z0,z7,z1101,z8,z4,z5]),(0,[z0,z7,z2,z8,z1102,z5])]],
   [[(0,[z0,z7,z2,z8,z4,z1103]),(0,[z0,z7,z2,z760,z8,z5])],[(0,[z0,z1104,z7,z2,z8,z4]),(0,[z7,z2,z8,z4,z137,z712]),(0,[z0,z199,z14,z7,z36,z4]),(0,[z0,z7,z23,z2,z96,z5]),(0,[z0,z79,z7,z2,z8,z47])],[(0,[z0,z7,z2,z1105,z4,z5]),(0,[z0,z7,z2,z1106,z4,z5]),(0,[z0,z82,z2,z13,z12,z5]),(0,[z288,z0,z7,z148,z8,z5])],[(0,[z0,z432,z7,z23,z2,z5]),(0,[z49,z0,z7,z167,z8,z4]),(0,[z0,z7,z23,z2,z316,z5]),(0,[z0,z7,z2,z8,z74,z5])],[(0,[z147,z7,z23,z2,z80,z5]),(0,[z0,z7,z2,z8,z4,z1019]),(0,[z0,z7,z1107,z2,z8,z5])],[(0,[z0,z7,z2,z8,z1108,z5]),(0,[z64,z7,z76,z8,z4,z5]),(0,[z0,z7,z2,z1109,z4,z5]),(0,[z0,z7,z2,z8,z1110,z5]),(0,[z0,z7,z2,z8,z1111,z5]),(0,[z0,z7,z2,z8,z1112,z5]),(0,[z0,z7,z2,z8,z4,z845]),(1,[z0,z7,z2,z4,z820])],[(0,[z0,z7,z2,z8,z1113,z4]),(0,[z0,z1114,z2,z8,z4,z5]),(0,[z0,z7,z2,z85,z4,z5]),(0,[z0,z7,z2,z138,z8,z4])],[(0,[z0,z7,z23,z311,z2,z5]),(0,[z0,z7,z2,z874,z4,z5]),(0,[z0,z7,z23,z2,z314,z5]),(0,[z0,z7,z134,z8,z135,z4]),(0,[z0,z7,z2,z4,z1115,z5]),(0,[z0,z7,z1116,z2,z8,z5]),(0,[z0,z7,z23,z2,z5,z100])]],
   [[(0,[z159,z7,z2,z80,z201,z5]),(0,[z0,z7,z2,z8,z1117,z5]),(0,[z0,z7,z23,z2,z5,z120]),(0,[z0,z7,z23,z2,z122,z5]),(0,[z0,z7,z221,z131,z2,z5]),(0,[z0,z7,z23,z585,z2,z5])],[(0,[z0,z7,z23,z2,z104,z5])],[(0,[z0,z7,z2,z8,z1118,z5]),(0,[z0,z7,z2,z13,z85,z5]),(0,[z0,z7,z2,z1119,z4,z5]),(0,[z0,z155,z7,z140,z2,z5])],[(0,[z0,z7,z2,z360,z4,z5]),(0,[z0,z7,z2,z141,z153,z5]),(0,[z0,z7,z1120,z2,z8,z5]),(0,[z0,z7,z2,z8,z1121,z5])],[(0,[z0,z7,z412,z8,z4,z5]),(0,[z119,z7,z2,z8,z4,z712]),(0,[z0,z7,z2,z1122,z4,z5]),(0,[z0,z7,z2,z8,z1123,z5]),(0,[z0,z964,z2,z8,z4,z5]),(0,[z0,z7,z114,z95,z8,z4])],[(0,[z0,z7,z452,z2,z80,z5]),(0,[z0,z536,z2,z8,z4,z9]),(0,[z0,z7,z2,z1124,z8,z5]),(0,[z0,z7,z140,z2,z19,z5]),(0,[z0,z7,z8,z4,z1125,z5]),(0,[z0,z7,z23,z2,z223,z5]),(0,[z0,z7,z2,z8,z4,z470])],[(0,[z0,z7,z23,z2,z8,z5]),(0,[z0,z7,z2,z13,z8,z88]),(0,[z0,z7,z2,z8,z4,z1126]),(0,[z428,z7,z2,z8,z4,z94]),(0,[z0,z612,z7,z23,z2,z5])],[(0,[z87,z182,z2,z8,z97,z5]),(0,[z0,z7,z23,z233,z8,z5]),(0,[z0,z7,z2,z8,z1127,z5]),(0,[z0,z7,z2,z13,z8,z1126])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 530) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 530).take 529) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1059).take 127) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1186)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [530, 529, 127] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 238).take 18).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 121, 18] = true :=
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

end PEqualNP.Outside.L_meta_42872

theorem PEqualNP.Outside.L_meta_42872 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4003520672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4003520672) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42872.solve