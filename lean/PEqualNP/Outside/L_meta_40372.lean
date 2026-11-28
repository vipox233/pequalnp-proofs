import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40372

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4276669632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1002cc71c0c6ecc8#64 ++ 0x21002cc71c0c6ecc#64 ++ 0xf04fdcf3c1cfecc7#64 ++ 0xdf04fdcf3c1cfecc#64 : BitVec 256),
   (0x0096051402114550#64 ++ 0x4009605140211455#64 ++ 0x71b6271c0631ffff#64 ++ 0xb71b6271c0631fff#64 : BitVec 256),
   (0x0628380ad82a30a2#64 ++ 0x80628380ad82a30a#64 ++ 0x9e38381ff83e30ff#64 ++ 0x79e38381ff83e30f#64 : BitVec 256),
   (0x0b403aa06d403a03#64 ++ 0x00b403aa06d403a0#64 ++ 0xefc03fe07fc03f0e#64 ++ 0xfefc03fe07fc03f0#64 : BitVec 256),
   (0x2dfd400037bd800c#64 ++ 0x02dfd400037bd800#64 ++ 0xbfffc0007fffc00d#64 ++ 0xfbfffc0007fffc00#64 : BitVec 256),
   (0x4fffb7df00000000#64 ++ 0x04fffb7df0000000#64 ++ 0x4fffffff80000003#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0096051402114550 0x4009605140211455 0x71b6271c0631ffff 0xb71b6271c0631fff

def z1 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38381ff83e30ff 0x79e38381ff83e30f

def z2 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc03fe07fc03f0e 0xfefc03fe07fc03f0

def z3 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04fdcf3c1cfecc7 0xdf04fdcf3c1cfecc

def z4 : W := mkw 0x1096cd75c2d7edd8 0x61096cd75c2d7edd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z5 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffc0007fffc00d 0xfbfffc0007fffc00

def z6 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e49d8e380000000 0x40e49d8e38000000

def z7 : W := mkw 0x4fffb7df00004550 0x44fffb7df0000455 0x4fffffff80003ff3 0xf4fffffff80003ff

def z8 : W := mkw 0x4202b7df00004550 0x44202b7df0000455 0x40003fff80003ff2 0x040003fff80003ff

def z9 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x7fffffff8631ffff 0xf7fffffff8631fff

def z10 : W := mkw 0x0940400025848008 0x0094040002584800 0xbfcfc0007fcfc00d 0xfbfcfc0007fcfc00

def z11 : W := mkw 0x1b42fef1edc6fecb 0x21b42fef1edc6fec 0xffcffff3ffcfffcf 0xfffcffff3ffcfffc

def z12 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffff80000003 0xf4fffffff8000000

def z13 : W := mkw 0x0002845100000000 0x0000284510000000 0x404fdcf380000003 0xd404fdcf38000000

def z14 : W := mkw 0x10028c71c0426cc0 0x210028c71c0426cc 0x40001cf380002cc2 0x040001cf380002cc

def z15 : W := mkw 0x0dfd000000000000 0x00dfd00000000000 0x0fb0000000000000 0x20fb000000000000

def z16 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffe01c7ffff0ff 0xfbfffe01c7ffff0f

def z17 : W := mkw 0x0628300a00000000 0x00628300a0000000 0x0e08180380000000 0x40e0818038000000

def z18 : W := mkw 0x0002051400004550 0x4000205140000455 0x0000001c000000f0 0x00000001c000000f

def z19 : W := mkw 0x0b4032802d001203 0x00b4032802d00120 0x0f8023003e001308 0x20f8023003e00130

def z20 : W := mkw 0x4fffb7df2d001203 0x04fffb7df2d00120 0x4fffffffbe00130b 0xf4fffffffbe00130

def z21 : W := mkw 0x59d7c7f500c4cc48 0x259d7c7f500c4cc4 0x61c7c7e001c1cc00 0x861c7c7e001c1cc0

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030201c00000003 0x30030201c0000000

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x6180270006003f0e 0xb6180270006003f0

def z24 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x0e7fd8ff80000001 0x40e7fd8ff8000000

def z25 : W := mkw 0x0000400000848008 0x0000040000084800 0xb04fc00041cfc005 0xdb04fc00041cfc00

def z26 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x1038001f803e00f1 0x01038001f803e00f

def z27 : W := mkw 0x29d5000027110004 0x029d500002711000 0x0180000006000000 0x0018000000600000

def z28 : W := mkw 0x0628300a982a10a2 0x80628300a982a10a 0x1e38201fb83e10f9 0x21e38201fb83e10f

def z29 : W := mkw 0x1202bef1c8427ec3 0x21202bef1c8427ec 0x40003ff380003fc2 0x040003ff380003fc

def z30 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb000000041cfecc4 0x0b000000041cfecc

def z31 : W := mkw 0x1b407aa0edc6fecb 0x21b407aa0edc6fec 0xffc03fe07fcfffce 0xfffc03fe07fcfffc

def z32 : W := mkw 0x0200380048003002 0x0020038004800300 0x8e00180078000000 0x48e0018007800000

def z33 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x1038201f803e30ff 0x31038201f803e30f

def z34 : W := mkw 0x0002051400004550 0x4000205140000455 0x4000271c00003ff2 0x04000271c00003ff

def z35 : W := mkw 0x1002c47100c4cc48 0x21002c47100c4cc4 0x6047c4e001c1cc00 0x86047c4e001c1cc0

def z36 : W := mkw 0x29d540002795800c 0x029d540002795800 0x21c7c00007c1c000 0x821c7c00007c1c00

def z37 : W := mkw 0x0094010402110110 0x4009401040211011 0x11b0231c063033ff 0x311b0231c063033f

def z38 : W := mkw 0x24bd400012bd800c 0x024bd400012bd800 0xb07fc00041ffc005 0xdb07fc00041ffc00

def z39 : W := mkw 0x06be3d1eda3b75f2 0xc06be3d1eda3b75f 0xffbe3f1ffe3fffff 0xfffbe3f1ffe3ffff

def z40 : W := mkw 0x10028c71c0426cc0 0x210028c71c0426cc 0x70061cf38001ecc7 0x970061cf38001ecc

def z41 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e38381ff80e0003 0x78e38381ff80e000

def z42 : W := mkw 0x0000080040002000 0x0000008004000200 0x8000180040002006 0x5800018004000200

def z43 : W := mkw 0x2dffc45137bd800c 0x02dffc45137bd800 0xffffdcf3ffffc00f 0xfffffdcf3ffffc00

def z44 : W := mkw 0x0002c45100848008 0x00002c4510084800 0xf04fdcf3c1cfc007 0xdf04fdcf3c1cfc00

def z45 : W := mkw 0x6ffd338e37390004 0x06ffd338e3739000 0x0fb0230c3e300008 0x20fb0230c3e30000

def z46 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x8ff9c0007ffe0008 0x68ff9c0007ffe000

def z47 : W := mkw 0x2dff451437bdc55c 0x42dff451437bdc55 0xffffe71c7fffffff 0xfffffe71c7ffffff

def z48 : W := mkw 0x0f683aaafd6a3aa3 0x80f683aaafd6a3aa 0xfff83ffffffe3fff 0xffff83ffffffe3ff

def z49 : W := mkw 0x00000800d82a30a2 0x800000800d82a30a 0x90000000783e30fc 0x090000000783e30f

def z50 : W := mkw 0x49d787d500000000 0x049d787d50000000 0x41c7c7e000000000 0x841c7c7e00000000

def z51 : W := mkw 0x0096855502114550 0x4009685550211455 0x71ffffff8631ffff 0xf71ffffff8631fff

def z52 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e30200c783e30fc 0x29e30200c783e30f

def z53 : W := mkw 0x3002cc71f7ffeccc 0x23002cc71f7ffecc 0xf04fdcf3ffffeccf 0xdf04fdcf3ffffecc

def z54 : W := mkw 0x1002c47100c4cc48 0x21002c47100c4cc4 0x7047c4f001c1ecc7 0x97047c4f001c1ecc

def z55 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0x904fd8f3c1cfc0c1 0x4904fd8f3c1cfc0c

def z56 : W := mkw 0x44bf855f00000000 0x044bf855f0000000 0x003fc01f80000001 0x0003fc01f8000000

def z57 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0x61c007e007c00f00 0x861c007e007c00f0

def z58 : W := mkw 0x4002855f00000000 0x04002855f0000000 0x0000001f80000000 0x00000001f8000000

def z59 : W := mkw 0x0f68328a00000000 0x00f68328a0000000 0x4ff83fff80000003 0xf4ff83fff8000000

def z60 : W := mkw 0x44bd010e00000000 0x044bd010e0000000 0x0030000c00000000 0x00030000c0000000

def z61 : W := mkw 0x5fffffffc0c6ecc8 0x25fffffffc0c6ecc 0xffffffffc1cfecc7 0xfffffffffc1cfecc

def z62 : W := mkw 0x29d540002795800c 0x029d540002795800 0x31f7c00007f1c00d 0xb31f7c00007f1c00

def z63 : W := mkw 0x4fffbfdfd82a30a2 0x84fffbfdfd82a30a 0xdffffffff83e30ff 0xfdffffffff83e30f

def z64 : W := mkw 0x5fffbfffc0426cc0 0x25fffbfffc0426cc 0x4fffffff80002cc3 0xf4fffffff80002cc

def z65 : W := mkw 0x0dfd400000848008 0x00dfd40000084800 0xbfffc00041cfc005 0xfbfffc00041cfc00

def z66 : W := mkw 0x1000c04180868088 0x21000c0418086808 0x0009c003800e0000 0x00009c003800e000

def z67 : W := mkw 0x0b4032a02d401a03 0x00b4032a02d401a0 0x6fc027e03fc01f08 0xa6fc027e03fc01f0

def z68 : W := mkw 0x00000800c80230a2 0x800000800c80230a 0x00000000000030f0 0x000000000000030f

def z69 : W := mkw 0x1002c4518086c4c8 0x21002c4518086c4c 0x100fc013800fc0c1 0x0100fc013800fc0c

def z70 : W := mkw 0x0428000010280000 0x0042800001028000 0x10380000003e0001 0x010380000003e000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008181380000003 0x5000818138000000

def z72 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z73 : W := mkw 0x5fffffffc0c6a888 0x25fffffffc0c6a88 0xcfffffffc1ce0003 0xfcfffffffc1ce000

def z74 : W := mkw 0x1b42fef16dc4fe4b 0x21b42fef16dc4fe4 0xefc7ffe07fc1ff0e 0xfefc7ffe07fc1ff0

def z75 : W := mkw 0x02003aa048403a03 0x002003aa048403a0 0x40003fe000003f02 0x040003fe000003f0

def z76 : W := mkw 0x24bd400012bd800c 0x024bd400012bd800 0x103fc000003fc001 0x0103fc000003fc00

def z77 : W := mkw 0x6ffff7df12bd800c 0x06ffff7df12bd800 0x5fffffff803fc003 0xf5fffffff803fc00

def z78 : W := mkw 0x0000082040402800 0x0000008204040280 0xe1c03fe047c03f0e 0xfe1c03fe047c03f0

def z79 : W := mkw 0x0200380048003002 0x0020038004800300 0x8e0038007800300e 0x78e0038007800300

def z80 : W := mkw 0x1202bc7bc8427ce2 0xa1202bc7bc8427ce 0x40003cff80003cf2 0x040003cff80003cf

def z81 : W := mkw 0x2dfd000037390004 0x02dfd00003739000 0x0fb000003e300008 0x20fb000003e30000

def z82 : W := mkw 0x5202bfffc0426cc0 0x25202bfffc0426cc 0x40003fff80002cc2 0x040003fff80002cc

def z83 : W := mkw 0x4202b7df00000000 0x04202b7df0000000 0x40003fff80000002 0x040003fff8000000

def z84 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xffb83f1ffe3e3fff 0xfffb83f1ffe3e3ff

def z85 : W := mkw 0x0096051402114550 0x4009605140211455 0x1036001c0031c0f1 0x01036001c0031c0f

def z86 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x5fffffff8031c0f3 0xf5fffffff8031c0f

def z87 : W := mkw 0x162afc7bc0c6ecc8 0x2162afc7bc0c6ecc 0xfe7ffcffc1cfecc7 0xffe7ffcffc1cfecc

def z88 : W := mkw 0x0002041000004440 0x0000204100000444 0x700604100001ecc7 0x9700604100001ecc

def z89 : W := mkw 0x4ffdb3cf00000000 0x04ffdb3cf0000000 0x0ff9fbef80000000 0x60ff9fbef8000000

def z90 : W := mkw 0x29d745142795c55c 0x429d745142795c55 0x61c7c70007c1cf00 0x861c7c70007c1cf0

def z91 : W := mkw 0x0628380ada3b75f2 0xc0628380ada3b75f 0xbe38381ffe3fffff 0x7be38381ffe3ffff

def z92 : W := mkw 0x0628300a18281022 0x80628300a1828102 0x0e30200c38301038 0x20e30200c3830103

def z93 : W := mkw 0x0628300a10280000 0x00628300a1028000 0x9e38381ff83e000f 0x79e38381ff83e000

def z94 : W := mkw 0x0094000002110000 0x0009400000211000 0x31b600000631c00d 0xb31b600000631c00

def z95 : W := mkw 0x0000000002114550 0x4000000000211455 0x300000000631fffc 0x0300000000631fff

def z96 : W := mkw 0x4b42bfff6d403a03 0x04b42bfff6d403a0 0xefc03fffffc03f0e 0xfefc03fffffc03f0

def z97 : W := mkw 0x0094400002958008 0x0009440000295800 0xb1ffc00047ffc00d 0xfb1ffc00047ffc00

def z98 : W := mkw 0x09400aa06d403a03 0x009400aa06d403a0 0xe1c007e07fc03f0c 0x8e1c007e07fc03f0

def z99 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x9e38001ff83e00fd 0x79e38001ff83e00f

def z100 : W := mkw 0x4ffd3bae6d403a03 0x04ffd3bae6d403a0 0xeff03fec7fc03f0e 0xfeff03fec7fc03f0

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000010000020c7 0x110000010000020c

def z102 : W := mkw 0x0940000025000000 0x0094000002500000 0xafc000007fc0000c 0xfafc000007fc0000

def z103 : W := mkw 0x2dff051437394554 0x42dff05143739455 0x7fb6271c3e31ffff 0xb7fb6271c3e31fff

def z104 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x6fffffff86003f0f 0xf6fffffff86003f0

def z105 : W := mkw 0x0b4032802d001203 0x00b4032802d00120 0x0e00000038000000 0x00e0000003800000

def z106 : W := mkw 0x2dfd410437bd811c 0x42dfd410437bd811 0xbfffe30c7fffd33d 0xfbfffe30c7fffd33

def z107 : W := mkw 0x162afc7bd8eefcea 0xa162afc7bd8eefce 0xfe7ffcfff9fffcff 0xffe7ffcfff9fffcf

def z108 : W := mkw 0x0428000010280000 0x0042800001028000 0x9e380000783e000d 0x79e380000783e000

def z109 : W := mkw 0x1002cc71c0c6a888 0x21002cc71c0c6a88 0xc04fdcf3c1ce0003 0xdc04fdcf3c1ce000

def z110 : W := mkw 0x209540000295800c 0x0209540000295800 0x0007c0000001c000 0x00007c0000001c00

def z111 : W := mkw 0x2ffd780affbfb0ae 0x82ffd780affbfb0a 0xbffff81ffffff0ff 0xfbffff81ffffff0f

def z112 : W := mkw 0x4fffb7df25000000 0x04fffb7df2500000 0xefffffffffc0000f 0xfefffffffffc0000

def z113 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0x8e49c00079ce0000 0x48e49c00079ce000

def z114 : W := mkw 0x4dff87d500000000 0x04dff87d50000000 0x4fffc7e000000001 0xf4fffc7e00000000

def z115 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xaf8023007fc03f0c 0x2af8023007fc03f0

def z116 : W := mkw 0x4fff379e00000000 0x04fff379e0000000 0x4fb6271c00000003 0xb4fb6271c0000000

def z117 : W := mkw 0x0940000025000000 0x0094000002500000 0x8e40000079c00000 0x48e40000079c0000

def z118 : W := mkw 0x2000400037bdc55c 0x42000400037bdc55 0xb00000007ffffffc 0x0b00000007ffffff

def z119 : W := mkw 0x0000000002114550 0x4000000000211455 0x3030201c0631ffff 0x33030201c0631fff

def z120 : W := mkw 0x0b40328000000000 0x00b4032800000000 0x4fc03fe000000002 0xf4fc03fe00000000

def z121 : W := mkw 0x3dffcc71f7ffeccc 0x23dffcc71f7ffecc 0xffffdcf3ffffeccf 0xfffffdcf3ffffecc

def z122 : W := mkw 0x0428400010ac8008 0x00428400010ac800 0xbe7fc00079ffc00d 0xfbe7fc00079ffc00

def z123 : W := mkw 0x1096c5558297c5d8 0x61096c5558297c5d 0x71bfe71f863fffff 0xb71bfe71f863ffff

def z124 : W := mkw 0x49d787d502114550 0x449d787d50211455 0x71f7e7fc0631ffff 0xb71f7e7fc0631fff

def z125 : W := mkw 0x10004820edc6fecb 0x210004820edc6fec 0xb00000007fcfffcc 0x0b00000007fcfffc

def z126 : W := mkw 0x0628380058283002 0x0062838005828300 0x9e383800783e300f 0x79e383800783e300

def z127 : W := mkw 0x0dff845100000000 0x00dff84510000000 0x4fffdcf380000003 0xf4fffdcf38000000

def z128 : W := mkw 0x10000820c0426cc0 0x210000820c0426cc 0x0000000000002cc0 0x00000000000002cc

def z129 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fcfdfe380000000 0xc4fcfdfe38000000

def z130 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38181ff83e00f1 0x49e38181ff83e00f

def z131 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x8e4018e079c00000 0x48e4018e079c0000

def z132 : W := mkw 0x2bd57aa06fd5ba0f 0x02bd57aa06fd5ba0 0xefc7ffe07fc1ff0e 0xfefc7ffe07fc1ff0

def z133 : W := mkw 0x2000400012bd800c 0x02000400012bd800 0x10000000003fc000 0x010000000003fc00

def z134 : W := mkw 0x0000010400000110 0x4000001040000011 0x0000230c00001330 0x00000230c0000133

def z135 : W := mkw 0x0200380ac80230a2 0x80200380ac80230a 0x0000381f800030f2 0x00000381f800030f

def z136 : W := mkw 0x162afc5bd8aef4ea 0xa162afc5bd8aef4e 0x9e3ff81ff83ff0ff 0x79e3ff81ff83ff0f

def z137 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e081803f80e0000 0x48e081803f80e000

def z138 : W := mkw 0x10004820c0c6a888 0x210004820c0c6a88 0x8000000041ce0000 0x08000000041ce000

def z139 : W := mkw 0x4fffb7df02110000 0x04fffb7df0211000 0x7fffffff8631c00f 0xf7fffffff8631c00

def z140 : W := mkw 0x4fffb7df18281022 0x84fffb7df1828102 0x4fffffffb830103b 0xf4fffffffb830103

def z141 : W := mkw 0x5f69faebc0c6a888 0x25f69faebc0c6a88 0x8e49d8e3c1ce0000 0x48e49d8e3c1ce000

def z142 : W := mkw 0x0000000010280000 0x0000000001028000 0x90000000783e000c 0x090000000783e000

def z143 : W := mkw 0x0ffd300a00000000 0x00ffd300a0000000 0x0ffff81f80000003 0xf0ffff81f8000000

def z144 : W := mkw 0x2dfd4800ffbfb0ae 0x82dfd4800ffbfb0a 0xbfffc0007ffff0fd 0xfbfffc0007ffff0f

def z145 : W := mkw 0x2ffd7aa07ffdba0f 0x02ffd7aa07ffdba0 0xffffffe07fffff0f 0xfffffffe07fffff0

def z146 : W := mkw 0x0940000025000000 0x0094000002500000 0xefc027007fc03f0e 0xfefc027007fc03f0

def z147 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e081803f83e30fc 0x49e081803f83e30f

def z148 : W := mkw 0x494182c100000000 0x0494182c10000000 0x0041c0e000000000 0x00041c0e00000000

def z149 : W := mkw 0x0000000000000000 0x0000000000000000 0x71b0271c06303fff 0xb71b0271c06303ff

def z150 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fb03fff80000002 0x24fb03fff8000000

def z151 : W := mkw 0x0096051402114550 0x4009605140211455 0x618607000601cf00 0x8618607000601cf0

def z152 : W := mkw 0x1002847100404c40 0x21002847100404c4 0x400004e000000c00 0x0400004e000000c0

def z153 : W := mkw 0x1002c4518086c4c8 0x21002c4518086c4c 0x504fdcf3800fc0c3 0xd504fdcf3800fc0c

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x1030201c003030ff 0x31030201c003030f

def z155 : W := mkw 0x4ffd338e00000000 0x04ffd338e0000000 0x0fb0230c00000000 0x20fb0230c0000000

def z156 : W := mkw 0x0b403a806d003203 0x00b403a806d00320 0x8f803b007e00330e 0x78f803b007e00330

def z157 : W := mkw 0x6ffff7df37bd800c 0x06ffff7df37bd800 0xffffffffffffc00f 0xfffffffffffffc00

def z158 : W := mkw 0x0628300a18281022 0x80628300a1828102 0x0e00000038000000 0x00e0000003800000

def z159 : W := mkw 0x0b403aa06f517f53 0x40b403aa06f517f5 0xffc03fe07ff1fffe 0xfffc03fe07ff1fff

def z160 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb04fc00041cfecc5 0xdb04fc00041cfecc

def z161 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0xafc9c0007fce000c 0xfafc9c0007fce000

def z162 : W := mkw 0x2dfd42a037fd8a0d 0x02dfd42a037fd8a0 0xffffc7e07fffcf0d 0xfffffc7e07fffcf0

def z163 : W := mkw 0x0200300a08001022 0x80200300a0800102 0x0000200c00001030 0x00000200c0000103

def z164 : W := mkw 0x400287d500000000 0x0400287d50000000 0x400007e000000000 0x0400007e00000000

def z165 : W := mkw 0x6fffb7df37390004 0x06fffb7df3739000 0x4fffffffbe30000b 0xf4fffffffbe30000

def z166 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x5fffffff803030ff 0xf5fffffff803030f

def z167 : W := mkw 0x0628382ad86a38a2 0x80628382ad86a38a 0xfe783cfff9fe3cff 0xffe783cfff9fe3cf

def z168 : W := mkw 0x000008206d403a03 0x0000008206d403a0 0xa00000007fc03f0c 0x0a00000007fc03f0

def z169 : W := mkw 0x0628380ac80230a2 0x80628380ac80230a 0x0e38381f800030f3 0x70e38381f800030f

def z170 : W := mkw 0x0dfd000000000000 0x00dfd00000000000 0x0fffc00000000001 0xf0fffc0000000000

def z171 : W := mkw 0x00000800c0022080 0x000000800c002208 0x90081813c00e20c7 0x590081813c00e20c

def z172 : W := mkw 0x0f68380afd2a30a2 0x80f68380afd2a30a 0xbff8381ffffe30ff 0xfbff8381ffffe30f

def z173 : W := mkw 0x10004820c2d7edd8 0x610004820c2d7edd 0xb000000047fffffc 0x0b000000047fffff

def z174 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e083803f80e300e 0x78e083803f80e300

def z175 : W := mkw 0x0d69000000000000 0x00d6900000000000 0x0e49c00000000000 0x40e49c0000000000

def z176 : W := mkw 0x0b4038006d003002 0x00b4038006d00300 0xafc038007fc0300e 0xfafc038007fc0300

def z177 : W := mkw 0x0b40328025000000 0x00b4032802500000 0xefc03fe07fc0000e 0xfefc03fe07fc0000

def z178 : W := mkw 0x4fffbfdfd82a30a2 0x84fffbfdfd82a30a 0xcffffffff80e0003 0xfcffffffff80e000

def z179 : W := mkw 0x1002c47100c4cc48 0x21002c47100c4cc4 0xf04fc4e041cfcc05 0xdf04fc4e041cfcc0

def z180 : W := mkw 0x0002051400004550 0x4000205140000455 0x5030271c00303fff 0x35030271c00303ff

def z181 : W := mkw 0x26bd780adabfb0ae 0x826bd780adabfb0a 0x9e3ff81ff83ff0ff 0x79e3ff81ff83ff0f

def z182 : W := mkw 0x34bfc45192bfc4cc 0x234bfc45192bfc4c 0x103fc013803fc0c1 0x0103fc013803fc0c

def z183 : W := mkw 0x0000082040402800 0x0000008204040280 0x804018e041c00000 0x4804018e041c0000

def z184 : W := mkw 0x4f69328a00000000 0x04f69328a0000000 0x0e00000000000000 0x00e0000000000000

def z185 : W := mkw 0x0000002025400a01 0x00000002025400a0 0x2000000007c00f00 0x02000000007c00f0

def z186 : W := mkw 0x1096c57502d5cd58 0x61096c57502d5cd5 0x71f7e7fc07f1ffff 0xb71f7e7fc07f1fff

def z187 : W := mkw 0x0000082040402800 0x0000008204040280 0xe0401ce041c02c06 0xde0401ce041c02c0

def z188 : W := mkw 0x0bd63fb46f517f53 0x40bd63fb46f517f5 0xfff63ffc7ff1ffff 0xffff63ffc7ff1fff

def z189 : W := mkw 0x4bd7bff56d403a03 0x04bd7bff56d403a0 0xefc7ffe07fc03f0e 0xfefc7ffe07fc03f0

def z190 : W := mkw 0x100040008086c4c8 0x2100040008086c4c 0x10000000000fc0c0 0x010000000000fc0c

def z191 : W := mkw 0x06be351e00000000 0x006be351e0000000 0x4fbe3f1f80000003 0xf4fbe3f1f8000000

def z192 : W := mkw 0x09d607b427514f51 0x409d607b427514f5 0x71f627fc07f1ffff 0xb71f627fc07f1fff

def z193 : W := mkw 0x02023d1ec80275f2 0xc02023d1ec80275f 0x40003f1f80003ff2 0x040003f1f80003ff

def z194 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0x8049d8e3c1ce0000 0x48049d8e3c1ce000

def z195 : W := mkw 0x0628300a00000000 0x00628300a0000000 0x1e38381f803030ff 0x71e38381f803030f

def z196 : W := mkw 0x24bd400012bd800c 0x024bd400012bd800 0x9e3fc000783fc00d 0x79e3fc000783fc00

def z197 : W := mkw 0x1b42bef1ed427ec3 0x21b42bef1ed427ec 0xefc03ff3ffc03fce 0xfefc03ff3ffc03fc

def z198 : W := mkw 0x0002051400004550 0x4000205140000455 0x7006271c0001fff7 0x97006271c0001fff

def z199 : W := mkw 0x2ffd380aff3b30a6 0x82ffd380aff3b30a 0x9fb8381ffe3e30ff 0x79fb8381ffe3e30f

def z200 : W := mkw 0x0096855500000000 0x0009685550000000 0x41ffffff80000003 0xf41ffffff8000000

def z201 : W := mkw 0x0200380048003002 0x0020038004800300 0x9e30381c783030ff 0x79e30381c783030f

def z202 : W := mkw 0x4f6bb7df00000000 0x04f6bb7df0000000 0x4e49ffff80000002 0x44e49ffff8000000

def z203 : W := mkw 0x4f69bacbd82a30a2 0x84f69bacbd82a30a 0x8e49d8e3f80e0000 0x48e49d8e3f80e000

def z204 : W := mkw 0x06283aaad86a3aa3 0x806283aaad86a3aa 0xde383ffff83e3fff 0x7de383ffff83e3ff

def z205 : W := mkw 0x02003aa048403a03 0x002003aa048403a0 0x000018e000000000 0x0000018e00000000

def z206 : W := mkw 0x0094010402110110 0x4009401040211011 0x01b0230c06301338 0x201b0230c0630133

def z207 : W := mkw 0x0096051400000000 0x0009605140000000 0x41b6271c00000003 0xb41b6271c0000000

def z208 : W := mkw 0x0940028000000000 0x0094002800000000 0x41c007e000000000 0x841c007e00000000

def z209 : W := mkw 0x4202b7df00000000 0x04202b7df0000000 0x404fffff80000003 0xd404fffff8000000

def z210 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfb000007fffc00c 0x2bfb000007fffc00

def z211 : W := mkw 0x0000000000000000 0x0000000000000000 0x218000000600000c 0xb218000000600000

def z212 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e381803f83e000d 0x79e381803f83e000

def z213 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4ff7e7ec00000000 0xa4ff7e7ec0000000

def z214 : W := mkw 0x3ffffef1fffffecf 0x23ffffef1fffffec 0xfffffff3ffffffcf 0xffffffff3ffffffc

def z215 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xb00fc013c1cfecc5 0x0b00fc013c1cfecc

def z216 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc01fe07fc00f00 0xcefc01fe07fc00f0

def z217 : W := mkw 0x04bc000012390000 0x004bc00001239000 0xbfbe00007e3fc00d 0xfbfbe00007e3fc00

def z218 : W := mkw 0x4fffbfff6f517f53 0x44fffbfff6f517f5 0xfffffffffff1ffff 0xffffffffffff1fff

def z219 : W := mkw 0x44bf855f02114550 0x444bf855f0211455 0x103fc01f8031c0f1 0x0103fc01f8031c0f

def z220 : W := mkw 0x020038206d403a03 0x0020038206d403a0 0xae0038007fc03f0e 0x7ae0038007fc03f0

def z221 : W := mkw 0x4fff379e02114550 0x44fff379e0211455 0x7fb6271c0631ffff 0xb7fb6271c0631fff

def z222 : W := mkw 0x0096051400004550 0x4009605140000455 0x41b6271c00003ff3 0xb41b6271c00003ff

def z223 : W := mkw 0x0002051400000000 0x0000205140000000 0x4000271c00000002 0x04000271c0000000

def z224 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xae4018e07fc03f0c 0x4ae4018e07fc03f0

def z225 : W := mkw 0x0b4032a025400a01 0x00b4032a025400a0 0x6fc03fe007c00f02 0xf6fc03fe007c00f0

def z226 : W := mkw 0x0b40328000000000 0x00b4032800000000 0x0f80230000000000 0x20f8023000000000

def z227 : W := mkw 0x10964d34c2d7edd8 0x610964d34c2d7edd 0xf1b6271c47ffffff 0xbf1b6271c47fffff

def z228 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xffffe7007fffff0f 0xfffffe7007fffff0

def z229 : W := mkw 0x0b403aa0ed423a83 0x00b403aa0ed423a8 0xffc83ff3ffce3fcf 0xfffc83ff3ffce3fc

def z230 : W := mkw 0x0628300a18281022 0x80628300a1828102 0x0e38381fb830103b 0x70e38381fb830103

def z231 : W := mkw 0x4bd7b7df00000000 0x04bd7b7df0000000 0x41c7ffff80000002 0x841c7ffff8000000

def z232 : W := mkw 0x0200300a00000000 0x00200300a0000000 0x0000381f80000002 0x00000381f8000000

def z233 : W := mkw 0x4dff87df00000000 0x04dff87df0000000 0x41ffc7ff80000001 0x841ffc7ff8000000

def z234 : W := mkw 0x1000c861c0c6ecc8 0x21000c861c0c6ecc 0xb049d8e3c1cfecc4 0x4b049d8e3c1cfecc

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x1030001c003000f1 0x01030001c003000f

def z236 : W := mkw 0x000008206d403a03 0x0000008206d403a0 0x8000000079c00000 0x08000000079c0000

def z237 : W := mkw 0x1f6afefbfdeefeeb 0xa1f6afefbfdeefee 0xffffffffffffffff 0xffffffffffffffff

def z238 : W := mkw 0x49d787d500000000 0x049d787d50000000 0x41cfdff380000003 0xd41cfdff38000000

def z239 : W := mkw 0x09400aa065402a01 0x009400aa065402a0 0xe1c01fe047c02f06 0xde1c01fe047c02f0

def z240 : W := mkw 0x4dff855f00000000 0x04dff855f0000000 0x0fffc01f80000001 0xf0fffc01f8000000

def z241 : W := mkw 0x24bd400037bd800c 0x024bd400037bd800 0xb03fc0007fffc00d 0x0b03fc0007fffc00

def z242 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e79f8ff80000003 0x70e79f8ff8000000

def z243 : W := mkw 0x0628300a00000000 0x00628300a0000000 0x0e38381f80000003 0x70e38381f8000000

def z244 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x9e7fc00079ffc001 0x49e7fc00079ffc00

def z245 : W := mkw 0x00020c3040406c40 0x000020c3040406c4 0xf0461cf041c1ecc7 0xdf0461cf041c1ecc

def z246 : W := mkw 0x0bd433842f111313 0x40bd433842f11131 0x0fb0230c3e301338 0x20fb0230c3e30133

def z247 : W := mkw 0x06be3d1eda3b75f2 0xc06be3d1eda3b75f 0x9e3e381ff83ff0ff 0x79e3e381ff83ff0f

def z248 : W := mkw 0x4f69bacbd82a30a2 0x84f69bacbd82a30a 0x9e79f8fff83e30ff 0x79e79f8fff83e30f

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180230006001308 0x2018023000600130

def z250 : W := mkw 0x2dfd400037bdc55c 0x42dfd400037bdc55 0xbfffc0007ffffffd 0xfbfffc0007ffffff

def z251 : W := mkw 0x0200380048003002 0x0020038004800300 0x0000380000003002 0x0000038000000300

def z252 : W := mkw 0x00960d14c21365d0 0x400960d14c21365d 0xf1be3f1fc63fffff 0xff1be3f1fc63ffff

def z253 : W := mkw 0x0428080ad02a20a0 0x80428080ad02a20a 0x9038181fc03e20f7 0x59038181fc03e20f

def z254 : W := mkw 0x4fffbfff6d403a03 0x04fffbfff6d403a0 0xefffffffffc03f0f 0xfefffffffffc03f0

def z255 : W := mkw 0x09d607b427514f51 0x409d607b427514f5 0x61c607e007c1cf00 0x861c607e007c1cf0

def z256 : W := mkw 0x49d5038400000000 0x049d503840000000 0x0180030000000000 0x0018003000000000

def z257 : W := mkw 0x24bd400a92bf80ac 0x824bd400a92bf80a 0x103fc01f803fc0f1 0x0103fc01f803fc0f

def z258 : W := mkw 0x0ffd380ad82a30a2 0x80ffd380ad82a30a 0x9ffff81ff83e30ff 0xf9ffff81ff83e30f

def z259 : W := mkw 0x00000800d82a30a2 0x800000800d82a30a 0x80000000780e0000 0x080000000780e000

def z260 : W := mkw 0x0000000000004550 0x4000000000000455 0x0000000000003ff0 0x00000000000003ff

def z261 : W := mkw 0x1000402000c4cc48 0x21000402000c4cc4 0x2000000001c1cc00 0x02000000001c1cc0

def z262 : W := mkw 0x0000000025000000 0x0000000002500000 0xa00000007fc0000c 0x0a00000007fc0000

def z263 : W := mkw 0x2ffd7aa07ffdba0f 0x02ffd7aa07ffdba0 0xbfffd8e07fffc00d 0xfbfffd8e07fffc00

def z264 : W := mkw 0x0b403aaaed423aa3 0x80b403aaaed423aa 0xefc03fffffc03ffe 0xfefc03fffffc03ff

def z265 : W := mkw 0x0628300a902a00a0 0x80628300a902a00a 0x1e38381f803e00f3 0x71e38381f803e00f

def z266 : W := mkw 0x2000400037bd800c 0x02000400037bd800 0xb00000007fffc00c 0x0b00000007fffc00

def z267 : W := mkw 0x2dfd482077fda80c 0x02dfd482077fda80 0xffffdce07fffec0f 0xfffffdce07fffec0

def z268 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0x6047dcf381c1ecc2 0x86047dcf381c1ecc

def z269 : W := mkw 0x00028c51c0022080 0x000028c51c002208 0xd04fdcf3c00e20c7 0xdd04fdcf3c00e20c

def z270 : W := mkw 0x0096051402110110 0x4009605140211011 0x41b6271c0630133b 0xb41b6271c0630133

def z271 : W := mkw 0x2429400010ac800c 0x02429400010ac800 0x0009c000000e0000 0x00009c000000e000

def z272 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0xe049dce3c1ce2c06 0xde049dce3c1ce2c0

def z273 : W := mkw 0x6ffff7df35ac800c 0x06ffff7df35ac800 0xcffffffff9ce0003 0xfcffffffff9ce000

def z274 : W := mkw 0x00000800c0022080 0x000000800c002208 0x00001813800020c2 0x000001813800020c

def z275 : W := mkw 0x1202fc7bc8c6fcea 0xa1202fc7bc8c6fce 0xf04ffcffc1cffcf7 0xdf04ffcffc1cffcf

def z276 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xe04fdce3c1cfcc00 0xce04fdce3c1cfcc0

def z277 : W := mkw 0x0002845100004440 0x0000284510000444 0x704fdcf38001ecc7 0xd704fdcf38001ecc

def z278 : W := mkw 0x02003aaac8423aa3 0x802003aaac8423aa 0x40003fff80003ff2 0x040003fff80003ff

def z279 : W := mkw 0x0002051402114550 0x4000205140211455 0x7000271c0631fffe 0x07000271c0631fff

def z280 : W := mkw 0x1b40fae1edc6ba8b 0x21b40fae1edc6ba8 0xefc9ffe3ffce3f0e 0xfefc9ffe3ffce3f0

def z281 : W := mkw 0x000002a000400a01 0x0000002a000400a0 0x400007e000000f00 0x0400007e000000f0

def z282 : W := mkw 0x6fffffdfffbfb0ae 0x86fffffdfffbfb0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z283 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xafcfc0007fcfc000 0xcafcfc0007fcfc00

def z284 : W := mkw 0x0200300000000000 0x0020030000000000 0x0e00380000000002 0x70e0038000000000

def z285 : W := mkw 0x1002c4518086c4c8 0x21002c4518086c4c 0x700fc413800fecc7 0x9700fc413800fecc

def z286 : W := mkw 0x0b423fb46d407f53 0x40b423fb46d407f5 0xefc03ffc7fc03ffe 0xfefc03ffc7fc03ff

def z287 : W := mkw 0x0b42b6d100000000 0x00b42b6d10000000 0x4fcffff380000003 0xf4fcffff38000000

def z288 : W := mkw 0x64bfc55f12bd800c 0x064bfc55f12bd800 0x103fc01f803fc001 0x0103fc01f803fc00

def z289 : W := mkw 0x0f683aaafd6a3aa3 0x80f683aaafd6a3aa 0x9e7838fff9fe30ff 0x79e7838fff9fe30f

def z290 : W := mkw 0x0bd6379400000000 0x00bd637940000000 0x4ff63ffc00000003 0xf4ff63ffc0000000

def z291 : W := mkw 0x0096051402114550 0x4009605140211455 0x41b0271c06303ffa 0x241b0271c06303ff

def z292 : W := mkw 0x0628300a18281022 0x80628300a1828102 0x1e30201c383030ff 0x31e30201c383030f

def z293 : W := mkw 0x4fffb7df00004440 0x04fffb7df0000444 0x7fffffff8001ecc7 0xf7fffffff8001ecc

def z294 : W := mkw 0x2000400035ac800c 0x02000400035ac800 0x8000000079ce0000 0x08000000079ce000

def z295 : W := mkw 0x2dfd400ab7bf80ac 0x82dfd400ab7bf80a 0xbfffc01fffffc0fd 0xfbfffc01fffffc0f

def z296 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf07ffcffc1fffcff 0xff07ffcffc1fffcf

def z297 : W := mkw 0x24bf451412bdc55c 0x424bf451412bdc55 0x103fc01c003fc0f1 0x0103fc01c003fc0f

def z298 : W := mkw 0x0002845100000000 0x0000284510000000 0x4047c4e000000000 0x84047c4e00000000

def z299 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x61c03fe007c03f02 0x861c03fe007c03f0

def z300 : W := mkw 0x0096051402114550 0x4009605140211455 0x6186271c0601fff2 0x86186271c0601fff

def z301 : W := mkw 0x0ffd328000000000 0x00ffd32800000000 0x4fffffe000000003 0xf4fffffe00000000

def z302 : W := mkw 0x0096051402114550 0x4009605140211455 0x31b6001c0631c0fd 0xb31b6001c0631c0f

def z303 : W := mkw 0x0b40328000000000 0x00b4032800000000 0x0e4018e000000000 0x40e4018e00000000

def z304 : W := mkw 0x4ffdb2cb00000000 0x04ffdb2cb0000000 0x0fffd8e380000001 0xf0fffd8e38000000

def z305 : W := mkw 0x0002041000004440 0x0000204100000444 0x718627100601ffcf 0xb718627100601ffc

def z306 : W := mkw 0x0dfd000002110000 0x00dfd00000211000 0x3fffc0000631c00d 0xf3fffc0000631c00

def z307 : W := mkw 0x00000800da3b75f2 0xc00000800da3b75f 0xb00000007e3ffffc 0x0b00000007e3ffff

def z308 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0xb04fd8e3c1cfc005 0xdb04fd8e3c1cfc00

def z309 : W := mkw 0x3dffc47137fdcc4c 0x23dffc47137fdcc4 0xffffc4e07fffcc0d 0xfffffc4e07fffcc0

def z310 : W := mkw 0x0096051402114550 0x4009605140211455 0x71b607000631cf0d 0xb71b607000631cf0

def z311 : W := mkw 0x0000082048403a03 0x00000082048403a0 0x0000000000003f00 0x00000000000003f0

def z312 : W := mkw 0x6f69f2cb35ac800c 0x06f69f2cb35ac800 0x8e49d8e3f9ce0000 0x48e49d8e3f9ce000

def z313 : W := mkw 0x0f68328a3d281223 0x80f68328a3d28122 0x0fb0230c3e301338 0x20fb0230c3e30133

def z314 : W := mkw 0x0428000010280000 0x0042800001028000 0x0e30000038300008 0x20e3000003830000

def z315 : W := mkw 0x0094010402110110 0x4009401040211011 0x61b0270c06303f3e 0xb61b0270c06303f3

def z316 : W := mkw 0x0002845100000000 0x0000284510000000 0x40001cf380000002 0x040001cf38000000

def z317 : W := mkw 0x0b423eb06d407e43 0x00b423eb06d407e4 0xffc63ff07fc1ffcf 0xfffc63ff07fc1ffc

def z318 : W := mkw 0x1096cc71c2d7ecc8 0x21096cc71c2d7ecc 0xf1ffdcf3c7ffeccf 0xff1ffdcf3c7ffecc

def z319 : W := mkw 0x0dff051400000000 0x00dff05140000000 0x4fffe71c00000003 0xf4fffe71c0000000

def z320 : W := mkw 0x2dfd48207ffdba0f 0x02dfd48207ffdba0 0xbfffc0007fffff0d 0xfbfffc0007fffff0

def z321 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0xbe4fc00079cfc005 0xdbe4fc00079cfc00

def z322 : W := mkw 0x0000082040402800 0x0000008204040280 0xa000000041c02c04 0x0a000000041c02c0

def z323 : W := mkw 0x44bf855f00000000 0x044bf855f0000000 0x41bfe71f80000003 0xb41bfe71f8000000

def z324 : W := mkw 0x0002041000004440 0x0000204100000444 0x4000041000002cc2 0x04000041000002cc

def z325 : W := mkw 0x0b40328000000000 0x00b4032800000000 0x6fc03fe006003f0e 0xf6fc03fe006003f0

def z326 : W := mkw 0x5f6bfefbc0c6ecc8 0x25f6bfefbc0c6ecc 0xfe4fdcf3c1cfecc7 0xdfe4fdcf3c1cfecc

def z327 : W := mkw 0x10004820d8eefcea 0xa10004820d8eefce 0xb000000079fffcfc 0x0b000000079fffcf

def z328 : W := mkw 0x0b403aa0fd6a3aa3 0x80b403aa0fd6a3aa 0xffc03fe07ffe3ffe 0xfffc03fe07ffe3ff

def z329 : W := mkw 0x4ffd3b8ed82a30a2 0x84ffd3b8ed82a30a 0x9fb83b1ff83e30ff 0x79fb83b1ff83e30f

def z330 : W := mkw 0x0b4032802d001203 0x00b4032802d00120 0x6f8027003e003f0e 0xb6f8027003e003f0

def z331 : W := mkw 0x2f69780afdaeb0ae 0x82f69780afdaeb0a 0x9e79f81ff9fe30ff 0x79e79f81ff9fe30f

def z332 : W := mkw 0x04be051e923b45f0 0xc04be051e923b45f 0x71be271f863fffff 0xb71be271f863ffff

def z333 : W := mkw 0x00960d14da3b75f2 0xc00960d14da3b75f 0xf1b6271c7e3fffff 0xbf1b6271c7e3ffff

def z334 : W := mkw 0x54bfcd7fc0c6ecc8 0x254bfcd7fc0c6ecc 0xf07fdcffc1cfecc7 0xdf07fdcffc1cfecc

def z335 : W := mkw 0x49d787d502114550 0x449d787d50211455 0x61c7c7e00601cf00 0x861c7c7e00601cf0

def z336 : W := mkw 0x0096051402114550 0x4009605140211455 0x11b6231c0631d3f9 0x211b6231c0631d3f

def z337 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf1cffff3c7cfffcf 0xff1cffff3c7cfffc

def z338 : W := mkw 0x2dff441037bdc44c 0x02dff441037bdc44 0xffffc4107fffeccf 0xfffffc4107fffecc

def z339 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb0081813c1cfecc7 0x5b0081813c1cfecc

def z340 : W := mkw 0x4fffbfdfda3b75f2 0xc4fffbfdfda3b75f 0xfffffffffe3fffff 0xffffffffffe3ffff

def z341 : W := mkw 0x4296b7df00000000 0x04296b7df0000000 0x41b63fff80000003 0xb41b63fff8000000

def z342 : W := mkw 0x0628382afd6a3aa3 0x80628382afd6a3aa 0xbe38381ffffe3fff 0x7be38381ffffe3ff

def z343 : W := mkw 0x4097855500000000 0x0409785550000000 0x0007c00000000000 0x00007c0000000000

def z344 : W := mkw 0x44bf855f00000000 0x044bf855f0000000 0x407fdcff80000003 0xd407fdcff8000000

def z345 : W := mkw 0x2dfd000037390004 0x02dfd00003739000 0xaff000007ff0000c 0xfaff000007ff0000

def z346 : W := mkw 0x49d787f525400a01 0x049d787f525400a0 0x61c7c7e007c00f00 0x861c7c7e007c00f0

def z347 : W := mkw 0x6ffd738e37bd800c 0x06ffd738e37bd800 0xbfffe30c7fffc00d 0xfbfffe30c7fffc00

def z348 : W := mkw 0x00000800d82a30a2 0x800000800d82a30a 0x9030201c783e30ff 0x39030201c783e30f

def z349 : W := mkw 0x4fffbfdfc0022080 0x04fffbfdfc002208 0xdfffffffc00e20c7 0xfdfffffffc00e20c

def z350 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x0fbfe31f80000001 0x20fbfe31f8000000

def z351 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000040000002c06 0x96000040000002c0

def z352 : W := mkw 0x5fffffffd8eefcea 0xa5fffffffd8eefce 0xfffffffff9fffcff 0xffffffffff9fffcf

def z353 : W := mkw 0x2ffd300a3f391026 0x82ffd300a3f39102 0x0fb0200c3e301038 0x20fb0200c3e30103

def z354 : W := mkw 0x02003800d82a30a2 0x802003800d82a30a 0x9e003800783e30fe 0x79e003800783e30f

def z355 : W := mkw 0x5202ffffc0c6ecc8 0x25202ffffc0c6ecc 0xf04fffffc1cfecc7 0xdf04fffffc1cfecc

def z356 : W := mkw 0x1942c6f125c4ce49 0x21942c6f125c4ce4 0x61c7c7e007c1cf00 0x861c7c7e007c1cf0

def z357 : W := mkw 0x10028451800244c0 0x210028451800244c 0x00000013800000c0 0x000000013800000c

def z358 : W := mkw 0x10028d75c0426dd0 0x610028d75c0426dd 0x40003fff80003ff2 0x040003fff80003ff

def z359 : W := mkw 0x1628f86bd8eeb8aa 0xa1628f86bd8eeb8a 0x9e79f8fff9fe30ff 0x79e79f8fff9fe30f

def z360 : W := mkw 0x4fffbfdfc80230a2 0x84fffbfdfc80230a 0x4fffffff800030f3 0xf4fffffff800030f

def z361 : W := mkw 0x0002845100000000 0x0000284510000000 0x000fc01380000001 0x0000fc0138000000

def z362 : W := mkw 0x0094010402110110 0x4009401040211011 0x31b6230c0631d33d 0xb31b6230c0631d33

def z363 : W := mkw 0x0f683aaa6d403a03 0x00f683aaa6d403a0 0xeff83fffffc03f0f 0xfeff83fffffc03f0

def z364 : W := mkw 0x1942cc71e5c6ecc8 0x21942cc71e5c6ecc 0xffcfdcf3ffcfeccf 0xfffcfdcf3ffcfecc

def z365 : W := mkw 0x00028c7140402800 0x000028c714040280 0xe04fdcf3c1c02c07 0xde04fdcf3c1c02c0

def z366 : W := mkw 0x0f683a8ad82a30a2 0x80f683a8ad82a30a 0xdff83ffff83e30ff 0xfdff83ffff83e30f

def z367 : W := mkw 0x1002cc71d8eefcea 0xa1002cc71d8eefce 0xf04fdcf3f9fffcff 0xdf04fdcf3f9fffcf

def z368 : W := mkw 0x5ffff7df8086c4c8 0x25ffff7df8086c4c 0x5fffffff800fc0c3 0xf5fffffff800fc0c

def z369 : W := mkw 0x4429804b00000000 0x04429804b0000000 0x0009c00380000000 0x00009c0038000000

def z370 : W := mkw 0x0002041000004440 0x0000204100000444 0x100600100001c0c1 0x0100600100001c0c

def z371 : W := mkw 0x1002c4510084c448 0x21002c4510084c44 0x0007c0000001c000 0x00007c0000001c00

def z372 : W := mkw 0x0000482040c4a808 0x00000482040c4a80 0xf04fdce041cfec07 0xdf04fdce041cfec0

def z373 : W := mkw 0x02003aa048403a03 0x002003aa048403a0 0x61803fe006003f0e 0xb61803fe006003f0

def z374 : W := mkw 0x0940028025000201 0x0094002802500020 0x0180030006000300 0x0018003000600030

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x90080000400e0005 0x590080000400e000

def z376 : W := mkw 0x1dffcc71c0c6ecc8 0x21dffcc71c0c6ecc 0xffffdcf3c1cfecc7 0xfffffdcf3c1cfecc

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000201c000030f2 0x00000201c000030f

def z378 : W := mkw 0x2dfd400035ac800c 0x02dfd400035ac800 0x8fffc00079ce0001 0xf8fffc00079ce000

def z379 : W := mkw 0x200040002795800c 0x0200040002795800 0x2000000007c1c000 0x02000000007c1c00

def z380 : W := mkw 0x1002c4518086c4c8 0x21002c4518086c4c 0xb04fc013c1cfc0c5 0xdb04fc013c1cfc0c

def z381 : W := mkw 0x2dff451437bdc55c 0x42dff451437bdc55 0xffffc7007fffcf0d 0xfffffc7007fffcf0

def z382 : W := mkw 0x0094010402110110 0x4009401040211011 0x0030000c00300030 0x00030000c0030003

def z383 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e38380ff83e1038 0x68e38380ff83e103

def z384 : W := mkw 0x09d5000000000000 0x009d500000000000 0x01c7c00000000000 0x801c7c0000000000

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x103000000030000d 0x3103000000030000

def z386 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000270000003f02 0x04000270000003f0

def z387 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xcfc03fe079c00002 0xfcfc03fe079c0000

def z388 : W := mkw 0x00000000902a00a0 0x800000000902a00a 0x10000000003e00f0 0x010000000003e00f

def z389 : W := mkw 0x29d542a027d58a0d 0x029d542a027d58a0 0x61c7c7e007c1cf00 0x861c7c7e007c1cf0

def z390 : W := mkw 0x6fffffff7ffdba0f 0x06fffffff7ffdba0 0xffffffffffffff0f 0xfffffffffffffff0

def z391 : W := mkw 0x0628380ac0022080 0x00628380ac002208 0x9e38381fc00e20c7 0x79e38381fc00e20c

def z392 : W := mkw 0x4fffb7df10280000 0x04fffb7df1028000 0xdffffffff83e000f 0xfdffffffff83e000

def z393 : W := mkw 0x44bf855f902a00a0 0x844bf855f902a00a 0x103fc01f803e00f1 0x0103fc01f803e00f

def z394 : W := mkw 0x02963fb44a517f53 0x402963fb44a517f5 0x71b63ffc0631ffff 0xb71b63ffc0631fff

def z395 : W := mkw 0x4200b2cb00000000 0x04200b2cb0000000 0x000018e380000000 0x0000018e38000000

def z396 : W := mkw 0x3d6bcc71f5eeeccc 0x23d6bcc71f5eeecc 0xfe4fdcf3f9cfecc7 0xdfe4fdcf3f9cfecc

def z397 : W := mkw 0x0940000025000000 0x0094000002500000 0x21c0000007c00000 0x821c0000007c0000

def z398 : W := mkw 0x00000800c0022080 0x000000800c002208 0x90000000400e20c4 0x090000000400e20c

def z399 : W := mkw 0x142ac45b90aec4e8 0xa142ac45b90aec4e 0x103fc01f803fc0f1 0x0103fc01f803fc0f

def z400 : W := mkw 0x02003aa06d403a03 0x002003aa06d403a0 0xe0003fe07fc03f0e 0x0e0003fe07fc03f0

def z401 : W := mkw 0x0000000a800200a0 0x80000000a800200a 0x0000001f800000f0 0x00000001f800000f

def z402 : W := mkw 0x0000400000848008 0x0000040000084800 0xb000000041cfc004 0x0b000000041cfc00

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x40401ce000000002 0xd40401ce00000000

def z404 : W := mkw 0x4f69baeb6d403a03 0x04f69baeb6d403a0 0xefc9ffe3ffc03f0e 0xfefc9ffe3ffc03f0

def z405 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xfff03ffc7ff03fff 0xffff03ffc7ff03ff

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x300600000001c005 0x9300600000001c00

def z407 : W := mkw 0x0bd43ba46f513b13 0x40bd43ba46f513b1 0xeff03fec7ff03f3e 0xfeff03fec7ff03f3

def z408 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x1038381f803e30f3 0x01038381f803e30f

def z409 : W := mkw 0x24bd400012bd800c 0x024bd400012bd800 0x31bfc000063fc00d 0xb31bfc000063fc00

def z410 : W := mkw 0x4fffb7df902a00a0 0x84fffb7df902a00a 0x5fffffff803e00f3 0xf5fffffff803e00f

def z411 : W := mkw 0x29d540002795800c 0x029d540002795800 0xb1cfc00047cfc005 0xdb1cfc00047cfc00

def z412 : W := mkw 0x4b42b7df00000000 0x04b42b7df0000000 0x4fc03fff80000002 0xf4fc03fff8000000

def z413 : W := mkw 0x4ffd338e00000000 0x04ffd338e0000000 0x4ff03fec00000002 0xf4ff03fec0000000

def z414 : W := mkw 0x0428000010280000 0x0042800001028000 0x8e080000780e0000 0x48e080000780e000

def z415 : W := mkw 0x3dfdc861f7ffa88c 0x23dfdc861f7ffa88 0xbfffd8e3ffffc00d 0xfbfffd8e3ffffc00

def z416 : W := mkw 0x1002cd75c0c6edd8 0x61002cd75c0c6edd 0xf04fffffc1cffff7 0xdf04fffffc1cffff

def z417 : W := mkw 0x4ffd338e02110110 0x44ffd338e0211011 0x0fb0230c06301338 0x20fb0230c0630133

def z418 : W := mkw 0x200048207ffdba0f 0x0200048207ffdba0 0xb00000007fffff0c 0x0b00000007fffff0

def z419 : W := mkw 0x2dfd400012bd800c 0x02dfd400012bd800 0x1fffc000003fc001 0xf1fffc000003fc00

def z420 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xc049dcf3c1ce2cc2 0x4c049dcf3c1ce2cc

def z421 : W := mkw 0x0094000000000000 0x0009400000000000 0x01b6000000000001 0xb01b600000000000

def z422 : W := mkw 0x00000820c0422880 0x000000820c042288 0xf0481cf3c1ce2cc7 0xdf0481cf3c1ce2cc

def z423 : W := mkw 0x0bd637942f115753 0x40bd637942f11575 0x7fb6271c3e31ffff 0xb7fb6271c3e31fff

def z424 : W := mkw 0x46bfbd5fd82a30a2 0x846bfbd5fd82a30a 0x9e3ff81ff83e30ff 0x79e3ff81ff83e30f

def z425 : W := mkw 0x6ffff7df37bdc55c 0x46ffff7df37bdc55 0xffffffffffffffff 0xffffffffffffffff

def z426 : W := mkw 0x39d7cc71e7d7eccc 0x239d7cc71e7d7ecc 0xf1cfdcf3c7cfecc7 0xdf1cfdcf3c7cfecc

def z427 : W := mkw 0x0000804100000000 0x0000080410000000 0x0049d8e380000000 0x40049d8e38000000

def z428 : W := mkw 0x4296b7df02114550 0x44296b7df0211455 0x71b63fff8631ffff 0xb71b63fff8631fff

def z429 : W := mkw 0x1000c06100c48808 0x21000c06100c4880 0x0041c0e001c00000 0x00041c0e001c0000

def z430 : W := mkw 0x10028c71c0426cc0 0x210028c71c0426cc 0xd0081cf3c00e2cc7 0x5d0081cf3c00e2cc

def z431 : W := mkw 0x6ffff7df2795800c 0x06ffff7df2795800 0x6fffffff87c1c003 0xf6fffffff87c1c00

def z432 : W := mkw 0x2000000037390004 0x0200000003739000 0x000000003e300008 0x0000000003e30000

def z433 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x0e30381fb83030fa 0x20e30381fb83030f

def z434 : W := mkw 0x0b4032802d001203 0x00b4032802d00120 0xafc023007fc0130c 0xfafc023007fc0130

def z435 : W := mkw 0x10028c71c0426cc0 0x210028c71c0426cc 0x404fdcf380002cc3 0xd404fdcf380002cc

def z436 : W := mkw 0x0200380048003002 0x0020038004800300 0xef803f007e003f0e 0xfef803f007e003f0

def z437 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0x004000e001c00000 0x0004000e001c0000

def z438 : W := mkw 0x4f6bb6db00000000 0x04f6bb6db0000000 0x4e4fdcf380000003 0xd4e4fdcf38000000

def z439 : W := mkw 0x0096051402110000 0x0009605140211000 0x71b6271c0631c00f 0xb71b6271c0631c00

def z440 : W := mkw 0x0200380ac80230a2 0x80200380ac80230a 0x1030381f803030ff 0x31030381f803030f

def z441 : W := mkw 0x2094400037bd800c 0x02094400037bd800 0xb1b600007fffc00d 0xbb1b600007fffc00

def z442 : W := mkw 0x2f697aa07decba0f 0x02f697aa07decba0 0x8e49d8e079ce0000 0x48e49d8e079ce000

def z443 : W := mkw 0x24bd000012390004 0x024bd00001239000 0x0030000000300000 0x0003000000030000

def z444 : W := mkw 0x0096051402114550 0x4009605140211455 0x7036041c0031ecf7 0x97036041c0031ecf

def z445 : W := mkw 0x2628780affbfb0ae 0x82628780affbfb0a 0xbe38381ffffff0ff 0x7be38381ffffff0f

def z446 : W := mkw 0x0bd43aa06f513a03 0x00bd43aa06f513a0 0xfff63fe07ff1ff0f 0xffff63fe07ff1ff0

def z447 : W := mkw 0x5fffffffc2d7edd8 0x65fffffffc2d7edd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z448 : W := mkw 0x02963d144a117552 0x402963d144a11755 0xffb63f1c7e31ffff 0xfffb63f1c7e31fff

def z449 : W := mkw 0x2dfd4800f7bfa08c 0x02dfd4800f7bfa08 0xbfffd813ffffe0cf 0xfbfffd813ffffe0c

def z450 : W := mkw 0x2ffd700a3fbd902e 0x82ffd700a3fbd902 0xbfffe00c7fffd03d 0xfbfffe00c7fffd03

def z451 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x31ffc00007ffc001 0x831ffc00007ffc00

def z452 : W := mkw 0x0000002000400800 0x0000000200040080 0x604004e001c00c00 0x8604004e001c00c0

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x004fc00000000001 0xd004fc0000000000

def z454 : W := mkw 0x00000820fd6a3aa3 0x800000820fd6a3aa 0xb00000007ffe3ffc 0x0b00000007ffe3ff

def z455 : W := mkw 0x142acc7bd0eeece8 0xa142acc7bd0eeece 0xf07fdcffc1ffecf7 0xdf07fdcffc1ffecf

def z456 : W := mkw 0x1942cef1e5c6eec9 0x21942cef1e5c6eec 0xf1cfdff3c7cfefc7 0xdf1cfdff3c7cfefc

def z457 : W := mkw 0x0096051402114550 0x4009605140211455 0x618627000601ff0e 0xb618627000601ff0

def z458 : W := mkw 0x2428400037bd800c 0x02428400037bd800 0xbe3800007fffc00d 0x7be3800007fffc00

def z459 : W := mkw 0x1b42fef1edc6fecb 0x21b42fef1edc6fec 0xfe4fdcf3f9cfecc7 0xdfe4fdcf3f9cfecc

def z460 : W := mkw 0x06bc380ada3b30a2 0x806bc380ada3b30a 0xbfbe381ffe3ff0ff 0xfbfbe381ffe3ff0f

def z461 : W := mkw 0x0200328000000000 0x0020032800000000 0x40003fe000000002 0x040003fe00000000

def z462 : W := mkw 0x0b4032802d001203 0x00b4032802d00120 0x4fc03fe03e00130a 0xf4fc03fe03e00130

def z463 : W := mkw 0x1002cc51c086e4c8 0x21002cc51c086e4c 0x900fd813c00fe0c7 0x5900fd813c00fe0c

def z464 : W := mkw 0x0b42bef16d403a03 0x00b42bef16d403a0 0xefcffff3ffc03f0f 0xfefcffff3ffc03f0

def z465 : W := mkw 0x2fff7fb47ffdff5f 0x42fff7fb47ffdff5 0xfffffffc7fffffff 0xffffffffc7ffffff

def z466 : W := mkw 0x1096c5558297c5d8 0x61096c5558297c5d 0x103fc01f803fc0f1 0x0103fc01f803fc0f

def z467 : W := mkw 0x0f683aaa7d683a23 0x80f683aaa7d683a2 0xeff03fec7ff03f3e 0xfeff03fec7ff03f3

def z468 : W := mkw 0x462ab7df00000000 0x0462ab7df0000000 0x4e383fff80000003 0x74e383fff8000000

def z469 : W := mkw 0x0094000002114550 0x4009400000211455 0x31b600000631fffd 0xb31b600000631fff

def z470 : W := mkw 0x0000000002110000 0x0000000000211000 0x300000000631c00c 0x0300000000631c00

def z471 : W := mkw 0x5fffffffedc6fecb 0x25fffffffedc6fec 0xffffffffffcfffcf 0xfffffffffffcfffc

def z472 : W := mkw 0x0940082065402800 0x0094008206540280 0xefc01ce07fc02c0e 0xfefc01ce07fc02c0

def z473 : W := mkw 0x4ffd338e18281022 0x84ffd338e1828102 0x0fb0230c38301038 0x20fb0230c3830103

def z474 : W := mkw 0x02003800c8023082 0x002003800c802308 0x9e083813f80e30cf 0x79e083813f80e30c

def z475 : W := mkw 0x0096051402114550 0x4009605140211455 0x5036271c0031fff3 0x05036271c0031fff

def z476 : W := mkw 0x1bd6fff5efd7ffdb 0x61bd6fff5efd7ffd 0xffffffffffffffff 0xffffffffffffffff

def z477 : W := mkw 0x4fffbfff6d403a03 0x04fffbfff6d403a0 0xcffffffff9c00003 0xfcffffffff9c0000

def z478 : W := mkw 0x00960d3442516d50 0x400960d3442516d5 0xf1f63ffc47f1ffff 0xff1f63ffc47f1fff

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0xa040000041c00004 0xda040000041c0000

def z480 : W := mkw 0x4fffbfff40402800 0x04fffbfff4040280 0xefffffffc1c02c07 0xfefffffffc1c02c0

def z481 : W := mkw 0x4fffbfff48403a03 0x04fffbfff48403a0 0x4fffffff80003f03 0xf4fffffff80003f0

def z482 : W := mkw 0x34bfcc71d2ffeccc 0x234bfcc71d2ffecc 0xf07fdcf3c1ffecc7 0xdf07fdcf3c1ffecc

def z483 : W := mkw 0x0200380ad82a30a2 0x80200380ad82a30a 0x9000381ff83e30fe 0x09000381ff83e30f

def z484 : W := mkw 0x02003aa048403a03 0x002003aa048403a0 0xe0403fe041c03f06 0xde0403fe041c03f0

def z485 : W := mkw 0x0094000002110000 0x0009400000211000 0x01b0000006300008 0x201b000000630000

def z486 : W := mkw 0x4202bfff48403a03 0x04202bfff48403a0 0x40003fff80003f02 0x040003fff80003f0

def z487 : W := mkw 0x0094010402110110 0x4009401040211011 0x0180030006000300 0x0018003000600030

def z488 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x6fffffff8601cf03 0xf6fffffff8601cf0

def z489 : W := mkw 0x2d69000035280004 0x02d6900003528000 0x0e00000038000000 0x00e0000003800000

def z490 : W := mkw 0x0200380ac80230a2 0x80200380ac80230a 0x0000180380000000 0x0000018038000000

def z491 : W := mkw 0x3dffc451b7bfc4cc 0x23dffc451b7bfc4c 0xbfffc013ffffc0cd 0xfbfffc013ffffc0c

def z492 : W := mkw 0x0428000a00000000 0x00428000a0000000 0x0038001f80000001 0x00038001f8000000

def z493 : W := mkw 0x0094000002110000 0x0009400000211000 0x218600000601c000 0x8218600000601c00

def z494 : W := mkw 0x162afc7bd8eefcea 0xa162afc7bd8eefce 0xfe4fdcf3f9cfecc7 0xdfe4fdcf3f9cfecc

def z495 : W := mkw 0x06bc390eda3b31b2 0xc06bc390eda3b31b 0x9fb83b1ffe3e33ff 0x79fb83b1ffe3e33f

def z496 : W := mkw 0x1096cd75c0c6ecc8 0x21096cd75c0c6ecc 0xf1ffffffc1cfecc7 0xff1ffffffc1cfecc

def z497 : W := mkw 0x000008206d403a03 0x0000008206d403a0 0xe18027007fc03f0e 0xbe18027007fc03f0

def z498 : W := mkw 0x5ffff7ff00c4cc48 0x25ffff7ff00c4cc4 0x6fffffff81c1cc03 0xf6fffffff81c1cc0

def z499 : W := mkw 0x69d7c7d52795800c 0x069d7c7d52795800 0x61c7c7e007c1c000 0x861c7c7e007c1c00

def z500 : W := mkw 0x2ffd7aaaffffbaaf 0x82ffd7aaaffffbaa 0xffffffffffffffff 0xffffffffffffffff

def z501 : W := mkw 0x29d5400037bd800c 0x029d5400037bd800 0xb1c7c0007fffc00c 0x8b1c7c0007fffc00

def z502 : W := mkw 0x4202bfdfc80230a2 0x84202bfdfc80230a 0x40003fff800030f2 0x040003fff800030f

def z503 : W := mkw 0x4ffd338e2d001203 0x04ffd338e2d00120 0x0fb0230c3e001308 0x20fb0230c3e00130

def z504 : W := mkw 0x4fffbffffd6a3aa3 0x84fffbffffd6a3aa 0xfffffffffffe3fff 0xffffffffffffe3ff

def z505 : W := mkw 0x062ab45b00000000 0x0062ab45b0000000 0x4e7ffcff80000003 0xf4e7ffcff8000000

def z506 : W := mkw 0x0000400000848008 0x0000040000084800 0x100fc000000fc001 0x0100fc000000fc00

def z507 : W := mkw 0x2dff451437bd800c 0x02dff451437bd800 0xffffe71c7fffc00f 0xfffffe71c7fffc00

def z508 : W := mkw 0x2ffd72803fbd920f 0x02ffd72803fbd920 0xbfffe3007fffd30d 0xfbfffe3007fffd30

def z509 : W := mkw 0x162abc7bd86a7ce2 0xa162abc7bd86a7ce 0xde383cfff83e3cff 0x7de383cfff83e3cf

def z510 : W := mkw 0x00000800d82a30a2 0x800000800d82a30a 0x90081813f83e30ff 0x590081813f83e30f

def z511 : W := mkw 0x00000800c0022080 0x000000800c002208 0x80081803c00e0000 0x480081803c00e000

def z512 : W := mkw 0x00960d346f517f53 0x400960d346f517f5 0xf1b6271c7ff1ffff 0xbf1b6271c7ff1fff

def z513 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x4f803fe03e003f0a 0x24f803fe03e003f0

def z514 : W := mkw 0x2ffd780affbfb0ae 0x82ffd780affbfb0a 0xbfffd803ffffc00d 0xfbfffd803ffffc00

def z515 : W := mkw 0x29d745142795c55c 0x429d745142795c55 0x71f7e71c07f1ffff 0xb71f7e71c07f1fff

def z516 : W := mkw 0x10028c71c0426cc0 0x210028c71c0426cc 0xe0401cf3c1c02cc6 0xde0401cf3c1c02cc

def z517 : W := mkw 0x0002041000000000 0x0000204100000000 0x4006041000000003 0x9400604100000000

def z518 : W := mkw 0x0d68000035280000 0x00d6800003528000 0xbff800007ffe000d 0xfbff800007ffe000

def z519 : W := mkw 0x2f69780afdaeb0ae 0x82f69780afdaeb0a 0x8e49d803f9ce0000 0x48e49d803f9ce000

def z520 : W := mkw 0x2dfd000037390004 0x02dfd00003739000 0x0fffc0003e300009 0xf0fffc0003e30000

def z521 : W := mkw 0x16befd7fdafffdfa 0xe16befd7fdafffdf 0xffffffffffffffff 0xffffffffffffffff

def z522 : W := mkw 0x30004820f7ffeccc 0x230004820f7ffecc 0xb00000007fffeccc 0x0b00000007fffecc

def z523 : W := mkw 0x2d69400037bd800c 0x02d69400037bd800 0xbe49c0007fffc00c 0x4be49c0007fffc00

def z524 : W := mkw 0x0200328008001203 0x0020032800800120 0x0000230000001300 0x0000023000000130

def z525 : W := mkw 0x0096051402114550 0x4009605140211455 0x000600000001c000 0x0000600000001c00

def z526 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0x9e79c00079fe000d 0x79e79c00079fe000

def z527 : W := mkw 0x0b403aa048403a03 0x00b403aa048403a0 0x4fc03fe000003f02 0xf4fc03fe000003f0

def z528 : W := mkw 0x0428000010280000 0x0042800001028000 0x9e38201c783e30ff 0x79e38201c783e30f

def z529 : W := mkw 0x1002cc7140c4ec48 0x21002cc7140c4ec4 0xe047dce041c1ec06 0xde047dce041c1ec0

def z530 : W := mkw 0x0628380a48003002 0x00628380a4800300 0x8e38381ff800300f 0x78e38381ff800300

def z531 : W := mkw 0x1002cc71edc6fecb 0x21002cc71edc6fec 0xf04fdcf3ffcfffcf 0xdf04fdcf3ffcfffc

def z532 : W := mkw 0x0000000000000000 0x0000000000000000 0x000020000000300e 0x3000020000000300

def z533 : W := mkw 0x062a3c1ad82a74e2 0x8062a3c1ad82a74e 0xfe3e3c1ff83ffcff 0xffe3e3c1ff83ffcf

def z534 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xce403fe079c03f02 0x4ce403fe079c03f0

def z535 : W := mkw 0x1628782ad8eefcea 0xa1628782ad8eefce 0xbe38381ff9fffcff 0x7be38381ff9fffcf

def z536 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e081813f80e20c7 0x59e081813f80e20c

def z537 : W := mkw 0x0096041002114440 0x0009604100211444 0x71b604100631eccf 0xb71b604100631ecc

def z538 : W := mkw 0x54bfc55f8086c4c8 0x254bfc55f8086c4c 0x103fc01f800fc0c1 0x0103fc01f800fc0c

def z539 : W := mkw 0x1002c47100c4cc48 0x21002c47100c4cc4 0x604fdcf381c1cc03 0xd604fdcf381c1cc0

def z540 : W := mkw 0x0f683aaafd6a3aa3 0x80f683aaafd6a3aa 0xefc83fe3ffce3f0e 0xfefc83fe3ffce3f0

def z541 : W := mkw 0x0096051402114550 0x4009605140211455 0x718607100601efc7 0x9718607100601efc

def z542 : W := mkw 0x0000000018281022 0x8000000001828102 0x0000000038301038 0x0000000003830103

def z543 : W := mkw 0x0096051400000000 0x0009605140000000 0x4186070000000000 0x8418607000000000

def z544 : W := mkw 0x0000080048003002 0x0000008004800300 0x800000007800300c 0x0800000007800300

def z545 : W := mkw 0x4ffd338e00000000 0x04ffd338e0000000 0x0fb83b1f80000003 0x70fb83b1f8000000

def z546 : W := mkw 0x0428000000000000 0x0042800000000000 0x0e38000000000001 0x70e3800000000000

def z547 : W := mkw 0x0bd63fb46d403a03 0x00bd63fb46d403a0 0xeff63ffc7fc03f0f 0xfeff63ffc7fc03f0

def z548 : W := mkw 0x0000000080020080 0x0000000008002008 0x10080013800e00c1 0x010080013800e00c

def z549 : W := mkw 0x0428000a10280020 0x80428000a1028002 0x0030000c00300030 0x00030000c0030003

def z550 : W := mkw 0x09d4000027110000 0x009d400002711000 0xbff600007ff1c00d 0xfbff600007ff1c00

def z551 : W := mkw 0x4fffb7df02110110 0x44fffb7df0211011 0x4fffffff8630133b 0xf4fffffff8630133

def z552 : W := mkw 0x062abc5bd82a30a2 0x8062abc5bd82a30a 0xde7ffcfff83e30ff 0xfde7ffcfff83e30f

def z553 : W := mkw 0x0096051402114550 0x4009605140211455 0x61b6270c0631df38 0xa61b6270c0631df3

def z554 : W := mkw 0x0200382048403802 0x0020038204840380 0xee403ce079c03c0e 0xfee403ce079c03c0

def z555 : W := mkw 0x009645140295c558 0x4009645140295c55 0xf1ffe71c47ffffff 0xff1ffe71c47fffff

def z556 : W := mkw 0x49d787d500000000 0x049d787d50000000 0x41f7e7fc00000003 0xb41f7e7fc0000000

def z557 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x1fbfc0003e3fc009 0x21fbfc0003e3fc00

def z558 : W := mkw 0x1096cd75c2d7edd8 0x61096cd75c2d7edd 0xf1cfdff3c7cfefc7 0xdf1cfdff3c7cfefc

def z559 : W := mkw 0x0000000000004440 0x0000000000000444 0x300000000001ecc4 0x0300000000001ecc

def z560 : W := mkw 0x00020c10c00264c0 0x000020c10c00264c 0xf00e1c13c00fecc7 0xdf00e1c13c00fecc

def z561 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xafc018e07fc0000c 0xfafc018e07fc0000

def z562 : W := mkw 0x0ffd3aa06d403a03 0x00ffd3aa06d403a0 0xefffffe07fc03f0f 0xfefffffe07fc03f0

def z563 : W := mkw 0x0f683a8afd2a32a3 0x80f683a8afd2a32a 0x9fb83b1ffe3e33ff 0x79fb83b1ffe3e33f

def z564 : W := mkw 0x39d7c47127d5cc4c 0x239d7c47127d5cc4 0x61c7c4e007c1cc00 0x861c7c4e007c1cc0

def z565 : W := mkw 0x0dfd000025000000 0x00dfd00002500000 0xafffc0007fc0000d 0xfafffc0007fc0000

def z566 : W := mkw 0x00004800c086a088 0x000004800c086a08 0xb04fd813c1cfe0c7 0xdb04fd813c1cfe0c

def z567 : W := mkw 0x09d6051427114550 0x409d605142711455 0xfff6271c7ff1ffff 0xffff6271c7ff1fff

def z568 : W := mkw 0x44bf855f02114550 0x444bf855f0211455 0x71bfe71f8631ffff 0xb71bfe71f8631fff

def z569 : W := mkw 0x062a3d1ed82a75f2 0xc062a3d1ed82a75f 0xde383f1ff83e3fff 0x7de383f1ff83e3ff

def z570 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf047c4e041cfecc4 0x8f047c4e041cfecc

def z571 : W := mkw 0x46bfb7df00000000 0x046bfb7df0000000 0x403fffff80000003 0x0403fffff8000000

def z572 : W := mkw 0x0000400000848008 0x0000040000084800 0x8049c00041ce0000 0x48049c00041ce000

def z573 : W := mkw 0x0628380a58283022 0x80628380a5828302 0x8e30380c7830303e 0x78e30380c7830303

def z574 : W := mkw 0x0002051400004550 0x4000205140000455 0x4000070000000f00 0x04000070000000f0

def z575 : W := mkw 0x1002c47180c6ccc8 0x21002c47180c6ccc 0x704fc4f381cfccc1 0x8704fc4f381cfccc

def z576 : W := mkw 0x6dffc55f37bd800c 0x06dffc55f37bd800 0xbfffc01fffffc00d 0xfbfffc01fffffc00

def z577 : W := mkw 0x02023fb448407f53 0x402023fb448407f5 0x40003ffc00003ff2 0x040003ffc00003ff

def z578 : W := mkw 0x10008861c0422880 0x210008861c042288 0x000018e380000000 0x0000018e38000000

def z579 : W := mkw 0x1b40fae1edc6ba8b 0x21b40fae1edc6ba8 0x8e49d8e3f9ce0000 0x48e49d8e3f9ce000

def z580 : W := mkw 0x2ffd32803f391207 0x02ffd32803f39120 0x0fb023003e301308 0x20fb023003e30130

def z581 : W := mkw 0x3d69c861f5eea88c 0x23d69c861f5eea88 0x8e49d8e3f9ce0000 0x48e49d8e3f9ce000

def z582 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e0000007800000c 0x78e0000007800000

def z583 : W := mkw 0x04be051412394550 0x404be05141239455 0xffbe271c7e3fffff 0xfffbe271c7e3ffff

def z584 : W := mkw 0x0094000002110000 0x0009400000211000 0x31b6201c0631f0ff 0xb31b6201c0631f0f

def z585 : W := mkw 0x0dfd000010280000 0x00dfd00001028000 0x9fffc000783e000d 0xf9fffc000783e000

def z586 : W := mkw 0x0002041000004440 0x0000204100000444 0x600604000001cc00 0x8600604000001cc0

def z587 : W := mkw 0x06be351e02114550 0x406be351e0211455 0x7fbe3f1f8631ffff 0xf7fbe3f1f8631fff

def z588 : W := mkw 0x0200300008001002 0x0020030000800100 0x0e00200038001008 0x20e0020003800100

def z589 : W := mkw 0x2ffd78007fbdb00e 0x02ffd78007fbdb00 0xbffff8007ffff00f 0xfbffff8007ffff00

def z590 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0xefc007e07fc00f0c 0xfefc007e07fc00f0

def z591 : W := mkw 0x0096051402114550 0x4009605140211455 0x718607000631fffc 0x8718607000631fff

def z592 : W := mkw 0x4ffd338e00000000 0x04ffd338e0000000 0x0fffe30c00000001 0xf0fffe30c0000000

def z593 : W := mkw 0x000008206d403a03 0x0000008206d403a0 0xe0401ce07fc03f0e 0xde0401ce07fc03f0

def z594 : W := mkw 0x0094000002110000 0x0009400000211000 0x71b627000631ff0f 0xb71b627000631ff0

def z595 : W := mkw 0x00000800c0022080 0x000000800c002208 0x9038381fc03e30ff 0x79038381fc03e30f

def z596 : W := mkw 0x0000400000848008 0x0000040000084800 0x2047c00001c1c000 0x82047c00001c1c00

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x4180270000000002 0xb418027000000000

def z598 : W := mkw 0x0940000025000000 0x0094000002500000 0x0f8000003e000008 0x20f8000003e00000

def z599 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x8fc03be07fc01308 0x68fc03be07fc0130

def z600 : W := mkw 0x3dffcd75f7ffeddc 0x63dffcd75f7ffedd 0xffffffffffffffff 0xffffffffffffffff

def z601 : W := mkw 0x1202fef1c8c6fecb 0x21202fef1c8c6fec 0xf04ffff3c1cfffc7 0xdf04ffff3c1cfffc

def z602 : W := mkw 0x0096051400000000 0x0009605140000000 0x61b6271c06003f0f 0xb61b6271c06003f0

def z603 : W := mkw 0x2f697aa07decba0f 0x02f697aa07decba0 0xefc9ffe07fce3f0e 0xfefc9ffe07fce3f0

def z604 : W := mkw 0x4fffbfdf48003002 0x04fffbfdf4800300 0xcffffffff800300f 0xfcffffffff800300

def z605 : W := mkw 0x0096051402114550 0x4009605140211455 0x1036201c0031f0ff 0x31036201c0031f0f

def z606 : W := mkw 0x0628780ad8aeb0aa 0x80628780ad8aeb0a 0xbe7ff81ff9fff0ff 0xfbe7ff81ff9fff0f

def z607 : W := mkw 0x04280800d82a30a2 0x804280800d82a30a 0x9e380000783e30fd 0x79e380000783e30f

def z608 : W := mkw 0x000008206f517f53 0x4000008206f517f5 0xb00000007ff1fffc 0x0b00000007ff1fff

def z609 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0x61c027e007c03f0e 0xb61c027e007c03f0

def z610 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x4fc9ffe380000002 0xf4fc9ffe38000000

def z611 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000000 0xf0fc000000000000

def z612 : W := mkw 0x1b42fef1c0c6ecc8 0x21b42fef1c0c6ecc 0xffcffff3c1cfecc7 0xfffcffff3c1cfecc

def z613 : W := mkw 0x294140002584800c 0x0294140002584800 0x0041c00001c00000 0x00041c00001c0000

def z614 : W := mkw 0x2ffd728037bd800c 0x02ffd728037bd800 0xffffffe07fffc00f 0xfffffffe07fffc00

def z615 : W := mkw 0x0ffe3fbeff7b7ff3 0xc0ffe3fbeff7b7ff 0xfffe3fffffffffff 0xffffe3ffffffffff

def z616 : W := mkw 0x2dfd000037390004 0x02dfd00003739000 0x3fb600003e31c00d 0xb3fb600003e31c00

def z617 : W := mkw 0x000244100084c448 0x0000244100084c44 0xf04fc41041cfecc7 0xdf04fc41041cfecc

def z618 : W := mkw 0x1628f86bd8eeb8aa 0xa1628f86bd8eeb8a 0x8e49d8e3f9ce0000 0x48e49d8e3f9ce000

def z619 : W := mkw 0x4200338e00000000 0x04200338e0000000 0x0000230c00000000 0x00000230c0000000

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x0030200c00301038 0x20030200c0030103

def z621 : W := mkw 0x6ffdf2cb37bd800c 0x06ffdf2cb37bd800 0xbfffd8e3ffffc00d 0xfbfffd8e3ffffc00

def z622 : W := mkw 0x46bfb55f00000000 0x046bfb55f0000000 0x0e3ff81f80000003 0x70e3ff81f8000000

def z623 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x00080003800e0000 0x000080003800e000

def z624 : W := mkw 0x1096c57502d5cd58 0x61096c57502d5cd5 0x61c7c7e007c1cf00 0x861c7c7e007c1cf0

def z625 : W := mkw 0x3ffffc7bfffffcee 0xa3ffffc7bfffffce 0xfffffcfffffffcff 0xffffffcfffffffcf

def z626 : W := mkw 0x0096051400000000 0x0009605140000000 0x51b6271c003030ff 0xb51b6271c003030f

def z627 : W := mkw 0x24bf451412bdc55c 0x424bf451412bdc55 0x71bfe71c063fffff 0xb71bfe71c063ffff

def z628 : W := mkw 0x0096051402114550 0x4009605140211455 0x71b6071c0631cff1 0x871b6071c0631cff

def z629 : W := mkw 0x0094010400000000 0x0009401040000000 0x01b0230c00000000 0x201b0230c0000000

def z630 : W := mkw 0x2dfd40002795800c 0x02dfd40002795800 0x2fffc00007c1c001 0xf2fffc00007c1c00

def z631 : W := mkw 0x2dfd000037390004 0x02dfd00003739000 0x9fb800007e3e000d 0x79fb800007e3e000

def z632 : W := mkw 0x04be051e923b45f0 0xc04be051e923b45f 0x103e001f803fc0f1 0x0103e001f803fc0f

def z633 : W := mkw 0x0000000002110110 0x4000000000211011 0x0000000006301338 0x0000000000630133

def z634 : W := mkw 0x4bd7b7d500000000 0x04bd7b7d50000000 0x4fc7ffe000000002 0xf4fc7ffe00000000

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000006003f0c 0x02000000006003f0

def z636 : W := mkw 0x4fffb7ff25400a01 0x04fffb7ff25400a0 0x6fffffff87c00f03 0xf6fffffff87c00f0

def z637 : W := mkw 0x2b407aa07ffdba0f 0x02b407aa07ffdba0 0xffc03fe07fffff0e 0xfffc03fe07fffff0

def z638 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xee401ce079c02c06 0xdee401ce079c02c0

def z639 : W := mkw 0x3dfd4820f7ffeccc 0x23dfd4820f7ffecc 0xbfffc0007fffeccd 0xfbfffc0007fffecc

def z640 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0x500fdcf3800fecc3 0x0500fdcf3800fecc

def z641 : W := mkw 0x6dffc7d537bd800c 0x06dffc7d537bd800 0xffffc7e07fffc00d 0xfffffc7e07fffc00

def z642 : W := mkw 0x0000000002114550 0x4000000000211455 0x718027000631fffe 0xb718027000631fff

def z643 : W := mkw 0x0b403a8048003002 0x00b403a804800300 0xcfc03fe07800300e 0xfcfc03fe07800300

def z644 : W := mkw 0x2096451437bdc55c 0x42096451437bdc55 0xf1b6271c7fffffff 0xbf1b6271c7ffffff

def z645 : W := mkw 0x02963d1eca1375f2 0xc02963d1eca1375f 0x71b63f1f8631ffff 0xb71b63f1f8631fff

def z646 : W := mkw 0x0094000002110000 0x0009400000211000 0x103600000031c001 0x0103600000031c00

def z647 : W := mkw 0x0096051402114550 0x4009605140211455 0x61b6271c0601cf03 0xb61b6271c0601cf0

def z648 : W := mkw 0x02003aa048403a03 0x002003aa048403a0 0xce003fe078003f0e 0x7ce003fe078003f0

def z649 : W := mkw 0x04280800d02a2080 0x004280800d02a208 0x9e381813f83e20cf 0x79e381813f83e20c

def z650 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000003030fc 0x010000000003030f

def z651 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0x9049d8f3c1ce20c7 0x59049d8f3c1ce20c

def z652 : W := mkw 0x20004800ffbfb0ae 0x820004800ffbfb0a 0xb00000007ffff0fc 0x0b00000007ffff0f

def z653 : W := mkw 0x59d7cff5c0c6ecc8 0x259d7cff5c0c6ecc 0xf1cfdff3c1cfecc7 0xdf1cfdff3c1cfecc

def z654 : W := mkw 0x0002051400004550 0x4000205140000455 0x6180271c06003ffe 0xb6180271c06003ff

def z655 : W := mkw 0x2dfd010437390114 0x42dfd01043739011 0x0fb0230c3e301338 0x20fb0230c3e30133

def z656 : W := mkw 0x10024c30c0c6ecc8 0x210024c30c0c6ecc 0xf006041041cfecc7 0x9f006041041cfecc

def z657 : W := mkw 0x7ffffffff7ffeccc 0x27ffffffff7ffecc 0xffffffffffffeccf 0xfffffffffffffecc

def z658 : W := mkw 0x0628300a00000000 0x00628300a0000000 0x0e30200c00000000 0x20e30200c0000000

def z659 : W := mkw 0x0f683aa07d683a03 0x00f683aa07d683a0 0xfff83fe07ffe3f0f 0xffff83fe07ffe3f0

def z660 : W := mkw 0x0096051400000000 0x0009605140000000 0x0036001c00000001 0x00036001c0000000

def z661 : W := mkw 0x0002041000004440 0x0000204100000444 0x7036241c0031fcff 0xb7036241c0031fcf

def z662 : W := mkw 0x06be351e1a395572 0xc06be351e1a39557 0x7fb6271c3e31ffff 0xb7fb6271c3e31fff

def z663 : W := mkw 0x1096cd75c2d7edd8 0x61096cd75c2d7edd 0xf07fdcffc1ffecf7 0xdf07fdcffc1ffecf

def z664 : W := mkw 0x0094010402114550 0x4009401040211455 0x31b0230c0631fffc 0x231b0230c0631fff

def z665 : W := mkw 0x0096051402114550 0x4009605140211455 0x51b6271c0031c0f3 0xb51b6271c0031c0f

def z666 : W := mkw 0x0096051400004440 0x0009605140000444 0x71b6271c0001ecc7 0xb71b6271c0001ecc

def z667 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xf0401ce041cfecc6 0xdf0401ce041cfecc

def z668 : W := mkw 0x29d540002795800c 0x029d540002795800 0xafc7c0007fc1c00c 0xfafc7c0007fc1c00

def z669 : W := mkw 0x2ffd3aa07f793a07 0x02ffd3aa07f793a0 0xeff03fe07ff03f0e 0xfeff03fe07ff03f0

def z670 : W := mkw 0x0002041002114550 0x4000204100211455 0x700604100631ffff 0x9700604100631fff

def z671 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e08381ff80e30f2 0x48e08381ff80e30f

def z672 : W := mkw 0x1202fc71c8c6fcca 0x21202fc71c8c6fcc 0xfe4ffcf3f9cffccf 0xffe4ffcf3f9cffcc

def z673 : W := mkw 0x4f69baeb6d403a03 0x04f69baeb6d403a0 0x8e49d8e3f9c00000 0x48e49d8e3f9c0000

def z674 : W := mkw 0x0bd6379402114550 0x40bd637940211455 0x7ff63ffc0631ffff 0xf7ff63ffc0631fff

def z675 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x8e4038e079c0300e 0x78e4038e079c0300

def z676 : W := mkw 0x0000000002114550 0x4000000000211455 0x200000000601cf00 0x0200000000601cf0

def z677 : W := mkw 0x0200380ac80230a2 0x80200380ac80230a 0x9008381fc00e30f7 0x59008381fc00e30f

def z678 : W := mkw 0x142acc71d0eeecc8 0x2142acc71d0eeecc 0xfe7fdcf3f9ffeccf 0xffe7fdcf3f9ffecc

def z679 : W := mkw 0x2fff7d1effbff5fe 0xc2fff7d1effbff5f 0xffffff1fffffffff 0xfffffff1ffffffff

def z680 : W := mkw 0x094008206d403a03 0x0094008206d403a0 0xafc000007fc03f0c 0xfafc000007fc03f0

def z681 : W := mkw 0x1002cc71c2d7edd8 0x61002cc71c2d7edd 0xf04fdcf3c7ffffff 0xdf04fdcf3c7fffff

def z682 : W := mkw 0x04bd000000000000 0x004bd00000000000 0x003fc00000000001 0x0003fc0000000000

def z683 : W := mkw 0x2940400037bd800c 0x02940400037bd800 0xbfc000007fffc00c 0xfbfc000007fffc00

def z684 : W := mkw 0x10968d75c2536dd0 0x610968d75c2536dd 0x71b63fff8631ffff 0xb71b63fff8631fff

def z685 : W := mkw 0x2ffd700a37bd800c 0x02ffd700a37bd800 0xbffff81fffffc00f 0xfbffff81fffffc00

def z686 : W := mkw 0x0000082040402800 0x0000008204040280 0x40001ce000002c02 0x040001ce000002c0

def z687 : W := mkw 0x000000002d001203 0x0000000002d00120 0x000000003e001308 0x0000000003e00130

def z688 : W := mkw 0x0b407aa06dc4ba0b 0x00b407aa06dc4ba0 0xffcfffe07fcfff0f 0xfffcfffe07fcfff0

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x6180070006000f00 0x86180070006000f0

def z690 : W := mkw 0x0628300a18281022 0x80628300a1828102 0x9e38200c783e103d 0x79e38200c783e103

def z691 : W := mkw 0x0000000002114550 0x4000000000211455 0x100000000031c0f0 0x0100000000031c0f

def z692 : W := mkw 0x06be3d1ed82a30a2 0x806be3d1ed82a30a 0xdfbe3f1ff83e30ff 0xfdfbe3f1ff83e30f

def z693 : W := mkw 0x0200380ac80230a2 0x80200380ac80230a 0x8e00381ff80030fe 0x78e00381ff80030f

def z694 : W := mkw 0x462abfdfd82a30a2 0x8462abfdfd82a30a 0xde383ffff83e30ff 0x7de383ffff83e30f

def z695 : W := mkw 0x2dff451437bdc55c 0x42dff451437bdc55 0xbfffc01c7fffc0fd 0xfbfffc01c7fffc0f

def z696 : W := mkw 0x0f683aaafd6a3aa3 0x80f683aaafd6a3aa 0x8e4818e3f9ce0000 0x48e4818e3f9ce000

def z697 : W := mkw 0x0096051402114550 0x4009605140211455 0x3036001c0631fffd 0x03036001c0631fff

def z698 : W := mkw 0x4ffff7df00848008 0x04ffff7df0084800 0xffffffffc1cfc007 0xfffffffffc1cfc00

def z699 : W := mkw 0x0dff051402114550 0x40dff05140211455 0x7fffe71c0631ffff 0xf7fffe71c0631fff

def z700 : W := mkw 0x06bc310e1a391132 0xc06bc310e1a39113 0x0fb0230c3e301338 0x20fb0230c3e30133

def z701 : W := mkw 0x0bd63fb46f517f53 0x40bd63fb46f517f5 0xefc63fe07fc1ff0e 0xfefc63fe07fc1ff0

def z702 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x2ff7c0003ff1c008 0xa2ff7c0003ff1c00

def z703 : W := mkw 0x0b403aa040402800 0x00b403aa04040280 0xefc03fe041c02c06 0xfefc03fe041c02c0

def z704 : W := mkw 0x0428080ad82a30a2 0x80428080ad82a30a 0x9038001ff83e30fd 0x09038001ff83e30f

def z705 : W := mkw 0x2000400037bd800c 0x02000400037bd800 0xb04fc0007fffc00d 0xdb04fc0007fffc00

def z706 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf0001cf3c1cfecc6 0x0f0001cf3c1cfecc

def z707 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x5fffffff8030000f 0xf5fffffff8030000

def z708 : W := mkw 0x4fffb7df00004440 0x04fffb7df0000444 0x5fffffff8001c0c3 0xf5fffffff8001c0c

def z709 : W := mkw 0x2dff845137390004 0x02dff84513739000 0x4fffdcf3be30000b 0xf4fffdcf3be30000

def z710 : W := mkw 0x2dfd428037bd820d 0x02dfd428037bd820 0xbfffc3007fffc30d 0xfbfffc3007fffc30

def z711 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x8e00000079c00000 0x08e00000079c0000

def z712 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xde383f1ff83e3fff 0x7de383f1ff83e3ff

def z713 : W := mkw 0x0dfd804100000000 0x00dfd80410000000 0x0fffd8e380000001 0xf0fffd8e38000000

def z714 : W := mkw 0x462bb7df00000000 0x0462bb7df0000000 0x4009ffff80000002 0x04009ffff8000000

def z715 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38181ff83e00fd 0x79e38181ff83e00f

def z716 : W := mkw 0x0002845100004440 0x0000284510000444 0x604fdcf38001cc03 0xd604fdcf38001cc0

def z717 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xffffdce07fffc00f 0xfffffdce07fffc00

def z718 : W := mkw 0x1b42f6d1ad86d6cb 0x21b42f6d1ad86d6c 0x1f8fe313be0fd3c9 0x21f8fe313be0fd3c

def z719 : W := mkw 0x6fffb7df37390114 0x46fffb7df3739011 0x4fffffffbe30133b 0xf4fffffffbe30133

def z720 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0fc9fbe380000000 0x60fc9fbe38000000

def z721 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x0e4fd8e380000000 0x40e4fd8e38000000

def z722 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x4ff9ffff80000003 0xf4ff9ffff8000000

def z723 : W := mkw 0x0b403aa0ed423a83 0x00b403aa0ed423a8 0xefc83fe3ffce3f0e 0xfefc83fe3ffce3f0

def z724 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e79d8e380000001 0x70e79d8e38000000

def z725 : W := mkw 0x4fffb7df00004550 0x44fffb7df0000455 0x6fffffff86003fff 0xf6fffffff86003ff

def z726 : W := mkw 0x44bf8d7f6d403a03 0x044bf8d7f6d403a0 0xa03fc01fffc03f0d 0x0a03fc01fffc03f0

def z727 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0x8000000041ce2cc0 0x08000000041ce2cc

def z728 : W := mkw 0x0096855502114550 0x4009685550211455 0x61c7c7e00601cf00 0x861c7c7e00601cf0

def z729 : W := mkw 0x10024c30d8eefcea 0xa10024c30d8eefce 0xf036241c79fffcff 0xbf036241c79fffcf

def z730 : W := mkw 0x2bd5780aef97b0ae 0x82bd5780aef97b0a 0x21c7f81f87c1f0f2 0x821c7f81f87c1f0f

def z731 : W := mkw 0x10024c30c0c6ecc8 0x210024c30c0c6ecc 0xf006040041cfecc4 0x8f006040041cfecc

def z732 : W := mkw 0x4ffdb2cb02110000 0x04ffdb2cb0211000 0x3fffd8e38631c00d 0xf3fffd8e38631c00

def z733 : W := mkw 0x0094000002110000 0x0009400000211000 0x31ffc0000631c00d 0xf31ffc0000631c00

def z734 : W := mkw 0x14284820d0eeecc8 0x214284820d0eeecc 0xbe38000079ffeccd 0x7be38000079ffecc

def z735 : W := mkw 0x06beb55f00000000 0x006beb55f0000000 0x4fffffff80000003 0xf4fffffff8000000

def z736 : W := mkw 0x4fffb7df1a395572 0xc4fffb7df1a39557 0x7fffffffbe31ffff 0xf7fffffffbe31fff

def z737 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xbe38381ffe3e3fff 0x7be38381ffe3e3ff

def z738 : W := mkw 0x0002845102114550 0x4000284510211455 0x704fdcf38631ffff 0xd704fdcf38631fff

def z739 : W := mkw 0x4fffb7df02114440 0x04fffb7df0211444 0x7fffffff8631eccf 0xf7fffffff8631ecc

def z740 : W := mkw 0x0000400000848008 0x0000040000084800 0xbe4fc00079cfc00d 0xfbe4fc00079cfc00

def z741 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x5fffffff800020c7 0xf5fffffff800020c

def z742 : W := mkw 0x0bd6bff56f517f53 0x40bd6bff56f517f5 0xfffffffffff1ffff 0xffffffffffff1fff

def z743 : W := mkw 0x4fffb7df10280020 0x84fffb7df1028002 0x4fffffff80300033 0xf4fffffff8030003

def z744 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0x6fc03fe03fc03f0a 0xa6fc03fe03fc03f0

def z745 : W := mkw 0x0dff845102114440 0x00dff84510211444 0x7fffdcf38631eccf 0xf7fffdcf38631ecc

def z746 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc03fe07fc03f02 0xcefc03fe07fc03f0

def z747 : W := mkw 0x30004820fffffcee 0xa30004820fffffce 0xb00000007ffffcfc 0x0b00000007ffffcf

def z748 : W := mkw 0x0096051402114550 0x4009605140211455 0x31b6231c0631fffd 0x231b6231c0631fff

def z749 : W := mkw 0x4f69b2cb18281022 0x84f69b2cb1828102 0x0e79f8efb8301038 0x60e79f8efb830103

def z750 : W := mkw 0x10004820c2d7ecc8 0x210004820c2d7ecc 0xb000000047ffeccc 0x0b000000047ffecc

def z751 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0xa04fd8e3c1cfc000 0xca04fd8e3c1cfc00

def z752 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xf000040041cfecc6 0x9f000040041cfecc

def z753 : W := mkw 0x1094c965c2d7a998 0x61094c965c2d7a99 0x81f9fbefc7fe1338 0x681f9fbefc7fe133

def z754 : W := mkw 0x5202bfffc8427ec3 0x25202bfffc8427ec 0x40003fff80003fc2 0x040003fff80003fc

def z755 : W := mkw 0x2dfd410437bd811c 0x42dfd410437bd811 0xffffe70c7fffff3f 0xfffffe70c7fffff3

def z756 : W := mkw 0x0002845100000000 0x0000284510000000 0x407ffcff80000003 0xf407ffcff8000000

def z757 : W := mkw 0x0b403aaaed423aa3 0x80b403aaaed423aa 0xfff03ffffff03fff 0xffff03ffffff03ff

def z758 : W := mkw 0x0002845100000000 0x0000284510000000 0x507ffcff803030ff 0xf507ffcff803030f

def z759 : W := mkw 0x1002cc71c8c6fcca 0x21002cc71c8c6fcc 0xf04fdcf3f9cffccf 0xdf04fdcf3f9cffcc

def z760 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x6fffffff8631df3b 0xf6fffffff8631df3

def z761 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x7fffffff8031ecf7 0xf7fffffff8031ecf

def z762 : W := mkw 0x46bfb7df02114550 0x446bfb7df0211455 0x71bfffff8631ffff 0xb71bfffff8631fff

def z763 : W := mkw 0x4f69b3cf00000000 0x04f69b3cf0000000 0x0e49fbef80000000 0x40e49fbef8000000

def z764 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc83ff3ffc03f0f 0xfefc83ff3ffc03f0

def z765 : W := mkw 0x10004820c8c6fcea 0xa10004820c8c6fce 0xb000000041cffcf4 0x0b000000041cffcf

def z766 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fcfffe380000002 0xf4fcfffe38000000

def z767 : W := mkw 0x0bd63fb46f517f53 0x40bd63fb46f517f5 0x9e7618fc79f1c0f1 0x49e7618fc79f1c0f

def z768 : W := mkw 0x0b403aa0ed423a83 0x00b403aa0ed423a8 0xfff83ffffffe3fff 0xffff83ffffffe3ff

def z769 : W := mkw 0x10004820d8eeb8aa 0xa10004820d8eeb8a 0x9000000079fe30fc 0x09000000079fe30f

def z770 : W := mkw 0x3dff8c71f77b6cc4 0x23dff8c71f77b6cc 0x4fb01cf3be302cca 0x24fb01cf3be302cc

def z771 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffdfe380000001 0xf4fffdfe38000000

def z772 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc03fe07fc00f02 0xfefc03fe07fc00f0

def z773 : W := mkw 0x2dfd400035ac800c 0x02dfd400035ac800 0xbfffc00079cfc005 0xfbfffc00079cfc00

def z774 : W := mkw 0x02003800c8023082 0x002003800c802308 0x9e38381ff83e30ff 0x79e38381ff83e30f

def z775 : W := mkw 0x0d6802aab56a0aa1 0x80d6802aab56a0aa 0x71f807ff87fe0ff1 0x871f807ff87fe0ff

def z776 : W := mkw 0x0096051402114550 0x4009605140211455 0x71b6270c0631fffc 0xa71b6270c0631fff

def z777 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffe01c7fffc00f 0xfbfffe01c7fffc00

def z778 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffe3007fffd30d 0xfbfffe3007fffd30

def z779 : W := mkw 0x44bf855f00000000 0x044bf855f0000000 0x007fd8ff80000001 0x4007fd8ff8000000

def z780 : W := mkw 0x6202f7df37bd800c 0x06202f7df37bd800 0xf0003fffffffc00e 0x0f0003fffffffc00

def z781 : W := mkw 0x1002c47100c4cc48 0x21002c47100c4cc4 0xf04fdcf3c1cfcc07 0xdf04fdcf3c1cfcc0

def z782 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb000000041fffcfc 0x0b000000041fffcf

def z783 : W := mkw 0x10964d34c2d7edd8 0x610964d34c2d7edd 0xb036001c41ffecf5 0x0b036001c41ffecf

def z784 : W := mkw 0x46bfb7df02114550 0x446bfb7df0211455 0x503fffff8031fff3 0x0503fffff8031fff

def z785 : W := mkw 0x062ab45b00004440 0x0062ab45b0000444 0x7e7ffcff8031fcff 0xf7e7ffcff8031fcf

def z786 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38381ff83e30f3 0x49e38381ff83e30f

def z787 : W := mkw 0x2d6b451435acc55c 0x42d6b451435acc55 0xce49e71c79ce3ff2 0x4ce49e71c79ce3ff

def z788 : W := mkw 0x4f6bb6db00004440 0x04f6bb6db0000444 0x7e4fdcf38001ecc7 0xd7e4fdcf38001ecc

def z789 : W := mkw 0x2dfd410437bd811c 0x42dfd410437bd811 0xbfffc3007fffc30d 0xfbfffc3007fffc30

def z790 : W := mkw 0x06be3d1eda3b75f2 0xc06be3d1eda3b75f 0xef8e1f03fe0fcf00 0xcef8e1f03fe0fcf0

def z791 : W := mkw 0x0094010402114550 0x4009401040211455 0x71b0270c0631fffe 0xb71b0270c0631fff

def z792 : W := mkw 0x4f69b2cb25000000 0x04f69b2cb2500000 0x8e49d8e3f9c00000 0x48e49d8e3f9c0000

def z793 : W := mkw 0x5ffd7baec0c6ecc8 0x25ffd7baec0c6ecc 0xbfb0230c41cfecc4 0x2bfb0230c41cfecc

def z794 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xde783cfff83e30ff 0xfde783cfff83e30f

def z795 : W := mkw 0x4fffb7df00004440 0x04fffb7df0000444 0x4fffffff80002cc3 0xf4fffffff80002cc

def z796 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf07fdcf3c1ffeccf 0xff07fdcf3c1ffecc

def z797 : W := mkw 0x46bfb7df00000000 0x046bfb7df0000000 0x407fffff80000003 0xd407fffff8000000

def z798 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xcfc03fe07fc03f0a 0x6cfc03fe07fc03f0

def z799 : W := mkw 0x5202bfffc8427ce2 0xa5202bfffc8427ce 0x40003fff80003cf2 0x040003fff80003cf

def z800 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x5fffffff8631d3fb 0xf5fffffff8631d3f

def z801 : W := mkw 0x0b42b6d100004440 0x00b42b6d10000444 0x7fcffff38601ffcf 0xf7fcffff38601ffc

def z802 : W := mkw 0x4202b7df00004550 0x44202b7df0000455 0x704fffff8001fff7 0xd704fffff8001fff

def z803 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x6fffffff8601fff3 0xf6fffffff8601fff

def z804 : W := mkw 0x4fffb7df02110110 0x44fffb7df0211011 0x6fffffff86303f3f 0xf6fffffff86303f3

def z805 : W := mkw 0x2dffc55537bdc55c 0x42dffc55537bdc55 0xffffffffffffffff 0xffffffffffffffff

def z806 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x1e79f8ff803030ff 0x71e79f8ff803030f

def z807 : W := mkw 0x0bd6b7d502114550 0x40bd6b7d50211455 0x7fffffff8631ffff 0xf7fffffff8631fff

def z808 : W := mkw 0x0096855502114550 0x4009685550211455 0x71f7e7fc0631ffff 0xb71f7e7fc0631fff

def z809 : W := mkw 0x6ffd338e3f391207 0x06ffd338e3f39120 0x0fb0230c3e301308 0x20fb0230c3e30130

def z810 : W := mkw 0x1000c861c0c6ecc8 0x21000c861c0c6ecc 0xb04fd8e3c1cfecc5 0xdb04fd8e3c1cfecc

def z811 : W := mkw 0x30004820fffffecf 0x230004820fffffec 0xb00000007fffffcc 0x0b00000007fffffc

def z812 : W := mkw 0x0b403aaaed423aa3 0x80b403aaaed423aa 0xefc03fe3ffc03f0e 0xfefc03fe3ffc03f0

def z813 : W := mkw 0x30004820f7ffeddc 0x630004820f7ffedd 0xb00000007ffffffc 0x0b00000007ffffff

def z814 : W := mkw 0x162af47b18ecdc6a 0xa162af47b18ecdc6 0x6e77e4ec39f1dc38 0xa6e77e4ec39f1dc3

def z815 : W := mkw 0x49d787d500000000 0x049d787d50000000 0x41ffffff80000003 0xf41ffffff8000000

def z816 : W := mkw 0x29d5400037bd800c 0x029d5400037bd800 0xbfc7c0007fffc00c 0xfbfc7c0007fffc00

def z817 : W := mkw 0x0002855500004550 0x4000285550000455 0x40003fff80003ff2 0x040003fff80003ff

def z818 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e49f8e380000002 0x70e49f8e38000000

def z819 : W := mkw 0x0b403aa0ed423a83 0x00b403aa0ed423a8 0xffc03fe07fce3fce 0xfffc03fe07fce3fc

def z820 : W := mkw 0x06283aaad86a3aa3 0x806283aaad86a3aa 0x9e3838fff83e30ff 0x79e3838fff83e30f

def z821 : W := mkw 0x10004820d8eeb8aa 0xa10004820d8eeb8a 0x8000000079ce0000 0x08000000079ce000

def z822 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb040000041cfecc4 0xdb040000041cfecc

def z823 : W := mkw 0x0000000000000000 0x0000000000000000 0x1038381f803030ff 0x71038381f803030f

def z824 : W := mkw 0x44bf855f00000000 0x044bf855f0000000 0x41ffffff80000003 0xf41ffffff8000000

def z825 : W := mkw 0x4f69b2cb02114550 0x44f69b2cb0211455 0x3e49d8e38631fffc 0x43e49d8e38631fff

def z826 : W := mkw 0x6ffd328a37390004 0x06ffd328a3739000 0x0fb000003e300008 0x20fb000003e30000

def z827 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fcfdff380000003 0xd4fcfdff38000000

def z828 : W := mkw 0x26bd7aa05afdba0f 0x026bd7aa05afdba0 0x503fffe0003fff03 0x0503fffe0003fff0

def z829 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xa000000041cfcc00 0x0a000000041cfcc0

def z830 : W := mkw 0x4f6bb7df00000000 0x04f6bb7df0000000 0x4e79ffff80000003 0x74e79ffff8000000

def z831 : W := mkw 0x0096051402114550 0x4009605140211455 0x61b6271c0631fffa 0xa61b6271c0631fff

def z832 : W := mkw 0x10004820dafffdfa 0xe10004820dafffdf 0xb00000007ffffffc 0x0b00000007ffffff

def z833 : W := mkw 0x6dfd438437bd800c 0x06dfd438437bd800 0xbfffc3007fffc00d 0xfbfffc3007fffc00

def z834 : W := mkw 0x4fffb7df18281022 0x84fffb7df1828102 0xdffffffff83e103f 0xfdffffffff83e103

def z835 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf1cfdcf3c7cfeccf 0xff1cfdcf3c7cfecc

def z836 : W := mkw 0x4fffb7df02110110 0x44fffb7df0211011 0x5fffffff863033ff 0xf5fffffff863033f

def z837 : W := mkw 0x0202b45100000000 0x00202b4510000000 0x4e4ffcf380000003 0xf4e4ffcf38000000

def z838 : W := mkw 0x24bd400037bd800c 0x024bd400037bd800 0xbe3fc0007fffc00d 0x7be3fc0007fffc00

def z839 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0x2000000001c1ecc0 0x02000000001c1ecc

def z840 : W := mkw 0x6ffd338e3f391026 0x86ffd338e3f39102 0x0fb0230c3e301038 0x20fb0230c3e30103

def z841 : W := mkw 0x0002845100000000 0x0000284510000000 0x400fdcf380000003 0x0400fdcf38000000

def z842 : W := mkw 0x0628b04b00000000 0x00628b04b0000000 0x0e79f8ff80000003 0x70e79f8ff8000000

def z843 : W := mkw 0x09d7845100000000 0x009d784510000000 0x41cfdcf380000003 0xd41cfdcf38000000

def z844 : W := mkw 0x4fffb7df27114550 0x44fffb7df2711455 0xfffffffffff1ffff 0xffffffffffff1fff

def z845 : W := mkw 0x4ffdb2cb00000000 0x04ffdb2cb0000000 0x0ff9d8e380000000 0x60ff9d8e38000000

def z846 : W := mkw 0x49d78fd5d82a30a2 0x849d78fd5d82a30a 0xd1c7c7e0783e30fc 0x8d1c7c7e0783e30f

def z847 : W := mkw 0x1002cc71c0c6edd8 0x61002cc71c0c6edd 0xf04fdcf3c1cffff7 0xdf04fdcf3c1cffff

def z848 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffc0107fffe0cf 0xfbfffc0107fffe0c

def z849 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04fdcf3c7cfffcf 0xdf04fdcf3c7cfffc

def z850 : W := mkw 0x0628382ad86a38a2 0x80628382ad86a38a 0xfff83ffffffe3fff 0xffff83ffffffe3ff

def z851 : W := mkw 0x4ffdb2cb00000000 0x04ffdb2cb0000000 0x0e7fd8e380000001 0x40e7fd8e38000000

def z852 : W := mkw 0x0200382048403802 0x0020038204840380 0xefc03fe07fc03f0e 0xfefc03fe07fc03f0

def z853 : W := mkw 0x1f68faebfdeebaab 0xa1f68faebfdeebaa 0x8e49d8e3f9ce0000 0x48e49d8e3f9ce000

def z854 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4ff9ffff80000002 0x64ff9ffff8000000

def z855 : W := mkw 0x0fffb45b00000000 0x00fffb45b0000000 0x4ffffcff80000003 0xf4ffffcff8000000

def z856 : W := mkw 0x0096051402114550 0x4009605140211455 0x71b0271c0631fffe 0x271b0271c0631fff

def z857 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc03fe07fc01f08 0xeefc03fe07fc01f0

def z858 : W := mkw 0x4f69b2cb10280000 0x04f69b2cb1028000 0x8e49d8e3f80e0000 0x48e49d8e3f80e000

def z859 : W := mkw 0x0002cc7140c4a808 0x00002cc7140c4a80 0xf04fdcf3c1cfec07 0xdf04fdcf3c1cfec0

def z860 : W := mkw 0x4f69b2cb25000000 0x04f69b2cb2500000 0xafc9d8e3ffc0000c 0xfafc9d8e3ffc0000

def z861 : W := mkw 0x0096051402114550 0x4009605140211455 0x71be3f1f8631ffff 0xf71be3f1f8631fff

def z862 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4e7fffff80000003 0x44e7fffff8000000

def z863 : W := mkw 0x1202bc7bc8427ce2 0xa1202bc7bc8427ce 0x40001cf380002cc2 0x040001cf380002cc

def z864 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e49d8f380000003 0x50e49d8f38000000

def z865 : W := mkw 0x06283aaad86a3aa3 0x806283aaad86a3aa 0xfe783ffff9fe3fff 0xffe783ffff9fe3ff

def z866 : W := mkw 0x30004820d2ffeccc 0x230004820d2ffecc 0xb000000041ffecc4 0x0b000000041ffecc

def z867 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04ffcffc1cffcf7 0xdf04ffcffc1cffcf

def z868 : W := mkw 0x4fffb7df02110110 0x44fffb7df0211011 0x4fffffff86000303 0xf4fffffff8600030

def z869 : W := mkw 0x4fffb7df18281022 0x84fffb7df1828102 0x5fffffffb83030ff 0xf5fffffffb83030f

def z870 : W := mkw 0x0428080ad02a20a0 0x80428080ad02a20a 0x9e38181ff83e20ff 0x79e38181ff83e20f

def z871 : W := mkw 0x69d7c7d52795c55c 0x469d7c7d52795c55 0x61c7c7e007c1cf00 0x861c7c7e007c1cf0

def z872 : W := mkw 0x44bf855f00000000 0x044bf855f0000000 0x403fdcff80000003 0x0403fdcff8000000

def z873 : W := mkw 0x0bd6b7d500000000 0x00bd6b7d50000000 0x4fffffff80000003 0xf4fffffff8000000

def z874 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04fdce3c1cfcc05 0xdf04fdce3c1cfcc0

def z875 : W := mkw 0x4fffb7df02110000 0x04fffb7df0211000 0x7fffffff8631f0ff 0xf7fffffff8631f0f

def z876 : W := mkw 0x0628382ad86a3aa3 0x80628382ad86a3aa 0x9e38381ff83e3fff 0x79e38381ff83e3ff

def z877 : W := mkw 0x10964d34c0c6ecc8 0x210964d34c0c6ecc 0xf1b6271c41cfecc7 0xbf1b6271c41cfecc

def z878 : W := mkw 0x09400aa06d403a03 0x009400aa06d403a0 0xefc007e07fc03f0c 0xfefc007e07fc03f0

def z879 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0xb04fd8f3c1cfe0c7 0xdb04fd8f3c1cfe0c

def z880 : W := mkw 0x0b42b6d100000000 0x00b42b6d10000000 0x4e4fdcf380000003 0xd4e4fdcf38000000

def z881 : W := mkw 0x4202b7df00000000 0x04202b7df0000000 0x400fffff80000003 0x0400fffff8000000

def z882 : W := mkw 0x04bf845100000000 0x004bf84510000000 0x407fdcf380000003 0xd407fdcf38000000

def z883 : W := mkw 0x0002845100000000 0x0000284510000000 0x41cffff380000003 0xf41cffff38000000

def z884 : W := mkw 0x4ffdb3cf00000000 0x04ffdb3cf0000000 0x0e79d8ef80000000 0x40e79d8ef8000000

def z885 : W := mkw 0x0942845125000000 0x0094284512500000 0xefcfdcf3ffc0000f 0xfefcfdcf3ffc0000

def z886 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04fdce3c1cfecc4 0xcf04fdce3c1cfecc

def z887 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x6fffffff8601ff0f 0xf6fffffff8601ff0

def z888 : W := mkw 0x0002845100000000 0x0000284510000000 0x004fd8f380000001 0x4004fd8f38000000

def z889 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x1e7fd8ff8031c0f1 0x41e7fd8ff8031c0f

def z890 : W := mkw 0x46bfb7df00000000 0x046bfb7df0000000 0x003fd8ff80000001 0x0003fd8ff8000000

def z891 : W := mkw 0x10004820e5c6ecc8 0x210004820e5c6ecc 0xb00000007fcfeccc 0x0b00000007fcfecc

def z892 : W := mkw 0x6ffdb2cb37390004 0x06ffdb2cb3739000 0x0ff9d8e3be300008 0x60ff9d8e3be30000

def z893 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf1cfdff3c7cfefc7 0xdf1cfdff3c7cfefc

def z894 : W := mkw 0x46bfb7df00000000 0x046bfb7df0000000 0x4e3fffff80000003 0x74e3fffff8000000

def z895 : W := mkw 0x4ffdb2cb00000000 0x04ffdb2cb0000000 0x0ffff8ff80000003 0xf0ffff8ff8000000

def z896 : W := mkw 0x64bfc55f12bdc55c 0x464bfc55f12bdc55 0x103fc01f803fc0f1 0x0103fc01f803fc0f

def z897 : W := mkw 0x2dfd428037bd800c 0x02dfd428037bd800 0xffffc7e07fffc00d 0xfffffc7e07fffc00

def z898 : W := mkw 0x4ffdb2cb00000000 0x04ffdb2cb0000000 0x4fffffe380000003 0xf4fffffe38000000

def z899 : W := mkw 0x6ffd338e37390114 0x46ffd338e3739011 0x0fb0230c3e301338 0x20fb0230c3e30133

def z900 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xffffe71c7fffffff 0xfffffe71c7ffffff

def z901 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x1e38381fb83e30fb 0x21e38381fb83e30f

def z902 : W := mkw 0x4fffb7df35280000 0x04fffb7df3528000 0xfffffffffffe000f 0xffffffffffffe000

def z903 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38381ff83e00f3 0x79e38381ff83e00f

def z904 : W := mkw 0x10004820edc6fecb 0x210004820edc6fec 0xb000000079cfecc4 0x0b000000079cfecc

def z905 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbff7c0007fffc00c 0xabff7c0007fffc00

def z906 : W := mkw 0x6f69b2cb35280004 0x06f69b2cb3528000 0x0e49d8e3b8000000 0x40e49d8e3b800000

def z907 : W := mkw 0x0096051402114550 0x4009605140211455 0xf1f6271c47f1ffff 0xff1f6271c47f1fff

def z908 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e000000780e0000 0x08e000000780e000

def z909 : W := mkw 0x4fffb7df18281022 0x84fffb7df1828102 0x4fffffffb8000003 0xf4fffffffb800000

def z910 : W := mkw 0x10004820c0c6a888 0x210004820c0c6a88 0xb000000041cfc004 0x0b000000041cfc00

def z911 : W := mkw 0x0002845100000000 0x0000284510000000 0x4047dcf380000002 0x84047dcf38000000

def z912 : W := mkw 0x0096855502114550 0x4009685550211455 0x71b63fff8631ffff 0xb71b63fff8631fff

def z913 : W := mkw 0x0628300a10280000 0x00628300a1028000 0x9e38381ff83e30ff 0x79e38381ff83e30f

def z914 : W := mkw 0x0002c4510084c448 0x00002c4510084c44 0xf04fdcf3c1cfecc7 0xdf04fdcf3c1cfecc

def z915 : W := mkw 0x0096051402114550 0x4009605140211455 0x71f63ffc0631ffff 0xf71f63ffc0631fff

def z916 : W := mkw 0x0002845100004440 0x0000284510000444 0x404fdcf380002cc3 0xd404fdcf380002cc

def z917 : W := mkw 0x4fffb7df12394550 0x44fffb7df1239455 0xfffffffffe3fffff 0xffffffffffe3ffff

def z918 : W := mkw 0x4fffb7df02110000 0x04fffb7df0211000 0x6fffffff8601c003 0xf6fffffff8601c00

def z919 : W := mkw 0x0b4032a02d401a03 0x00b4032a02d401a0 0x6fc03fe03fc01f0a 0xf6fc03fe03fc01f0

def z920 : W := mkw 0x4bd7b7df00000000 0x04bd7b7df0000000 0x41f7ffff80000003 0xb41f7ffff8000000

def z921 : W := mkw 0x1202bef1c8427ec3 0x21202bef1c8427ec 0x40001cf380002cc2 0x040001cf380002cc

def z922 : W := mkw 0x10004820c8c6fcca 0x210004820c8c6fcc 0xb000000079cffccc 0x0b000000079cffcc

def z923 : W := mkw 0x1002c4518086c4c8 0x21002c4518086c4c 0xf04fdcf3c1cfc0c7 0xdf04fdcf3c1cfc0c

def z924 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xeff03ffc7fc03f0f 0xfeff03ffc7fc03f0

def z925 : W := mkw 0x494386d100000000 0x0494386d10000000 0x404fdcf380000003 0xd404fdcf38000000

def z926 : W := mkw 0x0628300a982a10a2 0x80628300a982a10a 0x1e38381fb83e10fb 0x71e38381fb83e10f

def z927 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e30381ff83e30fe 0x29e30381ff83e30f

def z928 : W := mkw 0x10004820fdeefeeb 0xa10004820fdeefee 0xb00000007ffffffc 0x0b00000007ffffff

def z929 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffff800030f3 0xf4fffffff800030f

def z930 : W := mkw 0x10024c30c0c6ecc8 0x210024c30c0c6ecc 0xb006001041cfecc5 0x0b006001041cfecc

def z931 : W := mkw 0x10004820c0c6a888 0x210004820c0c6a88 0x9000000041ce20c4 0x09000000041ce20c

def z932 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffd813ffffc00f 0xfbfffd813ffffc00

def z933 : W := mkw 0x4ffdb3cf00000000 0x04ffdb3cf0000000 0x4ff9ffef80000002 0xf4ff9ffef8000000

def z934 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x6fffffff86000f03 0xf6fffffff86000f0

def z935 : W := mkw 0x4f69b2cb10280000 0x04f69b2cb1028000 0x9e79d8e3f83e000d 0x79e79d8e3f83e000

def z936 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x6fffffff8600000f 0xf6fffffff8600000

def z937 : W := mkw 0x10024c30edc6fecb 0x210024c30edc6fec 0xf18627107fcfffcf 0xbf18627107fcfffc

def z938 : W := mkw 0x0002845100000000 0x0000284510000000 0x404fdce380000000 0xc404fdce38000000

def z939 : W := mkw 0x0b403aaa6d403a23 0x80b403aaa6d403a2 0xefc03fec7fc03f3e 0xfefc03fec7fc03f3

def z940 : W := mkw 0x4fffb7df25000000 0x04fffb7df2500000 0x4fffffffbe00000b 0xf4fffffffbe00000

def z941 : W := mkw 0x0096051402114550 0x4009605140211455 0xffb6271c7e31ffff 0xfffb6271c7e31fff

def z942 : W := mkw 0x1202befbc8427ee3 0xa1202befbc8427ee 0x40003fff80003ff2 0x040003fff80003ff

def z943 : W := mkw 0x0202b45b00000000 0x00202b45b0000000 0x404ffcff80000003 0xd404ffcff8000000

def z944 : W := mkw 0x4fffb7df2d001203 0x04fffb7df2d00120 0xefffffffffc0130f 0xfefffffffffc0130

def z945 : W := mkw 0x2dfd400a37bd800c 0x02dfd400a37bd800 0xbfffc01fffffc00d 0xfbfffc01fffffc00

def z946 : W := mkw 0x0b403aaa6d403a03 0x00b403aaa6d403a0 0xefc03fffffc03f0e 0xfefc03fffffc03f0

def z947 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb000001041cfecc7 0x1b000001041cfecc

def z948 : W := mkw 0x4296b7df00000000 0x04296b7df0000000 0x41ffffff80000003 0xf41ffffff8000000

def z949 : W := mkw 0x0dff855502114550 0x40dff85550211455 0x7fffffff8631ffff 0xf7fffffff8631fff

def z950 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xef803fe07fc03f0e 0x2ef803fe07fc03f0

def z951 : W := mkw 0x1002cc71c0c6a888 0x21002cc71c0c6a88 0xf04fdcf3c1cfc007 0xdf04fdcf3c1cfc00

def z952 : W := mkw 0x0002041000004440 0x0000204100000444 0x71b6271c0631ffff 0xb71b6271c0631fff

def z953 : W := mkw 0x0628382ad86a38a2 0x80628382ad86a38a 0xde383cfff83e3cff 0x7de383cfff83e3cf

def z954 : W := mkw 0x0000804100000000 0x0000080410000000 0x004fd8e380000001 0xd004fd8e38000000

def z955 : W := mkw 0x6dfd410e37bd800c 0x06dfd410e37bd800 0xbfffc00c7fffc00d 0xfbfffc00c7fffc00

def z956 : W := mkw 0x06beb55f02114550 0x406beb55f0211455 0x7fffffff8631ffff 0xf7fffffff8631fff

def z957 : W := mkw 0x0096051402114550 0x4009605140211455 0x71ffe71c0631ffff 0xf71ffe71c0631fff

def z958 : W := mkw 0x1002cc71c8c6fecb 0x21002cc71c8c6fec 0xf04fdcf3c1cfffc7 0xdf04fdcf3c1cfffc

def z959 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x9fffc0007fffc009 0x69fffc0007fffc00

def z960 : W := mkw 0x4fffb7df2d001203 0x04fffb7df2d00120 0x4fffffffb8000003 0xf4fffffffb800000

def z961 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xffc83fe07fce3f0f 0xfffc83fe07fce3f0

def z962 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x4fffffff86303ffb 0xf4fffffff86303ff

def z963 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z964 : W := mkw 0x06bebd5fda3b75f2 0xc06bebd5fda3b75f 0xfffffffffe3fffff 0xffffffffffe3ffff

def z965 : W := mkw 0x4f6bb6db00000000 0x04f6bb6db0000000 0x4e7ffcff80000003 0xf4e7ffcff8000000

def z966 : W := mkw 0x2ffd328a3f391227 0x82ffd328a3f39122 0x0fb0230c3e301338 0x20fb0230c3e30133

def z967 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffc0007fffc001 0xcbfffc0007fffc00

def z968 : W := mkw 0x0dfd400010ac8008 0x00dfd400010ac800 0xbfffc00079ffc00d 0xfbfffc00079ffc00

def z969 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38381ff83e10f9 0x69e38381ff83e10f

def z970 : W := mkw 0x0628300a982a10a2 0x80628300a982a10a 0x1e38001fb83e00f1 0x01e38001fb83e00f

def z971 : W := mkw 0x10964d34dafffdfa 0xe10964d34dafffdf 0xf1b6271c7fffffff 0xbf1b6271c7ffffff

def z972 : W := mkw 0x2428400037bd800c 0x02428400037bd800 0xbe7fc0007fffc00d 0xfbe7fc0007fffc00

def z973 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x6fc9ffe386003f0e 0xf6fc9ffe386003f0

def z974 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xfe4fdcf3f9cfeccf 0xffe4fdcf3f9cfecc

def z975 : W := mkw 0x0628382ad86a38a2 0x80628382ad86a38a 0xbe38381ff9fe3cff 0x7be38381ff9fe3cf

def z976 : W := mkw 0x4dff87df00000000 0x04dff87df0000000 0x41ffdfff80000003 0xd41ffdfff8000000

def z977 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38201ff83e30fd 0x29e38201ff83e30f

def z978 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffff8030103b 0xf4fffffff8030103

def z979 : W := mkw 0x1202bc71c8427cc2 0x21202bc71c8427cc 0x40003cf380003cc2 0x040003cf380003cc

def z980 : W := mkw 0x0002845100000000 0x0000284510000000 0x504fdcf3800020c7 0xd504fdcf3800020c

def z981 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x7fffffff86303fff 0xf7fffffff86303ff

def z982 : W := mkw 0x0000000000000000 0x0000000000000000 0x61c03fe006003f0e 0xf61c03fe006003f0

def z983 : W := mkw 0x4fffb7df00004440 0x04fffb7df0000444 0x7fffffff8601ffcf 0xf7fffffff8601ffc

def z984 : W := mkw 0x10004820c2d7edd8 0x610004820c2d7edd 0xb000000047cfefc4 0x0b000000047cfefc

def z985 : W := mkw 0x0096845100000000 0x0009684510000000 0x41ffdcf380000003 0xf41ffdcf38000000

def z986 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x41ffffff80000003 0x841ffffff8000000

def z987 : W := mkw 0x1002cd75c0c6edd8 0x61002cd75c0c6edd 0xf07fffffc1ffffff 0xff07fffffc1fffff

def z988 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x0ffffbff80000001 0x60ffffbff8000000

def z989 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x0e7ff8ff80000003 0x70e7ff8ff8000000

def z990 : W := mkw 0x0096051402114550 0x4009605140211455 0xf1be271c463fffff 0xff1be271c463ffff

def z991 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0x9e4fc00079cfc001 0x49e4fc00079cfc00

def z992 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc01fe07fc02f06 0xdefc01fe07fc02f0

def z993 : W := mkw 0x2dfd410437bd811c 0x42dfd410437bd811 0xbfffe31c7ffff3ff 0xfbfffe31c7ffff3f

def z994 : W := mkw 0x10004820d0eeece8 0xa10004820d0eeece 0xb000000041ffecf4 0x0b000000041ffecf

def z995 : W := mkw 0x0202b6d100000000 0x00202b6d10000000 0x404ffff380000003 0xd404ffff38000000

def z996 : W := mkw 0x1002cd75c0c6edd8 0x61002cd75c0c6edd 0xf04fdff3c1cfefc7 0xdf04fdff3c1cfefc

def z997 : W := mkw 0x4bd7b7df00000000 0x04bd7b7df0000000 0x41cfffff80000003 0xd41cfffff8000000

def z998 : W := mkw 0x4fffb7df00004550 0x44fffb7df0000455 0x7fffffff8001fff7 0xf7fffffff8001fff

def z999 : W := mkw 0x10004820c0c6edd8 0x610004820c0c6edd 0xb000000041cffff4 0x0b000000041cffff

def z1000 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0xefffffffc1c00007 0xfefffffffc1c0000

def z1001 : W := mkw 0x0628b04b00000000 0x00628b04b0000000 0x0e49d8e380000000 0x40e49d8e38000000

def z1002 : W := mkw 0x4202b7df00000000 0x04202b7df0000000 0x4047ffff80000002 0x84047ffff8000000

def z1003 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xbe78381ff9fe30ff 0xfbe78381ff9fe30f

def z1004 : W := mkw 0x0096051402114550 0x4009605140211455 0x71b6271c0631fff3 0x871b6271c0631fff

def z1005 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffff8000300f 0xf4fffffff8000300

def z1006 : W := mkw 0x2dfd400a37bd802c 0x82dfd400a37bd802 0xbfffc00c7fffc03d 0xfbfffc00c7fffc03

def z1007 : W := mkw 0x442b845b00000000 0x0442b845b0000000 0x404fdcf380000003 0xd404fdcf38000000

def z1008 : W := mkw 0x30004820f7ffa88c 0x230004820f7ffa88 0xb00000007fffc00c 0x0b00000007fffc00

def z1009 : W := mkw 0x0fffb6d100000000 0x00fffb6d10000000 0x4ffffff380000003 0xf4ffffff38000000

def z1010 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e7ff81ff83e30ff 0xf9e7ff81ff83e30f

def z1011 : W := mkw 0x46bfb7df00000000 0x046bfb7df0000000 0x41bfffff80000003 0xb41bfffff8000000

def z1012 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfbfc0007fffc00d 0x2bfbfc0007fffc00

def z1013 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04fdcf3c1cfccc1 0xcf04fdcf3c1cfccc

def z1014 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb030201c41fffcff 0x3b030201c41fffcf

def z1015 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xeff03fec7ff03f3e 0xfeff03fec7ff03f3

def z1016 : W := mkw 0x0dff855500000000 0x00dff85550000000 0x4fffffff80000003 0xf4fffffff8000000

def z1017 : W := mkw 0x1002cd75c0c6ecc8 0x21002cd75c0c6ecc 0xf04fffffc1cfecc7 0xdf04fffffc1cfecc

def z1018 : W := mkw 0x094286d100000000 0x0094286d10000000 0x41cfdff380000003 0xd41cfdff38000000

def z1019 : W := mkw 0x1002cd75c0c6edd8 0x61002cd75c0c6edd 0xf1cfffffc7cfffff 0xff1cfffffc7cffff

def z1020 : W := mkw 0x09400aa065402a01 0x009400aa065402a0 0xefc01fe07fc02f0e 0xfefc01fe07fc02f0

def z1021 : W := mkw 0x10024c30c0c6ecc8 0x210024c30c0c6ecc 0xf000041041cfecc6 0x0f000041041cfecc

def z1022 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0x9000000041cfc0c0 0x09000000041cfc0c

def z1023 : W := mkw 0x0d6b845100000000 0x00d6b84510000000 0x4e4fdcf380000003 0xd4e4fdcf38000000

def z1024 : W := mkw 0x2d69400037bd800c 0x02d69400037bd800 0xbe4fc0007fffc00d 0xdbe4fc0007fffc00

def z1025 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0x804fd8e3c1cfc000 0x4804fd8e3c1cfc00

def z1026 : W := mkw 0x0b403aa0ed423aa3 0x80b403aa0ed423aa 0xefc03fe07fc03ffe 0xfefc03fe07fc03ff

def z1027 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0x10000000000fecc0 0x010000000000fecc

def z1028 : W := mkw 0x10944820c2d7ecc8 0x210944820c2d7ecc 0xb1b6000047ffeccd 0xbb1b6000047ffecc

def z1029 : W := mkw 0x0b403aa0ed423a83 0x00b403aa0ed423a8 0xefc03ff3ffc03fce 0xfefc03ff3ffc03fc

def z1030 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffe00c7fffd03d 0xfbfffe00c7fffd03

def z1031 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf07ffcffc1cfecc7 0xff07ffcffc1cfecc

def z1032 : W := mkw 0x0000804100000000 0x0000080410000000 0x0049d8f380000003 0x50049d8f38000000

def z1033 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0xefc027e07fc03f0e 0xfefc027e07fc03f0

def z1034 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc027e07fc03f0c 0xaefc027e07fc03f0

def z1035 : W := mkw 0x30964c30f7ffeccc 0x230964c30f7ffecc 0xf1b604107fffeccf 0xbf1b604107fffecc

def z1036 : W := mkw 0x6fffb7df37394554 0x46fffb7df3739455 0x7fffffffbe31ffff 0xf7fffffffbe31fff

def z1037 : W := mkw 0x4fffb7df27110000 0x04fffb7df2711000 0xfffffffffff1c00f 0xffffffffffff1c00

def z1038 : W := mkw 0x6fffb7df37390004 0x06fffb7df3739000 0xeffffffffff0000f 0xfeffffffffff0000

def z1039 : W := mkw 0x4fffb7df02110000 0x04fffb7df0211000 0x7fffffff8631ff0f 0xf7fffffff8631ff0

def z1040 : W := mkw 0x4f6bb6db00000000 0x04f6bb6db0000000 0x4e49dcf380000002 0x44e49dcf38000000

def z1041 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfcfc0007fffc00c 0xcbfcfc0007fffc00

def z1042 : W := mkw 0x10004820d8eefcea 0xa10004820d8eefce 0xb000000079cfecc4 0x0b000000079cfecc

def z1043 : W := mkw 0x0096855502110110 0x4009685550211011 0x41ffffff8630133b 0xf41ffffff8630133

def z1044 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0x904fd8e3c1cfc001 0x4904fd8e3c1cfc00

def z1045 : W := mkw 0x0002855500000000 0x0000285550000000 0x404fffff80000003 0xd404fffff8000000

def z1046 : W := mkw 0x0628300a982a10a2 0x80628300a982a10a 0x1e38201fb83e30ff 0x31e38201fb83e30f

def z1047 : W := mkw 0x4202b6db00000000 0x04202b6db0000000 0x404fdcf380000003 0xd404fdcf38000000

def z1048 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x6fcfdfe38601cf00 0xc6fcfdfe38601cf0

def z1049 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xd04fdcf3c1cfecc3 0x4d04fdcf3c1cfecc

def z1050 : W := mkw 0x4ffdb3cf00000000 0x04ffdb3cf0000000 0x0fc9dbe380000000 0x40fc9dbe38000000

def z1051 : W := mkw 0x4ffdb3cf00000000 0x04ffdb3cf0000000 0x0ffffbef80000001 0xf0ffffbef8000000

def z1052 : W := mkw 0x30004820f5eea88c 0x230004820f5eea88 0x8000000079ce0000 0x08000000079ce000

def z1053 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x7fffffff8631c0ff 0xf7fffffff8631c0f

def z1054 : W := mkw 0x0002845100000000 0x0000284510000000 0x604fdcf380002c07 0xd604fdcf380002c0

def z1055 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xb04fd8f3c1cfecc5 0x4b04fd8f3c1cfecc

def z1056 : W := mkw 0x29d540002795800c 0x029d540002795800 0xbfcfc0007fcfc00d 0xfbfcfc0007fcfc00

def z1057 : W := mkw 0x0002845100000000 0x0000284510000000 0xd04fdcf3c00e0007 0xdd04fdcf3c00e000

def z1058 : W := mkw 0x4fffb7df1a391132 0xc4fffb7df1a39113 0x4fffffffbe30133b 0xf4fffffffbe30133

def z1059 : W := mkw 0x10004820e5c6eec9 0x210004820e5c6eec 0xb000000047cfefc4 0x0b000000047cfefc

def z1060 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xafffc0007fffc008 0xeafffc0007fffc00

def z1061 : W := mkw 0x04280800d02a2080 0x004280800d02a208 0x9e38381ff83e30ff 0x79e38381ff83e30f

def z1062 : W := mkw 0x0f6ab6db00000000 0x00f6ab6db0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1063 : W := mkw 0x49d787d500000000 0x049d787d50000000 0x41c7dff380000002 0x841c7dff38000000

def z1064 : W := mkw 0x400287d500000000 0x0400287d50000000 0x404fdff380000003 0xd404fdff38000000

def z1065 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc01fe07fc03f0c 0xcefc01fe07fc03f0

def z1066 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fbfffff80000003 0x24fbfffff8000000

def z1067 : W := mkw 0x0002855500004550 0x4000285550000455 0x404fffff80003ff3 0xd404fffff80003ff

def z1068 : W := mkw 0x0000c04100848008 0x00000c0410084800 0xb04fd8e3c1cfc005 0xdb04fd8e3c1cfc00

def z1069 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbe7fc0007fffc00d 0x4be7fc0007fffc00

def z1070 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb000000047cfffcc 0x0b000000047cfffc

def z1071 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xf180270047cfffce 0xbf180270047cfffc

def z1072 : W := mkw 0x0b4032a02d401a03 0x00b4032a02d401a0 0x6fc027e03fc03f0e 0xb6fc027e03fc03f0

def z1073 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffff80003f03 0xf4fffffff80003f0

def z1074 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xd04fdcf3c1cfc0c3 0xdd04fdcf3c1cfc0c

def z1075 : W := mkw 0x4fffb7df25000000 0x04fffb7df2500000 0xcffffffff9c00003 0xfcffffffff9c0000

def z1076 : W := mkw 0x10944924c2d7edd8 0x610944924c2d7edd 0xb1b0230c47fffffc 0x2b1b0230c47fffff

def z1077 : W := mkw 0x0940082065402800 0x0094008206540280 0xefc03fe07fc03f0e 0xfefc03fe07fc03f0

def z1078 : W := mkw 0x4f6bb6db00000000 0x04f6bb6db0000000 0x0e4fd8f380000001 0x40e4fd8f38000000

def z1079 : W := mkw 0x1202bd7fc8427df2 0xe1202bd7fc8427df 0x40003fff80003ff2 0x040003fff80003ff

def z1080 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc01fe07fc00f0c 0xfefc01fe07fc00f0

def z1081 : W := mkw 0x1b407aa0edc6fecb 0x21b407aa0edc6fec 0xbf8023007fcfffcc 0x2bf8023007fcfffc

def z1082 : W := mkw 0x0d68400035ac8008 0x00d68400035ac800 0xbfffc0007fffc00d 0xfbfffc0007fffc00

def z1083 : W := mkw 0x24bd400012bd800c 0x024bd400012bd800 0xbe7fc00079ffc00d 0xfbe7fc00079ffc00

def z1084 : W := mkw 0x4097855500000000 0x0409785550000000 0x404fdcf380000003 0xd404fdcf38000000

def z1085 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb008000041cfecc5 0x5b008000041cfecc

def z1086 : W := mkw 0x10964d34c2d7edd8 0x610964d34c2d7edd 0xf186070047cfefc4 0x8f186070047cfefc

def z1087 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x9fffc00079ffc001 0xf9fffc00079ffc00

def z1088 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x9e38001ff83e00f1 0x49e38001ff83e00f

def z1089 : W := mkw 0x0094010402114550 0x4009401040211455 0x31b0231c0631ffff 0x331b0231c0631fff

def z1090 : W := mkw 0x10004820c8c6fecb 0x210004820c8c6fec 0xb000000041cfffc4 0x0b000000041cfffc

def z1091 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffc0007ffff0fd 0xfbfffc0007ffff0f

def z1092 : W := mkw 0x4fffb7df12390000 0x04fffb7df1239000 0xfffffffffe3fc00f 0xffffffffffe3fc00

def z1093 : W := mkw 0x49d787d500000000 0x049d787d50000000 0x41cfdfe380000000 0xc41cfdfe38000000

def z1094 : W := mkw 0x6fffb7df27110004 0x06fffb7df2711000 0x4fffffff86000003 0xf4fffffff8600000

def z1095 : W := mkw 0x4fffb7df00004550 0x44fffb7df0000455 0x4fffffff800000f3 0xf4fffffff800000f

def z1096 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0xae4fc00079cfc000 0xcae4fc00079cfc00

def z1097 : W := mkw 0x30964d34f7ffeddc 0x630964d34f7ffedd 0xf1b6271c7fffffff 0xbf1b6271c7ffffff

def z1098 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x8e38381ff83e30fa 0x68e38381ff83e30f

def z1099 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x7fffffff8001c007 0xf7fffffff8001c00

def z1100 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x4fc9dfe380000000 0xc4fc9dfe38000000

def z1101 : W := mkw 0x4002855f00000000 0x04002855f0000000 0x404fdcff80000003 0xd404fdcff8000000

def z1102 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xfff03fe07ff03f0f 0xffff03fe07ff03f0

def z1103 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xbe3e381ff83ff0ff 0xfbe3e381ff83ff0f

def z1104 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04ffcf3c1cffccf 0xff04ffcf3c1cffcc

def z1105 : W := mkw 0x4f6bb7df00004550 0x44f6bb7df0000455 0x4e49ffff80003ff2 0x44e49ffff80003ff

def z1106 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x4e49dce380000002 0xd4e49dce38000000

def z1107 : W := mkw 0x4fffb7df2f111313 0x44fffb7df2f11131 0x4fffffffbe30133b 0xf4fffffffbe30133

def z1108 : W := mkw 0x0b40328025000000 0x00b4032802500000 0xefc03fe07fc03f0e 0xfefc03fe07fc03f0

def z1109 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4ff7ffff80000002 0xa4ff7ffff8000000

def z1110 : W := mkw 0x4fffb7df10280000 0x04fffb7df1028000 0xdffffffff83e30ff 0xfdffffffff83e30f

def z1111 : W := mkw 0x462ab7df00000000 0x0462ab7df0000000 0x4e7fffff80000003 0xf4e7fffff8000000

def z1112 : W := mkw 0x0628300a982a10a2 0x80628300a982a10a 0x9e38201ff83e10fd 0x79e38201ff83e10f

def z1113 : W := mkw 0x4f6bb7df00000000 0x04f6bb7df0000000 0x0e49d8ff80000000 0x40e49d8ff8000000

def z1114 : W := mkw 0x0000000002114550 0x4000000000211455 0x71b0271c0631ffff 0xb71b0271c0631fff

def z1115 : W := mkw 0x3dfd4820f7ffeccc 0x23dfd4820f7ffecc 0xbfb000007fffeccc 0x2bfb000007fffecc

def z1116 : W := mkw 0x0096855500000000 0x0009685550000000 0x407fdcff80000003 0xd407fdcff8000000

def z1117 : W := mkw 0x4fffb7df08001002 0x04fffb7df0800100 0x4fffffffb800100b 0xf4fffffffb800100

def z1118 : W := mkw 0x2dfd410437bd811c 0x42dfd410437bd811 0xbfffc00c7fffc03d 0xfbfffc00c7fffc03

def z1119 : W := mkw 0x0940400025848008 0x0094040002584800 0xbe4fc00079cfc005 0xdbe4fc00079cfc00

def z1120 : W := mkw 0x0002cc51c086a088 0x00002cc51c086a08 0xf04fdcf3c1cfe0c7 0xdf04fdcf3c1cfe0c

def z1121 : W := mkw 0x4fffb7df25000201 0x04fffb7df2500020 0x4fffffff86000303 0xf4fffffff8600030

def z1122 : W := mkw 0x4bd7b7df00000000 0x04bd7b7df0000000 0x4fc7ffff80000002 0xf4fc7ffff8000000

def z1123 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0xbe7fc00079ffc00d 0xfbe7fc00079ffc00

def z1124 : W := mkw 0x062ab45b00000000 0x0062ab45b0000000 0x4e4fdcf380000003 0xd4e4fdcf38000000

def z1125 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefcfffe07fc03f0f 0xfefcfffe07fc03f0

def z1126 : W := mkw 0x49d787d502114550 0x449d787d50211455 0x71cfdff38601efc7 0xd71cfdff38601efc

def z1127 : W := mkw 0x46bfb55f00000000 0x046bfb55f0000000 0x4e7ffcff80000003 0xf4e7ffcff8000000

def z1128 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x5fffffff8031f0ff 0xf5fffffff8031f0f

def z1129 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0x904fd8f3c1cfe0c7 0x5904fd8f3c1cfe0c

def z1130 : W := mkw 0x09d4400027958008 0x009d440002795800 0xbfffc0007fffc00d 0xfbfffc0007fffc00

def z1131 : W := mkw 0x10004820d0eeecc8 0x210004820d0eeecc 0xb000000079ffeccc 0x0b000000079ffecc

def z1132 : W := mkw 0x1202bff5c8427fd3 0x61202bff5c8427fd 0x40003fff80003ff2 0x040003fff80003ff

def z1133 : W := mkw 0x10004820c0c6a888 0x210004820c0c6a88 0xa000000041ce2c04 0x0a000000041ce2c0

def z1134 : W := mkw 0x06283aaad86a3aa3 0x806283aaad86a3aa 0xffb83ffffe3e3fff 0xfffb83ffffe3e3ff

def z1135 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x7fffffff8631cff3 0xf7fffffff8631cff

def z1136 : W := mkw 0x0096051402114550 0x4009605140211455 0x51b6271c0631fffb 0x251b6271c0631fff

def z1137 : W := mkw 0x0096855502114550 0x4009685550211455 0x507fdcff8031c0f3 0xd507fdcff8031c0f

def z1138 : W := mkw 0x4097855502114550 0x4409785550211455 0x71b7e71c0631ffff 0xb71b7e71c0631fff

def z1139 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffef80000000 0xe4fffffef8000000

def z1140 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf1cffff3c1cfecc7 0xff1cffff3c1cfecc

def z1141 : W := mkw 0x494182c100000000 0x0494182c10000000 0x0049d8e380000000 0x40049d8e38000000

def z1142 : W := mkw 0x10004820edc6ba8b 0x210004820edc6ba8 0xa00000007fce3f0c 0x0a00000007fce3f0

def z1143 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0fc9d8e380000000 0xf0fc9d8e38000000

def z1144 : W := mkw 0x4fffb7df02110000 0x04fffb7df0211000 0x4fffffff8630000b 0xf4fffffff8630000

def z1145 : W := mkw 0x6fffb7df37390004 0x06fffb7df3739000 0x7fffffffbe31c00f 0xf7fffffffbe31c00

def z1146 : W := mkw 0x0428400010ac8008 0x00428400010ac800 0xbe4fc00079cfc005 0xdbe4fc00079cfc00

def z1147 : W := mkw 0x4fffb7df10280000 0x04fffb7df1028000 0xcffffffff80e0003 0xfcffffffff80e000

def z1148 : W := mkw 0x0b42b6d12d001203 0x00b42b6d12d00120 0x4fcffff3be00130b 0xf4fcffff3be00130

def z1149 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xffc63fe07fc1ff0f 0xfffc63fe07fc1ff0

def z1150 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e4fd8e380000001 0xd0e4fd8e38000000

def z1151 : W := mkw 0x19d6c7f527d5cf59 0x619d6c7f527d5cf5 0x61c7c7e007c1cf00 0x861c7c7e007c1cf0

def z1152 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xffffc4007fffec0f 0xfffffc4007fffec0

def z1153 : W := mkw 0x4f6bb7df00000000 0x04f6bb7df0000000 0x4e4fffff80000003 0xd4e4fffff8000000

def z1154 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04ffff3c1cfffc7 0xdf04ffff3c1cfffc

def z1155 : W := mkw 0x2dfd410437bd800c 0x02dfd410437bd800 0xbfffe30c7fffc00d 0xfbfffe30c7fffc00

def z1156 : W := mkw 0x0b40b2c100000000 0x00b40b2c10000000 0x0e49d8e380000000 0x40e49d8e38000000

def z1157 : W := mkw 0x4fffb7df02110110 0x44fffb7df0211011 0x4fffffff80300033 0xf4fffffff8030003

def z1158 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x4fffffff8001c003 0xf4fffffff8001c00

def z1159 : W := mkw 0x2940400037bd800c 0x02940400037bd800 0xbfcfc0007fffc00d 0xfbfcfc0007fffc00

def z1160 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x7fffffff8601efc7 0xf7fffffff8601efc

def z1161 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38181ff83e20f7 0x59e38181ff83e20f

def z1162 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xe04fdce3c1cfec06 0xde04fdce3c1cfec0

def z1163 : W := mkw 0x0002845100000000 0x0000284510000000 0x61cffff386003f0f 0xf61cffff386003f0

def z1164 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xb04fd8f3c1cfc0c5 0xdb04fd8f3c1cfc0c

def z1165 : W := mkw 0x34bfc55592bfc5dc 0x634bfc55592bfc5d 0x103fc01f803fc0f1 0x0103fc01f803fc0f

def z1166 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0x8e00000079ce0000 0x08e00000079ce000

def z1167 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x8e4fc00079cfc000 0x48e4fc00079cfc00

def z1168 : W := mkw 0x4fffb7df10280000 0x04fffb7df1028000 0x5fffffff803e0003 0xf5fffffff803e000

def z1169 : W := mkw 0x4ffdb3cf02110110 0x44ffdb3cf0211011 0x0ff9fbef86301338 0x60ff9fbef8630133

def z1170 : W := mkw 0x0b4032a02d401a03 0x00b4032a02d401a0 0xefc027e07fc01f0c 0xfefc027e07fc01f0

def z1171 : W := mkw 0x30004820e7d7eccc 0x230004820e7d7ecc 0xb000000047cfecc4 0x0b000000047cfecc

def z1172 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e79f8ef80000000 0x60e79f8ef8000000

def z1173 : W := mkw 0x4fffb7df00004550 0x44fffb7df0000455 0x4fffffff80000f03 0xf4fffffff80000f0

def z1174 : W := mkw 0x19404820e5c6ecc8 0x219404820e5c6ecc 0xbfc000007fcfeccc 0xfbfc000007fcfecc

def z1175 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xbfb8381ffe3e30ff 0xfbfb8381ffe3e30f

def z1176 : W := mkw 0x4fffb7df00004440 0x04fffb7df0000444 0x7fffffff8031fcff 0xf7fffffff8031fcf

def z1177 : W := mkw 0x0094010402114550 0x4009401040211455 0x31b6230c0631fffd 0xb31b6230c0631fff

def z1178 : W := mkw 0x14bec55f92bfc5f8 0xe14bec55f92bfc5f 0x103fc01f803fc0f1 0x0103fc01f803fc0f

def z1179 : W := mkw 0x6fffb7df35280004 0x06fffb7df3528000 0x4fffffffb8000003 0xf4fffffffb800000

def z1180 : W := mkw 0x20004820ffffbaaf 0x820004820ffffbaa 0xb00000007ffffffc 0x0b00000007ffffff

def z1181 : W := mkw 0x49d787d502114550 0x449d787d50211455 0x71ffffff8631ffff 0xf71ffffff8631fff

def z1182 : W := mkw 0x1000c861c0c6a888 0x21000c861c0c6a88 0xf04fdce3c1cfec07 0xdf04fdce3c1cfec0

def z1183 : W := mkw 0x4f6bb7df00000000 0x04f6bb7df0000000 0x4e49dfe380000000 0x44e49dfe38000000

def z1184 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0x704fdcf381cfecc3 0x8704fdcf381cfecc

def z1185 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x1e38001fb83e00f9 0x21e38001fb83e00f

def z1186 : W := mkw 0x10024d34c0c6edd8 0x610024d34c0c6edd 0xf000271c41cffff6 0x0f000271c41cffff

def z1187 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0xefc007e07fc00f00 0xcefc007e07fc00f0

def z1188 : W := mkw 0x2d69400035ac800c 0x02d69400035ac800 0xbfcfc0007fcfc00d 0xfbfcfc0007fcfc00

def z1189 : W := mkw 0x4bd7b7df00000000 0x04bd7b7df0000000 0x41c7dfe380000000 0x841c7dfe38000000

def z1190 : W := mkw 0x00004820c0c6a888 0x000004820c0c6a88 0xf04fdcf3c1cfecc7 0xdf04fdcf3c1cfecc

def z1191 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0x9e7fc00079ffc00d 0x79e7fc00079ffc00

def z1192 : W := mkw 0x4fffb7df2d001203 0x04fffb7df2d00120 0x6fffffffbe003f0f 0xf6fffffffbe003f0

def z1193 : W := mkw 0x0096855502114550 0x4009685550211455 0x71bfe71f8631ffff 0xb71bfe71f8631fff

def z1194 : W := mkw 0x4f6bb6db00000000 0x04f6bb6db0000000 0x4fcffff380000003 0xf4fcffff38000000

def z1195 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9fb83b1ffe3e33ff 0x79fb83b1ffe3e33f

def z1196 : W := mkw 0x2f697aaafdeebaaf 0x82f697aaafdeebaa 0x8e49d8e3f9ce0000 0x48e49d8e3f9ce000

def z1197 : W := mkw 0x0096855502114550 0x4009685550211455 0x103fc01f8031c0f1 0x0103fc01f8031c0f

def z1198 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfcfc0007fcfc005 0xdbfcfc0007fcfc00

def z1199 : W := mkw 0x042a845100000000 0x0042a84510000000 0x4e7fdcf380000003 0xf4e7fdcf38000000

def z1200 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x5fffffff8031fff3 0xf5fffffff8031fff

def z1201 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbe7fc00079ffc005 0xdbe7fc00079ffc00

def z1202 : W := mkw 0x06283a8ad82a32a3 0x806283a8ad82a32a 0x9e383b1ff83e33ff 0x79e383b1ff83e33f

def z1203 : W := mkw 0x4fffb7df02114550 0x44fffb7df0211455 0x7fffffff8631cf0f 0xf7fffffff8631cf0

def z1204 : W := mkw 0x4fffb7df08001203 0x04fffb7df0800120 0x4fffffff80001303 0xf4fffffff8000130

def z1205 : W := mkw 0x4bd7b7df02114550 0x44bd7b7df0211455 0x61c7ffff8601fff2 0x861c7ffff8601fff

def z1206 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0xcffffffff800000f 0xfcffffffff800000

def z1207 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xefc03ffc7fc03ffe 0xfefc03ffc7fc03ff

def z1208 : W := mkw 0x4fffb7df00004440 0x04fffb7df0000444 0x6fffffff8001cc03 0xf6fffffff8001cc0

def z1209 : W := mkw 0x4fffb7df00004550 0x44fffb7df0000455 0x5fffffff80303fff 0xf5fffffff80303ff

def z1210 : W := mkw 0x4429804b00000000 0x04429804b0000000 0x0049d8e380000000 0x40049d8e38000000

def z1211 : W := mkw 0x0ffd328a00000000 0x00ffd328a0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1212 : W := mkw 0x0628382ad86a38a2 0x80628382ad86a38a 0x9e7838fff9fe30ff 0x79e7838fff9fe30f

def z1213 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e79d8ff80000001 0x40e79d8ff8000000

def z1214 : W := mkw 0x0002845100000000 0x0000284510000000 0x4049dcf380000002 0x44049dcf38000000

def z1215 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xafffc0007fcfc001 0xfafffc0007fcfc00

def z1216 : W := mkw 0x4f6bb7df00000000 0x04f6bb7df0000000 0x4fc9ffff80000002 0xf4fc9ffff8000000

def z1217 : W := mkw 0x4fffb6db00000000 0x04fffb6db0000000 0x4fffdcf380000003 0xf4fffdcf38000000

def z1218 : W := mkw 0x4fffb7df10280000 0x04fffb7df1028000 0x4fffffffb830000b 0xf4fffffffb830000

def z1219 : W := mkw 0x4fffb7df3d281223 0x84fffb7df3d28122 0x4fffffffbe30133b 0xf4fffffffbe30133

def z1220 : W := mkw 0x0b4032a025400a01 0x00b4032a025400a0 0xefc03fe07fc00f0e 0xfefc03fe07fc00f0

def z1221 : W := mkw 0x4b41b2cb00000000 0x04b41b2cb0000000 0x0041d8e380000000 0x00041d8e38000000

def z1222 : W := mkw 0x1002cc71c8c6fcea 0xa1002cc71c8c6fce 0xf04fdcf3c1cffcf7 0xdf04fdcf3c1cffcf

def z1223 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffe0007ffff00f 0xfbfffe0007ffff00

def z1224 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xdfb83f1ff83e30ff 0xfdfb83f1ff83e30f

def z1225 : W := mkw 0x0942845100000000 0x0094284510000000 0x4fcfdcf380000003 0xf4fcfdcf38000000

def z1226 : W := mkw 0x0b40b2c100000000 0x00b40b2c10000000 0x4fc9ffe380000002 0xf4fc9ffe38000000

def z1227 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffc01c7fffc0fd 0xfbfffc01c7fffc0f

def z1228 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xffffe7007fffc00f 0xfffffe7007fffc00

def z1229 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0xdfffffffc00e0007 0xfdfffffffc00e000

def z1230 : W := mkw 0x4b43b7df00000000 0x04b43b7df0000000 0x4041ffff80000002 0x04041ffff8000000

def z1231 : W := mkw 0x0428000a902a00a0 0x80428000a902a00a 0x9e38201ff83e30ff 0x79e38201ff83e30f

def z1232 : W := mkw 0x0b4032a02d401a03 0x00b4032a02d401a0 0x6fc007e03fc00f00 0x86fc007e03fc00f0

def z1233 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf04fdcf3c1fffcff 0xdf04fdcf3c1fffcf

def z1234 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x5fffffff803000f3 0xf5fffffff803000f

def z1235 : W := mkw 0x4fffb7df08001022 0x84fffb7df0800102 0x4fffffff80001033 0xf4fffffff8000103

def z1236 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xf07fdcffc1ffecf7 0xdf07fdcffc1ffecf

def z1237 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x6fffffff80002c07 0xf6fffffff80002c0

def z1238 : W := mkw 0x4ffdb2cb00000000 0x04ffdb2cb0000000 0x0fcfd8e380000000 0xc0fcfd8e38000000

def z1239 : W := mkw 0x0002845100004440 0x0000284510000444 0x504fdcf38001c0c3 0xd504fdcf38001c0c

def z1240 : W := mkw 0x4dff87d500000000 0x04dff87d50000000 0x4fffdff380000003 0xf4fffdff38000000

def z1241 : W := mkw 0x4fffb7df02110110 0x44fffb7df0211011 0x7fffffff8631d33f 0xf7fffffff8631d33

def z1242 : W := mkw 0x0000804100000000 0x0000080410000000 0x4049dce380000002 0xd4049dce38000000

def z1243 : W := mkw 0x6fffb7df3f391207 0x06fffb7df3f39120 0x4fffffffbe30130b 0xf4fffffffbe30130

def z1244 : W := mkw 0x44bf855f02114550 0x444bf855f0211455 0x707fdcff8031ecf7 0xd707fdcff8031ecf

def z1245 : W := mkw 0x10964d34efd7ffdb 0x610964d34efd7ffd 0xf1b6271c7fffffff 0xbf1b6271c7ffffff

def z1246 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fcfffff80000002 0xc4fcfffff8000000

def z1247 : W := mkw 0x4200b2cb00000000 0x04200b2cb0000000 0x0049d8e380000000 0x40049d8e38000000

def z1248 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffdfff80000001 0xc4fffdfff8000000

def z1249 : W := mkw 0x2dfd400037bd811c 0x42dfd400037bd811 0xbfffc0007fffd33d 0xfbfffc0007fffd33

def z1250 : W := mkw 0x30004820f5eeeccc 0x230004820f5eeecc 0xb000000079cfecc4 0x0b000000079cfecc

def z1251 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4e7fdcff80000003 0xd4e7fdcff8000000

def z1252 : W := mkw 0x0096845102110000 0x0009684510211000 0x71ffdcf38631c00f 0xf71ffdcf38631c00

def z1253 : W := mkw 0x094002a025400a01 0x0094002a025400a0 0x6fc007e03fc00f08 0xa6fc007e03fc00f0

def z1254 : W := mkw 0x4202b7df00000000 0x04202b7df0000000 0x4049ffff80000002 0x44049ffff8000000

def z1255 : W := mkw 0x4f69b2cb2d001203 0x04f69b2cb2d00120 0x0e49d8e3b8000000 0x40e49d8e3b800000

def z1256 : W := mkw 0x44bf855f02114550 0x444bf855f0211455 0x71ffffff8631ffff 0xf71ffffff8631fff

def z1257 : W := mkw 0x0428080ad82a30a2 0x80428080ad82a30a 0x9e38001ff83e30fd 0x79e38001ff83e30f

def z1258 : W := mkw 0x10004820c0c6ecc8 0x210004820c0c6ecc 0xb006000041cfecc5 0x9b006000041cfecc

def z1259 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x4fffffff8600130b 0xf4fffffff8600130

def z1260 : W := mkw 0x06283a8ad82a30a2 0x806283a8ad82a30a 0xde383ffff83e30ff 0x7de383ffff83e30f

def z1261 : W := mkw 0x4bd7b7d500000000 0x04bd7b7d50000000 0x4fcffff380000003 0xf4fcffff38000000

def z1262 : W := mkw 0x6fffb7df37390004 0x06fffb7df3739000 0xdffffffffe3e000f 0xfdffffffffe3e000

def z1263 : W := mkw 0x4f69b2cb2d001203 0x04f69b2cb2d00120 0x0fc9fbe3be001308 0x60fc9fbe3be00130

def z1264 : W := mkw 0x4bd7b7df02114550 0x44bd7b7df0211455 0x71f7ffff8631ffff 0xb71f7ffff8631fff

def z1265 : W := mkw 0x10004820edc6ba8b 0x210004820edc6ba8 0x8000000079ce0000 0x08000000079ce000

def z1266 : W := mkw 0x042a845110280000 0x0042a84511028000 0xde7fdcf3f83e000f 0xfde7fdcf3f83e000

def z1267 : W := mkw 0x10004820c2d7edd8 0x610004820c2d7edd 0xb000000041ffecf4 0x0b000000041ffecf

def z1268 : W := mkw 0x4dff855f00000000 0x04dff855f0000000 0x4fffdcff80000003 0xf4fffdcff8000000

def z1269 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xe04fdcf3c1cfcc03 0xde04fdcf3c1cfcc0

def z1270 : W := mkw 0x4ffdb3cf00000000 0x04ffdb3cf0000000 0x0ff9fbff80000003 0x70ff9fbff8000000

def z1271 : W := mkw 0x6fffb7df3f391026 0x86fffb7df3f39102 0x4fffffffbe30103b 0xf4fffffffbe30103

def z1272 : W := mkw 0x0d69804100000000 0x00d6980410000000 0x0e49d8e380000000 0x40e49d8e38000000

def z1273 : W := mkw 0x10004820efd7ffdb 0x610004820efd7ffd 0xb00000007ffffffc 0x0b00000007ffffff

def z1274 : W := mkw 0x4b42b7df00000000 0x04b42b7df0000000 0x4fcfffff80000003 0xf4fcfffff8000000

def z1275 : W := mkw 0x0002845100000000 0x0000284510000000 0xe04fdcf3c1c00007 0xde04fdcf3c1c0000

def z1276 : W := mkw 0x1002cc71c0c6ecc8 0x21002cc71c0c6ecc 0xe04fdcf3c1cfecc2 0xce04fdcf3c1cfecc

def z1277 : W := mkw 0x4fffb7df00000110 0x44fffb7df0000011 0x4fffffff80001333 0xf4fffffff8000133

def z1278 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xbfffc0007fffff0d 0xfbfffc0007fffff0

def z1279 : W := mkw 0x1628782ad8eefcea 0xa1628782ad8eefce 0xbe30200c79fffcfc 0x2be30200c79fffcf

def z1280 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x0e49f8ff80000002 0x40e49f8ff8000000

def z1281 : W := mkw 0x042a845b00000000 0x0042a845b0000000 0x407fdcff80000003 0xd407fdcff8000000

def z1282 : W := mkw 0x4f69b2cb00000000 0x04f69b2cb0000000 0x4e49ffe380000002 0x44e49ffe38000000

def z1283 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xafcfc0007fcfc00c 0xfafcfc0007fcfc00

def z1284 : W := mkw 0x2dfd400037bd800c 0x02dfd400037bd800 0xffffc7007fffcf0d 0xfffffc7007fffcf0

def z1285 : W := mkw 0x4fffb7df00000000 0x04fffb7df0000000 0x0fffd8ff80000001 0xf0fffd8ff8000000

def z1286 : W := mkw 0x1002cd75c0c6edd8 0x61002cd75c0c6edd 0xf04fdcffc1cfecf7 0xdf04fdcffc1cfecf

def z1287 : W := mkw 0x4297b7df00000000 0x04297b7df0000000 0x4007ffff80000002 0x04007ffff8000000

def z1288 : W := mkw 0x0b403aaaed423aa3 0x80b403aaaed423aa 0xffc83fffffce3fff 0xfffc83fffffce3ff

def z1289 : W := mkw 0x4f69b2cb18281022 0x84f69b2cb1828102 0x0e49d8e3b8000000 0x40e49d8e3b800000

def z1290 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0x9e38181ff83e30fd 0x49e38181ff83e30f

def z1291 : W := mkw 0x39d7c57527d5cd5c 0x639d7c57527d5cd5 0x61c7c7e007c1cf00 0x861c7c7e007c1cf0

def z1292 : W := mkw 0x062ab45b18281022 0x8062ab45b1828102 0x4e7ffcffb830103b 0xf4e7ffcffb830103

def z1293 : W := mkw 0x0628300a902a00a0 0x80628300a902a00a 0x9e38381ff83e00ff 0x79e38381ff83e00f

def z1294 : W := mkw 0x4fffb7df02110000 0x04fffb7df0211000 0x5fffffff8031c003 0xf5fffffff8031c00

def z1295 : W := mkw 0x6fffb7df12390004 0x06fffb7df1239000 0x4fffffff80300003 0xf4fffffff8030000

def z1296 : W := mkw 0x4296b7df02114550 0x44296b7df0211455 0x71ffffff8631ffff 0xf71ffffff8631fff

def z1297 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xffc03ff07fc03fcf 0xfffc03ff07fc03fc

def z1298 : W := mkw 0x4fffb7df25000000 0x04fffb7df2500000 0x6fffffff87c00003 0xf6fffffff87c0000

def z1299 : W := mkw 0x0096855500000000 0x0009685550000000 0x41cfdff380000003 0xd41cfdff38000000

def z1300 : W := mkw 0x4f6bb6db00000000 0x04f6bb6db0000000 0x4e4fdce380000000 0xc4e4fdce38000000

def z1301 : W := mkw 0x0628380ad82a30a2 0x80628380ad82a30a 0xfe383c1ff83e3cff 0xffe383c1ff83e3cf

def z1302 : W := mkw 0x0002845100000000 0x0000284510000000 0x704fdcf38001c007 0xd704fdcf38001c00

def z1303 : W := mkw 0x4fffb7df2f115753 0x44fffb7df2f11575 0x7fffffffbe31ffff 0xf7fffffffbe31fff

def z1304 : W := mkw 0x0dfd400025848008 0x00dfd40002584800 0xbfffc0007fcfc00d 0xfbfffc0007fcfc00

def z1305 : W := mkw 0x4fffb7df25000000 0x04fffb7df2500000 0xefffffffffc03f0f 0xfefffffffffc03f0

def z1306 : W := mkw 0x1002c47180c6ccc8 0x21002c47180c6ccc 0x704fdcf381cfccc3 0xd704fdcf381cfccc

def z1307 : W := mkw 0x0094000002110000 0x0009400000211000 0x71b6271c0631ffff 0xb71b6271c0631fff

def z1308 : W := mkw 0x0b403aa06d403a03 0x00b403aa06d403a0 0xffc03fe07ff03ffe 0xfffc03fe07ff03ff

def z1309 : W := mkw 0x4629b2cb00000000 0x04629b2cb0000000 0x0009d8e380000000 0x00009d8e38000000

def z1310 : W := mkw 0x04bc400012bd8008 0x004bc400012bd800 0xbfffc0007fffc00d 0xfbfffc0007fffc00

def z1311 : W := mkw 0x0096855502114550 0x4009685550211455 0x61cfdff38601cf03 0xd61cfdff38601cf0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z2,z3,z5,z7]),(0,[z0,z1,z2,z3,z5,z8,z9]),(0,[z0,z1,z10,z2,z3,z11,z12]),(0,[z13,z0,z1,z2,z14,z3,z5]),(0,[z0,z1,z2,z15,z3,z5,z12])],[(1,[z0,z1,z2,z3,z16,z12]),(0,[z0,z17,z1,z2,z3,z5,z12]),(0,[z18,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z19,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z12,z21])],[(0,[z22,z0,z1,z2,z3,z5,z12]),(0,[z23,z0,z1,z2,z3,z5,z24]),(0,[z25,z0,z1,z2,z4,z5,z12]),(0,[z13,z0,z26,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z27,z5,z12]),(0,[z0,z28,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z29,z11,z12]),(0,[z0,z1,z2,z30,z3,z31,z5])],[(0,[z0,z32,z1,z2,z3,z5,z12]),(0,[z0,z33,z1,z2,z3,z5,z12]),(0,[z34,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z35,z3,z5,z9]),(0,[z0,z1,z2,z3,z36,z5,z6]),(0,[z37,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z38,z5,z12])],[(0,[z0,z1,z39,z2,z3,z5,z12]),(0,[z0,z1,z2,z40,z3,z5,z12]),(0,[z0,z41,z1,z2,z3,z5,z12]),(0,[z42,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z43,z12]),(0,[z44,z0,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z5,z12,z45])],[(0,[z0,z1,z2,z3,z46,z5,z12]),(0,[z25,z0,z1,z2,z3,z47,z12]),(0,[z0,z1,z19,z48,z3,z5,z12]),(0,[z49,z0,z1,z2,z3,z5,z50]),(0,[z13,z51,z1,z2,z3,z5,z12]),(0,[z0,z52,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z53,z12])],[(0,[z0,z1,z2,z54,z3,z5,z12]),(0,[z0,z1,z2,z55,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z56,z9]),(0,[z0,z57,z2,z48,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z58,z12])],[(0,[z0,z1,z2,z59,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z60,z12]),(0,[z0,z1,z2,z3,z5,z12,z61])]],
   [[],[(0,[z0,z1,z2,z3,z62,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z63]),(0,[z0,z1,z2,z3,z5,z12,z64]),(0,[z0,z1,z2,z65,z3,z5,z12])],[(0,[z0,z1,z2,z66,z3,z5,z12]),(0,[z25,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z67,z2,z3,z5,z12]),(0,[z68,z0,z1,z2,z3,z5,z12]),(1,[z0,z1,z19,z69,z5,z12])],[(0,[z0,z70,z1,z2,z3,z5,z12]),(0,[z0,z1,z69,z3,z11,z5,z12]),(0,[z71,z13,z0,z1,z2,z3,z5]),(0,[z72,z13,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z12,z73]),(0,[z0,z1,z2,z3,z5,z50,z9]),(0,[z0,z1,z2,z3,z74,z5,z12]),(0,[z0,z75,z1,z3,z76,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z77])],[(0,[z78,z0,z1,z2,z3,z5,z12]),(0,[z0,z79,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z3,z80,z12]),(0,[z13,z0,z1,z2,z3,z36,z5]),(0,[z0,z1,z2,z3,z81,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z82]),(0,[z0,z1,z2,z3,z5,z83,z12])],[(0,[z0,z1,z84,z2,z3,z5,z12]),(0,[z85,z0,z1,z2,z3,z5,z86]),(0,[z0,z1,z2,z3,z87,z5,z12]),(0,[z13,z0,z1,z2,z3,z5,z12])],[(0,[z88,z0,z1,z2,z3,z5,z89]),(0,[z0,z1,z2,z3,z90,z5,z12]),(0,[z0,z1,z91,z2,z3,z5,z12]),(0,[z0,z1,z57,z19,z3,z5,z12]),(0,[z13,z0,z92,z1,z2,z3,z5]),(0,[z0,z93,z1,z2,z3,z5,z12])]],
   [[(0,[z88,z0,z1,z2,z30,z3,z5]),(0,[z94,z0,z1,z2,z3,z5,z9]),(0,[z95,z0,z1,z2,z30,z3,z5]),(1,[z51,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z96,z12])],[(0,[z97,z0,z1,z2,z3,z5,z12]),(0,[z0,z17,z1,z2,z3,z5,z6]),(0,[z13,z0,z79,z1,z2,z3,z5]),(0,[z0,z26,z1,z48,z3,z5,z12]),(0,[z0,z1,z98,z2,z3,z5,z12]),(0,[z0,z75,z99,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z100,z12])],[(0,[z101,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z89,z12]),(0,[z13,z0,z1,z2,z3,z5,z47]),(0,[z13,z0,z1,z102,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z103,z12]),(0,[z13,z0,z1,z2,z3,z5,z83])],[(0,[z0,z1,z2,z3,z5,z12,z104]),(0,[z0,z1,z105,z2,z3,z5,z12]),(1,[z0,z1,z2,z3,z106,z12]),(0,[z0,z1,z2,z3,z107,z5,z9]),(0,[z0,z108,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z11,z5,z9]),(0,[z0,z1,z2,z109,z3,z5,z12]),(0,[z0,z1,z2,z3,z110,z5,z12]),(0,[z13,z0,z1,z2,z3,z5,z111]),(0,[z0,z1,z2,z3,z5,z12,z112]),(1,[z0,z75,z1,z3,z76,z12])],[(0,[z0,z1,z39,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z113,z111,z12]),(0,[z13,z0,z108,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z114,z12]),(0,[z0,z1,z115,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z116,z12]),(0,[z25,z13,z0,z1,z2,z5,z12]),(0,[z0,z1,z2,z3,z31,z5,z12])],[(0,[z0,z1,z117,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z118,z5,z12]),(0,[z119,z0,z1,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z11,z5]),(0,[z0,z1,z120,z2,z3,z5,z56]),(0,[z0,z1,z2,z3,z5,z121,z12])],[(1,[z0,z1,z2,z3,z5,z89]),(0,[z0,z122,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z83,z63]),(0,[z0,z1,z2,z3,z123,z5,z12]),(0,[z0,z75,z1,z2,z3,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z5,z124,z12]),(0,[z0,z1,z2,z125,z3,z5,z12]),(0,[z0,z126,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z127,z3,z5]),(0,[z0,z1,z2,z128,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z129,z12]),(1,[z0,z130,z2,z3,z5,z12]),(0,[z13,z0,z1,z131,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z47,z12]),(0,[z0,z1,z2,z3,z132,z5,z12]),(0,[z0,z75,z1,z102,z3,z5,z12]),(0,[z0,z1,z2,z3,z133,z5,z12])],[(0,[z134,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z14,z3,z5,z9]),(0,[z0,z1,z19,z2,z69,z5,z12]),(0,[z0,z1,z120,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z30,z5,z12])],[(0,[z0,z1,z2,z3,z5,z6,z61]),(0,[z0,z135,z2,z3,z36,z5,z12]),(0,[z0,z1,z2,z3,z136,z5,z12])],[(0,[z0,z137,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z138,z3,z5]),(0,[z0,z1,z2,z3,z5,z12,z139]),(0,[z0,z92,z1,z2,z3,z5,z140]),(0,[z0,z1,z2,z3,z5,z12,z141])],[(0,[z85,z0,z1,z2,z30,z3,z5]),(0,[z0,z79,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z63]),(0,[z142,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z143,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z144,z12]),(0,[z0,z1,z2,z3,z5,z145,z12])],[(0,[z0,z1,z146,z2,z3,z5,z12]),(0,[z0,z147,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z148,z6]),(0,[z149,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z150,z12])],[(0,[z151,z0,z39,z2,z3,z5,z12]),(0,[z13,z151,z0,z1,z2,z3,z5]),(0,[z88,z13,z0,z1,z2,z3,z5]),(0,[z95,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z152,z3,z5,z12]),(0,[z0,z1,z2,z153,z3,z5,z12]),(0,[z0,z1,z2,z138,z30,z3,z5])]],
   [[(0,[z154,z0,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z155,z9]),(0,[z0,z1,z156,z2,z3,z5,z12]),(0,[z0,z1,z2,z125,z3,z11,z5]),(0,[z0,z1,z102,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z157])],[(0,[z151,z0,z1,z2,z3,z5,z12]),(0,[z0,z158,z1,z2,z3,z5,z12]),(1,[z0,z84,z2,z3,z5,z12]),(0,[z0,z1,z2,z159,z3,z5,z12]),(0,[z0,z1,z2,z160,z3,z5,z12])],[(0,[z0,z1,z2,z3,z161,z5,z12]),(0,[z49,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z162,z12]),(0,[z0,z163,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z164,z12]),(0,[z0,z1,z2,z3,z5,z12,z165]),(1,[z13,z51,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z3,z5,z43])],[(0,[z0,z1,z2,z3,z5,z12,z166]),(0,[z154,z1,z39,z2,z3,z5,z12]),(0,[z94,z0,z1,z2,z3,z47,z12]),(0,[z0,z1,z167,z2,z3,z5,z12]),(0,[z168,z13,z0,z1,z2,z3,z5]),(0,[z0,z169,z1,z2,z3,z5,z12])],[(0,[z23,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z170,z3,z5,z9]),(0,[z171,z0,z1,z2,z107,z5,z12]),(0,[z0,z2,z3,z36,z5,z111,z12]),(0,[z0,z1,z2,z172,z3,z5,z12])],[(1,[z85,z1,z131,z3,z5,z12]),(1,[z0,z1,z2,z173,z3,z5]),(0,[z0,z1,z2,z3,z5,z9,z61])],[(0,[z0,z174,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z175,z3,z5,z12]),(0,[z0,z1,z176,z2,z3,z5,z12]),(0,[z0,z1,z177,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z9,z63]),(1,[z13,z0,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z12,z178]),(0,[z0,z1,z131,z2,z30,z3,z5]),(0,[z0,z1,z2,z179,z3,z5,z12]),(0,[z180,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z181,z5,z12]),(0,[z25,z0,z1,z2,z5,z121,z12]),(0,[z0,z1,z2,z3,z5,z182,z12]),(0,[z0,z1,z2,z81,z5,z121,z12])],[(0,[z183,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z184,z12]),(0,[z0,z1,z2,z3,z5,z47,z6]),(0,[z0,z108,z26,z2,z3,z5,z12]),(0,[z185,z0,z1,z2,z3,z5,z12]),(0,[z168,z0,z1,z3,z5,z56,z12])],[(0,[z0,z39,z2,z48,z3,z5,z12]),(0,[z0,z1,z120,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z186,z5,z12]),(0,[z187,z0,z167,z2,z3,z5,z12]),(0,[z0,z1,z2,z14,z3,z121,z12])],[(0,[z0,z1,z188,z48,z3,z5,z12]),(0,[z0,z1,z2,z4,z107,z5,z12]),(0,[z0,z1,z2,z4,z11,z5,z12]),(0,[z0,z1,z2,z3,z5,z189,z12]),(0,[z0,z1,z2,z190,z30,z3,z5])],[(0,[z0,z1,z191,z2,z3,z5,z12]),(0,[z0,z137,z1,z2,z3,z5,z6]),(0,[z23,z0,z84,z2,z3,z5,z12])],[(1,[z0,z1,z2,z3,z5,z104]),(0,[z0,z1,z2,z188,z3,z5,z6]),(0,[z0,z1,z131,z2,z3,z5,z9]),(0,[z0,z1,z2,z14,z3,z47,z12]),(0,[z0,z1,z192,z2,z3,z5,z12]),(1,[z0,z1,z2,z3,z5,z20]),(0,[z13,z0,z1,z2,z5,z12,z61])],[(0,[z0,z193,z1,z2,z3,z5,z12]),(0,[z25,z0,z1,z2,z194,z5,z12]),(0,[z0,z1,z2,z3,z36,z5,z9]),(0,[z0,z195,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z196,z5,z12]),(0,[z0,z1,z2,z3,z197,z5,z12]),(0,[z198,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z199,z12])],[(0,[z0,z200,z1,z2,z3,z5,z12])]],
   [[(0,[z0,z201,z1,z2,z3,z5,z12]),(0,[z94,z0,z1,z2,z3,z5,z202]),(0,[z0,z1,z102,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z203,z12]),(0,[z0,z1,z19,z2,z3,z5,z12]),(1,[z0,z204,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z81,z5,z165])],[(0,[z0,z205,z1,z2,z3,z5,z12]),(0,[z206,z0,z1,z2,z3,z5,z12]),(0,[z207,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z208,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z209,z12]),(0,[z0,z1,z2,z3,z210,z5,z12])],[(0,[z211,z0,z1,z2,z3,z5,z12]),(0,[z0,z212,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z213,z12]),(0,[z0,z1,z2,z3,z5,z214,z12]),(0,[z0,z1,z2,z215,z3,z5,z12])],[(0,[z154,z0,z1,z216,z3,z5,z12]),(0,[z0,z217,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z9,z218]),(0,[z0,z1,z2,z3,z5,z219,z12]),(0,[z0,z220,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z221,z12]),(0,[z222,z0,z1,z2,z3,z5,z12])],[(0,[z223,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z224,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z6,z157]),(0,[z171,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z225,z2,z3,z5,z12]),(0,[z0,z1,z226,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z76,z5])],[(0,[z0,z200,z1,z2,z3,z4,z5]),(0,[z25,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z48,z3,z11,z5,z12]),(1,[z0,z1,z67,z3,z5,z12]),(1,[z0,z1,z2,z3,z227,z5])],[(1,[z0,z1,z2,z3,z228,z12]),(1,[z0,z1,z2,z3,z5,z139]),(0,[z0,z1,z2,z175,z3,z5,z6]),(0,[z0,z2,z48,z3,z107,z5,z12]),(0,[z0,z1,z2,z229,z3,z5,z12]),(0,[z0,z1,z2,z3,z80,z107,z12]),(1,[z0,z167,z2,z3,z5,z12]),(0,[z0,z230,z1,z2,z30,z3,z5])],[(0,[z0,z108,z1,z2,z3,z5,z231]),(0,[z0,z232,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z36,z5])]],
   [[(0,[z23,z0,z1,z2,z3,z5,z104]),(0,[z0,z1,z2,z3,z5,z233,z12]),(1,[z168,z0,z1,z3,z5,z56])],[(0,[z0,z1,z2,z234,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z184,z6]),(0,[z13,z0,z1,z2,z3,z5,z155])],[(0,[z235,z0,z1,z2,z3,z5,z12]),(0,[z236,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z237,z5,z12]),(1,[z0,z1,z2,z3,z5,z238])],[(0,[z0,z1,z239,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z240,z12]),(0,[z0,z1,z2,z3,z241,z5,z12])],[(0,[z0,z1,z2,z3,z5,z242,z12]),(0,[z0,z243,z1,z2,z3,z5,z6]),(0,[z0,z108,z1,z2,z3,z36,z12]),(0,[z13,z0,z75,z1,z2,z3,z5]),(0,[z25,z0,z1,z2,z14,z5,z12]),(0,[z0,z51,z1,z2,z3,z5,z12]),(1,[z13,z0,z1,z2,z5,z61])],[(1,[z0,z1,z2,z3,z5,z166]),(0,[z0,z1,z2,z3,z244,z5,z12]),(0,[z245,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z76,z47,z12]),(0,[z0,z1,z2,z30,z3,z107,z5]),(0,[z0,z1,z2,z30,z3,z5,z111])],[(0,[z0,z1,z2,z30,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z9,z157]),(0,[z13,z0,z1,z2,z48,z3,z5]),(0,[z0,z26,z57,z2,z3,z5,z12]),(0,[z0,z122,z1,z2,z3,z107,z12])],[(0,[z0,z130,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z246,z3,z5,z12]),(0,[z0,z1,z247,z2,z3,z5,z12]),(0,[z13,z207,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z248]),(1,[z0,z108,z2,z3,z111,z12])]],
   [[(0,[z72,z0,z1,z2,z3,z5,z12]),(0,[z249,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z250,z12]),(0,[z0,z1,z19,z2,z3,z5,z6]),(0,[z0,z251,z1,z2,z3,z5,z12]),(0,[z0,z1,z57,z3,z76,z5,z12]),(0,[z0,z252,z1,z2,z3,z5,z12]),(0,[z71,z0,z1,z2,z3,z5,z12]),(0,[z0,z253,z1,z2,z3,z5,z12]),(0,[z0,z1,z120,z2,z3,z5,z254])],[(0,[z23,z0,z1,z2,z3,z228,z12]),(0,[z0,z1,z255,z2,z3,z5,z12]),(0,[z34,z0,z1,z2,z3,z47,z12]),(0,[z0,z1,z2,z3,z5,z256,z12]),(0,[z0,z1,z2,z3,z257,z5,z12]),(0,[z0,z1,z2,z258,z3,z5,z12])],[(0,[z259,z0,z1,z2,z3,z5,z12]),(1,[z1,z2,z3,z4,z5,z9]),(0,[z260,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z12]),(0,[z0,z92,z2,z48,z3,z5,z12]),(0,[z0,z1,z2,z261,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z5,z63]),(0,[z262,z0,z1,z2,z3,z5,z12])],[(0,[z151,z0,z1,z2,z3,z5,z242]),(0,[z0,z1,z2,z3,z5,z263,z12]),(1,[z0,z1,z264,z3,z5,z12]),(0,[z0,z265,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z266,z5,z157])],[(0,[z0,z1,z2,z3,z5,z267,z12]),(2,[z51,z1,z2,z3,z5]),(1,[z0,z1,z2,z170,z3,z157])],[(0,[z0,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z268,z3,z5,z12]),(0,[z269,z0,z1,z2,z3,z5,z12]),(0,[z25,z0,z1,z2,z3,z121,z12]),(0,[z270,z0,z1,z2,z30,z3,z5])],[(0,[z0,z1,z2,z3,z271,z5,z12]),(0,[z0,z1,z2,z272,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z273]),(0,[z274,z0,z1,z2,z3,z5,z12])],[(0,[z23,z0,z1,z188,z3,z5,z12]),(0,[z0,z1,z2,z3,z275,z5,z12]),(0,[z0,z1,z2,z14,z81,z5,z12]),(0,[z13,z0,z51,z1,z2,z3,z5])]],
   [[(0,[z154,z0,z1,z2,z276,z5,z12]),(0,[z277,z0,z1,z2,z3,z5,z9]),(0,[z0,z278,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z48,z30,z3,z5]),(0,[z0,z1,z2,z127,z3,z5,z121]),(0,[z279,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z280,z5,z12]),(0,[z281,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z282])],[(1,[z0,z1,z2,z3,z283,z12]),(0,[z0,z1,z2,z173,z3,z5,z12]),(0,[z0,z284,z1,z2,z3,z5,z12]),(0,[z0,z243,z1,z2,z3,z5,z50])],[(0,[z0,z1,z2,z285,z3,z5,z12]),(0,[z0,z1,z2,z286,z3,z5,z12]),(0,[z0,z1,z57,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z111,z12]),(0,[z0,z1,z2,z287,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z288])],[(0,[z154,z0,z1,z2,z3,z16,z12]),(0,[z0,z1,z2,z289,z3,z5,z12]),(0,[z0,z26,z1,z2,z3,z5,z6]),(0,[z0,z1,z48,z3,z76,z5,z12]),(0,[z0,z1,z2,z3,z5,z83,z56])],[(0,[z0,z1,z2,z290,z3,z5,z12]),(0,[z0,z1,z2,z48,z3,z5,z9]),(0,[z13,z0,z1,z2,z3,z5,z56]),(0,[z291,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z45])],[(0,[z0,z292,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z194,z69,z5,z12]),(0,[z94,z0,z1,z2,z30,z3,z5])],[(0,[z88,z0,z1,z2,z3,z5,z293])]],
   [[(0,[z0,z26,z137,z2,z3,z5,z12]),(0,[z0,z1,z2,z173,z3,z4,z5]),(0,[z206,z1,z2,z194,z3,z5,z12]),(0,[z0,z1,z2,z3,z294,z5,z12]),(0,[z0,z1,z2,z3,z5,z295,z12]),(0,[z171,z0,z1,z67,z3,z5,z12]),(0,[z25,z0,z135,z1,z2,z3,z12]),(0,[z187,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z10,z2,z3,z5,z12]),(1,[z0,z1,z2,z30,z5,z155])],[(1,[z0,z1,z2,z296,z5,z12]),(0,[z0,z1,z2,z3,z297,z5,z12]),(0,[z298,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z299,z2,z3,z5,z12]),(0,[z0,z108,z1,z2,z30,z3,z5]),(1,[z0,z135,z2,z3,z36,z12])],[(0,[z171,z0,z1,z2,z35,z5,z12]),(0,[z0,z1,z2,z3,z29,z5,z12])],[(0,[z300,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z287,z3,z11,z5]),(0,[z0,z1,z2,z301,z3,z5,z12]),(0,[z302,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z57,z131,z3,z5,z12]),(0,[z0,z1,z303,z2,z3,z5,z12]),(0,[z88,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z194,z107,z5,z12]),(0,[z0,z1,z2,z194,z11,z5,z12]),(0,[z0,z1,z2,z3,z5,z47,z9]),(1,[z0,z1,z2,z3,z5,z304]),(0,[z95,z0,z1,z2,z3,z5,z12]),(0,[z0,z92,z1,z2,z35,z5,z12]),(1,[z0,z243,z2,z3,z5,z63]),(0,[z305,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z227,z5])],[(0,[z0,z1,z120,z2,z3,z5,z9]),(0,[z0,z1,z2,z306,z3,z5,z12])],[(0,[z307,z0,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z308,z5,z12]),(0,[z0,z1,z2,z3,z5,z6,z12]),(0,[z0,z1,z2,z3,z5,z309,z12]),(0,[z310,z0,z1,z2,z3,z5,z12]),(1,[z0,z99,z2,z3,z5,z12]),(0,[z311,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z5,z121]),(0,[z0,z1,z2,z3,z5,z12,z312])],[(0,[z0,z137,z1,z2,z3,z5,z9]),(1,[z0,z1,z2,z3,z5,z293]),(0,[z0,z1,z2,z313,z3,z5,z12]),(0,[z0,z314,z1,z2,z3,z5,z12]),(0,[z0,z92,z1,z2,z3,z5,z238])]],
   [[(0,[z0,z1,z2,z188,z3,z5,z9]),(0,[z0,z108,z1,z2,z3,z111,z12]),(0,[z0,z135,z1,z264,z3,z5,z12]),(0,[z315,z0,z1,z2,z3,z5,z12]),(0,[z168,z0,z1,z2,z3,z5,z12]),(0,[z316,z13,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z317,z3,z5,z12]),(0,[z0,z1,z2,z3,z318,z5,z12]),(0,[z0,z1,z2,z319,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z320,z12]),(0,[z0,z1,z2,z30,z3,z5,z157])],[(0,[z0,z1,z2,z3,z321,z5,z12])],[(0,[z0,z1,z2,z3,z5,z111,z6]),(0,[z322,z0,z1,z2,z30,z3,z5])],[(1,[z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z323,z12]),(0,[z324,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z325,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z326]),(1,[z0,z1,z2,z327,z3,z5]),(0,[z0,z1,z2,z328,z3,z5,z12])],[(0,[z13,z0,z1,z2,z3,z5,z145]),(0,[z0,z1,z2,z3,z5,z329,z12])],[(0,[z13,z0,z1,z2,z188,z3,z5]),(0,[z0,z1,z330,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z331,z12]),(0,[z0,z79,z26,z2,z3,z5,z12]),(0,[z0,z108,z2,z48,z3,z5,z12]),(0,[z0,z332,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z76,z5])],[(0,[z0,z1,z2,z30,z194,z3,z5]),(1,[z0,z1,z120,z3,z5,z254])]],
   [[(0,[z187,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z81,z5,z6]),(0,[z0,z1,z2,z3,z5,z83,z6]),(0,[z0,z333,z1,z2,z3,z5,z12]),(0,[z49,z0,z1,z2,z30,z3,z5]),(0,[z187,z0,z28,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z334])],[(0,[z85,z0,z1,z2,z3,z5,z12]),(1,[z277,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z335,z12]),(0,[z13,z0,z1,z2,z3,z5,z6]),(0,[z336,z0,z1,z2,z3,z5,z12])],[(0,[z154,z0,z39,z2,z3,z5,z12]),(1,[z0,z1,z2,z337,z5,z12]),(0,[z0,z1,z2,z3,z5,z338,z12]),(0,[z34,z94,z1,z2,z3,z5,z12]),(0,[z0,z243,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z339,z3,z5,z12]),(0,[z0,z1,z2,z170,z30,z3,z5])],[(0,[z0,z1,z2,z3,z5,z12,z340]),(0,[z0,z1,z2,z3,z5,z341,z12]),(0,[z25,z0,z1,z102,z2,z3,z12]),(0,[z0,z1,z342,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z5,z155])],[(0,[z0,z1,z2,z194,z3,z5,z12]),(0,[z0,z1,z303,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z343,z12]),(0,[z0,z1,z2,z3,z5,z344,z12]),(0,[z0,z1,z2,z3,z345,z5,z12]),(0,[z0,z1,z2,z3,z5,z346,z12]),(0,[z0,z1,z2,z3,z5,z12,z347])],[(0,[z95,z1,z2,z3,z5,z6,z12]),(0,[z25,z0,z108,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z266,z5,z12])],[(0,[z94,z1,z2,z3,z5,z47,z12]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z348,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z349]),(0,[z0,z1,z2,z327,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z350,z12])],[(0,[z0,z1,z2,z276,z3,z5,z12]),(0,[z351,z0,z1,z2,z3,z5,z12]),(0,[z0,z243,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z12,z352]),(0,[z0,z1,z2,z3,z5,z353,z12]),(0,[z0,z354,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z355])]],
   [[(0,[z168,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z356,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z254])],[(0,[z206,z1,z2,z3,z5,z12,z9]),(0,[z0,z1,z2,z3,z5,z304,z12]),(0,[z207,z1,z2,z3,z5,z12,z9]),(0,[z0,z195,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z121,z6]),(0,[z0,z92,z1,z2,z107,z5,z12]),(0,[z0,z1,z2,z69,z3,z5,z12]),(1,[z0,z1,z2,z3,z29,z12]),(0,[z0,z1,z2,z3,z266,z5,z83])],[(0,[z0,z75,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z357,z3,z5,z12])],[(0,[z0,z1,z2,z358,z3,z5,z12]),(0,[z0,z1,z2,z3,z359,z5,z12]),(0,[z0,z1,z19,z2,z3,z5,z9]),(0,[z0,z1,z2,z327,z3,z107,z5]),(0,[z0,z1,z2,z3,z5,z12,z360]),(0,[z361,z13,z0,z1,z2,z3,z5])],[(0,[z34,z0,z1,z2,z30,z3,z5]),(1,[z0,z1,z2,z3,z5,z6]),(1,[z0,z28,z2,z3,z5,z12]),(0,[z362,z0,z1,z2,z3,z5,z12])],[(0,[z23,z0,z1,z2,z337,z5,z12]),(0,[z0,z1,z2,z3,z76,z5,z9]),(0,[z0,z1,z2,z363,z3,z5,z12]),(0,[z0,z1,z2,z3,z364,z5,z12]),(0,[z365,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z127,z3,z5,z12]),(0,[z0,z1,z2,z30,z14,z3,z5])],[(0,[z0,z1,z2,z3,z5,z24,z12]),(0,[z0,z1,z57,z188,z3,z5,z12]),(0,[z0,z1,z2,z3,z4,z5,z9]),(0,[z13,z206,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z83,z50]),(0,[z0,z1,z2,z366,z3,z5,z12]),(1,[z0,z1,z2,z3,z266,z83])],[(0,[z0,z1,z2,z3,z367,z5,z12]),(0,[z49,z0,z2,z3,z5,z50,z12]),(0,[z13,z0,z1,z2,z3,z5,z50]),(0,[z0,z1,z2,z3,z5,z12,z368])]],
   [[(0,[z0,z1,z2,z3,z5,z16,z12]),(0,[z23,z0,z1,z131,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z369,z12]),(0,[z370,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z145,z6]),(0,[z0,z1,z2,z3,z5,z6,z326]),(0,[z0,z1,z2,z371,z3,z5,z12]),(0,[z171,z0,z1,z229,z3,z5,z12]),(1,[z0,z1,z2,z3,z5,z112]),(0,[z372,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z254,z157]),(0,[z13,z0,z1,z2,z170,z3,z5])],[(0,[z34,z0,z1,z2,z3,z5,z9]),(0,[z0,z373,z1,z2,z3,z5,z12]),(0,[z0,z1,z374,z2,z3,z5,z12]),(0,[z375,z0,z1,z2,z3,z5,z12]),(0,[z0,z135,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z376,z5,z12])],[(0,[z377,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z283,z5,z12]),(0,[z154,z13,z0,z1,z2,z3,z5]),(0,[z0,z108,z1,z2,z14,z3,z12])],[(0,[z0,z1,z2,z3,z378,z5,z12]),(0,[z0,z1,z2,z3,z379,z5,z12]),(0,[z0,z1,z2,z380,z3,z5,z12]),(0,[z25,z0,z1,z2,z30,z3,z5])],[(0,[z0,z1,z216,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z381,z12]),(0,[z151,z0,z1,z2,z3,z5,z6]),(0,[z382,z0,z1,z2,z3,z5,z12]),(0,[z0,z383,z1,z2,z3,z5,z12]),(0,[z0,z1,z384,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z266,z5])],[(0,[z385,z0,z1,z2,z3,z5,z12]),(0,[z386,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z387,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z266,z5,z6]),(0,[z388,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z389,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z390]),(0,[z0,z391,z1,z2,z3,z5,z12])],[(0,[z0,z108,z1,z2,z3,z5,z392]),(0,[z0,z1,z2,z3,z5,z393,z12]),(0,[z0,z394,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z83,z254]),(0,[z13,z0,z1,z2,z81,z5,z12])],[(0,[z23,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z395,z12]),(0,[z0,z1,z2,z3,z5,z396,z12]),(0,[z0,z26,z1,z2,z3,z5,z9]),(0,[z0,z1,z397,z2,z3,z5,z12]),(0,[z398,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z399,z5,z12]),(0,[z13,z0,z1,z2,z3,z5,z254]),(0,[z0,z1,z2,z30,z3,z5,z56])]],
   [[(0,[z151,z0,z137,z2,z3,z5,z12]),(0,[z13,z94,z0,z1,z2,z3,z5]),(1,[z0,z1,z2,z287,z3,z5]),(0,[z0,z1,z2,z30,z5,z155,z12]),(0,[z0,z400,z1,z2,z3,z5,z12])],[(0,[z401,z0,z1,z2,z3,z5,z12]),(0,[z0,z92,z1,z2,z3,z5,z12]),(0,[z402,z0,z1,z2,z3,z5,z12]),(0,[z403,z13,z0,z1,z2,z3,z5])],[(0,[z154,z151,z1,z2,z3,z5,z12]),(1,[z23,z1,z188,z3,z5,z12]),(1,[z0,z1,z2,z3,z321,z12]),(0,[z0,z1,z2,z3,z5,z404,z12])],[(1,[z0,z1,z405,z3,z5,z12]),(0,[z406,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z407,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z5,z12])],[(0,[z206,z0,z1,z2,z4,z5,z12]),(0,[z0,z1,z2,z3,z5,z6,z254]),(0,[z0,z408,z1,z2,z3,z5,z12])],[(0,[z0,z1,z39,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z409,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z9]),(0,[z0,z1,z2,z3,z5,z12,z410]),(0,[z0,z1,z2,z3,z411,z5,z12]),(0,[z0,z1,z2,z3,z5,z412,z12])],[(1,[z0,z1,z2,z3,z5,z242]),(0,[z0,z1,z2,z3,z5,z413,z12])],[(0,[z0,z414,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z415,z12]),(0,[z0,z1,z2,z30,z3,z5,z47]),(0,[z0,z1,z2,z3,z416,z5,z12]),(0,[z0,z1,z2,z3,z5,z417,z12]),(0,[z0,z1,z2,z3,z418,z5,z12]),(0,[z0,z1,z2,z3,z419,z5,z12]),(1,[z0,z1,z2,z3,z5,z165]),(0,[z0,z1,z2,z5,z155,z12,z61]),(0,[z0,z1,z2,z30,z3,z5,z83]),(0,[z44,z0,z1,z2,z5,z12,z157])]],
   [[(0,[z0,z1,z2,z420,z3,z5,z12]),(0,[z421,z0,z1,z2,z3,z5,z12]),(0,[z422,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z423,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z424,z12])],[(0,[z0,z1,z2,z3,z5,z12,z425]),(0,[z0,z135,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z155]),(0,[z0,z1,z2,z3,z5,z426,z12]),(0,[z427,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z428,z12])],[(0,[z0,z1,z39,z2,z3,z5,z9]),(0,[z0,z1,z2,z429,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z106,z12]),(0,[z0,z1,z2,z194,z35,z5,z12]),(0,[z0,z1,z2,z3,z5,z8,z12]),(1,[z0,z26,z57,z3,z5,z12]),(0,[z0,z1,z2,z430,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z431]),(0,[z25,z13,z0,z1,z2,z3,z5])],[(0,[z154,z0,z1,z405,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z11,z5])],[(0,[z85,z0,z1,z188,z3,z5,z12]),(0,[z0,z1,z131,z48,z3,z5,z12]),(0,[z206,z0,z1,z2,z3,z5,z6]),(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z432,z5,z12])],[(0,[z0,z1,z2,z35,z3,z5,z12]),(0,[z0,z433,z1,z2,z3,z5,z12]),(0,[z0,z1,z434,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z81,z5]),(0,[z13,z0,z1,z2,z3,z210,z5]),(0,[z0,z1,z2,z435,z3,z5,z12])],[(0,[z0,z436,z1,z2,z3,z5,z12]),(0,[z0,z1,z437,z2,z3,z5,z12]),(1,[z151,z137,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z438,z12]),(0,[z0,z1,z2,z3,z5,z111,z9]),(0,[z0,z79,z1,z2,z30,z3,z5]),(0,[z0,z1,z102,z3,z5,z145,z12]),(0,[z439,z0,z1,z2,z3,z5,z12])],[(0,[z0,z440,z1,z2,z3,z5,z12]),(0,[z171,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z395,z6]),(0,[z0,z1,z2,z3,z441,z5,z12]),(0,[z0,z1,z2,z3,z5,z442,z12]),(0,[z0,z1,z2,z30,z3,z5,z145]),(0,[z13,z0,z1,z2,z30,z3,z5])]],
   [[(0,[z154,z0,z1,z2,z3,z5,z166]),(0,[z1,z2,z3,z4,z5,z12,z9]),(0,[z0,z26,z2,z3,z107,z5,z12]),(0,[z0,z1,z2,z3,z443,z5,z12]),(0,[z444,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z120,z3,z5,z12,z254]),(0,[z0,z1,z2,z3,z445,z5,z12])],[(0,[z0,z1,z2,z446,z3,z5,z12]),(0,[z0,z1,z19,z2,z3,z5,z344])],[(0,[z0,z1,z2,z3,z5,z12,z447]),(0,[z0,z1,z2,z138,z194,z3,z5]),(0,[z34,z0,z1,z2,z416,z5,z12]),(0,[z95,z207,z1,z2,z3,z5,z12])],[(0,[z0,z79,z1,z2,z3,z5,z9]),(0,[z187,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z81,z5,z9]),(0,[z0,z1,z2,z3,z294,z5,z9]),(0,[z0,z1,z2,z3,z5,z83,z9]),(0,[z0,z1,z2,z30,z3,z5,z6]),(0,[z0,z448,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z449,z12]),(0,[z0,z1,z2,z3,z5,z450,z12])],[(0,[z13,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z451,z5,z12]),(0,[z452,z0,z1,z2,z3,z5,z12]),(0,[z453,z13,z0,z1,z2,z3,z5])],[(1,[z0,z1,z2,z3,z5,z129]),(0,[z0,z1,z2,z35,z4,z5,z12]),(0,[z454,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z455,z5,z12]),(0,[z0,z1,z2,z3,z456,z5,z12]),(0,[z25,z0,z75,z1,z2,z3,z12]),(0,[z316,z0,z1,z2,z3,z5,z12])],[(0,[z457,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z458,z5,z12])],[(0,[z0,z1,z2,z3,z459,z5,z12]),(0,[z0,z1,z460,z2,z3,z5,z12]),(1,[z0,z122,z1,z2,z3,z12]),(0,[z0,z461,z1,z2,z3,z5,z12]),(0,[z0,z1,z462,z2,z30,z3,z5])]],
   [[(0,[z0,z1,z2,z463,z3,z5,z12]),(0,[z0,z75,z1,z2,z30,z3,z5]),(0,[z13,z0,z1,z2,z464,z3,z5])],[(0,[z0,z1,z2,z3,z5,z465,z12]),(0,[z0,z1,z2,z3,z466,z5,z12]),(0,[z0,z1,z2,z3,z5,z6,z9]),(0,[z0,z1,z2,z128,z30,z3,z5]),(0,[z0,z1,z2,z3,z83,z12,z157])],[(0,[z206,z0,z1,z2,z3,z321,z12])],[(0,[z72,z0,z1,z2,z3,z5,z6]),(0,[z0,z79,z2,z48,z3,z5,z12]),(0,[z0,z1,z2,z467,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z468,z12]),(0,[z0,z1,z120,z2,z30,z3,z5])],[(0,[z0,z1,z2,z3,z113,z5,z12]),(0,[z0,z1,z2,z3,z5,z121,z9]),(0,[z0,z2,z48,z3,z36,z5,z12]),(0,[z469,z0,z1,z2,z3,z5,z12])],[(0,[z154,z0,z1,z2,z3,z283,z12]),(0,[z154,z0,z1,z2,z3,z5,z129]),(0,[z0,z137,z1,z2,z30,z3,z5]),(0,[z470,z0,z1,z2,z3,z5,z12]),(0,[z0,z75,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z35,z3,z5,z6]),(0,[z0,z1,z2,z3,z107,z5,z12]),(0,[z0,z1,z2,z3,z11,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z471]),(0,[z0,z1,z472,z2,z3,z5,z12]),(1,[z0,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z188,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z473,z12]),(0,[z0,z474,z1,z2,z3,z5,z12]),(0,[z475,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z476,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z477]),(0,[z34,z0,z1,z2,z3,z5,z7]),(0,[z0,z1,z2,z3,z441,z5,z6]),(0,[z0,z478,z1,z2,z3,z5,z12]),(0,[z479,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z480]),(0,[z0,z1,z2,z3,z5,z12,z481]),(0,[z0,z1,z2,z3,z5,z482,z12]),(0,[z168,z0,z1,z2,z3,z5,z56]),(0,[z0,z483,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z5,z12,z45,z157])]],
   [[(0,[z0,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z229,z3,z5,z12])],[(0,[z13,z0,z1,z2,z35,z3,z5]),(0,[z0,z2,z3,z5,z50,z12,z63]),(0,[z0,z1,z2,z30,z3,z5,z50]),(0,[z0,z1,z102,z2,z30,z3,z5]),(0,[z0,z484,z1,z2,z3,z5,z12])],[(0,[z151,z0,z1,z2,z30,z3,z5]),(0,[z485,z0,z1,z2,z3,z5,z12]),(0,[z427,z0,z1,z2,z194,z3,z5]),(0,[z0,z26,z92,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z145,z9]),(0,[z0,z1,z2,z3,z5,z486,z12])],[(0,[z154,z0,z1,z2,z296,z5,z12]),(0,[z487,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z488]),(0,[z0,z1,z2,z3,z489,z5,z12]),(0,[z0,z1,z2,z3,z5,z335,z9]),(1,[z25,z13,z0,z1,z2,z5])],[(0,[z0,z490,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z491,z12]),(0,[z13,z0,z1,z115,z2,z3,z5])],[(0,[z0,z1,z102,z2,z3,z5,z9]),(0,[z0,z1,z57,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z238,z12])],[(0,[z151,z0,z1,z2,z3,z5,z9]),(0,[z88,z0,z1,z2,z4,z5,z12]),(0,[z0,z492,z1,z2,z3,z5,z12]),(0,[z13,z0,z243,z1,z2,z3,z5])]],
   [[(0,[z493,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z494,z5,z12]),(0,[z0,z1,z495,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z496,z5,z12]),(0,[z497,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z498]),(0,[z361,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z499])],[(0,[z0,z1,z2,z30,z3,z5,z254])],[(0,[z0,z137,z2,z48,z3,z5,z12]),(0,[z23,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z500,z12]),(0,[z0,z1,z2,z3,z501,z5,z12]),(0,[z0,z1,z2,z3,z5,z502,z12]),(0,[z0,z75,z1,z2,z3,z76,z12]),(0,[z0,z1,z2,z3,z5,z503,z12])],[(0,[z0,z1,z2,z3,z5,z12,z7]),(0,[z0,z1,z2,z3,z5,z12,z504]),(0,[z0,z26,z2,z3,z36,z5,z12]),(0,[z0,z1,z505,z2,z3,z5,z12]),(0,[z506,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z113,z5,z6]),(0,[z0,z1,z2,z3,z5,z507,z12]),(0,[z0,z1,z2,z3,z5,z508,z12]),(0,[z0,z1,z2,z3,z509,z5,z12]),(0,[z510,z0,z1,z2,z3,z5,z12])],[(0,[z511,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z228,z12]),(0,[z0,z1,z2,z3,z47,z111,z12]),(0,[z0,z1,z2,z3,z107,z5,z6]),(0,[z0,z1,z2,z3,z11,z5,z6]),(0,[z0,z512,z1,z2,z3,z5,z12]),(0,[z0,z1,z513,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z514,z12]),(0,[z0,z1,z2,z138,z3,z5,z12]),(0,[z0,z1,z2,z3,z515,z5,z12]),(0,[z0,z1,z2,z516,z3,z5,z12]),(0,[z517,z13,z0,z1,z2,z3,z5])],[(0,[z154,z0,z1,z2,z3,z5,z12]),(0,[z88,z0,z1,z2,z3,z5,z6]),(0,[z95,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z518,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z519,z12]),(0,[z0,z1,z2,z3,z520,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z521,z5,z12]),(0,[z206,z0,z1,z2,z194,z5,z12]),(1,[z1,z2,z3,z5,z6,z9]),(0,[z0,z1,z2,z3,z5,z9,z447]),(0,[z0,z1,z505,z2,z3,z107,z5]),(0,[z13,z0,z1,z2,z69,z3,z5]),(0,[z0,z1,z2,z3,z5,z522,z12]),(1,[z44,z0,z1,z2,z5,z12])],[(1,[z34,z1,z2,z3,z113,z12]),(0,[z0,z1,z2,z3,z523,z5,z12]),(0,[z0,z243,z2,z3,z5,z12,z63]),(0,[z0,z524,z1,z2,z3,z5,z12]),(0,[z0,z1,z19,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z56,z157])],[(0,[z525,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z526,z5,z12]),(0,[z13,z0,z1,z2,z3,z113,z5]),(0,[z13,z0,z1,z120,z2,z3,z5])],[(0,[z0,z1,z102,z2,z3,z76,z12]),(0,[z0,z1,z527,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z12,z86]),(0,[z0,z528,z1,z2,z3,z5,z12]),(0,[z0,z135,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z529,z3,z5,z12]),(0,[z0,z75,z1,z2,z3,z145,z12]),(0,[z0,z530,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z531,z5,z12])],[(0,[z532,z0,z1,z2,z3,z5,z12]),(0,[z85,z0,z1,z131,z3,z5,z12]),(0,[z0,z1,z533,z2,z3,z5,z12]),(0,[z0,z1,z534,z2,z3,z5,z12]),(1,[z187,z0,z1,z11,z5,z12]),(0,[z0,z1,z2,z30,z3,z535,z5])],[(0,[z0,z536,z1,z2,z3,z5,z12]),(0,[z49,z0,z1,z2,z3,z5,z63]),(0,[z403,z0,z1,z2,z3,z5,z12]),(0,[z537,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z538])],[(0,[z0,z1,z131,z2,z3,z5,z12]),(0,[z206,z0,z1,z2,z3,z5,z9]),(0,[z94,z0,z1,z2,z3,z5,z139]),(0,[z207,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z539,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z50,z157]),(0,[z0,z1,z2,z30,z3,z81,z5])]],
   [[(0,[z0,z1,z2,z540,z3,z5,z12]),(0,[z541,z0,z1,z2,z3,z5,z12]),(0,[z542,z0,z1,z2,z3,z5,z12]),(0,[z0,z243,z1,z2,z3,z5,z63]),(1,[z0,z1,z102,z3,z145,z12]),(1,[z25,z0,z1,z2,z121,z12]),(0,[z0,z1,z2,z3,z81,z5,z209])],[(0,[z0,z1,z2,z3,z5,z219,z9]),(0,[z0,z75,z1,z2,z14,z3,z12]),(0,[z0,z1,z2,z464,z3,z5,z12])],[(0,[z543,z0,z1,z2,z3,z5,z12]),(0,[z171,z0,z1,z2,z3,z5,z9]),(0,[z544,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z545,z12]),(0,[z0,z546,z1,z2,z3,z5,z12]),(0,[z49,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z190,z3,z5,z12])],[(0,[z0,z1,z2,z547,z3,z5,z12]),(0,[z548,z0,z1,z2,z3,z5,z12]),(0,[z0,z549,z1,z2,z3,z5,z12])],[(0,[z0,z1,z550,z2,z3,z5,z12]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z69,z4,z5,z12]),(0,[z206,z0,z1,z2,z3,z5,z551]),(0,[z0,z1,z2,z81,z5,z155,z12]),(0,[z0,z1,z2,z170,z3,z266,z12])],[(0,[z0,z26,z1,z2,z30,z3,z5]),(1,[z0,z1,z2,z3,z5,z344]),(0,[z0,z1,z102,z2,z3,z145,z12]),(0,[z0,z1,z552,z2,z3,z5,z12])],[(1,[z0,z1,z2,z3,z5,z488]),(0,[z427,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z5,z9]),(0,[z553,z0,z1,z2,z3,z5,z12]),(0,[z0,z554,z1,z2,z3,z5,z12]),(0,[z0,z555,z1,z2,z3,z5,z12])],[(0,[z154,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z556,z12]),(0,[z23,z0,z1,z2,z3,z244,z12]),(0,[z0,z1,z2,z194,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z202]),(0,[z0,z1,z2,z3,z557,z5,z12]),(0,[z25,z0,z1,z2,z3,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z558,z5,z12]),(0,[z559,z0,z1,z2,z30,z3,z5])],[(0,[z560,z0,z1,z2,z3,z5,z12]),(0,[z88,z206,z1,z2,z3,z5,z12]),(1,[z0,z200,z1,z2,z3,z5]),(0,[z95,z206,z1,z2,z3,z5,z12]),(0,[z0,z1,z561,z2,z3,z5,z12]),(0,[z348,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z562,z3,z5,z12])],[(1,[z88,z1,z2,z4,z5,z12]),(0,[z0,z1,z2,z3,z47,z145,z12]),(0,[z0,z2,z35,z3,z107,z5,z12]),(0,[z0,z1,z2,z563,z3,z5,z12]),(0,[z0,z1,z102,z2,z14,z3,z12]),(0,[z0,z1,z2,z3,z5,z564,z12])],[(0,[z154,z0,z137,z2,z3,z5,z12]),(0,[z0,z1,z2,z565,z3,z5,z12]),(0,[z0,z1,z2,z14,z3,z81,z12]),(0,[z0,z1,z2,z261,z30,z3,z5])],[(0,[z236,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z69,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z209])],[(0,[z1,z2,z194,z3,z4,z5,z12]),(0,[z566,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z567,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z568,z12]),(1,[z0,z1,z2,z14,z81,z12]),(0,[z0,z230,z1,z2,z3,z5,z12])],[(0,[z151,z0,z1,z2,z3,z5,z488]),(0,[z0,z1,z569,z2,z3,z5,z12]),(0,[z34,z13,z0,z1,z2,z3,z5]),(0,[z72,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z570,z3,z5,z12]),(0,[z0,z1,z102,z2,z3,z5,z571]),(0,[z13,z0,z1,z2,z3,z3,z5])],[(0,[z0,z1,z131,z2,z3,z5,z6]),(0,[z572,z0,z1,z2,z3,z5,z12])]],
   [[(0,[z259,z0,z1,z2,z3,z5,z9]),(0,[z0,z573,z1,z2,z3,z5,z12])],[(0,[z574,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z575,z3,z5,z12]),(0,[z168,z0,z1,z2,z3,z5,z254]),(0,[z0,z1,z2,z3,z5,z12,z576]),(0,[z453,z0,z1,z2,z3,z5,z12])],[(0,[z0,z577,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z3,z5,z522])],[(0,[z0,z1,z2,z578,z3,z5,z12]),(0,[z0,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z369,z6]),(0,[z171,z0,z2,z3,z107,z5,z12]),(0,[z0,z1,z2,z30,z35,z3,z5]),(0,[z0,z1,z2,z3,z579,z5,z12]),(0,[z0,z1,z2,z3,z5,z580,z12]),(0,[z0,z1,z2,z3,z5,z581,z12])],[(0,[z0,z1,z2,z3,z5,z9,z340]),(0,[z582,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z57,z2,z30,z3,z5]),(0,[z0,z583,z1,z2,z3,z5,z12]),(0,[z584,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z585,z3,z5,z12]),(1,[z0,z1,z10,z2,z3,z12])],[(0,[z586,z0,z1,z2,z3,z5,z12]),(0,[z13,z0,z137,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z12,z551]),(0,[z0,z1,z587,z2,z3,z5,z12])],[(1,[z0,z1,z2,z3,z5,z86]),(1,[z427,z0,z1,z2,z3,z5]),(0,[z427,z0,z1,z2,z3,z5,z6]),(0,[z0,z588,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z589,z12]),(1,[z0,z1,z590,z3,z5,z12]),(0,[z591,z0,z1,z2,z3,z5,z12]),(0,[z0,z99,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z522,z121]),(0,[z0,z1,z2,z3,z5,z592,z12]),(0,[z593,z0,z1,z2,z3,z5,z12])],[(0,[z594,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z170,z3,z5,z157])]],
   [[(0,[z0,z135,z1,z2,z14,z3,z12])],[(0,[z13,z85,z0,z1,z2,z3,z5]),(0,[z595,z0,z1,z2,z3,z5,z12]),(0,[z206,z0,z1,z2,z3,z5,z438]),(0,[z0,z1,z57,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z9,z254]),(0,[z596,z0,z1,z2,z3,z5,z12]),(0,[z187,z0,z1,z2,z30,z3,z5])],[(0,[z277,z0,z1,z2,z3,z5,z12]),(1,[z13,z0,z1,z2,z30,z5])],[(0,[z0,z1,z2,z3,z5,z148,z12]),(0,[z597,z0,z1,z2,z3,z5,z12]),(0,[z85,z1,z131,z2,z3,z5,z12]),(0,[z88,z0,z1,z2,z194,z5,z12]),(0,[z0,z1,z2,z3,z5,z5,z12]),(0,[z0,z1,z2,z3,z5,z63,z157]),(0,[z0,z1,z598,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z56,z12])],[(0,[z0,z1,z599,z2,z3,z5,z12]),(0,[z0,z1,z2,z194,z81,z5,z12]),(0,[z0,z1,z2,z308,z3,z5,z12]),(0,[z0,z92,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z80,z5,z12]),(0,[z0,z1,z2,z3,z227,z5,z12]),(0,[z270,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z600,z12]),(1,[z207,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z601,z5,z12]),(0,[z602,z0,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z603,z12]),(0,[z0,z1,z2,z3,z5,z12,z604]),(0,[z0,z26,z1,z57,z3,z5,z12]),(0,[z605,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z606,z2,z3,z5,z12])],[(0,[z1,z131,z2,z188,z3,z5,z12]),(0,[z0,z1,z2,z3,z113,z5,z9]),(0,[z0,z1,z2,z48,z3,z5,z12]),(0,[z0,z607,z1,z2,z3,z5,z12])]],
   [[(0,[z608,z0,z1,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z3,z5,z12,z20])],[(0,[z137,z1,z39,z2,z3,z5,z12]),(0,[z0,z1,z609,z2,z3,z5,z12]),(1,[z0,z1,z2,z3,z5,z610]),(0,[z0,z1,z2,z3,z5,z50,z12]),(0,[z187,z0,z1,z19,z3,z5,z12]),(0,[z0,z1,z611,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z612,z5,z12]),(0,[z168,z0,z1,z2,z30,z3,z5])],[(0,[z0,z1,z2,z3,z613,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z218]),(0,[z88,z0,z1,z2,z3,z5,z9]),(0,[z95,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z30,z69,z3,z5]),(0,[z0,z1,z2,z3,z5,z571,z12]),(0,[z0,z1,z2,z3,z5,z614,z12])],[(0,[z0,z1,z2,z615,z3,z5,z12]),(0,[z0,z1,z2,z3,z616,z5,z12]),(0,[z617,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z306,z3,z5,z9]),(0,[z13,z0,z1,z2,z3,z5,z61]),(0,[z0,z1,z2,z30,z3,z520,z5]),(0,[z0,z1,z462,z2,z3,z5,z12])],[(0,[z0,z1,z2,z30,z3,z113,z5]),(1,[z0,z79,z48,z3,z5,z12]),(0,[z0,z1,z2,z3,z618,z5,z12]),(0,[z0,z135,z108,z2,z3,z5,z12]),(0,[z13,z0,z1,z19,z2,z3,z5]),(0,[z0,z1,z3,z76,z5,z145,z12]),(0,[z0,z1,z2,z3,z5,z619,z12])],[(0,[z620,z0,z1,z2,z3,z5,z12]),(0,[z94,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z621]),(0,[z0,z1,z2,z3,z5,z622,z12]),(0,[z171,z0,z92,z2,z3,z5,z12]),(0,[z0,z135,z1,z2,z3,z36,z12]),(0,[z49,z0,z243,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z5,z63]),(1,[z0,z1,z2,z30,z3,z5])],[(0,[z0,z1,z2,z405,z3,z5,z12]),(0,[z0,z623,z1,z2,z3,z5,z12]),(0,[z85,z0,z1,z2,z3,z5,z610]),(0,[z0,z1,z2,z3,z624,z5,z12]),(0,[z94,z0,z1,z2,z3,z113,z12]),(1,[z94,z1,z2,z3,z47,z12]),(0,[z1,z2,z3,z5,z6,z12,z9]),(0,[z168,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z625,z12]),(0,[z626,z0,z1,z2,z3,z5,z12]),(0,[z25,z0,z1,z2,z3,z81,z12])],[(0,[z0,z1,z2,z3,z627,z5,z12])]],
   [[(0,[z628,z0,z1,z2,z3,z5,z12]),(1,[z0,z92,z2,z35,z5,z12]),(0,[z0,z108,z1,z2,z3,z5,z12]),(0,[z187,z13,z0,z1,z2,z3,z5])],[(0,[z629,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z630,z5,z12]),(0,[z298,z13,z0,z1,z2,z3,z5]),(0,[z13,z13,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z188,z3,z5,z12]),(1,[z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z325,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z631,z5,z12]),(0,[z0,z108,z2,z3,z5,z111,z12]),(0,[z0,z1,z204,z2,z3,z5,z12])],[(0,[z0,z632,z1,z2,z3,z5,z12]),(0,[z517,z0,z1,z2,z3,z5,z12]),(0,[z633,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z56,z6]),(0,[z0,z1,z2,z3,z5,z634,z12]),(1,[z0,z1,z505,z2,z3,z5]),(0,[z0,z135,z1,z590,z3,z5,z12]),(0,[z0,z1,z2,z3,z535,z5,z12])],[(1,[z0,z1,z2,z55,z5,z12]),(0,[z635,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z636]),(1,[z0,z1,z2,z125,z3,z5]),(0,[z0,z1,z2,z3,z637,z5,z12])],[(0,[z0,z1,z2,z3,z296,z5,z12]),(0,[z0,z1,z638,z2,z3,z5,z12]),(0,[z0,z1,z19,z2,z11,z5,z12]),(0,[z0,z1,z2,z30,z3,z5,z639]),(0,[z0,z1,z2,z3,z5,z639,z12])],[(0,[z0,z1,z2,z3,z5,z9,z9]),(0,[z0,z1,z2,z640,z3,z5,z12])],[(0,[z85,z0,z1,z2,z3,z5,z9]),(1,[z0,z1,z2,z3,z5,z551]),(0,[z0,z1,z2,z48,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z12,z641]),(0,[z642,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z14,z3,z5,z12])]],
   [[(0,[z23,z0,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z14,z3,z113,z12]),(0,[z0,z1,z2,z3,z5,z12,z392]),(0,[z0,z1,z643,z2,z3,z5,z12])],[(0,[z23,z0,z130,z2,z3,z5,z12]),(0,[z0,z1,z2,z138,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z50,z6]),(0,[z0,z1,z2,z264,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z266,z5]),(0,[z0,z1,z2,z3,z644,z5,z12])],[(0,[z154,z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z194,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z9,z425]),(0,[z0,z79,z1,z57,z3,z5,z12]),(0,[z0,z79,z1,z48,z3,z5,z12]),(0,[z0,z645,z1,z2,z3,z5,z12]),(0,[z322,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z19,z69,z3,z5,z12])],[(0,[z646,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z266,z5,z9]),(0,[z647,z0,z1,z2,z3,z5,z12])],[(0,[z23,z85,z1,z2,z3,z5,z12]),(0,[z0,z648,z1,z2,z3,z5,z12]),(0,[z0,z649,z1,z2,z3,z5,z12])],[(0,[z650,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z651,z3,z5,z12]),(0,[z94,z0,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z57,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z12,z140]),(0,[z0,z1,z2,z3,z652,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z653]),(0,[z654,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z155,z12])],[(0,[z0,z1,z2,z4,z81,z5,z12]),(0,[z0,z1,z2,z3,z113,z145,z12]),(0,[z0,z1,z57,z3,z11,z5,z12])],[(0,[z23,z0,z1,z2,z55,z5,z12]),(0,[z0,z1,z2,z3,z5,z610,z12]),(0,[z0,z1,z2,z3,z655,z5,z12]),(0,[z0,z1,z2,z69,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z248,z12]),(0,[z0,z1,z2,z656,z3,z5,z12]),(0,[z49,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z657])]],
   [[(1,[z0,z1,z216,z3,z5,z12]),(0,[z0,z1,z2,z3,z3,z5,z12]),(0,[z206,z0,z1,z2,z3,z106,z12]),(0,[z0,z108,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z656,z3,z5]),(0,[z0,z658,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z659,z3,z5,z12]),(0,[z0,z1,z2,z30,z3,z3,z5])],[(0,[z660,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z6,z621]),(0,[z661,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z662,z2,z3,z5,z12]),(0,[z0,z243,z1,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z5,z121]),(0,[z0,z1,z2,z170,z3,z5,z12])],[(0,[z0,z1,z2,z3,z663,z5,z12]),(0,[z0,z135,z1,z2,z30,z3,z5]),(0,[z13,z0,z52,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z266,z83,z12])],[(0,[z34,z0,z1,z2,z3,z5,z304]),(0,[z187,z0,z1,z3,z11,z5,z12]),(0,[z0,z75,z204,z2,z3,z5,z12]),(0,[z13,z664,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z202,z12]),(1,[z171,z0,z2,z107,z5,z12]),(0,[z665,z0,z1,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z3,z5,z157])],[(0,[z206,z0,z1,z2,z30,z3,z5]),(0,[z34,z0,z1,z2,z308,z5,z12]),(0,[z207,z0,z1,z2,z30,z3,z5]),(1,[z49,z0,z2,z3,z5,z50]),(0,[z664,z0,z1,z2,z3,z5,z12]),(0,[z666,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z170,z3,z5,z83])],[(0,[z0,z1,z2,z3,z337,z5,z12]),(0,[z0,z1,z2,z667,z3,z5,z12]),(1,[z13,z0,z1,z2,z81,z5])],[(1,[z0,z1,z2,z3,z244,z12]),(0,[z23,z13,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z14,z3,z5,z6]),(0,[z0,z1,z2,z3,z668,z5,z12]),(0,[z0,z1,z2,z3,z76,z5,z12]),(0,[z0,z1,z2,z3,z5,z669,z12]),(1,[z13,z664,z1,z2,z3,z5]),(0,[z670,z0,z1,z2,z3,z5,z12])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z12]),(0,[z0,z671,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z76,z113,z12]),(0,[z0,z1,z2,z3,z672,z5,z12]),(0,[z171,z0,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z673,z12]),(0,[z13,z664,z1,z2,z3,z5,z12]),(0,[z398,z0,z1,z2,z30,z3,z5])],[(1,[z95,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z404]),(0,[z0,z135,z1,z2,z3,z111,z12]),(0,[z0,z1,z102,z2,z3,z5,z112]),(0,[z0,z1,z2,z674,z3,z5,z12])],[(0,[z0,z1,z675,z2,z3,z5,z12]),(0,[z676,z0,z1,z2,z3,z5,z12]),(0,[z13,z0,z1,z2,z194,z3,z5]),(0,[z0,z92,z1,z2,z30,z3,z5]),(0,[z168,z0,z1,z120,z3,z5,z12]),(0,[z0,z677,z1,z2,z3,z5,z12]),(0,[z402,z0,z1,z2,z30,z3,z5])],[(0,[z34,z0,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z416,z5,z12]),(0,[z497,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z678,z5,z12]),(0,[z0,z1,z2,z3,z36,z5,z12])],[(0,[z0,z1,z2,z3,z5,z679,z12]),(1,[z0,z1,z2,z3,z5,z438]),(0,[z1,z2,z3,z113,z5,z47,z12]),(0,[z34,z0,z1,z2,z3,z113,z12]),(0,[z0,z1,z2,z3,z36,z113,z12]),(0,[z0,z1,z590,z2,z3,z5,z12]),(0,[z13,z0,z1,z552,z2,z3,z5]),(0,[z0,z1,z2,z30,z30,z3,z5]),(0,[z0,z1,z680,z2,z3,z5,z12])],[(0,[z13,z0,z1,z39,z2,z3,z5]),(1,[z206,z1,z2,z194,z5,z12]),(0,[z0,z1,z2,z3,z681,z5,z12]),(0,[z0,z1,z102,z48,z3,z5,z12]),(0,[z0,z1,z102,z57,z3,z5,z12]),(0,[z0,z682,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z683,z5,z12])],[],[(0,[z0,z26,z39,z2,z3,z5,z12]),(1,[z0,z1,z2,z3,z5,z24]),(0,[z0,z92,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z656,z3,z5,z6]),(0,[z49,z0,z1,z2,z3,z5,z6]),(0,[z187,z0,z1,z2,z69,z5,z12]),(0,[z25,z0,z1,z2,z5,z155,z12])]],
   [[(0,[z151,z137,z1,z2,z3,z5,z12]),(0,[z0,z92,z2,z35,z3,z5,z12]),(0,[z0,z1,z2,z3,z684,z5,z12])],[(0,[z0,z1,z2,z170,z3,z5,z6]),(0,[z0,z26,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z685,z12]),(0,[z686,z0,z1,z2,z3,z5,z12]),(0,[z687,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z688,z3,z5,z12])],[(0,[z689,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z293]),(1,[z0,z1,z2,z3,z5,z392]),(1,[z0,z1,z2,z3,z5,z571]),(0,[z0,z1,z3,z5,z56,z12,z254]),(0,[z0,z690,z1,z2,z3,z5,z12])],[(0,[z691,z0,z1,z2,z3,z5,z12]),(0,[z25,z0,z1,z2,z3,z113,z12]),(0,[z0,z1,z692,z2,z3,z5,z12]),(0,[z0,z693,z1,z2,z3,z5,z12]),(1,[z664,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z170,z3,z12,z157]),(0,[z0,z1,z2,z3,z5,z694,z12])],[(0,[z23,z1,z2,z188,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z695,z12]),(0,[z559,z0,z1,z2,z3,z5,z12]),(1,[z206,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z696,z3,z5,z12]),(0,[z72,z0,z1,z2,z30,z3,z5])],[(1,[z0,z1,z2,z276,z5,z12]),(0,[z0,z1,z2,z3,z5,z417,z9]),(0,[z187,z0,z1,z2,z11,z5,z12]),(0,[z697,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z698]),(0,[z0,z1,z2,z30,z3,z5,z61]),(0,[z0,z1,z2,z699,z3,z5,z12])],[(0,[z0,z1,z700,z2,z3,z5,z12]),(0,[z0,z1,z2,z701,z3,z5,z12]),(0,[z0,z1,z2,z3,z36,z47,z12]),(0,[z0,z1,z2,z3,z702,z5,z12]),(1,[z0,z1,z2,z3,z5,z231]),(0,[z0,z1,z703,z2,z3,z5,z12])],[(1,[z154,z39,z2,z3,z5,z12]),(0,[z88,z1,z2,z3,z4,z5,z12]),(0,[z95,z1,z2,z3,z4,z5,z12]),(0,[z34,z1,z2,z3,z113,z5,z12]),(0,[z0,z1,z2,z3,z76,z5,z6]),(0,[z171,z13,z0,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z140]),(0,[z0,z1,z2,z3,z5,z231,z12]),(0,[z13,z0,z135,z1,z2,z3,z5]),(0,[z0,z704,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z705,z5,z12]),(0,[z0,z1,z2,z706,z3,z5,z12])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z405,z276,z5,z12]),(0,[z0,z1,z2,z3,z5,z707]),(0,[z0,z1,z2,z3,z5,z708])],[(0,[z0,z1,z2,z81,z5,z709])],[(0,[z154,z39,z405,z3,z5,z12]),(0,[z0,z1,z2,z3,z710,z12]),(0,[z51,z1,z711,z2,z3,z5])],[(0,[z0,z1,z2,z55,z5,z12]),(1,[z51,z1,z2,z81,z5])],[(0,[z0,z712,z2,z3,z5,z12]),(0,[z0,z1,z2,z713,z3,z5]),(0,[z315,z1,z2,z3,z5,z9]),(0,[z0,z108,z2,z3,z111,z392])],[(0,[z0,z1,z2,z276,z5,z166]),(0,[z0,z1,z2,z3,z5,z714])],[(0,[z0,z715,z2,z3,z5,z12]),(0,[z1,z2,z35,z4,z5,z9])],[(0,[z154,z39,z2,z3,z5,z166]),(0,[z716,z0,z1,z2,z3,z5]),(0,[z151,z137,z2,z3,z5,z488]),(0,[z13,z0,z1,z2,z3,z717])],[(0,[z1,z2,z699,z3,z5,z6]),(0,[z0,z1,z3,z718,z5,z12]),(0,[z51,z1,z2,z3,z5,z43])],[(0,[z0,z1,z2,z173,z3,z5]),(0,[z0,z1,z2,z3,z5,z719]),(0,[z0,z1,z2,z3,z5,z720])],[(0,[z44,z0,z1,z2,z5,z9]),(0,[z0,z1,z2,z3,z5,z721])],[(0,[z13,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z722]),(0,[z0,z28,z2,z30,z3,z5])],[(0,[z0,z1,z723,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z724]),(0,[z0,z1,z2,z3,z5,z725]),(0,[z0,z1,z3,z5,z726,z254])],[(0,[z0,z1,z2,z727,z3,z5]),(0,[z51,z1,z57,z2,z3,z5])],[(0,[z0,z92,z2,z35,z5,z6])]],
   [[(0,[z23,z13,z1,z188,z3,z5]),(0,[z13,z51,z1,z2,z81,z5]),(0,[z728,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z729,z3,z5]),(0,[z0,z2,z3,z36,z730,z12]),(0,[z0,z1,z2,z3,z5,z20])],[(0,[z0,z1,z2,z276,z283,z12]),(0,[z0,z1,z2,z731,z3,z5]),(0,[z0,z1,z2,z3,z5,z732]),(0,[z0,z1,z102,z3,z145,z9]),(0,[z25,z0,z1,z2,z121,z9]),(0,[z51,z1,z2,z3,z5,z121])],[(0,[z277,z1,z2,z4,z5,z9]),(0,[z171,z0,z2,z107,z5,z12])],[(0,[z154,z39,z2,z3,z283,z12]),(0,[z0,z204,z2,z3,z5,z12]),(0,[z49,z0,z2,z3,z5,z50]),(0,[z733,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z734,z5]),(0,[z51,z1,z2,z3,z5,z157])],[(0,[z0,z1,z2,z3,z16,z129]),(0,[z0,z1,z735,z2,z3,z5]),(0,[z13,z0,z1,z2,z3,z244]),(0,[z13,z664,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z736])],[(0,[z0,z737,z2,z3,z5,z12]),(0,[z738,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z739])],[(0,[z0,z84,z2,z3,z5,z104]),(0,[z740,z0,z1,z2,z3,z12])],[(0,[z0,z1,z2,z3,z5,z741]),(0,[z0,z1,z2,z585,z3,z157]),(0,[z51,z1,z2,z3,z76,z5])],[(0,[z154,z39,z2,z296,z5,z12]),(0,[z51,z1,z2,z194,z3,z5]),(0,[z13,z0,z122,z1,z2,z3]),(1,[z25,z51,z1,z2,z5])],[(0,[z88,z1,z2,z4,z5,z9]),(0,[z51,z1,z2,z742,z3,z5]),(0,[z13,z0,z1,z2,z376,z5])],[(0,[z0,z92,z229,z3,z5,z12]),(0,[z168,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z128,z3,z520])],[(0,[z154,z51,z1,z2,z3,z5]),(0,[z51,z1,z39,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z24]),(0,[z512,z1,z2,z3,z5,z9]),(0,[z348,z0,z2,z3,z5,z148]),(0,[z0,z1,z2,z3,z5,z743]),(0,[z0,z1,z2,z3,z5,z238]),(0,[z0,z1,z744,z3,z5,z12]),(0,[z0,z1,z2,z3,z520,z157])],[(0,[z0,z1,z216,z3,z5,z6]),(0,[z0,z1,z2,z3,z321,z9]),(0,[z0,z1,z2,z745,z3,z5]),(0,[z0,z1,z2,z14,z81,z9])]],
   [[],[(0,[z0,z1,z746,z3,z5,z12]),(0,[z13,z0,z1,z2,z656,z5]),(0,[z0,z1,z2,z3,z5,z747]),(0,[z13,z748,z1,z2,z3,z5])],[(0,[z0,z84,z2,z3,z228,z12]),(0,[z0,z1,z2,z3,z5,z749]),(0,[z0,z26,z57,z30,z3,z5])],[(0,[z23,z84,z188,z3,z5,z12]),(0,[z206,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z750,z3,z5]),(0,[z1,z2,z3,z5,z124,z6]),(0,[z0,z1,z2,z751,z5,z12]),(0,[z0,z1,z462,z3,z5,z254])],[(0,[z0,z1,z2,z752,z3,z5]),(0,[z206,z1,z2,z753,z5,z12]),(0,[z13,z0,z92,z2,z35,z5]),(0,[z0,z1,z2,z3,z12,z754]),(0,[z0,z1,z2,z3,z755,z12]),(0,[z25,z13,z0,z1,z2,z210])],[(0,[z756,z0,z1,z2,z3,z5]),(0,[z0,z1,z757,z3,z5,z12])],[(0,[z0,z1,z2,z30,z153,z5])],[(0,[z758,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z759,z5,z12]),(0,[z0,z474,z48,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z760]),(0,[z0,z1,z2,z327,z3,z80])],[(0,[z0,z84,z188,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z761]),(0,[z0,z1,z2,z3,z5,z762]),(0,[z0,z1,z2,z3,z5,z763])],[(0,[z0,z1,z764,z3,z5,z12]),(0,[z51,z1,z2,z14,z3,z5])],[(0,[z0,z1,z2,z416,z5,z6]),(0,[z0,z1,z325,z3,z5,z218]),(0,[z0,z1,z2,z765,z3,z5]),(0,[z13,z0,z1,z2,z706,z5])],[(0,[z0,z1,z2,z125,z3,z29]),(0,[z13,z664,z1,z2,z5,z61])],[(0,[z0,z1,z2,z3,z5,z766]),(0,[z85,z1,z767,z3,z5,z12]),(0,[z0,z1,z768,z3,z5,z12]),(0,[z0,z1,z2,z769,z3,z5]),(0,[z0,z1,z2,z770,z121,z12]),(0,[z402,z44,z0,z1,z2,z5])],[(0,[z1,z2,z69,z4,z5,z9]),(0,[z51,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z771]),(0,[z0,z1,z772,z3,z5,z12]),(0,[z0,z1,z2,z3,z228,z104]),(0,[z0,z1,z2,z3,z773,z12]),(0,[z666,z1,z2,z3,z5,z9])],[(0,[z0,z774,z2,z3,z5,z12]),(0,[z206,z1,z2,z109,z5,z12]),(0,[z0,z57,z775,z3,z5,z12]),(0,[z776,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z14,z770,z12])]],
   [[(0,[z0,z1,z2,z3,z777,z12]),(0,[z0,z1,z2,z3,z778,z12]),(0,[z0,z1,z2,z3,z5,z779]),(0,[z0,z1,z2,z3,z266,z780])],[(0,[z0,z79,z48,z30,z3,z5]),(0,[z0,z1,z2,z781,z5,z12])],[(0,[z0,z1,z2,z308,z5,z304]),(0,[z1,z2,z696,z3,z5,z9]),(0,[z664,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z782,z3,z5]),(0,[z0,z1,z2,z3,z783,z5]),(0,[z0,z1,z2,z3,z5,z784])],[(0,[z72,z51,z1,z2,z3,z5])],[(0,[z71,z51,z1,z2,z3,z5])],[(0,[z0,z1,z785,z2,z3,z5]),(0,[z670,z1,z2,z3,z5,z6])],[(0,[z0,z786,z2,z3,z5,z12]),(0,[z51,z1,z2,z3,z5,z12]),(0,[z1,z2,z3,z787,z47,z12])],[(0,[z0,z1,z2,z3,z16,z6]),(0,[z23,z1,z188,z3,z228,z12]),(0,[z206,z1,z2,z3,z5,z788]),(0,[z0,z1,z2,z3,z5,z304]),(0,[z582,z0,z48,z3,z5,z12]),(0,[z51,z92,z1,z2,z3,z5]),(0,[z25,z0,z1,z2,z127,z121])],[(0,[z0,z1,z2,z3,z789,z12]),(0,[z85,z51,z1,z2,z3,z5]),(0,[z661,z1,z2,z4,z5,z12])],[(0,[z154,z790,z2,z3,z5,z12]),(0,[z0,z1,z2,z194,z656,z5]),(0,[z0,z92,z2,z35,z5,z9]),(0,[z51,z79,z1,z2,z3,z5]),(0,[z791,z1,z2,z3,z5,z12]),(0,[z0,z75,z1,z3,z76,z12]),(0,[z25,z13,z0,z75,z1,z2])],[(0,[z51,z1,z2,z3,z5,z47]),(0,[z171,z13,z0,z2,z107,z5]),(0,[z0,z1,z2,z3,z5,z792]),(0,[z25,z13,z0,z1,z102,z2]),(0,[z51,z1,z2,z3,z5,z83]),(0,[z322,z0,z1,z3,z31,z5])],[(0,[z13,z0,z26,z57,z3,z5]),(0,[z0,z1,z2,z30,z5,z793])],[(0,[z51,z1,z2,z3,z4,z5]),(0,[z51,z108,z1,z2,z3,z5]),(0,[z13,z0,z794,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z795]),(0,[z0,z1,z303,z3,z5,z404]),(0,[z0,z229,z3,z107,z5,z12]),(0,[z13,z0,z1,z2,z570,z5])],[(0,[z0,z1,z2,z796,z5,z12]),(0,[z1,z2,z674,z3,z5,z6]),(0,[z0,z26,z299,z3,z5,z12]),(0,[z51,z1,z2,z3,z11,z5]),(0,[z0,z1,z2,z3,z5,z797]),(0,[z0,z1,z2,z127,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z405,z3,z5,z166]),(0,[z0,z1,z798,z3,z5,z12]),(0,[z1,z2,z753,z4,z5,z12]),(0,[z0,z1,z2,z3,z12,z799]),(0,[z0,z1,z2,z3,z5,z800])],[(0,[z25,z1,z2,z4,z5,z9]),(0,[z0,z1,z10,z2,z4,z12]),(0,[z206,z1,z2,z3,z321,z9]),(0,[z0,z1,z2,z801,z3,z5]),(0,[z0,z1,z2,z3,z5,z802]),(0,[z0,z1,z2,z138,z5,z417]),(0,[z0,z1,z2,z3,z5,z803]),(0,[z13,z0,z1,z2,z5,z653]),(0,[z0,z1,z2,z3,z5,z804]),(0,[z25,z0,z1,z2,z581,z12]),(0,[z51,z1,z2,z3,z5,z805]),(0,[z453,z0,z1,z2,z3,z43])],[],[(0,[z0,z1,z2,z3,z5,z806]),(0,[z0,z1,z2,z138,z3,z5]),(0,[z0,z122,z2,z48,z3,z12]),(0,[z0,z1,z2,z807,z3,z5]),(0,[z51,z1,z2,z3,z5,z145]),(0,[z0,z1,z120,z3,z5,z254]),(0,[z13,z791,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z80,z6]),(0,[z25,z51,z1,z2,z5,z12]),(0,[z0,z1,z2,z14,z81,z209])],[(0,[z1,z2,z3,z227,z5,z9]),(0,[z44,z0,z1,z2,z170,z157])],[],[(0,[z808,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z5,z12,z809])],[(0,[z0,z1,z2,z810,z5,z12]),(0,[z0,z1,z2,z3,z5,z811]),(0,[z0,z1,z2,z30,z5,z503])],[(0,[z0,z1,z812,z3,z5,z12]),(0,[z0,z1,z2,z5,z9,z45])],[(0,[z0,z1,z216,z3,z5,z9]),(0,[z0,z1,z2,z3,z106,z6])],[],[(0,[z151,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z813]),(0,[z0,z2,z814,z107,z5,z12])],[(0,[z0,z1,z405,z3,z283,z12]),(0,[z0,z1,z2,z3,z5,z815]),(0,[z0,z1,z2,z30,z55,z5]),(0,[z0,z1,z2,z3,z294,z8]),(0,[z0,z1,z2,z3,z816,z12]),(0,[z0,z1,z2,z3,z29,z12]),(0,[z817,z51,z1,z2,z3,z5])],[(0,[z0,z84,z2,z337,z5,z12]),(0,[z0,z1,z2,z3,z5,z818])],[(0,[z0,z693,z48,z3,z5,z12]),(0,[z0,z1,z819,z30,z3,z5])]],
   [[(0,[z0,z820,z2,z3,z5,z12]),(0,[z0,z1,z2,z821,z3,z5]),(0,[z0,z1,z2,z822,z3,z5])],[(0,[z13,z0,z1,z405,z3,z5]),(0,[z0,z84,z131,z3,z5,z12]),(0,[z49,z51,z1,z2,z3,z5]),(0,[z823,z51,z1,z2,z3,z5]),(0,[z559,z1,z2,z3,z227,z5])],[(0,[z0,z1,z2,z3,z283,z166]),(0,[z0,z790,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z824]),(0,[z187,z0,z1,z11,z5,z9]),(0,[z0,z1,z2,z3,z266,z83])],[(0,[z95,z1,z2,z3,z5,z825]),(0,[z0,z1,z2,z5,z12,z826]),(0,[z44,z0,z1,z2,z5,z63])],[(0,[z0,z1,z2,z3,z5,z827]),(0,[z0,z108,z606,z2,z3,z12])],[(0,[z0,z1,z2,z416,z5,z9]),(0,[z51,z1,z2,z3,z5,z50]),(0,[z0,z1,z3,z76,z828,z12])],[],[(0,[z0,z1,z2,z829,z3,z5]),(0,[z206,z1,z2,z194,z5,z9]),(0,[z0,z243,z552,z2,z3,z5]),(0,[z0,z1,z2,z5,z793,z61])],[(0,[z0,z1,z2,z3,z5,z830]),(0,[z0,z84,z2,z3,z5,z6]),(0,[z831,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z296,z5,z166]),(0,[z0,z1,z2,z832,z3,z5]),(0,[z0,z1,z2,z3,z12,z833]),(0,[z13,z0,z1,z2,z5,z698]),(0,[z0,z1,z2,z3,z5,z834])],[(0,[z0,z1,z2,z337,z5,z104]),(0,[z0,z1,z2,z835,z5,z12]),(0,[z1,z2,z3,z644,z5,z9]),(0,[z0,z1,z2,z3,z5,z836])],[(0,[z13,z0,z1,z2,z3,z321])],[(0,[z149,z39,z2,z3,z5,z12]),(0,[z85,z1,z131,z3,z5,z6]),(0,[z0,z1,z2,z3,z227,z5]),(0,[z0,z1,z120,z464,z3,z5])],[(0,[z0,z39,z405,z3,z5,z12]),(0,[z95,z1,z2,z3,z5,z438]),(0,[z0,z1,z2,z3,z5,z139]),(0,[z0,z1,z2,z3,z441,z395]),(0,[z422,z0,z1,z11,z5,z12])],[(0,[z0,z837,z1,z2,z3,z5])],[(0,[z0,z1,z405,z3,z5,z12]),(0,[z0,z135,z264,z3,z36,z12])]],
   [[(0,[z0,z1,z2,z5,z155,z165])],[],[(0,[z0,z1,z2,z3,z5,z242]),(0,[z0,z1,z102,z3,z828,z12])],[(0,[z0,z1,z2,z3,z16,z9]),(0,[z0,z1,z2,z337,z228,z12]),(0,[z200,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z838,z12]),(0,[z0,z1,z2,z839,z3,z5]),(0,[z0,z1,z2,z5,z12,z840]),(0,[z841,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z165]),(0,[z13,z0,z1,z2,z5,z61]),(0,[z0,z1,z2,z3,z210,z83])],[(0,[z0,z1,z2,z3,z5,z166]),(0,[z23,z1,z188,z337,z5,z12]),(0,[z0,z1,z842,z2,z3,z5]),(0,[z13,z0,z79,z48,z3,z5])],[(0,[z95,z200,z1,z2,z3,z5]),(0,[z0,z1,z2,z656,z4,z5]),(0,[z0,z1,z2,z30,z308,z5]),(0,[z0,z195,z2,z3,z5,z340]),(0,[z0,z1,z843,z2,z3,z5]),(0,[z51,z75,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z780])],[(0,[z0,z1,z2,z296,z283,z12]),(0,[z0,z1,z2,z3,z5,z844]),(0,[z0,z48,z3,z451,z5,z12]),(0,[z0,z1,z590,z30,z3,z5]),(0,[z187,z0,z1,z10,z11,z12]),(0,[z0,z1,z2,z3,z5,z845])],[(0,[z0,z1,z2,z30,z296,z5]),(0,[z23,z1,z767,z3,z5,z12]),(0,[z34,z1,z2,z416,z113,z12]),(0,[z0,z1,z2,z5,z6,z826]),(0,[z0,z1,z2,z3,z730,z12]),(0,[z0,z1,z2,z30,z3,z29]),(0,[z361,z0,z1,z115,z3,z5])],[(0,[z151,z790,z2,z3,z5,z12]),(0,[z291,z1,z2,z194,z5,z12]),(0,[z0,z1,z2,z3,z5,z846])],[(0,[z1,z2,z3,z4,z5,z9]),(0,[z0,z1,z2,z847,z5,z12]),(0,[z171,z0,z122,z2,z107,z12]),(0,[z25,z13,z0,z1,z2,z81])],[(0,[z151,z137,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z848,z12])],[(0,[z0,z108,z2,z3,z295,z12])],[(0,[z0,z1,z2,z849,z5,z12]),(0,[z0,z1,z767,z3,z5,z12]),(0,[z0,z850,z2,z3,z5,z12]),(0,[z0,z1,z67,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z851])],[(0,[z0,z852,z1,z3,z5,z12]),(0,[z0,z1,z2,z3,z228,z6]),(0,[z0,z167,z2,z3,z5,z6]),(0,[z1,z2,z3,z853,z5,z12])],[(0,[z23,z1,z188,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z854]),(0,[z365,z0,z1,z2,z30,z5])],[(0,[z1,z2,z3,z5,z825,z12]),(0,[z0,z1,z2,z3,z80,z9])]],
   [[(0,[z0,z1,z2,z855,z3,z5]),(0,[z25,z0,z1,z2,z770,z12]),(0,[z13,z856,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z283,z12]),(0,[z0,z1,z857,z3,z5,z12]),(0,[z1,z2,z3,z684,z5,z9]),(0,[z0,z122,z1,z2,z30,z3]),(0,[z0,z1,z2,z3,z5,z858])],[(0,[z23,z1,z188,z3,z5,z104]),(0,[z362,z1,z2,z3,z5,z9]),(0,[z859,z0,z1,z2,z5,z12])],[(0,[z88,z13,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z5,z860]),(0,[z861,z1,z2,z3,z5,z12]),(0,[z0,z122,z1,z2,z3,z12])],[(0,[z457,z137,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z862]),(0,[z23,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z106,z9])],[(0,[z0,z1,z2,z3,z863,z12]),(0,[z0,z130,z2,z30,z3,z5]),(0,[z0,z108,z2,z3,z111,z6]),(0,[z0,z1,z2,z3,z5,z864]),(0,[z51,z1,z2,z3,z5,z56]),(0,[z0,z865,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z866]),(0,[z0,z1,z2,z30,z5,z155])],[(0,[z0,z1,z2,z296,z5,z12]),(0,[z1,z2,z3,z5,z9,z141]),(0,[z171,z0,z2,z327,z107,z5])],[(0,[z0,z1,z2,z867,z5,z12]),(0,[z0,z1,z2,z3,z5,z868]),(0,[z0,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z869]),(0,[z1,z2,z138,z3,z227,z5]),(0,[z0,z1,z264,z3,z5,z6]),(0,[z0,z870,z2,z3,z5,z12])],[(0,[z1,z2,z194,z3,z227,z5]),(0,[z0,z1,z2,z416,z5,z7]),(0,[z0,z2,z3,z5,z9,z871]),(0,[z0,z1,z2,z3,z5,z872])],[],[(0,[z0,z436,z48,z3,z5,z12]),(0,[z0,z1,z2,z873,z3,z5]),(0,[z0,z1,z2,z308,z5,z12]),(0,[z0,z2,z3,z5,z846,z63]),(0,[z269,z0,z1,z2,z30,z5]),(0,[z71,z0,z552,z2,z3,z5])],[(0,[z0,z1,z2,z874,z5,z12]),(0,[z85,z1,z131,z3,z5,z610]),(0,[z0,z1,z2,z308,z113,z12]),(0,[z0,z26,z775,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z875]),(0,[z0,z876,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z877,z5])]],
   [[(0,[z0,z1,z878,z3,z5,z12])],[(0,[z0,z264,z3,z36,z5,z12])],[(0,[z0,z1,z2,z879,z5,z12]),(0,[z0,z1,z2,z880,z3,z5]),(1,[z1,z2,z753,z5,z12]),(1,[z0,z2,z3,z730,z12]),(0,[z0,z1,z2,z3,z5,z881]),(0,[z0,z1,z120,z3,z5,z726]),(0,[z25,z0,z1,z2,z43,z12])],[(0,[z0,z84,z2,z3,z5,z9]),(0,[z0,z1,z2,z327,z3,z5]),(0,[z51,z1,z115,z2,z3,z5])],[(0,[z0,z882,z1,z2,z3,z5]),(0,[z0,z1,z2,z81,z12,z347])],[(0,[z883,z0,z1,z2,z337,z5]),(0,[z362,z1,z2,z3,z47,z12]),(0,[z0,z1,z2,z3,z5,z884]),(0,[z0,z1,z885,z2,z3,z5])],[(0,[z0,z1,z2,z886,z5,z12]),(0,[z0,z1,z2,z3,z5,z887]),(0,[z13,z0,z1,z19,z69,z5])],[(0,[z888,z0,z1,z2,z55,z5]),(0,[z85,z1,z131,z3,z5,z9]),(0,[z0,z1,z2,z30,z5,z53])],[(0,[z154,z39,z2,z3,z16,z12]),(0,[z0,z1,z2,z3,z5,z889]),(0,[z277,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z890]),(0,[z0,z135,z2,z3,z36,z6]),(0,[z0,z1,z2,z891,z3,z5])],[(0,[z13,z0,z1,z2,z3,z106]),(0,[z0,z1,z2,z3,z5,z892])],[(0,[z0,z1,z2,z893,z5,z12]),(0,[z0,z1,z19,z463,z5,z12]),(0,[z0,z1,z2,z5,z12,z793])],[],[(0,[z151,z137,z2,z3,z5,z242]),(0,[z88,z200,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z5,z894]),(0,[z566,z13,z0,z1,z2,z5]),(0,[z44,z0,z1,z2,z5,z12])],[(0,[z0,z1,z2,z3,z5,z895]),(0,[z0,z1,z3,z5,z12,z896]),(0,[z0,z99,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z897,z12]),(0,[z0,z204,z2,z30,z3,z5]),(0,[z0,z1,z2,z5,z770,z12])],[(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z1,z2,z5,z12,z899]),(0,[z0,z278,z1,z3,z76,z12])],[(0,[z0,z1,z2,z3,z900,z12])]],
   [[(0,[z1,z2,z3,z123,z5,z9]),(0,[z0,z901,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z902]),(0,[z0,z1,z462,z190,z3,z5])],[(0,[z0,z554,z48,z3,z5,z12])],[(0,[z0,z903,z2,z3,z5,z12]),(0,[z629,z1,z2,z3,z5,z9])],[(0,[z0,z1,z2,z904,z3,z5]),(0,[z25,z0,z1,z2,z121,z12])],[(0,[z277,z1,z2,z4,z5,z12]),(1,[z1,z2,z3,z787,z12])],[(0,[z0,z1,z2,z30,z681,z5]),(0,[z0,z1,z2,z3,z905,z12]),(0,[z0,z1,z2,z3,z5,z906])],[(0,[z0,z1,z405,z296,z5,z12]),(0,[z13,z0,z130,z2,z3,z5]),(0,[z0,z1,z67,z3,z5,z9]),(0,[z398,z0,z2,z3,z535,z5])],[(0,[z0,z1,z2,z3,z228,z9]),(0,[z0,z167,z2,z3,z5,z9]),(0,[z907,z1,z2,z3,z5,z12]),(0,[z51,z908,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z909]),(0,[z0,z1,z2,z337,z5,z6]),(0,[z0,z253,z57,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z709])],[(0,[z0,z1,z2,z910,z308,z5]),(0,[z911,z0,z1,z2,z3,z5]),(0,[z13,z912,z1,z2,z3,z5]),(0,[z0,z1,z2,z30,z5,z45])],[(0,[z0,z913,z2,z3,z5,z9]),(0,[z914,z0,z1,z2,z5,z9]),(0,[z915,z1,z2,z3,z5,z12])],[(0,[z916,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z917])],[(0,[z0,z1,z2,z3,z5,z918]),(0,[z277,z0,z1,z2,z5,z61]),(0,[z0,z1,z919,z3,z5,z12]),(0,[z51,z1,z2,z3,z266,z5])],[],[(0,[z154,z39,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z920])]],
   [[(0,[z0,z1,z2,z3,z921,z12]),(0,[z664,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z922,z3,z5]),(0,[z0,z1,z2,z30,z3,z80]),(0,[z13,z0,z1,z264,z3,z5]),(0,[z51,z1,z2,z3,z5,z254])],[(0,[z0,z1,z2,z3,z321,z12]),(0,[z0,z108,z2,z3,z111,z9]),(0,[z0,z1,z2,z923,z5,z12]),(0,[z0,z1,z2,z14,z81,z12])],[(0,[z0,z1,z924,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z925]),(0,[z1,z2,z3,z5,z184,z9]),(0,[z0,z926,z2,z3,z5,z12]),(0,[z0,z75,z204,z3,z76,z12]),(0,[z0,z927,z2,z3,z5,z12])],[(0,[z1,z2,z3,z186,z5,z9]),(0,[z0,z28,z2,z3,z5,z6]),(0,[z0,z1,z2,z928,z3,z5])],[(0,[z0,z1,z2,z3,z5,z929]),(0,[z0,z1,z2,z930,z3,z5]),(0,[z1,z2,z4,z107,z5,z9]),(0,[z1,z2,z4,z11,z5,z9]),(1,[z0,z1,z3,z5,z726])],[(0,[z0,z1,z2,z931,z3,z5]),(0,[z0,z1,z264,z3,z5,z9])],[(0,[z0,z1,z2,z3,z932,z12]),(0,[z0,z1,z505,z2,z3,z80]),(0,[z0,z1,z10,z2,z125,z3])],[(0,[z0,z1,z2,z3,z5,z933]),(0,[z1,z2,z138,z3,z4,z5]),(0,[z168,z0,z1,z3,z31,z5]),(0,[z0,z1,z2,z3,z83,z780])],[(0,[z88,z1,z2,z30,z4,z5]),(0,[z206,z1,z2,z138,z3,z5]),(0,[z0,z1,z2,z3,z441,z83])],[],[],[(0,[z0,z1,z2,z3,z5,z934]),(0,[z0,z1,z2,z3,z5,z935])],[(0,[z0,z1,z2,z3,z5,z936])],[(0,[z0,z1,z2,z937,z3,z5])],[(0,[z938,z0,z1,z2,z276,z5]),(0,[z13,z94,z1,z2,z3,z47]),(0,[z51,z1,z2,z3,z81,z5]),(0,[z51,z1,z2,z3,z210,z5])],[(0,[z207,z51,z1,z2,z3,z5]),(0,[z0,z408,z57,z3,z5,z12]),(0,[z0,z1,z939,z3,z5,z12]),(0,[z13,z0,z1,z2,z87,z5])]],
   [[(0,[z0,z1,z216,z276,z5,z12]),(0,[z187,z13,z0,z1,z11,z5]),(0,[z51,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z3,z266,z639])],[],[(0,[z154,z39,z216,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z940]),(0,[z0,z75,z1,z30,z3,z76])],[(0,[z0,z135,z2,z3,z36,z9]),(0,[z941,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z942,z12]),(0,[z0,z943,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z944])],[(0,[z0,z1,z2,z3,z945,z12]),(0,[z0,z1,z946,z3,z5,z12]),(0,[z13,z0,z1,z2,z5,z709])],[(0,[z37,z1,z2,z3,z5,z9]),(0,[z25,z0,z1,z2,z127,z5]),(0,[z427,z664,z1,z2,z3,z5])],[(0,[z0,z137,z405,z3,z5,z12]),(0,[z0,z1,z2,z947,z3,z5]),(0,[z0,z1,z2,z3,z5,z948]),(0,[z0,z2,z3,z5,z846,z12]),(0,[z13,z0,z204,z2,z3,z5]),(0,[z0,z1,z2,z949,z3,z5])],[(0,[z0,z528,z2,z3,z111,z12]),(0,[z0,z1,z2,z565,z3,z157]),(0,[z13,z0,z1,z950,z3,z5])],[(0,[z0,z1,z2,z951,z5,z12]),(0,[z1,z2,z3,z5,z9,z326]),(0,[z0,z99,z2,z3,z5,z9]),(0,[z13,z0,z1,z2,z5,z326]),(0,[z952,z1,z2,z3,z5,z12]),(0,[z0,z953,z2,z3,z5,z12])],[(0,[z954,z0,z1,z2,z308,z5]),(0,[z252,z1,z2,z3,z5,z9]),(0,[z0,z26,z57,z3,z5,z6]),(0,[z0,z1,z2,z3,z12,z955]),(0,[z0,z1,z3,z5,z56,z726]),(0,[z51,z1,z2,z464,z3,z5]),(0,[z13,z664,z1,z2,z30,z5]),(0,[z0,z1,z2,z30,z435,z5])],[(0,[z0,z1,z956,z2,z3,z5]),(0,[z13,z957,z1,z2,z3,z5])],[(0,[z0,z1,z2,z958,z5,z12])],[(0,[z422,z0,z2,z107,z5,z12])],[],[(0,[z0,z1,z2,z3,z959,z12]),(0,[z0,z1,z2,z3,z5,z960]),(0,[z13,z0,z1,z2,z339,z5]),(0,[z187,z0,z1,z718,z5,z12])],[(0,[z44,z0,z1,z2,z170,z5])]],
   [[(0,[z427,z0,z1,z2,z656,z5]),(0,[z0,z1,z2,z125,z3,z5])],[(0,[z0,z1,z961,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z962]),(0,[z13,z0,z1,z2,z5,z165])],[(0,[z0,z1,z2,z30,z3,z283]),(0,[z13,z0,z1,z2,z416,z5]),(0,[z0,z1,z2,z963,z5,z12]),(0,[z0,z1,z2,z3,z683,z83])],[(0,[z0,z1,z2,z3,z5,z551]),(0,[z51,z1,z964,z2,z3,z5])],[(0,[z13,z0,z1,z2,z3,z16]),(0,[z0,z1,z2,z3,z5,z965]),(0,[z0,z1,z2,z337,z5,z9]),(0,[z0,z1,z2,z30,z3,z244]),(0,[z0,z1,z2,z5,z966,z12]),(0,[z0,z1,z2,z14,z81,z165])],[(0,[z0,z108,z2,z3,z111,z231])],[(1,[z0,z2,z3,z5,z846])],[(0,[z0,z1,z2,z3,z967,z12]),(0,[z13,z0,z1,z2,z496,z5]),(0,[z0,z1,z2,z968,z3,z12]),(0,[z0,z1,z2,z287,z3,z29])],[(0,[z0,z84,z2,z55,z5,z12]),(0,[z0,z969,z2,z3,z5,z12]),(0,[z0,z970,z2,z3,z5,z12]),(0,[z0,z79,z48,z3,z5,z6]),(0,[z0,z588,z48,z3,z5,z12]),(0,[z0,z1,z2,z3,z971,z5]),(0,[z0,z1,z2,z3,z972,z12]),(0,[z51,z243,z1,z2,z3,z5]),(0,[z0,z1,z2,z5,z45,z165])],[(0,[z0,z1,z2,z276,z16,z12]),(0,[z0,z1,z2,z3,z5,z973]),(0,[z0,z122,z1,z2,z4,z12]),(0,[z0,z1,z2,z974,z5,z12]),(0,[z0,z975,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z976]),(0,[z0,z108,z2,z3,z730,z12]),(0,[z13,z0,z977,z2,z3,z5])],[(0,[z44,z0,z1,z2,z5,z56])],[(0,[z617,z13,z0,z1,z2,z5]),(0,[z13,z0,z1,z2,z3,z932])],[(0,[z0,z1,z2,z3,z5,z978]),(0,[z478,z1,z2,z3,z5,z9])],[(0,[z0,z130,z2,z3,z5,z104]),(0,[z0,z28,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z979,z12])],[(0,[z980,z0,z1,z2,z3,z5]),(0,[z13,z151,z137,z2,z3,z5]),(0,[z0,z1,z2,z416,z5,z304]),(0,[z1,z2,z3,z5,z6,z9]),(0,[z0,z1,z229,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z981]),(0,[z0,z1,z10,z2,z287,z3]),(0,[z982,z51,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z330,z69,z5,z12]),(0,[z0,z26,z239,z3,z5,z12]),(0,[z13,z0,z1,z2,z14,z81])],[(0,[z584,z1,z2,z3,z47,z12]),(0,[z0,z1,z2,z3,z5,z983]),(0,[z13,z0,z1,z2,z65,z5])],[(0,[z0,z1,z2,z984,z3,z5]),(0,[z279,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z160,z5])],[(0,[z51,z1,z2,z3,z113,z5])],[(0,[z0,z1,z2,z55,z5,z104]),(0,[z94,z1,z2,z30,z3,z47]),(0,[z187,z0,z1,z11,z5,z12]),(0,[z0,z794,z2,z3,z5,z12]),(0,[z0,z99,z2,z14,z3,z12])],[(0,[z0,z985,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z986])],[(0,[z0,z1,z2,z987,z5,z12]),(1,[z0,z1,z718,z5,z12])],[(0,[z0,z130,z2,z3,z228,z12]),(0,[z0,z1,z2,z3,z5,z988]),(0,[z0,z1,z102,z3,z145,z12])],[(0,[z0,z1,z405,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z438]),(0,[z0,z1,z2,z3,z458,z83])],[(0,[z0,z1,z2,z3,z5,z989]),(0,[z990,z1,z2,z3,z5,z12])],[(0,[z206,z1,z2,z3,z106,z9])],[(0,[z0,z84,z2,z3,z244,z12]),(0,[z13,z0,z1,z2,z234,z5])],[(0,[z23,z1,z188,z3,z5,z9]),(0,[z697,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z991,z12]),(0,[z25,z0,z1,z2,z30,z121]),(0,[z0,z1,z2,z3,z12,z780])],[(0,[z0,z1,z2,z55,z228,z12]),(0,[z0,z92,z2,z35,z5,z238]),(0,[z13,z664,z1,z2,z81,z5]),(0,[z13,z776,z1,z2,z3,z5])],[(0,[z0,z1,z992,z3,z5,z12]),(0,[z23,z1,z188,z55,z5,z12]),(0,[z277,z0,z1,z2,z4,z5]),(0,[z206,z51,z1,z2,z3,z5]),(0,[z0,z2,z775,z3,z5,z12]),(0,[z0,z1,z2,z3,z993,z12]),(0,[z0,z1,z2,z3,z5,z392]),(0,[z0,z167,z19,z3,z5,z12]),(0,[z0,z1,z19,z718,z5,z12]),(0,[z0,z1,z2,z3,z5,z571])],[(0,[z0,z1,z2,z994,z3,z5]),(0,[z44,z0,z1,z2,z30,z5])]],
   [[(0,[z0,z200,z1,z2,z3,z5]),(0,[z277,z206,z1,z2,z3,z5]),(0,[z34,z1,z2,z3,z113,z6]),(0,[z0,z995,z1,z2,z3,z5]),(0,[z298,z0,z52,z2,z3,z5])],[(0,[z0,z1,z2,z996,z5,z12]),(0,[z88,z1,z2,z4,z5,z12]),(0,[z0,z1,z2,z306,z3,z425]),(0,[z0,z1,z2,z3,z5,z997]),(0,[z0,z1,z2,z3,z5,z998])],[(0,[z0,z1,z2,z999,z3,z5]),(0,[z0,z135,z590,z3,z36,z12]),(0,[z0,z1,z2,z3,z5,z1000])],[(0,[z151,z137,z2,z30,z3,z5]),(0,[z0,z84,z2,z3,z5,z24]),(0,[z594,z1,z2,z3,z47,z12]),(0,[z0,z1,z1001,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z140])],[(0,[z0,z1,z2,z3,z5,z1002]),(0,[z0,z2,z3,z730,z5,z12])],[(0,[z0,z1003,z2,z3,z5,z12])],[(0,[z13,z0,z1,z2,z337,z5]),(0,[z1004,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z244,z104])],[(0,[z94,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z726]),(0,[z0,z1,z2,z5,z12,z45])],[(0,[z0,z1,z2,z3,z5,z1005]),(0,[z0,z1,z2,z3,z1006,z12]),(0,[z0,z1,z2,z3,z5,z522]),(0,[z403,z0,z1,z464,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1007])],[(0,[z0,z1,z2,z3,z5,z1008]),(0,[z0,z1,z146,z3,z145,z12])],[(0,[z171,z0,z67,z107,z5,z12]),(0,[z0,z1,z2,z1009,z3,z5]),(0,[z0,z1010,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z86]),(0,[z0,z1,z2,z3,z5,z1011]),(0,[z427,z0,z1,z2,z3,z5]),(0,[z44,z0,z1,z2,z5,z50]),(0,[z13,z0,z1,z2,z3,z1012])],[(0,[z0,z1,z2,z1013,z5,z12]),(0,[z0,z1,z2,z1014,z3,z5]),(0,[z372,z13,z0,z1,z2,z5]),(0,[z0,z75,z1,z3,z197,z12]),(0,[z402,z0,z1,z2,z3,z639])],[]],
   [[(0,[z0,z1,z216,z3,z5,z166]),(0,[z0,z1,z1015,z3,z5,z12]),(0,[z0,z1,z2,z1016,z3,z5]),(0,[z25,z277,z0,z1,z2,z5])],[(0,[z23,z1,z188,z3,z244,z12]),(0,[z0,z1,z2,z1017,z5,z12]),(0,[z0,z1,z1018,z2,z3,z5]),(0,[z171,z0,z2,z30,z107,z5]),(0,[z0,z1,z2,z1019,z5,z12]),(0,[z13,z0,z1,z2,z30,z5])],[(0,[z0,z1,z1020,z3,z5,z12]),(0,[z44,z0,z1,z2,z266,z5])],[],[(0,[z0,z1,z2,z1021,z3,z5]),(0,[z0,z1,z3,z828,z145,z12])],[(0,[z0,z1,z2,z1022,z55,z5]),(0,[z25,z0,z1,z2,z396,z12]),(0,[z0,z1,z2,z1023,z3,z5]),(0,[z44,z0,z1,z2,z5,z254])],[(0,[z0,z1,z2,z3,z1024,z12]),(0,[z0,z1,z2,z1025,z5,z12]),(0,[z0,z1,z1026,z3,z5,z12]),(0,[z0,z1,z2,z14,z601,z12]),(0,[z13,z0,z1,z2,z520,z5])],[(0,[z0,z1,z2,z3,z106,z12]),(0,[z171,z0,z505,z2,z107,z5])],[(0,[z0,z1,z2,z3,z228,z24]),(0,[z0,z167,z3,z11,z5,z12]),(0,[z187,z0,z1,z30,z11,z5])],[(0,[z51,z1,z2,z3,z107,z5]),(0,[z0,z1,z2,z1027,z3,z5]),(0,[z25,z13,z0,z1,z2,z43])],[(0,[z0,z1,z229,z3,z5,z9]),(0,[z0,z1,z2,z30,z5,z417])],[(0,[z0,z1,z2,z3,z5,z89]),(0,[z0,z1,z2,z3,z1028,z5]),(0,[z0,z1,z10,z2,z3,z6]),(0,[z0,z1,z1029,z3,z5,z12])],[(0,[z0,z1,z2,z30,z3,z5]),(0,[z0,z1,z2,z5,z6,z45])],[(0,[z0,z1,z216,z3,z283,z12]),(0,[z315,z1,z2,z194,z5,z12]),(0,[z0,z1,z590,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1030,z12]),(0,[z0,z1,z2,z1031,z5,z12]),(0,[z1032,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z175,z3,z621])],[(0,[z0,z1,z1033,z3,z5,z12]),(0,[z0,z92,z2,z35,z5,z12]),(0,[z0,z1,z1034,z3,z5,z12]),(0,[z187,z0,z1,z125,z11,z5])]],
   [[(0,[z0,z292,z2,z35,z5,z12]),(0,[z119,z1,z2,z3,z5,z6])],[(0,[z25,z13,z0,z1,z2,z113]),(0,[z0,z1,z2,z3,z5,z1035]),(0,[z25,z0,z1,z2,z522,z121])],[(0,[z13,z0,z1,z2,z276,z5]),(0,[z0,z1,z505,z2,z3,z5]),(0,[z0,z1,z2,z30,z539,z5])],[(0,[z0,z130,z2,z337,z5,z12]),(0,[z25,z13,z0,z1,z2,z121])],[(0,[z0,z1,z405,z3,z16,z12]),(0,[z0,z1,z216,z296,z5,z12]),(0,[z207,z1,z2,z3,z5,z825]),(0,[z0,z1,z2,z3,z5,z1036]),(0,[z13,z0,z1,z2,z432,z5])],[(0,[z0,z1,z2,z3,z5,z1037]),(0,[z0,z1,z718,z11,z5,z12]),(0,[z0,z1,z2,z3,z5,z1038]),(0,[z0,z1,z2,z3,z5,z1039]),(0,[z298,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z127,z81,z5]),(0,[z0,z1,z2,z3,z5,z1040])],[(0,[z0,z1,z2,z3,z1041,z12])],[],[(0,[z0,z1,z2,z3,z16,z166]),(0,[z0,z1,z2,z1042,z3,z5]),(0,[z85,z1,z131,z3,z5,z12]),(0,[z0,z1043,z1,z2,z3,z5]),(0,[z0,z278,z2,z3,z36,z12]),(0,[z0,z204,z3,z76,z5,z12]),(0,[z0,z1,z2,z1044,z5,z12])],[(0,[z1045,z0,z1,z2,z3,z5]),(0,[z25,z13,z0,z135,z1,z2])],[(0,[z0,z1046,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1047]),(0,[z34,z1,z2,z3,z113,z9]),(0,[z0,z195,z2,z3,z5,z63]),(0,[z0,z1,z2,z814,z5,z12]),(0,[z912,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z780,z157])],[(0,[z0,z1,z115,z3,z5,z56]),(0,[z13,z0,z1,z2,z3,z905])],[(0,[z0,z130,z2,z3,z5,z6]),(0,[z94,z1,z2,z3,z47,z6])],[(0,[z0,z1,z2,z3,z5,z1048])],[(0,[z0,z1,z216,z3,z5,z12]),(0,[z0,z1,z2,z1049,z5,z12]),(0,[z0,z1,z2,z3,z5,z1050])]],
   [[(0,[z0,z1,z2,z3,z5,z1051]),(0,[z13,z44,z0,z1,z2,z5])],[(0,[z0,z1,z2,z3,z5,z825]),(0,[z0,z1,z2,z3,z5,z1052])],[(0,[z0,z1,z2,z276,z5,z129]),(0,[z0,z1,z2,z81,z770,z12])],[(0,[z0,z1,z2,z55,z5,z6]),(0,[z605,z1,z131,z3,z5,z12]),(0,[z1,z587,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1012,z12]),(0,[z51,z52,z1,z2,z3,z5])],[(0,[z154,z39,z2,z3,z5,z129]),(0,[z25,z13,z664,z1,z2,z5])],[(1,[z790,z2,z3,z5,z12]),(0,[z88,z1,z2,z753,z5,z12]),(0,[z0,z1,z177,z3,z5,z254]),(0,[z0,z1,z680,z3,z5,z56]),(0,[z13,z0,z1,z2,z81,z5])],[(0,[z0,z204,z102,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1053]),(0,[z0,z1,z919,z30,z3,z5])],[(0,[z1054,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1055,z5,z12]),(0,[z0,z1,z2,z194,z321,z12]),(0,[z95,z1,z2,z3,z5,z6]),(0,[z664,z51,z1,z2,z3,z5])],[(0,[z1,z2,z3,z496,z5,z9]),(0,[z0,z1,z10,z48,z3,z12]),(0,[z0,z1,z2,z3,z1056,z12])],[(0,[z0,z1,z2,z416,z5,z12]),(0,[z0,z2,z3,z5,z12,z871]),(0,[z0,z1,z2,z30,z5,z473]),(0,[z0,z1,z2,z718,z5,z12])],[(0,[z23,z130,z188,z3,z5,z12]),(0,[z1057,z0,z1,z2,z3,z5]),(0,[z0,z926,z2,z30,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1058]),(0,[z0,z1,z2,z337,z244,z12]),(0,[z206,z1,z2,z194,z5,z12]),(0,[z1,z2,z4,z81,z5,z9]),(0,[z0,z448,z48,z3,z5,z12]),(0,[z0,z1,z2,z1059,z3,z5])],[(0,[z0,z1,z2,z296,z16,z12]),(0,[z0,z26,z609,z3,z5,z12]),(0,[z914,z0,z1,z2,z5,z12]),(0,[z51,z1,z552,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1060,z12]),(0,[z0,z201,z48,z3,z5,z12]),(0,[z0,z1061,z2,z3,z5,z12]),(0,[z34,z1,z2,z3,z787,z12]),(0,[z0,z1,z2,z1062,z3,z5]),(0,[z0,z135,z2,z3,z509,z12])],[(0,[z0,z1,z2,z3,z5,z1063])]],
   [[(0,[z277,z0,z1,z2,z5,z447]),(0,[z0,z1,z2,z170,z3,z621]),(0,[z0,z1,z2,z3,z5,z1064]),(0,[z316,z0,z1,z2,z3,z210])],[(0,[z0,z1,z1065,z3,z5,z12]),(0,[z1,z2,z767,z3,z5,z12])],[(0,[z664,z1,z2,z3,z5,z12]),(0,[z0,z122,z1,z2,z327,z3]),(0,[z0,z1,z2,z3,z5,z1066])],[(0,[z171,z0,z2,z107,z5,z6])],[(0,[z0,z1,z2,z337,z5,z24]),(0,[z0,z1,z2,z3,z321,z551]),(0,[z1067,z0,z1,z2,z3,z5]),(0,[z1068,z0,z1,z2,z5,z6]),(0,[z187,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1069,z12])],[(0,[z0,z1,z2,z3,z244,z6]),(0,[z198,z1,z2,z4,z5,z12])],[(0,[z0,z26,z57,z3,z5,z9]),(0,[z13,z0,z28,z2,z3,z5]),(0,[z13,z0,z1,z2,z601,z5])],[(0,[z0,z1,z2,z3,z16,z12]),(0,[z0,z1,z2,z1070,z3,z5]),(0,[z0,z1,z590,z3,z5,z9]),(0,[z51,z135,z1,z2,z3,z5]),(0,[z49,z0,z2,z3,z535,z5]),(0,[z0,z1,z2,z170,z3,z157])],[(0,[z137,z790,z2,z3,z5,z12]),(0,[z1,z767,z188,z3,z5,z12]),(0,[z180,z1,z2,z3,z113,z12])],[(0,[z0,z1,z2,z1071,z3,z5]),(0,[z654,z1,z2,z3,z113,z12])],[(0,[z0,z1,z1072,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1073]),(0,[z0,z1,z2,z1074,z5,z12]),(0,[z0,z1,z2,z3,z5,z1075]),(0,[z206,z1,z2,z4,z5,z9]),(0,[z277,z0,z1,z2,z30,z5]),(0,[z51,z26,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1076,z5]),(0,[z0,z1,z1077,z3,z5,z12]),(0,[z1,z2,z3,z787,z5,z12]),(0,[z25,z13,z0,z1,z2,z47]),(0,[z553,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z1078]),(0,[z0,z1,z2,z170,z3,z780])],[(0,[z790,z39,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z1079,z12]),(0,[z0,z1,z775,z3,z5,z12]),(0,[z0,z1,z2,z5,z155,z793])],[(0,[z0,z1,z1080,z3,z5,z12]),(0,[z0,z1,z2,z3,z1081,z5])],[(1,[z1,z767,z3,z5,z12]),(0,[z555,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z1082,z3,z12]),(0,[z0,z1,z2,z3,z1083,z12])]],
   [[(0,[z0,z1,z2,z3,z5,z1084]),(0,[z0,z1,z2,z1085,z3,z5]),(0,[z13,z0,z1,z764,z3,z5]),(0,[z0,z1,z2,z3,z5,z793])],[(0,[z0,z1,z2,z3,z1086,z5]),(0,[z0,z1,z2,z3,z1087,z12]),(0,[z0,z1,z2,z910,z3,z5]),(0,[z34,z1,z2,z3,z113,z7]),(0,[z0,z1088,z2,z3,z5,z12]),(0,[z0,z977,z2,z3,z5,z12])],[],[(0,[z1089,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z276,z5,z6]),(0,[z0,z1,z2,z3,z80,z12]),(0,[z0,z1,z2,z1090,z3,z5])],[(0,[z0,z135,z2,z3,z36,z12])],[(0,[z154,z13,z39,z2,z3,z5]),(0,[z154,z39,z2,z3,z5,z6]),(0,[z888,z0,z1,z2,z3,z5]),(0,[z0,z79,z48,z3,z5,z9])],[(0,[z0,z1,z2,z30,z3,z106]),(0,[z0,z1,z10,z2,z194,z12])],[(0,[z0,z1,z2,z3,z1091,z12]),(0,[z0,z1,z2,z358,z81,z12])],[(0,[z0,z1,z2,z3,z321,z438]),(0,[z13,z0,z927,z2,z3,z5])],[(0,[z206,z1,z2,z194,z321,z12]),(0,[z0,z99,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z1092]),(0,[z0,z1,z2,z3,z5,z293]),(0,[z0,z1,z2,z3,z5,z1093]),(0,[z0,z1,z2,z3,z5,z1094]),(0,[z13,z0,z108,z2,z3,z111]),(0,[z51,z1,z102,z2,z3,z5])],[(0,[z23,z1,z188,z3,z5,z24]),(0,[z0,z1,z2,z3,z5,z1095]),(1,[z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1096,z12]),(0,[z51,z1,z2,z3,z5,z111]),(0,[z0,z1,z2,z3,z5,z1097])],[(0,[z0,z1098,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1099]),(0,[z0,z1,z2,z3,z5,z1100]),(0,[z0,z1,z2,z3,z5,z1101])],[(0,[z0,z1,z1102,z3,z5,z12]),(0,[z0,z1,z2,z55,z5,z9]),(0,[z0,z1103,z2,z3,z5,z12])],[(0,[z0,z1,z2,z1104,z5,z12]),(0,[z0,z1,z2,z3,z5,z1105]),(0,[z1,z2,z3,z5,z6,z221]),(0,[z0,z1,z2,z3,z5,z1106])]],
   [[(0,[z305,z1,z2,z4,z5,z12]),(0,[z1,z2,z3,z5,z788,z9]),(0,[z0,z51,z1,z2,z81,z5])],[(0,[z0,z1,z2,z3,z5,z1107]),(0,[z0,z1,z1108,z3,z5,z9]),(0,[z0,z17,z2,z3,z5,z248]),(0,[z0,z1,z19,z69,z5,z6]),(0,[z0,z1,z2,z3,z5,z1109]),(0,[z187,z0,z1,z29,z11,z12])],[(0,[z51,z1,z131,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1110]),(0,[z0,z1,z2,z3,z5,z1111]),(0,[z0,z975,z2,z30,z3,z5])],[(0,[z0,z1112,z2,z3,z5,z12])],[(0,[z0,z373,z1,z3,z76,z12])],[(0,[z0,z1,z2,z3,z5,z1113])],[(0,[z1114,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1115])],[(0,[z0,z1116,z1,z2,z3,z5]),(0,[z51,z1,z2,z3,z5,z6])],[(0,[z0,z84,z2,z3,z5,z12]),(0,[z25,z427,z0,z1,z2,z5]),(0,[z497,z0,z1,z3,z5,z369]),(0,[z0,z1,z2,z3,z5,z1117])],[(0,[z13,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1118,z12]),(0,[z0,z75,z1,z3,z76,z6])],[(0,[z0,z1,z1119,z2,z3,z12]),(0,[z25,z0,z1,z2,z600,z12]),(0,[z1120,z0,z1,z2,z5,z12]),(0,[z13,z0,z1,z2,z179,z5])],[(0,[z13,z0,z1,z2,z3,z228]),(0,[z0,z1,z2,z30,z3,z321]),(0,[z0,z1,z2,z3,z5,z1121])],[(0,[z0,z1,z2,z3,z5,z1122])],[(0,[z0,z1,z2,z829,z276,z5]),(0,[z0,z1,z2,z3,z1123,z12]),(0,[z171,z0,z2,z107,z5,z9]),(0,[z0,z135,z2,z30,z3,z36])],[(0,[z0,z1,z1124,z2,z3,z5]),(0,[z277,z0,z1,z2,z81,z5]),(0,[z171,z0,z229,z107,z5,z12])]],
   [[(0,[z954,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z244,z9]),(0,[z25,z0,z200,z1,z2,z5]),(0,[z0,z1,z19,z30,z69,z5]),(0,[z13,z0,z1,z1125,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1126]),(0,[z0,z1,z2,z3,z5,z1127]),(0,[z517,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z170,z45,z157])],[(0,[z0,z1,z2,z3,z5,z1128]),(0,[z0,z1,z102,z688,z3,z12])],[(0,[z0,z1,z2,z3,z5,z104]),(0,[z0,z1,z2,z3,z5,z112])],[(0,[z0,z1,z2,z1129,z5,z12]),(0,[z0,z1,z1130,z2,z3,z12]),(0,[z0,z1,z2,z1131,z3,z5])],[(0,[z1,z790,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z1132,z12]),(0,[z0,z1,z950,z3,z5,z12])],[(0,[z0,z1,z2,z1133,z3,z5]),(0,[z94,z1,z2,z3,z47,z202]),(0,[z0,z1,z2,z14,z655,z12]),(0,[z0,z1134,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1135])],[(0,[z88,z1,z2,z4,z5,z89]),(0,[z1136,z1,z2,z3,z5,z12])],[(0,[z0,z243,z2,z3,z5,z248])],[(0,[z0,z1137,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z1138,z12])],[(0,[z13,z0,z1,z2,z55,z5]),(0,[z0,z1,z67,z3,z5,z12]),(0,[z0,z1,z2,z287,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1139]),(0,[z0,z1,z2,z3,z228,z12]),(0,[z0,z1,z2,z1140,z5,z12]),(0,[z0,z1,z2,z3,z5,z1141]),(0,[z0,z167,z2,z3,z5,z12])],[(0,[z23,z1,z188,z3,z5,z12]),(0,[z13,z51,z1,z2,z5,z61]),(0,[z0,z1,z2,z170,z3,z43])],[(0,[z0,z1,z2,z276,z5,z9]),(0,[z0,z1,z2,z3,z283,z129]),(0,[z0,z1,z2,z1142,z3,z5]),(0,[z0,z92,z2,z35,z5,z140]),(0,[z0,z1,z2,z3,z5,z1143]),(1,[z0,z1,z3,z828,z12]),(0,[z0,z1,z3,z828,z5,z12]),(0,[z168,z0,z1,z3,z5,z56])]],
   [[(0,[z0,z1,z2,z3,z5,z1144]),(0,[z0,z1,z2,z3,z5,z1145]),(0,[z0,z913,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z828,z12])],[(0,[z154,z39,z2,z3,z5,z9]),(0,[z0,z1146,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z5,z1147]),(0,[z13,z861,z1,z2,z3,z5])],[(0,[z1,z2,z3,z753,z5,z12]),(0,[z51,z1,z2,z3,z5,z155])],[(0,[z13,z0,z167,z2,z3,z5]),(0,[z0,z1,z2,z1148,z3,z5])],[(0,[z0,z2,z3,z730,z111,z12]),(0,[z403,z51,z1,z2,z3,z5])],[(0,[z0,z1,z1149,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1150])],[(0,[z0,z108,z2,z3,z111,z12])],[(0,[z0,z204,z2,z3,z5,z6]),(0,[z51,z1,z2,z48,z3,z5])],[(0,[z591,z1,z2,z3,z5,z6])],[(0,[z0,z1,z10,z2,z3,z9]),(0,[z1,z2,z3,z5,z673,z9]),(1,[z0,z2,z814,z5,z12])],[(0,[z0,z1,z264,z3,z5,z12])],[(0,[z0,z2,z3,z1151,z5,z12]),(0,[z595,z0,z2,z107,z5,z12]),(0,[z748,z1,z2,z3,z5,z12])],[(0,[z259,z0,z2,z3,z5,z335]),(0,[z0,z1,z19,z69,z5,z9]),(0,[z957,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z1152,z12]),(0,[z0,z1,z2,z3,z5,z1153])],[(0,[z49,z0,z2,z3,z5,z335])],[(0,[z0,z1,z2,z1154,z5,z12]),(0,[z88,z1,z2,z3,z227,z5]),(0,[z0,z1,z2,z3,z1155,z12]),(0,[z291,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z1156,z3,z5]),(0,[z13,z0,z1,z67,z3,z5]),(0,[z0,z230,z2,z3,z5,z63])]],
   [[(0,[z0,z1,z2,z3,z5,z1157]),(0,[z0,z1,z2,z30,z416,z5])],[(0,[z0,z1,z2,z3,z5,z129]),(0,[z206,z1,z2,z194,z5,z438]),(0,[z171,z0,z2,z80,z107,z12])],[(0,[z0,z1,z2,z30,z3,z16]),(0,[z0,z1,z2,z3,z5,z1158]),(0,[z0,z1,z2,z3,z1159,z12]),(0,[z13,z0,z1,z2,z215,z5])],[],[(0,[z13,z0,z1,z2,z308,z5]),(0,[z0,z1,z2,z3,z5,z1160])],[(0,[z0,z32,z48,z3,z5,z12]),(0,[z0,z1161,z2,z3,z5,z12]),(0,[z0,z75,z1,z3,z76,z9]),(0,[z0,z1,z102,z3,z145,z571])],[(0,[z0,z1,z2,z1162,z5,z12]),(0,[z13,z0,z1,z2,z296,z5]),(0,[z1163,z0,z1,z2,z3,z5]),(0,[z78,z0,z1,z11,z5,z12])],[(0,[z0,z1,z2,z1164,z5,z12]),(0,[z316,z51,z1,z2,z3,z5])],[(0,[z0,z1,z3,z5,z1165,z12]),(0,[z0,z1,z2,z30,z109,z5]),(0,[z51,z1,z2,z3,z1166,z5])],[(0,[z0,z230,z2,z261,z3,z5])],[(0,[z151,z137,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z106,z551])],[(0,[z0,z130,z2,z3,z5,z9]),(0,[z94,z1,z2,z3,z47,z9]),(0,[z0,z243,z2,z3,z5,z63])],[(0,[z0,z1,z229,z3,z5,z12])],[(0,[z0,z130,z2,z55,z5,z12]),(0,[z13,z85,z1,z131,z3,z5]),(0,[z0,z1,z2,z3,z1167,z12]),(0,[z0,z1,z2,z3,z5,z1168]),(0,[z0,z122,z1,z505,z2,z3])],[(0,[z0,z1,z2,z3,z5,z1169]),(0,[z0,z1,z1170,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1171])],[(0,[z0,z1,z2,z3,z5,z1172]),(0,[z0,z93,z2,z3,z5,z63])]],
   [[(0,[z0,z1,z2,z3,z5,z1173]),(0,[z0,z1,z2,z306,z3,z157]),(0,[z25,z13,z0,z1,z2,z5])],[(0,[z0,z1,z2,z3,z283,z6]),(0,[z149,z1,z188,z3,z5,z12]),(0,[z25,z13,z51,z1,z2,z5]),(1,[z0,z1,z2,z5,z793])],[(0,[z0,z1,z2,z3,z1174,z5])],[(0,[z277,z51,z1,z2,z3,z5])],[(0,[z154,z39,z2,z276,z5,z12]),(0,[z0,z1175,z2,z3,z5,z12]),(0,[z270,z1,z2,z3,z5,z9])],[(0,[z0,z1,z2,z3,z5,z1176]),(0,[z168,z0,z1,z3,z5,z726]),(0,[z1177,z1,z2,z3,z5,z12])],[(0,[z0,z1,z3,z1178,z5,z12]),(0,[z0,z1,z2,z3,z5,z1179]),(0,[z34,z1,z2,z30,z3,z113])],[(0,[z51,z1,z2,z188,z3,z5]),(0,[z0,z48,z3,z672,z5,z12]),(0,[z0,z1,z590,z14,z3,z12]),(0,[z13,z1089,z1,z2,z3,z5])],[(0,[z0,z1,z216,z30,z3,z5]),(0,[z0,z1,z2,z296,z5,z6]),(0,[z0,z1,z2,z3,z1180,z5]),(0,[z0,z1,z2,z3,z5,z1181])],[(0,[z0,z1,z2,z337,z5,z12]),(0,[z0,z1,z2,z1182,z5,z12]),(0,[z13,z0,z1,z2,z655,z5]),(0,[z0,z1,z2,z3,z5,z1183])],[(0,[z0,z1,z2,z656,z5,z155]),(0,[z0,z1,z2,z1184,z5,z12]),(0,[z0,z2,z35,z814,z5,z12]),(0,[z0,z1,z19,z69,z5,z344]),(0,[z13,z0,z1,z2,z667,z5]),(0,[z0,z1185,z2,z3,z5,z12])],[(0,[z0,z1,z2,z1186,z3,z5]),(0,[z0,z1,z1187,z3,z5,z12]),(1,[z0,z775,z3,z5,z12])],[(0,[z0,z1,z2,z3,z1188,z12]),(0,[z642,z1,z2,z3,z5,z6]),(0,[z0,z648,z48,z3,z5,z12]),(0,[z13,z0,z135,z2,z3,z36]),(0,[z0,z75,z1,z3,z828,z12])],[(0,[z0,z1,z2,z3,z5,z1189]),(0,[z0,z1,z2,z308,z5,z6]),(0,[z0,z440,z2,z3,z36,z12]),(0,[z0,z79,z775,z3,z5,z12])],[(0,[z13,z0,z84,z2,z3,z5]),(0,[z1,z2,z4,z5,z417,z9]),(0,[z1190,z0,z1,z2,z5,z12]),(0,[z51,z1,z2,z69,z3,z5]),(0,[z13,z0,z1,z2,z5,z793])],[(0,[z0,z1,z2,z3,z1191,z12]),(0,[z0,z1,z2,z3,z106,z438]),(0,[z0,z1,z2,z3,z5,z1192])]],
   [[(0,[z0,z1,z405,z3,z5,z129]),(0,[z756,z0,z1,z2,z296,z5]),(0,[z0,z130,z2,z3,z244,z12]),(0,[z13,z1193,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1194]),(1,[z1,z2,z3,z5,z825])],[(0,[z0,z1195,z2,z3,z5,z12]),(0,[z0,z204,z2,z3,z5,z9]),(0,[z1,z2,z3,z5,z1196,z12]),(0,[z13,z0,z1,z2,z380,z5]),(0,[z1197,z51,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1198,z12]),(1,[z277,z1,z2,z4,z5]),(0,[z277,z1,z2,z3,z4,z5]),(0,[z0,z28,z2,z3,z5,z12]),(0,[z0,z92,z2,z30,z35,z5])],[(0,[z0,z1,z2,z30,z337,z5]),(0,[z34,z13,z1,z2,z3,z113]),(0,[z13,z0,z1,z229,z3,z5]),(0,[z0,z1199,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1200])],[(0,[z0,z1,z2,z55,z244,z12])],[],[(0,[z0,z130,z2,z3,z5,z24]),(0,[z0,z1,z2,z3,z1201,z12])],[(0,[z88,z1,z2,z4,z5,z293]),(0,[z0,z1,z2,z999,z416,z5]),(0,[z0,z243,z2,z3,z5,z846]),(0,[z51,z1,z2,z170,z3,z5])],[(0,[z427,z0,z1,z2,z5,z326]),(0,[z0,z1,z2,z14,z275,z12])],[(0,[z0,z1,z2,z3,z5,z202]),(0,[z0,z92,z2,z529,z5,z12]),(0,[z187,z0,z1,z287,z11,z5]),(0,[z664,z1,z2,z30,z3,z5])],[(0,[z0,z1202,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z1203])],[(0,[z0,z1,z2,z782,z296,z5]),(0,[z0,z1,z2,z55,z5,z24]),(0,[z95,z1,z2,z3,z227,z5])],[(0,[z206,z1,z2,z194,z5,z551]),(0,[z0,z1,z2,z3,z5,z1204]),(0,[z51,z1,z2,z81,z5,z12])]],
   [[(0,[z206,z1,z2,z3,z5,z293]),(0,[z0,z1,z2,z3,z5,z1205]),(0,[z0,z1,z2,z3,z29,z6])],[(0,[z0,z1,z2,z3,z5,z1206]),(0,[z13,z0,z1,z2,z5,z580])],[(0,[z13,z0,z75,z1,z3,z76])],[(0,[z13,z0,z1,z10,z2,z3])],[(0,[z0,z1,z1207,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1208]),(0,[z0,z1,z2,z1022,z3,z5]),(0,[z25,z0,z1,z2,z121,z6]),(0,[z0,z1,z2,z3,z5,z1209]),(0,[z0,z75,z99,z3,z76,z12]),(0,[z0,z1,z3,z5,z726,z12]),(0,[z51,z1,z2,z3,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1210])],[(0,[z0,z1,z2,z1211,z3,z5]),(0,[z13,z0,z1,z590,z3,z5])],[(0,[z0,z1212,z2,z3,z5,z12]),(0,[z0,z200,z1,z2,z81,z5]),(0,[z277,z0,z1,z2,z138,z5]),(0,[z0,z1,z2,z3,z5,z1213])],[(0,[z200,z1,z2,z3,z5,z9]),(0,[z1214,z0,z1,z2,z3,z5]),(0,[z0,z1,z102,z3,z145,z112])],[(0,[z0,z1,z2,z296,z5,z129]),(0,[z0,z1,z2,z4,z321,z12]),(0,[z1,z2,z3,z5,z203,z9]),(0,[z0,z26,z57,z3,z5,z12]),(0,[z13,z0,z1,z2,z5,z45])],[(0,[z0,z1,z2,z3,z1215,z12]),(0,[z883,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1216]),(0,[z0,z2,z3,z814,z5,z12]),(0,[z0,z1,z2,z3,z770,z12])],[(0,[z0,z1,z2,z3,z5,z1217]),(0,[z0,z1,z3,z5,z9,z896]),(0,[z0,z1,z2,z3,z5,z1218])],[(0,[z0,z1,z2,z3,z283,z9]),(0,[z0,z1,z2,z5,z9,z899]),(0,[z0,z1,z2,z3,z5,z1219]),(0,[z0,z92,z2,z814,z5,z12])],[(0,[z0,z1,z1220,z3,z5,z12]),(0,[z0,z1,z2,z30,z367,z5]),(0,[z187,z0,z28,z11,z5,z12])],[(0,[z37,z1,z2,z194,z5,z12])],[(0,[z13,z206,z1,z2,z194,z5]),(0,[z0,z1,z2,z3,z5,z1221])]],
   [[(0,[z0,z1,z2,z30,z276,z5])],[(0,[z0,z1,z2,z3,z244,z24]),(0,[z0,z1,z2,z3,z321,z6]),(0,[z0,z1,z2,z1222,z5,z12]),(0,[z25,z51,z1,z2,z3,z5]),(0,[z13,z1177,z1,z2,z3,z5])],[(0,[z0,z1,z405,z3,z5,z6]),(0,[z1,z2,z3,z5,z9,z312]),(0,[z0,z1,z102,z30,z3,z145])],[(0,[z0,z1,z2,z3,z1223,z12]),(0,[z0,z1224,z2,z3,z5,z12]),(0,[z0,z1,z1225,z2,z3,z5])],[(0,[z0,z1,z216,z3,z16,z12]),(0,[z0,z1,z2,z1226,z3,z5]),(0,[z427,z0,z1,z2,z81,z5])],[(0,[z0,z1,z2,z3,z1227,z12]),(0,[z0,z1,z2,z3,z5,z610]),(0,[z88,z1,z2,z173,z4,z5]),(0,[z51,z1,z2,z3,z5,z9]),(0,[z0,z135,z2,z3,z730,z12])],[(0,[z0,z1,z2,z3,z1228,z12]),(0,[z85,z1,z131,z3,z5,z86]),(0,[z0,z1,z2,z3,z5,z1229])],[(0,[z0,z1,z2,z3,z5,z1230]),(0,[z0,z1231,z2,z3,z5,z12]),(0,[z0,z1,z1232,z3,z5,z12]),(0,[z51,z1,z2,z3,z5,z184])],[(0,[z0,z1,z2,z308,z5,z9]),(0,[z0,z1,z120,z3,z5,z404]),(0,[z0,z79,z48,z3,z5,z12]),(0,[z13,z0,z99,z2,z3,z5])],[(0,[z13,z0,z1,z2,z3,z29]),(0,[z0,z1,z2,z30,z531,z5])],[(0,[z0,z1,z2,z1233,z5,z12]),(0,[z664,z1,z2,z3,z5,z438])],[(0,[z0,z1,z2,z3,z5,z1234]),(0,[z0,z1,z2,z3,z5,z1235])],[(0,[z0,z1,z2,z1236,z5,z12]),(0,[z647,z1,z2,z3,z5,z9]),(0,[z13,z0,z1,z2,z5,z334])],[],[(0,[z0,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z1237]),(0,[z0,z1,z2,z3,z5,z1238])],[(0,[z1239,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z753,z5,z12]),(0,[z0,z122,z1,z2,z194,z12]),(0,[z0,z1,z19,z69,z5,z20])]],
   [[(0,[z0,z1,z2,z1070,z337,z5]),(0,[z602,z1,z2,z3,z5,z9]),(0,[z0,z1,z325,z3,z5,z254]),(0,[z0,z1,z2,z3,z5,z1240]),(0,[z0,z1,z2,z3,z5,z1241])],[(0,[z0,z84,z2,z30,z3,z5]),(0,[z1045,z0,z1,z2,z416,z5]),(0,[z171,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z30,z14,z81])],[(0,[z1242,z0,z1,z2,z3,z5]),(0,[z51,z1,z2,z35,z3,z5]),(0,[z0,z1,z2,z3,z5,z1243])],[(0,[z0,z1,z1108,z3,z5,z12]),(0,[z453,z51,z1,z2,z3,z5]),(0,[z13,z0,z1,z2,z5,z355])],[(0,[z0,z1,z2,z3,z5,z1244]),(0,[z0,z1,z2,z3,z1245,z5]),(0,[z13,z915,z1,z2,z3,z5])],[(0,[z85,z1,z131,z30,z3,z5]),(0,[z34,z51,z1,z2,z3,z5]),(0,[z0,z26,z122,z2,z3,z12])],[(0,[z0,z1,z2,z3,z5,z1246]),(0,[z0,z122,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z1247]),(0,[z270,z1,z2,z138,z3,z5])],[],[(0,[z0,z1,z2,z3,z5,z1248]),(0,[z0,z1,z2,z3,z1249,z12]),(0,[z34,z1,z2,z3,z113,z304]),(0,[z1,z2,z3,z5,z568,z6]),(0,[z25,z0,z99,z2,z3,z12])],[(0,[z0,z1,z2,z3,z5,z1250]),(0,[z168,z0,z1,z3,z5,z219]),(0,[z13,z0,z1,z2,z575,z5]),(0,[z0,z108,z2,z30,z3,z111])],[(0,[z0,z1,z2,z3,z5,z1251]),(0,[z0,z1252,z1,z2,z3,z5]),(0,[z34,z1,z2,z308,z113,z12])],[(0,[z0,z1,z2,z308,z47,z12]),(0,[z0,z1,z2,z3,z29,z9]),(0,[z222,z1,z2,z3,z5,z9]),(0,[z13,z0,z1,z2,z275,z5]),(0,[z0,z1,z1253,z3,z5,z12]),(1,[z0,z1,z2,z3,z780])],[(0,[z0,z1,z2,z656,z3,z5]),(0,[z0,z1,z69,z718,z5,z12])],[(0,[z0,z108,z264,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z1254]),(0,[z0,z1,z2,z3,z5,z1255])],[(0,[z88,z51,z1,z2,z3,z5]),(0,[z1,z2,z3,z5,z428,z6]),(0,[z0,z607,z2,z3,z5,z50])]],
   [[(0,[z34,z1,z2,z3,z113,z12]),(0,[z0,z1,z2,z3,z5,z1256]),(0,[z0,z1257,z2,z3,z5,z12])],[(0,[z13,z0,z1,z2,z3,z283]),(0,[z1068,z0,z1,z2,z5,z12])],[(0,[z0,z1,z2,z3,z787,z12])],[(0,[z0,z1,z2,z3,z244,z12]),(0,[z0,z1,z2,z3,z5,z788]),(0,[z206,z1,z2,z194,z106,z12]),(0,[z497,z0,z1,z3,z5,z56]),(0,[z13,z0,z1,z2,z672,z5]),(0,[z51,z1,z120,z2,z3,z5])],[(0,[z277,z0,z1,z2,z194,z5]),(0,[z0,z1,z2,z1258,z3,z5])],[(0,[z0,z1,z67,z30,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1259]),(0,[z1,z131,z767,z3,z5,z12]),(0,[z0,z1,z819,z3,z5,z12]),(0,[z0,z167,z2,z30,z3,z5]),(0,[z0,z1260,z2,z3,z5,z12]),(0,[z361,z51,z1,z2,z3,z5])],[(0,[z23,z1,z188,z30,z3,z5]),(0,[z94,z1,z2,z3,z47,z139]),(0,[z0,z1,z2,z3,z5,z1261])],[(0,[z13,z0,z1,z102,z3,z145])],[(0,[z333,z1,z2,z3,z5,z9]),(0,[z469,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1262])],[(0,[z0,z1,z2,z3,z5,z1263]),(0,[z0,z1,z2,z3,z5,z1264]),(0,[z13,z0,z1,z2,z5,z353]),(0,[z0,z52,z2,z3,z5,z50])],[(0,[z0,z1,z2,z1265,z3,z5]),(0,[z0,z1266,z1,z2,z3,z5]),(0,[z49,z0,z2,z3,z5,z846])],[(0,[z149,z1,z2,z3,z5,z9]),(0,[z0,z1,z102,z3,z162,z12]),(0,[z0,z1,z2,z3,z5,z344]),(0,[z1193,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z488]),(0,[z0,z1,z405,z3,z5,z9]),(0,[z0,z1,z2,z1267,z3,z5]),(0,[z336,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z5,z1268]),(0,[z25,z0,z1,z2,z364,z12]),(0,[z856,z1,z2,z3,z5,z12])],[(0,[z0,z1,z2,z1269,z5,z12]),(0,[z0,z1,z2,z3,z5,z1270]),(0,[z1,z2,z194,z753,z5,z12]),(0,[z0,z1,z2,z308,z5,z7]),(0,[z1,z2,z3,z113,z787,z12]),(0,[z0,z1,z2,z3,z5,z1271])],[(0,[z1,z2,z3,z5,z6,z825]),(0,[z0,z1,z2,z656,z5,z184]),(0,[z44,z0,z1,z2,z5,z6]),(0,[z13,z0,z1010,z2,z3,z5])]],
   [[],[(0,[z0,z1,z2,z276,z5,z12])],[(0,[z0,z1,z2,z1272,z3,z5]),(0,[z0,z1,z2,z3,z5,z231])],[(0,[z154,z39,z2,z3,z5,z12]),(0,[z0,z1,z264,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z209])],[(0,[z0,z1,z2,z1273,z3,z5]),(0,[z0,z1,z2,z3,z5,z7]),(0,[z187,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z1274])],[(0,[z1275,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1276,z5,z12]),(0,[z1,z2,z3,z4,z5,z293]),(0,[z0,z1,z2,z3,z5,z1277])],[(0,[z0,z1,z2,z3,z1278,z12]),(0,[z439,z1,z2,z3,z5,z9]),(0,[z0,z1,z102,z3,z145,z6])],[(0,[z151,z137,z2,z3,z5,z9]),(0,[z427,z51,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1279,z5]),(0,[z25,z13,z0,z108,z1,z2]),(0,[z0,z1,z2,z3,z5,z1280])],[(0,[z0,z1281,z1,z2,z3,z5]),(0,[z187,z0,z167,z11,z5,z12]),(0,[z0,z1,z10,z2,z30,z3]),(0,[z0,z1,z2,z3,z5,z1282]),(0,[z13,z0,z1,z2,z612,z5])],[(0,[z0,z1,z2,z3,z1283,z12]),(0,[z0,z1,z2,z3,z1284,z12]),(0,[z0,z1,z2,z3,z5,z1285])],[(0,[z0,z1,z2,z1286,z5,z12]),(0,[z0,z1,z2,z3,z5,z1287]),(0,[z0,z1,z10,z2,z3,z12]),(0,[z0,z1,z1288,z3,z5,z12])],[(0,[z0,z33,z57,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1289]),(0,[z13,z51,z1,z2,z30,z5])],[(0,[z0,z1290,z2,z3,z5,z12]),(0,[z0,z2,z3,z5,z1291,z12]),(0,[z1,z2,z3,z5,z825,z9]),(0,[z0,z1,z590,z3,z5,z12]),(0,[z0,z1,z1292,z2,z3,z5]),(0,[z0,z1293,z2,z3,z5,z12])],[(0,[z51,z137,z1,z2,z3,z5]),(0,[z171,z0,z2,z814,z5,z12]),(0,[z0,z1,z19,z69,z5,z12])],[(0,[z0,z1,z2,z3,z717,z12])]],
   [[(0,[z0,z2,z3,z5,z50,z846])],[(0,[z0,z1,z2,z3,z5,z1294]),(0,[z88,z1,z2,z4,z5,z6]),(0,[z0,z122,z1,z2,z3,z9]),(0,[z0,z1,z2,z3,z5,z1295]),(0,[z402,z13,z0,z1,z2,z5]),(0,[z0,z1,z2,z3,z5,z1296])],[(0,[z0,z1,z1297,z3,z5,z12]),(0,[z291,z1,z2,z3,z113,z12]),(0,[z665,z1,z2,z3,z5,z9]),(0,[z13,z0,z1,z2,z3,z80])],[(0,[z0,z1,z2,z3,z5,z1298]),(0,[z25,z0,z1,z2,z678,z12]),(0,[z51,z1,z2,z3,z36,z5]),(0,[z13,z808,z1,z2,z3,z5])],[(0,[z207,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z14,z81,z6])],[(0,[z0,z1299,z1,z2,z3,z5]),(0,[z0,z1,z229,z30,z3,z5]),(0,[z0,z1,z2,z3,z5,z1300]),(0,[z25,z0,z51,z1,z2,z5])],[(0,[z0,z1,z2,z296,z5,z9]),(0,[z0,z1301,z2,z3,z5,z12]),(0,[z626,z1,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z266,z8]),(0,[z0,z99,z2,z30,z3,z5]),(0,[z13,z0,z1,z1034,z3,z5])],[(0,[z1302,z0,z1,z2,z3,z5]),(0,[z51,z1,z2,z138,z3,z5])],[],[(0,[z0,z1,z2,z3,z5,z1303]),(0,[z25,z0,z1,z590,z3,z12])],[(0,[z938,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z30,z3,z228]),(0,[z0,z775,z48,z3,z5,z12]),(0,[z0,z1,z2,z1304,z3,z12])],[(1,[z0,z1,z2,z770,z12])],[(0,[z0,z1,z2,z3,z5,z1305]),(0,[z348,z0,z2,z3,z5,z50]),(0,[z0,z1,z2,z1306,z5,z12]),(0,[z1307,z1,z2,z3,z5,z12]),(0,[z0,z1,z57,z10,z3,z12]),(0,[z51,z1,z2,z3,z5,z61])],[(0,[z0,z130,z2,z3,z5,z12]),(0,[z13,z0,z1,z216,z3,z5]),(0,[z0,z1,z216,z3,z5,z129]),(0,[z0,z1,z1308,z3,z5,z12]),(0,[z25,z0,z1,z2,z415,z12]),(0,[z94,z1,z2,z3,z47,z12]),(0,[z236,z0,z1,z3,z5,z219]),(0,[z0,z1,z2,z3,z5,z1309]),(0,[z51,z1,z19,z2,z3,z5]),(0,[z0,z1,z1125,z3,z5,z12])],[(0,[z0,z1310,z1,z2,z3,z12]),(0,[z0,z1311,z1,z2,z3,z5]),(0,[z94,z1,z2,z3,z787,z12]),(0,[z95,z51,z1,z2,z3,z5]),(0,[z51,z1,z2,z3,z5,z63])],[(0,[z1,z2,z3,z5,z438,z9])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 505) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 505).take 507) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1012).take 369) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1381)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [505, 507, 369] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 101).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 244).take 147).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 391).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [101, 143, 147, 121] = true :=
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

end PEqualNP.Outside.L_meta_40372

theorem PEqualNP.Outside.L_meta_40372 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276669632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276669632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40372.solve