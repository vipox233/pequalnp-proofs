import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45890

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
  Nat.testBit (4008373992 * 2 ^ 32 + 4008372384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00002061604142d4#64 ++ 0x00000818581050b5#64 ++ 0xfc49e8e3e8c7c7ff#64 ++ 0xff127a38fa31f1ff#64 : BitVec 256),
   (0x4112830ca31b1972#64 ++ 0x9044a0c328c6c65c#64 ++ 0xffb6971cf73b39f3#64 ++ 0xffeda5c73dcece7c#64 : BitVec 256),
   (0x80c51816182c2c29#64 ++ 0x20314605860b0b0a#64 ++ 0xbcc7181f183c3e3d#64 ++ 0x6f31c607c60f0f8f#64 : BitVec 256),
   (0x02e81da01dc03781#64 ++ 0xc0ba076807700de0#64 ++ 0x73f81fe01fc03fc3#64 ++ 0xdcfe07f807f00ff0#64 : BitVec 256),
   (0x04ffc0001eb68002#64 ++ 0x013ff00007ada000#64 ++ 0xe5ffe0001fffc003#64 ++ 0x397ff80007fff000#64 : BitVec 256),
   (0x08fffedbc0000000#64 ++ 0x023fffb6f0000000#64 ++ 0xeaffffffe0000000#64 ++ 0xfabffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfc49e8e3e8c7c7ff 0xff127a38fa31f1ff

def z1 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z2 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe5ffe0001fffc003 0x397ff80007fff000

def z3 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeaffffffe0000000 0xfabffffff8000000

def z4 : W := mkw 0x4112830c831a1922 0x9044a0c320c68648 0x73b6171c173839c3 0xdced85c705ce0e70

def z5 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffb6971cf73b39f3 0xffeda5c73dcece7c

def z6 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z7 : W := mkw 0x80050016182c2c29 0x20014005860b0b0a 0x9c07001f183c3e3d 0x2701c007c60f0f8f

def z8 : W := mkw 0x0000010001001100 0x8000004000400440 0x11000000170039c3 0x0440000005c00e70

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z10 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x01b6000017380000 0x006d800005ce0000

def z11 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xefffffffffffc003 0xfbfffffffffff000

def z12 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x0a001fffe0000000 0xc28007fff8000000

def z13 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc4108030804063d 0x6f104200c201018f

def z14 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x43b6971cf73b39c2 0x90eda5c73dcece70

def z15 : W := mkw 0x0000000020010050 0x0000000008004014 0xfc418803e80707ff 0xff106200fa01c1ff

def z16 : W := mkw 0x00000020204142d4 0x00000008081050b5 0x1400000008c7c7ff 0x050000000231f1ff

def z17 : W := mkw 0x08fffefbe04142d4 0x023fffbef81050b5 0xfeffffffe8c7c7ff 0xffbffffffa31f1ff

def z18 : W := mkw 0x41000124235b5bf6 0x9040004908d6d6fd 0x150000001fffffff 0x0540000007ffffff

def z19 : W := mkw 0x4112a36de35b5bf6 0x9044a8db78d6d6fd 0xffffffffffffffff 0xffffffffffffffff

def z20 : W := mkw 0x0000002000400280 0x00000008001000a0 0xf449e8e008c7c7c3 0xfd127a380231f1f0

def z21 : W := mkw 0x0817e25bc0000000 0x0205f896f0000000 0x8807e01fe0000000 0x2201f807f8000000

def z22 : W := mkw 0x88fffedfd82c2c29 0x223fffb7f60b0b0a 0xfefffffff83c3e3d 0xffbffffffe0f0f8f

def z23 : W := mkw 0x00ffc00000000000 0x003ff00000000000 0xe0ffe00000000000 0x383ff80000000000

def z24 : W := mkw 0x0cfffefbfef7c2d6 0x033fffbeffbdf0b5 0xffffffffffffc7ff 0xfffffffffffff1ff

def z25 : W := mkw 0x80000004182c2c29 0x20000001060b0b0a 0xbc410803183c3e3d 0x6f104200c60f0f8f

def z26 : W := mkw 0x00e820617cc142d4 0x003a08185f3050b5 0xfdf9e8e3ffc7c7ff 0xff7e7a38fff1f1ff

def z27 : W := mkw 0x0817fedbc0000000 0x0205ffb6f0000000 0x8a07ffffe0000000 0xe281fffff8000000

def z28 : W := mkw 0x84c518161ebeac2b 0x2131460587afab0a 0xbdc7181f1ffffe3f 0x6f71c607c7ffff8f

def z29 : W := mkw 0x04ed40001ca48000 0x013b500007292000 0x0049600008c4c000 0x0012580002313000

def z30 : W := mkw 0x0cfffedbdca48000 0x033fffb6f7292000 0xeaffffffe8c4c000 0xfabffffffa313000

def z31 : W := mkw 0x040000203ef7c2d6 0x010000080fbdf0b5 0x150000001fffc7ff 0x0540000007fff1ff

def z32 : W := mkw 0x41128308a3131152 0x9044a0c228c4c454 0x43308700e70301c2 0x90cc21c039c0c070

def z33 : W := mkw 0x80c53877786d6efd 0x20314e1dde1b5bbf 0xfccff8fff8ffffff 0xff33fe3ffe3fffff

def z34 : W := mkw 0x02001da001403781 0xc080076800500de0 0x12001fe000003fc0 0xc48007f800000ff0

def z35 : W := mkw 0x02e81d801d803501 0xc0ba076007600d40 0x03b0170017003800 0x00ec05c005c00e00

def z36 : W := mkw 0x00000020204102d0 0x00000008081040b4 0xfc4888e0e8c307f3 0xff1222383a30c1fc

def z37 : W := mkw 0x06ed5da01de4b781 0xc1bb576807792de0 0x73f97fe01fc4ffc3 0xdcfe5ff807f13ff0

def z38 : W := mkw 0x00c5000018240000 0x0031400006090000 0xa4c70000183c0001 0x2931c000060f0000

def z39 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0x4138e00007c3c002 0x104e380001f0f000

def z40 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x14410803183c3e3d 0x05104200c60f0f8f

def z41 : W := mkw 0x49ffdf9e831a1922 0x927ff7e7a0c68648 0x03b6171c17383800 0x00ed85c705ce0e00

def z42 : W := mkw 0x08fffefbe04142d4 0x023fffbef81050b5 0xfaffffffe00007fc 0xfebffffff80001ff

def z43 : W := mkw 0x0afffffbddc03781 0xc2bffffef7700de0 0xfbffffffffc03fc3 0xfefffffffff00ff0

def z44 : W := mkw 0x88fffedfc0082c29 0x223fffb7f0020b0a 0xfaffffffe0003e3c 0xfebffffff8000f8f

def z45 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x1886181f10383e3c 0x46218607c40e0f8f

def z46 : W := mkw 0x08ffde9a80000000 0x023ff7a6a0000000 0x02b6171c00000000 0x00ad85c700000000

def z47 : W := mkw 0x0cffde9a9eb68002 0x033ff7a6a7ada000 0xe7fff71c1fffc003 0x39fffdc707fff000

def z48 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfff79f1fff3f3fff 0xfffde7c7ffcfcfff

def z49 : W := mkw 0x84ffd8161ebeac2b 0x213ff60587afab0a 0xe5fff01c1ffff803 0x397ffc0707fffe00

def z50 : W := mkw 0x0000000000000000 0x0000000000000000 0xe049e00000000000 0x3812780000000000

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0xe8008000e0000000 0xfa00200038000000

def z52 : W := mkw 0x04ffc1001fb69102 0x813ff04007eda440 0xf7fff7001ffff9c3 0xfdfffdc007fffe70

def z53 : W := mkw 0x06fadda01fd2b783 0xc1beb76807f4ade0 0x73f8ffe01fc3ffc3 0xdcfe3ff807f0fff0

def z54 : W := mkw 0x0000204140000000 0x0000081050000000 0xfc49e8e3e804063d 0xff127a38fa01018f

def z55 : W := mkw 0x04c500001eb68002 0x0131400007ada000 0xa5c700001fffc003 0x2971c00007fff000

def z56 : W := mkw 0x0000204160014054 0x0000081058005015 0x8c01e003e007c03c 0x23007800f801f00f

def z57 : W := mkw 0x02e83de17dc177d5 0xc0ba0f785f705df5 0xfff9ffe3ffc7ffff 0xfffe7ff8fff1ffff

def z58 : W := mkw 0x04ffe0617ef7c2d6 0x013ff8185fbdf0b5 0xfdffe8e3ffffc7ff 0xff7ffa38fffff1ff

def z59 : W := mkw 0x4112820ca21b0872 0x1044a0832886c21c 0x8c06801ce03b0030 0x2301a007380ec00c

def z60 : W := mkw 0x45ffc30c9fbe9922 0x917ff0c327efa648 0x03b6171c17383800 0x00ed85c705ce0e00

def z61 : W := mkw 0x08fffedbd8240000 0x023fffb6f6090000 0xeefffffff83c0001 0xfbbffffffe0f0000

def z62 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x43b817e017c039c2 0x90ee05f805f00e70

def z63 : W := mkw 0x00e81c8000000000 0x003a072000000000 0x62f81fe000000000 0xd8be07f800000000

def z64 : W := mkw 0x80ed1c96182c2c29 0x203b4725860b0b0a 0xfeff1fff183c3e3d 0xffbfc7ffc60f0f8f

def z65 : W := mkw 0x00000020204142d4 0x00000008081050b5 0x744808e008c7c7ff 0xdd1202380231f1ff

def z66 : W := mkw 0x82ed1cb61cec2ea9 0x60bb472d873b0baa 0xbccf18ff18fc3e3d 0x6f33c63fc63f0f8f

def z67 : W := mkw 0x4100030c81081920 0x904000c320420648 0x0200171c00003800 0x008005c700000e00

def z68 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x9d06801cf73b39f3 0x2741a0073dcece7c

def z69 : W := mkw 0x49ffffffe35b5bf6 0x927ffffff8d6d6fd 0xffffffffffffffff 0xffffffffffffffff

def z70 : W := mkw 0x41000104231b1972 0x9040004108c6c65c 0x15000000173b39f3 0x0540000005cece7c

def z71 : W := mkw 0x00c0180018002401 0x0030060006000900 0x30c0180018003e01 0x4c30060006000f80

def z72 : W := mkw 0x82ed1db61dec3fa9 0xe0bb476d877b0fea 0xffff1fff1ffc3fff 0xffffc7ffc7ff0fff

def z73 : W := mkw 0x08ed7edbc0000000 0x023b5fb6f0000000 0x0a497fffe0000000 0xc2925ffff8000000

def z74 : W := mkw 0x84ed58161cacac29 0x213b5605872b2b0a 0xbccf781f18fcfe3d 0x6f33de07c63f3f8f

def z75 : W := mkw 0x00000020204142d4 0x00000008081050b5 0xbc41080308c7c7ff 0x6f104200c231f1ff

def z76 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfc08e0e0e0c3c1f3 0xff0238383830f07c

def z77 : W := mkw 0x0000010001001100 0x8000004000400440 0x03b0170017003800 0x00ec05c005c00e00

def z78 : W := mkw 0x0000206140404284 0x00000818501010a1 0x000008e30000060c 0x00000238c0000183

def z79 : W := mkw 0x0417c00002368002 0x0105f000008da000 0x8407e000003fc000 0x2101f800000ff000

def z80 : W := mkw 0x0affdfba9dc03781 0xc2bff7eea7700de0 0x73fe1ffc1fc03fc3 0xdcff87ff07f00ff0

def z81 : W := mkw 0x02003de1614177d5 0xc0800f7858505df5 0xfe49ffe3e8c7ffff 0xff927ff8fa31ffff

def z82 : W := mkw 0x020001201dc03781 0xc080004807700de0 0x110000001fc03fc3 0x0440000007f00ff0

def z83 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0x1800181f00003e3c 0x46000607c0000f8f

def z84 : W := mkw 0x0000000020010050 0x0000000008004014 0xfc49e000e8c7c1f3 0xff1278003a31f07c

def z85 : W := mkw 0x0cfffedbc6928002 0x033fffb6f1a4a000 0xebffffffe7c3c002 0xfafffffff9f0f000

def z86 : W := mkw 0x00c5181200000000 0x0031460480000000 0xa8c7181f00000000 0x6a31c607c0000000

def z87 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0x4238e7e0e0000000 0x908e39f838000000

def z88 : W := mkw 0x0000002000400280 0x00000008001000a0 0x704808e008c007c3 0xdc120238023001f0

def z89 : W := mkw 0x0000204140000000 0x0000081050000000 0x4008e0e0e0000000 0x9002383838000000

def z90 : W := mkw 0x040000001eb68002 0x0100000007ada000 0xe549e0001fffc003 0x3952780007fff000

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x004108030804060c 0x00104200c2010183

def z92 : W := mkw 0x4112820ca21b0872 0x1044a0832886c21c 0xeeb6971ce03b0030 0xfbada5c7380ec00c

def z93 : W := mkw 0x80c51816002c0828 0x20314605800b020a 0xacc7181f003c003c 0x6b31c607c00f000f

def z94 : W := mkw 0x04ffd8001eb6a403 0x013ff60007ada900 0xf5fff8001ffffe03 0x7d7ffe0007ffff80

def z95 : W := mkw 0x45ffc30cbfbf9972 0x917ff0c32fefe65c 0xfffff71cfffff9f3 0xfffffdc73ffffe7c

def z96 : W := mkw 0x0012800002120002 0x0004a00000848000 0xe5b68000173b0003 0x396da00005cec000

def z97 : W := mkw 0xc1c519163b3f3d7b 0xb07146458ecfcf5e 0xbdc7181f1f3f3fff 0x6f71c607c7cfcfff

def z98 : W := mkw 0x020005a001401380 0xc0800168005004e0 0x020007e0000001c0 0x808001f800000070

def z99 : W := mkw 0x00c5181600080820 0x0031460580020208 0xbcc7181f10383831 0x6f31c607c40e0e0c

def z100 : W := mkw 0x0000204140000000 0x0000081050000000 0x8801e003e0000000 0x22007800f8000000

def z101 : W := mkw 0x45ffe36dffffdbf6 0x917ff8db7ffff6fd 0xffffffffffffffff 0xffffffffffffffff

def z102 : W := mkw 0x4112832ca35b5bf6 0x9044a0cb28d6d6fd 0xffb6971cffffffff 0xffeda5c73fffffff

def z103 : W := mkw 0x80ed18161cac2c29 0x203b4605872b0b0a 0xfdff181f1ffc3e3f 0x7f7fc607c7ff0f8f

def z104 : W := mkw 0x0417c0001eb68002 0x0105f00007ada000 0x8507e0001fffc003 0x2141f80007fff000

def z105 : W := mkw 0x020001201dc03781 0xc080004807700de0 0x714808e01fc03fc3 0xdc52023807f00ff0

def z106 : W := mkw 0x0805605340000000 0x02015814d0000000 0x0001600300000000 0x00005800c0000000

def z107 : W := mkw 0x49ffffdfe31b1972 0x927ffff7f8c6c65c 0xfffffffff73b39f3 0xfffffffffdcece7c

def z108 : W := mkw 0x02e81ca01cc02681 0x40ba0728073009a0 0x61f808e01fc00603 0x187e023807f00180

def z109 : W := mkw 0x8000000018242409 0x2000000006090902 0x000000000804060c 0x0000000002010183

def z110 : W := mkw 0x02e81ca01cc02681 0x40ba0728073009a0 0x704808e008c007c3 0xdc120238023001f0

def z111 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x41bee00017fbc002 0x106fb80005fef000

def z112 : W := mkw 0x06ffdda01ff6b783 0xc1bff76807fdade0 0xf7ffffe01fffffc3 0xfdfffff807fffff0

def z113 : W := mkw 0x0400000006928002 0x0100000001a4a000 0x0100000007c3c002 0x0040000001f0f000

def z114 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x114808e01fc03fc3 0x0452023807f00ff0

def z115 : W := mkw 0x08ed7cd340000000 0x023b5f34d0000000 0x004968e300000000 0x00125a38c0000000

def z116 : W := mkw 0x00000020204142d4 0x00000008081050b5 0x0000000000c3c1c2 0x000000000030f070

def z117 : W := mkw 0x043fc00006b68002 0x010ff00001ada000 0xc53fe00007ffc002 0x314ff80001fff000

def z118 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x144968e308c7c7ff 0x05125a38c231f1ff

def z119 : W := mkw 0x8000181200002409 0x2000060480000902 0x000008030000060c 0x00000200c0000183

def z120 : W := mkw 0x04ed60617ce5c2d4 0x013b58185f3970b5 0xfc49e8e3e8c7c7ff 0xff127a38fa31f1ff

def z121 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0xea49ffffe0000000 0xfa927ffff8000000

def z122 : W := mkw 0x0000010001001100 0x8000004000400440 0x73b01700170039c3 0xdcec05c005c00e70

def z123 : W := mkw 0x453ac308a7939152 0x914eb0c229e4e454 0x4338e700e7c3c1c2 0x90ce39c039f0f070

def z124 : W := mkw 0x88ed7cd7582c2c29 0x223b5f35d60b0b0a 0xbccf78ff183c3e3d 0x6f33de3fc60f0f8f

def z125 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x73b817e017c039c3 0xdcee05f805f00e70

def z126 : W := mkw 0x80c5181218242409 0x2031460486090902 0x004108030804060c 0x00104200c2010183

def z127 : W := mkw 0x00ffc00018240000 0x003ff00006090000 0xe4ffe000183c0001 0x393ff800060f0000

def z128 : W := mkw 0x02e81ca01cc02681 0x40ba0728073009a0 0x004808e008c00600 0x0012023802300180

def z129 : W := mkw 0x43fa9facbfdb3ff3 0xd0fea7eb2ff6cffc 0xfffe9ffcfffb3ff3 0xffffa7ff3ffecffc

def z130 : W := mkw 0x80000004182c2c29 0x20000001060b0b0a 0x14000000183c3e3d 0x05000000060f0f8f

def z131 : W := mkw 0x080026c9c0000000 0x020009b270000000 0x020007e0e0000000 0x808001f838000000

def z132 : W := mkw 0x0000204160014054 0x0000081058005015 0x08000003e000003c 0x02000000f800000f

def z133 : W := mkw 0x4112a34de31b5976 0x9044a8d378c6d65d 0xffb7f71ff73ff9ff 0xffedfdc7fdcffe7f

def z134 : W := mkw 0x04ffe0615ef6c286 0x013ff81857bdb0a1 0xe5ffe8e31fffc60f 0x397ffa38c7fff183

def z135 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x433807e007c001c2 0x90ce01f801f00070

def z136 : W := mkw 0x493ae7cde31b1972 0x924eb9f378c6c65c 0xffbef7fcf73b39f3 0xffefbdff3dcece7c

def z137 : W := mkw 0x82ed1db21de43789 0xe0bb476c87790de2 0x73f91fe31fc43fcf 0xdcfe47f8c7f10ff3

def z138 : W := mkw 0x0000206140404284 0x00000818501010a1 0x000860e000c0c000 0x0002183800303000

def z139 : W := mkw 0x08ffde9a80000000 0x023ff7a6a0000000 0xe2fff71c00000000 0x38bffdc700000000

def z140 : W := mkw 0x08ed7cd340000000 0x023b5f34d0000000 0xa8cf78ff00000000 0x6a33de3fc0000000

def z141 : W := mkw 0x020001203dc177d5 0xc08000480f705df5 0x150000001fc7ffff 0x0540000007f1ffff

def z142 : W := mkw 0x020001001d803501 0xc080004007600d40 0x0100000017003800 0x0040000005c00e00

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x0049600008c4c000 0x0012580002313000

def z144 : W := mkw 0x0000000000000000 0x0000000000000000 0xe449e00008c7c003 0x391278000231f000

def z145 : W := mkw 0x08fffedbc2120002 0x023fffb6f0848000 0xeffffffff73b0003 0xfbfffffffdcec000

def z146 : W := mkw 0x02e81c801c802401 0x40ba072007200900 0x0000000000000000 0x0000000000000000

def z147 : W := mkw 0x0405400000248000 0x0101500000092000 0x000160000004c000 0x0000580000013000

def z148 : W := mkw 0x0812e249c0000000 0x0204b89270000000 0x0000e000e0000000 0x0000380038000000

def z149 : W := mkw 0x0cffde9a9eb68002 0x033ff7a6a7ada000 0x03b6171c17380000 0x00ed85c705ce0000

def z150 : W := mkw 0x84ffd8161ebeac2b 0x213ff60587afab0a 0xfdfff81f1ffffe3f 0x7f7ffe07c7ffff8f

def z151 : W := mkw 0x4112a24de21b4876 0x1044a8937886d21d 0x8c07e01fe03fc03c 0x2301f807f80ff00f

def z152 : W := mkw 0x4100030ca1091970 0x904000c32842465c 0x1a00171ce00039f0 0xc68005c738000e7c

def z153 : W := mkw 0x84ffd8161ebeac2b 0x213ff60587afab0a 0x01b6101c17383800 0x006d840705ce0e00

def z154 : W := mkw 0x4917e25fe21b0872 0x1245f897f886c21c 0x8c07e01fe03b0030 0x2301f807f80ec00c

def z155 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x4008e0e0e0c3c1c2 0x900238383830f070

def z156 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xfff91fe31fc43fff 0xfffe47f8c7f10fff

def z157 : W := mkw 0x0000204160014054 0x0000081058005015 0xbc41e803e807c63d 0x6f107a00fa01f18f

def z158 : W := mkw 0x08d7fa5bc0000000 0x0235fe96f0000000 0xa8c7f81fe0000000 0x6a31fe07f8000000

def z159 : W := mkw 0x80050016002c0828 0x20014005800b020a 0xbc47081f083c063d 0x6f11c207c20f018f

def z160 : W := mkw 0x0012a249c0000000 0x0004a89270000000 0xeaffffffe0000000 0xfabffffff8000000

def z161 : W := mkw 0x0812bedbc0000000 0x0204afb6f0000000 0xeab69fffe0000000 0xfaada7fff8000000

def z162 : W := mkw 0x0012a269e04142d4 0x0004a89a781050b5 0xfeffffffe8c7c7ff 0xffbffffffa31f1ff

def z163 : W := mkw 0xc1d79b1ebb3f3d7b 0xb075e6c7aecfcf5e 0xfff79f1fff3f3fff 0xfffde7c7ffcfcfff

def z164 : W := mkw 0x47ffdfacbfffbff3 0xd1fff7eb2fffeffc 0xfffffffcfffffff3 0xffffffff3ffffffc

def z165 : W := mkw 0x0000000400080820 0x0000000100020208 0x1400000010383831 0x05000000040e0e0c

def z166 : W := mkw 0x08ffde9a80000000 0x023ff7a6a0000000 0x62fe1ffc00000000 0xd8bf87ff00000000

def z167 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x1486101c183c3e3d 0x05218407060f0f8f

def z168 : W := mkw 0x80050016002c0828 0x20014005800b020a 0xbc87101f103c383d 0x6f21c407c40f0e0f

def z169 : W := mkw 0x4100030ca1091970 0x904000c32842465c 0xbe86171cf03839f1 0xefa185c73c0e0e7c

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x180008030000063c 0x46000200c000018f

def z171 : W := mkw 0x00e800001c800000 0x003a000007200000 0x61f800001fc00003 0x187e000007f00000

def z172 : W := mkw 0x84ffc0041ebeac2b 0x213ff00107afab0a 0xf5ffe0001ffffe3f 0x3d7ff80007ffff8f

def z173 : W := mkw 0x0417c00002368002 0x0105f000008da000 0x0006000000380000 0x00018000000e0000

def z174 : W := mkw 0x0817e27be04142d4 0x0205f89ef81050b5 0xfc4fe8ffe8c7c7ff 0xff13fa3ffa31f1ff

def z175 : W := mkw 0x82ed3df77ded7ffd 0xe0bb4f7ddf7b5fff 0xffffffffffffffff 0xffffffffffffffff

def z176 : W := mkw 0x41d29b0cbb1b3d73 0x9074a6c32ec6cf5c 0xfff69f1cff3b3ff3 0xfffda7c73fcecffc

def z177 : W := mkw 0x00ffe061604142d4 0x003ff818581050b5 0xfcffe8e3e8c7c7ff 0xff3ffa38fa31f1ff

def z178 : W := mkw 0x00e81d8001001100 0x803a076000400440 0x73f81fe0170039c3 0xdcfe07f805c00e70

def z179 : W := mkw 0x49003fdfe1091970 0x92400ff7f842465c 0x1a001fffe00039f0 0xc68007fff8000e7c

def z180 : W := mkw 0x00000020204142d4 0x00000008081050b5 0x10000000000007fc 0x04000000000001ff

def z181 : W := mkw 0x0012820880000000 0x0004a08220000000 0xeab6971ce0000000 0xfaada5c738000000

def z182 : W := mkw 0x04ed40001eb68002 0x013b500007ada000 0x054960001fffc003 0x0152580007fff000

def z183 : W := mkw 0x80002065786d6efd 0x200008195e1b5bbf 0xfc49e8e3f8ffffff 0xff127a38fe3fffff

def z184 : W := mkw 0x0000204160014054 0x0000081058005015 0x0000e000e003c000 0x000038003800f000

def z185 : W := mkw 0x0000206140404284 0x00000818501010a1 0x004968e308c4c60c 0x00125a38c2313183

def z186 : W := mkw 0x80000004002c0828 0x20000001000b020a 0x04000000003c003c 0x01000000000f000f

def z187 : W := mkw 0x00fa9e8880000000 0x003ea7a220000000 0xeafe9ffce0000000 0xfabfa7ff38000000

def z188 : W := mkw 0x00e801001d801100 0x803a004007600440 0x73f817001fc039c3 0xdcfe05c007f00e70

def z189 : W := mkw 0x4112830c831a1922 0x9044a0c320c68648 0xe7b6971c173b3803 0x39eda5c705cece00

def z190 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x180008e3e00007fc 0xc6000238f80001ff

def z191 : W := mkw 0x00ffc00000000000 0x003ff00000000000 0xe4ffe00008c7c003 0x393ff8000231f000

def z192 : W := mkw 0x02003de1614177d5 0xc0800f7858505df5 0x1a001fe3e0003ffc 0xc68007f8f8000fff

def z193 : W := mkw 0x0aed7cf35cc02681 0x42bb5f3cd73009a0 0x004968e308c00600 0x00125a38c2300180

def z194 : W := mkw 0x0000000020010050 0x0000000008004014 0x14000000000301f3 0x050000000000c07c

def z195 : W := mkw 0x022825e165c153d4 0xc08a0978597054f5 0xff79efe3efc7c7ff 0xffde7bf8fbf1f1ff

def z196 : W := mkw 0x0ced7cd35ca48000 0x033b5f34d7292000 0x004968e308c4c000 0x00125a38c2313000

def z197 : W := mkw 0x00ffc20880000000 0x003ff08220000000 0xeafff71ce0000000 0xfabffdc738000000

def z198 : W := mkw 0x82c519361dec3fa9 0xe0b1464d877b0fea 0xbdc7181f1ffc3fff 0x6f71c607c7ff0fff

def z199 : W := mkw 0x0000000400080820 0x0000000100020208 0xbc86101c10383831 0x6f218407040e0e0c

def z200 : W := mkw 0x04ffc0003eb78052 0x013ff0000fade014 0xfdffe000ffffc1f3 0xff7ff8003ffff07c

def z201 : W := mkw 0x49fffedfe21b0872 0x127fffb7f886c21c 0xeeffffffe03b0030 0xfbbffffff80ec00c

def z202 : W := mkw 0x8cfffedfdebeac2b 0x233fffb7f7afab0a 0xfffffffffffffe3f 0xffffffffffffff8f

def z203 : W := mkw 0x00c52061786542d4 0x003148185e1950b5 0xfccfe8e3f8ffc7ff 0xff33fa38fe3ff1ff

def z204 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfccff81f18fffe3f 0x7f33fe07c63fff8f

def z205 : W := mkw 0x0012800002120002 0x0004a00000848000 0x01b6000017380000 0x006d800005ce0000

def z206 : W := mkw 0x0000000002120002 0x0000000000848000 0x05000000173b0003 0x0140000005cec000

def z207 : W := mkw 0x040000001eb68002 0x0100000007ada000 0x050000001fffc003 0x0140000007fff000

def z208 : W := mkw 0x00d780001a360002 0x0035e000068d8000 0xe5f780001f3f0003 0x397de00007cfc000

def z209 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfffff71cfffff9f3 0xfffffdc73ffffe7c

def z210 : W := mkw 0x022805a01dc03781 0xc08a016807700de0 0x533807e01fc03fc3 0x94ce01f807f00ff0

def z211 : W := mkw 0x04ffc0041ebe8822 0x013ff00107afa208 0xfdfff01c1ffff833 0x7f7ffc0707fffe0c

def z212 : W := mkw 0x43fa9fa8bfd337d3 0xd0fea7ea2ff4cdf4 0x73f89fe0ffc33fc3 0xdcfe27f83ff0cff0

def z213 : W := mkw 0x4112a36de35b5bf6 0x9044a8db78d6d6fd 0xffbef7fcf7fbf9f3 0xffefbdff3dfefe7c

def z214 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x4049e8e3e8c7c7ce 0x90127a38fa31f1f3

def z215 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x13b01fe017003fc0 0xc4ec07f805c00ff0

def z216 : W := mkw 0x08003efbe04142d4 0x02000fbef81050b5 0xfe49ffffe8c7c7ff 0xff927ffffa31f1ff

def z217 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0xeabef7fce0000000 0xfaafbdff38000000

def z218 : W := mkw 0x0000000020010050 0x0000000008004014 0xfc008000e00301f3 0xff0020003800c07c

def z219 : W := mkw 0x0012820c80080820 0x0004a08320020208 0xfeb6971cf0383831 0xffada5c73c0e0e0c

def z220 : W := mkw 0x02c019201dc03781 0xc0b0064807700de0 0x31c018001fc03fc3 0x4c70060007f00ff0

def z221 : W := mkw 0x00c5181200000000 0x0031460480000000 0x0086101c00000000 0x0021840700000000

def z222 : W := mkw 0x02e81d801d803501 0xc0ba076007600d40 0x73b01700170039c3 0xdcec05c005c00e70

def z223 : W := mkw 0x0000012001401380 0x80000048005004e0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z224 : W := mkw 0x84d7d8161a3eac2b 0x2135f605868fab0a 0xbcc7f81f183ffe3d 0x6f31fe07c60fff8f

def z225 : W := mkw 0x0000204140000000 0x0000081050000000 0xec49e8e3e8c7c003 0xfb127a38fa31f000

def z226 : W := mkw 0x41002165635b5bf6 0x9040085958d6d6fd 0xfd49e8e3ffffffff 0xff527a38ffffffff

def z227 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x01ff60001ffcc000 0x007fd80007ff3000

def z228 : W := mkw 0x02ed1db21dc03781 0xc0bb476c87700de0 0xfbff1fff1fc03fc3 0xfeffc7ffc7f00ff0

def z229 : W := mkw 0x04ffc00006928002 0x013ff00001a4a000 0xe1ffe00007c3c002 0x387ff80001f0f000

def z230 : W := mkw 0x08ed7cf3604142d4 0x023b5f3cd81050b5 0xfc49e8e3e8c7c7ff 0xff127a38fa31f1ff

def z231 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x1bb6171cf73839f0 0xc6ed85c73dce0e7c

def z232 : W := mkw 0x00ed400000000000 0x003b500000000000 0x0049600000000000 0x0012580000000000

def z233 : W := mkw 0x4100236de1495bf4 0x904008db785256fd 0xfe49ffffe8c7ffff 0xff927ffffa31ffff

def z234 : W := mkw 0x020000201cc02681 0x40800008073009a0 0x0000000008c00600 0x0000000002300180

def z235 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x42bef7fce0000000 0x90afbdff38000000

def z236 : W := mkw 0xc117831ea33f197a 0xb045e0c7a8cfc65e 0xffb7971ff73f39ff 0xffede5c7fdcfce7f

def z237 : W := mkw 0xc9ffffdffb3f3d7b 0xb27ffff7fecfcf5e 0xffffffffff3f3fff 0xffffffffffcfcfff

def z238 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x30c6181c18383e01 0x4c318607060e0f80

def z239 : W := mkw 0x00c0182018402681 0x00300608061009a0 0x70c818e018c03fc3 0xdc32063806300ff0

def z240 : W := mkw 0x04ffdc801eb68002 0x013ff72007ada000 0xe7ffffe01fffc003 0xf9fffff807fff000

def z241 : W := mkw 0x00c5181218002401 0x0031460486000900 0xb8c7181f18003e01 0x6e31c607c6000f80

def z242 : W := mkw 0x02e81ca01cc02681 0x40ba0728073009a0 0x30c818e018c03e01 0x4c32063806300f80

def z243 : W := mkw 0x0000000400080820 0x0000000100020208 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z244 : W := mkw 0x02001da001403781 0xc080076800500de0 0x73b01fe017003fc3 0xdcec07f805c00ff0

def z245 : W := mkw 0x80050016002c0828 0x20014005800b020a 0x0006001c00380000 0x00018007000e0000

def z246 : W := mkw 0x88d7fa5fd82c2c29 0x2235fe97f60b0b0a 0xbcc7f81ff83c3e3d 0x6f31fe07fe0f0f8f

def z247 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x8c49e8e3e8c7c63c 0x23127a38fa31f18f

def z248 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xcf36871ce73b01f2 0xb3cda1c739cec07c

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x604808e000000000 0xd812023800000000

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x61b0000017000003 0x186c000005c00000

def z251 : W := mkw 0x04ffc2089eb68002 0x013ff08227ada000 0xeffff71cffffc003 0xfbfffdc73ffff000

def z252 : W := mkw 0x0affdf9a9d803501 0xc2bff7e6a7600d40 0x03b6171c17003800 0x00ed85c705c00e00

def z253 : W := mkw 0x00c0180018002401 0x0030060006000900 0x0040080008000600 0x0010020002000180

def z254 : W := mkw 0x433a87aca7db1bf2 0xd0cea1eb29f6c6fc 0xffbe97fcf7fb39f3 0xffefa5ff3dfece7c

def z255 : W := mkw 0x08c53edbc0000000 0x02314fb6f0000000 0xaac71fffe0000000 0xeab1c7fff8000000

def z256 : W := mkw 0x06fffde17ff7f7d7 0xc1bfff785ffdfdf5 0xffffffe3ffffffff 0xfffffff8ffffffff

def z257 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0xe5bee00017fbc003 0x396fb80005fef000

def z258 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xbc4108e3e80407fd 0xef104238fa0101ff

def z259 : W := mkw 0x88fffedbd8242409 0x223fffb6f6090902 0xeaffffffe804060c 0xfabffffffa010183

def z260 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c0100030004003c 0x23004000c001000f

def z261 : W := mkw 0x00128208a0010050 0x0004a08228004014 0xfeb6971ce00301f3 0xffada5c73800c07c

def z262 : W := mkw 0x430001243fdb3ff3 0xd0c000490ff6cffc 0x150000001ffb3ff3 0x0540000007fecffc

def z263 : W := mkw 0x00000020204142d4 0x00000008081050b5 0xf449e00008c7c7ff 0x3d1278000231f1ff

def z264 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x5b30971ce70339f2 0xd6cc25c739c0ce7c

def z265 : W := mkw 0x4112a369e35353d6 0x9044a8da78d4d4f5 0xff79efe3efc7c7ff 0xffde7bf8fbf1f1ff

def z266 : W := mkw 0x00c0180018002401 0x0030060006000900 0x0080100010003800 0x0020040004000e00

def z267 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xa8c7181f10383800 0x6a31c607c40e0e00

def z268 : W := mkw 0x80052077606d4afc 0x2001481dd81b52bf 0xfc4fe8ffe8ffc7ff 0xff13fa3ffa3ff1ff

def z269 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x5808e8e3e0c3c7fe 0xd6023a38f830f1ff

def z270 : W := mkw 0x00e800001c800000 0x003a000007200000 0xe5f9e0001fc7c003 0x397e780007f1f000

def z271 : W := mkw 0x0417c00002368002 0x0105f000008da000 0xe5b7e000173fc003 0x396df80005cff000

def z272 : W := mkw 0x82ed1cb21ce42689 0x60bb472c873909a2 0x004908e308c4060c 0x00124238c2310183

def z273 : W := mkw 0x00c5181218240000 0x0031460486090000 0xacc7181f183c0001 0x6b31c607c60f0000

def z274 : W := mkw 0x08001e9a80000000 0x020007a6a0000000 0x0200171c00000000 0x008005c700000000

def z275 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x43780fe00fc007c2 0x90de03f803f001f0

def z276 : W := mkw 0x80c51836186c2ea9 0x2031460d861b0baa 0xfccf18ff18fc3fff 0xff33c63fc63f0fff

def z277 : W := mkw 0x00ed00001ca40000 0x003b400007290000 0xe5ff00001ffc0003 0x397fc00007ff0000

def z278 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0x0000101c00003800 0x0000040700000e00

def z279 : W := mkw 0x4112830c831a1922 0x9044a0c320c68648 0xebb6971cf7383800 0xfaeda5c73dce0e00

def z280 : W := mkw 0x0000000020010050 0x0000000008004014 0x40008000e00301c2 0x900020003800c070

def z281 : W := mkw 0x0000204160014054 0x0000081058005015 0xfc01e003e007c1ff 0xff007800f801f07f

def z282 : W := mkw 0x02e83ce15cc06685 0x40ba0f38573019a1 0x004968e308c4c60c 0x00125a38c2313183

def z283 : W := mkw 0x00fa80001e920002 0x003ea00007a48000 0xe5fe80001ffb0003 0x397fa00007fec000

def z284 : W := mkw 0x4912bfdfe31b1972 0x9244aff7f8c6c65c 0xffb69ffff73b39f3 0xffeda7fffdcece7c

def z285 : W := mkw 0x0817e25be0014054 0x0205f896f8005015 0x8c07e01fe007c03c 0x2301f807f801f00f

def z286 : W := mkw 0x06e81da01ff6b783 0xc1ba076807fdade0 0x77f81fe01fffffc3 0xddfe07f807fffff0

def z287 : W := mkw 0x08fffcd340000000 0x023fff34d0000000 0xe0ffe8e300000000 0x383ffa38c0000000

def z288 : W := mkw 0x80c53857782d6c7d 0x20314e15de0b5b1f 0xbcc7f81ff83ffe3d 0x6f31fe07fe0fff8f

def z289 : W := mkw 0x0000204140000000 0x0000081050000000 0xe849e8e3e0000000 0xfa127a38f8000000

def z290 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe5b68000173b0003 0x396da00005cec000

def z291 : W := mkw 0x00001c8000000000 0x0000072000000000 0x02001fe000000000 0xc08007f800000000

def z292 : W := mkw 0x450001043fbf9972 0x914000410fefe65c 0x150000001ffff9f3 0x0540000007fffe7c

def z293 : W := mkw 0x4100010421091970 0x904000410842465c 0x10000000000039f0 0x0400000000000e7c

def z294 : W := mkw 0x02e83de17dc177d5 0xc0ba0f785f705df5 0x7bf81fe3ffc03fff 0xdefe07f8fff00fff

def z295 : W := mkw 0x4100236de1495bf4 0x904008db785256fd 0x1a001fffe0003ffc 0xc68007fff8000fff

def z296 : W := mkw 0xc1d7bb7ffb7f7fff 0xb075eedffedfdfff 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x0086101c10383800 0x00218407040e0e00

def z298 : W := mkw 0x86ffddb61ffebfab 0xe1bff76d87ffafea 0xffffffff1fffffff 0xffffffffc7ffffff

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x6048000008c00003 0x1812000002300000

def z300 : W := mkw 0x08fffedbdc800000 0x023fffb6f7200000 0xebffffffffc00003 0xfafffffffff00000

def z301 : W := mkw 0x020001201dc03781 0xc080004807700de0 0x73b017001fc03fc3 0xdcec05c007f00ff0

def z302 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x13b017001fc03fc3 0x04ec05c007f00ff0

def z303 : W := mkw 0x80c50016182c0828 0x20314005860b020a 0xacc7001f183c003d 0x2b31c007c60f000f

def z304 : W := mkw 0x8000387760496efd 0x20000e1dd8125bbf 0xfc49f8ffe8c7ffff 0xff127e3ffa31ffff

def z305 : W := mkw 0x80c5181218242409 0x2031460486090902 0x30c1180318043e0d 0x4c304600c6010f83

def z306 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfeffffffe804063d 0xffbffffffa01018f

def z307 : W := mkw 0x4312832cbfdb3ff3 0xd0c4a0cb2ff6cffc 0xffb6971cfffb3ff3 0xffeda5c73ffecffc

def z308 : W := mkw 0x02ffdda01dc03781 0xc0bff76807700de0 0xf3ffffe01fc03fc3 0xfcfffff807f00ff0

def z309 : W := mkw 0x88ed7cd358242409 0x223b5f34d6090902 0x004968e30804060c 0x00125a38c2010183

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x8401e0000007c000 0x210078000001f000

def z311 : W := mkw 0x02e81d801d803501 0xc0ba076007600d40 0x63f81fe017003800 0xd8fe07f805c00e00

def z312 : W := mkw 0x02e81da03dc137d1 0xc0ba07680f704df4 0xfff89fe0ffc33ff3 0xfffe27f83ff0cffc

def z313 : W := mkw 0x00e800001c800000 0x003a000007200000 0x0048000008c00000 0x0012000002300000

def z314 : W := mkw 0x4112830c831a1922 0x9044a0c320c68648 0x03b6171c17383800 0x00ed85c705ce0e00

def z315 : W := mkw 0x00002161614153d4 0x80000858585054f5 0xfff9ffe3ffc7ffff 0xfffe7ff8fff1ffff

def z316 : W := mkw 0x8005001200240008 0x2001400480090002 0x000100030004000c 0x00004000c0010003

def z317 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x1c0008e3e8c7c7ff 0xc7000238fa31f1ff

def z318 : W := mkw 0x02281da005c03781 0xc08a076801700de0 0x53381fe007c03fc2 0xd4ce07f801f00ff0

def z319 : W := mkw 0x00e83cc140000000 0x003a0f3050000000 0xeaf9ffe3e0000000 0xfabe7ff8f8000000

def z320 : W := mkw 0x00e83ce1604142d4 0x003a0f38581050b5 0xfef9ffe3e8c7c7ff 0xffbe7ff8fa31f1ff

def z321 : W := mkw 0xc1d79a1eba3f2c7b 0x3075e687ae8fcb1e 0xbcc7981ff83f3e3d 0x6f31e607fe0fcf8f

def z322 : W := mkw 0x00c5181200000000 0x0031460480000000 0x0041080300000000 0x00104200c0000000

def z323 : W := mkw 0x0000002000400280 0x00000008001000a0 0x100008e0000007c0 0xc4000238000001f0

def z324 : W := mkw 0x0000000020010050 0x0000000008004014 0x8c008000e0030030 0x230020003800c00c

def z325 : W := mkw 0x0000204140004004 0x0000081050001001 0x000160030004c00c 0x00005800c0013003

def z326 : W := mkw 0x84ffd8161ebeac2b 0x213ff60587afab0a 0xbdf7181f1f3c3e3d 0x6f7dc607c7cf0f8f

def z327 : W := mkw 0x0417e0616277c2d6 0x0105f818589df0b5 0xfc4fe8e3e8ffc7ff 0xff13fa38fa3ff1ff

def z328 : W := mkw 0x0aed7df35dc03781 0xc2bb5f7cd7700de0 0x73f97fe31fc03fc3 0xdcfe5ff8c7f00ff0

def z329 : W := mkw 0x0afaffe9ddc03781 0xc2bebffa77700de0 0x73f8ffe0ffc03fc3 0xdcfe3ff83ff00ff0

def z330 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x0ab61fffe0000000 0xc2ad87fff8000000

def z331 : W := mkw 0x8affffffddec3fa9 0xe2bffffff77b0fea 0xfffffffffffc3fff 0xffffffffffff0fff

def z332 : W := mkw 0x0200012001403781 0xc080004800500de0 0x1000000000003fc0 0x0400000000000ff0

def z333 : W := mkw 0x00c0190019003501 0x8030064006400d40 0x73f01f001f003fc3 0xdcfc07c007c00ff0

def z334 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeeffffffe8c7c003 0xfbbffffffa31f000

def z335 : W := mkw 0x00e800201cc00280 0x003a0008073000a0 0x71f808e01fc007c3 0xdc7e023807f001f0

def z336 : W := mkw 0x02fa9fa89dc03781 0xc0bea7ea27700de0 0xfbfe9ffcffc03fc3 0xfeffa7ff3ff00ff0

def z337 : W := mkw 0x082864c140000000 0x020a193050000000 0x000860e000000000 0x0002183800000000

def z338 : W := mkw 0x02e81da41dc83fa1 0xc0ba076907720fe8 0xfffe1ffc1ff83ff3 0xffff87ff07fe0ffc

def z339 : W := mkw 0x0817e25bc0000000 0x0205f896f0000000 0xe84fe8ffe0000000 0xfa13fa3ff8000000

def z340 : W := mkw 0x0000000020014054 0x0000000008005015 0x040000000007c03c 0x010000000001f00f

def z341 : W := mkw 0x80c51836386d6efd 0x2031460d8e1b5bbf 0xbcc7181f18ffffff 0x6f31c607c63fffff

def z342 : W := mkw 0x06ed5ca01ce4a681 0x41bb5728073929a0 0x004968e008c4c600 0x00125a3802313180

def z343 : W := mkw 0x0012800000000000 0x0004a00000000000 0xe0b6800000000000 0x382da00000000000

def z344 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x1841181f08043e3c 0x46104607c2010f8f

def z345 : W := mkw 0x04ed40001ca48000 0x013b500007292000 0xe449e00008c7c003 0x391278000231f000

def z346 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0xea79efe3e0000000 0xfa9e7bf8f8000000

def z347 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0xbc86181f10383e3d 0x6f218607c40e0f8f

def z348 : W := mkw 0x0417c00002368002 0x0105f000008da000 0xe44fe00008ffc003 0x3913f800023ff000

def z349 : W := mkw 0x80000004182c2c29 0x20000001060b0b0a 0x0000000010383800 0x00000000040e0e00

def z350 : W := mkw 0x4112a369e35353d6 0x9044a8da78d4d4f5 0x4338e7e0e7c3c1c2 0x90ce39f839f0f070

def z351 : W := mkw 0x0017c00000000000 0x0005f00000000000 0x8007e00000000000 0x2001f80000000000

def z352 : W := mkw 0x0000010001001100 0x8000004000400440 0x43300700070001c2 0x90cc01c001c00070

def z353 : W := mkw 0x00e81c8018002401 0x003a072006000900 0x72f81fe018003e01 0xdcbe07f806000f80

def z354 : W := mkw 0x41128308a3131152 0x9044a0c228c4c454 0xebb6971ce70301c2 0xfaeda5c739c0c070

def z355 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xfdffe8031fffc63f 0x7f7ffa00c7fff18f

def z356 : W := mkw 0x00e800001c800000 0x003a000007200000 0x01b0000017000000 0x006c000005c00000

def z357 : W := mkw 0x80050016002c0828 0x20014005800b020a 0x8c07001f003c003c 0x2301c007c00f000f

def z358 : W := mkw 0x80c50004182c2c29 0x20314001060b0b0a 0xb4c70000183c3e3d 0x2d31c000060f0f8f

def z359 : W := mkw 0x02001da001403781 0xc080076800500de0 0x72481fe008c03fc3 0xdc9207f802300ff0

def z360 : W := mkw 0x0012800002120002 0x0004a00000848000 0xe5ffe0001fffc003 0x397ff80007fff000

def z361 : W := mkw 0x88c53edfd82c2c29 0x22314fb7f60b0b0a 0xbec71ffff83c3e3d 0xefb1c7fffe0f0f8f

def z362 : W := mkw 0x88003edfc0082c29 0x22000fb7f0020b0a 0x1a001fffe0003e3c 0xc68007fff8000f8f

def z363 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x17b6171c173b39f3 0x05ed85c705cece7c

def z364 : W := mkw 0x41d7830cbb3f1972 0x9075e0c32ecfc65c 0xfff7971cff3f39f3 0xfffde5c73fcfce7c

def z365 : W := mkw 0x0000002000400280 0x00000008001000a0 0x1000000008c007c3 0x04000000023001f0

def z366 : W := mkw 0x80c538735864668d 0x20314e1cd61919a3 0x004968e308c4c60c 0x00125a38c2313183

def z367 : W := mkw 0x0200012005c01380 0xc0800048017004e0 0x0100000007c001c2 0x0040000001f00070

def z368 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xcc09e0e3e0c7c1fe 0xb3027838f831f07f

def z369 : W := mkw 0x41d79b1ea31b1972 0x9075e6c7a8c6c65c 0xfff79f1ff73b39f3 0xfffde7c7fdcece7c

def z370 : W := mkw 0x083ae6e9e04142d4 0x020eb9ba781050b5 0xfe79efe3e8c7c7ff 0xff9e7bf8fa31f1ff

def z371 : W := mkw 0x0a3ae7e9c5c01380 0xc28eb9fa717004e0 0x4338e7e0e7c001c2 0x90ce39f839f00070

def z372 : W := mkw 0x80c51816382d2c79 0x203146058e0b4b1e 0xfcc7981ff83f3fff 0xff31e607fe0fcfff

def z373 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x884fe8ffe0000000 0x2213fa3ff8000000

def z374 : W := mkw 0x00e81c801c800000 0x003a072007200000 0x63f81fe01fc00003 0xd8fe07f807f00000

def z375 : W := mkw 0x41000104231b1972 0x9040004108c6c65c 0xbd86101c173b39f3 0x6f61840705cece7c

def z376 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x8ab7f71fe0000000 0x22adfdc7f8000000

def z377 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xf7f9ffe01fc7ffc3 0xfdfe7ff807f1fff0

def z378 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe1ffe00017380000 0x387ff80005ce0000

def z379 : W := mkw 0x08ed7cd340000000 0x023b5f34d0000000 0xe849e8e3e0000000 0xfa127a38f8000000

def z380 : W := mkw 0x06ffdd801fb6b503 0xc1bff76007edad40 0x03b6170017383800 0x00ed85c005ce0e00

def z381 : W := mkw 0x0afffefbdcc02681 0x42bfffbef73009a0 0xeaffffffe8c00600 0xfabffffffa300180

def z382 : W := mkw 0x41128104231b1972 0x9044a04108c6c65c 0xf5b68000173b39f3 0x3d6da00005cece7c

def z383 : W := mkw 0x45ffc20cbebf8872 0x117ff0832fafe21c 0xedffe01cffffc033 0x3b7ff8073ffff00c

def z384 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x8fb6971cf73b3830 0x23eda5c73dcece0c

def z385 : W := mkw 0x41128308a3131152 0x9044a0c228c4c454 0xff308700e70301f3 0xffcc21c039c0c07c

def z386 : W := mkw 0x0000206140404284 0x00000818501010a1 0xe449e8e308c7c60f 0x39127a38c231f183

def z387 : W := mkw 0x02001d8001003501 0xc080076000400d40 0x0200170000003800 0x008005c000000e00

def z388 : W := mkw 0x02e83de15dc03781 0xc0ba0f7857700de0 0xfbf9ffe3ffc03fc3 0xfefe7ff8fff00ff0

def z389 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xa5f700001f3c0001 0x297dc00007cf0000

def z390 : W := mkw 0xc3ff9fbebfff3ffb 0xf0ffe7efafffcffe 0xffff9fffffff3fff 0xffffe7ffffffcfff

def z391 : W := mkw 0x08fffedbd8002401 0x023fffb6f6000900 0xfafffffff8003e01 0xfebffffffe000f80

def z392 : W := mkw 0x04ffe0415eb68002 0x013ff81057ada000 0xedffe8e3ffffc003 0xfb7ffa38fffff000

def z393 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x03f81fe01fc03e00 0x00fe07f807f00f80

def z394 : W := mkw 0x0400000002368002 0x01000000008da000 0x04000000003fc000 0x01000000000ff000

def z395 : W := mkw 0x0005001200000000 0x0001400480000000 0x8807001f00000000 0x2201c007c0000000

def z396 : W := mkw 0x00ffc00002120002 0x003ff00000848000 0xe5ffe000173b0003 0x397ff80005cec000

def z397 : W := mkw 0x02e81ca01cc02681 0x40ba0728073009a0 0x62f81fe008c00600 0xd8be07f802300180

def z398 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x12481fe008c03fc0 0xc49207f802300ff0

def z399 : W := mkw 0x49ffffdbe3131152 0x927ffff6f8c4c454 0xebffffffe70301c2 0xfafffffff9c0c070

def z400 : W := mkw 0x00c5000018240000 0x0031400006090000 0xe4cfe00018ffc003 0x3933f800063ff000

def z401 : W := mkw 0x433a87a8a7d313d2 0xd0cea1ea29f4c4f4 0x433887e0e7c301c2 0x90ce21f839f0c070

def z402 : W := mkw 0x80d798161a3e2c2b 0x2035e605868f8b0a 0xfdf7981f1f3f3e3f 0x7f7de607c7cfcf8f

def z403 : W := mkw 0x00e8000000000000 0x003a000000000000 0x60f8000000000000 0x183e000000000000

def z404 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xbc86101c10383831 0x6f218407040e0e0c

def z405 : W := mkw 0x0012820880000000 0x0004a08220000000 0x8806801ce0000000 0x2201a00738000000

def z406 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xf849e8e3e00007fc 0xfe127a38f80001ff

def z407 : W := mkw 0x08003cd340000000 0x02000f34d0000000 0x000008e300000000 0x00000238c0000000

def z408 : W := mkw 0x02ed1da01de43781 0xc0bb476807790de0 0xf7ff1fe01ffc3fc3 0xfdffc7f807ff0ff0

def z409 : W := mkw 0x0417e0416237c056 0x0105f810588df015 0x8c07e003e03fc03c 0x2301f800f80ff00f

def z410 : W := mkw 0x0012820880000000 0x0004a08220000000 0x42308700e0000000 0x908c21c038000000

def z411 : W := mkw 0x0affffdbdd803501 0xc2bffff6f7600d40 0xebfffffff7003800 0xfafffffffdc00e00

def z412 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xebfffffff7380000 0xfafffffffdce0000

def z413 : W := mkw 0x04e800001eb68002 0x013a000007ada000 0x65f800001fffc003 0x197e000007fff000

def z414 : W := mkw 0x02e805a01dc01380 0xc0ba0168077004e0 0x63f807e01fc001c3 0x98fe01f807f00070

def z415 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0x0130000007000000 0x004c000001c00000

def z416 : W := mkw 0x0000204160010050 0x0000081058004014 0xfc49e8e3e00301f3 0xff127a38f800c07c

def z417 : W := mkw 0x80c53873786566dd 0x20314e1cde1959b7 0xfc49e8e3e8c7c7ff 0xff127a38fa31f1ff

def z418 : W := mkw 0xc5ffdb1ebfbfbd7b 0xb17ff6c7afefef5e 0xffffff1fffffffff 0xffffffc7ffffffff

def z419 : W := mkw 0x43fa9f8cbf9b3d73 0xd0fea7e32fe6cf5c 0xffb6971cf73b39f3 0xffeda5c73dcece7c

def z420 : W := mkw 0x43fa9fac9fda3fa3 0xd0fea7eb27f68fe8 0x73fe1ffc1ff83fc3 0xdcff87ff07fe0ff0

def z421 : W := mkw 0x41fa830cbf9b1972 0x907ea0c32fe6c65c 0xfffe971cfffb39f3 0xffffa5c73ffece7c

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0x3080100010003801 0x4c20040004000e00

def z423 : W := mkw 0x80c5181600082c29 0x2031460580020b0a 0xb8c7181f00003e3c 0x6e31c607c0000f8f

def z424 : W := mkw 0x04ffd8121eb68002 0x013ff60487ada000 0xedfff81f1fffc003 0x7b7ffe07c7fff000

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0xa841080300000000 0x6a104200c0000000

def z426 : W := mkw 0x4517c30ca33f9972 0x9145f0c328cfe65c 0xffb7f71cf73ff9f3 0xffedfdc73dcffe7c

def z427 : W := mkw 0x083fe6dbc0000000 0x020ff9b6f0000000 0xca3fe7ffe0000000 0xb28ff9fff8000000

def z428 : W := mkw 0x0012820880000000 0x0004a08220000000 0x02b6171c00000000 0x00ad85c700000000

def z429 : W := mkw 0x80c0181618082c29 0x2030060586020b0a 0x38c0181f18003e3d 0x4e300607c6000f8f

def z430 : W := mkw 0x06ffc5a01ff69382 0xc1bff16807fda4e0 0xe7ffe7e01fffc1c3 0xb9fff9f807fff070

def z431 : W := mkw 0x88fffedfc02c0828 0x223fffb7f00b020a 0xeeffffffe03c003c 0xfbbffffff80f000f

def z432 : W := mkw 0x0000000000000000 0x0000000000000000 0xa886101c00000000 0x6a21840700000000

def z433 : W := mkw 0x0012a061625342d6 0x0004a8185894d0b5 0xfdffe8e3ffffc7ff 0xff7ffa38fffff1ff

def z434 : W := mkw 0xc1d79b1e9b3e3d2b 0xb075e6c7a6cf8f4a 0x03b6171c17383800 0x00ed85c705ce0e00

def z435 : W := mkw 0x0a003ffbc1403781 0xc2800ffef0500de0 0x1a001fffe0003fc0 0xc68007fff8000ff0

def z436 : W := mkw 0x0000010401081920 0x8000004100420648 0xffb6171c173839f3 0xffed85c705ce0e7c

def z437 : W := mkw 0x82c51db6196c3fa9 0xe0b1476d865b0fea 0xbec71fff183c3ffd 0xefb1c7ffc60f0fff

def z438 : W := mkw 0x82001db601483fa9 0xe080076d80520fea 0x1a001fff00003ffc 0xc68007ffc0000fff

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc49e80308c7c63f 0x7f127a00c231f18f

def z440 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x4179e0000fc7c002 0x105e780003f1f000

def z441 : W := mkw 0x0000000000000000 0x0000000000000000 0xe400800000030003 0x390020000000c000

def z442 : W := mkw 0x06ffdda01ff6b783 0xc1bff76807fdade0 0x73fe1fe01ff83fc3 0xdcff87f807fe0ff0

def z443 : W := mkw 0x49ffffdfc31a1922 0x927ffff7f0c68648 0xebfffffff7383800 0xfafffffffdce0e00

def z444 : W := mkw 0x08e83edbc0000000 0x023a0fb6f0000000 0x6af81fffe0000000 0xdabe07fff8000000

def z445 : W := mkw 0x0000204140000000 0x0000081050000000 0x080008e3e0000000 0xc2000238f8000000

def z446 : W := mkw 0x4517c20ca23f8872 0x1145f083288fe21c 0x8c07e01ce03fc030 0x2301f807380ff00c

def z447 : W := mkw 0x00ffc00000000000 0x003ff00000000000 0x00b6000000000000 0x002d800000000000

def z448 : W := mkw 0x88fffefff86d6efd 0x223fffbffe1b5bbf 0xfefffffff8ffffff 0xffbffffffe3fffff

def z449 : W := mkw 0x8417c016023e882a 0x2105f005808fa20a 0x8c07e01f003fc03c 0x2301f807c00ff00f

def z450 : W := mkw 0x00c5385340000000 0x00314e14d0000000 0xe8cff8ffe0000000 0xfa33fe3ff8000000

def z451 : W := mkw 0x41128208a2130052 0x1044a0822884c014 0x00008000e0030000 0x000020003800c000

def z452 : W := mkw 0x80ffd816182c2c29 0x203ff605860b0b0a 0xfcfff81f183c3e3d 0x7f3ffe07c60f0f8f

def z453 : W := mkw 0x00000020204142d4 0x00000008081050b5 0xfc008000e8c7c7ff 0xff0020003a31f1ff

def z454 : W := mkw 0x00c53873604142d4 0x00314e1cd81050b5 0xfccff8ffe8c7c7ff 0xff33fe3ffa31f1ff

def z455 : W := mkw 0x04ed60615ce4c284 0x013b5818573930a1 0x004968e308c4c60c 0x00125a38c2313183

def z456 : W := mkw 0x0000204140000000 0x0000081050000000 0x004968e300000000 0x00125a38c0000000

def z457 : W := mkw 0x06ffc1201ff6b783 0xc1bff04807fdade0 0xf5ffe0001fffffc3 0x3d7ff80007fffff0

def z458 : W := mkw 0x0c17e25bc2368002 0x0305f896f08da000 0x8c07e01fe03fc000 0x2301f807f80ff000

def z459 : W := mkw 0x00d79a1a80000000 0x0035e686a0000000 0xeaf79f1fe0000000 0xfabde7c7f8000000

def z460 : W := mkw 0x040000001eb68002 0x0100000007ada000 0x0100000017380000 0x0040000005ce0000

def z461 : W := mkw 0x80c5181218242409 0x2031460486090902 0xbc4108030804063d 0x6f104200c201018f

def z462 : W := mkw 0x06ffdca01ef6a683 0x41bff72807bda9a0 0xe5ffe8e01fffc603 0x397ffa3807fff180

def z463 : W := mkw 0x08fffedfc0080820 0x023fffb7f0020208 0xfefffffff0383831 0xffbffffffc0e0e0c

def z464 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x184968e3e8c4c7fc 0xc6125a38fa3131ff

def z465 : W := mkw 0x493ae7c9e3131152 0x924eb9f278c4c454 0x4338e7e0e70301c2 0x90ce39f839c0c070

def z466 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x000000e0e00001c0 0x8000003838000070

def z467 : W := mkw 0x0012830881001100 0x8004a0c220400440 0xfbb6971cf70039c3 0xfeeda5c73dc00e70

def z468 : W := mkw 0x00ffd81200000000 0x003ff60480000000 0xe8fff81f00000000 0x7a3ffe07c0000000

def z469 : W := mkw 0x4112a36de35b5bf6 0x9044a8db78d6d6fd 0xffb69ffff73b3fff 0xffeda7fffdcecfff

def z470 : W := mkw 0x4bffffffffdb3ff3 0xd2fffffffff6cffc 0xfffffffffffb3ff3 0xfffffffffffecffc

def z471 : W := mkw 0x00128004021a0822 0x0004a00100868208 0xfdb6901c173b3833 0x7f6da40705cece0c

def z472 : W := mkw 0x84ffd8121eb6a40b 0x213ff60487ada902 0xe5ffe8031fffc60f 0x397ffa00c7fff183

def z473 : W := mkw 0x0817c21a80000000 0x0205f086a0000000 0x0006001c00000000 0x0001800700000000

def z474 : W := mkw 0x00c5000018240000 0x0031400006090000 0x0086000010380000 0x00218000040e0000

def z475 : W := mkw 0x49ffdf9ea31b1972 0x927ff7e7a8c6c65c 0xffb6971cf73b39f3 0xffeda5c73dcece7c

def z476 : W := mkw 0x4100030ca31b1972 0x904000c328c6c65c 0x1f00171cf73b39f3 0xc7c005c73dcece7c

def z477 : W := mkw 0x41000308a1011150 0x904000c228404454 0x02000700e00001c0 0x808001c038000070

def z478 : W := mkw 0x43e81facbdc93ff1 0xd0fa07eb2f724ffc 0x7bf81ffcffc03ff3 0xdefe07ff3ff00ffc

def z479 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x57308700f73b39f3 0x95cc21c03dcece7c

def z480 : W := mkw 0x8817e25fc02c0828 0x2205f897f00b020a 0x8c07e01fe03c003c 0x2301f807f80f000f

def z481 : W := mkw 0x083ac68880000000 0x020eb1a220000000 0x0230070000000000 0x008c01c000000000

def z482 : W := mkw 0x02e81da001403781 0xc0ba076800500de0 0x72f81fe000003fc0 0xdcbe07f800000ff0

def z483 : W := mkw 0x0000206560494af4 0x00000819581252bd 0xfccff8fff8ffffff 0xff33fe3ffe3fffff

def z484 : W := mkw 0x04ffc00002368002 0x013ff000008da000 0xe4ffe000003fc000 0x393ff800000ff000

def z485 : W := mkw 0x0000020880000000 0x0000008220000000 0x0a00171ce0000000 0xc28005c738000000

def z486 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x85b7e000173fc000 0x216df80005cff000

def z487 : W := mkw 0x08ffde9a80000000 0x023ff7a6a0000000 0xaaf71f1f00000000 0x6abdc7c7c0000000

def z488 : W := mkw 0x02001da01dc03781 0xc080076807700de0 0x13001fe01fc03fc3 0xc4c007f807f00ff0

def z489 : W := mkw 0x84ed58121ca4a409 0x213b560487292902 0x0049680308c4c60c 0x00125a00c2313183

def z490 : W := mkw 0x00c5181200000000 0x0031460480000000 0xbcc7181f0804063d 0x6f31c607c201018f

def z491 : W := mkw 0x41000104231b1972 0x9040004108c6c65c 0xfd008000f73b39f3 0xff4020003dcece7c

def z492 : W := mkw 0x4112830883121102 0x9044a0c220c48440 0x0330070007000000 0x00cc01c001c00000

def z493 : W := mkw 0x04ffe0617ef7c2d6 0x013ff8185fbdf0b5 0xe5ffe0e0ffffc1c3 0xb97ff8383ffff070

def z494 : W := mkw 0x4dffffdfffbf9972 0x937ffff7ffefe65c 0xfffffffffffff9f3 0xfffffffffffffe7c

def z495 : W := mkw 0x0000002000404284 0x00000008001010a1 0x0000000008c4c60c 0x0000000002313183

def z496 : W := mkw 0x45ffc308bfb79152 0x917ff0c22fede454 0xe7ffe700ffffc1c3 0xb9fff9c03ffff070

def z497 : W := mkw 0x08ed7cf340404284 0x023b5f3cd01010a1 0x004968e308c4c60c 0x00125a38c2313183

def z498 : W := mkw 0x4100020ca0090870 0x104000832802421c 0x0800001ce0000030 0x020000073800000c

def z499 : W := mkw 0x0000000018002401 0x0000000006000900 0x1000000018003e01 0x0400000006000f80

def z500 : W := mkw 0x00ffdc8000000000 0x003ff72000000000 0xe2ffffe000000000 0xf8bffff800000000

def z501 : W := mkw 0x00c0180000000000 0x0030060000000000 0x20c0180000000000 0x4830060000000000

def z502 : W := mkw 0x8000000400082c29 0x2000000100020b0a 0x1000000000003e3c 0x0400000000000f8f

def z503 : W := mkw 0x02e81d801d803501 0xc0ba076007600d40 0x33f01f001f003e01 0x4cfc07c007c00f80

def z504 : W := mkw 0x82ed1db61dec3fa9 0xe0bb476d877b0fea 0x73fe1ffc1ff83fc3 0xdcff87ff07fe0ff0

def z505 : W := mkw 0x82e81db61dc83fa9 0xe0ba076d87720fea 0x7bf81fff1fc03fff 0xdefe07ffc7f00fff

def z506 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x02ff7fff00000000 0x00bfdfffc0000000

def z507 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x9e06971ce03b39f0 0xe781a5c7380ece7c

def z508 : W := mkw 0x0cfffedbc2368002 0x033fffb6f08da000 0xeeffffffe03fc000 0xfbbffffff80ff000

def z509 : W := mkw 0x00c03861784166d5 0x00300e185e1059b5 0xfcc9f8e3f8c7ffff 0xff327e38fe31ffff

def z510 : W := mkw 0x4512830cbfbf9972 0x9144a0c32fefe65c 0xffb6971cfffff9f3 0xffeda5c73ffffe7c

def z511 : W := mkw 0x80000024386d6efd 0x200000090e1b5bbf 0x1400000018ffffff 0x05000000063fffff

def z512 : W := mkw 0x82ed1d961dac3d29 0xe0bb4765876b0f4a 0x03b6171c17383800 0x00ed85c705ce0e00

def z513 : W := mkw 0x84ffc0161ebe882a 0x213ff00587afa20a 0xedffe01f1fffc03f 0x3b7ff807c7fff00f

def z514 : W := mkw 0x08ffffdbc1001100 0x823ffff6f0400440 0xfbfffffff70039c3 0xfefffffffdc00e70

def z515 : W := mkw 0x0817e25bc0000000 0x0205f896f0000000 0xeab7f71fe0000000 0xfaadfdc7f8000000

def z516 : W := mkw 0x08ed7cd340000000 0x023b5f34d0000000 0x62f97fe300000000 0xd8be5ff8c0000000

def z517 : W := mkw 0x02e81da005c01380 0xc0ba0768017004e0 0x63f81fe007c001c2 0xd8fe07f801f00070

def z518 : W := mkw 0x8000387760496efd 0x20000e1dd8125bbf 0x180018ffe0003ffc 0xc600063ff8000fff

def z519 : W := mkw 0x84fff8777effeeff 0x213ffe1ddfbffbbf 0xfdfff8ffffffffff 0xff7ffe3fffffffff

def z520 : W := mkw 0x43129faca35b3ff3 0xd0c4a7eb28d6cffc 0xffb69ffcf73b3ff3 0xffeda7ff3dcecffc

def z521 : W := mkw 0x02001ca000402681 0x40800728001009a0 0x000008e000000600 0x0000023800000180

def z522 : W := mkw 0x08ed5c9200000000 0x023b572480000000 0x0000000000000000 0x0000000000000000

def z523 : W := mkw 0x0000010001001100 0x8000004000400440 0x12001700000039c0 0xc48005c000000e70

def z524 : W := mkw 0x08ffe6c9c0000000 0x023ff9b270000000 0xe2ffe7e0e0000000 0xb8bff9f838000000

def z525 : W := mkw 0x00c5180018242401 0x0031460006090900 0xb4c71800183c3e01 0x6d31c600060f0f80

def z526 : W := mkw 0x4112820ca21b0872 0x1044a0832886c21c 0xfc06801ce03b01f3 0xff01a007380ec07c

def z527 : W := mkw 0x0000000020010050 0x0000000008004014 0x18000000e00001f0 0xc60000003800007c

def z528 : W := mkw 0x08fffedbe0010050 0x023fffb6f8004014 0xfeffffffe00301f3 0xffbffffff800c07c

def z529 : W := mkw 0x04ffc0001ca48000 0x013ff00007292000 0xe0ffe00008c4c000 0x383ff80002313000

def z530 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xe849e8e3e0c3c1c2 0xfa127a38f830f070

def z531 : W := mkw 0x083afedbc0000000 0x020ebfb6f0000000 0x4a38ffffe0000000 0xd28e3ffff8000000

def z532 : W := mkw 0x41ffc30ca31b1972 0x907ff0c328c6c65c 0xfffff71cf73b39f3 0xfffffdc73dcece7c

def z533 : W := mkw 0x80c5181218242409 0x2031460486090902 0x0000000000000000 0x0000000000000000

def z534 : W := mkw 0x00ed1c9200000000 0x003b472480000000 0xeaff1fff00000000 0xfabfc7ffc0000000

def z535 : W := mkw 0x00c0180018002401 0x0030060006000900 0xbcc1180318043e3d 0x6f304600c6010f8f

def z536 : W := mkw 0x0afffffbc5c01380 0xc2bffffef17004e0 0xebffffffe7c001c2 0xfafffffff9f00070

def z537 : W := mkw 0x08fafec9c0000000 0x023ebfb270000000 0x62f8ffe0e0000000 0xd8be3ff838000000

def z538 : W := mkw 0x00c50004182c0820 0x00314001060b0208 0xbcc7101c183c3831 0x6f31c407060f0e0c

def z539 : W := mkw 0xc117821ea23f087a 0x3045e087a88fc21e 0x8c07801fe03f003c 0x2301e007f80fc00f

def z540 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x00c7181f183c3e0c 0x0031c607c60f0f83

def z541 : W := mkw 0x43fa9f8c9f9a3d23 0xd0fea7e327e68f48 0x03b6171c17383800 0x00ed85c705ce0e00

def z542 : W := mkw 0x4112a26de25b4af6 0x1044a89b7896d2bd 0xfc4fe8ffe8ffc7ff 0xff13fa3ffa3ff1ff

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x3040080008000601 0x4c10020002000180

def z544 : W := mkw 0x0000204160014054 0x0000081058005015 0xec49e8e3e007c03c 0xfb127a38f801f00f

def z545 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x4279efe3e0000000 0x909e7bf8f8000000

def z546 : W := mkw 0x00e81ca000400280 0x003a0728001000a0 0x72f81fe008c007c3 0xdcbe07f8023001f0

def z547 : W := mkw 0x0000000420090870 0x000000010802421c 0xfc86901cf03b39f3 0xff21a4073c0ece7c

def z548 : W := mkw 0x0000000000000000 0x0000000000000000 0xa486000010380001 0x29218000040e0000

def z549 : W := mkw 0x4917e35fe31b1972 0x9245f8d7f8c6c65c 0xffb7f71ff73b39f3 0xffedfdc7fdcece7c

def z550 : W := mkw 0x043ae06166d3c2d6 0x010eb81859b4f0b5 0xfd79e8e3efc7c7ff 0xff5e7a38fbf1f1ff

def z551 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x844fe00008ffc000 0x2113f800023ff000

def z552 : W := mkw 0x820001241dec3fa9 0xe0800049077b0fea 0x150000001ffc3fff 0x0540000007ff0fff

def z553 : W := mkw 0x41128308a3131152 0x9044a0c228c4c454 0xe7b68700f73b01c3 0xb9eda1c03dcec070

def z554 : W := mkw 0x0afffffbfdc177d5 0xc2bffffeff705df5 0xffffffffffc7ffff 0xfffffffffff1ffff

def z555 : W := mkw 0x04ffe0417eb7c056 0x013ff8105fadf015 0xedffe003ffffc03f 0x3b7ff800fffff00f

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0x140000000804063d 0x050000000201018f

def z557 : W := mkw 0x0800225bc0000000 0x02000896f0000000 0x0800001fe0000000 0x02000007f8000000

def z558 : W := mkw 0x0000181200000000 0x0000060480000000 0x0800181f00000000 0x42000607c0000000

def z559 : W := mkw 0x063ac5a007d29382 0xc18eb16801f4a4e0 0x4338e7e007c3c1c2 0x90ce39f801f0f070

def z560 : W := mkw 0x43fabfedffdb7ff7 0xd0feaffb7ff6dffd 0xffffffffffffffff 0xffffffffffffffff

def z561 : W := mkw 0x022804a004c00280 0x408a0128013000a0 0x000800e000c00000 0x0002003800300000

def z562 : W := mkw 0x45ffc30c9fbe9922 0x917ff0c327efa648 0xe7fff71c1ffff803 0x39fffdc707fffe00

def z563 : W := mkw 0x80052057602d487c 0x20014815d80b521f 0x8c07e01fe03fc03c 0x2301f807f80ff00f

def z564 : W := mkw 0x020021617dc177d5 0xc08008585f705df5 0xfd49e8e3ffc7ffff 0xff527a38fff1ffff

def z565 : W := mkw 0xc1c51b1eb92d3d79 0xb07146c7ae4b4f5e 0xbec71f1ff83c3ffd 0xefb1c7c7fe0f0fff

def z566 : W := mkw 0xc1001b1ea1093d79 0xb04006c7a8424f5e 0x1a001f1fe0003ffc 0xc68007c7f8000fff

def z567 : W := mkw 0x00c0000018000000 0x0030000006000000 0x20c0000018000001 0x0830000006000000

def z568 : W := mkw 0x80051816002c2c29 0x20014605800b0b0a 0x9c07181f003c3e3c 0x6701c607c00f0f8f

def z569 : W := mkw 0x41128308a3131152 0x9044a0c228c4c454 0x73b09700f70339c3 0xdcec25c03dc0ce70

def z570 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0xe579e0000fc7c003 0x395e780003f1f000

def z571 : W := mkw 0x0000206140400280 0x00000818501000a0 0xf849e8e3e8c007c3 0xfe127a38fa3001f0

def z572 : W := mkw 0x08fffedbe0014054 0x023fffb6f8005015 0xeeffffffe007c03c 0xfbbffffff801f00f

def z573 : W := mkw 0x00e81c8000000000 0x003a072000000000 0x02b0170000000000 0x00ac05c000000000

def z574 : W := mkw 0x4112820ca21b0872 0x1044a0832886c21c 0xedb6801cf73b0033 0x3b6da0073dcec00c

def z575 : W := mkw 0x060001201ff6b783 0xc180004807fdade0 0x150000001fffffc3 0x0540000007fffff0

def z576 : W := mkw 0x43e81da43fdb3ff3 0xd0fa07690ff6cffc 0x77f81fe01ffb3ff3 0xddfe07f807fecffc

def z577 : W := mkw 0x06ffdd801fb6b503 0xc1bff76007edad40 0xe7fff7001ffff803 0x39fffdc007fffe00

def z578 : W := mkw 0x80001816182c2c29 0x20000605860b0b0a 0x1c00181f183c3e3d 0x47000607c60f0f8f

def z579 : W := mkw 0x00e818001c802401 0x003a060007200900 0x71f818001fc03e03 0x5c7e060007f00f80

def z580 : W := mkw 0x00e81c8000000000 0x003a072000000000 0x004808e000000000 0x0012023800000000

def z581 : W := mkw 0x0000000400080820 0x0000000100020208 0x0086101c10383800 0x00218407040e0e00

def z582 : W := mkw 0x0000204160014054 0x0000081058005015 0xec49e003e8c7c03f 0x3b127800fa31f00f

def z583 : W := mkw 0x0000206140404284 0x00000818501010a1 0x704968e308c4c7cf 0xdc125a38c23131f3

def z584 : W := mkw 0x003ac00000000000 0x000eb00000000000 0x4038e00000000000 0x100e380000000000

def z585 : W := mkw 0x0000000018240000 0x0000000006090000 0x04000000183c0001 0x01000000060f0000

def z586 : W := mkw 0xc1d79b1e9b3e3d2b 0xb075e6c7a6cf8f4a 0xbff71f1f1f3c3e3d 0x6ffdc7c7c7cf0f8f

def z587 : W := mkw 0x040020617ef7c2d6 0x010008185fbdf0b5 0xfd49e8e3ffffc7ff 0xff527a38fffff1ff

def z588 : W := mkw 0x49ffffdfe1091970 0x927ffff7f842465c 0xfaffffffe00039f0 0xfebffffff8000e7c

def z589 : W := mkw 0x043ac0001eb68002 0x010eb00007ada000 0x4538e0001fffc003 0x114e380007fff000

def z590 : W := mkw 0x88ffde9e982c2c29 0x223ff7a7a60b0b0a 0x02b6171c10383800 0x00ad85c7040e0e00

def z591 : W := mkw 0x41000104031a1922 0x9040004100c68648 0x0100000017383800 0x0040000005ce0e00

def z592 : W := mkw 0x02e81da03dc177d5 0xc0ba07680f705df5 0x77f81fe01fc7ffff 0xddfe07f807f1ffff

def z593 : W := mkw 0x0000180000002401 0x0000060000000900 0x1000180000003e00 0x4400060000000f80

def z594 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x784808e3e8c007ff 0xde120238fa3001ff

def z595 : W := mkw 0x0ae83ffbddc03781 0xc2ba0ffef7700de0 0x7bf81fffffc03fc3 0xdefe07fffff00ff0

def z596 : W := mkw 0x022825e165c153d4 0xc08a0978597054f5 0x4338e7e0e7c3c1c2 0x90ce39f839f0f070

def z597 : W := mkw 0x04d7c0001a368002 0x0135f000068da000 0xa4c7e000183fc001 0x2931f800060ff000

def z598 : W := mkw 0x040000001ca48000 0x0100000007292000 0x0000000008c4c000 0x0000000002313000

def z599 : W := mkw 0x02e801201dc03781 0xc0ba004807700de0 0x71f800001fc03fc3 0x1c7e000007f00ff0

def z600 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x9c01e8e3e007c7fc 0xe7007a38f801f1ff

def z601 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x73780fe00fc007c3 0xdcde03f803f001f0

def z602 : W := mkw 0x0012820882120002 0x0004a08220848000 0xefb6971cf73b0003 0xfbeda5c73dcec000

def z603 : W := mkw 0x08ffe25bc0000000 0x023ff896f0000000 0xe8ffe01fe0000000 0x3a3ff807f8000000

def z604 : W := mkw 0x4100030ca1091970 0x904000c32842465c 0x7bb0171cf70039f3 0xdeec05c73dc00e7c

def z605 : W := mkw 0x41000004221b0872 0x104000010886c21c 0x04000000003b0030 0x01000000000ec00c

def z606 : W := mkw 0x840000041ebeac2b 0x2100000107afab0a 0x150000001ffffe3f 0x0540000007ffff8f

def z607 : W := mkw 0x04ed40001ca48000 0x013b500007292000 0xa4cf600018fcc001 0x2933d800063f3000

def z608 : W := mkw 0x0efffffbdff6b783 0xc3bffffef7fdade0 0xffffffffffffffc3 0xfffffffffffffff0

def z609 : W := mkw 0x8000001600080828 0x200000058002020a 0x0800001f0000003c 0x02000007c000000f

def z610 : W := mkw 0x0c3ae6c9c6928002 0x030eb9b271a4a000 0x4338e7e0e7c3c002 0x90ce39f839f0f000

def z611 : W := mkw 0x0afffffbc1403781 0xc2bffffef0500de0 0xfaffffffe0003fc0 0xfebffffff8000ff0

def z612 : W := mkw 0x0000002000400280 0x00000008001000a0 0x004808e008c00600 0x0012023802300180

def z613 : W := mkw 0x0000206140404284 0x00000818501010a1 0xbc4968e308c4c63d 0x6f125a38c231318f

def z614 : W := mkw 0x4112820c821a0822 0x1044a08320868208 0x0006001c00380000 0x00018007000e0000

def z615 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xa4c7101c183c3801 0x2931c407060f0e00

def z616 : W := mkw 0x08003efbe04142d4 0x02000fbef81050b5 0x1a001fffe00007fc 0xc68007fff80001ff

def z617 : W := mkw 0x00ffc0001c800000 0x003ff00007200000 0xe1ffe0001fc00003 0x387ff80007f00000

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0xa441000008040001 0x2910400002010000

def z619 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x05b600001fffc003 0x016d800007fff000

def z620 : W := mkw 0x41fa9f8ca31b1972 0x907ea7e328c6c65c 0xfffe9ffcf73b39f3 0xffffa7ff3dcece7c

def z621 : W := mkw 0x0412c00002128002 0x0104b0000084a000 0x0000e0000003c000 0x000038000000f000

def z622 : W := mkw 0x02e83ce17cc166d5 0x40ba0f385f3059b5 0xfc49e8e3e8c7c7ff 0xff127a38fa31f1ff

def z623 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x7048e8e0e8c3c7c3 0xdc123a383a30f1f0

def z624 : W := mkw 0x0228058005801100 0xc08a016001600440 0x0330070007000000 0x00cc01c001c00000

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008e00000c3c002 0x100238000030f000

def z626 : W := mkw 0x04ffc0203ef7c2d6 0x013ff0080fbdf0b5 0xf5ffe0001fffc7ff 0x3d7ff80007fff1ff

def z627 : W := mkw 0x0cfffcd35eb68002 0x033fff34d7ada000 0xe5ffe8e31fffc003 0x397ffa38c7fff000

def z628 : W := mkw 0x04ffc0201ef68282 0x013ff00807bda0a0 0xf5ffe8e01fffc7c3 0xfd7ffa3807fff1f0

def z629 : W := mkw 0x4112830ca1091970 0x9044a0c32842465c 0xfab6971ce00039f0 0xfeada5c738000e7c

def z630 : W := mkw 0x0428400004808000 0x010a100001202000 0x0008600000c0c000 0x0002180000303000

def z631 : W := mkw 0xc1129b1ea31b3d7b 0xb044a6c7a8c6cf5e 0xffb69f1ff73b3fff 0xffeda7c7fdcecfff

def z632 : W := mkw 0x08fffefbc0400280 0x023fffbef01000a0 0xfaffffffe8c007c3 0xfebffffffa3001f0

def z633 : W := mkw 0x00c5000000000000 0x0031400000000000 0xa0c7000000000000 0x2831c00000000000

def z634 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x5408e0e0e8c7c7ff 0x950238383a31f1ff

def z635 : W := mkw 0xc10001043b3f3d7b 0xb04000410ecfcf5e 0x150000001f3f3fff 0x0540000007cfcfff

def z636 : W := mkw 0x80c51916192c3d29 0xa0314645864b0f4a 0xfff71f1f1f3c3fff 0xfffdc7c7c7cf0fff

def z637 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x9c01e003e8c7c7ff 0x27007800fa31f1ff

def z638 : W := mkw 0x4112820ca21b0872 0x1044a0832886c21c 0xbc86901cf03b3831 0x6f21a4073c0ece0c

def z639 : W := mkw 0x02c01da019403781 0xc0b0076806500de0 0x32c01fe018003fc1 0xccb007f806000ff0

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x70000000000001c3 0xdc00000000000070

def z641 : W := mkw 0x0012800002120002 0x0004a00000848000 0x4130800007030002 0x104c200001c0c000

def z642 : W := mkw 0x82ed1d961dac3d29 0xe0bb4765876b0f4a 0xbff71f1f1f3c3e3d 0x6ffdc7c7c7cf0f8f

def z643 : W := mkw 0x45ffc30cbfbf9972 0x917ff0c32fefe65c 0xffb6971cf73b39f3 0xffeda5c73dcece7c

def z644 : W := mkw 0xc112830cbb3f3d7b 0xb044a0c32ecfcf5e 0xffb6971cff3f3fff 0xffeda5c73fcfcfff

def z645 : W := mkw 0x0005000000240000 0x0001400000090000 0x84070000003c0000 0x2101c000000f0000

def z646 : W := mkw 0x04fac0001e928002 0x013eb00007a4a000 0x61f8e0001fc3c003 0x187e380007f0f000

def z647 : W := mkw 0x80c53877786d6efd 0x20314e1dde1b5bbf 0xbcc718fff83c3ffd 0xef31c63ffe0f0fff

def z648 : W := mkw 0x0028048000000000 0x000a012000000000 0x423807e000000000 0x908e01f800000000

def z649 : W := mkw 0x80c5181218242409 0x2031460486090902 0xa4c70803183c060d 0x2931c200c60f0183

def z650 : W := mkw 0x4100010023131152 0x9040004008c4c454 0x01000000070301c2 0x0040000001c0c070

def z651 : W := mkw 0x80d79a1e982c2c29 0x2035e687a60b0b0a 0xfef79f1ff83c3e3d 0xffbde7c7fe0f0f8f

def z652 : W := mkw 0x80000004182c2c29 0x20000001060b0b0a 0xbc86101c183c3e3d 0x6f218407060f0f8f

def z653 : W := mkw 0x02e81d801d803501 0xc0ba076007600d40 0x63f817001fc03803 0x18fe05c007f00e00

def z654 : W := mkw 0xc1d79b1ebb3f3d7b 0xb075e6c7aecfcf5e 0xffb6971cf73b39f3 0xffeda5c73dcece7c

def z655 : W := mkw 0x0012800002120002 0x0004a00000848000 0x84068000003b0000 0x2101a000000ec000

def z656 : W := mkw 0x04ed40001ca48000 0x013b500007292000 0x0000000000000000 0x0000000000000000

def z657 : W := mkw 0x02e83de15dc07785 0xc0ba0f7857701de1 0x73f97fe31fc4ffcf 0xdcfe5ff8c7f13ff3

def z658 : W := mkw 0x4100030ca1091970 0x904000c32842465c 0xfe00971ce00339f3 0xff8025c73800ce7c

def z659 : W := mkw 0x02e83de17dc177d5 0xc0ba0f785f705df5 0x73f8ffe0ffc3ffc3 0xdcfe3ff83ff0fff0

def z660 : W := mkw 0x453ac30ca79b9972 0x914eb0c329e6e65c 0xffbef71cf7fbf9f3 0xffefbdc73dfefe7c

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000008c7c003 0x010000000231f000

def z662 : W := mkw 0x00ffe04140000000 0x003ff81050000000 0xe8ffe8e3e0000000 0xfa3ffa38f8000000

def z663 : W := mkw 0x80c01804182c2c29 0x20300601060b0b0a 0x34c01800183c3e3d 0x4d300600060f0f8f

def z664 : W := mkw 0x04ed40001ca48000 0x013b500007292000 0x61f960001fc4c003 0x187e580007f13000

def z665 : W := mkw 0x0000000400080820 0x0000000100020208 0x8c06001c00380030 0x23018007000e000c

def z666 : W := mkw 0x083ae6e9e04142d4 0x020eb9ba781050b5 0x4238e7e0e0c3c1c2 0x908e39f83830f070

def z667 : W := mkw 0x88fffedfd82c2c29 0x223fffb7f60b0b0a 0xeafffffff0383800 0xfabffffffc0e0e00

def z668 : W := mkw 0x80c53877586c6ead 0x20314e1dd61b1bab 0xbccf78ff18fcfe3d 0x6f33de3fc63f3f8f

def z669 : W := mkw 0x08fffefbe04142d4 0x023fffbef81050b5 0xeaffffffe0c3c1c2 0xfabffffff830f070

def z670 : W := mkw 0x4112830c831a1922 0x9044a0c320c68648 0xbfb6171c17383831 0x6fed85c705ce0e0c

def z671 : W := mkw 0x82e81da41dec3fa9 0xe0ba0769077b0fea 0x77f81fe01ffc3fff 0xddfe07f807ff0fff

def z672 : W := mkw 0x4112832ca35b1bf2 0x9044a0cb28d6c6fc 0xfffe9ffcfffb3ff3 0xffffa7ff3ffecffc

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc00000000000031 0x6f0000000000000c

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x62b0170000000000 0xd8ac05c000000000

def z675 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0xbc41181f08043e3d 0x6f104607c2010f8f

def z676 : W := mkw 0x0cffe25bdeb68002 0x033ff896f7ada000 0xedffe01fffffc003 0x3b7ff807fffff000

def z677 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x8c47081f083c063c 0x2311c207c20f018f

def z678 : W := mkw 0x45ffc1043fbf9972 0x917ff0410fefe65c 0xf5ffe0001ffff9f3 0x3d7ff80007fffe7c

def z679 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x8c87101f103c383c 0x2321c407c40f0e0f

def z680 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x61fe00001ff80003 0x187f800007fe0000

def z681 : W := mkw 0x08fffefbc0404284 0x023fffbef01010a1 0xeaffffffe8c4c60c 0xfabffffffa313183

def z682 : W := mkw 0x000000001c800000 0x0000000007200000 0x010000001fc00003 0x0040000007f00000

def z683 : W := mkw 0x02fa9da01fd23783 0xc0bea76807f48de0 0xf7fe9fe01ffb3fc3 0xfdffa7f807fecff0

def z684 : W := mkw 0x0000206140404284 0x00000818501010a1 0xe849e8e3e8c4c60c 0xfa127a38fa313183

def z685 : W := mkw 0x0012800022130052 0x0004a0000884c014 0xfdb68000f73b01f3 0xff6da0003dcec07c

def z686 : W := mkw 0x043ae06166d3c2d6 0x010eb81859b4f0b5 0x4138e0e0e7c3c1c2 0x904e383839f0f070

def z687 : W := mkw 0x4112a34de31b1972 0x9044a8d378c6c65c 0xfffffffff73b39f3 0xfffffffffdcece7c

def z688 : W := mkw 0x43001faca1493ff1 0xd0c007eb28524ffc 0x1a001ffce0003ff0 0xc68007ff38000ffc

def z689 : W := mkw 0x0000002000400280 0x00000008001000a0 0xfc4908e308c407ff 0xff124238c23101ff

def z690 : W := mkw 0x08ffde9a80000000 0x023ff7a6a0000000 0xeab6971ce0000000 0xfaada5c738000000

def z691 : W := mkw 0x041280001eb68002 0x0104a00007ada000 0xe5b680001fffc003 0x396da00007fff000

def z692 : W := mkw 0x0cffe6c9deb68002 0x033ff9b277ada000 0xe7ffe7e0ffffc003 0xb9fff9f83ffff000

def z693 : W := mkw 0x0028000004800000 0x000a000001200000 0x4138000007c00002 0x104e000001f00000

def z694 : W := mkw 0x00c5000018240000 0x0031400006090000 0x0041000008040000 0x0010400002010000

def z695 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xe449e0e0e8c7c1c3 0xb91278383a31f070

def z696 : W := mkw 0x80c53857582c2c29 0x20314e15d60b0b0a 0xfccff8fff83c3e3d 0xff33fe3ffe0f0f8f

def z697 : W := mkw 0x0012810003121102 0x8004a04000c48440 0xf7b69700173b39c3 0xfdeda5c005cece70

def z698 : W := mkw 0x80c5181218242409 0x2031460486090902 0xa8c7181f0804060c 0x6a31c607c2010183

def z699 : W := mkw 0x0000000400080820 0x0000000100020208 0x1800101c00003830 0x4600040700000e0c

def z700 : W := mkw 0x41000104231b1972 0x9040004108c6c65c 0x77b01700173b39f3 0xddec05c005cece7c

def z701 : W := mkw 0x0000002000400280 0x00000008001000a0 0x400800e000c001c2 0x9002003800300070

def z702 : W := mkw 0x00c5000018240000 0x0031400006090000 0xbcc70803183c063d 0x6f31c200c60f018f

def z703 : W := mkw 0x00c0180418082c21 0x0030060106020b08 0xbcc6181c18383e31 0x6f318607060e0f8c

def z704 : W := mkw 0x0000010021011150 0x8000004008404454 0xffb09700f70339f3 0xffec25c03dc0ce7c

def z705 : W := mkw 0x88ffde9e982c2c29 0x223ff7a7a60b0b0a 0xbef71f1f183c3e3d 0x6fbdc7c7c60f0f8f

def z706 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfc0088e3e00307ff 0xff002238f800c1ff

def z707 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffb69f1ff73b3fff 0xffeda7c7fdcecfff

def z708 : W := mkw 0x02e81da01dc07785 0xc0ba076807701de1 0x73f81fe01fc4ffcf 0xdcfe07f807f13ff3

def z709 : W := mkw 0x0cffde9a9eb68002 0x033ff7a6a7ada000 0xefffff1f1fffc003 0x7bffffc7c7fff000

def z710 : W := mkw 0x04ffd8121eb68002 0x013ff60487ada000 0xe5ffe8031fffc003 0x397ffa00c7fff000

def z711 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x43f81fe01fc03fc2 0x90fe07f807f00ff0

def z712 : W := mkw 0x04ffde889eb68002 0x013ff7a227ada000 0xeffffffcffffc003 0xfbffffff3ffff000

def z713 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xbc86181f10383e3d 0x6f218607c40e0f8f

def z714 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeabef7fce0000000 0xfaafbdff38000000

def z715 : W := mkw 0x80c53877786d6efd 0x20314e1dde1b5bbf 0x408ef0fcf0fbf9c2 0x9023bc3f3c3efe70

def z716 : W := mkw 0x02e81da001403781 0xc0ba076800500de0 0x73f81fe017003fc3 0xdcfe07f805c00ff0

def z717 : W := mkw 0x0817e6dbc0000000 0x0205f9b6f0000000 0x8a07e7ffe0000000 0xa281f9fff8000000

def z718 : W := mkw 0x04ffda1a9eb68002 0x013ff686a7ada000 0xefffff1fffffc003 0xfbffffc7fffff000

def z719 : W := mkw 0x0c17fedbc2368002 0x0305ffb6f08da000 0x8e07ffffe03fc000 0xe381fffff80ff000

def z720 : W := mkw 0x88fffedbc0002409 0x223fffb6f0000902 0xeaffffffe000060c 0xfabffffff8000183

def z721 : W := mkw 0x80051816002c2c29 0x20014605800b0b0a 0xbc87181f103c3e3d 0x6f21c607c40f0f8f

def z722 : W := mkw 0x843ad816069aac2b 0x210eb60581a6ab0a 0x5938f81f07c3fe3e 0x564e3e07c1f0ff8f

def z723 : W := mkw 0x80ed1816182c2c29 0x203b4605860b0b0a 0xfcff181f183c3e3d 0x7f3fc607c60f0f8f

def z724 : W := mkw 0x02001da01dc03781 0xc080076807700de0 0x73b01fe01fc03fc3 0xdcec07f807f00ff0

def z725 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73f8ffe01fc3ffc3 0xdcfe3ff807f0fff0

def z726 : W := mkw 0x020001201dc03781 0xc080004807700de0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z727 : W := mkw 0x040540001eb68002 0x0101500007ada000 0x050160001fffc003 0x0140580007fff000

def z728 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x9c49e8e3e8c7c7fc 0xe7127a38fa31f1ff

def z729 : W := mkw 0x47ffc1243fffbff3 0xd1fff0490fffeffc 0xf5ffe0001ffffff3 0x3d7ff80007fffffc

def z730 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x4579e0001fffc003 0x115e780007fff000

def z731 : W := mkw 0x883ae6cdd82c2c29 0x220eb9b3760b0b0a 0x5638e7e0f83c3e3d 0x958e39f83e0f0f8f

def z732 : W := mkw 0x08ed7edbc0000000 0x023b5fb6f0000000 0x0a001fffe0000000 0xc28007fff8000000

def z733 : W := mkw 0x0c003edbdeb68002 0x03000fb6f7ada000 0x0f001fffffffc003 0xc3c007fffffff000

def z734 : W := mkw 0x43fa9eacbedb2ef3 0x50fea7ab2fb6cbbc 0x8c4e88fce8fb0630 0x2313a23f3a3ec18c

def z735 : W := mkw 0x080026dbc0000000 0x020009b6f0000000 0x0a0007ffe0000000 0x828001fff8000000

def z736 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xfff9ffe31fc7ffff 0xfffe7ff8c7f1ffff

def z737 : W := mkw 0x49ed7dd7631b1972 0x927b5f75d8c6c65c 0x154968e3173b39f3 0x05525a38c5cece7c

def z738 : W := mkw 0x43003fede1497ff5 0xd0c00ffb78525ffd 0x1a001fffe0003ffc 0xc68007fff8000fff

def z739 : W := mkw 0x00ed3cd340000000 0x003b4f34d0000000 0xeaffffffe0000000 0xfabffffff8000000

def z740 : W := mkw 0x4112a36dc35a5ba6 0x9044a8db70d696e9 0x03ff7fff1ffcfe0c 0x00ffdfffc7ff3f83

def z741 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0xeaffffffe0000000 0xfabffffff8000000

def z742 : W := mkw 0x08c03edbc0000000 0x02300fb6f0000000 0x2ac01fffe0000000 0xcab007fff8000000

def z743 : W := mkw 0x08053edbc0000000 0x02014fb6f0000000 0x8a071fffe0000000 0xe281c7fff8000000

def z744 : W := mkw 0x45ed430cbdad9970 0x917b50c32f6b665c 0x1a49771ce8c4f9f0 0xc6925dc73a313e7c

def z745 : W := mkw 0x042840001eb68002 0x010a100007ada000 0x050860001fffc003 0x0142180007fff000

def z746 : W := mkw 0x80051816002c2c29 0x20014605800b0b0a 0xbc47181f083c3e3d 0x6f11c607c20f0f8f

def z747 : W := mkw 0x08fffedbc2120002 0x023fffb6f0848000 0xefffffffffffc003 0xfbfffffffffff000

def z748 : W := mkw 0x45ffc1243fffdbf6 0x917ff0490ffff6fd 0xf5ffe0001fffffff 0x3d7ff80007ffffff

def z749 : W := mkw 0x02281da005c03781 0xc08a076801700de0 0x73b81fe017c03fc3 0xdcee07f805f00ff0

def z750 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x9c87181f103c3e3c 0x6721c607c40f0f8f

def z751 : W := mkw 0x00c0192019403781 0x8030064806500de0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z752 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfef71f1f183c3e3d 0xffbdc7c7c60f0f8f

def z753 : W := mkw 0x04ed40001eb68002 0x013b500007ada000 0x65f960001fffc003 0x197e580007fff000

def z754 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x533817e007c039c2 0xd4ce05f801f00e70

def z755 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffb6971cff3f3fff 0xffeda5c73fcfcfff

def z756 : W := mkw 0x82e81db21dc03789 0xe0ba076c87700de2 0x73f81fe31fc03fcf 0xdcfe07f8c7f00ff3

def z757 : W := mkw 0x0012a249c0000000 0x0004a89270000000 0xeab69fffe0000000 0xfaada7fff8000000

def z758 : W := mkw 0x08fffedbd8242401 0x023fffb6f6090900 0xfefffffff83c3e01 0xffbffffffe0f0f80

def z759 : W := mkw 0x0cfffedbdeb6a403 0x033fffb6f7ada900 0xfffffffffffffe03 0xffffffffffffff80

def z760 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xf3f9ffe01fc03fc3 0xfcfe7ff807f00ff0

def z761 : W := mkw 0x08c53edbc0000000 0x02314fb6f0000000 0xeacfffffe0000000 0xfab3fffff8000000

def z762 : W := mkw 0x0a17e37bddc03781 0xc285f8def7700de0 0x9907e01fffc03fc3 0x2641f807fff00ff0

def z763 : W := mkw 0x06e85da01dc0b781 0xc1ba176807702de0 0x73f87fe01fc0ffc3 0xdcfe1ff807f03ff0

def z764 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xfbf91fe31fc03fc3 0xfefe47f8c7f00ff0

def z765 : W := mkw 0x022805a01dc03781 0xc08a016807700de0 0x73b817e01fc03fc3 0xdcee05f807f00ff0

def z766 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xf5ffe0001fffc1c3 0xfd7ff80007fff070

def z767 : W := mkw 0x02281da005c03781 0xc08a076801700de0 0x433817e007c039c2 0x90ce05f801f00e70

def z768 : W := mkw 0x08fffedbc0002401 0x023fffb6f0000900 0xfaffffffe0003e00 0xfebffffff8000f80

def z769 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x05ff60001fffc003 0x017fd80007fff000

def z770 : W := mkw 0x0000010001001100 0x8000004000400440 0x73f81fe0170039c3 0xdcfe07f805c00e70

def z771 : W := mkw 0x80ed5816182c2c29 0x203b5605860b0b0a 0xbccf781f183c3e3d 0x6f33de07c60f0f8f

def z772 : W := mkw 0xc1d79b1abb37355b 0xb075e6c6aecdcd56 0x43718f03ef0707ce 0x90dc63c0fbc1c1f3

def z773 : W := mkw 0xc10001243b7f7fff 0xb04000490edfdfff 0x150000001fffffff 0x0540000007ffffff

def z774 : W := mkw 0x0eed7cf35ce4a681 0x43bb5f3cd73929a0 0x004968e308c4c600 0x00125a38c2313180

def z775 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x9c49e8e3e8c7c7ff 0x27127a38fa31f1ff

def z776 : W := mkw 0x0812bedbc2120002 0x0204afb6f0848000 0xefb69ffff73b0003 0xfbeda7fffdcec000

def z777 : W := mkw 0x02e81da005c03781 0xc0ba076801700de0 0x73f81fe007c03fc2 0xdcfe07f801f00ff0

def z778 : W := mkw 0x0012a249c0000000 0x0004a89270000000 0xeabef7fce0000000 0xfaafbdff38000000

def z779 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x9c47181f083c3e3c 0x6711c607c20f0f8f

def z780 : W := mkw 0x86ed5db21de4b789 0xe1bb576c87792de2 0x73f97fe31fc4ffcf 0xdcfe5ff8c7f13ff3

def z781 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfccff8ffe8c7c7ff 0xff33fe3ffa31f1ff

def z782 : W := mkw 0x080026c9c0000000 0x020009b270000000 0x0a0017fce0000000 0xc28005ff38000000

def z783 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x53b81fe017c03fc2 0xd4ee07f805f00ff0

def z784 : W := mkw 0xc117a25fe23f487e 0x3045e897f88fd21f 0x8c07e01fe03fc03c 0x2301f807f80ff00f

def z785 : W := mkw 0x88fffedbd8242409 0x223fffb6f6090902 0xfeffffffe804063d 0xffbffffffa01018f

def z786 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x533807e017c039c3 0x94ce01f805f00e70

def z787 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfffe9ffcf73b39f3 0xffffa7ff3dcece7c

def z788 : W := mkw 0x0012a249c2120002 0x0004a89270848000 0xefffffffffffc003 0xfbfffffffffff000

def z789 : W := mkw 0x06ed5da01de4b781 0xc1bb576807792de0 0xf7ff7fe01ffcffc3 0xfdffdff807ff3ff0

def z790 : W := mkw 0x04ffd8121eb68002 0x013ff60487ada000 0xe5fff01c1fffc003 0x397ffc0707fff000

def z791 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x41ffe0001fffc002 0x107ff80007fff000

def z792 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfcc7181f183c3fff 0xff31c607c60f0fff

def z793 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x0aff7fffe0000000 0xc2bfdffff8000000

def z794 : W := mkw 0x84ffc0121eb6800a 0x213ff00487ada002 0xe5ffe0031fffc00f 0x397ff800c7fff003

def z795 : W := mkw 0x08c53edbd8240000 0x02314fb6f6090000 0xaec71ffff83c0001 0xebb1c7fffe0f0000

def z796 : W := mkw 0x04ffdc801eb68002 0x013ff72007ada000 0xe7fff7001fffc003 0x39fffdc007fff000

def z797 : W := mkw 0x08ffde9a80000000 0x023ff7a6a0000000 0xeafe9ffce0000000 0xfabfa7ff38000000

def z798 : W := mkw 0x0817fedbc0000000 0x0205ffb6f0000000 0xea4fffffe0000000 0xfa93fffff8000000

def z799 : W := mkw 0x083afedbc0000000 0x020ebfb6f0000000 0x4238f7fce0000000 0x908e3dff38000000

def z800 : W := mkw 0x80000004182c2c29 0x20000001060b0b0a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z801 : W := mkw 0x020005a001401380 0xc0800168005004e0 0x73b017e0170039c3 0xdcec05f805c00e70

def z802 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x5449e8e3e8c7c7ff 0x95127a38fa31f1ff

def z803 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x6afe1fffe0000000 0xdabf87fff8000000

def z804 : W := mkw 0x083fe6dbc0000000 0x020ff9b6f0000000 0xea7fefffe0000000 0xfa9ffbfff8000000

def z805 : W := mkw 0x00c5181600080820 0x0031460580020208 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z806 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0x9c06181f00383e3c 0x67018607c00e0f8f

def z807 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x18c7181f183c3e3c 0x4631c607c60f0f8f

def z808 : W := mkw 0x04ffe0617ef7c2d6 0x013ff8185fbdf0b5 0x19b608e3f73807fc 0xc66d8238fdce01ff

def z809 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xf5ffe0001fffc63f 0x3d7ff80007fff18f

def z810 : W := mkw 0x00002249c0000000 0x0000089270000000 0x0a001fffe0000000 0xc28007fff8000000

def z811 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x4a79ffffe0000000 0xd29e7ffff8000000

def z812 : W := mkw 0x8cfffedbdca4a409 0x233fffb6f7292902 0xeaffffffe8c4c60c 0xfabffffffa313183

def z813 : W := mkw 0x00129e8880000000 0x0004a7a220000000 0xeab69ffce0000000 0xfaada7ff38000000

def z814 : W := mkw 0x04ffc4801eb68002 0x013ff12007ada000 0xe7ffe7e01fffc003 0xb9fff9f807fff000

def z815 : W := mkw 0x0812fedbc0000000 0x0204bfb6f0000000 0x0a00ffffe0000000 0xc2803ffff8000000

def z816 : W := mkw 0x0012820880000000 0x0004a08220000000 0xeafe9ffce0000000 0xfabfa7ff38000000

def z817 : W := mkw 0x06ed5da01de4b781 0xc1bb576807792de0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z818 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xeeffffffe8ffc000 0xfbbffffffa3ff000

def z819 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x8cc7181f183c3e3c 0x2331c607c60f0f8f

def z820 : W := mkw 0x820001243ded7ffd 0xe08000490f7b5fff 0x150000001fffffff 0x0540000007ffffff

def z821 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xebfffffffff80003 0xfafffffffffe0000

def z822 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x4abeffffe0000000 0xd2afbffff8000000

def z823 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0xbe411fffe804063d 0xef9047fffa01018f

def z824 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfccf18ff183c3e3d 0xff33c63fc60f0f8f

def z825 : W := mkw 0x02e805a01dc03781 0xc0ba016807700de0 0x73f807e01fc03fc3 0x9cfe01f807f00ff0

def z826 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x43b817e017c039c2 0x90ee05f805f00e70

def z827 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x6ab01fffe0000000 0xdaac07fff8000000

def z828 : W := mkw 0x00002249c0000000 0x0000089270000000 0xea49ffffe0000000 0xfa927ffff8000000

def z829 : W := mkw 0x04ffc00006928002 0x013ff00001a4a000 0xe5ffe00017fbc003 0x397ff80005fef000

def z830 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x77f81fe01fc43fff 0xddfe07f807f10fff

def z831 : W := mkw 0x0812bedbc0000000 0x0204afb6f0000000 0x0ab61fffe0000000 0xc2ad87fff8000000

def z832 : W := mkw 0x02e83dc17d817555 0xc0ba0f705f605d55 0x8fb1f703f707f83c 0x23ec7dc0fdc1fe0f

def z833 : W := mkw 0x80c518161cac2c29 0x20314605872b0b0a 0xbdc7181f1ffc3e3f 0x6f71c607c7ff0f8f

def z834 : W := mkw 0x88fffedbd8242409 0x223fffb6f6090902 0xeaffffffe0000000 0xfabffffff8000000

def z835 : W := mkw 0x043ac0001eb68002 0x010eb00007ada000 0xe579e0001fffc003 0x395e780007fff000

def z836 : W := mkw 0x08fafec9c0000000 0x023ebfb270000000 0xeafefffce0000000 0xfabfbfff38000000

def z837 : W := mkw 0x84ffc0001eb6a40b 0x213ff00007ada902 0xe5ffe0001fffc60f 0x397ff80007fff183

def z838 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfafffffff0003801 0xfebffffffc000e00

def z839 : W := mkw 0x0012830883121102 0x8004a0c220c48440 0xffb6971cf73b39c3 0xffeda5c73dcece70

def z840 : W := mkw 0x0cfffedbc2368002 0x033fffb6f08da000 0xeeffffffe8ffc003 0xfbbffffffa3ff000

def z841 : W := mkw 0x08fffedbd8240000 0x023fffb6f6090000 0xeafffffff0380000 0xfabffffffc0e0000

def z842 : W := mkw 0x0417c00006b68002 0x0105f00001ada000 0x8507e00007ffc002 0x2141f80001fff000

def z843 : W := mkw 0x0812bedbc0000000 0x0204afb6f0000000 0x4a309fffe0000000 0xd28c27fff8000000

def z844 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xebfffffff7fbc002 0xfafffffffdfef000

def z845 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xbcc7181f18fffe3f 0x6f31c607c63fff8f

def z846 : W := mkw 0x04ffc2089eb68002 0x013ff08227ada000 0xe7fff71c1fffc003 0x39fffdc707fff000

def z847 : W := mkw 0x040000001eb68002 0x0100000007ada000 0x4508e0001fffc003 0x1142380007fff000

def z848 : W := mkw 0x80050016002c0828 0x20014005800b020a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z849 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffb6971cfffff9f3 0xffeda5c73ffffe7c

def z850 : W := mkw 0x84ffd8121eb6a40b 0x213ff60487ada902 0xedfff81f1fffc60f 0x7b7ffe07c7fff183

def z851 : W := mkw 0x003a868880000000 0x000ea1a220000000 0xeabe97fce0000000 0xfaafa5ff38000000

def z852 : W := mkw 0x80ed1c961cac2c29 0x203b4725872b0b0a 0xffff1fff1ffc3e3f 0xffffc7ffc7ff0f8f

def z853 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xefffffffff3c0001 0xfbffffffffcf0000

def z854 : W := mkw 0x08fffedbc2120002 0x023fffb6f0848000 0xeeffffffe03b0000 0xfbbffffff80ec000

def z855 : W := mkw 0x04d7c0001eb68002 0x0135f00007ada000 0xa5c7e0001fffc003 0x2971f80007fff000

def z856 : W := mkw 0x430001243fdb7ff7 0xd0c000490ff6dffd 0x150000001fffffff 0x0540000007ffffff

def z857 : W := mkw 0x08ffdebaa04142d4 0x023ff7aea81050b5 0x16b6171c08c7c7ff 0x05ad85c70231f1ff

def z858 : W := mkw 0x4912a25fe21b0872 0x1244a897f886c21c 0x8c06801fe03b0030 0x2301a007f80ec00c

def z859 : W := mkw 0x04ffc00006b68002 0x013ff00001ada000 0xe5ffe00007ffc002 0x397ff80001fff000

def z860 : W := mkw 0x04ffdc801eb68002 0x013ff72007ada000 0xe5ffe8e01fffc003 0x397ffa3807fff000

def z861 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfaffffffe8000601 0xfebffffffa000180

def z862 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeaffffffe8c4c000 0xfabffffffa313000

def z863 : W := mkw 0x0617dda00376b783 0xc185f76800ddade0 0x9607ffe0003fffc0 0xe581fff8000ffff0

def z864 : W := mkw 0x08e83edbdc800000 0x023a0fb6f7200000 0x6bf81fffffc00003 0xdafe07fffff00000

def z865 : W := mkw 0x82ed1db21de43789 0xe0bb476c87790de2 0xfff91fe31fc43fff 0xfffe47f8c7f10fff

def z866 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xffffffffffffc63f 0xfffffffffffff18f

def z867 : W := mkw 0x822d05b605ec1ba8 0xe08b416d817b06ea 0xcf3f07ff07fc01fe 0xb3cfc1ffc1ff007f

def z868 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xb8c7181f10383e3c 0x6e31c607c40e0f8f

def z869 : W := mkw 0x84ed58161cacac29 0x213b5605872b2b0a 0xfdff781f1ffcfe3f 0x7f7fde07c7ff3f8f

def z870 : W := mkw 0x80c51c96182c2c29 0x20314725860b0b0a 0xbec71fff183c3e3d 0xefb1c7ffc60f0f8f

def z871 : W := mkw 0x08fffedbdc800000 0x023fffb6f7200000 0xefffffffffc7c003 0xfbfffffffff1f000

def z872 : W := mkw 0x0cfffedbda368002 0x033fffb6f68da000 0xeefffffff83fc001 0xfbbffffffe0ff000

def z873 : W := mkw 0x4112830ca31b5976 0x9044a0c328c6d65d 0xffb6971cf73ff9ff 0xffeda5c73dcffe7f

def z874 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe5bee00017fbc003 0x396fb80005fef000

def z875 : W := mkw 0x08e83edbc0000000 0x023a0fb6f0000000 0x0a481fffe0000000 0xc29207fff8000000

def z876 : W := mkw 0x88fffedbd8242409 0x223fffb6f6090902 0xfafffffff8043e0d 0xfebffffffe010f83

def z877 : W := mkw 0x453ae369e7d3d3d6 0x914eb8da79f4f4f5 0x4338e7e0e7c3c1c2 0x90ce39f839f0f070

def z878 : W := mkw 0x41000124235b1bf2 0x9040004908d6c6fc 0x150000001ffb3ff3 0x0540000007fecffc

def z879 : W := mkw 0x0cfffedbc2128002 0x033fffb6f084a000 0xeaffffffe003c000 0xfabffffff800f000

def z880 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x020017fce0000000 0x808005ff38000000

def z881 : W := mkw 0x02ed1db21de43781 0xc0bb476c87790de0 0xffff1fff1ffc3fc3 0xffffc7ffc7ff0ff0

def z882 : W := mkw 0x08fffedbdc802401 0x023fffb6f7200900 0xfbffffffffc03e03 0xfefffffffff00f80

def z883 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xcfb6971cf73b39f2 0xb3eda5c73dcece7c

def z884 : W := mkw 0x02ed1da01de43781 0xc0bb476807790de0 0x73f91fe01fc43fc3 0xdcfe47f807f10ff0

def z885 : W := mkw 0x04ffc0121eb68002 0x013ff00487ada000 0xedffe01f1fffc003 0x3b7ff807c7fff000

def z886 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xf5ffe8001fffc603 0x7d7ffa0007fff180

def z887 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x7bb6171cf73839f3 0xdeed85c73dce0e7c

def z888 : W := mkw 0x08c53edbc0000000 0x02314fb6f0000000 0x0a411fffe0000000 0xc29047fff8000000

def z889 : W := mkw 0x022805a01dc03781 0xc08a016807700de0 0x73780fe01fc03fc3 0xdcde03f807f00ff0

def z890 : W := mkw 0x84c55816182cac29 0x21315605860b2b0a 0xbcc7781f183cfe3d 0x6f31de07c60f3f8f

def z891 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0xc53ee00007fbc002 0x314fb80001fef000

def z892 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xaaf71fffe0000000 0xeabdc7fff8000000

def z893 : W := mkw 0x08c53edbc0000000 0x02314fb6f0000000 0x0a861fffe0000000 0xc2a187fff8000000

def z894 : W := mkw 0x0cfffedbc6928002 0x033fffb6f1a4a000 0xeffffffff7fbc003 0xfbfffffffdfef000

def z895 : W := mkw 0x08fffedbd8002401 0x023fffb6f6000900 0xeafffffff0003800 0xfabffffffc000e00

def z896 : W := mkw 0x80c50016182c2c29 0x20314005860b0b0a 0xbcc7001f183c3e3d 0x2f31c007c60f0f8f

def z897 : W := mkw 0x02ed1db21dc03781 0xc0bb476c87700de0 0x73f91fe31fc03fc3 0xdcfe47f8c7f00ff0

def z898 : W := mkw 0x083ae6dbc0000000 0x020eb9b6f0000000 0x4a38e7ffe0000000 0x928e39fff8000000

def z899 : W := mkw 0x02ed1da01de43781 0xc0bb476807790de0 0x73fe1fe01ff83fc3 0xdcff87f807fe0ff0

def z900 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfef9ffe3e8c7c7ff 0xffbe7ff8fa31f1ff

def z901 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x8ab7ffffe0000000 0xe2adfffff8000000

def z902 : W := mkw 0x08fabedbc0000000 0x023eafb6f0000000 0xeafe9fffe0000000 0xfabfa7fff8000000

def z903 : W := mkw 0x04ffd8001eb68002 0x013ff60007ada000 0xe5fff8001fffc003 0x797ffe0007fff000

def z904 : W := mkw 0x02e81da005c01380 0xc0ba0768017004e0 0x73f81fe017c039c3 0xdcfe07f805f00e70

def z905 : W := mkw 0x493ae7e9e35353d6 0x924eb9fa78d4d4f5 0x4338e7e0e7c3c1c2 0x90ce39f839f0f070

def z906 : W := mkw 0x04fac0001e928002 0x013eb00007a4a000 0xe5fee0001ffbc003 0x397fb80007fef000

def z907 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeeffffffe004003c 0xfbbffffff801000f

def z908 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xcc49e8e3e8c7c7fe 0xb3127a38fa31f1ff

def z909 : W := mkw 0x88c53edbd8242409 0x22314fb6f6090902 0x0a411fffe804060c 0xc29047fffa010183

def z910 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x38c6181f18383e3d 0x4e318607c60e0f8f

def z911 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeab69fffe0000000 0xfaada7fff8000000

def z912 : W := mkw 0x02ed1da01de43781 0xc0bb476807790de0 0xffff1fe31ffc3fff 0xffffc7f8c7ff0fff

def z913 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfcc7981ff83c3e3d 0xff31e607fe0f0f8f

def z914 : W := mkw 0x043ac0001eb68002 0x010eb00007ada000 0x4138e00017fbc002 0x104e380005fef000

def z915 : W := mkw 0x00d7ba5bc0000000 0x0035ee96f0000000 0xeaffffffe0000000 0xfabffffff8000000

def z916 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfeffffffe8c7c63f 0xffbffffffa31f18f

def z917 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xedffe0031fffc03f 0x3b7ff800c7fff00f

def z918 : W := mkw 0x80c51816002c2c29 0x20314605800b0b0a 0xbcc7181f003c3e3c 0x6f31c607c00f0f8f

def z919 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe5ffe8e01fffc003 0xf97ffa3807fff000

def z920 : W := mkw 0x00fa80001e920002 0x003ea00007a48000 0xe5ffe0001fffc003 0x397ff80007fff000

def z921 : W := mkw 0x02e805a01dc01380 0xc0ba0168077004e0 0x73f817e01fc039c3 0xdcfe05f807f00e70

def z922 : W := mkw 0x4100012421495bf4 0x90400049085256fd 0x1400000008c7ffff 0x050000000231ffff

def z923 : W := mkw 0x08d7bedbc0000000 0x0235efb6f0000000 0xeaf79fffe0000000 0xfabde7fff8000000

def z924 : W := mkw 0x0cffe6c9deb68002 0x033ff9b277ada000 0xeffff7fcffffc003 0xfbfffdff3ffff000

def z925 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfcc9f8e3f8c7ffff 0xff327e38fe31ffff

def z926 : W := mkw 0x82003df761497ffd 0xe0800f7dd8525fff 0x1a001fffe0003ffc 0xc68007fff8000fff

def z927 : W := mkw 0x0817fedbc0000000 0x0205ffb6f0000000 0x0a061fffe0000000 0xc28187fff8000000

def z928 : W := mkw 0x08fffedbd8002401 0x023fffb6f6000900 0xeaffffffe8000600 0xfabffffffa000180

def z929 : W := mkw 0x02e81db21dc03781 0xc0ba076c87700de0 0x7bf81fff1fc03fc3 0xdefe07ffc7f00ff0

def z930 : W := mkw 0x08ffe6c9c0000000 0x023ff9b270000000 0xeafff7fce0000000 0xfabffdff38000000

def z931 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffb7971ff73f39ff 0xffede5c7fdcfce7f

def z932 : W := mkw 0x80ed1c96182c2c29 0x203b4725860b0b0a 0xbef71f1f183c3e3d 0x6fbdc7c7c60f0f8f

def z933 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x63f817e01fc039c3 0x98fe05f807f00e70

def z934 : W := mkw 0x82ed1db21de43789 0xe0bb476c87790de2 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z935 : W := mkw 0x08ed7edbc0000000 0x023b5fb6f0000000 0x6af97fffe0000000 0xdabe5ffff8000000

def z936 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xedfff01c1fffc003 0x7b7ffc0707fff000

def z937 : W := mkw 0x0afffedbdc802401 0x42bfffb6f7200900 0xeaffffffe0000000 0xfabffffff8000000

def z938 : W := mkw 0x02e81da01de43781 0xc0ba076807790de0 0x77f81fe01ffc3fc3 0xddfe07f807ff0ff0

def z939 : W := mkw 0x06e81da01de4b781 0xc1ba076807792de0 0x73f81fe01fc4ffc3 0xdcfe07f807f13ff0

def z940 : W := mkw 0x41000124235b5bf6 0x9040004908d6d6fd 0x1500000017fbf9f3 0x0540000005fefe7c

def z941 : W := mkw 0x43fa81243fdb3ff3 0xd0fea0490ff6cffc 0xf5fe80001ffb3ff3 0x3d7fa00007fecffc

def z942 : W := mkw 0x041280001eb68002 0x0104a00007ada000 0xe5ffe0001fffc003 0x397ff80007fff000

def z943 : W := mkw 0x08c03edbd8002401 0x02300fb6f6000900 0x3ac01ffff8003e01 0xceb007fffe000f80

def z944 : W := mkw 0x4912e24de21b0872 0x1244b8937886c21c 0x8c06e01ce03b0030 0x2301b807380ec00c

def z945 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73f81fe017003fc0 0xdcfe07f805c00ff0

def z946 : W := mkw 0x80ed18161cac2c29 0x203b4605872b0b0a 0xbdf7181f1f3c3e3d 0x6f7dc607c7cf0f8f

def z947 : W := mkw 0x0cfffedbdca48000 0x033fffb6f7292000 0xeeffffffe8c7c003 0xfbbffffffa31f000

def z948 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x13f81fe01fc03fc3 0x04fe07f807f00ff0

def z949 : W := mkw 0x8cfffedbdeb6a40b 0x233fffb6f7ada902 0xefffffffffffc60f 0xfbfffffffffff183

def z950 : W := mkw 0x00001d8001001100 0x8000076000400440 0x73b01fe0170039c3 0xdcec07f805c00e70

def z951 : W := mkw 0x043fc00006b68002 0x010ff00001ada000 0xe5bfe00017ffc003 0x396ff80005fff000

def z952 : W := mkw 0x0812a6c9c0000000 0x0204a9b270000000 0xeab697fce0000000 0xfaada5ff38000000

def z953 : W := mkw 0x00e801201dc01380 0x803a0048077004e0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z954 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x45bee0001fffc003 0x116fb80007fff000

def z955 : W := mkw 0x0cfffedbdca48000 0x033fffb6f7292000 0xeefffffff8fcc001 0xfbbffffffe3f3000

def z956 : W := mkw 0x450001243fffdbf6 0x914000490ffff6fd 0x150000001fffffff 0x0540000007ffffff

def z957 : W := mkw 0xc1003b7fe1497ffd 0xb0400edff8525fff 0x1a001fffe0003ffc 0xc68007fff8000fff

def z958 : W := mkw 0x04ffc0001eb6a403 0x013ff00007ada900 0xf5ffe0001ffffe03 0x3d7ff80007ffff80

def z959 : W := mkw 0x08fffedbd8240000 0x023fffb6f6090000 0xeaffffffe8040000 0xfabffffffa010000

def z960 : W := mkw 0x0417c0001eb68002 0x0105f00007ada000 0xe54fe0001fffc003 0x3953f80007fff000

def z961 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xebffffffefc7c002 0xfafffffffbf1f000

def z962 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0x1886181f10383e3c 0x46218607c40e0f8f

def z963 : W := mkw 0x80050016002c2c29 0x20014005800b0b0a 0x9c07001f003c3e3c 0x2701c007c00f0f8f

def z964 : W := mkw 0x08fffedbc0240000 0x023fffb6f0090000 0xeeffffffe03c0000 0xfbbffffff80f0000

def z965 : W := mkw 0x80050016182c2c29 0x20014005860b0b0a 0xbc87101f183c3e3d 0x6f21c407c60f0f8f

def z966 : W := mkw 0x0cfffedbc6b68002 0x033fffb6f1ada000 0xefffffffe7ffc002 0xfbfffffff9fff000

def z967 : W := mkw 0x00ff9e9a80000000 0x003fe7a6a0000000 0xeaff9fffe0000000 0xfabfe7fff8000000

def z968 : W := mkw 0x04ffd8001eb6a403 0x013ff60007ada900 0xe5fff0001ffff803 0x397ffc0007fffe00

def z969 : W := mkw 0x0000000400080820 0x0000000100020208 0xbc86181f10383e3d 0x6f218607c40e0f8f

def z970 : W := mkw 0x88ed5c96182c2c29 0x223b5725860b0b0a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z971 : W := mkw 0x04ffc2089eb68002 0x013ff08227ada000 0xedffe01cffffc003 0x3b7ff8073ffff000

def z972 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x03b017e0170039c0 0x80ec05f805c00e70

def z973 : W := mkw 0x0000010421091970 0x800000410842465c 0xffb6971cf73b39f3 0xffeda5c73dcece7c

def z974 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0x0bb61ffff7380000 0xc2ed87fffdce0000

def z975 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x62fefffce0000000 0xd8bfbfff38000000

def z976 : W := mkw 0x0cffe6dbdeb68002 0x033ff9b6f7ada000 0xefffe7ffffffc003 0xbbfff9fffffff000

def z977 : W := mkw 0x02ed1da01dc03781 0xc0bb476807700de0 0xf3ff1fe01fc03fc3 0xfcffc7f807f00ff0

def z978 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x77f81fe01fc7ffc3 0xddfe07f807f1fff0

def z979 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xbfb6171cf73839f1 0xefed85c73dce0e7c

def z980 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeeffffffe0030003 0xfbbffffff800c000

def z981 : W := mkw 0x84ed58161cacac29 0x213b5605872b2b0a 0xfccff81f18fffe3f 0x7f33fe07c63fff8f

def z982 : W := mkw 0x08fffedbd8000000 0x023fffb6f6000000 0xeafffffff8000001 0xfabffffffe000000

def z983 : W := mkw 0x80ed1c96182c2c29 0x203b4725860b0b0a 0xbccf18ff183c3e3d 0x6f33c63fc60f0f8f

def z984 : W := mkw 0x80ed18161cac2c29 0x203b4605872b0b0a 0xfdfff81f1ffffe3f 0x7f7ffe07c7ffff8f

def z985 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0xe5ffe0001fffc003 0x397ff80007fff000

def z986 : W := mkw 0x4300012427db1bf2 0xd0c0004909f6c6fc 0x1500000017fb39f3 0x0540000005fece7c

def z987 : W := mkw 0x0cfffedbde928002 0x033fffb6f7a4a000 0xebffffffffc3c003 0xfafffffffff0f000

def z988 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73b817e017c039c3 0xdcee05f805f00e70

def z989 : W := mkw 0x88fffedbc0240008 0x223fffb6f0090002 0xeaffffffe004000c 0xfabffffff8010003

def z990 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xcabff7ffe0000000 0xb2affdfff8000000

def z991 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe7fff7001fffc003 0xf9fffdc007fff000

def z992 : W := mkw 0x08fffedbda360002 0x023fffb6f68d8000 0xefffffffff3f0003 0xfbffffffffcfc000

def z993 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfccf181f18fc3e3f 0x7f33c607c63f0f8f

def z994 : W := mkw 0x0cfffedbc6928002 0x033fffb6f1a4a000 0xebffffffe7000000 0xfafffffff9c00000

def z995 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x14c7181f183c3e3d 0x0531c607c60f0f8f

def z996 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xedffe8031fffc003 0x7b7ffa00c7fff000

def z997 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfccfe8e3f8ffc7ff 0xff33fa38fe3ff1ff

def z998 : W := mkw 0x040000001eb68002 0x0100000007ada000 0x8501e0001fffc003 0x2140780007fff000

def z999 : W := mkw 0x0cfffedbc0248000 0x033fffb6f0092000 0xeaffffffe004c000 0xfabffffff8013000

def z1000 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xbccf781f18fcfe3d 0x6f33de07c63f3f8f

def z1001 : W := mkw 0x08fffedbc2120002 0x023fffb6f0848000 0xebffffffe7030002 0xfafffffff9c0c000

def z1002 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x03b6171cf73839c0 0x80ed85c73dce0e70

def z1003 : W := mkw 0x80c0181618082c29 0x2030060586020b0a 0xbcc6181f18383e3d 0x6f318607c60e0f8f

def z1004 : W := mkw 0x0000012001401380 0x80000048005004e0 0x73b01fe017003fc3 0xdcec07f805c00ff0

def z1005 : W := mkw 0x02001da001403781 0xc080076800500de0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z1006 : W := mkw 0x4100012421495bf4 0x90400049085256fd 0x1000000000003ffc 0x0400000000000fff

def z1007 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xeffffffff73fc000 0xfbfffffffdcff000

def z1008 : W := mkw 0x06ffdc801eb6a403 0x41bff72007ada900 0xe5ffe0001fffc003 0x397ff80007fff000

def z1009 : W := mkw 0x8000181600082c29 0x2000060580020b0a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z1010 : W := mkw 0x04ffe249deb68002 0x013ff89277ada000 0xefffffffffffc003 0xfbfffffffffff000

def z1011 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xbcc7f81f183ffe3d 0x6f31fe07c60fff8f

def z1012 : W := mkw 0x00ffc00002120002 0x003ff00000848000 0xe5ffe0001fffc003 0x397ff80007fff000

def z1013 : W := mkw 0xc917e25fe23f087a 0x3245f897f88fc21e 0x8c07e01fe03f003c 0x2301f807f80fc00f

def z1014 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x61fee0001ffbc003 0x187fb80007fef000

def z1015 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xf7f91fe01fc43fc3 0xfdfe47f807f10ff0

def z1016 : W := mkw 0x00e81d8019003501 0x803a076006400d40 0x73f81fe01f003fc3 0xdcfe07f807c00ff0

def z1017 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xfbf89fe0ffc03fc3 0xfefe27f83ff00ff0

def z1018 : W := mkw 0x04ffd8121eb68002 0x013ff60487ada000 0xfdfff81f1fffc63f 0x7f7ffe07c7fff18f

def z1019 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xe7fff7fcffffc003 0xb9fffdff3ffff000

def z1020 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xfbfe1ffc1fc03fc3 0xfeff87ff07f00ff0

def z1021 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfffff71cf73b39f3 0xfffffdc73dcece7c

def z1022 : W := mkw 0x4100236de1495bf4 0x904008db785256fd 0x1a0017fce00039f0 0xc68005ff38000e7c

def z1023 : W := mkw 0x04ffdc921eb68002 0x013ff72487ada000 0xefffffff1fffc003 0xfbffffffc7fff000

def z1024 : W := mkw 0x04e800001eb68002 0x013a000007ada000 0xe5f9e0001fffc003 0x397e780007fff000

def z1025 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xe2fff7fce0000000 0xb8bffdff38000000

def z1026 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfdf7181f1f3c3e3f 0x7f7dc607c7cf0f8f

def z1027 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0x4538e00017fbc003 0x114e380005fef000

def z1028 : W := mkw 0x0417c0001eb68002 0x0105f00007ada000 0xe5b7e0001fffc003 0x396df80007fff000

def z1029 : W := mkw 0x80001816182c2c29 0x20000605860b0b0a 0xbc86181f183c3e3d 0x6f218607c60f0f8f

def z1030 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x9fb6971cf73b39f3 0x27eda5c73dcece7c

def z1031 : W := mkw 0x022805a01dc03781 0xc08a016807700de0 0x433807e017c039c2 0x90ce01f805f00e70

def z1032 : W := mkw 0x02ed5da01dc03781 0xc0bb576807700de0 0x73f97fe01fc03fc3 0xdcfe5ff807f00ff0

def z1033 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x57b6971cf73b39f3 0x95eda5c73dcece7c

def z1034 : W := mkw 0x08e83edbc0000000 0x023a0fb6f0000000 0xeaf9ffffe0000000 0xfabe7ffff8000000

def z1035 : W := mkw 0x0817e25bc0000000 0x0205f896f0000000 0xeaffffffe0000000 0xfabffffff8000000

def z1036 : W := mkw 0x4112a369e35353d6 0x9044a8da78d4d4f5 0x433087e0e70301c2 0x90cc21f839c0c070

def z1037 : W := mkw 0x0cfffedbc2368002 0x033fffb6f08da000 0xeffffffff73fc003 0xfbfffffffdcff000

def z1038 : W := mkw 0x0c3ae6c9c6928002 0x030eb9b271a4a000 0xefbef7fcf7fbc003 0xfbefbdff3dfef000

def z1039 : W := mkw 0x08d7fedbc0000000 0x0235ffb6f0000000 0xaac7ffffe0000000 0xeab1fffff8000000

def z1040 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xc5bfe00017ffc002 0x316ff80005fff000

def z1041 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x13f81fe01fc03fc0 0xc4fe07f807f00ff0

def z1042 : W := mkw 0x0012800002120002 0x0004a00000848000 0xe5bee00017fbc003 0x396fb80005fef000

def z1043 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xf7fe1fe01ff83fc3 0xfdff87f807fe0ff0

def z1044 : W := mkw 0x08287edbc0000000 0x020a1fb6f0000000 0x0a087fffe0000000 0xc2821ffff8000000

def z1045 : W := mkw 0x04ed40001eb68002 0x013b500007ada000 0xe549e0001fffc003 0x3952780007fff000

def z1046 : W := mkw 0x04ffc2089eb68002 0x013ff08227ada000 0xe7ffe700ffffc003 0xb9fff9c03ffff000

def z1047 : W := mkw 0x430001243dc93ff1 0xd0c000490f724ffc 0x110000001fc03ff3 0x0440000007f00ffc

def z1048 : W := mkw 0x043ac0001eb68002 0x010eb00007ada000 0xe5bee0001fffc003 0x396fb80007fff000

def z1049 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0xca3ee7fce0000000 0xb28fb9ff38000000

def z1050 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x8affffffe0000000 0x22bffffff8000000

def z1051 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xfdffe0001fffc033 0x7f7ff80007fff00c

def z1052 : W := mkw 0x043fc00006b68002 0x010ff00001ada000 0xe57fe0000fffc003 0x395ff80003fff000

def z1053 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x53781fe00fc03fc2 0xd4de07f803f00ff0

def z1054 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x6a481fffe0000000 0xda9207fff8000000

def z1055 : W := mkw 0x02001da001403781 0xc080076800500de0 0x13b01fe017003fc0 0xc4ec07f805c00ff0

def z1056 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x854fe0001fffc003 0x2153f80007fff000

def z1057 : W := mkw 0x08057edbc0000000 0x02015fb6f0000000 0x0a017fffe0000000 0xc2805ffff8000000

def z1058 : W := mkw 0x0412c0001eb68002 0x0104b00007ada000 0x0500e0001fffc003 0x0140380007fff000

def z1059 : W := mkw 0x82e81da01de43789 0xe0ba076807790de2 0x73f81fe01fc43fcf 0xdcfe07f807f10ff3

def z1060 : W := mkw 0x00ffe249c0000000 0x003ff89270000000 0xeaffffffe0000000 0xfabffffff8000000

def z1061 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xfff81fe01fc03ff3 0xfffe07f807f00ffc

def z1062 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73f91fe31fc43fcf 0xdcfe47f8c7f10ff3

def z1063 : W := mkw 0x80ed18161cac2c29 0x203b4605872b0b0a 0xbccf181f18fc3e3d 0x6f33c607c63f0f8f

def z1064 : W := mkw 0x4512c30ca31b9972 0x9144b0c328c6e65c 0xffb6f71cf73bf9f3 0xffedbdc73dcefe7c

def z1065 : W := mkw 0x08283edbc0000000 0x020a0fb6f0000000 0x4a381fffe0000000 0xd28e07fff8000000

def z1066 : W := mkw 0x083afedbc0000000 0x020ebfb6f0000000 0xea79ffffe0000000 0xfa9e7ffff8000000

def z1067 : W := mkw 0x08fffedbdc800000 0x023fffb6f7200000 0xeaffffffe8c00000 0xfabffffffa300000

def z1068 : W := mkw 0x00002061604142d4 0x00000818581050b5 0x5849e8e3e8c7c7fe 0xd6127a38fa31f1ff

def z1069 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x13b01fe01fc03fc3 0xc4ec07f807f00ff0

def z1070 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfbb6971cf73839f0 0xfeeda5c73dce0e7c

def z1071 : W := mkw 0x02281da005c03781 0xc08a076801700de0 0x13301fe007003fc0 0xc4cc07f801c00ff0

def z1072 : W := mkw 0x82ed3cf35ce4668d 0x60bb4f3cd73919a3 0x004968e308c4c60c 0x00125a38c2313183

def z1073 : W := mkw 0x02001da001403781 0xc080076800500de0 0x53301fe007003fc2 0xd4cc07f801c00ff0

def z1074 : W := mkw 0x88003edbc0002409 0x22000fb6f0000902 0x0a001fffe000060c 0xc28007fff8000183

def z1075 : W := mkw 0x0cffde9a9eb68002 0x033ff7a6a7ada000 0xe7fffffc1fffc003 0xf9ffffff07fff000

def z1076 : W := mkw 0x083afedbc0000000 0x020ebfb6f0000000 0xeabeffffe0000000 0xfaafbffff8000000

def z1077 : W := mkw 0x04ed40001eb68002 0x013b500007ada000 0xa5cf60001fffc003 0x2973d80007fff000

def z1078 : W := mkw 0x0417c00002368002 0x0105f000008da000 0xe5ffe0001fffc003 0x397ff80007fff000

def z1079 : W := mkw 0x043ac00006928002 0x010eb00001a4a000 0x41bee00017fbc002 0x106fb80005fef000

def z1080 : W := mkw 0x02ed1da01de43781 0xc0bb476807790de0 0xf7ffffe01fffffc3 0xfdfffff807fffff0

def z1081 : W := mkw 0x4112a24de21b4876 0x1044a8937886d21d 0x8c06e01ce03bc030 0x2301b807380ef00c

def z1082 : W := mkw 0x04fac0001eb68002 0x013eb00007ada000 0x65f8e0001fffc003 0x197e380007fff000

def z1083 : W := mkw 0x84ffd8121eb6a40b 0x213ff60487ada902 0xf5fff8031ffffe0f 0x7d7ffe00c7ffff83

def z1084 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x9c87101f183c3e3d 0x2721c407c60f0f8f

def z1085 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xe7b6971cf73b39c3 0xb9eda5c73dcece70

def z1086 : W := mkw 0x80050016182c2c29 0x20014005860b0b0a 0xbc47081f183c3e3d 0x6f11c207c60f0f8f

def z1087 : W := mkw 0x84ed58161cacac29 0x213b5605872b2b0a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z1088 : W := mkw 0x470001243fffbff3 0xd1c000490fffeffc 0x150000001ffffff3 0x0540000007fffffc

def z1089 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeaffffffe8c00003 0xfabffffffa300000

def z1090 : W := mkw 0x08fffedbd8002401 0x023fffb6f6000900 0xfefffffff8043e3d 0xffbffffffe010f8f

def z1091 : W := mkw 0x4917e25fe21b4876 0x1245f897f886d21d 0x8c07e01fe03fc03c 0x2301f807f80ff00f

def z1092 : W := mkw 0x0817fedbc0000000 0x0205ffb6f0000000 0xeab7ffffe0000000 0xfaadfffff8000000

def z1093 : W := mkw 0x06ed5da01de4b781 0xc1bb576807792de0 0xf7f9ffe01fc7ffc3 0xfdfe7ff807f1fff0

def z1094 : W := mkw 0x00e81e8880000000 0x003a07a220000000 0x6af81ffce0000000 0xdabe07ff38000000

def z1095 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x1fb6171cf73b39f3 0xc7ed85c73dcece7c

def z1096 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x53b817e01fc03fc3 0x94ee05f807f00ff0

def z1097 : W := mkw 0x04ffdc801eb6a403 0x013ff72007ada900 0xf7ffffe01ffffe03 0xfdfffff807ffff80

def z1098 : W := mkw 0x00fabec9c0000000 0x003eafb270000000 0xeaffffffe0000000 0xfabffffff8000000

def z1099 : W := mkw 0x00c50004182c0820 0x00314001060b0208 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z1100 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x7bf81fe31fc03fff 0xdefe07f8c7f00fff

def z1101 : W := mkw 0x08fffedbde920002 0x023fffb6f7a48000 0xeffffffffffb0003 0xfbfffffffffec000

def z1102 : W := mkw 0x80c5181600082c29 0x2031460580020b0a 0xbcc7181f10383e3d 0x6f31c607c40e0f8f

def z1103 : W := mkw 0x08fffedbd8240000 0x023fffb6f6090000 0xeefffffff8ffc003 0xfbbffffffe3ff000

def z1104 : W := mkw 0x0000012001401380 0x80000048005004e0 0x73b817e017c039c3 0xdcee05f805f00e70

def z1105 : W := mkw 0x00ffde8880000000 0x003ff7a220000000 0xeafffffce0000000 0xfabfffff38000000

def z1106 : W := mkw 0x0cfffedbc4808000 0x033fffb6f1202000 0xeaffffffe0c0c000 0xfabffffff8303000

def z1107 : W := mkw 0x00ed00001ca40000 0x003b400007290000 0xe5ffe0001fffc003 0x397ff80007fff000

def z1108 : W := mkw 0x0000000002120002 0x0000000000848000 0xe549e0001fffc003 0x3952780007fff000

def z1109 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeaffffffe0c3c002 0xfabffffff830f000

def z1110 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xebfffffffffcc000 0xfaffffffffff3000

def z1111 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x42ffffffe0000000 0x90bffffff8000000

def z1112 : W := mkw 0x0cfffedbdca48000 0x033fffb6f7292000 0xebffffffffc4c003 0xfafffffffff13000

def z1113 : W := mkw 0x0028058001001100 0x800a016000400440 0x73b817e0170039c3 0xdcee05f805c00e70

def z1114 : W := mkw 0x0cffdc921eb68002 0x033ff72487ada000 0xe5ffe0001fffc003 0x397ff80007fff000

def z1115 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73b01fe017003fc3 0xdcec07f805c00ff0

def z1116 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x85b7e0001fffc003 0x216df80007fff000

def z1117 : W := mkw 0x433aa7e9e7d353d6 0xd0cea9fa79f4d4f5 0x4338e7e0e7c3c1c2 0x90ce39f839f0f070

def z1118 : W := mkw 0x80051816182c2c29 0x20014605860b0b0a 0x9c07181f183c3e3d 0x6701c607c60f0f8f

def z1119 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeeffffffe8040001 0xfbbffffffa010000

def z1120 : W := mkw 0x08fffedbdc800000 0x023fffb6f7200000 0xebfffffff7000000 0xfafffffffdc00000

def z1121 : W := mkw 0x0cfffedbc6928002 0x033fffb6f1a4a000 0xefffffffefc7c003 0xfbfffffffbf1f000

def z1122 : W := mkw 0x08ffe6dbc0000000 0x023ff9b6f0000000 0xeaffe7ffe0000000 0xbabff9fff8000000

def z1123 : W := mkw 0x08ed7edbc0000000 0x023b5fb6f0000000 0xaacf7fffe0000000 0xeab3dffff8000000

def z1124 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0x85ffe0001fffc000 0x217ff80007fff000

def z1125 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfff69f1cff3b3ff3 0xfffda7c73fcecffc

def z1126 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeaffffffe804060c 0xfabffffffa010183

def z1127 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xedffe000ffffc003 0xfb7ff8003ffff000

def z1128 : W := mkw 0x4112a24de21b0872 0x1044a8937886c21c 0x8c07e01fe03b0030 0x2301f807f80ec00c

def z1129 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xc57fe0000fffc002 0x315ff80003fff000

def z1130 : W := mkw 0x84ffd8121eb6a40b 0x213ff60487ada902 0xe5ffe0001fffc003 0x397ff80007fff000

def z1131 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeefffffff0380001 0xfbbffffffc0e0000

def z1132 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x9fb6971cf73b39f0 0xe7eda5c73dcece7c

def z1133 : W := mkw 0x043fc00006b68002 0x010ff00001ada000 0x413ee00007fbc002 0x104fb80001fef000

def z1134 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffffff1fffffffff 0xffffffc7ffffffff

def z1135 : W := mkw 0x08ed7edbc0000000 0x023b5fb6f0000000 0xea49ffffe0000000 0xfa927ffff8000000

def z1136 : W := mkw 0x4112830c831a1922 0x9044a0c320c68648 0xfbb6971cf73839c3 0xfeeda5c73dce0e70

def z1137 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x8a4fffffe0000000 0xe293fffff8000000

def z1138 : W := mkw 0x0cffc21a9eb68002 0x033ff086a7ada000 0xe5ffe01c1fffc003 0x397ff80707fff000

def z1139 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfcc7981f183f3e3f 0x7f31e607c60fcf8f

def z1140 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0x42bef7fce0000000 0x90afbdff38000000

def z1141 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x63f81fe017c039c2 0xd8fe07f805f00e70

def z1142 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe5ffe8031fffc60f 0x397ffa00c7fff183

def z1143 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xeeffffffe007c000 0xfbbffffff801f000

def z1144 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0xaa411fffe0000000 0xea9047fff8000000

def z1145 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfaffffffe00001c3 0xfebffffff8000070

def z1146 : W := mkw 0x08fffedbc2120002 0x023fffb6f0848000 0xebfffffff7380000 0xfafffffffdce0000

def z1147 : W := mkw 0x02ed1db21dc03781 0xc0bb476c87700de0 0x73fe1ffc1fc03fc3 0xdcff87ff07f00ff0

def z1148 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xebfffffff7000003 0xfafffffffdc00000

def z1149 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xca7fefffe0000000 0xb29ffbfff8000000

def z1150 : W := mkw 0x08ed3edbc0000000 0x023b4fb6f0000000 0xeaff1fffe0000000 0xfabfc7fff8000000

def z1151 : W := mkw 0x04ffd8001eb6a403 0x013ff60007ada900 0xe5ffe8001fffc603 0x397ffa0007fff180

def z1152 : W := mkw 0x08003edbc0002401 0x02000fb6f0000900 0x1a001fffe0003e00 0xc68007fff8000f80

def z1153 : W := mkw 0x88fffedbd8242409 0x223fffb6f6090902 0xeefffffff83c060d 0xfbbffffffe0f0183

def z1154 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0x02b617fce0000000 0x80ad85ff38000000

def z1155 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0xaa861fffe0000000 0xeaa187fff8000000

def z1156 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x8a01ffffe0000000 0xe2807ffff8000000

def z1157 : W := mkw 0x02281da005c03781 0xc08a076801700de0 0x73781fe00fc03fc3 0xdcde07f803f00ff0

def z1158 : W := mkw 0x04c500001eb68002 0x0131400007ada000 0xe5cfe0001fffc003 0x3973f80007fff000

def z1159 : W := mkw 0x8aed7cf35ce42689 0x62bb5f3cd73909a2 0x004968e308c4060c 0x00125a38c2310183

def z1160 : W := mkw 0x02ed1db21dc03781 0xc0bb476c87700de0 0xffff1fff1fc43fff 0xffffc7ffc7f10fff

def z1161 : W := mkw 0x0c3afedbc6928002 0x030ebfb6f1a4a000 0x4b38ffffe7c3c002 0xd2ce3ffff9f0f000

def z1162 : W := mkw 0x08e83edbc0000000 0x023a0fb6f0000000 0x0ab01fffe0000000 0xc2ac07fff8000000

def z1163 : W := mkw 0x08fffedbd8240000 0x023fffb6f6090000 0xfefffffff83c063d 0xffbffffffe0f018f

def z1164 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfff79f1ff73b39f3 0xfffde7c7fdcece7c

def z1165 : W := mkw 0x49003fffe1495bf4 0x92400ffff85256fd 0x1a001fffe0003ffc 0xc68007fff8000fff

def z1166 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffb7f71cf73ff9f3 0xffedfdc73dcffe7c

def z1167 : W := mkw 0x00d780001a360002 0x0035e000068d8000 0xe5ffe0001fffc003 0x397ff80007fff000

def z1168 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x1a001fffe000063c 0xc68007fff800018f

def z1169 : W := mkw 0x02281da01dc03781 0xc08a076807700de0 0x53381fe01fc03fc3 0xd4ce07f807f00ff0

def z1170 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0xea009fffe0000000 0xfa8027fff8000000

def z1171 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfeffffffe0000031 0xffbffffff800000c

def z1172 : W := mkw 0x4300012421493ff1 0xd0c0004908524ffc 0x1000000000003ff0 0x0400000000000ffc

def z1173 : W := mkw 0x4517e24de23fc876 0x1145f893788ff21d 0x8c07e01fe03fc03c 0x2301f807f80ff00f

def z1174 : W := mkw 0x0812bedbc0000000 0x0204afb6f0000000 0x8a069fffe0000000 0xe281a7fff8000000

def z1175 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0xfccff81f183c3e3d 0x7f33fe07c60f0f8f

def z1176 : W := mkw 0x08fffedbc0000000 0x023fffb6f0000000 0xfaffffffe000063c 0xfebffffff800018f

def z1177 : W := mkw 0x04ffd8121eb6a403 0x013ff60487ada900 0xfdfff81f1ffffe03 0x7f7ffe07c7ffff80

def z1178 : W := mkw 0x083fe6dbc0000000 0x020ff9b6f0000000 0xeabff7ffe0000000 0xfaaffdfff8000000

def z1179 : W := mkw 0x0ced7edbdca48000 0x033b5fb6f7292000 0x0a497fffe8c4c000 0xc2925ffffa313000

def z1180 : W := mkw 0x84c518161cacac29 0x21314605872b2b0a 0xbcc7181f18fcfe3d 0x6f31c607c63f3f8f

def z1181 : W := mkw 0x00c0180418082c21 0x0030060106020b08 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z1182 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x5bb6971cf73b39f2 0xd6eda5c73dcece7c

def z1183 : W := mkw 0x040000001eb68002 0x0100000007ada000 0x054960001fffc003 0x0152580007fff000

def z1184 : W := mkw 0x4d17e25fe23f8872 0x1345f897f88fe21c 0x8c07e01fe03fc030 0x2301f807f80ff00c

def z1185 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xffbef71cf7fbf9f3 0xffefbdc73dfefe7c

def z1186 : W := mkw 0x022805a005c03781 0xc08a016801700de0 0x533807e007c03fc2 0x94ce01f801f00ff0

def z1187 : W := mkw 0x4100216561495bf4 0x90400859585256fd 0x180008e3e0003ffc 0xc6000238f8000fff

def z1188 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x0a497fffe0000000 0xc2925ffff8000000

def z1189 : W := mkw 0x00002061604142d4 0x00000818581050b5 0xfdf9e8e3ffc7c7ff 0xff7e7a38fff1f1ff

def z1190 : W := mkw 0x82ed1c961cac2c29 0x60bb4725872b0b0a 0xbcc7181f183c3e3d 0x6f31c607c60f0f8f

def z1191 : W := mkw 0x41128124235b5bf6 0x9044a04908d6d6fd 0xf5ffe0001fffffff 0x3d7ff80007ffffff

def z1192 : W := mkw 0x00e81d801d801100 0x803a076007600440 0x73f81fe01fc039c3 0xdcfe07f807f00e70

def z1193 : W := mkw 0x08fffedbc0004004 0x023fffb6f0001001 0xeaffffffe004c00c 0xfabffffff8013003

def z1194 : W := mkw 0x0c3fe6dbc6b68002 0x030ff9b6f1ada000 0xcf3fe7ffe7ffc002 0xb3cff9fff9fff000

def z1195 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x1c86181f183c3e3d 0x47218607c60f0f8f

def z1196 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0xf7f89fe01fc33fc3 0xfdfe27f807f0cff0

def z1197 : W := mkw 0x80c51816182c2c29 0x20314605860b0b0a 0x9c47081f183c3e3d 0x2711c207c60f0f8f

def z1198 : W := mkw 0x083afedbc0000000 0x020ebfb6f0000000 0x0a301fffe0000000 0xc28c07fff8000000

def z1199 : W := mkw 0x083ffedbc0000000 0x020fffb6f0000000 0xca3fffffe0000000 0xf28ffffff8000000

def z1200 : W := mkw 0x083fe6dbc0000000 0x020ff9b6f0000000 0x423ee7fce0000000 0x908fb9ff38000000

def z1201 : W := mkw 0x043ac00006b68002 0x010eb00001ada000 0x4538e00007ffc002 0x114e380001fff000

def z1202 : W := mkw 0x0cffc6889eb68002 0x033ff1a227ada000 0xe7ffe7001fffc003 0x39fff9c007fff000

def z1203 : W := mkw 0x04ffd8001eb6a403 0x013ff60007ada900 0xfdfff8031ffffe3f 0x7f7ffe00c7ffff8f

def z1204 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfff7971cff3f39f3 0xfffde5c73fcfce7c

def z1205 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0x4a08ffffe0000000 0xd2823ffff8000000

def z1206 : W := mkw 0x0cfffedbdca48000 0x033fffb6f7292000 0xeaffffffe0000000 0xfabffffff8000000

def z1207 : W := mkw 0x00001e8880000000 0x000007a220000000 0x0a001ffce0000000 0xc28007ff38000000

def z1208 : W := mkw 0x022805a005c01380 0xc08a0168017004e0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z1209 : W := mkw 0x41000124235b5bf6 0x9040004908d6d6fd 0x15000000173b3fff 0x0540000005cecfff

def z1210 : W := mkw 0x0aed5db21dc03781 0xc2bb576c87700de0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z1211 : W := mkw 0x08fafedbc0000000 0x023ebfb6f0000000 0x6af8ffffe0000000 0xdabe3ffff8000000

def z1212 : W := mkw 0x0012830c81081920 0x8004a0c320420648 0xffb6971cf73839f3 0xffeda5c73dce0e7c

def z1213 : W := mkw 0x84ffd8121eb6a40b 0x213ff60487ada902 0xfdffe8031fffc63f 0x7f7ffa00c7fff18f

def z1214 : W := mkw 0xc30001243fff3ffb 0xf0c000490fffcffe 0x150000001fff3fff 0x0540000007ffcfff

def z1215 : W := mkw 0x0812bedbc0000000 0x0204afb6f0000000 0xeaffffffe0000000 0xfabffffff8000000

def z1216 : W := mkw 0x02e81d801d803501 0xc0ba076007600d40 0x73f81fe0170039c3 0xdcfe07f805c00e70

def z1217 : W := mkw 0x0cffde9a9eb68002 0x033ff7a6a7ada000 0xeffff71cffffc003 0xfbfffdc73ffff000

def z1218 : W := mkw 0x08fffedbdca40000 0x023fffb6f7290000 0xeffffffffffc0003 0xfbffffffffff0000

def z1219 : W := mkw 0x82ed1db21de43789 0xe0bb476c87790de2 0xf7ff1fe31ffc3fcf 0xfdffc7f8c7ff0ff3

def z1220 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x53780fe01fc03fc3 0x94de03f807f00ff0

def z1221 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xfffe971cfffb39f3 0xffffa5c73ffece7c

def z1222 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x73f97fe01fc4ffc3 0xdcfe5ff807f13ff0

def z1223 : W := mkw 0x4100030ca1091970 0x904000c32842465c 0xffb6171cf73839f3 0xffed85c73dce0e7c

def z1224 : W := mkw 0x0cfffedbc2368002 0x033fffb6f08da000 0xeaffffffe0380000 0xfabffffff80e0000

def z1225 : W := mkw 0x02e81da01dc03781 0xc0ba076807700de0 0x33f01fe01f003fc1 0xccfc07f807c00ff0

def z1226 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0xebb6971cf73b39c2 0xfaeda5c73dcece70

def z1227 : W := mkw 0x08fffedbc4800000 0x023fffb6f1200000 0xebffffffe7c00002 0xfafffffff9f00000

def z1228 : W := mkw 0x083ae6c9c0000000 0x020eb9b270000000 0x4a38f7fce0000000 0xd28e3dff38000000

def z1229 : W := mkw 0x82ed1db21de43789 0xe0bb476c87790de2 0xfbff1fff1fc43fcf 0xfeffc7ffc7f10ff3

def z1230 : W := mkw 0x4112a24de21b4876 0x1044a8937886d21d 0x8c06801fe03b003c 0x2301a007f80ec00f

def z1231 : W := mkw 0x00e81da001401380 0x803a0768005004e0 0x73f81fe01fc03fc3 0xdcfe07f807f00ff0

def z1232 : W := mkw 0x43000124235b3ff3 0xd0c0004908d6cffc 0x15000000173b3ff3 0x0540000005cecffc

def z1233 : W := mkw 0x02c01da019403781 0xc0b0076806500de0 0x73f01fe01f003fc3 0xdcfc07f807c00ff0

def z1234 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0x43bef7fcf7fbc002 0x90efbdff3dfef000

def z1235 : W := mkw 0x043fc0001eb68002 0x010ff00007ada000 0xc53fe0001fffc003 0x314ff80007fff000

def z1236 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xe1ffe00017fbc002 0x387ff80005fef000

def z1237 : W := mkw 0x80051816002c2c29 0x20014605800b0b0a 0x1806181f00383e3c 0x46018607c00e0f8f

def z1238 : W := mkw 0x4112830ca31b1972 0x9044a0c328c6c65c 0x73b6971cf73b39c3 0xdceda5c73dcece70

def z1239 : W := mkw 0x0cfffedbdeb68002 0x033fffb6f7ada000 0xeffffffff73b0003 0xfbfffffffdcec000

def z1240 : W := mkw 0x00fa9e889e920002 0x003ea7a227a48000 0xeffe9ffcfffb0003 0xfbffa7ff3ffec000

def z1241 : W := mkw 0x04ffc0001eb68002 0x013ff00007ada000 0xf5fff0001ffff803 0x7d7ffc0007fffe00

def z1242 : W := mkw 0x08003edbc0000000 0x02000fb6f0000000 0xee49ffffe8c7c003 0xfb927ffffa31f000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z5,z7,z6]),(0,[z8,z0,z1,z2,z3,z5,z6])],[(0,[z9,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z10,z2,z11,z5,z6]),(0,[z0,z1,z10,z2,z12,z5,z6]),(0,[z13,z0,z1,z2,z3,z14,z6]),(0,[z15,z0,z1,z2,z3,z5,z6])],[(0,[z16,z0,z1,z2,z17,z5,z6]),(0,[z0,z1,z2,z18,z5,z19,z6]),(0,[z20,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z21,z5,z6,z22]),(1,[z0,z23,z1,z11,z5,z6])],[(0,[z0,z1,z2,z3,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z25,z6]),(0,[z0,z26,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z27,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z28]),(0,[z0,z1,z29,z2,z30,z5,z6])],[(0,[z0,z1,z10,z2,z3,z5,z6]),(0,[z0,z1,z31,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z32,z5]),(0,[z0,z1,z2,z11,z5,z6,z33])],[(0,[z0,z34,z35,z2,z3,z5,z6]),(0,[z36,z0,z1,z2,z3,z5,z6]),(0,[z0,z29,z2,z37,z3,z5,z6]),(0,[z0,z38,z1,z39,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z40,z6]),(0,[z0,z1,z2,z3,z5,z41,z6])],[(0,[z0,z1,z2,z3,z42,z5,z6]),(0,[z0,z1,z2,z3,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z44])],[(1,[z0,z1,z2,z3,z5,z45]),(0,[z0,z1,z46,z3,z47,z5,z6]),(1,[z0,z1,z2,z3,z48,z6]),(0,[z0,z1,z2,z3,z5,z6,z49])]],
   [[(0,[z50,z0,z1,z2,z3,z5,z6]),(0,[z51,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z52,z3,z5,z6]),(0,[z0,z1,z2,z53,z3,z5,z6]),(0,[z54,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z55,z2,z3,z5,z6])],[],[(0,[z56,z0,z57,z2,z3,z5,z6]),(0,[z0,z1,z2,z58,z3,z5,z6]),(0,[z0,z34,z2,z3,z59,z5,z6]),(0,[z0,z1,z2,z3,z5,z60,z6]),(1,[z0,z1,z2,z30,z5,z6]),(0,[z0,z1,z2,z3,z61,z5,z6])],[(0,[z0,z1,z2,z46,z5,z6,z22]),(0,[z0,z62,z1,z2,z3,z5,z6]),(0,[z0,z63,z1,z2,z3,z5,z64]),(0,[z65,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z66]),(0,[z0,z1,z2,z3,z11,z5,z6])],[(0,[z0,z1,z2,z3,z67,z5,z6]),(1,[z0,z1,z2,z18,z5,z6]),(0,[z0,z1,z2,z3,z68,z5,z6])],[(0,[z0,z1,z2,z3,z5,z69,z6]),(0,[z0,z63,z1,z2,z70,z5,z6]),(1,[z0,z71,z2,z3,z5,z72]),(1,[z0,z1,z2,z73,z5,z6]),(0,[z0,z1,z29,z2,z3,z5,z74]),(0,[z75,z0,z1,z2,z3,z5,z6]),(0,[z76,z0,z1,z2,z3,z5,z6])],[(0,[z77,z0,z1,z2,z3,z5,z6]),(0,[z78,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z34,z79,z2,z3,z5,z6]),(0,[z0,z2,z21,z3,z59,z5,z6])],[(0,[z0,z1,z2,z3,z80,z5,z6]),(0,[z0,z81,z1,z2,z3,z5,z6]),(0,[z0,z82,z1,z2,z43,z5,z6]),(0,[z0,z1,z2,z12,z5,z83,z6]),(0,[z84,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z85,z5,z6]),(0,[z0,z86,z1,z2,z87,z5,z6])]],
   [[(1,[z88,z57,z2,z3,z5,z6]),(0,[z89,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z90,z2,z3,z5,z6]),(0,[z91,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z92,z5,z6]),(0,[z0,z1,z2,z3,z5,z93,z6]),(0,[z0,z1,z2,z94,z3,z5,z6]),(1,[z0,z1,z11,z5,z95,z6]),(1,[z0,z96,z1,z3,z95,z6]),(0,[z0,z1,z2,z3,z5,z6,z97])],[(0,[z88,z0,z35,z2,z3,z5,z6]),(0,[z0,z98,z1,z2,z3,z5,z6]),(0,[z0,z99,z1,z2,z3,z5,z6])],[(0,[z100,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z101,z6]),(0,[z0,z1,z2,z3,z5,z102,z6]),(1,[z0,z1,z2,z3,z5,z103]),(1,[z0,z1,z104,z3,z5,z6])],[(0,[z0,z105,z1,z2,z3,z5,z6]),(0,[z0,z1,z90,z46,z3,z5,z6]),(0,[z0,z34,z2,z3,z5,z6,z72]),(0,[z0,z1,z2,z106,z3,z5,z6]),(0,[z0,z1,z29,z2,z11,z5,z6]),(0,[z0,z1,z2,z12,z5,z107,z6]),(0,[z0,z108,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z109,z6])],[(0,[z0,z110,z1,z2,z3,z5,z6]),(0,[z0,z1,z111,z2,z3,z5,z6]),(0,[z0,z1,z2,z112,z3,z5,z6]),(0,[z0,z82,z1,z2,z11,z5,z6]),(0,[z0,z1,z113,z2,z3,z5,z6]),(0,[z0,z114,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z115,z70,z5,z6])],[(0,[z0,z35,z1,z2,z12,z5,z6]),(0,[z116,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z117,z3,z5,z6]),(0,[z118,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z39,z58,z3,z5,z6]),(0,[z0,z1,z2,z17,z11,z5,z6]),(0,[z0,z1,z29,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z119,z6]),(0,[z0,z1,z120,z2,z3,z5,z6])],[(0,[z0,z1,z2,z121,z3,z5,z6]),(0,[z0,z82,z1,z2,z3,z5,z6]),(0,[z122,z0,z2,z21,z3,z5,z6]),(1,[z0,z1,z12,z11,z5,z6]),(0,[z0,z1,z39,z3,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z123,z6]),(0,[z0,z1,z2,z3,z5,z6,z124]),(0,[z0,z125,z2,z3,z5,z126,z6])]],
   [[(0,[z0,z23,z1,z2,z12,z5,z6]),(0,[z0,z23,z1,z2,z11,z5,z6]),(0,[z0,z127,z1,z2,z3,z5,z6])],[(0,[z0,z128,z1,z2,z3,z129,z6]),(1,[z0,z1,z2,z61,z5,z6]),(0,[z0,z86,z1,z2,z3,z5,z130])],[(0,[z0,z63,z1,z2,z21,z5,z6]),(0,[z0,z63,z1,z2,z3,z5,z7]),(1,[z0,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z131,z3,z5,z6])],[(0,[z132,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z133,z6]),(0,[z0,z1,z2,z134,z3,z5,z6]),(0,[z0,z34,z135,z2,z3,z5,z6]),(0,[z0,z23,z1,z2,z3,z5,z6]),(1,[z0,z2,z37,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z136,z6]),(0,[z0,z1,z2,z3,z5,z6,z137])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z35,z1,z57,z2,z3,z5,z6]),(0,[z138,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z11,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z139,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z19,z6]),(0,[z0,z1,z2,z140,z3,z5,z6])],[(0,[z0,z141,z1,z2,z3,z5,z6]),(0,[z0,z142,z1,z2,z3,z5,z6]),(0,[z143,z0,z1,z2,z3,z5,z6]),(0,[z144,z0,z96,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z145,z5,z6]),(1,[z0,z1,z2,z85,z5,z6])],[(0,[z0,z135,z57,z2,z3,z5,z6]),(0,[z0,z146,z1,z2,z3,z5,z6]),(0,[z0,z35,z2,z112,z3,z5,z6]),(0,[z0,z1,z147,z2,z3,z5,z6]),(0,[z0,z1,z2,z148,z3,z5,z6]),(0,[z0,z1,z2,z149,z11,z5,z6]),(0,[z0,z1,z2,z3,z32,z5,z150])]],
   [[(0,[z0,z1,z2,z3,z5,z151,z6]),(0,[z0,z1,z39,z112,z3,z5,z6]),(0,[z0,z1,z29,z2,z3,z152,z6]),(0,[z0,z1,z2,z3,z5,z6,z153]),(0,[z0,z2,z3,z5,z154,z107,z6])],[(0,[z155,z0,z1,z2,z11,z5,z6]),(0,[z155,z0,z1,z2,z12,z5,z6])],[(1,[z0,z156,z2,z3,z5,z6]),(0,[z157,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z158,z3,z5,z6]),(1,[z0,z38,z1,z3,z5,z150])],[(0,[z0,z1,z2,z3,z5,z159,z6]),(0,[z0,z1,z58,z3,z5,z6,z150]),(0,[z0,z160,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z111,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z33]),(0,[z0,z1,z29,z2,z161,z5,z6]),(0,[z0,z162,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z126,z6,z163])],[(0,[z155,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z164,z6]),(0,[z0,z63,z2,z3,z59,z5,z6]),(0,[z165,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z166,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z167,z6]),(1,[z0,z1,z2,z3,z14,z6]),(0,[z0,z1,z2,z3,z5,z168,z6]),(0,[z0,z1,z2,z3,z169,z5,z6])],[(0,[z170,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z19,z6,z163]),(0,[z0,z171,z1,z2,z3,z5,z103]),(0,[z0,z1,z2,z3,z5,z6,z172])],[(0,[z0,z1,z173,z2,z3,z5,z6]),(0,[z0,z82,z1,z2,z70,z5,z6]),(0,[z0,z1,z2,z174,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z175]),(0,[z0,z171,z34,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z176,z6]),(0,[z0,z177,z1,z2,z3,z5,z6]),(0,[z0,z178,z2,z3,z5,z107,z6]),(0,[z0,z1,z2,z3,z5,z179,z6])],[(0,[z180,z0,z1,z2,z3,z5,z6]),(0,[z0,z181,z1,z182,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z183,z6])],[(0,[z184,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z161,z5,z6])],[(0,[z56,z0,z1,z2,z12,z5,z6]),(0,[z185,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z186,z6]),(0,[z0,z187,z1,z2,z5,z129,z6]),(0,[z0,z188,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z189,z5,z6]),(0,[z190,z0,z96,z1,z3,z5,z6]),(0,[z0,z191,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z150])],[(0,[z0,z192,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z193,z5,z6]),(1,[z0,z1,z2,z145,z5,z6])],[(0,[z194,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z19,z6]),(0,[z0,z195,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z196,z11,z5,z6]),(0,[z0,z197,z1,z2,z3,z5,z6])],[(0,[z144,z0,z1,z58,z3,z5,z6]),(1,[z190,z1,z10,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z198]),(0,[z199,z0,z1,z2,z3,z5,z150])]],
   [[(0,[z144,z0,z1,z3,z11,z5,z6]),(0,[z0,z1,z2,z200,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z201,z6]),(0,[z0,z1,z2,z3,z5,z6,z202]),(0,[z0,z203,z1,z2,z3,z5,z6]),(0,[z0,z181,z1,z2,z115,z5,z6])],[(1,[z0,z1,z2,z3,z5,z204]),(0,[z0,z205,z1,z2,z3,z5,z6]),(0,[z206,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z207,z29,z3,z5,z6]),(0,[z0,z208,z1,z2,z3,z5,z6])],[(0,[z144,z0,z1,z2,z3,z209,z6]),(0,[z0,z210,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z211,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z212,z6])],[(0,[z0,z1,z2,z3,z5,z213,z6]),(0,[z0,z181,z1,z2,z87,z5,z6]),(0,[z214,z0,z1,z2,z3,z5,z6])],[(1,[z0,z215,z2,z3,z5,z6]),(0,[z0,z82,z1,z2,z21,z5,z6]),(0,[z0,z1,z2,z12,z216,z5,z6]),(0,[z0,z1,z2,z217,z5,z126,z6])],[(0,[z122,z56,z0,z2,z3,z5,z6]),(0,[z16,z1,z2,z46,z3,z5,z6]),(0,[z218,z0,z1,z2,z3,z5,z6]),(0,[z0,z219,z1,z2,z3,z5,z6]),(0,[z0,z220,z1,z2,z3,z5,z6])],[(0,[z0,z221,z1,z2,z3,z5,z6]),(0,[z218,z1,z2,z3,z5,z19,z6]),(0,[z0,z222,z1,z2,z3,z5,z6]),(0,[z0,z128,z1,z2,z11,z5,z6]),(0,[z0,z128,z1,z2,z12,z5,z6]),(0,[z0,z1,z117,z2,z3,z5,z6])],[(1,[z223,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z224]),(0,[z225,z0,z1,z2,z3,z5,z6]),(1,[z0,z181,z1,z2,z107,z6]),(0,[z0,z1,z2,z3,z226,z5,z6])]],
   [[(0,[z0,z1,z227,z2,z3,z5,z6]),(0,[z0,z86,z228,z2,z3,z5,z6]),(0,[z0,z1,z228,z2,z3,z5,z6]),(0,[z0,z1,z229,z2,z3,z5,z6])],[(0,[z0,z34,z57,z2,z3,z5,z6]),(0,[z0,z128,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z2,z3,z95,z6]),(0,[z0,z1,z2,z230,z3,z5,z6])],[(1,[z0,z1,z2,z3,z231,z6]),(1,[z0,z1,z2,z3,z5,z7])],[(0,[z0,z232,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z11,z5,z6]),(0,[z0,z1,z2,z12,z12,z5,z6]),(0,[z0,z1,z2,z3,z233,z5,z6])],[(0,[z13,z0,z62,z2,z3,z5,z6]),(0,[z0,z234,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z235,z3,z5,z6]),(0,[z0,z1,z2,z21,z87,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z236]),(0,[z0,z1,z2,z11,z5,z6,z150]),(0,[z0,z1,z2,z3,z5,z6,z237])],[(0,[z0,z1,z2,z3,z5,z238,z6]),(0,[z190,z0,z1,z3,z11,z5,z6]),(0,[z0,z239,z1,z2,z3,z5,z6]),(0,[z0,z128,z1,z2,z3,z59,z6]),(0,[z0,z1,z2,z2,z12,z5,z6])],[(0,[z0,z63,z1,z240,z3,z5,z6]),(0,[z0,z241,z1,z2,z3,z5,z6]),(0,[z0,z242,z1,z2,z3,z5,z6])]],
   [[(1,[z243,z0,z1,z2,z3,z5]),(0,[z0,z244,z29,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z245,z6]),(0,[z0,z1,z2,z3,z5,z6,z246]),(0,[z247,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z248,z5,z6]),(0,[z0,z1,z2,z11,z5,z6,z202])],[(0,[z249,z0,z1,z2,z3,z5,z6]),(1,[z0,z187,z1,z2,z5,z6])],[(0,[z223,z0,z2,z3,z5,z19,z6]),(0,[z250,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z251,z3,z5,z6])],[(0,[z0,z1,z2,z3,z252,z5,z6])],[(0,[z88,z0,z57,z2,z3,z5,z6]),(0,[z0,z1,z79,z3,z11,z5,z6]),(0,[z0,z253,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z254,z6]),(1,[z0,z1,z2,z255,z5,z6])],[(0,[z0,z1,z2,z256,z3,z5,z6]),(0,[z0,z1,z2,z3,z17,z5,z6]),(0,[z0,z1,z2,z87,z43,z5,z6]),(0,[z0,z1,z257,z2,z3,z5,z6])],[(0,[z1,z2,z46,z3,z17,z5,z6]),(0,[z0,z1,z2,z12,z46,z5,z6]),(1,[z0,z1,z111,z3,z5,z6]),(0,[z0,z82,z2,z3,z5,z6,z72]),(0,[z258,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z126,z6,z259])]],
   [[(0,[z260,z0,z1,z2,z3,z5,z6]),(0,[z0,z261,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z262,z6]),(0,[z0,z71,z1,z2,z11,z5,z6]),(0,[z0,z71,z1,z2,z12,z5,z6]),(0,[z263,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z264,z5,z6]),(0,[z0,z1,z2,z3,z5,z265,z6])],[(0,[z0,z266,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z267,z6]),(0,[z0,z1,z2,z3,z5,z268,z6]),(1,[z0,z1,z39,z11,z5,z6]),(0,[z269,z0,z1,z2,z3,z5,z6]),(0,[z0,z181,z1,z2,z5,z107,z6])],[(0,[z0,z270,z1,z2,z3,z5,z6]),(0,[z0,z135,z2,z112,z3,z5,z6]),(0,[z0,z1,z271,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z272]),(0,[z0,z1,z39,z2,z11,z5,z6]),(0,[z0,z273,z1,z2,z11,z5,z6]),(1,[z0,z1,z207,z12,z5,z6]),(0,[z0,z1,z2,z274,z12,z5,z6]),(0,[z0,z1,z39,z2,z12,z5,z6]),(0,[z0,z275,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z276]),(0,[z0,z71,z1,z2,z3,z5,z6]),(0,[z0,z277,z1,z2,z3,z5,z6]),(0,[z0,z23,z1,z207,z3,z5,z6]),(0,[z0,z1,z2,z87,z11,z5,z6]),(0,[z0,z1,z207,z3,z5,z6,z150]),(0,[z0,z1,z2,z3,z32,z126,z6]),(1,[z0,z125,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z278,z6]),(0,[z0,z1,z2,z3,z279,z5,z6]),(0,[z280,z0,z1,z2,z3,z5,z6]),(0,[z281,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z39,z3,z5,z83])],[(0,[z0,z1,z2,z274,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z19,z6]),(0,[z0,z1,z2,z3,z5,z72,z150]),(0,[z0,z86,z1,z2,z11,z5,z6]),(0,[z0,z273,z1,z2,z3,z5,z6]),(0,[z0,z86,z1,z2,z12,z5,z6])],[(0,[z0,z1,z282,z2,z3,z5,z6]),(0,[z0,z283,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z284,z6]),(0,[z0,z1,z2,z37,z3,z5,z6]),(0,[z0,z1,z2,z87,z3,z5,z6]),(0,[z199,z0,z1,z2,z3,z6,z163])],[(0,[z0,z1,z2,z285,z3,z5,z6]),(0,[z0,z82,z135,z2,z3,z5,z6]),(0,[z0,z1,z2,z286,z3,z5,z6]),(0,[z0,z1,z2,z287,z3,z5,z6])]],
   [[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z288]),(0,[z289,z0,z1,z2,z11,z5,z6]),(0,[z289,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z290,z2,z3,z5,z6]),(0,[z291,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z292,z6])],[(0,[z0,z1,z2,z3,z293,z5,z6])],[(0,[z0,z1,z294,z2,z3,z5,z6]),(0,[z0,z1,z3,z295,z5,z19,z6]),(0,[z0,z1,z2,z3,z5,z6,z296]),(0,[z1,z2,z3,z5,z297,z6,z33]),(0,[z0,z2,z112,z3,z59,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z298])],[(0,[z299,z0,z1,z2,z3,z5,z6]),(0,[z289,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z300,z5,z6]),(0,[z291,z0,z1,z2,z3,z5,z6]),(0,[z0,z301,z1,z2,z3,z5,z6])],[(0,[z0,z302,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z303,z6]),(0,[z0,z1,z2,z3,z5,z304,z6])],[(1,[z289,z1,z2,z17,z5,z6]),(0,[z0,z1,z156,z2,z3,z5,z6]),(0,[z0,z79,z2,z112,z3,z5,z6]),(0,[z122,z0,z128,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z305,z6])],[(0,[z13,z0,z1,z2,z306,z5,z6]),(0,[z0,z1,z2,z43,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z307,z6]),(0,[z0,z1,z308,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z309])],[(0,[z310,z0,z1,z2,z3,z5,z6]),(0,[z0,z311,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z87,z46,z5,z6]),(0,[z0,z1,z312,z2,z3,z5,z6]),(0,[z0,z313,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z262,z6]),(0,[z0,z1,z39,z2,z3,z5,z150])]],
   [[(0,[z0,z35,z1,z2,z11,z5,z6]),(0,[z185,z0,z1,z2,z3,z314,z6]),(0,[z0,z1,z207,z79,z3,z5,z6]),(0,[z0,z315,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z316,z6]),(0,[z317,z0,z1,z2,z3,z5,z6]),(0,[z0,z318,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z32,z5,z83]),(0,[z0,z1,z2,z3,z32,z5,z6])],[(0,[z0,z319,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z45,z6]),(0,[z0,z1,z112,z3,z5,z6,z150]),(0,[z0,z320,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z321]),(0,[z0,z322,z1,z2,z3,z5,z6])],[(0,[z323,z0,z1,z2,z3,z5,z6]),(0,[z324,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z27,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z103]),(0,[z0,z1,z29,z3,z152,z5,z6]),(0,[z0,z86,z210,z2,z3,z5,z6]),(0,[z0,z1,z257,z3,z5,z126,z6]),(0,[z0,z1,z2,z3,z5,z6,z259])],[(0,[z0,z35,z1,z2,z3,z5,z6]),(0,[z325,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z326]),(0,[z0,z2,z112,z3,z5,z6,z72]),(0,[z0,z1,z327,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z328,z5,z6]),(0,[z0,z1,z2,z3,z329,z5,z6])],[(1,[z0,z1,z2,z330,z5,z6]),(0,[z289,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z331]),(0,[z0,z332,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z74]),(0,[z0,z333,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z334,z5,z6]),(0,[z0,z335,z1,z2,z3,z5,z6]),(0,[z0,z1,z207,z2,z11,z5,z6]),(0,[z0,z1,z207,z2,z12,z5,z6]),(0,[z0,z1,z207,z12,z3,z5,z6]),(0,[z0,z1,z336,z2,z3,z5,z6]),(0,[z0,z1,z2,z337,z3,z5,z6])],[(0,[z0,z1,z2,z87,z70,z5,z6]),(0,[z0,z1,z338,z2,z3,z5,z6])],[(0,[z0,z1,z2,z339,z3,z5,z6]),(0,[z0,z332,z1,z2,z3,z5,z6]),(1,[z0,z1,z240,z3,z5,z6]),(0,[z0,z1,z12,z3,z11,z5,z6])]],
   [[(0,[z340,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z341]),(0,[z185,z0,z1,z2,z3,z19,z6]),(1,[z0,z62,z2,z3,z5,z6]),(0,[z0,z1,z207,z2,z3,z5,z6])],[(0,[z0,z1,z2,z342,z3,z5,z6]),(0,[z0,z181,z82,z1,z2,z5,z6]),(0,[z0,z343,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z344,z6]),(0,[z0,z1,z2,z3,z70,z5,z6])],[(0,[z218,z0,z1,z2,z3,z314,z6]),(0,[z0,z1,z345,z2,z3,z5,z6]),(0,[z0,z1,z2,z346,z3,z5,z6]),(0,[z0,z1,z2,z11,z293,z5,z6]),(1,[z0,z1,z2,z87,z5,z130])],[(0,[z144,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z29,z2,z3,z5,z347])],[(0,[z0,z1,z348,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z349,z6]),(1,[z199,z0,z1,z2,z3,z163])],[(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z199,z0,z1,z2,z11,z5,z6]),(0,[z199,z0,z1,z2,z12,z5,z6])],[(0,[z0,z1,z2,z3,z5,z350,z6]),(0,[z0,z351,z1,z2,z3,z5,z6]),(0,[z0,z1,z79,z3,z5,z6,z150]),(0,[z0,z1,z104,z2,z3,z5,z6]),(0,[z352,z0,z1,z2,z3,z5,z6]),(0,[z0,z71,z1,z2,z3,z5,z72]),(0,[z0,z1,z2,z3,z5,z95,z6]),(0,[z0,z181,z1,z2,z3,z70,z6]),(0,[z0,z353,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z354,z5,z6])],[(0,[z13,z0,z1,z355,z3,z5,z6]),(0,[z0,z171,z1,z2,z300,z5,z6])]],
   [[(0,[z0,z356,z1,z2,z3,z5,z6]),(0,[z190,z0,z1,z10,z3,z5,z6]),(1,[z0,z135,z2,z3,z5,z357]),(0,[z0,z1,z2,z3,z5,z358,z6]),(0,[z199,z0,z1,z2,z3,z5,z83]),(0,[z199,z0,z1,z2,z3,z5,z6])],[(0,[z0,z359,z1,z2,z3,z5,z6]),(0,[z0,z360,z1,z3,z5,z19,z6]),(0,[z0,z1,z2,z11,z32,z5,z6]),(0,[z0,z1,z3,z11,z5,z95,z6]),(0,[z0,z1,z2,z3,z5,z6,z361]),(0,[z0,z1,z2,z3,z5,z6,z362]),(1,[z0,z1,z2,z5,z6,z259])],[(0,[z0,z1,z2,z3,z363,z5,z6]),(0,[z218,z0,z1,z2,z3,z19,z6]),(0,[z122,z0,z2,z112,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z347]),(0,[z0,z1,z2,z3,z5,z364,z6])],[(0,[z365,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z366]),(0,[z0,z367,z1,z2,z3,z5,z6]),(0,[z368,z0,z1,z2,z3,z5,z6])],[],[(0,[z0,z1,z2,z3,z5,z83,z33]),(0,[z0,z1,z2,z3,z5,z369,z6]),(0,[z0,z1,z2,z370,z3,z5,z6])],[(0,[z56,z0,z1,z2,z11,z5,z6]),(1,[z0,z1,z3,z47,z5,z6]),(0,[z0,z171,z1,z2,z27,z5,z6]),(0,[z0,z63,z82,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z64]),(0,[z0,z1,z2,z3,z371,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z372]),(0,[z0,z1,z2,z373,z3,z5,z6]),(0,[z0,z374,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z3,z375,z5,z6])]],
   [[(0,[z0,z1,z2,z376,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z72,z22])],[(0,[z56,z0,z1,z2,z3,z5,z6]),(1,[z0,z377,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z209,z6]),(0,[z190,z0,z1,z2,z11,z5,z6]),(0,[z190,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z378,z2,z3,z5,z6]),(0,[z0,z1,z2,z379,z3,z5,z6]),(0,[z0,z1,z2,z380,z3,z5,z6]),(0,[z0,z1,z2,z3,z381,z5,z6]),(0,[z0,z181,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z3,z382,z5,z6]),(0,[z0,z181,z1,z2,z12,z5,z6])],[(0,[z289,z0,z181,z1,z2,z5,z6]),(0,[z155,z0,z1,z2,z3,z32,z5]),(0,[z0,z1,z2,z3,z5,z383,z6]),(0,[z0,z1,z2,z3,z5,z357,z150]),(0,[z0,z374,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z11,z5,z6,z150]),(0,[z0,z1,z2,z11,z70,z5,z6])],[(0,[z0,z1,z2,z3,z384,z5,z6]),(0,[z0,z1,z2,z3,z385,z5,z6]),(0,[z0,z34,z1,z112,z3,z5,z6]),(0,[z386,z0,z1,z2,z3,z5,z6])],[(0,[z0,z387,z1,z2,z3,z5,z6]),(0,[z190,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z388,z2,z3,z5,z6]),(0,[z0,z1,z389,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z390]),(1,[z0,z1,z2,z391,z5,z6]),(0,[z0,z1,z2,z3,z196,z5,z6]),(0,[z0,z1,z3,z5,z83,z6,z150])],[(0,[z0,z1,z2,z392,z3,z5,z6]),(0,[z218,z185,z1,z2,z3,z5,z6]),(0,[z0,z393,z1,z2,z3,z5,z6]),(0,[z0,z1,z394,z2,z3,z5,z6]),(0,[z0,z395,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z2,z12,z5,z6]),(0,[z0,z1,z39,z2,z255,z5,z6]),(0,[z0,z396,z1,z2,z3,z5,z6]),(0,[z0,z397,z1,z2,z3,z5,z6])],[(0,[z223,z0,z1,z2,z3,z5,z6]),(0,[z0,z398,z1,z2,z3,z5,z6]),(0,[z0,z181,z1,z251,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z399,z6])],[(0,[z0,z57,z2,z112,z3,z5,z6]),(0,[z243,z0,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z235,z5,z6]),(0,[z0,z400,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z59,z5,z6]),(0,[z0,z1,z2,z11,z5,z95,z6])]],
   [[(0,[z0,z1,z2,z330,z3,z5,z6]),(0,[z0,z1,z79,z2,z11,z5,z6]),(0,[z0,z1,z79,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z401,z6]),(0,[z0,z1,z2,z3,z5,z6,z402])],[(0,[z88,z1,z57,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z204]),(0,[z0,z403,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z43,z5,z6])],[(1,[z0,z1,z2,z306,z5,z6]),(0,[z0,z244,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z404,z6]),(0,[z0,z1,z79,z2,z3,z5,z6]),(0,[z0,z405,z1,z2,z3,z5,z6]),(0,[z0,z71,z2,z3,z5,z6,z72]),(0,[z406,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z87,z3,z5,z22])],[(1,[z155,z1,z2,z3,z5,z297]),(0,[z0,z1,z2,z407,z12,z5,z6]),(0,[z0,z38,z408,z2,z3,z5,z6])],[(0,[z0,z1,z409,z2,z3,z5,z6]),(0,[z0,z410,z1,z2,z3,z5,z6]),(0,[z0,z86,z1,z2,z3,z5,z22])],[(0,[z0,z1,z2,z3,z411,z5,z6]),(0,[z0,z1,z10,z2,z412,z5,z6]),(0,[z0,z171,z1,z112,z3,z5,z6]),(0,[z0,z1,z413,z2,z3,z5,z6]),(0,[z0,z414,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z32,z5,z163])],[(0,[z0,z1,z10,z2,z121,z5,z6]),(0,[z0,z135,z2,z3,z43,z5,z6]),(0,[z0,z1,z2,z407,z3,z5,z6])]],
   [[(0,[z0,z1,z415,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z72]),(0,[z416,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z130,z6]),(0,[z0,z1,z2,z3,z5,z6,z417])],[(0,[z0,z1,z2,z12,z3,z5,z6]),(0,[z0,z1,z2,z2,z11,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z418])],[(0,[z0,z1,z2,z3,z5,z419,z6]),(0,[z0,z1,z2,z3,z5,z420,z6]),(0,[z0,z71,z135,z2,z3,z5,z6]),(0,[z0,z135,z1,z2,z11,z5,z6]),(0,[z0,z135,z1,z2,z12,z5,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z39,z10,z3,z5,z6]),(0,[z16,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z46,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z421,z6]),(0,[z422,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z423,z6]),(1,[z0,z1,z424,z3,z5,z6])],[(0,[z0,z1,z2,z3,z32,z314,z6]),(0,[z122,z0,z63,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z129,z6]),(0,[z0,z1,z207,z3,z5,z95,z6]),(0,[z0,z1,z2,z3,z152,z5,z6])],[(0,[z0,z1,z2,z87,z17,z5,z6]),(0,[z122,z0,z1,z2,z3,z129,z6]),(0,[z0,z135,z1,z2,z3,z5,z6]),(0,[z0,z71,z1,z117,z3,z5,z6]),(1,[z0,z2,z3,z5,z154,z6])],[(0,[z0,z1,z2,z46,z3,z5,z6]),(0,[z425,z0,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z5,z33]),(0,[z0,z1,z2,z3,z300,z5,z6]),(0,[z0,z1,z2,z3,z5,z426,z6]),(1,[z0,z1,z2,z427,z5,z6]),(0,[z0,z1,z3,z152,z5,z6,z150])]],
   [[(0,[z0,z428,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z429,z6]),(0,[z0,z82,z2,z21,z3,z5,z6]),(0,[z0,z1,z2,z11,z59,z5,z6]),(0,[z0,z1,z2,z430,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z431]),(0,[z0,z1,z2,z12,z32,z5,z6]),(0,[z0,z38,z318,z2,z3,z5,z6]),(0,[z432,z0,z1,z2,z3,z5,z6])],[(0,[z0,z433,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z434])],[(0,[z0,z1,z2,z3,z231,z5,z6]),(0,[z0,z1,z2,z3,z435,z5,z6]),(0,[z436,z0,z1,z2,z3,z5,z6])],[(0,[z0,z35,z2,z3,z5,z6,z72]),(0,[z289,z0,z1,z2,z17,z5,z6]),(1,[z0,z1,z355,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z437]),(0,[z0,z1,z2,z3,z5,z6,z438]),(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z130,z6,z22]),(0,[z0,z1,z440,z2,z3,z5,z6])],[(0,[z441,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z442,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z443,z6]),(0,[z0,z1,z2,z444,z3,z5,z6]),(0,[z0,z181,z63,z1,z2,z5,z6]),(0,[z445,z0,z1,z2,z12,z5,z6]),(0,[z0,z96,z1,z29,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z446,z6]),(0,[z0,z125,z1,z2,z3,z5,z6])],[(0,[z0,z447,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z448]),(0,[z0,z1,z2,z3,z32,z19,z6]),(0,[z0,z1,z2,z3,z5,z297,z150]),(0,[z0,z1,z2,z3,z5,z6,z449])],[(0,[z0,z450,z1,z2,z3,z5,z6]),(1,[z0,z128,z2,z3,z59,z6]),(0,[z0,z1,z2,z3,z451,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z452]),(0,[z263,z0,z1,z2,z3,z5,z6]),(0,[z453,z0,z1,z2,z3,z5,z6]),(0,[z0,z454,z1,z2,z3,z5,z6])],[(0,[z0,z1,z455,z2,z3,z5,z6]),(0,[z445,z0,z1,z2,z3,z5,z6]),(0,[z456,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z314,z95,z6]),(0,[z0,z1,z2,z3,z5,z48,z6]),(0,[z0,z1,z2,z457,z3,z5,z6]),(0,[z0,z1,z2,z458,z11,z5,z6]),(1,[z0,z1,z182,z3,z5,z6]),(0,[z0,z459,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z32,z126])]],
   [[(0,[z0,z1,z460,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z46,z5,z6]),(0,[z0,z1,z2,z3,z5,z461,z6]),(0,[z0,z1,z2,z462,z3,z5,z6]),(0,[z0,z1,z39,z2,z3,z5,z6]),(0,[z0,z1,z39,z2,z3,z5,z83]),(0,[z0,z1,z2,z3,z463,z5,z6])],[(0,[z0,z1,z2,z3,z334,z5,z6]),(0,[z0,z1,z2,z11,z5,z6,z72]),(0,[z0,z1,z2,z3,z149,z5,z6]),(0,[z0,z1,z2,z11,z5,z130,z6]),(0,[z0,z1,z2,z12,z70,z5,z6]),(0,[z464,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z39,z3,z152,z5,z6]),(0,[z0,z1,z39,z2,z85,z5,z6]),(0,[z0,z1,z2,z3,z5,z465,z6])],[(0,[z466,z0,z1,z2,z3,z5,z6]),(0,[z0,z467,z1,z2,z3,z5,z6]),(0,[z0,z468,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z22])],[(0,[z56,z0,z35,z2,z3,z5,z6]),(0,[z144,z0,z1,z2,z3,z5,z45]),(0,[z13,z155,z1,z2,z3,z5,z6]),(0,[z0,z86,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z469,z6]),(0,[z0,z1,z2,z3,z5,z470,z6]),(0,[z0,z1,z29,z2,z3,z95,z6]),(0,[z0,z471,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z5,z6,z472])],[(0,[z0,z1,z2,z473,z3,z5,z6]),(0,[z0,z474,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z475,z6]),(0,[z0,z1,z2,z3,z5,z33,z150]),(0,[z0,z1,z2,z3,z476,z5,z6]),(0,[z0,z1,z2,z3,z477,z5,z6]),(0,[z0,z178,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z11,z5,z129,z6]),(0,[z0,z1,z2,z11,z152,z5,z6]),(0,[z0,z1,z2,z12,z5,z95,z6]),(0,[z0,z1,z2,z3,z5,z478,z6])],[(0,[z144,z1,z2,z58,z3,z5,z6]),(1,[z0,z1,z2,z412,z5,z6]),(0,[z0,z1,z2,z3,z479,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z480]),(0,[z0,z1,z2,z3,z32,z5,z126])]],
   [[(0,[z56,z0,z2,z3,z59,z5,z6]),(1,[z0,z1,z2,z121,z5,z6]),(0,[z0,z1,z2,z481,z3,z5,z6]),(0,[z1,z2,z3,z314,z5,z19,z6]),(0,[z0,z34,z1,z79,z3,z5,z6]),(0,[z0,z482,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z358,z6]),(0,[z0,z483,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z126,z6])],[(0,[z0,z1,z484,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z361])],[(1,[z0,z1,z2,z444,z5,z6]),(0,[z485,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z70,z5,z6,z22])],[(0,[z0,z1,z486,z2,z3,z5,z6]),(1,[z0,z1,z2,z235,z5,z6]),(0,[z0,z1,z2,z487,z3,z5,z6]),(0,[z199,z155,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z130,z72]),(0,[z0,z488,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z489]),(0,[z199,z0,z1,z2,z3,z32,z6])],[(1,[z144,z0,z1,z11,z5,z6]),(0,[z0,z490,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z491,z5,z6]),(0,[z0,z1,z2,z3,z492,z5,z6]),(0,[z0,z1,z2,z493,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z6,z163]),(0,[z0,z1,z2,z3,z5,z494,z6])],[(0,[z144,z0,z1,z10,z3,z5,z6]),(0,[z0,z1,z2,z17,z5,z6,z22]),(0,[z495,z0,z1,z2,z3,z5,z6]),(0,[z0,z34,z1,z2,z12,z5,z6]),(0,[z0,z2,z21,z3,z43,z5,z6]),(0,[z0,z1,z29,z3,z11,z5,z6]),(0,[z0,z96,z1,z3,z5,z95,z6]),(0,[z0,z38,z1,z2,z3,z5,z150]),(0,[z0,z1,z2,z3,z5,z496,z6])],[(0,[z0,z1,z2,z497,z3,z5,z6]),(0,[z0,z1,z2,z3,z498,z5,z6]),(0,[z499,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z21,z5,z6])],[(0,[z190,z1,z10,z2,z3,z5,z6]),(0,[z0,z500,z1,z2,z3,z5,z6]),(0,[z0,z501,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z502,z6]),(0,[z0,z1,z2,z12,z5,z6,z150])]],
   [[(0,[z0,z503,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z504]),(0,[z0,z1,z2,z3,z5,z6,z505])],[(0,[z0,z1,z2,z506,z3,z5,z6]),(0,[z0,z1,z2,z3,z507,z5,z6]),(1,[z0,z1,z2,z508,z5,z6]),(0,[z0,z509,z1,z2,z3,z5,z6]),(0,[z0,z71,z1,z2,z3,z5,z357]),(0,[z0,z135,z1,z2,z3,z5,z72]),(0,[z0,z1,z2,z3,z5,z510,z6]),(0,[z0,z1,z2,z12,z382,z5,z6])],[(0,[z0,z1,z2,z3,z5,z511,z6]),(0,[z0,z1,z2,z3,z5,z6,z512]),(0,[z0,z1,z2,z3,z5,z6,z513])],[(0,[z0,z1,z57,z2,z11,z5,z6]),(0,[z0,z1,z57,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z514,z5,z6]),(0,[z122,z0,z1,z2,z11,z5,z6]),(0,[z122,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z515,z3,z5,z6]),(0,[z0,z128,z2,z3,z59,z5,z6]),(0,[z0,z1,z2,z516,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z6,z22])],[(0,[z0,z1,z377,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z83,z297]),(0,[z0,z517,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z518,z6]),(1,[z0,z2,z3,z5,z6,z137])],[(1,[z0,z1,z2,z3,z209,z6]),(0,[z144,z0,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z519]),(0,[z289,z0,z1,z2,z70,z5,z6]),(0,[z16,z0,z181,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z520,z6]),(0,[z0,z521,z1,z2,z3,z5,z6]),(0,[z122,z0,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z3,z5,z6,z150])],[(0,[z0,z1,z2,z522,z3,z5,z6]),(0,[z523,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z59,z5,z6]),(0,[z0,z1,z2,z524,z3,z5,z6]),(0,[z199,z0,z1,z2,z3,z5,z126]),(1,[z0,z1,z257,z3,z5,z6])]],
   [[(0,[z0,z525,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z391,z5,z6])],[(0,[z88,z0,z1,z2,z11,z5,z6]),(0,[z88,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z526,z5,z6]),(0,[z144,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z94,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z126,z6])],[(0,[z144,z0,z1,z3,z152,z5,z6]),(0,[z527,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z528,z5,z6]),(1,[z0,z2,z3,z5,z151,z6]),(1,[z0,z1,z112,z11,z5,z6]),(0,[z0,z1,z79,z39,z3,z5,z6]),(0,[z0,z1,z529,z2,z3,z5,z6]),(0,[z530,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z217,z3,z5,z6])],[(0,[z122,z0,z1,z2,z3,z59,z6]),(0,[z0,z1,z2,z3,z5,z357,z6]),(0,[z0,z96,z1,z2,z73,z5,z6]),(0,[z0,z38,z1,z2,z531,z5,z6])],[(0,[z88,z0,z1,z2,z3,z5,z6]),(0,[z88,z122,z0,z2,z3,z5,z6])],[(0,[z0,z135,z2,z3,z59,z5,z6]),(0,[z0,z1,z2,z427,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z532,z6]),(0,[z0,z1,z2,z11,z5,z494,z6])],[(0,[z0,z1,z2,z3,z5,z533,z6]),(0,[z0,z1,z2,z3,z306,z5,z6]),(0,[z0,z2,z3,z43,z5,z6,z72]),(0,[z0,z534,z1,z2,z3,z5,z6])],[(0,[z0,z535,z1,z2,z3,z5,z6]),(0,[z13,z199,z0,z1,z2,z3,z5]),(0,[z0,z63,z1,z104,z3,z5,z6]),(0,[z0,z1,z2,z3,z536,z5,z6]),(0,[z0,z1,z2,z537,z3,z5,z6]),(0,[z0,z538,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z531,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z539])]],
   [[(0,[z56,z35,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z540,z6]),(0,[z0,z1,z2,z3,z5,z541,z6]),(0,[z0,z1,z2,z3,z5,z542,z6]),(0,[z0,z2,z3,z5,z357,z6,z72]),(0,[z0,z1,z2,z12,z5,z6,z72]),(0,[z0,z1,z2,z11,z5,z502,z6]),(0,[z0,z1,z2,z12,z5,z130,z6])],[(1,[z0,z63,z2,z43,z5,z6]),(1,[z0,z86,z1,z2,z5,z22])],[(0,[z543,z0,z1,z2,z3,z5,z6]),(0,[z155,z0,z1,z2,z3,z5,z33]),(0,[z0,z171,z2,z112,z3,z5,z6]),(0,[z0,z63,z1,z2,z43,z5,z6]),(0,[z544,z0,z1,z2,z3,z5,z6]),(0,[z0,z181,z1,z2,z3,z107,z6]),(0,[z0,z1,z2,z545,z3,z5,z6])],[(0,[z0,z546,z1,z2,z3,z5,z6]),(0,[z13,z0,z1,z2,z12,z5,z6]),(0,[z547,z0,z1,z2,z3,z5,z6]),(0,[z0,z63,z2,z3,z43,z5,z6]),(0,[z548,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z115,z3,z70,z6])],[(0,[z0,z1,z2,z3,z314,z6,z163]),(0,[z0,z1,z2,z3,z5,z549,z6]),(0,[z0,z187,z1,z2,z3,z5,z6]),(0,[z0,z1,z550,z2,z3,z5,z6])],[(0,[z0,z1,z551,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z129,z6]),(0,[z0,z71,z1,z2,z427,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z552]),(0,[z0,z1,z2,z531,z3,z5,z6]),(0,[z0,z1,z2,z3,z553,z5,z6])],[(0,[z0,z1,z2,z3,z554,z5,z6]),(0,[z0,z1,z2,z555,z3,z5,z6]),(1,[z190,z0,z1,z11,z5,z6]),(0,[z556,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z64]),(0,[z0,z1,z2,z5,z262,z129,z6]),(0,[z0,z1,z2,z557,z12,z5,z6]),(0,[z558,z0,z1,z2,z12,z5,z6])],[(0,[z88,z56,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z559,z3,z5,z6]),(0,[z0,z63,z1,z2,z11,z5,z6]),(0,[z0,z63,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z83,z72]),(0,[z0,z181,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z560,z6]),(0,[z190,z0,z1,z3,z152,z5,z6]),(0,[z0,z561,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z472])],[(0,[z0,z1,z2,z12,z17,z5,z6]),(0,[z0,z1,z2,z3,z5,z562,z6]),(1,[z13,z1,z2,z3,z5,z33]),(0,[z0,z1,z2,z3,z5,z563,z6]),(0,[z0,z564,z1,z2,z3,z5,z6]),(0,[z558,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z154,z6])],[(1,[z218,z1,z2,z3,z19,z6]),(0,[z0,z63,z1,z2,z3,z5,z6]),(1,[z122,z0,z2,z3,z129,z6])],[(0,[z0,z96,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z565]),(0,[z0,z1,z2,z3,z5,z6,z566])],[(0,[z0,z567,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z568,z6]),(0,[z0,z1,z2,z11,z5,z357,z6]),(0,[z0,z1,z2,z3,z569,z5,z6])],[(0,[z144,z0,z1,z2,z3,z5,z204]),(0,[z0,z1,z570,z2,z3,z5,z6]),(0,[z571,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z572,z5,z6]),(0,[z0,z573,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z19,z95,z6]),(0,[z13,z0,z1,z2,z3,z5,z297]),(0,[z0,z1,z2,z3,z574,z5,z6]),(0,[z0,z1,z2,z21,z11,z5,z6]),(0,[z0,z1,z2,z115,z11,z5,z6])],[(0,[z0,z1,z2,z575,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z576,z6])]],
   [[(0,[z0,z1,z2,z577,z3,z5,z6]),(0,[z144,z0,z215,z2,z3,z5,z6]),(0,[z289,z1,z2,z3,z17,z5,z6]),(0,[z243,z0,z1,z2,z3,z5,z19]),(0,[z0,z1,z2,z3,z5,z578,z6]),(0,[z0,z579,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z87,z5,z130,z6])],[(0,[z0,z1,z2,z21,z3,z5,z6]),(0,[z0,z580,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z152,z5,z95,z6]),(0,[z0,z38,z1,z3,z5,z6,z150]),(0,[z0,z1,z2,z115,z3,z5,z6])],[(0,[z581,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z22]),(1,[z0,z228,z2,z3,z5,z6])],[(1,[z0,z171,z112,z3,z5,z6]),(0,[z582,z0,z1,z2,z3,z5,z6]),(0,[z583,z0,z1,z2,z3,z5,z6]),(0,[z0,z584,z1,z2,z3,z5,z6]),(0,[z585,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z73,z3,z5,z6]),(1,[z0,z408,z2,z3,z5,z6])],[(0,[z0,z1,z2,z58,z11,z5,z6]),(0,[z0,z1,z2,z58,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z586]),(0,[z0,z1,z587,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z588,z6]),(1,[z0,z178,z2,z3,z5,z6]),(1,[z0,z1,z589,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z590])],[(0,[z0,z1,z2,z3,z591,z5,z6]),(0,[z0,z1,z592,z2,z3,z5,z6]),(0,[z593,z0,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z2,z3,z152,z6])],[(0,[z144,z0,z1,z2,z3,z231,z6]),(1,[z0,z360,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z297,z6]),(0,[z594,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z240,z3,z5,z6]),(0,[z0,z1,z2,z3,z595,z5,z6])],[(0,[z144,z190,z1,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z11,z5,z6])]],
   [[(0,[z0,z596,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z5,z126,z6])],[(0,[z0,z1,z597,z2,z3,z5,z6]),(0,[z0,z1,z598,z2,z3,z5,z6]),(0,[z0,z599,z1,z2,z12,z5,z6])],[(0,[z0,z215,z1,z2,z3,z5,z6]),(0,[z16,z289,z1,z2,z3,z5,z6]),(0,[z16,z0,z1,z2,z3,z5,z6]),(0,[z600,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z412,z5,z6]),(0,[z0,z601,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z59,z5,z6,z72]),(0,[z0,z602,z1,z2,z11,z5,z6]),(0,[z0,z96,z1,z2,z145,z5,z6])],[(0,[z0,z1,z2,z603,z3,z5,z6]),(0,[z0,z1,z2,z3,z604,z5,z6]),(0,[z0,z1,z2,z3,z605,z5,z6]),(0,[z0,z599,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z161,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z606]),(0,[z0,z1,z607,z2,z3,z5,z6])],[(1,[z185,z1,z2,z3,z314,z6]),(0,[z0,z1,z2,z3,z14,z5,z6]),(0,[z0,z1,z2,z3,z608,z5,z6])],[(0,[z0,z1,z2,z3,z314,z5,z6]),(0,[z155,z1,z2,z3,z5,z297,z6]),(0,[z0,z171,z1,z2,z3,z5,z568]),(0,[z0,z1,z2,z112,z11,z5,z6]),(0,[z0,z1,z2,z112,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z609,z6]),(0,[z0,z602,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z610,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z163])],[(1,[z0,z1,z79,z11,z5,z6]),(1,[z0,z318,z2,z3,z5,z6])]],
   [[(0,[z0,z360,z1,z2,z3,z5,z6]),(0,[z13,z1,z2,z3,z5,z6,z33]),(0,[z0,z1,z2,z3,z611,z5,z6]),(0,[z0,z2,z3,z59,z5,z129,z6]),(0,[z0,z1,z29,z2,z12,z5,z6])],[(0,[z612,z0,z1,z2,z3,z5,z6]),(0,[z0,z82,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z11,z24,z5,z6]),(1,[z0,z1,z2,z3,z5,z74]),(0,[z199,z0,z1,z2,z3,z5,z163]),(0,[z613,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z614,z5,z6]),(0,[z0,z1,z2,z3,z5,z615,z6]),(0,[z0,z1,z207,z39,z3,z5,z6]),(0,[z0,z38,z1,z2,z61,z5,z6])],[(0,[z88,z0,z2,z3,z59,z5,z6]),(0,[z0,z1,z2,z616,z3,z5,z6]),(1,[z0,z1,z3,z295,z5,z6]),(0,[z0,z617,z1,z2,z3,z5,z6]),(0,[z0,z38,z1,z2,z11,z5,z6]),(0,[z0,z38,z1,z2,z12,z5,z6])],[(0,[z618,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z619,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z620,z6]),(0,[z0,z1,z2,z131,z12,z5,z6]),(0,[z0,z86,z1,z2,z5,z6,z22]),(0,[z0,z1,z2,z87,z3,z5,z130])],[(0,[z0,z1,z2,z3,z47,z5,z6]),(0,[z0,z1,z2,z3,z508,z5,z6]),(0,[z0,z1,z621,z2,z3,z5,z6]),(0,[z0,z1,z622,z2,z3,z5,z6]),(0,[z623,z0,z1,z2,z3,z5,z6])],[(0,[z0,z624,z1,z2,z3,z5,z6]),(0,[z625,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z626,z3,z5,z6]),(0,[z122,z0,z2,z3,z5,z6,z72]),(0,[z0,z1,z2,z3,z5,z130,z357]),(1,[z0,z1,z11,z5,z6,z150]),(0,[z0,z38,z1,z2,z3,z5,z6]),(0,[z0,z38,z1,z2,z3,z5,z83])],[(0,[z0,z1,z2,z11,z5,z297,z6]),(0,[z0,z71,z1,z94,z3,z5,z6]),(1,[z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z627,z5,z6])]],
   [[(0,[z0,z1,z2,z628,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z357,z22]),(0,[z0,z1,z2,z3,z629,z5,z6]),(0,[z0,z1,z630,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z631])],[(0,[z0,z1,z2,z3,z632,z5,z6]),(0,[z144,z0,z1,z207,z3,z5,z6]),(0,[z0,z633,z1,z2,z3,z5,z6]),(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z635])],[(0,[z16,z0,z1,z2,z70,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z636]),(0,[z0,z1,z2,z255,z3,z5,z6]),(0,[z0,z1,z3,z5,z126,z6,z472])],[(0,[z637,z0,z1,z2,z3,z5,z6]),(0,[z122,z0,z2,z3,z5,z129,z6]),(0,[z0,z1,z2,z3,z638,z5,z6]),(0,[z0,z1,z2,z12,z5,z357,z6]),(0,[z0,z1,z2,z3,z5,z284,z6]),(0,[z0,z639,z1,z2,z3,z5,z6])],[(0,[z640,z0,z1,z2,z3,z5,z6]),(1,[z0,z160,z1,z2,z5,z6]),(0,[z0,z135,z1,z2,z3,z5,z357]),(0,[z0,z641,z1,z2,z3,z5,z6]),(1,[z0,z1,z251,z3,z5,z6]),(0,[z0,z1,z589,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z642]),(0,[z0,z1,z2,z3,z5,z643,z6]),(0,[z185,z1,z2,z3,z314,z5,z6]),(0,[z0,z1,z2,z43,z5,z6,z22]),(0,[z0,z1,z2,z3,z5,z6,z644])],[(0,[z0,z645,z1,z2,z3,z5,z6]),(0,[z122,z0,z135,z2,z3,z5,z6]),(0,[z0,z1,z646,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z608,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z647]),(0,[z0,z1,z2,z11,z314,z5,z6]),(0,[z0,z648,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z216,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z649,z6]),(0,[z0,z1,z2,z3,z5,z83,z6]),(0,[z0,z1,z2,z3,z650,z5,z6])]],
   [[(0,[z122,z0,z34,z2,z3,z5,z6]),(0,[z0,z34,z1,z2,z11,z5,z6]),(0,[z485,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z651]),(0,[z0,z1,z2,z3,z5,z652,z6])],[(0,[z0,z653,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z654]),(0,[z0,z655,z1,z2,z3,z5,z6]),(0,[z0,z135,z2,z3,z5,z357,z6])],[(0,[z0,z1,z656,z2,z3,z5,z6]),(0,[z0,z1,z657,z2,z3,z5,z6])],[(0,[z0,z57,z2,z3,z5,z6,z72]),(0,[z0,z1,z2,z3,z658,z5,z6]),(1,[z0,z1,z90,z3,z5,z6]),(0,[z13,z0,z1,z2,z3,z48,z6]),(0,[z0,z34,z1,z2,z3,z5,z6]),(0,[z180,z0,z1,z2,z11,z5,z6]),(1,[z0,z244,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z347,z6]),(0,[z0,z1,z2,z3,z5,z107,z6])],[(0,[z0,z1,z659,z2,z3,z5,z6]),(0,[z0,z1,z2,z610,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z660,z6]),(1,[z0,z210,z2,z3,z5,z6])],[(0,[z661,z0,z1,z2,z3,z5,z6]),(0,[z0,z662,z1,z2,z3,z5,z6]),(0,[z185,z0,z1,z2,z11,z5,z6]),(0,[z185,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z5,z663,z6]),(0,[z0,z1,z664,z2,z3,z5,z6]),(0,[z665,z0,z1,z2,z3,z5,z6]),(0,[z0,z71,z1,z2,z391,z5,z6]),(0,[z0,z23,z1,z3,z11,z5,z6])],[(0,[z0,z1,z2,z666,z3,z5,z6]),(0,[z0,z2,z3,z5,z151,z19,z6]),(0,[z0,z171,z1,z79,z3,z5,z6])],[(0,[z190,z0,z1,z207,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z667])]],
   [[(0,[z144,z0,z1,z2,z330,z5,z6]),(0,[z0,z1,z2,z3,z5,z5,z6])],[(0,[z0,z1,z57,z2,z3,z5,z6]),(0,[z144,z0,z1,z2,z334,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z668]),(0,[z0,z1,z2,z3,z669,z5,z6]),(0,[z0,z1,z2,z3,z670,z5,z6]),(0,[z155,z0,z1,z2,z3,z5,z297]),(0,[z0,z1,z2,z3,z5,z6,z671])],[(0,[z0,z1,z2,z3,z5,z672,z6]),(1,[z144,z1,z58,z3,z5,z6]),(0,[z673,z0,z1,z2,z3,z5,z6]),(0,[z674,z0,z1,z2,z3,z5,z6]),(0,[z0,z96,z1,z39,z3,z5,z6]),(1,[z0,z1,z2,z217,z5,z6])],[(0,[z0,z135,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z675,z6]),(0,[z0,z171,z1,z2,z11,z5,z6]),(0,[z0,z171,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z3,z676,z5,z6]),(0,[z0,z1,z2,z3,z5,z677,z6]),(1,[z0,z1,z29,z11,z5,z6]),(0,[z0,z1,z39,z3,z5,z83,z6]),(0,[z0,z1,z2,z70,z5,z107,z6]),(0,[z0,z1,z2,z424,z3,z5,z6]),(0,[z0,z2,z3,z5,z126,z6,z137])],[(0,[z0,z1,z2,z3,z5,z678,z6])],[(0,[z0,z1,z2,z3,z5,z679,z6]),(0,[z0,z1,z680,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z681,z5,z6])],[(0,[z0,z171,z1,z2,z3,z5,z6]),(0,[z682,z0,z1,z2,z3,z5,z6]),(1,[z0,z82,z2,z21,z5,z6])],[(0,[z0,z1,z10,z3,z5,z6,z150]),(0,[z218,z0,z1,z2,z11,z5,z6]),(0,[z218,z0,z1,z2,z12,z5,z6]),(0,[z0,z160,z1,z2,z5,z19,z6]),(0,[z0,z1,z683,z2,z3,z5,z6]),(0,[z684,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z207,z112,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z83,z6]),(0,[z0,z1,z182,z2,z3,z5,z6])],[(0,[z0,z685,z1,z2,z3,z5,z6]),(0,[z225,z0,z1,z2,z11,z5,z6])],[(0,[z0,z1,z686,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z350,z19]),(0,[z0,z1,z2,z355,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z83,z357]),(0,[z0,z1,z2,z3,z458,z5,z6])],[(0,[z0,z1,z2,z3,z5,z687,z6]),(0,[z0,z1,z2,z3,z5,z6,z33]),(0,[z0,z1,z2,z3,z5,z688,z6]),(0,[z689,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z690,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z107,z6]),(0,[z0,z1,z691,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z152,z314,z6]),(0,[z0,z1,z112,z3,z11,z5,z6]),(0,[z0,z1,z2,z3,z692,z5,z6])],[(0,[z13,z0,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z12,z5,z297,z6]),(0,[z0,z693,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z595,z5,z6]),(0,[z0,z1,z408,z2,z3,z5,z6])],[(0,[z1,z10,z2,z58,z3,z5,z6]),(0,[z0,z1,z2,z3,z295,z5,z6]),(0,[z0,z694,z1,z2,z3,z5,z6]),(0,[z695,z0,z1,z2,z3,z5,z6]),(0,[z0,z86,z1,z589,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z696]),(0,[z0,z697,z1,z2,z3,z5,z6]),(0,[z0,z1,z79,z2,z444,z5,z6]),(0,[z0,z1,z2,z12,z152,z5,z6]),(1,[z0,z1,z29,z3,z152,z6]),(0,[z0,z181,z1,z2,z5,z6,z22]),(0,[z0,z1,z2,z3,z5,z698,z6])],[(0,[z13,z0,z1,z2,z3,z5,z6]),(0,[z699,z0,z1,z2,z3,z5,z6])],[(0,[z190,z0,z1,z58,z3,z5,z6]),(0,[z0,z1,z2,z3,z700,z5,z6]),(0,[z0,z1,z2,z12,z115,z5,z6]),(0,[z0,z86,z1,z424,z3,z5,z6])],[(0,[z701,z0,z1,z2,z3,z5,z6]),(0,[z0,z702,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z350]),(0,[z0,z1,z2,z3,z30,z5,z6])],[(0,[z0,z1,z2,z557,z3,z5,z6])],[(0,[z144,z0,z377,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z152,z19,z6]),(0,[z0,z1,z2,z3,z18,z5,z6]),(1,[z0,z1,z2,z3,z5,z568]),(0,[z0,z703,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z87,z5,z6])],[(0,[z0,z1,z2,z12,z314,z5,z6]),(0,[z13,z0,z156,z2,z3,z5,z6]),(0,[z9,z0,z1,z2,z11,z5,z6]),(0,[z9,z0,z1,z2,z12,z5,z6]),(0,[z0,z1,z2,z12,z5,z6,z163])],[(0,[z704,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z705]),(0,[z0,z1,z79,z2,z508,z5,z6]),(0,[z706,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z115,z3,z107,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z6]),(0,[z0,z708,z2,z3,z5,z6]),(0,[z0,z1,z11,z5,z383,z6]),(0,[z0,z1,z251,z11,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z2,z12,z5,z151,z6]),(0,[z0,z1,z345,z11,z5,z6]),(0,[z0,z1,z3,z709,z5,z6])],[(0,[z122,z0,z2,z3,z520,z6]),(0,[z0,z1,z430,z11,z5,z6]),(0,[z0,z1,z2,z85,z5,z6]),(0,[z0,z38,z1,z61,z5,z150]),(0,[z0,z1,z710,z3,z5,z6])],[(0,[z122,z0,z2,z3,z672,z6]),(0,[z289,z0,z1,z47,z5,z6]),(0,[z0,z711,z2,z3,z5,z6]),(0,[z0,z156,z2,z11,z5,z6]),(0,[z0,z156,z2,z12,z5,z6]),(0,[z0,z1,z712,z3,z5,z6]),(0,[z0,z38,z1,z11,z5,z150]),(0,[z0,z1,z251,z3,z5,z6]),(0,[z0,z396,z1,z11,z5,z6]),(0,[z0,z38,z1,z12,z5,z150])],[(0,[z0,z1,z2,z3,z5,z713]),(0,[z0,z1,z2,z714,z5,z6]),(0,[z0,z1,z2,z3,z32,z461]),(1,[z1,z2,z3,z5,z715]),(0,[z0,z716,z2,z3,z5,z6]),(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z1,z718,z3,z5,z6])],[(0,[z0,z62,z2,z235,z5,z6]),(0,[z0,z1,z2,z719,z5,z6]),(0,[z0,z1,z2,z5,z6,z720]),(0,[z0,z1,z2,z161,z5,z74])],[(0,[z0,z156,z2,z3,z5,z6]),(0,[z0,z1,z2,z12,z14,z6]),(0,[z0,z1,z2,z3,z5,z721]),(0,[z0,z1,z444,z11,z5,z6]),(0,[z0,z82,z2,z3,z5,z64]),(0,[z0,z1,z435,z11,z5,z6]),(0,[z0,z38,z1,z3,z5,z150]),(0,[z0,z38,z1,z3,z5,z722])],[(0,[z0,z1,z2,z3,z5,z723]),(0,[z0,z724,z2,z3,z5,z6]),(0,[z225,z1,z2,z24,z5,z6]),(0,[z0,z244,z2,z11,z5,z6])]],
   [[(0,[z144,z0,z377,z11,z5,z6]),(0,[z0,z1,z2,z3,z231,z45]),(0,[z0,z725,z2,z3,z5,z6]),(0,[z0,z726,z2,z3,z5,z6]),(0,[z0,z1,z11,z5,z6,z224]),(0,[z0,z1,z727,z3,z5,z6])],[(0,[z0,z1,z10,z3,z5,z204]),(0,[z728,z1,z2,z3,z5,z6]),(0,[z0,z1,z228,z2,z5,z22])],[(0,[z0,z1,z90,z3,z5,z6]),(0,[z223,z0,z2,z18,z5,z6]),(0,[z0,z1,z112,z300,z5,z6]),(0,[z0,z244,z2,z3,z5,z6]),(0,[z0,z1,z462,z11,z5,z6])],[(0,[z15,z1,z2,z3,z19,z6]),(0,[z13,z1,z355,z3,z5,z33]),(0,[z0,z351,z1,z11,z5,z6]),(0,[z0,z210,z2,z3,z5,z6]),(0,[z0,z220,z2,z21,z5,z6]),(0,[z0,z1,z2,z5,z729,z6]),(0,[z0,z1,z2,z3,z5,z722]),(0,[z0,z181,z1,z182,z107,z6]),(0,[z0,z1,z730,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z731])],[(0,[z0,z1,z2,z330,z209,z6]),(0,[z0,z1,z2,z732,z5,z6]),(0,[z0,z1,z733,z11,z5,z6]),(0,[z0,z2,z37,z161,z5,z6]),(0,[z0,z1,z29,z30,z152,z6])],[(0,[z0,z1,z2,z334,z209,z6]),(0,[z144,z1,z58,z330,z5,z6]),(0,[z225,z190,z1,z11,z5,z6]),(0,[z0,z2,z3,z59,z734,z6]),(0,[z0,z1,z94,z735,z5,z6]),(0,[z0,z736,z2,z3,z5,z6]),(0,[z0,z181,z1,z2,z737,z6])],[(0,[z0,z1,z3,z5,z738,z6]),(0,[z0,z739,z1,z2,z5,z6]),(0,[z218,z1,z2,z3,z740,z6]),(0,[z0,z1,z2,z741,z5,z6]),(0,[z0,z1,z345,z3,z152,z6]),(0,[z0,z1,z2,z161,z5,z6])],[(0,[z0,z1,z227,z11,z5,z6]),(0,[z0,z1,z355,z306,z5,z6]),(0,[z0,z1,z117,z742,z5,z6])]],
   [[(0,[z190,z1,z10,z12,z5,z6]),(0,[z0,z2,z3,z59,z6,z272]),(0,[z0,z1,z2,z743,z5,z6]),(0,[z0,z1,z3,z152,z744,z6]),(0,[z0,z1,z745,z3,z5,z6])],[(0,[z0,z1,z2,z145,z5,z6]),(0,[z0,z1,z3,z5,z722,z150])],[(0,[z0,z1,z2,z3,z5,z746]),(0,[z0,z1,z2,z11,z5,z204]),(0,[z0,z1,z2,z12,z5,z204]),(0,[z0,z1,z2,z747,z5,z6]),(0,[z0,z1,z2,z5,z748,z6]),(0,[z0,z749,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z750]),(0,[z0,z751,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z752]),(0,[z0,z1,z753,z3,z5,z6]),(0,[z0,z754,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z755,z6]),(0,[z0,z617,z1,z11,z5,z6]),(0,[z0,z2,z3,z5,z6,z756]),(0,[z0,z1,z217,z5,z6,z472])],[(0,[z0,z1,z2,z3,z5,z204]),(0,[z0,z215,z2,z11,z5,z6]),(0,[z0,z215,z2,z12,z5,z6]),(0,[z0,z757,z1,z2,z5,z6]),(0,[z0,z1,z111,z3,z48,z6]),(0,[z0,z374,z112,z11,z5,z6]),(0,[z0,z1,z2,z758,z5,z6])],[(0,[z0,z400,z1,z3,z5,z150]),(0,[z0,z1,z2,z759,z5,z6]),(0,[z0,z228,z2,z3,z5,z22])],[(0,[z0,z760,z2,z3,z5,z6]),(0,[z0,z1,z2,z761,z5,z6]),(0,[z0,z2,z342,z3,z59,z6]),(0,[z0,z2,z3,z762,z5,z6]),(0,[z0,z1,z2,z742,z5,z6]),(0,[z0,z244,z2,z161,z5,z6]),(0,[z0,z2,z763,z3,z5,z6])]],
   [[(0,[z0,z215,z2,z3,z5,z6]),(0,[z0,z764,z2,z3,z5,z6]),(0,[z223,z0,z2,z11,z5,z6]),(0,[z223,z0,z2,z12,z5,z6]),(0,[z0,z374,z112,z3,z5,z6]),(0,[z0,z765,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z698,z22])],[(0,[z0,z1,z766,z3,z5,z6]),(0,[z0,z767,z2,z3,z5,z6]),(0,[z190,z1,z3,z233,z5,z6]),(0,[z0,z1,z2,z768,z5,z6]),(0,[z0,z408,z39,z3,z5,z6])],[(0,[z0,z1,z769,z3,z5,z6]),(0,[z770,z0,z2,z3,z5,z6]),(0,[z0,z63,z240,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z771]),(0,[z0,z1,z11,z5,z446,z6]),(1,[z0,z1,z2,z3,z772]),(0,[z0,z1,z257,z5,z6,z259])],[(0,[z223,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z231,z6]),(0,[z0,z1,z2,z12,z231,z6]),(0,[z0,z1,z2,z5,z6,z773]),(0,[z0,z1,z2,z11,z5,z7]),(0,[z0,z1,z2,z12,z5,z7]),(0,[z0,z1,z11,z5,z6,z449]),(0,[z0,z181,z1,z2,z107,z6])],[(0,[z0,z1,z2,z11,z774,z6]),(0,[z0,z1,z29,z11,z5,z347]),(0,[z0,z1,z29,z11,z152,z6])],[(0,[z0,z1,z11,z314,z95,z6])],[(0,[z0,z1,z2,z3,z231,z6]),(0,[z0,z1,z2,z27,z5,z568]),(0,[z775,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z776,z5,z6]),(0,[z0,z777,z2,z3,z5,z6]),(0,[z0,z207,z37,z3,z5,z6]),(0,[z0,z181,z178,z2,z107,z6])],[(0,[z0,z377,z3,z11,z5,z6]),(0,[z0,z778,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z779]),(0,[z0,z1,z2,z3,z774,z6]),(0,[z0,z1,z29,z3,z152,z6]),(0,[z0,z2,z3,z5,z6,z780]),(0,[z781,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z171,z112,z300,z5,z6]),(0,[z0,z135,z2,z3,z5,z677]),(0,[z199,z0,z1,z2,z11,z163]),(0,[z0,z1,z2,z782,z5,z6])],[(0,[z0,z377,z2,z3,z209,z6]),(0,[z0,z783,z2,z3,z5,z6]),(0,[z0,z579,z112,z3,z5,z6]),(0,[z0,z2,z3,z5,z305,z72]),(0,[z0,z1,z61,z5,z6,z150]),(1,[z0,z1,z2,z5,z731])],[(0,[z0,z1,z11,z5,z469,z6]),(0,[z0,z2,z3,z5,z6,z784]),(0,[z0,z1,z2,z5,z6,z785]),(0,[z0,z82,z1,z251,z5,z6]),(0,[z0,z786,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z787,z6]),(0,[z223,z0,z160,z2,z5,z6]),(0,[z0,z788,z1,z2,z5,z6]),(0,[z0,z82,z2,z5,z576,z6]),(0,[z0,z181,z178,z2,z5,z6]),(0,[z0,z2,z789,z3,z5,z6])],[(0,[z0,z1,z790,z3,z5,z6]),(0,[z0,z1,z791,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z792]),(0,[z0,z1,z2,z793,z5,z6]),(0,[z0,z1,z3,z5,z6,z794]),(0,[z0,z1,z2,z795,z5,z6])],[(0,[z0,z1,z796,z3,z5,z6]),(0,[z0,z664,z112,z3,z5,z6]),(0,[z0,z187,z1,z2,z5,z6]),(0,[z0,z1,z39,z3,z5,z344]),(0,[z0,z1,z2,z5,z130,z731])],[(0,[z0,z57,z112,z11,z5,z6]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z0,z1,z2,z798,z5,z6]),(0,[z0,z1,z2,z799,z5,z6]),(0,[z0,z1,z2,z3,z5,z800]),(0,[z0,z1,z94,z391,z5,z6]),(0,[z0,z96,z1,z73,z95,z6]),(0,[z0,z801,z2,z3,z5,z6]),(0,[z0,z1,z424,z87,z5,z6])]],
   [[(0,[z0,z1,z111,z11,z5,z6]),(0,[z0,z1,z111,z12,z5,z6]),(0,[z0,z1,z207,z3,z5,z74]),(0,[z802,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z803,z5,z6]),(0,[z0,z1,z2,z804,z5,z6]),(0,[z0,z805,z1,z2,z3,z5]),(0,[z185,z1,z2,z3,z740,z6]),(0,[z0,z63,z2,z43,z5,z64]),(0,[z0,z1,z2,z87,z5,z663]),(0,[z0,z1,z2,z3,z5,z806]),(0,[z0,z23,z1,z11,z5,z6]),(0,[z0,z1,z2,z255,z5,z6])],[(0,[z0,z1,z294,z11,z5,z6]),(0,[z0,z112,z458,z11,z5,z6]),(0,[z0,z1,z776,z11,z5,z6]),(0,[z0,z1,z607,z11,z5,z6])],[(0,[z0,z1,z2,z3,z5,z807]),(0,[z0,z1,z111,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z45]),(1,[z1,z808,z3,z5,z6]),(0,[z0,z1,z809,z3,z5,z6]),(0,[z0,z810,z1,z295,z5,z6]),(0,[z0,z197,z1,z11,z5,z6]),(0,[z0,z1,z207,z733,z5,z6]),(0,[z0,z1,z2,z811,z5,z6]),(0,[z0,z1,z2,z5,z6,z812])],[(0,[z0,z215,z2,z3,z5,z204]),(0,[z0,z112,z11,z5,z6,z72]),(0,[z0,z813,z1,z2,z5,z6]),(0,[z0,z1,z814,z3,z5,z6]),(0,[z0,z71,z117,z3,z5,z72]),(0,[z0,z1,z2,z815,z5,z6]),(0,[z0,z125,z2,z12,z5,z6]),(0,[z0,z1,z29,z161,z152,z6])],[(0,[z0,z816,z1,z2,z5,z6]),(0,[z0,z2,z817,z3,z5,z6]),(0,[z0,z1,z2,z818,z5,z6]),(0,[z0,z1,z39,z11,z5,z6]),(0,[z0,z1,z39,z11,z5,z83]),(0,[z0,z1,z39,z12,z5,z83])],[(0,[z0,z1,z2,z3,z5,z819]),(0,[z0,z1,z2,z5,z6,z820]),(0,[z0,z1,z2,z821,z5,z6]),(0,[z0,z1,z2,z3,z5,z45]),(0,[z0,z1,z2,z822,z5,z6]),(0,[z0,z1,z2,z823,z5,z6]),(0,[z0,z1,z207,z12,z5,z6])],[(0,[z0,z1,z2,z3,z5,z824]),(0,[z0,z1,z47,z5,z6,z22]),(0,[z0,z1,z79,z300,z5,z6]),(0,[z0,z210,z424,z3,z5,z6])]],
   [[(0,[z0,z156,z111,z3,z5,z6]),(0,[z0,z1,z355,z235,z5,z6]),(0,[z0,z34,z2,z3,z5,z103]),(0,[z0,z1,z147,z11,z5,z6]),(0,[z122,z0,z2,z3,z620,z6]),(0,[z0,z825,z2,z12,z5,z6]),(0,[z0,z1,z3,z5,z744,z6])],[(0,[z0,z826,z2,z3,z5,z6]),(0,[z0,z1,z559,z11,z5,z6]),(0,[z0,z1,z2,z827,z5,z6]),(0,[z0,z828,z1,z2,z5,z6]),(0,[z0,z1,z829,z3,z5,z6])],[(0,[z0,z1,z2,z3,z231,z204]),(0,[z0,z830,z2,z3,z5,z6]),(0,[z0,z1,z2,z831,z5,z6]),(0,[z0,z63,z2,z514,z5,z6])],[(0,[z1,z832,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z833]),(0,[z0,z825,z2,z3,z5,z6]),(0,[z0,z1,z2,z32,z126,z259])],[(0,[z0,z192,z1,z11,z5,z6]),(0,[z289,z162,z1,z2,z5,z6]),(0,[z0,z1,z2,z5,z6,z834]),(0,[z0,z1,z355,z3,z5,z297]),(0,[z0,z71,z2,z3,z5,z72]),(0,[z0,z96,z1,z11,z95,z6]),(0,[z0,z86,z210,z2,z5,z22])],[(0,[z0,z215,z2,z3,z231,z6]),(0,[z0,z1,z330,z11,z5,z6]),(0,[z289,z0,z1,z251,z5,z6]),(0,[z0,z1,z835,z3,z5,z6]),(0,[z0,z1,z2,z836,z5,z6]),(0,[z0,z1,z646,z11,z5,z6]),(0,[z0,z1,z3,z5,z6,z837])],[(0,[z439,z1,z58,z3,z5,z6]),(0,[z0,z1,z2,z838,z5,z6]),(0,[z0,z839,z1,z2,z11,z6]),(0,[z0,z602,z1,z11,z95,z6])],[(0,[z0,z2,z3,z59,z549,z6]),(0,[z0,z1,z712,z5,z129,z6]),(0,[z0,z1,z39,z11,z5,z150]),(0,[z0,z96,z1,z3,z95,z6]),(0,[z0,z1,z2,z87,z5,z40]),(0,[z0,z86,z228,z2,z5,z22])]],
   [[(0,[z0,z1,z2,z840,z5,z6]),(0,[z0,z1,z2,z841,z5,z6]),(0,[z0,z112,z3,z5,z6,z103]),(0,[z0,z1,z646,z3,z5,z83]),(0,[z0,z1,z842,z3,z5,z6]),(0,[z0,z1,z2,z843,z5,z6])],[(0,[z0,z535,z2,z3,z5,z72]),(0,[z289,z1,z2,z17,z5,z6]),(0,[z0,z1,z2,z844,z5,z6]),(0,[z0,z1,z2,z3,z5,z103]),(0,[z0,z1,z413,z12,z5,z6]),(0,[z0,z1,z117,z11,z5,z6]),(0,[z0,z273,z1,z11,z5,z150]),(0,[z0,z602,z1,z3,z95,z6])],[(0,[z0,z1,z577,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z845]),(0,[z0,z1,z846,z3,z5,z6]),(0,[z0,z1,z847,z3,z5,z6]),(0,[z122,z0,z187,z2,z129,z6]),(0,[z0,z1,z94,z427,z5,z6]),(0,[z0,z1,z11,z5,z6,z361]),(0,[z0,z1,z11,z5,z6,z362]),(0,[z0,z1,z39,z3,z5,z722])],[(0,[z0,z1,z2,z3,z5,z848]),(0,[z0,z1,z2,z3,z849,z6]),(0,[z386,z1,z2,z3,z314,z6]),(0,[z0,z1,z2,z5,z262,z6]),(0,[z0,z2,z3,z5,z734,z6]),(0,[z0,z1,z11,z5,z532,z6]),(0,[z0,z1,z2,z30,z5,z347]),(0,[z0,z1,z3,z5,z6,z850])],[(0,[z243,z0,z1,z2,z18,z5]),(0,[z0,z1,z2,z3,z32,z48]),(0,[z0,z1,z117,z3,z5,z6]),(0,[z0,z1,z407,z11,z5,z6]),(0,[z0,z1,z3,z152,z5,z74])],[(0,[z13,z1,z2,z306,z5,z33]),(0,[z0,z851,z1,z2,z5,z6])],[(0,[z0,z270,z112,z3,z5,z6]),(0,[z439,z1,z2,z3,z5,z33]),(0,[z0,z1,z2,z11,z5,z852]),(0,[z0,z1,z207,z161,z5,z6])],[(0,[z243,z0,z1,z2,z11,z5]),(0,[z0,z125,z2,z217,z5,z6])]],
   [[(0,[z0,z1,z2,z330,z5,z6]),(0,[z144,z0,z1,z412,z5,z6]),(0,[z0,z1,z2,z853,z5,z6]),(0,[z0,z1,z2,z854,z5,z6]),(0,[z0,z181,z1,z240,z5,z6]),(0,[z0,z1,z240,z12,z5,z6]),(0,[z0,z1,z855,z3,z5,z6]),(0,[z0,z1,z257,z3,z32,z126])],[(0,[z0,z62,z2,z12,z5,z6]),(0,[z199,z0,z1,z355,z3,z5]),(0,[z0,z96,z1,z3,z744,z6]),(0,[z0,z38,z318,z3,z5,z150])],[(0,[z0,z1,z2,z5,z856,z6]),(0,[z0,z96,z1,z3,z209,z6]),(0,[z289,z1,z2,z857,z5,z6]),(0,[z0,z1,z2,z857,z5,z6]),(0,[z0,z2,z3,z5,z858,z6])],[(0,[z144,z190,z1,z11,z5,z6]),(0,[z0,z1,z859,z3,z5,z6]),(0,[z0,z1,z11,z5,z357,z150])],[(0,[z0,z1,z860,z3,z5,z6]),(0,[z0,z1,z251,z5,z6,z22])],[(0,[z0,z1,z2,z861,z5,z6]),(0,[z0,z215,z2,z3,z5,z45]),(0,[z0,z1,z2,z862,z5,z6]),(0,[z0,z1,z207,z3,z5,z204])],[(0,[z0,z1,z39,z3,z5,z675]),(0,[z0,z1,z570,z11,z5,z6]),(0,[z0,z1,z863,z3,z5,z6]),(0,[z0,z1,z864,z11,z5,z6]),(0,[z0,z1,z2,z87,z5,z130])],[(0,[z218,z360,z1,z3,z19,z6]),(0,[z0,z1,z11,z5,z562,z6]),(0,[z0,z2,z3,z5,z6,z865]),(0,[z0,z1,z355,z866,z5,z6]),(0,[z0,z1,z104,z3,z5,z64]),(0,[z0,z71,z2,z3,z5,z867]),(0,[z0,z353,z2,z3,z5,z72]),(0,[z0,z374,z2,z608,z5,z6]),(0,[z0,z1,z2,z610,z5,z130]),(0,[z0,z96,z1,z145,z95,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z868]),(0,[z199,z0,z1,z2,z3,z163])],[(0,[z0,z1,z90,z330,z5,z6]),(0,[z0,z1,z2,z11,z14,z6]),(0,[z0,z1,z570,z3,z5,z83]),(0,[z0,z1,z2,z3,z5,z869]),(0,[z0,z135,z2,z12,z5,z357]),(0,[z0,z1,z2,z12,z5,z870])],[(0,[z0,z1,z2,z871,z5,z6]),(0,[z0,z1,z11,z5,z6,z204]),(0,[z0,z1,z2,z43,z5,z64]),(1,[z0,z2,z762,z5,z6]),(0,[z0,z1,z2,z872,z5,z6]),(0,[z0,z37,z3,z11,z5,z6])],[(0,[z0,z1,z2,z3,z873,z6]),(0,[z0,z1,z874,z3,z5,z6]),(0,[z0,z2,z3,z43,z5,z64]),(0,[z0,z1,z2,z875,z5,z6]),(0,[z0,z1,z2,z11,z5,z347]),(0,[z0,z1,z2,z12,z5,z347])],[(0,[z144,z0,z1,z11,z209,z6]),(0,[z0,z1,z2,z3,z14,z6]),(0,[z0,z360,z3,z5,z151,z6]),(0,[z0,z400,z1,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z870]),(0,[z0,z1,z457,z11,z5,z6]),(0,[z0,z1,z2,z5,z6,z876]),(0,[z0,z2,z37,z3,z5,z347])],[(0,[z0,z1,z2,z3,z5,z877]),(0,[z13,z483,z1,z2,z3,z5]),(0,[z0,z277,z112,z3,z5,z6]),(0,[z0,z63,z1,z251,z5,z6]),(0,[z0,z1,z2,z5,z6,z259])],[(0,[z0,z1,z2,z878,z5,z6]),(0,[z0,z1,z2,z879,z5,z6]),(0,[z0,z1,z2,z3,z5,z347])],[(0,[z0,z1,z2,z880,z5,z6]),(0,[z0,z181,z1,z2,z620,z6]),(0,[z0,z1,z2,z11,z5,z64]),(0,[z0,z1,z2,z12,z5,z64]),(0,[z0,z881,z2,z11,z5,z6]),(0,[z0,z1,z2,z882,z5,z6]),(0,[z0,z1,z424,z131,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z883,z6]),(0,[z20,z57,z2,z3,z5,z6]),(0,[z0,z360,z160,z1,z5,z6]),(0,[z0,z884,z2,z3,z5,z6]),(0,[z0,z228,z424,z3,z5,z6])],[(0,[z144,z1,z58,z334,z5,z6]),(0,[z0,z156,z2,z3,z14,z6]),(0,[z0,z1,z885,z3,z5,z6]),(0,[z0,z1,z595,z11,z5,z6])],[(0,[z0,z1,z628,z11,z5,z6]),(0,[z0,z377,z2,z12,z5,z6]),(0,[z0,z1,z3,z47,z5,z6]),(0,[z0,z1,z2,z3,z5,z64]),(0,[z122,z0,z2,z3,z5,z64]),(0,[z0,z128,z2,z3,z734,z6]),(0,[z0,z881,z2,z3,z5,z6])],[(0,[z0,z1,z886,z3,z5,z6]),(0,[z0,z1,z2,z3,z887,z6]),(0,[z190,z1,z10,z11,z5,z6]),(0,[z0,z1,z11,z5,z6,z418]),(0,[z0,z1,z2,z888,z5,z6])],[(0,[z0,z1,z2,z330,z5,z204]),(0,[z0,z1,z3,z11,z209,z6]),(0,[z0,z889,z2,z3,z5,z6]),(0,[z218,z1,z3,z295,z19,z6]),(0,[z243,z0,z1,z2,z3,z48]),(0,[z0,z1,z2,z3,z5,z715]),(0,[z0,z1,z2,z3,z5,z890]),(0,[z122,z0,z2,z262,z129,z6]),(0,[z0,z1,z891,z3,z5,z6]),(0,[z0,z1,z39,z795,z5,z6]),(0,[z0,z1,z255,z11,z5,z6])],[(0,[z0,z63,z2,z595,z5,z6]),(0,[z0,z2,z3,z5,z867,z72])],[(0,[z190,z1,z10,z3,z5,z6]),(0,[z0,z1,z2,z892,z5,z6]),(1,[z1,z2,z3,z740,z6]),(0,[z0,z160,z2,z5,z151,z6]),(0,[z0,z1,z2,z893,z5,z6]),(0,[z0,z1,z104,z3,z5,z7]),(0,[z0,z82,z2,z458,z5,z6]),(0,[z0,z187,z2,z59,z5,z6]),(0,[z0,z181,z1,z2,z284,z6]),(0,[z0,z2,z5,z6,z137,z259]),(0,[z0,z1,z257,z894,z5,z6])],[(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z215,z2,z330,z5,z6]),(0,[z144,z1,z58,z3,z209,z6]),(0,[z0,z187,z1,z712,z5,z6]),(0,[z0,z1,z2,z12,z5,z896]),(0,[z0,z244,z2,z3,z5,z347])]],
   [[(0,[z689,z57,z2,z3,z5,z6]),(0,[z0,z702,z1,z3,z5,z150]),(0,[z0,z1,z11,z5,z426,z6]),(0,[z0,z1,z39,z255,z5,z83]),(0,[z0,z897,z2,z3,z5,z6])],[(0,[z88,z832,z2,z3,z5,z6]),(0,[z0,z1,z3,z152,z5,z204]),(0,[z0,z1,z355,z3,z48,z6]),(0,[z0,z693,z112,z3,z5,z6]),(0,[z0,z1,z2,z898,z5,z6]),(0,[z0,z1,z2,z762,z5,z6]),(0,[z0,z1,z630,z11,z5,z6]),(0,[z0,z1,z207,z255,z5,z6])],[(0,[z190,z0,z1,z412,z5,z6]),(0,[z0,z899,z2,z3,z5,z6]),(0,[z0,z1,z2,z300,z5,z568]),(0,[z900,z1,z2,z3,z5,z6]),(0,[z122,z0,z187,z2,z5,z6])],[(0,[z0,z1,z2,z901,z5,z6]),(0,[z0,z1,z2,z902,z5,z6]),(0,[z0,z1,z903,z3,z5,z6]),(0,[z0,z63,z2,z605,z5,z6]),(0,[z0,z1,z2,z161,z5,z347]),(0,[z0,z904,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z905]),(0,[z0,z171,z863,z3,z5,z6]),(0,[z0,z395,z1,z2,z5,z22]),(1,[z0,z1,z712,z5,z6]),(0,[z0,z1,z906,z3,z5,z6])],[(0,[z0,z1,z2,z907,z5,z6]),(0,[z0,z1,z2,z330,z231,z6]),(0,[z218,z160,z1,z2,z19,z6]),(0,[z155,z1,z2,z11,z5,z297]),(0,[z155,z1,z2,z12,z5,z297]),(0,[z0,z1,z529,z11,z5,z6])],[(0,[z13,z1,z2,z235,z5,z33]),(0,[z0,z1,z11,z5,z297,z150]),(0,[z0,z839,z1,z2,z3,z6]),(0,[z908,z1,z2,z3,z5,z6]),(0,[z122,z0,z2,z3,z254,z6]),(0,[z0,z1,z2,z5,z6,z909]),(0,[z0,z86,z1,z2,z5,z731]),(0,[z0,z1,z3,z32,z126,z472])],[(0,[z0,z1,z2,z3,z5,z910]),(0,[z0,z1,z2,z911,z5,z6]),(0,[z0,z912,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z913]),(0,[z0,z1,z914,z3,z5,z6]),(0,[z0,z915,z1,z2,z5,z6]),(0,[z0,z1,z271,z11,z5,z6]),(0,[z0,z1,z11,z5,z6,z452]),(0,[z0,z468,z1,z11,z5,z6]),(0,[z0,z1,z2,z916,z5,z6])]],
   [[(0,[z0,z1,z917,z3,z5,z6]),(0,[z155,z1,z2,z3,z5,z297]),(0,[z0,z1,z2,z3,z5,z918]),(0,[z199,z0,z1,z11,z5,z150])],[(0,[z0,z1,z919,z3,z5,z6]),(0,[z0,z920,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z7]),(0,[z0,z921,z2,z3,z5,z6])],[(0,[z13,z1,z2,z3,z5,z715]),(0,[z0,z1,z2,z922,z5,z6])],[(0,[z1,z10,z808,z3,z5,z6]),(0,[z218,z243,z1,z2,z3,z19]),(0,[z0,z1,z111,z844,z5,z6]),(0,[z594,z0,z1,z11,z5,z6]),(0,[z0,z1,z240,z557,z5,z6]),(1,[z0,z2,z3,z5,z867]),(0,[z0,z1,z2,z923,z5,z6]),(0,[z0,z1,z2,z924,z5,z6])],[(0,[z925,z1,z2,z3,z5,z6]),(0,[z0,z2,z391,z5,z6,z72])],[(0,[z0,z1,z3,z5,z6,z926]),(0,[z144,z377,z58,z3,z5,z6]),(0,[z0,z1,z424,z11,z5,z6]),(0,[z0,z1,z424,z12,z5,z6])],[(0,[z0,z1,z2,z927,z5,z6]),(0,[z1,z808,z58,z3,z5,z6]),(0,[z0,z1,z11,z5,z33,z150]),(0,[z0,z112,z11,z59,z5,z6]),(0,[z0,z1,z2,z928,z5,z6]),(0,[z0,z929,z2,z12,z5,z6]),(0,[z0,z1,z2,z930,z5,z6]),(0,[z0,z1,z3,z5,z649,z150]),(0,[z0,z1,z3,z5,z83,z722])],[(0,[z0,z1,z2,z3,z931,z6]),(0,[z0,z1,z2,z3,z5,z932]),(0,[z0,z933,z2,z3,z5,z6]),(0,[z243,z0,z1,z2,z3,z5]),(0,[z0,z2,z3,z5,z6,z934]),(0,[z0,z1,z2,z935,z5,z6]),(0,[z0,z353,z2,z43,z5,z6]),(0,[z0,z241,z1,z2,z5,z22]),(0,[z0,z135,z2,z3,z5,z867]),(0,[z706,z0,z1,z11,z5,z6]),(0,[z0,z1,z936,z3,z5,z6])]],
   [[(0,[z0,z1,z619,z12,z5,z6]),(0,[z0,z82,z2,z158,z5,z6]),(0,[z0,z1,z424,z3,z5,z6]),(0,[z0,z2,z217,z5,z6,z137])],[(0,[z445,z1,z2,z216,z5,z6]),(0,[z0,z1,z2,z3,z6,z772])],[(0,[z0,z1,z2,z937,z5,z6]),(0,[z0,z160,z1,z295,z5,z6]),(0,[z0,z2,z3,z5,z154,z6]),(0,[z0,z938,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z32,z489]),(0,[z0,z86,z1,z589,z5,z22])],[(0,[z0,z360,z1,z3,z95,z6]),(0,[z0,z1,z2,z427,z5,z6]),(0,[z0,z332,z2,z458,z5,z6]),(0,[z0,z1,z610,z11,z5,z150]),(0,[z0,z2,z939,z3,z5,z6]),(0,[z0,z1,z3,z32,z5,z472])],[(0,[z0,z1,z355,z11,z5,z6]),(0,[z0,z1,z355,z12,z5,z6]),(0,[z0,z1,z2,z940,z5,z6]),(0,[z0,z1,z2,z5,z941,z6]),(0,[z0,z1,z196,z11,z95,z6]),(0,[z0,z1,z11,z5,z6,z489]),(0,[z0,z86,z1,z2,z5,z361]),(0,[z0,z1,z29,z3,z152,z347])],[(0,[z0,z1,z2,z330,z5,z45]),(0,[z0,z599,z2,z557,z5,z6]),(0,[z0,z96,z1,z3,z5,z74]),(0,[z0,z228,z2,z5,z6,z22])],[(0,[z132,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z334,z5,z45]),(0,[z0,z181,z1,z2,z687,z6]),(0,[z0,z1,z942,z3,z5,z6]),(0,[z0,z1,z2,z943,z5,z6]),(0,[z0,z1,z11,z5,z496,z6]),(0,[z0,z2,z3,z5,z944,z6])],[(0,[z50,z0,z1,z11,z5,z6]),(0,[z0,z945,z2,z3,z5,z6]),(0,[z0,z1,z355,z3,z5,z6]),(0,[z0,z1,z2,z300,z5,z103]),(0,[z0,z128,z2,z11,z59,z6]),(0,[z0,z128,z2,z12,z59,z6]),(0,[z0,z125,z2,z11,z5,z6]),(0,[z0,z1,z39,z61,z5,z6]),(0,[z0,z228,z2,z3,z5,z130]),(0,[z0,z210,z589,z3,z5,z6]),(0,[z0,z2,z3,z32,z126,z137])]],
   [[(0,[z0,z1,z2,z3,z5,z946]),(0,[z243,z0,z360,z1,z3,z5]),(0,[z0,z1,z2,z947,z5,z6]),(0,[z0,z1,z2,z11,z32,z126]),(0,[z0,z1,z2,z12,z32,z126]),(0,[z0,z1,z182,z12,z5,z6])],[(1,[z0,z377,z11,z5,z6]),(0,[z0,z62,z2,z3,z48,z6]),(0,[z0,z181,z1,z2,z5,z64]),(0,[z0,z1,z2,z712,z5,z6])],[(0,[z0,z948,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z740,z6]),(0,[z0,z135,z2,z3,z5,z93]),(0,[z0,z125,z2,z3,z5,z6]),(0,[z0,z2,z3,z734,z129,z6]),(0,[z0,z1,z2,z3,z5,z867]),(0,[z0,z1,z11,z5,z660,z6]),(0,[z0,z1,z2,z5,z6,z949]),(0,[z950,z0,z2,z12,z5,z6]),(0,[z0,z2,z12,z5,z858,z6])],[(0,[z218,z1,z2,z3,z350,z19]),(0,[z0,z1,z951,z3,z5,z6]),(0,[z0,z1,z2,z391,z5,z72]),(0,[z0,z1,z11,z5,z6,z513]),(0,[z0,z1,z39,z3,z5,z83]),(0,[z0,z1,z2,z952,z5,z6]),(0,[z0,z1,z2,z87,z5,z731])],[(0,[z0,z953,z2,z3,z5,z6]),(0,[z0,z1,z954,z3,z5,z6]),(0,[z0,z156,z355,z3,z5,z6]),(0,[z0,z2,z3,z391,z5,z72]),(0,[z0,z1,z39,z85,z5,z83])],[(0,[z466,z0,z1,z11,z5,z6]),(0,[z445,z0,z1,z47,z5,z6]),(0,[z0,z127,z1,z11,z5,z6]),(0,[z950,z0,z2,z3,z5,z6]),(0,[z0,z1,z2,z955,z5,z6])],[(0,[z0,z360,z1,z3,z209,z6]),(0,[z0,z1,z2,z5,z956,z6]),(0,[z0,z1,z3,z5,z6,z957]),(0,[z0,z1,z111,z3,z14,z6]),(0,[z0,z1,z11,z5,z518,z6]),(0,[z0,z1,z2,z27,z5,z103]),(0,[z0,z1,z557,z11,z5,z6]),(0,[z0,z1,z958,z3,z5,z6]),(0,[z0,z1,z2,z959,z5,z6])],[(0,[z0,z1,z960,z3,z5,z6]),(0,[z1,z2,z857,z3,z5,z6]),(0,[z0,z1,z2,z961,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z962]),(0,[z0,z1,z3,z5,z6,z472])],[(0,[z0,z1,z5,z6,z472,z259])],[(0,[z0,z1,z486,z11,z5,z6]),(0,[z0,z1,z348,z11,z5,z6]),(0,[z0,z1,z2,z300,z5,z6]),(0,[z0,z2,z863,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z963])],[(0,[z0,z1,z808,z3,z5,z6]),(0,[z0,z1,z2,z964,z5,z6]),(0,[z0,z1,z2,z3,z5,z965]),(0,[z0,z1,z664,z11,z5,z6]),(0,[z0,z2,z11,z5,z154,z6])],[(0,[z0,z1,z2,z966,z5,z6]),(0,[z0,z408,z2,z531,z5,z6]),(0,[z0,z1,z251,z115,z5,z6])],[(0,[z0,z534,z2,z43,z5,z6]),(0,[z0,z967,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z963])],[(0,[z0,z1,z968,z3,z5,z6]),(0,[z969,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z70,z102,z6]),(0,[z0,z1,z2,z3,z5,z970]),(0,[z0,z1,z240,z43,z5,z6]),(1,[z0,z2,z43,z5,z64]),(0,[z0,z1,z971,z3,z5,z6]),(0,[z0,z972,z2,z3,z5,z6]),(0,[z0,z181,z2,z154,z107,z6])],[(0,[z832,z57,z2,z3,z5,z6]),(0,[z973,z0,z1,z2,z3,z6]),(0,[z144,z0,z1,z974,z5,z6]),(0,[z0,z1,z3,z11,z5,z74]),(0,[z0,z273,z1,z3,z5,z150]),(0,[z0,z1,z251,z87,z5,z6])]],
   [[(0,[z0,z1,z2,z975,z5,z6]),(0,[z0,z1,z377,z11,z5,z6]),(0,[z243,z0,z2,z3,z5,z151]),(0,[z0,z525,z1,z3,z5,z150]),(0,[z0,z1,z182,z161,z5,z6])],[(0,[z0,z1,z2,z27,z5,z6]),(0,[z0,z1,z2,z735,z5,z6]),(0,[z0,z1,z2,z976,z5,z6]),(0,[z0,z977,z2,z3,z5,z6]),(0,[z0,z584,z1,z11,z5,z6])],[(0,[z0,z377,z2,z3,z5,z45]),(0,[z0,z978,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z625,z0,z1,z11,z5,z6]),(0,[z0,z1,z52,z11,z5,z6])],[(0,[z0,z1,z2,z980,z5,z6]),(0,[z1,z2,z3,z740,z19,z6]),(0,[z0,z1,z2,z3,z5,z981]),(0,[z0,z1,z2,z982,z5,z6]),(0,[z0,z1,z240,z11,z5,z6]),(0,[z0,z1,z2,z3,z5,z983]),(0,[z0,z1,z39,z145,z5,z6]),(0,[z0,z1,z2,z217,z32,z126])],[(0,[z0,z1,z2,z3,z5,z984]),(0,[z0,z1,z2,z334,z5,z6]),(0,[z0,z1,z985,z3,z5,z6]),(0,[z0,z62,z2,z11,z5,z6]),(0,[z0,z63,z336,z2,z5,z6]),(0,[z0,z1,z2,z5,z986,z6]),(0,[z0,z1,z2,z987,z5,z6]),(0,[z0,z1,z2,z3,z5,z852]),(0,[z0,z1,z12,z627,z5,z6])],[(0,[z54,z1,z2,z17,z5,z6]),(0,[z0,z988,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z989]),(0,[z0,z1,z3,z733,z5,z6])],[(0,[z0,z1,z2,z990,z5,z6]),(0,[z223,z0,z360,z3,z5,z6]),(0,[z0,z1,z240,z3,z5,z6]),(0,[z122,z0,z240,z3,z5,z6]),(0,[z0,z1,z991,z3,z5,z6]),(0,[z0,z1,z2,z992,z5,z6])],[(0,[z0,z1,z2,z3,z5,z993]),(0,[z0,z62,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z209,z6]),(0,[z0,z1,z2,z12,z209,z6]),(0,[z0,z1,z412,z5,z6,z150]),(0,[z0,z1,z2,z994,z5,z6]),(0,[z13,z1,z2,z3,z48,z33]),(0,[z0,z171,z112,z3,z5,z568]),(0,[z0,z2,z3,z5,z6,z867]),(0,[z0,z1,z55,z12,z5,z6]),(0,[z199,z0,z1,z2,z3,z772])]],
   [[(0,[z0,z1,z2,z3,z5,z995]),(0,[z0,z1,z996,z3,z5,z6]),(0,[z0,z1,z378,z11,z5,z6]),(0,[z0,z360,z1,z3,z5,z350]),(0,[z0,z1,z257,z11,z5,z6]),(0,[z0,z1,z257,z12,z5,z6]),(0,[z997,z1,z2,z3,z5,z6]),(0,[z0,z318,z2,z531,z5,z6])],[(0,[z0,z1,z998,z3,z5,z6]),(0,[z0,z1,z2,z999,z5,z6]),(0,[z0,z1,z11,z5,z6,z472]),(0,[z0,z1,z161,z11,z5,z6]),(0,[z0,z1,z251,z407,z5,z6]),(0,[z0,z1,z2,z737,z107,z6]),(0,[z0,z1,z2,z894,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1000]),(0,[z0,z96,z1,z3,z5,z204]),(0,[z0,z63,z104,z43,z5,z6]),(0,[z0,z1,z94,z11,z5,z6]),(0,[z0,z1,z94,z12,z5,z6]),(0,[z0,z2,z3,z5,z357,z867]),(0,[z548,z0,z1,z3,z5,z150]),(0,[z0,z1,z2,z1001,z5,z6]),(0,[z0,z1,z2,z3,z1002,z6])],[(0,[z0,z1,z2,z306,z48,z6]),(0,[z0,z71,z2,z391,z5,z72])],[(0,[z0,z1,z2,z3,z5,z1003]),(0,[z0,z135,z2,z11,z5,z357])],[(0,[z1004,z0,z2,z3,z5,z6]),(0,[z0,z1005,z2,z3,z5,z6]),(0,[z225,z1,z2,z17,z5,z6]),(0,[z218,z1,z2,z18,z19,z6]),(0,[z0,z1,z1006,z295,z5,z6]),(0,[z0,z1,z94,z3,z5,z6]),(0,[z0,z1,z145,z5,z6,z150])],[(0,[z0,z1,z2,z1007,z5,z6]),(0,[z0,z1,z1008,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1009]),(0,[z0,z1,z2,z1010,z5,z6]),(0,[z0,z1,z112,z11,z5,z6]),(0,[z122,z0,z112,z11,z5,z6]),(0,[z0,z29,z37,z11,z5,z6]),(0,[z0,z257,z3,z5,z6,z137])],[(0,[z0,z1,z2,z3,z5,z1011]),(0,[z0,z1012,z1,z3,z5,z6]),(0,[z0,z1,z11,z19,z95,z6]),(0,[z0,z62,z2,z3,z14,z6]),(0,[z0,z135,z2,z3,z5,z357])]],
   [[(0,[z0,z1,z616,z11,z5,z6]),(0,[z0,z1,z29,z11,z95,z6]),(0,[z0,z2,z3,z5,z6,z1013]),(0,[z0,z228,z589,z3,z5,z6])],[(0,[z0,z1,z1014,z3,z5,z6]),(0,[z0,z1015,z2,z3,z5,z6]),(0,[z0,z1016,z2,z3,z5,z6])],[(0,[z0,z1017,z2,z3,z5,z6]),(0,[z0,z1,z1018,z3,z5,z6]),(0,[z0,z1,z87,z47,z5,z6]),(0,[z0,z1,z2,z1019,z5,z6]),(0,[z0,z1,z112,z85,z5,z6]),(0,[z0,z408,z3,z5,z6,z150]),(0,[z0,z181,z1,z251,z107,z6]),(0,[z0,z1020,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1021,z6]),(0,[z0,z1,z626,z11,z5,z6]),(0,[z0,z1,z3,z1022,z5,z6]),(0,[z0,z1,z39,z3,z5,z429]),(0,[z0,z1,z117,z391,z5,z6]),(0,[z0,z1,z1023,z3,z5,z6])],[(0,[z0,z1,z1024,z3,z5,z6]),(0,[z144,z0,z1,z11,z5,z204]),(0,[z144,z1,z587,z3,z5,z6]),(0,[z593,z0,z2,z3,z5,z72]),(0,[z0,z2,z21,z5,z201,z6]),(0,[z0,z1,z131,z11,z5,z6])],[(0,[z0,z377,z2,z11,z5,z6]),(0,[z0,z1,z2,z1025,z5,z6]),(0,[z0,z1,z3,z295,z5,z350]),(0,[z0,z1,z2,z3,z5,z1026]),(0,[z0,z1,z551,z11,z5,z6]),(0,[z0,z232,z1,z11,z5,z6]),(0,[z199,z0,z1,z2,z3,z631]),(0,[z0,z1,z251,z5,z107,z6]),(0,[z0,z1,z1027,z3,z5,z6]),(0,[z0,z86,z1,z2,z5,z22]),(0,[z0,z1,z2,z3,z772,z163])],[(0,[z0,z474,z1,z3,z5,z150]),(0,[z0,z1,z240,z70,z5,z6]),(0,[z0,z1,z1028,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1029]),(0,[z0,z181,z1,z2,z136,z6])],[(0,[z0,z1,z2,z3,z1030,z6]),(0,[z0,z1,z139,z11,z5,z6]),(0,[z258,z1,z10,z3,z5,z6]),(0,[z0,z1031,z2,z3,z5,z6]),(0,[z0,z1032,z2,z3,z5,z6])]],
   [[(0,[z0,z377,z2,z3,z5,z6]),(0,[z0,z1,z2,z334,z5,z204]),(0,[z0,z1,z2,z3,z1033,z6])],[(0,[z0,z1,z2,z1034,z5,z6]),(0,[z0,z1,z2,z1035,z5,z6]),(0,[z0,z1,z2,z3,z5,z1036]),(0,[z243,z223,z0,z2,z3,z5]),(0,[z0,z360,z1,z18,z5,z6]),(0,[z0,z1,z2,z1037,z5,z6]),(1,[z0,z94,z3,z5,z72]),(0,[z0,z1,z2,z1038,z5,z6])],[(0,[z190,z0,z1,z11,z5,z6]),(0,[z16,z0,z1,z251,z5,z6]),(0,[z13,z1,z2,z11,z5,z33]),(0,[z13,z1,z2,z12,z5,z33]),(0,[z0,z1,z2,z1039,z5,z6]),(0,[z0,z500,z1,z11,z5,z6])],[(0,[z0,z1,z1040,z3,z5,z6]),(0,[z0,z215,z2,z334,z5,z6]),(0,[z0,z1041,z2,z3,z5,z6]),(0,[z0,z1,z58,z3,z5,z204]),(0,[z218,z1,z2,z11,z19,z6]),(0,[z218,z1,z2,z12,z19,z6]),(0,[z1,z2,z3,z314,z740,z6]),(0,[z0,z1042,z1,z3,z5,z6]),(0,[z0,z1,z2,z391,z5,z6]),(0,[z122,z0,z2,z11,z129,z6]),(0,[z122,z0,z2,z12,z129,z6]),(0,[z0,z1043,z2,z3,z5,z6]),(0,[z0,z1,z257,z217,z5,z6])],[(0,[z0,z1,z18,z295,z5,z6]),(0,[z0,z171,z112,z3,z5,z103]),(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z2,z3,z126,z772])],[(0,[z144,z0,z1,z11,z231,z6]),(0,[z0,z1,z1045,z3,z5,z6]),(0,[z218,z223,z2,z3,z19,z6]),(0,[z13,z1,z2,z3,z5,z33]),(0,[z0,z1,z2,z3,z5,z896]),(0,[z0,z1,z29,z3,z744,z6]),(0,[z0,z1,z1046,z3,z5,z6])],[(0,[z0,z2,z3,z59,z133,z6]),(0,[z0,z1,z2,z3,z209,z204]),(0,[z218,z1,z2,z3,z19,z6]),(0,[z0,z160,z1,z2,z5,z350]),(0,[z122,z0,z2,z3,z129,z6]),(0,[z0,z71,z2,z427,z5,z72]),(0,[z0,z1,z2,z5,z1047,z6]),(0,[z0,z1,z1048,z3,z5,z6]),(0,[z0,z1,z5,z6,z472,z949])],[(0,[z0,z648,z2,z43,z5,z6]),(0,[z0,z1,z2,z1049,z5,z6])]],
   [[(0,[z0,z1,z2,z1050,z5,z6]),(0,[z0,z1,z1051,z3,z5,z6])],[(0,[z0,z215,z2,z3,z209,z6]),(0,[z0,z1,z2,z334,z231,z6]),(0,[z0,z1,z2,z306,z5,z6]),(0,[z695,z1,z2,z3,z5,z297])],[(0,[z0,z1,z1052,z3,z5,z6]),(0,[z13,z156,z2,z3,z5,z33]),(0,[z1,z2,z3,z5,z715,z33]),(0,[z0,z1,z94,z759,z5,z6]),(0,[z0,z1053,z2,z3,z5,z6])],[(0,[z0,z1,z240,z21,z5,z6]),(0,[z0,z1,z240,z3,z5,z7]),(0,[z122,z0,z2,z3,z734,z6]),(0,[z0,z1,z440,z11,z5,z6]),(0,[z0,z228,z2,z12,z5,z6]),(0,[z0,z408,z2,z61,z5,z6])],[(0,[z0,z1,z2,z1054,z5,z6]),(0,[z0,z1055,z2,z3,z5,z6]),(0,[z0,z171,z112,z11,z5,z6]),(0,[z0,z171,z112,z12,z5,z6]),(0,[z0,z1,z1056,z3,z5,z6]),(0,[z0,z1,z2,z1057,z5,z6]),(0,[z0,z1,z1058,z3,z5,z6]),(0,[z0,z408,z2,z11,z5,z6]),(0,[z0,z1,z39,z3,z5,z423]),(0,[z0,z408,z2,z12,z5,z6]),(0,[z0,z2,z3,z5,z6,z1059])],[(0,[z0,z270,z1,z11,z5,z6]),(0,[z0,z1060,z1,z2,z5,z6]),(0,[z0,z1061,z2,z3,z5,z6]),(0,[z0,z1062,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1063]),(0,[z0,z1,z2,z70,z5,z64]),(0,[z0,z1,z11,z5,z123,z6]),(0,[z0,z178,z2,z11,z5,z6]),(0,[z0,z1,z589,z11,z5,z6]),(0,[z0,z178,z2,z12,z5,z6]),(0,[z0,z1,z589,z12,z5,z6])],[(0,[z0,z1,z2,z3,z740,z6]),(0,[z243,z0,z1,z2,z3,z32]),(0,[z0,z156,z2,z306,z5,z6]),(0,[z0,z1,z117,z427,z5,z6]),(0,[z0,z1,z440,z3,z5,z83]),(0,[z0,z3,z5,z6,z137,z472])],[(0,[z78,z0,z1,z11,z5,z6]),(0,[z0,z360,z1,z11,z5,z6]),(0,[z0,z360,z1,z12,z5,z6]),(0,[z0,z171,z112,z3,z5,z6]),(0,[z0,z408,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1064,z6]),(1,[z0,z2,z391,z5,z72]),(0,[z0,z408,z2,z3,z5,z83]),(0,[z0,z1,z782,z5,z6,z472])]],
   [[(0,[z0,z1,z47,z11,z5,z6]),(0,[z0,z1,z94,z3,z5,z72]),(0,[z0,z1,z2,z1065,z5,z6]),(0,[z0,z1,z589,z3,z5,z6]),(0,[z0,z1,z12,z5,z6,z472]),(0,[z0,z228,z2,z87,z5,z6])],[(0,[z0,z1,z2,z1066,z5,z6]),(0,[z0,z1,z2,z306,z14,z6]),(0,[z0,z1,z2,z1067,z5,z6]),(0,[z1068,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z772])],[(0,[z0,z1069,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1070,z6]),(0,[z0,z1071,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z6,z1072]),(0,[z445,z0,z1,z11,z5,z6]),(0,[z16,z0,z1,z47,z5,z6]),(0,[z0,z94,z3,z5,z6,z72]),(0,[z0,z86,z1,z424,z5,z22]),(0,[z0,z1073,z2,z3,z5,z6]),(0,[z0,z1,z2,z5,z6,z1074])],[(0,[z0,z1,z3,z1075,z5,z6]),(0,[z0,z377,z2,z3,z5,z204]),(0,[z0,z1,z2,z235,z48,z6]),(0,[z0,z1,z79,z864,z5,z6]),(0,[z0,z579,z2,z3,z5,z72]),(0,[z0,z1,z11,z5,z284,z6]),(0,[z199,z0,z1,z2,z12,z163]),(0,[z0,z929,z2,z3,z5,z6]),(0,[z0,z1,z2,z1076,z5,z6]),(0,[z0,z1,z1077,z3,z5,z6])],[(0,[z0,z1,z1078,z3,z5,z6]),(0,[z144,z0,z1,z11,z5,z45]),(0,[z190,z0,z1,z145,z5,z6])],[(0,[z185,z1,z2,z11,z314,z6]),(0,[z185,z1,z2,z12,z314,z6]),(0,[z0,z1,z1079,z3,z5,z6]),(0,[z0,z1080,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1081,z6]),(0,[z0,z1,z2,z391,z5,z357]),(0,[z0,z602,z1,z2,z494,z6])],[(0,[z1,z2,z857,z17,z5,z6]),(0,[z0,z2,z3,z5,z151,z350]),(0,[z0,z135,z2,z3,z5,z303]),(0,[z0,z2,z43,z5,z72,z22]),(0,[z0,z1,z1082,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1083]),(0,[z485,z0,z1,z2,z284,z6]),(0,[z0,z318,z2,z61,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1084]),(0,[z0,z1,z2,z3,z1085,z6]),(0,[z0,z1,z11,z5,z6,z647]),(0,[z0,z318,z2,z11,z5,z6]),(0,[z0,z318,z2,z12,z5,z6])],[(0,[z185,z1,z2,z3,z314,z6]),(0,[z0,z62,z111,z3,z5,z6]),(0,[z499,z0,z2,z3,z5,z72]),(0,[z0,z408,z2,z3,z5,z150])],[(0,[z0,z1,z2,z3,z5,z1086]),(0,[z190,z1,z3,z149,z5,z6]),(0,[z0,z1,z2,z3,z5,z1087]),(0,[z0,z1,z2,z5,z1088,z6]),(0,[z0,z1,z2,z21,z5,z64]),(0,[z263,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z12,z5,z74])],[(0,[z0,z1,z207,z330,z5,z6]),(0,[z84,z1,z2,z3,z19,z6]),(0,[z243,z0,z160,z1,z2,z5]),(0,[z0,z1,z79,z11,z5,z6]),(0,[z0,z318,z2,z3,z5,z6]),(0,[z0,z1,z182,z11,z5,z6]),(0,[z0,z1,z29,z3,z629,z6])],[(0,[z0,z1,z2,z1089,z5,z6]),(0,[z0,z1,z2,z1090,z5,z6]),(0,[z0,z2,z3,z5,z1091,z6]),(0,[z155,z1,z2,z3,z5,z265]),(0,[z0,z1,z2,z1092,z5,z6])],[(0,[z0,z377,z2,z3,z231,z6]),(1,[z0,z1,z11,z209,z6]),(0,[z0,z360,z1,z732,z5,z6]),(0,[z243,z0,z1,z2,z3,z163]),(0,[z0,z2,z1093,z3,z5,z6]),(0,[z0,z2,z762,z43,z5,z6]),(0,[z0,z128,z2,z3,z59,z6]),(0,[z0,z1,z12,z733,z5,z6]),(0,[z0,z96,z1,z3,z660,z6])],[(0,[z0,z2,z18,z5,z151,z6]),(0,[z0,z1,z104,z444,z5,z6]),(0,[z0,z1,z182,z3,z5,z6]),(0,[z84,z0,z1,z11,z5,z6]),(0,[z0,z1,z11,z5,z179,z6]),(0,[z0,z1094,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z32,z126])],[(0,[z0,z1,z2,z3,z209,z45]),(0,[z0,z1,z3,z295,z5,z6]),(0,[z0,z1,z79,z85,z5,z6]),(0,[z0,z1,z117,z966,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z1095,z6]),(0,[z0,z1096,z2,z3,z5,z6]),(0,[z0,z645,z1,z3,z5,z150]),(0,[z0,z1,z1097,z3,z5,z6])],[(0,[z0,z1098,z1,z2,z5,z6]),(0,[z0,z1099,z1,z2,z3,z5]),(0,[z0,z1100,z2,z3,z5,z6]),(0,[z0,z79,z112,z11,z5,z6]),(0,[z0,z1,z2,z1101,z5,z6]),(0,[z0,z1,z2,z3,z5,z1102])],[(0,[z0,z1,z355,z3,z14,z6]),(1,[z0,z112,z3,z5,z103]),(0,[z0,z2,z112,z3,z5,z103]),(0,[z0,z1,z2,z87,z5,z358])],[(0,[z0,z1,z2,z1103,z5,z6]),(0,[z0,z1,z597,z11,z5,z6]),(0,[z0,z1,z2,z610,z5,z502])],[(0,[z1104,z0,z2,z3,z5,z6]),(0,[z0,z1105,z1,z2,z5,z6]),(0,[z0,z2,z3,z59,z5,z64]),(0,[z0,z1,z691,z12,z5,z6]),(0,[z0,z1,z2,z1106,z5,z6])],[(0,[z0,z1,z355,z880,z5,z6]),(0,[z0,z1,z355,z3,z32,z5]),(0,[z0,z1,z508,z5,z6,z150]),(0,[z0,z1,z308,z11,z5,z6]),(0,[z0,z1,z11,z5,z678,z6]),(0,[z0,z1,z251,z12,z5,z6])],[(0,[z0,z1107,z1,z3,z5,z6]),(0,[z0,z1,z2,z412,z5,z6]),(0,[z0,z1,z484,z11,z5,z6]),(0,[z0,z244,z2,z3,z5,z74]),(0,[z1108,z0,z1,z3,z5,z6]),(0,[z0,z125,z2,z5,z6,z259])],[(0,[z0,z1,z2,z121,z5,z6]),(0,[z0,z1,z2,z1109,z5,z6]),(0,[z0,z1,z2,z1110,z5,z6]),(0,[z0,z1,z2,z1111,z5,z6]),(0,[z0,z1,z2,z1112,z5,z6]),(1,[z0,z408,z3,z5,z150]),(0,[z0,z1113,z2,z3,z5,z6])]],
   [[(0,[z0,z160,z1,z2,z5,z6]),(0,[z0,z1,z3,z1114,z5,z6]),(0,[z0,z71,z94,z3,z5,z72])],[(0,[z0,z1115,z2,z3,z5,z6]),(0,[z0,z1,z2,z444,z5,z6]),(0,[z0,z277,z1,z3,z5,z150])],[(0,[z144,z1,z808,z3,z5,z6]),(0,[z0,z1,z2,z235,z5,z6]),(0,[z0,z273,z1,z2,z5,z202])],[(0,[z0,z1,z1116,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1117]),(0,[z144,z0,z1,z11,z5,z6]),(0,[z0,z3,z295,z5,z151,z6]),(0,[z0,z374,z2,z43,z5,z6])],[(0,[z0,z1,z90,z11,z5,z6]),(0,[z0,z1,z90,z12,z5,z6]),(0,[z0,z810,z1,z2,z5,z6]),(0,[z0,z244,z2,z12,z5,z6]),(0,[z0,z1,z2,z5,z731,z22])],[(0,[z0,z1,z12,z47,z5,z6]),(0,[z0,z1,z2,z3,z5,z1118]),(0,[z0,z135,z94,z3,z5,z6]),(0,[z0,z1,z53,z11,z5,z6]),(0,[z0,z210,z2,z11,z5,z6]),(0,[z0,z210,z2,z12,z5,z6])],[(0,[z0,z1,z2,z1119,z5,z6]),(0,[z0,z135,z112,z11,z5,z6]),(0,[z0,z1,z29,z11,z5,z74])],[(0,[z0,z1,z2,z1120,z5,z6]),(0,[z218,z2,z3,z151,z19,z6]),(0,[z0,z156,z2,z235,z5,z6]),(0,[z13,z1,z111,z3,z5,z33]),(0,[z0,z1,z2,z1121,z5,z6]),(0,[z0,z1,z2,z1122,z5,z6]),(0,[z0,z1,z145,z5,z95,z6]),(0,[z0,z1,z2,z1123,z5,z6])]],
   [[(0,[z0,z1,z1124,z3,z5,z6]),(0,[z0,z1,z2,z3,z1125,z6]),(0,[z0,z377,z207,z3,z5,z6]),(0,[z0,z1,z11,z295,z5,z6]),(0,[z0,z1,z2,z1126,z5,z6]),(0,[z0,z1,z2,z508,z5,z6]),(0,[z0,z517,z2,z3,z5,z357]),(0,[z0,z1,z37,z11,z5,z6]),(0,[z0,z1,z2,z5,z737,z6])],[(0,[z0,z1,z112,z3,z5,z103]),(0,[z0,z187,z1,z727,z5,z6]),(0,[z0,z1,z229,z11,z5,z6])],[(0,[z0,z1,z1127,z3,z5,z6]),(0,[z0,z2,z3,z5,z1128,z6]),(0,[z0,z1,z2,z235,z14,z6]),(0,[z0,z82,z2,z762,z5,z6]),(0,[z0,z2,z21,z762,z5,z6]),(0,[z0,z1,z1129,z3,z5,z6]),(0,[z0,z203,z1,z3,z5,z150])],[(0,[z144,z1,z58,z11,z5,z6]),(0,[z144,z1,z58,z12,z5,z6]),(0,[z243,z0,z1,z2,z12,z5]),(0,[z0,z1,z3,z5,z6,z1130]),(0,[z0,z1,z111,z306,z5,z6]),(0,[z0,z1,z2,z1131,z5,z6])],[(0,[z0,z1,z2,z3,z1132,z6]),(0,[z0,z1,z1133,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z137]),(0,[z0,z1,z795,z11,z5,z6]),(0,[z0,z1,z2,z3,z744,z6]),(0,[z0,z1,z2,z3,z1134,z6])],[(0,[z0,z1,z2,z3,z209,z6]),(0,[z0,z1,z2,z1135,z5,z6])],[(0,[z0,z1,z2,z3,z1136,z6]),(0,[z144,z1,z58,z3,z5,z6]),(0,[z0,z1,z3,z152,z209,z6]),(0,[z0,z1,z2,z18,z5,z350]),(0,[z0,z1,z2,z1137,z5,z6]),(0,[z0,z1,z257,z3,z5,z6]),(0,[z0,z1,z408,z3,z5,z150]),(0,[z0,z1,z2,z217,z5,z6])],[(0,[z0,z1,z3,z1138,z5,z6]),(0,[z0,z1,z2,z3,z5,z1139]),(0,[z0,z1,z2,z1140,z5,z6]),(0,[z0,z1,z29,z11,z5,z6]),(0,[z0,z38,z408,z3,z5,z150]),(0,[z0,z1,z3,z264,z5,z150])]],
   [[(0,[z0,z1,z974,z11,z5,z6]),(0,[z190,z1,z10,z412,z5,z6]),(0,[z0,z1141,z2,z3,z5,z6]),(0,[z0,z1,z1142,z3,z5,z6]),(0,[z0,z1,z589,z255,z5,z6])],[(0,[z0,z2,z3,z5,z151,z6]),(0,[z0,z1,z2,z1143,z5,z6]),(0,[z190,z1,z10,z121,z5,z6]),(0,[z223,z0,z3,z295,z5,z6]),(0,[z0,z1,z2,z1144,z5,z6])],[(0,[z0,z1,z2,z1145,z5,z6]),(0,[z0,z1,z2,z1146,z5,z6]),(0,[z0,z1147,z2,z3,z5,z6]),(0,[z0,z1,z2,z1148,z5,z6]),(0,[z0,z82,z2,z21,z5,z6]),(0,[z0,z1,z2,z1149,z5,z6])],[(0,[z0,z1,z2,z3,z32,z213]),(0,[z0,z1,z2,z1150,z5,z6]),(0,[z0,z1,z1151,z3,z5,z6]),(0,[z0,z135,z2,z391,z5,z6]),(0,[z0,z1,z2,z1152,z5,z6]),(0,[z0,z1,z29,z3,z152,z74])],[(0,[z0,z1,z2,z5,z6,z1153]),(0,[z0,z1,z2,z1154,z5,z6]),(0,[z0,z1,z2,z1155,z5,z6])],[],[(0,[z0,z1,z2,z1156,z5,z6]),(0,[z144,z0,z1,z145,z5,z6]),(0,[z0,z1157,z2,z3,z5,z6]),(0,[z0,z1,z1158,z3,z5,z6]),(0,[z0,z1,z2,z87,z5,z25]),(0,[z0,z1,z2,z3,z6,z1159]),(0,[z0,z1,z2,z531,z5,z6])],[(0,[z0,z377,z2,z330,z5,z6]),(0,[z0,z1160,z2,z3,z5,z6]),(0,[z0,z1,z240,z3,z5,z64]),(1,[z0,z2,z3,z734,z6]),(0,[z0,z1,z2,z1161,z5,z6])]],
   [[(0,[z0,z1,z2,z1162,z5,z6]),(0,[z0,z377,z2,z334,z5,z6]),(0,[z0,z1,z2,z1163,z5,z6]),(0,[z0,z1,z2,z3,z1164,z6]),(0,[z0,z1,z3,z5,z1165,z6]),(0,[z0,z1,z11,z5,z6,z49]),(0,[z0,z63,z2,z43,z5,z6]),(0,[z0,z244,z29,z11,z5,z6])],[(0,[z0,z1,z2,z3,z1166,z6]),(0,[z0,z1167,z1,z3,z5,z6]),(0,[z0,z1,z2,z866,z5,z6]),(0,[z0,z1,z2,z1168,z5,z6]),(0,[z0,z241,z2,z3,z5,z72]),(0,[z0,z1169,z2,z3,z5,z6]),(0,[z0,z1,z29,z12,z152,z6])],[(0,[z0,z1,z2,z1170,z5,z6]),(0,[z0,z1,z2,z1171,z5,z6]),(0,[z243,z0,z1,z3,z295,z5]),(0,[z0,z525,z2,z3,z5,z72]),(0,[z0,z1,z2,z5,z1172,z6])],[(0,[z0,z2,z3,z5,z1173,z6]),(0,[z0,z1,z342,z11,z5,z6]),(0,[z0,z1,z12,z676,z5,z6]),(0,[z0,z1,z2,z1174,z5,z6]),(0,[z0,z1,z11,z5,z72,z150]),(0,[z258,z0,z1,z11,z5,z6]),(0,[z0,z38,z1,z531,z5,z150])],[(0,[z0,z1,z2,z3,z5,z1175]),(0,[z0,z1,z2,z1176,z5,z6]),(0,[z190,z1,z808,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z350]),(0,[z0,z1,z2,z12,z5,z350]),(0,[z0,z240,z3,z59,z5,z6]),(0,[z0,z2,z94,z3,z5,z72]),(0,[z0,z1,z2,z537,z5,z130]),(0,[z0,z1,z2,z3,z32,z772])],[(0,[z0,z1,z1177,z3,z5,z6]),(0,[z0,z1,z2,z1178,z5,z6]),(0,[z0,z414,z2,z3,z5,z357]),(0,[z0,z2,z11,z5,z6,z137]),(0,[z0,z2,z12,z5,z154,z6]),(0,[z0,z1,z257,z888,z5,z6])],[(0,[z0,z1,z2,z11,z5,z568]),(0,[z0,z1,z2,z12,z5,z568]),(0,[z0,z1,z2,z1179,z5,z6]),(0,[z0,z29,z37,z3,z152,z6])],[(0,[z0,z1,z3,z11,z5,z204]),(0,[z0,z1,z2,z3,z5,z350]),(0,[z0,z1,z2,z1006,z5,z6]),(0,[z0,z1,z2,z3,z5,z1180])]],
   [[(0,[z0,z1181,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1182,z6]),(0,[z0,z1,z1183,z3,z5,z6]),(0,[z13,z62,z2,z3,z5,z33]),(0,[z1,z2,z3,z5,z6,z715]),(0,[z0,z1,z11,z5,z6,z298]),(0,[z0,z467,z63,z2,z5,z6]),(1,[z0,z1,z11,z5,z74])],[(0,[z0,z1,z2,z3,z5,z568]),(0,[z0,z273,z1,z2,z5,z22]),(0,[z0,z2,z3,z5,z1184,z6]),(0,[z558,z0,z1,z2,z5,z361])],[(0,[z144,z1,z58,z3,z5,z204]),(0,[z0,z1,z2,z3,z1185,z6]),(0,[z0,z2,z11,z5,z151,z6]),(0,[z0,z1186,z2,z11,z5,z6]),(0,[z0,z1,z2,z131,z5,z358]),(0,[z0,z1,z29,z145,z5,z6]),(0,[z0,z1,z3,z1187,z5,z6])],[(0,[z1,z2,z808,z3,z5,z6]),(0,[z0,z1,z2,z1188,z5,z6]),(0,[z1189,z1,z2,z3,z5,z6]),(0,[z0,z1,z94,z3,z5,z357]),(0,[z0,z23,z1,z733,z5,z6]),(0,[z291,z0,z2,z595,z5,z6])],[(0,[z0,z62,z2,z306,z5,z6]),(0,[z0,z171,z112,z27,z5,z6]),(0,[z0,z125,z2,z3,z32,z126])],[(0,[z0,z1,z2,z3,z5,z1190]),(0,[z144,z215,z58,z3,z5,z6]),(0,[z0,z1,z2,z1191,z5,z6]),(0,[z0,z1192,z2,z11,z5,z6]),(0,[z0,z1186,z2,z3,z5,z6]),(0,[z0,z1,z12,z692,z5,z6]),(0,[z0,z244,z29,z3,z152,z6]),(0,[z0,z1,z2,z30,z5,z74])],[(0,[z0,z1,z2,z1193,z5,z6]),(0,[z0,z1,z2,z3,z734,z6]),(0,[z0,z1,z2,z1194,z5,z6]),(1,[z0,z1,z733,z5,z6]),(0,[z0,z228,z2,z11,z5,z6]),(0,[z0,z1,z3,z744,z95,z6])],[(0,[z0,z1,z2,z3,z5,z1195]),(0,[z0,z1196,z2,z3,z5,z6]),(0,[z0,z1,z12,z295,z5,z6]),(0,[z199,z0,z1,z2,z3,z48]),(0,[z0,z1,z2,z3,z5,z1197])]],
   [[(0,[z0,z1,z2,z12,z5,z45]),(0,[z144,z433,z1,z3,z5,z6]),(0,[z0,z1,z2,z11,z48,z6]),(0,[z0,z1,z2,z12,z48,z6]),(0,[z13,z1,z2,z3,z14,z33]),(0,[z0,z1,z2,z1198,z5,z6]),(0,[z0,z1,z2,z1199,z5,z6]),(0,[z0,z112,z3,z5,z72,z150]),(0,[z439,z0,z1,z11,z5,z6]),(0,[z0,z1192,z2,z3,z5,z6])],[(0,[z0,z863,z112,z3,z5,z6]),(0,[z0,z228,z2,z3,z5,z6]),(0,[z0,z125,z3,z5,z6,z472])],[(0,[z0,z1,z2,z1200,z5,z6]),(0,[z0,z135,z2,z3,z5,z159]),(0,[z0,z1,z621,z11,z5,z6]),(0,[z0,z1,z1201,z3,z5,z6]),(0,[z0,z1,z11,z5,z6,z74])],[(0,[z144,z1,z58,z3,z231,z6]),(0,[z0,z1,z3,z1202,z5,z6]),(0,[z0,z1,z2,z3,z48,z6]),(0,[z0,z178,z2,z3,z5,z6]),(0,[z0,z534,z1,z2,z5,z22])],[(0,[z0,z1,z1203,z3,z5,z6]),(0,[z0,z1,z2,z3,z1204,z6]),(0,[z0,z1,z111,z235,z5,z6]),(0,[z0,z1,z2,z1205,z5,z6]),(0,[z0,z2,z37,z30,z5,z6]),(0,[z0,z1,z3,z5,z6,z722]),(0,[z0,z1,z424,z5,z6,z22])],[(0,[z0,z360,z1,z3,z5,z6]),(0,[z0,z1,z39,z412,z5,z6]),(0,[z0,z1,z2,z1206,z5,z6]),(0,[z0,z1,z200,z11,z5,z6]),(0,[z613,z1,z2,z3,z314,z6]),(0,[z0,z34,z79,z11,z5,z6]),(0,[z1207,z0,z1,z2,z5,z6])],[(0,[z0,z1208,z2,z3,z5,z6]),(0,[z155,z1,z2,z3,z5,z715]),(0,[z0,z1,z79,z3,z5,z103]),(0,[z0,z71,z2,z11,z5,z72]),(0,[z0,z71,z2,z12,z5,z72]),(0,[z317,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z30,z5,z6]),(0,[z0,z1,z2,z3,z737,z6])],[(0,[z0,z1,z2,z1209,z5,z6]),(0,[z0,z1,z392,z12,z5,z6]),(0,[z0,z2,z3,z1210,z5,z6]),(0,[z20,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z1211,z5,z6]),(0,[z0,z1212,z1,z2,z3,z6]),(0,[z0,z1,z29,z776,z5,z6]),(0,[z0,z1,z211,z11,z5,z6]),(0,[z199,z0,z1,z3,z5,z472])]],
   [[(0,[z0,z1,z2,z18,z5,z6]),(0,[z0,z1,z3,z5,z6,z1213]),(0,[z0,z156,z2,z3,z48,z6]),(0,[z0,z599,z2,z21,z5,z6]),(0,[z0,z1,z2,z5,z6,z1214]),(0,[z0,z1,z11,z32,z5,z150])],[(0,[z88,z57,z2,z11,z5,z6]),(0,[z88,z57,z2,z12,z5,z6]),(0,[z0,z1,z3,z152,z469,z6]),(0,[z0,z1,z207,z444,z5,z6]),(0,[z0,z1,z2,z73,z5,z6]),(0,[z0,z96,z1,z12,z95,z6])],[(0,[z0,z2,z11,z5,z1184,z6])],[(0,[z88,z315,z2,z3,z5,z6]),(0,[z0,z35,z112,z11,z5,z6]),(0,[z0,z1,z2,z1215,z5,z6]),(0,[z0,z1216,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z5,z103]),(0,[z0,z1,z2,z12,z5,z103]),(0,[z0,z1,z104,z11,z5,z6]),(0,[z0,z1,z104,z12,z5,z6])],[(0,[z88,z57,z2,z3,z5,z6]),(0,[z0,z1,z3,z1217,z5,z6]),(0,[z0,z1,z2,z1218,z5,z6]),(0,[z0,z1,z11,z5,z95,z6]),(0,[z0,z2,z3,z5,z6,z1219]),(0,[z0,z1,z607,z3,z5,z150]),(0,[z0,z1220,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1221,z6]),(0,[z0,z1222,z2,z3,z5,z6]),(0,[z0,z62,z355,z3,z5,z6]),(0,[z0,z1,z11,z5,z164,z6]),(0,[z0,z2,z43,z5,z6,z64]),(0,[z0,z63,z2,z43,z5,z7]),(0,[z0,z63,z2,z762,z5,z6]),(0,[z0,z1,z2,z11,z5,z74]),(0,[z0,z602,z1,z2,z107,z6])],[(0,[z143,z0,z1,z11,z5,z6]),(0,[z0,z1,z104,z3,z5,z6]),(0,[z0,z1,z2,z3,z1223,z6]),(0,[z0,z1,z117,z12,z5,z6]),(0,[z0,z2,z37,z3,z5,z74]),(1,[z0,z1,z3,z5,z722])],[(0,[z582,z35,z2,z3,z5,z6]),(0,[z289,z1,z2,z216,z5,z6]),(0,[z0,z490,z1,z2,z5,z22]),(0,[z0,z360,z1,z3,z152,z6]),(0,[z0,z1,z2,z864,z5,z6]),(0,[z0,z1,z39,z508,z5,z6]),(0,[z0,z1,z11,z5,z6,z172]),(0,[z0,z244,z2,z30,z5,z6]),(0,[z0,z1,z2,z3,z5,z731])]],
   [[(0,[z0,z1,z2,z1224,z5,z6]),(0,[z0,z1225,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z1226,z6]),(0,[z0,z1,z2,z1227,z5,z6]),(0,[z0,z1,z2,z3,z5,z74]),(0,[z0,z1,z3,z152,z6,z489]),(0,[z0,z1,z2,z1228,z5,z6]),(0,[z0,z2,z3,z5,z6,z1229])],[(0,[z0,z2,z3,z5,z1230,z6]),(0,[z0,z191,z1,z11,z5,z6]),(0,[z0,z1231,z2,z3,z5,z6]),(0,[z223,z0,z2,z3,z5,z350]),(0,[z0,z1,z2,z5,z1232,z6]),(0,[z0,z1233,z2,z3,z5,z6])],[(0,[z310,z0,z1,z11,z5,z6]),(0,[z0,z1,z2,z1234,z5,z6]),(0,[z0,z1,z1235,z3,z5,z6]),(1,[z0,z1,z3,z744,z6]),(1,[z0,z228,z2,z5,z22])],[(0,[z144,z1,z58,z3,z5,z45]),(0,[z0,z1,z1236,z3,z5,z6]),(0,[z0,z1,z111,z1144,z5,z6]),(0,[z0,z1,z12,z11,z5,z6]),(0,[z0,z1,z2,z733,z5,z6]),(0,[z0,z178,z2,z70,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1237]),(0,[z144,z0,z215,z11,z5,z6]),(1,[z0,z37,z11,z5,z6]),(0,[z0,z2,z37,z11,z5,z6]),(0,[z0,z2,z37,z12,z5,z6]),(0,[z0,z2,z12,z5,z6,z137]),(0,[z0,z125,z257,z3,z5,z6])],[(0,[z0,z1,z2,z3,z1238,z6]),(0,[z0,z1,z207,z3,z209,z6]),(1,[z0,z1,z11,z5,z204]),(0,[z0,z1,z2,z974,z5,z6]),(0,[z190,z1,z149,z11,z5,z6]),(0,[z0,z1,z2,z1239,z5,z6]),(0,[z0,z1,z355,z3,z5,z33]),(0,[z0,z1240,z1,z2,z5,z6]),(0,[z0,z1,z11,z5,z6,z150]),(0,[z0,z1,z2,z61,z5,z6])],[(0,[z0,z1,z2,z11,z5,z6]),(0,[z0,z1,z2,z12,z5,z6]),(0,[z0,z360,z1,z747,z5,z6]),(0,[z1,z2,z3,z5,z297,z715]),(0,[z0,z1,z1241,z3,z5,z6])],[(0,[z0,z832,z2,z3,z5,z6]),(0,[z0,z1,z11,z5,z209,z6]),(0,[z0,z1,z2,z1242,z5,z6]),(0,[z0,z2,z37,z3,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 513) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 513).take 520) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1033).take 239) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1272)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [513, 520, 239] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 82).take 74).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 156).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 235).take 21).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [82, 74, 79, 21] = true :=
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

end PEqualNP.Outside.L_meta_45890

theorem PEqualNP.Outside.L_meta_45890 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008372384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008372384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45890.solve