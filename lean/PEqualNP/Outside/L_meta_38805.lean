import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38805

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00012245701c71e0#64 ++ 0x20002448ae038e3c#64 ++ 0xa813e7cff03cf3e7#64 ++ 0xd5027cf9fe079e7c#64 : BitVec 256),
   (0x0064891300c1a6aa#64 ++ 0x400c9122601834d5#64 ++ 0xf8ec993301c7ffff#64 ++ 0xbf1d93266038ffff#64 : BitVec 256),
   (0x030b162c36061854#64 ++ 0x806162c586c0c30a#64 ++ 0xf70f1e3c3e071c7f#64 ++ 0x7ee1e3c787c0e38f#64 : BitVec 256),
   (0x0db01fc01b681f07#64 ++ 0x01b603f8036d03e0#64 ++ 0xdff01fc03ff81f86#64 ++ 0xfbfe03f807ff03f0#64 : BitVec 256),
   (0x16dfe0002db7c000#64 ++ 0x02dbfc0005b6f800#64 ++ 0x9fffe0003fffe005#64 ++ 0xf3fffc0007fffc00#64 : BitVec 256),
   (0x27feddba80000000#64 ++ 0x04ffdbb750000000#64 ++ 0xe7ffffffc0000003#64 ++ 0xfcfffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [9, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xa813e7cff03cf3e7 0xd5027cf9fe079e7c

def z1 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8ec993301c7ffff 0xbf1d93266038ffff

def z2 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf70f1e3c3e071c7f 0x7ee1e3c787c0e38f

def z3 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff01fc03ff81f86 0xfbfe03f807ff03f0

def z4 : W := mkw 0x0fba1fe81f6a1f17 0x81f743fd03ed43e2 0xdffc1ff03ffb1f9e 0xfbff83fe07ff63f3

def z5 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fffe0003fffe005 0xf3fffc0007fffc00

def z6 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xe7ffffffc0000003 0xfcfffffff8000000

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0xa013e7cfc0000003 0xd4027cf9f8000000

def z8 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x1fec00003fffe004 0x23fd800007fffc00

def z9 : W := mkw 0x27feddbb80c1a6aa 0x44ffdbb7701834d5 0xefffffffc1c0e383 0xfdfffffff8381c70

def z10 : W := mkw 0x0100160012001804 0x002002c002400300 0xf70c1e303e071c7f 0x7ee183c607c0e38f

def z11 : W := mkw 0x169b60002d364000 0x02d36c0005a6c800 0x071360003e380000 0x40e26c0007c70000

def z12 : W := mkw 0x0000000100c1a6aa 0x40000000201834d5 0x1800000001c7fffc 0x030000000038ffff

def z13 : W := mkw 0x0065ab5770ddf7ea 0x600cb56aee1bbefd 0xf8fffffff1ffffff 0xff1ffffffe3fffff

def z14 : W := mkw 0x16dee0000db3c000 0x02dbdc0001b67800 0x1ffce0000ffbe000 0xa3ff9c0001ff7c00

def z15 : W := mkw 0x00000245500831e0 0x20000048aa01063c 0x200007cfc00013e2 0x040000f9f800027c

def z16 : W := mkw 0x16dfe2457dbff1e0 0x22dbfc48afb7fe3c 0xbfffe7cffffff3e7 0xf7fffcf9fffffe7c

def z17 : W := mkw 0x2ffedffa9b681f07 0x05ffdbff536d03e0 0xfffffffffff81f87 0xffffffffffff03f0

def z18 : W := mkw 0x27fedfba92001804 0x04ffdbf752400300 0xf7fffffffe001c07 0xfeffffffffc00380

def z19 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0x50ec183001c30c18 0x2a1d830600386183

def z20 : W := mkw 0x27feddbb80c1a6aa 0x44ffdbb7701834d5 0xffffffffc1c7ffff 0xfffffffff838ffff

def z21 : W := mkw 0x16dfc0002da78000 0x02dbf80005b4f000 0x97ef00003fc70005 0x72fde00007f8e000

def z22 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x08000000303cf3e4 0x0100000006079e7c

def z23 : W := mkw 0x16dec0000da38000 0x02dbd80001b47000 0x97ffe0000fc30001 0xf2fffc0001f86000

def z24 : W := mkw 0x27feddbb80c1a6aa 0x44ffdbb7701834d5 0xffec993301c7ffff 0xbffd93266038ffff

def z25 : W := mkw 0x0cb009c009680703 0x01960138012d00e0 0xd8f019c001f81f86 0xbb1e0338003f03f0

def z26 : W := mkw 0x0cb009c009680703 0x01960138012d00e0 0x08f001c001f80380 0x811e0038003f0070

def z27 : W := mkw 0x00002041401861a0 0x2000040828030c34 0x0810e1c3c038e380 0x81021c3878071c70

def z28 : W := mkw 0x030b366d761e79f4 0xa06166cdaec3cf3e 0xff1ffffffe3fffff 0xffe3ffffffc7ffff

def z29 : W := mkw 0x0064a95340d9e7aa 0x600c952a681b3cf5 0xf8fcf9f3c1ffffff 0xbf1f9f3e783fffff

def z30 : W := mkw 0x27ffdfbeb6061854 0x84fffbf7d6c0c30a 0xf7ef1e3c3e071c7f 0x7efde3c787c0e38f

def z31 : W := mkw 0x0df49fd21be99f0f 0x41be93fa437d33e1 0xdffc1ff03ffb1f9e 0xfbff83fe07ff63f3

def z32 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xf7ffffffc0071c7f 0xfefffffff800e38f

def z33 : W := mkw 0x2ffedffb9be9bfaf 0x45ffdbff737d37f5 0xffffffffffffffff 0xffffffffffffffff

def z34 : W := mkw 0x05b01f8012001804 0x00b603f002400300 0xd7f01fc03e001c06 0xfafe03f807c00380

def z35 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x58ec183001c7fffc 0x2b1d83060038ffff

def z36 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x47ec183000000000 0x28fd830600000000

def z37 : W := mkw 0x0fbb1fec3f6e1f57 0x81f763fd87edc3ea 0xdff31fcc3ff81f86 0xfbfe63f987ff03f0

def z38 : W := mkw 0x0d9136c57b3c79e5 0x21b226d8af678f3c 0xaf13e7cffe3cf3e7 0xd5e27cf9ffc79e7c

def z39 : W := mkw 0x05f49d9300c1a6aa 0x40be93b2601834d5 0xfffc9ff301c7ffff 0xffff93fe6038ffff

def z40 : W := mkw 0x149120002db7c000 0x0292240005b6f800 0x9ff000003fffe004 0xf3fe000007fffc00

def z41 : W := mkw 0x0064891200818000 0x000c912240103000 0xf8ec993301c7e007 0xbf1d93266038fc00

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000041067 0x140000000000820c

def z43 : W := mkw 0x00012001201460a0 0x0000240024028c14 0xa813e103303cf3e7 0xd5027c2066079e7c

def z44 : W := mkw 0x04d4c00000000000 0x009a980000000000 0x00f0e00000000000 0x801e1c0000000000

def z45 : W := mkw 0x00012005601460e0 0x20002400ac028c1c 0x000000000004e060 0x0000000000009c0c

def z46 : W := mkw 0x07ded42800000000 0x00fbda8500000000 0xe7fffe3c00000003 0xfcffffc780000000

def z47 : W := mkw 0x0490000009200000 0x0092000001240000 0x9ff000003ff80004 0xf3fe000007ff0000

def z48 : W := mkw 0x27feddba89200000 0x04ffdbb751240000 0xfffffffffff80007 0xffffffffffff0000

def z49 : W := mkw 0x020b002c24060050 0x804160058480c00a 0x200f003c00070079 0x0401e0078000e00f

def z50 : W := mkw 0x0044800000818000 0x0008900000103000 0x98ec800001c7e005 0xb31d90000038fc00

def z51 : W := mkw 0x09201fc012481f07 0x012403f8024903e0 0x40001fc000001f82 0x080003f8000003f0

def z52 : W := mkw 0x124fe0002497c000 0x0249fc000492f800 0x000fe0000007e001 0x0001fc000000fc00

def z53 : W := mkw 0x030a142806020814 0x8061428500c04102 0x570c18300e030c18 0x2ae1830601c06183

def z54 : W := mkw 0x27ffdfbeb6061854 0x84fffbf7d6c0c30a 0xf7fffffffe071c7f 0xfeffffffffc0e38f

def z55 : W := mkw 0x0001020430041040 0x0000204086008208 0x0000000030041064 0x000000000600820c

def z56 : W := mkw 0x126fe91324d7e6aa 0x424dfd22649afcd5 0xf8eff93301c7ffff 0xbf1dff266038ffff

def z57 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xa703060c3e041067 0x54e060c187c0820c

def z58 : W := mkw 0x0db01dc00b680f07 0x01b603b8016d01e0 0x5ff019c00ff80f80 0xabfe033801ff01f0

def z59 : W := mkw 0x224ec03a80000000 0x0449d80750000000 0xa01fe7ffc0000003 0xd403fcfff8000000

def z60 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xbfffe7cfffffe007 0xf7fffcf9fffffc00

def z61 : W := mkw 0x06dfe00020144000 0x00dbfc0004028800 0x8fffe000303ce005 0xf1fffc0006079c00

def z62 : W := mkw 0x01649f1312c1beae 0x402c93e2625837d5 0xffec9f333fc7ffff 0xfffd93e667f8ffff

def z63 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x08ffe00001ffe001 0x811ffc00003ffc00

def z64 : W := mkw 0x030a142800000000 0x0061428500000000 0xe70f1e3c00000003 0x7ce1e3c780000000

def z65 : W := mkw 0x24f4c99280000000 0x049e993250000000 0x00f0e1c3c0000000 0x801e1c3878000000

def z66 : W := mkw 0x130b362c3fb7d854 0x826166c587f6fb0a 0xff0f1e3c3ffffc7f 0x7fe1e3c787ffff8f

def z67 : W := mkw 0x100120002db7c000 0x0200240005b6f800 0x180000003fffe004 0x0300000007fffc00

def z68 : W := mkw 0x21201dba80000000 0x042403b750000000 0x60001fffc0000002 0x0c0003fff8000000

def z69 : W := mkw 0x0c9002401b681f07 0x01920048036d03e0 0x9ff000003ff81f84 0xf3fe000007ff03f0

def z70 : W := mkw 0x0044800000818000 0x0008900000103000 0x10ec000001c30000 0x221d800000386000

def z71 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf71ffffffe071c7f 0xfee3ffffffc0e38f

def z72 : W := mkw 0x16ffe9132df7e6aa 0x42dffd2265befcd5 0xfffff9333fffffff 0xffffff2667ffffff

def z73 : W := mkw 0x0fbb3fed7f7e7ff7 0xa1f767fdafefcffe 0xffffffffffffffff 0xffffffffffffffff

def z74 : W := mkw 0x0064891200000000 0x000c912240000000 0xe0ec993300000003 0xbc1d932660000000

def z75 : W := mkw 0x020b020436061854 0x8041604086c0c30a 0x970f00003e071c7d 0x72e1e00007c0e38f

def z76 : W := mkw 0x00012244701c5140 0x200024488e038a28 0x001366ccf0380000 0x40026cd99e070000

def z77 : W := mkw 0x030a162c16021854 0x806142c582c0430a 0x770c1e3c0e031c7a 0x2ee183c781c0638f

def z78 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x0ff007c03ff80380 0xc1fe00f807ff0070

def z79 : W := mkw 0x0020090000400602 0x00040120000800c0 0xd8e0190001c01f86 0xbb1c0320003803f0

def z80 : W := mkw 0x0df49fd31be9bfaf 0x41be93fa637d37f5 0xfffc9ff33fffffff 0xffff93fe67ffffff

def z81 : W := mkw 0x2ffedffa9b281905 0x05ffdbff53650320 0xe7fffffffe380003 0xfcffffffffc70000

def z82 : W := mkw 0x0100160012001804 0x002002c002400300 0xd7001e003e001c06 0x7ae003c007c00380

def z83 : W := mkw 0x0001020436061854 0x8000204086c0c30a 0x100000003e071c7c 0x0200000007c0e38f

def z84 : W := mkw 0x24f4e9d3c01861a0 0x249e9d3a78030c34 0x08f0e1c3c038e380 0x811e1c3878071c70

def z85 : W := mkw 0x0001020430041040 0x0000204086008208 0xa003060c30041067 0x540060c18600820c

def z86 : W := mkw 0x1fffffc57fffffe7 0x23fffff8affffffc 0xffffffcfffffffe7 0xfffffff9fffffffc

def z87 : W := mkw 0x2ffffffffb7c7fe7 0x25ffffffff6f8ffc 0xfffffffffffcffe7 0xffffffffffff9ffc

def z88 : W := mkw 0x0df5bfd77bfdffef 0x61beb7faef7fbffd 0xffffffffffffffff 0xffffffffffffffff

def z89 : W := mkw 0x27fffdbaa0144000 0x04ffffb754028800 0xeffffffff03ce007 0xfdfffffffe079c00

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000183000001c7a 0x0c0003060000038f

def z91 : W := mkw 0x09201fc012481f07 0x012403f8024903e0 0xd8e01fc001c01f86 0xbb1c03f8003803f0

def z92 : W := mkw 0x0100166d520839f4 0xa02002cdaa41073e 0x60001fffc0001ffa 0x0c0003fff80003ff

def z93 : W := mkw 0x080002401b281905 0x0100004803650320 0x000000003e380000 0x0000000007c70000

def z94 : W := mkw 0x0001224570ddf7ea 0x60002448ae1bbefd 0xb813e7cff1ffffff 0xd7027cf9fe3fffff

def z95 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x600f1e3c00071c7b 0x0c01e3c78000e38f

def z96 : W := mkw 0x0065a91760d5e6ea 0x600cb522ec1abcdd 0xf8eff93fc1c7ffff 0xbf1dff27f838ffff

def z97 : W := mkw 0x2ffeddba8b600e07 0x05ffdbb7516c01c0 0xf7ffffffcfc00c03 0xfefffffff9f80180

def z98 : W := mkw 0x0000000000000000 0x0000000000000000 0xf00c183000071c7f 0x3e0183060000e38f

def z99 : W := mkw 0x036f9f3f36c7befe 0xc06df3e7e6d8f7df 0xffef9f3f3fc7ffff 0xfffdf3e7e7f8ffff

def z100 : W := mkw 0x0cf489d309e9a7ab 0x419e913a613d34f5 0x08f081c301f8e380 0x811e1038603f1c70

def z101 : W := mkw 0x01649f3f12c1befe 0xc02c93e7e25837df 0xf8ec9f3f01c7ffff 0xbf1d93e7e038ffff

def z102 : W := mkw 0x17dfd62c3fa79854 0x82fbfac587f4f30a 0xf7ef1e3c3fc71c7f 0x7efde3c787f8e38f

def z103 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x0703060c3e000000 0x40e060c187c00000

def z104 : W := mkw 0x14d4e00009b1c000 0x029a9c0001363800 0x98fce00001ffe005 0xb31f9c00003ffc00

def z105 : W := mkw 0x16ffe9002df7c602 0x02dffd2005bef8c0 0xdffff9003fffff87 0xfbffff2007fffff0

def z106 : W := mkw 0x100120002d364000 0x0200240005a6c800 0x000000003e380000 0x0000000007c70000

def z107 : W := mkw 0x120b20002db7c000 0x0241640005b6f800 0x9f0f00003fffe005 0x73e1e00007fffc00

def z108 : W := mkw 0x04912245793c71e0 0x20922448af278e3c 0xbff3e7cffffcf3e7 0xf7fe7cf9ffff9e7c

def z109 : W := mkw 0x05b01d8000000000 0x00b603b000000000 0xc7f01fc000000002 0xf8fe03f800000000

def z110 : W := mkw 0x00002001401060a0 0x2000040028020c14 0x0000e003c000e000 0x00001c0078001c00

def z111 : W := mkw 0x00200901004026a2 0x00040120200804d4 0xf8e0990301c4ffe7 0xbf1c132060389ffc

def z112 : W := mkw 0x00012244701c5140 0x200024488e038a28 0xa01366ccf03c1067 0x54026cd99e07820c

def z113 : W := mkw 0x14d4e00009b1c000 0x029a9c0001363800 0x08f0e00001f8e000 0x811e1c00003f1c00

def z114 : W := mkw 0x0d9016c01b681f07 0x01b202d8036d03e0 0x1f1006c03ff81f84 0x43e200d807ff03f0

def z115 : W := mkw 0x00200913004026aa 0x40040122600804d5 0x6000193300001ffa 0x0c000326600003ff

def z116 : W := mkw 0x2490408080000000 0x0492081010000000 0x001060c0c0000000 0x00020c1818000000

def z117 : W := mkw 0x00000245500831e0 0x20000048aa01063c 0xa81007cff03813e6 0xd50200f9fe07027c

def z118 : W := mkw 0x27ffdfbfb6c7befe 0xc4fffbf7f6d8f7df 0xffffffffffc7ffff 0xfffffffffff8ffff

def z119 : W := mkw 0x27feddba80818000 0x04ffdbb750103000 0xffffffffc1c7e007 0xfffffffff838fc00

def z120 : W := mkw 0x1fffffc03fffdf07 0x03fffff807fffbe0 0xdfffffc03fffff87 0xfbfffff807fffff0

def z121 : W := mkw 0x080002401b681f07 0x01000048036d03e0 0x180000003ff81f84 0x0300000007ff03f0

def z122 : W := mkw 0x224ec03a80000000 0x0449d80750000000 0x200fe03fc0000001 0x0401fc07f8000000

def z123 : W := mkw 0x0fbb1fec3f6e1f57 0x81f763fd87edc3ea 0xffff1ffc3fff1fff 0xffffe3ff87ffe3ff

def z124 : W := mkw 0x169b60002d364000 0x02d36c0005a6c800 0x971f60003e3f0005 0x72e3ec0007c7e000

def z125 : W := mkw 0x09201fc012481f07 0x012403f8024903e0 0xd7001fc03e001f86 0x7ae003f807c003f0

def z126 : W := mkw 0x27feddba80c1860a 0x44ffdbb7501830c1 0xf7ffffffc1c30c1b 0xfefffffff8386183

def z127 : W := mkw 0x0001000420040040 0x0000200084008008 0x2003000c00040061 0x040060018000800c

def z128 : W := mkw 0x279b76ecf01c5140 0x24f36edd9e038a28 0x071366ccf0380000 0x40e26cd99e070000

def z129 : W := mkw 0x0001020436061854 0x8000204086c0c30a 0xf00c18303e071c7f 0x3e01830607c0e38f

def z130 : W := mkw 0x0000020412001854 0x800000408240030a 0x0000000000001c78 0x000000000000038f

def z131 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x08e0810301c0e380 0x811c102060381c70

def z132 : W := mkw 0x1fffffd33fffffaf 0x43fffffa67fffff5 0xfffffff33fffffff 0xfffffffe67ffffff

def z133 : W := mkw 0x0045a257709df1e8 0x6008b44aee13be3d 0xa81fe7fff03ff3ff 0xd503fcfffe07fe7f

def z134 : W := mkw 0x0001000020040000 0x0000200004008000 0x8003000030040005 0x5000600006008000

def z135 : W := mkw 0x0fff9fff3fefbfff 0xc1fff3ffe7fdf7ff 0xffff9fff3fffffff 0xfffff3ffe7ffffff

def z136 : W := mkw 0x1fbb7fc03f7e5f07 0x03f76ff807efcbe0 0xdff37fc03ff81f86 0xfbfe6ff807ff03f0

def z137 : W := mkw 0x00002241501871a0 0x200004482a030e34 0x8810e7c3f038f386 0xd1021cf87e071e70

def z138 : W := mkw 0x16dfe02c2db7c050 0x82dbfc0585b6f80a 0xbfffe03c3fffe07d 0xf7fffc0787fffc0f

def z139 : W := mkw 0x0490000009200000 0x0092000001240000 0x08f0000001f80000 0x811e0000003f0000

def z140 : W := mkw 0x1df4ffc01bf9df07 0x03be9ff8037f3be0 0xdff0ffc03ff8ff86 0xfbfe1ff807ff1ff0

def z141 : W := mkw 0x27feddba86020814 0x84ffdbb750c04102 0xf7ffffffce030c1b 0xfefffffff9c06183

def z142 : W := mkw 0x0db01d800b600e07 0x01b603b0016c01c0 0x57e018000fc00c00 0x2afc030001f80180

def z143 : W := mkw 0x0020090000400602 0x00040120000800c0 0xf8ec193001c71fff 0xbf1d83260038e3ff

def z144 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2003e7cfc004f3e3 0x04007cf9f8009e7c

def z145 : W := mkw 0x0000024010081100 0x0000004802010220 0x881007c030381386 0xd10200f806070270

def z146 : W := mkw 0x030b166c360e1954 0x806162cd86c1c32a 0xff1f1ffc3e3f1fff 0xffe3e3ff87c7e3ff

def z147 : W := mkw 0x224fe03fe01460e0 0x2449fc07fc028c1c 0x200fe03fc004e061 0x0401fc07f8009c0c

def z148 : W := mkw 0x004480130081a0a8 0x4008900260103415 0xf00c98330007fc7f 0x3e0193066000ff8f

def z149 : W := mkw 0x00000041400821a0 0x2000000828010434 0x000001c3c0000380 0x0000003878000070

def z150 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xd8e0990301c0ff86 0xbb1c132060381ff0

def z151 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfff3ffcffff81f87 0xfffe7ff9ffff03f0

def z152 : W := mkw 0x169b60002d364000 0x02d36c0005a6c800 0x9ff360003ff80004 0xf3fe6c0007ff0000

def z153 : W := mkw 0x00000001000020a0 0x0000000020000414 0x080081030000e380 0x8100102060001c70

def z154 : W := mkw 0x0f9b16ec3f2e1955 0x81f362dd87e5c32a 0xf71f1efc3e3f1c7f 0x7ee3e3df87c7e38f

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0x001366ccc0000000 0x40026cd998000000

def z156 : W := mkw 0x27fffffff01c71e0 0x24fffffffe038e3c 0xeffffffff03cf3e7 0xfdfffffffe079e7c

def z157 : W := mkw 0x27ffdfbeb6061854 0x84fffbf7d6c0c30a 0xe7fffffffe000003 0xfcffffffffc00000

def z158 : W := mkw 0x0000000100c1a6aa 0x40000000201834d5 0xb800810301c7ffff 0x970010206038ffff

def z159 : W := mkw 0x37fffffffdbff1e0 0x26ffffffffb7fe3c 0xfffffffffffff3e7 0xfffffffffffffe7c

def z160 : W := mkw 0x0000000100c1a6aa 0x40000000201834d5 0x0800000001c0e380 0x0100000000381c70

def z161 : W := mkw 0x032b1f2c36461e56 0x806563e586c8c3ca 0xffef1f3c3fc71fff 0xfffde3e787f8e3ff

def z162 : W := mkw 0x27feddbb8081a0a8 0x44ffdbb770103415 0xe7ffffffc007e07b 0xfcfffffff800fc0f

def z163 : W := mkw 0x14f4e91309f1e6aa 0x429e9d22613e3cd5 0x08f0e10301f8e380 0x811e1c20603f1c70

def z164 : W := mkw 0x05b01d8000400602 0x00b603b0000800c0 0xdff01fc001c01f86 0xfbfe03f8003803f0

def z165 : W := mkw 0x37fffdbaadb7c000 0x06ffffb755b6f800 0xffffffffffffe007 0xfffffffffffffc00

def z166 : W := mkw 0x2db01ffa9b681f07 0x05b603ff536d03e0 0xfff01ffffff81f86 0xfffe03ffffff03f0

def z167 : W := mkw 0x00000001000020a0 0x0000000020000414 0xa80081030004f3e7 0x9500102060009e7c

def z168 : W := mkw 0x24f4c99280000000 0x049e993250000000 0x00e0000000000000 0x001c000000000000

def z169 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0xf0ec183001c71c7f 0x3e1d83060038e38f

def z170 : W := mkw 0x37dff4a8adb7c000 0x06fbfe9515b6f800 0x9fffe6ccffffe005 0xf3fffcd99ffffc00

def z171 : W := mkw 0x27ffddbea4060050 0x84fffbb7d480c00a 0xe7ffffffc007007b 0xfcfffffff800e00f

def z172 : W := mkw 0x0cf489d309e9a7ab 0x419e913a613d34f5 0xf8fc99f301ffffff 0xbf1f933e603fffff

def z173 : W := mkw 0x026f891324c7a6aa 0x404df1226498f4d5 0xffef99333fc7ffff 0xfffdf32667f8ffff

def z174 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0xa713e7cfc0000003 0xd4e27cf9f8000000

def z175 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x07f3e7cfc0000000 0xc0fe7cf9f8000000

def z176 : W := mkw 0x17dff6003fb7d804 0x02fbfec007f6fb00 0xdffffe003ffffc07 0xfbffffc007ffff80

def z177 : W := mkw 0x09201fec12481f57 0x812403fd824903ea 0x60001ffc00001ffa 0x0c0003ff800003ff

def z178 : W := mkw 0x0100162c12001854 0x802002c58240030a 0x60001e3c00001c7a 0x0c0003c78000038f

def z179 : W := mkw 0x0064891200000000 0x000c912240000000 0xe0ffffffc0000003 0xfc1ffffff8000000

def z180 : W := mkw 0x0db13fc57b7c7fe7 0x21b627f8af6f8ffc 0xfff3ffcffffcffe7 0xfffe7ff9ffff9ffc

def z181 : W := mkw 0x020b022c34061050 0x804160458680c20a 0xa00f063c3007107f 0x5401e0c78600e20f

def z182 : W := mkw 0x0fba1da80f620e17 0x81f743b501ec41c2 0x57ec18300fc30c18 0x2afd830601f86183

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x2003e00fc0000001 0x04007c01f8000000

def z184 : W := mkw 0x07ba1da800000000 0x00f743b500000000 0xe7ff1ffc00000003 0xfcffe3ff80000000

def z185 : W := mkw 0x16dfe2447dbfd140 0x22dbfc488fb7fa28 0x9fffe6ccffffe005 0xf3fffcd99ffffc00

def z186 : W := mkw 0x24f4c99280000000 0x049e993250000000 0xa0f3e7cfc0000003 0xd41e7cf9f8000000

def z187 : W := mkw 0x080122457b7c7fe7 0x21002448af6f8ffc 0x180000003ffcffe4 0x0300000007ff9ffc

def z188 : W := mkw 0x124fe0002497c000 0x0249fc000492f800 0x98efe00001c7e005 0xb31dfc000038fc00

def z189 : W := mkw 0x16fec9120de3860a 0x42dfd92241bc70c1 0x57ec18300fc30c18 0x2afd830601f86183

def z190 : W := mkw 0x0db01fec1b681f57 0x81b603fd836d03ea 0xfff01ffc3ff81ffe 0xfffe03ff87ff03ff

def z191 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x18e0810301c7fffc 0x831c10206038ffff

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c003000070079 0x040180060000e00f

def z193 : W := mkw 0x00200913004026aa 0x40040122600804d5 0xf8e0193301c01ffe 0xbf1c0326603803ff

def z194 : W := mkw 0x169b62447d3e5140 0x22d36c488fa7ca28 0x071366ccfe380000 0x40e26cd99fc70000

def z195 : W := mkw 0x0001200020144000 0x0000240004028800 0x08000000303ce004 0x0100000006079c00

def z196 : W := mkw 0x0df49d920be18e0f 0x41be93b2417c31c1 0x57ec18300fc30c18 0x2afd830601f86183

def z197 : W := mkw 0x0cb12bc5797c77e3 0x21962578af2f8efc 0xa8f3e7cff1fcf3e7 0xd51e7cf9fe3f9e7c

def z198 : W := mkw 0x236eddba80000000 0x046ddbb750000000 0x600fffffc0000003 0x0c01fffff8000000

def z199 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x570c18303e071c7c 0x2ae1830607c0e38f

def z200 : W := mkw 0x00000001000020a0 0x0000000020000414 0xa813e7cfc004f3e7 0xd5027cf9f8009e7c

def z201 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x57f01ec03ff80c00 0x6afe03d807ff0180

def z202 : W := mkw 0x16dfe2043fb7d854 0x82dbfc4087f6fb0a 0x9fffe0003ffffc7d 0xf3fffc0007ffff8f

def z203 : W := mkw 0x036fbf7f76dffffe 0xe06df7efeedbffff 0xffffffffffffffff 0xffffffffffffffff

def z204 : W := mkw 0x004480130081a0a8 0x4008900260103415 0x200c80330007e079 0x040190066000fc0f

def z205 : W := mkw 0x0001200020144000 0x0000240004028800 0x8813e000303ce005 0xd1027c0006079c00

def z206 : W := mkw 0x0000000000000000 0x0000000000000000 0x970000003e000004 0x72e0000007c00000

def z207 : W := mkw 0x00002041401861a0 0x2000040828030c34 0xa813e7cfc038e383 0xd5027cf9f8071c70

def z208 : W := mkw 0x00012005601460e0 0x20002400ac028c1c 0x2003e00fc004e061 0x04007c01f8009c0c

def z209 : W := mkw 0x16dec0000da38000 0x02dbd80001b47000 0x17ec00000fc30000 0x22fd800001f86000

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z211 : W := mkw 0x17dff62c3fb7d854 0x82fbfec587f6fb0a 0xfffffe3c3ffffc7f 0xffffffc787ffff8f

def z212 : W := mkw 0x0fbb1fc03f6e1f07 0x01f763f807edc3e0 0xdfff1fc03fff1f87 0xfbffe3f807ffe3f0

def z213 : W := mkw 0x0ffedfc01b681f07 0x01ffdbf8036d03e0 0xdfffffc03ff81f87 0xfbfffff807ff03f0

def z214 : W := mkw 0x06dec00000000000 0x00dbd80000000000 0x87ffe00000000001 0xf0fffc0000000000

def z215 : W := mkw 0x16dec0000da38000 0x02dbd80001b47000 0x9ffc00003ffb0004 0xf3ff800007ff6000

def z216 : W := mkw 0x0db01d800b600e07 0x01b603b0016c01c0 0xd7f01fc00fc00c02 0xfafe03f801f80180

def z217 : W := mkw 0x090016c012081905 0x012002d802410320 0x000006c000000000 0x000000d800000000

def z218 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x70ec983301c7ec79 0x2e1d93066038fd8f

def z219 : W := mkw 0x0800004009680703 0x01000008012d00e0 0x0800000001f80380 0x01000000003f0070

def z220 : W := mkw 0x0045a0002095c000 0x0008b4000412b800 0x98ffe00031ffe005 0xf31ffc00063ffc00

def z221 : W := mkw 0x0001200020144000 0x0000240004028800 0x0013600030380000 0x40026c0006070000

def z222 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xf81ffffff03fffff 0xff03fffffe07ffff

def z223 : W := mkw 0x124fe0132497e0a8 0x4249fc026492fc15 0x200fe0330007e079 0x0401fc066000fc0f

def z224 : W := mkw 0x0cb009c009680703 0x01960138012d00e0 0x9ff001c03ff80384 0xf3fe003807ff0070

def z225 : W := mkw 0x0d9016c01b281905 0x01b202d803650320 0x8f1007c03e381386 0xd1e200f807c70270

def z226 : W := mkw 0x030b142c26060854 0x8061628584c0c10a 0x770f183c0e070c79 0x2ee1e30781c0e18f

def z227 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013e00000000001 0xd0027c0000000000

def z228 : W := mkw 0x16dfe2457dbff1e0 0x22dbfc48afb7fe3c 0x9fffe0003ffff3e5 0xf3fffc0007fffe7c

def z229 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x0ff3e0003ff8e000 0xc1fe7c0007ff1c00

def z230 : W := mkw 0x09649fd312c9bfaf 0x412c93fa625937f5 0xf8ec9ff301c7ffff 0xbf1d93fe6038ffff

def z231 : W := mkw 0x34f4e99289b1c000 0x069e9d3251363800 0x08f0e1c3c1f8e000 0x811e1c38783f1c00

def z232 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x67ec1fffc0000002 0x2cfd83fff8000000

def z233 : W := mkw 0x00000245500831e0 0x20000048aa01063c 0x00000000000013e0 0x000000000000027c

def z234 : W := mkw 0x21201dba80000000 0x042403b750000000 0xe013ffffc0000003 0xdc027ffff8000000

def z235 : W := mkw 0x024ec00000000000 0x0049d80000000000 0x000fe00000000001 0x0001fc0000000000

def z236 : W := mkw 0x2ffeddba8b600e07 0x05ffdbb7516c01c0 0x57ec18300fc00c00 0x2afd830601f80180

def z237 : W := mkw 0x16dfe0012db7e0a0 0x02dbfc0025b6fc14 0xbfffe1033ffff3e7 0xf7fffc2067fffe7c

def z238 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x57e01fc00fc01f82 0x2afc03f801f803f0

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0xa003060c00000003 0x540060c180000000

def z240 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x5fe018003ff81f84 0x2bfc030007ff03f0

def z241 : W := mkw 0x024f800024878000 0x0049f0000490f000 0x9fef80003fc7e005 0xf3fdf00007f8fc00

def z242 : W := mkw 0x124fe245749ff1e0 0x2249fc48ae93fe3c 0xa81fe7cff03ff3e7 0xd503fcf9fe07fe7c

def z243 : W := mkw 0x036f9f3e36c79e5e 0xc06df3e7c6d8f3cb 0xf7ef1e3c3fc71c7f 0x7efde3c787f8e38f

def z244 : W := mkw 0x100122457dbff1e0 0x22002448afb7fe3c 0x180000003ffff3e4 0x0300000007fffe7c

def z245 : W := mkw 0x09201fc552483fe7 0x212403f8aa4907fc 0x60001fcfc0001fe2 0x0c0003f9f80003fc

def z246 : W := mkw 0x004480130081a0a8 0x4008900260103415 0xa80c81330007f3ff 0x950190266000fe7f

def z247 : W := mkw 0x00000001004026aa 0x40000000200804d5 0x0000000000001ff8 0x00000000000003ff

def z248 : W := mkw 0x01201f0012401e06 0x002403e0024803c0 0xdfe01f003fc01f86 0xfbfc03e007f803f0

def z249 : W := mkw 0x0490000009200000 0x0092000001240000 0x17e000000fc00000 0x22fc000001f80000

def z250 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8ffffffc1c7ffff 0xff1ffffff838ffff

def z251 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0x071366ccc0000000 0x40e26cd998000000

def z252 : W := mkw 0x0064a95340d9e7aa 0x600c952a681b3cf5 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z253 : W := mkw 0x00000001000020a0 0x0000000020000414 0xf80c99330007ffff 0xbf0193266000ffff

def z254 : W := mkw 0x030a142800000000 0x0061428500000000 0x0703060c00000000 0x40e060c180000000

def z255 : W := mkw 0x00212b45705c77e2 0x20042568ae0b8efc 0xf8f3ffcff1fcffe7 0xff1e7ff9fe3f9ffc

def z256 : W := mkw 0x069a400000000000 0x00d3480000000000 0x0713600000000000 0x40e26c0000000000

def z257 : W := mkw 0x059016001b201804 0x00b202c003640300 0xdff01e003ff81c06 0xfbfe03c007ff0380

def z258 : W := mkw 0x14d5e24579bdf1e0 0x229abc48af37be3c 0xa8f3e7cff1fcf3e7 0xd51e7cf9fe3f9e7c

def z259 : W := mkw 0x00012245761e79f4 0xa0002448aec3cf3e 0xb813e7cffe3fffff 0xd7027cf9ffc7ffff

def z260 : W := mkw 0x2df4dfd29b681f07 0x05be9bfa536d03e0 0xdff0ffc3fff81f86 0xfbfe1ff87fff03f0

def z261 : W := mkw 0x030a162c12001854 0x806142c58240030a 0xe70f1e3c00001c7b 0x7ce1e3c78000038f

def z262 : W := mkw 0x0044801200818008 0x4008900240103001 0x000c003000030018 0x0001800600006003

def z263 : W := mkw 0x020b000024060000 0x004160000480c000 0x970f00003e070005 0x72e1e00007c0e000

def z264 : W := mkw 0x00000241100831a0 0x0000004822010634 0xa81087c3303cf3e7 0xd50210f866079e7c

def z265 : W := mkw 0x0000000100c1a6aa 0x40000000201834d5 0xf80c183001c7ffff 0x3f0183060038ffff

def z266 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x570f1e3c3e030c18 0x6ae1e3c787c06183

def z267 : W := mkw 0x020a000004020000 0x0041400000804000 0x170c00000e030000 0x22e1800001c06000

def z268 : W := mkw 0x0044800000818000 0x0008900000103000 0x08e0800001c0e000 0x811c100000381c00

def z269 : W := mkw 0x169b60002d364000 0x02d36c0005a6c800 0x8f13e0003e3ce005 0xd1e27c0007c79c00

def z270 : W := mkw 0x0d9136c47b3c5945 0x21b226d88f678b28 0x071366ccfe380000 0x40e26cd99fc70000

def z271 : W := mkw 0x279b56acb6061854 0x84f36ad596c0c30a 0xf71f7efcfe071c7f 0x7ee3efdf9fc0e38f

def z272 : W := mkw 0x2fba5fe89b681f07 0x05f74bfd136d03e0 0xdff37fccfff81f86 0xfbfe6ff99fff03f0

def z273 : W := mkw 0x06dec00000000000 0x00dbd80000000000 0xa7ffe7cfc0000003 0xf4fffcf9f8000000

def z274 : W := mkw 0x0d9016c01b281905 0x01b202d803650320 0xd7101ec03e381c06 0x7ae203d807c70380

def z275 : W := mkw 0x0d9016c01b281905 0x01b202d803650320 0x071006c03e380000 0x40e200d807c70000

def z276 : W := mkw 0x0000024010081100 0x0000004802010220 0x000007c000001382 0x000000f800000270

def z277 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x67eff83fc0000001 0x2cfdff07f8000000

def z278 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xe8ec993301c0e383 0xbd1d932660381c70

def z279 : W := mkw 0x0490024019281100 0x0092004803250220 0x9ff007c03ff81386 0xf3fe00f807ff0270

def z280 : W := mkw 0x020b000024060000 0x004160000480c000 0x000f000000070001 0x0001e0000000e000

def z281 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x70ec193301c31ffa 0x2e1d8326603863ff

def z282 : W := mkw 0x0db01d800b600e07 0x01b603b0016c01c0 0xdff018003ff80c04 0xfbfe030007ff0180

def z283 : W := mkw 0x2020099280000000 0x0404013250000000 0x000001c3c0000000 0x0000003878000000

def z284 : W := mkw 0x00200b57504837ea 0x6004016aea0906fd 0x60001fffc0001ffa 0x0c0003fff80003ff

def z285 : W := mkw 0x0590148000000000 0x00b2029000000000 0x071006c000000000 0x40e200d800000000

def z286 : W := mkw 0x2ffedffa92481f07 0x05ffdbff524903e0 0xe7ffffffc0001f83 0xfcfffffff80003f0

def z287 : W := mkw 0x0800024012481f07 0x01000048024903e0 0x0000000000001f80 0x00000000000003f0

def z288 : W := mkw 0x25b01dba80000000 0x04b603b750000000 0xe7f01fffc0000002 0xfcfe03fff8000000

def z289 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x280007cff03cf3e6 0x050000f9fe079e7c

def z290 : W := mkw 0x030b362c36165854 0x806166c586c2cb0a 0xff1ffe3c3e3ffc7f 0xffe3ffc787c7ff8f

def z291 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2013e6cff03ce061 0x44027cd9fe079c0c

def z292 : W := mkw 0x24f4c99380c1a6aa 0x449e9932701834d5 0xf8fcf9f3c1c7ffff 0xbf1f9f3e7838ffff

def z293 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0xf0ec993301c30c1b 0xbe1d932660386183

def z294 : W := mkw 0x29201ffa92481f07 0x052403ff524903e0 0x60001fffc0001f82 0x0c0003fff80003f0

def z295 : W := mkw 0x27ded4ba80000000 0x04fbda9750000000 0x271fe6ffc0000001 0x44e3fcdff8000000

def z296 : W := mkw 0x0100162c12001854 0x802002c58240030a 0xf00c1e3c00071c7f 0x3e0183c78000e38f

def z297 : W := mkw 0x16dee00009b1c000 0x02dbdc0001363800 0x8fffe00001f8e001 0xf1fffc00003f1c00

def z298 : W := mkw 0x020b002c24060050 0x804160058480c00a 0xb70f003c3e07007d 0x76e1e00787c0e00f

def z299 : W := mkw 0x37feddba8da38000 0x06ffdbb751b47000 0x57ec18300fc30000 0x2afd830601f86000

def z300 : W := mkw 0x05b13fc5701c71e0 0x20b627f8ae038e3c 0xeff3ffcff03cf3e7 0xfdfe7ff9fe079e7c

def z301 : W := mkw 0x036f9f3e36061854 0x806df3e7c6c0c30a 0xf7ef9f3f3e071c7f 0xfefdf3e7e7c0e38f

def z302 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x28ec813301c7e3f9 0x851d90266038fc7f

def z303 : W := mkw 0x0db01d800b600e07 0x01b603b0016c01c0 0xdfe019000fc01f86 0xbbfc032001f803f0

def z304 : W := mkw 0x020b202d641660f0 0xa0416405ac82cc1e 0x200fe03fc007e079 0x0401fc07f800fc0f

def z305 : W := mkw 0x0000000000400602 0x00000000000800c0 0x1800000001c01f84 0x03000000003803f0

def z306 : W := mkw 0x04d4800009a18000 0x009a900001343000 0x9ffc80003fffe005 0xf3ff900007fffc00

def z307 : W := mkw 0x0db01fc11be9bfaf 0x41b603f8237d37f5 0xdff01fc03ffffffe 0xfbfe03f807ffffff

def z308 : W := mkw 0x036e9d3b00c1a6aa 0x406dd3a7601834d5 0xffef9f3f01c7ffff 0xfffdf3e7e038ffff

def z309 : W := mkw 0x06dfc00024060000 0x00dbf8000480c000 0x97ffe0003e070005 0xf2fffc0007c0e000

def z310 : W := mkw 0x0df49fd21b681f07 0x01be93fa436d03e0 0xfffc9ff33ff81f87 0xffff93fe67ff03f0

def z311 : W := mkw 0x2cf4c9d289680703 0x059e993a512d00e0 0x08f0e1c3c1f80380 0x811e1c38783f0070

def z312 : W := mkw 0x21201dba80000000 0x042403b750000000 0x4000183000000000 0x0800030600000000

def z313 : W := mkw 0x0000000000c1860a 0x40000000001830c1 0x1000000001c30c18 0x0200000000386183

def z314 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2803e00ff03cf3e5 0x05007c01fe079e7c

def z315 : W := mkw 0x36dfe03aadb7c000 0x06dbfc0755b6f800 0xbfffe03fffffe005 0xf7fffc07fffffc00

def z316 : W := mkw 0x06dfe245701c71e0 0x20dbfc48ae038e3c 0xafffe7cff03cf3e7 0xf5fffcf9fe079e7c

def z317 : W := mkw 0x0001224570ddf7ea 0x60002448ae1bbefd 0x1800000031fffffc 0x03000000063fffff

def z318 : W := mkw 0x0cb0098009600603 0x01960130012c00c0 0x00e0000001c00000 0x001c000000380000

def z319 : W := mkw 0x124ec00004838000 0x0249d80000907000 0x000c000000030000 0x0001800000006000

def z320 : W := mkw 0x14d4e04149b9e1a0 0x229a9c0829373c34 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z321 : W := mkw 0x0065ab5770ddf7ea 0x600cb56aee1bbefd 0xa8f3e7cff1fcf3e7 0xd51e7cf9fe3f9e7c

def z322 : W := mkw 0x090016401b681f07 0x012002c8036d03e0 0xdf001e003ff81f86 0x7be003c007ff03f0

def z323 : W := mkw 0x1cf4e9c009f9c703 0x039e9d38013f38e0 0x08f0e1c001f8e380 0x811e1c38003f1c70

def z324 : W := mkw 0x00000005400020e0 0x20000000a800041c 0x2000000fc0000060 0x04000001f800000c

def z325 : W := mkw 0x00012205701470e0 0x20002440ae028e1c 0xa003e60ff004f067 0x54007cc1fe009e0c

def z326 : W := mkw 0x020a002804020010 0x8041400500804002 0x000c003000030018 0x0001800600006003

def z327 : W := mkw 0x036e9d3a06c38e1e 0xc06dd3a740d871c3 0x57ec18300fc30c18 0x2afd830601f86183

def z328 : W := mkw 0x17ded4280fa38814 0x82fbda8501f47102 0x57ec18300fc30c18 0x2afd830601f86183

def z329 : W := mkw 0x27fefdfbc01861a0 0x24ffdfbf78030c34 0xefffffffc038e383 0xfdfffffff8071c70

def z330 : W := mkw 0x020b020434061040 0x004160408680c208 0xb70f060c3e071067 0x76e1e0c187c0e20c

def z331 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfffc1ff03fff1fff 0xffff83fe07ffe3ff

def z332 : W := mkw 0x14d5e0002db7c000 0x029abc0005b6f800 0x18f0e0003fffe004 0x831e1c0007fffc00

def z333 : W := mkw 0x14d4c00009a18000 0x029a980001343000 0x00e0000001c00000 0x001c000000380000

def z334 : W := mkw 0x0db03fc15b787fa7 0x21b607f82b6f0ff4 0xdff0ffc3fff8ff86 0xfbfe1ff87fff1ff0

def z335 : W := mkw 0x27fedffa90081100 0x04ffdbff52010220 0xeffffffff0381387 0xfdfffffffe070270

def z336 : W := mkw 0x034f963f3687b8fc 0xc069f2c7e6d0f71f 0xf70f9e3f3e07fc7f 0x7ee1f3c7e7c0ff8f

def z337 : W := mkw 0x00200913004026aa 0x40040122600804d5 0xf00c193300071fff 0x3e0183266000e3ff

def z338 : W := mkw 0x134ff62c3697d854 0x8269fec586d2fb0a 0xf70ffe3c3e07fc7f 0x7ee1ffc787c0ff8f

def z339 : W := mkw 0x0064891200400602 0x000c9122400800c0 0xf8ec993301c01f87 0xbf1d9326603803f0

def z340 : W := mkw 0x00002041401861a0 0x2000040828030c34 0x080000000038e380 0x0100000000071c70

def z341 : W := mkw 0x07bb1fac36061854 0x80f763f586c0c30a 0xf7ff1ffc3e071c7f 0xfeffe3ff87c0e38f

def z342 : W := mkw 0x0000024010081100 0x0000004802010220 0x0800000030381384 0x0100000006070270

def z343 : W := mkw 0x100120012df7e6aa 0x4200240025befcd5 0x180000003ffffffc 0x0300000007ffffff

def z344 : W := mkw 0x0100140000000000 0x0020028000000000 0xc7001e0000000002 0x78e003c000000000

def z345 : W := mkw 0x0cb00bc019681703 0x01960178032d02e0 0x88f007c031f81386 0xd11e00f8063f0270

def z346 : W := mkw 0x124fe0056497e0e0 0x2249fc00ac92fc1c 0x200fe00fc007e061 0x0401fc01f800fc0c

def z347 : W := mkw 0x27feddba80400602 0x04ffdbb7500800c0 0xffffffffc1c01f87 0xfffffffff83803f0

def z348 : W := mkw 0x224fe27ff01c71e0 0x2449fc4ffe038e3c 0xa81fe7fff03cf3e7 0xd503fcfffe079e7c

def z349 : W := mkw 0x036e9d3b06c3aebe 0xc06dd3a760d875d7 0xffec99330fc7ffff 0xbffd932661f8ffff

def z350 : W := mkw 0x0020090000400602 0x00040120000800c0 0x50e0180001c00c00 0x2a1c030000380180

def z351 : W := mkw 0x020b000024060000 0x004160000480c000 0xf70f18303e071c7f 0x7ee1e30607c0e38f

def z352 : W := mkw 0x00010245700c31e0 0x20002048ae01863c 0xa00307cff00413e7 0x540060f9fe00827c

def z353 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010e1c3c0000000 0x80021c3878000000

def z354 : W := mkw 0x030a142800000000 0x0061428500000000 0x470c183000000000 0x28e1830600000000

def z355 : W := mkw 0x21201fbe92001854 0x842403f7d240030a 0x60001fffc0001c7a 0x0c0003fff800038f

def z356 : W := mkw 0x00010205300430e0 0x00002040a600861c 0xa803870f3004f3e7 0xd50070e1e6009e7c

def z357 : W := mkw 0x0101366d721c79f4 0xa02026cdae438f3e 0xe813fffff03cffff 0xdd027ffffe079fff

def z358 : W := mkw 0x234fd63eb6061854 0x8469fac7d6c0c30a 0xf70ffe3ffe071c7f 0x7ee1ffc7ffc0e38f

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x200007cfc0000002 0x040000f9f8000000

def z360 : W := mkw 0x180122403fffdf07 0x0300244807fffbe0 0x180000003fffff84 0x0300000007fffff0

def z361 : W := mkw 0x0044800000000000 0x0008900000000000 0x80ec800000000001 0xb01d900000000000

def z362 : W := mkw 0x24f4c99380c1a6aa 0x449e9932701834d5 0x08f0e1c3c1c0e380 0x811e1c3878381c70

def z363 : W := mkw 0x080102443f6e1f57 0x8100204887edc3ea 0x180000003fff1ffc 0x0300000007ffe3ff

def z364 : W := mkw 0x00648913000020a0 0x000c912260000414 0xe8ec99330004f3e7 0xbd1d932660009e7c

def z365 : W := mkw 0x069b00002d260000 0x00d3600005a4c000 0x9fff00003fff0005 0xf3ffe00007ffe000

def z366 : W := mkw 0x27ffddbaa4060000 0x04fffbb75480c000 0xf7fffffffe070007 0xfeffffffffc0e000

def z367 : W := mkw 0x1db13fc03fffdf07 0x03b627f807fffbe0 0xdff01fc03fffff86 0xfbfe03f807fffff0

def z368 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x17ff60003ffb0000 0x62ffec0007ff6000

def z369 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x67031e3c3e001c7a 0x4ce063c787c0038f

def z370 : W := mkw 0x00000001000020a0 0x0000000020000414 0x20000103000013e2 0x040000206000027c

def z371 : W := mkw 0x0c9000c009280101 0x0192001801250020 0x001000c000380000 0x0002001800070000

def z372 : W := mkw 0x100122457dbff1e0 0x22002448afb7fe3c 0xb813e7cffffff3e7 0xd7027cf9fffffe7c

def z373 : W := mkw 0x1ffedd800fe38e07 0x03ffdbb001fc71c0 0x57ec18000fc30c00 0x2afd830001f86180

def z374 : W := mkw 0x0064891200000000 0x000c912240000000 0x40ec183000000000 0x281d830600000000

def z375 : W := mkw 0x37feddba8da38000 0x06ffdbb751b47000 0xf7ffffffcfc30003 0xfefffffff9f86000

def z376 : W := mkw 0x00002041401861a0 0x2000040828030c34 0xa810e1c3c03cf3e7 0x95021c3878079e7c

def z377 : W := mkw 0x0000000000000000 0x0000000000000000 0x500c183000030c18 0x2a01830600006183

def z378 : W := mkw 0x1000200009b1c000 0x0200040001363800 0x0800000001f8e000 0x01000000003f1c00

def z379 : W := mkw 0x17dff62c3fb7d854 0x82fbfec587f6fb0a 0x9fffe60c3fffe005 0xf3fffcc187fffc00

def z380 : W := mkw 0x0065ab57701c71e0 0x200cb56aee038e3c 0xe8fffffff03cf3e7 0xfd1ffffffe079e7c

def z381 : W := mkw 0x0000024010081100 0x0000004802010220 0x001006c030380000 0x400200d806070000

def z382 : W := mkw 0x0044800000818000 0x0008900000103000 0x000c80000007e001 0x000190000000fc00

def z383 : W := mkw 0x124fe02c2497c050 0x8249fc058492f80a 0x200fe03c0007e079 0x0401fc078000fc0f

def z384 : W := mkw 0x00012245761e79f4 0xa0002448aec3cf3e 0x180000003e3ffffc 0x0300000007c7ffff

def z385 : W := mkw 0x0000000000000000 0x0000000000000000 0x801007c000000002 0xd00200f800000000

def z386 : W := mkw 0x0db01dc009680703 0x01b603b8012d00e0 0xcff01fc001f80382 0xf9fe03f8003f0070

def z387 : W := mkw 0x00212b57705c77ea 0x6004256aee0b8efd 0xe813fffff03cffff 0xdd027ffffe079fff

def z388 : W := mkw 0x06dec00000818000 0x00dbd80000103000 0x9fffe00001c7e005 0xf3fffc000038fc00

def z389 : W := mkw 0x3ffffffabfffdf07 0x07ffffff57fffbe0 0xffffffffffffff87 0xfffffffffffffff0

def z390 : W := mkw 0x0b2b1fec364e1f57 0x816563fd86c9c3ea 0xf70f1ffc3e071fff 0x7ee1e3ff87c0e3ff

def z391 : W := mkw 0x0d9014800b200805 0x01b2029001640100 0x070000000e000000 0x00e0000001c00000

def z392 : W := mkw 0x030b366c761e5954 0xa06166cd8ec3cb2a 0x071366ccfe380000 0x40e26cd99fc70000

def z393 : W := mkw 0x27fffffff61e79f4 0xa4fffffffec3cf3e 0xfffffffffe3fffff 0xffffffffffc7ffff

def z394 : W := mkw 0x1490600009304000 0x02920c0001260800 0x0010600000380000 0x00020c0000070000

def z395 : W := mkw 0x0001020536c7befe 0xc0002040a6d8f7df 0x180000003fc7fffc 0x0300000007f8ffff

def z396 : W := mkw 0x020a000000000000 0x0041400000000000 0x870f000000000001 0x70e1e00000000000

def z397 : W := mkw 0x030b366c761e5954 0xa06166cd8ec3cb2a 0xf71f7efcfe3f1c7f 0x7ee3efdf9fc7e38f

def z398 : W := mkw 0x09201fc01b681f07 0x012403f8036d03e0 0x58001fc03ff81f86 0x0b0003f807ff03f0

def z399 : W := mkw 0x030a142800000000 0x0061428500000000 0xe71fffffc0000003 0xfce3fffff8000000

def z400 : W := mkw 0x0db01f801b601e07 0x01b603f0036c03c0 0xd7e01e003fc01c06 0x7afc03c007f80380

def z401 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xe70f1e3c3e000003 0x7ce1e3c787c00000

def z402 : W := mkw 0x026f893f24c7a6fa 0xc04df127e498f4df 0xf8ef993f01c7ffff 0xbf1df327e038ffff

def z403 : W := mkw 0x030b162d36c7befe 0xc06162c5a6d8f7df 0xff0f1e3c3fc7ffff 0x7fe1e3c787f8ffff

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000810300000003 0x9400102060000000

def z405 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xc7fc1ff000000002 0xf8ff83fe00000000

def z406 : W := mkw 0x27fffdbfe01460e0 0x24ffffb7fc028c1c 0xe7ffffffc004e063 0xfcfffffff8009c0c

def z407 : W := mkw 0x0db11fc43f6e1f57 0x81b623f887edc3ea 0xdff01fc03fff1ffe 0xfbfe03f807ffe3ff

def z408 : W := mkw 0x27ffdfbeb0041040 0x04fffbf7d6008208 0xe7fffffff0041067 0xfcfffffffe00820c

def z409 : W := mkw 0x0491200029344000 0x0092240005268800 0x9ff3e0003ffce005 0xf3fe7c0007ff9c00

def z410 : W := mkw 0x030b162c30041040 0x006162c586008208 0xe70f1e3c30041067 0x7ce1e3c78600820c

def z411 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x201367cff03813e2 0x44026cf9fe07027c

def z412 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x47ff7efcc0000000 0x68ffefdf98000000

def z413 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0xe71f7efcc0000003 0x7ce3efdf98000000

def z414 : W := mkw 0x0000020410001040 0x0000004082000208 0x2000060c00001062 0x040000c18000020c

def z415 : W := mkw 0x0db01fc55b683fe7 0x21b603f8ab6d07fc 0xfff01fcffff81fe6 0xfffe03f9ffff03fc

def z416 : W := mkw 0x030b366d761e79f4 0xa06166cdaec3cf3e 0xaf13e7cffe3cf3e7 0xd5e27cf9ffc79e7c

def z417 : W := mkw 0x0020090000400602 0x00040120000800c0 0x08e0010001c00380 0x811c002000380070

def z418 : W := mkw 0x279b76edf01c71e0 0x24f36eddbe038e3c 0xaf13e7cff03cf3e7 0xd5e27cf9fe079e7c

def z419 : W := mkw 0x004480130081a0a8 0x4008900260103415 0x000080030000e000 0x0000100060001c00

def z420 : W := mkw 0x0000000006020814 0x8000000000c04102 0x100000000e030c18 0x0200000001c06183

def z421 : W := mkw 0x07dfd62c36061854 0x80fbfac586c0c30a 0xf7fffe3c3e071c7f 0xfeffffc787c0e38f

def z422 : W := mkw 0x00000001000020a0 0x0000000020000414 0x200080030004e061 0x0400100060009c0c

def z423 : W := mkw 0x16ffe9122df7c60a 0x42dffd2245bef8c1 0xdffff8303fffec1d 0xfbffff0607fffd83

def z424 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xa8e0810301c4f3e7 0x951c102060389e7c

def z425 : W := mkw 0x05b01fc010081100 0x00b603f802010220 0xcff01fc030381386 0xf9fe03f806070270

def z426 : W := mkw 0x224ec03b8081a0a8 0x4449d80770103415 0x200fe03fc007e079 0x0401fc07f800fc0f

def z427 : W := mkw 0x1fffffec3fffdf57 0x83fffffd87fffbea 0xfffffffc3fffffff 0xffffffff87ffffff

def z428 : W := mkw 0x0100160012001804 0x002002c002400300 0x070006003e000000 0x40e000c007c00000

def z429 : W := mkw 0x220a402880000000 0x0441480510000000 0x0003600cc0000000 0x00006c0198000000

def z430 : W := mkw 0x04b0090009600602 0x00960120012c00c0 0xdff019003ff81f86 0xfbfe032007ff03f0

def z431 : W := mkw 0x00012045601c61e0 0x20002408ac038c3c 0x2813e1cfc03ce3e1 0x85027c39f8079c7c

def z432 : W := mkw 0x14d4e00009b1c000 0x029a9c0001363800 0x9ff0e0003ff8e004 0xf3fe1c0007ff1c00

def z433 : W := mkw 0x030a142806020814 0x8061428500c04102 0xf70f1e3c0e030c1b 0x7ee1e3c781c06183

def z434 : W := mkw 0x0065ab5770ddf7ea 0x600cb56aee1bbefd 0xf8ec993331ffffff 0xbf1d9326663fffff

def z435 : W := mkw 0x37fffdbaadb7c000 0x06ffffb755b6f800 0xdffff8303fffe005 0xfbffff0607fffc00

def z436 : W := mkw 0x00012041601c61a0 0x200024082c038c34 0x8813e1c3f03ce385 0xd1027c387e079c70

def z437 : W := mkw 0x27ba5da880000000 0x04f74bb510000000 0xc7f37fccc0000002 0xf8fe6ff998000000

def z438 : W := mkw 0x00012005601460e0 0x20002400ac028c1c 0xa013e7cfc004e063 0xd4027cf9f8009c0c

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x880080000004e005 0x9100100000009c00

def z440 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0x00e0000001c00000 0x001c000000380000

def z441 : W := mkw 0x100000000da38000 0x0200000001b47000 0x100000000fc30000 0x0200000001f86000

def z442 : W := mkw 0x030b366d761e79f4 0xa06166cdaec3cf3e 0xff0f1e3c3e3fffff 0x7fe1e3c787c7ffff

def z443 : W := mkw 0x080002401b681f07 0x01000048036d03e0 0x981007c03ff81f86 0xd30200f807ff03f0

def z444 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x081366ccf03cf3e4 0x41026cd99e079e7c

def z445 : W := mkw 0x00012244701c5140 0x200024488e038a28 0xa013e7cff0380003 0xd4027cf9fe070000

def z446 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xe7ec993300000003 0xbcfd932660000000

def z447 : W := mkw 0x120b600024164000 0x02416c000482c800 0x0003600000000000 0x00006c0000000000

def z448 : W := mkw 0x210014a880000000 0x0420029510000000 0x000006ccc0000000 0x000000d998000000

def z449 : W := mkw 0x0d9016c01b281905 0x01b202d803650320 0x9ff006c03ff80004 0xf3fe00d807ff0000

def z450 : W := mkw 0x0fba1fe81b681f07 0x01f743fd036d03e0 0xffff1ffc3ff81f87 0xffffe3ff87ff03f0

def z451 : W := mkw 0x030b166d760e39f4 0xa06162cdaec1c73e 0xf70f1ffffe071fff 0x7ee1e3ffffc0e3ff

def z452 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x071fe0003e3fe001 0x40e3fc0007c7fc00

def z453 : W := mkw 0x080002411be9bfaf 0x41000048237d37f5 0x180000003ffffffc 0x0300000007ffffff

def z454 : W := mkw 0x2000003a80000000 0x0400000750000000 0x2000003fc0000000 0x04000007f8000000

def z455 : W := mkw 0x030b162d360638f4 0x806162c5a6c0c71e 0xff0f9f3f3e07ffff 0xffe1f3e7e7c0ffff

def z456 : W := mkw 0x16fec9130de3a6aa 0x42dfd92261bc74d5 0xffec99330fc7ffff 0xbffd932661f8ffff

def z457 : W := mkw 0x2ffedffa9b681f07 0x05ffdbff536d03e0 0xdffc1ff03ff81f86 0xfbff83fe07ff03f0

def z458 : W := mkw 0x179b762c3f365854 0x82f36ec587e6cb0a 0xf71f7e3c3e3f1c7f 0x7ee3efc787c7e38f

def z459 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x0810e1c3f03cf3e4 0x81021c387e079e7c

def z460 : W := mkw 0x05b01d8000000000 0x00b603b000000000 0xe7f3ffcfc0000003 0xfcfe7ff9f8000000

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0xd000180000001c06 0x3a00030000000380

def z462 : W := mkw 0x24f4c99280000000 0x049e993250000000 0xe0fcf9f3c0000003 0xbc1f9f3e78000000

def z463 : W := mkw 0x00012005601460e0 0x20002400ac028c1c 0xa803e10fc004f3e7 0x95007c21f8009e7c

def z464 : W := mkw 0x06fec91200000000 0x00dfd92240000000 0xe7fff93300000003 0xfcffff2660000000

def z465 : W := mkw 0x00200913004026aa 0x40040122600804d5 0xe80099330004ffff 0x9d00132660009fff

def z466 : W := mkw 0x36ffe992adb7c000 0x06dffd3255b6f800 0x9fffe1c3ffffe005 0xf3fffc387ffffc00

def z467 : W := mkw 0x0cb029c1497867a3 0x21960538292f0cf4 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z468 : W := mkw 0x0001020430041040 0x0000204086008208 0x0003060c30000000 0x400060c186000000

def z469 : W := mkw 0x27ba5dba80000000 0x04f74bb750000000 0x67137fffc0000002 0x4ce26ffff8000000

def z470 : W := mkw 0x006489130081a0a8 0x400c912260103415 0xe0ec99330007e07b 0xbc1d93266000fc0f

def z471 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x0813e7cff038e380 0xc1027cf9fe071c70

def z472 : W := mkw 0x01013645721c79e4 0x202026c8ae438f3c 0xff13ffcffe3cffe7 0xffe27ff9ffc79ffc

def z473 : W := mkw 0x00200b4010481702 0x00040168020902e0 0xd8f01fc031f81f86 0xfb1e03f8063f03f0

def z474 : W := mkw 0x00012244701c5140 0x200024488e038a28 0x8813e6ccf03ce005 0xd1027cd99e079c00

def z475 : W := mkw 0x0db01fc01b281905 0x01b603f803650320 0xc7f01fc03e380002 0xf8fe03f807c70000

def z476 : W := mkw 0x37fffdbaa497c000 0x06ffffb75492f800 0xe7ffffffc007e003 0xfcfffffff800fc00

def z477 : W := mkw 0x06dec00009200000 0x00dbd80001240000 0x9fffe0003ff80005 0xf3fffc0007ff0000

def z478 : W := mkw 0x002009120040060a 0x40040122400800c1 0x4000183000000c18 0x0800030600000183

def z479 : W := mkw 0x079b162c3f261854 0x80f362c587e4c30a 0xffff1e3c3fff1c7f 0xffffe3c787ffe38f

def z480 : W := mkw 0x16dfe0056db7e0e0 0x22dbfc00adb6fc1c 0xbfffe00fffffe065 0xf7fffc01fffffc0c

def z481 : W := mkw 0x0db13fc57b7c7fe7 0x21b627f8af6f8ffc 0xdff01fc03ffcffe6 0xfbfe03f807ff9ffc

def z482 : W := mkw 0x0044800100c1a6aa 0x40089000201834d5 0x98ec800001c7fffd 0xb31d90000038ffff

def z483 : W := mkw 0x030b142c24060050 0x806162858480c00a 0xe70f1e3c0007007b 0x7ce1e3c78000e00f

def z484 : W := mkw 0x05f49d9200000000 0x00be93b240000000 0xe7fc9ff300000003 0xfcff93fe60000000

def z485 : W := mkw 0x27feddbb804026aa 0x44ffdbb7700804d5 0xe7ffffffc0001ffb 0xfcfffffff80003ff

def z486 : W := mkw 0x324fe03aa497c000 0x0649fc075492f800 0x200fe03fc007e001 0x0401fc07f800fc00

def z487 : W := mkw 0x0100164012081904 0x002002c802410320 0xdf101fc03e381f86 0xfbe203f807c703f0

def z488 : W := mkw 0x0db13fc03b7c5f07 0x01b627f8076f8be0 0xdff3ffc03ffcff87 0xfbfe7ff807ff9ff0

def z489 : W := mkw 0x234ed43a80000000 0x0469da8750000000 0xe70ffe3fc0000003 0x7ce1ffc7f8000000

def z490 : W := mkw 0x27feddba86020814 0x84ffdbb750c04102 0x57ec18300e030c18 0x2afd830601c06183

def z491 : W := mkw 0x224fc03ea4060050 0x8449f807d480c00a 0x200fe03fc0070079 0x0401fc07f800e00f

def z492 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xa803060c303cf3e7 0x550060c186079e7c

def z493 : W := mkw 0x080122457b7c7fe7 0x21002448af6f8ffc 0xb813e7cffffcffe7 0xd7027cf9ffff9ffc

def z494 : W := mkw 0x0000200000104000 0x0000040000020800 0x0810e0000038e000 0x81021c0000071c00

def z495 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xd7031e0c3e001c06 0x7ae063c187c00380

def z496 : W := mkw 0x0f9b16ec3f2e1955 0x81f362dd87e5c32a 0x071306cc3e380000 0x40e260d987c70000

def z497 : W := mkw 0x16dfe0002497c000 0x02dbfc000492f800 0x87ffe0000007e001 0xf0fffc000000fc00

def z498 : W := mkw 0x0db01fc11b683fa7 0x01b603f8236d07f4 0xfff09fc33ffcffe7 0xfffe13f867ff9ffc

def z499 : W := mkw 0x00000001000020a0 0x0000000020000414 0x080000000004f3e4 0x0100000000009e7c

def z500 : W := mkw 0x169b62457d3e71e0 0x22d36c48afa7ce3c 0xaf13e7cffe3cf3e7 0xd5e27cf9ffc79e7c

def z501 : W := mkw 0x379b74a8ad364000 0x06f36e9515a6c800 0x071366ccfe380000 0x40e26cd99fc70000

def z502 : W := mkw 0x124fe0002497c000 0x0249fc000492f800 0x881fe000303fe005 0xd103fc000607fc00

def z503 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xa8008103303cf3e7 0x9500102066079e7c

def z504 : W := mkw 0x1065a9132df7e6aa 0x420cb52265befcd5 0xf8ec99333fffffff 0xbf1d932667ffffff

def z505 : W := mkw 0x16dfe0132db7e0a8 0x42dbfc0265b6fc15 0xbfffe0333fffe07d 0xf7fffc0667fffc0f

def z506 : W := mkw 0x0001020430041040 0x0000204086008208 0xa013e7cff0041067 0xd4027cf9fe00820c

def z507 : W := mkw 0x16dec0000da38000 0x02dbd80001b47000 0x9fec80000fc7e005 0xb3fd900001f8fc00

def z508 : W := mkw 0x0100162c12001854 0x802002c58240030a 0xf7001e3c3e001c7e 0x7ee003c787c0038f

def z509 : W := mkw 0x279b56acb6061854 0x84f36ad596c0c30a 0x071366ccfe000000 0x40e26cd99fc00000

def z510 : W := mkw 0x030a162812001804 0x006142c502400300 0xf70f1e3c3e001c07 0x7ee1e3c787c00380

def z511 : W := mkw 0x14d5e00029b5c000 0x029abc000536b800 0x88f3e00031fce005 0xd11e7c00063f9c00

def z512 : W := mkw 0x2f9a56e89b281905 0x05f34add13650320 0x071366ccfe380000 0x40e26cd99fc70000

def z513 : W := mkw 0x0000004000080100 0x0000000800010020 0x081001c000380380 0x8102003800070070

def z514 : W := mkw 0x0064891200000000 0x000c912240000000 0xf0ec993300071c7f 0xbe1d93266000e38f

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c000000070005 0x320180000000e000

def z516 : W := mkw 0x179b762c3f365854 0x82f36ec587e6cb0a 0x0713660c3e380000 0x40e26cc187c70000

def z517 : W := mkw 0x1ffedfc01feb9f07 0x03ffdbf803fd73e0 0xdffc1fc03ffb1f86 0xfbff83f807ff63f0

def z518 : W := mkw 0x1effe9c02dffc703 0x03dffd3805bff8e0 0x9fffe1c03fffe385 0xf3fffc3807fffc70

def z519 : W := mkw 0x124fe0002497c000 0x0249fc000492f800 0x970fe0003e07e005 0x72e1fc0007c0fc00

def z520 : W := mkw 0x00648b5310c9b7aa 0x400c916a621936f5 0xf8fc9ff331ffffff 0xff1f93fe663fffff

def z521 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x600c99330007fffb 0x0c0193266000ffff

def z522 : W := mkw 0x17dff4282fb7c814 0x82fbfe8505f6f902 0xdffff8303fffec1d 0xfbffff0607fffd83

def z523 : W := mkw 0x0df49fc01be99f07 0x01be93f8037d33e0 0xdffc9fc03fffff87 0xfbff93f807fffff0

def z524 : W := mkw 0x0b0b166c3f6e1f57 0x816162cd87edc3ea 0xff0f1e3c3fff1fff 0x7fe1e3c787ffe3ff

def z525 : W := mkw 0x0001020430041040 0x0000204086008208 0xf00f1e3c30071c7f 0x7e01e3c78600e38f

def z526 : W := mkw 0x21201fffd00831e0 0x242403fffa01063c 0x60001fffc00013e2 0x0c0003fff800027c

def z527 : W := mkw 0x020b002c24060050 0x804160058480c00a 0xf00f183c00071c7f 0x3e01e3078000e38f

def z528 : W := mkw 0x0df49fd31be9bfaf 0x41be93fa637d37f5 0xdff09fc33ff8ff86 0xfbfe13f867ff1ff0

def z529 : W := mkw 0x226ec93b80c1a6aa 0x444dd927701834d5 0xf8eff93fc1c7ffff 0xbf1dff27f838ffff

def z530 : W := mkw 0x00000245500831e0 0x20000048aa01063c 0xa013e7cfc00013e3 0xd4027cf9f800027c

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800010000001386 0x9100002000000270

def z532 : W := mkw 0x0044801200000000 0x0008900240000000 0x200c803300000001 0x0401900660000000

def z533 : W := mkw 0x169b60002db7c000 0x02d36c0005b6f800 0x1f1360003fffe004 0x43e26c0007fffc00

def z534 : W := mkw 0x00200913004026aa 0x40040122600804d5 0x0000010300000380 0x0000002060000070

def z535 : W := mkw 0x00658b1736c7befe 0xc00cb162e6d8f7df 0xf8ec99333fc7ffff 0xbf1d932667f8ffff

def z536 : W := mkw 0x232b1fbeb6061854 0x846563f7d6c0c30a 0xf70f1ffffe071c7f 0x7ee1e3ffffc0e38f

def z537 : W := mkw 0x00012005601460e0 0x20002400ac028c1c 0xa813e00ff03ce065 0xd5027c01fe079c0c

def z538 : W := mkw 0x224ec03a80000000 0x0449d80750000000 0x000c003000000000 0x0001800600000000

def z539 : W := mkw 0x024f803f2487a0f8 0xc049f007e490f41f 0x200f803f0007e079 0x0401f007e000fc0f

def z540 : W := mkw 0x16dfe0002d364000 0x02dbfc0005a6c800 0x87ffe0003e380001 0xf0fffc0007c70000

def z541 : W := mkw 0x21649dbb80c1a6aa 0x442c93b7701834d5 0xf8ec9fffc1c7ffff 0xbf1d93fff838ffff

def z542 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x270f063c3e070079 0x44e1e0c787c0e00f

def z543 : W := mkw 0x09201fd312483faf 0x412403fa624907f5 0x60001ff300001ffa 0x0c0003fe600003ff

def z544 : W := mkw 0x17fffd802db7c000 0x02ffffb005b6f800 0xdfffffc03fffe007 0xfbfffff807fffc00

def z545 : W := mkw 0x0db11fc43b6c1f47 0x01b623f8876d83e8 0xfff31fcc3ffc1fe7 0xfffe63f987ff83fc

def z546 : W := mkw 0x05b01d8000000000 0x00b603b000000000 0x47e0180000000000 0x28fc030000000000

def z547 : W := mkw 0x25f4ddba80000000 0x04be9bb750000000 0x60f0ffffc0000002 0x8c1e1ffff8000000

def z548 : W := mkw 0x0db13fc47b7c5f47 0x21b627f88f6f8be8 0xdff37fccfff81f86 0xfbfe6ff99fff03f0

def z549 : W := mkw 0x01201f3f12403efe 0xc02403e7e24807df 0x60001f3f00001ffa 0x0c0003e7e00003ff

def z550 : W := mkw 0x1fdff6c03fbfd905 0x03fbfed807f7fb20 0x9fffe6c03fffe005 0xf3fffcd807fffc00

def z551 : W := mkw 0x16ffe9122db7c000 0x02dffd2245b6f800 0xfffff9333fffe007 0xffffff2667fffc00

def z552 : W := mkw 0x0cb00bc01b681f07 0x01960178036d03e0 0x18f001c03ff81f84 0x831e003807ff03f0

def z553 : W := mkw 0x0101162c36061854 0x802022c586c0c30a 0x70001e3c3e071c7e 0x0e0003c787c0e38f

def z554 : W := mkw 0x1ffffd802ff7ce07 0x03ffffb005fef9c0 0xdffff8003fffec05 0xfbffff0007fffd80

def z555 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xfffff8303ffffc7f 0xffffff0607ffff8f

def z556 : W := mkw 0x0020090000000000 0x0004012000000000 0xc0e0190000000002 0xb81c032000000000

def z557 : W := mkw 0x26fec99280000000 0x04dfd93250000000 0x87ffe1c3c0000001 0xf0fffc3878000000

def z558 : W := mkw 0x09201fc012481f07 0x012403f8024903e0 0xc8101fc030381f86 0xd90203f8060703f0

def z559 : W := mkw 0x000000010081a0a8 0x4000000020103415 0x000000000007e078 0x000000000000fc0f

def z560 : W := mkw 0x26fec9ba80000000 0x04dfd93750000000 0x20ffe1ffc0000001 0x841ffc3ff8000000

def z561 : W := mkw 0x01201d8000000000 0x002403b000000000 0x40001fc000000002 0x080003f800000000

def z562 : W := mkw 0x0100140002000804 0x0020028000400100 0x570018000e000c00 0x2ae0030001c00180

def z563 : W := mkw 0x06dec00000000000 0x00dbd80000000000 0x07ec000000000000 0x20fd800000000000

def z564 : W := mkw 0x07fedd8000000000 0x00ffdbb000000000 0xc7ffffc000000003 0xf8fffff800000000

def z565 : W := mkw 0x37fffdbbadf7e6aa 0x46ffffb775befcd5 0xffffffffffffffff 0xffffffffffffffff

def z566 : W := mkw 0x1045a0002db7c000 0x0208b40005b6f800 0x98ec80003fffe005 0xb31d900007fffc00

def z567 : W := mkw 0x030a142806020814 0x8061428500c04102 0xf70c18300e071c7f 0x3ee1830601c0e38f

def z568 : W := mkw 0x0000020010001000 0x0000004002000200 0x8000060030001006 0x500000c006000200

def z569 : W := mkw 0x080000000b600e07 0x01000000016c01c0 0x100000000fc00c00 0x0200000001f80180

def z570 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x68e0993301c0fffa 0x8d1c132660381fff

def z571 : W := mkw 0x0000000009200000 0x0000000001240000 0x180000003ff80004 0x0300000007ff0000

def z572 : W := mkw 0x00012244701c5140 0x200024488e038a28 0x881367ccf0381386 0xd1026cf99e070270

def z573 : W := mkw 0x0001020436061854 0x8000204086c0c30a 0x000000003e000000 0x0000000007c00000

def z574 : W := mkw 0x0001200020144000 0x0000240004028800 0xa813e7cff03ce007 0xd5027cf9fe079c00

def z575 : W := mkw 0x16dfe2043db7d040 0x02dbfc4087b6fa08 0xbfffe60c3ffff067 0xf7fffcc187fffe0c

def z576 : W := mkw 0x030a142800000000 0x0061428500000000 0xf70f1e3c00071c7f 0x7ee1e3c78000e38f

def z577 : W := mkw 0x00000245500831e0 0x20000048aa01063c 0xa80087cfc004f3e7 0x950010f9f8009e7c

def z578 : W := mkw 0x2fffdffebf6e1f57 0x85fffbffd7edc3ea 0xffffffffffff1fff 0xffffffffffffe3ff

def z579 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xc7fff83000000001 0xf8ffff0600000000

def z580 : W := mkw 0x0020091200000000 0x0004012240000000 0x6000193300000002 0x0c00032660000000

def z581 : W := mkw 0x27fedfbe92001854 0x84ffdbf7d240030a 0xe7ffffffc0001c7b 0xfcfffffff800038f

def z582 : W := mkw 0x0db01fc012481f07 0x01b603f8024903e0 0xc7f01fc000001f82 0xf8fe03f8000003f0

def z583 : W := mkw 0x004480010081a0a0 0x0008900020103414 0xb8ec810301c7f3e7 0xb71d90206038fe7c

def z584 : W := mkw 0x37fffdbaad364000 0x06ffffb755a6c800 0xe7fffffffe380003 0xfcffffffffc70000

def z585 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xe7ef1e3c00000003 0x7cfde3c780000000

def z586 : W := mkw 0x030a162816021814 0x806142c502c04302 0xd70c1e303e031c1e 0x7ae183c607c06383

def z587 : W := mkw 0x0100162c12001854 0x802002c58240030a 0x0000060c00000000 0x000000c180000000

def z588 : W := mkw 0x0490000000000000 0x0092000000000000 0x87f0000000000000 0xf0fe000000000000

def z589 : W := mkw 0x004480130081a0a8 0x4008900260103415 0xb8ec803301c7e07d 0xb71d90066038fc0f

def z590 : W := mkw 0x00012244701c5140 0x200024488e038a28 0x0000000030380000 0x0000000006070000

def z591 : W := mkw 0x0001000024060000 0x000020000480c000 0x100000003e070004 0x0200000007c0e000

def z592 : W := mkw 0x100120002db7c000 0x0200240005b6f800 0x9813e0003fffe005 0xd3027c0007fffc00

def z593 : W := mkw 0x020b022c36061854 0x8041604586c0c30a 0x300f003c3e071c7d 0x0601e00787c0e38f

def z594 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x881007c0303cf3e6 0xd10200f806079e7c

def z595 : W := mkw 0x09213fc5725c7fe7 0x212427f8ae4b8ffc 0xe813ffcff03cffe7 0xdd027ff9fe079ffc

def z596 : W := mkw 0x0000000000818000 0x0000000000103000 0x1800000001c7e004 0x030000000038fc00

def z597 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0x0700000000000000 0x00e0000000000000

def z598 : W := mkw 0x0100142802000814 0x8020028500400102 0x4000183000000c18 0x0800030600000183

def z599 : W := mkw 0x0fbb1fac3f661e57 0x81f763f587ecc3ca 0xf7ef1e3c3fc71c7f 0x7efde3c787f8e38f

def z600 : W := mkw 0x24f5ebd7f01c71e0 0x249ebd7afe038e3c 0xa8f3e7cff03cf3e7 0xd51e7cf9fe079e7c

def z601 : W := mkw 0x16dfe2403dbfd100 0x02dbfc4807b7fa20 0x9fffe7c03ffff387 0xf3fffcf807fffe70

def z602 : W := mkw 0x0101160432041844 0x002022c086408308 0xf7031e0c3e041c67 0x7ee063c187c0838c

def z603 : W := mkw 0x030b362d761678f4 0xa06166c5aec2cf1e 0xf70ffe3ffe07fc7f 0x7ee1ffc7ffc0ff8f

def z604 : W := mkw 0x0020090000400602 0x00040120000800c0 0x4000190000001f82 0x08000320000003f0

def z605 : W := mkw 0x0064890000c18602 0x000c9120001830c0 0xd8ec990001c7ff87 0xbb1d93200038fff0

def z606 : W := mkw 0x020b200024164000 0x004164000482c800 0x9f1fe0003e3fe005 0xf3e3fc0007c7fc00

def z607 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x17efe0000fc7e001 0x22fdfc0001f8fc00

def z608 : W := mkw 0x0000000000000000 0x0000000000000000 0xe00c183000000003 0x3c01830600000000

def z609 : W := mkw 0x17ffff3f3ff7fefe 0xc2ffffe7e7feffdf 0xffffff3f3fffffff 0xffffffe7e7ffffff

def z610 : W := mkw 0x020b2245741e71e0 0x20416448ae83ce3c 0xbf1fe7cffe3ff3e7 0xf7e3fcf9ffc7fe7c

def z611 : W := mkw 0x37fefdba89b1c000 0x06ffdfb751363800 0xefffffffc1f8e003 0xfdfffffff83f1c00

def z612 : W := mkw 0x08648b531be9bfaf 0x410c916a637d37f5 0xf8ec99333fffffff 0xbf1d932667ffffff

def z613 : W := mkw 0x16ffeb577dfff7ea 0x62dffd6aefbffefd 0xffffffffffffffff 0xffffffffffffffff

def z614 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0xd8ec983001c7ec1d 0xbb1d93060038fd83

def z615 : W := mkw 0x032b1f3f36463efe 0xc06563e7e6c8c7df 0xf70f1f3f3e071fff 0x7ee1e3e7e7c0e3ff

def z616 : W := mkw 0x1edfe2403fffdf07 0x03dbfc4807fffbe0 0x9fffe0003fffff85 0xf3fffc0007fffff0

def z617 : W := mkw 0x0001220430145040 0x0000244086028a08 0xa813e60c303cf067 0xd5027cc186079e0c

def z618 : W := mkw 0x0100142800000000 0x0020028500000000 0x60001e3c00000002 0x0c0003c780000000

def z619 : W := mkw 0x124fe0002db7c000 0x0249fc0005b6f800 0x180fe0003fffe005 0x0301fc0007fffc00

def z620 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x48f01fc001f81f82 0x891e03f8003f03f0

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x8810000030380004 0xd102000006070000

def z622 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x8813e000303cf3e5 0xd1027c0006079e7c

def z623 : W := mkw 0x27fffffff0ddf7ea 0x64fffffffe1bbefd 0xfffffffff1ffffff 0xfffffffffe3fffff

def z624 : W := mkw 0x0000204040184100 0x2000040808030820 0x001060c0c0380000 0x00020c1818070000

def z625 : W := mkw 0x00002245501871e0 0x20000448aa030e3c 0x2810e7cfc038f3e2 0x85021cf9f8071e7c

def z626 : W := mkw 0x0065a91320d5e6aa 0x400cb522641abcd5 0xf8fff93331ffffff 0xff1fff26663fffff

def z627 : W := mkw 0x020b000024060000 0x004160000480c000 0x070300003e000000 0x40e0600007c00000

def z628 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x1703060c3e071c7c 0x42e060c187c0e38f

def z629 : W := mkw 0x0100160012001804 0x002002c002400300 0x40001e0000001c02 0x080003c000000380

def z630 : W := mkw 0x036e9d3a00000000 0x006dd3a740000000 0xe7ef9f3f00000003 0xfcfdf3e7e0000000

def z631 : W := mkw 0x0001200020144000 0x0000240004028800 0x0003e0000004e001 0x00007c0000009c00

def z632 : W := mkw 0x0df49d930be1aeaf 0x41be93b2617c35d5 0xffec99330fc7ffff 0xbffd932661f8ffff

def z633 : W := mkw 0x0000002c00000050 0x800000058000000a 0x2000003c00000078 0x040000078000000f

def z634 : W := mkw 0x00648913004026aa 0x400c9122600804d5 0xe0ec993300001ffb 0xbc1d9326600003ff

def z635 : W := mkw 0x00648b5750c9b7ea 0x600c916aea1936fd 0xf8ec9fffc1c7ffff 0xbf1d93fff838ffff

def z636 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x47101fc03e381f82 0x48e203f807c703f0

def z637 : W := mkw 0x00010244300c1140 0x0000204886018228 0xa81307cc303c13e7 0xd50260f98607827c

def z638 : W := mkw 0x0044801300c1a6aa 0x40089002601834d5 0x380c803301c7fffd 0x070190066038ffff

def z639 : W := mkw 0x27fffffef01c5140 0x24ffffffde038a28 0xe7fffffff0380003 0xfcfffffffe070000

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000071c7c 0x020000000000e38f

def z641 : W := mkw 0x020b002c24060050 0x804160058480c00a 0x0003000c00000000 0x0000600180000000

def z642 : W := mkw 0x0490000009200000 0x0092000001240000 0x071000003e380000 0x40e2000007c70000

def z643 : W := mkw 0x16dfe0416dbfe1a0 0x22dbfc082db7fc34 0x9fffe1c3ffffe385 0xf3fffc387ffffc70

def z644 : W := mkw 0x00012240301c5100 0x0000244806038a20 0x8813e7c0303cf387 0xd1027cf806079e70

def z645 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0xd8ec193001c31f9e 0xbb1d8326003863f3

def z646 : W := mkw 0x0101162c32041854 0x802022c58640830a 0xe0031e3c30041c7f 0x5c0063c78600838f

def z647 : W := mkw 0x04b0098000000000 0x0096013000000000 0x00f001c000000000 0x801e003800000000

def z648 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x970f060c3e070005 0x72e1e0c187c0e000

def z649 : W := mkw 0x020b226d741e71f0 0xa041644dae83ce3e 0xa81fe7fff03ff3ff 0xd503fcfffe07fe7f

def z650 : W := mkw 0x0044800000818000 0x0008900000103000 0xf8ec983001c7fc7f 0xbf1d93060038ff8f

def z651 : W := mkw 0x232a1dba80000000 0x046543b750000000 0xe70f1fffc0000003 0x7ce1e3fff8000000

def z652 : W := mkw 0x04f4891309e1a6aa 0x409e9122613c34d5 0xfffc99333fffffff 0xffff932667ffffff

def z653 : W := mkw 0x100122043fb7d854 0x8200244087f6fb0a 0x180000003ffffc7c 0x0300000007ffff8f

def z654 : W := mkw 0x0020090100c1a6aa 0x40040120201834d5 0xd8e0190001c7fffe 0xbb1c03200038ffff

def z655 : W := mkw 0x27feddbb800020a0 0x04ffdbb770000414 0xefffffffc004f3e7 0xfdfffffff8009e7c

def z656 : W := mkw 0x0045a245709df1e0 0x2008b448ae13be3c 0xb8ffe7cff1fff3e7 0xf71ffcf9fe3ffe7c

def z657 : W := mkw 0x21201dbb804026aa 0x442403b7700804d5 0x60001fffc0001ffa 0x0c0003fff80003ff

def z658 : W := mkw 0x0000020012001804 0x0000004002400300 0x100000003e001c04 0x0200000007c00380

def z659 : W := mkw 0x020a002800000000 0x0041400500000000 0x200f003c00000001 0x0401e00780000000

def z660 : W := mkw 0x0045a0176095e0e8 0x6008b402ec12bc1d 0x200fe03fc007e079 0x0401fc07f800fc0f

def z661 : W := mkw 0x034f962c36879854 0x8069f2c586d0f30a 0xffef9e3c3fc7fc7f 0xfffdf3c787f8ff8f

def z662 : W := mkw 0x37ffffbebfb7d854 0x86fffff7d7f6fb0a 0xfffffffffffffc7f 0xffffffffffffff8f

def z663 : W := mkw 0x0000000000000000 0x0000000000000000 0x98e0000001c00004 0xb31c000000380000

def z664 : W := mkw 0x2ffeddfa89680703 0x05ffdbbf512d00e0 0xefffffffc1f80383 0xfdfffffff83f0070

def z665 : W := mkw 0x226ec93a80000000 0x044dd92750000000 0xe0eff93fc0000003 0xbc1dff27f8000000

def z666 : W := mkw 0x1f9b76c03f3e5905 0x03f36ed807e7cb20 0x071366c03e380000 0x40e26cd807c70000

def z667 : W := mkw 0x0000024010081100 0x0000004802010220 0xa813e7cff0381387 0xd5027cf9fe070270

def z668 : W := mkw 0x0000024450081140 0x200000488a010228 0x000006ccc0000000 0x000000d998000000

def z669 : W := mkw 0x030b142826060814 0x8061628504c0c102 0xd70f18303e070c1d 0x7ae1e30607c0e183

def z670 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x47fcf9f3c0000000 0xa8ff9f3e78000000

def z671 : W := mkw 0x08200b401b681f07 0x01040168036d03e0 0xd8e019003ff81f86 0xbb1c032007ff03f0

def z672 : W := mkw 0x05b01d8009200000 0x00b603b001240000 0xdff01fc03ff80006 0xfbfe03f807ff0000

def z673 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x58ec993301c3ef98 0xab1d932660387df3

def z674 : W := mkw 0x0020091300c1a6aa 0x40040122601834d5 0x7800193301c7fffe 0x0f0003266038ffff

def z675 : W := mkw 0x09201d8002400e07 0x012403b0004801c0 0x4000180000000c00 0x0800030000000180

def z676 : W := mkw 0x2044c01280000000 0x0408980250000000 0x0000e003c0000000 0x00001c0078000000

def z677 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x98ec810301c7e385 0xb31d90206038fc70

def z678 : W := mkw 0x030b142824060000 0x006162850480c000 0xf70f1e3c3e070007 0x7ee1e3c787c0e000

def z679 : W := mkw 0x030a142806020814 0x8061428500c04102 0x070000000e000000 0x00e0000001c00000

def z680 : W := mkw 0x21649dba80000000 0x042c93b750000000 0xe0ec9fffc0000003 0xbc1d93fff8000000

def z681 : W := mkw 0x14f4e91309f1e6aa 0x429e9d22613e3cd5 0xf8fcf93301ffffff 0xbf1f9f26603fffff

def z682 : W := mkw 0x17dff4282db7c000 0x02fbfe8505b6f800 0xfffffe3c3fffe007 0xffffffc787fffc00

def z683 : W := mkw 0x0db01fd31b683faf 0x41b603fa636d07f5 0xfff01ff33ff81ffe 0xfffe03fe67ff03ff

def z684 : W := mkw 0x27ded4a880000000 0x04fbda9510000000 0x87ffe6ccc0000001 0xf0fffcd998000000

def z685 : W := mkw 0x25f4dd9280000000 0x04be9bb250000000 0xc7f0ffc3c0000002 0xf8fe1ff878000000

def z686 : W := mkw 0x169a40000d220000 0x02d3480001a44000 0x070000000e000000 0x00e0000001c00000

def z687 : W := mkw 0x00658b1730c5b6ea 0x400cb162e618b6dd 0xf8ef9f3f31c7ffff 0xff1df3e7e638ffff

def z688 : W := mkw 0x0101160436061854 0x802022c086c0c30a 0xd7001e003e071c7e 0x7ae003c007c0e38f

def z689 : W := mkw 0x0001200460144040 0x200024008c028808 0x0003600cc0000000 0x00006c0198000000

def z690 : W := mkw 0x1044e0000091c000 0x02089c0000123800 0x0000e0000000e000 0x00001c0000001c00

def z691 : W := mkw 0x0001000424060050 0x800020008480c00a 0x0000000000070078 0x000000000000e00f

def z692 : W := mkw 0x030b160036061804 0x006162c006c0c300 0xd70f1e003e071c07 0x7ae1e3c007c0e380

def z693 : W := mkw 0x26dec03a80000000 0x04dbd80750000000 0xa7ffe03fc0000001 0xf4fffc07f8000000

def z694 : W := mkw 0x100120002497c000 0x020024000492f800 0x000000000007e000 0x000000000000fc00

def z695 : W := mkw 0x21213ffff01c71e0 0x242427fffe038e3c 0xe813fffff03cf3e7 0xdd027ffffe079e7c

def z696 : W := mkw 0x16ffe9132df7e6aa 0x42dffd2265befcd5 0x9fffe1033fffe385 0xf3fffc2067fffc70

def z697 : W := mkw 0x00000013000020a8 0x4000000260000415 0x2000003300000078 0x040000066000000f

def z698 : W := mkw 0x0001020436061854 0x8000204086c0c30a 0xb003060c3e071c7f 0x560060c187c0e38f

def z699 : W := mkw 0x0064891200000000 0x000c912240000000 0x00e0810300000000 0x801c102060000000

def z700 : W := mkw 0x082009c000480703 0x01040138000900e0 0x000001c000000380 0x0000003800000070

def z701 : W := mkw 0x16dfe0012df7e6aa 0x42dbfc0025befcd5 0x9fffe0003ffffffd 0xf3fffc0007ffffff

def z702 : W := mkw 0x030b366d701c71e0 0x206166cdae038e3c 0xef1ffffff03cf3e7 0xfde3fffffe079e7c

def z703 : W := mkw 0x06fec91300c1a6aa 0x40dfd922601834d5 0xfffff93301c7ffff 0xffffff266038ffff

def z704 : W := mkw 0x27fedfffd00831e0 0x24ffdbfffa01063c 0xe7ffffffc00013e3 0xfcfffffff800027c

def z705 : W := mkw 0x17dff66d7fbff9f4 0xa2fbfecdaff7ff3e 0xffffffffffffffff 0xffffffffffffffff

def z706 : W := mkw 0x27feddba80c1860a 0x44ffdbb7501830c1 0x57ec183001c30c18 0x2afd830600386183

def z707 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xcff01fc03ff80382 0xf9fe03f807ff0070

def z708 : W := mkw 0x09201fd752483fef 0x612403faea4907fd 0x60001fffc0001ffa 0x0c0003fff80003ff

def z709 : W := mkw 0x09201f401b681f07 0x012403e8036d03e0 0xdfe01f003ff81f86 0xfbfc03e007ff03f0

def z710 : W := mkw 0x0065ab5670ddd74a 0x600cb56ace1bbae9 0x50ff7efcf1fb0c18 0x6a1fefdf9e3f6183

def z711 : W := mkw 0x030b362c36165854 0x806166c586c2cb0a 0xf71f7e3c3e3f1c7f 0x7ee3efc787c7e38f

def z712 : W := mkw 0x030a3469461a69b4 0xa061468d28c34d36 0x5f1cf9f3ce3bef98 0xabe39f3e79c77df3

def z713 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x770f1e3c0e071c7b 0x2ee1e3c781c0e38f

def z714 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x570f1e3c3e071c7c 0x6ae1e3c787c0e38f

def z715 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2013e7cff03cf3e3 0x44027cf9fe079e7c

def z716 : W := mkw 0x24f5cb96b6061854 0x849eb972d6c0c30a 0x10f0e1c3fe071c7c 0x821e1c387fc0e38f

def z717 : W := mkw 0x030b366c761e5954 0xa06166cd8ec3cb2a 0xff1ffefcfe3ffc7f 0xffe3ffdf9fc7ff8f

def z718 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x1fefe0003fffe005 0x23fdfc0007fffc00

def z719 : W := mkw 0x124fe0056497e0e0 0x2249fc00ac92fc1c 0x000fe0000007e061 0x0001fc000000fc0c

def z720 : W := mkw 0x00000241100831a0 0x0000004822010634 0xa813e7cff03cf3e7 0xd5027cf9fe079e7c

def z721 : W := mkw 0x230b16acb6061854 0x846162d596c0c30a 0xf70f1efcfe071c7f 0x7ee1e3df9fc0e38f

def z722 : W := mkw 0x07ded42800000000 0x00fbda8500000000 0xe7ffffffc0000003 0xfcfffffff8000000

def z723 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fffe7c03fffe007 0xf3fffcf807fffc00

def z724 : W := mkw 0x27ba5dba80000000 0x04f74bb750000000 0xe71f7fffc0000003 0x7ce3effff8000000

def z725 : W := mkw 0x0dd496d31ba9b9ad 0x41ba92da63753735 0x271c86f33e3fe079 0x44e390de67c7fc0f

def z726 : W := mkw 0x2a4ec27a9b681f07 0x0549d84f536d03e0 0x380fe03ffff81f85 0x0701fc07ffff03f0

def z727 : W := mkw 0x31213dbaadb7c000 0x062427b755b6f800 0x78001fffffffe006 0x0f0003fffffffc00

def z728 : W := mkw 0x36dfe03aadb7c000 0x06dbfc0755b6f800 0xbfffe7ffffffe007 0xf7fffcfffffffc00

def z729 : W := mkw 0x27fffffff01c71e0 0x24fffffffe038e3c 0x4fec1830303cf3e4 0x29fd830606079e7c

def z730 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x1fffe0003ffbe000 0xe3fffc0007ff7c00

def z731 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xf813ffcff03cffe7 0xff027ff9fe079ffc

def z732 : W := mkw 0x2ffeddba8f620e17 0x85ffdbb751ec41c2 0xf7ffffffcfc30c1b 0xfefffffff9f86183

def z733 : W := mkw 0x00012240301c5100 0x0000244806038a20 0xa813e7cff03cf387 0xd5027cf9fe079e70

def z734 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8ef9f3f01c7ffff 0xff1df3e7e038ffff

def z735 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x671fffffc0000003 0x4ce3fffff8000000

def z736 : W := mkw 0x09201fed52483ff7 0xa12403fdaa4907fe 0x60001fffc0001ffa 0x0c0003fff80003ff

def z737 : W := mkw 0x124fa0002db7c000 0x0249f40005b6f800 0x9fef80003fffe005 0xf3fdf00007fffc00

def z738 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfff09fc33ff81f87 0xfffe13f867ff03f0

def z739 : W := mkw 0x24f4c99280000000 0x049e993250000000 0x00f3e7cfc0000000 0xc01e7cf9f8000000

def z740 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x68ec993301c7fffb 0x8d1d93266038ffff

def z741 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfff31fcc3ff81f87 0xfffe63f987ff03f0

def z742 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xe81ffffff03cf3e7 0xfd03fffffe079e7c

def z743 : W := mkw 0x04b0090009600602 0x00960120012c00c0 0x9ff001003ff80384 0xf3fe002007ff0070

def z744 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x5fe01fc03ff81f86 0x2bfc03f807ff03f0

def z745 : W := mkw 0x16dee00009b1c000 0x02dbdc0001363800 0x9fffe0003ff8e005 0xf3fffc0007ff1c00

def z746 : W := mkw 0x030b366d761e79f4 0xa06166cdaec3cf3e 0x5f0c18303e3ffffc 0x2be1830607c7ffff

def z747 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xa813e7cff038e383 0xd5027cf9fe071c70

def z748 : W := mkw 0x0db01dc009680703 0x01b603b8012d00e0 0xdff01fc03ff80386 0xfbfe03f807ff0070

def z749 : W := mkw 0x0000000000000000 0x0000000000000000 0xf70c18303e071c7f 0x7ee1830607c0e38f

def z750 : W := mkw 0x030a142806020814 0x8061428500c04102 0xf71fffffce030c1b 0xfee3fffff9c06183

def z751 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x770c1e3c3e071c7e 0x2ee183c787c0e38f

def z752 : W := mkw 0x0000000000000000 0x0000000000000000 0x201367cfc0000002 0x44026cf9f8000000

def z753 : W := mkw 0x0000000000000000 0x0000000000000000 0x2003e7cfc0000003 0x04007cf9f8000000

def z754 : W := mkw 0x0000000000000000 0x0000000000000000 0xe01fffffc0000003 0xfc03fffff8000000

def z755 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x000000000004f3e0 0x0000000000009e7c

def z756 : W := mkw 0x15d4f62c1bb1d854 0x82ba9ec583763b0a 0x68f0fe3c01f8fc7a 0x8d1e1fc7803f1f8f

def z757 : W := mkw 0x0ebb09ec2d6e0753 0x81d7613d85adc0ea 0x28ff01fc01ff03f9 0x851fe03f803fe07f

def z758 : W := mkw 0x27feddba82000814 0x84ffdbb750400102 0xe7ffffffc0000c1b 0xfcfffffff8000183

def z759 : W := mkw 0x024fa03f6497e0f8 0xe049f407ec92fc1f 0x200fe03fc007e079 0x0401fc07f800fc0f

def z760 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfff01fcffff81f86 0xfffe03f9ffff03f0

def z761 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x9ff007c03ff80384 0xf3fe00f807ff0070

def z762 : W := mkw 0x16bb69132d7666aa 0x42d76d2265aeccd5 0x671379333e381ffa 0x4ce26f2667c703ff

def z763 : W := mkw 0x2ffeddba82400e07 0x05ffdbb7504801c0 0xe7ffffffc0000c03 0xfcfffffff8000180

def z764 : W := mkw 0x3ffeddba8fe38e07 0x07ffdbb751fc71c0 0x57ec18300fc30c00 0x2afd830601f86180

def z765 : W := mkw 0x0101160432041844 0x002022c086408308 0xf70f1e3c3e071c7f 0x7ee1e3c787c0e38f

def z766 : W := mkw 0x00012245741e71f0 0xa0002448ae83ce3e 0xa813e7cff03ff3ff 0xd5027cf9fe07fe7f

def z767 : W := mkw 0x0cb00b401b681f07 0x01960168036d03e0 0xdff019003ff81f86 0xfbfe032007ff03f0

def z768 : W := mkw 0x100122457d3e71e0 0x22002448afa7ce3c 0x080000003e3cf3e4 0x0100000007c79e7c

def z769 : W := mkw 0x00012245709df1e0 0x20002448ae13be3c 0x1800000031fff3e4 0x03000000063ffe7c

def z770 : W := mkw 0x14f4c91309e1a6aa 0x429e9922613c34d5 0x08e0810301c0e380 0x811c102060381c70

def z771 : W := mkw 0x26fec9ba80000000 0x04dfd93750000000 0xa0ffe7ffc0000003 0xd41ffcfff8000000

def z772 : W := mkw 0x030a142806020814 0x8061428500c04102 0xf70f1e3c0e071c7f 0x7ee1e3c781c0e38f

def z773 : W := mkw 0x27feddba80c1860a 0x44ffdbb7501830c1 0xe7ffffffc1c00003 0xfcfffffff8380000

def z774 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x18000000303ffffc 0x030000000607ffff

def z775 : W := mkw 0x036f9f3f36c7befe 0xc06df3e7e6d8f7df 0x0fe3870f3fc0e380 0xc1fc70e1e7f81c70

def z776 : W := mkw 0x030b142824060000 0x006162850480c000 0xf70f1e3c3e071c7f 0x7ee1e3c787c0e38f

def z777 : W := mkw 0x00012245741e71e0 0x20002448ae83ce3c 0xb813e7cffe3ff3e7 0xd7027cf9ffc7fe7c

def z778 : W := mkw 0x024fa0002497c000 0x0049f4000492f800 0x9fffe0003fffe005 0xf3fffc0007fffc00

def z779 : W := mkw 0x030b362c36165854 0x806166c586c2cb0a 0xf70ffe3c3e07fc7f 0x7ee1ffc787c0ff8f

def z780 : W := mkw 0x2490408080000000 0x0492081010000000 0xa013e7cfc0000003 0xd4027cf9f8000000

def z781 : W := mkw 0x0000000000000000 0x0000000000000000 0xa813e7cfc0001387 0xd5027cf9f8000270

def z782 : W := mkw 0x00002245501871e0 0x20000448aa030e3c 0xa813e7cfc038f3e3 0xd5027cf9f8071e7c

def z783 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xefffffffc0001387 0xfdfffffff8000270

def z784 : W := mkw 0x0490200009304000 0x0092040001260800 0x9ff0e0003ff8e004 0xf3fe1c0007ff1c00

def z785 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff3ffc03ff81f87 0xfbfe7ff807ff03f0

def z786 : W := mkw 0x0490000009a18000 0x0092000001343000 0x9ff000003fffe004 0xf3fe000007fffc00

def z787 : W := mkw 0x2064c91380c1a6aa 0x440c9922701834d5 0xf8ecf933c1c7ffff 0xbf1d9f267838ffff

def z788 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fffe1003ffff387 0xf3fffc2007fffe70

def z789 : W := mkw 0x080122457bfdffef 0x61002448af7fbffd 0x180000003ffffffc 0x0300000007ffffff

def z790 : W := mkw 0x030b142826060814 0x8061628504c0c102 0xf70f18303e071c7f 0x7ee1e30607c0e38f

def z791 : W := mkw 0x1b6fffc036dfdf07 0x036dfff806dbfbe0 0x400fffc00007ff83 0x0801fff80000fff0

def z792 : W := mkw 0x27ba5da880000000 0x04f74bb510000000 0xe7f3ffcfc0000003 0xfcfe7ff9f8000000

def z793 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x5ff019c03ff81f84 0xabfe033807ff03f0

def z794 : W := mkw 0x27ded4ba80000000 0x04fbda9750000000 0xa71fe7ffc0000003 0xd4e3fcfff8000000

def z795 : W := mkw 0x2064899380c1a6aa 0x440c9132701834d5 0xf8ec99f3c1c7ffff 0xbf1d933e7838ffff

def z796 : W := mkw 0x224ec03a80000000 0x0449d80750000000 0x201fe6ffc0000001 0x4403fcdff8000000

def z797 : W := mkw 0x00012245721c79f4 0xa0002448ae438f3e 0xa813e7cff03cffff 0xd5027cf9fe079fff

def z798 : W := mkw 0x27feddba80c18602 0x04ffdbb7501830c0 0xffffffffc1c7ff87 0xfffffffff838fff0

def z799 : W := mkw 0x27feddba8040060a 0x44ffdbb7500800c1 0xe7ffffffc0000c1b 0xfcfffffff8000183

def z800 : W := mkw 0x27ba5dba80000000 0x04f74bb750000000 0xe7f37fffc0000002 0xfcfe6ffff8000000

def z801 : W := mkw 0x030a142806020814 0x8061428500c04102 0x570c18300e071c7c 0x2ae1830601c0e38f

def z802 : W := mkw 0x0065ab5770ddf7ea 0x600cb56aee1bbefd 0x58ec183031fffffc 0x2b1d8306063fffff

def z803 : W := mkw 0x24f4c99280000000 0x049e993250000000 0xe0ffffffc0000003 0xfc1ffffff8000000

def z804 : W := mkw 0x25b01dba80000000 0x04b603b750000000 0xe7f3ffffc0000003 0xfcfe7ffff8000000

def z805 : W := mkw 0x37feddba8de3860a 0x46ffdbb751bc70c1 0x57ec18300fc30c18 0x2afd830601f86183

def z806 : W := mkw 0x27ba5dba80000000 0x04f74bb750000000 0x071367cfc0000000 0x40e26cf9f8000000

def z807 : W := mkw 0x100122457fbff9f4 0xa2002448aff7ff3e 0x180000003ffffffc 0x0300000007ffffff

def z808 : W := mkw 0x37feddba84838000 0x06ffdbb750907000 0xe7ffffffc0030003 0xfcfffffff8006000

def z809 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff37fccfff81f86 0xfbfe6ff99fff03f0

def z810 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x67f3ffffc0000002 0xccfe7ffff8000000

def z811 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xa8000000303cf3e7 0x1500000006079e7c

def z812 : W := mkw 0x130b762c36165854 0x82616ec586c2cb0a 0xf70f7e3c3e071c7f 0x7ee1efc787c0e38f

def z813 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x8813e7cff03ce385 0xd1027cf9fe079c70

def z814 : W := mkw 0x0c90004009680703 0x01920008012d00e0 0x9ff000003ff80384 0xf3fe000007ff0070

def z815 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fef00003fffe005 0x73fde00007fffc00

def z816 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xff1f1e3c3e3f1c7f 0xffe3e3c787c7e38f

def z817 : W := mkw 0x080122457f7e7ff7 0xa1002448afefcffe 0x180000003ffffffc 0x0300000007ffffff

def z818 : W := mkw 0x2db05fc09b681f07 0x05b60bf8136d03e0 0xdff07fc0fff81f86 0xfbfe0ff81fff03f0

def z819 : W := mkw 0x232a5dba80000000 0x04654bb750000000 0x60037fffc0000002 0x0c006ffff8000000

def z820 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xdffff8303fffec1d 0xfbffff0607fffd83

def z821 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2813e7cff038f3e2 0xc5027cf9fe071e7c

def z822 : W := mkw 0x2db01ffe9b681f57 0x85b603ffd36d03ea 0xfff01ffffff81ffe 0xfffe03ffffff03ff

def z823 : W := mkw 0x069b20002d364000 0x00d3640005a6c800 0x9fffe0003fffe005 0xf3fffc0007fffc00

def z824 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9ffc00003fffe004 0xf3ff800007fffc00

def z825 : W := mkw 0x06dec00009a18000 0x00dbd80001343000 0x9fffe0003fffe005 0xf3fffc0007fffc00

def z826 : W := mkw 0x05b01d8009600602 0x00b603b0012c00c0 0xdff01fc03ff81f86 0xfbfe03f807ff03f0

def z827 : W := mkw 0x279a54a980c1a6aa 0x44f34a95301834d5 0x1f1366ccc1c7fffc 0x43e26cd99838ffff

def z828 : W := mkw 0x1f9b76ec3f3e5955 0x83f36edd87e7cb2a 0x071366cc3e380000 0x40e26cd987c70000

def z829 : W := mkw 0x27feddba89a18000 0x04ffdbb751343000 0xffffffffffffe007 0xfffffffffffffc00

def z830 : W := mkw 0x00012245741e71f0 0xa0002448ae83ce3e 0x08000000303ff3fc 0x010000000607fe7f

def z831 : W := mkw 0x01201d8000000000 0x002403b000000000 0xe013ffcfc0000003 0xdc027ff9f8000000

def z832 : W := mkw 0x09201fc112483fa7 0x012403f8224907f4 0x60001fc300001fe2 0x0c0003f8600003fc

def z833 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf70c18303e071c7f 0x3ee1830607c0e38f

def z834 : W := mkw 0x0044800000818000 0x0008900000103000 0xb8ffe7cfc1c7e007 0xf71ffcf9f838fc00

def z835 : W := mkw 0x0045a245709df1e0 0x2008b448ae13be3c 0x98ec800031fff3e5 0xb31d9000063ffe7c

def z836 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xbfffe0003ffff067 0xf7fffc0007fffe0c

def z837 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x080000003038e380 0x0100000006071c70

def z838 : W := mkw 0x0cb009c009680703 0x01960138012d00e0 0x0ff001c03ff80380 0xc1fe003807ff0070

def z839 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x5ff01ec03ff81f84 0x6bfe03d807ff03f0

def z840 : W := mkw 0x05f49d9200000000 0x00be93b240000000 0xe7ffffffc0000003 0xfcfffffff8000000

def z841 : W := mkw 0x024ec00000000000 0x0049d80000000000 0xa01fe7cfc0000003 0xd403fcf9f8000000

def z842 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x60ffffffc0000003 0x8c1ffffff8000000

def z843 : W := mkw 0x0100162c12001854 0x802002c58240030a 0xf70c1e3c3e071c7f 0x7ee183c787c0e38f

def z844 : W := mkw 0x0590148000000000 0x00b2029000000000 0xa713e7cfc0000003 0xd4e27cf9f8000000

def z845 : W := mkw 0x234ed43a80000000 0x0469da8750000000 0xe71fffffc0000003 0xfce3fffff8000000

def z846 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x770f183c3e071c7d 0x2ee1e30787c0e38f

def z847 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xd70f18303e071c7d 0x7ae1e30607c0e38f

def z848 : W := mkw 0x09201fc552483fe7 0x212403f8aa4907fc 0x40001fc000001fe2 0x080003f8000003fc

def z849 : W := mkw 0x07fedd8000000000 0x00ffdbb000000000 0xe7ffffcfc0000003 0xfcfffff9f8000000

def z850 : W := mkw 0x234ed4ba80000000 0x0469da9750000000 0x200fe6ffc0000001 0x0401fcdff8000000

def z851 : W := mkw 0x14d5e0002db7c000 0x029abc0005b6f800 0x9ff0e0003fffe004 0xf3fe1c0007fffc00

def z852 : W := mkw 0x27feddba80818000 0x04ffdbb750103000 0xf7ffffffc1c30003 0xfefffffff8386000

def z853 : W := mkw 0x0100140002000804 0x0020028000400100 0xf70c18300e071c7f 0x3ee1830601c0e38f

def z854 : W := mkw 0x04d5a00029b5c000 0x009ab4000536b800 0x9fffe0003fffe005 0xf3fffc0007fffc00

def z855 : W := mkw 0x26fec99280000000 0x04dfd93250000000 0xa7ffe7cfc0000003 0xf4fffcf9f8000000

def z856 : W := mkw 0x324fe03fe497e0e0 0x2649fc07fc92fc1c 0x200fe03fc007e061 0x0401fc07f800fc0c

def z857 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xffec99333fc7ffff 0xfffd932667f8ffff

def z858 : W := mkw 0x0cf4a9d349f9e7ab 0x619e953a693f3cf5 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z859 : W := mkw 0x09201fd312483faf 0x412403fa624907f5 0x40001fc300001f82 0x080003f8600003f0

def z860 : W := mkw 0x169b60002d364000 0x02d36c0005a6c800 0x9ff3e0003ffce005 0xf3fe7c0007ff9c00

def z861 : W := mkw 0x224ec03a80000000 0x0449d80750000000 0x200fe7ffc0000003 0x0401fcfff8000000

def z862 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x5ff01fc03ff80f80 0xebfe03f807ff01f0

def z863 : W := mkw 0x27feddba82000804 0x04ffdbb750400100 0xf7ffffffce000c03 0xfefffffff9c00180

def z864 : W := mkw 0x0c9002401b681f07 0x01920048036d03e0 0x1fe000003ff81f84 0x23fc000007ff03f0

def z865 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfff01ff03ff81ffe 0xfffe03fe07ff03ff

def z866 : W := mkw 0x030a162c16021854 0x806142c582c0430a 0xf70f1e3c0e031c7b 0x7ee1e3c781c0638f

def z867 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xb8f3e7cff1fcf3e7 0xf71e7cf9fe3f9e7c

def z868 : W := mkw 0x0db01fec1b681f57 0x81b603fd836d03ea 0xfffc1ffc3fff1fff 0xffff83ff87ffe3ff

def z869 : W := mkw 0x27feddba89200000 0x04ffdbb751240000 0xefffffffc1f80003 0xfdfffffff83f0000

def z870 : W := mkw 0x0cf4899309e1a6ab 0x419e9132613c34d5 0x08e0810301c0e380 0x811c102060381c70

def z871 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xf7ffffffc0030c1b 0xfefffffff8006183

def z872 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xd8ec983001c7fffd 0xbb1d93060038ffff

def z873 : W := mkw 0x080122457b3c79e5 0x21002448af678f3c 0x080000003e3cf3e4 0x0100000007c79e7c

def z874 : W := mkw 0x124fe0176497e0e8 0x6249fc02ec92fc1d 0x200fe03fc007e079 0x0401fc07f800fc0f

def z875 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8eff93fc1c7ffff 0xbf1dff27f838ffff

def z876 : W := mkw 0x00012245705c77e2 0x20002448ae0b8efc 0x1800000031fcffe4 0x03000000063f9ffc

def z877 : W := mkw 0x1001224579bdf1e0 0x22002448af37be3c 0x0800000031fcf3e4 0x01000000063f9e7c

def z878 : W := mkw 0x030b166c760e1954 0xa06162cd8ec1c32a 0xf70f1efcfe071c7f 0x7ee1e3df9fc0e38f

def z879 : W := mkw 0x232a1dba80000000 0x046543b750000000 0xe71fffffc0000003 0xfce3fffff8000000

def z880 : W := mkw 0x0490004009280100 0x0092000801250020 0x9ff001c03ff80384 0xf3fe003807ff0070

def z881 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x87ffe7cfc0000001 0xf0fffcf9f8000000

def z882 : W := mkw 0x2db01ffa9b681f07 0x05b603ff536d03e0 0xfff3fffffff81f87 0xfffe7fffffff03f0

def z883 : W := mkw 0x020b020436061854 0x8041604086c0c30a 0xf70f18303e071c7f 0x7ee1e30607c0e38f

def z884 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xff0f9e3c3e07fc7f 0xffe1f3c787c0ff8f

def z885 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xbfffe00fffffe005 0xf7fffc01fffffc00

def z886 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x00000000303813e0 0x000000000607027c

def z887 : W := mkw 0x16dfe0282db7c000 0x02dbfc0505b6f800 0xbfffe03c3fffe005 0xf7fffc0787fffc00

def z888 : W := mkw 0x08012245725c7fe7 0x21002448ae4b8ffc 0x08000000303cffe4 0x0100000006079ffc

def z889 : W := mkw 0x100122457dfff7ea 0x62002448afbffefd 0x180000003ffffffc 0x0300000007ffffff

def z890 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdfe01e003ff81f86 0x7bfc03c007ff03f0

def z891 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x0813e7cff03cf3e4 0xc1027cf9fe079e7c

def z892 : W := mkw 0x00012245761e79f4 0xa0002448aec3cf3e 0xa813e7cffe3cf3e7 0xd5027cf9ffc79e7c

def z893 : W := mkw 0x0db01fd21b681f0f 0x41b603fa436d03e1 0xdff01ff03ff81f9e 0xfbfe03fe07ff03f3

def z894 : W := mkw 0x36dfe028adb7c000 0x06dbfc0515b6f800 0x9fffe00cffffe005 0xf3fffc019ffffc00

def z895 : W := mkw 0x0490000009600602 0x00920000012c00c0 0x9ff000003ff81f84 0xf3fe000007ff03f0

def z896 : W := mkw 0x020a002800000000 0x0041400500000000 0xa01fe7ffc0000003 0xd403fcfff8000000

def z897 : W := mkw 0x030a162c16021854 0x806142c582c0430a 0x570c18300e031c78 0x2ae1830601c0638f

def z898 : W := mkw 0x27feddba80400602 0x04ffdbb7500800c0 0xffffffffc1c71fff 0xfffffffff838e3ff

def z899 : W := mkw 0x236eddba80000000 0x046ddbb750000000 0xe0efffffc0000003 0xbc1dfffff8000000

def z900 : W := mkw 0x36dfe012adb7c000 0x06dbfc0255b6f800 0x9fffe003ffffe005 0xf3fffc007ffffc00

def z901 : W := mkw 0x27feddba80400602 0x04ffdbb7500800c0 0xefffffffc1c00383 0xfdfffffff8380070

def z902 : W := mkw 0x00012245761e79f4 0xa0002448aec3cf3e 0x080000003e3cf3e4 0x0100000007c79e7c

def z903 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x1ffce0003fffe004 0xa3ff9c0007fffc00

def z904 : W := mkw 0x004480010081a0a0 0x0008900020103414 0xf8ec993301c7ffff 0xbf1d93266038ffff

def z905 : W := mkw 0x00002241501871a0 0x200004482a030e34 0xa813e7cff038f387 0xd5027cf9fe071e70

def z906 : W := mkw 0x0db13d856b746ee7 0x21b627b0ad6e8ddc 0x77e3f80fcfc4ec61 0x2efc7f01f9f89d8c

def z907 : W := mkw 0x36dfe03aadb7c000 0x06dbfc0755b6f800 0x9fffe0303fffe005 0xf3fffc0607fffc00

def z908 : W := mkw 0x27feddba89600602 0x04ffdbb7512c00c0 0xfffffffffff81f87 0xffffffffffff03f0

def z909 : W := mkw 0x179b766c7f3e5954 0xa2f36ecd8fe7cb2a 0x071366ccfe380000 0x40e26cd99fc70000

def z910 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf71f1ffc3e071c7f 0xfee3e3ff87c0e38f

def z911 : W := mkw 0x16dec2455dabb1e0 0x22dbd848abb5763c 0x37ec07cfcfc313e2 0x26fd80f9f9f8627c

def z912 : W := mkw 0x00012245721c79e4 0x20002448ae438f3c 0x180000003e3cffe4 0x0300000007c79ffc

def z913 : W := mkw 0x0db01fe81b681f17 0x81b603fd036d03e2 0xdff01ff03ff81f9e 0xfbfe03fe07ff03f3

def z914 : W := mkw 0x0db01dc00b680f07 0x01b603b8016d01e0 0xdff019c03ff80f84 0xfbfe033807ff01f0

def z915 : W := mkw 0x14d5e00029b5c000 0x029abc000536b800 0x9ff3e0003ffce005 0xf3fe7c0007ff9c00

def z916 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8fc9ff301c7ffff 0xff1f93fe6038ffff

def z917 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0x2713e6cfc0000001 0x44e27cd9f8000000

def z918 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x78ec983301c7fffd 0x2f1d93066038ffff

def z919 : W := mkw 0x05b01f001b601e06 0x00b603e0036c03c0 0xdff01f003ff81f86 0xfbfe03e007ff03f0

def z920 : W := mkw 0x030b366c761e5954 0xa06166cd8ec3cb2a 0xf71ffffffe3f1c7f 0xfee3ffffffc7e38f

def z921 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fffe6ccffffe005 0xf3fffcd99ffffc00

def z922 : W := mkw 0x030b366c761e5954 0xa06166cd8ec3cb2a 0xf70f1e3c3e3f1c7f 0x7ee1e3c787c7e38f

def z923 : W := mkw 0x16dec0000da38000 0x02dbd80001b47000 0xb7ffe7cfcfc30003 0xf6fffcf9f9f86000

def z924 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf71f7efcfe071c7f 0x7ee3efdf9fc0e38f

def z925 : W := mkw 0x279a54ba80000000 0x04f34a9750000000 0x271366ffc0000000 0x44e26cdff8000000

def z926 : W := mkw 0x030b362c36165854 0x806166c586c2cb0a 0xff1ffffffe3ffc7f 0xffe3ffffffc7ff8f

def z927 : W := mkw 0x030b362c36165854 0x806166c586c2cb0a 0xff0f1e3c3e3ffc7f 0x7fe1e3c787c7ff8f

def z928 : W := mkw 0x14d4e00009b1c000 0x029a9c0001363800 0x9ffce0003fffe005 0xf3ff9c0007fffc00

def z929 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x770f1e3c3e031c7a 0x6ee1e3c787c0638f

def z930 : W := mkw 0x0db01d800b600e07 0x01b603b0016c01c0 0xf7f3ffcfcfc00c03 0xfefe7ff9f9f80180

def z931 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf70f9f3f3e071c7f 0xfee1f3e7e7c0e38f

def z932 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xe813fffff03cffff 0xdd027ffffe079fff

def z933 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x67fffeffc0000001 0x6cffffdff8000000

def z934 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdfe019003ff81f86 0xbbfc032007ff03f0

def z935 : W := mkw 0x27ba5dba80000000 0x04f74bb750000000 0xe713ffffc0000003 0xdce27ffff8000000

def z936 : W := mkw 0x0cb00bc019681703 0x01960178032d02e0 0x9ff007c03ff81386 0xf3fe00f807ff0270

def z937 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf70f1ffffe071c7f 0x7ee1e3ffffc0e38f

def z938 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfffc1ff03ff81f87 0xffff83fe07ff03f0

def z939 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x670f1e3c3e071c7b 0x4ce1e3c787c0e38f

def z940 : W := mkw 0x169b60002db7c000 0x02d36c0005b6f800 0x9ff360003fffe004 0xf3fe6c0007fffc00

def z941 : W := mkw 0x030b366c761e5954 0xa06166cd8ec3cb2a 0xff1f7ffcfe3f1fff 0xffe3efff9fc7e3ff

def z942 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x70ec993301c7fffb 0x2e1d93266038ffff

def z943 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xeffffffff0380007 0xfdfffffffe070000

def z944 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xbfffe60c3fffe007 0xf7fffcc187fffc00

def z945 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf70ffe3ffe071c7f 0x7ee1ffc7ffc0e38f

def z946 : W := mkw 0x07ba1da800000000 0x00f743b500000000 0xe7ffffffc0000003 0xfcfffffff8000000

def z947 : W := mkw 0x0000000000000000 0x0000000000000000 0x2013e6cfc0000001 0x44027cd9f8000000

def z948 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2813e7cff03ce3e1 0xc5027cf9fe079c7c

def z949 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xff0f1f3c3e071fff 0xffe1e3e787c0e3ff

def z950 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fffe1c3ffffe005 0xf3fffc387ffffc00

def z951 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8fff93301c7ffff 0xff1fff266038ffff

def z952 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xffffffffc1c00007 0xfffffffff8380000

def z953 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xbf13e7cffe3cf3e7 0xf7e27cf9ffc79e7c

def z954 : W := mkw 0x27feddba86020814 0x84ffdbb750c04102 0xf7ffffffce071c7f 0xfefffffff9c0e38f

def z955 : W := mkw 0x29201fffd2483fe7 0x252403fffa4907fc 0x60001fffc0001fe2 0x0c0003fff80003fc

def z956 : W := mkw 0x16dfe02c2db7c050 0x82dbfc0585b6f80a 0x9fffe00c3fffe005 0xf3fffc0187fffc00

def z957 : W := mkw 0x14d5a0002db7c000 0x029ab40005b6f800 0x9ffc80003fffe005 0xf3ff900007fffc00

def z958 : W := mkw 0x05b01fc019281100 0x00b603f803250220 0xdff01fc03ff81386 0xfbfe03f807ff0270

def z959 : W := mkw 0x0101160436061854 0x802022c086c0c30a 0xf70c1e303e071c7f 0x7ee183c607c0e38f

def z960 : W := mkw 0x0064891200c1860a 0x400c9122401830c1 0xf0ffffffc1c30c1b 0xfe1ffffff8386183

def z961 : W := mkw 0x0020091200000000 0x0004012240000000 0xe013ffffc0000003 0xdc027ffff8000000

def z962 : W := mkw 0x0db01fec1b681f57 0x81b603fd836d03ea 0xdff01fcc3ff81f86 0xfbfe03f987ff03f0

def z963 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8fcf9f3c1c7ffff 0xbf1f9f3e7838ffff

def z964 : W := mkw 0x37feddba8fa38814 0x86ffdbb751f47102 0xf7ffffffcfc30c1b 0xfefffffff9f86183

def z965 : W := mkw 0x37feddba8d220000 0x06ffdbb751a44000 0xe7ffffffce000003 0xfcfffffff9c00000

def z966 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8ec183001c7ffff 0x3f1d83060038ffff

def z967 : W := mkw 0x020a000000000000 0x0041400000000000 0xa71fe7cfc0000003 0xf4e3fcf9f8000000

def z968 : W := mkw 0x3ffeddba8fe38e07 0x07ffdbb751fc71c0 0xf7ffffffcfc30c03 0xfefffffff9f86180

def z969 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x8ff3e0003ffce005 0xd1fe7c0007ff9c00

def z970 : W := mkw 0x27feddba80c1860a 0x44ffdbb7501830c1 0xffffffffc1c31f9f 0xfffffffff83863f3

def z971 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xe7ffffffc007007b 0xfcfffffff800e00f

def z972 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fffe0003ffffc7d 0xf3fffc0007ffff8f

def z973 : W := mkw 0x27feddba80818000 0x04ffdbb750103000 0xffffffffc1c7fc7f 0xfffffffff838ff8f

def z974 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0x770f1e3c3e070c79 0x6ee1e3c787c0e18f

def z975 : W := mkw 0x0000000000000000 0x0000000000000000 0xf01fffffc0071c7f 0xfe03fffff800e38f

def z976 : W := mkw 0x04d4c00000000000 0x009a980000000000 0xa0f3e7cfc0000003 0xd41e7cf9f8000000

def z977 : W := mkw 0x0044801200000000 0x0008900240000000 0xa01fe7ffc0000003 0xd403fcfff8000000

def z978 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xbfffe1033fffe007 0xf7fffc2067fffc00

def z979 : W := mkw 0x16dfe0046db7c040 0x22dbfc008db6f808 0x9fffe00cffffe005 0xf3fffc019ffffc00

def z980 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x58ec993301c7fffc 0xab1d93266038ffff

def z981 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xbfffe0303fffe07d 0xf7fffc0607fffc0f

def z982 : W := mkw 0x27feddba80818000 0x04ffdbb750103000 0xefffffffc1c0e003 0xfdfffffff8381c00

def z983 : W := mkw 0x0d9016401b681f07 0x01b202c8036d03e0 0xdff01e003ff81f86 0xfbfe03c007ff03f0

def z984 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x17ffe0003fffe001 0x62fffc0007fffc00

def z985 : W := mkw 0x21201dba80000000 0x042403b750000000 0x60137fffc0000002 0x4c026ffff8000000

def z986 : W := mkw 0x26dec03a80000000 0x04dbd80750000000 0xa7ffe7ffc0000003 0xf4fffcfff8000000

def z987 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xefffffffc004e007 0xfdfffffff8009c00

def z988 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x67efffffc0000003 0x2cfdfffff8000000

def z989 : W := mkw 0x27ded4ba80000000 0x04fbda9750000000 0xa7ffe6ffc0000001 0xf4fffcdff8000000

def z990 : W := mkw 0x16dfe02c2db7c050 0x82dbfc0585b6f80a 0xfffff83c3ffffc7f 0xffffff0787ffff8f

def z991 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xf7ffffffc0070007 0xfefffffff800e000

def z992 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xfff01fc03ffc1fe7 0xfffe03f807ff83fc

def z993 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x4ff01fc03ff81f82 0xc9fe03f807ff03f0

def z994 : W := mkw 0x27feddba89200000 0x04ffdbb751240000 0xe7fffffffe380003 0xfcffffffffc70000

def z995 : W := mkw 0x0020090100c1a6aa 0x40040120201834d5 0xf8ec193001c7ffff 0xbf1d83260038ffff

def z996 : W := mkw 0x00200901004026a2 0x00040120200804d4 0xf8ec993301c7ffff 0xbf1d93266038ffff

def z997 : W := mkw 0x16dfe0122db7c008 0x42dbfc0245b6f801 0x9fffe0303fffe01d 0xf3fffc0607fffc03

def z998 : W := mkw 0x27feddba89200000 0x04ffdbb751240000 0xf7ffffffcfc00003 0xfefffffff9f80000

def z999 : W := mkw 0x149120002db7c000 0x0292240005b6f800 0x1fe000003fffe004 0x23fc000007fffc00

def z1000 : W := mkw 0x37feddba8de3860a 0x46ffdbb751bc70c1 0xf7ffffffcfc30c1b 0xfefffffff9f86183

def z1001 : W := mkw 0x2db01fe89b681f07 0x05b603fd136d03e0 0xdff01fccfff81f86 0xfbfe03f99fff03f0

def z1002 : W := mkw 0x030a142806020814 0x8061428500c04102 0x770c18300e031c7a 0x2ee1830601c0638f

def z1003 : W := mkw 0x020b020434061040 0x004160408680c208 0xf70f1e3c3e071c7f 0x7ee1e3c787c0e38f

def z1004 : W := mkw 0x030b142c26060854 0x8061628584c0c10a 0x570c18300e070c78 0x2ae1830601c0e18f

def z1005 : W := mkw 0x0000000000000000 0x0000000000000000 0x0013e7cfc0000000 0xc0027cf9f8000000

def z1006 : W := mkw 0x124fe0132497e0a8 0x4249fc026492fc15 0x000fe0030007e001 0x0001fc006000fc00

def z1007 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xa7f3e7cfc0000003 0xd4fe7cf9f8000000

def z1008 : W := mkw 0x2ffeddba8be18e0f 0x45ffdbb7517c31c1 0x57ec18300fc30c18 0x2afd830601f86183

def z1009 : W := mkw 0x2db01fd29b681f07 0x05b603fa536d03e0 0xdff01fc3fff81f86 0xfbfe03f87fff03f0

def z1010 : W := mkw 0x0490024019281100 0x0092004803250220 0x9ff000003ff81384 0xf3fe000007ff0270

def z1011 : W := mkw 0x2db01ffa9b681f07 0x05b603ff536d03e0 0xdff01ff03ff81f86 0xfbfe03fe07ff03f0

def z1012 : W := mkw 0x1490200009b1c000 0x0292040001363800 0x9ff000003ff8e004 0xf3fe000007ff1c00

def z1013 : W := mkw 0x00012245709df1e8 0x60002448ae13be3d 0x08000000303ff3fc 0x010000000607fe7f

def z1014 : W := mkw 0x020b002c24060050 0x804160058480c00a 0xf70f183c3e071c7f 0x7ee1e30787c0e38f

def z1015 : W := mkw 0x27feddba80c1860a 0x44ffdbb7501830c1 0xffffffffc1c7ec1f 0xfffffffff838fd83

def z1016 : W := mkw 0x27feddba80818000 0x04ffdbb750103000 0xe7ffffffc007e003 0xfcfffffff800fc00

def z1017 : W := mkw 0x0490000009200000 0x0092000001240000 0x9ff080003ffce005 0xf3fe100007ff9c00

def z1018 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8fc993331ffffff 0xff1f9326663fffff

def z1019 : W := mkw 0x0490000009200000 0x0092000001240000 0x9ff001003ff81386 0xf3fe002007ff0270

def z1020 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x1fff60003fffe004 0x63ffec0007fffc00

def z1021 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x88000100303cf3e6 0x9100002006079e7c

def z1022 : W := mkw 0x324fe03ba497e0a8 0x4649fc077492fc15 0x200fe03fc007e079 0x0401fc07f800fc0f

def z1023 : W := mkw 0x0490000000000000 0x0092000000000000 0xa7f3e7cfc0000003 0xf4fe7cf9f8000000

def z1024 : W := mkw 0x030b166c360e1954 0x806162cd86c1c32a 0xf71f1efc3e3f1c7f 0x7ee3e3df87c7e38f

def z1025 : W := mkw 0x0100142800000000 0x0020028500000000 0xe013ffffc0000003 0xdc027ffff8000000

def z1026 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9fec80003fffe005 0xb3fd900007fffc00

def z1027 : W := mkw 0x210014a880000000 0x0420029510000000 0xa013e7cfc0000003 0xd4027cf9f8000000

def z1028 : W := mkw 0x124fe02d6497e0f0 0xa249fc05ac92fc1e 0x200fe03fc007e079 0x0401fc07f800fc0f

def z1029 : W := mkw 0x149120002db7c000 0x0292240005b6f800 0x9ff3e0003fffe005 0xf3fe7c0007fffc00

def z1030 : W := mkw 0x169b20002db7c000 0x02d3640005b6f800 0x9fff00003fffe005 0xf3ffe00007fffc00

def z1031 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x27ffe7ffc0000001 0xc4fffcfff8000000

def z1032 : W := mkw 0x030a162c16021854 0x806142c582c0430a 0xf70c1e3c0e071c7f 0x3ee183c781c0e38f

def z1033 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x8ff007c03ff81386 0xd1fe00f807ff0270

def z1034 : W := mkw 0x0d9016c01b681f07 0x01b202d8036d03e0 0x9ff006c03ff81f84 0xf3fe00d807ff03f0

def z1035 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x1ff007c03ff81f84 0xc3fe00f807ff03f0

def z1036 : W := mkw 0x0d9016c01b281905 0x01b202d803650320 0x9ff007c03ff81386 0xf3fe00f807ff0270

def z1037 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff018003ff81f84 0xfbfe030007ff03f0

def z1038 : W := mkw 0x09201fc112483faf 0x412403f8224907f5 0x40001fc000001ffa 0x080003f8000003ff

def z1039 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0x0713e7cfc0000000 0xc0e27cf9f8000000

def z1040 : W := mkw 0x16dfe0042db7c050 0x82dbfc0085b6f80a 0x9fffe0003fffe07d 0xf3fffc0007fffc0f

def z1041 : W := mkw 0x06fec91200000000 0x00dfd92240000000 0xe7ffffffc0000003 0xfcfffffff8000000

def z1042 : W := mkw 0x21649dba80000000 0x042c93b750000000 0xe0ffffffc0000003 0xfc1ffffff8000000

def z1043 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdffc1ff03ffb1f9e 0xfbff83fe07ff63f3

def z1044 : W := mkw 0x0db01fc41b681f47 0x01b603f8836d03e8 0xfff01fcc3ff81fe6 0xfffe03f987ff03fc

def z1045 : W := mkw 0x2ffeddba89600603 0x05ffdbb7512c00c0 0xe7ffffffc1c00003 0xfcfffffff8380000

def z1046 : W := mkw 0x16dfe2457dbff1e0 0x22dbfc48afb7fe3c 0x1fec00003ffff3e4 0x23fd800007fffe7c

def z1047 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xb81fe7cff03ff3e7 0xf703fcf9fe07fe7c

def z1048 : W := mkw 0x2044c01280000000 0x0408980250000000 0xa013e7cfc0000003 0xd4027cf9f8000000

def z1049 : W := mkw 0x27feddba80818008 0x44ffdbb750103001 0xe7ffffffc003001b 0xfcfffffff8006003

def z1050 : W := mkw 0x00012245721c79f4 0xa0002448ae438f3e 0x08000000303cfffc 0x0100000006079fff

def z1051 : W := mkw 0x030a162812001804 0x006142c502400300 0xf70f1e3c3e071c7f 0x7ee1e3c787c0e38f

def z1052 : W := mkw 0x030a142806020814 0x8061428500c04102 0x770c18300e070c79 0x2ee1830601c0e18f

def z1053 : W := mkw 0x0020090000000000 0x0004012000000000 0xe0f3ffcfc0000003 0xfc1e7ff9f8000000

def z1054 : W := mkw 0x0db01d800b600e07 0x01b603b0016c01c0 0xdff019003ff81f86 0xfbfe032007ff03f0

def z1055 : W := mkw 0x0490000009200000 0x0092000001240000 0xbff3e7cffff80007 0xf7fe7cf9ffff0000

def z1056 : W := mkw 0x09201fff12483fff 0xc12403ffe24907ff 0x60001fff00001ffa 0x0c0003ffe00003ff

def z1057 : W := mkw 0x069a400000000000 0x00d3480000000000 0xa713e7cfc0000003 0xd4e27cf9f8000000

def z1058 : W := mkw 0x030a142c06020854 0x8061428580c0410a 0x770c183c0e030c78 0x2ee1830781c0618f

def z1059 : W := mkw 0x04912245793c71e0 0x20922448af278e3c 0x9ff000003ffcf3e4 0xf3fe000007ff9e7c

def z1060 : W := mkw 0x0001224570ddf7ea 0x60002448ae1bbefd 0x0800000031fcf3e4 0x01000000063f9e7c

def z1061 : W := mkw 0x09201fc152483fa7 0x212403f82a4907f4 0x40001fc3c0001f82 0x080003f8780003f0

def z1062 : W := mkw 0x0db13fc57b7c7fe7 0x21b627f8af6f8ffc 0x5fe018003ffcffe4 0x2bfc030007ff9ffc

def z1063 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x9ff3e0003ff8e004 0xf3fe7c0007ff1c00

def z1064 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x47ffffffc0000000 0xe8fffffff8000000

def z1065 : W := mkw 0x04b00b4019681702 0x00960168032d02e0 0xdff01fc03ff81f86 0xfbfe03f807ff03f0

def z1066 : W := mkw 0x030b166c360e1954 0x806162cd86c1c32a 0xff1ffffffe3f1fff 0xffe3ffffffc7e3ff

def z1067 : W := mkw 0x030b166c360e1954 0x806162cd86c1c32a 0xff0f1e3c3e3f1fff 0x7fe1e3c787c7e3ff

def z1068 : W := mkw 0x030a142800000000 0x0061428500000000 0xa713e7cfc0000003 0xd4e27cf9f8000000

def z1069 : W := mkw 0x00012045601c61e0 0x20002408ac038c3c 0xa813e7cfc03ce3e3 0xd5027cf9f8079c7c

def z1070 : W := mkw 0x0044800000000000 0x0008900000000000 0xa0ffe7cfc0000003 0xf41ffcf9f8000000

def z1071 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xf7fffffffe000007 0xfeffffffffc00000

def z1072 : W := mkw 0x16dfe0042db7c040 0x02dbfc0085b6f808 0xbfffe00c3fffe065 0xf7fffc0187fffc0c

def z1073 : W := mkw 0x2020099280000000 0x0404013250000000 0xa013e7cfc0000003 0xd4027cf9f8000000

def z1074 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0x57f01fc03ff81f82 0x6afe03f807ff03f0

def z1075 : W := mkw 0x2ffeddba8b600e07 0x05ffdbb7516c01c0 0xffffffffcfc01f87 0xfffffffff9f803f0

def z1076 : W := mkw 0x030b142c26060854 0x8061628584c0c10a 0xf70f1e3c0e070c7b 0x7ee1e3c781c0e18f

def z1077 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0x78ec193301c7fffe 0x2f1d83266038ffff

def z1078 : W := mkw 0x020a000004020000 0x0041400000804000 0xf70c18300e071c7f 0x3ee1830601c0e38f

def z1079 : W := mkw 0x0000000000000000 0x0000000000000000 0xa813e7cfc004e007 0xd5027cf9f8009c00

def z1080 : W := mkw 0x27feddba86020814 0x84ffdbb750c04102 0xe7ffffffce000003 0xfcfffffff9c00000

def z1081 : W := mkw 0x2ffeddba8b600e07 0x05ffdbb7516c01c0 0xfffffffffff80c07 0xffffffffffff0180

def z1082 : W := mkw 0x030b362c76165854 0xa06166c58ec2cb0a 0xf70f7e3cfe071c7f 0x7ee1efc79fc0e38f

def z1083 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x8fffe0003ff8e001 0xf1fffc0007ff1c00

def z1084 : W := mkw 0x030a162816021814 0x806142c502c04302 0xf70c1e303e071c7f 0x7ee183c607c0e38f

def z1085 : W := mkw 0x0020090000400602 0x00040120000800c0 0xf8f3ffcfc1c01f87 0xff1e7ff9f83803f0

def z1086 : W := mkw 0x0001224576dffffe 0xe0002448aedbffff 0x180000003ffffffc 0x0300000007ffffff

def z1087 : W := mkw 0x25f4ddba80000000 0x04be9bb750000000 0xe0f3ffffc0000003 0xdc1e7ffff8000000

def z1088 : W := mkw 0x030a162c16021854 0x806142c582c0430a 0xf70c1e3c3e031c7e 0x7ee183c787c0638f

def z1089 : W := mkw 0x27feddba84020010 0x84ffdbb750804002 0xe7ffffffc003001b 0xfcfffffff8006003

def z1090 : W := mkw 0x00012245761e79f4 0xa0002448aec3cf3e 0xf81ffffffe3fffff 0xff03ffffffc7ffff

def z1091 : W := mkw 0x0100140000000000 0x0020028000000000 0xe713ffcfc0000003 0xfce27ff9f8000000

def z1092 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0xe71fffffc0000003 0xfce3fffff8000000

def z1093 : W := mkw 0x180122457fffffe7 0x23002448affffffc 0x180000003fffffe4 0x0300000007fffffc

def z1094 : W := mkw 0x27feddba80400602 0x04ffdbb7500800c0 0xe7ffffffc0001f83 0xfcfffffff80003f0

def z1095 : W := mkw 0x230b562cb6061854 0x84616ac596c0c30a 0xf70f7e3cfe071c7f 0x7ee1efc79fc0e38f

def z1096 : W := mkw 0x2cf4c9d389e9a7ab 0x459e993a713d34f5 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z1097 : W := mkw 0x34f4e99389f1e6aa 0x469e9d32713e3cd5 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z1098 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xd8ec193001c7fffe 0xbb1d83260038ffff

def z1099 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff01fc03fff1ffe 0xfbfe03f807ffe3ff

def z1100 : W := mkw 0x08012245797c77e3 0x21002448af2f8efc 0x0800000031fcf3e4 0x01000000063f9e7c

def z1101 : W := mkw 0x124fe0012497e0a0 0x0249fc002492fc14 0x200fe0030007e061 0x0401fc006000fc0c

def z1102 : W := mkw 0x00012245705c77ea 0x60002448ae0b8efd 0x08000000303cfffc 0x0100000006079fff

def z1103 : W := mkw 0x030b142c26060854 0x8061628584c0c10a 0xf70f183c0e071c7f 0x3ee1e30781c0e38f

def z1104 : W := mkw 0x279a54a880000000 0x04f34a9510000000 0x271367cfc0000002 0x44e26cf9f8000000

def z1105 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xe7ffffffc0041067 0xfcfffffff800820c

def z1106 : W := mkw 0x29201ffb92483faf 0x452403ff724907f5 0x60001fffc0001ffa 0x0c0003fff80003ff

def z1107 : W := mkw 0x0491200029344000 0x0092240005268800 0x9ff000003ffce004 0xf3fe000007ff9c00

def z1108 : W := mkw 0x27feddba80400602 0x04ffdbb7500800c0 0xf7ffffffc1c00c03 0xfefffffff8380180

def z1109 : W := mkw 0x0064891300c1a6aa 0x400c9122601834d5 0xf8ec9fffc1c7ffff 0xbf1d93fff838ffff

def z1110 : W := mkw 0x16dec0000da38000 0x02dbd80001b47000 0x9ffc80003fffe005 0xf3ff900007fffc00

def z1111 : W := mkw 0x27feddba86c38e1e 0xc4ffdbb750d871c3 0xf7ffffffcfc30c1b 0xfefffffff9f86183

def z1112 : W := mkw 0x0db01fe81b681f07 0x01b603fd036d03e0 0xfff01ffc3ff81f86 0xfffe03ff87ff03f0

def z1113 : W := mkw 0x37feddba89a18000 0x06ffdbb751343000 0xe7ffffffc1c00003 0xfcfffffff8380000

def z1114 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x1ff3e0003fffe004 0xc3fe7c0007fffc00

def z1115 : W := mkw 0x37feddba8da38000 0x06ffdbb751b47000 0xfffffffffffb0007 0xffffffffffff6000

def z1116 : W := mkw 0x0000000000000000 0x0000000000000000 0xa013e7cfc0041067 0xd4027cf9f800820c

def z1117 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0x67ff7fffc0000002 0x6cffeffff8000000

def z1118 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xd70c1e303e071c7e 0x7ae183c607c0e38f

def z1119 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xe7ffffffc0001c7b 0xfcfffffff800038f

def z1120 : W := mkw 0x00012245793c71e0 0x20002448af278e3c 0x180000003ffcf3e4 0x0300000007ff9e7c

def z1121 : W := mkw 0x0064891200000000 0x000c912240000000 0xa0f3e7cfc0000003 0xd41e7cf9f8000000

def z1122 : W := mkw 0x0064890000c18602 0x000c9120001830c0 0xf8ec993001c7ffff 0xbf1d93260038ffff

def z1123 : W := mkw 0x01201f4012481f06 0x002403e8024903e0 0xdff01fc03ff81f86 0xfbfe03f807ff03f0

def z1124 : W := mkw 0x0db01fc45b681f47 0x21b603f88b6d03e8 0xdff01fccfff81f86 0xfbfe03f99fff03f0

def z1125 : W := mkw 0x030b366c361e5954 0x806166cd86c3cb2a 0xff1ffffc3e3fffff 0xffe3ffff87c7ffff

def z1126 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xf71ffe3c3e071c7f 0xfee3ffc787c0e38f

def z1127 : W := mkw 0x14d4e00009b1c000 0x029a9c0001363800 0x0ff0e0003ff8e000 0xc1fe1c0007ff1c00

def z1128 : W := mkw 0x27ded4ba80000000 0x04fbda9750000000 0x0713e6cfc0000000 0x40e27cd9f8000000

def z1129 : W := mkw 0x0c9002401b681f07 0x01920048036d03e0 0x9ff007c03ff81f86 0xf3fe00f807ff03f0

def z1130 : W := mkw 0x0044800100c1a6aa 0x40089000201834d5 0xf8ec983001c7ffff 0xbf1d93060038ffff

def z1131 : W := mkw 0x030b166c360e1954 0x806162cd86c1c32a 0xf70f1ffc3e071fff 0x7ee1e3ff87c0e3ff

def z1132 : W := mkw 0x06dfe00029344000 0x00dbfc0005268800 0x9fffe0003ffce005 0xf3fffc0007ff9c00

def z1133 : W := mkw 0x27feddba80c1860a 0x44ffdbb7501830c1 0xf7ffffffc1c71c7f 0xfefffffff838e38f

def z1134 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xf7ffffffc0001c07 0xfefffffff8000380

def z1135 : W := mkw 0x2ffeddba8b200805 0x05ffdbb751640100 0xe7ffffffce000003 0xfcfffffff9c00000

def z1136 : W := mkw 0x030b160036061804 0x006162c006c0c300 0xf70f1e303e071c7f 0x7ee1e3c607c0e38f

def z1137 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0x0fffe0003fffe001 0xc1fffc0007fffc00

def z1138 : W := mkw 0x1cf4e9d309f9e7ab 0x439e9d3a613f3cf5 0x08f0e1c301f8e380 0x811e1c38603f1c70

def z1139 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x2813e7cfc03cf3e3 0x85027cf9f8079e7c

def z1140 : W := mkw 0x04d4800009a18000 0x009a900001343000 0x9ff080003ff8e004 0xf3fe100007ff1c00

def z1141 : W := mkw 0x236eddba80000000 0x046ddbb750000000 0xe01fffffc0000003 0xdc03fffff8000000

def z1142 : W := mkw 0x25f4dd9280000000 0x04be9bb250000000 0xe7f3ffcfc0000003 0xfcfe7ff9f8000000

def z1143 : W := mkw 0x059016401b281904 0x00b202c803650320 0xdff01fc03ff81f86 0xfbfe03f807ff03f0

def z1144 : W := mkw 0x27feddba80000000 0x04ffdbb750000000 0xc7f3ffcfc0000002 0xf8fe7ff9f8000000

def z1145 : W := mkw 0x236eddba80000000 0x046ddbb750000000 0xe70fffffc0000003 0x7ce1fffff8000000

def z1146 : W := mkw 0x00012041601c61a0 0x200024082c038c34 0xa813e7cff03ce387 0xd5027cf9fe079c70

def z1147 : W := mkw 0x37feddba8da38000 0x06ffdbb751b47000 0xffffffffcfc7e007 0xfffffffff9f8fc00

def z1148 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x00000000303ce060 0x0000000006079c0c

def z1149 : W := mkw 0x04b0098000000000 0x0096013000000000 0xa0f3e7cfc0000003 0xd41e7cf9f8000000

def z1150 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdffc1fc03fff1f87 0xfbff83f807ffe3f0

def z1151 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff0ffc3fff81f86 0xfbfe1ff87fff03f0

def z1152 : W := mkw 0x36dfe080adb7c000 0x06dbfc1015b6f800 0x9fffe0c0ffffe005 0xf3fffc181ffffc00

def z1153 : W := mkw 0x27ded4a880000000 0x04fbda9510000000 0xa7ffe7cfc0000003 0xf4fffcf9f8000000

def z1154 : W := mkw 0x036e9d3a00000000 0x006dd3a740000000 0xe7ffffffc0000003 0xfcfffffff8000000

def z1155 : W := mkw 0x0db01fd21b681f07 0x01b603fa436d03e0 0xfff01ff33ff81f86 0xfffe03fe67ff03f0

def z1156 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xf80c1830303fffff 0x3f0183060607ffff

def z1157 : W := mkw 0x220a402880000000 0x0441480510000000 0xa013e7cfc0000003 0xd4027cf9f8000000

def z1158 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xdffff8003ffffc07 0xfbffff0007ffff80

def z1159 : W := mkw 0x124fe0012497e0a8 0x4249fc002492fc15 0x000fe0000007e079 0x0001fc000000fc0f

def z1160 : W := mkw 0x00012245721c79e4 0x20002448ae438f3c 0xb813e7cffe3cffe7 0xd7027cf9ffc79ffc

def z1161 : W := mkw 0x27feddba84020000 0x04ffdbb750804000 0xf7ffffffce030003 0xfefffffff9c06000

def z1162 : W := mkw 0x06df80002da78000 0x00dbf00005b4f000 0x9fff80003fffe005 0xf3fff00007fffc00

def z1163 : W := mkw 0x030b162c36061854 0x806162c586c0c30a 0xffef1e3c3fc71c7f 0xfffde3c787f8e38f

def z1164 : W := mkw 0x00012001201460a0 0x0000240024028c14 0xa813e7cff03cf3e7 0xd5027cf9fe079e7c

def z1165 : W := mkw 0x00012245741e71e0 0x20002448ae83ce3c 0x180000003e3ff3e4 0x0300000007c7fe7c

def z1166 : W := mkw 0x14f4e95349f9e7aa 0x629e9d2a693f3cf5 0x08f0e1c3c1f8e380 0x811e1c38783f1c70

def z1167 : W := mkw 0x16dfe0002db7c000 0x02dbfc0005b6f800 0xfffff8303fffe007 0xffffff0607fffc00

def z1168 : W := mkw 0x2ffeddba8be18e0f 0x45ffdbb7517c31c1 0xf7ffffffcfc30c1b 0xfefffffff9f86183

def z1169 : W := mkw 0x04f4891309e1a6aa 0x409e9122613c34d5 0x08f0810301f8e380 0x811e1020603f1c70

def z1170 : W := mkw 0x2000003a80000000 0x0400000750000000 0xa013e7ffc0000003 0xd4027cfff8000000

def z1171 : W := mkw 0x21201dba80000000 0x042403b750000000 0x6003ffffc0000003 0x0c007ffff8000000

def z1172 : W := mkw 0x16dfe0122db7c000 0x02dbfc0245b6f800 0xbfffe0333fffe005 0xf7fffc0667fffc00

def z1173 : W := mkw 0x0db01fc41b681f57 0x81b603f8836d03ea 0xdff01fc03ff81ffe 0xfbfe03f807ff03ff

def z1174 : W := mkw 0x124fe03f2497e0f8 0xc249fc07e492fc1f 0x200fe03f0007e079 0x0401fc07e000fc0f

def z1175 : W := mkw 0x0cb009c009680703 0x01960138012d00e0 0xdff019c03ff81f86 0xfbfe033807ff03f0

def z1176 : W := mkw 0x0000000000000000 0x0000000000000000 0xa813e7cff0380007 0xd5027cf9fe070000

def z1177 : W := mkw 0x16dee0000db3c000 0x02dbdc0001b67800 0x9ffce0003ffbe004 0xf3ff9c0007ff7c00

def z1178 : W := mkw 0x226ec93a80000000 0x044dd92750000000 0xe0ffffffc0000003 0xfc1ffffff8000000

def z1179 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x8813e7cff038f386 0xd1027cf9fe071e70

def z1180 : W := mkw 0x00002041401861a0 0x2000040828030c34 0xa813e7cfc03cf3e7 0xd5027cf9f8079e7c

def z1181 : W := mkw 0x0b0b16ec360e1955 0x816162dd86c1c32a 0xf70f1efc3e071c7f 0x7ee1e3df87c0e38f

def z1182 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x88008000303cf3e5 0x9100100006079e7c

def z1183 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0x88100000303cf3e4 0xd102000006079e7c

def z1184 : W := mkw 0x0db01fc01b681f07 0x01b603f8036d03e0 0xdff09fc03ffcff87 0xfbfe13f807ff9ff0

def z1185 : W := mkw 0x124fe0016497e0a0 0x2249fc002c92fc14 0x000fe003c007e001 0x0001fc007800fc00

def z1186 : W := mkw 0x27ded4ba80000000 0x04fbda9750000000 0xe71ffeffc0000003 0x7ce3ffdff8000000

def z1187 : W := mkw 0x0f9b36ec7f3e5955 0xa1f366dd8fe7cb2a 0x071366ccfe380000 0x40e26cd99fc70000

def z1188 : W := mkw 0x00212b45705c77e2 0x20042568ae0b8efc 0xd8e0190031fcffe6 0xbb1c0320063f9ffc

def z1189 : W := mkw 0x0cb00bc01b681f07 0x01960178036d03e0 0x9ff001c03ff81f84 0xf3fe003807ff03f0

def z1190 : W := mkw 0x01201f7f52483ffe 0xe02403efea4907ff 0x60001fffc0001ffa 0x0c0003fff80003ff

def z1191 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xb813e7cff03fffff 0xd7027cf9fe07ffff

def z1192 : W := mkw 0x36dfe03eadb7c050 0x86dbfc07d5b6f80a 0xbfffe03fffffe07d 0xf7fffc07fffffc0f

def z1193 : W := mkw 0x10012245749ff1e0 0x22002448ae93fe3c 0x08000000303ff3e4 0x010000000607fe7c

def z1194 : W := mkw 0x030b142c26060854 0x8061628584c0c10a 0xf70f183c3e070c7d 0x7ee1e30787c0e18f

def z1195 : W := mkw 0x16dfe0282db7c010 0x82dbfc0505b6f802 0x9fffe0303fffe01d 0xf3fffc0607fffc03

def z1196 : W := mkw 0x00002041401861a0 0x2000040828030c34 0x0813e7cfc038e380 0xc1027cf9f8071c70

def z1197 : W := mkw 0x00012245701c71e0 0x20002448ae038e3c 0xa81fe7fff03ff3ff 0xd503fcfffe07fe7f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z5,z6,z9]),(0,[z0,z1,z10,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z11,z5,z6])],[(0,[z12,z0,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z14,z5,z6]),(0,[z15,z0,z1,z2,z3,z16,z6]),(0,[z7,z0,z1,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z6,z18])],[(0,[z0,z19,z2,z3,z5,z6,z20]),(0,[z0,z1,z2,z3,z21,z5,z6]),(0,[z22,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z6,z24]),(0,[z0,z1,z2,z25,z3,z5,z6]),(0,[z0,z1,z2,z26,z3,z5,z6])],[(0,[z27,z0,z1,z28,z3,z5,z6]),(0,[z0,z1,z29,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z30])],[(0,[z0,z1,z2,z3,z31,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z32]),(0,[z0,z1,z2,z3,z5,z6,z33]),(0,[z0,z1,z2,z34,z3,z5,z6])],[(0,[z7,z0,z35,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z3,z5,z36]),(0,[z0,z1,z2,z3,z37,z5,z6])],[(0,[z0,z1,z2,z38,z3,z5,z6]),(0,[z0,z1,z2,z39,z3,z5,z6]),(1,[z0,z1,z2,z3,z40,z6]),(0,[z0,z41,z1,z2,z3,z5,z6])],[(0,[z42,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z43,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z44,z3,z5,z6])]],
   [[(0,[z45,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z11,z5]),(0,[z0,z1,z2,z46,z3,z5,z6]),(0,[z0,z1,z2,z47,z3,z5,z48])],[(0,[z7,z27,z0,z1,z2,z3,z5]),(0,[z7,z0,z0,z1,z2,z3,z5]),(0,[z22,z0,z1,z49,z2,z3,z5]),(0,[z0,z50,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z52,z5,z6])],[(0,[z0,z1,z53,z3,z5,z6,z54]),(0,[z55,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z56,z5,z6])],[(0,[z0,z1,z57,z2,z3,z5,z6]),(0,[z0,z1,z2,z58,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z59,z6]),(1,[z0,z1,z2,z3,z60,z6]),(0,[z0,z1,z2,z61,z3,z5,z6]),(0,[z0,z1,z62,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z63,z5,z6]),(0,[z0,z1,z64,z2,z3,z5,z65]),(0,[z0,z1,z2,z3,z66,z5,z6]),(0,[z0,z1,z2,z3,z67,z5,z68]),(0,[z0,z1,z2,z69,z5,z68,z6])],[(0,[z0,z70,z1,z2,z3,z5,z6]),(0,[z27,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z71,z3,z5]),(0,[z0,z1,z2,z3,z5,z72,z6]),(1,[z0,z1,z2,z51,z52,z6])],[(0,[z0,z1,z2,z3,z73,z5,z6]),(0,[z12,z0,z74,z2,z3,z5,z6]),(0,[z0,z1,z75,z2,z3,z5,z6])],[(0,[z7,z76,z0,z1,z2,z3,z5]),(0,[z0,z1,z77,z2,z3,z5,z6]),(1,[z0,z1,z2,z78,z5,z6]),(1,[z0,z79,z2,z80,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z81]),(0,[z0,z1,z82,z2,z3,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z54])],[(0,[z0,z1,z2,z3,z5,z84,z6]),(0,[z22,z0,z1,z2,z3,z67,z5])]],
   [[(0,[z85,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z86,z6]),(0,[z0,z1,z2,z3,z5,z6,z87])],[(0,[z0,z1,z2,z3,z88,z5,z6]),(0,[z27,z76,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z89]),(0,[z90,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z91,z3,z5,z6])],[(0,[z0,z1,z92,z2,z3,z5,z6]),(0,[z0,z1,z2,z93,z3,z5,z6]),(0,[z0,z94,z1,z2,z3,z5,z6]),(0,[z0,z1,z95,z2,z3,z5,z6])],[(0,[z0,z1,z96,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z97]),(0,[z98,z0,z2,z99,z3,z5,z6]),(0,[z0,z79,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z100,z3,z5,z6]),(0,[z0,z1,z101,z2,z3,z5,z6])],[],[(0,[z0,z1,z2,z3,z5,z102,z6]),(0,[z22,z0,z1,z103,z2,z3,z5]),(0,[z0,z1,z2,z3,z104,z5,z6]),(0,[z0,z1,z2,z3,z5,z105,z6]),(0,[z0,z50,z1,z2,z3,z72,z6]),(0,[z0,z1,z2,z3,z106,z5,z6]),(0,[z83,z0,z1,z3,z5,z65,z6]),(0,[z0,z1,z2,z3,z107,z5,z6]),(0,[z0,z1,z2,z108,z3,z5,z6]),(0,[z0,z1,z2,z109,z5,z6,z17])],[(0,[z110,z0,z1,z2,z3,z5,z6]),(0,[z0,z111,z1,z2,z3,z5,z6]),(0,[z112,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z3,z113,z6])],[(0,[z22,z0,z1,z2,z3,z5,z72]),(0,[z0,z1,z2,z114,z3,z5,z6])]],
   [[(0,[z7,z0,z1,z2,z3,z5,z20]),(0,[z22,z0,z115,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z116,z6]),(0,[z117,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z118]),(0,[z0,z50,z1,z2,z3,z5,z119]),(0,[z0,z1,z2,z52,z5,z120,z6]),(1,[z0,z1,z2,z121,z5,z122])],[(0,[z22,z0,z1,z2,z3,z123,z5]),(0,[z0,z1,z2,z3,z124,z5,z6]),(0,[z0,z1,z2,z125,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z126]),(0,[z127,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z128,z6]),(0,[z129,z0,z1,z2,z3,z5,z6]),(0,[z130,z0,z1,z2,z3,z5,z6])],[(0,[z76,z0,z13,z2,z3,z5,z6]),(0,[z83,z22,z0,z1,z2,z3,z5]),(0,[z0,z131,z103,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z132,z6]),(0,[z0,z133,z1,z2,z3,z5,z6])],[(0,[z134,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z16,z6]),(0,[z0,z1,z2,z3,z135,z5,z6]),(0,[z0,z1,z2,z3,z5,z136,z6]),(0,[z137,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z138,z6]),(0,[z0,z1,z2,z139,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z140,z6])],[(0,[z0,z1,z53,z2,z3,z5,z141]),(0,[z0,z1,z2,z142,z3,z5,z59]),(0,[z0,z143,z1,z2,z3,z5,z6]),(0,[z144,z0,z1,z2,z3,z5,z6])],[(0,[z85,z1,z2,z28,z3,z5,z6]),(0,[z145,z0,z1,z146,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z147,z6]),(0,[z0,z115,z1,z2,z3,z11,z6]),(0,[z0,z148,z1,z2,z3,z5,z6])]],
   [[(0,[z149,z0,z1,z2,z3,z5,z6]),(0,[z0,z150,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z7,z0,z1,z71,z3,z5,z6]),(1,[z0,z1,z2,z151,z5,z6]),(0,[z0,z1,z2,z78,z3,z5,z6]),(0,[z0,z1,z2,z3,z152,z5,z6])],[(0,[z153,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z154,z5,z6])],[(0,[z22,z0,z1,z2,z28,z3,z5]),(0,[z155,z7,z0,z1,z2,z3,z5]),(0,[z7,z0,z1,z82,z2,z3,z5]),(1,[z7,z1,z2,z3,z5,z156]),(0,[z0,z1,z2,z3,z5,z6,z157]),(0,[z0,z1,z82,z2,z26,z5,z6])],[(0,[z22,z0,z1,z2,z47,z3,z5]),(0,[z158,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z109,z5,z17])],[(0,[z98,z0,z1,z53,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z159]),(0,[z160,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z161,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z162]),(0,[z0,z1,z3,z163,z5,z72,z6]),(0,[z0,z1,z2,z164,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z120,z6]),(0,[z0,z1,z2,z3,z68,z6,z165]),(0,[z0,z1,z2,z3,z5,z6,z166])],[(0,[z7,z167,z0,z1,z2,z3,z5]),(0,[z55,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z168,z6]),(0,[z0,z169,z1,z2,z3,z5,z6]),(0,[z22,z0,z74,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z170]),(0,[z0,z1,z2,z3,z5,z6,z171]),(0,[z0,z1,z2,z172,z3,z5,z6]),(0,[z0,z1,z173,z2,z3,z5,z6])],[(0,[z0,z19,z1,z2,z3,z5,z174]),(1,[z27,z1,z53,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z122]),(0,[z0,z1,z2,z3,z5,z175,z6]),(0,[z0,z1,z2,z3,z5,z176,z6]),(0,[z0,z1,z2,z177,z3,z5,z6]),(0,[z0,z1,z178,z2,z3,z5,z6])]],
   [[(0,[z0,z179,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z180,z5]),(0,[z0,z1,z181,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z182,z5,z6])],[(0,[z183,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z184,z3,z5,z6]),(0,[z0,z1,z2,z47,z5,z120,z6])],[(1,[z0,z179,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z185,z6]),(1,[z0,z1,z2,z3,z5,z186]),(1,[z0,z1,z2,z187,z3,z5]),(0,[z0,z1,z2,z3,z188,z5,z6]),(0,[z0,z1,z2,z3,z5,z189,z6]),(1,[z0,z1,z2,z190,z5,z6]),(0,[z0,z191,z1,z2,z3,z5,z6])],[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z51,z3,z5]),(0,[z192,z0,z1,z2,z3,z5,z6]),(1,[z0,z74,z2,z3,z5,z20]),(1,[z0,z1,z64,z3,z5,z54]),(0,[z0,z193,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z194,z5,z6]),(0,[z195,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z196,z5,z6]),(0,[z0,z1,z2,z197,z3,z5,z6]),(0,[z0,z1,z2,z47,z3,z5,z198])],[(0,[z7,z0,z1,z199,z3,z5,z6]),(0,[z200,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z201,z3,z5,z6]),(1,[z0,z1,z77,z3,z5,z6]),(0,[z7,z83,z0,z1,z2,z3,z5]),(1,[z0,z1,z178,z3,z113,z6]),(0,[z0,z1,z2,z3,z5,z202,z6])],[(0,[z1,z13,z2,z28,z3,z5,z6]),(0,[z0,z1,z2,z203,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z141]),(0,[z45,z22,z0,z1,z2,z3,z5]),(0,[z0,z204,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z109,z3,z5,z17]),(0,[z0,z1,z2,z3,z5,z6,z165])]],
   [[(0,[z0,z19,z1,z2,z3,z5,z6]),(0,[z205,z22,z0,z1,z2,z3,z5]),(0,[z7,z0,z1,z178,z2,z3,z5]),(0,[z22,z0,z1,z2,z3,z113,z5]),(0,[z206,z0,z1,z2,z3,z5,z6]),(1,[z207,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z5,z165])],[(0,[z208,z0,z1,z2,z47,z5,z6]),(0,[z22,z0,z1,z2,z3,z209,z5]),(0,[z210,z7,z0,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z3,z5,z211]),(0,[z0,z131,z1,z82,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z119]),(0,[z0,z1,z2,z3,z212,z5,z6]),(0,[z0,z1,z2,z3,z213,z5,z6]),(0,[z0,z1,z2,z214,z3,z5,z6])],[(0,[z0,z1,z2,z3,z215,z5,z6]),(0,[z22,z0,z1,z2,z216,z3,z5]),(0,[z0,z131,z1,z99,z3,z5,z6]),(0,[z0,z1,z2,z217,z3,z5,z6]),(0,[z0,z1,z2,z3,z113,z11,z6]),(0,[z0,z1,z82,z49,z3,z5,z6])],[(0,[z27,z22,z0,z1,z2,z3,z5]),(0,[z0,z218,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z209,z5,z16,z6]),(0,[z0,z1,z2,z219,z3,z5,z6])],[(0,[z0,z220,z1,z2,z3,z5,z6]),(0,[z221,z0,z1,z2,z3,z5,z6]),(0,[z1,z53,z2,z28,z3,z5,z6]),(0,[z0,z1,z49,z53,z3,z5,z6]),(1,[z0,z1,z146,z3,z5,z6]),(1,[z222,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z223,z5,z72,z6]),(1,[z0,z1,z2,z224,z5,z6]),(0,[z0,z1,z2,z214,z3,z5,z68])],[(0,[z0,z1,z2,z225,z3,z5,z6]),(0,[z27,z1,z53,z2,z3,z5,z6]),(0,[z0,z1,z226,z2,z3,z5,z6]),(0,[z227,z7,z0,z1,z2,z3,z5]),(0,[z22,z0,z1,z2,z3,z5,z228]),(0,[z98,z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z230,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z231])],[(0,[z15,z205,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z232,z6]),(0,[z233,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z234]),(0,[z22,z0,z1,z2,z3,z5,z65]),(0,[z0,z1,z2,z99,z3,z5,z6]),(0,[z0,z1,z235,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z236])],[(0,[z0,z1,z2,z3,z5,z237,z6]),(1,[z7,z27,z1,z2,z3,z5]),(0,[z0,z1,z2,z238,z3,z5,z6]),(0,[z239,z7,z0,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z240,z3,z5]),(0,[z98,z0,z1,z3,z113,z5,z6]),(0,[z0,z1,z241,z2,z3,z5,z6]),(0,[z207,z83,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z242,z5,z6]),(0,[z0,z1,z2,z3,z40,z122,z6])]],
   [[(0,[z0,z1,z2,z243,z3,z5,z6]),(0,[z0,z1,z2,z3,z244,z5,z6]),(0,[z22,z1,z2,z3,z5,z36,z6])],[(0,[z0,z1,z2,z146,z3,z5,z6]),(0,[z0,z1,z2,z245,z3,z5,z6]),(0,[z0,z246,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z216,z3,z5,z6]),(0,[z247,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z248,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z26,z5,z6])],[(0,[z0,z1,z28,z3,z5,z211,z6]),(0,[z0,z1,z2,z249,z3,z5,z6]),(1,[z7,z22,z1,z2,z3,z5]),(0,[z0,z1,z250,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z54]),(0,[z0,z1,z2,z3,z5,z65,z251])],[(0,[z0,z1,z252,z2,z3,z5,z6]),(0,[z253,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z254,z2,z3,z5,z6]),(0,[z0,z255,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z256,z3,z5,z6]),(0,[z0,z1,z2,z257,z3,z5,z6]),(0,[z0,z1,z2,z3,z258,z5,z6]),(0,[z0,z259,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z260]),(0,[z0,z1,z261,z2,z3,z5,z6])],[(0,[z0,z262,z1,z2,z3,z5,z6]),(0,[z145,z208,z1,z2,z3,z5,z6]),(1,[z98,z0,z99,z3,z5,z6]),(0,[z0,z1,z178,z263,z3,z5,z6])],[(0,[z264,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z138,z6]),(0,[z0,z1,z2,z47,z3,z211,z6]),(0,[z0,z1,z64,z3,z5,z6,z54]),(0,[z265,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z266,z2,z3,z5,z6]),(0,[z0,z1,z267,z2,z3,z5,z6]),(0,[z7,z0,z131,z1,z2,z3,z5]),(0,[z0,z1,z199,z2,z3,z5,z6]),(0,[z0,z268,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z269,z5,z6]),(0,[z0,z1,z2,z270,z3,z5,z6]),(0,[z98,z0,z131,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z271,z6]),(0,[z0,z1,z2,z3,z5,z6,z272]),(0,[z0,z1,z178,z2,z3,z211,z6])],[(1,[z0,z1,z2,z273,z3,z5]),(0,[z0,z1,z2,z274,z3,z5,z6]),(0,[z0,z1,z2,z275,z3,z5,z6]),(1,[z0,z1,z2,z223,z5,z6]),(0,[z0,z115,z1,z2,z51,z3,z6])],[(0,[z276,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z277,z6]),(0,[z0,z1,z2,z240,z3,z5,z6]),(0,[z22,z0,z50,z1,z2,z3,z5]),(1,[z0,z1,z10,z3,z5,z6]),(0,[z0,z278,z1,z2,z3,z5,z6])],[(0,[z0,z19,z1,z2,z3,z5,z126]),(0,[z0,z1,z2,z279,z3,z5,z6]),(0,[z0,z1,z280,z2,z3,z5,z6])],[(0,[z22,z0,z1,z53,z2,z3,z5]),(0,[z0,z281,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z282,z3,z5,z6]),(0,[z0,z1,z2,z71,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z283,z6])],[(1,[z167,z13,z2,z3,z5,z6]),(0,[z0,z284,z1,z2,z3,z5,z6]),(0,[z15,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z285,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z286]),(0,[z0,z1,z2,z287,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z288,z6]),(0,[z289,z0,z1,z2,z3,z5,z6])],[(0,[z22,z0,z1,z13,z2,z3,z5]),(0,[z205,z0,z1,z290,z3,z5,z6]),(0,[z291,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z292,z6]),(0,[z0,z1,z2,z3,z5,z122,z6])]],
   [[(0,[z195,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z64,z2,z3,z5]),(0,[z22,z0,z293,z1,z2,z3,z5])],[(0,[z85,z0,z1,z53,z3,z5,z6]),(0,[z7,z22,z0,z1,z2,z3,z5]),(0,[z7,z0,z204,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z229,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z294])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z0,z79,z1,z2,z3,z5,z295]),(0,[z0,z1,z2,z47,z3,z52,z6])],[(0,[z0,z1,z2,z3,z244,z5,z16]),(0,[z7,z0,z1,z263,z2,z3,z5]),(0,[z0,z1,z296,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z297,z5,z6]),(0,[z0,z1,z298,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z299])],[(0,[z205,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z300,z3,z5,z6])],[(1,[z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z301,z3,z5,z6]),(0,[z0,z302,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z224,z3,z5,z6])],[(0,[z0,z1,z2,z303,z3,z5,z6]),(0,[z0,z1,z304,z2,z3,z5,z6]),(1,[z15,z1,z2,z3,z209,z6]),(0,[z22,z0,z1,z2,z275,z3,z5]),(0,[z305,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z306,z3,z80,z6]),(0,[z0,z115,z1,z2,z3,z72,z6]),(0,[z0,z1,z2,z3,z307,z5,z6]),(0,[z0,z1,z2,z308,z3,z5,z6]),(0,[z0,z1,z2,z309,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z120,z6])],[(0,[z167,z0,z19,z2,z3,z5,z6]),(0,[z27,z1,z13,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z78,z5,z6]),(0,[z0,z1,z2,z3,z310,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z311])]],
   [[(0,[z208,z0,z1,z2,z180,z5,z6]),(0,[z0,z1,z2,z3,z5,z312,z6]),(0,[z0,z1,z2,z109,z3,z5,z6]),(0,[z0,z1,z2,z5,z122,z6,z17])],[(0,[z313,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z8,z6]),(1,[z0,z1,z100,z3,z5,z6]),(0,[z0,z50,z1,z2,z47,z3,z6]),(0,[z314,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z122,z6,z315]),(0,[z0,z1,z2,z316,z3,z5,z6])],[(0,[z0,z317,z1,z2,z3,z5,z6]),(0,[z0,z1,z28,z3,z123,z5,z6]),(0,[z0,z1,z2,z318,z3,z5,z6]),(0,[z0,z1,z2,z3,z319,z5,z6]),(0,[z0,z1,z2,z3,z320,z5,z6]),(0,[z0,z1,z321,z2,z3,z5,z6]),(0,[z12,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z322,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z323,z6])],[(0,[z145,z1,z2,z3,z180,z5,z6]),(0,[z7,z205,z0,z1,z2,z3,z5])],[(0,[z324,z0,z1,z2,z3,z5,z6]),(0,[z325,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z326,z2,z3,z5,z6]),(0,[z83,z0,z1,z53,z3,z5,z6]),(0,[z0,z1,z2,z327,z3,z5,z6]),(0,[z0,z79,z204,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z328,z6]),(0,[z0,z1,z2,z3,z5,z198,z6]),(0,[z0,z1,z2,z109,z3,z5,z122])],[(0,[z0,z1,z2,z3,z5,z6,z329]),(0,[z0,z1,z330,z2,z3,z5,z6]),(0,[z7,z0,z1,z250,z2,z3,z5]),(1,[z0,z1,z2,z331,z5,z6]),(0,[z0,z1,z2,z3,z332,z5,z6])],[(0,[z0,z1,z2,z3,z333,z5,z6]),(0,[z0,z1,z2,z3,z334,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z335]),(0,[z145,z0,z1,z2,z52,z5,z6]),(0,[z0,z1,z2,z336,z3,z5,z6]),(0,[z0,z337,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z338,z5,z6]),(0,[z0,z339,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z67,z68])]],
   [[(0,[z7,z1,z2,z28,z3,z5,z6]),(0,[z340,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z49,z2,z3,z5]),(0,[z7,z0,z1,z2,z121,z3,z5]),(0,[z0,z1,z2,z306,z3,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z65]),(0,[z0,z1,z2,z341,z3,z5,z6])],[(0,[z145,z0,z1,z226,z3,z5,z6]),(0,[z0,z131,z1,z263,z3,z5,z6]),(0,[z0,z204,z1,z2,z275,z5,z6]),(0,[z0,z1,z2,z214,z3,z5,z165])],[(0,[z155,z0,z1,z2,z3,z5,z6]),(0,[z7,z12,z0,z1,z2,z3,z5]),(0,[z342,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z343,z5,z6]),(0,[z0,z1,z344,z2,z3,z5,z6])],[(0,[z0,z1,z2,z345,z3,z5,z6]),(0,[z0,z1,z2,z142,z3,z5,z6])],[(0,[z7,z145,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z346,z5,z16,z6]),(0,[z7,z0,z1,z2,z3,z151,z5]),(1,[z0,z1,z2,z3,z5,z347]),(0,[z12,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z65,z20]),(0,[z0,z1,z82,z3,z123,z5,z6]),(0,[z0,z1,z2,z51,z3,z67,z6]),(0,[z0,z1,z2,z3,z5,z348,z6])],[(0,[z76,z19,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z349,z3,z5,z6]),(0,[z145,z0,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z3,z209,z5,z6]),(0,[z233,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z26,z80,z5,z6]),(0,[z0,z1,z2,z3,z72,z211,z6]),(0,[z0,z1,z2,z123,z52,z5,z6])],[(0,[z0,z350,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z67,z5]),(0,[z0,z1,z351,z2,z3,z5,z6]),(1,[z0,z115,z2,z3,z11,z6]),(0,[z352,z0,z1,z2,z3,z5,z6])],[(0,[z353,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z354,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z346,z5,z6]),(0,[z0,z1,z2,z3,z5,z355,z6])]],
   [[(0,[z356,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z357,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z358,z6])],[(0,[z0,z1,z178,z28,z3,z5,z6]),(0,[z359,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z295,z6]),(0,[z0,z1,z2,z3,z113,z72,z6]),(0,[z0,z1,z2,z3,z5,z360,z6]),(0,[z0,z1,z2,z5,z68,z6,z166])],[(0,[z167,z22,z0,z1,z2,z3,z5]),(0,[z7,z22,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z5,z6]),(0,[z0,z361,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z362,z6]),(0,[z0,z1,z2,z363,z3,z5,z6])],[(0,[z7,z0,z35,z2,z3,z5,z6]),(0,[z0,z364,z1,z2,z3,z5,z6])],[(0,[z7,z0,z1,z103,z2,z3,z5]),(0,[z22,z0,z1,z2,z3,z52,z5]),(0,[z0,z79,z2,z3,z80,z5,z6]),(0,[z0,z1,z2,z365,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z366]),(0,[z0,z1,z2,z3,z5,z367,z6])],[(0,[z0,z1,z2,z3,z368,z5,z6]),(0,[z7,z27,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z5,z251]),(0,[z0,z1,z369,z2,z3,z5,z6])],[(0,[z370,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z72]),(0,[z22,z0,z1,z2,z99,z3,z5]),(0,[z0,z1,z2,z371,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z65,z6]),(0,[z0,z1,z2,z3,z372,z5,z6])],[(0,[z7,z0,z115,z1,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z48]),(0,[z0,z1,z2,z3,z5,z373,z6])]],
   [[(0,[z0,z374,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z375]),(0,[z7,z0,z1,z2,z3,z5,z68]),(0,[z22,z0,z1,z2,z214,z3,z5]),(0,[z376,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z3,z5,z6])],[(0,[z377,z0,z1,z2,z3,z5,z6]),(1,[z205,z1,z2,z3,z16,z6]),(0,[z7,z0,z1,z2,z3,z123,z5]),(0,[z0,z1,z2,z3,z5,z68,z251]),(0,[z0,z1,z263,z2,z3,z113,z6])],[(0,[z0,z1,z2,z3,z5,z174,z6]),(0,[z208,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z378,z5,z6])],[(0,[z0,z1,z2,z3,z5,z379,z6]),(0,[z0,z1,z380,z2,z3,z5,z6])],[(0,[z381,z0,z1,z2,z3,z5,z6]),(0,[z27,z0,z1,z53,z3,z5,z6]),(0,[z0,z382,z1,z2,z3,z5,z6]),(0,[z0,z204,z1,z2,z52,z5,z6]),(0,[z0,z1,z2,z3,z5,z251,z54]),(0,[z0,z1,z2,z3,z383,z5,z6])],[(1,[z0,z384,z1,z2,z3,z5]),(0,[z385,z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z49,z2,z3,z138,z6]),(0,[z0,z1,z2,z386,z3,z5,z6])],[(0,[z239,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z226,z3,z5,z6]),(0,[z208,z0,z1,z2,z52,z5,z6]),(0,[z0,z79,z1,z2,z80,z5,z6]),(0,[z0,z387,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z388,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z389]),(0,[z0,z1,z2,z390,z3,z5,z6])],[(0,[z0,z1,z2,z391,z3,z5,z6]),(0,[z0,z1,z2,z392,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z393]),(0,[z145,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z394,z5,z6]),(0,[z395,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z396,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z122,z165])]],
   [[(0,[z76,z0,z1,z397,z3,z5,z6]),(0,[z12,z0,z19,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z315]),(0,[z0,z1,z2,z398,z3,z5,z6])],[(0,[z0,z1,z399,z2,z3,z5,z6]),(0,[z0,z1,z2,z400,z3,z5,z6]),(0,[z27,z1,z2,z3,z5,z36,z6]),(0,[z98,z0,z1,z82,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z119]),(0,[z0,z1,z401,z2,z3,z5,z6]),(0,[z0,z1,z402,z2,z3,z5,z6])],[(0,[z7,z0,z1,z2,z28,z3,z5]),(0,[z0,z131,z1,z103,z3,z5,z6]),(0,[z0,z1,z2,z403,z3,z5,z6]),(1,[z0,z1,z263,z3,z211,z6])],[(0,[z404,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z53,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z405,z6]),(0,[z0,z1,z2,z3,z5,z68,z17])],[(0,[z0,z1,z2,z3,z5,z6,z406]),(0,[z0,z1,z2,z3,z67,z209,z6]),(0,[z0,z1,z2,z3,z407,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z408]),(0,[z0,z1,z2,z409,z3,z180,z6]),(1,[z0,z1,z2,z279,z5,z6]),(0,[z7,z0,z250,z2,z3,z5,z6]),(0,[z7,z0,z74,z1,z2,z3,z5]),(0,[z0,z1,z410,z2,z3,z5,z6]),(0,[z98,z222,z1,z2,z3,z5,z6]),(0,[z0,z2,z275,z3,z80,z5,z6]),(0,[z0,z1,z100,z3,z80,z5,z6]),(0,[z411,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z251,z17])],[(0,[z0,z1,z2,z3,z5,z412,z6]),(0,[z342,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z413,z6]),(1,[z259,z1,z2,z3,z5,z6])],[(0,[z414,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z180,z5]),(1,[z0,z1,z2,z245,z3,z6]),(0,[z0,z1,z2,z3,z415,z5,z6]),(0,[z22,z0,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z228,z6]),(0,[z0,z1,z2,z416,z3,z5,z6])]],
   [[(0,[z7,z0,z1,z2,z3,z5,z16]),(0,[z22,z0,z1,z2,z3,z80,z5]),(0,[z0,z103,z2,z99,z3,z5,z6]),(0,[z0,z417,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z418,z6])],[(0,[z0,z419,z1,z2,z3,z5,z6])],[(0,[z420,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z49,z26,z5,z6]),(0,[z0,z1,z2,z421,z3,z5,z6])],[(0,[z422,z0,z1,z2,z3,z5,z6]),(1,[z0,z317,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z423,z6]),(0,[z0,z424,z1,z2,z3,z5,z6]),(1,[z208,z1,z2,z142,z5,z6]),(0,[z0,z1,z2,z425,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z426,z6]),(0,[z0,z1,z2,z3,z5,z427,z6])],[(0,[z0,z131,z1,z28,z3,z5,z6]),(0,[z0,z384,z1,z2,z3,z5,z6]),(0,[z145,z0,z1,z2,z180,z5,z6]),(0,[z0,z1,z428,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z80,z5,z6]),(0,[z0,z1,z2,z3,z5,z429,z6]),(1,[z0,z1,z2,z430,z5,z6]),(0,[z431,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z432,z6])],[(1,[z0,z1,z397,z3,z5,z6]),(0,[z22,z0,z1,z433,z2,z3,z5]),(0,[z0,z1,z434,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z211,z6]),(0,[z0,z1,z2,z51,z3,z113,z6])],[(0,[z167,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z186,z6]),(0,[z0,z1,z2,z3,z5,z6,z435]),(0,[z436,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z290,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z113,z5]),(0,[z340,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z437,z6]),(0,[z438,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z439,z0,z1,z2,z3,z5,z6]),(0,[z0,z440,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z28,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z209,z5]),(0,[z22,z0,z1,z2,z3,z5,z120])],[(0,[z0,z1,z2,z3,z441,z5,z6]),(0,[z0,z293,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z442,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z32]),(0,[z98,z0,z1,z26,z3,z5,z6])],[(0,[z0,z1,z2,z397,z3,z5,z6]),(0,[z7,z0,z1,z199,z2,z3,z5]),(0,[z7,z0,z1,z2,z3,z5,z60]),(0,[z0,z1,z2,z443,z3,z5,z6]),(0,[z444,z0,z1,z2,z3,z5,z6]),(0,[z445,z0,z1,z2,z3,z5,z6])],[(0,[z167,z76,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z446,z6]),(1,[z0,z1,z71,z3,z5,z6]),(0,[z12,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z121,z3,z5,z17])],[(0,[z0,z1,z2,z290,z3,z5,z6]),(0,[z0,z204,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z447,z5,z6]),(0,[z0,z1,z2,z3,z5,z448,z6]),(0,[z0,z1,z2,z449,z3,z5,z6]),(0,[z0,z1,z2,z3,z190,z5,z6]),(0,[z0,z1,z2,z3,z450,z5,z6])],[(0,[z0,z1,z2,z451,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z65]),(0,[z0,z131,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z452,z5,z6]),(0,[z0,z1,z2,z453,z3,z5,z6])],[(0,[z19,z1,z13,z2,z3,z5,z6]),(0,[z208,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z454,z6])],[(0,[z0,z1,z2,z455,z3,z5,z6]),(0,[z0,z1,z178,z53,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z456,z6]),(0,[z0,z1,z2,z3,z5,z6,z457]),(0,[z0,z1,z2,z3,z5,z458,z6]),(0,[z459,z0,z1,z2,z3,z5,z6])]],
   [[(1,[z0,z1,z2,z460,z3,z5]),(0,[z461,z0,z1,z2,z3,z5,z6])],[(0,[z22,z0,z19,z1,z2,z3,z5]),(0,[z0,z1,z2,z2,z3,z5,z6]),(1,[z7,z0,z1,z2,z240,z5]),(0,[z7,z0,z1,z2,z109,z3,z5]),(0,[z0,z1,z2,z3,z5,z462,z6]),(0,[z463,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z464,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z59]),(0,[z0,z115,z1,z2,z47,z3,z6]),(0,[z0,z1,z2,z3,z5,z68,z20]),(0,[z0,z1,z49,z2,z123,z5,z6])],[(0,[z76,z0,z19,z2,z3,z5,z6]),(0,[z0,z465,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z466]),(1,[z0,z1,z2,z3,z5,z198])],[(0,[z0,z1,z2,z467,z3,z5,z6]),(0,[z0,z1,z2,z121,z52,z5,z6])],[(0,[z0,z1,z13,z2,z3,z5,z6]),(0,[z468,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z165]),(0,[z0,z50,z1,z2,z3,z5,z469]),(0,[z0,z470,z1,z2,z3,z5,z6])],[(0,[z15,z0,z1,z2,z47,z3,z6]),(0,[z22,z0,z1,z2,z442,z3,z5]),(0,[z22,z0,z1,z2,z26,z3,z5]),(1,[z471,z1,z2,z3,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z251]),(0,[z0,z1,z472,z2,z3,z5,z6]),(0,[z0,z1,z3,z113,z5,z211,z6])],[(0,[z0,z473,z1,z2,z3,z5,z6]),(1,[z0,z1,z199,z3,z5,z6]),(0,[z474,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z475,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z476]),(0,[z0,z1,z2,z477,z3,z5,z6])]],
   [[(0,[z0,z478,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z5,z156]),(0,[z0,z50,z2,z3,z5,z72,z6]),(0,[z0,z2,z3,z5,z251,z6,z20]),(0,[z0,z1,z49,z26,z3,z5,z6]),(0,[z0,z1,z2,z479,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z480,z6]),(0,[z7,z0,z1,z2,z240,z5,z6]),(0,[z0,z1,z2,z3,z481,z5,z6]),(1,[z0,z1,z2,z3,z6,z315]),(0,[z0,z482,z1,z2,z3,z5,z6])],[(0,[z0,z1,z483,z2,z3,z5,z6])],[(0,[z0,z1,z2,z484,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z485])],[(0,[z22,z0,z1,z2,z3,z481,z5]),(0,[z0,z1,z2,z3,z5,z68,z6]),(0,[z0,z1,z2,z3,z5,z6,z486])],[(0,[z0,z1,z487,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z488,z5,z6]),(0,[z0,z1,z2,z3,z5,z489,z6]),(0,[z0,z1,z2,z3,z5,z6,z490]),(0,[z0,z1,z2,z3,z5,z491,z6])],[(0,[z7,z0,z1,z13,z2,z3,z5]),(0,[z145,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z97]),(0,[z0,z1,z2,z3,z5,z251,z6]),(0,[z0,z1,z2,z3,z432,z5,z6]),(0,[z492,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z493,z3,z5,z6]),(0,[z0,z1,z2,z3,z40,z5,z6])],[(0,[z494,z0,z1,z2,z3,z5,z6]),(0,[z145,z0,z1,z2,z142,z5,z6]),(0,[z208,z1,z2,z142,z3,z5,z6]),(0,[z0,z35,z1,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z331,z5,z6]),(0,[z0,z1,z495,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z496,z5,z6]),(0,[z0,z1,z2,z3,z497,z5,z6])]],
   [[(0,[z0,z1,z2,z69,z3,z5,z6])],[(0,[z0,z1,z2,z3,z498,z5,z6]),(0,[z0,z1,z178,z3,z113,z5,z6]),(0,[z0,z1,z2,z3,z5,z68,z122])],[(0,[z499,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z500,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z501])],[(0,[z0,z1,z28,z3,z5,z6,z54]),(0,[z0,z1,z2,z3,z502,z5,z6]),(0,[z15,z0,z1,z2,z3,z209,z6]),(1,[z0,z204,z2,z275,z5,z6]),(0,[z0,z204,z2,z275,z3,z5,z6]),(0,[z503,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z6,z165]),(0,[z0,z1,z2,z3,z504,z5,z6])],[(0,[z0,z179,z1,z13,z2,z3,z5]),(0,[z7,z1,z2,z3,z5,z6,z156]),(0,[z0,z1,z2,z3,z223,z5,z6])],[(1,[z76,z19,z2,z3,z5,z6]),(1,[z85,z1,z28,z3,z5,z6]),(0,[z7,z0,z1,z2,z275,z3,z5]),(0,[z0,z1,z2,z3,z5,z505,z6]),(0,[z506,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z507,z5,z6]),(0,[z76,z22,z0,z1,z2,z3,z5]),(1,[z83,z0,z1,z3,z5,z65]),(0,[z0,z1,z508,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z509,z6]),(0,[z0,z1,z510,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z511,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z512])],[(0,[z513,z0,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z142,z3,z5]),(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z0,z514,z1,z2,z3,z5,z6])],[(0,[z0,z131,z1,z53,z3,z5,z6]),(0,[z0,z1,z2,z187,z3,z5,z6]),(0,[z515,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z516,z6])],[],[(0,[z385,z0,z1,z2,z3,z5,z6]),(0,[z205,z0,z1,z2,z3,z16,z6]),(0,[z0,z1,z2,z3,z5,z517,z6]),(0,[z22,z0,z79,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z20,z17]),(0,[z0,z1,z2,z3,z5,z518,z6]),(0,[z0,z1,z2,z3,z519,z5,z6])],[(0,[z0,z1,z520,z2,z3,z5,z6]),(0,[z0,z79,z1,z2,z275,z5,z6]),(1,[z0,z1,z2,z3,z5,z469]),(0,[z0,z1,z3,z5,z65,z6,z54]),(0,[z0,z521,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z522,z6]),(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z205,z0,z1,z2,z51,z3,z6]),(0,[z0,z1,z2,z3,z523,z5,z6]),(0,[z0,z1,z2,z3,z5,z469,z6]),(0,[z0,z1,z2,z524,z3,z5,z6])],[(0,[z525,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z142,z3,z5,z97]),(1,[z22,z1,z2,z3,z5,z36]),(0,[z0,z1,z2,z3,z5,z6,z48])]],
   [[(0,[z0,z1,z2,z3,z5,z234,z6]),(0,[z0,z1,z2,z3,z5,z526,z6]),(1,[z0,z1,z2,z3,z5,z175]),(0,[z0,z1,z64,z2,z3,z5,z6])],[(1,[z0,z1,z399,z2,z3,z5]),(0,[z0,z1,z2,z460,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z60,z6]),(0,[z22,z0,z1,z2,z3,z5,z54]),(0,[z0,z1,z527,z2,z3,z5,z6]),(0,[z0,z1,z2,z121,z3,z5,z122])],[(0,[z0,z1,z53,z3,z5,z211,z6]),(0,[z0,z1,z2,z3,z528,z5,z6])],[(0,[z210,z0,z1,z2,z3,z5,z6]),(1,[z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z529,z6])],[(1,[z12,z0,z2,z3,z5,z251])],[(0,[z76,z1,z2,z28,z3,z5,z6]),(0,[z0,z1,z2,z3,z163,z5,z6]),(0,[z0,z1,z2,z430,z5,z72,z6]),(0,[z530,z0,z1,z2,z3,z5,z6])],[(0,[z531,z0,z1,z2,z3,z5,z6]),(0,[z208,z0,z1,z2,z142,z5,z6]),(0,[z0,z1,z2,z273,z3,z5,z6])],[(0,[z227,z0,z1,z2,z3,z5,z6]),(0,[z183,z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z36,z6]),(0,[z0,z50,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z532,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z533,z5,z6])],[(0,[z0,z1,z2,z121,z180,z5,z6]),(0,[z0,z534,z1,z2,z3,z5,z6]),(0,[z0,z1,z535,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z536,z6])],[(0,[z0,z1,z2,z3,z5,z6,z141]),(0,[z22,z0,z1,z2,z3,z5,z17]),(0,[z537,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z538,z6]),(0,[z205,z0,z1,z77,z3,z5,z6]),(1,[z0,z1,z2,z3,z8,z6]),(0,[z0,z1,z539,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z540,z5,z6]),(0,[z0,z1,z2,z3,z5,z541,z6])],[(0,[z0,z1,z2,z187,z3,z180,z5]),(1,[z7,z0,z1,z199,z3,z5]),(0,[z0,z1,z542,z2,z3,z5,z6]),(1,[z0,z1,z2,z543,z3,z6]),(0,[z0,z1,z2,z3,z5,z544,z6])],[(0,[z0,z1,z2,z3,z545,z5,z6]),(0,[z0,z1,z2,z546,z3,z5,z6]),(0,[z7,z0,z1,z2,z99,z3,z5]),(0,[z22,z0,z1,z434,z2,z3,z5]),(0,[z98,z0,z1,z99,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z547,z6]),(0,[z0,z1,z2,z47,z121,z5,z6])],[(0,[z499,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z548,z5,z6]),(0,[z7,z0,z1,z2,z47,z3,z5]),(0,[z22,z0,z1,z2,z3,z5,z36]),(0,[z22,z0,z1,z64,z2,z3,z5]),(0,[z0,z1,z549,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z550,z6]),(0,[z0,z115,z50,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z551,z6]),(0,[z0,z1,z2,z552,z3,z5,z6]),(0,[z0,z1,z553,z2,z3,z5,z6])],[(0,[z0,z1,z2,z180,z5,z6,z17]),(0,[z7,z0,z1,z2,z214,z3,z5]),(0,[z22,z22,z0,z1,z2,z3,z5]),(0,[z22,z0,z204,z1,z2,z3,z5]),(0,[z0,z1,z2,z51,z52,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z554,z6]),(0,[z0,z1,z2,z3,z5,z555,z6]),(0,[z0,z556,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z80,z123,z5,z6]),(0,[z0,z1,z2,z3,z5,z557,z6])],[(0,[z0,z1,z2,z558,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z11,z5]),(0,[z559,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z560,z6]),(0,[z0,z1,z561,z2,z3,z5,z6])],[(0,[z76,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z562,z2,z3,z5,z6]),(0,[z0,z1,z2,z563,z3,z5,z6]),(0,[z0,z1,z2,z564,z3,z5,z6]),(0,[z0,z1,z2,z214,z3,z6,z165])],[(0,[z0,z1,z2,z460,z3,z180,z5]),(1,[z0,z1,z2,z3,z5,z295]),(0,[z0,z1,z2,z3,z5,z6,z565]),(0,[z0,z1,z2,z3,z566,z5,z6]),(0,[z0,z1,z263,z2,z3,z5,z6])],[(0,[z0,z1,z567,z2,z3,z5,z6]),(0,[z568,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z569,z3,z5,z6]),(0,[z15,z1,z2,z3,z209,z5,z6]),(0,[z0,z1,z433,z2,z3,z5,z6]),(0,[z0,z570,z1,z2,z3,z5,z6]),(0,[z571,z0,z1,z2,z3,z5,z6])],[(0,[z205,z1,z2,z3,z5,z16,z6]),(0,[z572,z0,z1,z2,z3,z5,z6]),(0,[z0,z115,z2,z3,z11,z5,z6])],[(1,[z0,z1,z2,z3,z5,z174]),(0,[z0,z1,z2,z3,z209,z5,z375]),(0,[z0,z1,z2,z3,z151,z5,z6]),(0,[z573,z0,z1,z2,z3,z5,z6]),(0,[z0,z79,z1,z2,z47,z5,z6]),(0,[z0,z1,z2,z3,z5,z251,z165]),(0,[z0,z1,z2,z214,z3,z67,z6])],[(0,[z7,z0,z1,z2,z151,z5,z6]),(0,[z574,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z575,z6]),(0,[z0,z1,z2,z543,z3,z5,z6]),(0,[z0,z1,z576,z2,z3,z5,z6])],[(0,[z167,z1,z13,z2,z3,z5,z6]),(0,[z0,z1,z399,z2,z28,z3,z5]),(0,[z0,z1,z53,z3,z123,z5,z6]),(0,[z0,z1,z2,z273,z3,z5,z16]),(0,[z577,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z64,z2,z3,z5,z54])],[(1,[z0,z1,z2,z346,z5,z6]),(0,[z0,z1,z103,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z430,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z578])],[(0,[z0,z1,z2,z3,z5,z579,z6]),(0,[z0,z580,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z581]),(0,[z0,z1,z2,z582,z3,z5,z6])],[(0,[z0,z583,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z156]),(0,[z0,z1,z82,z2,z123,z5,z6])],[(1,[z0,z35,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z584]),(0,[z0,z1,z2,z3,z67,z5,z6])],[(0,[z0,z317,z1,z13,z2,z3,z5]),(0,[z22,z0,z1,z2,z121,z3,z5]),(0,[z83,z0,z1,z64,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z585,z6]),(0,[z0,z1,z586,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z80,z5]),(0,[z0,z1,z587,z2,z3,z5,z6]),(0,[z12,z0,z2,z3,z5,z251,z6]),(0,[z0,z1,z2,z588,z3,z5,z6]),(0,[z0,z589,z1,z2,z3,z5,z6])]],
   [[(0,[z590,z0,z1,z2,z3,z5,z6]),(0,[z591,z0,z1,z2,z3,z5,z6])],[(0,[z22,z0,z1,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z17,z165])],[(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z0,z1,z2,z121,z5,z122,z6])],[(0,[z0,z1,z49,z28,z3,z5,z6]),(0,[z0,z1,z2,z3,z16,z6,z165]),(0,[z0,z1,z2,z47,z51,z5,z6]),(0,[z0,z1,z593,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z6,z166])],[(0,[z0,z384,z1,z2,z28,z3,z5]),(0,[z0,z1,z2,z121,z142,z5,z6]),(0,[z0,z1,z2,z3,z209,z5,z234]),(0,[z0,z1,z49,z2,z3,z432,z6]),(0,[z594,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z178,z2,z190,z5,z6]),(0,[z0,z1,z2,z595,z3,z5,z6])],[(0,[z596,z0,z1,z2,z3,z5,z6]),(0,[z0,z74,z2,z3,z5,z6,z20])],[(0,[z0,z1,z2,z3,z5,z597,z6]),(0,[z0,z1,z598,z2,z3,z5,z6]),(0,[z0,z1,z2,z409,z3,z5,z6]),(0,[z0,z1,z2,z3,z599,z5,z6]),(0,[z7,z0,z1,z2,z3,z5,z120]),(0,[z98,z471,z1,z2,z3,z5,z6]),(0,[z207,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z600,z6]),(0,[z0,z1,z2,z51,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z601,z6]),(0,[z0,z1,z602,z2,z3,z5,z6]),(0,[z0,z1,z2,z603,z3,z5,z6]),(0,[z15,z22,z0,z1,z2,z3,z5]),(0,[z0,z604,z1,z2,z3,z5,z6]),(0,[z0,z605,z1,z2,z3,z5,z6])],[(0,[z0,z1,z606,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z607,z5,z6]),(0,[z7,z98,z0,z1,z2,z3,z5]),(0,[z608,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z609,z6]),(0,[z0,z1,z610,z2,z3,z5,z6])],[(0,[z210,z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z611]),(0,[z0,z1,z2,z612,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z613,z6]),(0,[z0,z614,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z244,z5]),(0,[z22,z0,z1,z82,z2,z3,z5]),(0,[z0,z1,z2,z615,z3,z5,z6]),(0,[z0,z1,z49,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z616,z6])],[(0,[z7,z0,z50,z1,z2,z3,z5]),(0,[z0,z1,z263,z2,z3,z211,z6]),(0,[z617,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z618,z2,z3,z5,z6]),(0,[z0,z1,z178,z2,z3,z113,z6]),(0,[z0,z1,z2,z3,z619,z5,z6]),(1,[z0,z1,z2,z214,z3,z165])],[(0,[z0,z1,z53,z2,z3,z5,z186]),(0,[z1,z2,z142,z3,z180,z5,z6]),(0,[z22,z0,z1,z2,z3,z5,z68]),(0,[z0,z1,z2,z620,z3,z5,z6])],[(0,[z7,z0,z1,z53,z2,z3,z5]),(0,[z621,z0,z1,z2,z3,z5,z6]),(1,[z0,z250,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z555,z6]),(0,[z0,z1,z2,z26,z275,z5,z6]),(0,[z0,z2,z3,z11,z5,z72,z6]),(0,[z0,z1,z2,z3,z11,z211,z6]),(0,[z0,z1,z2,z3,z123,z5,z6]),(0,[z0,z1,z178,z2,z224,z5,z6]),(0,[z622,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z623]),(0,[z624,z0,z1,z2,z3,z5,z6]),(0,[z7,z0,z19,z1,z2,z3,z5]),(0,[z7,z208,z0,z1,z2,z3,z5]),(0,[z22,z0,z1,z2,z3,z5,z122]),(0,[z625,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z626,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z555,z6]),(0,[z0,z1,z2,z3,z5,z122,z251])],[(0,[z0,z1,z627,z2,z3,z5,z6]),(0,[z0,z1,z628,z2,z3,z5,z6]),(0,[z0,z1,z629,z2,z3,z5,z6]),(0,[z0,z1,z2,z52,z5,z6,z17])],[(1,[z0,z1,z2,z3,z5,z126]),(0,[z0,z1,z2,z630,z3,z5,z6]),(0,[z0,z1,z2,z47,z123,z5,z6])],[(0,[z22,z0,z1,z2,z51,z3,z5]),(0,[z98,z0,z1,z263,z3,z5,z6])],[(1,[z0,z1,z2,z409,z3,z6]),(0,[z631,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z632,z5,z6]),(0,[z0,z1,z2,z142,z5,z6,z17]),(0,[z7,z0,z1,z2,z26,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z54])],[(0,[z1,z2,z28,z3,z5,z36,z6]),(0,[z0,z1,z2,z279,z5,z16,z6]),(1,[z0,z1,z351,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z20,z54]),(0,[z633,z0,z1,z2,z3,z5,z6]),(0,[z0,z634,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z245,z3,z180,z6]),(0,[z0,z1,z635,z2,z3,z5,z6]),(1,[z7,z0,z250,z2,z3,z5]),(0,[z7,z0,z1,z2,z3,z5,z156]),(0,[z0,z1,z2,z3,z5,z6,z347]),(0,[z0,z204,z1,z2,z80,z5,z6]),(0,[z0,z1,z2,z636,z3,z5,z6]),(0,[z637,z0,z1,z2,z3,z5,z6]),(0,[z0,z638,z1,z2,z3,z5,z6])]],
   [[(0,[z167,z0,z13,z2,z3,z5,z6]),(0,[z0,z13,z2,z3,z5,z6,z20]),(0,[z85,z0,z1,z28,z3,z5,z6]),(0,[z0,z1,z2,z109,z121,z5,z6])],[(0,[z76,z0,z1,z567,z3,z5,z6]),(0,[z7,z15,z0,z1,z2,z3,z5]),(1,[z7,z0,z1,z2,z151,z5]),(1,[z7,z0,z1,z2,z3,z8]),(0,[z22,z0,z1,z178,z2,z3,z5]),(0,[z0,z1,z351,z3,z5,z72,z6])],[(0,[z0,z1,z2,z3,z5,z6,z639]),(1,[z7,z0,z1,z71,z3,z5]),(0,[z22,z0,z1,z2,z3,z5,z211]),(0,[z640,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z641,z2,z3,z5,z6])],[(0,[z0,z1,z2,z642,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z643,z6]),(1,[z145,z1,z2,z180,z5,z6]),(0,[z644,z0,z1,z2,z3,z5,z6])],[(0,[z0,z645,z1,z2,z3,z5,z6]),(0,[z0,z1,z646,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z375]),(0,[z353,z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z647,z3,z5,z6]),(1,[z0,z1,z2,z69,z5,z6])],[(0,[z22,z0,z1,z2,z3,z5,z16]),(0,[z0,z1,z2,z3,z209,z6,z165]),(0,[z0,z50,z1,z2,z3,z11,z6]),(0,[z0,z1,z648,z2,z3,z5,z6]),(1,[z0,z1,z82,z123,z5,z6]),(0,[z0,z1,z649,z2,z3,z5,z6]),(0,[z0,z650,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z651,z6]),(0,[z0,z1,z2,z652,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z17])],[(0,[z359,z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z653,z5,z6]),(0,[z83,z259,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z3,z120,z6]),(0,[z0,z1,z2,z121,z3,z5,z6]),(0,[z0,z654,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z85,z0,z1,z2,z3,z5]),(0,[z0,z115,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z655]),(0,[z85,z0,z1,z2,z3,z5,z6]),(0,[z98,z0,z1,z2,z3,z5,z175]),(0,[z0,z1,z49,z2,z26,z5,z6]),(0,[z0,z1,z2,z51,z3,z211,z6])],[(0,[z0,z1,z2,z3,z5,z60,z6]),(0,[z0,z656,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z657,z6]),(0,[z658,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z659,z2,z3,z5,z6]),(0,[z0,z1,z2,z26,z52,z5,z6]),(0,[z0,z1,z2,z47,z5,z6,z17])],[(0,[z0,z660,z1,z2,z3,z5,z6]),(0,[z27,z85,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z180,z5,z6]),(0,[z7,z7,z0,z1,z2,z3,z5]),(1,[z7,z0,z35,z2,z3,z5]),(0,[z0,z79,z1,z2,z3,z5,z347]),(0,[z0,z1,z2,z661,z3,z5,z6]),(1,[z0,z1,z3,z163,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z662])],[(0,[z83,z0,z1,z28,z3,z5,z6]),(0,[z15,z0,z1,z2,z3,z5,z6]),(0,[z98,z22,z0,z1,z2,z3,z5]),(0,[z663,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z664])],[(1,[z0,z131,z103,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z665,z6]),(0,[z0,z1,z2,z3,z5,z20,z165]),(0,[z0,z1,z2,z3,z5,z666,z6]),(0,[z667,z0,z1,z2,z3,z5,z6])],[(1,[z0,z1,z567,z3,z5,z6]),(0,[z668,z0,z1,z2,z3,z5,z6]),(0,[z205,z0,z1,z2,z47,z3,z6]),(0,[z0,z1,z669,z2,z3,z5,z6]),(0,[z471,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z306,z3,z6]),(0,[z12,z0,z1,z2,z3,z5,z251])],[(0,[z0,z1,z2,z3,z5,z670,z6]),(0,[z590,z22,z0,z1,z2,z3,z5])]],
   [[(0,[z7,z0,z1,z2,z142,z3,z5])],[(0,[z22,z0,z131,z1,z2,z3,z5]),(0,[z0,z1,z2,z671,z3,z5,z6]),(0,[z0,z1,z26,z3,z123,z5,z6]),(1,[z0,z1,z2,z47,z120,z6]),(0,[z0,z1,z2,z47,z3,z6,z165]),(0,[z0,z1,z2,z672,z3,z5,z6])],[(0,[z0,z673,z1,z2,z3,z5,z6]),(0,[z0,z74,z1,z2,z3,z5,z20]),(0,[z0,z1,z263,z3,z5,z211,z6]),(0,[z0,z674,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z675,z3,z5,z6]),(0,[z7,z0,z79,z1,z2,z3,z5]),(1,[z0,z1,z2,z240,z5,z6]),(0,[z1,z2,z3,z5,z36,z6,z156]),(0,[z0,z1,z2,z3,z331,z5,z6]),(0,[z0,z1,z10,z3,z80,z5,z6])],[(1,[z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z5,z676,z6]),(0,[z0,z677,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z51,z3,z52,z6]),(0,[z0,z1,z678,z2,z3,z5,z6])],[(0,[z0,z1,z679,z2,z3,z5,z6]),(0,[z98,z0,z1,z103,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z680,z6]),(0,[z0,z1,z2,z3,z681,z5,z6]),(0,[z83,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z682,z6]),(0,[z0,z1,z2,z47,z3,z67,z6])],[(0,[z7,z0,z1,z2,z3,z52,z5]),(0,[z0,z1,z2,z3,z67,z68,z6])],[(0,[z7,z0,z1,z2,z3,z5,z251]),(0,[z22,z0,z1,z2,z109,z3,z5]),(0,[z0,z131,z1,z3,z113,z5,z6]),(0,[z0,z1,z2,z3,z683,z5,z6]),(0,[z0,z1,z2,z3,z5,z684,z6]),(0,[z0,z1,z2,z3,z5,z685,z6])]],
   [[(0,[z0,z1,z2,z3,z686,z5,z6]),(0,[z0,z1,z687,z2,z3,z5,z6]),(0,[z0,z1,z2,z275,z123,z5,z6]),(0,[z0,z1,z688,z2,z3,z5,z6])],[(0,[z689,z0,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z28,z3,z5]),(0,[z404,z7,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z543,z3,z80,z6]),(0,[z0,z1,z2,z3,z690,z5,z6]),(0,[z691,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z692,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z693,z6]),(0,[z0,z1,z2,z3,z694,z5,z6]),(0,[z0,z1,z2,z3,z5,z695,z6])],[(0,[z0,z222,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z696,z6]),(0,[z697,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z122,z20])],[(0,[z205,z0,z1,z2,z3,z209,z6]),(0,[z22,z0,z1,z2,z3,z5,z165]),(0,[z698,z0,z1,z2,z3,z5,z6]),(0,[z0,z699,z1,z2,z3,z5,z6]),(0,[z0,z79,z1,z2,z52,z5,z6]),(1,[z0,z50,z2,z3,z72,z6]),(0,[z0,z1,z2,z700,z3,z5,z6]),(0,[z0,z1,z2,z3,z113,z5,z6])],[(0,[z22,z0,z1,z263,z2,z3,z5]),(0,[z0,z74,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z701,z6]),(0,[z0,z1,z2,z702,z3,z5,z6]),(0,[z0,z1,z2,z703,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z704]),(0,[z0,z1,z2,z3,z5,z6,z20])],[(0,[z0,z1,z2,z3,z5,z705,z6]),(0,[z0,z1,z2,z3,z5,z16,z6]),(1,[z7,z0,z1,z2,z3,z60]),(0,[z0,z131,z1,z26,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z706])],[(0,[z98,z0,z1,z28,z3,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z460,z151,z5]),(0,[z0,z1,z290,z51,z3,z6]),(0,[z0,z1,z2,z216,z5,z17]),(0,[z0,z1,z2,z707,z5,z6]),(0,[z644,z0,z1,z2,z47,z6])],[(0,[z0,z1,z2,z708,z3,z6]),(0,[z0,z1,z2,z409,z121,z6]),(1,[z0,z1,z2,z151,z60]),(0,[z7,z0,z1,z2,z240,z8]),(0,[z0,z250,z2,z3,z5,z68]),(0,[z0,z1,z2,z709,z5,z6])],[(0,[z1,z710,z2,z3,z5,z6]),(0,[z12,z0,z179,z2,z3,z5]),(0,[z0,z1,z711,z3,z5,z6]),(0,[z0,z1,z712,z3,z5,z6]),(0,[z27,z1,z712,z3,z5,z6]),(0,[z0,z1,z713,z3,z5,z6]),(0,[z7,z0,z1,z71,z240,z5]),(0,[z0,z1,z2,z3,z8,z165]),(0,[z7,z1,z2,z316,z3,z5]),(0,[z0,z1,z2,z47,z323,z6]),(0,[z0,z1,z2,z121,z122,z315])],[(0,[z0,z1,z714,z3,z5,z6]),(0,[z715,z1,z2,z3,z5,z6]),(0,[z0,z50,z3,z163,z72,z6])],[(0,[z0,z1,z2,z409,z3,z6]),(0,[z0,z1,z71,z151,z5,z6]),(0,[z0,z1,z2,z3,z251,z315]),(0,[z0,z1,z3,z5,z65,z716])],[(0,[z7,z1,z2,z300,z3,z5]),(0,[z530,z22,z1,z2,z3,z5]),(0,[z0,z1,z717,z3,z5,z6])],[(0,[z0,z1,z146,z47,z5,z6]),(0,[z145,z1,z2,z409,z180,z6]),(0,[z7,z0,z1,z2,z3,z718]),(0,[z0,z1,z2,z240,z8,z6]),(0,[z22,z0,z1,z2,z719,z5]),(0,[z720,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z5,z721,z6])],[(0,[z19,z710,z2,z3,z5,z6]),(0,[z0,z1,z2,z722,z3,z5]),(0,[z7,z0,z1,z2,z3,z723]),(0,[z7,z0,z1,z2,z331,z5]),(0,[z0,z1,z2,z3,z5,z724]),(1,[z0,z2,z725,z5,z6]),(0,[z0,z1,z2,z5,z726,z17]),(0,[z0,z1,z2,z3,z68,z727])]],
   [[(0,[z0,z1,z2,z3,z6,z728]),(0,[z1,z2,z3,z5,z6,z729]),(0,[z0,z1,z2,z109,z5,z17])],[(0,[z0,z1,z2,z3,z730,z6]),(0,[z731,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z732]),(0,[z0,z1,z2,z224,z113,z6]),(0,[z733,z1,z2,z3,z5,z6])],[(0,[z0,z734,z2,z3,z5,z6]),(0,[z0,z1,z2,z409,z6,z17]),(0,[z7,z1,z2,z3,z5,z189]),(0,[z22,z0,z1,z351,z3,z5]),(0,[z0,z1,z2,z3,z5,z735])],[(0,[z27,z1,z53,z3,z5,z6]),(0,[z0,z1,z2,z736,z3,z6]),(0,[z145,z1,z2,z180,z5,z6]),(0,[z7,z0,z35,z2,z240,z5]),(0,[z0,z1,z2,z3,z737,z6])],[(0,[z0,z1,z2,z738,z5,z6]),(0,[z0,z1,z2,z3,z5,z739]),(0,[z0,z1,z2,z3,z59,z728]),(0,[z0,z1,z2,z3,z5,z375]),(0,[z7,z0,z1,z2,z738,z5])],[(0,[z76,z169,z2,z3,z5,z6]),(0,[z250,z2,z28,z3,z5,z6]),(0,[z0,z131,z392,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z348]),(0,[z22,z222,z1,z2,z3,z5]),(0,[z0,z740,z2,z3,z5,z6]),(0,[z0,z1,z2,z109,z5,z726])],[(0,[z0,z179,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z186]),(0,[z0,z1,z2,z741,z5,z6]),(0,[z0,z1,z2,z187,z3,z5]),(0,[z7,z207,z1,z199,z3,z5]),(0,[z742,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z743,z5,z6]),(0,[z0,z1,z2,z190,z5,z6]),(0,[z0,z1,z95,z3,z113,z6])],[(0,[z7,z27,z1,z2,z3,z60]),(0,[z7,z0,z1,z2,z744,z5]),(0,[z7,z1,z472,z2,z3,z5]),(0,[z0,z1,z306,z100,z3,z6]),(0,[z0,z1,z2,z3,z745,z6])]],
   [[(0,[z0,z1,z2,z746,z3,z5]),(0,[z145,z1,z2,z187,z180,z5]),(0,[z0,z1,z199,z151,z5,z6]),(0,[z747,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z671,z5,z122]),(0,[z0,z1,z2,z748,z5,z6]),(0,[z749,z0,z1,z3,z5,z6])],[(0,[z0,z1,z750,z2,z3,z5]),(0,[z0,z1,z2,z47,z488,z6]),(0,[z7,z0,z1,z751,z3,z5]),(0,[z752,z0,z1,z2,z3,z5]),(0,[z753,z0,z1,z2,z3,z5]),(0,[z22,z0,z1,z2,z3,z40])],[(0,[z0,z1,z77,z3,z5,z6]),(0,[z208,z22,z1,z2,z142,z5]),(0,[z754,z222,z1,z2,z3,z5]),(0,[z0,z1,z178,z3,z113,z6])],[(0,[z7,z22,z1,z2,z3,z60]),(0,[z7,z1,z649,z2,z3,z5]),(0,[z755,z0,z1,z2,z3,z5]),(0,[z0,z1,z3,z756,z5,z6])],[(0,[z1,z567,z28,z3,z5,z6]),(0,[z0,z131,z103,z3,z5,z6]),(0,[z0,z1,z49,z757,z5,z6]),(0,[z0,z1,z2,z47,z367,z6])],[(0,[z27,z1,z567,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z758]),(0,[z0,z1,z2,z306,z3,z6]),(0,[z0,z1,z2,z3,z5,z119])],[(0,[z0,z1,z759,z2,z5,z6]),(0,[z0,z1,z2,z187,z245,z3]),(0,[z7,z0,z1,z2,z760,z5]),(0,[z0,z1,z2,z78,z5,z175]),(0,[z0,z1,z2,z761,z5,z6]),(0,[z0,z50,z2,z3,z762,z6]),(0,[z0,z482,z2,z3,z5,z251]),(0,[z0,z1,z2,z123,z432,z6]),(0,[z207,z83,z1,z3,z5,z65])],[(0,[z0,z1,z2,z3,z5,z763]),(0,[z0,z1,z2,z672,z5,z17])]],
   [[(0,[z359,z0,z1,z2,z3,z8]),(0,[z0,z35,z2,z240,z5,z6]),(0,[z1,z2,z3,z5,z6,z764])],[(0,[z710,z13,z2,z3,z5,z6]),(0,[z0,z1,z765,z3,z5,z6]),(0,[z7,z1,z2,z28,z240,z5]),(0,[z0,z1,z199,z3,z5,z186]),(0,[z0,z1,z71,z240,z5,z6]),(0,[z0,z1,z2,z3,z5,z727])],[(0,[z0,z1,z2,z240,z5,z6]),(0,[z0,z1,z2,z273,z3,z60]),(0,[z22,z1,z2,z3,z5,z236]),(0,[z766,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z767,z5,z6]),(0,[z0,z1,z2,z3,z768,z5])],[(0,[z7,z0,z1,z2,z3,z229]),(0,[z22,z0,z1,z49,z26,z5]),(0,[z98,z471,z99,z3,z5,z6]),(0,[z0,z769,z1,z2,z3,z5])],[(0,[z0,z1,z53,z3,z555,z6]),(0,[z574,z1,z2,z3,z16,z6]),(0,[z0,z1,z3,z770,z5,z6]),(0,[z83,z0,z1,z442,z3,z5]),(0,[z0,z204,z2,z725,z5,z6]),(0,[z0,z2,z3,z11,z762,z6])],[(0,[z7,z35,z2,z28,z3,z5]),(0,[z0,z1,z2,z3,z5,z771]),(0,[z7,z0,z1,z226,z3,z5]),(0,[z7,z0,z1,z2,z240,z60]),(0,[z0,z250,z2,z3,z5,z65]),(0,[z1,z2,z3,z5,z729,z156]),(0,[z0,z1,z2,z47,z6,z389])],[(0,[z0,z1,z772,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z773]),(0,[z7,z0,z1,z2,z279,z5]),(0,[z7,z22,z1,z2,z3,z5]),(0,[z0,z1,z2,z240,z5,z122]),(0,[z774,z0,z1,z2,z3,z5]),(0,[z98,z0,z99,z3,z5,z32]),(0,[z0,z103,z775,z3,z5,z6]),(0,[z0,z1,z776,z3,z5,z6]),(0,[z777,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z0,z1,z100,z3,z5])],[(0,[z0,z710,z2,z3,z5,z6]),(0,[z0,z1,z778,z2,z3,z6]),(0,[z22,z0,z250,z2,z3,z5]),(0,[z7,z503,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z430,z5])],[(0,[z0,z1,z399,z71,z3,z5]),(0,[z0,z1,z779,z3,z5,z6]),(0,[z530,z1,z2,z3,z209,z6]),(0,[z7,z0,z204,z2,z275,z5]),(0,[z667,z22,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z780]),(0,[z781,z0,z1,z2,z3,z5]),(0,[z0,z1,z508,z123,z5,z6]),(0,[z782,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z783]),(0,[z0,z1,z2,z784,z3,z6]),(0,[z22,z0,z1,z2,z151,z5]),(0,[z7,z0,z1,z2,z785,z5]),(0,[z0,z1,z64,z71,z3,z5]),(0,[z7,z0,z1,z2,z69,z5]),(0,[z12,z0,z434,z2,z3,z5]),(0,[z0,z1,z2,z786,z3,z6]),(0,[z0,z2,z3,z5,z787,z6])],[(0,[z0,z1,z2,z3,z788,z6]),(0,[z0,z1,z2,z789,z3,z5]),(0,[z0,z1,z790,z3,z5,z6]),(0,[z22,z0,z1,z71,z3,z5]),(0,[z0,z115,z2,z230,z3,z6]),(0,[z0,z339,z2,z3,z5,z20]),(0,[z0,z1,z2,z791,z120,z6])],[(0,[z0,z1,z2,z279,z6,z165]),(0,[z7,z0,z1,z2,z3,z60]),(0,[z0,z1,z199,z240,z5,z6])],[(0,[z0,z1,z2,z3,z5,z792]),(0,[z0,z1,z2,z744,z5,z6]),(0,[z7,z0,z1,z2,z793,z5]),(0,[z0,z250,z2,z3,z5,z165]),(0,[z0,z1,z2,z223,z5,z6]),(0,[z0,z1,z2,z3,z693,z165])],[(0,[z0,z1,z2,z3,z5,z794]),(0,[z0,z143,z2,z80,z5,z6]),(0,[z0,z2,z3,z5,z795,z6])]],
   [[(0,[z22,z0,z1,z2,z190,z5]),(0,[z0,z1,z2,z52,z5,z347])],[(0,[z0,z1,z2,z3,z5,z796]),(0,[z0,z1,z2,z279,z67,z6]),(0,[z0,z1,z82,z331,z5,z6]),(0,[z0,z79,z2,z80,z5,z295]),(0,[z797,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z798])],[(0,[z0,z1,z2,z3,z5,z799]),(0,[z7,z0,z250,z199,z3,z5]),(0,[z7,z340,z1,z71,z3,z5]),(0,[z0,z1,z2,z3,z5,z800]),(0,[z0,z1,z801,z3,z5,z6])],[(0,[z0,z1,z802,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z803]),(0,[z1,z53,z712,z3,z5,z6]),(0,[z7,z0,z1,z2,z409,z3]),(0,[z0,z1,z2,z3,z5,z804]),(0,[z7,z471,z1,z2,z3,z5]),(0,[z7,z1,z357,z2,z3,z5]),(0,[z1,z2,z3,z5,z6,z805]),(0,[z0,z1,z2,z3,z5,z806])],[(0,[z167,z22,z13,z2,z3,z5]),(1,[z1,z712,z3,z5,z6]),(0,[z0,z1,z2,z3,z807,z5]),(0,[z0,z1,z2,z3,z5,z808]),(0,[z7,z0,z1,z199,z151,z5]),(0,[z0,z1,z178,z3,z756,z6])],[(0,[z22,z0,z35,z2,z3,z5]),(0,[z7,z0,z1,z2,z809,z5]),(0,[z7,z1,z2,z3,z5,z729]),(0,[z340,z0,z1,z433,z3,z5]),(0,[z222,z1,z2,z331,z5,z6]),(0,[z0,z1,z2,z3,z5,z810]),(0,[z811,z0,z1,z2,z3,z5]),(0,[z0,z1,z3,z812,z5,z6]),(0,[z207,z1,z2,z3,z5,z54])],[(0,[z205,z22,z1,z2,z3,z16]),(0,[z22,z0,z1,z3,z163,z5]),(0,[z813,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z5,z347]),(0,[z0,z1,z757,z123,z5,z6]),(0,[z0,z1,z2,z814,z5,z6])],[(0,[z0,z1,z2,z3,z815,z6]),(0,[z0,z1,z816,z3,z5,z6]),(0,[z22,z1,z2,z3,z5,z299]),(0,[z0,z1,z3,z113,z555,z6]),(1,[z0,z1,z3,z756,z6])]],
   [[(0,[z7,z250,z2,z28,z3,z5]),(0,[z0,z1,z2,z817,z3,z5]),(0,[z0,z35,z2,z3,z60,z6]),(0,[z0,z1,z2,z5,z6,z818]),(0,[z0,z1,z2,z3,z40,z68])],[(0,[z7,z0,z1,z2,z3,z5]),(0,[z525,z1,z28,z3,z5,z6]),(0,[z0,z1,z2,z460,z245,z3]),(0,[z0,z1,z2,z5,z59,z17]),(0,[z0,z1,z2,z3,z5,z819]),(0,[z0,z115,z1,z2,z430,z6])],[(0,[z0,z1,z2,z3,z820,z6]),(0,[z15,z1,z2,z3,z209,z6]),(0,[z0,z1,z2,z3,z60,z6]),(0,[z12,z0,z250,z2,z3,z5]),(0,[z0,z1,z2,z121,z151,z5]),(0,[z821,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z224,z211,z6]),(0,[z0,z1,z2,z5,z6,z822]),(0,[z0,z1,z2,z5,z6,z726])],[(0,[z0,z1,z567,z3,z5,z739]),(0,[z7,z384,z1,z2,z3,z5]),(0,[z0,z1,z2,z823,z3,z6]),(0,[z22,z0,z1,z290,z3,z5]),(0,[z7,z0,z1,z2,z3,z824]),(0,[z0,z1,z2,z825,z3,z6]),(0,[z0,z1,z2,z826,z5,z6]),(0,[z0,z1,z2,z3,z5,z827]),(0,[z0,z1,z2,z3,z20,z315]),(0,[z0,z1,z2,z757,z5,z6]),(0,[z0,z2,z3,z5,z828,z6]),(0,[z0,z1,z2,z51,z52,z6])],[(0,[z0,z1,z2,z151,z8,z6]),(0,[z7,z1,z380,z2,z3,z5]),(0,[z22,z0,z131,z103,z3,z5]),(0,[z0,z1,z2,z3,z5,z829]),(0,[z0,z830,z1,z2,z3,z5]),(0,[z0,z1,z831,z2,z3,z5])],[(0,[z0,z1,z2,z832,z3,z6]),(0,[z7,z0,z1,z833,z3,z5]),(0,[z0,z834,z1,z2,z3,z5]),(0,[z0,z835,z1,z2,z3,z5]),(0,[z0,z1,z2,z78,z5,z6]),(0,[z0,z1,z100,z3,z5,z6]),(0,[z0,z79,z2,z80,z5,z6])],[(0,[z0,z1,z2,z3,z836,z6]),(0,[z7,z0,z35,z199,z3,z5]),(0,[z7,z1,z2,z3,z8,z156]),(0,[z0,z1,z2,z52,z6,z294])],[(0,[z137,z1,z53,z3,z5,z6]),(0,[z837,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z331,z5,z32]),(0,[z0,z1,z2,z838,z5,z6])]],
   [[(0,[z145,z0,z1,z2,z409,z6]),(0,[z7,z0,z1,z2,z839,z5]),(0,[z0,z250,z2,z3,z151,z5])],[(0,[z0,z1,z2,z840,z3,z5]),(0,[z7,z0,z1,z146,z3,z5]),(0,[z7,z0,z1,z2,z245,z3]),(0,[z22,z0,z1,z199,z3,z5]),(0,[z0,z50,z351,z3,z72,z6]),(0,[z0,z1,z841,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z97]),(0,[z0,z1,z2,z3,z8,z60]),(0,[z0,z1,z2,z3,z5,z842])],[(0,[z0,z1,z28,z3,z138,z6]),(0,[z155,z0,z35,z2,z3,z5]),(0,[z0,z1,z843,z3,z5,z6])],[(0,[z0,z1,z71,z3,z5,z251]),(0,[z22,z0,z1,z263,z3,z211]),(0,[z222,z1,z2,z3,z5,z175]),(0,[z0,z1,z10,z26,z5,z6]),(0,[z0,z1,z2,z121,z40,z122])],[(0,[z7,z76,z19,z2,z3,z5]),(0,[z1,z2,z746,z28,z3,z5]),(0,[z7,z1,z2,z3,z196,z5]),(0,[z0,z1,z2,z844,z3,z5]),(0,[z0,z1,z351,z223,z5,z6])],[(0,[z167,z710,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z845]),(0,[z205,z1,z2,z279,z16,z6]),(0,[z7,z0,z1,z2,z741,z5]),(0,[z7,z0,z1,z846,z3,z5]),(0,[z7,z0,z1,z847,z3,z5]),(0,[z0,z1,z2,z151,z5,z20]),(0,[z0,z1,z2,z848,z3,z6]),(0,[z0,z1,z2,z5,z251,z166])],[(0,[z145,z22,z1,z2,z180,z5]),(0,[z0,z1,z2,z849,z3,z5]),(0,[z183,z0,z1,z2,z240,z5]),(0,[z7,z1,z2,z3,z5,z84]),(0,[z0,z1,z2,z430,z5,z850]),(0,[z0,z1,z2,z51,z683,z6]),(0,[z0,z1,z2,z3,z851,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z852]),(0,[z0,z1,z853,z3,z5,z6])],[(0,[z0,z1,z2,z854,z3,z6]),(0,[z0,z1,z2,z3,z5,z855]),(0,[z0,z1,z2,z5,z6,z856]),(0,[z7,z1,z2,z3,z5,z418]),(0,[z0,z857,z2,z3,z5,z6])],[(0,[z0,z1,z858,z3,z5,z6]),(0,[z0,z250,z2,z3,z60,z6]),(0,[z0,z1,z2,z859,z3,z6])],[(0,[z0,z1,z2,z3,z860,z6]),(0,[z0,z1,z146,z52,z5,z6]),(0,[z0,z1,z2,z3,z5,z861]),(0,[z0,z79,z2,z306,z80,z6])],[(0,[z0,z1,z2,z862,z5,z6]),(0,[z7,z0,z1,z397,z3,z5]),(0,[z1,z2,z28,z3,z5,z186]),(0,[z0,z1,z2,z3,z5,z863]),(0,[z0,z1,z2,z864,z5,z6]),(0,[z0,z1,z2,z865,z5,z6]),(0,[z0,z1,z2,z3,z138,z6])],[(0,[z7,z622,z1,z2,z3,z5]),(0,[z7,z0,z1,z2,z543,z3]),(0,[z0,z1,z775,z3,z5,z6])],[(0,[z0,z1,z866,z3,z5,z6]),(0,[z0,z35,z2,z151,z5,z6]),(0,[z98,z0,z99,z3,z5,z175]),(0,[z867,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z78,z555,z6]),(0,[z0,z1,z2,z3,z5,z850]),(0,[z0,z1,z2,z868,z5,z6]),(0,[z0,z1,z2,z3,z5,z869]),(0,[z0,z1,z263,z3,z756,z6])]],
   [[(0,[z0,z1,z28,z190,z5,z6]),(0,[z0,z1,z2,z151,z5,z6]),(0,[z0,z1,z290,z47,z3,z6]),(0,[z205,z1,z290,z3,z16,z6]),(0,[z7,z1,z2,z442,z3,z5]),(0,[z7,z35,z2,z3,z5,z156]),(0,[z0,z1,z2,z3,z762,z6])],[(0,[z0,z1,z870,z3,z5,z6]),(0,[z0,z1,z2,z3,z8,z234]),(0,[z7,z264,z1,z2,z3,z5]),(0,[z7,z1,z71,z3,z5,z156])],[(0,[z7,z0,z1,z2,z346,z5]),(0,[z7,z1,z2,z3,z5,z156]),(0,[z22,z0,z1,z2,z5,z166]),(0,[z0,z1,z2,z306,z26,z6])],[(0,[z0,z1,z2,z3,z5,z871]),(0,[z7,z0,z872,z2,z3,z5]),(0,[z0,z1,z2,z151,z5,z68]),(0,[z0,z1,z2,z3,z5,z729]),(0,[z0,z1,z2,z873,z3,z5]),(0,[z0,z1,z2,z3,z5,z48])],[(0,[z0,z1,z2,z874,z5,z6]),(0,[z0,z875,z2,z3,z5,z6]),(0,[z83,z0,z1,z71,z3,z5]),(0,[z0,z876,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z877,z5]),(0,[z0,z1,z2,z3,z5,z726])],[(0,[z0,z1,z878,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z879]),(0,[z0,z1,z2,z880,z5,z6]),(0,[z0,z1,z2,z3,z723,z6]),(0,[z205,z1,z2,z3,z16,z6]),(0,[z22,z0,z1,z866,z3,z5]),(0,[z0,z1,z2,z3,z5,z881])],[(0,[z167,z317,z13,z2,z3,z5]),(0,[z207,z1,z28,z3,z5,z6]),(0,[z0,z1,z2,z5,z234,z882]),(0,[z7,z289,z1,z2,z3,z5]),(0,[z0,z1,z883,z3,z5,z6])],[(0,[z0,z1,z884,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z885]),(0,[z7,z0,z79,z2,z80,z5]),(0,[z886,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z887,z6]),(0,[z0,z1,z2,z3,z791,z6]),(0,[z0,z1,z2,z888,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z889,z5]),(0,[z0,z1,z2,z890,z5,z6]),(0,[z7,z0,z1,z2,z3,z432]),(0,[z891,z1,z2,z3,z5,z6]),(0,[z892,z1,z2,z3,z5,z6])],[(0,[z27,z179,z1,z2,z3,z5]),(0,[z0,z1,z2,z893,z5,z6]),(0,[z0,z384,z1,z2,z3,z5]),(0,[z0,z1,z606,z3,z211,z6]),(0,[z0,z1,z399,z3,z5,z54]),(0,[z27,z1,z2,z3,z5,z186]),(0,[z22,z0,z1,z2,z224,z5]),(0,[z22,z0,z1,z2,z47,z120]),(0,[z0,z1,z2,z3,z6,z894]),(0,[z0,z1,z2,z430,z113,z6]),(0,[z0,z1,z2,z895,z5,z6]),(0,[z0,z1,z896,z2,z3,z5]),(0,[z0,z1,z897,z3,z5,z6])],[(0,[z98,z0,z775,z3,z5,z6]),(0,[z0,z74,z2,z3,z5,z20]),(0,[z0,z1,z2,z3,z5,z898]),(0,[z0,z1,z64,z3,z5,z54])],[(0,[z22,z0,z1,z2,z3,z555]),(0,[z0,z1,z2,z3,z5,z899])],[(0,[z0,z1,z2,z240,z151,z5]),(0,[z0,z148,z2,z275,z5,z6]),(0,[z0,z1,z2,z3,z6,z900]),(0,[z0,z1,z2,z47,z518,z6]),(0,[z0,z1,z2,z47,z360,z6])],[(0,[z227,z0,z1,z2,z3,z60]),(0,[z7,z1,z199,z3,z5,z156]),(0,[z0,z1,z2,z3,z5,z901]),(0,[z0,z902,z1,z2,z3,z5]),(0,[z0,z1,z2,z47,z523,z6]),(0,[z0,z1,z2,z3,z40,z165])],[(0,[z0,z1,z2,z3,z5,z141]),(0,[z0,z1,z2,z3,z903,z6]),(0,[z0,z904,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z223,z5]),(0,[z0,z79,z1,z2,z306,z6]),(0,[z905,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z69,z67,z6])],[(0,[z207,z1,z2,z3,z5,z6]),(0,[z1,z2,z906,z180,z5,z6]),(0,[z0,z1,z2,z3,z6,z907]),(0,[z7,z0,z250,z2,z151,z5]),(0,[z7,z0,z250,z2,z3,z8]),(0,[z574,z22,z1,z2,z3,z5]),(0,[z0,z1,z10,z543,z3,z6]),(0,[z0,z1,z2,z430,z5,z908])]],
   [[(0,[z445,z19,z2,z3,z5,z6]),(0,[z7,z0,z250,z71,z3,z5]),(0,[z0,z250,z2,z151,z5,z6]),(0,[z222,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z306,z3,z819])],[(0,[z7,z27,z1,z28,z3,z5]),(0,[z7,z0,z1,z2,z151,z8])],[(0,[z85,z22,z1,z28,z3,z5]),(0,[z259,z1,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z909,z6]),(0,[z0,z1,z910,z3,z5,z6]),(0,[z667,z1,z2,z180,z5,z6]),(0,[z205,z1,z2,z273,z3,z16]),(0,[z1,z2,z3,z911,z5,z6]),(0,[z353,z0,z250,z2,z3,z5]),(0,[z7,z0,z1,z71,z151,z5]),(0,[z7,z0,z1,z71,z3,z8]),(0,[z7,z250,z2,z3,z5,z156]),(0,[z774,z222,z1,z2,z3,z5]),(0,[z0,z50,z2,z223,z72,z6]),(0,[z0,z912,z1,z2,z3,z5])],[(0,[z222,z1,z2,z3,z5,z6]),(0,[z0,z1,z146,z3,z5,z6]),(0,[z0,z1,z2,z913,z5,z6]),(0,[z0,z1,z2,z245,z3,z6]),(0,[z7,z22,z1,z2,z240,z5]),(0,[z499,z0,z434,z2,z3,z5]),(0,[z0,z1,z2,z306,z3,z829]),(0,[z0,z1,z2,z224,z5,z6])],[(0,[z0,z1,z2,z914,z5,z6]),(0,[z0,z50,z1,z2,z430,z6])],[(0,[z0,z1,z2,z3,z915,z6]),(0,[z0,z916,z2,z3,z5,z6]),(0,[z145,z1,z2,z245,z180,z6]),(0,[z0,z1,z2,z3,z5,z917]),(0,[z0,z1,z2,z3,z5,z234]),(0,[z98,z22,z0,z99,z3,z5])],[(0,[z0,z1,z833,z3,z5,z6]),(0,[z7,z27,z1,z2,z3,z5]),(0,[z0,z250,z2,z3,z5,z60]),(0,[z7,z0,z918,z2,z3,z5]),(0,[z0,z1,z2,z240,z60,z6]),(0,[z0,z1,z2,z331,z5,z175]),(0,[z0,z1,z2,z919,z5,z6]),(0,[z0,z1,z920,z3,z5,z6])],[(0,[z0,z1,z2,z3,z921,z6]),(0,[z0,z1,z922,z3,z5,z6]),(0,[z7,z0,z1,z82,z123,z5]),(0,[z0,z1,z2,z3,z5,z908])]],
   [[(0,[z0,z2,z3,z762,z5,z6]),(0,[z0,z1,z2,z40,z6,z17])],[(0,[z0,z1,z53,z3,z138,z6]),(0,[z0,z1,z2,z3,z923,z5]),(0,[z7,z0,z1,z924,z3,z5]),(0,[z0,z1,z2,z3,z5,z925])],[(0,[z0,z179,z2,z3,z5,z20]),(0,[z7,z98,z1,z28,z3,z5]),(0,[z0,z1,z2,z409,z460,z3]),(0,[z207,z1,z199,z3,z5,z6]),(0,[z0,z1,z2,z78,z229,z6]),(0,[z0,z1,z926,z3,z5,z6])],[(0,[z0,z1,z927,z3,z5,z6]),(0,[z7,z0,z35,z2,z151,z5]),(0,[z7,z0,z35,z2,z3,z8]),(0,[z0,z1,z2,z109,z151,z5]),(0,[z0,z1,z2,z3,z928,z6]),(0,[z0,z1,z2,z164,z5,z17])],[(0,[z0,z1,z929,z3,z5,z6]),(0,[z0,z1,z2,z930,z3,z5]),(0,[z7,z0,z35,z71,z3,z5])],[(0,[z0,z1,z931,z3,z5,z6]),(0,[z208,z1,z2,z142,z5,z59]),(0,[z7,z0,z1,z2,z78,z5]),(0,[z22,z0,z1,z2,z331,z5]),(0,[z98,z0,z99,z3,z5,z6]),(0,[z932,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z933]),(0,[z15,z0,z1,z2,z279,z6]),(0,[z22,z0,z1,z2,z3,z8]),(0,[z7,z0,z1,z2,z934,z5]),(0,[z0,z337,z2,z3,z11,z6])],[(0,[z0,z1,z2,z3,z5,z935]),(0,[z0,z1,z2,z936,z5,z6]),(0,[z0,z1,z937,z3,z5,z6]),(0,[z7,z0,z1,z937,z3,z5]),(0,[z0,z1,z2,z938,z5,z6]),(0,[z0,z1,z939,z3,z5,z6]),(0,[z0,z1,z2,z3,z940,z6])]],
   [[(0,[z7,z492,z1,z2,z3,z5]),(0,[z0,z1,z941,z3,z5,z6])],[(0,[z76,z710,z2,z3,z5,z6]),(0,[z0,z1,z2,z273,z3,z5]),(0,[z0,z204,z1,z2,z306,z6])],[(0,[z0,z942,z2,z3,z5,z6]),(0,[z22,z0,z1,z772,z3,z5]),(0,[z0,z1,z10,z3,z5,z6]),(0,[z0,z514,z2,z3,z5,z20])],[(0,[z0,z1,z2,z3,z5,z943]),(0,[z7,z0,z1,z2,z3,z944]),(0,[z7,z0,z1,z2,z3,z903]),(0,[z7,z0,z1,z945,z3,z5])],[(0,[z0,z1,z2,z946,z3,z5]),(0,[z0,z1,z2,z460,z3,z5]),(0,[z208,z1,z2,z906,z5,z6]),(0,[z0,z1,z2,z273,z3,z67]),(0,[z0,z1,z3,z5,z716,z54])],[(0,[z167,z13,z2,z3,z5,z6]),(0,[z7,z15,z1,z2,z3,z209]),(0,[z7,z0,z1,z2,z240,z5]),(0,[z947,z0,z1,z2,z3,z5]),(0,[z0,z250,z2,z240,z5,z6]),(0,[z222,z1,z2,z3,z555,z6]),(0,[z0,z1,z2,z5,z20,z166])],[(0,[z22,z0,z1,z567,z3,z5]),(0,[z0,z1,z2,z3,z944,z6]),(0,[z85,z384,z1,z28,z3,z5]),(0,[z27,z1,z53,z3,z5,z186]),(0,[z0,z1,z53,z190,z5,z6]),(0,[z145,z1,z2,z460,z180,z5]),(0,[z55,z0,z1,z442,z3,z5]),(0,[z948,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z427,z6])],[(0,[z0,z1,z949,z3,z5,z6]),(0,[z0,z1,z2,z3,z950,z6]),(0,[z1,z2,z3,z911,z16,z6]),(0,[z7,z0,z1,z199,z3,z8]),(0,[z7,z0,z951,z2,z3,z5]),(0,[z7,z0,z1,z2,z306,z3]),(0,[z0,z1,z2,z3,z5,z952]),(0,[z0,z1,z2,z51,z3,z119]),(0,[z953,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z198])]],
   [[(0,[z0,z1,z2,z3,z5,z954]),(0,[z0,z1,z2,z151,z5,z165]),(0,[z0,z1,z351,z3,z113,z6]),(0,[z0,z1,z430,z163,z5,z6])],[(0,[z7,z1,z2,z28,z151,z5]),(0,[z7,z1,z2,z28,z3,z8]),(0,[z0,z1,z2,z3,z6,z955]),(0,[z0,z1,z3,z113,z696,z6]),(0,[z0,z1,z2,z3,z956,z6]),(0,[z0,z1,z2,z3,z957,z6])],[(0,[z0,z1,z2,z958,z5,z6]),(0,[z7,z444,z1,z2,z3,z5]),(0,[z353,z0,z1,z199,z3,z5]),(0,[z0,z1,z959,z3,z5,z6]),(0,[z0,z1,z2,z5,z122,z726])],[(0,[z0,z960,z1,z2,z3,z5]),(0,[z698,z1,z28,z3,z5,z6]),(0,[z0,z1,z250,z2,z151,z5]),(0,[z7,z0,z115,z2,z3,z11]),(0,[z7,z0,z1,z178,z3,z113]),(0,[z506,z22,z1,z2,z3,z5]),(0,[z0,z961,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z756,z6])],[(0,[z0,z1,z28,z331,z5,z6]),(0,[z207,z1,z53,z3,z5,z6]),(0,[z1,z2,z3,z906,z5,z6]),(0,[z7,z0,z250,z2,z3,z60]),(0,[z0,z1,z250,z71,z3,z5]),(0,[z155,z0,z1,z2,z151,z5]),(0,[z0,z293,z2,z3,z5,z20])],[(0,[z0,z1,z2,z793,z5,z6]),(0,[z155,z0,z1,z71,z3,z5]),(1,[z1,z2,z3,z5,z729]),(0,[z0,z1,z2,z962,z5,z6]),(0,[z0,z1,z2,z26,z432,z6]),(0,[z0,z1,z95,z26,z5,z6]),(0,[z0,z1,z178,z190,z113,z6]),(0,[z0,z1,z2,z47,z120,z48]),(0,[z0,z1,z2,z3,z6,z315])],[(0,[z7,z0,z963,z2,z3,z5]),(0,[z385,z0,z1,z2,z151,z5]),(0,[z22,z0,z1,z2,z3,z138]),(0,[z0,z1,z2,z3,z5,z964])],[(0,[z0,z1,z2,z3,z5,z965]),(0,[z0,z1,z751,z3,z5,z6]),(0,[z7,z0,z966,z2,z3,z5]),(0,[z98,z0,z99,z3,z555,z6]),(0,[z0,z1,z967,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z968])],[(0,[z22,z1,z2,z3,z5,z490]),(0,[z0,z1,z2,z47,z17,z165])],[(0,[z0,z1,z2,z3,z969,z6]),(0,[z0,z1,z487,z123,z5,z6]),(0,[z0,z1,z2,z3,z5,z970]),(0,[z7,z0,z1,z2,z51,z52]),(0,[z22,z0,z1,z2,z3,z229]),(0,[z0,z1,z2,z3,z5,z971]),(0,[z0,z1,z2,z3,z972,z6]),(0,[z0,z1,z2,z430,z211,z6]),(0,[z0,z1,z2,z121,z40,z6]),(0,[z0,z1,z2,z3,z6,z727])],[(0,[z7,z0,z50,z2,z3,z72]),(0,[z7,z0,z1,z49,z26,z5]),(0,[z0,z1,z2,z3,z5,z973]),(1,[z0,z1,z2,z3,z727])],[(0,[z0,z1,z974,z3,z5,z6]),(0,[z7,z83,z1,z28,z3,z5]),(0,[z0,z1,z846,z3,z5,z6]),(0,[z15,z1,z2,z595,z3,z6]),(0,[z975,z0,z1,z2,z3,z5]),(0,[z7,z98,z0,z99,z3,z5]),(0,[z22,z1,z2,z493,z3,z5]),(0,[z98,z0,z173,z3,z5,z6]),(0,[z0,z1,z2,z976,z3,z5])],[(0,[z76,z22,z19,z2,z3,z5]),(0,[z384,z1,z2,z3,z5,z36]),(0,[z22,z0,z1,z2,z279,z5]),(0,[z7,z43,z1,z2,z3,z5]),(0,[z438,z22,z1,z2,z3,z5]),(0,[z0,z1,z2,z331,z5,z6]),(0,[z0,z977,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z978,z6]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z980,z2,z3,z5,z6]),(0,[z0,z1,z2,z52,z480,z6]),(0,[z0,z35,z2,z3,z5,z251]),(0,[z22,z0,z1,z100,z3,z5]),(0,[z0,z1,z2,z3,z981,z6]),(0,[z0,z1,z2,z3,z5,z982]),(0,[z0,z1,z2,z983,z5,z6]),(0,[z0,z1,z2,z3,z67,z68])],[(0,[z0,z1,z2,z3,z984,z6]),(0,[z0,z1,z2,z3,z5,z985]),(0,[z0,z1,z2,z3,z5,z986]),(0,[z22,z0,z1,z2,z430,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z987]),(0,[z0,z1,z2,z3,z5,z988]),(0,[z0,z1,z2,z409,z187,z3]),(0,[z7,z0,z35,z2,z3,z60]),(0,[z22,z0,z204,z2,z275,z5])],[(0,[z0,z1,z2,z244,z346,z5]),(0,[z22,z0,z1,z2,z69,z5])],[(0,[z0,z1,z2,z273,z346,z5]),(0,[z0,z650,z2,z3,z72,z6])],[(0,[z22,z0,z1,z2,z3,z60]),(0,[z0,z1,z2,z3,z5,z347]),(0,[z0,z1,z2,z3,z5,z989]),(0,[z0,z1,z2,z3,z990,z6]),(0,[z129,z0,z1,z3,z5,z65])],[],[(0,[z0,z1,z2,z3,z5,z991]),(0,[z0,z115,z2,z3,z11,z6])],[(0,[z7,z22,z1,z199,z3,z5]),(0,[z200,z22,z1,z2,z3,z5])],[(0,[z0,z1,z2,z992,z5,z6]),(0,[z471,z1,z2,z331,z5,z6]),(0,[z0,z1,z2,z993,z5,z6]),(0,[z0,z1,z2,z3,z5,z994]),(0,[z0,z995,z2,z3,z5,z6])]],
   [[(0,[z0,z996,z2,z3,z5,z6]),(0,[z7,z259,z1,z2,z3,z5]),(0,[z222,z1,z2,z3,z229,z6])],[(0,[z1,z712,z28,z3,z5,z6]),(0,[z0,z1,z2,z3,z718,z6]),(0,[z22,z0,z1,z2,z409,z3]),(0,[z7,z0,z980,z2,z3,z5]),(0,[z22,z471,z1,z2,z3,z5]),(0,[z0,z1,z2,z719,z5,z6]),(0,[z0,z1,z2,z3,z5,z469]),(0,[z0,z1,z2,z51,z383,z6])],[(0,[z0,z1,z2,z3,z997,z6]),(0,[z15,z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z52,z505,z6])],[(0,[z0,z1,z2,z3,z5,z998]),(0,[z0,z1,z2,z3,z999,z59]),(0,[z205,z1,z2,z346,z16,z6]),(0,[z22,z1,z2,z3,z5,z729]),(0,[z0,z1,z2,z3,z5,z1000]),(0,[z0,z1,z2,z5,z6,z1001]),(0,[z0,z1,z1002,z3,z5,z6])],[(0,[z0,z1,z1003,z3,z5,z6]),(0,[z98,z0,z349,z3,z5,z6]),(0,[z7,z0,z1,z77,z3,z5]),(0,[z7,z0,z1,z199,z3,z60]),(0,[z0,z1,z199,z3,z5,z54]),(0,[z0,z1,z2,z151,z60,z6]),(0,[z22,z0,z1,z2,z3,z315]),(0,[z0,z1,z2,z3,z5,z175]),(0,[z0,z50,z2,z3,z72,z119]),(0,[z0,z1,z1004,z3,z5,z6])],[(0,[z0,z1,z399,z2,z3,z5]),(0,[z7,z0,z1,z3,z163,z5]),(0,[z1005,z471,z1,z2,z3,z5]),(0,[z0,z1,z2,z1006,z5,z6])],[(1,[z710,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1007]),(0,[z7,z1,z2,z28,z3,z60]),(0,[z7,z1,z2,z3,z60,z156]),(0,[z1,z2,z3,z5,z6,z1008]),(0,[z0,z1,z2,z5,z6,z1009])],[(0,[z342,z0,z1,z2,z481,z5]),(0,[z0,z1,z2,z331,z555,z6])]],
   [[(0,[z0,z1,z2,z3,z885,z6]),(0,[z208,z1,z2,z242,z5,z6]),(0,[z0,z1,z250,z2,z3,z60]),(0,[z7,z0,z1,z10,z3,z5]),(0,[z0,z74,z250,z2,z3,z5]),(0,[z233,z0,z1,z2,z3,z23]),(0,[z0,z1,z2,z1010,z5,z6])],[(0,[z0,z1,z2,z5,z6,z1011]),(0,[z155,z0,z1,z2,z3,z60]),(0,[z0,z1,z263,z3,z555,z6]),(0,[z0,z1,z10,z306,z3,z6]),(0,[z265,z0,z2,z3,z5,z251]),(0,[z0,z1,z2,z3,z1012,z6]),(0,[z0,z1,z2,z5,z791,z6])],[(0,[z1,z712,z2,z3,z5,z6]),(0,[z98,z0,z99,z3,z229,z6])],[(0,[z7,z1,z28,z3,z5,z211]),(0,[z0,z918,z2,z3,z5,z6]),(0,[z15,z1,z2,z3,z209,z375]),(0,[z22,z1,z2,z3,z372,z5]),(0,[z0,z131,z3,z681,z5,z6]),(0,[z0,z1013,z1,z2,z3,z5]),(0,[z0,z1,z1014,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1015]),(0,[z754,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1016])],[(0,[z0,z1,z2,z1017,z3,z6]),(0,[z0,z1,z226,z3,z5,z6]),(0,[z384,z259,z1,z2,z3,z5]),(0,[z7,z340,z1,z2,z3,z5]),(0,[z0,z1018,z2,z3,z5,z6]),(0,[z183,z0,z250,z2,z3,z5]),(0,[z0,z1,z2,z69,z6,z165])],[(0,[z0,z1,z2,z1019,z5,z6]),(0,[z7,z1,z178,z28,z3,z5]),(0,[z0,z951,z2,z3,z5,z6]),(0,[z7,z0,z1,z2,z3,z1020]),(0,[z0,z1,z2,z3,z151,z60]),(0,[z0,z1,z71,z3,z8,z6]),(0,[z0,z1,z2,z3,z23,z165]),(0,[z471,z1,z2,z3,z5,z175]),(0,[z1021,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z5,z6,z1022]),(0,[z0,z1,z2,z177,z52,z6]),(0,[z0,z1,z3,z5,z716,z6]),(0,[z0,z1,z2,z1023,z3,z5])],[(0,[z0,z1,z567,z3,z5,z954]),(0,[z0,z1,z1024,z3,z5,z6]),(0,[z22,z0,z1,z146,z3,z5]),(0,[z22,z0,z1,z2,z245,z3]),(0,[z404,z0,z250,z2,z3,z5]),(0,[z0,z1,z1025,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z1026,z6]),(0,[z1,z199,z28,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z60]),(0,[z0,z1,z2,z725,z5,z6]),(0,[z0,z1,z2,z3,z5,z1027])],[(0,[z200,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z1,z2,z3,z1029,z6]),(0,[z45,z0,z1,z2,z216,z5]),(0,[z0,z1,z2,z3,z1030,z6]),(0,[z0,z1,z49,z26,z432,z6]),(0,[z0,z1,z263,z3,z211,z6]),(0,[z0,z1,z2,z47,z120,z198])],[(0,[z7,z27,z1,z2,z240,z5]),(0,[z0,z1,z53,z331,z5,z6]),(0,[z0,z250,z2,z3,z5,z17]),(0,[z0,z1,z2,z3,z67,z228]),(0,[z0,z1,z2,z3,z5,z1031])],[(0,[z83,z0,z1,z3,z5,z716])],[(0,[z0,z1,z1032,z3,z5,z6]),(0,[z0,z1,z2,z1033,z5,z6]),(0,[z0,z1,z2,z279,z5,z6]),(0,[z0,z1,z2,z1034,z5,z6]),(0,[z0,z1,z2,z69,z67,z68])],[(0,[z7,z1,z28,z3,z5,z54]),(0,[z0,z1,z2,z906,z5,z6]),(0,[z0,z1,z2,z1035,z5,z6])],[(0,[z0,z1,z2,z1036,z5,z6]),(0,[z7,z0,z1,z2,z3,z921]),(0,[z7,z644,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z555,z175]),(0,[z697,z0,z1,z2,z47,z6]),(0,[z0,z1,z2,z67,z68,z166])],[(0,[z0,z1,z28,z3,z5,z32]),(0,[z0,z963,z2,z3,z5,z6]),(0,[z7,z208,z1,z2,z142,z5]),(0,[z0,z1,z2,z279,z273,z5]),(0,[z0,z1,z2,z1037,z5,z6]),(1,[z0,z250,z2,z151,z5]),(0,[z0,z35,z2,z3,z5,z20]),(0,[z195,z0,z1,z2,z3,z228]),(0,[z0,z1,z2,z1038,z3,z6])]],
   [[(0,[z0,z179,z250,z2,z3,z5]),(0,[z0,z35,z2,z3,z5,z174]),(0,[z0,z1,z2,z3,z5,z1039]),(1,[z0,z250,z71,z3,z5]),(0,[z0,z1,z199,z71,z3,z5]),(0,[z0,z1,z71,z3,z5,z20]),(0,[z0,z1,z2,z3,z1040,z6]),(1,[z0,z1,z3,z5,z716])],[(0,[z7,z167,z13,z2,z3,z5]),(0,[z0,z1,z2,z1041,z3,z5]),(0,[z0,z1,z2,z3,z5,z1042]),(0,[z0,z1,z2,z1043,z5,z6]),(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z2,z3,z5,z1045]),(0,[z0,z1,z2,z3,z5,z1046]),(0,[z7,z1,z2,z3,z5,z373]),(0,[z1047,z1,z2,z3,z5,z6]),(0,[z0,z1,z527,z26,z5,z6]),(0,[z0,z1,z49,z26,z5,z6]),(0,[z0,z1,z2,z3,z5,z1048])],[(0,[z0,z1,z2,z3,z5,z174]),(0,[z0,z317,z1,z2,z3,z5]),(0,[z22,z0,z1,z397,z3,z5]),(0,[z0,z1,z2,z3,z5,z1049]),(0,[z208,z1,z2,z142,z5,z6]),(0,[z0,z1,z199,z3,z8,z6]),(0,[z222,z1,z2,z78,z5,z6]),(1,[z0,z2,z3,z5,z827]),(0,[z0,z1050,z1,z2,z3,z5])],[(0,[z7,z0,z1,z2,z3,z1026]),(0,[z22,z0,z1,z2,z543,z3]),(0,[z0,z2,z775,z3,z5,z6]),(0,[z0,z1,z2,z430,z5,z6]),(0,[z0,z1,z1051,z3,z5,z6]),(0,[z0,z1,z1052,z3,z5,z6]),(0,[z0,z1,z2,z3,z432,z6])],[(0,[z0,z1,z397,z3,z5,z6]),(0,[z7,z1,z2,z151,z5,z156]),(0,[z0,z1053,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1054,z5,z6]),(0,[z0,z1,z2,z460,z5,z17]),(0,[z0,z1,z2,z1055,z3,z5]),(0,[z0,z1,z2,z1056,z3,z6]),(0,[z0,z1,z2,z1057,z3,z5]),(0,[z0,z1,z1058,z3,z5,z6])],[(0,[z7,z131,z1,z28,z3,z5]),(0,[z0,z1,z290,z3,z5,z6]),(0,[z0,z1,z2,z1059,z3,z5]),(0,[z0,z1060,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z67,z727])],[(0,[z7,z207,z1,z2,z3,z5]),(0,[z324,z0,z1,z2,z47,z6]),(0,[z7,z376,z1,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z1061,z3,z6]),(0,[z0,z1,z2,z3,z1062,z5]),(0,[z0,z1,z2,z151,z5,z60]),(0,[z0,z35,z71,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z3,z1063,z6]),(0,[z0,z1,z2,z69,z5,z17])],[(0,[z0,z1,z2,z3,z5,z1064]),(0,[z0,z1,z2,z1065,z5,z6]),(0,[z205,z1,z2,z3,z244,z16]),(0,[z0,z1,z2,z279,z244,z5]),(0,[z7,z0,z1,z2,z5,z166])],[(0,[z85,z1,z399,z28,z3,z5]),(0,[z0,z1,z71,z3,z5,z6]),(0,[z7,z314,z1,z2,z3,z5]),(0,[z0,z1,z2,z331,z229,z6])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z1066,z3,z5,z6])],[(0,[z471,z1,z28,z3,z5,z6]),(0,[z0,z1,z1067,z3,z5,z6]),(0,[z0,z1,z2,z460,z121,z5]),(0,[z7,z0,z1,z351,z3,z5]),(0,[z98,z0,z99,z78,z5,z6]),(0,[z0,z1,z1068,z2,z3,z5]),(0,[z0,z1,z2,z388,z3,z165]),(0,[z1069,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z600]),(0,[z22,z0,z79,z2,z80,z5])],[(0,[z1,z2,z142,z906,z5,z6]),(0,[z0,z1070,z1,z2,z3,z5]),(0,[z0,z1,z298,z3,z211,z6]),(0,[z0,z1,z2,z3,z40,z198])],[(0,[z7,z1,z2,z746,z3,z5]),(0,[z7,z222,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1071]),(0,[z0,z1,z2,z5,z6,z166]),(0,[z0,z1,z2,z5,z288,z17])]],
   [[(0,[z0,z1,z2,z3,z1072,z6]),(0,[z1,z2,z3,z5,z36,z729]),(0,[z0,z1,z2,z3,z5,z1073])],[(0,[z7,z85,z1,z28,z3,z5]),(0,[z0,z1,z2,z3,z5,z59]),(0,[z7,z22,z250,z2,z3,z5]),(0,[z7,z1,z2,z702,z3,z5]),(0,[z0,z79,z10,z80,z5,z6]),(0,[z340,z207,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1074,z5,z6]),(0,[z0,z1,z2,z3,z5,z1075]),(0,[z145,z1,z226,z180,z5,z6]),(0,[z0,z1,z2,z3,z911,z6]),(0,[z239,z0,z1,z71,z3,z5]),(0,[z7,z137,z1,z2,z3,z5]),(0,[z22,z0,z1,z1076,z3,z5]),(0,[z22,z0,z1,z2,z848,z3]),(0,[z471,z1,z2,z3,z5,z32]),(0,[z0,z1,z2,z51,z791,z6])],[(0,[z0,z1077,z2,z3,z5,z6]),(0,[z0,z1,z1078,z3,z5,z6]),(0,[z0,z1,z2,z864,z5,z234]),(0,[z7,z22,z1,z2,z151,z5]),(0,[z7,z22,z1,z2,z3,z8]),(0,[z7,z0,z1,z2,z3,z40])],[(0,[z0,z1,z28,z3,z555,z6]),(0,[z0,z1,z49,z345,z5,z6]),(0,[z208,z0,z1,z2,z409,z6]),(0,[z205,z1,z77,z3,z16,z6]),(0,[z7,z22,z1,z71,z3,z5]),(0,[z183,z0,z1,z2,z3,z60]),(0,[z0,z35,z199,z3,z5,z6]),(1,[z0,z775,z3,z5,z6]),(0,[z1079,z0,z1,z2,z3,z5])],[(0,[z471,z1,z2,z3,z5,z6]),(0,[z22,z0,z1,z922,z3,z5]),(0,[z0,z1,z64,z3,z5,z716])],[(0,[z0,z1,z2,z3,z5,z1080]),(0,[z0,z1,z199,z3,z5,z6]),(0,[z27,z1,z53,z3,z5,z141]),(0,[z27,z1,z199,z3,z5,z6]),(0,[z7,z625,z1,z2,z3,z5]),(0,[z0,z1,z2,z306,z123,z6])],[(0,[z7,z27,z1,z53,z3,z5]),(0,[z0,z1,z2,z3,z5,z1081]),(1,[z0,z2,z3,z762,z6]),(1,[z0,z1,z2,z5,z726])]],
   [[(0,[z0,z1,z1082,z3,z5,z6]),(0,[z0,z1,z2,z3,z244,z5]),(0,[z7,z0,z1,z2,z3,z978]),(0,[z0,z1,z2,z3,z1083,z6])],[(0,[z0,z1,z1084,z3,z5,z6]),(0,[z0,z1,z3,z5,z186,z54]),(0,[z7,z0,z1,z2,z151,z60]),(0,[z0,z1085,z1,z2,z3,z5]),(0,[z7,z1,z2,z240,z5,z156]),(0,[z7,z1,z2,z3,z5,z695]),(0,[z0,z1,z2,z121,z481,z5]),(0,[z0,z1,z2,z214,z3,z165])],[(0,[z0,z1086,z1,z2,z3,z5]),(0,[z7,z0,z1,z71,z3,z60]),(0,[z0,z1,z2,z3,z555,z32]),(0,[z0,z1,z543,z100,z3,z6]),(0,[z0,z1,z351,z430,z5,z6]),(0,[z207,z1,z2,z3,z5,z65]),(1,[z0,z1,z2,z791,z6])],[(0,[z76,z19,z2,z3,z5,z174]),(0,[z0,z1,z2,z3,z5,z1087]),(0,[z145,z1,z146,z180,z5,z6]),(0,[z0,z1,z1088,z3,z5,z6]),(0,[z7,z0,z1,z2,z890,z5])],[],[(0,[z76,z19,z397,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1089]),(0,[z7,z22,z35,z2,z3,z5]),(0,[z22,z0,z1,z82,z123,z5]),(0,[z0,z1,z2,z3,z555,z6]),(0,[z0,z50,z2,z3,z72,z469]),(0,[z1090,z1,z2,z3,z5,z6]),(0,[z0,z1,z1091,z2,z3,z5])],[(0,[z7,z1,z49,z28,z3,z5]),(0,[z0,z1,z2,z5,z198,z17])],[(0,[z0,z1,z2,z3,z5,z126]),(0,[z0,z1,z2,z3,z5,z1092]),(0,[z22,z0,z1,z226,z3,z5]),(0,[z0,z1,z2,z3,z5,z1093]),(0,[z0,z1,z2,z3,z5,z1094]),(0,[z0,z79,z100,z80,z5,z6]),(0,[z0,z1,z3,z5,z1095,z6])]],
   [[(0,[z0,z250,z2,z3,z5,z122]),(0,[z0,z1,z3,z5,z6,z1096]),(0,[z0,z1,z3,z5,z6,z1097])],[(0,[z0,z1098,z2,z3,z5,z6]),(0,[z7,z0,z734,z2,z3,z5]),(0,[z0,z1,z2,z1099,z5,z6]),(0,[z0,z131,z775,z3,z5,z6]),(0,[z0,z1,z2,z1100,z3,z5])],[(0,[z0,z1,z351,z3,z5,z6]),(0,[z0,z204,z2,z275,z5,z6]),(0,[z0,z1,z178,z224,z113,z6])],[(0,[z0,z1,z2,z1101,z5,z6]),(0,[z0,z1,z2,z47,z601,z6]),(0,[z7,z0,z250,z2,z3,z5]),(0,[z22,z0,z1,z2,z78,z5]),(0,[z0,z50,z2,z652,z3,z6]),(0,[z0,z1102,z1,z2,z3,z5])],[(0,[z76,z19,z2,z3,z5,z6]),(0,[z0,z1,z1103,z3,z5,z6]),(0,[z85,z1,z28,z3,z5,z6]),(0,[z0,z1,z1076,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1104]),(0,[z0,z1,z2,z3,z60,z251]),(0,[z0,z131,z172,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1105]),(0,[z7,z27,z1,z199,z3,z5]),(0,[z0,z1,z53,z3,z5,z32]),(0,[z83,z0,z1,z3,z5,z186]),(0,[z1,z2,z3,z209,z911,z6]),(0,[z7,z0,z1,z2,z151,z5]),(0,[z7,z0,z1,z2,z3,z8]),(0,[z590,z0,z293,z2,z3,z5]),(0,[z0,z1,z2,z47,z105,z6]),(0,[z83,z0,z1,z3,z5,z65]),(0,[z0,z1,z2,z3,z198,z165])],[(0,[z7,z0,z1,z71,z3,z5]),(0,[z0,z250,z199,z3,z5,z6]),(0,[z0,z79,z2,z543,z80,z6]),(0,[z0,z1,z2,z3,z6,z1106]),(0,[z0,z2,z3,z762,z72,z6])],[(0,[z0,z1,z2,z839,z5,z6]),(1,[z1,z2,z906,z5,z6]),(0,[z0,z1,z2,z1107,z3,z6]),(0,[z471,z1,z2,z3,z555,z6]),(0,[z0,z79,z2,z725,z5,z6]),(0,[z0,z1,z2,z47,z616,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z1108]),(0,[z0,z1,z2,z3,z999,z6]),(0,[z0,z1,z2,z760,z5,z6]),(0,[z7,z0,z1109,z2,z3,z5]),(0,[z0,z1,z2,z477,z3,z165])],[(0,[z637,z1,z28,z3,z5,z6]),(0,[z12,z0,z2,z3,z5,z827]),(0,[z0,z1,z2,z69,z5,z6])],[(0,[z0,z1,z2,z3,z1110,z6]),(0,[z7,z0,z1,z2,z190,z5]),(0,[z0,z1,z2,z3,z5,z1111]),(0,[z0,z79,z2,z80,z5,z347]),(0,[z0,z2,z3,z5,z827,z20]),(0,[z0,z1,z82,z123,z5,z6]),(0,[z0,z1,z2,z1112,z5,z6])],[(0,[z7,z1,z28,z3,z123,z5]),(0,[z0,z1,z2,z3,z5,z1113]),(0,[z22,z0,z1,z2,z240,z5]),(0,[z0,z1,z2,z3,z1114,z6]),(0,[z0,z1,z3,z757,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1115]),(0,[z1116,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1117]),(0,[z7,z0,z1,z567,z3,z5]),(0,[z22,z0,z1,z2,z306,z3]),(0,[z0,z1,z2,z47,z140,z6])],[(0,[z7,z0,z1,z2,z3,z815]),(0,[z7,z0,z1,z1118,z3,z5]),(0,[z22,z1,z2,z3,z5,z36]),(0,[z0,z1,z2,z3,z60,z17]),(0,[z0,z1,z2,z3,z5,z1119]),(0,[z0,z1120,z1,z2,z3,z5]),(0,[z0,z1,z2,z69,z5,z122])],[(0,[z83,z0,z1,z399,z3,z5]),(0,[z7,z0,z35,z2,z3,z5]),(0,[z7,z0,z1,z910,z3,z5]),(0,[z0,z1,z3,z163,z5,z6]),(0,[z0,z1121,z1,z2,z3,z5])]],
   [[(0,[z438,z1,z2,z142,z5,z6]),(0,[z0,z1109,z2,z3,z5,z6]),(0,[z0,z1122,z2,z3,z5,z6]),(0,[z0,z1,z2,z69,z5,z198])],[(0,[z0,z1,z1123,z2,z5,z6]),(0,[z0,z1,z2,z1124,z5,z6]),(0,[z22,z0,z115,z2,z3,z11]),(0,[z22,z0,z1,z178,z3,z113]),(0,[z0,z2,z3,z725,z5,z6])],[(0,[z22,z0,z1,z2,z3,z5]),(0,[z0,z1,z567,z3,z5,z6]),(0,[z471,z1,z53,z3,z5,z6]),(0,[z7,z0,z1,z2,z1037,z5]),(0,[z0,z1,z1125,z3,z5,z6])],[(0,[z359,z0,z250,z2,z3,z5]),(0,[z7,z0,z1,z1126,z3,z5]),(0,[z0,z1,z2,z3,z1127,z6]),(0,[z12,z0,z2,z3,z5,z251])],[(0,[z7,z0,z1,z199,z240,z5]),(0,[z0,z250,z2,z3,z5,z54]),(0,[z22,z0,z1,z927,z3,z5]),(0,[z0,z1,z351,z3,z555,z6]),(0,[z0,z2,z3,z5,z827,z6]),(0,[z0,z1,z2,z3,z5,z1128])],[(0,[z7,z0,z1,z290,z3,z5]),(0,[z0,z1,z2,z1129,z5,z6]),(0,[z0,z1,z2,z3,z234,z165]),(0,[z359,z0,z1,z2,z151,z5]),(0,[z7,z0,z1,z2,z3,z138]),(0,[z0,z1,z2,z3,z229,z32]),(0,[z0,z1130,z2,z3,z5,z6]),(0,[z0,z1,z2,z47,z120,z6])],[(0,[z0,z966,z2,z3,z5,z6]),(0,[z1005,z0,z1,z2,z3,z5]),(0,[z7,z0,z131,z103,z3,z5]),(0,[z0,z1,z199,z3,z5,z65]),(0,[z445,z22,z1,z2,z3,z5]),(0,[z0,z1,z433,z3,z5,z54]),(0,[z0,z204,z2,z56,z5,z6])],[(0,[z0,z1,z1131,z3,z5,z6]),(0,[z0,z1,z2,z1132,z3,z6]),(0,[z7,z0,z1,z714,z3,z5]),(0,[z0,z50,z2,z430,z72,z6])]],
   [[(0,[z76,z19,z2,z3,z5,z126]),(0,[z506,z1,z28,z3,z5,z6]),(0,[z7,z205,z1,z2,z3,z16]),(0,[z205,z0,z1,z2,z279,z6]),(0,[z7,z1,z2,z416,z3,z5]),(0,[z0,z35,z2,z3,z8,z6]),(0,[z22,z0,z1,z2,z51,z52]),(0,[z0,z605,z1,z2,z47,z6])],[(0,[z179,z1,z2,z28,z3,z5]),(0,[z0,z1,z2,z3,z5,z1133]),(0,[z7,z0,z1,z931,z3,z5]),(0,[z7,z436,z1,z2,z3,z5]),(0,[z22,z0,z50,z2,z3,z72]),(0,[z0,z1,z2,z3,z5,z1134]),(0,[z0,z41,z2,z3,z5,z20]),(0,[z83,z259,z1,z3,z5,z65])],[(0,[z253,z13,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1135]),(0,[z0,z1,z2,z3,z8,z6]),(0,[z0,z1,z2,z151,z5,z251]),(0,[z22,z0,z1,z2,z1107,z3]),(0,[z0,z1,z1136,z3,z5,z6])],[(0,[z7,z0,z1,z199,z3,z5]),(0,[z22,z0,z1,z2,z1010,z5]),(0,[z0,z1,z2,z3,z1137,z6]),(0,[z0,z1,z2,z543,z3,z6]),(0,[z0,z1,z3,z5,z1138,z6]),(0,[z1139,z1,z2,z3,z5,z6])],[(0,[z471,z1,z567,z3,z5,z6]),(0,[z7,z1,z71,z28,z3,z5]),(0,[z7,z1,z2,z3,z5,z329]),(1,[z1,z2,z3,z911,z6]),(0,[z0,z1,z2,z1140,z3,z6]),(0,[z0,z1,z351,z3,z211,z6]),(0,[z0,z1,z576,z3,z5,z54]),(0,[z0,z1,z2,z121,z5,z726])],[(0,[z7,z1,z2,z28,z3,z5]),(0,[z0,z1,z2,z3,z5,z1141]),(0,[z0,z1,z2,z240,z5,z59]),(0,[z0,z35,z250,z2,z3,z5]),(0,[z7,z431,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z8,z68]),(0,[z0,z1,z10,z123,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1142]),(0,[z7,z0,z1,z263,z3,z211])],[(0,[z0,z50,z2,z3,z72,z6]),(0,[z0,z1,z2,z3,z566,z68]),(0,[z0,z1,z82,z757,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z174,z20]),(0,[z112,z1,z28,z3,z5,z6]),(0,[z0,z1,z2,z1143,z5,z6]),(0,[z0,z1,z2,z3,z5,z1144]),(0,[z0,z1,z2,z3,z5,z1145]),(0,[z1146,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1147]),(0,[z85,z1,z712,z3,z5,z6]),(0,[z1148,z0,z1,z2,z3,z5]),(0,[z98,z0,z62,z3,z5,z6]),(0,[z0,z2,z3,z5,z251,z827]),(0,[z0,z1,z2,z1149,z3,z5])],[(0,[z0,z1,z2,z273,z3,z165]),(0,[z15,z22,z1,z2,z3,z209]),(0,[z22,z1,z2,z3,z5,z706]),(0,[z471,z1,z2,z3,z229,z6]),(0,[z0,z1,z2,z3,z5,z295]),(0,[z0,z1,z296,z3,z113,z6])],[(0,[z98,z222,z99,z3,z5,z6])],[(0,[z0,z872,z2,z3,z5,z6]),(0,[z15,z1,z2,z3,z209,z234]),(0,[z0,z1,z2,z1150,z5,z6]),(0,[z0,z74,z2,z3,z5,z827]),(0,[z0,z1,z2,z3,z5,z716])],[(0,[z0,z1,z2,z1151,z5,z6]),(0,[z0,z1,z1118,z3,z5,z6]),(0,[z7,z0,z1098,z2,z3,z5]),(0,[z0,z1,z2,z3,z60,z20]),(0,[z0,z1,z2,z3,z6,z1152]),(0,[z0,z1,z3,z113,z756,z6])],[(0,[z0,z1,z2,z3,z5,z1153]),(0,[z22,z259,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1154,z3,z5]),(0,[z0,z1,z2,z809,z5,z6]),(0,[z7,z145,z1,z2,z180,z5]),(0,[z0,z1,z2,z1155,z5,z6])]],
   [[(0,[z7,z1,z199,z28,z3,z5]),(0,[z0,z1,z2,z785,z5,z6]),(0,[z0,z250,z2,z71,z3,z5]),(0,[z7,z459,z1,z2,z3,z5]),(0,[z0,z1156,z1,z2,z3,z5])],[(0,[z0,z1,z2,z346,z5,z6]),(0,[z7,z594,z1,z2,z3,z5]),(0,[z207,z22,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1157]),(0,[z0,z654,z2,z3,z5,z251])],[(0,[z22,z0,z1,z77,z3,z5]),(0,[z205,z1,z2,z108,z3,z6]),(0,[z0,z1,z847,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z234]),(0,[z0,z250,z2,z3,z8,z6]),(0,[z0,z1,z2,z3,z1158,z6]),(0,[z0,z79,z2,z652,z5,z6]),(0,[z0,z1,z2,z1159,z5,z6]),(0,[z0,z1,z3,z756,z211,z6]),(0,[z0,z1,z2,z3,z40,z6])],[(0,[z76,z19,z567,z3,z5,z6]),(0,[z22,z0,z1,z2,z346,z5]),(0,[z7,z0,z1,z2,z3,z950]),(0,[z7,z0,z1,z2,z3,z315]),(0,[z0,z115,z2,z3,z762,z6]),(0,[z1160,z1,z2,z3,z5,z6])],[(0,[z0,z35,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1161]),(0,[z0,z1,z2,z1162,z3,z6]),(0,[z0,z1,z1163,z3,z5,z6]),(0,[z1164,z1,z2,z3,z5,z6]),(0,[z0,z1165,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1020,z6]),(0,[z0,z1,z3,z1166,z5,z6])],[(0,[z208,z1,z2,z142,z5,z97]),(0,[z0,z1,z1126,z3,z5,z6]),(0,[z0,z1,z71,z3,z60,z6]),(0,[z22,z0,z1,z10,z3,z5]),(0,[z837,z471,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z1167,z6]),(0,[z0,z1,z2,z3,z5,z1168]),(0,[z0,z1,z1169,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1170])],[(0,[z0,z1,z2,z3,z5,z1171]),(0,[z0,z1,z2,z78,z5,z32]),(0,[z0,z1,z2,z3,z1172,z6]),(1,[z0,z1,z757,z5,z6]),(0,[z0,z1,z26,z757,z5,z6]),(0,[z0,z1,z2,z1173,z5,z6])]],
   [[(0,[z0,z1,z924,z3,z5,z6]),(0,[z7,z27,z250,z2,z3,z5]),(0,[z145,z1,z2,z906,z5,z6]),(0,[z0,z1,z2,z51,z415,z6]),(0,[z0,z1,z2,z5,z6,z882]),(0,[z0,z1,z2,z1174,z5,z6]),(0,[z0,z1,z26,z528,z5,z6]),(0,[z0,z1,z2,z1175,z5,z6]),(0,[z1176,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1177,z6]),(0,[z0,z1,z2,z214,z3,z60]),(0,[z22,z0,z1,z2,z3,z432])],[(0,[z0,z1,z2,z3,z5,z1178]),(0,[z7,z27,z1,z2,z151,z5]),(0,[z7,z27,z1,z2,z3,z8]),(0,[z1179,z1,z2,z3,z5,z6]),(0,[z1180,z1,z2,z3,z5,z6]),(0,[z0,z2,z275,z725,z5,z6]),(0,[z0,z1,z1181,z3,z5,z6]),(0,[z1182,z0,z1,z2,z3,z5]),(0,[z1183,z0,z1,z2,z3,z5])],[(0,[z0,z1,z2,z1184,z5,z6]),(0,[z0,z1,z2,z1185,z5,z6]),(0,[z7,z27,z1,z71,z3,z5]),(0,[z7,z0,z1,z2,z224,z5]),(0,[z7,z0,z1,z2,z47,z120]),(0,[z0,z1,z2,z3,z5,z1186])],[(0,[z0,z2,z3,z1187,z5,z6]),(0,[z0,z1,z2,z3,z60,z122]),(0,[z22,z94,z1,z2,z3,z5]),(0,[z98,z0,z99,z331,z5,z6]),(0,[z0,z1,z2,z52,z791,z6]),(0,[z0,z1,z2,z3,z727,z165])],[(0,[z12,z0,z2,z3,z5,z174]),(0,[z7,z1,z2,z3,z5,z393]),(0,[z7,z0,z1,z2,z3,z555]),(0,[z0,z1188,z1,z2,z3,z5])],[(0,[z0,z1,z26,z331,z5,z6]),(0,[z0,z1,z2,z1189,z5,z6])],[(0,[z0,z1,z1190,z2,z3,z6]),(0,[z7,z1,z610,z2,z3,z5]),(0,[z22,z0,z1,z2,z223,z5]),(0,[z0,z1,z223,z163,z5,z6]),(0,[z0,z1,z49,z26,z138,z6])]],
   [[(0,[z7,z0,z1077,z2,z3,z5]),(0,[z1191,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z6,z1192])],[(0,[z7,z0,z916,z2,z3,z5]),(0,[z0,z1,z2,z240,z5,z17]),(0,[z22,z0,z1,z1067,z3,z5]),(0,[z0,z1,z10,z331,z5,z6])],[(0,[z0,z1,z199,z3,z60,z6]),(0,[z0,z775,z99,z3,z5,z6]),(0,[z0,z1,z2,z47,z3,z119]),(0,[z0,z1,z2,z47,z791,z6]),(0,[z0,z1,z2,z3,z1193,z5])],[(0,[z617,z1,z28,z3,z5,z6]),(0,[z0,z1,z178,z3,z511,z6]),(0,[z0,z1,z1194,z3,z5,z6]),(0,[z0,z1,z945,z3,z5,z6]),(0,[z7,z0,z1,z2,z1151,z5]),(0,[z7,z0,z875,z2,z3,z5])],[(0,[z7,z27,z35,z2,z3,z5]),(0,[z0,z1,z2,z3,z1195,z6]),(0,[z436,z1,z53,z3,z5,z6]),(0,[z145,z1,z2,z108,z5,z6]),(0,[z0,z1,z2,z3,z824,z6]),(0,[z205,z1,z2,z3,z911,z6]),(0,[z471,z1,z2,z78,z5,z6]),(0,[z0,z1,z2,z3,z229,z175]),(0,[z1196,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z67,z198]),(0,[z0,z1,z2,z51,z6,z486])],[(0,[z167,z179,z13,z2,z3,z5]),(0,[z0,z250,z71,z3,z5,z6]),(0,[z1197,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z121,z5,z122])],[(0,[z0,z250,z2,z3,z5,z6]),(0,[z0,z1,z2,z934,z5,z6]),(0,[z27,z250,z2,z3,z5,z6]),(0,[z0,z1,z2,z121,z5,z59]),(0,[z0,z2,z725,z80,z5,z6])],[(0,[z7,z0,z250,z2,z240,z5]),(1,[z0,z250,z2,z3,z60]),(0,[z0,z1,z2,z121,z5,z198]),(0,[z0,z1,z2,z214,z3,z727])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1045).take 209) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1254)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 523, 209] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 90).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 180).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [90, 90, 76] = true :=
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

end PEqualNP.Outside.L_meta_38805

theorem PEqualNP.Outside.L_meta_38805 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274571456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38805.solve